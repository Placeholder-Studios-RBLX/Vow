--!strict
--!optimize 2

--[=[
	@name Vow

	@desc A data-oriented, procedural Promise/Future library for Luau.

	Vow has no objects, metatables, resolve closures, or varargs. A Vow is a
	generation-tagged integer handle backed by module-level Structure-of-Arrays
	storage.

	Each Vow stores one state, one value, and an intrusive listener list.
	Listener nodes are pooled globally and linked through parallel arrays.
	Settled Vows remain alive until Vow.destroy is called.

	@usage
		local Vow = require(path.To.Vow)

		local id = Vow.new(function(id)
			task.defer(function()
				Vow.resolve(id, "ready")
			end)
		end)

		local nextId = Vow.andThen(id, function(value)
			print(value)
			return "finished"
		end)

		local ok, value = Vow.await(nextId)

	@notes
		* Vow handles are opaque integers. Never fabricate or modify them.
		* Every Vow resolves or rejects with exactly one value.
		* Vow.resolve adopts another live Vow passed as its value. So does a
		  value returned from an andThen fulfillment callback.
		* Adoption cycles (A -> B -> A) are detected and safely rejected.
		* Rejections are reported asynchronously when no rejection handler
		  is attached before the deferred unhandled check.
		* Destroying a rejected Vow before the deferred check suppresses the report.
		* Callbacks execute synchronously during resolution, rejection, or when attached to settled Vows.
		* Vow.all and Vow.race validate every input BEFORE allocating the
		  aggregate Vow, so a bad input never leaks a slot.
		* Vows allocate no per-instance tables, but Vow.all generates one table for results.
		* Because Vows are integer handles, Luau's garbage collector cannot
		  discover when a settled Vow is no longer needed. Developers MUST
		  call Vow.destroy(id) when completely finished with a Vow.

	@cancellation
		Cancellation flows downwards only.
		* Cancelling a Vow cancels its andThen/adoption children.
		* Cancelling an aggregate input cancels the aggregate.
		* Cancelling an aggregate detaches it from its inputs but never
		  cancels them, since inputs may be shared.
		* Awaiters of a cancelled Vow wake with (false, nil). A rejected Vow with
		  a nil reason also returns (false, nil), making them indistinguishable.

	@version 1.1.0
	@author checcerr
	@license MPL-2.0
]=]

-- We add a phantom type to vow so the type solver can distinguish between it and a normal number.
-- In reality, it is just a number, but this allows for stricter type checking with Vows.
export type Vow<T = any, E = any> = number & { _b: "Vow", _t: T, _e: E }
export type Executor = (id: Vow) -> ()
export type Handler<T = any, U = any> = ((value: T) -> U)?
export type VowStats = {
	vowCapacity: number,
	vowLive: number,
	vowFree: number,
	vowRetired: number,
	nodeCapacity: number,
	nodeActive: number,
	nodeFree: number,
}

-- ============================== tunables ================================

const INITIAL_VOWS = 64
const INITIAL_NODES = 128

const SLOT_ID_SPACE = 16_777_216
const GENERATION_SPACE = 268_435_456
const MAX_HANDLE = GENERATION_SPACE * SLOT_ID_SPACE + (SLOT_ID_SPACE - 1)
const MAX_NODES = 268_435_455

const STATE_PENDING = 1
const STATE_RESOLVED = 2
const STATE_REJECTED = 4
const STATE_CANCELLED = 8

const NODE_CALLBACK = 1
const NODE_AWAIT = 2
const NODE_ADOPT = 3
const NODE_AGGREGATE = 4
const NODE_FINALLY = 5

const AGG_ALL = 1
const AGG_RACE = 2

-- ============================== Vow SoA =================================

local vowValues: { any } = table.create(INITIAL_VOWS)
local vowAggregateResults = table.create(INITIAL_VOWS) :: { { any }? }

local vowCount = 0
local vowCapacity = INITIAL_VOWS
local vowRetired = 0

local vowGens: buffer = buffer.create(INITIAL_VOWS * 4)
local vowStates: buffer = buffer.create(INITIAL_VOWS)
local vowHeads: buffer = buffer.create(INITIAL_VOWS * 4)
local vowTails: buffer = buffer.create(INITIAL_VOWS * 4)
local vowOwnedHeads: buffer = buffer.create(INITIAL_VOWS * 4)
local vowOwnedTails: buffer = buffer.create(INITIAL_VOWS * 4)
local vowHandled: buffer = buffer.create(INITIAL_VOWS)
local vowAggregateModes: buffer = buffer.create(INITIAL_VOWS)
local vowAggregateRemaining: buffer = buffer.create(INITIAL_VOWS * 4)
local vowAdopts: buffer = buffer.create(INITIAL_VOWS * 4)
local vowParents: buffer = buffer.create(INITIAL_VOWS * 4)
local vowChildHeads: buffer = buffer.create(INITIAL_VOWS * 4)
local vowChildNexts: buffer = buffer.create(INITIAL_VOWS * 4)
local vowChildPrevs: buffer = buffer.create(INITIAL_VOWS * 4)

local vowFree: buffer = buffer.create(INITIAL_VOWS * 4)
local vowFreeLength = 0
local vowFreeCapacity = INITIAL_VOWS

-- ============================ Listener SoA ==============================

local nodeKinds: buffer = buffer.create(INITIAL_NODES)
local nodeNext: buffer = buffer.create(INITIAL_NODES * 4)
local nodePrevious: buffer = buffer.create(INITIAL_NODES * 4)

local nodeOwnerNext: buffer = buffer.create(INITIAL_NODES * 4)
local nodeOwnerPrevious: buffer = buffer.create(INITIAL_NODES * 4)

local nodeSources: buffer = buffer.create(INITIAL_NODES * 4)
local nodeOwners: buffer = buffer.create(INITIAL_NODES * 4)
local nodeIndices: buffer = buffer.create(INITIAL_NODES * 4)

local nodeResolved = table.create(INITIAL_NODES) :: { Handler }
local nodeRejected = table.create(INITIAL_NODES) :: { Handler }
local nodeChildren = table.create(INITIAL_NODES) :: { Vow? }
local nodeThreads = table.create(INITIAL_NODES) :: { thread? }
local nodeFinally = table.create(INITIAL_NODES) :: { ((ok: boolean, value: any) -> ())? }

local nodeCount = 0
local nodeCapacity = INITIAL_NODES

local nodeFree: buffer = buffer.create(INITIAL_NODES * 4)
local nodeFreeLength = 0
local nodeFreeCapacity = INITIAL_NODES

-- ============================== internals ================================

local settle: (id: number, state: number, value: any) -> ()
local cancelInternal: (handle: Vow, fireFinally: boolean) -> ()
local destroyInternal: (id: number) -> ()
local resolveValue: (id: number, value: any) -> ()

const function growU8(source: buffer, oldCount: number, newCount: number): buffer
	const result = buffer.create(newCount)
	buffer.copy(result, 0, source, 0, oldCount)
	return result
end

const function growU32(source: buffer, oldCount: number, newCount: number): buffer
	const result = buffer.create(newCount * 4)
	buffer.copy(result, 0, source, 0, oldCount * 4)
	return result
end

const function pushVow(id: number): ()
	if vowFreeLength >= vowFreeCapacity then
		const newCapacity = vowFreeCapacity * 2
		vowFree = growU32(vowFree, vowFreeCapacity, newCapacity)
		vowFreeCapacity = newCapacity
	end

	buffer.writeu32(vowFree, vowFreeLength * 4, id)
	vowFreeLength += 1
end

const function pushNode(id: number): ()
	if nodeFreeLength >= nodeFreeCapacity then
		const newCapacity = nodeFreeCapacity * 2
		nodeFree = growU32(nodeFree, nodeFreeCapacity, newCapacity)
		nodeFreeCapacity = newCapacity
	end

	buffer.writeu32(nodeFree, nodeFreeLength * 4, id)
	nodeFreeLength += 1
end

const function growVowsTo(newCapacity: number)
	vowGens = growU32(vowGens, vowCapacity, newCapacity)
	vowStates = growU8(vowStates, vowCapacity, newCapacity)
	vowHeads = growU32(vowHeads, vowCapacity, newCapacity)
	vowTails = growU32(vowTails, vowCapacity, newCapacity)
	vowOwnedHeads = growU32(vowOwnedHeads, vowCapacity, newCapacity)
	vowOwnedTails = growU32(vowOwnedTails, vowCapacity, newCapacity)
	vowHandled = growU8(vowHandled, vowCapacity, newCapacity)
	vowAggregateModes = growU8(vowAggregateModes, vowCapacity, newCapacity)
	vowAggregateRemaining = growU32(vowAggregateRemaining, vowCapacity, newCapacity)
	vowAdopts = growU32(vowAdopts, vowCapacity, newCapacity)
	vowParents = growU32(vowParents, vowCapacity, newCapacity)
	vowChildHeads = growU32(vowChildHeads, vowCapacity, newCapacity)
	vowChildNexts = growU32(vowChildNexts, vowCapacity, newCapacity)
	vowChildPrevs = growU32(vowChildPrevs, vowCapacity, newCapacity)

	const newValues = table.create(newCapacity) :: { any }
	const newAggResults = table.create(newCapacity) :: { { any }? }
	table.move(vowValues, 1, vowCapacity, 1, newValues)
	table.move(vowAggregateResults, 1, vowCapacity, 1, newAggResults)
	vowValues = newValues
	vowAggregateResults = newAggResults

	vowCapacity = newCapacity
end

const function growNodesTo(newCapacity: number)
	nodeKinds = growU8(nodeKinds, nodeCapacity, newCapacity)
	nodeNext = growU32(nodeNext, nodeCapacity, newCapacity)
	nodePrevious = growU32(nodePrevious, nodeCapacity, newCapacity)
	nodeOwnerNext = growU32(nodeOwnerNext, nodeCapacity, newCapacity)
	nodeOwnerPrevious = growU32(nodeOwnerPrevious, nodeCapacity, newCapacity)
	nodeSources = growU32(nodeSources, nodeCapacity, newCapacity)
	nodeOwners = growU32(nodeOwners, nodeCapacity, newCapacity)
	nodeIndices = growU32(nodeIndices, nodeCapacity, newCapacity)

	const newResolved = table.create(newCapacity) :: { ((value: any) -> any)? }
	const newRejected = table.create(newCapacity) :: { ((value: any) -> any)? }
	const newChildren = table.create(newCapacity) :: { Vow? }
	const newThreads = table.create(newCapacity) :: { thread? }
	const newFinally = table.create(newCapacity) :: { ((ok: boolean, value: any) -> ())? }

	table.move(nodeResolved, 1, nodeCapacity, 1, newResolved)
	table.move(nodeRejected, 1, nodeCapacity, 1, newRejected)
	table.move(nodeChildren, 1, nodeCapacity, 1, newChildren)
	table.move(nodeThreads, 1, nodeCapacity, 1, newThreads)
	table.move(nodeFinally, 1, nodeCapacity, 1, newFinally)

	nodeResolved = newResolved
	nodeRejected = newRejected
	nodeChildren = newChildren
	nodeThreads = newThreads
	nodeFinally = newFinally

	nodeCapacity = newCapacity
end

const function growVows()
	growVowsTo(vowCapacity * 2)
end
const function growNodes()
	growNodesTo(nodeCapacity * 2)
end

const function acquireVow(): (number, Vow)
	local id: number

	if vowFreeLength > 0 then
		vowFreeLength -= 1
		id = buffer.readu32(vowFree, vowFreeLength * 4)
	else
		if vowCount >= SLOT_ID_SPACE then error(`Vow.new: Vow slot limit ({SLOT_ID_SPACE}) reached`, 2) end

		if vowCount >= vowCapacity then growVows() end

		id = vowCount
		vowCount += 1
	end

	buffer.writeu8(vowStates, id, STATE_PENDING)

	const generation = buffer.readu32(vowGens, id * 4)
	return id, id + (generation + 1) * SLOT_ID_SPACE :: any
end

const function releaseVow(id: number): ()
	const generation = buffer.readu32(vowGens, id * 4) + 1

	vowValues[id + 1] = nil
	vowAggregateResults[id + 1] = nil

	buffer.writeu8(vowStates, id, 0)
	buffer.writeu8(vowHandled, id, 0)
	buffer.writeu8(vowAggregateModes, id, 0)

	buffer.writeu32(vowHeads, id * 4, 0)
	buffer.writeu32(vowTails, id * 4, 0)
	buffer.writeu32(vowOwnedHeads, id * 4, 0)
	buffer.writeu32(vowOwnedTails, id * 4, 0)
	buffer.writeu32(vowAggregateRemaining, id * 4, 0)
	buffer.writeu32(vowAdopts, id * 4, 0)
	buffer.writeu32(vowParents, id * 4, 0)
	buffer.writeu32(vowChildHeads, id * 4, 0)
	buffer.writeu32(vowChildNexts, id * 4, 0)
	buffer.writeu32(vowChildPrevs, id * 4, 0)

	if generation >= GENERATION_SPACE then
		buffer.writeu32(vowGens, id * 4, GENERATION_SPACE - 1)
		vowRetired += 1
		return
	end

	buffer.writeu32(vowGens, id * 4, generation)
	pushVow(id)
end

const function acquireNode(): number
	local id: number

	if nodeFreeLength > 0 then
		nodeFreeLength -= 1
		id = buffer.readu32(nodeFree, nodeFreeLength * 4)
	else
		if nodeCount >= MAX_NODES then error(`Vow.new: Node limit ({MAX_NODES}) reached`, 2) end

		if nodeCount >= nodeCapacity then growNodes() end

		id = nodeCount
		nodeCount += 1
	end

	return id
end

const function releaseNode(id: number): ()
	const slot = id + 1

	buffer.writeu8(nodeKinds, id, 0)
	buffer.writeu32(nodeNext, id * 4, 0)
	buffer.writeu32(nodePrevious, id * 4, 0)
	buffer.writeu32(nodeOwnerNext, id * 4, 0)
	buffer.writeu32(nodeOwnerPrevious, id * 4, 0)
	buffer.writeu32(nodeSources, id * 4, 0)
	buffer.writeu32(nodeOwners, id * 4, 0)
	buffer.writeu32(nodeIndices, id * 4, 0)

	nodeResolved[slot] = nil
	nodeRejected[slot] = nil
	nodeChildren[slot] = nil
	nodeThreads[slot] = nil
	nodeFinally[slot] = nil

	pushNode(id)
end

const function decode(handle: Vow, method: string): number
	if type(handle) ~= "number" then error(`Vow.{method}: expected a Vow handle`, 3) end

	if handle ~= handle or handle < SLOT_ID_SPACE or handle > MAX_HANDLE or handle % 1 ~= 0 then error(`Vow.{method}: invalid Vow handle`, 3) end

	const id = handle % SLOT_ID_SPACE
	const generation = (handle - id) // SLOT_ID_SPACE - 1

	if id >= vowCount then error(`Vow.{method}: handle references an unallocated slot`, 3) end

	if buffer.readu8(vowStates, id) == 0 then error(`Vow.{method}: Vow is no longer alive`, 3) end

	if buffer.readu32(vowGens, id * 4) ~= generation then error(`Vow.{method}: stale or recycled Vow handle`, 3) end

	return id
end

const function tryDecode(handle: any): number?
	if type(handle) ~= "number" then return nil end

	if handle ~= handle or handle < SLOT_ID_SPACE or handle > MAX_HANDLE or handle % 1 ~= 0 then return nil end

	const id = handle % SLOT_ID_SPACE
	const generation = (handle - id) // SLOT_ID_SPACE - 1

	if id >= vowCount then return nil end

	if buffer.readu8(vowStates, id) == 0 then return nil end

	if buffer.readu32(vowGens, id * 4) ~= generation then return nil end

	return id
end

const function handleOf(id: number): Vow
	return id + (buffer.readu32(vowGens, id * 4) + 1) * SLOT_ID_SPACE :: any
end

const function appendSource(source: number, node: number): ()
	const sourceOffset = source * 4
	const tail = buffer.readu32(vowTails, sourceOffset)

	buffer.writeu32(nodeSources, node * 4, source + 1)
	buffer.writeu32(nodePrevious, node * 4, tail)
	buffer.writeu32(nodeNext, node * 4, 0)

	if tail == 0 then
		buffer.writeu32(vowHeads, sourceOffset, node + 1)
	else
		buffer.writeu32(nodeNext, (tail - 1) * 4, node + 1)
	end

	buffer.writeu32(vowTails, sourceOffset, node + 1)
end

const function appendOwner(owner: number, node: number): ()
	const ownerOffset = owner * 4
	const tail = buffer.readu32(vowOwnedTails, ownerOffset)

	buffer.writeu32(nodeOwners, node * 4, owner + 1)
	buffer.writeu32(nodeOwnerPrevious, node * 4, tail)
	buffer.writeu32(nodeOwnerNext, node * 4, 0)

	if tail == 0 then
		buffer.writeu32(vowOwnedHeads, ownerOffset, node + 1)
	else
		buffer.writeu32(nodeOwnerNext, (tail - 1) * 4, node + 1)
	end

	buffer.writeu32(vowOwnedTails, ownerOffset, node + 1)
end

const function unlinkSource(node: number): ()
	const encodedSource = buffer.readu32(nodeSources, node * 4)

	if encodedSource == 0 then return end

	const source = encodedSource - 1
	const sourceOffset = source * 4
	const previous = buffer.readu32(nodePrevious, node * 4)
	const nextNode = buffer.readu32(nodeNext, node * 4)

	if previous == 0 then
		buffer.writeu32(vowHeads, sourceOffset, nextNode)
	else
		buffer.writeu32(nodeNext, (previous - 1) * 4, nextNode)
	end

	if nextNode == 0 then
		buffer.writeu32(vowTails, sourceOffset, previous)
	else
		buffer.writeu32(nodePrevious, (nextNode - 1) * 4, previous)
	end

	buffer.writeu32(nodeSources, node * 4, 0)
	buffer.writeu32(nodePrevious, node * 4, 0)
	buffer.writeu32(nodeNext, node * 4, 0)
end

const function unlinkOwner(node: number): ()
	const encodedOwner = buffer.readu32(nodeOwners, node * 4)

	if encodedOwner == 0 then return end

	const owner = encodedOwner - 1
	const ownerOffset = owner * 4
	const previous = buffer.readu32(nodeOwnerPrevious, node * 4)
	const nextNode = buffer.readu32(nodeOwnerNext, node * 4)

	if previous == 0 then
		buffer.writeu32(vowOwnedHeads, ownerOffset, nextNode)
	else
		buffer.writeu32(nodeOwnerNext, (previous - 1) * 4, nextNode)
	end

	if nextNode == 0 then
		buffer.writeu32(vowOwnedTails, ownerOffset, previous)
	else
		buffer.writeu32(nodeOwnerPrevious, (nextNode - 1) * 4, previous)
	end

	buffer.writeu32(nodeOwners, node * 4, 0)
	buffer.writeu32(nodeOwnerPrevious, node * 4, 0)
	buffer.writeu32(nodeOwnerNext, node * 4, 0)
end

const function linkChild(parent: number, child: number): ()
	const oldHead = buffer.readu32(vowChildHeads, parent * 4)
	buffer.writeu32(vowParents, child * 4, parent + 1)
	buffer.writeu32(vowChildNexts, child * 4, oldHead)
	buffer.writeu32(vowChildPrevs, child * 4, 0)
	if oldHead ~= 0 then buffer.writeu32(vowChildPrevs, (oldHead - 1) * 4, child + 1) end
	buffer.writeu32(vowChildHeads, parent * 4, child + 1)
end

const function unlinkChild(parent: number, child: number): ()
	const prev = buffer.readu32(vowChildPrevs, child * 4)
	const nextSib = buffer.readu32(vowChildNexts, child * 4)

	if prev == 0 then
		buffer.writeu32(vowChildHeads, parent * 4, nextSib)
	else
		buffer.writeu32(vowChildNexts, (prev - 1) * 4, nextSib)
	end

	if nextSib ~= 0 then buffer.writeu32(vowChildPrevs, (nextSib - 1) * 4, prev) end

	buffer.writeu32(vowParents, child * 4, 0)
	buffer.writeu32(vowChildNexts, child * 4, 0)
	buffer.writeu32(vowChildPrevs, child * 4, 0)
end

const function getPending(id: number): number
	local pending = 0

	local n = buffer.readu32(vowHeads, id * 4)
	while n ~= 0 do
		pending += 1
		n = buffer.readu32(nodeNext, (n - 1) * 4)
	end

	return pending
end

const function popSourceHead(source: number): number?
	const encoded = buffer.readu32(vowHeads, source * 4)
	if encoded == 0 then return nil end

	const node = encoded - 1
	unlinkSource(node)
	return node
end

const function makeNode(kind: number, source: number, owner: number?, index: number, resolved: Handler, rejected: Handler, child: Vow?, thread: thread?): number
	const node = acquireNode()
	const slot = node + 1

	buffer.writeu8(nodeKinds, node, kind)
	buffer.writeu32(nodeIndices, node * 4, index)

	nodeResolved[slot] = resolved
	nodeRejected[slot] = rejected
	nodeChildren[slot] = child
	nodeThreads[slot] = thread

	appendSource(source, node)

	if owner ~= nil then appendOwner(owner, node) end

	return node
end

const function makeFinallyNode(source: number, callback: (ok: boolean, value: any) -> ()): number
	local node = acquireNode()
	local slot = node + 1
	buffer.writeu8(nodeKinds, node, NODE_FINALLY)
	nodeFinally[slot] = callback
	appendSource(source, node)
	return node
end

const function detachOwned(owner: number): ()
	local head = buffer.readu32(vowOwnedHeads, owner * 4)

	buffer.writeu32(vowOwnedHeads, owner * 4, 0)
	buffer.writeu32(vowOwnedTails, owner * 4, 0)

	while head ~= 0 do
		const node = head - 1
		head = buffer.readu32(nodeOwnerNext, node * 4)

		buffer.writeu32(nodeOwners, node * 4, 0)
		buffer.writeu32(nodeOwnerPrevious, node * 4, 0)
		buffer.writeu32(nodeOwnerNext, node * 4, 0)

		unlinkSource(node)
		releaseNode(node)
	end
end

const function aggregateStep(parent: Vow, state: number, value: any, index: number): ()
	const parentId = tryDecode(parent)

	if parentId == nil or buffer.readu8(vowStates, parentId) ~= STATE_PENDING then return end

	const mode = buffer.readu8(vowAggregateModes, parentId)

	if mode == AGG_RACE then
		settle(parentId, state, value)
		return
	end

	if mode ~= AGG_ALL then return end

	if state == STATE_REJECTED then
		settle(parentId, STATE_REJECTED, value)
		return
	end

	const results = vowAggregateResults[parentId + 1]

	if results ~= nil then results[index] = value end

	const remaining = buffer.readu32(vowAggregateRemaining, parentId * 4) - 1
	buffer.writeu32(vowAggregateRemaining, parentId * 4, remaining)

	if remaining == 0 then settle(parentId, STATE_RESOLVED, results) end
end

const function invokeCallback(callback: Handler, value: any, child: Vow, rejected: boolean): ()
	if tryDecode(child) == nil then return end

	if callback == nil then
		const childId = tryDecode(child)
		if childId == nil then return end

		if rejected then
			settle(childId, STATE_REJECTED, value)
		else
			resolveValue(childId, value)
		end
		return
	end

	const ok, result = pcall(callback :: (any) -> any, value)
	const childId = tryDecode(child)

	if childId == nil then return end

	if ok then
		resolveValue(childId, result)
	else
		settle(childId, STATE_REJECTED, result)
	end
end

-- Invariant: no listener may be registered on a Vow during that Vow's dispatch. All current APIs
-- respect this; any new API that can append to vowHeads[id] on a settled Vow must route through
-- task.defer
const function dispatch(id: number, state: number, value: any): ()
	const rejected = state == STATE_REJECTED
	const childState = if rejected then STATE_REJECTED else STATE_RESOLVED
	const handle = handleOf(id)

	-- Snapshot the current listener count. Invariant: this count is fixed for the duration of the
	-- dispatch (no additions from callbacks)
	local pending = getPending(id)

	-- First pass: process non-finally nodes in registration order
	-- Finally nodes get popped off and reappended to the tail, deferring them
	while pending > 0 do
		pending -= 1

		const node = popSourceHead(id)
		if node == nil then return end

		const slot = node + 1
		const kind = buffer.readu8(nodeKinds, node)

		if kind == NODE_FINALLY then
			appendSource(id, node) -- Rotate to tail
			continue
		end

		const index = buffer.readu32(nodeIndices, node * 4)
		const child = nodeChildren[slot]
		const waiting = nodeThreads[slot]
		const callback = if rejected then nodeRejected[slot] else nodeResolved[slot]

		unlinkOwner(node)
		releaseNode(node)

		if rejected then buffer.writeu8(vowHandled, id, 1) end

		if kind == NODE_CALLBACK then
			if child ~= nil then invokeCallback(callback, value, child, rejected) end
		elseif kind == NODE_ADOPT then
			if child ~= nil then
				const childId = tryDecode(child)
				if childId ~= nil then settle(childId, childState, value) end
			end
		elseif kind == NODE_AWAIT then
			if waiting ~= nil then task.spawn(waiting, not rejected, value) end
		elseif kind == NODE_AGGREGATE then
			if child ~= nil then aggregateStep(child, childState, value, index) end
		end

		-- Bail if a callback destroyed or recycled this Vow
		if tryDecode(handle) == nil then return end
	end

	-- Second pass: run deferred finally nodes in registration order
	while true do
		const node = popSourceHead(id)
		if node == nil then break end

		const slot = node + 1
		const finalCb = nodeFinally[slot]

		unlinkOwner(node)
		releaseNode(node)

		if finalCb ~= nil then
			const ok, err = pcall(finalCb, not rejected, value)
			if not ok then task.defer(error, err, 0) end
		end

		if tryDecode(handle) == nil then return end
	end
end

const function raiseUnhandled(handle: Vow): ()
	const id = tryDecode(handle)

	if id == nil then return end

	if buffer.readu8(vowStates, id) == STATE_REJECTED and buffer.readu8(vowHandled, id) == 0 then error(vowValues[id + 1], 0) end
end

settle = function(id: number, state: number, value: any): ()
	if buffer.readu8(vowStates, id) ~= STATE_PENDING then return end

	const handle = handleOf(id)

	buffer.writeu8(vowStates, id, state)
	buffer.writeu32(vowAdopts, id * 4, 0)
	vowValues[id + 1] = value

	detachOwned(id)
	dispatch(id, state, value)

	if state == STATE_REJECTED then task.defer(raiseUnhandled, handle) end
end

cancelInternal = function(handle: Vow, fireFinally: boolean): ()
	const id = tryDecode(handle)

	if id == nil or buffer.readu8(vowStates, id) ~= STATE_PENDING then return end

	buffer.writeu8(vowStates, id, STATE_CANCELLED)
	buffer.writeu32(vowAdopts, id * 4, 0)

	detachOwned(id)

	local pending = getPending(id)

	while pending > 0 do
		pending -= 1

		const node = popSourceHead(id)
		if node == nil then return end

		const slot = node + 1
		const kind = buffer.readu8(nodeKinds, node)

		if kind == NODE_FINALLY then
			appendSource(id, node)
			continue
		end

		const child = nodeChildren[slot]
		const waiting = nodeThreads[slot]

		unlinkOwner(node)
		releaseNode(node)

		if kind == NODE_CALLBACK or kind == NODE_ADOPT or kind == NODE_AGGREGATE then
			if child ~= nil then cancelInternal(child, fireFinally) end
		elseif kind == NODE_AWAIT then
			if waiting ~= nil then task.spawn(waiting, false, nil) end
		end
	end

	while true do
		const node = popSourceHead(id)
		if node == nil then break end

		const slot = node + 1
		const finalCb = if fireFinally then nodeFinally[slot] else nil

		unlinkOwner(node)
		releaseNode(node)

		if finalCb ~= nil then
			const ok, err = pcall(finalCb, false, nil)
			if not ok then task.defer(error, err, 0) end
		end
	end
end

destroyInternal = function(id: number): ()
	-- Unlink from parent if the parent is still alive
	const encParent = buffer.readu32(vowParents, id * 4)
	if encParent ~= 0 then unlinkChild(encParent - 1, id) end

	-- Clear the parent pointers of any child vows
	local childHead = buffer.readu32(vowChildHeads, id * 4)
	while childHead ~= 0 do
		const childId = childHead - 1
		childHead = buffer.readu32(vowChildNexts, childId * 4)
		buffer.writeu32(vowParents, childId * 4, 0)
		buffer.writeu32(vowChildNexts, childId * 4, 0)
		buffer.writeu32(vowChildPrevs, childId * 4, 0)
	end
	buffer.writeu32(vowChildHeads, id * 4, 0)

	detachOwned(id)

	while true do
		const node = popSourceHead(id)
		if node == nil then break end

		const slot = node + 1
		const kind = buffer.readu8(nodeKinds, node)
		const waiting = nodeThreads[slot]

		unlinkOwner(node)
		releaseNode(node)

		if kind == NODE_AWAIT then
			if waiting ~= nil then task.spawn(waiting, false, nil) end
		end
	end

	releaseVow(id)
end

const function destroyChainInternal(id: number): ()
	-- Guard against double-visit
	if buffer.readu8(vowStates, id) == 0 then return end

	while true do
		const head = buffer.readu32(vowChildHeads, id * 4)
		if head == 0 then break end
		destroyChainInternal(head - 1)
	end

	if buffer.readu8(vowStates, id) == STATE_PENDING then cancelInternal(handleOf(id), false) end

	destroyInternal(id)
end

const function isAdoptionCycle(id: number, adopted: number): boolean
	local tortoise = adopted
	local hare = adopted

	while true do
		if hare == id then return true end

		const enc1 = buffer.readu32(vowAdopts, hare * 4)
		if enc1 == 0 then return false end
		hare = enc1 - 1

		if hare == id then return true end

		const enc2 = buffer.readu32(vowAdopts, hare * 4)
		if enc2 == 0 then return false end
		hare = enc2 - 1

		tortoise = buffer.readu32(vowAdopts, tortoise * 4) - 1

		if hare == tortoise then return false end
	end
end

resolveValue = function(id: number, value: any): ()
	if buffer.readu8(vowStates, id) ~= STATE_PENDING then return end

	if buffer.readu32(vowAdopts, id * 4) ~= 0 then return end

	const adopted = tryDecode(value)

	if adopted == nil then
		settle(id, STATE_RESOLVED, value)
		return
	end

	if adopted == id then
		settle(id, STATE_REJECTED, "Vow.resolve: cannot resolve a Vow with itself")
		return
	end

	if isAdoptionCycle(id, adopted) then
		settle(id, STATE_REJECTED, "Vow.resolve: adoption cycle detected")
		return
	end

	const state = buffer.readu8(vowStates, adopted)

	if state == STATE_PENDING then
		buffer.writeu32(vowAdopts, id * 4, adopted + 1)
		makeNode(NODE_ADOPT, adopted, id, 0, nil, nil, handleOf(id), nil)
	elseif state == STATE_RESOLVED then
		settle(id, STATE_RESOLVED, vowValues[adopted + 1])
	elseif state == STATE_REJECTED then
		buffer.writeu8(vowHandled, adopted, 1)
		settle(id, STATE_REJECTED, vowValues[adopted + 1])
	elseif state == STATE_CANCELLED then
		cancelInternal(handleOf(id), true)
	end
end

const function validateInputs(vows: { Vow }, method: string): ({ Vow }, number)
	if type(vows) ~= "table" then error(`Vow.{method}: expected an array of Vow handles`, 3) end

	local count = 0
	local maxIndex = 0

	for key, input in next, vows do
		if type(key) ~= "number" or key % 1 ~= 0 or key < 1 then error(`Vow.{method}: expected a dense array with integer keys`, 3) end

		count += 1
		if key > maxIndex then maxIndex = key end

		if tryDecode(input) == nil then error(`Vow.{method}: input #{key} is not a live Vow handle`, 3) end
	end

	if count ~= maxIndex then error(`Vow.{method}: sparse arrays are not allowed`, 3) end

	const snapshot = table.create(count) :: { Vow }
	for index = 1, count do
		snapshot[index] = rawget(vows :: any, index)
	end

	return snapshot, count
end

-- ================================= API ==================================

const Vow = {}

--[=[
	Creates a pending Vow and passes its integer handle to the executor.

	The executor receives no resolve or reject closures. It must call the
	procedural API using the supplied handle.

	If the executor throws, the Vow is rejected with the thrown value.

	@param executor Executor -- function receiving the new Vow handle
	@return Vow -- a generation-tagged integer handle
]=]
@native
function Vow.new(executor: Executor): Vow
	if type(executor) ~= "function" then error("Vow.new: executor must be a function", 2) end

	-- Since the executor may yield, using the id may be unsafe, so tryDecode is used instead
	const _, handle = acquireVow()
	const ok, err = pcall(executor, handle)

	if not ok then
		const currentId = tryDecode(handle)
		if currentId ~= nil and buffer.readu8(vowStates, currentId) == STATE_PENDING and buffer.readu32(vowAdopts, currentId * 4) == 0 then
			settle(currentId, STATE_REJECTED, err)
		end
	end

	return handle
end

--[=[
	Creates a Vow (same as Vow.new) but automatically attaches a Vow.finally
	that runs Vow.destroyChain. 
	
	Cleanup is deferred by one scheduler step after settlement. Callers may
	attach listeners in that window; any andThen children created in the
	window will be destroyed along with the parent. Rejections on the auto
	Vow do not raise unhandled-rejection errors; rejections on any andThen
	children still do.

	@param executor Executor -- function receiving the new Vow handle
	@return Vow -- a generation-tagged integer handle that automatically cleans itself up after settling.
]=]
@native
function Vow.newAuto(executor: Executor): Vow
	if type(executor) ~= "function" then error("Vow.newAuto: executor must be a function", 2) end

	const id = Vow.new(executor)
	const slot = tryDecode(id)
	if slot ~= nil then buffer.writeu8(vowHandled, slot, 1) end -- Suppress unhandled raise

	if buffer.readu8(vowStates, id) == STATE_PENDING then
		Vow.finally(id, function()
			if Vow.isAlive(id) then Vow.destroyChain(id) end
		end)
	else
		-- Already settled, defer so the caller gets a live handle for one tick
		task.defer(function()
			if Vow.isAlive(id) then Vow.destroyChain(id) end
		end)
	end

	return id
end

--[=[
	Resolves a pending Vow with one value.

	If value is another live Vow, this Vow adopts that Vow's eventual
	state and value. Direct and indirect adoption cycles reject instead
	of hanging. If the value is a number, it may conflict with live Vow handles;
	use Vow.resolveRaw to skip this adoption step safely.

	@param id Vow -- the Vow handle to resolve
	@param value any -- the single fulfillment value or another Vow
]=]
@native
function Vow.resolve<T>(id: Vow<T>, value: T | Vow): ()
	const slot = decode(id, "resolve")
	resolveValue(slot, value)
end

--[=[
	Resolves a pending Vow with one value, strictly bypassing any Vow adoption checks.
	Use this when your fulfillment value could be an integer matching a Vow handle.

	@param id Vow -- the Vow handle to resolve
	@param value any -- the raw fulfillment value
]=]
@native
function Vow.resolveRaw<T>(id: Vow<T>, value: T): ()
	const slot = decode(id, "resolveRaw")

	if buffer.readu8(vowStates, slot) ~= STATE_PENDING then return end

	if buffer.readu32(vowAdopts, slot * 4) ~= 0 then return end

	settle(slot, STATE_RESOLVED, value)
end

--[=[
	Rejects a pending Vow with exactly one value.

	If no rejection handler is attached before the deferred check runs,
	the rejection value is raised asynchronously.

	@param id Vow -- the Vow handle to reject
	@param value any -- the single rejection value
]=]
@native
function Vow.reject<_, E>(id: Vow<_, E>, value: E): ()
	const slot = decode(id, "reject")

	if buffer.readu8(vowStates, slot) ~= STATE_PENDING then return end

	if buffer.readu32(vowAdopts, slot * 4) ~= 0 then return end

	settle(slot, STATE_REJECTED, value)
end

--[=[
	Attaches fulfillment and rejection callbacks and returns a new child Vow.

	A nil callback propagates the corresponding value. Callback errors
	reject the child Vow with the thrown value. A Vow returned from a
	callback is adopted by the child Vow.

	@param id Vow -- the parent Vow handle
	@param onResolved function? -- fulfillment callback
	@param onRejected function? -- rejection callback
	@return Vow -- a new child Vow handle
]=]
@native
function Vow.andThen<T, E, R, R_e>(id: Vow<T, E>, onResolved: Handler<T, R>?, onRejected: Handler<E, R_e>?): Vow<R | R_e>
	const parent = decode(id, "andThen")

	if onResolved ~= nil and type(onResolved) ~= "function" then error("Vow.andThen: onResolved must be a function or nil", 2) end

	if onRejected ~= nil and type(onRejected) ~= "function" then error("Vow.andThen: onRejected must be a function or nil", 2) end

	const childId, child = acquireVow()
	linkChild(parent, childId)

	const state = buffer.readu8(vowStates, parent)
	if state == STATE_PENDING then
		makeNode(NODE_CALLBACK, parent, childId, 0, onResolved, onRejected, child, nil)
	elseif state == STATE_RESOLVED then
		invokeCallback(onResolved, vowValues[parent + 1], child, false)
	elseif state == STATE_REJECTED then
		buffer.writeu8(vowHandled, parent, 1)
		invokeCallback(onRejected, vowValues[parent + 1], child, true)
	elseif state == STATE_CANCELLED then
		cancelInternal(child, true)
	end

	return child
end

--[=[
	Attaches a rejection callback.

	This is shorthand for andThen(id, nil, onRejected).

	@param id Vow -- the parent Vow handle
	@param onRejected function -- rejection callback
	@return Vow -- a new child Vow handle
]=]
@native
function Vow.catch<_, E, R_e>(id: Vow, onRejected: (value: E) -> R_e): Vow<R_e>
	if type(onRejected) ~= "function" then error("Vow.catch: onRejected must be a function", 2) end

	return Vow.andThen(id, nil, onRejected)
end

--[=[
    Attaches a callback invoked exactly once when this Vow settles
    (resolved, rejected, or cancelled). The callback receives (true, value)
	on resolve, (false, rejectionValue) on reject, and (false, nil) on cancel.
	destroying does not execute finally callbacks. The callback's return value
	is ignored. Errors thrown by the callback are deferred and raised
	asynchronously.

    Does not allocate a child Vow and is not subject to cancellation
    (it always fires if the Vow settles for any reason).

	Callbacks run synchronously inside dispatch and may yield, which suspends
	the caller of Vow.resolve / Vow.Reject / Vow.cancel. Use task.spawn inside
	the callback if you do not want this.

    @param id Vow
    @param callback (ok: boolean, value: any) -> ()
]=]
@native
function Vow.finally<T, E>(id: Vow<T, E>, callback: (ok: boolean, value: T?) -> ()): ()
	if type(callback) ~= "function" then error("Vow.finally: callback must be a function", 2) end

	const slot = decode(id, "finally")
	const state = buffer.readu8(vowStates, slot)

	if state == STATE_PENDING then
		makeFinallyNode(slot, callback)
		return
	end

	-- Already settled: spawn to avoid re-enterant dispatch from the caller's frame
	const ok, value = (state == STATE_RESOLVED), vowValues[slot + 1]
	task.spawn(function()
		const success, err = pcall(callback, ok, value)
		if not success then task.defer(error, err, 0) end
	end)
end

--[=[
	Yields the current thread while the Vow is pending.

	Returns true and the fulfillment value when resolved. Returns false
	and the rejection value when rejected. Returns false, nil when the
	Vow is cancelled or destroyed while this thread waits.

	@param id Vow -- the Vow handle to await
	@return boolean -- true when resolved, false otherwise
	@return any -- the fulfillment or rejection value
]=]
function Vow.await<T>(id: Vow<T>): (boolean, T?) -- Using same type semantics as pcall
	const slot = decode(id, "await")
	const state = buffer.readu8(vowStates, slot)

	if state == STATE_RESOLVED then
		return true, vowValues[slot + 1]
	elseif state == STATE_REJECTED then
		buffer.writeu8(vowHandled, slot, 1)
		return false, vowValues[slot + 1]
	elseif state == STATE_CANCELLED then
		return false, nil
	end

	if not coroutine.isyieldable() then error("Vow.await: cannot await in a non-yieldable thread", 2) end

	makeNode(NODE_AWAIT, slot, nil, 0, nil, nil, nil, coroutine.running())

	return coroutine.yield()
end

--[=[
	Functions like await, but raises an error if the Vow is rejected or cancelled.

	@param id Vow -- the Vow handle to await
	@return any -- the fulfillment or rejection value
]=]
function Vow.expect<T>(id: Vow<T>): T
	const slot = decode(id, "await")
	const state = buffer.readu8(vowStates, slot)

	if state == STATE_RESOLVED then
		return vowValues[slot + 1]
	elseif state == STATE_REJECTED then
		buffer.writeu8(vowHandled, slot, 1)
		error(`Vow.expect: Vow was rejected with error value: {vowValues[slot + 1]}`, 2)
	elseif state == STATE_CANCELLED then
		error("Vow.expect: Vow was cancelled", 2)
	end

	if not coroutine.isyieldable() then error("Vow.expect: cannot expect in a non-yieldable thread", 2) end

	makeNode(NODE_AWAIT, slot, nil, 0, nil, nil, nil, coroutine.running())

	return coroutine.yield()
end

--[=[
	Cancels a pending Vow.

	Cancellation is silent, wakes awaiters with (false, nil), recursively
	cancels pending procedural children and dependent aggregates, detaches
	from any inputs without cancelling them. The cancelled Vow remains
	alive in a cancelled state until explicitly destroyed.

	@param id Vow -- the Vow handle to cancel
]=]
function Vow.cancel(id: Vow): ()
	decode(id, "cancel")
	cancelInternal(id, true)
end

--[=[
	Releases a Vow and all of its listener nodes without triggering any
	listener logic. Awaiting threads are woken with (false, nil).

	Developers MUST call this when a Vow is completely finished. Settled
	Vows remain alive and retain their values until explicitly destroyed.
	Destroying a pending Vow will seamlessly trigger cancellation recursively
	before destroying it.

	@param handle Vow -- the Vow handle to destroy
]=]
function Vow.destroy(handle: Vow): ()
	local slot = decode(handle, "destroy")

	if buffer.readu8(vowStates, slot) == STATE_PENDING then
		cancelInternal(handle, false)
		slot = decode(handle, "destroy")
	end

	destroyInternal(slot)
end

--[=[
	Functions like destroy, but also destroys any Vows that depend on it.
	This only targets vows chained with Vow.andThen or Vow.catch, adopted
	vows are not counted.

	Does not trigger finally callbacks, and wakes awaiters with (false, nil).

	@param handle Vow -- the Vow handle to destroy
]=]
function Vow.destroyChain(handle: Vow)
	destroyChainInternal(decode(handle, "destroyChain"))
end

--[=[
	Resolves when every Vow in the array resolves.

	The returned array preserves input order. It includes an `n` field
	for the total count of inputs, enabling safe iteration when values are nil.
	The returned Vow rejects immediately when any input rejects, and is
	cancelled when any input is cancelled. An empty input resolves with
	an empty array.

	Every input is validated BEFORE the aggregate is allocated, so an
	invalid or sparse array never leaks a Vow slot.

	@param vows {Vow} -- input Vow handles
	@return Vow -- aggregate Vow
]=]
function Vow.all<T, E>(vows: { Vow<T, E> }): Vow<{ [number]: T, n: number }, E>
	const snapshot, count = validateInputs(vows, "all")

	const parent, result = acquireVow()
	const results = table.create(count) :: any
	results.n = count

	vowAggregateResults[parent + 1] = results
	buffer.writeu8(vowAggregateModes, parent, AGG_ALL)
	buffer.writeu32(vowAggregateRemaining, parent * 4, count)

	if count == 0 then
		settle(parent, STATE_RESOLVED, results)
		return result
	end

	for index = 1, count do
		const inputId = tryDecode(snapshot[index])

		if inputId == nil then continue end

		const state = buffer.readu8(vowStates, inputId)

		if state == STATE_PENDING then
			makeNode(NODE_AGGREGATE, inputId, parent, index, nil, nil, result, nil)
		elseif state == STATE_RESOLVED then
			aggregateStep(result, STATE_RESOLVED, vowValues[inputId + 1], index)
		elseif state == STATE_REJECTED then
			buffer.writeu8(vowHandled, inputId, 1)
			aggregateStep(result, STATE_REJECTED, vowValues[inputId + 1], index)
			break
		elseif state == STATE_CANCELLED then
			cancelInternal(result, true)
			break
		end
	end

	return result
end

--[=[
	Settles as soon as the first Vow in the array settles.

	An empty input remains pending. Input rejection propagates as
	rejection, input resolution propagates as resolution, and input
	cancellation cancels the race.

	Every input is validated BEFORE the aggregate is allocated.

	@param vows {Vow} -- input Vow handles
	@return Vow -- race Vow
]=]
function Vow.race<T, E>(vows: { Vow<T, E> }): Vow<T, E>
	const snapshot, count = validateInputs(vows, "race")

	const parent, result = acquireVow()

	buffer.writeu8(vowAggregateModes, parent, AGG_RACE)

	for index = 1, count do
		const inputId = tryDecode(snapshot[index])

		if inputId == nil then continue end

		const state = buffer.readu8(vowStates, inputId)

		if state == STATE_PENDING then
			makeNode(NODE_AGGREGATE, inputId, parent, index, nil, nil, result, nil)
		elseif state == STATE_RESOLVED then
			settle(parent, STATE_RESOLVED, vowValues[inputId + 1])
			break
		elseif state == STATE_REJECTED then
			buffer.writeu8(vowHandled, inputId, 1)
			settle(parent, STATE_REJECTED, vowValues[inputId + 1])
			break
		elseif state == STATE_CANCELLED then
			cancelInternal(result, true)
			break
		end
	end

	return result
end

--[=[
	Checks whether a Vow handle is alive and not stale.

	@param id Vow -- any value
	@return boolean -- true when the handle addresses a live Vow
]=]
@native
function Vow.isAlive(id: Vow): boolean
	return tryDecode(id) ~= nil
end

--[=[
	Diagnostics for pool pressure and live counts.

	@return VowStats
]=]
function Vow.stats(): VowStats
	return {
		vowCapacity = vowCapacity,
		vowLive = vowCount - vowFreeLength - vowRetired,
		vowFree = vowFreeLength,
		vowRetired = vowRetired,
		nodeCapacity = nodeCapacity,
		nodeActive = nodeCount - nodeFreeLength,
		nodeFree = nodeFreeLength,
	}
end

--[=[
	Pre-allocates capacity for Vows and Nodes to prevent runtime memory reallocations.
	Use this at server startup if you know you will need a massive amount of Vows.
]=]
function Vow.reserve(vows: number, nodes: number)
	if type(vows) ~= "number" or vows < 0 or vows % 1 ~= 0 then error("Vow.reserve: vows must be a non-negative integer", 2) end

	if type(nodes) ~= "number" or nodes < 0 or nodes % 1 ~= 0 then error("Vow.reserve: nodes must be a non-negative integer", 2) end

	if vows > SLOT_ID_SPACE then error(`Vow.reserve: vows cannot exceed the maximum slot limit ({SLOT_ID_SPACE})`, 2) end

	if nodes > MAX_NODES then error(`Vow.reserve: nodes cannot exceed the maximum node limit ({MAX_NODES})`, 2) end

	if vows > vowCapacity then growVowsTo(vows) end
	if nodes > nodeCapacity then growNodesTo(nodes) end
end

table.freeze(Vow)

return Vow
