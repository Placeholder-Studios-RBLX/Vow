const Vow = require("../src/vow")
const test = require("@std/test")

const tracked: { number } = {}

const function track(id: number): number
	table.insert(tracked, id)
	return id
end

const function pending(): number
	return track(Vow.new(function() end))
end

const function resolved(value: any): number
	const id = pending()
	Vow.resolveRaw(id, value)
	return id
end

test.suite("Vow", function(suite)
	suite:beforeEach(function()
		table.clear(tracked)
	end)

	suite:afterEach(function()
		for index = #tracked, 1, -1 do
			const id = tracked[index]
			if Vow.isAlive(id) then Vow.destroy(id) end
		end
	end)

	suite:case("new executes executor and returns a live pending handle", function(asserts)
		local called = false
		const id = track(Vow.new(function(executorId)
			called = true
			Vow.resolveRaw(executorId, "ready")
		end))

		asserts.eq(true, called)
		asserts.eq(true, Vow.isAlive(id))
		const ok, value = Vow.await(id)
		asserts.eq(true, ok)
		asserts.eq("ready", value)
	end)

	suite:case("new rejects when its executor throws", function(asserts)
		const id = track(Vow.new(function()
			error("executor failed")
		end))

		const ok, reason = Vow.await(id)
		asserts.eq(false, ok)
		asserts.strContains(tostring(reason), "executor failed")
	end)

	suite:case("new validates executor", function(asserts)
		asserts.throws(function()
			Vow.new(nil :: any)
		end)
	end)

	suite:case("newAuto creates a live pending handle", function(asserts)
		const id = track(Vow.newAuto(function() end))
		asserts.eq(true, Vow.isAlive(id))
	end)

	suite:case("newAuto returns an already-settled handle before deferred cleanup", function(asserts)
		const id = track(Vow.newAuto(function(executorId)
			Vow.resolveRaw(executorId, "done")
		end))

		asserts.eq(true, Vow.isAlive(id))
		asserts.eq("done", Vow.expect(id))
	end)

	suite:case("newAuto tolerates its executor destroying the Vow", function(asserts)
		const id = track(Vow.newAuto(function(executorId)
			Vow.destroy(executorId)
		end))

		asserts.eq(false, Vow.isAlive(id))
	end)

	suite:case("newAuto validates executor", function(asserts)
		asserts.throws(function()
			Vow.newAuto(nil :: any)
		end)
	end)

	suite:case("resolveRaw preserves nil and ignores later settlement", function(asserts)
		const id = pending()
		Vow.resolveRaw(id, nil)
		Vow.resolveRaw(id, "ignored")

		const ok, value = Vow.await(id)
		asserts.eq(true, ok)
		asserts.eq(nil, value)
	end)

	suite:case("resolveRaw does not adopt a numeric value that is a live handle", function(asserts)
		const other = pending()
		const id = pending()
		Vow.resolveRaw(id, other)

		const ok, value = Vow.await(id)
		asserts.eq(true, ok)
		asserts.eq(other, value)
	end)

	suite:case("resolve adopts a pending Vow", function(asserts)
		const source = pending()
		const target = pending()
		Vow.resolve(target, source)
		Vow.resolveRaw(source, "adopted")

		const ok, value = Vow.await(target)
		asserts.eq(true, ok)
		asserts.eq("adopted", value)
	end)

	suite:case("resolve rejects direct and indirect adoption cycles", function(asserts)
		const direct = pending()
		Vow.resolve(direct, direct)
		const directOk, directReason = Vow.await(direct)
		asserts.eq(false, directOk)
		asserts.strContains(tostring(directReason), "itself")

		const first = pending()
		const second = pending()
		Vow.resolve(first, second)
		Vow.resolve(second, first)
		const cycleOk, cycleReason = Vow.await(second)
		asserts.eq(false, cycleOk)
		asserts.strContains(tostring(cycleReason), "cycle")
	end)

	suite:case("reject propagates its reason through await", function(asserts)
		const id = pending()
		Vow.reject(id, "failure")

		const ok, reason = Vow.await(id)
		asserts.eq(false, ok)
		asserts.eq("failure", reason)
	end)

	suite:case("andThen transforms values synchronously", function(asserts)
		const parent = resolved(4)
		const child = track(Vow.andThen(parent, function(value)
			return value * 3
		end))

		asserts.eq(12, Vow.expect(child))
	end)

	suite:case("andThen propagates values when callbacks are omitted", function(asserts)
		const parent = resolved("value")
		const child = track(Vow.andThen(parent, nil, nil))
		asserts.eq("value", Vow.expect(child))

		const rejected = pending()
		const rejectionChild = track(Vow.andThen(rejected, nil, nil))
		Vow.reject(rejected, "reason")
		const ok, reason = Vow.await(rejectionChild)
		asserts.eq(false, ok)
		asserts.eq("reason", reason)
	end)

	suite:case("andThen invokes pending callbacks on settlement", function(asserts)
		const parent = pending()
		local called = false
		const child = track(Vow.andThen(parent, function(value)
			called = true
			return value .. "!"
		end))

		Vow.resolveRaw(parent, "hello")
		asserts.eq(true, called)
		asserts.eq("hello!", Vow.expect(child))
	end)

	suite:case("andThen adopts a Vow returned by its callback", function(asserts)
		const adopted = pending()
		const parent = resolved("start")
		const child = track(Vow.andThen(parent, function()
			return adopted
		end))
		Vow.resolveRaw(adopted, "finished")

		asserts.eq("finished", Vow.expect(child))
	end)

	suite:case("andThen rejects its child when a callback throws", function(asserts)
		const child = track(Vow.andThen(resolved(1), function()
			error("callback failed")
		end))

		const ok, reason = Vow.await(child)
		asserts.eq(false, ok)
		asserts.strContains(tostring(reason), "callback failed")
	end)

	suite:case("andThen validates callbacks", function(asserts)
		const id = pending()
		asserts.throws(function()
			Vow.andThen(id, true :: any, nil)
		end)
		asserts.throws(function()
			Vow.andThen(id, nil, true :: any)
		end)
	end)

	suite:case("catch recovers from rejection", function(asserts)
		const parent = pending()
		const child = track(Vow.catch(parent, function(reason)
			return "recovered: " .. reason
		end))
		Vow.reject(parent, "failure")

		asserts.eq("recovered: failure", Vow.expect(child))
	end)

	suite:case("catch validates its handler", function(asserts)
		asserts.throws(function()
			Vow.catch(pending(), nil :: any)
		end)
	end)

	suite:case("finally runs once with the settled outcome", function(asserts)
		const id = pending()
		local calls = 0
		local resultOk = false
		local resultValue: any = nil
		Vow.finally(id, function(ok, value)
			calls += 1
			resultOk = ok
			resultValue = value
		end)
		Vow.resolveRaw(id, "done")

		asserts.eq(1, calls)
		asserts.eq(true, resultOk)
		asserts.eq("done", resultValue)
	end)

	suite:case("finally runs on rejection and cancellation", function(asserts)
		const rejected = pending()
		local rejectedOk: boolean? = nil
		Vow.finally(rejected, function(ok)
			rejectedOk = ok
		end)
		Vow.reject(rejected, "failure")
		asserts.eq(false, rejectedOk)

		const cancelled = pending()
		local cancelledOk: boolean? = nil
		local cancelledValue: any = "not nil"
		Vow.finally(cancelled, function(ok, value)
			cancelledOk = ok
			cancelledValue = value
		end)
		Vow.cancel(cancelled)
		asserts.eq(false, cancelledOk)
		asserts.eq(nil, cancelledValue)
	end)

	suite:case("finally validates callback", function(asserts)
		asserts.throws(function()
			Vow.finally(pending(), nil :: any)
		end)
	end)

	suite:case("await returns settled fulfillment and rejection", function(asserts)
		const fulfilled = resolved("yes")
		const ok, value = Vow.await(fulfilled)
		asserts.eq(true, ok)
		asserts.eq("yes", value)

		const rejected = pending()
		Vow.reject(rejected, "no")
		const rejectedOk, reason = Vow.await(rejected)
		asserts.eq(false, rejectedOk)
		asserts.eq("no", reason)
	end)

	suite:case("expect returns fulfillment and raises on rejection or cancellation", function(asserts)
		asserts.eq("value", Vow.expect(resolved("value")))

		const rejected = pending()
		Vow.reject(rejected, "broken")
		asserts.throwsWith("Vow.expect: Vow was rejected with error value: broken", function()
			Vow.expect(rejected)
		end)

		const cancelled = pending()
		Vow.cancel(cancelled)
		asserts.throwsWith("Vow.expect: Vow was cancelled", function()
			Vow.expect(cancelled)
		end)
	end)

	suite:case("cancel recursively cancels children", function(asserts)
		const parent = pending()
		const child = track(Vow.andThen(parent, function()
			return "unreachable"
		end))
		Vow.cancel(parent)

		asserts.throwsWith("Vow.expect: Vow was cancelled", function()
			Vow.expect(child)
		end)
		asserts.eq(true, Vow.isAlive(parent))
		asserts.eq(true, Vow.isAlive(child))
	end)

	suite:case("cancel is idempotent and does not cancel adopted input", function(asserts)
		const source = pending()
		const target = pending()
		Vow.resolve(target, source)
		Vow.cancel(target)
		Vow.cancel(target)

		asserts.eq(true, Vow.isAlive(source))
		Vow.resolveRaw(source, "source still works")
		asserts.eq("source still works", Vow.expect(source))
	end)

	suite:case("destroy releases handles and recycled handles reject stale access", function(asserts)
		const old = pending()
		Vow.destroy(old)
		asserts.eq(false, Vow.isAlive(old))

		const fresh = pending()
		asserts.neq(old, fresh)
		asserts.eq(true, Vow.isAlive(fresh))
		asserts.throws(function()
			Vow.resolveRaw(old, "stale")
		end)
	end)

	suite:case("destroyChain destroys descendants without destroying adopted inputs", function(asserts)
		const parent = pending()
		const child = track(Vow.andThen(parent, function(value)
			return value
		end))
		const grandchild = track(Vow.andThen(child, function(value)
			return value
		end))
		const adoptedInput = pending()
		const adoptingChild = track(Vow.andThen(parent, function()
			return adoptedInput
		end))
		Vow.resolveRaw(parent, "value")
		Vow.destroyChain(parent)

		asserts.eq(false, Vow.isAlive(parent))
		asserts.eq(false, Vow.isAlive(child))
		asserts.eq(false, Vow.isAlive(grandchild))
		asserts.eq(false, Vow.isAlive(adoptingChild))
		asserts.eq(true, Vow.isAlive(adoptedInput))
	end)

	suite:case("all resolves in input order and preserves nil values", function(asserts)
		const first = resolved("first")
		const middle = pending()
		const last = resolved("last")
		const aggregate = track(Vow.all({ first, middle, last }))
		Vow.resolveRaw(middle, nil)

		const values = Vow.expect(aggregate)
		asserts.eq(3, values.n)
		asserts.eq("first", values[1])
		asserts.eq(nil, values[2])
		asserts.eq("last", values[3])
	end)

	suite:case("all resolves an empty list", function(asserts)
		const aggregate = track(Vow.all({}))
		const values = Vow.expect(aggregate)
		asserts.eq(0, values.n)
	end)

	suite:case("all rejects or cancels when an input does", function(asserts)
		const failing = pending()
		const rejectedAggregate = track(Vow.all({ failing }))
		Vow.reject(failing, "input failed")
		const ok, reason = Vow.await(rejectedAggregate)
		asserts.eq(false, ok)
		asserts.eq("input failed", reason)

		const cancelled = pending()
		const cancelledAggregate = track(Vow.all({ cancelled }))
		Vow.cancel(cancelled)
		asserts.eq(true, Vow.isAlive(cancelledAggregate))
		asserts.eq(false, Vow.await(cancelledAggregate))
	end)

	suite:case("all validates dense arrays and live handles before aggregation", function(asserts)
		const id = pending()
		asserts.throws(function()
			Vow.all(nil :: any)
		end)
		asserts.throws(function()
			Vow.all({ [1] = id, [3] = id })
		end)
		asserts.throws(function()
			Vow.all({ id, 42 :: any })
		end)
		asserts.throws(function()
			Vow.all({ [0] = id })
		end)
	end)

	suite:case("race settles with the first fulfillment or rejection", function(asserts)
		const first = pending()
		const second = pending()
		const aggregate = track(Vow.race({ first, second }))
		Vow.resolveRaw(second, "winner")
		Vow.resolveRaw(first, "later")
		asserts.eq("winner", Vow.expect(aggregate))

		const rejection = pending()
		const rejectedRace = track(Vow.race({ rejection }))
		Vow.reject(rejection, "race failed")
		const ok, reason = Vow.await(rejectedRace)
		asserts.eq(false, ok)
		asserts.eq("race failed", reason)
	end)

	suite:case("race with no inputs stays pending and cancels with a cancelled input", function(asserts)
		const emptyRace = track(Vow.race({}))
		asserts.eq(true, Vow.isAlive(emptyRace))
		Vow.cancel(emptyRace)
		asserts.throwsWith("Vow.expect: Vow was cancelled", function()
			Vow.expect(emptyRace)
		end)

		const cancelled = pending()
		const race = track(Vow.race({ cancelled }))
		Vow.cancel(cancelled)
		asserts.eq(false, Vow.await(race))
	end)

	suite:case("race validates sparse and invalid input arrays", function(asserts)
		const id = pending()
		asserts.throws(function()
			Vow.race({ [2] = id })
		end)
		asserts.throws(function()
			Vow.race({ id, {} :: any })
		end)
	end)

	suite:case("isAlive rejects non-handles, destroyed handles, and stale generations", function(asserts)
		const id = pending()
		Vow.destroy(id)
		asserts.eq(false, Vow.isAlive(id))
		asserts.eq(false, Vow.isAlive(nil :: any))
		asserts.eq(false, Vow.isAlive(0 :: any))
		asserts.eq(false, Vow.isAlive(1.5 :: any))
	end)

	suite:case("stats report live/free pool counts and reserve grows capacities", function(asserts)
		const before = Vow.stats()
		Vow.reserve(before.vowCapacity + 8, before.nodeCapacity + 8)
		const afterReserve = Vow.stats()
		asserts.that(afterReserve.vowCapacity >= before.vowCapacity + 8)
		asserts.that(afterReserve.nodeCapacity >= before.nodeCapacity + 8)

		const id = pending()
		const withLive = Vow.stats()
		asserts.eq(before.vowLive + 1, withLive.vowLive)
		Vow.destroy(id)
		asserts.that(Vow.stats().vowFree >= withLive.vowFree + 1)
	end)

	suite:case("reserve validates capacity arguments", function(asserts)
		asserts.throws(function()
			Vow.reserve(-1, 0)
		end)
		asserts.throws(function()
			Vow.reserve(0, 1.5)
		end)
		asserts.throws(function()
			Vow.reserve("many" :: any, 0)
		end)
	end)
end)
