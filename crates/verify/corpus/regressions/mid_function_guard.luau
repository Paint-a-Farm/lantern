-- Mid-function guard clause: if cond then body; return end; continuation
-- The compiler generates JUMPIFNOT over the guard body + RETURN,
-- then falls through to the continuation.
-- The structurer should emit the guard form, not wrap the continuation.

function midGuard(x, y)
	local a = x + 1
	local b = y + 2
	if a == 0 then
		print("a is zero")
		return
	end
	print(a + b)
	return a * b
end

-- Multiple guards in sequence
function multiGuard(x, y, z)
	local sum = x + y + z
	if x == nil then
		return
	end
	if y == nil then
		print("missing y")
		return
	end
	if z < 0 then
		print("negative z")
		return -1
	end
	print(sum)
	return sum * 2
end

-- Guard with complex body before return
function guardWithWork(config)
	local result = {}
	result.name = config.name
	if config.enabled == false then
		print("disabled")
		result.status = "off"
		return result
	end
	result.value = config.value * 2
	result.status = "on"
	return result
end
