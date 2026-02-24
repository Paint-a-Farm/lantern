-- Guard clause: `if cond then return end; body` should not be negated to
-- `if not cond then body end` because that flips JumpIfNot → JumpIf.
function guardReturn(x, y)
	if x then
		return
	end
	return y + 1
end

function guardBreak(items)
	local sum = 0
	for _, v in ipairs(items) do
		if v < 0 then
			break
		end
		sum = sum + v
	end
	return sum
end

function guardContinue(items)
	local sum = 0
	for _, v in ipairs(items) do
		if v < 0 then
			continue
		end
		sum = sum + v
	end
	return sum
end
