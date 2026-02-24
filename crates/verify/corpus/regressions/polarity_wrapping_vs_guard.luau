-- Wrapping form: `if cond then body end` (JumpIfNotLt) vs
-- Guard form: `if NOT(cond) then continue end; body` (JumpIfLt)
-- The negated flag from the original opcode determines which form to use.

-- Wrapping form: condition true → execute body
function wrappingContinue(items)
	local sum = 0
	for _, v in ipairs(items) do
		if #v > 0 then
			sum = sum + v[1]
		end
	end
	return sum
end

-- Guard form: condition true → skip iteration
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

-- Guard form with break
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

-- Wrapping form with break (body guarded by positive condition)
function wrappingBreak(items)
	local found = nil
	for _, v in ipairs(items) do
		if v > 10 then
			found = v
		end
	end
	return found
end
