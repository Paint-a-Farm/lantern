-- If-else: condition polarity must be preserved. The compiler emits JumpIfNot
-- for `if x then A else B end`. Negating the condition would flip the opcode.
function ifElse(x)
	if x then
		return 1
	else
		return 2
	end
end

function ifElseNested(x, y)
	if x then
		if y then
			return "both"
		else
			return "xonly"
		end
	else
		return "neither"
	end
end
