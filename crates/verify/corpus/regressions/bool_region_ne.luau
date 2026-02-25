-- Boolean region: comparison-based boolean value computation.
-- The compiler generates LOADB false,+1 / LOADB true pairs.
-- JumpIfNotEq targeting true_pc means "true when not-equal" → source is ~=.
-- Previously we emitted == instead of ~= (semantic bug).

function isNotEqual(a, b)
	return a ~= b
end

function isEqual(a, b)
	return a == b
end

function isLess(a, b)
	return a < b
end

function isLessEq(a, b)
	return a <= b
end

-- AND chain with boolean result
function bothEqual(a, b, c, d)
	return a == b and c == d
end

-- OR chain with boolean result
function eitherNotEqual(a, b, c, d)
	return a ~= b or c ~= d
end
