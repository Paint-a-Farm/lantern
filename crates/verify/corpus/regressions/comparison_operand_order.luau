-- Comparison negation must swap operands, not wrap in `not(...)`.
--
-- When the structurer inverts `0 < x` it must produce `x <= 0`
-- (JUMPIFNOTLE with swapped operands), not `not(0 < x)` which
-- produces JUMPIFLT with the same operand order — a different opcode.
--
-- The Luau compiler normalises > to < and >= to <= by swapping:
--   `0 < x`         →  JUMPIFNOTLT(0, x)
--   `x > 0`         →  JUMPIFNOTLT(0, x)   (same)
--   `x >= 0`        →  JUMPIFNOTLE(0, x)   (swapped to 0 <= x)
--   `0 <= x`        →  JUMPIFNOTLE(0, x)   (same)
--   `not(0 < x)`    →  JUMPIFLT(x, 0)      (DIFFERENT opcode!)
--   `not(x < 0)`    →  JUMPIFLT(0, x)      (DIFFERENT opcode!)

-- Guard using `0 < direction`; negation should be `direction <= 0`
function guardLtConst(direction)
	if 0 < direction then
		return 1
	end
	return 0
end

-- Guard using `direction >= 0`; negation should be `0 > direction` = `direction < 0`
function guardGeConst(direction)
	if direction >= 0 then
		return 3
	end
	return 0
end

-- Negated form: `not(direction < 0)` produces JUMPIFLT — distinct from above
function guardNotLt(direction)
	if not (direction < 0) then
		return 4
	end
	return 0
end

-- Compound condition with mixed comparison directions
function compoundMixed(a, b, limit)
	if a > 0 and b < limit then
		return a + b
	end
	return 0
end

-- Or-chain with comparisons (the Animation fn#14 pattern)
function orChainComparisons(direction, fraction, targetRad, position, wrapPosition)
	if (0 < direction and 0.2 < math.abs(fraction)) or (direction < 0 and math.abs(fraction) < 0.2) or math.abs(targetRad - position) < wrapPosition * 0.5 then
		return 1
	end
	return 0
end
