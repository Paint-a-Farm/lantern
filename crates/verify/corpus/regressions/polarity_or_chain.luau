-- Or-chain: `if A or B or C then body end` must preserve polarity.
-- Each OR clause may use different branch opcodes.
function orChain(a, b, c)
	if a or b or c then
		return "any"
	end
	return "none"
end

-- Mixed and/or chain as seen in Animation.l64
function mixedAndOr(direction, fraction, targetRad, position, wrapPosition)
	if (0 < direction and 0.2 < math.abs(fraction)) or (direction < 0 and math.abs(fraction) < 0.2) or math.abs(targetRad - position) < wrapPosition * 0.5 then
		return true
	end
	return false
end
