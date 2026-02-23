-- Verified ground truth for Animation.l64 fn#14 (calculateTurnOffFadeTime)
-- Bytecode-verified: compiled output matches original instruction-for-instruction
--
-- Key patterns:
-- 1. Guard clause: `if cond then return 1 end` (compiler inverts to JumpIfNotLt)
-- 2. Short-circuit or-chain: three conditions merged into single `if (A) or (B) or (C)`
-- 3. Multi-return: `local int, fraction = math.modf(...)`
-- 4. Post-if shared computation: targetPos defined after the or-chain if-block

function calculateTurnOffFadeTime(currentSpeedFactor, currentSpeed, direction, position, targetPosition, originalFadeOut, wrapPosition, subDivisions)
	wrapPosition = wrapPosition / subDivisions
	local finalPos = position
	local speedChangePerMS = 1 / originalFadeOut
	for i = 1, originalFadeOut do
		currentSpeedFactor = math.max(currentSpeedFactor - speedChangePerMS, 0)
		finalPos = finalPos + currentSpeed * currentSpeedFactor
	end
	if math.abs(position - finalPos) < 0.00001 then
		return 1
	end
	local int, fraction = math.modf((finalPos - targetPosition) / wrapPosition)
	local targetRad = int * wrapPosition + targetPosition
	if (0 < direction and 0.2 < math.abs(fraction)) or (direction < 0 and math.abs(fraction) < 0.2) or math.abs(targetRad - position) < wrapPosition * 0.5 then
		int = int + direction
	end
	local targetPos = int * wrapPosition + targetPosition
	return (position - targetPos) / (position - finalPos) * originalFadeOut
end
