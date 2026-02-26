-- Boolean accumulator pattern: `acc = acc and expr` where the initial value
-- comes from a variable (Move), not a LoadB pre-init. The bool_region must
-- infer the chain type from JumpIfNot→end_pc (AND) or JumpIf→end_pc (OR).

function andAccumulator(items)
	local allValid = true
	for _, v in ipairs(items) do
		allValid = allValid and v > 0
	end
	return allValid
end

function orAccumulator(items)
	local anyValid = false
	for _, v in ipairs(items) do
		anyValid = anyValid or v > 0
	end
	return anyValid
end
