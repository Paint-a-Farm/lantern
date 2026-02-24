-- AND-chain: `if A and B and C then body end` should preserve condition
-- polarity through the chain. Each condition in the chain uses JumpIf/JumpIfNot
-- and negating any one flips the opcode.
function andChain(a, b, c)
	if a and b and c then
		return "all"
	end
	return "not all"
end

function andChainWithElse(a, b, c)
	if a and b and c then
		return "all"
	else
		return "not all"
	end
end
