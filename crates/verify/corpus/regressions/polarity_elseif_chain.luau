-- Nested if-else preserving polarity at each level
function nestedIfElse(a, b)
	if a then
		if b then
			return "both"
		end
		return "a_only"
	end
	return "none"
end

-- If-elseif chain: each branch condition has its own polarity
function ifElseifChain(x)
	if x > 10 then
		return "big"
	elseif x > 0 then
		return "small"
	elseif x == 0 then
		return "zero"
	else
		return "negative"
	end
end

-- Guard with early return value using `not`
function guardReturnValue(enabled, data)
	if not enabled then
		return nil
	end
	return data.value
end
