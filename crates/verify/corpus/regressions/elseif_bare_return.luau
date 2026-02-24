-- Regression: bare return in elseif must be preserved when else has valued return.
--
-- The strip_trailing_returns pass strips bare `return` at the end of
-- branches when the if-block is the last statement of a function.
-- But when a sibling branch (else) ends with `return <value>`, the
-- bare return changes compiler output: without it, the compiler adds
-- a Jump + trailing implicit Return instead of an inline Return.

function loadItem(data, name)
	local item, isMissing = createFromData(data)
	if isMissing then
		return
	elseif item == nil then
		warn("Could not create item '%s'!", name)
		return
	else
		register(item, name)
		return true
	end
end
