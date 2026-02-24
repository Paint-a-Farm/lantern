-- Regression: table fold must not fold when variable has multiple uses.
--
-- Sequential writes `t = {}; t.name = val` compile to NewTable in the
-- variable's register. Constructor `t = { ["name"] = val }` uses a temp
-- register + Move. For multi-use variables, the sequential form is correct.

function makeTable(name, color)
	local t = {}
	t.name = name
	t.color = color
	print(t)
	return t
end
