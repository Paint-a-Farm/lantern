-- `a or {default}` pattern: the table constructor in the fallback uses
-- temporary registers for element values, which must not be rejected by
-- `writes_multiple_registers`.

function simpleOrTable(val)
	local result = val or {1, 1, 1}
	return result
end

function orTableInAssign(attributes, xmlFile, key)
	attributes.color = xmlFile:getValue(key .. "#color", nil, true) or {1, 1, 1}
	return true
end

function orEmptyTable(val)
	local result = val or {}
	return result
end

function orNestedTable(val)
	local result = val or {x = 1, y = 2}
	return result
end
