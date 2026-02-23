-- call argument grammar: (), string, table literal
local function f(...)
    return ...
end

local a = f(1, 2, 3)
local b = f"hello"
local c = f{value = 7}
return a, b, c.value
