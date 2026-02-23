-- varargs and multi-return assignment
local function split(...)
    local a, b, c = ...
    return a, b, c
end

local x, y, z = split(1, 2, 3)
return x + y + z
