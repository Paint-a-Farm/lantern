-- short-circuit boolean value pattern (a and b or c)
local calls = 0
local function touch(v)
    calls += 1
    return v
end

local x = touch(false) and touch(1) or touch(2)
return x, calls
