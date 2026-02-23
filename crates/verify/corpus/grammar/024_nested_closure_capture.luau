-- nested closure captures and mutation
local function makeCounter()
    local n = 0
    return function()
        n += 1
        return n
    end
end

local c = makeCounter()
return c(), c(), c()
