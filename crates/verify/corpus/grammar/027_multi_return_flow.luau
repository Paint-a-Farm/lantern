-- multi-return propagation through caller
local function pair(v)
    return v, v + 1
end

local function consume()
    local a, b = pair(10)
    return a * b
end

return consume()
