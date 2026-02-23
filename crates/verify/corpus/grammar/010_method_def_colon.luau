-- method syntax and colon calls
local Obj = {}
Obj.__index = Obj

function Obj:new(v)
    return setmetatable({v = v}, Obj)
end

function Obj:add(delta)
    self.v += delta
    return self.v
end

local o = Obj:new(10)
return o:add(5)
