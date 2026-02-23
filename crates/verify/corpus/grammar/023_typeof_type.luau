-- typeof type syntax
local v = { x = 1 }
type V = typeof(v)
local c: V = { x = 2 }
return c.x
