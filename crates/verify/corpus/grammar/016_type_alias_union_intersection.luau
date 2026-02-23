-- type aliases with union/intersection table types
type Point = { x: number, y: number }
type Named = { name: string }
type NamedPoint = Point & Named

local p: NamedPoint = { x = 1, y = 2, name = "pt" }
return p.x + p.y
