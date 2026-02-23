-- table indexer type syntax
type Dict = { [string]: number }
local d: Dict = { a = 1, b = 2 }
d["c"] = 3
return d.a + d.b + d.c
