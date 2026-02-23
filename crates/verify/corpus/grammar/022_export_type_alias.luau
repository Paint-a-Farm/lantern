-- exported generic type alias syntax
export type Pair<T> = { first: T, second: T }
local p: Pair<number> = { first = 1, second = 2 }
return p.first + p.second
