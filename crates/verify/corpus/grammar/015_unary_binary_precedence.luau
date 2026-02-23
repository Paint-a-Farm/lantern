-- unary/binary operator precedence and associativity
local x = -3 + 10 / 2 ^ 2 .. ""
local y = not false and (1 < 2 or 3 < 2)
return x, y
