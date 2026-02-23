-- Assignment statement forms and table lvalues
local a, b = 1, 2
a, b = b, a
local t = {}
t.x = a + b
t[a] = b
return t.x, t[a]
