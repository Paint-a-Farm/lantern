-- table constructor forms: array/hash/index keys
local k = "name"
local t = {
    1,
    2,
    [10] = 20,
    [k] = "lantern",
    flag = true,
}
return t[1], t[10], t[k], t.flag
