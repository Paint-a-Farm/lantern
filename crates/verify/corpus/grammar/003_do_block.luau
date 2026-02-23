-- do-end block and block-local binding
local x = 1
do
    local y = 2
    x = x + y
end
return x
