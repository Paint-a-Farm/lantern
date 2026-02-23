-- generic function declaration and explicit type args
local function id<T>(x: T): T
    return x
end

local n: number = id(5)
return n
