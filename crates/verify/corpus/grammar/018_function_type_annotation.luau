-- function type annotation and typed anonymous function
type Mapper = (number) -> number

local function apply(f: Mapper, x: number): number
    return f(x)
end

return apply(function(v: number): number
    return v * 2
end, 21)
