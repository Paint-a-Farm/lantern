-- explicit return path integrity in branches
local function absLike(x: number): number
    if x >= 0 then
        return x
    end
    return -x
end

return absLike(-4), absLike(7)
