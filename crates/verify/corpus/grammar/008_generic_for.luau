-- generic for-loop over custom iterator
local function iterFactory(values)
    local i = 0
    return function()
        i += 1
        if i <= #values then
            return i, values[i]
        end
        return nil
    end
end

local sum = 0
for _, v in iterFactory({1, 2, 3, 4}) do
    sum += v
end
return sum
