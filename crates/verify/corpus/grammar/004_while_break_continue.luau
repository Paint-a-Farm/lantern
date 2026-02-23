-- while loop with continue and break
local i = 0
local sum = 0
while i < 10 do
    i += 1
    if i % 2 == 0 then
        continue
    end
    if i > 7 then
        break
    end
    sum += i
end
return sum
