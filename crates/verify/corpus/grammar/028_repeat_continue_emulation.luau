-- repeat-until with branch-heavy control flow
local i = 0
local acc = 0
repeat
    i += 1
    if i % 2 == 1 then
        acc += i
    end
until i >= 7
return acc
