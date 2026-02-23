-- if/elseif/else statement chains
local function classify(v)
    if v < 0 then
        return "neg"
    elseif v == 0 then
        return "zero"
    else
        return "pos"
    end
end

return classify(-1), classify(0), classify(2)
