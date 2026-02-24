-- For-loop guard patterns: break and continue inside for loops
-- with various condition types.
function forBreakGuard(items)
	local sum = 0
	for i = 1, #items do
		if items[i] == nil then
			break
		end
		sum = sum + items[i]
	end
	return sum
end

function forContinueGuard(items)
	local sum = 0
	for i = 1, #items do
		if items[i] == nil then
			continue
		end
		sum = sum + items[i]
	end
	return sum
end

function whileBreakGuard(x)
	local count = 0
	while x > 0 do
		if x % 3 == 0 then
			break
		end
		count = count + 1
		x = x - 1
	end
	return count
end
