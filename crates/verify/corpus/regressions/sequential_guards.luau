-- Sequential guard pattern: if cond then return end; if cond then return end; body
-- The compiler generates separate Return opcodes for each guard.
-- Previously the structurer merged these into if-elseif chains,
-- dropping the explicit returns and changing the opcode balance.

function twoGuards(a, b)
	if a == nil then
		return
	end
	if b == nil then
		return
	end
	print(a + b)
end

function guardWithBody(key, value)
	if key == nil then
		print("missing key")
		return
	end
	if value == nil then
		return
	end
	print(key, value)
end

-- If-else where both return should NOT be split into guards
function ifElseBothReturn(x)
	if x > 0 then
		return x
	else
		return -x
	end
end
