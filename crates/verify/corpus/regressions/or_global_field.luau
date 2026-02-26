-- Truthiness chain where the fallback value requires an intermediate register:
-- `val or GlobalTable.field`.  GetGlobal writes to a temp register above the
-- chain register; the truthy-chain detector must allow this.

SomeGlobal = { DEFAULT = 42 }

function orGlobalField(val)
	return val or SomeGlobal.DEFAULT
end
