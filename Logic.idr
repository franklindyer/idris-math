module Logic

total
public export
exNihilo : Void -> a

total
public export
piecewise : (a -> c) -> (b -> c) -> Either a b -> c
piecewise imp _ (Left x)    = imp x
piecewise _ imp (Right x)   = imp x

total
public export
caseSplit : (a -> b) -> ((a -> Void) -> b) -> Dec a -> b
caseSplit imp _ (Yes pf)    = imp pf
caseSplit _ imp (No pf)     = imp pf
