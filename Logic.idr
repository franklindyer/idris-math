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

total
public export
caseSplitYes : {y, n : b} ->
               (pf : Dec a) ->
               (x : a) ->
               (caseSplit (\_ => y) (\_ => n) pf = y)
caseSplitYes (Yes pf) x     = Refl
caseSplitYes (No pf) x      = exNihilo (pf x)

total
public export
caseSplitNo : {y, n : b} ->
              (pf : Dec a) ->
              (no : a -> Void) ->
              (caseSplit (\_ => y) (\_ => n) pf = n)
caseSplitNo (Yes pf) no = exNihilo (no pf)
caseSplitNo (No pf) no  = Refl
