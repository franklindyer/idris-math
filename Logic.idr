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

-- -- -- -- -- -- -- --
-- DOUBLE NEGATION   --
-- -- -- -- -- -- -- --

data NotNot : Type -> Type where
    DN : ((a -> Void) -> Void) -> NotNot a

dneg : a -> NotNot a
dneg x = DN (\nx => nx x)

unwrapNotNot : NotNot a -> (a -> Void) -> Void
unwrapNotNot (DN nnx) = nnx

reduceNotNot : NotNot (NotNot a) -> NotNot a
reduceNotNot (DN nnnnx) = DN (\nx => nnnnx $ \nnx => unwrapNotNot nnx $ nx)

public export
Functor NotNot where
    map f (DN nnx) = DN $ nnx . (. f)

Applicative NotNot where
    pure x                  = DN (\no => no x)
    (<*>) (DN nnf) (DN nnx) = DN (\ny => nnf (\f => nnx $ (. f) ny))

Monad NotNot where
    (>>=) nnx kf = reduceNotNot $ map kf nnx

notNotDec : (a : Type) -> NotNot (Dec a)
notNotDec a = DN (\nd => (nd . No) (nd . Yes))

