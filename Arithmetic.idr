module Arithmetic

import Logic
import Equality

predNat : Nat -> Nat
predNat 0       = 0
predNat (S n)   = n

-- -- -- -- --
-- ADDITION --
-- -- -- -- --

total
zeroPlusLeft : (x : Nat) -> 0 + x = x
zeroPlusLeft x = Refl

total
zeroPlusRight : (x : Nat) -> x + 0 = x
zeroPlusRight 0     = Refl
zeroPlusRight (S x) = cong S (zeroPlusRight x)

total
successorPlusShift : (x : Nat) -> (y : Nat) -> S x + y = x + S y
successorPlusShift 0 y      = Refl
successorPlusShift (S x) y  = cong S (successorPlusShift x y)

total
plusComm : (x, y : Nat) -> x + y = y + x
plusComm 0 y        = sym (zeroPlusRight y)
plusComm (S x) y    = trans
                        (cong S (plusComm x y))     -- Sx + y = S(y + x)
                        (successorPlusShift y x)    -- S(y + x) = y + Sx

total
plusAssoc : (x, y, z : Nat) -> (x + y) + z = x + (y + z)
plusAssoc 0 y z     = Refl
plusAssoc (S x) y z = cong S (plusAssoc x y z)

-- -- -- -- -- -- --
-- MULTIPLICATION --
-- -- -- -- -- -- --

total
zeroTimesLeft : (x : Nat) -> 0 * x = 0
zeroTimesLeft x = Refl

total
zeroTimesRight : (x : Nat) -> x * 0 = 0
zeroTimesRight 0        = Refl
zeroTimesRight (S x)    = zeroTimesRight x

total
oneTimesLeft : (x : Nat) -> 1 * x = x
oneTimesLeft = zeroPlusRight

total
oneTimesRight : (x : Nat) -> x * 1 = x
oneTimesRight 0     = zeroTimesLeft 1
oneTimesRight (S x) = cong S (oneTimesRight x)

total
succTimesRight : (x, y : Nat) -> x * (S y) = x + (x * y)
succTimesRight 0 y = Refl
succTimesRight (S x) y
    = trans
        (cong (S y +) (succTimesRight x y))         $ trans
        (sym $ plusAssoc (S y) x (x * y))           $ trans
        (cong (+ (x * y)) (successorPlusShift y x)) $ trans
        (cong (+ (x * y)) (plusComm y (S x)))       
        (plusAssoc (S x) y (x * y))

total
timesComm : (x, y : Nat) -> x * y = y * x
timesComm 0 y = sym (zeroTimesRight y)
timesComm (S x) y
    = trans
        (cong (y +) $ timesComm x y)
        (sym $ succTimesRight y x)

total
timesDistribL : (x, y, z : Nat) -> x * (y + z) = (x * y) + (x * z)
timesDistribL 0 y z = Refl
timesDistribL (S x) y z
    = trans
        (cong ((y + z) +) $ timesDistribL x y z)    $ trans
        (sym $ plusAssoc (y + z) (x * y) (x * z))   $ trans
        (cong (+ (x * z))                           $ trans
            (plusAssoc y z (x * y))                 $ trans
            (cong (y +) $ plusComm z (x * y))
            (sym $ plusAssoc y (x * y) z)
        )
        (plusAssoc ((S x) * y) z (x * z))

total
timesDistribR : (x, y, z : Nat) -> (x + y) * z = (x * z) + (y * z)
timesDistribR x y z
    = trans
        (timesComm (x + y) z)               $ trans
        (timesDistribL z x y)               $ trans
        (cong (+ (z * y)) (timesComm z x))
        (cong ((x * z) +) (timesComm z y))

total
timesAssoc : (x, y, z : Nat) -> (x * y) * z = x * (y * z)
timesAssoc 0 y z = Refl
timesAssoc (S x) y z
    = trans
        (timesDistribR y (x * y) z)
        (cong ((y * z) +) $ timesAssoc x y z)

-- -- -- -- --
-- EQUALITY --
-- -- -- -- --

isZero : Nat -> Type
isZero 0        = ()
isZero (S _)    = Void 

total
public export
decEq : (m, n : Nat) -> Dec (m = n)
decEq 0 0 = Yes Refl
decEq 0 (S n) = No $ (\eq => transport isZero eq ())
decEq (S m) 0 = No $ (\eq => transport isZero (sym eq) ())
decEq (S m) (S n)
    = caseSplit 
        (\eq => Yes (cong S eq)) 
        (\neq => No $ \eq => neq (cong predNat eq)) 
        (decEq m n)

-- -- -- -- -- -- --
-- INEQUALITIES   --
-- -- -- -- -- -- --

public export
data LeqNat : (m, n : Nat) -> Type where
    LeqZero : (n : Nat) -> LeqNat 0 n
    LeqShift : {m, n : Nat} -> LeqNat m n -> LeqNat (S m) (S n)

total
public export
leqSucc : (n : Nat) -> LeqNat n (S n)
leqSucc 0       = LeqZero 1
leqSucc (S n)   = LeqShift (leqSucc n)

total
leqShiftL : {m, n : Nat} -> LeqNat (S m) (S n) -> LeqNat m n
leqShiftL (LeqShift leq) = leq

total
public export
succNotLeqZero : (n : Nat) -> LeqNat (S n) 0 -> Void

total
public export
leqTrans : {x, y, z : Nat} -> LeqNat x y -> LeqNat y z -> LeqNat x z
leqTrans (LeqZero y) _                      = LeqZero z
leqTrans (LeqShift leq1) (LeqShift leq2)    = LeqShift $ leqTrans leq1 leq2

total
public export
leqAntisym : {x, y : Nat} -> LeqNat x y -> LeqNat y x -> x = y
leqAntisym (LeqZero 0) (LeqZero 0)          = Refl
leqAntisym (LeqShift leq1) (LeqShift leq2)  = cong S $ leqAntisym leq1 leq2

total
public export
decLeq : (m, n : Nat) -> Dec (LeqNat m n)
decLeq 0 n          = Yes $ LeqZero n
decLeq (S m) 0      = No $ nope
    where nope : LeqNat (S m) 0 -> Void
decLeq (S m) (S n)  = caseSplit (Yes . LeqShift) (No . (. leqShiftL)) (decLeq m n) 

total
public export
eqImpliesLeq : {m, n : Nat} -> m = n -> LeqNat m n
eqImpliesLeq {m = 0} {n = 0} Refl       = LeqZero 0
eqImpliesLeq {m = S m} {n = S m} Refl   = LeqShift $ eqImpliesLeq Refl

total
public export
leqImmediateSuc : {m, n : Nat} -> LeqNat m n -> (m = n -> Void) -> LeqNat (S m) n
leqImmediateSuc (LeqZero 0) notEq       = exNihilo $ notEq Refl
leqImmediateSuc (LeqZero (S n)) _       = LeqShift $ LeqZero n
leqImmediateSuc (LeqShift leq) notEq    = LeqShift $ leqImmediateSuc leq (\eq => notEq $ cong S eq)
