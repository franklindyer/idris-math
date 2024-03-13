module RecursionTest

import Logic
import Arithmetic

total
public export
div2 : Nat -> Nat
div2 0          = 0
div2 (S 0)      = 0
div2 (S (S x))  = S (div2 x)

total
public export
div2Leq : (n : Nat) -> LeqNat (div2 $ S n) n
div2Leq 0           = LeqZero 0
div2Leq (S 0)       = LeqShift $ LeqZero 0
div2Leq (S (S n))   = LeqShift $ leqTrans (div2Leq n) (leqSucc n) 

log2Careless : Nat -> Nat
log2Careless 0      = 0
log2Careless (S x)  = 1 + log2Careless (div2 $ S x)

log2CarelessRecurrence : (n : Nat) ->
                         log2Careless (S n) = 1 + log2Careless (div2 $ S n)
log2CarelessRecurrence n = Refl

total
log2CautiousHelper : Nat -> Nat -> Nat
log2CautiousHelper _ 0 = 0
log2CautiousHelper m (S n)
    = caseSplit 
        (\_ => 1 + log2CautiousHelper (div2 m) n)
        (\_ => log2CautiousHelper m n) 
        (decLeq (S n) m) 

total
log2Cautious : Nat -> Nat
log2Cautious n = log2CautiousHelper n n

total
log2DropDown : (m, n : Nat) -> LeqNat m n -> log2CautiousHelper m n = log2CautiousHelper m m
log2DropDown 0 0 _ = Refl
log2DropDown 0 (S n) (LeqZero (S n))
    = trans 
        (caseSplitNo 
            {y = 1 + log2CautiousHelper 0 n} 
            (decLeq (S n) 0) 
            (succNotLeqZero n)) 
        (log2DropDown 0 n (LeqZero n))
log2DropDown (S m) (S n) (LeqShift leq1)
    = caseSplit
        (\leq2 => cong (log2CautiousHelper $ S m) (leqAntisym leq2 $ LeqShift leq1))
        (\nleq =>
            let leq2 = leqImmediateSuc leq1 (\eq => nleq $ LeqShift $ eqImpliesLeq $ sym eq) in 
            trans
                (caseSplitNo (decLeq (S n) (S m)) nleq)
                (log2DropDown (S m) n leq2))
        (decLeq (S n) (S m))

total
log2CautiousRecurrence : (n : Nat) -> log2Cautious (S n) = 1 + log2Cautious (div2 $ S n)
log2CautiousRecurrence n =
    trans
        (caseSplitYes (decLeq (S n) (S n)) (eqImpliesLeq Refl))
        (cong (1+) $ log2DropDown (div2 $ S n) n (div2Leq n))
