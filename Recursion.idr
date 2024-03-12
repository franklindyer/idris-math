module Recursion

import Logic
import Equality
import Arithmetic
import RecursionTest

-- -- -- -- -- -- -- -- --
-- SIZE-BASED RECURSION --
-- -- -- -- -- -- -- -- --

public export
record GenericRecurrence a b where
    constructor MakeGenRec
    size : a -> Nat
    base : a -> b
    recf : a -> a
    recg : a -> b -> b 

public export
carelessNatRecurse : GenericRecurrence a b -> (a -> b)
carelessNatRecurse gr x
    = if (gr.size x) == 0 
      then gr.base x 
      else gr.recg x (carelessNatRecurse gr (gr.recf x))

total
cautiousHelper : GenericRecurrence a b -> (a -> Nat -> Nat -> b)
cautiousHelper gr x s 0 = gr.base x
cautiousHelper gr x s (S k)
    = caseSplit
        (\_ => gr.recg x (cautiousHelper gr (gr.recf x) (gr.size $ gr.recf x) k))
        (\_ => cautiousHelper gr x s k)
        (decLeq (S k) s)

total
public export
cautiousNatRecurse : GenericRecurrence a b -> (a -> b)
cautiousNatRecurse gr x = cautiousHelper gr x (gr.size x) (gr.size x)

total
cautiousHelperDropDown : (gr : GenericRecurrence a b) ->
                         (x : a) ->
                         (m, n : Nat) ->
                         (LeqNat m n) ->
                         cautiousHelper gr x m n = cautiousHelper gr x m m
cautiousHelperDropDown gr x m n leq = dropDown m n leq
    where dropDown : (m, n : Nat) -> 
                     (LeqNat m n) ->
                     cautiousHelper gr x m n = cautiousHelper gr x m m
          dropDown 0 0 _ = Refl
          dropDown 0 (S n) (LeqZero (S n))
            = trans
                (caseSplitNo
                    {y = cautiousHelper gr x 0 n}
                    (decLeq (S n) 0)
                    (succNotLeqZero n))
                (cautiousHelperDropDown gr x 0 n (LeqZero n))
          dropDown (S m) (S n) (LeqShift leq1)
            = caseSplit
                (\leq2 => cong (cautiousHelper gr x (S m)) (leqAntisym leq2 $ LeqShift leq1))
                (\nleq =>
                    let leq2 = leqImmediateSuc leq1 (\eq => nleq $ LeqShift $ eqImpliesLeq $ sym eq) in
                    trans
                        (caseSplitNo (decLeq (S n) (S m)) nleq)
                        (dropDown (S m) n leq2))
                (decLeq (S n) (S m))

total
public export
cautiousNatRecurrence : (gr : GenericRecurrence a b) ->
                        (bound : (x : a) -> 
                                 (n : Nat) -> 
                                 (gr.size x = S n) -> 
                                 LeqNat (gr.size (gr.recf x)) n) ->
                        (x : a) ->
                        (n : Nat) ->
                        (gr.size x = S n) ->
                        (cautiousNatRecurse gr x = gr.recg x (cautiousNatRecurse gr $ gr.recf x))
cautiousNatRecurrence gr bound x n szeq
    = trans
        (cong (\k => cautiousHelper gr x k k) szeq)             $ trans
        (caseSplitYes (decLeq (S n) (S n)) (eqImpliesLeq Refl))
        (cong (gr.recg x) $ cautiousHelperDropDown gr x' (gr.size x') n (bound x n szeq))
        where x' = gr.recf x


total
log2RecursionPackage : GenericRecurrence Nat Nat
log2RecursionPackage = MakeGenRec id id div2 (\_ => (1+))

total
log2 : Nat -> Nat
log2 = cautiousNatRecurse log2RecursionPackage

total
log2Recurrence : (n : Nat) -> log2 (S n) = 1 + log2 (div2 (S n))
log2Recurrence n 
    = cautiousNatRecurrence
        log2RecursionPackage
        (\sm, m, eq => transport (\k => LeqNat (div2 k) m) (sym eq) (div2Leq m))
        (S n) n Refl
