module Arithmetic

-- I've marked all of the functions below as "total" because they are meant to be proofs.
-- A non-total proof is pretty much worthless, because any type is inhabited by "undefined".

-- Zero is an additive left-identity.
-- This is trivial because it's part of the recursive definition of (+) in Idris.
total zeroPlusLeft : (x : Nat) -> 0 + x = x
zeroPlusLeft x = Refl

-- Zero is an additive right-identity.
-- This is not so trivial, because (+) is defined by recursing on the first argument.
-- Inductively, we apply S to both sides of the equality x + 0 = x to get Sx + 0 = Sx.
-- This works because S(x+0) = Sx+0 is part of the recursive definition of (+).
total zeroPlusRight : (x : Nat) -> x + 0 = x
zeroPlusRight 0     = Refl
zeroPlusRight (S x) = cong S (zeroPlusRight x)

-- Incrementing the left summand in a sum is the same as incrementing the right summand.
total successorPlusShift : (x : Nat) -> (y : Nat) -> S x + y = x + S y
successorPlusShift 0 y      = Refl
successorPlusShift (S x) y  = cong S (successorPlusShift x y)

-- Addition on natural numbers is commutative.
total plusComm : (x, y : Nat) -> x + y = y + x
plusComm 0 y        = sym (zeroPlusRight y)
plusComm (S x) y    = trans
                        (cong S (plusComm x y))     -- Sx + y = S(y + x)
                        (successorPlusShift y x)    -- S(y + x) = y + Sx

-- Addition on natural numbers is associative.
plusAssoc : (x, y, z : Nat) -> (x + y) + z = x + (y + z)
plusAssoc 0 y z = Refl
plusAssoc (S x) y z = cong S (plusAssoc x y z)
