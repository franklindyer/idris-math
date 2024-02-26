module ListProps

-- List concatenation is associative.
total appendAssoc : (xs1, xs2, xs3 : List a) -> (xs1 ++ xs2) ++ xs3 = xs1 ++ (xs2 ++ xs3)
appendAssoc [] xs2 xs3          = Refl
appendAssoc (x::xs1) xs2 xs3    = cong (x ::) (appendAssoc xs1 xs2 xs3)

-- The empty list is a right-identity for list appending.
total emptyListRightIdentity : (xs : List a) -> xs ++ [] = xs
emptyListRightIdentity []       = Refl
emptyListRightIdentity (x::xs)  = cong (x::) (emptyListRightIdentity xs)

-- We write our own naive implementation of "reverse", because the built-in uses tail recursion.
-- The tail-recursive implementation may be a little trickier to reason about formally.
slowReverse : List a -> List a
slowReverse []          = []
slowReverse (x::xs)     = (slowReverse xs) ++ [x]

-- Appending an element to the end of a list prepends that element to the beginning.
total reverseEndToBeginning : (x : a) -> (xs : List a) -> slowReverse (xs ++ [x]) = x :: (slowReverse xs)
reverseEndToBeginning x []          = Refl
reverseEndToBeginning x1 (x2::xs)   = cong (++ [x2]) (reverseEndToBeginning x1 xs)

-- Reversing swaps the order of list appending.
total reverseSwapAppend : (xs1, xs2 : List a) -> slowReverse (xs1 ++ xs2) = slowReverse xs2 ++ slowReverse xs1
reverseSwapAppend [] xs2        = sym (emptyListRightIdentity (slowReverse xs2))
reverseSwapAppend (x::xs1) xs2  = trans
                                    (cong (++ [x]) (reverseSwapAppend xs1 xs2))
                                    (appendAssoc (slowReverse xs2) (slowReverse xs1) [x])

-- The slowReverse function is an involution: that is, it is its own inverse.
total reverseInvolution : (xs : List a) -> slowReverse (slowReverse xs) = xs
reverseInvolution []        = Refl
reverseInvolution (x::xs)   = trans
                                (reverseEndToBeginning x (slowReverse xs))
                                (cong (x ::) (reverseInvolution xs))

