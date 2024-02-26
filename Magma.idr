module Magma

import Logic

interface Magma a where
    mop : a -> a -> a

hasLeftId : Type -> Type
hasLeftId a = Magma a => DPair a (\e => (x : a) -> mop e x = x)

hasRightId : Type -> Type
hasRightId a = Magma a => DPair a (\e => (x : a) -> mop x e = x)

isCommutative : Type -> Type
isCommutative a = Magma a => (x, y : a) -> mop x y = mop y x

isAssociative : Type -> Type
isAssociative a = Magma a => (x, y, z : a) -> mop (mop x y) z = mop x (mop y z)

assocFour : Magma a => 
            isAssociative a ->
            (w, x, y, z : a) -> mop (mop (mop w x) y) z = mop w (mop x (mop y z))
assocFour assoc w x y z
    = trans 
        (cong (\v => mop v z) (assoc w x y)) $ trans
        (assoc w (mop x y) z)
        (cong (mop w) (assoc x y z)) 

twoSidedId : Magma a =>
             (idL : hasLeftId a) -> 
             (idR : hasRightId a) ->
             .fst idL = .fst idR
twoSidedId idL idR
    = trans
        (sym (.snd idR $ .fst idL))
        (.snd idL $ .fst idR)

-- Still buggy
putnam32B1 : Magma a =>
             ((x : a) -> mop x x = x) ->
             ((x, y, z : a) -> mop (mop x y) z = mop (mop y z) x) ->
             Pair (isCommutative a) (isAssociative a)            
putnam32B1 idemp cycle
    = let
        comm : (x, y : a) -> mop x y = mop y x
        comm y x =
            trans
                (sym $ idemp $ mop y x) $ trans
                (cycle y x (mop y x))   $ trans
                (cycle x (mop y x) y)   $ trans
                (cong (\z => mop z x)   $ trans
                    (cycle y x y)           $ trans
                    (cycle x y y)
                    (cong (\z => mop z x) (idemp y))
                )                       $ trans
                (cycle y x x)         
                (cong (\z => mop z y) (idemp x));
        assoc : (x, y, z : a) -> mop (mop x y) z = mop x (mop y z)
        assoc x y z = trans (cycle x y z) (comm (mop y z) x)
      in (comm, assoc)

putnam62A1 : Magma a =>
             ((x, y : a) -> mop (mop x y) x = y) ->
             (x, y : a) -> mop x (mop y x) = y
putnam62A1 ident x y
    = trans
        (cong (\z => mop z (mop y x)) $ sym $ ident y x)
        (ident (mop y x) y)
