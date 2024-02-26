module Magma

record Magma where
    set : Type
    bop : set -> set -> set

hasLeftId : Magma -> Type
hasLeftId mag = DPair mag.set (\e => (x : mag.set) -> mag.bop e x = x)

hasRightId : Magma -> Type
hasRightId mag = DPair mag.set (\e => (x : mag.set) -> mag.bop x e = x)

isCommutative : Magma -> Type
isCommutative mag = (x, y : mag.set) -> mag.bop x y = mag.bop y x

isAssociative : Magma -> Type
isAssociative mag = (x, y, z : mag.set) -> mag.bop (mag.bop x y) z = mag.bop x (mag.bop y z)

twoSidedId : (m : Magma) ->
             (idL : hasLeftId m) -> 
             (idR : hasRightId m) ->
             idL.fst = idR.fst
twoSidedId mag idL idR
    = trans
        (sym (idR.snd $ idL.fst))
        (idL.snd $ idR.fst)

{-
    Down here are some exercises involving magmas that are not likely
    to be useful elsewhere.
-}

assocFour : (m : Magma) -> 
            isAssociative m ->
            (w, x, y, z : m.set) -> 
            m.bop (m.bop (m.bop w x) y) z = m.bop w (m.bop x (m.bop y z))
assocFour mag assoc w x y z
    = trans 
        (cong (\v => mag.bop v z) (assoc w x y)) $ trans
        (assoc w (mag.bop x y) z)
        (cong (mag.bop w) (assoc x y z)) 

putnam32B1 : (m : Magma) ->
             ((x : m.set) -> m.bop x x = x) ->
             ((x, y, z : m.set) -> m.bop (m.bop x y) z = m.bop (m.bop y z) x) ->
             Pair (isCommutative m) (isAssociative m)
putnam32B1 mag idemp cycle
    = let
        a : Type
        a = mag.set;
        mop : a -> a -> a
        mop = mag.bop;
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

putnam62A1 : (m : Magma) ->
             ((x, y : m.set) -> m.bop (m.bop x y) x = y) ->
             (x, y : m.set) -> m.bop x (m.bop y x) = y
putnam62A1 mag ident x y
    = trans
        (cong (\z => mag.bop z (mag.bop y x)) $ sym $ ident y x)
        (ident (mag.bop y x) y)
