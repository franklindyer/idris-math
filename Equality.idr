module Equality

import Logic

total
public export
transport : {x, y : a} -> (p : a -> Type) -> (x = y) -> p x -> p y
transport p Refl = id
