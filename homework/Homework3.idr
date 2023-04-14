{-- Vladyslava Shekula --}

module Homework3

import Data.Vect


{-- Problem 1 --}

-- (<+>)  :  List a -> List a -> List a
-- assoc : (x , y , z : a) -> (x <+> y) <+> z == x <+> (y <+> z)

implementation [pointwise] Monoid a => Semigroup (List a) where
   (<+>) [] [] =  []
   (<+>) [] ys =  ys
   (<+>) xs [] =  xs
   (<+>) (x :: xs) (y :: ys) = (x <+> y) :: (xs <+> ys)


-- Test on:
-- (<+>)@{pointwise} ["hello ", "goodbye ", "tere!"] ["world", "friend"]
-- (<+>)@{pointwise} [Just 1, Nothing, Nothing] [Nothing, Just 2]




{-- Problem 2 --}

{-Write the update function for lists, returning Nothing if the index i is out-of-bounds for the
argument list, and Just the list with new replacing the element at index i otherwise: -}

update_list : (new : a) -> (i : Nat) -> List a -> Maybe (List a)
update_list new i [] = Nothing
update_list new Z (x :: xs) = Just (new :: xs)                      -- update the first element of the list
update_list new (S i) (x :: xs) = case update_list new i xs of
                                       Nothing => Nothing
                                       (Just y) => Just (x :: y)    -- initial head + updated tail

{- i : Nat
   xs : List a
   x : a
   new : a
   y : List a
------------------------------
update_list_rhs_5 : Maybe (List a) -}


-- Test on: update_list 80 1 [1, 2, 3, 4, 5, 6]




{-- Problem 3 --}

-- index in-bounds < Fin n
-- Fin n: Numbers strictly less than some bound

-- FZ : Fin (S k)
-- FS : Fin k -> Fin (S k)

update_vect : (new : a) -> (i : Fin n) -> Vect n a -> Vect n a
update_vect new i [] = Nil                                         -- Vect 0 a
update_vect new FZ (x :: xs) = new :: xs                           -- a :: Vect len a  ->  Vect (S len) a
update_vect new (FS i) (x :: xs) = x :: update_vect new i xs

{-
   new : a
   i : Fin len
   x : a
   xs : Vect len a
------------------------------
update_vect_rhs_3 : Vect (S len) a
-}

-- Test on:
-- update_vect 80 1 [1, 2, 3, 4, 5]




{-- Problem 4 --}

monadify : Monad m => (a -> b -> c) -> m a -> m b -> m c
monadify f x y = do
                a <- x    -- a : a
                b <- y    -- b : b
                pure $ f a b

-- monadify (+) (Just 1) (Just 2)
-- monadify (+) (the (List _) [1,2]) [3,4,5]
-- :exec monadify (++) getLine getLine >>= printLn




{-- Problem 5 --}

data  Tuple : (ts : Vect n Type) -> Type  where
    Nil : Tuple []
    (::) : t -> Tuple ts -> Tuple (t :: ts)


concat_tuple : Tuple a -> Tuple b -> Tuple (a ++ b)         -- a - first tuple, b - second tuple
concat_tuple Nil ts = ts                                    -- ts : Tuple b
concat_tuple (t :: ts) x = t :: concat_tuple ts x           -- Tuple (t :: (ts ++ b))


-- Test on:
-- concat_tuple ["hello", 42] [True, id]
-- concat_tuple ["hello", 42] []
-- concat_tuple [] [True, id]




{-- Problem 6 --}

{-
empty_tuple : Vect Z a -> Tuple []
empty_tuple [] = Nil

one_elem_tuple : Vect 1 a -> Tuple [a]
one_elem_tuple (x :: xs) = x :: Nil

two_elem_tuple : Vect 2 a -> Tuple [a, a]
two_elem_tuple (x :: (y :: [])) = x :: y :: Nil

three_elem_tuple : Vect 3 a -> Tuple [a, a, a]
three_elem_tuple (x :: (y :: (z :: []))) = x :: y :: z :: Nil
-}


constant_vect  :  (n : Nat) -> a -> Vect n a
constant_vect Z x  =  []                              -- Vect 0 a
constant_vect (S n) x  =  x :: constant_vect n x      -- Vect (S n) a

{-
as_tuple : Vect n a -> Tuple (constant_vect n a)
as_tuple [] = Nil
as_tuple (x :: xs) = x :: as_tuple xs
-}

-- replicate : (n : Nat) -> a -> Vect n a
as_tuple : Vect n a -> Tuple (replicate n a)
as_tuple [] = Nil
as_tuple (x :: xs) = x :: as_tuple xs


-- Test on:
-- as_tuple []
-- as_tuple [1, 2, 3]
-- concat_tuple (as_tuple ["hello", "world"]) (as_tuple [1, 2, 3])




{-- Problem 7 --}

data  DPair' : (a : Type) -> (f : a -> Type) -> Type  where
    MkDPair'  :  (x : a) -> (y : f x) -> DPair' a f

Either' : Type -> Type -> Type
Either' a b = DPair Bool (\x => if x then b else a)

-- (x : Bool ** if x then b else a)
-- Syntactic sugar (x ** y) : (x : a ** b x) means MkDPair x y : DPair a b

from_either : Either a b -> Either' a b
from_either (Left x) = MkDPair False x
from_either (Right x) = MkDPair True x

to_either : Either' a b -> Either a b
to_either (MkDPair False x) = Left x
to_either (MkDPair True x) = Right x


-- Test on:
-- from_either (to_either (False ** 10))
-- to_either (from_either (Right 5))




{-- Problem 8 --}

-- with the type of dependent functions:
-- (->) : (a : Type) -> (b : a -> Type) -> Type  (written (x : a) -> b x)

-- MkDPair : (x : a) -> p x -> DPair a p

Object : Type
Object = DPair Type id

wrap : {a : Type} -> (x : a) -> Object
wrap x = MkDPair a x
-- Test on: wrap "hello"

-- (String ** "hello")
--   Type        id


unwrap : (t : Object) -> fst t
unwrap (MkDPair a x) = x
-- Test on: unwrap (Integer ** 3)


-- unwrap returns id (something that has a type a)
-- fst : Type      ->   String
-- snd : id fst    ->   "hello"

-- unwrap (wrap ?x) evaluates to ?x for arbitrary ?x




{-- Problem 9 --}

data Error : Type where
    MkError : String -> Error

-- MkDPair : (x : a) -> p x -> DPair a p

-- Object : DPair Type id
-- We return only 'id', without Type  ->  unwrap function


(+) : Object -> Object -> Object
(+) (MkDPair Integer n1) (MkDPair Integer n2) = wrap (unwrap (MkDPair Integer (n1 + n2)))           -- integer + integer
(+) (MkDPair String str1) (MkDPair String str2) = wrap (unwrap (MkDPair String (str1 ++ str2)))     -- string ++ string
(+) (MkDPair Bool b1) (MkDPair Bool b2) = wrap (unwrap (MkDPair Bool (b1 && b2)))                   -- bool && bool
(+) _ _ = wrap (MkError "type error")

-- MkDPair Integer 2 + MkDPair Integer 3 -> unwrap (MkDPair Integer 2) + unwrap (MkDPair Integer 3) -> 2 + 3 -> wrap 5 -> MkDPair (Integer 5)

-- wrap (unwrap (n1 + n2))
-- n1, n2: MkDPair Type Integer

-- unwrap (wrap 2 + wrap 3) -> unwrap (MkDPair Integer 2 + MkDPair Integer 3) -> unwrap (MkDPair Integer 5) -> 5

-- :set showtypes

-- Test on:
-- unwrap $ wrap 2 + wrap 3
-- unwrap $ wrap "hello " + wrap "world"
-- unwrap $ wrap False + wrap True
-- unwrap $ wrap "hello " + wrap 42

-- Firstly apply wrap  ->  get MkDPair Type id
-- Secondly apply unwrap  ->  get just id



