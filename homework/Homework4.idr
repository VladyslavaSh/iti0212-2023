{- Vladyslava Shekula -}

module Homework4

import Data.List
import Data.Vect
import Syntax.PreorderReasoning

%default total


{-- Problem 1 --}

data (<=) : (p : Nat) -> (n : Nat) -> Type where
    LeZ : 0 <= n
    LeS : p <= n -> S p <= S n

data IsSorted : List Nat -> Type where
    NilSort : IsSorted []
    SinglSort : IsSorted [x]  --(x : Nat) -> IsSorted [x]
    ConsSort : IsSorted (y :: ys) -> x <= y -> IsSorted (x :: y :: ys)

le01 : 0 <= 1
le01 = LeZ

le12 : 1 <= 2
le12 = LeS le01

le23 : 2 <= 3
le23 = LeS le12

-- 0 <= 1
-- 1 <= 2
-- 2 <= 3

-- ConsSort : IsSorted (y :: ys) -> x <= y        -> IsSorted (x :: y :: ys)


is_sorted_0123 : IsSorted [0, 1, 2, 3]
--               |----------IsSorted (1 :: [2, 3])                 0 <= 1--|
--               |                                                         |
--               |        |-------IsSorted (2 :: [3])         1 <= 2--|    |
--               |        |                                           |    |
--               |        |         |----IsSorted [3]     2 <= 3-|    |    |
--               |        |         |                            |    |    |
is_sorted_0123 = ConsSort (ConsSort (ConsSort (SinglSort {x = 3}) le23) le12) le01




{-- Problem 2 --}

is_sorted_succ : (xs : List Nat) -> IsSorted xs -> IsSorted (map S xs)
is_sorted_succ [] NilSort = NilSort                                         -- IsSorted []
is_sorted_succ (y :: []) (SinglSort {x = y}) = SinglSort {x = (S y)}        -- IsSorted [S y]
is_sorted_succ (x :: (y :: ys)) (ConsSort ys_sort p) = ConsSort (is_sorted_succ (y :: ys) ys_sort) (LeS p) 
--                                                              |   IsSorted (map S (y :: ys))   || S x <= S y |

-- ConsSort : IsSorted (y :: ys) -> x <= y -> IsSorted (x :: y :: ys)
-- IsSorted (S x :: S y :: (map S ys))  =  IsSorted (map S (y :: ys))  ->  S x <= S y

{-
   x : Nat
   y : Nat
   ys : List Nat
   p : x <= y
   ys_sort : IsSorted (y :: ys)
------------------------------
g : IsSorted (S x :: (S y :: mapImpl S ys))
-}




{-- Problem 3 --}

-- replicate : Nat -> a -> List a

leRefl : (n : Nat) -> n <= n
leRefl 0 = LeZ
leRefl (S k) = LeS (leRefl k)

is_sorted_cst : (lg, val : Nat) -> IsSorted (replicate lg val)
is_sorted_cst 0 val = NilSort                                    -- IsSorted []
is_sorted_cst (S 0) val = SinglSort {x = val}                    -- IsSorted [val]
is_sorted_cst (S (S k)) val = ConsSort (is_sorted_cst (S k) val) (leRefl val)
--                          | IsSorted (val :: replicate k val) | | val <= val |


-- ConsSort : IsSorted (y :: ys) -> x <= y -> IsSorted (x :: (y :: ys))
 
-- IsSorted (val :: (val :: replicate k val))  =  IsSorted (val :: replicate k val) -> val <= val




{-- Problem 4 (De Morgan’s laws) --} -- CHECK SOLUTIONS

And : Type -> Type -> Type
And = Pair

Or : Type -> Type -> Type
Or = Either

Not' : Type -> Type
Not' a = a -> Void

Implies : Type -> Type -> Type
Implies a b = a -> b

-- A and B -> not (not A or not B)
and_not_or : (a `And` b) `Implies` Not (Not a `Or` Not b)
and_not_or (x, y) (Left z) = z x                               -- z : a -> Void
and_not_or (x, y) (Right z) = z y                              -- z : b -> Void

{- x : a
   y : b
   or : Either (a -> Void) (b -> Void)
------------------------------
and_not_or_rhs_0 : Void -}

-- A or B -> not (not A and not B)
or_not_and : (a `Or` b) `Implies` Not (Not a `And` Not b)
or_not_and (Left x) (y, z) = y x                                 -- x : a,    y : a -> Void
or_not_and (Right x) (y, z) = z x                                -- x : b,    z : b -> Void

{- y : (a -> Void, b -> Void)
   x : Either a b
------------------------------
or_not_and_rhs : Void -}


-- Law: not (A or B) -> not A and not B
not_or : Not (a `Or` b) `Implies` (Not a `And` Not b)
not_or f = ((\x => f (Left x)), (\x => f (Right x)))

{-  f : Either a b -> Void
------------------------------
not_or_rhs : (a -> Void, b -> Void) -}

-- Either a b -> Left a -> Right b
-- f (Left a) -> Void
-- f (Right b) -> Void


-- Law: not A and not B -> not (A or B)
-- not_or' : (Not a `And` Not b) `Implies` Not (a `Or` b)
-- not_or' (x, z) (Left y) = x y                             -- x : a -> Void, y : a
-- not_or' (x, z) (Right y) = z y                            -- z : b -> Void, y : b

not_or' : (Not a `And` Not b) `Implies` Not (a `Or` b)
not_or' x y = or_not_and y x

-- y : Either a b
-- x : (a -> Void, b -> Void)



-- Law: not (A and B) -> not A or not B
not_and : Not (a `And` b) `Implies` (Not a `Or` Not b)

-- Law: not A or not B -> not (A and B)
not_and' : (Not a `Or` Not b) `Implies` Not (a `And` b)

-- not_and and not_and' cannot be proved, because it requires proof and we can't always know if a statement or its opposite is true




{-- Problem 5 (Universals and disjunctions) --}

Exists : ( t : Type ) -> ( p : t -> Type ) -> Type
Exists = DPair

Forall : ( t : Type ) -> ( p : t -> Type ) -> Type
Forall t p = ( x : t ) -> p x

forall_or : (Forall t p `Or` Forall t q) `Implies` Forall t (\x => p x `Or` q x)
forall_or (Left f) x = Left (f x)                   -- f : (x : t) -> p x
forall_or (Right f) x = Right (f x)                 -- f : (x : t) -> q x

-- y : Either ((x : t) -> p x) ((x : t) -> q x)
-- forall_or_rhs : Either (p x) (q x)


contradiction : p -> Not p -> a
contradiction x f = absurd (f x)

exist_p_not_p : ((Exists a p) `And` (Exists a (Not . p))) -> Not (Forall a p `Or` Forall a (Not . p)) -- absurd, we can't get Void!
exist_p_not_p (p, not_p) (Left z) = contradiction (z (fst not_p)) (snd not_p)       -- z : (x : a) -> p x
-- f : z (fst not_p)  =>  p x
-- x : snd not_p  =>  p x
exist_p_not_p (p, not_p) (Right z) = contradiction (snd p) (z (fst p))              -- z : (x : a) -> p x -> Void
-- f : z (fst p)  =>  p x -> Void
-- x : snd p  =>  p x


-- x : DPair a p
-- y : (x : a ** p x -> Void)
-- z : Either ((x : a) -> p x) ((x : a) -> p x -> Void)




{-- Problem 6 (Fun with the law of excluded middle) --}

-- If the law of excluded middle (LEM), then prove double negation elimination (DNE):
lem_to_dne : a `Or` Not a -> Not (Not a) `Implies` a
lem_to_dne (Left x) f = x               -- a
lem_to_dne (Right x) f = absurd (f x)   -- a -> Void  -- we expect to get 'a' here, but we can't

-- f : (a -> Void) -> Void
-- x : Either a (a -> Void)

-- Prove that it must be impossible for LEM to be false:
not_not_lem : Not (Not (a `Or` Not a))
not_not_lem f = f (Right (\x => f (Left x)))

-- f : Either a (a -> Void) -> Void
-- Void  =  a -> Void  =  Right x  =  f (Left x)




{-- Problem 7 --}

same_length : {xs : Vect m a} -> {ys : Vect n a} -> xs = ys -> length xs = length ys
same_length Refl = Refl

same_elments : {xs , ys : Vect n a} -> xs = ys -> index i xs = index i ys
same_elments Refl = Refl

symmetry : {x, y : a} -> x = y -> y = x
symmetry Refl = Refl

different_heads : {xs , ys : Vect n a} -> Not (x = y) -> Not (x :: xs = y :: ys)
different_heads f Refl = f Refl

-- f : x = x -> Void




{-- Problem 8 (List is a functor) --}

interface Functor t => FunctorV (t : Type -> Type) where
    pres_idty : (xs : t a) -> map Prelude.id xs = xs
    pres_comp : (f : a -> b) -> (g : b -> c) -> (xs : t a) -> map (g . f) xs = (map g . map f) xs


cong' : {x, y : a} -> (f : a -> b) -> x = y -> f x = f y
cong' f Refl = Refl -- f x = f x


FunctorV List where
    pres_idty [] = Refl
    pres_idty (x :: xs) = 
        let
         tail_eq = pres_idty xs
        in 
        cong (x ::) tail_eq              -- x :: mapImpl id xs = x :: xs 


    pres_comp f g [] = Refl
    pres_comp f g (x :: xs) = 
        let 
          tail_eq = pres_comp f g xs
        in 
          cong ((g (f x)) ::) tail_eq    -- g (f x) :: mapImpl (\x => g (f x)) xs  =  g (f x) :: mapImpl g (mapImpl f xs)




{-- Problem 9 (Reversing a list is an involution) --}

rev : List a -> List a
rev [] = []
rev (x :: xs) = rev xs ++ [x]


rev_inv_cons : (x : a) -> (xs : List a) -> rev (xs ++ [x]) = x :: rev xs
rev_inv_cons x [] = Refl                                          -- rev [x] = rev (x :: [])  =>  [x] = [x]
rev_inv_cons x (y :: xs) =                                        -- rev (y :: xs ++ [x]) = x :: rev (y :: xs)
    let
        IH = rev_inv_cons x xs                                    -- rev (xs ++ [x]) = x :: rev xs
    in Calc $
        |~ rev ((y :: xs) ++ [x])
        ~~ rev (xs ++ [x]) ++ [y] ...( Refl )                      -- rev (xs ++ [x]) ++ [y] = rev (xs ++ [x]) ++ [y]
        ~~ (x :: rev xs) ++ [y] ...( cong (\ih => ih ++ [y]) IH )  -- rev (xs ++ [x]) ++ [y] = x :: (rev xs ++ [y])
        ~~ x :: (rev xs ++ [y]) ...( Refl )                        -- x :: (rev xs ++ [y]) = x :: (rev xs ++ [y])
        ~~ x :: rev (y :: xs) ...( Refl )                          -- x :: (rev xs ++ [y]) = x :: (rev xs ++ [y])


rev_inv : (xs : List a) -> rev (rev xs) = xs
rev_inv [] = ?rev_inv_0
rev_inv (x :: xs) =
    let
        IH = rev_inv xs                                       -- rev (rev xs) = xs
    in Calc $
        |~ rev (rev (x :: xs))
        ~~ rev (rev xs ++ [x]) ...( Refl )                    -- rev (rev xs ++ [x]) = rev (rev xs ++ [x])
        ~~ x :: rev (rev xs) ...( rev_inv_cons x (rev xs) )   -- rev (rev xs ++ [x]) = x :: rev (rev xs)
        ~~ x :: xs ...( cong (\ih => x :: ih) IH )            -- x :: rev (rev xs) = x :: xs


