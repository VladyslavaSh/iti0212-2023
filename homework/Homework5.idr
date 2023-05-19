{- Vladyslava Shekula -}

module Homework5

import Decidable.Equality
import Data.Nat
import Data.List
import Data.Vect
import Data.Fin

%default total

And : Type -> Type -> Type
And = Pair

coerce : a = b -> a -> b
coerce {a = a'} {b = a'} Refl = id

transport : (0 fam : a -> Type) -> {x, y : a} -> x = y -> fam x -> fam y
transport fam prf = coerce (cong fam prf)

plus_Z : {n : Nat} -> n + 0 = n
plus_Z {n = 0} = Refl
plus_Z {n = (S n')} = cong S plus_Z

plus_S : {m, n : Nat} -> m + S n = S m + n
plus_S {m = 0} = Refl
plus_S {m = S m'} = cong S plus_S

plus_comm : {m, n : Nat} -> m + n = n + m
plus_comm {m = 0} = sym plus_Z
plus_comm {m = (S m')} =
  transitive
    (cong S plus_comm)
    (sym plus_S)

data IsEven : (n : Nat) -> Type where
    IsEvenZ : IsEven 0
    IsEvenSS : IsEven n -> IsEven (S (S n))



{- Problem 1 -}

plus_one_right : {n : Nat} -> n + 1 = S n
plus_one_right {n = 0} = Refl                          -- 1 = 1
plus_one_right {n = (S k)} = cong S plus_one_right     -- S (k + 1) = S (S k)



{- Problem 2 -}

vect_append : {n : Nat} -> Vect n a -> a -> Vect (S n) a
vect_append xs x = let 
                      res = xs ++ [x] 
                    in 
                      transport (\x => Vect x a) plus_comm res        -- Vect (plus n 1) a -> Vect (S n) a


vect_reverse : {n : Nat} -> Vect n a -> Vect n a
vect_reverse {n = 0} [] = Nil                                          -- Vect 0 a
vect_reverse {n = (S k)} (x :: xs) = vect_append (vect_reverse xs) x   -- Vect (S k) a

-- Test on:
-- vect_reverse []
-- vect_reverse [1]
-- vect_reverse [1, 2]
-- vect_reverse [1, 2, 3]



{- Problem 3 -}

dec_and : Dec p -> Dec q -> Dec (p `And` q)
dec_and (Yes p_true) (Yes q_true) = Yes $ MkPair p_true q_true   -- Dec (p, q)
-- (p, q) -> Void
dec_and _ (No q_false) = No (\(x, y) => q_false y)      -- q_false : q -> Void
dec_and (No p_false) _ = No (\(x, y) => p_false x)      -- p_false : p -> Void


dec_not : Dec p -> Dec (Not p)
dec_not (Yes p_true) = No (\x => x p_true)        -- x : p -> Void, ?g : (p -> Void) -> Void
dec_not (No p_false) = Yes p_false                -- p_false : p -> Void



{- Problem 4 -}

half : (n : Nat) -> (even_constraint : IsEven n) => Nat 
half 0 {even_constraint = IsEvenZ} = 0                               -- even_constraint : IsEven 0
-- even_constraint : IsEven (S (S k))
half (S (S k)) {even_constraint = IsEvenSS x} = S (half k {even_constraint = x})

-- :set showtypes

-- Test on:
-- half 0
-- half 2
-- half 3
-- half 42



{- Problem 5 -}

record PlayerState where
    constructor PS
    health : Fin 11
    wealth : Fin 101


-- 1 health = 10 wealth

hire_healer : PlayerState -> PlayerState
-- no health and no wealth -> player's state remains unchanged
hire_healer (PS FZ FZ) = PS FZ FZ

-- no health, but wealth -> check if wealth is GTE 10 ->
-- yes: buy 1 helath (FS FZ) for 10 wealth each (FS x - 10) 
-- no: player's state remains unchanged
-- hire_healer (PS FZ (FS x)) = if (FS x) >= 10 then (PS (FS FZ) (FS x - 10)) else PS FZ (FS x)
hire_healer (PS FZ (FS x)) = if (FS x) >= 10 then {health := FS FZ, wealth := (FS x - 10)} (PS FZ (FS x)) else PS FZ (FS x)

-- health, but no wealth -> player's state remains unchanged
hire_healer (PS (FS x) FZ) = PS (FS x) FZ

-- health and wealth -> check if health is max or wealth is less then 10 -> 
-- yes: player's state remains unchanged
-- no: increase health by one (FS x + 1) and reduce wealth by 10 (FS y - 10)
--hire_healer (PS (FS x) (FS y)) = if (FS x) == 10 || (FS y) < 10 then PS (FS x) (FS y) else (PS (FS x + 1) (FS y - 10))
hire_healer (PS (FS x) (FS y)) = if (FS x) == 10 || (FS y) < 10 then PS (FS x) (FS y) else {health $= (+ 1), wealth := (FS y - 10)} (PS (FS x) (FS y))


-- Test on:
-- 0 health, 0 wealth
player1 = PS FZ FZ
-- hire_healer player1

-- 0 health, 10 wealth -> 1 health, 0 wealth
player2 = PS FZ (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ)))))))))) --> PS (FS FZ) FZ
-- hire_healer player2

-- 1 health, 0 wealth
player3 = PS (FS FZ) FZ
-- hire_healer player3

-- 2 health, 10 wealth -> 3 health, 0 wealth
player4 = PS (FS (FS FZ)) (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ)))))))))) --> PS (FS (FS (FS FZ))) FZ
-- hire_healer player4



{- Problem 6 -}

infixl 10 !!
record Complex where
  constructor (!!)
  real : Double
  imaginary : Double

{-
(+) :  Complex -> Complex -> Complex
(+) (r1 !! i1) (r2 !! i2) = (r1 + r2) !! (i1 + i2)
-- 1 !! 2 + 3 !! 4 = (1 + 3) !! (2 + 4) = 4 !! 6

(*) : Complex -> Complex -> Complex
(*) (r1 !! i1) (r2 !! i2) = (r1 * r2 - i1 * i2) !! (r1 * i2 + r2 * i1)
-- 1 !! 2 * 3 !! 4 = 1 * 3 - 2 * 4 !! 1 * 4 + 2 * 3 = 3 - 8 !! 4 + 6 = -5 !! 10

fromInteger : Integer -> Complex
fromInteger i = (fromInteger i) !! 0.0
-- fromInteger 7 = 7.0 !! 0.0

num_implements_complex : Num Complex 
num_implements_complex = MkNum (+) (*) fromInteger
-}

implementation Num Complex where
  (+) (r1 !! i1) (r2 !! i2) = (r1 + r2) !! (i1 + i2)
  (*) (r1 !! i1) (r2 !! i2) = (r1 * r2 - i1 * i2) !! (r1 * i2 + r2 * i1)
  fromInteger i = (fromInteger i) !! 0.0

-- Test on:
-- 1 !! 2 + 3 !! 4
-- 1 !! 2 * 3 !! 4
-- the Complex (fromInteger 7)

