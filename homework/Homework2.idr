{-- Vladyslava Shekula --}

module Homework2

import Data.Colist
import Data.Stream

import Data.String



{-- Problem 1 --}

interface Queue (queue : Type -> Type) where
    emp : queue a
    push : a -> queue a -> queue a
    pop : queue a -> Maybe (Pair a (queue a))


implementation Queue List where
    emp = []
    -- push x onto its back end
    push x xs = xs ++ [x]
    -- Maybe (a, List a)
    pop [] = Nothing
    -- pop an element off of its front end in a first-in–first-out manner
    pop (x :: xs) = Just (x, xs)


-- the (List Nat) ((push 3 . push 2 . push 1) emp)
-- pop (the (List Nat) [1, 2, 3])
-- pop (the (List Nat) [])




{-- Problem 2 --}

data  List' : (a : Type) -> Type  where
	NilL  :  List' a
	ConsL  :  a -> List' a -> List' a

data  Colist' : (a : Type) -> Type  where
	NilC  :  Colist' a
	ConsC  :  a -> Inf (Colist' a) -> Colist' a

data Stream' : (a : Type) -> Type where
    (::) : a -> Inf (Stream' a) -> Stream' a



implementation Cast (List a) (Colist a) where
    cast xs = case xs of
                   [] => Nil                       -- Nil : Colist a
                   (y :: ys) => y :: cast ys       -- (::) : a -> Inf (Colist a) -> Colist a

-- Test:
list : List Int
list = [1, 2, 3]

list_colist : Colist Int
list_colist = cast list


implementation Cast (Stream a) (Colist a) where
    cast (x :: xs) = x :: cast xs

-- Test:
stream : Stream Int
stream = 1 :: 2 :: 3 :: repeat 0

stream_colist : Colist Int
stream_colist = cast stream




{-- Problem 3 --}

pred' : Nat -> Maybe Nat
pred' Z = Nothing
pred' (S k) = Just k

-- pred' 42


unroll : (a -> Maybe a) -> a -> Colist a
unroll f x = case f x of
                  Nothing => x :: Nil
                  (Just y) => x :: unroll f y


-- take 5 (unroll pred' 5)
-- take 5 (unroll pred' 3)

-- Question: Why does the result sequence type of this function need to be a Colist and not a List or a Stream?
-- Answer: It is because function unroll may give the infinite result. While List takes finite and Stream takes infinite, 
-- Colist can take both finite and infinite results. Therefore, for this function it is better to use Colist. 




{-- Problem 4 --}

data Conat : Type where
    Zero : Conat
    Succ : Inf Conat -> Conat

infinity : Conat
infinity = Succ infinity

coN : Nat -> Conat
coN Z = Zero
coN (S n) = Succ (coN n)


partial 
implementation Eq Conat where
    (==) Zero Zero = True
    (==) Zero (Succ x) = False
    (==) (Succ x) Zero = False
    (==) (Succ x) (Succ y) = (x == y)
    -- (/=) (Succ x) (Succ y) = not (x == y)


partial
implementation Ord Conat where
    Zero < Zero = False
    Zero < (Succ y) = True
    (Succ x) < Zero = False
    (Succ x) < (Succ y) = x < y
  
    Zero > Zero = False
    Zero > (Succ y) = False
    (Succ x) > Zero = True
    (Succ x) > (Succ y) = x > y
  
    {-Zero <= Zero = True
    Zero <= (Succ y) = True
    (Succ x) <= Zero = False
    (Succ x) <= (Succ y) = x <= y-}
  
    {-Zero >= Zero = True
    Zero >= (Succ y) = False
    (Succ x) >= Zero = True
    (Succ x) >= (Succ y) = x >= y-}


-- coN 42 == coN 42
-- coN 42 == coN 43
-- coN 42 < coN 43
-- coN 42 < infinity
-- coN 35 <= coN 45
-- coN 20 >= coN 20




{-- Problem 5 --}

-- pure : a -> IO a
-- (>>=): IO a -> (a -> IO b)-> IO b


joinIO : IO (IO a) -> IO a
joinIO x = x >>= \a => a 

-- x : IO (IO a)
-- a : IO a


mapIO : (a -> b) -> IO a -> IO b
mapIO f x = x >>= \a => pure $ f a
            {-do
            a <- x           -- getting a type a
            pure $ f a-}


-- x : IO a
-- f : a -> b
-- ?g : IO b

-- IO b -> pure (f (a))

-- pure (f a) = pure $ f a




{-- Problem 6 --}

eitherIO : Either (IO a) (IO b) -> IO (Either a b)
eitherIO (Left x) = x >>= \a => pure (Left a)
eitherIO (Right y) = y >>= \b => pure (Right b)

-- x : IO a
-- y : IO b

-- pure (Left x) : IO (Either (IO a) (IO b))
-- pure (Right y) : IO (Either (IO a) (IO b))



bothIO : Pair (IO a) (IO b) -> IO (Pair a b)
bothIO (x, y) = do
                a <- x         -- from IO a to a
                b <- y         -- from IO b to b
                pure (a, b)

-- x : IO a
-- y : IO b

-- pure (x, y) : IO (Pair (IO a) (IO b))




{-- Problem 7 --}

get_number : IO (Maybe Integer)
get_number = do
            putStr ("Please, enter the number: ")
            str <- getLine
            case (parsePositive str) of
                 Nothing => pure (Nothing)
                 (Just n) => pure (Just n)


-- pure (Nothing) : IO (Maybe Integer)
-- pure (Just n) : IO (Maybe Integer)



insist : IO (Maybe a) -> IO a
insist x = do
            a <- x        -- get Maybe a
            case a of
                 Nothing => insist x
                 (Just n) => pure n


-- :exec insist get_number >>= printLn


