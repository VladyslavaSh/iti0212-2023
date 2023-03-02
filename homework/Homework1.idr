{-- Vladyslava Shekula --}
module Homework1


{-- Problem 1 --}

fib : Nat -> Nat
fib Z = (S Z)
fib (S Z) = (S Z)
fib (S (S k)) = fib (S k) + fib k
--	1, 1, 2, 3, 5, 8, 13, 21, 34, 55, ...
--fib (𝑛 − 1) + fib (𝑛 − 2)

-- Test: fib 7



{-- Problem 2 --}

exp : Nat -> Nat -> Nat
exp m Z = (S Z)
--exp m (S Z) = m
exp m (S n) = m * exp m n

-- Test: exp 2 3



{-- Problem 3 --}

fun1 : Either a a -> a
fun1 (Left x) = x
fun1 (Right x) = x

-- Tests:
-- fun1 (Right 67)
-- fun1 (Left True)


fun2 : Pair (Pair a b) c -> Pair a (Pair b c)
fun2 ((x, y), z) = (x, (y, z))
-- ((a, b), c) -> (a, (b, c))

-- Tests:
-- fun2 ((2, 3), 5)
-- fun2 ((True, False), True)


fun3 : Pair a (Either b c) -> Either (Pair a b) (Pair a c)
fun3 (x, (Left y)) = Left (x, y)
fun3 (x, (Right y)) = Right (x, y)

-- Tests:
-- fun3 (20, Left 6)
-- fun3 (True, Left False) 



-- Either (Pair a b) (Pair a c)
-- b -> Left (Pair a b)
-- c -> Right (Pair a c)

-- x : a
-- y : b
-- Either (a, b) (a, c)

-- x : a
-- y : c
-- Either (a, b) (a, c)




{-- Problem 4 --}

data Tree : (a : Type) -> Type where
    Leaf : Tree a
    Node : (l : Tree a) -> (x : a) -> (r : Tree a) -> Tree a


reflect : Tree a -> Tree a
reflect Leaf = Leaf
reflect (Node l x r) = Node (reflect r) x (reflect l)

-- Tests:
-- reflect (Node (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf)) 4 (Node (Node Leaf 5 Leaf) 6 (Node Leaf 7 Leaf)))
-- reflect (Node (Node Leaf 1 (Node Leaf 3 Leaf)) 5 Leaf)




{-- Problem 5 --}

greatest : List Integer -> Maybe Integer
greatest [] = Nothing
greatest [x] = Just x
greatest (x :: xs) = case greatest xs of
                    Just k => Just (max x k)
                    Nothing => Just x


-- Tests:
-- greatest []
-- greatest [1]
-- greatest [1, 2, 3, 3, 2, 1]




{-- Problem 6 --}

-- Left : Unit -> Either Unit a
-- Right : a -> Either Unit a

forward : Maybe a -> Either Unit a
forward Nothing = Left ()
forward (Just x) = Right x


backward : Either Unit a -> Maybe a
backward (Left ()) = Nothing
backward (Right x) = Just x

-- backward (forward x) = x for any x : Maybe a
-- forward (backward y) = y for any y : Either Unit a


{--Tests:
backward (forward Nothing)
backward (forward (Just 2))
forward (backward (Left ()))
forward (backward (Right False))
--}




{-- Problem 7 --}

zip_tree : (a -> b -> c) -> Tree a -> Tree b -> Tree c
zip_tree f Leaf Leaf = Leaf
zip_tree f Leaf (Node l x r) = Leaf
zip_tree f (Node l x r) Leaf = Leaf
zip_tree f (Node l1 x1 r1) (Node l2 x2 r2) = Node (zip_tree f l1 l2) (f x1 x2) (zip_tree f r1 r2)

-- Node ((max l1 l2) (max x1 x2) (max r1 r2))


-- Tests:
-- zip_tree max (Node (Node Leaf 2 (Node Leaf 3 Leaf)) 5 Leaf) (Node (Node Leaf 6 (Node Leaf 4 Leaf)) 3 Leaf)




{-- Problem 8 --}

flatten_list : List (List a) -> List a
flatten_list [] = []
flatten_list (x :: xs) = x ++ flatten_list xs

-- x : List a
-- xs : List (List a)

{-- Tests:
flatten_list []
flatten_list [[] , [] , []]
flatten_list [[1,2,3] , [4,5,6] , [7,8,9]]
--}


fold_list : (n : t) -> (c : a -> t -> t) -> List a -> t
fold_list n c [] = n
--apply 'c' to 'x' and the result of recursively applying 'fold_list' to 'xs':
fold_list n c (x :: xs) = c x (fold_list n c xs)


-- c : List a -> List a -> List a
-- (\x, xs => x ++ xs)
-- ?c = x ++ flatten_list xs


flatten_list’ : List (List a) -> List a
flatten_list’ = fold_list [] (\x, xs => x ++ xs)


{--Tests:
flatten_list’ []
flatten_list’ [[] , [] , []]
flatten_list’ [[1,2,3] , [4,5,6] , [7,8,9]]
--}

