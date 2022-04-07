{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}

module ListsAssignment where
import Prelude hiding (head, max)

{-@ type Nat = { v:Int | 0 <= v } @-}
{-@ type Pos = { v:Int | 0 < v } @-}
{-@ type NonZero = { v:Int | 0 /= v } @-}
{-@ type IntBiggerThan N = { v:Int | v >= N } @-}
{-@ type BiggerThan a N = { v:a | v >= N } @-}

infixr 9 :<
data IncList a = Emp | (:<) { hd::a, tl::IncList a }
{-@ data IncList a = Emp | (:<) { hd::a, tl::IncList (BiggerThan a hd) } @-}

{-@ okList :: IncList Int @-}
okList :: IncList Int
okList = 1 :< 2 :< 3 :< Emp

{- rejected by LiquidHaskell
{-@ badList :: IncList Int @-}
badList :: IncList Int
badList = 3 :< 1 :< 2 :< Emp -}

{-@ insert :: (Ord a) => a -> IncList a -> IncList a @-}
insert y Emp = y :< Emp
insert y (x :< xs)
    | y <= x = y :< x :< xs
    | otherwise = x :< insert y xs

{-@ insertSort :: (Ord a) => [a] -> IncList a @-}
insertSort [] = Emp
insertSort (x:xs) = insert x (insertSort xs)

{-@ merge :: (Ord a) => IncList a -> IncList a -> IncList a @-}
merge Emp ys = ys
merge xs@(_ :< _) Emp = xs -- annotation needed (pattern-matching exhaustivity)
merge (x :< xs) (y :< ys)
  | x <= y = x :< merge xs (y :< ys)
  | otherwise = y :< merge (x :< xs) ys

{-@ mergeSort :: (Ord a) => [a] -> IncList a @-}
mergeSort [] = Emp
mergeSort [x] = x :< Emp
mergeSort xs = merge (mergeSort ys) (mergeSort zs)
  where (ys, zs) = split xs
        split (x:y:zs) = (x:xs, y:ys)
          where (xs, ys) = split zs
        split zs = (zs, [])

{-@ quickSort :: (Ord a) => [a] -> IncList a @-}
quickSort [] = Emp
quickSort (x:xs) = join x lessers greaters
  where lessers = quickSort [y | y <- xs, y < x]
        greaters = quickSort [z | z <- xs, x <= z]

{-@ join :: (Ord a) => z:a -> IncList { v:a | v < z }
            -> IncList { v:a | z <= v } -> IncList a @-}
join z Emp ys = z :< ys
join z (x :< xs) ys = x :< join z xs ys

{-@ measure nonEmpty @-}
nonEmpty :: [a] -> Bool
nonEmpty [] = False
nonEmpty (_:_) = True

{-@ type NEList a = { v:[a] | nonEmpty v } @-}

{-@ head :: NEList a -> a @-}
head :: [a] -> a
head (x:_) = x -- exhaustive because the [] constructor gives empty lists

{- rejected by LiquidHaskell
h = head [] -}
