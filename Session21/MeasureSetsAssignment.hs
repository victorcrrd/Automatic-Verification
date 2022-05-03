{-@ LIQUID "--no-termination" @-}

module MeasureSetsAssignment where
import Data.Set hiding (insert, partition, filter, split, elems)
import Prelude hiding (elem, reverse, filter)

main :: IO ()
main = return ()

{-@ die :: {v:_ | false} -> a @-}
die msg = error msg

type List a = [a]

{-@ type True = {v:Bool | v} @-}
{-@ type False = {v:Bool | not v} @-}

{-@ measure elts @-}
elts :: (Ord a) => [a] -> Set a
elts [] = empty
elts (x:xs) = singleton x `union` elts xs

{-@ type ListS a S = {v:List a | elts v = S} @-}
{-@ type ListEmp a = ListS a {Set_empty 0} @-}
{-@ type ListEq a X = ListS a {elts X} @-}
{-@ type ListSub a X = {v:List a | Set_sub (elts v) (elts X)} @-}
{-@ type ListUnion a X Y = ListS a {Set_cup (elts X) (elts Y)} @-}
{-@ type ListUnionSingle a X Y = ListS a {Set_cup (Set_sng X) (elts Y)} @-}

{-@ append' :: xs:_ -> ys:_ -> ListUnion a xs ys @-}
append' [] ys = ys
append' (x:xs) ys = x : append' xs ys

{-@ reverse' :: xs:List a -> ListEq a xs @-}
reverse' xs = revHelper [] xs

-- Exercise 1
{-@ revHelper :: acc:List a -> xs:List a -> ListUnion a acc xs @-}
revHelper acc [] = acc
revHelper acc (x:xs) = revHelper (x:acc) xs

-- Exercise 2
{-@ halve :: _ -> xs:List a -> {v:(List a, List a) | elts xs = Set_cup (elts (fst v)) (elts (snd v))} @-}
halve :: Int -> [a] -> ([a], [a])
halve 0 xs = ([], xs)
halve n (x:y:zs) = (x:xs, y:ys) where (xs, ys) = halve (n-1) zs
halve _ xs = ([], xs)

{-@ prop_halve_append :: _ -> _ -> True @-}
prop_halve_append n xs = elts xs == elts xs'
  where
    xs' = append' ys zs
    (ys, zs) = halve n xs

-- Exercise 3
{-@ elem :: (Eq a) => x:a -> xs:List a -> {v:Bool | v <=> member x (elts xs)} @-}
elem _ [] = False
elem x (y:ys) = x == y || elem x ys

{-@ test1 :: True @-}
test1 = elem 2 [1, 2, 3]

{-@ test2 :: False @-}
test2 = elem 2 [1, 3]

-- Exercise 4
{-@ partition :: (a -> Bool) -> xs:List a -> {v:(List a, List a) | elts xs = union (elts (fst v)) (elts (snd v))} @-}
partition _ [] = ([], [])
partition f (x:xs)
    | f x = (x:ys, zs)
    | otherwise = (ys, x:zs)
    where (ys, zs) = partition f xs

{-@ quickSort :: (Ord a) => xs:List a -> ListEq a xs @-}
quickSort :: (Ord a) => List a -> List a
quickSort [] = []
quickSort (x:xs) = append' (append' smallerS (x:equal)) greaterS
  where (smaller, greaterOrEqual) = partition (< x) xs
        (greater, equal) = partition (> x) greaterOrEqual
        smallerS = quickSort smaller
        greaterS = quickSort greater

{-@ measure unique @-}
unique :: (Ord a) => List a -> Bool
unique [] = True
unique (x:xs) = unique xs && not (member x (elts xs))

{-@ type UList a = {v:List a | unique v} @-}

-- Exercise 5
{-@ filter' :: (a -> Bool) -> xs:List a -> {v:ListSub a xs | unique xs => unique v} @-}
filter' _ [] = []
filter' f (x:xs)
    | f x = x : xs'
    | otherwise = xs'
  where xs' = filter' f xs

{-@ test3 :: UList _ @-}
test3 = filter' (> 2) [1,2,3,4]

{-@ test4 :: List _ @-}
test4 = filter' (> 3) [3,1,2,3]

{-@ reverse :: UList a -> UList a @-}
reverse = go []
  where
    {-@ go :: acc:UList a -> xs:{v:UList a | intersection (elts acc) (elts xs) = empty} -> {v:UList a | elts v = union (elts acc) (elts xs)} @-}
    go acc [] = acc
    go acc (x:xs) = go (x:acc) xs

-- Exercise 7
{-@ append :: xs:UList a -> ys:{v:UList a | intersection (elts v) (elts xs) = empty} -> {v:UList a | elts v = union (elts xs) (elts ys)} @-}
append [] ys = ys
append (x:xs) ys = x : append xs ys
