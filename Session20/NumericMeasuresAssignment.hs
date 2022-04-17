{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}

module NumericMeasuresAssignment where
import Prelude hiding (map, size, reverse, zip, zipWith, take, drop, fst, snd, concat, flatten, foldr, head, tail)

{-@ type TRUE = {v:Bool | v} @-}

{-@ die :: {v:_ | false} -> a @-}
die msg = error msg

{-@ type Nat = {v:Int | v >= 0} @-}
{-@ type Pos = {v:Int | v > 0} @-}

type List a = [a]

{-@ invariant { v:List a | 0 <= size v } @-}
{-@ measure size @-}
{-@ size :: xs:List a -> Nat @-}
size :: List a -> Int
size [] = 0
size (_:xs) = 1 + size xs

{-@ measure notEmpty @-}
notEmpty :: List a -> Bool
notEmpty [] = False
notEmpty (_:_) = True

{-@ invariant { v:List a | 0 < size v <=> notEmpty v } @-}

{-@ type ListN a N = {v:List a | size v = N} @-}
{-@ type ListX a X = ListN a (size X) @-}
{-@ type NEList a = {v:List a | notEmpty v} @-}

{-@ map :: (a -> b) -> xs:List a -> ListX b xs @-}
map _ [] = []
map f (x:xs) = f x : map f xs

{-@ propMapId :: List a -> TRUE @-} -- we can prove that size is mantained by mapping the id
propMapId xs = size xs == size ys
  where ys = map id xs

-- Exercise 1
{-@ reverse :: xs:List a -> ListX a xs @-}
{-@ go :: acc:List a -> xs:List a -> { v:List a | size v = size acc + size xs } @-}
reverse xs = go [] xs
  where go acc [] = acc
        go acc (x:xs) = go (x:acc) xs

{-@ zipWith :: (a -> b -> c) -> xs:List a -> ListX b xs -> ListX c xs @-}
zipWith _ [] [] = []
zipWith f (x:xs) (y:ys) = f x y : zipWith f xs ys
zipWith _ _ _ = die "unreachable"

{-@ predicate Tinier X Y Z = Min (size X) (size Y) (size Z) @-}
{-@ predicate Min X Y Z = if Y < Z then X = Y else X = Z @-}
{-@ zip :: xs:List a -> ys:List b -> { v:List (a, b) | Tinier v xs ys } @-}
zip _ [] = []
zip [] _ = []
zip (x:xs) (y:ys) = (x, y) : zip xs ys

-- Exercise 2
{-@ predicate EqualOrZero X Y = if Y /= 0 then (X = Y || X = 0) else True @-}
{-@ predicate AnyZeroOrEqual X Y Z = if (Y = 0 || Z = 0) then X = 0 else X = Y @-}
{-@ zipOrNull :: xs:List a -> ys:{ v:List b | EqualOrZero (size v) (size xs) } -> { v:List (a, b) | AnyZeroOrEqual (size v) (size xs) (size ys) } @-}
zipOrNull _ [] = []
zipOrNull [] _ = []
zipOrNull xs ys = zipWith (,) xs ys

{-@ test1 :: { v:_ | size v = 2 } @-}
test1 = zipOrNull [0, 1] [True, False]

{-@ test2 :: { v:_ | size v = 0 } @-}
test2 = zipOrNull [] [True, False]

{-@ test3 :: { v:_ | size v = 0 } @-}
test3 = zipOrNull ["cat", "dog"] []

{-@ type ListGE a N = {v:List a | size v >= N} @-}

{-@ takeP :: n:Nat -> ListGE a n -> ListN a n @-}
takeP :: Int -> List a -> List a
takeP 0 _ = []
takeP n (x:xs) = x : takeP (n-1) xs
takeP _ _ = die "unreachable"

-- Exercise 3
{-@ dropP :: n:Nat -> xs:ListGE a n -> ListN a {size xs - n} @-}
dropP :: Int -> List a -> List a
dropP 0 xs = xs
dropP n (_:xs) = dropP (n-1) xs
dropP _ _ = die "unreachable"

{-@ test4 :: ListN String 2 @-}
test4 = dropP 1 ["cat", "dog", "mouse"]

-- Exercise 4
{-@ take :: n:Nat -> xs:List a -> {v:List a | Min (size v) n (size xs)} @-}
take :: Int -> List a -> List a
take 0 _ = []
take _ [] = []
take n (x:xs) = x : take (n-1) xs

{-@ test5 :: ListN (ListN String 2) 2 @-}
test5 = [take 2 ["cat", "dog", "mouse"], take 20 ["cow", "goat"]]

{-@ predicate Maxx X Y Z = if Y < Z then X = Z else X = Y @-}
{-@ drop :: n:Nat -> xs:List a -> {v:List a | Maxx (size v) 0 (size xs - n)} @-}
drop :: Int -> List a -> List a
drop _ [] = []
drop 0 xs = xs
drop n (_:xs) = drop (n-1) xs

{-@ test6 :: ListN String 0 @-}
test6 = drop 20 ["cat", "dog", "mouse", "goat"]

{-@ test7 :: ListN String 2 @-}
test7 = drop 2 ["cat", "dog", "mouse", "goat"]

{-@ measure fst @-}
fst :: (a, b) -> a
fst (x, _) = x

{-@ measure snd @-}
snd :: (a, b) -> b
snd (_, y) = y

{-@ predicate Sum2 X N = size (fst X) + size (snd X) = N @-}
{-@ partition :: (a -> Bool) -> xs:List a -> {v:(List a, List a) | Sum2 v (size xs)} @-}
partition _ [] = ([], [])
partition f (x:xs)
    | f x = (x:ys, zs)
    | otherwise = (ys, x:zs)
    where (ys, zs) = partition f xs

{-@ concat :: xs:List a -> ys:List a -> {v:List a | size v = size xs + size ys} @-}
concat [] ys = ys
concat (x:xs) ys = x : concat xs ys

-- Exercise 5
{-@ type IncrList a X = (ListX a X)<{\xi xj -> xi <= xj}> @-} -- taken from https://ucsd-progsys.github.io/liquidhaskell-blog/2013/07/29/putting-things-in-order.lhs/
{-@ quickSort :: (Ord a) => xs:List a -> IncrList a xs / [size xs] @-} -- [size xs] at the end tells LiquidHaskell that that expression decreases (for proving termination)
quickSort :: (Ord a) => List a -> List a
quickSort [] = []
quickSort (x:xs) = concat (concat smallerS (x:equal)) greaterS
  where (smaller, greaterOrEqual) = partition (< x) xs
        (greater, equal) = partition (> x) greaterOrEqual
        smallerS = quickSort smaller
        greaterS = quickSort greater

{-@ data Vector a = V { vDim::Nat, vElts::ListN a vDim } @-}
data Vector a = V { vDim::Int, vElts::List a } deriving (Eq, Show)

{-@ type VectorNE a = {v:Vector a | vDim v > 0} @-}
{-@ type VectorN a N = {v:Vector a | vDim v = N} @-}
{-@ type VectorX a X = VectorN a {vDim X} @-}

{-@ vHd :: VectorNE a -> a @-}
vHd (V _ (x:_)) = x
vHd _ = die "unreachable"

{-@ vTl :: vx:VectorNE a -> VectorN a {vDim vx - 1} @-}
vTl (V n (_:xs)) = V (n-1) xs
vTl _ = die "unreachable"

{-@ for :: vx:Vector a -> (a -> b) -> VectorX b vx @-}
for :: Vector a -> (a -> b) -> Vector b
for (V n xs) f = V n (map f xs)

{-@ vBin :: (a -> b -> c) -> vx:Vector a -> VectorX b vx -> VectorX c vx @-}
vBin op (V n xs) (V _ ys) = V n (zipWith op xs ys)

{-@ dotProduct :: (Num a) -> vx:Vector a -> VectorX a vx -> a @-}
dotProduct vx vy = sum $ vElts $ vBin (*) vx vy

-- Exercise 6
{-@ vecFromList :: xs:List a -> VectorN a {size xs} @-}
vecFromList :: List a -> Vector a
vecFromList xs = V (size xs) xs

test8 = dotProduct vs ws
  where vs = vecFromList [1, 2, 3]
        ws = vecFromList [4, 5, 6]

-- Exercise 7
{-@ measure head @-}
{-@ head :: NEList a -> a @-}
head (x:_) = x

{-@ measure tail @-}
{-@ tail :: xs:NEList a -> ListN a {size xs - 1} @-}
tail (_:xs) = xs

{-@ flattenList :: n:Nat -> m:Nat -> ListN (ListN a m) n -> ListN a {m*n} @-}
flattenList :: Int -> Int -> List (List a) -> List a
flattenList 0 _ _ = []
flattenList n m xss = concat (head xss) (flattenList (n-1) m (tail xss))

{-@ flatten :: n:Nat -> m:Nat -> VectorN (VectorN a m) n -> VectorN a {m*n} @-}
flatten :: Int -> Int -> Vector (Vector a) -> Vector a
flatten n m (V _ vxs) = V (m*n) (flattenList n m (map vElts vxs))

{-@ data Matrix a = M { mRow::Pos, mCol::Pos, mElts::VectorN (VectorN a mCol) mRow } @-}
data Matrix a = M { mRow::Int, mCol::Int, mElts::Vector (Vector a) } deriving (Eq, Show)

{-@ predicate Dims M R C = mRow M = R && mCol M = C @-}
{-@ type MatrixN a R C = {v:Matrix a | Dims v R C} @-}

-- Exercise 8
matrixExample :: Matrix Int
matrixExample = M 2 3 (V 2 [V 3 [1, 2, 3], V 3 [4, 5, 6]])

anotherMatrixExample :: Matrix Int
anotherMatrixExample = M 2 2 (V 2 [V 2 [1, 2], V 2 [4, 5]])

-- Exercise 9
{-@ withSize :: xss:List (List a) -> Maybe (ListX (ListX a (head xss)) xss) @-}
withSize :: List (List a) -> Maybe (List (List a))
withSize [] = Nothing
withSize (xs:[]) = Just $ xs:[]
withSize (xs:xss)
    | ok = fmap (\zss -> xs:zss) yss
    | otherwise = Nothing
  where c = size xs
        yss = withSize xss
        ok = size (head xss) == c

{-@ matFromListWithSize :: c:Pos -> r:Pos -> ListN (ListN a c) r -> MatrixN a r c @-}
matFromListWithSize :: Int -> Int -> List (List a) -> Matrix a
matFromListWithSize c r xss = M r c (vecFromList (map vecFromList xss))

{-@ matFromList :: xss:List (List a) -> Maybe (MatrixN a (size xss) (size (head xss))) @-}
matFromList :: List (List a) -> Maybe (Matrix a)
matFromList [] = Nothing
matFromList xss@(xs:_)
    | c > 0 = fmap (matFromListWithSize c r) (withSize xss)
    | otherwise = Nothing
  where r = size xss
        c = size xs

{-@ test9 :: Maybe (MatrixN Int 2 3) @-}
test9 :: Maybe (Matrix Int)
test9 = matFromList [[1, 2, 3], [4, 5, 6]]
