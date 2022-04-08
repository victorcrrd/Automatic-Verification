{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}

module BooleanMeasuresAssignment where
import Prelude hiding (foldl, foldl1, map, sum, size, head, tail, null)

{-@ type NonZero = { v:Int | v /= 0 } @-}

{-@ die :: { v:_ | false } -> a @-}
die msg = error msg

{-@ divide :: Int -> NonZero -> Int @-}
divide :: Int -> Int -> Int
divide _ 0 = die "division by zero" -- not necessary, but tells us about non-reachable code
divide x n = x `div` n

{-@ measure sizeLH @-}
{-@ type Nat = { v:Int | v >= 0 } @-}
{- type refined below {-@ sizeLH :: [a] -> Nat @-} -}
sizeLH :: [a] -> Int
sizeLH [] = 0
sizeLH (_:xs) = 1 + sizeLH xs

{-@ type GT0List a = { v:[a] | sizeLH v > 0 } @-}
{-@ avgMany :: GT0List Int -> Int @-}
avgMany :: [Int] -> Int
avgMany xs = divide total elems
  where total = sum xs
        elems = sizeLH xs

{-@ measure notEmpty @-}
{-@ notEmpty :: [a] -> Bool @-}
notEmpty :: [a] -> Bool
notEmpty [] = False
notEmpty (_:_) = True

{-@ type NEList a = { v:[a] | notEmpty v } @-}
{-@ sizeLH :: xs:[a] -> { v:Nat | notEmpty xs <=> v > 0 } @-}
{-@ avgManyP :: NEList Int -> Int @-}
avgManyP :: [Int] -> Int
avgManyP xs = divide total elems
  where total = sum xs
        elems = sizeLH xs

avgManyMaybe :: [Int] -> Maybe Int
avgManyMaybe xs
    | notEmpty xs = Just $ divide (sum xs) elems
    | otherwise = Nothing
      where elems = sizeLH xs

{- the following variants of size are rejected by LiquidHaskell
{-@ anotherSize :: NEList a -> Pos @-}
anotherSize :: [a] -> Int
anotherSize []     =  0
anotherSize (_:xs) =  1 + anotherSize xs

{-@ yetAnotherSize :: xs:[a] -> { v:Int | notEmpty xs => v > 0 } @-}
yetAnotherSize :: [a] -> Int
yetAnotherSize [] = 0
yetAnotherSize (_:xs) = 1 + yetAnotherSize xs -}

{-@ anotherSize :: NEList a -> { v:Int | v > 0 } @-}
anotherSize :: [a] -> Int
anotherSize (_:[]) = 1
anotherSize (_:xs) = 1 + anotherSize xs

{-@ yetAnotherSize :: xs:[a] -> { v:Nat | notEmpty xs => v > 0 } @-}
yetAnotherSize :: [a] -> Int
yetAnotherSize [] = 0
yetAnotherSize (_:xs) = 1 + yetAnotherSize xs

{-@ head :: NEList a -> a @-}
head :: [a] -> a
head (x:_) = x
head [] = die "not reachable" -- not necessary, but tells us about non-reachable code

{-@ tail :: NEList a -> [a] @-}
tail :: [a] -> [a]
tail (_:xs) = xs
tail [] = die "not reachable" -- not necessary, but tells us about non-reachable code

safeHead :: [a] -> Maybe a
safeHead xs
    | null xs = Nothing
    | otherwise = Just $ head xs

{-@ null :: xs:[a] -> { v:Bool | v <=> not (notEmpty xs) } @-}
null :: [a] -> Bool
null [] = True
null (_:_) = False

{-@ groupEq :: (Eq a) => [a] -> [NEList a] @-}
groupEq [] = []
groupEq (x:xs) = (x:ys) : groupEq zs
  where
    (ys, zs) = span (x ==) xs

eliminateStutter xs = map head $ groupEq xs

{-@ foldl1 :: (a -> a -> a) -> NEList a -> a @-}
foldl1 f (x:xs) = foldl f x xs
foldl1 _ [] = die "not reachable" -- not necessary, but tells us about non-reachable code

foldl :: (a -> b -> a) -> a -> [b] -> a
foldl _ acc [] = acc
foldl f acc (x:xs) = foldl f (f acc x) xs

{-@ map :: (a -> b) -> xs:[a] -> { ys:[b] | sizeLH ys == sizeLH xs } @-}
map _ [] = []
map f (x:xs) = f x : map f xs

{-@ sum :: (Num a) => NEList a -> a @-}
sum xs@(_:_) = foldl1 (+) xs -- annotation not necessary, but avoids a warning
sum [] = die "not reachable" -- not necessary, but tells us about non-reachable code

{-@ type Pos = { v:Int | v > 0 } @-}
{-@ wtAverage :: NEList (Pos, Pos) -> Int @-}
wtAverage wxs = divide totElems totWeight
  where elems = map (\(w, x) -> w * x) wxs
        weights = map (\(w, _) -> w) wxs
        totElems = sum elems
        totWeight = sum weights
        sum = foldl1 (+)

{-@ risers :: (Ord a) => NEList a -> NEList (NEList a) @-}
risers [] = die "not reachable" -- not necessary, but tells us about non-reachable code
risers [x] = [[x]]
risers (x:y:etc)
    | x <= y = (x:s):ss
    | otherwise = [x] : (s:ss)
      where (s, ss) = safeSplit $ risers (y:etc)

{-@ safeSplit :: NEList a -> (a, [a]) @-}
safeSplit (x:xs) = (x, xs)
safeSplit [] = die "not reachable" -- not necessary, but tells us about non-reachable code
