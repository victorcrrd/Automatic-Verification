{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names" @-}

module TreesAssignment where
import Prelude hiding (head, max)

{-@ die :: { v:_ | false } -> a @-}
die msg = error msg

{-@ type BiggerThan a N = { v:a | v >= N } @-}

infixr 9 :<
data IncList a = Emp | (:<) { hd::a, tl::IncList a }
{-@ data IncList a = Emp | (:<) { hd::a, tl::IncList (BiggerThan a hd) } @-}

data BST a = Leaf | Node { root::a, left::BST a, right::BST a }
{-@ data BST a = Leaf | Node { root::a, left::BSTL a root, right::BSTR a root } @-}
{-@ type BSTL a X = BST { v:a | v < X } @-}
{-@ type BSTR a X = BST { v:a | X < v } @-}

{- rejected by LiquidHaskell
{-@ badBST :: BST Int @-}
badBST = Node 66
            (Node 4
                (Node 1 Leaf Leaf)
                (Node 69 Leaf Leaf)
            )
            (Node 99
                Leaf
                (Node 77 Leaf Leaf)
            )
-}

{-@ member :: (Ord a) => a -> BST a -> Bool @-}
member _ Leaf = False
member x (Node y l r)
    | x > y = member x r
    | x < y = member x l
    | otherwise = True

{-@ add :: (Ord a) => a -> BST a -> BST a @-}
add x Leaf = Node x Leaf Leaf
add x t@(Node y l r)
    | x < y = Node y (add x l) r
    | y < x = Node y l (add x r)
    | otherwise = t

data MinPair a = MP { mElt::a, rest::BST a }
{-@ data MinPair a = MP { mElt::a, rest::BSTR a mElt } @-}

{-@ measure notLeaf @-}
{-@ notLeaf :: (Ord a) => BST a -> Bool @-}
notLeaf Leaf = False
notLeaf (Node _ _ _) = True

{-@ type NotLeaf a = { v:BST a | notLeaf v } @-}
{-@ delMin :: (Ord a) => NotLeaf a -> MinPair a @-}
delMin (Node x Leaf r) = MP x r
delMin (Node x l r) = MP y (Node x lp r)
  where MP y lp = delMin l
delMin Leaf = die "undefined" -- may be removed

{-@ delete :: (Ord a) => a -> BST a -> BST a @-}
delete _ Leaf = Leaf
delete x t@(Node y l r)
    | x < y = Node y (delete x l) r
    | y < x = Node y l (delete x r)
    | notLeaf r = let MP z rp = delMin r in Node z l rp
    | otherwise = l

bstSort :: (Ord a) => [a] -> IncList a
bstSort = toIncList . toBST

toBST :: (Ord a) => [a] -> BST a
toBST = foldr add Leaf

toIncList :: BST a -> IncList a
toIncList (Node x l r) = join x (toIncList l) (toIncList r)
toIncList Leaf = Emp

{-@ type IncListLT a X = IncList { v:a | v < X } @-}
{-@ type IncListGT a X = IncList { v:a | X < v } @-}
{-@ join :: (Ord a) => z:a -> IncListLT a z -> IncListGT a z -> IncList a @-}
join z Emp ys = z :< ys
join z (x :< xs) ys = x :< join z xs ys

data SkewHeap a = EmpS | NodeS { rootS::a, leftS::SkewHeap a, rightS::SkewHeap a }
{-@ data SkewHeap a = EmpS | NodeS { rootS::a, leftS::SkewHeap { v:a | rootS <= v }, rightS::SkewHeap { v:a | rootS <= v } } @-}

{-@ type NotEmpS a = { v:SkewHeap a | notEmpS v } @-}
{-@ measure notEmpS @-}
notEmpS :: SkewHeap a -> Bool
notEmpS EmpS = False
notEmpS (NodeS _ _ _) = True

{-@ measure minimum @-}
{-@ minimum :: NotEmpS a -> a @-}
minimum (NodeS r _ _) = r

{-@ cast :: h:NotEmpS a -> NotEmpS { v:a | minimum h <= v } @-}
cast (NodeS x l r) = NodeS x l r -- interestingly, if the equation is cast h = h it doesn't work

{-@ joinS :: SkewHeap a -> SkewHeap a -> SkewHeap a @-}
joinS EmpS EmpS = EmpS
joinS EmpS h2@(NodeS _ _ _) = h2
joinS h1@(NodeS _ _ _) EmpS = h1
joinS h1@(NodeS x1 l1 r1) h2@(NodeS x2 l2 r2)
    | x1 <= x2 = NodeS x1 (joinS r1 (cast h2)) l1
    | otherwise = NodeS x2 (joinS r2 (cast h1)) l2
