{- DO NOT CHANGE MODULE NAME, if you do, the file will not load properly -}
module CourseworkRev where

import qualified Data.Set as HS (fromList, toList)
import Test.QuickCheck

{-
  Your task is to design a datatype that represents the mathematical concept of
  a (finite) set of elements (of the same type). We have provided you with an
  interface (do not change this!) but you will need to design the datatype and
  also support the required functions over sets. Any functions you write should
  maintain the following invariant: no duplication of set elements.

  There are lots of different ways to implement a set. The easiest is to use a
  list. Alternatively, one could use an algebraic data type, wrap a binary
  search tree, or even use a self-balancing binary search tree. Extra marks will
  be awarded for efficient implementations (a self-balancing tree will be more
  efficient than a linked list for example).

  You are **NOT** allowed to import anything from the standard library or other
  libraries. Your edit of this file should be completely self-contained.

  **DO NOT** change the type signatures of the functions below: if you do, we
  will not be able to test them and you will get 0% for that part. While sets
  are unordered collections, we have included the Ord constraint on some
  signatures: this is to make testing easier.

  You may write as many auxiliary functions as you need. Everything must be in
  this file.

  See the note **ON MARKING** at the end of the file.
-}

{-
   PART 1.
   You need to define a Set datatype.
-}

-- you **MUST** change this to your own data type. The declaration of Set a =
-- Int is just to allow you to load the file into ghci without an error, it
-- cannot be used to represent a set.
data Set a = Empty | Leaf a | Node (Set a) (Set a) deriving (Show)
{-
   PART 2.
   If you do nothing else, you must get the toList, fromList and equality working. If they
   do not work properly, it is impossible to test your other functions, and you
   will fail the coursework!
-}

removeDuplicates :: (Eq a) => [a] -> [a]
removeDuplicates [] = []
removeDuplicates (x:xs) | x `elem` xs = removeDuplicates xs
                        | otherwise = x : (removeDuplicates xs)

merge :: Ord a => [a] -> [a] -> [a]
merge [] b = b
merge a [] = a
merge a b = if head a <= head b then [head a] ++ merge (tail a) b else [head b] ++ merge a (tail b)

msort :: (Ord a) => [a] -> [a]
msort xs = if length xs <= 1 then xs else merge (msort (take (length xs `div` 2) xs)) (msort [x | x <- xs, not (elem x (take (length xs `div` 2) xs))])

goodList :: (Eq a, Ord a) => [a] -> [a]
goodList xs = msort $ (removeDuplicates xs)

splitList :: [a] -> ([a], [a])
splitList xs = ((take n xs), (drop n xs)) where n = div (length xs) 2

toList' :: Ord a => Set a -> [a]
toList' Empty = []
toList' (Leaf a) = [a]
toList' (Node a b) = (toList a) ++ (toList b)

-- toList {2,1,4,3} => [1,2,3,4]
-- the output must be sorted.
toList :: Ord a => Set a -> [a]
toList x = goodList $ toList' x

-- fromList: do not forget to remove duplicates!
fromList :: Ord a => [a] -> Set a
fromList [] = Empty
fromList xs = let (l, r) = splitList $ goodList xs
              in if l==[] then Leaf (head r)
              else Node (fromList l) (fromList r)

-- Make sure you satisfy this property. If it fails, then all of the functions
-- on Part 3 will also fail their tests
toFromListProp :: IO ()
toFromListProp =
  quickCheck
    ((\xs -> (HS.toList . HS.fromList $ xs) == (toList . fromList $ xs)) :: [Int] -> Bool)

-- test if two sets have the same elements (pointwise equivalent).
instance (Ord a) => Eq (Set a) where
  s1 == s2 = (toList s1) == (toList s2)

-- you should be able to satisfy this property quite easily
eqProp :: IO ()
eqProp =
  quickCheck ((\xs -> (fromList . HS.toList . HS.fromList $ xs) == fromList xs) :: [Char] -> Bool)

{-
   PART 3. Your Set should contain the following functions. DO NOT CHANGE THE
   TYPE SIGNATURES.
-}

-- the empty set
empty :: Set a
empty = Empty

-- is it the empty set?
isNull :: Set a -> Bool
isNull Empty = True
isNull _ = False

-- build a one element Set
singleton :: a -> Set a
singleton x = Leaf x

-- insert an element *x* of type *a* into Set *s*. Make sure there are no
-- duplicates!

getMax :: (Ord a) => Set a -> a
getMax Empty = error "No maximum in empty list"
getMax (Leaf x) = x
getMax (Node x y) = max (getMax x) (getMax y)

getMin :: (Ord a) => Set a -> a
getMin Empty = error "No minimum in empty list"
getMin (Leaf x) = x
getMin (Node x y) = min (getMin x) (getMin y)

insert :: (Ord a) => a -> Set a -> Set a
insert x Empty = Leaf x
insert x (Leaf y) = if x==y then Leaf y else Node (Leaf $ min x y) (Leaf $ max x y)
insert x (Node a b) | x>=(getMin b) = Node a (insert x b)
                    | otherwise = Node (insert x a) b

-- join two Sets together be careful not to introduce duplicates.

inTree :: (Eq a) => a -> Set a -> Bool
inTree _ Empty = False
inTree e (Leaf x) = e==x
inTree e (Node x y) = (inTree e x) || (inTree e y)

union :: (Ord a) => Set a -> Set a -> Set a
union x Empty = x
union Empty y = y
union x (Leaf y) = insert y x
union (Leaf x) y = insert x y
union (Node x y) (Node a b) = (union (Node x y) a) `union `b

-- return, as a Set, the common elements between two Sets
intersection :: (Ord a) => Set a -> Set a -> Set a
intersection x Empty = Empty
intersection Empty y = Empty
intersection (Leaf x) y | inTree x y = Leaf x
                        | otherwise = Empty
intersection x (Leaf y) | inTree y x = Leaf y
                        | otherwise = Empty
intersection (Node x y) (Node a b) = (intersection (Node x y) a) `union` (intersection (Node x y) b)

-- all the elements in *s1* not in *s2*
-- {1,2,3,4} `difference` {3,4} => {1,2}
-- {} `difference` {0} => {}
difference :: (Ord a) => Set a -> Set a -> Set a
difference Empty _ = Empty
difference x Empty = x
difference (Leaf x) (Leaf y) = if x==y then Empty else Leaf x
difference (Node x y) (Leaf a) = (difference x (Leaf a)) `union` (difference y (Leaf a))
difference (Leaf x) (Node a b) = if x `inTree` (Node a b) then Empty else Leaf x
difference (Node x y) a = (difference x a) `union` (difference y a)

-- is element *x* in the Set s1?
member :: (Ord a) => a -> Set a -> Bool
member x Empty = False
member x (Leaf a) = x==a
member x (Node a b) = (member x a) || (member x b)

-- how many elements are there in the Set?
cardinality :: Set a -> Int
cardinality Empty = 0
cardinality (Leaf x) = 1
cardinality (Node x y) = (cardinality x) + (cardinality y)

setmap' :: (Ord b) => (a -> b) -> Set a -> Set b
setmap' f Empty = Empty
setmap' f (Leaf x) = Leaf (f x)
setmap' f (Node x y) = Node (setmap f x) (setmap f y)

-- apply a function to every element in the Set
setmap :: (Ord b) => (a -> b) -> Set a -> Set b
setmap f x = fromList $ toList (setmap' f x)

-- right fold a Set using a function *f*
setfoldr :: (a -> b -> b) -> b -> Set a -> b
setfoldr f acc x = undefined

-- remove an element *x* from the set
-- return the set unaltered if *x* is not present
removeSet :: (Eq a) => a -> Set a -> Set a
removeSet x Empty = Empty
removeSet x (Leaf y) = if x==y then Empty else Leaf y
removeSet x (Node (Leaf a) (Leaf b)) | x==a = Leaf b
                                     | x==b = Leaf a
                                     | otherwise = Node (Leaf a) (Leaf b)
removeSet x (Node (Leaf a) b) = if a==x then b else Node (Leaf a) (removeSet x b)
removeSet x (Node a (Leaf b)) = if b==x then a else Node (removeSet x a) (Leaf b)
removeSet x (Node a b) = Node (removeSet x a) (removeSet x b)

-- powerset of a set
-- powerset {1,2} => { {}, {1}, {2}, {1,2} }
powerset' :: [a] -> [[a]]
powerset' [] = [[]]
powerset' (x:xs) = ys ++ [x:y | y <- ys] where ys = powerset' xs

powerSet :: Set a -> Set (Set a)
powerSet x = undefined

{-
   ON MARKING:

   Be careful! This coursework will be marked using QuickCheck, against
   Haskell's own Data.Set implementation. This testing will be conducted
   automatically via a marking script that tests for equivalence between your
   output and Data.Set's output. There is no room for discussion, a failing test
   means that your function does not work properly: you do not know better than
   QuickCheck and Data.Set! Even one failing test means 0 marks for that
   function. Changing the interface by renaming functions, deleting functions,
   or changing the type of a function will cause the script to fail to load in
   the test harness. This requires manual adjustment by a TA: each manual
   adjustment will lose 10% from your score. If you do not want to/cannot
   implement a function, leave it as it is in the file (with undefined).

   Marks will be lost for too much similarity to the Data.Set implementation.

   Pass: creating the Set type and implementing toList and fromList is enough
   for a passing mark of 40%, as long as both toList and fromList satisfy the
   toFromListProp function.

   The maximum mark for those who use Haskell lists to represent a Set is 70%.
   To achieve a higher grade than is, one must write a more efficient
   implementation. 100% is reserved for those brave few who write their own
   self-balancing binary tree.
-}