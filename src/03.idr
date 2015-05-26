module Main

-- 3.1
weirdMatch : List Int -> Int
weirdMatch (x :: 2 :: 4 :: _) = x                  
weirdMatch Nil = 42                                          
weirdMatch (h :: t) = h + sum t
weirdMatch (x :: y :: 3 :: 4 :: _) = x + y     
weirdMatch _ = 101

-- 3.2
myTail : List a -> Maybe (List a)
myTail Nil = Nothing
myTail (_ :: xs) = Just xs

-- 3.3
setHead : List a -> a -> Maybe (List a)
setHead Nil _ = Nothing
setHead (x :: xs) x1 = Just (x1 :: xs)

-- 3.4
safeDrop : List a -> Nat -> List a
safeDrop Nil _ = Nil
safeDrop l Z = l
safeDrop (x :: xs) (S n) = safeDrop xs n

-- 3.5
myDropWhile : List a -> (a -> Bool) -> List a
myDropWhile Nil _ = Nil
myDropWhile (x :: xs) p = if p x then myDropWhile xs p else (x :: xs)

-- 3.6
init : List a -> List a
init Nil = Nil
init (_ :: Nil) = Nil
init (x :: xs) = x :: init xs  

-- 3.7: no because foldright is eager
foldRight : List a -> b -> (a -> b -> b) -> b
foldRight Nil z _ = z
foldRight (x :: xs) z f = f x (foldRight xs z f)

-- 3.8: proving!!!
foldRightWithNilAndConsIsId : (xs : List a) -> foldRight xs Nil (::) = xs
foldRightWithNilAndConsIsId Nil = ?foldRightWithNilAndConsIsId_Nil
foldRightWithNilAndConsIsId (x :: xs) = let ih = foldRightWithNilAndConsIsId xs in ?foldRightWithNilAndConsIsId_Cons

-- 3.9
myLength : List a -> Nat
myLength l = foldRight l Z (\_, acc => S acc)

-- 3.10
foldLeft: List a -> b -> (b -> a -> b) -> b
foldLeft Nil z _ = z
foldLeft (x :: xs) acc f = foldLeft xs (f acc x) f

-- 3.11
sumLeft: List Int -> Int
sumLeft l = foldLeft l 0 (+)

productLeft: List Int -> Int
productLeft l = foldLeft l 1 (*)

lengthLeft: List a -> Nat
lengthLeft l = foldLeft l Z (\acc, _ => S acc)

-- 3.12
reverseList: List a -> List a
reverseList l = foldLeft l Nil (flip (::))

-- 3.13
foldLeftViaRight : List a -> b -> (b -> a -> b) -> b
foldLeftViaRight l z f = foldRight l id (\a, g => \b => g $ f b a) z 

foldRightViaLeft : List a -> b -> (a -> b -> b) -> b
foldRightViaLeft l z f = foldLeft (reverse l) z (flip f) 

-- 3.14
appendRight : List a -> List a -> List a
appendRight l1 l2 = foldRight l1 l2 (::)

-- 3.15
concatRight : List (List a) -> List a
concatRight ll = foldRight ll Nil appendRight

-- 3.16
add1 : List Int -> List Int
add1 l = foldRight l Nil (\x, xs => x + 1 :: xs)

-- 3.17
stringify : List Double -> List String
stringify l = foldRight l Nil (\x, xs => show x :: xs)

-- 3.18
mapList : List a -> (a -> b) -> List b
mapList l f = foldRight l Nil (\x, xs => f x :: xs)

-- 3.19
filterList : List a -> (a -> Bool) -> List a
filterList l p = foldRight l Nil (\x, xs => if p x then x :: xs else xs)

-- 3.20
flatMapList : List a -> (a -> List b) -> List b
flatMapList l f = concatRight (mapList l f)

-- 3.21
filterViaFlatMap: List a -> (a -> Bool) -> List a
filterViaFlatMap l p = flatMapList l (\x => if p x then [x] else Nil) 

-- 3.22
zipAdd : List Int -> List Int -> List Int
zipAdd _ Nil = Nil
zipAdd Nil _ = Nil
zipAdd (x :: xs) (y :: ys) = x + y :: zipAdd xs ys

-- 3.23
myZipWith : List a -> List b -> (a -> b -> c) -> List c
myZipWith _ Nil _ = Nil
myZipWith Nil _ _ = Nil
myZipWith (x :: xs) (y :: ys) f = f x y :: myZipWith xs ys f 

-- 3.24
startsW : Eq a => List a -> List a -> Bool
startsW _ Nil = True
startsW Nil _ = False 
startsW (x :: xs) (y :: ys) = if x == y then startsW xs ys else False

hasSubseq : Eq a => List a -> List a -> Bool
hasSubseq Nil Nil = True
hasSubseq Nil (_ :: _) = False
hasSubseq (x :: xs) s = if startsW (x :: xs) s then True else hasSubseq xs s

main : IO ()
main = putStrLn $ show$ hasSubseq [1..4] [2]
---------- Proofs ----------

Main.foldRightWithNilAndConsIsId_Nil = proof
  intros
  trivial

Main.foldRightWithNilAndConsIsId_Cons = proof
  intros
  rewrite ih
  trivial


