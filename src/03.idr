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
foldRight : List a -> b -> (a -> b ->b) -> b
foldRight Nil z _ = z
foldRight (x :: xs) z f = f x (foldRight xs z f)

-- 3.8: proving!!!
foldRightWithNilAndConsIsId : (xs : List a) -> foldRight xs Nil (::) = xs
foldRightWithNilAndConsIsId Nil = ?foldRightWithNilAndConsIsId_Nil
foldRightWithNilAndConsIsId (x :: xs) = let ih = foldRightWithNilAndConsIsId xs in ?foldRightWithNilAndConsIsId_Cons

-- 3.9
myLength : List a -> Nat
myLength l = foldRight l Z (\_ => \acc => S acc)

main : IO ()
main = putStrLn $ show (length [1..5])

---------- Proofs ----------

Main.foldRightWithNilAndConsIsId_Nil = proof
  intros
  trivial

Main.foldRightWithNilAndConsIsId_Cons = proof
  intros
  rewrite ih
  trivial


