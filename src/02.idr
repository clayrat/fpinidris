module Main

-- 2.1
total
fibci : Nat -> Int
fibci Z = 0
fibci (S n) = fibTail n 0 1 where 
  fibTail : Nat -> Int -> Int -> Int
  fibTail Z prev _ = prev
  fibTail (S Z) _ cur = cur
  fibTail (S n) prev cur = fibTail n cur (prev + cur)

-- 2.2
isSorted : List a -> (a -> a -> Bool) -> Bool
isSorted Nil _ = True
isSorted (_ :: Nil) _ = True
isSorted (x1 :: x2 :: xs) p = (p x1 x2) && isSorted (x2 :: xs) p 

-- 2.3
currry : ((a, b) -> c) -> (a -> b -> c)
currry f = (\a => \b => f (a, b))

-- 2.4
uncurrry : (a -> b -> c) -> ((a, b) -> c)
uncurrry f = (\(a, b) => f a b)

-- 2.5
compose : (b -> c) -> (a -> b) -> (a -> c)
compose f g = (\a => f (g a))

main : IO ()
main = putStrLn $ show (fibci 1)
