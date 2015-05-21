module Main

-- 2.1
fibci : Int -> Int
fibci n = fibTail n 0 1 where 
  fibTail : Int -> Int -> Int -> Int
  fibTail 1 prev _ = prev
  fibTail 2 _ cur = cur
  fibTail n prev cur = fibTail (n-1) cur (prev+cur)

-- 2.2
isSorted : List a -> (a -> a -> Bool) -> Bool
isSorted Nil _ = True
isSorted (_ :: Nil) _ = True
isSorted (x1 :: x2 :: xs) p = (p x1 x2) && isSorted (x2 :: xs) p 

-- 2.3
cury : ((a, b) -> c) -> (a -> b -> c)
cury f = (\a => \b => f (a, b))

-- 2.4
uncury : (a -> b -> c) -> ((a, b) -> c)
uncury f = (\(a, b) => f a b)

-- 2.5
compose : (b -> c) -> (a -> b) -> (a -> c)
compose f g = (\a => f (g a))

main : IO ()
main = putStrLn $ show (isSorted [1, 3, 2] (\x => \y => x < y))