module Main where

--main :: IO ()
main = mapM_ (putStrLn . show) (map (\x -> x*x) [1..25])
--
--
    where curried = (2+)