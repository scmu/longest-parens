module LongestParens03 where

import Data.List
import Control.Arrow ((&&&))

type List a = [a]

-- S -> ( S ) S
data Tree = N | B Tree Tree deriving (Eq, Show, Read)

size :: Tree -> Int
size N = 0
size (B t u) = 2 + size t + size u

pr :: Tree -> String
pr N = ""
pr (B t u) = "(" ++ pr t ++ ")" ++ pr u

type Forest = List Tree

prF :: Forest -> String
prF [t] = pr t
prF (t:ts) = pr t ++ ")" ++ prF ts

-- map parseF . inits

stage2 :: String -> [Maybe Forest]
stage2 = foldr (\x tss -> Just [N] : map (>>= stepM x) tss) [Just [N]]
  where stepM ')' ts           = Just (N : ts)
        stepM '(' [ t ]        = Nothing
        stepM '(' (t : u : ts) = Just(B t u : ts)

  -- > stage2 "())()("
  -- [Just [N],Nothing,Just [B N N],
  --  Just [B N N,N],Nothing,Just [B N N,B N N],Nothing]

-- filtJust · map parseF · inits

stage3 :: String -> [Forest]
stage3 = foldr (\x tss -> [N] : extend x tss) [[N]]
  where extend ')' tts = map (N:) tts
        extend '(' tts = [(B t u : ts) | (t:u:ts) <- tts]

-- caching the size

type Forest2 = List (Tree, Int)

lbs :: String -> Tree
lbs = fst . maxBy snd . map head . scanr step [(N,0)]
   where step ')' ts  = (N,0) : ts
         step '(' [t] = [(N,0)]
         step '(' ((t,m):(u,n):ts) = (B t u, 2+m+n) : ts

-- size only

type Forest3 = List Int

lbsl :: String -> Int
lbsl = maximum . map head . scanr step [0]
   where step ')' ts  = 0 : ts
         step '(' [_] = [0]
         step '(' (m:n:ts) = (2+m+n) : ts

--
maxBy f [x] = x
maxBy f (x:y:xs) = maxBy f (mx x y : xs)
    where mx x y | f x >= f y = x
                 | otherwise  = y


repeatN n = take n . repeat

(f *** g) (x,y) = (f x, g y)

--

-- a faster pr

pr' :: Tree -> String
pr' t = prAux t []
  where prAux N = id
        prAux (B t u) = ('(':) . prAux t . (')':) . prAux u
