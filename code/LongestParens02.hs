import Data.List
import Control.Arrow ((&&&))

type List a = [a]

-- S -> ( S ) S
data Tree = N | F Tree Tree deriving (Eq, Show, Read)

size :: Tree -> Int
size N = 0
size (F t u) = 2 + size t + size u

pr :: Tree -> String
pr N = ""
pr (F t u) = "(" ++ pr t ++ ")" ++ pr u

type Spine = (Tree, List Tree)

roll :: Spine -> Tree
roll (t, []) = t
roll (t, u:ts) = roll (F t u, ts)

{-

lemma:

pr (roll (t,ts)) =
   replicate (length ts) '(' ++
     pr t ++ foldr (\t xs -> ")" ++ pr t ++ xs) "" ts
-}

prS :: Spine -> String
prS (t,ts) = pr t ++ foldr (\t xs -> ")" ++ pr t ++ xs) "" ts

{-

prS (N, []) = ""

prS (N, t:ts)
= ')' : pr t ++ foldr (\v xs -> ")" ++ pr v ++ xs) "" ts
= ')' : prS (t,ts)

prS (F t u, ts) =
= '(' : pr t ++ ")" ++ pr u ++ foldr (\v xs -> ")" ++ pr v ++ xs) "" ts
= '(' : prS (t, u:ts)

-}

 -- prS' = prS
prS' :: Spine -> String
prS' (N,     []) = ""
prS' (N,   t:ts) = ')' : prS' (t,ts)
prS' (F t u, ts) = '(' : prS' (t, u:ts)

prSinv :: String -> Spine
prSinv ""       = (N,[])
prSinv (')':xs) = case prSinv xs of (t,ts) -> (N, t:ts)
prSinv ('(':xs) = case prSinv xs of (t,u:ts) -> (F t u, ts)


build :: String -> Spine
build ""       = (N,[])
build (')':xs) = case build xs of (t,ts) -> (N, t:ts)
build ('(':xs) = case build xs of
    (t,[])   -> (N,[])
    (t,u:ts) -> (F t u, ts)

-- longest valid parentheses

lvp :: String -> Tree
lvp = fst . maxBy sizeS . scanr step (N,[])
   where step ')' (t, ts)   = (N, t:ts)
         step '(' (t, [])   = (N,[])
         step '(' (t, u:ts) = (F t u, ts)

sizeS (t,ts) = size t

-- caching the size

type Spine2 = ((Tree, Int), List (Tree, Int))

lvp2 :: String -> (Tree, Int)
lvp2 = fst . maxBy sizeS2 . scanr step ((N,0),[])
   where step ')' (t,ts) = ((N,0),t:ts)
         step '(' (t,[]) = ((N,0),[])
         step '(' ((t,m),(u,n):ts) = ((F t u, 2+m+n),ts)

sizeS2 ((t,n),ts) = n

-- size only

type Spine3 = (Int, List Int)

lvp3 :: String -> Int
lvp3 = fst . maxBy sizeS3 . scanr step (0,[])
   where step ')' (t,ts) = (0,t:ts)
         step '(' (t,[]) = (0,[])
         step '(' (m,n:ts) = (2+m+n, ts)

sizeS3 (n,ts) = n


--
maxBy f [x] = x
maxBy f (x:y:xs) = maxBy f (mx x y : xs)
    where mx x y | f x >= f y = x
                 | otherwise  = y


repeatN n = take n . repeat

(f *** g) (x,y) = (f x, g y)
