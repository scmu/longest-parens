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

type Spine = List Tree

roll :: Spine -> Tree
roll [t] = t
roll (t:u:ts) = roll (F t u : ts)

prS :: Spine -> String
prS [t] = pr t
prS (t:ts) = pr t ++ ")" ++ prS ts

build :: String -> Spine
build "" = [N]
build (')':xs) = N : build xs
build ('(':xs) = case build xs of
  [t] -> [N] --- ???
  (t:u:ts) -> F t u : ts

  -- prS : generalised parse
  -- build : right inverse of prS

  -- longest . map parse . inits =
  --      head . build


-- We have

--   prS [N] = ""
--   prS (build (')':xs))
-- = prS (N : build xs)
-- = ')' : prS (build xs)

--   prS (build ('(':xs))
-- = case build xs of (t:u:ts) -> prS (F t u : ts)
-- = case build xs of (t:u:ts) -> "(" ++ pr t ++ ")" ++ pr u ++ ")" ++ prS ts
-- = case build xs of (t:u:ts) -> "(" ++ prS (t:u:ts)
-- = '(' : prS (build xs)


-- longest valid parentheses

lvp :: String -> Tree
lvp = head . maxBy sizeS . scanr step [N]
   where step ')' ts = N : ts
         step '(' [t] = [N]
         step '(' (t:u:ts) = F t u : ts

sizeS (t:ts) = size t

-- caching the size

type Spine2 = List (Tree, Int)

lvp2 :: String -> (Tree, Int)
lvp2 = head . maxBy sizeS2 . scanr step [(N,0)]
   where step ')' ts = (N,0) : ts
         step '(' [t] = [(N,0)]
         step '(' ((t,m):(u,n):ts) = (F t u, 2+m+n) : ts

sizeS2 ((t,n):ts) = n

-- size only

type Spine3 = List Int

lvp3 :: String -> Int
lvp3 = head . maxBy sizeS3 . scanr step [0]
   where step ')' ts = 0 : ts
         step '(' [_] = [0]
         step '(' (m:n:ts) = (2+m+n) : ts

sizeS3 (n:ts) = n


--
maxBy f [x] = x
maxBy f (x:y:xs) = maxBy f (mx x y : xs)
    where mx x y | f x >= f y = x
                 | otherwise  = y


repeatN n = take n . repeat

(f *** g) (x,y) = (f x, g y)
