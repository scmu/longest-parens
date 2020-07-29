type List a = [a]

-- S -> ( S ) S
data S = E | B S S deriving (Eq, Show, Read)

size :: S -> Int
size E = 0
size (B t u) = 2 + size t + size u

pr :: S -> String
pr E = ""
pr (B t u) = "(" ++ pr t ++ ")" ++ pr u

type Spine = List S

roll :: Spine -> S
roll [t] = t
roll (t:u:ts) = roll (B t u : ts)

prS :: Spine -> String
prS [t] = pr t
prS (t:ts) = pr t ++ ")" ++ prS ts

build :: String -> Spine
build "" = [E]
build (')':xs) = E : build xs
build ('(':xs) = case build xs of
  [t] -> [E] --- ???
  (t:u:ts) -> B t u : ts

  -- prS : generalised parse
  -- build : right inverse of prS

  -- longest . map parse . inits =
  --      head . build


-- We have

--   prS [E] = ""
--   prS (build (')':xs))
-- = prS (E : build xs)
-- = ')' : prS (build xs)

--   prS (build ('(':xs))
-- = case build xs of (t:u:ts) -> prS (B t u : ts)
-- = case build xs of (t:u:ts) -> "(" ++ pr t ++ ")" ++ pr u ++ ")" ++ prS ts
-- = case build xs of (t:u:ts) -> "(" ++ prS (t:u:ts)
-- = '(' : prS (build xs)


-- longest valid parentheses

lvp :: String -> S
lvp = head . maxBy sizeS . scanr step [E]
   where step ')' ts = E : ts
         step '(' [t] = [E]
         step '(' (t:u:ts) = B t u : ts

sizeS (t:ts) = size t

-- caching the size

type Spine2 = List (S, Int)

lvp2 :: String -> (S, Int)
lvp2 = head . maxBy sizeS2 . scanr step [(E,0)]
   where step ')' ts = (E,0) : ts
         step '(' [t] = [(E,0)]
         step '(' ((t,m):(u,n):ts) = (B t u, 2+m+n) : ts

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
