type List a = [a]

data T = N (List T)
  deriving (Show, Read, Eq)

size :: T -> Int  -- length of string when printed
size (N ts) = 2 + sizeF ts

sizeF :: List T -> Int
sizeF = sum . map size

lv = N []

pr :: T -> String
pr (N ts) = "(" ++ prF ts ++ ")"

prF :: List T -> String
prF = concat . map pr

type Spine = List (List T)

roll :: Spine -> T
roll [ts] = N ts
roll (ts:us:tss) = roll ((N ts : us) : tss)

  -- roll' t (ts:tss) = roll ((t:ts):tss)

roll' :: T -> Spine -> T
roll' t [] = t
roll' t (ts:tss) = roll' (N (t:ts)) tss

prS :: Spine -> String
prS [] = []
prS ([]:tss) = ')' : prS tss
prS ((N ts:us):tss) = '(' : prS (ts:us:tss)

prS'' tss = repeatN (length tss) '(' ++
               foldr step "" tss
      where step ts xs = prF ts ++ ")" ++ xs
{-

Lemma:

 pr (roll tss) = prS'' tss
         = repeatN (length tss) '(' ++  foldr step "" tss

Proof.
   pr (roll [ts])
 = pr (N ts)
 = "(" ++ prF ts ++ ")"
 = repeat 1 '(' ++ foldr step "" [ts]
 = prS'' [ts]

   pr (roll (ts:us:tss))
 = pr (roll ((N ts : us) : tss))
 =    { induction }
   repeatN (length tss) '(' ++ "(" ++
     pr N ts ++ prF us ++ ")" ++ foldr step base tss
 = repeatN (length tss) '(' ++ "(" ++
     "(" ++ prF ts ")" ++ prF us ++ ")" ++ foldr step base tss
 = repeatN (2 + length tss) '()' ++
    foldr step base (ts:us:tss)
 = prS'' (ts:us:tss)

-}

{-

prS = foldr step "" tss
     where step ts xs = prF ts ++ ")" ++ xs

prS [] = ""

  prS ([]:tss)
= step [] (prS tss)
= prF [] ++ ")" ++ prS tss
= ')' : prS tss

  prS ((N ts : us) : tss)
= step (t:ts) (prS tss)
= pr N ts ++ prF us  ++ ")" ++ prS tss
= "(" ++ prF ts ++ ")" ++ prF us  ++ ")" ++ prS tss
= '(' : prS (ts:us:tss)

Thus we have

prS :: Spine -> String
prS [] = []
prS ([]:tss) = ')' : prS tss
prS ((N ts:us):tss) = '(' : prS (ts:us:tss)

-}

--
type SF = (Spine, List T)

{-
prSF (sp,tss) = prS sp ++ prF tss

prSF ([],[]) = []
prSF ([]:tss,uss) = ')' : prSF (tss,uss)
prSF ((N ts:us):tss, uss) = '(' : prSF (ts:us:tss, uss)

prSF ([],N ts:uss) = '(' : prF ts ++ ")" ++ prF uss
= '(' : prSF ([ts], uss)
-}

prSF :: SF -> String
prSF ([],[]) = []
prSF ([], N ts:uss) = '(' : prSF ([ts], uss)
prSF ([]:tss, uss)  = ')' : prSF (tss,uss)
prSF ((N ts:us):tss, uss) = '(' : prSF (ts:us:tss, uss)


buildSF :: String -> SF
buildSF [] = ([], [])
buildSF (')':xs) = (([]:) *** id) $ buildSF xs
buildSF ('(':xs) = case buildSF xs of
   ([],        tss) -> ([],[])              -- additional case
   ([ts],      uss) -> ([], N ts:uss)
   (ts:us:tss, uss) -> ((N ts:us):tss, uss)


--
 -- obselete

build :: String -> Spine
build [] = []
build (')':xs) = [] : build xs
build ('(':xs) = (N ts : us) : tss
   where (ts:us:tss) = build xs

-- longest valid parentheses

lvp :: String -> SF
lvp = longest . scanr step ([],[])
  where step ')' (sp,us) = ([]:sp, us)
        step '(' ([], tss) = ([],[])
        step '(' ([ts],      uss) = ([], N ts:uss)
        step '(' (ts:us:tss, uss) = ((N ts:us):tss, uss)

sizeSF :: SF -> Int
sizeSF ([],us) = sizeF us
sizeSF (ts:tss, us) = sizeF ts

prRes :: SF -> String
prRes ([],us) = prF us
prRes (ts:tss, us) = prF ts

longest [sf] = sf
longest (x1:x2:sf) = longest (lng x1 x2 : sf)
  where lng x1 x2 | sizeSF x1 >= sizeSF x2 = x1
                  | otherwise = x2

--- cached size

type Spine2 = List (List T, Int)
type SF2 = (Spine2, (List T, Int))

lvp2 :: String -> SF2
lvp2 = longest2 . scanr step ([],([],0))
  where step ')' (sp,us) = (([],0):sp, us)
        step '(' ([], tss) = ([],([],0))
        step '(' ([(ts, m)], (uss,k)) = ([], (N ts:uss, m+k+2))
        step '(' ((ts,m):(us,n):tss, uss) = ((N ts:us, m+n+2):tss, uss)

sizeSF2 :: SF2 -> Int
sizeSF2 ([],(us,k)) = k
sizeSF2 ((ts,m):tss, us) = m

prRes2 :: SF2 -> (String, Int)
prRes2 ([],(us,k)) = (prF us, k)
prRes2 ((ts,m):tss, us) = (prF ts, m)

longest2 [sf] = sf
longest2 (x1:x2:sf) = longest2 (lng x1 x2 : sf)
  where lng x1 x2 | sizeSF2 x1 >= sizeSF2 x2 = x1
                  | otherwise = x2

--- returning only the size

type Spine3 = List Int
type SF3 = (Spine3, Int)

-- lvp3 :: String -> SF3
lvp3 = --longest3 .
     scanr step ([],0)
  where step ')' (ns,  k) = (0:ns, k)
        step '(' ([],  k) = ([], 0)
        step '(' ([m], k) = ([], m+k+2)
        step '(' (m:n:ns, k) = (m+n+2:ns, k)

sizeSF3 :: SF3 -> Int
sizeSF3 ([],   k) = k
sizeSF3 (m:ns, k) = m

prRes3 :: SF3 -> Int
prRes3 ([],k) = k
prRes3 (m:ns, k) = m

longest3 [sf] = sf
longest3 (x1:x2:sf) = longest3 (lng x1 x2 : sf)
  where lng x1 x2 | sizeSF3 x1 >= sizeSF3 x2 = x1
                  | otherwise = x2

---
repeatN n = take n . repeat

(f *** g) (x,y) = (f x, g y)
