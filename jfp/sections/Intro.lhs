%if False
\begin{code}
module Intro where
\end{code}
%endif


\section{Introduction}

Given a string of parentheses, the task is to find a longest consecutive segment that is properly bracketed.
For example, for input |"))(()())())()("| the output should be |"(()())()"|.
We also consider a reduced version of the problem in which we return only the length of the segment.

For an initial specification, balanced parentheses can be captured by a number of grammars that are equivalent, for example |S -> epsilon || (S) || SS|, or |S -> epsilon || (S)S|. We choose the latter because it is both concise and unambiguous. Its parse tree can be represented in Haskell as
\begin{code}
data Tree = Null | Fork Tree Tree {-"~~."-}
\end{code}
%if False
\begin{code}
   deriving (Show, Read, Eq)
\end{code}
%endif
The function |pr| specifies how a |Tree| is printed:
\begin{code}
pr :: Tree -> String
pr Null        = ""
pr (Fork t u)  = "(" ++ pr t ++ ")" ++ pr u {-"~~."-}
\end{code}
The problem can thus be specified by (|lbp| standing for ``longest balanced parentheses''):
\begin{spec}
  lbp = maxBy size . map parse . segments {-"~~,"-}
\end{spec}
where |segments :: [a] -> [[a]]|, defined by |segments = concat . map inits . tails|, returns all segments of a list --- functions |inits, tails :: [a] -> [[a]]| respectively computes all prefixes and suffixes of the input list.
The function |parse :: String -> Tree| builds a parse tree if the given string of parentheses is balanced, and returns a null tree otherwise --- a precise definition will be given later. Given |f :: a -> b| where |b| is a type that is totally ordered, |maxBy f :: [a] -> a| picks a maximum element from a list, and |size t| computes the length of |pr t|.
Specification of the ``length only'' problem is simply |size . lbp|.

To derive an algorithm solving the problem, we start with the usual routine.
Finding an optimal segment is often factored into finding, for each suffix, an optimal prefix:
\begin{spec}
   maxBy size . map parse . segments
=    {- definition of |segments| -}
   maxBy size . map parse . concat . map inits . tails
=    {- since |map f . concat = concat . map (map f)|, |map| fusion -}
   maxBy size . concat . map (map parse . inits) . tails
=    {- since |maxBy . concat = maxBy . map maxBy|, |map| fusion -}
   maxBy size . map (maxBy size . map parse . inits) . tails {-"~~."-}
\end{spec}
That is, for each suffix returned by |tails|, we attempt to compute the longest prefix of balanced parentheses (as in |maxBy size . map parse . inits|).

The next step is usually to apply the ``scan lemma'':
|map (foldr oplus e) . tails = scanr oplus e|.
If we can turn |maxBy size . map parse . inits| into a |foldr|,
the algorithm can proceed in a |scanr|. And if |oplus| is a constant-time operation, we get a linear-time algorithm.
Since |inits| is a |foldr|:
\begin{spec}
  inits = foldr (\x xss -> [] : map (x:) xss) [[]] {-"~~,"-}
\end{spec}
a reasonable attempt is to use the fold-fusion theorem to fuse |map parse| and |maxBy size| into |init|, to form a single |foldr|:
\begin{theorem}[|foldr|-fusion]
  |h . foldr f e = foldr g (h e)| if |h (f x y) = g x (h y)|.
\end{theorem}
Trying to satsify the condition for fusing |map parse| and |inits|:
\begin{spec}
   map parse ([] : map (x:) xss)
=    {- assuming |parse [] = Null| -}
   Null : map (parse . (x:)) xss
=    {- wish, for some |g'| -}
   Null : g' x (map parse xss) {-"~~,"-}
\end{spec}
we wish that |map (parse . (x:)) = g' x . map parse| for some |g'|.
For that to be true, we need |parse (x : xs) = g'' x (parse xs)| for some |g''|, that is, |parse| shall be a |foldr| too. Is that possible?

\paragraph*{Totalising right inverses}
It is about time to be a bit more precise about |parse :: String -> Tree|.
Given a string |xs| of balanced parentheses, |parse xs| should return a tree |t| such that |pr t = xs|.
Therefore, |parse| appears to be related to the right inverse of |pr| ---
that is, the function |inv pr| such that |pr (inv pr xs) = xs|.
However, |inv pr| is a partial function --- there is no |t| such that |pr t = "((("|, for example.
When given such an input, we do not want the entire computation to fail.
Partial computations are typically modeled in Haskell by |Maybe| monad.
For this problem, however, we use a light-weight approach.
We let |parse| return |Null|, which prints to |""|, indeed the longest segment of |"((("| that can be parsed to a tree.
Define the following ``totalising'' operator:
\begin{spec}
total :: (a -> Tree) -> a -> Tree
total f x  = f x   {-"\quad\mbox{, } x \in \Varid{dom}~\Varid{f} "-}
           = Null  {-"\quad\mbox{, otherwise.}"-}
\end{spec}
We let |parse = total (inv pr)|.

Now that |parse| is defined in terms of |inv pr|,
it would be helpful if there is a method to construct the inverse of a function as a fold --- as presented in the next section.
