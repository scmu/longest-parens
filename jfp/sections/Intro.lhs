%if False
\begin{code}
module Intro where
\end{code}
%endif

\section{Introduction}

Given a string of parentheses, the task is to find a longest consecutive segment that is properly bracketed.
For example, for input |"))(()())())()("| the output should be |"(()())()"|.
We also consider a reduced version of the problem in which we return only the length of the segment.

For an initial specification, balanced parentheses can be captured by a number of grammars that are equivalent, for example |S -> epsilon || (S) || SS|, or |S -> epsilon || (S)S|. We choose the latter because it is both concise and unambiguous. Its parse tree can be represented in Haskell as below,
with a function |pr| specifying how a tree is printed:
\begin{code}
data Tree = Null | Fork Tree Tree {-"~~,"-}

pr :: Tree -> String
pr Null        = ""
pr (Fork t u)  = "(" ++ pr t ++ ")" ++ pr u {-"~~."-}
\end{code}
%if False
\begin{code}
deriving instance Show Tree
deriving instance Read Tree
deriving instance Eq   Tree
\end{code}
%endif
The problem can thus be specified by (|lbp| standing for ``longest balanced parentheses''):
\begin{spec}
  lbp = maxBy size . filtJust . map parse . segments {-"~~,"-}

  segments = concat . map inits tails {-"~~,"-}
  filtJust ts = [t | Just t <- ts] {-"~~,"-}
  size t = length (pr t) {-"~~."-}
\end{spec}
The function |segments :: [a] -> [[a]]| returns all segments of a list, with |inits, tails :: [a] -> [[a]]| respectively compute all prefixes and suffixes of the input list.
The function |parse :: String -> Maybe Tree| builds a parse tree ---
|parse xs| should return |Just t| such that |pr t = xs| if |xs| is balanced, and return |Nothing| otherwise.
It is related to the right inverse of |pr|,
that is, the function |inv pr| such that |pr (inv pr xs) = xs|.
The function |inv pr| is partial (e.g. there is no |t| such that |pr t = "((("|),
while |parse| is the ``monadified'' variation of |inv pr|, using a |Maybe| monad to represent partialty.
We will talk about how to construct |inv pr| and |parse| later.
% It returns |Nothing| for inputs not in the domain of |inv pr|.
% It may appear that it defeats the purpose if we assume that we can determine whether a input is in the domain of |inv pr|, but we will present a more precise definition later.

The result of |map parse| is passed to |filtJust :: [Maybe a] -> [a]|, which chooses only those elements wrapped by |Just|.
For this problem |filtJust| always returns a non-empty list, because the empty string can always be parsed to |Just Null|.
Given |f :: a -> b| where |b| is a type that is totally ordered, |maxBy f :: [a] -> a| picks a maximum element from the input.
%Finally, |size t| computes the length of |pr t|.
% Specification of the ``length only'' problem is simply |size . lbp|.


\paragraph*{An initial derivation.}
To derive an algorithm, we proceed by the usual routine.
Finding an optimal segment is often factored into finding, for each suffix, an optimal prefix:
\begin{spec}
   maxBy size . filtJust . map parse . segments
=    {- definition of |segments| -}
   maxBy size . filtJust . map parse . concat . map inits . tails
=    {- since |map f . concat = concat . map (map f)|, |map| fusion -}
   maxBy size . filtJust . concat . map (map parse . inits) . tails
=    {- since |filtJust . concat = concat . map filtJust| -}
   maxBy size . concat . map (filtJust . map parse . inits) . tails
=    {- since |maxBy f . concat = maxBy f . map (maxBy f)| -}
   maxBy size . map (maxBy size . filtJust . map parse . inits) . tails {-"~~."-}
\end{spec}
That is, for each suffix returned by |tails|, we attempt to compute the longest prefix of balanced parentheses (as in |maxBy size . filtJust . map parse . inits|).

The next step is usually to apply the ``scan lemma'':
|map (foldr oplus e) . tails = scanr oplus e|.
If we can turn |maxBy size . filtJust . map parse . inits| into a |foldr|,
the algorithm can proceed in a |scanr|. And if |oplus| is a constant-time operation, we get a linear-time algorithm.
Since |inits| is a |foldr| --- |inits = foldr (\x xss -> [] : map (x:) xss) [[]]|,
% \begin{spec}
%   inits = foldr (\x xss -> [] : map (x:) xss) [[]] {-"~~,"-}
% \end{spec}
a reasonable attempt is to use the fold-fusion theorem to fuse |maxBy size . filtJust . map parse| into |inits|, to form a single |foldr|:
\begin{theorem}[|foldr|-fusion]
  |h . foldr f e = foldr g (h e)| if |h (f x y) = g x (h y)|.
\end{theorem}
Trying to satsify the condition for fusing |map parse| and |inits|:
\begin{spec}
   map parse ([] : map (x:) xss)
=    {- since |parse [] = Just Null| -}
   Just Null : map (parse . (x:)) xss
=    {- wish, for some |g'| -}
   Just Null : g' x (map parse xss) {-"~~,"-}
\end{spec}
we wish |map (parse . (x:)) = g' x . map parse| for some |g'|.
For that, we need |parse (x : xs) = g'' x (parse xs)| for some |g''|,
that is, |parse| shall be a |foldr| too. Is that possible?

Since |parse| is defined in terms of |inv pr|,
it would be helpful if there is a method to construct the inverse of a function as a fold --- as presented in the next section.

% \paragraph*{Totalising right inverses}
% It is about time to be a bit more precise about |parse :: String -> Tree|.
% Given a string |xs| of balanced parentheses, |parse xs| should return a tree |t| such that |pr t = xs|.
% Therefore, |parse| appears to be related to the right inverse of |pr| ---
% that is, the function |inv pr| such that |pr (inv pr xs) = xs|.
% However, |inv pr| is a partial function --- there is no |t| such that |pr t = "((("|, for example.
% When given such an input, we do not want the entire computation to fail.
% Partial computations are typically modeled in Haskell by |Maybe| monad.
% For this problem, however, we use a light-weight approach.
% We let |parse| return |Null|, which prints to |""|, indeed the longest segment of |"((("| that can be parsed to a tree.
% Define the following ``totalising'' operator:
% \begin{spec}
% total :: (a -> Tree) -> a -> Tree
% total f x  = f x   {-"\quad\mbox{, } x \in \Varid{dom}~\Varid{f} "-}
%            = Null  {-"\quad\mbox{, otherwise.}"-}
% \end{spec}
% We let |parse = total (inv pr)|.
