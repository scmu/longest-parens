%if False
\begin{code}
{-# LANGUAGE StandaloneDeriving #-}
module Intro where

import Data.List
import Utilities
\end{code}
%endif

\section{Introduction}
\label{sec:intro}

Given a string of parentheses, the task is to find a longest consecutive segment that is balanced.
For example, for input |"))(()())())()("| the output should be |"(()())()"|.
We also consider a reduced version of the problem in which we return only the length of the segment.
While there is no direct application of this problem
\footnote{However, the length-only version was possibly used as an interview problem collected in, for example, \url{https://leetcode.com/problems/longest-valid-parentheses/}.},
the authors find it interesting because it involves two techniques:
the usual approach for solving segment problems, and program inversion --- through which we will discover an instance of shift-reduce parsing.

\paragraph{Specification} Balanced parentheses can be captured by a number of grammars, for example |S -> epsilon || (S) || SS|, or |S -> epsilon || (S)S|.
After trying some of them, the authors settled down on |S -> epsilon || (S)S| because it is unambiguous and the most concise.
Other grammars have worked too, however, albeit leading to lengthier algorithms.
The parse tree of the chosen grammar can be represented in Haskell as below,
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
For example, applying |pr| to the |Fork (Fork Null (Fork Null Null)) (Fork Null Null)| yields the string |"(()())()"|.

Function |pr| is injective but not surjective: it does not yield un-balanced strings.
Therefore its right inverse, that is, the function |inv pr| such that |pr (inv pr xs) = xs|, is partial;
its domain is the set of balanced parenthesis strings.
We implement it by a function that is made total by using the |Maybe| monad.
This function |parse :: String -> Maybe Tree| builds a parse tree  --- |parse xs| should return |Just t| such that |pr t = xs| if |xs| is balanced, and return |Nothing| otherwise. We will construct parse more formally in Section~\ref{sec:spine}.

The problem can then be specified by (|lbs| standing for ``longest balanced segment (of parentheses)''):
\begin{code}
lbs :: String -> Tree
lbs = maxBy size . filtJust . map parse . segments {-"~~,"-}

segments = concat . map inits . tails {-"~~,"-}
filtJust ts = [t | Just t <- ts] {-"~~,"-}
size t = length (pr t) {-"~~."-}
\end{code}
The function |segments :: [a] -> [[a]]| returns all segments of a list, with |inits, tails :: [a] -> [[a]]| respectively compute all prefixes and suffixes of their input lists.
% It returns |Nothing| for inputs not in the domain of |inv pr|.
% It may appear that it defeats the purpose if we assume that we can determine whether a input is in the domain of |inv pr|, but we will present a more precise definition later.
The result of |map parse| is passed to |filtJust :: [Maybe a] -> [a]|, which collects only those elements wrapped by |Just|.
\footnote{|filtJust| is called |catMaybes| in the standard Haskell libraries.}
For this problem |filtJust| always returns a non-empty list, because the empty string, which is a member of |segments xs| for any |xs|, can always be parsed to |Just Null|.
Given |f :: a -> b| where |b| is a type that is ordered, |maxBy f :: [a] -> a| picks a maximum element from the input.
Finally, |size t| computes the length of |pr t|.
% Specification of the ``length only'' problem is simply |size . lbp|.

The length-only problem can be specified by |lbsl = size . lbs|.

\section{An Initial Derivation}

It is known that many \emph{optimal segment} problems (those whose goal is to compute a segment of a list that is optimal up to certain criteria) can be solved by following a fixed pattern
\cite{Bird:87:Introduction, Gibbons:97:Calculating}.
In the first step, finding an optimal segment is factored into finding, for each suffix, an optimal prefix.
For our problem, the calculation goes:
%if False
\begin{code}
initDer0 :: String -> Tree
initDer0 =
\end{code}
%endif
\begin{code}
      maxBy size . filtJust . map parse . segments
 ===    {- definition of |segments| -}
      maxBy size . filtJust . map parse . concat . map inits . tails
 ===    {- since |map f . concat = concat . map (map f)|, |map| fusion -}
      maxBy size . filtJust . concat . map (map parse . inits) . tails
 ===    {- since |filtJust . concat = concat . map filtJust| -}
      maxBy size . concat . map (filtJust . map parse . inits) . tails
 ===    {- since |maxBy f . concat = maxBy f . map (maxBy f)| -}
      maxBy size . map (maxBy size . filtJust . map parse . inits) . tails {-"~~."-}
\end{code}
For each suffix returned by |tails|, the program above computes its longest \emph{prefix} of balanced parentheses by |maxBy size . filtJust . map parse . inits|. We abbreviate the latter to |lbp| (for ``longest balanced prefix'').

Calling |lbp| for each suffix is rather costly.
The next step is to try to apply the following ``scan lemma'',
which says that if a function |f| can be expressed as right fold,
there is a more efficient algorithm to compute |map f . inits|:
\begin{lemma}
\label{lma:scan-lemma}
{\rm
|map (foldr oplus e) . tails = scanr oplus e|, where
\begin{spec}
scanr oplus e []      = [e]
scanr oplus e (x:xs)  = let (y:ys) = scanr oplus e xs in (x `oplus` y) : y : ys {-"~~."-}
\end{spec}
} %rm
\end{lemma}
If |lbp| can be written in the form |foldr oplus e|, we do not need to compute |lbp| of each suffix from scratch;
each optimal prefix can be computed, in |scanr|, from the previous optimal prefix by |oplus|.
%the algorithm can proceed in a |scanr|.
If |oplus| is a constant-time operation, we get a linear-time algorithm.

The next challenge is therefore to express |lbp| as a right fold.
Since |inits| can be expressed as a right fold  --- |inits = foldr (\x xss -> [] : map (x:) xss) [[]]|,
% \begin{spec}
%   inits = foldr (\x xss -> [] : map (x:) xss) [[]] {-"~~,"-}
% \end{spec}
a reasonable attempt is to use the fold-fusion theorem to fuse |maxBy size . filtJust . map parse| with |inits|, to form a single |foldr|.
Recall the |foldr|-fusion theorem:
\begin{theorem}[|foldr|-fusion]
\label{thm:foldr-fusion}
{\rm
  |h . foldr f e = foldr g (h e)| if |h (f x y) = g x (h y)|.
} %rm
\end{theorem}
To fuse |map parse| and |inits|, we need to have
|map parse ([] : map (x:) xss) = Just Null : g' x (map parse xss)|
for some |g'|.
For that, we need |parse (x : xs) = g'' x (parse xs)| for some |g''|,
that is, |parse| needs to be a right fold too.
Is that possible?
% Trying to satsify the condition for fusing |map parse| and |inits|:
% %if False
% \begin{code}
% -- fuseCond0 :: String -> Tree
% fuseCond0 :: Char -> [String] -> [Maybe Tree]
% fuseCond0 x xss =
% \end{code}
% %endif
% \begin{code}
%       map parse ([] : map (x:) xss)
%  ===    {- since |parse [] = Just Null| -}
%       Just Null : map (parse . (x:)) xss
%  ===    {- wish, for some |g'| -}
%       Just Null : g' x (map parse xss) {-"~~,"-}
% \end{code}
% %if False
% \begin{code}
%   where g' :: Char -> [Maybe Tree] -> [Maybe Tree]
%         g' = undefined
% \end{code}
% %endif

Since |parse| implements |inv pr|,
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


%if False
\begin{code}
maxBy f [x] = x
maxBy f (x:y:xs) = maxBy f (mx x y : xs)
    where mx x y | f x >= f y = x
                 | otherwise  = y

parse :: String -> Maybe Tree
parse = undefined
\end{code}
%endif
