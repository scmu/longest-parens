%if False
\begin{code}
module Foldify where

import Data.List
import Control.Monad

import Intro
import Spine
import Utilities
\end{code}
%endif

\section{Longest Balanced Prefix in a Fold}
\label{sec:foldify}

Recall our objective: to compute
|lbp = maxBy size . filtJust . map parse . inits| in a right fold.
% posssibly by |foldr|-fusion.
Now that we have |parse = unwrapM <=< parseF| where |parseF| is a right fold, we calculate:
%if False
\begin{code}
optPreDer0 :: String -> Tree
optPreDer0 =
\end{code}
%endif
\begin{code}
      maxBy size . filtJust . map parse . inits
 ===    {- since |parse = unwrapM <=< parseF| -}
      maxBy size . filtJust . map (unwrapM <=< parseF) . inits
 ===    {- see below -}
      unwrap . maxBy (size . unwrap) . filtJust . map parseF . inits {-"~~."-}
\end{code}
%if False
\begin{code}
unwrap :: Spine -> Tree
unwrap [t] = t
unwrap _   = Nil
\end{code}
%endif
The last step is a routine calculation whose purpose is to factor the postprocessing |unwrapM| out of the main computation.
We introduce |unwrap :: [Tree] -> Tree|, defined by |unwrap [t] = t| and for all other input it returns |Null|, the smallest tree.

Recall that |inits = foldr (\x xss -> [] : map (x:) xss) [[]]|.
The aim now is to fuse |map parseF|, |filtJust|, and |maxBy (size . unwrap)| with |inits|.
By Theorem~\ref{thm:foldr-fusion}, to fuse |map parseF| with |inits|, we need to construct some |step| such that
|map parseF ([] : map (x:) xss) = step x (map parseF xss)|.
We calculate:
%if False
\begin{code}
fuseCondMapParseFInit :: Char -> [String] -> [Maybe [Tree]]
fuseCondMapParseFInit x xss =
\end{code}
%endif
\begin{code}
      map parseF ([] : map (x:) xss)
 ===  Just [Nil] : map (parseF . (x:)) xss
 ===   {- the |foldr| definition of |parseF| -}
      Just [Nil] : map (\ts -> parseF ts >>= stepM x) xss
 ===  Just [Nil] : map (>>= stepM x) (map parseF xss) {-"~~."-}
\end{code}
Therefore we have
%{
%format mapParseFInits = map "~" parseF . inits
\begin{code}
mapParseFInits :: String -> [Maybe [Tree]]
mapParseFInits =
   foldr (\x tss -> Just [Nil] : map (>>= stepM x) tss) [Just [Nil]] {-"~~."-}
\end{code}
%}
Next, we fuse |filtJust| with |map parseF . inits| by Theorem~\ref{thm:foldr-fusion}.
After some calculations, we get:
%{
%format filtJustMapParseFInits = filtJust . map "~" parseF . inits
\begin{code}
filtJustMapParseFInits :: String -> [[Tree]]
filtJustMapParseFInits = foldr (\x tss -> [Nil] : extend x tss) [[Nil]] {-"~~,"-}
    where  extend ')' tts = map (Nil :) tts
           extend '(' tts = [(Bin t u : ts) | (t : u : ts) <- tts] {-"~~."-}
\end{code}
%}
The program still maintains a collection of |[Tree]|, but all the |Nothing| entries are filtered away.
If the next character is |')'|, we append |Nil| to every list of trees.
If the next entry is |'('|, we choose those lists having at least two trees, and combine them ---
the list comprehension keeps only those elements that matches the pattern |(t : u : ts)| and throws away those do not.
In both cases we add |[Nil]|, which the empty string is parsed to, to the collection.

\begin{figure}[t]
{\small
\begin{center}
\begin{tabular}{lll}
|inits|    & |map parseF|         & |filtJust| \\
\hline
|""|       & |J [N]|              & |[N]| \\
|"("|      & |Nothing|            &  \\
|"()"|     & |J [B N N]|          & |[B N N]| \\
|"())"|    & |J [B N N,N]|        & |[B N N,N]| \\
|"())("|   & |Nothing|            &  \\
|"())()"|  & |J [B N N,F N N]|    & |[B N N,B N N]|\\
|"())()("| & |Nothing|            &
\end{tabular}
\end{center}
}%\small
\caption{Results of |parseF| and |filtJust| for prefixes of |"())()("|.}
\label{fig:FiltParseFExample}
\end{figure}

To think about how to deal with |unwrap . maxBy (size . unwrap)|, we consider an example.
Figure~\ref{fig:FiltParseFExample} shows the results of |map parseF| and |filtJust| for prefixes of |"())()("|,
where |Just|, |Nil|, and |Bin| are respectively abbreviated to |J|, |N|, and |B|.
The function |maxBy (size . unwrap)| chooses between |[N]| and |[B N N]|, the two complete parses, and returns |[B N N]|. However, notice that |B N N| is also the head of |[B N N,B N N]|, the head of the last result returned by |filtJust|. In general, the head of the last list returned will be the largest parse tree. That is, |unwrap . maxBy (size . unwrap)| can be replaced by |head . last|.


\begin{code}
build :: String -> [Tree]
build = foldr bstep [Nil] {-"~~,"-}
  where  bstep ')' ts        = Nil : ts
         bstep '(' [t]       = [Nil]
         bstep '(' (t:u:ts)  = Bin t u : ts {-"~~."-}
\end{code}
%if False
\begin{code}
bstep :: Char -> Spine -> Spine
bstep ')' ts        = Null:ts
bstep '(' [t]       = [Null]
bstep '(' (t:u:ts)  = Fork t u : ts {-"~~."-}
\end{code}
%endif
