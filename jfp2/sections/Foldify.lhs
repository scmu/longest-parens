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

Recall our objective at the close of Section \ref{sec:inits-tails}:
to compute
|lbp = maxBy size . filtJust . map parse . inits| in a right fold,
such that we can get a faster algorithm using the scan lemma.
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
 ===    {- |maxBy f . map g = g . maxBy (f.g)| and other properties, see below -}
      unwrap . maxBy (size . unwrap) . filtJust . map parseF . inits {-"~~."-}
\end{code}
%if False
\begin{code}
unwrap :: Forest -> Tree
unwrap [t] = t
unwrap _   = Nul
\end{code}
%endif
The last step is a routine calculation whose purpose is to factor the postprocessing |unwrapM| out of the main computation.
We introduce |unwrap :: Forest -> Tree|, defined by |unwrap [t] = t| and for all other input it returns |Nul|, the smallest tree.

Recall that |inits = foldr (\x xss -> [] : map (x:) xss) [[]]|.
The aim now is to fuse |map parseF|, |filtJust|, and |maxBy (size . unwrap)| with |inits|.

By Theorem~\ref{thm:foldr-fusion}, to fuse |map parseF| with |inits|, we need to construct |g| that meets the fusion condition:
\begin{spec}
 map parseF ([] : map (x:) xss) = g x (map parseF xss) {-"~~."-}
\end{spec}
Now that we know that |parseF| is a fold, the calculation goes:
%if False
\begin{code}
fuseCondMapParseFInit :: Char -> [String] -> [Maybe Forest]
fuseCondMapParseFInit x xss =
\end{code}
%endif
\begin{code}
      map parseF ([] : map (x:) xss)
 ===  Just [Nul] : map (parseF . (x:)) xss
 ===   {- the |foldr| definition of |parseF| -}
      Just [Nul] : map (\ts -> parseF ts >>= stepM x) xss
 ===  Just [Nul] : map (>>= stepM x) (map parseF xss) {-"~~."-}
\end{code}
Therefore we have
%{
%format mapParseFInits = map "~" parseF . inits
\begin{code}
mapParseFInits :: String -> [Maybe Forest]
mapParseFInits =
   foldr (\x tss -> Just [Nul] : map (>>= stepM x) tss) [Just [Nul]] {-"~~."-}
\end{code}
%}

Next, we fuse |filtJust| with |map parseF . inits| by Theorem~\ref{thm:foldr-fusion}.
After some calculations, we get:
%{
%format filtJustMapParseFInits = filtJust . map "~" parseF . inits
\begin{code}
filtJustMapParseFInits :: String -> [Forest]
filtJustMapParseFInits = foldr (\x tss -> [Nul] : extend x tss) [[Nul]] {-"~~,"-}
    where  extend ')' tts = map (Nul :) tts
           extend '(' tts = [(Bin t u : ts) | (t : u : ts) <- tts] {-"~~."-}
\end{code}
%}
After the fusion we need not keep the |Nothing| entries in the fold;
the computation returns a collection of forests.
If the next character is |')'|, we append |Nul| to every forest.
If the next entry is |'('|, we choose those forests having at least two trees, and combine them ---
the list comprehension keeps only those forests that matches the pattern |(t : u : ts)| and throws away those do not.
Note that |[Nul]|, to which the empty string is parsed, is always added to the collection of forests.

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
|"())()"|  & |J [B N N,B N N]|    & |[B N N,B N N]|\\
|"())()("| & |Nothing|            &
\end{tabular}
\end{center}
}%\small
\caption{Results of |parseF| and |filtJust| for prefixes of |"())()("|.}
\label{fig:FiltParseFExample}
\end{figure}

To think about how to deal with |unwrap . maxBy (size . unwrap)|, we consider an example.
Figure~\ref{fig:FiltParseFExample} shows the results of |map parseF| and |filtJust| for prefixes of |"())()("|,
where |Just|, |Nul|, and |Bin| are respectively abbreviated to |J|, |N|, and |B|.
The function |maxBy (size . unwrap)| chooses between |[N]| and |[B N N]|, the two parses resulting in single trees, and returns |[B N N]|.
However, notice that |B N N| is also the head of |[B N N,B N N]|, the last forest returned by |filtJust|.
In general, the largest singleton parse tree will also present in the the head of the last forest returned by |filtJust . map parseF . inits|.
One can intuitively see why: if we print them both, the former is a prefix of the latter.
Therefore, |unwrap . maxBy (size . unwrap)| can be replaced by |head . last|.

To fuse |last| with |filtJust . map parseF . inits| by Theorem~\ref{thm:foldr-fusion}, we need to construct a function |step| that satisfies the fusion condition
\begin{spec}
 last ([Nul] : extend x tss) = step x (last tss) {-"~~,"-}
\end{spec}
where |tss| is a non-empty list of forests.
The case when |x = ')'| is easy --- choosing |step ')' ts = Nul : ts| will do the job.
For the case when |x = '('| we need to analyse the result of |last tss|,
and use the property that forests in |tss| are ordered in ascending lengths.
\begin{compactenum}
\item If |last tss = [t]|, a forest having only one tree, there are no forests in |tss| that contains two or more trees. Therefore |extend '(' tss| returns an empty list, and |last ([Nul] : extend '(' tss) = [Nul]|.
\item Otherwise, |extend '(' tss| would not be empty, and |last ([Nul] : extend x tss) = last (extend x tss)|. We may then combine the first two trees, as |extend| would do.
\end{compactenum}
In summary, we have
%{
%format build = last . filtJust . map "~" parseF . inits
\begin{code}
build :: String -> Forest
build = foldr step [Nul] {-"~~,"-}
  where  step ')' ts        = Nul : ts
         step '(' [t]       = [Nul]
         step '(' (t:u:ts)  = Bin t u : ts {-"~~,"-}
\end{code}
%}
%if False
\begin{code}
step :: Char -> Forest -> Forest
step ')' ts        = Nul:ts
step '(' [t]       = [Nul]
step '(' (t:u:ts)  = Bin t u : ts {-"~~."-}
\end{code}
%endif
which is now a total function on strings of parentheses.

The function derived above turns out to be |inv prF| with one additional case (|step '(' [t] = [Nul]|). What we have done in section can be seen as justifying adding that case (which is a result of case (1) in the fusion of |last|), which is not as trivial as one might think.
