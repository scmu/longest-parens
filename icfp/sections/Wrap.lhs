%if False
\begin{code}
module Wrap where

import Data.List
import Control.Monad

import Intro
import Spine
import Foldify
import Utilities
\end{code}
%endif

\section{Wrapping Up}
\label{sec:wrap}

We can finally resume the main derivation in Section~\ref{sec:inits-tails}:
%if False
\begin{code}
initDer1 :: String -> Tree
initDer1 =
\end{code}
%endif
\begin{code}
      maxBy size . map (maxBy size . filtJust . map parse . inits) . tails
 ===    {- Section~\ref{sec:foldify}: |lbp = head . foldr step [Nul]| -}
      maxBy size . map (head . foldr step [Nul]) . tails
 ===    {- |map|-fusion reversed, Lemma~\ref{lma:scan-lemma} -}
      maxBy size . map head . scanr step [Nul] {-"~~."-}
\end{code}

We have therefore derived:
\begin{code}
lbs :: String -> Tree
lbs = maxBy size . map head . scanr step [Nul] {-"~~,"-}
\end{code}
%if False
\begin{code}
   where  step ')' ts         = Nul : ts
          step '(' [t]        = [Nul]
          step '(' (t:u:ts)   = Bin t u : ts {-"~~,"-}
\end{code}
%endif
where |step| is as defined in the end of Section~\ref{sec:foldify}.
To avoid recomputing the sizes in |maxBy size|, we can annotate each tree by its size: letting |Forest = [(Tree, Int)]|, resulting in an algorithm that runs in linear-time:
%{
%format lbs' = lbs
\begin{code}
lbs' :: String -> Tree
lbs' = fst . maxBy snd . map head . scanr step [(Nul,0)] {-"~~,"-}
   where  step ')' ts   = (Nul,0):ts
          step '(' [t]  = [(Nul,0)]
          step '(' ((t,m):(u,n):ts) = (Bin t u, 2+m+n):ts {-"~~."-}
\end{code}
%} %lbp'
Finally, the size-only version can be obtained by fusing |size| into |lbs|.
It turns out that we do not need to keep the actual tree, but only their sizes ---
|Forest = [Int]|:
\begin{code}
lbsl :: String -> Int
lbsl = maximum . map head . scanr step [0] {-"~~,"-}
   where  step ')' ts   = 0 : ts
          step '(' [t]  = [0]
          step '(' (m:n:ts) = (2+m+n) : ts {-"~~."-}
\end{code}

\section{Conclusions and Discussions}
\label{sec:conclude}

So we have derived a linear-time algorithm for solving the problem.
We find it an interesting journey because it relates two techniques:
prefix-suffix decomposition for solving segment problems, and the converse-of-a-function theorem for program inversion.

In Section~\ref{sec:spine} we generalised from trees to forests.
It is common when applying the converse-of-a-function theorem.
It was observed that the trees in a forest are those along the left spine of the final tree, therefore such a generalisation is referred to as switching to a ``spine representation'' \cite{MuBird:03:Theory}.

What we derived in Section~\ref{sec:spine} and \ref{sec:foldify} is a compacted form of shift-reduce parsing, where the input is processed right-to-left.
The forest serves as the stack, but we do not need to push the parser state to the stack, as is done in shift-reduce parsing.
If we were to process the input in the more conventional left-to-right order, the corresponding grammar would be |S -> epsilon || S(S)|.
It is an SLR(1) grammar whose parse table contains 5 states.
Our program is much simpler.
A possible reason is that consecutive shifting and reducing are condensed into one step.
It is likely that parsing SLR(1) grammars can be done in a fold.
The relationship between LR parsing and the converse-of-a-function theorem awaits further investigation.

\begin{acks}
  % The problem was suggested by Yi-Chia Chen.
  % The authors would like to thank our colleagues in IIS, Academia Sinica, in particular Hsiang-Shang `Josh' Ko, Liang-Ting Chen, and Ting-Yan Lai, for valuable discussions.
  % Also thanks to Chung-Chieh Shan and Kim-Ee Yeoh for their advices on earlier drafts of this paper.
Temporarily hidden for double-blinded review.
However, the authors would like to thank the reviewers of previous versions of this article, whose detailed and constructive criticisms helped a lot in improving this work.
\end{acks}
