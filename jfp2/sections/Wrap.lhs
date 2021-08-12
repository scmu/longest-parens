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
It turns out that we do not need to keep the actual trees, but only their sizes ---
|Forest = [Int]|:
\begin{code}
lbsl :: String -> Int
lbsl = maximum . map head . scanr step [0] {-"~~,"-}
\end{code}
\begin{code}
{-"\qquad"-}where  step ')' ts   = 0 : ts
                   step '(' [t]  = [0]
                   step '(' (m:n:ts) = (2+m+n) : ts {-"~~."-}
\end{code}

\begin{figure}
\begin{center}
\begin{tabular}{||r||rrrrrr||}
\hline
input size (M)      & 1 & 2 & 4 & 6 & 8 & 10 \\
\hline
user time (sec.)
& 0.52
& 1.25
& 2.38
& 3.20
& 4.74
& 5.50\\
\hline
\end{tabular}
\end{center}
\caption{Measured running time for some input sizes.}
\label{fig:experiments}
\end{figure}

We ran some simple experiments to measure the efficiency of the algorithm.
The test machine was a laptop computer with a Apple M1 chip (8 core, 3.2GHz) and 16GB RAM.
We ran |lbs| on randomly generated inputs containing 1, 2, 4, 6, 8, and 10 million  parentheses, and measured the user times.
The results, shown in Figure~\ref{fig:experiments}, confirmed the linear-time behaviour.

\section{Conclusions and Discussions}
\label{sec:conclude}

So we have derived a linear-time algorithm for solving the problem.
We find it an interesting journey because it relates two techniques:
prefix-suffix decomposition for solving segment problems, and the converse-of-a-function theorem for program inversion.

In Section~\ref{sec:spine} we generalised from trees to forests.
It is common when applying the converse-of-a-function theorem.
It was observed that the trees in a forest are those along the left spine of the final tree, therefore such a generalisation is referred to as switching to a ``spine representation'' \citep{MuBird:03:Theory}.

What we derived in Section~\ref{sec:spine} and \ref{sec:foldify} is a compacted form of shift-reduce parsing, where the input is processed right-to-left.
The forest serves as the stack, but we do not need to push the parser state to the stack, as is done in shift-reduce parsing.
If we were to process the input in the more conventional left-to-right order, the corresponding grammar would be |S -> epsilon || S(S)|.
It is an SLR(1) grammar whose parse table contains 5 states.
Our program is much simpler.
A possible reason is that consecutive shifting and reducing are condensed into one step.
It is likely that parsing SLR(1) grammars can be done in a fold.
The relationship between LR parsing and the converse-of-a-function theorem awaits further investigation.

There are certainly other ways to solve the problem.
For example, one may interpret a |'('| as a $-1$, and a |')'| as a $+1$.
A left-partially balanced string would be a list whose right-to-left running sum is never negative.
One may then apply the method in \cite{Zantema:92:Longest} to find the longest such prefix for each suffixes.
The result will be an algorihm that maintains the sum in a loop --- an approach that might be more common among programmers.
% We are happy to have found an alternative algorithm.
The problem can also be seen as an instance of \emph{maximum-marking problems} --- choosing elements in a data structure that meet a given criteria while maximising a cost function --- to which methods of \cite{SasanoHu:01:Generation} can be applied.

\paragraph*{Acknowledgements}~
The problem was suggested by Yi-Chia Chen.
The authors would like to thank our colleagues in the PLFM group in IIS, Academia Sinica, in particular Hsiang-Shang `Josh' Ko, Liang-Ting Chen, and Ting-Yan Lai, for valuable discussions.
Also thanks to Chung-Chieh Shan and Kim-Ee Yeoh for their advices on earlier drafts of this paper.
We are grateful to the reviewers of previous versions of this article, who gave detailed and constructive criticisms that helped a lot in improving this work.

\paragraph*{Conflicts of interest}~ None.
