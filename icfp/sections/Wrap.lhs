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

\section{Wrapping Up and Conclusions}
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
 ===    {- Section~\ref{sec:foldify}: lbp = head . foldr step [Nil] -}
      maxBy size . map (head . foldr step [Nil]) . tails
 ===    {- since |mapBy f . map g = g . maxBy (f . g)| -}
      head . maxBy (size . head) . map build . tails
 ===    {- Lemma~\ref{lma:scan-lemma}, |build = foldr bstep (Null,[])| -}
      head . maxBy (size . head) . scanr step [Nil] {-"~~."-}
\end{code}
We have therefore derived:
\begin{code}
lbs :: String -> Tree
lbs = head . maxBy (size . head) . scanr step [Nil] {-"~~."-}
\end{code}
%if False
\begin{code}
   where  step ')' ts         = Nil : ts
          step '(' [t]        = [Nil]
          step '(' (t:u:ts)   = Bin t u : ts {-"~~,"-}
\end{code}
%endif
where |step| is as defined in the end of Section~\ref{sec:foldify}.
To avoid recomputing the sizes each time, we can annotate each tree by its size: letting |Forest = [(Tree, Int)]|, resulting in an algorithm that runs in linear-time:
%{
%format lbp' = lbp
\begin{code}
lbs' = fst . head . maxBy (snd . head) . scanr bstep [(Nil,0)] {-"~~,"-}
   where  bstep ')' ts   = (Nil,0):ts
          bstep '(' [t]  = [(Nil,0)]
          bstep '(' ((t,m):(u,n):ts) = (Bin t u, 2+m+n):ts {-"~~."-}
\end{code}
%} %lbp'
Finally, the size-only version can be obtained by fusing |size| into |lbp|.
It turns out that we do not need to keep the actual tree, but only their sizes ---
|Forest = [Int]|:
\begin{code}
lbsl :: String -> Int
lbsl = head . maxBy head . scanr step [0] {-"~~,"-}
   where  step ')' ts   = 0:ts
          step '(' [t]  = [0]
          step '(' (m:n:ts) = 2+m+n : ts {-"~~."-}
\end{code}

\section{Conclusions and Discussions}
\label{sec:conclude}

So we have derived a solution to the problem.
We find it an interesting journey because it involves two techniques:
the usual approach for solving segment problems, and the converse-of-a-function theorem --- through which we derived an instance of shift-reduce parsing.
We hope the reader enjoyed this journey too.


\paragraph*{Acknowledgements}~
The problem was suggested by Yi-Chia Chen.
The authors would like to thank our colleagues in IIS, Academia Sinica, in particular Hsiang-Shang `Josh' Ko, Liang-Ting Chen, and Ting-Yan Lai, for valuable discussions.
Also thanks to Chung-Chieh Shan and Kim-Ee Yeoh for their advices on earlier drafts of this paper.
