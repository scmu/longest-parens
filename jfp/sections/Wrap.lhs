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

We can finally resume the main derivation in Section~\ref{sec:intro}:
%if False
\begin{code}
initDer1 :: String -> Tree
initDer1 =
\end{code}
%endif
\begin{code}
      maxBy size . map (maxBy size . filtJust . map parse . inits) . tails
 ===    {- Section~\ref{sec:foldify} -}
      maxBy size . map (head . build) . tails
 ===  head . maxBy (size . head) . map build . tails
 ===    {- Lemma~\ref{lma:scan-lemma}, |build = foldr bstep (Null,[])| -}
      head . maxBy (size . head) . scanr bstep [Null] {-"~~."-}
\end{code}
We have therefore derived:
\begin{code}
lbp :: String -> Tree
lbp = head . maxBy (size . head) . scanr bstep [Null] {-"~~."-}
\end{code}
%if False
\begin{code}
   where  bstep ')' ts         = Null : ts
          bstep '(' [t]        = [Null]
          bstep '(' (t:u:ts)   = Fork t u : ts {-"~~."-}
\end{code}
%endif
To avoid recomputing the sizes each time, we can annotate each tree by its size: letting |Spine = [(Tree, Int)]|, resulting in an algorithm that runs in linear-time:
%{
%format lbp' = lbp
\begin{code}
lbp' = fst . head . maxBy (snd . head) . scanr bstep [(Null,0)] {-"~~,"-}
   where  bstep ')' ts   = (Null,0):ts
          bstep '(' [t]  = [(Null,0)]
          bstep '(' ((t,m):(u,n):ts) = (Fork t u, 2+m+n):ts {-"~~."-}
\end{code}
%} %lbp'
Finally, the size-only version can be obtained by fusing |size| into |lbp|.
It turns out that we do not need to keep the actual tree, but only their sizes ---
|Spine = [Int]|:
\begin{code}
lbpl :: String -> Int
lbpl = head . maxBy head . scanr step [0] {-"~~,"-}
   where  step ')' ts   = 0:ts
          step '(' [t]  = [0]
          step '(' (m:n:ts) = 2+m+n : ts {-"~~."-}
\end{code}

So we have derived a solution to the problem.
We find it an interesting journey because it involves two techniques:
the usual approach for solving segment problems, and the converse-of-a-function theorem --- through which we derived an instance of shift-reduce parsing.
We hope the reader enjoyed this journey too.

\paragraph*{Acknowledgements}~
The problem was suggested by Yi-Chia Chen.
The authors would like to thank our colleagues in IIS, Academia Sinica, in particular Hsiang-Shang `Josh' Ko, Liang-Ting Chen, and Ting-Yan Lai, for valuable discussions.
Also thanks to Chung-Chieh Shan and Kim-Ee Yeoh for their advices on earlier drafts of this paper.
