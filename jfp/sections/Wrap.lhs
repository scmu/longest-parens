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
      maxBy size . map (fst . build) . tails
 ===  fst . maxBy (size . fst) . map build . tails
 ===    {- Lemma~\ref{lma:scan-lemma}, |build = foldr bstep (Null,[])| -}
      fst . maxBy (size . fst) . scanr bstep (Null,[]) {-"~~."-}
\end{code}
We have therefore derived:
\begin{code}
lbp :: String -> Tree
lbp = fst . maxBy (size . fst) . scanr bstep (Null,[]) {-"~~."-}
\end{code}
%if False
\begin{code}
   where  bstep ')' (t, ts)    = (Null, t:ts)
          bstep '(' (t, [])    = (Null,[])
          bstep '(' (t, u:ts)  = (Fork t u, ts) {-"~~."-}
\end{code}
%endif
To avoid recomputing the sizes each time, we can annotate each tree by its size: letting |Spine = ((Tree, Int), [(Tree, Int)])|, resulting in the an algorithm that runs in linear-time:
%{
%format lbp' = lbp
\begin{code}
lbp' = fst . fst . maxBy (snd . fst) . scanr bstep ((Null,0),[]) {-"~~,"-}
   where  bstep ')' (t,ts)  = ((Null,0),t:ts)
          bstep '(' (t,[])  = ((Null,0),[])
          bstep '(' ((t,m),(u,n):ts) = ((Fork t u, 2+m+n),ts) {-"~~."-}
\end{code}
%} %lbp'
Finally, the size-only version can be obtained by fusing |size| into |lbp|.
It turns out that we do not need to keep the actual tree, but only their sizes ---
|Spine = (Int, [Int])|:
\begin{code}
lbpl :: String -> Int
lbpl = fst . maxBy fst . scanr step (0,[]) {-"~~,"-}
   where  step ')' (t,ts) = (0,t:ts)
          step '(' (t,[]) = (0,[])
          step '(' (m,n:ts) = (2+m+n, ts) {-"~~."-}
\end{code}

\paragraph*{Acknowledgements}~
The problem was suggested by Yijia Chen.
The authors would like to thank our colleagues in IIS, Academia Sinica, in particular Hsiang-Shang `Josh' Ko, for valuable discussions.
