%if False
\begin{code}
module Wrap where

import Data.List
import Control.Monad

import Intro
import Spine
import Utilities
\end{code}
%endif

\section{Wrapping Up}
\label{sec:wrap}

\begin{code}
lbp :: String -> Tree
lbp = fst . maxBy sizeS . scanr bstep (Null,[])
   where  bstep ')' (t, ts)    = (Null, t:ts)
          bstep '(' (t, [])    = (Null,[])
          bstep '(' (t, u:ts)  = (Fork t u, ts)
\end{code}


\begin{code}
lvp2 :: String -> (Tree, Int)
lvp2 = fst . maxBy sizeS2 . scanr step ((Null,0),[])
   where  step ')' (t,ts)  = ((Null,0),t:ts)
          step '(' (t,[])  = ((Null,0),[])
          step '(' ((t,m),(u,n):ts) = ((Fork t u, 2+m+n),ts)
\end{code}

\begin{code}
lvp3 :: String -> Int
lvp3 = fst . maxBy sizeS3 . scanr step (0,[])
   where  step ')' (t,ts) = (0,t:ts)
          step '(' (t,[]) = (0,[])
          step '(' (m,n:ts) = (2+m+n, ts)
\end{code}
