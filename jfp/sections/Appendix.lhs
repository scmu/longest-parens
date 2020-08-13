%if False
\begin{code}
module Appendix where

import Data.List
import Control.Monad

import Intro
import Spine
import Foldify
import Utilities
\end{code}
%endif

\section{Appendix}
\label{sec:largest-build-gen}

Let |bsteps [y0,y1..yn] = bstep y0 . bstep y1 ... bstep yn|,
and |stepsM [y0,y1..yn] = stepM y0 <=< stepM y1 ... <=< stepM yn|.
\begin{equation}
\begin{split}
&  |fst ((largest . map build . inits) ys `oplus`| \\
& \qquad |(maxBy (size . unwrap) . filtJust . map (stepsM ys <=< parseS) . initsP) xs) ===|\\
& ~~|fst ((largest . map build . inits) ys `oplus`| \\
& ~~\qquad |(largest . map (bsteps ys . build) . initsP) xs)| ~~\mbox{~~.}
\end{split}
\label{eq:largest-build-gen}
\end{equation}

%if False
\begin{code}
largestBuildGen :: String -> String -> Tree
largestBuildGen ys xs =
  fst ((largest . map build . inits) ys `bl`
        (maxBy (size . unwrap) . filtJust . map (stepsM ys <=< parseS) . initsP) xs) ===
  fst ((largest . map build . inits) ys `bl`
        (largest . map (bsteps ys . build) . initsP) xs)
\end{code}
%endif

%if False
\begin{code}
bstep :: Char -> Spine -> Spine
bstep ')' (t,ts)    = (Null, t:ts)
bstep '(' (t,[])    = (Null,[])
bstep '(' (t,u:ts)  = (Fork t u, ts)

bsteps :: String -> Spine -> Spine
bsteps [] = id
bsteps (x:xs) = bstep x . bsteps xs

stepsM :: String -> Spine -> Maybe Spine
stepsM [] = return
stepsM (x:xs) = stepM x <=< stepsM xs

initsP :: [a] -> [[a]]
initsP = undefined
\end{code}
%endif
