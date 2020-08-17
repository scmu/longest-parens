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

\section{On Introducing |build|}
\label{sec:largest-build-gen}

Regarding proving \eqref{eq:largest-build-intro}.
We notice two properties:
\begin{enumerate}
\item |parseS xs| is either |Nothing|, or |Just (build xs)|,
\item if |parseS xs| is |Nothing|, |build xs = build xs'| for some proper
   prefix |xs'| of |xs|.
\end{enumerate}
Let |oplus :: Spine -> Spine -> Spine| be any binary operator that is associative, commutative, and idempotent, with identity |(Null,[])|, and let |choose = foldr oplus (Null,[])|.
The two properties above imply that for all |ys| and |x|:
\begin{equation}
\begin{split}
& |(choose . map build . inits) ys `bl` pickJust (parseS (ys++[x]))|~=\\
& \quad |(choose . map build . inits) ys `bl` build (ys++[x])| \mbox{~~.}
\end{split}
\label{eq:build-shadow}
\end{equation}
%if False
\begin{code}
buildInitsShadow :: String -> Char -> Spine
buildInitsShadow ys x =
 (choose . map build . inits) ys `bl` pickJust (parseS (ys++[x])) ===
  (choose . map build . inits) ys `bl` build (ys++[x])

pickJust :: Maybe Spine -> Spine
pickJust (Just t) = t
pickJust Nothing = (Null, [])

ml :: Spine -> Spine -> Spine
ml = undefined

choose = foldr ml (Null,[])
\end{code}
%endif
where |pickJust :: Maybe Spine -> Spine| extracts the spine if the input is wrapped by |Just|, otherwise returns |(Null,[])|.

Let |bsteps [y0,y1..yn] = bstep y0 . bstep y1 ... bstep yn|,
and |stepsM [y0,y1..yn] = stepM y0 <=< stepM y1 ... <=< stepM yn|.
The generalisation we can prove is:
\begin{equation}
\begin{split}
&  |(choose . map build . inits) ys {-"\,"-} `ml`| \\
& \qquad |(choose . filtJust . map (stepsM ys <=< parseS) . initsP) xs ===|\\
& ~~|(choose . map build . inits) ys {-"\,"-} `ml`| \\
& ~~\qquad |(choose . map (bsteps ys . build) . initsP) xs| ~~\mbox{~~,}
\end{split}
\label{eq:largest-build-gen}
\end{equation}
%if False
\begin{code}
largestBuildGen :: String -> String -> Tree
largestBuildGen ys xs =
  fst ((largest . map build . inits) ys `bl`
        (maxBy (size . unwrap) . filtJust . map (stepsM ys <=< parseS) . initsP) xs) ===
  fst ((largest . map build . inits) ys `bl` (largest . map (bsteps ys . build) . initsP) xs)
\end{code}
%endif
where |initsP| returns \emph{non-empty} prefixes of the input list.
When |ys := []|, \eqref{eq:largest-build-gen} reduces to
|choose . filtJust . map parseS . inits === choose . map build . inits|,
a generalisation of \eqref{eq:largest-build-intro}.

We show the inductive case:
%if False
\begin{code}
largestBuildGenInd ys x xs =
\end{code}
%endif
\begin{code}
      (choose . map build . inits) ys `bl`
        (choose . filtJust . map (stepsM ys <=< parseS) . initsP) (x:xs)
 ===  (choose . map build . inits) ys `bl` pickJust (parseS (ys ++ [x])) `bl`
        (choose . filtJust . map (stepsM ys <=< parseS) . initsP) xs
 ===    {- by \eqref{eq:build-shadow} -}
      (choose . map build . inits) ys `bl` build (ys ++ [x]) `bl`
        (choose . filtJust . map (stepsM ys <=< parseS) . initsP) xs
 ===    {- induction -}
      (choose . map build . inits) ys `bl` build (ys ++ [x]) `bl`
        (choose . map (bsteps ys . build) . initsP) xs
 ===  (choose . map build . inits) ys `bl` (choose . map (bsteps ys . build) . initsP) (x:xs) {-"~~."-}
\end{code}

%if False
\begin{code}
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
