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

\section{Optimal Prefix in a Fold}
\label{sec:foldify}

Recall our objective: to turn
|maxBy size . filtJust . map parse . inits| into a |foldr|.
% posssibly by |foldr|-fusion.
We calculate:
%if False
\begin{code}
optPreDer0 :: String -> Tree
optPreDer0 =
\end{code}
%endif
\begin{code}
      maxBy size . filtJust . map parse . inits
 ===    {- since |parse = unwrapM <=< parseS| -}
      maxBy size . filtJust . map (unwrapM <=< parseS) . inits
 ===    {- see below -}
      unwrap . maxBy (size . unwrap) . filtJust . map parseS . inits {-"~~."-}
\end{code}
%if False
\begin{code}
unwrap :: Spine -> Tree
unwrap [t] = t
unwrap _   = Null
\end{code}
%endif
The last step is a routine calculation whose purpose is to factor the postprocessing |unwarpM| out of the main computation.
We introduce |unwrap :: Spine -> Tree|, defined by |unwrap [t] = t| and for all other input it returns |Null|, the smallest tree.

% For reason to be clear later, however, we need two generalisations.
% Firstly, we compare spine trees by \emph{lexicographic ordering}, that is
% |(t,ts)| and |(u,us)| are compared first by comparing sizes of |t| and |u|.
% If |size t = size u|, we then compare the first trees in |ts| and |us|, and so on.
% An empty list is considered smaller than a non-empty list.
% We denote the binary operator that chooses a lexicographically larger spine by |bl :: Spine -> Spine -> Spine|, and define |largest = foldr bl (Null,[])|.

To compute the optimal spine tree in a |foldr|, we need two more generalisations.
Firstly, recall the definition of |parseS|.
In the |('(':xs)| case, when the recursive call returns |[t]|, we abort the computation by returning |Nothing|.
This means that the information computed so far is disposed of,
while if we wish to process all prefixes in a single |foldr|, it helps to maintain some accumulated results.
The following function |build| returns |[Null]| in this case, allowing the computation to carry on:
% \begin{spec}
% build :: String -> Spine
% build ""        = (Null,[])
% build (')':xs)  = case build xs of  (t,ts)      -> (Null, t:ts)
% build ('(':xs)  = case build xs of  (t,[])      -> (Null,[])
%                                     (t, u: ts)  -> (Fork t u, ts) {-"~~,"-}
% \end{spec}
\begin{code}
build :: String -> Spine
build = foldr bstep [Null] {-"~~,"-}
  where  bstep ')' ts        = Null:ts
         bstep '(' [t]       = [Null]
         bstep '(' (t:u:ts)  = Fork t u : ts {-"~~."-}
\end{code}
%if False
\begin{code}
bstep :: Char -> Spine -> Spine
bstep ')' ts        = Null:ts
bstep '(' [t]       = [Null]
bstep '(' (t:u:ts)  = Fork t u : ts {-"~~."-}
\end{code}
%endif
For example, while |parseS "))(" = Nothing|,
we have |build "))(" = [Null,Null,Null]| ---
the same result |build| and |parseS| would return for |"))"|.
In effect, while |parseS| is a partial function that attempts to parse an entire string, |build| is a total function that parses a prefix of the string.

\begin{figure}[t]
{\small
\begin{center}
\begin{tabular}{lll}
|inits|    & |parseS|           & |build| \\
\hline
|""|       & |J [N]|              & |[N]| \\
|"("|      & |Nothing|            & |[N]| \\
|"()"|     & |J [F N N]|          & |[F N N]| \\
|"())"|    & |J [F N N,N]|        & |[F N N,N]| \\
|"())("|   & |Nothing|            & |[F N N,N]| \\
|"())()"|  & |J [F N N,F N N]|    & |[F N N,F N N]|\\
|"())()("| & |Nothing|            & |[F N N,F N N]|
\end{tabular}
\end{center}
}%\small
\caption{Results of |parseS| and |build| for each prefix of |"())()("|.}
\label{fig:parseSvsBuild}
\end{figure}

We claim that the optimal prefix can be computed by |build|:
\begin{equation}
\begin{split}
  & |maxBy (size . unwrap) . filtJust . map parseS . inits|~=\\
  & \qquad |maxBy (size . unwrap) . map build . inits| \mbox{~~.}
\end{split}
\label{eq:largest-build-intro}
\end{equation}
%if False
\begin{code}
optPreProp0 :: String -> Spine
optPreProp0 =
  maxBy (size . unwrap) . filtJust . map parseS . inits ===
    maxBy (size . unwrap) . map build . inits

largest :: [Spine] -> Spine
largest = foldr bl [Null]

bl :: Spine -> Spine -> Spine
bl = undefined
\end{code}
%endif
An informal explanation is that using |build| instead of |parseS| does not generate anything new.
Figure~\ref{fig:parseSvsBuild} shows the results of |parseS| and |build| for each prefix of |"())()("|,
where |Just|, |Null|, and |Fork| are respectively abbreviated to |J|, |N|, and |F|.
We can see that there are three prefixes for which |parseS| returns |Nothing|, while |build| yields a spine.
All of these spines, however, are what |parseS| would return for some other prefix anyway.
% Using |fst . largest| instead of |maxBy (size . unwrap)| is safe too: if |(F N N,[F N N])| is chosen by lexicographic ordering, the spine |(F N N, [])| must be a result of some prefix, and either way the optimal tree is |F N N|.

Formally proving \eqref{eq:largest-build-intro}, however, is a tricky task.
It turns out that we need to prove a non-trivial generalisation of \eqref{eq:largest-build-intro}, recorded in Appendix~\ref{sec:largest-build-gen} for interested readers.

For the second generalisation, note that in |maxBy (size . unwrap)|,
two singleton spines |[t]| and |[u]| are compared by the sizes of |t| and |u|, while |t:ts| is treated the same as |Null|.
We generalise the process to picking a maximum using the ordering |unlhd|, defined below:
% \begin{spec}
%   []      `unlhd` us  {-"~~"-} &&
%   (t:ts)  `unlhd` (u:us) {-"~~"-}<=>{-"~~"-} size t <= size u {-"\,"-}&&{-"\,"-} ts `unlhd` us {-"~~."-}
% \end{spec}
\begin{align*}
  |[]| & |`unlhd` us  {-"~~"-} &&| \\
  |(t:ts)| & |`unlhd` (u:us) {-"~~"-}<=>{-"~~"-} size t <= size u {-"\,"-}&&{-"\,"-} ts `unlhd` us {-"~~."-}|
\end{align*}
% \begin{spec}
%   (t,ts) `unlhd` (u,us) {-"~~"-}<=> {-"~~"-} size t <= size u {-"\,"-}&&{-"\,"-} ts `preceq` us {-"~~,"-}
%     where  [] `preceq` us  {-"~~"-} &&
%            (t:ts) `preceq` (u:us) {-"~~"-}<=>{-"~~"-} size t <= size u {-"\,"-}&&{-"\,"-} ts `preceq` us {-"~~."-}
% \end{spec}
That is, |ts `unlhd` us| if |ts| is no longer than
|us|, and for every tree |t| in |ts|, we have |size t <= size u| where |u| is the tree in |us| in corresponding position.
The ``smallest'' spine under |unlhd| is |[Null]|.
In our context where we choose an optimal spine built from prefixes of the same list,
it is safe using |unlhd| because if a spine |t:ts| is the largest under |unlhd|, the spine |[t]| must be in the set of spines too and is optimal under the original order.

Furthermore, while |unlhd| is not a total ordering, |bstep| is monotonic with respect to |unlhd|: for all |vs, ws :: Spine| and |x = '('| or |')'|, we have
|vs `unlhd` ws  ==> bstep x vs `unlhd` bstep x ws|.
That means the list of spines returned by |map build . inits| is sorted in ascending order, with the largest spine in the end:
\begin{equation*}
   |build [] {-"~"-}`unlhd`{-"~"-} build [x0] {-"~"-}`unlhd`{-"~"-} build [x0,x1]{-"~"-}`unlhd`{-"~"-}... {-"~"-}`unlhd`{-"~"-} build [x0...xn] {-"~~."-}|
\end{equation*}

In summary, we have
%{
%if False
\begin{code}
mapParseBuild =
\end{code}
%endif
%format max_unlhd = "\Varid{max}_{\unlhd}"
\begin{code}
     unwrap . maxBy (size . unwrap) . filtJust . map parseS . inits
 ===  {- \eqref{eq:largest-build-intro} -}
     unwrap . maxBy (size . unwrap) . map build . inits
 ===  {- let |max_unlhd| denote choosing maximum by |unlhd| -}
     head . max_unlhd . map build . inits
 ===  {- discussion above -}
     head . last . map build . inits
 ===  {- free theorem of |last| and |last . inits = id| -}
     head . build {-"~~."-}
\end{code}
%if False
\begin{code}
 where max_unlhd :: [Spine] -> Spine
       max_unlhd = undefined
\end{code}
%endif
