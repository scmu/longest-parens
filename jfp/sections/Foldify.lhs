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

Recall that our objective is to turn
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
unwrap (t,[]) = t
unwrap _      = Null
\end{code}
%endif
The last step is a routine calculation whose purpose is to factor the postprocessing |unwarpM| out of the main computation.
We introduce |unwrap :: Spine -> Tree|, defined by |unwrap (t,[]) = t| and for all other input it returns |Null|, the smallest tree.

% For reason to be clear later, however, we need two generalisations.
% Firstly, we compare spine trees by \emph{lexicographic ordering}, that is
% |(t,ts)| and |(u,us)| are compared first by comparing sizes of |t| and |u|.
% If |size t = size u|, we then compare the first trees in |ts| and |us|, and so on.
% An empty list is considered smaller than a non-empty list.
% We denote the binary operator that chooses a lexicographically larger spine by |bl :: Spine -> Spine -> Spine|, and define |largest = foldr bl (Null,[])|.

To compute the optimal spine tree in a |foldr|, we need two more generalisations.
Firstly, recall the definition of |parseS|.
In the |('(':xs)| case, when the recursive call returns |(t,[])|, we abort the computation by returning |Nothing|.
This means that the information computed so far is disposed of,
while if we wish to process all prefixes in a single |foldr|, it helps to maintain some accumulated results.
The following function |build| returns |(Null, [])| in this case, allowing the computation to carry on:
% \begin{spec}
% build :: String -> Spine
% build ""        = (Null,[])
% build (')':xs)  = case build xs of  (t,ts)      -> (Null, t:ts)
% build ('(':xs)  = case build xs of  (t,[])      -> (Null,[])
%                                     (t, u: ts)  -> (Fork t u, ts) {-"~~,"-}
% \end{spec}
\begin{code}
build :: String -> Spine
build = foldr bstep (Null,[]) {-"~~,"-}
  where  bstep ')' (t,ts)    = (Null, t:ts)
         bstep '(' (t,[])    = (Null,[])
         bstep '(' (t,u:ts)  = (Fork t u, ts) {-"~~."-}
\end{code}
%if False
\begin{code}
bstep :: Char -> Spine -> Spine
bstep ')' (t,ts)    = (Null, t:ts)
bstep '(' (t,[])    = (Null,[])
bstep '(' (t,u:ts)  = (Fork t u, ts) {-"~~."-}
\end{code}
%endif
For example,
|parseS "))(" = Nothing|, while |build "))(" = (Null,[Null,Null])| ---
the same result |build| and |parseS| would return for |"))"|.

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
optPreProp0 :: String -> Tree
optPreProp0 =
  maxBy (size . unwrap) . filtJust . map parseS . inits ===
    maxBy (size . unwrap) . map build . inits

largest :: [Spine] -> Spine
largest = foldr bl (Null,[])

bl :: Spine -> Spine -> Spine
bl = undefined
\end{code}
%endif
An informal explanation is that using |build| instead of |parseS| does not generate anything new.
Figure~\ref{fig:parseSvsBuild} shows the results of |parseS| and |build| for each prefix of |"())()("|, where |Just|, |Null|, and |Fork| are respectively abbreviated to |J|, |N|, and |F|.
We can see that there are three prefixes for which |parseS| returns |Nothing|, while |build| yields a spine.
All of these spines, however, are what |parseS| would return for some other prefix anyway.
% Using |fst . largest| instead of |maxBy (size . unwrap)| is safe too: if |(F N N,[F N N])| is chosen by lexicographic ordering, the spine |(F N N, [])| must be a result of some prefix, and either way the optimal tree is |F N N|.
\begin{figure}[t]
{\small
\begin{center}
\begin{tabular}{lll}
|inits|    & |parseS|           & |build| \\
\hline
|""|       & |J (N,[])|           & |(N,[])| \\
|"("|      & |Nothing|            & |(N,[])| \\
|"()"|     & |J (F N N,[])|       & |(F N N,[])| \\
|"())"|    & |J (F N N,[N])|      & |(F N N,[N])| \\
|"())("|   & |Nothing|            & |(F N N,[N])| \\
|"())()"|  & |J (F N N,[F N N])|  & |(F N N,[F N N])|\\
|"())()("| & |Nothing|            & |(F N N,[F N N])|
\end{tabular}
\end{center}
}%\small
\caption{Results of |parseS| and |build| for each prefix of |"())()("|.}
\label{fig:parseSvsBuild}
\end{figure}

Formally proving \eqref{eq:largest-build-intro}, however, is a tricky task.
It turns out that we need to prove a non-trivial generalisation of \eqref{eq:largest-build-intro}, recorded in Appendix~\ref{sec:largest-build-gen}.

For the second generalisation, note that in |maxBy (size . unwrap)|,
two spine trees |(t,[])| and |(u,[])| are compared by the sizes of |t| and |u|, while |(t,u:ts)| is treated the same as |Null|.
We generalise the process to picking a maximum using the ordering |unlhd|, defined below:
\begin{spec}
  (t,ts) `unlhd` (u,us) {-"~~"-}<=> {-"~~"-} size t <= size u {-"\,"-}&&{-"\,"-} ts `preceq` us {-"~~,"-}
    where  [] `preceq` us  {-"~~"-} &&
           (t:ts) `preceq` (u:us) {-"~~"-}<=>{-"~~"-} size t <= size u {-"\,"-}&&{-"\,"-} ts `preceq` us {-"~~."-}
\end{spec}
That is, |(t,ts) `unlhd` (u,us)| if |size t <= size u|, |ts| is no longer than
|us|, and for every tree |t'| in |ts|, we have |size t' <= size u'| where |u'| is the tree in |us| in corresponding position.
The ``smallest'' spine under |unlhd| is |(Null,[])|.
While |unlhd| is not a total ordering, |bstep| is monotonic with respect to |unlhd|: for all |v, w :: Spine| and |x `elem` {'(',')'}|, we have
|v `unlhd` w  ==> bstep x v `unlhd` bstep x w|.
That means the list of spines returned by |map build . inits| is sorted in ascending order, with the largest spine in the end:
\begin{spec}
   build [] {-"\,"-}`unlhd`{-"\,"-} build [x0] {-"\,"-}`unlhd`{-"\,"-} build [x0,x1]{-"\,"-}`unlhd`{-"\,"-}... {-"\,"-}`unlhd`{-"\,"-} build [x0...xn] {-"~~."-}
\end{spec}

In summary, we have
%{
%format max_unlhd = "\Varid{max}_{\unlhd}"
\begin{spec}
  unwrap . maxBy (size . unwrap) . filtJust . map parseS . inits
=  {- \eqref{eq:largest-build-intro} -}
  unwrap . maxBy (size . unwrap) . map build . inits
=  {- let |max_unlhd| denote choosing maximum by |unlhd| -}
  fst . max_unlhd . map build . inits
=  {- discussion above -}
  fst . last . map build . inits
= fst . build {-"~~."-}
\end{spec}

% Now we are ready to fuse |largest . map build| into |inits| by Theorem~\ref{thm:foldr-fusion}.
% To prove the fusion condition we calculate:
% %if False
% \begin{code}
% fuseCond1 :: Char -> [String] -> Spine
% fuseCond1 x xss =
% \end{code}
% %endif
% \begin{code}
%       largest (map build ([] : map (x:) xss))
%  ===  (Null, []) `bl` largest (map (build . (x:)) xss)
%  ===    {- |(Null, []) `bl` t = t|, and |build| is a |foldr| -}
%       largest (map (bstep x . build) xss)
%  ===    {- monotonicity: |largest . map bstep x = bstep x . largest| -}
%       bstep x (largest (map build xss)) {-"~~."-}
% \end{code}
% It is for the last step that we generalised to lexicographical ordering.
% The monotonicity would not hold if we had compared only the first tree.
