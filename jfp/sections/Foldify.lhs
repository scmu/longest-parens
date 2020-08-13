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
\label{sec:longest}

Recall that our objective is to turn
|maxBy size . filtJust . map parse . inits| into a |foldr|, posssibly by |foldr|-fusion.
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
After the transformation above, |maxBy| chooses an maximum element by |size . unwrap|.
That is, two spine trees |(t,[])| and |(u,[])| are compared by the sizes of |t| and |u|, while |(t,u:ts)| is treated the same as |Null|.

% In the second expression, for each prefix of the input we try to build a spine tree by |praseS|; |unwrapM| then chooses only those having the form |(t,[])|.
% In the last step,
% This step can be justified by routine calculation.
% The rationale for doing this transformation is to to delay a destructive operation (removing non-singleton spines), keeping more information in the early stage of computation, to make |foldr|-fusion possible.

For reason to be clear later, however, we need two generalisations.
Firstly, we compare spine trees by \emph{lexicographic order}, that is
|(t,ts)| and |(u,us)| are compared first by comparing sizes of |t| and |u|.
If |size t = size u|, we then compare the first trees in |ts| and |us|, and so on.
An empty list is considered smaller than a non-empty list.
We denote the binary operator that chooses a lexicographically larger spine by |oplus :: Spine -> Spine -> Spine|, and define |largest = foldr oplus (Null,[])|.

On the second generalisation, recall the definition of |parseS|.
In the |('(':xs)| case, when the recursive call returns |(t,[])|, we abort the computation by returning |Nothing|.
This means that the information computed so far is disposed of, which is not good if we wish to
process all prefixes in a single |foldr|.
The following function |build| returns |(Null, [])| in this case, allowing the computation to reset and carry on:
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
For example,
|parseS "))(" = Nothing|, while |build "))(" = (Null,[Null,Null])| ---
the same result |build| and |parseS| would return for |"))"|.

We claim that the optimal prefix can be computed by |largest| and |build|:
\begin{equation}
\begin{split}
  & |unwrap . maxBy (size . unwrap) . filtJust . map parseS . inits|~=\\
  & \qquad |fst . largest . map build . inits| \mbox{~~.}
\end{split}
\label{eq:largest-build-intro}
\end{equation}
%if False
\begin{code}
optPreProp0 :: String -> Tree
optPreProp0 =
  unwrap . maxBy (size . unwrap) . filtJust . map parseS . inits ===
    fst . largest . map build . inits

largest :: [Spine] -> Spine
largest = undefined

bl :: Spine -> Spine -> Spine
bl = undefined
\end{code}
%endif
%format bl = "(\oplus)"
%format `bl` = "\oplus"

An informal explanation is that using |build| instead of |parseS| does not adding anything new to the collection of spine trees.
Figure~\ref{fig:parseSvsBuild} shows the results of |parseS| and |build| for each prefix of |"())()("|, where |Just|, |Null|, and |Fork| are respectively abbreviated to |J|, |N|, and |F|.
We can see that there are three cases where |parseS| returns |Nothing| while |build| yields a value. All of them, however, are values |parseS| would return for other prefixes anyway.
Using |fst . largest| is safe too: if |(F N N,[F N N])| is chosen by lexicographic ordering, the spine |(F N N, [])| must be a result of some prefix. Either way the optimal tree is |F N N|.
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
It turns out that we need to prove a generalisation, recorded in Appendix~\ref{sec:largest-build-gen}.

Now we are ready to fuse |largest . map build| into |inits|.
\begin{code}
      largest . map build $ ([] : map (x:) xss)
 ===  (Null, []) `bl` largest (map (build . (x:)) xss)
 ===    {- |build| is a |foldr| -}
      largest (map (bstep x . build) xss)
 ===    {- monotonicity: |largest . map bstep x = bstep x . largest| -}
      bstep x (largest (map build xss)) {-"~~."-}
\end{code}

We therefore conclude that
|largest . map build . inits = foldr bstep (Null, [])|.
