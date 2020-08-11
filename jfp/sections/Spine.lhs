%if False
\begin{code}
module Spine where

import Intro
import Utilities
\end{code}
%endif

\section{The Spine Tree}

Consider the tree in Figure~\ref{fig:spine01}. Adding a subtree |s| to its left results in the tree in Figure~\ref{fig:spine02}.
If we represent a tree by the leftmost subtree and the list of subtrees alone its left spine, the tree in Figure~\ref{fig:spine01} is represented by |(t,[u,v,w])|,
and adding a subtree is simply extending the list --- the tree in Figure~\ref{fig:spine02} is represented by |(s,[t,u,v,w])|.
Define the following \emph{spine tree}, a representation that allows us to easily extend trees to the lefthand side:
\begin{code}
type Spine = (Tree,[Tree]) {-"~~,"-}
\end{code}
The following function rolls a spine tree back to an ordinary tree:
\begin{code}
roll :: Spine -> Tree
roll (t,[])    = t
roll (t,u:ts)  = roll (Fork t u, ts) {-"~~."-}
\end{code}
For example, |roll (t,[u,v,w]) = Fork (Fork (Fork t u) v) w|.
Note that the tree in Figure~\ref{fig:spine01} can also be represented by |(Fork t u,[v,w])| --- both roll back to the same tree.
When it is represented this way, a newly added subtree becomes the sibling of |Fork t u|, rather than |t|.

\begin{figure}[t]
  \begin{subfigure}{.5\textwidth}
    \centering
     \includegraphics[scale=0.2]{pics/spine01.pdf}
     \caption{A spine tree represented by |(t,[u,v,w])|.}
     \label{fig:spine01}
  \end{subfigure}
  \begin{subfigure}{.5\textwidth}
    \centering
    \includegraphics[scale=0.2]{pics/spine02.pdf}
    \caption{Adding a subtree |s| to the tree in Figure \ref{fig:spine01}.}
    \label{fig:spine02}
  \end{subfigure}
\caption{Spine trees.}
\label{fig:spine}
\end{figure}

How do we print a spine tree?
Observe that the tree in Figure~\ref{fig:spine01} shall be printed as
|"(((t)u)v)w"|
(where {\tt t} and {\tt u}, etc in typewriter font denote |pr t| and |pr u|).
%|"(((" ++ pr t ++ ")" ++ pr u ++ ")" ++ pr v ++ ")" ++ pr w|.
For general cases, we claim that the following lemma is true:
\begin{lemma} For all |ts :: Spine|, we have
%if False
\begin{code}
propPrRoll :: Tree -> [Tree] -> String
propPrRoll t ts =
\end{code}
%endif
\begin{code}
 pr (roll (t,ts)) ===  replicate (length ts) '(' ++ pr t ++
                         foldr (\u xs -> ")" ++ pr u ++ xs) "" ts {-"~~,"-}
\end{code}
where |replicate n x| returns a list containing |n| copies of |x|.
\end{lemma}%
The proof is a routine induction on the length of |ts|.
Define
\begin{code}
prS :: Spine -> String
prS (t,ts) = pr t ++ foldr (\u xs -> ")" ++ pr u ++ xs) "" ts{-"~~."-}
\end{code}
That is, |prS s| is |pr (roll s)| without the leading left parentheses.
When a spine tree contains merely a singleton tree, |prS (t,[])| equals |pr t|, which is a string of balanced parentheses.
A spine tree |(t,[u,v])| is printed as |"t)u)v"|,
having two unmatched right parentheses, because we anticipate more trees to be added from the lefthand side.

We now try to construct an inductive definition of |prS| that does not use |(++)| and does not rely on |pr|.
For a base case, |prS (Null,[]) = ""|.
When the spine contains more than one tree, we calculate:
%if False
\begin{code}
prSIndDer0 :: Tree -> [Tree] -> String
prSIndDer0 t ts =
\end{code}
%endif
\begin{code}
      prS (Null, t:ts)
 ===     {- definition of |prS| -}
      pr Null ++ ")" ++ pr t ++ foldr (\u xs -> ")" ++ pr u ++ xs) "" ts
 ===  ')' : prS (t,ts) {-"~~."-}
\end{code}
When the first tree has the form |Fork t u|:
%if False
\begin{code}
prSIndDer1 :: Tree -> Tree -> [Tree] -> String
prSIndDer1 t u ts =
\end{code}
%endif
\begin{code}
      prS (Fork t u, ts)
 ===    {- definitions of |pr| and |prS| -}
      "(" ++ pr t ++ ")" ++ pr u ++ foldr (\u xs -> ")" ++ pr u ++ xs) "" ts
 ===    {- definition of |prS| -}
      '(' : prS (t, u : ts) {-"~~."-}
\end{code}
% --   pr (Fork t u) ++ foldr (\u xs -> ")" ++ pr u ++ xs) "" ts
% -- =   {- definition of |pr| -}
% The case when the spine is a singleton |[Fork t u]| turns out to be absorbed by the case above.
We have thus derived the following definition of |prS|:
%{
%format prS' = prS
\begin{code}
prS' (Null, [])      = ""
prS' (Null, t:ts)    = ')' : prS' (t, ts)
prS' (Fork t u, ts)  = '(' : prS' (t, u : ts) {-"~~."-}
\end{code}
%}
We are now ready to invert |prS| by Theorem~\ref{thm:conv-fun},
which amounts to finding |base| and |step| such that |prS base = ""| and |prS (step x ts) = x : prS ts| for |x = '('| or |')'|.
Now that |prS| has been transformed into the form above, we pick |base = (Null,[])|, and |step| is given by:
\begin{spec}
step ')' (t, ts)      = (Null, t:ts)
step '(' (t, u : ts)  = (Fork t u, ts) {-"~~."-}
\end{spec}
We have thus constructed |inv prS = foldr step (Null,[])|,
that is,
%format prSi = "{\Varid{prS}}^{\hstretch{0.5}{-}1}"
\begin{code}
prSi ""        = (Null, [])
prSi (')':xs)  = case prSi xs of (t, ts)      -> (Null, t:ts)
prSi ('(':xs)  = case prSi xs of (t, u : ts)  -> (Fork t u, ts) {-"~~,"-}
\end{code}
which is pleasingly symmetrical to |prS|.
For some intuition how the tree construction works,
when we see a |')'| we start a new tree, thus we shift |t| to the right and start freshly with |Null|;
when we see a |'('|, it ought to be the leftmost symbol of some |"(t)u"|,
thus we wrap the two most recent siblings into one tree.
When there are no such two siblings (that is, |inv prS xs = (t,[])|), the construction fails.
% In other words, we have derived:
% %{
% %format invprS = "{" prS "}^{\hstretch{0.5}{-}1}"
% \begin{spec}
% invprS :: String -> Spine
% invprS "" = [Null]
% invprS (')':xs) = Null : invprS xs
% invprS ('(':xs) = case invprS xs of (t : u : ts) -> Fork t u : ts {-"~~,"-}
% \end{spec}
% We have that |prS (invprS ts) = ts| for all |ts| in the domain of |invprS|.
% %}

Let |parseS| be the monadified version of |inv prS|, given by:
\begin{code}
parseS :: String -> Maybe Spine
parseS ""      = Just (Null,[])
parseS (x:xs)  = parseS xs >>= stepM x {-"~~,"-}
  where  stepM ')' (t, ts)      = Just (Null, t:ts)
         stepM '(' (t, [])      = Nothing
         stepM '(' (t, u : ts)  = Just (Fork t u, ts) {-"~~,"-}
\end{code}
where |stepM| is monadified |step| --- the case |(t,[])| missing in |step| is extended to returning |Nothing|.
Note that another way to write the inductive case is
|parseS (x:xs) = (stepM x <=< parseS) xs|, where |(<=<) :: (b -> M c) -> (a -> M b) -> (a -> M c)| is Kleisli composition, an operator we will use later.
