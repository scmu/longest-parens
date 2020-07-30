%if False
\begin{code}
module Spine where

import Intro
\end{code}
%endif

\section{The Spine Tree}

To find the right inverse of |pr| using Theorem~\ref{thm:conv-fun}, we have to find |step :: Char -> Tree -> Tree| such that
|pr (step x t) = x : pr t|, where |x| is either |'('| or |')'|.
One can see that there is no way this equality could hold: |pr| always returns strings containing balanced parentheses,
but the strings returned by the two calls to |pr| in the equation cannot be both balanced.
This is a hint that we should generalise the problem to consider trees that are partially built, which would be printed to strings of parentheses that are not necessarily balanced.

Consider the tree in Figure~\ref{fig:spine01}. Adding a subtree |s| to its left results in the tree in Figure~\ref{fig:spine02}.
If we represent a tree by the leftmost subtree and the list of subtrees alone its left spine, the tree in Figure~\ref{fig:spine01} is represented by the list |[t,u,v,w]|,
and adding a subtree is simply extending the list --- the tree in Figure~\ref{fig:spine02} is represented by |[s,t,u,v,w]|.
Define the following \emph{spine tree}, a representation that allows us to easily extend trees to the lefthand side:
\begin{code}
type Spine = ListP Tree {-"~~,"-}
\end{code}
where |ListP _| denotes non-empty lists.
The following function rolls a spine tree back to an ordinary tree.
\begin{code}
roll :: Spine -> Tree
roll [t]       = t
roll (t:u:ts)  = roll (Fork t u : ts) {-"~~."-}
\end{code}
For example, |roll [t,u,v,w] = Fork (Fork (Fork t u) v) w|.
Note that the tree in Figure~\ref{fig:spine01} can also be represented by |[Fork t u,v,w]| --- both roll back to the same tree.
When it is represented this way, a newly added subtree becomes the sibling of |Fork t u|, rather than |t|.

\begin{figure}[t]
  \begin{subfigure}{.5\textwidth}
    \centering
     \includegraphics[scale=0.2]{pics/spine01.pdf}
     \caption{A spine tree represented by |[t,u,v,w]|.}
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
|"(((" ++ pr t ++ ")" ++ pr u ++ ")" ++ pr v ++ ")" ++ pr w|.
For the general case, we claim that the following lemma is true:
\begin{lemma} For all |ts :: Spine|, we have
\begin{spec}
pr (roll ts) =  replicate (length ts - 1) '(' ++
                  foldrn (\t xs -> pr t ++ ")" ++ xs) pr ts {-"~~,"-}
\end{spec}
where |replicate n x| returns a list containing |n| copies of |x|.
\end{lemma}%
The proof is a routine induction on the length of |ts|.
Define
\begin{code}
prS :: Spine -> String
prS = foldrn (\t xs -> pr t ++ ")" ++ xs) pr {-"~~."-}
\end{code}
That is, |prS ts| is |pr (roll ts)| without the leading left parentheses.
When a spine tree contains merely a singleton tree, |prS [t]| equals |pr t|, which is a string of balanced parentheses.
A spine tree |[t,u,v]| is printed as |pr t ++ ")" ++ pr u ++ ")" ++ pr v|, having two unmatched right parentheses, because we anticipate that more trees could be added.

We now try to construct an inductive definition of |prS| that does not use |(++)| and does not rely on |pr|.
For the base case, |prS [Null] = ""|.
When the spine contains more than one tree and the first tree is |Null|, we calculate:
\begin{spec}
  prS (Null : ts)
=  {- definition of |prS| -}
  pr Null ++ ")" ++ prS ts
= ')' : prS ts {-"~~."-}
\end{spec}
When the first tree has the form |Fork t u|:
\begin{spec}
  prS (Fork t u : ts)
=   {- definition of |prS| -}
  pr (Fork t u) ++ ")" ++ prS ts
=   {- definition of |pr| -}
  "(" ++ pr t ++ ")" ++ pr u ++ ")" ++ prS ts
=    {- definition of |prS| -}
  '(' : prS (t : u : ts) {-"~~."-}
\end{spec}
The case when the spine is a singleton |[Fork t u]| turns out to be absorbed by the case above.
We have thus derived the following definition of |prS|:
\begin{spec}
prS [Null]           = ""
prS (Null : ts)      = ')' : prS ts
prS (Fork t u : ts)  = '(' : prS (t : u : ts) {-"~~."-}
\end{spec}

We are now ready to invert |prS| by Theorem~\ref{thm:conv-fun},
which amounts to finding |base| and |step| such that |prS base = ""| and |prS (step x ts) = x : prS ts| for |x = '('| or |')'|.
Now that |prS| has been transformed into the form above, apparently |base = [Null]|, and |step| is given by:
\begin{spec}
step ')' ts = Null : ts
step '(' (t : u : ts) = Fork t u : ts {-"~~."-}
\end{spec}
In other words, if we define
\begin{spec}
build :: String -> Spine
build "" = [Null]
build (')':xs) = Null : build xs
build ('(':xs) = case build xs of (t : u : ts) -> Fork t u : ts {-"~~,"-}
\end{spec}
We have that |prS (build ts) = ts| for all |ts| in the domain of |build|.
