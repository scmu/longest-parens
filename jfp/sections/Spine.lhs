%if False
\begin{code}
module Spine where

import Intro
import Utilities
\end{code}
%endif

\section{The Spine Tree}
\label{sec:spine}

\begin{figure}[t]
  \centering
    \begin{subfigure}{.4\textwidth}
      \centering
       \includegraphics[scale=0.2]{pics/spine03.pdf}
       \caption{After having read \texttt{t)u)v}.}
       \label{fig:spine01}
    \end{subfigure}
    \begin{subfigure}{.4\textwidth}
      \centering
      \includegraphics[scale=0.2]{pics/spine04.pdf}
      \caption{After reading two more symbols.}
      \label{fig:spine02}
    \end{subfigure}
\caption{The tree constructed while reading \texttt{"(()(()t)u)v"}. |Fork| is represented by a round node, and |Null| the ground symbol.}
\label{fig:spine}
\end{figure}

Our aim now is to construct a data structure that represent partially built trees that can be extended from left.
%
Figure~\ref{fig:spine01} shows a tree constructed from
\texttt{"(()(()t)u)v"}.
The input is processed from right to left, and when we have only read
\texttt{"t)u)v"}, we should have construct the three trees |t|, |u|, and
|v| under the dotted line.
If we read two more symbols \texttt{"()"}, we should have constructed the
three trees under the dotted line of Figure~\ref{fig:spine02},
where |u| and |v| stay the same, while |t| is extended to |Fork Null t|, which prints to \texttt{"()t"}.

One may infer that we should maintain a list of trees while reading an input halfway. In Figure~\ref{fig:spine01} the list is |[t,u,v]|, and in Figure~\ref{fig:spine02} |[Fork Null t, u, v]|.
This \emph{spine representation} --- so called because the list contains subtrees alone the left spine of the final tree --- was also used by, for example \cite{MuBird:03:Theory}, to efficiently build trees in a |foldr|.
Let |Spine| be a \emph{non-empty} list of |Tree|s:
\begin{code}
type Spine = [Tree] {-"~~."-}
\end{code}
The following function rolls a spine back to an ordinary tree:
\begin{code}
roll :: Spine -> Tree
roll [t]       = t
roll (t:u:ts)  = roll (Fork t u : ts)
\end{code}
For example, |roll [t,u,v,w] = Fork (Fork (Fork t u) v) w|.

How do we print a spine?
Inspired by Figure~\ref{fig:spine}, |[t,u,v] :: Spine|
should be printed as |"t)u)v"|, where \texttt{t} and \texttt{u}, etc. in typewriter font denote |pr t| and |pr u|.
More generally, the following function |prS| prints a |Spine|:
\begin{code}
prS :: Spine -> String
prS [t]     = pr t
prS (t:ts)  = pr t ++ ")" ++ prS ts {-"~~."-}
\end{code}
To relate it to |roll|, for all |ts| we have
%if False
\begin{code}
propPrRoll :: Spine -> String
propPrRoll ts =
 pr (roll ts) ===  replicate (length ts - 1) '(' ++ prS ts {-"~~,"-}
\end{code}
%endif
\begin{equation}
  |pr (roll ts) = replicate (length ts - 1) '(' ++ prS ts| \mbox{~~.}
\label{eq:pr-roll}
\end{equation}
% \begin{equation}
% \begin{split}
%  |pr (roll (t,ts))| &= |replicate (length ts - 1) '('| \\
%                     & \qquad |foldr (\u xs -> pr u ++ ")" ++ xs) "" ts| \mbox{~~.}
% \end{split}
% \label{eq:pr-roll}
% \end{equation}
where |replicate n x| returns a list containing |n| copies of |x|.
Proof of \eqref{eq:pr-roll} is a routine induction on |ts|.

Before using Theorem~\ref{thm:conv-fun}, we construct an inductive definition of |prS| that does not use |(++)| and does not rely on |pr|.
For a base case, |prS [Null] = ""|.
It is also immediate that |prS (Null:ts) = ')' : prS ts|.
When the spine contains more than one tree and the first tree is not |Null|, we calculate:
% %if False
% \begin{code}
% prSIndDer0 :: Tree -> [Tree] -> String
% prSIndDer0 t ts =
% \end{code}
% %endif
% \begin{code}
%       prS (Null:t:ts)
%  ===     {- definition of |prS| -}
%       pr Null ++ ")" ++ pr t ++ foldr (\u xs -> ")" ++ pr u ++ xs) "" ts
%  ===  ')' : prS (t:ts) {-"~~."-}
% \end{code}
% When the first tree has the form |Fork t u|:
%if False
\begin{code}
prSIndDer1 :: Tree -> Tree -> [Tree] -> String
prSIndDer1 t u ts =
\end{code}
%endif
\begin{code}
      prS (Fork t u: ts)
 ===    {- definitions of |pr| and |prS| -}
      "(" ++ pr t ++ ")" ++ pr u ++ ")" ++ prS ts
 ===    {- definition of |prS| -}
      '(' : prS (t : u : ts) {-"~~."-}
\end{code}
% --   pr (Fork t u) ++ foldr (\u xs -> ")" ++ pr u ++ xs) "" ts
% -- =   {- definition of |pr| -}
% The case when the spine is a singleton |[Fork t u]| turns out to be absorbed by the case above.
We have thus derived the following definition of |prS|:
%{
%format prS' = prS
\begin{code}
prS' [Null]         = ""
prS' (Null:ts)      = ')' : prS' ts
prS' (Fork t u:ts)  = '(' : prS' (t:u:ts) {-"~~."-}
\end{code}
%}
We are now ready to invert |prS| by Theorem~\ref{thm:conv-fun},
which amounts to finding |base| and |step| such that |prS base = ""| and |prS (step x ts) = x : prS ts| for |x = '('| or |')'|.
Now that |prS| has been transformed into the form above, we pick |base = [Null]|, and |step| is given by:
\begin{spec}
step ')' ts            =  Null : ts
step '(' (t : u : ts)  =  Fork t u : ts {-"~~."-}
\end{spec}
We have thus constructed |inv prS = foldr step [Null]|,
that is,
%format prSi = "{\Varid{prS}}^{\hstretch{0.5}{-}1}"
\begin{code}
prSi ""        = [Null]
prSi (')':xs)  = Null : prSi xs
prSi ('(':xs)  = case prSi xs of (t : u : ts)  -> Fork t u : ts {-"~~,"-}
\end{code}
which is pleasingly symmetrical to |prS|.

For an operational explanation,
a right parenthesis |')'| indicates starting a new tree, thus we start freshly with a |Null|;
a left parenthesis |'('| ought to be the leftmost symbol of some |"(t)u"|,
thus we wrap the two most recent siblings into one tree.
When there are no such two siblings (that is, |inv prS xs = [t]|), the construction fails --- |inv prS| is a partial function.

Some readers might have noticed the similarity to shift-reduce parsing,
in which, after reading a symbol we either "shift"
the symbol by pushing it onto a stack, or "reduce" the symbol against
a top segment of the stack.
Here, the spine tree is the stack. This is a special case where the decision to shift or reduce can be made by looking ahead to a single symbol.


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

We could proceed to work with |inv prS| for the rest of this pearl but,
for clarity, we prefer to observe partiality explicitly.
Let |parseS| be the monadified version of |inv prS|, given by:
\begin{code}
parseS :: String -> Maybe Spine
parseS ""      = Just [Null]
parseS (x:xs)  = parseS xs >>= stepM x {-"~~,"-}
  where  stepM ')' ts            = Just (Null : ts)
         stepM '(' [t]           = Nothing
         stepM '(' (t : u : ts)  = Just (Fork t u : ts) {-"~~,"-}
\end{code}
where |stepM| is monadified |step| --- for the case |[t]| missing in |step| we return |Nothing|.
% Note that another way to write the inductive case is
% |parseS (x:xs) = (stepM x <=< parseS) xs|, where |(<=<) :: (b -> M c) -> (a -> M b) -> (a -> M c)| is Kleisli composition, an operator we will use later.

To relate |parseS| to |parse|, notice that |prS [t] = pr t|.
We therefore have |parse = unwrapM <=< parseS|,
where |(<=<) :: (b -> M c) -> (a -> M b) -> (a -> M c)| is (reversed) Kleisli composition, and |unwrapM [t] = Just t|, otherwise |unwrapM| returns |Nothing|.

%if False
\begin{code}
unwrapM [t]  = Just t
unwrapM _    = Nothing

stepM :: Char -> Spine -> Maybe Spine
stepM ')' ts            = Just (Null : ts)
stepM '(' [t]           = Nothing
stepM '(' (t : u : ts)  = Just (Fork t u : ts)
\end{code}
%endif
