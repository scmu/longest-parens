%if False
\begin{code}
module Spine where

import Intro
import Utilities
import Data.List (inits, tails)
import Control.Monad ((<=<))
\end{code}
%endif

\section{Parsing Partially Balanced Strings}
\label{sec:spine}

A string of parentheses is said to be \emph{left-partially balanced} if it may possibly be balanced by adding zero or more parentheses to the left.
For example, |xs = "(())()))()"| is left-partially balanced because |"((" ++ xs| is balanced. Note that |"(()(" ++ xs| is also balanced.
As a counter example, the string |ys = "()(()"| is not left-partially balanced --- due to the unmatched |'('| in the middle of |ys|, there is no |zs| such that |zs++ys| is balanced.

While parsing a fully balanced string cannot be expressed as a right fold, it is possible to parse left-partially balanced strings using a right fold.
In this section we consider what data structure such a string should be parsed to, how to parse it, and finally formally define |parse|.

A left-partially balanced string can always be uniquely factored into a sequence of balanced substrings, separated by one or more right parentheses.
For example, |xs| can be factored into two balanced substrings, |"(())()"| and |"()"|, separated by |"))"|.
One of the possible ways to represent such a string is by a list of trees --- a |Forest|, where the trees are supposed to be separated by a |')'|.
That is, such a forest can be printed by:
\newcommand{\hscomment}[1]{\{-~~\mbox{#1}~~-\}}
\begin{code}
type Forest = [Tree] {-"~~,\qquad\qquad \hscomment{non-empty}"-}

prF :: Forest -> String
prF [t]     = pr t
prF (t:ts)  = pr t ++ ")" ++ prF ts {-"~~."-}
\end{code}
For example, |xs = "(())()))()"| can be represented by a forest containing three trees:
\begin{spec}
ts = [Bin (Bin Nul Nul) (Bin Nul Nul), {-"~~"-} Nul, {-"~~"-} Bin Nul Nul] {-"~~,"-}
\end{spec}
where |Bin (Bin Nul Nul) (Bin Nul Nul)| prints to |"()(())"|,
|Bin Nul Nul| prints to |"()"|, and there is a |Nul| between
them due to the consecutive right parentheses |"))"| in |xs|.
One can verify that |prF ts = xs| indeed.
Note that we can let the type |Forest| be \emph{non-empty} lists of trees, since the empty string can be represented by |[Nul]|: |prF [Nul] = pr Nul = ""|.
\footnote{We have also tried an equivalent representation: |Forest = ([Tree], Tree)|. Presentation-wise, both representations have their pros and cons, and we eventually decided on non-empty lists.}

The aim now is to construct the right inverse of |prF| using Theorem~\ref{thm:conv-fun} --- thereby parsing a left-partially balanced string using a right fold.
It will be easier if we first construct a new definition of |prF|, one that is inductive, does not use |(++)|, and does not rely on |pr|.
For a base case, |prF [Nul] = ""|.
It is also immediate that |prF (Nul:ts) = ')' : prF ts|.
When the list contains more than one tree and the first tree is not |Nul|, we calculate:
% %if False
% \begin{code}
% prFIndDer0 :: Tree -> [Tree] -> String
% prFIndDer0 t ts =
% \end{code}
% %endif
% \begin{code}
%       prF (Nul:t:ts)
%  ===     {- definition of |prF| -}
%       pr Nul ++ ")" ++ pr t ++ foldr (\u xs -> ")" ++ pr u ++ xs) "" ts
%  ===  ')' : prF (t:ts) {-"~~."-}
% \end{code}
% When the first tree has the form |Bin t u|:
%if False
\begin{code}
prFIndDer1 :: Tree -> Tree -> Forest -> String
prFIndDer1 t u ts =
\end{code}
%endif
\begin{code}
      prF (Bin t u: ts)
 ===    {- definitions of |pr| and |prF| -}
      "(" ++ pr t ++ ")" ++ pr u ++ ")" ++ prF ts
 ===    {- definition of |prF| -}
      '(' : prF (t : u : ts) {-"~~."-}
\end{code}
We have thus derived the following new definition of |prF|:
%{
%format prF' = prF
\begin{code}
prF' [Nul]         = ""
prF' (Nul:ts)      = ')' : prF' ts
prF' (Bin t u:ts)  = '(' : prF' (t:u:ts) {-"~~."-}
\end{code}
%}

We are now ready to invert |prF| by Theorem~\ref{thm:conv-fun},
which amounts to finding |base| and |step| such that |prF base = ""| and |prF (step x ts) = x : prF ts| for |x = '('| or |')'|.
With the inductive definition of |prF| in mind, we pick |base = [Nul]|, and |step| is given by:
\begin{spec}
step ')' ts            =  Nul : ts
step '(' (t : u : ts)  =  Bin t u : ts {-"~~."-}
\end{spec}
We have thus constructed |inv prF = foldr step [Nul]|,
that is,
%format prFi = "{\Varid{prF}}^{\hstretch{0.5}{-}1}"
\begin{code}
prFi :: String -> Forest
prFi ""        = [Nul]
prFi (')':xs)  = Nul : prFi xs
prFi ('(':xs)  = case prFi xs of (t : u : ts) -> Bin t u : ts {-"~~,"-}
\end{code}
which is pleasingly symmetrical to the inductive definition of |prF|.

For an operational explanation,
a right parenthesis |')'| indicates starting a new tree, thus we start freshly with a |Nul|;
a left parenthesis |'('| ought to be the leftmost symbol of some |"(t)u"|,
thus we wrap the two most recent siblings into one tree.
When there are no such two siblings (that is, |inv prF xs| in the |case| expression evaluates to a singleton list), the input |'(':xs| is not a left-partially balanced string --- |'('| appears too early.
The partial function |inv prF| thus just fails.

Readers may have noticed the similarity to shift-reduce parsing,
in which, after reading a symbol we either "shift"
the symbol by pushing it onto a stack, or "reduce" the symbol against
a top segment of the stack.
Here, the forest is the stack.
The input is processed right-to-left, as opposed to left-to-right, which is more common when talking about parsing.
More discussions will be given in Section~\ref{sec:conclude}.

%This is a special case where the decision to shift or reduce can be made by looking ahead to a single symbol.

We could proceed to work with |inv prF| for the rest of this pearl but,
for clarity, we prefer to observe partiality explicitly.
Let |parseF| be the monadified version of |inv prF|, given by:
\begin{code}
parseF :: String -> Maybe Forest
parseF ""      = Just [Nul]
parseF (x:xs)  = parseF xs >>= stepM x {-"~~,"-}
  where  stepM ')' ts            = Just (Nul : ts)
         stepM '(' [t]           = Nothing
         stepM '(' (t : u : ts)  = Just (Bin t u : ts) {-"~~,"-}
\end{code}
where |stepM| is monadified |step| --- for the case |[t]| missing in |step| we return |Nothing|.
% Note that another way to write the inductive case is
% |parseS (x:xs) = (stepM x <=< parseS) xs|, where |(<=<) :: (b -> M c) -> (a -> M b) -> (a -> M c)| is Kleisli composition, an operator we will use later.

To relate |parseF| to |parse|, notice that |prF [t] = pr t|.
We therefore have
%{
%format parse' = parse
\begin{code}
parse' :: String -> Maybe Tree
parse' = unwrapM <=< parseF {-"~~."-}
\end{code}
%}
where |(<=<) :: (b -> M c) -> (a -> M b) -> (a -> M c)| is (reversed) Kleisli composition, and |unwrapM [t] = Just t|; otherwise |unwrapM| returns |Nothing|.
That is, |parse| calls |parseF|, but declares success only when the input can be parsed into a single tree.

%if False
\begin{code}
type Spine = [Tree]

unwrapM [t]  = Just t
unwrapM _    = Nothing

stepM :: Char -> Spine -> Maybe Spine
stepM ')' ts            = Just (Nul : ts)
stepM '(' [t]           = Nothing
stepM '(' (t : u : ts)  = Just (Bin t u : ts)
\end{code}
%endif
