\section{Converse-of-a-Function Theorem}

The converse-of-a-function theorem, introduced by \cite{BirddeMoor:97:Algebra}, gives us conditions under which the \emph{relational converse} --- a generalised notion of inverse --- of a function can be written as a \emph{relational} fold of any initial datatype defined as a least fixed-point of a base functor.
For this paper we need only a simplified version that covers functional folds on lists:
%{
%format finv = "\Varid{f}^{-1}"
\begin{theorem}
\label{thm:conv-fun}
Given |f :: b -> [a]|, if we have |base :: a| and |step :: a -> b -> b| satisfying:
\begin{align*}
|f base| &= |[]| \quad\wedge \\
|f (step x t)| &= |x : f t| \mbox{~~,}
\end{align*}
then |inv f = foldr step base xs| is a partial right inverse of |f|. That is, we have |f (inv f xs) = xs| for all |xs| in the domain of |inv f|.
\end{theorem}
%} % finv
% This functional version of them theorem can be proved by a simple induction on the input list.
% Define fold for non-empty lists:
% \begin{code}
% foldrn :: (a -> b -> b) -> (a -> b) -> [a] -> b
% foldrn step base [x]     = base x
% foldrn step base (x:xs)  = step x (foldrn step base xs) {-"~~,"-}
% \end{code}
% We also have a variation of the theorem where the condition on |base| is replaced by |f (base x) = [x]|.

% \todo{A simpler example, or trim some parts of this section off if they are not necessary.}

To find the right inverse of |pr| using Theorem~\ref{thm:conv-fun}, we have to find |step :: Char -> Tree -> Tree| such that
|pr (step x t) = x : pr t|, where |x| is either |'('| or |')'|.
One can see that there is no way this equality could hold: |pr| always returns strings containing balanced parentheses,
but the strings returned by the two calls to |pr| in the equation cannot be both balanced.
This is a hint that we should generalise the problem to consider trees that are partially built, which would be printed to strings of parentheses that are not necessarily balanced.
