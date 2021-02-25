\section{Converse-of-a-Function Theorem}

Given a function |f :: b -> t|, the converse-of-a-function theorem \citep{BirddeMoor:97:Algebra, deMoorGibbons:00:Pointwise} constructs the relational converse --- a generalised notion of inverse --- of |f|.
The converse is given as a relational fold whose input type is |t|, which can be any inductively-defined datatype with a polynomial base functor.
We specialize the general theorem for our needs: we use it to construct only functions, not relations, and only when |t| is a list.
%{
%format finv = "\Varid{f}^{-1}"
\begin{theorem}
\label{thm:conv-fun}
Given |f :: b -> [a]|, if we have |base :: b| and |step :: a -> b -> b| satisfying:
\begin{align*}
|f base| &= |[]| \quad\wedge \\
|f (step x t)| &= |x : f t| \mbox{~~,}
\end{align*}
then |inv f = foldr step base xs| is a partial right inverse of |f|. That is, we have |f (inv f xs) = xs| for all |xs| in the domain of |inv f|.
\end{theorem}
%} % finv

While the general version of the theorem is not trivial to prove,
the version above specialized to functions and lists can be verified by an easy induction on the input list.

To find the right inverse of |pr| using Theorem~\ref{thm:conv-fun}, we have to find |step :: Char -> Tree -> Tree| such that
|pr (step x t) = x : pr t|, where |x| is either |'('| or |')'|.
One can see that there is no way this equality could hold: |pr| always returns strings containing balanced parentheses,
but for all |u| such that |pr u = x : pr t|, it is not possible that both |pr u| and |pr t| are balanced.

This is a hint that we should instead consider a generalisation of |pr| whose input are not necessarily fully built trees (that print to balanced parentheses).
For |pr (step x t) = x : pr t| to hold, |t| should represent some partially built trees that can still be extended from the left, while |step x t| extends |t| such that its printout is preceded by an additional |x|.
