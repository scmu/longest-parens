%if False
\begin{code}
{-# LANGUAGE StandaloneDeriving #-}
module ConvFnThm where

import Data.List
import Utilities
\end{code}
%endif

\section{Converse-of-a-Function Theorem}

Given a function |f :: b -> t|, the converse-of-a-function theorem \citep{BirddeMoor:97:Algebra, deMoorGibbons:00:Pointwise} constructs the relational converse --- a generalised notion of inverse --- of |f|.
The converse is given as a relational fold whose input type is |t|, which can be any inductively-defined datatype with a polynomial base functor.
We specialise the general theorem to our needs: we use it to construct only functions, not relations, and only for the case where |t| is a list type.
%{
%format finv = "\Varid{f}^{-1}"
\begin{theorem}
\label{thm:conv-fun}
{\rm
Given |f :: b -> [a]|, if we have |base :: b| and |step :: a -> b -> b| satisfying:
\begin{align*}
|f base| &= |[]| \quad\wedge \\
|f (step x t)| &= |x : f t| \mbox{~~,}
\end{align*}
then |inv f = foldr step base| is a partial right inverse of |f|. That is, we have |f (inv f xs) = xs| for all |xs| in the range of |f|.
} % rm
\end{theorem}
%} % finv

While the general version of the theorem is not trivial to prove,
the version above, specialised to functions and lists, can be verified by an easy induction on the input list.

To find the right inverse of |pr| using Theorem~\ref{thm:conv-fun}, we have to find |step :: Char -> Tree -> Tree| such that
|pr (step x t) = x : pr t|, where |x| is either |'('| or |')'|.
One can see that there is no way this equality could hold: |pr| always returns strings containing balanced parentheses,
but for all |u| such that |pr u = x : pr t|, it is not possible that both |pr u| and |pr t| are balanced.

This is a hint that we should instead consider a generalisation of |pr| which prints strings that are not necessarily fully balanced.
For |pr (step x t) = x : pr t| to possibly hold, |pr t| is a string of parentheses that might not be balanced yet, but can be balanced by being extended to the left.
We characterise such strings and consider how to parse them in the next section.

% This is a hint that we should instead consider a generalisation of |pr| whose inputs are not necessarily fully built trees (trees that print to balanced parentheses).
% For |pr (step x t) = x : pr t| to hold, |t| should also be able to represent  partially built trees that can still become balanced by being extended to the left.
