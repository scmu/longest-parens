%if False
\begin{code}
module Longest where
\end{code}
%endif

\section{Longest Segment}
\label{sec:longest}

\begin{spec}
total f x  = f x   {-"\quad\mbox{, } x \in \Varid{dom}~\Varid{f} "-}
           = Null  {-"\quad\mbox{, otherwise.}"-}
\end{spec}

|parse = total (inv pr)|.

|pr = prS . wrap|

|total (inv wrap . inv prS)|

|total head . build|
