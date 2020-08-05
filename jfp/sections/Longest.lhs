%if False
\begin{code}
module Longest where
\end{code}
%endif

\section{Longest Segment}
\label{sec:longest}

Given a singleton spine |[t]|

That is, we have |pr = prS . wrap|, where |wrap x = [x]|.
The function |inv prS| is not total either.
Its domain consists of proper print-outs of |Spine| -- strings of the form |"t1)t2)...tn"| where {\tt t1} .. {\tt tn} are balanced parentheses (including empty strings). For example, |")"|, |"())"|, |"()()"|, |"())()"| are all in the domain of |inv prS|, while |"()("| is not.


|pr = prS . wrap|

|total (inv wrap . inv prS)|

\begin{spec}
build :: String -> Spine
build "" = [Null]
build (')':xs) = Null : build xs
build ('(':xs) = case build xs of  [t] -> [Null]
                                   (t : u : ts) -> Fork t u : ts {-"~~,"-}
\end{spec}


\begin{spec}
   maxBy size . map (total (inv pr)) . inits
=    {- since |pr = prS . wrap| -}
   maxBy size . map (total (inv wrap . inv prS)) . inits
=  maxBy size . map (total (inv wrap) . build) . inits
=  maxBy size . map (head . build) . inits
\end{spec}
