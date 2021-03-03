\documentclass[acmsmall]{acmart}

% build using
%    lhs2TeX LongParensICFP.lhs | pdflatex --jobname=LongParensICFP

%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt

\usepackage{scalerel}
\usepackage{paralist}
\usepackage{doubleequals}

\setlength{\mathindent}{15pt}

\AtBeginDocument{%
  \providecommand\BibTeX{{%
    \normalfont B\kern-0.5em{\scshape i\kern-0.25em b}\kern-0.8em\TeX}}}

\setcopyright{acmcopyright}
\copyrightyear{2021}
\acmYear{2021}
\acmDOI{10.1145/???.???}

\acmJournal{PACMPL}
\acmVolume{5}
\acmNumber{ICFP}
\acmArticle{111}
\acmMonth{8}

% \acmJournal{Proc. ACM Program. Lang}
% \acmVolume{37}
% \acmNumber{4}
% \acmArticle{1}
% \acmMonth{9}

\begin{document}

\title[Longest Segment of Balanced Parentheses]%
{Longest Segment of Balanced Parentheses:\\
An Exercise in Program Inversion in a Segment Problem.
{\small Functional Pearl}}

\author{Anonymous}
% \author{Shin-Cheng Mu}
% %\authornote{Both authors contributed equally to this research.}
% %\email{trovato@corporation.com}
% %\orcid{1234-5678-9012}
% \author{Tsung-Ju Chiang}
% %\authornotemark[1]
% %\email{webmaster@marysville-ohio.com}
% \affiliation{%
% \institution{Institute of Information Science, %\\
% Academia Sinica}
% \country{Taiwan}
}

%\renewcommand{\shortauthors}{Mu and Chiang}

\begin{abstract}
Given a string of parentheses, the task is to find the longest consecutive segment that is balanced, in linear time.
We find this problem interesting because it involves techniques: the usual approach for solving segment problems, and a theorem for constructing the inverse of a function --- through which we derive an instance of shift-reduce parsing.
\end{abstract}

\begin{CCSXML}
<ccs2012>
<concept>
<concept_id>10003752.10010124.10010138</concept_id>
<concept_desc>Theory of computation~Program reasoning</concept_desc>
<concept_significance>500</concept_significance>
</concept>
<concept>
<concept_id>10011007.10011006.10011008.10011009.10011012</concept_id>
<concept_desc>Software and its engineering~Functional languages</concept_desc>
<concept_significance>500</concept_significance>
</concept>
</ccs2012>
\end{CCSXML}

\ccsdesc[500]{Theory of computation~Program reasoning}
\ccsdesc[500]{Software and its engineering~Functional languages}

\keywords{program derivation, segment problems, program inversion, parsing}

\maketitle

%include sections/Intro.lhs
%include sections/ConvFnThm.lhs
%include sections/Spine.lhs
%include sections/Foldify.lhs
%include sections/Wrap.lhs


\bibliographystyle{ACM-Reference-Format}
%\bibliography{LongParensICFP}
\input{LongParensICFP.bbl}
\end{document}
