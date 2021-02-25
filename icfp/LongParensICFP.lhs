\documentclass[acmsmall]{acmart}

% build using
%    lhs2TeX LongParensICFP.lhs | pdflatex --jobname=LongParensICFP

%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt

\usepackage{scalerel}
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
{Longest Segment of Balanced Parentheses\\
{\small Functional Pearl}}

\author{Shin-Cheng Mu}
%\authornote{Both authors contributed equally to this research.}
%\email{trovato@corporation.com}
%\orcid{1234-5678-9012}
\author{Tsung-Ju Chiang}
%\authornotemark[1]
%\email{webmaster@marysville-ohio.com}
\affiliation{%
\institution{Institute of Information Science, %\\
Academia Sinica}
\country{Taiwan}
}

%\renewcommand{\shortauthors}{Mu and Chiang}

\begin{abstract}
Given a string of parentheses, the task is to find a longest consecutive segment that is balanced.
We find it an interesting problem because it involves two techniques: the usual approach for solving segment problems, and the converse-of-a-function theorem --- through which we derived an instance of shift-reduce parsing.
\end{abstract}

\keywords{program derivation, segment problems, program inversion, parsing}

\maketitle

%include sections/Intro.lhs


\bibliographystyle{ACM-Reference-Format}
\bibliography{LongParensICFP}
\end{document}
