\RequirePackage{amsmath}
\documentclass{jfp}

% build using
%    lhs2TeX LongParens.lhs | pdflatex --jobname=LongParens

%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt

\usepackage{amsfonts}
\usepackage{hyperref}
\usepackage{url}
\usepackage{xcolor}
\usepackage{subcaption}
\usepackage{graphicx}

\usepackage{doubleequals}

%\input{Preamble}

\setlength{\mathindent}{15pt}

\newcommand{\todo}[1]{{\bf [To do: #1]}}
\newcommand{\delete}[1]{}

\allowdisplaybreaks

\newcommand{\scm}[1]{\textcolor{teal}{#1}}
% \newcommand{\koen}[1]{\textcolor{blue}{#1}}
% \newcommand{\tom}[1]{\textcolor{red}{#1}}

\newtheorem{theorem}{Theorem}
\newtheorem{definition}{Definition}
\newtheorem{lemma}{Lemma}

\begin{document}

\journaltitle{JFP}
\cpr{Cambridge University Press}
\doival{TODO}

%% Title information
\title{Longest Segment of Balanced Parentheses:\\
\large
an Exercise in Program Inversion in a Segment Problem}
\jnlDoiYr{2020}
\titlerunning{Longest Segment of Balanced Parentheses}

\begin{authgrp}
  \author{Shin-Cheng Mu,~}
  \author{Tsung-Ju Chiang}
  \affiliation{
    Institute of Information Science, %\\
    Academia Sinica, Taiwan %\\
    %\email{scm@@iis.sinica.edu.tw}
    }
\end{authgrp}

% \begin{abstract}

% \end{abstract}

% \keywords{monads \and effect handlers \and equational reasoning \and nondeterminism \and state \and contextual equivalence}

\maketitle[F]


%include sections/Intro.lhs
%include sections/ConvFnThm.lhs
%include sections/Spine.lhs


%% Bibliography
\bibliographystyle{JFPlike}
\bibliography{LongParens}


\end{document}
