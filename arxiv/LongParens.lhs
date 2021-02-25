\documentclass{article}
% build using
%    lhs2TeX LongParens.lhs | pdflatex --jobname=LongParens

%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt

\usepackage{classicthesis}
\usepackage{amsmath}
%\usepackage{amsfonts}
\usepackage{scalerel}
\usepackage{hyperref}
\usepackage{url}
\usepackage[dvipsnames]{xcolor}
\usepackage{subcaption}
\usepackage{graphicx}
\usepackage{natbib}
\usepackage[T1]{fontenc}

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
\newtheorem{definition}[theorem]{Definition}
\newtheorem{lemma}[theorem]{Lemma}

\definecolor{mediumpersianblue}{rgb}{0.0, 0.4, 0.65}
\everymath{\color{mediumpersianblue}}

\begin{document}


%% Title information
\title{{\large\bf Functional Pearl}\\
Longest Segment of Balanced Parentheses:\\
{\large an Exercise in Program Inversion in a Segment Problem}}
%\jnlDoiYr{2020}

\author{\color{black} Shin-Cheng Mu,~Tsung-Ju Chiang\\
%\affiliation{
    {\small\color{black}  Institute of Information Science, %\\
    Academia Sinica, Taiwan} %\\
    %\email{scm@@iis.sinica.edu.tw}
    }
\date{}
\maketitle

\begin{abstract}
Given a string of parentheses, the task is to find a longest consecutive egment that is properly bracketed.
We find it an interesting problem because it involves two techniques: the usual approach for solving segment problems, and the converse-of-a-function theorem --- through which we derived an instance of shift-reduce parsing.
\end{abstract}

% \keywords{program inversion \and segment problem}


%include sections/Intro.lhs
%include sections/ConvFnThm.lhs
%include sections/Spine.lhs
%include sections/Foldify.lhs
%include sections/Wrap.lhs

%% Bibliography
\bibliographystyle{abbrvnat}
%\bibliography{LongParens}
\input{LongParens.bbl}

\appendix
\renewcommand{\thesection}{\Alph{section}}
% \renewcommand{\appendixname}{A}
% \renewcommand{\theequation}{A.\arabic{equation}}
  % redefine the command that creates the equation no.
\setcounter{equation}{0}  % reset counter
%include sections/Appendix.lhs

\end{document}
