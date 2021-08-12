\RequirePackage{amsmath}
\documentclass{jfp}
% build using
%    lhs2TeX LongParens.lhs | pdflatex --jobname=LongParens

%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt
%include Formatting.fmt

\usepackage[dvipsnames]{xcolor}
\usepackage{amsfonts}
\usepackage{scalerel}
\usepackage{hyperref}
\usepackage{url}
\usepackage{xcolor}
\usepackage{subcaption}
\usepackage{graphicx}
\usepackage[T1]{fontenc}
\usepackage{textcomp}
%\usepackage[utf8x]{inputenc}

\usepackage{doubleequals}

%\input{Preamble}

\setlength{\mathindent}{15pt}

\newcommand{\todo}[1]{{\bf [To do: #1]}}
\newcommand{\delete}[1]{}

\allowdisplaybreaks

\newcommand{\txbr}[1]{\textcolor{Orange}{#1}}
\newcommand{\txtl}[1]{\textcolor{teal}{#1}}
\newcommand{\txbl}[1]{\textcolor{Cerulean}{#1}}
\newcommand{\scm}[1]{\textcolor{teal}{#1}}
% \newcommand{\koen}[1]{\textcolor{blue}{#1}}
% \newcommand{\tom}[1]{\textcolor{red}{#1}}

\newtheorem{theorem}{Theorem}[section]
\newtheorem{definition}[theorem]{Definition}
\newtheorem{lemma}[theorem]{Lemma}

\begin{document}

\journaltitle{JFP}
\cpr{Cambridge University Press}
\doival{TODO}

%% Title information
\title{Longest Segment of Balanced Parentheses:\\
\large
an Exercise in Program Inversion in a Segment Problem}
\jnlDoiYr{2021}
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

\begin{abstract}
Given a string of parentheses, the task is to find the longest consecutive segment that is balanced, in linear time.
We find this problem interesting because it involves techniques: the usual approach for solving segment problems, and a theorem for constructing the inverse of a function --- through which we derive an instance of shift-reduce parsing.
\end{abstract}

% \keywords{program inversion \and segment problem}

\maketitle[F]

%include sections/Intro.lhs
%include sections/ConvFnThm.lhs
%include sections/Spine.lhs
%include sections/Foldify.lhs
%include sections/Wrap.lhs

%% Bibliography
\bibliographystyle{JFPlike}
\bibliography{LongParens}
%\input{LongParens.bbl}

%\appendix
%\renewcommand{\thesection}{\Alph{section}}
% \renewcommand{\appendixname}{A}
% \renewcommand{\theequation}{A.\arabic{equation}}
  % redefine the command that creates the equation no.
%\setcounter{equation}{0}  % reset counter
%%include sections/Appendix.lhs

\end{document}
