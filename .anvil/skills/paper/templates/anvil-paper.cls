%% anvil-paper.cls — Default LaTeX class for anvil:paper
%%
%% Minimal generic single-column research-paper class. Compiles cleanly with
%% pdflatex + bibtex from a fresh checkout, no venue-specific assumptions.
%% Consumers override by dropping a venue-specific .cls/.sty into
%% .anvil/skills/paper/templates/ in their own repo and setting the brief's
%% `documentclass:` frontmatter accordingly.
%%
%% Options:
%%   anonymous  Suppress author/affiliation rendering for double-blind submission.
%%   numeric    Render numeric [7]-style citations instead of the default
%%              author-year (Author, Year) style. Composes with anonymous.
%%
%% Provides:
%%   \title{}, \author{}, \date{}, \abstract{}
%%   Standard \section, \subsection, \subsubsection
%%   natbib (\citep, \citet) loaded with sort&compress; author-year
%%     (round) by default, numeric with the `numeric` option
%%   graphicx, amsmath, amssymb, xcolor, hyperref loaded
%%   booktabs + longtable + array + calc + caption loaded in that order, so
%%     a `pandoc -t latex` table body (which is always a `longtable`, and for
%%     wide tables uses `>{\raggedright\arraybackslash}p{... \real{...}}`
%%     column specs) typesets as-is, caption included. See issue #1328.
%%   plainnat bibliography style baked in (natbib-aware; adapts to
%%     both author-year and numeric modes)

\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{anvil-paper}[2026/05/28 Anvil generic paper class]

%% Option handling ---------------------------------------------------------
\newif\ifanvil@anonymous
\anvil@anonymousfalse
\DeclareOption{anonymous}{\anvil@anonymoustrue}
\newif\ifanvil@numeric
\anvil@numericfalse
\DeclareOption{numeric}{\anvil@numerictrue}
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{article}}
\ProcessOptions\relax

%% Base class --------------------------------------------------------------
\LoadClass[11pt,letterpaper]{article}

%% Geometry: reasonable margins for readability + comfortable line length
\RequirePackage[margin=1in]{geometry}

%% Common packages ---------------------------------------------------------
\RequirePackage{graphicx}
\RequirePackage{amsmath}
\RequirePackage{amssymb}
\RequirePackage{amsthm}
\RequirePackage{microtype}
%% Citation style: author-year (round) by default; numeric with `numeric`
%% option. `numbers` and `authoryear` are mutually exclusive natbib globals,
%% so this must be a conditional load, not an option-append. plainnat (set as
%% the default bibliographystyle below) is natbib-aware and renders correctly
%% under either mode, so no bibliographystyle branching is required.
\ifanvil@numeric
  \RequirePackage[numbers,sort&compress]{natbib}
\else
  \RequirePackage[round,sort&compress,authoryear]{natbib}
\fi
\RequirePackage{booktabs}
%% Table packages, ordered BEFORE caption on purpose (issue #1328).
%% `longtable` is what `pandoc -t latex` emits for every pipe table, so a
%% manuscript converted with pandoc pastes in `\begin{longtable}` bodies that
%% the class must be able to typeset without the consumer patching the
%% preamble. `array` backs pandoc's `>{\raggedright\arraybackslash}p{...}`
%% column specs; `calc` backs the `\real{...}` width arithmetic in them.
%% The ordering is load-bearing: `caption` registers its longtable-aware
%% `\LT@` hooks for a `longtable` that is already loaded when `caption` itself
%% loads. Adding `\usepackage{longtable}` to the *document* preamble instead
%% is not a reliable substitute -- on older caption/longtable releases nothing
%% installs those hooks retroactively, which is the reported
%% "No counter 'none' defined" failure at the first `\caption` inside a
%% longtable. Do not move `caption` above this block.
\RequirePackage{longtable}
\RequirePackage{array}
\RequirePackage{calc}
\RequirePackage{xcolor}
\RequirePackage{caption}
\captionsetup{font=small,labelfont=bf}
\RequirePackage[colorlinks=true,linkcolor=blue!50!black,citecolor=blue!50!black,urlcolor=blue!50!black]{hyperref}
\RequirePackage{url}

%% Default bibliography style — consumers can override with their own
%% \bibliographystyle{...} in main.tex.
\AtBeginDocument{%
  \ifx\@bibstyle\@empty\bibliographystyle{plainnat}\fi%
}

%% Anonymous-mode author block --------------------------------------------
\ifanvil@anonymous
  \renewcommand{\@maketitle}{%
    \begin{center}%
      {\LARGE\bfseries\@title\par}%
      \vskip 1em%
      {\large Author Name(s) Withheld\par}%
      {\itshape Affiliation Withheld\par}%
      \vskip 0.5em%
      {\small\@date\par}%
    \end{center}%
  }%
\fi

%% Abstract formatting -----------------------------------------------------
\renewenvironment{abstract}%
  {\begin{center}\bfseries Abstract\end{center}%
   \begin{quote}\small}%
  {\end{quote}}

%% Section spacing — slightly tighter than article defaults
\renewcommand{\section}{\@startsection{section}{1}{\z@}%
  {-2.5ex \@plus -1ex \@minus -.2ex}%
  {1.5ex \@plus.2ex}%
  {\normalfont\large\bfseries}}
\renewcommand{\subsection}{\@startsection{subsection}{2}{\z@}%
  {-2.0ex \@plus -1ex \@minus -.2ex}%
  {1.0ex \@plus.2ex}%
  {\normalfont\normalsize\bfseries}}

%% End of class ------------------------------------------------------------
\endinput
