%% anvil-doc.cls — Shared XeLaTeX base class for Anvil Markdown-substrate skills
%%
%% This is the shared base class extracted from anvil-installation.cls (issue #310).
%% It unifies the shared XeLaTeX preamble family across Markdown-substrate skills
%% (anvil:installation, anvil:proposal, and future doc-class consumers). Per-skill
%% accent palettes, titles, and footers are customized via the BRIEF.md frontmatter
%% keys and the anvil-doc.tex.j2 template.
%%
%% ── Engine ──────────────────────────────────────────────────────────────────
%% Compile with XeLaTeX (NOT pdflatex): the class uses fontspec for system fonts.
%%   xelatex doc.tex
%% This differs from anvil:paper (pdflatex). The render primitive in
%% anvil/lib/latex_render.py drives the two-pass xelatex invocation.
%%
%% ── Fonts ───────────────────────────────────────────────────────────────────
%% Default main font is Helvetica Neue (the signature face of the installation
%% and proposal worked examples). Consumers without Helvetica Neue installed get
%% an automatic fallback to Latin Modern Sans via \IfFontExistsTF, so the class
%% compiles on a stock TeX Live install with no system fonts.
%%
%% ── Provides ────────────────────────────────────────────────────────────────
%%   \anvildoctitle, \anvildocstudio, \anvildocdate, \anvildocstage  — metadata setters
%%   \anvildoctype  — footer label string (default "Document")
%%   \maketitleblock  — renders the title block + accent rule
%%   \herofigure{path}  — full-width hero image (no-op if path is empty)
%%   \coda{text}  — closing accent rule + italic coda
%%   callout (tcolorbox)   — left accent border; used for Premise / key-framing
%%   metricbox (tcolorbox) — breakable borderless bg fill; used for spec/budget tables
%%   colors: ink, accent, muted, bg, rule
%%
%% ── Options ─────────────────────────────────────────────────────────────────
%%   landscape — switches geometry from portrait to landscape letter (792 x 612 pt).
%%               Driven from the BRIEF.md `orientation: landscape` frontmatter key
%%               by the anvil-doc.tex.j2 template. Default portrait.
%%   (other)  — the signature accent color is set via \definecolor in the preamble
%%              below; the template overrides it from the brief's signature_color.

\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{anvil-doc}[2026/06/04 v0.1 Anvil shared Markdown-substrate document class]

%% landscape orientation flag — declared option that sets a boolean the geometry
%% block conditionally honors. Default false (portrait). See \ifanvil@landscape
%% in the layout section below.
\newif\ifanvil@landscape
\anvil@landscapefalse
\DeclareOption{landscape}{\anvil@landscapetrue}
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{article}}
\ProcessOptions\relax

%% Base class — single-column article, 10pt, US Letter
\LoadClass[10pt,letterpaper]{article}

%% ─── Typography ──────────────────────────────────────────────────────────────
\RequirePackage{fontspec}
%% Helvetica Neue with documented fallback to Latin Modern Sans (ships with
%% every TeX Live install) so the class compiles without system fonts.
\IfFontExistsTF{Helvetica Neue}{%
  \setmainfont{Helvetica Neue}[
    UprightFont    = *,
    BoldFont       = * Bold,
    ItalicFont     = * Italic,
    BoldItalicFont = * Bold Italic,
  ]%
}{%
  \setmainfont{Latin Modern Sans}%
}
\IfFontExistsTF{Menlo}{%
  \setmonofont{Menlo}[Scale=0.85]%
}{%
  \setmonofont{Latin Modern Mono}[Scale=0.85]%
}

%% ─── Layout ──────────────────────────────────────────────────────────────────
%% The geometry package honors the class-level landscape option (set by the
%% template from the brief's `orientation: landscape` frontmatter key). The
%% landscape option, when set, is forwarded via \PassOptionsToPackage so the
%% geometry option list stays a plain comma-separated key=value sequence (an
%% inline \ifanvil@landscape ... \fi inside the option list expands awkwardly
%% during geometry's preprocessing). The geometry call carries `letterpaper`
%% explicitly so the paper dimensions are reset in the same pass that the
%% landscape orientation flag applies — without it, geometry's mode toggle
%% does not swap paperwidth/paperheight.
\ifanvil@landscape
  \PassOptionsToPackage{landscape}{geometry}
\fi
\RequirePackage[
  letterpaper,
  top=0.7in,
  bottom=0.8in,
  left=0.95in,
  right=0.95in,
]{geometry}
\RequirePackage{parskip}
\setlength{\parskip}{0.4em}
\RequirePackage{enumitem}
\setlist{nosep, leftmargin=1.5em, itemsep=2pt}

%% ─── Colors ──────────────────────────────────────────────────────────────────
\RequirePackage{xcolor}
\definecolor{ink}{HTML}{1A1A1F}        % near-black for body
\definecolor{accent}{HTML}{6B7280}     % neutral gray — default, overridden by template
\definecolor{muted}{HTML}{6B7280}      % gray for secondary text
\definecolor{bg}{HTML}{F5F7FA}         % cool light fill for callouts
\definecolor{rule}{HTML}{6B7280}

\color{ink}

%% ─── Headings ────────────────────────────────────────────────────────────────
\RequirePackage{titlesec}
\RequirePackage{needspace}

\titleformat{\section}
  {\needspace{6\baselineskip}\large\bfseries\color{accent}}
  {}
  {0em}
  {}
  [\vspace{-0.4em}{\color{rule}\rule{\textwidth}{1.0pt}}\vspace{0.1em}]

\titleformat{\subsection}
  {\normalsize\bfseries\color{ink}}
  {}
  {0em}
  {}

\titlespacing*{\section}{0pt}{1.0em}{0.3em}
\titlespacing*{\subsection}{0pt}{0.6em}{0.15em}

%% ─── Tables ──────────────────────────────────────────────────────────────────
\RequirePackage{booktabs}
\RequirePackage{tabularx}
\RequirePackage{array}
\renewcommand{\arraystretch}{1.3}

%% ─── Callout + metricbox ─────────────────────────────────────────────────────
\RequirePackage{tcolorbox}
\tcbuselibrary{skins, breakable}

%% callout — left accent border; used for the Premise / key framing.
\newtcolorbox{callout}[1][]{%
  enhanced,
  breakable,
  colback=bg,
  colframe=bg,
  boxrule=0pt,
  borderline west={3pt}{0pt}{accent},
  sharp corners,
  left=12pt, right=12pt, top=8pt, bottom=8pt,
  fonttitle=\bfseries\color{accent},
  coltitle=accent,
  attach boxed title to top left={yshift=-2mm, xshift=4mm},
  boxed title style={colback=bg, colframe=bg, boxrule=0pt, sharp corners},
  #1
}

%% metricbox — breakable borderless bg fill; used for spec/budget/throughput tables.
%% breakable added (vs. anvil-installation.cls) so multi-page metric tables
%% don't overflow into the margin on the first occurrence.
\newtcolorbox{metricbox}{%
  enhanced,
  breakable,
  colback=bg,
  colframe=bg,
  boxrule=0pt,
  sharp corners,
  left=12pt, right=12pt, top=6pt, bottom=6pt,
}

%% ─── Header / Footer ─────────────────────────────────────────────────────────
\RequirePackage{fancyhdr}
\RequirePackage{lastpage}
%% Studio name and document type for the footer; set via \anvildocstudio and
%% \anvildoctype, defaulting sensibly.
\newcommand{\anvil@studio}{Studio}
\newcommand{\anvil@doctype}{Document}
\newcommand{\anvildocstudio}[1]{\renewcommand{\anvil@studio}{#1}}
\newcommand{\anvildoctype}[1]{\renewcommand{\anvil@doctype}{#1}}
\pagestyle{fancy}
\fancyhf{}
\renewcommand{\headrulewidth}{0pt}
\fancyfoot[L]{\footnotesize\color{muted}\anvil@studio\ --- \anvil@doctype}
\fancyfoot[R]{\footnotesize\color{muted}\thepage\ / \pageref{LastPage}}

%% ─── Hyperlinks ──────────────────────────────────────────────────────────────
\RequirePackage[hidelinks]{hyperref}
\hypersetup{colorlinks=true, linkcolor=accent, urlcolor=accent}

%% ─── Graphics ────────────────────────────────────────────────────────────────
\RequirePackage{graphicx}
\RequirePackage{microtype}

%% ─── Math support ────────────────────────────────────────────────────────────
%% pandoc emits amsmath-only commands when converting markdown math, most
%% commonly \text{} (subscripts like $B_{\text{eff}}$, units, multi-letter
%% labels). amsmath defines \text{} (via amstext); amssymb covers the broader
%% symbol set pandoc can emit (\mathbb, \lesssim, \nleq, …). This is the shared
%% pdf_output: true path (anvil/lib/latex_render.py), so every PDF-emitting
%% skill inherits this fix. Without these loads any \text{}-in-math body fails
%% to render with ``Undefined control sequence'' (xelatex exit 43). See issue
%% #592. amssymb loads after amsmath (standard ordering; no conflict).
\RequirePackage{amsmath}
\RequirePackage{amssymb}

%% ─── Title-block metadata + renderer ─────────────────────────────────────────
%% etoolbox supplies \ifdefempty for the empty-subtitle/hero guards below.
%% Already loaded transitively by tcolorbox; the explicit load is idempotent
%% and self-documenting. The expansion-based \ifdefempty replaces the legacy
%% \ifx-against-\empty idiom, which silently depends on prefix equality:
%% \ifx is false whenever the operands differ in \long/\protected status, so
%% it breaks if the initialization ever becomes \long (e.g. older kernels'
%% \newcommand, or a future \NewDocumentCommand refactor). See issue #422.
\RequirePackage{etoolbox}
\newcommand{\anvil@title}{Document Title}
\newcommand{\anvil@subtitle}{}
\newcommand{\anvil@date}{\today}
\newcommand{\anvil@stage}{DOCUMENT --- DRAFT STAGE}
\newcommand{\anvildoctitle}[1]{\renewcommand{\anvil@title}{#1}}
\newcommand{\anvildocsubtitle}[1]{\renewcommand{\anvil@subtitle}{#1}}
\newcommand{\anvildocdate}[1]{\renewcommand{\anvil@date}{#1}}
\newcommand{\anvildocstage}[1]{\renewcommand{\anvil@stage}{#1}}

%% \maketitleblock — renders the studio kicker, title, subtitle, accent rule,
%% and the date/stage line.
\newcommand{\maketitleblock}{%
  \thispagestyle{empty}%
  \begin{flushleft}%
    {\color{muted}\footnotesize\textsf{\MakeUppercase{\anvil@studio}}}\\[0.8em]%
    {\fontsize{26}{30}\selectfont\bfseries\color{ink}\anvil@title}\\[0.3em]%
    \ifdefempty{\anvil@subtitle}{}{%
      {\large\color{muted}\itshape\anvil@subtitle}\\[0.7em]%
    }%
    {\color{rule}\rule{\textwidth}{2pt}}\\[0.2em]%
    {\footnotesize\color{muted}\anvil@date \hfill \anvil@stage}%
  \end{flushleft}%
  \vspace{0.4em}%
}

%% \herofigure{path} — full-width hero image. No-op when the argument is empty
%% (so a brief without a hero render still compiles).
\newcommand{\herofigure}[1]{%
  \def\anvil@hero{#1}%
  \ifdefempty{\anvil@hero}{}{%
    \begin{figure}[h]\centering
      \includegraphics[width=0.92\textwidth]{#1}%
    \end{figure}%
    \vspace{-0.6em}%
  }%
}

%% \coda{text} — closing accent rule + italic muted coda line.
\newcommand{\coda}[1]{%
  \vfill
  {\color{rule}\rule{\textwidth}{1pt}}\\[0.2em]%
  {\footnotesize\itshape\color{muted}#1}%
}

\endinput
