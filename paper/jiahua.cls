%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Jiahua's latex styles.
% 
% Usage: 
% \documentclass[letterpaper, anon, colorful]{jiahua}
% 
% Mainly used for homework and class notes. 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{jiahua}[2022/01/31 Jiahua's Template]

%%%%%%%%%%%%%%%%%%%%%%%%%%%% options %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\newif\ifanon
\anonfalse
\DeclareOption{anon}{\anontrue}

% This doesn't work yet. 
\newif\ifcolorful
\colorfulfalse
\DeclareOption{colorful}{\colorfultrue}

% Hides date in top left header
\newif\ifnodate
\nodatefalse
\DeclareOption{nodate}{\nodatetrue}

% Section numbering
\newif\ifrawnumbering
\rawnumberingtrue
\newif\ifsectionnumbering
\sectionnumberingfalse
\DeclareOption{sections}{
    \sectionnumberingtrue
    \subsectionnumberingfalse
    \rawnumberingfalse
}
\newif\ifsubsectionnumbering
\subsectionnumberingfalse
\DeclareOption{subsections}{
    \sectionnumberingfalse
    \subsectionnumberingtrue
    \rawnumberingfalse
}

\DeclareOption*{\PassOptionsToClass{\CurrentOption}{article}}
\ProcessOptions\relax

%%%%%%%%%%%%%%%%%%%%%%%%%%%% preamble %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Base class, uses KOMA-Script. 
\LoadClass[oneside]{scrbook}

% book fixes
\counterwithout{section}{chapter}
\counterwithout{figure}{chapter}


% Language
\RequirePackage[english]{babel}
\RequirePackage[T1]{fontenc}
\RequirePackage{microtype}

% Math
\RequirePackage{amsmath}
\RequirePackage{amsfonts}
\RequirePackage{amssymb}
\RequirePackage{amsthm}
\RequirePackage{thmtools}

% Metadata
\RequirePackage{titling}
\setlength{\droptitle}{-2cm}
\pretitle{\begin{center}\sffamily\bfseries\LARGE}
\preauthor{\begin{center}
    \large\sffamily \lineskip 0.5em%
    \begin{tabular}[t]{c}}
\predate{\begin{center}\sffamily\large}
% \newenvironment{abstract}{}{}
% \RequirePackage{abstract}
% \renewcommand\abstractnamefont{\sffamily}

\ifanon
    \author{}
\else
    \author{Jiahua Chen}
\fi
\date{\today}

% Fix titling
\let\settitle\title
\renewcommand{\title}[1]{%
    \settitle{#1}%
    \newcommand{\headertitle}{#1}%
}

% Loads colors
\RequirePackage[dvipsnames,svgnames,x11names,table,xcdraw]{xcolor}
\newcommand{\accentcolor}{\color{violet}}

% Format
\RequirePackage{geometry}
\geometry{
    left=1in,
    right=1in,
    top=1in,
    bottom=1in,
    headsep=0mm,
}

% For header
\@ifundefined{KOMAClassName}
{
    \RequirePackage{fancyhdr}
    \setlength{\headheight}{0.75in}
    \setlength{\oddsidemargin}{0in}
    \setlength{\evensidemargin}{0in}
    \setlength{\voffset}{-1.0in}
    \setlength{\headsep}{10pt}
    \setlength{\textwidth}{6.5in}
    \setlength{\headwidth}{6.5in}
    \setlength{\textheight}{8.75in}
    \setlength{\parskip}{1ex plus 0.5ex minus 0.2ex}
    \setlength{\footskip}{0.3in}
}
{
    \RequirePackage[]{scrlayer-scrpage}
    \renewcommand{\headfont}{}
    \setlength{\footskip}{0.5in}
    % \setlength{\headsep}{10pt}
    % \ifnodate
    %     \ihead{\footnotesize\textbf{\theauthor}}
    % \else
    %     \ihead{\footnotesize\textbf{\theauthor} (\thedate)}
    % \fi
    % \automark{section}
    \ihead{}
    \chead{}
    \ohead{}
    \cfoot{\pagemark}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%% packages %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% For tables
\RequirePackage{booktabs}
\renewcommand{\arraystretch}{1.05}
\RequirePackage{longtable}
\RequirePackage{threeparttable}

% For links
\RequirePackage[
    colorlinks = true,
    linkcolor = Blue,
    urlcolor  = Blue,
    citecolor = Blue,
    anchorcolor = Blue]{hyperref}
\RequirePackage[noabbrev,nameinlink]{cleveref}

% Underlining
\RequirePackage{soul}

% Graphs
\RequirePackage{tikz}

% Better enumerations
\RequirePackage{enumerate}

% Mathy stuff
\RequirePackage{mathrsfs}
\RequirePackage{textcomp}
\RequirePackage{multirow}
\RequirePackage{mathtools}
\RequirePackage{microtype}
\RequirePackage{stmaryrd}

% Listings (code)
\RequirePackage{listings}
\lstset{
    basicstyle=\small\sffamily,
    numbers=left,
    numberstyle=\tiny,
    frame=tb,
    columns=fullflexible,
    showstringspaces=false
}

\RequirePackage{fontawesome}

%%%%%%%%%%%%%%%%%%%%%%%%%%%% environments %%%%%%%%%%%%%%%%%%%%%%%%%%%%
\ifcolorful
    \RequirePackage[framemethod=TikZ]{mdframed}
    \mdfdefinestyle{mdbluebox}{%
        roundcorner = 10pt,
        linewidth=1pt,
        skipabove=12pt,
        innerbottommargin=9pt,
        skipbelow=2pt,
        linecolor=blue,
        nobreak=true,% Page breaking
        backgroundcolor=TealBlue!5,
    }
    \declaretheoremstyle[
        headfont=\sffamily\bfseries\color{MidnightBlue},
        mdframed={style=mdbluebox},
        headpunct={\\[3pt]},
        postheadspace={0pt}
    ]{thmbluebox}
    \mdfdefinestyle{mdredbox}{%
        linewidth=0.5pt,
        skipabove=12pt,
        frametitleaboveskip=5pt,
        frametitlebelowskip=0pt,
        skipbelow=2pt,
        frametitlefont=\bfseries,
        innertopmargin=4pt,
        innerbottommargin=8pt,
        nobreak=true,%Page breaking
        backgroundcolor=Salmon!5,
        linecolor=RawSienna,
    }
    \declaretheoremstyle[
        headfont=\bfseries\color{RawSienna},
        mdframed={style=mdredbox},
        headpunct={\\[3pt]},
        postheadspace={0pt},
    ]{thmredbox}
    \mdfdefinestyle{mdredboxbreakable}{%
        linewidth=0.5pt,
        skipabove=12pt,
        frametitleaboveskip=5pt,
        frametitlebelowskip=0pt,
        skipbelow=2pt,
        frametitlefont=\bfseries,
        innertopmargin=4pt,
        innerbottommargin=8pt,
        nobreak=false,%Page breaking
        backgroundcolor=CarnationPink!5,
        linecolor=Fuchsia,
    }
    \declaretheoremstyle[
        headfont=\bfseries\color{Fuchsia},
        mdframed={style=mdredboxbreakable},
        headpunct={\\[3pt]},
        postheadspace={0pt},
    ]{thmredboxexample}
    \mdfdefinestyle{mdgreenbox}{%
        skipabove=8pt,
        linewidth=2pt,
        rightline=false,
        leftline=true,
        topline=false,
        bottomline=false,
        linecolor=ForestGreen,
        backgroundcolor=ForestGreen!5,
    }
    \declaretheoremstyle[
        headfont=\bfseries\sffamily\color{ForestGreen!70!black},
        bodyfont=\normalfont,
        spaceabove=2pt,
        spacebelow=1pt,
        mdframed={style=mdgreenbox},
        headpunct={ --- },
    ]{thmgreenbox}
    \mdfdefinestyle{mdblackbox}{%
        skipabove=8pt,
        linewidth=3pt,
        rightline=false,
        leftline=true,
        topline=false,
        bottomline=false,
        linecolor=black,
        backgroundcolor=RedViolet!5!gray!5,
    }
    \declaretheoremstyle[
        headfont=\bfseries,
        bodyfont=\normalfont\small,
        spaceabove=0pt,
        spacebelow=0pt,
        mdframed={style=mdblackbox}
    ]{thmblackbox}
    \newcommand{\listhack}{$\empty$\vspace{-2em}}
\fi

\theoremstyle{definition}
\ifcolorful
    \ifsectionnumbering
        \declaretheorem[%
            style=thmredbox,name=Theorem,numberwithin=section]{theorem}
    \fi
	\ifsubsectionnumbering
		\declaretheorem[%
			style=thmredbox,name=Theorem,numberwithin=subsection]{theorem}
	\fi
	\ifrawnumbering
		\declaretheorem[%
			style=thmredbox,name=Theorem]{theorem}
    \fi
    \declaretheorem[style=thmredbox,name=Lemma,sibling=theorem]{lemma}
    \declaretheorem[style=thmredbox,name=Proposition,sibling=theorem]{proposition}
    \declaretheorem[style=thmredbox,name=Corollary,sibling=theorem]{corollary}
    \declaretheorem[style=thmredbox,name=Theorem,numbered=no]{theorem*}
    \declaretheorem[style=thmredbox,name=Lemma,numbered=no]{lemma*}
    \declaretheorem[style=thmredbox,name=Proposition,numbered=no]{proposition*}
    \declaretheorem[style=thmredbox,name=Corollary,numbered=no]{corollary*}
\else
    \ifsectionnumbering
        \declaretheorem[name=Theorem,numberwithin=section]{theorem}
    \else
        \declaretheorem[name=Theorem]{theorem}
    \fi
    \declaretheorem[name=Lemma,sibling=theorem]{lemma}
    \declaretheorem[name=Proposition,sibling=theorem]{proposition}
    \declaretheorem[name=Corollary,sibling=theorem]{corollary}
    \declaretheorem[name=Theorem,numbered=no]{theorem*}
    \declaretheorem[name=Lemma,numbered=no]{lemma*}
    \declaretheorem[name=Proposition,numbered=no]{proposition*}
    \declaretheorem[name=Corollary,numbered=no]{corollary*}
\fi
\ifcolorful
    \declaretheorem[style=thmgreenbox,name=Algorithm,sibling=theorem]{algorithm}
    \declaretheorem[style=thmgreenbox,name=Algorithm,numbered=no]{algorithm*}
    \declaretheorem[style=thmgreenbox,name=Claim,sibling=theorem]{claim}
    \declaretheorem[style=thmgreenbox,name=Claim,numbered=no]{claim*}
    \declaretheorem[style=thmgreenbox,name=Fact,sibling=theorem]{fct}
    \declaretheorem[style=thmgreenbox,name=Fact,numbered=no]{fct*}
\else
    \declaretheorem[name=Algorithm,sibling=theorem]{algorithm}
    \declaretheorem[name=Algorithm,numbered=no]{algorithm*}
    \declaretheorem[name=Claim,sibling=theorem]{claim}
    \declaretheorem[name=Claim,numbered=no]{claim*}
    \declaretheorem[name=Fact,sibling=theorem]{fct}
    \declaretheorem[name=Fact,numbered=no]{fct*}
\fi
\ifcolorful
    \declaretheorem[style=thmredboxexample,name=Example,sibling=theorem]{example}
    \declaretheorem[style=thmredboxexample,name=Example,numbered=no]{example*}
\else
    \declaretheorem[name=Example,sibling=theorem]{example}
    \declaretheorem[name=Example,numbered=no]{example*}
\fi
% Remark-style theorems
\ifcolorful
    \declaretheorem[style=thmblackbox,name=Remark,sibling=theorem]{remark}
    \declaretheorem[style=thmblackbox,name=Remark,numbered=no]{remark*}
\else
    \declaretheorem[name=Remark,sibling=theorem]{remark}
    \declaretheorem[name=Remark,numbered=no]{remark*}
\fi
\ifcolorful
    \declaretheorem[style=thmredbox, name=Conjecture,sibling=theorem]{conjecture}
    \declaretheorem[style=thmredbox, name=Conjecture,numbered=no]{conjecture*}
\else
    \declaretheorem[name=Conjecture,sibling=theorem]{conjecture}
    \declaretheorem[name=Conjecture,numbered=no]{conjecture*}
\fi
\ifcolorful
    \declaretheorem[style=thmbluebox, name=Definition,sibling=theorem]{definition}
    \declaretheorem[style=thmbluebox, name=Definition,numbered=no]{definition*}
\else
    \declaretheorem[name=Definition,sibling=theorem]{definition}
    \declaretheorem[name=Definition,numbered=no]{definition*}
\fi

\declaretheorem[name=Exercise,sibling=theorem]{exercise}
\declaretheorem[name=Exercise,numbered=no]{exercise*}
\declaretheorem[name=Fact,sibling=theorem]{fact}
\declaretheorem[name=Fact,numbered=no]{fact*}
\declaretheorem[name=Problem,sibling=theorem]{problem}
\declaretheorem[name=Problem,numbered=no]{problem*}
\declaretheorem[name=Question,sibling=theorem]{ques}
\declaretheorem[name=Question,numbered=no]{ques*}
\Crefname{claim}{Claim}{Claims}
\Crefname{fact}{Fact}{Facts}
\Crefname{conjecture}{Conjecture}{Conjectures}
\Crefname{exercise}{Exercise}{Exercises}
\Crefname{fact}{Fact}{Facts}
\Crefname{problem}{Problem}{Problems}
\Crefname{ques}{Question}{Questions}

% Fancy section and chapter heads
\ifcolorful
    \@ifundefined{KOMAClassName}{}{
        \@ifundefined{chapter}{}{
            \addtokomafont{partprefix}{\rmfamily}
            \renewcommand*{\partformat}{\accentcolor
                \scalebox{2.5}{\thepart}\enlargethispage{2em}}
            \addtokomafont{chapterprefix}{\raggedleft}
            \RedeclareSectionCommand[beforeskip=0.5em]{chapter}
            \renewcommand*{\chapterformat}{\mbox{%
                    \scalebox{1.5}{\chapappifchapterprefix{\nobreakspace}}%
                    \scalebox{2.718}{\accentcolor\thechapter}\enskip}}
        }
        \renewcommand*{\sectionformat}%
        {\accentcolor\S\thesection\enskip}
        \renewcommand*{\subsectionformat}%
        {\accentcolor\S\thesubsection\enskip}
        \renewcommand*{\subsubsectionformat}%
        {\accentcolor\S\thesubsubsection\enskip}
        \KOMAoptions{numbers=noenddot}
    }
\fi

\RequirePackage[textsize=tiny, textwidth=18mm]{todonotes}
\setuptodonotes{color=green!20}
\RequirePackage{cancel}
\usetikzlibrary{cd}
\usetikzlibrary{arrows.meta, calc, chains, positioning, quotes, shapes.multipart}
\newcommand\ppbb{path picture bounding box}
\numberwithin{equation}{section}

\setmonofont[
  Path = ./fonts/,
  Extension = .ttf,
  Ligatures=TeX,
  Numbers=,
  Scale=1,
  WordSpace={1,0,0},
  PunctuationSpace=WordSpace,
  UprightFont=*,
  ItalicFont=*-Oblique,
  BoldFont=*-Bold,
  BoldItalicFont=*-BoldOblique
]{DejaVuSansMono}

\setsansfont[
  Path = ./fonts/,
  Extension = .otf,
  UprightFont=*,
  ItalicFont=*-Italic,
  BoldFont=*-Semibold,
  BoldItalicFont=*-SemiboldItalic
]{SolitaireMVBPro}

\RequirePackage{letltxmacro}
% https://tex.stackexchange.com/q/88001/5764
\LetLtxMacro\oldttfamily\ttfamily
\DeclareRobustCommand{\ttfamily}{\oldttfamily\csname ttsize\endcsname}
\newcommand{\setttsize}[1]{\def\ttsize{#1}}%
\setttsize{\scriptsize}

% Source code with highlighting
\RequirePackage{minted}
\setminted{baselinestretch=1.1}
\usemintedstyle{autumn}

\RequirePackage{tcolorbox}
\tcbuselibrary{listings, minted, skins, breakable, hooks}

\tcbset{listing engine=minted}

% tcb listings for languages

\colorlet{forgelistingcolor}{MistyRose}
\colorlet{leanimpllistingcolor}{WhiteSmoke}
\colorlet{leanlistingcolor}{AliceBlue}

\newtcblisting{forge}{listing only, minted language=alloy, minted style=autumn,
    colback=forgelistingcolor, enhanced, frame hidden, top=4pt, bottom=4pt, left=4pt, right=4pt, breakable, 
    minted options={fontsize=\footnotesize, tabsize=2, autogobble, linenos}}

\newtcblisting{forge*}{listing only, minted language=alloy, minted style=autumn,
    colback=forgelistingcolor, enhanced, frame hidden, top=4pt, bottom=4pt, left=4pt, right=4pt, breakable, 
    minted options={fontsize=\footnotesize, tabsize=2, autogobble}}

\newtcblisting{leanimpl}{listing only, minted language=lean, minted style=autumn,
    colback=leanimpllistingcolor, enhanced, frame hidden, top=4pt, bottom=4pt, left=4pt, right=4pt, breakable, 
    minted options={fontsize=\footnotesize, tabsize=2, breaklines, autogobble, linenos, escapeinside=!!, texcomments}}

\newtcblisting{leanimpl*}{listing only, minted language=lean, minted style=autumn,
    colback=leanimpllistingcolor, enhanced, frame hidden, top=4pt, bottom=4pt, left=4pt, right=4pt, breakable, 
    minted options={fontsize=\footnotesize, tabsize=2, breaklines, autogobble, escapeinside=!!, texcomments}}

\newtcblisting{lean}{listing only, minted language=lean, minted style=autumn,
    colback=leanlistingcolor, enhanced, frame hidden, top=4pt, bottom=4pt, left=4pt, right=4pt, breakable, 
    minted options={fontsize=\footnotesize, tabsize=2, autogobble, linenos, escapeinside=??, texcomments}}

\newtcblisting{lean*}{listing only, minted language=lean, minted style=autumn,
    colback=leanlistingcolor, enhanced, frame hidden, top=4pt, bottom=4pt, left=4pt, right=4pt, breakable, 
    minted options={fontsize=\footnotesize, tabsize=2, autogobble, escapeinside=??, texcomments}}

% suppress ending paragraph after tcb
% https://tex.stackexchange.com/questions/568782/allowing-paragraph-continuation-after-a-tcolorbox
\makeatletter
\tcbset{
    after app={%
    \ifx\tcb@drawcolorbox\tcb@drawcolorbox@breakable
    \else
        % add only when not breakabel
        \@endparenv
    \fi
    }
}

% for breakable
\appto\tcb@use@after@lastbox{\@endparenv\@doendpe}
\makeatother

\RequirePackage{multicol}

\RequirePackage[all,cmtip]{xy}

\linespread{1.2}

% syntax
\RequirePackage{syntax}

\RequirePackage{metalogo}

% Bibliography
\RequirePackage{csquotes,xpatch}
\RequirePackage[backend=biber,style=numeric]{biblatex}
\addbibresource{bibliographies/google-scholar.bib}
\addbibresource{bibliographies/additional.bib}

% Table of Contents
\BeforeTOCHead[toc]{%
  \KOMAoptions{parskip=false}% no parskip in ToC
  \RedeclareSectionCommand[afterskip=1sp minus 1sp]{section}% no skip after ToC title
}\DeclareTOCStyleEntry[beforeskip=0.3em, entryformat=\bfseries]{section}{section}

% fcolorboxes
\renewcommand\fbox{\fcolorbox{lightgray}{white}}
\setlength{\fboxsep}{0pt}

% Typesetting (widows and orphans)
\RequirePackage[all]{nowidow}

\RequirePackage{caption}
\captionsetup[table]{labelsep=space}
\captionsetup[figure]{labelsep=space}

%%%%%%%%%%%%%%%%%%%%%%%%%%%% macros %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\newcommand{\recall}{\textit{Recall:} }

% Sets of numbers
\newcommand{\CC}{\mathbb C}
\newcommand{\FF}{\mathbb F}
\newcommand{\NN}{\mathbb N}
\newcommand{\QQ}{\mathbb Q}
\newcommand{\RR}{\mathbb R}
\newcommand{\ZZ}{\mathbb Z}

% For Math1530
\DeclareMathOperator{\im}{im}

% From Math1560
\DeclareMathOperator{\ord}{ord}
\DeclareMathOperator{\id}{id}
\newcommand{\lege}[2]{\left(\dfrac{#1}{#2}\right)}
\newcommand{\otoh}{\textsc{otoh}}
\DeclareMathOperator{\minpoly}{\mathsf{minpoly}}
\DeclareMathOperator{\disc}{\mathsf{disc}}
\DeclareMathOperator{\Disc}{\mathsf{Disc}}
\newcommand{\QQbar}{\overline{\QQ}}
\newcommand{\ZZbar}{\overline{\ZZ}}
\newcommand{\riO}{\mathcal{O}}
\newcommand{\frk}[1]{\mathfrak{#1}}
\DeclareMathOperator{\Vol}{\mathsf{Vol}}

\newcommand{\bvec}[1]{\vec{\mathbf{#1}}}

\DeclareMathOperator{\E}{\mathsf{E}}
\DeclareMathOperator{\Var}{\mathsf{Var}}
\DeclareMathOperator{\Cov}{\mathrm{Cov}}
\DeclareMathOperator{\diam}{\mathrm{diam}}

\newcommand{\cN}{\mathcal N}

