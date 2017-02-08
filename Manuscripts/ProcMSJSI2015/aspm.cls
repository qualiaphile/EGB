\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{aspm}[2009/01/13 v.1.0c]

\LoadClassWithOptions{amsproc}

\newif\ifdraft \draftfalse
\newbox\@OnePage
\newif\if@Spread \@Spreadfalse
\newif\if@NoShipout
\newif\if@tombow
\newif\if@TextFrame
\newif\if@AdjustLines
\newif\if@BoldTitles
\newif\if@CenterPut% 2009/01/13
\newif\if@HeaderInfo \@HeaderInfotrue% 2009/01/13

%%%%
\begingroup
\nfss@catcodes
\edef\@scale@font{[1]}
\DeclareFontFamily{OT1}{cmr}{\hyphenchar\font=45}
\DeclareFontShape{OT1}{cmr}{m}{n}{
        <-6>    s * \@scale@font cmr5
        <6-7>   s * \@scale@font cmr6
        <7-8>   s * \@scale@font cmr7
        <8-12>  s * \@scale@font cmr10
        <12-17> s * \@scale@font cmr12
        <17->   s * \@scale@font cmr17
      }{}
\DeclareFontShape{OT1}{cmr}{m}{sl}{
        <-8>    s * \@scale@font cmsl8
        <8-12>  s * \@scale@font cmsl10
        <12->   s * \@scale@font cmsl12
        }{}
\DeclareFontShape{OT1}{cmr}{m}{it}{
        <-8>    s * \@scale@font cmti7
        <8-12>  s * \@scale@font cmti10
        <12->   s * \@scale@font cmti12
      }{}
\DeclareFontShape{OT1}{cmr}{m}{sc}{
        <-8> s * \@scale@font cmcsc9
        <8-> s * \@scale@font cmcsc10
      }{}
\DeclareFontShape{OT1}{cmr}{m}{ui}{
        <->  s * \@scale@font cmu10
      }{}
\DeclareFontShape{OT1}{cmr}{b}{n}{
        <->  s * \@scale@font cmb10
      }{}
\DeclareFontShape{OT1}{cmr}{bx}{n}{
        <-6>    s * \@scale@font cmbx5
        <6-7>   s * \@scale@font cmbx6
        <7-8>   s * \@scale@font cmbx7
        <8-12>  s * \@scale@font cmbx10
        <12->   s * \@scale@font cmbx12
        }{}
\DeclareFontShape{OT1}{cmr}{bx}{sl}{
        <->     s * \@scale@font cmbxsl10
      }{}
\DeclareFontShape{OT1}{cmr}{bx}{it}{
        <->     s * \@scale@font cmbxti10
      }{}
\DeclareFontShape{OT1}{cmr}{bx}{ui}
      {<->ssub * cmr/m/ui}{}
\DeclareFontFamily{OT1}{cmss}{\hyphenchar\font=45}
\DeclareFontShape{OT1}{cmss}{m}{n}{
        <-8>    s * \@scale@font cmss8
        <8-12>  s * \@scale@font cmss10
        <12-17> s * \@scale@font cmss12
        <17->   s * \@scale@font cmss17
      }{}
\DeclareFontShape{OT1}{cmss}{m}{it}
      {<->ssub*cmss/m/sl}{}
\DeclareFontShape{OT1}{cmss}{m}{sl}{
        <-8>    s * \@scale@font cmssi8
        <8-12>  s * \@scale@font cmssi10
        <12-17> s * \@scale@font cmssi12
        <17->   s * \@scale@font cmssi17
      }{}
\DeclareFontShape{OT1}{cmss}{m}{sc}
       {<->ssub*cmr/m/sc}{}
\DeclareFontShape{OT1}{cmss}{m}{ui}
       {<->ssub*cmr/m/ui}{}
\DeclareFontShape{OT1}{cmss}{sbc}{n}{
        <->   s * \@scale@font cmssdc10
       }{}
\DeclareFontShape{OT1}{cmss}{bx}{n}{
        <->   s * \@scale@font cmssbx10
      }{}
\DeclareFontShape{OT1}{cmss}{bx}{ui}
       {<->ssub*cmr/bx/ui}{}
\DeclareFontFamily{OT1}{cmtt}{\hyphenchar \font\m@ne}
\DeclareFontShape{OT1}{cmtt}{m}{n}{
        <-8>    s * \@scale@font cmtt8
        <8-12>  s * \@scale@font cmtt9
        <12->   s * \@scale@font cmtt12
      }{}
\DeclareFontShape{OT1}{cmtt}{m}{it}{
        <->     s * \@scale@font cmitt10
      }{}
\DeclareFontShape{OT1}{cmtt}{m}{sl}{
        <->     s * \@scale@font cmsltt10
      }{}
\DeclareFontShape{OT1}{cmtt}{m}{sc}{
        <->     s * \@scale@font cmtcsc10
      }{}
\DeclareFontShape{OT1}{cmtt}{m}{ui}
  {<->ssub * cmtt/m/it}{}
\DeclareFontShape{OT1}{cmtt}{bx}{n}
  {<->ssub * cmtt/m/n}{}
\DeclareFontShape{OT1}{cmtt}{bx}{it}
  {<->ssub * cmtt/m/it}{}
\DeclareFontShape{OT1}{cmtt}{bx}{ui}
  {<->ssub * cmtt/m/it}{}
\DeclareFontFamily{OT1}{cmfr}{\hyphenchar\font=45}
\DeclareFontShape{OT1}{cmfr}{m}{n}{%
        <->   s *  \@scale@font cmff10
    }{}
\DeclareFontShape{OT1}{cmfr}{m}{it}{
        <->   s *  \@scale@font cmfi10
    }{}
\DeclareFontFamily{OT1}{cmdh}{\hypenchar\font=45}
\DeclareFontShape{OT1}{cmdh}{m}{n}{
        <->   s * \@scale@font cmdunh10
    }{}
\DeclareFontFamily{OT1}{cmfib}{\hyphenchar\font=45}
\DeclareFontShape{OT1}{cmfib}{m}{n}{
        <->   s * \@scale@font cmfib8
    }{}
\DeclareFontFamily{OML}{cmm}{\skewchar\font127 }
\DeclareFontShape{OML}{cmm}{m}{it}{
        <-6>   s * \@scale@font cmmi5
        <6-7>  s * \@scale@font cmmi6
        <7-8>  s * \@scale@font cmmi7
        <8-12>  s * \@scale@font cmmi10
        <12->   s * \@scale@font cmmi12
      }{}
\DeclareFontShape{OML}{cmm}{b}{it}{%
        <-7>   s * \@scale@font cmmib5
        <7-8>  s * \@scale@font cmmib7
        <8->   s * \@scale@font cmmib10
      }{}
\DeclareFontShape{OML}{cmm}{bx}{it}
   {<-> ssub * cmm/b/it}{}
\DeclareFontFamily{OML}{cmr}{\skewchar\font127 }
\DeclareFontShape{OML}{cmr}{m}{n}
   {<-> ssub * cmm/m/it}{}
\DeclareFontShape{OML}{cmr}{m}{it}
   {<-> ssub * cmm/m/it}{}
\DeclareFontShape{OML}{cmr}{m}{sl}
   {<-> ssub * cmm/m/it}{}
\DeclareFontShape{OML}{cmr}{m}{sc}
   {<-> ssub * cmm/m/it}{}
\DeclareFontShape{OML}{cmr}{bx}{n}
   {<-> ssub * cmm/b/it}{}
\DeclareFontShape{OML}{cmr}{bx}{it}
   {<-> ssub * cmm/b/it}{}
\DeclareFontShape{OML}{cmr}{bx}{sl}
   {<-> ssub * cmm/b/it}{}
\DeclareFontShape{OML}{cmr}{bx}{sc}
   {<-> ssub * cmm/b/it}{}
\DeclareFontFamily{OMS}{cmsy}{\skewchar\font48 }
\DeclareFontShape{OMS}{cmsy}{m}{n}{%
        <-6>   s * \@scale@font cmsy5
        <6-7>  s * \@scale@font cmsy6
        <7-8>  s * \@scale@font cmsy7
        <8->  s * \@scale@font cmsy10
      }{}
\DeclareFontShape{OMS}{cmsy}{b}{n}{%
        <-7>   s * \@scale@font cmbsy5
        <7-8>  s * \@scale@font cmbsy7
        <8->   s * \@scale@font cmbsy10
      }{}
\DeclareFontFamily{OMS}{cmr}{\skewchar\font48 }
\DeclareFontShape{OMS}{cmr}{m}{n}
   {<-> ssub * cmsy/m/n}{}
\DeclareFontShape{OMS}{cmr}{m}{it}
   {<-> ssub * cmsy/m/n}{}
\DeclareFontShape{OMS}{cmr}{m}{sl}
   {<-> ssub * cmsy/m/n}{}
\DeclareFontShape{OMS}{cmr}{m}{sc}
   {<-> ssub * cmsy/m/n}{}
\DeclareFontShape{OMS}{cmr}{bx}{n}
   {<-> ssub * cmsy/b/n}{}
\DeclareFontShape{OMS}{cmr}{bx}{it}
   {<-> ssub * cmsy/b/n}{}
\DeclareFontShape{OMS}{cmr}{bx}{sl}
   {<-> ssub * cmsy/b/n}{}
\DeclareFontShape{OMS}{cmr}{bx}{sc}
   {<-> ssub * cmsy/b/n}{}
\DeclareFontFamily{OMX}{cmex}{}{}
\DeclareFontShape{OMX}{cmex}{m}{n}{
          <-> s *  \@scale@font cmex10
        }{}
\DeclareFontFamily{U}{lasy}{}
\DeclareFontShape{U}{lasy}{m}{n}{
        <-6>   s * \@scale@font lasy5
        <6-7>  s * \@scale@font lasy6
        <7-8>  s * \@scale@font lasy7
        <8->  s * \@scale@font lasy10
        }{}
\DeclareFontShape{U}{lasy}{b}{n}{
        <->    s * \@scale@font lasyb10
        }{}
\DeclareFontFamily{U}{msa}{}
\DeclareFontShape{U}{msa}{m}{n}{
          <-7>   s * \@scale@font msam5
          <7-8>  s * \@scale@font msam7
          <8->   s * \@scale@font  msam10
          }{}
\DeclareFontFamily{U}{msb}{}
\DeclareFontShape{U}{msb}{m}{n}{
          <-7>  s * \@scale@font msbm5
          <7-8> s * \@scale@font msbm7
          <8->  s * \@scale@font msbm10
          }{}
%%%
\DeclareFontFamily{U}{euex}{}
\DeclareFontShape{U}{euex}{m}{n}{
        <->   s * \@scale@font euex10 %
        }{}
\DeclareFontFamily{U}{euf}{}
\DeclareFontShape{U}{euf}{m}{n}{
        <-7>  s * \@scale@font eufm5
        <7-8> s * \@scale@font eufm7
        <8->  s * \@scale@font eufm10
         }{}
\DeclareFontShape{U}{euf}{b}{n}{
        <-7>  s * \@scale@font eufb5
        <7-8> s * \@scale@font eufb7
        <8->  s * \@scale@font eufb10
         }{}
\DeclareFontFamily{U}{eur}{\skewchar\font'177}
\DeclareFontShape{U}{eur}{m}{n}{
        <-7>   s * \@scale@font eurm5
        <7-8> s * \@scale@font eurm7
        <8->  s * \@scale@font eurm10
         }{}
\DeclareFontShape{U}{eur}{b}{n}{
        <-7>   s * \@scale@font eurb5
        <7-8>  s * \@scale@font eurb7
        <8->   s * \@scale@font eurb10
         }{}
\DeclareFontFamily{U}{eus}{\skewchar\font'60}
\DeclareFontShape{U}{eus}{m}{n}{
        <-7>  s * \@scale@font eusm5
        <7-8> s * \@scale@font eusm7
        <8->  s * \@scale@font eusm10
         }{}
\DeclareFontShape{U}{eus}{b}{n}{
        <-7>  s * \@scale@font eusb5
        <7-8> s * \@scale@font eusb7
        <8->  s * \@scale@font eusb10
         }{}
\endgroup

%%%%
\DeclareOption{tombow}{\@tombowtrue\@HeaderInfotrue}% 2009/01/13
\DeclareOption{notombow}{\@tombowfalse\@HeaderInfofalse}% 2009/01/13
\DeclareOption{spread}{\@Spreadtrue}
\DeclareOption{frame}{\@TextFrametrue}
\DeclareOption{draft}{\drafttrue \setlength\overfullrule{5pt}}
\DeclareOption{bftitles}{\@BoldTitlestrue}
\DeclareOption{center}{\@CenterPuttrue}% 2009/01/13

\ExecuteOptions{notombow}
\ProcessOptions

%%%%
\RequirePackage{color}

%%%%
\if@BoldTitles
\def\@BF{\bfseries\mathversion{bold}}
\else
\def\@BF{\bfseries}
\fi

%%%%
\setlength\paperheight{231mm}% 2007/02/28
\setlength\paperwidth {150mm}
\setlength\textwidth{312pt}
\setlength\textheight{504pt}

\setlength\topmargin{20mm}
\setbox\@tempboxa\hbox{\small(}\@tempdima=\ht\@tempboxa
\advance\@tempdima-10pt
\newdimen\TOPMARGIN@ \TOPMARGIN@\@tempdima
\addtolength{\topmargin}{\TOPMARGIN@}
\setlength\headheight{10pt}%
\setlength{\headsep}{16pt}
\setlength\topskip{10pt}
\normaltopskip\topskip

\setlength\evensidemargin{20mm}
\@tempdima=\paperwidth
\advance\@tempdima-\textwidth
\advance\@tempdima-\evensidemargin
\setlength\oddsidemargin{\@tempdima}

\setlength{\parindent}{18pt}

%%%%
\newskip\smallskipamountaspm
\smallskipamountaspm4\p@ plus1\p@ minus1\p@
\newskip\medskipamountaspm
\medskipamountaspm8\p@ plus2\p@ minus2\p@
\newskip\bigskipamountaspm
\bigskipamountaspm16\p@ plus4\p@ minus4\p@
\skip\footins\bigskipamountaspm
\def\@adjustvertspacing{%
  \bigskipamount.7\baselineskip plus.7\baselineskip
  \medskipamount\bigskipamount \divide\medskipamount\tw@
  \smallskipamount\medskipamount \divide\smallskipamount\tw@
  \jot\baselineskip \divide\jot 4 \relax
  \abovedisplayskip 9\p@ plus3\p@ minus3\p@
  \belowdisplayskip\abovedisplayskip
  \abovedisplayshortskip \z@ plus3\p@
  \belowdisplayshortskip 6\p@ plus3\p@ minus3\p@
}
\renewcommand\normalsize{\@xsetfontsize\normalsize 6%
  \@adjustvertspacing \let\@listi\@listI}

\if@AdjustLines
\renewcommand{\normalsize}{%
  \@setfontsize\normalsize{10pt}{12}%
  \lineskiplimit.1\baselineskip\lineskip=\lineskiplimit
  \topsep.5\baselineskip\parskip0mm\partopsep0mm
  \abovedisplayskip .5\baselineskip \@plus.05\baselineskip \@minus.05\baselineskip
  \abovedisplayshortskip .5\baselineskip \@plus.05\baselineskip \@minus.05\baselineskip
  \belowdisplayshortskip .5\baselineskip \@plus.05\baselineskip \@minus.05\baselineskip
  \belowdisplayskip \abovedisplayskip
  \bigskipamount\baselineskip
  \medskipamount\bigskipamount \divide\medskipamount\tw@
  \smallskipamount\medskipamount \divide\smallskipamount\tw@
  \jot=.2\baselineskip %% 
  \let\@listi\@listI}
\normalsize\raggedbottom
\fi

%%%%
\def\ps@headings{\ps@empty
  \def\@evenhead{\normalfont\small
      \rlap{\thepage}\hfil\@gridframe\hbox to\z@{\hss\leftmark{}{}\hss}\hfil}%
  \def\@oddhead{\normalfont\small\hfil\@gridframe%
      \hbox to\z@{\hss\rightmark{}{}\hss}\hfil\llap{\thepage}}%
  \let\@mkboth\markboth
}
\pagestyle{headings}

\def\ps@empty{%
  \def\@oddfoot{}%
  \let\@evenfoot\@oddfoot
  \def\@oddhead{\hss\@gridframe\hss}%
  \let\@evenhead\@oddhead}

%%%%
\def\@if@empty#1{%
  \def\reserved@e{#1}%
  \def\reserved@empty{}%
  \ifx\reserved@e\reserved@empty%
    \expandafter\@firstoftwo
  \else
    \expandafter\@secondoftwo
  \fi}

\newif\if@tempswt \@tempswtfalse
\newif\if@no@title \@no@titlefalse
\newif\if@no@volume \@no@volumefalse
\newif\if@no@year \@no@yearfalse
\newif\if@no@titlehead \@no@titleheadfalse

\def\notitlehead{\global\@no@titleheadtrue}

\def\articleinfo#1#2#3{%
  \@if@empty{#1}{\global\@no@titletrue}{\global\@no@titlefalse\gdef\BookTitle@ASPM{#1}}%
  \@if@empty{#2}{\global\@no@volumetrue}{\global\@no@volumefalse\gdef\Volume@ASPM{#2}}%
  \@if@empty{#3}{\global\@no@yeartrue}{\global\@no@yearfalse\gdef\Year@ASPM{#3}}%
}

\def\BookTitle@ASPM{{\it Title}}
\def\Volume@ASPM{{\it 99}}
\def\Year@ASPM{{\it 20XX}}

\newbox\@bookinfobox
\def\@bookinfohead{%
  {\parindent\z@\fboxsep\z@\fboxrule\z@\fbox{%
  \vbox{%
  \renewcommand{\baselinestretch}{1.05}\small%
  \if@no@title\if@no@volume\if@no@year\@tempswttrue\fi\fi\fi%
  \if@no@titlehead\@tempswttrue\fi%
  \if@tempswt
    \leavevmode\phantom{(}\\\phantom{)}\\\phantom{)}%
  \else
    Advanced Studies in Pure Mathematics \Volume@ASPM{}, \Year@ASPM\\
    \BookTitle@ASPM
    \\
    pp.~\thepage--\pageref{lastpage}%
  \fi\relax%
  \par}%
  }%
  }%
}

\def\enddoc@text{\ifx\@empty\@translators \else\@settranslators\fi
  \ifx\@empty\addresses \else\@setaddresses\fi\label{lastpage}}

%%%%
\def\@setaddresses{\par
  \nobreak \begingroup
\footnotesize
  \def\author##1{\nobreak\addvspace\bigskipamount}%
  \interlinepenalty\@M
  \def\address##1##2{\begingroup
    \par\addvspace\bigskipamountaspm\noindent
     \@ifnotempty{##1}{(\ignorespaces##1\unskip) }%
    {\itshape\small\ignorespaces##2}\par\endgroup}%
  \def\curraddr##1##2{\begingroup
    \@ifnotempty{##2}{\nobreak\indent{\itshape Current address}%
      \@ifnotempty{##1}{, \ignorespaces##1\unskip}\/:\space
      ##2\par\endgroup}}%
  \def\email##1##2{\begingroup
    \@ifnotempty{##2}{\nobreak\noindent{\itshape E-mail address}%
      \@ifnotempty{##1}{, \ignorespaces##1\unskip}\/:\space
      \ttfamily##2\par\endgroup}}%
  \def\urladdr##1##2{\begingroup
    \@ifnotempty{##2}{\nobreak\noindent{\itshape URL}%
      \@ifnotempty{##1}{, \ignorespaces##1\unskip}\/:\space
      \ttfamily##2\par\endgroup}}%
  \addresses
  \endgroup
}
\def\rcvdate#1{\def\@rcvdate{#1}}
\let\@rcvdate\@empty
\def\rvsdate#1{\def\@rvsdate{#1}}
\let\@rvsdate\@empty
\def\@setrcvdate{\upshape\rcvdatename\ \@rcvdate\@addpunct.}
\def\@setrvsdate{\upshape\rvsdatename\ \@rvsdate\@addpunct.}
\newcommand{\rcvdatename}{Received}
\newcommand{\rvsdatename}{Revised}
\renewcommand{\title}[2][]{\gdef\shorttitle{#1}\gdef\@title{%
\addtolength{\baselineskip}{1pt}
#2}}
\edef\title{\@nx\@dblarg
  \@xp\@nx\csname\string\title\endcsname}
\def\subtitle#1{\def\@subtitle{#1}}
\let\@subtitle=\@empty
\def\maketitle{\par
  \@topnum\z@
  \ifx\@empty\shortauthors \let\shortauthors\shorttitle
  \else \andify\shortauthors  \fi
  \begingroup
  \@maketitle
  \toks@\@xp{\shortauthors}\@temptokena\@xp{{\itshape\shorttitle}}%
  \edef\@tempa{\@nx\markboth{\the\toks@}{\the\@temptokena}}\@tempa
  \endgroup
  \thispagestyle{empty}
  \c@footnote\z@
  \def\do##1{\let##1\relax}%
  \do\maketitle \do\@maketitle \do\title \do\@xtitle \do\@title
  \do\subtitle \do\@subtitle
  \do\author \do\@xauthor \do\address \do\@xaddress
  \do\email \do\@xemail \do\curraddr \do\@xcurraddr
  \do\dedicatory \do\@dedicatory \do\thanks \do\thankses
  \do\keywords \do\@keywords \do\subjclass \do\@subjclass 
  \do\rcvdate \do\@rcvdate
  \do\rvsdate \do\@rvsdate
}
\def\@maketitle{%
  \normalfont\normalsize
  \let\@makefnmark\relax  \let\@thefnmark\relax
  \ifx\@empty\@rcvdate\else \@footnotetext{\@setrcvdate}\fi
  \ifx\@empty\@rvsdate\else \@footnotetext{\@setrvsdate}\fi
  \ifx\@empty\@subjclass\else \@footnotetext{\@setsubjclass}\fi
  \ifx\@empty\@keywords\else \@footnotetext{\@setkeywords}\fi
  \ifx\@empty\thankses\else \@footnotetext{%
    \def\par{\let\par\@par}\@setthanks}\fi
  \@mkboth{\@nx\shortauthors}{\@nx\shorttitle}%
  \normalfont\Large
  \noindent\smash{%
    \setbox2\hbox{\@bookinfohead}\relax%
    \@tempdimb=-\ht2\relax%
    \ifdim-\@tempdimb>\topskip\advance\@tempdimb\topskip\fi\relax%
    \advance\@tempdimb\topmargin\advance\@tempdimb\headheight
    \advance\@tempdimb\headsep\relax\advance\@tempdimb-2cm
    \raise\@tempdimb\hbox{\box2}}%
  \vspace*{26pt}
  \@settitle
  \ifx\@empty\@subtitle
  \else
    \vtop{\centering{\normalsize\@BF\@subtitle\@@par}%
      \global\dimen@i\prevdepth}\prevdepth\dimen@i
  \fi
  \ifx\@empty\authors \else \@setauthors \fi
  \ifx\@empty\@dedicatory
  \else
    \vtop{\centering{\normalsize\itshape\@BF\@dedicatory\@@par}%
      \global\dimen@i\prevdepth}\prevdepth\dimen@i
  \fi
  \@setabstract
  \normalsize
  \if@titlepage
    \newpage
  \else
    \dimen@34\p@ \advance\dimen@-\baselineskip
    \vskip\dimen@\relax
  \fi
\topskip=\normaltopskip
}
\def\@setauthors{%
  \begingroup
  \trivlist
  \vskip14\p@
  \centering
  \normalsize
  \@BF
  \item\relax
  \andify\authors
  \authors
  \endtrivlist
  \endgroup
}
\def\@settitle{\begin{center}%
 \Large
    \@BF
  \@title
  \end{center}%
}
\renewenvironment{abstract}{%
  \ifx\maketitle\relax
    \ClassWarning{\@classname}{Abstract should precede
      \protect\maketitle\space in AMS documentclasses; reported}%
  \fi
  \global\setbox\abstractbox=\vtop \bgroup
  \normalfont\small
  \advance \hsize -\parindent
  \advance \hsize -\parindent
   \noindent{\@BF\abstractname.}
   \vspace{\smallskipamountaspm}\par
}{%
  \egroup
  \ifx\@setabstract\relax \@setabstracta \fi
}
\def\@setabstracta{%
  \ifvoid\abstractbox
  \else
    \skip@24\p@ \advance\skip@-\lastskip
    \advance\skip@-\baselineskip \vskip\skip@
  \moveright \parindent
    \box\abstractbox
  \vspace{-9pt}
  \fi
}

%%%%
\def\@sect#1#2#3#4#5#6[#7]#8{%
  \edef\@toclevel{\ifnum#2=\@m 0\else\number#2\fi}%
  \ifnum #2>\c@secnumdepth \let\@secnumber\@empty
  \else \@xp\let\@xp\@secnumber\csname the#1\endcsname\fi
 \ifnum #2>\c@secnumdepth
   \let\@svsec\@empty
 \else
    \refstepcounter{#1}%
    \edef\@svsec{\ifnum#2<\@m
       \@ifundefined{#1name}{}{%
         \ignorespaces\csname #1name\endcsname\space}\fi
       \@nx\textup{%
         \csname the#1\endcsname.}\enspace
    }%
  \fi
  \@tempskipa #5\relax
  \ifdim \@tempskipa>\z@ % 
    \begingroup #6\relax
    \@hangfrom{\hskip #3\relax\@svsec}{\interlinepenalty\@M
    \hspace{.1em} #8\par}%
    \endgroup
    \ifnum#2>\@m \else \@tocwrite{#1}{#8}\fi
  \else
  \def\@svsechd{#6\hskip #3\@svsec
    \@ifnotempty{#8}{\ignorespaces#8}%
    \ifnum#2>\@m \else \@tocwrite{#1}{#8}\fi
  }%
  \fi
  \global\@nobreaktrue
  \@xsect{#5}}
\def\section{\@startsection{section}{1}%
  \z@{\bigskipamountaspm}{.7\linespacing}%
  {\noindent\mathhexbox278\normalfont\@BF}}
\def\subsection{\@startsection{subsection}{2}%
  \normalparindent{\medskipamountaspm}{\smallskipamount}%
  {\normalfont\@BF}}

\if@AdjustLines
\def\section{\@startsection{section}{1}%
  \z@{1.25\baselineskip}{.25\baselineskip}%
  {\noindent\mathhexbox278\normalfont\@BF}}
\def\subsection{\@startsection{subsection}{2}%
  \normalparindent{.75\baselineskip}{.25\baselineskip}%
  {\normalfont\@BF}}
\fi

%%%%
\renewenvironment{thebibliography}[1]{%
\addvspace{27pt}
\begin{center}\@BF\refname\end{center}
\vspace{4pt}
  \normalfont\small\labelsep .5em\relax
  \renewcommand\theenumiv{\arabic{enumiv}}\let\p@enumiv\@empty
\newdimen\truelabelwidth
\settowidth\truelabelwidth{#1}
  \list{[\makebox[\truelabelwidth]{\theenumiv}]}{
        \settowidth\labelwidth{\@biblabel{#1}}%
        \leftmargin\labelwidth \advance\leftmargin\labelsep
\addtolength{\leftmargin}{1em}
\addtolength{\itemindent}{-1em}
    \usecounter{enumiv}}%
  \sloppy \clubpenalty\@M \widowpenalty\clubpenalty
  \sfcode`\.=\@m
}{%
  \def\@noitemerr{\@latex@warning{Empty `thebibliography' environment}}%
  \endlist
}

%%%%
\def\footnoterule{\vskip-3.4\p@\hrule width 96\p@ \vskip 3\p@}
\long\def\@footnotetext#1{\insert\footins{%
  \normalfont\small
  \interlinepenalty\interfootnotelinepenalty
  \splittopskip\footnotesep \splitmaxdepth \dp\strutbox
  \floatingpenalty\@MM \hsize\columnwidth
  \@parboxrestore \parindent\normalparindent \sloppy
  \edef\@currentlabel{\p@footnote\@thefnmark}%
  \@makefntext{\rule\z@\footnotesep\ignorespaces#1\unskip\strut\par}}}

%%%%
\def\@captionheadfont{\upshape}
\def\@captionfont{\small}
\def\figurename{Fig.}
\newlength{\captionwidtha}
\setlength{\captionwidtha}{\textwidth}
\addtolength{\captionwidtha}{-6pc}
\def\hangcaption{\refstepcounter\@captype\@dblarg{%
\@hangcaption\@captype}}
\long\def\@hangcaption#1[#2]#3{%
  \baselineskip 14.5\p@
  \addcontentsline{\csname ext@#1\endcsname}{#1}%
    {\protect\numberline{\csname the#1\endcsname}{\ignorespaces #2}}%
  \par
  \begingroup
    \@parboxrestore
    \setbox\@tempboxa\hbox{\csname fnum@#1\endcsname: #3}%
    \ifdim \wd\@tempboxa > \captionwidtha
      \begingroup
        \setbox\@tempboxa\hbox{\csname fnum@#1\endcsname: }%
        \advance \captionwidtha by -\wd\@tempboxa
        \@makecaption{\csname fnum@#1\endcsname}%
            {\ignorespaces{\protect\parbox[t]{%
             \captionwidtha}{\leavevmode#3}}}%
      \endgroup
    \else
      \begingroup
        \@makecaption{\csname fnum@#1\endcsname}{\ignorespaces #3}%
      \endgroup
    \fi
    \par\vspace{1.7ex}%
  \endgroup}
\let\caption\hangcaption

%%%%
\def\@thm#1#2#3{\normalfont
  \trivlist
  \edef\@restorelabelsep{\labelsep\the\labelsep}%
  \normalfont\bfseries
  \labelsep1em\relax
  \normalfont
  \let\thmheadnl\relax
  \let\thm@indent\noindent % no indent
  \let\thm@swap\@gobble
  \thm@headfont{\bfseries}% heading font bold
  \thm@headpunct{.}% add period after heading
  \thm@preskip\topsep
  \thm@postskip\thm@preskip
  #1% style overrides
  \@topsep \thm@preskip               % used by first \item
  \@topsepadd \thm@postskip           % used by \@endparenv
  \def\@tempa{#2}\ifx\@empty\@tempa
    \def\@tempa{\@oparg{\@begintheorem{#3}{}}[]}%
  \else
    \refstepcounter{#2}%
    \def\@tempa{\@oparg{\@begintheorem{#3}{\csname the#2\endcsname}}[]}%
  \fi
  \@tempa
}
\renewcommand{\qedsymbol}{\hbox{Q.E.D.}}
\def\th@plain{%
  \let\thm@indent\indent
  \thm@headfont{\bfseries}% heading font bold face
  \thm@notefont{\mdseries\upshape}%
  \let\thmhead\thmhead@plain \let\swappedhead\swappedhead@plain
  \if@AdjustLines
    \thm@preskip.5\baselineskip
  \else
    \thm@preskip.5\baselineskip\@plus.2\baselineskip
                                    \@minus.2\baselineskip
  \fi
  \thm@postskip\thm@preskip
  \itshape
}
\def\th@definition{%
  \let\thm@indent\indent
  \thm@headfont{\bfseries}% heading font bold face
  \thm@notefont{\mdseries\upshape}%
  \let\thmhead\thmhead@plain \let\swappedhead\swappedhead@plain
  \if@AdjustLines
    \thm@preskip.5\baselineskip
  \else
    \thm@preskip.5\baselineskip\@plus.2\baselineskip
                                    \@minus.2\baselineskip
  \fi
  \thm@postskip\thm@preskip
  \upshape
}
\def\th@remark{%
  \let\thm@indent\indent
  \thm@headfont{\itshape}% heading font italic
  \thm@notefont{\mdseries\upshape}%
  \let\thmhead\thmhead@plain \let\swappedhead\swappedhead@plain
  \if@AdjustLines
    \thm@preskip.5\baselineskip
  \else
    \thm@preskip.5\baselineskip\@plus.2\baselineskip
                                    \@minus.2\baselineskip
  \fi
  \thm@postskip\thm@preskip
  \upshape
}
\renewenvironment{proof}[1][\proofname]{\par \normalfont
  \if@AdjustLines
    \topsep.5\baselineskip
  \else
    \topsep6\p@\@plus6\p@ 
  \fi
  \trivlist \itemindent\normalparindent
  \item[\hskip\labelsep\itshape
    #1\@addpunct{.}\hspace{5pt}]\ignorespaces
}{%
  \qed\endtrivlist
}
\def\@cite#1#2{{%
 \m@th\upshape\mdseries[{#1\if@tempswa, #2\fi}]}}
\@ifundefined{cite }{%
  \expandafter\let\csname cite \endcsname\cite
  \edef\cite{\@nx\protect\@xp\@nx\csname cite \endcsname}%
}{}
%%%%
\@ifundefined{thm@headfont}{%
  \ClassWarning{aspm.cls}{Use the latest amsproc.cls}
  \let\captionheadfont@\@captionheadfont
  \let\captionfont@\@captionfont
  \let\theoremindent\indent
  \let\thm@headfont\theoremheadfont
  \let\thm@headpunct\theoremheadpunct
  \let\thm@preskip\theorempreskipamount
  \let\thm@postskip\theorempostskipamount
  \let\thm@notefont\theoremnotefont}{}

%%%%
\definecolor{linecolor}{rgb}{0.58,.72,.5}%
\newdimen\frame@rule \frame@rule=.12mm
\def\@OneLine{\leavevmode\noindent%
  \vrule width\z@ height10pt depth\z@%
  \vrule width312pt height.12mm depth\z@%
}
\def\@@gridframe{%
  \hbox to\z@{%
    \hss\vbox to\z@{\vskip16pt\parindent\z@\ifdim\topskip>10pt \vskip-10pt\else\fi
      \vskip-\frame@rule
      \color{linecolor}%
      \hrule height\frame@rule\hbox{\vrule width\frame@rule%
      \dimen@=504pt \advance\dimen@ by\maxdepth\relax%
      \vbox to\dimen@{%
        \hsize=312pt\normalsize\normalfont%
          \parfillskip=\z@\relax%
          \@tempcntb=42\relax% 42 lines
          \loop\ifnum\@tempcntb>0 
            \textcolor{linecolor}{\@OneLine}\par%
            \advance\@tempcntb by-1
          \repeat
      \vss}%
      \vrule width\frame@rule}\hrule height\frame@rule%
    \vss}%
  \hss}%
}
\def\@gridframe{\if@TextFrame\protect\@@gridframe\else\fi}
\if@TextFrame
\def\@Paper@Domain@L{%
  {\color{linecolor}\smash{%
    \lower\paperheight\hbox to\z@{%
      \hss\vrule height\paperheight width\frame@rule depth\z@}%
    \lower\paperheight\hbox to\z@{%
      \hskip\paperwidth\if@Spread\hskip-.5\frame@rule\else\fi\vrule height\paperheight width\frame@rule depth\z@\hss}%
    \lower\paperheight\hbox to\z@{%
      \lower\frame@rule\hbox{\vrule width\paperwidth height\frame@rule depth\z@}\hss}%
    \hbox to\z@{\vrule width\paperwidth height\frame@rule depth\z@\hss}}}}
\def\@Paper@Domain@R{%
  {\color{linecolor}\smash{%
    \lower\paperheight\hbox to\z@{%
      \vrule height\paperheight width\frame@rule depth\z@\hss}%
    \lower\paperheight\hbox to\z@{%
      \hss\lower\frame@rule\hbox{\vrule width\paperwidth height\frame@rule depth\z@}}%
    \hbox to\z@{\hss\vrule width\paperwidth height\frame@rule depth\z@}}}}
\else
\def\@Paper@Domain@L{}\def\@Paper@Domain@R{}
\fi

\newdimen\pagewidth  \pagewidth=\paperwidth
\newdimen\pageheight \pageheight=\paperheight

\newdimen\tombowrule   \tombowrule.1mm % 
\newdimen\tombowlength \tombowlength 10mm % 
\newdimen\tombowgap    \tombowgap     3mm % 

\def\tb@v{\hbox to\tombowgap{\hss
 \vrule width\tombowrule height\tombowlength \kern-\tombowrule\kern\tombowgap%
 \vrule width\tombowrule height\tombowlength\hss}}
\def\tb@h{\vbox to\tombowgap{\hsize\tombowlength\vss
 \hrule height\tombowrule width\tombowlength \kern-\tombowrule\kern\tombowgap%
 \hrule height\tombowrule width\tombowlength\vss}}

\def\@RH{\rlap{%
  \vbox to\z@{\offinterlineskip\vss\tb@v\hbox{\kern\tombowgap\tb@h}}%
  }}
\def\@LH{\llap{%
  \vbox to\z@{\offinterlineskip\vss\hbox{\kern\tombowlength\tb@v}\hbox{\tb@h\kern\tombowgap}}%
  }}
\def\@RB{\rlap{%
  \vbox to\z@{\offinterlineskip\hbox{\kern\tombowgap\tb@h}\tb@v\vss}%
  }}
\def\@LB{\llap{%
  \vbox to\z@{\offinterlineskip\hbox{\tb@h\kern\tombowgap}\hbox{\kern\tombowlength\tb@v}\vss}%
  }}

\def\@PLUS{%
  \hb@xt@\z@{%
    \hb@xt@\z@{\hss
      \vbox to\z@{\vss\hrule height\tombowrule width\tombowlength\vss}\hss}%
    \hb@xt@\z@{\hss
      \vbox to\z@{\vss\hrule width\tombowrule height\tombowlength\vss}\hss}%
    }%
  }
\def\@PLUST{\vbox to\z@{\vss\@PLUS\kern.5\tombowlength\kern\tombowgap}}
\def\@PLUSB{\vbox to\z@{\kern.5\tombowlength\kern\tombowgap\@PLUS\vss}}
\def\@PLUSL{\llap{\@PLUS\kern.5\tombowlength\kern\tombowgap}}
\def\@PLUSR{\rlap{\kern.5\tombowlength\kern\tombowgap\@PLUS}}

\def\print@date@header{%
  \vbox to\z@{\vskip-\tombowlength\vskip-\tombowgap%
    \rlap{%
      \if@Spread
        \ifodd\c@page
          \kern\pagewidth
        \fi
      \fi
    \hskip.5cm\reset@font\@PrintAtDate}%
  \vss}%
}

\def\PrintAtDate#1{%
  \gdef\@PrintAtDate{#1}
}

\newcount\hour
\newcount\minute
\hour\time \divide\hour by 60\relax
\@tempcnta\hour \multiply\@tempcnta 60\relax
\minute\time \advance\minute-\@tempcnta

\PrintAtDate{\jobname.tex\space:\space\number\year/\number\month/\number\day\space
      (\number\hour:\number\minute)\quad page: \the\c@page}

\let\print@date\@PrintAtDate

\def\@outputpage{%
\begingroup
  \let\protect\noexpand
  \@resetactivechars
  \@parboxrestore
  \global\setbox\@OnePage
   \vbox to\pageheight{%
     \set@typeset@protect
     \if@specialpage
       \global\@specialpagefalse\@nameuse{ps@\@specialstyle}%
     \fi
     \if@twoside
       \ifodd\count\z@ \let\@thehead\@oddhead \let\@thefoot\@oddfoot
          \let\@themargin\oddsidemargin
       \else \let\@thehead\@evenhead
          \let\@thefoot\@evenfoot
           \let\@themargin\evensidemargin
     \fi\fi
     \reset@font\normalsize\normalsfcodes
     \let\label\@gobble
     \let\index\@gobble
     \let\glossary\@gobble
     \baselineskip\z@skip
     \lineskip\z@skip
     \lineskiplimit\z@
     \@begindvi
     \vbox to\z@{\box\@OnePage\vss}%%
     \hbox to\if@Spread 2\fi\pagewidth{\@Paper@Domain@L%
       \@LH\print@date@header\hfil\@PLUST\hfil\@RH%
     \@Paper@Domain@R}%
     \vbox to\z@{\kern.5\pageheight%
     \hbox to\if@Spread 2\fi\pagewidth{\@PLUSL\hfil\@PLUSR}\vss}%
     \vskip \topmargin%
     \hbox to\pagewidth{\kern\@themargin%
      \if@Spread
        \ifodd\c@page
          \kern\pagewidth
        \fi
      \fi
      \vbox{\setbox\@tempboxa
      \vbox to\headheight{\vfil
        \color@hbox\normalcolor
          \hb@xt@\textwidth{\@thehead}%
        \color@endbox}
        \dp\@tempboxa\z@
        \box\@tempboxa
        \vskip \headsep
        \box\@outputbox
        \baselineskip\footskip
        \color@hbox\normalcolor
          \hbox to\textwidth{\@thefoot}%
        \color@endbox}\hss}
     \vss
     \hbox to\if@Spread 2\fi\pagewidth{\@LB\hfil\@PLUSB\hfil\@RB}
   }
   \if@Spread
     \ifodd\c@page
       \if@NoShipout\else\shipout\box\@OnePage\fi
     \fi
   \else
     \if@NoShipout\else\shipout\box\@OnePage\fi
   \fi
\endgroup
\global\@colht\textheight
\stepcounter{page}\let\firstmark\botmark}

\def\holdpage{\global\@NoShipouttrue}

\if@tombow
  \tombowrule.12mm
\else\relax% 2009/01/13
  \tombowrule\z@ 
\fi

% 2009/01/13
\if@CenterPut
  \if@Spread
  \else
    \@tempdima=210mm
    \advance\@tempdima-\paperwidth
    \divide\@tempdima+2
    \addtolength{\hoffset}{\@tempdima}
    \addtolength{\hoffset}{-1in}
    \@tempdima=297mm
    \advance\@tempdima-\paperheight
    \divide\@tempdima+2
    \addtolength{\voffset}{\@tempdima}
    \addtolength{\voffset}{-1in}
  \fi
\fi

% 2009/01/13
\if@HeaderInfo
\else
  \let\@PrintAtDate\relax
\fi

\if@Spread
  \special{papersize=380mm,297mm}
\else
  \special{papersize=210mm,297mm}
\fi

\endinput
