%% For double-blind review submission
%\documentclass[acmsmall,10pt,fleqn,review,anonymous]{acmart}\settopmatter{printfolios=true}
%% For single-blind review submission
\documentclass[acmsmall,10pt,review]{acmart}\settopmatter{printfolios=true}
%% For final camera-ready submission
%\documentclass[acmsmall,10pt,fleqn]{acmart}\settopmatter{}

%% Note: Authors migrating a paper from PACMPL format to traditional
%% SIGPLAN proceedings format should change 'acmlarge' to
%% 'sigplan,10pt'.

%include agda.fmt

%subst keyword a = "\keyword{" a "}"
%subst conid a = "\identifier{" a "}"
%subst varid a = "\identifier{" a "}"
%subst numeral a = "\mathbf{" a "}"
%format : = "{:}"
%format Set = "\constructor{Set}"
%format (GOAL(t)(i)) = "\highlight{goal}{\textbf\{\," t "\,\textbf\}_{\kern1pt" i "}}"
%format (GOAL'(t)) = "\highlight{goal}{\textbf\{\," t "\,\textbf\}}"
%format (CXT(t)) = "\kern-2pt_{\highlight{cxt}{" t "}}"

%format refl = "\constructor{refl}"
%format × = "{×}"
%format , = "\kern-1pt,"
%format Maybe = "\constructor{Maybe}"
%format nothing = "\constructor{nothing}"
%format just = "\constructor{just}"
%format List = "\constructor{List}"
%format AlgList = "\constructor{AlgList}"
%format CoList = "\constructor{CoList}"
%format CoListF = "\constructor{CoListF}"
%format CoalgList = "\constructor{CoalgList}"
%format CoalgListF = "\constructor{CoalgListF}"
%format ∷ = "{::}"
%format ∷⟨ = ∷ ⟨
%format _∷⟨_⟩_ = _ "\kern1pt" ∷⟨ "\kern-1pt" _ ⟩ _
%format ⟨_⟩ = ⟨ "\kern-1pt" _ ⟩
%format _∷_ = _ "\kern1pt" ∷ _
%format [ = "[\!"
%format ] = "\!]"
%format decon = "\constructor{decon}"
%format Σ[ = "\Sigma" [
%format jigsawᵢᵥ = "\identifier{jigsaw_\mathrm{\,IV}}"
%format fillᵢᵥ = "\identifier{fill_\mathrm{\,IV}}"
%format flat-edge-productionᵢ = "\identifier{flat-edge-production_\mathrm{\,I}}"
%format jigsaw-conditionᵢ = "\identifier{jigsaw-condition_\mathrm{\,I}}"
%format jigsawᵢₕ = "\identifier{jigsaw_\mathrm{\,IH}}"
%format fillᵢₕ = "\identifier{fill_\mathrm{\,IH}}"

\newcommand{\token}[1]{{\operatorname{\mathcode`\'="8000 #1}}}
\newcommand{\keyword}[1]{\token{\mathbf{#1}}}
\newcommand{\identifier}[1]{\token{\mathit{#1}}}
\newcommand{\constructor}[1]{\token{\mathsf{#1}}}

\definecolor{goal}{RGB}{209,243,205}
\definecolor{cxt}{RGB}{255,255,150}
\definecolor{emphasis}{RGB}{255,255,200}
\newcommand{\highlight}[2]{\smash{\text{\colorbox{#1}{\kern-.1em\vphantom{\vrule height 1.2ex depth 0.1ex}\smash{\ensuremath{#2}}\kern-.1em}}}}

\makeatletter
\newcommand{\shorteq}{%
  \settowidth{\@@tempdima}{-}%
  \resizebox{\@@tempdima}{\height}{=}%
}
\makeatother

\newcommand{\name}[1]{\textsc{#1}}
\newcommand{\Agda}{\name{Agda}}

%\newcommand{\varref}[2]{\hyperref[#2]{#1\ref*{#2}}}

%% Some recommended packages.
\usepackage{booktabs}   %% For formal tables:
                        %% http://ctan.org/pkg/booktabs
\usepackage{subcaption} %% For complex figures with subfigures/subcaptions
                        %% http://ctan.org/pkg/subcaption

\usepackage{mathtools}
\usepackage{enumitem}
\usepackage{xifthen}
\usepackage[UKenglish]{isodate}

\usepackage{tikz}
\usetikzlibrary{matrix,arrows,calc,fadings,positioning}
\tikzset{every path/.append style={semithick}}
\begin{tikzfadingfrompicture}[name=fade out, x=25bp, y=25bp]
\fill[color=transparent!0] (-1, -.66) rectangle (1, .66);
\shade[top color=transparent!0, bottom color=transparent!100] (-1, -1) rectangle (1, -.4);
\shade[top color=transparent!100, bottom color=transparent!0] (-1, .4) rectangle (1, 1);
\end{tikzfadingfrompicture}
\tikzset{label on arrow/.style={fill=white, path fading=fade out}}
\begin{tikzfadingfrompicture}[name=horizontal fade out, x=25bp, y=25bp]
\fill[color=transparent!0] (-.66 , -1) rectangle (.66 , 1);
\shade[right color=transparent!0, left color=transparent!100] (-1, -1) rectangle (-.65 , 1);
\shade[right color=transparent!100, left color=transparent!0] (.65, -1) rectangle (1, 1);
\end{tikzfadingfrompicture}
\tikzset{horizontal label on arrow/.style={fill=white, path fading=horizontal fade out}}

\usepackage[color=yellow,textsize=scriptsize]{todonotes}
\setlength{\marginparwidth}{1cm}

\renewcommand{\sectionautorefname}{Section}
\renewcommand{\subsectionautorefname}{Section}
\renewcommand{\subsubsectionautorefname}{Section}
\renewcommand{\figureautorefname}{Figure}
\newcommand{\lemmaautorefname}{Lemma}
\newcommand{\propositionautorefname}{Proposition}
\newcommand{\corollaryautorefname}{Corollary}
\newcommand{\definitionautorefname}{Definition}
\newcommand{\exampleautorefname}{Example}

\newcommand{\varparagraph}[1]{\paragraph{#1}\hspace{.5em}} % {\textit{#1}\hspace{.5em}}
\newcommand{\awa}[2]{\mathrlap{#2}\phantom{#1}} % as wide as
\newcommand{\varawa}[2]{\phantom{#1}\mathllap{#2}}
\newcommand{\varcitet}[3][]{\citeauthor{#2}#3~[\ifthenelse{\isempty{#1}}{\citeyear{#2}}{\citeyear[#1]{#2}}]}

\makeatletter\if@@ACM@@journal\makeatother
%% Journal information (used by PACMPL format)
%% Supplied to authors by publisher for camera-ready submission
\acmJournal{PACMPL}
\acmVolume{0}
\acmNumber{0}
\acmArticle{0}
\acmYear{\the\year}
\acmMonth{\the\month}
\acmDOI{10.1145/nnnnnnn.nnnnnnn}
%\startPage{1}
%\else\makeatother
%% Conference information (used by SIGPLAN proceedings format)
%% Supplied to authors by publisher for camera-ready submission
%\acmConference[PL'17]{ACM SIGPLAN Conference on Programming Languages}{January 01--03, 2017}{New York, NY, USA}
%\acmYear{2017}
%\acmISBN{978-x-xxxx-xxxx-x/YY/MM}
%\acmDOI{10.1145/nnnnnnn.nnnnnnn}
%\startPage{1}
\fi


%% Copyright information
%% Supplied to authors (based on authors' rights management selection;
%% see authors.acm.org) by publisher for camera-ready submission
\setcopyright{none}             %% For review submission
%\setcopyright{acmcopyright}
%\setcopyright{acmlicensed}
%\setcopyright{rightsretained}
%\copyrightyear{2017}           %% If different from \acmYear


%% Bibliography style
\bibliographystyle{ACM-Reference-Format}
%% Citation style
%% Note: author/year citations are required for papers published as an
%% issue of PACMPL.
\citestyle{acmauthoryear}   %% For author/year citations
\setcitestyle{nosort}

\begin{document}

\setlength{\mathindent}{\parindent}

%% Title information
\title{Programming Metamorphic Algorithms (Functional Pearl)}
                                        %% [Short Title] is optional;
                                        %% when present, will be used in
                                        %% header instead of Full Title.
\begin{anonsuppress}
\titlenote{Draft manuscript (\today)}    %% \titlenote is optional;
\end{anonsuppress}
                                        %% can be repeated if necessary;
                                        %% contents suppressed with 'anonymous'
%\subtitle{An Exercise in Algorithm Design with Inductive and Coinductive Families}
                                        %% \subtitle is optional
%\subtitlenote{with subtitle note}      %% \subtitlenote is optional;
                                        %% can be repeated if necessary;
                                        %% contents suppressed with 'anonymous'


%% Author information
%% Contents and number of authors suppressed with 'anonymous'.
%% Each author should be introduced by \author, followed by
%% \authornote (optional), \orcid (optional), \affiliation, and
%% \email.
%% An author may have multiple affiliations and/or emails; repeat the
%% appropriate command.
%% Many elements are not rendered, but should be provided for metadata
%% extraction tools.

%% Author with single affiliation.
\author{Hsiang-Shang Ko}
%\authornote{with author1 note}         %% \authornote is optional;
                                        %% can be repeated if necessary
%\orcid{nnnn-nnnn-nnnn-nnnn}            %% \orcid is optional
\affiliation{
  \position{Project Researcher}
  \department{Information Systems Architecture Science Research Division}
                                        %% \department is recommended
  \institution{National Institute of Informatics}
                                        %% \institution is required
  \streetaddress{2-1-2 Hitotsubashi}
  \city{Chiyoda-ku}
  \state{Tokyo}
  \postcode{101-8430}
  \country{Japan}
}
\email{hsiang-shang@@nii.ac.jp}         %% \email is recommended

%% Paper note
%% The \thanks command may be used to create a "paper note" ---
%% similar to a title note or an author note, but not explicitly
%% associated with a particular element.  It will appear immediately
%% above the permission/copyright statement.
%\thanks{with paper note}               %% \thanks is optional
                                        %% can be repeated if necessary
                                        %% contents suppressed with 'anonymous'


%% Abstract
%% Note: \begin{abstract}...\end{abstract} environment must come
%% before \maketitle command
\begin{abstract}
\todo[inline]{abstract}
\end{abstract}


%% 2012 ACM Computing Classification System (CSS) concepts
%% Generate at 'http://dl.acm.org/ccs/ccs.cfm'.
%\begin{CCSXML}
%<ccs2012>
%<concept>
%<concept_id>10011007.10011006.10011008</concept_id>
%<concept_desc>Software and its engineering~General programming languages</concept_desc>
%<concept_significance>500</concept_significance>
%</concept>
%<concept>
%<concept_id>10003456.10003457.10003521.10003525</concept_id>
%<concept_desc>Social and professional topics~History of programming languages</concept_desc>
%<concept_significance>300</concept_significance>
%</concept>
%</ccs2012>
%\end{CCSXML}

%\ccsdesc[500]{Software and its engineering~General programming languages}
%\ccsdesc[300]{Social and professional topics~History of programming languages}
%% End of generated code


%% Keywords
%% comma separated list
%\keywords{keyword1, keyword2, keyword3}  %% \keywords is optional


%% \maketitle
%% Note: \maketitle command must come after title commands, author
%% commands, abstract environment, Computing Classification System
%% environment and commands, and keywords command.
\maketitle


\section{Why dependently typed programming?}

Why do we want to program with full dependent types?
For larger-scale proofs, writing proof terms in a dependently typed language is usually much less efficient than working with a proof assistant with decent automation.
What has been more successful with dependently typed programming (DTP) --- in particular with the use of indexed datatypes --- is intrinsic hygienic guarantees, which tend to work better for smaller, hand-crafted programs: if we need to, for example, track the bounds of indices or work with well-typed syntax trees, let us encode bound and typing constraints in the datatypes of indices and syntax trees so that the type system can help the programmer to enforce the constraints.
But this is achievable with automated proof assistants, and does not make DTP truly shine --- the most fascinating aspect of DTP is the prospect that intrinsic typing can provide semantic hints to the programmer during an interactive development process, so that the heavy typing becomes a worthwhile asset rather than a unnecessary burden.

\todo[inline]{In exchange for this kind of guarantee, though\ldots}

\section{Metamorphisms}

A \emph{metamorphism}~\citep{Gibbons-metamorphisms} is an unfold after a fold --- it consumes a data structure to compute an intermediate value and then produces a new data structure using the intermediate value as the seed.
In this paper we will look at metamorphisms consuming and producing lists.

\begin{code}
data List (A : Set) : Set where
  []   : List A
  _∷_  : A → List A → List A
\end{code}

\begin{code}
foldr : {A X : Set} → (A → X → X) → X → List A → X
foldr f e []        = e
foldr f e (a ∷ as)  = f a (foldr f e as)
\end{code}

\section{Specification of Metamorphisms in Types}

\begin{code}
data AlgList (A {X} : Set) (f : A → X → X) (e : X) : X → Set where
  []   : AlgList A f e e
  _∷_  : ∀ {x} → (a : A) → AlgList A f e x → AlgList A f e (f a x)
\end{code}

\citet{McBride-ornaments}

\begin{code}
mutual

  record CoList (B : Set) : Set where
    coinductive
    field
      decon : CoListF B
  
  data CoListF (B : Set) : Set where
    []   : CoListF B
    _∷_  : B → CoList B → CoListF B
\end{code}

\begin{code}
unfoldr : {B X : Set} → (X → Maybe (B × X)) → X → CoList B
decon (unfoldr g x) with g x
decon (unfoldr g x) | nothing        = []
decon (unfoldr g x) | just (b , x')  = b ∷ unfoldr g x'
\end{code}

\begin{code}
mutual

  record CoalgList (B {X} : Set) (g : X → Maybe (B × X)) (x : X) : Set where
    coinductive
    field
      decon : CoalgListF B g x

  data CoalgListF (B {X} : Set) (g : X → Maybe (B × X)) : X → Set where
    ⟨_⟩     : ∀ {x} → g x ≡ nothing → CoalgListF B g x
    _∷⟨_⟩_  : ∀ {x x'} → (b : B) → g x ≡ just (b , x') → CoalgList B g x' → CoalgListF B g x
\end{code}

The |foldr| version, and then the |foldl| version.

Let |A|, |B|, |S : Set| throughout the rest of this paper.

\section{Definitional Implementation of Metamorphisms}

Let |f : S → A → S| and |g : S → Maybe (B × S)| throughout this section and the next.

\todo[inline]{This exposes the state, which can participate in the computation.}

As a sanity check, we start from the most straightforward algorithm that strictly follows the definition of metamorphisms, \textbf{c}onsuming all inputs \textbf{b}efore \textbf{p}roducing outputs:
\begin{code}
cbp : {h : S → S} → AlgList A (foldl-alg f) id h → (s : S) → CoalgList B g (h s)
cbp as s = (GOAL(CoalgList B g (h s))(0))
\end{code}
The \highlight{goal}{\text{green-shaded part}} is an \emph{interaction point} or a \emph{goal}, which is a hole in the program to be filled in.%
\todo{more explanation}\
We are trying to consume the input list first, so we pattern match on the argument |as| to see if there is anything to consume:
\begin{code}
cbp []        s = (GOAL(CoalgList B g s)(1))
cbp (a ∷ as)  s = (GOAL(CoalgList B g (h' (f s a)))(2))
\end{code}
If there is, we go into Goal~2, where we keep consuming the tail |as| but from a new state:
\begin{code}
cbp (a ∷ as) s = cbp as (GOAL(S)(3))
\end{code}
What is this new state? It should be the one obtained by merging~|a| into~|s|, i.e., |f s a|.
\Agda\ knows this too, in fact --- firing Auto (\texttt{C-c C-a}) at Goal~3 yields:
\begin{code}
cbp (a ∷ as) s = cbp as (f s a)
\end{code}
If the input list is empty (that is, there is nothing more to consume), we go into Goal~1, where we should produce the output co-list, to specify which we should say what will result if we observe/|decon|struct the co-list:
\begin{code}
decon (cbp [] s) = (GOAL(CoalgListF B g s)(4))
\end{code}
The result of observation depends on whether |g|~can produce anything from the current state~|s|, so we pattern match on |g s|:
\begin{code}
decon (cbp [] s) with g s
decon (cbp [] s) | nothing        = (GOAL(CoalgListF B g s)(5))
decon (cbp [] s) | just (b , s')  = (GOAL(CoalgListF B g s)(6))
\end{code}
If |g s| is |nothing| (Goal~5), the output co-list is empty; otherwise |g s| is some |just (b , s')| (Goal~6), in which case we use~|b| as the head and continue to produce the tail from~|s'|.
We therefore refine the two goals into:
\begin{code}
decon (cbp [] s) with g s
decon (cbp [] s) | nothing        = ⟨ (GOAL(g s ≡ nothing)(7)) ⟩
decon (cbp [] s) | just (b , s')  = b ∷⟨ (GOAL(g s ≡ just (b , s'))(8)) ⟩ cbp [] s'
\end{code}
We are now required to discharge equality proof obligations about |g s|, and the obligations exactly correspond to the results of the |with|-matching.
This is precisely a situation in which the |inspect| idiom of the \Agda\ standard library can help: with |inspect|, we can obtain an equality proof of the right type in each of the cases of the |with|-matching.
We therefore obtain:
\begin{code}
cbp : {h : S → S} → AlgList A (foldl-alg f) id h → (s : S) → CoalgList B g (h s)
decon (cbp [] s) with g s         | inspect g s
decon (cbp [] s) | nothing        | [ eq(CXT(g s ≡ nothing))        ] = ⟨ eq ⟩
decon (cbp [] s) | just (b , s')  | [ eq(CXT(g s ≡ just (b , s')))  ] = b ∷⟨ eq ⟩ cbp [] s'
cbp (a ∷ as) s = cbp as (f s a)
\end{code}
where, in each case of the |with|-matching, we annotate |eq| with its type in \highlight{cxt}{\text{yellow-shaded subscript}} (which is not part of the program text).
\todo[inline]{Expected, even boring, typical type-directed programming}

\section{Streaming Metamorphisms}

As \citet{Gibbons-metamorphisms} noted, (list) metamorphisms in general cannot be automatically optimised in terms of time and space, but under certain conditions it is possible to refine a list metamorphism to a \emph{streaming algorithm} --- which can produce an initial segment of the output list without consuming all of the input list.

We implement a different algorithm with the same type:
\begin{code}
stream : {h : S → S} → AlgList A (foldl-alg f) id h → (s : S) → CoalgList B g (h s)
stream as s = (GOAL(CoalgList B g (h s))(0))
\end{code}
Different from |cbp|, this time we try to produce using~|g| whenever possible, so our first step is to pattern match on |g s| (and we are also introducing |decon| and |inspect|, which will be needed like in |cbp|):
\begin{code}
decon (stream as s) with g s         | inspect g s
decon (stream as s) | nothing        | [ eq ] = (GOAL(CoalgListF B g (h s))(1))
decon (stream as s) | just (b , s')  | [ eq ] = (GOAL(CoalgListF B g (h s))(2))
\end{code}
For Goal~1, we cannot produce anything since |g s| is |nothing|, but this does not mean that the output co-list is empty --- we may be able to produce something once we consume the input list and advance to a new state.
We therefore pattern match on the input list:
\begin{code}
decon (stream []        s) | nothing | [ eq ] = (GOAL(CoalgListF B g s)(3))
decon (stream (a ∷ as)  s) | nothing | [ eq ] = (GOAL(CoalgListF B g (h' (f s a)))(4))
\end{code}
These two goals are similar to what we have seen in |cbp|.
At Goal~3, there is nothing more in the input list to consume, so we should end production as well, emitting an empty co-list, while for Goal~4 (where |h'|~is the index in the type of the tail~|as|) we should advance to the new state |f s a| and set the tail |as| as the list to be consumed next:
\begin{code}
decon (stream []        s) | nothing | [ eq ] = ⟨ eq ⟩
decon (stream (a ∷ as)  s) | nothing | [ eq ] = decon (stream as (f s a))
\end{code}
Goal~2 is the interesting case.
Using~|g|, from the current state~|s| we can produce~|b|, which we set as the head of the output co-list, and advance to a new state~|s'|, from which we produce the tail of the co-list:
\begin{code}
decon (stream as s) | just (b , s') | [ eq(CXT(g s ≡ just (b , s'))) ] =
  b ∷⟨ (GOAL(g (h s) ≡ just (b , h s'))(5)) ⟩ stream as s'
\end{code}
Now we get a non-trivial proof obligation (Goal~5) --- what does it mean?
The left-hand side |g (h s)| is trying to produce using~|g| from the state |h s|, where |h|~is the state transformation function resulting from consuming the entire input list~|as| (since |h|~is the index in the type of~|as|), and the whole equality says that this has to produce a specific result.
Drawing this as a state transition diagram:
\[ \begin{tikzpicture}[x=12em,y=4em]
\node(x) [anchor=center] {|s|};
\node(x') [below=1 of x,anchor=center] {\phantom{|s'|}};
\node(hx) [right=1 of x,anchor=center] {|h s|};
\node(hx') [right=1 of x',anchor=center] {|h s'|};
\draw[serif cm-to] (x) edge node[above]{consume~|as| with~|h|} (hx);
%\draw[serif cm-to] (x') edge node[below]{consume~|as| with~|h|} (hx');
%\draw[serif cm-to] (x) edge node(t)[left]{produce~|b| with~|g|} (x ||- x'.north);
\draw[serif cm-to] (hx) edge node(u)[right]{\rlap{produce~|b| with~|g|}} (hx ||- hx'.north);
%\node at ($(t)!0.5!(u)$) [anchor=center] {$\Rightarrow$};
\end{tikzpicture} \]
We already have in the context a similar-looking equality proof, namely~|eq|, which we can superimpose on the diagram:
\[ \begin{tikzpicture}[x=12em,y=4em]
\node(x) [anchor=center] {|s|};
\node(x') [below=1 of x,anchor=center] {|s'|};
\node(hx) [right=1 of x,anchor=center] {|h s|};
\node(hx') [right=1 of x',anchor=center] {|h s'|};
\draw[serif cm-to] (x) edge node[above]{consume~|as| with~|h|} (hx);
%\draw[serif cm-to] (x') edge node[below]{consume~|as| with~|h|} (hx');
\draw[serif cm-to] (x) edge node(t)[left]{produce~|b| with~|g|} (x ||- x'.north);
\draw[serif cm-to] (hx) edge node(u)[right]{produce~|b| with~|g|} (hx ||- hx'.north);
\node at ($(t)!0.5!(u)$) [anchor=center] {$\Rightarrow$};
\end{tikzpicture} \]
We also put in an implication arrow to indicate more explicitly that |g s ≡ just (b , s')| is a premise, from which we should derive |g (h s) ≡ just (b , h s')|.
Now it is tempting, and indeed easy, to complete the diagram:
\[ \begin{tikzpicture}[x=12em,y=4em,baseline=(u.base)]
\node(x) [anchor=center] {|s|};
\node(x') [below=1 of x,anchor=center] {|s'|};
\node(hx) [right=1 of x,anchor=center] {|h s|};
\node(hx') [right=1 of x',anchor=center] {|h s'|};
\draw[serif cm-to] (x) edge node[above]{consume~|as| with~|h|} (hx);
\draw[serif cm-to] (x') edge node[below]{consume~|as| with~|h|} (hx');
\draw[serif cm-to] (x) edge node(t)[left]{produce~|b| with~|g|} (x ||- x'.north);
\draw[serif cm-to] (hx) edge node(u)[right]{produce~|b| with~|g|} (hx ||- hx'.north);
\node at ($(t)!0.5!(u)$) [anchor=center] {$\Rightarrow$};
\end{tikzpicture} \]
This is a kind of commutativity of production and consumption:
From the initial state~|s|, we can either
\begin{itemize}
\item apply~|g| to~|s| to \emph{produce}~|b| and reach a new state~|s'|, and then apply~|h| to \emph{consume} the list and update the state to~|h s'|, or
\item apply~|h| to \emph{consume} the list and update the state to~|h s|, and then apply~|g| to~|h s| to \emph{produce} an element and reach a new state.
\end{itemize}
If the first route is possible, the second route should also be possible, and the outcomes should be the same --- doing production using~|g| and consumption using~|h| in whichever order should emit the same element and reach the same final state.
This cannot be true in general, and should be formulated as a condition of the streaming algorithm.
However, this commutativity of |g|~and~|h| looks more like a derived consequence rather than a basic condition ---
it is commutativity of one step of production (using~|g|) and multiple steps of consumption (of the entire list, using~|h|), whereas the algorithm is specified in terms of |g|~and~|f|, which are single-step production and consumption, and it is more natural to require that |g|~and~|f| commute instead:
\[ \begin{tikzpicture}[x=12em,y=4em]
\node(x) [anchor=center] {|s|};
\node(x') [below=1 of x,anchor=center] {|s'|};
\node(hx) [right=1 of x,anchor=center] {|f s a|};
\node(hx') [right=1 of x',anchor=center] {|f s' a|};
\draw[serif cm-to] (x) edge node[above]{consume~|a| with~|f|} (hx);
\draw[serif cm-to] (x') edge node[below]{consume~|a| with~|f|} (hx');
\draw[serif cm-to] (x) edge node(t)[left]{produce~|b| with~|g|} (x ||- x'.north);
\draw[serif cm-to] (hx) edge node(u)[right]{produce~|b| with~|g|} (hx ||- hx'.north);
\node at ($(t)!0.5!(u)$) [anchor=center] {$\Rightarrow$};
\end{tikzpicture} \]
This is \varcitet{Gibbons-metamorphisms}{'s} \emph{streaming condition}, which is needed for proving the correctness of the streaming algorithm.
In our development of |stream|, we can assume that a proof of the streaming condition is available:
\begin{code}
streaming-condition :
  {a : A} {b : B} {s s' : S} → g s ≡ just (b , s') → g (f s a) ≡ just (b , f s' a)
\end{code}
Back to Goal~5, where we should prove the commutativity of |g|~and~|h|.
All it takes should be a straightforward induction to extend the streaming condition along the axis of consumption --- so straightforward that \Agda\ can do most of the work for us!
We know that we need a helper function |streaming-lemma| that performs induction on |as| and uses |eq| as a premise; by filling |streaming-lemma as eq| into Goal~5 and firing a command (\texttt{C-c C-h}), \Agda\ can generate a type for |streaming-lemma|, which, after removing some over-generalisations and unnecessary definition expansions, is:
\begin{code}
streaming-lemma :  {b : B} {s s' : S} {h : S → S} →
                   AlgList A (foldl-alg f) id h → g s ≡ just (b , s') → g (h s) ≡ just (b , h s')
streaming-lemma as eq = (GOAL(g (h s) ≡ just (b , h s'))(6))
\end{code}
\Agda\ then accepts |streaming-lemma as eq| as a type-correct term for Goal~5, completing the definition of |stream|:
\begin{code}
stream : {h : S → S} → AlgList A (foldl-alg f) id h → (s : S) → CoalgList B g (h s)
decon (stream as        s) with g s         | inspect g s
decon (stream []        s) | nothing        | [ eq ] = ⟨ eq ⟩
decon (stream (a ∷ as)  s) | nothing        | [ eq ] = decon (stream as (f s a))
decon (stream as        s) | just (b , s')  | [ eq ] = b ∷⟨ streaming-lemma as eq ⟩ stream as s'
\end{code}
Now all that is left is the body of |streaming-lemma| (Goal~6).
If we give a hint that case-splitting is needed (\texttt{-c}), Auto can complete the definition of |streaming-lemma| on its own, yielding (modulo one cosmetic variable renaming):
\begin{code}
streaming-lemma []        eq = eq
streaming-lemma (a ∷ as)  eq = streaming-lemma as (streaming-condition eq)
\end{code}

\section{Jigsaw Metamorphisms: Infinite Cases}

Back to the |foldr| version, but there is some problem with a definitional implementation.
\citet{Nakano-jigsaw}

Let |f : A → S → S|, |e : S|, |g : S → B × S|, and |piece : A × B → B × A|.

\subsection{Vertical Placement}

\begin{code}
jigsawᵢᵥ : {s : S} → AlgList A f e s → CoalgList B (just ∘ g) s
jigsawᵢᵥ as = (GOAL(CoalgList B (just ∘ g) s)(0))
\end{code}

\begin{code}
fillᵢᵥ : {s : S} → AlgList A f e s → B × Σ[ t ∈ S ] AlgList A f e t
fillᵢᵥ as = (GOAL'(B × Σ[ t ∈ S ] AlgList A f e t))

jigsawᵢᵥ : {s : S} → AlgList A f e s → CoalgList B (just ∘ g) s
decon (jigsawᵢᵥ as) with fillᵢᵥ as
decon (jigsawᵢᵥ as) | (b , t , as') = b ∷⟨ (GOAL(just (g s) ≡ just (b , t))(1)) ⟩ jigsawᵢᵥ as'
\end{code}

\begin{code}
fillᵢᵥ : {s : S} → AlgList A f e s → Σ[ b ∈ B ] Σ[ t ∈ S ] AlgList A f e t × g s ≡ (b , t)
fillᵢᵥ as = (GOAL(Σ[ b ∈ B ] Σ[ t ∈ S ] AlgList A f e t × g s ≡ (b , t))(2))

jigsawᵢᵥ : {s : S} → AlgList A f e s → CoalgList B (just ∘ g) s
decon (jigsawᵢᵥ as) with fillᵢᵥ as
decon (jigsawᵢᵥ as) | (b , _ , as' , eq) = b ∷⟨ cong just eq ⟩ jigsawᵢᵥ as'
\end{code}

\begin{code}
fillᵢᵥ []                            = (GOAL(Σ[ b ∈ B ] Σ[ t ∈ S ] AlgList A f e t × g e ≡ (b , t))(3))
fillᵢᵥ (a ∷ as(CXT(AlgList f e s)))  = (GOAL(Σ[ b ∈ B ] Σ[ t ∈ S ] AlgList A f e t × g (f a s) ≡ (b , t))(4))
\end{code}

\begin{code}
fillᵢᵥ [] = (flat-edge , _ , [] , (GOAL(g e ≡ (flat-edge , e))(5)))
\end{code}
for some constants |flat-edge : B| and |flat-edge-productionᵢ : g e ≡ (flat-edge , e)| (which discharges Goal~5).

\begin{code}
fillᵢᵥ (a ∷ as(CXT(AlgList f e s))  ) with fillᵢᵥ as
fillᵢᵥ (a ∷ as                      ) | (b , s' , as' , eq) =
  (GOAL(Σ[ b ∈ B ] Σ[ t ∈ S ] AlgList A f e t × g (f a s) ≡ (b , t))(6))
\end{code}

\begin{code}
fillᵢᵥ (a ∷ as(CXT(AlgList f e s))  ) with fillᵢᵥ as
fillᵢᵥ (a ∷ as                      ) | (b , s' , as' , eq(CXT(g s ≡ (b , s')))) =
  let (b' , a') = piece (a , b) in (b' , _ , a' ∷ as' , (GOAL(g (f a s) ≡ (b' , f a' s'))(7)))
\end{code}

\[ \begin{tikzpicture}[x=12em,y=4em]
\node(x) [anchor=center] {|s|};
\node(x') [below=1 of x,anchor=center] {|s'|};
\node(hx) [left=1 of x,anchor=center] {|f a s|};
\node(hx') [left=1 of x',anchor=center] {|f a' s'|};
\draw[serif cm-to] (x) edge node[above]{consume~|a| with~|f|} (hx);
\draw[serif cm-to] (x') edge node[below]{consume~|a'| with~|f|} (hx');
\draw[serif cm-to] (x) edge node(t)[right]{produce~|b| with~|g|} (x ||- x'.north);
\draw[serif cm-to] (hx) edge node(u)[left]{produce~|b'| with~|g|} (hx ||- hx'.north);
\node at ($(t)!0.5!(u)$) [anchor=center] {$\Leftarrow$};
\end{tikzpicture} \]

\begin{code}
jigsaw-conditionᵢ :  {a : A} {b : B} {s s' : S} →
                     g s ≡ (b , s') → let (b' , a') = piece (a , b) in g (f a s) ≡ (b' , f a' s')
\end{code}

\subsection{Horizontal Placement}

\begin{code}
jigsawᵢₕ : {s : S} → AlgList A f e s → CoalgList B (just ∘ g) s
jigsawᵢₕ as = (GOAL(CoalgList B (just ∘ g) s)(0))
\end{code}

\begin{code}
jigsawᵢₕ []                              = (GOAL(CoalgList B (just ∘ g) e)(1))
jigsawᵢₕ (a ∷ as(CXT(AlgList A f e s)))  = (GOAL(CoalgList B (just ∘ g) (f a s))(2))
\end{code}

\begin{code}
decon (jigsawᵢₕ []) = flat-edge ∷⟨ (GOAL(just (g e) ≡ just (flat-edge , e))(3)) ⟩ jigsawᵢₕ []
\end{code}

\begin{code}
jigsawᵢₕ (a ∷ as) = fillᵢₕ a (jigsawᵢₕ as)
\end{code}

\begin{code}
fillᵢₕ : {s : S} (a : A) → CoalgList B (just ∘ g) s → CoalgList B (just ∘ g) (f a s)
fillᵢₕ a bs = (GOAL(CoalgList B (just ∘ g) (f a s))(4))
\end{code}

\begin{code}
decon (fillᵢₕ a bs) with decon bs
decon (fillᵢₕ a bs) | ⟨ eq(CXT(just (g s) ≡ nothing)) ⟩ = (GOAL(CoalgListF B (just ∘ g) (f a s))(5))
decon (fillᵢₕ a bs) | b ∷⟨ eq(CXT(just (g s) ≡ just (b , s'))) ⟩ bs'(CXT(CoalgList B (just ∘ g) s')) =
  (GOAL(CoalgListF B (just ∘ g) (f a s))(6))
\end{code}

\begin{code}
decon (fillᵢₕ a bs) | ⟨ () ⟩
\end{code}

\begin{code}
decon (fillᵢₕ a bs) | b ∷⟨ eq(CXT(just (g s) ≡ just (b , s'))) ⟩ bs'(CXT(CoalgList B (just ∘ g) s')) =
  let (b' , a') = piece (a , b) in b' ∷⟨ (GOAL(just (g (f a s)) ≡ just (b' , f a' s'))(7)) ⟩ fillᵢₕ a' bs'
\end{code}

\section{Jigsaw Metamorphisms: Possibly Finite Cases}

\section{Discussion}

Asymmetric treatment of index equality of |AlgList| and |CoalgList|; ``green slime''~\citep{McBride-pivotal}; |AlgList| specialises the context, which is propagated into |CoalgList|, forming proof obligations.

\citet{McBride-pivotal} tries to hide the proofs; we try to use the proofs.

|CoalgList B g| is interesting when its elements are actually computed by mechanisms other than~|g|.
Index-level order of computation may differ from the data-level order (traditional vs index-first inductive families; there is probably a similar story for coinductive families).
Relationship with \citet{Thibodeau-indexed-codata-types}.

It is not just reducing the activity of program design to type design and good type inhabitation algorithms --- types do not determine programs.
Correctness concerns are moved into the types and enforced, but the programmer still gets to make decisions about algorithmic details.

It is interesting to compare our implementation with the proofs of \citet{Bird-arithmetic-coding}.
While their Lemma~29 turns explicitly into our |streaming-lemma|, their Theorem~30 goes implicitly into the typing of |stream| and no longer needs special attention.
The structure of |stream| already matches that of \citeauthor{Bird-arithmetic-coding}'s proof of their Theorem~30, and the principled type design using algebraic ornamentation elegantly loads the proof onto the structure of |stream|.

Intermediate variable conjecture (comparison with extrinsic proofs)

Contrast with verification condition extraction

Extensional properties vs intensional design

Generality? Perhaps not much. For example, ``metaphorisms''~\citep{Oliveira-metaphorisms} --- optimising metamorphisms --- will probably need a more involved development similar to \varcitet{Ko-algOrn}{'s}.

%% Acknowledgements
\begin{acks}                            %% acks environment is optional
                                        %% contents suppressed with 'anonymous'
  %% Commands \grantsponsor{<sponsorID>}{<name>}{<url>} and
  %% \grantnum[<url>]{<sponsorID>}{<number>} should be used to
  %% acknowledge financial support and will be used by metadata
  %% extraction tools.
Jeremy Gibbons and Shin-Cheng Mu for discussions in Oxford.
This work originated from the author's DPhil work at Oxford~\citep{Ko-thesis}, which was supported by a University of Oxford Clarendon Scholarship and the UK Engineering and Physical Sciences Research Council (EPSRC) project \textit{Reusability and Dependent Types}.
After the author moved to NII, the work continued with the support of the \grantsponsor{GS501100001691}{Japan Society for the Promotion of Science}{https://doi.org/10.13039/501100001691} (JSPS) Grant-in-Aid for Scientific Research (A)~No.~\grantnum{GS501100001691}{25240009} and (S)~No.~\grantnum{GS501100001691}{17H06099}.
\end{acks}

%% Bibliography
\bibliography{../bib}


%% Appendix
%\appendix
%\section{Appendix}
%
%Text of appendix \ldots

\end{document}