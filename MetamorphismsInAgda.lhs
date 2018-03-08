%% For double-blind review submission
%\documentclass[acmsmall,review,anonymous]{acmart}\settopmatter{printfolios=true}
%% For single-blind review submission
\documentclass[acmsmall,review]{acmart}\settopmatter{printfolios=true}
%% For final camera-ready submission
%\documentclass[acmsmall]{acmart}\settopmatter{}

%% Note: Authors migrating a paper from PACMPL format to traditional
%% SIGPLAN proceedings format should change 'acmlarge' to
%% 'sigplan,10pt'.

%include agda.fmt

%subst keyword a = "\keyword{" a "}"
%subst conid a = "\identifier{" a "}"
%subst varid a = "\identifier{" a "}"
%subst numeral a = "\mathbf{" a "}"
%format : = "{:}"
%format LETEQ = "{=}"
%format Set = "\constructor{Set}"
%format DOT = ".\kern-3pt"
%format (GOAL(t)(i)) = "\highlight{goal}{\textbf\{\," t "\,\textbf\}_{\kern1pt" i "}}"
%format (GOAL'(t)) = "\highlight{goal}{\textbf\{\," t "\,\textbf\}}"
%format (CXT(t)) = "\kern-2pt_{\highlight{cxt}{" t "}}"
%format constant ="\keyword{constant}"

%format ◁ = "{\kern-.25pt\lhd\kern.25pt}"
%format _◁_ = _ ◁ _
%format ▷ = "{\kern.5pt\rhd\kern-.5pt}"
%format _▷_ = _ ▷ _
%format Rational = "\mathbb{Q}"
%format Nat = "\mathbb{N}"
%format S_C = "S_\mathrm{\kern.5ptC}"
%format ▷ᶜ = "\kern.5pt{\rhd}_\mathrm{C}\kern-.5pt"
%format _▷ᶜ_ = _ ▷ᶜ _
%format g_C = "g_\mathrm{\kern.5ptC}"
%format g_C' = "g_\mathrm{\kern.5ptC}^\prime"
%format e_C = "\identifier{e}_\mathrm{C}"
%format if = "\keyword{if}"
%format then = "\keyword{then}"
%format else = "\keyword{else}"
%format Val = "\constructor{Val}"
%format Heap = "\constructor{Heap}"
%format refl = "\constructor{refl}"
%format × = "{×}"
%format , = "\kern-1pt,"
%format inj₁ = "\constructor{inj_1}"
%format inj₂ = "\constructor{inj_2}"
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
%format jigsaw-conditionᵢ = "\identifier{jigsaw-condition_\mathrm{\,I}}"
%format jigsawᵢₕ = "\identifier{jigsaw_\mathrm{\,IH}}"
%format fillᵢₕ = "\identifier{fill_\mathrm{\,IH}}"
%format INF = "\infty"
%format g∞ = "\identifier{g}^\infty"
%format flat? = "\identifier{flat}^?"

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

%\newcommand{\varref}[2]{\hyperref[#2]{#1~\ref*{#2}}}

%% Some recommended packages.
\usepackage{booktabs}   %% For formal tables:
                        %% http://ctan.org/pkg/booktabs
\usepackage{subcaption} %% For complex figures with subfigures/subcaptions
                        %% http://ctan.org/pkg/subcaption

\usepackage{mathtools}
\usepackage{nicefrac}
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

\newcommand{\varparagraph}[1]{\par\ensuremath{\blacktriangleright}~\textit{#1}\hspace{.5em}} % {\textit{#1}\hspace{.5em}}
\newcommand{\awa}[2]{\mathrlap{#2}\phantom{#1}} % as wide as
\newcommand{\varawa}[2]{\phantom{#1}\mathllap{#2}}
\newcommand{\varcitet}[3][]{\citeauthor{#2}#3~[\ifthenelse{\isempty{#1}}{\citeyear{#2}}{\citeyear[#1]{#2}}]}

\newcommand{\beforefigurecode}{\setlength{\mathindent}{0em}}

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
\title[Programming Metamorphic Algorithms in Agda   (Functional Pearl)]
      {Programming Metamorphic Algorithms in Agda\\ (Functional Pearl)}
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
\orcid{0000-0002-2439-1048}            %% \orcid is optional
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
\label{sec:intro}

Why do we want to program with full dependent types?
For larger-scale proofs, writing proof terms in a dependently typed language is usually much less efficient than working with a proof assistant with decent automation.
What has been more successful with dependently typed programming (DTP) --- in particular with the use of indexed datatypes --- is intrinsic hygienic guarantees, which tend to work better for smaller, hand-crafted programs: if we need to, for example, track the bounds of indices or work with well-typed syntax trees, let us encode bound and typing constraints in the datatypes of indices and syntax trees so that the type system can help the programmer to enforce the constraints.
But this is achievable with automated proof assistants, and does not make DTP truly shine --- the most fascinating aspect of DTP is the prospect that intrinsic typing can provide semantic hints to the programmer during an interactive development process, so that the heavy typing becomes a worthwhile asset rather than an unnecessary burden.

\todo[inline]{In exchange for this kind of guarantee, though\ldots}

\todo[inline]{Agda 2.5.2 with Standard Library version 0.13}

\section{Metamorphisms}
\label{sec:metamorphisms}

A \emph{metamorphism}~\citep{Gibbons-metamorphisms} consumes a data structure to compute an intermediate value and then produces a new data structure using the intermediate value as the seed.
Like \citet{Gibbons-metamorphisms}, we will focus on \emph{list metamorphisms}, i.e., metamorphisms consuming and producing lists.
Two of the examples of list metamorphisms given by \citet{Gibbons-metamorphisms} are:
\begin{itemize}
\item \emph{Base conversion for fractions}: A list of digits representing a fractional number in a particular base (e.g., $0.625_{10}$) can be converted to another list of digits in a different base (e.g., $0.101_2$).
The conversion is a metamorphism because we can consume an input list of digits to compute the value represented by the list, and then produce an output list of digits representing the same value.
Note that even when the input list is finite, the output list may have to be infinite --- $0.1_3 = 0.\overline{3}_{10}$, for example.
\item \emph{Heapsort}: An input list of numbers is consumed by pushing every element into a min-heap (priority queue), from which we then pop all the elements, from the smallest to the largest, producing a sorted output list.
\end{itemize}
%We will use these two examples to provide more intuition in the rest of this paper.

\varparagraph{Lists for consumption.}
Formally, a metamorphism is a \emph{fold} followed by an \emph{unfold}, the former consuming a finite data structure and the latter producing a potentially infinite codata structure.
For list metamorphisms, the inputs to be consumed are the standard finite lists:
\begin{code}
data List (A : Set) : Set where
  []   : List A
  _∷_  : A → List A → List A
\end{code}
The |foldr| operator subsumes the elements (of type~|A|) of a list into a state (of type~|S|) using a ``right algebra'' |(◁) : A → S → S| and an initial (empty) state |e : S|:%
\footnote{In \Agda, a name with underscores like~|_∷_| can be used as an operator, and the underscores indicate where the arguments go.
As an exception, we often write a binary infix operator like~|_◁_| in \name{Haskell} syntax like |(◁)|.
Also, in the type of a function, arguments wrapped in curly brackets are implicit, and can be left out (if they are inferable by \Agda) when applying the function.}
\begin{code}
foldr : {A S : Set} → (A → S → S) → S → List A → S
foldr (◁) e []        = e
foldr (◁) e (a ∷ as)  = a ◁ foldr f e as
\end{code}
With |foldr|, a list is consumed from the right (cf.~wind direction).
Dually, the |foldl| operator consumes a list from the left using a ``left algebra'' |(▷) : S → A → S|:
\begin{code}
foldl : {A S : Set} → (S → A → S) → S → List A → S
foldl (▷) e []        = e
foldl (▷) e (a ∷ as)  = foldl (▷) (e ▷ a) as
\end{code}
A list metamorphism can use either |foldr| or |foldl| in its consuming part, and we will see both kinds in the paper.
We will refer to a list metamorphism using |foldr| as a ``right metamorphism'', and one using |foldl| as a ``left metamorphism''.

\varparagraph{Colists for production.}
For the producing part of list metamorphisms, where we need to produce potentially infinite lists, in a total language like \Agda\ we can no longer use |List|, whose elements are necessarily finite; instead, we should switch to a \emph{codatatype} of \emph{colists}, which are potentially infinite.
Dual to a datatype, which is defined by all the possible ways to \emph{construct} its elements, a codatatype is defined by all the possible ways to \emph{deconstruct} (or \emph{observe}) its elements.
For a colist, we only need one way of deconstruction: exposing the colist's outermost structure, which is either empty or a pair of a head element and a tail colist.
In \Agda\ this can be expressed as a coinductive record type |CoList| with only one field, which is a sum (empty or non-empty) structure; for cosmetic reasons, this sum structure is defined (mutually recursively with |CoList|) as a datatype |CoListF|:
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
Note that |decon| denotes a projection function of type |{B : Set} → CoList B → CoListF B|, and plays the role of the deconstructor of |CoList|.
Now we can define the standard |unfoldr| operator, which uses a coalgebra |g : S → Maybe (B × S)| to unfold a colist from a given state:
\begin{code}
unfoldr : {B S : Set} → (S → Maybe (B × S)) → S → CoList B
decon (unfoldr g s) with g s
decon (unfoldr g s) | nothing        = []
decon (unfoldr g s) | just (b , s')  = b ∷ unfoldr g s'
\end{code}
The operator is defined with copattern matching~\citep{Abel-copatterns}:
To define |unfoldr g s|, which is a colist, we need to specify what will result if we deconstruct it, i.e., what |decon (unfoldr g s)| will compute to.
This depends on whether |g|~can produce anything from~|s|, so, using the |with| construct, we introduce |g s| as an additional ``argument'', on which we can then perform a pattern match.
If |g s| is |nothing|, then the resulting colist will be empty --- that is, |decon (unfoldr g s)| will compute to |[]|;
otherwise, |g s| is |just (b , s')| for some |b|~and~|s'|, and the resulting colist will have |b|~as its head and |unfoldr g s'| as its tail --- that is, |decon (unfoldr g s)| will compute to |b ∷ unfoldr g s'|.

To be more concrete, let us describe our two examples --- base conversion for fractions and heapsort --- explicitly as metamorphisms.

\varparagraph{Base conversion for fractions.}
Suppose that the input and output bases are |b_i : Nat| and |b_o : Nat| --- in $0.625_{10} = 0.101_2$, for example, $b_i = 10$ and $b_o = 2$.
We represent fractions as (co)lists of digits (of type~|Nat|) starting from the most significant digit --- for example, $0.625$ is represented as |{-"6\;"-} ∷ {-"2\;"-} ∷ {-"5\;"-} ∷ []|.
To make the story short later,%
\footnote{\citet[Section~4.2]{Gibbons-metamorphisms} gives a more complete story, where base conversion for fractions is first described as a right metamorphism with simple states (consisting of only an accumulator), and then transformed to a left metamorphism with more complex states.}
we describe base conversion for fractions as a left metamorphism:
\begin{code}
unfoldr g_C ∘ foldl _▷ᶜ_ e_C
\end{code}
where the state type is |S_C LETEQ Rational × Rational × Rational|, which are triples of the form |(v , w_i , w_o)| where |v|~is an accumulator, |w_i| the weight of the incoming input digit, and |w_o| the weight of the outgoing output digit.
The initial (empty) state |e_C| is |({-"0\;"-} , {-"\nicefrac{1}{\identifier{b_i}}\;"-} , {-"\;\nicefrac{1}{\identifier{b_o}}"-})|.
The left algebra~|(▷ᶜ)| adds the the product of the current input digit and its weight to the accumulator, and updates the input weight in preparation for the next input digit:
\begin{code}
(▷ᶜ) : S_C → Nat → S_C
(v , w_i , w_o) ▷ᶜ d = ({-"\identifier{v} + d \times w_i\;"-} , {-"\nicefrac{w_i}{b_i}\;"-}, w_o)
\end{code}
while the coalgebra~|g_C| produces an output digit and updates the accumulator and the next output weight if the accumulator is not yet zero:
\begin{code}
g_C (v , w_i , w_o) =  let  d  LETEQ {-"\;\lfloor\nicefrac{\identifier{v}\kern1pt}{\identifier{w_o}}\rfloor"-}; r  LETEQ {-"\;\identifier{v} - d \times \identifier{w_o}"-}
                       in   if {-"\identifier{v} > 0\;"-} then  just (d , (r , w_i , {-"\;\nicefrac{\identifier{w_o}\kern1pt}{\identifier{b_o}}"-})) else  nothing
\end{code}
For the example $0.625_{10} = 0.101_2$, the metamorphism first consumes the input digits using~|(▷ᶜ)|:
\[ (0\,,\;0.1\,,\;0.5) ~\stackrel{6}{\mapsto}~ (0.6\,,\;0.01\,,\;0.5) ~\stackrel{2}{\mapsto}~ (0.62\,,\;0.001\,,\;0.5) ~\stackrel{5}{\mapsto}~ (0.625\,,\;0.0001\,,\;0.5) \]
and then produces the output digits using~|g_C|:
\[ (0.625\,,\;10^{-4}\,,\;0.5) ~\stackrel{1}{\mapsto}~ (0.125\,,\;10^{-4}\,,\;0.25) ~\stackrel{0}{\mapsto}~ (0.125\,,\;10^{-4}\,,\;0.125) ~\stackrel{1}{\mapsto}~ (0\,,\;10^{-4}\,,\;0.0625) ~\not\mapsto \]

\varparagraph{Heapsort.}
Let |Heap| be an abstract type of min-heaps on some totally ordered set |Val|, equipped with three operations:
\begin{code}
empty   : Heap
push    : Val → Heap → Heap
popMin  : Heap → Maybe (Val × Heap)
\end{code}
where |empty| is the empty heap, |push| adds an element into a heap, and |popMin| returns a minimum element and the rest of the input heap if and only if the input heap is non-empty.
Then heapsort can be directly described as a right metamorphism:
\begin{code}
unfoldr popMin ∘ foldr push empty
\end{code}

\section{Specification of Metamorphisms in Types}
\label{sec:spec}

In the rest of this paper we will develop several \emph{metamorphic algorithms}, which compute a metamorphism but do not take the form of a fold followed by an unfold.
Rather than proving that these algorithms satisfy their metamorphic specifications, we will encode metamorphic specifications in types, such that any type-checked program is a correct metamorphic algorithm.

The encoding is based on \varcitet{McBride-ornaments}{'s} \emph{algebraic ornamentation}.
Given a right algebra |(◁) : A → S → S| and |e : S|, we can partition |List A| into a family of types |AlgList A f e : S → Set| indexed by~|S| such that (conceptually) every list~|as| falls into the type |AlgList A f e (foldr (◁) e as)|.
The definition of |AlgList| is obtained by ``fusing'' |foldr| into |List|:
\begin{code}
data AlgList (A {S} : Set) ((◁) : A → S → S) (e : S) : S → Set where
  []   : AlgList A (◁) e e
  _∷_  : (a : A) → {s : S} → AlgList A (◁) e s → AlgList A (◁) e (a ◁ s)
\end{code}
The empty list is classified under the index |e LETEQ foldr f e []|.
For the cons case, if a tail~|as| is classified under~|s|, meaning that |foldr (◁) e as LETEQ s|, then the whole list |a ∷ as| should be classified under |a ◁ s| since |foldr (◁) e (a ∷ as) = a ◁ foldr (◁) e as = a ◁ s|.

Dually, given a coalgebra |g : S → Maybe (B × S)|, we can partition |CoList B| into a family of types |CoalgList B g : S → Set| such that a colist falls into |CoalgList B g s| if it is unfolded from~|s| using~|g|.
(Note that, extensionally, every |CoalgList B g s| has exactly one inhabitant; intensionally there may be different ways to describe/compute that inhabitant, though.)
Again the definition of |CoalgList| is obtained by fusing |unfoldr| into |CoList|:
\begin{code}
mutual

  record CoalgList (B {S} : Set) (g : S → Maybe (B × S)) (s : S) : Set where
    coinductive
    field
      decon : CoalgListF B g s

  data CoalgListF (B {S} : Set) (g : S → Maybe (B × S)) : S → Set where
    ⟨_⟩     : {s : S} → g s ≡ nothing → CoalgListF B g s
    _∷⟨_⟩_  : (b : B) → {s s' : S} → g s ≡ just (b , s') → CoalgList B g s' → CoalgListF B g s
\end{code}
Deconstructing a colist of type |CoalgList B g s| can lead to two possible outcomes: the colist can be empty, in which case we also get an equality proof that |g s| is |nothing|, or it can be non-empty, in which case we know that |g s| produces the head element, and that the tail colist is unfolded from the next state~|s'| produced by |g s|.

\varparagraph{Right metamorphisms.}
Let |A|, |B|, |S : Set| throughout the rest of this paper%
\footnote{That is, think of the code in the rest of this paper as contained in a module with parameters |A|, |B|, |S : Set|.}
--- we will assume that |A|~is the type of input elements, |B|~the type of output elements, and |S|~the type of states.
We will also consistently let |(◁) : A → S → S| denote a right algebra, |(▷) : S → A → S| a left algebra, |e : S| an initial (empty) state, and |g : S → Maybe (B × S)| a coalgebra.
Now any program of type:
\begin{code}
{s : S} → AlgList A (◁) e s → CoalgList B g s
\end{code}
implements the right metamorphism |unfoldr g ∘ foldr (◁) e|, since the indexing enforces that the input list folds to~|s|, from which the output colist is then unfolded.

\varparagraph{Left metamorphisms.}
What about left metamorphisms?
Thankfully, we do not need to define another variant of |AlgList| due to an old trick that expresses |foldl| in terms of |foldr|.
Given a list |as : List A|, think of the work of |foldl (▷) e as| as (i)~partially applying |flip (▷) : A → S → S| (where |flip f x y LETEQ f y x|) to every element of~|as| to obtain state transformations of type |S → S|, (ii)~composing the state transformations from left to right, and finally (iii)~applying the resulting composite transformation to~|e|.
The left-to-right order appears only in step~(ii), which, in fact, can also be performed from right to left since function composition is associative.
Formally, we have:
\begin{code}
foldl (▷) e as = foldr (left-alg (▷)) id as e
\end{code}
where
\begin{code}
left-alg : {A S : Set} → (S → A → S) → A → (S → S) → (S → S)
left-alg (▷) a t = t ∘ flip (▷) a
\end{code}
The type of left metamorphic algorithms can then be specified as:
\begin{code}
(s : S) → {h : S → S} → AlgList A (left-alg (▷)) id h → CoalgList B g (h s)
\end{code}
which says that if the initial state is~|s| and the input list folds to a state transformation~|h|, then the output colist should be unfolded from |h s|.

\section{Definitional Implementation of Metamorphisms}
\label{sec:cbp}

To warm up, let us start from the left metamorphic type and implement the most straightforward algorithm that strictly follows the definition of metamorphisms, \textbf{c}onsuming all inputs \textbf{b}efore \textbf{p}roducing outputs:
\begin{code}
cbp : (s : S) → {h : S → S} → AlgList A (left-alg (▷)) id h → CoalgList B g (h s)
cbp s as(CXT(AlgList A (left-alg (▷)) id h)) = (GOAL(CoalgList B g (h s))(0))
\end{code}
\Agda\ provides an interactive development environment as an emacs mode.
In this environment, we can leave ``holes'' in programs and fill or refine them, often with \Agda's help.
Such a hole is called an \emph{interaction point} or a \emph{goal}, of which the \highlight{goal}{\text{green-shaded part}} above is an example.
At goals, \Agda\ can be instructed to provide various information and even perform some program synthesis.
One most important piece of information for a goal is its expected type, which we always display in curly brackets.
Goals are numbered so they can be referred to in the text.
At goals, we can also query the types of the variables in scope; whenever the type of a variable needs to be displayed, we will annotate the variable with its type in \highlight{cxt}{\text{yellow-shaded subscript}} (which is not part of the program text).
In the program above, we annotate~|as| with its type because the expected type at Goal~0 refers to~|h|, which is the index in the type of~|as|.

Now let us try to develop the program.
We are trying to consume the input list first, so we pattern match on the argument |as| to see if there is anything to consume.
In \Agda\ this is as easy as putting |as| into Goal~0 and firing a ``case splitting'' command (\texttt{C-c C-c}); the program will then be split into two clauses, listing all possible cases of~|as|:
\begin{code}
cbp : (s : S) → {h : S → S} → AlgList A (left-alg (▷)) id h → CoalgList B g (h s)
cbp s []                                            = (GOAL(CoalgList B g s)(1))
cbp s (a ∷ as(CXT(AlgList A (left-alg (▷)) id h)))  = (GOAL(CoalgList B g (h (s ▷ a)))(2))
\end{code}
Now Goal~0 is gone, and two new goals appear.
Note that the expected types of the two new goals have changed: at Goal~1, for example, we see that the output colist should be unfolded directly from the initial state~|s| since the input list is empty.
By providing sufficient type information, \Agda\ can keep track of such relationship for us!
We continue to interact with and refine these two new goals.

If there is something to consume, that is, the input list is non-empty, we go into Goal~2, where we keep consuming the tail |as| but from a new state:
\begin{code}
cbp : (s : S) → {h : S → S} → AlgList A (left-alg (▷)) id h → CoalgList B g (h s)
cbp s []        = (GOAL(CoalgList B g s)(1))
cbp s (a ∷ as)  = cbp (GOAL(S)(3)) as
\end{code}
What is this new state? It should be the one obtained by subsuming~|a| into~|s|, i.e., |s ▷ a|.
\Agda\ knows this too, in fact --- firing the ``Auto'' command (\texttt{C-c C-a}) at Goal~3 yields:
\begin{code}
cbp : (s : S) → {h : S → S} → AlgList A (left-alg (▷)) id h → CoalgList B g (h s)
cbp s []        = (GOAL(CoalgList B g s)(1))
cbp s (a ∷ as)  = cbp (s ▷ a) as
\end{code}

If there is nothing more to consume, that is, the input list is empty, we go into Goal~1, where we should produce the output colist, to specify which we should say what will result if we |decon|struct the colist.
That is, we perform a copattern match (which can be done by \Agda\ if we give it the case splitting command (\texttt{C-c C-c}) without specifying a variable):
\begin{code}
cbp : (s : S) → {h : S → S} → AlgList A (left-alg (▷)) id h → CoalgList B g (h s)
decon (cbp s []) = (GOAL(CoalgListF B g s)(4))
cbp s (a ∷ as) = cbp (s ▷ a) as
\end{code}
The result of deconstruction depends on whether |g|~can produce anything from the current state~|s|, so we pattern match on |g s|, splitting Goal~4 into:
\begin{code}
cbp : (s : S) → {h : S → S} → AlgList A (left-alg (▷)) id h → CoalgList B g (h s)
decon (cbp s []) with g s
decon (cbp s []) | nothing        = (GOAL(CoalgListF B g s)(5))
decon (cbp s []) | just (b , s')  = (GOAL(CoalgListF B g s)(6))
cbp s (a ∷ as) = cbp (s ▷ a) as
\end{code}
If |g s| is |nothing| (Goal~5), the output colist is empty; otherwise |g s| is some |just (b , s')| (Goal~6), in which case we use~|b| as the head and go on to produce the tail from~|s'|.
We therefore refine the two goals into:
\begin{code}
cbp : (s : S) → {h : S → S} → AlgList A (left-alg (▷)) id h → CoalgList B g (h s)
decon (cbp s []) with g s
decon (cbp s []) | nothing        = ⟨ (GOAL(g s ≡ nothing)(7)) ⟩
decon (cbp s []) | just (b , s')  = b ∷⟨ (GOAL(g s ≡ just (b , s'))(8)) ⟩ cbp s' []
cbp s (a ∷ as) = cbp (s ▷ a) as
\end{code}

We are now required to discharge equality proof obligations about |g s|, and the obligations exactly correspond to the results of the |with|-matching.
This is precisely a situation in which the |inspect| idiom of the \Agda\ standard library can help: with |inspect|, we can obtain an equality proof of the right type in each of the cases of the |with|-matching.
We therefore obtain:
\begin{code}
cbp : (s : S) → {h : S → S} → AlgList A (left-alg (▷)) id h → CoalgList B g (h s)
decon (cbp s []) with g s         | inspect g s
decon (cbp s []) | nothing        | [ eq(CXT(g s ≡ nothing))        ] = ⟨ (GOAL(g s ≡ nothing)(7)) ⟩
decon (cbp s []) | just (b , s')  | [ eq(CXT(g s ≡ just (b , s')))  ] = b ∷⟨ (GOAL(g s ≡ just (b , s'))(8)) ⟩ cbp s' []
cbp s (a ∷ as) = cbp (s ▷ a) as
\end{code}
Both goals can now be discharged with |eq|, and we arrive at a complete program, shown in \autoref{fig:cbp}.
As explained in \autoref{sec:spec}, this program is a correct metamorphic algorithm because it type-checks.

\begin{figure}
\beforefigurecode
\begin{code}
module ConsumingBeforeProducing
  ((▷) : S → A → S) (g : S → Maybe (B × S))
  where

  cbp : (s : S) → {h : S → S} → AlgList A (left-alg (▷)) id h → CoalgList B g (h s)
  decon (cbp s []) with g s         | inspect g s
  decon (cbp s []) | nothing        | [ eq ] = ⟨ eq ⟩
  decon (cbp s []) | just (b , s')  | [ eq ] = b ∷⟨ eq ⟩ cbp s' []
  cbp s (a ∷ as) = cbp (s ▷ a) as
\end{code}
\caption{Definitional implementation of metamorphisms}
\label{fig:cbp}
\end{figure}

\section{Streaming Metamorphisms}
\label{sec:streaming}

As \citet{Gibbons-metamorphisms} noted, (list) metamorphisms in general cannot be automatically optimised in terms of time and space, but in some cases it is possible to compute a list metamorphism using a \emph{streaming algorithm}, which can produce an initial segment of the output colist from an initial segment of the input list.
For example, when converting $0.625_{10}$ to $0.101_2$, after consuming the first decimal digit~$6$ and reaching the state $(0.6\,,\;0.01\,,\;0.5)$, we can directly produce the first binary digit~$1$ because we know that the number will definitely be greater than $0.5$.
Streaming is not always possible, of course.
Heapsort is a counterexample: no matter how many input elements have been consumed, it is always possible that a minimum element --- which should be the first output element --- has yet to appear, and thus we can never produce the first output element before we see the whole input list.
There should be some condition under which we can stream metamorphisms, and we should be able to discover such condition if we program a streaming algorithm together with \Agda, which knows what metamorphisms are and can provide us with semantic hints regarding what conditions need to be introduced to make the program a valid metamorphic algorithm.

%\[ \begin{tikzpicture}[x=2.5em,y=2em]
%\node(0) {$(0\,,\;10^{-1}\,,\;0.5)$};
%\node(6) [right=1 of 0] {$(0.6\,,\;10^{-2}\,,\;0.5)$};
%\node(62) [right=1 of 6] {$(0.62\,,\;10^{-3}\,,\;0.5)$};
%\node(625) [right=1 of 62] {$(0.625\,,\;10^{-4}\,,\;0.5)$};
%
%\draw[serif cm-to] (0) edge node[above]{$6$} (6);
%\draw[serif cm-to] (6) edge node[above]{$2$} (62);
%\draw[serif cm-to] (62) edge node[above]{$5$} (625);
%
%\node(125) [below=1 of 625] {$(0.125\,,\;10^{-4}\,,\;0.25)$};
%\node(125') [below=1 of 125] {$(0.125\,,\;10^{-4}\,,\;0.125)$};
%\node(0') [below=1 of 125'] {$(0\,,\;10^{-4}\,,\;0.0625)$};
%
%\draw[serif cm-to] (625) edge node[right]{$1$} (125);
%\draw[serif cm-to] (125) edge node[right]{$0$} (125');
%\draw[serif cm-to] (125') edge node[right]{$1$} (0');
%
%\node(1) [below=1 of 6] {$(0.1\,,\;10^{-2}\,,\;0.25)$};
%\node(1') [below=1 of 1] {$(0.1\,,\;10^{-2}\,,\;0.125)$};
%\node(12) at ($(1')!0.5!(125')$) {$(0.12\,,\;10^{-3}\,,\;0.125)$};
%
%\draw[serif cm-to] (6) edge node[right]{$1$} (1);
%\draw[serif cm-to] (1) edge node[right]{$0$} (1');
%\draw[serif cm-to] (1') edge node[above]{$2$} (12);
%\draw[serif cm-to] (12) edge node[above]{$5$} (125');
%\end{tikzpicture} \]

We start from the same left metamorphic type:
\begin{code}
stream : (s : S) → {h : S → S} → AlgList A (left-alg (▷)) id h → CoalgList B g (h s)
stream s as(CXT(AlgList A (left-alg (▷)) id h)) = (GOAL(CoalgList B g (h s))(0))
\end{code}
Different from |cbp| (\autoref{sec:cbp}/\autoref{fig:cbp}), this time we try to produce using~|g| whenever possible, so our first step is to pattern match on |g s| (and we also introduce |decon| and |inspect|, which will be needed like in |cbp|):
\begin{code}
stream : (s : S) → {h : S → S} → AlgList A (left-alg (▷)) id h → CoalgList B g (h s)
decon (stream s as(CXT(AlgList A (left-alg (▷)) id h))  ) with g s         | inspect g s
decon (stream s as                                      ) | nothing        | [ eq ] = (GOAL(CoalgListF B g (h s))(1))
decon (stream s as                                      ) | just (b , s')  | [ eq ] = (GOAL(CoalgListF B g (h s))(2))
\end{code}

For Goal~1, we cannot produce anything since |g s| is |nothing|, but this does not mean that the output colist is empty --- we may be able to produce something once we consume the input list and advance to a new state.
We therefore pattern match on the input list:
\begin{code}
stream : (s : S) → {h : S → S} → AlgList A (left-alg (▷)) id h → CoalgList B g (h s)
decon (stream s as                                            )  with g s         | inspect g s
decon (stream s []                                            )  | nothing        | [ eq ] = (GOAL(CoalgListF B g s)(3))
decon (stream s (a ∷ as(CXT(AlgList A (left-alg (▷)) id h)))  )  | nothing        | [ eq ] =
{-"\hfill"-} (GOAL(CoalgListF B g (h (s ▷ a)))(4))
decon (stream s as                                            )  | just (b , s')  | [ eq ] =
{-"\hfill"-} (GOAL(CoalgListF B g (h s))(2))
\end{code}
These two goals are similar to what we have seen in |cbp|.
At Goal~3, there is nothing more in the input list to consume, so we should end production and emit an empty colist, while for Goal~4 we should advance to the new state |s ▷ a| and set the tail |as| as the list to be consumed next:
\begin{code}
stream : (s : S) → {h : S → S} → AlgList A (left-alg (▷)) id h → CoalgList B g (h s)
decon (stream s as        )  with g s        | inspect g s
decon (stream s []        ) | nothing        | [ eq ] = ⟨ eq ⟩
decon (stream s (a ∷ as)  ) | nothing        | [ eq ] = decon (stream (s ▷ a) as)
decon (stream s as        ) | just (b , s')  | [ eq ] = (GOAL(CoalgListF B g (h s))(2))
\end{code}

Goal~2 is the interesting case.
Using~|g|, from the current state~|s| we can produce~|b|, which we set as the head of the output colist, and advance to a new state~|s'|, from which we produce the tail of the colist:
\begin{code}
stream : (s : S) → {h : S → S} → AlgList A (left-alg (▷)) id h → CoalgList B g (h s)
decon (stream s as                                    ) with g s         | inspect g s
decon (stream s []                                    ) | nothing        | [ eq ] = ⟨ eq ⟩
decon (stream s (a ∷ as)                              ) | nothing        | [ eq ] = decon (stream (s ▷ a) as)
decon (stream s as(CXT(AlgList A (left-alg f) id h))  ) | just (b , s')  | [ eq(CXT(g s ≡ just (b , s'))) ] =
{-"\hfill"-} b ∷⟨ (GOAL(g (h s) ≡ just (b , h s'))(5)) ⟩ stream s' as
\end{code}

\varparagraph{The streaming condition.}
Now we get a non-trivial proof obligation (Goal~5) --- what does it mean?
The left-hand side |g (h s)| is trying to produce using~|g| from the state |h s|, where |h|~is the state transformation function resulting from consuming the entire input list~|as| (since |h|~is the index in the type of~|as|), and the whole equality says that this has to produce a specific result.
Drawing this as a state transition diagram:
\[ \begin{tikzpicture}[x=12em,y=4em]
\node(x) [anchor=center] {|s|};
\node(x') [below=1 of x,anchor=center] {\phantom{|s'|}};
\node(hx) [right=1 of x,anchor=center] {|h s|};
\node(hx') [right=1 of x',anchor=center] {|h s'|};
\draw[serif cm-to] (x) edge node[above]{consume~|as| using~|h|} (hx);
%\draw[serif cm-to] (x') edge node[below]{consume~|as| using~|h|} (hx');
%\draw[serif cm-to] (x) edge node(t)[left]{produce~|b| using~|g|} (x ||- x'.north);
\draw[serif cm-to] (hx) edge node(u)[right]{\rlap{produce~|b| using~|g|}} (hx ||- hx'.north);
%\node at ($(t)!0.5!(u)$) [anchor=center] {$\Rightarrow$};
\end{tikzpicture} \]
We already have in the context a similar-looking equality, namely |eq : g s ≡ just (b , s')|, which we can superimpose on the diagram:
\[ \begin{tikzpicture}[x=12em,y=4em]
\node(x) [anchor=center] {|s|};
\node(x') [below=1 of x,anchor=center] {|s'|};
\node(hx) [right=1 of x,anchor=center] {|h s|};
\node(hx') [right=1 of x',anchor=center] {|h s'|};
\draw[serif cm-to] (x) edge node[above]{consume~|as| using~|h|} (hx);
%\draw[serif cm-to] (x') edge node[below]{consume~|as| using~|h|} (hx');
\draw[serif cm-to] (x) edge node(t)[left]{produce~|b| using~|g|} (x ||- x'.north);
\draw[serif cm-to] (hx) edge node(u)[right]{produce~|b| using~|g|} (hx ||- hx'.north);
\node at ($(t)!0.5!(u)$) [anchor=center] {$\Rightarrow$};
\end{tikzpicture} \]
We also put in an implication arrow to indicate more explicitly that |g s ≡ just (b , s')| is a premise, from which we should derive |g (h s) ≡ just (b , h s')|.
Now it is tempting, and indeed easy, to complete the diagram:
\begin{equation}
\begin{tikzpicture}[x=12em,y=4em,baseline=(u.base)]
\node(x) [anchor=center] {|s|};
\node(x') [below=1 of x,anchor=center] {|s'|};
\node(hx) [right=1 of x,anchor=center] {|h s|};
\node(hx') [right=1 of x',anchor=center] {|h s'|};
\draw[serif cm-to] (x) edge node[above]{consume~|as|  using~|h|} (hx);
\draw[serif cm-to] (x') edge node[below]{consume~|as|  using~|h|} (hx');
\draw[serif cm-to] (x) edge node(t)[left]{produce~|b| using~|g|} (x ||- x'.north);
\draw[serif cm-to] (hx) edge node(u)[right]{produce~|b| using~|g|} (hx ||- hx'.north);
\node at ($(t)!0.5!(u)$) [anchor=center] {$\Rightarrow$};
\end{tikzpicture}
\label{eq:streaming-big-step}
\end{equation}
This is a kind of commutativity of production and consumption:
From the initial state~|s|, we can either
\begin{itemize}
\item apply~|g| to~|s| to produce~|b| and reach a new state~|s'|, and then apply~|h| to consume the list and update the state to~|h s'|, or
\item apply~|h| to~|s| to consume the list and update the state to~|h s|, and then apply~|g| to~|h s| to produce an element and reach a new state.
\end{itemize}
If the first route is possible, the second route should also be possible, and the outcomes should be the same --- doing production using~|g| and consumption using~|h| in whichever order should emit the same element and reach the same final state.
This cannot be true in general, and should be formulated as a condition of the streaming algorithm.

The above commutativity~(\ref{eq:streaming-big-step}) of |g|~and~|h| is commutativity of one step of production (using~|g|) and multiple steps of consumption (of the entire input list, using~|h|).
If we require that |g|~and~|(▷)| commute instead, this commutativity of single-step production and consumption will be easier for the algorithm user to verify:
\begin{equation}
\begin{tikzpicture}[x=12em,y=4em,baseline=(u.base)]
\node(x) [anchor=center] {|s|};
\node(x') [below=1 of x,anchor=center] {|s'|};
\node(hx) [right=1 of x,anchor=center] {|s ▷ a|};
\node(hx') [right=1 of x',anchor=center] {|s' ▷ a|};
\draw[serif cm-to] (x) edge node[above]{consume~|a| using~|(▷)|} (hx);
\draw[serif cm-to] (x') edge node[below]{consume~|a| using~|(▷)|} (hx');
\draw[serif cm-to] (x) edge node(t)[left]{produce~|b| using~|g|} (x ||- x'.north);
\draw[serif cm-to] (hx) edge node(u)[right]{produce~|b| using~|g|} (hx ||- hx'.north);
\node at ($(t)!0.5!(u)$) [anchor=center] {$\Rightarrow$};
\end{tikzpicture}
\label{eq:streaming}
\end{equation}
This is \varcitet{Gibbons-metamorphisms}{'s} \emph{streaming condition}, which is needed for proving the correctness of the streaming algorithm.
In our development of |stream|, we can assume that a proof of the streaming condition is available:
\begin{code}
constant streaming-condition :  {a : A} {b : B} {s s' : S} →
                                g s ≡ just (b , s') → g (s ▷ a) ≡ just (b , s' ▷ a)
\end{code}
We use a hypothetical |constant| keyword here to emphasise that |streaming-condition| is a constant made available to us and does not need to be defined.
In the complete program in \autoref{fig:stream}, the functions defined in this section are contained in a module, and |streaming-condition| becomes a parameter of this module.

Back to Goal~5, where we should prove the commutativity of |g|~and~|h|.
All it takes should be a straightforward induction to extend the streaming condition along the axis of consumption --- so straightforward, in fact, that \Agda\ can do most of the work for us!
We know that we need a helper function |streaming-lemma| that performs induction on |as| and uses |eq| as a premise; by filling |streaming-lemma as eq| into Goal~5 and firing a ``helper type'' command (\texttt{C-c C-h}), \Agda\ can generate a type for |streaming-lemma|, which, after removing some over-generalisations and unnecessary definition expansions, is:
\begin{code}
streaming-lemma :  {b : B} {s s' : S} {h : S → S} → AlgList A (left-alg (▷)) id h →
                   g s ≡ just (b , s') → g (h s) ≡ just (b , h s')
streaming-lemma as(CXT(AlgList A (left-alg (▷)) id h)) eq(CXT(g s ≡ just (b , s'))) = (GOAL(g (h s) ≡ just (b , h s'))(6))
\end{code}
\Agda\ then accepts |streaming-lemma as eq| as a type-correct term for Goal~5, completing the definition of |stream|.

Now all that is left is the body of |streaming-lemma| (Goal~6).
If we give a hint that case-splitting is needed (\texttt{-c}), Auto can complete the definition of |streaming-lemma| on its own, yielding (modulo one cosmetic variable renaming):
\begin{code}
streaming-lemma :  {b : B} {s s' : S} {h : S → S} → AlgList A (left-alg (▷)) id h →
                   g s ≡ just (b , s') → g (h s) ≡ just (b , h s')
streaming-lemma []        eq = eq
streaming-lemma (a ∷ as)  eq = streaming-lemma as (streaming-condition eq)
\end{code}

The complete program is shown in \autoref{fig:stream}.

\varparagraph{Streaming base conversion for fractions.}
We have (re)discovered the streaming condition, but does it hold for the base conversion metamorphism |unfoldr g_C ∘ foldl (▷ᶜ) e_C| given in \autoref{sec:metamorphisms}?
Actually, no.
The problem is that |g_C|~can be too eager to produce an output digit.
In $0.625_{10} = 0.101_2$, for example, after consuming the first decimal digit~$6$, we can safely use~|g_C| to produce the first two binary digits $1$~and~$0$, reaching the state $(0.1\,,\;0.01\,,\;0.125)$.
From this state, |g_C|~will produce a third binary digit~$0$, but this can be wrong if there are more input digits to consume --- indeed, in our example the next input digit is~$5$, and the accumulator will go up to $0.1 + 5 \times 0.01 = 0.15$, exceeding the next output weight $0.125$, and hence the next output digit should be~$1$ instead.
To allow streaming, we should make~|g_C| more conservative, producing an output digit only when the accumulator will not go up too much to change the produced output digit whatever the unconsumed input digits might be.
We therefore revise |g_C| to check an extra condition (underlined below) before producing:
\begin{code}
g_C' (v , w_i , w_o) =  let  d  LETEQ {-"\;\lfloor\nicefrac{\identifier{v}\kern1pt}{\identifier{w_o}}\rfloor"-}; r  LETEQ {-"\;\identifier{v} - d \times \identifier{w_o}"-}
                        in   if {-"\identifier{v} > 0 \,\mathrel\wedge\, \underline{r + \identifier{b_i} \times \identifier{w_i} \leq \identifier{w_o}}\;"-} then  just (d , (r , w_i , {-"\;\nicefrac{\identifier{w_o}\kern1pt}{\identifier{b_o}}"-})) else  nothing
\end{code}
In this extra condition, $r$~is the updated accumulator after producing an output digit, and $b_i \times w_i$ is the supremum value attainable by the unconsumed input digits.
If the sum $r + b_i \times w_i$ exceeds~$w_o$, the output digit may have to be increased, in which case we should not produce the digit just yet.
After this revision, the streaming condition holds for |g_C'| and |(▷ᶜ)|.

Once all the input digits have been consumed, however, |g_C'| can be too conservative and does not produce output digits even when the accumulator is not zero.
This is another story though --- the interested reader is referred to \citet[Section~4.4]{Gibbons-metamorphisms}.

\begin{figure}
\beforefigurecode
\begin{code}
module Streaming
  ((▷) : S → A → S) (g : S → Maybe (B × S))
  (streaming-condition :  {a : A} {b : B} {s s' : S} →
                          g s ≡ just (b , s') → g (s ▷ a) ≡ just (b , s' ▷ a))
  where

  streaming-lemma :  {b : B} {s s' : S} {h : S → S} → AlgList A (left-alg (▷)) id h →
                     g s ≡ just (b , s') → g (h s) ≡ just (b , h s')
  streaming-lemma []        eq = eq
  streaming-lemma (a ∷ as)  eq = streaming-lemma as (streaming-condition eq)

  stream : (s : S) → {h : S → S} → AlgList A (left-alg (▷)) id h → CoalgList B g (h s)
  decon (stream s as         ) with g s         | inspect g s
  decon (stream s []         ) | nothing        | [ eq ] = ⟨ eq ⟩
  decon (stream s (a ∷ as)   ) | nothing        | [ eq ] = decon (stream (s ▷ a) as)
  decon (stream s as         ) | just (b , s')  | [ eq ] = b ∷⟨ streaming-lemma as eq ⟩ stream s' as
\end{code}
\caption{Streaming metamorphisms}
\label{fig:stream}
\end{figure}

\section{Jigsaw Metamorphisms}
\label{sec:jigsaw-infinite}

Let us now turn to right metamorphisms.
Recall that a right metamorphic type has the form:
\begin{code}
{s : S} → AlgList A (◁) e s → CoalgList B g s
\end{code}
which, unlike a left metamorphic type, does not have an initial state as one of its arguments --- the implicit argument |s : S| is the intermediate state reached after consuming the entire input list, and it is unrealistic to assume that this intermediate state is also given at the start of a metamorphic computation.
This suggests that |s|~plays a role only in the type-level specification, and we should avoid using~|s| in the actual computation, so that it becomes computationally irrelevant and could be somehow erased; correspondingly, the indices and proofs in |AlgList| and |CoalgList| could all be erased eventually, turning a program with a right metamorphic type into one that maps plain lists to colists.
Does this mean that we can bypass computation with states and just work with list elements to compute a metamorphism?
Surprisingly, \citet{Nakano-jigsaw} has such a computation model, in which it is possible to compute a metamorphism without using the states mentioned in its specification!
(By contrast, in |cbp| (\autoref{sec:cbp}/\autoref{fig:cbp}) and |stream| (\autoref{sec:streaming}/\autoref{fig:stream}), we can hope to erase the indices and proofs in |AlgList| and |CoalgList| but not the input state, which is used in the computation.)

\subsection{The Jigsaw Model}

In \varcitet{Nakano-jigsaw}{'s} model, a computation transforms a |List A| to a |CoList B|, and to program its behaviour, we need to provide a suitable function |piece : A × B → B × A|.
\citet{Nakano-jigsaw} neatly visualises his model as a jigsaw puzzle.
The |piece| function can be thought of as describing a set of jigsaw pieces:
\[ \includegraphics{figs/piece-crop.pdf} \]
In each piece, the horizontal edges are associated with a value of type~|A|, and the vertical edges with a value of type~|B|.
Two pieces fit together exactly when the values on their adjacent edges coincide.
Moreover, the values on the top and right edges should determine those on the left and bottom edges, and the |piece| function records the mappings for all the pieces --- the piece above, for example, corresponds to the mapping |piece (a , b) LETEQ (b' , a')|.

Below is an illustration of an ongoing computation:
\[
\raisebox{-.5\height+1mm+.125pt}{\includegraphics{figs/board-empty-crop.pdf}}
\quad\leadsto\quad
\raisebox{-.5\height}{\includegraphics{figs/board-filling-crop.pdf}}
\quad\leadsto\quad
\cdots \]
Given an input list, we start from an empty board with its top boundary initialised to the input elements and its right boundary to some special ``straight'' value.
Then we put in pieces to fill the board:
Whenever a top edge and a right edge is known, we consult the |piece| function to find the unique fitting piece and put it in.
Initially the only place we can put in a piece is the top-right corner, but as we put in more pieces, the number of choices will increase --- in the board on the right, for example, we can choose one of the two dashed places to put in the next piece.
Eventually we will reach the left boundary, and the values on the left boundary are the output elements.
Although we can put in the pieces in a nondeterministic order and even in parallel, the final board configuration is determined by the initial boundary, and thus the output elements are produced deterministically.

\varparagraph{Heapsort in the jigsaw model.}
For a concrete example, the heapsort metamorphism can be computed in the jigsaw model with |piece (a , b) LETEQ (min a b , max a b)|.
The final board configuration after sorting the list |{-"2\;"-} ∷ {-"3\;"-} ∷ {-"1\;"-} ∷ []| is shown below:
\begin{equation}
\raisebox{-7.125ex}{\includegraphics{figs/heapsort-piece-crop.pdf}}
\qquad\qquad
\raisebox{-7.125ex-6mm-.975pt}{\includegraphics{figs/heapsort-crop.pdf}}
\label{eq:heapsort}
\end{equation}
\citet{Nakano-jigsaw} remarks that this transforms heapsort into ``a form of parallel bubble sort'', which looks very different from the original metamorphic computation --- in particular, heaps are nowhere to be seen.

In general, how is the jigsaw model related to metamorphisms, and under what conditions does the jigsaw model compute metamorphisms?
Again, we will figure out the answers by trying to program jigsaw computations with metamorphic types in \Agda.

\subsection{The Infinite Case}

Let us first look at a simpler case where the output colist is always infinite; that is, the coalgebra used in the metamorphic type is |just ∘ g∞| where |g∞ : S → B × S| --- for heapsort, |g∞|~is an adapted version of |popMin| such that popping from the empty heap returns~$\infty$ and the empty heap itself, so the output colist is the sorted input list followed by an infinite number of $\infty$'s.

\subsubsection{Horizontal Placement}

We start by writing down the metamorphic type:
\begin{code}
jigsawᵢₕ : {s : S} → AlgList A (◁) e s → CoalgList B (just ∘ g∞) s
jigsawᵢₕ as(CXT(AlgList A (◁) e s)) = (GOAL(CoalgList B (just ∘ g∞) s)(0))
\end{code}
One possible placement strategy is to place one row of jigsaw pieces at a time.
Placing a row is equivalent to transforming an input list~|as| into a new one~|as'| and also a vertical edge~|b|:
\[ \includegraphics{figs/row-crop.pdf} \]
We therefore introduce the following function |fillᵢₕ| for filling a row:
\begin{code}
fillᵢₕ : {s : S} → AlgList A (◁) e s → B × Σ[ t ∈ S ] AlgList A (◁) e t
fillᵢₕ as = (GOAL(B × Σ[ t ∈ S ] AlgList A (◁) e t)(1))
\end{code}
We do not know (or cannot easily specify) the index~|t| in the type of the new |AlgList|, so the index is simply existentially quantified.
The job of |jigsawᵢₕ|, then, is to call |fillᵢₕ| repeatedly to cover the board.
We revise Goal~0 into:
\begin{code}
jigsawᵢₕ : {s : S} → AlgList A (◁) e s → CoalgList B (just ∘ g∞) s
decon (jigsawᵢₕ as(CXT(AlgList A (◁) e s))) with fillᵢₕ as
decon (jigsawᵢₕ as) | (b , t , as') = b ∷⟨ (GOAL(just (g∞ s) ≡ just (b , t))(2)) ⟩ jigsawᵢₕ as'
\end{code}
Goal~2 demands an equality linking |s|~and~|t|, which are the input and output indices of |fillᵢₕ|.
This suggests that |fillᵢₕ| is responsible for not only computing~|t| but also establishing the relationship between |t|~and~|s|.
We therefore add the equality to the result type of |fillᵢₕ|, and discharge Goal~2 with the equality proof that will be produced by |fillᵢₕ|:
\begin{code}
fillᵢₕ : {s : S} → AlgList A (◁) e s → Σ[ b ∈ B ] Σ[ t ∈ S ] AlgList A (◁) e t × g∞ s ≡ (b , t)
fillᵢₕ as = (GOAL(Σ[ b ∈ B ] Σ[ t ∈ S ] AlgList A (◁) e t × g∞ s ≡ (b , t))(1))

jigsawᵢₕ : {s : S} → AlgList A (◁) e s → CoalgList B (just ∘ g∞) s
decon (jigsawᵢₕ as) with fillᵢₕ as
decon (jigsawᵢₕ as) | (b , _ , as' , eq) = b ∷⟨ cong just eq ⟩ jigsawᵢₕ as'
\end{code}
(The combinator `|cong just|' has type |{X : Set} {x x' : X} → x ≡ x' → just x ≡ just x'|.)

\varparagraph{The road not taken.}
From Goal~2, there seems to be another way forward: the equality says that the output vertical edge~|b| and the index~|t| in the type of~|as'| are determined by |g∞ s|, so |jigsawᵢₕ| could have computed |g∞ s| and obtained |b|~and~|t| directly!
However, recall that the characteristic of the jigsaw model is that computation proceeds by converting input list elements directly into output colist elements without involving the states appearing in the specifications.
In our setting, this means that states only appear in the function types, not the function bodies, so having |jigsawᵢₕ| invoke |g s| would deviate from the jigsaw model.
Instead, |jigsawᵢₕ| invokes |fillᵢₕ|, which will only use |piece| to compute~|b|.
(It would probably be better if we declared the argument~|s| in the metamorphic type as irrelevant to enforce that |s|~does not participate in the computation; this irrelevance declaration would then need to be propagated to related parts in |AlgList| and |CoalgList|, though, which we are trying to avoid.)

Let us get back to |fillᵢₕ| (Goal~1).
The process of filling a row follows the structure of the input list, so overall it is an induction, of which the first step is a case analysis:
\begin{code}
fillᵢₕ : {s : S} → AlgList A (◁) e s → Σ[ b ∈ B ] Σ[ t ∈ S ] AlgList A (◁) e t × g∞ s ≡ (b , t)
fillᵢₕ [] = (GOAL(Σ[ b ∈ B ] Σ[ t ∈ S ] AlgList A (◁) e t × g∞ e ≡ (b , t))(3))
fillᵢₕ (a ∷ as(CXT(AlgList (◁) e s))) = (GOAL(Σ[ b ∈ B ] Σ[ t ∈ S ] AlgList A (◁) e t × g∞ (a ◁ s) ≡ (b , t))(4))
\end{code}
If the input list is empty (Goal~3), we return the rightmost ``straight'' edge.
We therefore assume that a |constant straight : B| is available, and fill it into Goal~3:
\begin{code}
fillᵢₕ : {s : S} → AlgList A (◁) e s → Σ[ b ∈ B ] Σ[ t ∈ S ] AlgList A (◁) e t × g∞ s ≡ (b , t)
fillᵢₕ [] = straight , (GOAL(Σ[ t ∈ S ] AlgList A (◁) e t × g∞ e ≡ (straight , t))(5))
fillᵢₕ (a ∷ as(CXT(AlgList (◁) e s))) = (GOAL(Σ[ b ∈ B ] Σ[ t ∈ S ] AlgList A (◁) e t × g∞ (a ◁ s) ≡ (b , t))(4))
\end{code}
We should now give the new list, which we know should have the same length as the old list, so in this case it is easy to see that the new list should be empty as well (and, by giving an underscore as an instruction, \Agda\ can infer the index in the type of the new list):
\begin{code}
fillᵢₕ : {s : S} → AlgList A (◁) e s → Σ[ b ∈ B ] Σ[ t ∈ S ] AlgList A (◁) e t × g∞ s ≡ (b , t)
fillᵢₕ [] = straight , _ , [] , (GOAL(g∞ e ≡ (straight , e))(6))
fillᵢₕ (a ∷ as(CXT(AlgList (◁) e s))) = (GOAL(Σ[ b ∈ B ] Σ[ t ∈ S ] AlgList A (◁) e t × g∞ (a ◁ s) ≡ (b , t))(4))
\end{code}
Here we arrive at another proof obligation, which says that from the initial state~|e| the coalgebra~|g∞| should produce |straight| and leave the state unchanged.
This seems a reasonable property to add as a condition of the algorithm: in heapsort, for example, |e|~is the empty heap and |straight| is~|INF|, and popping from the empty heap, as we mentioned, can be defined to return~|INF| and the empty heap itself.
We therefore add an additional |constant straight-production : g∞ e ≡ (straight , e)|, which discharges Goal~6.

The interesting case is when the input list is non-empty (Goal~4).
We start with an inductive call to |fillᵢₕ| itself:
\begin{code}
fillᵢₕ : {s : S} → AlgList A (◁) e s → Σ[ b ∈ B ] Σ[ t ∈ S ] AlgList A (◁) e t × g∞ s ≡ (b , t)
fillᵢₕ [] = straight , _ , [] , straight-production
fillᵢₕ (a ∷ as(CXT(AlgList (◁) e s))  ) with fillᵢₕ as
fillᵢₕ (a ∷ as                        ) | (b , s' , as' , eq) =
  (GOAL(Σ[ b ∈ B ] Σ[ t ∈ S ] AlgList A (◁) e t × g∞ (a ◁ s) ≡ (b , t))(7))
\end{code}
With the inductive call, the jigsaw pieces below the tail~|as| have been placed, yielding a vertical edge~|b| and a list~|as'| of horizontal edges below~|as|:
\[ \includegraphics{figs/row-inductive-case-crop.pdf} \]
We should complete the row by placing the last jigsaw piece with |a|~and~|b| as input, and use the output edges |(b' , a') = piece (a , b)| in the right places:
\begin{code}
fillᵢₕ : {s : S} → AlgList A (◁) e s → Σ[ b ∈ B ] Σ[ t ∈ S ] AlgList A (◁) e t × g∞ s ≡ (b , t)
fillᵢₕ [] = straight , _ , [] , straight-production
fillᵢₕ (a ∷ as(CXT(AlgList (◁) e s))  ) with fillᵢₕ as
fillᵢₕ (a ∷ as                        ) | (b , s' , as' , eq(CXT(g∞ s ≡ (b , s')))) =
  let (b' , a') LETEQ piece (a , b) in (b' , _ , a' ∷ as' , (GOAL(g∞ (a ◁ s) ≡ (b' , a' ◁ s'))(8)))
\end{code}

\varparagraph{The jigsaw condition.}
Here we see a familiar pattern: Goal~8 demands an equality about producing from a state after consumption, and in the context we have an equality~|eq| about producing from a state before consumption.
Following what we did in \autoref{sec:streaming}, a commutative state transition diagram can be drawn:
\begin{equation}
\begin{tikzpicture}[x=12em,y=4em,baseline=(u.base)]
\node(x) [anchor=center] {|s|\vphantom{|◁|}};
\node(x') [below=1 of x,anchor=center] {|s'|\vphantom{|◁|}};
\node(hx) [left=1 of x,anchor=center] {|a ◁ s|};
\node(hx') [left=1 of x',anchor=center] {|a' ◁ s'|};
\draw[serif cm-to] (x) edge node[above]{consume~|a| using~|(◁)|} (hx);
\draw[serif cm-to] (x') edge node[below]{consume~|a'| using~|(◁)|} (hx');
\draw[serif cm-to] (x) edge node(t)[right]{produce~|b| using~|g∞|} (x ||- x'.north);
\draw[serif cm-to] (hx) edge node(u)[left]{produce~|b'| using~|g∞|} (hx ||- hx'.north);
\node at ($(t)!0.5!(u)$) [anchor=center] {$\Leftarrow$};
\end{tikzpicture}
\label{eq:jigsaw-infinite}
\end{equation}
where |(b' , a') = piece (a , b)|.
This is again a kind of commutativity of production and consump\-tion, but unlike the streaming condition~(\ref{eq:streaming}) in \autoref{sec:streaming}, the elements produced and consumed can change after swapping the order of production and consumption.
Given any top and right edges |a|~and~|b|, the |piece| function should be able to find the left and bottom edges |b'|~and~|a'| to complete the commutative diagram.
This constitutes a specification for |piece|, and, following \citet{Nakano-jigsaw} (but not strictly), we call it the \emph{jigsaw condition}:
\begin{code}
constant
  jigsaw-conditionᵢ :  {a : A} {b : B} {s s' : S} →
                       g∞ s ≡ (b , s') → let (b' , a') LETEQ piece (a , b) in g∞ (a ◁ s) ≡ (b' , a' ◁ s')
\end{code}
Adding |jigsaw-conditionᵢ| as the final assumption, we can fill |jigsaw-conditionᵢ eq| into Goal~8 and complete the program, which is shown in \autoref{fig:jigsaw-infinite-horizontal}.

\varparagraph{Metamorphisms and the jigsaw model.}
We can now see a connection between metamorphic computations and the jigsaw model.
Definitionally, a metamorphism folds the input list to a state, and then produces the output elements while updating the state.
In the jigsaw model, and with the horizontal placement strategy, rather than folding the input list to a ``compressed'' state, we use the whole list as an ``uncompressed'' state, and ensure that the production process using uncompressed states simulates the definitional one using compressed states.
The type of |fillᵢₕ| makes this clear:
The produced element~|b| is exactly the one that would have been produced from the compressed state~|s| obtained by folding the old list.
Then, on the compressed side, the state~|s| is updated to~|t|; correspondingly, on the uncompressed side, the old list is updated to a new list that folds to~|t|.
The jigsaw condition ensures that this relationship between compressed and uncompressed states can be maintained by placing rows of jigsaw pieces.

\varparagraph{Deriving the \textit{piece} function for heapsort using the jigsaw condition.}
For the heapsort metamorphism, consuming an element is pushing it into a heap, and producing an element is popping a minimum element from a heap.
In diagram~(\ref{eq:jigsaw-infinite}), producing~|b| on the right means that |b|~is a minimum element in the heap~|s|, and |s'|~is the rest of the heap.
If |a|~is pushed into~|s|, popping from the updated heap |a ◁ s| will either still produce~|b| if $a > b$, or produce~|a| if $a \leq b$, so |b'|~should be |min a b|.
Afterwards, the final heap |a' ◁ s'| should still contain the other element that was not popped out, i.e., |max a b|, and can be obtained by pushing |max a b| into~|s'|, so |a'|~should be |max a b|.

\begin{figure}
\beforefigurecode
\begin{code}
module Jigsaw-Infinite-Horizontal
  ((◁) : A → S → S) (e : S) (g∞ : S → B × S)
  (piece : A × B → B × A)
  (jigsaw-conditionᵢ :  {a : A} {b : B} {s s' : S} →
                        g∞ s ≡ (b , s') → let (b' , a') LETEQ piece (a , b) in g∞ (a ◁ s) ≡ (b' , a' ◁ s'))
  (straight : B) (straight-production : g∞ e ≡ (straight , e))
  where

  fillᵢₕ : {s : S} → AlgList A (◁) e s → Σ[ b ∈ B ] Σ[ t ∈ S ] AlgList A (◁) e t × g∞ s ≡ (b , t)
  fillᵢₕ [] = straight , _ , [] , straight-production
  fillᵢₕ (a ∷ as) with fillᵢₕ as
  fillᵢₕ (a ∷ as) | b , _ , as' , eq =  let  (b' , a') LETEQ piece (a , b)
                                        in   b' , _ , a' ∷ as' , jigsaw-conditionᵢ eq

  jigsawᵢₕ : {s : S} → AlgList A (◁) e s → CoalgList B (just ∘ g∞) s
  decon (jigsawᵢᵥ as) with fillᵢₕ as
  decon (jigsawᵢᵥ as) | b , _ , as' , eq = b ∷⟨ cong just eq ⟩ jigsawᵢᵥ as'
\end{code}
\caption{Infinite jigsaw metamorphisms --- horizontal placement}
\label{fig:jigsaw-infinite-horizontal}
\end{figure}

\subsubsection{Vertical Placement}
\label{sec:jigsaw-vertical}

There is another obvious placement strategy --- the vertical one, where we place one column of jigsaw pieces at a time.
This corresponds to another way of thinking about metamorphic computations in the jigsaw model.
In contrast to streaming metamorphisms (\autoref{sec:streaming}), where we need to be cautious about producing an element because once an element is produced we can no longer change it, computing metamorphisms in the jigsaw model with the vertical placement strategy is like having an entire output colist right from the start and then updating it:
\begin{itemize}
\item initially we start with a colist of |straight| edges, which is unfolded from the empty state~|e|;
\item inductively, if we have a colist unfolded from some state~|s|, and an input element~|a| comes in, we place a column of jigsaw pieces to update the colist, and the result --- due to the jigsaw condition --- is a colist unfolded from the new state |a ◁ s|;
\item finally, after all elements of the input list~|as| are consumed, we get a colist unfolded from |foldr (◁) e as|.
\end{itemize}
We should be able to program this strategy as well!
Moreover, we expect to use the same conditions as those for programming the horizontal placement strategy.
We start from exactly the same type as |jigsawᵢₕ|:
\begin{code}
jigsawᵢᵥ : {s : S} → AlgList A (◁) e s → CoalgList B (just ∘ g∞) s
jigsawᵢᵥ as(CXT(AlgList A (◁) e s)) = (GOAL(CoalgList B (just ∘ g∞) s)(0))
\end{code}
As described above, the vertical placement strategy is an induction on the input list, so we proceed with a case analysis on~|as|:
\begin{code}
jigsawᵢᵥ : {s : S} → AlgList A (◁) e s → CoalgList B (just ∘ g∞) s
jigsawᵢᵥ [] = (GOAL(CoalgList B (just ∘ g∞) e)(1))
jigsawᵢᵥ (a ∷ as(CXT(AlgList A (◁) e s))) = (GOAL(CoalgList B (just ∘ g∞) (a ◁ s))(2))
\end{code}
If the input list is empty (Goal~1), we should produce a colist of |straight| egdes:
\begin{code}
jigsawᵢᵥ : {s : S} → AlgList A (◁) e s → CoalgList B (just ∘ g∞) s
decon (jigsawᵢᵥ []) = straight ∷⟨ (GOAL(just (g∞ e) ≡ just (straight , e))(3)) ⟩ jigsawᵢᵥ []
jigsawᵢᵥ (a ∷ as(CXT(AlgList A (◁) e s))) = (GOAL(CoalgList B (just ∘ g∞) (a ◁ s))(2))
\end{code}
and the proof obligation (Goal~3) is discharged with |cong just straight-production|.
For the inductive case (Goal~2):
\[ \includegraphics{figs/column-crop.pdf} \]
We place all the columns below the tail~|as| by an inductive call |jigsawᵢᵥ as|, which gives us a colist of vertical edges.
To the left of this colist, we should place the last column below the head element~|a|; again we introduce a helper function |fillᵢᵥ| that takes |a|~and the colist |jigsawᵢᵥ as| as input and produces the leftmost colist:
\begin{code}
jigsawᵢᵥ : {s : S} → AlgList A (◁) e s → CoalgList B (just ∘ g∞) s
decon (jigsawᵢᵥ []) = straight ∷⟨ cong just straight-production ⟩ jigsawᵢᵥ []
jigsawᵢᵥ (a ∷ as) = fillᵢᵥ a (jigsawᵢᵥ as)
\end{code}
\Agda\ again can give us a suitable type of |fillᵢᵥ|:
\begin{code}
fillᵢᵥ : {s : S} (a : A) → CoalgList B (just ∘ g∞) s → CoalgList B (just ∘ g∞) (a ◁ s)
fillᵢᵥ a bs(CXT(CoalgList B (just ∘ g∞) s)) = (GOAL(CoalgList B (just ∘ g∞) (a ◁ s))(4))
\end{code}
Here we should deconstruct~|bs| so that we can invoke |piece| on |a|~and the first element of~|bs|:
\begin{code}
fillᵢᵥ : {s : S} (a : A) → CoalgList B (just ∘ g∞) s → CoalgList B (just ∘ g∞) (a ◁ s)
decon (fillᵢᵥ a bs(CXT(CoalgList B (just ∘ g∞) s))) with decon bs
decon (fillᵢᵥ a bs) | ⟨ eq(CXT(just (g∞ s) ≡ nothing)) ⟩ = (GOAL(CoalgListF B (just ∘ g∞) (a ◁ s))(5))
decon (fillᵢᵥ a bs) | b ∷⟨ eq(CXT(just (g∞ s) ≡ just (b , s'))) ⟩ bs'(CXT(CoalgList B (just ∘ g∞) s')) =
  (GOAL(CoalgListF B (just ∘ g∞) (a ◁ s))(6))
\end{code}
For Goal~5, since the coalgebra |just ∘ g∞| in the type of~|bs| never returns |nothing|, it is impossible for~|bs| to be empty.
We can convince \Agda\ that this case is impossible by matching~|eq| with the absurd pattern~|()|, saying that |eq|~cannot possibly exist (and \Agda\ accepts this because a |just|-value can never be equal to |nothing|):
\begin{code}
fillᵢᵥ : {s : S} (a : A) → CoalgList B (just ∘ g∞) s → CoalgList B (just ∘ g∞) (a ◁ s)
decon (fillᵢᵥ a bs(CXT(CoalgList B (just ∘ g∞) s))) with decon bs
decon (fillᵢᵥ a bs) | ⟨ () ⟩
decon (fillᵢᵥ a bs) | b ∷⟨ eq(CXT(just (g∞ s) ≡ just (b , s'))) ⟩ bs'(CXT(CoalgList B (just ∘ g∞) s')) =
  (GOAL(CoalgListF B (just ∘ g∞) (a ◁ s))(6))
\end{code}
The real work is done at Goal~6, where |bs|~is deconstructed into its head~|b| and tail~|bs'|:
\[ \includegraphics{figs/column-coinductive-case-crop.pdf} \]
We invoke the |piece| function to transform |a|~and~|b| to |b'|~and~|a'|; the head of the output colist is then~|b'|, and the tail is coinductively computed from |a'|~and~|bs'|:
\begin{code}
fillᵢᵥ : {s : S} (a : A) → CoalgList B (just ∘ g∞) s → CoalgList B (just ∘ g∞) (a ◁ s)
decon (fillᵢᵥ a bs(CXT(CoalgList B (just ∘ g∞) s))) with decon bs
decon (fillᵢᵥ a bs) | ⟨ () ⟩
decon (fillᵢᵥ a bs) | b ∷⟨ eq(CXT(just (g∞ s) ≡ just (b , s'))) ⟩ bs'(CXT(CoalgList B (just ∘ g∞) s')) =
  let (b' , a') LETEQ piece (a , b) in b' ∷⟨ (GOAL(just (g∞ (a ◁ s)) ≡ just (b' , a' ◁ s'))(7)) ⟩ fillᵢᵥ a' bs'
\end{code}
The remaining proof obligation is indeed the jigsaw condition modulo the harmless occurrences of |just|, so we arrive at the complete program shown in \autoref{fig:jigsaw-infinite-vertical}.

\begin{figure}
\beforefigurecode
\begin{code}
module Jigsaw-Infinite-Vertical
  ((◁) : A → S → S) (e : S) (g∞ : S → B × S)
  (piece : A × B → B × A)
  (jigsaw-conditionᵢ :  {a : A} {b : B} {s s' : S} →
                        g∞ s ≡ (b , s') → let (b' , a') LETEQ piece (a , b) in g∞ (a ◁ s) ≡ (b' , a' ◁ s'))
  (straight : B) (straight-production : g∞ e ≡ (straight , e))
  where

  fillᵢᵥ : {s : S} (a : A) → CoalgList B (just ∘ g∞) s → CoalgList B (just ∘ g∞) (a ◁ s)  
  decon (fillᵢᵥ a bs) with decon bs
  decon (fillᵢᵥ a bs) | ⟨ () ⟩
  decon (fillᵢᵥ a bs) | b ∷⟨ eq ⟩ bs' =
    let  (b' , a') LETEQ piece (a , b)
    in   b' ∷⟨ cong just (jigsaw-conditionᵢ (cong-from-just eq)) ⟩ fillᵢᵥ a' bs'
         -- |cong-from-just : {X : Set} {x x' : X} → just x ≡ just x' → x ≡ x'|

  jigsawᵢᵥ : {s : S} → AlgList A (◁) e s → CoalgList B (just ∘ g∞) s
  decon (jigsawᵢᵥ []) = straight ∷⟨ cong just straight-production ⟩ jigsawᵢᵥ []
  jigsawᵢᵥ (a ∷ as) = fillᵢᵥ a (jigsawᵢᵥ as)
\end{code}
\caption{Infinite jigsaw metamorphisms --- vertical placement}
\label{fig:jigsaw-infinite-vertical}
\end{figure}

\subsection{The General (Possibly Finite) Case}
\label{sec:jigsaw-general}

Finally, let us tackle the general case, where the produced colist can be finite.
This is the same setting as \varcitet{Nakano-jigsaw}{'s}, and will allow us to compare our derived conditions with his.
The metamorphic type we use is exactly the one we saw in \autoref{sec:spec}:
\begin{code}
jigsaw : {s : S} → AlgList A (◁) e s → CoalgList B g s
jigsaw as(CXT(AlgList A (◁) e s)) = (GOAL(CoalgList B g s)(0))
\end{code}
We use the vertical placement strategy, so the overall structure will be similar to |jigsawᵢᵥ| in (\autoref{sec:jigsaw-vertical}/\autoref{fig:jigsaw-infinite-vertical}).
Starting from a case analysis:
\begin{code}
jigsaw : {s : S} → AlgList A (◁) e s → CoalgList B g s
jigsaw [] = (GOAL(CoalgList B g e)(1))
jigsaw (a ∷ as(CXT(AlgList A (◁) e s))) = (GOAL(CoalgList B g (a ◁ s))(2))
\end{code}
At Goal~1, it should suffice to produce an empty colist:
\begin{code}
jigsaw : {s : S} → AlgList A (◁) e s → CoalgList B g s
decon (jigsaw []) = ⟨ (GOAL(g e ≡ nothing)(3)) ⟩
jigsaw (a ∷ as(CXT(AlgList A (◁) e s))) = (GOAL(CoalgList B g (a ◁ s))(2))
\end{code}
To do so we need |g e ≡ nothing|, which is a reasonable assumption --- for heapsort, for example, |e|~is the empty heap, on which |popMin| computes to |nothing|.
We therefore introduce a |constant nothing-from-e : g e ≡ nothing| and use it to discharge Goal~1:
\begin{code}
jigsaw : {s : S} → AlgList A (◁) e s → CoalgList B g s
decon (jigsaw []) = ⟨ nothing-from-e ⟩
jigsaw (a ∷ as(CXT(AlgList A (◁) e s))) = (GOAL(CoalgList B g (a ◁ s))(2))
\end{code}
For Goal~2, we proceed in exactly the same way as we dealt with the corresponding case of |jigsawᵢᵥ|:
\begin{code}
jigsaw : {s : S} → AlgList A (◁) e s → CoalgList B g s
decon (jigsaw []) = ⟨ nothing-from-e ⟩
jigsaw (a ∷ as) = fill a (jigsaw as)
\end{code}
where the type and the top-level structure of the helper function |fill| is also exactly the same as |fillᵢᵥ|:
\begin{code}
fill : {s : S} (a : A) → CoalgList B g s → CoalgList B g (a ◁ s)
decon (fill a bs(CXT(CoalgList B g s))) with decon bs
decon (fill a bs) | ⟨ eq(CXT(g s ≡ nothing)) ⟩ = (GOAL(CoalgListF B g (a ◁ s))(4))
decon (fill a bs) | b ∷⟨ eq(CXT(g s ≡ just (b , s'))) ⟩ bs'(CXT(CoalgList B g s')) = (GOAL(CoalgListF B g (a ◁ s))(5))
\end{code}
The situation gets more interesting from this point.

Let us work on the familiar case first, namely Goal~5.
If we do the same thing as the corresponding case of |fillᵢᵥ|:
\begin{code}
fill : {s : S} (a : A) → CoalgList B g s → CoalgList B g (a ◁ s)
decon (fill a bs(CXT(CoalgList B g s))) with decon bs
decon (fill a bs) | ⟨ eq(CXT(g s ≡ nothing)) ⟩ = (GOAL(CoalgListF B g (a ◁ s))(4))
decon (fill a bs) | b ∷⟨ eq(CXT(g s ≡ just (b , s'))) ⟩ bs'(CXT(CoalgList B g s')) =
  let (b' , a') LETEQ piece (a , b) in b' ∷⟨ (GOAL(g (a ◁ s) ≡ just (b' , a' ◁ s'))(6)) ⟩ fill a' bs'
\end{code}
we will see that the condition we need is depicted in the same way as the diagram~(\ref{eq:jigsaw-infinite}) for the infinite jigsaw condition.
Formally it is slightly different though, because we need to wrap the results of~|g| in the |just| constructor:
\begin{flalign}
\hspace\mathindent
& |{a : A} {b : B} {s s' : S} →| \nonumber & \\[-.5ex]
& |g s ≡ just (b , s') → let (b' , a') LETEQ piece (a , b) in g (a ◁ s) ≡ just (b' , a' ◁ s'))| &
\label{eq:jigsaw-just}
\end{flalign}
We will come back to this condition and close Goal~6 later.

Goal~4, unlike the corresponding case of |fillᵢᵥ|, is no longer an impossible case.
We might be tempted to produce an empty colist here:
\begin{code}
fill : {s : S} (a : A) → CoalgList B g s → CoalgList B g (a ◁ s)
decon (fill a bs(CXT(CoalgList B g s))) with decon bs
decon (fill a bs) | ⟨ eq(CXT(g s ≡ nothing)) ⟩ = ⟨ (GOAL(g (a ◁ s) ≡ nothing)(7)) ⟩
decon (fill a bs) | b ∷⟨ eq(CXT(g s ≡ just (b , s'))) ⟩ bs'(CXT(CoalgList B g s')) =
  let (b' , a') LETEQ piece (a , b) in b' ∷⟨ (GOAL(g (a ◁ s) ≡ just (b' , a' ◁ s'))(6)) ⟩ fill a' bs'
\end{code}
But the proof obligation indicates that this is not a right choice.
Let us call a state~|s| ``empty'' exactly when |g s ≡ nothing|.
The proof obligation says that if a state~|s| is empty then the next state |a ◁ s| should also be empty, but obviously this does not hold in general.
For heapsort, pushing a finite element to a heap always makes the heap extractable, constituting a counterexample.
On the other hand, it is conceivable that we can make some elements satisfy this property --- for example, it is reasonable to define the |push| operation such that pushing~|INF| into an empty heap keeps the heap empty --- so producing an empty colist is not always wrong.

\varparagraph{Flat elements.}
The above reasoning suggests that we should do a case analysis on~|a| to determine whether to produce an empty or non-empty colist at Goal~4.
Let us call an element ``flat'' exactly when subsuming it into an empty state results in another empty state. 
We should be given a decision procedure |flat?| that can be used to identify flat elements:
\begin{code}
constant flat? : (a : A) →  ({s : S} → g s ≡ nothing → g (a ◁ s) ≡ nothing) ⊎ (GOAL(Set)(8))
\end{code}
Traditionally, |flat?| would return a boolean, but using booleans in dependently typed programming almost always raises an alarm since their meaning --- e.g., whether the input satisfies a certain property or not --- will almost always need to be explained to the type-checker later; instead, it is more convenient to make the decision procedure directly return a proof or a refutation of the property.
In the case of |flat?|, its type directly says that an element of~|A| is flat or otherwise.
This ``otherwise'' at Goal~8 also requires some thought.
We could fill in the negation of the ``flat'' property, but we may need something stronger.
Unable to decide now, let us leave Goal~8 open for the moment, and come back when we have more information.

Abandoning Goal~7, we roll back to Goal~4 and refine it into Goals 9~and~10:
\begin{code}
fill : {s : S} (a : A) → CoalgList B g s → CoalgList B g (a ◁ s)
decon (fill a bs(CXT(CoalgList B g s))) with decon bs
decon (fill a bs) | ⟨ eq(CXT(g s ≡ nothing)) ⟩ with flat? a
decon (fill a bs) | ⟨ eq ⟩ | inj₁  flat      = ⟨ (GOAL(g (a ◁ s) ≡ nothing)(9)) ⟩
decon (fill a bs) | ⟨ eq ⟩ | inj₂  not-flat  = (GOAL(CoalgListF B g (a ◁ s))(10))
decon (fill a bs) | b ∷⟨ eq(CXT(g s ≡ just (b , s'))) ⟩ bs'(CXT(CoalgList B g s')) =
  let (b' , a') LETEQ piece (a , b) in b' ∷⟨ (GOAL(g (a ◁ s) ≡ just (b' , a' ◁ s'))(6)) ⟩ fill a' bs'
\end{code}
At Goal~9, we know that |a|~is flat, so it is fine to produce an empty colist; the proof obligation is easily discharged with |flat eq|, where |flat| is the proof given by |flat?| affirming that |a|~is flat.

For Goal~10, we want to invoke |piece| and produce a non-empty colist.
However, the input colist is empty, so we do not have a vertical input edge for |piece|.
The situation is not entirely clear here, but let us make some choices first and see if they make sense later.
Without an input vertical edge, let us again introduce a |constant straight : B|, which solves the problem with |piece|.
Also, in the coinductive call that generates the tail, we use~|bs| (the only colist available in the context) as the second argument:
\begin{code}
fill : {s : S} (a : A) → CoalgList B g s → CoalgList B g (a ◁ s)
decon (fill a bs(CXT(CoalgList B g s))) with decon bs
decon (fill a bs) | ⟨ eq(CXT(g s ≡ nothing)) ⟩ with flat? a
decon (fill a bs) | ⟨ eq ⟩ | inj₁ flat      = ⟨ flat eq ⟩
decon (fill a bs) | ⟨ eq ⟩ | inj₂ not-flat  =
  let (b' , a') LETEQ piece (a , straight) in b' ∷⟨ (GOAL(g (a ◁ s) ≡ just (b' , a' ◁ s))(11)) ⟩ fill a' bs
decon (fill a bs) | b ∷⟨ eq(CXT(g s ≡ just (b , s'))) ⟩ bs'(CXT(CoalgList B g s')) =
  let (b' , a') LETEQ piece (a , b) in b' ∷⟨ (GOAL(g (a ◁ s) ≡ just (b' , a' ◁ s'))(6)) ⟩ fill a' bs'
\end{code}

\varparagraph{Porting the jigsaw condition from the infinite case to the general (possibly finite) case.}
Now let us examine whether our choices are sensible.
The expected type at Goal~11 can be depicted as:
\begin{equation}
\begin{tikzpicture}[x=12em,y=4em,baseline=(u.base)]
\node(x) [anchor=center] {|s|};
\node(x') [below=1 of x,anchor=center] {|s|};
\node(hx) [left=1 of x,anchor=center] {|a ◁ s|};
\node(hx') [left=1 of x',anchor=center] {|a' ◁ s|};
\draw[serif cm-to] (x) edge node[above]{consume~|a| using~|f|} (hx);
\draw[serif cm-to] (x') edge node[below]{consume~|a'| using~|f|} (hx');
\draw[serif cm-to] (x) edge[dashed] node(t)[right]{(produce |stright| using~|g|)} (x ||- x'.north);
\draw[serif cm-to] (hx) edge node(u)[left]{produce~|b'| using~|g|} (hx ||- hx'.north);
%\node at ($(t)!0.5!(u)$) [anchor=center] {$\Leftarrow$};
\end{tikzpicture}
\label{eq:jigsaw-nothing}
\end{equation}
The dashed transition on the right is not a real state transition --- we know that |s|~is an empty state since in the context we have |eq : g s ≡ nothing|.
Completing the above diagram~(\ref{eq:jigsaw-nothing}) with the dashed transition allows us to compare it with the diagram~(\ref{eq:jigsaw-infinite}) for the infinite jigsaw condition, and the key to the comparison is to link the notions of empty states in the infinite case and the general (possibly finite) case.
In the infinite case, we have a condition |straight-production : g∞ e ≡ (straight , e)| saying that the |straight| edge is produced from the empty state~|e|, which remains unchanged after production.
We could have defined empty states in the infinite case to be the states~|s| such that |g∞ s ≡ (straight , s)| (although this was not necessary).
Now, the general (possibly finite) case can be thought of as an optimisation of the infinite case.
We stop producing |straight| edges from empty states --- that is, we modify the coalgebra to return |nothing| from empty states --- because these |straight| edges provide no information: if we omit, and only omit, the production of these |straight| edges, then whenever a vertical input edge is missing we know that it can only be |straight|.
However, the modification to the coalgebra destroys the production transitions from empty states in the infinite jigsaw condition. What remains is condition~(\ref{eq:jigsaw-just}), and cases involving empty states and |straight| edges as depicted by the diagram~(\ref{eq:jigsaw-nothing}) above are left out.

One thing we can do is merging diagram~(\ref{eq:jigsaw-nothing}) back into condition~(\ref{eq:jigsaw-just}) by relaxing the latter's premise:
\begin{code}
constant
  jigsaw-condition :
    {a : A} {b : B} {s s' : S} →
    g s ≡ just (b , s') ⊎ (g s ≡ nothing × g (a ◁ s) ≢ nothing × b ≡ straight × s' ≡ s) →
    let (b' , a') LETEQ piece (a , b) in g (a ◁ s) ≡ just (b' , a' ◁ s')
\end{code}
Note that we include |g (a ◁ s) ≢ nothing| in the new part of the premise to rule out the case where |a|~is flat.
A proof of this type should come from |flat?|, so at Goal~8 we make |flat?| return a proof of |{s : S} → g (a ◁ s) ≢ nothing| when the input element~|a| is not flat.
Finally, having |jigsaw-condition| in the context is informative enough for Auto to discharge both Goals 6~and~11 for us, and we arrive at the complete program in \autoref{fig:jigsaw-general}.

\varparagraph{Comparison with \varcitet{Nakano-jigsaw}{'s} jigsaw condition.}
How do our conditions compare with \varcitet{Nakano-jigsaw}{'s}?
Ours seem to be weaker, but this is probably because our algorithm is not as sophisticated as it can be.
\citeauthor{Nakano-jigsaw} imposes three conditions, which he refers to collectively as the jigsaw condition: the first one is exactly our |nothing-from-e|, the second one is related to flat elements but more complicated than our corresponding formulation, and the third one, though requiring some decoding, is almost our |jigsaw-condition|.
Comparing \citeauthor{Nakano-jigsaw}'s third condition with our |jigsaw-condition| reveals that there is one possibility that we did not consider: at Goal~5 we went ahead and produced a non-empty colist, but producing an empty colist was also a possibility.
Our current |jigsaw| algorithm produces columns of non-decreasing lengths from right to left like:
\[ \includegraphics{figs/heapsort-optimised-crop.pdf} \]
If we performed some case analysis at Goal~5 like for Goal~4, we might have been able to come up with an algorithm that can decrease column lengths when going left, saving more jigsaw pieces.

\begin{figure}
\beforefigurecode
\begin{code}
module Jigsaw-General
  ((◁) : A → S → S) (e : S) (g : S → Maybe (B × S))
  (piece : A × B → B × A)
  (straight : B)
  (flat? : (a : A) →  ({s : S} → g s ≡ nothing → g (a ◁ s) ≡ nothing) ⊎
                      ({s : S} → g (a ◁ s) ≢ nothing))
  (nothing-from-e : g e ≡ nothing)
  (jigsaw-condition :
    {a : A} {b : B} {s s' : S} →
    g s ≡ just (b , s') ⊎ (g s ≡ nothing × g (a ◁ s) ≢ nothing × b ≡ straight × s' ≡ s) →
    let (b' , a') LETEQ piece (a , b) in g (a ◁ s) ≡ just (b' , a' ◁ s'))
  where

  fill : {s : S} (a : A) → CoalgList B g s → CoalgList B g (a ◁ s)
  decon (fill a bs) with decon bs
  decon (fill a bs) | ⟨ eq ⟩ with flat? a 
  decon (fill a bs) | ⟨ eq ⟩ | inj₁ flat      = ⟨ flat eq ⟩
  decon (fill a bs) | ⟨ eq ⟩ | inj₂ not-flat  =
    let  (b' , a') LETEQ piece (a , straight)
    in   b' ∷⟨ jigsaw-condition (inj₂ (eq , not-flat , refl , refl)) ⟩ fill a' bs
  decon (fill a bs) | b ∷⟨ eq ⟩ bs' =
    let  (b' , a') LETEQ piece (a , b)
    in   b' ∷⟨ jigsaw-condition (inj₁ eq) ⟩ fill a' bs'

  jigsaw : {s : S} → AlgList A (◁) e s → CoalgList B g s
  decon (jigsaw [])  = ⟨ nothing-from-e ⟩
  jigsaw (a ∷ as)    = fill a (jigsaw as)
\end{code}
\caption{General (possibly finite) jigsaw metamorphisms}
\label{fig:jigsaw-general}
\end{figure}

\section{Discussion}

Faithful documentation of actual developments (except that\ldots)

Asymmetric treatment of index equality of |AlgList| and |CoalgList|; ``green slime''~\citep{McBride-pivotal}; |AlgList| specialises the context, which is propagated into |CoalgList|, forming proof obligations.

Work with proofs, not hide them \citep{McBride-pivotal}.

|CoalgList B g| is interesting when its elements are actually computed by mechanisms other than~|g|.
Index-level order of computation may differ from the data-level order (traditional vs index-first inductive families; there is probably a similar story for coinductive families).
Relationship with \citet{Thibodeau-indexed-codata-types}.

It is not just reducing the activity of program design to type design and good type inhabitation algorithms --- types do not determine programs.
Correctness concerns are moved into the types and enforced, but the programmer still gets to make decisions about algorithmic details.

``situation awareness''

It is interesting to compare our implementation with the proofs of \citet{Bird-arithmetic-coding}.
While their Lemma~29 turns explicitly into our |streaming-lemma|, their Theorem~30 goes implicitly into the typing of |stream| and no longer needs special attention.
The structure of |stream| already matches that of \citeauthor{Bird-arithmetic-coding}'s proof of their Theorem~30, and the principled type design using algebraic ornamentation elegantly loads the proof onto the structure of |stream|.

Intermediate variable conjecture (comparison with extrinsic proofs)

Contrast with verification condition extraction; possibility to stop nonsensical program development early, which is not possible with extrinsic development

Extensional properties vs intensional design

Generality? Perhaps not much. For example, ``metaphorisms''~\citep{Oliveira-metaphorisms} --- optimising metamorphisms --- will probably need a more involved development similar to \varcitet{Ko-algOrn}{'s}.

%% Acknowledgements
\begin{acks}                            %% acks environment is optional
                                        %% contents suppressed with 'anonymous'
  %% Commands \grantsponsor{<sponsorID>}{<name>}{<url>} and
  %% \grantnum[<url>]{<sponsorID>}{<number>} should be used to
  %% acknowledge financial support and will be used by metadata
  %% extraction tools.
The author thanks Shin-Cheng Mu and Jeremy Gibbons for the discussions during and after ICFP 2017 in Oxford.
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