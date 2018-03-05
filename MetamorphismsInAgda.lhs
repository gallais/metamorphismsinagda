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

%format ◁ = "{\lhd}"
%format _◁_ = _ ◁ _
%format ▷ = "{\kern.5pt\rhd\kern-1pt}"
%format _▷_ = _ ▷ _
%format Rational = "\mathbb{Q}"
%format Nat = "\mathbb{N}"
%format S_C = "S_\mathrm{\kern.5ptC}"
%format ▷ᶜ = "\kern.5pt{\rhd}_\mathrm{C}\kern-.5pt"
%format _▷ᶜ_ = _ ▷ᶜ _
%format g_C = "g_\mathrm{\kern1ptC}"
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

\newcommand{\varparagraph}[1]{\par\textit{#1}\hspace{.5em}} % {\textit{#1}\hspace{.5em}}
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

Formally, a metamorphism is a \emph{fold} followed by an \emph{unfold}, the former consuming a finite data structure and the latter producing a potentially infinite codata structure.
For list metamorphisms, the inputs to be consumed are the standard finite lists:
\begin{code}
data List (A : Set) : Set where
  []   : List A
  _∷_  : A → List A → List A
\end{code}
The |foldr| operator subsumes the elements (of type~|A|) of a list into a state (of type~|S|) using a ``right algebra'' |_◁_ : A → S → S| and an initial (empty) state |e : S|:%
\footnote{In \Agda, a name with underscores like |_◁_| can be used as an operator, and the underscores indicate where the arguments go.
Also, in the type of a function, arguments wrapped in curly brackets are implicit, and can be left out (if they are inferable by \Agda) when applying the function.}
\begin{code}
foldr : {A S : Set} → (A → S → S) → S → List A → S
foldr _◁_ e []        = e
foldr _◁_ e (a ∷ as)  = a ◁ foldr f e as
\end{code}
With |foldr|, a list is consumed from the right (cf.~wind direction).
Dually, the |foldl| operator consumes a list from the left using a ``left algebra'' |_▷_ : S → A → S|:
\begin{code}
foldl : {A S : Set} → (S → A → S) → S → List A → S
foldl _▷_ e []        = e
foldl _▷_ e (a ∷ as)  = foldl _▷_ (e ▷ a) as
\end{code}
A list metamorphism can use either |foldr| or |foldl| in its consuming part, and we will see both kinds in the paper.
We will refer to a list metamorphism using |foldr| as a ``right metamorphism'', and one using |foldl| as a ``left metamorphism''.

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
This depends on whether |g|~can produce anything from~|s|, so, using the |with| construct, we introduce the expression |g s| as an additional ``argument'', on which we can then perform a pattern match.
If |g s| is |nothing|, then the resulting colist will be empty --- that is, |decon (unfoldr g s)| will compute to |[]|;
otherwise, |g s| is |just (b , s')| for some |b|~and~|s'|, and the resulting colist will have |b|~as its head and |unfoldr g s'| as its tail --- that is, |decon (unfoldr g s)| will compute to |b ∷ unfoldr g s'|.

To be more concrete, let us describe our two examples --- base conversion for fractions and heapsort --- explicitly as metamorphisms.

\varparagraph{Base conversion for fractions.}
Suppose that the input and output bases are |b_i : Nat| and |b_o : Nat| --- in $0.625_{10} = 0.101_2$, for example, $b_i = 10$ and $b_o = 2$.
We represent fractions as (co)lists of digits (of type~|Nat|) starting from the most significant digit --- for example, $0.625$ is represented as |{-"6\;"-} ∷ {-"2\;"-} ∷ {-"5\;"-} ∷ []|.
To make the story short later,%
\footnote{\citet{Gibbons-metamorphisms} gives a more complete story, where base conversion for fractions is first described as a right metamorphism with simple states (consisting of only an accumulator), and then transformed to a left metamorphism with more complex states.}
we describe base conversion for fractions as a left metamorphism:
\begin{code}
unfoldr g_C ∘ foldl _▷ᶜ_ e_C
\end{code}
where the state type is |S_C LETEQ Rational × Rational × Rational|, which are triples of the form |(v , w_i , w_o)| where |v|~is an accumulator, |w_i| the weight of the incoming input digit, and |w_o| the weight of the outgoing output digit.
The initial (empty) state |e_C| is |({-"0\;"-} , {-"\nicefrac{1}{\identifier{b_i}}\;"-} , {-"\;\nicefrac{1}{\identifier{b_o}}"-})|.
The left algebra~|_▷ᶜ_| adds the the product of the current input digit and its weight to the accumulator, and updates the input weight in preparation for the next input digit:
\begin{code}
_▷ᶜ_ : S_C → Nat → S_C
(v , w_i , w_o) ▷ᶜ d = ({-"\identifier{v} + d \times w_i\;"-} , {-"\nicefrac{w_i}{b_i}\;"-}, w_o)
\end{code}
while the coalgebra~|g_C| produces an output digit and updates the accumulator and the next output weight if the accumulator is not yet zero:
\begin{code}
g_C (v , w_i , w_o) =  let  d  LETEQ {-"\;\lfloor\nicefrac{\identifier{v}\kern1pt}{\identifier{w_o}}\rfloor"-}; r  LETEQ {-"\;\identifier{v} - d \times \identifier{w_o}"-}
                       in   if {-"\identifier{v} > 0\;"-} then  just (d , (r , w_i , {-"\;\nicefrac{\identifier{w_o}\kern1pt}{\identifier{b_o}}"-})) else  nothing
\end{code}
For the example $0.625_{10} = 0.101_2$, the metamorphism first consumes the input digits using~|_▷ᶜ_|\,:
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
where |empty| is the empty heap, |push| adds an element into a heap, and |popMin| returns the minimum element and the rest of the input heap if and only if the input heap is non-empty.
Then heapsort can be directly described as a right metamorphism:
\begin{code}
unfoldr popMin ∘ foldr push empty
\end{code}

\section{Specification of Metamorphisms in Types}
\label{sec:spec}

In the rest of this paper we will develop several \emph{metamorphic algorithms}, which compute a metamorphism but do not take the form of a fold followed by an unfold.
Rather than proving that these algorithms satisfy their metamorphic specifications, we will encode metamorphic specifications in types, such that any type-checked program is a correct metamorphic algorithm.

The encoding is based on \varcitet{McBride-ornaments}{'s} \emph{algebraic ornamentation}.
Given a right algebra |_◁_ : A → S → S| and |e : S|, we can partition |List A| into a family of types |AlgList A f e : S → Set| indexed by~|S| such that (conceptually) every list~|as| falls into the type |AlgList A f e (foldr _◁_ e as)|.
The definition of |AlgList| is obtained by ``fusing'' |foldr| into |List|:
\begin{code}
data AlgList (A {S} : Set) (_◁_ : A → S → S) (e : S) : S → Set where
  []   : AlgList A f e e
  _∷_  : (a : A) → {s : S} → AlgList A f e s → AlgList A f e (a ◁ s)
\end{code}
The empty list is classified under the index |e LETEQ foldr f e []|.
For the cons case, if a tail~|as| is classified under~|s|, meaning that |foldr _◁_ e as LETEQ s|, then the whole list |a ∷ as| should be classified under |a ◁ s| since |foldr _◁_ e (a ∷ as) = a ◁ foldr _◁_ e as = a ◁ s|.

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

Let |A|, |B|, |S : Set| throughout the rest of this paper%
\footnote{That is, think of the code in the rest of this paper as contained in a module with parameters |A|, |B|, |S : Set|.}
--- we will assume that |A|~is the type of input elements, |B|~the type of output elements, and |S|~the type of states.
We will also consistently let |_◁_ : A → S → S| denote a right algebra, |_▷_ : S → A → S| a left algebra, |e : S| an initial (empty) state, and |g : S → Maybe (B × S)| a coalgebra.
Now any program of type:
\begin{code}
{s : S} → AlgList A _◁_ e s → CoalgList B g s
\end{code}
implements the right metamorphism |unfoldr g ∘ foldr _◁_ e|, since the indexing enforces that the input list folds to~|s|, from which the output colist is then unfolded.

What about left metamorphisms?
Thankfully, we do not need to define another variant of |AlgList| due to an old trick that expresses |foldl| in terms of |foldr|.
Given a list |as : List A|, think of the work of |foldl _▷_ e as| as (i)~partially applying |flip _▷_ : A → S → S| (where |flip f x y LETEQ f y x|) to every element of~|as| to obtain state transformations of type |S → S|, (ii)~composing the state transformations from left to right, and finally (iii)~applying the resulting composite transformation to~|e|.
The left-to-right order appears only in step~(ii), which, in fact, can also be performed from right to left since function composition is associative.
Formally, we have:
\begin{code}
foldl _▷_ e as = foldr (left-alg _▷_) id as e
\end{code}
where
\begin{code}
left-alg : {A S : Set} → (S → A → S) → A → (S → S) → (S → S)
left-alg _▷_ a t = t ∘ flip _▷_ a
\end{code}
The type of left metamorphic algorithms can then be specified as:
\begin{code}
{h : S → S} → AlgList A (left-alg _▷_) id h → (s : S) → CoalgList B g (h s)
\end{code}
which says that if the input list folds to a state transformation~|h| and the initial state is~|s|, then the output colist should be unfolded from |h s|.

\section{Definitional Implementation of Metamorphisms}
\label{sec:cbp}

To warm up, let us start from the left metamorphic type and implement the most straightforward algorithm that strictly follows the definition of metamorphisms, \textbf{c}onsuming all inputs \textbf{b}efore \textbf{p}roducing outputs:
\begin{code}
cbp : {h : S → S} → AlgList A (left-alg _▷_) id h → (s : S) → CoalgList B g (h s)
cbp as(CXT(AlgList A (left-alg _▷_) id h)) s = (GOAL(CoalgList B g (h s))(0))
\end{code}
\Agda\ provides an interactive development environment as an emacs mode.
In this environment, we can leave ``holes'' in programs and fill or refine them, often with \Agda's help.
Such a hole is called an \emph{interaction point} or a \emph{goal}, of which the \highlight{goal}{\text{green-shaded part}} above is an example.
At goals, \Agda\ can be instructed to provide various information and even perform some program synthesis (with an ``Auto'' command).
One most important piece of information for a goal is its expected type, which we always display in curly brackets.
Goals are numbered when they need to be referred to in the text.
At goals, we can also query the types of the variables in scope; whenever the type of a variable needs to be displayed, we will annotate the variable with its type in \highlight{cxt}{\text{yellow-shaded subscript}} (which is not part of the program text).
In the partial program above, we give the type of~|as| because the goal type refers to~|h|, which is the index in the type of~|as|.

Back to the program itself.
We are trying to consume the input list first, so we pattern match on the argument |as| to see if there is anything to consume.
In \Agda\ this is as easy as putting |as| into Goal~0 and firing a ``case splitting'' command (\texttt{C-c C-c}); the program will then be split into two clauses, listing all possible cases of~|as|:
\begin{code}
cbp []                                            s = (GOAL(CoalgList B g s)(1))
cbp (a ∷ as(CXT(AlgList A (left-alg _▷_) id h)))  s = (GOAL(CoalgList B g (h (f s a)))(2))
\end{code}
Now Goal~0 is gone, and two new goals appear.
Note that the expected types of the two new goals have changed: at Goal~1, for example, we see that the output colist should be unfolded directly from the initial state~|s| since the input list is empty.
By providing sufficient type information, \Agda\ can keep track of such relationship for us!
We continue to interact with and refine these two new goals.

If there is something to consume, that is, the input list is non-empty, we go into Goal~2, where we keep consuming the tail |as| but from a new state:
\begin{code}
cbp (a ∷ as) s = cbp as (GOAL(S)(3))
\end{code}
What is this new state? It should be the one obtained by subsuming~|a| into~|s|, i.e., |s ▷ a|.
\Agda\ knows this too, in fact --- firing the ``Auto'' command (\texttt{C-c C-a}) at Goal~3 yields:
\begin{code}
cbp (a ∷ as) s = cbp as (s ▷ a)
\end{code}

If there is nothing more to consume, that is, the input list is empty, we go into Goal~1, where we should produce the output colist, to specify which we should say what will result if we |decon|struct the colist:
\begin{code}
decon (cbp [] s) = (GOAL(CoalgListF B g s)(4))
\end{code}
The result of observation depends on whether |g|~can produce anything from the current state~|s|, so we pattern match on |g s|, splitting Goal~4 into:
\begin{code}
decon (cbp [] s) with g s
decon (cbp [] s) | nothing        = (GOAL(CoalgListF B g s)(5))
decon (cbp [] s) | just (b , s')  = (GOAL(CoalgListF B g s)(6))
\end{code}
If |g s| is |nothing| (Goal~5), the output colist is empty; otherwise |g s| is some |just (b , s')| (Goal~6), in which case we use~|b| as the head and continue to produce the tail from~|s'|.
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
decon (cbp [] s) with g s         | inspect g s
decon (cbp [] s) | nothing        | [ eq(CXT(g s ≡ nothing))        ] = ⟨ (GOAL(g s ≡ nothing)(7)) ⟩
decon (cbp [] s) | just (b , s')  | [ eq(CXT(g s ≡ just (b , s')))  ] = b ∷⟨ (GOAL(g s ≡ just (b , s'))(8)) ⟩ cbp [] s'
\end{code}
Both goals can now be discharged with |eq|, and we arrive at a complete program, shown in \autoref{fig:cbp}.
As explained in \autoref{sec:spec}, this program is a correct metamorphic algorithm because it type-checks.

\begin{figure}
\beforefigurecode
\begin{code}
module ConsumingBeforeProducing
  (_▷_ : S → A → S) (g : S → Maybe (B × S))
  where

  cbp : {h : S → S} → AlgList A (left-alg _▷_) id h → (s : S) → CoalgList B g (h s)
  decon (cbp [] s) with g s         | inspect g s
  decon (cbp [] s) | nothing        | [ eq ] = ⟨ eq ⟩
  decon (cbp [] s) | just (b , s')  | [ eq ] = b ∷⟨ eq ⟩ cbp [] s'
  cbp (a ∷ as) s = cbp as (s ▷ a)
\end{code}
\caption{Definitional implementation of metamorphisms}
\label{fig:cbp}
\end{figure}

\section{Streaming Metamorphisms}
\label{sec:streaming}

As \citet{Gibbons-metamorphisms} noted, (list) metamorphisms in general cannot be automatically optimised in terms of time and space, but under certain conditions it is possible to refine a list metamorphism to a \emph{streaming algorithm} --- which can produce an initial segment of the output list without consuming all of the input list.%
\todo{\ldots}\
Again let |f : S → A → S| and |g : S → Maybe (B × S)|.
We implement a different algorithm with the same type:
\begin{code}
stream : {h : S → S} → AlgList A (left-alg f) id h → (s : S) → CoalgList B g (h s)
stream as s = (GOAL(CoalgList B g (h s))(0))
\end{code}

Different from |cbp| (\autoref{sec:cbp}/\autoref{fig:cbp}), this time we try to produce using~|g| whenever possible, so our first step is to pattern match on |g s| (and we are also introducing |decon| and |inspect|, which will be needed like in |cbp|):
\begin{code}
decon (stream as s) with g s         | inspect g s
decon (stream as s) | nothing        | [ eq ] = (GOAL(CoalgListF B g (h s))(1))
decon (stream as s) | just (b , s')  | [ eq ] = (GOAL(CoalgListF B g (h s))(2))
\end{code}

For Goal~1, we cannot produce anything since |g s| is |nothing|, but this does not mean that the output colist is empty --- we may be able to produce something once we consume the input list and advance to a new state.
We therefore pattern match on the input list:
\begin{code}
decon (stream []        s) | nothing | [ eq ] = (GOAL(CoalgListF B g s)(3))
decon (stream (a ∷ as)  s) | nothing | [ eq ] = (GOAL(CoalgListF B g (h' (f s a)))(4))
\end{code}
These two goals are similar to what we have seen in |cbp|.
At Goal~3, there is nothing more in the input list to consume, so we should end production as well, emitting an empty colist, while for Goal~4 (where |h'|~is the index in the type of the tail~|as|) we should advance to the new state |f s a| and set the tail |as| as the list to be consumed next:
\begin{code}
decon (stream []        s) | nothing | [ eq ] = ⟨ eq ⟩
decon (stream (a ∷ as)  s) | nothing | [ eq ] = decon (stream as (f s a))
\end{code}

Goal~2 is the interesting case.
Using~|g|, from the current state~|s| we can produce~|b|, which we set as the head of the output colist, and advance to a new state~|s'|, from which we produce the tail of the colist:
\begin{code}
decon (stream as(CXT(AlgList A (left-alg f) id h)) s) | just (b , s') | [ eq(CXT(g s ≡ just (b , s'))) ] =
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
We already have in the context a similar-looking equality, namely |eq : g s ≡ just (b , s')|, which we can superimpose on the diagram:
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
\begin{equation}
\begin{tikzpicture}[x=12em,y=4em,baseline=(u.base)]
\node(x) [anchor=center] {|s|};
\node(x') [below=1 of x,anchor=center] {|s'|};
\node(hx) [right=1 of x,anchor=center] {|h s|};
\node(hx') [right=1 of x',anchor=center] {|h s'|};
\draw[serif cm-to] (x) edge node[above]{consume~|as| with~|h|} (hx);
\draw[serif cm-to] (x') edge node[below]{consume~|as| with~|h|} (hx');
\draw[serif cm-to] (x) edge node(t)[left]{produce~|b| with~|g|} (x ||- x'.north);
\draw[serif cm-to] (hx) edge node(u)[right]{produce~|b| with~|g|} (hx ||- hx'.north);
\node at ($(t)!0.5!(u)$) [anchor=center] {$\Rightarrow$};
\end{tikzpicture}
\label{eq:streaming-big-step}
\end{equation}
This is a kind of commutativity of production and consumption:
From the initial state~|s|, we can either
\begin{itemize}
\item apply~|g| to~|s| to \emph{produce}~|b| and reach a new state~|s'|, and then apply~|h| to \emph{consume} the list and update the state to~|h s'|, or
\item apply~|h| to~|s| to \emph{consume} the list and update the state to~|h s|, and then apply~|g| to~|h s| to \emph{produce} an element and reach a new state.
\end{itemize}
If the first route is possible, the second route should also be possible, and the outcomes should be the same --- doing production using~|g| and consumption using~|h| in whichever order should emit the same element and reach the same final state.
This cannot be true in general, and should be formulated as a condition of the streaming algorithm.

The above commutativity~(\ref{eq:streaming-big-step}) of |g|~and~|h| is commutativity of one step of production (using~|g|) and multiple steps of consumption of a particular list (using~|h|).
If we require instead that |g|~and~|f| commute, this commutativity of single-step production and consumption will be independent from the input list and become easier to verify:
\begin{equation}
\begin{tikzpicture}[x=12em,y=4em,baseline=(u.base)]
\node(x) [anchor=center] {|s|};
\node(x') [below=1 of x,anchor=center] {|s'|};
\node(hx) [right=1 of x,anchor=center] {|f s a|};
\node(hx') [right=1 of x',anchor=center] {|f s' a|};
\draw[serif cm-to] (x) edge node[above]{consume~|a| with~|f|} (hx);
\draw[serif cm-to] (x') edge node[below]{consume~|a| with~|f|} (hx');
\draw[serif cm-to] (x) edge node(t)[left]{produce~|b| with~|g|} (x ||- x'.north);
\draw[serif cm-to] (hx) edge node(u)[right]{produce~|b| with~|g|} (hx ||- hx'.north);
\node at ($(t)!0.5!(u)$) [anchor=center] {$\Rightarrow$};
\end{tikzpicture}
\label{eq:streaming}
\end{equation}
This is \varcitet{Gibbons-metamorphisms}{'s} \emph{streaming condition}, which is needed for proving the correctness of the streaming algorithm.
In our development of |stream|, we can assume that a proof of the streaming condition is available:
\begin{code}
streaming-condition :  {a : A} {b : B} {s s' : S} →
                       g s ≡ just (b , s') → g (f s a) ≡ just (b , f s' a)
\end{code}

Back to Goal~5, where we should prove the commutativity of |g|~and~|h|.
All it takes should be a straightforward induction to extend the streaming condition along the axis of consumption --- so straightforward, in fact, that \Agda\ can do most of the work for us!
We know that we need a helper function |streaming-lemma| that performs induction on |as| and uses |eq| as a premise; by filling |streaming-lemma as eq| into Goal~5 and firing a command (\texttt{C-c C-h}), \Agda\ can generate a type for |streaming-lemma|, which, after removing some over-generalisations and unnecessary definition expansions, is:
\begin{code}
streaming-lemma :  {b : B} {s s' : S} {h : S → S} →
                   AlgList A (left-alg f) id h → g s ≡ just (b , s') → g (h s) ≡ just (b , h s')
streaming-lemma as eq = (GOAL(g (h s) ≡ just (b , h s'))(6))
\end{code}
\Agda\ then accepts |streaming-lemma as eq| as a type-correct term for Goal~5, completing the definition of |stream|.

Now all that is left is the body of |streaming-lemma| (Goal~6).
If we give a hint that case-splitting is needed (\texttt{-c}), Auto can complete the definition of |streaming-lemma| on its own, yielding (modulo one cosmetic variable renaming):
\begin{code}
streaming-lemma []        eq = eq
streaming-lemma (a ∷ as)  eq = streaming-lemma as (streaming-condition eq)
\end{code}

\begin{code}
g_B (v , w_i , w_o) =  let  d  LETEQ {-"\;\lfloor\nicefrac{\identifier{v}\kern1pt}{\identifier{w_o}}\rfloor"-}; r  LETEQ {-"\;\identifier{v} - d \times \identifier{w_o}"-}
                       in   if {-"\identifier{v} > 0 \,\mathrel\wedge\, r + \identifier{b_i} \times \identifier{w_i} \leq \identifier{w_o}\;"-} then  just (d , (r , w_i , {-"\;\nicefrac{\identifier{w_o}\kern1pt}{\identifier{b_o}}"-})) else  nothing
\end{code}

\begin{figure}
\beforefigurecode
\begin{code}
module Streaming
  (f : S → A → S) (g : S → Maybe (B × S))
  (streaming-condition :  {a : A} {b : B} {s s' : S} →
                          g s ≡ just (b , s') → g (f s a) ≡ just (b , f s' a))
  where

  streaming-lemma :  {b : B} {s s' : S} {h : S → S} →
                     AlgList A (left-alg f) id h → g s ≡ just (b , s') → g (h s) ≡ just (b , h s')
  streaming-lemma []        eq = eq
  streaming-lemma (a ∷ as)  eq = streaming-lemma as (streaming-condition eq)

  stream : {h : S → S} → AlgList A (left-alg f) id h → (s : S) → CoalgList B g (h s)
  decon (stream as        s) with g s         | inspect g s
  decon (stream []        s) | nothing        | [ eq ] = ⟨ eq ⟩
  decon (stream (a ∷ as)  s) | nothing        | [ eq ] = decon (stream as (f s a))
  decon (stream as        s) | just (b , s')  | [ eq ] = b ∷⟨ streaming-lemma as eq ⟩ stream as s'
\end{code}
\caption{Streaming metamorphisms}
\label{fig:stream}
\end{figure}

\section{Jigsaw Metamorphisms: The Infinite Case}
\label{sec:jigsaw-infinite}

Back to the |foldr| version, but there is some problem with a definitional implementation.
\citet{Nakano-jigsaw}

Let |f : A → S → S|, |e : S|, |g : S → B × S|, and |piece : A × B → B × A|.

\subsection{Horizontal Placement}


\begin{code}
jigsawᵢₕ : {s : S} → AlgList A f e s → CoalgList B (just ∘ g) s
jigsawᵢₕ as = (GOAL(CoalgList B (just ∘ g) s)(0))
\end{code}

Our strategy is to place one row of jigsaw pieces at a time.
Placing a row is equivalent to transforming an input list |as| into a new one |as'| and also a vertical edge~|b|.
\todo[inline]{illustration}
We therefore introduce the following function |fillᵢₕ| for filling a row:
\begin{code}
fillᵢₕ : {s : S} → AlgList A f e s → B × Σ[ t ∈ S ] AlgList A f e t
fillᵢₕ as = (GOAL'(B × Σ[ t ∈ S ] AlgList A f e t))
\end{code}
We do not know (or cannot easily specify) the index~|t| in the type of the output |AlgList|, so the index is simply existentially quantified.
The job of |jigsawᵢₕ|, then, is to call |fillᵢₕ| repeatedly to cover the board:
\begin{code}
jigsawᵢₕ : {s : S} → AlgList A f e s → CoalgList B (just ∘ g) s
decon (jigsawᵢₕ as) with fillᵢₕ as
decon (jigsawᵢₕ as) | (b , t , as') = b ∷⟨ (GOAL(just (g s) ≡ just (b , t))(1)) ⟩ jigsawᵢₕ as'
\end{code}
Goal~1 demands an equality linking |s|~and~|t|, which are the input and output indices of |fillᵢₕ|.
This suggests that |fillᵢₕ| is responsible for not only computing~|t| but also establishing the relationship between |t|~and~|s|.
We therefore add the equality to the result type of |fillᵢₕ|, and discharge Goal~1 with the equality proof that will be produced by |fillᵢₕ|:
\begin{code}
fillᵢₕ : {s : S} → AlgList A f e s → Σ[ b ∈ B ] Σ[ t ∈ S ] AlgList A f e t × g s ≡ (b , t)
fillᵢₕ as = (GOAL(Σ[ b ∈ B ] Σ[ t ∈ S ] AlgList A f e t × g s ≡ (b , t))(2))

jigsawᵢₕ : {s : S} → AlgList A f e s → CoalgList B (just ∘ g) s
decon (jigsawᵢₕ as) with fillᵢₕ as
decon (jigsawᵢₕ as) | (b , _ , as' , eq) = b ∷⟨ cong just eq ⟩ jigsawᵢₕ as'
\end{code}

\varparagraph{The road not taken.}
From Goal~1, there seems to be another way forward: the equality says that the output vertical edge~|b| and the index~|t| in the type of~|as'| are determined by |g s|, so |jigsawᵢₕ| could have computed |g s| and obtained |b|~and~|t| directly!
However, recall that the characteristic of the jigsaw model is that computation proceeds by converting input list elements directly into output colist elements without involving states, which only appear in the specifications.%
\todo{irrelevance}\
In our setting, this means that states only appear in the function types, not the function bodies, so having |jigsawᵢₕ| invoke |g s| would deviate from the jigsaw model.
Instead, |jigsawᵢₕ| invokes |fillᵢₕ|, which will only use |piece| to compute~|b|.

Let us get back to work on |fillᵢₕ| (Goal~2).
The process of filling a row follows the structure of the input list, so overall it is an induction, of which the first step is a case analysis:
\begin{code}
fillᵢₕ []                            = (GOAL(Σ[ b ∈ B ] Σ[ t ∈ S ] AlgList A f e t × g e ≡ (b , t))(3))
fillᵢₕ (a ∷ as(CXT(AlgList f e s)))  = (GOAL(Σ[ b ∈ B ] Σ[ t ∈ S ] AlgList A f e t × g (f a s) ≡ (b , t))(4))
\end{code}
If the input list is empty (Goal~3), we return the rightmost ``flat'' edge.
We therefore assume the existence of a constant |flat-edge : B| and fill it into Goal~3:
\begin{code}
fillᵢₕ [] = (flat-edge , (GOAL(Σ[ t ∈ S ] AlgList A f e t × g e ≡ (flat-edge , t))(5)))
\end{code}
We should now give the output list, which we know should have the same length as the input list, so in this case it is easy to see that the output list should be empty as well (and, by giving an underscore as an instruction, \Agda\ can infer the index in the type of the output list):
\begin{code}
fillᵢₕ [] = (flat-edge , _ , [] , (GOAL(g e ≡ (flat-edge , e))(6)))
\end{code}
Here we arrive at another proof obligation, which says that from the initial state~|e| the coalgebra~|g| should produce |flat-edge| and leave the state unchanged.
This is a reasonable property to add as an assumption of the algorithm: if we want all the rightmost vertical edges to be ``flat'', it had better be the case that the initial state (at the top right corner) does give rise to a colist of |flat-edge|s.
We there add an additional assumption |flat-edge-production : g e ≡ (flat-edge , e)|, which discharges Goal~5.

The interesting case is when the input list is non-empty (Goal~4).
We start with an inductive call to |fillᵢₕ| itself:
\begin{code}
fillᵢₕ (a ∷ as(CXT(AlgList f e s))  ) with fillᵢₕ as
fillᵢₕ (a ∷ as                      ) | (b , s' , as' , eq) =
  (GOAL(Σ[ b ∈ B ] Σ[ t ∈ S ] AlgList A f e t × g (f a s) ≡ (b , t))(7))
\end{code}
With the inductive call, the jigsaw pieces below the tail~|as| have been placed, yielding a vertical edge~|b| and a list~|as'| of horizontal edges below~|as|.
\todo[inline]{illustration}
We should complete the row by placing the last jigsaw piece with |a|~and~|b| as input, and use the output edges in the right places:
\begin{code}
fillᵢₕ (a ∷ as(CXT(AlgList f e s))  ) with fillᵢₕ as
fillᵢₕ (a ∷ as                      ) | (b , s' , as' , eq(CXT(g s ≡ (b , s')))) =
  let (b' , a') LETEQ piece (a , b) in (b' , _ , a' ∷ as' , (GOAL(g (f a s) ≡ (b' , f a' s'))(8)))
\end{code}
Here we see a familiar pattern: Goal~8 demands an equality about producing from a state after consumption, and in the context we have an equality |eq| about producing from a state before consumption.
Following what we did in \autoref{sec:streaming}, a commutative state transition diagram can be drawn:
\begin{equation}
\begin{tikzpicture}[x=12em,y=4em,baseline=(u.base)]
\node(x) [anchor=center] {|s|\vphantom{|f|}};
\node(x') [below=1 of x,anchor=center] {|s'|\vphantom{|f|}};
\node(hx) [left=1 of x,anchor=center] {|f a s|};
\node(hx') [left=1 of x',anchor=center] {|f a' s'|};
\draw[serif cm-to] (x) edge node[above]{consume~|a| with~|f|} (hx);
\draw[serif cm-to] (x') edge node[below]{consume~|a'| with~|f|} (hx');
\draw[serif cm-to] (x) edge node(t)[right]{produce~|b| with~|g|} (x ||- x'.north);
\draw[serif cm-to] (hx) edge node(u)[left]{produce~|b'| with~|g|} (hx ||- hx'.north);
\node at ($(t)!0.5!(u)$) [anchor=center] {$\Leftarrow$};
\end{tikzpicture}
\label{eq:jigsaw}
\end{equation}
where |(b' , a') = piece (a , b)|.
This is again a kind of commutativity of production and consump\-tion, but unlike the streaming condition~(\ref{eq:streaming}) in \autoref{sec:streaming}, the elements produced and consumed can change after swapping the order of production and consumption.
Given any top and right edges |a|~and~|b|, the |piece| function can always compute the left and bottom edges |b'|~and~|a'| to complete the commutative diagram.
This constitutes a specification for |piece|, and we call it the \emph{jigsaw condition}:
\begin{code}
jigsaw-conditionᵢ :  {a : A} {b : B} {s s' : S} →
                     g s ≡ (b , s') → let (b' , a') LETEQ piece (a , b) in g (f a s) ≡ (b' , f a' s')
\end{code}
Adding |jigsaw-conditionᵢ| as the final assumption, we can fill |jigsaw-conditionᵢ eq| into Goal~8 and complete the program.

\subsection{Vertical Placement}

We have discovered conditions for computing metamorphisms in the infinite jigsaw model, but for only one particular placement strategy.
Do the same conditions work for a different placement strategy?
Let us find out!

A natural strategy to try next is to place jigsaw pieces vertically, one column at a time.
We start from exactly the same type:
\begin{code}
jigsawᵢᵥ : {s : S} → AlgList A f e s → CoalgList B (just ∘ g) s
jigsawᵢᵥ as = (GOAL(CoalgList B (just ∘ g) s)(0))
\end{code}
The placing of columns follows the structure of the input list, so |jigsawᵢᵥ| is itself an induction:
\begin{code}
jigsawᵢᵥ []                              = (GOAL(CoalgList B (just ∘ g) e)(1))
jigsawᵢᵥ (a ∷ as(CXT(AlgList A f e s)))  = (GOAL(CoalgList B (just ∘ g) (f a s))(2))
\end{code}
If the input list is empty (Goal~1), we should produce a colist of |flat-edge|s:
\begin{code}
decon (jigsawᵢᵥ []) = flat-edge ∷⟨ (GOAL(just (g e) ≡ just (flat-edge , e))(3)) ⟩ jigsawᵢᵥ []
\end{code}
The proof obligation here (Goal~3) is discharged with |cong just flat-edge-production|.
For the inductive case (Goal~2):
We place all the columns below the tail~|as| by an inductive call |jigsawᵢₕ as|, which gives us a colist of vertical edges.
To the left of this colist, we should place the last column below the head element~|a|; again we introduce a helper function |fillᵢᵥ| that takes |a|~and the colist as input and produces the colist of the leftmost edges:
\begin{code}
jigsawᵢᵥ (a ∷ as) = fillᵢᵥ a (jigsawᵢₕ as)
\end{code}
Agda again can give us a suitable type of |fillᵢᵥ|:
\begin{code}
fillᵢᵥ : {s : S} (a : A) → CoalgList B (just ∘ g) s → CoalgList B (just ∘ g) (f a s)
fillᵢᵥ a bs = (GOAL(CoalgList B (just ∘ g) (f a s))(4))
\end{code}
Here we should deconstruct |bs| so that we can invoke |piece| on |a|~and the first element of~|bs|:
\begin{code}
decon (fillᵢᵥ a bs(CXT(CoalgList B (just ∘ g) s))) with decon bs
decon (fillᵢᵥ a bs) | ⟨ eq(CXT(just (g s) ≡ nothing)) ⟩ = (GOAL(CoalgListF B (just ∘ g) (f a s))(5))
decon (fillᵢᵥ a bs) | b ∷⟨ eq(CXT(just (g s) ≡ just (b , s'))) ⟩ bs'(CXT(CoalgList B (just ∘ g) s')) =
  (GOAL(CoalgListF B (just ∘ g) (f a s))(6))
\end{code}
For Goal~5, since the coalgebra |just ∘ g| in the type of~|bs| never returns |nothing|, it is impossible for |bs| to be empty.
We can convince \Agda\ that this case is impossible by matching |eq| with the absurd pattern~|()|, saying that |eq| cannot possibly exist (and \Agda\ accepts this because a |just|-value can never be equal to |nothing|):
\begin{code}
decon (fillᵢᵥ a bs) | ⟨ () ⟩
\end{code}
For Goal~6, we invoke the |piece| function to transform |a|~and~|b| to |b'|~and~|a'|; the head of the output colist is then~|b'|, and the tail is coinductively computed from |a'|~and~|bs'|.
\begin{code}
decon (fillᵢᵥ a bs) | b ∷⟨ eq(CXT(just (g s) ≡ just (b , s'))) ⟩ bs'(CXT(CoalgList B (just ∘ g) s')) =
  let (b' , a') LETEQ piece (a , b) in b' ∷⟨ (GOAL(just (g (f a s)) ≡ just (b' , f a' s'))(7)) ⟩ fillᵢᵥ a' bs'
\end{code}
The remaining proof obligation can indeed be discharged with the jigsaw condition, modulo the harmless occurrences of |just|.

\todo[inline]{Not too surprising though, if we think about how |jigsawᵢᵥ| will be evaluated.}

\begin{figure}
\beforefigurecode
\begin{code}
module Jigsaw-Infinite
  (f : A → S → S) (e : S) (g : S → B × S)
  (piece : A × B → B × A)
  (jigsaw-conditionᵢ :  {a : A} {b : B} {s s' : S} →
                        g s ≡ (b , s') → let (b' , a') LETEQ piece (a , b) in g (f a s) ≡ (b' , f a' s'))
  (flat-edge : B) (flat-edge-production : g e ≡ (flat-edge , e))
  where

  fillᵢₕ : {s : S} → AlgList A f e s → Σ[ b ∈ B ] Σ[ t ∈ S ] AlgList A f e t × g s ≡ (b , t)
  fillᵢₕ [] = flat-edge , _ , [] , flat-edge-production
  fillᵢₕ (a ∷ as) with fillᵢₕ as
  fillᵢₕ (a ∷ as) | b , _ , as' , eq =  let  (b' , a') LETEQ piece (a , b)
                                        in   b' , _ , a' ∷ as' , jigsaw-conditionᵢ eq

  jigsawᵢₕ : {s : S} → AlgList A f e s → CoalgList B (just ∘ g) s
  decon (jigsawᵢᵥ as) with fillᵢₕ as
  decon (jigsawᵢᵥ as) | b , _ , as' , eq = b ∷⟨ cong just eq ⟩ jigsawᵢᵥ as'

  fillᵢᵥ : {s : S} (a : A) → CoalgList B (just ∘ g) s → CoalgList B (just ∘ g) (f a s)  
  decon (fillᵢᵥ a bs) with decon bs
  decon (fillᵢᵥ a bs) | ⟨ () ⟩
  decon (fillᵢᵥ a bs) | b ∷⟨ eq ⟩ bs' =
    let  (b' , a') LETEQ piece (a , b)
    in   b' ∷⟨ cong just (jigsaw-conditionᵢ (cong-from-just eq)) ⟩ fillᵢᵥ a' bs'

  jigsawᵢᵥ : {s : S} → AlgList A f e s → CoalgList B (just ∘ g) s
  decon (jigsawᵢᵥ []) = flat-edge ∷⟨ cong just flat-edge-production ⟩ jigsawᵢᵥ []
  jigsawᵢᵥ (a ∷ as) = fillᵢᵥ a (jigsawᵢᵥ as)
\end{code}
\caption{Infinite jigsaw metamorphisms}
\label{fig:jigsaw-infinite}
\end{figure}

\section{Jigsaw Metamorphisms: The General (Possibly Finite) Case}
\label{sec:jigsaw-general}

Let |f : A → S → S|, |e : S|, and |g : S → Maybe (B × S)|.

\begin{code}
jigsaw : {s : S} → AlgList A f e s → CoalgList B g s
jigsaw as = (GOAL(CoalgList B g s)(0))
\end{code}
We use the vertical placement strategy, so the overall structure will be similar to |jigsawᵢᵥ| in \autoref{sec:jigsaw-infinite}.
Start from a case analysis:
\begin{code}
jigsaw []                              = (GOAL(CoalgList B g e)(1))
jigsaw (a ∷ as(CXT(AlgList A f e s)))  = (GOAL(CoalgList B g (f a s))(2))
\end{code}
At Goal~1, it should suffice to produce an empty colist:
\begin{code}
decon (jigsaw []) = ⟨ (GOAL(g e ≡ nothing)(3)) ⟩
\end{code}
To do so we need |g e ≡ nothing|, which is a reasonable assumption --- |e|~is intuitively an empty state, from which |g|~should produce |nothing|.
For Goal~2, we proceed in exactly the same way as we dealt with the corresponding case of |jigsawᵢᵥ|:
\begin{code}
jigsaw (a ∷ as) = fill a (jigsaw as)
\end{code}
where the type and the top-level structure of the helper function |fill| is also exactly the same as |fillᵢᵥ|:
\begin{code}
fill : {s : S} (a : A) → CoalgList B g s → CoalgList B g (f a s)
decon (fill a bs(CXT(CoalgList B g s))) with decon bs
decon (fill a bs) | ⟨ eq(CXT(g s ≡ nothing)) ⟩ = (GOAL(CoalgListF B g (f a s))(4))
decon (fill a bs) | b ∷⟨ eq(CXT(g s ≡ just (b , s'))) ⟩ bs'(CXT(CoalgList B g s')) = (GOAL(CoalgListF B g (f a s))(5))
\end{code}
The situation gets more interesting from this point.

Let us work on the familiar case first, namely Goal~5.
If we do the same thing as the corresponding case of |fillᵢᵥ|:
\begin{code}
decon (fill a bs) | b ∷⟨ eq(CXT(g s ≡ just (b , s'))) ⟩ bs'(CXT(CoalgList B g s')) =
  let (b' , a') LETEQ piece (a , b) in b' ∷⟨ (GOAL'(g (f a s) ≡ just (b' , f a' s'))) ⟩ fill a' bs'
\end{code}
we will see that the condition we need is depicted exactly as diagram~(\ref{eq:jigsaw}).
Formally it is slightly different though, because we need to wrap the results of~|g| in the |just| constructor:
\begin{flalign}
\hspace\mathindent
& |{a : A} {b : B} {s s' : S} →| \nonumber & \\[-.5ex]
& |g s ≡ just (b , s') → let (b' , a') LETEQ piece (a , b) in g (f a s) ≡ just (b' , f a' s'))| &
\label{eq:jigsaw-just}
\end{flalign}

Goal~4, unlike the corresponding case of |fillᵢᵥ|, is no longer impossible.
We might be tempted to produce an empty colist here:
\begin{code}
decon (fill a bs) | ⟨ eq(CXT(g s ≡ nothing)) ⟩ = ⟨ (GOAL'(g (f a s) ≡ nothing)) ⟩
\end{code}
But the proof obligation indicates that this is not a right choice.
From an empty state~|s| (i.e., |g s ≡ nothing|) we have to deduce that the next state |f a s| is also empty (i.e., |g (f a s) ≡ nothing|), but this apparently does not hold in general.
For heapsort, adding a finite element to a heap always makes the heap extractable, constituting a counterexample.
On the other hand, adding~|INF| to an empty heap does keep the heap empty by our definition, so producing an empty colist is not always wrong.
This suggests that we should do a case analysis on~|a| to determine whether to produce an empty or non-empty colist at Goal~4.
Let us call an element of~|A| \emph{flat} exactly when merging it into an empty state results in another empty state. 
There should be a decision procedure |flat?| that can be used to identify flat elements:
\begin{code}
flat? : (a : A) →  ({s : S} → g s ≡ nothing → g (f a s) ≡ nothing) ⊎ (GOAL(Set)(7))
\end{code}

\begin{code}
decon (fill a bs) | ⟨ eq(CXT(g s ≡ nothing)) ⟩ with flat? a
decon (fill a bs) | ⟨ eq ⟩ | inj₁  flat      = ⟨ (GOAL(g (f a s) ≡ nothing)(8)) ⟩
decon (fill a bs) | ⟨ eq ⟩ | inj₂  not-flat  = (GOAL(CoalgListF B g (f a s))(9))
\end{code}

|flat eq|

|flat-edge : B|

\begin{code}
let (b' , a') LETEQ piece (a , flat-edge) in b' ∷⟨ (GOAL'(g (f a s) ≡ just (b' , f a' s))) ⟩ fill a' bs
\end{code}

\[ \begin{tikzpicture}[x=12em,y=4em,baseline=(u.base)]
\node(x) [anchor=center] {|s|\vphantom{|f|}};
\node(x') [below=1 of x,anchor=center] {|s|\vphantom{|f|}};
\node(hx) [left=1 of x,anchor=center] {|f a s|};
\node(hx') [left=1 of x',anchor=center] {|f a' s|};
\draw[serif cm-to] (x) edge node[above]{consume~|a| with~|f|} (hx);
\draw[serif cm-to] (x') edge node[below]{consume~|a'| with~|f|} (hx');
\draw[serif cm-to] (x) edge[dashed] node(t)[right]{(produce |flat-edge| with~|g|)} (x ||- x'.north);
\draw[serif cm-to] (hx) edge node(u)[left]{produce~|b'| with~|g|} (hx ||- hx'.north);
%\node at ($(t)!0.5!(u)$) [anchor=center] {$\Leftarrow$};
\end{tikzpicture} \]

\begin{code}
jigsaw-condition :
  {a : A} {b : B} {s s' : S} →
  g s ≡ just (b , s') ⊎ (g s ≡ nothing × g (f a s) ≢ nothing × b ≡ flat-edge × s' ≡ s) →
  let (b' , a') LETEQ piece (a , b) in g (f a s) ≡ just (b' , f a' s')
\end{code}

\begin{figure}
\beforefigurecode
\begin{code}
module Jigsaw-General
  (f : A → S → S) (e : S) (g : S → Maybe (B × S))
  (piece : A × B → B × A)
  (flat-edge : B)
  (flat? : (a : A) →  ({s : S} → g s ≡ nothing → g (f a s) ≡ nothing) ⊎
                      ({s : S} → g (f a s) ≢ nothing))
  (nothing-from-e : g e ≡ nothing)
  (jigsaw-condition :
    {a : A} {b : B} {s s' : S} →
    g s ≡ just (b , s') ⊎ (g s ≡ nothing × g (f a s) ≢ nothing × b ≡ flat-edge × s' ≡ s) →
    let (b' , a') LETEQ piece (a , b) in g (f a s) ≡ just (b' , f a' s'))
  where

  fill : {s : S} (a : A) → CoalgList B g s → CoalgList B g (f a s)
  decon (fill a bs) with decon bs
  decon (fill a bs) | ⟨ eq ⟩ with flat? a 
  decon (fill a bs) | ⟨ eq ⟩ | inj₁ flat      = ⟨ flat eq ⟩
  decon (fill a bs) | ⟨ eq ⟩ | inj₂ not-flat  =
    let  (b' , a') LETEQ piece (a , flat-edge)
    in   b' ∷⟨ jigsaw-condition (inj₂ (eq , not-flat , refl , refl)) ⟩ fill a' bs
  decon (fill a bs) | b ∷⟨ eq ⟩ bs' =
    let  (b' , a') LETEQ piece (a , b)
    in   b' ∷⟨ jigsaw-condition (inj₁ eq) ⟩ fill a' bs'

  jigsaw : {s : S} → AlgList A f e s → CoalgList B g s
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