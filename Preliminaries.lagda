\documentclass[a4paper,UKenglish]{lipics-v2016}

%%%%%%%%%%%%%%%%% Preamble %%%%%%%%%%%%%%%%%%%%%%%

\usepackage{microtype} %if unwanted, comment out or use option "draft"
\bibliographystyle{plainurl} % the recommended bibstyle

%% Fix Margins 
%\usepackage[margin=1in]{geometry}

\usepackage{listings}
\usepackage{amsfonts}
\usepackage{xcolor}
\usepackage{graphicx}

% Equations
\usepackage{amsmath}

% Fonts
\usepackage{amssymb}
\usepackage{bbm}
%\usepackage[greek,english]{babel}
\usepackage{textgreek}
\usepackage{stmaryrd}
\usepackage{dsfont}

%% This handles the translation of unicode to latex:
%\usepackage{ucs}
%\usepackage[utf8x]{inputenc}
\usepackage{autofe}

%% Some convenient shorthands
\newcommand{\AD}{\AgdaDatatype}
\newcommand{\AF}{\AgdaFunction}
\newcommand{\AB}{\AgdaBound}
\newcommand{\AIC}{\AgdaInductiveConstructor}
\newcommand{\AM}{\AgdaModule}
\newcommand{\AP}{\AgdaPrimitive}
\newcommand{\AS}{\AgdaString}
\newcommand{\AR}{\AgdaRecord}
\newcommand{\AK}{\AgdaKeyword}
\newcommand{\AO}{\AgdaOperator}
\newcommand{\AC}{\AgdaComment}
\newcommand{\AN}{\AgdaNumber}
\newcommand{\ARF}{\AgdaField}
% Better use this one!

\usepackage{agda}
%include agda.fmt

\usepackage{bussproofs}

%% Lambda Calculus (should be a .sty at some point) 
\definecolor{typeColour}              {HTML}{0000CD}
\definecolor{judgementColour}         {HTML}{008B00}

\newcommand{\atype}[1]{\textcolor{typeColour}{#1}}

\newcommand{\ofty}[2]{{#1}{:}{#2}}
%\newcommand{\ofty}[2]{{#1}\colon\kern-.15em{#2}}
\newcommand{\bigofty}[2]{{#1} \textcolor{judgementColour}{\;:\;} { \atype{#2} }}
\newcommand{\lam}[3]{\lambda(\ofty{#1}{ \atype{#2} }).{#3}}
\newcommand{\app}[2]{{#1}\circ{#2}}
\newcommand{\bred}{\;\Rightarrow_{\beta}\;}
\newcommand{\subst}[2]{ [{#1} := {#2}] }

\newcommand{\seq}[3]{{#1} \textcolor{judgementColour}{\;\vdash\;} \bigofty{#2}{#3} }

\newcommand{\oseq}[2]{{#1} \textcolor{judgementColour}{\;\vdash\;} {#2}}

\newcommand{\imp}[2]{{#1} \rightarrow {#2}}

\newcommand{\impElim}{$E^{\rightarrow}$}


%% Some characters that are not automatically defined
%% (you figure out by the latex compilation errors you get),
%% and you need to define:
%
%\DeclareUnicodeCharacter{8988}{\ensuremath{\ulcorner}}
%\DeclareUnicodeCharacter{8989}{\ensuremath{\urcorner}}
%\DeclareUnicodeCharacter{8803}{\ensuremath{\overline{\equiv}}}
\DeclareUnicodeCharacter{8799}{\ensuremath{\stackrel{{!!}}{=}}}
\DeclareUnicodeCharacter{8759}{\ensuremath{\colon\colon}}
\DeclareUnicodeCharacter{7477}{\ensuremath{^{I}}}
\DeclareUnicodeCharacter{7472}{\ensuremath{^{D}}}
\DeclareUnicodeCharacter{7580}{\ensuremath{^{C}}}
\DeclareUnicodeCharacter{7488}{\ensuremath{^{T}}}
\DeclareUnicodeCharacter{7480}{\ensuremath{^{L}}}
\DeclareUnicodeCharacter{7486}{\ensuremath{^{P}}}
\DeclareUnicodeCharacter{7484}{\ensuremath{^{O}}}
\DeclareUnicodeCharacter{7584}{\ensuremath{^{F}}}
\DeclareUnicodeCharacter{7468}{\ensuremath{^{A}}}
\DeclareUnicodeCharacter{2208}{\ensuremath{\in}}
\DeclareUnicodeCharacter{8346}{\ensuremath{_{p}}}
%% Add more as you need them (shouldn’t happen often). 

%% Hyper ref for \url support
\usepackage{hyperref}

%%%%%%%%%%%%%%%%%%% Paper %%%%%%%%%%%%%%%%%%%%%%%%%%


\title{Programming Language Semantics}
\author[0]{Gavin Mendel-Gleason} 
\affil[0]{Trinity College Dublin\\
  \texttt{mendelgg@scss.tcd.ie}}

\Copyright{Gavin Mendel-Gleason}

\subjclass{Program semantics}
\keywords{operational semantics, type theory}
\begin{document}

\maketitle 

\begin{abstract}

This paper comprises a set of notes for a short course on programming
language semantics using Agda \cite{norell2009dependently}. We cover
the basics of operational and denotational semantics, with some
example proofs and proof exercises.

Most other proof assistants / programming languages would work as a
replacement, and the diligent student should be able to translate them
into their language of choice with little difficulty, aside from some
subtleties with coinduction in a very limited number of proofs.

\end{abstract}

\section{Introduction}

Programming language semantics is the study of the meaning of
programming languages. A programming language can be thought of as
some syntactic means of describing what computation we would like to
perform, coupled with a mechanism for performing the computation
according to what this language describes.

We are going to take a quick tour of programming language semantics,
making use of the Agda proof assistant as a method of both
implementing, and proving properties of programming languages.

The advantages in clarity of using a formal proof assistant which is
itself a programming language as the approach to describing semantics
are many. It's often much clearer what precisely is being described in
language semantics when we can actually see the datastructures, proofs
and evaluation itself described in a well structured metalanguage. We
can steal the computation of our host system to clarify meaning as
well as give succinct descriptions of what precisely we are trying to
prove by means of {\em types}.

Prior familiarity with type theory is not required to understand this
course, though it would be useful if the student is somewhat fluent
with both functional programming in a language such as haskell, ML or
similar, as well as some familiarity with imperative programming
paradigms.

Type theory is a discipline in mathematics which gives a formal
approach to the statement of conjectures and evidence for their
satisfaction. It is also, however, possible using something known as
the Curry-Howard correspondence, to view the evidence of satisfaction,
or proofs, as a functional programming language. This is exploited to
great effect in so-called ‘Dependently typed languages’ such as Agda.

We will see how Agda can be used to describe programming language
semantics using “Dependent types” for programming languages which we
implement in agda.

If all of this is clear as mud: fear not. The detail may in fact
dispel the devil.

\section{Preliminaries}

Instead of thinking of type theory through a very general mathematical
lens, we’re going to take a more prosaic approach.  We are

We’ll start from the ground up, building some basic machinery
ourselves in order to understand how it works. Later we will use the
analogous machinery from the Agda standard library.

We will start our exploration by defining a number of {\em inductive
types}. Inductive types are the primary manner in which we describe
our data structures for our semantics. They will also prove useful for
defining properties and relations about the terms in the programming
languages we will define.

Inductive types come equiped automatically with mechanisms to
introduce elements of them, known as {\em constructors} and ways of
eliminating them, using pattern matching in a manner which should be
familiar users of ML and Haskell.

The simplest inductive type is the empty type, which we call "bottom" or \AD{⊥}. 

\AgdaHide{
\begin{code}
record Basic : Set where
\end{code}
}

\begin{code}

  data ⊥ : Set where

  explosion : ∀ {A : Set} → ⊥ → A
  explosion ()

  ¬_ : ∀ (A : Set) → Set
  ¬ A = A → ⊥
  
\end{code} 

This type has very little to say. You can't produce one so it has no
constructors, and if you find one, you can't pattern match on it
because it could not have been introduced in the first place.

We can see how this is used with our term \AF{explosion} which is the
proof of the {\em principle of explosion}. First, the brackets, \{ \}
around the \AS{A} say that the argument is {\em implicit} and we are
asking Agda to try and infer it from context. This means that the
first argument we pattern match on is the terms of type
\AD{⊥}. However, since there are none to match, we don't even have to
finish our description of what to do if we find an occurence and so
need not find a way to produce an element of the type \AD{A}. From
false premises, anything follows.

In addition we can describe a kind of negation with \AD{¬\_} which
allows us to say that our premise can not hold, because otherwise we
would be able to produce a datatype with no elements. This will prove
a powerful, if somewhat non-intuitive way of describe that certain
properties do not hold.

The next simplest type is the type called {\em top} or \AD{⊤}. Sometimes this
type is called {\em one} (and the type \AD{⊥} is called {\em zero}) since
it only has the one constructor: \AIC{tt}.

\begin{code}

  data ⊤ : Set where
    tt : ⊤

\end{code}

Next we see the more familar type of booleans. The boolean type has
two constructors, \AIC{true} and \AIC{false}.

\begin{code}
  data Bool : Set where
    true : Bool
    false : Bool

  not : Bool → Bool
  not true = false
  not false = true

  _and_ : Bool → Bool → Bool
  true and true = true
  true and false = false
  false and b = false

  _or_ : Bool → Bool → Bool
  true or b = true
  false or true = true
  false or false = false

  if_then_else_ : ∀ {C : Set} → Bool → C → C → C
  if true then x else y = x
  if false then x else y = y

\end{code}

With the bool type defined, we can define the \AF{not} function, which
maps booleans to booleans, but flips the constructor.

Similarly we can define the usual \AF{\_and\_} and \AF{\_or\_} which allow
us to combine booleans in the usual way. Here the underscores tell
Agda that we mean for the function to be infix, so its first argument
is on the left, and its second is on the right.

However, we can also describe mixfix functions in Agda, as we see with
the \AF{if\_then\_else\_} function, which takes a boolean as its first
argument, and then takes two branches of type \AD{C} which the boolean
is used to select from. We can then recover the quite familiar form of
conditional branching as a function.

For a more in-depth description of the Agda programming language of
dependent types and its use as a proof-assistant, see Ulf Norell's
work {\em Dependently Typed Programming in
Agda}\cite{norell2009dependently} and Aaron Stump's {\em Verified
Functional Programming in Agda}\cite{Stump:2016:VFP:2841316}. We will
press on hoping that the reader can pick things up as we go along,
and, if not, looks to these additional resources in the event of
confusion.

\section{Operational Semantics}

Now that we've seen some basic uses of inductive types and functions
which manipulate them, we are ready to do some heavier lifting in the
service of programming language semantics.

Operational semantics is an approach to semantics which looks at how,
operationally, our programming terms {\em compute}. We'll get into the
nitty-gritty of evaluation, and learn how to state geeneral properties
of terms by seeing how evaluation progresses.

\begin{code}

module OperationalSemantics where
  open import Data.Nat

  data Exp : Set where
    num : ℕ → Exp
    _⊕_ : Exp → Exp → Exp
     
\end{code} 

We define a new {\em module} which we name
\AM{OperationalSemantics}. In Agda, a module is essentially a record
that allows us to define parameters, control our namespace and produce
a collection of associated terms which refer to eachother. In this
case we have a very simple module with no parameters. Directly below
the introduction of our module, and within its scope, we import
another module, \AM{Data.Nat} which contains the definitions for the
natural numbers, and various functions to manipulate them and facts
about them.

We can then define the syntax of our first language: \AD{Exp}. This
language is composed of numbers, and addition.  The syntax for
introducting a number uses the constructor \AIC{num} on a natural
number, the definition of which we've imported from \AM{Data.Nat}. We
can then add two expressions using the infix constructor \AIC{\_⊗\_}.

So what does an expression look like? The expression \AF{twelve} shows
how to write the addition of 3 numbers in our syntax.

\begin{code}

  twelve : Exp
  twelve = num 3 ⊕ (num 4 ⊕ num 5)
  
\end{code}

Our syntax is, however, merely a data-structure. It doesn't {\em do}
anything. We must add {\em dynamics} to our syntax in order to get
something worthy of being called a language.

We can do this by defining what it would mean to {\em evaluate} an
expression. We will do this by defining an {\em evaluation relation}.

\subsection{Big-Step Operational Semantics}

The first evaluation relation we will define, is something called a
{\em big-step evaluation relation}. It's called a big-step relation
because we define a relation between a term in our syntax, with the
final stage of evaluation is when something has reached a {\em
value}. In this case our values are numbers.

This provides a contrast with {\em small-step evaluation relations}
that instead tell you what the next step of a computation is. We will
look at small-step evaluation relations later, and then explore how
they relate.

\begin{minipage}{\linewidth}
\begin{code}

  infix 10 _⇓_ 
  data _⇓_ : Exp → ℕ → Set where
     n⇓n : ∀ {n} →
    
        ------------------
        num n ⇓ n
      
     E⊕E : ∀ {E₁ E₂ n₁ n₂} →
  
        E₁ ⇓ n₁  →  E₂ ⇓ n₂ →
        ------------------------------
          E₁ ⊕ E₂ ⇓ (n₁ + n₂)
  
\end{code} 
\end{minipage}

We introduce a new, infix, inductive type which we name \AD{\_⇓\_}. We
will call this a relation, because it has two parameters, an
expression, drawn from \AD{Exp} and a natural number drawn from
\AD{ℕ}.

All other types we've seen were defined to be themself of type
\AR{Set} directly. We can think of this as a family of types, with
each member of the family drawn by chosing elements of \AD{Exp} and
\AD{ℕ}, or as is natural for our current problem, as a {\em relation}
between \AD{Exp} and \AD{ℕ}.

Our relation has two constructors. The first is called \AIC{n⇓n}. It
basically says, that the big step evaluation relation relates an
expression formed of a natural number, to that same natural number. In
other words, when you evaluate a natural number, nothing happens.

We use a number of dashes, \AC{----} to simulate the horizontal bar
sometimes used in proofs, to separate our premises, from our conclusions.
In our first case, we have no premises (aside from the
uninteresting implicit \AB{n}). 

The second constructor is \AIC{E⊕E}. We can read this as stating that,
given we know the number to which two expressions \AB{E₁} and \AB{E₂}
evaluate, we can then determine that the expressions conjoined with
\AIC{\_⊕\_} will evaluate to the sum of the numbers to which each
expression evaluates, respectively.

\AgdaHide{
\begin{code}
  open import Data.Product
\end{code}
} 

\begin{minipage}{\linewidth}
\begin{code}

  evalBig : ∀ E → Σ[ n ∈ ℕ ] E ⇓ n
  evalBig (num x) = x , n⇓n
  evalBig (e ⊕ e₁) with evalBig e | evalBig e₁
  evalBig (e ⊕ e₁) | n , proof_n | m , proof_m = n + m , E⊕E proof_n proof_m

\end{code}
\end{minipage}

With this bigstep evaluation relation in hand, we can write an
evaluation function, \AF{evalBig}, which demonstrates that given any
expression in our syntax defined above, we can obtain a natural number
which relates the expression to its final evaluated form.

In Agda, we do this using the \AR{Σ} record. This is a pair
datastructure, comprising an element, and a proof of the type
\AB{E}\;\AD{⇓}\;\AB{n} which depends on both \AB{n} and \AB{E}. In this
case the element is some natural number \AD{ℕ} and the proof we must
construct is the full demonstration that \AB{E} evaluates to that
number under the big step evaluation relations.

In English we might read the type of \AF{evalBig} as stating that:

\begin{quotation}
``Given any expression, \AF{evalBig} will give us the number this
expression evaluates to, and a proof that this is a value which is
related by the big-step evaluation relation.''
\end{quotation}

So how does \AF{evalBig} work? It is essentially a simple proof by
induction on the structure of the syntax. With the syntax of our
language we have two cases. If we are the base case, namely
(\AIC{num}\;\AB{x}) we can use the fact that numbers evaluate to
themselves. This expression has no sub-expressions, and so we are
done, which is what makes it a base case.

If we are a sum of two expressions, combined with the \AIC{\_⊕\_}
constructor, we first evaluate each sub expression independently, and
then sum their values, using the \AIC{E⊕E} constructor to combine the
proofs obtained in both branches to produce the {\em next step} of the
proof.

With \AF{evalBig} in hand, we can look back at \AF{twelve} and see
the effect of evaluating this expression.

\begin{minipage}{\linewidth}
\begin{code}

  example⇓ : num 3 ⊕ (num 4 ⊕ num 5) ⇓ 12
  example⇓ = proj₂ (evalBig (num 3 ⊕ (num 4 ⊕ num 5)))

\end{code}
\end{minipage}

We apply \AF{evalBig} to our expression, and then use \ARF{proj₂} to
project out the {\em proof} from our pair of the number \AN{12} and
the proof which it is coupled with.

This example provides a sort of template for the way in which we can
build up operational semantics using big-step evaluation. Using this
general approach as a guide, we can look at more interesting
languages, and ask more sophisticated questions and get proofs about
our semantics.

However, for now we will continue on with this simple language, and
look at another approach to operational semantics.

\subsection{Small-step operational semantics}

In our previous example we demonstrated our reduction relation by
relating expressions to the values which they must evaluate to. There
is another option, namely, that we describe our reduction in terms of
{\em the next step}.

We can define a new type, \AD{\_⟶\_}, which relates two expressions
when the expression on the left can transition to the expression on
the right in {\em one step}.

\begin{minipage}{\linewidth}
\begin{code}

  infix 8 _⟶_
  data _⟶_ : Exp → Exp → Set where
    +⟶ : ∀ {n m} →
  
          -----------------------------
          num n ⊕ num m ⟶ num (n + m)

    ⊕₁⟶ : ∀ {E₁ E₁' E₂} →

          E₁ ⟶ E₁' → 
          ---------------------
          E₁ ⊕ E₂ ⟶ E₁' ⊕ E₂

    ⊕₂⟶ : ∀ {n E₂ E₂'} →

          E₂ ⟶ E₂' →  
          --------------------------
          num n ⊕ E₂ ⟶ num n ⊕ E₂'


\end{code}
\end{minipage}

This time we have three rules with one base case and a left and right
rule. The base case, \AIC{+⟶} takes two values combined with
\AIC{\_⊕\_} and evaluates to a value by summing the two values.

The left rule, \AIC{⊕₁⟶}, relates an expression with a sum in which
the left-hand summand can be further related by a small step, but
whose right-hand summand remains unchanged.

The right rule, \AIC{⊕₂⟶}, relates an expression with a sum in which
the left-hand is already fully evaluated to a number, but whose
right-hand can still be related by a small step.

To get a feel for whats going on, we can look at how we can relate
expressions concretely using this relation.


\begin{minipage}{\linewidth}
\begin{code}

  example⟶₁ : (num 3 ⊕ num 7) ⊕ (num 8 ⊕ num 1) ⟶ num 10 ⊕ (num 8 ⊕ num 1)
  example⟶₁ = ⊕₁⟶ +⟶ 
  example⟶₂ : (num 10) ⊕ (num 8 ⊕ num 1) ⟶ num 10 ⊕ num 9
  example⟶₂ = ⊕₂⟶ +⟶

\end{code}
\end{minipage} 

In \AF{example⟶₁} the left hand side has summed exactly one
pair of numbers. This is done by descending into the left branch and
then summing the pair of summands.

In \AF{example⟶₂} we have already reduced the left-hand side to a
number, we can then use the \AIC{⊕₂⟶} to decend into the right branch
where we find a pair of numbers which can be summed.

The reader may have noticed that these rules are written very
carefully such that there is no choice in the application of
rules. You have to evaluate all left expressions first, before one is
allowed to proceed with the right branch.

This choice is not necessary, but describes a {\em deterministic}
relation. Instead of this we could choose an alternative approach
which allows a choice of summand in which to descend.

\begin{minipage}{\linewidth}
\begin{code}

  infix 8 _⟶ch_
  data _⟶ch_ : Exp → Exp → Set where
    +⟶ch : ∀ {n m} →
  
          -------------------------------
          num n ⊕ num m ⟶ch num (n + m)

    ⊕₁⟶ch : ∀ {E₁ E₁' E₂} →

          E₁ ⟶ch E₁' → 
          ----------------------
          E₁ ⊕ E₂ ⟶ch E₁' ⊕ E₂

    ⊕₂⟶ch : ∀ {E₁ E₂ E₂'} →

          E₂ ⟶ch E₂' →  
          ----------------------
          E₁ ⊕ E₂ ⟶ch E₁ ⊕ E₂'

\end{code}
\end{minipage}

We have a new relation, \AD{\_⟶ch\_}, where the {\em ch} is short for
'choice'. Here we have the same approach to taking two summands which
are themselves values and combining it to a single value. However for
the left and right rules, we are not constrained in which branch we
choose. We can choose to make our step in either the right branch or
the left branch.

\begin{minipage}{\linewidth}
\begin{code}

  example⟶ch₁ : (num 3 ⊕ num 7) ⊕ (num 8 ⊕ num 1) ⟶ch num 10 ⊕ (num 8 ⊕ num 1)
  example⟶ch₁ = ⊕₁⟶ch +⟶ch
  example⟶ch₂ : (num 3 ⊕ num 7) ⊕ (num 8 ⊕ num 1) ⟶ch (num 3 ⊕ num 7) ⊕ num 9
  example⟶ch₂ = ⊕₂⟶ch +⟶ch

\end{code} 
\end{minipage}

We can now see two different examples where we make a choice of branch
in which to step. In \AF{example⟶ch₁} we chose the left branch for
evaluation, summing \AN{3} and \AN{7} and producing \AN{10}. In
\AF{example⟶ch₂} we take the right branch, summing \AN{8} and \AN{1}
to produce \AN{9}.

Now that we have defined these two different approaches, we might ask,
are we performing the same evaluation?

\begin{minipage}{\linewidth}
\begin{code}

  ⟶⇒⟶ch : ∀ {E₁ E₂} → (E₁ ⟶ E₂) → (E₁ ⟶ch E₂)
  ⟶⇒⟶ch +⟶ = +⟶ch
  ⟶⇒⟶ch (⊕₁⟶ d) = ⊕₁⟶ch (⟶⇒⟶ch d)
  ⟶⇒⟶ch (⊕₂⟶ d) = ⊕₂⟶ch (⟶⇒⟶ch d)

\end{code}
\end{minipage}

We can see from the theorem \AF{⟶⇒⟶ch} that we can always mimic the
deterministic small step evaluation relation \AF{\_⟶\_} with the
\AF{\_⟶ch\_} by simply always choosing the semetric proof rule.

However, the reverse theorem which transforms a choice small step to
the deterministic one is not true. To prove this, we make use of Agda's
\AM{Data.Empty} and the \AM{Relation.Nullary} libraries, rather than
our own negation which we described in the introduction.

\begin{minipage}{\linewidth}
\begin{code}

  open import Data.Empty
  open import Relation.Nullary

  ¬⟶ch⇒⟶ : ¬ (∀ E₁ E₂ → (E₁ ⟶ch E₂) → (E₁ ⟶ E₂))
  ¬⟶ch⇒⟶ f with f ((num 0 ⊕ num 0) ⊕ (num 0 ⊕ num 0)) ((num 0 ⊕ num 0) ⊕ num 0)
                        (⊕₂⟶ch +⟶ch)
  ¬⟶ch⇒⟶ f | ()

\end{code}
\end{minipage}

To prove that we can not always perform the same small step reduction
we need merely to find a single example for which does not hold.
 
Since \AD{¬\_} is essentially short hand for a function which maps from
a type to the empty type, our first argument, \AF{f} has the type of
the theorem

\begin{quote}
  \AO{∀}\AB{E₁}\AB{E₂} \AO{→} (\AB{E₁} \AD{⟶ch} \AB{E₂}) \AO{→} (\AB{E₁} \AD{⟶} \AB{E₂})
\end{quote}

... which we know can not be true. 

With our proof in hand, we can apply it to a patently impossible
reduction. Agda cleverly detects that we have no cases in which this
can hold and we are able to eliminate the possibility of our argument,
which eliminates the need to supply an impossible proof of \AD{⊥}. 

We have claimed earlier that our small step evaluation realtion is
deterministic, but we have not yet proved it. In order to prove
determinism, it is convenient first to have a notion of
equivalence. In Agda we can do this by means of a propositional
equality type \AD{\_≡ₚ\_}. We will define our own here in order to get
a flavour. Later we will use Agda's libraries to handle this machinery
for us.

\begin{minipage}{\linewidth}
\begin{code}

  infix 4 _≡ₚ_
  data _≡ₚ_ {A : Set} (x : A) : A → Set where
    instance reflₚ : x ≡ₚ x

\end{code}
\end{minipage}

The equality type can be described as follows. Given any type and a
value of that type, we can show that the value is equivalent to
itself, using the \AIC{reflₚ} constructor. This might seem quite
useless, as we can only show things are equal to themselves! However,
it is more flexible than it first appears, because Agda is able to
perform computations. So in order to show two things are equal, we
will be able to make the host system perform some computation and we
can build up non-trivial equivalences in this way.

Now that we have the basic idea of equivalence, we can switch to
Agda's built in propositional equality \AD{\_≡\_} and its single
constructor \AIC{refl}.

\begin{minipage}{\linewidth}
\begin{code}

  open import Relation.Binary.PropositionalEquality
  
  ⟶deterministic : ∀ {E E₁ E₂} → E ⟶ E₁ → E ⟶ E₂ → E₁ ≡ E₂
  ⟶deterministic +⟶ +⟶ = refl
  ⟶deterministic +⟶ (⊕₁⟶ ())
  ⟶deterministic +⟶ (⊕₂⟶ ())
  ⟶deterministic (⊕₁⟶ ()) +⟶
  ⟶deterministic (⊕₁⟶ p) (⊕₁⟶ q) = cong₂ _⊕_ (⟶deterministic p q) refl
  ⟶deterministic (⊕₁⟶ ()) (⊕₂⟶ q)
  ⟶deterministic (⊕₂⟶ ()) +⟶
  ⟶deterministic (⊕₂⟶ p) (⊕₁⟶ ())
  ⟶deterministic (⊕₂⟶ p) (⊕₂⟶ q) = cong₂ _⊕_ refl ((⟶deterministic p q))

\end{code}
\end{minipage} 

That our small step evalution relation is deterministic is described
by the type of \AF{⟶deterministic}. The theorem we are trying to
prove, is that given any term \AB{E} in our language, and a proof that
this is related by a single step to a term \AB{E₁}, then if it is also
related by a single step to some other term \AB{E₂} then \AB{E₁} and
\AB{E₂} must actually be the same term.

The proof of the theorem proceeds by induction on the proof of both
reduction relations using a simultaneous case match. The base case of
both is trivial, giving us that the sum of the numbers \AB{n} and
\AB{m} which are implicit variables of \AIC{+⟶} are equal to
themselves which is easily proved with \AIC{refl}. Though we can not
see these numbers in the proof as written here, replacing refl with a
{\em hole} by compiling Agda with a '?' will allow you to see the
implicit variables in the context.

Six more of the cases are eliminated by Agda automatically and can be
replaced with a vacuous match. As an example, in the first case in
which we have a vacuous match, the argument to \AIC{⊕₁⟶} would have to
have type: \AIC{num} \AN{n} \AD{⟶} \AB{E₁'}. Case analysis on this
yields no ways in which to form this type as \AIC{num} \AN{n} can not
be the left-hand side of any reduction.

as they require two different
constructors to be equivalent. Since inductive datatypes assume that
constructors are disjoint by construction, Agda can safely eliminate
cases in which two constructors actually being the same.

This leaves us with only

\begin{minipage}{\linewidth}
\begin{code}

\end{code}
\end{minipage} 

\bibliography{export.bib}

\end{document}

