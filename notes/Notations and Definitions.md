### MathJax macros

$$
\def\elems{{\operatorname{elems}}}
\def\Vars{{\mathrm{Vars}}}
\def\Nulls{{\mathrm{Nulls}}}
\def\Consts{{\mathrm{Consts}}}
\def\Predicates{{\mathrm{Predicates}}}
\def\Arity{{\operatorname{Arity}}}
\def\FactualTerms{{\mathrm{FactualTerms}}}
\def\Terms{{\mathrm{{Terms}}}}
\def\Atoms{{\mathrm{Atoms}}}
\def\Facts{{\mathrm{Facts}}}
\def\Formulae{{\mathrm{Formulae}}}
\def\Instances{{\mathrm{Instances}}}
\def\consts{{\mathrm{consts}}}

\def\exlift{{\operatorname{Lift}_\exists}}
\def\Sat{{\operatorname{Sat}}}
$$

### General Notations

For a formal finite sequence $(X_1, \ldots, X_n)$ of same sorts, we abbriviate it as $\vec{X}$. The set $\set{\ X_1, \ldots, X_n\ }$ will then be denoted as $\elems(\vec{X})$. We write $\vec{X'} \triangleleft \vec{X}$ to mean that $\vec{X'}$ is a subsequence of $\vec{X}$, and $X' \subseteq X$ to mean $\elems(\vec{X'}) \subseteq \elems(\vec{X})$.

### Logic Preliminaries

This section mainly pulls definitions from [Rewriting the Infinite Chase](https://krr-oxford.github.io/Guarded-saturation/files/p2537-benedikt-long.pdf), but with a few modifications.

We assume an infinite collection $\Vars = \set{x_1, x_2, x_3, \ldots}$ of variables, the ordered set $\Nulls = \set{\ n_i \mid i \in \mathbb{N}\ }$ of *labelled nulls* and some given fixed (finite or infinite) set $\Consts = \set{c_1, c_2, \ldots}$ of constants.

Given a finite collection $\Predicates = \set{P_1, P_2, \ldots, P_N}$ of predicates with finite arities $\Arity(P_i)$ associated to each of them (both of which we will not explicitly write from now on), we define:
 - *the set $\Terms$ of (non-null) terms* as $\Vars \cup \Consts$
 - _the set $\FactualTerms$ of factual terms_ as $\Nulls \cup \Consts$
 - _the set $\Atoms$ of atomic formulae (resp. the set $\Facts$ of facts)_ to be a set of formal expression $P(t_1, t_2, \ldots, t_{\Arity(P)})$ with $P \in \Predicates$, $t_i \in \Terms$ (resp. $FactualTerms$) for each $1 \leq i \leq \Arity(P)$
 - *the set $\Formulae$ of (first-order) formulas under the sigunature $(\Predicates, \Consts)$* to be a set of formal expressions inductively built up from $\Atoms$ using unary connective $\neg$, binary connectives $\wedge, \vee, \rightarrow$ and quantifiers $\exists x.$ and $\forall x.$ (where $x \in \Vars$)

Semantics (interpretation, logical-consequence relation and truth) of formulae is defined using the standard terminology. We also follow standard conventions concerning variables being *bound* and *free*.

For brevity, we adopt the following notational conventions:
  - for a an atomic formula $P(t_1, \ldots, t_{\Arity(P)})$, we simply write it as $P(\vec{t})$ with an intention that $\vec{t} = (t_1, \ldots, t_{\Arity(P)})$.
  - for a formula of a form $\exists x_1. \exists x_2. \ldots \exists x_n. \phi$, we simply write it as $\exists \vec{x}. \phi$ with an intention that $\vec{x} = (x_1, \ldots, x_n)$.

For conjunctions $F = \bigwedge_{1 \leq i \leq n} F_i$ and $G = \bigwedge_{1 \leq j \leq m} G_j$ of formulae, we write $F \subseteq G$ when for each $1 \leq i \leq n$, $F_i$ appears in $G$. That is, for each $1 \leq i \leq n$, there exists $1 \leq j \leq m$ with $F_i = G_j$.

We now define subclasses of objects defined above:
  - a fact $P(\vec{t})$ is *a base fact* if $\vec{t}$ contains only constants (hence no nulls).
  - *an instance* is a finite set of facts. We write $\Instances$ for the set $\mathcal{P}_{fin}(\Facts)$.
  - an instance $I$ is *a base instance* if each fact in $I$ is a base fact.
  - a formula is *a rectified formula* if no variable is bound twice, and no variable occurs both bound and free. By a standard renaming argument, any first-order formula is equivalent to a rectified formula. Hence from now on we will assume all formulae to be rectified.
  - a formula is closed when every occurence of variable is bound.
  - a closed formula is a *Tuple-Generating Dependency (or TGD)* if it is of the form $\forall \vec{x}. (\beta \rightarrow \exists \vec{y}. \eta)$ where $\beta$ and $\eta$ are conjunctions of atoms with $\eta$ nonempty. In such a formula, $\beta$ is referred to as the *body* and $\eta$ is referred to as the *head* of this TGD.
  - a TGD $\forall \vec{x}. (\beta \rightarrow \exists \vec{y}. \eta)$ is *a full TGD* if $\vec{y}$ is empty, i.e. it is of the form $\forall \vec{x}. \beta \rightarrow \eta$.
  - a full TGD is *a Datalog rule* if its head contains exactly one atom. A finite set of Datalog rules is is called *a Datalog program*.
  - a TGD is in a head-normal form if it is either a *Datalog rule*, or each atom in the head contains at least one existentially quantified variable.
  - a TGD $\forall \vec{x}. (\beta \rightarrow \exists \vec{y}. \eta)$ is a *guarded-TGD (or GTGD)* if $\beta$ contains an atom $P(\vec{t})$ such that $\vec{t} \supseteq \vec{x}$.
  - a Conjunctive Query (CQ) is a formula of the form $\exists \vec{x}. \bigwedge_i A_i$ where each $A_i$ is an atomic formula.

A *finite substitution* is a function $\sigma: \Vars \rightarrow \Terms$ such that $\sigma(x) \neq x$ for finitely many $x \in \Vars$. A substitution $\sigma: \Vars \rightarrow \Terms$ canonically extends to a function $\Terms \rightarrow \Terms$ and then to a function $\Formulae \rightarrow \Formulae$ that replaces each occurence of $x \in \Vars$ in a term by $\sigma(x) \in \Terms$. We shall identify these extentions with the subsitution by an abuse of notation.

A *factual substitution* is a function $\sigma: \Vars \rightarrow \FactualTerms$. A factual substitution canonically extends to a function $\Atoms \rightarrow \Facts$. Again, we shall identify this extension with the factual substitution.

We say that a (potentially infinite) set $\mathcal{F}$ of facts *witnesses a closed conjunctive query $\exists \vec{x}. \bigwedge_{1 \leq i \leq N} A_i$* if there exists a ground substitution $\sigma$ such that $$\set{\ \sigma(A_i) \mid 1 \leq i \leq N \ } \subseteq \mathcal{F}.$$

### Rewriting, Existential Lifting and Saturation

Given a set $\Sigma$ of TGDs, a Datalog program $\Sigma_{\text{rew}}$ is *a rewriting of $\Sigma$* if for every base instance $I$, $\Sigma$ and $\Sigma_{\text{rew}}$ generate the same set of consequences, i.e. for every __base fact__ $F$, $$I \wedge \Sigma \models F \Longleftrightarrow I \wedge \Sigma_{\text{rew}} \models F.$$
Given a fact $F(\vec{f})$, the *existential lifting $\elift(F(\vec{f}))$ of $F(\vec{f})$* is defined as the formula $$\exlift(F(\vec{f})) := \exists \vec{\nu}. F(\vec{f}[\ \vec{n} \leftarrow \vec{\nu}\ ])$$
where
 - $\vec{\nu}$ are variables corresponding to nulls in $\vec{f}$,
 - $\vec{f}[\ \vec{n} \leftarrow \vec{\nu}\ ]$ is $\vec{f}$ with nulls replaced by their corresponding variables in $\nu$. 

The *existential lifting $\exlift(I)$ of an instance $I$* is a set $\set{\ \exlift(F) \mid F \in I\ }$ of formulae.

Given a set $\Sigma$ of TGDs and an instance $I$, the *saturation $\Sat_\Sigma(I)$ of $I$ under $\Sigma$* is the instance defined by $$\Sat_\Sigma(I) := I \cup \set{\ F \in Facts \mid \Sigma \wedge \exlift(I) \models F\ }.$$

### Canonically Completed Chase

We shall define a tree-like structure that "stems from the "

