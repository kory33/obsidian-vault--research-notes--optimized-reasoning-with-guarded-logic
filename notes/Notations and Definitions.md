### MathJax macros

$$
\def\elems{{\operatorname{elems}}}
\def\Vars{{\mathrm{Vars}}}
\def\Consts{{\mathrm{Consts}}}
\def\GroundTerms{{\mathrm{GroundTerms}}}
\def\Terms{{\mathrm{{Terms}}}}
\def\Nulls{{\mathrm{Nulls}}}
\def\Predicates{{\mathrm{Predicates}}}
\def\Arity{{\operatorname{Arity}}}
\def\Formulae{{\mathrm{Formulae}}}
\def\Facts{{\operatorname{Facts}}}
\def\consts{{\mathrm{consts}}}
\def\chase{{\operatorname{chase}}}
$$

### General Notations

For a formal finite sequence $(X_1, \ldots, X_n)$ of same sorts, we abbriviate it as $\vec{X}$. The set $\set{\ X_1, \ldots, X_n\ }$ will then be denoted as $\elems(\vec{X})$. We write $\vec{X'} \leq \vec{X}$ to mean that $\vec{X'}$ is a subsequence of $\vec{X}$, and $X' \subseteq X$ to mean $\elems(\vec{X'}) \subseteq \elems(\vec{X})$.

### Logic Preliminaries

This section mainly pulls definitions from [Rewriting the Infinite Chase](https://krr-oxford.github.io/Guarded-saturation/files/p2537-benedikt-long.pdf), with minor modifications.

We assume an infinite collection $\Vars = \set{x, y, z, \ldots}$ of variables, the ordered set $\Nulls = \set{\ n_i \mid i \in \mathbb{N}\ }$ of *labelled nulls* and some given fixed (finite or infinite) set $\Consts = \set{c_1, c_2, \ldots}$ of constants.

Given a finite collection $\Predicates = \set{P_1, P_2, \ldots, P_N}$ of predicates with finite arities $\Arity(P_i)$ associated to each of them, we define:
 - _the set $\GroundTerms$ of ground terms_ as $\Vars \cup \Consts$
 - _the set $\Terms$ of terms_ as $\GroundTerms \cup \Nulls$
 - _an atom_ to be a formal expression $P(t_1, t_2, \ldots, t_{\Arity(P)})$ with $P \in \Predicates$, $t_i \in \Terms$ for each $1 \leq i \leq \Arity(P)$.
 - *the set $\Formulae$ of first-order formulas under the sigunature $(\Predicates, \Nulls, \Consts)$* to be a set of formal expressions inductively built up from atoms using unary connective $\neg$, binary connectives $\wedge, \vee, \rightarrow$ and quantifiers $\exists x.$ and $\forall x.$ (where $x \in \Vers$).

Semantics (interpretation, logical-consequence relation and truth) of formulae is defined using the standard terminology. We also follow standard conventions concerning variables being *bound* and *free*.

For brevity, we adopt the following notational conventions:
  - for a fact $P(t_1, \ldots, t_{\Arity(P)})$, we simply write it as $P(\vec{t})$ with an intention that $\vec{t} = (x_1, \ldots, x_n)$.
  - for a formula of a form $\exists x_1. \exists x_2. \ldots \exists x_n. \phi$, we simply writeit as $\exists \vec{x}. \phi$ with an intention that $\vec{x} = (x_1, \ldots, x_n)$.

For conjunctions $F = \bigwedge_{1 \leq i \leq n} F_i$ and $G = \bigwedge_{1 \leq j \leq m} G_j$ of formulae, we write $F \subseteq G$ when for each $1 \leq i \leq n$, $F_i$ appears in $G$. That is, for each $1 \leq i \leq n$, there exists $1 \leq j \leq m$ with $F_i = G_j$.

We now define subclasses of objects defined above:
  - an atomic formula $P(\vec{t})$ is *a fact* if $\vec{t}$ only contains ground terms
  - a fact $P(\vec{t})$ is *a base fact* if $\vec{t}$ only contains constants.
  - a subset $I \subseteq \Formulae$ is *an instance* if each formula is a fact.
  - an instance $I$ is *a base instance* if each fact in $I$ is a base fact.
  - a formula is *a rectified formula* if no variable is bound twice, and no variable occurs both bound and free. By a standard renaming argument, any first-order formula is equivalent to a rectified formula. Hence from now on we will assume formulae to be rectified.
  - a formula is closed when every occurence of variable is bound.
  - a closed formula is a *Tuple-Generating Dependency (or TGD)* if it is of the form $\forall \vec{x}. (\beta \rightarrow \exists \vec{y}. \eta)$ where $\beta$ and $\eta$ are conjunctions of atoms with $\eta$ nonempty. In such a formula, $\beta$ is referred to as the *body* and $\eta$ is referred to as the *head* of this TGD.
  - a TGD $\forall \vec{x}. (\beta \rightarrow \exists \vec{y}. \eta)$ is *a full TGD* if $\vec{y}$ is empty, i.e. it is of the form $\forall \vec{x}. \beta \rightarrow \eta$.
  - a TGD $\forall \vec{x}. (\beta \rightarrow \exists \vec{y}. \eta)$ is a *guarded-TGD (or GTGD)* if $\beta$ contains an atom $P(\vec{t})$ such that $\vec{t} \supseteq \vec{x}$.

A *substitution* is a function $\sigma: \Vars \rightarrow \Terms$ such that $\sigma(x) \neq x$ for finitely mane $x \in \Vars$. A substitution $\sigma: \Vars \rightarrow \Terms$ canonically extends to a function $\Formulae \rightarrow \Formulae$ that replaces each occurence of $x \in \Vars$ in a formula by $\sigma(x) \in \Terms$.

### Chase Trees and Chase Proofs

The chase tree.
