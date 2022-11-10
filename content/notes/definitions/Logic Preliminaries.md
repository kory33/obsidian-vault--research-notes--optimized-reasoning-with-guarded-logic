---
title: Logic Preliminaries
tag:
  - notes
  - definitions
---

> This note builds on [[General Notations]].

This note mainly pulls definitions from [Rewriting the Infinite Chase](https://krr-oxford.github.io/Guarded-saturation/files/p2537-benedikt-long.pdf), but with quite a lot of modifications.

We assume the countably infinite collection $\Vars = \set{x_1, x_2, x_3, \ldots}$ of variables, the ordered set $\Nulls = \set{\ n_i \mid i \in \mathbb{N}\ }$ of *labelled nulls* and some given fixed (at most countable) set $\Consts = \set{c_1, c_2, \ldots}$ of constants.

Given a finite collection $\Predicates = \set{P_1, P_2, \ldots, P_N}$ of predicate symbols with finite arities $\Arity(P_i) \in \mathbb{N}$ associated to each of them, we say that a tuple $(\Vars, \Nulls, \Consts, \Predicates, \set{\Arity(P_i)}_{1 \leq i \leq N})$, is a *first-order language*. For a first order language $\mathcal{L} = (\Vars_\mathcal{L}, \Nulls_\mathcal{L}, \Consts_\mathcal{L}, \Predicates_\mathcal{L}, \set{\Arity_\mathcal{L}(P_i)}_{1 \leq i \leq N})$, we define:
 - *the set $\Terms_\mathcal{L}$ of (non-null) terms* as $\Vars_\mathcal{L} \cup \Consts_\mathcal{L}$
 - *the set $\NullableTerms_\mathcal{L}$ of nullable terms* as $\Vars_\mathcal{L} \cup \Consts_\mathcal{L} \cup \Nulls_\mathcal{L}$
 - _the set $\FactualTerms_\mathcal{L}$ of factual terms_ as $\Nulls_\mathcal{L} \cup \Consts_\mathcal{L}$
 - _the set $\Atoms_\mathcal{L}$ of atomic formulae (resp. the set $\Facts_\mathcal{L}$ of facts)_ to be a set of formal expression $P(t_1, t_2, \ldots, t_{\Arity_\mathcal{L}(P)})$ with $P \in \Predicates_\mathcal{L}$, $t_i \in \Terms_\mathcal{L}$ (resp. $\FactualTerms_\mathcal{L}$) for each $1 \leq i \leq \Arity_\mathcal{L}(P)$
 - *the set $\Formulae_\mathcal{L}$ of (first-order) formulas under the sigunature $(\Predicates_\mathcal{L}, \Consts_\mathcal{L})$* to be a set of formal expressions inductively built up from $\Atoms_\mathcal{L}$ using unary connective $\neg$, binary connectives $\wedge, \vee, \rightarrow$ and quantifiers $\exists x.$ and $\forall x.$ (where $x \in \Vars_\mathcal{L}$)

For most of the following definitions, we will assume some fixed first-order language $\mathcal{L}$ and omit the subscript $_\mathcal{L}$ unless it becomes necessary to specify the language.

Semantics (interpretation, logical-consequence relation and truth) of formulae is defined using the standard terminology. We also follow standard conventions concerning variables being *bound* and *free*.

For brevity, we adopt the following notational conventions:
  - for a an atomic formula $P(t_1, \ldots, t_{\Arity(P)})$, we simply write it as $P(\vec{t})$ with an intention that $\vec{t} = (t_1, \ldots, t_{\Arity(P)})$.
  - for a formula of a form $\exists x_1. \exists x_2. \ldots \exists x_n. \phi$, we simply write it as $\exists \vec{x}. \phi$ with an intention that $\vec{x} = (x_1, \ldots, x_n)$.

For conjunctions $F = \bigwedge_{1 \leq i \leq n} F_i$ and $G = \bigwedge_{1 \leq j \leq m} G_j$ of formulae, we write $F \subseteq G$ when for each $1 \leq i \leq n$, $F_i$ appears in $G$. That is, for each $1 \leq i \leq n$, there exists $1 \leq j \leq m$ with $F_i = G_j$.

We now define subclasses of objects defined above:
  - a fact $P(\vec{t})$ is *a base fact* if $\vec{t}$ contains only constants (hence no nulls). We write $\BaseFacts$ for the set of base facts.
  - *an instance* is a finite set of facts. We write $\Instances$ for the set $\mathcal{P}_{< \omega}(\Facts)$.
  - an instance $I$ is *a base instance* if each fact in $I$ is a base fact.
  - a formula is *a rectified formula* if no variable is bound twice, and no variable occurs both bound and free. By a standard renaming argument, any first-order formula is equivalent to a rectified formula. Hence from now on we will assume all formulae to be rectified.
  - a formula is closed when every occurence of variable is bound.
  - a closed formula is a *Tuple-Generating Dependency (or TGD)* if it is of the form $\forall \vec{x}. (\beta \rightarrow \exists \vec{y}. \eta)$ where $\beta$ and $\eta$ are conjunctions of atoms with $\eta$ nonempty. In such a formula, $\beta$ is referred to as the *body* and $\eta$ is referred to as the *head* of this TGD.
  - a TGD $\forall \vec{x}. (\beta \rightarrow \exists \vec{y}. \eta)$ is *a full TGD* if $\vec{y}$ is empty, i.e. it is of the form $\forall \vec{x}. \beta \rightarrow \eta$.
  - a full TGD is *a Datalog rule* if its head contains exactly one atom. A finite set of Datalog rules is is called *a Datalog program*.
  - a TGD is in a head-normal form if it is either a *Datalog rule*, or each atom in the head contains at least one existentially quantified variable.
  - a TGD $\forall \vec{x}. (\beta \rightarrow \exists \vec{y}. \eta)$ is a *guarded-TGD (or GTGD)* if $\beta$ contains an atom $P(\vec{t})$ such that $\vec{t} \supseteq \vec{x}$.
  - a Conjunctive Query (CQ) is a formula of the form $\exists \vec{x}. \bigwedge_i A_i$ where each $A_i$ is an atomic formula.

We say that a Datalog program $\Sigma_\rew$ is a *Datalog rewriting* of a finite collection $\Sigma$ of GTDGs when for every base instance $I$ and a base fact $F$, $$I \wedge \Sigma \models F \Longleftrightarrow I \wedge \Sigma_\rew \models F.$$
A *factual substitution* is a partial function $\sigma: \Vars \rightharpoonup \FactualTerms$ with a finite domain. A factual substitution canonically extends to a partial function $\Atoms \rightharpoonup \Facts$ that is defined on atoms all of whose variables are in the domain of $\sigma$. We identity this extension of $\sigma$ with $\sigma$ by an abuse of notation. We write $\FactualSubstitutions = (\Vars \rightharpoonup \FactualTerms)_{< \omega}$ for the countable set of all factual substitutions.

We say that a factual substitution $\sigma$ *covers* a set $\vec{y}$ of variables when $\elems(\vec{y}) \subseteq \domain(\sigma)$, and that $\sigma$ *covers* an atom $A$ (resp. a vector of atoms $\vec{A}$) when $\sigma$ covers the set $\vars(A)$ (resp. $\vars(\vec{A})$) of variables in $A$ (resp. $\vec{A}$).

We say that a (potentially infinite) set $\mathcal{F}$ of facts *witnesses a closed conjunctive query $\exists \vec{x}. \bigwedge_{1 \leq i \leq n} A_i$* if there exists a factual substitution $\sigma$ covering $\vec{A}$ such that $$\set{\ \sigma(A_i) \mid 1 \leq i \leq n \ } \subseteq \mathcal{F}.$$