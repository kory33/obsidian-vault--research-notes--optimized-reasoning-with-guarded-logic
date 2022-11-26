---
title: Logic Preliminaries
tag:
  - notes
  - definitions
---

> This note builds on [[General Notations]].

This note mainly pulls definitions from [Rewriting the Infinite Chase](https://krr-oxford.github.io/Guarded-saturation/files/p2537-benedikt-long.pdf), but with quite a lot of modifications.

We assume the countably infinite collection $\Vars = \set{x_0, x_1, \ldots}$ of variables, the ordered set $\Nulls = \set{\ n_i \mid i \in \mathbb{N}\ }$ of *labelled nulls*, some given fixed (at most countable) set $\Consts = \set{c_0, c_1, \ldots}$ of constants. We also assume an infinite collection $\Predicates = \set{P_0, P_1, \ldots}$ of predicate symbols, such that there is an associated *arity-function* $\Arity: \Predicates \rightarrow \mathbb{N}$ such that the preimage $\Arity^{-1}[\set{n}]$ of $n \in \mathbb{N}$ is always infinite.

We say that a tuple $\mathcal{L} = (\Vars_\mathcal{L}, \Nulls_\mathcal{L}, \Consts_\mathcal{L}, \Predicates_\mathcal{L})$ where $\Vars_\mathcal{L} \subseteq \Vars$ and so on, is a *first-order language*. For a first order language $\mathcal{L} = (\Vars_\mathcal{L}, \Nulls_\mathcal{L}, \Consts_\mathcal{L}, \Predicates_\mathcal{L})$, we define:
 - *the set $\Terms_\mathcal{L}$ of (non-null) terms* as $\Vars_\mathcal{L} \cup \Consts_\mathcal{L}$
 - *the set $\NullableTerms_\mathcal{L}$ of nullable terms* as $\Vars_\mathcal{L} \cup \Consts_\mathcal{L} \cup \Nulls_\mathcal{L}$
 - _the set $\FactualTerms_\mathcal{L}$ of factual terms_ as $\Nulls_\mathcal{L} \cup \Consts_\mathcal{L}$
 - _the set $\Atoms_\mathcal{L}$ of atomic formulae (resp. the set $\Facts_\mathcal{L}$ of facts)_ to be a set of formal expression $P(t_1, t_2, \ldots, t_{\Arity(P)})$ with $P \in \Predicates_\mathcal{L}$, $t_i \in \Terms_\mathcal{L}$ (resp. $\FactualTerms_\mathcal{L}$) for each $1 \leq i \leq \Arity(P)$
 - *the set $\Formulae_\mathcal{L}$ of (first-order) formulas under the signature $(\Predicates_\mathcal{L}, \Consts_\mathcal{L})$* to be a set of formal expressions inductively built up from $\Atoms_\mathcal{L}$ using unary connective $\neg$, binary connectives $\wedge, \vee, \rightarrow$ and quantifiers $\exists x.$ and $\forall x.$ (where $x \in \Vars_\mathcal{L}$)

For most of the following definitions, we will assume some fixed first-order language $\mathcal{L}$ and omit the subscript $_\mathcal{L}$ unless it becomes necessary to specify the language. 

> **Notational remark**. By an abuse of notation, we may omit the subscript $_\mathcal{L}$ to denote the "unconstraint version" of the inductive construction. For example, by $\Atoms$ we may simply mean the set of formal expressions of the form $P(t_1, \ldots, t_{\Arity(P)})$ where $P \in \Predicates$ and $t_i \in \Terms = \Vars \cup \Consts$ for each $1 \leq i \leq \Arity(P)$.

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
  - a TGD $\forall \vec{x}. (\beta \rightarrow \exists \vec{y}. \eta)$ is a *guarded-TGD (or GTGD)* if $\beta$ contains an atom $P(\vec{t})$ such that $\vec{t} \supseteq \vec{x}$. We write $\GTGDFormulae_\mathcal{L}$ for the set of $\mathcal{L}$-formulae that are GTGDs.
  - a Conjunctive Query (CQ) is a formula of the form $\exists \vec{x}. \bigwedge_i A_i$ where each $A_i$ is an atomic formula.

We say that a Datalog program $\Sigma_\rew$ is a *Datalog rewriting* of a finite collection $\Sigma$ of GTGDs when for every base instance $I$ and a base fact $F$, $$I \wedge \Sigma \models F \Longleftrightarrow I \wedge \Sigma_\rew \models F.$$

## Notions of Substitutions

### Factual subtitutions

> **Definition**. A *factual substitution* is a partial function $\sigma: \Vars \rightharpoonup \FactualTerms$ with a finite domain.

A factual substitution canonically extends to a partial function $\Atoms \rightharpoonup \Facts$ that is defined on atoms all of whose variables are in the domain of $\sigma$. We identity this extension of $\sigma$ with $\sigma$ by an abuse of notation.

> **Definition**. We write $\FactualSubstitutions = (\Vars \rightharpoonup \FactualTerms)_{< \omega}$ for the countable set of all factual substitutions.

> **Definition**. We say that a factual substitution $\sigma$ *covers* a set $\vec{y}$ of variables when $\elems(\vec{y}) \subseteq \domain(\sigma)$, and say that $\sigma$ *exactly covers $\vec{y}$* if $\elems(\vec{y}) = \domain(\sigma)$.

> **Definition**. We say that a factual substitution $\sigma$ together with a (potentially infinite) set $\mathcal{F}$ of facts *witness a boolean conjunctive query $\exists \vec{x}. \bigwedge_{1 \leq i \leq n} A_i$* if $\sigma$ exactly covers $\vec{x}$ and $$\set{\ \sigma(A_i) \mid 1 \leq i \leq n \ } \subseteq \mathcal{F}.$$

### Consts translations

> **Definition**. A *consts translation* is a function $\sigma: \Consts \rightarrow \Consts$.

A consts translation $\sigma$ then canonically extends to a function $\tilde{\sigma}: \Facts \rightarrow \Facts$ that applies $\sigma$ to each constant appearing in a fact (without modifying nulls). Then $\tilde{\sigma}$ further extends to a function $\tilde{\tilde{\sigma}}: \Instance \rightarrow \Instance$ that applies $\tilde{\sigma}$ to each fact in an instance. By an abuse of notation we shall identify all of $\sigma, \tilde{\sigma}$ and $\tilde{\tilde{\sigma}}$.
