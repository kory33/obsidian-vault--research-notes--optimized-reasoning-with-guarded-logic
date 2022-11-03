> This note builds on [[General Notations]].

This note mainly pulls definitions from [Rewriting the Infinite Chase](https://krr-oxford.github.io/Guarded-saturation/files/p2537-benedikt-long.pdf), but with a few modifications.

We assume a countably infinite collection $\Vars = \set{x_1, x_2, x_3, \ldots}$ of variables, the ordered set $\Nulls = \set{\ n_i \mid i \in \mathbb{N}\ }$ of *labelled nulls* and some given fixed (at most countable) set $\Consts = \set{c_1, c_2, \ldots}$ of constants.

Given a finite collection $\Predicates = \set{P_1, P_2, \ldots, P_N}$ of predicates with finite arities $\Arity(P_i)$ associated to each of them (both of which we will not explicitly write from now on), we define:
 - *the set $\Terms$ of (non-null) terms* as $\Vars \cup \Consts$
 - *the set $\NullableTerms$ of nullable terms* as $\Vars \cup \Consts \cup \Nulls$
 - _the set $\FactualTerms$ of factual terms_ as $\Nulls \cup \Consts$
 - _the set $\Atoms$ of atomic formulae (resp. the set $\Facts$ of facts)_ to be a set of formal expression $P(t_1, t_2, \ldots, t_{\Arity(P)})$ with $P \in \Predicates$, $t_i \in \Terms$ (resp. $\FactualTerms$) for each $1 \leq i \leq \Arity(P)$
 - *the set $\Formulae$ of (first-order) formulas under the sigunature $(\Predicates, \Consts)$* to be a set of formal expressions inductively built up from $\Atoms$ using unary connective $\neg$, binary connectives $\wedge, \vee, \rightarrow$ and quantifiers $\exists x.$ and $\forall x.$ (where $x \in \Vars$)

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

A *factual substitution* is a partial function $\sigma: \Vars \rightharpoonup \FactualTerms$ with a finite domain. A factual substitution canonically extends to a partial function $\Atoms \rightharpoonup \Facts$ that is defined on atoms all of whose variables are in the domain of $\sigma$. We identity this extension of $\sigma$ with $\sigma$ by an abuse of notation. We write $\FactualSubstitutions = (\Vars \rightharpoonup \FactualTerms)_{< \omega}$ for the countable set of all factual substitutions.

We say that a factual substitution $\sigma$ *covers* a set $\vec{y}$ of variables when $\elems(\vec{y}) \subseteq \domain(\sigma)$, and that $\sigma$ *covers* an atom $A$ (resp. a vector of atoms $\vec{A}$) when $\sigma$ covers the set $\vars(A)$ (resp. $\vars(\vec{A})$) of variables in $A$ (resp. $\vec{A}$).

We say that a (potentially infinite) set $\mathcal{F}$ of facts *witnesses a closed conjunctive query $\exists \vec{x}. \bigwedge_{1 \leq i \leq n} A_i$* if there exists a factual substitution $\sigma$ covering $\vec{A}$ such that $$\set{\ \sigma(A_i) \mid 1 \leq i \leq n \ } \subseteq \mathcal{F}.$$