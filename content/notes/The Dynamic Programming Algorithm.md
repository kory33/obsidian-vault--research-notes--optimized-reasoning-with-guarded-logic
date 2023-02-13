---
title: The Dynamic Programming Algorithm
tags:
  - notes
---

## Preliminaries

We begin with preliminary notions of certain properties of queries, notions related to hypergraphs and hypergraphs asccoated with queries.

> **Definition**. Let $\Sigma$ be a finite set of GTGDs. A boolean conjunctive query $Q = \exists \vec{z}. \bigwedge_{j \in J} A_j(\vec{u}_j)$ is said to be *fully $\Sigma$-existential* if
>   - $\consts(Q) \subseteq \consts(\Sigma)$, and
>   - for each $j \in J$, $\vars(\vec{u}_j) \neq \emptyset$.

> **Definition**. Let $\mathcal{H} = (\mathcal{V}_\mathcal{H}, \mathcal{E}_\mathcal{H})$ be a hypergraph.
> 
> For a set $V \subseteq \mathcal{V}_\mathcal{H}$ of vertices, we define
>   - the *strict $\mathcal{H}$-neighbourhood $\mathrm{nbhd}_\mathcal{H}(V)$ of $V$* as the set $$\mathrm{nbhd}_\mathcal{H}(V) = \set{\ v \in \mathcal{V}_\mathcal{H} \mid \exists E \in \mathcal{E}_\mathcal{H}. v \in E \ } \setminus V$$

> **Definition**. Let $Q = \exists \vec{z}. \bigwedge_{j \in J} A_j(\vec{u}_j)$ be a boolean conjunctive query.
> 
> The *query-structure hypergraph $\mathcal{H}(Q)$* of $Q$ is the hypergraph having one vertex for each element in $\vec{z}$ and one hyperedge spanning $\vars(\vec{u}_j)$ for each $j \in J$.
> 
> For $V \subseteq \elems(\vec{z})$, we define
>   - the *set $\mathrm{relv}_Q(V)$ of $V$-relevant atom indices in $Q$* to be the set $$\mathrm{relv}_Q(V) := \set{\ j \in J \mid \elems(\vec{u}_j) \cap V \neq \emptyset \ }$$
>   - the *set $\mathrm{clidx}_Q(V)$ of $V$-closed atom indices in $Q$ to be the set* $$\mathrm{clidx}_Q(V) := \set{\ j \in J \mid \elems(\vec{u}_j) \subseteq V \ }$$
>   - the *subquery $\mathrm{ind}_V(Q)$ strictly induced by $V$* to be the boolean conjunctive query $$\mathrm{ind}_V(Q) := \exists \vec{V}. \bigwedge_{j \in \mathrm{clidx}_Q(V)}A_j(\vec{u}_j)$$
>   - the *$V$-masked query structure hypergraph $\mathcal{H}(Q-V)$* to be the hypergraph that can be obtained by weakly deleting all vertices in $V$ from $\mathcal{H}_V$ and then removing all empty hyperedges.

## The Algorithm

Now we describe the structure that will be used in describing the DP algorithm.

> **Definition**. Let $\mathcal{L}$ be a language, $\Sigma$ be a set of $\mathcal{L}$-GTGDs with single-headed existential rules, $Q = \exists \vec{z}. \bigwedge_{j \in J} A_j(\vec{u}_j)$ a connected fully $\Sigma$-existential boolean $\mathcal{L}$-conjunctive query with $\consts(Q) \subseteq \consts(\Sigma)$. Let $\mathcal{H}(Q)$ be the query structure hypergraph of $Q$.
> 
> The set $\mathrm{Conn}_Q$ of *connected set of variables in $Q$* is the set of all $\mathcal{H}(Q)$-connected subsets of $\elems(\vec{z}) = \mathcal{V}_\mathcal{H}$.
> 
> The set $\mathrm{LocalInst}_{\mathcal{L}, \Sigma}$ of *$\Sigma$-saturated local instances* is the set of all $\mathcal{L}$-structures $I$ over the set $W_\Sigma = \set{0, \ldots, 2 \times \mathrm{maxArity}_\mathcal{L} - 1, c_0, \ldots, c_{n-1}}$ where $\set{c_i}_{0 \leq i < n}$ is an enumeration of $\consts(\Sigma)$, such that $I \models \Sigma$.
> 
> For $V \in \mathrm{Conn}_Q$ and $I \in \mathrm{LocalInst}_{\mathcal{L}, \Sigma}$, the *set $\mathrm{NbhdSubsts}_{V, I}$ of neighbourhood local substitutions into $I$ around $V$* is defined to be the set of all functions $\sigma: \mathrm{nbhd}_\mathcal{H}(V) \rightarrow \overline{ 2 \times \mathrm{maxArity}_\mathcal{L}} \cap \mathrm{ActiveValues}(I)$.

Consider the following recursively defined problem on the set $$\sum_{\substack{V \in \mathrm{Conn}_Q \\ I \in \mathrm{LocalInst}_{\mathcal{L}, \Sigma}}} \mathrm{NbhdSubsts}_{V, I}\ .$$
> **Definition**. Let $\mathcal{L}$ be a language, $\Sigma$ be a set of $\mathcal{L}$-GTGDs with single-headed existential rules, $Q = \exists \vec{z}. \bigwedge_{j \in J} A_j(\vec{u}_j)$ a connected fully $\Sigma$-existential boolean $\mathcal{L}$-conjunctive query with $\consts(Q) \subseteq \consts(\Sigma)$. Let $\mathcal{H}(Q)$ be the query structure hypergraph of $Q$.
> 
> Let $\mathrm{SubqueryEntailments}_{\Sigma, Q}$ be the set of triples $$\langle V, I, \sigma \rangle \in \sum_{\substack{V \in \mathrm{Conn}_Q \\ I \in \mathrm{LocalInst}_{\mathcal{L}, \Sigma}}} \mathrm{NbhdSubsts}_{V, I}$$such that either
>   - $V = \emptyset$, or
>   - if $\mathcal{I}_{W_\Sigma}(I, \sigma) \subseteq \mathrm{LocalInst}_{\mathcal{L}, \Sigma}$ is the set of *all* saturated local instances over $W_\Sigma$ obtainable from $I$ without dropping any local name in $\operatorname{im}(\sigma)$, then there is some $I' \in \mathcal{I}_{W_\Sigma}(I, \sigma)$ (called a *successful branching point under $\langle V, \langle I, \sigma \rangle \rangle$*) and a nonempty partial local substitution $\sigma': V \rightharpoonup \overline{ 2 \times \mathrm{maxArity}_\mathcal{L}} \cap \mathrm{ActiveValues}(I)$ on $V$ satisfying the following *branching conditions at $I'$*:
>       - for every $j \in J$, if $\vars(\vec{u}_j) \subseteq \operatorname{dom}(\sigma \cup \sigma')$ and $\vars(\vec{u}_j) \cap \operatorname{dom}(\sigma') \neq \emptyset$, then  $A_j((\sigma \cup \sigma')(\vec{u}_j)) \in I'$, and
>       - for every connected component $V'$ of $\mathcal{H}(\mathrm{ind}_V(Q) - \operatorname{dom}(\sigma'))$, $$\langle V', I', (\sigma \cup \sigma') \upharpoonright \mathrm{nbhd}_{\mathcal{H}(Q)}(V') \rangle {} \in \mathrm{SubqueryEntailments}_{\Sigma, Q}.$$

> *Remark*. The definition of $\mathrm{SubqueryEntailments}_{\Sigma, Q}$ is recursive on the size of $V \in \mathrm{Conn}_Q$.

The problem $\mathrm{SubqueryEntailments}_{\Sigma, Q}$, which can be decided by a recursion if one wishes to do so, precisely models the query entailment problem as its name suggests.

> **Theorem ($\mathrm{SubqueryEntailments}_{\Sigma, Q}$ is Equivalent to Subquery Entailment)**.
> Let $\mathcal{L}$ be a language, $\Sigma$ be a set of $\mathcal{L}$-GTGDs with single-headed existential rules, $Q = \exists \vec{z}. \bigwedge_{j \in J} A_j(\vec{u}_j)$ a connected fully $\Sigma$-existential boolean $\mathcal{L}$-conjunctive query with $\consts(Q) \subseteq \consts(\Sigma).$
> 
> Then for every triple $$\langle V, I, \sigma \rangle \in \sum_{\substack{V \in \mathrm{Conn}_Q \\ I \in \mathrm{LocalInst}_{\mathcal{L}, \Sigma}}} \mathrm{NbhdSubsts}_{V, I},$$we have $$
\left(
  I \wedge \Sigma \models
    \exists \overrightarrow{V}.
      \bigwedge_{j \in \mathrm{relv}_Q(V)}
        A_j(\sigma(\vec{u}_j))
\right) \Longleftrightarrow \langle
    V, I, \sigma
  \rangle \in \mathrm{SubqueryEntailments}_{\Sigma, Q}.
$$
>
> > *Proof*.
> > ($\Longrightarrow$, "completeness"): (TODO)
> > 
> > ($\Longleftarrow$, "soundness"): We proceed by induction on $|V|$. Suppose $\langle V, I, \sigma \rangle \in \mathrm{SubqueryEntailments}_{\Sigma, Q}$.
> > 
> > If $V = \emptyset$, $\exists \overrightarrow{V}. \bigwedge_{j \in \mathrm{relv}_Q(V)} A_j(\sigma(\vec{u}_j)) \equiv \top$ so we are done.
> > 
> > So assume $V \neq \emptyset$. By definition of $\mathrm{SubqueryEntailments}_{\Sigma, Q}$, there exists a successful branching point $I' \in \mathcal{I}_{W_\Sigma}(I, \sigma)$ under $\langle V, I, \sigma \rangle$ and a nonempty $\sigma': V \rightharpoonup \overline{ 2 \times \mathrm{maxArity}_\mathcal{L}} \cap \mathrm{ActiveValues}(I)$ satisfying branching conditions at $I'$.
> > 
> > Let $\set{ V'_i }_{i \in I_{V, \sigma'}}$ be the family of connected components of $\mathcal{H}(\mathrm{ind}_V(Q) - \operatorname{dom}(\sigma'))$, indexed by the set $I_{V, \sigma'}$. For each $i \in I_{V, \sigma'}$, $V' \subsetneq V$ and $V'$ satisfies the branching conditions at $I'$. Applying the inductive hypothesis to $V'_i$, we have $$
I' \wedge \Sigma \models
  \exists \overrightarrow{V'_i}.
    \bigwedge_{j \in \mathrm{relv}_Q(V'_i)}
      A_j((\sigma \cup \sigma')(\vec{u}_j)).
$$(TODO)

## Translating Generic BCQ Answering Problems to Subquery Entailments

The following procedure allows us to reduce arbitrary BCQ answering problem to an instance of $\mathrm{SubqueryEntailments}_{\Sigma, -}$.

> **Definition**. Let $Q = \exists \vec{z}. \bigwedge_{j \in J} A_j(\vec{u}_j)$ be a connected boolean conjunctive query, which need not be fully $\Sigma$-existential. Let $I \in \mathrm{LocalInst}_{\mathcal{L}, \Sigma}$.
> 
> (TODO: "lift" $\langle I, Q \rangle$ to some $Q'_I, \sigma_{I, Q}$ so that we can test $I \wedge \Sigma \models Q$ by testing the membership $\langle Q'_I, \langle I, \sigma \rangle \rangle \in \mathrm{SubqueryEntailments}_{\Sigma, Q'_I}$)

> **Proposition**. (State that $I \wedge \Sigma \models Q$ if and only if the "lift" $Q'_I, \sigma_{I, Q}$ of $\langle I, Q \rangle$ exists, and $\langle Q'_I, \langle I, \sigma_{I, Q} \rangle \rangle \in \mathrm{SubqueryEntailments}_{\Sigma, Q'_I}$.)
> 
> > *Proof*.
> > ($\Longrightarrow$): (TODO)
> >
> > ($\Longleftarrow$): (TODO)

## Monotonicity of Subquery Entailments

As $\mathrm{SubqueryEntailments}_{\Sigma, Q}$ is Equivalent to Subquery Entailment, it has certain monotonicity properties.

> **Definition**. (TODO: define a partial order $\preceq$ on $\sum_{\substack{V \in \mathrm{Conn}_Q \\ I \in \mathrm{LocalInst}_{\mathcal{L}, \Sigma}}} \mathrm{NbhdSubsts}_{V, I}$ so that $\mathrm{SubqueryEntailments}_{\Sigma, Q}$ is downward-closed in $\sum_{\substack{V \in \mathrm{Conn}_Q \\ I \in \mathrm{LocalInst}_{\mathcal{L}, \Sigma}}} \mathrm{NbhdSubsts}_{V, I}$)

> **Proposition**. $\mathrm{SubqueryEntailments}_Q$ is a downward-closed subset of $\langle \sum_{\substack{V \in \mathrm{Conn}_Q \\ I \in \mathrm{LocalInst}_{\mathcal{L}, \Sigma}}} \mathrm{NbhdSubsts}_{V, I}, \preceq \rangle$.