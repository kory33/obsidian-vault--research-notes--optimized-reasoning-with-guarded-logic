---
title: The Dynamic Programming Algorithm
tags:
  - notes
---

## Preliminaries

We begin with some preliminary notions.

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

> **Definition**. Let $\Sigma$ be a finite set of GTGDs.
> 
> A boolean conjunctive query $Q = \exists \vec{z}. \bigwedge_{j \in J} A_j(\vec{u}_j)$ is
>   - *fully $\Sigma$-existential* if $\consts(Q) \subseteq \consts(\Sigma)$, and for each $j \in J$, $\vars(\vec{u}_j) \neq \emptyset$
>   - *connected* if $\mathcal{H}(Q)$ is a connected hypergraph
> 

> **Definition**. Let $\mathcal{L}$ be a language and $\Sigma$ a finite set of TGDs.
> 
> For a set $D$ with $D \cap \consts(\Sigma) = \emptyset$, we write $D^{+\Sigma}$ for the set $D \cup \consts(\Sigma)$. A set of formal terms of the form $F(d_1, d_2, \ldots, d_{\Arity_\mathcal{L}(F)})$ with $d \in (D^{+\Sigma})^{\Arity_\mathcal{L}(F)}$ is said to be a *$\Sigma$-formal instance over $D$*. In particular, a ground instance (resp. an instance) is a $\Sigma$-formal instance over $\Consts_\mathcal{L} \setminus \consts(\Sigma)$ (resp. $\Nulls_\mathcal{L} \cup (\Consts_\mathcal{L} \setminus \consts(\Sigma))$). By an abuse of notation, we treat generic $\Sigma$-formal instances just like ordinary instances.
> 
> For a $\Sigma$-formal instance $I$ over $D$, *the set $\mathrm{ActiveValues}_D(I)$ of $D$-active values* is the set defined by $$
\mathrm{ActiveValues}_D(I) = \set{\ 
  d \in D \mid
    \exists F(\vec{e}) \in I. d \in \elems(\vec{e})
\ }.$$
> We say that a $\Sigma$-formal instance $I$ over a set $D$ is $(\mathcal{L}, \Sigma)$-small if $|\consts(I) \setminus \consts(\Sigma)| \leq \mathrm{maxArity}_\mathcal{L}$.

## The Algorithm

Now we describe the structure that will be used in describing the DP algorithm.

> **Definition**. Let $\mathcal{L}$ be a language, $\Sigma$ be a set of $\mathcal{L}$-GTGDs with single-headed existential rules, $Q = \exists \vec{z}. \bigwedge_{j \in J} A_j(\vec{u}_j)$ a connected fully $\Sigma$-existential boolean $\mathcal{L}$-conjunctive query with $\consts(Q) \subseteq \consts(\Sigma)$.
> 
> Let $\mathrm{LocalConsts}_\mathcal{L} = \set{0, \ldots, 2 \times \mathrm{maxArity}_\mathcal{L} - 1}$.
> 
> The set $\mathrm{RuleConstGuess}_{\Sigma, Q}$ *of guesses of $\Sigma$-constant substitutions* is the partial function space $$
\mathrm{RuleConstGuess}_{Q, \Sigma} :=
  \elems(\vec{z}) \rightharpoonup \consts(\Sigma).
$$
> 
> For $\sigma_\Sigma \in \mathrm{RuleConstGuess}_{\Sigma, Q}$, the set $\mathrm{Conn}_{Q-\sigma_\Sigma}$ of *$Q$-connected set of variables unassigned by $\sigma_\Sigma$* is the set of all $\mathcal{H}(Q - \mathrm{dom}(\sigma_\Sigma))$-connected subsets of $\elems(\vec{z}) \setminus \mathrm{dom}(\sigma_\Sigma) = \mathcal{V}_{\mathcal{H}(Q - \mathrm{dom}(\sigma_\Sigma))}$.
> 
> The set $\mathrm{LocalInst}_{\mathcal{L}, \Sigma}$ of *$\Sigma$-saturated local instances* is the set of all $\Sigma$-formal instances $I$ over $\mathrm{LocalConsts}_\mathcal{L}$ such that $\FullSat_\Sigma(I) = I$.
> 
> For $V \in \mathrm{Conn}_Q$ and $I \in \mathrm{LocalInst}_{\mathcal{L}, \Sigma}$, the *set $\mathrm{NbhdSubsts}_{V, I}$ of $V$-neighbourhood local substitutions into $I$* is the function space $$
\mathrm{NbhdSubsts}_{V, I} :=
  {\mathrm{nbhd}_\mathcal{H}(V)}
    \rightarrow
  (\mathrm{ActiveValues}_{\mathrm{LocalConsts}_\mathcal{L}}(I)).
$$
>
> Finally, the *problem space $\mathrm{SubqueryEntailmentInstances}_{\Sigma, Q}$ of subquery entailments* is defined to be the dependent sum $$
\sum_{\substack{
  \sigma_\Sigma \in \mathrm{RuleConstGuess}_{\Sigma, Q} \\
  I \in \mathrm{LocalInst}_{\mathcal{L}, \Sigma}
}}
\sum_{V \in \mathrm{Conn}_{Q-\sigma_\Sigma}}
  \mathrm{NbhdSubsts}_{V, I}
$$

We now consider the following recursively defined problem $\mathrm{SubqueryEntailments}_{\Sigma, Q} \subseteq \mathrm{SubqueryEntailmentInstances}_{\Sigma, Q}$

> **Definition**. Let $\mathcal{L}$ be a language, $\Sigma$ be a set of $\mathcal{L}$-GTGDs with single-headed existential rules, $Q = \exists \vec{z}. \bigwedge_{j \in J} A_j(\vec{u}_j)$ a connected fully $\Sigma$-existential boolean $\mathcal{L}$-conjunctive query with $\consts(Q) \subseteq \consts(\Sigma)$. Let $\mathcal{H}(Q)$ be the query structure hypergraph of $Q$.
> 
> Let $\mathrm{SubqueryEntailments}_{\Sigma, Q}$ be the set of 4-tuples $$\langle \sigma_\Sigma, V, I, \sigma_\text{local} \rangle \in \mathrm{SubqueryEntailmentInstances}_{\Sigma, Q}$$such that either
>   - $V = \emptyset$, or
>   - If $\mathcal{I}_{W_\Sigma}(I, \sigma_\text{local}) \subseteq \mathrm{LocalInst}_{\mathcal{L}, \Sigma}$ is the set of *all* $\Sigma$-saturated local instances over $\mathrm{LocalConsts}_\mathcal{L}$ that can be obtained from $I$ by applying finitely many existential rules in $\Sigma$ without dropping any local name in $\operatorname{im}(\sigma_\text{local})$, then there is some $I' \in \mathcal{I}_{W_\Sigma}(I, \sigma_\text{local})$ (which we shall call *successful branching point under $\langle \sigma_\Sigma, V, I, \sigma_\text{local} \rangle$*) and a *nonempty* partial local substitution $\sigma_\text{new}: V \rightharpoonup \mathrm{ActiveValues}_{\mathrm{LocalConsts}_\mathcal{L}}(I')$ on $V$ satisfying the following *branching conditions at $I'$*:
>       - for every $j \in J$, if $\vars(\vec{u}_j) \subseteq \operatorname{dom}(\sigma_\Sigma \cup \sigma_\text{local} \cup \sigma_\text{new})$ and $\vars(\vec{u}_j) \cap \operatorname{dom}(\sigma_\text{new}) \neq \emptyset$, then $A_j((\sigma_\Sigma \cup \sigma_\text{local} \cup \sigma_\text{new})(\vec{u}_j)) \in I'$, and
>       - for every connected component $V'$ of $\mathcal{H}(\mathrm{ind}_V(Q) - \operatorname{dom}(\sigma'))$, $$\langle \sigma_\Sigma, V', I', (\sigma_\text{local} \cup \sigma_\text{new}) \upharpoonright \mathrm{nbhd}_{\mathcal{H}(Q)}(V') \rangle {} \in \mathrm{SubqueryEntailments}_{\Sigma, Q}.$$

> *Remark*. The definition of $\mathrm{SubqueryEntailments}_{\Sigma, Q}$ is recursive on the size of $V \in \mathrm{Conn}_{Q - \sigma_\Sigma}$, and the set $$
\sum_{
  I' \in
    \mathcal{I}_{W_\Sigma}(I, \sigma_\text{local})
} (
  V \rightharpoonup 
    \mathrm{ActiveValues}_{\mathrm{LocalConsts}_\mathcal{L}}(I')
)
$$of all recursion branches can be computed in a finite amount of time. In particular, $\mathrm{SubqueryEntailments}_{\Sigma, Q}$ can be decided.

As the name suggests, the problem $\mathrm{SubqueryEntailments}_{\Sigma, Q}$ precisely models the query entailment problem.

> **Theorem ($\mathrm{SubqueryEntailments}_{\Sigma, Q}$ is Equivalent to Subquery Entailment)**.
> Let $\mathcal{L}$ be a language, $\Sigma$ be a set of $\mathcal{L}$-GTGDs with single-headed existential rules, $Q = \exists \vec{z}. \bigwedge_{j \in J} A_j(\vec{u}_j)$ a connected fully $\Sigma$-existential boolean $\mathcal{L}$-conjunctive query with $\consts(Q) \subseteq \consts(\Sigma).$
> 
> Then for every 4-tuple $$\langle \sigma_\Sigma, V, I, \sigma_\text{local} \rangle \in \mathrm{SubqueryEntailmentInstances}_{\Sigma, Q},$$we have $$
\left(
  I \wedge \Sigma \models
    \exists \overrightarrow{V}.
      \bigwedge_{j \in \mathrm{relv}_Q(V)}
        A_j((\sigma_\Sigma \cup \sigma_\text{local})(\vec{u}_j))
\right) \Longleftrightarrow \langle
    \sigma_\Sigma, V, I, \sigma_\text{local}
  \rangle \in \mathrm{SubqueryEntailments}_{\Sigma, Q}.
$$
>
> > *Proof*.
> > ($\Longrightarrow$, "completeness"): (TODO)
> > 
> > ($\Longleftarrow$, "soundness"): We proceed by induction on $|V|$. Suppose $\langle \sigma_\Sigma, V, I, \sigma_\text{local} \rangle \in \mathrm{SubqueryEntailments}_{\Sigma, Q}$.
> > 
> > If $V = \emptyset$, $\exists \overrightarrow{V}. \bigwedge_{j \in \mathrm{relv}_Q(V)} A_j((\sigma_\Sigma \cup \sigma_\text{local})(\vec{u}_j)) \equiv \top$ so we are done.
> > 
> > So assume $V \neq \emptyset$. By definition of $\mathrm{SubqueryEntailments}_{\Sigma, Q}$, there exists a successful branching point $I' \in \mathcal{I}_{W_\Sigma}(I, \sigma_\text{local})$ under $\langle \sigma_\Sigma, V, I, \sigma_\text{local} \rangle$ and a nonempty $\sigma_\text{new}: V \rightharpoonup \mathrm{ActiveValues}_{\mathrm{LocalConsts}_\mathcal{L}}(I')$ satisfying branching conditions at $I'$.
> > 
> > Let $\set{ V'_i }_{i \in I_{V, \sigma'}}$ be the family of connected components of $\mathcal{H}(\mathrm{ind}_V(Q) - \operatorname{dom}(\sigma'))$, indexed by the set $I_{V, \sigma'}$. For each $i \in I_{V, \sigma'}$, $V' \subsetneq V$ and $V'$ satisfies the branching conditions at $I'$. Applying the inductive hypothesis to $V'_i$, we have $$
I' \wedge \Sigma \models
  \exists \overrightarrow{V'_i}.
    \bigwedge_{j \in \mathrm{relv}_Q(V'_i)}
      A_j((\sigma_\Sigma \cup \sigma_\text{local} \cup \sigma_\text{new})(\vec{u}_j)).
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

## Using Subquery Entailments for Rewriting
