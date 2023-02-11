---
title: The Dynamic Programming Algorithm
tags:
  - notes
---

> **Definition**. Let $\mathcal{H}$ be a hypergraph. We say that a subset $V \subseteq \mathcal{V}_\mathcal{H}$ of vertex set is *$\mathcal{H}$-coconnected* if $\mathcal{V}_\mathcal{H} \setminus V$ is connected in $\mathcal{H}$.

> **Definition**. Let $\mathcal{L}$ be a language, $\Sigma$ be a set of $\mathcal{L}$-GTGDs with single-headed existential rules, $Q = \exists \vec{z}. \bigwedge_{j \in J} A_j(\vec{u}_j)$ a connected $\mathcal{L}$-conjunctive query with $\consts(Q) \subseteq \consts(\Sigma)$. Let $\mathcal{H}(Q)$ be the query structure hypergraph of $Q$.
> 
> The set $\mathrm{Conn}_Q$ of *connected subqueries of $Q$* is the set of all $\mathcal{H}(Q)$-connected subsets of $\elems(\vec{z}) = \mathcal{V}_\mathcal{H}$.
> 
> The set $\mathrm{LocalInst}_{\mathcal{L}, \Sigma}$ of *$\Sigma$-saturated local instances* is the set of all $\mathcal{L}$-structures $I$ over the set $W_\Sigma = \set{0, \ldots, 2 \times \mathrm{maxArity}_\mathcal{L} - 1, c_0, \ldots, c_{n-1}}$ where $\set{c_i}_{0 \leq i < n}$ is an enumeration of $\consts(\Sigma)$, such that $I \models \Sigma$.
> 
> For $V \in \mathrm{Conn}_Q$ and $I \in \mathrm{LocalInst}_{\mathcal{L}, \Sigma}$, the *set $\mathrm{CcnPartialSubsts}_{V, I}$ of coconnected partial substitutions of $I$ on $V$* is defined to be the set of all partial functions $\sigma: V \rightharpoonup \overline{ 2 \times \mathrm{maxArity}_\mathcal{L}} \cap \mathrm{ActiveValues}(I)$ such that $\mathrm{dom}(\sigma)$ is $\mathcal{H}(Q_V)$-coconnected.

Consider the following recursively defined problem on $$\sum_{\substack{V \in \mathrm{Conn}_Q \\ I \in \mathrm{LocalInst}_{\mathcal{L}, \Sigma}}} \mathrm{CcnPartialSubsts}_{V, I}\ .$$
> **Definition**. Let $\mathcal{L}$ be a language, $\Sigma$ be a set of $\mathcal{L}$-GTGDs with single-headed existential rules, $Q = \exists \vec{z}. \bigwedge_{j \in J} A_j(\vec{u}_j)$ a connected $\mathcal{L}$-conjunctive query with $\consts(Q) \subseteq \consts(\Sigma)$. Let $\mathcal{H}(Q)$ be the query structure hypergraph of $Q$.
> 
> Let $\mathrm{SubqueryEntailments}_{\Sigma, Q}$ be the set of triples $$\langle V, I, \sigma \rangle \in \sum_{\substack{V \in \mathrm{Conn}_Q \\ I \in \mathrm{LocalInst}_{\mathcal{L}, \Sigma}}} \mathrm{CcnPartialSubsts}_{V, I}$$such that either
>   - $V = \emptyset$, or
>   - if $\mathcal{I}_{W_\Sigma}(I, \sigma)$ is the set of *all* saturated local instances over $W_\Sigma$ obtainable from $I$ without dropping any local name in $\operatorname{dom}(\sigma)$, then there is some $I' \in \mathcal{I}_{W_\Sigma}(I, \sigma)$ (called a *successful branching point under $\langle V, \langle I, \sigma \rangle \rangle$*) and a proper extension $\sigma' \in \mathrm{CcnPartialSubsts}_{I', Q_V}$ of $\sigma$ such that
>       - for every connected component $V'$ of $\mathcal{H}(Q_V - \operatorname{dom}(\sigma'))$, $$\langle \overline{V'}, I', \sigma' \upharpoonright \partial V' \rangle {} \in \mathrm{SubqueryEntailments}_{\Sigma, Q}$$where $\overline{V'}$ and $\partial V'$ in the above expression are the closure and the boundary of $V'$ inside $\mathcal{H}(Q_V)$, and
>       - for every atom $A_j(\vec{u}_j)$ of $Q_V$, if $\vars(\vec{u}_j) \subseteq \operatorname{dom}(\sigma')$ then $A_j(\sigma'(\vec{u}_j)) \in I'$.

> *Remark*. The definition of $\mathrm{SubqueryEntailments}_{\Sigma, Q}$ is recursive on the complexity of the subquery.

The problem $\mathrm{SubqueryEntailments}_{\Sigma, Q}$, which can be decided by a recursion if one wishes to do so, precisely models the query entailment problem as its name suggests.

> **Theorem ($\mathrm{SubqueryEntailments}_{\Sigma, Q}$ is Equivalent to Subquery Entailment)**.
> Let $\mathcal{L}$ be a language, $\Sigma$ be a set of $\mathcal{L}$-GTGDs with single-headed existential rules, $Q = \exists \vec{z}. \bigwedge_{j \in J} A_j(\vec{u}_j)$ a connected $\mathcal{L}$-conjunctive query with $\consts(Q) \subseteq \consts(\Sigma).$
> 
> Then for every triple $$\langle V, I, \sigma \rangle \in \sum_{\substack{V \in \mathrm{Conn}_Q \\ I \in \mathrm{LocalInst}_{\mathcal{L}, \Sigma}}} \mathrm{CcnPartialSubsts}_{V, I},$$we have $$
I \wedge \Sigma \models \exists \overrightarrow{\vec{z} \setminus \mathrm{dom}(\sigma)}. \bigwedge_{j \in J_V} A_j(\sigma(\vec{u}_j))
  \Longleftrightarrow \langle
    Q_V, \langle I, \sigma \rangle
  \rangle \in \mathrm{SubqueryEntailments}_{\Sigma, Q}.
$$
>> *Proof*.
>> ($\Longrightarrow$, "completeness"): (TODO)
>> 
>> ($\Longleftarrow$, "soundness"): (TODO)

The following procedure allows us to reduce arbitrary BCQ answering problem to an instance of $\mathrm{SubqueryEntailments}_{\Sigma, -}$.

> **Definition**. Let $Q = \exists \vec{z}. \bigwedge_{j \in J} A_j(\vec{u}_j)$ be a connected boolean conjunctive query, which need not have $\consts(Q) \subseteq \consts(\Sigma)$. Let $I \in \mathrm{LocalInst}_{\mathcal{L}, \Sigma}$.
> 
> (TODO: "lift" $\langle I, Q \rangle$ to some $Q'_I, \sigma_{I, Q}$ so that we can test $I \wedge \Sigma \models Q$ by testing the membership $\langle Q'_I, \langle I, \sigma \rangle \rangle \in \mathrm{SubqueryEntailments}_{\Sigma, Q'_I}$)

> **Proposition**. (State that $I \wedge \Sigma \models Q$ if and only if the "lift" $Q'_I, \sigma_{I, Q}$ of $\langle I, Q \rangle$ exists, and $\langle Q'_I, \langle I, \sigma_{I, Q} \rangle \rangle \in \mathrm{SubqueryEntailments}_{\Sigma, Q'_I}$.)
> 
> > *Proof*.
> > ($\Longrightarrow$): (TODO)
> >
> > ($\Longleftarrow$): (TODO)

As $\mathrm{SubqueryEntailments}_{\Sigma, Q}$ is Equivalent to Subquery Entailment, it has certain monotonicity properties.

> **Definition**. (TODO: define a partial order $\preceq$ on $\sum_{\substack{V \in \mathrm{Conn}_Q \\ I \in \mathrm{LocalInst}_{\mathcal{L}, \Sigma}}} \mathrm{CcnPartialSubsts}_{V, I}$ so that $\mathrm{SubqueryEntailments}_Q$ is downward-closed in $\sum_{\substack{V \in \mathrm{Conn}_Q \\ I \in \mathrm{LocalInst}_{\mathcal{L}, \Sigma}}} \mathrm{CcnPartialSubsts}_{V, I}$.)

> **Proposition**. $\mathrm{SubqueryEntailments}_Q$ is a downward-closed subset of $\langle \sum_{\substack{V \in \mathrm{Conn}_Q \\ I \in \mathrm{LocalInst}_{\mathcal{L}, \Sigma}}} \mathrm{CcnPartialSubsts}_{V, I}, \preceq \rangle$.