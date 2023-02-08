---
title: The Dynamic Programming Algorithm
tags:
  - notes
---

Consider the following recursively defined problem:

> **Definition**. Let $\mathcal{L}$ be a language, $\Sigma$ be a set of $\mathcal{L}$-GTGDs with single-headed existential rules, $Q = \exists \vec{z}. \bigwedge_{j \in J} A_j(\vec{u}_j)$ a connected $\mathcal{L}$-conjunctive query with $\consts(Q) \subseteq \consts(\Sigma)$. Let $\mathcal{H}(Q)$ be the query structure hypergraph of $Q$.
> 
> Let $\mathrm{SubqueryEntailments}_Q$ be the set of triples $\langle Q', I, \sigma \rangle$ with
>   - $Q' = Q_V$ (the subquery of $Q$ induced by $V$) for some $\mathcal{H}(Q)$-connected $V \subset \elems(\vec{z}) = \mathcal{V}_\mathcal{H}$
>   - $I$ a $\Sigma$-saturated $(\mathcal{L}, \Sigma)$-small local instance over $W = \set{0, \ldots, 2 \times \mathrm{maxArity}_\mathcal{L} - 1, c_0, \ldots, c_{n-1}}$ where $\set{c_i}_{0 \leq i < n}$ is an enumeration of $\consts(\Sigma)$
>   - $\sigma$ a partial local substitution $V \rightharpoonup \overline{ 2 \times \mathrm{maxArity}_\mathcal{L}} \cap \mathrm{ActiveValues}(I)$ 
> 
> such that either
>   - $Q' = \emptyset$, or
>   - if $\mathcal{I}$ is the set of *all* saturated local instances over $W$ obtainable from $I$ without dropping any local name in $\operatorname{dom}(\sigma)$, then there is some $I' \in \mathcal{I}$ (called a *successful branching point under $<Q', I, \sigma>$*) and a proper extension $\sigma'$ of $\sigma$ with $\operatorname{dom}(\sigma') \subseteq V$ such that
>       - for every connected component $V'$ of $\mathcal{H}(Q' - \operatorname{dom}(\sigma'))$, $$\langle Q_\overline{V'}, I', \sigma' \upharpoonright \partial V' \rangle {} \in \mathrm{SubqueryEntailments}_Q$$where $\overline{V}$ and $\partial V'$ in the above expression are the closure and the boundary of $V'$ inside $\mathcal{H}(Q')$, and
>       - for every atom $A_j(\vec{u}_j)$ of $Q$, if $\vars(\vec{u}_j) \subseteq \operatorname{dom}(\sigma')$ then $A_j(\sigma'(\vec{u}_j)) \in I'$.

> *Remark*. The definition of $\mathrm{SubqueryEntailments}_Q$ is recursive on the complexity of the subquery.

> **Theorem**. (TODO: We can "lift" a conjunctive query with constants to an instance of $\mathrm{SubqueryEntailments}_Q$ problem by existentially quantifying all of $\consts(Q) \setminus \consts(\Sigma)$ and setting the partial local substitution $\sigma$ of those newly quantified variables to the local names corresponding to those variables mentioned in $I$ (if not the lifting procedure fails and we cannot hope for the entailment). Now we can state in this theorem that $I \wedge \Sigma \models Q$ if and only if $\langle Q', I', \sigma \rangle \in \mathrm{SubqueryEntailments}_Q$, where $Q'$ is the "lift" of $Q$ and $I', \sigma$ are generated simultaneously depending on $I$ and $Q'$).
