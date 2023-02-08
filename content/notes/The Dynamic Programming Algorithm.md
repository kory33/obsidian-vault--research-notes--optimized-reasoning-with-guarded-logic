Consider the following recursively defined problem:

> **Definition**. Let $\mathcal{L}$ be a language, $\Sigma$ be a set of $\mathcal{L}$-GTGDs with single-headed existential rules, $Q = \exists \vec{z}. \bigwedge_{j \in J} A(\vec{u}_j)$ a $\mathcal{L}$-conjunctive query with $\consts(Q) \subseteq \consts(\Sigma)$. Let $\mathcal{H}(Q)$ be the query structure hypergraph of $Q$.
> 
> Let $\mathrm{Entailments}$ be the set of triples $<Q', I, \sigma>$ with either $Q' = \emptyset$, or
>     - $Q' = Q_\overline{V}$ for some $V \subset \elems(\vec{z})$ that is $\mathcal{H}(Q)$-connected
>     - $I$ a local instance over $W = \set{0, \ldots, \mathrm{maxArity}_\mathcal{L} - 1, c_0, \ldots, c_{n-1}}$ where $c_i$ is an enumeration of $\consts(\Sigma)$
>     - $\sigma$ a partial local substitution $V \rightharpoonup \overline{\mathrm{maxArity}_\mathcal{L}}$ 
>  such that if $\mathcal{I}$ is the set of *all* local instances obtainable from $I$ without dropping any local name in $\operatorname{dom}(\sigma)$, then there is some $I' \in \mathcal{I}$ (called the *branching point* of $<Q', I, \sigma>$) and a proper extension $\sigma'$ of $\sigma$ with $\operatorname{dom}(\sigma') \subseteq V$ such that for every $\mathcal{H}(Q)$-connected component $V'$ of $\mathcal{H}(Q' - \operatorname{dom}(\sigma' \setminus \sigma))$, $$<Q_\overline{V'}, I', \sigma' \cap (\partial V' \times W)> {} \in \mathrm{Entailments}$$and for atom $A(\vec{u}_j)$ with $\vars(\vec{u}_j) \subseteq \operatorname{dom}(\sigma' \setminus \sigma)$, $A(\sigma'(\vec{u}_j)) \in I'$.

> *Remark*. The definition of $\mathrm{Entailments}$ is recursive on the complexity of the subquery.

> **Theorem**. (TODO: We can "lift" a conjunctive query with constants to an instance of $\mathrm{Entailments}$ problem by existentially quantifying all of $\consts(Q) \setminus \consts(\Sigma)$ and setting the partial local substitution $\sigma$ of those newly quantified variables to the local names corresponding to those variables mentioned in $I$ (if not the lifting procedure fails and we cannot hope for the entailment). Now we can state in this theorem that $I \wedge \Sigma \models Q$ if and only if $<Q, I', \sigma> \in \mathrm{Entailment}$, where $I', \sigma$ are generated simultaneously depending on $I$ and $Q$).
