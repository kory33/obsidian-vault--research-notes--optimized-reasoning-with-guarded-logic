---
title: Preliminary Results about Saturated Chase-Like Trees
tags:
  - notes
---

> **Definition.** For chase-like tree $T$ and its vertex $v \in T_0$, we say that $v$ *mentions* a factual term $t$ if $\Instance_T(v)$ contains a fact $P(\vec{t'})$ such that $t \in \elems(\vec{t'})$.

> **Definition.** For a chase-like tree $T$ and a factual term $t$, the _subgraph of $T$ mentioning $t$_, denoted $T \upharpoonright t$, is the subgraph of $T$ induced by the vertex set $V_t = \set{v \in T \mid v \text{ mentions } t }$ together with the instance assignment restricted to $V_t$, i.e. $\Instance_{T \upharpoonright t} = \Instance_T \upharpoonright V_t$ .

We can see that the subgraph of a $\SatTree$ mentioning $t$ really is then a subtree sitting in the $\SatTree$ as seen in the following proposition:

> **Proposition**. For a finite set $\Sigma$ of GTGDs, a base instance $I$ and any factual term $t$, $\SatTree_\Sigma(I) \upharpoonright t$ is connected. In particular, if $t$ is mentioned in $\TreeFacts(\SatTree_\Sigma(I))$, then $\SatTree_\Sigma(I) \upharpoonright t$ is a rooted subtree of $\SatTree_\Sigma(I)$.
> 
> _Proof (sketch)_. By construction of $\SatTree_\Sigma(I)$, we have that
>  - a factual term not already mentioned in $I$ is never introduced by any chase-step direction from any node
>  - a null introduced at a node $\vec{d}$ is never introduced anywhere else in the tree

Now, for each factual term $t$ mentioned somewhere in the $\SatTree$, we can identify where $t$ has been "introduced" in the tree:

> **Definition.** For a factual term $t$ mentioned in $\TreeFacts(\SatTree_\Sigma(I))$, the *introduction point $\Intro(t)$ of $t$* is the root node of the subtree $\SatTree_\Sigma(I) \upharpoonright t$.

Clearly, $\Intro(t)$ is the root node $()$ if and only if $t$ is a constant.

> **Proposition**. For a node $n$ of $\SatTree_\Sigma(I)$, its ancestor node $a$ and a fact $P(\vec{t}) \in \Instance_{\SatTree_\Sigma(I)}(n)$, if $\Intro(t) \geq a$ for all $t \in \elems(\vec{t})$, then $P(\vec{t}) \in \Instance_{\SatTree_\Sigma(I)}(a)$.
> 
> _Proof (sketch)_. TODO (is this even necessary? we'll see later)

### Witness Decomposition

^d79951

Now, we shall see how a witness on $\SatTree$ for a CQ is constrained. We begin with some preliminary definitions.

> **Definition**. For a boolean conjunctive query $Q$ and its witness $(\sigma, \mathcal{F})$, the *set of touchdowners* $\touchDowners(\sigma)$ of $\sigma$ is the set $\sigma^{-1}[\consts(\mathcal{F})]$ of variables that get sent to constants in $\mathcal{F}$.
> 
> **Examples**: ![[Pasted image 20221116200624.png]]![[Pasted image 20221116200657.png]] 

> **Definition**. For a valid generative chase-path $((\tau, \sigma))$ on $I$, we define the *tentacle of $\SatTree_\Sigma(I)$ hanging from $(\tau, \sigma)$* to be the subtree of $\SatTree_\Sigma(I)$ induced by all descendants of the node $((\tau, \sigma))$.

> **Definition**. For a binary conjunctive query $Q = \exists \vec{x}. \bigwedge_i Q_i(\vec{x'}_i)$, the *query structure hypergraph $\mathcal{H}(Q)$* of $Q$ is the labelled hypergraph defined with
>  - the vertex set $V_Q = \elems(\vec{x})$
>  - for each $i$, a hyperedge named $Q_i$ that spans $\elems(\vec{x'}_i) \subseteq V_Q$.

> **Definition**. For a BCQ $Q = \exists \vec{x}. \bigwedge_i Q_i(\vec{x'}_i)$ and a subset $X$ of $\elems(\vec{x})$, the *$X$-blind query structure hypergraph*, denoted $\mathcal{H}(Q-X)$, is the hypergraph obtained by weak-deleting [^1] all vertices in $X$.

First we have the following proposition, which states that "vertices adjacent in $\mathcal{H}(Q - \touchDowners(\sigma))$ must be sent to nulls lying the same chase-path":

> **Proposition**. For a binary conjunctive query $Q = \exists \vec{x}. \bigwedge_{j \in J} Q_j(\vec{x'}_j)$ and a witness $(\sigma, \SatTree_\Sigma(I))$, if two variables $x_1$ and $x_2$ appear in a single atom $Q_j(\vec{x'}_j)$ for some $j \in J$, then $\Intro(\sigma(x_1))$ and $\Intro(\sigma(x_2))$ are $\leq$-comparable.
> 
> > *Proof*. By assumption on $\sigma$, there exists a node (i.e. a valid chase-path on $I$) $\vec{d}$ such that $Q_j(\sigma(\vec{x'}_j)) \in \Instance_{\SatTree_\Sigma(I)}(n)$. Since both $\SatTree_\Sigma(I) \upharpoonright \sigma(x_1)$ and $\SatTree_\Sigma(I) \upharpoonright \sigma(x_2)$ are rooted subtrees containing $n$, both $\Intro(\sigma(x_1))$ and $\Intro(\sigma(x_2))$ are ancestors of $n$, so all of $\set{ n, \Intro(\sigma(x_1)), \Intro(\sigma(x_2)) }$ lie on the same path in $\SatTree_\Sigma(I)$.

^809307

From this proposition, we can now deduce the *witness decomposition*, as described in the following lemma:

> **Lemma (Witness Decomposition)**. For a binary conjunctive query $Q = \exists \vec{x}. \bigwedge_{j \in J} Q_j(\vec{x'}_j)$, a witness $(\sigma, \SatTree_\Sigma(I))$ and a connected component $V$ of $\mathcal{H}(Q - \touchDowners(\sigma))$, $\sigma$ sends variables in $V$ to nulls whose introduction points all lie in the same tentacle of $\SatTree_\Sigma(I)$. ^a87015
> 
> > *Proof*.
> > The [previous proposition][[#^809307]] implies that, if two variables $x_1$ and $x_2$ are adjacent in $\mathcal{H}(Q - \touchDowners(\sigma))$, then in particular they lie in the same tentacle.
> > 
> > So take any two variables $x_1, x_2$ in $V \in \ConnComp(\mathcal{H}(Q - \touchDowners(\sigma)))$. By connectedness of $V$, there exists a path $x_1 E_0 y_0 \ldots y_{k-1} E_K x_2$ from $x_1$ to $x_2$. By induction on $k$, all of $y_0, \ldots, y_{k-1}$ lie in the same tentacle in which $x_1$ is introduced, so $x_1$ and $x_2$ are introduced in the same tentacle.

### Witness Gluing

The previous section on [Witness Decomposition][[#^d79951]] described how we can decompose a witness on $\SatTree$s. In this section, we shall see the inverse operation that "glues several fragmented witnesses" into a single witness for a query.

We start with some definitions.

> **Definition**. We say that a factual substitution $\sigma$ is *a base-factual substitution* if $\operatorname{im} \sigma \subseteq \Consts$, and that it is a *null-factual substitution* if $\operatorname{im} \sigma \subseteq \Nulls$.

> **Definition**. Given a finite set $\Sigma$ of GTGDs, a base instance $I$ and a boolean conjunctive query $Q = \exists \vec{x}. \bigwedge_{j \in J} Q_j(\vec{x'}_j)$, a *$(\Sigma, I)$-fragmented substitution for $Q$* is a pair $(\sigma_b, \set{ \sigma'_V }_{V \in \ConnComp(\mathcal{H}(Q - \domain(\sigma_b))})$ such that
>  - $\sigma_b$ is a base-factual substitution such that $\domain(\sigma_b) \subseteq \elems(\vec{x})$
>  - for each $V \in \ConnComp(\mathcal{H}(Q - \domain(\sigma_b)))$, $\sigma'_V$ is a null-factual substitution with $\domain(\sigma'_V) = V$.
>
> We will often omit the indexing set of the family $\set{\sigma'_V}$.

> **Definition**. A $(\Sigma, I)$-fragmented substitution $(\sigma_b, \set{\sigma'_V}_V)$ for $Q$ is said to be a *$(\Sigma, I)$-fragmented witness for $Q$* if
>  - TODO (require that atoms contained in $\touchDowners(\sigma)$ are witnessed in the root of $\SatTree$)
>  - TODO (require that each $\sigma'_V$ takes $V$ to nulls whose tentacle witnesses all atoms contained in $V$)

> **Remark**. By construction, $(\Sigma, I)$-fragmented substitution $(\sigma_b, \set{\sigma'_V}_V)$ for $Q$ is a *collection of compatible factual substitutions*, in a sense that $\sigma_b \not\in \set{\sigma'_V}_V$, and for each pair $\sigma_1, \sigma_2$ of factual substitutions in the set $\set{ \sigma_b } \cup \set{ \sigma'_V }_V$, $\domain(\sigma_1) \cup \domain(\sigma_2) \neq \emptyset \Longrightarrow \sigma_1 = \sigma_2$.

> **Definition**. By the previous remark, for a $(\Sigma, I)$-fragmented substitution $(\sigma_b, \set{\sigma'_V}_V)$ for $Q$, the set-theoretic union $\bigcup(\set{ \sigma_b } \cup \set{ \sigma'_V }_V)$ is a well-defined factual substitution. We shall call this union the *gluing of $(\sigma_b, \set{\sigma'_V}_V)$*, and denote it by $\Glue(\sigma_b, \set{\sigma'_V}_V)$.

> **Lemma (Witness Gluing)**. Suppose $(\sigma_b, \set{\sigma'_V})$ is a $(\Sigma, I)$-fragmented witness for $Q$. Then $(\Glue(\sigma_b, \set{\sigma'_V}_V), \SatTree_\Sigma(I))$ is a witness for $Q$.
> 
> > *Proof*. TODO; should be a routine.

[^1]: see Ch. 7, [[Books#^327283]] for details