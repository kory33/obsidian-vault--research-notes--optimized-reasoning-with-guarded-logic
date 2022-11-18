---
title: Preliminary Results about Saturated Chase-Like Trees
tags:
  - notes
---

## General Definitions surrounding $\SatTree$s

> **Definition.** For chase-like tree $T$ and its vertex $v \in T_0$, we say that $v$ *mentions* a factual term $t$ if $\Instance_T(v)$ contains a fact $P(\vec{t'})$ such that $t \in \elems(\vec{t'})$.

> **Definition.** For a chase-like tree $T$ and a factual term $t$, the _subgraph of $T$ mentioning $t$_, denoted $T \upharpoonright t$, is the subgraph of $T$ induced by the vertex set $V_t = \set{v \in T \mid v \text{ mentions } t }$ together with the instance assignment restricted to $V_t$, i.e. $\Instance_{T \upharpoonright t} = \Instance_T \upharpoonright V_t$ .

We can see that the subgraph of a $\SatTree$ mentioning $t$ really is then a subtree sitting in the $\SatTree$ as seen in the following proposition:

> **Proposition**. For a finite set $\Sigma$ of GTGDs, a base instance $I$ and any factual term $t$, $\SatTree_\Sigma(I) \upharpoonright t$ is connected. In particular, if $t$ is mentioned in $\TreeFacts(\SatTree_\Sigma(I))$, then $\SatTree_\Sigma(I) \upharpoonright t$ is a rooted subtree of $\SatTree_\Sigma(I)$.
> 
> _Proof_. By construction of $\SatTree_\Sigma(I)$, we have that
>  - a factual term not already mentioned in $I$ is never introduced by any chase-step direction from any node
>  - a null introduced at a node $\vec{d}$ is never introduced anywhere else in the tree

Now, for each factual term $t$ mentioned somewhere in the $\SatTree$, we can identify where $t$ has been "introduced" in the tree:

> **Definition.** For a factual term $t$ mentioned in $\TreeFacts(\SatTree_\Sigma(I))$, the *introduction point $\Intro(t)$ of $t$* is the root node of the subtree $\SatTree_\Sigma(I) \upharpoonright t$.

Clearly, $\Intro(t)$ is the root node $()$ if and only if $t$ is a constant.

We have the following useful lemma:

> **Lemma (Fact Introduction)**. For a node $n$ of $\SatTree_\Sigma(I)$, its ancestor node $a$ and a fact $P(\vec{t}) \in \Instance_{\SatTree_\Sigma(I)}(n)$, if $\Intro(t) \geq a$ for all $t \in \elems(\vec{t})$, then $P(\vec{t}) \in \Instance_{\SatTree_\Sigma(I)}(a)$.
> 
> _Proof_. TODO

An immediate consequence of the lemma is the following:

> **Proposition**. If $P(\vec{t}) \in \TreeFacts(\SatTree_\Sigma(I))$ is a base fact, then $P(\vec{t}) \in \Sat_\Sigma(I)$.
> 
> > *Proof*.
> > By the assumption, $P(\vec{t}) \in \Instance_{\SatTree_\Sigma(I)}(n)$ for some node $n \in \SatTree_\Sigma(I)$.
> > 
> > Now for all $t \in \elems(\vec{t})$, $\Intro(t)$ is the root node $()$, which is an ancestor of $n$. Therefore by the Fact Introduction lemma $P(\vec{t}) \in \Instance_{\SatTree_\Sigma(I)}(()) = \Sat_\Sigma(I)$.

^6bd969

## Witness Decomposition

^d79951

Now, we shall see how a witness on $\SatTree$ for a CQ is constrained. We begin with some preliminary definitions.

> **Definition**. For a boolean conjunctive query $Q$ and its witness $(\sigma, \mathcal{F})$, the *set of touchdowners* $\touchDowners(\sigma)$ of $\sigma$ is the set $\sigma^{-1}[\consts(\mathcal{F})]$ of variables that get sent to constants in $\mathcal{F}$.
> 
> **Examples**: ![[Pasted image 20221116200624.png]]![[Pasted image 20221116200657.png]] 

> **Definition**. For a valid generative chase-path $((\tau, \sigma))$ on $I$, we define the *tentacle of $\SatTree_\Sigma(I)$ hanging from $(\tau, \sigma)$* to be the subtree of $\SatTree_\Sigma(I)$ induced by all descendants of the node $((\tau, \sigma))$.

> **Definition**. For a binary conjunctive query $Q = \exists \vec{x}. \bigwedge_i Q_i(\vec{x'}_i)$, the *query structure hypergraph $\mathcal{H}(Q)$* of $Q$ is the labelled hypergraph defined with
>  - the vertex set $V_Q = \elems(\vec{x})$
>  - for each $i$, a hyperedge named $Q_i$ that spans $\elems(\vec{x'}_i) \subseteq V_Q$.

> **Definition**. For a BCQ $Q = \exists \vec{x}. \bigwedge_i Q_i(\vec{x'}_i)$ and a subset $X$ of $\elems(\vec{x})$, the *$X$-masked query structure hypergraph*, denoted $\mathcal{H}(Q-X)$, is the hypergraph obtained by weak-deleting [^1] all vertices in $X$.

First we have the following proposition, which states that "vertices adjacent in $\mathcal{H}(Q - \touchDowners(\sigma))$ must be sent to nulls lying the same chase-path":

> **Proposition**. For a binary conjunctive query $Q = \exists \vec{x}. \bigwedge_{j \in J} Q_j(\vec{x'}_j)$ and a $(\Sigma, I)$-witness $\sigma$, if two variables $x_1$ and $x_2$ appear in a single atom $Q_j(\vec{x'}_j)$ for some $j \in J$, then $\Intro(\sigma(x_1))$ and $\Intro(\sigma(x_2))$ are $\leq$-comparable.
> 
> > *Proof*. By assumption on $\sigma$, there exists a node (i.e. a valid chase-path on $I$) $\vec{d}$ such that $Q_j(\sigma(\vec{x'}_j)) \in \Instance_{\SatTree_\Sigma(I)}(n)$. Since both $\SatTree_\Sigma(I) \upharpoonright \sigma(x_1)$ and $\SatTree_\Sigma(I) \upharpoonright \sigma(x_2)$ are rooted subtrees containing $n$, both $\Intro(\sigma(x_1))$ and $\Intro(\sigma(x_2))$ are ancestors of $n$, so all of $\set{ n, \Intro(\sigma(x_1)), \Intro(\sigma(x_2)) }$ lie on the same path in $\SatTree_\Sigma(I)$.

^809307

From this proposition, we can now deduce the *witness decomposition*, as described in the following lemma:

> **Lemma (Witness Decomposition)**. For a binary conjunctive query $Q = \exists \vec{x}. \bigwedge_{j \in J} Q_j(\vec{x'}_j)$, a $(\Sigma, I)$-witness $\sigma$ and a connected component $V$ of $\mathcal{H}(Q - \touchDowners(\sigma))$, $\sigma$ sends variables in $V$ to nulls whose introduction points all lie in the same tentacle of $\SatTree_\Sigma(I)$. ^a87015
> 
> > *Proof*.
> > The [previous proposition][[#^809307]] implies that, if two variables $x_1$ and $x_2$ are adjacent in $\mathcal{H}(Q - \touchDowners(\sigma))$, then in particular they lie in the same tentacle.
> > 
> > So take any two variables $x_1, x_2$ in $V \in \ConnComp(\mathcal{H}(Q - \touchDowners(\sigma)))$. By connectedness of $V$, there exists a path $x_1 E_0 y_0 \ldots y_{k-1} E_k x_2$ from $x_1$ to $x_2$. By induction on $k$, all of $y_0, \ldots, y_{k-1}$ lie in the same tentacle in which $x_1$ is introduced, so $x_1$ and $x_2$ are introduced in the same tentacle.

## Witness Gluing

The previous section on [Witness Decomposition][[#^d79951]] described how we can decompose a witness on $\SatTree$s. In this section, we shall see the inverse operation that "glues several fragmented witnesses" into a single witness for a query. *(TODO: this section no longer applies, because fragmented witnesses per se have nothing to do with the decomposition, and it is more correct to say that "decomposition translates to the world of fragmented witnesses by glue-fragmentation isomorphism")*

We start with some definitions.

> **Definition**. We say that a factual substitution $\sigma$ is *a base-factual substitution* if $\operatorname{im} \sigma \subseteq \Consts$, and that it is a *null-factual substitution* if $\operatorname{im} \sigma \subseteq \Nulls$.

> **Definition**. Given a finite set $\Sigma$ of GTGDs, a base instance $I$ and a boolean conjunctive query $Q = \exists \vec{x}. \bigwedge_{j \in J} Q_j(\vec{x'}_j)$, a *Q-fragmented substitution* is a pair $(\sigma_b, \set{ \sigma'_V }_{V \in \ConnComp(\mathcal{H}(Q - \domain(\sigma_b))})$ such that
>  - $\sigma_b$ is a base-factual substitution such that $\domain(\sigma_b) \subseteq \elems(\vec{x})$
>  - for each $V \in \ConnComp(\mathcal{H}(Q - \domain(\sigma_b)))$, $\sigma'_V$ is a null-factual substitution with $\domain(\sigma'_V) = V$.
>
> > *Notational convention*. We will often omit the indexing set of the family $\set{\sigma'_V}_{V \in \ConnComp(\mathcal{H}(Q - \domain(\sigma_b))}$ and simply write it as $\set{\sigma'_V}_V$.

> **Remark**. By construction, a $Q$-fragmented substitution $(\sigma_b, \set{\sigma'_V}_V)$ is a *collection of compatible factual substitutions*, in a sense that $\sigma_b \not\in \set{\sigma'_V}_V$, and for each pair $\sigma_1, \sigma_2$ of factual substitutions in the set $\set{ \sigma_b } \cup \set{ \sigma'_V }_V$, $\domain(\sigma_1) \cup \domain(\sigma_2) \neq \emptyset \Longrightarrow \sigma_1 = \sigma_2$.

> **Definition**. By the previous remark, for a $Q$-fragmented substitution $(\sigma_b, \set{\sigma'_V}_V)$, the set-theoretic union $\bigcup(\set{ \sigma_b } \cup \set{ \sigma'_V }_V)$ is a well-defined factual substitution. We shall call this union the *gluing of $(\sigma_b, \set{\sigma'_V}_V)$*, and denote it by $\Glue_Q(\sigma_b, \set{\sigma'_V}_V)$.

> **Definition**. For a BCQ $Q = \exists \vec{x}. \bigwedge_{j \in J} Q_j(\vec{x'}_j)$, a $Q$-fragmented substitution $(\sigma_b, \set{\sigma'_V}_V)$ is said to be a *$Q$-fragmented $(\Sigma, I)$-witness for $Q$* if
>  - for each $Q_j(\vec{x'}_j)$ in $Q$ such that $\elems(\vec{x'}_j) \subseteq \domain(\sigma_b)$, the fact $Q_j(\sigma_b(\vec{x'}_j))$ is an element of $\Sat_\Sigma(I)$, which is the instance assigned to the root of $\SatTree_\Sigma(I)$
>  - for each connected component $V \in \ConnComp(\mathcal{H}(Q - \domain(\sigma_b)))$ and each predicate $Q_j(\vec{x'}_j)$ corresponding to an edge $Q_j$ contained in $V$, the fact $Q_j((\sigma_V \circ \sigma_b)(\vec{x'}_j))$ is an element of $\TreeFacts(\SatTree_\Sigma(I))$.

Then almost by definition we obtain the following lemma:

> **Lemma (Witness Gluing)**. Suppose $(\sigma_b, \set{\sigma'_V}_V)$ is a $Q$-fragmented $(\Sigma, I)$-witness for $Q = \exists \vec{x}. \bigwedge_{j \in J} Q_j(\vec{x'}_j)$. Then $(\Glue_Q(\sigma_b, \set{\sigma'_V}_V), \SatTree_\Sigma(I))$ is a witness for $Q$.
> 
> > *Proof*.
> > Write $\sigma$ for the factual substitution $\Glue_Q(\sigma_b, \set{\sigma'_V}_V)$. Clearly $\sigma$ exactly covers $\vec{x}$.
> > 
> > Now pick $j \in J$. We need to see that $Q_j(\sigma(\vec{x'}_j))$ is an element of $\TreeFacts(\SatTree_\Sigma(I))$.
> > 
> > If the edge $Q_j$ does not span any vertex in $\mathcal{H}(Q - \domain(\sigma_b))$, then $Q_j$ does not mention any variable *not in* $\domain(\sigma_b)$. Hence $\elems(\vec{x'}_j) \subseteq \domain(\sigma_b)$, so by the assumption on $(\sigma_b, \set{\sigma'_V}_V)$, the fact $Q_j(\sigma_b(\vec{x'}_j))$ appears in $\Sat_\Sigma(I)$, hence in $\TreeFacts(\SatTree_\Sigma(I))$.
> > 
> > So suppose that $Q_j$ does span a vertex $x$ in $\mathcal{H}(Q - \domain(\sigma_b))$. Then $x$ belongs to some connected component $V$ of $\mathcal{H}(Q - \domain(\sigma_b))$, and by definition of being a connected component $Q_j$ spans vertices in $V$. So by assumption on $(\sigma_b, \set{\sigma'_V}_V)$, $Q_j((\sigma_V \circ \sigma_b)(\vec{x'}_j))$ is an element of $\TreeFacts(\SatTree_\Sigma(I))$. As $\sigma \supseteq \sigma_V \circ \sigma_b$, $Q_j(\sigma(\vec{x'}_j)) = Q_j((\sigma_V \circ \sigma_b)(\vec{x'}_j)) \in \TreeFacts(\SatTree_\Sigma(I))$.

## Fragmentation and Gluing

In this section, we shall see that fragmented witnesses and witnesses are in a bijective relation via the gluging operation and its inverse operation, which we shall call "fragmentation".

We begin with the definition of the fragmentation operator $\Frag_Q$.

> **Definition**. For a BCQ $Q = \exists \vec{x}. \bigwedge_{j \in J} Q_j(\vec{x'}_j)$ and a factual substitution $\sigma$ covering $\vec{x}$, define the *fragmentation $\Frag_Q(\sigma)$ of $\sigma$* as the $Q$-fragmented substitution $(\sigma_b, \set{\sigma'_V}_{V \in \ConnComp(\mathcal{H}(Q - \domain(\sigma_b)))})$, where
>  - $\sigma_b$ is a restriction of $\sigma$ to $\touchDowners(\sigma)$
>  - for each $V \in \ConnComp(\mathcal{H}(Q - \domain(\sigma_b)))$, $\sigma'_V: V \rightarrow \Facts$ is a restriction of $\sigma$ to $V$

Then the following holds:

> **Lemma** (Witness Fragmentation). If $\sigma$ is a $(\Sigma, I)$-witness for a BCQ $Q = \exists \vec{x}. \bigwedge_{j \in J} Q_j(\vec{x'}_j)$, then $\Frag_Q(\sigma)$ is a $Q$-fragmented $(\Sigma, I)$-witness for $Q$.
> 
> > *Proof*.
> > Let $(\sigma_b, \set{\sigma'_V}_V) = \Frag_Q(\sigma)$. We check that this is in fact a $Q$-fragmented $(\Sigma, I)$-witness for $Q$ according to the definition of $Q$-fragmented witnesses.
> > 
> > To check the first condition, take $j \in J$ such that $\elems(\vec{x'}_j) \subseteq \domain(\sigma_b)$. Then since $Q_j(\sigma(\vec{x'}_j)) \in \TreeFacts(\SatTree_\Sigma(I))$, by [a consequence][[#^6bd969]] of Fact Introduction lemma, $Q_j(\sigma(\vec{x'}_j)) \in \Sat_\Sigma(I)$.
> > 
> > To check the second condition, take $V \in \ConnComp(\mathcal{H}(Q - \domain(\sigma_b)))$ and $j \in J$ such that $Q_j$ lies entirely in $V$. Now $(\sigma_V \circ \sigma_b)(x) = \sigma(x)$ for each $x \in V \cup \domain(\sigma_b)$ by construction of $\sigma_V$ and $\sigma_b$, and as $\vec{x'}_j$ only contains variables from $V \cup \domain(\sigma_b)$, $Q_j((\sigma_V \circ \sigma_b)(\vec{x'}_j)) = Q_j(\sigma(\vec{x'}_j)) \in \TreeFacts(\SatTree_\Sigma(I))$.

As a corollary, we have the following propositions:

> **Proposition**. $\Frag_Q$ defines a assignment of $Q$-fragmented $(\Sigma, I)$-witnesses for $Q$ on the set of $(\Sigma, I)$-witnesses for $Q$

> **Theorem (Fragmentation-Gluing Bijection)**. For a BCQ $Q$, $\Frag_Q$ and $\Glue_Q$ are mutual bijections between $(\Sigma, I)$-witnesses for $Q$ and $Q$-fragmented $(\Sigma, I)$-witnesses for $Q$.
> 
> > *Proof*. We only need to check that the two maps are mutual inverses. But this is the case by definition: $\Frag_Q \circ \Glue_Q$ essentially unions fragmented substitutions and then restricts them to respective domains, while $\Glue_Q \circ \Frag_Q$ unions all restricted substitutions, recovering the original substitution.


[^1]: see Ch. 7, [[Books#^327283]] for details