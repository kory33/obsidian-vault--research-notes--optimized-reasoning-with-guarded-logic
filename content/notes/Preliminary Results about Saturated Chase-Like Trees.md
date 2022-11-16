---
title: Preliminary Results about Saturated Chase-Like Trees
tags:
  - notes
---

**Definition.** For chase-like tree $T$ and its vertex $v \in T_0$, we say that $v$ *mentions* a factual term $t$ if $\Instance_T(v)$ contains a fact $P(\vec{t'})$ such that $t \in \elems(\vec{t'})$.

**Definition.** For a chase-like tree $T$ and a factual term $t$, the _subgraph of $T$ mentioning $t$_, denoted $T \upharpoonright t$, is the subgraph of $T$ induced by the vertex set $V_t = \set{v \in T \mid v \text{ mentions } t }$ together with the instance assignment restricted to $V_t$, i.e. $\Instance_{T \upharpoonright t} = \Instance_T \upharpoonright V_t$ .

We can see that the subgraph of a $\SatTree$ mentioning $t$ really is then a subtree sitting in the $\SatTree$ as seen in the following proposition:

**Proposition**. For a finite set $\Sigma$ of GTGDs, a base instance $I$ and any factual term $t$, $\SatTree_\Sigma(I) \upharpoonright t$ is connected. In particular, if $t$ is mentioned in $\TreeFacts(\SatTree_\Sigma(I))$, then $\SatTree_\Sigma(I) \upharpoonright t$ is a rooted subtree of $\SatTree_\Sigma(I)$.

_Proof (sketch)_. By construction of $\SatTree_\Sigma(I)$, we have that
 - a factual term not already mentioned in $I$ is never introduced by any chase-step direction from any node
 - a null introduced at a node $\vec{d}$ is never introduced anywhere else in the tree

Now, for each factual term $t$ mentioned somewhere in the $\SatTree$, we can identify where $t$ has been "introduced" in the tree:

**Definition.** For a factual term $t$ mentioned in $\TreeFacts(\SatTree_\Sigma(I))$, the *introduction point $\Intro(t)$ of $t$* is the root node of the subtree $\SatTree_\Sigma(I) \upharpoonright t$.

Clearly, $\Intro(t)$ is the root node $()$ if and only if $t$ is a constant.

**Proposition**. For a node $n$ of $\SatTree_\Sigma(I)$, its ancestor node $a$ and a fact $P(\vec{t}) \in \Instance_{\SatTree_\Sigma(I)}(n)$, if $\Intro(t) \geq a$ for all $t \in \elems(\vec{t})$, then $P(\vec{t}) \in \Instance_{\SatTree_\Sigma(I)}(a)$.

_Proof (sketch)_. TODO (is this even necessary? we'll see later)

### Witness Constraints

Now, we see how a witness on $\SatTree$ for a CQ is constrained. We begin with some preliminary definitions.

**Definition**. For a conjunctive query $Q$ and its witness $(\sigma, \mathcal{F})$, the *consts preimage* $\consts(\sigma)$ of $\sigma$ (TODO: a better name?) is the set $\sigma^{-1}[\consts(\mathcal{F})]$ of variables that get sent to constants in $\mathcal{F}$.

**Definition**. For a valid generative chase-path $((\tau, \sigma))$ on $I$, we define the *tentacle of $\SatTree_\Sigma(I)$ hanging from $(\tau, \sigma)$* to be the subtree of $\SatTree_\Sigma(I)$ induced by all descendants of the node $((\tau, \sigma))$.

**Definition**. For a binary conjunctive query $Q = \exists \vec{x}. \bigwedge_i Q_i(\vec{x'}_i)$, the *query structure hypergraph $\mathcal{H}(Q)$* of $Q$ is the labelled hypergraph defined with
 - the vertex set $V_Q = \elems(\vec{x})$
 - for each $i$, a hyperedge named $Q_i$ that spans $\elems(\vec{x'}_i) \subseteq V_Q$.

**Definition**. For a BCQ $Q = \exists \vec{x}. \bigwedge_i Q_i(\vec{x'}_i)$ and a subset $X$ of $\elems(\vec{x})$, the *$X$-residual query structure hypergraph* (TODO: a better name?), denoted $\mathcal{H}(Q-X)$, is the hypergraph obtained by weak-deleting [^1] all vertices in $X$.

We then have the following:

**Proposition**. For a binary conjunctive query $Q = \exists \vec{x}. \bigwedge_i Q_i(\vec{x'}_i)$, a witness $(\sigma, \SatTree_\Sigma(I))$ and a connected component $V$ of $\mathcal{H}(Q - \consts(\sigma))$, $\sigma$ sends variables in $V$ to nulls whose introduction points all lie in the same tentacle of $\SatTree_\Sigma(I)$. ^a87015

*Proof (sketch)*. (TODO, but shouldn't be much complicated)

[^1]: see Ch. 7, [[Books#^327283]] for details