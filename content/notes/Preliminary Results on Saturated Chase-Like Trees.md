---
title: Preliminary Results on Saturated Chase-Like Trees
tags:
  - notes
---

## General Definitions surrounding $\SatTree$s

> **Definition.** For chase-like tree $T$ and its vertex $v \in T_0$, we say that $v$ *mentions* a factual term $t$ if $\Instance_T(v)$ contains a fact $P(\vec{t'})$ such that $t \in \elems(\vec{t'})$.

> **Definition.** For a chase-like tree $T$ and a factual term $t$, the _subgraph of $T$ mentioning $t$_, denoted $T \upharpoonright t$, is the subgraph of $T$ induced by the vertex set $V_t = \set{v \in T \mid v \text{ mentions } t }$ together with the instance assignment restricted to $V_t$, i.e. $\Instance_{T \upharpoonright t} = \Instance_T \upharpoonright V_t$ .

We can see that the subgraph of a $\SatTree$ mentioning $t$ really is then a subtree sitting in the $\SatTree$ as seen in the following proposition:

> **Proposition**. For a finite set $\Sigma$ of GTGDs, a base instance $I$ and any factual term $t$, $\SatTree_\Sigma(I) \upharpoonright t$ is connected. In particular, if $t$ is mentioned in $\TreeFacts(\SatTree_\Sigma(I))$, then $\SatTree_\Sigma(I) \upharpoonright t$ is a rooted subtree of $\SatTree_\Sigma(I)$.
> 
> > _Proof_. By construction of $\SatTree_\Sigma(I)$, we have that
> > - a factual term not already mentioned in $I$ is never introduced by any chase-step direction from any node
> > - a null introduced at a node $\vec{d}$ is never introduced anywhere else in the tree

Now, for each factual term $t$ mentioned somewhere in the $\SatTree$, we can identify where $t$ has been "introduced" in the tree:

> **Definition.** For a factual term $t$ mentioned in $\TreeFacts(\SatTree_\Sigma(I))$, the *introduction point $\Intro(t)$ of $t$* is the root node of the subtree $\SatTree_\Sigma(I) \upharpoonright t$.

Clearly, $\Intro(t)$ is the root node $()$ if and only if $t$ is a constant.

## Fact Introduction Lemma

We have the following useful lemma:

> **Lemma (Fact Introduction)**. For a node $n$ of $\SatTree_\Sigma(I)$, its ancestor node $a$ and a fact $P(\vec{t}) \in \Instance_{\SatTree_\Sigma(I)}(n)$, if $\Intro(t) \geq a$ for all $t \in \elems(\vec{t})$, then $P(\vec{t}) \in \Instance_{\SatTree_\Sigma(I)}(a)$.
> 
> > _Proof_. TODO (we would probably make a heavy use of this lemma when arguing validity of query reductions)

An immediate consequence of the lemma is the following:

> **Proposition**. If $P(\vec{t}) \in \TreeFacts(\SatTree_\Sigma(I))$ is a base fact, then $P(\vec{t}) \in \Sat_\Sigma(I)$. ^6bd969
> 
> > *Proof*.
> > By the assumption, $P(\vec{t}) \in \Instance_{\SatTree_\Sigma(I)}(n)$ for some node $n \in \SatTree_\Sigma(I)$.
> > 
> > Now for all $t \in \elems(\vec{t})$, $\Intro(t)$ is the root node $()$, which is an ancestor of $n$. Therefore by the Fact Introduction lemma $P(\vec{t}) \in \Instance_{\SatTree_\Sigma(I)}(()) = \Sat_\Sigma(I)$.
