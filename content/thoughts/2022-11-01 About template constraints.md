---
title: "2022-11-01: About template constraints"
tag:
  - thoughts
  - template-constraints
---

## Constraints on Partitioning Imposed by the Query

Suppose that the following query is given as $Q = \exists xyz. R(x, y) \wedge R(y, z)$.

There are a few ways this query could be witnessed by nulls in an infinite branch of the tree-like chase (a.k.a. "tentacles") or by constants in the collection of input or saturated facts (a.k.a. "squid head"). The following is an exhaustive list of all possible combinations:
 - 0 variable in the squid head
	 - all of $x, y, z$ get witnessed in the same tentacle
 - 1 variable in the squid head
	 - $x$ gets witnessed in the head and $y, z$ get witnessed in the same tentacle
	 - $y$ gets witnessed in the head and $x, z$ get witnessed in the same tentacle
	 - $y$ gets witnessed in the head and $x, z$ get witnessed in different tentacles
	 - $z$ gets witnessed in the head and $x, y$ get witnessed in the same tentacle
 - 2 variables in the squid head
	 - $x$ and $y$ get witnessed in the head and $z$ gets witnessed in a tentacle
	 - $x$ and $z$ get witnessed in the head and $y$ gets witnessed in a tentacle
	 - $y$ and $z$ get witnessed in the head and $x$ gets witnessed in a tentacle
 - 3 variables in the squid head
	 - All of $x, y, z$ get witnessed in the squid head

There are two impossible combinations, namely:

 - `x` gets witnessed in the head and $y$ and $z$ get witnessed in _different_ tentacles
 - `z` gets witnessed in the head and $y$ and $x$ get witnessed in _different_ tentacles

To see why, suppose $y$ and $z$ are instantiated as nulls $n_1$ and $n_2$ in _different tentacles_. Then there is nowhere in the infinite tree-like chase structure that proves $R(n_1, n_2)$, which uses $n_1$ and $n_2$ at the same time. So we conclude that: _if_ $y$ and $z$ are to be instantiated with nulls, _then_ that must be happen on the same tentacle.

Generalising the example above, we can see that: if the query contains an atom $P(\vec{u})$ within the existential, then every vector witnessing $\vec{u}$ in $P(\vec{u})$ always have all the nulls appear in the single tentacle.

So we can deduce to a certain extent how the instantiation of variables may be distributed to different tentacles by just looking at the query.

## Constraints Imposed by the Reasoning Rules

In this section, we shall write $\Sigma$ for the generic set of rules.

When a pseudoquery is proven in a tentacle of the infinite chase, one might imagine the following situation:

![[Pasted image 20221101171150.png]]

However, this diagram needs a slight modification: we will always get a set different from $\operatorname{Sat}(\operatorname{rew}(\Sigma), I_i)$ in the $i$-th step of this short-cut proof. This is because we cannot salvage atoms that are not facts (i.e. ones containing nulls) from branches steming from $I_i$. So on top of $I_i$, we are only going to add ***base facts*** that are derived from $I_i$ using $\Sigma$ (my guess is that this is in general not even a subset of $\operatorname{Sat}(\operatorname{rew}(\Sigma), I_i)$; is this true?). So we wrill write fact-saturated sets of $I_i$ with $\Sigma$ as $\operatorname{Sat}_{\mathrm{facts}}(\operatorname{rew}(\Sigma), I_i)$.

Also, by splitting the pseudoquery we can assume that a pseudoquery is realized in $I_n$ as oppsed to $\operatorname{Sat}_{\mathrm{facts}}(\operatorname{rew}(\Sigma), I_n)$, since if we are assuming all variables in an atom $F(\vec{t})$ to be realized in the squid head, we may treat $F(\vec{t})$ as a separate query (TODO: this is really hand-wavy!).

In fact we will have something like the following:

![[Pasted image 20221101171906.png]]

