---
title: Decomposing the Larger Problem into Smaller Subproblems
tags:
  - notes
  - idea
---

> We shall build on definitions given in [[Chase-Like Trees and Saturated Chase-Like Trees]]. We will also rely on the results in [[Preliminary Results on Saturated Chase-Like Trees]], [[Witness Fragmentation and Witness Gluing]] and [[Witness Decomposition]].

We start with the following claim, which we leave a detailed proof to some other part of the notes:

> **Claim 1 (Universality of $\SatTree$s)**. For any finite set of GTGDs $\Sigma$, a base instance $I$ and a binary conjunctive query $Q$, $I \wedge \Sigma \models Q$ if and only if there exists a $(\Sigma, I)$-witness for $Q$.

From now on we shall write `AnswerQuery(I, Σ, Q)` for the problem of deciding where $I \wedge \Sigma \models Q$ holds. We shall also consider the problem `WitnessedUnderTentacle(τ, σ, I, Σ, Q')`, which decides whether a binary conjunctive query `Q'` is witnessed on a tentacle of $\SatTree_\Sigma(I)$ hanging from $(\tau, \sigma)$.

Suppose for now that $Q$ is given in a form $\exists \vec{x}. \wedge_i Q_i(\vec{x'}_i)$, where $\vec{x'}_i \subseteq \vec{x}$ for each $i$.

By Claim 1, we can answer $I \wedge \Sigma \models Q$ by finding a witness $(\sigma, \SatTree_\Sigma(I))$ (or proving that none exists) for $Q$. Due to constraints on $\sigma$ as described in 
[[Preliminary Results on Saturated Chase-Like Trees#^a87015]]), we can nondeterministically guess $\consts(\sigma)$ and how $\sigma$ sends each connected component of $\mathcal{H}(Q - \consts(\sigma))$ to different tentacles, and then verify that our guess was right by using the oracle for `WitnessedUnderSubTree(-, -, -, -, -)`.

This yields a nondeterministic algorithm [^1], which we shall refer to as `AnswerQueryNonDet1`, that reduces `AnswerQuery(I, Σ, Q)` to instances of `WitnessedUnderSubTree(τ, σ, I, Σ, Q')`:

```
AnswerQueryNonDet1(I, Σ, Q):
  TODO
```

[^1]: In a sense of an algorithm running on nondeterministic turing machines, so `ACCEPT`s if *any* nondeterministic branch `ACCEPT`s, and `REJECT`s if *no* nondeterministic branch `ACCEPT`s.