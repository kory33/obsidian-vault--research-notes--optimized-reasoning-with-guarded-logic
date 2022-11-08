---
title: Decomposing the Larger Problem into Smaller Subproblems
tags:
  - notes
  - idea
---

> We shall build on definitions given in [[Chase-Like Trees and Saturated Chase-Like Trees]].

We first make the following claim:

Claim 1(Completeness and Soundness of saturated chase-like trees). For any finite set of GTGDs $\Sigma$, a base instance $I$ and a conjunctive query $Q$, $$I \wedge \Sigma \models Q\Longleftrightarrow \TreeFacts(\SatTree_\Sigma(I)) \text{ witnesses } Q.$$
