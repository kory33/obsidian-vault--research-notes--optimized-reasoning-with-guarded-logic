---
title: Fresh Tentacle Theorem
tags:
  - notes
---

> This note builds on top of definitions in [[Chase-Like Trees and Saturated Chase-Like Trees]] and results in [[Preliminary Results on Saturated Chase-Like Trees]].

The aim of this note is to explain how the problem of deciding whether a query is witnessed inside a particular tentacle can be reduced to a query answering problem on a much smaller database.

## SatTree Translation Lemma

In this subsection, we aim to prove a simple "translation lemma" on $\SatTree$s.

First, we define what it means to apply a consts translation (see [[Logic Preliminaries#Factual translations]] for details) to the a chase-like tree and chase-paths.

> **Definition**. Let $T = (\Instance_T, (T_0, v_r))$ be a generic chase-like tree, and $\sigma: \Consts \rightarrow \Consts$ be a consts translation. The *$\sigma$-substituted chase-like tree $\sigma(T)$* is defined as the chase-like tree $(\sigma \circ \Instance_T, (T_0, v_r))$.
> 
> > *Remark*. $\sigma(\SatTree_\Sigma(I))$ in general does not equal $\SatTree_\Sigma(\sigma(I))$, since the former tree structure has $\Sigma$-valid generative chase-paths *for $I$* as nodes, while the latter tree has chase-paths for $\sigma(I)$. The goal of this subsection, however, is to show that these trees are "isomorphic via $\sigma$".

> **Definition**. Let $\vec{d} \in \ChaseStepDir^{< \omega}$ be a finite generic chase-path and $\sigma: \Consts \rightarrow \Consts$ a consts translation. The *$\sigma$-translation $\sigma(\vec{d})$ of a generic chase-path $\vec{d}$* is defined by induction on $\vec{d}$: $$
\begin{align}
  \sigma(()) &= () \\
  \sigma(\vec{d} \concat (\tau_p, \sigma_p)) &= \sigma(\vec{d}) \concat (\tau_p, \sigma_p \circ \sigma)
\end{align}
$$

To package preconditions of the transition lemma, we define the following notions:

> **Definition**. A consts translation $\sigma: \Consts \rightarrow \Consts$ is *$\Sigma$-invariant* if for each $t \in \FactualTerms$, if $t \in \consts(\Sigma)$ then $\sigma(t) = t$.

> **Definition**. Given an instance $I$ and a finite set $\Sigma$ of GTGDs, a factual translation $\sigma: \Consts \rightarrow \Consts$ is said to be *$(I \setminus \Sigma)$-exotic* if for each $t \in \Consts$ that appears in $I$ but not in $\Sigma$, $\sigma(t)$ does not appear in neither $I$ nor in $\Sigma$.

Now we have the following lemma.

> **Lemma (SatTree Translation)**. Let $\Sigma$ be a finite set of GTGDs and $I$ a base instance. If $\sigma: \Consts \rightarrow \Consts$ is a $\Sigma$-invariant $(I \setminus \Sigma)$-exotic consts translation, then
>   i. for each valid generative $\Sigma$-chase-path $\vec{d}$ on $I$, $\sigma(\vec{d})$ is a valid generative $\Sigma$-chase-path on $\sigma(I)$, and
>   ii. conversely, every valid generative $\Sigma$-chase-path $\vec{d'}$ on $\sigma(I)$, there exists a valid generative $\Sigma$-chase-path $\vec{d}$ on $I$ such that $\vec{d'} = \sigma(\vec{d})$. Moreover,
>   iii. $\sigma(\Instance_{\SatTree_\Sigma(I)}(\vec{d})) = \Instance_{\SatTree_\Sigma(\sigma(I))}(\sigma(\vec{d}))$.
> 
> > *Proof*.
> > 
> > (i): TODO
> > 
> > (ii): TODO
> > 
> > (iii): TODO
> > 

## Tentacle Relevance Theorem

> **Definition**. Let $((\tau, \sigma))$ be a valid generative $\Sigma$-chase-path on a base instance $I$.

(TODO: build up to the tentacle relevance theorem)