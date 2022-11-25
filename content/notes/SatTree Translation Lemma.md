---
title: SatTree Translation Lemma
---

> (TODO: write the dependency)

In this note, we aim to prove a simple "translation lemma" on $\SatTree$s.

First, we define what it means to apply a consts translation (see [[Logic Preliminaries#Factual translations]] for details) to the a chase-like tree and chase-paths.

> **Definition**. Let $T = (\Instance_T, (T_0, v_r))$ be a generic chase-like tree, and $\sigma: \Consts \rightarrow \Consts$ be a consts translation. The *$\sigma$-substituted chase-like tree $\sigma(T)$* is defined as the chase-like tree $(\sigma \circ \Instance_T, (T_0, v_r))$.
> 
> > *Remark*. $\sigma(\SatTree_\Sigma(I))$ in general does not equal $\SatTree_\Sigma(\sigma(I))$, since the former tree structure has valid generative $\Sigma$-chase-paths *for $I$* as nodes, while the latter tree has chase-paths for $\sigma(I)$. The goal of this note, however, is to show that these trees are "isomorphic via $\sigma$".

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

> **Lemma (SatTree Translation)**. Let $\Sigma$ be a finite set of GTGDs and $I$ a base instance. If $\sigma: \Consts \rightarrow \Consts$ is a $\Sigma$-invariant $(I \setminus \Sigma)$-exotic consts translation, then:
> 
>   1. for each valid generative $\Sigma$-chase-path $\vec{d}$ on $I$, $\sigma(\vec{d})$ is a valid generative $\Sigma$-chase-path on $\sigma(I)$, and
>   2. for each valid generative $\Sigma$-chase-path $\vec{d}$, $\sigma(\Instance_{\SatTree_\Sigma(I)}(\vec{d})) = \Instance_{\SatTree_\Sigma(\sigma(I))}(\sigma(\vec{d}))$.
> 
> > *Proof*.
> > 
> > We prove (1) and (2) simultaneously by induction on $\vec{d}$. (TODO)
> > 

We also have the "converse" to the SatTree translation, as described in the following corollary.

> **Corollary**. Let $\Sigma$ be a finite set of GTGDs and $I$ a base instance. If $\sigma: \Consts \rightarrow \Consts$ is a $\Sigma$-invariant $(I \setminus \Sigma)$-exotic consts translation. Then for every valid generative $\Sigma$-chase-path $\vec{d'}$ on $\sigma(I)$, there exists a valid generative $\Sigma$-chase-path $\vec{d}$ on $I$ such that $\vec{d'} = \sigma(\vec{d})$.
> 
> > *Proof*. We prove this by induction on $\vec{d'}$. The base case $\vec{d'} = () = \sigma(())$ is trivial.
> > 
> > For the inductive part, take a valid generative $\Sigma$-chase-path $\vec{d'} \concat (\tau_p, \sigma_p)$ on $\sigma(I)$. By the inductive hypothesis, there is a valid generative $\Sigma$-chase-path $\vec{d}$ on $I$ such that $\vec{d'} = \sigma(\vec{d})$. By the SatTree Translation Lemma, $$
\begin{align}
  \Instance_{\SatTree_\Sigma(\sigma(I))}(\vec{d'}) &=
  \Instance_{\SatTree_\Sigma(\sigma(I))}(\sigma(\vec{d})) \\
  &= \sigma(\Instance_{\SatTree_\Sigma(I)}(\vec{d'}))
\end{align}
$$ holds.
> > (TODO)
