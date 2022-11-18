---
title: Witness Decomposition
tags:
  - notes
---

> This note depends on [[Witness Fragmentation and Witness Gluing]]

In this note, we shall see how a $(\Sigma, I)$-witness for a BCQ must be constrained, and how that constraints maps to fragmented witnesses by the fragmentation-gluing bijeciton. 

## Witness Decomposition

First, we have the following proposition, which states that "vertices adjacent in $\mathcal{H}(Q - \touchDowners(\sigma))$ must be sent to nulls lying the same chase-path":

> **Proposition**. For a binary conjunctive query $Q = \exists \vec{x}. \bigwedge_{j \in J} Q_j(\vec{x'}_j)$ and a $(\Sigma, I)$-witness $\sigma$, if two variables $x_1$ and $x_2$ appear in a single atom $Q_j(\vec{x'}_j)$ for some $j \in J$, then $\Intro(\sigma(x_1))$ and $\Intro(\sigma(x_2))$ are $\leq$-comparable.
> 
> > *Proof*. By assumption on $\sigma$, there exists a node (i.e. a valid chase-path on $I$) $\vec{d}$ such that $Q_j(\sigma(\vec{x'}_j)) \in \Instance_{\SatTree_\Sigma(I)}(n)$. Since both $\SatTree_\Sigma(I) \upharpoonright \sigma(x_1)$ and $\SatTree_\Sigma(I) \upharpoonright \sigma(x_2)$ are rooted subtrees containing $n$, both $\Intro(\sigma(x_1))$ and $\Intro(\sigma(x_2))$ are ancestors of $n$, so all of $\set{ n, \Intro(\sigma(x_1)), \Intro(\sigma(x_2)) }$ lie on the same path in $\SatTree_\Sigma(I)$.

From this proposition, we can deduce the *witness decomposition*, as described in the following lemma:

> **Lemma (Witness Decomposition)**. For a binary conjunctive query $Q = \exists \vec{x}. \bigwedge_{j \in J} Q_j(\vec{x'}_j)$, a $(\Sigma, I)$-witness $\sigma$ and a connected component $V$ of $\mathcal{H}(Q - \touchDowners(\sigma))$, $\sigma$ sends variables in $V$ to nulls whose introduction points all lie in the same tentacle of $\SatTree_\Sigma(I)$. ^a87015
> 
> > *Proof*.
> > The previous proposition implies that, if two variables $x_1$ and $x_2$ are adjacent in $\mathcal{H}(Q - \touchDowners(\sigma))$, then in particular they lie in the same tentacle.
> > 
> > So take any two variables $x_1, x_2$ in $V \in \ConnComp(\mathcal{H}(Q - \touchDowners(\sigma)))$. By connectedness of $V$, there exists a path $x_1 E_0 y_0 \ldots y_{k-1} E_k x_2$ from $x_1$ to $x_2$. By induction on $k$, all of $y_0, \ldots, y_{k-1}$ lie in the same tentacle in which $x_1$ is introduced, so $x_1$ and $x_2$ are introduced in the same tentacle.

## Fragmented Witness Decomposition

*TODO: write how fragmented witnesses can be decomposed into tentacles.*