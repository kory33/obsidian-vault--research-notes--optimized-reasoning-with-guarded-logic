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

Now we define the property of a witness:

> **Definition**. Let $Q = \exists \vec{x}. \bigwedge_{j \in J} Q_j(\vec{x'}_j)$ be a BCQ, $\sigma$ a $(\Sigma, I)$-witness and $X \subseteq \elems(\vec{x})$. We say that *$\sigma$ sends the entire $X$ to a single tentacle* if there exists a tentacle $T$ of $\SatTree_\Sigma(I)$ such that $\Intro(\sigma(x)) \in T$ for every $x \in X$.

From this proposition, we can deduce the *witness decomposition*, as described in the following lemma:

> **Lemma (Witness Decomposition)**. Let $Q = \exists \vec{x}. \bigwedge_{j \in J} Q_j(\vec{x'}_j)$ be a BCQ, $\sigma$ a $(\Sigma, I)$-witness and $V$ a connected component $\mathcal{H}(Q - \touchDowners(\sigma))$. Then $\sigma$ sends the entire $V$ to a single tentacle. ^a87015
> 
> > *Proof*.
> > The previous proposition implies that, if two variables $x_1$ and $x_2$ are adjacent in $\mathcal{H}(Q - \touchDowners(\sigma))$, then in particular they lie in the same tentacle.
> > 
> > So take any two variables $x_1, x_2$ in $V \in \ConnComp(\mathcal{H}(Q - \touchDowners(\sigma)))$. By connectedness of $V$, there exists a path $x_1 E_0 y_0 \ldots y_{k-1} E_k x_2$ from $x_1$ to $x_2$. By induction on $k$, all of $y_0, \ldots, y_{k-1}$ lie in the same tentacle in which $x_1$ is introduced, so $x_1$ and $x_2$ are introduced in the same tentacle.

## Fragmented Witness Decomposition

The Witness Decomposition lemma shown above can be easily translated to the statement about fragmented witnesses using the Fragmentation-Gluing Bijection. We state this in the following theorem.

> **Theorem (Fragmented Witness Decomposition)**. Let $Q$ be a binary conjunctive query and $(\sigma_b, \set{\sigma'_V}_V)$ a $Q$-fragmented $(\Sigma, I)$-witness for $Q$. Then for each $V' \in \ConnComp(\mathcal{H}(Q - \domain(\sigma_b)))$, $\sigma'_{V'}: V' \rightarrow \Nulls$ sends the entire $V'$ a single tentacle.
> 
> > *Proof*. Let $\sigma = \Glue(\sigma_b, \set{\sigma'_V}_V)$ be the gluing of $(\sigma_b, \set{\sigma'_V}_V)$. By applying Witness Decomposition Lemma to $\sigma$, $\sigma$ sends the entire $V'$ to a single tentacle. Because $\sigma$ and $\sigma_{V'}$ agree on $V'$, $\sigma_V$ sends the entire $V'$ to a single tentacle.
