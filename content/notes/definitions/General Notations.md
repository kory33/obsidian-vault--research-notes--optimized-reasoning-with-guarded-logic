---
title: General Notations
tag:
  - notes
  - definitions
---

> This section defines general notations used throughout the notes.

For a formal finite sequence $(X_1, \ldots, X_n)$ of same sorts, we abbriviate it as $\vec{X}$. The set $\set{\ X_1, \ldots, X_n\ }$ will then be denoted as $\elems(\vec{X})$. We write $\vec{X'} \triangleleft \vec{X}$ to mean that $\vec{X'}$ is an initial segment of $\vec{X}$, $\vec{X'} \leq \vec{X}$ to mean that $\vec{X'}$ is a subsequence of $\vec{X}$ and $X' \subseteq X$ to mean $\elems(\vec{X'}) \subseteq \elems(\vec{X})$.

For two formal finite sequences $\vec{X}$ and $\vec{Y}$, we denote by $\vec{X} \concat \vec{Y}$ the concatenation of $\vec{X}$ and $\vec{Y}$. For a nonempty (possibly infinite) sequence $(x) \concat \vec{X}$, we write $\head((x) \concat \vec{X})$ to mean the first element $x$ of the sequence.

A pair $(T, v_r)$ of a directed acyclic graph $T$ and a vertex $v_r \in V(T)$ is called a *directed tree rooted at $v_r$* if the underlying undirected graph of $T$ is a tree and every $v \in V(T) \setminus \set{v_r}$ has precisely one vertex $p_v \in V(T)$ such that there is an edge $(p_v, v) \in E(T)$. We shall often call $T$ a *rooted tree*.

For a directed tree $T$, we say that a node $u$ is a _descendant_ of $v$, written $u < v$, when there is a (directed) path from $v$ to $u$.

For a hypergraph $\mathcal{H} = (V, \mathcal{E})$, we write $\ConnComp(\mathcal{H})$ for the set of connected components (i.e. the quotient of $V$ under the smallest equivalence relation $\sim$ containing $x_1 \sim x_2$ for each $x_1, x_2$ such that there is a hyperedge $E \in \mathcal{E}$ that spans both $x_1$ and $x_2$).

We write $f: A \rightharpoonup B$ to mean that $f$ is a partial function from $A$ to $B$. We denote by $\domain(f)$ to mean the domain of $f$, and write $\isDefinedAt{f}{x}$ to mean that $x \in \domain(f) \subseteq A$, i.e. $f$ is defined at $x \in A$.