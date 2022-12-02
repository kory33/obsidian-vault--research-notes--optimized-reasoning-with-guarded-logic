---
title: Chase-Like Trees and Saturated Chase-Like Trees
tag:
  - notes
  - definitions
---

> This note builds on [[Saturations]]

We shall define a tree structure that "stems from a base instance $I$ and witnesses every possible conclusion that can be $\Sigma$-deduced from $I$". To make this idea precise, we define a few concepts.

## Some generic definitions 

> **Definition**. Let $\Sigma$ be a finite set of GTGDs. We say that _a set $G$ of factual terms is $\Sigma$-guarded by a set of factual terms $\vec{t}$_ when $G \subseteq \consts(\Sigma) \cup \vec{t}$ .

> **Definition**. Injective functions of the form $\nu: \mathbb{N} \rightarrow \Nulls$ will be referred to as *null-picking functions*.

> **Definition**. For a null-picking function $\nu$, a vector $\vec{y} = (y_1, \ldots, y_n)$ of variables and a factual substitution $\sigma$ whose domain is disjoint from $\vec{y}$, we define *the factual substitution $\sigma[\vec{y} \xrightarrow{\nu} \Nulls]$* with domain $\domain(\sigma) + \elems(\vec{y})$ that substitutes each $y_i$ to distinct nulls (chosen by $\nu$) and follows $\sigma$ elsewhere: $$
\sigma[\vec{y} \xrightarrow{\nu} \Nulls](x)=
\begin{cases}
    n_{\nu(i)} & \text{if $x = y_i$} \\
    \sigma(x) & \text{if $x \in \domain(\sigma)$}
\end{cases}$$

> **Definition**. For a TGD $\tau = \forall \vec{x}. (\beta \rightarrow \exists \vec{y}. \eta)$, an instance $I$ and a factual substitution $\sigma$ that covers $\vec{x}$, we say that *$I$ can be $\tau$-chased with $\sigma$* when $\sigma(\beta) \subseteq I$.

Intuitively, this means that the premise $\beta$ is witnessed by some facts in $I$, and $\sigma$ specifies which constant or null appearing in $I$ is witnessing each variable in $\vec{x}$.

We shall describe how an instance can be "extended" by applying a GTGD.

> **Definition**. Given a null-picking function $\nu$, a finite set $\Sigma$ of GTGDs, an element $\tau = \forall \vec{x}. (\beta \rightarrow \exists \vec{y}. \eta) \in \Sigma$ and an instance $I$ that can be $\tau$-chased with a factual substitution $\sigma$, we define:
>  - *the $(\tau, \sigma)$-chase head $\chaseHead_\nu(\tau, \sigma)$ (through $\nu$)* to be the set $$\chaseHead_\nu(\tau, \sigma) := \sigma[\vec{y} \xrightarrow{\nu} \Nulls](\eta).$$ of facts. 
>    Intuitively, this is a set of new facts generated from $I$ by applying the rule $\tau$ with $\sigma$.
>  - *the $\Sigma$-exports $\exports_\Sigma(I, (\tau, \sigma))$ from $I$ along $(\tau, \sigma)$* to be the set $$\exports_\Sigma(I, (\tau, \sigma)) := \set{\ F \in I\ |\ F \text{ is } \Sigma \text{-guarded by }\chaseHead_\nu(\tau, \sigma) \ }.$$
>  - *the one-step $\Sigma$-chase $\chase_{\Sigma, \nu}(I, (\tau, \sigma))$ of $I$ with $(\tau, \sigma)$ (through $\nu$)* to be an instance defined by  $$\chase_{\Sigma, \nu}(I, (\tau, \sigma)) := \chaseHead_\nu(\tau, \sigma) \cup \exports_\Sigma(I, (\tau, \sigma)).$$

### Chase-Like Trees

> **Definition**. A *chase-like tree $T$* is a directed rooted tree $(T_0, v_r)$ together with the *instance assignment* $\operatorname{Instance}_T: V(T_0) \rightarrow \Instances$ of instances to vertices.

> **Definition**. For a chase-like tree $T$ with the instance assignment $\operatorname{Instance}_T$, we define the instance $\TreeFacts(T)$ as the union $\bigcup \mathrm{im} \operatorname{Instance}_T$ of images of the instance assignment.

### The Canonical Global Null-Picking Function

> **Definition**. We write $\ChaseStepDir$ for the set $\GTGDFormulae \times \FactualSubstitutions$, and call a pair $(\tau, \sigma) \in \ChaseStepDir$ a *generic chase-step direction*. We call a finite (resp. infinite) sequence of generic chase-step directions a *finite (resp. infinite) generic chase-path*.

>**Definition**. We fix a coding function (hence a computable injection into $\mathbb{N}$) $$\#: \ChaseStepDir^{< \omega} \times \mathbb{N} \rightarrow \mathbb{N}$$ on pairs of a finite generic chase-path and a natural.

By precomposing $\#$ to the canonical null-picking function $\nu_{\mathrm{id}}(i \in \mathbb{N}) = n_i$ and currying, we obtain a $\ChaseStepDir^{< \omega}$-indexed family $\set{ \widehat{\#_\vec{d}}}_{\vec{d} \in \ChaseStepDir^{< \omega}}$ of null-picking functions. More explicitly, we have the following:

>**Definition**. For each $\vec{d} \in \ChaseStepDir^{< \omega}$, we define *the canonical null-picking function $\widehat{\#_{\vec{d}}}$ at $\vec{d}$* to be the function $$
\begin{align}
\widehat{\#_{\vec{d}}} : \mathbb{N} & \rightarrow \Nulls\\
                                   i & \mapsto n_{\#(\vec{d}, i)}
\end{align}
$$

This family of null-picking functions will be used in the following definition to formally ensure that no null introduced in one branch is brought to its sibling branches.

## Saturated Chase-Like Trees

Throughout this section, we shall fix some finite set $\Sigma$ of head-normal GTGDs.

From now on, we would like to work with specialized chase-step directions:

> **Definition**. We write $\ChaseStepDir_\Sigma$ for the set $\Sigma \times \FactualSubstitutions$, and call a pair $(\tau, \sigma) \in \Sigma \times \FactualSubstitutions$ a *$\Sigma$-chase-step direction*. We call a finite (resp. infinite) sequence of $\Sigma$-chase-step directions a *finite (resp. infinite) $\Sigma$-chase-path*.

> **Definition**. We say that a $\Sigma$-chase-step direction $(\tau, \sigma)$ is *generative* if $\tau$ is a non-full rule, and that a $\Sigma$-chase-path $\vec{d}$ is *generative* if each $(\tau, \sigma) \in \elems(\vec{d})$ is generative.

> **Definition**. Given a base instance $I$, define, by induction on finite chase-paths $\vec{d} \in \ChaseStepDir^{< \omega}$, the *shortcut $\Sigma$-chase $\operatorname{SC}_{\Sigma, \vec{d}}(I)$ of $I$ along $\vec{d}$* by $$
\begin{align}
  \operatorname{SC}_{\Sigma, ()}(I) &= \FullSat_\Sigma(I) \\
  \operatorname{SC}_{\Sigma, \vec{d} \concat (\tau, \sigma)}(I) &=
    \begin{cases}
      \FullSat_\Sigma(\chase_{\widehat{\#_{\vec{d}}}}(\operatorname{SC}_{\Sigma, \vec{d}}(I), (\tau, \sigma))) & \text{if $\operatorname{SC}_{\Sigma, \vec{d}}(I)$ can be $\tau$-chased with $\sigma$} \\
      \emptyset & \text{otherwise}
    \end{cases}
\end{align}
$$

> **Definition**. For a base instance $I$ and a finite chase-path $\vec{d}$, we say that $\vec{d}$ is *a valid $\Sigma$-chase-path on $I$* if either $\operatorname{SC}_{\Sigma, \vec{d}}(I) \neq \emptyset$ or both $I$ and $\vec{d}$ are empty.

> **Definition**. The *$\Sigma$-saturated chase-like tree $\SatTree_\Sigma(I)$ of a base instance $I$* is a chase-like tree with:
>  - the set $(\ChaseStepDir^{< \omega})_{\Sigma\mathrm{, valid, gen}}$ of *all* valid generative $\Sigma$-chase-paths on $I$ as the vertex set
>  - (labelled) edges of the form $\vec{p} \xrightarrow{d} \vec{p} \concat (d)$ for each pair of vertices (hence valid , generative $\Sigma$-chase-paths) $\vec{p}$ and $\vec{p} \concat (d)$
>  - the instance assignment function defined by $$
\begin{array}{c c}
\operatorname{Instance}_{\SatTree_\Sigma(I)}:
  &(\ChaseStepDir^{< \omega})_{\Sigma\mathrm{, valid, gen}} & \longrightarrow &\Instances \\
  &\vec{d} &\longmapsto &\operatorname{SC}_{\Sigma, \vec{d}}(I)
\end{array}
$$

> **Proposition (SatTree monotonicity)**. If $\Sigma$ is a finite set of GTGDs and $I \subseteq I'$ are base instances, then for each node $\vec{d}$ in $\SatTree_\Sigma(I)$,
>   1. $\vec{d}$ is also a node in $\SatTree_\Sigma(I')$, and moreover,
>   2. $\Instance_{\SatTree_\Sigma(I)}(\vec{d}) \subseteq \Instance_{\SatTree_\Sigma(I')}(\vec{d})$.
>
> > *Proof*. We show both of (1) and (2) simultaneously by induction on $\vec{d}$.
> > 
> > (Base case):
> >   1. Obvious.
> >   2. By saturation monotonicity.
> > (Inductive part):
> >  Let $\vec{d} \concat (\tau, \sigma)$ be a node in $\SatTree_\Sigma(I)$, hence a valid generative $\Sigma$-chase-path on $I$. Then $\vec{d}$ is a node in $\SatTree_\Sigma(I)$, so by inductive hypothesis, $\vec{d}$ is a valid generative $\Sigma$-chase-path on $I'$, and $\Instance_{\SatTree_\Sigma(I)}(\vec{d}) \subseteq \Instance_{\SatTree_\Sigma(I')}(\vec{d}))$. Then we have:
> >    1. Since $\vec{d} \concat (\tau, \sigma)$ is a valid $\Sigma$-chase-path on $I$, by definition of $\Instance_{\SatTree_\Sigma(I)}$, $\Instance_{\SatTree_\Sigma(I)}(\vec{d})$ can be $\tau$-chased with $\sigma$. So $\Instance_{\SatTree_\Sigma(I')}(\vec{d}) \supseteq \Instance_{\SatTree_\Sigma(I)}(\vec{d})$ can also be $\tau$-chased with $\sigma$, and $\vec{d} \concat (\tau, \sigma)$ is a valid $\Sigma$-chase-path on $I'$ as well. Moreover,
> >    2. as $\chase$ is clearly monotonic in its first argument, we have $$
\begin{align}
\Instance_{\SatTree_\Sigma(I)}(\vec{d} \concat (\tau, \sigma))
 &= \FullSat_\Sigma(\chase_{\widehat{\#_{\vec{d}}}}(\Instance_{\SatTree_\Sigma(I)}(\vec{d}), (\tau, \sigma))) \\
 &\subseteq \FullSat_\Sigma(\chase_{\widehat{\#_{\vec{d}}}}(\Instance_{\SatTree_\Sigma(I')}(\vec{d}), (\tau, \sigma))) \\
 &= \Instance_{\SatTree_\Sigma(I')}(\vec{d} \concat (\tau, \sigma)).
\end{align}
$$

We will often deal with witnesses of the form $(\sigma, \TreeFacts(\SatTree_\Sigma(I)))$. This motivates a distinguished name for such witnesses:

> **Definition**. For a BCQ $Q$, we say that a factual substitution $\sigma$ is *a $(\Sigma, I)$-witness for $Q$* when $(\sigma, \TreeFacts(\SatTree_\Sigma(I)))$ is a witness for $Q$.

