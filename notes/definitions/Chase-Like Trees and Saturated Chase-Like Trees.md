---
tag:
  - notes
  - definitions
---

> This note builds on [[Rewriting, Existential Lifting and Saturation]]

We shall define a tree structure that "stems from a base instance $I$ and witnesses every possible conclusion that can be $\Sigma$-deduced from $I$". To make this precise, we define a few concepts in this section. So fix a finite set $\Sigma$ of head-normal GTGDs.

We say that _a set $G$ of factual terms is $\Sigma$-guarded by a set of factual terms $\vec{t}$_ when $G \subseteq \consts(\Sigma) \cup \vec{t}$ .

Injective functions of the form $\nu: \mathbb{N} \rightarrow \Nulls$ will be referred to as *null-picking functions*. For a null-picking function $\nu$, a vector $\vec{y} = (y_1, \ldots, y_n)$ of variables and a factual substitution $\sigma$ whose domain is disjoint from $\vec{y}$, we define *the factual substitution $\sigma[\vec{y} \xrightarrow{\nu} \Nulls]$* with domain $\domain(\sigma) + \elems(\vec{y})$ that substitutes each $y_i$ to distinct nulls (chosen by $\nu$) and follows $\sigma$ elsewhere: $$
\sigma[\vec{y} \xrightarrow{\nu} \Nulls](x)=
\begin{cases}
    n_{\nu(i)} & \text{if $x = y_i$} \\
    \sigma(x) & \text{if $x \in \domain(\sigma)$}
\end{cases}$$

For a TGD $D = \forall \vec{x}. (\beta \rightarrow \exists \vec{y}. \eta)$, an instance $I$ and a factual substitution $\sigma$ that covers $\vec{x}$, we say that *$I$ can be $D$-chased with $\sigma$* when $\sigma(\beta) \subseteq I$. Intuitively, this means that the premise $\beta$ is witnessed by some facts in $I$, and $\sigma$ specifies which constant or null appearing in $I$ is witnessing each variable in $\vec{x}$.

We shall describe how an instance can be "extended" by applying a GTGD. (*Question: this is not a proper extension of $I$ because we are only taking along $\Sigma$-guarded facts to the "extension". Is there any intuition why we should we do this, or is this just a technical trick that is used to bound the size of tree-like chase proofs so as to make the decision procedure decidable? Will I get an insight about the intuition behind this limitation if I read the proof of chase-proof completeness?*) Given a null-picking function $\nu$, a GTGD $D = \forall \vec{x}. (\beta \rightarrow \exists \vec{y}. \eta)$ and an instance $I$ that can be $D$-chased with a factual substitution $\sigma$, we define
 - *the chase head $\chaseHead_\nu(D, \sigma)$* to be the fact $$\sigma[\vec{y} \xrightarrow{\nu} \Nulls](\eta).$$ Intuitively, this is a new fact generated from $I$ by applying the rule $D$.
 - *the one-step chase $\chase_\nu(I; D, \sigma)$ of $I$ with $(D, \sigma)$ (through $\nu$)* to be an instance defined by  $$\set{\chaseHead_\nu(D, \sigma)} \cup \set{\ F \in I\ |\ F \text{ is } \Sigma \text{-guarded by }\chaseHead_\nu(D, \sigma) \ }.$$

A *chase-like tree $T$ on an instance* is a directed rooted tree $(T_0, v_r)$ together with the *instance assignment* $\operatorname{Instance}_T: V(T_0) \rightarrow \Instances$ of instances to vertices.

For a chase-like tree $T$ with the instance assignment $\operatorname{Instance}_T$, we define the instance $\TreeFacts(T)$ as the union $\bigcup \mathrm{im} \operatorname{Instance}_T$ of image of the instance assignment.


We shall call a pair $(D, \sigma) \in \Sigma \times \FactualSubstitutions$ a *chase-step direction*, and write $\ChaseStepDir$ for the set $\Sigma \times \FactualSubstitutions$ of all chase-step directions. We call a finite (resp. infinite) sequence of chase-step directions a *finite (resp. infinite) chase-path*.

---
TODO: we also need to encode "the choice of facts that we take along $(D, \sigma)$ when applying the chase step", otherwise (I think) we can't quite argue about what we are trying to.

---

Fix a coding function (hence a computable injection into $\mathbb{N}$) $$\#: \ChaseStepDir^{< \omega} \times \mathbb{N} \rightarrow \mathbb{N}$$ on pairs of a finite chase-path and a natural. Precompose $\#$ to the canonical null-picking function $\nu_{\mathrm{id}}(i \in \mathbb{N}) = n_i$ and curry to obtain a $\ChaseStepDir^{< \omega}$-indexed family $\set{ \widehat{\#_\vec{d}}}_{\vec{d} \in \ChaseStepDir^{< \omega}}$ of null-picking functions: More explicitly, for each $\vec{d} \in \ChaseStepDir^{< \omega}$, we have $$
\begin{align}
\widehat{\#_{\vec{d}}}\ : \mathbb{N} & \rightarrow \Nulls\\
                                   i & \mapsto n_{\#(\vec{d}, i)}
\end{align}
$$
This family of null-picking functions will be used in the following definition to formally ensure that no null introduced in one branch is brought to its sibling branches.

Given a base instance $I$, define, by induction on finite chase-paths $\vec{d} \in \ChaseStepDir^{< \omega}$, the *canonical completion $\operatorname{CC}_\vec{d}(I)$ of $I$ along $\vec{d}$* by $$
\begin{align}
  \operatorname{CC}_{()}(I) &= \FullSat_\Sigma(I) \\
  \operatorname{CC}_{\vec{d} \concat (D, \sigma)}(I) &=
    \begin{cases}
      \FullSat_\Sigma(\chase_{\widehat{\#_{\vec{d}}}}(\operatorname{CC}_\vec{d}(I); D, \sigma)) & \text{if $\operatorname{CC}_\vec{d}(I)$ can be $D$-chased with $\sigma$} \\
      \emptyset & \text{otherwise}
    \end{cases}
\end{align}
$$
For a base instance $I$ and a finite chase-path $\vec{d}$, we say that $\vec{d}$ is *a valid chase-path on $I$* if either $\operatorname{CC}_\vec{d}(I) \neq \emptyset$ or both $I$ and $\vec{d}$ are empty.

Now define the *$\Sigma$-saturated chase-like tree $\SatTree_\Sigma(I)$ of a base instance $I$* with:
 - the set $(\ChaseStepDir^{< \omega})_{\mathrm{valid}}$ of *all* valid chase-paths on $I$ as the vertex set
 - (labelled) edges of the form $\vec{p} \xrightarrow{d} \vec{p} \concat (d)$ for each pair of vertices (hence valid chase-paths) $\vec{p}$ and $\vec{p} \concat (d)$
 - the instance assignment function defined by $$
\begin{array}{c c}
\operatorname{Instance}_{\SatTree_\Sigma(I)}:
  &(\ChaseStepDir^{< \omega})_{\mathrm{valid}} & \longrightarrow &\Instances \\
  &\vec{d} &\longmapsto &\operatorname{CC}_\vec{d}(I)
\end{array}
$$
