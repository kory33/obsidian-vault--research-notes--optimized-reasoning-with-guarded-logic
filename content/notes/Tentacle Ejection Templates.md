---
title: Tentacle Ejection Templates
tag:
  - notes
---

## Preliminaries

### In-place unifications

We shall first define what it means to identify (in-place) variables in a GTGD rule.

> **Definition**. Let $\vec{x}$ be a set of variables. An *in-place unification on $\vec{x}$* is a partition $\sim_\vec{x}$ of $\elems(\vec{x})$.

> **Example**. If $\vec{x} = (x_0, x_1, x_2, x_3)$, then an equivalence relation given by a partition $\set{\set{x_0}, \set{x_1, x_3}, \set{x_2}}$ is an in-place unification on $\vec{x}$.

## Tentacle Ejection Templates

We first describe an object that abstractly describe a situation where a tentacle hangs from some saturation of some base instance:

> **Definition**. Let $\Sigma$ be a finite set of GTGDs and $\tau = (\forall \vec{x}. \beta \rightarrow \exists \vec{y}. \eta) \in \Sigma$. A *$(\tau, \Sigma)$-export template* is a set $F$ of atomic formulae such that each $A \in F$
>   1. only mentions variables from $\elems(\vec{x})$ and constants from $\Sigma$, and
>   2. is guarded by some atom in $\eta$.

> **Definition**. Let $\Sigma$ be a finite set of GTGDs. A *$\Sigma$-tentacle ejection template* is a triple $(\tau, \sim_\tau, F_\tau)$ where $\tau = (\forall \vec{x}. \beta \rightarrow \exists \vec{y}. \eta) \in \Sigma$, $\sim_\tau$ is an in-place unification on $\vec{x}$ and $F_\tau$ is a $(\tau, \Sigma)$-export template.

Next, we define what is means to "instantiate" $\Sigma$-tentacle ejection templates.

> **Definition**. Let $\vec{x}$ be a set of variables and $\sim_\vec{x}$ an in-place unification on $\vec{x}$. A factual substitution $\sigma: \Vars \rightharpoonup \Consts$ is said to *conform to $\sim_\vec{x}$* if $\sigma$ covers exactly $\vec{x}$ and for each $x_1, x_2 \in \elems(\vec{x})$, and $$\sigma(x_1) = \sigma(x_2) \Longleftrightarrow x_1 \sim_\vec{x} x_2.$$ In other words, $\sigma$ covering exactly $\vec{x}$ conforms to $\sim_\vec{x}$ if and only if $\mathrm{ker}(\sigma) = \sim_\vec{x}$ where $\mathrm{ker}(\sigma)$ is the set-theoretic kernel of $\sigma$.
>
> > *Example*. If $\vec{x} = (x_0, x_1, x_2, x_3)$ and $\elems(\vec{x}) / \sim_\vec{x} = \set{\set{x_0}, \set{x_1, x_3}, \set{x_2}}$ as in the previous example, then a substitution $\sigma$ given by $$
\begin{array}{c c}
  \sigma: &\Vars &\rightharpoonup &\Consts \\
          &x_0 &\mapsto &c_3 \\
          &x_1 &\mapsto &c_6 \\
          &x_2 &\mapsto &c_2 \\
          &x_3 &\mapsto &c_6 \\
\end{array}
$$ conforms to $\sim_\vec{x}$.

> **Definition** Let $\Sigma$ be a finite set of GTGDs, and $T = (\tau, \sim_\tau, F_\tau)$ be a $\Sigma$-tentacle ejection template. Given a factual substitution $\sigma$ (TODO: we can assume that the image of $\sigma$ lies in $\Consts$) that conforms to $\sim_\tau$, the *$\Sigma$-instantiation $\Tentacle_\Sigma(T, \sigma)$ of $T$ with $\sigma$* is defined as the subtree of $\SatTree_\Sigma(\sigma(F_\tau))$ induced by the set of nodes in $\SatTree_\Sigma(\sigma(F_\tau))$ that either
>   1. is the root node, or
>   2. corresponds to a valid generative $\Sigma$-chase-path on $\sigma(F_\tau)$ and starts with $(\tau, \sigma)$.

> **Definition**. Let $\Sigma$ be a finite set of GTGDs, $I$ a base instance, $T = (\tau, \sim_\tau, F_\tau)$ a $\Sigma$-tentacle ejection template and $\sigma$ a factual substitution conforming to $\sim_\tau$. We say that *$T$ can be $\Sigma$-instantiated on $I$ using $\sigma$* if $\sigma(F_\tau) \subseteq \FullSat_\Sigma(I)$. If $T$ can be instantiated on $I$ using *some* factual substitution $\sigma$, we say that $T$ is applicable to $I$.

Not surprisingly, an instantiation of a $\Sigma$-tentacle ejection template embeds into the original SatTree, in the following sense:

> **Proposition (Ejection Embedding)**.
> Let $\Sigma$ be a finite set of GTGDs, $I$ a base instance and $T = (\tau, \sim_\tau, F_\tau)$ a $\Sigma$-tentacle ejection template that can be instantiated on $I$ using $\sigma$. Then for each node $\vec{d}$ in $\Tentacle_\Sigma(T, \sigma)$,
>  1. $\vec{d}$ is a valid generative $\Sigma$-chase-path on $I$, i.e. is a node in $\SatTree_\Sigma(I)$, and moreover,
>  2. $\Instance_{\Tentacle_\Sigma(T, \sigma)}(\vec{d}) \subseteq \Instance_{\SatTree_\Sigma(I)}(\vec{d})$
> 
> > *Proof*. Since $\Tentacle_\Sigma(T, \sigma)$ is a subtree of $\SatTree_\Sigma(\sigma(F_\tau))$, the proposition is obvious from the SatTree monotonicity.

### Tentacle Abstraction

We have just seen that the instantiation of a tentacle $(\tau, \sim_\tau, F_\tau)$ with a substitution $\sigma$ is a way of turning a tentacle ejection template into a chase-like tree that can be actually embeded to a tentacle hanging from $(\tau, \sigma)$.

We now describe a way to "abstract" an actual tentacle to a tentacle ejection template that can be instantiated back to the original tentacle.

> **Definition**. Let $(\tau, \sigma)$ be a valid generative $\Sigma$-chase-path on $I$. We define the *abstraction $\Abst_\Sigma(\tau, \sigma; I)$ of $(\tau, \sigma)$* to be the $\Sigma$-tentacle ejection template $(\tau, \sim_\sigma, F_{\Sigma, \tau, \sigma})$ where
>   - $\sim_\sigma$ is the relation given by $x_1 \sim_\sigma x_2 \Longleftrightarrow \sigma(x_1) = \sigma(x_2)$
>   - $F_{\Sigma, \tau, \sigma} =$ (TODO; this should be all the exports carried outside from $\FullSat(I)$, but we need constants "abstracted" to variables)

As promised, $\Abst_\Sigma(-, -; I)$ is a right inverse to $\Tentacle_\Sigma$:

> **Lemma (abstraction-instantiation)**. Let $T$ be the subtree of $\Tentacle_\Sigma(\Abst_\Sigma(\tau, \sigma; I), \sigma)$ induced by all non-root nodes. Then $T$ equals the tentacle of $\SatTree_\Sigma(I)$ hanging from $(\tau, \sigma)$.
> 
> > *Proof*. (TODO)

## Generic Proofs and Ejection Templates

Throughout this section, whenever we take a generic $\Sigma$-tentacle ejection template $T = (\tau = \forall \vec{x}. (\beta \rightarrow \exists \vec{y}. \eta) \in \Sigma, \sim_\tau, F_\tau)$ and a (not necessarily boolean) conjunctive query $Q = \exists \vec{z}. \bigwedge_{i \in I} A_i(\vec{w_i})$, by renaming bound variables we shall assume that $\vec{x}, \vec{y}$, $\vec{z}$ and $\operatorname{FV}(Q)$ are all disjoint to each other.

> **Definition**. For a set $\Sigma$ of finite GTGDs, a *$\Sigma$-generic constant assignment* is a computable function $\GenConst_\Sigma: \mathcal{P}_\mathrm{fin}(\Vars) \rightarrow \Consts$ such that $\mathrm{im}(\GenConst) \cap \consts(\Sigma) = \emptyset$.

> **Remark**. From now on, we shall assume that, for each $\Sigma$, we have decided a choice on a $\Sigma$-generic constant assignment $\GenConst_\Sigma$. We shall refer to this particular function as *the* $\Sigma$-generic constant assignment.

> **Definition**. Let $T = (\tau = \forall \vec{x}. (\beta \rightarrow \exists \vec{y}. \eta) \in \Sigma, \sim_\tau, F_\tau)$ be a $\Sigma$-tentacle ejection template. The *generic instance $\GenInst_\Sigma(T)$ associated with $T$* is the instance $$\GenInst_\Sigma(T) := \set{ \GenConst_\Sigma(F) \mid F \in F_\tau }.$$

> **Definition**. Let $T = (\tau = \forall \vec{x}. (\beta \rightarrow \exists \vec{y}. \eta) \in \Sigma, \sim_\tau, F_\tau)$ be a $\Sigma$-tentacle ejection template, and let $Q$ be a (*not necessarily boolean*) conjunctive query.  A *$T$-expectation on $Q$* is a map $\sigma: \operatorname{FV}(Q) \rightarrow {\sim}_\tau$.
> 
> > *Remark*. The reason we call such $\sigma$ an *expectation* is because we will later expect that the closure of $Q$ by $\sigma$ will be witnessed in a tentacle hanging from the generic instance associated with $T$. (TODO: I think this is a very bad way of naming a cocnept)

> **Definition**. Let $T = (\tau, \sim_\tau, F_\tau)$ be a $\Sigma$-tentacle ejection template, $Q = \exists \vec{z}. \bigwedge_{i \in I} A_i(\vec{w_i})$ a conjunctive query and $\sigma: \mathrm{FV}(Q) \rightarrow {\sim_\tau}$ a $T$-expectation on $Q$. The *$T$-generic closure of $Q$ by $\sigma$* is a boolean conjunctive query $\mathrm{cl}_\sigma(Q)$ given by $$\mathrm{cl}_\sigma(Q) = \exists \vec{z}. \bigwedge_{i \in I} A_i((\GenConst_\Sigma \circ \sigma)(\vec{w_i}))$$

> **Definition**. Let $T$ be a $\Sigma$-tentacle ejection template, $Q$ a conjunctive query and $\sigma_Q: \mathrm{FV}(Q) \rightarrow {\sim_\tau}$ a $T$-expectation on $Q$. We say that $(T, \sigma_Q)$ *generically proves* $Q$ when $\GenInst_\Sigma(T) \wedge \Sigma \models \mathrm{cl}_\sigma(Q)$.

(TODO: from here, within this note, prove that the query-rule rewriting that we described in [[Decomposing the Larger Problem into Smaller Subproblems]] is actually a query-rule rewriting)
