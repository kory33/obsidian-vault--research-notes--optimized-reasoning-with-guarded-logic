---
title: Reducing Query-Rule-Rewriting Problem to BCQ Answerings
tags:
  - notes
  - idea
---

> We shall build on definitions given in [[Chase-Like Trees and Saturated Chase-Like Trees]]. We will also rely on the results in [[Preliminary Results on Saturated Chase-Like Trees]], and [[Witness Fragmentation and Witness Gluing]].

## Preliminaries

We first make precise the terms that will be useful in describing the algorithm.

> **Definition**. Given a boolean conjunctive query $\overline{Q} = \exists \vec{x}. \bigwedge_{j \in J} A_j(\vec{y'}_j)$ and a subset $V$,
>  - the *closure $\overline{V}$ of $V$ in $\overline{Q}$* is the set of variables given by $$
\overline{V} = \Set{ x \in \elems(\vec{x})\ \biggm\vert
\begin{array}{l}
  \text{ there are } j \in J \text{ and } x' \in \elems(\vec{x}) \\
  \text{ such that } \vec{y'_j} \text{ contains both $x$ and $x'$}
\end{array}
}
$$
>  - the *boundary $\partial V$ of $V$ in $\overline{Q}$* is the set of variables given by $$\partial V = \overline{V} \setminus V$$
>  - the *subquery $\overline{Q}_V$ of $\overline{Q}$ induced by $V$* is the conjunctive query $$\exists \vec{V}. \bigwedge_{j \in J_V} A_j(\vec{y'}_j)$$ where
> 	 - $\vec{V}$ is $V$ ordered into a sequence by the order of appearance in $\vec{x}$
> 	 - $J_V = \set{ j \in J \mid \vec{y'}_j \text{ only mentions variables from } \overline{V}}$
> 
> > *Remark*. The subquery $\overline{Q}_V$ of $\overline{Q}$ induced by $V$ is typically not boolean anymore, since $\mathrm{FV}(\overline{Q}_V) = \partial V$.

## The Basic Rewriting Algorithm

Now consider the following algorithm. Note that we make use of an oracle for BCQ answering over GTGD rules in Step `6-3-1-1`.

> **Definition** Define the procedure $\mathrm{QueryRuleRewrite1}(\Sigma, Q)$ as follows:
> 
> *Input*:
>   - $\Sigma$ a finite set of head-normal GTGDs
>   - $Q = \exists \vec{x}. \bigwedge_{j \in J} A_j(\vec{u}_j)$ a conjunctive query
>
> *Algorithm*:
>  1. Let $\Sigma_\mathrm{rew}$ be a Datalog rewriting of $\Sigma$.
>  2. Let `mut` $\Sigma' \leftarrow \emptyset$ be a variable holding new full TGD rules
>  3. Let $\vec{z} \leftarrow$ free variables of $Q$, in the order of quantification
>  4. Let $\overline{Q} = \exists \vec{z}. Q$
>  5. Let $\mathcal{H}(\overline{Q}) = (\mathcal{V}, \mathcal{E})$ be the query structure hypergraph of $\overline{Q}$
>  6. For each connected sub-hypergraph $C$ of vertices in $\mathcal{H}(\overline{Q})$, do:
>      1. Let $\partial C$ be the boundary of $C$ in $\overline{Q}$, and let $\mathrm{Subgoal_C}$ be a fresh $|\partial C|$-ary predicate symbol associated with $C$
>      2. Let $\overline{Q}_C$ be the subquery of $\overline{Q}$ induced by $C$
>      3. For each $\Sigma$-tentacle ejection template $T = (\tau = \forall \vec{x}. (\beta \rightarrow \exists \vec{y}. \eta) \in \Sigma, \sim_\tau, F_\tau)$, do:
>          1. For every possible $T$-closing map $\sigma: \partial C \rightarrow {\sim}_\tau$ on $\overline{Q}_C$ do:
>              1. If $(T, \sigma)$ generically $\Sigma$-proves $\overline{Q}_C$, then
>                  1. Let $\operatorname{remap}: {\sim_\tau} \rightarrow \Vars$ be any injection from $\sim_\tau$ to the set of variables (for instance, a choice function on $\sim_\tau$)
>                  2. Let $\mathrm{quotient}: (\bigcup {\sim_\tau}) \rightarrow {\sim_\tau}$ be the quotient map sending an element in $\bigcup {\sim_\tau}$ to its equivalence class under $\sim_\tau$
>                  3. Let $\vec{v}$ be the sequence of variables in $\operatorname{im} (\mathrm{remap} \circ \mathrm{quotient})$ (in some order)
>                  4. Add a full TGD rule $$\forall \vec{v}. (\mathrm{remap} \circ \mathrm{quotient})(\beta \wedge F_\tau) \rightarrow (\mathrm{remap} \circ \sigma)(\mathrm{Subgoal}_V(\vec{\partial C}))$$ to $\Sigma'$
>  7. Let $\mathrm{Goal}$ be a fresh $|\vec{z}|$-ary goal predicate
>  8. For each subset $V \supseteq \elems(\vec{z})$ of $\mathcal{V}$, do the following:
>      1. Let $\set{C_i}_{i \in I_V}$ be the set of connected components of $\mathcal{H}(\overline{Q}-V)$
>      2. Let $J_V = \set{ j \in J \mid \vec{u}_j \text{ only contains variables from } V}$
>      3. Add a full TGD rule $$\forall \vec{V}. \left(\bigwedge_{j \in J_V} A_j(\vec{u}_j)\right) \wedge \left(\bigwedge_{i \in I_V} \mathrm{Subgoal}_{C_i}(\partial C_i)\right) \rightarrow \mathrm{Goal}(\vec{z})$$ to $\Sigma'$
>  9. Return $(\Sigma_\mathrm{rew} \cup \Sigma', \mathrm{Goal})$

> **Theorem**. $\mathrm{QueryRuleRewrite1}(\Sigma, Q)$ is a query-rule-rewriting of $(\Sigma, Q)$.
> 
> > *Proof*. Fix $\Sigma$ and $Q = \exists \vec{q}. \bigwedge_{j \in J} A_j(\vec{u}_j)$ and let
> >  - $(\Sigma_\mathrm{qrr}, \mathrm{Goal}^Q) = \mathrm{QueryRuleRewrite1}(\Sigma, Q)$
> >  - $\vec{z} = \mathrm{FV}(Q)$
> >  - $\mathcal{H}(\overline{Q}) = (\mathcal{V}, \mathcal{E})$ be the query hypergraph of $\overline{Q} = \exists \vec{z}. Q$
> >
> > Take any base instance $I$ and a ground substitution $\sigma_\mathrm{sol}$ that covers exactly $\vec{z}$. We wish to see that $$I \wedge \Sigma \models \sigma_\mathrm{sol}(Q) \Longleftrightarrow I \wedge \Sigma_\mathrm{qrr} \models \sigma_\mathrm{sol}(\mathrm{Goal^Q}(\vec{z})) $$holds.
> > 
> > ($\Longrightarrow$, the "completeness" of the rewrite):
> > Suppose that $I \wedge \Sigma \models \sigma_\mathrm{sol}(Q)$. Then by the universality of $\SatTree_\Sigma$, the ground substitution $\sigma_\mathrm{sol}$ extends to the factual substitution $\sigma$ exactly covering $\vec{z} \concat \vec{q}$ such that $\set{\sigma(A_j(\vec{u}_j)) \mid j \in J} \subseteq \TreeFacts(\SatTree_\Sigma(I))$.
> > 
> > Let $V = \touchDowners(\sigma)$ be the touchdowners of $\sigma$. Since $\sigma \supseteq \sigma_\mathrm{sol}$, $V \supseteq \elems(\vec{z})$. Now let $\set{C_i}_{i \in I_V}$ be the set of connected components of $\mathcal{H}(\overline{Q}-V)$, and let $J_V = \set{ j \in J \mid \vec{u}_j \text{ only contains variables from } V}$. By the base-fact completeness of Datalog saturations, it suffices see that the rule $$\forall \vec{V}. \left(\bigwedge_{j \in J_V} A_j(\vec{u}_j)\right) \wedge \left(\bigwedge_{i \in I_V} \mathrm{Subgoal}_{C_i}(\partial C_i)\right) \rightarrow \mathrm{Goal}^Q(\vec{z})$$is applicable to $\FullSat_{\Sigma_\mathrm{qrr}}(I)$ with the ground substitution $\sigma \upharpoonright V$.
> > 
> > For each $j \in J_V$, $\sigma(A_j(\vec{u}_j))) \in \TreeFacts(\SatTree_\Sigma(I))$, but by choice of $j$, $\vec{u}_j$ only contains variables from $V$, so $\sigma(A_j(\vec{u}_j)))$ is a ground fact and therefore $\sigma(A_j(\vec{u}_j))) \in \FullSat_{\Sigma_\mathrm{qrr}}(I)$.
> > 
> > Take $i \in I_V$. It remains to see that $\sigma(\mathrm{Subgoal}_{C_i}(\partial C_i)) \in \FullSat_{\Sigma_\mathrm{qrr}}(I)$. (TODO: prove that a fragmentation of a witness induces the subgoal fact)
> > 
> > ($\Longleftarrow$, the "soundness" of the rewrite):
> > Suppose $I \wedge \Sigma_\mathrm{qrr} \models \sigma(\mathrm{Goal^Q}(\vec{z}))$. By construction of $\Sigma_\mathrm{qrr}$, there must be some subset $V \supseteq \elems(\vec{z})$ of $\mathcal{V}$ such that if we write
> >  - $\set{C_i}_{i \in I_V}$ for the set of connected components of $\mathcal{H}(\overline{Q}-V)$, and
> >  - $J_V$ for the set $\set{ j \in J \mid \vec{y'}_j \text{ only contains variables from } V}$,
> > 
> > then the substitution $\sigma_\mathrm{sol}$ can be extended to a ground substitution $\sigma_V$ that exactly covers $\vec{V}$ such that $$
\sigma_V \left(
  \set{A_j(\vec{y'}_j) \mid j \in J_V} \cup \set{\mathrm{Subgoal}_{C_i}(\partial C_i) \mid i \in I_V}
\right) \subseteq \FullSat_{\Sigma_\mathrm{qrr}}(I)
$$
> > holds, so that the base fact $\sigma(\mathrm{Goal^Q}(\vec{z}))$ is derived through the rule $$\forall \vec{V}. \left(\bigwedge_{j \in J_V} A_j(\vec{y'}_j)\right) \wedge \left(\bigwedge_{i \in I_V} \mathrm{Subgoal}_{C_i}(\partial C_i)\right) \rightarrow \mathrm{Goal}(\vec{z}).$$
> > Now for each $i \in I_V$, (TODO: show that the subquery induced by $C_i$ is witnessed, so that the whole witness can be reconstructed).
