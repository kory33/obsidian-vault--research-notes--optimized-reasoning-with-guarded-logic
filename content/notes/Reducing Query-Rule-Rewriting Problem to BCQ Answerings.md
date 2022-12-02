---
title: Reducing Query-Rule-Rewriting Problem to BCQ Answerings
tags:
  - notes
  - idea
---

> We shall build on definitions given in [[Chase-Like Trees and Saturated Chase-Like Trees]]. We will also rely on the results in [[Preliminary Results on Saturated Chase-Like Trees]], and [[Witness Fragmentation and Witness Gluing]].

> **Definition** Define the procedure $\mathrm{QueryRuleRewrite1}(\Sigma, Q)$ as follows:
> 
> *Input*:
>   - $\Sigma$ a finite set of head-normal GTGDs
>   - $Q = \exists \vec{x}. \bigwedge_{j \in J} A_j(\vec{y'}_j)$ a conjunctive query
>
> *Algorithm*:
>  1. Let $\Sigma_\mathrm{rew}$ be a Datalog rewriting of $\Sigma$.
>  2. Let `mut` $\Sigma' \leftarrow \emptyset$ be a variable holding new full TGD rules
>  3. Let $\vec{z} \leftarrow$ free variables of $Q$, in the order of quantification
>  4. Let $\overline{Q} = \exists \vec{z}. Q$
>  5. Let $\mathcal{H}(\overline{Q}) = (\mathcal{V}, \mathcal{E})$ be the query structure hypergraph of $\overline{Q}$
>  6. For each connected sub-hypergraph $C$ of vertices in $\mathcal{H}(\overline{Q})$, do:
> 	 1. Let $\partial C$ be the boundary of $C$ in $\overline{Q}$, and let $\mathrm{Subgoal_C}$ be a fresh $|\partial C|$-ary predicate symbol associated with $C$
> 	 2. Let $\exists \vec{C}. \overline{Q}_\overline{C}$ be the subquery of $\overline{Q}$ induced by $C$
> 	 3. For each $\Sigma$-tentacle ejection template $T = (\tau \in \Sigma, \sim_\tau, F_\tau)$, do:
> 		 1. For every possible $T$-generic constant mapping $\sigma: \partial C \rightarrow {\sim}_\tau$, do:
> 			 1. If $(T, \sigma)$ generically $\Sigma$-proves $\exists \vec{C}. \overline{Q}_\overline{C}$, then
> 				 1. Let $\operatorname{remap}: {\sim_\tau} \rightarrow \Vars$ be any injection from $\sim_\tau$ to the set of variables (for instance, a choice function on $\sim_\tau$)
> 				 2. Let $\mathrm{quotient}: (\bigcup {\sim_\tau}) \rightarrow {\sim_\tau}$ be the quotient map sending an element in $\bigcup {\sim_\tau}$ to its equivalence class under $\sim_\tau$
> 				 3. Add a full TGD rule $$(\mathrm{remap} \circ \mathrm{quotient})(F_\tau) \rightarrow (\mathrm{remap} \circ \sigma)(\mathrm{Subgoal}_V(\vec{\partial C}))$$ to $\Sigma'$
>  7. Let $\mathrm{Goal}$ be a fresh $|\vec{z}|$-ary goal predicate
>  8. For each subset $V \supseteq \elems(\vec{z})$ of $\mathcal{V}$, do the following:
> 	 1. Let $\set{C_i}_{i \in I_V}$ be the set of connected components of $\mathcal{H}(\overline{Q}-V)$
> 	 2. Let $J_V = \set{ j \in J \mid \vec{y'}_j \text{ only contains variables from } V}$
> 	 3. Add a full TGD rule $$(\bigwedge_{j \in J_V} A_j(\vec{y'}_j)) \wedge (\bigwedge_{C \in \set{C_i}_{i \in I_V}} \mathrm{Subgoal}_C(\partial C)) \rightarrow \mathrm{Goal}(\vec{z})$$ to $\Sigma'$
>  9. Return $(\Sigma_\mathrm{rew} \cup \Sigma', \mathrm{Goal})$

> **Theorem**. $\mathrm{QueryRuleRewrite1}(\Sigma, Q)$ is a query-rule-rewriting of $(\Sigma, Q)$.
> 
> > *Proof*. TODO
