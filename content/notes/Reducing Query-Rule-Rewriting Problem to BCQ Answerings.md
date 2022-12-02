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
>  6. For each connected sub-hypergraph $V$ of vertices in $\mathcal{H}(\overline{Q})$, do:
> 	 1. Let $\partial V$ be the boundary of $V$ in $\overline{Q}$, and let $\mathrm{Subgoal_V}$ be a fresh $|\partial V|$-ary predicate symbol associated with $V$
> 	 2. Let $\exists \vec{V}. \overline{Q}_\overline{V}$ be the subquery of $\overline{Q}$ induced by $V$
> 	 3. For each $\Sigma$-tentacle ejection template $T = (\tau \in \Sigma, \sim_\tau, F_\tau)$, do:
> 		 1. For every possible $T$-generic constant mapping $\sigma: \partial V \rightarrow {\sim}_\tau$, do:
> 			 1. If $(T, \sigma)$ generically $\Sigma$-proves $\exists \vec{V}. \overline{Q}_\overline{V}$, then
> 				 1. Add a full TGD rule $$F_\tau \rightarrow \mathrm{Subgoal}_V(\partial V)$$ to $\Sigma'$
> 				    (TODO: We should have $F_\tau$ substituted with something else here!)
>  7. Let $\mathrm{Goal}$ be a fresh $|\vec{z}|$-ary goal predicate
>  8. For each subset $V \supseteq \elems(\vec{z})$ of $\mathcal{V}$, do the following:
> 	 1. Let $\set{C_i}_{i \in I_V}$ be the set of connected components of $\mathcal{H}(\overline{Q}-V)$
> 	 2. Let $J_V = \set{ j \in J \mid \vec{y'}_j \text{ only contains variables from } V}$
> 	 3. Add a full TGD rule $$(\bigwedge_{j \in J_V} A_j(\vec{y'}_j)) \wedge (\bigwedge_{i \in I_V} \mathrm{Subgoal}_{C_i}(\partial C_i)) \rightarrow \mathrm{Goal}(\vec{z})$$ to $\Sigma'$
>  9. Return $(\Sigma_\mathrm{rew} \cup \Sigma', \mathrm{Goal})$

> **Theorem**. $\mathrm{QueryRuleRewrite1}(\Sigma, Q)$ is a query-rule-rewriting of $(\Sigma, Q)$.
> 
> > *Proof*. TODO
