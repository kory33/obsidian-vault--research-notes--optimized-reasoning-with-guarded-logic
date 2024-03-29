---
title: Reducing Query-Rule-Rewriting Problem to BCQ Answerings
tags:
  - notes
  - idea
---

> We shall build on definitions given in [[Chase-Like Trees and Saturated Chase-Like Trees]]. We will also rely on the results in [[Preliminary Results on Saturated Chase-Like Trees]], and [[Witness Fragmentation and Witness Gluing]].

## Preliminaries

We first make precise the terms that will be useful in describing the algorithm.

> **Definition**. Given a boolean conjunctive query $\overline{Q} = \exists \vec{x}. \bigwedge_{j \in J} A_j(\vec{u}_j)$ and a subset $V$ of $\elems(\vec{x})$,
>  - the *closure $\overline{V}$ of $V$ in $\overline{Q}$* is the set of variables given by $$
\overline{V} = \Set{ x \in \elems(\vec{x})\ \biggm\vert
\begin{array}{c}
  \text{ there are } j \in J \text{ and } x' \in V \text{ such that} \\
  \vec{u_j} \text{ contains both $x$ and $x'$}
\end{array}
}
$$
>  - the *boundary $\partial V$ of $V$ in $\overline{Q}$* is the set of variables given by $$\partial V = \overline{V} \setminus V$$
>  - the *subquery $\overline{Q}_V$ of $\overline{Q}$ induced by $V$* is the conjunctive query $$\exists \vec{V}. \bigwedge_{j \in J_\overline{V}} A_j(\vec{u}_j)$$ where
> 	 - $\vec{V}$ is $V$ ordered into a sequence by the order of appearance in $\vec{x}$
> 	 - $J_\overline{V} = \set{ j \in J \mid \vec{u}_j \text{ only mentions variables from } \overline{V}}$
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
>          1. For every possible $T$-closing map $\gamma: \partial C \rightarrow {\sim}_\tau \cup \consts(\Sigma)$ on $\overline{Q}_C$ do:
>              1. If $(T, \gamma)$ generically $\Sigma$-proves $\overline{Q}_C$, then
>                  1. Let $\operatorname{remap}: {\sim_\tau} \rightarrow \Vars$ be any injection from $\sim_\tau$ to the set of variables (for instance, a choice function on $\sim_\tau$)
>                  2. Let $\mathrm{quotient}: (\bigcup {\sim_\tau}) \rightarrow {\sim_\tau}$ be the quotient map sending an element in $\bigcup {\sim_\tau}$ to its equivalence class under $\sim_\tau$
>                  3. Let $\vec{v}$ be the sequence of variables in $\operatorname{im} (\mathrm{remap} \circ \mathrm{quotient})$ (in some order)
>                  4. Add a full TGD rule $$\forall \vec{v}. (\mathrm{remap} \circ \mathrm{quotient})(\beta \wedge F_\tau) \rightarrow (\mathrm{remap} \circ \gamma)(\mathrm{Subgoal}_C(\vec{\partial C}))$$ to $\Sigma'$
>  7. Let $\mathrm{Goal}$ be a fresh $|\vec{z}|$-ary goal predicate
>  8. For each subset $V \supseteq \elems(\vec{z})$ of $\mathcal{V}$, do the following:
>      1. Let $\set{C_i}_{i \in I_V}$ be the set of connected components of $\mathcal{H}(\overline{Q}-V)$
>      2. Let $J_V = \set{ j \in J \mid \vec{u}_j \text{ only contains variables from } V}$
>      3. Add a full TGD rule $$\forall \vec{V}. \left(\bigwedge_{j \in J_V} A_j(\vec{u}_j)\right) \wedge \left(\bigwedge_{i \in I_V} \mathrm{Subgoal}_{C_i}(\partial C_i)\right) \rightarrow \mathrm{Goal}(\vec{z})$$ to $\Sigma'$
>  9. Return $(\Sigma_\mathrm{rew} \cup \Sigma', \mathrm{Goal})$

The $\mathrm{Subgoal}_C$ predicate essentially captures the fulfilment of the subquery, with variables in $C$ being witnessed by nulls and variables in $\partial C$ being witnessed by constants in the base instance. To make this idea precise, we prove the following lemma, which also turns out to be useful for the correctness proof of the $\mathrm{QueryRuleRewrite1}$ algorithm.

> **Lemma (Subquery-Subgoal Correspondence)**. Let $\Sigma$ be a finite set of GTDGs, $Q = \exists \vec{q}. \bigwedge_{j \in J} A_j(\vec{u}_j)$ a conjunctive query and $I$ a ground instance. 
> 
> Write
>  - $(\Sigma_\mathrm{qrr}, \mathrm{Goal}^Q) = \mathrm{QueryRuleRewrite1}(\Sigma, Q)$,
>  - $\vec{z} = \mathrm{FV}(Q)$ and $\overline{Q} = \exists \vec{z}. Q$, and
>  - $\mathcal{H}(\overline{Q}) = (\mathcal{V}, \mathcal{E})$ for the query hypergraph of $\overline{Q}$.
>
> Take any connected sub-hypergraph $C$ of $\mathcal{H}(\overline{Q})$, and let $\overline{Q}_C = \exists \vec{C}. \bigwedge_{j \in J_\overline{C}} A_j(\vec{u}_j)$ be the subquery of $\overline{Q}$ induced by $C$. Then the following implications hold.
> 
>  1. If $\sigma_\overline{C}$ is a factual substitution that exactly covers $\overline{C}$ with $\touchDowners(\sigma_\overline{C}) = \partial C$, then $$
\sigma_\overline{C} \left(
  \bigwedge_{j \in J_\overline{C}} A_j(\vec{u}_j)      
\right) \in \TreeFacts(\SatTree_\Sigma(I))
  \Longrightarrow
    I \wedge \Sigma_\mathrm{qrr} \models \sigma_\overline{C}(\mathrm{Subgoal}_C(\vec{\partial C})).
$$
>  2. If $\sigma_{\partial C}$ is a ground substitution that covers exactly $\partial C$, then $$
I \wedge \Sigma_\mathrm{qrr}
  \models
    \sigma_{\partial C}(
      \mathrm{Subgoal}_C(\vec{\partial C})
    )
  \Longrightarrow
I \wedge \Sigma
    \models
      \sigma_{\partial C}(\overline{Q}_C)
$$
> 
> > *Proof of (1)*. Suppose that $\sigma_\overline{C}$ is a factual substitution that exactly covers $\overline{C}$ with $\touchDowners(\sigma_\overline{C}) = \partial C$. Suppose further that $$
\sigma_\overline{C}\left(
  \bigwedge_{j \in J_\overline{C}} A_j(\vec{u}_j)
\right) \in \TreeFacts(\SatTree_\Sigma(I))$$holds.
> >
> > Then all of $\overline{C} \setminus \partial C = C$ are mapped to nulls by $\sigma_\overline{C}$ , and by connectedness of $C$ and the definition of $J_\overline{C}$ , there exists some valid generative path $(\tau = \forall \vec{x}. \beta \rightarrow \exists \vec{y}. \eta, \sigma)$ such that all nulls in $\sigma_\overline{C}[C]$ are introduced within the tentacle hanging from $(\tau, \sigma)$ (TODO: write this fact as a lemma somewhere: this follows from the witness decomposition).
> > 
> > 
> > For a variable $w \in \partial C$ such that $\sigma_\overline{C}(w) \in \consts(\Sigma)$, set $\gamma_\sigma(w) = \sigma_\overline{C}(w)$. Otherwise, if $w \in \partial C$ has $\sigma_\overline{C}(w) \not\in \consts(\Sigma)$, then as $\sigma_\overline{C}\left(\bigwedge_{j \in J_\overline{C}} A_j(\vec{u}_j)\right)$ contains a fact that mentions both $\sigma_\overline{C}(w)$ and a null occuring in $\Tentacle_\Sigma(T, \sigma)$, $\sigma$ must send some variable $\tilde{w} \in \vec{x}$ to $\sigma_\overline{C}(w)$ (TODO: We might want to make this argument a bit more precise. The reasoning is informally as follows: as there is no way $\sigma_\overline{C}(w)$ can be introduced during the chase process (since $\sigma_\overline{C}(w)$ does not appear in $\Sigma$), $\sigma_\overline{C}(w)$ must be mentioned in one of exported facts at the root of the tentacle). So choose such $\tilde{w}$ for each $w \in \partial C$ with $\sigma_\overline{C}(w) \not \in \consts(\Sigma)$, and set $\gamma_\sigma(w) = [\tilde{w}]_{\sim_T}$ for all such $w$.
> >
> > We make the following claim:
> >
> > > **Claim 1**. $(T, \gamma_\sigma)$ generically proves $\overline{Q}_C$.
> > > 
> > > *Proof*. We need to prove that $(\GenConst_\Sigma \circ \mathrm{quotient}_{\sim_T})(F_T \wedge \beta) \wedge \Sigma \models (\mathrm{GenConst}_\Sigma \circ \gamma_\sigma)(\overline{Q}_C)$.
> > > 
> > > By the assumption on $\sigma$ and $\sigma_\overline{C}$, we have $\sigma(F_T \wedge \beta) \wedge \Sigma \models \sigma_\overline{C}(\overline{Q}_C)$. As $\mathrm{ker}(\sigma) = {\sim}_T$, $\sigma$ factors through the quotient map and an injection, i.e. there is an injective map $\phi: {\sim}_T \rightarrow \Consts$ such that $\sigma = \phi \circ \mathrm{quotient}_{{\sim}_T}$. 
> > > 
> > > **If $\consts(\Sigma)$ is empty,** then for any $w \in \partial C$,  $(\phi^{-1} \circ \sigma_\overline{C})(w) = \gamma_\sigma(w)$ by the construction of $\gamma_\sigma$.
> > > 
> > > (TODO: Unfortunately, we do not have $\phi^{-1} \circ \sigma_\overline{C} = \gamma_\sigma$ when $\Sigma$ contains constants. For such cases to work, we need to include the data of "which equivalence classes are mapped to which elements in $\consts(\Sigma)$", likely in a form of partial function $\sigma_T \rightharpoonup \consts(\Sigma)$.)
> > > 
> > > So $\phi^{-1} \circ \sigma_\overline{C} = \gamma_\sigma$, and as $\mathrm{GenConst}_\Sigma \circ \phi^{-1}$ is a $\consts(\Sigma)$-fixing consts translation, $(\mathrm{GenConst}_\Sigma \circ \phi^{-1} \circ \sigma)(F_T \wedge \beta) \wedge \Sigma = (\GenConst_\Sigma \circ \mathrm{quotient}_{\sim_T})(F_T \wedge \beta) \wedge \Sigma$ entails $(\mathrm{GenConst}_\Sigma \circ \phi^{-1} \circ \sigma_\overline{C}) = (\mathrm{GenConst}_\Sigma \circ \gamma_\sigma)$.
> >
> > Now that Claim 1 has been established, $\Sigma_\mathrm{qrr}$ contains a rule $$\tau_\mathrm{Subgoal} = \forall \vec{v}. (\mathrm{remap} \circ \mathrm{quotient})(\beta \wedge F_T) \rightarrow (\mathrm{remap} \circ \gamma_\sigma)(\mathrm{Subgoal}_C(\vec{\partial C})).$$for some remapping function $\mathrm{remap}: {\sim_T} \rightarrow \Vars$ and some ordering $\vec{v}$ of variables in $(\mathrm{remap} \circ \mathrm{quotient})(\beta \wedge F_T)$.
> > 
> > We now wish to set up a substitution $\sigma_\vec{v}$ exactly covering $\vec{v}$ such that $\FullSat(I)$ can be $\tau_\mathrm{Subgoal}$-chased with $\sigma_\vec{v}$ and $\sigma_\vec{v}((\mathrm{remap} \circ \gamma_\sigma)(\mathrm{Subgoal}_C(\vec{\partial C}))) = \sigma_\overline{C}(\mathrm{Subgoal}_C(\vec{\partial C}))$. Pick a retraction $\mathrm{remap}^{-1}$ of $\mathrm{remap}$ and a section $\mathrm{quotient}^{-1}$ of $\mathrm{quotient}$. Now let $\sigma_\vec{v} = \sigma \circ \mathrm{quotient}^{-1} \circ \mathrm{remap}^{-1}$.
> > 
> > Then $\sigma_\vec{v}((\mathrm{remap} \circ \mathrm{quotient})(\beta \wedge F_T)) = \sigma(\beta \wedge F_T)$. Since $T$ is an abstraction of $(\tau, \sigma)$, we have $\sigma(\beta \wedge F_T) \in \FullSat(I)$, so $\FullSat(I)$ can be $\tau_\mathrm{Subgoal}$-chased with $\sigma_\vec{v}$.
> > 
> > To check the remaining equality, pick any $w \in \partial C$. If $\sigma_\overline{C}(w) \in \consts(\Sigma)$, then $$
\begin{align}
  \sigma_\vec{v}(\mathrm{remap}(\gamma_\sigma(w)))
    &= \sigma_\vec{v}(\mathrm{remap}(\sigma_\overline{C}(w))) \\
    &= \sigma_\vec{v}(\sigma_\overline{C}(w)) \\
    &= \sigma_\overline{C}(w) \\
\end{align}
$$ as $\sigma_\overline{C}(w)$ is just a constant. On the other hand, if $\sigma_\overline{C}(w) \not \in \consts(\Sigma)$, then $$
\begin{align}
  \sigma_\vec{v}(\mathrm{remap}(\gamma_\sigma(w)))
    &= \sigma_\vec{v}(\mathrm{remap}([\tilde{w}]_{\sim_T})) \\
    &= (\sigma \circ \mathrm{quotient}^{-1} \circ \mathrm{remap}^{-1})(\mathrm{remap}([\tilde{w}]_{\sim_T})) \\
    &= (\sigma \circ \mathrm{quotient}^{-1})([\tilde{w}]_{\sim_T}) \\
    &= \sigma(\tilde{w}) \\
    &= \sigma_\overline{C}(w),
\end{align}
$$where the second last equality is due to $\sigma$ conforming to $\sim_T$, and the last equality follows from the choice of $\tilde{w}$.
> > 
> > From these calculations we have $\sigma_\vec{v}((\mathrm{remap} \circ \gamma_\sigma)(\mathrm{Subgoal}_C(\vec{\partial C}))) = \sigma_\overline{C}(\mathrm{Subgoal}_C(\vec{\partial C}))$. Therefore $\tau_\mathrm{Subgoal}$-chasing $\FullSat(I)$ with $\sigma_\vec{v}$ indeed yields $\sigma_\overline{C}(\mathrm{Subgoal}_C(\vec{\partial C}))$. We conclude that $I \wedge \Sigma_\mathrm{qrr} \models \sigma_\overline{C}(\mathrm{Subgoal}_C(\vec{\partial C}))$.
>
> > *Proof of (2)*. Suppose that $\sigma_{\partial C}$ is a ground substitution that covers exactly $\partial C$. Suppose further that $$
I \wedge \Sigma_\mathrm{qrr}
  \models
    \sigma_{\partial C}(
      \mathrm{Subgoal}_C(\vec{\partial C})
    )$$holds. By construction of $\Sigma_\mathrm{qrr}$, there must be some
> >     - $\Sigma$-ejection template $T = (\tau_T = \forall \vec{x}. (\beta \rightarrow \exists \vec{y}. \eta) \in \Sigma, \sim_T, F_T)$,
> >     - a $T$-closing map $\gamma_T: \partial C \rightarrow {\sim_T} \cup \consts(\Sigma)$,
> >     - an injection $\mathrm{remap}: {\sim}_T \rightarrow \Vars$ and
> >     - a substitution $\sigma_\vec{v}$ that exactly covers $\vec{v} = \operatorname{im} (\mathrm{remap} \circ \mathrm{quotient})$
> >
> > such that $(T, \gamma_T)$ generically proves $\overline{Q}_C$ and $$
\begin{align}
(
  \sigma_\vec{v}
    \circ \mathrm{remap}
    \circ \mathrm{quotient}
)(\beta \wedge F_T)
  &\subseteq
    \FullSat_{\Sigma_\mathrm{qrr}}(I), \\
(
  \sigma_\vec{v}
    \circ \mathrm{remap}
    \circ \gamma_T
)(\mathrm{Subgoal}_C(\vec{\partial C}))
 &=
   \sigma_{\partial C}(\mathrm{Subgoal}_C(\vec{\partial C})).
\end{align}
$$
> >
> > Let $\phi: {\sim}_T \rightarrow \Consts$ be the map defined by $\sigma_\vec{v} \circ \mathrm{remap}$. Since $(\phi \circ \mathrm{quotient})(\beta \wedge F_T) \subseteq \FullSat_{\Sigma_\mathrm{qrr}}(I)$, and as $\Sigma_\mathrm{qrr}$ is a conservative extenstion of $\Sigma$ (where we consider $\mathrm{Subgoal}_C$-s and $\mathrm{Goal}$ as newly introduced predicate symbols) by construction of $\Sigma_\mathrm{qrr}$, $(\phi \circ \mathrm{quotient})(\beta \wedge F_T) \subseteq \FullSat_{\Sigma}(I)$. As $(\phi \circ \mathrm{quotient})(\beta)$ is a set of base facts, $I \wedge \Sigma \models (\phi \circ \mathrm{quotient})(\beta \wedge F_T)$.
> >
> > Now, by the application of Genericity of Generic Proofs to $(T, \gamma_T)$ and $\phi$, $(\phi \circ \mathrm{quotient})(\beta \wedge F_T) \models (\phi \circ \gamma_T)(\overline{Q}_C)$. As $(\sigma_\vec{v} \circ \mathrm{remap} \circ \gamma_T)(\mathrm{Subgoal}_C(\vec{\partial C})) = \sigma_{\partial C}(\mathrm{Subgoal}_C(\vec{\partial C}))$, we have $(\sigma_\vec{v} \circ \mathrm{remap} \circ \gamma_T) = \sigma_{\partial C}$. Therefore $$
\begin{align}
  (\phi \circ \gamma_T)(\overline{Q}_C)
    &= (\sigma_\vec{v} \circ \mathrm{remap} \circ \gamma_T)(\overline{Q}_C) \\
    &= \sigma_{\partial C}(\overline{Q}_C),
\end{align}
$$and hence $(\phi \circ \mathrm{quotient})(\beta \wedge F_T) \models \sigma_{\partial C}(\overline{Q}_C)$.
> >
> > By transitivity of the $\models$ relation, we conclude that $I \wedge \Sigma \models \sigma_{\partial C}(\overline{Q}_C)$.

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
> > Let $V = \touchDowners(\sigma)$ be the touchdowners of $\sigma$. Since $\sigma \supseteq \sigma_\mathrm{sol}$, and $\touchDowners(\sigma_\mathrm{sol}) = \elems(z)$, $V \supseteq \elems(\vec{z})$. Now let $\set{C_i}_{i \in I_V}$ be the set of connected components of $\mathcal{H}(\overline{Q}-V)$, and let $J_V = \set{ j \in J \mid \vec{u}_j \text{ only contains variables from } V}$. By the base-fact completeness of Datalog saturations, it suffices see that the rule $$\forall \vec{V}. \left(\bigwedge_{j \in J_V} A_j(\vec{u}_j)\right) \wedge \left(\bigwedge_{i \in I_V} \mathrm{Subgoal}_{C_i}(\partial C_i)\right) \rightarrow \mathrm{Goal}^Q(\vec{z})$$is applicable to $\FullSat_{\Sigma_\mathrm{qrr}}(I)$ with the ground substitution $\sigma \upharpoonright V$.
> > 
> > For each $j \in J_V$, $\vec{u}_j$ only contains variables from $V$, so $\sigma(A_j(\vec{u}_j)))$ is a ground fact. Since $\sigma(A_j(\vec{u}_j))) \in \TreeFacts(\SatTree_\Sigma(I))$ and $\Sigma_\mathrm{qrr}$ contains a Datalog rewriting of $\Sigma$, we have $\sigma(A_j(\vec{u}_j))) \in \TreeFacts(\SatTree_{\Sigma_\mathrm{qrr}}(I))$. As $\sigma(A_j(\vec{u}_j)))$ is a ground fact, $\sigma(A_j(\vec{u}_j))) \in \FullSat_{\Sigma_\mathrm{qrr}}(I)$.
> > 
> > Take $i \in I_V$. It remains to see that $\sigma(\mathrm{Subgoal}_{C_i}(\partial C_i)) \in \FullSat_{\Sigma_\mathrm{qrr}}(I)$. Since $V \cap \overline{C_i} = \partial C_i$, $(\sigma \upharpoonright \overline{C_i})$ exactly covers $\overline{C_i}$ while $\touchDowners(\sigma \upharpoonright \overline{C_i}) = \partial C_i$. Since $$
\sigma\left(\bigwedge_{j \in J} A_j(\vec{u}_j) \right)
  \in \TreeFacts(\SatTree_\Sigma(I)),
$$and $J_\overline{C_i} \subseteq J$, *a fortiori* $$
(\sigma \upharpoonright \overline{C_i})\left(\bigwedge_{j \in J_\overline{C_i}} A_j(\vec{u}_j) \right)
  \in \TreeFacts(\SatTree_\Sigma(I)).
$$Therefore by (1) of the Subquery-Subgoal Correspondence Lemma, $$
\begin{align}
  I \wedge \Sigma_\mathrm{qrr}
    &\models (\sigma \upharpoonright \overline{C_i})(\mathrm{Subgoal}_{C_i}(\vec{\partial C_i})) \\
    &= \sigma(\mathrm{Subgoal}_{C_i}(\vec{\partial C_i})).
\end{align}
$$Since $\sigma(\mathrm{Subgoal}_{C_i}(\partial C_i))$ is a ground fact, we conclude that $\sigma(\mathrm{Subgoal}_{C_i}(\partial C_i)) \in \FullSat_{\Sigma_\mathrm{qrr}}(I)$.
> > 
> > ($\Longleftarrow$, the "soundness" of the rewrite):
> > Suppose $I \wedge \Sigma_\mathrm{qrr} \models \sigma_\mathrm{sol}(\mathrm{Goal^Q}(\vec{z}))$. By construction of $\Sigma_\mathrm{qrr}$, there must be some subset $V \supseteq \elems(\vec{z})$ of $\mathcal{V}$ such that if we write
> >  - $\set{C_i}_{i \in I_V}$ for the set of connected components of $\mathcal{H}(\overline{Q}-V)$, and
> >  - $J_V$ for the set $\set{ j \in J \mid \vec{u}_j \text{ only contains variables from } V}$,
> > 
> > then the ground substitution $\sigma_\mathrm{sol}$ can be extended to a ground substitution $\sigma_V$ that exactly covers $\vec{V}$ such that $$
\sigma_V \left(
  \set{A_j(\vec{u}_j) \mid j \in J_V} \cup \set{\mathrm{Subgoal}_{C_i}(\partial C_i) \mid i \in I_V}
\right) \subseteq \FullSat_{\Sigma_\mathrm{qrr}}(I)
$$holds, so that the base fact $\sigma_\mathrm{sol}(\mathrm{Goal^Q}(\vec{z}))$ is $\Sigma_\mathrm{qrr}$-derived through the rule $$\forall \vec{V}. \left(\bigwedge_{j \in J_V} A_j(\vec{u}_j)\right) \wedge \left(\bigwedge_{i \in I_V} \mathrm{Subgoal}_{C_i}(\partial C_i)\right) \rightarrow \mathrm{Goal}^Q(\vec{z}).$$together with $\sigma_V$.
> > 
> > Now for each $i \in I_V$, $\sigma_V \upharpoonright (\partial C_i)$ is a ground substitution exactly covering $\partial C_i$, so by (2) of the Subquery-Subgoal Correspondence Lemma, $I \wedge \Sigma \models (\sigma_V \upharpoonright (\partial C_i))(\overline{Q}_{C_i}) = \sigma_V(\overline{Q}_{C_i})$.
> > 
> > Also for each $j \in J_V$, $I \wedge \Sigma_\mathrm{qrr} \models \sigma_V(A_j(\vec{u}_j))$, but since $\Sigma_\mathrm{qrr}$ proves no new instance of existing predicates (i.e. predicates that are not $\mathrm{Subgoal}$s and $\mathrm{Goal}^Q$), $I \wedge \Sigma \models \sigma_V(A_j(\vec{u}_j))$.
> > 
> > Therefore, we have $$
\begin{align}
I \wedge \Sigma
  &\models \left(
    \bigwedge_{j \in J_V} \sigma_V(A_j(\vec{u}_j))
  \right) \wedge \left(
    \bigwedge_{i \in I_V}\sigma_V(\overline{Q}_{C_i})
  \right).
\end{align}
$$Now $$
\begin{align}
  \left(
    \bigwedge_{j \in J_V} \sigma_V(A_j(\vec{u}_j))
  \right) &\wedge \left(
    \bigwedge_{i \in I_V}\sigma_V(\overline{Q}_{C_i})
  \right) \\
    &= \sigma_V \left(
      \left(
        \bigwedge_{j \in J_V} A_j(\vec{u}_j)
      \right) \wedge \left(
        \bigwedge_{i \in I_V} \overline{Q}_{C_i}
      \right)
    \right) \\
    &= \sigma_V \left(
      \left(
        \bigwedge_{j \in J_V} A_j(\vec{u}_j)
      \right) \wedge \left(
        \bigwedge_{i \in I_V}
          \exists \vec{C_i}. \bigwedge_{j \in J_\overline{C_i}} A_j(\vec{u}_j)
      \right)
    \right) \\
    &\equiv \sigma_V \left(
      \left(
        \bigwedge_{j \in J_V} A_j(\vec{u}_j)
      \right) \wedge \left(
        \exists \vec{C_{i_1}}, \ldots ,\vec{C_{i_{|I_V|}}}.
        \bigwedge_{i \in I_V}
          \bigwedge_{j \in J_\overline{C_i}} A_j(\vec{u}_j)
      \right)
    \right) \\
    &\equiv \sigma_V \left(
      \exists \vec{C_{i_1}}, \ldots ,\vec{C_{i_{|I_V|}}}.
      \left(
        \bigwedge_{j \in J_V} A_j(\vec{u}_j)
      \right) \wedge \left(
        \bigwedge_{i \in I_V}
          \bigwedge_{j \in J_\overline{C_i}} A_j(\vec{u}_j)
      \right)
    \right) \\
    &\equiv \sigma_V \left(
      \exists \vec{C_{i_1}}, \ldots ,\vec{C_{i_{|I_V|}}}.
      \bigwedge_{j \in J} A_j(\vec{u}_j)
    \right)
\end{align}
$$where $J_\overline{C_i} = \set{ j \in J \mid \vec{u}_j \text{ only mentions variables from } \overline{C_i}}$, and the last equivalence is justified by the fact that $J_V \cup \bigcup \set{J_\overline{C_i} \mid i \in I_V} = J$ (which is straightforward to check) and by the $\wedge$-commutativity. Therefore $$I \wedge \Sigma
  \models \sigma_V \left(
      \exists \vec{C_{i_1}}, \ldots ,\vec{C_{i_{|I_V|}}}.
      \bigwedge_{j \in J} A_j(\vec{u}_j)
    \right).
  $$Now, restricting $\sigma_V$ to $\elems(\vec{z})$ yields $\sigma_\mathrm{sol}$, and existentially quantifying all variables in $V \setminus \elems(\vec{z})$ from the formula $\exists \vec{C_{i_1}}, \ldots ,\vec{C_{i_{|I_V|}}}. \bigwedge_{j \in J} A_j(\vec{u}_j)$ yields the original query $Q$, since $\set{\elems(C_i) \mid i \in I_V}$ is a disjoint cover of $(\elems(\vec{q} \concat \vec{z})) \setminus V$.
> >
> > We therefore conclude that $I \wedge \Sigma \models \sigma_\mathrm{sol}(Q)$.
