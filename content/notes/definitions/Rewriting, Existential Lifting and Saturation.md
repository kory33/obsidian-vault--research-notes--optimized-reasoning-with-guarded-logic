---
title: Rewriting, Existential Lifting and Saturation
tag:
  - notes
  - definitions
---

> This note builds on [[Logic Preliminaries]]

Given a set $\Sigma$ of TGDs, a Datalog program $\Sigma_{\text{rew}}$ is *a rule-rewriting of $\Sigma$* if for every base instance $I$, $\Sigma$ and $\Sigma_{\text{rew}}$ generate the same set of consequences, i.e. for every __base fact__ $F$, $$I \wedge \Sigma \models F \Longleftrightarrow I \wedge \Sigma_{\text{rew}} \models F.$$

If we also have a conjunctive query $Q$, we say that a Datalog program $\Sigma^Q_\rew$ together with a fresh *0-ary goal predicate* $\mathrm{Goal^Q}()$ is a *query-rule-rewriting of $(\Sigma, Q)$* if for every base instance $I$, $$I \wedge \Sigma \models Q \Longleftrightarrow I \wedge \Sigma^Q_\rew \models \mathrm{Goal^Q}() $$

Given a fact $R(\vec{f})$, the *existential lifting $\exlift(R(\vec{f}))$ of $R(\vec{f})$* is defined as the formula $$\exlift(R(\vec{f})) := \exists \vec{\nu}. R(\vec{f}[\ \vec{n} \leftarrow \vec{\nu}\ ])$$
where
 - $\vec{\nu}$ are variables corresponding to nulls in $\vec{f}$,
 - $\vec{f}[\ \vec{n} \leftarrow \vec{\nu}\ ]$ is $\vec{f}$ with nulls replaced by their corresponding variables in $\vec{\nu}$. 

The *existential lifting $\exlift(I)$ of an instance $I$* is a set $\set{\ \exlift(F) \mid F \in I\ }$ of formulae.

Given a Datalog program $\Sigma$ and an instance $I$, we define the *$k$-th partial Datalog-saturation $\Sat^k_\Sigma(I)$ of $I$ by $\Sigma$* by induction on $k \in \mathbb{N}$, by $$\begin{align}
  \Sat^0_\Sigma(I) &= I \\
  \Sat^{k + 1}_\Sigma(I) &= \Sat^k_\Sigma(I) \cup \set{\ \sigma(\eta) \mid (\forall \vec{x}. \beta \rightarrow \eta) \in \Sigma, \sigma \text{ covers } \vec{x}, \sigma(\beta) \subseteq \Sat^k_\Sigma(I)\ }
\end{align}$$
We define the *Datalog saturation $\Sat_\Sigma(I)$ of $I$ by a Datalog program $\Sigma$* as $$\Sat_\Sigma(I) = \bigcup_{k \in \mathbb{N}} \Sat^k_\Sigma(I)$$
More generally, for an arbitrary finite collection $\Sigma$ of GTDGs and an instance $I$, we define *the full saturation $\FullSat_\Sigma(I)$ of $I$ by $\Sigma$* as $$\FullSat_\Sigma(I) = \Sat_{\Sigma_\rew}(I)$$ for *some* rule-rewriting $\Sigma_\rew$ of $\Sigma$. This definition is well-defined, since any two Datalog rewritings produce the same Datalog saturation by definition. 