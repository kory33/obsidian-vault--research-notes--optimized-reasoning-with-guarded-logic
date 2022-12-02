---
title: Rewriting, Existential Lifting and Saturation
tag:
  - notes
  - definitions
---

> This note builds on [[Logic Preliminaries]]

## Rewritings

> **Definition**. Given a set $\Sigma$ of TGDs, a Datalog program $\Sigma_{\text{rew}}$ is *a rule-rewriting of $\Sigma$* if, for every base instance $I$, $\Sigma$ and $\Sigma_{\text{rew}}$ generate the same set of **base facts**, i.e. for every base fact $F$, $$I \wedge \Sigma \models F \Longleftrightarrow I \wedge \Sigma_{\text{rew}} \models F.$$

> **Definition**. Given a set $\Sigma$ of TGDs and a conjunctive query $Q$, we say that a Datalog program $\Sigma^Q_\rew$ together with a fresh *0-ary goal predicate* $\mathrm{Goal^Q}()$ is a *query-rule-rewriting of $(\Sigma, Q)$* if for every base instance $I$, $$I \wedge \Sigma \models Q \Longleftrightarrow I \wedge \Sigma^Q_\rew \models \mathrm{Goal^Q}(). $$

## Saturations

Given an instance $I$ and a finite set $\Sigma$ of Datalog rules, we can form *the smallest superinstance of $I$ satisfying $\Sigma$*, which we shall call $\Sat_\Sigma(I)$. To make this precise, we begin with the following definition.

### Datalog Saturations

> **Definition**. Given a Datalog program $\Sigma$ and an instance $I$, we define the *$k$-th partial Datalog-saturation $\Sat^k_\Sigma(I)$ of $I$ by $\Sigma$* by induction on $k \in \mathbb{N}$, by $$\begin{align}
  \Sat^0_\Sigma(I) &= I \\
  \Sat^{k + 1}_\Sigma(I) &= \Sat^k_\Sigma(I) \cup \set{\ \sigma(\eta) \mid (\forall \vec{x}. \beta \rightarrow \eta) \in \Sigma, \sigma \text{ covers } \vec{x}, \sigma(\beta) \subseteq \Sat^k_\Sigma(I)\ }
\end{align}$$

Here are some basic properties of $\Sat^k_\Sigma(-)$.

> **Proposition**. If $I \subseteq I'$ are instances and $\Sigma$ is a finite set of GTGDs, then for each $k \in \mathbb{N}$, $\Sat^k_\Sigma(I) \subseteq \Sat^k_\Sigma(I')$.
> 
> > *Proof*. By a simple induction on $k$.

> **Proposition**. Let $\Sigma$ be a Datalog program and $I$ an instance. Then for each $k \in \mathbb{N}$ and for all base fact $F$, if $F \in \Sat_\Sigma^k(I)$ then $I \wedge \Sigma \vdash F$  (by $\vdash$ we simply mean "provable in natural deduction"). ^7faefd
> 
> > *Proof*. By induction on $k$.
> > 
> > The base case is obvious, since if $F \in \Sat^0_\Sigma(I) = I$, $I \vdash F$ and therefore $I \wedge \Sigma \vdash F$. 
> > 
> > For the inductive part, suppose $F \in \Sat^{k+1}_\Sigma(I)$. If $F \in \Sat^k_\Sigma(I)$ then we are done by the inductive hypothesis. Otherwise, there must be some $(\forall \vec{x}. \beta \rightarrow \eta) \in \Sigma$ and a factual substitution $\sigma$ covering $\vec{x}$ such that $\sigma(\beta) \subseteq \Sat^k_\Sigma(I)$, and $F = \sigma(\eta)$. By inductive hypothesis, each atom $F \in \sigma(\beta) \subseteq \Sat^k_\Sigma(I)$ can be derived from $I \wedge \Sigma$, hence $I \wedge \Sigma \vdash \sigma(\beta)$. Since $\sigma(\beta) \rightarrow \sigma(\eta)$ can be deduced from $\Sigma$ in one step, by modus ponens $I \wedge \Sigma \vdash \sigma(\eta)$.

Now, we define the desired instance.

> **Definition**. The *Datalog saturation $\Sat_\Sigma(I)$ of $I$ by a Datalog program $\Sigma$* is defined as the instance $$\Sat_\Sigma(I) = \bigcup_{k \in \mathbb{N}} \Sat^k_\Sigma(I).$$

> **Proposition (Saturation monotonicity)**. If $I \subseteq I'$ are instances and $\Sigma$ is a finite set of GTGDs, then $\Sat_\Sigma(I) \subseteq \Sat_\Sigma(I')$.
> 
> > *Proof*. By monotonicity of $\Sat^k_\Sigma(-)$ for each $k \in \mathbb{N}$.

Our requirement that the $\Sat_\Sigma(I)$ is "*the smallest superinstance of $I$ satisfying $\Sigma$*" is captured in the following theorem.

> **Theorem (Base-fact completeness of Datalog saturations)**.
> Let $I$ be a base instance, $F$ a base fact and $\Sigma$ be a Datalog program. Then $$F \in \Sat_\Sigma(I) \Longleftrightarrow I \wedge \Sigma \models F.$$
> ^b7f0b5
> > *Proof*.
> > ($\Longrightarrow$): By [[#^7faefd]] and soundness of natural deduction, $$
\begin{align}
F \in \Sat_\Sigma(I)
  &\Longrightarrow F \in \Sat_\Sigma^k(I) \text{ for some } k \in \mathbb{N} \\
  &\Longrightarrow I \wedge \Sigma \vdash F \\
  &\Longrightarrow I \wedge \Sigma \models F \\
\end{align}$$
> > ($\Longleftarrow$):
> > Let $\mathcal{M}$ be a model that makes precisely the facts in $\Sat_\Sigma(I)$ true. We then have $\mathcal{M} \models I$, since $\Sat_\Sigma(I) \supseteq \Sat^0_\Sigma(I) = I$.
> > 
> > > **Claim**. $\mathcal{M} \models \Sigma$.
> > > *Proof of the claim*. Take any $\tau = (\forall \vec{x}. \beta \rightarrow \eta) \in \Sigma$. We show that $\mathcal{M} \models \tau$.
> > > 
> > > So take any factual substitution $\sigma$ such that $\mathcal{M} \models \sigma(\beta)$. By construction of $\mathcal{M}$, $\sigma(\beta) \subseteq \Sat_\Sigma(I)$. Since $\sigma(\beta)$ is finite, $\sigma(\beta) \subseteq \Sat^k_\Sigma(I)$ for some $k \in \mathbb{N}$. But then by definition of $\Sat^{k+1}_\Sigma(I)$, $\sigma(\eta) \in \Sat^{k+1}_\Sigma(I) \subseteq \Sat_\Sigma(I)$, so $\mathcal{M} \models \sigma(\eta)$.
> >
> > Therefore $\mathcal{M} \models I \wedge \Sigma$ and by assumption $\mathcal{M} \models F$. But then by construction of $\mathcal{M}$, $F \in \Sat_\Sigma(I)$.

### Full Saturations

The previous section talked about saturating an instance using a finite set of *Datalog* rules.

We can try to do the similar thing with a finite set of *guarded TGDs*, but at the same time we want to collect facts that does not mention newly introduced nulls. This motivates the following definition.

> **Definition**. Let $\Sigma$ be a finite collection of TGDs and $I$ an instance.
> 
> If $\Sigma$ has some rule-rewriting $\Sigma_\mathrm{rew}$, then we define *the full saturation $\FullSat_\Sigma(I)$ of $I$ by $\Sigma$* as $$\FullSat_\Sigma(I) = \Sat_{\Sigma_\rew}(I).$$ 
> > *Remark*. This definition is well-defined, i.e. does not depend on the choice of $\Sigma_\mathrm{rew}$, since any two Datalog rewritings produce the same Datalog saturation by the theorem [[#^b7f0b5]]. 

The following proposition is a simple consequence of [[#^b7f0b5]] and the definition of $\FullSat_\Sigma(-)$:

> **Proposition**. Suppose that $\Sigma$ is a set of TGDs that admit a rule-rewriting. Then for a base instance $I$ and a *base fact* $F$, $$F \in \FullSat_\Sigma(I) \Longleftrightarrow I \wedge \Sigma \models F.$$
> > *Proof*. $$
\begin{align}
  F \in \FullSat_\Sigma(I)
    &\Longleftrightarrow F \in \Sat_{\Sigma_\mathrm{rew}}(I) \\
    &\Longleftrightarrow I \wedge \Sigma_\mathrm{rew} \models F \\
    &\Longleftrightarrow I \wedge \Sigma \models F.
\end{align}
$$
