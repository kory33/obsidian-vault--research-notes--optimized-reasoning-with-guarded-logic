---
title: Rewritings
tag:
  - notes
  - definitions
---

> This note builds on [[Logic Preliminaries]].

## Conjunctive Query Answering

Through the language of substitutions, we define what it means to *answer* a conjunctive query.

> **Definition**. Given a set $\Sigma$ of TGDs, a base instance $I$ and a rectified conjunctive query $Q = \exists \vec{x}. \bigwedge_{j \in J} A_j(\vec{y'}_j)$, an *answer to $Q$ on $I$ under $\Sigma$* is a ground substitution $\sigma$ covering exactly $\mathrm{FV}(Q)$ such that $I \wedge \Sigma \models \sigma(Q)$. The set of all ansers to $Q$ on $I$ under $\Sigma$ is denoted by $\QueryAnswers(Q, I; \Sigma)$.

## Rule-Rewritings

> **Definition**. Given a set $\Sigma$ of TGDs, a Datalog program $\Sigma_{\text{rew}}$ is *a rule-rewriting of $\Sigma$* if, for every base instance $I$, $\Sigma$ and $\Sigma_{\text{rew}}$ generate the same set of **base facts**, i.e. for every base fact $F$, $$I \wedge \Sigma \models F \Longleftrightarrow I \wedge \Sigma_{\text{rew}} \models F.$$

> **Fact**. If $\Sigma$ is a finite set of GTGDs, then there exists a rule-rewriting of $\Sigma$, and moreover it can be computed.
> 
> > *Proof*: See [[Papers#^a74196]], where three different competitive algorithms for computing rule-rewriting of GTGDs are presented.

## Query-Rule-Rewritings

> **Definition**. Let $\Sigma$ be a set of TGDs and $Q = \exists \vec{x}. \bigwedge_{j \in J} A_j(\vec{y'}_j)$ a conjunctive query. Let $\vec{z}$ be the sequence of free variables in $Q$. 
> 
> We say that a pair of a Datalog program $\Sigma^Q_\rew$ (with a suitably extended set of predicates) together with a (possibly fresh) *$|\vec{z}|$-ary goal predicate* $\mathrm{Goal^Q}(\underbrace{-, \ldots, -}_{|\vec{z}|\text{ arguments}})$ is a *query-rule-rewriting of $(\Sigma, Q)$* if, for every base instance $I$, $$\QueryAnswers(Q, I; \Sigma) = \QueryAnswers(\mathrm{Goal}^Q(\vec{z}), I; \Sigma^Q_\mathrm{rew}).$$ holds.
> 
> > *Remark*. This is equivalent to saying that, for all base instance $I$ and every ground substitution $\sigma$ that exactly covers $\elems(\vec{z})$, $$I \wedge \Sigma \models \sigma(Q) \Longleftrightarrow I \wedge \Sigma^Q_\rew \models \sigma(\mathrm{Goal^Q}(\vec{z})). $$ holds.
