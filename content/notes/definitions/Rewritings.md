---
title: Rewritings
tag:
  - notes
  - definitions
---

> This note builds on [[Logic Preliminaries]].

## Rule-Rewritings

> **Definition**. Given a set $\Sigma$ of TGDs, a Datalog program $\Sigma_{\text{rew}}$ is *a rule-rewriting of $\Sigma$* if, for every base instance $I$, $\Sigma$ and $\Sigma_{\text{rew}}$ generate the same set of **base facts**, i.e. for every base fact $F$, $$I \wedge \Sigma \models F \Longleftrightarrow I \wedge \Sigma_{\text{rew}} \models F.$$

> **Fact**. If $\Sigma$ is a finite set of GTGDs, then there exists a rule-rewriting of $\Sigma$, and moreover it can be computed.
> 
> > *Proof*: See [[Papers#^a74196]], where three different competitive algorithms for computing rule-rewriting of GTGDs are presented.

## Query-Rule-Rewritings

> **Definition**. Given a set $\Sigma$ of TGDs and a conjunctive query $Q$, we say that a Datalog program $\Sigma^Q_\rew$ together with a fresh *0-ary goal predicate* $\mathrm{Goal^Q}()$ is a *query-rule-rewriting of $(\Sigma, Q)$* if for every base instance $I$, $$I \wedge \Sigma \models Q \Longleftrightarrow I \wedge \Sigma^Q_\rew \models \mathrm{Goal^Q}(). $$
