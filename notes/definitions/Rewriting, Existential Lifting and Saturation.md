---
tag:
  - notes
  - definitions
---

> This note builds on [[Logic Preliminaries]]

Given a set $\Sigma$ of TGDs, a Datalog program $\Sigma_{\text{rew}}$ is *a rewriting of $\Sigma$* if for every base instance $I$, $\Sigma$ and $\Sigma_{\text{rew}}$ generate the same set of consequences, i.e. for every __base fact__ $F$, $$I \wedge \Sigma \models F \Longleftrightarrow I \wedge \Sigma_{\text{rew}} \models F.$$
Given a fact $R(\vec{f})$, the *existential lifting $\exlift(R(\vec{f}))$ of $R(\vec{f})$* is defined as the formula $$\exlift(R(\vec{f})) := \exists \vec{\nu}. R(\vec{f}[\ \vec{n} \leftarrow \vec{\nu}\ ])$$
where
 - $\vec{\nu}$ are variables corresponding to nulls in $\vec{f}$,
 - $\vec{f}[\ \vec{n} \leftarrow \vec{\nu}\ ]$ is $\vec{f}$ with nulls replaced by their corresponding variables in $\vec{\nu}$. 

The *existential lifting $\exlift(I)$ of an instance $I$* is a set $\set{\ \exlift(F) \mid F \in I\ }$ of formulae.

Given a set $\Sigma$ of TGDs and an instance $I$, the *saturation $\Sat_\Sigma(I)$ of $I$ under $\Sigma$* is the instance defined by $$\Sat_\Sigma(I) := I \cup \set{\ F \in \BaseFacts \mid \Sigma \wedge \exlift(I) \models F\ }$$ i.e. $I$ together with the set of all base facts $\Sigma$-derivable from $I$.