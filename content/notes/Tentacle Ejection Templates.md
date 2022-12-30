---
title: Tentacle Ejection Templates
tag:
  - notes
---

## Preliminaries

### In-place unifications

We shall first define what it means to identify (in-place) variables in a GTGD rule.

> **Definition**. Let $\vec{x}$ be a set of variables. An *in-place unification on $\vec{x}$* is a partition $\sim_\vec{x}$ of $\elems(\vec{x})$.
> 
> > **Example**. If $\vec{x} = (x_0, x_1, x_2, x_3)$, then an equivalence relation given by a partition $\set{\set{x_0}, \set{x_1, x_3}, \set{x_2}}$ is an in-place unification on $\vec{x}$.

## Tentacle Ejection Templates

We first describe an object that abstractly describe a situation where a tentacle hangs from some saturation of some base instance:

> **Definition**. Let $\Sigma$ be a finite set of GTGDs and $\tau = (\forall \vec{x}. \beta \rightarrow \exists \vec{y}. \eta) \in \Sigma$. A *$(\tau, \Sigma)$-export template* is a set $F$ of atomic formulae such that each $A \in F$
>   1. only mentions constants from $\Sigma$, and
>   2. only mentions variables in $\elems(\vec{x})$ that appear in some atom in $\eta$.
>
> > *Example*. Let $\tau = \forall x_1, x_2. R_1(x_1, x_2) \wedge U(x_1) \wedge P(c_0) \rightarrow \exists y. H(x_2, y, c_1)$ and $\Sigma = \set{\tau}$. Then the following are all $(\tau, \Sigma)$-export templates:
> >   - $\set{R_1(x_2, c_1), R_1(x_2, x_2)}$
> >   - $\set{R_1(c_0, c_1), U(x_2)}$
> >   - $\set{H(x_2, x_2, x_2), P(x_2)}$

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

> **Definition** Let $\Sigma$ be a finite set of GTGDs, and $T = (\tau = \forall \vec{x}. \beta \rightarrow \exists \vec{y}. \eta, \sim_\tau, F_\tau)$ be a $\Sigma$-tentacle ejection template. Given a ground substitution $\sigma_{F_\tau}$ that conforms to $\sim_\tau$, the *$\Sigma$-instantiation $\Tentacle_\Sigma(T, \sigma)$ of $T$ fired with $\sigma$* is defined as the subtree of $\SatTree_\Sigma(\sigma(F_\tau \cup \beta))$ induced by the set of nodes in $\SatTree_\Sigma(\sigma(F_\tau \cup \beta))$ that either
>   1. is the root node, or
>   2. corresponds to a valid generative $\Sigma$-chase-path on $\sigma(F_\tau)$ and starts with $(\tau, \sigma)$.

> **Definition**. Let $\Sigma$ be a finite set of GTGDs, $I$ a base instance, $T = (\tau = \forall \vec{x}. \beta \rightarrow \exists \vec{y}. \eta, \sim_\tau, F_\tau)$ a $\Sigma$-tentacle ejection template and $\sigma$ a factual substitution conforming to $\sim_\tau$. We say that *$T$ can be $\Sigma$-instantiated on $I$ using $\sigma$* if $\sigma(F_\tau \cup \beta) \subseteq \FullSat_\Sigma(I)$.

An instantiation of a $\Sigma$-tentacle ejection template on an instance embeds into the $\SatTree$ of the instance, in the following sense:

> **Proposition (Ejection Embedding)**.
> Let $\Sigma$ be a finite set of GTGDs, $I$ a base instance and $T = (\tau, \sim_\tau, F_\tau)$ a $\Sigma$-tentacle ejection template that can be instantiated on $I$ using $\sigma$. Then for each node $\vec{d}$ in $\Tentacle_\Sigma(T, \sigma)$,
>  1. $\vec{d}$ is a valid generative $\Sigma$-chase-path on $I$, i.e. is a node in $\SatTree_\Sigma(I)$, and moreover,
>  2. $\Instance_{\Tentacle_\Sigma(T, \sigma)}(\vec{d}) \subseteq \Instance_{\SatTree_\Sigma(I)}(\vec{d})$
> 
> > *Proof*. Since $\Tentacle_\Sigma(T, \sigma)$ is a subtree of $\SatTree_\Sigma(\sigma(F_\tau \cup \beta))$, the proposition is obvious from the SatTree monotonicity.

### Tentacle Abstraction

We have just seen that the instantiation of a tentacle $(\tau, \sim_\tau, F_\tau)$ with a substitution $\sigma$ is a way of turning a tentacle ejection template into a chase-like tree that can be actually embeded to a tentacle hanging from $(\tau, \sigma)$.

We now describe a way to "abstract" an actual tentacle to a tentacle ejection template that can be instantiated back exactly to the original tentacle.

> **Definition**. Let $(\tau, \sigma)$ be a valid generative $\Sigma$-chase-path on $I$. We say that a $\Sigma$-tentacle ejection template $T = (\tau_T, \sim_T, F_T)$ is an *abstraction of $(\tau, \sigma)$ over $I$* if
>   - $\tau_T = \tau$
>   - $\sigma$ conforms to $\sim_T$
>   - $\sigma(F_T) = \exports_\Sigma(I, (\tau, \sigma))$

The next proposition shows that we can always abstract a valid generative $\Sigma$-chase-path on a base instance.

> **Proposition (existence of abstraction)**. Let $(\tau = (\forall \vec{x}. \beta \rightarrow \exists \vec{y}. \eta), \sigma)$ be a valid generative $\Sigma$-chase-path on a base instance $I$. Then there exists an abstraction of $(\tau, \sigma)$ over $I$. ^d4d09d
> 
> > *Proof*.
> > Let $E = \exports_\Sigma(I, (\tau, \sigma))$, $D = (\operatorname{im} \sigma \cap \consts(E)) \setminus \consts(\Sigma)$ and $V \subseteq \elems(\vec{x})$ be variables in $\vec{x}$ that appear in some atom in $\eta$ (these are the *exported variables of $\tau$*).
> > 
> > We first claim the following:
> > 
> > > **Claim 1**. $\sigma \upharpoonright V: V \rightarrow D$ is a surjection onto $D$. In particular, there exists a right-inverse $\sigma^{-1}: D \rightarrow V$ of $\sigma \upharpoonright V$, so that $\sigma \circ \sigma^{-1} = \mathrm{id}_D$.
> > > 
> > > *Proof*. Take any constant $c \in D$. Then $c$ occurs in $E$, so $c$ is $\Sigma$-guarded by some fact $\sigma[\vec{y} \xrightarrow{\nu} \Nulls](G(\vec{t}))$ in $\sigma[\vec{y} \xrightarrow{\nu} \Nulls](\eta)$ (where $\nu$ is some null-picking function). As $c \in D$, $c$ does not occur in $\Sigma$, hence the fact $\sigma[\vec{y} \xrightarrow{\nu} \Nulls](G(\vec{t}))$ must contain $c$. Moreover, as $c$ does not occur in $\Sigma$, $G(\vec{t})$ does not contain $c$, so $\sigma$ must introduce $c$ to the fact $\sigma[\vec{y} \xrightarrow{\nu} \Nulls](G(\vec{t}))$. Hence there is variable $x$ occuring in $G(\vec{t})$ such that $\sigma(x) = c$, and we are done since $x \in V$.
> > 
> > Let $\sigma^{-1}: D \rightarrow V$ be the right-inverse of $\sigma \upharpoonright V$ constructed in Claim 1, and now let $F = \sigma^{-1}(E)$ (assume that every constant not in $D$ is sent as-is by $\sigma^{-1}$). Then by construction $\sigma(F) = E$.
> > 
> > Next, we make the following useful claim:
> > 
> > > **Claim 2**. For each atomic formula $A \in F$, $(\sigma^{-1} \circ \sigma)(A) = A$.
> > > 
> > > *Proof*. By construction of $F$, $A = \sigma^{-1}(B)$ for some fact $B \in E$. But since $\sigma^{-1}$ is a right-inverse of $\sigma \upharpoonright V$, $$
\begin{align}
(\sigma^{-1} \circ \sigma)(A)
  &= (\sigma^{-1} \circ \sigma \circ \sigma^{-1})(B) \\
  &= (\sigma^{-1} \circ (\sigma \upharpoonright V) \circ \sigma^{-1})(B) \\
  &= \sigma^{-1}(B) \\
  &= A
\end{align}
$$
> > 
> > We now claim that $F$ is a $(\tau, \Sigma)$-export template. Since every atom $A$ in $F$ can be written as $A = \sigma^{-1}(R(\vec{c}))$ for some fact $R(\vec{c}) \in E$, we need to check that for each $R(\vec{c}) \in E$, the atom $\sigma^{-1}(R(\vec{c})) \in F$
> >   - *(only mentions constants from $\Sigma$)*: Take a constant $a$ in $\sigma^{-1}(R(\vec{c}))$. Assume for contradiction that $a$ does not appear in $\Sigma$.
> >     
> >     We must have $a \not \in D$; if $a \in D$, then by Claim 2 the atom $\sigma^{-1}(R(\vec{c})) = (\sigma^{-1} \circ \sigma \circ \sigma^{-1})(R(\vec{c}))$ would not contain $a$, since the outer $\sigma^{-1}$ would send $\sigma(a) = a \in D$ to a variable, contradicting the choice of $a$.
> >     
> >     Since $a \not \in D = (\operatorname{im} \sigma \cap \consts(E)) \setminus \consts(\Sigma)$ while $a \not \in \consts(\Sigma)$, we must have either $a \not \in \operatorname{im} \sigma$ or $a \not \in \consts(E)$. It is impossible that $a \not \in \consts(E)$, since $F$ is obtained by replacing a constants in $E$ by variables. Hence $a \not \in \operatorname{im} \sigma$.
> >     
> >     As $R(\vec{c}) \in E$, $R(\vec{c}) = \sigma(\sigma^{-1}(R(\vec{c})))$ is $\Sigma$-guarded by some fact in $\chaseHead_\nu(\tau, \sigma) = \sigma[\vec{y} \xrightarrow{\nu} \Nulls](\eta)$. In particular, $a = \sigma(a)$ appears either in $\Sigma$ or in some atom of $\sigma[\vec{y} \xrightarrow{\nu} \Nulls](\eta)$.
> >     
> >     If $a$ appears in some atom of $\sigma[\vec{y} \xrightarrow{\nu} \Nulls](\eta)$, then $a$ must appear in $\eta$, since $a \not \in \operatorname{im} \sigma$. In any case $a$ appears in $\Sigma$, hence a contradiction.
> >
> >   - *(only mentions variables from $\elems(\vec{x})$ that appear in some atom in $\eta$)*: This is obvious from the construction of $F$, since $\sigma^{-1}: D \rightarrow V$.
> > 
> > We now have that $(\tau, \operatorname{ker} \sigma, F)$ is an abstraction of $(\tau, \sigma)$.

As expected, instantiation of an abstraction of chase-step direction $(\tau, \sigma)$ equals the tentacle hanging from $(\tau, \sigma)$, as formulated in the following lemma.

> **Lemma (abstraction-instantiation)**. Let $(\tau, \sigma)$ be a valid generative $\Sigma$-chase-path on $I$, and $T = (\tau, \sim, F)$ be an abstraction of $(\tau, \sigma)$ over $I$. ^efa86e
> 
> Then for all nonempty valid generative $\Sigma$-chase-path $\vec{d}$ on $I$, if $\vec{d}$ starts with $(\tau, \sigma)$, then $\Instance_{\Tentacle_\Sigma(T, \sigma)}(\vec{d}) = \Instance_{\SatTree_\Sigma(I)}(\vec{d})$.
> 
> > *Proof*. Let $\tau = \forall \vec{x}. \beta \rightarrow \exists \vec{y}. \eta$. We proceed by induction on $\vec{d}$. 
> > 
> > (base case $\vec{d} = ((\tau, \sigma))$): We first make the following claim: 
> > 
> > > **Claim**. $$\exports_\Sigma(I, (\tau, \sigma)) = \exports_\Sigma(\exports_\Sigma(I, (\tau, \sigma)) \cup \sigma(\beta), (\tau, \sigma))$$
> > > *Proof*.
> > > ($\subseteq$): Take any $F \in \exports_\Sigma(I, (\tau, \sigma))$. Then $F$ is guarded by $\chaseHead_\nu(\tau, \sigma)$, and $F \in \exports_\Sigma(I, (\tau, \sigma)) \cup \sigma(\beta)$ so $F \in \exports_\Sigma(\exports_\Sigma(I, (\tau, \sigma)) \cup \sigma(\beta), (\tau, \sigma))$.
> > > 
> > > ($\supseteq$): Follows from the fact that $I \supseteq \exports_\Sigma(I, (\tau, \sigma)) \cup \sigma(\beta)$.
> >
> > Now $$

\begin{align}
\Instance_{\SatTree_{\Sigma(I)}}(\vec{d})
  &= \FullSat_\Sigma(\chase_{\widehat{\#_{\vec{d}}}}(\operatorname{SC}_{\Sigma, ()}(I), (\tau, \sigma))) \\
  &= \FullSat_\Sigma(\chase_{\widehat{\#_{\vec{d}}}}(I, (\tau, \sigma))) \\
  &= \FullSat_\Sigma(\chaseHead_{\widehat{\#_{\vec{d}}}}(\tau, \sigma) \cup \exports_\Sigma(I, (\tau, \sigma))) \\
  &= \FullSat_\Sigma(\chaseHead_{\widehat{\#_{\vec{d}}}}(\tau, \sigma) \cup \exports_\Sigma(\exports_\Sigma(I, (\tau, \sigma)) \cup \sigma(\beta), (\tau, \sigma)) \\
  &= \FullSat_\Sigma(\chase_{\widehat{\#_{\vec{d}}}}(\exports_\Sigma(I, (\tau, \sigma)) \cup \sigma(\beta), (\tau, \sigma))) \\
  &= \FullSat_\Sigma(\chase_{\widehat{\#_{\vec{d}}}}(\sigma(F \cup \beta), (\tau, \sigma))) \\
  &= \Instance_{\SatTree_\Sigma(\sigma(F \cup \beta))}(\vec{d}) \\
  &= \Instance_{\Tentacle_\Sigma(T, \sigma)}(\vec{d})
\end{align}
$$so we are done.
> >
> > (inductive part): Obvious.


## Generic Proofs

Throughout this section, whenever we take a generic $\Sigma$-tentacle ejection template $T = (\tau = \forall \vec{x}. (\beta \rightarrow \exists \vec{y}. \eta) \in \Sigma, \sim_\tau, F_\tau)$ and a (not necessarily boolean) conjunctive query $Q = \exists \vec{z}. \bigwedge_{i \in I} A_i(\vec{w_i})$, by renaming bound variables we shall assume that $\vec{x}, \vec{y}$, $\vec{z}$ and $\operatorname{FV}(Q)$ are all disjoint to each other.

> **Definition**. For a set $\Sigma$ of finite GTGDs, a *$\Sigma$-generic constant assignment* is a computable function $\GenConst_\Sigma: \mathcal{P}_\mathrm{fin}(\Vars) \rightarrow \Consts$ such that $\mathrm{im}(\GenConst) \cap \consts(\Sigma) = \emptyset$.

From now on, we shall assume that, for each $\Sigma$, we have decided a choice on a $\Sigma$-generic constant assignment $\GenConst_\Sigma$. We shall refer to this particular function as *the* $\Sigma$-generic constant assignment.

> **Definition**. Let $T = (\tau = \forall \vec{x}. (\beta \rightarrow \exists \vec{y}. \eta) \in \Sigma, \sim_\tau, F_\tau)$ be a $\Sigma$-tentacle ejection template. The *generic instance $\GenInst_\Sigma(T)$ associated with $T$* is the instance $$
\GenInst_\Sigma(T) :=
  (\GenConst_\Sigma \circ \mathrm{quotient}_{\sim_T})(F_\tau \cup \beta)
$$ where $\mathrm{quotient}_{\sim_T}: \elems(\vec{x}) \rightarrow {\sim_\tau}$ is the quotient map $x \mapsto [x]_{\sim_\tau}$.

> **Definition**. Let $T = (\tau = \forall \vec{x}. (\beta \rightarrow \exists \vec{y}. \eta) \in \Sigma, \sim_\tau, F_\tau)$ be a $\Sigma$-tentacle ejection template, and let $Q$ be a (*not necessarily boolean*) conjunctive query.  A *$T$-closing map on $Q$* is a map $\gamma: \operatorname{FV}(Q) \rightarrow ({\sim}_\tau \cup \consts(\Sigma))$.

> **Definition**. Let $T = (\tau, \sim_\tau, F_\tau)$ be a $\Sigma$-tentacle ejection template and $Q = \exists \vec{z}. \bigwedge_{i \in I} A_i(\vec{w_i})$ a conjunctive query. Write $\vec{z'}$ for $\mathrm{FV}(Q)$ in some order, and $\gamma: \elems(\vec{z'}) \rightarrow ({\sim}_\tau \cup \consts(\Sigma))$ a $T$-closing map on $Q$. The *$T$-generic closure of $Q$ by $\gamma$* is a boolean conjunctive query $\mathrm{cl}_\gamma(Q)$ given by $$\mathrm{cl}_\gamma(Q) = \exists \vec{z'}, \vec{z}. \bigwedge_{i \in I} A_i((\GenConst_\Sigma \circ \gamma)(\vec{w_i}))$$

> **Definition**. Let $T$ be a $\Sigma$-tentacle ejection template, $Q$ a conjunctive query and $\gamma_Q: \mathrm{FV}(Q) \rightarrow {\sim_\tau}$ a $T$-closing map on $Q$. We say that $(T, \gamma_Q)$ *generically proves* $Q$ when $\GenInst_\Sigma(T) \wedge \Sigma \models \mathrm{cl}_\gamma(Q)$.

(TODO: We probably need the following two results in order to prove the correctness of the rewrite algorithm:
 1. If there is a generic proof of a subquery, then the instantiation of the template induces an actual witness on $\SatTree$ of the subquery
 2. If there is a witness of the subquery in a tentacle, then the abstraction of the tentacle, together with the induced $T$-expectation (we should make this precise), generically proves the subquery.
)
