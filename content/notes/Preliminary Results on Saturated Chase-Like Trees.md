---
title: Preliminary Results on Saturated Chase-Like Trees
tags:
  - notes
---

## General Definitions surrounding $\SatTree$s

> **Definition.** For chase-like tree $T$ and its vertex $v \in T_0$, we say that $v$ *mentions* a factual term $t$ if $\Instance_T(v)$ contains a fact $P(\vec{t'})$ such that $t \in \elems(\vec{t'})$.

> **Definition.** For a chase-like tree $T$ and a factual term $t$, the _subgraph of $T$ mentioning $t$_, denoted $T \upharpoonright t$, is the subgraph of $T$ induced by the vertex set $V_t = \set{v \in T \mid v \text{ mentions } t }$ together with the instance assignment restricted to $V_t$, i.e. $\Instance_{T \upharpoonright t} = \Instance_T \upharpoonright V_t$ .

We can see that the subgraph of a $\SatTree$ mentioning $t$ really is then a subtree sitting in the $\SatTree$ as seen in the following proposition:

> **Proposition**. For a finite set $\Sigma$ of GTGDs, a base instance $I$ and any factual term $t$, $\SatTree_\Sigma(I) \upharpoonright t$ is connected. In particular, if $t$ is mentioned in $\TreeFacts(\SatTree_\Sigma(I))$, then $\SatTree_\Sigma(I) \upharpoonright t$ is a rooted subtree of $\SatTree_\Sigma(I)$.
> 
> > _Proof_. By construction of $\SatTree_\Sigma(I)$, we have that
> > - a factual term not already mentioned in $I$ is never introduced by any chase-step direction from any node
> > - a null introduced at a node $\vec{d}$ is never introduced anywhere else in the tree

Now, for each factual term $t$ mentioned somewhere in the $\SatTree$, we can identify where $t$ has been "introduced" in the tree:

> **Definition.** For a factual term $t$ mentioned in $\TreeFacts(\SatTree_\Sigma(I))$, the *introduction point $\Intro(t)$ of $t$* is the root node of the subtree $\SatTree_\Sigma(I) \upharpoonright t$.

Clearly, $\Intro(t)$ is the root node $()$ if and only if $t$ is a constant.

## Fact Introduction Lemma

We have the following useful lemma:

> **Lemma (Fact Introduction)**. For a node $n$ of $\SatTree_\Sigma(I)$, its ancestor node $a$ and a fact $P(\vec{t}) \in \Instance_{\SatTree_\Sigma(I)}(n)$, if $\Intro(t) \geq a$ for all $t \in \elems(\vec{t})$, then $P(\vec{t}) \in \Instance_{\SatTree_\Sigma(I)}(a)$.
> 
> > _Proof_. TODO (we would probably make a heavy use of this lemma when arguing validity of query reductions)

An immediate consequence of the lemma is the following:

> **Proposition**. If $P(\vec{t}) \in \TreeFacts(\SatTree_\Sigma(I))$ is a base fact, then $P(\vec{t}) \in \Sat_\Sigma(I)$. ^6bd969
> 
> > *Proof*.
> > By the assumption, $P(\vec{t}) \in \Instance_{\SatTree_\Sigma(I)}(n)$ for some node $n \in \SatTree_\Sigma(I)$.
> > 
> > Now for all $t \in \elems(\vec{t})$, $\Intro(t)$ is the root node $()$, which is an ancestor of $n$. Therefore by the Fact Introduction lemma $P(\vec{t}) \in \Instance_{\SatTree_\Sigma(I)}(()) = \Sat_\Sigma(I)$.

## Acting Consts Translations on SatTrees

We now want to consider acting consts translations on $\SatTree$s. To do so, we extend a const translation $t: \Consts \rightarrow \Consts$ to a function $\tilde{t}: \Consts \cup \mathrm{im}(\#) \rightarrow \Consts \cup \mathrm{im}(\#)$ on the set of constants unioned with the image $\mathrm{im}(\#)$ of the global null-picking function $\#$.

> **Definition**. Let $\vec{d} = ((\tau_1, \sigma_1), \ldots, (\tau_n, \sigma_n))$ be a finite generic chase path and $t: \Consts \rightarrow \Consts$ a consts translation. We define *the finite generic chase path $\mathrm{map}_t(\vec{d})$ mapped by $t$* to be the finite generic chase path given by $$\mathrm{map}_t(\vec{d}) = ((\tau_1, t \circ \sigma_1), \ldots, (\tau_n, t \circ \sigma_n)).$$

> **Definition**. Given a consts translation $t: \Consts \rightarrow \Consts$, we define the *extension $\tilde{t}: \Consts \cup \mathrm{im}(\#) \rightarrow \Consts \cup \mathrm{im}(\#)$ of $t$ to introduced nulls* with $$
\tilde{t}(\#(\vec{d}, n)) := \#(\mathrm{map}_t(\vec{d}), n),
$$and by an abuse of notation we identify $\tilde{t}$ with $t$.

The previous definition is motivated by the following series of propositions.

> **Definition**. For an endofunction $f: A \rightarrow A$ and $S \subseteq A$, we say that *$f$ fixes $S$* if for all $s \in S$, $f(s) = s$.

> **Proposition**. Let $\Sigma$ be a finite set of GTGDs, $I$ an instance and $t: \Consts \rightarrow \Consts$ a consts translation that fixes $\consts(\Sigma)$. Then $t(\FullSat_\Sigma(I)) \subseteq \FullSat_\Sigma(t(I))$.
> 
> > *Proof*. Choose a rewriting $\Sigma_\mathrm{rew}$ of $\Sigma$, then $$
\begin{align}
  t(\FullSat_\Sigma(I))
   &= t(\Sat_{\Sigma_\mathrm{rew}}(I)) \\
   &= t(\bigcup_{k \in \mathbb{N}} \Sat^k_{\Sigma_\mathrm{rew}}(I)),
\end{align}
$$and $$
\begin{align}
  \FullSat_\Sigma(t(I))
   &= \Sat_{\Sigma_\mathrm{rew}}(t(I)) \\
   &= \bigcup_{k \in \mathbb{N}} \Sat^k_{\Sigma_\mathrm{rew}}(t(I)).
\end{align}
$$
> > So it suffices to show that $t(\Sat^k_{\Sigma_\mathrm{rew}}(I)) \subseteq \Sat^k_{\Sigma_\mathrm{rew}}(t(I))$ for all $k \in \mathbb{N}$. We proceed by induction on $k$. The base case is $t(\Sat_{\Sigma_\mathrm{rew}}^0(I)) = t(I) = \Sat_{\Sigma_\mathrm{rew}}^0(t(I))$. To see the inductive part, suppose $t(\Sat^k_{\Sigma_\mathrm{rew}}(I)) \subseteq \Sat^k_{\Sigma_\mathrm{rew}}(t(I))$. Then $$
\begin{align}
  t(\Sat^{k+1}_{\Sigma_\mathrm{rew}}(I))
    &= t(\Sat^k_{\Sigma_\mathrm{rew}}(I) \cup \set{\ \sigma(\eta) \mid (\forall \vec{x}. \beta \rightarrow \eta) \in {\Sigma_\mathrm{rew}}, \sigma \text{ covers } \vec{x}, \sigma(\beta) \subseteq \Sat^k_{\Sigma_\mathrm{rew}}(I)\ }) \\
    &= t(\Sat^k_{\Sigma_\mathrm{rew}}(I)) \cup \set{\ (t \circ \sigma)(\eta) \mid (\forall \vec{x}. \beta \rightarrow \eta) \in {\Sigma_\mathrm{rew}}, \sigma \text{ covers } \vec{x}, \sigma(\beta) \subseteq \Sat^k_{\Sigma_\mathrm{rew}}(I)\ } \\
    &\subseteq \Sat^k_{\Sigma_\mathrm{rew}}(t(I)) \cup \set{\ \sigma'(\eta) \mid (\forall \vec{x}. \beta \rightarrow \eta) \in {\Sigma_\mathrm{rew}}, \sigma' \text{ covers } \vec{x}, \sigma'(\beta) \subseteq \Sat^k_{\Sigma_\mathrm{rew}}(t(I))\ } \\
	&= \Sat^{k+1}_{\Sigma_\mathrm{rew}}(t(I))
\end{align}
$$where the third subset relation follows from the fact that if $\sigma$ covers $\vec{x} = \mathrm{FV}(\beta)$ and $\sigma(\beta) \subseteq \mathrm{Sat}^k_\Sigma(I)$, then $t \circ \sigma$ is a factual substitution covering $\vec{x}$ (as $t$ fixes $\consts(\Sigma) \supseteq \consts(\beta) = \consts(\sigma(\beta))$) and $(t \circ \sigma)(\beta) \subseteq t(\Sat^k_\Sigma(I)) \subseteq \Sat^k_\Sigma(t(I))$ by induction hypothesis. 

> **Proposition**. Let $\Sigma$ be a finite set of GTGDs, $I$ a base instance and $t: \Consts \rightarrow \Consts$ a consts translation that fixes $\consts(\Sigma)$.Then for any valid $\Sigma$-chase path $\vec{d} = ((\tau_1, \sigma_1), \ldots, (\tau_n, \sigma_n))$ on $I$, $$t(\Instance_{\SatTree_\Sigma(I)}(\vec{d})) \subseteq \Instance_{\SatTree_\Sigma(t(I))}(\mathrm{map}_t(\vec{d})).$$
>
> > *Proof*. By induction on the length of $\vec{d}$. The base case is proven in the preceding proposition.
> > 
> > For the inductive part, take a valid $\Sigma$-chase path $\vec{d} = ((\tau_1, \sigma_1), \ldots, (\tau_{n-1}, \sigma_{n-1}))$ on $I$, a chase-step direction $(\tau_n, \sigma_n)$ with $\vec{d} \concat (\tau_n, \sigma_n)$ being a valid $\Sigma$-chase path on $I$, and suppose that $\mathrm{map}_t(\vec{d})$ is a valid $\Sigma$-chase path on $t(I)$ with $$t(\Instance_{\SatTree_\Sigma(I)}(\vec{d})) \subseteq \Instance_{\SatTree_\Sigma(t(I))}(\mathrm{map}_t(\vec{d})).$$
> > Now $$
\begin{align}
  t(\Instance_{\SatTree_\Sigma(I)}(\vec{d} \concat (\tau_n, \sigma_n)))
    &= t(\FullSat_\Sigma(\chase_{\widehat{\#_{\vec{d} \concat (\tau, \sigma)}}}(\operatorname{SC}_{\Sigma, \vec{d}}(I), (\tau_n, \sigma_n)))) \\
    &\subseteq \FullSat_\Sigma(t(\chase_{\widehat{\#_{\vec{d} \concat (\tau, \sigma)}}}(\operatorname{SC}_{\Sigma, \vec{d}}(I), (\tau_n, \sigma_n)))) \\
    &= \FullSat_\Sigma(
      t(
        \chaseHead_{\widehat{\#_{\vec{d} \concat (\tau, \sigma)}}}(\tau_n, \sigma_n)
      ) \cup t(
        \exports_\Sigma(\operatorname{SC}_{\Sigma, \vec{d}}(I), (\tau_n, \sigma_n)
      )
    )) \\
    &= \FullSat_\Sigma(
      \chaseHead_{\widehat{\#_{\mathrm{map}_t(\vec{d} \concat (\tau, \sigma))}}}(\tau_n, t \circ \sigma_n)
      \cup t(
        \exports_\Sigma(\operatorname{SC}_{\Sigma, \vec{d}}(I), (\tau_n, \sigma_n)
      )
    )) \\
    &\subseteq \FullSat_\Sigma(
      \chaseHead_{\widehat{\#_{\mathrm{map}_t(\vec{d} \concat (\tau, \sigma))}}}(\tau_n, t \circ \sigma_n)
      \cup
        \exports_\Sigma(\operatorname{SC}_{\Sigma, \mathrm{map}_t(\vec{d})}(t(I)), (\tau_n, t \circ \sigma_n)
      )
    )) \\
    &= \Instance_{\SatTree_\Sigma(t(I))}(\mathrm{map}_t(\vec{d}) \concat (\tau_n, t \circ \sigma_n))).
\end{align}
$$

> **Corollary (facts-translation inclusion).** Let $\Sigma$ be a finite set of GTGDs, $I$ a base instance and $t: \Consts \rightarrow \Consts$ a consts translation that fixes $\consts(\Sigma)$. Then $$t(\TreeFacts(\SatTree_\Sigma(I))) \subseteq \TreeFacts(\SatTree_\Sigma(t(I))).$$
> 
> > *Proof*. Take $F \in t(\TreeFacts(\SatTree_\Sigma(I)))$. Then there is some $\tilde{F} \in \TreeFacts(\SatTree_\Sigma(I))$ with $t(\tilde{F}) = F$, and hence some valid $\Sigma$-chase path $\vec{d}$ on $I$ with $\tilde{F} \in \Instance_{\SatTree_\Sigma(I)}(\vec{d})$. As $$
\begin{align}
  F
    &= t(\tilde{F}) \\
    &\in t(\Instance_{\SatTree_\Sigma(I)}(\vec{d})) \\
    &\subseteq \Instance_{\SatTree_\Sigma(t(I))}(\mathrm{map}_t(\vec{d})),
\end{align}
$$$F \in \TreeFacts(\SatTree_\Sigma(t(I)))$.

## Universality of SatTrees

> **Fact**. Let $\Sigma$ be a finite set of GTGDs, $I$ a base instance and $Q = \exists \vec{z}. \bigwedge_{j \in J} A_j(\vec{u}_j)$ a conjunctive query. Then $$I \wedge \Sigma \models Q \Longleftrightarrow \TreeFacts(\SatTree_\Sigma(I)) \text{ witnesses } Q.$$

> **Corollary (query entailment is preserved by $\consts(\Sigma)$-fixing consts translations)**. Let $\Sigma$ be a finite set of GTGDs, $I$ a base instance, $Q = \exists \vec{x}. \bigwedge_{j \in J} A_j$ a boolean conjunctive query and $t: \Consts \rightarrow \Consts$ a consts translation that fixes $\consts(\Sigma)$.
> 
> If $I \wedge \Sigma \models Q$, then $t(I) \wedge \Sigma \models t(Q)$.
> 
> > *Proof.* Suppose $I \wedge \Sigma \models Q$. By the previous fact, there exists a factual substitution $\sigma: \elems(\vec{x}) \rightarrow \Consts \cup \Nulls$ with $\sigma(\bigwedge_{j \in J} A_j) \subseteq \TreeFacts(\SatTree_\Sigma(I))$. As $t$ fixes $\consts(\Sigma)$, by facts-translation inclusion $$
\begin{align}
  (t \circ \sigma)\left(\bigwedge_{j \in J} A_j\right)
    &\subseteq t(\TreeFacts(\SatTree_\Sigma(I))) \\
    &\subseteq \TreeFacts(\SatTree_\Sigma(t(I)))
\end{align}
$$Now, as $t \circ \sigma = (t \upharpoonright \Nulls) \circ \sigma \circ t$, we have $$
\begin{align}
  ((t \upharpoonright \Nulls) \circ \sigma \circ t) \left(
    \bigwedge_{j \in J} A_j
  \right)
    &= (t \circ \sigma)\left(\bigwedge_{j \in J} A_j\right) \\
    &\subseteq \TreeFacts(\SatTree_\Sigma(t(I))).
\end{align}
$$as $t(Q) = \exists \vec{z}. t \left(\bigwedge_{j \in J} A_j \right)$, we see that $\TreeFacts(\SatTree_\Sigma(t(I)))$ witnesses $t(Q)$ with the factual substitution $(t \upharpoonright \Nulls) \circ \sigma$. 
> >
> > By the previous fact, we conclude that $t(I) \wedge \Sigma \models t(Q)$.
