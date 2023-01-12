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

> **Proposition**. Let $\Sigma$ be a finite set of GTGDs, $I$ an instance and $t: \Consts \rightarrow \Consts$ a consts translation. Then $t(\FullSat_\Sigma(I)) \subseteq \FullSat_\Sigma(t(I))$.
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
> > So it suffices to show that $t(\Sat^k_{\Sigma_\mathrm{rew}}(I)) \subseteq \Sat^k_{\Sigma_\mathrm{rew}}(t(I))$. We proceed by induction on $k$. The base case is $t(\Sat_{\Sigma_\mathrm{rew}}^0(I)) = t(I) = \Sat_{\Sigma_\mathrm{rew}}^0(t(I))$. To see the inductive part, suppose $t(\Sat^k_{\Sigma_\mathrm{rew}}(I)) \subseteq \Sat^k_{\Sigma_\mathrm{rew}}(t(I))$. Then $$
\begin{align}
  t(\Sat^{k+1}_{\Sigma_\mathrm{rew}}(I))
    &= t(\Sat^k_\Sigma(I) \cup \set{\ \sigma(\eta) \mid (\forall \vec{x}. \beta \rightarrow \eta) \in \Sigma, \sigma \text{ covers } \vec{x}, \sigma(\beta) \subseteq \Sat^k_\Sigma(I)\ }) \\
    &= t(\Sat^k_\Sigma(I)) \cup \set{\ (t \circ \sigma)(\eta) \mid (\forall \vec{x}. \beta \rightarrow \eta) \in \Sigma, \sigma \text{ covers } \vec{x}, \sigma(\beta) \subseteq \Sat^k_\Sigma(I)\ } \\
    &\subseteq \Sat^k_\Sigma(t(I)) \cup \set{\ \sigma'(\eta) \mid (\forall \vec{x}. \beta \rightarrow \eta) \in \Sigma, \sigma' \text{ covers } \vec{x}, \sigma'(\beta) \subseteq \Sat^k_\Sigma(t(I))\ } \\
	&= \Sat^{k+1}_{\Sigma_\mathrm{rew}}(t(I))
\end{align}
$$where the third subset relation follows from the fact that if $\sigma$ covers $\vec{x} = \mathrm{FV}(\beta)$ and $\sigma(\beta) \subseteq \mathrm{Sat}^k_\Sigma(I)$, then $t \circ \sigma$ is a factual substitution covering $\vec{x}$ and $(t \circ \sigma)(\beta) \subseteq t(\Sat^k_\Sigma(I)) \subseteq \Sat^k_\Sigma(t(I))$ by induction hypothesis. 

> **Proposition**. Let $\Sigma$ be a finite set of GTGDs, $I$ a base instance and $t: \Consts \rightarrow \Consts$ a consts translation. Then for any valid $\Sigma$-chase path $\vec{d} = ((\tau_1, \sigma_1), \ldots, (\tau_n, \sigma_n))$ on $I$, $\mathrm{map}_t(\vec{d}) = ((\tau_1, t \circ \sigma_1), \ldots, (\tau_n, t \circ \sigma_n))$ is a valid $\Sigma$-chase path on $t(I)$, and moreover $$t(\Instance_{\SatTree_\Sigma(I)}(\vec{d})) \subseteq \Instance_{\SatTree_\Sigma(t(I))}(\mathrm{map}_t(\vec{d})).$$
> > *Proof*. By induction on the length of $\vec{d}$. The base case is proven in the preceding proposition.
> > 
> > For the inductive part, take a valid $\Sigma$-chase path $\vec{d} = ((\tau_1, \sigma_1), \ldots, (\tau_{n-1}, \sigma_{n-1}))$ on $I$, a chase-step direction $(\tau_n, \sigma_n)$ with $\vec{d} \concat (\tau_n, \sigma_n)$ being a valid $\Sigma$-chase path on $I$, and suppose that $\mathrm{map}_t(\vec{d})$ is a valid $\Sigma$-chase path on $t(I)$ with $$t(\Instance_{\SatTree_\Sigma(I)}(\vec{d})) \subseteq \Instance_{\SatTree_\Sigma(t(I))}(\mathrm{map}_t(\vec{d})).$$
> > Now $$
\begin{align}
  t(\Instance_{\SatTree_\Sigma(I)}(\vec{d} \concat (\tau_n, \sigma_n)))
    &= t(\FullSat_\Sigma(\chase_{\widehat{\#_{\vec{d}}}}(\operatorname{SC}_{\Sigma, \vec{d}}(I), (\tau_n, \sigma_n)))) \\
    &\subseteq \FullSat_\Sigma(t(\chase_{\widehat{\#_{\vec{d}}}}(\operatorname{SC}_{\Sigma, \vec{d}}(I), (\tau_n, \sigma_n)))) \\
    &= \FullSat_\Sigma(
      t(
        \chaseHead_{\widehat{\#_{\vec{d}}}}(\tau_n, \sigma_n)
      ) \cup t(
        \exports_\Sigma(\operatorname{SC}_{\Sigma, \vec{d}}(I), (\tau_n, \sigma_n)
      )
    )) \\
    &= \FullSat_\Sigma(
      \chaseHead_{\widehat{\#_{\vec{d}}}}(\tau_n, t \circ \sigma_n)
      \cup t(
        \exports_\Sigma(\operatorname{SC}_{\Sigma, \vec{d}}(I), (\tau_n, \sigma_n)
      )
    )) \\
    &\subseteq \FullSat_\Sigma(
      \chaseHead_{\widehat{\#_{\vec{d}}}}(\tau_n, t \circ \sigma_n)
      \cup
        \exports_\Sigma(\operatorname{SC}_{\Sigma, \mathrm{map}_t(\vec{d})}(t(I)), (\tau_n, t \circ \sigma_n)
      )
    )) \\
    &= \Instance_{\SatTree_\Sigma(t(I))}(\mathrm{map}_t(\vec{d}) \concat (\tau_n, t \circ \sigma_n))).
\end{align}
$$

> **Corollary (facts-translation inclusion).** Let $\Sigma$ be a finite set of GTGDs, $I$ a base instance and $t: \Consts \rightarrow \Consts$ a consts translation. Then $$t(\TreeFacts(\SatTree_\Sigma(I))) \subseteq \TreeFacts(\SatTree_\Sigma(t(I))).$$
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