We explorered before in [[2022-11-01 About template constraints#Constraints on Partitioning Imposed by the Query]] a few possibility on how the entire query can be witnessed by nulls in different tentacles.

Let us be more precise and formal.

**Definition**. For a vector $\vec{x}$ of distinct variables, we say that a pair $(H, \mathcal{T})$ is a _head-tentacle partition of $\vec{x}$_ when
 - $H \subseteq \elems(\vec{x})$ and $\mathcal{T} \subseteq \mathcal{P}(\elems(\vec{x}))$
 - $H \not\in \mathcal{T}$
 - Either
	 - $H = \emptyset$ and $\mathcal{T}$ is a partition (i.e. a cover of disjoint nonempty sets) of $\elems(\vec{x})$
	 - $\set{H} \cup \mathcal{T}$ is a partition of $\elems(\vec{x})$

**Definition**. For a head-tentacle partition $(H, \mathcal{T})$ of $\vec{x}$, define the corresponding _compatible cover_ $(H, \mathcal{T})_\text{cover}$ as the set $\set{ H \cup T \mid T \in \mathcal{T} }$.

**Definition**. Given a boolean conjunctive query $$Q = \exists \vec{x}. \bigwedge_{1 \leq i \leq n} A_i(\vec{v_i})$$ we say that a head-tentacle partition $(H, \mathcal{T})$ of $\vec{x}$ is _compatible with $Q$_ if, for every $1 \leq i \leq n$ and every $x_1, x_2 \in \elems(\vec{v_i})$, there exists $C \in (H, \mathcal{T})_\text{cover}$ such that $\set{x_1, x_2} \subseteq C$.

**Definition**. For finite set $\Sigma$ of GTGDs, a base instance $I$, a conjunctive query $Q = \exists \vec{x}. \bigwedge_{1 \leq i \leq n} A_i$ and a factual subsitition $\sigma$ such that $\sigma(\vec{A}) \subseteq \SatTree_\Sigma(I)$, the _witness pattern $\mathrm{Pat}_\sigma$ of $\sigma$_ is the head-tentacle paritition $(H, \mathcal{T})$ defined by $$\begin{align}
H &= \set{ x \in \elems(\vec{x}) \mid \sigma(x) \text{ is a constant}} \\
T &= (\elems(\vec{x}) \setminus H) / \sim
\end{align}$$ where $\sim$ is the equivalence relation given by $x_1 \sim x_2$ iff $\sigma(x_1)$ and $\sigma(x_2)$ appear in the same tentacle (TODO: define this precisely; it should be easy thanks to the explicit construction of $\SatTree_\Sigma(I)$).

**Claim**:  For finite set $\Sigma$ of GTGDs, a base instance $I$, a conjunctive query $Q = \exists \vec{x}. \bigwedge_{1 \leq i \leq n} A_i$ and a factual subsitition $\sigma$ such that $\sigma(\vec{A}) \subseteq \SatTree_\Sigma(I)$ (TODO: define notions so that this statement can be shortened), $\mathrm{Pat}_\sigma$ is compatible with $Q$.

---
Now that we defined notions, we can say the same thing as in [[2022-11-01 About template constraints#Constraints on Partitioning Imposed by the Query]], but more concisely:

For a query $Q = \exists xyz. R(x, y) \wedge R(y, z)$, the following are the only head-tentacle partitions compatible with $Q$:
 - $(\emptyset, \set{\set{x, y, z}})$
 - $(\set{x}, \set{\set{y, z}})$
 - $(\set{y}, \set{\set{x, z}})$
 - $(\set{y}, \set{\set{x}, \set{z}})$
 - $(\set{z}, \set{x, y})$
 - $(\set{x, y}, \set{\set{z}})$
 - $(\set{x, z}, \set{\set{y}})$
 - $(\set{y, z}, \set{\set{x}})$
 - $(\set{x, y, z}, \emptyset)$

Let us tinker with this example.

**Question.** Given a finite set $\Sigma$ of GTGDs, is $$
\left(
\Sigma \cup \left\lbrace
  \begin{aligned}
  & \forall u, v. R(u, v) \rightarrow \mathrm{Subgoal}_\mathrm{left}(v), \\
  & \forall v, w. R(v, w) \rightarrow \mathrm{Subgoal}_\mathrm{right}(v), \\
  & \forall v. \mathrm{Subgoal}_\mathrm{left}(v) \wedge \mathrm{Subgoal}_\mathrm{right}(v) \rightarrow \mathrm{Goal}^Q() \\
\end{aligned}
\right\rbrace
\right)_\mathrm{rew}
$$ a query-rule-rewriting of $(\Sigma, Q)$?

**Answer**: For each possible head-tentacle partition, we can "enrich" the $\SatTree$ by added rules and see if $\mathrm{Goal}^Q()$ can be derived using chase steps.