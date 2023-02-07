In [[Reducing Query-Rule-Rewriting Problem to BCQ Answerings]], we saw how to reduce the query-rewriting problem to exponentially many, mostly independent subproblems of BCQ answerings. While the independence allows easy parallelization of the rewrite algorithm, solving these subproblems is not at all trivial.

After the reduction, we had to solve BCQ answering problems on "small" base instances. These instances only contain generic constants, constants in rules and constants in the query, and the number of constants appearing in such instances is bounded by the sum of $|\consts(\Sigma)|$ and the maximum arity $\mathrm{maxArity}_\mathcal{L}$ of predicates in the relation schema $\mathcal{L}$ (because they are $\Sigma$-guarded by a single guard in the single rule that is supposed to fire a tentacle witnessing a subquery).

In this note, we aim to describe the basic algorithm for deciding BCQ queries over those "generic base instances".

## Problem Framing

> **Definition**. Suppose $\Sigma$ is a finite set of $\mathcal{L}$-GTGDs. An instance $I$ is $(\mathcal{L}, \Sigma)$-small if $|\consts(I) \setminus \consts(\Sigma)| + |\mathrm{nulls}(I)| \leq \mathrm{maxArity}_\mathcal{L}$. We say that a chase-like tree $(T, \Instance_T)$ is $(\mathcal{L}, \Sigma)$-small if $\Instance_T(v)$ is $(\mathcal{L}, \Sigma)$-small for every $v \in T$.

> *Remark*. If an instance $I$ is $(\mathcal{L}, \Sigma)$-small, then $$|\consts(I) \cup \mathrm{nulls}(I)| \leq \mathrm{maxArity}_\mathcal{L} + |\consts(\Sigma)|.$$

The following is the problem we need to decide.

> **Definition**. Let $\Sigma$ be a finite set of $\mathcal{L}$-GTGDs **whose existential rules are single-headed**, and $Q = \bigwedge_{j \in J} A_j(\vec{u}_j)$ a boolean conjunctive query over $\mathcal{L}$.
> 
> The problem $\mathrm{GuardedBCQOverSmallInsts}_{\Sigma, Q}$ is the set of all $(\mathcal{L}, \Sigma)$-small base instances $I$ such that $I \wedge \Sigma \models Q$.

The assumption that existential rules in $\Sigma$ must be single-headed is not a loss of generality, because given any GTGD $\tau = \forall \vec{x}. \beta \rightarrow \exists \vec{y}. \eta$ that is not necessarily single-headed, by introducing an intermediate predicate $P_\tau$ of arity $|\vec{x}| + |\vec{y}|$, we can "split" $\tau$ into two rules $\forall \vec{x}. \beta \rightarrow \exists \vec{y}.   P_\tau(\vec{x}, \vec{y})$ and $\forall \vec{x}, \vec{y}. P_\tau(\vec{x}, \vec{y}) \rightarrow \eta$.

> *Note*: We can do a bit better than $|\vec{x}| + |\vec{y}|$ for arity of $P_\tau$; in fact, $|\vars(\eta)|$ is enough (so that variables "discarded" by the rule $\tau$ do not carry over to the rule $\forall \vec{z}. P_\tau \rightarrow \eta$).

> *Question*: This splitting process unavoidably increases maximum arity in the signature, which we would like to keep as small as possible. How much can we do better if we drop this assumption and begin with the original $\Sigma$? Put more precisely, if $\Sigma$ is the original set of rules and $\Sigma'$ is the single-headed variant of $\Sigma$, does the chase of $I \wedge \Sigma$ ever have a smaller treewidth compared to the chase of $I \wedge \Sigma'$ ?

## The Strategy

To decide $\mathrm{GuardedBCQOverSmallInsts}_{\Sigma, Q}$, we shall explicitly define the class of tree structures that act as possible witnesses to instances of $\mathrm{GuardedBCQOverSmallInsts}_{\Sigma, Q}$.

Notice first the following:

> **Proposition**. If $\Sigma$ is a finite set of $\mathcal{L}$-GTGDs whose existential rules are single-headed and $I$ is a $(\mathcal{L}, \Sigma)$-small base instance, then $\SatTree_\Sigma(I)$ is $(\mathcal{L}, \Sigma)$-small.
> 
> > *Proof*. We show, by induction on $\vec{d}$, that $\Instance_{\SatTree_\Sigma(I)}(\vec{d})$ is $(\mathcal{L}, \Sigma)$-small for every node $\vec{d}$ in $\SatTree_\Sigma(I)$.
> > 
> > To see the base case, $I$ is $(\mathcal{L}, \Sigma)$-small, so $\FullSat(I) = \Instance_{\SatTree_\Sigma(I)}(())$ is also $(\mathcal{L}, \Sigma)$-small, since $\FullSat$ cannot introduce new non-$\Sigma$-constant factual terms into the instance.
> > 
> > For the inductive part, suppose $\vec{d} \concat (\tau = \forall \vec{x}. \beta \rightarrow \exists \vec{y}. H(\vec{u}), \sigma)$ is a valid generative $\Sigma$-chase path. Notice that $\tau$ is generative and single-headed, so it has a single atom $H$ in its head. By definition, $\Instance_{\SatTree_\Sigma(I)}(\vec{d} \concat (\tau, \sigma))$ is a $\FullSat$ of an instance $\Sigma$-guarded by $\chaseHead_\nu(\tau, \sigma) = H(\sigma[\vec{y} \xrightarrow{\nu} \Nulls](\vec{u}))$ for some null-picking function $\nu$. Since $H(\sigma[\vec{y} \xrightarrow{\nu} \Nulls](\vec{u}))$ contains at most $|\Arity(H)|$ factual terms, $\Instance_{\SatTree_\Sigma(I)}(\vec{d} \concat (\tau, \sigma))$ can contain at most $|\Arity(H)| \leq \mathrm{maxArity}_\mathcal{L}$ non-$\Sigma$-constant factual terms, so $\Instance_{\SatTree_\Sigma(I)}(\vec{d} \concat (\tau, \sigma))$ is $(\mathcal{L}, \Sigma)$-small.

Together with the universality of $\SatTree$s, this proposition implies that a chase-like tree with a treewidth of at most $\mathrm{maxArity}_\mathcal{L} + |\consts(\Sigma)|$, that is also a "finite prefix" of $\SatTree_\Sigma(I)$ and witnesses $Q$, is the witness of an instance of $\mathrm{GuardedBCQOverSmallInsts}_{\Sigma, Q}$, and conversely there is such a chase-like tree whenever $I \in \mathrm{GuardedBCQOverSmallInsts}_{\Sigma, Q}$.

### The Data Structure Describing Chase-Like Trees With Bounded Width

We shall temporarily move away from considering models of $I \wedge \Sigma$, and work with more general structures of (a sublanguage of) $\mathcal{L}$. We will describe a data structure, which we shall call *finite $(\mathcal{L}, k)$-tree codes*, that is able encode finite chase-like trees over (a sublanguage of) $\mathcal{L}$ with a specified maximum treewidth $k$.

We begin with the formal description of the structure. These definitions are adopted from [[Papers#`Decidable Logics via Automata`]].

> **Definition**. The first order language $\mathcal{L}^-$ is defined to be the language with no constants and the same predicate set as $\mathcal{L}$.

> **Definition**. Let $X$ be a set. The set $\mathrm{PStructuresOver}_\mathcal{L}(X)$ of *predicate structures over the set $X$* is defined to be the set of all $\mathcal{L}^-$-structures having the universe as $X$. For $\mathcal{S} \in \mathrm{StructuresOver}_\mathcal{L}(X)$, the subset $\mathrm{ActiveValues}(\mathcal{S})$ of $X$ is the set given by $$\mathrm{ActiveValues}(\mathcal{S}) = \set{ x \in X \mid (\vec{y}_1, x, \vec{y}_2) \in P_\mathcal{S} \text { for some predicate } P \text{ and } \vec{y}_1, \vec{y}_2 \subseteq X }.$$

> **Definition**. Let $k \geq 1$. A *finite $(\mathcal{L}, k)$-tree code* is a pair of a rooted tree $(T, v_0)$ and a *labelling function* $\lambda: V_T \rightarrow \mathrm{PStructuresOver}_\mathcal{L}(\overline{2k})$ where $V_T$ is the vertex tree of $T$ and $\overline{2k}$ is the set $\set{0, 1, \ldots, 2k-1}$, such that $$|\mathrm{ActiveValues}(\lambda(v))| \leq k.$$

Each finite $(\mathcal{L}, k)$-tree code encodes a finite $\mathcal{L}^-$-structure having a treewidth at most $k$, in the following sense.

> **Definition**. Let $\mathcal{C} = ((T, v_0), \lambda: V_T \rightarrow \mathrm{PStructuresOver}_\mathcal{L}(\overline{2k}))$ be a finite $(\mathcal{L}, k)$-tree code.
> 
> The set $\mathrm{GNames}(\mathcal{C})$ of *global names in $\mathcal{C}$* is the subset of $V_T \times \overline{2k}$ defined by $$
\mathrm{GNames}(\mathcal{C}) =
  \set{\ (v, n) \in V_T \times \overline{2k} \mid n \in \mathrm{ActiveValues}(\lambda(v))\ }.
$$
> We say that two global names $(v_1, n_1)$ and $(v_2, n_2)$ are *linked in $\mathcal{C}$* if $n_1 = n_2$ and $v_1$ is adjacent to $v_2$ in $T$.
> 
> Let $\sim_\mathcal{C}$ be the reflexive transitive closure of the relation "linked in $\mathcal{C}$" on $\mathrm{GNames}(\mathcal{C}) \times \mathrm{GNames}(\mathcal{C})$. The *$\mathcal{L}^-$-structure $\mathrm{Decode}(\mathcal{C})$ coded by $\mathcal{C}$* is the quotient $\mathcal{L}^-$-structure $$
\mathrm{Decode}(\mathcal{C}) := \left(
  \coprod_{v \in V_T} \lambda(v)
\right) \Bigg/ \sim_\mathcal{C}.
$$

> *Remark*. Elements in the numeral $\overline{2k}$ are often referred to as "local names", for instance in [[Papers#`Decidable Logics via Automata`]]. This is because the same local name $n \in \overline{2k}$ at two different nodes $v_1, v_2$ correspond to different global names $(v_1, n)$ and $(v_2, n)$, which in turn *may* represent distinct elements in $\mathrm{Decode}(\mathcal{C})$ when $v_1$ and $v_2$ are not adjacent in $T$.

> *Remark*. The variant used here encodes "equality between local names" (this is an abuse of notation; what we really mean is the equality of the elements in the structure encoded by the local names) in adjacent nodes *implicitly*, by asserting that two equal local names in adjacent nodes encode the same element in the original chase-like structure.
> 
> We could also demand that there are only $k$ local names, and equality between local names to be encoded by explicit *equality predicates*. This is referred to as the *explicit equality coding* in [[Papers#`Decidable Logics via Automata`]].

> *Example*. Let $\Predicates_\mathcal{L} = \set{ U, Edge }$ with arities $\Arity(U) = 1$ and $\Arity(Edge) = 2$.
> 
> Consider the following $(\mathcal{L}, k)$-tree code $\mathcal{C}$, with $k = 3$:
> 
> ![[tree-codes-example-code.drawio.svg]]
> 
> For $i \in \set{1, 2}$, the global names $(v_0, i)$ and $(v_1, i)$ are linked, so in $\mathrm{Decode}(\mathcal{C})$ will have these global names identified. Moreover, these are the only global names that form nontrivial equivalence classes of $\sim_\mathcal{C}$ (where $\sim_\mathcal{C}$ is as in the defintion of the coded structure). Therefore $\mathrm{Decode}(\mathcal{C})$ has a structure as in the following picture:
>
> ![[tree-codes-example-decoded.drawio.svg]]

### Finite Witnesses to the Problem

We now describe the condition of finite tree codes being a witness to the problem $\mathrm{GuardedBCQOverSmallInsts}_{\Sigma, Q}$.

(TODO)

### The High-Level Algorithm

(TODO: we should make clear how a certain class of finite $\mathcal{L}^-$-structure can be "reinterpreted" as a finite prefix of $\SatTree_\Sigma(I)$, which are Herbrand $\mathcal{L}^+$-structures.)

The preceding arguments motivate the following basic algorithm for deciding $\mathrm{GuardedBCQOverSmallInsts}_{\Sigma, Q}$:
   1. Build a finite tree automaton $\mathcal{A}_{\Sigma\text{-chase}}$ (the *chase automaton*) over $(\mathcal{L}, \mathrm{maxArity}_\mathcal{L} + |\consts(\Sigma)|)$-tree codes that recognizes all tree codes which encode finite prefixes of $\SatTree_\Sigma(I)$.
   2. Build another finite tree automaton $\mathcal{A}_Q$ (the *query automaton*) over $(\mathcal{L}, \mathrm{maxArity}_\mathcal{L} + |\consts(\Sigma)|)$-tree-codes that recognizes all tree codes which encode finite chase-like trees satisfying $Q$.
   3. Formally intersect $\mathcal{A}_{\Sigma\text{-chase}}$ and $\mathcal{A}_Q$ to form the product automaton $\mathcal{A}$, so that $L(\mathcal{A}) = \mathcal{A}_{\Sigma\text{-chase}} \cap \mathcal{A}_Q$.
   4. Return $L(\mathcal{A}) \neq \emptyset$.

## Construction of the Chase Automaton

## Construction of the Query Automaton
