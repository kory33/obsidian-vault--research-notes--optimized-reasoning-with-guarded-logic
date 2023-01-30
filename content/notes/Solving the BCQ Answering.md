In [[Reducing Query-Rule-Rewriting Problem to BCQ Answerings]], we saw how to reduce the query-rewriting problem to exponentially many, mostly independent subproblems of BCQ answerings. While the independence allows easy parallelization of the rewrite algorithm, solving these subproblems is not at all trivial.

After the reduction, we had to solve BCQ answering problems on "small" base instances. These instances only contain generic constants, constants in rules and constants in the query, and the number of constants appearing in such instances is bounded by the maximum arity $\mathrm{maxArity}_\mathcal{L}$ of predicates in the relation schema $\mathcal{L}$ (because they are guarded by a single guard in the single rule that is supposed to fire a tentacle witnessing a subquery).

In this note, we aim to describe the basic algorithm for deciding BCQ queries over those "generic base instances".

## Problem Framing

> **Definition**. An instance $I$ is $\mathcal{L}$-small if $|\consts(I)| + |\mathrm{nulls}(I)| \leq \mathrm{maxArity}_\mathcal{L}$.

The following is the problem we need to decide.

> **Definition**. Let $\Sigma$ be a finite set of $\mathcal{L}$-GTGDs **whose existential rules are single-headed**, and $Q = \bigwedge_{j \in J} A_j(\vec{u}_j)$ a boolean conjunctive query over $\mathcal{L}$.
> 
> The problem $\mathrm{GuardedBCQOverSmallInsts}_{\Sigma, Q}$ is the set of all $\mathcal{L}$-small base instances $I$ such that $I \wedge \Sigma \models Q$.

The assumption that existential rules in $\Sigma$ must be single-headed will be exploited later. This assumption is not a loss of generality, because given any GTGD $\tau = \forall \vec{x}. \beta \rightarrow \exists \vec{y}. \eta$ that is not necessarily single-headed, by introducing an intermediate predicate $P_\tau$ of arity $|\vec{x}| + |\vec{y}|$, we can "split" $\tau$ into two rules $\forall \vec{x}. \beta \rightarrow \exists \vec{y}.   P_\tau(\vec{x}, \vec{y})$ and $\forall \vec{x}, \vec{y}. P_\tau(\vec{x}, \vec{y}) \rightarrow \eta$.

> *Note*: We can do a bit better than $|\vec{x}| + |\vec{y}|$ for arity of $P_\tau$; in fact, $|\vars(\eta)|$ is enough.

> *Question*: This splitting process unavoidably increases maximum arity in the signature, which we would like to keep as small as possible. How much can we do better if we drop this assumption and begin with the original $\Sigma$? More precisely put, if $\Sigma$ is the original set of rules and $\Sigma'$ is the single-headed variant of $\Sigma$, do models of $I \wedge \Sigma$ ever have a smaller treewidth compared to models of $I \wedge \Sigma'$ ?

To decide this, we shall explicitly define the class of tree structures that act as possible witnesses to instances of $\mathrm{GuardedBCQOverSmallInst}$.

Notice first the following:

> **Proposition**. If $I$ is a $\mathcal{L}$-small base instance, then for all node $\vec{d}$ in $\SatTree_\Sigma(I)$, $\Instance_{\SatTree_\Sigma(I)}(\vec{d})$ is $\mathcal{L}$-small.
> 
> > *Proof*. By induction on $\vec{d}$.
> > 
> > To see the base case, $I$ is $\mathcal{L}$-small, so $\FullSat(I) = \Instance_{\SatTree_\Sigma(I)}(())$ is also $\mathcal{L}$-small, since $\FullSat$ cannot introduce new factual terms into the instance.
> > 
> > For the inductive part, suppose $\vec{d} \concat (\tau, \sigma)$ is a valid generative $\Sigma$-chase path. Then $\Instance_{\SatTree_\Sigma(I)}(\vec{d} \concat (\tau, \sigma))$ is $\mathcal{L}$-small since it is a $\FullSat$ of an instance guarded by $\chaseHead_\nu(\tau, \sigma)$ for some null-picking function $\nu$, which again is $\mathcal{L}$-small.

Together with the universality of $\SatTree$s, this proposition suggests that a chase-like tree with a treewidth of at most $\mathrm{maxArity}_\mathcal{L}$, that is also a finite prefix of $\SatTree_\Sigma(I)$ and witnesses $Q$, is the witness of $I \in \mathrm{GuardedBCQOverSmallInsts}_{\Sigma, Q}$, and conversely there is such a chase-like tree whenever $I \in \mathrm{GuardedBCQOverSmallInsts}_{\Sigma, Q}$.

(TODO: explain what tree-codes of width $k$ are: adopt the explanation given in [[Papers#`Decidable Logics via Automata`]]).

This motivates us to consider the following basic algorithm for deciding $\mathrm{GuardedBCQOverSmallInsts}_{\Sigma, Q}$:
   1. Build a finite tree automaton $\mathcal{A}_{\Sigma\text{-chase}}$ over $\mathcal{L}$-tree-codes of width $\mathrm{maxArity}_\mathcal{L}$ that recognizes all tree codes that encode finite prefixes of $\SatTree_\Sigma(I)$.
   2. Build another finite tree automaton $\mathcal{A}_Q$ over $\mathcal{L}$-tree-codes of width $\mathrm{maxArity}_\mathcal{L}$ that recognizes all tree codes that encode chase-like trees satisfying $Q$.
   3. Formally intersect $\mathcal{A}_{\Sigma\text{-chase}}$ and $\mathcal{A}_Q$ to form the product automaton $\mathcal{A}$, so that $L(\mathcal{A}) = \mathcal{A}_{\Sigma\text{-chase}} \cap \mathcal{A}_Q$.
   4. Return $L(\mathcal{A}) \neq \emptyset$.
