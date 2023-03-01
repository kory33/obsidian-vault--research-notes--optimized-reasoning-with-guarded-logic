---
title: The Dynamic Programming Algorithm
tags:
  - notes
---

## Preliminaries

We begin with some preliminary notions.

> **Definition**. Let $\mathcal{H} = (\mathcal{V}_\mathcal{H}, \mathcal{E}_\mathcal{H})$ be a hypergraph.
> 
> For a set $V \subseteq \mathcal{V}_\mathcal{H}$ of vertices, we define
>   - the *strict $\mathcal{H}$-neighbourhood $\mathrm{nbhd}_\mathcal{H}(V)$ of $V$* as the set $$\mathrm{nbhd}_\mathcal{H}(V) = \set{\ v \in \mathcal{V}_\mathcal{H} \mid \exists E \in \mathcal{E}_\mathcal{H}. v \in E \ } \setminus V$$

> **Definition**. Let $Q = \exists \vec{z}. \bigwedge_{j \in J} A_j(\vec{u}_j)$ be a boolean conjunctive query.
> 
> The *query-structure hypergraph $\mathcal{H}(Q)$* of $Q$ is the hypergraph having one vertex for each element in $\vec{z}$ and one hyperedge spanning $\vars(\vec{u}_j)$ for each $j \in J$.
> 
> For $V \subseteq \elems(\vec{z})$, we define
>   - the *set $\mathrm{relv}_Q(V)$ of $V$-relevant atom indices in $Q$* to be the set $$\mathrm{relv}_Q(V) := \set{\ j \in J \mid \vars(\vec{u}_j) \cap V \neq \emptyset \ }$$
>   - the *set $\mathrm{clidx}_Q(V)$ of $V$-closed atom indices in $Q$ to be the set* $$\mathrm{clidx}_Q(V) := \set{\ j \in J \mid \vars(\vec{u}_j) \subseteq V \ }$$
>   - the *subquery $\mathrm{ind}_V(Q)$ strictly induced by $V$* to be the boolean conjunctive query $$\mathrm{ind}_V(Q) := \exists \vec{V}. \bigwedge_{j \in \mathrm{clidx}_Q(V)}A_j(\vec{u}_j)$$
>   - the *$V$-masked query structure hypergraph $\mathcal{H}(Q-V)$* to be the hypergraph that can be obtained by weakly deleting all vertices in $V$ from $\mathcal{H}_V$ and then removing all empty hyperedges.

> **Definition**. Let $\Sigma$ be a finite set of GTGDs.
> 
> A boolean conjunctive query $Q = \exists \vec{z}. \bigwedge_{j \in J} A_j(\vec{u}_j)$ is
>   - *fully $\Sigma$-existential* if $\consts(Q) \subseteq \consts(\Sigma)$, and for each $j \in J$, $\vars(\vec{u}_j) \neq \emptyset$
>   - *connected* if $\mathcal{H}(Q)$ is a connected hypergraph
> 

> **Definition**. Let $\mathcal{L}$ be a language and $\Sigma$ a finite set of TGDs.
> 
> For a set $D$ with $D \cap \consts(\Sigma) = \emptyset$, we write $D^{+\Sigma}$ for the set $D \cup \consts(\Sigma)$. A set of formal terms of the form $F(d_0, d_1, \ldots, d_{\Arity_\mathcal{L}(F) - 1})$ with $d \in (D^{+\Sigma})^{\Arity_\mathcal{L}(F)}$ is said to be a *$\Sigma$-formal instance over $D$*. In particular, a ground instance (resp. an instance) is a $\Sigma$-formal instance over $\Consts_\mathcal{L} \setminus \consts(\Sigma)$ (resp. $\Nulls_\mathcal{L} \cup (\Consts_\mathcal{L} \setminus \consts(\Sigma))$). By an abuse of notation, we treat generic $\Sigma$-formal instances just like ordinary instances.
> 
> For a $\Sigma$-formal instance $I$ over $D$, *the set $\mathrm{ActiveValues}_D(I)$ of $D$-active values* is the set defined by $$
\mathrm{ActiveValues}_D(I) = \set{\ 
  d \in D \mid
    \exists F(\vec{e}) \in I. d \in \elems(\vec{e})
\ }.$$
> We say that a $\Sigma$-formal instance $I$ over a set $D$ is $(\mathcal{L}, \Sigma)$-small if $|\consts(I) \setminus \consts(\Sigma)| \leq \mathrm{maxArity}_\mathcal{L}$.

## The Algorithm

Now we describe the structure that will be used in describing the DP algorithm.

> **Definition**. Let $\mathcal{L}$ be a language, $\Sigma$ be a set of $\mathcal{L}$-GTGDs with single-headed existential rules, $Q = \exists \vec{z}. \bigwedge_{j \in J} A_j(\vec{u}_j)$ a connected fully $\Sigma$-existential boolean $\mathcal{L}$-conjunctive query.
> 
> Let $\mathrm{LocalConsts}_\mathcal{L} = \set{0, \ldots, 2 \times \mathrm{maxArity}_\mathcal{L} - 1}$.
> 
> The set $\mathrm{RuleConstGuess}_{\Sigma, Q}$ *of guesses of $\Sigma$-constant substitutions* is the partial function space $$
\mathrm{RuleConstGuess}_{Q, \Sigma} :=
  \elems(\vec{z}) \rightharpoonup \consts(\Sigma).
$$
> 
> For $\sigma_\Sigma \in \mathrm{RuleConstGuess}_{\Sigma, Q}$, the set $\mathrm{Conn}_{Q-\sigma_\Sigma}$ of *$Q$-connected set of variables unassigned by $\sigma_\Sigma$* is the set of all $\mathcal{H}(Q - \mathrm{dom}(\sigma_\Sigma))$-connected subsets of $\elems(\vec{z}) \setminus \mathrm{dom}(\sigma_\Sigma) = \mathcal{V}_{\mathcal{H}(Q - \mathrm{dom}(\sigma_\Sigma))}$.
> 
> The set $\mathrm{LocalInst}_{\mathcal{L}, \Sigma}$ of *$\Sigma$-saturated local instances* is the set of all $\Sigma$-formal instances $I$ over $\mathrm{LocalConsts}_\mathcal{L}$ such that $\FullSat_\Sigma(I) = I$.
> 
> For $\sigma_\Sigma \in \mathrm{RuleConstGuess}_{\Sigma, Q}$, $V \in \mathrm{Conn}_{Q-\sigma_\Sigma}$ and $I \in \mathrm{LocalInst}_{\mathcal{L}, \Sigma}$, the *set $\mathrm{NbhdSubsts}_{\sigma_\Sigma, V, I}$ of $V$-neighbourhood local substitutions into $I$* is the function space $$
\mathrm{NbhdSubsts}_{\sigma_\Sigma, V, I} :=
  {\mathrm{nbhd}_{\mathcal{H}(Q - \mathrm{dom}(\sigma_\Sigma))}(V)}
    \rightarrow
  (\mathrm{ActiveValues}_{\mathrm{LocalConsts}_\mathcal{L}}(I)).
$$
>
> Finally, the *problem space $\mathrm{SubqueryEntailmentInstances}_{\Sigma, Q}$ of subquery entailments* is defined to be the dependent sum $$
\sum_{\substack{
  \sigma_\Sigma \in \mathrm{RuleConstGuess}_{\Sigma, Q} \\
  I \in \mathrm{LocalInst}_{\mathcal{L}, \Sigma}
}}
\sum_{V \in \mathrm{Conn}_{Q-\sigma_\Sigma}}
  \mathrm{NbhdSubsts}_{\sigma_\Sigma, V, I}
$$

We now consider the following recursively defined problem $\mathrm{SubqueryEntailments}_{\Sigma, Q} \subseteq \mathrm{SubqueryEntailmentInstances}_{\Sigma, Q}$

> **Definition**. Let $\mathcal{L}$ be a language, $\Sigma$ be a set of $\mathcal{L}$-GTGDs with single-headed existential rules, $Q = \exists \vec{z}. \bigwedge_{j \in J} A_j(\vec{u}_j)$ a connected fully $\Sigma$-existential boolean $\mathcal{L}$-conjunctive query with $\consts(Q) \subseteq \consts(\Sigma)$. Let $\mathcal{H}(Q)$ be the query structure hypergraph of $Q$.
> 
> Let $\mathrm{SubqueryEntailments}_{\Sigma, Q}$ be the set of 4-tuples $$\langle \sigma_\Sigma, V, I, \sigma_\text{local} \rangle \in \mathrm{SubqueryEntailmentInstances}_{\Sigma, Q}$$such that either
>   - $V = \emptyset$, or
>   - If $\mathcal{I}_{W_\Sigma}(I, \sigma_\text{local}) \subseteq \mathrm{LocalInst}_{\mathcal{L}, \Sigma}$ is the set of *all* $\Sigma$-saturated local instances over $\mathrm{LocalConsts}_\mathcal{L}$ that can be obtained from $I$ by applying finitely many existential rules in $\Sigma$ without dropping any local name in $\operatorname{im}(\sigma_\text{local})$, then there is some $I_\text{below} \in \mathcal{I}_{W_\Sigma}(I, \sigma_\text{local})$ (which we shall call *successful branching point under $\langle \sigma_\Sigma, V, I, \sigma_\text{local} \rangle$*) and a *nonempty* partial local substitution $\sigma_\text{new}: V \rightharpoonup \mathrm{ActiveValues}_{\mathrm{LocalConsts}_\mathcal{L}}(I_\text{below})$ on $V$ satisfying the following *branching conditions at $I_\text{below}$*:
>       - for every $j \in J$, if $\vars(\vec{u}_j) \subseteq \operatorname{dom}(\sigma_\Sigma \cup \sigma_\text{local} \cup \sigma_\text{new})$ and $\vars(\vec{u}_j) \cap \operatorname{dom}(\sigma_\text{new}) \neq \emptyset$, then $A_j((\sigma_\Sigma \cup \sigma_\text{local} \cup \sigma_\text{new})(\vec{u}_j)) \in I_\text{below}$, and
>       - for every connected component $V_\text{split}$ of $\mathcal{H}(\mathrm{ind}_V(Q) - \operatorname{dom}(\sigma_\text{new}))$, $$\langle \sigma_\Sigma, V_\text{split}, I_\text{below}, (\sigma_\text{local} \cup \sigma_\text{new}) \upharpoonright \mathrm{nbhd}_{\mathcal{H}(Q - \mathrm{dom}(\sigma_\Sigma)))}(V_\text{split}) \rangle {} \in \mathrm{SubqueryEntailments}_{\Sigma, Q}.$$

> *Remark*. The definition of $\mathrm{SubqueryEntailments}_{\Sigma, Q}$ is recursive on the size of $V \in \mathrm{Conn}_{Q - \sigma_\Sigma}$, and the set $$
\sum_{
  I_\text{below} \in
    \mathcal{I}_{W_\Sigma}(I, \sigma_\text{local})
} (
  V \rightharpoonup 
    \mathrm{ActiveValues}_{\mathrm{LocalConsts}_\mathcal{L}}(I_\text{below})
)
$$of all recursion branches can be computed in a finite amount of time. In particular, $\mathrm{SubqueryEntailments}_{\Sigma, Q}$ can be decided.

As the name suggests, the problem $\mathrm{SubqueryEntailments}_{\Sigma, Q}$ precisely models the query entailment problem.

> **Theorem ($\mathrm{SubqueryEntailments}_{\Sigma, Q}$ is Equivalent to Subquery Entailment)**.
> Let $\mathcal{L}$ be a language, $\Sigma$ be a set of $\mathcal{L}$-GTGDs with single-headed existential rules, $Q = \exists \vec{z}. \bigwedge_{j \in J} A_j(\vec{u}_j)$ a connected fully $\Sigma$-existential boolean $\mathcal{L}$-conjunctive query with $\consts(Q) \subseteq \consts(\Sigma).$
> 
> Then for every 4-tuple $$\langle \sigma_\Sigma, V, I, \sigma_\text{local} \rangle \in \mathrm{SubqueryEntailmentInstances}_{\Sigma, Q},$$we have $$
\left(
  I \wedge \Sigma \models
    \exists \overrightarrow{V}.
      \bigwedge_{j \in \mathrm{relv}_Q(V)}
        A_j((\sigma_\Sigma \cup \sigma_\text{local})(\vec{u}_j))
\right) \Longleftrightarrow \langle
    \sigma_\Sigma, V, I, \sigma_\text{local}
  \rangle \in \mathrm{SubqueryEntailments}_{\Sigma, Q}.
$$
>
> > *Proof*.
> > ($\Longrightarrow$, "completeness"): (TODO)
> > 
> > ($\Longleftarrow$, "soundness"): We proceed by induction on $|V|$. Suppose $\langle \sigma_\Sigma, V, I, \sigma_\text{local} \rangle \in \mathrm{SubqueryEntailments}_{\Sigma, Q}$.
> > 
> > If $V = \emptyset$, $\exists \overrightarrow{V}. \bigwedge_{j \in \mathrm{relv}_Q(V)} A_j((\sigma_\Sigma \cup \sigma_\text{local})(\vec{u}_j)) \equiv \top$ so we are done.
> > 
> > So assume $V \neq \emptyset$. By definition of $\mathrm{SubqueryEntailments}_{\Sigma, Q}$, there exists a successful branching point $I_\text{below} \in \mathcal{I}_{W_\Sigma}(I, \sigma_\text{local})$ under $\langle \sigma_\Sigma, V, I, \sigma_\text{local} \rangle$ and a nonempty $\sigma_\text{new}: V \rightharpoonup \mathrm{ActiveValues}_{\mathrm{LocalConsts}_\mathcal{L}}(I_\text{below})$ satisfying branching conditions at $I_\text{below}$.
> > 
> > Let $\set{ V'_i }_{i \in \overline{N}}$ be the family of connected components of $\mathcal{H}(\mathrm{ind}_V(Q) - \operatorname{dom}(\sigma_\text{new}))$, indexed by the set $\overline{N} = \set{0, 1, \ldots, N - 1}$.
> > 
> > For each $i \in \overline{N}$, $V'_i \subsetneq V$, and $$\langle \sigma_\Sigma, V'_i, I_\text{below}, (\sigma_\text{local} \cup \sigma_\text{new}) \upharpoonright \mathrm{nbhd}_{\mathcal{H}(Q)}(V'_i) \rangle {} \in \mathrm{SubqueryEntailments}_{\Sigma, Q}$$by the branching condition. Applying the inductive hypothesis to $V'_i$, we have $$
I_\text{below} \wedge \Sigma \models
  \exists \overrightarrow{V'_i}.
    \bigwedge_{j \in \mathrm{relv}_Q(V'_i)}
      A_j((\sigma_\Sigma \cup \sigma_\text{local} \cup \sigma_\text{new})(\vec{u}_j)).
$$
> >
> > Collectively, we have $$
\begin{align}
I_\text{below} \wedge \Sigma
  &\models
    \bigwedge_{i \in \overline{N}}
      \exists \overrightarrow{V'_i}.
        \bigwedge_{j \in \mathrm{relv}_Q(V'_i)}
          A_j((\sigma_\Sigma \cup \sigma_\text{local} \cup \sigma_\text{new})(\vec{u}_j)) \\
  &\equiv
    \exists \overrightarrow{V'_0}, \ldots, \overrightarrow{V'_{N-1}}.
      \bigwedge_{i \in \overline{N}}
      \bigwedge_{j \in \mathrm{relv}_Q(V'_i)}
        A_j((\sigma_\Sigma \cup \sigma_\text{local} \cup \sigma_\text{new})(\vec{u}_j)) \\
  &\equiv
    \exists \overrightarrow{V'_0}, \ldots, \overrightarrow{V'_{N-1}}.
      \bigwedge_{j \in \bigcup_{i \in \overline{N}} \mathrm{relv}_Q(V'_i)}
        A_j((\sigma_\Sigma \cup \sigma_\text{local} \cup \sigma_\text{new})(\vec{u}_j)).
\end{align}
$$We claim the following:
> >
> > > **Claim**. If $j \in \mathrm{relv}_Q(V) \setminus \bigcup_{i \in \overline{N}} \mathrm{relv}_Q(V'_i)$, then $\vars(\vec{u}_j) \subseteq \operatorname{dom}(\sigma_\Sigma \cup \sigma_\text{local} \cup \sigma_\text{new})$ and $\vars(\vec{u}_j) \cap \operatorname{dom}(\sigma_\text{new}) \neq \emptyset$.
> > > 
> > > > *Proof*. Take any $j \in \mathrm{relv}_Q(V) \setminus \bigcup_{i \in \overline{N}} \mathrm{relv}_Q(V'_i)$. Then $\vars(\vec{u}_j) \cap V \neq \emptyset$ as $j \in \mathrm{relv}_Q(V)$, and $\vars(\vec{u}_j) \cap \bigcup_{i \in \overline{N}} V'_i = \emptyset$ as $j \not\in \mathrm{relv}_Q(V'_i)$ for each $i \in \overline{N}$.
> > > > 
> > > > Since $\bigcup_{i \in \overline{N}} V'_i = V \setminus \mathrm{dom}(\sigma_\text{new})$ by definition of $\set{ V'_i }_{i \in \overline{N}}$, $\vars(\vec{u}_j) \cap (V \setminus \mathrm{dom}(\sigma_\text{new})) = \emptyset$ and thus $\vars(\vec{u}_j) \cap V \subseteq \mathrm{dom}(\sigma_\text{new})$. Since $\vars(\vec{u}_j) \cap V \neq \emptyset$, we have $\vars(\vec{u}_j) \cap \mathrm{dom}(\sigma_\text{new}) \neq \emptyset$. It now remains to see $\vars(\vec{u}_j) \subseteq \operatorname{dom}(\sigma_\Sigma \cup \sigma_\text{local} \cup \sigma_\text{new})$.
> > > > 
> > > > As $\vars(\vec{u}_j) \cap V \neq \emptyset$, we have $\vars(\vec{u}_j) \subseteq V \cup \mathrm{nbhd}_{\mathcal{H}(Q)}(V)$. As $V \cap \mathrm{dom}(\sigma_\Sigma) = \emptyset$, $\mathrm{nbhd}_{\mathcal{H}(Q)}(V) = \mathrm{dom}(\sigma_\Sigma) \cup \mathrm{nbhd}_{\mathcal{H}(Q - \mathrm{dom}(\sigma_\Sigma))}(V)$. Therefore $$
\begin{align}
  \vars(\vec{u}_j)
    &\subseteq V \cup \mathrm{nbhd}_{\mathcal{H}(Q)}(V) \\
    &= V \cup \mathrm{dom}(\sigma_\Sigma) \cup \mathrm{nbhd}_{\mathcal{H}(Q - \mathrm{dom}(\sigma_\Sigma))}(V) \\
    &= V \cup \mathrm{dom}(\sigma_\Sigma) \cup \mathrm{dom}(\sigma_\text{local}).
\end{align}
$$Combined with $\vars(\vec{u}_j) \cap V \subseteq \mathrm{dom}(\sigma_\text{new})$, we have $\vars(\vec{u}_j) \subseteq \operatorname{dom}(\sigma_\Sigma \cup \sigma_\text{local} \cup \sigma_\text{new})$ as required.
> > 
> > Now, by the previous claim and the branching condition satisfied by $I_\text{below}$ and $\sigma_\text{new}$, we have $$
I_\text{below} \models
  \bigwedge_{j \in \mathrm{relv}_Q(V) \setminus \bigcup_{i \in \overline{N}} \mathrm{relv}_Q(V'_i)}
    A_j((\sigma_\Sigma \cup \sigma_\text{local} \cup \sigma_\text{new})(\vec{u}_j)).
$$Therefore $$
\begin{align}
  I_\text{below} \wedge \Sigma
    &\models
      \exists \overrightarrow{V'_0}, \ldots, \overrightarrow{V'_{N-1}}.
        \bigwedge_{j \in \mathrm{relv}_Q(V)}
          A_j((\sigma_\Sigma \cup \sigma_\text{local} \cup \sigma_\text{new})(\vec{u}_j))
\end{align},
$$and existentially quantifying away all variables in $\operatorname{dom}(\sigma_\text{new})$, we obtain $$
\begin{align}
  I_\text{below} \wedge \Sigma
    &\models
      \exists \overrightarrow{V'_0}, \ldots, \overrightarrow{V'_{N-1}}, \overrightarrow{\operatorname{dom}(\sigma_\text{new})}.
        \bigwedge_{j \in \mathrm{relv}_Q(V)}
          A_j((\sigma_\Sigma \cup \sigma_\text{local})(\vec{u}_j)) \\
    &\equiv
      \exists \overrightarrow{V}.
        \bigwedge_{j \in \mathrm{relv}_Q(V)}
          A_j((\sigma_\Sigma \cup \sigma_\text{local})(\vec{u}_j))
\end{align}
$$as desired. (TODO: in some way "$I \wedge \Sigma \models I_\text{below}$". To formalize this we need to properly talk about the model encoded by "local instance tree"s with implicit equality codings... After we concluded "$I \wedge \Sigma \models I_\text{below}$", we can conclude that $I \wedge \Sigma$ models the RHS of the last expression.)

## Translating Generic BCQ Answering Problems to Subquery Entailments

The following procedure allows us to reduce arbitrary BCQ answering problem to an instance of $\mathrm{SubqueryEntailments}_{\Sigma, -}$. We begin with some definitions.

> **Definition**. Let $Q = \exists \vec{z}. \bigwedge_{j \in J} A_j(\vec{u}_j)$ be an arbitrary boolean conjunctive query. We define $CC(Q)$ to be the set of $\mathcal{H}(Q)$-connected components.

> *Remark*. For each $V \in CC(Q)$, $\mathrm{ind}_V(Q)$ is a connected BCQ.

> **Definition**. Let $\Sigma$ be a finite set of GTGDs and $I \in \mathrm{LocalInst}_{\mathcal{L}, \Sigma}$. Let $Q = \exists \vec{z}. \bigwedge_{j \in J} A_j(\vec{u}_j)$ a connected boolean conjunctive query.
> 
> We say that for $Q$ *can be lifted to a fully $\Sigma$-existential query over $I$* if $\consts(Q) \setminus \consts(\Sigma) \subseteq \mathrm{ActiveValues}(I)$. When this is the case, we define the *fully $\Sigma$-existential lift $\mathrm{Lift_{\Sigma, I}(Q)}$ of $Q$ over $I$* to be the pair $\langle Q_\mathrm{lifted}, \sigma_\mathrm{lifted} \rangle$ with $$Q_\text{lifted} := \exists \vec{z}. \exists \vec{z'} \bigwedge_{j \in J} A_j(\vec{u'}_j)$$and$$
\begin{array}{}
  &\sigma_\text{lifted}: &\elems(\vec{z'}) &\longrightarrow &\mathrm{ActiveValues}(I) \\
  & &z'_i &\longmapsto &c_i
\end{array}
$$where $$
\begin{align}
  \vec{z'} &:= \set{ z'_1, \ldots z'_n } \text{ are fresh variables}, \\
  \set{ c_1, c_2, \ldots, c_n } &\text{ is an enumeration of } \consts(Q) \setminus \consts(\Sigma), \\
  \vec{u'}_j &\text{'s are } \vec{u}_j \text{'s except } c_i \text{'s are replaced with } z'_i \text{'s}.
\end{align}
$$

> **Proposition**. Let $\Sigma$ be a finite set of GTGDs, $I \in \mathrm{LocalInst}_{\mathcal{L}, \Sigma}$, and $Q$ a connected boolean conjunctive query. Then $I \wedge \Sigma \models Q$ if and only if $\langle Q_\text{lifted} = \exists \vec{z''}. \bigwedge_{j \in J} A_j(\vec{u'}_j), \sigma_\text{lifted} \rangle = \mathrm{Lift}_{\Sigma, I}(Q)$ exists, and there exists $\sigma_\Sigma: \elems(\vec{z''}) \rightharpoonup \mathrm{ActiveValues}(I)$ such that for each $\mathcal{H}(Q_\text{lifted} - \mathrm{dom}(\sigma_\Sigma)))$-connected component $V$, $\langle \sigma_\Sigma, V, I, \sigma_\text{lifted} \upharpoonright _{\mathrm{nbhd}_\mathcal{H}(Q_\text{lifted} - \mathrm{dom}(\sigma_\Sigma))(V)} \rangle$ is an element of $\mathrm{SubqueryEntailments}_{\Sigma, Q}$.
> 
> > *Proof*.
> > ($\Longrightarrow$): (TODO)
> >
> > ($\Longleftarrow$): (TODO)

## Monotonicity of Subquery Entailments

As $\mathrm{SubqueryEntailments}_{\Sigma, Q}$ is Equivalent to Subquery Entailment, it has certain monotonicity properties.

> **Definition**. (TODO: define a partial order $\preceq$ on $\sum_{\substack{V \in \mathrm{Conn}_Q \\ I \in \mathrm{LocalInst}_{\mathcal{L}, \Sigma}}} \mathrm{NbhdSubsts}_{V, I}$ so that $\mathrm{SubqueryEntailments}_{\Sigma, Q}$ is downward-closed in $\sum_{\substack{V \in \mathrm{Conn}_Q \\ I \in \mathrm{LocalInst}_{\mathcal{L}, \Sigma}}} \mathrm{NbhdSubsts}_{V, I}$)

> **Proposition**. $\mathrm{SubqueryEntailments}_Q$ is a downward-closed subset of $\langle \sum_{\substack{V \in \mathrm{Conn}_Q \\ I \in \mathrm{LocalInst}_{\mathcal{L}, \Sigma}}} \mathrm{NbhdSubsts}_{V, I}, \preceq \rangle$.

## Using Subquery Entailments for Rewriting
