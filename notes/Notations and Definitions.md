### MathJax Macros

$$
\newcommand\isDefinedAt[2]{{#1 \downarrow #2}}
\def\domain{{\operatorname{dom}}}

\def\elems{{\operatorname{elems}}}
\def\concat{{^\frown}}

\def\Vars{{\mathrm{Vars}}}
\def\Nulls{{\mathrm{Nulls}}}
\def\Consts{{\mathrm{Consts}}}
\def\Predicates{{\mathrm{Predicates}}}
\def\Arity{{\operatorname{Arity}}}
\def\FactualTerms{{\mathrm{FactualTerms}}}
\def\Terms{{\mathrm{Terms}}}
\def\NullableTerms{{\mathrm{NullableTerms}}}
\def\Atoms{{\mathrm{Atoms}}}
\def\Formulae{{\mathrm{Formulae}}}

\def\FactualSubstitutions{{\mathrm{FactualSubstitutions}}}

\def\Facts{{\mathrm{Facts}}}
\def\BaseFacts{{\mathrm{BaseFacts}}}
\def\Instances{{\mathrm{Instances}}}

\def\exlift{{\operatorname{Lift}_\exists}}
\def\Sat{{\operatorname{Sat}}}

\def\consts{{\operatorname{consts}}}
\def\vars{{\operatorname{vars}}}
\def\chase{{\operatorname{chase}}}
\def\chaseHead{{\operatorname{chaseHead}}}

\def\ChaseStepDir{{\operatorname{ChaseStepDir}}}
$$

### General Notations

For a formal finite sequence $(X_1, \ldots, X_n)$ of same sorts, we abbriviate it as $\vec{X}$. The set $\set{\ X_1, \ldots, X_n\ }$ will then be denoted as $\elems(\vec{X})$. We write $\vec{X'} \triangleleft \vec{X}$ to mean that $\vec{X'}$ is an initial segment of $\vec{X}$, $\vec{X'} \leq \vec{X}$ to mean that $\vec{X'}$ is a subsequence of $\vec{X}$ and $X' \subseteq X$ to mean $\elems(\vec{X'}) \subseteq \elems(\vec{X})$.

For two formal finite sequences $\vec{X}$ and $\vec{Y}$, we denote by $\vec{X} \concat \vec{Y}$ the concatenation of $\vec{X}$ and $\vec{Y}$.

A pair $(T, v_r)$ of a directed acyclic graph $T$ and a vertex $v_r \in V(T)$ is called a *directed tree rooted at $v_r$* if the underlying undirected graph of $T$ is a tree and every $v \in V(T) \setminus \set{v_r}$ has precisely one vertex $p_v \in V(T)$ such that there is an edge $(p_v, v) \in E(T)$. We shall often call $T$ a *rooted tree*.

We write $f: A \rightharpoonup B$ to mean that $f$ is a partial function from $A$ to $B$. We denote by $\domain(f)$ to mean the domain of $f$, and write $\isDefinedAt{f}{x}$ to mean that $x \in dom(f) \subseteq A$, i.e. $f$ is defined at $x \in A$.

### Logic Preliminaries

This section mainly pulls definitions from [Rewriting the Infinite Chase](https://krr-oxford.github.io/Guarded-saturation/files/p2537-benedikt-long.pdf), but with a few modifications.

We assume a countably infinite collection $\Vars = \set{x_1, x_2, x_3, \ldots}$ of variables, the ordered set $\Nulls = \set{\ n_i \mid i \in \mathbb{N}\ }$ of *labelled nulls* and some given fixed (at most countable) set $\Consts = \set{c_1, c_2, \ldots}$ of constants.

Given a finite collection $\Predicates = \set{P_1, P_2, \ldots, P_N}$ of predicates with finite arities $\Arity(P_i)$ associated to each of them (both of which we will not explicitly write from now on), we define:
 - *the set $\Terms$ of (non-null) terms* as $\Vars \cup \Consts$
 - *the set $\NullableTerms$ of nullable terms* as $\Vars \cup \Consts \cup \Nulls$
 - _the set $\FactualTerms$ of factual terms_ as $\Nulls \cup \Consts$
 - _the set $\Atoms$ of atomic formulae (resp. the set $\Facts$ of facts)_ to be a set of formal expression $P(t_1, t_2, \ldots, t_{\Arity(P)})$ with $P \in \Predicates$, $t_i \in \Terms$ (resp. $\FactualTerms$) for each $1 \leq i \leq \Arity(P)$
 - *the set $\Formulae$ of (first-order) formulas under the sigunature $(\Predicates, \Consts)$* to be a set of formal expressions inductively built up from $\Atoms$ using unary connective $\neg$, binary connectives $\wedge, \vee, \rightarrow$ and quantifiers $\exists x.$ and $\forall x.$ (where $x \in \Vars$)

Semantics (interpretation, logical-consequence relation and truth) of formulae is defined using the standard terminology. We also follow standard conventions concerning variables being *bound* and *free*.

For brevity, we adopt the following notational conventions:
  - for a an atomic formula $P(t_1, \ldots, t_{\Arity(P)})$, we simply write it as $P(\vec{t})$ with an intention that $\vec{t} = (t_1, \ldots, t_{\Arity(P)})$.
  - for a formula of a form $\exists x_1. \exists x_2. \ldots \exists x_n. \phi$, we simply write it as $\exists \vec{x}. \phi$ with an intention that $\vec{x} = (x_1, \ldots, x_n)$.

For conjunctions $F = \bigwedge_{1 \leq i \leq n} F_i$ and $G = \bigwedge_{1 \leq j \leq m} G_j$ of formulae, we write $F \subseteq G$ when for each $1 \leq i \leq n$, $F_i$ appears in $G$. That is, for each $1 \leq i \leq n$, there exists $1 \leq j \leq m$ with $F_i = G_j$.

We now define subclasses of objects defined above:
  - a fact $P(\vec{t})$ is *a base fact* if $\vec{t}$ contains only constants (hence no nulls). We write $\BaseFacts$ for the set of base facts.
  - *an instance* is a finite set of facts. We write $\Instances$ for the set $\mathcal{P}_{< \omega}(\Facts)$.
  - an instance $I$ is *a base instance* if each fact in $I$ is a base fact.
  - a formula is *a rectified formula* if no variable is bound twice, and no variable occurs both bound and free. By a standard renaming argument, any first-order formula is equivalent to a rectified formula. Hence from now on we will assume all formulae to be rectified.
  - a formula is closed when every occurence of variable is bound.
  - a closed formula is a *Tuple-Generating Dependency (or TGD)* if it is of the form $\forall \vec{x}. (\beta \rightarrow \exists \vec{y}. \eta)$ where $\beta$ and $\eta$ are conjunctions of atoms with $\eta$ nonempty. In such a formula, $\beta$ is referred to as the *body* and $\eta$ is referred to as the *head* of this TGD.
  - a TGD $\forall \vec{x}. (\beta \rightarrow \exists \vec{y}. \eta)$ is *a full TGD* if $\vec{y}$ is empty, i.e. it is of the form $\forall \vec{x}. \beta \rightarrow \eta$.
  - a full TGD is *a Datalog rule* if its head contains exactly one atom. A finite set of Datalog rules is is called *a Datalog program*.
  - a TGD is in a head-normal form if it is either a *Datalog rule*, or each atom in the head contains at least one existentially quantified variable.
  - a TGD $\forall \vec{x}. (\beta \rightarrow \exists \vec{y}. \eta)$ is a *guarded-TGD (or GTGD)* if $\beta$ contains an atom $P(\vec{t})$ such that $\vec{t} \supseteq \vec{x}$.
  - a Conjunctive Query (CQ) is a formula of the form $\exists \vec{x}. \bigwedge_i A_i$ where each $A_i$ is an atomic formula.

A *factual substitution* is a partial function $\sigma: \Vars \rightharpoonup \FactualTerms$ with a finite domain. A factual substitution canonically extends to a partial function $\Atoms \rightharpoonup \Facts$ that is defined on atoms all of whose variables are in the domain of $\sigma$. We identity this extension of $\sigma$ with $\sigma$ by an abuse of notation. We write $\FactualSubstitutions = (\Vars \rightharpoonup \FactualTerms)_{< \omega}$ for the countable set of all factual substitutions.

We say that a factual substitution $\sigma$ *covers* a set $\vec{y}$ of variables when $\elems(\vec{y}) \subseteq \domain(\sigma)$, and that $\sigma$ *covers* an atom $A$ (resp. a vector of atoms $\vec{A}$) when $\sigma$ covers the set $\vars(A)$ (resp. $\vars(\vec{A})$) of variables in $A$ (resp. $\vec{A}$).

We say that a (potentially infinite) set $\mathcal{F}$ of facts *witnesses a closed conjunctive query $\exists \vec{x}. \bigwedge_{1 \leq i \leq n} A_i$* if there exists a factual substitution $\sigma$ covering $\vec{A}$ such that $$\set{\ \sigma(A_i) \mid 1 \leq i \leq n \ } \subseteq \mathcal{F}.$$

### Rewriting, Existential Lifting and Saturation

Given a set $\Sigma$ of TGDs, a Datalog program $\Sigma_{\text{rew}}$ is *a rewriting of $\Sigma$* if for every base instance $I$, $\Sigma$ and $\Sigma_{\text{rew}}$ generate the same set of consequences, i.e. for every __base fact__ $F$, $$I \wedge \Sigma \models F \Longleftrightarrow I \wedge \Sigma_{\text{rew}} \models F.$$
Given a fact $R(\vec{f})$, the *existential lifting $\exlift(R(\vec{f}))$ of $R(\vec{f})$* is defined as the formula $$\exlift(R(\vec{f})) := \exists \vec{\nu}. R(\vec{f}[\ \vec{n} \leftarrow \vec{\nu}\ ])$$
where
 - $\vec{\nu}$ are variables corresponding to nulls in $\vec{f}$,
 - $\vec{f}[\ \vec{n} \leftarrow \vec{\nu}\ ]$ is $\vec{f}$ with nulls replaced by their corresponding variables in $\vec{\nu}$. 

The *existential lifting $\exlift(I)$ of an instance $I$* is a set $\set{\ \exlift(F) \mid F \in I\ }$ of formulae.

Given a set $\Sigma$ of TGDs and an instance $I$, the *saturation $\Sat_\Sigma(I)$ of $I$ under $\Sigma$* is the instance defined by $$\Sat_\Sigma(I) := I \cup \set{\ F \in \BaseFacts \mid \Sigma \wedge \exlift(I) \models F\ }$$ i.e. $I$ together with the set of all base facts $\Sigma$-derivable from $I$.

### Chase-Like Trees and Canonically Completed Chase-Like Trees

We shall define a tree structure that "stems from a base instance $I$ and witnesses every possible conclusion that can be $\Sigma$-deduced from $I$". To make this precise, we define a few concepts in this section. So fix a finite set $\Sigma$ of head-normal GTGDs.

We say that _a set $G$ of factual terms is $\Sigma$-guarded by a set of factual terms $\vec{t}$_ when $G \subseteq \consts(\Sigma) \cup \vec{t}$ .

Injective functions of the form $\nu: \mathbb{N} \rightarrow \Nulls$ will be referred to as *null-picking functions*. For a null-picking function $\nu$, a vector $\vec{y} = (y_1, \ldots, y_n)$ of variables and a factual substitution $\sigma$ whose domain is disjoint from $\vec{y}$, we define *the factual substitution $\sigma[\vec{y} \xrightarrow{\nu} \Nulls]$* with domain $\domain(\sigma) + \elems(\vec{y})$ that substitutes each $y_i$ to distinct nulls (chosen by $\nu$) and follows $\sigma$ elsewhere: $$
\sigma[\vec{y} \xrightarrow{\nu} \Nulls](x)=
\begin{cases}
    n_{\nu(i)} & \text{if $x = y_i$} \\
    \sigma(x) & \text{if $x \in \domain(\sigma)$}
\end{cases}$$

For a TGD $D = \forall \vec{x}. (\beta \rightarrow \exists \vec{y}. \eta)$, an instance $I$ and a factual substitution $\sigma$ that covers $\vec{x}$, we say that *$I$ can be $D$-chased with $\sigma$* when $\sigma(\beta) \subseteq I$. Intuitively, this means that the premise $\beta$ is witnessed by some facts in $I$, and $\sigma$ specifies which constant or null appearing in $I$ is witnessing each variable in $\vec{x}$.

We shall describe how an instance can be "extended" by applying a GTGD. (*Question: this is not a proper extension of $I$ because we are only taking along $\Sigma$-guarded facts to the "extension". Is there any intuition why we should we do this, or is this just a technical trick that is used to bound the size of tree-like chase proofs so as to make the decision procedure decidable? Will I get an insight about the intuition behind this limitation if I read the proof of chase-proof completeness?*) Given a null-picking function $\nu$, a GTGD $D = \forall \vec{x}. (\beta \rightarrow \exists \vec{y}. \eta)$ and an instance $I$ that can be $D$-chased with a factual substitution $\sigma$, we define
 - *the chase head $\chaseHead_\nu(D, \sigma)$* to be the fact $$\sigma[\vec{y} \xrightarrow{\nu} \Nulls](\eta).$$ Intuitively, this is a new fact generated from $I$ by applying the rule $D$.
 - *the one-step chase $\chase_\nu(I; D, \sigma)$ of $I$ with $(D, \sigma)$ (through $\nu$)* to be an instance defined by  $$\set{\chaseHead_\nu(D, \sigma)} \cup \set{\ F \in I\ |\ F \text{ is } \Sigma \text{-guarded by }\chaseHead_\nu(D, \sigma) \ }.$$

A *chase-like tree $T$ on an instance* is a directed rooted tree $(T_0, v_r)$ together with the *instance assignment* $\operatorname{Instance}_T: V(T_0) \rightarrow \Instances$ of instances to vertices.

We shall call a pair $(D, \sigma) \in \Sigma \times \FactualSubstitutions$ a *chase-step direction*, and write $\ChaseStepDir$ for the set $\Sigma \times \FactualSubstitutions$ of all chase-step directions. We call a finite (resp. infinite) sequence of chase-step directions a *finite (resp. infinite) chase-path*.

Fix a coding function (hence a computable injection into $\mathbb{N}$) $$\#: \ChaseStepDir^{< \omega} \times \mathbb{N} \rightarrow \mathbb{N}$$ on pairs of a finite chase-path and a natural. Precompose $\#$ to the canonical null-picking function $\nu_{\mathrm{id}}(i \in \mathbb{N}) = n_i$ and curry to obtain a $\ChaseStepDir^{< \omega}$-indexed family $\set{ \widehat{\#_\vec{d}}}_{\vec{d} \in \ChaseStepDir^{< \omega}}$ of null-picking functions: More explicitly, for each $\vec{d} \in \ChaseStepDir^{< \omega}$, we have $$
\begin{align}
\widehat{\#_{\vec{d}}}\ : \mathbb{N} & \rightarrow \Nulls\\
                                   i & \mapsto n_{\#(\vec{d}, i)}
\end{align}
$$
This family of null-picking functions will be used in the following definition to formally ensure that no null introduced in one branch is brought to its sibling branches.

Given a base instance $I$, define, by induction on finite chase-paths $\vec{d} \in \ChaseStepDir^{< \omega}$, the *canonical completion $\operatorname{CC}_\vec{d}(I)$ of $I$ along $\vec{d}$* by $$
\begin{align}
  \operatorname{CC}_{()}(I) &= \Sat_\Sigma(I) \\
  \operatorname{CC}_{\vec{d} \concat (D, \sigma)}(I) &=
    \begin{cases}
      \Sat_\Sigma(\chase_{\widehat{\#_{\vec{d}}}}(\operatorname{CC}_\vec{d}(I); D, \sigma)) & \text{if $\operatorname{CC}_\vec{d}(I)$ can be $D$-chased with $\sigma$} \\
      \emptyset & \text{otherwise}
    \end{cases}
\end{align}
$$
For a base instance $I$ and a finite chase-path $\vec{d}$, we say that $\vec{d}$ is *a valid chase-path on $I$* if either $\operatorname{CC}_\vec{d}(I) \neq \emptyset$ or both $I$ and $\vec{d}$ are empty.

Now define the *canonically $\Sigma$-completed chase-like tree $\operatorname{\mathrm{CCT}}_\Sigma(I)$ of a base instance $I$* with:
 - the set $(\ChaseStepDir^{< \omega})_{\mathrm{valid}}$ of *all* valid chase-paths on $I$ as the vertex set
 - (labelled) edges of the form $\vec{p} \xrightarrow{d} \vec{p} \concat (d)$ for each pair of vertices (hence valid chase-paths) $\vec{p}$ and $\vec{p} \concat (d)$
 - the instance assignment function defined by $$
\begin{array}{c c}
\operatorname{Instance}_{\operatorname{\mathrm{CCT}}_\Sigma(I)}:
  &(\ChaseStepDir^{< \omega})_{\mathrm{valid}} & \longrightarrow &\Instances \\
  &\vec{d} &\longmapsto &\operatorname{CC}_\vec{d}(I)
\end{array}
$$
