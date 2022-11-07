---
tag:
  - notes
  - definitions
---

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
\def\FullSat{{\operatorname{FullSat}}}

\def\TreeFacts{{\operatorname{TreeFacts}}}
\def\consts{{\operatorname{consts}}}
\def\vars{{\operatorname{vars}}}
\def\chase{{\operatorname{chase}}}
\def\chaseHead{{\operatorname{chaseHead}}}
\def\rew{{\operatorname{rew}}}

\def\ChaseStepDir{{\operatorname{ChaseStepDir}}}
\def\SatTree{{\operatorname{SatTree}}}
$$

> This section defines general notations used throughout the notes.

For a formal finite sequence $(X_1, \ldots, X_n)$ of same sorts, we abbriviate it as $\vec{X}$. The set $\set{\ X_1, \ldots, X_n\ }$ will then be denoted as $\elems(\vec{X})$. We write $\vec{X'} \triangleleft \vec{X}$ to mean that $\vec{X'}$ is an initial segment of $\vec{X}$, $\vec{X'} \leq \vec{X}$ to mean that $\vec{X'}$ is a subsequence of $\vec{X}$ and $X' \subseteq X$ to mean $\elems(\vec{X'}) \subseteq \elems(\vec{X})$.

For two formal finite sequences $\vec{X}$ and $\vec{Y}$, we denote by $\vec{X} \concat \vec{Y}$ the concatenation of $\vec{X}$ and $\vec{Y}$.

A pair $(T, v_r)$ of a directed acyclic graph $T$ and a vertex $v_r \in V(T)$ is called a *directed tree rooted at $v_r$* if the underlying undirected graph of $T$ is a tree and every $v \in V(T) \setminus \set{v_r}$ has precisely one vertex $p_v \in V(T)$ such that there is an edge $(p_v, v) \in E(T)$. We shall often call $T$ a *rooted tree*.

We write $f: A \rightharpoonup B$ to mean that $f$ is a partial function from $A$ to $B$. We denote by $\domain(f)$ to mean the domain of $f$, and write $\isDefinedAt{f}{x}$ to mean that $x \in dom(f) \subseteq A$, i.e. $f$ is defined at $x \in A$.