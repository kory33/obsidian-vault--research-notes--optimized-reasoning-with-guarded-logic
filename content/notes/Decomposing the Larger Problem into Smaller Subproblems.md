---
title: Decomposing the Larger Problem into Smaller Subproblems
tags:
  - notes
  - idea
---

> We shall build on definitions given in [[Chase-Like Trees and Saturated Chase-Like Trees]]. We will also rely on the results in [[Preliminary Results on Saturated Chase-Like Trees]], and [[Witness Fragmentation and Witness Gluing]].

We start with the following claim, whose proof we leave to some other part of the notes:

> **Theorem (SatTree Universality)**. For any finite set of GTGDs $\Sigma$, a base instance $I$ and a binary conjunctive query $Q$, $I \wedge \Sigma \models Q$ if and only if there exists a $(\Sigma, I)$-witness for $Q$.
> 
> > *Proof*. TODO

The main problem of our concern is the following decision problem:

> **Definition**. `AnswerQuery(I, Σ, Q)` is the problem of deciding whether $I \wedge \Sigma \models Q$ holds.

Throughout this note, we shall assume that the input query $Q$ is given in a form $\exists \vec{x}. \bigwedge_{j \in J} Q_j(\vec{x'}_j)$, where $\vec{x'}_i \subseteq \vec{x}$ for each $i$.

By SatTree Universality, we can answer $I \wedge \Sigma \models Q$ by finding a $(\Sigma, I)$-witness $\sigma$ (or proving that none exists) for $Q$. By Fragmentation-Gluing Bijection, this amounts to finding a $Q$-fragmented $(\Sigma, I)$-witness $(\sigma_b, \set{\sigma'_V}_V)$ for $Q$.

To find a fragmented witness $(\sigma_b, \set{\sigma'_V}_V)$, we can nondeterministically guess $\sigma_b$ which determines the indexing set of $\set{\sigma'_V}_V$, and then nondeterministically guess each $\sigma'_V$ that sends a connected component of $\mathcal{H}(Q - \domain(\sigma_b))$ to a single tentacle. We can verify the choice for $\sigma_b$ by simply looking at $\Sat_\Sigma(I)$, and verify the choice for $\sigma'_V$ by actually computing $\SatTree_\Sigma(I)$ up until all the introduction points of nulls in $\operatorname{im}(\sigma'_V)$.

The method just described yields a nondeterministic algorithm[^1], which we shall refer to as `AnswerQueryNonDet1`, for the problem `AnswerQuery(-, -, -)`.

```
AnswerQueryNonDet1(I, Σ, Q):
  σ_base_domain <- nondeterministically guess a subset of vec{x}
  σ_base <- nondeterministically guess an assignment of constants to each variable in σ_base_domain

  masked_H := (σ_base_domain)-masked query structure hypergraph of Q
  SatBase := Sat_Σ(I)

  // check the condition for the base substitution
  for each j in J:
    if all variables in Q_j(vec{x'}_j) are in σ_base_domain:
      if σ_base(Q_j(vec{x'}_j)) ∉ SatBase:
        REJECT
      fi
    fi
  done

  // nondeterministically guess fragments
  for each V in the connected components of masked_H:
    (τ_t, σ_t) <- nondeterministically guess a valid generative chase-direction on (I, Σ)
    σ_V <- nondeterministically guess an assignment of nulls in the tentacle hanging from (τ_t, σ_t) for each variable in V

    Q'_V := conjunction of all atoms in Q that only mention variables from V or σ_base_domain
    T := compute the tree of shortcut Σ-chase along all introduction points of nulls that are in the image of σ_V

    for each Q' in σ_base(σ_V(Q'_V)):
      if NOT (Q' in some node of T):
        REJECT
      fi
    done

	// at this point, σ_V witnesses the non-existential subquery Q'_V
  done

  ACCEPT
```

This is only a semi-decision nondeterministic algorithm, since the set of choices that can be made for `σ_V` is in general infinite. It turns out that this can be fixed immediately if we suppose an oracle for the following problem:

> **Definition**. `WitnessedUnderTentacle(τ_t, σ_t, I, Σ, Q')` is the problem of deciding whether a binary conjunctive query $Q'$ is witnessed on a tentacle of $\SatTree_\Sigma(I)$ hanging from $(\tau_t, \sigma_t)$.

So now, assume that an oracle for the problem `WitnessedUnderSubTree(-, -, -, -, -)` has been given. Then successfully guessing the factual substitution `σ_V` is equivalent to `WitnessedUnderTentacle(τ_t, σ_t, I, Σ, Q'')`, where `Q''` is the existential query  $$
\begin{align}
\exists \vec{x} &= V. \bigwedge_{j \in J_{\sigma_{\text{base}, V}}} Q_j(\vec{x'}_j) \\

& \text{where } J_{\sigma_\text{base}, V} = \set{ j \in J \mid Q_j \text { contains only variables from V and }  \domain(\sigma_\text{base})}.
\end{align}
$$

Hence we have the following nondeterministic decision procedure, which we call `AnswerQueryNonDet2`, `ACCEPT`ing whenever `AnswerQueryNonDet1` does and `REJECT`ing whenever `AnswerQueryNonDet1` does not `ACCEPT`:

```diff
AnswerQueryNonDet2(I, Σ, Q):
  ...

  // nondeterministically guess fragments
  for each V in the connected components of masked_H:
    (τ_t, σ_t) <- nondeterministically guess a valid generative chase-direction on (I, Σ)

-    σ_V <- nondeterministically guess an assignment of nulls in the tentacle hanging from (τ_t, σ_t) for each variable in V
-
-    Q'_V := conjunction of all atoms in Q that only mention variables from V or σ_base_domain
-    T := compute the tree of shortcut Σ-chase along all introduction points of nulls that are in the image of σ_V
-
-    for each Q' in σ_base(σ_V(Q'_V)):
-      if NOT (Q' in some node of T):
-        REJECT
-      fi
-    done
-
-	 // at this point, σ_V witnesses the non-existential subquery Q'_V
+    A'_V := conjunction of all atoms in Q that only mention variables from V or σ_base_domain, with all variables in σ_base_domain substituted using σ_base
+    Q'_V = ∃{x in V}. σ_base(A'_V)
+    if NOT WitnessedUnderSubTree(τ_t, σ_t, I, Σ, Q'_V):
+      REJECT
+    fi
+
+    // at this point, there exists a σ_V witnessing the existential subquery Q'_V
  done

  ACCEPT
```

(TODO; explain why the following is equivalent to the previous program). We now have the following algorithm:

```diff
AnswerQueryNonDet3(I, Σ, Q):
  ...

  // nondeterministically guess fragments
  for each V in the connected components of masked_H:
    (τ_t, σ_t) <- nondeterministically guess a valid generative chase-direction on (I, Σ)

    A'_V := conjunction of all atoms in Q that only mention variables from V or σ_base_domain, with all variables in σ_base_domain substituted using σ_base
-    Q'_V = ∃{x in V}. σ_base(A'_V)
-    if NOT WitnessedUnderSubTree(τ_t, σ_t, I, Σ, Q'_V):
-      REJECT
-    fi
+    Q'_V = ∃{x in V}. A'_V // has variables in σ_base_domain free
+    if NOT σ_base IN AnswerNonBooleanQuery(GenericInstance(Abst_Σ(τ_t, σ_t; I)), Σ, Q'_V):
+      REJECT
+    fi

-    // at this point, there exists a σ_V witnessing the existential subquery Q'_V
+    // at this point, there exists a σ_V witnessing the existential subquery σ_base_domain(Q'_V)
  done

  ACCEPT
```

The next algorithm much more redundant than `AnswerQueryNonDet3`, but is still equivalent:

```diff
AnswerQueryNonDet4(I, Σ, Q):
  ...

  // nondeterministically guess fragments
  for each V in the connected components of masked_H:
    (τ_t, σ_t) <- nondeterministically guess a valid generative chase-direction on (I, Σ)

    A'_V := conjunction of all atoms in Q that only mention variables from V or σ_base_domain, with all variables in σ_base_domain substituted using σ_base
    Q'_V = ∃{x in V}. A'_V // has variables in σ_base_domain free
-    if NOT σ_base IN AnswerNonBooleanQuery(GenericInstance(Abst_Σ(τ_t, σ_t; I)), Σ, Q'_V):
-      REJECT
-    fi
+    T <- nondeterministically guess a Σ-tentacle ejection template
+    if NOT T is applicable to SatBase:
+      REJECT
+    fi
+    if NOT σ_base IN AnswerNonBooleanQuery(GenericInstance(T), Σ, Q'_V):
+      REJECT
+    fi

    // at this point, there exists a σ_V witnessing the existential subquery Q'_V
  done

  ACCEPT
```

## Towards a query-rule rewriting

(TODO: do all the theory work in [[Tentacle Ejection Templates]], and leave in this note just the following algorithm.)

Therefore, we obtain the following rewriting algorithm:

 1. Let $\Sigma_\mathrm{rew}$ be a Datalog rewriting of $\Sigma$.
 2. Let $\Sigma' \leftarrow \emptyset$ be a mutable variable of new full TGD rules
 3. Let $\mathcal{H}(Q) = (\mathcal{V}, \mathcal{E})$ be the query structure hypergraph of $Q$
 4. For each connected sub-hypergraph $V$ of vertices in $\mathcal{H}(Q)$, do the following:
	 1. Let $\partial V$ be the boundary of $V$, and let $\mathrm{Subgoal_V}$ be a new $|\partial V|$-ary predicate symbol associated with $V$.
	 2. Let $\exists \vec{V}. Q_V$ be the subquery of $Q$ induced by $V$.
	 3. For each $\Sigma$-tentacle ejection template $T = (\tau = \forall \vec{x}. (\beta \rightarrow \exists \vec{y}. \eta) \in \Sigma, \sim_\tau, F_\tau)$, do:
		 1. For every possible $T$-generic constant mapping $\sigma: \partial V \rightarrow {\sim}_\tau$, do:
			 1. If $(T, \sigma)$ generically $\Sigma$-proves $\exists \vec{V}. Q_V$, then
				 1. Add a full TGD rule $F_\tau \rightarrow \mathrm{Subgoal}_V(\partial V)$ to $\Sigma'$.
 5. Let $\mathrm{Goal}$ be the 0-ary goal predicate. 
 6. For each subset $V \subseteq \mathcal{V}$, do the following:
	 1. Let $\set{C_i}_{i \in I_V}$ be the set of connected components of $\mathcal{H}(Q-V)$.
	 2. Let $\mathrm{Goal}_V$ be a new $|V|$-ary predicate symbol associated with $V$.
	 3. Add a full TGD rule $(\bigwedge_{i \in I_V} \mathrm{Subgoal}_{C_i}(\partial C_i)) \rightarrow \mathrm{Goal_V}(V)$ to $\Sigma'$.
	 4. Add a full TGD rule $\mathrm{Goal_V}(V) \rightarrow \mathrm{Goal}()$ to $\Sigma'$.
 7. Return $\Sigma_\mathrm{rew} \cup \Sigma'$ as a query-rule-rewriting of $(\Sigma, Q)$.

[^1]: In a sense of an algorithm running on nondeterministic turing machines, so `ACCEPT`s if *any* nondeterministic branch `ACCEPT`s, and `REJECT`s if *no* nondeterministic branch `ACCEPT`s.