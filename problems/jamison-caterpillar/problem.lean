import Mathlib
set_option maxHeartbeats 4000000

/-!
# Jamison's caterpillar conjecture (strong "every maximizer" form)

*Source:* `jamison_journal_manuscript.md`, "Main theorem (candidate)":

> For every integer `n ≥ 1`, every tree on `n` vertices maximizing the mean order of its
> nonempty connected induced vertex subsets is a caterpillar. Consequently, for every `n`,
> a caterpillar attains the maximum mean subtree order among all `n`-vertex trees.

*References:*
 - [1] R. E. Jamison, On the average number of nodes in a subtree of a tree,
   J. Combin. Theory Ser. B 35 (1983), 207–223.
 - [4] REGS 2011 problem page, Conjecture 1 (Jamison's caterpillar conjecture).

## Conventions

* A *subtree* of a graph `G` on `V` is a nonempty vertex set `S` such that the induced
  subgraph `G[S]` is connected (manuscript §1).
* `N G` = number of subtrees, `R G` = sum of their orders, `μ G = R G / N G`.
* Trees on `n` vertices are modelled as trees on the vertex type `Fin n`. Since `μ` is
  invariant under graph isomorphism, maximizing over labelled trees on `Fin n` is the same as
  maximizing over all (unlabelled) `n`-vertex trees.
* A *caterpillar* is a tree containing a path such that every vertex lies on the path or is
  adjacent to a vertex of it. For trees this is equivalent to the manuscript's definition
  "the skeleton (subgraph induced by the non-leaf vertices) is a path, possibly empty or a
  single vertex": a non-leaf vertex off a dominating path would create a cycle, so all
  non-leaves lie on the path, and they form a contiguous sub-path (only the two endpoints of
  the path can be leaves).
-/

namespace Jamison

variable {V : Type*} [Fintype V]

/-- `S` is a subtree of `G`: a nonempty vertex set inducing a connected subgraph. -/
def IsSubtree (G : SimpleGraph V) (S : Finset V) : Prop :=
  S.Nonempty ∧ (G.induce (S : Set V)).Connected

open Classical in
/-- The finite set of all subtrees of `G`. -/
noncomputable def subtrees (G : SimpleGraph V) : Finset (Finset V) :=
  Finset.univ.filter (IsSubtree G)

/-- `N_G`: the number of subtrees of `G`. -/
noncomputable def subtreeCount (G : SimpleGraph V) : ℕ :=
  (subtrees G).card

/-- `R_G`: the sum of the orders of all subtrees of `G`. -/
noncomputable def subtreeOrderSum (G : SimpleGraph V) : ℕ :=
  ∑ S ∈ subtrees G, S.card

/-- `μ(G) = R_G / N_G`: the mean subtree order of `G`. -/
noncomputable def meanSubtreeOrder (G : SimpleGraph V) : ℚ :=
  (subtreeOrderSum G : ℚ) / (subtreeCount G : ℚ)

/-- A caterpillar: a tree with a path such that every vertex is on the path or adjacent to
a vertex on it. -/
def IsCaterpillar (G : SimpleGraph V) : Prop :=
  G.IsTree ∧
    ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧
      ∀ v : V, v ∈ p.support ∨ ∃ u ∈ p.support, G.Adj v u

/-- **Main theorem (Jamison's caterpillar conjecture, strong form).**
For every `n ≥ 1`, every tree `T` on `n` vertices whose mean subtree order is maximal among
all trees on `n` vertices is a caterpillar. -/
theorem jamison_every_maximizer_is_caterpillar (n : ℕ) (hn : 1 ≤ n)
    (T : SimpleGraph (Fin n)) (hT : T.IsTree)
    (hmax : ∀ T' : SimpleGraph (Fin n), T'.IsTree →
      meanSubtreeOrder T' ≤ meanSubtreeOrder T) :
    IsCaterpillar T := by
  sorry

end Jamison
