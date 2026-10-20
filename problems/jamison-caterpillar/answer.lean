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
noncomputable def subtreesIn {V : Type*} [Fintype V]
    (G : SimpleGraph V) (U : Finset V) : Finset (Finset V) :=
  open Classical in (subtrees G).filter (fun S => S ⊆ U)


noncomputable def rootedSubtreesIn {V : Type*} [Fintype V]
    (G : SimpleGraph V) (U : Finset V) (r : V) : Finset (Finset V) :=
  open Classical in (subtrees G).filter (fun S => S ⊆ U ∧ r ∈ S)


noncomputable def rootedCount {V : Type*} [Fintype V]
    (G : SimpleGraph V) (U : Finset V) (r : V) : ℕ :=
  (rootedSubtreesIn G U r).card


noncomputable def rootedOrderSum {V : Type*} [Fintype V]
    (G : SimpleGraph V) (U : Finset V) (r : V) : ℕ :=
  ∑ S ∈ rootedSubtreesIn G U r, S.card


def IsLeafIn {V : Type*} (G : SimpleGraph V) (x u : V) : Prop :=
  ∀ v : V, G.Adj x v ↔ v = u


def IsLeafPacket {V : Type*} (G : SimpleGraph V) (L : Finset V) (u : V) : Prop :=
  ∀ x ∈ L, IsLeafIn G x u


def IsBridgeJoin {V : Type*} (G : SimpleGraph V) (U₁ U₂ : Finset V) (r₁ r₂ : V) : Prop :=
  Disjoint U₁ U₂ ∧ r₁ ∈ U₁ ∧ r₂ ∈ U₂ ∧ G.Adj r₁ r₂ ∧
    ∀ u ∈ U₁, ∀ v ∈ U₂, G.Adj u v → u = r₁ ∧ v = r₂


def HasLeafAtDegTwo {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  4 ≤ Fintype.card V ∧
  ∃ x u w : V, x ≠ w ∧
    IsLeafIn G x u ∧
    (∀ v : V, G.Adj u v ↔ v = x ∨ v = w)


def HasInternalPacketSuffix {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ (ℓ a k : ℕ) (H L_a L_k : Finset V) (w₀ : V) (v : Fin (ℓ + 1) → V),
    1 ≤ ℓ ∧ 1 ≤ a ∧ 2 ≤ k ∧
    Function.Injective v ∧
    IsSubtree G H ∧
    L_a.card = a ∧ L_k.card = k ∧
    Disjoint H (Finset.univ.image v) ∧ Disjoint H L_a ∧ Disjoint H L_k ∧
    Disjoint (Finset.univ.image v) L_a ∧ Disjoint (Finset.univ.image v) L_k ∧ Disjoint L_a L_k ∧
    H ∪ (Finset.univ.image v) ∪ L_a ∪ L_k = Finset.univ ∧
    IsBridgeJoin G H ((Finset.univ.image v) ∪ L_a ∪ L_k) w₀ (v 0) ∧
    (∀ i j : Fin (ℓ + 1), G.Adj (v i) (v j) ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val)) ∧
    IsLeafPacket G L_a (v 0) ∧
    IsLeafPacket G L_k (v (Fin.last ℓ)) ∧
    (2 ^ a * (ℓ + 2 ^ k)) ^ 2 ≤ rootedCount G H w₀ ∧
    (2 ^ a * (ℓ + 2 ^ k)) * rootedOrderSum G H w₀ ≤ (rootedCount G H w₀) ^ 2


def HasTerminalCherryBranch {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ (w u ℓ₁ ℓ₂ : V) (H : Finset V),
    ℓ₁ ≠ ℓ₂ ∧ u ≠ ℓ₁ ∧ u ≠ ℓ₂ ∧
    H = Finset.univ \ ({u, ℓ₁, ℓ₂} : Finset V) ∧
    IsSubtree G H ∧
    IsBridgeJoin G H ({u, ℓ₁, ℓ₂} : Finset V) w u ∧
    IsLeafIn G ℓ₁ u ∧ IsLeafIn G ℓ₂ u ∧
    (∀ v : V, G.Adj u v ↔ v = w ∨ v = ℓ₁ ∨ v = ℓ₂) ∧
    ((∃ (A B : Finset V) (z : V),
        H = A ∪ B ∧ IsSubtree G A ∧ IsSubtree G B ∧
        IsBridgeJoin G A B w z ∧
        120 * rootedOrderSum G A w ≤
          25 * (rootedCount G A w) ^ 2 + 48 * rootedCount G A w) ∨
     (∃ (L_c B C : Finset V) (r_B r_C : V),
        w ∉ L_c ∧ L_c.card ≤ 1 ∧ IsLeafPacket G L_c w ∧
        Disjoint (insert w L_c) B ∧ Disjoint (insert w L_c) C ∧ Disjoint B C ∧
        H = (insert w L_c) ∪ B ∪ C ∧
        IsSubtree G B ∧ IsSubtree G C ∧
        IsBridgeJoin G (insert w L_c) B w r_B ∧
        IsBridgeJoin G ((insert w L_c) ∪ B) C w r_C ∧
        4 ≤ rootedCount G B r_B ∧ 4 ≤ rootedCount G C r_C))


def HasCountDominatedBroom {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ (ℓ k : ℕ) (A B C L_k : Finset V) (w r_B r_C : V) (v : Fin (ℓ + 1) → V),
    ((1 ≤ ℓ ∧ 2 ≤ k) ∨ (ℓ = 0 ∧ 3 ≤ k)) ∧
    Function.Injective v ∧
    IsSubtree G A ∧ IsSubtree G B ∧ IsSubtree G C ∧
    L_k.card = k ∧
    Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧
    Disjoint (A ∪ B ∪ C) (Finset.univ.image v) ∧ Disjoint (A ∪ B ∪ C) L_k ∧
    Disjoint (Finset.univ.image v) L_k ∧
    A ∪ B ∪ C ∪ (Finset.univ.image v) ∪ L_k = Finset.univ ∧
    IsBridgeJoin G A B w r_B ∧
    IsBridgeJoin G (A ∪ B) C w r_C ∧
    IsBridgeJoin G (A ∪ B ∪ C) ((Finset.univ.image v) ∪ L_k) w (v 0) ∧
    (∀ i j : Fin (ℓ + 1), G.Adj (v i) (v j) ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val)) ∧
    IsLeafPacket G L_k (v (Fin.last ℓ)) ∧
    ℓ + 2 ^ k ≤ rootedCount G B r_B ∧
    ℓ + 2 ^ k ≤ rootedCount G C r_C
def reattachLeaf {V : Type*} (G : SimpleGraph V) (x w : V) (hxw : x ≠ w) : SimpleGraph V where
  Adj a b := (a ≠ x ∧ b ≠ x ∧ G.Adj a b) ∨ (a = x ∧ b = w) ∨ (a = w ∧ b = x)
  symm _ _ h := by
    rcases h with ⟨ha, hb, hab⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hb, ha, G.symm hab⟩
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  loopless a h := by
    rcases h with ⟨_, _, haa⟩ | ⟨rfl, h⟩ | ⟨h, rfl⟩
    · exact G.loopless a haa
    · exact hxw h
    · exact hxw h
def IsMinCountTerminalArm {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (ℓ : ℕ) (A₀ B C P : Finset V) (w r_B r_C : V)
    (v : Fin (ℓ + 1) → V) (L : Fin (ℓ + 1) → Finset V) : Prop :=
  2 ≤ (L (Fin.last ℓ)).card ∧
  Function.Injective v ∧
  IsSubtree G A₀ ∧ IsSubtree G B ∧ IsSubtree G C ∧ IsSubtree G P ∧
  Disjoint A₀ B ∧ Disjoint A₀ C ∧ Disjoint B C ∧ Disjoint (A₀ ∪ B ∪ C) P ∧
  A₀ ∪ B ∪ C ∪ P = Finset.univ ∧
  P = (Finset.univ.image v) ∪ (Finset.univ.biUnion L) ∧
  Disjoint (Finset.univ.image v) (Finset.univ.biUnion L) ∧
  (∀ i j : Fin (ℓ + 1), i ≠ j → Disjoint (L i) (L j)) ∧
  IsBridgeJoin G A₀ B w r_B ∧
  IsBridgeJoin G (A₀ ∪ B) C w r_C ∧
  IsBridgeJoin G (A₀ ∪ B ∪ C) P w (v 0) ∧
  (∀ i j : Fin (ℓ + 1), G.Adj (v i) (v j) ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val)) ∧
  (∀ i : Fin (ℓ + 1), IsLeafPacket G (L i) (v i)) ∧
  rootedCount G P (v 0) ≤ rootedCount G B r_B ∧
  rootedCount G P (v 0) ≤ rootedCount G C r_C
def IsDoubleBroomSuffix {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (m p q : ℕ) (H L_p L_q : Finset V) (w₀ : V) (v : Fin (m + 1) → V) : Prop :=
  Function.Injective v ∧
  IsSubtree G H ∧
  L_p.card = p ∧ L_q.card = q ∧
  Disjoint H (Finset.univ.image v) ∧ Disjoint H L_p ∧ Disjoint H L_q ∧
  Disjoint (Finset.univ.image v) L_p ∧ Disjoint (Finset.univ.image v) L_q ∧ Disjoint L_p L_q ∧
  H ∪ (Finset.univ.image v) ∪ L_p ∪ L_q = Finset.univ ∧
  IsBridgeJoin G H ((Finset.univ.image v) ∪ L_p ∪ L_q) w₀ (v 0) ∧
  (∀ i j : Fin (m + 1), G.Adj (v i) (v j) ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val)) ∧
  IsLeafPacket G L_p (v 0) ∧
  IsLeafPacket G L_q (v (Fin.last m))


def doubleBroomCount (NH sH m p q : ℕ) : ℚ :=
  let r : ℚ := (2 : ℚ) ^ p
  let z : ℚ := (2 : ℚ) ^ q
  let mQ : ℚ := m
  let pQ : ℚ := p
  let qQ : ℚ := q
  let sD : ℚ := r * (mQ + z)
  let ND : ℚ := pQ + qQ + r * z + mQ * (r + z) + mQ * (mQ - 1) / 2
  (NH : ℚ) + ND + (sH : ℚ) * sD


def doubleBroomOrderSum (RH sH tH m p q : ℕ) : ℚ :=
  let r : ℚ := (2 : ℚ) ^ p
  let z : ℚ := (2 : ℚ) ^ q
  let mQ : ℚ := m
  let pQ : ℚ := p
  let qQ : ℚ := q
  let sD : ℚ := r * (mQ + z)
  let tD : ℚ := r * mQ * (mQ + 1) / 2 + r * pQ * mQ / 2 + r * z * (mQ + 1 + (pQ + qQ) / 2)
  let RD : ℚ := pQ + qQ + r * z * (mQ + 1 + (pQ + qQ) / 2) +
    mQ * (mQ + 1) / 2 * (r + z) + mQ / 2 * (r * pQ + z * qQ) +
    (mQ - 1) * mQ * (mQ + 1) / 6
  (RH : ℚ) + RD + (tH : ℚ) * sD + (sH : ℚ) * tD
def armPrefixHost {V : Type*} [Fintype V] [DecidableEq V]
    (ℓ : ℕ) (A₀ B C : Finset V) (v : Fin (ℓ + 1) → V) (L : Fin (ℓ + 1) → Finset V)
    (j : ℕ) : Finset V :=
  A₀ ∪ B ∪ C ∪
    (Finset.univ.filter (fun i : Fin (ℓ + 1) => i.val < j)).biUnion
      (fun i => insert (v i) (L i))


def armPrefixRoot {V : Type*} (ℓ : ℕ) (w : V) (v : Fin (ℓ + 1) → V)
    (j : ℕ) (hj : j ≤ ℓ + 1) : V :=
  if h : j = 0 then w else v ⟨j - 1, by omega⟩
def IsBranchAt {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (U : Finset V) (w r : V) : Prop :=
  IsSubtree G U ∧ IsBridgeJoin G (Finset.univ \ U) U w r


def IsThreeBranchAt {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (w r_P r_B r_C : V) (P B C : Finset V) : Prop :=
  r_P ≠ r_B ∧ r_P ≠ r_C ∧ r_B ≠ r_C ∧
  IsBranchAt G P w r_P ∧ 2 ≤ P.card ∧
  IsBranchAt G B w r_B ∧ 2 ≤ B.card ∧
  IsBranchAt G C w r_C ∧ 2 ≤ C.card


def IsTerminalArm {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P : Finset V) (w : V) (ℓ : ℕ) (v : Fin (ℓ + 1) → V) (L : Fin (ℓ + 1) → Finset V) : Prop :=
  IsBranchAt G P w (v 0) ∧
  2 ≤ (L (Fin.last ℓ)).card ∧
  Function.Injective v ∧
  P = (Finset.univ.image v) ∪ (Finset.univ.biUnion L) ∧
  Disjoint (Finset.univ.image v) (Finset.univ.biUnion L) ∧
  (∀ i j : Fin (ℓ + 1), i ≠ j → Disjoint (L i) (L j)) ∧
  (∀ i j : Fin (ℓ + 1), G.Adj (v i) (v j) ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val)) ∧
  (∀ i : Fin (ℓ + 1), IsLeafPacket G (L i) (v i))
noncomputable def unrootedCount {V : Type*} [Fintype V]
    (G : SimpleGraph V) (U : Finset V) : ℕ :=
  (subtreesIn G U).card

noncomputable def unrootedOrderSum {V : Type*} [Fintype V]
    (G : SimpleGraph V) (U : Finset V) : ℕ :=
  ∑ S ∈ subtreesIn G U, S.card
noncomputable def broomThreshold (ℓ k : ℕ) : ℚ :=
  let z : ℚ := (2 : ℚ) ^ k
  let ρ : ℚ := (ℓ : ℚ) + z
  let χ : ℚ := (k : ℚ) * z / (2 * (z - 1))
  if ℓ = 0 then χ
  else (ℓ : ℚ) + χ - 3 * ((ℓ : ℚ) - 1) / (2 * (ρ + 1))

noncomputable def broomInsertionScore
    (p x y ℓ k : ℕ) (c u v d : ℚ) : ℚ :=
  let b : ℕ := (k + 1) / 2
  let z : ℚ := (2 : ℚ) ^ k
  let L : ℚ := (2 : ℚ) ^ b
  let J : ℚ := (2 : ℚ) ^ (k - b)
  let h : ℚ := (ℓ : ℚ) + 1
  let xp : ℚ := (x : ℚ)
  let yp : ℚ := (y : ℚ)
  let pp : ℚ := (p : ℚ)
  let t_P : ℚ := (ℓ : ℚ) * ((ℓ : ℚ) + 1) / 2 + z * (h + (k : ℚ) / 2)
  let dN_avoid : ℚ := ((h + 1) * L - 1) * xp + (J - 1) * yp - h * (z - 1)
  let c_xy_0 : ℚ := d * h - (ℓ : ℚ) * ((ℓ : ℚ) + 1) / 2
  let c_x_0 : ℚ := d * (h + z - L) + L * (h + (b : ℚ) / 2) - t_P
  let c_y_0 : ℚ := d * (h + z - (h + 1) * J) + J * (h * (h + 1) + (h + 1) * ((k - b : ℕ) : ℚ)) / 2 - t_P
  let c_1_0 : ℚ := d * (z - 1) + h * (h + 1) / 2 - t_P
  let sig_root : ℚ := c_xy_0 * xp * yp + c_x_0 * xp + c_y_0 * yp + c_1_0
    + (1 + J * yp) * (L - h - 1) * u + (1 + h + L * xp) * (J - 1) * v
  let dR_avoid_0 : ℚ := L * (h + 1) * (h + (b : ℚ)) / 2 * xp
    + J * ((k - b : ℕ) : ℚ) / 2 * yp - h * (h + 1) * (z - 1) / 2 - z * (k : ℚ) * h / 2
  let sig_avoid_0 : ℚ := dR_avoid_0 - (1 + d) * dN_avoid
    + ((h + 1) * L - 1 - (J - 1) * yp + h * (z - 1)) * u
    + (J - 1 - ((h + 1) * L - 1) * xp + h * (z - 1)) * v
  pp * sig_root + sig_avoid_0 - (c / 2) * dN_avoid
def relocatePacket {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S : Finset V) (w : V)
    (hw : w ∉ S) : SimpleGraph V where
  Adj a b := (a ∉ S ∧ b ∉ S ∧ G.Adj a b) ∨ (a ∈ S ∧ b = w) ∨ (a = w ∧ b ∈ S)
  symm _ _ h := by
    rcases h with ⟨ha, hb, hab⟩ | ⟨ha, rfl⟩ | ⟨rfl, hb⟩
    · exact Or.inl ⟨hb, ha, G.symm hab⟩
    · exact Or.inr (Or.inr ⟨rfl, ha⟩)
    · exact Or.inr (Or.inl ⟨hb, rfl⟩)
  loopless a h := by
    rcases h with ⟨_, _, haa⟩ | ⟨ha, rfl⟩ | ⟨rfl, ha⟩
    · exact G.loopless a haa
    · exact hw ha
    · exact hw ha
def reattachBridge {V : Type*} (G : SimpleGraph V) (w r_B v_last : V)
    (h_ne : v_last ≠ r_B) : SimpleGraph V where
  Adj a b :=
    (¬ (a = w ∧ b = r_B) ∧ ¬ (a = r_B ∧ b = w) ∧ G.Adj a b) ∨
    (a = v_last ∧ b = r_B) ∨ (a = r_B ∧ b = v_last)
  symm _ _ h := by
    rcases h with ⟨h1, h2, hab⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨fun ⟨hr, hw⟩ => h2 ⟨hw, hr⟩, fun ⟨hw, hr⟩ => h1 ⟨hr, hw⟩, G.symm hab⟩
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  loopless a h := by
    rcases h with ⟨_, _, haa⟩ | ⟨rfl, h⟩ | ⟨h, rfl⟩
    · exact G.loopless a haa
    · exact h_ne h
    · exact h_ne h
def cherryB (x U : ℚ) : ℚ :=
  (3 / 2 * x + 1) * (x + 1) * U - x * (x + 5) / 4

def cherryF1Hat (x y U V : ℚ) : ℚ :=
  let S := 2 * (1 + x) * (1 + y)
  let q_hat := 17 / 6 + x * U + y * V
  4 / 3 * S - cherryB x U * (q_hat - (x + 1) * U)
    - cherryB y V * (q_hat - (y + 1) * V) - 7 * q_hat + 11

def cherryB0 (x β : ℚ) : ℚ :=
  (3 / 2 * x + 1) * β - x * (x + 5) / 4

def cherryF0Tilde (x y β γ : ℚ) : ℚ :=
  let S := (1 + x) * (1 + y)
  let S1 := x * y + x + y
  let Q0 := 7 / 3 * S1 + x * (y + 1) * β + y * (x + 1) * γ
  S1 * (4 / 3 * S - 4) - 11 * (x * (y + 1) * β + y * (x + 1) * γ)
    - cherryB0 x β * (Q0 - S1 * β) - cherryB0 y γ * (Q0 - S1 * γ)

def cherryBivarQuad (Cuu Cuv Cvv Lu Lv C0 u v : ℚ) : ℚ :=
  Cuu * u ^ 2 - Cuv * u * v + Cvv * v ^ 2 + Lu * u + Lv * v + C0

theorem non_caterpillar_has_three_branches : ∀ (n : ℕ) (hn : 1 ≤ n) (T : SimpleGraph (Fin n)),
    T.IsTree → ¬ IsCaterpillar T →
    ∃ (w r_P r_B r_C : Fin n) (P B C : Finset (Fin n)),
      IsThreeBranchAt T w r_P r_B r_C P B C :=
by
  intro n hn T hT h_not_cat
  
  have h_max_path : ∃ (a b : Fin n) (p : T.Walk a b), p.IsPath ∧
      ∀ (a' b' : Fin n) (p' : T.Walk a' b'), p'.IsPath → p'.length ≤ p.length := by
    let α := Σ (a b : Fin n), T.Walk a b
    let S : Set α := {s | s.2.2.IsPath}
    have hS_ne : S.Nonempty := ⟨⟨⟨0, hn⟩, ⟨0, hn⟩, SimpleGraph.Walk.nil⟩, SimpleGraph.Walk.IsPath.nil⟩
    obtain ⟨⟨a, b, p⟩, hp, hmin⟩ := (measure (fun s : α => n - s.2.2.length)).wf.has_min S hS_ne
    refine ⟨a, b, p, hp, fun a' b' p' hp' => ?_⟩
    have hlen : p'.support.length ≤ Fintype.card (Fin n) := hp'.support_nodup.length_le_card
    rw [SimpleGraph.Walk.length_support, Fintype.card_fin] at hlen
    have hle : n - p.length ≤ n - p'.length := not_lt.mp (hmin ⟨a', b', p'⟩ hp')
    omega
  obtain ⟨a, b, p, hp, hmax⟩ := h_max_path
  
  have hx_exists : ∃ x : Fin n, x ∉ p.support ∧ ∀ u ∈ p.support, ¬ T.Adj x u := by
    by_contra h_all
    push_neg at h_all
    apply h_not_cat
    refine ⟨hT, a, b, p, hp, fun v => ?_⟩
    by_cases hv : v ∈ p.support
    · exact Or.inl hv
    · exact Or.inr (h_all v hv)
  obtain ⟨x, hx_not_mem, hx_not_adj⟩ := hx_exists
  
  have h_path_to_supp : ∃ (w : Fin n) (q : T.Walk x w),
      w ∈ p.support ∧ q.IsPath ∧ 2 ≤ q.length ∧
      (∀ z ∈ q.support, z ∈ p.support → z = w) := by
    obtain ⟨q₀⟩ := hT.isConnected.preconnected x a
    have hq₁ : q₀.bypass.IsPath := q₀.bypass_isPath
    have ha_mem : a ∈ p.support := p.start_mem_support
    have aux : ∀ {u d : Fin n} (r : T.Walk u d), d ∈ p.support → r.IsPath →
        ∃ (w : Fin n) (q : T.Walk u w),
          w ∈ p.support ∧ q.IsPath ∧ q.support ⊆ r.support ∧
          (∀ z ∈ q.support, z ∈ p.support → z = w) := by
      intro u d r
      induction r with
      | nil =>
        intro hd _
        refine ⟨_, SimpleGraph.Walk.nil, hd, SimpleGraph.Walk.IsPath.nil, List.Subset.refl _, ?_⟩
        intro z hz _
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
        exact hz
      | @cons u v d hadj r' ih =>
        intro hd hr
        rw [SimpleGraph.Walk.cons_isPath_iff] at hr
        by_cases hu : u ∈ p.support
        · refine ⟨u, SimpleGraph.Walk.nil, hu, SimpleGraph.Walk.IsPath.nil, ?_, ?_⟩
          · intro z hz
            simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
            subst hz
            exact SimpleGraph.Walk.start_mem_support _
          · intro z hz _
            simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
            exact hz
        · obtain ⟨w, q', hw, hq'_path, hq'_sub, hq'_inter⟩ := ih hd hr.1
          have hu_not_q' : u ∉ q'.support := fun h => hr.2 (hq'_sub h)
          have hq_path : (SimpleGraph.Walk.cons hadj q').IsPath := by
            rw [SimpleGraph.Walk.cons_isPath_iff]
            exact ⟨hq'_path, hu_not_q'⟩
          refine ⟨w, SimpleGraph.Walk.cons hadj q', hw, hq_path, ?_, ?_⟩
          · intro z hz
            simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz ⊢
            exact hz.elim Or.inl (fun h => Or.inr (hq'_sub h))
          · intro z hz hzp
            simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
            rcases hz with rfl | hz'
            · exact False.elim (hu hzp)
            · exact hq'_inter z hz' hzp
    obtain ⟨w, q, hw, hq_path, _, hq_inter⟩ := aux q₀.bypass ha_mem hq₁
    refine ⟨w, q, hw, hq_path, ?_, hq_inter⟩
    match q with
    | .nil => exact False.elim (hx_not_mem hw)
    | .cons hadj .nil => exact False.elim (hx_not_adj w hw hadj)
    | .cons _ (.cons _ q'') =>
      simp only [SimpleGraph.Walk.length_cons]
      omega
  obtain ⟨w, q, hw, hq, hq_len, hq_inter⟩ := h_path_to_supp
  
  have append_path : ∀ {c : Fin n} (γ : T.Walk w c),
      γ.IsPath → γ.support ⊆ p.support → (q.append γ).IsPath := by
    intro c γ hγ hγ_sub
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append, List.nodup_append]
    refine ⟨hq.support_nodup, (List.tail_sublist γ.support).nodup hγ.support_nodup, ?_⟩
    intro z hzq y hytail hzy
    subst hzy
    have hzp : z ∈ p.support := hγ_sub ((List.tail_sublist γ.support).subset hytail)
    have hzw : z = w := hq_inter z hzq hzp
    rw [hzw] at hytail
    have hnodup : (w :: γ.support.tail).Nodup := by
      rw [← SimpleGraph.Walk.support_eq_cons]
      exact hγ.support_nodup
    exact (List.nodup_cons.mp hnodup).1 hytail
  have two_step : ∀ {u c : Fin n} (γ : T.Walk u c),
      γ.IsPath → 2 ≤ γ.length →
      ∃ (r y : Fin n), r ∈ γ.support.tail ∧ T.Adj u r ∧ T.Adj r y ∧ y ≠ u := by
    intro u c γ hγ hlen
    match γ with
    | .nil =>
      simp only [SimpleGraph.Walk.length_nil] at hlen
      omega
    | .cons _ .nil =>
      simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at hlen
      omega
    | .cons hadj₁ (.cons hadj₂ γ') =>
      rw [SimpleGraph.Walk.cons_isPath_iff] at hγ
      refine ⟨_, _, ?_, hadj₁, hadj₂, ?_⟩
      · simp only [SimpleGraph.Walk.support_cons, List.tail_cons, List.mem_cons, true_or]
      · intro hyu
        apply hγ.2
        rw [SimpleGraph.Walk.support_cons, List.mem_cons]
        right
        rw [← hyu]
        exact γ'.start_mem_support
  let p_a := p.takeUntil w hw
  let p_b := p.dropUntil w hw
  have hp_eq : p_a.append p_b = p := SimpleGraph.Walk.take_spec p hw
  have hp_len : p_a.length + p_b.length = p.length := by
    rw [← SimpleGraph.Walk.length_append, hp_eq]
  have hp_a : p_a.IsPath := hp.takeUntil hw
  have hp_b : p_b.IsPath := hp.dropUntil hw
  have hp_a_sub : p_a.support ⊆ p.support := SimpleGraph.Walk.support_takeUntil_subset p hw
  have hp_b_sub : p_b.support ⊆ p.support := SimpleGraph.Walk.support_dropUntil_subset p hw
  have hqb_path : (q.append p_b).IsPath := append_path p_b hp_b hp_b_sub
  have hqb_le : (q.append p_b).length ≤ p.length := hmax x b (q.append p_b) hqb_path
  rw [SimpleGraph.Walk.length_append] at hqb_le
  have hp_a_rev_sub : p_a.reverse.support ⊆ p.support := by
    intro z hz
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
    exact hp_a_sub hz
  have hqa_path : (q.append p_a.reverse).IsPath := append_path p_a.reverse hp_a.reverse hp_a_rev_sub
  have hqa_le : (q.append p_a.reverse).length ≤ p.length := hmax x a (q.append p_a.reverse) hqa_path
  rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse] at hqa_le
  have hlen_q_rev : 2 ≤ q.reverse.length := by
    rw [SimpleGraph.Walk.length_reverse]
    exact hq_len
  have hlen_pa_rev : 2 ≤ p_a.reverse.length := by
    rw [SimpleGraph.Walk.length_reverse]
    omega
  have hlen_pb : 2 ≤ p_b.length := by omega
  obtain ⟨r₁, y₁, hr₁_mem, hadj_wr₁, hadj_r₁y₁, hy₁_ne⟩ := two_step q.reverse hq.reverse hlen_q_rev
  obtain ⟨r₂, y₂, hr₂_mem, hadj_wr₂, hadj_r₂y₂, hy₂_ne⟩ := two_step p_a.reverse hp_a.reverse hlen_pa_rev
  obtain ⟨r₃, y₃, hr₃_mem, hadj_wr₃, hadj_r₃y₃, hy₃_ne⟩ := two_step p_b hp_b hlen_pb
  have hr₁_q : r₁ ∈ q.support := by
    have h₁ : r₁ ∈ q.reverse.support := (List.tail_sublist q.reverse.support).subset hr₁_mem
    rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at h₁
  have hr₁_not_p : r₁ ∉ p.support := by
    intro hr₁_p
    have h_eq : r₁ = w := hq_inter r₁ hr₁_q hr₁_p
    exact T.ne_of_adj hadj_wr₁ h_eq.symm
  have hr₂_pa : r₂ ∈ p_a.support := by
    have h₂ : r₂ ∈ p_a.reverse.support := (List.tail_sublist p_a.reverse.support).subset hr₂_mem
    rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at h₂
  have hr₂_p : r₂ ∈ p.support := hp_a_sub hr₂_pa
  have hr₃_p : r₃ ∈ p.support := hp_b_sub ((List.tail_sublist p_b.support).subset hr₃_mem)
  have hne₁₂ : r₁ ≠ r₂ := fun h => hr₁_not_p (h ▸ hr₂_p)
  have hne₁₃ : r₁ ≠ r₃ := fun h => hr₁_not_p (h ▸ hr₃_p)
  have hne₂₃ : r₂ ≠ r₃ := by
    have hnodup : (p_a.support ++ p_b.support.tail).Nodup := by
      rw [← SimpleGraph.Walk.support_append, hp_eq]
      exact hp.support_nodup
    exact (List.nodup_append.mp hnodup).2.2 r₂ hr₂_pa r₃ hr₃_mem
  
  have branch_of_step : ∀ (r y : Fin n), T.Adj w r → T.Adj r y → y ≠ w →
      ∃ U : Finset (Fin n), IsBranchAt T U w r ∧ 2 ≤ U.card := by
    intro r y hadj_wr hadj_ry hy_ne
    classical
    let U : Finset (Fin n) := Finset.univ.filter (fun z => ∃ p_z : T.Walk r z, s(w, r) ∉ p_z.edges)
    have mem_U : ∀ z : Fin n, z ∈ U ↔ ∃ p_z : T.Walk r z, s(w, r) ∉ p_z.edges := by
      intro z
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
    have hr_U : r ∈ U := (mem_U r).mpr ⟨SimpleGraph.Walk.nil, by simp⟩
    have hw_not_U : w ∉ U := by
      rw [mem_U]
      rintro ⟨p_w, hp_w⟩
      have hbr : T.IsBridge s(r, w) :=
        SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.IsAcyclic hadj_wr.symm
      have hmem : s(r, w) ∈ p_w.edges :=
        (SimpleGraph.isBridge_iff_adj_and_forall_walk_mem_edges.mp hbr).2 p_w
      rw [Sym2.eq_swap] at hmem
      exact hp_w hmem
    have hw_sdiff : w ∈ Finset.univ \ U :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw_not_U⟩
    have walk_ind : ∀ {u_a u_b : Fin n} (p_ab : T.Walk u_a u_b) (ha : u_a ∈ U) (hb : u_b ∈ U),
        s(w, r) ∉ p_ab.edges → (T.induce (U : Set (Fin n))).Reachable ⟨u_a, ha⟩ ⟨u_b, hb⟩ := by
      intro u_a u_b p_ab
      induction p_ab with
      | nil =>
        intro ha hb _
        exact SimpleGraph.Reachable.rfl
      | @cons u_a u_c u_b hadj_ac q_cb ih =>
        intro ha hb hp_edges
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons, not_or] at hp_edges
        have hc : u_c ∈ U := by
          obtain ⟨p_a, hp_a⟩ := (mem_U u_a).mp ha
          refine (mem_U u_c).mpr ⟨p_a.append (SimpleGraph.Walk.cons hadj_ac SimpleGraph.Walk.nil), ?_⟩
          rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
            List.mem_append, List.mem_singleton, not_or]
          exact ⟨hp_a, hp_edges.1⟩
        have hadj_ind : (T.induce (U : Set (Fin n))).Adj ⟨u_a, ha⟩ ⟨u_c, hc⟩ := hadj_ac
        exact (SimpleGraph.Adj.reachable hadj_ind).trans (ih hc hb hp_edges.2)
    have hU_sub : IsSubtree T U := by
      refine ⟨⟨r, hr_U⟩, @SimpleGraph.Connected.mk _ _ (fun u_a u_b => ?_) ⟨⟨r, hr_U⟩⟩⟩
      have reach_r : ∀ z : {z // z ∈ (U : Set (Fin n))},
          (T.induce (U : Set (Fin n))).Reachable ⟨r, hr_U⟩ z := by
        rintro ⟨z, hz⟩
        obtain ⟨p_z, hp_z⟩ := (mem_U z).mp hz
        exact walk_ind p_z hr_U hz hp_z
      exact (reach_r u_a).symm.trans (reach_r u_b)
    have hU_bridge : IsBridgeJoin T (Finset.univ \ U) U w r := by
      refine ⟨disjoint_sdiff_self_left, hw_sdiff, hr_U, hadj_wr, fun u hu v hv hadj_uv => ?_⟩
      have hu_not_U : u ∉ U := (Finset.mem_sdiff.mp hu).2
      obtain ⟨p_v, hp_v⟩ := (mem_U v).mp hv
      let p_u : T.Walk r u := p_v.append (SimpleGraph.Walk.cons hadj_uv.symm SimpleGraph.Walk.nil)
      have h_mem_edges : s(w, r) ∈ p_u.edges := by
        by_contra h_not
        exact hu_not_U ((mem_U u).mpr ⟨p_u, h_not⟩)
      rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
        List.mem_append, List.mem_singleton] at h_mem_edges
      rcases h_mem_edges with h_in_pv | h_eq_edge
      · exact False.elim (hp_v h_in_pv)
      · rw [Sym2.eq_iff] at h_eq_edge
        rcases h_eq_edge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact False.elim (hw_not_U hv)
        · exact ⟨rfl, rfl⟩
    have hU_card : 2 ≤ U.card := by
      have hy_U : y ∈ U := by
        refine (mem_U y).mpr ⟨SimpleGraph.Walk.cons hadj_ry SimpleGraph.Walk.nil, ?_⟩
        simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_singleton,
          Sym2.eq_iff, not_or, not_and]
        refine ⟨fun hwr _ => T.ne_of_adj hadj_wr hwr, fun hwy _ => hy_ne hwy.symm⟩
      exact Finset.one_lt_card_iff.mpr ⟨r, y, hr_U, hy_U, T.ne_of_adj hadj_ry⟩
    exact ⟨U, ⟨hU_sub, hU_bridge⟩, hU_card⟩
  obtain ⟨P, hP_br, hP_card⟩ := branch_of_step r₁ y₁ hadj_wr₁ hadj_r₁y₁ hy₁_ne
  obtain ⟨B, hB_br, hB_card⟩ := branch_of_step r₂ y₂ hadj_wr₂ hadj_r₂y₂ hy₂_ne
  obtain ⟨C, hC_br, hC_card⟩ := branch_of_step r₃ y₃ hadj_wr₃ hadj_r₃y₃ hy₃_ne
  exact ⟨w, r₁, r₂, r₃, P, B, C, hne₁₂, hne₁₃, hne₂₃, hP_br, hP_card, hB_br, hB_card, hC_br, hC_card⟩

theorem branch_child_rootedCount_lt : ∀ (n : ℕ) (T : SimpleGraph (Fin n))
    (P U : Finset (Fin n)) (r r₁ : Fin n),
    r ∈ P → U ⊆ P.erase r → r₁ ∈ U → T.Adj r r₁ →
    rootedCount T U r₁ < rootedCount T P r :=
by
  intro n T P U r r₁ hrP hU hr₁U hadj
  classical
  change (rootedSubtreesIn T U r₁).card < (rootedSubtreesIn T P r).card
  have hr_mem : ({r} : Finset (Fin n)) ∈ rootedSubtreesIn T P r := by
    simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨Finset.singleton_nonempty r, ?_⟩,
      Finset.singleton_subset_iff.mpr hrP, Finset.mem_singleton_self r⟩
    refine @SimpleGraph.Connected.mk _ _ (fun a b => ?_) ⟨⟨r, Finset.mem_singleton_self r⟩⟩
    have ha : a.1 = r := Finset.mem_singleton.mp a.2
    have hb : b.1 = r := Finset.mem_singleton.mp b.2
    have hab : a = b := Subtype.ext (ha.trans hb.symm)
    exact hab ▸ SimpleGraph.Reachable.refl a
  have hr₁_ne_r : r₁ ≠ r := (Finset.mem_erase.mp (hU hr₁U)).1
  have h_maps : ∀ S ∈ rootedSubtreesIn T U r₁,
      insert r S ∈ (rootedSubtreesIn T P r).erase {r} := by
    intro S hS
    simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    rcases hS with ⟨⟨_hS_ne, hS_conn⟩, hSU, hr₁S⟩
    rw [Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · intro h_eq
      have hr₁_in : r₁ ∈ ({r} : Finset (Fin n)) := h_eq ▸ Finset.mem_insert_of_mem hr₁S
      exact hr₁_ne_r (Finset.mem_singleton.mp hr₁_in)
    · simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
      have hS_P : S ⊆ P := hSU.trans (hU.trans (Finset.erase_subset r P))
      refine ⟨⟨Finset.insert_nonempty r S, ?_⟩,
        Finset.insert_subset_iff.mpr ⟨hrP, hS_P⟩, Finset.mem_insert_self r S⟩
      refine @SimpleGraph.Connected.mk _ _ (fun a b => ?_) ⟨⟨r, Finset.mem_insert_self r S⟩⟩
      have walk_lift : ∀ (x y : {z // z ∈ (S : Set (Fin n))})
          (p : (T.induce (S : Set (Fin n))).Walk x y),
          (T.induce ((insert r S : Finset (Fin n)) : Set (Fin n))).Reachable
            ⟨x.1, Finset.mem_insert_of_mem x.2⟩
            ⟨y.1, Finset.mem_insert_of_mem y.2⟩ := by
        intro x y p
        induction p with
        | nil => exact SimpleGraph.Reachable.refl _
        | @cons x mid y h_adj p ih =>
          have h_adj' : (T.induce ((insert r S : Finset (Fin n)) : Set (Fin n))).Adj
              ⟨x.1, Finset.mem_insert_of_mem x.2⟩
              ⟨mid.1, Finset.mem_insert_of_mem mid.2⟩ := h_adj
          exact (SimpleGraph.Adj.reachable h_adj').trans ih
      have reach_r : ∀ (u : {z // z ∈ ((insert r S : Finset (Fin n)) : Set (Fin n))}),
          (T.induce ((insert r S : Finset (Fin n)) : Set (Fin n))).Reachable
            u ⟨r, Finset.mem_insert_self r S⟩ := by
        intro u
        rcases Finset.mem_insert.mp u.2 with hu_r | hu_S
        · have hu_eq : u = ⟨r, Finset.mem_insert_self r S⟩ := Subtype.ext hu_r
          exact hu_eq ▸ SimpleGraph.Reachable.refl _
        · obtain ⟨p⟩ := hS_conn.preconnected ⟨u.1, hu_S⟩ ⟨r₁, hr₁S⟩
          have h_u_r₁ := walk_lift ⟨u.1, hu_S⟩ ⟨r₁, hr₁S⟩ p
          have h_r_r₁ : (T.induce ((insert r S : Finset (Fin n)) : Set (Fin n))).Adj
              ⟨r, Finset.mem_insert_self r S⟩
              ⟨r₁, Finset.mem_insert_of_mem hr₁S⟩ := hadj
          exact h_u_r₁.trans (SimpleGraph.Adj.reachable h_r_r₁).symm
      exact (reach_r a).trans (reach_r b).symm
  have h_inj : Set.InjOn (insert r) (rootedSubtreesIn T U r₁ : Set (Finset (Fin n))) := by
    intro S₁ hS₁ S₂ hS₂ h_eq
    simp only [Finset.mem_coe, rootedSubtreesIn, subtrees, Finset.mem_filter,
      Finset.mem_univ, true_and] at hS₁ hS₂
    have hr_not_S₁ : r ∉ S₁ := fun hrS₁ => Finset.notMem_erase r P (hU (hS₁.2.1 hrS₁))
    have hr_not_S₂ : r ∉ S₂ := fun hrS₂ => Finset.notMem_erase r P (hU (hS₂.2.1 hrS₂))
    have h_er := congrArg (fun X : Finset (Fin n) => X.erase r) h_eq
    dsimp only at h_er
    rw [Finset.erase_insert hr_not_S₁, Finset.erase_insert hr_not_S₂] at h_er
    exact h_er
  have h_sub : (rootedSubtreesIn T U r₁).image (insert r) ⊆
      (rootedSubtreesIn T P r).erase {r} := by
    intro X hX
    rcases Finset.mem_image.mp hX with ⟨S, hS, rfl⟩
    exact h_maps S hS
  have h_le : (rootedSubtreesIn T U r₁).card ≤ ((rootedSubtreesIn T P r).erase {r}).card := by
    rw [← Finset.card_image_of_injOn h_inj]
    exact Finset.card_le_card h_sub
  exact lt_of_le_of_lt h_le (Finset.card_erase_lt_of_mem hr_mem)

theorem branch_zero_nonleaf_is_terminal_arm : ∀ (n : ℕ) (T : SimpleGraph (Fin n)),
    T.IsTree → ¬ HasLeafAtDegTwo T →
    ∀ (P : Finset (Fin n)) (w r : Fin n),
      IsBranchAt T P w r → 2 ≤ P.card → 2 ≤ (Finset.univ \ P).card →
      (∀ z ∈ P, T.Adj r z → IsLeafIn T z r) →
      ∃ (ℓ : ℕ) (v : Fin (ℓ + 1) → Fin n) (L : Fin (ℓ + 1) → Finset (Fin n)),
        v 0 = r ∧ IsTerminalArm T P w ℓ v L :=
by
  intro n T _hT h_no_deg2 P w r hP_br hP_card h_comp_card h_all_leaf
  classical
  have hP_sub : IsSubtree T P := hP_br.1
  have hP_bridge : IsBridgeJoin T (Finset.univ \ P) P w r := hP_br.2
  have hw_sdiff : w ∈ Finset.univ \ P := hP_bridge.2.1
  have hr_P : r ∈ P := hP_bridge.2.2.1
  have hadj_wr : T.Adj w r := hP_bridge.2.2.2.1
  have h_bridge_uniq : ∀ u ∈ Finset.univ \ P, ∀ v ∈ P, T.Adj u v → u = w ∧ v = r :=
    hP_bridge.2.2.2.2
  let L₀ : Finset (Fin n) := P.filter (fun x => IsLeafIn T x r)
  have hr_not_L₀ : r ∉ L₀ := by
    intro hr_L₀
    have h_leaf_r : IsLeafIn T r r := (Finset.mem_filter.mp hr_L₀).2
    exact T.loopless r ((h_leaf_r r).mpr rfl)
  have hL₀_sub : L₀ ⊆ P := Finset.filter_subset _ P
  have h_ins_sub : insert r L₀ ⊆ P := Finset.insert_subset_iff.mpr ⟨hr_P, hL₀_sub⟩
  have hL₀_pkt : IsLeafPacket T L₀ r := fun x hx => (Finset.mem_filter.mp hx).2
  have h_walk_inv : ∀ (a b : {x // x ∈ (P : Set (Fin n))})
      (p : (T.induce (P : Set (Fin n))).Walk a b),
      (a : Fin n) ∈ insert r L₀ → (b : Fin n) ∈ insert r L₀ := by
    intro a b p
    induction p with
    | nil =>
      intro ha
      exact ha
    | @cons a mid b hadj p ih =>
      intro ha
      rcases Finset.mem_insert.mp ha with ha_r | ha_L₀
      · have hadj_r : T.Adj r (mid : Fin n) := ha_r ▸ hadj
        have hmid_leaf : IsLeafIn T (mid : Fin n) r := h_all_leaf (mid : Fin n) mid.2 hadj_r
        have hmid_L₀ : (mid : Fin n) ∈ L₀ := Finset.mem_filter.mpr ⟨mid.2, hmid_leaf⟩
        exact ih (Finset.mem_insert_of_mem hmid_L₀)
      · have ha_leaf : IsLeafIn T (a : Fin n) r := (Finset.mem_filter.mp ha_L₀).2
        have hmid_r : (mid : Fin n) = r := (ha_leaf (mid : Fin n)).mp hadj
        exact ih (hmid_r ▸ Finset.mem_insert_self r L₀)
  have h_sub_ins : P ⊆ insert r L₀ := by
    intro u hu
    obtain ⟨p⟩ := hP_sub.2.preconnected ⟨r, hr_P⟩ ⟨u, hu⟩
    exact h_walk_inv ⟨r, hr_P⟩ ⟨u, hu⟩ p (Finset.mem_insert_self r L₀)
  have hP_eq_ins : P = insert r L₀ := Finset.Subset.antisymm h_sub_ins h_ins_sub
  have hP_card_eq : P.card = L₀.card + 1 := by
    rw [hP_eq_ins, Finset.card_insert_of_notMem hr_not_L₀]
  have hL₀_card : 2 ≤ L₀.card := by
    by_contra h_lt2
    have hL₀_one : L₀.card = 1 := by omega
    obtain ⟨x, hL₀_eq⟩ := Finset.card_eq_one.mp hL₀_one
    have hx_L₀ : x ∈ L₀ := hL₀_eq ▸ Finset.mem_singleton_self x
    rcases Finset.mem_filter.mp hx_L₀ with ⟨hx_P, hx_leaf⟩
    have h_sdiff_add : (Finset.univ \ P).card + P.card = Fintype.card (Fin n) := by
      rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ P), Finset.card_univ]
    have h_card4 : 4 ≤ Fintype.card (Fin n) := by omega
    have hx_ne_w : x ≠ w := by
      intro h_eq
      exact (Finset.mem_sdiff.mp hw_sdiff).2 (h_eq ▸ hx_P)
    have h_deg2 : ∀ v : Fin n, T.Adj r v ↔ v = x ∨ v = w := by
      intro v
      constructor
      · intro hadj
        by_cases hv : v ∈ P
        · have hv_leaf : IsLeafIn T v r := h_all_leaf v hv hadj
          have hv_L₀ : v ∈ L₀ := Finset.mem_filter.mpr ⟨hv, hv_leaf⟩
          rw [hL₀_eq] at hv_L₀
          exact Or.inl (Finset.mem_singleton.mp hv_L₀)
        · have hv_sdiff : v ∈ Finset.univ \ P :=
            Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩
          exact Or.inr (h_bridge_uniq v hv_sdiff r hr_P (T.symm hadj)).1
      · rintro (rfl | rfl)
        · exact T.symm ((hx_leaf r).mpr rfl)
        · exact T.symm hadj_wr
    exact h_no_deg2 ⟨h_card4, x, r, w, hx_ne_w, hx_leaf, h_deg2⟩
  let v : Fin 1 → Fin n := fun _ => r
  let L : Fin 1 → Finset (Fin n) := fun _ => L₀
  have h_img_v : ∀ x : Fin n, x ∈ Finset.univ.image v ↔ x = r := by
    intro x
    rw [Finset.mem_image]
    constructor
    · rintro ⟨_, _, h_eq⟩
      exact h_eq.symm
    · intro h_eq
      exact ⟨0, Finset.mem_univ 0, h_eq.symm⟩
  have h_biUnion_L : ∀ x : Fin n, x ∈ Finset.univ.biUnion L ↔ x ∈ L₀ := by
    intro x
    rw [Finset.mem_biUnion]
    constructor
    · rintro ⟨_, _, hx⟩
      exact hx
    · intro hx
      exact ⟨0, Finset.mem_univ 0, hx⟩
  refine ⟨0, v, L, rfl, ?_⟩
  refine ⟨hP_br, hL₀_card, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j _
    exact Fin.ext (by omega)
  · ext x
    rw [hP_eq_ins, Finset.mem_insert, Finset.mem_union, h_img_v, h_biUnion_L]
  · rw [Finset.disjoint_left]
    intro x hx_v hx_L
    have h_xr : x = r := (h_img_v x).mp hx_v
    have h_xL₀ : x ∈ L₀ := (h_biUnion_L x).mp hx_L
    exact hr_not_L₀ (h_xr ▸ h_xL₀)
  · intro i j hne
    exact False.elim (hne (Fin.ext (by omega)))
  · intro i j
    have hi : i.val = 0 := by omega
    have hj : j.val = 0 := by omega
    constructor
    · intro hadj
      exact False.elim (T.loopless r hadj)
    · intro h_step
      omega
  · intro _
    exact hL₀_pkt

theorem branch_unique_nonleaf_peel : ∀ (n : ℕ) (T : SimpleGraph (Fin n)),
    T.IsTree →
    ∀ (P L₀ : Finset (Fin n)) (w r r₁ : Fin n),
      IsBranchAt T P w r → 2 ≤ (Finset.univ \ P).card →
      (∀ x : Fin n, x ∈ L₀ ↔ x ∈ P ∧ IsLeafIn T x r) →
      r₁ ∈ P → T.Adj r r₁ → ¬ IsLeafIn T r₁ r →
      (∀ z ∈ P, T.Adj r z → IsLeafIn T z r ∨ z = r₁) →
      IsBranchAt T (P \ insert r L₀) r r₁ ∧
      2 ≤ (P \ insert r L₀).card ∧
      2 ≤ (Finset.univ \ (P \ insert r L₀)).card ∧
      P \ insert r L₀ ⊆ P.erase r :=
by
  intro n T hT P L₀ w r r₁ hP_br h_comp_card hL₀_iff hr₁_P hadj₁ hnl₁ h_unique
  set P₁ := P \ insert r L₀
  have hr₁_ne_r : r₁ ≠ r := (T.ne_of_adj hadj₁).symm
  have hr₁_not_L₀ : r₁ ∉ L₀ := fun h => hnl₁ ((hL₀_iff r₁).mp h).2
  have hr₁_in_P₁ : r₁ ∈ P₁ := by
    simp only [P₁, Finset.mem_sdiff, Finset.mem_insert, not_or]
    exact ⟨hr₁_P, hr₁_ne_r, hr₁_not_L₀⟩
  have hr_not_P₁ : r ∉ P₁ :=
    fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_insert_self r L₀)
  have hr_sdiff₁ : r ∈ Finset.univ \ P₁ :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ r, hr_not_P₁⟩
  have hP₁_sub : P₁ ⊆ P.erase r := by
    intro x hx
    simp only [P₁, Finset.mem_sdiff, Finset.mem_insert, not_or] at hx
    exact Finset.mem_erase.mpr ⟨hx.2.1, hx.1⟩
  have hP₁_comp : 2 ≤ (Finset.univ \ P₁).card := by
    have h_sub_sdiff : Finset.univ \ P ⊆ Finset.univ \ P₁ :=
      Finset.sdiff_subset_sdiff (Finset.Subset.refl _) Finset.sdiff_subset
    exact le_trans h_comp_card (Finset.card_le_card h_sub_sdiff)
  have hBridge₁ : IsBridgeJoin T (Finset.univ \ P₁) P₁ r r₁ := by
    refine ⟨disjoint_sdiff_self_left, hr_sdiff₁, hr₁_in_P₁, hadj₁, fun u hu v hv hadj => ?_⟩
    have hv' : v ∈ P ∧ v ≠ r ∧ v ∉ L₀ := by
      simpa only [P₁, Finset.mem_sdiff, Finset.mem_insert, not_or] using hv
    rcases hv' with ⟨hv_P, hv_ne_r, hv_not_L₀⟩
    have hv_nl : ¬ IsLeafIn T v r := fun h => hv_not_L₀ ((hL₀_iff v).mpr ⟨hv_P, h⟩)
    have hu_not_P₁ : u ∉ P₁ := (Finset.mem_sdiff.mp hu).2
    have hu_eq_r : u = r := by
      by_contra hu_ne_r
      by_cases hu_P : u ∈ P
      · have hu_L₀ : u ∈ L₀ := by
          simp only [P₁, Finset.mem_sdiff, Finset.mem_insert, not_and, not_not] at hu_not_P₁
          exact (hu_not_P₁ hu_P).resolve_left hu_ne_r
        have hleaf_u : IsLeafIn T u r := ((hL₀_iff u).mp hu_L₀).2
        exact hv_ne_r ((hleaf_u v).mp hadj)
      · have hu_sdiff : u ∈ Finset.univ \ P :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, hu_P⟩
        exact hv_ne_r (hP_br.2.2.2.2.2 u hu_sdiff v hv_P hadj).2
    have hadj_rv : T.Adj r v := hu_eq_r ▸ hadj
    rcases h_unique v hv_P hadj_rv with hleaf_v | hv_eq_r₁
    · exact False.elim (hv_nl hleaf_v)
    · exact ⟨hu_eq_r, hv_eq_r₁⟩
  have hP₁_card : 2 ≤ P₁.card := by
    have h_ex_y : ∃ y : Fin n, T.Adj r₁ y ∧ y ≠ r := by
      by_contra! h_all
      apply hnl₁
      intro v
      exact ⟨h_all v, fun hv => hv ▸ hadj₁.symm⟩
    obtain ⟨y, hadj_r₁y, hy_ne_r⟩ := h_ex_y
    have hy_in_P₁ : y ∈ P₁ := by
      by_contra hy_not_P₁
      have hy_sdiff₁ : y ∈ Finset.univ \ P₁ :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy_not_P₁⟩
      exact hy_ne_r (hBridge₁.2.2.2.2 y hy_sdiff₁ r₁ hr₁_in_P₁ hadj_r₁y.symm).1
    exact Finset.one_lt_card_iff.mpr ⟨r₁, y, hr₁_in_P₁, hy_in_P₁, T.ne_of_adj hadj_r₁y⟩
  have hSub₁ : IsSubtree T P₁ := by
    refine ⟨⟨r₁, hr₁_in_P₁⟩, @SimpleGraph.Connected.mk _ _ (fun a b => ?_) ⟨⟨r₁, hr₁_in_P₁⟩⟩⟩
    have reach_r₁ : ∀ (x : {z // z ∈ (P₁ : Set (Fin n))}),
        (T.induce (P₁ : Set (Fin n))).Reachable x ⟨r₁, hr₁_in_P₁⟩ := by
      intro x
      obtain ⟨q⟩ := hT.1.preconnected x.1 r
      have walk_lem : ∀ (u z : Fin n) (p : T.Walk u z) (hu : u ∈ P₁),
          z ∉ P₁ → (T.induce (P₁ : Set (Fin n))).Reachable ⟨u, hu⟩ ⟨r₁, hr₁_in_P₁⟩ := by
        intro u z p
        induction p with
        | nil => intro hu hz; exact False.elim (hz hu)
        | @cons u mid z hadj p ih =>
          intro hu hz
          by_cases hmid : mid ∈ P₁
          · have hadj_ind : (T.induce (P₁ : Set (Fin n))).Adj ⟨u, hu⟩ ⟨mid, hmid⟩ := hadj
            exact (SimpleGraph.Adj.reachable hadj_ind).trans (ih hmid hz)
          · have hmid_sdiff : mid ∈ Finset.univ \ P₁ :=
              Finset.mem_sdiff.mpr ⟨Finset.mem_univ mid, hmid⟩
            have hu_eq_r₁ : u = r₁ := (hBridge₁.2.2.2.2 mid hmid_sdiff u hu hadj.symm).2
            have h_sub_eq : (⟨u, hu⟩ : {z // z ∈ (P₁ : Set (Fin n))}) = ⟨r₁, hr₁_in_P₁⟩ :=
              Subtype.ext hu_eq_r₁
            rw [h_sub_eq]
      exact walk_lem x.1 r q x.2 hr_not_P₁
    exact (reach_r₁ a).trans (reach_r₁ b).symm
  exact ⟨⟨hSub₁, hBridge₁⟩, hP₁_card, hP₁_comp, hP₁_sub⟩

theorem terminal_arm_cons : ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : Finset V) (w r : V) (L₀ : Finset V)
    (ℓ : ℕ) (v' : Fin (ℓ + 1) → V) (L' : Fin (ℓ + 1) → Finset V),
    IsBranchAt G P w r → r ∉ L₀ → L₀ ⊆ P → IsLeafPacket G L₀ r →
    IsTerminalArm G (P \ insert r L₀) r ℓ v' L' →
    IsTerminalArm G P w (ℓ + 1) (Fin.cons r v') (Fin.cons L₀ L') :=
by
  intro V _ _ G P w r L₀ ℓ v' L' hP hr_not_L₀ hL₀_sub hL₀_pkt hArm'
  set P₁ := P \ insert r L₀
  rcases hArm' with ⟨hBr', hLast', hInj', hP₁_eq, hDisj_im_bi', hDisj_L', hAdj', hPkt'⟩
  have hv'_mem_P₁ : ∀ k : Fin (ℓ + 1), v' k ∈ P₁ := by
    intro k
    rw [hP₁_eq]
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem v' (Finset.mem_univ k))
  have hv'_ne_r : ∀ k : Fin (ℓ + 1), v' k ≠ r := by
    intro k hk_eq
    have hmem : v' k ∈ P \ insert r L₀ := hv'_mem_P₁ k
    rw [hk_eq] at hmem
    exact (Finset.mem_sdiff.mp hmem).2 (Finset.mem_insert_self r L₀)
  have hL'_sub_P₁ : ∀ (k : Fin (ℓ + 1)) {x : V}, x ∈ L' k → x ∈ P₁ := by
    intro k x hx
    rw [hP₁_eq]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, hx⟩)
  have hDisj_L₀_L' : ∀ k : Fin (ℓ + 1), Disjoint L₀ (L' k) := by
    intro k
    rw [Finset.disjoint_left]
    intro x hx₀ hxk
    have hmem : x ∈ P \ insert r L₀ := hL'_sub_P₁ k hxk
    exact (Finset.mem_sdiff.mp hmem).2 (Finset.mem_insert_of_mem hx₀)
  have h_im : ∀ x : V, x ∈ Finset.univ.image (Fin.cons r v') ↔ x = r ∨ x ∈ Finset.univ.image v' := by
    intro x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      refine Fin.cases ?_ ?_ i
      · simp [Fin.cons_zero]
      · intro k
        simp only [Fin.cons_succ]
        exact Or.inr ⟨k, rfl⟩
    · rintro (rfl | ⟨k, rfl⟩)
      · exact ⟨0, Fin.cons_zero _ _⟩
      · exact ⟨k.succ, Fin.cons_succ _ _ _⟩
  have h_bi : ∀ x : V, x ∈ Finset.univ.biUnion (Fin.cons L₀ L') ↔ x ∈ L₀ ∨ x ∈ Finset.univ.biUnion L' := by
    intro x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      refine Fin.cases ?_ ?_ i hi
      · simp only [Fin.cons_zero]
        exact Or.inl
      · intro k
        simp only [Fin.cons_succ]
        intro hk
        exact Or.inr ⟨k, hk⟩
    · rintro (hx₀ | ⟨k, hxk⟩)
      · refine ⟨0, ?_⟩
        simpa only [Fin.cons_zero] using hx₀
      · refine ⟨k.succ, ?_⟩
        simpa only [Fin.cons_succ] using hxk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Fin.cons_zero] using hP
  · simpa only [Fin.cons_last] using hLast'
  · intro i j h_eq
    refine Fin.cases ?_ ?_ i h_eq
    · refine Fin.cases ?_ ?_ j
      · intro _; rfl
      · intro k hk
        simp only [Fin.cons_zero, Fin.cons_succ] at hk
        exact False.elim (hv'_ne_r k hk.symm)
    · intro k₁
      refine Fin.cases ?_ ?_ j
      · intro hk
        simp only [Fin.cons_succ, Fin.cons_zero] at hk
        exact False.elim (hv'_ne_r k₁ hk)
      · intro k₂ hk
        simp only [Fin.cons_succ] at hk
        exact congrArg Fin.succ (hInj' hk)
  · ext x
    rw [Finset.mem_union, h_im, h_bi]
    have hx_P₁ : x ∈ Finset.univ.image v' ∨ x ∈ Finset.univ.biUnion L' ↔ x ∈ P \ insert r L₀ := by
      rw [← Finset.mem_union, ← hP₁_eq]
    constructor
    · intro hxP
      by_cases hx_ins : x ∈ insert r L₀
      · rcases Finset.mem_insert.mp hx_ins with rfl | hx₀
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr (Or.inl hx₀)
      · have hx_sdiff : x ∈ P \ insert r L₀ := Finset.mem_sdiff.mpr ⟨hxP, hx_ins⟩
        rcases hx_P₁.mpr hx_sdiff with h₁ | h₂
        · exact Or.inl (Or.inr h₁)
        · exact Or.inr (Or.inr h₂)
    · rintro ((rfl | h₁) | (hx₀ | h₂))
      · exact hP.2.2.2.1
      · exact (Finset.mem_sdiff.mp (hx_P₁.mp (Or.inl h₁))).1
      · exact hL₀_sub hx₀
      · exact (Finset.mem_sdiff.mp (hx_P₁.mp (Or.inr h₂))).1
  · rw [Finset.disjoint_left]
    intro x h₁ h₂
    rw [h_im] at h₁
    rw [h_bi] at h₂
    rcases h₁ with hx_eq | h₁
    · rcases h₂ with hx₀ | h₂
      · exact hr_not_L₀ (hx_eq ▸ hx₀)
      · have hr_mem : r ∈ P \ insert r L₀ := by
          change r ∈ P₁
          rw [hP₁_eq]
          exact Finset.mem_union_right _ (hx_eq ▸ h₂)
        exact (Finset.mem_sdiff.mp hr_mem).2 (Finset.mem_insert_self r L₀)
    · rcases h₂ with hx₀ | h₂
      · have hx_mem : x ∈ P \ insert r L₀ := by
          change x ∈ P₁
          rw [hP₁_eq]
          exact Finset.mem_union_left _ h₁
        exact (Finset.mem_sdiff.mp hx_mem).2 (Finset.mem_insert_of_mem hx₀)
      · exact Finset.disjoint_left.mp hDisj_im_bi' h₁ h₂
  · intro i j hne
    refine Fin.cases ?_ ?_ i hne
    · refine Fin.cases ?_ ?_ j
      · intro h; exact False.elim (h rfl)
      · intro k _
        simpa only [Fin.cons_zero, Fin.cons_succ] using hDisj_L₀_L' k
    · intro k₁
      refine Fin.cases ?_ ?_ j
      · intro _
        simpa only [Fin.cons_succ, Fin.cons_zero] using (hDisj_L₀_L' k₁).symm
      · intro k₂ hne'
        simp only [Fin.cons_succ]
        apply hDisj_L' k₁ k₂
        intro hk_eq
        exact hne' (congrArg Fin.succ hk_eq)
  · have h_adj_0_succ : ∀ k : Fin (ℓ + 1), G.Adj r (v' k) ↔ k.val = 0 := by
      intro k
      constructor
      · intro hadj
        have hr_sdiff : r ∈ Finset.univ \ P₁ := hBr'.2.2.1
        have hvk_P₁ : v' k ∈ P₁ := hv'_mem_P₁ k
        have h_eq := (hBr'.2.2.2.2.2 r hr_sdiff (v' k) hvk_P₁ hadj).2
        have hk0 : k = 0 := hInj' h_eq
        rw [hk0, Fin.val_zero]
      · intro hk_val
        have hk0 : k = 0 := Fin.ext hk_val
        rw [hk0]
        exact hBr'.2.2.2.2.1
    intro i j
    refine Fin.cases ?_ ?_ i
    · refine Fin.cases ?_ ?_ j
      · simp only [Fin.cons_zero, Fin.val_zero]
        constructor
        · intro h; exact False.elim (G.loopless r h)
        · omega
      · intro k
        simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ]
        rw [h_adj_0_succ k]
        omega
    · intro k₁
      refine Fin.cases ?_ ?_ j
      · simp only [Fin.cons_succ, Fin.cons_zero, Fin.val_succ, Fin.val_zero]
        rw [G.adj_comm, h_adj_0_succ k₁]
        omega
      · intro k₂
        simp only [Fin.cons_succ, Fin.val_succ]
        rw [hAdj' k₁ k₂]
        omega
  · intro i
    refine Fin.cases ?_ ?_ i
    · simpa only [Fin.cons_zero] using hL₀_pkt
    · intro k
      simpa only [Fin.cons_succ] using hPkt' k

theorem branch_two_nonleaf_three_branch : ∀ (n : ℕ) (T : SimpleGraph (Fin n)),
    T.IsTree →
    ∀ (P : Finset (Fin n)) (w r r₁ r₂ : Fin n),
      IsBranchAt T P w r → 2 ≤ (Finset.univ \ P).card →
      r₁ ∈ P → r₂ ∈ P → r₁ ≠ r₂ →
      T.Adj r r₁ → ¬ IsLeafIn T r₁ r →
      T.Adj r r₂ → ¬ IsLeafIn T r₂ r →
      ∃ (P' B' C' : Finset (Fin n)),
        IsThreeBranchAt T r r₁ r₂ w P' B' C' ∧ P' ⊆ P.erase r :=
by
  intro n T hT P w r r₁ r₂ hP_br h_comp_card hr₁_P hr₂_P hne hadj₁ hnl₁ hadj₂ hnl₂
  classical
  have hw_sdiff : w ∈ Finset.univ \ P := hP_br.2.2.1
  have hw_not_P : w ∉ P := (Finset.mem_sdiff.mp hw_sdiff).2
  have hr_P : r ∈ P := hP_br.2.2.2.1
  have hadj_wr : T.Adj w r := hP_br.2.2.2.2.1
  have hP_uniq : ∀ u ∈ Finset.univ \ P, ∀ v ∈ P, T.Adj u v → u = w ∧ v = r := hP_br.2.2.2.2.2
  have hr₁_ne_w : r₁ ≠ w := fun h => hw_not_P (h ▸ hr₁_P)
  have hr₂_ne_w : r₂ ≠ w := fun h => hw_not_P (h ▸ hr₂_P)
  set C' : Finset (Fin n) := Finset.univ \ P
  have h_sdiff_C' : Finset.univ \ C' = P :=
    Finset.sdiff_sdiff_eq_self (Finset.subset_univ P)
  have hr_sdiff_C' : r ∈ Finset.univ \ C' := by
    rw [h_sdiff_C']
    exact hr_P
  have hC'_bridge : IsBridgeJoin T (Finset.univ \ C') C' r w := by
    refine ⟨disjoint_sdiff_self_left, hr_sdiff_C', hw_sdiff, hadj_wr.symm, fun u hu v hv hadj_uv => ?_⟩
    rw [h_sdiff_C'] at hu
    have h_eq := hP_uniq v hv u hu hadj_uv.symm
    exact ⟨h_eq.2, h_eq.1⟩
  have hr_not_C' : r ∉ C' := fun h => (Finset.mem_sdiff.mp h).2 hr_P
  have hC'_sub : IsSubtree T C' := by
    refine ⟨⟨w, hw_sdiff⟩, @SimpleGraph.Connected.mk _ _ (fun a b => ?_) ⟨⟨w, hw_sdiff⟩⟩⟩
    have reach_w : ∀ (x : {z // z ∈ (C' : Set (Fin n))}),
        (T.induce (C' : Set (Fin n))).Reachable x ⟨w, hw_sdiff⟩ := by
      intro x
      obtain ⟨q⟩ := hT.1.preconnected x.1 r
      have walk_lem : ∀ (u z : Fin n) (p : T.Walk u z) (hu : u ∈ C'),
          z ∉ C' → (T.induce (C' : Set (Fin n))).Reachable ⟨u, hu⟩ ⟨w, hw_sdiff⟩ := by
        intro u z p
        induction p with
        | nil => intro hu hz; exact False.elim (hz hu)
        | @cons u mid z hadj p ih =>
          intro hu hz
          by_cases hmid : mid ∈ C'
          · have hadj_ind : (T.induce (C' : Set (Fin n))).Adj ⟨u, hu⟩ ⟨mid, hmid⟩ := hadj
            exact (SimpleGraph.Adj.reachable hadj_ind).trans (ih hmid hz)
          · have hmid_sdiff : mid ∈ Finset.univ \ C' :=
              Finset.mem_sdiff.mpr ⟨Finset.mem_univ mid, hmid⟩
            rw [h_sdiff_C'] at hmid_sdiff
            have hu_eq_w : u = w := (hP_uniq u hu mid hmid_sdiff hadj).1
            have h_sub_eq : (⟨u, hu⟩ : {z // z ∈ (C' : Set (Fin n))}) = ⟨w, hw_sdiff⟩ :=
              Subtype.ext hu_eq_w
            rw [h_sub_eq]
      exact walk_lem x.1 r q x.2 hr_not_C'
    exact (reach_w a).trans (reach_w b).symm
  have hC'_br : IsBranchAt T C' r w := ⟨hC'_sub, hC'_bridge⟩
  have branch_of_nonleaf : ∀ (r_i : Fin n), T.Adj r r_i → ¬ IsLeafIn T r_i r →
      ∃ U : Finset (Fin n), IsBranchAt T U r r_i ∧ 2 ≤ U.card := by
    intro r_i hadj_rr_i hnl_i
    have h_ex_y : ∃ y : Fin n, T.Adj r_i y ∧ y ≠ r := by
      by_contra! h_all
      apply hnl_i
      intro v
      exact ⟨h_all v, fun hv => hv ▸ hadj_rr_i.symm⟩
    obtain ⟨y, hadj_r_iy, hy_ne_r⟩ := h_ex_y
    let U : Finset (Fin n) := Finset.univ.filter (fun z => ∃ p_z : T.Walk r_i z, s(r, r_i) ∉ p_z.edges)
    have mem_U : ∀ z : Fin n, z ∈ U ↔ ∃ p_z : T.Walk r_i z, s(r, r_i) ∉ p_z.edges := by
      intro z
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
    have hr_i_U : r_i ∈ U := (mem_U r_i).mpr ⟨SimpleGraph.Walk.nil, by simp⟩
    have hr_not_U : r ∉ U := by
      rw [mem_U]
      rintro ⟨p_r, hp_r⟩
      have hbr : T.IsBridge s(r_i, r) :=
        SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.IsAcyclic hadj_rr_i.symm
      have hmem : s(r_i, r) ∈ p_r.edges :=
        (SimpleGraph.isBridge_iff_adj_and_forall_walk_mem_edges.mp hbr).2 p_r
      rw [Sym2.eq_swap] at hmem
      exact hp_r hmem
    have hr_sdiff : r ∈ Finset.univ \ U :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ r, hr_not_U⟩
    have walk_ind : ∀ {u_a u_b : Fin n} (p_ab : T.Walk u_a u_b) (ha : u_a ∈ U) (hb : u_b ∈ U),
        s(r, r_i) ∉ p_ab.edges → (T.induce (U : Set (Fin n))).Reachable ⟨u_a, ha⟩ ⟨u_b, hb⟩ := by
      intro u_a u_b p_ab
      induction p_ab with
      | nil =>
        intro ha hb _
        exact SimpleGraph.Reachable.rfl
      | @cons u_a u_c u_b hadj_ac q_cb ih =>
        intro ha hb hp_edges
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons, not_or] at hp_edges
        have hc : u_c ∈ U := by
          obtain ⟨p_a, hp_a⟩ := (mem_U u_a).mp ha
          refine (mem_U u_c).mpr ⟨p_a.append (SimpleGraph.Walk.cons hadj_ac SimpleGraph.Walk.nil), ?_⟩
          rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
            List.mem_append, List.mem_singleton, not_or]
          exact ⟨hp_a, hp_edges.1⟩
        have hadj_ind : (T.induce (U : Set (Fin n))).Adj ⟨u_a, ha⟩ ⟨u_c, hc⟩ := hadj_ac
        exact (SimpleGraph.Adj.reachable hadj_ind).trans (ih hc hb hp_edges.2)
    have hU_sub : IsSubtree T U := by
      refine ⟨⟨r_i, hr_i_U⟩, @SimpleGraph.Connected.mk _ _ (fun u_a u_b => ?_) ⟨⟨r_i, hr_i_U⟩⟩⟩
      have reach_r : ∀ z : {z // z ∈ (U : Set (Fin n))},
          (T.induce (U : Set (Fin n))).Reachable ⟨r_i, hr_i_U⟩ z := by
        rintro ⟨z, hz⟩
        obtain ⟨p_z, hp_z⟩ := (mem_U z).mp hz
        exact walk_ind p_z hr_i_U hz hp_z
      exact (reach_r u_a).symm.trans (reach_r u_b)
    have hU_bridge : IsBridgeJoin T (Finset.univ \ U) U r r_i := by
      refine ⟨disjoint_sdiff_self_left, hr_sdiff, hr_i_U, hadj_rr_i, fun u hu v hv hadj_uv => ?_⟩
      have hu_not_U : u ∉ U := (Finset.mem_sdiff.mp hu).2
      obtain ⟨p_v, hp_v⟩ := (mem_U v).mp hv
      let p_u : T.Walk r_i u := p_v.append (SimpleGraph.Walk.cons hadj_uv.symm SimpleGraph.Walk.nil)
      have h_mem_edges : s(r, r_i) ∈ p_u.edges := by
        by_contra h_not
        exact hu_not_U ((mem_U u).mpr ⟨p_u, h_not⟩)
      rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
        List.mem_append, List.mem_singleton] at h_mem_edges
      rcases h_mem_edges with h_in_pv | h_eq_edge
      · exact False.elim (hp_v h_in_pv)
      · rw [Sym2.eq_iff] at h_eq_edge
        rcases h_eq_edge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact False.elim (hr_not_U hv)
        · exact ⟨rfl, rfl⟩
    have hU_card : 2 ≤ U.card := by
      have hy_U : y ∈ U := by
        refine (mem_U y).mpr ⟨SimpleGraph.Walk.cons hadj_r_iy SimpleGraph.Walk.nil, ?_⟩
        simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_singleton,
          Sym2.eq_iff, not_or, not_and]
        refine ⟨fun hrr_i _ => T.ne_of_adj hadj_rr_i hrr_i, fun hry _ => hy_ne_r hry.symm⟩
      exact Finset.one_lt_card_iff.mpr ⟨r_i, y, hr_i_U, hy_U, T.ne_of_adj hadj_r_iy⟩
    exact ⟨U, ⟨hU_sub, hU_bridge⟩, hU_card⟩
  obtain ⟨P', hP'_br, hP'_card⟩ := branch_of_nonleaf r₁ hadj₁ hnl₁
  obtain ⟨B', hB'_br, hB'_card⟩ := branch_of_nonleaf r₂ hadj₂ hnl₂
  have hr_not_P' : r ∉ P' := (Finset.mem_sdiff.mp hP'_br.2.2.1).2
  have hr₁_P' : r₁ ∈ P' := hP'_br.2.2.2.1
  have h_walk_P : ∀ (a b : {x // x ∈ (P' : Set (Fin n))})
      (q : (T.induce (P' : Set (Fin n))).Walk a b),
      (a : Fin n) ∈ P → (b : Fin n) ∈ P := by
    intro a b q
    induction q with
    | nil => intro ha; exact ha
    | @cons a mid b hadj q ih =>
      intro ha
      have hmid_P : (mid : Fin n) ∈ P := by
        by_contra hmid_not_P
        have hmid_sdiff : (mid : Fin n) ∈ Finset.univ \ P :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hmid_not_P⟩
        have h_eq := hP_uniq (mid : Fin n) hmid_sdiff (a : Fin n) ha hadj.symm
        exact hr_not_P' (h_eq.2 ▸ a.2)
      exact ih hmid_P
  have hP'_sub : P' ⊆ P.erase r := by
    intro z hz
    have hz_ne_r : z ≠ r := fun h => hr_not_P' (h ▸ hz)
    obtain ⟨q⟩ := hP'_br.1.2.preconnected ⟨r₁, hr₁_P'⟩ ⟨z, hz⟩
    have hz_P : z ∈ P := h_walk_P ⟨r₁, hr₁_P'⟩ ⟨z, hz⟩ q hr₁_P
    exact Finset.mem_erase.mpr ⟨hz_ne_r, hz_P⟩
  exact ⟨P', B', C', ⟨hne, hr₁_ne_w, hr₂_ne_w, hP'_br, hP'_card, hB'_br, hB'_card, hC'_br, h_comp_card⟩, hP'_sub⟩

theorem branch_terminal_arm_or_smaller_three_branch : ∀ (n : ℕ) (hn : 1 ≤ n) (T : SimpleGraph (Fin n)),
    T.IsTree → ¬ HasLeafAtDegTwo T →
    ∀ (P : Finset (Fin n)) (w r : Fin n),
      IsBranchAt T P w r → 2 ≤ P.card → 2 ≤ (Finset.univ \ P).card →
      (∃ (ℓ : ℕ) (v : Fin (ℓ + 1) → Fin n) (L : Fin (ℓ + 1) → Finset (Fin n)),
        v 0 = r ∧ IsTerminalArm T P w ℓ v L) ∨
      (∃ (w' r'_P r'_B r'_C : Fin n) (P' B' C' : Finset (Fin n)),
        IsThreeBranchAt T w' r'_P r'_B r'_C P' B' C' ∧
        rootedCount T P' r'_P < rootedCount T P r) :=
by
  intro n _hn T hT h_no_deg2
  have main_ind : ∀ (m : ℕ) (P : Finset (Fin n)) (w r : Fin n),
      P.card = m → IsBranchAt T P w r → 2 ≤ P.card → 2 ≤ (Finset.univ \ P).card →
      (∃ (ℓ : ℕ) (v : Fin (ℓ + 1) → Fin n) (L : Fin (ℓ + 1) → Finset (Fin n)),
        v 0 = r ∧ IsTerminalArm T P w ℓ v L) ∨
      (∃ (w' r'_P r'_B r'_C : Fin n) (P' B' C' : Finset (Fin n)),
        IsThreeBranchAt T w' r'_P r'_B r'_C P' B' C' ∧
        rootedCount T P' r'_P < rootedCount T P r) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      classical
      intro P w r hm hP_br hP_card h_comp_card
      have hr_in_P : r ∈ P := hP_br.2.2.2.1
      let L₀ := P.filter (fun x => IsLeafIn T x r)
      let N_nl := P.filter (fun z => T.Adj r z ∧ ¬ IsLeafIn T z r)
      rcases Nat.lt_trichotomy N_nl.card 1 with h_lt1 | h_eq1 | h_gt1
      · have h_zero : N_nl.card = 0 := by omega
        have h_empty : N_nl = ∅ := Finset.card_eq_zero.mp h_zero
        have h_all_leaf : ∀ z ∈ P, T.Adj r z → IsLeafIn T z r := by
          intro z hz hadj
          by_contra h_not_leaf
          have hz_mem : z ∈ N_nl := Finset.mem_filter.mpr ⟨hz, hadj, h_not_leaf⟩
          rw [h_empty] at hz_mem
          exact Finset.notMem_empty z hz_mem
        exact Or.inl (branch_zero_nonleaf_is_terminal_arm n T hT h_no_deg2 P w r
          hP_br hP_card h_comp_card h_all_leaf)
      · obtain ⟨r₁, hr₁_eq⟩ := Finset.card_eq_one.mp h_eq1
        have hr₁_mem : r₁ ∈ N_nl := by
          rw [hr₁_eq]
          exact Finset.mem_singleton_self r₁
        rcases Finset.mem_filter.mp hr₁_mem with ⟨hr₁_P, hadj₁, hnl₁⟩
        have h_unique : ∀ z ∈ P, T.Adj r z → IsLeafIn T z r ∨ z = r₁ := by
          intro z hz hadj
          by_cases hleaf : IsLeafIn T z r
          · exact Or.inl hleaf
          · have hz_mem : z ∈ N_nl := Finset.mem_filter.mpr ⟨hz, hadj, hleaf⟩
            rw [hr₁_eq] at hz_mem
            exact Or.inr (Finset.mem_singleton.mp hz_mem)
        have hL₀_iff : ∀ x : Fin n, x ∈ L₀ ↔ x ∈ P ∧ IsLeafIn T x r :=
          fun x => Finset.mem_filter
        rcases branch_unique_nonleaf_peel n T hT P L₀ w r r₁ hP_br h_comp_card
            hL₀_iff hr₁_P hadj₁ hnl₁ h_unique with
          ⟨hP₁_br, hP₁_card, hP₁_comp, hP₁_sub⟩
        set P₁ := P \ insert r L₀
        have h_card_lt : P₁.card < m := by
          rw [← hm]
          exact lt_of_le_of_lt (Finset.card_le_card hP₁_sub) (Finset.card_erase_lt_of_mem hr_in_P)
        have hr₁_in_P₁ : r₁ ∈ P₁ := hP₁_br.2.2.2.1
        have h_rc_lt : rootedCount T P₁ r₁ < rootedCount T P r :=
          branch_child_rootedCount_lt n T P P₁ r r₁ hr_in_P hP₁_sub hr₁_in_P₁ hadj₁
        rcases ih P₁.card h_card_lt P₁ r r₁ rfl hP₁_br hP₁_card hP₁_comp with
          ⟨ℓ', v', L', _hv'0, hArm'⟩ | ⟨w', r'_P, r'_B, r'_C, P', B', C', h3', hlt'⟩
        · have hr_not_L₀ : r ∉ L₀ := by
            intro hr_L₀
            have hleaf_r : IsLeafIn T r r := (Finset.mem_filter.mp hr_L₀).2
            exact T.loopless r ((hleaf_r r).mpr rfl)
          have hL₀_sub : L₀ ⊆ P := Finset.filter_subset _ P
          have hL₀_pkt : IsLeafPacket T L₀ r :=
            fun x hx => (Finset.mem_filter.mp hx).2
          have hArm : IsTerminalArm T P w (ℓ' + 1) (Fin.cons r v') (Fin.cons L₀ L') :=
            terminal_arm_cons T P w r L₀ ℓ' v' L' hP_br hr_not_L₀ hL₀_sub hL₀_pkt hArm'
          exact Or.inl ⟨ℓ' + 1, Fin.cons r v', Fin.cons L₀ L', rfl, hArm⟩
        · exact Or.inr ⟨w', r'_P, r'_B, r'_C, P', B', C', h3', Nat.lt_trans hlt' h_rc_lt⟩
      · obtain ⟨r₁, r₂, hr₁_mem, hr₂_mem, hne⟩ := Finset.one_lt_card_iff.mp h_gt1
        rcases Finset.mem_filter.mp hr₁_mem with ⟨hr₁_P, hadj₁, hnl₁⟩
        rcases Finset.mem_filter.mp hr₂_mem with ⟨hr₂_P, hadj₂, hnl₂⟩
        obtain ⟨P', B', C', h3, hP'_sub⟩ :=
          branch_two_nonleaf_three_branch n T hT P w r r₁ r₂ hP_br h_comp_card
            hr₁_P hr₂_P hne hadj₁ hnl₁ hadj₂ hnl₂
        have hr₁_in_P' : r₁ ∈ P' := h3.2.2.2.1.2.2.2.1
        have h_rc_lt : rootedCount T P' r₁ < rootedCount T P r :=
          branch_child_rootedCount_lt n T P P' r r₁ hr_in_P hP'_sub hr₁_in_P' hadj₁
        exact Or.inr ⟨r, r₁, r₂, w, P', B', C', h3, h_rc_lt⟩
  intro P w r hP_br hP_card h_comp_card
  exact main_ind P.card P w r rfl hP_br hP_card h_comp_card

theorem exists_min_count_terminal_arm : ∀ (n : ℕ) (hn : 1 ≤ n) (T : SimpleGraph (Fin n)),
    T.IsTree → ¬ IsCaterpillar T → ¬ HasLeafAtDegTwo T →
    ∃ (ℓ : ℕ) (A₀ B C P : Finset (Fin n)) (w r_B r_C : Fin n)
      (v : Fin (ℓ + 1) → Fin n) (L : Fin (ℓ + 1) → Finset (Fin n)),
      IsMinCountTerminalArm T ℓ A₀ B C P w r_B r_C v L :=
by
  intro n hn T hT h_not_cat h_no_deg2
  let α := Fin n × Fin n × Fin n × Fin n × Finset (Fin n) × Finset (Fin n) × Finset (Fin n)
  let S : Set α := {x | IsThreeBranchAt T x.1 x.2.1 x.2.2.1 x.2.2.2.1
    x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2}
  have hS_ne : S.Nonempty := by
    obtain ⟨w, r_P, r_B, r_C, P, B, C, h3⟩ :=
      non_caterpillar_has_three_branches n hn T hT h_not_cat
    exact ⟨⟨w, r_P, r_B, r_C, P, B, C⟩, h3⟩
  obtain ⟨⟨w, r_P, r_B, r_C, P, B, C⟩, h3, hmin⟩ :=
    (measure (fun x : α => rootedCount T x.2.2.2.2.1 x.2.1)).wf.has_min S hS_ne
  dsimp only [S, Set.mem_setOf_eq] at h3
  have hmin' : ∀ (w' r'_P r'_B r'_C : Fin n) (P' B' C' : Finset (Fin n)),
      IsThreeBranchAt T w' r'_P r'_B r'_C P' B' C' →
      rootedCount T P r_P ≤ rootedCount T P' r'_P := by
    intro w' r'_P r'_B r'_C P' B' C' h3'
    exact not_lt.mp (hmin ⟨w', r'_P, r'_B, r'_C, P', B', C'⟩ h3')
  rcases h3 with ⟨hne_PB, hne_PC, hne_BC, hP_br, hP_card, hB_br, hB_card, hC_br, hC_card⟩
  have hleB : rootedCount T P r_P ≤ rootedCount T B r_B :=
    hmin' w r_B r_P r_C B P C ⟨hne_PB.symm, hne_BC, hne_PC, hB_br, hB_card, hP_br, hP_card, hC_br, hC_card⟩
  have hleC : rootedCount T P r_P ≤ rootedCount T C r_C :=
    hmin' w r_C r_B r_P C B P ⟨hne_BC.symm, hne_PC.symm, hne_PB.symm, hC_br, hC_card, hB_br, hB_card, hP_br, hP_card⟩
  have h_comp_card : 2 ≤ (Finset.univ \ P).card := by
    have hw_sdiff : w ∈ Finset.univ \ P := hP_br.2.2.1
    have hr_B_not_P : r_B ∉ P := by
      intro hr_B_P
      exact hne_PB (hP_br.2.2.2.2.2 w hw_sdiff r_B hr_B_P hB_br.2.2.2.2.1).2.symm
    have hr_B_sdiff : r_B ∈ Finset.univ \ P :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hr_B_not_P⟩
    have hw_ne_rB : w ≠ r_B := T.ne_of_adj hB_br.2.2.2.2.1
    exact Finset.one_lt_card_iff.mpr ⟨w, r_B, hw_sdiff, hr_B_sdiff, hw_ne_rB⟩
  rcases branch_terminal_arm_or_smaller_three_branch n hn T hT h_no_deg2 P w r_P
      hP_br hP_card h_comp_card with ⟨ℓ, v, L, hv0, hArm⟩ | ⟨w', r'_P, r'_B, r'_C, P', B', C', h3', hlt⟩
  · subst hv0
    have branch_disj : ∀ {r₁ r₂ : Fin n} {U₁ U₂ : Finset (Fin n)},
        IsBranchAt T U₁ w r₁ → IsBranchAt T U₂ w r₂ → r₁ ≠ r₂ → Disjoint U₁ U₂ := by
      intro r₁ r₂ U₁ U₂ h₁ h₂ hne
      rw [Finset.disjoint_left]
      intro z hz₁ hz₂
      have hw_not_U₂ : w ∉ U₂ := (Finset.mem_sdiff.mp h₂.2.2.1).2
      have hr₂_not_U₁ : r₂ ∉ U₁ := by
        intro hr₂_U₁
        exact hne (h₁.2.2.2.2.2 w h₁.2.2.1 r₂ hr₂_U₁ h₂.2.2.2.2.1).2.symm
      obtain ⟨p⟩ := h₂.1.2.preconnected ⟨r₂, h₂.2.2.2.1⟩ ⟨z, hz₂⟩
      have key : ∀ (a b : {x // x ∈ (U₂ : Set (Fin n))}) (q : (T.induce (U₂ : Set (Fin n))).Walk a b),
          (a : Fin n) ∉ U₁ → (b : Fin n) ∈ U₁ → False := by
        intro a b q
        induction q with
        | nil => intro ha hb; exact ha hb
        | @cons a mid b hadj q ih =>
          intro ha hb
          by_cases hmid : (mid : Fin n) ∈ U₁
          · have h_eq := h₁.2.2.2.2.2 (a : Fin n) (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩) (mid : Fin n) hmid hadj
            exact hw_not_U₂ (h_eq.1 ▸ a.2)
          · exact ih hmid hb
      exact key ⟨r₂, h₂.2.2.2.1⟩ ⟨z, hz₂⟩ p hr₂_not_U₁ hz₁
    rcases hArm with ⟨_, hL_last, hv_inj, hP_eq, hP_disj, hL_disj, hv_adj, hL_pkt⟩
    set A₀ := Finset.univ \ (B ∪ C ∪ P)
    refine ⟨ℓ, A₀, B, C, P, w, r_B, r_C, v, L, ?_⟩
    have hDisj_BC : Disjoint B C := branch_disj hB_br hC_br hne_BC
    have hDisj_BP : Disjoint B P := branch_disj hB_br hP_br hne_PB.symm
    have hDisj_CP : Disjoint C P := branch_disj hC_br hP_br hne_PC.symm
    have hw_not_B : w ∉ B := (Finset.mem_sdiff.mp hB_br.2.2.1).2
    have hw_not_C : w ∉ C := (Finset.mem_sdiff.mp hC_br.2.2.1).2
    have hw_not_P : w ∉ P := (Finset.mem_sdiff.mp hP_br.2.2.1).2
    have hw_A₀ : w ∈ A₀ := by
      simp only [A₀, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, not_or]
      exact ⟨⟨hw_not_B, hw_not_C⟩, hw_not_P⟩
    have hA₀_sub : IsSubtree T A₀ := by
      refine ⟨⟨w, hw_A₀⟩, @SimpleGraph.Connected.mk _ _ (fun a b => ?_) ⟨⟨w, hw_A₀⟩⟩⟩
      have reach_w : ∀ (x : {z // z ∈ (A₀ : Set (Fin n))}),
          (T.induce (A₀ : Set (Fin n))).Reachable x ⟨w, hw_A₀⟩ := by
        intro x
        obtain ⟨q⟩ := hT.1.preconnected x.1 r_B
        have hr_B_not_A₀ : r_B ∉ A₀ := by
          simp only [A₀, Finset.mem_sdiff, Finset.mem_union, not_and, not_not]
          intro _
          exact Or.inl (Or.inl hB_br.2.2.2.1)
        have walk_lem : ∀ (u z : Fin n) (p : T.Walk u z) (hu : u ∈ A₀),
            z ∉ A₀ → (T.induce (A₀ : Set (Fin n))).Reachable ⟨u, hu⟩ ⟨w, hw_A₀⟩ := by
          intro u z p
          induction p with
          | nil => intro hu hz; exact False.elim (hz hu)
          | @cons u mid z hadj p ih =>
            intro hu hz
            by_cases hmid : mid ∈ A₀
            · have hadj_ind : (T.induce (A₀ : Set (Fin n))).Adj ⟨u, hu⟩ ⟨mid, hmid⟩ := hadj
              exact (SimpleGraph.Adj.reachable hadj_ind).trans (ih hmid hz)
            · have hmid_union : mid ∈ B ∪ C ∪ P := by
                simp only [A₀, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at hmid
                exact hmid
              have hu_eq_w : u = w := by
                rcases Finset.mem_union.mp hmid_union with hBC | hP
                · rcases Finset.mem_union.mp hBC with hB | hC
                  · have hu_sdiff : u ∈ Finset.univ \ B := by
                      simp only [A₀, Finset.mem_sdiff, Finset.mem_union, not_or] at hu ⊢
                      exact ⟨Finset.mem_univ u, hu.2.1.1⟩
                    exact (hB_br.2.2.2.2.2 u hu_sdiff mid hB hadj).1
                  · have hu_sdiff : u ∈ Finset.univ \ C := by
                      simp only [A₀, Finset.mem_sdiff, Finset.mem_union, not_or] at hu ⊢
                      exact ⟨Finset.mem_univ u, hu.2.1.2⟩
                    exact (hC_br.2.2.2.2.2 u hu_sdiff mid hC hadj).1
                · have hu_sdiff : u ∈ Finset.univ \ P := by
                    simp only [A₀, Finset.mem_sdiff, Finset.mem_union, not_or] at hu ⊢
                    exact ⟨Finset.mem_univ u, hu.2.2⟩
                  exact (hP_br.2.2.2.2.2 u hu_sdiff mid hP hadj).1
              have h_sub_eq : (⟨u, hu⟩ : {z // z ∈ (A₀ : Set (Fin n))}) = ⟨w, hw_A₀⟩ :=
                Subtype.ext hu_eq_w
              rw [h_sub_eq]
        exact walk_lem x.1 r_B q x.2 hr_B_not_A₀
      exact (reach_w a).trans (reach_w b).symm
    have hDisj_A₀B : Disjoint A₀ B := by
      rw [Finset.disjoint_left]
      intro x hx hB
      simp only [A₀, Finset.mem_sdiff, Finset.mem_union, not_or] at hx
      exact hx.2.1.1 hB
    have hDisj_A₀C : Disjoint A₀ C := by
      rw [Finset.disjoint_left]
      intro x hx hC
      simp only [A₀, Finset.mem_sdiff, Finset.mem_union, not_or] at hx
      exact hx.2.1.2 hC
    have hDisj_A₀BCP : Disjoint (A₀ ∪ B ∪ C) P := by
      rw [Finset.disjoint_left]
      intro x hx hP
      rcases Finset.mem_union.mp hx with hA₀B | hC
      · rcases Finset.mem_union.mp hA₀B with hA₀ | hB
        · simp only [A₀, Finset.mem_sdiff, Finset.mem_union, not_or] at hA₀
          exact hA₀.2.2 hP
        · exact Finset.disjoint_left.mp hDisj_BP hB hP
      · exact Finset.disjoint_left.mp hDisj_CP hC hP
    have hUnion_all : A₀ ∪ B ∪ C ∪ P = Finset.univ := by
      ext x
      simp only [A₀, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, iff_true]
      tauto
    have hBridge_B : IsBridgeJoin T A₀ B w r_B := by
      refine ⟨hDisj_A₀B, hw_A₀, hB_br.2.2.2.1, hB_br.2.2.2.2.1, fun u hu v hv hadj => ?_⟩
      have hu_sdiff : u ∈ Finset.univ \ B :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, Finset.disjoint_left.mp hDisj_A₀B hu⟩
      exact hB_br.2.2.2.2.2 u hu_sdiff v hv hadj
    have hDisj_A₀B_C : Disjoint (A₀ ∪ B) C :=
      Finset.disjoint_union_left.mpr ⟨hDisj_A₀C, hDisj_BC⟩
    have hBridge_C : IsBridgeJoin T (A₀ ∪ B) C w r_C := by
      refine ⟨hDisj_A₀B_C, Finset.mem_union_left _ hw_A₀, hC_br.2.2.2.1, hC_br.2.2.2.2.1,
        fun u hu v hv hadj => ?_⟩
      have hu_sdiff : u ∈ Finset.univ \ C :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, Finset.disjoint_left.mp hDisj_A₀B_C hu⟩
      exact hC_br.2.2.2.2.2 u hu_sdiff v hv hadj
    have hBridge_P : IsBridgeJoin T (A₀ ∪ B ∪ C) P w (v 0) := by
      refine ⟨hDisj_A₀BCP, Finset.mem_union_left _ (Finset.mem_union_left _ hw_A₀),
        hP_br.2.2.2.1, hP_br.2.2.2.2.1, fun u hu v hv hadj => ?_⟩
      have hu_sdiff : u ∈ Finset.univ \ P :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, Finset.disjoint_left.mp hDisj_A₀BCP hu⟩
      exact hP_br.2.2.2.2.2 u hu_sdiff v hv hadj
    exact ⟨hL_last, hv_inj, hA₀_sub, hB_br.1, hC_br.1, hP_br.1,
      hDisj_A₀B, hDisj_A₀C, hDisj_BC, hDisj_A₀BCP, hUnion_all,
      hP_eq, hP_disj, hL_disj, hBridge_B, hBridge_C, hBridge_P,
      hv_adj, hL_pkt, hleB, hleC⟩
  · exact False.elim ((not_lt_of_ge (hmin' w' r'_P r'_B r'_C P' B' C' h3')) hlt)

theorem bridge_join_rooted_moments : ∀ (n : ℕ) (T : SimpleGraph (Fin n))
    (U₁ U₂ : Finset (Fin n)) (r₁ r₂ : Fin n),
    IsBridgeJoin T U₁ U₂ r₁ r₂ →
    rootedCount T (U₁ ∪ U₂) r₁ = rootedCount T U₁ r₁ * (1 + rootedCount T U₂ r₂) ∧
    rootedOrderSum T (U₁ ∪ U₂) r₁ =
      rootedOrderSum T U₁ r₁ * (1 + rootedCount T U₂ r₂) +
      rootedCount T U₁ r₁ * rootedOrderSum T U₂ r₂ :=
by
  intro n T A B w r_B hJ
  classical
  have isBridgeJoin_symm : ∀ {A B : Finset (Fin n)} {w r_B : Fin n},
      IsBridgeJoin T A B w r_B → IsBridgeJoin T B A r_B w := by
    intro A B w r_B hJ
    rcases hJ with ⟨h_disj, hw, hr_B, hadj, h_bridge⟩
    refine ⟨h_disj.symm, hr_B, hw, T.symm hadj, ?_⟩
    intro u hu v hv huv
    exact (h_bridge v hv u hu (T.symm huv)).symm
  have exists_walk_of_isSubtree : ∀ {S : Finset (Fin n)},
      IsSubtree T S → ∀ {a b : Fin n}, a ∈ S → b ∈ S →
      ∃ q : T.Walk a b, ∀ z ∈ q.support, z ∈ S := by
    intro S hS a b ha hb
    obtain ⟨q₀⟩ := hS.2.preconnected ⟨a, ha⟩ ⟨b, hb⟩
    suffices ∀ {u v : ↑(S : Set (Fin n))} (q : (T.induce (S : Set (Fin n))).Walk u v),
        ∃ q' : T.Walk u.1 v.1, ∀ z ∈ q'.support, z ∈ S from this q₀
    intro u v q
    induction q with
    | @nil u =>
      refine ⟨SimpleGraph.Walk.nil, ?_⟩
      intro z hz
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      rw [hz]
      exact Finset.mem_coe.mp u.2
    | @cons u c v hadj q' ih =>
      obtain ⟨q₁, hq₁⟩ := ih
      refine ⟨SimpleGraph.Walk.cons hadj q₁, ?_⟩
      intro z hz
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz'
      · exact Finset.mem_coe.mp u.2
      · exact hq₁ z hz'
  have bridge_walk_mem_edges : ∀ {A B : Finset (Fin n)} {w r_B : Fin n},
      IsBridgeJoin T A B w r_B → ∀ {a b : Fin n} (q : T.Walk a b),
      (∀ z ∈ q.support, z ∈ A ∪ B) →
      ((a ∈ A ∧ b ∈ B) ∨ (a ∈ B ∧ b ∈ A)) →
      s(w, r_B) ∈ q.edges := by
    intro A B w r_B hJ a b q
    induction q with
    | nil =>
      intro _ h_ab
      rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact False.elim (Finset.disjoint_left.mp hJ.1 ha hb)
      · exact False.elim (Finset.disjoint_left.mp hJ.1 hb ha)
    | @cons a c b h_step q' ih =>
      intro h_supp h_ab
      have hc_mem : c ∈ A ∪ B := h_supp c (by
        simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.start_mem_support])
      have h_supp' : ∀ z ∈ q'.support, z ∈ A ∪ B := fun z hz =>
        h_supp z (by simp [SimpleGraph.Walk.support_cons, hz])
      rcases Finset.mem_union.mp hc_mem with hcA | hcB
      · rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ (ih h_supp' (Or.inl ⟨hcA, hb⟩))
        · obtain ⟨hcw, har⟩ := hJ.2.2.2.2 c hcA a ha (T.symm h_step)
          subst hcw har
          rw [SimpleGraph.Walk.edges_cons, Sym2.eq_swap]
          exact List.mem_cons_self
      · rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · obtain ⟨haw, hcr⟩ := hJ.2.2.2.2 a ha c hcB h_step
          subst haw hcr
          rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_self
        · rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ (ih h_supp' (Or.inr ⟨hcB, hb⟩))
  have bridge_path_support_left : ∀ {A B : Finset (Fin n)} {w r_B : Fin n},
      IsBridgeJoin T A B w r_B → ∀ {a b : Fin n} (p : T.Walk a b), p.IsPath →
      (∀ z ∈ p.support, z ∈ A ∪ B) → a ∈ A → b ∈ A →
      ∀ z ∈ p.support, z ∈ A := by
    intro A B w r_B hJ a b p hp h_supp ha hb z hz
    rcases Finset.mem_union.mp (h_supp z hz) with hzA | hzB
    · exact hzA
    · exfalso
      let p₁ := p.takeUntil z hz
      let p₂ := p.dropUntil z hz
      have hp₁_supp : ∀ x ∈ p₁.support, x ∈ A ∪ B :=
        fun x hx => h_supp x (p.support_takeUntil_subset hz hx)
      have hp₂_supp : ∀ x ∈ p₂.support, x ∈ A ∪ B :=
        fun x hx => h_supp x (p.support_dropUntil_subset hz hx)
      have he₁ : s(w, r_B) ∈ p₁.edges :=
        bridge_walk_mem_edges hJ p₁ hp₁_supp (Or.inl ⟨ha, hzB⟩)
      have he₂ : s(w, r_B) ∈ p₂.edges :=
        bridge_walk_mem_edges hJ p₂ hp₂_supp (Or.inr ⟨hzB, hb⟩)
      have h_nodup : p.edges.Nodup := hp.isTrail.edges_nodup
      have h_edges : p₁.edges ++ p₂.edges = p.edges := by
        rw [← SimpleGraph.Walk.edges_append, p.take_spec hz]
      rw [← h_edges, List.nodup_append] at h_nodup
      exact h_nodup.2.2 s(w, r_B) he₁ s(w, r_B) he₂ rfl
  have bridge_crossing_left : ∀ {A B S : Finset (Fin n)} {w r_B : Fin n},
      IsBridgeJoin T A B w r_B → S ⊆ A ∪ B →
      IsSubtree T S → (S ∩ A).Nonempty → (S ∩ B).Nonempty →
      S ∩ A ∈ rootedSubtreesIn T A w := by
    intro A B S w r_B hJ hS_sub hS hSA hSB
    obtain ⟨a₀, ha₀⟩ := hSA
    obtain ⟨b₀, hb₀⟩ := hSB
    have ha₀S : a₀ ∈ S := (Finset.mem_inter.mp ha₀).1
    have ha₀A : a₀ ∈ A := (Finset.mem_inter.mp ha₀).2
    have hb₀S : b₀ ∈ S := (Finset.mem_inter.mp hb₀).1
    have hb₀B : b₀ ∈ B := (Finset.mem_inter.mp hb₀).2
    obtain ⟨q, hq_supp⟩ := exists_walk_of_isSubtree hS ha₀S hb₀S
    have hq_AB : ∀ z ∈ q.support, z ∈ A ∪ B := fun z hz => hS_sub (hq_supp z hz)
    have he : s(w, r_B) ∈ q.edges :=
      bridge_walk_mem_edges hJ q hq_AB (Or.inl ⟨ha₀A, hb₀B⟩)
    have hwS : w ∈ S := hq_supp w (q.fst_mem_support_of_mem_edges he)
    have hwSA : w ∈ S ∩ A := Finset.mem_inter.mpr ⟨hwS, hJ.2.1⟩
    have hSA_subtree : IsSubtree T (S ∩ A) := by
      refine ⟨⟨w, hwSA⟩, ?_⟩
      have : Nonempty ↑((S ∩ A : Finset (Fin n)) : Set (Fin n)) := ⟨⟨w, hwSA⟩⟩
      refine ⟨?_⟩
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      have hxS : x ∈ S := (Finset.mem_inter.mp hx).1
      have hxA : x ∈ A := (Finset.mem_inter.mp hx).2
      have hyS : y ∈ S := (Finset.mem_inter.mp hy).1
      have hyA : y ∈ A := (Finset.mem_inter.mp hy).2
      obtain ⟨q₁, hq₁_supp⟩ := exists_walk_of_isSubtree hS hxS hyS
      let p : T.Walk x y := (q₁.toPath : T.Walk x y)
      have hp_path : p.IsPath := q₁.toPath.2
      have hp_S : ∀ z ∈ p.support, z ∈ S := fun z hz => hq₁_supp z (q₁.support_toPath_subset hz)
      have hp_AB : ∀ z ∈ p.support, z ∈ A ∪ B := fun z hz => hS_sub (hp_S z hz)
      have hp_A : ∀ z ∈ p.support, z ∈ A :=
        bridge_path_support_left hJ p hp_path hp_AB hxA hyA
      have hp_SA : ∀ z ∈ p.support, z ∈ ((S ∩ A : Finset (Fin n)) : Set (Fin n)) :=
        fun z hz => Finset.mem_inter.mpr ⟨hp_S z hz, hp_A z hz⟩
      exact (p.induce ((S ∩ A : Finset (Fin n)) : Set (Fin n)) hp_SA).reachable
    simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hSA_subtree, Finset.inter_subset_right, hwSA⟩
  have bridge_union_isSubtree : ∀ {A B SA SB : Finset (Fin n)} {w r_B : Fin n},
      IsBridgeJoin T A B w r_B →
      SA ∈ rootedSubtreesIn T A w → SB ∈ rootedSubtreesIn T B r_B →
      IsSubtree T (SA ∪ SB) := by
    intro A B SA SB w r_B hJ hSA hSB
    simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hSA hSB
    rcases hSA with ⟨hSA_sub, _, hw_SA⟩
    rcases hSB with ⟨hSB_sub, _, hr_SB⟩
    have hw_U : w ∈ SA ∪ SB := Finset.mem_union_left SB hw_SA
    have hr_U : r_B ∈ SA ∪ SB := Finset.mem_union_right SA hr_SB
    refine ⟨⟨w, hw_U⟩, ?_⟩
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨w, hw_U⟩, ?_⟩
    rintro ⟨x, hx⟩
    rcases Finset.mem_union.mp hx with hxA | hxB
    · obtain ⟨q, hq⟩ := exists_walk_of_isSubtree hSA_sub hw_SA hxA
      have hq_U : ∀ z ∈ q.support, z ∈ ((SA ∪ SB : Finset (Fin n)) : Set (Fin n)) :=
        fun z hz => Finset.mem_union_left SB (hq z hz)
      exact (q.induce ((SA ∪ SB : Finset (Fin n)) : Set (Fin n)) hq_U).reachable
    · obtain ⟨q, hq⟩ := exists_walk_of_isSubtree hSB_sub hr_SB hxB
      have hq_U : ∀ z ∈ q.support, z ∈ ((SA ∪ SB : Finset (Fin n)) : Set (Fin n)) :=
        fun z hz => Finset.mem_union_right SA (hq z hz)
      have hadj_ind : (T.induce ((SA ∪ SB : Finset (Fin n)) : Set (Fin n))).Adj ⟨w, hw_U⟩ ⟨r_B, hr_U⟩ :=
        hJ.2.2.2.1
      exact hadj_ind.reachable.trans (q.induce ((SA ∪ SB : Finset (Fin n)) : Set (Fin n)) hq_U).reachable
  let RA_set := rootedSubtreesIn T A w
  let RB_set := rootedSubtreesIn T B r_B
  let φ : Finset (Fin n) × Finset (Fin n) → Finset (Fin n) := fun p => p.1 ∪ p.2
  let M := (RA_set ×ˢ RB_set).image φ
  have h_inter_left : ∀ {X Y : Finset (Fin n)}, X ⊆ A → Y ⊆ B → (X ∪ Y) ∩ A = X := by
    intro X Y hX hY
    ext z
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hzX | hzY, hzA⟩
      · exact hzX
      · exact False.elim (Finset.disjoint_left.mp hJ.1 hzA (hY hzY))
    · intro hzX
      exact ⟨Or.inl hzX, hX hzX⟩
  have h_inter_right : ∀ {X Y : Finset (Fin n)}, X ⊆ A → Y ⊆ B → (X ∪ Y) ∩ B = Y := by
    intro X Y hX hY
    ext z
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hzX | hzY, hzB⟩
      · exact False.elim (Finset.disjoint_left.mp hJ.1 (hX hzX) hzB)
      · exact hzY
    · intro hzY
      exact ⟨Or.inr hzY, hY hzY⟩
  have h_inj : Set.InjOn φ ((RA_set ×ˢ RB_set : Finset (Finset (Fin n) × Finset (Fin n))) : Set (Finset (Fin n) × Finset (Fin n))) := by
    intro p₁ hp₁ p₂ hp₂ h_eq
    rcases Finset.mem_product.mp (Finset.mem_coe.mp hp₁) with ⟨hp₁A, hp₁B⟩
    rcases Finset.mem_product.mp (Finset.mem_coe.mp hp₂) with ⟨hp₂A, hp₂B⟩
    simp only [RA_set, RB_set, rootedSubtreesIn, Finset.mem_filter] at hp₁A hp₁B hp₂A hp₂B
    have h1A : p₁.1 ⊆ A := hp₁A.2.1
    have h1B : p₁.2 ⊆ B := hp₁B.2.1
    have h2A : p₂.1 ⊆ A := hp₂A.2.1
    have h2B : p₂.2 ⊆ B := hp₂B.2.1
    have h1 : p₁.1 = p₂.1 := by
      calc p₁.1 = (p₁.1 ∪ p₁.2) ∩ A := (h_inter_left h1A h1B).symm
        _ = (p₂.1 ∪ p₂.2) ∩ A := by rw [show p₁.1 ∪ p₁.2 = p₂.1 ∪ p₂.2 from h_eq]
        _ = p₂.1 := h_inter_left h2A h2B
    have h2 : p₁.2 = p₂.2 := by
      calc p₁.2 = (p₁.1 ∪ p₁.2) ∩ B := (h_inter_right h1A h1B).symm
        _ = (p₂.1 ∪ p₂.2) ∩ B := by rw [show p₁.1 ∪ p₁.2 = p₂.1 ∪ p₂.2 from h_eq]
        _ = p₂.2 := h_inter_right h2A h2B
    exact Prod.ext h1 h2
  have hM_card : M.card = rootedCount T A w * rootedCount T B r_B := by
    dsimp [M, RA_set, RB_set, rootedCount]
    rw [Finset.card_image_of_injOn h_inj, Finset.card_product]
  have hM_sum : ∑ S ∈ M, S.card =
      rootedOrderSum T A w * rootedCount T B r_B + rootedCount T A w * rootedOrderSum T B r_B := by
    dsimp [M]
    rw [Finset.sum_image h_inj, Finset.sum_product]
    have h_inner : ∀ x ∈ RA_set,
        ∑ y ∈ RB_set, (x ∪ y).card = x.card * RB_set.card + ∑ y ∈ RB_set, y.card := by
      intro x hx
      simp only [RA_set, rootedSubtreesIn, Finset.mem_filter] at hx
      have hx_sub : x ⊆ A := hx.2.1
      have h_congr : ∑ y ∈ RB_set, (x ∪ y).card = ∑ y ∈ RB_set, (x.card + y.card) := by
        refine Finset.sum_congr rfl fun y hy => ?_
        simp only [RB_set, rootedSubtreesIn, Finset.mem_filter] at hy
        have hy_sub : y ⊆ B := hy.2.1
        exact Finset.card_union_of_disjoint (Disjoint.mono hx_sub hy_sub hJ.1)
      rw [h_congr, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
    rw [Finset.sum_congr rfl h_inner, Finset.sum_add_distrib, ← Finset.sum_mul,
      Finset.sum_const, smul_eq_mul]
    rfl
  have h_mem_M : ∀ S : Finset (Fin n),
      S ∈ M ↔ S ∈ subtreesIn T (A ∪ B) ∧ (S ∩ A).Nonempty ∧ (S ∩ B).Nonempty := by
    intro S
    constructor
    · intro hS
      obtain ⟨⟨SA, SB⟩, hp, rfl⟩ := Finset.mem_image.mp hS
      rcases Finset.mem_product.mp hp with ⟨hSA, hSB⟩
      have hSA' := hSA
      have hSB' := hSB
      simp only [RA_set, RB_set, rootedSubtreesIn, subtrees, Finset.mem_filter,
        Finset.mem_univ, true_and] at hSA' hSB'
      have h_sub_AB : SA ∪ SB ⊆ A ∪ B := Finset.union_subset_union hSA'.2.1 hSB'.2.1
      have h_tree : IsSubtree T (SA ∪ SB) := bridge_union_isSubtree hJ hSA hSB
      have h_in_sub : SA ∪ SB ∈ subtreesIn T (A ∪ B) := by
        simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨h_tree, h_sub_AB⟩
      have h_ne_A : ((SA ∪ SB) ∩ A).Nonempty := by
        rw [h_inter_left hSA'.2.1 hSB'.2.1]
        exact ⟨w, hSA'.2.2⟩
      have h_ne_B : ((SA ∪ SB) ∩ B).Nonempty := by
        rw [h_inter_right hSA'.2.1 hSB'.2.1]
        exact ⟨r_B, hSB'.2.2⟩
      exact ⟨h_in_sub, h_ne_A, h_ne_B⟩
    · rintro ⟨hS_in, hSA_ne, hSB_ne⟩
      simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hS_in
      rcases hS_in with ⟨hS_tree, hS_sub⟩
      have hSA_mem : S ∩ A ∈ RA_set := bridge_crossing_left hJ hS_sub hS_tree hSA_ne hSB_ne
      have hS_sub' : S ⊆ B ∪ A := by simpa [Finset.union_comm] using hS_sub
      have hSB_mem : S ∩ B ∈ RB_set :=
        bridge_crossing_left (isBridgeJoin_symm hJ) hS_sub' hS_tree hSB_ne hSA_ne
      refine Finset.mem_image.mpr ⟨(S ∩ A, S ∩ B), Finset.mem_product.mpr ⟨hSA_mem, hSB_mem⟩, ?_⟩
      dsimp [φ]
      rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hS_sub]
  have h_sub_of_inter_empty_right : ∀ {S : Finset (Fin n)}, S ⊆ A ∪ B → S ∩ B = ∅ → S ⊆ A := by
    intro S hS h_emp z hz
    rcases Finset.mem_union.mp (hS hz) with hzA | hzB
    · exact hzA
    · exfalso
      have : z ∈ (∅ : Finset (Fin n)) := h_emp ▸ Finset.mem_inter.mpr ⟨hz, hzB⟩
      exact Finset.notMem_empty z this
  have h_root_disj : Disjoint RA_set M := by
    rw [Finset.disjoint_left]
    intro S hS_RA hS_M
    obtain ⟨_, _, b, hb⟩ := (h_mem_M S).mp hS_M
    simp only [RA_set, rootedSubtreesIn, Finset.mem_filter] at hS_RA
    have hS_A : S ⊆ A := hS_RA.2.1
    exact Finset.disjoint_left.mp hJ.1 (hS_A (Finset.mem_inter.mp hb).1) (Finset.mem_inter.mp hb).2
  have h_root_part : rootedSubtreesIn T (A ∪ B) w = RA_set ∪ M := by
    ext S
    rw [Finset.mem_union, h_mem_M]
    constructor
    · intro hS
      simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hS
      rcases hS with ⟨hS_tree, hS_sub, hwS⟩
      rcases Finset.eq_empty_or_nonempty (S ∩ B) with h_emp | hSB_ne
      · left
        simp only [RA_set, rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hS_tree, h_sub_of_inter_empty_right hS_sub h_emp, hwS⟩
      · right
        have hS_in : S ∈ subtreesIn T (A ∪ B) := by
          simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hS_tree, hS_sub⟩
        exact ⟨hS_in, ⟨w, Finset.mem_inter.mpr ⟨hwS, hJ.2.1⟩⟩, hSB_ne⟩
    · rintro (hS_RA | ⟨hS_in, hSA_ne, hSB_ne⟩)
      · simp only [RA_set, rootedSubtreesIn, subtrees, Finset.mem_filter,
          Finset.mem_univ, true_and] at hS_RA ⊢
        exact ⟨hS_RA.1, Finset.Subset.trans hS_RA.2.1 Finset.subset_union_left, hS_RA.2.2⟩
      · simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hS_in
        have hSA_mem : S ∩ A ∈ RA_set :=
          bridge_crossing_left hJ hS_in.2 hS_in.1 hSA_ne hSB_ne
        simp only [RA_set, rootedSubtreesIn, Finset.mem_filter] at hSA_mem
        have hw_SA : w ∈ S ∩ A := hSA_mem.2.2
        simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hS_in.1, hS_in.2, (Finset.mem_inter.mp hw_SA).1⟩
  have h_eq1 : rootedCount T (A ∪ B) w = rootedCount T A w * (1 + rootedCount T B r_B) := by
    dsimp [rootedCount]
    rw [h_root_part, Finset.card_union_of_disjoint h_root_disj, hM_card]
    dsimp [RA_set, rootedCount]
    ring
  have h_eq2 : rootedOrderSum T (A ∪ B) w =
      rootedOrderSum T A w * (1 + rootedCount T B r_B) + rootedCount T A w * rootedOrderSum T B r_B := by
    dsimp [rootedOrderSum]
    rw [h_root_part, Finset.sum_union h_root_disj, hM_sum]
    dsimp [RA_set, rootedOrderSum]
    ring
  exact ⟨h_eq1, h_eq2⟩

theorem rooted_subtree_card_and_moment_bound : ∀ (n : ℕ) (T : SimpleGraph (Fin n))
    (U : Finset (Fin n)) (r : Fin n),
    T.IsTree → IsSubtree T U → r ∈ U →
    U.card ≤ rootedCount T U r ∧
    2 * rootedOrderSum T U r ≤ rootedCount T U r * (rootedCount T U r + 1) :=
by
  intro n T U₀ r₀ hT hU₀ hr₀
  classical
  have rooted_singleton_moments : ∀ (U : Finset (Fin n)) (w : Fin n),
      w ∈ U → U.card ≤ 1 →
      rootedCount T U w = 1 ∧
      rootedOrderSum T U w = 1 := by
    intro U w hw hle
    have hU_eq : U = {w} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      refine ⟨hw, fun x hx => Finset.card_le_one.mp hle x hx w hw⟩
    subst hU_eq
    have hw_sub : IsSubtree T {w} := by
      refine ⟨Finset.singleton_nonempty w, ?_⟩
      have : Nonempty ↑(({w} : Finset (Fin n)) : Set (Fin n)) := ⟨⟨w, by simp⟩⟩
      refine ⟨?_⟩
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      have ha' : a = w := by simpa using ha
      have hb' : b = w := by simpa using hb
      have hab : (⟨a, ha⟩ : ↑(({w} : Finset (Fin n)) : Set (Fin n))) = ⟨b, hb⟩ :=
        Subtype.ext (ha'.trans hb'.symm)
      rw [hab]
    have h_root_eq : rootedSubtreesIn T {w} w = {{w}} := by
      ext S
      simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h_ne, _⟩, h_sub, _⟩
        rcases Finset.subset_singleton_iff.mp h_sub with rfl | rfl
        · exact False.elim (Finset.not_nonempty_empty h_ne)
        · rfl
      · rintro rfl
        exact ⟨hw_sub, Finset.Subset.refl _, Finset.mem_singleton_self w⟩
    simp [rootedCount, rootedOrderSum, h_root_eq]
  have isBridgeJoin_symm : ∀ {A B : Finset (Fin n)} {w r_B : Fin n},
      IsBridgeJoin T A B w r_B → IsBridgeJoin T B A r_B w := by
    intro A B w r_B hJ
    rcases hJ with ⟨h_disj, hw, hr_B, hadj, h_bridge⟩
    refine ⟨h_disj.symm, hr_B, hw, T.symm hadj, ?_⟩
    intro u hu v hv huv
    exact (h_bridge v hv u hu (T.symm huv)).symm
  have exists_walk_of_isSubtree : ∀ {S : Finset (Fin n)},
      IsSubtree T S → ∀ {a b : Fin n}, a ∈ S → b ∈ S →
      ∃ q : T.Walk a b, ∀ z ∈ q.support, z ∈ S := by
    intro S hS a b ha hb
    obtain ⟨q₀⟩ := hS.2.preconnected ⟨a, ha⟩ ⟨b, hb⟩
    suffices ∀ {u v : ↑(S : Set (Fin n))} (q : (T.induce (S : Set (Fin n))).Walk u v),
        ∃ q' : T.Walk u.1 v.1, ∀ z ∈ q'.support, z ∈ S from this q₀
    intro u v q
    induction q with
    | @nil u =>
      refine ⟨SimpleGraph.Walk.nil, ?_⟩
      intro z hz
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      rw [hz]
      exact Finset.mem_coe.mp u.2
    | @cons u c v hadj q' ih =>
      obtain ⟨q₁, hq₁⟩ := ih
      refine ⟨SimpleGraph.Walk.cons hadj q₁, ?_⟩
      intro z hz
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz'
      · exact Finset.mem_coe.mp u.2
      · exact hq₁ z hz'
  have bridge_walk_mem_edges : ∀ {A B : Finset (Fin n)} {w r_B : Fin n},
      IsBridgeJoin T A B w r_B → ∀ {a b : Fin n} (q : T.Walk a b),
      (∀ z ∈ q.support, z ∈ A ∪ B) →
      ((a ∈ A ∧ b ∈ B) ∨ (a ∈ B ∧ b ∈ A)) →
      s(w, r_B) ∈ q.edges := by
    intro A B w r_B hJ a b q
    induction q with
    | nil =>
      intro _ h_ab
      rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact False.elim (Finset.disjoint_left.mp hJ.1 ha hb)
      · exact False.elim (Finset.disjoint_left.mp hJ.1 hb ha)
    | @cons a c b h_step q' ih =>
      intro h_supp h_ab
      have hc_mem : c ∈ A ∪ B := h_supp c (by
        simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.start_mem_support])
      have h_supp' : ∀ z ∈ q'.support, z ∈ A ∪ B := fun z hz =>
        h_supp z (by simp [SimpleGraph.Walk.support_cons, hz])
      rcases Finset.mem_union.mp hc_mem with hcA | hcB
      · rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ (ih h_supp' (Or.inl ⟨hcA, hb⟩))
        · obtain ⟨hcw, har⟩ := hJ.2.2.2.2 c hcA a ha (T.symm h_step)
          subst hcw har
          rw [SimpleGraph.Walk.edges_cons, Sym2.eq_swap]
          exact List.mem_cons_self
      · rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · obtain ⟨haw, hcr⟩ := hJ.2.2.2.2 a ha c hcB h_step
          subst haw hcr
          rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_self
        · rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ (ih h_supp' (Or.inr ⟨hcB, hb⟩))
  have bridge_path_support_left : ∀ {A B : Finset (Fin n)} {w r_B : Fin n},
      IsBridgeJoin T A B w r_B → ∀ {a b : Fin n} (p : T.Walk a b), p.IsPath →
      (∀ z ∈ p.support, z ∈ A ∪ B) → a ∈ A → b ∈ A →
      ∀ z ∈ p.support, z ∈ A := by
    intro A B w r_B hJ a b p hp h_supp ha hb z hz
    rcases Finset.mem_union.mp (h_supp z hz) with hzA | hzB
    · exact hzA
    · exfalso
      let p₁ := p.takeUntil z hz
      let p₂ := p.dropUntil z hz
      have hp₁_supp : ∀ x ∈ p₁.support, x ∈ A ∪ B :=
        fun x hx => h_supp x (p.support_takeUntil_subset hz hx)
      have hp₂_supp : ∀ x ∈ p₂.support, x ∈ A ∪ B :=
        fun x hx => h_supp x (p.support_dropUntil_subset hz hx)
      have he₁ : s(w, r_B) ∈ p₁.edges :=
        bridge_walk_mem_edges hJ p₁ hp₁_supp (Or.inl ⟨ha, hzB⟩)
      have he₂ : s(w, r_B) ∈ p₂.edges :=
        bridge_walk_mem_edges hJ p₂ hp₂_supp (Or.inr ⟨hzB, hb⟩)
      have h_nodup : p.edges.Nodup := hp.isTrail.edges_nodup
      have h_edges : p₁.edges ++ p₂.edges = p.edges := by
        rw [← SimpleGraph.Walk.edges_append, p.take_spec hz]
      rw [← h_edges, List.nodup_append] at h_nodup
      exact h_nodup.2.2 s(w, r_B) he₁ s(w, r_B) he₂ rfl
  have subtree_exists_root_bridge_split : ∀ (U : Finset (Fin n)) (w : Fin n),
      IsSubtree T U → w ∈ U → 2 ≤ U.card →
      ∃ (A B : Finset (Fin n)) (r_B : Fin n),
        U = A ∪ B ∧ IsSubtree T A ∧ IsSubtree T B ∧ IsBridgeJoin T A B w r_B := by
    intro U w hU hw hge2
    obtain ⟨u, hu, huw⟩ := Finset.exists_mem_ne (by omega : 1 < U.card) w
    obtain ⟨p₀⟩ := hU.2.preconnected ⟨w, hw⟩ ⟨u, hu⟩
    have h_adj_exists : ∃ r_B ∈ U, T.Adj w r_B := by
      cases p₀ with
      | nil => exact False.elim (huw rfl)
      | @cons _ r _ hadj _ => exact ⟨r.1, r.2, hadj⟩
    obtain ⟨r_B, hr_B_U, hadj_wr⟩ := h_adj_exists
    let T₀ := T \ SimpleGraph.fromEdgeSet {s(w, r_B)}
    have h_bridge_wr : T.IsBridge s(w, r_B) :=
      SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.IsAcyclic hadj_wr
    have h_not_reach : ¬ T₀.Reachable w r_B :=
      (SimpleGraph.isBridge_iff.mp h_bridge_wr).2
    let A := U.filter (fun v => T₀.Reachable w v)
    let B := U \ A
    have hA_sub : A ⊆ U := Finset.filter_subset _ U
    have hU_eq : U = A ∪ B := (Finset.union_sdiff_of_subset hA_sub).symm
    have h_disj : Disjoint A B := Finset.disjoint_sdiff
    have hw_A : w ∈ A := Finset.mem_filter.mpr ⟨hw, SimpleGraph.Reachable.refl w⟩
    have hr_B : r_B ∈ B := by
      rw [Finset.mem_sdiff]
      refine ⟨hr_B_U, ?_⟩
      rw [Finset.mem_filter]
      rintro ⟨_, h_reach⟩
      exact h_not_reach h_reach
    have hJ : IsBridgeJoin T A B w r_B := by
      refine ⟨h_disj, hw_A, hr_B, hadj_wr, ?_⟩
      intro a ha b hb hab
      by_cases h_edge : s(a, b) = s(w, r_B)
      · rw [Sym2.eq_iff] at h_edge
        rcases h_edge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨rfl, rfl⟩
        · exact False.elim (Finset.disjoint_left.mp h_disj ha hr_B)
      · exfalso
        have hab₀ : T₀.Adj a b := by
          dsimp [T₀]
          rw [SimpleGraph.sdiff_adj, SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff]
          exact ⟨hab, fun ⟨h_eq, _⟩ => h_edge h_eq⟩
        have ha_reach : T₀.Reachable w a := (Finset.mem_filter.mp ha).2
        have hb_reach : T₀.Reachable w b := ha_reach.trans hab₀.reachable
        have hb_A : b ∈ A := Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hb).1, hb_reach⟩
        exact (Finset.mem_sdiff.mp hb).2 hb_A
    have hA_subtree : IsSubtree T A := by
      refine ⟨⟨w, hw_A⟩, ?_⟩
      have : Nonempty ↑(A : Set (Fin n)) := ⟨⟨w, hw_A⟩⟩
      refine ⟨?_⟩
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      have hxU : x ∈ U := hA_sub hx
      have hyU : y ∈ U := hA_sub hy
      obtain ⟨q, hq_supp⟩ := exists_walk_of_isSubtree hU hxU hyU
      let p : T.Walk x y := (q.toPath : T.Walk x y)
      have hp_path : p.IsPath := q.toPath.2
      have hp_supp : ∀ z ∈ p.support, z ∈ A ∪ B := by
        intro z hz
        rw [← hU_eq]
        exact hq_supp z (q.support_toPath_subset hz)
      have hp_A : ∀ z ∈ p.support, z ∈ (A : Set (Fin n)) :=
        bridge_path_support_left hJ p hp_path hp_supp hx hy
      exact (p.induce (A : Set (Fin n)) hp_A).reachable
    have hB_subtree : IsSubtree T B := by
      refine ⟨⟨r_B, hr_B⟩, ?_⟩
      have : Nonempty ↑(B : Set (Fin n)) := ⟨⟨r_B, hr_B⟩⟩
      refine ⟨?_⟩
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      have hxU : x ∈ U := Finset.sdiff_subset hx
      have hyU : y ∈ U := Finset.sdiff_subset hy
      obtain ⟨q, hq_supp⟩ := exists_walk_of_isSubtree hU hxU hyU
      let p : T.Walk x y := (q.toPath : T.Walk x y)
      have hp_path : p.IsPath := q.toPath.2
      have hp_supp : ∀ z ∈ p.support, z ∈ B ∪ A := by
        intro z hz
        rw [Finset.union_comm, ← hU_eq]
        exact hq_supp z (q.support_toPath_subset hz)
      have hp_B : ∀ z ∈ p.support, z ∈ (B : Set (Fin n)) :=
        bridge_path_support_left (isBridgeJoin_symm hJ) p hp_path hp_supp hx hy
      exact (p.induce (B : Set (Fin n)) hp_B).reachable
    exact ⟨A, B, r_B, hU_eq, hA_subtree, hB_subtree, hJ⟩
  have bridge_crossing_left : ∀ {A B S : Finset (Fin n)} {w r_B : Fin n},
      IsBridgeJoin T A B w r_B → S ⊆ A ∪ B →
      IsSubtree T S → (S ∩ A).Nonempty → (S ∩ B).Nonempty →
      S ∩ A ∈ rootedSubtreesIn T A w := by
    intro A B S w r_B hJ hS_sub hS hSA hSB
    obtain ⟨a₀, ha₀⟩ := hSA
    obtain ⟨b₀, hb₀⟩ := hSB
    have ha₀S : a₀ ∈ S := (Finset.mem_inter.mp ha₀).1
    have ha₀A : a₀ ∈ A := (Finset.mem_inter.mp ha₀).2
    have hb₀S : b₀ ∈ S := (Finset.mem_inter.mp hb₀).1
    have hb₀B : b₀ ∈ B := (Finset.mem_inter.mp hb₀).2
    obtain ⟨q, hq_supp⟩ := exists_walk_of_isSubtree hS ha₀S hb₀S
    have hq_AB : ∀ z ∈ q.support, z ∈ A ∪ B := fun z hz => hS_sub (hq_supp z hz)
    have he : s(w, r_B) ∈ q.edges :=
      bridge_walk_mem_edges hJ q hq_AB (Or.inl ⟨ha₀A, hb₀B⟩)
    have hwS : w ∈ S := hq_supp w (q.fst_mem_support_of_mem_edges he)
    have hwSA : w ∈ S ∩ A := Finset.mem_inter.mpr ⟨hwS, hJ.2.1⟩
    have hSA_subtree : IsSubtree T (S ∩ A) := by
      refine ⟨⟨w, hwSA⟩, ?_⟩
      have : Nonempty ↑((S ∩ A : Finset (Fin n)) : Set (Fin n)) := ⟨⟨w, hwSA⟩⟩
      refine ⟨?_⟩
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      have hxS : x ∈ S := (Finset.mem_inter.mp hx).1
      have hxA : x ∈ A := (Finset.mem_inter.mp hx).2
      have hyS : y ∈ S := (Finset.mem_inter.mp hy).1
      have hyA : y ∈ A := (Finset.mem_inter.mp hy).2
      obtain ⟨q₁, hq₁_supp⟩ := exists_walk_of_isSubtree hS hxS hyS
      let p : T.Walk x y := (q₁.toPath : T.Walk x y)
      have hp_path : p.IsPath := q₁.toPath.2
      have hp_S : ∀ z ∈ p.support, z ∈ S := fun z hz => hq₁_supp z (q₁.support_toPath_subset hz)
      have hp_AB : ∀ z ∈ p.support, z ∈ A ∪ B := fun z hz => hS_sub (hp_S z hz)
      have hp_A : ∀ z ∈ p.support, z ∈ A :=
        bridge_path_support_left hJ p hp_path hp_AB hxA hyA
      have hp_SA : ∀ z ∈ p.support, z ∈ ((S ∩ A : Finset (Fin n)) : Set (Fin n)) :=
        fun z hz => Finset.mem_inter.mpr ⟨hp_S z hz, hp_A z hz⟩
      exact (p.induce ((S ∩ A : Finset (Fin n)) : Set (Fin n)) hp_SA).reachable
    simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hSA_subtree, Finset.inter_subset_right, hwSA⟩
  have bridge_union_isSubtree : ∀ {A B SA SB : Finset (Fin n)} {w r_B : Fin n},
      IsBridgeJoin T A B w r_B →
      SA ∈ rootedSubtreesIn T A w → SB ∈ rootedSubtreesIn T B r_B →
      IsSubtree T (SA ∪ SB) := by
    intro A B SA SB w r_B hJ hSA hSB
    simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hSA hSB
    rcases hSA with ⟨hSA_sub, _, hw_SA⟩
    rcases hSB with ⟨hSB_sub, _, hr_SB⟩
    have hw_U : w ∈ SA ∪ SB := Finset.mem_union_left SB hw_SA
    have hr_U : r_B ∈ SA ∪ SB := Finset.mem_union_right SA hr_SB
    refine ⟨⟨w, hw_U⟩, ?_⟩
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨w, hw_U⟩, ?_⟩
    rintro ⟨x, hx⟩
    rcases Finset.mem_union.mp hx with hxA | hxB
    · obtain ⟨q, hq⟩ := exists_walk_of_isSubtree hSA_sub hw_SA hxA
      have hq_U : ∀ z ∈ q.support, z ∈ ((SA ∪ SB : Finset (Fin n)) : Set (Fin n)) :=
        fun z hz => Finset.mem_union_left SB (hq z hz)
      exact (q.induce ((SA ∪ SB : Finset (Fin n)) : Set (Fin n)) hq_U).reachable
    · obtain ⟨q, hq⟩ := exists_walk_of_isSubtree hSB_sub hr_SB hxB
      have hq_U : ∀ z ∈ q.support, z ∈ ((SA ∪ SB : Finset (Fin n)) : Set (Fin n)) :=
        fun z hz => Finset.mem_union_right SA (hq z hz)
      have hadj_ind : (T.induce ((SA ∪ SB : Finset (Fin n)) : Set (Fin n))).Adj ⟨w, hw_U⟩ ⟨r_B, hr_U⟩ :=
        hJ.2.2.2.1
      exact hadj_ind.reachable.trans (q.induce ((SA ∪ SB : Finset (Fin n)) : Set (Fin n)) hq_U).reachable
  have bridge_join_rooted_moments_local : ∀ (A B : Finset (Fin n)) (w r_B : Fin n),
      IsBridgeJoin T A B w r_B →
      rootedCount T (A ∪ B) w = rootedCount T A w * (1 + rootedCount T B r_B) ∧
      rootedOrderSum T (A ∪ B) w =
        rootedOrderSum T A w * (1 + rootedCount T B r_B) + rootedCount T A w * rootedOrderSum T B r_B := by
    intro A B w r_B hJ
    let RA_set := rootedSubtreesIn T A w
    let RB_set := rootedSubtreesIn T B r_B
    let φ : Finset (Fin n) × Finset (Fin n) → Finset (Fin n) := fun p => p.1 ∪ p.2
    let M := (RA_set ×ˢ RB_set).image φ
    have h_inter_left : ∀ {X Y : Finset (Fin n)}, X ⊆ A → Y ⊆ B → (X ∪ Y) ∩ A = X := by
      intro X Y hX hY
      ext z
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hzX | hzY, hzA⟩
        · exact hzX
        · exact False.elim (Finset.disjoint_left.mp hJ.1 hzA (hY hzY))
      · intro hzX
        exact ⟨Or.inl hzX, hX hzX⟩
    have h_inter_right : ∀ {X Y : Finset (Fin n)}, X ⊆ A → Y ⊆ B → (X ∪ Y) ∩ B = Y := by
      intro X Y hX hY
      ext z
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hzX | hzY, hzB⟩
        · exact False.elim (Finset.disjoint_left.mp hJ.1 (hX hzX) hzB)
        · exact hzY
      · intro hzY
        exact ⟨Or.inr hzY, hY hzY⟩
    have h_inj : Set.InjOn φ ((RA_set ×ˢ RB_set : Finset (Finset (Fin n) × Finset (Fin n))) : Set (Finset (Fin n) × Finset (Fin n))) := by
      intro p₁ hp₁ p₂ hp₂ h_eq
      rcases Finset.mem_product.mp (Finset.mem_coe.mp hp₁) with ⟨hp₁A, hp₁B⟩
      rcases Finset.mem_product.mp (Finset.mem_coe.mp hp₂) with ⟨hp₂A, hp₂B⟩
      have h1A : p₁.1 ⊆ A := by
        simp only [RA_set, rootedSubtreesIn, Finset.mem_filter] at hp₁A
        exact hp₁A.2.1
      have h1B : p₁.2 ⊆ B := by
        simp only [RB_set, rootedSubtreesIn, Finset.mem_filter] at hp₁B
        exact hp₁B.2.1
      have h2A : p₂.1 ⊆ A := by
        simp only [RA_set, rootedSubtreesIn, Finset.mem_filter] at hp₂A
        exact hp₂A.2.1
      have h2B : p₂.2 ⊆ B := by
        simp only [RB_set, rootedSubtreesIn, Finset.mem_filter] at hp₂B
        exact hp₂B.2.1
      have h1 : p₁.1 = p₂.1 := by
        calc p₁.1 = (p₁.1 ∪ p₁.2) ∩ A := (h_inter_left h1A h1B).symm
          _ = (p₂.1 ∪ p₂.2) ∩ A := by rw [show p₁.1 ∪ p₁.2 = p₂.1 ∪ p₂.2 from h_eq]
          _ = p₂.1 := h_inter_left h2A h2B
      have h2 : p₁.2 = p₂.2 := by
        calc p₁.2 = (p₁.1 ∪ p₁.2) ∩ B := (h_inter_right h1A h1B).symm
          _ = (p₂.1 ∪ p₂.2) ∩ B := by rw [show p₁.1 ∪ p₁.2 = p₂.1 ∪ p₂.2 from h_eq]
          _ = p₂.2 := h_inter_right h2A h2B
      exact Prod.ext h1 h2
    have hM_card : M.card = rootedCount T A w * rootedCount T B r_B := by
      dsimp [M, RA_set, RB_set, rootedCount]
      rw [Finset.card_image_of_injOn h_inj, Finset.card_product]
    have hM_sum : ∑ S ∈ M, S.card =
        rootedOrderSum T A w * rootedCount T B r_B + rootedCount T A w * rootedOrderSum T B r_B := by
      dsimp [M]
      rw [Finset.sum_image h_inj, Finset.sum_product]
      have h_inner : ∀ x ∈ RA_set,
          ∑ y ∈ RB_set, (x ∪ y).card = x.card * RB_set.card + ∑ y ∈ RB_set, y.card := by
        intro x hx
        have hx_sub : x ⊆ A := by
          simp only [RA_set, rootedSubtreesIn, Finset.mem_filter] at hx
          exact hx.2.1
        have h_congr : ∑ y ∈ RB_set, (x ∪ y).card = ∑ y ∈ RB_set, (x.card + y.card) := by
          refine Finset.sum_congr rfl fun y hy => ?_
          have hy_sub : y ⊆ B := by
            simp only [RB_set, rootedSubtreesIn, Finset.mem_filter] at hy
            exact hy.2.1
          exact Finset.card_union_of_disjoint (Disjoint.mono hx_sub hy_sub hJ.1)
        rw [h_congr, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
      rw [Finset.sum_congr rfl h_inner, Finset.sum_add_distrib, ← Finset.sum_mul,
        Finset.sum_const, smul_eq_mul]
      rfl
    have h_mem_M : ∀ S : Finset (Fin n),
        S ∈ M ↔ S ∈ subtreesIn T (A ∪ B) ∧ (S ∩ A).Nonempty ∧ (S ∩ B).Nonempty := by
      intro S
      constructor
      · intro hS
        obtain ⟨⟨SA, SB⟩, hp, rfl⟩ := Finset.mem_image.mp hS
        rcases Finset.mem_product.mp hp with ⟨hSA, hSB⟩
        have hSA' := hSA
        have hSB' := hSB
        simp only [RA_set, RB_set, rootedSubtreesIn, subtrees, Finset.mem_filter,
          Finset.mem_univ, true_and] at hSA' hSB'
        have h_sub_AB : SA ∪ SB ⊆ A ∪ B := Finset.union_subset_union hSA'.2.1 hSB'.2.1
        have h_tree : IsSubtree T (SA ∪ SB) := bridge_union_isSubtree hJ hSA hSB
        have h_in_sub : SA ∪ SB ∈ subtreesIn T (A ∪ B) := by
          simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨h_tree, h_sub_AB⟩
        have h_ne_A : ((SA ∪ SB) ∩ A).Nonempty := by
          rw [h_inter_left hSA'.2.1 hSB'.2.1]
          exact ⟨w, hSA'.2.2⟩
        have h_ne_B : ((SA ∪ SB) ∩ B).Nonempty := by
          rw [h_inter_right hSA'.2.1 hSB'.2.1]
          exact ⟨r_B, hSB'.2.2⟩
        exact ⟨h_in_sub, h_ne_A, h_ne_B⟩
      · rintro ⟨hS_in, hSA_ne, hSB_ne⟩
        simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hS_in
        rcases hS_in with ⟨hS_tree, hS_sub⟩
        have hSA_mem : S ∩ A ∈ RA_set := bridge_crossing_left hJ hS_sub hS_tree hSA_ne hSB_ne
        have hS_sub' : S ⊆ B ∪ A := by simpa [Finset.union_comm] using hS_sub
        have hSB_mem : S ∩ B ∈ RB_set :=
          bridge_crossing_left (isBridgeJoin_symm hJ) hS_sub' hS_tree hSB_ne hSA_ne
        refine Finset.mem_image.mpr ⟨(S ∩ A, S ∩ B), Finset.mem_product.mpr ⟨hSA_mem, hSB_mem⟩, ?_⟩
        dsimp [φ]
        rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hS_sub]
    have h_sub_of_inter_empty_right : ∀ {S : Finset (Fin n)}, S ⊆ A ∪ B → S ∩ B = ∅ → S ⊆ A := by
      intro S hS h_emp z hz
      rcases Finset.mem_union.mp (hS hz) with hzA | hzB
      · exact hzA
      · exfalso
        have : z ∈ (∅ : Finset (Fin n)) := h_emp ▸ Finset.mem_inter.mpr ⟨hz, hzB⟩
        exact Finset.notMem_empty z this
    have h_root_disj : Disjoint RA_set M := by
      rw [Finset.disjoint_left]
      intro S hS_RA hS_M
      obtain ⟨_, _, b, hb⟩ := (h_mem_M S).mp hS_M
      have hS_A : S ⊆ A := by
        simp only [RA_set, rootedSubtreesIn, Finset.mem_filter] at hS_RA
        exact hS_RA.2.1
      exact Finset.disjoint_left.mp hJ.1 (hS_A (Finset.mem_inter.mp hb).1) (Finset.mem_inter.mp hb).2
    have h_root_part : rootedSubtreesIn T (A ∪ B) w = RA_set ∪ M := by
      ext S
      rw [Finset.mem_union, h_mem_M]
      constructor
      · intro hS
        simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hS
        rcases hS with ⟨hS_tree, hS_sub, hwS⟩
        rcases Finset.eq_empty_or_nonempty (S ∩ B) with h_emp | hSB_ne
        · left
          simp only [RA_set, rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hS_tree, h_sub_of_inter_empty_right hS_sub h_emp, hwS⟩
        · right
          have hS_in : S ∈ subtreesIn T (A ∪ B) := by
            simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hS_tree, hS_sub⟩
          exact ⟨hS_in, ⟨w, Finset.mem_inter.mpr ⟨hwS, hJ.2.1⟩⟩, hSB_ne⟩
      · rintro (hS_RA | ⟨hS_in, hSA_ne, hSB_ne⟩)
        · simp only [RA_set, rootedSubtreesIn, subtrees, Finset.mem_filter,
            Finset.mem_univ, true_and] at hS_RA ⊢
          exact ⟨hS_RA.1, Finset.Subset.trans hS_RA.2.1 Finset.subset_union_left, hS_RA.2.2⟩
        · simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hS_in
          have hSA_mem : S ∩ A ∈ RA_set :=
            bridge_crossing_left hJ hS_in.2 hS_in.1 hSA_ne hSB_ne
          have hw_SA : w ∈ S ∩ A := by
            simp only [RA_set, rootedSubtreesIn, Finset.mem_filter] at hSA_mem
            exact hSA_mem.2.2
          simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hS_in.1, hS_in.2, (Finset.mem_inter.mp hw_SA).1⟩
    have h_eq1 : rootedCount T (A ∪ B) w = rootedCount T A w * (1 + rootedCount T B r_B) := by
      dsimp [rootedCount]
      rw [h_root_part, Finset.card_union_of_disjoint h_root_disj, hM_card]
      dsimp [RA_set, rootedCount]
      ring
    have h_eq2 : rootedOrderSum T (A ∪ B) w =
        rootedOrderSum T A w * (1 + rootedCount T B r_B) + rootedCount T A w * rootedOrderSum T B r_B := by
      dsimp [rootedOrderSum]
      rw [h_root_part, Finset.sum_union h_root_disj, hM_sum]
      dsimp [RA_set, rootedOrderSum]
      ring
    exact ⟨h_eq1, h_eq2⟩
  have rooted_card_and_moment_step : ∀ (c₁ c₂ s₁ t₁ s₂ t₂ : ℕ),
      1 ≤ c₁ → c₁ ≤ s₁ → 2 * t₁ ≤ s₁ * (s₁ + 1) →
      1 ≤ c₂ → c₂ ≤ s₂ → 2 * t₂ ≤ s₂ * (s₂ + 1) →
      c₁ + c₂ ≤ s₁ * (1 + s₂) ∧
      2 * (t₁ * (1 + s₂) + s₁ * t₂) ≤ (s₁ * (1 + s₂)) * (s₁ * (1 + s₂) + 1) := by
    intro c₁ c₂ s₁ t₁ s₂ t₂ hc₁ hcs₁ ht₁ hc₂ hcs₂ ht₂
    have hs₁ : 1 ≤ s₁ := le_trans hc₁ hcs₁
    have h_mul : s₂ ≤ s₁ * s₂ := by
      simpa using Nat.mul_le_mul_right s₂ hs₁
    refine ⟨by linarith, ?_⟩
    have h1 : (2 * t₁) * (1 + s₂) ≤ (s₁ * (s₁ + 1)) * (1 + s₂) :=
      Nat.mul_le_mul_right (1 + s₂) ht₁
    have h2 : s₁ * (2 * t₂) ≤ s₁ * (s₂ * (s₂ + 1)) :=
      Nat.mul_le_mul_left s₁ ht₂
    have h_sum_le : s₁ + s₂ + 1 ≤ s₁ * (1 + s₂) + 1 := by linarith
    have h3 : (s₁ * (1 + s₂)) * (s₁ + s₂ + 1) ≤ (s₁ * (1 + s₂)) * (s₁ * (1 + s₂) + 1) :=
      Nat.mul_le_mul_left (s₁ * (1 + s₂)) h_sum_le
    calc 2 * (t₁ * (1 + s₂) + s₁ * t₂)
      _ = (2 * t₁) * (1 + s₂) + s₁ * (2 * t₂) := by ring
      _ ≤ (s₁ * (s₁ + 1)) * (1 + s₂) + s₁ * (s₂ * (s₂ + 1)) := Nat.add_le_add h1 h2
      _ = (s₁ * (1 + s₂)) * (s₁ + s₂ + 1) := by ring
      _ ≤ (s₁ * (1 + s₂)) * (s₁ * (1 + s₂) + 1) := h3
  have h_ind : ∀ (m : ℕ) (U : Finset (Fin n)) (w : Fin n),
      U.card = m → IsSubtree T U → w ∈ U →
      U.card ≤ rootedCount T U w ∧
      2 * rootedOrderSum T U w ≤ rootedCount T U w * (rootedCount T U w + 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro U w hm hU hw
      by_cases hle : U.card ≤ 1
      · obtain ⟨hs, ht⟩ := rooted_singleton_moments U w hw hle
        rw [hs, ht]
        omega
      · push_neg at hle
        obtain ⟨A, B, r_B, hU_eq, hA_sub, hB_sub, hJ⟩ :=
          subtree_exists_root_bridge_split U w hU hw hle
        have hc₁ : 1 ≤ A.card := Finset.card_pos.mpr ⟨w, hJ.2.1⟩
        have hc₂ : 1 ≤ B.card := Finset.card_pos.mpr ⟨r_B, hJ.2.2.1⟩
        have hU_card : U.card = A.card + B.card := by
          rw [hU_eq, Finset.card_union_of_disjoint hJ.1]
        have hA_lt : A.card < m := by omega
        have hB_lt : B.card < m := by omega
        obtain ⟨hcs₁, ht₁⟩ := ih A.card hA_lt A w rfl hA_sub hJ.2.1
        obtain ⟨hcs₂, ht₂⟩ := ih B.card hB_lt B r_B rfl hB_sub hJ.2.2.1
        obtain ⟨h_s, h_t⟩ := bridge_join_rooted_moments_local A B w r_B hJ
        rw [hU_card, hU_eq, h_s, h_t]
        exact rooted_card_and_moment_step A.card B.card
          (rootedCount T A w) (rootedOrderSum T A w)
          (rootedCount T B r_B) (rootedOrderSum T B r_B)
          hc₁ hcs₁ ht₁ hc₂ hcs₂ ht₂
  exact h_ind U₀.card U₀ r₀ rfl hU₀ hr₀

theorem min_arm_base_host_bounds : ∀ (n : ℕ) (hn : 1 ≤ n) (T : SimpleGraph (Fin n)),
    T.IsTree → ∀ (ℓ : ℕ) (A₀ B C P : Finset (Fin n)) (w r_B r_C : Fin n)
      (v : Fin (ℓ + 1) → Fin n) (L : Fin (ℓ + 1) → Finset (Fin n)),
      IsMinCountTerminalArm T ℓ A₀ B C P w r_B r_C v L →
      let H₀ := armPrefixHost ℓ A₀ B C v L 0
      let w₀ := armPrefixRoot ℓ w v 0 (Nat.zero_le (ℓ + 1))
      IsSubtree T H₀ ∧ w₀ ∈ H₀ ∧
        (rootedCount T P (v 0) + 1) ^ 2 ≤ rootedCount T H₀ w₀ ∧
        (rootedCount T P (v 0) + 1) ^ 2 * rootedOrderSum T H₀ w₀ ≤
          (rootedCount T P (v 0) + 1 + 0) * (rootedCount T H₀ w₀) ^ 2 :=
by
  intro n _hn T hT ℓ A₀ B C P w r_B r_C v L h_arm H₀ w₀
  rcases h_arm with ⟨_, _, hA₀_sub, hB_sub, hC_sub, _, _, _, _, _, _, _, _, _,
    h_bridge_B, h_bridge_C, _, _, _, hx_dom, hy_dom⟩
  have hH₀_eq : H₀ = A₀ ∪ B ∪ C := by
    dsimp [H₀, armPrefixHost]
    have h_emp : Finset.univ.filter (fun i : Fin (ℓ + 1) => i.val < 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro i _
      exact Nat.not_lt_zero i.val
    rw [h_emp, Finset.biUnion_empty, Finset.union_empty]
  have hw₀_eq : w₀ = w := by
    dsimp [w₀, armPrefixRoot]
  have hw : w ∈ A₀ := h_bridge_B.2.1
  have hr_B : r_B ∈ B := h_bridge_B.2.2.1
  have hr_C : r_C ∈ C := h_bridge_C.2.2.1
  have hw₀_mem : w₀ ∈ H₀ := by
    rw [hH₀_eq, hw₀_eq]
    exact Finset.mem_union_left C (Finset.mem_union_left B hw)
  have h_bridge_sub : ∀ (U₁ U₂ : Finset (Fin n)) (r₁ r₂ : Fin n),
      IsSubtree T U₁ → IsSubtree T U₂ → IsBridgeJoin T U₁ U₂ r₁ r₂ →
      IsSubtree T (U₁ ∪ U₂) := by
    intro U₁ U₂ r₁ r₂ hU₁ hU₂ hb
    rcases hb with ⟨_, hr₁, hr₂, hadj, _⟩
    refine ⟨⟨r₁, Finset.mem_union_left U₂ hr₁⟩, ?_⟩
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    let r₁' : (↑(U₁ ∪ U₂ : Finset (Fin n)) : Set (Fin n)) :=
      ⟨r₁, Finset.mem_coe.mpr (Finset.mem_union_left U₂ hr₁)⟩
    let r₂' : (↑(U₁ ∪ U₂ : Finset (Fin n)) : Set (Fin n)) :=
      ⟨r₂, Finset.mem_coe.mpr (Finset.mem_union_right U₁ hr₂)⟩
    let ι₁ : T.induce (U₁ : Set (Fin n)) →g T.induce ((U₁ ∪ U₂ : Finset (Fin n)) : Set (Fin n)) :=
      { toFun := fun x => ⟨x.1, Finset.mem_coe.mpr (Finset.mem_union_left U₂ (Finset.mem_coe.mp x.2))⟩
        map_rel' := fun h => h }
    let ι₂ : T.induce (U₂ : Set (Fin n)) →g T.induce ((U₁ ∪ U₂ : Finset (Fin n)) : Set (Fin n)) :=
      { toFun := fun x => ⟨x.1, Finset.mem_coe.mpr (Finset.mem_union_right U₁ (Finset.mem_coe.mp x.2))⟩
        map_rel' := fun h => h }
    refine ⟨r₁', fun z => ?_⟩
    rcases Finset.mem_union.mp (Finset.mem_coe.mp z.2) with hz₁ | hz₂
    · obtain ⟨p⟩ := hU₁.2.preconnected ⟨r₁, Finset.mem_coe.mpr hr₁⟩ ⟨z.1, Finset.mem_coe.mpr hz₁⟩
      exact ⟨p.map ι₁⟩
    · have hr₁₂ : (T.induce ((U₁ ∪ U₂ : Finset (Fin n)) : Set (Fin n))).Reachable r₁' r₂' :=
        SimpleGraph.Adj.reachable hadj
      obtain ⟨p⟩ := hU₂.2.preconnected ⟨r₂, Finset.mem_coe.mpr hr₂⟩ ⟨z.1, Finset.mem_coe.mpr hz₂⟩
      exact hr₁₂.trans ⟨p.map ι₂⟩
  have hAB_sub : IsSubtree T (A₀ ∪ B) := h_bridge_sub A₀ B w r_B hA₀_sub hB_sub h_bridge_B
  have hH₀_sub : IsSubtree T H₀ := by
    rw [hH₀_eq]
    exact h_bridge_sub (A₀ ∪ B) C w r_C hAB_sub hC_sub h_bridge_C
  obtain ⟨hS_AB, ht_AB⟩ := bridge_join_rooted_moments n T A₀ B w r_B h_bridge_B
  obtain ⟨hS_ABC, ht_ABC⟩ := bridge_join_rooted_moments n T (A₀ ∪ B) C w r_C h_bridge_C
  obtain ⟨hA₀_card, htA₀⟩ := rooted_subtree_card_and_moment_bound n T A₀ w hT hA₀_sub hw
  obtain ⟨_hB_card, htB⟩ := rooted_subtree_card_and_moment_bound n T B r_B hT hB_sub hr_B
  obtain ⟨_hC_card, htC⟩ := rooted_subtree_card_and_moment_bound n T C r_C hT hC_sub hr_C
  set ρ := rootedCount T P (v 0)
  set p := rootedCount T A₀ w
  set tA₀ := rootedOrderSum T A₀ w
  set x := rootedCount T B r_B
  set tB := rootedOrderSum T B r_B
  set y := rootedCount T C r_C
  set tC := rootedOrderSum T C r_C
  set S₀ := rootedCount T H₀ w₀
  set t₀ := rootedOrderSum T H₀ w₀
  have hA₀_pos : 1 ≤ A₀.card := Finset.card_pos.mpr ⟨w, hw⟩
  have hp_pos : 1 ≤ p := le_trans hA₀_pos hA₀_card
  have hS₀ : S₀ = p * (1 + x) * (1 + y) := by
    dsimp [S₀]
    rw [hH₀_eq, hw₀_eq, hS_ABC, hS_AB]
  have ht₀ : t₀ = (tA₀ * (1 + x) + p * tB) * (1 + y) + p * (1 + x) * tC := by
    dsimp [t₀]
    rw [hH₀_eq, hw₀_eq, ht_ABC, ht_AB, hS_AB]
  set dp := p - 1
  set dx := x - ρ
  set dy := y - ρ
  have hp_eq : p = 1 + dp := by omega
  have hx_eq : x = ρ + dx := by omega
  have hy_eq : y = ρ + dy := by omega
  have h_bound1 : (ρ + 1) ^ 2 ≤ S₀ := by
    have h_id1 : (ρ + 1) ^ 2 + (ρ + 1) * (dx + dy) + dx * dy +
        dp * (1 + ρ + dx) * (1 + ρ + dy) = S₀ := by
      rw [hS₀, hp_eq, hx_eq, hy_eq]
      ring
    omega
  have h_2t₀ : 2 * t₀ ≤ S₀ * (p + 1 + x + y) := by
    have h_t1 : (2 * tA₀) * ((1 + x) * (1 + y)) ≤ (p * (p + 1)) * ((1 + x) * (1 + y)) :=
      Nat.mul_le_mul_right ((1 + x) * (1 + y)) htA₀
    have h_t2 : (2 * tB) * (p * (1 + y)) ≤ (x * (x + 1)) * (p * (1 + y)) :=
      Nat.mul_le_mul_right (p * (1 + y)) htB
    have h_t3 : (2 * tC) * (p * (1 + x)) ≤ (y * (y + 1)) * (p * (1 + x)) :=
      Nat.mul_le_mul_right (p * (1 + x)) htC
    have h_lhs : 2 * t₀ = (2 * tA₀) * ((1 + x) * (1 + y)) +
        (2 * tB) * (p * (1 + y)) + (2 * tC) * (p * (1 + x)) := by
      rw [ht₀]
      ring
    have h_rhs : (p * (p + 1)) * ((1 + x) * (1 + y)) +
        (x * (x + 1)) * (p * (1 + y)) + (y * (y + 1)) * (p * (1 + x)) =
        S₀ * (p + 1 + x + y) := by
      rw [hS₀]
      ring
    omega
  have h_lin : (ρ + 1) * (p + 1 + x + y) ≤ 2 * S₀ := by
    have h_id2 : (ρ + 1) * (p + 1 + x + y) +
        p * (x + 1) * dy + p * (y + 1) * dx + (ρ + 1) * dp * (x + y + 1) =
        2 * S₀ := by
      rw [hS₀, hp_eq, hx_eq, hy_eq]
      ring
    omega
  have h_rho_t₀ : (ρ + 1) * t₀ ≤ S₀ ^ 2 := by
    have h_step1 : (ρ + 1) * (2 * t₀) ≤ (ρ + 1) * (S₀ * (p + 1 + x + y)) :=
      Nat.mul_le_mul_left (ρ + 1) h_2t₀
    have h_step2 : S₀ * ((ρ + 1) * (p + 1 + x + y)) ≤ S₀ * (2 * S₀) :=
      Nat.mul_le_mul_left S₀ h_lin
    have h_eq1 : 2 * ((ρ + 1) * t₀) = (ρ + 1) * (2 * t₀) := by ring
    have h_eq2 : (ρ + 1) * (S₀ * (p + 1 + x + y)) = S₀ * ((ρ + 1) * (p + 1 + x + y)) := by ring
    have h_eq3 : S₀ * (2 * S₀) = 2 * (S₀ ^ 2) := by ring
    omega
  have h_bound2 : (ρ + 1) ^ 2 * t₀ ≤ (ρ + 1 + 0) * S₀ ^ 2 := by
    have h_mul : (ρ + 1) * ((ρ + 1) * t₀) ≤ (ρ + 1) * (S₀ ^ 2) :=
      Nat.mul_le_mul_left (ρ + 1) h_rho_t₀
    have h_lhs : (ρ + 1) ^ 2 * t₀ = (ρ + 1) * ((ρ + 1) * t₀) := by ring
    have h_rhs : (ρ + 1 + 0) * S₀ ^ 2 = (ρ + 1) * (S₀ ^ 2) := by ring
    omega
  exact ⟨hH₀_sub, hw₀_mem, h_bound1, h_bound2⟩

theorem arm_prefix_host_step : ∀ (n : ℕ) (hn : 1 ≤ n) (T : SimpleGraph (Fin n)),
    T.IsTree → ∀ (ℓ : ℕ) (A₀ B C P : Finset (Fin n)) (w r_B r_C : Fin n)
      (v : Fin (ℓ + 1) → Fin n) (L : Fin (ℓ + 1) → Finset (Fin n)),
      IsMinCountTerminalArm T ℓ A₀ B C P w r_B r_C v L →
      ∀ (j : ℕ) (hj : j < ℓ) (hj1 : j ≤ ℓ + 1) (hj2 : j + 1 ≤ ℓ + 1),
        let H_j := armPrefixHost ℓ A₀ B C v L j
        let w_j := armPrefixRoot ℓ w v j hj1
        let H_next := armPrefixHost ℓ A₀ B C v L (j + 1)
        let w_next := armPrefixRoot ℓ w v (j + 1) hj2
        (IsSubtree T H_j ∧ w_j ∈ H_j ∧
          (rootedCount T P (v 0) + 1) ^ 2 ≤ rootedCount T H_j w_j ∧
          (rootedCount T P (v 0) + 1) ^ 2 * rootedOrderSum T H_j w_j ≤
            (rootedCount T P (v 0) + 1 + j) * (rootedCount T H_j w_j) ^ 2) →
        IsSubtree T H_next ∧ w_next ∈ H_next ∧
          (rootedCount T P (v 0) + 1) ^ 2 ≤ rootedCount T H_next w_next ∧
          (rootedCount T P (v 0) + 1) ^ 2 * rootedOrderSum T H_next w_next ≤
            (rootedCount T P (v 0) + 1 + (j + 1)) * (rootedCount T H_next w_next) ^ 2 :=
by
  intro n _hn T _hT ℓ A₀ B C P w r_B r_C v L h_arm j hj hj1 hj2 H_j w_j H_next w_next h_ih
  have isSubtree_insert_leaf_iff : ∀ (G : SimpleGraph (Fin n)) (U S₀ : Finset (Fin n)) (z r : Fin n),
      z ∉ U → r ∈ U → (∀ y ∈ insert z U, G.Adj z y ↔ y = r) → S₀ ⊆ U →
      (IsSubtree G (insert z S₀) ↔ S₀ = ∅ ∨ (IsSubtree G S₀ ∧ r ∈ S₀)) := by
    intro G U S₀ z r hz hr hadj hS₀
    have hzr : z ≠ r := fun h => hz (h ▸ hr)
    have hzS₀ : z ∉ S₀ := fun h => hz (hS₀ h)
    rcases S₀.eq_empty_or_nonempty with rfl | hS₀_ne
    · simp only [Finset.insert_empty, true_or, iff_true]
      refine ⟨Finset.singleton_nonempty z, ?_⟩
      rw [SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨⟨z, by simp⟩, fun ⟨w, hw⟩ => ?_⟩
      have hwz : w = z := by simpa using hw
      subst hwz
      exact SimpleGraph.Reachable.rfl
    · simp only [hS₀_ne.ne_empty, false_or]
      let S : Finset (Fin n) := insert z S₀
      change IsSubtree G S ↔ IsSubtree G S₀ ∧ r ∈ S₀
      constructor
      · intro hS
        have hr_mem : r ∈ S₀ := by
          obtain ⟨a, ha⟩ := hS₀_ne
          have h_walk : ∀ (u v : ↑(S : Set (Fin n))) (p : (G.induce (S : Set (Fin n))).Walk u v),
              u.1 = z → v.1 ∈ S₀ → r ∈ S₀ := by
            intro u v p huz hvS₀
            cases p with
            | nil =>
              exact False.elim (hzS₀ (huz ▸ hvS₀))
            | @cons _ b _ hadj_step _ =>
              have hb_mem : b.1 ∈ insert z S₀ := b.2
              have hb_U : b.1 ∈ insert z U := Finset.insert_subset_insert z hS₀ hb_mem
              have hbr : b.1 = r := (hadj b.1 hb_U).mp (huz ▸ hadj_step)
              rcases Finset.mem_insert.mp hb_mem with hbz | hbS₀
              · exact False.elim (hzr (hbz.symm.trans hbr))
              · exact hbr ▸ hbS₀
          obtain ⟨p⟩ := hS.2.preconnected
            ⟨z, Finset.mem_coe.mpr (Finset.mem_insert_self z S₀)⟩
            ⟨a, Finset.mem_coe.mpr (Finset.mem_insert_of_mem ha)⟩
          exact h_walk _ _ p rfl ha
        refine ⟨⟨hS₀_ne, ?_⟩, hr_mem⟩
        rw [SimpleGraph.connected_iff_exists_forall_reachable]
        let φ : ↑(S : Set (Fin n)) → ↑(S₀ : Set (Fin n)) := fun x =>
          ⟨if x.1 = z then r else x.1, by
            by_cases hx : x.1 = z
            · simp [hx, hr_mem]
            · simp only [hx, ↓reduceIte, Finset.mem_coe]
              rcases Finset.mem_insert.mp x.2 with hxz | h
              · exact False.elim (hx hxz)
              · exact h⟩
        have hφ_mem : ∀ (a : Fin n) (ha : a ∈ S₀),
            φ ⟨a, Finset.mem_coe.mpr (Finset.mem_insert_of_mem ha)⟩ = ⟨a, ha⟩ := by
          intro a ha
          have haz : a ≠ z := fun h => hzS₀ (h ▸ ha)
          ext
          simp [φ, haz]
        have hφ_adj : ∀ x y : ↑(S : Set (Fin n)),
            (G.induce (S : Set (Fin n))).Adj x y →
            (G.induce (S₀ : Set (Fin n))).Reachable (φ x) (φ y) := by
          intro x y hxy
          change G.Adj x.1 y.1 at hxy
          by_cases hx : x.1 = z
          · have hy_U : y.1 ∈ insert z U := Finset.insert_subset_insert z hS₀ y.2
            have hyr : y.1 = r := (hadj y.1 hy_U).mp (hx ▸ hxy)
            have hφ_eq : φ x = φ y := by
              ext
              simp [φ, hx, hyr]
            rw [hφ_eq]
          · by_cases hy : y.1 = z
            · have hx_U : x.1 ∈ insert z U := Finset.insert_subset_insert z hS₀ x.2
              have hxr : x.1 = r := (hadj x.1 hx_U).mp (hy ▸ G.symm hxy)
              have hφ_eq : φ x = φ y := by
                ext
                simp [φ, hy, hxr]
              rw [hφ_eq]
            · apply SimpleGraph.Adj.reachable
              change G.Adj (φ x).1 (φ y).1
              simp [φ, hx, hy, hxy]
        have hφ_walk : ∀ (x y : ↑(S : Set (Fin n)))
            (p : (G.induce (S : Set (Fin n))).Walk x y),
            (G.induce (S₀ : Set (Fin n))).Reachable (φ x) (φ y) := by
          intro x y p
          induction p with
          | nil => exact SimpleGraph.Reachable.rfl
          | cons h_step _ ih => exact (hφ_adj _ _ h_step).trans ih
        refine ⟨⟨r, hr_mem⟩, fun ⟨b, hb⟩ => ?_⟩
        obtain ⟨p⟩ := hS.2.preconnected
          ⟨r, Finset.mem_coe.mpr (Finset.mem_insert_of_mem hr_mem)⟩
          ⟨b, Finset.mem_coe.mpr (Finset.mem_insert_of_mem hb)⟩
        have h_reach := hφ_walk _ _ p
        rwa [hφ_mem r hr_mem, hφ_mem b hb] at h_reach
      · rintro ⟨hS₀_sub, hr_mem⟩
        refine ⟨Finset.insert_nonempty z S₀, ?_⟩
        rw [SimpleGraph.connected_iff_exists_forall_reachable]
        let ι : ↑(S₀ : Set (Fin n)) → ↑(S : Set (Fin n)) :=
          fun x => ⟨x.1, Finset.mem_coe.mpr (Finset.mem_insert_of_mem x.2)⟩
        have hι_walk : ∀ (x y : ↑(S₀ : Set (Fin n))) (p : (G.induce (S₀ : Set (Fin n))).Walk x y),
            (G.induce (S : Set (Fin n))).Reachable (ι x) (ι y) := by
          intro x y p
          induction p with
          | nil => exact SimpleGraph.Reachable.rfl
          | cons h_step _ ih =>
            have h_step' : (G.induce (S : Set (Fin n))).Adj (ι _) (ι _) := h_step
            exact h_step'.reachable.trans ih
        refine ⟨ι ⟨r, hr_mem⟩, fun ⟨b, hb⟩ => ?_⟩
        rcases Finset.mem_insert.mp hb with hbz | hbS₀
        · subst b
          apply SimpleGraph.Adj.reachable
          change G.Adj r z
          exact G.symm ((hadj r (Finset.mem_insert_of_mem hr)).mpr rfl)
        · obtain ⟨p⟩ := hS₀_sub.2.preconnected ⟨r, hr_mem⟩ ⟨b, hbS₀⟩
          exact hι_walk _ _ p
  have pendant_ext_moments : ∀ (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) (z r : Fin n),
      z ∉ U → r ∈ U → (∀ y ∈ insert z U, G.Adj z y ↔ y = r) →
      rootedCount G (insert z U) z = rootedCount G U r + 1 ∧
      rootedOrderSum G (insert z U) z = rootedOrderSum G U r + rootedCount G U r + 1 ∧
      rootedCount G (insert z U) r = 2 * rootedCount G U r ∧
      rootedOrderSum G (insert z U) r = 2 * rootedOrderSum G U r + rootedCount G U r ∧
      rootedCount G U r ≤ rootedOrderSum G U r := by
    intro G U z r hz hr hadj
    have h_ext : ∀ S₀ ⊆ U, IsSubtree G (insert z S₀) ↔ S₀ = ∅ ∨ (IsSubtree G S₀ ∧ r ∈ S₀) :=
      fun S₀ hS₀ => isSubtree_insert_leaf_iff G U S₀ z r hz hr hadj hS₀
    have hzr : z ≠ r := fun h => hz (h ▸ hr)
    have h_mem_rooted : ∀ W r' S, S ∈ rootedSubtreesIn G W r' ↔ IsSubtree G S ∧ S ⊆ W ∧ r' ∈ S := by
      intro W r' S
      simp [rootedSubtreesIn, subtrees]
    have h_rooted_z : rootedSubtreesIn G (insert z U) z =
        insert ({z} : Finset (Fin n)) ((rootedSubtreesIn G U r).image (insert z)) := by
      ext S
      simp only [Finset.mem_insert, Finset.mem_image, h_mem_rooted]
      constructor
      · rintro ⟨hS_sub, hS_U, hzS⟩
        let S₀ := S.erase z
        have hS₀_U : S₀ ⊆ U := by
          intro v hv
          rcases Finset.mem_insert.mp (hS_U (Finset.mem_of_mem_erase hv)) with rfl | hvU
          · exact False.elim ((Finset.mem_erase.mp hv).1 rfl)
          · exact hvU
        have h_ins : insert z S₀ = S := Finset.insert_erase hzS
        have hS_iff := (h_ext S₀ hS₀_U).mp (h_ins.symm ▸ hS_sub)
        rcases hS_iff with h_emp | ⟨hS₀_tree, hrS₀⟩
        · left
          rw [← h_ins, h_emp, Finset.insert_empty]
        · right
          exact ⟨S₀, ⟨hS₀_tree, hS₀_U, hrS₀⟩, h_ins⟩
      · rintro (rfl | ⟨S₀, ⟨hS₀_tree, hS₀_U, hrS₀⟩, rfl⟩)
        · have h_emp : IsSubtree G (insert z ∅) := (h_ext ∅ (Finset.empty_subset U)).mpr (Or.inl rfl)
          simpa using h_emp
        · refine ⟨(h_ext S₀ hS₀_U).mpr (Or.inr ⟨hS₀_tree, hrS₀⟩),
            Finset.insert_subset_insert z hS₀_U, Finset.mem_insert_self z S₀⟩
    have h_notMem_img : ({z} : Finset (Fin n)) ∉ (rootedSubtreesIn G U r).image (insert z) := by
      simp only [Finset.mem_image, not_exists, not_and]
      intro S₀ hS₀ h_eq
      have hrS₀ : r ∈ S₀ := ((h_mem_rooted U r S₀).mp hS₀).2.2
      have hrz : r ∈ ({z} : Finset (Fin n)) := h_eq ▸ Finset.mem_insert_of_mem hrS₀
      exact hzr (Finset.mem_singleton.mp hrz).symm
    have h_inj : Set.InjOn (insert z) (rootedSubtreesIn G U r : Set (Finset (Fin n))) := by
      intro S₁ hS₁ S₂ hS₂ h_eq
      have hz₁ : z ∉ S₁ := fun h => hz (((h_mem_rooted U r S₁).mp hS₁).2.1 h)
      have hz₂ : z ∉ S₂ := fun h => hz (((h_mem_rooted U r S₂).mp hS₂).2.1 h)
      have := congrArg (fun S : Finset (Fin n) => S.erase z) h_eq
      simpa [Finset.erase_insert hz₁, Finset.erase_insert hz₂] using this
    have h_rc_z : rootedCount G (insert z U) z = rootedCount G U r + 1 := by
      change (rootedSubtreesIn G (insert z U) z).card = (rootedSubtreesIn G U r).card + 1
      rw [h_rooted_z, Finset.card_insert_of_notMem h_notMem_img, Finset.card_image_of_injOn h_inj]
    have h_sum_img : ∑ S ∈ (rootedSubtreesIn G U r).image (insert z), S.card =
        rootedOrderSum G U r + rootedCount G U r := by
      rw [Finset.sum_image h_inj]
      have h_congr : ∑ S₀ ∈ rootedSubtreesIn G U r, (insert z S₀).card =
          ∑ S₀ ∈ rootedSubtreesIn G U r, (S₀.card + 1) := by
        refine Finset.sum_congr rfl (fun S₀ hS₀ => ?_)
        have hzS₀ : z ∉ S₀ := fun h => hz (((h_mem_rooted U r S₀).mp hS₀).2.1 h)
        exact Finset.card_insert_of_notMem hzS₀
      rw [h_congr, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
      rfl
    have h_ros_z : rootedOrderSum G (insert z U) z =
        rootedOrderSum G U r + rootedCount G U r + 1 := by
      change ∑ S ∈ rootedSubtreesIn G (insert z U) z, S.card =
        rootedOrderSum G U r + rootedCount G U r + 1
      rw [h_rooted_z, Finset.sum_insert h_notMem_img, Finset.card_singleton, h_sum_img]
      omega
    have h_rooted_r : rootedSubtreesIn G (insert z U) r =
        rootedSubtreesIn G U r ∪ (rootedSubtreesIn G U r).image (insert z) := by
      ext S
      simp only [Finset.mem_union, Finset.mem_image, h_mem_rooted]
      constructor
      · rintro ⟨hS_tree, hS_sub, hrS⟩
        by_cases hzS : z ∈ S
        · right
          let S₀ := S.erase z
          have hS₀_U : S₀ ⊆ U := by
            intro v hv
            rcases Finset.mem_insert.mp (hS_sub (Finset.mem_of_mem_erase hv)) with rfl | hvU
            · exact False.elim ((Finset.mem_erase.mp hv).1 rfl)
            · exact hvU
          have h_ins : insert z S₀ = S := Finset.insert_erase hzS
          have hrS₀ : r ∈ S₀ := Finset.mem_erase.mpr ⟨hzr.symm, hrS⟩
          have hS_iff := (h_ext S₀ hS₀_U).mp (h_ins.symm ▸ hS_tree)
          rcases hS_iff with h_emp | ⟨hS₀_tree, _⟩
          · simp [h_emp] at hrS₀
          · exact ⟨S₀, ⟨hS₀_tree, hS₀_U, hrS₀⟩, h_ins⟩
        · left
          refine ⟨hS_tree, fun v hv => ?_, hrS⟩
          rcases Finset.mem_insert.mp (hS_sub hv) with rfl | hvU
          · exact False.elim (hzS hv)
          · exact hvU
      · rintro (⟨hS_tree, hS_U, hrS⟩ | ⟨S₀, ⟨hS₀_tree, hS₀_U, hrS₀⟩, rfl⟩)
        · exact ⟨hS_tree, Finset.Subset.trans hS_U (Finset.subset_insert z U), hrS⟩
        · exact ⟨(h_ext S₀ hS₀_U).mpr (Or.inr ⟨hS₀_tree, hrS₀⟩),
            Finset.insert_subset_insert z hS₀_U, Finset.mem_insert_of_mem hrS₀⟩
    have h_rooted_r_disj : Disjoint (rootedSubtreesIn G U r)
        ((rootedSubtreesIn G U r).image (insert z)) := by
      rw [Finset.disjoint_left]
      intro S hS₁ hS₂
      have hS_U : S ⊆ U := ((h_mem_rooted U r S).mp hS₁).2.1
      rcases Finset.mem_image.mp hS₂ with ⟨S₀, _, rfl⟩
      exact hz (hS_U (Finset.mem_insert_self z S₀))
    have h_rc_r : rootedCount G (insert z U) r = 2 * rootedCount G U r := by
      change (rootedSubtreesIn G (insert z U) r).card = 2 * (rootedSubtreesIn G U r).card
      rw [h_rooted_r, Finset.card_union_of_disjoint h_rooted_r_disj, Finset.card_image_of_injOn h_inj]
      omega
    have h_ros_r : rootedOrderSum G (insert z U) r =
        2 * rootedOrderSum G U r + rootedCount G U r := by
      change ∑ S ∈ rootedSubtreesIn G (insert z U) r, S.card =
        2 * rootedOrderSum G U r + rootedCount G U r
      rw [h_rooted_r, Finset.sum_union h_rooted_r_disj, h_sum_img]
      change rootedOrderSum G U r + (rootedOrderSum G U r + rootedCount G U r) = _
      omega
    have h_rc_le_ros : rootedCount G U r ≤ rootedOrderSum G U r := by
      have h_pos : ∀ S ∈ rootedSubtreesIn G U r, 1 ≤ S.card := by
        intro S hS
        exact Finset.card_pos.mpr ⟨r, ((h_mem_rooted U r S).mp hS).2.2⟩
      have h_sum := Finset.card_nsmul_le_sum (rootedSubtreesIn G U r) (fun S => S.card) 1 h_pos
      simpa [rootedCount, rootedOrderSum] using h_sum
    exact ⟨h_rc_z, h_ros_z, h_rc_r, h_ros_r, h_rc_le_ros⟩
  rcases h_arm with ⟨_, hv_inj, _, _, _, _, _, _, _, h_disj_P, _, hP_eq,
    h_disj_vL, hL_disj, _, _, h_bridge_P, hv_adj, hL_pkt, _, _⟩
  let i_j : Fin (ℓ + 1) := ⟨j, by omega⟩
  let u : Fin n := v i_j
  have hw_next : w_next = u := rfl
  have h_filter_succ : Finset.univ.filter (fun i : Fin (ℓ + 1) => i.val < j + 1) =
      insert i_j (Finset.univ.filter (fun i : Fin (ℓ + 1) => i.val < j)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hi
      by_cases hij : i.val = j
      · left; exact Fin.ext hij
      · right; omega
    · rintro (rfl | hi)
      · change j < j + 1; omega
      · omega
  have hH_next : H_next = (insert u H_j) ∪ L i_j := by
    dsimp [H_next, H_j, armPrefixHost, u]
    rw [h_filter_succ, Finset.biUnion_insert]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert]
    tauto
  have hv_mem_image : ∀ i : Fin (ℓ + 1), v i ∈ Finset.univ.image v :=
    fun i => Finset.mem_image_of_mem v (Finset.mem_univ i)
  have hL_sub_biUnion : ∀ i : Fin (ℓ + 1), L i ⊆ Finset.univ.biUnion L := by
    intro i x hx
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩
  have hv_mem_P : ∀ i : Fin (ℓ + 1), v i ∈ P := by
    intro i
    rw [hP_eq]
    exact Finset.mem_union_left _ (hv_mem_image i)
  have hL_sub_P : ∀ i : Fin (ℓ + 1), L i ⊆ P := by
    intro i x hx
    rw [hP_eq]
    exact Finset.mem_union_right _ (hL_sub_biUnion i hx)
  have hu_notMem : u ∉ H_j := by
    intro hu_mem
    dsimp [H_j, armPrefixHost] at hu_mem
    rcases Finset.mem_union.mp hu_mem with hu_ABC | hu_bi
    · exact Finset.disjoint_left.mp h_disj_P hu_ABC (hv_mem_P i_j)
    · rcases Finset.mem_biUnion.mp hu_bi with ⟨i, hi_flt, hu_ins⟩
      have hi_lt : i.val < j := (Finset.mem_filter.mp hi_flt).2
      rcases Finset.mem_insert.mp hu_ins with hui | huL
      · have hij : i_j = i := hv_inj hui
        have : j = i.val := congrArg Fin.val hij
        omega
      · exact Finset.disjoint_left.mp h_disj_vL (hv_mem_image i_j) (hL_sub_biUnion i huL)
  have h_disj_L : Disjoint (insert u H_j) (L i_j) := by
    rw [Finset.disjoint_right]
    intro x hxL hx_ins
    rcases Finset.mem_insert.mp hx_ins with rfl | hx_Hj
    · exact Finset.disjoint_left.mp h_disj_vL (hv_mem_image i_j) (hL_sub_biUnion i_j hxL)
    · dsimp [H_j, armPrefixHost] at hx_Hj
      rcases Finset.mem_union.mp hx_Hj with hx_ABC | hx_bi
      · exact Finset.disjoint_left.mp h_disj_P hx_ABC (hL_sub_P i_j hxL)
      · rcases Finset.mem_biUnion.mp hx_bi with ⟨i, hi_flt, hx_i⟩
        have hi_lt : i.val < j := (Finset.mem_filter.mp hi_flt).2
        rcases Finset.mem_insert.mp hx_i with rfl | hxLi
        · exact Finset.disjoint_left.mp h_disj_vL (hv_mem_image i) (hL_sub_biUnion i_j hxL)
        · have hij_ne : i ≠ i_j := by
            intro h_eq
            have : i.val = j := congrArg Fin.val h_eq
            omega
          exact Finset.disjoint_left.mp (hL_disj i i_j hij_ne) hxLi hxL
  have hadj_u : ∀ y ∈ insert u H_j, T.Adj u y ↔ y = w_j := by
    intro y hy_ins
    constructor
    · intro hadj
      have hy_ne_u : y ≠ u := fun h => T.loopless u (h ▸ hadj)
      have hy_Hj : y ∈ H_j := by
        rcases Finset.mem_insert.mp hy_ins with rfl | h
        · exact False.elim (hy_ne_u rfl)
        · exact h
      dsimp [H_j, armPrefixHost] at hy_Hj
      rcases Finset.mem_union.mp hy_Hj with hy_ABC | hy_bi
      · have h_br := h_bridge_P.2.2.2.2 y hy_ABC u (hv_mem_P i_j) (T.symm hadj)
        have hij0 : i_j = 0 := hv_inj h_br.2
        have hj0 : j = 0 := congrArg Fin.val hij0
        simp only [w_j, armPrefixRoot, hj0, ↓reduceDIte, ↓reduceIte]
        exact h_br.1
      · rcases Finset.mem_biUnion.mp hy_bi with ⟨i, hi_flt, hy_i⟩
        have hi_lt : i.val < j := (Finset.mem_filter.mp hi_flt).2
        rcases Finset.mem_insert.mp hy_i with rfl | hyLi
        · have h_step := (hv_adj i_j i).mp hadj
          have hij_step : i.val + 1 = j := by
            rcases h_step with h1 | h2
            · change j + 1 = i.val at h1; omega
            · exact h2
          have hj_ne0 : j ≠ 0 := by omega
          simp only [w_j, armPrefixRoot, hj_ne0, ↓reduceDIte, ↓reduceIte]
          congr 1
          ext
          dsimp
          omega
        · have hu_eq : u = v i := (hL_pkt i y hyLi u).mp (T.symm hadj)
          have hij : i_j = i := hv_inj hu_eq
          have : j = i.val := congrArg Fin.val hij
          omega
    · rintro rfl
      dsimp [w_j, armPrefixRoot]
      split_ifs with hj0
      · have hij0 : i_j = 0 := Fin.ext hj0
        change T.Adj (v i_j) w
        rw [hij0]
        exact T.symm h_bridge_P.2.2.2.1
      · exact (hv_adj i_j ⟨j - 1, by omega⟩).mpr (Or.inr (by dsimp [i_j]; omega))
  rcases h_ih with ⟨hHj_sub, hwj_mem, hQ_le, ht_le⟩
  set Q := (rootedCount T P (v 0) + 1) ^ 2
  set K := rootedCount T P (v 0) + 1 + j
  let W₀ : Finset (Fin n) := insert u H_j
  have hW₀_sub : IsSubtree T W₀ :=
    (isSubtree_insert_leaf_iff T H_j H_j u w_j hu_notMem hwj_mem hadj_u Finset.Subset.rfl).mpr
      (Or.inr ⟨hHj_sub, hwj_mem⟩)
  have hu_W₀ : u ∈ W₀ := Finset.mem_insert_self u H_j
  obtain ⟨h_rc_W₀, h_ros_W₀, _, _, _⟩ :=
    pendant_ext_moments T H_j u w_j hu_notMem hwj_mem hadj_u
  have hQ_W₀ : Q ≤ rootedCount T W₀ u := by
    change Q ≤ rootedCount T (insert u H_j) u
    rw [h_rc_W₀]
    omega
  have ht_W₀ : Q * rootedOrderSum T W₀ u ≤ (K + 1) * (rootedCount T W₀ u) ^ 2 := by
    change Q * rootedOrderSum T (insert u H_j) u ≤ (K + 1) * (rootedCount T (insert u H_j) u) ^ 2
    rw [h_rc_W₀, h_ros_W₀]
    set S_j := rootedCount T H_j w_j
    set t_j := rootedOrderSum T H_j w_j
    have hQS : Q * (S_j + 1) ≤ (S_j + 1) ^ 2 := by
      have h1 : Q ≤ S_j + 1 := by omega
      nlinarith
    nlinarith
  have h_pkt_ind : ∀ (F : Finset (Fin n)), F ⊆ L i_j →
      let W := W₀ ∪ F
      IsSubtree T W ∧ u ∈ W ∧
        Q ≤ rootedCount T W u ∧
        Q * rootedOrderSum T W u ≤ (K + 1) * (rootedCount T W u) ^ 2 := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.union_empty]
      exact ⟨hW₀_sub, hu_W₀, hQ_W₀, ht_W₀⟩
    | @insert x F₀ hx_notMem_F₀ ih =>
      intro hF_sub
      have hx_L : x ∈ L i_j := hF_sub (Finset.mem_insert_self x F₀)
      have hF₀_sub : F₀ ⊆ L i_j :=
        Finset.Subset.trans (Finset.subset_insert x F₀) hF_sub
      let W := W₀ ∪ F₀
      have h_ih_F₀ : IsSubtree T W ∧ u ∈ W ∧
          Q ≤ rootedCount T W u ∧
          Q * rootedOrderSum T W u ≤ (K + 1) * (rootedCount T W u) ^ 2 := ih hF₀_sub
      obtain ⟨hW_sub, hu_W, hQ_W, ht_W⟩ := h_ih_F₀
      have hW_ins : W₀ ∪ insert x F₀ = insert x W := by
        simp [W, Finset.union_insert]
      change IsSubtree T (W₀ ∪ insert x F₀) ∧ u ∈ W₀ ∪ insert x F₀ ∧
        Q ≤ rootedCount T (W₀ ∪ insert x F₀) u ∧
        Q * rootedOrderSum T (W₀ ∪ insert x F₀) u ≤ (K + 1) * (rootedCount T (W₀ ∪ insert x F₀) u) ^ 2
      rw [hW_ins]
      have hx_notMem_W₀ : x ∉ W₀ :=
        Finset.disjoint_right.mp h_disj_L hx_L
      have hx_notMem_W : x ∉ W := by
        simp [W, hx_notMem_W₀, hx_notMem_F₀]
      have hadj_x : ∀ y ∈ insert x W, T.Adj x y ↔ y = u :=
        fun y _ => hL_pkt i_j x hx_L y
      have h_ins_sub : IsSubtree T (insert x W) :=
        (isSubtree_insert_leaf_iff T W W x u hx_notMem_W hu_W hadj_x Finset.Subset.rfl).mpr
          (Or.inr ⟨hW_sub, hu_W⟩)
      have hu_ins : u ∈ insert x W := Finset.mem_insert_of_mem hu_W
      obtain ⟨_, _, h_rc_x, h_ros_x, h_rc_le_ros⟩ :=
        pendant_ext_moments T W x u hx_notMem_W hu_W hadj_x
      refine ⟨h_ins_sub, hu_ins, ?_, ?_⟩
      · rw [h_rc_x]
        omega
      · rw [h_rc_x, h_ros_x]
        nlinarith
  have h_final : IsSubtree T ((insert u H_j) ∪ L i_j) ∧ u ∈ (insert u H_j) ∪ L i_j ∧
      Q ≤ rootedCount T ((insert u H_j) ∪ L i_j) u ∧
      Q * rootedOrderSum T ((insert u H_j) ∪ L i_j) u ≤
        (K + 1) * (rootedCount T ((insert u H_j) ∪ L i_j) u) ^ 2 :=
    h_pkt_ind (L i_j) Finset.Subset.rfl
  rw [← hH_next, ← hw_next] at h_final
  obtain ⟨hH_next_sub, hu_H_next, hQ_next, ht_next⟩ := h_final
  have hK_eq : K + 1 = rootedCount T P (v 0) + 1 + (j + 1) := by
    dsimp [K]
    omega
  rw [hK_eq] at ht_next
  exact ⟨hH_next_sub, hu_H_next, hQ_next, ht_next⟩

theorem arm_rooted_count_lower_bound : ∀ (n : ℕ) (hn : 1 ≤ n) (T : SimpleGraph (Fin n)),
    T.IsTree → ∀ (ℓ : ℕ) (A₀ B C P : Finset (Fin n)) (w r_B r_C : Fin n)
      (v : Fin (ℓ + 1) → Fin n) (L : Fin (ℓ + 1) → Finset (Fin n)),
      IsMinCountTerminalArm T ℓ A₀ B C P w r_B r_C v L →
      ∀ (i₀ : Fin (ℓ + 1)), i₀.val < ℓ →
        i₀.val + 2 ^ (L i₀).card * ((ℓ - i₀.val) + 2 ^ (L (Fin.last ℓ)).card) ≤
          rootedCount T P (v 0) :=
by
  intro n hn T hT ℓ A₀ B C P w r_B r_C v L h_arm i₀ hi₀_lt
  rcases h_arm with ⟨_, h_inj, _, _, _, _, _, _, _,
    _, _, hP_eq, h_disj_vL, h_disj_L, _, _, _,
    h_spine_adj, h_leaf_pkt, _, _⟩
  set L_a := L i₀
  set L_k := L (Fin.last ℓ)
  have hi₀_ne_last : i₀ ≠ Fin.last ℓ := by
    intro h_eq
    have h_val : i₀.val = (Fin.last ℓ).val := congrArg Fin.val h_eq
    rw [Fin.val_last] at h_val
    omega
  have h_disj_La_Lk : Disjoint L_a L_k := h_disj_L i₀ (Fin.last ℓ) hi₀_ne_last
  have h_sub_biUnion : ∀ i : Fin (ℓ + 1), L i ⊆ Finset.univ.biUnion L := by
    intro i x hx
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩
  have h_disj_v_La : Disjoint (Finset.univ.image v) L_a := by
    rw [Finset.disjoint_left]
    intro x hx_v hx_La
    exact Finset.disjoint_left.mp h_disj_vL hx_v (h_sub_biUnion i₀ hx_La)
  have h_disj_v_Lk : Disjoint (Finset.univ.image v) L_k := by
    rw [Finset.disjoint_left]
    intro x hx_v hx_Lk
    exact Finset.disjoint_left.mp h_disj_vL hx_v (h_sub_biUnion (Fin.last ℓ) hx_Lk)
  let Seg : ℕ → Finset (Fin n) :=
    fun m => (Finset.univ.filter (fun j : Fin (ℓ + 1) => j.val ≤ m)).image v
  let cand : ℕ → Finset (Fin n) → Finset (Fin n) → Finset (Fin n) :=
    fun m J I => Seg m ∪ J ∪ I
  have hSeg_sub_v : ∀ m : ℕ, Seg m ⊆ Finset.univ.image v := by
    intro m x hx
    simp only [Seg, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with ⟨j, _, rfl⟩
    exact ⟨j, rfl⟩
  have h_spine_reach : ∀ (S : Finset (Fin n)) (m : ℕ) (hm : m ≤ ℓ)
      (hS : ∀ j : Fin (ℓ + 1), j.val ≤ m → v j ∈ S)
      (hv0 : v 0 ∈ S) (d : ℕ) (hd : d ≤ m),
      (T.induce (S : Set (Fin n))).Reachable ⟨v 0, hv0⟩
        ⟨v ⟨d, by omega⟩, hS ⟨d, by omega⟩ hd⟩ := by
    intro S m hm hS hv0 d
    induction d with
    | zero =>
      intro hd
      have h0 : (⟨0, by omega⟩ : Fin (ℓ + 1)) = 0 := rfl
      have hsub : (⟨v ⟨0, by omega⟩, hS ⟨0, by omega⟩ hd⟩ : (S : Set (Fin n))) = ⟨v 0, hv0⟩ := by
        ext
        simp [h0]
      rw [hsub]
    | succ d ih =>
      intro hd
      have hd_le : d ≤ m := by omega
      have h_prev := ih hd_le
      have h_adj : (T.induce (S : Set (Fin n))).Adj
          ⟨v ⟨d, by omega⟩, hS ⟨d, by omega⟩ hd_le⟩
          ⟨v ⟨d + 1, by omega⟩, hS ⟨d + 1, by omega⟩ hd⟩ := by
        change T.Adj (v ⟨d, by omega⟩) (v ⟨d + 1, by omega⟩)
        exact (h_spine_adj ⟨d, by omega⟩ ⟨d + 1, by omega⟩).mpr (Or.inl rfl)
      exact h_prev.trans h_adj.reachable
  have h_spine_reach_fin : ∀ (S : Finset (Fin n)) (m : ℕ) (hm : m ≤ ℓ)
      (hS : ∀ j : Fin (ℓ + 1), j.val ≤ m → v j ∈ S)
      (hv0 : v 0 ∈ S) (j : Fin (ℓ + 1)) (hj : j.val ≤ m) (hvj : v j ∈ S),
      (T.induce (S : Set (Fin n))).Reachable ⟨v 0, hv0⟩ ⟨v j, hvj⟩ := by
    intro S m hm hS hv0 j hj hvj
    have h_r := h_spine_reach S m hm hS hv0 j.val hj
    have h_eq : (⟨v ⟨j.val, by omega⟩, hS ⟨j.val, by omega⟩ hj⟩ : (S : Set (Fin n))) = ⟨v j, hvj⟩ := by
      ext
      rfl
    rwa [h_eq] at h_r
  have h_mem_v_cand : ∀ (m : ℕ) (J I : Finset (Fin n)),
      J ⊆ L_a → I ⊆ L_k → ∀ (j : Fin (ℓ + 1)), v j ∈ cand m J I ↔ j.val ≤ m := by
    intro m J I hJ hI j
    have hvj_im : v j ∈ Finset.univ.image v :=
      Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
    have hvj_not_J : v j ∉ J := fun h =>
      Finset.disjoint_left.mp h_disj_v_La hvj_im (hJ h)
    have hvj_not_I : v j ∉ I := fun h =>
      Finset.disjoint_left.mp h_disj_v_Lk hvj_im (hI h)
    simp only [cand, Seg, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ((⟨j', hj', h_eq⟩ | h_in_J) | h_in_I)
      · have hjj' := h_inj h_eq
        subst hjj'
        exact hj'
      · exact (hvj_not_J h_in_J).elim
      · exact (hvj_not_I h_in_I).elim
    · intro hj
      exact Or.inl (Or.inl ⟨j, hj, rfl⟩)
  have h_eq_J : ∀ (m₁ m₂ : ℕ) (J₁ J₂ I₁ I₂ : Finset (Fin n)),
      J₁ ⊆ L_a → J₂ ⊆ L_a → I₁ ⊆ L_k → I₂ ⊆ L_k →
      cand m₁ J₁ I₁ = cand m₂ J₂ I₂ → J₁ = J₂ := by
    intro m₁ m₂ J₁ J₂ I₁ I₂ hJ₁ hJ₂ hI₁ hI₂ h_eq
    ext x
    constructor
    · intro hx
      have hx_La : x ∈ L_a := hJ₁ hx
      have hx_not_v : x ∉ Finset.univ.image v :=
        Finset.disjoint_right.mp h_disj_v_La hx_La
      have hx_not_Lk : x ∉ L_k :=
        Finset.disjoint_left.mp h_disj_La_Lk hx_La
      have hx_cand : x ∈ cand m₂ J₂ I₂ := by
        rw [← h_eq]
        exact Finset.mem_union_left I₁ (Finset.mem_union_right (Seg m₁) hx)
      rcases Finset.mem_union.mp hx_cand with hx_seg_J₂ | hx_I₂
      · rcases Finset.mem_union.mp hx_seg_J₂ with hx_seg | hx_J₂
        · exact (hx_not_v (hSeg_sub_v m₂ hx_seg)).elim
        · exact hx_J₂
      · exact (hx_not_Lk (hI₂ hx_I₂)).elim
    · intro hx
      have hx_La : x ∈ L_a := hJ₂ hx
      have hx_not_v : x ∉ Finset.univ.image v :=
        Finset.disjoint_right.mp h_disj_v_La hx_La
      have hx_not_Lk : x ∉ L_k :=
        Finset.disjoint_left.mp h_disj_La_Lk hx_La
      have hx_cand : x ∈ cand m₁ J₁ I₁ := by
        rw [h_eq]
        exact Finset.mem_union_left I₂ (Finset.mem_union_right (Seg m₂) hx)
      rcases Finset.mem_union.mp hx_cand with hx_seg_J₁ | hx_I₁
      · rcases Finset.mem_union.mp hx_seg_J₁ with hx_seg | hx_J₁
        · exact (hx_not_v (hSeg_sub_v m₁ hx_seg)).elim
        · exact hx_J₁
      · exact (hx_not_Lk (hI₁ hx_I₁)).elim
  have h_eq_I : ∀ (m₁ m₂ : ℕ) (J₁ J₂ I₁ I₂ : Finset (Fin n)),
      J₁ ⊆ L_a → J₂ ⊆ L_a → I₁ ⊆ L_k → I₂ ⊆ L_k →
      cand m₁ J₁ I₁ = cand m₂ J₂ I₂ → I₁ = I₂ := by
    intro m₁ m₂ J₁ J₂ I₁ I₂ hJ₁ hJ₂ hI₁ hI₂ h_eq
    ext y
    constructor
    · intro hy
      have hy_Lk : y ∈ L_k := hI₁ hy
      have hy_not_v : y ∉ Finset.univ.image v :=
        Finset.disjoint_right.mp h_disj_v_Lk hy_Lk
      have hy_not_La : y ∉ L_a :=
        Finset.disjoint_right.mp h_disj_La_Lk hy_Lk
      have hy_cand : y ∈ cand m₂ J₂ I₂ := by
        rw [← h_eq]
        exact Finset.mem_union_right (Seg m₁ ∪ J₁) hy
      rcases Finset.mem_union.mp hy_cand with hy_seg_J₂ | hy_I₂
      · rcases Finset.mem_union.mp hy_seg_J₂ with hy_seg | hy_J₂
        · exact (hy_not_v (hSeg_sub_v m₂ hy_seg)).elim
        · exact (hy_not_La (hJ₂ hy_J₂)).elim
      · exact hy_I₂
    · intro hy
      have hy_Lk : y ∈ L_k := hI₂ hy
      have hy_not_v : y ∉ Finset.univ.image v :=
        Finset.disjoint_right.mp h_disj_v_Lk hy_Lk
      have hy_not_La : y ∉ L_a :=
        Finset.disjoint_right.mp h_disj_La_Lk hy_Lk
      have hy_cand : y ∈ cand m₁ J₁ I₁ := by
        rw [h_eq]
        exact Finset.mem_union_right (Seg m₂ ∪ J₂) hy
      rcases Finset.mem_union.mp hy_cand with hy_seg_J₁ | hy_I₁
      · rcases Finset.mem_union.mp hy_seg_J₁ with hy_seg | hy_J₁
        · exact (hy_not_v (hSeg_sub_v m₁ hy_seg)).elim
        · exact (hy_not_La (hJ₁ hy_J₁)).elim
      · exact hy_I₁
  have h_cand_in_rooted : ∀ (m : ℕ), m ≤ ℓ → ∀ (J I : Finset (Fin n)),
      J ⊆ L_a → I ⊆ L_k →
      (J = ∅ ∨ i₀.val ≤ m) → (I = ∅ ∨ m = ℓ) →
      cand m J I ∈ rootedSubtreesIn T P (v 0) := by
    intro m hm J I hJ hI hJ_cond hI_cond
    have hv0 : v 0 ∈ cand m J I :=
      (h_mem_v_cand m J I hJ hI 0).mpr (Nat.zero_le m)
    have h_sub_P : cand m J I ⊆ P := by
      intro x hx
      rw [hP_eq, Finset.mem_union]
      rcases Finset.mem_union.mp hx with hx_seg_J | hx_I
      · rcases Finset.mem_union.mp hx_seg_J with hx_seg | hx_J
        · exact Or.inl (hSeg_sub_v m hx_seg)
        · exact Or.inr (h_sub_biUnion i₀ (hJ hx_J))
      · exact Or.inr (h_sub_biUnion (Fin.last ℓ) (hI hx_I))
    have h_conn : (T.induce (cand m J I : Set (Fin n))).Connected := by
      rw [SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨⟨v 0, hv0⟩, ?_⟩
      rintro ⟨u, hu⟩
      have hu' : u ∈ cand m J I := hu
      rcases Finset.mem_union.mp hu' with hu_seg_J | hu_I
      · rcases Finset.mem_union.mp hu_seg_J with hu_seg | hu_J
        · simp only [Seg, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hu_seg
          rcases hu_seg with ⟨j, hj, rfl⟩
          exact h_spine_reach_fin (cand m J I) m hm
            (fun j' hj' => (h_mem_v_cand m J I hJ hI j').mpr hj') hv0 j hj hu
        · rcases hJ_cond with rfl | hi₀_le
          · exact (Finset.notMem_empty u hu_J).elim
          · have hvi₀ : v i₀ ∈ cand m J I :=
              (h_mem_v_cand m J I hJ hI i₀).mpr hi₀_le
            have h_reach_vi₀ := h_spine_reach_fin (cand m J I) m hm
              (fun j' hj' => (h_mem_v_cand m J I hJ hI j').mpr hj') hv0 i₀ hi₀_le hvi₀
            have h_adj_T : T.Adj (v i₀) u :=
              T.symm ((h_leaf_pkt i₀ u (hJ hu_J) (v i₀)).mpr rfl)
            have h_adj_ind : (T.induce (cand m J I : Set (Fin n))).Adj ⟨v i₀, hvi₀⟩ ⟨u, hu⟩ := h_adj_T
            exact h_reach_vi₀.trans h_adj_ind.reachable
      · rcases hI_cond with rfl | hm_eq
        · exact (Finset.notMem_empty u hu_I).elim
        · have h_last_le : (Fin.last ℓ).val ≤ m := by
            rw [Fin.val_last]
            omega
          have hv_last : v (Fin.last ℓ) ∈ cand m J I :=
            (h_mem_v_cand m J I hJ hI (Fin.last ℓ)).mpr h_last_le
          have h_reach_last := h_spine_reach_fin (cand m J I) m hm
            (fun j' hj' => (h_mem_v_cand m J I hJ hI j').mpr hj') hv0 (Fin.last ℓ) h_last_le hv_last
          have h_adj_T : T.Adj (v (Fin.last ℓ)) u :=
            T.symm ((h_leaf_pkt (Fin.last ℓ) u (hI hu_I) (v (Fin.last ℓ))).mpr rfl)
          have h_adj_ind : (T.induce (cand m J I : Set (Fin n))).Adj ⟨v (Fin.last ℓ), hv_last⟩ ⟨u, hu⟩ := h_adj_T
          exact h_reach_last.trans h_adj_ind.reachable
    simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨⟨v 0, hv0⟩, h_conn⟩, h_sub_P, hv0⟩
  set R := rootedSubtreesIn T P (v 0)
  set R₁ := R.filter (fun S => v i₀ ∉ S)
  set R_pos := R.filter (fun S => v i₀ ∈ S)
  set R₂ := R_pos.filter (fun S => v (Fin.last ℓ) ∉ S)
  set R₃ := R_pos.filter (fun S => v (Fin.last ℓ) ∈ S)
  have h_bucket1 : i₀.val ≤ R₁.card := by
    let D₁ : Finset ℕ := Finset.range i₀.val
    let f₁ : ℕ → Finset (Fin n) := fun m => cand m ∅ ∅
    have hf₁_sub : D₁.image f₁ ⊆ R₁ := by
      intro S hS
      simp only [Finset.mem_image, D₁, Finset.mem_range] at hS
      rcases hS with ⟨m, hm_lt, rfl⟩
      have hm_le : m ≤ ℓ := by omega
      have h_in_R : f₁ m ∈ R :=
        h_cand_in_rooted m hm_le ∅ ∅ (Finset.empty_subset L_a) (Finset.empty_subset L_k)
          (Or.inl rfl) (Or.inl rfl)
      have h_not_vi₀ : v i₀ ∉ f₁ m := by
        rw [h_mem_v_cand m ∅ ∅ (Finset.empty_subset L_a) (Finset.empty_subset L_k) i₀]
        omega
      exact Finset.mem_filter.mpr ⟨h_in_R, h_not_vi₀⟩
    have hf₁_injOn : Set.InjOn f₁ (D₁ : Set ℕ) := by
      intro m₁ hm₁ m₂ hm₂ h_eq
      simp only [Finset.mem_coe, D₁, Finset.mem_range] at hm₁ hm₂
      have h1 : m₁ ≤ m₂ := by
        have hm₁_mem : v ⟨m₁, by omega⟩ ∈ f₁ m₁ :=
          (h_mem_v_cand m₁ ∅ ∅ (Finset.empty_subset L_a) (Finset.empty_subset L_k) ⟨m₁, by omega⟩).mpr (le_refl m₁)
        rw [h_eq, h_mem_v_cand m₂ ∅ ∅ (Finset.empty_subset L_a) (Finset.empty_subset L_k) ⟨m₁, by omega⟩] at hm₁_mem
        exact hm₁_mem
      have h2 : m₂ ≤ m₁ := by
        have hm₂_mem : v ⟨m₂, by omega⟩ ∈ f₁ m₂ :=
          (h_mem_v_cand m₂ ∅ ∅ (Finset.empty_subset L_a) (Finset.empty_subset L_k) ⟨m₂, by omega⟩).mpr (le_refl m₂)
        rw [← h_eq, h_mem_v_cand m₁ ∅ ∅ (Finset.empty_subset L_a) (Finset.empty_subset L_k) ⟨m₂, by omega⟩] at hm₂_mem
        exact hm₂_mem
      omega
    have h_le := Finset.card_le_card hf₁_sub
    rw [Finset.card_image_of_injOn hf₁_injOn, Finset.card_range] at h_le
    exact h_le
  have h_bucket2 : 2 ^ L_a.card * (ℓ - i₀.val) ≤ R₂.card := by
    let D₂ : Finset (Finset (Fin n) × ℕ) := L_a.powerset ×ˢ Finset.Ico i₀.val ℓ
    let f₂ : Finset (Fin n) × ℕ → Finset (Fin n) := fun p => cand p.2 p.1 ∅
    have hf₂_sub : D₂.image f₂ ⊆ R₂ := by
      intro S hS
      simp only [Finset.mem_image, D₂, Finset.mem_product, Finset.mem_powerset, Finset.mem_Ico] at hS
      rcases hS with ⟨⟨J, m⟩, ⟨hJ, hi₀_le, hm_lt⟩, rfl⟩
      have hm_le : m ≤ ℓ := by omega
      have h_in_R : f₂ (J, m) ∈ R :=
        h_cand_in_rooted m hm_le J ∅ hJ (Finset.empty_subset L_k) (Or.inr hi₀_le) (Or.inl rfl)
      have h_vi₀ : v i₀ ∈ f₂ (J, m) :=
        (h_mem_v_cand m J ∅ hJ (Finset.empty_subset L_k) i₀).mpr hi₀_le
      have h_not_last : v (Fin.last ℓ) ∉ f₂ (J, m) := by
        rw [h_mem_v_cand m J ∅ hJ (Finset.empty_subset L_k) (Fin.last ℓ), Fin.val_last]
        omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨h_in_R, h_vi₀⟩, h_not_last⟩
    have hf₂_injOn : Set.InjOn f₂ (D₂ : Set (Finset (Fin n) × ℕ)) := by
      rintro ⟨J₁, m₁⟩ hp₁ ⟨J₂, m₂⟩ hp₂ h_eq
      simp only [Finset.mem_coe, D₂, Finset.mem_product, Finset.mem_powerset, Finset.mem_Ico] at hp₁ hp₂
      rcases hp₁ with ⟨hJ₁, _, hm₁_lt⟩
      rcases hp₂ with ⟨hJ₂, _, hm₂_lt⟩
      have h1 : m₁ ≤ m₂ := by
        have hm₁_mem : v ⟨m₁, by omega⟩ ∈ f₂ (J₁, m₁) :=
          (h_mem_v_cand m₁ J₁ ∅ hJ₁ (Finset.empty_subset L_k) ⟨m₁, by omega⟩).mpr (le_refl m₁)
        rw [h_eq, h_mem_v_cand m₂ J₂ ∅ hJ₂ (Finset.empty_subset L_k) ⟨m₁, by omega⟩] at hm₁_mem
        exact hm₁_mem
      have h2 : m₂ ≤ m₁ := by
        have hm₂_mem : v ⟨m₂, by omega⟩ ∈ f₂ (J₂, m₂) :=
          (h_mem_v_cand m₂ J₂ ∅ hJ₂ (Finset.empty_subset L_k) ⟨m₂, by omega⟩).mpr (le_refl m₂)
        rw [← h_eq, h_mem_v_cand m₁ J₁ ∅ hJ₁ (Finset.empty_subset L_k) ⟨m₂, by omega⟩] at hm₂_mem
        exact hm₂_mem
      have hm_eq : m₁ = m₂ := by omega
      have hJ_eq : J₁ = J₂ :=
        h_eq_J m₁ m₂ J₁ J₂ ∅ ∅ hJ₁ hJ₂ (Finset.empty_subset L_k) (Finset.empty_subset L_k) h_eq
      exact Prod.ext hJ_eq hm_eq
    have h_le := Finset.card_le_card hf₂_sub
    rw [Finset.card_image_of_injOn hf₂_injOn, Finset.card_product, Finset.card_powerset, Nat.card_Ico] at h_le
    exact h_le
  have h_bucket3 : 2 ^ L_a.card * 2 ^ L_k.card ≤ R₃.card := by
    let D₃ : Finset (Finset (Fin n) × Finset (Fin n)) := L_a.powerset ×ˢ L_k.powerset
    let f₃ : Finset (Fin n) × Finset (Fin n) → Finset (Fin n) := fun q => cand ℓ q.1 q.2
    have hf₃_sub : D₃.image f₃ ⊆ R₃ := by
      intro S hS
      simp only [Finset.mem_image, D₃, Finset.mem_product, Finset.mem_powerset] at hS
      rcases hS with ⟨⟨J, I⟩, ⟨hJ, hI⟩, rfl⟩
      have hi₀_le : i₀.val ≤ ℓ := by omega
      have h_in_R : f₃ (J, I) ∈ R :=
        h_cand_in_rooted ℓ (le_refl ℓ) J I hJ hI (Or.inr hi₀_le) (Or.inr rfl)
      have h_vi₀ : v i₀ ∈ f₃ (J, I) :=
        (h_mem_v_cand ℓ J I hJ hI i₀).mpr hi₀_le
      have h_vlast : v (Fin.last ℓ) ∈ f₃ (J, I) := by
        rw [h_mem_v_cand ℓ J I hJ hI (Fin.last ℓ), Fin.val_last]
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨h_in_R, h_vi₀⟩, h_vlast⟩
    have hf₃_injOn : Set.InjOn f₃ (D₃ : Set (Finset (Fin n) × Finset (Fin n))) := by
      rintro ⟨J₁, I₁⟩ hq₁ ⟨J₂, I₂⟩ hq₂ h_eq
      simp only [Finset.mem_coe, D₃, Finset.mem_product, Finset.mem_powerset] at hq₁ hq₂
      rcases hq₁ with ⟨hJ₁, hI₁⟩
      rcases hq₂ with ⟨hJ₂, hI₂⟩
      have hJ_eq : J₁ = J₂ := h_eq_J ℓ ℓ J₁ J₂ I₁ I₂ hJ₁ hJ₂ hI₁ hI₂ h_eq
      have hI_eq : I₁ = I₂ := h_eq_I ℓ ℓ J₁ J₂ I₁ I₂ hJ₁ hJ₂ hI₁ hI₂ h_eq
      exact Prod.ext hJ_eq hI_eq
    have h_le := Finset.card_le_card hf₃_sub
    rw [Finset.card_image_of_injOn hf₃_injOn, Finset.card_product, Finset.card_powerset, Finset.card_powerset] at h_le
    exact h_le
  have h_split1 : R_pos.card + R₁.card = rootedCount T P (v 0) := by
    simpa [rootedCount, R, R_pos, R₁] using
      Finset.card_filter_add_card_filter_not (s := R)
        (fun S : Finset (Fin n) => v i₀ ∈ S)
  have h_split2 : R₃.card + R₂.card = R_pos.card := by
    simpa [R_pos, R₃, R₂] using
      Finset.card_filter_add_card_filter_not (s := R_pos)
        (fun S : Finset (Fin n) => v (Fin.last ℓ) ∈ S)
  have h_distrib : 2 ^ L_a.card * ((ℓ - i₀.val) + 2 ^ L_k.card) =
      2 ^ L_a.card * (ℓ - i₀.val) + 2 ^ L_a.card * 2 ^ L_k.card :=
    Nat.left_distrib (2 ^ L_a.card) (ℓ - i₀.val) (2 ^ L_k.card)
  omega

theorem arm_internal_cut_structure : ∀ (n : ℕ) (hn : 1 ≤ n) (T : SimpleGraph (Fin n)),
    T.IsTree → ∀ (ℓ : ℕ) (A₀ B C P : Finset (Fin n)) (w r_B r_C : Fin n)
      (v : Fin (ℓ + 1) → Fin n) (L : Fin (ℓ + 1) → Finset (Fin n)),
      IsMinCountTerminalArm T ℓ A₀ B C P w r_B r_C v L →
      ∀ (i₀ : Fin (ℓ + 1)) (hi₀ : i₀.val < ℓ) (h_root : i₀.val ≤ ℓ + 1),
        (L i₀).Nonempty →
        (∀ j : Fin (ℓ + 1), i₀.val < j.val → j.val < ℓ → L j = ∅) →
        let ℓ' := ℓ - i₀.val
        let L_a := L i₀
        let L_k := L (Fin.last ℓ)
        let H := armPrefixHost ℓ A₀ B C v L i₀.val
        let w₀ := armPrefixRoot ℓ w v i₀.val h_root
        let v' : Fin (ℓ' + 1) → Fin n := fun m => v ⟨i₀.val + m.val, by omega⟩
        1 ≤ ℓ' ∧ 1 ≤ L_a.card ∧ 2 ≤ L_k.card ∧
        Function.Injective v' ∧
        Disjoint H (Finset.univ.image v') ∧ Disjoint H L_a ∧ Disjoint H L_k ∧
        Disjoint (Finset.univ.image v') L_a ∧ Disjoint (Finset.univ.image v') L_k ∧ Disjoint L_a L_k ∧
        H ∪ (Finset.univ.image v') ∪ L_a ∪ L_k = Finset.univ ∧
        IsBridgeJoin T H ((Finset.univ.image v') ∪ L_a ∪ L_k) w₀ (v' 0) ∧
        (∀ i j : Fin (ℓ' + 1), T.Adj (v' i) (v' j) ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val)) ∧
        IsLeafPacket T L_a (v' 0) ∧
        IsLeafPacket T L_k (v' (Fin.last ℓ')) :=
by
  intro n hn T hT ℓ A₀ B C P w r_B r_C v L h_arm i₀ hi₀ h_root hi₀_ne h_empty_after
  intro ℓ' L_a L_k H w₀ v'
  rcases h_arm with ⟨hk_ge, hv_inj, hA₀_sub, hB_sub, hC_sub, hP_sub,
    h_disj_AB, h_disj_AC, h_disj_BC, h_disj_ABCP, h_univ_P, hP_eq,
    h_disj_vL, h_disj_L, h_br_AB, h_br_ABC, h_br_P, h_spine_adj,
    h_leaf_pkt, h_count_B, h_count_C⟩
  have hℓ' : 1 ≤ ℓ' := by omega
  have ha_pos : 1 ≤ L_a.card := Finset.Nonempty.card_pos hi₀_ne
  have hv'_inj : Function.Injective v' := by
    intro m₁ m₂ h_eq
    have h_eq' : (⟨i₀.val + m₁.val, by omega⟩ : Fin (ℓ + 1)) = ⟨i₀.val + m₂.val, by omega⟩ :=
      hv_inj h_eq
    have h_val : i₀.val + m₁.val = i₀.val + m₂.val := congrArg Fin.val h_eq'
    ext
    omega
  have h_v_mem_P : ∀ j : Fin (ℓ + 1), v j ∈ P := by
    intro j
    rw [hP_eq]
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem v (Finset.mem_univ j))
  have h_L_mem_P : ∀ (j : Fin (ℓ + 1)) (x : Fin n), x ∈ L j → x ∈ P := by
    intro j x hx
    rw [hP_eq]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hx⟩)
  have h_v_not_ABC : ∀ j : Fin (ℓ + 1), v j ∉ A₀ ∪ B ∪ C := by
    intro j
    exact Finset.disjoint_right.mp h_disj_ABCP (h_v_mem_P j)
  have h_L_not_ABC : ∀ (j : Fin (ℓ + 1)) (x : Fin n), x ∈ L j → x ∉ A₀ ∪ B ∪ C := by
    intro j x hx
    exact Finset.disjoint_right.mp h_disj_ABCP (h_L_mem_P j x hx)
  have h_v_not_L : ∀ i j : Fin (ℓ + 1), v i ∉ L j := by
    intro i j h_mem
    have h1 : v i ∈ Finset.univ.image v := Finset.mem_image_of_mem v (Finset.mem_univ i)
    have h2 : v i ∈ Finset.univ.biUnion L := Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, h_mem⟩
    exact Finset.disjoint_left.mp h_disj_vL h1 h2
  have h_L_unique : ∀ (i j : Fin (ℓ + 1)) (x : Fin n), x ∈ L i → x ∈ L j → i = j := by
    intro i j x hxi hxj
    by_contra h_ne
    exact Finset.disjoint_left.mp (h_disj_L i j h_ne) hxi hxj
  have h_mem_img_v' : ∀ x : Fin n,
      x ∈ Finset.univ.image v' ↔ ∃ j : Fin (ℓ + 1), i₀.val ≤ j.val ∧ v j = x := by
    intro x
    rw [Finset.mem_image]
    constructor
    · rintro ⟨m, _, rfl⟩
      exact ⟨⟨i₀.val + m.val, by omega⟩, by dsimp; omega, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      refine ⟨⟨j.val - i₀.val, by omega⟩, Finset.mem_univ _, ?_⟩
      dsimp [v']
      congr 1
      ext
      dsimp
      omega
  have h_v_mem_img_v' : ∀ j : Fin (ℓ + 1), v j ∈ Finset.univ.image v' ↔ i₀.val ≤ j.val := by
    intro j
    rw [h_mem_img_v']
    constructor
    · rintro ⟨j', hj', h_eq⟩
      have := hv_inj h_eq
      subst this
      exact hj'
    · intro hj
      exact ⟨j, hj, rfl⟩
  have h_mem_H : ∀ x : Fin n,
      x ∈ H ↔ x ∈ A₀ ∪ B ∪ C ∨ ∃ i : Fin (ℓ + 1), i.val < i₀.val ∧ (x = v i ∨ x ∈ L i) := by
    intro x
    change x ∈ A₀ ∪ B ∪ C ∪
      (Finset.univ.filter (fun i : Fin (ℓ + 1) => i.val < i₀.val)).biUnion
        (fun i => insert (v i) (L i)) ↔ _
    rw [Finset.mem_union, Finset.mem_biUnion]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  have h_v_mem_H : ∀ j : Fin (ℓ + 1), v j ∈ H ↔ j.val < i₀.val := by
    intro j
    rw [h_mem_H]
    constructor
    · rintro (h_abc | ⟨i, hi_lt, h_eq | h_in_L⟩)
      · exact False.elim (h_v_not_ABC j h_abc)
      · have := hv_inj h_eq
        subst this
        exact hi_lt
      · exact False.elim (h_v_not_L j i h_in_L)
    · intro hj_lt
      exact Or.inr ⟨j, hj_lt, Or.inl rfl⟩
  have h_L_mem_H : ∀ (j : Fin (ℓ + 1)) (x : Fin n), x ∈ L j → (x ∈ H ↔ j.val < i₀.val) := by
    intro j x hx
    rw [h_mem_H]
    constructor
    · rintro (h_abc | ⟨i, hi_lt, rfl | h_in_L⟩)
      · exact False.elim (h_L_not_ABC j x hx h_abc)
      · exact False.elim (h_v_not_L i j hx)
      · have := h_L_unique j i x hx h_in_L
        subst this
        exact hi_lt
    · intro hj_lt
      exact Or.inr ⟨j, hj_lt, Or.inr hx⟩
  have h_disj1 : Disjoint H (Finset.univ.image v') := by
    rw [Finset.disjoint_right]
    intro x hx_img hx_H
    rcases (h_mem_img_v' x).mp hx_img with ⟨j, hj_ge, rfl⟩
    have hj_lt : j.val < i₀.val := (h_v_mem_H j).mp hx_H
    omega
  have h_disj2 : Disjoint H L_a := by
    rw [Finset.disjoint_right]
    intro x hx_La hx_H
    have hi_lt : i₀.val < i₀.val := (h_L_mem_H i₀ x hx_La).mp hx_H
    omega
  have h_disj3 : Disjoint H L_k := by
    rw [Finset.disjoint_right]
    intro x hx_Lk hx_H
    have hk_lt : (Fin.last ℓ).val < i₀.val := (h_L_mem_H (Fin.last ℓ) x hx_Lk).mp hx_H
    rw [Fin.val_last] at hk_lt
    omega
  have h_disj4 : Disjoint (Finset.univ.image v') L_a := by
    rw [Finset.disjoint_left]
    intro x hx_img hx_La
    rcases (h_mem_img_v' x).mp hx_img with ⟨j, _, rfl⟩
    exact h_v_not_L j i₀ hx_La
  have h_disj5 : Disjoint (Finset.univ.image v') L_k := by
    rw [Finset.disjoint_left]
    intro x hx_img hx_Lk
    rcases (h_mem_img_v' x).mp hx_img with ⟨j, _, rfl⟩
    exact h_v_not_L j (Fin.last ℓ) hx_Lk
  have h_disj6 : Disjoint L_a L_k := by
    apply h_disj_L i₀ (Fin.last ℓ)
    intro h_eq
    have h_val : i₀.val = (Fin.last ℓ).val := congrArg Fin.val h_eq
    rw [Fin.val_last] at h_val
    omega
  have h_univ : H ∪ (Finset.univ.image v') ∪ L_a ∪ L_k = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro x
    have hx_univ : x ∈ A₀ ∪ B ∪ C ∪ P := by
      rw [h_univ_P]
      exact Finset.mem_univ x
    rw [Finset.mem_union] at hx_univ
    simp only [Finset.mem_union]
    rcases hx_univ with h_abc | hx_P
    · left; left; left
      exact (h_mem_H x).mpr (Or.inl h_abc)
    · rw [hP_eq, Finset.mem_union] at hx_P
      rcases hx_P with hx_v | hx_L
      · rw [Finset.mem_image] at hx_v
        rcases hx_v with ⟨j, _, rfl⟩
        by_cases hj : j.val < i₀.val
        · left; left; left
          exact (h_v_mem_H j).mpr hj
        · left; left; right
          exact (h_v_mem_img_v' j).mpr (by omega)
      · rw [Finset.mem_biUnion] at hx_L
        rcases hx_L with ⟨j, _, hxj⟩
        by_cases hj1 : j.val < i₀.val
        · left; left; left
          exact (h_L_mem_H j x hxj).mpr hj1
        · by_cases hj2 : j.val = i₀.val
          · left; right
            have hj_eq : j = i₀ := Fin.ext hj2
            subst hj_eq
            exact hxj
          · by_cases hj3 : j.val < ℓ
            · have h_emp := h_empty_after j (by omega) hj3
              rw [h_emp] at hxj
              exact False.elim (Finset.notMem_empty x hxj)
            · right
              have hj_eq : j = Fin.last ℓ := by
                ext
                rw [Fin.val_last]
                omega
              subst hj_eq
              exact hxj
  have hv'0 : v' 0 = v i₀ := by
    dsimp [v']
  have h_bridge : IsBridgeJoin T H ((Finset.univ.image v') ∪ L_a ∪ L_k) w₀ (v' 0) := by
    have h_disj_H_U2 : Disjoint H ((Finset.univ.image v') ∪ L_a ∪ L_k) := by
      rw [Finset.disjoint_union_right, Finset.disjoint_union_right]
      exact ⟨⟨h_disj1, h_disj2⟩, h_disj3⟩
    have hw₀_mem : w₀ ∈ H := by
      dsimp [w₀, armPrefixRoot]
      split_ifs with h_zero
      · have hw_A0 : w ∈ A₀ := h_br_AB.2.1
        apply (h_mem_H w).mpr
        left
        simp only [Finset.mem_union]
        exact Or.inl (Or.inl hw_A0)
      · apply (h_v_mem_H ⟨i₀.val - 1, by omega⟩).mpr
        dsimp
        omega
    have hv'0_mem : v' 0 ∈ (Finset.univ.image v') ∪ L_a ∪ L_k := by
      simp only [Finset.mem_union]
      left; left
      exact Finset.mem_image_of_mem v' (Finset.mem_univ 0)
    have h_adj_w0 : T.Adj w₀ (v' 0) := by
      rw [hv'0]
      dsimp [w₀, armPrefixRoot]
      split_ifs with h_zero
      · have hi₀_eq : i₀ = 0 := by
          ext
          exact h_zero
        rw [hi₀_eq]
        exact h_br_P.2.2.2.1
      · exact (h_spine_adj ⟨i₀.val - 1, by omega⟩ i₀).mpr (Or.inl (by dsimp; omega))
    refine ⟨h_disj_H_U2, hw₀_mem, hv'0_mem, h_adj_w0, ?_⟩
    intro u hu y hy h_adj
    simp only [Finset.mem_union] at hy
    rcases hy with (hy_img | hy_La) | hy_Lk
    · rcases (h_mem_img_v' y).mp hy_img with ⟨j, hj_ge, rfl⟩
      rcases (h_mem_H u).mp hu with hu_abc | ⟨i, hi_lt, rfl | hu_Li⟩
      · have h_uy := h_br_P.2.2.2.2 u hu_abc (v j) (h_v_mem_P j) h_adj
        rcases h_uy with ⟨rfl, hvj_eq⟩
        have hj_eq : j = 0 := hv_inj hvj_eq
        have hj_val : j.val = 0 := by rw [hj_eq]; rfl
        have h_zero : i₀.val = 0 := by omega
        have hi₀_eq : i₀ = 0 := Fin.ext h_zero
        have hw₀_eq : w₀ = u := by
          dsimp [w₀, armPrefixRoot]
          exact if_pos h_zero
        refine ⟨hw₀_eq.symm, ?_⟩
        rw [hvj_eq, hv'0, hi₀_eq]
      · have h_step := (h_spine_adj i j).mp h_adj
        have h_nz : i₀.val ≠ 0 := by omega
        have hi_eq : i = ⟨i₀.val - 1, by omega⟩ := by
          ext
          dsimp
          omega
        have hj_eq : j = i₀ := by
          ext
          omega
        have hw₀_eq : w₀ = v i := by
          dsimp [w₀, armPrefixRoot]
          rw [if_neg h_nz, ← hi_eq]
        refine ⟨hw₀_eq.symm, ?_⟩
        rw [hj_eq, hv'0]
      · have hy_eq : v j = v i := (h_leaf_pkt i u hu_Li (v j)).mp h_adj
        have hj_eq : j = i := hv_inj hy_eq
        have : j.val = i.val := congrArg Fin.val hj_eq
        omega
    · have hu_eq : u = v i₀ := (h_leaf_pkt i₀ y hy_La u).mp h_adj.symm
      subst hu_eq
      have : i₀.val < i₀.val := (h_v_mem_H i₀).mp hu
      omega
    · have hu_eq : u = v (Fin.last ℓ) := (h_leaf_pkt (Fin.last ℓ) y hy_Lk u).mp h_adj.symm
      subst hu_eq
      have hk_lt : (Fin.last ℓ).val < i₀.val := (h_v_mem_H (Fin.last ℓ)).mp hu
      rw [Fin.val_last] at hk_lt
      omega
  have hv'_adj : ∀ i j : Fin (ℓ' + 1),
      T.Adj (v' i) (v' j) ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
    intro i j
    dsimp [v']
    rw [h_spine_adj]
    dsimp
    omega
  have hLa_pkt : IsLeafPacket T L_a (v' 0) := by
    rw [hv'0]
    exact h_leaf_pkt i₀
  have hv'_last : v' (Fin.last ℓ') = v (Fin.last ℓ) := by
    dsimp [v']
    congr 1
    ext
    dsimp [Fin.val_last]
    omega
  have hLk_pkt : IsLeafPacket T L_k (v' (Fin.last ℓ')) := by
    rw [hv'_last]
    exact h_leaf_pkt (Fin.last ℓ)
  exact ⟨hℓ', ha_pos, hk_ge, hv'_inj, h_disj1, h_disj2, h_disj3,
    h_disj4, h_disj5, h_disj6, h_univ, h_bridge, hv'_adj, hLa_pkt, hLk_pkt⟩

theorem min_arm_internal_packet_to_suffix : ∀ (n : ℕ) (hn : 1 ≤ n) (T : SimpleGraph (Fin n)),
    T.IsTree → ∀ (ℓ : ℕ) (A₀ B C P : Finset (Fin n)) (w r_B r_C : Fin n)
      (v : Fin (ℓ + 1) → Fin n) (L : Fin (ℓ + 1) → Finset (Fin n)),
      IsMinCountTerminalArm T ℓ A₀ B C P w r_B r_C v L →
      (∃ i : Fin (ℓ + 1), i.val < ℓ ∧ (L i).Nonempty) →
      HasInternalPacketSuffix T :=
by
  intro n hn T hT ℓ A₀ B C P w r_B r_C v L h_arm h_int
  let I_int : Finset (Fin (ℓ + 1)) :=
    Finset.univ.filter (fun i : Fin (ℓ + 1) => i.val < ℓ ∧ (L i).Nonempty)
  have h_ne : I_int.Nonempty := by
    rcases h_int with ⟨i, hi_lt, hi_ne⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi_lt, hi_ne⟩⟩
  let i₀ : Fin (ℓ + 1) := I_int.max' h_ne
  have hi₀_mem : i₀ ∈ I_int := Finset.max'_mem I_int h_ne
  obtain ⟨_, hi₀_lt, hi₀_ne⟩ := Finset.mem_filter.mp hi₀_mem
  have h_empty_after : ∀ j : Fin (ℓ + 1), i₀.val < j.val → j.val < ℓ → L j = ∅ := by
    intro j hj_gt hj_lt
    by_contra hj_ne
    have hj_nonempty : (L j).Nonempty := Finset.nonempty_iff_ne_empty.mpr hj_ne
    have hj_mem : j ∈ I_int := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj_lt, hj_nonempty⟩
    have hj_le : j ≤ i₀ := Finset.le_max' I_int j hj_mem
    have hj_val_le : j.val ≤ i₀.val := hj_le
    omega
  have h_root : i₀.val ≤ ℓ + 1 := by omega
  have h_ind : ∀ (j : ℕ) (hj : j ≤ i₀.val),
      let H_j := armPrefixHost ℓ A₀ B C v L j
      let w_j := armPrefixRoot ℓ w v j (by omega)
      IsSubtree T H_j ∧ w_j ∈ H_j ∧
        (rootedCount T P (v 0) + 1) ^ 2 ≤ rootedCount T H_j w_j ∧
        (rootedCount T P (v 0) + 1) ^ 2 * rootedOrderSum T H_j w_j ≤
          (rootedCount T P (v 0) + 1 + j) * (rootedCount T H_j w_j) ^ 2 := by
    intro j
    induction j with
    | zero =>
      intro _
      exact min_arm_base_host_bounds n hn T hT ℓ A₀ B C P w r_B r_C v L h_arm
    | succ j ih =>
      intro hj_succ
      exact arm_prefix_host_step n hn T hT ℓ A₀ B C P w r_B r_C v L h_arm
        j (by omega) (by omega) (by omega) (ih (by omega))
  obtain ⟨hH_sub, _, hS_ge, ht_le⟩ := h_ind i₀.val le_rfl
  have h_count_lb := arm_rooted_count_lower_bound n hn T hT ℓ A₀ B C P w r_B r_C v L h_arm i₀ hi₀_lt
  have h_struct := arm_internal_cut_structure n hn T hT ℓ A₀ B C P w r_B r_C v L h_arm
    i₀ hi₀_lt h_root hi₀_ne h_empty_after
  dsimp only at h_struct
  rcases h_struct with ⟨hℓ', ha_pos, hk_ge, hv'_inj, h_disj1, h_disj2, h_disj3,
    h_disj4, h_disj5, h_disj6, h_univ, h_bridge, hv'_adj, hLa_pkt, hLk_pkt⟩
  set ℓ' := ℓ - i₀.val
  set L_a := L i₀
  set L_k := L (Fin.last ℓ)
  set a := L_a.card
  set k := L_k.card
  set H := armPrefixHost ℓ A₀ B C v L i₀.val
  set w₀ := armPrefixRoot ℓ w v i₀.val h_root
  let v' : Fin (ℓ' + 1) → Fin n := fun m => v ⟨i₀.val + m.val, by omega⟩
  set b := 2 ^ a * (ℓ' + 2 ^ k)
  set ρ := rootedCount T P (v 0)
  set S := rootedCount T H w₀
  set t := rootedOrderSum T H w₀
  have hd_b_le : i₀.val + b ≤ ρ := h_count_lb
  have hb_le_rho1 : b ≤ ρ + 1 := by omega
  have hb2_le_S : b ^ 2 ≤ S := by
    have hb2_le : b ^ 2 ≤ (ρ + 1) ^ 2 := Nat.pow_le_pow_left hb_le_rho1 2
    exact le_trans hb2_le hS_ge
  have h_poly : (b + 1) * (ρ + 1 + i₀.val) ≤ (ρ + 1) ^ 2 := by
    set m := ρ - (i₀.val + b)
    have hm : ρ = i₀.val + b + m := by omega
    have h_id : (b + 1) * (ρ + 1 + i₀.val) + (b + 1) * m + (i₀.val + m) ^ 2 = (ρ + 1) ^ 2 := by
      rw [hm]
      ring
    omega
  have hbt_le_S2 : b * t ≤ S ^ 2 := by
    have h_mul : (ρ + 1) ^ 2 * (b * t) ≤ (ρ + 1) ^ 2 * S ^ 2 := by
      calc (ρ + 1) ^ 2 * (b * t)
        _ ≤ (ρ + 1) ^ 2 * ((b + 1) * t) := by
            gcongr
            omega
        _ = (b + 1) * ((ρ + 1) ^ 2 * t) := by ring
        _ ≤ (b + 1) * ((ρ + 1 + i₀.val) * S ^ 2) := Nat.mul_le_mul_left (b + 1) ht_le
        _ = ((b + 1) * (ρ + 1 + i₀.val)) * S ^ 2 := by ring
        _ ≤ (ρ + 1) ^ 2 * S ^ 2 := Nat.mul_le_mul_right (S ^ 2) h_poly
    exact Nat.le_of_mul_le_mul_left h_mul (by positivity)
  exact ⟨ℓ', a, k, H, L_a, L_k, w₀, v', hℓ', ha_pos, hk_ge, hv'_inj, hH_sub, rfl, rfl,
    h_disj1, h_disj2, h_disj3, h_disj4, h_disj5, h_disj6, h_univ, h_bridge,
    hv'_adj, hLa_pkt, hLk_pkt, hb2_le_S, hbt_le_S2⟩

theorem cherry_arm_unpack_and_bounds : ∀ (n : ℕ) (T : SimpleGraph (Fin n)) (ℓ : ℕ)
    (A₀ B C P : Finset (Fin n)) (w r_B r_C : Fin n)
    (v : Fin (ℓ + 1) → Fin n) (L : Fin (ℓ + 1) → Finset (Fin n)),
    IsMinCountTerminalArm T ℓ A₀ B C P w r_B r_C v L →
    (ℓ = 0 ∧ (L (Fin.last ℓ)).card = 2) →
    ∃ (u ℓ₁ ℓ₂ : Fin n),
      let H := A₀ ∪ B ∪ C
      ℓ₁ ≠ ℓ₂ ∧ u ≠ ℓ₁ ∧ u ≠ ℓ₂ ∧
      P = ({u, ℓ₁, ℓ₂} : Finset (Fin n)) ∧
      H = Finset.univ \ ({u, ℓ₁, ℓ₂} : Finset (Fin n)) ∧
      IsSubtree T H ∧
      IsBridgeJoin T H ({u, ℓ₁, ℓ₂} : Finset (Fin n)) w u ∧
      IsLeafIn T ℓ₁ u ∧ IsLeafIn T ℓ₂ u ∧
      (∀ x : Fin n, T.Adj u x ↔ x = w ∨ x = ℓ₁ ∨ x = ℓ₂) ∧
      4 ≤ rootedCount T B r_B ∧
      4 ≤ rootedCount T C r_C ∧
      4 ≤ Fintype.card (Fin n) :=
by
  classical
  intro n T ℓ A₀ B C P w r_B r_C v L h_arm h_cherry
  rcases h_cherry with ⟨rfl, hL_card⟩
  rcases h_arm with ⟨_, _hv_inj, hA₀_sub, hB_sub, hC_sub, _hP_sub,
    _h_disj_AB, _h_disj_AC, _h_disj_BC, h_disj_ABCP, h_univ_P, hP_eq,
    _h_disj_vL, _h_disj_L, h_bridge_B, h_bridge_C, h_bridge_P, _h_spine_adj,
    h_leaf_pkt, h_dom_B, h_dom_C⟩
  let u : Fin n := v 0
  let H : Finset (Fin n) := A₀ ∪ B ∪ C
  have h_last_zero : (Fin.last 0 : Fin 1) = 0 := rfl
  rw [h_last_zero] at hL_card
  obtain ⟨ℓ₁, ℓ₂, hℓ₁₂, hL0⟩ := Finset.card_eq_two.mp hL_card
  have h_fin1 : ∀ i : Fin 1, i = 0 := fun i => Fin.ext (by omega)
  have h_img_v : Finset.univ.image v = ({u} : Finset (Fin n)) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      rw [h_fin1 i]
    · rintro rfl
      exact ⟨0, rfl⟩
  have h_biUnion_L : Finset.univ.biUnion L = L 0 := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hx⟩
      rwa [h_fin1 i] at hx
    · intro hx
      exact ⟨0, hx⟩
  have hP_insert : P = insert u (L 0) := by
    rw [hP_eq, h_img_v, h_biUnion_L, Finset.singleton_union]
  have hP_pair : P = ({u, ℓ₁, ℓ₂} : Finset (Fin n)) := by
    rw [hP_insert, hL0]
  have hℓ₁_in : ℓ₁ ∈ L 0 := by
    rw [hL0]
    exact Finset.mem_insert_self ℓ₁ {ℓ₂}
  have hℓ₂_in : ℓ₂ ∈ L 0 := by
    rw [hL0]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self ℓ₂)
  have hℓ₁_leaf : IsLeafIn T ℓ₁ u := h_leaf_pkt 0 ℓ₁ hℓ₁_in
  have hℓ₂_leaf : IsLeafIn T ℓ₂ u := h_leaf_pkt 0 ℓ₂ hℓ₂_in
  have hadj_ℓ₁u : T.Adj ℓ₁ u := (hℓ₁_leaf u).mpr rfl
  have hadj_ℓ₂u : T.Adj ℓ₂ u := (hℓ₂_leaf u).mpr rfl
  have huℓ₁ : u ≠ ℓ₁ := (T.ne_of_adj hadj_ℓ₁u).symm
  have huℓ₂ : u ≠ ℓ₂ := (T.ne_of_adj hadj_ℓ₂u).symm
  have hu_not_L0 : u ∉ L 0 := by
    rw [hL0]
    simp [huℓ₁, huℓ₂]
  have hH_eq : H = Finset.univ \ ({u, ℓ₁, ℓ₂} : Finset (Fin n)) := by
    rw [← hP_pair]
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · intro hxH
      exact Finset.disjoint_left.mp h_disj_ABCP hxH
    · intro hxP
      have hx_univ : x ∈ H ∪ P := by
        change x ∈ A₀ ∪ B ∪ C ∪ P
        rw [h_univ_P]
        exact Finset.mem_univ x
      rcases Finset.mem_union.mp hx_univ with hxH | hx_in_P
      · exact hxH
      · exact (hxP hx_in_P).elim
  have hH_bridge : IsBridgeJoin T H ({u, ℓ₁, ℓ₂} : Finset (Fin n)) w u := by
    rw [← hP_pair]
    exact h_bridge_P
  have hu_adj : ∀ x : Fin n, T.Adj u x ↔ x = w ∨ x = ℓ₁ ∨ x = ℓ₂ := by
    intro x
    constructor
    · intro hadj
      have hx_univ : x ∈ H ∪ P := by
        change x ∈ A₀ ∪ B ∪ C ∪ P
        rw [h_univ_P]
        exact Finset.mem_univ x
      rcases Finset.mem_union.mp hx_univ with hxH | hxP
      · have huP : u ∈ P := by
          rw [hP_insert]
          exact Finset.mem_insert_self u (L 0)
        have h_uniq := h_bridge_P.2.2.2.2 x hxH u huP (T.symm hadj)
        exact Or.inl h_uniq.1
      · rw [hP_pair] at hxP
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxP
        rcases hxP with rfl | rfl | rfl
        · exact (T.ne_of_adj hadj rfl).elim
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl)
      · exact T.symm h_bridge_P.2.2.2.1
      · exact T.symm hadj_ℓ₁u
      · exact T.symm hadj_ℓ₂u
  have h_bridge_sub : ∀ (U₁ U₂ : Finset (Fin n)) (r₁ r₂ : Fin n),
      IsSubtree T U₁ → IsSubtree T U₂ → IsBridgeJoin T U₁ U₂ r₁ r₂ →
      IsSubtree T (U₁ ∪ U₂) := by
    intro U₁ U₂ r₁ r₂ hU₁ hU₂ hb
    rcases hb with ⟨_, hr₁, hr₂, hadj, _⟩
    refine ⟨⟨r₁, Finset.mem_union_left U₂ hr₁⟩, ?_⟩
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    let r₁' : (↑(U₁ ∪ U₂ : Finset (Fin n)) : Set (Fin n)) :=
      ⟨r₁, Finset.mem_coe.mpr (Finset.mem_union_left U₂ hr₁)⟩
    let r₂' : (↑(U₁ ∪ U₂ : Finset (Fin n)) : Set (Fin n)) :=
      ⟨r₂, Finset.mem_coe.mpr (Finset.mem_union_right U₁ hr₂)⟩
    let ι₁ : T.induce (U₁ : Set (Fin n)) →g T.induce ((U₁ ∪ U₂ : Finset (Fin n)) : Set (Fin n)) :=
      { toFun := fun x => ⟨x.1, Finset.mem_coe.mpr (Finset.mem_union_left U₂ (Finset.mem_coe.mp x.2))⟩
        map_rel' := fun h => h }
    let ι₂ : T.induce (U₂ : Set (Fin n)) →g T.induce ((U₁ ∪ U₂ : Finset (Fin n)) : Set (Fin n)) :=
      { toFun := fun x => ⟨x.1, Finset.mem_coe.mpr (Finset.mem_union_right U₁ (Finset.mem_coe.mp x.2))⟩
        map_rel' := fun h => h }
    refine ⟨r₁', fun z => ?_⟩
    rcases Finset.mem_union.mp (Finset.mem_coe.mp z.2) with hz₁ | hz₂
    · obtain ⟨p⟩ := hU₁.2.preconnected ⟨r₁, Finset.mem_coe.mpr hr₁⟩ ⟨z.1, Finset.mem_coe.mpr hz₁⟩
      exact ⟨p.map ι₁⟩
    · have hr₁₂ : (T.induce ((U₁ ∪ U₂ : Finset (Fin n)) : Set (Fin n))).Reachable r₁' r₂' :=
        SimpleGraph.Adj.reachable hadj
      obtain ⟨p⟩ := hU₂.2.preconnected ⟨r₂, Finset.mem_coe.mpr hr₂⟩ ⟨z.1, Finset.mem_coe.mpr hz₂⟩
      exact hr₁₂.trans ⟨p.map ι₂⟩
  have hAB_sub : IsSubtree T (A₀ ∪ B) := h_bridge_sub A₀ B w r_B hA₀_sub hB_sub h_bridge_B
  have hH_sub : IsSubtree T H := h_bridge_sub (A₀ ∪ B) C w r_C hAB_sub hC_sub h_bridge_C
  let S₂ : Finset (Fin n) → Finset (Fin n) := fun I => insert u I
  have hS₂_sub : (L 0).powerset.image S₂ ⊆ rootedSubtreesIn T P u := by
    intro S hS
    simp only [Finset.mem_image, Finset.mem_powerset] at hS
    rcases hS with ⟨I, hI, rfl⟩
    have hu_mem : u ∈ S₂ I := Finset.mem_insert_self u I
    have h_sub_P : S₂ I ⊆ P := by
      rw [hP_insert]
      exact Finset.insert_subset_insert u hI
    have h_conn : (T.induce (S₂ I : Set (Fin n))).Connected := by
      rw [SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨⟨u, hu_mem⟩, ?_⟩
      rintro ⟨y, hy⟩
      have hy' : y ∈ insert u I := hy
      rcases Finset.mem_insert.mp hy' with hy_u | hy_I
      · have h_sub_eq : (⟨y, hy⟩ : (S₂ I : Set (Fin n))) = ⟨u, hu_mem⟩ :=
          Subtype.ext hy_u
        rw [h_sub_eq]
      · have hadj_uy : T.Adj u y := T.symm ((h_leaf_pkt 0 y (hI hy_I) u).mpr rfl)
        have hadj_ind : (T.induce (S₂ I : Set (Fin n))).Adj ⟨u, hu_mem⟩ ⟨y, hy⟩ := hadj_uy
        exact hadj_ind.reachable
    simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨⟨u, hu_mem⟩, h_conn⟩, h_sub_P, hu_mem⟩
  have hS₂_inj : Set.InjOn S₂ ((L 0).powerset : Set (Finset (Fin n))) := by
    intro I₁ hI₁ I₂ hI₂ h_eq
    simp only [Finset.mem_coe, Finset.mem_powerset] at hI₁ hI₂
    have hu₁ : u ∉ I₁ := fun h => hu_not_L0 (hI₁ h)
    have hu₂ : u ∉ I₂ := fun h => hu_not_L0 (hI₂ h)
    have h_er := congrArg (fun S : Finset (Fin n) => S.erase u) h_eq
    dsimp [S₂] at h_er
    rwa [Finset.erase_insert hu₁, Finset.erase_insert hu₂] at h_er
  have hP_ge4 : 4 ≤ rootedCount T P u := by
    have h_le : ((L 0).powerset.image S₂).card ≤ rootedCount T P u :=
      Finset.card_le_card hS₂_sub
    rw [Finset.card_image_of_injOn hS₂_inj, Finset.card_powerset, hL_card] at h_le
    exact h_le
  have hB_ge4 : 4 ≤ rootedCount T B r_B := le_trans hP_ge4 h_dom_B
  have hC_ge4 : 4 ≤ rootedCount T C r_C := le_trans hP_ge4 h_dom_C
  have hw_H : w ∈ H := Finset.mem_union_left C (Finset.mem_union_left B h_bridge_B.2.1)
  have hH_pos : 1 ≤ H.card := Finset.card_pos.mpr ⟨w, hw_H⟩
  have hP_card : P.card = 3 := by
    rw [hP_insert, Finset.card_insert_of_notMem hu_not_L0, hL_card]
  have h_card_sum : H.card + P.card = Fintype.card (Fin n) := by
    rw [← Finset.card_union_of_disjoint h_disj_ABCP]
    have h_u : H ∪ P = Finset.univ := h_univ_P
    rw [h_u, Finset.card_univ]
  have hn4 : 4 ≤ Fintype.card (Fin n) := by omega
  exact ⟨u, ℓ₁, ℓ₂, hℓ₁₂, huℓ₁, huℓ₂, hP_pair, hH_eq, hH_sub, hH_bridge,
    hℓ₁_leaf, hℓ₂_leaf, hu_adj, hB_ge4, hC_ge4, hn4⟩

theorem cherry_small_core_second_disjunct : ∀ (n : ℕ) (T : SimpleGraph (Fin n)) (ℓ : ℕ)
    (A₀ B C P : Finset (Fin n)) (w r_B r_C : Fin n)
    (v : Fin (ℓ + 1) → Fin n) (L : Fin (ℓ + 1) → Finset (Fin n)),
    IsMinCountTerminalArm T ℓ A₀ B C P w r_B r_C v L →
    4 ≤ rootedCount T B r_B →
    4 ≤ rootedCount T C r_C →
    A₀.card ≤ 2 →
    ∃ (L_c B' C' : Finset (Fin n)) (r_B' r_C' : Fin n),
      w ∉ L_c ∧ L_c.card ≤ 1 ∧ IsLeafPacket T L_c w ∧
      Disjoint (insert w L_c) B' ∧ Disjoint (insert w L_c) C' ∧ Disjoint B' C' ∧
      A₀ ∪ B ∪ C = (insert w L_c) ∪ B' ∪ C' ∧
      IsSubtree T B' ∧ IsSubtree T C' ∧
      IsBridgeJoin T (insert w L_c) B' w r_B' ∧
      IsBridgeJoin T ((insert w L_c) ∪ B') C' w r_C' ∧
      4 ≤ rootedCount T B' r_B' ∧ 4 ≤ rootedCount T C' r_C' :=
by
  intro n T ℓ A₀ B C P w r_B r_C v L h_arm hB_ge4 hC_ge4 hA₀_le
  obtain ⟨_, _, hA₀_sub, hB_sub, hC_sub, _, h_disj_AB, h_disj_AC, h_disj_BC, _,
    h_univ, _, _, _, h_bridge_B, h_bridge_C, h_bridge_P, _, _, _, _⟩ := h_arm
  have hw : w ∈ A₀ := h_bridge_B.2.1
  have hw_not_mem : w ∉ A₀.erase w := Finset.notMem_erase w A₀
  have hLc_card : (A₀.erase w).card ≤ 1 := by
    have h_er := Finset.card_erase_of_mem hw
    omega
  have h_ins : insert w (A₀.erase w) = A₀ := Finset.insert_erase hw
  have hLc_leaf : IsLeafPacket T (A₀.erase w) w := by
    intro x hx
    obtain ⟨hxw, hxA⟩ := Finset.mem_erase.mp hx
    have hA₀_cases : ∀ z ∈ A₀, z = w ∨ z = x := by
      intro z hzA
      by_cases hzw : z = w
      · exact Or.inl hzw
      · have hz_er : z ∈ A₀.erase w := Finset.mem_erase.mpr ⟨hzw, hzA⟩
        exact Or.inr (Finset.card_le_one.mp hLc_card z hz_er x hx)
    have hx_adj_w : T.Adj x w := by
      obtain ⟨p⟩ := hA₀_sub.2.preconnected ⟨x, hxA⟩ ⟨w, hw⟩
      cases p with
      | nil => exact absurd rfl hxw
      | @cons _ z _ h_adj _ =>
        have h_adj' : T.Adj x z.1 := h_adj
        rcases hA₀_cases z.1 z.2 with hzw | hzx
        · exact hzw ▸ h_adj'
        · exfalso
          exact T.loopless x (hzx ▸ h_adj')
    intro y
    constructor
    · intro hxy
      have hy_univ : y ∈ A₀ ∪ B ∪ C ∪ P := h_univ ▸ Finset.mem_univ y
      rcases Finset.mem_union.mp hy_univ with hyABC | hyP
      · rcases Finset.mem_union.mp hyABC with hyAB | hyC
        · rcases Finset.mem_union.mp hyAB with hyA | hyB
          · rcases hA₀_cases y hyA with hyw | hyx
            · exact hyw
            · exfalso
              exact T.loopless x (hyx ▸ hxy)
          · exfalso
            exact hxw (h_bridge_B.2.2.2.2 x hxA y hyB hxy).1
        · exfalso
          have hxAB : x ∈ A₀ ∪ B := Finset.mem_union_left B hxA
          exact hxw (h_bridge_C.2.2.2.2 x hxAB y hyC hxy).1
      · exfalso
        have hxABC : x ∈ A₀ ∪ B ∪ C := Finset.mem_union_left C (Finset.mem_union_left B hxA)
        exact hxw (h_bridge_P.2.2.2.2 x hxABC y hyP hxy).1
    · rintro rfl
      exact hx_adj_w
  refine ⟨A₀.erase w, B, C, r_B, r_C, hw_not_mem, hLc_card, hLc_leaf, ?_⟩
  rw [h_ins]
  exact ⟨h_disj_AB, h_disj_AC, h_disj_BC, rfl, hB_sub, hC_sub, h_bridge_B, h_bridge_C, hB_ge4, hC_ge4⟩

theorem cherry_large_core_setup : ∀ (n : ℕ) (T : SimpleGraph (Fin n)) (ℓ : ℕ)
    (A₀ B C P : Finset (Fin n)) (w r_B r_C : Fin n)
    (v : Fin (ℓ + 1) → Fin n) (L : Fin (ℓ + 1) → Finset (Fin n)),
    ¬ HasLeafAtDegTwo T →
    IsMinCountTerminalArm T ℓ A₀ B C P w r_B r_C v L →
    4 ≤ Fintype.card (Fin n) →
    3 ≤ A₀.card →
    A₀.card ≤ rootedCount T A₀ w →
    A₀ ∪ B ∪ C = (A₀ ∪ C) ∪ B ∧
    IsSubtree T (A₀ ∪ C) ∧
    IsBridgeJoin T (A₀ ∪ C) B w r_B ∧
    IsBridgeJoin T A₀ C w r_C ∧
    4 ≤ rootedCount T A₀ w :=
by
  classical
  intro n T ℓ A₀ B C P w r_B r_C v L h_deg2 h_arm hn4 hA₀_ge3 hA₀_card
  obtain ⟨_, _, hA₀_sub, hB_sub, hC_sub, _, h_disj_AB, h_disj_AC, h_disj_BC, _,
    h_univ, _, _, _, h_bridge_B, h_bridge_C, h_bridge_P, _, _, _, _⟩ := h_arm
  have hw : w ∈ A₀ := h_bridge_B.2.1
  have hr_B : r_B ∈ B := h_bridge_B.2.2.1
  have hadj_wB : T.Adj w r_B := h_bridge_B.2.2.2.1
  have hr_C : r_C ∈ C := h_bridge_C.2.2.1
  have hadj_wC : T.Adj w r_C := h_bridge_C.2.2.2.1
  have hH_split : A₀ ∪ B ∪ C = (A₀ ∪ C) ∪ B := Finset.union_right_comm A₀ B C
  have hA₀_C_bridge : IsBridgeJoin T A₀ C w r_C := by
    refine ⟨h_disj_AC, hw, hr_C, hadj_wC, ?_⟩
    intro u hu y hy hadj
    exact h_bridge_C.2.2.2.2 u (Finset.mem_union_left B hu) y hy hadj
  have hAC_sub : IsSubtree T (A₀ ∪ C) := by
    refine ⟨⟨w, Finset.mem_union_left C hw⟩, ?_⟩
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    let w' : (↑(A₀ ∪ C : Finset (Fin n)) : Set (Fin n)) :=
      ⟨w, Finset.mem_coe.mpr (Finset.mem_union_left C hw)⟩
    let r_C' : (↑(A₀ ∪ C : Finset (Fin n)) : Set (Fin n)) :=
      ⟨r_C, Finset.mem_coe.mpr (Finset.mem_union_right A₀ hr_C)⟩
    let ι₁ : T.induce (A₀ : Set (Fin n)) →g T.induce ((A₀ ∪ C : Finset (Fin n)) : Set (Fin n)) :=
      { toFun := fun x => ⟨x.1, Finset.mem_coe.mpr (Finset.mem_union_left C (Finset.mem_coe.mp x.2))⟩
        map_rel' := fun h => h }
    let ι₂ : T.induce (C : Set (Fin n)) →g T.induce ((A₀ ∪ C : Finset (Fin n)) : Set (Fin n)) :=
      { toFun := fun x => ⟨x.1, Finset.mem_coe.mpr (Finset.mem_union_right A₀ (Finset.mem_coe.mp x.2))⟩
        map_rel' := fun h => h }
    refine ⟨w', fun z => ?_⟩
    rcases Finset.mem_union.mp (Finset.mem_coe.mp z.2) with hz₁ | hz₂
    · obtain ⟨p⟩ := hA₀_sub.2.preconnected ⟨w, Finset.mem_coe.mpr hw⟩ ⟨z.1, Finset.mem_coe.mpr hz₁⟩
      exact ⟨p.map ι₁⟩
    · have hwC : (T.induce ((A₀ ∪ C : Finset (Fin n)) : Set (Fin n))).Reachable w' r_C' :=
        SimpleGraph.Adj.reachable hadj_wC
      obtain ⟨p⟩ := hC_sub.2.preconnected ⟨r_C, Finset.mem_coe.mpr hr_C⟩ ⟨z.1, Finset.mem_coe.mpr hz₂⟩
      exact hwC.trans ⟨p.map ι₂⟩
  have hAC_B_bridge : IsBridgeJoin T (A₀ ∪ C) B w r_B := by
    refine ⟨Finset.disjoint_union_left.mpr ⟨h_disj_AB, h_disj_BC.symm⟩,
      Finset.mem_union_left C hw, hr_B, hadj_wB, ?_⟩
    intro u hu y hy hadj
    rcases Finset.mem_union.mp hu with huA | huC
    · exact h_bridge_B.2.2.2.2 u huA y hy hadj
    · exfalso
      have hyAB : y ∈ A₀ ∪ B := Finset.mem_union_right A₀ hy
      have hyw : y = w := (h_bridge_C.2.2.2.2 y hyAB u huC (T.symm hadj)).1
      exact Finset.disjoint_left.mp h_disj_AB hw (hyw ▸ hy)
  have hf_ge4 : 4 ≤ rootedCount T A₀ w := by
    by_cases hA₀_ge4 : 4 ≤ A₀.card
    · exact le_trans hA₀_ge4 hA₀_card
    · have h_er_card : (A₀.erase w).card = 2 := by
        have h_er := Finset.card_erase_of_mem hw
        omega
      obtain ⟨x₁, x₂, hx₁₂, h_er⟩ := Finset.card_eq_two.mp h_er_card
      have hA₀_ins : insert w (A₀.erase w) = A₀ := Finset.insert_erase hw
      have hw_not_er : w ∉ A₀.erase w := Finset.notMem_erase w A₀
      have hx₁_er : x₁ ∈ A₀.erase w := by rw [h_er]; simp
      have hx₂_er : x₂ ∈ A₀.erase w := by rw [h_er]; simp
      obtain ⟨hx₁w, hx₁A⟩ := Finset.mem_erase.mp hx₁_er
      obtain ⟨hx₂w, hx₂A⟩ := Finset.mem_erase.mp hx₂_er
      have hz_cases : ∀ z ∈ A₀, z = w ∨ z = x₁ ∨ z = x₂ := by
        intro z hz
        rw [← hA₀_ins, h_er] at hz
        simpa [or_assoc] using hz
      have hA₀_iso : ∀ u ∈ A₀, u ≠ w → ∀ y : Fin n, T.Adj u y → y ∈ A₀ := by
        intro u hu huw y huy
        have hy_univ : y ∈ A₀ ∪ B ∪ C ∪ P := h_univ ▸ Finset.mem_univ y
        rcases Finset.mem_union.mp hy_univ with hyABC | hyP
        · rcases Finset.mem_union.mp hyABC with hyAB | hyC
          · rcases Finset.mem_union.mp hyAB with hyA | hyB
            · exact hyA
            · exact False.elim (huw (h_bridge_B.2.2.2.2 u hu y hyB huy).1)
          · exact False.elim (huw (h_bridge_C.2.2.2.2 u (Finset.mem_union_left B hu) y hyC huy).1)
        · exact False.elim (huw (h_bridge_P.2.2.2.2 u
            (Finset.mem_union_left C (Finset.mem_union_left B hu)) y hyP huy).1)
      have hA₀_step : ∀ u ∈ A₀, ∀ z ∈ A₀, u ≠ z → ∃ y ∈ A₀, y ≠ u ∧ T.Adj u y := by
        intro u hu z hz huz
        obtain ⟨p⟩ := hA₀_sub.2.preconnected ⟨u, hu⟩ ⟨z, hz⟩
        cases p with
        | nil => exact False.elim (huz rfl)
        | @cons _ y _ hadj _ =>
          have hadj' : T.Adj u y.1 := hadj
          exact ⟨y.1, y.2, fun h => T.loopless u (h ▸ hadj'), hadj'⟩
      have h_deg2_of_path : ∀ (u₁ u₂ : Fin n),
          u₁ ∈ A₀ → u₂ ∈ A₀ → u₁ ≠ w → u₂ ≠ w →
          (∀ z ∈ A₀, z = w ∨ z = u₁ ∨ z = u₂) →
          T.Adj w u₁ → ¬ T.Adj w u₂ → False := by
        intro u₁ u₂ hu₁A hu₂A hu₁w hu₂w hz_u hadj_wu₁ hnot_wu₂
        obtain ⟨y, hyA, hy_ne, hadj_u₂y⟩ := hA₀_step u₂ hu₂A w hw hu₂w
        have hy_eq : y = u₁ := by
          rcases hz_u y hyA with rfl | rfl | rfl
          · exact False.elim (hnot_wu₂ (T.symm hadj_u₂y))
          · rfl
          · exact False.elim (hy_ne rfl)
        have hadj_u₂u₁ : T.Adj u₂ u₁ := hy_eq ▸ hadj_u₂y
        have h_leaf_u₂ : IsLeafIn T u₂ u₁ := by
          intro z
          constructor
          · intro hz
            rcases hz_u z (hA₀_iso u₂ hu₂A hu₂w z hz) with rfl | rfl | rfl
            · exact False.elim (hnot_wu₂ (T.symm hz))
            · rfl
            · exact False.elim (T.loopless z hz)
          · rintro rfl
            exact hadj_u₂u₁
        have h_deg2_u₁ : ∀ z : Fin n, T.Adj u₁ z ↔ z = u₂ ∨ z = w := by
          intro z
          constructor
          · intro hz
            rcases hz_u z (hA₀_iso u₁ hu₁A hu₁w z hz) with rfl | rfl | rfl
            · exact Or.inr rfl
            · exact False.elim (T.loopless z hz)
            · exact Or.inl rfl
          · rintro (rfl | rfl)
            · exact T.symm hadj_u₂u₁
            · exact T.symm hadj_wu₁
        exact h_deg2 ⟨hn4, u₂, u₁, w, hu₂w, h_leaf_u₂, h_deg2_u₁⟩
      by_cases hw₁ : T.Adj w x₁
      · by_cases hw₂ : T.Adj w x₂
        · let S₂ : Finset (Fin n) → Finset (Fin n) := fun I => insert w I
          have hS₂_in : ∀ I ∈ (A₀.erase w).powerset, S₂ I ∈ rootedSubtreesIn T A₀ w := by
            intro I hI
            rw [Finset.mem_powerset] at hI
            have hw_mem : w ∈ S₂ I := Finset.mem_insert_self w I
            have h_sub_A₀ : S₂ I ⊆ A₀ := hA₀_ins ▸ Finset.insert_subset_insert w hI
            have h_conn : (T.induce (S₂ I : Set (Fin n))).Connected := by
              rw [SimpleGraph.connected_iff_exists_forall_reachable]
              refine ⟨⟨w, hw_mem⟩, ?_⟩
              rintro ⟨y, hy⟩
              have hy' : y ∈ insert w I := hy
              rcases Finset.mem_insert.mp hy' with rfl | hyI
              · exact SimpleGraph.Reachable.refl _
              · have hy_er : y ∈ A₀.erase w := hI hyI
                rw [h_er] at hy_er
                have hadj_wy : T.Adj w y := by
                  rcases Finset.mem_insert.mp hy_er with rfl | hy₂
                  · exact hw₁
                  · rw [Finset.mem_singleton.mp hy₂]
                    exact hw₂
                have hadj_ind : (T.induce (S₂ I : Set (Fin n))).Adj ⟨w, hw_mem⟩ ⟨y, hy⟩ := hadj_wy
                exact hadj_ind.reachable
            simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨⟨⟨w, hw_mem⟩, h_conn⟩, h_sub_A₀, hw_mem⟩
          have hS₂_inj : Set.InjOn S₂ ((A₀.erase w).powerset : Set (Finset (Fin n))) := by
            intro I₁ hI₁ I₂ hI₂ h_eq
            simp only [Finset.mem_coe, Finset.mem_powerset] at hI₁ hI₂
            have hw₁_not : w ∉ I₁ := fun h => hw_not_er (hI₁ h)
            have hw₂_not : w ∉ I₂ := fun h => hw_not_er (hI₂ h)
            have h_er_eq := congrArg (fun S => S.erase w) h_eq
            dsimp [S₂] at h_er_eq
            rwa [Finset.erase_insert hw₁_not, Finset.erase_insert hw₂_not] at h_er_eq
          have h_sub : (A₀.erase w).powerset.image S₂ ⊆ rootedSubtreesIn T A₀ w := by
            intro S hS
            simp only [Finset.mem_image] at hS
            rcases hS with ⟨I, hI, rfl⟩
            exact hS₂_in I hI
          have h_le := Finset.card_le_card h_sub
          rw [Finset.card_image_of_injOn hS₂_inj, Finset.card_powerset, h_er_card] at h_le
          exact h_le
        · exact False.elim (h_deg2_of_path x₁ x₂ hx₁A hx₂A hx₁w hx₂w hz_cases hw₁ hw₂)
      · by_cases hw₂ : T.Adj w x₂
        · exact False.elim (h_deg2_of_path x₂ x₁ hx₂A hx₁A hx₂w hx₁w
            (fun z hz => by rcases hz_cases z hz with rfl | rfl | rfl <;> tauto) hw₂ hw₁)
        · exfalso
          obtain ⟨y, hyA, hyw, hadj_wy⟩ := hA₀_step w hw x₁ hx₁A hx₁w.symm
          rcases hz_cases y hyA with rfl | rfl | rfl
          · exact hyw rfl
          · exact hw₁ hadj_wy
          · exact hw₂ hadj_wy
  exact ⟨hH_split, hAC_sub, hAC_B_bridge, hA₀_C_bridge, hf_ge4⟩

theorem min_arm_cherry_to_terminal_cherry : ∀ (n : ℕ) (hn : 1 ≤ n) (T : SimpleGraph (Fin n)),
    T.IsTree → ¬ HasLeafAtDegTwo T →
    ∀ (ℓ : ℕ) (A₀ B C P : Finset (Fin n)) (w r_B r_C : Fin n)
      (v : Fin (ℓ + 1) → Fin n) (L : Fin (ℓ + 1) → Finset (Fin n)),
      IsMinCountTerminalArm T ℓ A₀ B C P w r_B r_C v L →
      (∀ i : Fin (ℓ + 1), i.val < ℓ → L i = ∅) →
      (ℓ = 0 ∧ (L (Fin.last ℓ)).card = 2) →
      HasTerminalCherryBranch T :=
by
  intro n _hn T hT h_deg2 ℓ A₀ B C P w r_B r_C v L h_arm _h_int h_cherry
  obtain ⟨u, ℓ₁, ℓ₂, hℓ₁₂, huℓ₁, huℓ₂, _hP_eq, hH_eq, hH_sub, hH_bridge,
    hℓ₁_leaf, hℓ₂_leaf, hu_adj, hB_ge4, hC_ge4, hn4⟩ :=
    cherry_arm_unpack_and_bounds n T ℓ A₀ B C P w r_B r_C v L h_arm h_cherry
  refine ⟨w, u, ℓ₁, ℓ₂, A₀ ∪ B ∪ C, hℓ₁₂, huℓ₁, huℓ₂, hH_eq, hH_sub, hH_bridge,
    hℓ₁_leaf, hℓ₂_leaf, hu_adj, ?_⟩
  by_cases hA₀_le : A₀.card ≤ 2
  · exact Or.inr (cherry_small_core_second_disjunct n T ℓ A₀ B C P w r_B r_C v L
      h_arm hB_ge4 hC_ge4 hA₀_le)
  · have hA₀_ge3 : 3 ≤ A₀.card := by omega
    obtain ⟨_, _, hA₀_sub, hB_sub, hC_sub, _, _, _, _, _, _, _, _, _,
      h_bridge_B, h_bridge_C, _, _, _, _, _⟩ := id h_arm
    have hw : w ∈ A₀ := h_bridge_B.2.1
    have hr_C : r_C ∈ C := h_bridge_C.2.2.1
    obtain ⟨hA₀_card, hA₀_mom⟩ :=
      rooted_subtree_card_and_moment_bound n T A₀ w hT hA₀_sub hw
    obtain ⟨_hC_card, hC_mom⟩ :=
      rooted_subtree_card_and_moment_bound n T C r_C hT hC_sub hr_C
    obtain ⟨hH_split, hAC_sub, hAC_B_bridge, hA₀_C_bridge, hf_ge4⟩ :=
      cherry_large_core_setup n T ℓ A₀ B C P w r_B r_C v L h_deg2 h_arm hn4 hA₀_ge3 hA₀_card
    obtain ⟨hsA, htA⟩ :=
      bridge_join_rooted_moments n T A₀ C w r_C hA₀_C_bridge
    refine Or.inl ⟨A₀ ∪ C, B, r_B, hH_split, hAC_sub, hB_sub, hAC_B_bridge, ?_⟩
    set f := rootedCount T A₀ w
    set tA₀ := rootedOrderSum T A₀ w
    set y := rootedCount T C r_C
    set tC := rootedOrderSum T C r_C
    set sA := rootedCount T (A₀ ∪ C) w
    set tA := rootedOrderSum T (A₀ ∪ C) w
    have h1 : (2 * tA₀) * (1 + y) ≤ (f * (f + 1)) * (1 + y) :=
      Nat.mul_le_mul_right (1 + y) hA₀_mom
    have h2 : f * (2 * tC) ≤ f * (y * (y + 1)) :=
      Nat.mul_le_mul_left f hC_mom
    have h2tA : 2 * tA ≤ sA * (f + y + 1) := by
      calc 2 * tA = (2 * tA₀) * (1 + y) + f * (2 * tC) := by rw [htA]; ring
        _ ≤ (f * (f + 1)) * (1 + y) + f * (y * (y + 1)) := Nat.add_le_add h1 h2
        _ = sA * (f + y + 1) := by rw [hsA]; ring
    have hf_eq : f = (f - 4) + 4 := by omega
    have hy_eq : y = (y - 4) + 4 := by omega
    have h_poly : 60 * (f + y + 1) ≤ 25 * sA + 48 := by
      calc 60 * (f + y + 1)
        _ = 60 * (((f - 4) + 4) + ((y - 4) + 4) + 1) := by rw [← hf_eq, ← hy_eq]
        _ ≤ 60 * (((f - 4) + 4) + ((y - 4) + 4) + 1) +
            (25 * (f - 4) * (y - 4) + 65 * (f - 4) + 40 * (y - 4) + 8) := Nat.le_add_right _ _
        _ = 25 * (((f - 4) + 4) * (1 + ((y - 4) + 4))) + 48 := by ring
        _ = 25 * sA + 48 := by rw [← hf_eq, ← hy_eq, ← hsA]
    calc 120 * tA = 60 * (2 * tA) := by ring
      _ ≤ 60 * (sA * (f + y + 1)) := Nat.mul_le_mul_left 60 h2tA
      _ = sA * (60 * (f + y + 1)) := by ring
      _ ≤ sA * (25 * sA + 48) := Nat.mul_le_mul_left sA h_poly
      _ = 25 * sA ^ 2 + 48 * sA := by ring

theorem min_arm_broom_to_count_dominated_broom : ∀ (n : ℕ) (hn : 1 ≤ n) (T : SimpleGraph (Fin n)),
    T.IsTree → ∀ (ℓ : ℕ) (A₀ B C P : Finset (Fin n)) (w r_B r_C : Fin n)
      (v : Fin (ℓ + 1) → Fin n) (L : Fin (ℓ + 1) → Finset (Fin n)),
      IsMinCountTerminalArm T ℓ A₀ B C P w r_B r_C v L →
      (∀ i : Fin (ℓ + 1), i.val < ℓ → L i = ∅) →
      ¬ (ℓ = 0 ∧ (L (Fin.last ℓ)).card = 2) →
      HasCountDominatedBroom T :=
by
  intro n hn T hT ℓ A₀ B C P w r_B r_C v L h_arm h_int_empty h_not_cherry
  rcases h_arm with ⟨h_k, h_inj, hA₀, hB, hC, hP, h_disj_A₀B, h_disj_A₀C, h_disj_BC,
    h_disj_ABCP, h_univ, hP_eq, h_disj_vL, h_disj_L, h_bridge_B, h_bridge_C, h_bridge_P,
    h_spine_adj, h_leaf_pkt, h_dom_B, h_dom_C⟩
  have h_param : (1 ≤ ℓ ∧ 2 ≤ (L (Fin.last ℓ)).card) ∨ (ℓ = 0 ∧ 3 ≤ (L (Fin.last ℓ)).card) := by
    omega
  have h_biUnion : Finset.univ.biUnion L = L (Fin.last ℓ) := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hx⟩
      by_cases hi : i.val < ℓ
      · rw [h_int_empty i hi] at hx
        exact (Finset.notMem_empty x hx).elim
      · have hi_eq : i = Fin.last ℓ := by
          ext
          simp only [Fin.val_last]
          omega
        rwa [hi_eq] at hx
    · intro hx
      exact ⟨Fin.last ℓ, hx⟩
  have hP_broom : P = (Finset.univ.image v) ∪ L (Fin.last ℓ) := by
    rw [hP_eq, h_biUnion]
  have h_disj_vLk : Disjoint (Finset.univ.image v) (L (Fin.last ℓ)) := by
    rwa [h_biUnion] at h_disj_vL
  have h_disj_ABC_v : Disjoint (A₀ ∪ B ∪ C) (Finset.univ.image v) := by
    rw [hP_broom, Finset.disjoint_union_right] at h_disj_ABCP
    exact h_disj_ABCP.1
  have h_disj_ABC_Lk : Disjoint (A₀ ∪ B ∪ C) (L (Fin.last ℓ)) := by
    rw [hP_broom, Finset.disjoint_union_right] at h_disj_ABCP
    exact h_disj_ABCP.2
  have h_univ_broom : A₀ ∪ B ∪ C ∪ (Finset.univ.image v) ∪ L (Fin.last ℓ) = Finset.univ := by
    rw [Finset.union_assoc (A₀ ∪ B ∪ C), ← hP_broom]
    exact h_univ
  have h_bridge_P_broom : IsBridgeJoin T (A₀ ∪ B ∪ C) ((Finset.univ.image v) ∪ L (Fin.last ℓ)) w (v 0) := by
    rwa [← hP_broom]
  have h_spine_reach : ∀ (S : Finset (Fin n)) (m : ℕ) (hm : m ≤ ℓ)
      (hS : ∀ j : Fin (ℓ + 1), j.val ≤ m → v j ∈ S)
      (hv0 : v 0 ∈ S) (d : ℕ) (hd : d ≤ m),
      (T.induce (S : Set (Fin n))).Reachable ⟨v 0, hv0⟩
        ⟨v ⟨d, by omega⟩, hS ⟨d, by omega⟩ hd⟩ := by
    intro S m hm hS hv0 d
    induction d with
    | zero =>
      intro hd
      have h0 : (⟨0, by omega⟩ : Fin (ℓ + 1)) = 0 := rfl
      have hsub : (⟨v ⟨0, by omega⟩, hS ⟨0, by omega⟩ hd⟩ : (S : Set (Fin n))) = ⟨v 0, hv0⟩ := by
        ext
        simp [h0]
      rw [hsub]
    | succ d ih =>
      intro hd
      have hd_le : d ≤ m := by omega
      have h_prev := ih hd_le
      have h_adj : (T.induce (S : Set (Fin n))).Adj
          ⟨v ⟨d, by omega⟩, hS ⟨d, by omega⟩ hd_le⟩
          ⟨v ⟨d + 1, by omega⟩, hS ⟨d + 1, by omega⟩ hd⟩ := by
        change T.Adj (v ⟨d, by omega⟩) (v ⟨d + 1, by omega⟩)
        exact (h_spine_adj ⟨d, by omega⟩ ⟨d + 1, by omega⟩).mpr (Or.inl rfl)
      exact h_prev.trans h_adj.reachable
  have h_spine_reach_fin : ∀ (S : Finset (Fin n)) (m : ℕ) (hm : m ≤ ℓ)
      (hS : ∀ j : Fin (ℓ + 1), j.val ≤ m → v j ∈ S)
      (hv0 : v 0 ∈ S) (j : Fin (ℓ + 1)) (hj : j.val ≤ m) (hvj : v j ∈ S),
      (T.induce (S : Set (Fin n))).Reachable ⟨v 0, hv0⟩ ⟨v j, hvj⟩ := by
    intro S m hm hS hv0 j hj hvj
    have h_r := h_spine_reach S m hm hS hv0 j.val hj
    have h_eq : (⟨v ⟨j.val, by omega⟩, hS ⟨j.val, by omega⟩ hj⟩ : (S : Set (Fin n))) = ⟨v j, hvj⟩ := by
      ext
      rfl
    rwa [h_eq] at h_r
  have h_card_prefix : ℓ ≤ ((rootedSubtreesIn T P (v 0)).filter (fun S => v (Fin.last ℓ) ∉ S)).card := by
    let S₁ : Fin ℓ → Finset (Fin n) :=
      fun m => (Finset.univ.filter (fun j : Fin (ℓ + 1) => j.val ≤ m.val)).image v
    have hS₁_mem_v : ∀ (m : Fin ℓ) (j : Fin (ℓ + 1)), v j ∈ S₁ m ↔ j.val ≤ m.val := by
      intro m j
      simp only [S₁, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j', hj', h_eq⟩
        have hjj' := h_inj h_eq
        subst hjj'
        exact hj'
      · intro hj
        exact ⟨j, hj, rfl⟩
    have hS₁_in_filter : ∀ m : Fin ℓ,
        S₁ m ∈ (rootedSubtreesIn T P (v 0)).filter (fun S => v (Fin.last ℓ) ∉ S) := by
      intro m
      have hv0 : v 0 ∈ S₁ m := (hS₁_mem_v m 0).mpr (Nat.zero_le _)
      have h_not_last : v (Fin.last ℓ) ∉ S₁ m := by
        rw [hS₁_mem_v m (Fin.last ℓ), Fin.val_last]
        omega
      have h_sub_P : S₁ m ⊆ P := by
        intro x hx
        rw [hP_broom, Finset.mem_union]
        left
        simp only [S₁, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        rcases hx with ⟨j, _, rfl⟩
        exact ⟨j, rfl⟩
      have h_conn : (T.induce (S₁ m : Set (Fin n))).Connected := by
        rw [SimpleGraph.connected_iff_exists_forall_reachable]
        refine ⟨⟨v 0, hv0⟩, ?_⟩
        rintro ⟨u, hu⟩
        have hu' : u ∈ S₁ m := hu
        simp only [S₁, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hu'
        rcases hu' with ⟨j, hj, rfl⟩
        exact h_spine_reach_fin (S₁ m) m.val (by omega)
          (fun j' hj' => (hS₁_mem_v m j').mpr hj') hv0 j hj hu
      simp only [Finset.mem_filter, rootedSubtreesIn, subtrees, Finset.mem_univ, true_and]
      exact ⟨⟨⟨⟨v 0, hv0⟩, h_conn⟩, h_sub_P, hv0⟩, h_not_last⟩
    have hS₁_inj : Function.Injective S₁ := by
      intro m₁ m₂ h_eq
      have h1 : m₁.val ≤ m₂.val := by
        have hm1 : v ⟨m₁.val, by omega⟩ ∈ S₁ m₁ :=
          (hS₁_mem_v m₁ ⟨m₁.val, by omega⟩).mpr (le_refl _)
        rw [h_eq, hS₁_mem_v m₂ ⟨m₁.val, by omega⟩] at hm1
        exact hm1
      have h2 : m₂.val ≤ m₁.val := by
        have hm2 : v ⟨m₂.val, by omega⟩ ∈ S₁ m₂ :=
          (hS₁_mem_v m₂ ⟨m₂.val, by omega⟩).mpr (le_refl _)
        rw [← h_eq, hS₁_mem_v m₁ ⟨m₂.val, by omega⟩] at hm2
        exact hm2
      ext
      omega
    have h_sub : Finset.univ.image S₁ ⊆
        (rootedSubtreesIn T P (v 0)).filter (fun S => v (Fin.last ℓ) ∉ S) := by
      intro S hS
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hS
      rcases hS with ⟨m, rfl⟩
      exact hS₁_in_filter m
    have h_le := Finset.card_le_card h_sub
    rw [Finset.card_image_of_injective _ hS₁_inj, Finset.card_fin] at h_le
    exact h_le
  have h_card_leaf : 2 ^ (L (Fin.last ℓ)).card ≤
      ((rootedSubtreesIn T P (v 0)).filter (fun S => v (Fin.last ℓ) ∈ S)).card := by
    let S₂ : Finset (Fin n) → Finset (Fin n) :=
      fun I => (Finset.univ.image v) ∪ I
    have hS₂_in_filter : ∀ I ∈ (L (Fin.last ℓ)).powerset,
        S₂ I ∈ (rootedSubtreesIn T P (v 0)).filter (fun S => v (Fin.last ℓ) ∈ S) := by
      intro I hI
      rw [Finset.mem_powerset] at hI
      have hv_mem : ∀ j : Fin (ℓ + 1), v j ∈ S₂ I := by
        intro j
        simp only [S₂, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
        exact Or.inl ⟨j, rfl⟩
      have hv0 : v 0 ∈ S₂ I := hv_mem 0
      have hv_last : v (Fin.last ℓ) ∈ S₂ I := hv_mem (Fin.last ℓ)
      have h_sub_P : S₂ I ⊆ P := by
        rw [hP_broom]
        exact Finset.union_subset_union Finset.Subset.rfl hI
      have h_conn : (T.induce (S₂ I : Set (Fin n))).Connected := by
        rw [SimpleGraph.connected_iff_exists_forall_reachable]
        refine ⟨⟨v 0, hv0⟩, ?_⟩
        have h_last_reach : (T.induce (S₂ I : Set (Fin n))).Reachable ⟨v 0, hv0⟩ ⟨v (Fin.last ℓ), hv_last⟩ :=
          h_spine_reach_fin (S₂ I) ℓ (le_refl ℓ) (fun j _ => hv_mem j) hv0 (Fin.last ℓ) (le_refl ℓ) hv_last
        rintro ⟨u, hu⟩
        have hu' : u ∈ S₂ I := hu
        simp only [S₂, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hu'
        rcases hu' with ⟨j, rfl⟩ | hu_I
        · exact h_spine_reach_fin (S₂ I) ℓ (le_refl ℓ) (fun j' _ => hv_mem j') hv0 j (by omega) hu
        · have h_adj_T : T.Adj (v (Fin.last ℓ)) u :=
            T.symm ((h_leaf_pkt (Fin.last ℓ) u (hI hu_I) (v (Fin.last ℓ))).mpr rfl)
          have h_adj_ind : (T.induce (S₂ I : Set (Fin n))).Adj ⟨v (Fin.last ℓ), hv_last⟩ ⟨u, hu⟩ := h_adj_T
          exact h_last_reach.trans h_adj_ind.reachable
      simp only [Finset.mem_filter, rootedSubtreesIn, subtrees, Finset.mem_univ, true_and]
      exact ⟨⟨⟨⟨v 0, hv0⟩, h_conn⟩, h_sub_P, hv0⟩, hv_last⟩
    have hS₂_injOn : Set.InjOn S₂ ((L (Fin.last ℓ)).powerset : Set (Finset (Fin n))) := by
      intro I₁ hI₁ I₂ hI₂ h_eq
      simp only [Finset.mem_coe, Finset.mem_powerset] at hI₁ hI₂
      ext x
      constructor
      · intro hx
        have hx_Lk : x ∈ L (Fin.last ℓ) := hI₁ hx
        have hx_not_v : x ∉ Finset.univ.image v :=
          Finset.disjoint_right.mp h_disj_vLk hx_Lk
        have hx_S₂ : x ∈ S₂ I₂ := by
          rw [← h_eq]
          exact Finset.mem_union_right _ hx
        rcases Finset.mem_union.mp hx_S₂ with hx_v | hx_I₂
        · exact (hx_not_v hx_v).elim
        · exact hx_I₂
      · intro hx
        have hx_Lk : x ∈ L (Fin.last ℓ) := hI₂ hx
        have hx_not_v : x ∉ Finset.univ.image v :=
          Finset.disjoint_right.mp h_disj_vLk hx_Lk
        have hx_S₁ : x ∈ S₂ I₁ := by
          rw [h_eq]
          exact Finset.mem_union_right _ hx
        rcases Finset.mem_union.mp hx_S₁ with hx_v | hx_I₁
        · exact (hx_not_v hx_v).elim
        · exact hx_I₁
    have h_sub : (L (Fin.last ℓ)).powerset.image S₂ ⊆
        (rootedSubtreesIn T P (v 0)).filter (fun S => v (Fin.last ℓ) ∈ S) := by
      intro S hS
      simp only [Finset.mem_image] at hS
      rcases hS with ⟨I, hI, rfl⟩
      exact hS₂_in_filter I hI
    have h_le := Finset.card_le_card h_sub
    rw [Finset.card_image_of_injOn hS₂_injOn, Finset.card_powerset] at h_le
    exact h_le
  have h_split : ((rootedSubtreesIn T P (v 0)).filter (fun S => v (Fin.last ℓ) ∈ S)).card +
      ((rootedSubtreesIn T P (v 0)).filter (fun S => v (Fin.last ℓ) ∉ S)).card =
      rootedCount T P (v 0) := by
    simpa [rootedCount] using
      Finset.card_filter_add_card_filter_not (s := rootedSubtreesIn T P (v 0))
        (fun S : Finset (Fin n) => v (Fin.last ℓ) ∈ S)
  have h_le_P : ℓ + 2 ^ (L (Fin.last ℓ)).card ≤ rootedCount T P (v 0) := by
    rw [← h_split, add_comm]
    exact Nat.add_le_add h_card_leaf h_card_prefix
  refine ⟨ℓ, (L (Fin.last ℓ)).card, A₀, B, C, L (Fin.last ℓ), w, r_B, r_C, v,
    h_param, h_inj, hA₀, hB, hC, rfl, h_disj_A₀B, h_disj_A₀C, h_disj_BC,
    h_disj_ABC_v, h_disj_ABC_Lk, h_disj_vLk, h_univ_broom,
    h_bridge_B, h_bridge_C, h_bridge_P_broom, h_spine_adj, h_leaf_pkt (Fin.last ℓ),
    le_trans h_le_P h_dom_B, le_trans h_le_P h_dom_C⟩

theorem non_caterpillar_decomposition : ∀ (n : ℕ) (hn : 1 ≤ n) (T : SimpleGraph (Fin n)),
    T.IsTree → ¬ IsCaterpillar T →
    HasLeafAtDegTwo T ∨ HasInternalPacketSuffix T ∨ HasTerminalCherryBranch T ∨ HasCountDominatedBroom T :=
by
  intro n hn T hT h_not_cat
  by_cases h_deg2 : HasLeafAtDegTwo T
  · exact Or.inl h_deg2
  · obtain ⟨ℓ, A₀, B, C, P, w, r_B, r_C, v, L, h_arm⟩ :=
      exists_min_count_terminal_arm n hn T hT h_not_cat h_deg2
    by_cases h_int : ∃ i : Fin (ℓ + 1), i.val < ℓ ∧ (L i).Nonempty
    · exact Or.inr (Or.inl (min_arm_internal_packet_to_suffix n hn T hT ℓ A₀ B C P w r_B r_C v L h_arm h_int))
    · simp only [not_exists, not_and, Finset.not_nonempty_iff_eq_empty] at h_int
      by_cases h_cherry : ℓ = 0 ∧ (L (Fin.last ℓ)).card = 2
      · exact Or.inr (Or.inr (Or.inl (min_arm_cherry_to_terminal_cherry n hn T hT h_deg2 ℓ A₀ B C P w r_B r_C v L h_arm h_int h_cherry)))
      · exact Or.inr (Or.inr (Or.inr (min_arm_broom_to_count_dominated_broom n hn T hT ℓ A₀ B C P w r_B r_C v L h_arm h_int h_cherry)))

theorem reattachLeaf_isTree : ∀ {V : Type*} [Fintype V] (G : SimpleGraph V) (x u w : V) (hxw : x ≠ w),
    G.IsTree → IsLeafIn G x u → (reattachLeaf G x w hxw).IsTree :=
by
  intro V _ G x u w hxw hG hx
  classical
  have hG_conn : G.Connected := hG.isConnected
  have hG_acyc : G.IsAcyclic := hG.IsAcyclic
  have h_leaf_avoid : ∀ {H : SimpleGraph V} {x₀ u₀ : V}, IsLeafIn H x₀ u₀ →
      ∀ {a b : V} (p : H.Walk a b), p.IsPath → a ≠ x₀ → b ≠ x₀ → x₀ ∉ p.support := by
    intro H x₀ u₀ hx₀ a b p
    induction p with
    | nil =>
      intro _ ha _ hmem
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hmem
      exact ha hmem.symm
    | @cons a c b hac q ih =>
      intro hp ha hb
      rw [SimpleGraph.Walk.cons_isPath_iff] at hp
      rcases hp with ⟨hq, ha_not_mem⟩
      have hc : c ≠ x₀ := by
        intro hcx
        subst hcx
        cases q with
        | nil => exact hb rfl
        | @cons _ d _ hxd q' =>
          have ha_eq : a = u₀ := (hx₀ a).mp (H.symm hac)
          have hd_eq : d = u₀ := (hx₀ d).mp hxd
          have had : a = d := ha_eq.trans hd_eq.symm
          apply ha_not_mem
          rw [SimpleGraph.Walk.support_cons, had]
          exact List.mem_cons_of_mem _ q'.start_mem_support
      have hx_not_q : x₀ ∉ q.support := ih hq hc hb
      rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
      exact ⟨ha.symm, hx_not_q⟩
  have h_reach_transfer : ∀ {a b : V} (p : G.Walk a b),
      x ∉ p.support → (reattachLeaf G x w hxw).Reachable a b := by
    intro a b p
    induction p with
    | nil =>
      intro _
      exact SimpleGraph.Reachable.refl _
    | @cons a c b hac q ih =>
      intro h_not_mem
      rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at h_not_mem
      rcases h_not_mem with ⟨hxa, hx_not_q⟩
      have ha : a ≠ x := Ne.symm hxa
      have hc : c ≠ x := by
        intro hcx
        apply hx_not_q
        rw [← hcx]
        exact q.start_mem_support
      have hadj : (reattachLeaf G x w hxw).Adj a c := Or.inl ⟨ha, hc, hac⟩
      exact hadj.reachable.trans (ih hx_not_q)
  have h_conn : (reattachLeaf G x w hxw).Connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨w, fun a => ?_⟩
    by_cases hax : a = x
    · rw [hax]
      have hadj : (reattachLeaf G x w hxw).Adj w x := Or.inr (Or.inr ⟨rfl, rfl⟩)
      exact hadj.reachable
    · obtain ⟨p, hp⟩ := (hG_conn.preconnected w a).exists_isPath
      have hx_not_p : x ∉ p.support := h_leaf_avoid hx p hp hxw.symm hax
      exact h_reach_transfer p hx_not_p
  let G' := reattachLeaf G x w hxw
  have h_leaf_G' : IsLeafIn G' x w := by
    intro v
    constructor
    · intro hadj
      rcases hadj with ⟨hxx, _, _⟩ | ⟨_, rfl⟩ | ⟨hxw_eq, _⟩
      · exact False.elim (hxx rfl)
      · rfl
      · exact False.elim (hxw hxw_eq)
    · intro hvw
      subst hvw
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  have h_edge_mem : ∀ {a b : V} (q : G'.Walk a b),
      a ≠ x → b = x → s(x, w) ∈ q.edges := by
    intro a b q
    induction q with
    | nil =>
      intro ha hb
      exact False.elim (ha hb)
    | @cons a c b hac q' ih =>
      intro ha hb
      by_cases hcx : c = x
      · subst hcx
        have haw : a = w := (h_leaf_G' a).mp (G'.symm hac)
        subst haw
        rw [SimpleGraph.Walk.edges_cons, Sym2.eq_swap]
        exact List.mem_cons_self
      · rw [SimpleGraph.Walk.edges_cons]
        exact List.mem_cons_of_mem _ (ih hcx hb)
  have h_acyc : G'.IsAcyclic := by
    intro v c hc
    have hx_not_c : x ∉ c.support := by
      cases c with
      | nil => exact False.elim hc.not_of_nil
      | @cons _ y _ hvy p =>
        have h_cons := (SimpleGraph.Walk.cons_isCycle_iff p hvy).mp hc
        rcases h_cons with ⟨hp, h_no_edge⟩
        by_cases hvx : v = x
        · subst v
          have hyw : y = w := (h_leaf_G' y).mp hvy
          subst y
          have h_in : s(x, w) ∈ p.edges := h_edge_mem p hxw.symm rfl
          exact False.elim (h_no_edge h_in)
        · by_cases hyx : y = x
          · subst y
            have hvw : v = w := (h_leaf_G' v).mp (G'.symm hvy)
            cases p with
            | nil => exact False.elim (hvx rfl)
            | @cons _ z _ hxz p' =>
              have hzv : z = v := ((h_leaf_G' z).mp hxz).trans hvw.symm
              subst z
              apply False.elim (h_no_edge _)
              rw [SimpleGraph.Walk.edges_cons, Sym2.eq_swap]
              exact List.mem_cons_self
          · have hx_not_p : x ∉ p.support := h_leaf_avoid h_leaf_G' p hp hyx hvx
            rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
            exact ⟨Ne.symm hvx, hx_not_p⟩
    have h_edges : ∀ e ∈ c.edges, e ∈ G.edgeSet := by
      intro e
      refine Sym2.ind (fun a b he => ?_) e
      have ha_mem : a ∈ c.support := c.fst_mem_support_of_mem_edges he
      have hb_mem : b ∈ c.support := c.snd_mem_support_of_mem_edges he
      have ha_ne : a ≠ x := fun h => hx_not_c (h ▸ ha_mem)
      have hb_ne : b ≠ x := fun h => hx_not_c (h ▸ hb_mem)
      have hadj' : G'.Adj a b := c.adj_of_mem_edges he
      rw [SimpleGraph.mem_edgeSet]
      rcases hadj' with ⟨_, _, hab⟩ | ⟨hax, _⟩ | ⟨_, hbx⟩
      · exact hab
      · exact False.elim (ha_ne hax)
      · exact False.elim (hb_ne hbx)
    exact hG_acyc (c.transfer G h_edges) (hc.transfer h_edges)
  exact ⟨h_conn, h_acyc⟩

theorem leaf_shift_host_bounds : ∀ (n : ℕ) (T : SimpleGraph (Fin n)) (x u w : Fin n),
    4 ≤ Fintype.card (Fin n) → T.IsTree → x ≠ w → IsLeafIn T x u →
    (∀ v : Fin n, T.Adj u v ↔ v = x ∨ v = w) →
    let H := Finset.univ \ ({x, u} : Finset (Fin n))
    IsSubtree T H ∧ w ∈ H ∧
      2 ≤ rootedCount T H w ∧
      rootedCount T H w + 1 ≤ rootedOrderSum T H w ∧
      rootedCount T H w ≤ (subtreesIn T H).card :=
by
  intro n T x u w hn4 hT hxw hx hu H
  have isPath_internal_two_adj : ∀ {a b : Fin n} (p : T.Walk a b),
      p.IsPath → ∀ z ∈ p.support, z ≠ a → z ≠ b →
      ∃ v₁ v₂ : Fin n, v₁ ∈ p.support ∧ v₂ ∈ p.support ∧ v₁ ≠ v₂ ∧ T.Adj z v₁ ∧ T.Adj z v₂ := by
    intro a b p hp z hz hza hzb
    induction p with
    | nil =>
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      exact False.elim (hza hz)
    | @cons a c b h₁ p₁ ih =>
      have hp₁ : p₁.IsPath := hp.of_cons
      have h_nodup : (a :: p₁.support).Nodup := by
        have h_nd := hp.support_nodup
        rwa [SimpleGraph.Walk.support_cons] at h_nd
      have ha_not_mem : a ∉ p₁.support := (List.nodup_cons.mp h_nodup).1
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz₁
      · exact False.elim (hza rfl)
      · by_cases hzc : z = c
        · subst hzc
          cases p₁ with
          | nil => exact False.elim (hzb rfl)
          | @cons _ d _ h₂ p₂ =>
            refine ⟨a, d, ?_, ?_, ?_, T.symm h₁, h₂⟩
            · simp only [SimpleGraph.Walk.support_cons, List.mem_cons, true_or]
            · simp only [SimpleGraph.Walk.support_cons, List.mem_cons,
                SimpleGraph.Walk.start_mem_support, or_true]
            · intro had
              apply ha_not_mem
              rw [had, SimpleGraph.Walk.support_cons]
              exact List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support p₂)
        · obtain ⟨v₁, v₂, hv₁, hv₂, hne, hadj₁, hadj₂⟩ := ih hp₁ hz₁ hzc hzb
          refine ⟨v₁, v₂, ?_, ?_, hne, hadj₁, hadj₂⟩
          · exact List.mem_cons_of_mem a hv₁
          · exact List.mem_cons_of_mem a hv₂
  have h_adj_xu : T.Adj x u := (hx u).mpr rfl
  have hxu : x ≠ u := T.ne_of_adj h_adj_xu
  have h_adj_uw : T.Adj u w := (hu w).mpr (Or.inr rfl)
  have huw : u ≠ w := T.ne_of_adj h_adj_uw
  have hw : w ∈ H := by
    simp only [H, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_and, not_or]
    exact ⟨hxw.symm, huw.symm⟩
  have hH_card : 2 ≤ H.card := by
    have h1 : H.card = (Finset.univ : Finset (Fin n)).card - ({x, u} : Finset (Fin n)).card := by
      simp only [H, Finset.card_sdiff, Finset.inter_univ]
    rw [Finset.card_univ, Finset.card_pair hxu] at h1
    omega
  have hH : IsSubtree T H := by
    refine ⟨⟨w, hw⟩, ?_⟩
    have : Nonempty ↑(H : Set (Fin n)) := ⟨⟨w, hw⟩⟩
    refine ⟨?_⟩
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    have ha' : a ∈ H := ha
    have hb' : b ∈ H := hb
    simp only [H, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_and, not_or] at ha' hb'
    rcases ha' with ⟨ha_x, ha_u⟩
    rcases hb' with ⟨hb_x, hb_u⟩
    obtain ⟨p, hp⟩ := (hT.isConnected.preconnected a b).exists_isPath
    have hx_not : x ∉ p.support := by
      intro hx_mem
      obtain ⟨v₁, v₂, _, _, hne, hadj₁, hadj₂⟩ :=
        isPath_internal_two_adj p hp x hx_mem (Ne.symm ha_x) (Ne.symm hb_x)
      have hv₁ : v₁ = u := (hx v₁).mp hadj₁
      have hv₂ : v₂ = u := (hx v₂).mp hadj₂
      exact hne (hv₁.trans hv₂.symm)
    have hu_not : u ∉ p.support := by
      intro hu_mem
      obtain ⟨v₁, v₂, hv₁_mem, hv₂_mem, hne, hadj₁, hadj₂⟩ :=
        isPath_internal_two_adj p hp u hu_mem (Ne.symm ha_u) (Ne.symm hb_u)
      rcases (hu v₁).mp hadj₁ with rfl | rfl
      · exact hx_not hv₁_mem
      · rcases (hu v₂).mp hadj₂ with rfl | rfl
        · exact hx_not hv₂_mem
        · exact hne rfl
    have hw_supp : ∀ z ∈ p.support, z ∈ (H : Set (Fin n)) := by
      intro z hz
      have hzx : z ≠ x := fun h => hx_not (h ▸ hz)
      have hzu : z ≠ u := fun h => hu_not (h ▸ hz)
      simp only [Finset.mem_coe, H, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
        Finset.mem_singleton, true_and, not_or]
      exact ⟨hzx, hzu⟩
    exact (p.induce (H : Set (Fin n)) hw_supp).reachable
  have h_w_sub : IsSubtree T ({w} : Finset (Fin n)) := by
    refine ⟨Finset.singleton_nonempty w, ?_⟩
    have hw_in : w ∈ (({w} : Finset (Fin n)) : Set (Fin n)) :=
      Finset.mem_coe.mpr (Finset.mem_singleton_self w)
    have : Nonempty ↑(({w} : Finset (Fin n)) : Set (Fin n)) := ⟨⟨w, hw_in⟩⟩
    refine ⟨?_⟩
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    have ha' : a = w := Finset.mem_singleton.mp (Finset.mem_coe.mp ha)
    have hb' : b = w := Finset.mem_singleton.mp (Finset.mem_coe.mp hb)
    have hab : (⟨a, ha⟩ : ↑(({w} : Finset (Fin n)) : Set (Fin n))) = ⟨b, hb⟩ :=
      Subtype.ext (ha'.trans hb'.symm)
    rw [hab]
  have hw_mem : ({w} : Finset (Fin n)) ∈ rootedSubtreesIn T H w := by
    simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h_w_sub, Finset.singleton_subset_iff.mpr hw, Finset.mem_singleton_self w⟩
  have hH_mem : H ∈ rootedSubtreesIn T H w := by
    simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hH, Finset.Subset.refl H, hw⟩
  have hw_ne_H : ({w} : Finset (Fin n)) ≠ H := by
    intro h_eq
    have h_c : ({w} : Finset (Fin n)).card = H.card := congrArg Finset.card h_eq
    rw [Finset.card_singleton] at h_c
    omega
  have hw_erase : ({w} : Finset (Fin n)) ∈ (rootedSubtreesIn T H w).erase H :=
    Finset.mem_erase.mpr ⟨hw_ne_H, hw_mem⟩
  have h_erase_pos : 1 ≤ ((rootedSubtreesIn T H w).erase H).card :=
    Finset.one_le_card.mpr ⟨{w}, hw_erase⟩
  have h_card_split : ((rootedSubtreesIn T H w).erase H).card + 1 = rootedCount T H w := by
    dsimp only [rootedCount]
    exact Finset.card_erase_add_one hH_mem
  have hS2 : 2 ≤ rootedCount T H w := by omega
  have h_sum_ge : ((rootedSubtreesIn T H w).erase H).card ≤
      ∑ S ∈ (rootedSubtreesIn T H w).erase H, S.card := by
    calc ((rootedSubtreesIn T H w).erase H).card
      _ = ∑ _S ∈ (rootedSubtreesIn T H w).erase H, 1 := by
          rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ S ∈ (rootedSubtreesIn T H w).erase H, S.card := by
          refine Finset.sum_le_sum ?_
          intro S hS
          have hS_mem : S ∈ rootedSubtreesIn T H w := Finset.mem_of_mem_erase hS
          simp only [rootedSubtreesIn, Finset.mem_filter] at hS_mem
          exact Finset.one_le_card.mpr ⟨w, hS_mem.2.2⟩
  have h_sum_split : H.card + ∑ S ∈ (rootedSubtreesIn T H w).erase H, S.card =
      rootedOrderSum T H w := by
    dsimp only [rootedOrderSum]
    exact Finset.add_sum_erase (rootedSubtreesIn T H w) Finset.card hH_mem
  have htS : rootedCount T H w + 1 ≤ rootedOrderSum T H w := by omega
  have hSN : rootedCount T H w ≤ (subtreesIn T H).card := by
    dsimp only [rootedCount]
    refine Finset.card_le_card ?_
    intro S hS
    simp only [rootedSubtreesIn, subtreesIn, Finset.mem_filter] at hS ⊢
    exact ⟨hS.1, hS.2.1⟩
  exact ⟨hH, hw, hS2, htS, hSN⟩

theorem leaf_shift_subtree_moments : ∀ (n : ℕ) (T : SimpleGraph (Fin n)) (x u w : Fin n) (hxw : x ≠ w),
    T.IsTree → IsLeafIn T x u → (∀ v : Fin n, T.Adj u v ↔ v = x ∨ v = w) →
    let H := Finset.univ \ ({x, u} : Finset (Fin n))
    let T' := reattachLeaf T x w hxw
    subtreeCount T = (subtreesIn T H).card + 2 * rootedCount T H w + 3 ∧
    subtreeOrderSum T = (∑ S ∈ subtreesIn T H, S.card) + 2 * rootedOrderSum T H w + 3 * rootedCount T H w + 4 ∧
    subtreeCount T' = (subtreesIn T H).card + 3 * rootedCount T H w + 2 ∧
    subtreeOrderSum T' = (∑ S ∈ subtreesIn T H, S.card) + 3 * rootedOrderSum T H w + 4 * rootedCount T H w + 2 :=
by
  intro n T x u w hxw _hT hx hu H T'
  have isSubtree_insert_leaf_iff : ∀ (G : SimpleGraph (Fin n)) (U S₀ : Finset (Fin n)) (z r : Fin n),
      z ∉ U → r ∈ U → (∀ v ∈ insert z U, G.Adj z v ↔ v = r) → S₀ ⊆ U →
      (IsSubtree G (insert z S₀) ↔ S₀ = ∅ ∨ (IsSubtree G S₀ ∧ r ∈ S₀)) := by
    intro G U S₀ z r hz hr hadj hS₀
    have hzr : z ≠ r := fun h => hz (h ▸ hr)
    have hzS₀ : z ∉ S₀ := fun h => hz (hS₀ h)
    rcases S₀.eq_empty_or_nonempty with rfl | hS₀_ne
    · simp only [Finset.insert_empty, true_or, iff_true]
      refine ⟨Finset.singleton_nonempty z, ?_⟩
      rw [SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨⟨z, by simp⟩, fun ⟨w, hw⟩ => ?_⟩
      have hwz : w = z := by simpa using hw
      subst hwz
      exact SimpleGraph.Reachable.rfl
    · simp only [hS₀_ne.ne_empty, false_or]
      let S : Finset (Fin n) := insert z S₀
      change IsSubtree G S ↔ IsSubtree G S₀ ∧ r ∈ S₀
      constructor
      · intro hS
        have hr_mem : r ∈ S₀ := by
          obtain ⟨a, ha⟩ := hS₀_ne
          have h_walk : ∀ (u v : ↑(S : Set (Fin n))) (p : (G.induce (S : Set (Fin n))).Walk u v),
              u.1 = z → v.1 ∈ S₀ → r ∈ S₀ := by
            intro u v p huz hvS₀
            cases p with
            | nil =>
              exact False.elim (hzS₀ (huz ▸ hvS₀))
            | @cons _ b _ hadj_step _ =>
              have hb_mem : b.1 ∈ insert z S₀ := b.2
              have hb_U : b.1 ∈ insert z U := Finset.insert_subset_insert z hS₀ hb_mem
              have hbr : b.1 = r := (hadj b.1 hb_U).mp (huz ▸ hadj_step)
              rcases Finset.mem_insert.mp hb_mem with hbz | hbS₀
              · exact False.elim (hzr (hbz.symm.trans hbr))
              · exact hbr ▸ hbS₀
          obtain ⟨p⟩ := hS.2.preconnected
            ⟨z, Finset.mem_coe.mpr (Finset.mem_insert_self z S₀)⟩
            ⟨a, Finset.mem_coe.mpr (Finset.mem_insert_of_mem ha)⟩
          exact h_walk _ _ p rfl ha
        refine ⟨⟨hS₀_ne, ?_⟩, hr_mem⟩
        rw [SimpleGraph.connected_iff_exists_forall_reachable]
        let φ : ↑(S : Set (Fin n)) → ↑(S₀ : Set (Fin n)) := fun x =>
          ⟨if x.1 = z then r else x.1, by
            by_cases hx : x.1 = z
            · simp [hx, hr_mem]
            · simp only [hx, ↓reduceIte, Finset.mem_coe]
              rcases Finset.mem_insert.mp x.2 with hxz | h
              · exact False.elim (hx hxz)
              · exact h⟩
        have hφ_mem : ∀ (a : Fin n) (ha : a ∈ S₀),
            φ ⟨a, Finset.mem_coe.mpr (Finset.mem_insert_of_mem ha)⟩ = ⟨a, ha⟩ := by
          intro a ha
          have haz : a ≠ z := fun h => hzS₀ (h ▸ ha)
          ext
          simp [φ, haz]
        have hφ_adj : ∀ x y : ↑(S : Set (Fin n)),
            (G.induce (S : Set (Fin n))).Adj x y →
            (G.induce (S₀ : Set (Fin n))).Reachable (φ x) (φ y) := by
          intro x y hxy
          change G.Adj x.1 y.1 at hxy
          by_cases hx : x.1 = z
          · have hy_U : y.1 ∈ insert z U := Finset.insert_subset_insert z hS₀ y.2
            have hyr : y.1 = r := (hadj y.1 hy_U).mp (hx ▸ hxy)
            have hφ_eq : φ x = φ y := by
              ext
              simp [φ, hx, hyr]
            rw [hφ_eq]
          · by_cases hy : y.1 = z
            · have hx_U : x.1 ∈ insert z U := Finset.insert_subset_insert z hS₀ x.2
              have hxr : x.1 = r := (hadj x.1 hx_U).mp (hy ▸ G.symm hxy)
              have hφ_eq : φ x = φ y := by
                ext
                simp [φ, hy, hxr]
              rw [hφ_eq]
            · apply SimpleGraph.Adj.reachable
              change G.Adj (φ x).1 (φ y).1
              simp [φ, hx, hy, hxy]
        have hφ_walk : ∀ (x y : ↑(S : Set (Fin n)))
            (p : (G.induce (S : Set (Fin n))).Walk x y),
            (G.induce (S₀ : Set (Fin n))).Reachable (φ x) (φ y) := by
          intro x y p
          induction p with
          | nil => exact SimpleGraph.Reachable.rfl
          | cons h_step _ ih => exact (hφ_adj _ _ h_step).trans ih
        refine ⟨⟨r, hr_mem⟩, fun ⟨b, hb⟩ => ?_⟩
        obtain ⟨p⟩ := hS.2.preconnected
          ⟨r, Finset.mem_coe.mpr (Finset.mem_insert_of_mem hr_mem)⟩
          ⟨b, Finset.mem_coe.mpr (Finset.mem_insert_of_mem hb)⟩
        have h_reach := hφ_walk _ _ p
        rwa [hφ_mem r hr_mem, hφ_mem b hb] at h_reach
      · rintro ⟨hS₀_sub, hr_mem⟩
        refine ⟨Finset.insert_nonempty z S₀, ?_⟩
        rw [SimpleGraph.connected_iff_exists_forall_reachable]
        let ι : ↑(S₀ : Set (Fin n)) → ↑(S : Set (Fin n)) :=
          fun x => ⟨x.1, Finset.mem_coe.mpr (Finset.mem_insert_of_mem x.2)⟩
        have hι_walk : ∀ (x y : ↑(S₀ : Set (Fin n))) (p : (G.induce (S₀ : Set (Fin n))).Walk x y),
            (G.induce (S : Set (Fin n))).Reachable (ι x) (ι y) := by
          intro x y p
          induction p with
          | nil => exact SimpleGraph.Reachable.rfl
          | cons h_step _ ih =>
            have h_step' : (G.induce (S : Set (Fin n))).Adj (ι _) (ι _) := h_step
            exact h_step'.reachable.trans ih
        refine ⟨ι ⟨r, hr_mem⟩, fun ⟨b, hb⟩ => ?_⟩
        rcases Finset.mem_insert.mp hb with hbz | hbS₀
        · subst b
          apply SimpleGraph.Adj.reachable
          change G.Adj r z
          exact G.symm ((hadj r (Finset.mem_insert_of_mem hr)).mpr rfl)
        · obtain ⟨p⟩ := hS₀_sub.2.preconnected ⟨r, hr_mem⟩ ⟨b, hbS₀⟩
          exact hι_walk _ _ p
  have leaf_ext_moments : ∀ (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) (z r : Fin n),
      z ∉ U → r ∈ U → (∀ v ∈ insert z U, G.Adj z v ↔ v = r) →
      rootedCount G (insert z U) z = rootedCount G U r + 1 ∧
      rootedOrderSum G (insert z U) z = rootedOrderSum G U r + rootedCount G U r + 1 ∧
      (subtreesIn G (insert z U)).card = (subtreesIn G U).card + rootedCount G U r + 1 ∧
      (∑ S ∈ subtreesIn G (insert z U), S.card) =
        (∑ S ∈ subtreesIn G U, S.card) + rootedOrderSum G U r + rootedCount G U r + 1 ∧
      rootedCount G (insert z U) r = 2 * rootedCount G U r ∧
      rootedOrderSum G (insert z U) r = 2 * rootedOrderSum G U r + rootedCount G U r := by
    intro G U z r hz hr hadj
    have h_ext : ∀ S₀ ⊆ U, IsSubtree G (insert z S₀) ↔ S₀ = ∅ ∨ (IsSubtree G S₀ ∧ r ∈ S₀) :=
      fun S₀ hS₀ => isSubtree_insert_leaf_iff G U S₀ z r hz hr hadj hS₀
    have hzr : z ≠ r := fun h => hz (h ▸ hr)
    have h_mem_rooted : ∀ W r' S, S ∈ rootedSubtreesIn G W r' ↔ IsSubtree G S ∧ S ⊆ W ∧ r' ∈ S := by
      intro W r' S
      simp [rootedSubtreesIn, subtrees]
    have h_mem_subtreesIn : ∀ W S, S ∈ subtreesIn G W ↔ IsSubtree G S ∧ S ⊆ W := by
      intro W S
      simp [subtreesIn, subtrees]
    have h_rooted_z : rootedSubtreesIn G (insert z U) z =
        insert ({z} : Finset (Fin n)) ((rootedSubtreesIn G U r).image (insert z)) := by
      ext S
      simp only [Finset.mem_insert, Finset.mem_image, h_mem_rooted]
      constructor
      · rintro ⟨hS_sub, hS_U, hzS⟩
        let S₀ := S.erase z
        have hS₀_U : S₀ ⊆ U := by
          intro v hv
          rcases Finset.mem_insert.mp (hS_U (Finset.mem_of_mem_erase hv)) with rfl | hvU
          · exact False.elim ((Finset.mem_erase.mp hv).1 rfl)
          · exact hvU
        have h_ins : insert z S₀ = S := Finset.insert_erase hzS
        have hS_iff := (h_ext S₀ hS₀_U).mp (h_ins.symm ▸ hS_sub)
        rcases hS_iff with h_emp | ⟨hS₀_tree, hrS₀⟩
        · left
          rw [← h_ins, h_emp, Finset.insert_empty]
        · right
          exact ⟨S₀, ⟨hS₀_tree, hS₀_U, hrS₀⟩, h_ins⟩
      · rintro (rfl | ⟨S₀, ⟨hS₀_tree, hS₀_U, hrS₀⟩, rfl⟩)
        · have h_emp : IsSubtree G (insert z ∅) := (h_ext ∅ (Finset.empty_subset U)).mpr (Or.inl rfl)
          simpa using h_emp
        · refine ⟨(h_ext S₀ hS₀_U).mpr (Or.inr ⟨hS₀_tree, hrS₀⟩),
            Finset.insert_subset_insert z hS₀_U, Finset.mem_insert_self z S₀⟩
    have h_notMem_img : ({z} : Finset (Fin n)) ∉ (rootedSubtreesIn G U r).image (insert z) := by
      simp only [Finset.mem_image, not_exists, not_and]
      intro S₀ hS₀ h_eq
      have hrS₀ : r ∈ S₀ := ((h_mem_rooted U r S₀).mp hS₀).2.2
      have hrz : r ∈ ({z} : Finset (Fin n)) := h_eq ▸ Finset.mem_insert_of_mem hrS₀
      exact hzr (Finset.mem_singleton.mp hrz).symm
    have h_inj : Set.InjOn (insert z) (rootedSubtreesIn G U r : Set (Finset (Fin n))) := by
      intro S₁ hS₁ S₂ hS₂ h_eq
      have hz₁ : z ∉ S₁ := fun h => hz (((h_mem_rooted U r S₁).mp hS₁).2.1 h)
      have hz₂ : z ∉ S₂ := fun h => hz (((h_mem_rooted U r S₂).mp hS₂).2.1 h)
      have := congrArg (fun S : Finset (Fin n) => S.erase z) h_eq
      simpa [Finset.erase_insert hz₁, Finset.erase_insert hz₂] using this
    have h_rc_z : rootedCount G (insert z U) z = rootedCount G U r + 1 := by
      change (rootedSubtreesIn G (insert z U) z).card = (rootedSubtreesIn G U r).card + 1
      rw [h_rooted_z, Finset.card_insert_of_notMem h_notMem_img, Finset.card_image_of_injOn h_inj]
    have h_sum_img : ∑ S ∈ (rootedSubtreesIn G U r).image (insert z), S.card =
        rootedOrderSum G U r + rootedCount G U r := by
      rw [Finset.sum_image h_inj]
      have h_congr : ∑ S₀ ∈ rootedSubtreesIn G U r, (insert z S₀).card =
          ∑ S₀ ∈ rootedSubtreesIn G U r, (S₀.card + 1) := by
        refine Finset.sum_congr rfl (fun S₀ hS₀ => ?_)
        have hzS₀ : z ∉ S₀ := fun h => hz (((h_mem_rooted U r S₀).mp hS₀).2.1 h)
        exact Finset.card_insert_of_notMem hzS₀
      rw [h_congr, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
      rfl
    have h_ros_z : rootedOrderSum G (insert z U) z =
        rootedOrderSum G U r + rootedCount G U r + 1 := by
      change ∑ S ∈ rootedSubtreesIn G (insert z U) z, S.card =
        rootedOrderSum G U r + rootedCount G U r + 1
      rw [h_rooted_z, Finset.sum_insert h_notMem_img, Finset.card_singleton, h_sum_img]
      omega
    have h_subtrees_union : subtreesIn G (insert z U) =
        subtreesIn G U ∪ rootedSubtreesIn G (insert z U) z := by
      ext S
      simp only [Finset.mem_union, h_mem_subtreesIn, h_mem_rooted]
      constructor
      · rintro ⟨hS_tree, hS_sub⟩
        by_cases hzS : z ∈ S
        · exact Or.inr ⟨hS_tree, hS_sub, hzS⟩
        · left
          refine ⟨hS_tree, fun v hv => ?_⟩
          rcases Finset.mem_insert.mp (hS_sub hv) with rfl | hvU
          · exact False.elim (hzS hv)
          · exact hvU
      · rintro (⟨hS_tree, hS_U⟩ | ⟨hS_tree, hS_sub, _⟩)
        · exact ⟨hS_tree, Finset.Subset.trans hS_U (Finset.subset_insert z U)⟩
        · exact ⟨hS_tree, hS_sub⟩
    have h_subtrees_disj : Disjoint (subtreesIn G U) (rootedSubtreesIn G (insert z U) z) := by
      rw [Finset.disjoint_left]
      intro S hS₁ hS₂
      have hS_U : S ⊆ U := ((h_mem_subtreesIn U S).mp hS₁).2
      exact hz (hS_U ((h_mem_rooted (insert z U) z S).mp hS₂).2.2)
    have h_sc_z : (subtreesIn G (insert z U)).card =
        (subtreesIn G U).card + rootedCount G U r + 1 := by
      rw [h_subtrees_union, Finset.card_union_of_disjoint h_subtrees_disj]
      change (subtreesIn G U).card + rootedCount G (insert z U) z = _
      rw [h_rc_z]
      omega
    have h_sos_z : (∑ S ∈ subtreesIn G (insert z U), S.card) =
        (∑ S ∈ subtreesIn G U, S.card) + rootedOrderSum G U r + rootedCount G U r + 1 := by
      rw [h_subtrees_union, Finset.sum_union h_subtrees_disj]
      change (∑ S ∈ subtreesIn G U, S.card) + rootedOrderSum G (insert z U) z = _
      rw [h_ros_z]
      omega
    have h_rooted_r : rootedSubtreesIn G (insert z U) r =
        rootedSubtreesIn G U r ∪ (rootedSubtreesIn G U r).image (insert z) := by
      ext S
      simp only [Finset.mem_union, Finset.mem_image, h_mem_rooted]
      constructor
      · rintro ⟨hS_tree, hS_sub, hrS⟩
        by_cases hzS : z ∈ S
        · right
          let S₀ := S.erase z
          have hS₀_U : S₀ ⊆ U := by
            intro v hv
            rcases Finset.mem_insert.mp (hS_sub (Finset.mem_of_mem_erase hv)) with rfl | hvU
            · exact False.elim ((Finset.mem_erase.mp hv).1 rfl)
            · exact hvU
          have h_ins : insert z S₀ = S := Finset.insert_erase hzS
          have hrS₀ : r ∈ S₀ := Finset.mem_erase.mpr ⟨hzr.symm, hrS⟩
          have hS_iff := (h_ext S₀ hS₀_U).mp (h_ins.symm ▸ hS_tree)
          rcases hS_iff with h_emp | ⟨hS₀_tree, _⟩
          · simp [h_emp] at hrS₀
          · exact ⟨S₀, ⟨hS₀_tree, hS₀_U, hrS₀⟩, h_ins⟩
        · left
          refine ⟨hS_tree, fun v hv => ?_, hrS⟩
          rcases Finset.mem_insert.mp (hS_sub hv) with rfl | hvU
          · exact False.elim (hzS hv)
          · exact hvU
      · rintro (⟨hS_tree, hS_U, hrS⟩ | ⟨S₀, ⟨hS₀_tree, hS₀_U, hrS₀⟩, rfl⟩)
        · exact ⟨hS_tree, Finset.Subset.trans hS_U (Finset.subset_insert z U), hrS⟩
        · exact ⟨(h_ext S₀ hS₀_U).mpr (Or.inr ⟨hS₀_tree, hrS₀⟩),
            Finset.insert_subset_insert z hS₀_U, Finset.mem_insert_of_mem hrS₀⟩
    have h_rooted_r_disj : Disjoint (rootedSubtreesIn G U r)
        ((rootedSubtreesIn G U r).image (insert z)) := by
      rw [Finset.disjoint_left]
      intro S hS₁ hS₂
      have hS_U : S ⊆ U := ((h_mem_rooted U r S).mp hS₁).2.1
      rcases Finset.mem_image.mp hS₂ with ⟨S₀, _, rfl⟩
      exact hz (hS_U (Finset.mem_insert_self z S₀))
    have h_rc_r : rootedCount G (insert z U) r = 2 * rootedCount G U r := by
      change (rootedSubtreesIn G (insert z U) r).card = 2 * (rootedSubtreesIn G U r).card
      rw [h_rooted_r, Finset.card_union_of_disjoint h_rooted_r_disj, Finset.card_image_of_injOn h_inj]
      omega
    have h_ros_r : rootedOrderSum G (insert z U) r =
        2 * rootedOrderSum G U r + rootedCount G U r := by
      change ∑ S ∈ rootedSubtreesIn G (insert z U) r, S.card =
        2 * rootedOrderSum G U r + rootedCount G U r
      rw [h_rooted_r, Finset.sum_union h_rooted_r_disj, h_sum_img]
      change rootedOrderSum G U r + (rootedOrderSum G U r + rootedCount G U r) = _
      omega
    exact ⟨h_rc_z, h_ros_z, h_sc_z, h_sos_z, h_rc_r, h_ros_r⟩
  have reattachLeaf_subtreesIn_eq : ∀ (G : SimpleGraph (Fin n)) (x w r : Fin n) (hxw : x ≠ w) (U : Finset (Fin n)),
      x ∉ U →
      subtreesIn (reattachLeaf G x w hxw) U = subtreesIn G U ∧
      rootedCount (reattachLeaf G x w hxw) U r = rootedCount G U r ∧
      rootedOrderSum (reattachLeaf G x w hxw) U r = rootedOrderSum G U r := by
    intro G x w r hxw U hx
    let G' := reattachLeaf G x w hxw
    have h_induce : ∀ S : Finset (Fin n), S ⊆ U →
        G'.induce (S : Set (Fin n)) = G.induce (S : Set (Fin n)) := by
      intro S hS
      ext ⟨a, ha⟩ ⟨b, hb⟩
      have hax : a ≠ x := fun h => hx (h ▸ hS ha)
      have hbx : b ≠ x := fun h => hx (h ▸ hS hb)
      change G'.Adj a b ↔ G.Adj a b
      simp [G', reattachLeaf, hax, hbx]
    have h_sub : subtreesIn G' U = subtreesIn G U := by
      ext S
      simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
      refine and_congr_left (fun hSU => ?_)
      dsimp [IsSubtree]
      rw [h_induce S hSU]
    have h_rooted : rootedSubtreesIn G' U r = rootedSubtreesIn G U r := by
      ext S
      simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
      refine and_congr_left (fun hSU => ?_)
      dsimp [IsSubtree]
      rw [h_induce S hSU.1]
    refine ⟨h_sub, ?_, ?_⟩
    · dsimp [rootedCount]; rw [h_rooted]
    · dsimp [rootedOrderSum]; rw [h_rooted]
  have hxu : x ≠ u := T.ne_of_adj ((hx u).mpr rfl)
  have huw : u ≠ w := T.ne_of_adj ((hu w).mpr (Or.inr rfl))
  let U₁ : Finset (Fin n) := Finset.univ \ {x}
  have hu_notMem_H : u ∉ H := by simp [H]
  have hw_mem_H : w ∈ H := by simp [H, hxw.symm, huw.symm]
  have h_ins_u : insert u H = U₁ := by
    ext v
    simp only [H, U₁, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_singleton, not_or]
    constructor
    · rintro (rfl | ⟨hvx, _⟩)
      · exact hxu.symm
      · exact hvx
    · intro hvx
      by_cases hvu : v = u
      · exact Or.inl hvu
      · exact Or.inr ⟨hvx, hvu⟩
  have hx_notMem_U₁ : x ∉ U₁ := by simp [U₁]
  have hu_mem_U₁ : u ∈ U₁ := by simp [U₁, hxu.symm]
  have hw_mem_U₁ : w ∈ U₁ := by simp [U₁, hxw.symm]
  have h_ins_x : insert x U₁ = Finset.univ := by
    ext v
    simp [U₁]
  have hadj_u : ∀ v ∈ insert u H, T.Adj u v ↔ v = w := by
    intro v hv
    rw [h_ins_u] at hv
    have hvx : v ≠ x := by simpa [U₁] using hv
    rw [hu v]
    simp [hvx]
  have hadj_x_T : ∀ v ∈ insert x U₁, T.Adj x v ↔ v = u :=
    fun v _ => hx v
  have hadj_x_T' : ∀ v ∈ insert x U₁, T'.Adj x v ↔ v = w := by
    intro v _
    change (x ≠ x ∧ v ≠ x ∧ T.Adj x v) ∨ (x = x ∧ v = w) ∨ (x = w ∧ v = x) ↔ v = w
    simp [hxw]
  have h_univ_sub : ∀ G : SimpleGraph (Fin n), subtreesIn G (insert x U₁) = subtrees G := by
    intro G
    rw [h_ins_x]
    ext S
    simp [subtreesIn]
  obtain ⟨h_rc_u, h_ros_u, h_sc_u, h_sos_u, h_rc_w, h_ros_w⟩ :=
    leaf_ext_moments T H u w hu_notMem_H hw_mem_H hadj_u
  rw [h_ins_u] at h_rc_u h_ros_u h_sc_u h_sos_u h_rc_w h_ros_w
  obtain ⟨_, _, h_sc_T, h_sos_T, _, _⟩ :=
    leaf_ext_moments T U₁ x u hx_notMem_U₁ hu_mem_U₁ hadj_x_T
  rw [h_univ_sub T] at h_sc_T h_sos_T
  obtain ⟨_, _, h_sc_T', h_sos_T', _, _⟩ :=
    leaf_ext_moments T' U₁ x w hx_notMem_U₁ hw_mem_U₁ hadj_x_T'
  rw [h_univ_sub T'] at h_sc_T' h_sos_T'
  obtain ⟨h_eq_sub, h_eq_rc, h_eq_ros⟩ :=
    reattachLeaf_subtreesIn_eq T x w w hxw U₁ hx_notMem_U₁
  change (subtrees T).card = _ ∧ (∑ S ∈ subtrees T, S.card) = _ ∧
    (subtrees T').card = _ ∧ (∑ S ∈ subtrees T', S.card) = _
  rw [h_eq_sub, h_eq_rc] at h_sc_T'
  rw [h_eq_sub, h_eq_rc, h_eq_ros] at h_sos_T'
  refine ⟨by omega, by omega, by omega, by omega⟩

theorem rooted_local_global_ineq : ∀ {V : Type*} [Fintype V] (T : SimpleGraph V) (U : Finset V) (w : V),
    T.IsTree → IsSubtree T U → w ∈ U →
    rootedCount T U w * (∑ S ∈ subtreesIn T U, S.card) ≤
      rootedOrderSum T U w * (subtreesIn T U).card :=
by
  intro V _ T U₀ w₀ hT hU₀ hw₀
  classical
  have singleton_subtree_moments : ∀ (U : Finset V) (w : V),
      w ∈ U → U.card ≤ 1 →
      rootedCount T U w = 1 ∧
      rootedOrderSum T U w = 1 ∧
      (subtreesIn T U).card = 1 ∧
      (∑ S ∈ subtreesIn T U, S.card) = 1 := by
    intro U w hw hle
    have hU_eq : U = {w} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      refine ⟨hw, fun x hx => Finset.card_le_one.mp hle x hx w hw⟩
    subst hU_eq
    have hw_sub : IsSubtree T {w} := by
      refine ⟨Finset.singleton_nonempty w, ?_⟩
      have : Nonempty ↑(({w} : Finset V) : Set V) := ⟨⟨w, by simp⟩⟩
      refine ⟨?_⟩
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      have ha' : a = w := by simpa using ha
      have hb' : b = w := by simpa using hb
      have hab : (⟨a, ha⟩ : ↑(({w} : Finset V) : Set V)) = ⟨b, hb⟩ :=
        Subtype.ext (ha'.trans hb'.symm)
      rw [hab]
    have h_sub_eq : subtreesIn T {w} = {{w}} := by
      ext S
      simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h_ne, _⟩, h_sub⟩
        rcases Finset.subset_singleton_iff.mp h_sub with rfl | rfl
        · exact False.elim (Finset.not_nonempty_empty h_ne)
        · rfl
      · rintro rfl
        exact ⟨hw_sub, Finset.Subset.refl _⟩
    have h_root_eq : rootedSubtreesIn T {w} w = {{w}} := by
      ext S
      simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h_ne, _⟩, h_sub, _⟩
        rcases Finset.subset_singleton_iff.mp h_sub with rfl | rfl
        · exact False.elim (Finset.not_nonempty_empty h_ne)
        · rfl
      · rintro rfl
        exact ⟨hw_sub, Finset.Subset.refl _, Finset.mem_singleton_self w⟩
    simp [rootedCount, rootedOrderSum, h_sub_eq, h_root_eq]
  have isBridgeJoin_symm : ∀ {A B : Finset V} {w r_B : V},
      IsBridgeJoin T A B w r_B → IsBridgeJoin T B A r_B w := by
    intro A B w r_B hJ
    rcases hJ with ⟨h_disj, hw, hr_B, hadj, h_bridge⟩
    refine ⟨h_disj.symm, hr_B, hw, T.symm hadj, ?_⟩
    intro u hu v hv huv
    exact (h_bridge v hv u hu (T.symm huv)).symm
  have exists_walk_of_isSubtree : ∀ {S : Finset V},
      IsSubtree T S → ∀ {a b : V}, a ∈ S → b ∈ S →
      ∃ q : T.Walk a b, ∀ z ∈ q.support, z ∈ S := by
    intro S hS a b ha hb
    obtain ⟨q₀⟩ := hS.2.preconnected ⟨a, ha⟩ ⟨b, hb⟩
    suffices ∀ {u v : ↑(S : Set V)} (q : (T.induce (S : Set V)).Walk u v),
        ∃ q' : T.Walk u.1 v.1, ∀ z ∈ q'.support, z ∈ S from this q₀
    intro u v q
    induction q with
    | @nil u =>
      refine ⟨SimpleGraph.Walk.nil, ?_⟩
      intro z hz
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      rw [hz]
      exact Finset.mem_coe.mp u.2
    | @cons u c v hadj q' ih =>
      obtain ⟨q₁, hq₁⟩ := ih
      refine ⟨SimpleGraph.Walk.cons hadj q₁, ?_⟩
      intro z hz
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz'
      · exact Finset.mem_coe.mp u.2
      · exact hq₁ z hz'
  have bridge_walk_mem_edges : ∀ {A B : Finset V} {w r_B : V},
      IsBridgeJoin T A B w r_B → ∀ {a b : V} (q : T.Walk a b),
      (∀ z ∈ q.support, z ∈ A ∪ B) →
      ((a ∈ A ∧ b ∈ B) ∨ (a ∈ B ∧ b ∈ A)) →
      s(w, r_B) ∈ q.edges := by
    intro A B w r_B hJ a b q
    induction q with
    | nil =>
      intro _ h_ab
      rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact False.elim (Finset.disjoint_left.mp hJ.1 ha hb)
      · exact False.elim (Finset.disjoint_left.mp hJ.1 hb ha)
    | @cons a c b h_step q' ih =>
      intro h_supp h_ab
      have hc_mem : c ∈ A ∪ B := h_supp c (by
        simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.start_mem_support])
      have h_supp' : ∀ z ∈ q'.support, z ∈ A ∪ B := fun z hz =>
        h_supp z (by simp [SimpleGraph.Walk.support_cons, hz])
      rcases Finset.mem_union.mp hc_mem with hcA | hcB
      · rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ (ih h_supp' (Or.inl ⟨hcA, hb⟩))
        · obtain ⟨hcw, har⟩ := hJ.2.2.2.2 c hcA a ha (T.symm h_step)
          subst hcw har
          rw [SimpleGraph.Walk.edges_cons, Sym2.eq_swap]
          exact List.mem_cons_self
      · rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · obtain ⟨haw, hcr⟩ := hJ.2.2.2.2 a ha c hcB h_step
          subst haw hcr
          rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_self
        · rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ (ih h_supp' (Or.inr ⟨hcB, hb⟩))
  have bridge_path_support_left : ∀ {A B : Finset V} {w r_B : V},
      IsBridgeJoin T A B w r_B → ∀ {a b : V} (p : T.Walk a b), p.IsPath →
      (∀ z ∈ p.support, z ∈ A ∪ B) → a ∈ A → b ∈ A →
      ∀ z ∈ p.support, z ∈ A := by
    intro A B w r_B hJ a b p hp h_supp ha hb z hz
    rcases Finset.mem_union.mp (h_supp z hz) with hzA | hzB
    · exact hzA
    · exfalso
      let p₁ := p.takeUntil z hz
      let p₂ := p.dropUntil z hz
      have hp₁_supp : ∀ x ∈ p₁.support, x ∈ A ∪ B :=
        fun x hx => h_supp x (p.support_takeUntil_subset hz hx)
      have hp₂_supp : ∀ x ∈ p₂.support, x ∈ A ∪ B :=
        fun x hx => h_supp x (p.support_dropUntil_subset hz hx)
      have he₁ : s(w, r_B) ∈ p₁.edges :=
        bridge_walk_mem_edges hJ p₁ hp₁_supp (Or.inl ⟨ha, hzB⟩)
      have he₂ : s(w, r_B) ∈ p₂.edges :=
        bridge_walk_mem_edges hJ p₂ hp₂_supp (Or.inr ⟨hzB, hb⟩)
      have h_nodup : p.edges.Nodup := hp.isTrail.edges_nodup
      have h_edges : p₁.edges ++ p₂.edges = p.edges := by
        rw [← SimpleGraph.Walk.edges_append, p.take_spec hz]
      rw [← h_edges, List.nodup_append] at h_nodup
      exact h_nodup.2.2 s(w, r_B) he₁ s(w, r_B) he₂ rfl
  have subtree_exists_root_bridge_split : ∀ (U : Finset V) (w : V),
      IsSubtree T U → w ∈ U → 2 ≤ U.card →
      ∃ (A B : Finset V) (r_B : V),
        U = A ∪ B ∧ IsSubtree T A ∧ IsSubtree T B ∧ IsBridgeJoin T A B w r_B := by
    intro U w hU hw hge2
    obtain ⟨u, hu, huw⟩ := Finset.exists_mem_ne (by omega : 1 < U.card) w
    obtain ⟨p₀⟩ := hU.2.preconnected ⟨w, hw⟩ ⟨u, hu⟩
    have h_adj_exists : ∃ r_B ∈ U, T.Adj w r_B := by
      cases p₀ with
      | nil => exact False.elim (huw rfl)
      | @cons _ r _ hadj _ => exact ⟨r.1, r.2, hadj⟩
    obtain ⟨r_B, hr_B_U, hadj_wr⟩ := h_adj_exists
    let T₀ := T \ SimpleGraph.fromEdgeSet {s(w, r_B)}
    have h_bridge_wr : T.IsBridge s(w, r_B) :=
      SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.IsAcyclic hadj_wr
    have h_not_reach : ¬ T₀.Reachable w r_B :=
      (SimpleGraph.isBridge_iff.mp h_bridge_wr).2
    let A := U.filter (fun v => T₀.Reachable w v)
    let B := U \ A
    have hA_sub : A ⊆ U := Finset.filter_subset _ U
    have hU_eq : U = A ∪ B := (Finset.union_sdiff_of_subset hA_sub).symm
    have h_disj : Disjoint A B := Finset.disjoint_sdiff
    have hw_A : w ∈ A := Finset.mem_filter.mpr ⟨hw, SimpleGraph.Reachable.refl w⟩
    have hr_B : r_B ∈ B := by
      rw [Finset.mem_sdiff]
      refine ⟨hr_B_U, ?_⟩
      rw [Finset.mem_filter]
      rintro ⟨_, h_reach⟩
      exact h_not_reach h_reach
    have hJ : IsBridgeJoin T A B w r_B := by
      refine ⟨h_disj, hw_A, hr_B, hadj_wr, ?_⟩
      intro a ha b hb hab
      by_cases h_edge : s(a, b) = s(w, r_B)
      · rw [Sym2.eq_iff] at h_edge
        rcases h_edge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨rfl, rfl⟩
        · exact False.elim (Finset.disjoint_left.mp h_disj ha hr_B)
      · exfalso
        have hab₀ : T₀.Adj a b := by
          dsimp [T₀]
          rw [SimpleGraph.sdiff_adj, SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff]
          exact ⟨hab, fun ⟨h_eq, _⟩ => h_edge h_eq⟩
        have ha_reach : T₀.Reachable w a := (Finset.mem_filter.mp ha).2
        have hb_reach : T₀.Reachable w b := ha_reach.trans hab₀.reachable
        have hb_A : b ∈ A := Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hb).1, hb_reach⟩
        exact (Finset.mem_sdiff.mp hb).2 hb_A
    have hA_subtree : IsSubtree T A := by
      refine ⟨⟨w, hw_A⟩, ?_⟩
      have : Nonempty ↑(A : Set V) := ⟨⟨w, hw_A⟩⟩
      refine ⟨?_⟩
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      have hxU : x ∈ U := hA_sub hx
      have hyU : y ∈ U := hA_sub hy
      obtain ⟨q, hq_supp⟩ := exists_walk_of_isSubtree hU hxU hyU
      let p : T.Walk x y := (q.toPath : T.Walk x y)
      have hp_path : p.IsPath := q.toPath.2
      have hp_supp : ∀ z ∈ p.support, z ∈ A ∪ B := by
        intro z hz
        rw [← hU_eq]
        exact hq_supp z (q.support_toPath_subset hz)
      have hp_A : ∀ z ∈ p.support, z ∈ (A : Set V) :=
        bridge_path_support_left hJ p hp_path hp_supp hx hy
      exact (p.induce (A : Set V) hp_A).reachable
    have hB_subtree : IsSubtree T B := by
      refine ⟨⟨r_B, hr_B⟩, ?_⟩
      have : Nonempty ↑(B : Set V) := ⟨⟨r_B, hr_B⟩⟩
      refine ⟨?_⟩
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      have hxU : x ∈ U := Finset.sdiff_subset hx
      have hyU : y ∈ U := Finset.sdiff_subset hy
      obtain ⟨q, hq_supp⟩ := exists_walk_of_isSubtree hU hxU hyU
      let p : T.Walk x y := (q.toPath : T.Walk x y)
      have hp_path : p.IsPath := q.toPath.2
      have hp_supp : ∀ z ∈ p.support, z ∈ B ∪ A := by
        intro z hz
        rw [Finset.union_comm, ← hU_eq]
        exact hq_supp z (q.support_toPath_subset hz)
      have hp_B : ∀ z ∈ p.support, z ∈ (B : Set V) :=
        bridge_path_support_left (isBridgeJoin_symm hJ) p hp_path hp_supp hx hy
      exact (p.induce (B : Set V) hp_B).reachable
    exact ⟨A, B, r_B, hU_eq, hA_subtree, hB_subtree, hJ⟩
  have bridge_crossing_left : ∀ {A B S : Finset V} {w r_B : V},
      IsBridgeJoin T A B w r_B → S ⊆ A ∪ B →
      IsSubtree T S → (S ∩ A).Nonempty → (S ∩ B).Nonempty →
      S ∩ A ∈ rootedSubtreesIn T A w := by
    intro A B S w r_B hJ hS_sub hS hSA hSB
    obtain ⟨a₀, ha₀⟩ := hSA
    obtain ⟨b₀, hb₀⟩ := hSB
    have ha₀S : a₀ ∈ S := (Finset.mem_inter.mp ha₀).1
    have ha₀A : a₀ ∈ A := (Finset.mem_inter.mp ha₀).2
    have hb₀S : b₀ ∈ S := (Finset.mem_inter.mp hb₀).1
    have hb₀B : b₀ ∈ B := (Finset.mem_inter.mp hb₀).2
    obtain ⟨q, hq_supp⟩ := exists_walk_of_isSubtree hS ha₀S hb₀S
    have hq_AB : ∀ z ∈ q.support, z ∈ A ∪ B := fun z hz => hS_sub (hq_supp z hz)
    have he : s(w, r_B) ∈ q.edges :=
      bridge_walk_mem_edges hJ q hq_AB (Or.inl ⟨ha₀A, hb₀B⟩)
    have hwS : w ∈ S := hq_supp w (q.fst_mem_support_of_mem_edges he)
    have hwSA : w ∈ S ∩ A := Finset.mem_inter.mpr ⟨hwS, hJ.2.1⟩
    have hSA_subtree : IsSubtree T (S ∩ A) := by
      refine ⟨⟨w, hwSA⟩, ?_⟩
      have : Nonempty ↑((S ∩ A : Finset V) : Set V) := ⟨⟨w, hwSA⟩⟩
      refine ⟨?_⟩
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      have hxS : x ∈ S := (Finset.mem_inter.mp hx).1
      have hxA : x ∈ A := (Finset.mem_inter.mp hx).2
      have hyS : y ∈ S := (Finset.mem_inter.mp hy).1
      have hyA : y ∈ A := (Finset.mem_inter.mp hy).2
      obtain ⟨q₁, hq₁_supp⟩ := exists_walk_of_isSubtree hS hxS hyS
      let p : T.Walk x y := (q₁.toPath : T.Walk x y)
      have hp_path : p.IsPath := q₁.toPath.2
      have hp_S : ∀ z ∈ p.support, z ∈ S := fun z hz => hq₁_supp z (q₁.support_toPath_subset hz)
      have hp_AB : ∀ z ∈ p.support, z ∈ A ∪ B := fun z hz => hS_sub (hp_S z hz)
      have hp_A : ∀ z ∈ p.support, z ∈ A :=
        bridge_path_support_left hJ p hp_path hp_AB hxA hyA
      have hp_SA : ∀ z ∈ p.support, z ∈ ((S ∩ A : Finset V) : Set V) :=
        fun z hz => Finset.mem_inter.mpr ⟨hp_S z hz, hp_A z hz⟩
      exact (p.induce ((S ∩ A : Finset V) : Set V) hp_SA).reachable
    simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hSA_subtree, Finset.inter_subset_right, hwSA⟩
  have bridge_union_isSubtree : ∀ {A B SA SB : Finset V} {w r_B : V},
      IsBridgeJoin T A B w r_B →
      SA ∈ rootedSubtreesIn T A w → SB ∈ rootedSubtreesIn T B r_B →
      IsSubtree T (SA ∪ SB) := by
    intro A B SA SB w r_B hJ hSA hSB
    simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hSA hSB
    rcases hSA with ⟨hSA_sub, _, hw_SA⟩
    rcases hSB with ⟨hSB_sub, _, hr_SB⟩
    have hw_U : w ∈ SA ∪ SB := Finset.mem_union_left SB hw_SA
    have hr_U : r_B ∈ SA ∪ SB := Finset.mem_union_right SA hr_SB
    refine ⟨⟨w, hw_U⟩, ?_⟩
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨w, hw_U⟩, ?_⟩
    rintro ⟨x, hx⟩
    rcases Finset.mem_union.mp hx with hxA | hxB
    · obtain ⟨q, hq⟩ := exists_walk_of_isSubtree hSA_sub hw_SA hxA
      have hq_U : ∀ z ∈ q.support, z ∈ ((SA ∪ SB : Finset V) : Set V) :=
        fun z hz => Finset.mem_union_left SB (hq z hz)
      exact (q.induce ((SA ∪ SB : Finset V) : Set V) hq_U).reachable
    · obtain ⟨q, hq⟩ := exists_walk_of_isSubtree hSB_sub hr_SB hxB
      have hq_U : ∀ z ∈ q.support, z ∈ ((SA ∪ SB : Finset V) : Set V) :=
        fun z hz => Finset.mem_union_right SA (hq z hz)
      have hadj_ind : (T.induce ((SA ∪ SB : Finset V) : Set V)).Adj ⟨w, hw_U⟩ ⟨r_B, hr_U⟩ :=
        hJ.2.2.2.1
      exact hadj_ind.reachable.trans (q.induce ((SA ∪ SB : Finset V) : Set V) hq_U).reachable
  have bridge_join_subtree_moments : ∀ (A B : Finset V) (w r_B : V),
      IsBridgeJoin T A B w r_B →
      rootedCount T (A ∪ B) w = rootedCount T A w * (1 + rootedCount T B r_B) ∧
      rootedOrderSum T (A ∪ B) w =
        rootedOrderSum T A w * (1 + rootedCount T B r_B) + rootedCount T A w * rootedOrderSum T B r_B ∧
      (subtreesIn T (A ∪ B)).card =
        (subtreesIn T A).card + (subtreesIn T B).card + rootedCount T A w * rootedCount T B r_B ∧
      (∑ S ∈ subtreesIn T (A ∪ B), S.card) =
        (∑ S ∈ subtreesIn T A, S.card) + (∑ S ∈ subtreesIn T B, S.card) +
          rootedOrderSum T A w * rootedCount T B r_B + rootedCount T A w * rootedOrderSum T B r_B := by
    intro A B w r_B hJ
    let RA_set := rootedSubtreesIn T A w
    let RB_set := rootedSubtreesIn T B r_B
    let φ : Finset V × Finset V → Finset V := fun p => p.1 ∪ p.2
    let M := (RA_set ×ˢ RB_set).image φ
    have h_inter_left : ∀ {X Y : Finset V}, X ⊆ A → Y ⊆ B → (X ∪ Y) ∩ A = X := by
      intro X Y hX hY
      ext z
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hzX | hzY, hzA⟩
        · exact hzX
        · exact False.elim (Finset.disjoint_left.mp hJ.1 hzA (hY hzY))
      · intro hzX
        exact ⟨Or.inl hzX, hX hzX⟩
    have h_inter_right : ∀ {X Y : Finset V}, X ⊆ A → Y ⊆ B → (X ∪ Y) ∩ B = Y := by
      intro X Y hX hY
      ext z
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hzX | hzY, hzB⟩
        · exact False.elim (Finset.disjoint_left.mp hJ.1 (hX hzX) hzB)
        · exact hzY
      · intro hzY
        exact ⟨Or.inr hzY, hY hzY⟩
    have h_inj : Set.InjOn φ ((RA_set ×ˢ RB_set : Finset (Finset V × Finset V)) : Set (Finset V × Finset V)) := by
      intro p₁ hp₁ p₂ hp₂ h_eq
      rcases Finset.mem_product.mp (Finset.mem_coe.mp hp₁) with ⟨hp₁A, hp₁B⟩
      rcases Finset.mem_product.mp (Finset.mem_coe.mp hp₂) with ⟨hp₂A, hp₂B⟩
      have h1A : p₁.1 ⊆ A := (Finset.mem_filter.mp hp₁A).2.1
      have h1B : p₁.2 ⊆ B := (Finset.mem_filter.mp hp₁B).2.1
      have h2A : p₂.1 ⊆ A := (Finset.mem_filter.mp hp₂A).2.1
      have h2B : p₂.2 ⊆ B := (Finset.mem_filter.mp hp₂B).2.1
      have h1 : p₁.1 = p₂.1 := by
        calc p₁.1 = (p₁.1 ∪ p₁.2) ∩ A := (h_inter_left h1A h1B).symm
          _ = (p₂.1 ∪ p₂.2) ∩ A := by rw [show p₁.1 ∪ p₁.2 = p₂.1 ∪ p₂.2 from h_eq]
          _ = p₂.1 := h_inter_left h2A h2B
      have h2 : p₁.2 = p₂.2 := by
        calc p₁.2 = (p₁.1 ∪ p₁.2) ∩ B := (h_inter_right h1A h1B).symm
          _ = (p₂.1 ∪ p₂.2) ∩ B := by rw [show p₁.1 ∪ p₁.2 = p₂.1 ∪ p₂.2 from h_eq]
          _ = p₂.2 := h_inter_right h2A h2B
      exact Prod.ext h1 h2
    have hM_card : M.card = rootedCount T A w * rootedCount T B r_B := by
      dsimp [M, RA_set, RB_set, rootedCount]
      rw [Finset.card_image_of_injOn h_inj, Finset.card_product]
    have hM_sum : ∑ S ∈ M, S.card =
        rootedOrderSum T A w * rootedCount T B r_B + rootedCount T A w * rootedOrderSum T B r_B := by
      dsimp [M]
      rw [Finset.sum_image h_inj, Finset.sum_product]
      have h_inner : ∀ x ∈ RA_set,
          ∑ y ∈ RB_set, (x ∪ y).card = x.card * RB_set.card + ∑ y ∈ RB_set, y.card := by
        intro x hx
        have hx_sub : x ⊆ A := (Finset.mem_filter.mp hx).2.1
        have h_congr : ∑ y ∈ RB_set, (x ∪ y).card = ∑ y ∈ RB_set, (x.card + y.card) := by
          refine Finset.sum_congr rfl fun y hy => ?_
          have hy_sub : y ⊆ B := (Finset.mem_filter.mp hy).2.1
          exact Finset.card_union_of_disjoint (Disjoint.mono hx_sub hy_sub hJ.1)
        rw [h_congr, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
      rw [Finset.sum_congr rfl h_inner, Finset.sum_add_distrib, ← Finset.sum_mul,
        Finset.sum_const, smul_eq_mul]
      rfl
    have h_mem_M : ∀ S : Finset V,
        S ∈ M ↔ S ∈ subtreesIn T (A ∪ B) ∧ (S ∩ A).Nonempty ∧ (S ∩ B).Nonempty := by
      intro S
      constructor
      · intro hS
        obtain ⟨⟨SA, SB⟩, hp, rfl⟩ := Finset.mem_image.mp hS
        rcases Finset.mem_product.mp hp with ⟨hSA, hSB⟩
        have hSA' := hSA
        have hSB' := hSB
        simp only [RA_set, RB_set, rootedSubtreesIn, subtrees, Finset.mem_filter,
          Finset.mem_univ, true_and] at hSA' hSB'
        have h_sub_AB : SA ∪ SB ⊆ A ∪ B := Finset.union_subset_union hSA'.2.1 hSB'.2.1
        have h_tree : IsSubtree T (SA ∪ SB) := bridge_union_isSubtree hJ hSA hSB
        have h_in_sub : SA ∪ SB ∈ subtreesIn T (A ∪ B) := by
          simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨h_tree, h_sub_AB⟩
        have h_ne_A : ((SA ∪ SB) ∩ A).Nonempty := by
          rw [h_inter_left hSA'.2.1 hSB'.2.1]
          exact ⟨w, hSA'.2.2⟩
        have h_ne_B : ((SA ∪ SB) ∩ B).Nonempty := by
          rw [h_inter_right hSA'.2.1 hSB'.2.1]
          exact ⟨r_B, hSB'.2.2⟩
        exact ⟨h_in_sub, h_ne_A, h_ne_B⟩
      · rintro ⟨hS_in, hSA_ne, hSB_ne⟩
        simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hS_in
        rcases hS_in with ⟨hS_tree, hS_sub⟩
        have hSA_mem : S ∩ A ∈ RA_set := bridge_crossing_left hJ hS_sub hS_tree hSA_ne hSB_ne
        have hS_sub' : S ⊆ B ∪ A := by simpa [Finset.union_comm] using hS_sub
        have hSB_mem : S ∩ B ∈ RB_set :=
          bridge_crossing_left (isBridgeJoin_symm hJ) hS_sub' hS_tree hSB_ne hSA_ne
        refine Finset.mem_image.mpr ⟨(S ∩ A, S ∩ B), Finset.mem_product.mpr ⟨hSA_mem, hSB_mem⟩, ?_⟩
        dsimp [φ]
        rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hS_sub]
    have h_sub_of_inter_empty_right : ∀ {S : Finset V}, S ⊆ A ∪ B → S ∩ B = ∅ → S ⊆ A := by
      intro S hS h_emp z hz
      rcases Finset.mem_union.mp (hS hz) with hzA | hzB
      · exact hzA
      · exfalso
        have : z ∈ (∅ : Finset V) := h_emp ▸ Finset.mem_inter.mpr ⟨hz, hzB⟩
        exact Finset.notMem_empty z this
    have h_sub_of_inter_empty_left : ∀ {S : Finset V}, S ⊆ A ∪ B → S ∩ A = ∅ → S ⊆ B := by
      intro S hS h_emp z hz
      rcases Finset.mem_union.mp (hS hz) with hzA | hzB
      · exfalso
        have : z ∈ (∅ : Finset V) := h_emp ▸ Finset.mem_inter.mpr ⟨hz, hzA⟩
        exact Finset.notMem_empty z this
      · exact hzB
    have h_root_disj : Disjoint RA_set M := by
      rw [Finset.disjoint_left]
      intro S hS_RA hS_M
      obtain ⟨_, _, b, hb⟩ := (h_mem_M S).mp hS_M
      have hS_A : S ⊆ A := (Finset.mem_filter.mp hS_RA).2.1
      exact Finset.disjoint_left.mp hJ.1 (hS_A (Finset.mem_inter.mp hb).1) (Finset.mem_inter.mp hb).2
    have h_root_part : rootedSubtreesIn T (A ∪ B) w = RA_set ∪ M := by
      ext S
      rw [Finset.mem_union, h_mem_M]
      constructor
      · intro hS
        simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hS
        rcases hS with ⟨hS_tree, hS_sub, hwS⟩
        rcases Finset.eq_empty_or_nonempty (S ∩ B) with h_emp | hSB_ne
        · left
          simp only [RA_set, rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hS_tree, h_sub_of_inter_empty_right hS_sub h_emp, hwS⟩
        · right
          have hS_in : S ∈ subtreesIn T (A ∪ B) := by
            simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hS_tree, hS_sub⟩
          exact ⟨hS_in, ⟨w, Finset.mem_inter.mpr ⟨hwS, hJ.2.1⟩⟩, hSB_ne⟩
      · rintro (hS_RA | ⟨hS_in, hSA_ne, hSB_ne⟩)
        · simp only [RA_set, rootedSubtreesIn, subtrees, Finset.mem_filter,
            Finset.mem_univ, true_and] at hS_RA ⊢
          exact ⟨hS_RA.1, Finset.Subset.trans hS_RA.2.1 Finset.subset_union_left, hS_RA.2.2⟩
        · simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hS_in
          have hSA_mem : S ∩ A ∈ RA_set :=
            bridge_crossing_left hJ hS_in.2 hS_in.1 hSA_ne hSB_ne
          have hw_SA : w ∈ S ∩ A := (Finset.mem_filter.mp hSA_mem).2.2
          simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hS_in.1, hS_in.2, (Finset.mem_inter.mp hw_SA).1⟩
    have h_sub_AB_disj : Disjoint (subtreesIn T A) (subtreesIn T B) := by
      rw [Finset.disjoint_left]
      intro S hSA hSB
      simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hSA hSB
      obtain ⟨x, hx⟩ := hSA.1.1
      exact Finset.disjoint_left.mp hJ.1 (hSA.2 hx) (hSB.2 hx)
    have h_sub_M_disj : Disjoint (subtreesIn T A ∪ subtreesIn T B) M := by
      rw [Finset.disjoint_left]
      intro S hS_AB hS_M
      obtain ⟨_, ⟨a, ha⟩, ⟨b, hb⟩⟩ := (h_mem_M S).mp hS_M
      rcases Finset.mem_union.mp hS_AB with hSA | hSB
      · have hS_A : S ⊆ A := (Finset.mem_filter.mp hSA).2
        exact Finset.disjoint_left.mp hJ.1 (hS_A (Finset.mem_inter.mp hb).1) (Finset.mem_inter.mp hb).2
      · have hS_B : S ⊆ B := (Finset.mem_filter.mp hSB).2
        exact Finset.disjoint_left.mp hJ.1 (Finset.mem_inter.mp ha).2 (hS_B (Finset.mem_inter.mp ha).1)
    have h_sub_part : subtreesIn T (A ∪ B) = (subtreesIn T A ∪ subtreesIn T B) ∪ M := by
      ext S
      rw [Finset.mem_union, Finset.mem_union, h_mem_M]
      constructor
      · intro hS
        have hS' := hS
        simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hS'
        rcases hS' with ⟨hS_tree, hS_sub⟩
        rcases Finset.eq_empty_or_nonempty (S ∩ B) with hB_emp | hSB_ne
        · left; left
          simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hS_tree, h_sub_of_inter_empty_right hS_sub hB_emp⟩
        · rcases Finset.eq_empty_or_nonempty (S ∩ A) with hA_emp | hSA_ne
          · left; right
            simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hS_tree, h_sub_of_inter_empty_left hS_sub hA_emp⟩
          · right
            exact ⟨hS, hSA_ne, hSB_ne⟩
      · rintro ((hSA | hSB) | ⟨hS, _, _⟩)
        · simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hSA ⊢
          exact ⟨hSA.1, Finset.Subset.trans hSA.2 Finset.subset_union_left⟩
        · simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hSB ⊢
          exact ⟨hSB.1, Finset.Subset.trans hSB.2 Finset.subset_union_right⟩
        · exact hS
    have h_eq1 : rootedCount T (A ∪ B) w = rootedCount T A w * (1 + rootedCount T B r_B) := by
      dsimp [rootedCount]
      rw [h_root_part, Finset.card_union_of_disjoint h_root_disj, hM_card]
      dsimp [RA_set, rootedCount]
      ring
    have h_eq2 : rootedOrderSum T (A ∪ B) w =
        rootedOrderSum T A w * (1 + rootedCount T B r_B) + rootedCount T A w * rootedOrderSum T B r_B := by
      dsimp [rootedOrderSum]
      rw [h_root_part, Finset.sum_union h_root_disj, hM_sum]
      dsimp [RA_set, rootedOrderSum]
      ring
    have h_eq3 : (subtreesIn T (A ∪ B)).card =
        (subtreesIn T A).card + (subtreesIn T B).card + rootedCount T A w * rootedCount T B r_B := by
      rw [h_sub_part, Finset.card_union_of_disjoint h_sub_M_disj,
        Finset.card_union_of_disjoint h_sub_AB_disj, hM_card]
    have h_eq4 : (∑ S ∈ subtreesIn T (A ∪ B), S.card) =
        (∑ S ∈ subtreesIn T A, S.card) + (∑ S ∈ subtreesIn T B, S.card) +
          rootedOrderSum T A w * rootedCount T B r_B + rootedCount T A w * rootedOrderSum T B r_B := by
      rw [h_sub_part, Finset.sum_union h_sub_M_disj,
        Finset.sum_union h_sub_AB_disj, hM_sum]
      ring
    exact ⟨h_eq1, h_eq2, h_eq3, h_eq4⟩
  have bridge_join_moment_ineq_step : ∀ (sA tA NA RA sB tB NB RB : ℕ),
      1 ≤ sA → sA ≤ tA → sA ≤ NA → 2 * tA ≤ sA * (sA + 1) → sA * RA ≤ tA * NA →
      1 ≤ sB → sB ≤ tB → sB ≤ NB → 2 * tB ≤ sB * (sB + 1) → sB * RB ≤ tB * NB →
      let s := sA * (1 + sB)
      let t := tA * (1 + sB) + sA * tB
      let N := NA + NB + sA * sB
      let R := RA + RB + tA * sB + sA * tB
      1 ≤ s ∧ s ≤ t ∧ s ≤ N ∧ 2 * t ≤ s * (s + 1) ∧ s * R ≤ t * N := by
    intro sA tA NA RA sB tB NB RB hsA1 hstA hsNA h2tA hlgA hsB1 hstB hsNB h2tB hlgB
    dsimp only
    refine ⟨by nlinarith, by nlinarith, by nlinarith, ?_, ?_⟩
    · zify at hsA1 hstA hsNA h2tA hlgA hsB1 hstB hsNB h2tB hlgB ⊢
      have h_id1 :
          (sA : ℤ) * (1 + sB) * ((sA : ℤ) * (1 + sB) + 1) -
            2 * ((tA : ℤ) * (1 + sB) + (sA : ℤ) * tB) =
          (1 + (sB : ℤ)) * ((sA : ℤ) * (sA + 1) - 2 * tA) +
          (sA : ℤ) * ((sB : ℤ) * (sB + 1) - 2 * tB) +
          (sA : ℤ) * (1 + sB) * (sA - 1) * sB := by ring
      have h1 : 0 ≤ (1 + (sB : ℤ)) * ((sA : ℤ) * (sA + 1) - 2 * tA) :=
        mul_nonneg (by omega) (by omega)
      have h2 : 0 ≤ (sA : ℤ) * ((sB : ℤ) * (sB + 1) - 2 * tB) :=
        mul_nonneg (by omega) (by omega)
      have h3 : 0 ≤ (sA : ℤ) * (1 + sB) * (sA - 1) * sB :=
        mul_nonneg (mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)) (by omega)
      linarith
    · zify at hsA1 hstA hsNA h2tA hlgA hsB1 hstB hsNB h2tB hlgB ⊢
      have h_id2 :
          (sB : ℤ) * (((tA : ℤ) * (1 + sB) + (sA : ℤ) * tB) * ((NA : ℤ) + NB + (sA : ℤ) * sB) -
            (sA : ℤ) * (1 + sB) * ((RA : ℤ) + RB + (tA : ℤ) * sB + (sA : ℤ) * tB)) =
          (sB : ℤ) * (1 + sB) * ((tA : ℤ) * NA - (sA : ℤ) * RA) +
          (sA : ℤ) * (1 + sB) * ((tB : ℤ) * NB - (sB : ℤ) * RB) +
          (sA : ℤ) * sB * tB * ((NA : ℤ) - sA) +
          (NB : ℤ) * (((tA : ℤ) - sA) * sB * (1 + sB) +
            (sA : ℤ) * ((sB : ℤ) * (1 + sB) - tB)) := by ring
      have htB_le : (tB : ℤ) ≤ (sB : ℤ) * (1 + sB) := by linarith
      have h1 : 0 ≤ (sB : ℤ) * (1 + sB) * ((tA : ℤ) * NA - (sA : ℤ) * RA) :=
        mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)
      have h2 : 0 ≤ (sA : ℤ) * (1 + sB) * ((tB : ℤ) * NB - (sB : ℤ) * RB) :=
        mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)
      have h3 : 0 ≤ (sA : ℤ) * sB * tB * ((NA : ℤ) - sA) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)) (by omega)
      have h4 : 0 ≤ (NB : ℤ) * (((tA : ℤ) - sA) * sB * (1 + sB) +
          (sA : ℤ) * ((sB : ℤ) * (1 + sB) - tB)) := by
        refine mul_nonneg (by omega) (add_nonneg ?_ ?_)
        · exact mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)
        · exact mul_nonneg (by omega) (by omega)
      have h_prod : 0 ≤ (sB : ℤ) * (((tA : ℤ) * (1 + sB) + (sA : ℤ) * tB) * ((NA : ℤ) + NB + (sA : ℤ) * sB) -
          (sA : ℤ) * (1 + sB) * ((RA : ℤ) + RB + (tA : ℤ) * sB + (sA : ℤ) * tB)) := by
        linarith
      nlinarith
  have h_ind : ∀ (m : ℕ) (U : Finset V) (w : V),
      U.card = m → IsSubtree T U → w ∈ U →
      1 ≤ rootedCount T U w ∧
      rootedCount T U w ≤ rootedOrderSum T U w ∧
      rootedCount T U w ≤ (subtreesIn T U).card ∧
      2 * rootedOrderSum T U w ≤ rootedCount T U w * (rootedCount T U w + 1) ∧
      rootedCount T U w * (∑ S ∈ subtreesIn T U, S.card) ≤
        rootedOrderSum T U w * (subtreesIn T U).card := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro U w hm hU hw
      by_cases hle : U.card ≤ 1
      · obtain ⟨hs, ht, hN, hR⟩ := singleton_subtree_moments U w hw hle
        rw [hs, ht, hN, hR]
        omega
      · push_neg at hle
        obtain ⟨A, B, r_B, hU_eq, hA_sub, hB_sub, hJ⟩ :=
          subtree_exists_root_bridge_split U w hU hw hle
        have hA_pos : 0 < A.card := Finset.card_pos.mpr ⟨w, hJ.2.1⟩
        have hB_pos : 0 < B.card := Finset.card_pos.mpr ⟨r_B, hJ.2.2.1⟩
        have hU_card : U.card = A.card + B.card := by
          rw [hU_eq, Finset.card_union_of_disjoint hJ.1]
        have hA_lt : A.card < m := by omega
        have hB_lt : B.card < m := by omega
        obtain ⟨hsA1, hstA, hsNA, h2tA, hlgA⟩ := ih A.card hA_lt A w rfl hA_sub hJ.2.1
        obtain ⟨hsB1, hstB, hsNB, h2tB, hlgB⟩ := ih B.card hB_lt B r_B rfl hB_sub hJ.2.2.1
        obtain ⟨h_s, h_t, h_N, h_R⟩ := bridge_join_subtree_moments A B w r_B hJ
        rw [hU_eq, h_s, h_t, h_N, h_R]
        exact bridge_join_moment_ineq_step
          (rootedCount T A w) (rootedOrderSum T A w) (subtreesIn T A).card (∑ S ∈ subtreesIn T A, S.card)
          (rootedCount T B r_B) (rootedOrderSum T B r_B) (subtreesIn T B).card (∑ S ∈ subtreesIn T B, S.card)
          hsA1 hstA hsNA h2tA hlgA hsB1 hstB hsNB h2tB hlgB
  exact (h_ind U₀.card U₀ w₀ rfl hU₀ hw₀).2.2.2.2

theorem leaf_deg_two_improves : ∀ (n : ℕ) (hn : 1 ≤ n) (T : SimpleGraph (Fin n)),
    T.IsTree → HasLeafAtDegTwo T →
    ∃ T' : SimpleGraph (Fin n), T'.IsTree ∧ meanSubtreeOrder T < meanSubtreeOrder T' :=
by
  intro n _hn T hT h_leaf
  rcases h_leaf with ⟨hn4, x, u, w, hxw, hx, hu⟩
  let T' := reattachLeaf T x w hxw
  refine ⟨T', reattachLeaf_isTree T x u w hxw hT hx, ?_⟩
  let H : Finset (Fin n) := Finset.univ \ ({x, u} : Finset (Fin n))
  obtain ⟨hH, hw, hS2, htS, hSN⟩ := leaf_shift_host_bounds n T x u w hn4 hT hxw hx hu
  obtain ⟨hNT, hRT, hNT', hRT'⟩ := leaf_shift_subtree_moments n T x u w hxw hT hx hu
  have h_lg := rooted_local_global_ineq T H w hT hH hw
  dsimp only [meanSubtreeOrder]
  have hNT_pos : (0 : ℚ) < (subtreeCount T : ℚ) := by
    rw [hNT]
    positivity
  have hNT'_pos : (0 : ℚ) < (subtreeCount T' : ℚ) := by
    rw [hNT']
    positivity
  rw [div_lt_div_iff₀ hNT_pos hNT'_pos]
  have hS2_q : (2 : ℚ) ≤ (rootedCount T H w : ℚ) := by exact_mod_cast hS2
  have htS_q : (rootedCount T H w : ℚ) + 1 ≤ (rootedOrderSum T H w : ℚ) := by exact_mod_cast htS
  have hSN_q : (rootedCount T H w : ℚ) ≤ ((subtreesIn T H).card : ℚ) := by exact_mod_cast hSN
  have h_lg_q : (rootedCount T H w : ℚ) * ((∑ S ∈ subtreesIn T H, S.card : ℕ) : ℚ) ≤
      (rootedOrderSum T H w : ℚ) * ((subtreesIn T H).card : ℚ) := by exact_mod_cast h_lg
  have hNT_q : (subtreeCount T : ℚ) = ((subtreesIn T H).card : ℚ) + 2 * (rootedCount T H w : ℚ) + 3 := by
    exact_mod_cast hNT
  have hRT_q : (subtreeOrderSum T : ℚ) = ((∑ S ∈ subtreesIn T H, S.card : ℕ) : ℚ) +
      2 * (rootedOrderSum T H w : ℚ) + 3 * (rootedCount T H w : ℚ) + 4 := by
    exact_mod_cast hRT
  have hNT'_q : (subtreeCount T' : ℚ) = ((subtreesIn T H).card : ℚ) + 3 * (rootedCount T H w : ℚ) + 2 := by
    exact_mod_cast hNT'
  have hRT'_q : (subtreeOrderSum T' : ℚ) = ((∑ S ∈ subtreesIn T H, S.card : ℕ) : ℚ) +
      3 * (rootedOrderSum T H w : ℚ) + 4 * (rootedCount T H w : ℚ) + 2 := by
    exact_mod_cast hRT'
  rw [hNT_q, hRT_q, hNT'_q, hRT'_q]
  set S_q : ℚ := (rootedCount T H w : ℚ)
  set t_q : ℚ := (rootedOrderSum T H w : ℚ)
  set N_q : ℚ := ((subtreesIn T H).card : ℚ)
  set R_q : ℚ := ((∑ S ∈ subtreesIn T H, S.card : ℕ) : ℚ)
  have h_id : S_q * (((R_q + 3 * t_q + 4 * S_q + 2) * (N_q + 2 * S_q + 3)) -
      ((R_q + 2 * t_q + 3 * S_q + 4) * (N_q + 3 * S_q + 2))) =
      (S_q - 1) * (t_q * N_q - S_q * R_q) +
      (t_q + S_q * (S_q - 2)) * (N_q - S_q) +
      S_q * (6 * t_q - 4 * S_q - 2) := by ring
  have h1 : 0 ≤ (S_q - 1) * (t_q * N_q - S_q * R_q) :=
    mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ (t_q + S_q * (S_q - 2)) * (N_q - S_q) := by
    have : 0 ≤ S_q * (S_q - 2) := mul_nonneg (by linarith) (by linarith)
    exact mul_nonneg (by linarith) (by linarith)
  have h3 : 0 < S_q * (6 * t_q - 4 * S_q - 2) :=
    mul_pos (by linarith) (by linarith)
  nlinarith

theorem double_broom_suffix_moments : ∀ (n m p q : ℕ) (G : SimpleGraph (Fin n))
    (H L_p L_q : Finset (Fin n)) (w₀ : Fin n) (v : Fin (m + 1) → Fin n),
    G.IsTree → IsDoubleBroomSuffix G m p q H L_p L_q w₀ v →
    (subtreeCount G : ℚ) =
      doubleBroomCount (subtreesIn G H).card (rootedCount G H w₀) m p q ∧
    (subtreeOrderSum G : ℚ) =
      doubleBroomOrderSum (∑ S ∈ subtreesIn G H, S.card) (rootedCount G H w₀)
        (rootedOrderSum G H w₀) m p q :=
by
  intro n m p q G H L_p L_q w₀ v _hG hDB
  have isSubtree_insert_leaf_iff : ∀ (U S₀ : Finset (Fin n)) (z r : Fin n),
      z ∉ U → r ∈ U → (∀ y ∈ insert z U, G.Adj z y ↔ y = r) → S₀ ⊆ U →
      (IsSubtree G (insert z S₀) ↔ S₀ = ∅ ∨ (IsSubtree G S₀ ∧ r ∈ S₀)) := by
    intro U S₀ z r hz hr hadj hS₀
    have hzr : z ≠ r := fun h => hz (h ▸ hr)
    have hzS₀ : z ∉ S₀ := fun h => hz (hS₀ h)
    rcases S₀.eq_empty_or_nonempty with rfl | hS₀_ne
    · simp only [Finset.insert_empty, true_or, iff_true]
      refine ⟨Finset.singleton_nonempty z, ?_⟩
      rw [SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨⟨z, by simp⟩, fun ⟨w, hw⟩ => ?_⟩
      have hwz : w = z := by simpa using hw
      subst hwz
      exact SimpleGraph.Reachable.rfl
    · simp only [hS₀_ne.ne_empty, false_or]
      let S : Finset (Fin n) := insert z S₀
      change IsSubtree G S ↔ IsSubtree G S₀ ∧ r ∈ S₀
      constructor
      · intro hS
        have hr_mem : r ∈ S₀ := by
          obtain ⟨a, ha⟩ := hS₀_ne
          have h_walk : ∀ (u w : ↑(S : Set (Fin n))) (pw : (G.induce (S : Set (Fin n))).Walk u w),
              u.1 = z → w.1 ∈ S₀ → r ∈ S₀ := by
            intro u w pw huz hwS₀
            cases pw with
            | nil =>
              exact False.elim (hzS₀ (huz ▸ hwS₀))
            | @cons _ b _ hadj_step _ =>
              have hb_mem : b.1 ∈ insert z S₀ := b.2
              have hb_U : b.1 ∈ insert z U := Finset.insert_subset_insert z hS₀ hb_mem
              have hbr : b.1 = r := (hadj b.1 hb_U).mp (huz ▸ hadj_step)
              rcases Finset.mem_insert.mp hb_mem with hbz | hbS₀
              · exact False.elim (hzr (hbz.symm.trans hbr))
              · exact hbr ▸ hbS₀
          obtain ⟨pw⟩ := hS.2.preconnected
            ⟨z, Finset.mem_coe.mpr (Finset.mem_insert_self z S₀)⟩
            ⟨a, Finset.mem_coe.mpr (Finset.mem_insert_of_mem ha)⟩
          exact h_walk _ _ pw rfl ha
        refine ⟨⟨hS₀_ne, ?_⟩, hr_mem⟩
        rw [SimpleGraph.connected_iff_exists_forall_reachable]
        let φ : ↑(S : Set (Fin n)) → ↑(S₀ : Set (Fin n)) := fun x =>
          ⟨if x.1 = z then r else x.1, by
            by_cases hx : x.1 = z
            · simp [hx, hr_mem]
            · simp only [hx, ↓reduceIte, Finset.mem_coe]
              rcases Finset.mem_insert.mp x.2 with hxz | h
              · exact False.elim (hx hxz)
              · exact h⟩
        have hφ_mem : ∀ (a : Fin n) (ha : a ∈ S₀),
            φ ⟨a, Finset.mem_coe.mpr (Finset.mem_insert_of_mem ha)⟩ = ⟨a, ha⟩ := by
          intro a ha
          have haz : a ≠ z := fun h => hzS₀ (h ▸ ha)
          ext
          simp [φ, haz]
        have hφ_adj : ∀ x y : ↑(S : Set (Fin n)),
            (G.induce (S : Set (Fin n))).Adj x y →
            (G.induce (S₀ : Set (Fin n))).Reachable (φ x) (φ y) := by
          intro x y hxy
          change G.Adj x.1 y.1 at hxy
          by_cases hx : x.1 = z
          · have hy_U : y.1 ∈ insert z U := Finset.insert_subset_insert z hS₀ y.2
            have hyr : y.1 = r := (hadj y.1 hy_U).mp (hx ▸ hxy)
            have hφ_eq : φ x = φ y := by
              ext
              simp [φ, hx, hyr]
            rw [hφ_eq]
          · by_cases hy : y.1 = z
            · have hx_U : x.1 ∈ insert z U := Finset.insert_subset_insert z hS₀ x.2
              have hxr : x.1 = r := (hadj x.1 hx_U).mp (hy ▸ G.symm hxy)
              have hφ_eq : φ x = φ y := by
                ext
                simp [φ, hy, hxr]
              rw [hφ_eq]
            · apply SimpleGraph.Adj.reachable
              change G.Adj (φ x).1 (φ y).1
              simp [φ, hx, hy, hxy]
        have hφ_walk : ∀ (x y : ↑(S : Set (Fin n)))
            (pw : (G.induce (S : Set (Fin n))).Walk x y),
            (G.induce (S₀ : Set (Fin n))).Reachable (φ x) (φ y) := by
          intro x y pw
          induction pw with
          | nil => exact SimpleGraph.Reachable.rfl
          | cons h_step _ ih => exact (hφ_adj _ _ h_step).trans ih
        refine ⟨⟨r, hr_mem⟩, fun ⟨b, hb⟩ => ?_⟩
        obtain ⟨pw⟩ := hS.2.preconnected
          ⟨r, Finset.mem_coe.mpr (Finset.mem_insert_of_mem hr_mem)⟩
          ⟨b, Finset.mem_coe.mpr (Finset.mem_insert_of_mem hb)⟩
        have h_reach := hφ_walk _ _ pw
        rwa [hφ_mem r hr_mem, hφ_mem b hb] at h_reach
      · rintro ⟨hS₀_sub, hr_mem⟩
        refine ⟨Finset.insert_nonempty z S₀, ?_⟩
        rw [SimpleGraph.connected_iff_exists_forall_reachable]
        let ι : ↑(S₀ : Set (Fin n)) → ↑(S : Set (Fin n)) :=
          fun x => ⟨x.1, Finset.mem_coe.mpr (Finset.mem_insert_of_mem x.2)⟩
        have hι_walk : ∀ (x y : ↑(S₀ : Set (Fin n))) (pw : (G.induce (S₀ : Set (Fin n))).Walk x y),
            (G.induce (S : Set (Fin n))).Reachable (ι x) (ι y) := by
          intro x y pw
          induction pw with
          | nil => exact SimpleGraph.Reachable.rfl
          | cons h_step _ ih =>
            have h_step' : (G.induce (S : Set (Fin n))).Adj (ι _) (ι _) := h_step
            exact h_step'.reachable.trans ih
        refine ⟨ι ⟨r, hr_mem⟩, fun ⟨b, hb⟩ => ?_⟩
        rcases Finset.mem_insert.mp hb with hbz | hbS₀
        · subst b
          apply SimpleGraph.Adj.reachable
          change G.Adj r z
          exact G.symm ((hadj r (Finset.mem_insert_of_mem hr)).mpr rfl)
        · obtain ⟨pw⟩ := hS₀_sub.2.preconnected ⟨r, hr_mem⟩ ⟨b, hbS₀⟩
          exact hι_walk _ _ pw
  have leaf_ext_moments_Q : ∀ (U : Finset (Fin n)) (z r : Fin n),
      z ∉ U → r ∈ U → (∀ y ∈ insert z U, G.Adj z y ↔ y = r) →
      (rootedCount G (insert z U) z : ℚ) = (rootedCount G U r : ℚ) + 1 ∧
      (rootedOrderSum G (insert z U) z : ℚ) =
        (rootedOrderSum G U r : ℚ) + (rootedCount G U r : ℚ) + 1 ∧
      ((subtreesIn G (insert z U)).card : ℚ) =
        ((subtreesIn G U).card : ℚ) + (rootedCount G U r : ℚ) + 1 ∧
      ((∑ S ∈ subtreesIn G (insert z U), S.card : ℕ) : ℚ) =
        ((∑ S ∈ subtreesIn G U, S.card : ℕ) : ℚ) +
        (rootedOrderSum G U r : ℚ) + (rootedCount G U r : ℚ) + 1 ∧
      (rootedCount G (insert z U) r : ℚ) = 2 * (rootedCount G U r : ℚ) ∧
      (rootedOrderSum G (insert z U) r : ℚ) =
        2 * (rootedOrderSum G U r : ℚ) + (rootedCount G U r : ℚ) := by
    intro U z r hz hr hadj
    have h_ext : ∀ S₀ ⊆ U, IsSubtree G (insert z S₀) ↔ S₀ = ∅ ∨ (IsSubtree G S₀ ∧ r ∈ S₀) :=
      fun S₀ hS₀ => isSubtree_insert_leaf_iff U S₀ z r hz hr hadj hS₀
    have hzr : z ≠ r := fun h => hz (h ▸ hr)
    have h_mem_rooted : ∀ W r' S, S ∈ rootedSubtreesIn G W r' ↔ IsSubtree G S ∧ S ⊆ W ∧ r' ∈ S := by
      intro W r' S
      simp [rootedSubtreesIn, subtrees]
    have h_mem_subtreesIn : ∀ W S, S ∈ subtreesIn G W ↔ IsSubtree G S ∧ S ⊆ W := by
      intro W S
      simp [subtreesIn, subtrees]
    have h_rooted_z : rootedSubtreesIn G (insert z U) z =
        insert ({z} : Finset (Fin n)) ((rootedSubtreesIn G U r).image (insert z)) := by
      ext S
      simp only [Finset.mem_insert, Finset.mem_image, h_mem_rooted]
      constructor
      · rintro ⟨hS_sub, hS_U, hzS⟩
        let S₀ := S.erase z
        have hS₀_U : S₀ ⊆ U := by
          intro w hw
          rcases Finset.mem_insert.mp (hS_U (Finset.mem_of_mem_erase hw)) with rfl | hwU
          · exact False.elim ((Finset.mem_erase.mp hw).1 rfl)
          · exact hwU
        have h_ins : insert z S₀ = S := Finset.insert_erase hzS
        have hS_iff := (h_ext S₀ hS₀_U).mp (h_ins.symm ▸ hS_sub)
        rcases hS_iff with h_emp | ⟨hS₀_tree, hrS₀⟩
        · left
          rw [← h_ins, h_emp, Finset.insert_empty]
        · right
          exact ⟨S₀, ⟨hS₀_tree, hS₀_U, hrS₀⟩, h_ins⟩
      · rintro (rfl | ⟨S₀, ⟨hS₀_tree, hS₀_U, hrS₀⟩, rfl⟩)
        · have h_emp : IsSubtree G (insert z ∅) := (h_ext ∅ (Finset.empty_subset U)).mpr (Or.inl rfl)
          simpa using h_emp
        · refine ⟨(h_ext S₀ hS₀_U).mpr (Or.inr ⟨hS₀_tree, hrS₀⟩),
            Finset.insert_subset_insert z hS₀_U, Finset.mem_insert_self z S₀⟩
    have h_notMem_img : ({z} : Finset (Fin n)) ∉ (rootedSubtreesIn G U r).image (insert z) := by
      simp only [Finset.mem_image, not_exists, not_and]
      intro S₀ hS₀ h_eq
      have hrS₀ : r ∈ S₀ := ((h_mem_rooted U r S₀).mp hS₀).2.2
      have hrz : r ∈ ({z} : Finset (Fin n)) := h_eq ▸ Finset.mem_insert_of_mem hrS₀
      exact hzr (Finset.mem_singleton.mp hrz).symm
    have h_inj : Set.InjOn (insert z) (rootedSubtreesIn G U r : Set (Finset (Fin n))) := by
      intro S₁ hS₁ S₂ hS₂ h_eq
      have hz₁ : z ∉ S₁ := fun h => hz (((h_mem_rooted U r S₁).mp hS₁).2.1 h)
      have hz₂ : z ∉ S₂ := fun h => hz (((h_mem_rooted U r S₂).mp hS₂).2.1 h)
      have := congrArg (fun S : Finset (Fin n) => S.erase z) h_eq
      simpa [Finset.erase_insert hz₁, Finset.erase_insert hz₂] using this
    have h_rc_z : rootedCount G (insert z U) z = rootedCount G U r + 1 := by
      change (rootedSubtreesIn G (insert z U) z).card = (rootedSubtreesIn G U r).card + 1
      rw [h_rooted_z, Finset.card_insert_of_notMem h_notMem_img, Finset.card_image_of_injOn h_inj]
    have h_sum_img : ∑ S ∈ (rootedSubtreesIn G U r).image (insert z), S.card =
        rootedOrderSum G U r + rootedCount G U r := by
      rw [Finset.sum_image h_inj]
      have h_congr : ∑ S₀ ∈ rootedSubtreesIn G U r, (insert z S₀).card =
          ∑ S₀ ∈ rootedSubtreesIn G U r, (S₀.card + 1) := by
        refine Finset.sum_congr rfl (fun S₀ hS₀ => ?_)
        have hzS₀ : z ∉ S₀ := fun h => hz (((h_mem_rooted U r S₀).mp hS₀).2.1 h)
        exact Finset.card_insert_of_notMem hzS₀
      rw [h_congr, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
      rfl
    have h_ros_z : rootedOrderSum G (insert z U) z =
        rootedOrderSum G U r + rootedCount G U r + 1 := by
      change ∑ S ∈ rootedSubtreesIn G (insert z U) z, S.card =
        rootedOrderSum G U r + rootedCount G U r + 1
      rw [h_rooted_z, Finset.sum_insert h_notMem_img, Finset.card_singleton, h_sum_img]
      omega
    have h_subtrees_union : subtreesIn G (insert z U) =
        subtreesIn G U ∪ rootedSubtreesIn G (insert z U) z := by
      ext S
      simp only [Finset.mem_union, h_mem_subtreesIn, h_mem_rooted]
      constructor
      · rintro ⟨hS_tree, hS_sub⟩
        by_cases hzS : z ∈ S
        · exact Or.inr ⟨hS_tree, hS_sub, hzS⟩
        · left
          refine ⟨hS_tree, fun w hw => ?_⟩
          rcases Finset.mem_insert.mp (hS_sub hw) with rfl | hwU
          · exact False.elim (hzS hw)
          · exact hwU
      · rintro (⟨hS_tree, hS_U⟩ | ⟨hS_tree, hS_sub, _⟩)
        · exact ⟨hS_tree, Finset.Subset.trans hS_U (Finset.subset_insert z U)⟩
        · exact ⟨hS_tree, hS_sub⟩
    have h_subtrees_disj : Disjoint (subtreesIn G U) (rootedSubtreesIn G (insert z U) z) := by
      rw [Finset.disjoint_left]
      intro S hS₁ hS₂
      have hS_U : S ⊆ U := ((h_mem_subtreesIn U S).mp hS₁).2
      exact hz (hS_U ((h_mem_rooted (insert z U) z S).mp hS₂).2.2)
    have h_sc_z : (subtreesIn G (insert z U)).card =
        (subtreesIn G U).card + rootedCount G U r + 1 := by
      rw [h_subtrees_union, Finset.card_union_of_disjoint h_subtrees_disj]
      change (subtreesIn G U).card + rootedCount G (insert z U) z = _
      rw [h_rc_z]
      omega
    have h_sos_z : (∑ S ∈ subtreesIn G (insert z U), S.card) =
        (∑ S ∈ subtreesIn G U, S.card) + rootedOrderSum G U r + rootedCount G U r + 1 := by
      rw [h_subtrees_union, Finset.sum_union h_subtrees_disj]
      change (∑ S ∈ subtreesIn G U, S.card) + rootedOrderSum G (insert z U) z = _
      rw [h_ros_z]
      omega
    have h_rooted_r : rootedSubtreesIn G (insert z U) r =
        rootedSubtreesIn G U r ∪ (rootedSubtreesIn G U r).image (insert z) := by
      ext S
      simp only [Finset.mem_union, Finset.mem_image, h_mem_rooted]
      constructor
      · rintro ⟨hS_tree, hS_sub, hrS⟩
        by_cases hzS : z ∈ S
        · right
          let S₀ := S.erase z
          have hS₀_U : S₀ ⊆ U := by
            intro w hw
            rcases Finset.mem_insert.mp (hS_sub (Finset.mem_of_mem_erase hw)) with rfl | hwU
            · exact False.elim ((Finset.mem_erase.mp hw).1 rfl)
            · exact hwU
          have h_ins : insert z S₀ = S := Finset.insert_erase hzS
          have hrS₀ : r ∈ S₀ := Finset.mem_erase.mpr ⟨hzr.symm, hrS⟩
          have hS_iff := (h_ext S₀ hS₀_U).mp (h_ins.symm ▸ hS_tree)
          rcases hS_iff with h_emp | ⟨hS₀_tree, _⟩
          · simp [h_emp] at hrS₀
          · exact ⟨S₀, ⟨hS₀_tree, hS₀_U, hrS₀⟩, h_ins⟩
        · left
          refine ⟨hS_tree, fun w hw => ?_, hrS⟩
          rcases Finset.mem_insert.mp (hS_sub hw) with rfl | hwU
          · exact False.elim (hzS hw)
          · exact hwU
      · rintro (⟨hS_tree, hS_U, hrS⟩ | ⟨S₀, ⟨hS₀_tree, hS₀_U, hrS₀⟩, rfl⟩)
        · exact ⟨hS_tree, Finset.Subset.trans hS_U (Finset.subset_insert z U), hrS⟩
        · exact ⟨(h_ext S₀ hS₀_U).mpr (Or.inr ⟨hS₀_tree, hrS₀⟩),
            Finset.insert_subset_insert z hS₀_U, Finset.mem_insert_of_mem hrS₀⟩
    have h_rooted_r_disj : Disjoint (rootedSubtreesIn G U r)
        ((rootedSubtreesIn G U r).image (insert z)) := by
      rw [Finset.disjoint_left]
      intro S hS₁ hS₂
      have hS_U : S ⊆ U := ((h_mem_rooted U r S).mp hS₁).2.1
      rcases Finset.mem_image.mp hS₂ with ⟨S₀, _, rfl⟩
      exact hz (hS_U (Finset.mem_insert_self z S₀))
    have h_rc_r : rootedCount G (insert z U) r = 2 * rootedCount G U r := by
      change (rootedSubtreesIn G (insert z U) r).card = 2 * (rootedSubtreesIn G U r).card
      rw [h_rooted_r, Finset.card_union_of_disjoint h_rooted_r_disj, Finset.card_image_of_injOn h_inj]
      omega
    have h_ros_r : rootedOrderSum G (insert z U) r =
        2 * rootedOrderSum G U r + rootedCount G U r := by
      change ∑ S ∈ rootedSubtreesIn G (insert z U) r, S.card =
        2 * rootedOrderSum G U r + rootedCount G U r
      rw [h_rooted_r, Finset.sum_union h_rooted_r_disj, h_sum_img]
      change rootedOrderSum G U r + (rootedOrderSum G U r + rootedCount G U r) = _
      omega
    refine ⟨by exact_mod_cast h_rc_z, by exact_mod_cast h_ros_z, by exact_mod_cast h_sc_z,
      by exact_mod_cast h_sos_z, by exact_mod_cast h_rc_r, by exact_mod_cast h_ros_r⟩
  have leaf_packet_union_moments : ∀ (U L : Finset (Fin n)) (r : Fin n),
      r ∈ U → Disjoint U L → IsLeafPacket G L r →
      (rootedCount G (U ∪ L) r : ℚ) = (2 : ℚ) ^ L.card * (rootedCount G U r : ℚ) ∧
      (rootedOrderSum G (U ∪ L) r : ℚ) =
        (2 : ℚ) ^ L.card * (rootedOrderSum G U r : ℚ) +
        (L.card : ℚ) * (2 : ℚ) ^ L.card / 2 * (rootedCount G U r : ℚ) ∧
      ((subtreesIn G (U ∪ L)).card : ℚ) =
        ((subtreesIn G U).card : ℚ) + (L.card : ℚ) +
        ((2 : ℚ) ^ L.card - 1) * (rootedCount G U r : ℚ) ∧
      ((∑ S ∈ subtreesIn G (U ∪ L), S.card : ℕ) : ℚ) =
        ((∑ S ∈ subtreesIn G U, S.card : ℕ) : ℚ) + (L.card : ℚ) +
        ((2 : ℚ) ^ L.card - 1) * (rootedOrderSum G U r : ℚ) +
        (L.card : ℚ) * (2 : ℚ) ^ L.card / 2 * (rootedCount G U r : ℚ) := by
    intro U L r hrU
    induction L using Finset.induction_on with
    | empty =>
      intro _ _
      simp only [Finset.union_empty, Finset.card_empty, Nat.cast_zero, pow_zero]
      exact ⟨by ring, by ring, by ring, by ring⟩
    | @insert x L₀ hx_L₀ ih =>
      intro hdisj hpkt
      have hx_U : x ∉ U := (Finset.disjoint_insert_right.mp hdisj).1
      have hdisj₀ : Disjoint U L₀ := (Finset.disjoint_insert_right.mp hdisj).2
      have hx_leaf : IsLeafIn G x r := hpkt x (Finset.mem_insert_self x L₀)
      have hpkt₀ : IsLeafPacket G L₀ r := fun y hy => hpkt y (Finset.mem_insert_of_mem hy)
      obtain ⟨ih_s, ih_t, ih_N, ih_R⟩ := ih hdisj₀ hpkt₀
      let U' := U ∪ L₀
      have hU_ins : U ∪ insert x L₀ = insert x U' := Finset.union_insert x U L₀
      have hx_U' : x ∉ U' := Finset.notMem_union.mpr ⟨hx_U, hx_L₀⟩
      have hr_U' : r ∈ U' := Finset.mem_union_left L₀ hrU
      have hadj_x : ∀ y ∈ insert x U', G.Adj x y ↔ y = r := fun y _ => hx_leaf y
      obtain ⟨_, _, h_N, h_R, h_s, h_t⟩ := leaf_ext_moments_Q U' x r hx_U' hr_U' hadj_x
      have hcard : ((insert x L₀).card : ℚ) = (L₀.card : ℚ) + 1 := by
        rw [Finset.card_insert_of_notMem hx_L₀, Nat.cast_add, Nat.cast_one]
      have hpow : (2 : ℚ) ^ (insert x L₀).card = (2 : ℚ) ^ L₀.card * 2 := by
        rw [Finset.card_insert_of_notMem hx_L₀, pow_succ]
      rw [hU_ins, hcard, hpow]
      change (rootedCount G (insert x U') r : ℚ) = _ ∧
        (rootedOrderSum G (insert x U') r : ℚ) = _ ∧
        ((subtreesIn G (insert x U')).card : ℚ) = _ ∧
        ((∑ S ∈ subtreesIn G (insert x U'), S.card : ℕ) : ℚ) = _
      rw [h_s, h_t, h_N, h_R]
      dsimp [U'] at ih_s ih_t ih_N ih_R ⊢
      rw [ih_s, ih_t, ih_N, ih_R]
      exact ⟨by ring, by ring, by ring, by ring⟩
  rcases hDB with ⟨h_inj, _hSub_H, hcard_p, hcard_q, hdisj_Hv, hdisj_Hp, hdisj_Hq,
    hdisj_vp, hdisj_vq, hdisj_pq, h_univ, h_bridge, h_spine, h_pkt_p, h_pkt_q⟩
  have hv_mem_img : ∀ i : Fin (m + 1), v i ∈ Finset.univ.image v :=
    fun i => Finset.mem_image_of_mem v (Finset.mem_univ i)
  have hv_mem_D : ∀ i : Fin (m + 1), v i ∈ (Finset.univ.image v) ∪ L_p ∪ L_q :=
    fun i => Finset.mem_union_left _ (Finset.mem_union_left _ (hv_mem_img i))
  
  let U₀ : Finset (Fin n) := insert (v 0) H
  have hv0_notMem_H : v 0 ∉ H := Finset.disjoint_right.mp hdisj_Hv (hv_mem_img 0)
  have hw0_mem_H : w₀ ∈ H := h_bridge.2.1
  have hadj_v0 : ∀ y ∈ insert (v 0) H, G.Adj (v 0) y ↔ y = w₀ := by
    intro y hy
    constructor
    · intro hadj
      have hy_ne : y ≠ v 0 := fun h => G.loopless (v 0) (h ▸ hadj)
      have hy_H : y ∈ H := by
        rcases Finset.mem_insert.mp hy with rfl | h
        · exact False.elim (hy_ne rfl)
        · exact h
      exact (h_bridge.2.2.2.2 y hy_H (v 0) (hv_mem_D 0) (G.symm hadj)).1
    · rintro rfl
      exact G.symm h_bridge.2.2.2.1
  obtain ⟨hU0_s, hU0_t, hU0_N, hU0_R, _, _⟩ :=
    leaf_ext_moments_Q H (v 0) w₀ hv0_notMem_H hw0_mem_H hadj_v0
  
  let W₀ : Finset (Fin n) := U₀ ∪ L_p
  have hv0_mem_U0 : v 0 ∈ U₀ := Finset.mem_insert_self (v 0) H
  have hdisj_U0_Lp : Disjoint U₀ L_p :=
    Finset.disjoint_insert_left.mpr
      ⟨Finset.disjoint_left.mp hdisj_vp (hv_mem_img 0), hdisj_Hp⟩
  obtain ⟨hW0_s, hW0_t, hW0_N, hW0_R⟩ :=
    leaf_packet_union_moments U₀ L_p (v 0) hv0_mem_U0 hdisj_U0_Lp h_pkt_p
  rw [hcard_p] at hW0_s hW0_t hW0_N hW0_R
  
  let W : ℕ → Finset (Fin n) := fun k =>
    H ∪ L_p ∪ (Finset.univ.filter (fun i : Fin (m + 1) => i.val ≤ k)).image v
  let s₀ : ℚ := rootedCount G W₀ (v 0)
  let t₀ : ℚ := rootedOrderSum G W₀ (v 0)
  let N₀ : ℚ := (subtreesIn G W₀).card
  let R₀ : ℚ := ((∑ S ∈ subtreesIn G W₀, S.card : ℕ) : ℚ)
  have h_spine_ind : ∀ (k : ℕ) (hk : k ≤ m),
      let v_k := v ⟨k, Nat.lt_succ_of_le hk⟩
      (rootedCount G (W k) v_k : ℚ) = s₀ + (k : ℚ) ∧
      (rootedOrderSum G (W k) v_k : ℚ) =
        t₀ + (k : ℚ) * s₀ + (k : ℚ) * ((k : ℚ) + 1) / 2 ∧
      ((subtreesIn G (W k)).card : ℚ) =
        N₀ + (k : ℚ) * s₀ + (k : ℚ) * ((k : ℚ) + 1) / 2 ∧
      ((∑ S ∈ subtreesIn G (W k), S.card : ℕ) : ℚ) =
        R₀ + (k : ℚ) * t₀ + (k : ℚ) * ((k : ℚ) + 1) / 2 * s₀ +
        (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) / 6 := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h_flt0 : Finset.univ.filter (fun i : Fin (m + 1) => i.val ≤ 0) = {0} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hi
          exact Fin.ext (by change i.val ≤ 0 at hi; change i.val = 0; omega)
        · rintro rfl
          exact le_rfl
      have hW0_eq : W 0 = W₀ := by
        dsimp [W, W₀, U₀]
        rw [h_flt0, Finset.image_singleton]
        ext x
        simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
        tauto
      have hv0_eq : v ⟨0, Nat.lt_succ_of_le hk⟩ = v 0 := rfl
      dsimp only
      rw [hW0_eq, hv0_eq, Nat.cast_zero]
      change s₀ = _ ∧ t₀ = _ ∧ N₀ = _ ∧ R₀ = _
      exact ⟨by ring, by ring, by ring, by ring⟩
    | succ k ih =>
      intro hk1
      have hk : k ≤ m := Nat.le_of_succ_le hk1
      obtain ⟨ih_s, ih_t, ih_N, ih_R⟩ := ih hk
      let i_k : Fin (m + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
      let i_k1 : Fin (m + 1) := ⟨k + 1, Nat.lt_succ_of_le hk1⟩
      have h_flt_succ : Finset.univ.filter (fun i : Fin (m + 1) => i.val ≤ k + 1) =
          insert i_k1 (Finset.univ.filter (fun i : Fin (m + 1) => i.val ≤ k)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro hi
          by_cases hik : i.val = k + 1
          · left; exact Fin.ext hik
          · right; omega
        · rintro (rfl | hi)
          · exact le_rfl
          · omega
      have hW_succ : W (k + 1) = insert (v i_k1) (W k) := by
        dsimp [W]
        rw [h_flt_succ, Finset.image_insert]
        ext x
        simp only [Finset.mem_union, Finset.mem_insert]
        tauto
      have hv_notMem_Wk : v i_k1 ∉ W k := by
        intro h_mem
        dsimp [W] at h_mem
        rcases Finset.mem_union.mp h_mem with h_HLp | h_img
        · rcases Finset.mem_union.mp h_HLp with h_H | h_Lp
          · exact Finset.disjoint_right.mp hdisj_Hv (hv_mem_img i_k1) h_H
          · exact Finset.disjoint_left.mp hdisj_vp (hv_mem_img i_k1) h_Lp
        · rcases Finset.mem_image.mp h_img with ⟨i, hi_flt, hvi⟩
          have hi_le : i.val ≤ k := (Finset.mem_filter.mp hi_flt).2
          have hi_eq : i = i_k1 := h_inj hvi
          have : i.val = k + 1 := congrArg Fin.val hi_eq
          omega
      have hvk_mem_Wk : v i_k ∈ W k := by
        dsimp [W]
        refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i_k, ?_, rfl⟩)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩
      have hadj_vk1 : ∀ y ∈ insert (v i_k1) (W k), G.Adj (v i_k1) y ↔ y = v i_k := by
        intro y hy_ins
        constructor
        · intro hadj
          have hy_ne : y ≠ v i_k1 := fun h => G.loopless _ (h ▸ hadj)
          have hy_Wk : y ∈ W k := by
            rcases Finset.mem_insert.mp hy_ins with rfl | h
            · exact False.elim (hy_ne rfl)
            · exact h
          dsimp [W] at hy_Wk
          rcases Finset.mem_union.mp hy_Wk with h_HLp | h_img
          · rcases Finset.mem_union.mp h_HLp with h_H | h_Lp
            · have h_br := h_bridge.2.2.2.2 y h_H (v i_k1) (hv_mem_D i_k1) (G.symm hadj)
              have hi0 : i_k1 = 0 := h_inj h_br.2
              have : k + 1 = 0 := congrArg Fin.val hi0
              omega
            · have hv_eq : v i_k1 = v 0 := (h_pkt_p y h_Lp (v i_k1)).mp (G.symm hadj)
              have hi0 : i_k1 = 0 := h_inj hv_eq
              have : k + 1 = 0 := congrArg Fin.val hi0
              omega
          · rcases Finset.mem_image.mp h_img with ⟨i, hi_flt, rfl⟩
            have hi_le : i.val ≤ k := (Finset.mem_filter.mp hi_flt).2
            have h_sp := (h_spine i_k1 i).mp hadj
            have hi_eq : i.val = k := by
              change (k + 1) + 1 = i.val ∨ i.val + 1 = k + 1 at h_sp
              omega
            congr 1
            exact Fin.ext hi_eq
        · rintro rfl
          exact (h_spine i_k1 i_k).mpr (Or.inr rfl)
      obtain ⟨h_s, h_t, h_N, h_R, _, _⟩ :=
        leaf_ext_moments_Q (W k) (v i_k1) (v i_k) hv_notMem_Wk hvk_mem_Wk hadj_vk1
      dsimp only
      rw [hW_succ]
      change (rootedCount G (insert (v i_k1) (W k)) (v i_k1) : ℚ) = _ ∧
        (rootedOrderSum G (insert (v i_k1) (W k)) (v i_k1) : ℚ) = _ ∧
        ((subtreesIn G (insert (v i_k1) (W k))).card : ℚ) = _ ∧
        ((∑ S ∈ subtreesIn G (insert (v i_k1) (W k)), S.card : ℕ) : ℚ) = _
      rw [h_s, h_t, h_N, h_R]
      dsimp [i_k] at ih_s ih_t ih_N ih_R ⊢
      rw [ih_s, ih_t, ih_N, ih_R, Nat.cast_add, Nat.cast_one]
      exact ⟨by ring, by ring, by ring, by ring⟩
  obtain ⟨hWm_s, hWm_t, hWm_N, hWm_R⟩ := h_spine_ind m le_rfl
  let W_m : Finset (Fin n) := H ∪ (Finset.univ.image v) ∪ L_p
  have hWm_eq : W m = W_m := by
    have h_flt_m : Finset.univ.filter (fun i : Fin (m + 1) => i.val ≤ m) = Finset.univ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact Nat.le_of_lt_succ i.isLt
    dsimp [W, W_m]
    rw [h_flt_m]
    ext x
    simp only [Finset.mem_union]
    tauto
  have hvm_eq : v ⟨m, Nat.lt_succ_of_le le_rfl⟩ = v (Fin.last m) := rfl
  rw [hWm_eq, hvm_eq] at hWm_s hWm_t
  rw [hWm_eq] at hWm_N hWm_R
  
  have hvm_mem_Wm : v (Fin.last m) ∈ W_m :=
    Finset.mem_union_left _ (Finset.mem_union_right _ (hv_mem_img (Fin.last m)))
  have hdisj_Wm_Lq : Disjoint W_m L_q :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr ⟨hdisj_Hq, hdisj_vq⟩, hdisj_pq⟩
  obtain ⟨_, _, hUniv_N, hUniv_R⟩ :=
    leaf_packet_union_moments W_m L_q (v (Fin.last m)) hvm_mem_Wm hdisj_Wm_Lq h_pkt_q
  have hWm_Lq : W_m ∪ L_q = Finset.univ := h_univ
  have h_subtrees_univ : subtreesIn G Finset.univ = subtrees G := by
    ext S
    simp [subtreesIn]
  rw [hWm_Lq, h_subtrees_univ, hcard_q] at hUniv_N hUniv_R
  change ((subtrees G).card : ℚ) = _ ∧ ((∑ S ∈ subtrees G, S.card : ℕ) : ℚ) = _
  rw [hUniv_N, hUniv_R, hWm_N, hWm_R, hWm_s, hWm_t]
  dsimp [s₀, t₀, N₀, R₀, doubleBroomCount, doubleBroomOrderSum]
  rw [hW0_N, hW0_R, hW0_s, hW0_t, hU0_N, hU0_R, hU0_s, hU0_t]
  exact ⟨by ring, by ring⟩

theorem shortened_double_broom_exists : ∀ (n ℓ a k : ℕ) (T : SimpleGraph (Fin n))
    (H L_a L_k : Finset (Fin n)) (w₀ : Fin n) (v : Fin (ℓ + 1) → Fin n),
    T.IsTree → 1 ≤ ℓ → IsDoubleBroomSuffix T ℓ a k H L_a L_k w₀ v →
    ∃ (T_short : SimpleGraph (Fin n)) (L' : Finset (Fin n)) (v' : Fin (ℓ - 1 + 1) → Fin n),
      T_short.IsTree ∧
      IsDoubleBroomSuffix T_short (ℓ - 1) a (k + 1) H L_a L' w₀ v' ∧
      subtreesIn T_short H = subtreesIn T H ∧
      rootedSubtreesIn T_short H w₀ = rootedSubtreesIn T H w₀ :=
by
  have h_reattachLeaf_isTree : ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (x u w : V) (hxw : x ≠ w),
      G.IsTree → IsLeafIn G x u → (reattachLeaf G x w hxw).IsTree := by
    intro V _ G x u w hxw hG hx
    classical
    have hG_conn : G.Connected := hG.isConnected
    have hG_acyc : G.IsAcyclic := hG.IsAcyclic
    have h_leaf_avoid : ∀ {H : SimpleGraph V} {x₀ u₀ : V}, IsLeafIn H x₀ u₀ →
        ∀ {a b : V} (p : H.Walk a b), p.IsPath → a ≠ x₀ → b ≠ x₀ → x₀ ∉ p.support := by
      intro H x₀ u₀ hx₀ a b p
      induction p with
      | nil =>
        intro _ ha _ hmem
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hmem
        exact ha hmem.symm
      | @cons a c b hac q ih =>
        intro hp ha hb
        rw [SimpleGraph.Walk.cons_isPath_iff] at hp
        rcases hp with ⟨hq, ha_not_mem⟩
        have hc : c ≠ x₀ := by
          intro hcx
          subst hcx
          cases q with
          | nil => exact hb rfl
          | @cons _ d _ hxd q' =>
            have ha_eq : a = u₀ := (hx₀ a).mp (H.symm hac)
            have hd_eq : d = u₀ := (hx₀ d).mp hxd
            have had : a = d := ha_eq.trans hd_eq.symm
            apply ha_not_mem
            rw [SimpleGraph.Walk.support_cons, had]
            exact List.mem_cons_of_mem _ q'.start_mem_support
        have hx_not_q : x₀ ∉ q.support := ih hq hc hb
        rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
        exact ⟨ha.symm, hx_not_q⟩
    have h_reach_transfer : ∀ {a b : V} (p : G.Walk a b),
        x ∉ p.support → (reattachLeaf G x w hxw).Reachable a b := by
      intro a b p
      induction p with
      | nil =>
        intro _
        exact SimpleGraph.Reachable.refl _
      | @cons a c b hac q ih =>
        intro h_not_mem
        rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at h_not_mem
        rcases h_not_mem with ⟨hxa, hx_not_q⟩
        have ha : a ≠ x := Ne.symm hxa
        have hc : c ≠ x := by
          intro hcx
          apply hx_not_q
          rw [← hcx]
          exact q.start_mem_support
        have hadj : (reattachLeaf G x w hxw).Adj a c := Or.inl ⟨ha, hc, hac⟩
        exact hadj.reachable.trans (ih hx_not_q)
    have h_conn : (reattachLeaf G x w hxw).Connected := by
      rw [SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨w, fun a => ?_⟩
      by_cases hax : a = x
      · rw [hax]
        have hadj : (reattachLeaf G x w hxw).Adj w x := Or.inr (Or.inr ⟨rfl, rfl⟩)
        exact hadj.reachable
      · obtain ⟨p, hp⟩ := (hG_conn.preconnected w a).exists_isPath
        have hx_not_p : x ∉ p.support := h_leaf_avoid hx p hp hxw.symm hax
        exact h_reach_transfer p hx_not_p
    let G' := reattachLeaf G x w hxw
    have h_leaf_G' : IsLeafIn G' x w := by
      intro v
      constructor
      · intro hadj
        rcases hadj with ⟨hxx, _, _⟩ | ⟨_, rfl⟩ | ⟨hxw_eq, _⟩
        · exact False.elim (hxx rfl)
        · rfl
        · exact False.elim (hxw hxw_eq)
      · intro hvw
        subst hvw
        exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    have h_edge_mem : ∀ {a b : V} (q : G'.Walk a b),
        a ≠ x → b = x → s(x, w) ∈ q.edges := by
      intro a b q
      induction q with
      | nil =>
        intro ha hb
        exact False.elim (ha hb)
      | @cons a c b hac q' ih =>
        intro ha hb
        by_cases hcx : c = x
        · subst hcx
          have haw : a = w := (h_leaf_G' a).mp (G'.symm hac)
          subst haw
          rw [SimpleGraph.Walk.edges_cons, Sym2.eq_swap]
          exact List.mem_cons_self
        · rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ (ih hcx hb)
    have h_acyc : G'.IsAcyclic := by
      intro v c hc
      have hx_not_c : x ∉ c.support := by
        cases c with
        | nil => exact False.elim hc.not_of_nil
        | @cons _ y _ hvy p =>
          have h_cons := (SimpleGraph.Walk.cons_isCycle_iff p hvy).mp hc
          rcases h_cons with ⟨hp, h_no_edge⟩
          by_cases hvx : v = x
          · subst v
            have hyw : y = w := (h_leaf_G' y).mp hvy
            subst y
            have h_in : s(x, w) ∈ p.edges := h_edge_mem p hxw.symm rfl
            exact False.elim (h_no_edge h_in)
          · by_cases hyx : y = x
            · subst y
              have hvw : v = w := (h_leaf_G' v).mp (G'.symm hvy)
              cases p with
              | nil => exact False.elim (hvx rfl)
              | @cons _ z _ hxz p' =>
                have hzv : z = v := ((h_leaf_G' z).mp hxz).trans hvw.symm
                subst z
                apply False.elim (h_no_edge _)
                rw [SimpleGraph.Walk.edges_cons, Sym2.eq_swap]
                exact List.mem_cons_self
            · have hx_not_p : x ∉ p.support := h_leaf_avoid h_leaf_G' p hp hyx hvx
              rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
              exact ⟨Ne.symm hvx, hx_not_p⟩
      have h_edges : ∀ e ∈ c.edges, e ∈ G.edgeSet := by
        intro e
        refine Sym2.ind (fun a b he => ?_) e
        have ha_mem : a ∈ c.support := c.fst_mem_support_of_mem_edges he
        have hb_mem : b ∈ c.support := c.snd_mem_support_of_mem_edges he
        have ha_ne : a ≠ x := fun h => hx_not_c (h ▸ ha_mem)
        have hb_ne : b ≠ x := fun h => hx_not_c (h ▸ hb_mem)
        have hadj' : G'.Adj a b := c.adj_of_mem_edges he
        rw [SimpleGraph.mem_edgeSet]
        rcases hadj' with ⟨_, _, hab⟩ | ⟨hax, _⟩ | ⟨_, hbx⟩
        · exact hab
        · exact False.elim (ha_ne hax)
        · exact False.elim (hb_ne hbx)
      exact hG_acyc (c.transfer G h_edges) (hc.transfer h_edges)
    exact ⟨h_conn, h_acyc⟩
  have h_relocatePacket_isTree : ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (S : Finset V) (u w : V) (hu : u ∉ S) (hw : w ∉ S),
      G.IsTree → IsLeafPacket G S u → (relocatePacket G S w hw).IsTree := by
    intro V _ _ G S u w hu hw hG hleaf
    induction S using Finset.induction_on with
    | empty =>
      have h_emp : relocatePacket G ∅ w hw = G := by
        ext a b
        simp [relocatePacket]
      rw [h_emp]
      exact hG
    | @insert x S hxS ih =>
      have hux : u ≠ x := fun h => hu (h ▸ Finset.mem_insert_self x S)
      have huS : u ∉ S := fun h => hu (Finset.mem_insert_of_mem h)
      have hxw : x ≠ w := fun h => hw (h ▸ Finset.mem_insert_self x S)
      have hwS : w ∉ S := fun h => hw (Finset.mem_insert_of_mem h)
      have hx_leaf : IsLeafIn G x u := hleaf x (Finset.mem_insert_self x S)
      have hleafS : IsLeafPacket G S u := fun y hy => hleaf y (Finset.mem_insert_of_mem hy)
      let G_S := relocatePacket G S w hwS
      have hG_S : G_S.IsTree := ih huS hwS hleafS
      have hx_leaf_S : IsLeafIn G_S x u := by
        intro y
        change ((x ∉ S ∧ y ∉ S ∧ G.Adj x y) ∨ (x ∈ S ∧ y = w) ∨ (x = w ∧ y ∈ S)) ↔ y = u
        constructor
        · rintro (⟨_, _, hxy⟩ | ⟨hx_in, _⟩ | ⟨hx_eq, _⟩)
          · exact (hx_leaf y).mp hxy
          · exact False.elim (hxS hx_in)
          · exact False.elim (hxw hx_eq)
        · intro hyu
          rw [hyu]
          exact Or.inl ⟨hxS, huS, (hx_leaf u).mpr rfl⟩
      have hTree_re : (reattachLeaf G_S x w hxw).IsTree :=
        h_reattachLeaf_isTree G_S x u w hxw hG_S hx_leaf_S
      have h_step_eq : relocatePacket G (insert x S) w hw = reattachLeaf G_S x w hxw := by
        ext a b
        change ((a ∉ insert x S ∧ b ∉ insert x S ∧ G.Adj a b) ∨
            (a ∈ insert x S ∧ b = w) ∨ (a = w ∧ b ∈ insert x S)) ↔
          ((a ≠ x ∧ b ≠ x ∧ ((a ∉ S ∧ b ∉ S ∧ G.Adj a b) ∨ (a ∈ S ∧ b = w) ∨ (a = w ∧ b ∈ S))) ∨
            (a = x ∧ b = w) ∨ (a = w ∧ b = x))
        simp only [Finset.mem_insert, not_or]
        constructor
        · rintro (⟨⟨hax, haS⟩, ⟨hbx, hbS⟩, hab⟩ | ⟨rfl | haS, rfl⟩ | ⟨rfl, rfl | hbS⟩)
          · exact Or.inl ⟨hax, hbx, Or.inl ⟨haS, hbS, hab⟩⟩
          · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
          · have hax : a ≠ x := fun h => hxS (h ▸ haS)
            exact Or.inl ⟨hax, hxw.symm, Or.inr (Or.inl ⟨haS, rfl⟩)⟩
          · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
          · have hbx : b ≠ x := fun h => hxS (h ▸ hbS)
            exact Or.inl ⟨hxw.symm, hbx, Or.inr (Or.inr ⟨rfl, hbS⟩)⟩
        · rintro (⟨hax, hbx, ⟨haS, hbS, hab⟩ | ⟨haS, rfl⟩ | ⟨rfl, hbS⟩⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact Or.inl ⟨⟨hax, haS⟩, ⟨hbx, hbS⟩, hab⟩
          · exact Or.inr (Or.inl ⟨Or.inr haS, rfl⟩)
          · exact Or.inr (Or.inr ⟨rfl, Or.inr hbS⟩)
          · exact Or.inr (Or.inl ⟨Or.inl rfl, rfl⟩)
          · exact Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩)
      rw [h_step_eq]
      exact hTree_re
  have h_induce_relocate : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
      (w : Fin n) (hw : w ∉ S) (H A : Finset (Fin n)),
      Disjoint H S → A ⊆ H →
      (relocatePacket G S w hw).induce (A : Set (Fin n)) = G.induce (A : Set (Fin n)) := by
    intro n G S w hw H A hHS hAH
    ext ⟨a, ha⟩ ⟨b, hb⟩
    have haS : a ∉ S := Finset.disjoint_left.mp hHS (hAH ha)
    have hbS : b ∉ S := Finset.disjoint_left.mp hHS (hAH hb)
    change (relocatePacket G S w hw).Adj a b ↔ G.Adj a b
    simp [relocatePacket, haS, hbS]
  have h_isSubtree_relocate : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
      (w : Fin n) (hw : w ∉ S) (H A : Finset (Fin n)),
      Disjoint H S → A ⊆ H →
      (IsSubtree (relocatePacket G S w hw) A ↔ IsSubtree G A) := by
    intro n G S w hw H A hHS hAH
    simp only [IsSubtree, h_induce_relocate G S w hw H A hHS hAH]
  have h_subtreesIn_relocate : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
      (w : Fin n) (hw : w ∉ S) (H : Finset (Fin n)),
      Disjoint H S →
      subtreesIn (relocatePacket G S w hw) H = subtreesIn G H := by
    intro n G S w hw H hHS
    ext A
    simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_congr_left (fun hAH => h_isSubtree_relocate G S w hw H A hHS hAH)
  have h_rootedSubtreesIn_relocate : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
      (w w₀ : Fin n) (hw : w ∉ S) (H : Finset (Fin n)),
      Disjoint H S →
      rootedSubtreesIn (relocatePacket G S w hw) H w₀ = rootedSubtreesIn G H w₀ := by
    intro n G S w w₀ hw H hHS
    ext A
    simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_congr_left (fun hAH => h_isSubtree_relocate G S w hw H A hHS hAH.1)
  intro n ℓ a k T H L_a L_k w₀ v hT hℓ hDB
  rcases hDB with ⟨hv_inj, hSub_H, hcard_a, hcard_k,
    hdisj_Hv, hdisj_Ha, hdisj_Hk, hdisj_va, hdisj_vk, hdisj_ak,
    h_univ, h_bridge, h_spine, h_pkt_a, h_pkt_k⟩
  let v' : Fin (ℓ - 1 + 1) → Fin n := fun i => v ⟨i.val, by omega⟩
  let v_last : Fin n := v (Fin.last ℓ)
  let i_pred : Fin (ℓ + 1) := ⟨(Fin.last (ℓ - 1)).val, by omega⟩
  let v_pred : Fin n := v' (Fin.last (ℓ - 1))
  have hv_pred_eq : v_pred = v i_pred := rfl
  let L' : Finset (Fin n) := insert v_last L_k
  have hv_mem_v : ∀ j : Fin (ℓ + 1), v j ∈ Finset.univ.image v :=
    fun j => Finset.mem_image_of_mem v (Finset.mem_univ j)
  have hv_not_Lk : ∀ j : Fin (ℓ + 1), v j ∉ L_k :=
    fun j => Finset.disjoint_left.mp hdisj_vk (hv_mem_v j)
  have hv_not_La : ∀ j : Fin (ℓ + 1), v j ∉ L_a :=
    fun j => Finset.disjoint_left.mp hdisj_va (hv_mem_v j)
  have hv_not_H : ∀ j : Fin (ℓ + 1), v j ∉ H :=
    fun j => Finset.disjoint_right.mp hdisj_Hv (hv_mem_v j)
  have hv_last_not_Lk : v_last ∉ L_k := hv_not_Lk (Fin.last ℓ)
  have hw_not_Lk : v_pred ∉ L_k := hv_not_Lk i_pred
  have hv_pred_not_H : v_pred ∉ H := hv_not_H i_pred
  have hv_pred_not_La : v_pred ∉ L_a := hv_not_La i_pred
  let T_short : SimpleGraph (Fin n) := relocatePacket T L_k v_pred hw_not_Lk
  have h_adj_out : ∀ {a b : Fin n}, a ∉ L_k → b ∉ L_k → (T_short.Adj a b ↔ T.Adj a b) := by
    intro a b ha hb
    simp [T_short, relocatePacket, ha, hb]
  have hT_short : T_short.IsTree :=
    h_relocatePacket_isTree T L_k v_last v_pred hv_last_not_Lk hw_not_Lk hT h_pkt_k
  have hSub_H_short : IsSubtree T_short H :=
    (h_isSubtree_relocate T L_k v_pred hw_not_Lk H H hdisj_Hk (Finset.Subset.refl H)).mpr hSub_H
  have hSub_short : subtreesIn T_short H = subtreesIn T H :=
    h_subtreesIn_relocate T L_k v_pred hw_not_Lk H hdisj_Hk
  have hRoot_short : rootedSubtreesIn T_short H w₀ = rootedSubtreesIn T H w₀ :=
    h_rootedSubtreesIn_relocate T L_k v_pred w₀ hw_not_Lk H hdisj_Hk
  have hv'_inj : Function.Injective v' := by
    intro i j hij
    have h_eq : (⟨i.val, by omega⟩ : Fin (ℓ + 1)) = ⟨j.val, by omega⟩ := hv_inj hij
    exact Fin.ext (Fin.mk.inj_iff.mp h_eq)
  have hv'0 : v' 0 = v 0 := by
    change v ⟨(0 : Fin (ℓ - 1 + 1)).val, _⟩ = v 0
    congr 1
  have h_mem_img_v' : ∀ x : Fin n, x ∈ Finset.univ.image v' ↔ ∃ j : Fin (ℓ + 1), j.val < ℓ ∧ v j = x := by
    intro x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨⟨i.val, by omega⟩, ?_, rfl⟩
      change i.val < ℓ
      have hi : i.val < ℓ - 1 + 1 := i.isLt
      omega
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j.val, by omega⟩, rfl⟩
  have hv_last_not_v' : v_last ∉ Finset.univ.image v' := by
    rw [h_mem_img_v']
    rintro ⟨j, hj, hj_eq⟩
    have hj_last : j = Fin.last ℓ := hv_inj hj_eq
    have hj_val : j.val = ℓ := by rw [hj_last, Fin.val_last]
    omega
  have h_img_v_eq : Finset.univ.image v = insert v_last (Finset.univ.image v') := by
    ext x
    simp only [Finset.mem_insert, h_mem_img_v', Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, rfl⟩
      have hj : j.val < ℓ + 1 := j.isLt
      by_cases hj_eq : j.val = ℓ
      · left
        have hj_last : j = Fin.last ℓ := by
          ext
          rw [Fin.val_last]
          exact hj_eq
        rw [hj_last]
      · right
        exact ⟨j, by omega, rfl⟩
    · rintro (rfl | ⟨j, _, rfl⟩)
      · exact ⟨Fin.last ℓ, rfl⟩
      · exact ⟨j, rfl⟩
  have h_img_v'_sub : Finset.univ.image v' ⊆ Finset.univ.image v := by
    rw [h_img_v_eq]
    exact Finset.subset_insert _ _
  have h_D_eq : (Finset.univ.image v') ∪ L_a ∪ L' = (Finset.univ.image v) ∪ L_a ∪ L_k := by
    ext x
    simp only [L', h_img_v_eq, Finset.mem_union, Finset.mem_insert]
    tauto
  have hcard_L' : L'.card = k + 1 := by
    rw [Finset.card_insert_of_notMem hv_last_not_Lk, hcard_k]
  have h_univ_short : H ∪ (Finset.univ.image v') ∪ L_a ∪ L' = Finset.univ := by
    calc H ∪ (Finset.univ.image v') ∪ L_a ∪ L'
      _ = H ∪ ((Finset.univ.image v') ∪ L_a ∪ L') := by simp only [Finset.union_assoc]
      _ = H ∪ ((Finset.univ.image v) ∪ L_a ∪ L_k) := by rw [h_D_eq]
      _ = H ∪ (Finset.univ.image v) ∪ L_a ∪ L_k := by simp only [Finset.union_assoc]
      _ = Finset.univ := h_univ
  have h_bridge_short : IsBridgeJoin T_short H ((Finset.univ.image v') ∪ L_a ∪ L') w₀ (v' 0) := by
    rw [h_D_eq, hv'0]
    rcases h_bridge with ⟨hdisj_HD, hw₀_H, hv0_D, hadj_w0_v0, huniq_bridge⟩
    refine ⟨hdisj_HD, hw₀_H, hv0_D, ?_, ?_⟩
    · have hw₀_not_Lk : w₀ ∉ L_k := Finset.disjoint_left.mp hdisj_Hk hw₀_H
      exact Or.inl ⟨hw₀_not_Lk, hv_not_Lk 0, hadj_w0_v0⟩
    · intro u hu y hy hadj_short
      have hu_not_Lk : u ∉ L_k := Finset.disjoint_left.mp hdisj_Hk hu
      have hu_ne_vpred : u ≠ v_pred := fun h => hv_pred_not_H (h ▸ hu)
      rcases hadj_short with ⟨_, _, hadj⟩ | ⟨hu_Lk, _⟩ | ⟨hu_eq, _⟩
      · exact huniq_bridge u hu y hy hadj
      · exact False.elim (hu_not_Lk hu_Lk)
      · exact False.elim (hu_ne_vpred hu_eq)
  have h_spine_short : ∀ i j : Fin (ℓ - 1 + 1),
      T_short.Adj (v' i) (v' j) ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
    intro i j
    have hvi_not_Lk : v' i ∉ L_k := hv_not_Lk ⟨i.val, by omega⟩
    have hvj_not_Lk : v' j ∉ L_k := hv_not_Lk ⟨j.val, by omega⟩
    rw [h_adj_out hvi_not_Lk hvj_not_Lk]
    exact h_spine ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
  have h_pkt_a_short : IsLeafPacket T_short L_a (v' 0) := by
    rw [hv'0]
    intro x hx y
    have hx_not_Lk : x ∉ L_k := Finset.disjoint_left.mp hdisj_ak hx
    have hx_ne_vpred : x ≠ v_pred := fun h => hv_pred_not_La (h ▸ hx)
    change ((x ∉ L_k ∧ y ∉ L_k ∧ T.Adj x y) ∨ (x ∈ L_k ∧ y = v_pred) ∨ (x = v_pred ∧ y ∈ L_k)) ↔ y = v 0
    simp only [hx_not_Lk, hx_ne_vpred, false_and, or_false, true_and, not_false_eq_true, h_pkt_a x hx y]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hv_not_Lk 0, h⟩⟩
  have h_pkt_L'_short : IsLeafPacket T_short L' (v' (Fin.last (ℓ - 1))) := by
    intro x hx y
    change T_short.Adj x y ↔ y = v_pred
    rcases Finset.mem_insert.mp hx with rfl | hx_Lk
    · have hv_last_ne_vpred : v_last ≠ v_pred := by
        intro h_eq
        have h_idx : Fin.last ℓ = i_pred := hv_inj h_eq
        have h_val : (Fin.last ℓ).val = i_pred.val := congrArg Fin.val h_idx
        simp only [i_pred, Fin.val_last] at h_val
        omega
      have hv_last_ne_v0 : v_last ≠ v 0 := by
        intro h_eq
        have h_idx : Fin.last ℓ = 0 := hv_inj h_eq
        have h_val : (Fin.last ℓ).val = (0 : Fin (ℓ + 1)).val := congrArg Fin.val h_idx
        simp only [Fin.val_last, Fin.val_zero] at h_val
        omega
      change ((v_last ∉ L_k ∧ y ∉ L_k ∧ T.Adj v_last y) ∨ (v_last ∈ L_k ∧ y = v_pred) ∨ (v_last = v_pred ∧ y ∈ L_k)) ↔ y = v_pred
      simp only [hv_last_not_Lk, hv_last_ne_vpred, false_and, or_false, true_and, not_false_eq_true]
      constructor
      · rintro ⟨hy_not_Lk, hadj⟩
        have hy_univ : y ∈ H ∪ (Finset.univ.image v) ∪ L_a ∪ L_k := by
          rw [h_univ]
          exact Finset.mem_univ y
        simp only [Finset.mem_union] at hy_univ
        rcases hy_univ with ((hy_H | hy_v) | hy_La) | hy_Lk
        · have hv_last_D : v_last ∈ (Finset.univ.image v) ∪ L_a ∪ L_k := by
            simp only [Finset.mem_union]
            exact Or.inl (Or.inl (hv_mem_v (Fin.last ℓ)))
          have h_eq := (h_bridge.2.2.2.2 y hy_H v_last hv_last_D (T.symm hadj)).2
          exact False.elim (hv_last_ne_v0 h_eq)
        · rcases Finset.mem_image.mp hy_v with ⟨j, _, rfl⟩
          have h_adj_idx := (h_spine (Fin.last ℓ) j).mp hadj
          simp only [Fin.val_last] at h_adj_idx
          have hj_lt : j.val < ℓ + 1 := j.isLt
          have hj_eq : j = i_pred := by
            ext
            simp only [i_pred, Fin.val_last]
            omega
          rw [hj_eq, hv_pred_eq]
        · have h_eq : v_last = v 0 := (h_pkt_a y hy_La v_last).mp (T.symm hadj)
          exact False.elim (hv_last_ne_v0 h_eq)
        · exact False.elim (hy_not_Lk hy_Lk)
      · rintro rfl
        refine ⟨hw_not_Lk, ?_⟩
        rw [hv_pred_eq]
        apply (h_spine (Fin.last ℓ) i_pred).mpr
        right
        simp only [i_pred, Fin.val_last]
        omega
    · have hx_ne_vpred : x ≠ v_pred := fun h => hw_not_Lk (h ▸ hx_Lk)
      change ((x ∉ L_k ∧ y ∉ L_k ∧ T.Adj x y) ∨ (x ∈ L_k ∧ y = v_pred) ∨ (x = v_pred ∧ y ∈ L_k)) ↔ y = v_pred
      simp [hx_Lk, hx_ne_vpred]
  refine ⟨T_short, L', v', hT_short, ⟨hv'_inj, hSub_H_short, hcard_a, hcard_L',
    Disjoint.mono_right h_img_v'_sub hdisj_Hv,
    hdisj_Ha,
    Finset.disjoint_insert_right.mpr ⟨hv_not_H (Fin.last ℓ), hdisj_Hk⟩,
    Disjoint.mono_left h_img_v'_sub hdisj_va,
    Finset.disjoint_insert_right.mpr ⟨hv_last_not_v', Disjoint.mono_left h_img_v'_sub hdisj_vk⟩,
    Finset.disjoint_insert_right.mpr ⟨hv_not_La (Fin.last ℓ), hdisj_ak⟩,
    h_univ_short, h_bridge_short, h_spine_short, h_pkt_a_short, h_pkt_L'_short⟩,
    hSub_short, hRoot_short⟩

theorem concentrated_double_broom_exists : ∀ (n ℓ a k : ℕ) (T : SimpleGraph (Fin n))
    (H L_a L_k : Finset (Fin n)) (w₀ : Fin n) (v : Fin (ℓ + 1) → Fin n),
    T.IsTree → IsDoubleBroomSuffix T ℓ a k H L_a L_k w₀ v →
    ∃ T_conc : SimpleGraph (Fin n),
      T_conc.IsTree ∧
      IsDoubleBroomSuffix T_conc ℓ 0 (a + k) H ∅ (L_a ∪ L_k) w₀ v ∧
      subtreesIn T_conc H = subtreesIn T H ∧
      rootedSubtreesIn T_conc H w₀ = rootedSubtreesIn T H w₀ :=
by
  have h_reattachLeaf_isTree : ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (x u w : V) (hxw : x ≠ w),
      G.IsTree → IsLeafIn G x u → (reattachLeaf G x w hxw).IsTree := by
    intro V _ G x u w hxw hG hx
    classical
    have hG_conn : G.Connected := hG.isConnected
    have hG_acyc : G.IsAcyclic := hG.IsAcyclic
    have h_leaf_avoid : ∀ {H : SimpleGraph V} {x₀ u₀ : V}, IsLeafIn H x₀ u₀ →
        ∀ {a b : V} (p : H.Walk a b), p.IsPath → a ≠ x₀ → b ≠ x₀ → x₀ ∉ p.support := by
      intro H x₀ u₀ hx₀ a b p
      induction p with
      | nil =>
        intro _ ha _ hmem
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hmem
        exact ha hmem.symm
      | @cons a c b hac q ih =>
        intro hp ha hb
        rw [SimpleGraph.Walk.cons_isPath_iff] at hp
        rcases hp with ⟨hq, ha_not_mem⟩
        have hc : c ≠ x₀ := by
          intro hcx
          subst hcx
          cases q with
          | nil => exact hb rfl
          | @cons _ d _ hxd q' =>
            have ha_eq : a = u₀ := (hx₀ a).mp (H.symm hac)
            have hd_eq : d = u₀ := (hx₀ d).mp hxd
            have had : a = d := ha_eq.trans hd_eq.symm
            apply ha_not_mem
            rw [SimpleGraph.Walk.support_cons, had]
            exact List.mem_cons_of_mem _ q'.start_mem_support
        have hx_not_q : x₀ ∉ q.support := ih hq hc hb
        rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
        exact ⟨ha.symm, hx_not_q⟩
    have h_reach_transfer : ∀ {a b : V} (p : G.Walk a b),
        x ∉ p.support → (reattachLeaf G x w hxw).Reachable a b := by
      intro a b p
      induction p with
      | nil =>
        intro _
        exact SimpleGraph.Reachable.refl _
      | @cons a c b hac q ih =>
        intro h_not_mem
        rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at h_not_mem
        rcases h_not_mem with ⟨hxa, hx_not_q⟩
        have ha : a ≠ x := Ne.symm hxa
        have hc : c ≠ x := by
          intro hcx
          apply hx_not_q
          rw [← hcx]
          exact q.start_mem_support
        have hadj : (reattachLeaf G x w hxw).Adj a c := Or.inl ⟨ha, hc, hac⟩
        exact hadj.reachable.trans (ih hx_not_q)
    have h_conn : (reattachLeaf G x w hxw).Connected := by
      rw [SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨w, fun a => ?_⟩
      by_cases hax : a = x
      · rw [hax]
        have hadj : (reattachLeaf G x w hxw).Adj w x := Or.inr (Or.inr ⟨rfl, rfl⟩)
        exact hadj.reachable
      · obtain ⟨p, hp⟩ := (hG_conn.preconnected w a).exists_isPath
        have hx_not_p : x ∉ p.support := h_leaf_avoid hx p hp hxw.symm hax
        exact h_reach_transfer p hx_not_p
    let G' := reattachLeaf G x w hxw
    have h_leaf_G' : IsLeafIn G' x w := by
      intro v
      constructor
      · intro hadj
        rcases hadj with ⟨hxx, _, _⟩ | ⟨_, rfl⟩ | ⟨hxw_eq, _⟩
        · exact False.elim (hxx rfl)
        · rfl
        · exact False.elim (hxw hxw_eq)
      · intro hvw
        subst hvw
        exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    have h_edge_mem : ∀ {a b : V} (q : G'.Walk a b),
        a ≠ x → b = x → s(x, w) ∈ q.edges := by
      intro a b q
      induction q with
      | nil =>
        intro ha hb
        exact False.elim (ha hb)
      | @cons a c b hac q' ih =>
        intro ha hb
        by_cases hcx : c = x
        · subst hcx
          have haw : a = w := (h_leaf_G' a).mp (G'.symm hac)
          subst haw
          rw [SimpleGraph.Walk.edges_cons, Sym2.eq_swap]
          exact List.mem_cons_self
        · rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ (ih hcx hb)
    have h_acyc : G'.IsAcyclic := by
      intro v c hc
      have hx_not_c : x ∉ c.support := by
        cases c with
        | nil => exact False.elim hc.not_of_nil
        | @cons _ y _ hvy p =>
          have h_cons := (SimpleGraph.Walk.cons_isCycle_iff p hvy).mp hc
          rcases h_cons with ⟨hp, h_no_edge⟩
          by_cases hvx : v = x
          · subst v
            have hyw : y = w := (h_leaf_G' y).mp hvy
            subst y
            have h_in : s(x, w) ∈ p.edges := h_edge_mem p hxw.symm rfl
            exact False.elim (h_no_edge h_in)
          · by_cases hyx : y = x
            · subst y
              have hvw : v = w := (h_leaf_G' v).mp (G'.symm hvy)
              cases p with
              | nil => exact False.elim (hvx rfl)
              | @cons _ z _ hxz p' =>
                have hzv : z = v := ((h_leaf_G' z).mp hxz).trans hvw.symm
                subst z
                apply False.elim (h_no_edge _)
                rw [SimpleGraph.Walk.edges_cons, Sym2.eq_swap]
                exact List.mem_cons_self
            · have hx_not_p : x ∉ p.support := h_leaf_avoid h_leaf_G' p hp hyx hvx
              rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
              exact ⟨Ne.symm hvx, hx_not_p⟩
      have h_edges : ∀ e ∈ c.edges, e ∈ G.edgeSet := by
        intro e
        refine Sym2.ind (fun a b he => ?_) e
        have ha_mem : a ∈ c.support := c.fst_mem_support_of_mem_edges he
        have hb_mem : b ∈ c.support := c.snd_mem_support_of_mem_edges he
        have ha_ne : a ≠ x := fun h => hx_not_c (h ▸ ha_mem)
        have hb_ne : b ≠ x := fun h => hx_not_c (h ▸ hb_mem)
        have hadj' : G'.Adj a b := c.adj_of_mem_edges he
        rw [SimpleGraph.mem_edgeSet]
        rcases hadj' with ⟨_, _, hab⟩ | ⟨hax, _⟩ | ⟨_, hbx⟩
        · exact hab
        · exact False.elim (ha_ne hax)
        · exact False.elim (hb_ne hbx)
      exact hG_acyc (c.transfer G h_edges) (hc.transfer h_edges)
    exact ⟨h_conn, h_acyc⟩
  have h_induce : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (x w : Fin n) (hxw : x ≠ w)
      (H S : Finset (Fin n)), x ∉ H → S ⊆ H →
      (reattachLeaf G x w hxw).induce (S : Set (Fin n)) = G.induce (S : Set (Fin n)) := by
    intro n G x w hxw H S hxH hSH
    ext ⟨u, hu⟩ ⟨z, hz⟩
    have hux : u ≠ x := fun h => hxH (h ▸ hSH hu)
    have hzx : z ≠ x := fun h => hxH (h ▸ hSH hz)
    change (reattachLeaf G x w hxw).Adj u z ↔ G.Adj u z
    simp [reattachLeaf, hux, hzx]
  have h_isSubtree_iff : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (x w : Fin n) (hxw : x ≠ w)
      (H S : Finset (Fin n)), x ∉ H → S ⊆ H →
      (IsSubtree (reattachLeaf G x w hxw) S ↔ IsSubtree G S) := by
    intro n G x w hxw H S hxH hSH
    simp only [IsSubtree, h_induce G x w hxw H S hxH hSH]
  have h_subtreesIn_eq : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (x w : Fin n) (hxw : x ≠ w)
      (H : Finset (Fin n)), x ∉ H →
      subtreesIn (reattachLeaf G x w hxw) H = subtreesIn G H := by
    intro n G x w hxw H hxH
    ext S
    simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_congr_left (fun hSH => h_isSubtree_iff G x w hxw H S hxH hSH)
  have h_rootedSubtreesIn_eq : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (x w w₀ : Fin n) (hxw : x ≠ w)
      (H : Finset (Fin n)), x ∉ H →
      rootedSubtreesIn (reattachLeaf G x w hxw) H w₀ = rootedSubtreesIn G H w₀ := by
    intro n G x w w₀ hxw H hxH
    ext S
    simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_congr_left (fun hSH => h_isSubtree_iff G x w hxw H S hxH hSH.1)
  have h_union_eq : ∀ {n : ℕ} (L_a L_k : Finset (Fin n)) (x : Fin n),
      x ∈ L_a → (L_a.erase x) ∪ (insert x L_k) = L_a ∪ L_k := by
    intro n L_a L_k x hx
    ext y
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert]
    by_cases hyx : y = x
    · subst hyx
      simp [hx]
    · simp [hyx]
  have h_step : ∀ (n ℓ a k : ℕ) (T : SimpleGraph (Fin n))
      (H L_a L_k : Finset (Fin n)) (w₀ : Fin n) (v : Fin (ℓ + 1) → Fin n) (x : Fin n),
      T.IsTree → IsDoubleBroomSuffix T ℓ (a + 1) k H L_a L_k w₀ v → x ∈ L_a →
      ∃ T₁ : SimpleGraph (Fin n),
        T₁.IsTree ∧
        IsDoubleBroomSuffix T₁ ℓ a (k + 1) H (L_a.erase x) (insert x L_k) w₀ v ∧
        subtreesIn T₁ H = subtreesIn T H ∧
        rootedSubtreesIn T₁ H w₀ = rootedSubtreesIn T H w₀ := by
    intro n ℓ a k T H L_a L_k w₀ v x hT hDB hx
    rcases hDB with ⟨h_inj, hSub_H, hcard_a, hcard_k, hdisj_Hv, hdisj_Ha, hdisj_Hk,
      hdisj_va, hdisj_vk, hdisj_ak, h_univ, h_bridge, h_spine, h_pkt_a, h_pkt_k⟩
    let w : Fin n := v (Fin.last ℓ)
    have hx_not_H : x ∉ H := Finset.disjoint_right.mp hdisj_Ha hx
    have hx_not_v : x ∉ Finset.univ.image v := Finset.disjoint_right.mp hdisj_va hx
    have hx_not_Lk : x ∉ L_k := Finset.disjoint_left.mp hdisj_ak hx
    have hv_mem_v : ∀ i : Fin (ℓ + 1), v i ∈ Finset.univ.image v :=
      fun i => Finset.mem_image_of_mem v (Finset.mem_univ i)
    have hv_ne_x : ∀ i : Fin (ℓ + 1), v i ≠ x :=
      fun i h => hx_not_v (h ▸ hv_mem_v i)
    have hxw : x ≠ w := (hv_ne_x (Fin.last ℓ)).symm
    have hv0_ne_x : v 0 ≠ x := hv_ne_x 0
    have hw_mem_v : w ∈ Finset.univ.image v := hv_mem_v (Fin.last ℓ)
    have hu_ne_x : ∀ {u : Fin n}, u ∈ H → u ≠ x :=
      fun hu h => hx_not_H (h ▸ hu)
    have hu_ne_w : ∀ {u : Fin n}, u ∈ H → u ≠ w :=
      fun hu h => Finset.disjoint_left.mp hdisj_Hv hu (h ▸ hw_mem_v)
    have hy_La_ne_w : ∀ {y : Fin n}, y ∈ L_a → y ≠ w :=
      fun hy h => Finset.disjoint_right.mp hdisj_va hy (h ▸ hw_mem_v)
    have hy_Lk_ne_x : ∀ {y : Fin n}, y ∈ L_k → y ≠ x :=
      fun hy h => hx_not_Lk (h ▸ hy)
    have hy_Lk_ne_w : ∀ {y : Fin n}, y ∈ L_k → y ≠ w :=
      fun hy h => Finset.disjoint_right.mp hdisj_vk hy (h ▸ hw_mem_v)
    let T₁ : SimpleGraph (Fin n) := reattachLeaf T x w hxw
    have h_adj_ne : ∀ {u z : Fin n}, u ≠ x → z ≠ x → (T₁.Adj u z ↔ T.Adj u z) := by
      intro u z hux hzx
      simp [T₁, reattachLeaf, hux, hzx]
    have h_adj_ne_both : ∀ {u : Fin n} (z : Fin n), u ≠ x → u ≠ w → (T₁.Adj u z ↔ z ≠ x ∧ T.Adj u z) := by
      intro u z hux huw
      simp [T₁, reattachLeaf, hux, huw]
    have h_adj_x : ∀ (z : Fin n), T₁.Adj x z ↔ z = w := by
      intro z
      simp [T₁, reattachLeaf, hxw]
    have hT₁ : T₁.IsTree := h_reattachLeaf_isTree T x (v 0) w hxw hT (h_pkt_a x hx)
    have hSub_H₁ : IsSubtree T₁ H :=
      (h_isSubtree_iff T x w hxw H H hx_not_H (Finset.Subset.refl H)).mpr hSub_H
    have hSub_eq : subtreesIn T₁ H = subtreesIn T H :=
      h_subtreesIn_eq T x w hxw H hx_not_H
    have hRoot_eq : rootedSubtreesIn T₁ H w₀ = rootedSubtreesIn T H w₀ :=
      h_rootedSubtreesIn_eq T x w w₀ hxw H hx_not_H
    have h_D_eq : (Finset.univ.image v) ∪ (L_a.erase x) ∪ (insert x L_k) =
        (Finset.univ.image v) ∪ L_a ∪ L_k := by
      rw [Finset.union_assoc, h_union_eq L_a L_k x hx, ← Finset.union_assoc]
    have hcard_a₁ : (L_a.erase x).card = a := by
      rw [Finset.card_erase_of_mem hx, hcard_a]
      rfl
    have hcard_k₁ : (insert x L_k).card = k + 1 := by
      rw [Finset.card_insert_of_notMem hx_not_Lk, hcard_k]
    have h_univ₁ : H ∪ (Finset.univ.image v) ∪ (L_a.erase x) ∪ (insert x L_k) = Finset.univ := by
      rw [Finset.union_assoc (H ∪ Finset.univ.image v), h_union_eq L_a L_k x hx, ← Finset.union_assoc]
      exact h_univ
    have h_bridge₁ : IsBridgeJoin T₁ H ((Finset.univ.image v) ∪ (L_a.erase x) ∪ (insert x L_k)) w₀ (v 0) := by
      rw [h_D_eq]
      rcases h_bridge with ⟨h_disj_HD, hw₀_H, hv0_D, hadj_w0_v0, h_bridge_uniq⟩
      refine ⟨h_disj_HD, hw₀_H, hv0_D, ?_, ?_⟩
      · exact (h_adj_ne (hu_ne_x hw₀_H) hv0_ne_x).mpr hadj_w0_v0
      · intro u hu z hz hadj₁
        have hadj : T.Adj u z := ((h_adj_ne_both z (hu_ne_x hu) (hu_ne_w hu)).mp hadj₁).2
        exact h_bridge_uniq u hu z hz hadj
    have h_spine₁ : ∀ i j : Fin (ℓ + 1), T₁.Adj (v i) (v j) ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
      intro i j
      rw [h_adj_ne (hv_ne_x i) (hv_ne_x j)]
      exact h_spine i j
    have h_pkt_a₁ : IsLeafPacket T₁ (L_a.erase x) (v 0) := by
      intro y hy z
      rcases Finset.mem_erase.mp hy with ⟨hy_ne_x, hy_La⟩
      rw [h_adj_ne_both z hy_ne_x (hy_La_ne_w hy_La), h_pkt_a y hy_La z]
      exact ⟨fun h => h.2, fun h => ⟨h ▸ hv0_ne_x, h⟩⟩
    have h_pkt_k₁ : IsLeafPacket T₁ (insert x L_k) w := by
      intro y hy z
      rcases Finset.mem_insert.mp hy with rfl | hy_Lk
      · exact h_adj_x z
      · rw [h_adj_ne_both z (hy_Lk_ne_x hy_Lk) (hy_Lk_ne_w hy_Lk), h_pkt_k y hy_Lk z]
        exact ⟨fun h => h.2, fun h => ⟨h ▸ hxw.symm, h⟩⟩
    refine ⟨T₁, hT₁, ⟨h_inj, hSub_H₁, hcard_a₁, hcard_k₁, hdisj_Hv,
      Disjoint.mono_right (Finset.erase_subset x L_a) hdisj_Ha,
      Finset.disjoint_insert_right.mpr ⟨hx_not_H, hdisj_Hk⟩,
      Disjoint.mono_right (Finset.erase_subset x L_a) hdisj_va,
      Finset.disjoint_insert_right.mpr ⟨hx_not_v, hdisj_vk⟩,
      Finset.disjoint_insert_right.mpr ⟨Finset.notMem_erase x L_a,
        Disjoint.mono_left (Finset.erase_subset x L_a) hdisj_ak⟩,
      h_univ₁, h_bridge₁, h_spine₁, h_pkt_a₁, h_pkt_k₁⟩, hSub_eq, hRoot_eq⟩
  intro n ℓ a k T H L_a L_k w₀ v hT hDB
  induction a generalizing k T L_a L_k with
  | zero =>
    have hLa_emp : L_a = ∅ := Finset.card_eq_zero.mp hDB.2.2.1
    refine ⟨T, hT, ?_, rfl, rfl⟩
    rw [hLa_emp, Finset.empty_union, Nat.zero_add]
    rw [hLa_emp] at hDB
    exact hDB
  | succ a ih =>
    have hcard_pos : 0 < L_a.card := by
      rw [hDB.2.2.1]
      omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hcard_pos
    obtain ⟨T₁, hT₁, hDB₁, hSub₁, hRoot₁⟩ := h_step n ℓ a k T H L_a L_k w₀ v x hT hDB hx
    obtain ⟨T_conc, hT_conc, hDB_conc, hSub_conc, hRoot_conc⟩ :=
      ih (k + 1) T₁ (L_a.erase x) (insert x L_k) hT₁ hDB₁
    have h_ak : a + (k + 1) = a + 1 + k := by omega
    rw [h_union_eq L_a L_k x hx, h_ak] at hDB_conc
    exact ⟨T_conc, hT_conc, hDB_conc, hSub_conc.trans hSub₁, hRoot_conc.trans hRoot₁⟩

theorem lemma_p_algebraic_dichotomy : ∀ (NH RH S tH ℓ a k : ℕ),
    1 ≤ ℓ → 1 ≤ a → 2 ≤ k →
    (2 ^ a * (ℓ + 2 ^ k)) ^ 2 ≤ S →
    (2 ^ a * (ℓ + 2 ^ k)) * tH ≤ S ^ 2 →
    doubleBroomOrderSum RH S tH ℓ a k / doubleBroomCount NH S ℓ a k <
      doubleBroomOrderSum RH S tH (ℓ - 1) a (k + 1) / doubleBroomCount NH S (ℓ - 1) a (k + 1) ∨
    doubleBroomOrderSum RH S tH ℓ a k / doubleBroomCount NH S ℓ a k <
      doubleBroomOrderSum RH S tH ℓ 0 (a + k) / doubleBroomCount NH S ℓ 0 (a + k) :=
by
  intro NH RH S tH ℓ a k hℓ ha hk hS htH
  set N0 : ℚ := doubleBroomCount NH S ℓ a k
  set R0 : ℚ := doubleBroomOrderSum RH S tH ℓ a k
  set N1 : ℚ := doubleBroomCount NH S (ℓ - 1) a (k + 1)
  set R1 : ℚ := doubleBroomOrderSum RH S tH (ℓ - 1) a (k + 1)
  set N2 : ℚ := doubleBroomCount NH S ℓ 0 (a + k)
  set R2 : ℚ := doubleBroomOrderSum RH S tH ℓ 0 (a + k)
  set r : ℚ := (2 : ℚ) ^ a
  set z : ℚ := (2 : ℚ) ^ k
  set ℓQ : ℚ := (ℓ : ℚ)
  set aQ : ℚ := (a : ℚ)
  set kQ : ℚ := (k : ℚ)
  set SQ : ℚ := (S : ℚ)
  set tHQ : ℚ := (tH : ℚ)
  set NHQ : ℚ := (NH : ℚ)
  set RHQ : ℚ := (RH : ℚ)
  set b : ℚ := r * (ℓQ + z)
  set D0 : ℚ := r * (SQ + 1) + ℓQ - 2
  set E : ℚ := SQ - z + 1
  
  have hℓ_sub : ((ℓ - 1 : ℕ) : ℚ) = ℓQ - 1 := by
    dsimp only [ℓQ]
    rw [Nat.cast_sub hℓ, Nat.cast_one]
  have hpow_k1 : (2 : ℚ) ^ (k + 1) = 2 * z := by
    dsimp only [z]
    rw [pow_add, pow_one]
    ring
  have hpow_ak : (2 : ℚ) ^ (a + k) = r * z := by
    dsimp only [r, z]
    rw [pow_add]
  
  have hN1_sub_N0 : N1 - N0 = (z - 1) * D0 := by
    dsimp only [N1, N0, D0, doubleBroomCount, r, z, ℓQ, aQ, kQ, SQ, NHQ]
    rw [hℓ_sub, hpow_k1]
    push_cast
    ring
  have hN0_sub_N2 : N0 - N2 = ℓQ * (r - 1) * E := by
    dsimp only [N0, N2, E, doubleBroomCount, r, z, ℓQ, aQ, kQ, SQ, NHQ]
    rw [hpow_ak, pow_zero]
    push_cast
    ring
  have h_master :
      2 * ((N0 - N2) * (R1 * N0 - R0 * N1) + (N1 - N0) * (R2 * N0 - R0 * N2)) =
      N0 * ℓQ * (
        2 * (r - 1) * (z - 1) * (SQ ^ 2 - b * tHQ) +
        2 * (r - 1) * (z - 1) * ((r - 1) * ℓQ + 2) * tHQ +
        (r - 1) * (kQ - 2) * z * D0 * SQ +
        (r - 1) * (z + 1) * ((r - 2) * SQ + r + ℓQ - 2) * SQ +
        4 * (r - 1) * SQ ^ 2 +
        (r - 1) * (z - 1) ^ 2 * D0 +
        (r - 1 - aQ) * (z - 1) * D0 * E +
        (r - 1) * (z - 1) * E * ((ℓQ - 1) * (r * SQ + r - 1 - aQ) + ℓQ - 1 + aQ)
      ) := by
    dsimp only [N0, R0, N1, R1, N2, R2, b, D0, E, doubleBroomCount, doubleBroomOrderSum,
      r, z, ℓQ, aQ, kQ, SQ, tHQ, NHQ, RHQ]
    rw [hℓ_sub, hpow_k1, hpow_ak, pow_zero]
    push_cast
    ring
  
  have ha_pow_nat : a + 1 ≤ 2 ^ a := Nat.lt_two_pow_self
  have ha_pow : aQ + 1 ≤ r := by
    dsimp only [aQ, r]
    have h1 : ((a + 1 : ℕ) : ℚ) ≤ ((2 ^ a : ℕ) : ℚ) := by exact_mod_cast ha_pow_nat
    push_cast at h1
    exact h1
  have hk_pow_nat : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hk_pow : (4 : ℚ) ≤ z := by
    dsimp only [z]
    have h1 : ((4 : ℕ) : ℚ) ≤ ((2 ^ k : ℕ) : ℚ) := by exact_mod_cast hk_pow_nat
    push_cast at h1
    exact h1
  have hℓQ : (1 : ℚ) ≤ ℓQ := by dsimp only [ℓQ]; exact_mod_cast hℓ
  have haQ : (1 : ℚ) ≤ aQ := by dsimp only [aQ]; exact_mod_cast ha
  have hkQ : (2 : ℚ) ≤ kQ := by dsimp only [kQ]; exact_mod_cast hk
  have hNHQ : (0 : ℚ) ≤ NHQ := Nat.cast_nonneg NH
  have htHQ : (0 : ℚ) ≤ tHQ := Nat.cast_nonneg tH
  have hSQ_b : b ^ 2 ≤ SQ := by
    dsimp only [b, r, z, ℓQ, SQ]
    have h1 : (((2 ^ a * (ℓ + 2 ^ k)) ^ 2 : ℕ) : ℚ) ≤ (S : ℚ) := by exact_mod_cast hS
    push_cast at h1
    exact h1
  have htHQ_S : b * tHQ ≤ SQ ^ 2 := by
    dsimp only [b, r, z, ℓQ, tHQ, SQ]
    have h1 : (((2 ^ a * (ℓ + 2 ^ k)) * tH : ℕ) : ℚ) ≤ ((S ^ 2 : ℕ) : ℚ) := by exact_mod_cast htH
    push_cast at h1
    exact h1
  
  have hr_ge : (2 : ℚ) ≤ r := by linarith
  have hb_ge : (10 : ℚ) ≤ b := by
    dsimp only [b]
    nlinarith
  have hSQ_ge : (100 : ℚ) ≤ SQ := by nlinarith
  have hb_ge_z : z ≤ b := by
    dsimp only [b]
    nlinarith
  have hSQ_ge_b : b ≤ SQ := by nlinarith
  have hE_pos : (0 : ℚ) < E := by
    dsimp only [E]
    linarith
  have hD0_pos : (0 : ℚ) < D0 := by
    dsimp only [D0]
    nlinarith
  have hN2_expand : N2 = NHQ + aQ + kQ + r * z + ℓQ * (1 + r * z) +
      ℓQ * (ℓQ - 1) / 2 + SQ * (ℓQ + r * z) := by
    dsimp only [N2, doubleBroomCount, r, z, ℓQ, aQ, kQ, SQ, NHQ]
    rw [hpow_ak, pow_zero]
    push_cast
    ring
  have hN2_pos : (0 : ℚ) < N2 := by
    rw [hN2_expand]
    have h_rz : (0 : ℚ) < r * z := by positivity
    have h_l_rz : (0 : ℚ) < ℓQ * (1 + r * z) := by positivity
    have h_l_sub : (0 : ℚ) ≤ ℓQ * (ℓQ - 1) / 2 := by
      have : (0 : ℚ) ≤ ℓQ - 1 := by linarith
      positivity
    have h_S_term : (0 : ℚ) < SQ * (ℓQ + r * z) := by
      have : (0 : ℚ) < ℓQ + r * z := by linarith
      have : (0 : ℚ) < SQ := by linarith
      positivity
    linarith
  have hN0_sub_N2_pos : (0 : ℚ) < N0 - N2 := by
    rw [hN0_sub_N2]
    have : (0 : ℚ) < r - 1 := by linarith
    positivity
  have hN1_sub_N0_pos : (0 : ℚ) < N1 - N0 := by
    rw [hN1_sub_N0]
    have : (0 : ℚ) < z - 1 := by linarith
    positivity
  have hN0_pos : (0 : ℚ) < N0 := by linarith
  have hN1_pos : (0 : ℚ) < N1 := by linarith
  
  have hr1_pos : (0 : ℚ) < r - 1 := by linarith
  have hz1_pos : (0 : ℚ) < z - 1 := by linarith
  have hz_pos : (0 : ℚ) < z := by linarith
  have hSQ_pos : (0 : ℚ) < SQ := by linarith
  have hr2_nonneg : (0 : ℚ) ≤ r - 2 := by linarith
  have hra_nonneg : (0 : ℚ) ≤ r - 1 - aQ := by linarith
  have hk2_nonneg : (0 : ℚ) ≤ kQ - 2 := by linarith
  have hℓ1_nonneg : (0 : ℚ) ≤ ℓQ - 1 := by linarith
  have hS2_bt : (0 : ℚ) ≤ SQ ^ 2 - b * tHQ := by linarith
  have hT1 : (0 : ℚ) ≤ 2 * (r - 1) * (z - 1) * (SQ ^ 2 - b * tHQ) := by positivity
  have hT2 : (0 : ℚ) ≤ 2 * (r - 1) * (z - 1) * ((r - 1) * ℓQ + 2) * tHQ := by positivity
  have hT3 : (0 : ℚ) ≤ (r - 1) * (kQ - 2) * z * D0 * SQ := by positivity
  have hT4_inner : (0 : ℚ) ≤ (r - 2) * SQ + r + ℓQ - 2 := by
    have : (0 : ℚ) ≤ (r - 2) * SQ := by positivity
    linarith
  have hT4 : (0 : ℚ) ≤ (r - 1) * (z + 1) * ((r - 2) * SQ + r + ℓQ - 2) * SQ := by positivity
  have hT5 : (0 : ℚ) < 4 * (r - 1) * SQ ^ 2 := by positivity
  have hT6 : (0 : ℚ) ≤ (r - 1) * (z - 1) ^ 2 * D0 := by positivity
  have hT7 : (0 : ℚ) ≤ (r - 1 - aQ) * (z - 1) * D0 * E := by positivity
  have hT8_inner1 : (0 : ℚ) ≤ r * SQ + r - 1 - aQ := by
    have : (0 : ℚ) ≤ r * SQ := by positivity
    linarith
  have hT8_inner2 : (0 : ℚ) ≤ (ℓQ - 1) * (r * SQ + r - 1 - aQ) + ℓQ - 1 + aQ := by
    have : (0 : ℚ) ≤ (ℓQ - 1) * (r * SQ + r - 1 - aQ) := by positivity
    linarith
  have hT8 : (0 : ℚ) ≤ (r - 1) * (z - 1) * E *
      ((ℓQ - 1) * (r * SQ + r - 1 - aQ) + ℓQ - 1 + aQ) := by positivity
  have h_bracket_pos : (0 : ℚ) <
      2 * (r - 1) * (z - 1) * (SQ ^ 2 - b * tHQ) +
      2 * (r - 1) * (z - 1) * ((r - 1) * ℓQ + 2) * tHQ +
      (r - 1) * (kQ - 2) * z * D0 * SQ +
      (r - 1) * (z + 1) * ((r - 2) * SQ + r + ℓQ - 2) * SQ +
      4 * (r - 1) * SQ ^ 2 +
      (r - 1) * (z - 1) ^ 2 * D0 +
      (r - 1 - aQ) * (z - 1) * D0 * E +
      (r - 1) * (z - 1) * E * ((ℓQ - 1) * (r * SQ + r - 1 - aQ) + ℓQ - 1 + aQ) := by
    linarith
  have h_lhs_pos : (0 : ℚ) < 2 * ((N0 - N2) * (R1 * N0 - R0 * N1) + (N1 - N0) * (R2 * N0 - R0 * N2)) := by
    rw [h_master]
    have hℓQ_pos : (0 : ℚ) < ℓQ := by linarith
    positivity
  
  have h_disj : 0 < R1 * N0 - R0 * N1 ∨ 0 < R2 * N0 - R0 * N2 := by
    by_contra! h_neg
    rcases h_neg with ⟨h1, h2⟩
    have h_prod1 : (N0 - N2) * (R1 * N0 - R0 * N1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hN0_sub_N2_pos) h1
    have h_prod2 : (N1 - N0) * (R2 * N0 - R0 * N2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hN1_sub_N0_pos) h2
    linarith
  
  rcases h_disj with h_short | h_conc
  · left
    rw [div_lt_div_iff₀ hN0_pos hN1_pos]
    linarith
  · right
    rw [div_lt_div_iff₀ hN0_pos hN2_pos]
    linarith

theorem packet_concentration_improves : ∀ (n : ℕ) (hn : 1 ≤ n) (T : SimpleGraph (Fin n)),
    T.IsTree → HasInternalPacketSuffix T →
    ∃ T' : SimpleGraph (Fin n), T'.IsTree ∧ meanSubtreeOrder T < meanSubtreeOrder T' :=
by
  intro n _hn T hT hSuffix
  rcases hSuffix with ⟨ℓ, a, k, H, L_a, L_k, w₀, v, hℓ, ha, hk, h_inj, hSub_H,
    hcard_a, hcard_k, hdisj_Hv, hdisj_Ha, hdisj_Hk, hdisj_va, hdisj_vk, hdisj_ak,
    h_univ, h_bridge, h_spine, h_pkt_a, h_pkt_k, hS, htH⟩
  have hDB_T : IsDoubleBroomSuffix T ℓ a k H L_a L_k w₀ v :=
    ⟨h_inj, hSub_H, hcard_a, hcard_k, hdisj_Hv, hdisj_Ha, hdisj_Hk,
     hdisj_va, hdisj_vk, hdisj_ak, h_univ, h_bridge, h_spine, h_pkt_a, h_pkt_k⟩
  obtain ⟨hCount_T, hOrder_T⟩ :=
    double_broom_suffix_moments n ℓ a k T H L_a L_k w₀ v hT hDB_T
  have h_dich := lemma_p_algebraic_dichotomy
    (subtreesIn T H).card (∑ S ∈ subtreesIn T H, S.card)
    (rootedCount T H w₀) (rootedOrderSum T H w₀) ℓ a k hℓ ha hk hS htH
  rcases h_dich with h_short | h_conc
  · obtain ⟨T_short, L', v', hTree_short, hDB_short, hSub_short, hRoot_short⟩ :=
      shortened_double_broom_exists n ℓ a k T H L_a L_k w₀ v hT hℓ hDB_T
    obtain ⟨hCount_short, hOrder_short⟩ :=
      double_broom_suffix_moments n (ℓ - 1) a (k + 1) T_short H L_a L' w₀ v' hTree_short hDB_short
    have hRC_short : rootedCount T_short H w₀ = rootedCount T H w₀ := by
      simp only [rootedCount, hRoot_short]
    have hRO_short : rootedOrderSum T_short H w₀ = rootedOrderSum T H w₀ := by
      simp only [rootedOrderSum, hRoot_short]
    refine ⟨T_short, hTree_short, ?_⟩
    simp only [meanSubtreeOrder, hCount_T, hOrder_T, hCount_short, hOrder_short,
      hSub_short, hRC_short, hRO_short]
    exact h_short
  · obtain ⟨T_conc, hTree_conc, hDB_conc, hSub_conc, hRoot_conc⟩ :=
      concentrated_double_broom_exists n ℓ a k T H L_a L_k w₀ v hT hDB_T
    obtain ⟨hCount_conc, hOrder_conc⟩ :=
      double_broom_suffix_moments n ℓ 0 (a + k) T_conc H ∅ (L_a ∪ L_k) w₀ v hTree_conc hDB_conc
    have hRC_conc : rootedCount T_conc H w₀ = rootedCount T H w₀ := by
      simp only [rootedCount, hRoot_conc]
    have hRO_conc : rootedOrderSum T_conc H w₀ = rootedOrderSum T H w₀ := by
      simp only [rootedOrderSum, hRoot_conc]
    refine ⟨T_conc, hTree_conc, ?_⟩
    simp only [meanSubtreeOrder, hCount_T, hOrder_T, hCount_conc, hOrder_conc,
      hSub_conc, hRC_conc, hRO_conc]
    exact h_conc

theorem cherry_bridge_split_improves : ∀ (n : ℕ) (hn : 1 ≤ n) (T : SimpleGraph (Fin n)),
    T.IsTree →
    ∀ (w u ℓ₁ ℓ₂ z : Fin n) (H A B : Finset (Fin n)),
      ℓ₁ ≠ ℓ₂ → u ≠ ℓ₁ → u ≠ ℓ₂ →
      H = Finset.univ \ ({u, ℓ₁, ℓ₂} : Finset (Fin n)) →
      IsSubtree T H →
      IsBridgeJoin T H ({u, ℓ₁, ℓ₂} : Finset (Fin n)) w u →
      IsLeafIn T ℓ₁ u → IsLeafIn T ℓ₂ u →
      (∀ v : Fin n, T.Adj u v ↔ v = w ∨ v = ℓ₁ ∨ v = ℓ₂) →
      H = A ∪ B → IsSubtree T A → IsSubtree T B →
      IsBridgeJoin T A B w z →
      120 * rootedOrderSum T A w ≤
        25 * (rootedCount T A w) ^ 2 + 48 * rootedCount T A w →
      ∃ T' : SimpleGraph (Fin n), T'.IsTree ∧ meanSubtreeOrder T < meanSubtreeOrder T' :=
by
  intro n _hn T hT w u ℓ₁ ℓ₂ z H A B h12 hu1 hu2 hH_eq _hH_sub hBridge_u hLeaf1 hLeaf2 hu_adj
    hHAB hA hB hBridge_z hIneqA
  classical
  
  have h_reattachLeaf_isTree : ∀ (G : SimpleGraph (Fin n)) (x u₀ w₀ : Fin n) (hxw : x ≠ w₀),
      G.IsTree → IsLeafIn G x u₀ → (reattachLeaf G x w₀ hxw).IsTree := by
    intro G x u₀ w₀ hxw hG hx
    have hG_conn : G.Connected := hG.isConnected
    have hG_acyc : G.IsAcyclic := hG.IsAcyclic
    have h_leaf_avoid : ∀ {G₀ : SimpleGraph (Fin n)} {x₀ u₁ : Fin n}, IsLeafIn G₀ x₀ u₁ →
        ∀ {a b : Fin n} (p : G₀.Walk a b), p.IsPath → a ≠ x₀ → b ≠ x₀ → x₀ ∉ p.support := by
      intro G₀ x₀ u₁ hx₀ a b p
      induction p with
      | nil =>
        intro _ ha _ hmem
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hmem
        exact ha hmem.symm
      | @cons a c b hac q ih =>
        intro hp ha hb
        rw [SimpleGraph.Walk.cons_isPath_iff] at hp
        rcases hp with ⟨hq, ha_not_mem⟩
        have hc : c ≠ x₀ := by
          intro hcx
          subst hcx
          cases q with
          | nil => exact hb rfl
          | @cons _ d _ hxd q' =>
            have ha_eq : a = u₁ := (hx₀ a).mp (G₀.symm hac)
            have hd_eq : d = u₁ := (hx₀ d).mp hxd
            have had : a = d := ha_eq.trans hd_eq.symm
            apply ha_not_mem
            rw [SimpleGraph.Walk.support_cons, had]
            exact List.mem_cons_of_mem _ q'.start_mem_support
        have hx_not_q : x₀ ∉ q.support := ih hq hc hb
        rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
        exact ⟨ha.symm, hx_not_q⟩
    have h_reach_transfer : ∀ {a b : Fin n} (p : G.Walk a b),
        x ∉ p.support → (reattachLeaf G x w₀ hxw).Reachable a b := by
      intro a b p
      induction p with
      | nil =>
        intro _
        exact SimpleGraph.Reachable.refl _
      | @cons a c b hac q ih =>
        intro h_not_mem
        rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at h_not_mem
        rcases h_not_mem with ⟨hxa, hx_not_q⟩
        have ha : a ≠ x := Ne.symm hxa
        have hc : c ≠ x := by
          intro hcx
          apply hx_not_q
          rw [← hcx]
          exact q.start_mem_support
        have hadj : (reattachLeaf G x w₀ hxw).Adj a c := Or.inl ⟨ha, hc, hac⟩
        exact hadj.reachable.trans (ih hx_not_q)
    have h_conn : (reattachLeaf G x w₀ hxw).Connected := by
      rw [SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨w₀, fun a => ?_⟩
      by_cases hax : a = x
      · rw [hax]
        have hadj : (reattachLeaf G x w₀ hxw).Adj w₀ x := Or.inr (Or.inr ⟨rfl, rfl⟩)
        exact hadj.reachable
      · obtain ⟨p, hp⟩ := (hG_conn.preconnected w₀ a).exists_isPath
        have hx_not_p : x ∉ p.support := h_leaf_avoid hx p hp hxw.symm hax
        exact h_reach_transfer p hx_not_p
    let G' := reattachLeaf G x w₀ hxw
    have h_leaf_G' : IsLeafIn G' x w₀ := by
      intro v
      constructor
      · intro hadj
        rcases hadj with ⟨hxx, _, _⟩ | ⟨_, rfl⟩ | ⟨hxw_eq, _⟩
        · exact False.elim (hxx rfl)
        · rfl
        · exact False.elim (hxw hxw_eq)
      · intro hvw
        subst hvw
        exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    have h_edge_mem : ∀ {a b : Fin n} (q : G'.Walk a b),
        a ≠ x → b = x → s(x, w₀) ∈ q.edges := by
      intro a b q
      induction q with
      | nil =>
        intro ha hb
        exact False.elim (ha hb)
      | @cons a c b hac q' ih =>
        intro ha hb
        by_cases hcx : c = x
        · subst hcx
          have haw : a = w₀ := (h_leaf_G' a).mp (G'.symm hac)
          subst haw
          rw [SimpleGraph.Walk.edges_cons, Sym2.eq_swap]
          exact List.mem_cons_self
        · rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ (ih hcx hb)
    have h_acyc : G'.IsAcyclic := by
      intro v c hc
      have hx_not_c : x ∉ c.support := by
        cases c with
        | nil => exact False.elim hc.not_of_nil
        | @cons _ y _ hvy p =>
          have h_cons := (SimpleGraph.Walk.cons_isCycle_iff p hvy).mp hc
          rcases h_cons with ⟨hp, h_no_edge⟩
          by_cases hvx : v = x
          · subst v
            have hyw : y = w₀ := (h_leaf_G' y).mp hvy
            subst y
            have h_in : s(x, w₀) ∈ p.edges := h_edge_mem p hxw.symm rfl
            exact False.elim (h_no_edge h_in)
          · by_cases hyx : y = x
            · subst y
              have hvw : v = w₀ := (h_leaf_G' v).mp (G'.symm hvy)
              cases p with
              | nil => exact False.elim (hvx rfl)
              | @cons _ z₀ _ hxz p' =>
                have hzv : z₀ = v := ((h_leaf_G' z₀).mp hxz).trans hvw.symm
                subst z₀
                apply False.elim (h_no_edge _)
                rw [SimpleGraph.Walk.edges_cons, Sym2.eq_swap]
                exact List.mem_cons_self
            · have hx_not_p : x ∉ p.support := h_leaf_avoid h_leaf_G' p hp hyx hvx
              rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
              exact ⟨Ne.symm hvx, hx_not_p⟩
      have h_edges : ∀ e ∈ c.edges, e ∈ G.edgeSet := by
        intro e
        refine Sym2.ind (fun a b he => ?_) e
        have ha_mem : a ∈ c.support := c.fst_mem_support_of_mem_edges he
        have hb_mem : b ∈ c.support := c.snd_mem_support_of_mem_edges he
        have ha_ne : a ≠ x := fun h => hx_not_c (h ▸ ha_mem)
        have hb_ne : b ≠ x := fun h => hx_not_c (h ▸ hb_mem)
        have hadj' : G'.Adj a b := c.adj_of_mem_edges he
        rw [SimpleGraph.mem_edgeSet]
        rcases hadj' with ⟨_, _, hab⟩ | ⟨hax, _⟩ | ⟨_, hbx⟩
        · exact hab
        · exact False.elim (ha_ne hax)
        · exact False.elim (hb_ne hbx)
      exact hG_acyc (c.transfer G h_edges) (hc.transfer h_edges)
    exact ⟨h_conn, h_acyc⟩
  
  have isSubtree_insert_leaf_iff : ∀ (G : SimpleGraph (Fin n)) (U S₀ : Finset (Fin n)) (z₀ r : Fin n),
      z₀ ∉ U → r ∈ U → (∀ v ∈ insert z₀ U, G.Adj z₀ v ↔ v = r) → S₀ ⊆ U →
      (IsSubtree G (insert z₀ S₀) ↔ S₀ = ∅ ∨ (IsSubtree G S₀ ∧ r ∈ S₀)) := by
    intro G U S₀ z₀ r hz hr hadj hS₀
    have hzr : z₀ ≠ r := fun h => hz (h ▸ hr)
    have hzS₀ : z₀ ∉ S₀ := fun h => hz (hS₀ h)
    rcases S₀.eq_empty_or_nonempty with rfl | hS₀_ne
    · simp only [Finset.insert_empty, true_or, iff_true]
      refine ⟨Finset.singleton_nonempty z₀, ?_⟩
      rw [SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨⟨z₀, by simp⟩, fun ⟨w₀, hw₀⟩ => ?_⟩
      have hwz : w₀ = z₀ := by simpa using hw₀
      subst hwz
      exact SimpleGraph.Reachable.rfl
    · simp only [hS₀_ne.ne_empty, false_or]
      let S : Finset (Fin n) := insert z₀ S₀
      change IsSubtree G S ↔ IsSubtree G S₀ ∧ r ∈ S₀
      constructor
      · intro hS
        have hr_mem : r ∈ S₀ := by
          obtain ⟨a, ha⟩ := hS₀_ne
          have h_walk : ∀ (u₀ v₀ : ↑(S : Set (Fin n))) (p : (G.induce (S : Set (Fin n))).Walk u₀ v₀),
              u₀.1 = z₀ → v₀.1 ∈ S₀ → r ∈ S₀ := by
            intro u₀ v₀ p huz hvS₀
            cases p with
            | nil =>
              exact False.elim (hzS₀ (huz ▸ hvS₀))
            | @cons _ b _ hadj_step _ =>
              have hb_mem : b.1 ∈ insert z₀ S₀ := b.2
              have hb_U : b.1 ∈ insert z₀ U := Finset.insert_subset_insert z₀ hS₀ hb_mem
              have hbr : b.1 = r := (hadj b.1 hb_U).mp (huz ▸ hadj_step)
              rcases Finset.mem_insert.mp hb_mem with hbz | hbS₀
              · exact False.elim (hzr (hbz.symm.trans hbr))
              · exact hbr ▸ hbS₀
          obtain ⟨p⟩ := hS.2.preconnected
            ⟨z₀, Finset.mem_coe.mpr (Finset.mem_insert_self z₀ S₀)⟩
            ⟨a, Finset.mem_coe.mpr (Finset.mem_insert_of_mem ha)⟩
          exact h_walk _ _ p rfl ha
        refine ⟨⟨hS₀_ne, ?_⟩, hr_mem⟩
        rw [SimpleGraph.connected_iff_exists_forall_reachable]
        let φ : ↑(S : Set (Fin n)) → ↑(S₀ : Set (Fin n)) := fun x =>
          ⟨if x.1 = z₀ then r else x.1, by
            by_cases hx : x.1 = z₀
            · simp [hx, hr_mem]
            · simp only [hx, ↓reduceIte, Finset.mem_coe]
              rcases Finset.mem_insert.mp x.2 with hxz | h
              · exact False.elim (hx hxz)
              · exact h⟩
        have hφ_mem : ∀ (a : Fin n) (ha : a ∈ S₀),
            φ ⟨a, Finset.mem_coe.mpr (Finset.mem_insert_of_mem ha)⟩ = ⟨a, ha⟩ := by
          intro a ha
          have haz : a ≠ z₀ := fun h => hzS₀ (h ▸ ha)
          ext
          simp [φ, haz]
        have hφ_adj : ∀ x y : ↑(S : Set (Fin n)),
            (G.induce (S : Set (Fin n))).Adj x y →
            (G.induce (S₀ : Set (Fin n))).Reachable (φ x) (φ y) := by
          intro x y hxy
          change G.Adj x.1 y.1 at hxy
          by_cases hx : x.1 = z₀
          · have hy_U : y.1 ∈ insert z₀ U := Finset.insert_subset_insert z₀ hS₀ y.2
            have hyr : y.1 = r := (hadj y.1 hy_U).mp (hx ▸ hxy)
            have hφ_eq : φ x = φ y := by
              ext
              simp [φ, hx, hyr]
            rw [hφ_eq]
          · by_cases hy : y.1 = z₀
            · have hx_U : x.1 ∈ insert z₀ U := Finset.insert_subset_insert z₀ hS₀ x.2
              have hxr : x.1 = r := (hadj x.1 hx_U).mp (hy ▸ G.symm hxy)
              have hφ_eq : φ x = φ y := by
                ext
                simp [φ, hy, hxr]
              rw [hφ_eq]
            · apply SimpleGraph.Adj.reachable
              change G.Adj (φ x).1 (φ y).1
              simp [φ, hx, hy, hxy]
        have hφ_walk : ∀ (x y : ↑(S : Set (Fin n)))
            (p : (G.induce (S : Set (Fin n))).Walk x y),
            (G.induce (S₀ : Set (Fin n))).Reachable (φ x) (φ y) := by
          intro x y p
          induction p with
          | nil => exact SimpleGraph.Reachable.rfl
          | cons h_step _ ih => exact (hφ_adj _ _ h_step).trans ih
        refine ⟨⟨r, hr_mem⟩, fun ⟨b, hb⟩ => ?_⟩
        obtain ⟨p⟩ := hS.2.preconnected
          ⟨r, Finset.mem_coe.mpr (Finset.mem_insert_of_mem hr_mem)⟩
          ⟨b, Finset.mem_coe.mpr (Finset.mem_insert_of_mem hb)⟩
        have h_reach := hφ_walk _ _ p
        rwa [hφ_mem r hr_mem, hφ_mem b hb] at h_reach
      · rintro ⟨hS₀_sub, hr_mem⟩
        refine ⟨Finset.insert_nonempty z₀ S₀, ?_⟩
        rw [SimpleGraph.connected_iff_exists_forall_reachable]
        let ι : ↑(S₀ : Set (Fin n)) → ↑(S : Set (Fin n)) :=
          fun x => ⟨x.1, Finset.mem_coe.mpr (Finset.mem_insert_of_mem x.2)⟩
        have hι_walk : ∀ (x y : ↑(S₀ : Set (Fin n))) (p : (G.induce (S₀ : Set (Fin n))).Walk x y),
            (G.induce (S : Set (Fin n))).Reachable (ι x) (ι y) := by
          intro x y p
          induction p with
          | nil => exact SimpleGraph.Reachable.rfl
          | cons h_step _ ih =>
            have h_step' : (G.induce (S : Set (Fin n))).Adj (ι _) (ι _) := h_step
            exact h_step'.reachable.trans ih
        refine ⟨ι ⟨r, hr_mem⟩, fun ⟨b, hb⟩ => ?_⟩
        rcases Finset.mem_insert.mp hb with hbz | hbS₀
        · subst b
          apply SimpleGraph.Adj.reachable
          change G.Adj r z₀
          exact G.symm ((hadj r (Finset.mem_insert_of_mem hr)).mpr rfl)
        · obtain ⟨p⟩ := hS₀_sub.2.preconnected ⟨r, hr_mem⟩ ⟨b, hbS₀⟩
          exact hι_walk _ _ p
  have leaf_ext_moments : ∀ (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) (z₀ r : Fin n),
      z₀ ∉ U → r ∈ U → (∀ v ∈ insert z₀ U, G.Adj z₀ v ↔ v = r) →
      rootedCount G (insert z₀ U) z₀ = rootedCount G U r + 1 ∧
      rootedOrderSum G (insert z₀ U) z₀ = rootedOrderSum G U r + rootedCount G U r + 1 ∧
      (subtreesIn G (insert z₀ U)).card = (subtreesIn G U).card + rootedCount G U r + 1 ∧
      (∑ S ∈ subtreesIn G (insert z₀ U), S.card) =
        (∑ S ∈ subtreesIn G U, S.card) + rootedOrderSum G U r + rootedCount G U r + 1 ∧
      rootedCount G (insert z₀ U) r = 2 * rootedCount G U r ∧
      rootedOrderSum G (insert z₀ U) r = 2 * rootedOrderSum G U r + rootedCount G U r := by
    intro G U z₀ r hz hr hadj
    have h_ext : ∀ S₀ ⊆ U, IsSubtree G (insert z₀ S₀) ↔ S₀ = ∅ ∨ (IsSubtree G S₀ ∧ r ∈ S₀) :=
      fun S₀ hS₀ => isSubtree_insert_leaf_iff G U S₀ z₀ r hz hr hadj hS₀
    have hzr : z₀ ≠ r := fun h => hz (h ▸ hr)
    have h_mem_rooted : ∀ W r' S, S ∈ rootedSubtreesIn G W r' ↔ IsSubtree G S ∧ S ⊆ W ∧ r' ∈ S := by
      intro W r' S
      simp [rootedSubtreesIn, subtrees]
    have h_mem_subtreesIn : ∀ W S, S ∈ subtreesIn G W ↔ IsSubtree G S ∧ S ⊆ W := by
      intro W S
      simp [subtreesIn, subtrees]
    have h_rooted_z : rootedSubtreesIn G (insert z₀ U) z₀ =
        insert ({z₀} : Finset (Fin n)) ((rootedSubtreesIn G U r).image (insert z₀)) := by
      ext S
      simp only [Finset.mem_insert, Finset.mem_image, h_mem_rooted]
      constructor
      · rintro ⟨hS_sub, hS_U, hzS⟩
        let S₀ := S.erase z₀
        have hS₀_U : S₀ ⊆ U := by
          intro v hv
          rcases Finset.mem_insert.mp (hS_U (Finset.mem_of_mem_erase hv)) with rfl | hvU
          · exact False.elim ((Finset.mem_erase.mp hv).1 rfl)
          · exact hvU
        have h_ins : insert z₀ S₀ = S := Finset.insert_erase hzS
        have hS_iff := (h_ext S₀ hS₀_U).mp (h_ins.symm ▸ hS_sub)
        rcases hS_iff with h_emp | ⟨hS₀_tree, hrS₀⟩
        · left
          rw [← h_ins, h_emp, Finset.insert_empty]
        · right
          exact ⟨S₀, ⟨hS₀_tree, hS₀_U, hrS₀⟩, h_ins⟩
      · rintro (rfl | ⟨S₀, ⟨hS₀_tree, hS₀_U, hrS₀⟩, rfl⟩)
        · have h_emp : IsSubtree G (insert z₀ ∅) := (h_ext ∅ (Finset.empty_subset U)).mpr (Or.inl rfl)
          simpa using h_emp
        · refine ⟨(h_ext S₀ hS₀_U).mpr (Or.inr ⟨hS₀_tree, hrS₀⟩),
            Finset.insert_subset_insert z₀ hS₀_U, Finset.mem_insert_self z₀ S₀⟩
    have h_notMem_img : ({z₀} : Finset (Fin n)) ∉ (rootedSubtreesIn G U r).image (insert z₀) := by
      simp only [Finset.mem_image, not_exists, not_and]
      intro S₀ hS₀ h_eq
      have hrS₀ : r ∈ S₀ := ((h_mem_rooted U r S₀).mp hS₀).2.2
      have hrz : r ∈ ({z₀} : Finset (Fin n)) := h_eq ▸ Finset.mem_insert_of_mem hrS₀
      exact hzr (Finset.mem_singleton.mp hrz).symm
    have h_inj : Set.InjOn (insert z₀) (rootedSubtreesIn G U r : Set (Finset (Fin n))) := by
      intro S₁ hS₁ S₂ hS₂ h_eq
      have hz₁ : z₀ ∉ S₁ := fun h => hz (((h_mem_rooted U r S₁).mp hS₁).2.1 h)
      have hz₂ : z₀ ∉ S₂ := fun h => hz (((h_mem_rooted U r S₂).mp hS₂).2.1 h)
      have := congrArg (fun S : Finset (Fin n) => S.erase z₀) h_eq
      simpa [Finset.erase_insert hz₁, Finset.erase_insert hz₂] using this
    have h_rc_z : rootedCount G (insert z₀ U) z₀ = rootedCount G U r + 1 := by
      change (rootedSubtreesIn G (insert z₀ U) z₀).card = (rootedSubtreesIn G U r).card + 1
      rw [h_rooted_z, Finset.card_insert_of_notMem h_notMem_img, Finset.card_image_of_injOn h_inj]
    have h_sum_img : ∑ S ∈ (rootedSubtreesIn G U r).image (insert z₀), S.card =
        rootedOrderSum G U r + rootedCount G U r := by
      rw [Finset.sum_image h_inj]
      have h_congr : ∑ S₀ ∈ rootedSubtreesIn G U r, (insert z₀ S₀).card =
          ∑ S₀ ∈ rootedSubtreesIn G U r, (S₀.card + 1) := by
        refine Finset.sum_congr rfl (fun S₀ hS₀ => ?_)
        have hzS₀ : z₀ ∉ S₀ := fun h => hz (((h_mem_rooted U r S₀).mp hS₀).2.1 h)
        exact Finset.card_insert_of_notMem hzS₀
      rw [h_congr, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
      rfl
    have h_ros_z : rootedOrderSum G (insert z₀ U) z₀ =
        rootedOrderSum G U r + rootedCount G U r + 1 := by
      change ∑ S ∈ rootedSubtreesIn G (insert z₀ U) z₀, S.card =
        rootedOrderSum G U r + rootedCount G U r + 1
      rw [h_rooted_z, Finset.sum_insert h_notMem_img, Finset.card_singleton, h_sum_img]
      omega
    have h_subtrees_union : subtreesIn G (insert z₀ U) =
        subtreesIn G U ∪ rootedSubtreesIn G (insert z₀ U) z₀ := by
      ext S
      simp only [Finset.mem_union, h_mem_subtreesIn, h_mem_rooted]
      constructor
      · rintro ⟨hS_tree, hS_sub⟩
        by_cases hzS : z₀ ∈ S
        · exact Or.inr ⟨hS_tree, hS_sub, hzS⟩
        · left
          refine ⟨hS_tree, fun v hv => ?_⟩
          rcases Finset.mem_insert.mp (hS_sub hv) with rfl | hvU
          · exact False.elim (hzS hv)
          · exact hvU
      · rintro (⟨hS_tree, hS_U⟩ | ⟨hS_tree, hS_sub, _⟩)
        · exact ⟨hS_tree, Finset.Subset.trans hS_U (Finset.subset_insert z₀ U)⟩
        · exact ⟨hS_tree, hS_sub⟩
    have h_subtrees_disj : Disjoint (subtreesIn G U) (rootedSubtreesIn G (insert z₀ U) z₀) := by
      rw [Finset.disjoint_left]
      intro S hS₁ hS₂
      have hS_U : S ⊆ U := ((h_mem_subtreesIn U S).mp hS₁).2
      exact hz (hS_U ((h_mem_rooted (insert z₀ U) z₀ S).mp hS₂).2.2)
    have h_sc_z : (subtreesIn G (insert z₀ U)).card =
        (subtreesIn G U).card + rootedCount G U r + 1 := by
      rw [h_subtrees_union, Finset.card_union_of_disjoint h_subtrees_disj]
      change (subtreesIn G U).card + rootedCount G (insert z₀ U) z₀ = _
      rw [h_rc_z]
      omega
    have h_sos_z : (∑ S ∈ subtreesIn G (insert z₀ U), S.card) =
        (∑ S ∈ subtreesIn G U, S.card) + rootedOrderSum G U r + rootedCount G U r + 1 := by
      rw [h_subtrees_union, Finset.sum_union h_subtrees_disj]
      change (∑ S ∈ subtreesIn G U, S.card) + rootedOrderSum G (insert z₀ U) z₀ = _
      rw [h_ros_z]
      omega
    have h_rooted_r : rootedSubtreesIn G (insert z₀ U) r =
        rootedSubtreesIn G U r ∪ (rootedSubtreesIn G U r).image (insert z₀) := by
      ext S
      simp only [Finset.mem_union, Finset.mem_image, h_mem_rooted]
      constructor
      · rintro ⟨hS_tree, hS_sub, hrS⟩
        by_cases hzS : z₀ ∈ S
        · right
          let S₀ := S.erase z₀
          have hS₀_U : S₀ ⊆ U := by
            intro v hv
            rcases Finset.mem_insert.mp (hS_sub (Finset.mem_of_mem_erase hv)) with rfl | hvU
            · exact False.elim ((Finset.mem_erase.mp hv).1 rfl)
            · exact hvU
          have h_ins : insert z₀ S₀ = S := Finset.insert_erase hzS
          have hrS₀ : r ∈ S₀ := Finset.mem_erase.mpr ⟨hzr.symm, hrS⟩
          have hS_iff := (h_ext S₀ hS₀_U).mp (h_ins.symm ▸ hS_tree)
          rcases hS_iff with h_emp | ⟨hS₀_tree, _⟩
          · simp [h_emp] at hrS₀
          · exact ⟨S₀, ⟨hS₀_tree, hS₀_U, hrS₀⟩, h_ins⟩
        · left
          refine ⟨hS_tree, fun v hv => ?_, hrS⟩
          rcases Finset.mem_insert.mp (hS_sub hv) with rfl | hvU
          · exact False.elim (hzS hv)
          · exact hvU
      · rintro (⟨hS_tree, hS_U, hrS⟩ | ⟨S₀, ⟨hS₀_tree, hS₀_U, hrS₀⟩, rfl⟩)
        · exact ⟨hS_tree, Finset.Subset.trans hS_U (Finset.subset_insert z₀ U), hrS⟩
        · exact ⟨(h_ext S₀ hS₀_U).mpr (Or.inr ⟨hS₀_tree, hrS₀⟩),
            Finset.insert_subset_insert z₀ hS₀_U, Finset.mem_insert_of_mem hrS₀⟩
    have h_rooted_r_disj : Disjoint (rootedSubtreesIn G U r)
        ((rootedSubtreesIn G U r).image (insert z₀)) := by
      rw [Finset.disjoint_left]
      intro S hS₁ hS₂
      have hS_U : S ⊆ U := ((h_mem_rooted U r S).mp hS₁).2.1
      rcases Finset.mem_image.mp hS₂ with ⟨S₀, _, rfl⟩
      exact hz (hS_U (Finset.mem_insert_self z₀ S₀))
    have h_rc_r : rootedCount G (insert z₀ U) r = 2 * rootedCount G U r := by
      change (rootedSubtreesIn G (insert z₀ U) r).card = 2 * (rootedSubtreesIn G U r).card
      rw [h_rooted_r, Finset.card_union_of_disjoint h_rooted_r_disj, Finset.card_image_of_injOn h_inj]
      omega
    have h_ros_r : rootedOrderSum G (insert z₀ U) r =
        2 * rootedOrderSum G U r + rootedCount G U r := by
      change ∑ S ∈ rootedSubtreesIn G (insert z₀ U) r, S.card =
        2 * rootedOrderSum G U r + rootedCount G U r
      rw [h_rooted_r, Finset.sum_union h_rooted_r_disj, h_sum_img]
      change rootedOrderSum G U r + (rootedOrderSum G U r + rootedCount G U r) = _
      omega
    exact ⟨h_rc_z, h_ros_z, h_sc_z, h_sos_z, h_rc_r, h_ros_r⟩
  have reattachLeaf_subtreesIn_eq : ∀ (G : SimpleGraph (Fin n)) (x w₀ r : Fin n) (hxw : x ≠ w₀) (U : Finset (Fin n)),
      x ∉ U →
      subtreesIn (reattachLeaf G x w₀ hxw) U = subtreesIn G U ∧
      rootedCount (reattachLeaf G x w₀ hxw) U r = rootedCount G U r ∧
      rootedOrderSum (reattachLeaf G x w₀ hxw) U r = rootedOrderSum G U r := by
    intro G x w₀ r hxw U hx
    let G' := reattachLeaf G x w₀ hxw
    have h_induce : ∀ S : Finset (Fin n), S ⊆ U →
        G'.induce (S : Set (Fin n)) = G.induce (S : Set (Fin n)) := by
      intro S hS
      ext ⟨a, ha⟩ ⟨b, hb⟩
      have hax : a ≠ x := fun h => hx (h ▸ hS ha)
      have hbx : b ≠ x := fun h => hx (h ▸ hS hb)
      change G'.Adj a b ↔ G.Adj a b
      simp [G', reattachLeaf, hax, hbx]
    have h_sub : subtreesIn G' U = subtreesIn G U := by
      ext S
      simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
      refine and_congr_left (fun hSU => ?_)
      dsimp [IsSubtree]
      rw [h_induce S hSU]
    have h_rooted : rootedSubtreesIn G' U r = rootedSubtreesIn G U r := by
      ext S
      simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
      refine and_congr_left (fun hSU => ?_)
      dsimp [IsSubtree]
      rw [h_induce S hSU.1]
    refine ⟨h_sub, ?_, ?_⟩
    · dsimp [rootedCount]; rw [h_rooted]
    · dsimp [rootedOrderSum]; rw [h_rooted]
  
  have isBridgeJoin_symm : ∀ {G : SimpleGraph (Fin n)} {U₁ U₂ : Finset (Fin n)} {r₁ r₂ : Fin n},
      IsBridgeJoin G U₁ U₂ r₁ r₂ → IsBridgeJoin G U₂ U₁ r₂ r₁ := by
    intro G U₁ U₂ r₁ r₂ hJ
    rcases hJ with ⟨h_disj, hr₁, hr₂, hadj, h_bridge⟩
    refine ⟨h_disj.symm, hr₂, hr₁, G.symm hadj, ?_⟩
    intro u₀ hu₀ v₀ hv₀ huv
    exact (h_bridge v₀ hv₀ u₀ hu₀ (G.symm huv)).symm
  have exists_walk_of_isSubtree : ∀ {G : SimpleGraph (Fin n)} {S : Finset (Fin n)},
      IsSubtree G S → ∀ {a b : Fin n}, a ∈ S → b ∈ S →
      ∃ q : G.Walk a b, ∀ z₀ ∈ q.support, z₀ ∈ S := by
    intro G S hS a b ha hb
    obtain ⟨q₀⟩ := hS.2.preconnected ⟨a, ha⟩ ⟨b, hb⟩
    suffices ∀ {u₀ v₀ : ↑(S : Set (Fin n))} (q : (G.induce (S : Set (Fin n))).Walk u₀ v₀),
        ∃ q' : G.Walk u₀.1 v₀.1, ∀ z₀ ∈ q'.support, z₀ ∈ S from this q₀
    intro u₀ v₀ q
    induction q with
    | @nil u₀ =>
      refine ⟨SimpleGraph.Walk.nil, ?_⟩
      intro z₀ hz₀
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz₀
      rw [hz₀]
      exact Finset.mem_coe.mp u₀.2
    | @cons u₀ c v₀ hadj q' ih =>
      obtain ⟨q₁, hq₁⟩ := ih
      refine ⟨SimpleGraph.Walk.cons hadj q₁, ?_⟩
      intro z₀ hz₀
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz₀
      rcases hz₀ with rfl | hz₀'
      · exact Finset.mem_coe.mp u₀.2
      · exact hq₁ z₀ hz₀'
  have bridge_walk_mem_edges : ∀ {G : SimpleGraph (Fin n)} {U₁ U₂ : Finset (Fin n)} {r₁ r₂ : Fin n},
      IsBridgeJoin G U₁ U₂ r₁ r₂ → ∀ {a b : Fin n} (q : G.Walk a b),
      (∀ z₀ ∈ q.support, z₀ ∈ U₁ ∪ U₂) →
      ((a ∈ U₁ ∧ b ∈ U₂) ∨ (a ∈ U₂ ∧ b ∈ U₁)) →
      s(r₁, r₂) ∈ q.edges := by
    intro G U₁ U₂ r₁ r₂ hJ a b q
    induction q with
    | nil =>
      intro _ h_ab
      rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact False.elim (Finset.disjoint_left.mp hJ.1 ha hb)
      · exact False.elim (Finset.disjoint_left.mp hJ.1 hb ha)
    | @cons a c b h_step q' ih =>
      intro h_supp h_ab
      have hc_mem : c ∈ U₁ ∪ U₂ := h_supp c (by
        simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.start_mem_support])
      have h_supp' : ∀ z₀ ∈ q'.support, z₀ ∈ U₁ ∪ U₂ := fun z₀ hz₀ =>
        h_supp z₀ (by simp [SimpleGraph.Walk.support_cons, hz₀])
      rcases Finset.mem_union.mp hc_mem with hcA | hcB
      · rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ (ih h_supp' (Or.inl ⟨hcA, hb⟩))
        · obtain ⟨hcw, har⟩ := hJ.2.2.2.2 c hcA a ha (G.symm h_step)
          subst hcw har
          rw [SimpleGraph.Walk.edges_cons, Sym2.eq_swap]
          exact List.mem_cons_self
      · rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · obtain ⟨haw, hcr⟩ := hJ.2.2.2.2 a ha c hcB h_step
          subst haw hcr
          rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_self
        · rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ (ih h_supp' (Or.inr ⟨hcB, hb⟩))
  have bridge_path_support_left : ∀ {G : SimpleGraph (Fin n)} {U₁ U₂ : Finset (Fin n)} {r₁ r₂ : Fin n},
      IsBridgeJoin G U₁ U₂ r₁ r₂ → ∀ {a b : Fin n} (p : G.Walk a b), p.IsPath →
      (∀ z₀ ∈ p.support, z₀ ∈ U₁ ∪ U₂) → a ∈ U₁ → b ∈ U₁ →
      ∀ z₀ ∈ p.support, z₀ ∈ U₁ := by
    intro G U₁ U₂ r₁ r₂ hJ a b p hp h_supp ha hb z₀ hz₀
    rcases Finset.mem_union.mp (h_supp z₀ hz₀) with hzA | hzB
    · exact hzA
    · exfalso
      let p₁ := p.takeUntil z₀ hz₀
      let p₂ := p.dropUntil z₀ hz₀
      have hp₁_supp : ∀ x ∈ p₁.support, x ∈ U₁ ∪ U₂ :=
        fun x hx => h_supp x (p.support_takeUntil_subset hz₀ hx)
      have hp₂_supp : ∀ x ∈ p₂.support, x ∈ U₁ ∪ U₂ :=
        fun x hx => h_supp x (p.support_dropUntil_subset hz₀ hx)
      have he₁ : s(r₁, r₂) ∈ p₁.edges :=
        bridge_walk_mem_edges hJ p₁ hp₁_supp (Or.inl ⟨ha, hzB⟩)
      have he₂ : s(r₁, r₂) ∈ p₂.edges :=
        bridge_walk_mem_edges hJ p₂ hp₂_supp (Or.inr ⟨hzB, hb⟩)
      have h_nodup : p.edges.Nodup := hp.isTrail.edges_nodup
      have h_edges : p₁.edges ++ p₂.edges = p.edges := by
        rw [← SimpleGraph.Walk.edges_append, p.take_spec hz₀]
      rw [← h_edges, List.nodup_append] at h_nodup
      exact h_nodup.2.2 s(r₁, r₂) he₁ s(r₁, r₂) he₂ rfl
  have bridge_crossing_left : ∀ {G : SimpleGraph (Fin n)} {U₁ U₂ S : Finset (Fin n)} {r₁ r₂ : Fin n},
      IsBridgeJoin G U₁ U₂ r₁ r₂ → S ⊆ U₁ ∪ U₂ →
      IsSubtree G S → (S ∩ U₁).Nonempty → (S ∩ U₂).Nonempty →
      S ∩ U₁ ∈ rootedSubtreesIn G U₁ r₁ := by
    intro G U₁ U₂ S r₁ r₂ hJ hS_sub hS hSA hSB
    obtain ⟨a₀, ha₀⟩ := hSA
    obtain ⟨b₀, hb₀⟩ := hSB
    have ha₀S : a₀ ∈ S := (Finset.mem_inter.mp ha₀).1
    have ha₀A : a₀ ∈ U₁ := (Finset.mem_inter.mp ha₀).2
    have hb₀S : b₀ ∈ S := (Finset.mem_inter.mp hb₀).1
    have hb₀B : b₀ ∈ U₂ := (Finset.mem_inter.mp hb₀).2
    obtain ⟨q, hq_supp⟩ := exists_walk_of_isSubtree hS ha₀S hb₀S
    have hq_AB : ∀ z₀ ∈ q.support, z₀ ∈ U₁ ∪ U₂ := fun z₀ hz₀ => hS_sub (hq_supp z₀ hz₀)
    have he : s(r₁, r₂) ∈ q.edges :=
      bridge_walk_mem_edges hJ q hq_AB (Or.inl ⟨ha₀A, hb₀B⟩)
    have hwS : r₁ ∈ S := hq_supp r₁ (q.fst_mem_support_of_mem_edges he)
    have hwSA : r₁ ∈ S ∩ U₁ := Finset.mem_inter.mpr ⟨hwS, hJ.2.1⟩
    have hSA_subtree : IsSubtree G (S ∩ U₁) := by
      refine ⟨⟨r₁, hwSA⟩, ?_⟩
      have : Nonempty ↑((S ∩ U₁ : Finset (Fin n)) : Set (Fin n)) := ⟨⟨r₁, hwSA⟩⟩
      refine ⟨?_⟩
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      have hxS : x ∈ S := (Finset.mem_inter.mp hx).1
      have hxA : x ∈ U₁ := (Finset.mem_inter.mp hx).2
      have hyS : y ∈ S := (Finset.mem_inter.mp hy).1
      have hyA : y ∈ U₁ := (Finset.mem_inter.mp hy).2
      obtain ⟨q₁, hq₁_supp⟩ := exists_walk_of_isSubtree hS hxS hyS
      let p : G.Walk x y := (q₁.toPath : G.Walk x y)
      have hp_path : p.IsPath := q₁.toPath.2
      have hp_S : ∀ z₀ ∈ p.support, z₀ ∈ S := fun z₀ hz₀ => hq₁_supp z₀ (q₁.support_toPath_subset hz₀)
      have hp_AB : ∀ z₀ ∈ p.support, z₀ ∈ U₁ ∪ U₂ := fun z₀ hz₀ => hS_sub (hp_S z₀ hz₀)
      have hp_A : ∀ z₀ ∈ p.support, z₀ ∈ U₁ :=
        bridge_path_support_left hJ p hp_path hp_AB hxA hyA
      have hp_SA : ∀ z₀ ∈ p.support, z₀ ∈ ((S ∩ U₁ : Finset (Fin n)) : Set (Fin n)) :=
        fun z₀ hz₀ => Finset.mem_inter.mpr ⟨hp_S z₀ hz₀, hp_A z₀ hz₀⟩
      exact (p.induce ((S ∩ U₁ : Finset (Fin n)) : Set (Fin n)) hp_SA).reachable
    simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hSA_subtree, Finset.inter_subset_right, hwSA⟩
  have bridge_union_isSubtree : ∀ {G : SimpleGraph (Fin n)} {U₁ U₂ SA SB : Finset (Fin n)} {r₁ r₂ : Fin n},
      IsBridgeJoin G U₁ U₂ r₁ r₂ →
      SA ∈ rootedSubtreesIn G U₁ r₁ → SB ∈ rootedSubtreesIn G U₂ r₂ →
      IsSubtree G (SA ∪ SB) := by
    intro G U₁ U₂ SA SB r₁ r₂ hJ hSA hSB
    simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hSA hSB
    rcases hSA with ⟨hSA_sub, _, hw_SA⟩
    rcases hSB with ⟨hSB_sub, _, hr_SB⟩
    have hw_U : r₁ ∈ SA ∪ SB := Finset.mem_union_left SB hw_SA
    have hr_U : r₂ ∈ SA ∪ SB := Finset.mem_union_right SA hr_SB
    refine ⟨⟨r₁, hw_U⟩, ?_⟩
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨r₁, hw_U⟩, ?_⟩
    rintro ⟨x, hx⟩
    rcases Finset.mem_union.mp hx with hxA | hxB
    · obtain ⟨q, hq⟩ := exists_walk_of_isSubtree hSA_sub hw_SA hxA
      have hq_U : ∀ z₀ ∈ q.support, z₀ ∈ ((SA ∪ SB : Finset (Fin n)) : Set (Fin n)) :=
        fun z₀ hz₀ => Finset.mem_union_left SB (hq z₀ hz₀)
      exact (q.induce ((SA ∪ SB : Finset (Fin n)) : Set (Fin n)) hq_U).reachable
    · obtain ⟨q, hq⟩ := exists_walk_of_isSubtree hSB_sub hr_SB hxB
      have hq_U : ∀ z₀ ∈ q.support, z₀ ∈ ((SA ∪ SB : Finset (Fin n)) : Set (Fin n)) :=
        fun z₀ hz₀ => Finset.mem_union_right SA (hq z₀ hz₀)
      have hadj_ind : (G.induce ((SA ∪ SB : Finset (Fin n)) : Set (Fin n))).Adj ⟨r₁, hw_U⟩ ⟨r₂, hr_U⟩ :=
        hJ.2.2.2.1
      exact hadj_ind.reachable.trans (q.induce ((SA ∪ SB : Finset (Fin n)) : Set (Fin n)) hq_U).reachable
  have bridge_join_subtree_moments : ∀ (G : SimpleGraph (Fin n)) (U₁ U₂ : Finset (Fin n)) (r₁ r₂ : Fin n),
      IsBridgeJoin G U₁ U₂ r₁ r₂ →
      rootedCount G (U₁ ∪ U₂) r₁ = rootedCount G U₁ r₁ * (1 + rootedCount G U₂ r₂) ∧
      rootedOrderSum G (U₁ ∪ U₂) r₁ =
        rootedOrderSum G U₁ r₁ * (1 + rootedCount G U₂ r₂) + rootedCount G U₁ r₁ * rootedOrderSum G U₂ r₂ ∧
      (subtreesIn G (U₁ ∪ U₂)).card =
        (subtreesIn G U₁).card + (subtreesIn G U₂).card + rootedCount G U₁ r₁ * rootedCount G U₂ r₂ ∧
      (∑ S ∈ subtreesIn G (U₁ ∪ U₂), S.card) =
        (∑ S ∈ subtreesIn G U₁, S.card) + (∑ S ∈ subtreesIn G U₂, S.card) +
          rootedOrderSum G U₁ r₁ * rootedCount G U₂ r₂ + rootedCount G U₁ r₁ * rootedOrderSum G U₂ r₂ := by
    intro G U₁ U₂ r₁ r₂ hJ
    let RA_set := rootedSubtreesIn G U₁ r₁
    let RB_set := rootedSubtreesIn G U₂ r₂
    let φ : Finset (Fin n) × Finset (Fin n) → Finset (Fin n) := fun p => p.1 ∪ p.2
    let M := (RA_set ×ˢ RB_set).image φ
    have h_mem_RA : ∀ S, S ∈ RA_set ↔ IsSubtree G S ∧ S ⊆ U₁ ∧ r₁ ∈ S := by
      intro S; simp [RA_set, rootedSubtreesIn, subtrees]
    have h_mem_RB : ∀ S, S ∈ RB_set ↔ IsSubtree G S ∧ S ⊆ U₂ ∧ r₂ ∈ S := by
      intro S; simp [RB_set, rootedSubtreesIn, subtrees]
    have h_mem_sub : ∀ U' S, S ∈ subtreesIn G U' ↔ IsSubtree G S ∧ S ⊆ U' := by
      intro U' S; simp [subtreesIn, subtrees]
    have h_inter_left : ∀ {X Y : Finset (Fin n)}, X ⊆ U₁ → Y ⊆ U₂ → (X ∪ Y) ∩ U₁ = X := by
      intro X Y hX hY
      ext z₀
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hzX | hzY, hzA⟩
        · exact hzX
        · exact False.elim (Finset.disjoint_left.mp hJ.1 hzA (hY hzY))
      · intro hzX
        exact ⟨Or.inl hzX, hX hzX⟩
    have h_inter_right : ∀ {X Y : Finset (Fin n)}, X ⊆ U₁ → Y ⊆ U₂ → (X ∪ Y) ∩ U₂ = Y := by
      intro X Y hX hY
      ext z₀
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hzX | hzY, hzB⟩
        · exact False.elim (Finset.disjoint_left.mp hJ.1 (hX hzX) hzB)
        · exact hzY
      · intro hzY
        exact ⟨Or.inr hzY, hY hzY⟩
    have h_inj : Set.InjOn φ ((RA_set ×ˢ RB_set : Finset (Finset (Fin n) × Finset (Fin n))) : Set (Finset (Fin n) × Finset (Fin n))) := by
      intro p₁ hp₁ p₂ hp₂ h_eq
      rcases Finset.mem_product.mp (Finset.mem_coe.mp hp₁) with ⟨hp₁A, hp₁B⟩
      rcases Finset.mem_product.mp (Finset.mem_coe.mp hp₂) with ⟨hp₂A, hp₂B⟩
      have h1A : p₁.1 ⊆ U₁ := ((h_mem_RA p₁.1).mp hp₁A).2.1
      have h1B : p₁.2 ⊆ U₂ := ((h_mem_RB p₁.2).mp hp₁B).2.1
      have h2A : p₂.1 ⊆ U₁ := ((h_mem_RA p₂.1).mp hp₂A).2.1
      have h2B : p₂.2 ⊆ U₂ := ((h_mem_RB p₂.2).mp hp₂B).2.1
      have h1 : p₁.1 = p₂.1 := by
        calc p₁.1 = (p₁.1 ∪ p₁.2) ∩ U₁ := (h_inter_left h1A h1B).symm
          _ = (p₂.1 ∪ p₂.2) ∩ U₁ := by rw [show p₁.1 ∪ p₁.2 = p₂.1 ∪ p₂.2 from h_eq]
          _ = p₂.1 := h_inter_left h2A h2B
      have h2 : p₁.2 = p₂.2 := by
        calc p₁.2 = (p₁.1 ∪ p₁.2) ∩ U₂ := (h_inter_right h1A h1B).symm
          _ = (p₂.1 ∪ p₂.2) ∩ U₂ := by rw [show p₁.1 ∪ p₁.2 = p₂.1 ∪ p₂.2 from h_eq]
          _ = p₂.2 := h_inter_right h2A h2B
      exact Prod.ext h1 h2
    have hM_card : M.card = rootedCount G U₁ r₁ * rootedCount G U₂ r₂ := by
      dsimp [M, RA_set, RB_set, rootedCount]
      rw [Finset.card_image_of_injOn h_inj, Finset.card_product]
    have hM_sum : ∑ S ∈ M, S.card =
        rootedOrderSum G U₁ r₁ * rootedCount G U₂ r₂ + rootedCount G U₁ r₁ * rootedOrderSum G U₂ r₂ := by
      dsimp [M]
      rw [Finset.sum_image h_inj, Finset.sum_product]
      have h_inner : ∀ x ∈ RA_set,
          ∑ y ∈ RB_set, (x ∪ y).card = x.card * RB_set.card + ∑ y ∈ RB_set, y.card := by
        intro x hx
        have hx_sub : x ⊆ U₁ := ((h_mem_RA x).mp hx).2.1
        have h_congr : ∑ y ∈ RB_set, (x ∪ y).card = ∑ y ∈ RB_set, (x.card + y.card) := by
          refine Finset.sum_congr rfl fun y hy => ?_
          have hy_sub : y ⊆ U₂ := ((h_mem_RB y).mp hy).2.1
          exact Finset.card_union_of_disjoint (Disjoint.mono hx_sub hy_sub hJ.1)
        rw [h_congr, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
      rw [Finset.sum_congr rfl h_inner, Finset.sum_add_distrib, ← Finset.sum_mul,
        Finset.sum_const, smul_eq_mul]
      rfl
    have h_mem_M : ∀ S : Finset (Fin n),
        S ∈ M ↔ S ∈ subtreesIn G (U₁ ∪ U₂) ∧ (S ∩ U₁).Nonempty ∧ (S ∩ U₂).Nonempty := by
      intro S
      constructor
      · intro hS
        obtain ⟨⟨SA, SB⟩, hp, rfl⟩ := Finset.mem_image.mp hS
        rcases Finset.mem_product.mp hp with ⟨hSA, hSB⟩
        have hSA' := (h_mem_RA SA).mp hSA
        have hSB' := (h_mem_RB SB).mp hSB
        have h_sub_AB : SA ∪ SB ⊆ U₁ ∪ U₂ := Finset.union_subset_union hSA'.2.1 hSB'.2.1
        have h_tree : IsSubtree G (SA ∪ SB) := bridge_union_isSubtree hJ hSA hSB
        have h_in_sub : SA ∪ SB ∈ subtreesIn G (U₁ ∪ U₂) :=
          (h_mem_sub (U₁ ∪ U₂) (SA ∪ SB)).mpr ⟨h_tree, h_sub_AB⟩
        have h_ne_A : ((SA ∪ SB) ∩ U₁).Nonempty := by
          rw [h_inter_left hSA'.2.1 hSB'.2.1]
          exact ⟨r₁, hSA'.2.2⟩
        have h_ne_B : ((SA ∪ SB) ∩ U₂).Nonempty := by
          rw [h_inter_right hSA'.2.1 hSB'.2.1]
          exact ⟨r₂, hSB'.2.2⟩
        exact ⟨h_in_sub, h_ne_A, h_ne_B⟩
      · rintro ⟨hS_in, hSA_ne, hSB_ne⟩
        rcases (h_mem_sub (U₁ ∪ U₂) S).mp hS_in with ⟨hS_tree, hS_sub⟩
        have hSA_mem : S ∩ U₁ ∈ RA_set := bridge_crossing_left hJ hS_sub hS_tree hSA_ne hSB_ne
        have hS_sub' : S ⊆ U₂ ∪ U₁ := by simpa [Finset.union_comm] using hS_sub
        have hSB_mem : S ∩ U₂ ∈ RB_set :=
          bridge_crossing_left (isBridgeJoin_symm hJ) hS_sub' hS_tree hSB_ne hSA_ne
        refine Finset.mem_image.mpr ⟨(S ∩ U₁, S ∩ U₂), Finset.mem_product.mpr ⟨hSA_mem, hSB_mem⟩, ?_⟩
        dsimp [φ]
        rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hS_sub]
    have h_sub_of_inter_empty_right : ∀ {S : Finset (Fin n)}, S ⊆ U₁ ∪ U₂ → S ∩ U₂ = ∅ → S ⊆ U₁ := by
      intro S hS h_emp z₀ hz₀
      rcases Finset.mem_union.mp (hS hz₀) with hzA | hzB
      · exact hzA
      · exfalso
        have : z₀ ∈ (∅ : Finset (Fin n)) := h_emp ▸ Finset.mem_inter.mpr ⟨hz₀, hzB⟩
        exact Finset.notMem_empty z₀ this
    have h_sub_of_inter_empty_left : ∀ {S : Finset (Fin n)}, S ⊆ U₁ ∪ U₂ → S ∩ U₁ = ∅ → S ⊆ U₂ := by
      intro S hS h_emp z₀ hz₀
      rcases Finset.mem_union.mp (hS hz₀) with hzA | hzB
      · exfalso
        have : z₀ ∈ (∅ : Finset (Fin n)) := h_emp ▸ Finset.mem_inter.mpr ⟨hz₀, hzA⟩
        exact Finset.notMem_empty z₀ this
      · exact hzB
    have h_root_disj : Disjoint RA_set M := by
      rw [Finset.disjoint_left]
      intro S hS_RA hS_M
      obtain ⟨_, _, b₀, hb₀⟩ := (h_mem_M S).mp hS_M
      have hS_A : S ⊆ U₁ := ((h_mem_RA S).mp hS_RA).2.1
      exact Finset.disjoint_left.mp hJ.1 (hS_A (Finset.mem_inter.mp hb₀).1) (Finset.mem_inter.mp hb₀).2
    have h_root_part : rootedSubtreesIn G (U₁ ∪ U₂) r₁ = RA_set ∪ M := by
      ext S
      rw [Finset.mem_union, h_mem_M]
      constructor
      · intro hS
        simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hS
        rcases hS with ⟨hS_tree, hS_sub, hwS⟩
        rcases Finset.eq_empty_or_nonempty (S ∩ U₂) with h_emp | hSB_ne
        · left
          exact (h_mem_RA S).mpr ⟨hS_tree, h_sub_of_inter_empty_right hS_sub h_emp, hwS⟩
        · right
          have hS_in : S ∈ subtreesIn G (U₁ ∪ U₂) :=
            (h_mem_sub (U₁ ∪ U₂) S).mpr ⟨hS_tree, hS_sub⟩
          exact ⟨hS_in, ⟨r₁, Finset.mem_inter.mpr ⟨hwS, hJ.2.1⟩⟩, hSB_ne⟩
      · rintro (hS_RA | ⟨hS_in, hSA_ne, hSB_ne⟩)
        · rcases (h_mem_RA S).mp hS_RA with ⟨h1, h2, h3⟩
          simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨h1, Finset.Subset.trans h2 Finset.subset_union_left, h3⟩
        · rcases (h_mem_sub (U₁ ∪ U₂) S).mp hS_in with ⟨h1, h2⟩
          have hSA_mem : S ∩ U₁ ∈ RA_set :=
            bridge_crossing_left hJ h2 h1 hSA_ne hSB_ne
          have hw_SA : r₁ ∈ S ∩ U₁ := ((h_mem_RA (S ∩ U₁)).mp hSA_mem).2.2
          simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨h1, h2, (Finset.mem_inter.mp hw_SA).1⟩
    have h_sub_AB_disj : Disjoint (subtreesIn G U₁) (subtreesIn G U₂) := by
      rw [Finset.disjoint_left]
      intro S hSA hSB
      rcases (h_mem_sub U₁ S).mp hSA with ⟨h1, h2⟩
      rcases (h_mem_sub U₂ S).mp hSB with ⟨_, h4⟩
      obtain ⟨x, hx⟩ := h1.1
      exact Finset.disjoint_left.mp hJ.1 (h2 hx) (h4 hx)
    have h_sub_M_disj : Disjoint (subtreesIn G U₁ ∪ subtreesIn G U₂) M := by
      rw [Finset.disjoint_left]
      intro S hS_AB hS_M
      obtain ⟨_, ⟨a₀, ha₀⟩, ⟨b₀, hb₀⟩⟩ := (h_mem_M S).mp hS_M
      rcases Finset.mem_union.mp hS_AB with hSA | hSB
      · have hS_A : S ⊆ U₁ := ((h_mem_sub U₁ S).mp hSA).2
        exact Finset.disjoint_left.mp hJ.1 (hS_A (Finset.mem_inter.mp hb₀).1) (Finset.mem_inter.mp hb₀).2
      · have hS_B : S ⊆ U₂ := ((h_mem_sub U₂ S).mp hSB).2
        exact Finset.disjoint_left.mp hJ.1 (Finset.mem_inter.mp ha₀).2 (hS_B (Finset.mem_inter.mp ha₀).1)
    have h_sub_part : subtreesIn G (U₁ ∪ U₂) = (subtreesIn G U₁ ∪ subtreesIn G U₂) ∪ M := by
      ext S
      rw [Finset.mem_union, Finset.mem_union, h_mem_M]
      constructor
      · intro hS
        have hS' := hS
        simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hS'
        rcases hS' with ⟨hS_tree, hS_sub⟩
        rcases Finset.eq_empty_or_nonempty (S ∩ U₂) with hB_emp | hSB_ne
        · left; left
          simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hS_tree, h_sub_of_inter_empty_right hS_sub hB_emp⟩
        · rcases Finset.eq_empty_or_nonempty (S ∩ U₁) with hA_emp | hSA_ne
          · left; right
            simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hS_tree, h_sub_of_inter_empty_left hS_sub hA_emp⟩
          · right
            exact ⟨hS, hSA_ne, hSB_ne⟩
      · rintro ((hSA | hSB) | ⟨hS, _, _⟩)
        · simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hSA ⊢
          exact ⟨hSA.1, Finset.Subset.trans hSA.2 Finset.subset_union_left⟩
        · simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hSB ⊢
          exact ⟨hSB.1, Finset.Subset.trans hSB.2 Finset.subset_union_right⟩
        · exact hS
    have h_eq1 : rootedCount G (U₁ ∪ U₂) r₁ = rootedCount G U₁ r₁ * (1 + rootedCount G U₂ r₂) := by
      dsimp [rootedCount]
      rw [h_root_part, Finset.card_union_of_disjoint h_root_disj, hM_card]
      dsimp [RA_set, rootedCount]
      ring
    have h_eq2 : rootedOrderSum G (U₁ ∪ U₂) r₁ =
        rootedOrderSum G U₁ r₁ * (1 + rootedCount G U₂ r₂) + rootedCount G U₁ r₁ * rootedOrderSum G U₂ r₂ := by
      dsimp [rootedOrderSum]
      rw [h_root_part, Finset.sum_union h_root_disj, hM_sum]
      dsimp [RA_set, rootedOrderSum]
      ring
    have h_eq3 : (subtreesIn G (U₁ ∪ U₂)).card =
        (subtreesIn G U₁).card + (subtreesIn G U₂).card + rootedCount G U₁ r₁ * rootedCount G U₂ r₂ := by
      rw [h_sub_part, Finset.card_union_of_disjoint h_sub_M_disj,
        Finset.card_union_of_disjoint h_sub_AB_disj, hM_card]
    have h_eq4 : (∑ S ∈ subtreesIn G (U₁ ∪ U₂), S.card) =
        (∑ S ∈ subtreesIn G U₁, S.card) + (∑ S ∈ subtreesIn G U₂, S.card) +
          rootedOrderSum G U₁ r₁ * rootedCount G U₂ r₂ + rootedCount G U₁ r₁ * rootedOrderSum G U₂ r₂ := by
      rw [h_sub_part, Finset.sum_union h_sub_M_disj,
        Finset.sum_union h_sub_AB_disj, hM_sum]
      ring
    exact ⟨h_eq1, h_eq2, h_eq3, h_eq4⟩
  have singleton_subtree_moments : ∀ (U : Finset (Fin n)) (r : Fin n),
      r ∈ U → U.card ≤ 1 →
      rootedCount T U r = 1 ∧
      rootedOrderSum T U r = 1 ∧
      (subtreesIn T U).card = 1 ∧
      (∑ S ∈ subtreesIn T U, S.card) = 1 := by
    intro U r hr hle
    have hU_eq : U = {r} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      refine ⟨hr, fun x hx => Finset.card_le_one.mp hle x hx r hr⟩
    subst hU_eq
    have hr_sub : IsSubtree T {r} := by
      refine ⟨Finset.singleton_nonempty r, ?_⟩
      have : Nonempty ↑(({r} : Finset (Fin n)) : Set (Fin n)) := ⟨⟨r, by simp⟩⟩
      refine ⟨?_⟩
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      have ha' : a = r := by simpa using ha
      have hb' : b = r := by simpa using hb
      have hab : (⟨a, ha⟩ : ↑(({r} : Finset (Fin n)) : Set (Fin n))) = ⟨b, hb⟩ :=
        Subtype.ext (ha'.trans hb'.symm)
      rw [hab]
    have h_sub_eq : subtreesIn T {r} = {{r}} := by
      ext S
      simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h_ne, _⟩, h_sub⟩
        rcases Finset.subset_singleton_iff.mp h_sub with rfl | rfl
        · exact False.elim (Finset.not_nonempty_empty h_ne)
        · rfl
      · rintro rfl
        exact ⟨hr_sub, Finset.Subset.refl _⟩
    have h_root_eq : rootedSubtreesIn T {r} r = {{r}} := by
      ext S
      simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h_ne, _⟩, h_sub, _⟩
        rcases Finset.subset_singleton_iff.mp h_sub with rfl | rfl
        · exact False.elim (Finset.not_nonempty_empty h_ne)
        · rfl
      · rintro rfl
        exact ⟨hr_sub, Finset.Subset.refl _, Finset.mem_singleton_self r⟩
    simp [rootedCount, rootedOrderSum, h_sub_eq, h_root_eq]
  have subtree_exists_root_bridge_split : ∀ (U : Finset (Fin n)) (r : Fin n),
      IsSubtree T U → r ∈ U → 2 ≤ U.card →
      ∃ (U₁ U₂ : Finset (Fin n)) (r₂ : Fin n),
        U = U₁ ∪ U₂ ∧ IsSubtree T U₁ ∧ IsSubtree T U₂ ∧ IsBridgeJoin T U₁ U₂ r r₂ := by
    intro U r hU hr hge2
    obtain ⟨u₀, hu₀, huw⟩ := Finset.exists_mem_ne (by omega : 1 < U.card) r
    obtain ⟨p₀⟩ := hU.2.preconnected ⟨r, hr⟩ ⟨u₀, hu₀⟩
    have h_adj_exists : ∃ r₂ ∈ U, T.Adj r r₂ := by
      cases p₀ with
      | nil => exact False.elim (huw rfl)
      | @cons _ r' _ hadj _ => exact ⟨r'.1, r'.2, hadj⟩
    obtain ⟨r₂, hr₂_U, hadj_wr⟩ := h_adj_exists
    let T₀ := T \ SimpleGraph.fromEdgeSet {s(r, r₂)}
    have h_bridge_wr : T.IsBridge s(r, r₂) :=
      SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.IsAcyclic hadj_wr
    have h_not_reach : ¬ T₀.Reachable r r₂ :=
      (SimpleGraph.isBridge_iff.mp h_bridge_wr).2
    let U₁ := U.filter (fun v => T₀.Reachable r v)
    let U₂ := U \ U₁
    have hU₁_sub : U₁ ⊆ U := Finset.filter_subset _ U
    have hU_eq : U = U₁ ∪ U₂ := (Finset.union_sdiff_of_subset hU₁_sub).symm
    have h_disj : Disjoint U₁ U₂ := Finset.disjoint_sdiff
    have hr_U₁ : r ∈ U₁ := Finset.mem_filter.mpr ⟨hr, SimpleGraph.Reachable.refl r⟩
    have hr₂ : r₂ ∈ U₂ := by
      rw [Finset.mem_sdiff]
      refine ⟨hr₂_U, ?_⟩
      rw [Finset.mem_filter]
      rintro ⟨_, h_reach⟩
      exact h_not_reach h_reach
    have hJ : IsBridgeJoin T U₁ U₂ r r₂ := by
      refine ⟨h_disj, hr_U₁, hr₂, hadj_wr, ?_⟩
      intro a ha b hb hab
      by_cases h_edge : s(a, b) = s(r, r₂)
      · rw [Sym2.eq_iff] at h_edge
        rcases h_edge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨rfl, rfl⟩
        · exact False.elim (Finset.disjoint_left.mp h_disj ha hr₂)
      · exfalso
        have hab₀ : T₀.Adj a b := by
          dsimp [T₀]
          rw [SimpleGraph.sdiff_adj, SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff]
          exact ⟨hab, fun ⟨h_eq, _⟩ => h_edge h_eq⟩
        have ha_reach : T₀.Reachable r a := (Finset.mem_filter.mp ha).2
        have hb_reach : T₀.Reachable r b := ha_reach.trans hab₀.reachable
        have hb_U₁ : b ∈ U₁ := Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hb).1, hb_reach⟩
        exact (Finset.mem_sdiff.mp hb).2 hb_U₁
    have hU₁_subtree : IsSubtree T U₁ := by
      refine ⟨⟨r, hr_U₁⟩, ?_⟩
      have : Nonempty ↑(U₁ : Set (Fin n)) := ⟨⟨r, hr_U₁⟩⟩
      refine ⟨?_⟩
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      have hxU : x ∈ U := hU₁_sub hx
      have hyU : y ∈ U := hU₁_sub hy
      obtain ⟨q, hq_supp⟩ := exists_walk_of_isSubtree hU hxU hyU
      let p : T.Walk x y := (q.toPath : T.Walk x y)
      have hp_path : p.IsPath := q.toPath.2
      have hp_supp : ∀ z₀ ∈ p.support, z₀ ∈ U₁ ∪ U₂ := by
        intro z₀ hz₀
        rw [← hU_eq]
        exact hq_supp z₀ (q.support_toPath_subset hz₀)
      have hp_U₁ : ∀ z₀ ∈ p.support, z₀ ∈ (U₁ : Set (Fin n)) :=
        bridge_path_support_left hJ p hp_path hp_supp hx hy
      exact (p.induce (U₁ : Set (Fin n)) hp_U₁).reachable
    have hU₂_subtree : IsSubtree T U₂ := by
      refine ⟨⟨r₂, hr₂⟩, ?_⟩
      have : Nonempty ↑(U₂ : Set (Fin n)) := ⟨⟨r₂, hr₂⟩⟩
      refine ⟨?_⟩
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      have hxU : x ∈ U := Finset.sdiff_subset hx
      have hyU : y ∈ U := Finset.sdiff_subset hy
      obtain ⟨q, hq_supp⟩ := exists_walk_of_isSubtree hU hxU hyU
      let p : T.Walk x y := (q.toPath : T.Walk x y)
      have hp_path : p.IsPath := q.toPath.2
      have hp_supp : ∀ z₀ ∈ p.support, z₀ ∈ U₂ ∪ U₁ := by
        intro z₀ hz₀
        rw [Finset.union_comm, ← hU_eq]
        exact hq_supp z₀ (q.support_toPath_subset hz₀)
      have hp_U₂ : ∀ z₀ ∈ p.support, z₀ ∈ (U₂ : Set (Fin n)) :=
        bridge_path_support_left (isBridgeJoin_symm hJ) p hp_path hp_supp hx hy
      exact (p.induce (U₂ : Set (Fin n)) hp_U₂).reachable
    exact ⟨U₁, U₂, r₂, hU_eq, hU₁_subtree, hU₂_subtree, hJ⟩
  have bridge_join_moment_ineq_step : ∀ (sA tA NA RA sB tB NB RB : ℕ),
      1 ≤ sA → sA ≤ tA → sA ≤ NA → 2 * tA ≤ sA * (sA + 1) → sA * RA ≤ tA * NA →
      1 ≤ sB → sB ≤ tB → sB ≤ NB → 2 * tB ≤ sB * (sB + 1) → sB * RB ≤ tB * NB →
      let s := sA * (1 + sB)
      let t := tA * (1 + sB) + sA * tB
      let N := NA + NB + sA * sB
      let R := RA + RB + tA * sB + sA * tB
      1 ≤ s ∧ s ≤ t ∧ s ≤ N ∧ 2 * t ≤ s * (s + 1) ∧ s * R ≤ t * N := by
    intro sA tA NA RA sB tB NB RB hsA1 hstA hsNA h2tA hlgA hsB1 hstB hsNB h2tB hlgB
    dsimp only
    refine ⟨by nlinarith, by nlinarith, by nlinarith, ?_, ?_⟩
    · zify at hsA1 hstA hsNA h2tA hlgA hsB1 hstB hsNB h2tB hlgB ⊢
      have h_id1 :
          (sA : ℤ) * (1 + sB) * ((sA : ℤ) * (1 + sB) + 1) -
            2 * ((tA : ℤ) * (1 + sB) + (sA : ℤ) * tB) =
          (1 + (sB : ℤ)) * ((sA : ℤ) * (sA + 1) - 2 * tA) +
          (sA : ℤ) * ((sB : ℤ) * (sB + 1) - 2 * tB) +
          (sA : ℤ) * (1 + sB) * (sA - 1) * sB := by ring
      have h1 : 0 ≤ (1 + (sB : ℤ)) * ((sA : ℤ) * (sA + 1) - 2 * tA) :=
        mul_nonneg (by omega) (by omega)
      have h2 : 0 ≤ (sA : ℤ) * ((sB : ℤ) * (sB + 1) - 2 * tB) :=
        mul_nonneg (by omega) (by omega)
      have h3 : 0 ≤ (sA : ℤ) * (1 + sB) * (sA - 1) * sB :=
        mul_nonneg (mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)) (by omega)
      linarith
    · zify at hsA1 hstA hsNA h2tA hlgA hsB1 hstB hsNB h2tB hlgB ⊢
      have h_id2 :
          (sB : ℤ) * (((tA : ℤ) * (1 + sB) + (sA : ℤ) * tB) * ((NA : ℤ) + NB + (sA : ℤ) * sB) -
            (sA : ℤ) * (1 + sB) * ((RA : ℤ) + RB + (tA : ℤ) * sB + (sA : ℤ) * tB)) =
          (sB : ℤ) * (1 + sB) * ((tA : ℤ) * NA - (sA : ℤ) * RA) +
          (sA : ℤ) * (1 + sB) * ((tB : ℤ) * NB - (sB : ℤ) * RB) +
          (sA : ℤ) * sB * tB * ((NA : ℤ) - sA) +
          (NB : ℤ) * (((tA : ℤ) - sA) * sB * (1 + sB) +
            (sA : ℤ) * ((sB : ℤ) * (1 + sB) - tB)) := by ring
      have htB_le : (tB : ℤ) ≤ (sB : ℤ) * (1 + sB) := by linarith
      have h1 : 0 ≤ (sB : ℤ) * (1 + sB) * ((tA : ℤ) * NA - (sA : ℤ) * RA) :=
        mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)
      have h2 : 0 ≤ (sA : ℤ) * (1 + sB) * ((tB : ℤ) * NB - (sB : ℤ) * RB) :=
        mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)
      have h3 : 0 ≤ (sA : ℤ) * sB * tB * ((NA : ℤ) - sA) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)) (by omega)
      have h4 : 0 ≤ (NB : ℤ) * (((tA : ℤ) - sA) * sB * (1 + sB) +
          (sA : ℤ) * ((sB : ℤ) * (1 + sB) - tB)) := by
        refine mul_nonneg (by omega) (add_nonneg ?_ ?_)
        · exact mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)
        · exact mul_nonneg (by omega) (by omega)
      have h_prod : 0 ≤ (sB : ℤ) * (((tA : ℤ) * (1 + sB) + (sA : ℤ) * tB) * ((NA : ℤ) + NB + (sA : ℤ) * sB) -
          (sA : ℤ) * (1 + sB) * ((RA : ℤ) + RB + (tA : ℤ) * sB + (sA : ℤ) * tB)) := by
        linarith
      nlinarith
  have h_ind : ∀ (m : ℕ) (U : Finset (Fin n)) (r : Fin n),
      U.card = m → IsSubtree T U → r ∈ U →
      1 ≤ rootedCount T U r ∧
      rootedCount T U r ≤ rootedOrderSum T U r ∧
      rootedCount T U r ≤ (subtreesIn T U).card ∧
      2 * rootedOrderSum T U r ≤ rootedCount T U r * (rootedCount T U r + 1) ∧
      rootedCount T U r * (∑ S ∈ subtreesIn T U, S.card) ≤
        rootedOrderSum T U r * (subtreesIn T U).card := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro U r hm hU hr
      by_cases hle : U.card ≤ 1
      · obtain ⟨hs, ht, hN, hR⟩ := singleton_subtree_moments U r hr hle
        rw [hs, ht, hN, hR]
        omega
      · push_neg at hle
        obtain ⟨U₁, U₂, r₂, hU_eq, hU₁_sub, hU₂_sub, hJ⟩ :=
          subtree_exists_root_bridge_split U r hU hr hle
        have hU₁_pos : 0 < U₁.card := Finset.card_pos.mpr ⟨r, hJ.2.1⟩
        have hU₂_pos : 0 < U₂.card := Finset.card_pos.mpr ⟨r₂, hJ.2.2.1⟩
        have hU_card : U.card = U₁.card + U₂.card := by
          rw [hU_eq, Finset.card_union_of_disjoint hJ.1]
        have hU₁_lt : U₁.card < m := by omega
        have hU₂_lt : U₂.card < m := by omega
        obtain ⟨hsA1, hstA, hsNA, h2tA, hlgA⟩ := ih U₁.card hU₁_lt U₁ r rfl hU₁_sub hJ.2.1
        obtain ⟨hsB1, hstB, hsNB, h2tB, hlgB⟩ := ih U₂.card hU₂_lt U₂ r₂ rfl hU₂_sub hJ.2.2.1
        obtain ⟨h_s, h_t, h_N, h_R⟩ := bridge_join_subtree_moments T U₁ U₂ r r₂ hJ
        rw [hU_eq, h_s, h_t, h_N, h_R]
        exact bridge_join_moment_ineq_step
          (rootedCount T U₁ r) (rootedOrderSum T U₁ r) (subtreesIn T U₁).card (∑ S ∈ subtreesIn T U₁, S.card)
          (rootedCount T U₂ r₂) (rootedOrderSum T U₂ r₂) (subtreesIn T U₂).card (∑ S ∈ subtreesIn T U₂, S.card)
          hsA1 hstA hsNA h2tA hlgA hsB1 hstB hsNB h2tB hlgB
  
  have cherry_bridge_split_algebraic_contradiction_int :
      ∀ (aZ tAZ NAZ RAZ bZ tBZ NBZ RBZ : ℤ),
        1 ≤ aZ → aZ ≤ tAZ → aZ ≤ NAZ →
        2 * tAZ ≤ aZ * (aZ + 1) → aZ * RAZ ≤ tAZ * NAZ →
        1 ≤ bZ → bZ ≤ tBZ → bZ ≤ NBZ →
        2 * tBZ ≤ bZ * (bZ + 1) → bZ * RBZ ≤ tBZ * NBZ →
        120 * tAZ ≤ 25 * aZ ^ 2 + 48 * aZ →
        (RAZ + RBZ + tAZ * bZ + aZ * tBZ + 7 * (tAZ * (1 + bZ) + aZ * tBZ) + 12 * (aZ * (1 + bZ)) + 3) *
            (NAZ + NBZ + aZ * bZ + 4 * (aZ * (1 + bZ)) + 6) ≤
          (RAZ + RBZ + tAZ * bZ + aZ * tBZ + 4 * (tAZ * (1 + bZ) + aZ * tBZ) + 8 * (aZ * (1 + bZ)) + 10) *
            (NAZ + NBZ + aZ * bZ + 7 * (aZ * (1 + bZ)) + 3) →
        (RAZ + RBZ + 4 * tAZ * (1 + bZ) + 4 * (aZ + 1) * tBZ + 8 * aZ * (1 + bZ) + 8 * bZ + 10) *
            (NAZ + NBZ + aZ * bZ + 4 * (aZ * (1 + bZ)) + 6) ≤
          (RAZ + RBZ + tAZ * bZ + aZ * tBZ + 4 * (tAZ * (1 + bZ) + aZ * tBZ) + 8 * (aZ * (1 + bZ)) + 10) *
            (NAZ + NBZ + 4 * aZ * (1 + bZ) + 4 * bZ + 6) →
        False := by
    intro aZ tAZ NAZ RAZ bZ tBZ NBZ RBZ
      ha1 hatA haNA h2tA hlgA hb1 hbtB hbNB h2tB hlgB hIneqA_Z h_fold h_swing
    let SZ : ℤ := aZ * (1 + bZ)
    let tHZ : ℤ := tAZ * (1 + bZ) + aZ * tBZ
    let NHZ : ℤ := NAZ + NBZ + aZ * bZ
    let RHZ : ℤ := RAZ + RBZ + tAZ * bZ + aZ * tBZ
    let NTZ : ℤ := NHZ + 4 * SZ + 6
    let RTZ : ℤ := RHZ + 4 * tHZ + 8 * SZ + 10
    let NfoldZ : ℤ := NHZ + 7 * SZ + 3
    let RfoldZ : ℤ := RHZ + 7 * tHZ + 12 * SZ + 3
    let NswingZ : ℤ := NAZ + NBZ + 4 * aZ * (1 + bZ) + 4 * bZ + 6
    let RswingZ : ℤ := RAZ + RBZ + 4 * tAZ * (1 + bZ) + 4 * (aZ + 1) * tBZ + 8 * aZ * (1 + bZ) + 8 * bZ + 10
    let F_fold : ℤ := RTZ * NfoldZ - RfoldZ * NTZ
    let F_swing : ℤ := RTZ * NswingZ - RswingZ * NTZ
    let D_lg : ℤ := (tBZ * (1 + 5 * aZ) + bZ * (5 * tAZ + 8 * aZ)) * NTZ - bZ * (1 + 5 * aZ) * RTZ
    let A1 : ℤ := 3 * (SZ * RTZ - tHZ * NTZ) - 4 * SZ * NTZ
    let A2 : ℤ := (5 * aZ * tBZ + 5 * bZ * tAZ + 8 * aZ * bZ) * NTZ - 5 * aZ * bZ * RTZ
    let A3 : ℤ := bZ * (bZ + 1) - 2 * tBZ
    let A4 : ℤ := 25 * aZ ^ 2 + 48 * aZ - 120 * tAZ
    have hF_fold : 0 ≤ F_fold := sub_nonneg.mpr h_fold
    have hF_swing : 0 ≤ F_swing := sub_nonneg.mpr h_swing
    clear h_fold h_swing
    have h_id_lg : 5 * aZ * D_lg =
        5 * aZ * (1 + 5 * aZ) * (tBZ * NBZ - bZ * RBZ) +
        bZ * (1 + 5 * aZ) * (5 * (tAZ * NAZ - aZ * RAZ) + 8 * aZ * (NAZ - aZ) + 30 * (tAZ - aZ) + 28 * aZ) +
        5 * aZ * bZ * (5 * tAZ + 8 * aZ) * (NBZ - bZ) +
        (NAZ + 6 + 4 * aZ) * ((tBZ - bZ) * 5 * aZ * (1 + 5 * aZ) + bZ * (25 * aZ ^ 2 - 3 * aZ - 5 * tAZ)) := by
      dsimp [D_lg, NTZ, RTZ, NHZ, RHZ, SZ, tHZ]
      ring
    have h_id_A2 : (1 + 5 * aZ) * A2 = 5 * aZ * D_lg + bZ * (5 * tAZ + 8 * aZ) * NTZ := by
      dsimp [A2, D_lg]
      ring
    have h_id_fold : (SZ - 1) * A1 = SZ * F_fold + 3 * (tHZ - SZ) * NTZ := by
      dsimp [A1, F_fold, NTZ, RTZ, NfoldZ, RfoldZ, NHZ, RHZ, SZ, tHZ]
      ring
    have h_id_swing : 30 * aZ * (1 + bZ) * F_swing +
        (10 * aZ * bZ * A1 + 24 * (1 + bZ) * A2 + 15 * aZ ^ 2 * A3 * NTZ + bZ * (1 + bZ) * A4 * NTZ) = 0 := by
      dsimp [F_swing, A1, A2, A3, A4, NTZ, RTZ, NswingZ, RswingZ, NHZ, RHZ, SZ, tHZ]
      ring
    have h_25a : 0 < 25 * aZ ^ 2 - 3 * aZ - 5 * tAZ := by
      have h_25a_id : 2 * (25 * aZ ^ 2 - 3 * aZ - 5 * tAZ) =
          5 * (aZ * (aZ + 1) - 2 * tAZ) + aZ * (45 * aZ - 11) := by ring
      have h1 : 0 ≤ aZ * (aZ + 1) - 2 * tAZ := sub_nonneg.mpr h2tA
      have h2 : 0 < aZ * (45 * aZ - 11) := mul_pos (by omega) (by omega)
      omega
    have h_lg1 : 0 ≤ 5 * aZ * (1 + 5 * aZ) * (tBZ * NBZ - bZ * RBZ) :=
      mul_nonneg (mul_nonneg (by omega) (by omega)) (sub_nonneg.mpr hlgB)
    have h_lg2 : 0 ≤ bZ * (1 + 5 * aZ) * (5 * (tAZ * NAZ - aZ * RAZ) + 8 * aZ * (NAZ - aZ) + 30 * (tAZ - aZ) + 28 * aZ) := by
      refine mul_nonneg (mul_nonneg (by omega) (by omega)) ?_
      have h1 : 0 ≤ tAZ * NAZ - aZ * RAZ := sub_nonneg.mpr hlgA
      have h2 : 0 ≤ 8 * aZ * (NAZ - aZ) := mul_nonneg (by omega) (by omega)
      omega
    have h_lg3 : 0 ≤ 5 * aZ * bZ * (5 * tAZ + 8 * aZ) * (NBZ - bZ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)) (by omega)
    have h_lg4 : 0 ≤ (NAZ + 6 + 4 * aZ) * ((tBZ - bZ) * 5 * aZ * (1 + 5 * aZ) + bZ * (25 * aZ ^ 2 - 3 * aZ - 5 * tAZ)) := by
      refine mul_nonneg (by omega) (add_nonneg ?_ ?_)
      · exact mul_nonneg (mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)) (by omega)
      · exact mul_nonneg (by omega) (by omega)
    have h_5a_Dlg : 0 ≤ 5 * aZ * D_lg := by
      rw [h_id_lg]
      omega
    have hSZ : 2 ≤ SZ := by
      change 2 ≤ aZ * (1 + bZ)
      have : 1 * 2 ≤ aZ * (1 + bZ) := mul_le_mul ha1 (by omega) (by omega) (by omega)
      omega
    have hNTZ : 0 < NTZ := by
      change 0 < NAZ + NBZ + aZ * bZ + 4 * SZ + 6
      have : 0 ≤ aZ * bZ := mul_nonneg (by omega) (by omega)
      omega
    have h_A2_rhs : 0 < (1 + 5 * aZ) * A2 := by
      rw [h_id_A2]
      have : 0 < bZ * (5 * tAZ + 8 * aZ) * NTZ :=
        mul_pos (mul_pos (by omega) (by omega)) hNTZ
      omega
    have hA2_pos : 0 < A2 := by
      by_contra h_le
      have : (1 + 5 * aZ) * A2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
      omega
    have htHZ_ge : SZ ≤ tHZ := by
      change aZ * (1 + bZ) ≤ tAZ * (1 + bZ) + aZ * tBZ
      have h1 : aZ * (1 + bZ) ≤ tAZ * (1 + bZ) := mul_le_mul_of_nonneg_right hatA (by omega)
      have h2 : 0 ≤ aZ * tBZ := mul_nonneg (by omega) (by omega)
      omega
    have h_A1_rhs : 0 ≤ (SZ - 1) * A1 := by
      rw [h_id_fold]
      exact add_nonneg (mul_nonneg (by omega) hF_fold) (mul_nonneg (by omega) (by omega))
    have hA1_nonneg : 0 ≤ A1 := by
      by_contra h_lt
      have : (SZ - 1) * A1 < 0 := mul_neg_of_pos_of_neg (by omega) (by omega)
      omega
    have hA3_nonneg : 0 ≤ A3 := sub_nonneg.mpr h2tB
    have hA4_nonneg : 0 ≤ A4 := sub_nonneg.mpr hIneqA_Z
    have h_swing_lhs : 0 ≤ 30 * aZ * (1 + bZ) * F_swing :=
      mul_nonneg (mul_nonneg (by omega) (by omega)) hF_swing
    have h_swing_rhs : 0 < 10 * aZ * bZ * A1 + 24 * (1 + bZ) * A2 + 15 * aZ ^ 2 * A3 * NTZ + bZ * (1 + bZ) * A4 * NTZ := by
      have h1 : 0 ≤ 10 * aZ * bZ * A1 := mul_nonneg (mul_nonneg (by omega) (by omega)) hA1_nonneg
      have h2 : 0 < 24 * (1 + bZ) * A2 := mul_pos (by omega) hA2_pos
      have ha2 : 0 ≤ 15 * aZ ^ 2 := by positivity
      have h3 : 0 ≤ 15 * aZ ^ 2 * A3 * NTZ :=
        mul_nonneg (mul_nonneg ha2 hA3_nonneg) (by omega)
      have h4 : 0 ≤ bZ * (1 + bZ) * A4 * NTZ :=
        mul_nonneg (mul_nonneg (mul_nonneg (by omega) (by omega)) hA4_nonneg) (by omega)
      omega
    omega
  
  have hw_A : w ∈ A := hBridge_z.2.1
  have hz_B : z ∈ B := hBridge_z.2.2.1
  have h_disj_AB : Disjoint A B := hBridge_z.1
  have hA_sub_H : A ⊆ H := hHAB ▸ Finset.subset_union_left
  have hB_sub_H : B ⊆ H := hHAB ▸ Finset.subset_union_right
  have hw_H : w ∈ H := hBridge_u.2.1
  have hz_H : z ∈ H := hB_sub_H hz_B
  have h_not_P_of_H : ∀ x ∈ H, x ≠ u ∧ x ≠ ℓ₁ ∧ x ≠ ℓ₂ := by
    intro x hx
    rw [hH_eq] at hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hx
    exact hx
  obtain ⟨hwu, hw1, hw2⟩ := h_not_P_of_H w hw_H
  obtain ⟨hzu, hz1, hz2⟩ := h_not_P_of_H z hz_H
  have hwz : w ≠ z := fun h => Finset.disjoint_left.mp h_disj_AB hw_A (h ▸ hz_B)
  have h_univ_sub : ∀ (G : SimpleGraph (Fin n)) (U : Finset (Fin n)),
      U = Finset.univ → subtreesIn G U = subtrees G := by
    intro G U hU
    rw [hU]
    ext X
    simp [subtreesIn]
  set a := rootedCount T A w
  set t_A := rootedOrderSum T A w
  set N_A := (subtreesIn T A).card
  set R_A := ∑ X ∈ subtreesIn T A, X.card
  set b := rootedCount T B z
  set t_B := rootedOrderSum T B z
  set N_B := (subtreesIn T B).card
  set R_B := ∑ X ∈ subtreesIn T B, X.card
  set S := rootedCount T H w
  set t_H := rootedOrderSum T H w
  set N_H := (subtreesIn T H).card
  set R_H := ∑ X ∈ subtreesIn T H, X.card
  obtain ⟨ha1, hatA, haNA, h2tA, hlgA⟩ := h_ind A.card A w rfl hA hw_A
  obtain ⟨hb1, hbtB, hbNB, h2tB, hlgB⟩ := h_ind B.card B z rfl hB hz_B
  obtain ⟨hS_eq, htH_eq, hNH_eq, hRH_eq⟩ := bridge_join_subtree_moments T A B w z hBridge_z
  rw [← hHAB] at hS_eq htH_eq hNH_eq hRH_eq
  change S = a * (1 + b) at hS_eq
  change t_H = t_A * (1 + b) + a * t_B at htH_eq
  change N_H = N_A + N_B + a * b at hNH_eq
  change R_H = R_A + R_B + t_A * b + a * t_B at hRH_eq
  
  let T₁ := reattachLeaf T ℓ₁ w hw1.symm
  let T_fold := reattachLeaf T₁ ℓ₂ w hw2.symm
  have hT₁_tree : T₁.IsTree := h_reattachLeaf_isTree T ℓ₁ u w hw1.symm hT hLeaf1
  have hLeaf2_T₁ : IsLeafIn T₁ ℓ₂ u := by
    intro v
    change (ℓ₂ ≠ ℓ₁ ∧ v ≠ ℓ₁ ∧ T.Adj ℓ₂ v) ∨ (ℓ₂ = ℓ₁ ∧ v = w) ∨ (ℓ₂ = w ∧ v = ℓ₁) ↔ v = u
    constructor
    · rintro (⟨_, _, hv⟩ | ⟨h, _⟩ | ⟨h, _⟩)
      · exact (hLeaf2 v).mp hv
      · exact False.elim (h12 h.symm)
      · exact False.elim (hw2 h.symm)
    · intro hvu
      rw [hvu]
      exact Or.inl ⟨h12.symm, hu1, (hLeaf2 u).mpr rfl⟩
  have hT_fold_tree : T_fold.IsTree := h_reattachLeaf_isTree T₁ ℓ₂ u w hw2.symm hT₁_tree hLeaf2_T₁
  let U₁ : Finset (Fin n) := insert u H
  let U₂ : Finset (Fin n) := insert ℓ₁ U₁
  have hu_not_H : u ∉ H := fun h => (h_not_P_of_H u h).1 rfl
  have h1_not_H : ℓ₁ ∉ H := fun h => (h_not_P_of_H ℓ₁ h).2.1 rfl
  have h2_not_H : ℓ₂ ∉ H := fun h => (h_not_P_of_H ℓ₂ h).2.2 rfl
  have h1_not_U₁ : ℓ₁ ∉ U₁ := by simp [U₁, hu1.symm, h1_not_H]
  have h2_not_U₁ : ℓ₂ ∉ U₁ := by simp [U₁, hu2.symm, h2_not_H]
  have h2_not_U₂ : ℓ₂ ∉ U₂ := by simp [U₂, h12.symm, h2_not_U₁]
  have hu_U₁ : u ∈ U₁ := Finset.mem_insert_self u H
  have hu_U₂ : u ∈ U₂ := Finset.mem_insert_of_mem hu_U₁
  have hw_U₁ : w ∈ U₁ := Finset.mem_insert_of_mem hw_H
  have hw_U₂ : w ∈ U₂ := Finset.mem_insert_of_mem hw_U₁
  have hU₂_univ : insert ℓ₂ U₂ = Finset.univ := by
    ext v
    simp only [U₂, U₁, hH_eq, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_univ,
      true_and, Finset.mem_singleton, iff_true]
    tauto
  have hadj_u_H : ∀ v ∈ insert u H, T.Adj u v ↔ v = w := by
    intro v hv
    have hv1 : v ≠ ℓ₁ := by
      rcases Finset.mem_insert.mp hv with rfl | hvH
      · exact hu1
      · exact (h_not_P_of_H v hvH).2.1
    have hv2 : v ≠ ℓ₂ := by
      rcases Finset.mem_insert.mp hv with rfl | hvH
      · exact hu2
      · exact (h_not_P_of_H v hvH).2.2
    rw [hu_adj v]
    simp [hv1, hv2]
  obtain ⟨h_rc_U₁_u, h_ros_U₁_u, h_sc_U₁, h_sos_U₁, h_rc_U₁_w, h_ros_U₁_w⟩ :=
    leaf_ext_moments T H u w hu_not_H hw_H hadj_u_H
  obtain ⟨_, _, h_sc_U₂_T, h_sos_U₂_T, h_rc_U₂_u, h_ros_U₂_u⟩ :=
    leaf_ext_moments T U₁ ℓ₁ u h1_not_U₁ hu_U₁ (fun v _ => hLeaf1 v)
  obtain ⟨_, _, h_sc_T, h_sos_T, _, _⟩ :=
    leaf_ext_moments T U₂ ℓ₂ u h2_not_U₂ hu_U₂ (fun v _ => hLeaf2 v)
  rw [h_univ_sub T (insert ℓ₂ U₂) hU₂_univ] at h_sc_T h_sos_T
  change rootedCount T U₁ u = S + 1 at h_rc_U₁_u
  change rootedOrderSum T U₁ u = t_H + S + 1 at h_ros_U₁_u
  change (subtreesIn T U₁).card = N_H + S + 1 at h_sc_U₁
  change (∑ X ∈ subtreesIn T U₁, X.card) = R_H + t_H + S + 1 at h_sos_U₁
  change rootedCount T U₁ w = 2 * S at h_rc_U₁_w
  change rootedOrderSum T U₁ w = 2 * t_H + S at h_ros_U₁_w
  change (subtreesIn T U₂).card = (subtreesIn T U₁).card + rootedCount T U₁ u + 1 at h_sc_U₂_T
  change (∑ X ∈ subtreesIn T U₂, X.card) =
    (∑ X ∈ subtreesIn T U₁, X.card) + rootedOrderSum T U₁ u + rootedCount T U₁ u + 1 at h_sos_U₂_T
  change rootedCount T U₂ u = 2 * rootedCount T U₁ u at h_rc_U₂_u
  change rootedOrderSum T U₂ u = 2 * rootedOrderSum T U₁ u + rootedCount T U₁ u at h_ros_U₂_u
  change subtreeCount T = (subtreesIn T U₂).card + rootedCount T U₂ u + 1 at h_sc_T
  change subtreeOrderSum T =
    (∑ X ∈ subtreesIn T U₂, X.card) + rootedOrderSum T U₂ u + rootedCount T U₂ u + 1 at h_sos_T
  have hNT_eq : subtreeCount T = N_H + 4 * S + 6 := by omega
  have hRT_eq : subtreeOrderSum T = R_H + 4 * t_H + 8 * S + 10 := by omega
  obtain ⟨h_sub_T₁_U₁, h_rc_T₁_U₁, h_ros_T₁_U₁⟩ :=
    reattachLeaf_subtreesIn_eq T ℓ₁ w w hw1.symm U₁ h1_not_U₁
  obtain ⟨h_sub_fold_U₁, h_rc_fold_U₁, h_ros_fold_U₁⟩ :=
    reattachLeaf_subtreesIn_eq T₁ ℓ₂ w w hw2.symm U₁ h2_not_U₁
  have hadj_1_fold : ∀ v ∈ insert ℓ₁ U₁, T_fold.Adj ℓ₁ v ↔ v = w := by
    intro v _
    change (ℓ₁ ≠ ℓ₂ ∧ v ≠ ℓ₂ ∧ ((ℓ₁ ≠ ℓ₁ ∧ v ≠ ℓ₁ ∧ T.Adj ℓ₁ v) ∨ (ℓ₁ = ℓ₁ ∧ v = w) ∨ (ℓ₁ = w ∧ v = ℓ₁))) ∨
      (ℓ₁ = ℓ₂ ∧ v = w) ∨ (ℓ₁ = w ∧ v = ℓ₂) ↔ v = w
    constructor
    · rintro (⟨_, _, ⟨h, _, _⟩ | ⟨_, rfl⟩ | ⟨h, _⟩⟩ | ⟨h, _⟩ | ⟨h, _⟩)
      · exact False.elim (h rfl)
      · rfl
      · exact False.elim (hw1 h.symm)
      · exact False.elim (h12 h)
      · exact False.elim (hw1 h.symm)
    · rintro rfl
      exact Or.inl ⟨h12, hw2, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  have hadj_2_fold : ∀ v ∈ insert ℓ₂ U₂, T_fold.Adj ℓ₂ v ↔ v = w := by
    intro v _
    change (ℓ₂ ≠ ℓ₂ ∧ v ≠ ℓ₂ ∧ T₁.Adj ℓ₂ v) ∨ (ℓ₂ = ℓ₂ ∧ v = w) ∨ (ℓ₂ = w ∧ v = ℓ₂) ↔ v = w
    simp [hw2.symm]
  obtain ⟨_, _, h_sc_U₂_fold, h_sos_U₂_fold, h_rc_U₂_fold_w, h_ros_U₂_fold_w⟩ :=
    leaf_ext_moments T_fold U₁ ℓ₁ w h1_not_U₁ hw_U₁ hadj_1_fold
  obtain ⟨_, _, h_sc_fold, h_sos_fold, _, _⟩ :=
    leaf_ext_moments T_fold U₂ ℓ₂ w h2_not_U₂ hw_U₂ hadj_2_fold
  rw [h_univ_sub T_fold (insert ℓ₂ U₂) hU₂_univ] at h_sc_fold h_sos_fold
  change subtreesIn T₁ U₁ = subtreesIn T U₁ at h_sub_T₁_U₁
  change rootedCount T₁ U₁ w = rootedCount T U₁ w at h_rc_T₁_U₁
  change rootedOrderSum T₁ U₁ w = rootedOrderSum T U₁ w at h_ros_T₁_U₁
  change subtreesIn T_fold U₁ = subtreesIn T₁ U₁ at h_sub_fold_U₁
  change rootedCount T_fold U₁ w = rootedCount T₁ U₁ w at h_rc_fold_U₁
  change rootedOrderSum T_fold U₁ w = rootedOrderSum T₁ U₁ w at h_ros_fold_U₁
  change (subtreesIn T_fold U₂).card = (subtreesIn T_fold U₁).card + rootedCount T_fold U₁ w + 1 at h_sc_U₂_fold
  change (∑ X ∈ subtreesIn T_fold U₂, X.card) =
    (∑ X ∈ subtreesIn T_fold U₁, X.card) + rootedOrderSum T_fold U₁ w + rootedCount T_fold U₁ w + 1 at h_sos_U₂_fold
  change rootedCount T_fold U₂ w = 2 * rootedCount T_fold U₁ w at h_rc_U₂_fold_w
  change rootedOrderSum T_fold U₂ w = 2 * rootedOrderSum T_fold U₁ w + rootedCount T_fold U₁ w at h_ros_U₂_fold_w
  change subtreeCount T_fold = (subtreesIn T_fold U₂).card + rootedCount T_fold U₂ w + 1 at h_sc_fold
  change subtreeOrderSum T_fold =
    (∑ X ∈ subtreesIn T_fold U₂, X.card) + rootedOrderSum T_fold U₂ w + rootedCount T_fold U₂ w + 1 at h_sos_fold
  rw [h_sub_fold_U₁, h_sub_T₁_U₁] at h_sc_U₂_fold h_sos_U₂_fold
  rw [h_rc_fold_U₁, h_rc_T₁_U₁] at h_sc_U₂_fold h_sos_U₂_fold h_rc_U₂_fold_w h_ros_U₂_fold_w
  rw [h_ros_fold_U₁, h_ros_T₁_U₁] at h_sos_U₂_fold h_ros_U₂_fold_w
  have hNfold_eq : subtreeCount T_fold = N_H + 7 * S + 3 := by omega
  have hRfold_eq : subtreeOrderSum T_fold = R_H + 7 * t_H + 12 * S + 3 := by omega
  
  let K : Finset (Fin n) := A ∪ ({u, ℓ₁, ℓ₂} : Finset (Fin n))
  let T_swing : SimpleGraph (Fin n) := {
    Adj := fun x y =>
      (¬(x = w ∧ y = z) ∧ ¬(x = z ∧ y = w) ∧ T.Adj x y) ∨
      (x = u ∧ y = z) ∨ (x = z ∧ y = u)
    symm := fun x y h => by
      rcases h with ⟨h1, h2, hxy⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨fun ⟨hyw, hxz⟩ => h2 ⟨hxz, hyw⟩, fun ⟨hyz, hxw⟩ => h1 ⟨hxw, hyz⟩, T.symm hxy⟩
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    loopless := fun x h => by
      rcases h with ⟨_, _, hxx⟩ | ⟨rfl, h⟩ | ⟨h, rfl⟩
      · exact T.loopless x hxx
      · exact hzu.symm h
      · exact hzu h.symm
  }
  have hadj_wu_swing : T_swing.Adj w u :=
    Or.inl ⟨fun ⟨_, huz⟩ => hzu huz.symm, fun ⟨hwz', _⟩ => hwz hwz', hBridge_u.2.2.2.1⟩
  have hadj_uz_swing : T_swing.Adj u z := Or.inr (Or.inl ⟨rfl, rfl⟩)
  have h_reach_wz : T_swing.Reachable w z :=
    hadj_wu_swing.reachable.trans hadj_uz_swing.reachable
  have h_adj_reach : ∀ {x y : Fin n}, T.Adj x y → T_swing.Reachable x y := by
    intro x y hxy
    by_cases h1 : x = w ∧ y = z
    · rcases h1 with ⟨rfl, rfl⟩; exact h_reach_wz
    · by_cases h2 : x = z ∧ y = w
      · rcases h2 with ⟨rfl, rfl⟩; exact h_reach_wz.symm
      · exact SimpleGraph.Adj.reachable (Or.inl ⟨h1, h2, hxy⟩)
  have h_walk_reach : ∀ {x y : Fin n} (p : T.Walk x y), T_swing.Reachable x y := by
    intro x y p
    induction p with
    | nil => exact SimpleGraph.Reachable.rfl
    | cons h_step _ ih => exact (h_adj_reach h_step).trans ih
  have h_conn_swing : T_swing.Connected := by
    have : Nonempty (Fin n) := ⟨w⟩
    refine ⟨fun x y => ?_⟩
    obtain ⟨p⟩ := hT.isConnected.preconnected x y
    exact h_walk_reach p
  have h_disj_KB : Disjoint K B := by
    dsimp [K]
    rw [Finset.disjoint_union_left]
    refine ⟨h_disj_AB, Disjoint.mono_left hB_sub_H hBridge_u.1 |>.symm⟩
  have h_KB_univ : K ∪ B = Finset.univ := by
    ext x
    simp only [K, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ, iff_true]
    by_cases hxP : x = u ∨ x = ℓ₁ ∨ x = ℓ₂
    · exact Or.inl (Or.inr hxP)
    · have hxH : x ∈ H := by
        rw [hH_eq]
        simp [hxP]
      rw [hHAB] at hxH
      rcases Finset.mem_union.mp hxH with hxA | hxB
      · exact Or.inl (Or.inl hxA)
      · exact Or.inr hxB
  have hu_K : u ∈ K := by simp [K]
  have hBridge_KB : IsBridgeJoin T_swing K B u z := by
    refine ⟨h_disj_KB, hu_K, hz_B, hadj_uz_swing, ?_⟩
    intro x hxK y hyB hadj
    have hx_ne_z : x ≠ z := fun h => Finset.disjoint_left.mp h_disj_KB hxK (h ▸ hz_B)
    rcases hadj with ⟨h_not_wz, _, hxy_T⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exfalso
      rcases Finset.mem_union.mp hxK with hxA | hxP
      · exact h_not_wz (hBridge_z.2.2.2.2 x hxA y hyB hxy_T)
      · have h_eq := hBridge_u.2.2.2.2 y (hB_sub_H hyB) x hxP (T.symm hxy_T)
        exact Finset.disjoint_left.mp h_disj_AB hw_A (h_eq.1 ▸ hyB)
    · exact ⟨rfl, rfl⟩
    · exact False.elim (hx_ne_z rfl)
  have h_isBridge_uz : T_swing.IsBridge s(u, z) := by
    rw [SimpleGraph.isBridge_iff_adj_and_forall_walk_mem_edges]
    refine ⟨hadj_uz_swing, fun p => ?_⟩
    apply bridge_walk_mem_edges hBridge_KB p
    · intro x _
      rw [h_KB_univ]
      exact Finset.mem_univ x
    · exact Or.inl ⟨hu_K, hz_B⟩
  have h_acyc_swing : T_swing.IsAcyclic := by
    intro v c hc
    have h_not_mem : s(u, z) ∉ c.edges :=
      (SimpleGraph.isBridge_iff_adj_and_forall_cycle_notMem.mp h_isBridge_uz).2 c hc
    have h_edges : ∀ e ∈ c.edges, e ∈ T.edgeSet := by
      intro e
      refine Sym2.ind (fun x y he => ?_) e
      have hadj : T_swing.Adj x y := c.adj_of_mem_edges he
      rw [SimpleGraph.mem_edgeSet]
      rcases hadj with ⟨_, _, hxy⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hxy
      · exact False.elim (h_not_mem he)
      · rw [Sym2.eq_swap] at he
        exact False.elim (h_not_mem he)
    exact hT.IsAcyclic (c.transfer T h_edges) (hc.transfer h_edges)
  have hT_swing_tree : T_swing.IsTree := ⟨h_conn_swing, h_acyc_swing⟩
  have h_sub_insA : insert u A ⊆ K := by
    intro x hx
    simp only [K, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with rfl | hxA
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl hxA
  have hBridge_insA_B : IsBridgeJoin T_swing (insert u A) B u z := by
    refine ⟨Disjoint.mono_left h_sub_insA h_disj_KB, Finset.mem_insert_self u A, hz_B, hadj_uz_swing, ?_⟩
    intro x hx y hy hadj
    exact hBridge_KB.2.2.2.2 x (h_sub_insA hx) y hy hadj
  have h_swing_induce_eq : ∀ (U : Finset (Fin n)) (r : Fin n),
      (z ∉ U ∨ (w ∉ U ∧ u ∉ U)) →
      subtreesIn T_swing U = subtreesIn T U ∧
      rootedCount T_swing U r = rootedCount T U r ∧
      rootedOrderSum T_swing U r = rootedOrderSum T U r := by
    intro U r hU
    have h_ind_eq : ∀ X : Finset (Fin n), X ⊆ U →
        T_swing.induce (X : Set (Fin n)) = T.induce (X : Set (Fin n)) := by
      intro X hX
      ext ⟨x, hx⟩ ⟨y, hy⟩
      change T_swing.Adj x y ↔ T.Adj x y
      rcases hU with hzU | ⟨hwU, huU⟩
      · have hxz : x ≠ z := fun h => hzU (h ▸ hX hx)
        have hyz : y ≠ z := fun h => hzU (h ▸ hX hy)
        simp [T_swing, hxz, hyz]
      · have hxw : x ≠ w := fun h => hwU (h ▸ hX hx)
        have hyw : y ≠ w := fun h => hwU (h ▸ hX hy)
        have hxu : x ≠ u := fun h => huU (h ▸ hX hx)
        have hyu : y ≠ u := fun h => huU (h ▸ hX hy)
        simp [T_swing, hxw, hyw, hxu, hyu]
    have h_sub : subtreesIn T_swing U = subtreesIn T U := by
      ext X
      simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
      refine and_congr_left (fun hXU => ?_)
      dsimp [IsSubtree]
      rw [h_ind_eq X hXU]
    have h_root : rootedSubtreesIn T_swing U r = rootedSubtreesIn T U r := by
      ext X
      simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
      refine and_congr_left (fun hXU => ?_)
      dsimp [IsSubtree]
      rw [h_ind_eq X hXU.1]
    refine ⟨h_sub, ?_, ?_⟩
    · dsimp [rootedCount]; rw [h_root]
    · dsimp [rootedOrderSum]; rw [h_root]
  have hz_not_A : z ∉ A := Finset.disjoint_right.mp h_disj_AB hz_B
  have hw_not_B : w ∉ B := Finset.disjoint_left.mp h_disj_AB hw_A
  have hu_not_B : u ∉ B := fun h => hu_not_H (hB_sub_H h)
  have hu_not_A : u ∉ A := fun h => hu_not_H (hA_sub_H h)
  obtain ⟨h_sub_swing_A, h_rc_swing_A, h_ros_swing_A⟩ :=
    h_swing_induce_eq A w (Or.inl hz_not_A)
  obtain ⟨h_sub_swing_B, h_rc_swing_B, h_ros_swing_B⟩ :=
    h_swing_induce_eq B z (Or.inr ⟨hw_not_B, hu_not_B⟩)
  have hadj_u_insA : ∀ v ∈ insert u A, T_swing.Adj u v ↔ v = w := by
    intro v hv
    have hv_ne_z : v ≠ z := by
      rcases Finset.mem_insert.mp hv with rfl | hvA
      · exact hzu.symm
      · exact fun h => hz_not_A (h ▸ hvA)
    have hv_ne_1 : v ≠ ℓ₁ := by
      rcases Finset.mem_insert.mp hv with rfl | hvA
      · exact hu1
      · exact (h_not_P_of_H v (hA_sub_H hvA)).2.1
    have hv_ne_2 : v ≠ ℓ₂ := by
      rcases Finset.mem_insert.mp hv with rfl | hvA
      · exact hu2
      · exact (h_not_P_of_H v (hA_sub_H hvA)).2.2
    change (¬(u = w ∧ v = z) ∧ ¬(u = z ∧ v = w) ∧ T.Adj u v) ∨ (u = u ∧ v = z) ∨ (u = z ∧ v = u) ↔ v = w
    simp [hwu.symm, hzu.symm, hv_ne_z, hu_adj v, hv_ne_1, hv_ne_2]
  obtain ⟨h_rc_insA_u, h_ros_insA_u, h_sc_insA, h_sos_insA, _, _⟩ :=
    leaf_ext_moments T_swing A u w hu_not_A hw_A hadj_u_insA
  rw [h_rc_swing_A] at h_rc_insA_u
  rw [h_sub_swing_A, h_rc_swing_A] at h_sc_insA
  rw [h_rc_swing_A, h_ros_swing_A] at h_ros_insA_u
  rw [h_sub_swing_A, h_rc_swing_A, h_ros_swing_A] at h_sos_insA
  let W₁ : Finset (Fin n) := (insert u A) ∪ B
  let W₂ : Finset (Fin n) := insert ℓ₁ W₁
  have hW₁_eq_U₁ : W₁ = U₁ := by
    dsimp [W₁, U₁]
    rw [hHAB, Finset.insert_union]
  obtain ⟨h_rc_W₁_u, h_ros_W₁_u, h_sc_W₁, h_sos_W₁⟩ :=
    bridge_join_subtree_moments T_swing (insert u A) B u z hBridge_insA_B
  rw [h_rc_swing_B] at h_rc_W₁_u
  rw [h_sub_swing_B, h_rc_swing_B] at h_sc_W₁
  rw [h_rc_swing_B, h_ros_swing_B] at h_ros_W₁_u
  rw [h_sub_swing_B, h_rc_swing_B, h_ros_swing_B] at h_sos_W₁
  have hadj_1_swing : ∀ v ∈ insert ℓ₁ W₁, T_swing.Adj ℓ₁ v ↔ v = u := by
    intro v _
    change (¬(ℓ₁ = w ∧ v = z) ∧ ¬(ℓ₁ = z ∧ v = w) ∧ T.Adj ℓ₁ v) ∨ (ℓ₁ = u ∧ v = z) ∨ (ℓ₁ = z ∧ v = u) ↔ v = u
    simp [hw1.symm, hz1.symm, hu1.symm, hLeaf1 v]
  have hadj_2_swing : ∀ v ∈ insert ℓ₂ W₂, T_swing.Adj ℓ₂ v ↔ v = u := by
    intro v _
    change (¬(ℓ₂ = w ∧ v = z) ∧ ¬(ℓ₂ = z ∧ v = w) ∧ T.Adj ℓ₂ v) ∨ (ℓ₂ = u ∧ v = z) ∨ (ℓ₂ = z ∧ v = u) ↔ v = u
    simp [hw2.symm, hz2.symm, hu2.symm, hLeaf2 v]
  have h1_not_W₁ : ℓ₁ ∉ W₁ := hW₁_eq_U₁ ▸ h1_not_U₁
  have hu_W₁ : u ∈ W₁ := hW₁_eq_U₁ ▸ hu_U₁
  have hW₂_eq_U₂ : W₂ = U₂ := by dsimp [W₂, U₂]; rw [hW₁_eq_U₁]
  have h2_not_W₂ : ℓ₂ ∉ W₂ := hW₂_eq_U₂ ▸ h2_not_U₂
  have hu_W₂ : u ∈ W₂ := hW₂_eq_U₂ ▸ hu_U₂
  have hW₂_univ : insert ℓ₂ W₂ = Finset.univ := hW₂_eq_U₂ ▸ hU₂_univ
  obtain ⟨_, _, h_sc_W₂_swing, h_sos_W₂_swing, h_rc_W₂_swing_u, h_ros_W₂_swing_u⟩ :=
    leaf_ext_moments T_swing W₁ ℓ₁ u h1_not_W₁ hu_W₁ hadj_1_swing
  obtain ⟨_, _, h_sc_swing, h_sos_swing, _, _⟩ :=
    leaf_ext_moments T_swing W₂ ℓ₂ u h2_not_W₂ hu_W₂ hadj_2_swing
  rw [h_univ_sub T_swing (insert ℓ₂ W₂) hW₂_univ] at h_sc_swing h_sos_swing
  change subtreeCount T_swing = _ at h_sc_swing
  change subtreeOrderSum T_swing = _ at h_sos_swing
  change rootedCount T_swing W₁ u = _ at h_rc_W₁_u
  change rootedOrderSum T_swing W₁ u = _ at h_ros_W₁_u
  change (subtreesIn T_swing W₁).card = _ at h_sc_W₁
  change (∑ X ∈ subtreesIn T_swing W₁, X.card) = _ at h_sos_W₁
  change rootedCount T_swing W₂ u = _ at h_rc_W₂_swing_u
  change rootedOrderSum T_swing W₂ u = _ at h_ros_W₂_swing_u
  change (subtreesIn T_swing W₂).card = _ at h_sc_W₂_swing
  change (∑ X ∈ subtreesIn T_swing W₂, X.card) = _ at h_sos_W₂_swing
  have hNswing_eq : subtreeCount T_swing = N_A + N_B + 4 * a * (1 + b) + 4 * b + 6 := by
    rw [h_sc_swing, h_sc_W₂_swing, h_rc_W₂_swing_u, h_sc_W₁, h_rc_W₁_u, h_sc_insA, h_rc_insA_u]
    ring
  have hRswing_eq : subtreeOrderSum T_swing =
      R_A + R_B + 4 * t_A * (1 + b) + 4 * (a + 1) * t_B + 8 * a * (1 + b) + 8 * b + 10 := by
    rw [h_sos_swing, h_sos_W₂_swing, h_ros_W₂_swing_u, h_rc_W₂_swing_u,
      h_sos_W₁, h_ros_W₁_u, h_rc_W₁_u, h_sos_insA, h_ros_insA_u, h_rc_insA_u]
    ring
  
  by_contra h_no_imp
  push_neg at h_no_imp
  have h_le_fold : meanSubtreeOrder T_fold ≤ meanSubtreeOrder T := h_no_imp T_fold hT_fold_tree
  have h_le_swing : meanSubtreeOrder T_swing ≤ meanSubtreeOrder T := h_no_imp T_swing hT_swing_tree
  dsimp [meanSubtreeOrder] at h_le_fold h_le_swing
  have hNT_pos : (0 : ℚ) < (subtreeCount T : ℚ) := Nat.cast_pos.mpr (by omega)
  have hNfold_pos : (0 : ℚ) < (subtreeCount T_fold : ℚ) := Nat.cast_pos.mpr (by omega)
  have hNswing_pos : (0 : ℚ) < (subtreeCount T_swing : ℚ) := Nat.cast_pos.mpr (by omega)
  rw [div_le_div_iff₀ hNfold_pos hNT_pos] at h_le_fold
  rw [div_le_div_iff₀ hNswing_pos hNT_pos] at h_le_swing
  have h_fold_nat : subtreeOrderSum T_fold * subtreeCount T ≤ subtreeOrderSum T * subtreeCount T_fold := by
    exact_mod_cast h_le_fold
  have h_swing_nat : subtreeOrderSum T_swing * subtreeCount T ≤ subtreeOrderSum T * subtreeCount T_swing := by
    exact_mod_cast h_le_swing
  rw [hRfold_eq, hNT_eq, hRT_eq, hNfold_eq, hRH_eq, hNH_eq, htH_eq, hS_eq] at h_fold_nat
  rw [hRswing_eq, hNT_eq, hRT_eq, hNswing_eq, hRH_eq, hNH_eq, htH_eq, hS_eq] at h_swing_nat
  exact cherry_bridge_split_algebraic_contradiction_int
    (a : ℤ) (t_A : ℤ) (N_A : ℤ) (R_A : ℤ) (b : ℤ) (t_B : ℤ) (N_B : ℤ) (R_B : ℤ)
    (by exact_mod_cast ha1) (by exact_mod_cast hatA) (by exact_mod_cast haNA)
    (by exact_mod_cast h2tA) (by exact_mod_cast hlgA)
    (by exact_mod_cast hb1) (by exact_mod_cast hbtB) (by exact_mod_cast hbNB)
    (by exact_mod_cast h2tB) (by exact_mod_cast hlgB)
    (by exact_mod_cast hIneqA)
    (by exact_mod_cast h_fold_nat)
    (by exact_mod_cast h_swing_nat)

theorem cherry_three_branch_nonimproving_bounds : ∀ (n : ℕ) (hn : 1 ≤ n) (T : SimpleGraph (Fin n)),
    T.IsTree →
    ∀ (w u ℓ₁ ℓ₂ r_B r_C : Fin n) (H L_c B C : Finset (Fin n)),
      ℓ₁ ≠ ℓ₂ → u ≠ ℓ₁ → u ≠ ℓ₂ →
      H = Finset.univ \ ({u, ℓ₁, ℓ₂} : Finset (Fin n)) →
      IsSubtree T H →
      IsBridgeJoin T H ({u, ℓ₁, ℓ₂} : Finset (Fin n)) w u →
      IsLeafIn T ℓ₁ u → IsLeafIn T ℓ₂ u →
      (∀ v : Fin n, T.Adj u v ↔ v = w ∨ v = ℓ₁ ∨ v = ℓ₂) →
      w ∉ L_c → L_c.card ≤ 1 → IsLeafPacket T L_c w →
      Disjoint (insert w L_c) B → Disjoint (insert w L_c) C → Disjoint B C →
      H = (insert w L_c) ∪ B ∪ C →
      IsSubtree T B → IsSubtree T C →
      IsBridgeJoin T (insert w L_c) B w r_B →
      IsBridgeJoin T ((insert w L_c) ∪ B) C w r_C →
      (¬ ∃ T' : SimpleGraph (Fin n), T'.IsTree ∧ meanSubtreeOrder T < meanSubtreeOrder T') →
      let c := L_c.card
      let p := 2 ^ c
      let x := rootedCount T B r_B
      let t_B := rootedOrderSum T B r_B
      let N_B := unrootedCount T B
      let R_B := unrootedOrderSum T B
      let y := rootedCount T C r_C
      let t_C := rootedOrderSum T C r_C
      let N_C := unrootedCount T C
      let R_C := unrootedOrderSum T C
      let S := p * (1 + x) * (1 + y)
      let t_H := (p + c) * (1 + x) * (1 + y) + p * (1 + y) * t_B + p * (1 + x) * t_C
      let a_B := p * (1 + y)
      let t_AB := (p + c) * (1 + y) + p * t_C
      let a_C := p * (1 + x)
      let t_AC := (p + c) * (1 + x) + p * t_B
      let q := meanSubtreeOrder T
      (5 * (t_H : ℚ) + 8 * (S : ℚ) + (R_B : ℚ) + (R_C : ℚ) + 10 + (c : ℚ) =
        q * (5 * (S : ℚ) + (N_B : ℚ) + (N_C : ℚ) + 6 + (c : ℚ))) ∧
      (3 * (t_H : ℚ) + 4 * (S : ℚ) - 7 ≤ q * (3 * ((S : ℚ) - 1))) ∧
      ((x : ℚ) * (8 - (t_AB : ℚ)) - ((a_B : ℚ) - 4) * (t_B : ℚ) ≤
        q * (x : ℚ) * (4 - (a_B : ℚ))) ∧
      ((y : ℚ) * (8 - (t_AC : ℚ)) - ((a_C : ℚ) - 4) * (t_C : ℚ) ≤
        q * (y : ℚ) * (4 - (a_C : ℚ))) :=
by
  intro n _hn T hT
  classical
  
  let AcyclicOn (G' : SimpleGraph (Fin n)) (U : Finset (Fin n)) : Prop :=
    ∀ (v₀ : Fin n) (walk : G'.Walk v₀ v₀), walk.IsCycle → (∀ v ∈ walk.support, v ∈ U) → False
  have isBridgeJoin_symm : ∀ {G' : SimpleGraph (Fin n)} {U₁ U₂ : Finset (Fin n)} {r₁ r₂ : Fin n},
      IsBridgeJoin G' U₁ U₂ r₁ r₂ → IsBridgeJoin G' U₂ U₁ r₂ r₁ := by
    intro G' U₁ U₂ r₁ r₂ hJ
    rcases hJ with ⟨h_disj, hr₁, hr₂, hadj, h_bridge⟩
    refine ⟨h_disj.symm, hr₂, hr₁, G'.symm hadj, ?_⟩
    intro a ha b hb hab
    exact (h_bridge b hb a ha (G'.symm hab)).symm
  have exists_walk_of_isSubtree : ∀ {G' : SimpleGraph (Fin n)} {U : Finset (Fin n)},
      IsSubtree G' U → ∀ {a b : Fin n}, a ∈ U → b ∈ U →
      ∃ q : G'.Walk a b, ∀ z ∈ q.support, z ∈ U := by
    intro G' U hU a b ha hb
    obtain ⟨q₀⟩ := hU.2.preconnected ⟨a, ha⟩ ⟨b, hb⟩
    suffices ∀ {u₁ v₁ : ↑(U : Set (Fin n))} (q : (G'.induce (U : Set (Fin n))).Walk u₁ v₁),
        ∃ q' : G'.Walk u₁.1 v₁.1, ∀ z ∈ q'.support, z ∈ U from this q₀
    intro u₁ v₁ q
    induction q with
    | @nil u₁ =>
      refine ⟨SimpleGraph.Walk.nil, ?_⟩
      intro z hz
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      rw [hz]
      exact Finset.mem_coe.mp u₁.2
    | @cons u₁ c₁ v₁ hadj q' ih =>
      obtain ⟨q₁, hq₁⟩ := ih
      refine ⟨SimpleGraph.Walk.cons hadj q₁, ?_⟩
      intro z hz
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz'
      · exact Finset.mem_coe.mp u₁.2
      · exact hq₁ z hz'
  have bridge_walk_mem_edges : ∀ {G' : SimpleGraph (Fin n)} {U₁ U₂ : Finset (Fin n)} {r₁ r₂ : Fin n},
      IsBridgeJoin G' U₁ U₂ r₁ r₂ → ∀ {a b : Fin n} (q : G'.Walk a b),
      (∀ z ∈ q.support, z ∈ U₁ ∪ U₂) →
      ((a ∈ U₁ ∧ b ∈ U₂) ∨ (a ∈ U₂ ∧ b ∈ U₁)) →
      s(r₁, r₂) ∈ q.edges := by
    intro G' U₁ U₂ r₁ r₂ hJ a b q
    induction q with
    | nil =>
      intro _ h_ab
      rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact False.elim (Finset.disjoint_left.mp hJ.1 ha hb)
      · exact False.elim (Finset.disjoint_left.mp hJ.1 hb ha)
    | @cons a c₁ b h_step q' ih =>
      intro h_supp h_ab
      have hc_mem : c₁ ∈ U₁ ∪ U₂ := h_supp c₁ (by
        simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.start_mem_support])
      have h_supp' : ∀ z ∈ q'.support, z ∈ U₁ ∪ U₂ := fun z hz =>
        h_supp z (by simp [SimpleGraph.Walk.support_cons, hz])
      rcases Finset.mem_union.mp hc_mem with hcA | hcB
      · rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ (ih h_supp' (Or.inl ⟨hcA, hb⟩))
        · obtain ⟨hcr₁, har₂⟩ := hJ.2.2.2.2 c₁ hcA a ha (G'.symm h_step)
          subst hcr₁ har₂
          rw [SimpleGraph.Walk.edges_cons, Sym2.eq_swap]
          exact List.mem_cons_self
      · rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · obtain ⟨har₁, hcr₂⟩ := hJ.2.2.2.2 a ha c₁ hcB h_step
          subst har₁ hcr₂
          rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_self
        · rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ (ih h_supp' (Or.inr ⟨hcB, hb⟩))
  have bridge_path_support_left : ∀ {G' : SimpleGraph (Fin n)} {U₁ U₂ : Finset (Fin n)} {r₁ r₂ : Fin n},
      IsBridgeJoin G' U₁ U₂ r₁ r₂ → ∀ {a b : Fin n} (p₀ : G'.Walk a b), p₀.IsPath →
      (∀ z ∈ p₀.support, z ∈ U₁ ∪ U₂) → a ∈ U₁ → b ∈ U₁ →
      ∀ z ∈ p₀.support, z ∈ U₁ := by
    intro G' U₁ U₂ r₁ r₂ hJ a b p₀ hp h_supp ha hb z hz
    rcases Finset.mem_union.mp (h_supp z hz) with hzA | hzB
    · exact hzA
    · exfalso
      let p₁ := p₀.takeUntil z hz
      let p₂ := p₀.dropUntil z hz
      have hp₁_supp : ∀ v ∈ p₁.support, v ∈ U₁ ∪ U₂ :=
        fun v hv => h_supp v (p₀.support_takeUntil_subset hz hv)
      have hp₂_supp : ∀ v ∈ p₂.support, v ∈ U₁ ∪ U₂ :=
        fun v hv => h_supp v (p₀.support_dropUntil_subset hz hv)
      have he₁ : s(r₁, r₂) ∈ p₁.edges :=
        bridge_walk_mem_edges hJ p₁ hp₁_supp (Or.inl ⟨ha, hzB⟩)
      have he₂ : s(r₁, r₂) ∈ p₂.edges :=
        bridge_walk_mem_edges hJ p₂ hp₂_supp (Or.inr ⟨hzB, hb⟩)
      have h_nodup : p₀.edges.Nodup := hp.isTrail.edges_nodup
      have h_edges : p₁.edges ++ p₂.edges = p₀.edges := by
        rw [← SimpleGraph.Walk.edges_append, p₀.take_spec hz]
      rw [← h_edges, List.nodup_append] at h_nodup
      exact h_nodup.2.2 s(r₁, r₂) he₁ s(r₁, r₂) he₂ rfl
  have acyclicOn_of_adj_imp : ∀ {G' : SimpleGraph (Fin n)} {U : Finset (Fin n)},
      (∀ a ∈ U, ∀ b ∈ U, G'.Adj a b → T.Adj a b) → AcyclicOn G' U := by
    intro G' U h_adj v₀ walk hc h_supp
    have h_edges : ∀ {a b : Fin n} (p₀ : G'.Walk a b),
        (∀ v ∈ p₀.support, v ∈ U) → ∀ e ∈ p₀.edges, e ∈ T.edgeSet := by
      intro a b p₀
      induction p₀ with
      | nil => intro _ e he; simp at he
      | @cons a v₁ b h_step p' ih =>
        intro hp e he
        have haU : a ∈ U := hp a (by simp)
        have hv₁U : v₁ ∈ U := hp v₁ (by simp [SimpleGraph.Walk.start_mem_support])
        have hp' : ∀ v ∈ p'.support, v ∈ U := fun v hv => hp v (by simp [hv])
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
        rcases he with rfl | he'
        · exact h_adj a haU v₁ hv₁U h_step
        · exact ih hp' e he'
    have he_T := h_edges walk h_supp
    exact hT.2 (walk.transfer T he_T) (hc.transfer he_T)
  have acyclicOn_singleton : ∀ (G' : SimpleGraph (Fin n)) (z : Fin n), AcyclicOn G' {z} := by
    intro G' z
    refine acyclicOn_of_adj_imp (fun a ha b hb hab => ?_)
    have haz : a = z := Finset.mem_singleton.mp ha
    have hbz : b = z := Finset.mem_singleton.mp hb
    subst a b
    exact False.elim (G'.loopless z hab)
  have acyclicOn_bridge_join : ∀ {G' : SimpleGraph (Fin n)} {U₁ U₂ : Finset (Fin n)} {r₁ r₂ : Fin n},
      IsBridgeJoin G' U₁ U₂ r₁ r₂ → AcyclicOn G' U₁ → AcyclicOn G' U₂ → AcyclicOn G' (U₁ ∪ U₂) := by
    intro G' U₁ U₂ r₁ r₂ hJ hA₁ hA₂ v₀ walk hc h_supp
    cases walk with
    | nil => exact hc.ne_nil rfl
    | @cons v₀ v₁ _ h_step p₀ =>
      rcases (SimpleGraph.Walk.cons_isCycle_iff p₀ h_step).mp hc with ⟨hp_path, he_not⟩
      have hv₀_mem : v₀ ∈ U₁ ∪ U₂ := h_supp v₀ (by simp)
      have hv₁_mem : v₁ ∈ U₁ ∪ U₂ := h_supp v₁ (by simp [SimpleGraph.Walk.start_mem_support])
      have hp_supp : ∀ v ∈ p₀.support, v ∈ U₁ ∪ U₂ := fun v hv => h_supp v (by simp [hv])
      rcases Finset.mem_union.mp hv₀_mem with hv₀1 | hv₀2
      · rcases Finset.mem_union.mp hv₁_mem with hv₁1 | hv₁2
        · have hp_U₁ : ∀ v ∈ p₀.support, v ∈ U₁ :=
            bridge_path_support_left hJ p₀ hp_path hp_supp hv₁1 hv₀1
          refine hA₁ v₀ (SimpleGraph.Walk.cons h_step p₀) hc (fun v hv => ?_)
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
          rcases hv with rfl | hv'
          · exact hv₀1
          · exact hp_U₁ v hv'
        · obtain ⟨hv₀r₁, hv₁r₂⟩ := hJ.2.2.2.2 v₀ hv₀1 v₁ hv₁2 h_step
          subst v₀ v₁
          exact he_not (bridge_walk_mem_edges hJ p₀ hp_supp (Or.inr ⟨hv₁2, hv₀1⟩))
      · rcases Finset.mem_union.mp hv₁_mem with hv₁1 | hv₁2
        · obtain ⟨hv₁r₁, hv₀r₂⟩ := hJ.2.2.2.2 v₁ hv₁1 v₀ hv₀2 (G'.symm h_step)
          subst v₁ v₀
          rw [Sym2.eq_swap] at he_not
          exact he_not (bridge_walk_mem_edges hJ p₀ hp_supp (Or.inl ⟨hv₁1, hv₀2⟩))
        · have hp_supp' : ∀ v ∈ p₀.support, v ∈ U₂ ∪ U₁ := by
            intro v hv; rw [Finset.union_comm]; exact hp_supp v hv
          have hp_U₂ : ∀ v ∈ p₀.support, v ∈ U₂ :=
            bridge_path_support_left (isBridgeJoin_symm hJ) p₀ hp_path hp_supp' hv₁2 hv₀2
          refine hA₂ v₀ (SimpleGraph.Walk.cons h_step p₀) hc (fun v hv => ?_)
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
          rcases hv with rfl | hv'
          · exact hv₀2
          · exact hp_U₂ v hv'
  have h_join_sub : ∀ (G' : SimpleGraph (Fin n)) {U₁ U₂ : Finset (Fin n)} {r₁ r₂ : Fin n},
      IsSubtree G' U₁ → IsSubtree G' U₂ → IsBridgeJoin G' U₁ U₂ r₁ r₂ →
      IsSubtree G' (U₁ ∪ U₂) := by
    intro G' U₁ U₂ r₁ r₂ hU₁ hU₂ hJ
    have hr₁ : r₁ ∈ U₁ := hJ.2.1
    have hr₂ : r₂ ∈ U₂ := hJ.2.2.1
    have hadj : G'.Adj r₁ r₂ := hJ.2.2.2.1
    refine ⟨⟨r₁, Finset.mem_union_left U₂ hr₁⟩, ?_⟩
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    let r₁' : (↑(U₁ ∪ U₂ : Finset (Fin n)) : Set (Fin n)) :=
      ⟨r₁, Finset.mem_coe.mpr (Finset.mem_union_left U₂ hr₁)⟩
    let r₂' : (↑(U₁ ∪ U₂ : Finset (Fin n)) : Set (Fin n)) :=
      ⟨r₂, Finset.mem_coe.mpr (Finset.mem_union_right U₁ hr₂)⟩
    let ι₁ : G'.induce (U₁ : Set (Fin n)) →g G'.induce ((U₁ ∪ U₂ : Finset (Fin n)) : Set (Fin n)) :=
      { toFun := fun z => ⟨z.1, Finset.mem_coe.mpr (Finset.mem_union_left U₂ (Finset.mem_coe.mp z.2))⟩
        map_rel' := fun h => h }
    let ι₂ : G'.induce (U₂ : Set (Fin n)) →g G'.induce ((U₁ ∪ U₂ : Finset (Fin n)) : Set (Fin n)) :=
      { toFun := fun z => ⟨z.1, Finset.mem_coe.mpr (Finset.mem_union_right U₁ (Finset.mem_coe.mp z.2))⟩
        map_rel' := fun h => h }
    refine ⟨r₁', fun z => ?_⟩
    rcases Finset.mem_union.mp (Finset.mem_coe.mp z.2) with hz₁ | hz₂
    · obtain ⟨q₀⟩ := hU₁.2.preconnected ⟨r₁, Finset.mem_coe.mpr hr₁⟩ ⟨z.1, Finset.mem_coe.mpr hz₁⟩
      exact ⟨q₀.map ι₁⟩
    · have hr₁₂ : (G'.induce ((U₁ ∪ U₂ : Finset (Fin n)) : Set (Fin n))).Reachable r₁' r₂' :=
        SimpleGraph.Adj.reachable hadj
      obtain ⟨q₀⟩ := hU₂.2.preconnected ⟨r₂, Finset.mem_coe.mpr hr₂⟩ ⟨z.1, Finset.mem_coe.mpr hz₂⟩
      exact hr₁₂.trans ⟨q₀.map ι₂⟩
  have isTree_of_univ : ∀ (G' : SimpleGraph (Fin n)),
      IsSubtree G' Finset.univ → AcyclicOn G' Finset.univ → G'.IsTree := by
    intro G' h_sub h_acyc
    refine ⟨?_, fun v₀ walk hc => h_acyc v₀ walk hc (fun v _ => Finset.mem_univ v)⟩
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    let v₀ : Fin n := ⟨0, _hn⟩
    refine ⟨v₀, fun z => ?_⟩
    obtain ⟨p₀⟩ := h_sub.2.preconnected
      ⟨v₀, Finset.mem_coe.mpr (Finset.mem_univ v₀)⟩
      ⟨z, Finset.mem_coe.mpr (Finset.mem_univ z)⟩
    let proj : G'.induce ((Finset.univ : Finset (Fin n)) : Set (Fin n)) →g G' :=
      { toFun := Subtype.val
        map_rel' := fun h => h }
    exact ⟨p₀.map proj⟩
  have h_sing : ∀ (G' : SimpleGraph (Fin n)) (v : Fin n),
      IsSubtree G' {v} ∧
      rootedCount G' {v} v = 1 ∧
      rootedOrderSum G' {v} v = 1 ∧
      unrootedCount G' {v} = 1 ∧
      unrootedOrderSum G' {v} = 1 := by
    intro G' v
    have h_sub : IsSubtree G' {v} := by
      refine ⟨Finset.singleton_nonempty v, ?_⟩
      rw [SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨⟨v, by simp⟩, fun ⟨z, hz⟩ => ?_⟩
      have hzv : z = v := by simpa using hz
      subst hzv
      exact SimpleGraph.Reachable.rfl
    have h_subtreesIn : subtreesIn G' {v} = {{v}} := by
      ext S₀
      simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hS_tree, hS_sub⟩
        rcases Finset.subset_singleton_iff.mp hS_sub with rfl | rfl
        · exact False.elim (Finset.not_nonempty_empty hS_tree.1)
        · rfl
      · rintro rfl
        exact ⟨h_sub, Finset.Subset.refl _⟩
    have h_rootedIn : rootedSubtreesIn G' {v} v = {{v}} := by
      ext S₀
      simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hS_tree, hS_sub, _⟩
        rcases Finset.subset_singleton_iff.mp hS_sub with rfl | rfl
        · exact False.elim (Finset.not_nonempty_empty hS_tree.1)
        · rfl
      · rintro rfl
        exact ⟨h_sub, Finset.Subset.refl _, Finset.mem_singleton_self v⟩
    refine ⟨h_sub, ?_, ?_, ?_, ?_⟩
    · dsimp [rootedCount]; rw [h_rootedIn]; simp
    · dsimp [rootedOrderSum]; rw [h_rootedIn]; simp
    · dsimp [unrootedCount]; rw [h_subtreesIn]; simp
    · dsimp [unrootedOrderSum]; rw [h_subtreesIn]; simp
  have bridge_join_both_moments : ∀ (G' : SimpleGraph (Fin n))
      (U₁ U₂ : Finset (Fin n)) (r₁ r₂ : Fin n),
      IsBridgeJoin G' U₁ U₂ r₁ r₂ →
      (rootedCount G' (U₁ ∪ U₂) r₁ = rootedCount G' U₁ r₁ * (1 + rootedCount G' U₂ r₂) ∧
       rootedOrderSum G' (U₁ ∪ U₂) r₁ =
         rootedOrderSum G' U₁ r₁ * (1 + rootedCount G' U₂ r₂) +
         rootedCount G' U₁ r₁ * rootedOrderSum G' U₂ r₂) ∧
      (unrootedCount G' (U₁ ∪ U₂) =
         unrootedCount G' U₁ + unrootedCount G' U₂ + rootedCount G' U₁ r₁ * rootedCount G' U₂ r₂ ∧
       unrootedOrderSum G' (U₁ ∪ U₂) =
         unrootedOrderSum G' U₁ + unrootedOrderSum G' U₂ +
         rootedOrderSum G' U₁ r₁ * rootedCount G' U₂ r₂ +
         rootedCount G' U₁ r₁ * rootedOrderSum G' U₂ r₂) := by
    intro G' A B w₀ r₀ hJ
    have bridge_crossing_left : ∀ {A' B' S₀ : Finset (Fin n)} {w' r' : Fin n},
        IsBridgeJoin G' A' B' w' r' → S₀ ⊆ A' ∪ B' →
        IsSubtree G' S₀ → (S₀ ∩ A').Nonempty → (S₀ ∩ B').Nonempty →
        S₀ ∩ A' ∈ rootedSubtreesIn G' A' w' := by
      intro A' B' S₀ w' r' hJ' hS_sub hS hSA hSB
      obtain ⟨a₀, ha₀⟩ := hSA
      obtain ⟨b₀, hb₀⟩ := hSB
      have ha₀S : a₀ ∈ S₀ := (Finset.mem_inter.mp ha₀).1
      have ha₀A : a₀ ∈ A' := (Finset.mem_inter.mp ha₀).2
      have hb₀S : b₀ ∈ S₀ := (Finset.mem_inter.mp hb₀).1
      have hb₀B : b₀ ∈ B' := (Finset.mem_inter.mp hb₀).2
      obtain ⟨q₀, hq_supp⟩ := exists_walk_of_isSubtree hS ha₀S hb₀S
      have hq_AB : ∀ z ∈ q₀.support, z ∈ A' ∪ B' := fun z hz => hS_sub (hq_supp z hz)
      have he : s(w', r') ∈ q₀.edges :=
        bridge_walk_mem_edges hJ' q₀ hq_AB (Or.inl ⟨ha₀A, hb₀B⟩)
      have hwS : w' ∈ S₀ := hq_supp w' (q₀.fst_mem_support_of_mem_edges he)
      have hwSA : w' ∈ S₀ ∩ A' := Finset.mem_inter.mpr ⟨hwS, hJ'.2.1⟩
      have hSA_subtree : IsSubtree G' (S₀ ∩ A') := by
        refine ⟨⟨w', hwSA⟩, ?_⟩
        have : Nonempty ↑((S₀ ∩ A' : Finset (Fin n)) : Set (Fin n)) := ⟨⟨w', hwSA⟩⟩
        refine ⟨?_⟩
        rintro ⟨a, ha⟩ ⟨b, hb⟩
        have haS : a ∈ S₀ := (Finset.mem_inter.mp ha).1
        have haA : a ∈ A' := (Finset.mem_inter.mp ha).2
        have hbS : b ∈ S₀ := (Finset.mem_inter.mp hb).1
        have hbA : b ∈ A' := (Finset.mem_inter.mp hb).2
        obtain ⟨q₁, hq₁_supp⟩ := exists_walk_of_isSubtree hS haS hbS
        let p₀ : G'.Walk a b := (q₁.toPath : G'.Walk a b)
        have hp_path : p₀.IsPath := q₁.toPath.2
        have hp_S : ∀ z ∈ p₀.support, z ∈ S₀ := fun z hz => hq₁_supp z (q₁.support_toPath_subset hz)
        have hp_AB : ∀ z ∈ p₀.support, z ∈ A' ∪ B' := fun z hz => hS_sub (hp_S z hz)
        have hp_A : ∀ z ∈ p₀.support, z ∈ A' :=
          bridge_path_support_left hJ' p₀ hp_path hp_AB haA hbA
        have hp_SA : ∀ z ∈ p₀.support, z ∈ ((S₀ ∩ A' : Finset (Fin n)) : Set (Fin n)) :=
          fun z hz => Finset.mem_inter.mpr ⟨hp_S z hz, hp_A z hz⟩
        exact (p₀.induce ((S₀ ∩ A' : Finset (Fin n)) : Set (Fin n)) hp_SA).reachable
      simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hSA_subtree, Finset.inter_subset_right, hwSA⟩
    have bridge_union_isSubtree : ∀ {SA SB : Finset (Fin n)},
        SA ∈ rootedSubtreesIn G' A w₀ → SB ∈ rootedSubtreesIn G' B r₀ →
        IsSubtree G' (SA ∪ SB) := by
      intro SA SB hSA hSB
      simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hSA hSB
      rcases hSA with ⟨hSA_sub, hSA_A, hw_SA⟩
      rcases hSB with ⟨hSB_sub, hSB_B, hr_SB⟩
      refine h_join_sub G' hSA_sub hSB_sub ⟨Disjoint.mono hSA_A hSB_B hJ.1, hw_SA, hr_SB, hJ.2.2.2.1, ?_⟩
      intro a ha b hb hab
      exact hJ.2.2.2.2 a (hSA_A ha) b (hSB_B hb) hab
    let RA_set := rootedSubtreesIn G' A w₀
    let RB_set := rootedSubtreesIn G' B r₀
    let UA_set := subtreesIn G' A
    let UB_set := subtreesIn G' B
    let φ : Finset (Fin n) × Finset (Fin n) → Finset (Fin n) := fun p₀ => p₀.1 ∪ p₀.2
    let M := (RA_set ×ˢ RB_set).image φ
    have h_inter_left : ∀ {X Y : Finset (Fin n)}, X ⊆ A → Y ⊆ B → (X ∪ Y) ∩ A = X := by
      intro X Y hX hY
      ext z
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hzX | hzY, hzA⟩
        · exact hzX
        · exact False.elim (Finset.disjoint_left.mp hJ.1 hzA (hY hzY))
      · intro hzX
        exact ⟨Or.inl hzX, hX hzX⟩
    have h_inter_right : ∀ {X Y : Finset (Fin n)}, X ⊆ A → Y ⊆ B → (X ∪ Y) ∩ B = Y := by
      intro X Y hX hY
      ext z
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hzX | hzY, hzB⟩
        · exact False.elim (Finset.disjoint_left.mp hJ.1 (hX hzX) hzB)
        · exact hzY
      · intro hzY
        exact ⟨Or.inr hzY, hY hzY⟩
    have h_inj : Set.InjOn φ ((RA_set ×ˢ RB_set : Finset (Finset (Fin n) × Finset (Fin n))) : Set (Finset (Fin n) × Finset (Fin n))) := by
      intro p₁ hp₁ p₂ hp₂ h_eq
      rcases Finset.mem_product.mp (Finset.mem_coe.mp hp₁) with ⟨hp₁A, hp₁B⟩
      rcases Finset.mem_product.mp (Finset.mem_coe.mp hp₂) with ⟨hp₂A, hp₂B⟩
      simp only [RA_set, RB_set, rootedSubtreesIn, Finset.mem_filter] at hp₁A hp₁B hp₂A hp₂B
      have h1 : p₁.1 = p₂.1 := by
        calc p₁.1 = (p₁.1 ∪ p₁.2) ∩ A := (h_inter_left hp₁A.2.1 hp₁B.2.1).symm
          _ = (p₂.1 ∪ p₂.2) ∩ A := by rw [show p₁.1 ∪ p₁.2 = p₂.1 ∪ p₂.2 from h_eq]
          _ = p₂.1 := h_inter_left hp₂A.2.1 hp₂B.2.1
      have h2 : p₁.2 = p₂.2 := by
        calc p₁.2 = (p₁.1 ∪ p₁.2) ∩ B := (h_inter_right hp₁A.2.1 hp₁B.2.1).symm
          _ = (p₂.1 ∪ p₂.2) ∩ B := by rw [show p₁.1 ∪ p₁.2 = p₂.1 ∪ p₂.2 from h_eq]
          _ = p₂.2 := h_inter_right hp₂A.2.1 hp₂B.2.1
      exact Prod.ext h1 h2
    have hM_card : M.card = rootedCount G' A w₀ * rootedCount G' B r₀ := by
      dsimp [M, RA_set, RB_set, rootedCount]
      rw [Finset.card_image_of_injOn h_inj, Finset.card_product]
    have hM_sum : ∑ S₀ ∈ M, S₀.card =
        rootedOrderSum G' A w₀ * rootedCount G' B r₀ + rootedCount G' A w₀ * rootedOrderSum G' B r₀ := by
      dsimp [M]
      rw [Finset.sum_image h_inj, Finset.sum_product]
      have h_inner : ∀ a ∈ RA_set,
          ∑ b ∈ RB_set, (a ∪ b).card = a.card * RB_set.card + ∑ b ∈ RB_set, b.card := by
        intro a ha
        simp only [RA_set, rootedSubtreesIn, Finset.mem_filter] at ha
        have h_congr : ∑ b ∈ RB_set, (a ∪ b).card = ∑ b ∈ RB_set, (a.card + b.card) := by
          refine Finset.sum_congr rfl fun b hb => ?_
          simp only [RB_set, rootedSubtreesIn, Finset.mem_filter] at hb
          exact Finset.card_union_of_disjoint (Disjoint.mono ha.2.1 hb.2.1 hJ.1)
        rw [h_congr, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
      rw [Finset.sum_congr rfl h_inner, Finset.sum_add_distrib, ← Finset.sum_mul,
        Finset.sum_const, smul_eq_mul]
      rfl
    have h_mem_M : ∀ S₀ : Finset (Fin n),
        S₀ ∈ M ↔ S₀ ∈ subtreesIn G' (A ∪ B) ∧ (S₀ ∩ A).Nonempty ∧ (S₀ ∩ B).Nonempty := by
      intro S₀
      constructor
      · intro hS₀
        obtain ⟨⟨SA, SB⟩, hp, rfl⟩ := Finset.mem_image.mp hS₀
        rcases Finset.mem_product.mp hp with ⟨hSA, hSB⟩
        have hSA' := hSA
        have hSB' := hSB
        simp only [RA_set, RB_set, rootedSubtreesIn, subtrees, Finset.mem_filter,
          Finset.mem_univ, true_and] at hSA' hSB'
        have h_sub_AB : SA ∪ SB ⊆ A ∪ B := Finset.union_subset_union hSA'.2.1 hSB'.2.1
        have h_tree : IsSubtree G' (SA ∪ SB) := bridge_union_isSubtree hSA hSB
        have h_in_sub : SA ∪ SB ∈ subtreesIn G' (A ∪ B) := by
          simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨h_tree, h_sub_AB⟩
        have h_ne_A : ((SA ∪ SB) ∩ A).Nonempty := by
          rw [h_inter_left hSA'.2.1 hSB'.2.1]
          exact ⟨w₀, hSA'.2.2⟩
        have h_ne_B : ((SA ∪ SB) ∩ B).Nonempty := by
          rw [h_inter_right hSA'.2.1 hSB'.2.1]
          exact ⟨r₀, hSB'.2.2⟩
        exact ⟨h_in_sub, h_ne_A, h_ne_B⟩
      · rintro ⟨hS_in, hSA_ne, hSB_ne⟩
        simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hS_in
        rcases hS_in with ⟨hS_tree, hS_sub⟩
        have hSA_mem : S₀ ∩ A ∈ RA_set := bridge_crossing_left hJ hS_sub hS_tree hSA_ne hSB_ne
        have hS_sub' : S₀ ⊆ B ∪ A := by simpa [Finset.union_comm] using hS_sub
        have hSB_mem : S₀ ∩ B ∈ RB_set :=
          bridge_crossing_left (isBridgeJoin_symm hJ) hS_sub' hS_tree hSB_ne hSA_ne
        refine Finset.mem_image.mpr ⟨(S₀ ∩ A, S₀ ∩ B), Finset.mem_product.mpr ⟨hSA_mem, hSB_mem⟩, ?_⟩
        dsimp [φ]
        rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hS_sub]
    have h_sub_of_inter_empty_right : ∀ {S₀ : Finset (Fin n)}, S₀ ⊆ A ∪ B → S₀ ∩ B = ∅ → S₀ ⊆ A := by
      intro S₀ hS₀ h_emp z hz
      rcases Finset.mem_union.mp (hS₀ hz) with hzA | hzB
      · exact hzA
      · exfalso
        have : z ∈ (∅ : Finset (Fin n)) := h_emp ▸ Finset.mem_inter.mpr ⟨hz, hzB⟩
        exact Finset.notMem_empty z this
    have h_sub_of_inter_empty_left : ∀ {S₀ : Finset (Fin n)}, S₀ ⊆ A ∪ B → S₀ ∩ A = ∅ → S₀ ⊆ B := by
      intro S₀ hS₀ h_emp z hz
      rcases Finset.mem_union.mp (hS₀ hz) with hzA | hzB
      · exfalso
        have : z ∈ (∅ : Finset (Fin n)) := h_emp ▸ Finset.mem_inter.mpr ⟨hz, hzA⟩
        exact Finset.notMem_empty z this
      · exact hzB
    have h_root_disj : Disjoint RA_set M := by
      rw [Finset.disjoint_left]
      intro S₀ hS_RA hS_M
      obtain ⟨_, _, b, hb⟩ := (h_mem_M S₀).mp hS_M
      simp only [RA_set, rootedSubtreesIn, Finset.mem_filter] at hS_RA
      exact Finset.disjoint_left.mp hJ.1 (hS_RA.2.1 (Finset.mem_inter.mp hb).1) (Finset.mem_inter.mp hb).2
    have h_root_part : rootedSubtreesIn G' (A ∪ B) w₀ = RA_set ∪ M := by
      ext S₀
      rw [Finset.mem_union, h_mem_M]
      constructor
      · intro hS₀
        simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hS₀
        rcases hS₀ with ⟨hS_tree, hS_sub, hwS⟩
        rcases Finset.eq_empty_or_nonempty (S₀ ∩ B) with h_emp | hSB_ne
        · left
          simp only [RA_set, rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hS_tree, h_sub_of_inter_empty_right hS_sub h_emp, hwS⟩
        · right
          have hS_in : S₀ ∈ subtreesIn G' (A ∪ B) := by
            simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hS_tree, hS_sub⟩
          exact ⟨hS_in, ⟨w₀, Finset.mem_inter.mpr ⟨hwS, hJ.2.1⟩⟩, hSB_ne⟩
      · rintro (hS_RA | ⟨hS_in, hSA_ne, hSB_ne⟩)
        · simp only [RA_set, rootedSubtreesIn, subtrees, Finset.mem_filter,
            Finset.mem_univ, true_and] at hS_RA ⊢
          exact ⟨hS_RA.1, Finset.Subset.trans hS_RA.2.1 Finset.subset_union_left, hS_RA.2.2⟩
        · simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hS_in
          have hSA_mem : S₀ ∩ A ∈ RA_set :=
            bridge_crossing_left hJ hS_in.2 hS_in.1 hSA_ne hSB_ne
          simp only [RA_set, rootedSubtreesIn, Finset.mem_filter] at hSA_mem
          simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hS_in.1, hS_in.2, (Finset.mem_inter.mp hSA_mem.2.2).1⟩
    have h_disj_UA_UB : Disjoint UA_set UB_set := by
      rw [Finset.disjoint_left]
      intro S₀ hUA hUB
      simp only [UA_set, UB_set, subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hUA hUB
      obtain ⟨z, hz⟩ := hUA.1.1
      exact Finset.disjoint_left.mp hJ.1 (hUA.2 hz) (hUB.2 hz)
    have h_disj_UAB_M : Disjoint (UA_set ∪ UB_set) M := by
      rw [Finset.disjoint_left]
      intro S₀ hUAB hM
      obtain ⟨_, ⟨a, ha⟩, ⟨b, hb⟩⟩ := (h_mem_M S₀).mp hM
      rcases Finset.mem_union.mp hUAB with hUA | hUB
      · simp only [UA_set, subtreesIn, Finset.mem_filter] at hUA
        exact Finset.disjoint_left.mp hJ.1 (hUA.2 (Finset.mem_inter.mp hb).1) (Finset.mem_inter.mp hb).2
      · simp only [UB_set, subtreesIn, Finset.mem_filter] at hUB
        exact Finset.disjoint_left.mp hJ.1 (Finset.mem_inter.mp ha).2 (hUB.2 (Finset.mem_inter.mp ha).1)
    have h_unroot_part : subtreesIn G' (A ∪ B) = (UA_set ∪ UB_set) ∪ M := by
      ext S₀
      rw [Finset.mem_union, Finset.mem_union, h_mem_M]
      constructor
      · intro hS₀
        have hS₀' := hS₀
        simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hS₀'
        rcases Finset.eq_empty_or_nonempty (S₀ ∩ B) with hB_emp | hSB_ne
        · left; left
          simp only [UA_set, subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hS₀'.1, h_sub_of_inter_empty_right hS₀'.2 hB_emp⟩
        · rcases Finset.eq_empty_or_nonempty (S₀ ∩ A) with hA_emp | hSA_ne
          · left; right
            simp only [UB_set, subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hS₀'.1, h_sub_of_inter_empty_left hS₀'.2 hA_emp⟩
          · right
            exact ⟨hS₀, hSA_ne, hSB_ne⟩
      · rintro ((hUA | hUB) | ⟨hS_in, _, _⟩)
        · simp only [UA_set, subtreesIn, Finset.mem_filter] at hUA ⊢
          exact ⟨hUA.1, Finset.Subset.trans hUA.2 Finset.subset_union_left⟩
        · simp only [UB_set, subtreesIn, Finset.mem_filter] at hUB ⊢
          exact ⟨hUB.1, Finset.Subset.trans hUB.2 Finset.subset_union_right⟩
        · exact hS_in
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · dsimp [rootedCount]
      rw [h_root_part, Finset.card_union_of_disjoint h_root_disj, hM_card]
      dsimp [RA_set, rootedCount]; ring
    · dsimp [rootedOrderSum]
      rw [h_root_part, Finset.sum_union h_root_disj, hM_sum]
      dsimp [RA_set, rootedOrderSum]; ring
    · dsimp [unrootedCount]
      rw [h_unroot_part, Finset.card_union_of_disjoint h_disj_UAB_M,
        Finset.card_union_of_disjoint h_disj_UA_UB, hM_card]
    · dsimp [unrootedOrderSum]
      rw [h_unroot_part, Finset.sum_union h_disj_UAB_M,
        Finset.sum_union h_disj_UA_UB, hM_sum]
      dsimp [UA_set, UB_set, unrootedOrderSum]; ring
  intro w u ℓ₁ ℓ₂ r_B r_C H L_c B C
    h12 hu1 hu2 hH_eq hH_sub hBridge_u hLeaf1 hLeaf2 _hu_adj
    hw_not_Lc hLc_card hLc_packet hDisj_wB hDisj_wC hDisj_BC
    hH_split hB_sub hC_sub hBridge_B hBridge_C h_no_imp
    c p x t_B N_B R_B y t_C N_C R_C S t_H a_B t_AB a_C t_AC q
  
  have hW_moments : IsSubtree T (insert w L_c) ∧
      rootedCount T (insert w L_c) w = p ∧
      rootedOrderSum T (insert w L_c) w = p + c ∧
      unrootedCount T (insert w L_c) = p + c ∧
      unrootedOrderSum T (insert w L_c) = p + 2 * c := by
    have hc_cases : L_c.card = 0 ∨ L_c.card = 1 :=
      Nat.le_one_iff_eq_zero_or_eq_one.mp hLc_card
    rcases hc_cases with hc0 | hc1
    · have hLc_emp : L_c = ∅ := Finset.card_eq_zero.mp hc0
      have hW_eq : insert w L_c = {w} := by rw [hLc_emp]; rfl
      have hc_eq : c = 0 := hc0
      have hp_eq : p = 1 := by dsimp [p]; rw [hc_eq]; rfl
      obtain ⟨h_sub, h_rc, h_ros, h_uc, h_uos⟩ := h_sing T w
      rw [hW_eq]
      refine ⟨h_sub, ?_, ?_, ?_, ?_⟩
      · rw [h_rc, hp_eq]
      · rw [h_ros, hp_eq, hc_eq]
      · rw [h_uc, hp_eq, hc_eq]
      · rw [h_uos, hp_eq, hc_eq]
    · obtain ⟨z, hz_eq⟩ := Finset.card_eq_one.mp hc1
      have hwz : w ≠ z := fun h => hw_not_Lc (hz_eq ▸ (h ▸ Finset.mem_singleton_self w))
      have hz_leaf : IsLeafIn T z w := hLc_packet z (hz_eq ▸ Finset.mem_singleton_self z)
      have hJ_wz : IsBridgeJoin T {w} {z} w z := by
        refine ⟨Finset.disjoint_singleton.mpr hwz, Finset.mem_singleton_self w,
          Finset.mem_singleton_self z, T.symm ((hz_leaf w).mpr rfl), ?_⟩
        intro a ha b hb _
        exact ⟨Finset.mem_singleton.mp ha, Finset.mem_singleton.mp hb⟩
      have hW_eq : ({w} : Finset (Fin n)) ∪ {z} = insert w L_c := by
        rw [hz_eq]; ext v; simp; tauto
      obtain ⟨hw_sub, hw_rc, hw_ros, hw_uc, hw_uos⟩ := h_sing T w
      obtain ⟨hz_sub, hz_rc, hz_ros, hz_uc, hz_uos⟩ := h_sing T z
      obtain ⟨⟨h_rc, h_ros⟩, ⟨h_uc, h_uos⟩⟩ := bridge_join_both_moments T {w} {z} w z hJ_wz
      have hW_sub : IsSubtree T (insert w L_c) := hW_eq ▸ h_join_sub T hw_sub hz_sub hJ_wz
      rw [hW_eq, hw_rc, hz_rc] at h_rc
      rw [hW_eq, hw_rc, hw_ros, hz_rc, hz_ros] at h_ros
      rw [hW_eq, hw_uc, hz_uc, hw_rc, hz_rc] at h_uc
      rw [hW_eq, hw_uos, hz_uos, hw_ros, hz_rc, hw_rc, hz_ros] at h_uos
      have hc_eq : c = 1 := hc1
      have hp_eq : p = 2 := by dsimp [p]; rw [hc_eq]; rfl
      refine ⟨hW_sub, ?_, ?_, ?_, ?_⟩
      · rw [h_rc, hp_eq]
      · rw [h_ros, hp_eq, hc_eq]
      · rw [h_uc, hp_eq, hc_eq]
      · rw [h_uos, hp_eq, hc_eq]
  rcases hW_moments with ⟨hW_sub, hW_rc, hW_ros, hW_uc, hW_uos⟩
  have hAC_sub : IsSubtree T ((insert w L_c) ∪ B) := h_join_sub T hW_sub hB_sub hBridge_B
  obtain ⟨⟨hAC_rc, hAC_ros⟩, ⟨hAC_uc, hAC_uos⟩⟩ :=
    bridge_join_both_moments T (insert w L_c) B w r_B hBridge_B
  rw [hW_rc] at hAC_rc
  rw [hW_ros, hW_rc] at hAC_ros
  rw [hW_uc, hW_rc] at hAC_uc
  rw [hW_uos, hW_ros, hW_rc] at hAC_uos
  have hAC_rc' : rootedCount T ((insert w L_c) ∪ B) w = a_C := hAC_rc
  have hAC_ros' : rootedOrderSum T ((insert w L_c) ∪ B) w = t_AC := hAC_ros
  obtain ⟨⟨hH_rc, hH_ros⟩, ⟨hH_uc, hH_uos⟩⟩ :=
    bridge_join_both_moments T ((insert w L_c) ∪ B) C w r_C hBridge_C
  rw [← hH_split, hAC_rc'] at hH_rc
  rw [← hH_split, hAC_ros', hAC_rc'] at hH_ros
  rw [← hH_split, hAC_uc, hAC_rc'] at hH_uc
  rw [← hH_split, hAC_uos, hAC_ros', hAC_rc'] at hH_uos
  have hH_rc_eq : rootedCount T H w = S := hH_rc
  have hH_ros_eq : rootedOrderSum T H w = t_H := by
    rw [hH_ros]
    dsimp only [t_H, t_AC, a_C, y, t_C]
    ring
  have hH_uc_eq : unrootedCount T H = S + N_B + N_C + c := by
    rw [hH_uc]
    dsimp only [S, a_C, x, N_B, y, N_C]
    ring
  have hH_uos_eq : unrootedOrderSum T H = t_H + R_B + R_C + c := by
    rw [hH_uos]
    dsimp only [t_H, t_AC, a_C, x, t_B, R_B, y, t_C, R_C]
    ring
  
  have hBridge_WC : IsBridgeJoin T (insert w L_c) C w r_C := by
    refine ⟨hDisj_wC, Finset.mem_insert_self w L_c, hBridge_C.2.2.1, hBridge_C.2.2.2.1, ?_⟩
    intro a ha b hb hab
    exact hBridge_C.2.2.2.2 a (Finset.mem_union_left B ha) b hb hab
  have hAB_sub : IsSubtree T ((insert w L_c) ∪ C) := h_join_sub T hW_sub hC_sub hBridge_WC
  obtain ⟨⟨hAB_rc, hAB_ros⟩, _⟩ := bridge_join_both_moments T (insert w L_c) C w r_C hBridge_WC
  rw [hW_rc] at hAB_rc
  rw [hW_ros, hW_rc] at hAB_ros
  have hAB_rc' : rootedCount T ((insert w L_c) ∪ C) w = a_B := hAB_rc
  have hAB_ros' : rootedOrderSum T ((insert w L_c) ∪ C) w = t_AB := hAB_ros
  have hH_AB_B : H = ((insert w L_c) ∪ C) ∪ B := by
    rw [hH_split]; exact Finset.union_right_comm (insert w L_c) B C
  have hBridge_AB_B : IsBridgeJoin T ((insert w L_c) ∪ C) B w r_B := by
    refine ⟨Finset.disjoint_union_left.mpr ⟨hDisj_wB, hDisj_BC.symm⟩,
      Finset.mem_union_left C (Finset.mem_insert_self w L_c),
      hBridge_B.2.2.1, hBridge_B.2.2.2.1, ?_⟩
    intro a ha b hb hab
    rcases Finset.mem_union.mp ha with haW | haC
    · exact hBridge_B.2.2.2.2 a haW b hb hab
    · exfalso
      have hbw : b = w := (hBridge_C.2.2.2.2 b (Finset.mem_union_right (insert w L_c) hb) a haC (T.symm hab)).1
      exact Finset.disjoint_left.mp hDisj_wB (Finset.mem_insert_self w L_c) (hbw ▸ hb)
  
  have hw_H : w ∈ H := hBridge_u.2.1
  have hw_not_ch : w ∉ ({u, ℓ₁, ℓ₂} : Finset (Fin n)) := by
    have hw_H' := hw_H
    rw [hH_eq] at hw_H'
    exact (Finset.mem_sdiff.mp hw_H').2
  have hw1 : w ≠ ℓ₁ := fun h => hw_not_ch (by simp [h])
  have hw2 : w ≠ ℓ₂ := fun h => hw_not_ch (by simp [h])
  have hJ_u1 : IsBridgeJoin T {u} {ℓ₁} u ℓ₁ := by
    refine ⟨Finset.disjoint_singleton.mpr hu1, Finset.mem_singleton_self u,
      Finset.mem_singleton_self ℓ₁, T.symm ((hLeaf1 u).mpr rfl), ?_⟩
    intro a ha b hb _
    exact ⟨Finset.mem_singleton.mp ha, Finset.mem_singleton.mp hb⟩
  have hJ_u12 : IsBridgeJoin T ({u} ∪ {ℓ₁}) {ℓ₂} u ℓ₂ := by
    refine ⟨Finset.disjoint_singleton_right.mpr (by simp [hu2.symm, h12.symm]),
      Finset.mem_union_left _ (Finset.mem_singleton_self u),
      Finset.mem_singleton_self ℓ₂, T.symm ((hLeaf2 u).mpr rfl), ?_⟩
    intro a _ b hb hab
    have hb_eq : b = ℓ₂ := Finset.mem_singleton.mp hb
    subst b
    exact ⟨(hLeaf2 a).mp (T.symm hab), rfl⟩
  have h_ch_union : ({u} : Finset (Fin n)) ∪ {ℓ₁} ∪ {ℓ₂} = ({u, ℓ₁, ℓ₂} : Finset (Fin n)) := by
    ext z
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  obtain ⟨hu_sub, hu_rc, hu_ros, hu_uc, hu_uos⟩ := h_sing T u
  obtain ⟨h1_sub, h1_rc, h1_ros, h1_uc, h1_uos⟩ := h_sing T ℓ₁
  obtain ⟨h2_sub, h2_rc, h2_ros, h2_uc, h2_uos⟩ := h_sing T ℓ₂
  have hP_sub : IsSubtree T ({u, ℓ₁, ℓ₂} : Finset (Fin n)) := by
    rw [← h_ch_union]
    exact h_join_sub T (h_join_sub T hu_sub h1_sub hJ_u1) h2_sub hJ_u12
  obtain ⟨⟨h_u1_rc, h_u1_ros⟩, ⟨h_u1_uc, h_u1_uos⟩⟩ := bridge_join_both_moments T {u} {ℓ₁} u ℓ₁ hJ_u1
  obtain ⟨⟨h_ch_rc, h_ch_ros⟩, ⟨h_ch_uc, h_ch_uos⟩⟩ := bridge_join_both_moments T ({u} ∪ {ℓ₁}) {ℓ₂} u ℓ₂ hJ_u12
  rw [h_ch_union] at h_ch_rc h_ch_ros h_ch_uc h_ch_uos
  have h_ch_rc4 : rootedCount T ({u, ℓ₁, ℓ₂} : Finset (Fin n)) u = 4 := by
    rw [h_ch_rc, h_u1_rc, hu_rc, h1_rc, h2_rc]
  have h_ch_ros8 : rootedOrderSum T ({u, ℓ₁, ℓ₂} : Finset (Fin n)) u = 8 := by
    rw [h_ch_ros, h_u1_ros, h_u1_rc, hu_rc, hu_ros, h1_rc, h1_ros, h2_rc, h2_ros]
  have h_ch_uc6 : unrootedCount T ({u, ℓ₁, ℓ₂} : Finset (Fin n)) = 6 := by
    rw [h_ch_uc, h_u1_uc, h_u1_rc, hu_uc, h1_uc, h2_uc, hu_rc, h1_rc, h2_rc]
  have h_ch_uos10 : unrootedOrderSum T ({u, ℓ₁, ℓ₂} : Finset (Fin n)) = 10 := by
    rw [h_ch_uos, h_u1_uos, h_u1_ros, h_u1_rc, hu_uos, h1_uos, h2_uos, hu_ros, h1_ros, h2_ros, hu_rc, h1_rc, h2_rc]
  have h_univ_union : H ∪ ({u, ℓ₁, ℓ₂} : Finset (Fin n)) = Finset.univ := by
    rw [hH_eq]
    exact Finset.sdiff_union_of_subset (Finset.subset_univ _)
  have h_uc_univ : ∀ G' : SimpleGraph (Fin n), unrootedCount G' Finset.univ = subtreeCount G' := by
    intro G'
    dsimp [unrootedCount, subtreeCount, subtreesIn]
    congr 1; ext S₀; simp
  have h_uos_univ : ∀ G' : SimpleGraph (Fin n), unrootedOrderSum G' Finset.univ = subtreeOrderSum G' := by
    intro G'
    dsimp [unrootedOrderSum, subtreeOrderSum, subtreesIn]
    congr 1; ext S₀; simp
  obtain ⟨_, ⟨h_sc_T, h_sos_T⟩⟩ := bridge_join_both_moments T H ({u, ℓ₁, ℓ₂} : Finset (Fin n)) w u hBridge_u
  rw [h_univ_union, h_uc_univ T, hH_rc_eq, h_ch_rc4, h_ch_uc6] at h_sc_T
  rw [h_univ_union, h_uos_univ T, hH_rc_eq, hH_ros_eq, h_ch_rc4, h_ch_ros8, h_ch_uos10] at h_sos_T
  have h_sc_T_pos : (0 : ℚ) < (subtreeCount T : ℚ) := by
    have : 0 < subtreeCount T := by rw [h_sc_T]; positivity
    exact_mod_cast this
  have h_q_bal : (subtreeOrderSum T : ℚ) = q * (subtreeCount T : ℚ) := by
    dsimp [q, meanSubtreeOrder]
    exact (div_mul_cancel₀ (subtreeOrderSum T : ℚ) (ne_of_gt h_sc_T_pos)).symm
  have h_sc_T_H_Q : (subtreeCount T : ℚ) = (unrootedCount T H : ℚ) + 4 * (S : ℚ) + 6 := by
    have := congrArg (fun m : ℕ => (m : ℚ)) h_sc_T
    push_cast at this; linarith
  have h_sos_T_H_Q : (subtreeOrderSum T : ℚ) = (unrootedOrderSum T H : ℚ) + 4 * (t_H : ℚ) + 8 * (S : ℚ) + 10 := by
    have := congrArg (fun m : ℕ => (m : ℚ)) h_sos_T
    push_cast at this; linarith
  have h_bal_H : (unrootedOrderSum T H : ℚ) + 4 * (t_H : ℚ) + 8 * (S : ℚ) + 10 =
      q * ((unrootedCount T H : ℚ) + 4 * (S : ℚ) + 6) := by
    rw [← h_sos_T_H_Q, ← h_sc_T_H_Q]; exact h_q_bal
  have hH_uc_Q : (unrootedCount T H : ℚ) = (S : ℚ) + (N_B : ℚ) + (N_C : ℚ) + (c : ℚ) := by
    have := congrArg (fun m : ℕ => (m : ℚ)) hH_uc_eq
    push_cast at this; linarith
  have hH_uos_Q : (unrootedOrderSum T H : ℚ) = (t_H : ℚ) + (R_B : ℚ) + (R_C : ℚ) + (c : ℚ) := by
    have := congrArg (fun m : ℕ => (m : ℚ)) hH_uos_eq
    push_cast at this; linarith
  have h_conj1 : 5 * (t_H : ℚ) + 8 * (S : ℚ) + (R_B : ℚ) + (R_C : ℚ) + 10 + (c : ℚ) =
      q * (5 * (S : ℚ) + (N_B : ℚ) + (N_C : ℚ) + 6 + (c : ℚ)) := by
    have h_bal_H' := h_bal_H
    rw [hH_uc_Q, hH_uos_Q] at h_bal_H'
    linarith [h_bal_H']
  
  have hw_not_L : w ∉ ({ℓ₁, ℓ₂} : Finset (Fin n)) := by simp [hw1, hw2]
  let T_fold := relocatePacket T ({ℓ₁, ℓ₂} : Finset (Fin n)) w hw_not_L
  have h_not_ch_of_H : ∀ z ∈ H, z ≠ u ∧ z ≠ ℓ₁ ∧ z ≠ ℓ₂ := by
    intro z hz
    rw [hH_eq] at hz
    have hz' := (Finset.mem_sdiff.mp hz).2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz'
    exact hz'
  have h_adj_fold_H : ∀ a ∈ H, ∀ b ∈ H, T_fold.Adj a b ↔ T.Adj a b := by
    intro a ha b hb
    obtain ⟨_, ha1, ha2⟩ := h_not_ch_of_H a ha
    obtain ⟨_, hb1, hb2⟩ := h_not_ch_of_H b hb
    change (a ∉ ({ℓ₁, ℓ₂} : Finset (Fin n)) ∧ b ∉ ({ℓ₁, ℓ₂} : Finset (Fin n)) ∧ T.Adj a b) ∨
      (a ∈ ({ℓ₁, ℓ₂} : Finset (Fin n)) ∧ b = w) ∨ (a = w ∧ b ∈ ({ℓ₁, ℓ₂} : Finset (Fin n))) ↔ T.Adj a b
    simp [ha1, ha2, hb1, hb2]
  have h_induce_fold_H : ∀ S₀ : Finset (Fin n), S₀ ⊆ H →
      T_fold.induce (S₀ : Set (Fin n)) = T.induce (S₀ : Set (Fin n)) := by
    intro S₀ hS₀
    ext ⟨a, ha⟩ ⟨b, hb⟩
    exact h_adj_fold_H a (hS₀ ha) b (hS₀ hb)
  have hH_sub_fold : IsSubtree T_fold H := by
    dsimp [IsSubtree]
    rw [h_induce_fold_H H (Finset.Subset.refl H)]
    exact hH_sub
  have hH_acyc_fold : AcyclicOn T_fold H :=
    acyclicOn_of_adj_imp (fun a ha b hb hab => (h_adj_fold_H a ha b hb).mp hab)
  have h_sub_fold_H : subtreesIn T_fold H = subtreesIn T H := by
    ext S₀
    simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
    refine and_congr_left (fun hS₀ => ?_)
    dsimp [IsSubtree]; rw [h_induce_fold_H S₀ hS₀]
  have h_root_fold_H : rootedSubtreesIn T_fold H w = rootedSubtreesIn T H w := by
    ext S₀
    simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
    refine and_congr_left (fun hS₀ => ?_)
    dsimp [IsSubtree]; rw [h_induce_fold_H S₀ hS₀.1]
  have hs_fold_H : rootedCount T_fold H w = S := by
    rw [← hH_rc_eq]; dsimp [rootedCount]; rw [h_root_fold_H]
  have ht_fold_H : rootedOrderSum T_fold H w = t_H := by
    rw [← hH_ros_eq]; dsimp [rootedOrderSum]; rw [h_root_fold_H]
  have hN_fold_H : unrootedCount T_fold H = unrootedCount T H := by
    dsimp [unrootedCount]; rw [h_sub_fold_H]
  have hR_fold_H : unrootedOrderSum T_fold H = unrootedOrderSum T H := by
    dsimp [unrootedOrderSum]; rw [h_sub_fold_H]
  have hu_not_H : u ∉ H := fun h => (h_not_ch_of_H u h).1 rfl
  have h1_not_Hu : ℓ₁ ∉ H ∪ {u} := by
    simp only [Finset.mem_union, Finset.mem_singleton, not_or]
    exact ⟨fun h => (h_not_ch_of_H ℓ₁ h).2.1 rfl, hu1.symm⟩
  have h2_not_Hu1 : ℓ₂ ∉ H ∪ {u} ∪ {ℓ₁} := by
    simp only [Finset.mem_union, Finset.mem_singleton, not_or]
    exact ⟨⟨fun h => (h_not_ch_of_H ℓ₂ h).2.2 rfl, hu2.symm⟩, h12.symm⟩
  have hJ_fold_u : IsBridgeJoin T_fold H {u} w u := by
    refine ⟨Finset.disjoint_singleton_right.mpr hu_not_H, hw_H, Finset.mem_singleton_self u,
      Or.inl ⟨by simp [hw1, hw2], by simp [hu1, hu2], hBridge_u.2.2.2.1⟩, ?_⟩
    intro a ha b hb hab
    have hb_eq : b = u := Finset.mem_singleton.mp hb
    subst b
    obtain ⟨_, ha1, ha2⟩ := h_not_ch_of_H a ha
    rcases hab with ⟨_, _, habT⟩ | ⟨ha_in, _⟩ | ⟨_, hu_in⟩
    · exact hBridge_u.2.2.2.2 a ha u (by simp) habT
    · simp [ha1, ha2] at ha_in
    · simp [hu1, hu2] at hu_in
  have hJ_fold_1 : IsBridgeJoin T_fold (H ∪ {u}) {ℓ₁} w ℓ₁ := by
    refine ⟨Finset.disjoint_singleton_right.mpr h1_not_Hu, Finset.mem_union_left _ hw_H,
      Finset.mem_singleton_self ℓ₁, Or.inr (Or.inr ⟨rfl, by simp⟩), ?_⟩
    intro a ha b hb hab
    have hb_eq : b = ℓ₁ := Finset.mem_singleton.mp hb
    subst b
    have ha_not_L : a ∉ ({ℓ₁, ℓ₂} : Finset (Fin n)) := by
      rcases Finset.mem_union.mp ha with haH | hau
      · obtain ⟨_, ha1, ha2⟩ := h_not_ch_of_H a haH
        simp [ha1, ha2]
      · rw [Finset.mem_singleton.mp hau]
        simp [hu1, hu2]
    rcases hab with ⟨_, hb_not_L, _⟩ | ⟨ha_in, _⟩ | ⟨haw, _⟩
    · simp at hb_not_L
    · exact False.elim (ha_not_L ha_in)
    · exact ⟨haw, rfl⟩
  have hJ_fold_2 : IsBridgeJoin T_fold (H ∪ {u} ∪ {ℓ₁}) {ℓ₂} w ℓ₂ := by
    refine ⟨Finset.disjoint_singleton_right.mpr h2_not_Hu1,
      Finset.mem_union_left _ (Finset.mem_union_left _ hw_H),
      Finset.mem_singleton_self ℓ₂, Or.inr (Or.inr ⟨rfl, by simp⟩), ?_⟩
    intro a _ b hb hab
    have hb_eq : b = ℓ₂ := Finset.mem_singleton.mp hb
    subst b
    rcases hab with ⟨_, hb_not_L, _⟩ | ⟨_, h_eq⟩ | ⟨haw, _⟩
    · simp at hb_not_L
    · exact False.elim (hw2 h_eq.symm)
    · exact ⟨haw, rfl⟩
  have h_fold_univ : H ∪ {u} ∪ {ℓ₁} ∪ {ℓ₂} = Finset.univ := by
    calc H ∪ {u} ∪ {ℓ₁} ∪ {ℓ₂} = H ∪ ({u} ∪ {ℓ₁} ∪ {ℓ₂}) := by
          ext z; simp only [Finset.mem_union]; tauto
      _ = Finset.univ := by rw [h_ch_union, h_univ_union]
  obtain ⟨hu_f_sub, hu_f_rc, hu_f_ros, hu_f_uc, hu_f_uos⟩ := h_sing T_fold u
  obtain ⟨h1_f_sub, h1_f_rc, h1_f_ros, h1_f_uc, h1_f_uos⟩ := h_sing T_fold ℓ₁
  obtain ⟨h2_f_sub, h2_f_rc, h2_f_ros, h2_f_uc, h2_f_uos⟩ := h_sing T_fold ℓ₂
  have hHu_sub : IsSubtree T_fold (H ∪ {u}) := h_join_sub T_fold hH_sub_fold hu_f_sub hJ_fold_u
  have hHu1_sub : IsSubtree T_fold (H ∪ {u} ∪ {ℓ₁}) := h_join_sub T_fold hHu_sub h1_f_sub hJ_fold_1
  have h_fold_univ_sub : IsSubtree T_fold Finset.univ := by
    rw [← h_fold_univ]
    exact h_join_sub T_fold hHu1_sub h2_f_sub hJ_fold_2
  have hHu_acyc : AcyclicOn T_fold (H ∪ {u}) :=
    acyclicOn_bridge_join hJ_fold_u hH_acyc_fold (acyclicOn_singleton T_fold u)
  have hHu1_acyc : AcyclicOn T_fold (H ∪ {u} ∪ {ℓ₁}) :=
    acyclicOn_bridge_join hJ_fold_1 hHu_acyc (acyclicOn_singleton T_fold ℓ₁)
  have h_fold_univ_acyc : AcyclicOn T_fold Finset.univ := by
    rw [← h_fold_univ]
    exact acyclicOn_bridge_join hJ_fold_2 hHu1_acyc (acyclicOn_singleton T_fold ℓ₂)
  have hT_fold : T_fold.IsTree := isTree_of_univ T_fold h_fold_univ_sub h_fold_univ_acyc
  obtain ⟨⟨hs_Hu, ht_Hu⟩, ⟨hN_Hu, hR_Hu⟩⟩ := bridge_join_both_moments T_fold H {u} w u hJ_fold_u
  obtain ⟨⟨hs_Hu1, ht_Hu1⟩, ⟨hN_Hu1, hR_Hu1⟩⟩ := bridge_join_both_moments T_fold (H ∪ {u}) {ℓ₁} w ℓ₁ hJ_fold_1
  obtain ⟨_, ⟨h_sc_fold, h_sos_fold⟩⟩ := bridge_join_both_moments T_fold (H ∪ {u} ∪ {ℓ₁}) {ℓ₂} w ℓ₂ hJ_fold_2
  rw [hs_fold_H, hu_f_rc] at hs_Hu
  rw [ht_fold_H, hs_fold_H, hu_f_rc, hu_f_ros] at ht_Hu
  rw [hN_fold_H, hs_fold_H, hu_f_uc, hu_f_rc] at hN_Hu
  rw [hR_fold_H, ht_fold_H, hs_fold_H, hu_f_uos, hu_f_rc, hu_f_ros] at hR_Hu
  rw [hs_Hu, h1_f_rc] at hs_Hu1
  rw [ht_Hu, hs_Hu, h1_f_rc, h1_f_ros] at ht_Hu1
  rw [hN_Hu, hs_Hu, h1_f_uc, h1_f_rc] at hN_Hu1
  rw [hR_Hu, ht_Hu, hs_Hu, h1_f_uos, h1_f_rc, h1_f_ros] at hR_Hu1
  rw [h_fold_univ, h_uc_univ T_fold, hN_Hu1, hs_Hu1, h2_f_uc, h2_f_rc] at h_sc_fold
  rw [h_fold_univ, h_uos_univ T_fold, hR_Hu1, ht_Hu1, hs_Hu1, h2_f_uos, h2_f_rc, h2_f_ros] at h_sos_fold
  have h_sc_fold' : subtreeCount T_fold = unrootedCount T H + 7 * S + 3 := by
    rw [h_sc_fold]; ring
  have h_sos_fold' : subtreeOrderSum T_fold = unrootedOrderSum T H + 7 * t_H + 12 * S + 3 := by
    rw [h_sos_fold]; ring
  have h_fold_le : meanSubtreeOrder T_fold ≤ q := by
    by_contra h_gt
    exact h_no_imp ⟨T_fold, hT_fold, not_le.mp h_gt⟩
  have h_sc_fold_pos : (0 : ℚ) < (subtreeCount T_fold : ℚ) := by
    have : 0 < subtreeCount T_fold := by rw [h_sc_fold']; positivity
    exact_mod_cast this
  have h_fold_ineq : (subtreeOrderSum T_fold : ℚ) ≤ q * (subtreeCount T_fold : ℚ) :=
    (div_le_iff₀ h_sc_fold_pos).mp h_fold_le
  have h_sc_fold_Q : (subtreeCount T_fold : ℚ) = (unrootedCount T H : ℚ) + 7 * (S : ℚ) + 3 := by
    have := congrArg (fun m : ℕ => (m : ℚ)) h_sc_fold'
    push_cast at this; linarith
  have h_sos_fold_Q : (subtreeOrderSum T_fold : ℚ) = (unrootedOrderSum T H : ℚ) + 7 * (t_H : ℚ) + 12 * (S : ℚ) + 3 := by
    have := congrArg (fun m : ℕ => (m : ℚ)) h_sos_fold'
    push_cast at this; linarith
  rw [h_sos_fold_Q, h_sc_fold_Q] at h_fold_ineq
  have h_conj2 : 3 * (t_H : ℚ) + 4 * (S : ℚ) - 7 ≤ q * (3 * ((S : ℚ) - 1)) := by
    linarith [h_bal_H, h_fold_ineq]
  
  have h_swing_general : ∀ (A X : Finset (Fin n)) (z : Fin n),
      H = A ∪ X → IsSubtree T A → IsSubtree T X → IsBridgeJoin T A X w z →
      let a := rootedCount T A w
      let t_A := rootedOrderSum T A w
      let b := rootedCount T X z
      let t_X := rootedOrderSum T X z
      ((b : ℚ) * (8 - (t_A : ℚ)) - ((a : ℚ) - 4) * (t_X : ℚ) ≤
        q * (b : ℚ) * (4 - (a : ℚ))) := by
    intro A X z hH_AX hA_sub hX_sub hBridge_AX a t_A b t_X
    let P_ch : Finset (Fin n) := {u, ℓ₁, ℓ₂}
    let K : Finset (Fin n) := A ∪ P_ch
    have hDisj_AX : Disjoint A X := hBridge_AX.1
    have hw_A : w ∈ A := hBridge_AX.2.1
    have hz_X : z ∈ X := hBridge_AX.2.2.1
    have hadj_wz : T.Adj w z := hBridge_AX.2.2.2.1
    have hDisj_HP : Disjoint H P_ch := hBridge_u.1
    have hu_P : u ∈ P_ch := hBridge_u.2.2.1
    have hadj_wu : T.Adj w u := hBridge_u.2.2.2.1
    have hA_sub_H : A ⊆ H := hH_AX ▸ Finset.subset_union_left
    have hX_sub_H : X ⊆ H := hH_AX ▸ Finset.subset_union_right
    have hDisj_AP : Disjoint A P_ch := Disjoint.mono_left hA_sub_H hDisj_HP
    have hDisj_XP : Disjoint X P_ch := Disjoint.mono_left hX_sub_H hDisj_HP
    have hDisj_KX : Disjoint K X := Finset.disjoint_union_left.mpr ⟨hDisj_AX, hDisj_XP.symm⟩
    have hKX_univ : K ∪ X = Finset.univ := by
      calc K ∪ X = (A ∪ X) ∪ P_ch := by dsimp [K]; rw [Finset.union_right_comm]
        _ = H ∪ P_ch := by rw [← hH_AX]
        _ = Finset.univ := h_univ_union
    have hJ_AP : IsBridgeJoin T A P_ch w u := by
      refine ⟨hDisj_AP, hw_A, hu_P, hadj_wu, ?_⟩
      intro a' ha' b' hb' hab
      exact hBridge_u.2.2.2.2 a' (hA_sub_H ha') b' hb' hab
    have hJ_PA : IsBridgeJoin T P_ch A u w := isBridgeJoin_symm hJ_AP
    have hJ_KX_T : IsBridgeJoin T K X w z := by
      refine ⟨hDisj_KX, Finset.mem_union_left P_ch hw_A, hz_X, hadj_wz, ?_⟩
      intro a' ha' b' hb' hab
      rcases Finset.mem_union.mp ha' with ha'A | ha'P
      · exact hBridge_AX.2.2.2.2 a' ha'A b' hb' hab
      · exfalso
        have hbw : b' = w := (hBridge_u.2.2.2.2 b' (hX_sub_H hb') a' ha'P (T.symm hab)).1
        exact Finset.disjoint_left.mp hDisj_AX hw_A (hbw ▸ hb')
    have hK_sub : IsSubtree T K := h_join_sub T hA_sub hP_sub hJ_AP
    obtain ⟨⟨hs_K_w, ht_K_w⟩, _⟩ := bridge_join_both_moments T A P_ch w u hJ_AP
    obtain ⟨⟨hs_K_u, ht_K_u⟩, _⟩ := bridge_join_both_moments T P_ch A u w hJ_PA
    have hPA_eq_K : P_ch ∪ A = K := Finset.union_comm P_ch A
    rw [hPA_eq_K, h_ch_rc4] at hs_K_u
    rw [hPA_eq_K, h_ch_rc4, h_ch_ros8] at ht_K_u
    rw [h_ch_rc4] at hs_K_w
    rw [h_ch_rc4, h_ch_ros8] at ht_K_w
    change rootedCount T K w = a * (1 + 4) at hs_K_w
    change rootedOrderSum T K w = t_A * (1 + 4) + a * 8 at ht_K_w
    change rootedCount T K u = 4 * (1 + a) at hs_K_u
    change rootedOrderSum T K u = 8 * (1 + a) + 4 * t_A at ht_K_u
    have hu_K : u ∈ K := Finset.mem_union_right A hu_P
    have hw_K : w ∈ K := Finset.mem_union_left P_ch hw_A
    have huz : u ≠ z := fun h => Finset.disjoint_left.mp hDisj_KX hu_K (h ▸ hz_X)
    let T_swing : SimpleGraph (Fin n) :=
      { Adj := fun a' b' => (¬(a' = w ∧ b' = z) ∧ ¬(a' = z ∧ b' = w) ∧ T.Adj a' b') ∨
          (a' = u ∧ b' = z) ∨ (a' = z ∧ b' = u)
        symm := by
          intro a' b' h
          rcases h with ⟨h1, h2, hab⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl ⟨fun ⟨hbw, haz⟩ => h2 ⟨haz, hbw⟩, fun ⟨hbz, haw⟩ => h1 ⟨haw, hbz⟩, T.symm hab⟩
          · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
          · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        loopless := by
          intro a' h
          rcases h with ⟨_, _, haa⟩ | ⟨rfl, h⟩ | ⟨h, rfl⟩
          · exact T.loopless a' haa
          · exact huz h
          · exact huz h }
    have h_not_z_of_K : ∀ v ∈ K, v ≠ z :=
      fun v hv h => Finset.disjoint_left.mp hDisj_KX hv (h ▸ hz_X)
    have h_not_w_of_X : ∀ v ∈ X, v ≠ w :=
      fun v hv h => Finset.disjoint_left.mp hDisj_KX hw_K (h ▸ hv)
    have h_not_u_of_X : ∀ v ∈ X, v ≠ u :=
      fun v hv h => Finset.disjoint_left.mp hDisj_KX hu_K (h ▸ hv)
    have h_adj_K : ∀ a' ∈ K, ∀ b' ∈ K, T_swing.Adj a' b' ↔ T.Adj a' b' := by
      intro a' ha' b' hb'
      have haz : a' ≠ z := h_not_z_of_K a' ha'
      have hbz : b' ≠ z := h_not_z_of_K b' hb'
      change (¬(a' = w ∧ b' = z) ∧ ¬(a' = z ∧ b' = w) ∧ T.Adj a' b') ∨ (a' = u ∧ b' = z) ∨ (a' = z ∧ b' = u) ↔ T.Adj a' b'
      simp [haz, hbz]
    have h_adj_X : ∀ a' ∈ X, ∀ b' ∈ X, T_swing.Adj a' b' ↔ T.Adj a' b' := by
      intro a' ha' b' hb'
      have haw : a' ≠ w := h_not_w_of_X a' ha'
      have hbw : b' ≠ w := h_not_w_of_X b' hb'
      have hau : a' ≠ u := h_not_u_of_X a' ha'
      have hbu : b' ≠ u := h_not_u_of_X b' hb'
      change (¬(a' = w ∧ b' = z) ∧ ¬(a' = z ∧ b' = w) ∧ T.Adj a' b') ∨ (a' = u ∧ b' = z) ∨ (a' = z ∧ b' = u) ↔ T.Adj a' b'
      simp [haw, hbw, hau, hbu]
    have h_induce_K : ∀ S₀ : Finset (Fin n), S₀ ⊆ K →
        T_swing.induce (S₀ : Set (Fin n)) = T.induce (S₀ : Set (Fin n)) := by
      intro S₀ hS₀
      ext ⟨a', ha'⟩ ⟨b', hb'⟩
      exact h_adj_K a' (hS₀ ha') b' (hS₀ hb')
    have h_induce_X : ∀ S₀ : Finset (Fin n), S₀ ⊆ X →
        T_swing.induce (S₀ : Set (Fin n)) = T.induce (S₀ : Set (Fin n)) := by
      intro S₀ hS₀
      ext ⟨a', ha'⟩ ⟨b', hb'⟩
      exact h_adj_X a' (hS₀ ha') b' (hS₀ hb')
    have hK_sub_swing : IsSubtree T_swing K := by
      dsimp [IsSubtree]
      rw [h_induce_K K (Finset.Subset.refl K)]
      exact hK_sub
    have hX_sub_swing : IsSubtree T_swing X := by
      dsimp [IsSubtree]
      rw [h_induce_X X (Finset.Subset.refl X)]
      exact hX_sub
    have hJ_KX_swing : IsBridgeJoin T_swing K X u z := by
      refine ⟨hDisj_KX, hu_K, hz_X, Or.inr (Or.inl ⟨rfl, rfl⟩), ?_⟩
      intro a' ha' b' hb' hab
      rcases hab with ⟨hn1, _, habT⟩ | ⟨rfl, rfl⟩ | ⟨ha'z, _⟩
      · exact False.elim (hn1 (hJ_KX_T.2.2.2.2 a' ha' b' hb' habT))
      · exact ⟨rfl, rfl⟩
      · exact False.elim (h_not_z_of_K a' ha' ha'z)
    have h_swing_univ_sub : IsSubtree T_swing Finset.univ := by
      rw [← hKX_univ]
      exact h_join_sub T_swing hK_sub_swing hX_sub_swing hJ_KX_swing
    have hK_acyc_swing : AcyclicOn T_swing K :=
      acyclicOn_of_adj_imp (fun a' ha' b' hb' hab => (h_adj_K a' ha' b' hb').mp hab)
    have hX_acyc_swing : AcyclicOn T_swing X :=
      acyclicOn_of_adj_imp (fun a' ha' b' hb' hab => (h_adj_X a' ha' b' hb').mp hab)
    have h_swing_univ_acyc : AcyclicOn T_swing Finset.univ := by
      rw [← hKX_univ]
      exact acyclicOn_bridge_join hJ_KX_swing hK_acyc_swing hX_acyc_swing
    have hT_swing : T_swing.IsTree := isTree_of_univ T_swing h_swing_univ_sub h_swing_univ_acyc
    have h_sub_K : subtreesIn T_swing K = subtreesIn T K := by
      ext S₀
      simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
      refine and_congr_left (fun hS₀ => ?_)
      dsimp [IsSubtree]; rw [h_induce_K S₀ hS₀]
    have h_root_K : rootedSubtreesIn T_swing K u = rootedSubtreesIn T K u := by
      ext S₀
      simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
      refine and_congr_left (fun hS₀ => ?_)
      dsimp [IsSubtree]; rw [h_induce_K S₀ hS₀.1]
    have h_sub_X : subtreesIn T_swing X = subtreesIn T X := by
      ext S₀
      simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
      refine and_congr_left (fun hS₀ => ?_)
      dsimp [IsSubtree]; rw [h_induce_X S₀ hS₀]
    have h_root_X : rootedSubtreesIn T_swing X z = rootedSubtreesIn T X z := by
      ext S₀
      simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
      refine and_congr_left (fun hS₀ => ?_)
      dsimp [IsSubtree]; rw [h_induce_X S₀ hS₀.1]
    have hN_K_swing : unrootedCount T_swing K = unrootedCount T K := by
      dsimp [unrootedCount]; rw [h_sub_K]
    have hR_K_swing : unrootedOrderSum T_swing K = unrootedOrderSum T K := by
      dsimp [unrootedOrderSum]; rw [h_sub_K]
    have hs_K_swing : rootedCount T_swing K u = rootedCount T K u := by
      dsimp [rootedCount]; rw [h_root_K]
    have ht_K_swing : rootedOrderSum T_swing K u = rootedOrderSum T K u := by
      dsimp [rootedOrderSum]; rw [h_root_K]
    have hN_X_swing : unrootedCount T_swing X = unrootedCount T X := by
      dsimp [unrootedCount]; rw [h_sub_X]
    have hR_X_swing : unrootedOrderSum T_swing X = unrootedOrderSum T X := by
      dsimp [unrootedOrderSum]; rw [h_sub_X]
    have hs_X_swing : rootedCount T_swing X z = b := by
      dsimp [rootedCount, b]; rw [h_root_X]
    have ht_X_swing : rootedOrderSum T_swing X z = t_X := by
      dsimp [rootedOrderSum, t_X]; rw [h_root_X]
    obtain ⟨_, ⟨h_sc_T_KX, h_sos_T_KX⟩⟩ := bridge_join_both_moments T K X w z hJ_KX_T
    obtain ⟨_, ⟨h_sc_swing, h_sos_swing⟩⟩ := bridge_join_both_moments T_swing K X u z hJ_KX_swing
    rw [hKX_univ, h_uc_univ T, hs_K_w] at h_sc_T_KX
    rw [hKX_univ, h_uos_univ T, hs_K_w, ht_K_w] at h_sos_T_KX
    rw [hKX_univ, h_uc_univ T_swing, hN_K_swing, hN_X_swing, hs_K_swing, hs_K_u, hs_X_swing] at h_sc_swing
    rw [hKX_univ, h_uos_univ T_swing, hR_K_swing, hR_X_swing, hs_K_swing, ht_K_swing, hs_K_u, ht_K_u, hs_X_swing, ht_X_swing] at h_sos_swing
    change subtreeCount T = unrootedCount T K + unrootedCount T X + a * (1 + 4) * b at h_sc_T_KX
    change subtreeOrderSum T = unrootedOrderSum T K + unrootedOrderSum T X + (t_A * (1 + 4) + a * 8) * b + a * (1 + 4) * t_X at h_sos_T_KX
    have h_univ_in_swing : Finset.univ ∈ subtrees T_swing := by
      simp only [subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
      exact h_swing_univ_sub
    have h_sc_swing_pos : (0 : ℚ) < (subtreeCount T_swing : ℚ) := by
      have : 0 < subtreeCount T_swing := Finset.card_pos.mpr ⟨Finset.univ, h_univ_in_swing⟩
      exact_mod_cast this
    have h_swing_le : meanSubtreeOrder T_swing ≤ q := by
      by_contra h_gt
      exact h_no_imp ⟨T_swing, hT_swing, not_le.mp h_gt⟩
    have h_swing_ineq : (subtreeOrderSum T_swing : ℚ) ≤ q * (subtreeCount T_swing : ℚ) :=
      (div_le_iff₀ h_sc_swing_pos).mp h_swing_le
    have h_q_bal_KX := h_q_bal
    have h_sc_T_KX_Q := congrArg (fun m : ℕ => (m : ℚ)) h_sc_T_KX
    have h_sos_T_KX_Q := congrArg (fun m : ℕ => (m : ℚ)) h_sos_T_KX
    have h_sc_swing_Q := congrArg (fun m : ℕ => (m : ℚ)) h_sc_swing
    have h_sos_swing_Q := congrArg (fun m : ℕ => (m : ℚ)) h_sos_swing
    push_cast at h_sc_T_KX_Q h_sos_T_KX_Q h_sc_swing_Q h_sos_swing_Q
    rw [h_sos_T_KX_Q, h_sc_T_KX_Q] at h_q_bal_KX
    rw [h_sos_swing_Q, h_sc_swing_Q] at h_swing_ineq
    linarith
  have h_conj3 : (x : ℚ) * (8 - (t_AB : ℚ)) - ((a_B : ℚ) - 4) * (t_B : ℚ) ≤
      q * (x : ℚ) * (4 - (a_B : ℚ)) := by
    have h_raw := h_swing_general ((insert w L_c) ∪ C) B r_B hH_AB_B hAB_sub hB_sub hBridge_AB_B
    dsimp only at h_raw
    rw [hAB_rc', hAB_ros'] at h_raw
    exact h_raw
  have h_conj4 : (y : ℚ) * (8 - (t_AC : ℚ)) - ((a_C : ℚ) - 4) * (t_C : ℚ) ≤
      q * (y : ℚ) * (4 - (a_C : ℚ)) := by
    have h_raw := h_swing_general ((insert w L_c) ∪ B) C r_C hH_split hAC_sub hC_sub hBridge_C
    dsimp only at h_raw
    rw [hAC_rc', hAC_ros'] at h_raw
    exact h_raw
  exact ⟨h_conj1, h_conj2, h_conj3, h_conj4⟩

theorem subtree_unrooted_moment_bounds : ∀ (n : ℕ) (T : SimpleGraph (Fin n)),
    T.IsTree →
    ∀ (X : Finset (Fin n)) (r : Fin n),
      IsSubtree T X → r ∈ X →
      let s := rootedCount T X r
      let t := rootedOrderSum T X r
      let N := unrootedCount T X
      let R := unrootedOrderSum T X
      1 ≤ s ∧ s ≤ t ∧ 2 * t ≤ s * (s + 1) ∧ R * s ≤ N * t ∧
        (6 * s + 4) * t ≤ 4 * s * N + s ^ 2 * (s + 5) :=
by
  suffices h_gen : ∀ {V : Type} [Fintype V] (T : SimpleGraph V),
      T.IsTree →
      ∀ (U₀ : Finset V) (w₀ : V),
        IsSubtree T U₀ → w₀ ∈ U₀ →
        let s := rootedCount T U₀ w₀
        let t := rootedOrderSum T U₀ w₀
        let N := unrootedCount T U₀
        let R := unrootedOrderSum T U₀
        1 ≤ s ∧ s ≤ t ∧ 2 * t ≤ s * (s + 1) ∧ R * s ≤ N * t ∧
          (6 * s + 4) * t ≤ 4 * s * N + s ^ 2 * (s + 5) by
    intro n T hT X r hX hr
    exact h_gen T hT X r hX hr
  intro V _ T hT U₀ w₀ hU₀ hw₀
  classical
  have singleton_subtree_moments : ∀ (U : Finset V) (w : V),
      w ∈ U → U.card ≤ 1 →
      rootedCount T U w = 1 ∧
      rootedOrderSum T U w = 1 ∧
      (subtreesIn T U).card = 1 ∧
      (∑ S ∈ subtreesIn T U, S.card) = 1 := by
    intro U w hw hle
    have hU_eq : U = {w} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      refine ⟨hw, fun x hx => Finset.card_le_one.mp hle x hx w hw⟩
    subst hU_eq
    have hw_sub : IsSubtree T {w} := by
      refine ⟨Finset.singleton_nonempty w, ?_⟩
      have : Nonempty ↑(({w} : Finset V) : Set V) := ⟨⟨w, by simp⟩⟩
      refine ⟨?_⟩
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      have ha' : a = w := by simpa using ha
      have hb' : b = w := by simpa using hb
      have hab : (⟨a, ha⟩ : ↑(({w} : Finset V) : Set V)) = ⟨b, hb⟩ :=
        Subtype.ext (ha'.trans hb'.symm)
      rw [hab]
    have h_sub_eq : subtreesIn T {w} = {{w}} := by
      ext S
      simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h_ne, _⟩, h_sub⟩
        rcases Finset.subset_singleton_iff.mp h_sub with rfl | rfl
        · exact False.elim (Finset.not_nonempty_empty h_ne)
        · rfl
      · rintro rfl
        exact ⟨hw_sub, Finset.Subset.refl _⟩
    have h_root_eq : rootedSubtreesIn T {w} w = {{w}} := by
      ext S
      simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h_ne, _⟩, h_sub, _⟩
        rcases Finset.subset_singleton_iff.mp h_sub with rfl | rfl
        · exact False.elim (Finset.not_nonempty_empty h_ne)
        · rfl
      · rintro rfl
        exact ⟨hw_sub, Finset.Subset.refl _, Finset.mem_singleton_self w⟩
    simp [rootedCount, rootedOrderSum, h_sub_eq, h_root_eq]
  have isBridgeJoin_symm : ∀ {A B : Finset V} {w r_B : V},
      IsBridgeJoin T A B w r_B → IsBridgeJoin T B A r_B w := by
    intro A B w r_B hJ
    rcases hJ with ⟨h_disj, hw, hr_B, hadj, h_bridge⟩
    refine ⟨h_disj.symm, hr_B, hw, T.symm hadj, ?_⟩
    intro u hu v hv huv
    exact (h_bridge v hv u hu (T.symm huv)).symm
  have exists_walk_of_isSubtree : ∀ {S : Finset V},
      IsSubtree T S → ∀ {a b : V}, a ∈ S → b ∈ S →
      ∃ q : T.Walk a b, ∀ z ∈ q.support, z ∈ S := by
    intro S hS a b ha hb
    obtain ⟨q₀⟩ := hS.2.preconnected ⟨a, ha⟩ ⟨b, hb⟩
    suffices ∀ {u v : ↑(S : Set V)} (q : (T.induce (S : Set V)).Walk u v),
        ∃ q' : T.Walk u.1 v.1, ∀ z ∈ q'.support, z ∈ S from this q₀
    intro u v q
    induction q with
    | @nil u =>
      refine ⟨SimpleGraph.Walk.nil, ?_⟩
      intro z hz
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      rw [hz]
      exact Finset.mem_coe.mp u.2
    | @cons u c v hadj q' ih =>
      obtain ⟨q₁, hq₁⟩ := ih
      refine ⟨SimpleGraph.Walk.cons hadj q₁, ?_⟩
      intro z hz
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz'
      · exact Finset.mem_coe.mp u.2
      · exact hq₁ z hz'
  have bridge_walk_mem_edges : ∀ {A B : Finset V} {w r_B : V},
      IsBridgeJoin T A B w r_B → ∀ {a b : V} (q : T.Walk a b),
      (∀ z ∈ q.support, z ∈ A ∪ B) →
      ((a ∈ A ∧ b ∈ B) ∨ (a ∈ B ∧ b ∈ A)) →
      s(w, r_B) ∈ q.edges := by
    intro A B w r_B hJ a b q
    induction q with
    | nil =>
      intro _ h_ab
      rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact False.elim (Finset.disjoint_left.mp hJ.1 ha hb)
      · exact False.elim (Finset.disjoint_left.mp hJ.1 hb ha)
    | @cons a c b h_step q' ih =>
      intro h_supp h_ab
      have hc_mem : c ∈ A ∪ B := h_supp c (by
        simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.start_mem_support])
      have h_supp' : ∀ z ∈ q'.support, z ∈ A ∪ B := fun z hz =>
        h_supp z (by simp [SimpleGraph.Walk.support_cons, hz])
      rcases Finset.mem_union.mp hc_mem with hcA | hcB
      · rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ (ih h_supp' (Or.inl ⟨hcA, hb⟩))
        · obtain ⟨hcw, har⟩ := hJ.2.2.2.2 c hcA a ha (T.symm h_step)
          subst hcw har
          rw [SimpleGraph.Walk.edges_cons, Sym2.eq_swap]
          exact List.mem_cons_self
      · rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · obtain ⟨haw, hcr⟩ := hJ.2.2.2.2 a ha c hcB h_step
          subst haw hcr
          rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_self
        · rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ (ih h_supp' (Or.inr ⟨hcB, hb⟩))
  have bridge_path_support_left : ∀ {A B : Finset V} {w r_B : V},
      IsBridgeJoin T A B w r_B → ∀ {a b : V} (p : T.Walk a b), p.IsPath →
      (∀ z ∈ p.support, z ∈ A ∪ B) → a ∈ A → b ∈ A →
      ∀ z ∈ p.support, z ∈ A := by
    intro A B w r_B hJ a b p hp h_supp ha hb z hz
    rcases Finset.mem_union.mp (h_supp z hz) with hzA | hzB
    · exact hzA
    · exfalso
      let p₁ := p.takeUntil z hz
      let p₂ := p.dropUntil z hz
      have hp₁_supp : ∀ x ∈ p₁.support, x ∈ A ∪ B :=
        fun x hx => h_supp x (p.support_takeUntil_subset hz hx)
      have hp₂_supp : ∀ x ∈ p₂.support, x ∈ A ∪ B :=
        fun x hx => h_supp x (p.support_dropUntil_subset hz hx)
      have he₁ : s(w, r_B) ∈ p₁.edges :=
        bridge_walk_mem_edges hJ p₁ hp₁_supp (Or.inl ⟨ha, hzB⟩)
      have he₂ : s(w, r_B) ∈ p₂.edges :=
        bridge_walk_mem_edges hJ p₂ hp₂_supp (Or.inr ⟨hzB, hb⟩)
      have h_nodup : p.edges.Nodup := hp.isTrail.edges_nodup
      have h_edges : p₁.edges ++ p₂.edges = p.edges := by
        rw [← SimpleGraph.Walk.edges_append, p.take_spec hz]
      rw [← h_edges, List.nodup_append] at h_nodup
      exact h_nodup.2.2 s(w, r_B) he₁ s(w, r_B) he₂ rfl
  have subtree_exists_root_bridge_split : ∀ (U : Finset V) (w : V),
      IsSubtree T U → w ∈ U → 2 ≤ U.card →
      ∃ (A B : Finset V) (r_B : V),
        U = A ∪ B ∧ IsSubtree T A ∧ IsSubtree T B ∧ IsBridgeJoin T A B w r_B := by
    intro U w hU hw hge2
    obtain ⟨u, hu, huw⟩ := Finset.exists_mem_ne (by omega : 1 < U.card) w
    obtain ⟨p₀⟩ := hU.2.preconnected ⟨w, hw⟩ ⟨u, hu⟩
    have h_adj_exists : ∃ r_B ∈ U, T.Adj w r_B := by
      cases p₀ with
      | nil => exact False.elim (huw rfl)
      | @cons _ r _ hadj _ => exact ⟨r.1, r.2, hadj⟩
    obtain ⟨r_B, hr_B_U, hadj_wr⟩ := h_adj_exists
    let T₀ := T \ SimpleGraph.fromEdgeSet {s(w, r_B)}
    have h_bridge_wr : T.IsBridge s(w, r_B) :=
      SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.IsAcyclic hadj_wr
    have h_not_reach : ¬ T₀.Reachable w r_B :=
      (SimpleGraph.isBridge_iff.mp h_bridge_wr).2
    let A := U.filter (fun v => T₀.Reachable w v)
    let B := U \ A
    have hA_sub : A ⊆ U := Finset.filter_subset _ U
    have hU_eq : U = A ∪ B := (Finset.union_sdiff_of_subset hA_sub).symm
    have h_disj : Disjoint A B := Finset.disjoint_sdiff
    have hw_A : w ∈ A := Finset.mem_filter.mpr ⟨hw, SimpleGraph.Reachable.refl w⟩
    have hr_B : r_B ∈ B := by
      rw [Finset.mem_sdiff]
      refine ⟨hr_B_U, ?_⟩
      rw [Finset.mem_filter]
      rintro ⟨_, h_reach⟩
      exact h_not_reach h_reach
    have hJ : IsBridgeJoin T A B w r_B := by
      refine ⟨h_disj, hw_A, hr_B, hadj_wr, ?_⟩
      intro a ha b hb hab
      by_cases h_edge : s(a, b) = s(w, r_B)
      · rw [Sym2.eq_iff] at h_edge
        rcases h_edge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨rfl, rfl⟩
        · exact False.elim (Finset.disjoint_left.mp h_disj ha hr_B)
      · exfalso
        have hab₀ : T₀.Adj a b := by
          dsimp [T₀]
          rw [SimpleGraph.sdiff_adj, SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff]
          exact ⟨hab, fun ⟨h_eq, _⟩ => h_edge h_eq⟩
        have ha_reach : T₀.Reachable w a := (Finset.mem_filter.mp ha).2
        have hb_reach : T₀.Reachable w b := ha_reach.trans hab₀.reachable
        have hb_A : b ∈ A := Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hb).1, hb_reach⟩
        exact (Finset.mem_sdiff.mp hb).2 hb_A
    have hA_subtree : IsSubtree T A := by
      refine ⟨⟨w, hw_A⟩, ?_⟩
      have : Nonempty ↑(A : Set V) := ⟨⟨w, hw_A⟩⟩
      refine ⟨?_⟩
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      have hxU : x ∈ U := hA_sub hx
      have hyU : y ∈ U := hA_sub hy
      obtain ⟨q, hq_supp⟩ := exists_walk_of_isSubtree hU hxU hyU
      let p : T.Walk x y := (q.toPath : T.Walk x y)
      have hp_path : p.IsPath := q.toPath.2
      have hp_supp : ∀ z ∈ p.support, z ∈ A ∪ B := by
        intro z hz
        rw [← hU_eq]
        exact hq_supp z (q.support_toPath_subset hz)
      have hp_A : ∀ z ∈ p.support, z ∈ (A : Set V) :=
        bridge_path_support_left hJ p hp_path hp_supp hx hy
      exact (p.induce (A : Set V) hp_A).reachable
    have hB_subtree : IsSubtree T B := by
      refine ⟨⟨r_B, hr_B⟩, ?_⟩
      have : Nonempty ↑(B : Set V) := ⟨⟨r_B, hr_B⟩⟩
      refine ⟨?_⟩
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      have hxU : x ∈ U := Finset.sdiff_subset hx
      have hyU : y ∈ U := Finset.sdiff_subset hy
      obtain ⟨q, hq_supp⟩ := exists_walk_of_isSubtree hU hxU hyU
      let p : T.Walk x y := (q.toPath : T.Walk x y)
      have hp_path : p.IsPath := q.toPath.2
      have hp_supp : ∀ z ∈ p.support, z ∈ B ∪ A := by
        intro z hz
        rw [Finset.union_comm, ← hU_eq]
        exact hq_supp z (q.support_toPath_subset hz)
      have hp_B : ∀ z ∈ p.support, z ∈ (B : Set V) :=
        bridge_path_support_left (isBridgeJoin_symm hJ) p hp_path hp_supp hx hy
      exact (p.induce (B : Set V) hp_B).reachable
    exact ⟨A, B, r_B, hU_eq, hA_subtree, hB_subtree, hJ⟩
  have bridge_crossing_left : ∀ {A B S : Finset V} {w r_B : V},
      IsBridgeJoin T A B w r_B → S ⊆ A ∪ B →
      IsSubtree T S → (S ∩ A).Nonempty → (S ∩ B).Nonempty →
      S ∩ A ∈ rootedSubtreesIn T A w := by
    intro A B S w r_B hJ hS_sub hS hSA hSB
    obtain ⟨a₀, ha₀⟩ := hSA
    obtain ⟨b₀, hb₀⟩ := hSB
    have ha₀S : a₀ ∈ S := (Finset.mem_inter.mp ha₀).1
    have ha₀A : a₀ ∈ A := (Finset.mem_inter.mp ha₀).2
    have hb₀S : b₀ ∈ S := (Finset.mem_inter.mp hb₀).1
    have hb₀B : b₀ ∈ B := (Finset.mem_inter.mp hb₀).2
    obtain ⟨q, hq_supp⟩ := exists_walk_of_isSubtree hS ha₀S hb₀S
    have hq_AB : ∀ z ∈ q.support, z ∈ A ∪ B := fun z hz => hS_sub (hq_supp z hz)
    have he : s(w, r_B) ∈ q.edges :=
      bridge_walk_mem_edges hJ q hq_AB (Or.inl ⟨ha₀A, hb₀B⟩)
    have hwS : w ∈ S := hq_supp w (q.fst_mem_support_of_mem_edges he)
    have hwSA : w ∈ S ∩ A := Finset.mem_inter.mpr ⟨hwS, hJ.2.1⟩
    have hSA_subtree : IsSubtree T (S ∩ A) := by
      refine ⟨⟨w, hwSA⟩, ?_⟩
      have : Nonempty ↑((S ∩ A : Finset V) : Set V) := ⟨⟨w, hwSA⟩⟩
      refine ⟨?_⟩
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      have hxS : x ∈ S := (Finset.mem_inter.mp hx).1
      have hxA : x ∈ A := (Finset.mem_inter.mp hx).2
      have hyS : y ∈ S := (Finset.mem_inter.mp hy).1
      have hyA : y ∈ A := (Finset.mem_inter.mp hy).2
      obtain ⟨q₁, hq₁_supp⟩ := exists_walk_of_isSubtree hS hxS hyS
      let p : T.Walk x y := (q₁.toPath : T.Walk x y)
      have hp_path : p.IsPath := q₁.toPath.2
      have hp_S : ∀ z ∈ p.support, z ∈ S := fun z hz => hq₁_supp z (q₁.support_toPath_subset hz)
      have hp_AB : ∀ z ∈ p.support, z ∈ A ∪ B := fun z hz => hS_sub (hp_S z hz)
      have hp_A : ∀ z ∈ p.support, z ∈ A :=
        bridge_path_support_left hJ p hp_path hp_AB hxA hyA
      have hp_SA : ∀ z ∈ p.support, z ∈ ((S ∩ A : Finset V) : Set V) :=
        fun z hz => Finset.mem_inter.mpr ⟨hp_S z hz, hp_A z hz⟩
      exact (p.induce ((S ∩ A : Finset V) : Set V) hp_SA).reachable
    simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hSA_subtree, Finset.inter_subset_right, hwSA⟩
  have bridge_union_isSubtree : ∀ {A B SA SB : Finset V} {w r_B : V},
      IsBridgeJoin T A B w r_B →
      SA ∈ rootedSubtreesIn T A w → SB ∈ rootedSubtreesIn T B r_B →
      IsSubtree T (SA ∪ SB) := by
    intro A B SA SB w r_B hJ hSA hSB
    simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hSA hSB
    rcases hSA with ⟨hSA_sub, _, hw_SA⟩
    rcases hSB with ⟨hSB_sub, _, hr_SB⟩
    have hw_U : w ∈ SA ∪ SB := Finset.mem_union_left SB hw_SA
    have hr_U : r_B ∈ SA ∪ SB := Finset.mem_union_right SA hr_SB
    refine ⟨⟨w, hw_U⟩, ?_⟩
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨w, hw_U⟩, ?_⟩
    rintro ⟨x, hx⟩
    rcases Finset.mem_union.mp hx with hxA | hxB
    · obtain ⟨q, hq⟩ := exists_walk_of_isSubtree hSA_sub hw_SA hxA
      have hq_U : ∀ z ∈ q.support, z ∈ ((SA ∪ SB : Finset V) : Set V) :=
        fun z hz => Finset.mem_union_left SB (hq z hz)
      exact (q.induce ((SA ∪ SB : Finset V) : Set V) hq_U).reachable
    · obtain ⟨q, hq⟩ := exists_walk_of_isSubtree hSB_sub hr_SB hxB
      have hq_U : ∀ z ∈ q.support, z ∈ ((SA ∪ SB : Finset V) : Set V) :=
        fun z hz => Finset.mem_union_right SA (hq z hz)
      have hadj_ind : (T.induce ((SA ∪ SB : Finset V) : Set V)).Adj ⟨w, hw_U⟩ ⟨r_B, hr_U⟩ :=
        hJ.2.2.2.1
      exact hadj_ind.reachable.trans (q.induce ((SA ∪ SB : Finset V) : Set V) hq_U).reachable
  have bridge_join_subtree_moments : ∀ (A B : Finset V) (w r_B : V),
      IsBridgeJoin T A B w r_B →
      rootedCount T (A ∪ B) w = rootedCount T A w * (1 + rootedCount T B r_B) ∧
      rootedOrderSum T (A ∪ B) w =
        rootedOrderSum T A w * (1 + rootedCount T B r_B) + rootedCount T A w * rootedOrderSum T B r_B ∧
      (subtreesIn T (A ∪ B)).card =
        (subtreesIn T A).card + (subtreesIn T B).card + rootedCount T A w * rootedCount T B r_B ∧
      (∑ S ∈ subtreesIn T (A ∪ B), S.card) =
        (∑ S ∈ subtreesIn T A, S.card) + (∑ S ∈ subtreesIn T B, S.card) +
          rootedOrderSum T A w * rootedCount T B r_B + rootedCount T A w * rootedOrderSum T B r_B := by
    intro A B w r_B hJ
    let RA_set := rootedSubtreesIn T A w
    let RB_set := rootedSubtreesIn T B r_B
    let φ : Finset V × Finset V → Finset V := fun p => p.1 ∪ p.2
    let M := (RA_set ×ˢ RB_set).image φ
    have h_inter_left : ∀ {X Y : Finset V}, X ⊆ A → Y ⊆ B → (X ∪ Y) ∩ A = X := by
      intro X Y hX hY
      ext z
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hzX | hzY, hzA⟩
        · exact hzX
        · exact False.elim (Finset.disjoint_left.mp hJ.1 hzA (hY hzY))
      · intro hzX
        exact ⟨Or.inl hzX, hX hzX⟩
    have h_inter_right : ∀ {X Y : Finset V}, X ⊆ A → Y ⊆ B → (X ∪ Y) ∩ B = Y := by
      intro X Y hX hY
      ext z
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hzX | hzY, hzB⟩
        · exact False.elim (Finset.disjoint_left.mp hJ.1 (hX hzX) hzB)
        · exact hzY
      · intro hzY
        exact ⟨Or.inr hzY, hY hzY⟩
    have h_inj : Set.InjOn φ ((RA_set ×ˢ RB_set : Finset (Finset V × Finset V)) : Set (Finset V × Finset V)) := by
      intro p₁ hp₁ p₂ hp₂ h_eq
      rcases Finset.mem_product.mp (Finset.mem_coe.mp hp₁) with ⟨hp₁A, hp₁B⟩
      rcases Finset.mem_product.mp (Finset.mem_coe.mp hp₂) with ⟨hp₂A, hp₂B⟩
      have h1A : p₁.1 ⊆ A := (Finset.mem_filter.mp hp₁A).2.1
      have h1B : p₁.2 ⊆ B := (Finset.mem_filter.mp hp₁B).2.1
      have h2A : p₂.1 ⊆ A := (Finset.mem_filter.mp hp₂A).2.1
      have h2B : p₂.2 ⊆ B := (Finset.mem_filter.mp hp₂B).2.1
      have h1 : p₁.1 = p₂.1 := by
        calc p₁.1 = (p₁.1 ∪ p₁.2) ∩ A := (h_inter_left h1A h1B).symm
          _ = (p₂.1 ∪ p₂.2) ∩ A := by rw [show p₁.1 ∪ p₁.2 = p₂.1 ∪ p₂.2 from h_eq]
          _ = p₂.1 := h_inter_left h2A h2B
      have h2 : p₁.2 = p₂.2 := by
        calc p₁.2 = (p₁.1 ∪ p₁.2) ∩ B := (h_inter_right h1A h1B).symm
          _ = (p₂.1 ∪ p₂.2) ∩ B := by rw [show p₁.1 ∪ p₁.2 = p₂.1 ∪ p₂.2 from h_eq]
          _ = p₂.2 := h_inter_right h2A h2B
      exact Prod.ext h1 h2
    have hM_card : M.card = rootedCount T A w * rootedCount T B r_B := by
      dsimp [M, RA_set, RB_set, rootedCount]
      rw [Finset.card_image_of_injOn h_inj, Finset.card_product]
    have hM_sum : ∑ S ∈ M, S.card =
        rootedOrderSum T A w * rootedCount T B r_B + rootedCount T A w * rootedOrderSum T B r_B := by
      dsimp [M]
      rw [Finset.sum_image h_inj, Finset.sum_product]
      have h_inner : ∀ x ∈ RA_set,
          ∑ y ∈ RB_set, (x ∪ y).card = x.card * RB_set.card + ∑ y ∈ RB_set, y.card := by
        intro x hx
        have hx_sub : x ⊆ A := (Finset.mem_filter.mp hx).2.1
        have h_congr : ∑ y ∈ RB_set, (x ∪ y).card = ∑ y ∈ RB_set, (x.card + y.card) := by
          refine Finset.sum_congr rfl fun y hy => ?_
          have hy_sub : y ⊆ B := (Finset.mem_filter.mp hy).2.1
          exact Finset.card_union_of_disjoint (Disjoint.mono hx_sub hy_sub hJ.1)
        rw [h_congr, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
      rw [Finset.sum_congr rfl h_inner, Finset.sum_add_distrib, ← Finset.sum_mul,
        Finset.sum_const, smul_eq_mul]
      rfl
    have h_mem_M : ∀ S : Finset V,
        S ∈ M ↔ S ∈ subtreesIn T (A ∪ B) ∧ (S ∩ A).Nonempty ∧ (S ∩ B).Nonempty := by
      intro S
      constructor
      · intro hS
        obtain ⟨⟨SA, SB⟩, hp, rfl⟩ := Finset.mem_image.mp hS
        rcases Finset.mem_product.mp hp with ⟨hSA, hSB⟩
        have hSA' := hSA
        have hSB' := hSB
        simp only [RA_set, RB_set, rootedSubtreesIn, subtrees, Finset.mem_filter,
          Finset.mem_univ, true_and] at hSA' hSB'
        have h_sub_AB : SA ∪ SB ⊆ A ∪ B := Finset.union_subset_union hSA'.2.1 hSB'.2.1
        have h_tree : IsSubtree T (SA ∪ SB) := bridge_union_isSubtree hJ hSA hSB
        have h_in_sub : SA ∪ SB ∈ subtreesIn T (A ∪ B) := by
          simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨h_tree, h_sub_AB⟩
        have h_ne_A : ((SA ∪ SB) ∩ A).Nonempty := by
          rw [h_inter_left hSA'.2.1 hSB'.2.1]
          exact ⟨w, hSA'.2.2⟩
        have h_ne_B : ((SA ∪ SB) ∩ B).Nonempty := by
          rw [h_inter_right hSA'.2.1 hSB'.2.1]
          exact ⟨r_B, hSB'.2.2⟩
        exact ⟨h_in_sub, h_ne_A, h_ne_B⟩
      · rintro ⟨hS_in, hSA_ne, hSB_ne⟩
        simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hS_in
        rcases hS_in with ⟨hS_tree, hS_sub⟩
        have hSA_mem : S ∩ A ∈ RA_set := bridge_crossing_left hJ hS_sub hS_tree hSA_ne hSB_ne
        have hS_sub' : S ⊆ B ∪ A := by simpa [Finset.union_comm] using hS_sub
        have hSB_mem : S ∩ B ∈ RB_set :=
          bridge_crossing_left (isBridgeJoin_symm hJ) hS_sub' hS_tree hSB_ne hSA_ne
        refine Finset.mem_image.mpr ⟨(S ∩ A, S ∩ B), Finset.mem_product.mpr ⟨hSA_mem, hSB_mem⟩, ?_⟩
        dsimp [φ]
        rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hS_sub]
    have h_sub_of_inter_empty_right : ∀ {S : Finset V}, S ⊆ A ∪ B → S ∩ B = ∅ → S ⊆ A := by
      intro S hS h_emp z hz
      rcases Finset.mem_union.mp (hS hz) with hzA | hzB
      · exact hzA
      · exfalso
        have : z ∈ (∅ : Finset V) := h_emp ▸ Finset.mem_inter.mpr ⟨hz, hzB⟩
        exact Finset.notMem_empty z this
    have h_sub_of_inter_empty_left : ∀ {S : Finset V}, S ⊆ A ∪ B → S ∩ A = ∅ → S ⊆ B := by
      intro S hS h_emp z hz
      rcases Finset.mem_union.mp (hS hz) with hzA | hzB
      · exfalso
        have : z ∈ (∅ : Finset V) := h_emp ▸ Finset.mem_inter.mpr ⟨hz, hzA⟩
        exact Finset.notMem_empty z this
      · exact hzB
    have h_root_disj : Disjoint RA_set M := by
      rw [Finset.disjoint_left]
      intro S hS_RA hS_M
      obtain ⟨_, _, b, hb⟩ := (h_mem_M S).mp hS_M
      have hS_A : S ⊆ A := (Finset.mem_filter.mp hS_RA).2.1
      exact Finset.disjoint_left.mp hJ.1 (hS_A (Finset.mem_inter.mp hb).1) (Finset.mem_inter.mp hb).2
    have h_root_part : rootedSubtreesIn T (A ∪ B) w = RA_set ∪ M := by
      ext S
      rw [Finset.mem_union, h_mem_M]
      constructor
      · intro hS
        simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hS
        rcases hS with ⟨hS_tree, hS_sub, hwS⟩
        rcases Finset.eq_empty_or_nonempty (S ∩ B) with h_emp | hSB_ne
        · left
          simp only [RA_set, rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hS_tree, h_sub_of_inter_empty_right hS_sub h_emp, hwS⟩
        · right
          have hS_in : S ∈ subtreesIn T (A ∪ B) := by
            simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hS_tree, hS_sub⟩
          exact ⟨hS_in, ⟨w, Finset.mem_inter.mpr ⟨hwS, hJ.2.1⟩⟩, hSB_ne⟩
      · rintro (hS_RA | ⟨hS_in, hSA_ne, hSB_ne⟩)
        · simp only [RA_set, rootedSubtreesIn, subtrees, Finset.mem_filter,
            Finset.mem_univ, true_and] at hS_RA ⊢
          exact ⟨hS_RA.1, Finset.Subset.trans hS_RA.2.1 Finset.subset_union_left, hS_RA.2.2⟩
        · simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hS_in
          have hSA_mem : S ∩ A ∈ RA_set :=
            bridge_crossing_left hJ hS_in.2 hS_in.1 hSA_ne hSB_ne
          have hw_SA : w ∈ S ∩ A := (Finset.mem_filter.mp hSA_mem).2.2
          simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hS_in.1, hS_in.2, (Finset.mem_inter.mp hw_SA).1⟩
    have h_sub_AB_disj : Disjoint (subtreesIn T A) (subtreesIn T B) := by
      rw [Finset.disjoint_left]
      intro S hSA hSB
      simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hSA hSB
      obtain ⟨x, hx⟩ := hSA.1.1
      exact Finset.disjoint_left.mp hJ.1 (hSA.2 hx) (hSB.2 hx)
    have h_sub_M_disj : Disjoint (subtreesIn T A ∪ subtreesIn T B) M := by
      rw [Finset.disjoint_left]
      intro S hS_AB hS_M
      obtain ⟨_, ⟨a, ha⟩, ⟨b, hb⟩⟩ := (h_mem_M S).mp hS_M
      rcases Finset.mem_union.mp hS_AB with hSA | hSB
      · have hS_A : S ⊆ A := (Finset.mem_filter.mp hSA).2
        exact Finset.disjoint_left.mp hJ.1 (hS_A (Finset.mem_inter.mp hb).1) (Finset.mem_inter.mp hb).2
      · have hS_B : S ⊆ B := (Finset.mem_filter.mp hSB).2
        exact Finset.disjoint_left.mp hJ.1 (Finset.mem_inter.mp ha).2 (hS_B (Finset.mem_inter.mp ha).1)
    have h_sub_part : subtreesIn T (A ∪ B) = (subtreesIn T A ∪ subtreesIn T B) ∪ M := by
      ext S
      rw [Finset.mem_union, Finset.mem_union, h_mem_M]
      constructor
      · intro hS
        have hS' := hS
        simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hS'
        rcases hS' with ⟨hS_tree, hS_sub⟩
        rcases Finset.eq_empty_or_nonempty (S ∩ B) with hB_emp | hSB_ne
        · left; left
          simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hS_tree, h_sub_of_inter_empty_right hS_sub hB_emp⟩
        · rcases Finset.eq_empty_or_nonempty (S ∩ A) with hA_emp | hSA_ne
          · left; right
            simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hS_tree, h_sub_of_inter_empty_left hS_sub hA_emp⟩
          · right
            exact ⟨hS, hSA_ne, hSB_ne⟩
      · rintro ((hSA | hSB) | ⟨hS, _, _⟩)
        · simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hSA ⊢
          exact ⟨hSA.1, Finset.Subset.trans hSA.2 Finset.subset_union_left⟩
        · simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hSB ⊢
          exact ⟨hSB.1, Finset.Subset.trans hSB.2 Finset.subset_union_right⟩
        · exact hS
    have h_eq1 : rootedCount T (A ∪ B) w = rootedCount T A w * (1 + rootedCount T B r_B) := by
      dsimp [rootedCount]
      rw [h_root_part, Finset.card_union_of_disjoint h_root_disj, hM_card]
      dsimp [RA_set, rootedCount]
      ring
    have h_eq2 : rootedOrderSum T (A ∪ B) w =
        rootedOrderSum T A w * (1 + rootedCount T B r_B) + rootedCount T A w * rootedOrderSum T B r_B := by
      dsimp [rootedOrderSum]
      rw [h_root_part, Finset.sum_union h_root_disj, hM_sum]
      dsimp [RA_set, rootedOrderSum]
      ring
    have h_eq3 : (subtreesIn T (A ∪ B)).card =
        (subtreesIn T A).card + (subtreesIn T B).card + rootedCount T A w * rootedCount T B r_B := by
      rw [h_sub_part, Finset.card_union_of_disjoint h_sub_M_disj,
        Finset.card_union_of_disjoint h_sub_AB_disj, hM_card]
    have h_eq4 : (∑ S ∈ subtreesIn T (A ∪ B), S.card) =
        (∑ S ∈ subtreesIn T A, S.card) + (∑ S ∈ subtreesIn T B, S.card) +
          rootedOrderSum T A w * rootedCount T B r_B + rootedCount T A w * rootedOrderSum T B r_B := by
      rw [h_sub_part, Finset.sum_union h_sub_M_disj,
        Finset.sum_union h_sub_AB_disj, hM_sum]
      ring
    exact ⟨h_eq1, h_eq2, h_eq3, h_eq4⟩
  have bridge_join_moment_ineq_step : ∀ (sA tA NA RA sB tB NB RB : ℕ),
      1 ≤ sA → sA ≤ tA → sA ≤ NA → 2 * tA ≤ sA * (sA + 1) → sA * RA ≤ tA * NA →
      (6 * sA + 4) * tA ≤ 4 * sA * NA + sA ^ 2 * (sA + 5) →
      1 ≤ sB → sB ≤ tB → sB ≤ NB → 2 * tB ≤ sB * (sB + 1) → sB * RB ≤ tB * NB →
      (6 * sB + 4) * tB ≤ 4 * sB * NB + sB ^ 2 * (sB + 5) →
      let s := sA * (1 + sB)
      let t := tA * (1 + sB) + sA * tB
      let N := NA + NB + sA * sB
      let R := RA + RB + tA * sB + sA * tB
      1 ≤ s ∧ s ≤ t ∧ s ≤ N ∧ 2 * t ≤ s * (s + 1) ∧ s * R ≤ t * N ∧
        (6 * s + 4) * t ≤ 4 * s * N + s ^ 2 * (s + 5) := by
    intro sA tA NA RA sB tB NB RB hsA1 hstA hsNA h2tA hlgA hB3A hsB1 hstB hsNB h2tB hlgB hB3B
    dsimp only
    refine ⟨by nlinarith, by nlinarith, by nlinarith, ?_, ?_, ?_⟩
    · zify at hsA1 hstA hsNA h2tA hlgA hsB1 hstB hsNB h2tB hlgB ⊢
      have h_id1 :
          (sA : ℤ) * (1 + sB) * ((sA : ℤ) * (1 + sB) + 1) -
            2 * ((tA : ℤ) * (1 + sB) + (sA : ℤ) * tB) =
          (1 + (sB : ℤ)) * ((sA : ℤ) * (sA + 1) - 2 * tA) +
          (sA : ℤ) * ((sB : ℤ) * (sB + 1) - 2 * tB) +
          (sA : ℤ) * (1 + sB) * (sA - 1) * sB := by ring
      have h1 : 0 ≤ (1 + (sB : ℤ)) * ((sA : ℤ) * (sA + 1) - 2 * tA) :=
        mul_nonneg (by omega) (by omega)
      have h2 : 0 ≤ (sA : ℤ) * ((sB : ℤ) * (sB + 1) - 2 * tB) :=
        mul_nonneg (by omega) (by omega)
      have h3 : 0 ≤ (sA : ℤ) * (1 + sB) * (sA - 1) * sB :=
        mul_nonneg (mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)) (by omega)
      linarith
    · zify at hsA1 hstA hsNA h2tA hlgA hsB1 hstB hsNB h2tB hlgB ⊢
      have h_id2 :
          (sB : ℤ) * (((tA : ℤ) * (1 + sB) + (sA : ℤ) * tB) * ((NA : ℤ) + NB + (sA : ℤ) * sB) -
            (sA : ℤ) * (1 + sB) * ((RA : ℤ) + RB + (tA : ℤ) * sB + (sA : ℤ) * tB)) =
          (sB : ℤ) * (1 + sB) * ((tA : ℤ) * NA - (sA : ℤ) * RA) +
          (sA : ℤ) * (1 + sB) * ((tB : ℤ) * NB - (sB : ℤ) * RB) +
          (sA : ℤ) * sB * tB * ((NA : ℤ) - sA) +
          (NB : ℤ) * (((tA : ℤ) - sA) * sB * (1 + sB) +
            (sA : ℤ) * ((sB : ℤ) * (1 + sB) - tB)) := by ring
      have htB_le : (tB : ℤ) ≤ (sB : ℤ) * (1 + sB) := by linarith
      have h1 : 0 ≤ (sB : ℤ) * (1 + sB) * ((tA : ℤ) * NA - (sA : ℤ) * RA) :=
        mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)
      have h2 : 0 ≤ (sA : ℤ) * (1 + sB) * ((tB : ℤ) * NB - (sB : ℤ) * RB) :=
        mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)
      have h3 : 0 ≤ (sA : ℤ) * sB * tB * ((NA : ℤ) - sA) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)) (by omega)
      have h4 : 0 ≤ (NB : ℤ) * (((tA : ℤ) - sA) * sB * (1 + sB) +
          (sA : ℤ) * ((sB : ℤ) * (1 + sB) - tB)) := by
        refine mul_nonneg (by omega) (add_nonneg ?_ ?_)
        · exact mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)
        · exact mul_nonneg (by omega) (by omega)
      have h_prod : 0 ≤ (sB : ℤ) * (((tA : ℤ) * (1 + sB) + (sA : ℤ) * tB) * ((NA : ℤ) + NB + (sA : ℤ) * sB) -
          (sA : ℤ) * (1 + sB) * ((RA : ℤ) + RB + (tA : ℤ) * sB + (sA : ℤ) * tB)) := by
        linarith
      nlinarith
    · zify at hsA1 hstA hsNA h2tA hlgA hB3A hsB1 hstB hsNB h2tB hlgB hB3B ⊢
      have h_sA_quad : 0 ≤ ((sA : ℤ) - 1) * ((sA : ℤ) - 2) := by
        rcases le_or_gt (sA : ℤ) 1 with h | h
        · have h_eq : (sA : ℤ) = 1 := by omega
          rw [h_eq]
          omega
        · exact mul_nonneg (by omega) (by omega)
      let FA : ℤ := 4 * (sA : ℤ) * NA + (sA : ℤ) ^ 2 * (sA + 5) - (6 * (sA : ℤ) + 4) * tA
      let FB : ℤ := 4 * (sB : ℤ) * NB + (sB : ℤ) ^ 2 * (sB + 5) - (6 * (sB : ℤ) + 4) * tB
      let EA : ℤ := (sA : ℤ) * (sA + 1) - 2 * tA
      let EB : ℤ := (sB : ℤ) * (sB + 1) - 2 * tB
      let F : ℤ :=
        4 * ((sA : ℤ) * (1 + sB)) * ((NA : ℤ) + NB + (sA : ℤ) * sB) +
          ((sA : ℤ) * (1 + sB)) ^ 2 * ((sA : ℤ) * (1 + sB) + 5) -
          (6 * ((sA : ℤ) * (1 + sB)) + 4) * ((tA : ℤ) * (1 + sB) + (sA : ℤ) * tB)
      have h_id3 :
          (sB : ℤ) * F =
          (sB : ℤ) * (1 + sB) * FA +
          (sA : ℤ) * (1 + sB) * FB +
          3 * (sA : ℤ) * (sB : ℤ) ^ 2 * (1 + sB) * EA +
          3 * (sA : ℤ) * (sA - 1) * sB * (1 + sB) * EB +
          4 * (sA : ℤ) * tB +
          (sA : ℤ) * (((sA : ℤ) - 1) * ((sA : ℤ) - 2)) * (sB : ℤ) ^ 2 * (sB - 1) * (1 + sB) := by
        dsimp [FA, FB, EA, EB, F]
        ring
      have hFA : 0 ≤ FA := by dsimp [FA]; linarith
      have hFB : 0 ≤ FB := by dsimp [FB]; linarith
      have hEA : 0 ≤ EA := by dsimp [EA]; linarith
      have hEB : 0 ≤ EB := by dsimp [EB]; linarith
      have h_t1 : 0 ≤ (sB : ℤ) * (1 + sB) * FA :=
        mul_nonneg (mul_nonneg (by omega) (by omega)) hFA
      have h_t2 : 0 ≤ (sA : ℤ) * (1 + sB) * FB :=
        mul_nonneg (mul_nonneg (by omega) (by omega)) hFB
      have h_t3 : 0 ≤ 3 * (sA : ℤ) * (sB : ℤ) ^ 2 * (1 + sB) * EA :=
        mul_nonneg (mul_nonneg (mul_nonneg (by omega) (sq_nonneg _)) (by omega)) hEA
      have h_t4 : 0 ≤ 3 * (sA : ℤ) * (sA - 1) * sB * (1 + sB) * EB :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)) (by omega)) hEB
      have h_t5 : 0 ≤ 4 * (sA : ℤ) * tB :=
        mul_nonneg (by omega) (by omega)
      have h_t6 : 0 ≤ (sA : ℤ) * (((sA : ℤ) - 1) * ((sA : ℤ) - 2)) * (sB : ℤ) ^ 2 * (sB - 1) * (1 + sB) :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by omega) h_sA_quad) (sq_nonneg _)) (by omega)) (by omega)
      have h_sBF : 0 ≤ (sB : ℤ) * F := by linarith
      have hF : 0 ≤ F := by nlinarith
      dsimp [F] at hF
      linarith
  have h_ind : ∀ (m : ℕ) (U : Finset V) (w : V),
      U.card = m → IsSubtree T U → w ∈ U →
      1 ≤ rootedCount T U w ∧
      rootedCount T U w ≤ rootedOrderSum T U w ∧
      rootedCount T U w ≤ (subtreesIn T U).card ∧
      2 * rootedOrderSum T U w ≤ rootedCount T U w * (rootedCount T U w + 1) ∧
      rootedCount T U w * (∑ S ∈ subtreesIn T U, S.card) ≤
        rootedOrderSum T U w * (subtreesIn T U).card ∧
      (6 * rootedCount T U w + 4) * rootedOrderSum T U w ≤
        4 * rootedCount T U w * (subtreesIn T U).card +
          (rootedCount T U w) ^ 2 * (rootedCount T U w + 5) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro U w hm hU hw
      by_cases hle : U.card ≤ 1
      · obtain ⟨hs, ht, hN, hR⟩ := singleton_subtree_moments U w hw hle
        rw [hs, ht, hN, hR]
        omega
      · push_neg at hle
        obtain ⟨A, B, r_B, hU_eq, hA_sub, hB_sub, hJ⟩ :=
          subtree_exists_root_bridge_split U w hU hw hle
        have hA_pos : 0 < A.card := Finset.card_pos.mpr ⟨w, hJ.2.1⟩
        have hB_pos : 0 < B.card := Finset.card_pos.mpr ⟨r_B, hJ.2.2.1⟩
        have hU_card : U.card = A.card + B.card := by
          rw [hU_eq, Finset.card_union_of_disjoint hJ.1]
        have hA_lt : A.card < m := by omega
        have hB_lt : B.card < m := by omega
        obtain ⟨hsA1, hstA, hsNA, h2tA, hlgA, hB3A⟩ := ih A.card hA_lt A w rfl hA_sub hJ.2.1
        obtain ⟨hsB1, hstB, hsNB, h2tB, hlgB, hB3B⟩ := ih B.card hB_lt B r_B rfl hB_sub hJ.2.2.1
        obtain ⟨h_s, h_t, h_N, h_R⟩ := bridge_join_subtree_moments A B w r_B hJ
        rw [hU_eq, h_s, h_t, h_N, h_R]
        exact bridge_join_moment_ineq_step
          (rootedCount T A w) (rootedOrderSum T A w) (subtreesIn T A).card (∑ S ∈ subtreesIn T A, S.card)
          (rootedCount T B r_B) (rootedOrderSum T B r_B) (subtreesIn T B).card (∑ S ∈ subtreesIn T B, S.card)
          hsA1 hstA hsNA h2tA hlgA hB3A hsB1 hstB hsNB h2tB hlgB hB3B
  obtain ⟨h1, h2, _, h3, h4, h5⟩ := h_ind U₀.card U₀ w₀ rfl hU₀ hw₀
  dsimp [unrootedCount, unrootedOrderSum]
  refine ⟨h1, h2, h3, ?_, h5⟩
  linarith

theorem cherry_three_branch_algebraic_contradiction : ∀ (c x y t_B t_C N_B N_C R_B R_C : ℕ) (q : ℚ),
      c ≤ 1 → 4 ≤ x → 4 ≤ y →
      x ≤ t_B → 2 * t_B ≤ x * (x + 1) → R_B * x ≤ N_B * t_B →
      (6 * x + 4) * t_B ≤ 4 * x * N_B + x ^ 2 * (x + 5) →
      y ≤ t_C → 2 * t_C ≤ y * (y + 1) → R_C * y ≤ N_C * t_C →
      (6 * y + 4) * t_C ≤ 4 * y * N_C + y ^ 2 * (y + 5) →
      let p := 2 ^ c
      let S := p * (1 + x) * (1 + y)
      let t_H := (p + c) * (1 + x) * (1 + y) + p * (1 + y) * t_B + p * (1 + x) * t_C
      let a_B := p * (1 + y)
      let t_AB := (p + c) * (1 + y) + p * t_C
      let a_C := p * (1 + x)
      let t_AC := (p + c) * (1 + x) + p * t_B
      (5 * (t_H : ℚ) + 8 * (S : ℚ) + (R_B : ℚ) + (R_C : ℚ) + 10 + (c : ℚ) =
        q * (5 * (S : ℚ) + (N_B : ℚ) + (N_C : ℚ) + 6 + (c : ℚ))) →
      (3 * (t_H : ℚ) + 4 * (S : ℚ) - 7 ≤ q * (3 * ((S : ℚ) - 1))) →
      ((x : ℚ) * (8 - (t_AB : ℚ)) - ((a_B : ℚ) - 4) * (t_B : ℚ) ≤
        q * (x : ℚ) * (4 - (a_B : ℚ))) →
      ((y : ℚ) * (8 - (t_AC : ℚ)) - ((a_C : ℚ) - 4) * (t_C : ℚ) ≤
        q * (y : ℚ) * (4 - (a_C : ℚ))) →
      False :=
by
  intro c x y t_B t_C N_B N_C R_B R_C q hc hx hy h1B h2B h3B h4B h1C h2C h3C h4C p S t_H a_B t_AB a_C t_AC h_bal h_fold h_swingB h_swingC
  have hxQ : (4 : ℚ) ≤ (x : ℚ) := by exact_mod_cast hx
  have hyQ : (4 : ℚ) ≤ (y : ℚ) := by exact_mod_cast hy
  have h1BQ : (x : ℚ) ≤ (t_B : ℚ) := by exact_mod_cast h1B
  have h2BQ : 2 * (t_B : ℚ) ≤ (x : ℚ) * ((x : ℚ) + 1) := by exact_mod_cast h2B
  have h3BQ : (R_B : ℚ) * (x : ℚ) ≤ (N_B : ℚ) * (t_B : ℚ) := by exact_mod_cast h3B
  have h4BQ : (6 * (x : ℚ) + 4) * (t_B : ℚ) ≤ 4 * (x : ℚ) * (N_B : ℚ) + (x : ℚ) ^ 2 * ((x : ℚ) + 5) := by
    exact_mod_cast h4B
  have h1CQ : (y : ℚ) ≤ (t_C : ℚ) := by exact_mod_cast h1C
  have h2CQ : 2 * (t_C : ℚ) ≤ (y : ℚ) * ((y : ℚ) + 1) := by exact_mod_cast h2C
  have h3CQ : (R_C : ℚ) * (y : ℚ) ≤ (N_C : ℚ) * (t_C : ℚ) := by exact_mod_cast h3C
  have h4CQ : (6 * (y : ℚ) + 4) * (t_C : ℚ) ≤ 4 * (y : ℚ) * (N_C : ℚ) + (y : ℚ) ^ 2 * ((y : ℚ) + 5) := by
    exact_mod_cast h4C
  have hx_pos : 0 < (x : ℚ) := by linarith only [hxQ]
  have hy_pos : 0 < (y : ℚ) := by linarith only [hyQ]
  have hc_cases : c = 0 ∨ c = 1 := by omega
  rcases hc_cases with rfl | rfl
  · 
    let β : ℚ := (t_B : ℚ) / (x : ℚ)
    let γ : ℚ := (t_C : ℚ) / (y : ℚ)
    let S1 : ℚ := (x : ℚ) * (y : ℚ) + (x : ℚ) + (y : ℚ)
    have htB : (t_B : ℚ) = (x : ℚ) * β := (mul_div_cancel₀ (t_B : ℚ) (ne_of_gt hx_pos)).symm
    have htC : (t_C : ℚ) = (y : ℚ) * γ := (mul_div_cancel₀ (t_C : ℚ) (ne_of_gt hy_pos)).symm
    have hβ_ge1 : 1 ≤ β := by
      have h_id : (t_B : ℚ) - (x : ℚ) = (x : ℚ) * (β - 1) := by rw [htB]; ring
      have h0 := nonneg_of_mul_nonneg_right (by linarith only [h1BQ, h_id] : 0 ≤ (x : ℚ) * (β - 1)) hx_pos
      linarith only [h0]
    have hβ_le : β ≤ ((x : ℚ) + 1) / 2 := by
      have h_id : (x : ℚ) * ((x : ℚ) + 1) - 2 * (t_B : ℚ) = (2 * (x : ℚ)) * (((x : ℚ) + 1) / 2 - β) := by
        rw [htB]; ring
      have h0 := nonneg_of_mul_nonneg_right (by linarith only [h2BQ, h_id] : 0 ≤ (2 * (x : ℚ)) * (((x : ℚ) + 1) / 2 - β)) (by positivity)
      linarith only [h0]
    have hγ_ge1 : 1 ≤ γ := by
      have h_id : (t_C : ℚ) - (y : ℚ) = (y : ℚ) * (γ - 1) := by rw [htC]; ring
      have h0 := nonneg_of_mul_nonneg_right (by linarith only [h1CQ, h_id] : 0 ≤ (y : ℚ) * (γ - 1)) hy_pos
      linarith only [h0]
    have hγ_le : γ ≤ ((y : ℚ) + 1) / 2 := by
      have h_id : (y : ℚ) * ((y : ℚ) + 1) - 2 * (t_C : ℚ) = (2 * (y : ℚ)) * (((y : ℚ) + 1) / 2 - γ) := by
        rw [htC]; ring
      have h0 := nonneg_of_mul_nonneg_right (by linarith only [h2CQ, h_id] : 0 ≤ (2 * (y : ℚ)) * (((y : ℚ) + 1) / 2 - γ)) (by positivity)
      linarith only [h0]
    have hRB_le : (R_B : ℚ) ≤ β * (N_B : ℚ) := by
      have h_id : (N_B : ℚ) * (t_B : ℚ) - (R_B : ℚ) * (x : ℚ) = (x : ℚ) * (β * (N_B : ℚ) - (R_B : ℚ)) := by
        rw [htB]; ring
      have h0 := nonneg_of_mul_nonneg_right (by linarith only [h3BQ, h_id] : 0 ≤ (x : ℚ) * (β * (N_B : ℚ) - (R_B : ℚ))) hx_pos
      linarith only [h0]
    have hRC_le : (R_C : ℚ) ≤ γ * (N_C : ℚ) := by
      have h_id : (N_C : ℚ) * (t_C : ℚ) - (R_C : ℚ) * (y : ℚ) = (y : ℚ) * (γ * (N_C : ℚ) - (R_C : ℚ)) := by
        rw [htC]; ring
      have h0 := nonneg_of_mul_nonneg_right (by linarith only [h3CQ, h_id] : 0 ≤ (y : ℚ) * (γ * (N_C : ℚ) - (R_C : ℚ))) hy_pos
      linarith only [h0]
    have hNB_le : cherryB0 (x : ℚ) β ≤ (N_B : ℚ) := by
      have h_id : 4 * (x : ℚ) * (N_B : ℚ) + (x : ℚ) ^ 2 * ((x : ℚ) + 5) - (6 * (x : ℚ) + 4) * (t_B : ℚ) =
          (4 * (x : ℚ)) * ((N_B : ℚ) - cherryB0 (x : ℚ) β) := by unfold cherryB0; rw [htB]; ring
      have h0 := nonneg_of_mul_nonneg_right (by linarith only [h4BQ, h_id] : 0 ≤ (4 * (x : ℚ)) * ((N_B : ℚ) - cherryB0 (x : ℚ) β)) (by positivity)
      linarith only [h0]
    have hNC_le : cherryB0 (y : ℚ) γ ≤ (N_C : ℚ) := by
      have h_id : 4 * (y : ℚ) * (N_C : ℚ) + (y : ℚ) ^ 2 * ((y : ℚ) + 5) - (6 * (y : ℚ) + 4) * (t_C : ℚ) =
          (4 * (y : ℚ)) * ((N_C : ℚ) - cherryB0 (y : ℚ) γ) := by unfold cherryB0; rw [htC]; ring
      have h0 := nonneg_of_mul_nonneg_right (by linarith only [h4CQ, h_id] : 0 ≤ (4 * (y : ℚ)) * ((N_C : ℚ) - cherryB0 (y : ℚ) γ)) (by positivity)
      linarith only [h0]
    have hSQ : (S : ℚ) = (1 + (x : ℚ)) * (1 + (y : ℚ)) := by dsimp [S, p]; push_cast; ring
    have htHQ : (t_H : ℚ) = (1 + (x : ℚ)) * (1 + (y : ℚ)) + (1 + (y : ℚ)) * ((x : ℚ) * β) +
        (1 + (x : ℚ)) * ((y : ℚ) * γ) := by dsimp [t_H, p]; push_cast; rw [htB, htC]; ring
    have haBQ : (a_B : ℚ) = 1 + (y : ℚ) := by dsimp [a_B, p]; push_cast; ring
    have htABQ : (t_AB : ℚ) = 1 + (y : ℚ) + (y : ℚ) * γ := by dsimp [t_AB, p]; push_cast; rw [htC]; ring
    have haCQ : (a_C : ℚ) = 1 + (x : ℚ) := by dsimp [a_C, p]; push_cast; ring
    have htACQ : (t_AC : ℚ) = 1 + (x : ℚ) + (x : ℚ) * β := by dsimp [t_AC, p]; push_cast; rw [htB]; ring
    let Q0 : ℚ := 7 / 3 * S1 + (x : ℚ) * ((y : ℚ) + 1) * β + (y : ℚ) * ((x : ℚ) + 1) * γ
    have hS1_pos : 0 < S1 := by dsimp [S1]; positivity
    have h_fold_id : 3 * Q0 = 3 * (t_H : ℚ) + 4 * (S : ℚ) - 7 := by
      dsimp [Q0, S1]; rw [htHQ, hSQ]; ring
    have h_S_sub : q * (3 * ((S : ℚ) - 1)) = 3 * (S1 * q) := by dsimp [S1]; rw [hSQ]; ring
    have h_Sq_ge : Q0 ≤ S1 * q := by linarith only [h_fold, h_fold_id, h_S_sub]
    have h_swingB_id : S1 * (q * (x : ℚ) * (4 - (a_B : ℚ)) - ((x : ℚ) * (8 - (t_AB : ℚ)) - ((a_B : ℚ) - 4) * (t_B : ℚ))) =
        ((x : ℚ) * (y : ℚ)) * (-(4 / 3 * S1 - ((y : ℚ) - 3) * β - (4 * (x : ℚ) + 3) * γ)) -
        (x : ℚ) * ((y : ℚ) - 3) * (S1 * q - Q0) := by
      dsimp [Q0, S1]; rw [htABQ, haBQ, htB]; ring
    have hLB : 4 / 3 * S1 - ((y : ℚ) - 3) * β - (4 * (x : ℚ) + 3) * γ ≤ 0 := by
      have h_lhs_nonneg : 0 ≤ S1 * (q * (x : ℚ) * (4 - (a_B : ℚ)) - ((x : ℚ) * (8 - (t_AB : ℚ)) - ((a_B : ℚ) - 4) * (t_B : ℚ))) :=
        mul_nonneg (le_of_lt hS1_pos) (by linarith only [h_swingB])
      have h_term2 : 0 ≤ (x : ℚ) * ((y : ℚ) - 3) * (S1 * q - Q0) :=
        mul_nonneg (mul_nonneg (le_of_lt hx_pos) (by linarith only [hyQ])) (by linarith only [h_Sq_ge])
      have h_prod : 0 ≤ ((x : ℚ) * (y : ℚ)) * (-(4 / 3 * S1 - ((y : ℚ) - 3) * β - (4 * (x : ℚ) + 3) * γ)) := by
        linarith only [h_swingB_id, h_lhs_nonneg, h_term2]
      have h0 := nonneg_of_mul_nonneg_right h_prod (by positivity)
      linarith only [h0]
    have h_swingC_id : S1 * (q * (y : ℚ) * (4 - (a_C : ℚ)) - ((y : ℚ) * (8 - (t_AC : ℚ)) - ((a_C : ℚ) - 4) * (t_C : ℚ))) =
        ((x : ℚ) * (y : ℚ)) * (-(4 / 3 * S1 - (4 * (y : ℚ) + 3) * β - ((x : ℚ) - 3) * γ)) -
        (y : ℚ) * ((x : ℚ) - 3) * (S1 * q - Q0) := by
      dsimp [Q0, S1]; rw [htACQ, haCQ, htC]; ring
    have hLC : 4 / 3 * S1 - (4 * (y : ℚ) + 3) * β - ((x : ℚ) - 3) * γ ≤ 0 := by
      have h_lhs_nonneg : 0 ≤ S1 * (q * (y : ℚ) * (4 - (a_C : ℚ)) - ((y : ℚ) * (8 - (t_AC : ℚ)) - ((a_C : ℚ) - 4) * (t_C : ℚ))) :=
        mul_nonneg (le_of_lt hS1_pos) (by linarith only [h_swingC])
      have h_term2 : 0 ≤ (y : ℚ) * ((x : ℚ) - 3) * (S1 * q - Q0) :=
        mul_nonneg (mul_nonneg (le_of_lt hy_pos) (by linarith only [hxQ])) (by linarith only [h_Sq_ge])
      have h_prod : 0 ≤ ((x : ℚ) * (y : ℚ)) * (-(4 / 3 * S1 - (4 * (y : ℚ) + 3) * β - ((x : ℚ) - 3) * γ)) := by
        linarith only [h_swingC_id, h_lhs_nonneg, h_term2]
      have h0 := nonneg_of_mul_nonneg_right h_prod (by positivity)
      linarith only [h0]
    have h_bal_id : cherryF0Tilde (x : ℚ) (y : ℚ) β γ -
        S1 * ((5 * (t_H : ℚ) + 8 * (S : ℚ) + (R_B : ℚ) + (R_C : ℚ) + 10 + ((0 : ℕ) : ℚ)) -
              q * (5 * (S : ℚ) + (N_B : ℚ) + (N_C : ℚ) + 6 + ((0 : ℕ) : ℚ))) =
        (5 * (S : ℚ) + (N_B : ℚ) + (N_C : ℚ) + 6) * (S1 * q - Q0) +
        S1 * (β * (N_B : ℚ) - (R_B : ℚ)) + S1 * (γ * (N_C : ℚ) - (R_C : ℚ)) +
        ((N_B : ℚ) - cherryB0 (x : ℚ) β) * (Q0 - S1 * β) +
        ((N_C : ℚ) - cherryB0 (y : ℚ) γ) * (Q0 - S1 * γ) := by
      unfold cherryF0Tilde; dsimp [Q0, S1]; rw [htHQ, hSQ]; push_cast; ring
    have hQ0_β : 0 ≤ Q0 - S1 * β := by
      have h_id : Q0 - S1 * β = 7 / 3 * S1 + (y : ℚ) * (((x : ℚ) + 1) / 2 - β) +
          (y : ℚ) * ((x : ℚ) + 1) * (γ - 1 / 2) := by dsimp [Q0, S1]; ring
      rw [h_id]
      have : 0 ≤ ((x : ℚ) + 1) / 2 - β := by linarith only [hβ_le]
      have : 0 ≤ γ - 1 / 2 := by linarith only [hγ_ge1]
      positivity
    have hQ0_γ : 0 ≤ Q0 - S1 * γ := by
      have h_id : Q0 - S1 * γ = 7 / 3 * S1 + (x : ℚ) * (((y : ℚ) + 1) / 2 - γ) +
          (x : ℚ) * ((y : ℚ) + 1) * (β - 1 / 2) := by dsimp [Q0, S1]; ring
      rw [h_id]
      have : 0 ≤ ((y : ℚ) + 1) / 2 - γ := by linarith only [hγ_le]
      have : 0 ≤ β - 1 / 2 := by linarith only [hβ_ge1]
      positivity
    have hF0_nonneg : 0 ≤ cherryF0Tilde (x : ℚ) (y : ℚ) β γ := by
      have h_bal0 : S1 * ((5 * (t_H : ℚ) + 8 * (S : ℚ) + (R_B : ℚ) + (R_C : ℚ) + 10 + ((0 : ℕ) : ℚ)) -
          q * (5 * (S : ℚ) + (N_B : ℚ) + (N_C : ℚ) + 6 + ((0 : ℕ) : ℚ))) = 0 := by
        have : (5 * (t_H : ℚ) + 8 * (S : ℚ) + (R_B : ℚ) + (R_C : ℚ) + 10 + ((0 : ℕ) : ℚ)) -
            q * (5 * (S : ℚ) + (N_B : ℚ) + (N_C : ℚ) + 6 + ((0 : ℕ) : ℚ)) = 0 := by linarith only [h_bal]
        rw [this, mul_zero]
      have h1 : 0 ≤ (5 * (S : ℚ) + (N_B : ℚ) + (N_C : ℚ) + 6) * (S1 * q - Q0) :=
        mul_nonneg (by positivity) (by linarith only [h_Sq_ge])
      have h2 : 0 ≤ S1 * (β * (N_B : ℚ) - (R_B : ℚ)) :=
        mul_nonneg (le_of_lt hS1_pos) (by linarith only [hRB_le])
      have h3 : 0 ≤ S1 * (γ * (N_C : ℚ) - (R_C : ℚ)) :=
        mul_nonneg (le_of_lt hS1_pos) (by linarith only [hRC_le])
      have h4 : 0 ≤ ((N_B : ℚ) - cherryB0 (x : ℚ) β) * (Q0 - S1 * β) :=
        mul_nonneg (by linarith only [hNB_le]) hQ0_β
      have h5 : 0 ≤ ((N_C : ℚ) - cherryB0 (y : ℚ) γ) * (Q0 - S1 * γ) :=
        mul_nonneg (by linarith only [hNC_le]) hQ0_γ
      linarith only [h_bal_id, h_bal0, h1, h2, h3, h4, h5]
    have hF0_neg : cherryF0Tilde (x : ℚ) (y : ℚ) β γ < 0 := by
      have bq_horiz {Cuu Cuv Cvv Lu Lv C0 u1 u2 u v : ℚ}
          (hCuu : 0 ≤ Cuu) (hu1 : u1 ≤ u) (hu2 : u ≤ u2)
          (h1 : cherryBivarQuad Cuu Cuv Cvv Lu Lv C0 u1 v < 0)
          (h2 : cherryBivarQuad Cuu Cuv Cvv Lu Lv C0 u2 v < 0) :
          cherryBivarQuad Cuu Cuv Cvv Lu Lv C0 u v < 0 := by
        rcases eq_or_lt_of_le hu1 with rfl | hu1_lt
        · exact h1
        · have hu21 : 0 < u2 - u1 := by linarith only [hu1_lt, hu2]
          have h_id : (u2 - u1) * (-cherryBivarQuad Cuu Cuv Cvv Lu Lv C0 u v) =
              (u2 - u) * (-cherryBivarQuad Cuu Cuv Cvv Lu Lv C0 u1 v) +
              (u - u1) * (-cherryBivarQuad Cuu Cuv Cvv Lu Lv C0 u2 v) +
              Cuu * (u2 - u1) * (u - u1) * (u2 - u) := by
            unfold cherryBivarQuad; ring
          have ht1 : 0 ≤ (u2 - u) * (-cherryBivarQuad Cuu Cuv Cvv Lu Lv C0 u1 v) :=
            mul_nonneg (by linarith only [hu2]) (by linarith only [h1])
          have ht2 : 0 < (u - u1) * (-cherryBivarQuad Cuu Cuv Cvv Lu Lv C0 u2 v) :=
            mul_pos (by linarith only [hu1_lt]) (by linarith only [h2])
          have ht3 : 0 ≤ Cuu * (u2 - u1) * (u - u1) * (u2 - u) := by
            have : 0 ≤ u - u1 := by linarith only [hu1_lt]
            have : 0 ≤ u2 - u := by linarith only [hu2]
            positivity
          have h_prod : 0 < (u2 - u1) * (-cherryBivarQuad Cuu Cuv Cvv Lu Lv C0 u v) := by
            linarith only [h_id, ht1, ht2, ht3]
          have h0 := pos_of_mul_pos_right h_prod (le_of_lt hu21)
          linarith only [h0]
      have bq_affine {Cuu Cuv Cvv Lu Lv C0 u0 m v1 v2 v : ℚ}
          (hCuu : 0 ≤ Cuu) (hCuv : 0 ≤ Cuv) (hCvv : 0 ≤ Cvv) (hm : 0 ≤ m)
          (hv1 : v1 ≤ v) (hv2 : v ≤ v2)
          (h1 : cherryBivarQuad Cuu Cuv Cvv Lu Lv C0 (u0 - m * v1) v1 < 0)
          (h2 : cherryBivarQuad Cuu Cuv Cvv Lu Lv C0 (u0 - m * v2) v2 < 0) :
          cherryBivarQuad Cuu Cuv Cvv Lu Lv C0 (u0 - m * v) v < 0 := by
        rcases eq_or_lt_of_le hv1 with rfl | hv1_lt
        · exact h1
        · have hv21 : 0 < v2 - v1 := by linarith only [hv1_lt, hv2]
          have h_id : (v2 - v1) * (-cherryBivarQuad Cuu Cuv Cvv Lu Lv C0 (u0 - m * v) v) =
              (v2 - v) * (-cherryBivarQuad Cuu Cuv Cvv Lu Lv C0 (u0 - m * v1) v1) +
              (v - v1) * (-cherryBivarQuad Cuu Cuv Cvv Lu Lv C0 (u0 - m * v2) v2) +
              (Cuu * m ^ 2 + Cuv * m + Cvv) * (v2 - v1) * (v - v1) * (v2 - v) := by
            unfold cherryBivarQuad; ring
          have ht1 : 0 ≤ (v2 - v) * (-cherryBivarQuad Cuu Cuv Cvv Lu Lv C0 (u0 - m * v1) v1) :=
            mul_nonneg (by linarith only [hv2]) (by linarith only [h1])
          have ht2 : 0 < (v - v1) * (-cherryBivarQuad Cuu Cuv Cvv Lu Lv C0 (u0 - m * v2) v2) :=
            mul_pos (by linarith only [hv1_lt]) (by linarith only [h2])
          have ht3 : 0 ≤ (Cuu * m ^ 2 + Cuv * m + Cvv) * (v2 - v1) * (v - v1) * (v2 - v) := by
            have : 0 ≤ v - v1 := by linarith only [hv1_lt]
            have : 0 ≤ v2 - v := by linarith only [hv2]
            positivity
          have h_prod : 0 < (v2 - v1) * (-cherryBivarQuad Cuu Cuv Cvv Lu Lv C0 (u0 - m * v) v) := by
            linarith only [h_id, ht1, ht2, ht3]
          have h0 := pos_of_mul_pos_right h_prod (le_of_lt hv21)
          linarith only [h0]
      have h_vert_J : ∀ (a b : ℚ), 4 ≤ a → 4 ≤ b →
          cherryF0Tilde a b ((a + 1) / 2) ((5 * a * b + 17 * a + 5 * b + 9) / (6 * (4 * a + 3))) < 0 := by
        intro a b ha hb
        set Xa := a - 4
        set Yb := b - 4
        have hXa : 0 ≤ Xa := by linarith only [ha]
        have hYb : 0 ≤ Yb := by linarith only [hb]
        have ha_pos : 0 < a := by linarith only [ha]
        have hb_pos : 0 < b := by linarith only [hb]
        let gJa := (5 * a * b + 17 * a + 5 * b + 9) / (6 * (4 * a + 3))
        have hgJa : (4 * a + 3) * gJa = (5 * a * b + 17 * a + 5 * b + 9) / 6 := by
          dsimp [gJa]
          have hne : 6 * (4 * a + 3) ≠ 0 := by positivity
          calc (4 * a + 3) * ((5 * a * b + 17 * a + 5 * b + 9) / (6 * (4 * a + 3)))
            _ = (6 * (4 * a + 3)) * ((5 * a * b + 17 * a + 5 * b + 9) / (6 * (4 * a + 3))) / 6 := by ring
            _ = (5 * a * b + 17 * a + 5 * b + 9) / 6 := by rw [mul_div_cancel₀ _ hne]
        let S1a := a * b + a + b
        let PJa := 458 * (Xa - Yb) ^ 2 + 20 * Xa ^ 4 * Yb + 304 * Xa ^ 4 + 6 * Xa ^ 3 * Yb ^ 2 +
          149 * Xa ^ 3 * Yb + 5288 * Xa ^ 3 + 114 * Xa ^ 2 * Yb ^ 2 + 33 * Xa ^ 2 * Yb +
          37296 * Xa ^ 2 + 705 * Xa * Yb ^ 2 + 131700 * Xa + 964 * Yb ^ 2 + 705 * Yb + 185730
        have h_id : (4 * a + 3) ^ 2 * (-cherryF0Tilde a b ((a + 1) / 2) gJa) = S1a * (PJa / 12) := by
          calc (4 * a + 3) ^ 2 * (-cherryF0Tilde a b ((a + 1) / 2) gJa)
            _ = - (S1a * (4 / 3 * ((1 + a) * (1 + b)) - 4) * (4 * a + 3) ^ 2
                  - 11 * (a * (b + 1) * ((a + 1) / 2) * (4 * a + 3) ^ 2 + b * (a + 1) * (4 * a + 3) * ((4 * a + 3) * gJa))
                  - cherryB0 a ((a + 1) / 2) * (4 * a + 3) * (7 / 3 * S1a * (4 * a + 3) + a * (b + 1) * ((a + 1) / 2) * (4 * a + 3) + b * (a + 1) * ((4 * a + 3) * gJa) - S1a * ((a + 1) / 2) * (4 * a + 3))
                  - ((3 / 2 * b + 1) * ((4 * a + 3) * gJa) - b * (b + 5) / 4 * (4 * a + 3)) * (7 / 3 * S1a * (4 * a + 3) + a * (b + 1) * ((a + 1) / 2) * (4 * a + 3) + b * (a + 1) * ((4 * a + 3) * gJa) - S1a * ((4 * a + 3) * gJa))) := by
              unfold cherryF0Tilde cherryB0; ring
            _ = S1a * (PJa / 12) := by
              rw [hgJa]; unfold cherryB0; dsimp [S1a, PJa, Xa, Yb]; ring
        have hS1a : 0 < S1a := by dsimp [S1a]; positivity
        have hPJa : 0 < PJa := by dsimp [PJa]; positivity
        have h_prod_pos : 0 < (4 * a + 3) ^ 2 * (-cherryF0Tilde a b ((a + 1) / 2) gJa) := by
          rw [h_id]; positivity
        have h4a3_sq : 0 < (4 * a + 3) ^ 2 := by positivity
        have h0 := pos_of_mul_pos_right h_prod_pos (le_of_lt h4a3_sq)
        linarith only [h0]
      set X := (x : ℚ) - 4
      set Y := (y : ℚ) - 4
      have hX : 0 ≤ X := by linarith only [hxQ]
      have hY : 0 ≤ Y := by linarith only [hyQ]
      let SQ := (1 + (x : ℚ)) * (1 + (y : ℚ))
      let Cuu := (3 * (x : ℚ) + 2) / 2 * (y : ℚ)
      let Cvv := (3 * (y : ℚ) + 2) / 2 * (x : ℚ)
      let Cuv := (3 * (x : ℚ) + 2) / 2 * (y : ℚ) * ((x : ℚ) + 1) + (3 * (y : ℚ) + 2) / 2 * (x : ℚ) * ((y : ℚ) + 1)
      let Lu := -11 * (x : ℚ) * ((y : ℚ) + 1) - 7 * (3 * (x : ℚ) + 2) / 6 * S1 - (x : ℚ) * ((x : ℚ) + 5) / 4 * (y : ℚ) + (y : ℚ) * ((y : ℚ) + 5) / 4 * (x : ℚ) * ((y : ℚ) + 1)
      let Lv := -11 * (y : ℚ) * ((x : ℚ) + 1) - 7 * (3 * (y : ℚ) + 2) / 6 * S1 - (y : ℚ) * ((y : ℚ) + 5) / 4 * (x : ℚ) + (x : ℚ) * ((x : ℚ) + 5) / 4 * (y : ℚ) * ((x : ℚ) + 1)
      let C0 := S1 * (4 / 3 * SQ - 4 + 7 * ((x : ℚ) * ((x : ℚ) + 5) + (y : ℚ) * ((y : ℚ) + 5)) / 12)
      have h_bq (u v : ℚ) : cherryF0Tilde (x : ℚ) (y : ℚ) u v = cherryBivarQuad Cuu Cuv Cvv Lu Lv C0 u v := by
        unfold cherryF0Tilde cherryB0 cherryBivarQuad
        dsimp [Cuu, Cvv, Cuv, Lu, Lv, C0, SQ, S1]
        ring
      have hCuu : 0 ≤ Cuu := by dsimp [Cuu]; positivity
      have hCvv : 0 ≤ Cvv := by dsimp [Cvv]; positivity
      have hCuv : 0 ≤ Cuv := by dsimp [Cuv]; positivity
      let bI := 4 * ((x : ℚ) + 2) / 15
      let gI := 4 * ((y : ℚ) + 2) / 15
      let bK := ((x : ℚ) + 1) / 2
      let gK := ((y : ℚ) + 1) / 2
      let gJ := (5 * (x : ℚ) * (y : ℚ) + 17 * (x : ℚ) + 5 * (y : ℚ) + 9) / (6 * (4 * (x : ℚ) + 3))
      let bJtop := (5 * (y : ℚ) * (x : ℚ) + 17 * (y : ℚ) + 5 * (x : ℚ) + 9) / (6 * (4 * (y : ℚ) + 3))
      have h_I : cherryBivarQuad Cuu Cuv Cvv Lu Lv C0 bI gI < 0 := by
        rw [← h_bq]
        let PI := 356 * (X - Y) ^ 2 + 36 * X ^ 2 * Y + 103 * X ^ 2 + 36 * X * Y ^ 2 +
          279 * X + 103 * Y ^ 2 + 279 * Y + 13464
        have h_id : -cherryF0Tilde (x : ℚ) (y : ℚ) bI gI = S1 * (PI / 900) := by
          unfold cherryF0Tilde cherryB0; dsimp [bI, gI, S1, PI, X, Y]; ring
        have hPI : 0 < PI := by dsimp [PI]; positivity
        have h0 : 0 < -cherryF0Tilde (x : ℚ) (y : ℚ) bI gI := by rw [h_id]; positivity
        linarith only [h0]
      have h_K : cherryBivarQuad Cuu Cuv Cvv Lu Lv C0 bK gK < 0 := by
        rw [← h_bq]
        let PK := 3 * X ^ 3 * Y ^ 2 + 38 * X ^ 3 * Y + 118 * X ^ 3 + 3 * X ^ 2 * Y ^ 3 +
          62 * X ^ 2 * Y ^ 2 + 571 * X ^ 2 * Y + 1705 * X ^ 2 + 38 * X * Y ^ 3 +
          571 * X * Y ^ 2 + 3984 * X * Y + 10454 * X + 118 * Y ^ 3 + 1705 * Y ^ 2 +
          10454 * Y + 24336
        have h_id : -cherryF0Tilde (x : ℚ) (y : ℚ) bK gK = PK / 12 := by
          unfold cherryF0Tilde cherryB0; dsimp [bK, gK, PK, X, Y]; ring
        have hPK : 0 < PK := by dsimp [PK]; positivity
        have h0 : 0 < -cherryF0Tilde (x : ℚ) (y : ℚ) bK gK := by rw [h_id]; positivity
        linarith only [h0]
      have h_J : cherryBivarQuad Cuu Cuv Cvv Lu Lv C0 bK gJ < 0 := by
        rw [← h_bq]; exact h_vert_J (x : ℚ) (y : ℚ) hxQ hyQ
      have h_Jtop : cherryBivarQuad Cuu Cuv Cvv Lu Lv C0 bJtop gK < 0 := by
        rw [← h_bq]
        have h_symm : cherryF0Tilde (x : ℚ) (y : ℚ) bJtop gK = cherryF0Tilde (y : ℚ) (x : ℚ) gK bJtop := by
          unfold cherryF0Tilde cherryB0; ring
        rw [h_symm]; exact h_vert_J (y : ℚ) (x : ℚ) hyQ hxQ
      let u0B := (4 / 3 * S1) / ((y : ℚ) - 3)
      let mB := (4 * (x : ℚ) + 3) / ((y : ℚ) - 3)
      let u0C := (4 / 3 * S1) / (4 * (y : ℚ) + 3)
      let mC := ((x : ℚ) - 3) / (4 * (y : ℚ) + 3)
      have hx3 : 0 ≤ (x : ℚ) - 3 := by linarith only [hxQ]
      have hy3 : 0 < (y : ℚ) - 3 := by linarith only [hyQ]
      have h4x3 : 0 < 4 * (x : ℚ) + 3 := by linarith only [hxQ]
      have h4y3 : 0 < 4 * (y : ℚ) + 3 := by linarith only [hyQ]
      have hmB : 0 ≤ mB := by dsimp [mB]; positivity
      have hmC : 0 ≤ mC := by dsimp [mC]; positivity
      have h_bB_le : u0B - mB * γ ≤ β := by
        have h_id : ((y : ℚ) - 3) * (β - (u0B - mB * γ)) =
            ((y : ℚ) - 3) * β + (4 * (x : ℚ) + 3) * γ - 4 / 3 * S1 := by
          dsimp [u0B, mB]
          have hne : (y : ℚ) - 3 ≠ 0 := ne_of_gt hy3
          calc ((y : ℚ) - 3) * (β - (4 / 3 * S1 / ((y : ℚ) - 3) - (4 * (x : ℚ) + 3) / ((y : ℚ) - 3) * γ))
            _ = ((y : ℚ) - 3) * β - ((y : ℚ) - 3) * (4 / 3 * S1 / ((y : ℚ) - 3)) + ((y : ℚ) - 3) * ((4 * (x : ℚ) + 3) / ((y : ℚ) - 3)) * γ := by ring
            _ = ((y : ℚ) - 3) * β - 4 / 3 * S1 + (4 * (x : ℚ) + 3) * γ := by
              rw [mul_div_cancel₀ _ hne, mul_div_cancel₀ _ hne]
            _ = ((y : ℚ) - 3) * β + (4 * (x : ℚ) + 3) * γ - 4 / 3 * S1 := by ring
        have h_prod : 0 ≤ ((y : ℚ) - 3) * (β - (u0B - mB * γ)) := by linarith only [h_id, hLB]
        have h0 := nonneg_of_mul_nonneg_right h_prod hy3
        linarith only [h0]
      have h_bC_le : u0C - mC * γ ≤ β := by
        have h_id : (4 * (y : ℚ) + 3) * (β - (u0C - mC * γ)) =
            (4 * (y : ℚ) + 3) * β + ((x : ℚ) - 3) * γ - 4 / 3 * S1 := by
          dsimp [u0C, mC]
          have hne : 4 * (y : ℚ) + 3 ≠ 0 := ne_of_gt h4y3
          calc (4 * (y : ℚ) + 3) * (β - (4 / 3 * S1 / (4 * (y : ℚ) + 3) - ((x : ℚ) - 3) / (4 * (y : ℚ) + 3) * γ))
            _ = (4 * (y : ℚ) + 3) * β - (4 * (y : ℚ) + 3) * (4 / 3 * S1 / (4 * (y : ℚ) + 3)) + (4 * (y : ℚ) + 3) * (((x : ℚ) - 3) / (4 * (y : ℚ) + 3)) * γ := by ring
            _ = (4 * (y : ℚ) + 3) * β - 4 / 3 * S1 + ((x : ℚ) - 3) * γ := by
              rw [mul_div_cancel₀ _ hne, mul_div_cancel₀ _ hne]
            _ = (4 * (y : ℚ) + 3) * β + ((x : ℚ) - 3) * γ - 4 / 3 * S1 := by ring
        have h_prod : 0 ≤ (4 * (y : ℚ) + 3) * (β - (u0C - mC * γ)) := by linarith only [h_id, hLC]
        have h0 := nonneg_of_mul_nonneg_right h_prod h4y3
        linarith only [h0]
      have h_end_BJ : u0B - mB * gJ = bK := by
        dsimp [u0B, mB, gJ, bK, S1]
        have hne1 : (y : ℚ) - 3 ≠ 0 := ne_of_gt hy3
        have hne2 : 6 * (4 * (x : ℚ) + 3) ≠ 0 := by positivity
        field_simp; ring
      have h_end_BI : u0B - mB * gI = bI := by
        dsimp [u0B, mB, gI, bI, S1]
        have hne1 : (y : ℚ) - 3 ≠ 0 := ne_of_gt hy3
        field_simp; ring
      have h_end_CI : u0C - mC * gI = bI := by
        dsimp [u0C, mC, gI, bI, S1]
        have hne1 : 4 * (y : ℚ) + 3 ≠ 0 := ne_of_gt h4y3
        field_simp; ring
      have h_end_CK : u0C - mC * gK = bJtop := by
        dsimp [u0C, mC, gK, bJtop, S1]
        have hne1 : 4 * (y : ℚ) + 3 ≠ 0 := ne_of_gt h4y3
        field_simp; ring
      have hgJ_le : gJ ≤ γ := by
        have hβ' : β ≤ bK := hβ_le
        have h2 : 0 ≤ mB * (γ - gJ) := by linarith only [h_bB_le, hβ', h_end_BJ]
        have hmB_pos : 0 < mB := by dsimp [mB]; positivity
        have h0 := nonneg_of_mul_nonneg_right h2 hmB_pos
        linarith only [h0]
      have h_right_edge : cherryBivarQuad Cuu Cuv Cvv Lu Lv C0 bK γ < 0 := by
        have h_zero (v : ℚ) : bK = bK - 0 * v := by ring
        rw [h_zero γ]
        apply bq_affine hCuu hCuv hCvv (le_refl 0) hgJ_le hγ_le
        · rw [← h_zero gJ]; exact h_J
        · rw [← h_zero gK]; exact h_K
      rw [h_bq]
      rcases le_total γ gI with hγ_le_I | hI_le_γ
      · have h_left_B : cherryBivarQuad Cuu Cuv Cvv Lu Lv C0 (u0B - mB * γ) γ < 0 := by
          apply bq_affine hCuu hCuv hCvv hmB hgJ_le hγ_le_I
          · rw [h_end_BJ]; exact h_J
          · rw [h_end_BI]; exact h_I
        exact bq_horiz hCuu h_bB_le hβ_le h_left_B h_right_edge
      · have h_left_C : cherryBivarQuad Cuu Cuv Cvv Lu Lv C0 (u0C - mC * γ) γ < 0 := by
          apply bq_affine hCuu hCuv hCvv hmC hI_le_γ hγ_le
          · rw [h_end_CI]; exact h_I
          · rw [h_end_CK]; exact h_Jtop
        exact bq_horiz hCuu h_bC_le hβ_le h_left_C h_right_edge
    linarith only [hF0_nonneg, hF0_neg]
  · 
    let U : ℚ := (t_B : ℚ) / ((x : ℚ) * ((x : ℚ) + 1))
    let V : ℚ := (t_C : ℚ) / ((y : ℚ) * ((y : ℚ) + 1))
    have hxx_pos : 0 < (x : ℚ) * ((x : ℚ) + 1) := by positivity
    have hyy_pos : 0 < (y : ℚ) * ((y : ℚ) + 1) := by positivity
    have htB : (t_B : ℚ) = (x : ℚ) * ((x : ℚ) + 1) * U :=
      (mul_div_cancel₀ (t_B : ℚ) (ne_of_gt hxx_pos)).symm
    have htC : (t_C : ℚ) = (y : ℚ) * ((y : ℚ) + 1) * V :=
      (mul_div_cancel₀ (t_C : ℚ) (ne_of_gt hyy_pos)).symm
    have hU_nonneg : 0 ≤ U := by dsimp [U]; positivity
    have hV_nonneg : 0 ≤ V := by dsimp [V]; positivity
    have hU_le : U ≤ 1 / 2 := by
      have h_id : (x : ℚ) * ((x : ℚ) + 1) - 2 * (t_B : ℚ) =
          2 * ((x : ℚ) * ((x : ℚ) + 1)) * (1 / 2 - U) := by rw [htB]; ring
      have h_prod : 0 ≤ (2 * ((x : ℚ) * ((x : ℚ) + 1))) * (1 / 2 - U) := by linarith only [h2BQ, h_id]
      have h0 : 0 ≤ 1 / 2 - U := nonneg_of_mul_nonneg_right h_prod (by positivity)
      linarith only [h0]
    have hV_le : V ≤ 1 / 2 := by
      have h_id : (y : ℚ) * ((y : ℚ) + 1) - 2 * (t_C : ℚ) =
          2 * ((y : ℚ) * ((y : ℚ) + 1)) * (1 / 2 - V) := by rw [htC]; ring
      have h_prod : 0 ≤ (2 * ((y : ℚ) * ((y : ℚ) + 1))) * (1 / 2 - V) := by linarith only [h2CQ, h_id]
      have h0 : 0 ≤ 1 / 2 - V := nonneg_of_mul_nonneg_right h_prod (by positivity)
      linarith only [h0]
    have hRB_le : (R_B : ℚ) ≤ ((x : ℚ) + 1) * U * (N_B : ℚ) := by
      have h_id : (N_B : ℚ) * (t_B : ℚ) - (R_B : ℚ) * (x : ℚ) =
          (x : ℚ) * (((x : ℚ) + 1) * U * (N_B : ℚ) - (R_B : ℚ)) := by rw [htB]; ring
      have h_prod : 0 ≤ (x : ℚ) * (((x : ℚ) + 1) * U * (N_B : ℚ) - (R_B : ℚ)) := by linarith only [h3BQ, h_id]
      have h0 := nonneg_of_mul_nonneg_right h_prod hx_pos
      linarith only [h0]
    have hRC_le : (R_C : ℚ) ≤ ((y : ℚ) + 1) * V * (N_C : ℚ) := by
      have h_id : (N_C : ℚ) * (t_C : ℚ) - (R_C : ℚ) * (y : ℚ) =
          (y : ℚ) * (((y : ℚ) + 1) * V * (N_C : ℚ) - (R_C : ℚ)) := by rw [htC]; ring
      have h_prod : 0 ≤ (y : ℚ) * (((y : ℚ) + 1) * V * (N_C : ℚ) - (R_C : ℚ)) := by linarith only [h3CQ, h_id]
      have h0 := nonneg_of_mul_nonneg_right h_prod hy_pos
      linarith only [h0]
    have hNB_le : cherryB (x : ℚ) U ≤ (N_B : ℚ) := by
      have h_id : 4 * (x : ℚ) * (N_B : ℚ) + (x : ℚ) ^ 2 * ((x : ℚ) + 5) - (6 * (x : ℚ) + 4) * (t_B : ℚ) =
          (4 * (x : ℚ)) * ((N_B : ℚ) - cherryB (x : ℚ) U) := by unfold cherryB; rw [htB]; ring
      have h_prod : 0 ≤ (4 * (x : ℚ)) * ((N_B : ℚ) - cherryB (x : ℚ) U) := by linarith only [h4BQ, h_id]
      have h0 := nonneg_of_mul_nonneg_right h_prod (by positivity)
      linarith only [h0]
    have hNC_le : cherryB (y : ℚ) V ≤ (N_C : ℚ) := by
      have h_id : 4 * (y : ℚ) * (N_C : ℚ) + (y : ℚ) ^ 2 * ((y : ℚ) + 5) - (6 * (y : ℚ) + 4) * (t_C : ℚ) =
          (4 * (y : ℚ)) * ((N_C : ℚ) - cherryB (y : ℚ) V) := by unfold cherryB; rw [htC]; ring
      have h_prod : 0 ≤ (4 * (y : ℚ)) * ((N_C : ℚ) - cherryB (y : ℚ) V) := by linarith only [h4CQ, h_id]
      have h0 := nonneg_of_mul_nonneg_right h_prod (by positivity)
      linarith only [h0]
    have hSQ : (S : ℚ) = 2 * (1 + (x : ℚ)) * (1 + (y : ℚ)) := by
      dsimp [S, p]; push_cast; ring
    have htHQ : (t_H : ℚ) = 3 * (1 + (x : ℚ)) * (1 + (y : ℚ)) +
        2 * (1 + (y : ℚ)) * ((x : ℚ) * ((x : ℚ) + 1) * U) +
        2 * (1 + (x : ℚ)) * ((y : ℚ) * ((y : ℚ) + 1) * V) := by
      dsimp [t_H, p]; push_cast; rw [htB, htC]
    have haBQ : (a_B : ℚ) = 2 * (1 + (y : ℚ)) := by dsimp [a_B, p]; push_cast; ring
    have htABQ : (t_AB : ℚ) = 3 * (1 + (y : ℚ)) + 2 * ((y : ℚ) * ((y : ℚ) + 1) * V) := by
      dsimp [t_AB, p]; push_cast; rw [htC]
    have haCQ : (a_C : ℚ) = 2 * (1 + (x : ℚ)) := by dsimp [a_C, p]; push_cast; ring
    have htACQ : (t_AC : ℚ) = 3 * (1 + (x : ℚ)) + 2 * ((x : ℚ) * ((x : ℚ) + 1) * U) := by
      dsimp [t_AC, p]; push_cast; rw [htB]
    let q_hat : ℚ := 17 / 6 + (x : ℚ) * U + (y : ℚ) * V
    have h_fold_id : (3 * (t_H : ℚ) + 4 * (S : ℚ) - 7) - 3 * ((S : ℚ) - 1) * q_hat =
        3 * ((x : ℚ) * U + (y : ℚ) * V) + 3 / 2 := by
      dsimp [q_hat]; rw [htHQ, hSQ]; ring
    have h_fold_pos : 0 < (3 * (t_H : ℚ) + 4 * (S : ℚ) - 7) - 3 * ((S : ℚ) - 1) * q_hat := by
      rw [h_fold_id]; positivity
    have hS1_pos : 0 < 3 * ((S : ℚ) - 1) := by
      have : (S : ℚ) - 1 = 2 * (x : ℚ) * (y : ℚ) + 2 * (x : ℚ) + 2 * (y : ℚ) + 1 := by rw [hSQ]; ring
      rw [this]; positivity
    have hq_ge : q_hat ≤ q := by
      have h_prod : 0 ≤ (3 * ((S : ℚ) - 1)) * (q - q_hat) := by linarith only [h_fold, h_fold_pos]
      have h0 := nonneg_of_mul_nonneg_right h_prod hS1_pos
      linarith only [h0]
    have h_swingC_id : (y : ℚ) * (8 - (t_AC : ℚ)) - ((a_C : ℚ) - 4) * (t_C : ℚ) - q * (y : ℚ) * (4 - (a_C : ℚ)) =
        (y : ℚ) * (4 * (x : ℚ) * (5 / 12 - U) + 1 / 3 + (2 * (x : ℚ) - 2) * (1 / 2 - V) +
        (2 * (x : ℚ) - 2) * (q - q_hat)) := by
      dsimp [q_hat]; rw [htACQ, haCQ, htC]; ring
    have hU_ge : 5 / 12 ≤ U := by
      have h2x2 : 0 ≤ 2 * (x : ℚ) - 2 := by linarith only [hxQ]
      have h1 : 0 ≤ (2 * (x : ℚ) - 2) * (1 / 2 - V) := mul_nonneg h2x2 (by linarith only [hV_le])
      have h2 : 0 ≤ (2 * (x : ℚ) - 2) * (q - q_hat) := mul_nonneg h2x2 (by linarith only [hq_ge])
      have h3 : 0 ≤ (y : ℚ) * (-(4 * (x : ℚ) * (5 / 12 - U) + 1 / 3 + (2 * (x : ℚ) - 2) * (1 / 2 - V) +
          (2 * (x : ℚ) - 2) * (q - q_hat))) := by linarith only [h_swingC, h_swingC_id]
      have h4 := nonneg_of_mul_nonneg_right h3 hy_pos
      have h5 : 0 ≤ (4 * (x : ℚ)) * (U - 5 / 12) := by linarith only [h1, h2, h4]
      have h6 := nonneg_of_mul_nonneg_right h5 (by positivity)
      linarith only [h6]
    have h_swingB_id : (x : ℚ) * (8 - (t_AB : ℚ)) - ((a_B : ℚ) - 4) * (t_B : ℚ) - q * (x : ℚ) * (4 - (a_B : ℚ)) =
        (x : ℚ) * (4 * (y : ℚ) * (5 / 12 - V) + 1 / 3 + (2 * (y : ℚ) - 2) * (1 / 2 - U) +
        (2 * (y : ℚ) - 2) * (q - q_hat)) := by
      dsimp [q_hat]; rw [htABQ, haBQ, htB]; ring
    have hV_ge : 5 / 12 ≤ V := by
      have h2y2 : 0 ≤ 2 * (y : ℚ) - 2 := by linarith only [hyQ]
      have h1 : 0 ≤ (2 * (y : ℚ) - 2) * (1 / 2 - U) := mul_nonneg h2y2 (by linarith only [hU_le])
      have h2 : 0 ≤ (2 * (y : ℚ) - 2) * (q - q_hat) := mul_nonneg h2y2 (by linarith only [hq_ge])
      have h3 : 0 ≤ (x : ℚ) * (-(4 * (y : ℚ) * (5 / 12 - V) + 1 / 3 + (2 * (y : ℚ) - 2) * (1 / 2 - U) +
          (2 * (y : ℚ) - 2) * (q - q_hat))) := by linarith only [h_swingB, h_swingB_id]
      have h4 := nonneg_of_mul_nonneg_right h3 hx_pos
      have h5 : 0 ≤ (4 * (y : ℚ)) * (V - 5 / 12) := by linarith only [h1, h2, h4]
      have h6 := nonneg_of_mul_nonneg_right h5 (by positivity)
      linarith only [h6]
    have h_bal_id : cherryF1Hat (x : ℚ) (y : ℚ) U V -
        ((5 * (t_H : ℚ) + 8 * (S : ℚ) + (R_B : ℚ) + (R_C : ℚ) + 10 + ((1 : ℕ) : ℚ)) -
         q * (5 * (S : ℚ) + (N_B : ℚ) + (N_C : ℚ) + 6 + ((1 : ℕ) : ℚ))) =
        (5 * (S : ℚ) + (N_B : ℚ) + (N_C : ℚ) + 7) * (q - q_hat) +
        (((x : ℚ) + 1) * U * (N_B : ℚ) - (R_B : ℚ)) +
        (((y : ℚ) + 1) * V * (N_C : ℚ) - (R_C : ℚ)) +
        ((N_B : ℚ) - cherryB (x : ℚ) U) * (q_hat - ((x : ℚ) + 1) * U) +
        ((N_C : ℚ) - cherryB (y : ℚ) V) * (q_hat - ((y : ℚ) + 1) * V) := by
      unfold cherryF1Hat; dsimp [q_hat]; rw [htHQ, hSQ]; push_cast; ring
    have hq_U : 0 ≤ q_hat - ((x : ℚ) + 1) * U := by
      have h_id : q_hat - ((x : ℚ) + 1) * U = 17 / 6 - U + (y : ℚ) * V := by dsimp [q_hat]; ring
      have h0 : 0 ≤ (y : ℚ) * V := by positivity
      linarith only [h_id, hU_le, h0]
    have hq_V : 0 ≤ q_hat - ((y : ℚ) + 1) * V := by
      have h_id : q_hat - ((y : ℚ) + 1) * V = 17 / 6 - V + (x : ℚ) * U := by dsimp [q_hat]; ring
      have h0 : 0 ≤ (x : ℚ) * U := by positivity
      linarith only [h_id, hV_le, h0]
    have hF1_nonneg : 0 ≤ cherryF1Hat (x : ℚ) (y : ℚ) U V := by
      have h_bal1 : (5 * (t_H : ℚ) + 8 * (S : ℚ) + (R_B : ℚ) + (R_C : ℚ) + 10 + ((1 : ℕ) : ℚ)) -
          q * (5 * (S : ℚ) + (N_B : ℚ) + (N_C : ℚ) + 6 + ((1 : ℕ) : ℚ)) = 0 := by linarith only [h_bal]
      have h1 : 0 ≤ (5 * (S : ℚ) + (N_B : ℚ) + (N_C : ℚ) + 7) * (q - q_hat) :=
        mul_nonneg (by positivity) (by linarith only [hq_ge])
      have h2 : 0 ≤ ((N_B : ℚ) - cherryB (x : ℚ) U) * (q_hat - ((x : ℚ) + 1) * U) :=
        mul_nonneg (by linarith only [hNB_le]) hq_U
      have h3 : 0 ≤ ((N_C : ℚ) - cherryB (y : ℚ) V) * (q_hat - ((y : ℚ) + 1) * V) :=
        mul_nonneg (by linarith only [hNC_le]) hq_V
      linarith only [h_bal_id, h_bal1, h1, hRB_le, hRC_le, h2, h3]
    have hF1_neg : cherryF1Hat (x : ℚ) (y : ℚ) U V < 0 := by
      have quad_neg {A B C a b t : ℚ} (hA : 0 ≤ A) (hat : a ≤ t) (htb : t ≤ b)
          (ha : A * a ^ 2 + B * a + C < 0) (hb : A * b ^ 2 + B * b + C < 0) :
          A * t ^ 2 + B * t + C < 0 := by
        rcases eq_or_lt_of_le hat with rfl | hat_lt
        · exact ha
        · have hba : 0 < b - a := by linarith only [hat_lt, htb]
          have h_id : (b - a) * (-(A * t ^ 2 + B * t + C)) =
              (b - t) * (-(A * a ^ 2 + B * a + C)) + (t - a) * (-(A * b ^ 2 + B * b + C)) +
              A * (b - a) * (t - a) * (b - t) := by ring
          have ht1 : 0 ≤ (b - t) * (-(A * a ^ 2 + B * a + C)) :=
            mul_nonneg (by linarith only [htb]) (by linarith only [ha])
          have ht2 : 0 < (t - a) * (-(A * b ^ 2 + B * b + C)) :=
            mul_pos (by linarith only [hat_lt]) (by linarith only [hb])
          have ht3 : 0 ≤ A * (b - a) * (t - a) * (b - t) := by
            have : 0 ≤ t - a := by linarith only [hat_lt]
            have : 0 ≤ b - t := by linarith only [htb]
            positivity
          have h_prod : 0 < (b - a) * (-(A * t ^ 2 + B * t + C)) := by
            linarith only [h_id, ht1, ht2, ht3]
          have h0 := pos_of_mul_pos_right h_prod (le_of_lt hba)
          linarith only [h0]
      set X := (x : ℚ) - 4
      set Y := (y : ℚ) - 4
      have hX : 0 ≤ X := by linarith only [hxQ]
      have hY : 0 ≤ Y := by linarith only [hyQ]
      have h11 : cherryF1Hat (x : ℚ) (y : ℚ) (5 / 12) (5 / 12) < 0 := by
        have h_id : -cherryF1Hat (x : ℚ) (y : ℚ) (5 / 12) (5 / 12) =
            799 / 72 + 953 / 288 * (X + Y) + 49 / 288 * (X - Y) ^ 2 +
            49 / 36 * (X ^ 2 + Y ^ 2) + 5 / 32 * X * Y * (X + Y) := by
          unfold cherryF1Hat cherryB; ring
        have h_pos : 0 < 799 / 72 + 953 / 288 * (X + Y) + 49 / 288 * (X - Y) ^ 2 +
            49 / 36 * (X ^ 2 + Y ^ 2) + 5 / 32 * X * Y * (X + Y) := by positivity
        linarith only [h_id, h_pos]
      have h12 : cherryF1Hat (x : ℚ) (y : ℚ) (5 / 12) (1 / 2) < 0 := by
        have h_id : -cherryF1Hat (x : ℚ) (y : ℚ) (5 / 12) (1 / 2) =
            3815 / 144 + 1571 / 288 * X + 215 / 24 * Y + 53 / 32 * X ^ 2 +
            19 / 48 * X * Y + 2 * Y ^ 2 + 3 / 16 * X ^ 2 * Y + 5 / 24 * X * Y ^ 2 := by
          unfold cherryF1Hat cherryB; ring
        have h_pos : 0 < 3815 / 144 + 1571 / 288 * X + 215 / 24 * Y + 53 / 32 * X ^ 2 +
            19 / 48 * X * Y + 2 * Y ^ 2 + 3 / 16 * X ^ 2 * Y + 5 / 24 * X * Y ^ 2 := by positivity
        linarith only [h_id, h_pos]
      have h21 : cherryF1Hat (x : ℚ) (y : ℚ) (1 / 2) (5 / 12) < 0 := by
        have h_id : -cherryF1Hat (x : ℚ) (y : ℚ) (1 / 2) (5 / 12) =
            3815 / 144 + 1571 / 288 * Y + 215 / 24 * X + 53 / 32 * Y ^ 2 +
            19 / 48 * X * Y + 2 * X ^ 2 + 3 / 16 * Y ^ 2 * X + 5 / 24 * Y * X ^ 2 := by
          unfold cherryF1Hat cherryB; ring
        have h_pos : 0 < 3815 / 144 + 1571 / 288 * Y + 215 / 24 * X + 53 / 32 * Y ^ 2 +
            19 / 48 * X * Y + 2 * X ^ 2 + 3 / 16 * Y ^ 2 * X + 5 / 24 * Y * X ^ 2 := by positivity
        linarith only [h_id, h_pos]
      have h22 : cherryF1Hat (x : ℚ) (y : ℚ) (1 / 2) (1 / 2) < 0 := by
        have h_id : -cherryF1Hat (x : ℚ) (y : ℚ) (1 / 2) (1 / 2) =
            263 / 6 + 47 / 4 * (X + Y) + 13 / 6 * (X ^ 2 + Y ^ 2) +
            4 / 3 * X * Y + 1 / 4 * X * Y * (X + Y) := by
          unfold cherryF1Hat cherryB; ring
        have h_pos : 0 < 263 / 6 + 47 / 4 * (X + Y) + 13 / 6 * (X ^ 2 + Y ^ 2) +
            4 / 3 * X * Y + 1 / 4 * X * Y * (X + Y) := by positivity
        linarith only [h_id, h_pos]
      let Cuu := (3 * (x : ℚ) + 2) / 2 * ((x : ℚ) + 1)
      let Cvv := (3 * (y : ℚ) + 2) / 2 * ((y : ℚ) + 1)
      let Cuv := Cuu * (y : ℚ) + Cvv * (x : ℚ)
      let Lu := -7 * (x : ℚ) - Cuu * (17 / 6) - (x : ℚ) * ((x : ℚ) + 5) / 4 + (y : ℚ) * ((y : ℚ) + 5) / 4 * (x : ℚ)
      let Lv := -7 * (y : ℚ) - Cvv * (17 / 6) - (y : ℚ) * ((y : ℚ) + 5) / 4 + (x : ℚ) * ((x : ℚ) + 5) / 4 * (y : ℚ)
      let C0 := 8 / 3 * (1 + (x : ℚ)) * (1 + (y : ℚ)) + 17 * ((x : ℚ) * ((x : ℚ) + 5) + (y : ℚ) * ((y : ℚ) + 5)) / 24 - 53 / 6
      have h_bq (u v : ℚ) : cherryF1Hat (x : ℚ) (y : ℚ) u v =
          Cuu * u ^ 2 - Cuv * u * v + Cvv * v ^ 2 + Lu * u + Lv * v + C0 := by
        unfold cherryF1Hat cherryB; ring
      have hCuu : 0 ≤ Cuu := by dsimp [Cuu]; positivity
      have hCvv : 0 ≤ Cvv := by dsimp [Cvv]; positivity
      have h_left : cherryF1Hat (x : ℚ) (y : ℚ) (5 / 12) V < 0 := by
        have h_v (v : ℚ) : cherryF1Hat (x : ℚ) (y : ℚ) (5 / 12) v =
            Cvv * v ^ 2 + (Lv - Cuv * (5 / 12)) * v + (Cuu * (5 / 12) ^ 2 + Lu * (5 / 12) + C0) := by
          rw [h_bq]; ring
        rw [h_v] at h11 h12 ⊢
        exact quad_neg hCvv hV_ge hV_le h11 h12
      have h_right : cherryF1Hat (x : ℚ) (y : ℚ) (1 / 2) V < 0 := by
        have h_v (v : ℚ) : cherryF1Hat (x : ℚ) (y : ℚ) (1 / 2) v =
            Cvv * v ^ 2 + (Lv - Cuv * (1 / 2)) * v + (Cuu * (1 / 2) ^ 2 + Lu * (1 / 2) + C0) := by
          rw [h_bq]; ring
        rw [h_v] at h21 h22 ⊢
        exact quad_neg hCvv hV_ge hV_le h21 h22
      have h_u (u : ℚ) : cherryF1Hat (x : ℚ) (y : ℚ) u V =
          Cuu * u ^ 2 + (Lu - Cuv * V) * u + (Cvv * V ^ 2 + Lv * V + C0) := by
        rw [h_bq]; ring
      rw [h_u] at h_left h_right ⊢
      exact quad_neg hCuu hU_ge hU_le h_left h_right
    linarith only [hF1_nonneg, hF1_neg]

theorem cherry_branch_improves : ∀ (n : ℕ) (hn : 1 ≤ n) (T : SimpleGraph (Fin n)),
    T.IsTree → HasTerminalCherryBranch T →
    ∃ T' : SimpleGraph (Fin n), T'.IsTree ∧ meanSubtreeOrder T < meanSubtreeOrder T' :=
by
  intro n hn T hT hCherry
  rcases hCherry with ⟨w, u, ℓ₁, ℓ₂, H, h12, hu1, hu2, hH_eq, hH_sub,
    hBridge_u, hLeaf1, hLeaf2, hu_adj, hDisj⟩
  rcases hDisj with ⟨A, B, z, hHAB, hA, hB, hBridge_z, hIneqA⟩ |
    ⟨L_c, B, C, r_B, r_C, hw_Lc, hLc_card, hLc_pack, hDisj_wB, hDisj_wC, hDisj_BC,
      hH_union, hB_sub, hC_sub, hBridge_B, hBridge_C, hx4, hy4⟩
  · exact cherry_bridge_split_improves n hn T hT w u ℓ₁ ℓ₂ z H A B
      h12 hu1 hu2 hH_eq hH_sub hBridge_u hLeaf1 hLeaf2 hu_adj hHAB hA hB hBridge_z hIneqA
  · by_contra h_no_imp
    obtain ⟨h_bal, h_fold, h_swingB, h_swingC⟩ :=
      cherry_three_branch_nonimproving_bounds n hn T hT w u ℓ₁ ℓ₂ r_B r_C H L_c B C
        h12 hu1 hu2 hH_eq hH_sub hBridge_u hLeaf1 hLeaf2 hu_adj
        hw_Lc hLc_card hLc_pack hDisj_wB hDisj_wC hDisj_BC hH_union
        hB_sub hC_sub hBridge_B hBridge_C h_no_imp
    obtain ⟨_, h_x_le_tB, h_2tB, h_RB, h_B3_B⟩ :=
      subtree_unrooted_moment_bounds n T hT B r_B hB_sub hBridge_B.2.2.1
    obtain ⟨_, h_y_le_tC, h_2tC, h_RC, h_B3_C⟩ :=
      subtree_unrooted_moment_bounds n T hT C r_C hC_sub hBridge_C.2.2.1
    exact cherry_three_branch_algebraic_contradiction
      L_c.card (rootedCount T B r_B) (rootedCount T C r_C)
      (rootedOrderSum T B r_B) (rootedOrderSum T C r_C)
      (unrootedCount T B) (unrootedCount T C)
      (unrootedOrderSum T B) (unrootedOrderSum T C)
      (meanSubtreeOrder T)
      hLc_card hx4 hy4
      h_x_le_tB h_2tB h_RB h_B3_B
      h_y_le_tC h_2tC h_RC h_B3_C
      h_bal h_fold h_swingB h_swingC

theorem broom_rooted_moment_bounds : ∀ (n : ℕ) (T : SimpleGraph (Fin n))
    (U : Finset (Fin n)) (r : Fin n),
    T.IsTree → IsSubtree T U → r ∈ U →
    1 ≤ rootedCount T U r ∧
    rootedCount T U r ≤ rootedOrderSum T U r ∧
    2 * rootedOrderSum T U r ≤ rootedCount T U r * (rootedCount T U r + 1) ∧
    (5 ≤ rootedCount T U r → 5 * rootedCount T U r ≤ 2 * rootedOrderSum T U r) :=
by
  intro n T U₀ r₀ hT hU₀ hr₀
  classical
  have rooted_singleton_moments : ∀ (U : Finset (Fin n)) (w : Fin n),
      w ∈ U → U.card ≤ 1 →
      rootedCount T U w = 1 ∧
      rootedOrderSum T U w = 1 := by
    intro U w hw hle
    have hU_eq : U = {w} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      refine ⟨hw, fun x hx => Finset.card_le_one.mp hle x hx w hw⟩
    subst hU_eq
    have hw_sub : IsSubtree T {w} := by
      refine ⟨Finset.singleton_nonempty w, ?_⟩
      have : Nonempty ↑(({w} : Finset (Fin n)) : Set (Fin n)) := ⟨⟨w, by simp⟩⟩
      refine ⟨?_⟩
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      have ha' : a = w := by simpa using ha
      have hb' : b = w := by simpa using hb
      have hab : (⟨a, ha⟩ : ↑(({w} : Finset (Fin n)) : Set (Fin n))) = ⟨b, hb⟩ :=
        Subtype.ext (ha'.trans hb'.symm)
      rw [hab]
    have h_root_eq : rootedSubtreesIn T {w} w = {{w}} := by
      ext S
      simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h_ne, _⟩, h_sub, _⟩
        rcases Finset.subset_singleton_iff.mp h_sub with rfl | rfl
        · exact False.elim (Finset.not_nonempty_empty h_ne)
        · rfl
      · rintro rfl
        exact ⟨hw_sub, Finset.Subset.refl _, Finset.mem_singleton_self w⟩
    simp [rootedCount, rootedOrderSum, h_root_eq]
  have isBridgeJoin_symm : ∀ {A B : Finset (Fin n)} {w r_B : Fin n},
      IsBridgeJoin T A B w r_B → IsBridgeJoin T B A r_B w := by
    intro A B w r_B hJ
    rcases hJ with ⟨h_disj, hw, hr_B, hadj, h_bridge⟩
    refine ⟨h_disj.symm, hr_B, hw, T.symm hadj, ?_⟩
    intro u hu v hv huv
    exact (h_bridge v hv u hu (T.symm huv)).symm
  have exists_walk_of_isSubtree : ∀ {S : Finset (Fin n)},
      IsSubtree T S → ∀ {a b : Fin n}, a ∈ S → b ∈ S →
      ∃ q : T.Walk a b, ∀ z ∈ q.support, z ∈ S := by
    intro S hS a b ha hb
    obtain ⟨q₀⟩ := hS.2.preconnected ⟨a, ha⟩ ⟨b, hb⟩
    suffices ∀ {u v : ↑(S : Set (Fin n))} (q : (T.induce (S : Set (Fin n))).Walk u v),
        ∃ q' : T.Walk u.1 v.1, ∀ z ∈ q'.support, z ∈ S from this q₀
    intro u v q
    induction q with
    | @nil u =>
      refine ⟨SimpleGraph.Walk.nil, ?_⟩
      intro z hz
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      rw [hz]
      exact Finset.mem_coe.mp u.2
    | @cons u c v hadj q' ih =>
      obtain ⟨q₁, hq₁⟩ := ih
      refine ⟨SimpleGraph.Walk.cons hadj q₁, ?_⟩
      intro z hz
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz'
      · exact Finset.mem_coe.mp u.2
      · exact hq₁ z hz'
  have bridge_walk_mem_edges : ∀ {A B : Finset (Fin n)} {w r_B : Fin n},
      IsBridgeJoin T A B w r_B → ∀ {a b : Fin n} (q : T.Walk a b),
      (∀ z ∈ q.support, z ∈ A ∪ B) →
      ((a ∈ A ∧ b ∈ B) ∨ (a ∈ B ∧ b ∈ A)) →
      s(w, r_B) ∈ q.edges := by
    intro A B w r_B hJ a b q
    induction q with
    | nil =>
      intro _ h_ab
      rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact False.elim (Finset.disjoint_left.mp hJ.1 ha hb)
      · exact False.elim (Finset.disjoint_left.mp hJ.1 hb ha)
    | @cons a c b h_step q' ih =>
      intro h_supp h_ab
      have hc_mem : c ∈ A ∪ B := h_supp c (by
        simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.start_mem_support])
      have h_supp' : ∀ z ∈ q'.support, z ∈ A ∪ B := fun z hz =>
        h_supp z (by simp [SimpleGraph.Walk.support_cons, hz])
      rcases Finset.mem_union.mp hc_mem with hcA | hcB
      · rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ (ih h_supp' (Or.inl ⟨hcA, hb⟩))
        · obtain ⟨hcw, har⟩ := hJ.2.2.2.2 c hcA a ha (T.symm h_step)
          subst hcw har
          rw [SimpleGraph.Walk.edges_cons, Sym2.eq_swap]
          exact List.mem_cons_self
      · rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · obtain ⟨haw, hcr⟩ := hJ.2.2.2.2 a ha c hcB h_step
          subst haw hcr
          rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_self
        · rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ (ih h_supp' (Or.inr ⟨hcB, hb⟩))
  have bridge_path_support_left : ∀ {A B : Finset (Fin n)} {w r_B : Fin n},
      IsBridgeJoin T A B w r_B → ∀ {a b : Fin n} (p : T.Walk a b), p.IsPath →
      (∀ z ∈ p.support, z ∈ A ∪ B) → a ∈ A → b ∈ A →
      ∀ z ∈ p.support, z ∈ A := by
    intro A B w r_B hJ a b p hp h_supp ha hb z hz
    rcases Finset.mem_union.mp (h_supp z hz) with hzA | hzB
    · exact hzA
    · exfalso
      let p₁ := p.takeUntil z hz
      let p₂ := p.dropUntil z hz
      have hp₁_supp : ∀ x ∈ p₁.support, x ∈ A ∪ B :=
        fun x hx => h_supp x (p.support_takeUntil_subset hz hx)
      have hp₂_supp : ∀ x ∈ p₂.support, x ∈ A ∪ B :=
        fun x hx => h_supp x (p.support_dropUntil_subset hz hx)
      have he₁ : s(w, r_B) ∈ p₁.edges :=
        bridge_walk_mem_edges hJ p₁ hp₁_supp (Or.inl ⟨ha, hzB⟩)
      have he₂ : s(w, r_B) ∈ p₂.edges :=
        bridge_walk_mem_edges hJ p₂ hp₂_supp (Or.inr ⟨hzB, hb⟩)
      have h_nodup : p.edges.Nodup := hp.isTrail.edges_nodup
      have h_edges : p₁.edges ++ p₂.edges = p.edges := by
        rw [← SimpleGraph.Walk.edges_append, p.take_spec hz]
      rw [← h_edges, List.nodup_append] at h_nodup
      exact h_nodup.2.2 s(w, r_B) he₁ s(w, r_B) he₂ rfl
  have subtree_exists_root_bridge_split : ∀ (U : Finset (Fin n)) (w : Fin n),
      IsSubtree T U → w ∈ U → 2 ≤ U.card →
      ∃ (A B : Finset (Fin n)) (r_B : Fin n),
        U = A ∪ B ∧ IsSubtree T A ∧ IsSubtree T B ∧ IsBridgeJoin T A B w r_B := by
    intro U w hU hw hge2
    obtain ⟨u, hu, huw⟩ := Finset.exists_mem_ne (by omega : 1 < U.card) w
    obtain ⟨p₀⟩ := hU.2.preconnected ⟨w, hw⟩ ⟨u, hu⟩
    have h_adj_exists : ∃ r_B ∈ U, T.Adj w r_B := by
      cases p₀ with
      | nil => exact False.elim (huw rfl)
      | @cons _ r _ hadj _ => exact ⟨r.1, r.2, hadj⟩
    obtain ⟨r_B, hr_B_U, hadj_wr⟩ := h_adj_exists
    let T₀ := T \ SimpleGraph.fromEdgeSet {s(w, r_B)}
    have h_bridge_wr : T.IsBridge s(w, r_B) :=
      SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.IsAcyclic hadj_wr
    have h_not_reach : ¬ T₀.Reachable w r_B :=
      (SimpleGraph.isBridge_iff.mp h_bridge_wr).2
    let A := U.filter (fun v => T₀.Reachable w v)
    let B := U \ A
    have hA_sub : A ⊆ U := Finset.filter_subset _ U
    have hU_eq : U = A ∪ B := (Finset.union_sdiff_of_subset hA_sub).symm
    have h_disj : Disjoint A B := Finset.disjoint_sdiff
    have hw_A : w ∈ A := Finset.mem_filter.mpr ⟨hw, SimpleGraph.Reachable.refl w⟩
    have hr_B : r_B ∈ B := by
      rw [Finset.mem_sdiff]
      refine ⟨hr_B_U, ?_⟩
      rw [Finset.mem_filter]
      rintro ⟨_, h_reach⟩
      exact h_not_reach h_reach
    have hJ : IsBridgeJoin T A B w r_B := by
      refine ⟨h_disj, hw_A, hr_B, hadj_wr, ?_⟩
      intro a ha b hb hab
      by_cases h_edge : s(a, b) = s(w, r_B)
      · rw [Sym2.eq_iff] at h_edge
        rcases h_edge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨rfl, rfl⟩
        · exact False.elim (Finset.disjoint_left.mp h_disj ha hr_B)
      · exfalso
        have hab₀ : T₀.Adj a b := by
          dsimp [T₀]
          rw [SimpleGraph.sdiff_adj, SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff]
          exact ⟨hab, fun ⟨h_eq, _⟩ => h_edge h_eq⟩
        have ha_reach : T₀.Reachable w a := (Finset.mem_filter.mp ha).2
        have hb_reach : T₀.Reachable w b := ha_reach.trans hab₀.reachable
        have hb_A : b ∈ A := Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hb).1, hb_reach⟩
        exact (Finset.mem_sdiff.mp hb).2 hb_A
    have hA_subtree : IsSubtree T A := by
      refine ⟨⟨w, hw_A⟩, ?_⟩
      have : Nonempty ↑(A : Set (Fin n)) := ⟨⟨w, hw_A⟩⟩
      refine ⟨?_⟩
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      have hxU : x ∈ U := hA_sub hx
      have hyU : y ∈ U := hA_sub hy
      obtain ⟨q, hq_supp⟩ := exists_walk_of_isSubtree hU hxU hyU
      let p : T.Walk x y := (q.toPath : T.Walk x y)
      have hp_path : p.IsPath := q.toPath.2
      have hp_supp : ∀ z ∈ p.support, z ∈ A ∪ B := by
        intro z hz
        rw [← hU_eq]
        exact hq_supp z (q.support_toPath_subset hz)
      have hp_A : ∀ z ∈ p.support, z ∈ (A : Set (Fin n)) :=
        bridge_path_support_left hJ p hp_path hp_supp hx hy
      exact (p.induce (A : Set (Fin n)) hp_A).reachable
    have hB_subtree : IsSubtree T B := by
      refine ⟨⟨r_B, hr_B⟩, ?_⟩
      have : Nonempty ↑(B : Set (Fin n)) := ⟨⟨r_B, hr_B⟩⟩
      refine ⟨?_⟩
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      have hxU : x ∈ U := Finset.sdiff_subset hx
      have hyU : y ∈ U := Finset.sdiff_subset hy
      obtain ⟨q, hq_supp⟩ := exists_walk_of_isSubtree hU hxU hyU
      let p : T.Walk x y := (q.toPath : T.Walk x y)
      have hp_path : p.IsPath := q.toPath.2
      have hp_supp : ∀ z ∈ p.support, z ∈ B ∪ A := by
        intro z hz
        rw [Finset.union_comm, ← hU_eq]
        exact hq_supp z (q.support_toPath_subset hz)
      have hp_B : ∀ z ∈ p.support, z ∈ (B : Set (Fin n)) :=
        bridge_path_support_left (isBridgeJoin_symm hJ) p hp_path hp_supp hx hy
      exact (p.induce (B : Set (Fin n)) hp_B).reachable
    exact ⟨A, B, r_B, hU_eq, hA_subtree, hB_subtree, hJ⟩
  have bridge_crossing_left : ∀ {A B S : Finset (Fin n)} {w r_B : Fin n},
      IsBridgeJoin T A B w r_B → S ⊆ A ∪ B →
      IsSubtree T S → (S ∩ A).Nonempty → (S ∩ B).Nonempty →
      S ∩ A ∈ rootedSubtreesIn T A w := by
    intro A B S w r_B hJ hS_sub hS hSA hSB
    obtain ⟨a₀, ha₀⟩ := hSA
    obtain ⟨b₀, hb₀⟩ := hSB
    have ha₀S : a₀ ∈ S := (Finset.mem_inter.mp ha₀).1
    have ha₀A : a₀ ∈ A := (Finset.mem_inter.mp ha₀).2
    have hb₀S : b₀ ∈ S := (Finset.mem_inter.mp hb₀).1
    have hb₀B : b₀ ∈ B := (Finset.mem_inter.mp hb₀).2
    obtain ⟨q, hq_supp⟩ := exists_walk_of_isSubtree hS ha₀S hb₀S
    have hq_AB : ∀ z ∈ q.support, z ∈ A ∪ B := fun z hz => hS_sub (hq_supp z hz)
    have he : s(w, r_B) ∈ q.edges :=
      bridge_walk_mem_edges hJ q hq_AB (Or.inl ⟨ha₀A, hb₀B⟩)
    have hwS : w ∈ S := hq_supp w (q.fst_mem_support_of_mem_edges he)
    have hwSA : w ∈ S ∩ A := Finset.mem_inter.mpr ⟨hwS, hJ.2.1⟩
    have hSA_subtree : IsSubtree T (S ∩ A) := by
      refine ⟨⟨w, hwSA⟩, ?_⟩
      have : Nonempty ↑((S ∩ A : Finset (Fin n)) : Set (Fin n)) := ⟨⟨w, hwSA⟩⟩
      refine ⟨?_⟩
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      have hxS : x ∈ S := (Finset.mem_inter.mp hx).1
      have hxA : x ∈ A := (Finset.mem_inter.mp hx).2
      have hyS : y ∈ S := (Finset.mem_inter.mp hy).1
      have hyA : y ∈ A := (Finset.mem_inter.mp hy).2
      obtain ⟨q₁, hq₁_supp⟩ := exists_walk_of_isSubtree hS hxS hyS
      let p : T.Walk x y := (q₁.toPath : T.Walk x y)
      have hp_path : p.IsPath := q₁.toPath.2
      have hp_S : ∀ z ∈ p.support, z ∈ S := fun z hz => hq₁_supp z (q₁.support_toPath_subset hz)
      have hp_AB : ∀ z ∈ p.support, z ∈ A ∪ B := fun z hz => hS_sub (hp_S z hz)
      have hp_A : ∀ z ∈ p.support, z ∈ A :=
        bridge_path_support_left hJ p hp_path hp_AB hxA hyA
      have hp_SA : ∀ z ∈ p.support, z ∈ ((S ∩ A : Finset (Fin n)) : Set (Fin n)) :=
        fun z hz => Finset.mem_inter.mpr ⟨hp_S z hz, hp_A z hz⟩
      exact (p.induce ((S ∩ A : Finset (Fin n)) : Set (Fin n)) hp_SA).reachable
    simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hSA_subtree, Finset.inter_subset_right, hwSA⟩
  have bridge_union_isSubtree : ∀ {A B SA SB : Finset (Fin n)} {w r_B : Fin n},
      IsBridgeJoin T A B w r_B →
      SA ∈ rootedSubtreesIn T A w → SB ∈ rootedSubtreesIn T B r_B →
      IsSubtree T (SA ∪ SB) := by
    intro A B SA SB w r_B hJ hSA hSB
    simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hSA hSB
    rcases hSA with ⟨hSA_sub, _, hw_SA⟩
    rcases hSB with ⟨hSB_sub, _, hr_SB⟩
    have hw_U : w ∈ SA ∪ SB := Finset.mem_union_left SB hw_SA
    have hr_U : r_B ∈ SA ∪ SB := Finset.mem_union_right SA hr_SB
    refine ⟨⟨w, hw_U⟩, ?_⟩
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨w, hw_U⟩, ?_⟩
    rintro ⟨x, hx⟩
    rcases Finset.mem_union.mp hx with hxA | hxB
    · obtain ⟨q, hq⟩ := exists_walk_of_isSubtree hSA_sub hw_SA hxA
      have hq_U : ∀ z ∈ q.support, z ∈ ((SA ∪ SB : Finset (Fin n)) : Set (Fin n)) :=
        fun z hz => Finset.mem_union_left SB (hq z hz)
      exact (q.induce ((SA ∪ SB : Finset (Fin n)) : Set (Fin n)) hq_U).reachable
    · obtain ⟨q, hq⟩ := exists_walk_of_isSubtree hSB_sub hr_SB hxB
      have hq_U : ∀ z ∈ q.support, z ∈ ((SA ∪ SB : Finset (Fin n)) : Set (Fin n)) :=
        fun z hz => Finset.mem_union_right SA (hq z hz)
      have hadj_ind : (T.induce ((SA ∪ SB : Finset (Fin n)) : Set (Fin n))).Adj ⟨w, hw_U⟩ ⟨r_B, hr_U⟩ :=
        hJ.2.2.2.1
      exact hadj_ind.reachable.trans (q.induce ((SA ∪ SB : Finset (Fin n)) : Set (Fin n)) hq_U).reachable
  have bridge_join_rooted_moments_local : ∀ (A B : Finset (Fin n)) (w r_B : Fin n),
      IsBridgeJoin T A B w r_B →
      rootedCount T (A ∪ B) w = rootedCount T A w * (1 + rootedCount T B r_B) ∧
      rootedOrderSum T (A ∪ B) w =
        rootedOrderSum T A w * (1 + rootedCount T B r_B) + rootedCount T A w * rootedOrderSum T B r_B := by
    intro A B w r_B hJ
    let RA_set := rootedSubtreesIn T A w
    let RB_set := rootedSubtreesIn T B r_B
    let φ : Finset (Fin n) × Finset (Fin n) → Finset (Fin n) := fun p => p.1 ∪ p.2
    let M := (RA_set ×ˢ RB_set).image φ
    have h_inter_left : ∀ {X Y : Finset (Fin n)}, X ⊆ A → Y ⊆ B → (X ∪ Y) ∩ A = X := by
      intro X Y hX hY
      ext z
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hzX | hzY, hzA⟩
        · exact hzX
        · exact False.elim (Finset.disjoint_left.mp hJ.1 hzA (hY hzY))
      · intro hzX
        exact ⟨Or.inl hzX, hX hzX⟩
    have h_inter_right : ∀ {X Y : Finset (Fin n)}, X ⊆ A → Y ⊆ B → (X ∪ Y) ∩ B = Y := by
      intro X Y hX hY
      ext z
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hzX | hzY, hzB⟩
        · exact False.elim (Finset.disjoint_left.mp hJ.1 (hX hzX) hzB)
        · exact hzY
      · intro hzY
        exact ⟨Or.inr hzY, hY hzY⟩
    have h_inj : Set.InjOn φ ((RA_set ×ˢ RB_set : Finset (Finset (Fin n) × Finset (Fin n))) : Set (Finset (Fin n) × Finset (Fin n))) := by
      intro p₁ hp₁ p₂ hp₂ h_eq
      rcases Finset.mem_product.mp (Finset.mem_coe.mp hp₁) with ⟨hp₁A, hp₁B⟩
      rcases Finset.mem_product.mp (Finset.mem_coe.mp hp₂) with ⟨hp₂A, hp₂B⟩
      have h1A : p₁.1 ⊆ A := by
        simp only [RA_set, rootedSubtreesIn, Finset.mem_filter] at hp₁A
        exact hp₁A.2.1
      have h1B : p₁.2 ⊆ B := by
        simp only [RB_set, rootedSubtreesIn, Finset.mem_filter] at hp₁B
        exact hp₁B.2.1
      have h2A : p₂.1 ⊆ A := by
        simp only [RA_set, rootedSubtreesIn, Finset.mem_filter] at hp₂A
        exact hp₂A.2.1
      have h2B : p₂.2 ⊆ B := by
        simp only [RB_set, rootedSubtreesIn, Finset.mem_filter] at hp₂B
        exact hp₂B.2.1
      have h1 : p₁.1 = p₂.1 := by
        calc p₁.1 = (p₁.1 ∪ p₁.2) ∩ A := (h_inter_left h1A h1B).symm
          _ = (p₂.1 ∪ p₂.2) ∩ A := by rw [show p₁.1 ∪ p₁.2 = p₂.1 ∪ p₂.2 from h_eq]
          _ = p₂.1 := h_inter_left h2A h2B
      have h2 : p₁.2 = p₂.2 := by
        calc p₁.2 = (p₁.1 ∪ p₁.2) ∩ B := (h_inter_right h1A h1B).symm
          _ = (p₂.1 ∪ p₂.2) ∩ B := by rw [show p₁.1 ∪ p₁.2 = p₂.1 ∪ p₂.2 from h_eq]
          _ = p₂.2 := h_inter_right h2A h2B
      exact Prod.ext h1 h2
    have hM_card : M.card = rootedCount T A w * rootedCount T B r_B := by
      dsimp [M, RA_set, RB_set, rootedCount]
      rw [Finset.card_image_of_injOn h_inj, Finset.card_product]
    have hM_sum : ∑ S ∈ M, S.card =
        rootedOrderSum T A w * rootedCount T B r_B + rootedCount T A w * rootedOrderSum T B r_B := by
      dsimp [M]
      rw [Finset.sum_image h_inj, Finset.sum_product]
      have h_inner : ∀ x ∈ RA_set,
          ∑ y ∈ RB_set, (x ∪ y).card = x.card * RB_set.card + ∑ y ∈ RB_set, y.card := by
        intro x hx
        have hx_sub : x ⊆ A := by
          simp only [RA_set, rootedSubtreesIn, Finset.mem_filter] at hx
          exact hx.2.1
        have h_congr : ∑ y ∈ RB_set, (x ∪ y).card = ∑ y ∈ RB_set, (x.card + y.card) := by
          refine Finset.sum_congr rfl fun y hy => ?_
          have hy_sub : y ⊆ B := by
            simp only [RB_set, rootedSubtreesIn, Finset.mem_filter] at hy
            exact hy.2.1
          exact Finset.card_union_of_disjoint (Disjoint.mono hx_sub hy_sub hJ.1)
        rw [h_congr, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
      rw [Finset.sum_congr rfl h_inner, Finset.sum_add_distrib, ← Finset.sum_mul,
        Finset.sum_const, smul_eq_mul]
      rfl
    have h_mem_M : ∀ S : Finset (Fin n),
        S ∈ M ↔ S ∈ subtreesIn T (A ∪ B) ∧ (S ∩ A).Nonempty ∧ (S ∩ B).Nonempty := by
      intro S
      constructor
      · intro hS
        obtain ⟨⟨SA, SB⟩, hp, rfl⟩ := Finset.mem_image.mp hS
        rcases Finset.mem_product.mp hp with ⟨hSA, hSB⟩
        have hSA' := hSA
        have hSB' := hSB
        simp only [RA_set, RB_set, rootedSubtreesIn, subtrees, Finset.mem_filter,
          Finset.mem_univ, true_and] at hSA' hSB'
        have h_sub_AB : SA ∪ SB ⊆ A ∪ B := Finset.union_subset_union hSA'.2.1 hSB'.2.1
        have h_tree : IsSubtree T (SA ∪ SB) := bridge_union_isSubtree hJ hSA hSB
        have h_in_sub : SA ∪ SB ∈ subtreesIn T (A ∪ B) := by
          simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨h_tree, h_sub_AB⟩
        have h_ne_A : ((SA ∪ SB) ∩ A).Nonempty := by
          rw [h_inter_left hSA'.2.1 hSB'.2.1]
          exact ⟨w, hSA'.2.2⟩
        have h_ne_B : ((SA ∪ SB) ∩ B).Nonempty := by
          rw [h_inter_right hSA'.2.1 hSB'.2.1]
          exact ⟨r_B, hSB'.2.2⟩
        exact ⟨h_in_sub, h_ne_A, h_ne_B⟩
      · rintro ⟨hS_in, hSA_ne, hSB_ne⟩
        simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hS_in
        rcases hS_in with ⟨hS_tree, hS_sub⟩
        have hSA_mem : S ∩ A ∈ RA_set := bridge_crossing_left hJ hS_sub hS_tree hSA_ne hSB_ne
        have hS_sub' : S ⊆ B ∪ A := by simpa [Finset.union_comm] using hS_sub
        have hSB_mem : S ∩ B ∈ RB_set :=
          bridge_crossing_left (isBridgeJoin_symm hJ) hS_sub' hS_tree hSB_ne hSA_ne
        refine Finset.mem_image.mpr ⟨(S ∩ A, S ∩ B), Finset.mem_product.mpr ⟨hSA_mem, hSB_mem⟩, ?_⟩
        dsimp [φ]
        rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hS_sub]
    have h_sub_of_inter_empty_right : ∀ {S : Finset (Fin n)}, S ⊆ A ∪ B → S ∩ B = ∅ → S ⊆ A := by
      intro S hS h_emp z hz
      rcases Finset.mem_union.mp (hS hz) with hzA | hzB
      · exact hzA
      · exfalso
        have : z ∈ (∅ : Finset (Fin n)) := h_emp ▸ Finset.mem_inter.mpr ⟨hz, hzB⟩
        exact Finset.notMem_empty z this
    have h_root_disj : Disjoint RA_set M := by
      rw [Finset.disjoint_left]
      intro S hS_RA hS_M
      obtain ⟨_, _, b, hb⟩ := (h_mem_M S).mp hS_M
      have hS_A : S ⊆ A := by
        simp only [RA_set, rootedSubtreesIn, Finset.mem_filter] at hS_RA
        exact hS_RA.2.1
      exact Finset.disjoint_left.mp hJ.1 (hS_A (Finset.mem_inter.mp hb).1) (Finset.mem_inter.mp hb).2
    have h_root_part : rootedSubtreesIn T (A ∪ B) w = RA_set ∪ M := by
      ext S
      rw [Finset.mem_union, h_mem_M]
      constructor
      · intro hS
        simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hS
        rcases hS with ⟨hS_tree, hS_sub, hwS⟩
        rcases Finset.eq_empty_or_nonempty (S ∩ B) with h_emp | hSB_ne
        · left
          simp only [RA_set, rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hS_tree, h_sub_of_inter_empty_right hS_sub h_emp, hwS⟩
        · right
          have hS_in : S ∈ subtreesIn T (A ∪ B) := by
            simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hS_tree, hS_sub⟩
          exact ⟨hS_in, ⟨w, Finset.mem_inter.mpr ⟨hwS, hJ.2.1⟩⟩, hSB_ne⟩
      · rintro (hS_RA | ⟨hS_in, hSA_ne, hSB_ne⟩)
        · simp only [RA_set, rootedSubtreesIn, subtrees, Finset.mem_filter,
            Finset.mem_univ, true_and] at hS_RA ⊢
          exact ⟨hS_RA.1, Finset.Subset.trans hS_RA.2.1 Finset.subset_union_left, hS_RA.2.2⟩
        · simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hS_in
          have hSA_mem : S ∩ A ∈ RA_set :=
            bridge_crossing_left hJ hS_in.2 hS_in.1 hSA_ne hSB_ne
          have hw_SA : w ∈ S ∩ A := by
            simp only [RA_set, rootedSubtreesIn, Finset.mem_filter] at hSA_mem
            exact hSA_mem.2.2
          simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hS_in.1, hS_in.2, (Finset.mem_inter.mp hw_SA).1⟩
    have h_eq1 : rootedCount T (A ∪ B) w = rootedCount T A w * (1 + rootedCount T B r_B) := by
      dsimp [rootedCount]
      rw [h_root_part, Finset.card_union_of_disjoint h_root_disj, hM_card]
      dsimp [RA_set, rootedCount]
      ring
    have h_eq2 : rootedOrderSum T (A ∪ B) w =
        rootedOrderSum T A w * (1 + rootedCount T B r_B) + rootedCount T A w * rootedOrderSum T B r_B := by
      dsimp [rootedOrderSum]
      rw [h_root_part, Finset.sum_union h_root_disj, hM_sum]
      dsimp [RA_set, rootedOrderSum]
      ring
    exact ⟨h_eq1, h_eq2⟩
  have rooted_moment_ladder_step : ∀ (s₁ t₁ s₂ t₂ : ℕ),
      1 ≤ s₁ → s₁ ≤ t₁ → 2 * t₁ ≤ s₁ * (s₁ + 1) →
      (2 ≤ s₁ → 3 * s₁ ≤ 2 * t₁) → (3 ≤ s₁ → 2 * s₁ ≤ t₁) →
      1 ≤ s₂ → s₂ ≤ t₂ → 2 * t₂ ≤ s₂ * (s₂ + 1) →
      (2 ≤ s₂ → 3 * s₂ ≤ 2 * t₂) → (3 ≤ s₂ → 2 * s₂ ≤ t₂) →
      1 ≤ s₁ * (1 + s₂) ∧
      s₁ * (1 + s₂) ≤ t₁ * (1 + s₂) + s₁ * t₂ ∧
      2 * (t₁ * (1 + s₂) + s₁ * t₂) ≤ (s₁ * (1 + s₂)) * (s₁ * (1 + s₂) + 1) ∧
      (2 ≤ s₁ * (1 + s₂) → 3 * (s₁ * (1 + s₂)) ≤ 2 * (t₁ * (1 + s₂) + s₁ * t₂)) ∧
      (3 ≤ s₁ * (1 + s₂) → 2 * (s₁ * (1 + s₂)) ≤ t₁ * (1 + s₂) + s₁ * t₂) ∧
      (5 ≤ s₁ * (1 + s₂) → 5 * (s₁ * (1 + s₂)) ≤ 2 * (t₁ * (1 + s₂) + s₁ * t₂)) := by
    intro s₁ t₁ s₂ t₂ hs₁ ht₁ hub₁ h2_1 h3_1 hs₂ ht₂ hub₂ h2_2 h3_2
    have h_mul1 : s₁ ≤ s₁ * s₂ := by simpa using Nat.mul_le_mul_left s₁ hs₂
    have h_mul2 : s₂ ≤ s₁ * s₂ := by simpa using Nat.mul_le_mul_right s₂ hs₁
    have h_t1 : s₁ * (1 + s₂) ≤ t₁ * (1 + s₂) := Nat.mul_le_mul_right (1 + s₂) ht₁
    have h_t2 : s₁ * s₂ ≤ s₁ * t₂ := Nat.mul_le_mul_left s₁ ht₂
    have hub_1 : (2 * t₁) * (1 + s₂) ≤ (s₁ * (s₁ + 1)) * (1 + s₂) :=
      Nat.mul_le_mul_right (1 + s₂) hub₁
    have hub_2 : s₁ * (2 * t₂) ≤ s₁ * (s₂ * (s₂ + 1)) :=
      Nat.mul_le_mul_left s₁ hub₂
    have h_sum_le : s₁ + s₂ + 1 ≤ s₁ * (1 + s₂) + 1 := by linarith
    have hub_3 : (s₁ * (1 + s₂)) * (s₁ + s₂ + 1) ≤ (s₁ * (1 + s₂)) * (s₁ * (1 + s₂) + 1) :=
      Nat.mul_le_mul_left (s₁ * (1 + s₂)) h_sum_le
    have hub : 2 * (t₁ * (1 + s₂) + s₁ * t₂) ≤ (s₁ * (1 + s₂)) * (s₁ * (1 + s₂) + 1) := by
      calc 2 * (t₁ * (1 + s₂) + s₁ * t₂)
        _ = (2 * t₁) * (1 + s₂) + s₁ * (2 * t₂) := by ring
        _ ≤ (s₁ * (s₁ + 1)) * (1 + s₂) + s₁ * (s₂ * (s₂ + 1)) := Nat.add_le_add hub_1 hub_2
        _ = (s₁ * (1 + s₂)) * (s₁ + s₂ + 1) := by ring
        _ ≤ (s₁ * (1 + s₂)) * (s₁ * (1 + s₂) + 1) := hub_3
    refine ⟨by linarith, by linarith, hub, ?_, ?_, ?_⟩
    · intro _
      linarith
    · intro hs3
      by_cases h2 : 2 ≤ s₁
      · have hL2 := h2_1 h2
        have hL2_mul : (3 * s₁) * (1 + s₂) ≤ (2 * t₁) * (1 + s₂) :=
          Nat.mul_le_mul_right (1 + s₂) hL2
        linarith
      · have hs₁_eq : s₁ = 1 := by omega
        subst hs₁_eq
        have hs₂_ge : 2 ≤ s₂ := by omega
        have hL2 := h2_2 hs₂_ge
        have ht₁_mul : 1 + s₂ ≤ t₁ * (1 + s₂) := by simpa using h_t1
        omega
    · intro hs5
      by_cases h3 : 3 ≤ s₁
      · have hL3 := h3_1 h3
        have hL3_mul : (2 * s₁) * (1 + s₂) ≤ t₁ * (1 + s₂) :=
          Nat.mul_le_mul_right (1 + s₂) hL3
        linarith
      · by_cases h2 : 2 ≤ s₁
        · have hs₁_eq : s₁ = 2 := by omega
          subst hs₁_eq
          have hs₂_ge : 2 ≤ s₂ := by omega
          have hL2_a : 6 ≤ 2 * t₁ := h2_1 (by omega)
          have ht₁_ge : 3 ≤ t₁ := by omega
          have ht₁_mul : 3 * (1 + s₂) ≤ t₁ * (1 + s₂) :=
            Nat.mul_le_mul_right (1 + s₂) ht₁_ge
          have hL2_b := h2_2 hs₂_ge
          omega
        · have hs₁_eq : s₁ = 1 := by omega
          subst hs₁_eq
          have hs₂_ge : 4 ≤ s₂ := by omega
          have hL3 := h3_2 (by omega)
          have ht₁_mul : 1 + s₂ ≤ t₁ * (1 + s₂) := by simpa using h_t1
          omega
  have h_ind : ∀ (m : ℕ) (U : Finset (Fin n)) (w : Fin n),
      U.card = m → IsSubtree T U → w ∈ U →
      1 ≤ rootedCount T U w ∧
      rootedCount T U w ≤ rootedOrderSum T U w ∧
      2 * rootedOrderSum T U w ≤ rootedCount T U w * (rootedCount T U w + 1) ∧
      (2 ≤ rootedCount T U w → 3 * rootedCount T U w ≤ 2 * rootedOrderSum T U w) ∧
      (3 ≤ rootedCount T U w → 2 * rootedCount T U w ≤ rootedOrderSum T U w) ∧
      (5 ≤ rootedCount T U w → 5 * rootedCount T U w ≤ 2 * rootedOrderSum T U w) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro U w hm hU hw
      by_cases hle : U.card ≤ 1
      · obtain ⟨hs, ht⟩ := rooted_singleton_moments U w hw hle
        rw [hs, ht]
        omega
      · push_neg at hle
        obtain ⟨A, B, r_B, hU_eq, hA_sub, hB_sub, hJ⟩ :=
          subtree_exists_root_bridge_split U w hU hw hle
        have hc₁ : 1 ≤ A.card := Finset.card_pos.mpr ⟨w, hJ.2.1⟩
        have hc₂ : 1 ≤ B.card := Finset.card_pos.mpr ⟨r_B, hJ.2.2.1⟩
        have hU_card : U.card = A.card + B.card := by
          rw [hU_eq, Finset.card_union_of_disjoint hJ.1]
        have hA_lt : A.card < m := by omega
        have hB_lt : B.card < m := by omega
        obtain ⟨hs₁, ht₁, hub₁, h2_1, h3_1, _⟩ := ih A.card hA_lt A w rfl hA_sub hJ.2.1
        obtain ⟨hs₂, ht₂, hub₂, h2_2, h3_2, _⟩ := ih B.card hB_lt B r_B rfl hB_sub hJ.2.2.1
        obtain ⟨h_s, h_t⟩ := bridge_join_rooted_moments_local A B w r_B hJ
        rw [hU_eq, h_s, h_t]
        exact rooted_moment_ladder_step
          (rootedCount T A w) (rootedOrderSum T A w)
          (rootedCount T B r_B) (rootedOrderSum T B r_B)
          hs₁ ht₁ hub₁ h2_1 h3_1 hs₂ ht₂ hub₂ h2_2 h3_2
  obtain ⟨h1, h2, h3, _, _, h6⟩ := h_ind U₀.card U₀ r₀ rfl hU₀ hr₀
  exact ⟨h1, h2, h3, h6⟩

theorem broom_shortening_or_threshold : ∀ (n : ℕ) (hn : 1 ≤ n) (T : SimpleGraph (Fin n)),
    T.IsTree → ∀ (ℓ k : ℕ) (A B C L_k : Finset (Fin n)) (w r_B r_C : Fin n)
      (v : Fin (ℓ + 1) → Fin n),
      ((1 ≤ ℓ ∧ 2 ≤ k) ∨ (ℓ = 0 ∧ 3 ≤ k)) →
      Function.Injective v →
      IsSubtree T A → IsSubtree T B → IsSubtree T C →
      L_k.card = k →
      Disjoint A B → Disjoint A C → Disjoint B C →
      Disjoint (A ∪ B ∪ C) (Finset.univ.image v) → Disjoint (A ∪ B ∪ C) L_k →
      Disjoint (Finset.univ.image v) L_k →
      A ∪ B ∪ C ∪ (Finset.univ.image v) ∪ L_k = Finset.univ →
      IsBridgeJoin T A B w r_B →
      IsBridgeJoin T (A ∪ B) C w r_C →
      IsBridgeJoin T (A ∪ B ∪ C) ((Finset.univ.image v) ∪ L_k) w (v 0) →
      (∀ i j : Fin (ℓ + 1), T.Adj (v i) (v j) ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val)) →
      IsLeafPacket T L_k (v (Fin.last ℓ)) →
      ℓ + 2 ^ k ≤ rootedCount T B r_B →
      ℓ + 2 ^ k ≤ rootedCount T C r_C →
      (∃ T' : SimpleGraph (Fin n), T'.IsTree ∧ meanSubtreeOrder T < meanSubtreeOrder T') ∨
      broomThreshold ℓ k ≤
        meanSubtreeOrder T -
          ((rootedOrderSum T A w : ℚ) / (rootedCount T A w : ℚ) +
           (rootedOrderSum T B r_B : ℚ) / ((rootedCount T B r_B : ℚ) + 1) +
           (rootedOrderSum T C r_C : ℚ) / ((rootedCount T C r_C : ℚ) + 1)) :=
by
  have isBridgeJoin_symm : ∀ {n : ℕ} {T : SimpleGraph (Fin n)} {A B : Finset (Fin n)} {w r_B : Fin n},
      IsBridgeJoin T A B w r_B → IsBridgeJoin T B A r_B w := by
    intro n T A B w r_B hJ
    rcases hJ with ⟨h_disj, hw, hr_B, hadj, h_bridge⟩
    refine ⟨h_disj.symm, hr_B, hw, T.symm hadj, ?_⟩
    intro u hu v hv huv
    exact (h_bridge v hv u hu (T.symm huv)).symm
  have exists_walk_of_isSubtree : ∀ {n : ℕ} {T : SimpleGraph (Fin n)} {S : Finset (Fin n)},
      IsSubtree T S → ∀ {a b : Fin n}, a ∈ S → b ∈ S →
      ∃ q : T.Walk a b, ∀ z ∈ q.support, z ∈ S := by
    intro n T S hS a b ha hb
    obtain ⟨q₀⟩ := hS.2.preconnected ⟨a, ha⟩ ⟨b, hb⟩
    suffices ∀ {u v : ↑(S : Set (Fin n))} (q : (T.induce (S : Set (Fin n))).Walk u v),
        ∃ q' : T.Walk u.1 v.1, ∀ z ∈ q'.support, z ∈ S from this q₀
    intro u v q
    induction q with
    | @nil u =>
      refine ⟨SimpleGraph.Walk.nil, ?_⟩
      intro z hz
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      rw [hz]
      exact Finset.mem_coe.mp u.2
    | @cons u c v hadj q' ih =>
      obtain ⟨q₁, hq₁⟩ := ih
      refine ⟨SimpleGraph.Walk.cons hadj q₁, ?_⟩
      intro z hz
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz'
      · exact Finset.mem_coe.mp u.2
      · exact hq₁ z hz'
  have bridge_walk_mem_edges : ∀ {n : ℕ} {T : SimpleGraph (Fin n)} {A B : Finset (Fin n)} {w r_B : Fin n},
      IsBridgeJoin T A B w r_B → ∀ {a b : Fin n} (q : T.Walk a b),
      (∀ z ∈ q.support, z ∈ A ∪ B) →
      ((a ∈ A ∧ b ∈ B) ∨ (a ∈ B ∧ b ∈ A)) →
      s(w, r_B) ∈ q.edges := by
    intro n T A B w r_B hJ a b q
    induction q with
    | nil =>
      intro _ h_ab
      rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact False.elim (Finset.disjoint_left.mp hJ.1 ha hb)
      · exact False.elim (Finset.disjoint_left.mp hJ.1 hb ha)
    | @cons a c b h_step q' ih =>
      intro h_supp h_ab
      have hc_mem : c ∈ A ∪ B := h_supp c (by
        simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.start_mem_support])
      have h_supp' : ∀ z ∈ q'.support, z ∈ A ∪ B := fun z hz =>
        h_supp z (by simp [SimpleGraph.Walk.support_cons, hz])
      rcases Finset.mem_union.mp hc_mem with hcA | hcB
      · rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ (ih h_supp' (Or.inl ⟨hcA, hb⟩))
        · obtain ⟨hcw, har⟩ := hJ.2.2.2.2 c hcA a ha (T.symm h_step)
          subst hcw har
          rw [SimpleGraph.Walk.edges_cons, Sym2.eq_swap]
          exact List.mem_cons_self
      · rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · obtain ⟨haw, hcr⟩ := hJ.2.2.2.2 a ha c hcB h_step
          subst haw hcr
          rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_self
        · rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ (ih h_supp' (Or.inr ⟨hcB, hb⟩))
  have bridge_path_support_left : ∀ {n : ℕ} {T : SimpleGraph (Fin n)} {A B : Finset (Fin n)} {w r_B : Fin n},
      IsBridgeJoin T A B w r_B → ∀ {a b : Fin n} (p : T.Walk a b), p.IsPath →
      (∀ z ∈ p.support, z ∈ A ∪ B) → a ∈ A → b ∈ A →
      ∀ z ∈ p.support, z ∈ A := by
    intro n T A B w r_B hJ a b p hp h_supp ha hb z hz
    rcases Finset.mem_union.mp (h_supp z hz) with hzA | hzB
    · exact hzA
    · exfalso
      let p₁ := p.takeUntil z hz
      let p₂ := p.dropUntil z hz
      have hp₁_supp : ∀ x ∈ p₁.support, x ∈ A ∪ B :=
        fun x hx => h_supp x (p.support_takeUntil_subset hz hx)
      have hp₂_supp : ∀ x ∈ p₂.support, x ∈ A ∪ B :=
        fun x hx => h_supp x (p.support_dropUntil_subset hz hx)
      have he₁ : s(w, r_B) ∈ p₁.edges :=
        bridge_walk_mem_edges hJ p₁ hp₁_supp (Or.inl ⟨ha, hzB⟩)
      have he₂ : s(w, r_B) ∈ p₂.edges :=
        bridge_walk_mem_edges hJ p₂ hp₂_supp (Or.inr ⟨hzB, hb⟩)
      have h_nodup : p.edges.Nodup := hp.isTrail.edges_nodup
      have h_edges : p₁.edges ++ p₂.edges = p.edges := by
        rw [← SimpleGraph.Walk.edges_append, p.take_spec hz]
      rw [← h_edges, List.nodup_append] at h_nodup
      exact h_nodup.2.2 s(w, r_B) he₁ s(w, r_B) he₂ rfl
  have bridge_crossing_left : ∀ {n : ℕ} {T : SimpleGraph (Fin n)} {A B S : Finset (Fin n)} {w r_B : Fin n},
      IsBridgeJoin T A B w r_B → S ⊆ A ∪ B →
      IsSubtree T S → (S ∩ A).Nonempty → (S ∩ B).Nonempty →
      S ∩ A ∈ rootedSubtreesIn T A w := by
    intro n T A B S w r_B hJ hS_sub hS hSA hSB
    obtain ⟨a₀, ha₀⟩ := hSA
    obtain ⟨b₀, hb₀⟩ := hSB
    have ha₀S : a₀ ∈ S := (Finset.mem_inter.mp ha₀).1
    have ha₀A : a₀ ∈ A := (Finset.mem_inter.mp ha₀).2
    have hb₀S : b₀ ∈ S := (Finset.mem_inter.mp hb₀).1
    have hb₀B : b₀ ∈ B := (Finset.mem_inter.mp hb₀).2
    obtain ⟨q, hq_supp⟩ := exists_walk_of_isSubtree hS ha₀S hb₀S
    have hq_AB : ∀ z ∈ q.support, z ∈ A ∪ B := fun z hz => hS_sub (hq_supp z hz)
    have he : s(w, r_B) ∈ q.edges :=
      bridge_walk_mem_edges hJ q hq_AB (Or.inl ⟨ha₀A, hb₀B⟩)
    have hwS : w ∈ S := hq_supp w (q.fst_mem_support_of_mem_edges he)
    have hwSA : w ∈ S ∩ A := Finset.mem_inter.mpr ⟨hwS, hJ.2.1⟩
    have hSA_subtree : IsSubtree T (S ∩ A) := by
      refine ⟨⟨w, hwSA⟩, ?_⟩
      have : Nonempty ↑((S ∩ A : Finset (Fin n)) : Set (Fin n)) := ⟨⟨w, hwSA⟩⟩
      refine ⟨?_⟩
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      have hxS : x ∈ S := (Finset.mem_inter.mp hx).1
      have hxA : x ∈ A := (Finset.mem_inter.mp hx).2
      have hyS : y ∈ S := (Finset.mem_inter.mp hy).1
      have hyA : y ∈ A := (Finset.mem_inter.mp hy).2
      obtain ⟨q₁, hq₁_supp⟩ := exists_walk_of_isSubtree hS hxS hyS
      let p : T.Walk x y := (q₁.toPath : T.Walk x y)
      have hp_path : p.IsPath := q₁.toPath.2
      have hp_S : ∀ z ∈ p.support, z ∈ S := fun z hz => hq₁_supp z (q₁.support_toPath_subset hz)
      have hp_AB : ∀ z ∈ p.support, z ∈ A ∪ B := fun z hz => hS_sub (hp_S z hz)
      have hp_A : ∀ z ∈ p.support, z ∈ A :=
        bridge_path_support_left hJ p hp_path hp_AB hxA hyA
      have hp_SA : ∀ z ∈ p.support, z ∈ ((S ∩ A : Finset (Fin n)) : Set (Fin n)) :=
        fun z hz => Finset.mem_inter.mpr ⟨hp_S z hz, hp_A z hz⟩
      exact (p.induce ((S ∩ A : Finset (Fin n)) : Set (Fin n)) hp_SA).reachable
    simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hSA_subtree, Finset.inter_subset_right, hwSA⟩
  have bridge_union_isSubtree : ∀ {n : ℕ} {T : SimpleGraph (Fin n)} {A B SA SB : Finset (Fin n)} {w r_B : Fin n},
      IsBridgeJoin T A B w r_B →
      SA ∈ rootedSubtreesIn T A w → SB ∈ rootedSubtreesIn T B r_B →
      IsSubtree T (SA ∪ SB) := by
    intro n T A B SA SB w r_B hJ hSA hSB
    simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hSA hSB
    rcases hSA with ⟨hSA_sub, _, hw_SA⟩
    rcases hSB with ⟨hSB_sub, _, hr_SB⟩
    have hw_U : w ∈ SA ∪ SB := Finset.mem_union_left SB hw_SA
    have hr_U : r_B ∈ SA ∪ SB := Finset.mem_union_right SA hr_SB
    refine ⟨⟨w, hw_U⟩, ?_⟩
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨w, hw_U⟩, ?_⟩
    rintro ⟨x, hx⟩
    rcases Finset.mem_union.mp hx with hxA | hxB
    · obtain ⟨q, hq⟩ := exists_walk_of_isSubtree hSA_sub hw_SA hxA
      have hq_U : ∀ z ∈ q.support, z ∈ ((SA ∪ SB : Finset (Fin n)) : Set (Fin n)) :=
        fun z hz => Finset.mem_union_left SB (hq z hz)
      exact (q.induce ((SA ∪ SB : Finset (Fin n)) : Set (Fin n)) hq_U).reachable
    · obtain ⟨q, hq⟩ := exists_walk_of_isSubtree hSB_sub hr_SB hxB
      have hq_U : ∀ z ∈ q.support, z ∈ ((SA ∪ SB : Finset (Fin n)) : Set (Fin n)) :=
        fun z hz => Finset.mem_union_right SA (hq z hz)
      have hadj_ind : (T.induce ((SA ∪ SB : Finset (Fin n)) : Set (Fin n))).Adj ⟨w, hw_U⟩ ⟨r_B, hr_U⟩ :=
        hJ.2.2.2.1
      exact hadj_ind.reachable.trans (q.induce ((SA ∪ SB : Finset (Fin n)) : Set (Fin n)) hq_U).reachable
  have bridge_join_rooted_moments : ∀ (n : ℕ) (T : SimpleGraph (Fin n))
      (U₁ U₂ : Finset (Fin n)) (r₁ r₂ : Fin n),
      IsBridgeJoin T U₁ U₂ r₁ r₂ →
      rootedCount T (U₁ ∪ U₂) r₁ = rootedCount T U₁ r₁ * (1 + rootedCount T U₂ r₂) ∧
      rootedOrderSum T (U₁ ∪ U₂) r₁ =
        rootedOrderSum T U₁ r₁ * (1 + rootedCount T U₂ r₂) +
        rootedCount T U₁ r₁ * rootedOrderSum T U₂ r₂ := by
    intro n T A B w r_B hJ
    classical
    let RA_set := rootedSubtreesIn T A w
    let RB_set := rootedSubtreesIn T B r_B
    let φ : Finset (Fin n) × Finset (Fin n) → Finset (Fin n) := fun p => p.1 ∪ p.2
    let M := (RA_set ×ˢ RB_set).image φ
    have h_inter_left : ∀ {X Y : Finset (Fin n)}, X ⊆ A → Y ⊆ B → (X ∪ Y) ∩ A = X := by
      intro X Y hX hY
      ext z
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hzX | hzY, hzA⟩
        · exact hzX
        · exact False.elim (Finset.disjoint_left.mp hJ.1 hzA (hY hzY))
      · intro hzX
        exact ⟨Or.inl hzX, hX hzX⟩
    have h_inter_right : ∀ {X Y : Finset (Fin n)}, X ⊆ A → Y ⊆ B → (X ∪ Y) ∩ B = Y := by
      intro X Y hX hY
      ext z
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hzX | hzY, hzB⟩
        · exact False.elim (Finset.disjoint_left.mp hJ.1 (hX hzX) hzB)
        · exact hzY
      · intro hzY
        exact ⟨Or.inr hzY, hY hzY⟩
    have h_inj : Set.InjOn φ ((RA_set ×ˢ RB_set : Finset (Finset (Fin n) × Finset (Fin n))) : Set (Finset (Fin n) × Finset (Fin n))) := by
      intro p₁ hp₁ p₂ hp₂ h_eq
      rcases Finset.mem_product.mp (Finset.mem_coe.mp hp₁) with ⟨hp₁A, hp₁B⟩
      rcases Finset.mem_product.mp (Finset.mem_coe.mp hp₂) with ⟨hp₂A, hp₂B⟩
      simp only [RA_set, RB_set, rootedSubtreesIn, Finset.mem_filter] at hp₁A hp₁B hp₂A hp₂B
      have h1A : p₁.1 ⊆ A := hp₁A.2.1
      have h1B : p₁.2 ⊆ B := hp₁B.2.1
      have h2A : p₂.1 ⊆ A := hp₂A.2.1
      have h2B : p₂.2 ⊆ B := hp₂B.2.1
      have h1 : p₁.1 = p₂.1 := by
        calc p₁.1 = (p₁.1 ∪ p₁.2) ∩ A := (h_inter_left h1A h1B).symm
          _ = (p₂.1 ∪ p₂.2) ∩ A := by rw [show p₁.1 ∪ p₁.2 = p₂.1 ∪ p₂.2 from h_eq]
          _ = p₂.1 := h_inter_left h2A h2B
      have h2 : p₁.2 = p₂.2 := by
        calc p₁.2 = (p₁.1 ∪ p₁.2) ∩ B := (h_inter_right h1A h1B).symm
          _ = (p₂.1 ∪ p₂.2) ∩ B := by rw [show p₁.1 ∪ p₁.2 = p₂.1 ∪ p₂.2 from h_eq]
          _ = p₂.2 := h_inter_right h2A h2B
      exact Prod.ext h1 h2
    have hM_card : M.card = rootedCount T A w * rootedCount T B r_B := by
      dsimp [M, RA_set, RB_set, rootedCount]
      rw [Finset.card_image_of_injOn h_inj, Finset.card_product]
    have hM_sum : ∑ S ∈ M, S.card =
        rootedOrderSum T A w * rootedCount T B r_B + rootedCount T A w * rootedOrderSum T B r_B := by
      dsimp [M]
      rw [Finset.sum_image h_inj, Finset.sum_product]
      have h_inner : ∀ x ∈ RA_set,
          ∑ y ∈ RB_set, (x ∪ y).card = x.card * RB_set.card + ∑ y ∈ RB_set, y.card := by
        intro x hx
        simp only [RA_set, rootedSubtreesIn, Finset.mem_filter] at hx
        have hx_sub : x ⊆ A := hx.2.1
        have h_congr : ∑ y ∈ RB_set, (x ∪ y).card = ∑ y ∈ RB_set, (x.card + y.card) := by
          refine Finset.sum_congr rfl fun y hy => ?_
          simp only [RB_set, rootedSubtreesIn, Finset.mem_filter] at hy
          have hy_sub : y ⊆ B := hy.2.1
          exact Finset.card_union_of_disjoint (Disjoint.mono hx_sub hy_sub hJ.1)
        rw [h_congr, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
      rw [Finset.sum_congr rfl h_inner, Finset.sum_add_distrib, ← Finset.sum_mul,
        Finset.sum_const, smul_eq_mul]
      rfl
    have h_mem_M : ∀ S : Finset (Fin n),
        S ∈ M ↔ S ∈ subtreesIn T (A ∪ B) ∧ (S ∩ A).Nonempty ∧ (S ∩ B).Nonempty := by
      intro S
      constructor
      · intro hS
        obtain ⟨⟨SA, SB⟩, hp, rfl⟩ := Finset.mem_image.mp hS
        rcases Finset.mem_product.mp hp with ⟨hSA, hSB⟩
        have hSA' := hSA
        have hSB' := hSB
        simp only [RA_set, RB_set, rootedSubtreesIn, subtrees, Finset.mem_filter,
          Finset.mem_univ, true_and] at hSA' hSB'
        have h_sub_AB : SA ∪ SB ⊆ A ∪ B := Finset.union_subset_union hSA'.2.1 hSB'.2.1
        have h_tree : IsSubtree T (SA ∪ SB) := bridge_union_isSubtree hJ hSA hSB
        have h_in_sub : SA ∪ SB ∈ subtreesIn T (A ∪ B) := by
          simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨h_tree, h_sub_AB⟩
        have h_ne_A : ((SA ∪ SB) ∩ A).Nonempty := by
          rw [h_inter_left hSA'.2.1 hSB'.2.1]
          exact ⟨w, hSA'.2.2⟩
        have h_ne_B : ((SA ∪ SB) ∩ B).Nonempty := by
          rw [h_inter_right hSA'.2.1 hSB'.2.1]
          exact ⟨r_B, hSB'.2.2⟩
        exact ⟨h_in_sub, h_ne_A, h_ne_B⟩
      · rintro ⟨hS_in, hSA_ne, hSB_ne⟩
        simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hS_in
        rcases hS_in with ⟨hS_tree, hS_sub⟩
        have hSA_mem : S ∩ A ∈ RA_set := bridge_crossing_left hJ hS_sub hS_tree hSA_ne hSB_ne
        have hS_sub' : S ⊆ B ∪ A := by simpa [Finset.union_comm] using hS_sub
        have hSB_mem : S ∩ B ∈ RB_set :=
          bridge_crossing_left (isBridgeJoin_symm hJ) hS_sub' hS_tree hSB_ne hSA_ne
        refine Finset.mem_image.mpr ⟨(S ∩ A, S ∩ B), Finset.mem_product.mpr ⟨hSA_mem, hSB_mem⟩, ?_⟩
        dsimp [φ]
        rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hS_sub]
    have h_sub_of_inter_empty_right : ∀ {S : Finset (Fin n)}, S ⊆ A ∪ B → S ∩ B = ∅ → S ⊆ A := by
      intro S hS h_emp z hz
      rcases Finset.mem_union.mp (hS hz) with hzA | hzB
      · exact hzA
      · exfalso
        have : z ∈ (∅ : Finset (Fin n)) := h_emp ▸ Finset.mem_inter.mpr ⟨hz, hzB⟩
        exact Finset.notMem_empty z this
    have h_root_disj : Disjoint RA_set M := by
      rw [Finset.disjoint_left]
      intro S hS_RA hS_M
      obtain ⟨_, _, b, hb⟩ := (h_mem_M S).mp hS_M
      simp only [RA_set, rootedSubtreesIn, Finset.mem_filter] at hS_RA
      have hS_A : S ⊆ A := hS_RA.2.1
      exact Finset.disjoint_left.mp hJ.1 (hS_A (Finset.mem_inter.mp hb).1) (Finset.mem_inter.mp hb).2
    have h_root_part : rootedSubtreesIn T (A ∪ B) w = RA_set ∪ M := by
      ext S
      rw [Finset.mem_union, h_mem_M]
      constructor
      · intro hS
        simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hS
        rcases hS with ⟨hS_tree, hS_sub, hwS⟩
        rcases Finset.eq_empty_or_nonempty (S ∩ B) with h_emp | hSB_ne
        · left
          simp only [RA_set, rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hS_tree, h_sub_of_inter_empty_right hS_sub h_emp, hwS⟩
        · right
          have hS_in : S ∈ subtreesIn T (A ∪ B) := by
            simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hS_tree, hS_sub⟩
          exact ⟨hS_in, ⟨w, Finset.mem_inter.mpr ⟨hwS, hJ.2.1⟩⟩, hSB_ne⟩
      · rintro (hS_RA | ⟨hS_in, hSA_ne, hSB_ne⟩)
        · simp only [RA_set, rootedSubtreesIn, subtrees, Finset.mem_filter,
            Finset.mem_univ, true_and] at hS_RA ⊢
          exact ⟨hS_RA.1, Finset.Subset.trans hS_RA.2.1 Finset.subset_union_left, hS_RA.2.2⟩
        · simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hS_in
          have hSA_mem : S ∩ A ∈ RA_set :=
            bridge_crossing_left hJ hS_in.2 hS_in.1 hSA_ne hSB_ne
          simp only [RA_set, rootedSubtreesIn, Finset.mem_filter] at hSA_mem
          have hw_SA : w ∈ S ∩ A := hSA_mem.2.2
          simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hS_in.1, hS_in.2, (Finset.mem_inter.mp hw_SA).1⟩
    have h_eq1 : rootedCount T (A ∪ B) w = rootedCount T A w * (1 + rootedCount T B r_B) := by
      dsimp [rootedCount]
      rw [h_root_part, Finset.card_union_of_disjoint h_root_disj, hM_card]
      dsimp [RA_set, rootedCount]
      ring
    have h_eq2 : rootedOrderSum T (A ∪ B) w =
        rootedOrderSum T A w * (1 + rootedCount T B r_B) + rootedCount T A w * rootedOrderSum T B r_B := by
      dsimp [rootedOrderSum]
      rw [h_root_part, Finset.sum_union h_root_disj, hM_sum]
      dsimp [RA_set, rootedOrderSum]
      ring
    exact ⟨h_eq1, h_eq2⟩
  have rooted_subtree_card_and_moment_bound : ∀ (n : ℕ) (T : SimpleGraph (Fin n))
      (U : Finset (Fin n)) (r : Fin n),
      T.IsTree → IsSubtree T U → r ∈ U →
      U.card ≤ rootedCount T U r ∧
      2 * rootedOrderSum T U r ≤ rootedCount T U r * (rootedCount T U r + 1) := by
    intro n T U₀ r₀ hT hU₀ hr₀
    classical
    have rooted_singleton_moments : ∀ (U : Finset (Fin n)) (w : Fin n),
        w ∈ U → U.card ≤ 1 →
        rootedCount T U w = 1 ∧
        rootedOrderSum T U w = 1 := by
      intro U w hw hle
      have hU_eq : U = {w} := by
        rw [Finset.eq_singleton_iff_unique_mem]
        refine ⟨hw, fun x hx => Finset.card_le_one.mp hle x hx w hw⟩
      subst hU_eq
      have hw_sub : IsSubtree T {w} := by
        refine ⟨Finset.singleton_nonempty w, ?_⟩
        have : Nonempty ↑(({w} : Finset (Fin n)) : Set (Fin n)) := ⟨⟨w, by simp⟩⟩
        refine ⟨?_⟩
        rintro ⟨a, ha⟩ ⟨b, hb⟩
        have ha' : a = w := by simpa using ha
        have hb' : b = w := by simpa using hb
        have hab : (⟨a, ha⟩ : ↑(({w} : Finset (Fin n)) : Set (Fin n))) = ⟨b, hb⟩ :=
          Subtype.ext (ha'.trans hb'.symm)
        rw [hab]
      have h_root_eq : rootedSubtreesIn T {w} w = {{w}} := by
        ext S
        simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        constructor
        · rintro ⟨⟨h_ne, _⟩, h_sub, _⟩
          rcases Finset.subset_singleton_iff.mp h_sub with rfl | rfl
          · exact False.elim (Finset.not_nonempty_empty h_ne)
          · rfl
        · rintro rfl
          exact ⟨hw_sub, Finset.Subset.refl _, Finset.mem_singleton_self w⟩
      simp [rootedCount, rootedOrderSum, h_root_eq]
    have subtree_exists_root_bridge_split : ∀ (U : Finset (Fin n)) (w : Fin n),
        IsSubtree T U → w ∈ U → 2 ≤ U.card →
        ∃ (A B : Finset (Fin n)) (r_B : Fin n),
          U = A ∪ B ∧ IsSubtree T A ∧ IsSubtree T B ∧ IsBridgeJoin T A B w r_B := by
      intro U w hU hw hge2
      obtain ⟨u, hu, huw⟩ := Finset.exists_mem_ne (by omega : 1 < U.card) w
      obtain ⟨p₀⟩ := hU.2.preconnected ⟨w, hw⟩ ⟨u, hu⟩
      have h_adj_exists : ∃ r_B ∈ U, T.Adj w r_B := by
        cases p₀ with
        | nil => exact False.elim (huw rfl)
        | @cons _ r _ hadj _ => exact ⟨r.1, r.2, hadj⟩
      obtain ⟨r_B, hr_B_U, hadj_wr⟩ := h_adj_exists
      let T₀ := T \ SimpleGraph.fromEdgeSet {s(w, r_B)}
      have h_bridge_wr : T.IsBridge s(w, r_B) :=
        SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.IsAcyclic hadj_wr
      have h_not_reach : ¬ T₀.Reachable w r_B :=
        (SimpleGraph.isBridge_iff.mp h_bridge_wr).2
      let A := U.filter (fun v => T₀.Reachable w v)
      let B := U \ A
      have hA_sub : A ⊆ U := Finset.filter_subset _ U
      have hU_eq : U = A ∪ B := (Finset.union_sdiff_of_subset hA_sub).symm
      have h_disj : Disjoint A B := Finset.disjoint_sdiff
      have hw_A : w ∈ A := Finset.mem_filter.mpr ⟨hw, SimpleGraph.Reachable.refl w⟩
      have hr_B : r_B ∈ B := by
        rw [Finset.mem_sdiff]
        refine ⟨hr_B_U, ?_⟩
        rw [Finset.mem_filter]
        rintro ⟨_, h_reach⟩
        exact h_not_reach h_reach
      have hJ : IsBridgeJoin T A B w r_B := by
        refine ⟨h_disj, hw_A, hr_B, hadj_wr, ?_⟩
        intro a ha b hb hab
        by_cases h_edge : s(a, b) = s(w, r_B)
        · rw [Sym2.eq_iff] at h_edge
          rcases h_edge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨rfl, rfl⟩
          · exact False.elim (Finset.disjoint_left.mp h_disj ha hr_B)
        · exfalso
          have hab₀ : T₀.Adj a b := by
            dsimp [T₀]
            rw [SimpleGraph.sdiff_adj, SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff]
            exact ⟨hab, fun ⟨h_eq, _⟩ => h_edge h_eq⟩
          have ha_reach : T₀.Reachable w a := (Finset.mem_filter.mp ha).2
          have hb_reach : T₀.Reachable w b := ha_reach.trans hab₀.reachable
          have hb_A : b ∈ A := Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hb).1, hb_reach⟩
          exact (Finset.mem_sdiff.mp hb).2 hb_A
      have hA_subtree : IsSubtree T A := by
        refine ⟨⟨w, hw_A⟩, ?_⟩
        have : Nonempty ↑(A : Set (Fin n)) := ⟨⟨w, hw_A⟩⟩
        refine ⟨?_⟩
        rintro ⟨x, hx⟩ ⟨y, hy⟩
        have hxU : x ∈ U := hA_sub hx
        have hyU : y ∈ U := hA_sub hy
        obtain ⟨q, hq_supp⟩ := exists_walk_of_isSubtree hU hxU hyU
        let p : T.Walk x y := (q.toPath : T.Walk x y)
        have hp_path : p.IsPath := q.toPath.2
        have hp_supp : ∀ z ∈ p.support, z ∈ A ∪ B := by
          intro z hz
          rw [← hU_eq]
          exact hq_supp z (q.support_toPath_subset hz)
        have hp_A : ∀ z ∈ p.support, z ∈ (A : Set (Fin n)) :=
          bridge_path_support_left hJ p hp_path hp_supp hx hy
        exact (p.induce (A : Set (Fin n)) hp_A).reachable
      have hB_subtree : IsSubtree T B := by
        refine ⟨⟨r_B, hr_B⟩, ?_⟩
        have : Nonempty ↑(B : Set (Fin n)) := ⟨⟨r_B, hr_B⟩⟩
        refine ⟨?_⟩
        rintro ⟨x, hx⟩ ⟨y, hy⟩
        have hxU : x ∈ U := Finset.sdiff_subset hx
        have hyU : y ∈ U := Finset.sdiff_subset hy
        obtain ⟨q, hq_supp⟩ := exists_walk_of_isSubtree hU hxU hyU
        let p : T.Walk x y := (q.toPath : T.Walk x y)
        have hp_path : p.IsPath := q.toPath.2
        have hp_supp : ∀ z ∈ p.support, z ∈ B ∪ A := by
          intro z hz
          rw [Finset.union_comm, ← hU_eq]
          exact hq_supp z (q.support_toPath_subset hz)
        have hp_B : ∀ z ∈ p.support, z ∈ (B : Set (Fin n)) :=
          bridge_path_support_left (isBridgeJoin_symm hJ) p hp_path hp_supp hx hy
        exact (p.induce (B : Set (Fin n)) hp_B).reachable
      exact ⟨A, B, r_B, hU_eq, hA_subtree, hB_subtree, hJ⟩
    have rooted_card_and_moment_step : ∀ (c₁ c₂ s₁ t₁ s₂ t₂ : ℕ),
        1 ≤ c₁ → c₁ ≤ s₁ → 2 * t₁ ≤ s₁ * (s₁ + 1) →
        1 ≤ c₂ → c₂ ≤ s₂ → 2 * t₂ ≤ s₂ * (s₂ + 1) →
        c₁ + c₂ ≤ s₁ * (1 + s₂) ∧
        2 * (t₁ * (1 + s₂) + s₁ * t₂) ≤ (s₁ * (1 + s₂)) * (s₁ * (1 + s₂) + 1) := by
      intro c₁ c₂ s₁ t₁ s₂ t₂ hc₁ hcs₁ ht₁ hc₂ hcs₂ ht₂
      have hs₁ : 1 ≤ s₁ := le_trans hc₁ hcs₁
      have h_mul : s₂ ≤ s₁ * s₂ := by
        simpa using Nat.mul_le_mul_right s₂ hs₁
      refine ⟨by linarith, ?_⟩
      have h1 : (2 * t₁) * (1 + s₂) ≤ (s₁ * (s₁ + 1)) * (1 + s₂) :=
        Nat.mul_le_mul_right (1 + s₂) ht₁
      have h2 : s₁ * (2 * t₂) ≤ s₁ * (s₂ * (s₂ + 1)) :=
        Nat.mul_le_mul_left s₁ ht₂
      have h_sum_le : s₁ + s₂ + 1 ≤ s₁ * (1 + s₂) + 1 := by linarith
      have h3 : (s₁ * (1 + s₂)) * (s₁ + s₂ + 1) ≤ (s₁ * (1 + s₂)) * (s₁ * (1 + s₂) + 1) :=
        Nat.mul_le_mul_left (s₁ * (1 + s₂)) h_sum_le
      calc 2 * (t₁ * (1 + s₂) + s₁ * t₂)
        _ = (2 * t₁) * (1 + s₂) + s₁ * (2 * t₂) := by ring
        _ ≤ (s₁ * (s₁ + 1)) * (1 + s₂) + s₁ * (s₂ * (s₂ + 1)) := Nat.add_le_add h1 h2
        _ = (s₁ * (1 + s₂)) * (s₁ + s₂ + 1) := by ring
        _ ≤ (s₁ * (1 + s₂)) * (s₁ * (1 + s₂) + 1) := h3
    have h_ind : ∀ (m : ℕ) (U : Finset (Fin n)) (w : Fin n),
        U.card = m → IsSubtree T U → w ∈ U →
        U.card ≤ rootedCount T U w ∧
        2 * rootedOrderSum T U w ≤ rootedCount T U w * (rootedCount T U w + 1) := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
        intro U w hm hU hw
        by_cases hle : U.card ≤ 1
        · obtain ⟨hs, ht⟩ := rooted_singleton_moments U w hw hle
          rw [hs, ht]
          omega
        · push_neg at hle
          obtain ⟨A, B, r_B, hU_eq, hA_sub, hB_sub, hJ⟩ :=
            subtree_exists_root_bridge_split U w hU hw hle
          have hc₁ : 1 ≤ A.card := Finset.card_pos.mpr ⟨w, hJ.2.1⟩
          have hc₂ : 1 ≤ B.card := Finset.card_pos.mpr ⟨r_B, hJ.2.2.1⟩
          have hU_card : U.card = A.card + B.card := by
            rw [hU_eq, Finset.card_union_of_disjoint hJ.1]
          have hA_lt : A.card < m := by omega
          have hB_lt : B.card < m := by omega
          obtain ⟨hcs₁, ht₁⟩ := ih A.card hA_lt A w rfl hA_sub hJ.2.1
          obtain ⟨hcs₂, ht₂⟩ := ih B.card hB_lt B r_B rfl hB_sub hJ.2.2.1
          obtain ⟨h_s, h_t⟩ := bridge_join_rooted_moments n T A B w r_B hJ
          rw [hU_card, hU_eq, h_s, h_t]
          exact rooted_card_and_moment_step A.card B.card
            (rootedCount T A w) (rootedOrderSum T A w)
            (rootedCount T B r_B) (rootedOrderSum T B r_B)
            hc₁ hcs₁ ht₁ hc₂ hcs₂ ht₂
    exact h_ind U₀.card U₀ r₀ rfl hU₀ hr₀
  have isSubtree_insert_leaf_iff : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (U S₀ : Finset (Fin n)) (z r : Fin n),
      z ∉ U → r ∈ U → (∀ y ∈ insert z U, G.Adj z y ↔ y = r) → S₀ ⊆ U →
      (IsSubtree G (insert z S₀) ↔ S₀ = ∅ ∨ (IsSubtree G S₀ ∧ r ∈ S₀)) := by
    intro n G U S₀ z r hz hr hadj hS₀
    have hzr : z ≠ r := fun h => hz (h ▸ hr)
    have hzS₀ : z ∉ S₀ := fun h => hz (hS₀ h)
    rcases S₀.eq_empty_or_nonempty with rfl | hS₀_ne
    · simp only [Finset.insert_empty, true_or, iff_true]
      refine ⟨Finset.singleton_nonempty z, ?_⟩
      rw [SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨⟨z, by simp⟩, fun ⟨w, hw⟩ => ?_⟩
      have hwz : w = z := by simpa using hw
      subst hwz
      exact SimpleGraph.Reachable.rfl
    · simp only [hS₀_ne.ne_empty, false_or]
      let S : Finset (Fin n) := insert z S₀
      change IsSubtree G S ↔ IsSubtree G S₀ ∧ r ∈ S₀
      constructor
      · intro hS
        have hr_mem : r ∈ S₀ := by
          obtain ⟨a, ha⟩ := hS₀_ne
          have h_walk : ∀ (u w : ↑(S : Set (Fin n))) (pw : (G.induce (S : Set (Fin n))).Walk u w),
              u.1 = z → w.1 ∈ S₀ → r ∈ S₀ := by
            intro u w pw huz hwS₀
            cases pw with
            | nil =>
              exact False.elim (hzS₀ (huz ▸ hwS₀))
            | @cons _ b _ hadj_step _ =>
              have hb_mem : b.1 ∈ insert z S₀ := b.2
              have hb_U : b.1 ∈ insert z U := Finset.insert_subset_insert z hS₀ hb_mem
              have hbr : b.1 = r := (hadj b.1 hb_U).mp (huz ▸ hadj_step)
              rcases Finset.mem_insert.mp hb_mem with hbz | hbS₀
              · exact False.elim (hzr (hbz.symm.trans hbr))
              · exact hbr ▸ hbS₀
          obtain ⟨pw⟩ := hS.2.preconnected
            ⟨z, Finset.mem_coe.mpr (Finset.mem_insert_self z S₀)⟩
            ⟨a, Finset.mem_coe.mpr (Finset.mem_insert_of_mem ha)⟩
          exact h_walk _ _ pw rfl ha
        refine ⟨⟨hS₀_ne, ?_⟩, hr_mem⟩
        rw [SimpleGraph.connected_iff_exists_forall_reachable]
        let φ : ↑(S : Set (Fin n)) → ↑(S₀ : Set (Fin n)) := fun x =>
          ⟨if x.1 = z then r else x.1, by
            by_cases hx : x.1 = z
            · simp [hx, hr_mem]
            · simp only [hx, ↓reduceIte, Finset.mem_coe]
              rcases Finset.mem_insert.mp x.2 with hxz | h
              · exact False.elim (hx hxz)
              · exact h⟩
        have hφ_mem : ∀ (a : Fin n) (ha : a ∈ S₀),
            φ ⟨a, Finset.mem_coe.mpr (Finset.mem_insert_of_mem ha)⟩ = ⟨a, ha⟩ := by
          intro a ha
          have haz : a ≠ z := fun h => hzS₀ (h ▸ ha)
          ext
          simp [φ, haz]
        have hφ_adj : ∀ x y : ↑(S : Set (Fin n)),
            (G.induce (S : Set (Fin n))).Adj x y →
            (G.induce (S₀ : Set (Fin n))).Reachable (φ x) (φ y) := by
          intro x y hxy
          change G.Adj x.1 y.1 at hxy
          by_cases hx : x.1 = z
          · have hy_U : y.1 ∈ insert z U := Finset.insert_subset_insert z hS₀ y.2
            have hyr : y.1 = r := (hadj y.1 hy_U).mp (hx ▸ hxy)
            have hφ_eq : φ x = φ y := by
              ext
              simp [φ, hx, hyr]
            rw [hφ_eq]
          · by_cases hy : y.1 = z
            · have hx_U : x.1 ∈ insert z U := Finset.insert_subset_insert z hS₀ x.2
              have hxr : x.1 = r := (hadj x.1 hx_U).mp (hy ▸ G.symm hxy)
              have hφ_eq : φ x = φ y := by
                ext
                simp [φ, hy, hxr]
              rw [hφ_eq]
            · apply SimpleGraph.Adj.reachable
              change G.Adj (φ x).1 (φ y).1
              simp [φ, hx, hy, hxy]
        have hφ_walk : ∀ (x y : ↑(S : Set (Fin n)))
            (pw : (G.induce (S : Set (Fin n))).Walk x y),
            (G.induce (S₀ : Set (Fin n))).Reachable (φ x) (φ y) := by
          intro x y pw
          induction pw with
          | nil => exact SimpleGraph.Reachable.rfl
          | cons h_step _ ih => exact (hφ_adj _ _ h_step).trans ih
        refine ⟨⟨r, hr_mem⟩, fun ⟨b, hb⟩ => ?_⟩
        obtain ⟨pw⟩ := hS.2.preconnected
          ⟨r, Finset.mem_coe.mpr (Finset.mem_insert_of_mem hr_mem)⟩
          ⟨b, Finset.mem_coe.mpr (Finset.mem_insert_of_mem hb)⟩
        have h_reach := hφ_walk _ _ pw
        rwa [hφ_mem r hr_mem, hφ_mem b hb] at h_reach
      · rintro ⟨hS₀_sub, hr_mem⟩
        refine ⟨Finset.insert_nonempty z S₀, ?_⟩
        rw [SimpleGraph.connected_iff_exists_forall_reachable]
        let ι : ↑(S₀ : Set (Fin n)) → ↑(S : Set (Fin n)) :=
          fun x => ⟨x.1, Finset.mem_coe.mpr (Finset.mem_insert_of_mem x.2)⟩
        have hι_walk : ∀ (x y : ↑(S₀ : Set (Fin n))) (pw : (G.induce (S₀ : Set (Fin n))).Walk x y),
            (G.induce (S : Set (Fin n))).Reachable (ι x) (ι y) := by
          intro x y pw
          induction pw with
          | nil => exact SimpleGraph.Reachable.rfl
          | cons h_step _ ih =>
            have h_step' : (G.induce (S : Set (Fin n))).Adj (ι _) (ι _) := h_step
            exact h_step'.reachable.trans ih
        refine ⟨ι ⟨r, hr_mem⟩, fun ⟨b, hb⟩ => ?_⟩
        rcases Finset.mem_insert.mp hb with hbz | hbS₀
        · subst b
          apply SimpleGraph.Adj.reachable
          change G.Adj r z
          exact G.symm ((hadj r (Finset.mem_insert_of_mem hr)).mpr rfl)
        · obtain ⟨pw⟩ := hS₀_sub.2.preconnected ⟨r, hr_mem⟩ ⟨b, hbS₀⟩
          exact hι_walk _ _ pw
  have leaf_ext_moments_Q : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) (z r : Fin n),
      z ∉ U → r ∈ U → (∀ y ∈ insert z U, G.Adj z y ↔ y = r) →
      (rootedCount G (insert z U) z : ℚ) = (rootedCount G U r : ℚ) + 1 ∧
      (rootedOrderSum G (insert z U) z : ℚ) =
        (rootedOrderSum G U r : ℚ) + (rootedCount G U r : ℚ) + 1 ∧
      ((subtreesIn G (insert z U)).card : ℚ) =
        ((subtreesIn G U).card : ℚ) + (rootedCount G U r : ℚ) + 1 ∧
      ((∑ S ∈ subtreesIn G (insert z U), S.card : ℕ) : ℚ) =
        ((∑ S ∈ subtreesIn G U, S.card : ℕ) : ℚ) +
        (rootedOrderSum G U r : ℚ) + (rootedCount G U r : ℚ) + 1 ∧
      (rootedCount G (insert z U) r : ℚ) = 2 * (rootedCount G U r : ℚ) ∧
      (rootedOrderSum G (insert z U) r : ℚ) =
        2 * (rootedOrderSum G U r : ℚ) + (rootedCount G U r : ℚ) := by
    intro n G U z r hz hr hadj
    have h_ext : ∀ S₀ ⊆ U, IsSubtree G (insert z S₀) ↔ S₀ = ∅ ∨ (IsSubtree G S₀ ∧ r ∈ S₀) :=
      fun S₀ hS₀ => isSubtree_insert_leaf_iff G U S₀ z r hz hr hadj hS₀
    have hzr : z ≠ r := fun h => hz (h ▸ hr)
    have h_mem_rooted : ∀ W r' S, S ∈ rootedSubtreesIn G W r' ↔ IsSubtree G S ∧ S ⊆ W ∧ r' ∈ S := by
      intro W r' S
      simp [rootedSubtreesIn, subtrees]
    have h_mem_subtreesIn : ∀ W S, S ∈ subtreesIn G W ↔ IsSubtree G S ∧ S ⊆ W := by
      intro W S
      simp [subtreesIn, subtrees]
    have h_rooted_z : rootedSubtreesIn G (insert z U) z =
        insert ({z} : Finset (Fin n)) ((rootedSubtreesIn G U r).image (insert z)) := by
      ext S
      simp only [Finset.mem_insert, Finset.mem_image, h_mem_rooted]
      constructor
      · rintro ⟨hS_sub, hS_U, hzS⟩
        let S₀ := S.erase z
        have hS₀_U : S₀ ⊆ U := by
          intro w hw
          rcases Finset.mem_insert.mp (hS_U (Finset.mem_of_mem_erase hw)) with rfl | hwU
          · exact False.elim ((Finset.mem_erase.mp hw).1 rfl)
          · exact hwU
        have h_ins : insert z S₀ = S := Finset.insert_erase hzS
        have hS_iff := (h_ext S₀ hS₀_U).mp (h_ins.symm ▸ hS_sub)
        rcases hS_iff with h_emp | ⟨hS₀_tree, hrS₀⟩
        · left
          rw [← h_ins, h_emp, Finset.insert_empty]
        · right
          exact ⟨S₀, ⟨hS₀_tree, hS₀_U, hrS₀⟩, h_ins⟩
      · rintro (rfl | ⟨S₀, ⟨hS₀_tree, hS₀_U, hrS₀⟩, rfl⟩)
        · have h_emp : IsSubtree G (insert z ∅) := (h_ext ∅ (Finset.empty_subset U)).mpr (Or.inl rfl)
          simpa using h_emp
        · refine ⟨(h_ext S₀ hS₀_U).mpr (Or.inr ⟨hS₀_tree, hrS₀⟩),
            Finset.insert_subset_insert z hS₀_U, Finset.mem_insert_self z S₀⟩
    have h_notMem_img : ({z} : Finset (Fin n)) ∉ (rootedSubtreesIn G U r).image (insert z) := by
      simp only [Finset.mem_image, not_exists, not_and]
      intro S₀ hS₀ h_eq
      have hrS₀ : r ∈ S₀ := ((h_mem_rooted U r S₀).mp hS₀).2.2
      have hrz : r ∈ ({z} : Finset (Fin n)) := h_eq ▸ Finset.mem_insert_of_mem hrS₀
      exact hzr (Finset.mem_singleton.mp hrz).symm
    have h_inj : Set.InjOn (insert z) (rootedSubtreesIn G U r : Set (Finset (Fin n))) := by
      intro S₁ hS₁ S₂ hS₂ h_eq
      have hz₁ : z ∉ S₁ := fun h => hz (((h_mem_rooted U r S₁).mp hS₁).2.1 h)
      have hz₂ : z ∉ S₂ := fun h => hz (((h_mem_rooted U r S₂).mp hS₂).2.1 h)
      have := congrArg (fun S : Finset (Fin n) => S.erase z) h_eq
      simpa [Finset.erase_insert hz₁, Finset.erase_insert hz₂] using this
    have h_rc_z : rootedCount G (insert z U) z = rootedCount G U r + 1 := by
      change (rootedSubtreesIn G (insert z U) z).card = (rootedSubtreesIn G U r).card + 1
      rw [h_rooted_z, Finset.card_insert_of_notMem h_notMem_img, Finset.card_image_of_injOn h_inj]
    have h_sum_img : ∑ S ∈ (rootedSubtreesIn G U r).image (insert z), S.card =
        rootedOrderSum G U r + rootedCount G U r := by
      rw [Finset.sum_image h_inj]
      have h_congr : ∑ S₀ ∈ rootedSubtreesIn G U r, (insert z S₀).card =
          ∑ S₀ ∈ rootedSubtreesIn G U r, (S₀.card + 1) := by
        refine Finset.sum_congr rfl (fun S₀ hS₀ => ?_)
        have hzS₀ : z ∉ S₀ := fun h => hz (((h_mem_rooted U r S₀).mp hS₀).2.1 h)
        exact Finset.card_insert_of_notMem hzS₀
      rw [h_congr, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
      rfl
    have h_ros_z : rootedOrderSum G (insert z U) z =
        rootedOrderSum G U r + rootedCount G U r + 1 := by
      change ∑ S ∈ rootedSubtreesIn G (insert z U) z, S.card =
        rootedOrderSum G U r + rootedCount G U r + 1
      rw [h_rooted_z, Finset.sum_insert h_notMem_img, Finset.card_singleton, h_sum_img]
      omega
    have h_subtrees_union : subtreesIn G (insert z U) =
        subtreesIn G U ∪ rootedSubtreesIn G (insert z U) z := by
      ext S
      simp only [Finset.mem_union, h_mem_subtreesIn, h_mem_rooted]
      constructor
      · rintro ⟨hS_tree, hS_sub⟩
        by_cases hzS : z ∈ S
        · exact Or.inr ⟨hS_tree, hS_sub, hzS⟩
        · left
          refine ⟨hS_tree, fun w hw => ?_⟩
          rcases Finset.mem_insert.mp (hS_sub hw) with rfl | hwU
          · exact False.elim (hzS hw)
          · exact hwU
      · rintro (⟨hS_tree, hS_U⟩ | ⟨hS_tree, hS_sub, _⟩)
        · exact ⟨hS_tree, Finset.Subset.trans hS_U (Finset.subset_insert z U)⟩
        · exact ⟨hS_tree, hS_sub⟩
    have h_subtrees_disj : Disjoint (subtreesIn G U) (rootedSubtreesIn G (insert z U) z) := by
      rw [Finset.disjoint_left]
      intro S hS₁ hS₂
      have hS_U : S ⊆ U := ((h_mem_subtreesIn U S).mp hS₁).2
      exact hz (hS_U ((h_mem_rooted (insert z U) z S).mp hS₂).2.2)
    have h_sc_z : (subtreesIn G (insert z U)).card =
        (subtreesIn G U).card + rootedCount G U r + 1 := by
      rw [h_subtrees_union, Finset.card_union_of_disjoint h_subtrees_disj]
      change (subtreesIn G U).card + rootedCount G (insert z U) z = _
      rw [h_rc_z]
      omega
    have h_sos_z : (∑ S ∈ subtreesIn G (insert z U), S.card) =
        (∑ S ∈ subtreesIn G U, S.card) + rootedOrderSum G U r + rootedCount G U r + 1 := by
      rw [h_subtrees_union, Finset.sum_union h_subtrees_disj]
      change (∑ S ∈ subtreesIn G U, S.card) + rootedOrderSum G (insert z U) z = _
      rw [h_ros_z]
      omega
    have h_rooted_r : rootedSubtreesIn G (insert z U) r =
        rootedSubtreesIn G U r ∪ (rootedSubtreesIn G U r).image (insert z) := by
      ext S
      simp only [Finset.mem_union, Finset.mem_image, h_mem_rooted]
      constructor
      · rintro ⟨hS_tree, hS_sub, hrS⟩
        by_cases hzS : z ∈ S
        · right
          let S₀ := S.erase z
          have hS₀_U : S₀ ⊆ U := by
            intro w hw
            rcases Finset.mem_insert.mp (hS_sub (Finset.mem_of_mem_erase hw)) with rfl | hwU
            · exact False.elim ((Finset.mem_erase.mp hw).1 rfl)
            · exact hwU
          have h_ins : insert z S₀ = S := Finset.insert_erase hzS
          have hrS₀ : r ∈ S₀ := Finset.mem_erase.mpr ⟨hzr.symm, hrS⟩
          have hS_iff := (h_ext S₀ hS₀_U).mp (h_ins.symm ▸ hS_tree)
          rcases hS_iff with h_emp | ⟨hS₀_tree, _⟩
          · simp [h_emp] at hrS₀
          · exact ⟨S₀, ⟨hS₀_tree, hS₀_U, hrS₀⟩, h_ins⟩
        · left
          refine ⟨hS_tree, fun w hw => ?_, hrS⟩
          rcases Finset.mem_insert.mp (hS_sub hw) with rfl | hwU
          · exact False.elim (hzS hw)
          · exact hwU
      · rintro (⟨hS_tree, hS_U, hrS⟩ | ⟨S₀, ⟨hS₀_tree, hS₀_U, hrS₀⟩, rfl⟩)
        · exact ⟨hS_tree, Finset.Subset.trans hS_U (Finset.subset_insert z U), hrS⟩
        · exact ⟨(h_ext S₀ hS₀_U).mpr (Or.inr ⟨hS₀_tree, hrS₀⟩),
            Finset.insert_subset_insert z hS₀_U, Finset.mem_insert_of_mem hrS₀⟩
    have h_rooted_r_disj : Disjoint (rootedSubtreesIn G U r)
        ((rootedSubtreesIn G U r).image (insert z)) := by
      rw [Finset.disjoint_left]
      intro S hS₁ hS₂
      have hS_U : S ⊆ U := ((h_mem_rooted U r S).mp hS₁).2.1
      rcases Finset.mem_image.mp hS₂ with ⟨S₀, _, rfl⟩
      exact hz (hS_U (Finset.mem_insert_self z S₀))
    have h_rc_r : rootedCount G (insert z U) r = 2 * rootedCount G U r := by
      change (rootedSubtreesIn G (insert z U) r).card = 2 * (rootedSubtreesIn G U r).card
      rw [h_rooted_r, Finset.card_union_of_disjoint h_rooted_r_disj, Finset.card_image_of_injOn h_inj]
      omega
    have h_ros_r : rootedOrderSum G (insert z U) r =
        2 * rootedOrderSum G U r + rootedCount G U r := by
      change ∑ S ∈ rootedSubtreesIn G (insert z U) r, S.card =
        2 * rootedOrderSum G U r + rootedCount G U r
      rw [h_rooted_r, Finset.sum_union h_rooted_r_disj, h_sum_img]
      change rootedOrderSum G U r + (rootedOrderSum G U r + rootedCount G U r) = _
      omega
    refine ⟨by exact_mod_cast h_rc_z, by exact_mod_cast h_ros_z, by exact_mod_cast h_sc_z,
      by exact_mod_cast h_sos_z, by exact_mod_cast h_rc_r, by exact_mod_cast h_ros_r⟩
  have leaf_packet_union_moments : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (U L : Finset (Fin n)) (r : Fin n),
      r ∈ U → Disjoint U L → IsLeafPacket G L r →
      (rootedCount G (U ∪ L) r : ℚ) = (2 : ℚ) ^ L.card * (rootedCount G U r : ℚ) ∧
      (rootedOrderSum G (U ∪ L) r : ℚ) =
        (2 : ℚ) ^ L.card * (rootedOrderSum G U r : ℚ) +
        (L.card : ℚ) * (2 : ℚ) ^ L.card / 2 * (rootedCount G U r : ℚ) ∧
      ((subtreesIn G (U ∪ L)).card : ℚ) =
        ((subtreesIn G U).card : ℚ) + (L.card : ℚ) +
        ((2 : ℚ) ^ L.card - 1) * (rootedCount G U r : ℚ) ∧
      ((∑ S ∈ subtreesIn G (U ∪ L), S.card : ℕ) : ℚ) =
        ((∑ S ∈ subtreesIn G U, S.card : ℕ) : ℚ) + (L.card : ℚ) +
        ((2 : ℚ) ^ L.card - 1) * (rootedOrderSum G U r : ℚ) +
        (L.card : ℚ) * (2 : ℚ) ^ L.card / 2 * (rootedCount G U r : ℚ) := by
    intro n G U L r hrU
    induction L using Finset.induction_on with
    | empty =>
      intro _ _
      simp only [Finset.union_empty, Finset.card_empty, Nat.cast_zero, pow_zero]
      exact ⟨by ring, by ring, by ring, by ring⟩
    | @insert x L₀ hx_L₀ ih =>
      intro hdisj hpkt
      have hx_U : x ∉ U := (Finset.disjoint_insert_right.mp hdisj).1
      have hdisj₀ : Disjoint U L₀ := (Finset.disjoint_insert_right.mp hdisj).2
      have hx_leaf : IsLeafIn G x r := hpkt x (Finset.mem_insert_self x L₀)
      have hpkt₀ : IsLeafPacket G L₀ r := fun y hy => hpkt y (Finset.mem_insert_of_mem hy)
      obtain ⟨ih_s, ih_t, ih_N, ih_R⟩ := ih hdisj₀ hpkt₀
      let U' := U ∪ L₀
      have hU_ins : U ∪ insert x L₀ = insert x U' := Finset.union_insert x U L₀
      have hx_U' : x ∉ U' := Finset.notMem_union.mpr ⟨hx_U, hx_L₀⟩
      have hr_U' : r ∈ U' := Finset.mem_union_left L₀ hrU
      have hadj_x : ∀ y ∈ insert x U', G.Adj x y ↔ y = r := fun y _ => hx_leaf y
      obtain ⟨_, _, h_N, h_R, h_s, h_t⟩ := leaf_ext_moments_Q G U' x r hx_U' hr_U' hadj_x
      have hcard : ((insert x L₀).card : ℚ) = (L₀.card : ℚ) + 1 := by
        rw [Finset.card_insert_of_notMem hx_L₀, Nat.cast_add, Nat.cast_one]
      have hpow : (2 : ℚ) ^ (insert x L₀).card = (2 : ℚ) ^ L₀.card * 2 := by
        rw [Finset.card_insert_of_notMem hx_L₀, pow_succ]
      rw [hU_ins, hcard, hpow]
      change (rootedCount G (insert x U') r : ℚ) = _ ∧
        (rootedOrderSum G (insert x U') r : ℚ) = _ ∧
        ((subtreesIn G (insert x U')).card : ℚ) = _ ∧
        ((∑ S ∈ subtreesIn G (insert x U'), S.card : ℕ) : ℚ) = _
      rw [h_s, h_t, h_N, h_R]
      dsimp [U'] at ih_s ih_t ih_N ih_R ⊢
      rw [ih_s, ih_t, ih_N, ih_R]
      exact ⟨by ring, by ring, by ring, by ring⟩
  have double_broom_suffix_moments : ∀ (n m p q : ℕ) (G : SimpleGraph (Fin n))
      (H L_p L_q : Finset (Fin n)) (w₀ : Fin n) (v : Fin (m + 1) → Fin n),
      G.IsTree → IsDoubleBroomSuffix G m p q H L_p L_q w₀ v →
      (subtreeCount G : ℚ) =
        doubleBroomCount (subtreesIn G H).card (rootedCount G H w₀) m p q ∧
      (subtreeOrderSum G : ℚ) =
        doubleBroomOrderSum (∑ S ∈ subtreesIn G H, S.card) (rootedCount G H w₀)
          (rootedOrderSum G H w₀) m p q := by
    intro n m p q G H L_p L_q w₀ v _hG hDB
    rcases hDB with ⟨h_inj, _hSub_H, hcard_p, hcard_q, hdisj_Hv, hdisj_Hp, hdisj_Hq,
      hdisj_vp, hdisj_vq, hdisj_pq, h_univ, h_bridge, h_spine, h_pkt_p, h_pkt_q⟩
    have hv_mem_img : ∀ i : Fin (m + 1), v i ∈ Finset.univ.image v :=
      fun i => Finset.mem_image_of_mem v (Finset.mem_univ i)
    have hv_mem_D : ∀ i : Fin (m + 1), v i ∈ (Finset.univ.image v) ∪ L_p ∪ L_q :=
      fun i => Finset.mem_union_left _ (Finset.mem_union_left _ (hv_mem_img i))
    let U₀ : Finset (Fin n) := insert (v 0) H
    have hv0_notMem_H : v 0 ∉ H := Finset.disjoint_right.mp hdisj_Hv (hv_mem_img 0)
    have hw0_mem_H : w₀ ∈ H := h_bridge.2.1
    have hadj_v0 : ∀ y ∈ insert (v 0) H, G.Adj (v 0) y ↔ y = w₀ := by
      intro y hy
      constructor
      · intro hadj
        have hy_ne : y ≠ v 0 := fun h => G.loopless (v 0) (h ▸ hadj)
        have hy_H : y ∈ H := by
          rcases Finset.mem_insert.mp hy with rfl | h
          · exact False.elim (hy_ne rfl)
          · exact h
        exact (h_bridge.2.2.2.2 y hy_H (v 0) (hv_mem_D 0) (G.symm hadj)).1
      · rintro rfl
        exact G.symm h_bridge.2.2.2.1
    obtain ⟨hU0_s, hU0_t, hU0_N, hU0_R, _, _⟩ :=
      leaf_ext_moments_Q G H (v 0) w₀ hv0_notMem_H hw0_mem_H hadj_v0
    let W₀ : Finset (Fin n) := U₀ ∪ L_p
    have hv0_mem_U0 : v 0 ∈ U₀ := Finset.mem_insert_self (v 0) H
    have hdisj_U0_Lp : Disjoint U₀ L_p :=
      Finset.disjoint_insert_left.mpr
        ⟨Finset.disjoint_left.mp hdisj_vp (hv_mem_img 0), hdisj_Hp⟩
    obtain ⟨hW0_s, hW0_t, hW0_N, hW0_R⟩ :=
      leaf_packet_union_moments G U₀ L_p (v 0) hv0_mem_U0 hdisj_U0_Lp h_pkt_p
    rw [hcard_p] at hW0_s hW0_t hW0_N hW0_R
    let W : ℕ → Finset (Fin n) := fun k =>
      H ∪ L_p ∪ (Finset.univ.filter (fun i : Fin (m + 1) => i.val ≤ k)).image v
    let s₀ : ℚ := rootedCount G W₀ (v 0)
    let t₀ : ℚ := rootedOrderSum G W₀ (v 0)
    let N₀ : ℚ := (subtreesIn G W₀).card
    let R₀ : ℚ := ((∑ S ∈ subtreesIn G W₀, S.card : ℕ) : ℚ)
    have h_spine_ind : ∀ (k : ℕ) (hk : k ≤ m),
        let v_k := v ⟨k, Nat.lt_succ_of_le hk⟩
        (rootedCount G (W k) v_k : ℚ) = s₀ + (k : ℚ) ∧
        (rootedOrderSum G (W k) v_k : ℚ) =
          t₀ + (k : ℚ) * s₀ + (k : ℚ) * ((k : ℚ) + 1) / 2 ∧
        ((subtreesIn G (W k)).card : ℚ) =
          N₀ + (k : ℚ) * s₀ + (k : ℚ) * ((k : ℚ) + 1) / 2 ∧
        ((∑ S ∈ subtreesIn G (W k), S.card : ℕ) : ℚ) =
          R₀ + (k : ℚ) * t₀ + (k : ℚ) * ((k : ℚ) + 1) / 2 * s₀ +
          (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) / 6 := by
      intro k
      induction k with
      | zero =>
        intro hk
        have h_flt0 : Finset.univ.filter (fun i : Fin (m + 1) => i.val ≤ 0) = {0} := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro hi
            exact Fin.ext (by change i.val ≤ 0 at hi; change i.val = 0; omega)
          · rintro rfl
            exact le_rfl
        have hW0_eq : W 0 = W₀ := by
          dsimp [W, W₀, U₀]
          rw [h_flt0, Finset.image_singleton]
          ext x
          simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
          tauto
        have hv0_eq : v ⟨0, Nat.lt_succ_of_le hk⟩ = v 0 := rfl
        dsimp only
        rw [hW0_eq, hv0_eq, Nat.cast_zero]
        change s₀ = _ ∧ t₀ = _ ∧ N₀ = _ ∧ R₀ = _
        exact ⟨by ring, by ring, by ring, by ring⟩
      | succ k ih =>
        intro hk1
        have hk : k ≤ m := Nat.le_of_succ_le hk1
        obtain ⟨ih_s, ih_t, ih_N, ih_R⟩ := ih hk
        let i_k : Fin (m + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
        let i_k1 : Fin (m + 1) := ⟨k + 1, Nat.lt_succ_of_le hk1⟩
        have h_flt_succ : Finset.univ.filter (fun i : Fin (m + 1) => i.val ≤ k + 1) =
            insert i_k1 (Finset.univ.filter (fun i : Fin (m + 1) => i.val ≤ k)) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · intro hi
            by_cases hik : i.val = k + 1
            · left; exact Fin.ext hik
            · right; omega
          · rintro (rfl | hi)
            · exact le_rfl
            · omega
        have hW_succ : W (k + 1) = insert (v i_k1) (W k) := by
          dsimp [W]
          rw [h_flt_succ, Finset.image_insert]
          ext x
          simp only [Finset.mem_union, Finset.mem_insert]
          tauto
        have hv_notMem_Wk : v i_k1 ∉ W k := by
          intro h_mem
          dsimp [W] at h_mem
          rcases Finset.mem_union.mp h_mem with h_HLp | h_img
          · rcases Finset.mem_union.mp h_HLp with h_H | h_Lp
            · exact Finset.disjoint_right.mp hdisj_Hv (hv_mem_img i_k1) h_H
            · exact Finset.disjoint_left.mp hdisj_vp (hv_mem_img i_k1) h_Lp
          · rcases Finset.mem_image.mp h_img with ⟨i, hi_flt, hvi⟩
            have hi_le : i.val ≤ k := (Finset.mem_filter.mp hi_flt).2
            have hi_eq : i = i_k1 := h_inj hvi
            have : i.val = k + 1 := congrArg Fin.val hi_eq
            omega
        have hvk_mem_Wk : v i_k ∈ W k := by
          dsimp [W]
          refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i_k, ?_, rfl⟩)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩
        have hadj_vk1 : ∀ y ∈ insert (v i_k1) (W k), G.Adj (v i_k1) y ↔ y = v i_k := by
          intro y hy_ins
          constructor
          · intro hadj
            have hy_ne : y ≠ v i_k1 := fun h => G.loopless _ (h ▸ hadj)
            have hy_Wk : y ∈ W k := by
              rcases Finset.mem_insert.mp hy_ins with rfl | h
              · exact False.elim (hy_ne rfl)
              · exact h
            dsimp [W] at hy_Wk
            rcases Finset.mem_union.mp hy_Wk with h_HLp | h_img
            · rcases Finset.mem_union.mp h_HLp with h_H | h_Lp
              · have h_br := h_bridge.2.2.2.2 y h_H (v i_k1) (hv_mem_D i_k1) (G.symm hadj)
                have hi0 : i_k1 = 0 := h_inj h_br.2
                have : k + 1 = 0 := congrArg Fin.val hi0
                omega
              · have hv_eq : v i_k1 = v 0 := (h_pkt_p y h_Lp (v i_k1)).mp (G.symm hadj)
                have hi0 : i_k1 = 0 := h_inj hv_eq
                have : k + 1 = 0 := congrArg Fin.val hi0
                omega
            · rcases Finset.mem_image.mp h_img with ⟨i, hi_flt, rfl⟩
              have hi_le : i.val ≤ k := (Finset.mem_filter.mp hi_flt).2
              have h_sp := (h_spine i_k1 i).mp hadj
              have hi_eq : i.val = k := by
                change (k + 1) + 1 = i.val ∨ i.val + 1 = k + 1 at h_sp
                omega
              congr 1
              exact Fin.ext hi_eq
          · rintro rfl
            exact (h_spine i_k1 i_k).mpr (Or.inr rfl)
        obtain ⟨h_s, h_t, h_N, h_R, _, _⟩ :=
          leaf_ext_moments_Q G (W k) (v i_k1) (v i_k) hv_notMem_Wk hvk_mem_Wk hadj_vk1
        dsimp only
        rw [hW_succ]
        change (rootedCount G (insert (v i_k1) (W k)) (v i_k1) : ℚ) = _ ∧
          (rootedOrderSum G (insert (v i_k1) (W k)) (v i_k1) : ℚ) = _ ∧
          ((subtreesIn G (insert (v i_k1) (W k))).card : ℚ) = _ ∧
          ((∑ S ∈ subtreesIn G (insert (v i_k1) (W k)), S.card : ℕ) : ℚ) = _
        rw [h_s, h_t, h_N, h_R]
        dsimp [i_k] at ih_s ih_t ih_N ih_R ⊢
        rw [ih_s, ih_t, ih_N, ih_R, Nat.cast_add, Nat.cast_one]
        exact ⟨by ring, by ring, by ring, by ring⟩
    obtain ⟨hWm_s, hWm_t, hWm_N, hWm_R⟩ := h_spine_ind m le_rfl
    let W_m : Finset (Fin n) := H ∪ (Finset.univ.image v) ∪ L_p
    have hWm_eq : W m = W_m := by
      have h_flt_m : Finset.univ.filter (fun i : Fin (m + 1) => i.val ≤ m) = Finset.univ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact Nat.le_of_lt_succ i.isLt
      dsimp [W, W_m]
      rw [h_flt_m]
      ext x
      simp only [Finset.mem_union]
      tauto
    have hvm_eq : v ⟨m, Nat.lt_succ_of_le le_rfl⟩ = v (Fin.last m) := rfl
    rw [hWm_eq, hvm_eq] at hWm_s hWm_t
    rw [hWm_eq] at hWm_N hWm_R
    have hvm_mem_Wm : v (Fin.last m) ∈ W_m :=
      Finset.mem_union_left _ (Finset.mem_union_right _ (hv_mem_img (Fin.last m)))
    have hdisj_Wm_Lq : Disjoint W_m L_q :=
      Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_union_left.mpr ⟨hdisj_Hq, hdisj_vq⟩, hdisj_pq⟩
    obtain ⟨_, _, hUniv_N, hUniv_R⟩ :=
      leaf_packet_union_moments G W_m L_q (v (Fin.last m)) hvm_mem_Wm hdisj_Wm_Lq h_pkt_q
    have hWm_Lq : W_m ∪ L_q = Finset.univ := h_univ
    have h_subtrees_univ : subtreesIn G Finset.univ = subtrees G := by
      ext S
      simp [subtreesIn]
    rw [hWm_Lq, h_subtrees_univ, hcard_q] at hUniv_N hUniv_R
    change ((subtrees G).card : ℚ) = _ ∧ ((∑ S ∈ subtrees G, S.card : ℕ) : ℚ) = _
    rw [hUniv_N, hUniv_R, hWm_N, hWm_R, hWm_s, hWm_t]
    dsimp [s₀, t₀, N₀, R₀, doubleBroomCount, doubleBroomOrderSum]
    rw [hW0_N, hW0_R, hW0_s, hW0_t, hU0_N, hU0_R, hU0_s, hU0_t]
    exact ⟨by ring, by ring⟩
  have h_reattachLeaf_isTree : ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (x u w : V) (hxw : x ≠ w),
      G.IsTree → IsLeafIn G x u → (reattachLeaf G x w hxw).IsTree := by
    intro V _ G x u w hxw hG hx
    classical
    have hG_conn : G.Connected := hG.isConnected
    have hG_acyc : G.IsAcyclic := hG.IsAcyclic
    have h_leaf_avoid : ∀ {H : SimpleGraph V} {x₀ u₀ : V}, IsLeafIn H x₀ u₀ →
        ∀ {a b : V} (p : H.Walk a b), p.IsPath → a ≠ x₀ → b ≠ x₀ → x₀ ∉ p.support := by
      intro H x₀ u₀ hx₀ a b p
      induction p with
      | nil =>
        intro _ ha _ hmem
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hmem
        exact ha hmem.symm
      | @cons a c b hac q ih =>
        intro hp ha hb
        rw [SimpleGraph.Walk.cons_isPath_iff] at hp
        rcases hp with ⟨hq, ha_not_mem⟩
        have hc : c ≠ x₀ := by
          intro hcx
          subst hcx
          cases q with
          | nil => exact hb rfl
          | @cons _ d _ hxd q' =>
            have ha_eq : a = u₀ := (hx₀ a).mp (H.symm hac)
            have hd_eq : d = u₀ := (hx₀ d).mp hxd
            have had : a = d := ha_eq.trans hd_eq.symm
            apply ha_not_mem
            rw [SimpleGraph.Walk.support_cons, had]
            exact List.mem_cons_of_mem _ q'.start_mem_support
        have hx_not_q : x₀ ∉ q.support := ih hq hc hb
        rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
        exact ⟨ha.symm, hx_not_q⟩
    have h_reach_transfer : ∀ {a b : V} (p : G.Walk a b),
        x ∉ p.support → (reattachLeaf G x w hxw).Reachable a b := by
      intro a b p
      induction p with
      | nil =>
        intro _
        exact SimpleGraph.Reachable.refl _
      | @cons a c b hac q ih =>
        intro h_not_mem
        rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at h_not_mem
        rcases h_not_mem with ⟨hxa, hx_not_q⟩
        have ha : a ≠ x := Ne.symm hxa
        have hc : c ≠ x := by
          intro hcx
          apply hx_not_q
          rw [← hcx]
          exact q.start_mem_support
        have hadj : (reattachLeaf G x w hxw).Adj a c := Or.inl ⟨ha, hc, hac⟩
        exact hadj.reachable.trans (ih hx_not_q)
    have h_conn : (reattachLeaf G x w hxw).Connected := by
      rw [SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨w, fun a => ?_⟩
      by_cases hax : a = x
      · rw [hax]
        have hadj : (reattachLeaf G x w hxw).Adj w x := Or.inr (Or.inr ⟨rfl, rfl⟩)
        exact hadj.reachable
      · obtain ⟨p, hp⟩ := (hG_conn.preconnected w a).exists_isPath
        have hx_not_p : x ∉ p.support := h_leaf_avoid hx p hp hxw.symm hax
        exact h_reach_transfer p hx_not_p
    let G' := reattachLeaf G x w hxw
    have h_leaf_G' : IsLeafIn G' x w := by
      intro v
      constructor
      · intro hadj
        rcases hadj with ⟨hxx, _, _⟩ | ⟨_, rfl⟩ | ⟨hxw_eq, _⟩
        · exact False.elim (hxx rfl)
        · rfl
        · exact False.elim (hxw hxw_eq)
      · intro hvw
        subst hvw
        exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    have h_edge_mem : ∀ {a b : V} (q : G'.Walk a b),
        a ≠ x → b = x → s(x, w) ∈ q.edges := by
      intro a b q
      induction q with
      | nil =>
        intro ha hb
        exact False.elim (ha hb)
      | @cons a c b hac q' ih =>
        intro ha hb
        by_cases hcx : c = x
        · subst hcx
          have haw : a = w := (h_leaf_G' a).mp (G'.symm hac)
          subst haw
          rw [SimpleGraph.Walk.edges_cons, Sym2.eq_swap]
          exact List.mem_cons_self
        · rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ (ih hcx hb)
    have h_acyc : G'.IsAcyclic := by
      intro v c hc
      have hx_not_c : x ∉ c.support := by
        cases c with
        | nil => exact False.elim hc.not_of_nil
        | @cons _ y _ hvy p =>
          have h_cons := (SimpleGraph.Walk.cons_isCycle_iff p hvy).mp hc
          rcases h_cons with ⟨hp, h_no_edge⟩
          by_cases hvx : v = x
          · subst v
            have hyw : y = w := (h_leaf_G' y).mp hvy
            subst y
            have h_in : s(x, w) ∈ p.edges := h_edge_mem p hxw.symm rfl
            exact False.elim (h_no_edge h_in)
          · by_cases hyx : y = x
            · subst y
              have hvw : v = w := (h_leaf_G' v).mp (G'.symm hvy)
              cases p with
              | nil => exact False.elim (hvx rfl)
              | @cons _ z _ hxz p' =>
                have hzv : z = v := ((h_leaf_G' z).mp hxz).trans hvw.symm
                subst z
                apply False.elim (h_no_edge _)
                rw [SimpleGraph.Walk.edges_cons, Sym2.eq_swap]
                exact List.mem_cons_self
            · have hx_not_p : x ∉ p.support := h_leaf_avoid h_leaf_G' p hp hyx hvx
              rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
              exact ⟨Ne.symm hvx, hx_not_p⟩
      have h_edges : ∀ e ∈ c.edges, e ∈ G.edgeSet := by
        intro e
        refine Sym2.ind (fun a b he => ?_) e
        have ha_mem : a ∈ c.support := c.fst_mem_support_of_mem_edges he
        have hb_mem : b ∈ c.support := c.snd_mem_support_of_mem_edges he
        have ha_ne : a ≠ x := fun h => hx_not_c (h ▸ ha_mem)
        have hb_ne : b ≠ x := fun h => hx_not_c (h ▸ hb_mem)
        have hadj' : G'.Adj a b := c.adj_of_mem_edges he
        rw [SimpleGraph.mem_edgeSet]
        rcases hadj' with ⟨_, _, hab⟩ | ⟨hax, _⟩ | ⟨_, hbx⟩
        · exact hab
        · exact False.elim (ha_ne hax)
        · exact False.elim (hb_ne hbx)
      exact hG_acyc (c.transfer G h_edges) (hc.transfer h_edges)
    exact ⟨h_conn, h_acyc⟩
  have h_relocatePacket_isTree : ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (S : Finset V) (u w : V) (hu : u ∉ S) (hw : w ∉ S),
      G.IsTree → IsLeafPacket G S u → (relocatePacket G S w hw).IsTree := by
    intro V _ _ G S u w hu hw hG hleaf
    induction S using Finset.induction_on with
    | empty =>
      have h_emp : relocatePacket G ∅ w hw = G := by
        ext a b
        simp [relocatePacket]
      rw [h_emp]
      exact hG
    | @insert x S hxS ih =>
      have hux : u ≠ x := fun h => hu (h ▸ Finset.mem_insert_self x S)
      have huS : u ∉ S := fun h => hu (Finset.mem_insert_of_mem h)
      have hxw : x ≠ w := fun h => hw (h ▸ Finset.mem_insert_self x S)
      have hwS : w ∉ S := fun h => hw (Finset.mem_insert_of_mem h)
      have hx_leaf : IsLeafIn G x u := hleaf x (Finset.mem_insert_self x S)
      have hleafS : IsLeafPacket G S u := fun y hy => hleaf y (Finset.mem_insert_of_mem hy)
      let G_S := relocatePacket G S w hwS
      have hG_S : G_S.IsTree := ih huS hwS hleafS
      have hx_leaf_S : IsLeafIn G_S x u := by
        intro y
        change ((x ∉ S ∧ y ∉ S ∧ G.Adj x y) ∨ (x ∈ S ∧ y = w) ∨ (x = w ∧ y ∈ S)) ↔ y = u
        constructor
        · rintro (⟨_, _, hxy⟩ | ⟨hx_in, _⟩ | ⟨hx_eq, _⟩)
          · exact (hx_leaf y).mp hxy
          · exact False.elim (hxS hx_in)
          · exact False.elim (hxw hx_eq)
        · intro hyu
          rw [hyu]
          exact Or.inl ⟨hxS, huS, (hx_leaf u).mpr rfl⟩
      have hTree_re : (reattachLeaf G_S x w hxw).IsTree :=
        h_reattachLeaf_isTree G_S x u w hxw hG_S hx_leaf_S
      have h_step_eq : relocatePacket G (insert x S) w hw = reattachLeaf G_S x w hxw := by
        ext a b
        change ((a ∉ insert x S ∧ b ∉ insert x S ∧ G.Adj a b) ∨
            (a ∈ insert x S ∧ b = w) ∨ (a = w ∧ b ∈ insert x S)) ↔
          ((a ≠ x ∧ b ≠ x ∧ ((a ∉ S ∧ b ∉ S ∧ G.Adj a b) ∨ (a ∈ S ∧ b = w) ∨ (a = w ∧ b ∈ S))) ∨
            (a = x ∧ b = w) ∨ (a = w ∧ b = x))
        simp only [Finset.mem_insert, not_or]
        constructor
        · rintro (⟨⟨hax, haS⟩, ⟨hbx, hbS⟩, hab⟩ | ⟨rfl | haS, rfl⟩ | ⟨rfl, rfl | hbS⟩)
          · exact Or.inl ⟨hax, hbx, Or.inl ⟨haS, hbS, hab⟩⟩
          · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
          · have hax : a ≠ x := fun h => hxS (h ▸ haS)
            exact Or.inl ⟨hax, hxw.symm, Or.inr (Or.inl ⟨haS, rfl⟩)⟩
          · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
          · have hbx : b ≠ x := fun h => hxS (h ▸ hbS)
            exact Or.inl ⟨hxw.symm, hbx, Or.inr (Or.inr ⟨rfl, hbS⟩)⟩
        · rintro (⟨hax, hbx, ⟨haS, hbS, hab⟩ | ⟨haS, rfl⟩ | ⟨rfl, hbS⟩⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact Or.inl ⟨⟨hax, haS⟩, ⟨hbx, hbS⟩, hab⟩
          · exact Or.inr (Or.inl ⟨Or.inr haS, rfl⟩)
          · exact Or.inr (Or.inr ⟨rfl, Or.inr hbS⟩)
          · exact Or.inr (Or.inl ⟨Or.inl rfl, rfl⟩)
          · exact Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩)
      rw [h_step_eq]
      exact hTree_re
  have h_induce_relocate : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
      (w : Fin n) (hw : w ∉ S) (H A : Finset (Fin n)),
      Disjoint H S → A ⊆ H →
      (relocatePacket G S w hw).induce (A : Set (Fin n)) = G.induce (A : Set (Fin n)) := by
    intro n G S w hw H A hHS hAH
    ext ⟨a, ha⟩ ⟨b, hb⟩
    have haS : a ∉ S := Finset.disjoint_left.mp hHS (hAH ha)
    have hbS : b ∉ S := Finset.disjoint_left.mp hHS (hAH hb)
    change (relocatePacket G S w hw).Adj a b ↔ G.Adj a b
    simp [relocatePacket, haS, hbS]
  have h_isSubtree_relocate : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
      (w : Fin n) (hw : w ∉ S) (H A : Finset (Fin n)),
      Disjoint H S → A ⊆ H →
      (IsSubtree (relocatePacket G S w hw) A ↔ IsSubtree G A) := by
    intro n G S w hw H A hHS hAH
    simp only [IsSubtree, h_induce_relocate G S w hw H A hHS hAH]
  have h_subtreesIn_relocate : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
      (w : Fin n) (hw : w ∉ S) (H : Finset (Fin n)),
      Disjoint H S →
      subtreesIn (relocatePacket G S w hw) H = subtreesIn G H := by
    intro n G S w hw H hHS
    ext A
    simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_congr_left (fun hAH => h_isSubtree_relocate G S w hw H A hHS hAH)
  have h_rootedSubtreesIn_relocate : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
      (w w₀ : Fin n) (hw : w ∉ S) (H : Finset (Fin n)),
      Disjoint H S →
      rootedSubtreesIn (relocatePacket G S w hw) H w₀ = rootedSubtreesIn G H w₀ := by
    intro n G S w w₀ hw H hHS
    ext A
    simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_congr_left (fun hAH => h_isSubtree_relocate G S w hw H A hHS hAH.1)
  have shortened_double_broom_exists : ∀ (n ℓ a k : ℕ) (T : SimpleGraph (Fin n))
      (H L_a L_k : Finset (Fin n)) (w₀ : Fin n) (v : Fin (ℓ + 1) → Fin n),
      T.IsTree → 1 ≤ ℓ → IsDoubleBroomSuffix T ℓ a k H L_a L_k w₀ v →
      ∃ (T_short : SimpleGraph (Fin n)) (L' : Finset (Fin n)) (v' : Fin (ℓ - 1 + 1) → Fin n),
        T_short.IsTree ∧
        IsDoubleBroomSuffix T_short (ℓ - 1) a (k + 1) H L_a L' w₀ v' ∧
        subtreesIn T_short H = subtreesIn T H ∧
        rootedSubtreesIn T_short H w₀ = rootedSubtreesIn T H w₀ := by
    intro n ℓ a k T H L_a L_k w₀ v hT hℓ hDB
    rcases hDB with ⟨hv_inj, hSub_H, hcard_a, hcard_k,
      hdisj_Hv, hdisj_Ha, hdisj_Hk, hdisj_va, hdisj_vk, hdisj_ak,
      h_univ, h_bridge, h_spine, h_pkt_a, h_pkt_k⟩
    let v' : Fin (ℓ - 1 + 1) → Fin n := fun i => v ⟨i.val, by omega⟩
    let v_last : Fin n := v (Fin.last ℓ)
    let i_pred : Fin (ℓ + 1) := ⟨(Fin.last (ℓ - 1)).val, by omega⟩
    let v_pred : Fin n := v' (Fin.last (ℓ - 1))
    have hv_pred_eq : v_pred = v i_pred := rfl
    let L' : Finset (Fin n) := insert v_last L_k
    have hv_mem_v : ∀ j : Fin (ℓ + 1), v j ∈ Finset.univ.image v :=
      fun j => Finset.mem_image_of_mem v (Finset.mem_univ j)
    have hv_not_Lk : ∀ j : Fin (ℓ + 1), v j ∉ L_k :=
      fun j => Finset.disjoint_left.mp hdisj_vk (hv_mem_v j)
    have hv_not_La : ∀ j : Fin (ℓ + 1), v j ∉ L_a :=
      fun j => Finset.disjoint_left.mp hdisj_va (hv_mem_v j)
    have hv_not_H : ∀ j : Fin (ℓ + 1), v j ∉ H :=
      fun j => Finset.disjoint_right.mp hdisj_Hv (hv_mem_v j)
    have hv_last_not_Lk : v_last ∉ L_k := hv_not_Lk (Fin.last ℓ)
    have hw_not_Lk : v_pred ∉ L_k := hv_not_Lk i_pred
    have hv_pred_not_H : v_pred ∉ H := hv_not_H i_pred
    have hv_pred_not_La : v_pred ∉ L_a := hv_not_La i_pred
    let T_short : SimpleGraph (Fin n) := relocatePacket T L_k v_pred hw_not_Lk
    have h_adj_out : ∀ {a b : Fin n}, a ∉ L_k → b ∉ L_k → (T_short.Adj a b ↔ T.Adj a b) := by
      intro a b ha hb
      simp [T_short, relocatePacket, ha, hb]
    have hT_short : T_short.IsTree :=
      h_relocatePacket_isTree T L_k v_last v_pred hv_last_not_Lk hw_not_Lk hT h_pkt_k
    have hSub_H_short : IsSubtree T_short H :=
      (h_isSubtree_relocate T L_k v_pred hw_not_Lk H H hdisj_Hk (Finset.Subset.refl H)).mpr hSub_H
    have hSub_short : subtreesIn T_short H = subtreesIn T H :=
      h_subtreesIn_relocate T L_k v_pred hw_not_Lk H hdisj_Hk
    have hRoot_short : rootedSubtreesIn T_short H w₀ = rootedSubtreesIn T H w₀ :=
      h_rootedSubtreesIn_relocate T L_k v_pred w₀ hw_not_Lk H hdisj_Hk
    have hv'_inj : Function.Injective v' := by
      intro i j hij
      have h_eq : (⟨i.val, by omega⟩ : Fin (ℓ + 1)) = ⟨j.val, by omega⟩ := hv_inj hij
      exact Fin.ext (Fin.mk.inj_iff.mp h_eq)
    have hv'0 : v' 0 = v 0 := by
      change v ⟨(0 : Fin (ℓ - 1 + 1)).val, _⟩ = v 0
      congr 1
    have h_mem_img_v' : ∀ x : Fin n, x ∈ Finset.univ.image v' ↔ ∃ j : Fin (ℓ + 1), j.val < ℓ ∧ v j = x := by
      intro x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        refine ⟨⟨i.val, by omega⟩, ?_, rfl⟩
        change i.val < ℓ
        have hi : i.val < ℓ - 1 + 1 := i.isLt
        omega
      · rintro ⟨j, hj, rfl⟩
        exact ⟨⟨j.val, by omega⟩, rfl⟩
    have hv_last_not_v' : v_last ∉ Finset.univ.image v' := by
      rw [h_mem_img_v']
      rintro ⟨j, hj, hj_eq⟩
      have hj_last : j = Fin.last ℓ := hv_inj hj_eq
      have hj_val : j.val = ℓ := by rw [hj_last, Fin.val_last]
      omega
    have h_img_v_eq : Finset.univ.image v = insert v_last (Finset.univ.image v') := by
      ext x
      simp only [Finset.mem_insert, h_mem_img_v', Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, rfl⟩
        have hj : j.val < ℓ + 1 := j.isLt
        by_cases hj_eq : j.val = ℓ
        · left
          have hj_last : j = Fin.last ℓ := by
            ext
            rw [Fin.val_last]
            exact hj_eq
          rw [hj_last]
        · right
          exact ⟨j, by omega, rfl⟩
      · rintro (rfl | ⟨j, _, rfl⟩)
        · exact ⟨Fin.last ℓ, rfl⟩
        · exact ⟨j, rfl⟩
    have h_img_v'_sub : Finset.univ.image v' ⊆ Finset.univ.image v := by
      rw [h_img_v_eq]
      exact Finset.subset_insert _ _
    have h_D_eq : (Finset.univ.image v') ∪ L_a ∪ L' = (Finset.univ.image v) ∪ L_a ∪ L_k := by
      ext x
      simp only [L', h_img_v_eq, Finset.mem_union, Finset.mem_insert]
      tauto
    have hcard_L' : L'.card = k + 1 := by
      rw [Finset.card_insert_of_notMem hv_last_not_Lk, hcard_k]
    have h_univ_short : H ∪ (Finset.univ.image v') ∪ L_a ∪ L' = Finset.univ := by
      calc H ∪ (Finset.univ.image v') ∪ L_a ∪ L'
        _ = H ∪ ((Finset.univ.image v') ∪ L_a ∪ L') := by simp only [Finset.union_assoc]
        _ = H ∪ ((Finset.univ.image v) ∪ L_a ∪ L_k) := by rw [h_D_eq]
        _ = H ∪ (Finset.univ.image v) ∪ L_a ∪ L_k := by simp only [Finset.union_assoc]
        _ = Finset.univ := h_univ
    have h_bridge_short : IsBridgeJoin T_short H ((Finset.univ.image v') ∪ L_a ∪ L') w₀ (v' 0) := by
      rw [h_D_eq, hv'0]
      rcases h_bridge with ⟨hdisj_HD, hw₀_H, hv0_D, hadj_w0_v0, huniq_bridge⟩
      refine ⟨hdisj_HD, hw₀_H, hv0_D, ?_, ?_⟩
      · have hw₀_not_Lk : w₀ ∉ L_k := Finset.disjoint_left.mp hdisj_Hk hw₀_H
        exact Or.inl ⟨hw₀_not_Lk, hv_not_Lk 0, hadj_w0_v0⟩
      · intro u hu y hy hadj_short
        have hu_not_Lk : u ∉ L_k := Finset.disjoint_left.mp hdisj_Hk hu
        have hu_ne_vpred : u ≠ v_pred := fun h => hv_pred_not_H (h ▸ hu)
        rcases hadj_short with ⟨_, _, hadj⟩ | ⟨hu_Lk, _⟩ | ⟨hu_eq, _⟩
        · exact huniq_bridge u hu y hy hadj
        · exact False.elim (hu_not_Lk hu_Lk)
        · exact False.elim (hu_ne_vpred hu_eq)
    have h_spine_short : ∀ i j : Fin (ℓ - 1 + 1),
        T_short.Adj (v' i) (v' j) ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
      intro i j
      have hvi_not_Lk : v' i ∉ L_k := hv_not_Lk ⟨i.val, by omega⟩
      have hvj_not_Lk : v' j ∉ L_k := hv_not_Lk ⟨j.val, by omega⟩
      rw [h_adj_out hvi_not_Lk hvj_not_Lk]
      exact h_spine ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
    have h_pkt_a_short : IsLeafPacket T_short L_a (v' 0) := by
      rw [hv'0]
      intro x hx y
      have hx_not_Lk : x ∉ L_k := Finset.disjoint_left.mp hdisj_ak hx
      have hx_ne_vpred : x ≠ v_pred := fun h => hv_pred_not_La (h ▸ hx)
      change ((x ∉ L_k ∧ y ∉ L_k ∧ T.Adj x y) ∨ (x ∈ L_k ∧ y = v_pred) ∨ (x = v_pred ∧ y ∈ L_k)) ↔ y = v 0
      simp only [hx_not_Lk, hx_ne_vpred, false_and, or_false, true_and, not_false_eq_true, h_pkt_a x hx y]
      exact ⟨fun h => h.2, fun h => ⟨h ▸ hv_not_Lk 0, h⟩⟩
    have h_pkt_L'_short : IsLeafPacket T_short L' (v' (Fin.last (ℓ - 1))) := by
      intro x hx y
      change T_short.Adj x y ↔ y = v_pred
      rcases Finset.mem_insert.mp hx with rfl | hx_Lk
      · have hv_last_ne_vpred : v_last ≠ v_pred := by
          intro h_eq
          have h_idx : Fin.last ℓ = i_pred := hv_inj h_eq
          have h_val : (Fin.last ℓ).val = i_pred.val := congrArg Fin.val h_idx
          simp only [i_pred, Fin.val_last] at h_val
          omega
        have hv_last_ne_v0 : v_last ≠ v 0 := by
          intro h_eq
          have h_idx : Fin.last ℓ = 0 := hv_inj h_eq
          have h_val : (Fin.last ℓ).val = (0 : Fin (ℓ + 1)).val := congrArg Fin.val h_idx
          simp only [Fin.val_last, Fin.val_zero] at h_val
          omega
        change ((v_last ∉ L_k ∧ y ∉ L_k ∧ T.Adj v_last y) ∨ (v_last ∈ L_k ∧ y = v_pred) ∨ (v_last = v_pred ∧ y ∈ L_k)) ↔ y = v_pred
        simp only [hv_last_not_Lk, hv_last_ne_vpred, false_and, or_false, true_and, not_false_eq_true]
        constructor
        · rintro ⟨hy_not_Lk, hadj⟩
          have hy_univ : y ∈ H ∪ (Finset.univ.image v) ∪ L_a ∪ L_k := by
            rw [h_univ]
            exact Finset.mem_univ y
          simp only [Finset.mem_union] at hy_univ
          rcases hy_univ with ((hy_H | hy_v) | hy_La) | hy_Lk
          · have hv_last_D : v_last ∈ (Finset.univ.image v) ∪ L_a ∪ L_k := by
              simp only [Finset.mem_union]
              exact Or.inl (Or.inl (hv_mem_v (Fin.last ℓ)))
            have h_eq := (h_bridge.2.2.2.2 y hy_H v_last hv_last_D (T.symm hadj)).2
            exact False.elim (hv_last_ne_v0 h_eq)
          · rcases Finset.mem_image.mp hy_v with ⟨j, _, rfl⟩
            have h_adj_idx := (h_spine (Fin.last ℓ) j).mp hadj
            simp only [Fin.val_last] at h_adj_idx
            have hj_lt : j.val < ℓ + 1 := j.isLt
            have hj_eq : j = i_pred := by
              ext
              simp only [i_pred, Fin.val_last]
              omega
            rw [hj_eq, hv_pred_eq]
          · have h_eq : v_last = v 0 := (h_pkt_a y hy_La v_last).mp (T.symm hadj)
            exact False.elim (hv_last_ne_v0 h_eq)
          · exact False.elim (hy_not_Lk hy_Lk)
        · rintro rfl
          refine ⟨hw_not_Lk, ?_⟩
          rw [hv_pred_eq]
          apply (h_spine (Fin.last ℓ) i_pred).mpr
          right
          simp only [i_pred, Fin.val_last]
          omega
      · have hx_ne_vpred : x ≠ v_pred := fun h => hw_not_Lk (h ▸ hx_Lk)
        change ((x ∉ L_k ∧ y ∉ L_k ∧ T.Adj x y) ∨ (x ∈ L_k ∧ y = v_pred) ∨ (x = v_pred ∧ y ∈ L_k)) ↔ y = v_pred
        simp [hx_Lk, hx_ne_vpred]
    refine ⟨T_short, L', v', hT_short, ⟨hv'_inj, hSub_H_short, hcard_a, hcard_L',
      Disjoint.mono_right h_img_v'_sub hdisj_Hv,
      hdisj_Ha,
      Finset.disjoint_insert_right.mpr ⟨hv_not_H (Fin.last ℓ), hdisj_Hk⟩,
      Disjoint.mono_left h_img_v'_sub hdisj_va,
      Finset.disjoint_insert_right.mpr ⟨hv_last_not_v', Disjoint.mono_left h_img_v'_sub hdisj_vk⟩,
      Finset.disjoint_insert_right.mpr ⟨hv_not_La (Fin.last ℓ), hdisj_ak⟩,
      h_univ_short, h_bridge_short, h_spine_short, h_pkt_a_short, h_pkt_L'_short⟩,
      hSub_short, hRoot_short⟩
  have broom_host_moments_and_bounds : ∀ (n ℓ k : ℕ) (T : SimpleGraph (Fin n))
      (A B C : Finset (Fin n)) (w r_B r_C : Fin n),
      T.IsTree → IsSubtree T A → IsSubtree T B → IsSubtree T C →
      IsBridgeJoin T A B w r_B → IsBridgeJoin T (A ∪ B) C w r_C →
      ℓ + 2 ^ k ≤ rootedCount T B r_B → ℓ + 2 ^ k ≤ rootedCount T C r_C →
      IsSubtree T (A ∪ B ∪ C) ∧
      1 ≤ rootedCount T A w ∧
      rootedCount T (A ∪ B ∪ C) w =
        rootedCount T A w * (1 + rootedCount T B r_B) * (1 + rootedCount T C r_C) ∧
      ((rootedOrderSum T (A ∪ B ∪ C) w : ℚ) / (rootedCount T (A ∪ B ∪ C) w : ℚ) =
        (rootedOrderSum T A w : ℚ) / (rootedCount T A w : ℚ) +
        (rootedOrderSum T B r_B : ℚ) / ((rootedCount T B r_B : ℚ) + 1) +
        (rootedOrderSum T C r_C : ℚ) / ((rootedCount T C r_C : ℚ) + 1)) ∧
      rootedCount T (A ∪ B ∪ C) w ≤ rootedOrderSum T (A ∪ B ∪ C) w ∧
      (ℓ + 2 ^ k + 1) ^ 2 ≤ rootedCount T (A ∪ B ∪ C) w ∧
      (ℓ + 2 ^ k + 1) * rootedOrderSum T (A ∪ B ∪ C) w ≤ (rootedCount T (A ∪ B ∪ C) w) ^ 2 := by
    intro n ℓ k T A B C w r_B r_C hT hA hB hC hJ_AB hJ_ABC hB_lb hC_lb
    classical
    have h_bridge_isSubtree : ∀ {U₁ U₂ : Finset (Fin n)} {r₁ r₂ : Fin n},
        IsSubtree T U₁ → IsSubtree T U₂ → IsBridgeJoin T U₁ U₂ r₁ r₂ → IsSubtree T (U₁ ∪ U₂) := by
      intro U₁ U₂ r₁ r₂ hU₁ hU₂ hJ
      have hr₁ : r₁ ∈ U₁ ∪ U₂ := Finset.mem_union_left U₂ hJ.2.1
      have hr₂ : r₂ ∈ U₁ ∪ U₂ := Finset.mem_union_right U₁ hJ.2.2.1
      refine ⟨⟨r₁, hr₁⟩, ?_⟩
      rw [SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨⟨r₁, hr₁⟩, ?_⟩
      rintro ⟨x, hx⟩
      rcases Finset.mem_union.mp hx with hx₁ | hx₂
      · obtain ⟨q, hq⟩ := exists_walk_of_isSubtree hU₁ hJ.2.1 hx₁
        have hq_U : ∀ z ∈ q.support, z ∈ ((U₁ ∪ U₂ : Finset (Fin n)) : Set (Fin n)) :=
          fun z hz => Finset.mem_union_left U₂ (hq z hz)
        exact (q.induce ((U₁ ∪ U₂ : Finset (Fin n)) : Set (Fin n)) hq_U).reachable
      · obtain ⟨q, hq⟩ := exists_walk_of_isSubtree hU₂ hJ.2.2.1 hx₂
        have hq_U : ∀ z ∈ q.support, z ∈ ((U₁ ∪ U₂ : Finset (Fin n)) : Set (Fin n)) :=
          fun z hz => Finset.mem_union_right U₁ (hq z hz)
        have hadj_ind : (T.induce ((U₁ ∪ U₂ : Finset (Fin n)) : Set (Fin n))).Adj ⟨r₁, hr₁⟩ ⟨r₂, hr₂⟩ :=
          hJ.2.2.2.1
        exact hadj_ind.reachable.trans (q.induce ((U₁ ∪ U₂ : Finset (Fin n)) : Set (Fin n)) hq_U).reachable
    have hAB_sub : IsSubtree T (A ∪ B) := h_bridge_isSubtree hA hB hJ_AB
    have hH_sub : IsSubtree T (A ∪ B ∪ C) := h_bridge_isSubtree hAB_sub hC hJ_ABC
    have hw_A : w ∈ A := hJ_AB.2.1
    have hrB_B : r_B ∈ B := hJ_AB.2.2.1
    have hrC_C : r_C ∈ C := hJ_ABC.2.2.1
    obtain ⟨hA_card_le, htA_bound⟩ := rooted_subtree_card_and_moment_bound n T A w hT hA hw_A
    obtain ⟨hB_card_le, htB_bound⟩ := rooted_subtree_card_and_moment_bound n T B r_B hT hB hrB_B
    obtain ⟨hC_card_le, htC_bound⟩ := rooted_subtree_card_and_moment_bound n T C r_C hT hC hrC_C
    have hA_card_pos : 1 ≤ A.card := Finset.card_pos.mpr ⟨w, hw_A⟩
    have hsA_ge1 : 1 ≤ rootedCount T A w := le_trans hA_card_pos hA_card_le
    obtain ⟨hS_AB, ht_AB⟩ := bridge_join_rooted_moments n T A B w r_B hJ_AB
    obtain ⟨hS_ABC, ht_ABC⟩ := bridge_join_rooted_moments n T (A ∪ B) C w r_C hJ_ABC
    set sA := rootedCount T A w
    set tA := rootedOrderSum T A w
    set sB := rootedCount T B r_B
    set tB := rootedOrderSum T B r_B
    set sC := rootedCount T C r_C
    set tC := rootedOrderSum T C r_C
    set S := rootedCount T (A ∪ B ∪ C) w
    set tH := rootedOrderSum T (A ∪ B ∪ C) w
    have hS_prod : S = sA * (1 + sB) * (1 + sC) := by
      rw [hS_ABC, hS_AB]
    have htH_eq : tH = tA * (1 + sB) * (1 + sC) + sA * tB * (1 + sC) + sA * (1 + sB) * tC := by
      rw [ht_ABC, ht_AB, hS_AB]
      ring
    have h_ratio : (tH : ℚ) / (S : ℚ) =
        (tA : ℚ) / (sA : ℚ) + (tB : ℚ) / ((sB : ℚ) + 1) + (tC : ℚ) / ((sC : ℚ) + 1) := by
      have hsA_pos : (0 : ℚ) < (sA : ℚ) := by exact_mod_cast hsA_ge1
      have hsB1_pos : (0 : ℚ) < (sB : ℚ) + 1 := by positivity
      have hsC1_pos : (0 : ℚ) < (sC : ℚ) + 1 := by positivity
      have hS_q : (S : ℚ) = (sA : ℚ) * (1 + (sB : ℚ)) * (1 + (sC : ℚ)) := by
        exact_mod_cast hS_prod
      have htH_q : (tH : ℚ) = (tA : ℚ) * (1 + (sB : ℚ)) * (1 + (sC : ℚ)) +
          (sA : ℚ) * (tB : ℚ) * (1 + (sC : ℚ)) + (sA : ℚ) * (1 + (sB : ℚ)) * (tC : ℚ) := by
        exact_mod_cast htH_eq
      rw [hS_q, htH_q]
      have hsA_ne : (sA : ℚ) ≠ 0 := ne_of_gt hsA_pos
      have hsB1_ne : (sB : ℚ) + 1 ≠ 0 := ne_of_gt hsB1_pos
      have hsC1_ne : 1 + (sB : ℚ) ≠ 0 := by linarith
      have hsC2_ne : (sC : ℚ) + 1 ≠ 0 := ne_of_gt hsC1_pos
      have hsC3_ne : 1 + (sC : ℚ) ≠ 0 := by linarith
      field_simp
      ring
    have hS_le_tH : S ≤ tH := by
      dsimp [S, tH, rootedCount, rootedOrderSum]
      calc (rootedSubtreesIn T (A ∪ B ∪ C) w).card
        _ = ∑ x ∈ rootedSubtreesIn T (A ∪ B ∪ C) w, 1 := by simp
        _ ≤ ∑ x ∈ rootedSubtreesIn T (A ∪ B ∪ C) w, x.card := by
            refine Finset.sum_le_sum fun x hx => ?_
            simp only [rootedSubtreesIn, Finset.mem_filter] at hx
            exact Finset.card_pos.mpr ⟨w, hx.2.2⟩
    have h_bc_lb : (ℓ + 2 ^ k + 1) ^ 2 ≤ (1 + sB) * (1 + sC) := by
      have h1 : ℓ + 2 ^ k + 1 ≤ 1 + sB := by omega
      have h2 : ℓ + 2 ^ k + 1 ≤ 1 + sC := by omega
      calc (ℓ + 2 ^ k + 1) ^ 2
        _ = (ℓ + 2 ^ k + 1) * (ℓ + 2 ^ k + 1) := sq _
        _ ≤ (1 + sB) * (1 + sC) := Nat.mul_le_mul h1 h2
    have hS_lb : (ℓ + 2 ^ k + 1) ^ 2 ≤ S := by
      rw [hS_prod, mul_assoc]
      calc (ℓ + 2 ^ k + 1) ^ 2
        _ ≤ (1 + sB) * (1 + sC) := h_bc_lb
        _ = 1 * ((1 + sB) * (1 + sC)) := (one_mul _).symm
        _ ≤ sA * ((1 + sB) * (1 + sC)) := Nat.mul_le_mul_right _ hsA_ge1
    have htH_ub : (ℓ + 2 ^ k + 1) * tH ≤ S ^ 2 := by
      have h1 : 2 * tA * (1 + sB) * (1 + sC) ≤ sA * (sA + 1) * (1 + sB) * (1 + sC) :=
        Nat.mul_le_mul_right (1 + sC) (Nat.mul_le_mul_right (1 + sB) htA_bound)
      have h2 : sA * (2 * tB) * (1 + sC) ≤ sA * (sB * (sB + 1)) * (1 + sC) :=
        Nat.mul_le_mul_right (1 + sC) (Nat.mul_le_mul_left sA htB_bound)
      have h3 : sA * (1 + sB) * (2 * tC) ≤ sA * (1 + sB) * (sC * (sC + 1)) :=
        Nat.mul_le_mul_left (sA * (1 + sB)) htC_bound
      have h2tH : 2 * tH ≤ S * ((sA + 1) + sB + sC) := by
        calc 2 * tH
          _ = 2 * tA * (1 + sB) * (1 + sC) + sA * (2 * tB) * (1 + sC) + sA * (1 + sB) * (2 * tC) := by
              rw [htH_eq]; ring
          _ ≤ sA * (sA + 1) * (1 + sB) * (1 + sC) + sA * (sB * (sB + 1)) * (1 + sC) +
              sA * (1 + sB) * (sC * (sC + 1)) :=
              Nat.add_le_add (Nat.add_le_add h1 h2) h3
          _ = S * ((sA + 1) + sB + sC) := by
              rw [hS_prod]; ring
      have h_lin : (ℓ + 2 ^ k + 1) * ((sA + 1) + sB + sC) ≤ 2 * S := by
        set dp := sA - 1
        set dx := sB - (ℓ + 2 ^ k)
        set dy := sC - (ℓ + 2 ^ k)
        have hsA_eq : sA = 1 + dp := by omega
        have hsB_eq : sB = (ℓ + 2 ^ k) + dx := by omega
        have hsC_eq : sC = (ℓ + 2 ^ k) + dy := by omega
        have h_id2 : (ℓ + 2 ^ k + 1) * ((sA + 1) + sB + sC) +
            sA * (sB + 1) * dy + sA * (sC + 1) * dx + (ℓ + 2 ^ k + 1) * dp * (sB + sC + 1) =
            2 * S := by
          rw [hS_prod, hsA_eq, hsB_eq, hsC_eq]
          ring
        omega
      have h_2mul : 2 * ((ℓ + 2 ^ k + 1) * tH) ≤ 2 * (S ^ 2) := by
        calc 2 * ((ℓ + 2 ^ k + 1) * tH)
          _ = (ℓ + 2 ^ k + 1) * (2 * tH) := by ring
          _ ≤ (ℓ + 2 ^ k + 1) * (S * ((sA + 1) + sB + sC)) := Nat.mul_le_mul_left _ h2tH
          _ = S * ((ℓ + 2 ^ k + 1) * ((sA + 1) + sB + sC)) := by ring
          _ ≤ S * (2 * S) := Nat.mul_le_mul_left S h_lin
          _ = 2 * (S ^ 2) := by ring
      omega
    exact ⟨hH_sub, hsA_ge1, hS_prod, h_ratio, hS_le_tH, hS_lb, htH_ub⟩
  have folded_star_broom_exists_and_moments : ∀ (n k : ℕ) (T : SimpleGraph (Fin n))
      (H L_k : Finset (Fin n)) (w₀ : Fin n) (v : Fin (0 + 1) → Fin n),
      T.IsTree → IsDoubleBroomSuffix T 0 0 k H ∅ L_k w₀ v →
      ∃ T_fold : SimpleGraph (Fin n),
        T_fold.IsTree ∧
        (subtreeCount T_fold : ℚ) =
          ((subtreesIn T H).card : ℚ) + ((k : ℚ) + 1) +
            ((2 : ℚ) ^ (k + 1) - 1) * (rootedCount T H w₀ : ℚ) ∧
        (subtreeOrderSum T_fold : ℚ) =
          ((∑ S ∈ subtreesIn T H, S.card : ℕ) : ℚ) + ((k : ℚ) + 1) +
            ((2 : ℚ) ^ (k + 1) - 1) * (rootedOrderSum T H w₀ : ℚ) +
            ((k : ℚ) + 1) * (2 : ℚ) ^ k * (rootedCount T H w₀ : ℚ) := by
    intro n k T H L_k w₀ v hT hDB
    rcases hDB with ⟨_hv_inj, _hSub_H, _hcard_0, hcard_k,
      hdisj_Hv, _hdisj_H0, hdisj_Hk, _hdisj_v0, hdisj_vk, _hdisj_0k,
      h_univ, h_bridge, _h_spine, _h_pkt_0, h_pkt_k⟩
    let u : Fin n := v 0
    have h_last0 : Fin.last 0 = (0 : Fin (0 + 1)) := rfl
    have h_pkt_k_u : IsLeafPacket T L_k u := by
      simpa only [u, h_last0] using h_pkt_k
    have hu_mem_v : u ∈ Finset.univ.image v := Finset.mem_image_of_mem v (Finset.mem_univ 0)
    have hu_not_Lk : u ∉ L_k := Finset.disjoint_left.mp hdisj_vk hu_mem_v
    have hu_not_H : u ∉ H := Finset.disjoint_right.mp hdisj_Hv hu_mem_v
    have hw₀_H : w₀ ∈ H := h_bridge.2.1
    have hw₀_not_Lk : w₀ ∉ L_k := Finset.disjoint_left.mp hdisj_Hk hw₀_H
    have hu_ne_w₀ : u ≠ w₀ := fun h => hu_not_H (h ▸ hw₀_H)
    let T_fold : SimpleGraph (Fin n) := relocatePacket T L_k w₀ hw₀_not_Lk
    have hT_fold : T_fold.IsTree :=
      h_relocatePacket_isTree T L_k u w₀ hu_not_Lk hw₀_not_Lk hT h_pkt_k_u
    have hSub_fold : subtreesIn T_fold H = subtreesIn T H :=
      h_subtreesIn_relocate T L_k w₀ hw₀_not_Lk H hdisj_Hk
    have hRoot_fold : rootedSubtreesIn T_fold H w₀ = rootedSubtreesIn T H w₀ :=
      h_rootedSubtreesIn_relocate T L_k w₀ w₀ hw₀_not_Lk H hdisj_Hk
    have hRC_fold : rootedCount T_fold H w₀ = rootedCount T H w₀ := by
      simp only [rootedCount, hRoot_fold]
    have hRO_fold : rootedOrderSum T_fold H w₀ = rootedOrderSum T H w₀ := by
      simp only [rootedOrderSum, hRoot_fold]
    let L' : Finset (Fin n) := insert u L_k
    have hcard_L' : L'.card = k + 1 := by
      rw [Finset.card_insert_of_notMem hu_not_Lk, hcard_k]
    have hdisj_HL' : Disjoint H L' :=
      Finset.disjoint_insert_right.mpr ⟨hu_not_H, hdisj_Hk⟩
    have h_img_v : Finset.univ.image v = {u} := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨i, rfl⟩
        have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
        rw [hi]
      · rintro rfl
        exact ⟨0, rfl⟩
    have h_univ_fold : H ∪ L' = Finset.univ := by
      ext x
      have hx : x ∈ H ∪ (Finset.univ.image v) ∪ ∅ ∪ L_k := by
        rw [h_univ]
        exact Finset.mem_univ x
      simp only [L', h_img_v, Finset.union_empty, Finset.mem_union, Finset.mem_singleton,
        Finset.mem_insert, Finset.mem_univ, iff_true] at hx ⊢
      tauto
    have h_pkt_L' : IsLeafPacket T_fold L' w₀ := by
      intro x hx y
      change T_fold.Adj x y ↔ y = w₀
      rcases Finset.mem_insert.mp hx with rfl | hx_Lk
      · change ((u ∉ L_k ∧ y ∉ L_k ∧ T.Adj u y) ∨ (u ∈ L_k ∧ y = w₀) ∨ (u = w₀ ∧ y ∈ L_k)) ↔ y = w₀
        simp only [hu_not_Lk, hu_ne_w₀, false_and, or_false, true_and, not_false_eq_true]
        constructor
        · rintro ⟨hy_not_Lk, hadj⟩
          have hy_ne_u : y ≠ u := fun h => T.loopless u (h ▸ hadj)
          have hy_univ : y ∈ H ∪ L' := by
            rw [h_univ_fold]
            exact Finset.mem_univ y
          have hy_H : y ∈ H := by
            rcases Finset.mem_union.mp hy_univ with hy_H | hy_L'
            · exact hy_H
            · rcases Finset.mem_insert.mp hy_L' with rfl | hy_Lk
              · exact False.elim (hy_ne_u rfl)
              · exact False.elim (hy_not_Lk hy_Lk)
          have hu_D : u ∈ (Finset.univ.image v) ∪ ∅ ∪ L_k :=
            Finset.mem_union_left _ (Finset.mem_union_left _ hu_mem_v)
          exact (h_bridge.2.2.2.2 y hy_H u hu_D (T.symm hadj)).1
        · rintro rfl
          exact ⟨hw₀_not_Lk, T.symm h_bridge.2.2.2.1⟩
      · have hx_ne_w₀ : x ≠ w₀ := fun h => hw₀_not_Lk (h ▸ hx_Lk)
        change ((x ∉ L_k ∧ y ∉ L_k ∧ T.Adj x y) ∨ (x ∈ L_k ∧ y = w₀) ∨ (x = w₀ ∧ y ∈ L_k)) ↔ y = w₀
        simp [hx_Lk, hx_ne_w₀]
    obtain ⟨_, _, h_N, h_R⟩ :=
      leaf_packet_union_moments T_fold H L' w₀ hw₀_H hdisj_HL' h_pkt_L'
    have h_subtrees_univ : subtreesIn T_fold Finset.univ = subtrees T_fold := by
      ext S
      simp [subtreesIn]
    rw [h_univ_fold, h_subtrees_univ, hcard_L', hSub_fold, hRC_fold] at h_N
    rw [h_univ_fold, h_subtrees_univ, hcard_L', hSub_fold, hRC_fold, hRO_fold] at h_R
    refine ⟨T_fold, hT_fold, ?_, ?_⟩
    · change ((subtrees T_fold).card : ℚ) = _
      rw [h_N, Nat.cast_add, Nat.cast_one]
    · change ((∑ S ∈ subtrees T_fold, S.card : ℕ) : ℚ) = _
      rw [h_R, Nat.cast_add, Nat.cast_one, pow_succ]
      ring
  have broom_shortening_algebraic_dichotomy : ∀ (NH RH S tH ℓ k : ℕ),
      ((1 ≤ ℓ ∧ 2 ≤ k) ∨ (ℓ = 0 ∧ 3 ≤ k)) →
      S ≤ tH →
      (ℓ + 2 ^ k + 1) ^ 2 ≤ S →
      (ℓ + 2 ^ k + 1) * tH ≤ S ^ 2 →
      ((1 ≤ ℓ ∧
        (doubleBroomOrderSum RH S tH ℓ 0 k / doubleBroomCount NH S ℓ 0 k <
          doubleBroomOrderSum RH S tH (ℓ - 1) 0 (k + 1) / doubleBroomCount NH S (ℓ - 1) 0 (k + 1) ∨
         broomThreshold ℓ k ≤
          doubleBroomOrderSum RH S tH ℓ 0 k / doubleBroomCount NH S ℓ 0 k - (tH : ℚ) / (S : ℚ))) ∨
       (ℓ = 0 ∧
        (doubleBroomOrderSum RH S tH 0 0 k / doubleBroomCount NH S 0 0 k <
          ((RH : ℚ) + ((k : ℚ) + 1) + ((2 : ℚ) ^ (k + 1) - 1) * (tH : ℚ) + ((k : ℚ) + 1) * (2 : ℚ) ^ k * (S : ℚ)) /
          ((NH : ℚ) + ((k : ℚ) + 1) + ((2 : ℚ) ^ (k + 1) - 1) * (S : ℚ)) ∨
         broomThreshold 0 k ≤
          doubleBroomOrderSum RH S tH 0 0 k / doubleBroomCount NH S 0 0 k - (tH : ℚ) / (S : ℚ)))) := by
    intro NH RH S tH ℓ k h_lk hStH hS_lb htH_ub
    rcases h_lk with ⟨hℓ, hk⟩ | ⟨hℓ, hk⟩
    · left
      refine ⟨hℓ, ?_⟩
      set z : ℚ := (2 : ℚ) ^ k
      set ρ : ℚ := (ℓ : ℚ) + z
      set D : ℚ := (S : ℚ) + (ℓ : ℚ) - 1
      set N₀ : ℚ := doubleBroomCount NH S ℓ 0 k
      set R₀ : ℚ := doubleBroomOrderSum RH S tH ℓ 0 k
      set N₁ : ℚ := doubleBroomCount NH S (ℓ - 1) 0 (k + 1)
      set R₁ : ℚ := doubleBroomOrderSum RH S tH (ℓ - 1) 0 (k + 1)
      by_cases h_imp : R₀ / N₀ < R₁ / N₁
      · exact Or.inl h_imp
      · right
        have h_not_lt : R₁ / N₁ ≤ R₀ / N₀ := not_lt.mp h_imp
        have hℓ_q : (1 : ℚ) ≤ (ℓ : ℚ) := by exact_mod_cast hℓ
        have hk_pow : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
        have hz_ge4 : (4 : ℚ) ≤ z := by
          have h_cast : ((2 ^ 2 : ℕ) : ℚ) ≤ ((2 ^ k : ℕ) : ℚ) := by exact_mod_cast hk_pow
          push_cast at h_cast
          linarith
        have hz1_pos : (0 : ℚ) < z - 1 := by linarith
        have hρ1_pos : (0 : ℚ) < ρ + 1 := by linarith
        have hS_ge_q : (ρ + 1) ^ 2 ≤ (S : ℚ) := by
          have h_cast : (((ℓ + 2 ^ k + 1) ^ 2 : ℕ) : ℚ) ≤ (S : ℚ) := by exact_mod_cast hS_lb
          push_cast at h_cast
          linarith
        have htH_le_q : (ρ + 1) * (tH : ℚ) ≤ (S : ℚ) ^ 2 := by
          have h_cast : (((ℓ + 2 ^ k + 1) * tH : ℕ) : ℚ) ≤ ((S ^ 2 : ℕ) : ℚ) := by exact_mod_cast htH_ub
          push_cast at h_cast
          linarith
        have hS_pos : (0 : ℚ) < (S : ℚ) := by nlinarith
        have hD_pos : (0 : ℚ) < D := by dsimp [D]; linarith
        have hNH_nonneg : (0 : ℚ) ≤ (NH : ℚ) := Nat.cast_nonneg NH
        have hN₀_eq : N₀ = (NH : ℚ) + (k : ℚ) + z + (ℓ : ℚ) * (1 + z) +
            (ℓ : ℚ) * ((ℓ : ℚ) - 1) / 2 + (S : ℚ) * ((ℓ : ℚ) + z) := by
          dsimp [N₀, doubleBroomCount, z]
          ring
        have hN₀_pos : (0 : ℚ) < N₀ := by
          rw [hN₀_eq]
          have h1 : (0 : ℚ) ≤ (ℓ : ℚ) * ((ℓ : ℚ) - 1) / 2 := by nlinarith
          have h2 : (0 : ℚ) ≤ (k : ℚ) := Nat.cast_nonneg k
          nlinarith
        have hN₁_sub : N₁ - N₀ = (z - 1) * D := by
          dsimp [N₁, N₀, D, doubleBroomCount, z]
          rw [Nat.cast_sub hℓ, Nat.cast_add, Nat.cast_one, pow_succ]
          ring
        have hN₁_pos : (0 : ℚ) < N₁ := by nlinarith
        have h_cross : 0 ≤ R₀ * N₁ - R₁ * N₀ := by
          have h_le := (div_le_div_iff₀ hN₁_pos hN₀_pos).mp h_not_lt
          linarith
        have h_thresh : 2 * (ρ + 1) * (z - 1) * broomThreshold ℓ k =
            2 * (ρ + 1) * (z - 1) * (ℓ : ℚ) + (ρ + 1) * (k : ℚ) * z - 3 * (z - 1) * ((ℓ : ℚ) - 1) := by
          have hℓ_ne : ℓ ≠ 0 := by omega
          dsimp [broomThreshold]
          rw [if_neg hℓ_ne]
          have hz_ne : z - 1 ≠ 0 := ne_of_gt hz1_pos
          have hρ_ne : ρ + 1 ≠ 0 := ne_of_gt hρ1_pos
          change 2 * (ρ + 1) * (z - 1) *
              ((ℓ : ℚ) + (k : ℚ) * z / (2 * (z - 1)) - 3 * ((ℓ : ℚ) - 1) / (2 * (ρ + 1))) = _
          field_simp
        have h_id : 2 * (ρ + 1) * (z - 1) * D * ((S : ℚ) * R₀ - (tH : ℚ) * N₀) -
            (S : ℚ) * N₀ * D * (2 * (ρ + 1) * (z - 1) * broomThreshold ℓ k) -
            2 * (S : ℚ) * (ρ + 1) * (R₀ * N₁ - R₁ * N₀) =
            N₀ * (z - 1) * ((ℓ : ℚ) - 1) * (
              2 * ((S : ℚ) ^ 2 - (ρ + 1) * (tH : ℚ)) +
              (S : ℚ) * ((S : ℚ) - (ρ + 1) ^ 2) +
              (S : ℚ) * (ρ + 1) * (z + 3) +
              3 * (S : ℚ) * ((ℓ : ℚ) - 1)) := by
          rw [h_thresh]
          dsimp [N₀, R₀, N₁, R₁, D, ρ, doubleBroomCount, doubleBroomOrderSum, z]
          rw [Nat.cast_sub hℓ, Nat.cast_add, Nat.cast_one, pow_succ]
          ring
        have h_rhs_nonneg : 0 ≤ N₀ * (z - 1) * ((ℓ : ℚ) - 1) * (
            2 * ((S : ℚ) ^ 2 - (ρ + 1) * (tH : ℚ)) +
            (S : ℚ) * ((S : ℚ) - (ρ + 1) ^ 2) +
            (S : ℚ) * (ρ + 1) * (z + 3) +
            3 * (S : ℚ) * ((ℓ : ℚ) - 1)) := by
          have h_f1 : 0 ≤ N₀ * (z - 1) * ((ℓ : ℚ) - 1) := by
            exact mul_nonneg (mul_nonneg (le_of_lt hN₀_pos) (le_of_lt hz1_pos)) (by linarith)
          have h_t1 : 0 ≤ 2 * ((S : ℚ) ^ 2 - (ρ + 1) * (tH : ℚ)) := by linarith
          have h_t2 : 0 ≤ (S : ℚ) * ((S : ℚ) - (ρ + 1) ^ 2) :=
            mul_nonneg (le_of_lt hS_pos) (by linarith)
          have h_t3 : 0 ≤ (S : ℚ) * (ρ + 1) * (z + 3) := by positivity
          have h_t4 : 0 ≤ 3 * (S : ℚ) * ((ℓ : ℚ) - 1) :=
            mul_nonneg (by positivity) (by linarith)
          exact mul_nonneg h_f1 (by linarith)
        have h_main_ineq : 0 ≤ 2 * (ρ + 1) * (z - 1) * D *
            ((S : ℚ) * R₀ - (tH : ℚ) * N₀ - (S : ℚ) * N₀ * broomThreshold ℓ k) := by
          have h_rew : 2 * (ρ + 1) * (z - 1) * D *
              ((S : ℚ) * R₀ - (tH : ℚ) * N₀ - (S : ℚ) * N₀ * broomThreshold ℓ k) =
              (2 * (ρ + 1) * (z - 1) * D * ((S : ℚ) * R₀ - (tH : ℚ) * N₀) -
               (S : ℚ) * N₀ * D * (2 * (ρ + 1) * (z - 1) * broomThreshold ℓ k) -
               2 * (S : ℚ) * (ρ + 1) * (R₀ * N₁ - R₁ * N₀)) +
              2 * (S : ℚ) * (ρ + 1) * (R₀ * N₁ - R₁ * N₀) := by ring
          rw [h_rew, h_id]
          have h_term2 : 0 ≤ 2 * (S : ℚ) * (ρ + 1) * (R₀ * N₁ - R₁ * N₀) := by
            have : 0 ≤ 2 * (S : ℚ) * (ρ + 1) := by positivity
            exact mul_nonneg this h_cross
          linarith
        have h_factor_pos : 0 < 2 * (ρ + 1) * (z - 1) * D := by positivity
        have h_core : (S : ℚ) * N₀ * broomThreshold ℓ k ≤ (S : ℚ) * R₀ - (tH : ℚ) * N₀ := by
          have h_nonneg := nonneg_of_mul_nonneg_right h_main_ineq h_factor_pos
          linarith
        have h_div_sub : R₀ / N₀ - (tH : ℚ) / (S : ℚ) =
            ((S : ℚ) * R₀ - (tH : ℚ) * N₀) / ((S : ℚ) * N₀) := by
          have hS_ne : (S : ℚ) ≠ 0 := ne_of_gt hS_pos
          have hN₀_ne : N₀ ≠ 0 := ne_of_gt hN₀_pos
          field_simp
        rw [h_div_sub, le_div_iff₀ (mul_pos hS_pos hN₀_pos)]
        linarith
    · right
      refine ⟨hℓ, ?_⟩
      subst hℓ
      set z : ℚ := (2 : ℚ) ^ k
      set N₀ : ℚ := doubleBroomCount NH S 0 0 k
      set R₀ : ℚ := doubleBroomOrderSum RH S tH 0 0 k
      set N_fold : ℚ := (NH : ℚ) + ((k : ℚ) + 1) + ((2 : ℚ) ^ (k + 1) - 1) * (S : ℚ)
      set R_fold : ℚ := (RH : ℚ) + ((k : ℚ) + 1) + ((2 : ℚ) ^ (k + 1) - 1) * (tH : ℚ) +
          ((k : ℚ) + 1) * (2 : ℚ) ^ k * (S : ℚ)
      by_cases h_imp : R₀ / N₀ < R_fold / N_fold
      · exact Or.inl h_imp
      · right
        have h_not_lt : R_fold / N_fold ≤ R₀ / N₀ := not_lt.mp h_imp
        have hk_pow : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
        have hz_ge8 : (8 : ℚ) ≤ z := by
          have h_cast : ((2 ^ 3 : ℕ) : ℚ) ≤ ((2 ^ k : ℕ) : ℚ) := by exact_mod_cast hk_pow
          push_cast at h_cast
          linarith
        have hz1_pos : (0 : ℚ) < z - 1 := by linarith
        have hS_ge_q : (z + 1) ^ 2 ≤ (S : ℚ) := by
          have h_cast : (((0 + 2 ^ k + 1) ^ 2 : ℕ) : ℚ) ≤ (S : ℚ) := by exact_mod_cast hS_lb
          push_cast at h_cast
          linarith
        have hStH_q : (S : ℚ) ≤ (tH : ℚ) := by exact_mod_cast hStH
        have hS_pos : (0 : ℚ) < (S : ℚ) := by nlinarith
        have hS1_pos : (0 : ℚ) < (S : ℚ) - 1 := by nlinarith
        have hNH_nonneg : (0 : ℚ) ≤ (NH : ℚ) := Nat.cast_nonneg NH
        have hN₀_eq : N₀ = (NH : ℚ) + (k : ℚ) + z + (S : ℚ) * z := by
          dsimp [N₀, doubleBroomCount, z]
          ring
        have hN₀_pos : (0 : ℚ) < N₀ := by
          rw [hN₀_eq]
          have : (0 : ℚ) ≤ (k : ℚ) := Nat.cast_nonneg k
          nlinarith
        have hNfold_sub : N_fold - N₀ = (z - 1) * ((S : ℚ) - 1) := by
          dsimp [N_fold, N₀, doubleBroomCount, z]
          rw [pow_succ]
          ring
        have hNfold_pos : (0 : ℚ) < N_fold := by nlinarith
        have h_cross : 0 ≤ R₀ * N_fold - R_fold * N₀ := by
          have h_le := (div_le_div_iff₀ hNfold_pos hN₀_pos).mp h_not_lt
          linarith
        have h_thresh : 2 * (z - 1) * broomThreshold 0 k = (k : ℚ) * z := by
          dsimp [broomThreshold]
          have hz_ne : z - 1 ≠ 0 := ne_of_gt hz1_pos
          change 2 * (z - 1) * ((k : ℚ) * z / (2 * (z - 1))) = (k : ℚ) * z
          field_simp
        have h_id : 2 * (z - 1) * ((S : ℚ) - 1) * ((S : ℚ) * R₀ - (tH : ℚ) * N₀) -
            (S : ℚ) * N₀ * ((S : ℚ) - 1) * (2 * (z - 1) * broomThreshold 0 k) -
            2 * (S : ℚ) * (R₀ * N_fold - R_fold * N₀) =
            2 * N₀ * (z - 1) * ((tH : ℚ) - (S : ℚ)) := by
          rw [h_thresh]
          dsimp [N₀, R₀, N_fold, R_fold, doubleBroomCount, doubleBroomOrderSum, z]
          rw [pow_succ]
          ring
        have h_rhs_nonneg : 0 ≤ 2 * N₀ * (z - 1) * ((tH : ℚ) - (S : ℚ)) := by
          have h1 : 0 ≤ 2 * N₀ * (z - 1) := by positivity
          exact mul_nonneg h1 (by linarith)
        have h_main_ineq : 0 ≤ 2 * (z - 1) * ((S : ℚ) - 1) *
            ((S : ℚ) * R₀ - (tH : ℚ) * N₀ - (S : ℚ) * N₀ * broomThreshold 0 k) := by
          have h_rew : 2 * (z - 1) * ((S : ℚ) - 1) *
              ((S : ℚ) * R₀ - (tH : ℚ) * N₀ - (S : ℚ) * N₀ * broomThreshold 0 k) =
              (2 * (z - 1) * ((S : ℚ) - 1) * ((S : ℚ) * R₀ - (tH : ℚ) * N₀) -
               (S : ℚ) * N₀ * ((S : ℚ) - 1) * (2 * (z - 1) * broomThreshold 0 k) -
               2 * (S : ℚ) * (R₀ * N_fold - R_fold * N₀)) +
              2 * (S : ℚ) * (R₀ * N_fold - R_fold * N₀) := by ring
          rw [h_rew, h_id]
          have h_term2 : 0 ≤ 2 * (S : ℚ) * (R₀ * N_fold - R_fold * N₀) :=
            mul_nonneg (by positivity) h_cross
          linarith
        have h_factor_pos : 0 < 2 * (z - 1) * ((S : ℚ) - 1) := by positivity
        have h_core : (S : ℚ) * N₀ * broomThreshold 0 k ≤ (S : ℚ) * R₀ - (tH : ℚ) * N₀ := by
          have h_nonneg := nonneg_of_mul_nonneg_right h_main_ineq h_factor_pos
          linarith
        have h_div_sub : R₀ / N₀ - (tH : ℚ) / (S : ℚ) =
            ((S : ℚ) * R₀ - (tH : ℚ) * N₀) / ((S : ℚ) * N₀) := by
          have hS_ne : (S : ℚ) ≠ 0 := ne_of_gt hS_pos
          have hN₀_ne : N₀ ≠ 0 := ne_of_gt hN₀_pos
          field_simp
        rw [h_div_sub, le_div_iff₀ (mul_pos hS_pos hN₀_pos)]
        linarith
  intro n _hn T hT ℓ k A B C L_k w r_B r_C v h_lk hv_inj hA hB hC hcard_k
    _hdisj_AB _hdisj_AC _hdisj_BC hdisj_Hv hdisj_Hk hdisj_vk h_univ
    hJ_AB hJ_ABC hJ_HD h_spine h_pkt_k hB_lb hC_lb
  set H := A ∪ B ∪ C
  obtain ⟨hH_sub, _hsA_ge1, _hS_prod, h_ratio, hS_le_tH, hS_lb, htH_ub⟩ :=
    broom_host_moments_and_bounds n ℓ k T A B C w r_B r_C hT hA hB hC hJ_AB hJ_ABC hB_lb hC_lb
  have hDB : IsDoubleBroomSuffix T ℓ 0 k H ∅ L_k w v := by
    refine ⟨hv_inj, hH_sub, Finset.card_empty, hcard_k,
      hdisj_Hv, Finset.disjoint_empty_right H, hdisj_Hk,
      Finset.disjoint_empty_right _, hdisj_vk, Finset.disjoint_empty_left L_k,
      ?_, ?_, h_spine, fun x hx => False.elim (Finset.notMem_empty x hx), h_pkt_k⟩
    · simp only [Finset.union_empty]
      exact h_univ
    · simp only [Finset.union_empty]
      exact hJ_HD
  obtain ⟨hN_T, hR_T⟩ := double_broom_suffix_moments n ℓ 0 k T H ∅ L_k w v hT hDB
  set NH := (subtreesIn T H).card
  set RH := ∑ S ∈ subtreesIn T H, S.card
  set S_H := rootedCount T H w
  set tH := rootedOrderSum T H w
  have h_mu_T : meanSubtreeOrder T =
      doubleBroomOrderSum RH S_H tH ℓ 0 k / doubleBroomCount NH S_H ℓ 0 k := by
    dsimp [meanSubtreeOrder]
    rw [hN_T, hR_T]
  have h_dich := broom_shortening_algebraic_dichotomy NH RH S_H tH ℓ k h_lk hS_le_tH hS_lb htH_ub
  rcases h_dich with ⟨hℓ_ge1, h_imp | h_thr⟩ | ⟨hℓ_eq0, h_imp | h_thr⟩
  · left
    obtain ⟨T_short, L', v', hT_short, hDB_short, hSub_short, hRoot_short⟩ :=
      shortened_double_broom_exists n ℓ 0 k T H ∅ L_k w v hT hℓ_ge1 hDB
    obtain ⟨hN_short, hR_short⟩ :=
      double_broom_suffix_moments n (ℓ - 1) 0 (k + 1) T_short H ∅ L' w v' hT_short hDB_short
    have hNH_eq : (subtreesIn T_short H).card = NH := by simp [NH, hSub_short]
    have hRH_eq : (∑ S ∈ subtreesIn T_short H, S.card) = RH := by simp [RH, hSub_short]
    have hSH_eq : rootedCount T_short H w = S_H := by simp [S_H, rootedCount, hRoot_short]
    have htH_eq : rootedOrderSum T_short H w = tH := by simp [tH, rootedOrderSum, hRoot_short]
    refine ⟨T_short, hT_short, ?_⟩
    rw [h_mu_T]
    dsimp [meanSubtreeOrder]
    rw [hN_short, hR_short, hNH_eq, hRH_eq, hSH_eq, htH_eq]
    exact h_imp
  · right
    rw [h_mu_T, ← h_ratio]
    exact h_thr
  · left
    subst hℓ_eq0
    obtain ⟨T_fold, hT_fold, hN_fold, hR_fold⟩ :=
      folded_star_broom_exists_and_moments n k T H L_k w v hT hDB
    refine ⟨T_fold, hT_fold, ?_⟩
    rw [h_mu_T]
    dsimp [meanSubtreeOrder]
    rw [hN_fold, hR_fold]
    exact h_imp
  · right
    subst hℓ_eq0
    rw [h_mu_T, ← h_ratio]
    exact h_thr

theorem bridge_join_unrooted_moments : ∀ (n : ℕ) (G : SimpleGraph (Fin n))
    (U₁ U₂ : Finset (Fin n)) (r₁ r₂ : Fin n),
    IsSubtree G U₁ → IsSubtree G U₂ → IsBridgeJoin G U₁ U₂ r₁ r₂ →
    IsSubtree G (U₁ ∪ U₂) ∧
    unrootedCount G (U₁ ∪ U₂) =
      unrootedCount G U₁ + unrootedCount G U₂ + rootedCount G U₁ r₁ * rootedCount G U₂ r₂ ∧
    unrootedOrderSum G (U₁ ∪ U₂) =
      unrootedOrderSum G U₁ + unrootedOrderSum G U₂ +
      rootedOrderSum G U₁ r₁ * rootedCount G U₂ r₂ +
      rootedCount G U₁ r₁ * rootedOrderSum G U₂ r₂ :=
by
  intro n G A B w r_B hSubA hSubB hJ
  classical
  have isBridgeJoin_symm : ∀ {A B : Finset (Fin n)} {w r_B : Fin n},
      IsBridgeJoin G A B w r_B → IsBridgeJoin G B A r_B w := by
    intro A B w r_B hJ
    rcases hJ with ⟨h_disj, hw, hr_B, hadj, h_bridge⟩
    refine ⟨h_disj.symm, hr_B, hw, G.symm hadj, ?_⟩
    intro u hu v hv huv
    exact (h_bridge v hv u hu (G.symm huv)).symm
  have exists_walk_of_isSubtree : ∀ {S : Finset (Fin n)},
      IsSubtree G S → ∀ {a b : Fin n}, a ∈ S → b ∈ S →
      ∃ q : G.Walk a b, ∀ z ∈ q.support, z ∈ S := by
    intro S hS a b ha hb
    obtain ⟨q₀⟩ := hS.2.preconnected ⟨a, ha⟩ ⟨b, hb⟩
    suffices ∀ {u v : ↑(S : Set (Fin n))} (q : (G.induce (S : Set (Fin n))).Walk u v),
        ∃ q' : G.Walk u.1 v.1, ∀ z ∈ q'.support, z ∈ S from this q₀
    intro u v q
    induction q with
    | @nil u =>
      refine ⟨SimpleGraph.Walk.nil, ?_⟩
      intro z hz
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      rw [hz]
      exact Finset.mem_coe.mp u.2
    | @cons u c v hadj q' ih =>
      obtain ⟨q₁, hq₁⟩ := ih
      refine ⟨SimpleGraph.Walk.cons hadj q₁, ?_⟩
      intro z hz
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz'
      · exact Finset.mem_coe.mp u.2
      · exact hq₁ z hz'
  have bridge_walk_mem_edges : ∀ {A B : Finset (Fin n)} {w r_B : Fin n},
      IsBridgeJoin G A B w r_B → ∀ {a b : Fin n} (q : G.Walk a b),
      (∀ z ∈ q.support, z ∈ A ∪ B) →
      ((a ∈ A ∧ b ∈ B) ∨ (a ∈ B ∧ b ∈ A)) →
      s(w, r_B) ∈ q.edges := by
    intro A B w r_B hJ a b q
    induction q with
    | nil =>
      intro _ h_ab
      rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact False.elim (Finset.disjoint_left.mp hJ.1 ha hb)
      · exact False.elim (Finset.disjoint_left.mp hJ.1 hb ha)
    | @cons a c b h_step q' ih =>
      intro h_supp h_ab
      have hc_mem : c ∈ A ∪ B := h_supp c (by
        simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.start_mem_support])
      have h_supp' : ∀ z ∈ q'.support, z ∈ A ∪ B := fun z hz =>
        h_supp z (by simp [SimpleGraph.Walk.support_cons, hz])
      rcases Finset.mem_union.mp hc_mem with hcA | hcB
      · rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ (ih h_supp' (Or.inl ⟨hcA, hb⟩))
        · obtain ⟨hcw, har⟩ := hJ.2.2.2.2 c hcA a ha (G.symm h_step)
          subst hcw har
          rw [SimpleGraph.Walk.edges_cons, Sym2.eq_swap]
          exact List.mem_cons_self
      · rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · obtain ⟨haw, hcr⟩ := hJ.2.2.2.2 a ha c hcB h_step
          subst haw hcr
          rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_self
        · rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ (ih h_supp' (Or.inr ⟨hcB, hb⟩))
  have bridge_path_support_left : ∀ {A B : Finset (Fin n)} {w r_B : Fin n},
      IsBridgeJoin G A B w r_B → ∀ {a b : Fin n} (p : G.Walk a b), p.IsPath →
      (∀ z ∈ p.support, z ∈ A ∪ B) → a ∈ A → b ∈ A →
      ∀ z ∈ p.support, z ∈ A := by
    intro A B w r_B hJ a b p hp h_supp ha hb z hz
    rcases Finset.mem_union.mp (h_supp z hz) with hzA | hzB
    · exact hzA
    · exfalso
      let p₁ := p.takeUntil z hz
      let p₂ := p.dropUntil z hz
      have hp₁_supp : ∀ x ∈ p₁.support, x ∈ A ∪ B :=
        fun x hx => h_supp x (p.support_takeUntil_subset hz hx)
      have hp₂_supp : ∀ x ∈ p₂.support, x ∈ A ∪ B :=
        fun x hx => h_supp x (p.support_dropUntil_subset hz hx)
      have he₁ : s(w, r_B) ∈ p₁.edges :=
        bridge_walk_mem_edges hJ p₁ hp₁_supp (Or.inl ⟨ha, hzB⟩)
      have he₂ : s(w, r_B) ∈ p₂.edges :=
        bridge_walk_mem_edges hJ p₂ hp₂_supp (Or.inr ⟨hzB, hb⟩)
      have h_nodup : p.edges.Nodup := hp.isTrail.edges_nodup
      have h_edges : p₁.edges ++ p₂.edges = p.edges := by
        rw [← SimpleGraph.Walk.edges_append, p.take_spec hz]
      rw [← h_edges, List.nodup_append] at h_nodup
      exact h_nodup.2.2 s(w, r_B) he₁ s(w, r_B) he₂ rfl
  have bridge_crossing_left : ∀ {A B S : Finset (Fin n)} {w r_B : Fin n},
      IsBridgeJoin G A B w r_B → S ⊆ A ∪ B →
      IsSubtree G S → (S ∩ A).Nonempty → (S ∩ B).Nonempty →
      S ∩ A ∈ rootedSubtreesIn G A w := by
    intro A B S w r_B hJ hS_sub hS hSA hSB
    obtain ⟨a₀, ha₀⟩ := hSA
    obtain ⟨b₀, hb₀⟩ := hSB
    have ha₀S : a₀ ∈ S := (Finset.mem_inter.mp ha₀).1
    have ha₀A : a₀ ∈ A := (Finset.mem_inter.mp ha₀).2
    have hb₀S : b₀ ∈ S := (Finset.mem_inter.mp hb₀).1
    have hb₀B : b₀ ∈ B := (Finset.mem_inter.mp hb₀).2
    obtain ⟨q, hq_supp⟩ := exists_walk_of_isSubtree hS ha₀S hb₀S
    have hq_AB : ∀ z ∈ q.support, z ∈ A ∪ B := fun z hz => hS_sub (hq_supp z hz)
    have he : s(w, r_B) ∈ q.edges :=
      bridge_walk_mem_edges hJ q hq_AB (Or.inl ⟨ha₀A, hb₀B⟩)
    have hwS : w ∈ S := hq_supp w (q.fst_mem_support_of_mem_edges he)
    have hwSA : w ∈ S ∩ A := Finset.mem_inter.mpr ⟨hwS, hJ.2.1⟩
    have hSA_subtree : IsSubtree G (S ∩ A) := by
      refine ⟨⟨w, hwSA⟩, ?_⟩
      have : Nonempty ↑((S ∩ A : Finset (Fin n)) : Set (Fin n)) := ⟨⟨w, hwSA⟩⟩
      refine ⟨?_⟩
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      have hxS : x ∈ S := (Finset.mem_inter.mp hx).1
      have hxA : x ∈ A := (Finset.mem_inter.mp hx).2
      have hyS : y ∈ S := (Finset.mem_inter.mp hy).1
      have hyA : y ∈ A := (Finset.mem_inter.mp hy).2
      obtain ⟨q₁, hq₁_supp⟩ := exists_walk_of_isSubtree hS hxS hyS
      let p : G.Walk x y := (q₁.toPath : G.Walk x y)
      have hp_path : p.IsPath := q₁.toPath.2
      have hp_S : ∀ z ∈ p.support, z ∈ S := fun z hz => hq₁_supp z (q₁.support_toPath_subset hz)
      have hp_AB : ∀ z ∈ p.support, z ∈ A ∪ B := fun z hz => hS_sub (hp_S z hz)
      have hp_A : ∀ z ∈ p.support, z ∈ A :=
        bridge_path_support_left hJ p hp_path hp_AB hxA hyA
      have hp_SA : ∀ z ∈ p.support, z ∈ ((S ∩ A : Finset (Fin n)) : Set (Fin n)) :=
        fun z hz => Finset.mem_inter.mpr ⟨hp_S z hz, hp_A z hz⟩
      exact (p.induce ((S ∩ A : Finset (Fin n)) : Set (Fin n)) hp_SA).reachable
    simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hSA_subtree, Finset.inter_subset_right, hwSA⟩
  have bridge_union_isSubtree : ∀ {A B SA SB : Finset (Fin n)} {w r_B : Fin n},
      IsBridgeJoin G A B w r_B →
      SA ∈ rootedSubtreesIn G A w → SB ∈ rootedSubtreesIn G B r_B →
      IsSubtree G (SA ∪ SB) := by
    intro A B SA SB w r_B hJ hSA hSB
    simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hSA hSB
    rcases hSA with ⟨hSA_sub, _, hw_SA⟩
    rcases hSB with ⟨hSB_sub, _, hr_SB⟩
    have hw_U : w ∈ SA ∪ SB := Finset.mem_union_left SB hw_SA
    have hr_U : r_B ∈ SA ∪ SB := Finset.mem_union_right SA hr_SB
    refine ⟨⟨w, hw_U⟩, ?_⟩
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨w, hw_U⟩, ?_⟩
    rintro ⟨x, hx⟩
    rcases Finset.mem_union.mp hx with hxA | hxB
    · obtain ⟨q, hq⟩ := exists_walk_of_isSubtree hSA_sub hw_SA hxA
      have hq_U : ∀ z ∈ q.support, z ∈ ((SA ∪ SB : Finset (Fin n)) : Set (Fin n)) :=
        fun z hz => Finset.mem_union_left SB (hq z hz)
      exact (q.induce ((SA ∪ SB : Finset (Fin n)) : Set (Fin n)) hq_U).reachable
    · obtain ⟨q, hq⟩ := exists_walk_of_isSubtree hSB_sub hr_SB hxB
      have hq_U : ∀ z ∈ q.support, z ∈ ((SA ∪ SB : Finset (Fin n)) : Set (Fin n)) :=
        fun z hz => Finset.mem_union_right SA (hq z hz)
      have hadj_ind : (G.induce ((SA ∪ SB : Finset (Fin n)) : Set (Fin n))).Adj ⟨w, hw_U⟩ ⟨r_B, hr_U⟩ :=
        hJ.2.2.2.1
      exact hadj_ind.reachable.trans (q.induce ((SA ∪ SB : Finset (Fin n)) : Set (Fin n)) hq_U).reachable
  have hA_in_RA : A ∈ rootedSubtreesIn G A w := by
    simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hSubA, Finset.Subset.refl A, hJ.2.1⟩
  have hB_in_RB : B ∈ rootedSubtreesIn G B r_B := by
    simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hSubB, Finset.Subset.refl B, hJ.2.2.1⟩
  have hSub_AB : IsSubtree G (A ∪ B) := bridge_union_isSubtree hJ hA_in_RA hB_in_RB
  let RA_set := rootedSubtreesIn G A w
  let RB_set := rootedSubtreesIn G B r_B
  let φ : Finset (Fin n) × Finset (Fin n) → Finset (Fin n) := fun p => p.1 ∪ p.2
  let M := (RA_set ×ˢ RB_set).image φ
  have h_inter_left : ∀ {X Y : Finset (Fin n)}, X ⊆ A → Y ⊆ B → (X ∪ Y) ∩ A = X := by
    intro X Y hX hY
    ext z
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hzX | hzY, hzA⟩
      · exact hzX
      · exact False.elim (Finset.disjoint_left.mp hJ.1 hzA (hY hzY))
    · intro hzX
      exact ⟨Or.inl hzX, hX hzX⟩
  have h_inter_right : ∀ {X Y : Finset (Fin n)}, X ⊆ A → Y ⊆ B → (X ∪ Y) ∩ B = Y := by
    intro X Y hX hY
    ext z
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hzX | hzY, hzB⟩
      · exact False.elim (Finset.disjoint_left.mp hJ.1 (hX hzX) hzB)
      · exact hzY
    · intro hzY
      exact ⟨Or.inr hzY, hY hzY⟩
  have h_inj : Set.InjOn φ ((RA_set ×ˢ RB_set : Finset (Finset (Fin n) × Finset (Fin n))) : Set (Finset (Fin n) × Finset (Fin n))) := by
    intro p₁ hp₁ p₂ hp₂ h_eq
    rcases Finset.mem_product.mp (Finset.mem_coe.mp hp₁) with ⟨hp₁A, hp₁B⟩
    rcases Finset.mem_product.mp (Finset.mem_coe.mp hp₂) with ⟨hp₂A, hp₂B⟩
    simp only [RA_set, RB_set, rootedSubtreesIn, Finset.mem_filter] at hp₁A hp₁B hp₂A hp₂B
    have h1A : p₁.1 ⊆ A := hp₁A.2.1
    have h1B : p₁.2 ⊆ B := hp₁B.2.1
    have h2A : p₂.1 ⊆ A := hp₂A.2.1
    have h2B : p₂.2 ⊆ B := hp₂B.2.1
    have h1 : p₁.1 = p₂.1 := by
      calc p₁.1 = (p₁.1 ∪ p₁.2) ∩ A := (h_inter_left h1A h1B).symm
        _ = (p₂.1 ∪ p₂.2) ∩ A := by rw [show p₁.1 ∪ p₁.2 = p₂.1 ∪ p₂.2 from h_eq]
        _ = p₂.1 := h_inter_left h2A h2B
    have h2 : p₁.2 = p₂.2 := by
      calc p₁.2 = (p₁.1 ∪ p₁.2) ∩ B := (h_inter_right h1A h1B).symm
        _ = (p₂.1 ∪ p₂.2) ∩ B := by rw [show p₁.1 ∪ p₁.2 = p₂.1 ∪ p₂.2 from h_eq]
        _ = p₂.2 := h_inter_right h2A h2B
    exact Prod.ext h1 h2
  have hM_card : M.card = rootedCount G A w * rootedCount G B r_B := by
    dsimp [M, RA_set, RB_set, rootedCount]
    rw [Finset.card_image_of_injOn h_inj, Finset.card_product]
  have hM_sum : ∑ S ∈ M, S.card =
      rootedOrderSum G A w * rootedCount G B r_B + rootedCount G A w * rootedOrderSum G B r_B := by
    dsimp [M]
    rw [Finset.sum_image h_inj, Finset.sum_product]
    have h_inner : ∀ x ∈ RA_set,
        ∑ y ∈ RB_set, (x ∪ y).card = x.card * RB_set.card + ∑ y ∈ RB_set, y.card := by
      intro x hx
      simp only [RA_set, rootedSubtreesIn, Finset.mem_filter] at hx
      have hx_sub : x ⊆ A := hx.2.1
      have h_congr : ∑ y ∈ RB_set, (x ∪ y).card = ∑ y ∈ RB_set, (x.card + y.card) := by
        refine Finset.sum_congr rfl fun y hy => ?_
        simp only [RB_set, rootedSubtreesIn, Finset.mem_filter] at hy
        have hy_sub : y ⊆ B := hy.2.1
        exact Finset.card_union_of_disjoint (Disjoint.mono hx_sub hy_sub hJ.1)
      rw [h_congr, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
    rw [Finset.sum_congr rfl h_inner, Finset.sum_add_distrib, ← Finset.sum_mul,
      Finset.sum_const, smul_eq_mul]
    rfl
  have h_mem_M : ∀ S : Finset (Fin n),
      S ∈ M ↔ S ∈ subtreesIn G (A ∪ B) ∧ (S ∩ A).Nonempty ∧ (S ∩ B).Nonempty := by
    intro S
    constructor
    · intro hS
      obtain ⟨⟨SA, SB⟩, hp, rfl⟩ := Finset.mem_image.mp hS
      rcases Finset.mem_product.mp hp with ⟨hSA, hSB⟩
      have hSA' := hSA
      have hSB' := hSB
      simp only [RA_set, RB_set, rootedSubtreesIn, subtrees, Finset.mem_filter,
        Finset.mem_univ, true_and] at hSA' hSB'
      have h_sub_AB : SA ∪ SB ⊆ A ∪ B := Finset.union_subset_union hSA'.2.1 hSB'.2.1
      have h_tree : IsSubtree G (SA ∪ SB) := bridge_union_isSubtree hJ hSA hSB
      have h_in_sub : SA ∪ SB ∈ subtreesIn G (A ∪ B) := by
        simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨h_tree, h_sub_AB⟩
      have h_ne_A : ((SA ∪ SB) ∩ A).Nonempty := by
        rw [h_inter_left hSA'.2.1 hSB'.2.1]
        exact ⟨w, hSA'.2.2⟩
      have h_ne_B : ((SA ∪ SB) ∩ B).Nonempty := by
        rw [h_inter_right hSA'.2.1 hSB'.2.1]
        exact ⟨r_B, hSB'.2.2⟩
      exact ⟨h_in_sub, h_ne_A, h_ne_B⟩
    · rintro ⟨hS_in, hSA_ne, hSB_ne⟩
      simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hS_in
      rcases hS_in with ⟨hS_tree, hS_sub⟩
      have hSA_mem : S ∩ A ∈ RA_set := bridge_crossing_left hJ hS_sub hS_tree hSA_ne hSB_ne
      have hS_sub' : S ⊆ B ∪ A := by simpa [Finset.union_comm] using hS_sub
      have hSB_mem : S ∩ B ∈ RB_set :=
        bridge_crossing_left (isBridgeJoin_symm hJ) hS_sub' hS_tree hSB_ne hSA_ne
      refine Finset.mem_image.mpr ⟨(S ∩ A, S ∩ B), Finset.mem_product.mpr ⟨hSA_mem, hSB_mem⟩, ?_⟩
      dsimp [φ]
      rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hS_sub]
  have h_sub_of_inter_empty_right : ∀ {S : Finset (Fin n)}, S ⊆ A ∪ B → S ∩ B = ∅ → S ⊆ A := by
    intro S hS h_emp z hz
    rcases Finset.mem_union.mp (hS hz) with hzA | hzB
    · exact hzA
    · exfalso
      have : z ∈ (∅ : Finset (Fin n)) := h_emp ▸ Finset.mem_inter.mpr ⟨hz, hzB⟩
      exact Finset.notMem_empty z this
  have h_sub_of_inter_empty_left : ∀ {S : Finset (Fin n)}, S ⊆ A ∪ B → S ∩ A = ∅ → S ⊆ B := by
    intro S hS h_emp z hz
    rcases Finset.mem_union.mp (hS hz) with hzA | hzB
    · exfalso
      have : z ∈ (∅ : Finset (Fin n)) := h_emp ▸ Finset.mem_inter.mpr ⟨hz, hzA⟩
      exact Finset.notMem_empty z this
    · exact hzB
  have h_sub_AB_disj : Disjoint (subtreesIn G A) (subtreesIn G B) := by
    rw [Finset.disjoint_left]
    intro S hSA hSB
    simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hSA hSB
    obtain ⟨x, hx⟩ := hSA.1.1
    exact Finset.disjoint_left.mp hJ.1 (hSA.2 hx) (hSB.2 hx)
  have h_sub_M_disj : Disjoint (subtreesIn G A ∪ subtreesIn G B) M := by
    rw [Finset.disjoint_left]
    intro S hS_AB hS_M
    obtain ⟨_, ⟨a, ha⟩, ⟨b, hb⟩⟩ := (h_mem_M S).mp hS_M
    rcases Finset.mem_union.mp hS_AB with hSA | hSB
    · simp only [subtreesIn, Finset.mem_filter] at hSA
      have hS_A : S ⊆ A := hSA.2
      exact Finset.disjoint_left.mp hJ.1 (hS_A (Finset.mem_inter.mp hb).1) (Finset.mem_inter.mp hb).2
    · simp only [subtreesIn, Finset.mem_filter] at hSB
      have hS_B : S ⊆ B := hSB.2
      exact Finset.disjoint_left.mp hJ.1 (Finset.mem_inter.mp ha).2 (hS_B (Finset.mem_inter.mp ha).1)
  have h_sub_part : subtreesIn G (A ∪ B) = (subtreesIn G A ∪ subtreesIn G B) ∪ M := by
    ext S
    rw [Finset.mem_union, Finset.mem_union, h_mem_M]
    constructor
    · intro hS
      have hS' := hS
      simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hS'
      rcases hS' with ⟨hS_tree, hS_sub⟩
      rcases Finset.eq_empty_or_nonempty (S ∩ B) with hB_emp | hSB_ne
      · left; left
        simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hS_tree, h_sub_of_inter_empty_right hS_sub hB_emp⟩
      · rcases Finset.eq_empty_or_nonempty (S ∩ A) with hA_emp | hSA_ne
        · left; right
          simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hS_tree, h_sub_of_inter_empty_left hS_sub hA_emp⟩
        · right
          exact ⟨hS, hSA_ne, hSB_ne⟩
    · rintro ((hSA | hSB) | ⟨hS, _, _⟩)
      · simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hSA ⊢
        exact ⟨hSA.1, Finset.Subset.trans hSA.2 Finset.subset_union_left⟩
      · simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and] at hSB ⊢
        exact ⟨hSB.1, Finset.Subset.trans hSB.2 Finset.subset_union_right⟩
      · exact hS
  have h_eq1 : unrootedCount G (A ∪ B) =
      unrootedCount G A + unrootedCount G B + rootedCount G A w * rootedCount G B r_B := by
    dsimp [unrootedCount]
    rw [h_sub_part, Finset.card_union_of_disjoint h_sub_M_disj,
      Finset.card_union_of_disjoint h_sub_AB_disj, hM_card]
  have h_eq2 : unrootedOrderSum G (A ∪ B) =
      unrootedOrderSum G A + unrootedOrderSum G B +
      rootedOrderSum G A w * rootedCount G B r_B +
      rootedCount G A w * rootedOrderSum G B r_B := by
    dsimp [unrootedOrderSum]
    rw [h_sub_part, Finset.sum_union h_sub_M_disj,
      Finset.sum_union h_sub_AB_disj, hM_sum]
    ring
  exact ⟨hSub_AB, h_eq1, h_eq2⟩

theorem pendant_packet_and_spine_moments : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    (∀ (U L : Finset (Fin n)) (r : Fin n),
      IsSubtree G U → r ∈ U → Disjoint U L → IsLeafPacket G L r →
      IsSubtree G (U ∪ L) ∧
      (rootedCount G (U ∪ L) r : ℚ) = (2 : ℚ) ^ L.card * (rootedCount G U r : ℚ) ∧
      (rootedOrderSum G (U ∪ L) r : ℚ) =
        (2 : ℚ) ^ L.card * (rootedOrderSum G U r : ℚ) +
        (L.card : ℚ) * (2 : ℚ) ^ L.card / 2 * (rootedCount G U r : ℚ) ∧
      (unrootedCount G (U ∪ L) : ℚ) =
        (unrootedCount G U : ℚ) + (L.card : ℚ) +
        ((2 : ℚ) ^ L.card - 1) * (rootedCount G U r : ℚ) ∧
      (unrootedOrderSum G (U ∪ L) : ℚ) =
        (unrootedOrderSum G U : ℚ) + (L.card : ℚ) +
        ((2 : ℚ) ^ L.card - 1) * (rootedOrderSum G U r : ℚ) +
        (L.card : ℚ) * (2 : ℚ) ^ L.card / 2 * (rootedCount G U r : ℚ)) ∧
    (∀ (ℓ : ℕ) (U : Finset (Fin n)) (w₀ : Fin n) (v : Fin (ℓ + 1) → Fin n),
      Function.Injective v →
      IsSubtree G U →
      Disjoint U (Finset.univ.image v) →
      IsBridgeJoin G U (Finset.univ.image v) w₀ (v 0) →
      (∀ i j : Fin (ℓ + 1), G.Adj (v i) (v j) ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val)) →
      let W := U ∪ (Finset.univ.image v)
      let h : ℚ := (ℓ : ℚ) + 1
      IsSubtree G W ∧
      (rootedCount G W (v (Fin.last ℓ)) : ℚ) = (rootedCount G U w₀ : ℚ) + h ∧
      (rootedOrderSum G W (v (Fin.last ℓ)) : ℚ) =
        (rootedOrderSum G U w₀ : ℚ) + h * (rootedCount G U w₀ : ℚ) + h * (h + 1) / 2 ∧
      (unrootedCount G W : ℚ) =
        (unrootedCount G U : ℚ) + h * (rootedCount G U w₀ : ℚ) + h * (h + 1) / 2 ∧
      (unrootedOrderSum G W : ℚ) =
        (unrootedOrderSum G U : ℚ) + h * (rootedOrderSum G U w₀ : ℚ) +
        h * (h + 1) / 2 * (rootedCount G U w₀ : ℚ) + h * (h + 1) * (h + 2) / 6) :=
by
  intro n G
  have isSubtree_insert_leaf_iff : ∀ (U S₀ : Finset (Fin n)) (z r : Fin n),
      z ∉ U → r ∈ U → (∀ y ∈ insert z U, G.Adj z y ↔ y = r) → S₀ ⊆ U →
      (IsSubtree G (insert z S₀) ↔ S₀ = ∅ ∨ (IsSubtree G S₀ ∧ r ∈ S₀)) := by
    intro U S₀ z r hz hr hadj hS₀
    have hzr : z ≠ r := fun h => hz (h ▸ hr)
    have hzS₀ : z ∉ S₀ := fun h => hz (hS₀ h)
    rcases S₀.eq_empty_or_nonempty with rfl | hS₀_ne
    · simp only [Finset.insert_empty, true_or, iff_true]
      refine ⟨Finset.singleton_nonempty z, ?_⟩
      rw [SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨⟨z, by simp⟩, fun ⟨w, hw⟩ => ?_⟩
      have hwz : w = z := by simpa using hw
      subst hwz
      exact SimpleGraph.Reachable.rfl
    · simp only [hS₀_ne.ne_empty, false_or]
      let S : Finset (Fin n) := insert z S₀
      change IsSubtree G S ↔ IsSubtree G S₀ ∧ r ∈ S₀
      constructor
      · intro hS
        have hr_mem : r ∈ S₀ := by
          obtain ⟨a, ha⟩ := hS₀_ne
          have h_walk : ∀ (u w : ↑(S : Set (Fin n))) (pw : (G.induce (S : Set (Fin n))).Walk u w),
              u.1 = z → w.1 ∈ S₀ → r ∈ S₀ := by
            intro u w pw huz hwS₀
            cases pw with
            | nil =>
              exact False.elim (hzS₀ (huz ▸ hwS₀))
            | @cons _ b _ hadj_step _ =>
              have hb_mem : b.1 ∈ insert z S₀ := b.2
              have hb_U : b.1 ∈ insert z U := Finset.insert_subset_insert z hS₀ hb_mem
              have hbr : b.1 = r := (hadj b.1 hb_U).mp (huz ▸ hadj_step)
              rcases Finset.mem_insert.mp hb_mem with hbz | hbS₀
              · exact False.elim (hzr (hbz.symm.trans hbr))
              · exact hbr ▸ hbS₀
          obtain ⟨pw⟩ := hS.2.preconnected
            ⟨z, Finset.mem_coe.mpr (Finset.mem_insert_self z S₀)⟩
            ⟨a, Finset.mem_coe.mpr (Finset.mem_insert_of_mem ha)⟩
          exact h_walk _ _ pw rfl ha
        refine ⟨⟨hS₀_ne, ?_⟩, hr_mem⟩
        rw [SimpleGraph.connected_iff_exists_forall_reachable]
        let φ : ↑(S : Set (Fin n)) → ↑(S₀ : Set (Fin n)) := fun x =>
          ⟨if x.1 = z then r else x.1, by
            by_cases hx : x.1 = z
            · simp [hx, hr_mem]
            · simp only [hx, ↓reduceIte, Finset.mem_coe]
              rcases Finset.mem_insert.mp x.2 with hxz | h
              · exact False.elim (hx hxz)
              · exact h⟩
        have hφ_mem : ∀ (a : Fin n) (ha : a ∈ S₀),
            φ ⟨a, Finset.mem_coe.mpr (Finset.mem_insert_of_mem ha)⟩ = ⟨a, ha⟩ := by
          intro a ha
          have haz : a ≠ z := fun h => hzS₀ (h ▸ ha)
          ext
          simp [φ, haz]
        have hφ_adj : ∀ x y : ↑(S : Set (Fin n)),
            (G.induce (S : Set (Fin n))).Adj x y →
            (G.induce (S₀ : Set (Fin n))).Reachable (φ x) (φ y) := by
          intro x y hxy
          change G.Adj x.1 y.1 at hxy
          by_cases hx : x.1 = z
          · have hy_U : y.1 ∈ insert z U := Finset.insert_subset_insert z hS₀ y.2
            have hyr : y.1 = r := (hadj y.1 hy_U).mp (hx ▸ hxy)
            have hφ_eq : φ x = φ y := by
              ext
              simp [φ, hx, hyr]
            rw [hφ_eq]
          · by_cases hy : y.1 = z
            · have hx_U : x.1 ∈ insert z U := Finset.insert_subset_insert z hS₀ x.2
              have hxr : x.1 = r := (hadj x.1 hx_U).mp (hy ▸ G.symm hxy)
              have hφ_eq : φ x = φ y := by
                ext
                simp [φ, hy, hxr]
              rw [hφ_eq]
            · apply SimpleGraph.Adj.reachable
              change G.Adj (φ x).1 (φ y).1
              simp [φ, hx, hy, hxy]
        have hφ_walk : ∀ (x y : ↑(S : Set (Fin n)))
            (pw : (G.induce (S : Set (Fin n))).Walk x y),
            (G.induce (S₀ : Set (Fin n))).Reachable (φ x) (φ y) := by
          intro x y pw
          induction pw with
          | nil => exact SimpleGraph.Reachable.rfl
          | cons h_step _ ih => exact (hφ_adj _ _ h_step).trans ih
        refine ⟨⟨r, hr_mem⟩, fun ⟨b, hb⟩ => ?_⟩
        obtain ⟨pw⟩ := hS.2.preconnected
          ⟨r, Finset.mem_coe.mpr (Finset.mem_insert_of_mem hr_mem)⟩
          ⟨b, Finset.mem_coe.mpr (Finset.mem_insert_of_mem hb)⟩
        have h_reach := hφ_walk _ _ pw
        rwa [hφ_mem r hr_mem, hφ_mem b hb] at h_reach
      · rintro ⟨hS₀_sub, hr_mem⟩
        refine ⟨Finset.insert_nonempty z S₀, ?_⟩
        rw [SimpleGraph.connected_iff_exists_forall_reachable]
        let ι : ↑(S₀ : Set (Fin n)) → ↑(S : Set (Fin n)) :=
          fun x => ⟨x.1, Finset.mem_coe.mpr (Finset.mem_insert_of_mem x.2)⟩
        have hι_walk : ∀ (x y : ↑(S₀ : Set (Fin n))) (pw : (G.induce (S₀ : Set (Fin n))).Walk x y),
            (G.induce (S : Set (Fin n))).Reachable (ι x) (ι y) := by
          intro x y pw
          induction pw with
          | nil => exact SimpleGraph.Reachable.rfl
          | cons h_step _ ih =>
            have h_step' : (G.induce (S : Set (Fin n))).Adj (ι _) (ι _) := h_step
            exact h_step'.reachable.trans ih
        refine ⟨ι ⟨r, hr_mem⟩, fun ⟨b, hb⟩ => ?_⟩
        rcases Finset.mem_insert.mp hb with hbz | hbS₀
        · subst b
          apply SimpleGraph.Adj.reachable
          change G.Adj r z
          exact G.symm ((hadj r (Finset.mem_insert_of_mem hr)).mpr rfl)
        · obtain ⟨pw⟩ := hS₀_sub.2.preconnected ⟨r, hr_mem⟩ ⟨b, hbS₀⟩
          exact hι_walk _ _ pw
  have leaf_ext_moments_Q : ∀ (U : Finset (Fin n)) (z r : Fin n),
      z ∉ U → r ∈ U → (∀ y ∈ insert z U, G.Adj z y ↔ y = r) → IsSubtree G U →
      IsSubtree G (insert z U) ∧
      (rootedCount G (insert z U) z : ℚ) = (rootedCount G U r : ℚ) + 1 ∧
      (rootedOrderSum G (insert z U) z : ℚ) =
        (rootedOrderSum G U r : ℚ) + (rootedCount G U r : ℚ) + 1 ∧
      (unrootedCount G (insert z U) : ℚ) =
        (unrootedCount G U : ℚ) + (rootedCount G U r : ℚ) + 1 ∧
      (unrootedOrderSum G (insert z U) : ℚ) =
        (unrootedOrderSum G U : ℚ) +
        (rootedOrderSum G U r : ℚ) + (rootedCount G U r : ℚ) + 1 ∧
      (rootedCount G (insert z U) r : ℚ) = 2 * (rootedCount G U r : ℚ) ∧
      (rootedOrderSum G (insert z U) r : ℚ) =
        2 * (rootedOrderSum G U r : ℚ) + (rootedCount G U r : ℚ) := by
    intro U z r hz hr hadj hSubU
    have h_ext : ∀ S₀ ⊆ U, IsSubtree G (insert z S₀) ↔ S₀ = ∅ ∨ (IsSubtree G S₀ ∧ r ∈ S₀) :=
      fun S₀ hS₀ => isSubtree_insert_leaf_iff U S₀ z r hz hr hadj hS₀
    have h_sub_ins : IsSubtree G (insert z U) :=
      (h_ext U Finset.Subset.rfl).mpr (Or.inr ⟨hSubU, hr⟩)
    have hzr : z ≠ r := fun h => hz (h ▸ hr)
    have h_mem_rooted : ∀ W r' S, S ∈ rootedSubtreesIn G W r' ↔ IsSubtree G S ∧ S ⊆ W ∧ r' ∈ S := by
      intro W r' S
      simp [rootedSubtreesIn, subtrees]
    have h_mem_subtreesIn : ∀ W S, S ∈ subtreesIn G W ↔ IsSubtree G S ∧ S ⊆ W := by
      intro W S
      simp [subtreesIn, subtrees]
    have h_rooted_z : rootedSubtreesIn G (insert z U) z =
        insert ({z} : Finset (Fin n)) ((rootedSubtreesIn G U r).image (insert z)) := by
      ext S
      simp only [Finset.mem_insert, Finset.mem_image, h_mem_rooted]
      constructor
      · rintro ⟨hS_sub, hS_U, hzS⟩
        let S₀ := S.erase z
        have hS₀_U : S₀ ⊆ U := by
          intro w hw
          rcases Finset.mem_insert.mp (hS_U (Finset.mem_of_mem_erase hw)) with rfl | hwU
          · exact False.elim ((Finset.mem_erase.mp hw).1 rfl)
          · exact hwU
        have h_ins : insert z S₀ = S := Finset.insert_erase hzS
        have hS_iff := (h_ext S₀ hS₀_U).mp (h_ins.symm ▸ hS_sub)
        rcases hS_iff with h_emp | ⟨hS₀_tree, hrS₀⟩
        · left
          rw [← h_ins, h_emp, Finset.insert_empty]
        · right
          exact ⟨S₀, ⟨hS₀_tree, hS₀_U, hrS₀⟩, h_ins⟩
      · rintro (rfl | ⟨S₀, ⟨hS₀_tree, hS₀_U, hrS₀⟩, rfl⟩)
        · have h_emp : IsSubtree G (insert z ∅) := (h_ext ∅ (Finset.empty_subset U)).mpr (Or.inl rfl)
          simpa using h_emp
        · refine ⟨(h_ext S₀ hS₀_U).mpr (Or.inr ⟨hS₀_tree, hrS₀⟩),
            Finset.insert_subset_insert z hS₀_U, Finset.mem_insert_self z S₀⟩
    have h_notMem_img : ({z} : Finset (Fin n)) ∉ (rootedSubtreesIn G U r).image (insert z) := by
      simp only [Finset.mem_image, not_exists, not_and]
      intro S₀ hS₀ h_eq
      have hrS₀ : r ∈ S₀ := ((h_mem_rooted U r S₀).mp hS₀).2.2
      have hrz : r ∈ ({z} : Finset (Fin n)) := h_eq ▸ Finset.mem_insert_of_mem hrS₀
      exact hzr (Finset.mem_singleton.mp hrz).symm
    have h_inj : Set.InjOn (insert z) (rootedSubtreesIn G U r : Set (Finset (Fin n))) := by
      intro S₁ hS₁ S₂ hS₂ h_eq
      have hz₁ : z ∉ S₁ := fun h => hz (((h_mem_rooted U r S₁).mp hS₁).2.1 h)
      have hz₂ : z ∉ S₂ := fun h => hz (((h_mem_rooted U r S₂).mp hS₂).2.1 h)
      have := congrArg (fun S : Finset (Fin n) => S.erase z) h_eq
      simpa [Finset.erase_insert hz₁, Finset.erase_insert hz₂] using this
    have h_rc_z : rootedCount G (insert z U) z = rootedCount G U r + 1 := by
      change (rootedSubtreesIn G (insert z U) z).card = (rootedSubtreesIn G U r).card + 1
      rw [h_rooted_z, Finset.card_insert_of_notMem h_notMem_img, Finset.card_image_of_injOn h_inj]
    have h_sum_img : ∑ S ∈ (rootedSubtreesIn G U r).image (insert z), S.card =
        rootedOrderSum G U r + rootedCount G U r := by
      rw [Finset.sum_image h_inj]
      have h_congr : ∑ S₀ ∈ rootedSubtreesIn G U r, (insert z S₀).card =
          ∑ S₀ ∈ rootedSubtreesIn G U r, (S₀.card + 1) := by
        refine Finset.sum_congr rfl (fun S₀ hS₀ => ?_)
        have hzS₀ : z ∉ S₀ := fun h => hz (((h_mem_rooted U r S₀).mp hS₀).2.1 h)
        exact Finset.card_insert_of_notMem hzS₀
      rw [h_congr, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
      rfl
    have h_ros_z : rootedOrderSum G (insert z U) z =
        rootedOrderSum G U r + rootedCount G U r + 1 := by
      change ∑ S ∈ rootedSubtreesIn G (insert z U) z, S.card =
        rootedOrderSum G U r + rootedCount G U r + 1
      rw [h_rooted_z, Finset.sum_insert h_notMem_img, Finset.card_singleton, h_sum_img]
      omega
    have h_subtrees_union : subtreesIn G (insert z U) =
        subtreesIn G U ∪ rootedSubtreesIn G (insert z U) z := by
      ext S
      simp only [Finset.mem_union, h_mem_subtreesIn, h_mem_rooted]
      constructor
      · rintro ⟨hS_tree, hS_sub⟩
        by_cases hzS : z ∈ S
        · exact Or.inr ⟨hS_tree, hS_sub, hzS⟩
        · left
          refine ⟨hS_tree, fun w hw => ?_⟩
          rcases Finset.mem_insert.mp (hS_sub hw) with rfl | hwU
          · exact False.elim (hzS hw)
          · exact hwU
      · rintro (⟨hS_tree, hS_U⟩ | ⟨hS_tree, hS_sub, _⟩)
        · exact ⟨hS_tree, Finset.Subset.trans hS_U (Finset.subset_insert z U)⟩
        · exact ⟨hS_tree, hS_sub⟩
    have h_subtrees_disj : Disjoint (subtreesIn G U) (rootedSubtreesIn G (insert z U) z) := by
      rw [Finset.disjoint_left]
      intro S hS₁ hS₂
      have hS_U : S ⊆ U := ((h_mem_subtreesIn U S).mp hS₁).2
      exact hz (hS_U ((h_mem_rooted (insert z U) z S).mp hS₂).2.2)
    have h_sc_z : unrootedCount G (insert z U) =
        unrootedCount G U + rootedCount G U r + 1 := by
      change (subtreesIn G (insert z U)).card = (subtreesIn G U).card + rootedCount G U r + 1
      rw [h_subtrees_union, Finset.card_union_of_disjoint h_subtrees_disj]
      change (subtreesIn G U).card + rootedCount G (insert z U) z = _
      rw [h_rc_z]
      omega
    have h_sos_z : unrootedOrderSum G (insert z U) =
        unrootedOrderSum G U + rootedOrderSum G U r + rootedCount G U r + 1 := by
      change (∑ S ∈ subtreesIn G (insert z U), S.card) =
        (∑ S ∈ subtreesIn G U, S.card) + rootedOrderSum G U r + rootedCount G U r + 1
      rw [h_subtrees_union, Finset.sum_union h_subtrees_disj]
      change (∑ S ∈ subtreesIn G U, S.card) + rootedOrderSum G (insert z U) z = _
      rw [h_ros_z]
      omega
    have h_rooted_r : rootedSubtreesIn G (insert z U) r =
        rootedSubtreesIn G U r ∪ (rootedSubtreesIn G U r).image (insert z) := by
      ext S
      simp only [Finset.mem_union, Finset.mem_image, h_mem_rooted]
      constructor
      · rintro ⟨hS_tree, hS_sub, hrS⟩
        by_cases hzS : z ∈ S
        · right
          let S₀ := S.erase z
          have hS₀_U : S₀ ⊆ U := by
            intro w hw
            rcases Finset.mem_insert.mp (hS_sub (Finset.mem_of_mem_erase hw)) with rfl | hwU
            · exact False.elim ((Finset.mem_erase.mp hw).1 rfl)
            · exact hwU
          have h_ins : insert z S₀ = S := Finset.insert_erase hzS
          have hrS₀ : r ∈ S₀ := Finset.mem_erase.mpr ⟨hzr.symm, hrS⟩
          have hS_iff := (h_ext S₀ hS₀_U).mp (h_ins.symm ▸ hS_tree)
          rcases hS_iff with h_emp | ⟨hS₀_tree, _⟩
          · simp [h_emp] at hrS₀
          · exact ⟨S₀, ⟨hS₀_tree, hS₀_U, hrS₀⟩, h_ins⟩
        · left
          refine ⟨hS_tree, fun w hw => ?_, hrS⟩
          rcases Finset.mem_insert.mp (hS_sub hw) with rfl | hwU
          · exact False.elim (hzS hw)
          · exact hwU
      · rintro (⟨hS_tree, hS_U, hrS⟩ | ⟨S₀, ⟨hS₀_tree, hS₀_U, hrS₀⟩, rfl⟩)
        · exact ⟨hS_tree, Finset.Subset.trans hS_U (Finset.subset_insert z U), hrS⟩
        · exact ⟨(h_ext S₀ hS₀_U).mpr (Or.inr ⟨hS₀_tree, hrS₀⟩),
            Finset.insert_subset_insert z hS₀_U, Finset.mem_insert_of_mem hrS₀⟩
    have h_rooted_r_disj : Disjoint (rootedSubtreesIn G U r)
        ((rootedSubtreesIn G U r).image (insert z)) := by
      rw [Finset.disjoint_left]
      intro S hS₁ hS₂
      have hS_U : S ⊆ U := ((h_mem_rooted U r S).mp hS₁).2.1
      rcases Finset.mem_image.mp hS₂ with ⟨S₀, _, rfl⟩
      exact hz (hS_U (Finset.mem_insert_self z S₀))
    have h_rc_r : rootedCount G (insert z U) r = 2 * rootedCount G U r := by
      change (rootedSubtreesIn G (insert z U) r).card = 2 * (rootedSubtreesIn G U r).card
      rw [h_rooted_r, Finset.card_union_of_disjoint h_rooted_r_disj, Finset.card_image_of_injOn h_inj]
      omega
    have h_ros_r : rootedOrderSum G (insert z U) r =
        2 * rootedOrderSum G U r + rootedCount G U r := by
      change ∑ S ∈ rootedSubtreesIn G (insert z U) r, S.card =
        2 * rootedOrderSum G U r + rootedCount G U r
      rw [h_rooted_r, Finset.sum_union h_rooted_r_disj, h_sum_img]
      change rootedOrderSum G U r + (rootedOrderSum G U r + rootedCount G U r) = _
      omega
    refine ⟨h_sub_ins, by exact_mod_cast h_rc_z, by exact_mod_cast h_ros_z,
      by exact_mod_cast h_sc_z, by exact_mod_cast h_sos_z,
      by exact_mod_cast h_rc_r, by exact_mod_cast h_ros_r⟩
  refine ⟨?_, ?_⟩
  · intro U L r hSubU hrU
    induction L using Finset.induction_on with
    | empty =>
      intro _ _
      simp only [Finset.union_empty, Finset.card_empty, Nat.cast_zero, pow_zero]
      exact ⟨hSubU, by ring, by ring, by ring, by ring⟩
    | @insert x L₀ hx_L₀ ih =>
      intro hdisj hpkt
      have hx_U : x ∉ U := (Finset.disjoint_insert_right.mp hdisj).1
      have hdisj₀ : Disjoint U L₀ := (Finset.disjoint_insert_right.mp hdisj).2
      have hx_leaf : IsLeafIn G x r := hpkt x (Finset.mem_insert_self x L₀)
      have hpkt₀ : IsLeafPacket G L₀ r := fun y hy => hpkt y (Finset.mem_insert_of_mem hy)
      obtain ⟨ih_sub, ih_s, ih_t, ih_N, ih_R⟩ := ih hdisj₀ hpkt₀
      let U' := U ∪ L₀
      have hU_ins : U ∪ insert x L₀ = insert x U' := Finset.union_insert x U L₀
      have hx_U' : x ∉ U' := Finset.notMem_union.mpr ⟨hx_U, hx_L₀⟩
      have hr_U' : r ∈ U' := Finset.mem_union_left L₀ hrU
      have hadj_x : ∀ y ∈ insert x U', G.Adj x y ↔ y = r := fun y _ => hx_leaf y
      obtain ⟨h_sub, _, _, h_N, h_R, h_s, h_t⟩ :=
        leaf_ext_moments_Q U' x r hx_U' hr_U' hadj_x ih_sub
      have hcard : ((insert x L₀).card : ℚ) = (L₀.card : ℚ) + 1 := by
        rw [Finset.card_insert_of_notMem hx_L₀, Nat.cast_add, Nat.cast_one]
      have hpow : (2 : ℚ) ^ (insert x L₀).card = (2 : ℚ) ^ L₀.card * 2 := by
        rw [Finset.card_insert_of_notMem hx_L₀, pow_succ]
      rw [hU_ins, hcard, hpow]
      refine ⟨h_sub, ?_, ?_, ?_, ?_⟩
      · rw [h_s]; dsimp [U'] at ih_s ⊢; rw [ih_s]; ring
      · rw [h_t]; dsimp [U'] at ih_s ih_t ⊢; rw [ih_s, ih_t]; ring
      · rw [h_N]; dsimp [U'] at ih_s ih_N ⊢; rw [ih_s, ih_N]; ring
      · rw [h_R]; dsimp [U'] at ih_s ih_t ih_R ⊢; rw [ih_s, ih_t, ih_R]; ring
  · intro ℓ U w₀ v hv hSubU hdisj_Uv hBridge hSpine
    dsimp only
    have hv_mem_img : ∀ i : Fin (ℓ + 1), v i ∈ Finset.univ.image v :=
      fun i => Finset.mem_image_of_mem v (Finset.mem_univ i)
    let W_k : ℕ → Finset (Fin n) := fun k =>
      U ∪ (Finset.univ.filter (fun i : Fin (ℓ + 1) => i.val ≤ k)).image v
    let s_U : ℚ := rootedCount G U w₀
    let t_U : ℚ := rootedOrderSum G U w₀
    let N_U : ℚ := unrootedCount G U
    let R_U : ℚ := unrootedOrderSum G U
    have h_spine_ind : ∀ (k : ℕ) (hk : k ≤ ℓ),
        let v_k := v ⟨k, Nat.lt_succ_of_le hk⟩
        let h_k : ℚ := (k : ℚ) + 1
        IsSubtree G (W_k k) ∧
        (rootedCount G (W_k k) v_k : ℚ) = s_U + h_k ∧
        (rootedOrderSum G (W_k k) v_k : ℚ) =
          t_U + h_k * s_U + h_k * (h_k + 1) / 2 ∧
        (unrootedCount G (W_k k) : ℚ) =
          N_U + h_k * s_U + h_k * (h_k + 1) / 2 ∧
        (unrootedOrderSum G (W_k k) : ℚ) =
          R_U + h_k * t_U + h_k * (h_k + 1) / 2 * s_U +
          h_k * (h_k + 1) * (h_k + 2) / 6 := by
      intro k
      induction k with
      | zero =>
        intro hk
        have h_flt0 : Finset.univ.filter (fun i : Fin (ℓ + 1) => i.val ≤ 0) = {0} := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro hi
            exact Fin.ext (by change i.val ≤ 0 at hi; change i.val = 0; omega)
          · rintro rfl
            exact le_rfl
        have hW0_eq : W_k 0 = insert (v 0) U := by
          dsimp [W_k]
          rw [h_flt0, Finset.image_singleton]
          ext x
          simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
          tauto
        have hv0_eq : v ⟨0, Nat.lt_succ_of_le hk⟩ = v 0 := rfl
        have hv0_notMem_U : v 0 ∉ U := Finset.disjoint_right.mp hdisj_Uv (hv_mem_img 0)
        have hw0_mem_U : w₀ ∈ U := hBridge.2.1
        have hadj_v0 : ∀ y ∈ insert (v 0) U, G.Adj (v 0) y ↔ y = w₀ := by
          intro y hy
          constructor
          · intro hadj
            have hy_ne : y ≠ v 0 := fun h => G.loopless (v 0) (h ▸ hadj)
            have hy_U : y ∈ U := by
              rcases Finset.mem_insert.mp hy with rfl | h
              · exact False.elim (hy_ne rfl)
              · exact h
            exact (hBridge.2.2.2.2 y hy_U (v 0) (hv_mem_img 0) (G.symm hadj)).1
          · rintro rfl
            exact G.symm hBridge.2.2.2.1
        obtain ⟨hU0_sub, hU0_s, hU0_t, hU0_N, hU0_R, _, _⟩ :=
          leaf_ext_moments_Q U (v 0) w₀ hv0_notMem_U hw0_mem_U hadj_v0 hSubU
        dsimp only
        rw [hW0_eq, hv0_eq, Nat.cast_zero]
        refine ⟨hU0_sub, ?_, ?_, ?_, ?_⟩
        · rw [hU0_s]; dsimp [s_U]; ring
        · rw [hU0_t]; dsimp [s_U, t_U]; ring
        · rw [hU0_N]; dsimp [s_U, N_U]; ring
        · rw [hU0_R]; dsimp [s_U, t_U, R_U]; ring
      | succ k ih =>
        intro hk1
        have hk : k ≤ ℓ := Nat.le_of_succ_le hk1
        obtain ⟨ih_sub, ih_s, ih_t, ih_N, ih_R⟩ := ih hk
        let i_k : Fin (ℓ + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
        let i_k1 : Fin (ℓ + 1) := ⟨k + 1, Nat.lt_succ_of_le hk1⟩
        have h_flt_succ : Finset.univ.filter (fun i : Fin (ℓ + 1) => i.val ≤ k + 1) =
            insert i_k1 (Finset.univ.filter (fun i : Fin (ℓ + 1) => i.val ≤ k)) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · intro hi
            by_cases hik : i.val = k + 1
            · left; exact Fin.ext hik
            · right; omega
          · rintro (rfl | hi)
            · exact le_rfl
            · omega
        have hW_succ : W_k (k + 1) = insert (v i_k1) (W_k k) := by
          dsimp [W_k]
          rw [h_flt_succ, Finset.image_insert]
          ext x
          simp only [Finset.mem_union, Finset.mem_insert]
          tauto
        have hv_notMem_Wk : v i_k1 ∉ W_k k := by
          intro h_mem
          dsimp [W_k] at h_mem
          rcases Finset.mem_union.mp h_mem with h_U | h_img
          · exact Finset.disjoint_right.mp hdisj_Uv (hv_mem_img i_k1) h_U
          · rcases Finset.mem_image.mp h_img with ⟨i, hi_flt, hvi⟩
            have hi_le : i.val ≤ k := (Finset.mem_filter.mp hi_flt).2
            have hi_eq : i = i_k1 := hv hvi
            have : i.val = k + 1 := congrArg Fin.val hi_eq
            omega
        have hvk_mem_Wk : v i_k ∈ W_k k := by
          dsimp [W_k]
          refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i_k, ?_, rfl⟩)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩
        have hadj_vk1 : ∀ y ∈ insert (v i_k1) (W_k k), G.Adj (v i_k1) y ↔ y = v i_k := by
          intro y hy_ins
          constructor
          · intro hadj
            have hy_ne : y ≠ v i_k1 := fun h => G.loopless _ (h ▸ hadj)
            have hy_Wk : y ∈ W_k k := by
              rcases Finset.mem_insert.mp hy_ins with rfl | h
              · exact False.elim (hy_ne rfl)
              · exact h
            dsimp [W_k] at hy_Wk
            rcases Finset.mem_union.mp hy_Wk with h_U | h_img
            · have h_br := hBridge.2.2.2.2 y h_U (v i_k1) (hv_mem_img i_k1) (G.symm hadj)
              have hi0 : i_k1 = 0 := hv h_br.2
              have : k + 1 = 0 := congrArg Fin.val hi0
              omega
            · rcases Finset.mem_image.mp h_img with ⟨i, hi_flt, rfl⟩
              have hi_le : i.val ≤ k := (Finset.mem_filter.mp hi_flt).2
              have h_sp := (hSpine i_k1 i).mp hadj
              have hi_eq : i.val = k := by
                change (k + 1) + 1 = i.val ∨ i.val + 1 = k + 1 at h_sp
                omega
              congr 1
              exact Fin.ext hi_eq
          · rintro rfl
            exact (hSpine i_k1 i_k).mpr (Or.inr rfl)
        obtain ⟨h_sub, h_s, h_t, h_N, h_R, _, _⟩ :=
          leaf_ext_moments_Q (W_k k) (v i_k1) (v i_k) hv_notMem_Wk hvk_mem_Wk hadj_vk1 ih_sub
        dsimp only
        rw [hW_succ, Nat.cast_add, Nat.cast_one]
        refine ⟨h_sub, ?_, ?_, ?_, ?_⟩
        · change (rootedCount G (insert (v i_k1) (W_k k)) (v i_k1) : ℚ) = _
          rw [h_s]; dsimp [i_k] at ih_s ⊢; rw [ih_s]; ring
        · change (rootedOrderSum G (insert (v i_k1) (W_k k)) (v i_k1) : ℚ) = _
          rw [h_t]; dsimp [i_k] at ih_s ih_t ⊢; rw [ih_s, ih_t]; ring
        · rw [h_N]; dsimp [i_k] at ih_s ⊢; rw [ih_s, ih_N]; ring
        · rw [h_R]; dsimp [i_k] at ih_s ih_t ⊢; rw [ih_s, ih_t, ih_R]; ring
    obtain ⟨hW_sub, hW_s, hW_t, hW_N, hW_R⟩ := h_spine_ind ℓ le_rfl
    have hW_eq : W_k ℓ = U ∪ Finset.univ.image v := by
      have h_flt_l : Finset.univ.filter (fun i : Fin (ℓ + 1) => i.val ≤ ℓ) = Finset.univ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact Nat.le_of_lt_succ i.isLt
      dsimp [W_k]
      rw [h_flt_l]
    have hvl_eq : v ⟨ℓ, Nat.lt_succ_of_le le_rfl⟩ = v (Fin.last ℓ) := rfl
    rw [hW_eq] at hW_sub hW_N hW_R
    rw [hW_eq, hvl_eq] at hW_s hW_t
    exact ⟨hW_sub, hW_s, hW_t, hW_N, hW_R⟩

theorem isTree_of_isSubtree_univ_and_bridge_acyclic : ∀ (n : ℕ)
    (G₀ G₁ : SimpleGraph (Fin n)) (U₁ U₂ : Finset (Fin n)) (r₁ r₂ : Fin n),
    G₀.IsAcyclic →
    IsSubtree G₁ (U₁ ∪ U₂) →
    U₁ ∪ U₂ = Finset.univ →
    IsBridgeJoin G₁ U₁ U₂ r₁ r₂ →
    (∀ a b : Fin n, G₁.Adj a b → ¬ (a = r₁ ∧ b = r₂) → ¬ (a = r₂ ∧ b = r₁) → G₀.Adj a b) →
    G₁.IsTree :=
by
  intro n G₀ G₁ U₁ U₂ r₁ r₂ hG₀_acyc hSub hUniv hJ h_sub
  rcases hJ with ⟨h_disj, hr₁, hr₂, hadj, h_bridge⟩
  have h_induce_reach : ∀ {u v : ↑((Finset.univ : Finset (Fin n)) : Set (Fin n))}
      (q : (G₁.induce ((Finset.univ : Finset (Fin n)) : Set (Fin n))).Walk u v),
      G₁.Reachable u.1 v.1 := by
    intro u v q
    induction q with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons a b c h_step _ ih => exact (show G₁.Adj a.1 b.1 from h_step).reachable.trans ih
  have hSub_univ : IsSubtree G₁ Finset.univ := hUniv ▸ hSub
  have h_conn : G₁.Connected := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨r₁, fun a => ?_⟩
    obtain ⟨q⟩ := hSub_univ.2.preconnected
      ⟨r₁, Finset.mem_coe.mpr (Finset.mem_univ r₁)⟩
      ⟨a, Finset.mem_coe.mpr (Finset.mem_univ a)⟩
    exact h_induce_reach q
  have h_mem_union : ∀ z : Fin n, z ∈ U₁ ∪ U₂ := fun z => hUniv.symm ▸ Finset.mem_univ z
  have bridge_walk_mem_edges : ∀ {a b : Fin n} (q : G₁.Walk a b),
      ((a ∈ U₁ ∧ b ∈ U₂) ∨ (a ∈ U₂ ∧ b ∈ U₁)) →
      s(r₁, r₂) ∈ q.edges := by
    intro a b q
    induction q with
    | nil =>
      intro h_ab
      rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact False.elim (Finset.disjoint_left.mp h_disj ha hb)
      · exact False.elim (Finset.disjoint_left.mp h_disj hb ha)
    | @cons a c b h_step q' ih =>
      intro h_ab
      rcases Finset.mem_union.mp (h_mem_union c) with hc₁ | hc₂
      · rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ (ih (Or.inl ⟨hc₁, hb⟩))
        · obtain ⟨hcr₁, har₂⟩ := h_bridge c hc₁ a ha (G₁.symm h_step)
          subst hcr₁ har₂
          rw [SimpleGraph.Walk.edges_cons, Sym2.eq_swap]
          exact List.mem_cons_self
      · rcases h_ab with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · obtain ⟨har₁, hcr₂⟩ := h_bridge a ha c hc₂ h_step
          subst har₁ hcr₂
          rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_self
        · rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ (ih (Or.inr ⟨hc₂, hb⟩))
  have h_no_cross : ∀ {v z : Fin n} (c : G₁.Walk v v),
      c.edges.Nodup → z ∈ c.support →
      ((v ∈ U₁ ∧ z ∈ U₂) ∨ (v ∈ U₂ ∧ z ∈ U₁)) → False := by
    intro v z c h_nodup hz h_opp
    let p₁ := c.takeUntil z hz
    let p₂ := c.dropUntil z hz
    have he₁ : s(r₁, r₂) ∈ p₁.edges := bridge_walk_mem_edges p₁ h_opp
    have h_opp_symm : (z ∈ U₁ ∧ v ∈ U₂) ∨ (z ∈ U₂ ∧ v ∈ U₁) := by
      rcases h_opp with ⟨hv, hz'⟩ | ⟨hv, hz'⟩
      · exact Or.inr ⟨hz', hv⟩
      · exact Or.inl ⟨hz', hv⟩
    have he₂ : s(r₁, r₂) ∈ p₂.edges := bridge_walk_mem_edges p₂ h_opp_symm
    have h_edges_eq : p₁.edges ++ p₂.edges = c.edges := by
      rw [← SimpleGraph.Walk.edges_append, c.take_spec hz]
    rw [← h_edges_eq, List.nodup_append] at h_nodup
    exact h_nodup.2.2 s(r₁, r₂) he₁ s(r₁, r₂) he₂ rfl
  have h_acyc : G₁.IsAcyclic := by
    intro v c hc
    have h_nodup : c.edges.Nodup := hc.isCircuit.isTrail.edges_nodup
    have h_bridge_not_mem : s(r₁, r₂) ∉ c.edges := by
      intro he
      have hr₁_supp : r₁ ∈ c.support := c.fst_mem_support_of_mem_edges he
      have hr₂_supp : r₂ ∈ c.support := c.snd_mem_support_of_mem_edges he
      rcases Finset.mem_union.mp (h_mem_union v) with hv₁ | hv₂
      · exact h_no_cross c h_nodup hr₂_supp (Or.inl ⟨hv₁, hr₂⟩)
      · exact h_no_cross c h_nodup hr₁_supp (Or.inr ⟨hv₂, hr₁⟩)
    have h_edges : ∀ e ∈ c.edges, e ∈ G₀.edgeSet := by
      intro e
      refine Sym2.ind (fun a b he => ?_) e
      have hadj_ab : G₁.Adj a b := c.adj_of_mem_edges he
      have h1 : ¬ (a = r₁ ∧ b = r₂) := by
        rintro ⟨rfl, rfl⟩
        exact h_bridge_not_mem he
      have h2 : ¬ (a = r₂ ∧ b = r₁) := by
        rintro ⟨rfl, rfl⟩
        rw [Sym2.eq_swap] at he
        exact h_bridge_not_mem he
      rw [SimpleGraph.mem_edgeSet]
      exact h_sub a b hadj_ab h1 h2
    exact hG₀_acyc (c.transfer G₀ h_edges) (hc.transfer h_edges)
  exact ⟨h_conn, h_acyc⟩

theorem broom_insertion_graph_structure : ∀ (n : ℕ) (T : SimpleGraph (Fin n)),
    T.IsTree → ∀ (ℓ k b : ℕ) (A B C L_k : Finset (Fin n)) (w r_B r_C : Fin n)
      (v : Fin (ℓ + 1) → Fin n),
      b ≤ k →
      Function.Injective v →
      IsSubtree T A → IsSubtree T B → IsSubtree T C →
      L_k.card = k →
      Disjoint A B → Disjoint A C → Disjoint B C →
      Disjoint (A ∪ B ∪ C) (Finset.univ.image v) → Disjoint (A ∪ B ∪ C) L_k →
      Disjoint (Finset.univ.image v) L_k →
      A ∪ B ∪ C ∪ (Finset.univ.image v) ∪ L_k = Finset.univ →
      IsBridgeJoin T A B w r_B →
      IsBridgeJoin T (A ∪ B) C w r_C →
      IsBridgeJoin T (A ∪ B ∪ C) ((Finset.univ.image v) ∪ L_k) w (v 0) →
      (∀ i j : Fin (ℓ + 1), T.Adj (v i) (v j) ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val)) →
      IsLeafPacket T L_k (v (Fin.last ℓ)) →
      ∃ (L_b L_kb : Finset (Fin n)) (G₀ T₁ : SimpleGraph (Fin n)),
        G₀.IsAcyclic ∧
        (∀ a z : Fin n, T₁.Adj a z →
          ¬ (a = v (Fin.last ℓ) ∧ z = r_B) →
          ¬ (a = r_B ∧ z = v (Fin.last ℓ)) → G₀.Adj a z) ∧
        IsSubtree T₁ A ∧
        rootedCount T₁ A w = rootedCount T A w ∧
        rootedOrderSum T₁ A w = rootedOrderSum T A w ∧
        unrootedCount T₁ A = unrootedCount T A ∧
        unrootedOrderSum T₁ A = unrootedOrderSum T A ∧
        IsSubtree T₁ B ∧
        rootedCount T₁ B r_B = rootedCount T B r_B ∧
        rootedOrderSum T₁ B r_B = rootedOrderSum T B r_B ∧
        unrootedCount T₁ B = unrootedCount T B ∧
        unrootedOrderSum T₁ B = unrootedOrderSum T B ∧
        IsSubtree T₁ C ∧
        rootedCount T₁ C r_C = rootedCount T C r_C ∧
        rootedOrderSum T₁ C r_C = rootedOrderSum T C r_C ∧
        unrootedCount T₁ C = unrootedCount T C ∧
        unrootedOrderSum T₁ C = unrootedOrderSum T C ∧
        L_b.card = b ∧
        L_kb.card = k - b ∧
        Disjoint C L_kb ∧
        IsLeafPacket T₁ L_kb r_C ∧
        Disjoint B L_b ∧
        IsLeafPacket T₁ L_b r_B ∧
        IsBridgeJoin T₁ A (C ∪ L_kb) w r_C ∧
        Disjoint (A ∪ (C ∪ L_kb)) (Finset.univ.image v) ∧
        IsBridgeJoin T₁ (A ∪ (C ∪ L_kb)) (Finset.univ.image v) w (v 0) ∧
        (∀ i j : Fin (ℓ + 1), T₁.Adj (v i) (v j) ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val)) ∧
        IsBridgeJoin T₁ ((A ∪ (C ∪ L_kb)) ∪ (Finset.univ.image v)) (B ∪ L_b) (v (Fin.last ℓ)) r_B ∧
        ((A ∪ (C ∪ L_kb)) ∪ (Finset.univ.image v)) ∪ (B ∪ L_b) = Finset.univ :=
by
  have h_reattachLeaf_isTree : ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (x u w : V) (hxw : x ≠ w),
      G.IsTree → IsLeafIn G x u → (reattachLeaf G x w hxw).IsTree := by
    intro V _ G x u w hxw hG hx
    classical
    have hG_conn : G.Connected := hG.isConnected
    have hG_acyc : G.IsAcyclic := hG.IsAcyclic
    have h_leaf_avoid : ∀ {H : SimpleGraph V} {x₀ u₀ : V}, IsLeafIn H x₀ u₀ →
        ∀ {a b : V} (p : H.Walk a b), p.IsPath → a ≠ x₀ → b ≠ x₀ → x₀ ∉ p.support := by
      intro H x₀ u₀ hx₀ a b p
      induction p with
      | nil =>
        intro _ ha _ hmem
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hmem
        exact ha hmem.symm
      | @cons a c b hac q ih =>
        intro hp ha hb
        rw [SimpleGraph.Walk.cons_isPath_iff] at hp
        rcases hp with ⟨hq, ha_not_mem⟩
        have hc : c ≠ x₀ := by
          intro hcx
          subst hcx
          cases q with
          | nil => exact hb rfl
          | @cons _ d _ hxd q' =>
            have ha_eq : a = u₀ := (hx₀ a).mp (H.symm hac)
            have hd_eq : d = u₀ := (hx₀ d).mp hxd
            have had : a = d := ha_eq.trans hd_eq.symm
            apply ha_not_mem
            rw [SimpleGraph.Walk.support_cons, had]
            exact List.mem_cons_of_mem _ q'.start_mem_support
        have hx_not_q : x₀ ∉ q.support := ih hq hc hb
        rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
        exact ⟨ha.symm, hx_not_q⟩
    have h_reach_transfer : ∀ {a b : V} (p : G.Walk a b),
        x ∉ p.support → (reattachLeaf G x w hxw).Reachable a b := by
      intro a b p
      induction p with
      | nil =>
        intro _
        exact SimpleGraph.Reachable.refl _
      | @cons a c b hac q ih =>
        intro h_not_mem
        rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at h_not_mem
        rcases h_not_mem with ⟨hxa, hx_not_q⟩
        have ha : a ≠ x := Ne.symm hxa
        have hc : c ≠ x := by
          intro hcx
          apply hx_not_q
          rw [← hcx]
          exact q.start_mem_support
        have hadj : (reattachLeaf G x w hxw).Adj a c := Or.inl ⟨ha, hc, hac⟩
        exact hadj.reachable.trans (ih hx_not_q)
    have h_conn : (reattachLeaf G x w hxw).Connected := by
      rw [SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨w, fun a => ?_⟩
      by_cases hax : a = x
      · rw [hax]
        have hadj : (reattachLeaf G x w hxw).Adj w x := Or.inr (Or.inr ⟨rfl, rfl⟩)
        exact hadj.reachable
      · obtain ⟨p, hp⟩ := (hG_conn.preconnected w a).exists_isPath
        have hx_not_p : x ∉ p.support := h_leaf_avoid hx p hp hxw.symm hax
        exact h_reach_transfer p hx_not_p
    let G' := reattachLeaf G x w hxw
    have h_leaf_G' : IsLeafIn G' x w := by
      intro v
      constructor
      · intro hadj
        rcases hadj with ⟨hxx, _, _⟩ | ⟨_, rfl⟩ | ⟨hxw_eq, _⟩
        · exact False.elim (hxx rfl)
        · rfl
        · exact False.elim (hxw hxw_eq)
      · intro hvw
        subst hvw
        exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    have h_edge_mem : ∀ {a b : V} (q : G'.Walk a b),
        a ≠ x → b = x → s(x, w) ∈ q.edges := by
      intro a b q
      induction q with
      | nil =>
        intro ha hb
        exact False.elim (ha hb)
      | @cons a c b hac q' ih =>
        intro ha hb
        by_cases hcx : c = x
        · subst hcx
          have haw : a = w := (h_leaf_G' a).mp (G'.symm hac)
          subst haw
          rw [SimpleGraph.Walk.edges_cons, Sym2.eq_swap]
          exact List.mem_cons_self
        · rw [SimpleGraph.Walk.edges_cons]
          exact List.mem_cons_of_mem _ (ih hcx hb)
    have h_acyc : G'.IsAcyclic := by
      intro v c hc
      have hx_not_c : x ∉ c.support := by
        cases c with
        | nil => exact False.elim hc.not_of_nil
        | @cons _ y _ hvy p =>
          have h_cons := (SimpleGraph.Walk.cons_isCycle_iff p hvy).mp hc
          rcases h_cons with ⟨hp, h_no_edge⟩
          by_cases hvx : v = x
          · subst v
            have hyw : y = w := (h_leaf_G' y).mp hvy
            subst y
            have h_in : s(x, w) ∈ p.edges := h_edge_mem p hxw.symm rfl
            exact False.elim (h_no_edge h_in)
          · by_cases hyx : y = x
            · subst y
              have hvw : v = w := (h_leaf_G' v).mp (G'.symm hvy)
              cases p with
              | nil => exact False.elim (hvx rfl)
              | @cons _ z _ hxz p' =>
                have hzv : z = v := ((h_leaf_G' z).mp hxz).trans hvw.symm
                subst z
                apply False.elim (h_no_edge _)
                rw [SimpleGraph.Walk.edges_cons, Sym2.eq_swap]
                exact List.mem_cons_self
            · have hx_not_p : x ∉ p.support := h_leaf_avoid h_leaf_G' p hp hyx hvx
              rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
              exact ⟨Ne.symm hvx, hx_not_p⟩
      have h_edges : ∀ e ∈ c.edges, e ∈ G.edgeSet := by
        intro e
        refine Sym2.ind (fun a b he => ?_) e
        have ha_mem : a ∈ c.support := c.fst_mem_support_of_mem_edges he
        have hb_mem : b ∈ c.support := c.snd_mem_support_of_mem_edges he
        have ha_ne : a ≠ x := fun h => hx_not_c (h ▸ ha_mem)
        have hb_ne : b ≠ x := fun h => hx_not_c (h ▸ hb_mem)
        have hadj' : G'.Adj a b := c.adj_of_mem_edges he
        rw [SimpleGraph.mem_edgeSet]
        rcases hadj' with ⟨_, _, hab⟩ | ⟨hax, _⟩ | ⟨_, hbx⟩
        · exact hab
        · exact False.elim (ha_ne hax)
        · exact False.elim (hb_ne hbx)
      exact hG_acyc (c.transfer G h_edges) (hc.transfer h_edges)
    exact ⟨h_conn, h_acyc⟩
  have h_relocatePacket_isTree : ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (S : Finset V) (u w : V) (hu : u ∉ S) (hw : w ∉ S),
      G.IsTree → IsLeafPacket G S u → (relocatePacket G S w hw).IsTree := by
    intro V _ _ G S u w hu hw hG hleaf
    induction S using Finset.induction_on with
    | empty =>
      have h_emp : relocatePacket G ∅ w hw = G := by
        ext a b
        simp [relocatePacket]
      rw [h_emp]
      exact hG
    | @insert x S hxS ih =>
      have hux : u ≠ x := fun h => hu (h ▸ Finset.mem_insert_self x S)
      have huS : u ∉ S := fun h => hu (Finset.mem_insert_of_mem h)
      have hxw : x ≠ w := fun h => hw (h ▸ Finset.mem_insert_self x S)
      have hwS : w ∉ S := fun h => hw (Finset.mem_insert_of_mem h)
      have hx_leaf : IsLeafIn G x u := hleaf x (Finset.mem_insert_self x S)
      have hleafS : IsLeafPacket G S u := fun y hy => hleaf y (Finset.mem_insert_of_mem hy)
      let G_S := relocatePacket G S w hwS
      have hG_S : G_S.IsTree := ih huS hwS hleafS
      have hx_leaf_S : IsLeafIn G_S x u := by
        intro y
        change ((x ∉ S ∧ y ∉ S ∧ G.Adj x y) ∨ (x ∈ S ∧ y = w) ∨ (x = w ∧ y ∈ S)) ↔ y = u
        constructor
        · rintro (⟨_, _, hxy⟩ | ⟨hx_in, _⟩ | ⟨hx_eq, _⟩)
          · exact (hx_leaf y).mp hxy
          · exact False.elim (hxS hx_in)
          · exact False.elim (hxw hx_eq)
        · intro hyu
          rw [hyu]
          exact Or.inl ⟨hxS, huS, (hx_leaf u).mpr rfl⟩
      have hTree_re : (reattachLeaf G_S x w hxw).IsTree :=
        h_reattachLeaf_isTree G_S x u w hxw hG_S hx_leaf_S
      have h_step_eq : relocatePacket G (insert x S) w hw = reattachLeaf G_S x w hxw := by
        ext a b
        change ((a ∉ insert x S ∧ b ∉ insert x S ∧ G.Adj a b) ∨
            (a ∈ insert x S ∧ b = w) ∨ (a = w ∧ b ∈ insert x S)) ↔
          ((a ≠ x ∧ b ≠ x ∧ ((a ∉ S ∧ b ∉ S ∧ G.Adj a b) ∨ (a ∈ S ∧ b = w) ∨ (a = w ∧ b ∈ S))) ∨
            (a = x ∧ b = w) ∨ (a = w ∧ b = x))
        simp only [Finset.mem_insert, not_or]
        constructor
        · rintro (⟨⟨hax, haS⟩, ⟨hbx, hbS⟩, hab⟩ | ⟨rfl | haS, rfl⟩ | ⟨rfl, rfl | hbS⟩)
          · exact Or.inl ⟨hax, hbx, Or.inl ⟨haS, hbS, hab⟩⟩
          · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
          · have hax : a ≠ x := fun h => hxS (h ▸ haS)
            exact Or.inl ⟨hax, hxw.symm, Or.inr (Or.inl ⟨haS, rfl⟩)⟩
          · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
          · have hbx : b ≠ x := fun h => hxS (h ▸ hbS)
            exact Or.inl ⟨hxw.symm, hbx, Or.inr (Or.inr ⟨rfl, hbS⟩)⟩
        · rintro (⟨hax, hbx, ⟨haS, hbS, hab⟩ | ⟨haS, rfl⟩ | ⟨rfl, hbS⟩⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact Or.inl ⟨⟨hax, haS⟩, ⟨hbx, hbS⟩, hab⟩
          · exact Or.inr (Or.inl ⟨Or.inr haS, rfl⟩)
          · exact Or.inr (Or.inr ⟨rfl, Or.inr hbS⟩)
          · exact Or.inr (Or.inl ⟨Or.inl rfl, rfl⟩)
          · exact Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩)
      rw [h_step_eq]
      exact hTree_re
  intro n T hT ℓ k b A B C L_k w r_B r_C v
    hb hv hSubA hSubB hSubC hcard hDisjAB hDisjAC hDisjBC
    hDisjABC_v hDisjABC_L hDisj_v_L hUniv
    hBridgeAB hBridgeABC hBridgeAll hSpine hLeaf
  have hb_card : b ≤ L_k.card := hcard.symm ▸ hb
  obtain ⟨L_b, hLb_sub, hcard_Lb⟩ := Finset.exists_subset_card_eq hb_card
  let L_kb : Finset (Fin n) := L_k \ L_b
  have hLkb_sub : L_kb ⊆ L_k := Finset.sdiff_subset
  have hcard_Lkb : L_kb.card = k - b := by
    rw [Finset.card_sdiff_of_subset hLb_sub, hcard, hcard_Lb]
  have hDisj_Lb_Lkb : Disjoint L_b L_kb := disjoint_sdiff_self_right
  have hUnion_L : L_b ∪ L_kb = L_k := Finset.union_sdiff_of_subset hLb_sub
  have hDisjAB_v : Disjoint (A ∪ B) (Finset.univ.image v) := (Finset.disjoint_union_left.mp hDisjABC_v).1
  have hDisjC_v : Disjoint C (Finset.univ.image v) := (Finset.disjoint_union_left.mp hDisjABC_v).2
  have hDisjA_v : Disjoint A (Finset.univ.image v) := (Finset.disjoint_union_left.mp hDisjAB_v).1
  have hDisjB_v : Disjoint B (Finset.univ.image v) := (Finset.disjoint_union_left.mp hDisjAB_v).2
  have hDisjAB_L : Disjoint (A ∪ B) L_k := (Finset.disjoint_union_left.mp hDisjABC_L).1
  have hDisjC_L : Disjoint C L_k := (Finset.disjoint_union_left.mp hDisjABC_L).2
  have hDisjA_L : Disjoint A L_k := (Finset.disjoint_union_left.mp hDisjAB_L).1
  have hDisjB_L : Disjoint B L_k := (Finset.disjoint_union_left.mp hDisjAB_L).2
  have hDisjA_Lb : Disjoint A L_b := Disjoint.mono_right hLb_sub hDisjA_L
  have hDisjB_Lb : Disjoint B L_b := Disjoint.mono_right hLb_sub hDisjB_L
  have hDisjC_Lb : Disjoint C L_b := Disjoint.mono_right hLb_sub hDisjC_L
  have hDisj_v_Lb : Disjoint (Finset.univ.image v) L_b := Disjoint.mono_right hLb_sub hDisj_v_L
  have hDisjA_Lkb : Disjoint A L_kb := Disjoint.mono_right hLkb_sub hDisjA_L
  have hDisjB_Lkb : Disjoint B L_kb := Disjoint.mono_right hLkb_sub hDisjB_L
  have hDisjC_Lkb : Disjoint C L_kb := Disjoint.mono_right hLkb_sub hDisjC_L
  have hDisj_v_Lkb : Disjoint (Finset.univ.image v) L_kb := Disjoint.mono_right hLkb_sub hDisj_v_L
  let v_last : Fin n := v (Fin.last ℓ)
  have hw_A : w ∈ A := hBridgeAB.2.1
  have hrB_B : r_B ∈ B := hBridgeAB.2.2.1
  have hrC_C : r_C ∈ C := hBridgeABC.2.2.1
  have hv_mem : ∀ i : Fin (ℓ + 1), v i ∈ Finset.univ.image v :=
    fun i => Finset.mem_image_of_mem v (Finset.mem_univ i)
  have hv0_v : v 0 ∈ Finset.univ.image v := hv_mem 0
  have hvlast_v : v_last ∈ Finset.univ.image v := hv_mem (Fin.last ℓ)
  have hw_not_Lk : w ∉ L_k := Finset.disjoint_left.mp hDisjA_L hw_A
  have hrB_not_Lk : r_B ∉ L_k := Finset.disjoint_left.mp hDisjB_L hrB_B
  have hrC_not_Lk : r_C ∉ L_k := Finset.disjoint_left.mp hDisjC_L hrC_C
  have hvlast_not_Lk : v_last ∉ L_k := Finset.disjoint_left.mp hDisj_v_L hvlast_v
  have hrB_not_Lb : r_B ∉ L_b := fun h => hrB_not_Lk (hLb_sub h)
  have hrB_not_Lkb : r_B ∉ L_kb := fun h => hrB_not_Lk (hLkb_sub h)
  have hrC_not_Lb : r_C ∉ L_b := fun h => hrC_not_Lk (hLb_sub h)
  have hrC_not_Lkb : r_C ∉ L_kb := fun h => hrC_not_Lk (hLkb_sub h)
  have hvlast_not_Lb : v_last ∉ L_b := fun h => hvlast_not_Lk (hLb_sub h)
  have hvlast_not_Lkb : v_last ∉ L_kb := fun h => hvlast_not_Lk (hLkb_sub h)
  have hvlast_ne_rB : v_last ≠ r_B := fun h => Finset.disjoint_right.mp hDisjB_v hvlast_v (h ▸ hrB_B)
  let G₁_pkt : SimpleGraph (Fin n) := relocatePacket T L_b r_B hrB_not_Lb
  let G₀ : SimpleGraph (Fin n) := relocatePacket G₁_pkt L_kb r_C hrC_not_Lkb
  let T₁ : SimpleGraph (Fin n) := reattachBridge G₀ w r_B v_last hvlast_ne_rB
  have hLeaf_T_Lb : IsLeafPacket T L_b v_last := fun x hx => hLeaf x (hLb_sub hx)
  have hG₁_tree : G₁_pkt.IsTree :=
    h_relocatePacket_isTree T L_b v_last r_B hvlast_not_Lb hrB_not_Lb hT hLeaf_T_Lb
  have hLeaf_G₁_Lkb : IsLeafPacket G₁_pkt L_kb v_last := by
    intro x hx y
    have hx_not_Lb : x ∉ L_b := Finset.disjoint_right.mp hDisj_Lb_Lkb hx
    have hx_ne_rB : x ≠ r_B := fun h => hrB_not_Lkb (h ▸ hx)
    change ((x ∉ L_b ∧ y ∉ L_b ∧ T.Adj x y) ∨ (x ∈ L_b ∧ y = r_B) ∨ (x = r_B ∧ y ∈ L_b)) ↔ y = v_last
    simp only [hx_not_Lb, hx_ne_rB, false_and, or_false, true_and, not_false_eq_true, hLeaf x (hLkb_sub hx) y]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hvlast_not_Lb, h⟩⟩
  have hG₀_tree : G₀.IsTree :=
    h_relocatePacket_isTree G₁_pkt L_kb v_last r_C hvlast_not_Lkb hrC_not_Lkb hG₁_tree hLeaf_G₁_Lkb
  have hG₀_acyc : G₀.IsAcyclic := hG₀_tree.IsAcyclic
  have hT₁_sub_G₀ : ∀ a z : Fin n, T₁.Adj a z →
      ¬ (a = v_last ∧ z = r_B) → ¬ (a = r_B ∧ z = v_last) → G₀.Adj a z := by
    intro a z hadj h1 h2
    rcases hadj with ⟨_, _, hadj₀⟩ | h_eq1 | h_eq2
    · exact hadj₀
    · exact False.elim (h1 h_eq1)
    · exact False.elim (h2 h_eq2)
  have hG₀_adj_out_Lk : ∀ {a z : Fin n}, a ∉ L_k → z ∉ L_k → (G₀.Adj a z ↔ T.Adj a z) := by
    intro a z ha hz
    have ha_Lb : a ∉ L_b := fun h => ha (hLb_sub h)
    have hz_Lb : z ∉ L_b := fun h => hz (hLb_sub h)
    have ha_Lkb : a ∉ L_kb := fun h => ha (hLkb_sub h)
    have hz_Lkb : z ∉ L_kb := fun h => hz (hLkb_sub h)
    change ((a ∉ L_kb ∧ z ∉ L_kb ∧
      ((a ∉ L_b ∧ z ∉ L_b ∧ T.Adj a z) ∨ (a ∈ L_b ∧ z = r_B) ∨ (a = r_B ∧ z ∈ L_b))) ∨
      (a ∈ L_kb ∧ z = r_C) ∨ (a = r_C ∧ z ∈ L_kb)) ↔ T.Adj a z
    simp [ha_Lb, hz_Lb, ha_Lkb, hz_Lkb]
  have h_adj_out_Lk : ∀ {a z : Fin n}, a ∉ L_k → z ∉ L_k →
      (T₁.Adj a z ↔
        (¬ (a = w ∧ z = r_B) ∧ ¬ (a = r_B ∧ z = w) ∧ T.Adj a z) ∨
        (a = v_last ∧ z = r_B) ∨ (a = r_B ∧ z = v_last)) := by
    intro a z ha hz
    change (¬ (a = w ∧ z = r_B) ∧ ¬ (a = r_B ∧ z = w) ∧ G₀.Adj a z) ∨
        (a = v_last ∧ z = r_B) ∨ (a = r_B ∧ z = v_last) ↔ _
    rw [hG₀_adj_out_Lk ha hz]
  have h_adj_no_rB_no_Lk : ∀ {a z : Fin n}, a ∉ L_k → z ∉ L_k → a ≠ r_B → z ≠ r_B →
      (T₁.Adj a z ↔ T.Adj a z) := by
    intro a z ha hz harB hzrB
    rw [h_adj_out_Lk ha hz]
    simp [harB, hzrB]
  have h_adj_on_B : ∀ a ∈ B, ∀ z ∈ B, T₁.Adj a z ↔ T.Adj a z := by
    intro a ha z hz
    have ha_Lk : a ∉ L_k := Finset.disjoint_left.mp hDisjB_L ha
    have hz_Lk : z ∉ L_k := Finset.disjoint_left.mp hDisjB_L hz
    have haw : a ≠ w := fun h => Finset.disjoint_left.mp hDisjAB hw_A (h ▸ ha)
    have hzw : z ≠ w := fun h => Finset.disjoint_left.mp hDisjAB hw_A (h ▸ hz)
    have hav : a ≠ v_last := fun h => Finset.disjoint_left.mp hDisjB_v (h ▸ ha) hvlast_v
    have hzv : z ≠ v_last := fun h => Finset.disjoint_left.mp hDisjB_v (h ▸ hz) hvlast_v
    rw [h_adj_out_Lk ha_Lk hz_Lk]
    simp [haw, hzw, hav, hzv]
  have hLeaf_Lb : IsLeafPacket T₁ L_b r_B := by
    intro x hx y
    have hx_Lk : x ∈ L_k := hLb_sub hx
    have hx_not_Lkb : x ∉ L_kb := Finset.disjoint_left.mp hDisj_Lb_Lkb hx
    have hxw : x ≠ w := fun h => hw_not_Lk (h ▸ hx_Lk)
    have hxrB : x ≠ r_B := fun h => hrB_not_Lb (h ▸ hx)
    have hxrC : x ≠ r_C := fun h => hrC_not_Lb (h ▸ hx)
    have hxv : x ≠ v_last := fun h => hvlast_not_Lb (h ▸ hx)
    change (¬ (x = w ∧ y = r_B) ∧ ¬ (x = r_B ∧ y = w) ∧
      ((x ∉ L_kb ∧ y ∉ L_kb ∧
        ((x ∉ L_b ∧ y ∉ L_b ∧ T.Adj x y) ∨ (x ∈ L_b ∧ y = r_B) ∨ (x = r_B ∧ y ∈ L_b))) ∨
       (x ∈ L_kb ∧ y = r_C) ∨ (x = r_C ∧ y ∈ L_kb))) ∨
      (x = v_last ∧ y = r_B) ∨ (x = r_B ∧ y = v_last) ↔ y = r_B
    simp only [hx, hx_not_Lkb, hxw, hxrB, hxrC, hxv, false_and, or_false, false_or,
      true_and, not_false_eq_true, not_true_eq_false]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hrB_not_Lkb, h⟩⟩
  have hLeaf_Lkb : IsLeafPacket T₁ L_kb r_C := by
    intro x hx y
    have hx_Lk : x ∈ L_k := hLkb_sub hx
    have hxw : x ≠ w := fun h => hw_not_Lk (h ▸ hx_Lk)
    have hxrB : x ≠ r_B := fun h => hrB_not_Lkb (h ▸ hx)
    have hxrC : x ≠ r_C := fun h => hrC_not_Lkb (h ▸ hx)
    have hxv : x ≠ v_last := fun h => hvlast_not_Lkb (h ▸ hx)
    change (¬ (x = w ∧ y = r_B) ∧ ¬ (x = r_B ∧ y = w) ∧
      ((x ∉ L_kb ∧ y ∉ L_kb ∧ G₁_pkt.Adj x y) ∨
       (x ∈ L_kb ∧ y = r_C) ∨ (x = r_C ∧ y ∈ L_kb))) ∨
      (x = v_last ∧ y = r_B) ∨ (x = r_B ∧ y = v_last) ↔ y = r_C
    simp [hx, hxw, hxrB, hxrC, hxv]
  have h_moments_of_adj_eq : ∀ (U : Finset (Fin n)) (r : Fin n),
      IsSubtree T U →
      (∀ a ∈ U, ∀ z ∈ U, T₁.Adj a z ↔ T.Adj a z) →
      IsSubtree T₁ U ∧
      rootedCount T₁ U r = rootedCount T U r ∧
      rootedOrderSum T₁ U r = rootedOrderSum T U r ∧
      unrootedCount T₁ U = unrootedCount T U ∧
      unrootedOrderSum T₁ U = unrootedOrderSum T U := by
    intro U r hSubU hadjU
    have h_induce : ∀ S : Finset (Fin n), S ⊆ U →
        T₁.induce (S : Set (Fin n)) = T.induce (S : Set (Fin n)) := by
      intro S hSU
      ext ⟨a, ha⟩ ⟨z, hz⟩
      exact hadjU a (hSU ha) z (hSU hz)
    have h_sub_iff : ∀ S : Finset (Fin n), S ⊆ U → (IsSubtree T₁ S ↔ IsSubtree T S) := by
      intro S hSU
      simp only [IsSubtree, h_induce S hSU]
    have hSubU₁ : IsSubtree T₁ U := (h_sub_iff U (Finset.Subset.refl U)).mpr hSubU
    have h_subIn : subtreesIn T₁ U = subtreesIn T U := by
      ext S
      simp only [subtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
      exact and_congr_left (fun hSU => h_sub_iff S hSU)
    have h_rootIn : rootedSubtreesIn T₁ U r = rootedSubtreesIn T U r := by
      ext S
      simp only [rootedSubtreesIn, subtrees, Finset.mem_filter, Finset.mem_univ, true_and]
      exact and_congr_left (fun hSU => h_sub_iff S hSU.1)
    refine ⟨hSubU₁, ?_, ?_, ?_, ?_⟩
    · simp only [rootedCount, h_rootIn]
    · simp only [rootedOrderSum, h_rootIn]
    · simp only [unrootedCount, h_subIn]
    · simp only [unrootedOrderSum, h_subIn]
  have h_adj_on_A : ∀ a ∈ A, ∀ z ∈ A, T₁.Adj a z ↔ T.Adj a z := by
    intro a ha z hz
    exact h_adj_no_rB_no_Lk
      (Finset.disjoint_left.mp hDisjA_L ha)
      (Finset.disjoint_left.mp hDisjA_L hz)
      (fun h => Finset.disjoint_left.mp hDisjAB ha (h ▸ hrB_B))
      (fun h => Finset.disjoint_left.mp hDisjAB hz (h ▸ hrB_B))
  have h_adj_on_C : ∀ a ∈ C, ∀ z ∈ C, T₁.Adj a z ↔ T.Adj a z := by
    intro a ha z hz
    exact h_adj_no_rB_no_Lk
      (Finset.disjoint_left.mp hDisjC_L ha)
      (Finset.disjoint_left.mp hDisjC_L hz)
      (fun h => Finset.disjoint_right.mp hDisjBC ha (h ▸ hrB_B))
      (fun h => Finset.disjoint_right.mp hDisjBC hz (h ▸ hrB_B))
  obtain ⟨hSubA₁, hsA₁, htA₁, hNA₁, hRA₁⟩ := h_moments_of_adj_eq A w hSubA h_adj_on_A
  obtain ⟨hSubB₁, hsB₁, htB₁, hNB₁, hRB₁⟩ := h_moments_of_adj_eq B r_B hSubB h_adj_on_B
  obtain ⟨hSubC₁, hsC₁, htC₁, hNC₁, hRC₁⟩ := h_moments_of_adj_eq C r_C hSubC h_adj_on_C
  have hBridge_A_CLkb : IsBridgeJoin T₁ A (C ∪ L_kb) w r_C := by
    refine ⟨Finset.disjoint_union_right.mpr ⟨hDisjAC, hDisjA_Lkb⟩,
      hw_A, Finset.mem_union_left L_kb hrC_C, ?_, ?_⟩
    · rw [h_adj_no_rB_no_Lk hw_not_Lk hrC_not_Lk
        (fun h => Finset.disjoint_left.mp hDisjAB hw_A (h ▸ hrB_B))
        (fun h => Finset.disjoint_right.mp hDisjBC hrC_C (h ▸ hrB_B))]
      exact hBridgeABC.2.2.2.1
    · intro u hu z hz hadj₁
      rcases Finset.mem_union.mp hz with hzC | hzLkb
      · have hadj_T : T.Adj u z :=
          (h_adj_no_rB_no_Lk
            (Finset.disjoint_left.mp hDisjA_L hu)
            (Finset.disjoint_left.mp hDisjC_L hzC)
            (fun h => Finset.disjoint_left.mp hDisjAB hu (h ▸ hrB_B))
            (fun h => Finset.disjoint_right.mp hDisjBC hzC (h ▸ hrB_B))).mp hadj₁
        exact hBridgeABC.2.2.2.2 u (Finset.mem_union_left B hu) z hzC hadj_T
      · have hurC : u = r_C := (hLeaf_Lkb z hzLkb u).mp (T₁.symm hadj₁)
        exact False.elim (Finset.disjoint_left.mp hDisjAC hu (hurC ▸ hrC_C))
  have hDisj_AC_v : Disjoint (A ∪ (C ∪ L_kb)) (Finset.univ.image v) :=
    Finset.disjoint_union_left.mpr ⟨hDisjA_v, Finset.disjoint_union_left.mpr ⟨hDisjC_v, hDisj_v_Lkb.symm⟩⟩
  have hBridge_AC_v : IsBridgeJoin T₁ (A ∪ (C ∪ L_kb)) (Finset.univ.image v) w (v 0) := by
    refine ⟨hDisj_AC_v, Finset.mem_union_left _ hw_A, hv0_v, ?_, ?_⟩
    · rw [h_adj_no_rB_no_Lk hw_not_Lk
        (Finset.disjoint_left.mp hDisj_v_L hv0_v)
        (fun h => Finset.disjoint_left.mp hDisjAB hw_A (h ▸ hrB_B))
        (fun h => Finset.disjoint_right.mp hDisjB_v hv0_v (h ▸ hrB_B))]
      exact hBridgeAll.2.2.2.1
    · intro u hu z hz hadj₁
      have hz_not_Lk : z ∉ L_k := Finset.disjoint_left.mp hDisj_v_L hz
      have hz_ne_rB : z ≠ r_B := fun h => Finset.disjoint_right.mp hDisjB_v hz (h ▸ hrB_B)
      rcases Finset.mem_union.mp hu with huA | huCL
      · have hadj_T : T.Adj u z :=
          (h_adj_no_rB_no_Lk
            (Finset.disjoint_left.mp hDisjA_L huA)
            hz_not_Lk
            (fun h => Finset.disjoint_left.mp hDisjAB huA (h ▸ hrB_B))
            hz_ne_rB).mp hadj₁
        exact hBridgeAll.2.2.2.2 u
          (Finset.mem_union_left C (Finset.mem_union_left B huA))
          z (Finset.mem_union_left L_k hz) hadj_T
      · rcases Finset.mem_union.mp huCL with huC | huLkb
        · have hadj_T : T.Adj u z :=
            (h_adj_no_rB_no_Lk
              (Finset.disjoint_left.mp hDisjC_L huC)
              hz_not_Lk
              (fun h => Finset.disjoint_right.mp hDisjBC huC (h ▸ hrB_B))
              hz_ne_rB).mp hadj₁
          exact hBridgeAll.2.2.2.2 u
            (Finset.mem_union_right (A ∪ B) huC)
            z (Finset.mem_union_left L_k hz) hadj_T
        · have hzrC : z = r_C := (hLeaf_Lkb u huLkb z).mp hadj₁
          exact False.elim (Finset.disjoint_right.mp hDisjC_v hz (hzrC ▸ hrC_C))
  have hSpine₁ : ∀ i j : Fin (ℓ + 1), T₁.Adj (v i) (v j) ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
    intro i j
    rw [h_adj_no_rB_no_Lk
      (Finset.disjoint_left.mp hDisj_v_L (hv_mem i))
      (Finset.disjoint_left.mp hDisj_v_L (hv_mem j))
      (fun h => Finset.disjoint_right.mp hDisjB_v (hv_mem i) (h ▸ hrB_B))
      (fun h => Finset.disjoint_right.mp hDisjB_v (hv_mem j) (h ▸ hrB_B))]
    exact hSpine i j
  have hDisj_W₁_BLb : Disjoint ((A ∪ (C ∪ L_kb)) ∪ (Finset.univ.image v)) (B ∪ L_b) := by
    refine Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨?_, Finset.disjoint_union_left.mpr ⟨?_, ?_⟩⟩, ?_⟩
    · exact Finset.disjoint_union_right.mpr ⟨hDisjAB, hDisjA_Lb⟩
    · exact Finset.disjoint_union_right.mpr ⟨hDisjBC.symm, hDisjC_Lb⟩
    · exact Finset.disjoint_union_right.mpr ⟨hDisjB_Lkb.symm, hDisj_Lb_Lkb.symm⟩
    · exact Finset.disjoint_union_right.mpr ⟨hDisjB_v.symm, hDisj_v_Lb⟩
  have hBridge_all₁ : IsBridgeJoin T₁ ((A ∪ (C ∪ L_kb)) ∪ (Finset.univ.image v)) (B ∪ L_b) v_last r_B := by
    refine ⟨hDisj_W₁_BLb, Finset.mem_union_right _ hvlast_v, Finset.mem_union_left L_b hrB_B,
      Or.inr (Or.inl ⟨rfl, rfl⟩), ?_⟩
    intro u hu z hz hadj₁
    rcases Finset.mem_union.mp hz with hzB | hzLb
    · have hz_not_Lk : z ∉ L_k := Finset.disjoint_left.mp hDisjB_L hzB
      rcases Finset.mem_union.mp hu with huACL | huv
      · rcases Finset.mem_union.mp huACL with huA | huCL
        · have hu_not_Lk : u ∉ L_k := Finset.disjoint_left.mp hDisjA_L huA
          have hu_ne_rB : u ≠ r_B := fun h => Finset.disjoint_left.mp hDisjAB huA (h ▸ hrB_B)
          rcases (h_adj_out_Lk hu_not_Lk hz_not_Lk).mp hadj₁ with ⟨h_not_w_rB, _, hadj_T⟩ | h_eq | ⟨hurB, _⟩
          · exact False.elim (h_not_w_rB (hBridgeAB.2.2.2.2 u huA z hzB hadj_T))
          · exact h_eq
          · exact False.elim (hu_ne_rB hurB)
        · rcases Finset.mem_union.mp huCL with huC | huLkb
          · have hu_not_Lk : u ∉ L_k := Finset.disjoint_left.mp hDisjC_L huC
            have hu_ne_rB : u ≠ r_B := fun h => Finset.disjoint_right.mp hDisjBC huC (h ▸ hrB_B)
            rcases (h_adj_out_Lk hu_not_Lk hz_not_Lk).mp hadj₁ with ⟨_, _, hadj_T⟩ | h_eq | ⟨hurB, _⟩
            · have hzw : z = w := (hBridgeABC.2.2.2.2 z (Finset.mem_union_right A hzB) u huC (T.symm hadj_T)).1
              exact False.elim (Finset.disjoint_left.mp hDisjAB hw_A (hzw ▸ hzB))
            · exact h_eq
            · exact False.elim (hu_ne_rB hurB)
          · have hzrC : z = r_C := (hLeaf_Lkb u huLkb z).mp hadj₁
            exact False.elim (Finset.disjoint_left.mp hDisjBC hzB (hzrC ▸ hrC_C))
      · have hu_not_Lk : u ∉ L_k := Finset.disjoint_left.mp hDisj_v_L huv
        have hu_ne_rB : u ≠ r_B := fun h => Finset.disjoint_right.mp hDisjB_v huv (h ▸ hrB_B)
        rcases (h_adj_out_Lk hu_not_Lk hz_not_Lk).mp hadj₁ with ⟨_, _, hadj_T⟩ | h_eq | ⟨hurB, _⟩
        · have hzw : z = w := (hBridgeAll.2.2.2.2 z
            (Finset.mem_union_left C (Finset.mem_union_right A hzB))
            u (Finset.mem_union_left L_k huv) (T.symm hadj_T)).1
          exact False.elim (Finset.disjoint_left.mp hDisjAB hw_A (hzw ▸ hzB))
        · exact h_eq
        · exact False.elim (hu_ne_rB hurB)
    · have hurB : u = r_B := (hLeaf_Lb z hzLb u).mp (T₁.symm hadj₁)
      exact False.elim (Finset.disjoint_left.mp hDisj_W₁_BLb hu (Finset.mem_union_left L_b (hurB ▸ hrB_B)))
  have hUniv₁ : ((A ∪ (C ∪ L_kb)) ∪ (Finset.univ.image v)) ∪ (B ∪ L_b) = Finset.univ := by
    ext x
    simp only [← hUniv, ← hUnion_L, Finset.mem_union]
    tauto
  exact ⟨L_b, L_kb, G₀, T₁, hG₀_acyc, hT₁_sub_G₀,
    hSubA₁, hsA₁, htA₁, hNA₁, hRA₁,
    hSubB₁, hsB₁, htB₁, hNB₁, hRB₁,
    hSubC₁, hsC₁, htC₁, hNC₁, hRC₁,
    hcard_Lb, hcard_Lkb, hDisjC_Lkb, hLeaf_Lkb,
    hDisjB_Lb, hLeaf_Lb, hBridge_A_CLkb,
    hDisj_AC_v, hBridge_AC_v, hSpine₁,
    hBridge_all₁, hUniv₁⟩

theorem broom_balanced_insertion_candidates : ∀ (n : ℕ) (hn : 1 ≤ n) (T : SimpleGraph (Fin n)),
    T.IsTree → ∀ (ℓ k : ℕ) (A B C L_k : Finset (Fin n)) (w r_B r_C : Fin n)
      (v : Fin (ℓ + 1) → Fin n),
      ((1 ≤ ℓ ∧ 2 ≤ k) ∨ (ℓ = 0 ∧ 3 ≤ k)) →
      Function.Injective v →
      IsSubtree T A → IsSubtree T B → IsSubtree T C →
      L_k.card = k →
      Disjoint A B → Disjoint A C → Disjoint B C →
      Disjoint (A ∪ B ∪ C) (Finset.univ.image v) → Disjoint (A ∪ B ∪ C) L_k →
      Disjoint (Finset.univ.image v) L_k →
      A ∪ B ∪ C ∪ (Finset.univ.image v) ∪ L_k = Finset.univ →
      IsBridgeJoin T A B w r_B →
      IsBridgeJoin T (A ∪ B) C w r_C →
      IsBridgeJoin T (A ∪ B ∪ C) ((Finset.univ.image v) ∪ L_k) w (v 0) →
      (∀ i j : Fin (ℓ + 1), T.Adj (v i) (v j) ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val)) →
      IsLeafPacket T L_k (v (Fin.last ℓ)) →
      ∃ T₁ T₂ : SimpleGraph (Fin n),
        T₁.IsTree ∧ T₂.IsTree ∧
        0 < (subtreeCount T₁ : ℚ) ∧ 0 < (subtreeCount T₂ : ℚ) ∧
        ((subtreeOrderSum T₁ : ℚ) - meanSubtreeOrder T * (subtreeCount T₁ : ℚ)) =
          broomInsertionScore (rootedCount T A w) (rootedCount T B r_B) (rootedCount T C r_C)
            ℓ k
            (2 * ((rootedOrderSum T A w : ℚ) / (rootedCount T A w : ℚ) - 1))
            ((rootedOrderSum T B r_B : ℚ) / ((rootedCount T B r_B : ℚ) + 1))
            ((rootedOrderSum T C r_C : ℚ) / ((rootedCount T C r_C : ℚ) + 1))
            (meanSubtreeOrder T -
              ((rootedOrderSum T A w : ℚ) / (rootedCount T A w : ℚ) +
               (rootedOrderSum T B r_B : ℚ) / ((rootedCount T B r_B : ℚ) + 1) +
               (rootedOrderSum T C r_C : ℚ) / ((rootedCount T C r_C : ℚ) + 1))) ∧
        ((subtreeOrderSum T₂ : ℚ) - meanSubtreeOrder T * (subtreeCount T₂ : ℚ)) =
          broomInsertionScore (rootedCount T A w) (rootedCount T C r_C) (rootedCount T B r_B)
            ℓ k
            (2 * ((rootedOrderSum T A w : ℚ) / (rootedCount T A w : ℚ) - 1))
            ((rootedOrderSum T C r_C : ℚ) / ((rootedCount T C r_C : ℚ) + 1))
            ((rootedOrderSum T B r_B : ℚ) / ((rootedCount T B r_B : ℚ) + 1))
            (meanSubtreeOrder T -
              ((rootedOrderSum T A w : ℚ) / (rootedCount T A w : ℚ) +
               (rootedOrderSum T B r_B : ℚ) / ((rootedCount T B r_B : ℚ) + 1) +
               (rootedOrderSum T C r_C : ℚ) / ((rootedCount T C r_C : ℚ) + 1))) :=
by
  intro n hn T hT ℓ k A B C L_k w r_B r_C v
    h_lk hv hSubA hSubB hSubC hcard hDisjAB hDisjAC hDisjBC
    hDisjABC_v hDisjABC_L hDisj_v_L hUniv hBridgeAB hBridgeABC hBridgeAll
    hSpine hLeaf
  have h_subtreesIn_univ : ∀ G : SimpleGraph (Fin n),
      subtreesIn G Finset.univ = subtrees G := by
    intro G
    simp [subtreesIn, Finset.subset_univ]
  have single_candidate : ∀ (B' C' : Finset (Fin n)) (r_B' r_C' : Fin n),
      IsSubtree T B' → IsSubtree T C' →
      Disjoint A B' → Disjoint A C' → Disjoint B' C' →
      Disjoint (A ∪ B' ∪ C') (Finset.univ.image v) →
      Disjoint (A ∪ B' ∪ C') L_k →
      A ∪ B' ∪ C' ∪ (Finset.univ.image v) ∪ L_k = Finset.univ →
      IsBridgeJoin T A B' w r_B' →
      IsBridgeJoin T (A ∪ B') C' w r_C' →
      IsBridgeJoin T (A ∪ B' ∪ C') ((Finset.univ.image v) ∪ L_k) w (v 0) →
      ∃ T₁ : SimpleGraph (Fin n),
        T₁.IsTree ∧
        0 < (subtreeCount T₁ : ℚ) ∧
        ((subtreeOrderSum T₁ : ℚ) - meanSubtreeOrder T * (subtreeCount T₁ : ℚ)) =
          broomInsertionScore (rootedCount T A w) (rootedCount T B' r_B') (rootedCount T C' r_C')
            ℓ k
            (2 * ((rootedOrderSum T A w : ℚ) / (rootedCount T A w : ℚ) - 1))
            ((rootedOrderSum T B' r_B' : ℚ) / ((rootedCount T B' r_B' : ℚ) + 1))
            ((rootedOrderSum T C' r_C' : ℚ) / ((rootedCount T C' r_C' : ℚ) + 1))
            (meanSubtreeOrder T -
              ((rootedOrderSum T A w : ℚ) / (rootedCount T A w : ℚ) +
               (rootedOrderSum T B' r_B' : ℚ) / ((rootedCount T B' r_B' : ℚ) + 1) +
               (rootedOrderSum T C' r_C' : ℚ) / ((rootedCount T C' r_C' : ℚ) + 1))) := by
    intro B' C' r_B' r_C' hSubB' hSubC' hDisjAB' hDisjAC' hDisjB'C'
      hDisjABC'_v hDisjABC'_L hUniv' hBridgeAB' hBridgeABC' hBridgeAll'
    have hk2 : 2 ≤ k := by
      rcases h_lk with ⟨_, hk⟩ | ⟨_, hk⟩ <;> omega
    have hb : (k + 1) / 2 ≤ k := by omega
    have hw_in_A : w ∈ A := hBridgeAB'.2.1
    have hrB'_in_B' : r_B' ∈ B' := hBridgeAB'.2.2.1
    have hrC'_in_C' : r_C' ∈ C' := hBridgeABC'.2.2.1
    have hp_pos_nat : 0 < rootedCount T A w := by
      refine Finset.card_pos.mpr ⟨A, ?_⟩
      simp [rootedSubtreesIn, subtrees, hSubA, hw_in_A]
    have hp_pos : (0 : ℚ) < (rootedCount T A w : ℚ) := by exact_mod_cast hp_pos_nat
    have hp_ne : (rootedCount T A w : ℚ) ≠ 0 := ne_of_gt hp_pos
    have hNT_pos_nat : 0 < subtreeCount T := by
      refine Finset.card_pos.mpr ⟨A, ?_⟩
      simp [subtrees, hSubA]
    have hNT_pos : (0 : ℚ) < (subtreeCount T : ℚ) := by exact_mod_cast hNT_pos_nat
    have hNT_ne : (subtreeCount T : ℚ) ≠ 0 := ne_of_gt hNT_pos
    obtain ⟨hsAB', htAB'⟩ := bridge_join_rooted_moments n T A B' w r_B' hBridgeAB'
    obtain ⟨hSubAB', hNAB', hRAB'⟩ :=
      bridge_join_unrooted_moments n T A B' w r_B' hSubA hSubB' hBridgeAB'
    obtain ⟨hsABC', htABC'⟩ := bridge_join_rooted_moments n T (A ∪ B') C' w r_C' hBridgeABC'
    obtain ⟨hSubABC', hNABC', hRABC'⟩ :=
      bridge_join_unrooted_moments n T (A ∪ B') C' w r_C' hSubAB' hSubC' hBridgeABC'
    have hDB_T : IsDoubleBroomSuffix T ℓ 0 k (A ∪ B' ∪ C') ∅ L_k w v := by
      refine ⟨hv, hSubABC', Finset.card_empty, hcard, hDisjABC'_v,
        Finset.disjoint_empty_right _, hDisjABC'_L,
        Finset.disjoint_empty_right _, hDisj_v_L, Finset.disjoint_empty_left _,
        ?_, ?_, hSpine, fun x hx => False.elim (Finset.notMem_empty x hx), hLeaf⟩
      · simpa only [Finset.union_empty] using hUniv'
      · simpa only [Finset.union_empty] using hBridgeAll'
    obtain ⟨hNT_eq, hRT_eq⟩ :=
      double_broom_suffix_moments n ℓ 0 k T (A ∪ B' ∪ C') ∅ L_k w v hT hDB_T
    change (subtreeCount T : ℚ) =
      doubleBroomCount (unrootedCount T (A ∪ B' ∪ C')) (rootedCount T (A ∪ B' ∪ C') w) ℓ 0 k at hNT_eq
    change (subtreeOrderSum T : ℚ) =
      doubleBroomOrderSum (unrootedOrderSum T (A ∪ B' ∪ C')) (rootedCount T (A ∪ B' ∪ C') w)
        (rootedOrderSum T (A ∪ B' ∪ C') w) ℓ 0 k at hRT_eq
    obtain ⟨L_b, L_kb, G₀, T₁, hG₀_acyc, hT₁_sub_G₀,
      hSubA₁, hsA₁, htA₁, hNA₁, hRA₁,
      hSubB₁, hsB₁, htB₁, hNB₁, hRB₁,
      hSubC₁, hsC₁, htC₁, hNC₁, hRC₁,
      hcard_Lb, hcard_Lkb, hDisj_C_Lkb, hLeaf_Lkb,
      hDisj_B_Lb, hLeaf_Lb, hBridge_A_CLkb,
      hDisj_AC_v, hBridge_AC_v, hSpine₁,
      hBridge_all₁, hUniv₁⟩ :=
      broom_insertion_graph_structure n T hT ℓ k ((k + 1) / 2) A B' C' L_k w r_B' r_C' v
        hb hv hSubA hSubB' hSubC' hcard hDisjAB' hDisjAC' hDisjB'C'
        hDisjABC'_v hDisjABC'_L hDisj_v_L hUniv' hBridgeAB' hBridgeABC' hBridgeAll'
        hSpine hLeaf
    obtain ⟨hPkt₁, hSpineMom₁⟩ := pendant_packet_and_spine_moments n T₁
    obtain ⟨hSub_CLkb, hs_CLkb, ht_CLkb, hN_CLkb, hR_CLkb⟩ :=
      hPkt₁ C' L_kb r_C' hSubC₁ hrC'_in_C' hDisj_C_Lkb hLeaf_Lkb
    obtain ⟨hs_H₁, ht_H₁⟩ :=
      bridge_join_rooted_moments n T₁ A (C' ∪ L_kb) w r_C' hBridge_A_CLkb
    obtain ⟨hSub_H₁, hN_H₁, hR_H₁⟩ :=
      bridge_join_unrooted_moments n T₁ A (C' ∪ L_kb) w r_C' hSubA₁ hSub_CLkb hBridge_A_CLkb
    obtain ⟨hSub_W₁, hs_W₁, ht_W₁, hN_W₁, hR_W₁⟩ :=
      hSpineMom₁ ℓ (A ∪ (C' ∪ L_kb)) w v hv hSub_H₁ hDisj_AC_v hBridge_AC_v hSpine₁
    obtain ⟨hSub_BLb, hs_BLb, ht_BLb, hN_BLb, hR_BLb⟩ :=
      hPkt₁ B' L_b r_B' hSubB₁ hrB'_in_B' hDisj_B_Lb hLeaf_Lb
    obtain ⟨hSub_univ₁, hN_univ₁, hR_univ₁⟩ :=
      bridge_join_unrooted_moments n T₁
        ((A ∪ (C' ∪ L_kb)) ∪ (Finset.univ.image v)) (B' ∪ L_b)
        (v (Fin.last ℓ)) r_B' hSub_W₁ hSub_BLb hBridge_all₁
    have hT₁_tree : T₁.IsTree :=
      isTree_of_isSubtree_univ_and_bridge_acyclic n G₀ T₁
        ((A ∪ (C' ∪ L_kb)) ∪ (Finset.univ.image v)) (B' ∪ L_b)
        (v (Fin.last ℓ)) r_B'
        hG₀_acyc hSub_univ₁ hUniv₁ hBridge_all₁ hT₁_sub_G₀
    have hN₁_pos_nat : 0 < subtreeCount T₁ := by
      refine Finset.card_pos.mpr ⟨A, ?_⟩
      simp [subtrees, hSubA₁]
    have hN₁_pos : (0 : ℚ) < (subtreeCount T₁ : ℚ) := by exact_mod_cast hN₁_pos_nat
    have hN₁_eq_univ : unrootedCount T₁ (((A ∪ (C' ∪ L_kb)) ∪ (Finset.univ.image v)) ∪ (B' ∪ L_b)) =
        subtreeCount T₁ := by
      rw [hUniv₁]
      change (subtreesIn T₁ Finset.univ).card = (subtrees T₁).card
      rw [h_subtreesIn_univ]
    have hR₁_eq_univ : unrootedOrderSum T₁ (((A ∪ (C' ∪ L_kb)) ∪ (Finset.univ.image v)) ∪ (B' ∪ L_b)) =
        subtreeOrderSum T₁ := by
      rw [hUniv₁]
      change (∑ S ∈ subtreesIn T₁ Finset.univ, S.card) = ∑ S ∈ subtrees T₁, S.card
      rw [h_subtreesIn_univ]
    refine ⟨T₁, hT₁_tree, hN₁_pos, ?_⟩
    set p : ℕ := rootedCount T A w
    set t_A : ℕ := rootedOrderSum T A w
    set x : ℕ := rootedCount T B' r_B'
    set t_B : ℕ := rootedOrderSum T B' r_B'
    set y : ℕ := rootedCount T C' r_C'
    set t_C : ℕ := rootedOrderSum T C' r_C'
    set c : ℚ := 2 * ((t_A : ℚ) / (p : ℚ) - 1)
    set u : ℚ := (t_B : ℚ) / ((x : ℚ) + 1)
    set v_p : ℚ := (t_C : ℚ) / ((y : ℚ) + 1)
    set q : ℚ := meanSubtreeOrder T
    set d : ℚ := q - ((t_A : ℚ) / (p : ℚ) + u + v_p)
    have hx1_ne : (x : ℚ) + 1 ≠ 0 := by positivity
    have hy1_ne : (y : ℚ) + 1 ≠ 0 := by positivity
    have htA_eq : (t_A : ℚ) = (p : ℚ) * (1 + c / 2) := by
      dsimp [c]
      field_simp [hp_ne]
      ring
    have htB_eq : (t_B : ℚ) = ((x : ℚ) + 1) * u := by
      dsimp [u]
      field_simp [hx1_ne]
    have htC_eq : (t_C : ℚ) = ((y : ℚ) + 1) * v_p := by
      dsimp [v_p]
      field_simp [hy1_ne]
    have hq_eq : q = 1 + c / 2 + u + v_p + d := by
      dsimp [d, c]
      field_simp [hp_ne]
      ring
    have hRT_q : (subtreeOrderSum T : ℚ) = q * (subtreeCount T : ℚ) := by
      dsimp [q, meanSubtreeOrder]
      exact (div_mul_cancel₀ (subtreeOrderSum T : ℚ) hNT_ne).symm
    have h_pow_k : (2 : ℚ) ^ k = (2 : ℚ) ^ ((k + 1) / 2) * (2 : ℚ) ^ (k - (k + 1) / 2) := by
      rw [← pow_add]
      congr 1
      omega
    have h_cast_kb : ((k - (k + 1) / 2 : ℕ) : ℚ) = (k : ℚ) - (((k + 1) / 2 : ℕ) : ℚ) :=
      Nat.cast_sub hb
    have hN₁_q : (subtreeCount T₁ : ℚ) =
        (unrootedCount T₁ ((A ∪ (C' ∪ L_kb)) ∪ (Finset.univ.image v)) : ℚ) +
        (unrootedCount T₁ (B' ∪ L_b) : ℚ) +
        (rootedCount T₁ ((A ∪ (C' ∪ L_kb)) ∪ (Finset.univ.image v)) (v (Fin.last ℓ)) : ℚ) *
          (rootedCount T₁ (B' ∪ L_b) r_B' : ℚ) := by
      rw [← hN₁_eq_univ, hN_univ₁]
      push_cast
      ring
    have hR₁_q : (subtreeOrderSum T₁ : ℚ) =
        (unrootedOrderSum T₁ ((A ∪ (C' ∪ L_kb)) ∪ (Finset.univ.image v)) : ℚ) +
        (unrootedOrderSum T₁ (B' ∪ L_b) : ℚ) +
        (rootedOrderSum T₁ ((A ∪ (C' ∪ L_kb)) ∪ (Finset.univ.image v)) (v (Fin.last ℓ)) : ℚ) *
          (rootedCount T₁ (B' ∪ L_b) r_B' : ℚ) +
        (rootedCount T₁ ((A ∪ (C' ∪ L_kb)) ∪ (Finset.univ.image v)) (v (Fin.last ℓ)) : ℚ) *
          (rootedOrderSum T₁ (B' ∪ L_b) r_B' : ℚ) := by
      rw [← hR₁_eq_univ, hR_univ₁]
      push_cast
      ring
    have hs_H₁_q : (rootedCount T₁ (A ∪ (C' ∪ L_kb)) w : ℚ) =
        (p : ℚ) * (1 + (rootedCount T₁ (C' ∪ L_kb) r_C' : ℚ)) := by
      rw [hs_H₁, hsA₁]
      push_cast
      ring
    have ht_H₁_q : (rootedOrderSum T₁ (A ∪ (C' ∪ L_kb)) w : ℚ) =
        (t_A : ℚ) * (1 + (rootedCount T₁ (C' ∪ L_kb) r_C' : ℚ)) +
        (p : ℚ) * (rootedOrderSum T₁ (C' ∪ L_kb) r_C' : ℚ) := by
      rw [ht_H₁, hsA₁, htA₁]
      push_cast
      ring
    have hN_H₁_q : (unrootedCount T₁ (A ∪ (C' ∪ L_kb)) : ℚ) =
        (unrootedCount T A : ℚ) + (unrootedCount T₁ (C' ∪ L_kb) : ℚ) +
        (p : ℚ) * (rootedCount T₁ (C' ∪ L_kb) r_C' : ℚ) := by
      rw [hN_H₁, hNA₁, hsA₁]
      push_cast
      ring
    have hR_H₁_q : (unrootedOrderSum T₁ (A ∪ (C' ∪ L_kb)) : ℚ) =
        (unrootedOrderSum T A : ℚ) + (unrootedOrderSum T₁ (C' ∪ L_kb) : ℚ) +
        (t_A : ℚ) * (rootedCount T₁ (C' ∪ L_kb) r_C' : ℚ) +
        (p : ℚ) * (rootedOrderSum T₁ (C' ∪ L_kb) r_C' : ℚ) := by
      rw [hR_H₁, hRA₁, hsA₁, htA₁]
      push_cast
      ring
    simp only [hcard_Lkb, hsC₁, htC₁, hNC₁, hRC₁] at hs_CLkb ht_CLkb hN_CLkb hR_CLkb
    simp only [hcard_Lb, hsB₁, htB₁, hNB₁, hRB₁] at hs_BLb ht_BLb hN_BLb hR_BLb
    have h_lhs_diff : (subtreeOrderSum T₁ : ℚ) - q * (subtreeCount T₁ : ℚ) =
        ((subtreeOrderSum T₁ : ℚ) - (subtreeOrderSum T : ℚ)) -
        q * ((subtreeCount T₁ : ℚ) - (subtreeCount T : ℚ)) := by
      linear_combination hRT_q
    rw [h_lhs_diff, hR₁_q, hN₁_q, hRT_eq, hNT_eq]
    rw [hR_W₁, hN_W₁, ht_W₁, hs_W₁]
    rw [hR_H₁_q, hN_H₁_q, ht_H₁_q, hs_H₁_q]
    rw [hR_CLkb, hN_CLkb, ht_CLkb, hs_CLkb]
    rw [hR_BLb, hN_BLb, ht_BLb, hs_BLb]
    unfold doubleBroomOrderSum doubleBroomCount broomInsertionScore
    dsimp only
    simp only [hRABC', hNABC', htABC', hsABC', hRAB', hNAB', htAB', hsAB']
    push_cast
    simp only [htA_eq, htB_eq, htC_eq, hq_eq, h_pow_k, h_cast_kb]
    ring
  obtain ⟨T₁, hT₁, hN₁, hScore₁⟩ :=
    single_candidate B C r_B r_C hSubB hSubC hDisjAB hDisjAC hDisjBC
      hDisjABC_v hDisjABC_L hUniv hBridgeAB hBridgeABC hBridgeAll
  have hABC_comm : A ∪ C ∪ B = A ∪ B ∪ C := Finset.union_right_comm A C B
  have hBridgeAC : IsBridgeJoin T A C w r_C := by
    refine ⟨hDisjAC, hBridgeAB.2.1, hBridgeABC.2.2.1, hBridgeABC.2.2.2.1, ?_⟩
    intro u hu z hz hadj
    exact hBridgeABC.2.2.2.2 u (Finset.mem_union_left B hu) z hz hadj
  have hBridgeACB : IsBridgeJoin T (A ∪ C) B w r_B := by
    refine ⟨Finset.disjoint_union_left.mpr ⟨hDisjAB, hDisjBC.symm⟩,
      Finset.mem_union_left C hBridgeAB.2.1, hBridgeAB.2.2.1, hBridgeAB.2.2.2.1, ?_⟩
    intro u hu z hz hadj
    rcases Finset.mem_union.mp hu with huA | huC
    · exact hBridgeAB.2.2.2.2 u huA z hz hadj
    · have hzw := (hBridgeABC.2.2.2.2 z (Finset.mem_union_right A hz) u huC (T.symm hadj)).1
      subst hzw
      exact False.elim (Finset.disjoint_left.mp hDisjAB hBridgeAB.2.1 hz)
  have hDisjACB_v : Disjoint (A ∪ C ∪ B) (Finset.univ.image v) := by
    rwa [hABC_comm]
  have hDisjACB_L : Disjoint (A ∪ C ∪ B) L_k := by
    rwa [hABC_comm]
  have hUniv_ACB : A ∪ C ∪ B ∪ (Finset.univ.image v) ∪ L_k = Finset.univ := by
    rwa [hABC_comm]
  have hBridgeAll_ACB : IsBridgeJoin T (A ∪ C ∪ B) ((Finset.univ.image v) ∪ L_k) w (v 0) := by
    rwa [hABC_comm]
  obtain ⟨T₂, hT₂, hN₂, hScore₂⟩ :=
    single_candidate C B r_C r_B hSubC hSubB hDisjAC hDisjAB hDisjBC.symm
      hDisjACB_v hDisjACB_L hUniv_ACB hBridgeAC hBridgeACB hBridgeAll_ACB
  have h_d_comm :
      meanSubtreeOrder T -
        ((rootedOrderSum T A w : ℚ) / (rootedCount T A w : ℚ) +
         (rootedOrderSum T C r_C : ℚ) / ((rootedCount T C r_C : ℚ) + 1) +
         (rootedOrderSum T B r_B : ℚ) / ((rootedCount T B r_B : ℚ) + 1)) =
      meanSubtreeOrder T -
        ((rootedOrderSum T A w : ℚ) / (rootedCount T A w : ℚ) +
         (rootedOrderSum T B r_B : ℚ) / ((rootedCount T B r_B : ℚ) + 1) +
         (rootedOrderSum T C r_C : ℚ) / ((rootedCount T C r_C : ℚ) + 1)) := by
    ring
  rw [h_d_comm] at hScore₂
  exact ⟨T₁, T₂, hT₁, hT₂, hN₁, hN₂, hScore₁, hScore₂⟩

theorem broom_score_host_and_d_mono : ∀ (ℓ k p x y : ℕ) (c u v d : ℚ),
    ((1 ≤ ℓ ∧ 2 ≤ k) ∨ (ℓ = 0 ∧ 3 ≤ k)) →
    1 ≤ p →
    0 ≤ c → c ≤ (p : ℚ) - 1 →
    ℓ + 2 ^ k ≤ x → ℓ + 2 ^ k ≤ y →
    (25 : ℚ) / 12 ≤ u → u ≤ (x : ℚ) / 2 →
    (25 : ℚ) / 12 ≤ v → v ≤ (y : ℚ) / 2 →
    broomThreshold ℓ k ≤ d →
    (p : ℚ) * broomInsertionScore 1 x y ℓ k 0 u v (broomThreshold ℓ k) ≤
      broomInsertionScore p x y ℓ k c u v d :=
by
  intro ℓ k p x y c u v d hlk hp hc0 hcp hx hy hu1 hu2 hv1 hv2 hd
  set d0 : ℚ := broomThreshold ℓ k
  set g : ℕ := k / 2
  have hk2 : 2 ≤ k := by rcases hlk with ⟨_, hk⟩ | ⟨_, hk⟩ <;> omega
  have hg1 : 1 ≤ g := by omega
  set J : ℚ := (2 : ℚ) ^ g
  have hJ2 : 2 ≤ J := by
    have : 2 ^ 1 ≤ 2 ^ g := Nat.pow_le_pow_right (by omega) hg1
    have h2g : 2 ≤ 2 ^ g := by omega
    dsimp [J]
    exact_mod_cast h2g
  set W : ℚ := J - 2
  have hW : 0 ≤ W := by linarith
  set G : ℚ := (g : ℚ) - 1
  have hG : 0 ≤ G := by
    have : (1 : ℚ) ≤ (g : ℚ) := by exact_mod_cast hg1
    linarith
  set H : ℚ := (ℓ : ℚ)
  have hH : 0 ≤ H := Nat.cast_nonneg ℓ
  set z : ℚ := (2 : ℚ) ^ k
  have hz4 : 4 ≤ z := by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk2
    have h4k : 4 ≤ 2 ^ k := by omega
    dsimp [z]
    exact_mod_cast h4k
  set X : ℚ := (x : ℚ) - (H + z)
  set Y : ℚ := (y : ℚ) - (H + z)
  have hX : 0 ≤ X := by
    have : (ℓ : ℚ) + (2 : ℚ) ^ k ≤ (x : ℚ) := by exact_mod_cast hx
    dsimp [X, H, z]
    linarith
  have hY : 0 ≤ Y := by
    have : (ℓ : ℚ) + (2 : ℚ) ^ k ≤ (y : ℚ) := by exact_mod_cast hy
    dsimp [Y, H, z]
    linarith
  have hp1 : 1 ≤ (p : ℚ) := by exact_mod_cast hp
  have hd_lb : H + ((k : ℚ) - 3) / 2 ≤ d0 := by
    dsimp [d0]
    unfold broomThreshold
    have hz1 : 0 < z - 1 := by linarith
    have h2z1 : 0 < 2 * (z - 1) := by linarith
    have hk_pos : 0 ≤ (k : ℚ) := Nat.cast_nonneg k
    have hchi : ((k : ℚ) - 3) / 2 + 3 / 2 ≤ (k : ℚ) * z / (2 * (z - 1)) := by
      rw [le_div_iff₀ h2z1]
      nlinarith
    split_ifs with hℓ0
    · subst hℓ0
      have hH0 : H = 0 := by simp [H]
      linarith
    · have hrho1 : 0 < H + z + 1 := by linarith
      have h2rho1 : 0 < 2 * (H + z + 1) := by linarith
      have hcorr : 3 * (H - 1) / (2 * (H + z + 1)) ≤ 3 / 2 := by
        rw [div_le_iff₀ h2rho1]
        linarith
      linarith
  have hk_par : k = 2 * g ∨ k = 2 * g + 1 := by omega
  rcases hk_par with hk_even | hk_odd
  · 
    have hb : (k + 1) / 2 = g := by omega
    have hkb : k - (k + 1) / 2 = g := by omega
    have hL_eq : (2 : ℚ) ^ ((k + 1) / 2) = J := by rw [hb]
    have hJ_eq : (2 : ℚ) ^ (k - (k + 1) / 2) = J := by rw [hkb]
    have hz_eq : z = J ^ 2 := by
      dsimp [z, J]
      rw [hk_even, mul_comm, pow_mul]
    have hk_cast : (k : ℚ) = 2 * (g : ℚ) := by exact_mod_cast hk_even
    have hb_cast : (((k + 1) / 2 : ℕ) : ℚ) = (g : ℚ) := by rw [hb]
    have hkb_cast : ((k - (k + 1) / 2 : ℕ) : ℚ) = (g : ℚ) := by rw [hkb]
    have hHW1 : 1 ≤ H + W := by
      rcases hlk with ⟨hℓ1, _⟩ | ⟨hℓ0, hk3⟩
      · have : (1 : ℚ) ≤ (ℓ : ℚ) := by exact_mod_cast hℓ1
        dsimp [H]
        linarith
      · have hg2 : 2 ≤ g := by omega
        have hJ4 : 4 ≤ J := by
          have : 2 ^ 2 ≤ 2 ^ g := Nat.pow_le_pow_right (by omega) hg2
          have h4g : 4 ≤ 2 ^ g := by omega
          dsimp [J]
          exact_mod_cast h4g
        linarith
    set dN_avoid : ℚ := ((H + 2) * J - 1) * (x : ℚ) + (J - 1) * (y : ℚ) - (H + 1) * (z - 1)
    set dN_root_neg : ℚ := (H + 1) * (x : ℚ) * (y : ℚ) + (H + 1 + z - J) * (x : ℚ) +
      (H + 1 + z - (H + 2) * J) * (y : ℚ) + (z - 1)
    set sig_avoid_d0 : ℚ := (J * (H + 2) * (H + 1 + (g : ℚ)) / 2 * (x : ℚ) +
      J * (g : ℚ) / 2 * (y : ℚ) - (H + 1) * (H + 2) * (z - 1) / 2 - z * (2 * (g : ℚ)) * (H + 1) / 2) -
      (1 + d0) * dN_avoid +
      ((H + 2) * J - 1 - (J - 1) * (y : ℚ) + (H + 1) * (z - 1)) * u +
      (J - 1 - ((H + 2) * J - 1) * (x : ℚ) + (H + 1) * (z - 1)) * v
    have h_decomp : broomInsertionScore p x y ℓ k c u v d -
        (p : ℚ) * broomInsertionScore 1 x y ℓ k 0 u v d0 =
        (d - d0) * ((p : ℚ) * dN_root_neg - dN_avoid) +
        ((p : ℚ) - 1 - c) / 2 * dN_avoid +
        ((p : ℚ) - 1) * (-sig_avoid_d0 - dN_avoid / 2) := by
      dsimp only [broomInsertionScore]
      rw [hL_eq, hJ_eq, hb_cast, hkb_cast, hk_cast]
      dsimp [dN_avoid, dN_root_neg, sig_avoid_d0, H, z]
      push_cast
      ring
    have hdN_avoid_pos : 0 ≤ dN_avoid := by
      have h_id : dN_avoid =
          (13 + 9 * H + 2 * H ^ 2 + (24 + 11 * H + H ^ 2) * W + (15 + 5 * H) * W ^ 2 + (3 + H) * W ^ 3) +
          (1 + W) * Y + ((3 + 2 * H) + (2 + H) * W) * X := by
        dsimp [dN_avoid, X, Y, W]
        rw [hz_eq]
        ring
      rw [h_id]
      positivity
    have hdN_diff_pos : 0 ≤ dN_root_neg - dN_avoid := by
      have h_id2 : dN_root_neg - dN_avoid =
          (22 + 19 * H + 7 * H ^ 2 + H ^ 3 + (48 + 30 * H + 6 * H ^ 2) * W +
           (42 + 19 * H + 2 * H ^ 2) * W ^ 2 + (18 + 6 * H) * W ^ 3 + (3 + H) * W ^ 4) +
          ((4 + 4 * H + H ^ 2) + (5 + 3 * H) * W + (2 + H) * W ^ 2) * Y +
          ((4 + 4 * H + H ^ 2) + (5 + 3 * H) * W + (2 + H) * W ^ 2) * X +
          (1 + H) * X * Y := by
        dsimp [dN_root_neg, dN_avoid, X, Y, W]
        rw [hz_eq]
        ring
      rw [h_id2]
      positivity
    have h_avoid_id : 24 * (-sig_avoid_d0 - dN_avoid / 2) =
        24 * (d0 - (H + (2 * (g : ℚ) - 3) / 2)) * dN_avoid +
        24 * (v - 25 / 12) * (((H + 2) * J - 1) * (x : ℚ) - (J - 1) - (H + 1) * (z - 1)) +
        24 * (u - 25 / 12) * ((J - 1) * ((y : ℚ) - z) + (H + 2) + 2 * J * W) +
        24 * J * (W - H / 2) ^ 2 * u +
        6 * (H ^ 2 + 12 * H + 8) * J * ((x : ℚ) / 2 - u) +
        24 * G * ((((H + 2) * J) / 2 - 1) * (x : ℚ) + (W / 2) * (y : ℚ) + H + 1) +
        (4 * (H + W - 1) + 172 * H + 64 * H ^ 2 + 18 * H ^ 3 +
         (130 + 274 * H + 98 * H ^ 2 + 9 * H ^ 3) * W +
         (144 + 166 * H + 42 * H ^ 2) * W ^ 2 + (16 + 38 * H + 9 * H ^ 2) * W ^ 3 +
         (6 + 4 * H + 18 * H ^ 2 + (28 + 14 * H + 9 * H ^ 2) * W) * X +
         (26 + 24 * H + (38 + 24 * H) * W) * Y) := by
      dsimp [sig_avoid_d0, dN_avoid, X, Y, W, G]
      rw [hz_eq]
      ring
    have hv_coeff : 0 ≤ ((H + 2) * J - 1) * (x : ℚ) - (J - 1) - (H + 1) * (z - 1) := by
      have h_id : ((H + 2) * J - 1) * (x : ℚ) - (J - 1) - (H + 1) * (z - 1) =
          (8 + 8 * H + 2 * H ^ 2 + (15 + 10 * H + H ^ 2) * W + (10 + 5 * H) * W ^ 2 + (2 + H) * W ^ 3) +
          ((3 + 2 * H) + (2 + H) * W) * X := by
        dsimp [X, W]
        rw [hz_eq]
        ring
      rw [h_id]
      positivity
    have hu_coeff : 0 ≤ (J - 1) * ((y : ℚ) - z) + (H + 2) + 2 * J * W := by
      have h_id : (J - 1) * ((y : ℚ) - z) + (H + 2) + 2 * J * W =
          (2 + 2 * H + (4 + H) * W + 2 * W ^ 2) + (1 + W) * Y := by
        dsimp [Y, W]
        ring
      rw [h_id]
      positivity
    have hG_coeff : 0 ≤ (((H + 2) * J) / 2 - 1) * (x : ℚ) + (W / 2) * (y : ℚ) + H + 1 := by
      have h_id : 2 * ((((H + 2) * J) / 2 - 1) * (x : ℚ) + (W / 2) * (y : ℚ) + H + 1) =
          (10 + 12 * H + 2 * H ^ 2 + (20 + 15 * H + H ^ 2) * W + (14 + 6 * H) * W ^ 2 + (3 + H) * W ^ 3) +
          W * Y + ((2 + 2 * H) + (2 + H) * W) * X := by
        dsimp [X, Y, W]
        rw [hz_eq]
        ring
      linarith [show 0 ≤ (10 + 12 * H + 2 * H ^ 2 + (20 + 15 * H + H ^ 2) * W + (14 + 6 * H) * W ^ 2 + (3 + H) * W ^ 3) +
          W * Y + ((2 + 2 * H) + (2 + H) * W) * X by positivity]
    have h_avoid_pos : 0 ≤ -sig_avoid_d0 - dN_avoid / 2 := by
      have hd0_sub : 0 ≤ d0 - (H + (2 * (g : ℚ) - 3) / 2) := by
        rw [← hk_cast]
        linarith
      have hu' : 0 ≤ u - 25 / 12 := by linarith
      have hv' : 0 ≤ v - 25 / 12 := by linarith
      have hux : 0 ≤ (x : ℚ) / 2 - u := by linarith
      have hHW' : 0 ≤ H + W - 1 := by linarith
      have h24 : 0 ≤ 24 * (-sig_avoid_d0 - dN_avoid / 2) := by
        rw [h_avoid_id]
        positivity
      linarith
    have hd_sub : 0 ≤ d - d0 := by linarith
    have hp_sub : 0 ≤ (p : ℚ) - 1 := by linarith
    have hpc_sub : 0 ≤ ((p : ℚ) - 1 - c) / 2 := by linarith
    have hdN_root_pos : 0 ≤ (p : ℚ) * dN_root_neg - dN_avoid := by
      have : (p : ℚ) * dN_root_neg - dN_avoid =
          ((p : ℚ) - 1) * dN_root_neg + (dN_root_neg - dN_avoid) := by ring
      rw [this]
      have hdN_r : 0 ≤ dN_root_neg := by linarith
      positivity
    have h_diff_nonneg : 0 ≤ broomInsertionScore p x y ℓ k c u v d -
        (p : ℚ) * broomInsertionScore 1 x y ℓ k 0 u v d0 := by
      rw [h_decomp]
      positivity
    linarith
  · 
    have hb : (k + 1) / 2 = g + 1 := by omega
    have hkb : k - (k + 1) / 2 = g := by omega
    have hL_eq : (2 : ℚ) ^ ((k + 1) / 2) = 2 * J := by
      rw [hb, pow_succ']
    have hJ_eq : (2 : ℚ) ^ (k - (k + 1) / 2) = J := by rw [hkb]
    have hz_eq : z = 2 * J ^ 2 := by
      dsimp [z, J]
      rw [hk_odd, pow_add, pow_one, mul_comm 2 g, pow_mul]
      ring
    have hk_cast : (k : ℚ) = 2 * (g : ℚ) + 1 := by exact_mod_cast hk_odd
    have hb_cast : (((k + 1) / 2 : ℕ) : ℚ) = (g : ℚ) + 1 := by
      rw [hb]
      push_cast
      rfl
    have hkb_cast : ((k - (k + 1) / 2 : ℕ) : ℚ) = (g : ℚ) := by rw [hkb]
    set dN_avoid : ℚ := ((H + 2) * (2 * J) - 1) * (x : ℚ) + (J - 1) * (y : ℚ) - (H + 1) * (z - 1)
    set dN_root_neg : ℚ := (H + 1) * (x : ℚ) * (y : ℚ) + (H + 1 + z - 2 * J) * (x : ℚ) +
      (H + 1 + z - (H + 2) * J) * (y : ℚ) + (z - 1)
    set sig_avoid_d0 : ℚ := ((2 * J) * (H + 2) * (H + 1 + ((g : ℚ) + 1)) / 2 * (x : ℚ) +
      J * (g : ℚ) / 2 * (y : ℚ) - (H + 1) * (H + 2) * (z - 1) / 2 - z * (2 * (g : ℚ) + 1) * (H + 1) / 2) -
      (1 + d0) * dN_avoid +
      ((H + 2) * (2 * J) - 1 - (J - 1) * (y : ℚ) + (H + 1) * (z - 1)) * u +
      (J - 1 - ((H + 2) * (2 * J) - 1) * (x : ℚ) + (H + 1) * (z - 1)) * v
    have h_decomp : broomInsertionScore p x y ℓ k c u v d -
        (p : ℚ) * broomInsertionScore 1 x y ℓ k 0 u v d0 =
        (d - d0) * ((p : ℚ) * dN_root_neg - dN_avoid) +
        ((p : ℚ) - 1 - c) / 2 * dN_avoid +
        ((p : ℚ) - 1) * (-sig_avoid_d0 - dN_avoid / 2) := by
      dsimp only [broomInsertionScore]
      rw [hL_eq, hJ_eq, hb_cast, hkb_cast, hk_cast]
      dsimp [dN_avoid, dN_root_neg, sig_avoid_d0, H, z]
      push_cast
      ring
    have hdN_avoid_pos : 0 ≤ dN_avoid := by
      have h_id : dN_avoid =
          (57 + 33 * H + 4 * H ^ 2 + (96 + 45 * H + 2 * H ^ 2) * W + (54 + 22 * H) * W ^ 2 + (10 + 4 * H) * W ^ 3) +
          (1 + W) * Y + ((7 + 4 * H) + (4 + 2 * H) * W) * X := by
        dsimp [dN_avoid, X, Y, W]
        rw [hz_eq]
        ring
      rw [h_id]
      positivity
    have hdN_diff_pos : 0 ≤ dN_root_neg - dN_avoid := by
      have h_id : dN_root_neg - dN_avoid =
          (94 + 57 * H + 13 * H ^ 2 + H ^ 3 + (216 + 103 * H + 13 * H ^ 2) * W +
           (192 + 74 * H + 4 * H ^ 2) * W ^ 2 + (78 + 26 * H) * W ^ 3 + (12 + 4 * H) * W ^ 4) +
          ((12 + 8 * H + H ^ 2) + (13 + 7 * H) * W + (4 + 2 * H) * W ^ 2) * Y +
          ((6 + 6 * H + H ^ 2) + (10 + 6 * H) * W + (4 + 2 * H) * W ^ 2) * X +
          (1 + H) * X * Y := by
        dsimp [dN_root_neg, dN_avoid, X, Y, W]
        rw [hz_eq]
        ring
      rw [h_id]
      positivity
    have h_avoid_id : 24 * (-sig_avoid_d0 - dN_avoid / 2) =
        24 * (d0 - (H + (2 * (g : ℚ) - 2) / 2)) * dN_avoid +
        24 * (v - 25 / 12) * (((H + 2) * (2 * J) - 1) * (x : ℚ) - (J - 1) - (H + 1) * (z - 1)) +
        24 * (u - 25 / 12) * ((J - 1) * ((y : ℚ) - z) + (H + 2) + 2 * (2 * J) * W) +
        24 * (2 * J) * (W - H / 2) ^ 2 * u +
        6 * (H ^ 2 + 12 * H + 8) * (2 * J) * ((x : ℚ) / 2 - u) +
        24 * G * ((((H + 2) * (2 * J)) / 2 - 1) * (x : ℚ) + (W / 2) * (y : ℚ) + H + 1) +
        ((376 + 524 * H + 260 * H ^ 2 + 36 * H ^ 3 +
          (1086 + 858 * H + 388 * H ^ 2 + 18 * H ^ 3) * W +
          (720 + 500 * H + 192 * H ^ 2) * W ^ 2 + (112 + 104 * H + 36 * H ^ 2) * W ^ 3) +
         (50 + 32 * H + 36 * H ^ 2 + (56 + 28 * H + 18 * H ^ 2) * W) * X +
         (38 + 24 * H + (50 + 24 * H) * W) * Y) := by
      dsimp [sig_avoid_d0, dN_avoid, X, Y, W, G]
      rw [hz_eq]
      ring
    have hv_coeff : 0 ≤ ((H + 2) * (2 * J) - 1) * (x : ℚ) - (J - 1) - (H + 1) * (z - 1) := by
      have h_id : ((H + 2) * (2 * J) - 1) * (x : ℚ) - (J - 1) - (H + 1) * (z - 1) =
          (48 + 32 * H + 4 * H ^ 2 + (79 + 44 * H + 2 * H ^ 2) * W + (44 + 22 * H) * W ^ 2 + (8 + 4 * H) * W ^ 3) +
          ((7 + 4 * H) + (4 + 2 * H) * W) * X := by
        dsimp [X, W]
        rw [hz_eq]
        ring
      rw [h_id]
      positivity
    have hu_coeff : 0 ≤ (J - 1) * ((y : ℚ) - z) + (H + 2) + 2 * (2 * J) * W := by
      have h_id : (J - 1) * ((y : ℚ) - z) + (H + 2) + 2 * (2 * J) * W =
          (2 + 2 * H + (8 + H) * W + 4 * W ^ 2) + (1 + W) * Y := by
        dsimp [Y, W]
        ring
      rw [h_id]
      positivity
    have hG_coeff : 0 ≤ (((H + 2) * (2 * J)) / 2 - 1) * (x : ℚ) + (W / 2) * (y : ℚ) + H + 1 := by
      have h_id : 2 * ((((H + 2) * (2 * J)) / 2 - 1) * (x : ℚ) + (W / 2) * (y : ℚ) + H + 1) =
          (50 + 40 * H + 4 * H ^ 2 + (88 + 53 * H + 2 * H ^ 2) * W + (52 + 24 * H) * W ^ 2 + (10 + 4 * H) * W ^ 3) +
          W * Y + ((6 + 4 * H) + (4 + 2 * H) * W) * X := by
        dsimp [X, Y, W]
        rw [hz_eq]
        ring
      linarith [show 0 ≤ (50 + 40 * H + 4 * H ^ 2 + (88 + 53 * H + 2 * H ^ 2) * W + (52 + 24 * H) * W ^ 2 + (10 + 4 * H) * W ^ 3) +
          W * Y + ((6 + 4 * H) + (4 + 2 * H) * W) * X by positivity]
    have h_avoid_pos : 0 ≤ -sig_avoid_d0 - dN_avoid / 2 := by
      have hd0_sub : 0 ≤ d0 - (H + (2 * (g : ℚ) - 2) / 2) := by
        have : H + ((k : ℚ) - 3) / 2 = H + (2 * (g : ℚ) - 2) / 2 := by
          rw [hk_cast]
          ring
        linarith
      have hu' : 0 ≤ u - 25 / 12 := by linarith
      have hv' : 0 ≤ v - 25 / 12 := by linarith
      have hux : 0 ≤ (x : ℚ) / 2 - u := by linarith
      have h24 : 0 ≤ 24 * (-sig_avoid_d0 - dN_avoid / 2) := by
        rw [h_avoid_id]
        positivity
      linarith
    have hd_sub : 0 ≤ d - d0 := by linarith
    have hp_sub : 0 ≤ (p : ℚ) - 1 := by linarith
    have hpc_sub : 0 ≤ ((p : ℚ) - 1 - c) / 2 := by linarith
    have hdN_root_pos : 0 ≤ (p : ℚ) * dN_root_neg - dN_avoid := by
      have : (p : ℚ) * dN_root_neg - dN_avoid =
          ((p : ℚ) - 1) * dN_root_neg + (dN_root_neg - dN_avoid) := by ring
      rw [this]
      have hdN_r : 0 ≤ dN_root_neg := by linarith
      positivity
    have h_diff_nonneg : 0 ≤ broomInsertionScore p x y ℓ k c u v d -
        (p : ℚ) * broomInsertionScore 1 x y ℓ k 0 u v d0 := by
      rw [h_decomp]
      positivity
    linarith

theorem broom_base_score_pos_small_k : ∀ (ℓ k x y : ℕ) (u v : ℚ),
    ((1 ≤ ℓ ∧ k = 2) ∨ k = 3) →
    ℓ + 2 ^ k ≤ x → ℓ + 2 ^ k ≤ y →
    (25 : ℚ) / 12 ≤ u → u ≤ (x : ℚ) / 2 →
    (25 : ℚ) / 12 ≤ v → v ≤ (y : ℚ) / 2 →
    0 < broomInsertionScore 1 x y ℓ k 0 u v (broomThreshold ℓ k) +
      broomInsertionScore 1 y x ℓ k 0 v u (broomThreshold ℓ k) :=
by
  intro ℓ k x y u v hlk hx hy hu1 hu2 hv1 hv2
  rcases hlk with ⟨hℓ1, rfl⟩ | rfl
  · 
    set d0 : ℚ := broomThreshold ℓ 2
    set H : ℚ := (ℓ : ℚ) - 1
    have hH : 0 ≤ H := by
      have : (1 : ℚ) ≤ (ℓ : ℚ) := by exact_mod_cast hℓ1
      linarith
    have hd0 : 6 * (H + 6) * d0 - (6 * H ^ 2 + 41 * H + 84) = 0 := by
      dsimp only [d0, broomThreshold, H]
      rw [if_neg (by omega : ℓ ≠ 0)]
      norm_num
      have hden : (ℓ : ℚ) + 4 + 1 ≠ 0 := by positivity
      field_simp
      ring
    have h_dir : ∀ (x' y' : ℕ) (u' v' : ℚ),
        ℓ + 2 ^ 2 ≤ x' → ℓ + 2 ^ 2 ≤ y' →
        u' ≤ (x' : ℚ) / 2 → v' ≤ (y' : ℚ) / 2 →
        0 < broomInsertionScore 1 x' y' ℓ 2 0 u' v' d0 := by
      intro x' y' u' v' hx' hy' hu' hv'
      set X' : ℚ := (x' : ℚ) - (H + 5)
      set Y' : ℚ := (y' : ℚ) - (H + 5)
      have hX' : 0 ≤ X' := by
        have : (ℓ : ℚ) + 4 ≤ (x' : ℚ) := by exact_mod_cast hx'
        dsimp only [X', H]
        linarith
      have hY' : 0 ≤ Y' := by
        have : (ℓ : ℚ) + 4 ≤ (y' : ℚ) := by exact_mod_cast hy'
        dsimp only [Y', H]
        linarith
      have hu'_diff : 0 ≤ (x' : ℚ) / 2 - u' := by linarith
      have hv'_diff : 0 ≤ (y' : ℚ) / 2 - v' := by linarith
      set coeff_d2 : ℚ := (H + 2) * (x' : ℚ) * (y' : ℚ) - (H + 1) * ((x' : ℚ) + (y' : ℚ)) + 3 * H + 9
      have hid : 72 * (H + 6) * broomInsertionScore 1 x' y' ℓ 2 0 u' v' d0
          - 12 * coeff_d2 * (6 * (H + 6) * d0 - (6 * H ^ 2 + 41 * H + 84)) =
          72 * (H + 6) * ((2 * H + 3) * Y' + 2 * H ^ 2 + 9 * H + 5) * ((x' : ℚ) / 2 - u')
          + 72 * (H + 6) * ((2 * H + 3) * X' + 2 * H ^ 2 + 9 * H + 5) * ((y' : ℚ) / 2 - v')
          + (1440 + 4020 * H + 4680 * H ^ 2 + 2184 * H ^ 3 + 456 * H ^ 4 + 36 * H ^ 5)
          + (864 + 900 * H + 864 * H ^ 2 + 312 * H ^ 3 + 36 * H ^ 4) * (X' + Y')
          + (288 + 192 * H + 168 * H ^ 2 + 36 * H ^ 3) * X' * Y' := by
        dsimp only [broomInsertionScore, H, X', Y', coeff_d2]
        norm_num
        ring
      have hrhs_pos : 0 <
          72 * (H + 6) * ((2 * H + 3) * Y' + 2 * H ^ 2 + 9 * H + 5) * ((x' : ℚ) / 2 - u')
          + 72 * (H + 6) * ((2 * H + 3) * X' + 2 * H ^ 2 + 9 * H + 5) * ((y' : ℚ) / 2 - v')
          + (1440 + 4020 * H + 4680 * H ^ 2 + 2184 * H ^ 3 + 456 * H ^ 4 + 36 * H ^ 5)
          + (864 + 900 * H + 864 * H ^ 2 + 312 * H ^ 3 + 36 * H ^ 4) * (X' + Y')
          + (288 + 192 * H + 168 * H ^ 2 + 36 * H ^ 3) * X' * Y' := by positivity
      rw [hd0, mul_zero, sub_zero] at hid
      have hH6 : 0 < 72 * (H + 6) := by positivity
      nlinarith
    have h1 := h_dir x y u v hx hy hu2 hv2
    have h2 := h_dir y x v u hy hx hv2 hu2
    linarith
  · 
    rcases (by omega : ℓ = 0 ∨ 1 ≤ ℓ) with rfl | hℓ1
    · 
      set d0 : ℚ := broomThreshold 0 3
      have hd0 : d0 = 12 / 7 := by
        dsimp only [d0, broomThreshold]
        rw [if_pos rfl]
        norm_num
      set X : ℚ := (x : ℚ) - 8
      set Y : ℚ := (y : ℚ) - 8
      have hX : 0 ≤ X := by
        have : (8 : ℚ) ≤ (x : ℚ) := by exact_mod_cast hx
        dsimp only [X]
        linarith
      have hY : 0 ≤ Y := by
        have : (8 : ℚ) ≤ (y : ℚ) := by exact_mod_cast hy
        dsimp only [Y]
        linarith
      have hu_diff : 0 ≤ u - 25 / 12 := by linarith
      have hv_diff : 0 ≤ v - 25 / 12 := by linarith
      have hid : 42 * (broomInsertionScore 1 x y 0 3 0 u v d0 +
          broomInsertionScore 1 y x 0 3 0 v u d0) =
          26 + 330 * (X + Y) + 144 * X * Y + 1092 * (u - 25 / 12) + 1092 * (v - 25 / 12) := by
        rw [hd0]
        dsimp only [broomInsertionScore, X, Y]
        norm_num
        ring
      have hrhs_pos : 0 < 26 + 330 * (X + Y) + 144 * X * Y +
          1092 * (u - 25 / 12) + 1092 * (v - 25 / 12) := by positivity
      linarith
    · 
      set d0 : ℚ := broomThreshold ℓ 3
      set H : ℚ := (ℓ : ℚ) - 1
      have hH : 0 ≤ H := by
        have : (1 : ℚ) ≤ (ℓ : ℚ) := by exact_mod_cast hℓ1
        linarith
      have hd0 : 14 * (H + 10) * d0 - (14 * H ^ 2 + 157 * H + 380) = 0 := by
        dsimp only [d0, broomThreshold, H]
        rw [if_neg (by omega : ℓ ≠ 0)]
        norm_num
        have hden : (ℓ : ℚ) + 8 + 1 ≠ 0 := by positivity
        field_simp
        ring
      set X : ℚ := (x : ℚ) - (H + 9)
      set Y : ℚ := (y : ℚ) - (H + 9)
      have hX : 0 ≤ X := by
        have : (ℓ : ℚ) + 8 ≤ (x : ℚ) := by exact_mod_cast hx
        dsimp only [X, H]
        linarith
      have hY : 0 ≤ Y := by
        have : (ℓ : ℚ) + 8 ≤ (y : ℚ) := by exact_mod_cast hy
        dsimp only [Y, H]
        linarith
      have hu_diff : 0 ≤ (x : ℚ) / 2 - u := by linarith
      have hv_diff : 0 ≤ (y : ℚ) / 2 - v := by linarith
      set coeff_d3 : ℚ := 2 * (H + 2) * (x : ℚ) * (y : ℚ) - (4 * H + 2) * ((x : ℚ) + (y : ℚ)) + 14 * (H + 3)
      have hid : 168 * (H + 10) * (broomInsertionScore 1 x y ℓ 3 0 u v d0 +
          broomInsertionScore 1 y x ℓ 3 0 v u d0)
          - 12 * coeff_d3 * (14 * (H + 10) * d0 - (14 * H ^ 2 + 157 * H + 380)) =
          168 * (H + 10) * ((6 * H + 6) * Y + 6 * H ^ 2 + 42 * H + 10) * ((x : ℚ) / 2 - u)
          + 168 * (H + 10) * ((6 * H + 6) * X + 6 * H ^ 2 + 42 * H + 10) * ((y : ℚ) / 2 - v)
          + (164160 + 1896 * H + 59040 * H ^ 2 + 25728 * H ^ 3 + 3600 * H ^ 4 + 168 * H ^ 5)
          + (30720 + 984 * H + 8592 * H ^ 2 + 2424 * H ^ 3 + 168 * H ^ 4) * (X + Y)
          + (4800 + 192 * H + 1248 * H ^ 2 + 168 * H ^ 3) * X * Y := by
        dsimp only [broomInsertionScore, H, X, Y, coeff_d3]
        norm_num
        ring
      have hrhs_pos : 0 <
          168 * (H + 10) * ((6 * H + 6) * Y + 6 * H ^ 2 + 42 * H + 10) * ((x : ℚ) / 2 - u)
          + 168 * (H + 10) * ((6 * H + 6) * X + 6 * H ^ 2 + 42 * H + 10) * ((y : ℚ) / 2 - v)
          + (164160 + 1896 * H + 59040 * H ^ 2 + 25728 * H ^ 3 + 3600 * H ^ 4 + 168 * H ^ 5)
          + (30720 + 984 * H + 8592 * H ^ 2 + 2424 * H ^ 3 + 168 * H ^ 4) * (X + Y)
          + (4800 + 192 * H + 1248 * H ^ 2 + 168 * H ^ 3) * X * Y := by positivity
      rw [hd0, mul_zero, sub_zero] at hid
      have hH10 : 0 < 168 * (H + 10) := by positivity
      nlinarith

theorem broom_base_score_pos_even_k_ge_four : ∀ (ℓ g x y : ℕ) (u v : ℚ),
    2 ≤ g →
    ℓ + 2 ^ (2 * g) ≤ x → ℓ + 2 ^ (2 * g) ≤ y →
    (25 : ℚ) / 12 ≤ u → u ≤ (x : ℚ) / 2 →
    (25 : ℚ) / 12 ≤ v → v ≤ (y : ℚ) / 2 →
    0 < broomInsertionScore 1 x y ℓ (2 * g) 0 u v (broomThreshold ℓ (2 * g)) :=
by
  intro ℓ g x y u v hg2 hx hy hu1 hu2 hv1 hv2
  set d0 : ℚ := broomThreshold ℓ (2 * g)
  set J : ℚ := (2 : ℚ) ^ g
  have hJ4 : 4 ≤ J := by
    dsimp [J]
    have : 2 ^ 2 ≤ 2 ^ g := Nat.pow_le_pow_right (by omega) hg2
    exact_mod_cast this
  set W : ℚ := J - 4
  have hW : 0 ≤ W := by linarith
  set G2 : ℚ := (g : ℚ) - 2
  have hG2 : 0 ≤ G2 := by
    have : (2 : ℚ) ≤ (g : ℚ) := by exact_mod_cast hg2
    linarith
  set H0 : ℚ := (ℓ : ℚ)
  have hH0 : 0 ≤ H0 := Nat.cast_nonneg ℓ
  set z : ℚ := (2 : ℚ) ^ (2 * g)
  have hz_eq : z = J ^ 2 := by
    dsimp [z, J]
    rw [mul_comm, pow_mul]
  have hz16 : 16 ≤ z := by
    rw [hz_eq]
    nlinarith
  set ρ : ℚ := H0 + z
  set X : ℚ := (x : ℚ) - ρ
  set Y : ℚ := (y : ℚ) - ρ
  have hX : 0 ≤ X := by
    have : (ℓ : ℚ) + (2 : ℚ) ^ (2 * g) ≤ (x : ℚ) := by exact_mod_cast hx
    linarith
  have hY : 0 ≤ Y := by
    have : (ℓ : ℚ) + (2 : ℚ) ^ (2 * g) ≤ (y : ℚ) := by exact_mod_cast hy
    linarith
  have hb : (2 * g + 1) / 2 = g := by omega
  have hkb : 2 * g - (2 * g + 1) / 2 = g := by omega
  have hL_eq : (2 : ℚ) ^ ((2 * g + 1) / 2) = J := by rw [hb]
  have hJ_eq : (2 : ℚ) ^ (2 * g - (2 * g + 1) / 2) = J := by rw [hkb]
  have hb_cast : (((2 * g + 1) / 2 : ℕ) : ℚ) = (g : ℚ) := by rw [hb]
  have hkb_cast : ((2 * g - (2 * g + 1) / 2 : ℕ) : ℚ) = (g : ℚ) := by rw [hkb]
  set corr : ℚ := if ℓ = 0 then 0 else 3 * (H0 - 1) / (2 * (ρ + 1))
  set d_lin2 : ℚ := H0 + 2 - corr
  set d_lin : ℚ := d_lin2 + G2
  have hd_lin : d_lin ≤ d0 := by
    dsimp [d0, d_lin, d_lin2, corr, G2, H0, ρ, z]
    unfold broomThreshold
    have h2z1 : 0 < 2 * ((2 : ℚ) ^ (2 * g) - 1) := by
      change 0 < 2 * (z - 1)
      linarith
    have hg_pos : 0 ≤ (g : ℚ) := Nat.cast_nonneg g
    have hchi : (g : ℚ) ≤ ((2 * g : ℕ) : ℚ) * (2 : ℚ) ^ (2 * g) / (2 * ((2 : ℚ) ^ (2 * g) - 1)) := by
      rw [le_div_iff₀ h2z1]
      push_cast
      nlinarith
    split_ifs with hℓ0
    · have hℓ0_q : (ℓ : ℚ) = 0 := by exact_mod_cast hℓ0
      linarith
    · linarith
  set dN_avoid : ℚ := ((H0 + 2) * J - 1) * (x : ℚ) + (J - 1) * (y : ℚ) - (H0 + 1) * (z - 1)
  set dN_root_neg : ℚ := (H0 + 1) * (x : ℚ) * (y : ℚ) + (H0 + 1 + z - J) * (x : ℚ) +
    (H0 + 1 + z - (H0 + 2) * J) * (y : ℚ) + (z - 1)
  let score2 (d : ℚ) : ℚ :=
    let h : ℚ := H0 + 1
    let t_P2 : ℚ := H0 * (H0 + 1) / 2 + z * (h + 2)
    let c_xy_0 : ℚ := d * h - H0 * (H0 + 1) / 2
    let c_x_0 : ℚ := d * (h + z - J) + J * (h + 1) - t_P2
    let c_y_0 : ℚ := d * (h + z - (h + 1) * J) + J * (h * (h + 1) + 2 * (h + 1)) / 2 - t_P2
    let c_1_0 : ℚ := d * (z - 1) + h * (h + 1) / 2 - t_P2
    let sig_root : ℚ := c_xy_0 * (x : ℚ) * (y : ℚ) + c_x_0 * (x : ℚ) + c_y_0 * (y : ℚ) + c_1_0
      + (1 + J * (y : ℚ)) * (J - h - 1) * u + (1 + h + J * (x : ℚ)) * (J - 1) * v
    let dR_avoid_0 : ℚ := J * (h + 1) * (h + 2) / 2 * (x : ℚ)
      + J * (y : ℚ) - h * (h + 1) * (z - 1) / 2 - 2 * z * h
    let sig_avoid_0 : ℚ := dR_avoid_0 - (1 + d) * dN_avoid
      + ((h + 1) * J - 1 - (J - 1) * (y : ℚ) + h * (z - 1)) * u
      + (J - 1 - ((h + 1) * J - 1) * (x : ℚ) + h * (z - 1)) * v
    sig_root + sig_avoid_0
  have h_step : broomInsertionScore 1 x y ℓ (2 * g) 0 u v d0 - score2 d_lin2 =
      (d0 - d_lin) * (dN_root_neg - dN_avoid) +
      G2 * ((H0 + 1) * (x : ℚ) * (y : ℚ) + (H0 + 2 - (H0 + 3) * J / 2) * ((x : ℚ) + (y : ℚ)) - (H0 + 2)) := by
    dsimp only [broomInsertionScore, score2]
    rw [hL_eq, hJ_eq, hb_cast, hkb_cast]
    dsimp [d_lin, G2, dN_root_neg, dN_avoid, H0, z]
    push_cast
    ring
  have hdN_diff_pos : 0 ≤ dN_root_neg - dN_avoid := by
    have hx_pos : 0 ≤ (x : ℚ) := Nat.cast_nonneg x
    have hy_pos : 0 ≤ (y : ℚ) := Nat.cast_nonneg y
    have h_id : dN_root_neg - dN_avoid =
        (H0 + 1) * (H0 + X) * (y : ℚ) / 2 + (H0 + 1) * (x : ℚ) * (H0 + Y) / 2 +
        ((H0 + 1) * (2 + W) * (4 + W) / 2 + (2 + W) * (4 + W) + H0 + 2) * (y : ℚ) +
        ((H0 + 1) * (2 + W) * (4 + W) / 2 + (2 + W) * (4 + W) + H0 + 2) * (x : ℚ) +
        (H0 + 2) * (15 + 8 * W + W ^ 2) := by
      dsimp [dN_root_neg, dN_avoid, X, Y, ρ, W]
      rw [hz_eq]
      ring
    rw [h_id]
    positivity
  have hG2_coeff : 0 ≤ (H0 + 1) * (x : ℚ) * (y : ℚ) + (H0 + 2 - (H0 + 3) * J / 2) * ((x : ℚ) + (y : ℚ)) - (H0 + 2) := by
    have hx_pos : 0 ≤ (x : ℚ) := Nat.cast_nonneg x
    have hy_pos : 0 ≤ (y : ℚ) := Nat.cast_nonneg y
    have h_id : (H0 + 1) * (x : ℚ) * (y : ℚ) + (H0 + 2 - (H0 + 3) * J / 2) * ((x : ℚ) + (y : ℚ)) - (H0 + 2) =
        (H0 + 1) * (H0 + X) * (y : ℚ) / 2 + (H0 + 1) * (x : ℚ) * (H0 + Y) / 2 +
        (((1 + 3 * H0 + (1 + H0) * W) * (4 + W) + 2 * H0 + 4) / 2) * ((x : ℚ) + (y : ℚ) - 1) +
        ((1 + 3 * H0 + (1 + H0) * W) * (4 + W)) / 2 := by
      dsimp [X, Y, ρ, W]
      rw [hz_eq]
      ring
    rw [h_id]
    have hxy1 : 0 ≤ (x : ℚ) + (y : ℚ) - 1 := by linarith
    positivity
  have h_ge_score2 : score2 d_lin2 ≤ broomInsertionScore 1 x y ℓ (2 * g) 0 u v d0 := by
    have hd0_sub : 0 ≤ d0 - d_lin := by linarith
    have : 0 ≤ broomInsertionScore 1 x y ℓ (2 * g) 0 u v d0 - score2 d_lin2 := by
      rw [h_step]
      positivity
    linarith
  have h_score2_d : ∀ (d1 c1 : ℚ), score2 (d1 - c1) = score2 d1 - c1 * (dN_root_neg - dN_avoid) := by
    intro d1 c1
    dsimp [score2, dN_root_neg, dN_avoid]
    ring
  set C_u : ℚ := ((J - H0 - 3) * J + 1) * (y : ℚ) + (H0 + 3) * (J - 1) + (H0 + 1) * (z - 1)
  set C_v : ℚ := ((J - H0 - 3) * J + 1) * (x : ℚ) + (H0 + 3) * (J - 1) + (H0 + 1) * (z - 1)
  have hrho_pos : 0 < 24 * (ρ + 1) := by linarith
  suffices h_pos : 0 < 24 * (ρ + 1) * score2 d_lin2 by nlinarith
  by_cases hℓ0 : ℓ = 0
  · 
    have hH0_zero : H0 = 0 := by simp [H0, hℓ0]
    have hd_lin2_eq : d_lin2 = H0 + 2 := by simp [d_lin2, corr, hℓ0]
    rw [hd_lin2_eq]
    have h_id : 24 * (ρ + 1) * score2 (H0 + 2) =
        24 * (ρ + 1) * C_u * (u - 25 / 12) + 24 * (ρ + 1) * C_v * (v - 25 / 12) +
        (77656 + 171116 * W + 147592 * W ^ 2 + 65072 * W ^ 3 + 15636 * W ^ 4 + 1956 * W ^ 5 + 100 * W ^ 6) +
        (7922 + 10018 * W + 4684 * W ^ 2 + 962 * W ^ 3 + 74 * W ^ 4) * (X + Y) +
        (816 + 384 * W + 48 * W ^ 2) * X * Y := by
      dsimp [score2, dN_avoid, C_u, C_v, X, Y, ρ, W]
      rw [hH0_zero, hz_eq]
      ring
    have hCu_pos : 0 ≤ C_u := by
      have : C_u = ((1 + W) * (4 + W) + 1) * ((4 + W) ^ 2 + Y) + 3 * (3 + W) + ((4 + W) ^ 2 - 1) := by
        dsimp [C_u, Y, ρ, W]
        rw [hH0_zero, hz_eq]
        ring
      rw [this]
      have : 0 ≤ (4 + W) ^ 2 - 1 := by nlinarith
      positivity
    have hCv_pos : 0 ≤ C_v := by
      have : C_v = ((1 + W) * (4 + W) + 1) * ((4 + W) ^ 2 + X) + 3 * (3 + W) + ((4 + W) ^ 2 - 1) := by
        dsimp [C_v, X, ρ, W]
        rw [hH0_zero, hz_eq]
        ring
      rw [this]
      have : 0 ≤ (4 + W) ^ 2 - 1 := by nlinarith
      positivity
    have hu' : 0 ≤ u - 25 / 12 := by linarith
    have hv' : 0 ≤ v - 25 / 12 := by linarith
    rw [h_id]
    positivity
  · 
    have hℓ1 : 1 ≤ ℓ := by omega
    have h_clear : 24 * (ρ + 1) * score2 d_lin2 =
        24 * (ρ + 1) * score2 (H0 + 2) - 36 * (H0 - 1) * (dN_root_neg - dN_avoid) := by
      dsimp [d_lin2]
      rw [h_score2_d]
      dsimp [corr]
      rw [if_neg hℓ0]
      have h_div : 24 * (ρ + 1) * (3 * (H0 - 1) / (2 * (ρ + 1))) = 36 * (H0 - 1) := by
        rw [mul_div_assoc', div_eq_iff (by linarith : 2 * (ρ + 1) ≠ 0)]
        ring
      linear_combination -(dN_root_neg - dN_avoid) * h_div
    rw [h_clear]
    have h_low_low : ∀ (H : ℚ), H = H0 - 1 →
        24 * (ρ + 1) * score2 (H0 + 2) - 36 * (H0 - 1) * (dN_root_neg - dN_avoid) =
        24 * (ρ + 1) * C_u * (u - 25 / 12) + 24 * (ρ + 1) * C_v * (v - 25 / 12) +
        (272520 + 253784 * H + 86564 * H ^ 2 + 11024 * H ^ 3 + 600 * H ^ 4 + 12 * H ^ 5 +
         (461536 + 366544 * H + 104200 * H ^ 2 + 9332 * H ^ 3 + 264 * H ^ 4) * W +
         (333476 + 229200 * H + 54488 * H ^ 2 + 3216 * H ^ 3 + 36 * H ^ 4) * W ^ 2 +
         (130304 + 78976 * H + 15784 * H ^ 2 + 528 * H ^ 3) * W ^ 3 +
         (28888 + 15808 * H + 2700 * H ^ 2 + 36 * H ^ 3) * W ^ 4 +
         (3440 + 1748 * H + 264 * H ^ 2) * W ^ 5 +
         (172 + 84 * H + 12 * H ^ 2) * W ^ 6) +
        (24228 + 20174 * H + 5080 * H ^ 2 + 432 * H ^ 3 + 12 * H ^ 4 +
         (25600 + 18748 * H + 3814 * H ^ 2 + 180 * H ^ 3) * W +
         (10566 + 6974 * H + 1188 * H ^ 2 + 24 * H ^ 3) * W ^ 2 +
         (1992 + 1210 * H + 180 * H ^ 2) * W ^ 3 +
         (146 + 84 * H + 12 * H ^ 2) * W ^ 4) * (X + Y) +
        (2160 + 1560 * H + 264 * H ^ 2 + 12 * H ^ 3 +
         (960 + 672 * H + 96 * H ^ 2) * W +
         (120 + 84 * H + 12 * H ^ 2) * W ^ 2) * X * Y := by
      intro H hH_eq
      subst hH_eq
      dsimp [score2, dN_root_neg, dN_avoid, C_u, C_v, X, Y, ρ, W]
      rw [hz_eq]
      ring
    rcases (by omega : ℓ + 3 ≤ 2 ^ g ∨ 2 ^ g ≤ ℓ + 2) with hℓ_small | hℓ_large
    · 
      set H : ℚ := H0 - 1
      have hH : 0 ≤ H := by
        have : (1 : ℚ) ≤ (ℓ : ℚ) := by exact_mod_cast hℓ1
        linarith
      have hKJ : 0 ≤ J - H0 - 3 := by
        have : (ℓ : ℚ) + 3 ≤ (2 : ℚ) ^ g := by exact_mod_cast hℓ_small
        linarith
      have hy_pos : 0 ≤ (y : ℚ) := Nat.cast_nonneg y
      have hx_pos : 0 ≤ (x : ℚ) := Nat.cast_nonneg x
      have hz2 : 0 ≤ z - 2 := by linarith
      have hz1 : 0 ≤ z - 1 := by linarith
      have hJ1 : 0 ≤ J - 1 := by linarith
      have hCu_pos : 0 ≤ C_u := by
        dsimp [C_u]
        positivity
      have hCv_pos : 0 ≤ C_v := by
        dsimp [C_v]
        positivity
      have hu' : 0 ≤ u - 25 / 12 := by linarith
      have hv' : 0 ≤ v - 25 / 12 := by linarith
      rw [h_low_low H rfl]
      positivity
    · 
      set H : ℚ := H0 - (J - 2)
      have hH : 0 ≤ H := by
        have : (2 : ℚ) ^ g ≤ (ℓ : ℚ) + 2 := by exact_mod_cast hℓ_large
        linarith
      have hH0_eq : H0 = J - 2 + H := by ring
      rcases le_total 0 C_u with hCu | hCu <;> rcases le_total 0 C_v with hCv | hCv
      · 
        set H1 : ℚ := H0 - 1
        have hH1 : 0 ≤ H1 := by
          have : (1 : ℚ) ≤ (ℓ : ℚ) := by exact_mod_cast hℓ1
          linarith
        have hu' : 0 ≤ u - 25 / 12 := by linarith
        have hv' : 0 ≤ v - 25 / 12 := by linarith
        rw [h_low_low H1 rfl]
        positivity
      · 
        have h_id : 24 * (ρ + 1) * score2 (H0 + 2) - 36 * (H0 - 1) * (dN_root_neg - dN_avoid) =
            24 * (ρ + 1) * C_u * (u - 25 / 12) + 24 * (ρ + 1) * (-C_v) * ((y : ℚ) / 2 - v) +
            (643428 + 285030 * H + 88354 * H ^ 2 + 11284 * H ^ 3 + 612 * H ^ 4 + 12 * H ^ 5 +
             (1431904 + 505586 * H + 126662 * H ^ 2 + 11218 * H ^ 3 + 312 * H ^ 4) * W +
             (1363056 + 377910 * H + 74434 * H ^ 2 + 4080 * H ^ 3 + 36 * H ^ 4) * W ^ 2 +
             (724912 + 153830 * H + 22832 * H ^ 2 + 636 * H ^ 3) * W ^ 3 +
             (235464 + 36690 * H + 3840 * H ^ 2 + 36 * H ^ 3) * W ^ 4 +
             (47796 + 5110 * H + 336 * H ^ 2) * W ^ 5 +
             (5916 + 384 * H + 12 * H ^ 2) * W ^ 6 +
             (408 + 12 * H) * W ^ 7 + 12 * W ^ 8) +
            (40464 + 17880 * H + 4836 * H ^ 2 + 432 * H ^ 3 + 12 * H ^ 4 +
             (66228 + 21432 * H + 4524 * H ^ 2 + 216 * H ^ 3) * W +
             (44472 + 10272 * H + 1560 * H ^ 2 + 24 * H ^ 3) * W ^ 2 +
             (15624 + 2424 * H + 228 * H ^ 2) * W ^ 3 +
             (3012 + 276 * H + 12 * H ^ 2) * W ^ 4 +
             (300 + 12 * H) * W ^ 5 + 12 * W ^ 6) * X +
            (51294 + 18754 * H + 4852 * H ^ 2 + 432 * H ^ 3 + 12 * H ^ 4 +
             (81124 + 23192 * H + 4582 * H ^ 2 + 216 * H ^ 3) * W +
             (52404 + 11182 * H + 1572 * H ^ 2 + 24 * H ^ 3) * W ^ 2 +
             (17662 + 2602 * H + 228 * H ^ 2) * W ^ 3 +
             (3264 + 288 * H + 12 * H ^ 2) * W ^ 4 +
             (312 + 12 * H) * W ^ 5 + 12 * W ^ 6) * Y +
            (3312 + 1176 * H + 252 * H ^ 2 + 12 * H ^ 3 +
             (3300 + 792 * H + 120 * H ^ 2) * W +
             (1236 + 180 * H + 12 * H ^ 2) * W ^ 2 +
             (204 + 12 * H) * W ^ 3 + 12 * W ^ 4) * X * Y := by
          dsimp [score2, dN_root_neg, dN_avoid, C_u, C_v, X, Y, ρ, H, W]
          rw [hz_eq]
          ring
        have hu' : 0 ≤ u - 25 / 12 := by linarith
        have hvy : 0 ≤ (y : ℚ) / 2 - v := by linarith
        have hCv' : 0 ≤ -C_v := by linarith
        rw [h_id]
        positivity
      · 
        have h_id : 24 * (ρ + 1) * score2 (H0 + 2) - 36 * (H0 - 1) * (dN_root_neg - dN_avoid) =
            24 * (ρ + 1) * (-C_u) * ((x : ℚ) / 2 - u) + 24 * (ρ + 1) * C_v * (v - 25 / 12) +
            (643428 + 285030 * H + 88354 * H ^ 2 + 11284 * H ^ 3 + 612 * H ^ 4 + 12 * H ^ 5 +
             (1431904 + 505586 * H + 126662 * H ^ 2 + 11218 * H ^ 3 + 312 * H ^ 4) * W +
             (1363056 + 377910 * H + 74434 * H ^ 2 + 4080 * H ^ 3 + 36 * H ^ 4) * W ^ 2 +
             (724912 + 153830 * H + 22832 * H ^ 2 + 636 * H ^ 3) * W ^ 3 +
             (235464 + 36690 * H + 3840 * H ^ 2 + 36 * H ^ 3) * W ^ 4 +
             (47796 + 5110 * H + 336 * H ^ 2) * W ^ 5 +
             (5916 + 384 * H + 12 * H ^ 2) * W ^ 6 +
             (408 + 12 * H) * W ^ 7 + 12 * W ^ 8) +
            (51294 + 18754 * H + 4852 * H ^ 2 + 432 * H ^ 3 + 12 * H ^ 4 +
             (81124 + 23192 * H + 4582 * H ^ 2 + 216 * H ^ 3) * W +
             (52404 + 11182 * H + 1572 * H ^ 2 + 24 * H ^ 3) * W ^ 2 +
             (17662 + 2602 * H + 228 * H ^ 2) * W ^ 3 +
             (3264 + 288 * H + 12 * H ^ 2) * W ^ 4 +
             (312 + 12 * H) * W ^ 5 + 12 * W ^ 6) * X +
            (40464 + 17880 * H + 4836 * H ^ 2 + 432 * H ^ 3 + 12 * H ^ 4 +
             (66228 + 21432 * H + 4524 * H ^ 2 + 216 * H ^ 3) * W +
             (44472 + 10272 * H + 1560 * H ^ 2 + 24 * H ^ 3) * W ^ 2 +
             (15624 + 2424 * H + 228 * H ^ 2) * W ^ 3 +
             (3012 + 276 * H + 12 * H ^ 2) * W ^ 4 +
             (300 + 12 * H) * W ^ 5 + 12 * W ^ 6) * Y +
            (3312 + 1176 * H + 252 * H ^ 2 + 12 * H ^ 3 +
             (3300 + 792 * H + 120 * H ^ 2) * W +
             (1236 + 180 * H + 12 * H ^ 2) * W ^ 2 +
             (204 + 12 * H) * W ^ 3 + 12 * W ^ 4) * X * Y := by
          dsimp [score2, dN_root_neg, dN_avoid, C_u, C_v, X, Y, ρ, H, W]
          rw [hz_eq]
          ring
        have hux : 0 ≤ (x : ℚ) / 2 - u := by linarith
        have hv' : 0 ≤ v - 25 / 12 := by linarith
        have hCu' : 0 ≤ -C_u := by linarith
        rw [h_id]
        positivity
      · 
        have h_id : 24 * (ρ + 1) * score2 (H0 + 2) - 36 * (H0 - 1) * (dN_root_neg - dN_avoid) =
            24 * (ρ + 1) * (-C_u) * ((x : ℚ) / 2 - u) + 24 * (ρ + 1) * (-C_v) * ((y : ℚ) / 2 - v) +
            (662352 + 107616 * H + 53352 * H ^ 2 + 9024 * H ^ 3 + 564 * H ^ 4 + 12 * H ^ 5 +
             (1459488 + 160464 * H + 78912 * H ^ 2 + 9408 * H ^ 3 + 300 * H ^ 4) * W +
             (1378344 + 99660 * H + 49392 * H ^ 2 + 3624 * H ^ 3 + 36 * H ^ 4) * W ^ 2 +
             (728940 + 33024 * H + 16512 * H ^ 2 + 600 * H ^ 3) * W ^ 3 +
             (235968 + 6132 * H + 3072 * H ^ 2 + 36 * H ^ 3) * W ^ 4 +
             (47820 + 600 * H + 300 * H ^ 2) * W ^ 5 +
             (5916 + 24 * H + 12 * H ^ 2) * W ^ 6 +
             408 * W ^ 7 + 12 * W ^ 8) +
            (41832 + 4956 * H + 3240 * H ^ 2 + 384 * H ^ 3 + 12 * H ^ 4 +
             (67332 + 4812 * H + 3312 * H ^ 2 + 204 * H ^ 3) * W +
             (44760 + 1884 * H + 1260 * H ^ 2 + 24 * H ^ 3) * W ^ 2 +
             (15648 + 348 * H + 204 * H ^ 2) * W ^ 3 +
             (3012 + 24 * H + 12 * H ^ 2) * W ^ 4 +
             300 * W ^ 5 + 12 * W ^ 6) * (X + Y) +
            (2628 + 228 * H + 204 * H ^ 2 + 12 * H ^ 3 +
             (2748 + 120 * H + 108 * H ^ 2) * W +
             (1092 + 24 * H + 12 * H ^ 2) * W ^ 2 +
             192 * W ^ 3 + 12 * W ^ 4) * X * Y := by
          dsimp [score2, dN_root_neg, dN_avoid, C_u, C_v, X, Y, ρ, H, W]
          rw [hz_eq]
          ring
        have hux : 0 ≤ (x : ℚ) / 2 - u := by linarith
        have hvy : 0 ≤ (y : ℚ) / 2 - v := by linarith
        have hCu' : 0 ≤ -C_u := by linarith
        have hCv' : 0 ≤ -C_v := by linarith
        rw [h_id]
        positivity

theorem broom_base_score_pos_odd_k_ge_five : ∀ (ℓ g x y : ℕ) (u v : ℚ),
    2 ≤ g →
    ℓ + 2 ^ (2 * g + 1) ≤ x → ℓ + 2 ^ (2 * g + 1) ≤ y →
    (25 : ℚ) / 12 ≤ u → u ≤ (x : ℚ) / 2 →
    (25 : ℚ) / 12 ≤ v → v ≤ (y : ℚ) / 2 →
    0 < broomInsertionScore 1 x y ℓ (2 * g + 1) 0 u v (broomThreshold ℓ (2 * g + 1)) :=
by
  intro ℓ g x y u v hg2 hx hy hu1 hu2 hv1 hv2
  set d0 : ℚ := broomThreshold ℓ (2 * g + 1)
  set J : ℚ := (2 : ℚ) ^ g
  have hJ4 : 4 ≤ J := by
    dsimp [J]
    have : 2 ^ 2 ≤ 2 ^ g := Nat.pow_le_pow_right (by omega) hg2
    exact_mod_cast this
  set W : ℚ := J - 4
  have hW : 0 ≤ W := by linarith
  set G2 : ℚ := (g : ℚ) - 2
  have hG2 : 0 ≤ G2 := by
    have : (2 : ℚ) ≤ (g : ℚ) := by exact_mod_cast hg2
    linarith
  set H0 : ℚ := (ℓ : ℚ)
  have hH0 : 0 ≤ H0 := Nat.cast_nonneg ℓ
  set L : ℚ := 2 * J
  set z : ℚ := (2 : ℚ) ^ (2 * g + 1)
  have hz_eq : z = 2 * J ^ 2 := by
    dsimp [z, J]
    rw [pow_add, pow_one, mul_comm (2 : ℕ) g, pow_mul]
    ring
  have hz32 : 32 ≤ z := by
    rw [hz_eq]
    nlinarith
  set ρ : ℚ := H0 + z
  set X : ℚ := (x : ℚ) - ρ
  set Y : ℚ := (y : ℚ) - ρ
  have hX : 0 ≤ X := by
    have : (ℓ : ℚ) + (2 : ℚ) ^ (2 * g + 1) ≤ (x : ℚ) := by exact_mod_cast hx
    linarith
  have hY : 0 ≤ Y := by
    have : (ℓ : ℚ) + (2 : ℚ) ^ (2 * g + 1) ≤ (y : ℚ) := by exact_mod_cast hy
    linarith
  have hb : (2 * g + 1 + 1) / 2 = g + 1 := by omega
  have hkb : 2 * g + 1 - (2 * g + 1 + 1) / 2 = g := by omega
  have hL_eq : (2 : ℚ) ^ ((2 * g + 1 + 1) / 2) = L := by
    rw [hb, pow_add, pow_one]
    dsimp [L, J]
    ring
  have hJ_eq : (2 : ℚ) ^ (2 * g + 1 - (2 * g + 1 + 1) / 2) = J := by
    rw [hkb]
  have hb_cast : (((2 * g + 1 + 1) / 2 : ℕ) : ℚ) = (g : ℚ) + 1 := by
    rw [hb]
    push_cast
    rfl
  have hkb_cast : ((2 * g + 1 - (2 * g + 1 + 1) / 2 : ℕ) : ℚ) = (g : ℚ) := by
    rw [hkb]
  set corr : ℚ := if ℓ = 0 then 0 else 3 * (H0 - 1) / (2 * (ρ + 1))
  set d_lin2 : ℚ := H0 + 5 / 2 - corr
  set d_lin : ℚ := d_lin2 + G2
  have hd_lin : d_lin ≤ d0 := by
    dsimp [d0, d_lin, d_lin2, corr, G2, H0, ρ, z]
    unfold broomThreshold
    have h2z1 : 0 < 2 * ((2 : ℚ) ^ (2 * g + 1) - 1) := by
      change 0 < 2 * (z - 1)
      linarith
    have hg_pos : 0 ≤ (g : ℚ) := Nat.cast_nonneg g
    have hchi : (g : ℚ) + 1 / 2 ≤ ((2 * g + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (2 * g + 1) / (2 * ((2 : ℚ) ^ (2 * g + 1) - 1)) := by
      rw [le_div_iff₀ h2z1]
      push_cast
      nlinarith
    split_ifs with hℓ0
    · have hℓ0_q : (ℓ : ℚ) = 0 := by exact_mod_cast hℓ0
      linarith
    · linarith
  set dN_avoid : ℚ := ((H0 + 2) * L - 1) * (x : ℚ) + (J - 1) * (y : ℚ) - (H0 + 1) * (z - 1)
  set dN_root_neg : ℚ := (H0 + 1) * (x : ℚ) * (y : ℚ) + (H0 + 1 + z - L) * (x : ℚ) +
    (H0 + 1 + z - (H0 + 2) * J) * (y : ℚ) + (z - 1)
  let score2 (d : ℚ) : ℚ :=
    let h : ℚ := H0 + 1
    let t_P2 : ℚ := H0 * (H0 + 1) / 2 + z * (h + 5 / 2)
    let c_xy_0 : ℚ := d * h - H0 * (H0 + 1) / 2
    let c_x_0 : ℚ := d * (h + z - L) + L * (h + 3 / 2) - t_P2
    let c_y_0 : ℚ := d * (h + z - (h + 1) * J) + J * (h * (h + 1) + 2 * (h + 1)) / 2 - t_P2
    let c_1_0 : ℚ := d * (z - 1) + h * (h + 1) / 2 - t_P2
    let sig_root : ℚ := c_xy_0 * (x : ℚ) * (y : ℚ) + c_x_0 * (x : ℚ) + c_y_0 * (y : ℚ) + c_1_0
      + (1 + J * (y : ℚ)) * (L - h - 1) * u + (1 + h + L * (x : ℚ)) * (J - 1) * v
    let dR_avoid_0 : ℚ := L * (h + 1) * (h + 3) / 2 * (x : ℚ)
      + J * (y : ℚ) - h * (h + 1) * (z - 1) / 2 - (5 / 2) * z * h
    let sig_avoid_0 : ℚ := dR_avoid_0 - (1 + d) * dN_avoid
      + ((h + 1) * L - 1 - (J - 1) * (y : ℚ) + h * (z - 1)) * u
      + (J - 1 - ((h + 1) * L - 1) * (x : ℚ) + h * (z - 1)) * v
    sig_root + sig_avoid_0
  have h_step : broomInsertionScore 1 x y ℓ (2 * g + 1) 0 u v d0 - score2 d_lin2 =
      (d0 - d_lin) * (dN_root_neg - dN_avoid) +
      G2 * ((H0 + 1) * (x : ℚ) * (y : ℚ) + (H0 + 2 - (H0 + 3) * J) * (x : ℚ) +
        (H0 + 2 - (H0 + 3) * J / 2) * (y : ℚ) - (H0 + 2)) := by
    dsimp only [broomInsertionScore, score2]
    rw [hL_eq, hJ_eq, hb_cast, hkb_cast]
    dsimp [d_lin, G2, dN_root_neg, dN_avoid, H0, L, z]
    push_cast
    ring
  have hdN_diff_pos : 0 ≤ dN_root_neg - dN_avoid := by
    have hx_pos : 0 ≤ (x : ℚ) := Nat.cast_nonneg x
    have hy_pos : 0 ≤ (y : ℚ) := Nat.cast_nonneg y
    have h_id : dN_root_neg - dN_avoid =
        (H0 + 1) * (H0 + X) * (y : ℚ) / 2 + (H0 + 1) * (x : ℚ) * (H0 + Y) / 2 +
        ((H0 + 1) * (3 + W) * (4 + W) + 2 * (3 + W) * (4 + W) + H0 + 2) * (y : ℚ) +
        ((H0 + 1) * (2 + W) * (4 + W) + 2 * (2 + W) * (4 + W) + H0 + 2) * (x : ℚ) +
        (H0 + 2) * (31 + 16 * W + 2 * W ^ 2) := by
      dsimp [dN_root_neg, dN_avoid, L, X, Y, ρ, W]
      rw [hz_eq]
      ring
    rw [h_id]
    positivity
  have hG2_coeff : 0 ≤ (H0 + 1) * (x : ℚ) * (y : ℚ) + (H0 + 2 - (H0 + 3) * J) * (x : ℚ) +
      (H0 + 2 - (H0 + 3) * J / 2) * (y : ℚ) - (H0 + 2) := by
    have hx_pos : 0 ≤ (x : ℚ) := Nat.cast_nonneg x
    have hy_pos : 0 ≤ (y : ℚ) := Nat.cast_nonneg y
    have h_id : (H0 + 1) * (x : ℚ) * (y : ℚ) + (H0 + 2 - (H0 + 3) * J) * (x : ℚ) +
        (H0 + 2 - (H0 + 3) * J / 2) * (y : ℚ) - (H0 + 2) =
        (H0 + 1) * (H0 + X) * (y : ℚ) / 2 + (H0 + 1) * (x : ℚ) * (H0 + Y) / 2 +
        ((1 + 3 * H0 + (1 + H0) * W) * (4 + W) + H0 + 2) * ((x : ℚ) - 1) +
        ((5 + 7 * H0 + 2 * (1 + H0) * W) * (4 + W) / 2 + H0 + 2) * (y : ℚ) +
        (1 + 3 * H0 + (1 + H0) * W) * (4 + W) := by
      dsimp [X, Y, ρ, W]
      rw [hz_eq]
      ring
    rw [h_id]
    have hx1 : 0 ≤ (x : ℚ) - 1 := by linarith
    positivity
  have h_ge_score2 : score2 d_lin2 ≤ broomInsertionScore 1 x y ℓ (2 * g + 1) 0 u v d0 := by
    have hd0_sub : 0 ≤ d0 - d_lin := by linarith
    have : 0 ≤ broomInsertionScore 1 x y ℓ (2 * g + 1) 0 u v d0 - score2 d_lin2 := by
      rw [h_step]
      positivity
    linarith
  have h_score2_d : ∀ (d1 c1 : ℚ), score2 (d1 - c1) = score2 d1 - c1 * (dN_root_neg - dN_avoid) := by
    intro d1 c1
    dsimp [score2, dN_root_neg, dN_avoid]
    ring
  set C_u : ℚ := ((L - H0 - 3) * J + 1) * (y : ℚ) + (H0 + 3) * (L - 1) + (H0 + 1) * (z - 1)
  set C_v : ℚ := ((J - H0 - 3) * L + 1) * (x : ℚ) + (H0 + 3) * (J - 1) + (H0 + 1) * (z - 1)
  have hrho_pos : 0 < 24 * (ρ + 1) := by linarith
  suffices h_pos : 0 < 24 * (ρ + 1) * score2 d_lin2 by nlinarith
  by_cases hℓ0 : ℓ = 0
  · 
    have hH0_zero : H0 = 0 := by simp [H0, hℓ0]
    have hd_lin2_eq : d_lin2 = H0 + 5 / 2 := by simp [d_lin2, corr, hℓ0]
    rw [hd_lin2_eq]
    have h_id : 24 * (ρ + 1) * score2 (H0 + 5 / 2) =
        24 * (ρ + 1) * C_u * (u - 25 / 12) + 24 * (ρ + 1) * C_v * (v - 25 / 12) +
        (1352472 + 2476354 * W + 1858592 * W ^ 2 + 733960 * W ^ 3 + 161184 * W ^ 4 + 18696 * W ^ 5 + 896 * W ^ 6) +
        (38610 + 49476 * W + 22928 * W ^ 2 + 4616 * W ^ 3 + 344 * W ^ 4) * X +
        (63162 + 67518 * W + 27392 * W ^ 2 + 4988 * W ^ 3 + 344 * W ^ 4) * Y +
        (1980 + 960 * W + 120 * W ^ 2) * X * Y := by
      dsimp [score2, dN_avoid, C_u, C_v, L, X, Y, ρ, W]
      rw [hH0_zero, hz_eq]
      ring
    have hCu_pos : 0 ≤ C_u := by
      have : C_u = ((5 + 2 * W) * (4 + W) + 1) * (2 * (4 + W) ^ 2 + Y) + 3 * (7 + 2 * W) + (2 * (4 + W) ^ 2 - 1) := by
        dsimp [C_u, L, Y, ρ, W]
        rw [hH0_zero, hz_eq]
        ring
      rw [this]
      have : 0 ≤ 2 * (4 + W) ^ 2 - 1 := by nlinarith
      positivity
    have hCv_pos : 0 ≤ C_v := by
      have : C_v = ((1 + W) * (8 + 2 * W) + 1) * (2 * (4 + W) ^ 2 + X) + 3 * (3 + W) + (2 * (4 + W) ^ 2 - 1) := by
        dsimp [C_v, L, X, ρ, W]
        rw [hH0_zero, hz_eq]
        ring
      rw [this]
      have : 0 ≤ 2 * (4 + W) ^ 2 - 1 := by nlinarith
      positivity
    have hu' : 0 ≤ u - 25 / 12 := by linarith
    have hv' : 0 ≤ v - 25 / 12 := by linarith
    rw [h_id]
    positivity
  · 
    have hℓ1 : 1 ≤ ℓ := by omega
    have h_clear : 24 * (ρ + 1) * score2 d_lin2 =
        24 * (ρ + 1) * score2 (H0 + 5 / 2) - 36 * (H0 - 1) * (dN_root_neg - dN_avoid) := by
      dsimp [d_lin2]
      rw [h_score2_d]
      dsimp [corr]
      rw [if_neg hℓ0]
      have h_div : 24 * (ρ + 1) * (3 * (H0 - 1) / (2 * (ρ + 1))) = 36 * (H0 - 1) := by
        rw [mul_div_assoc', div_eq_iff (by linarith : 2 * (ρ + 1) ≠ 0)]
        ring
      linear_combination -(dN_root_neg - dN_avoid) * h_div
    rw [h_clear]
    rcases (by omega : ℓ + 3 ≤ 2 ^ g ∨ 2 ^ g ≤ ℓ + 2) with hℓ_small | hℓ_large
    · 
      set H : ℚ := H0 - 1
      have hH : 0 ≤ H := by
        have : (1 : ℚ) ≤ (ℓ : ℚ) := by exact_mod_cast hℓ1
        linarith
      have hKJ : 0 ≤ J - H0 - 3 := by
        have : (ℓ : ℚ) + 3 ≤ (2 : ℚ) ^ g := by exact_mod_cast hℓ_small
        linarith
      have hKL : 0 ≤ L - H0 - 3 := by
        dsimp [L]
        linarith
      have hy_pos : 0 ≤ (y : ℚ) := Nat.cast_nonneg y
      have hx_pos : 0 ≤ (x : ℚ) := Nat.cast_nonneg x
      have hz1 : 0 ≤ z - 1 := by linarith
      have hJ1 : 0 ≤ J - 1 := by linarith
      have hL1 : 0 ≤ L - 1 := by dsimp [L]; linarith
      have hCu_pos : 0 ≤ C_u := by
        dsimp [C_u]
        positivity
      have hCv_pos : 0 ≤ C_v := by
        dsimp [C_v]
        positivity
      have hu' : 0 ≤ u - 25 / 12 := by linarith
      have hv' : 0 ≤ v - 25 / 12 := by linarith
      have h_id : 24 * (ρ + 1) * score2 (H0 + 5 / 2) - 36 * (H0 - 1) * (dN_root_neg - dN_avoid) =
          24 * (ρ + 1) * C_u * (u - 25 / 12) + 24 * (ρ + 1) * C_v * (v - 25 / 12) +
          (3302080 + 2366644 * H + 530436 * H ^ 2 + 38568 * H ^ 3 + 1140 * H ^ 4 + 12 * H ^ 5 +
           (5458752 + 3558736 * H + 694232 * H ^ 2 + 35490 * H ^ 3 + 540 * H ^ 4) * W +
           (3787296 + 2270672 * H + 388864 * H ^ 2 + 12840 * H ^ 3 + 72 * H ^ 4) * W ^ 2 +
           (1408864 + 786168 * H + 119688 * H ^ 2 + 2160 * H ^ 3) * W ^ 3 +
           (296064 + 155808 * H + 21504 * H ^ 2 + 144 * H ^ 3) * W ^ 4 +
           (33312 + 16776 * H + 2160 * H ^ 2) * W ^ 5 +
           (1568 + 768 * H + 96 * H ^ 2) * W ^ 6) +
          (106556 + 80890 * H + 15224 * H ^ 2 + 780 * H ^ 3 + 12 * H ^ 4 +
           (119232 + 81464 * H + 13004 * H ^ 2 + 360 * H ^ 3) * W +
           (50340 + 31660 * H + 4440 * H ^ 2 + 48 * H ^ 3) * W ^ 2 +
           (9504 + 5608 * H + 720 * H ^ 2) * W ^ 3 +
           (680 + 384 * H + 48 * H ^ 2) * W ^ 4) * X +
          (146812 + 98090 * H + 17200 * H ^ 2 + 828 * H ^ 3 + 12 * H ^ 4 +
           (148240 + 93572 * H + 14266 * H ^ 2 + 372 * H ^ 3) * W +
           (57444 + 34588 * H + 4728 * H ^ 2 + 48 * H ^ 3) * W ^ 2 +
           (10096 + 5852 * H + 744 * H ^ 2) * W ^ 3 +
           (680 + 384 * H + 48 * H ^ 2) * W ^ 4) * Y +
          (4896 + 3336 * H + 468 * H ^ 2 + 12 * H ^ 3 +
           (2304 + 1536 * H + 192 * H ^ 2) * W +
           (288 + 192 * H + 24 * H ^ 2) * W ^ 2) * X * Y := by
        dsimp [score2, dN_root_neg, dN_avoid, C_u, C_v, L, X, Y, ρ, H, W]
        rw [hz_eq]
        ring
      rw [h_id]
      positivity
    · 
      set H3 : ℚ := H0 - (J - 2)
      have hH3 : 0 ≤ H3 := by
        have : (2 : ℚ) ^ g ≤ (ℓ : ℚ) + 2 := by exact_mod_cast hℓ_large
        linarith
      have hCv_neg_pos : 0 ≤ -C_v := by
        have h_cv : -C_v = 130 + 245 * H3 + 8 * H3 ^ 2 +
            (100 + 189 * H3 + 2 * H3 ^ 2) * W +
            (25 + 48 * H3) * W ^ 2 +
            (2 + 4 * H3) * W ^ 3 +
            (7 + 8 * H3 + (2 + 2 * H3) * W) * X := by
          dsimp [C_v, L, X, ρ, H3, W]
          rw [hz_eq]
          ring
        rw [h_cv]
        positivity
      rcases le_total 0 C_u with hCu | hCu
      · 
        have h_id : 24 * (ρ + 1) * score2 (H0 + 5 / 2) - 36 * (H0 - 1) * (dN_root_neg - dN_avoid) =
            24 * (ρ + 1) * C_u * (u - 25 / 12) + 24 * (ρ + 1) * (-C_v) * ((y : ℚ) / 2 - v) +
            (4609980 + 376850 * H3 + 360690 * H3 ^ 2 + 34084 * H3 ^ 3 + 1104 * H3 ^ 4 + 12 * H3 ^ 5 +
             (10323210 + 622650 * H3 + 554616 * H3 ^ 2 + 35362 * H3 ^ 3 + 576 * H3 ^ 4) * W +
             (9879704 + 426312 * H3 + 354806 * H3 ^ 2 + 13632 * H3 ^ 3 + 72 * H3 ^ 4) * W ^ 2 +
             (5287088 + 154426 * H3 + 120544 * H3 ^ 2 + 2304 * H3 ^ 3) * W ^ 3 +
             (1732318 + 31132 * H3 + 22896 * H3 ^ 2 + 144 * H3 ^ 3) * W ^ 4 +
             (356096 + 3304 * H3 + 2304 * H3 ^ 2) * W ^ 5 +
             (44864 + 144 * H3 + 96 * H3 ^ 2) * W ^ 6 +
             3168 * W ^ 7 + 96 * W ^ 8) +
            (115752 + 8040 * H3 + 11328 * H3 ^ 2 + 732 * H3 ^ 3 + 12 * H3 ^ 4 +
             (210144 + 8544 * H3 + 11724 * H3 ^ 2 + 384 * H3 ^ 3) * W +
             (151056 + 3540 * H3 + 4536 * H3 ^ 2 + 48 * H3 ^ 3) * W ^ 2 +
             (55668 + 672 * H3 + 768 * H3 ^ 2) * W ^ 3 +
             (11148 + 48 * H3 + 48 * H3 ^ 2) * W ^ 4 +
             1152 * W ^ 5 + 48 * W ^ 6) * X +
            (208342 + 30562 * H3 + 13456 * H3 ^ 2 + 780 * H3 ^ 3 + 12 * H3 ^ 4 +
             (322952 + 32172 * H3 + 13270 * H3 ^ 2 + 396 * H3 ^ 3) * W +
             (205764 + 12684 * H3 + 4884 * H3 ^ 2 + 48 * H3 ^ 3) * W ^ 2 +
             (68798 + 2216 * H3 + 792 * H3 ^ 2) * W ^ 3 +
             (12700 + 144 * H3 + 48 * H3 ^ 2) * W ^ 4 +
             1224 * W ^ 5 + 48 * W ^ 6) * Y +
            (5772 + 864 * H3 + 408 * H3 ^ 2 + 12 * H3 ^ 3 +
             (6072 + 432 * H3 + 204 * H3 ^ 2) * W +
             (2352 + 60 * H3 + 24 * H3 ^ 2) * W ^ 2 +
             396 * W ^ 3 + 24 * W ^ 4) * X * Y := by
          dsimp [score2, dN_root_neg, dN_avoid, C_u, C_v, L, X, Y, ρ, H3, W]
          rw [hz_eq]
          ring
        have hu' : 0 ≤ u - 25 / 12 := by linarith
        have hvy : 0 ≤ (y : ℚ) / 2 - v := by linarith
        rw [h_id]
        positivity
      · 
        set H4 : ℚ := H0 - (2 * J - 2)
        have hH4 : 0 ≤ H4 := by
          rcases (by omega : ℓ + 3 ≤ 2 * 2 ^ g ∨ 2 * 2 ^ g ≤ ℓ + 2) with hℓ_mid | hℓ_vlarge
          · have hL_sub : 0 ≤ L - H0 - 3 := by
              have : (ℓ : ℚ) + 3 ≤ 2 * (2 : ℚ) ^ g := by exact_mod_cast hℓ_mid
              dsimp [L, H0, J]
              linarith
            have hy_pos : 0 ≤ (y : ℚ) := Nat.cast_nonneg y
            have hL1 : 0 < L - 1 := by dsimp [L]; linarith
            have hz1 : 0 ≤ z - 1 := by linarith
            have hH0_3 : 0 < H0 + 3 := by linarith
            have hCu_strict : 0 < C_u := by
              dsimp [C_u]
              positivity
            linarith
          · have : 2 * (2 : ℚ) ^ g ≤ (ℓ : ℚ) + 2 := by exact_mod_cast hℓ_vlarge
            dsimp [H4, H0, J]
            linarith
        have h_id : 24 * (ρ + 1) * score2 (H0 + 5 / 2) - 36 * (H0 - 1) * (dN_root_neg - dN_avoid) =
            24 * (ρ + 1) * (-C_u) * ((x : ℚ) / 2 - u) + 24 * (ρ + 1) * (-C_v) * ((y : ℚ) / 2 - v) +
            (16993152 + 3488892 * H4 + 719760 * H4 ^ 2 + 48768 * H4 ^ 3 + 1296 * H4 ^ 4 + 12 * H4 ^ 5 +
             (33711264 + 5529276 * H4 + 986040 * H4 ^ 2 + 46236 * H4 ^ 3 + 624 * H4 ^ 4) * W +
             (29081208 + 3744480 * H4 + 562368 * H4 ^ 2 + 16296 * H4 ^ 3 + 72 * H4 ^ 4) * W ^ 2 +
             (14233032 + 1403064 * H4 + 170472 * H4 ^ 2 + 2520 * H4 ^ 3) * W ^ 3 +
             (4317456 + 313728 * H4 + 28896 * H4 ^ 2 + 144 * H4 ^ 3) * W ^ 4 +
             (830160 + 41808 * H4 + 2592 * H4 ^ 2) * W ^ 5 +
             (98688 + 3072 * H4 + 96 * H4 ^ 2) * W ^ 6 +
             (6624 + 96 * H4) * W ^ 7 + 192 * W ^ 8) +
            (456768 + 84108 * H4 + 17988 * H4 ^ 2 + 876 * H4 ^ 3 + 12 * H4 ^ 4 +
             (682560 + 95868 * H4 + 16656 * H4 ^ 2 + 420 * H4 ^ 3) * W +
             (423672 + 43752 * H4 + 5736 * H4 ^ 2 + 48 * H4 ^ 3) * W ^ 2 +
             (139320 + 9912 * H4 + 864 * H4 ^ 2) * W ^ 3 +
             (25488 + 1104 * H4 + 48 * H4 ^ 2) * W ^ 4 +
             (2448 + 48 * H4) * W ^ 5 + 96 * W ^ 6) * X +
            (551376 + 112764 * H4 + 20436 * H4 ^ 2 + 924 * H4 ^ 3 + 12 * H4 ^ 4 +
             (804996 + 124344 * H4 + 18324 * H4 ^ 2 + 432 * H4 ^ 3) * W +
             (486384 + 54168 * H4 + 6096 * H4 ^ 2 + 48 * H4 ^ 3) * W ^ 2 +
             (155160 + 11568 * H4 + 888 * H4 ^ 2) * W ^ 3 +
             (27456 + 1200 * H4 + 48 * H4 ^ 2) * W ^ 4 +
             (2544 + 48 * H4) * W ^ 5 + 96 * W ^ 6) * Y +
            (15120 + 2796 * H4 + 504 * H4 ^ 2 + 12 * H4 ^ 3 +
             (14652 + 1824 * H4 + 228 * H4 ^ 2) * W +
             (5304 + 384 * H4 + 24 * H4 ^ 2) * W ^ 2 +
             (840 + 24 * H4) * W ^ 3 + 48 * W ^ 4) * X * Y := by
          dsimp [score2, dN_root_neg, dN_avoid, C_u, C_v, L, X, Y, ρ, H4, W]
          rw [hz_eq]
          ring
        have hux : 0 ≤ (x : ℚ) / 2 - u := by linarith
        have hvy : 0 ≤ (y : ℚ) / 2 - v := by linarith
        have hCu' : 0 ≤ -C_u := by linarith
        rw [h_id]
        positivity

theorem broom_insertion_score_positivity : ∀ (ℓ k p x y : ℕ) (c u v d : ℚ),
    ((1 ≤ ℓ ∧ 2 ≤ k) ∨ (ℓ = 0 ∧ 3 ≤ k)) →
    1 ≤ p →
    0 ≤ c → c ≤ (p : ℚ) - 1 →
    ℓ + 2 ^ k ≤ x → ℓ + 2 ^ k ≤ y →
    (25 : ℚ) / 12 ≤ u → u ≤ (x : ℚ) / 2 →
    (25 : ℚ) / 12 ≤ v → v ≤ (y : ℚ) / 2 →
    broomThreshold ℓ k ≤ d →
    0 < broomInsertionScore p x y ℓ k c u v d + broomInsertionScore p y x ℓ k c v u d :=
by
  intro ℓ k p x y c u v d hlk hp hc0 hcp hx hy hu1 hu2 hv1 hv2 hd
  have hmono1 := broom_score_host_and_d_mono ℓ k p x y c u v d hlk hp hc0 hcp hx hy hu1 hu2 hv1 hv2 hd
  have hmono2 := broom_score_host_and_d_mono ℓ k p y x c v u d hlk hp hc0 hcp hy hx hv1 hv2 hu1 hu2 hd
  have hp_pos : (0 : ℚ) < (p : ℚ) := by
    have : (1 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
    linarith
  have h_base_pos : 0 < broomInsertionScore 1 x y ℓ k 0 u v (broomThreshold ℓ k) +
      broomInsertionScore 1 y x ℓ k 0 v u (broomThreshold ℓ k) := by
    rcases (by omega : ((1 ≤ ℓ ∧ k = 2) ∨ k = 3) ∨ 4 ≤ k) with h_small | hk4
    · exact broom_base_score_pos_small_k ℓ k x y u v h_small hx hy hu1 hu2 hv1 hv2
    · set g : ℕ := k / 2
      have hg2 : 2 ≤ g := by omega
      rcases (by omega : k = 2 * g ∨ k = 2 * g + 1) with hk_even | hk_odd
      · rw [hk_even] at hx hy ⊢
        have h1 := broom_base_score_pos_even_k_ge_four ℓ g x y u v hg2 hx hy hu1 hu2 hv1 hv2
        have h2 := broom_base_score_pos_even_k_ge_four ℓ g y x v u hg2 hy hx hv1 hv2 hu1 hu2
        linarith
      · rw [hk_odd] at hx hy ⊢
        have h1 := broom_base_score_pos_odd_k_ge_five ℓ g x y u v hg2 hx hy hu1 hu2 hv1 hv2
        have h2 := broom_base_score_pos_odd_k_ge_five ℓ g y x v u hg2 hy hx hv1 hv2 hu1 hu2
        linarith
  nlinarith

theorem broom_straightening_improves : ∀ (n : ℕ) (hn : 1 ≤ n) (T : SimpleGraph (Fin n)),
    T.IsTree → HasCountDominatedBroom T →
    ∃ T' : SimpleGraph (Fin n), T'.IsTree ∧ meanSubtreeOrder T < meanSubtreeOrder T' :=
by
  intro n hn T hT hBroom
  rcases hBroom with ⟨ℓ, k, A, B, C, L_k, w, r_B, r_C, v, h_lk, hv,
    hSubA, hSubB, hSubC, hcard, hDisjAB, hDisjAC, hDisjBC,
    hDisjABC_v, hDisjABC_L, hDisj_v_L, hUniv,
    hBridgeAB, hBridgeABC, hBridgeAll, hSpine, hLeaf, hx_lb, hy_lb⟩
  rcases broom_shortening_or_threshold n hn T hT ℓ k A B C L_k w r_B r_C v
    h_lk hv hSubA hSubB hSubC hcard hDisjAB hDisjAC hDisjBC
    hDisjABC_v hDisjABC_L hDisj_v_L hUniv hBridgeAB hBridgeABC hBridgeAll
    hSpine hLeaf hx_lb hy_lb with hShort | hd
  · exact hShort
  · have hw : w ∈ A := hBridgeAB.2.1
    have hr_B : r_B ∈ B := hBridgeAB.2.2.1
    have hr_C : r_C ∈ C := hBridgeABC.2.2.1
    obtain ⟨hp1, hptA, htA_ub, _⟩ := broom_rooted_moment_bounds n T A w hT hSubA hw
    obtain ⟨_, _, htB_ub, htB_lb_imp⟩ := broom_rooted_moment_bounds n T B r_B hT hSubB hr_B
    obtain ⟨_, _, htC_ub, htC_lb_imp⟩ := broom_rooted_moment_bounds n T C r_C hT hSubC hr_C
    have h_rho5 : 5 ≤ ℓ + 2 ^ k := by
      rcases h_lk with ⟨hℓ, hk⟩ | ⟨hℓ, hk⟩
      · have hk2 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
        omega
      · have hk3 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
        omega
    have hx5 : 5 ≤ rootedCount T B r_B := le_trans h_rho5 hx_lb
    have hy5 : 5 ≤ rootedCount T C r_C := le_trans h_rho5 hy_lb
    have htB_lb : 5 * rootedCount T B r_B ≤ 2 * rootedOrderSum T B r_B := htB_lb_imp hx5
    have htC_lb : 5 * rootedCount T C r_C ≤ 2 * rootedOrderSum T C r_C := htC_lb_imp hy5
    have hp1_q : (1 : ℚ) ≤ (rootedCount T A w : ℚ) := by exact_mod_cast hp1
    have hp_pos : (0 : ℚ) < (rootedCount T A w : ℚ) := by linarith
    have hptA_q : (rootedCount T A w : ℚ) ≤ (rootedOrderSum T A w : ℚ) := by exact_mod_cast hptA
    have htA_ub_q : 2 * (rootedOrderSum T A w : ℚ) ≤
        (rootedCount T A w : ℚ) * ((rootedCount T A w : ℚ) + 1) := by exact_mod_cast htA_ub
    have hc_lb : 0 ≤ 2 * ((rootedOrderSum T A w : ℚ) / (rootedCount T A w : ℚ) - 1) := by
      have h1 : (1 : ℚ) ≤ (rootedOrderSum T A w : ℚ) / (rootedCount T A w : ℚ) := by
        rw [le_div_iff₀ hp_pos]
        linarith
      linarith
    have hc_ub : 2 * ((rootedOrderSum T A w : ℚ) / (rootedCount T A w : ℚ) - 1) ≤
        (rootedCount T A w : ℚ) - 1 := by
      have h2 : (rootedOrderSum T A w : ℚ) / (rootedCount T A w : ℚ) ≤
          ((rootedCount T A w : ℚ) + 1) / 2 := by
        rw [div_le_iff₀ hp_pos]
        linarith
      linarith
    have hx5_q : (5 : ℚ) ≤ (rootedCount T B r_B : ℚ) := by exact_mod_cast hx5
    have hx1_pos : (0 : ℚ) < (rootedCount T B r_B : ℚ) + 1 := by linarith
    have htB_ub_q : 2 * (rootedOrderSum T B r_B : ℚ) ≤
        (rootedCount T B r_B : ℚ) * ((rootedCount T B r_B : ℚ) + 1) := by exact_mod_cast htB_ub
    have htB_lb_q : 5 * (rootedCount T B r_B : ℚ) ≤ 2 * (rootedOrderSum T B r_B : ℚ) := by
      exact_mod_cast htB_lb
    have hu_lb : (25 : ℚ) / 12 ≤
        (rootedOrderSum T B r_B : ℚ) / ((rootedCount T B r_B : ℚ) + 1) := by
      rw [le_div_iff₀ hx1_pos]
      linarith
    have hu_ub : (rootedOrderSum T B r_B : ℚ) / ((rootedCount T B r_B : ℚ) + 1) ≤
        (rootedCount T B r_B : ℚ) / 2 := by
      rw [div_le_iff₀ hx1_pos]
      linarith
    have hy5_q : (5 : ℚ) ≤ (rootedCount T C r_C : ℚ) := by exact_mod_cast hy5
    have hy1_pos : (0 : ℚ) < (rootedCount T C r_C : ℚ) + 1 := by linarith
    have htC_ub_q : 2 * (rootedOrderSum T C r_C : ℚ) ≤
        (rootedCount T C r_C : ℚ) * ((rootedCount T C r_C : ℚ) + 1) := by exact_mod_cast htC_ub
    have htC_lb_q : 5 * (rootedCount T C r_C : ℚ) ≤ 2 * (rootedOrderSum T C r_C : ℚ) := by
      exact_mod_cast htC_lb
    have hv_lb : (25 : ℚ) / 12 ≤
        (rootedOrderSum T C r_C : ℚ) / ((rootedCount T C r_C : ℚ) + 1) := by
      rw [le_div_iff₀ hy1_pos]
      linarith
    have hv_ub : (rootedOrderSum T C r_C : ℚ) / ((rootedCount T C r_C : ℚ) + 1) ≤
        (rootedCount T C r_C : ℚ) / 2 := by
      rw [div_le_iff₀ hy1_pos]
      linarith
    obtain ⟨T₁, T₂, hT₁, hT₂, hN₁, hN₂, hScore₁, hScore₂⟩ :=
      broom_balanced_insertion_candidates n hn T hT ℓ k A B C L_k w r_B r_C v
        h_lk hv hSubA hSubB hSubC hcard hDisjAB hDisjAC hDisjBC
        hDisjABC_v hDisjABC_L hDisj_v_L hUniv hBridgeAB hBridgeABC hBridgeAll
        hSpine hLeaf
    have hPos := broom_insertion_score_positivity ℓ k
      (rootedCount T A w) (rootedCount T B r_B) (rootedCount T C r_C)
      (2 * ((rootedOrderSum T A w : ℚ) / (rootedCount T A w : ℚ) - 1))
      ((rootedOrderSum T B r_B : ℚ) / ((rootedCount T B r_B : ℚ) + 1))
      ((rootedOrderSum T C r_C : ℚ) / ((rootedCount T C r_C : ℚ) + 1))
      (meanSubtreeOrder T -
        ((rootedOrderSum T A w : ℚ) / (rootedCount T A w : ℚ) +
         (rootedOrderSum T B r_B : ℚ) / ((rootedCount T B r_B : ℚ) + 1) +
         (rootedOrderSum T C r_C : ℚ) / ((rootedCount T C r_C : ℚ) + 1)))
      h_lk hp1 hc_lb hc_ub hx_lb hy_lb hu_lb hu_ub hv_lb hv_ub hd
    rw [← hScore₁, ← hScore₂] at hPos
    have hOr : meanSubtreeOrder T * (subtreeCount T₁ : ℚ) < (subtreeOrderSum T₁ : ℚ) ∨
        meanSubtreeOrder T * (subtreeCount T₂ : ℚ) < (subtreeOrderSum T₂ : ℚ) := by
      by_contra h
      push_neg at h
      linarith
    rcases hOr with h1 | h2
    · refine ⟨T₁, hT₁, ?_⟩
      change meanSubtreeOrder T < (subtreeOrderSum T₁ : ℚ) / (subtreeCount T₁ : ℚ)
      exact (lt_div_iff₀ hN₁).mpr h1
    · refine ⟨T₂, hT₂, ?_⟩
      change meanSubtreeOrder T < (subtreeOrderSum T₂ : ℚ) / (subtreeCount T₂ : ℚ)
      exact (lt_div_iff₀ hN₂).mpr h2

theorem jamison_every_maximizer_is_caterpillar (n : ℕ) (hn : 1 ≤ n)
    (T : SimpleGraph (Fin n)) (hT : T.IsTree)
    (hmax : ∀ T' : SimpleGraph (Fin n), T'.IsTree →
      meanSubtreeOrder T' ≤ meanSubtreeOrder T) :
    IsCaterpillar T :=
by
  by_contra h_not_cat
  rcases non_caterpillar_decomposition n hn T hT h_not_cat with h1 | h2 | h3 | h4
  · obtain ⟨T', hT', hlt⟩ := leaf_deg_two_improves n hn T hT h1
    have hle := hmax T' hT'
    linarith
  · obtain ⟨T', hT', hlt⟩ := packet_concentration_improves n hn T hT h2
    have hle := hmax T' hT'
    linarith
  · obtain ⟨T', hT', hlt⟩ := cherry_branch_improves n hn T hT h3
    have hle := hmax T' hT'
    linarith
  · obtain ⟨T', hT', hlt⟩ := broom_straightening_improves n hn T hT h4
    have hle := hmax T' hT'
    linarith
