import Mathlib
import Hilbert10Defs
set_option maxHeartbeats 4000000

/-! ### Statement (originally `mordell_weil.lean`) -/

/--
**Mordell–Weil theorem.** Let `K` be a number field and `E/K` an elliptic curve.
Then the group `E(K)` of `K`-rational points is a finitely generated abelian group.
-/
noncomputable def fieldLogHeight {K : Type u} [Field K] [NumberField K] (x : K) : ℝ :=
  Real.log ((∏ w : NumberField.InfinitePlace K, max (w x) 1 ^ w.mult) *
    (∏ᶠ v : NumberField.FinitePlace K, max (v x) 1))

noncomputable def weierstrassHeight {K : Type u} [Field K] [NumberField K]
    (E : WeierstrassCurve K) (P : E.toAffine.Point) : ℝ :=
  match P with
  | .zero => 0
  | @WeierstrassCurve.Affine.Point.some _ _ _ x _ _ => fieldLogHeight x
noncomputable def twoTorsionPoly {K : Type u} [Field K] (E : WeierstrassCurve K) : Polynomial K :=
  Polynomial.X ^ 3 + Polynomial.C (E.b₂ / 4) * Polynomial.X ^ 2 +
    Polynomial.C (E.b₄ / 2) * Polynomial.X + Polynomial.C (E.b₆ / 4)

noncomputable def pointKummer {F : Type u} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) (e₁ e₂ : F) (P : W.toAffine.Point) : SqCl F × SqCl F :=
  match P with
  | .zero => (1, 1)
  | @WeierstrassCurve.Affine.Point.some _ _ _ x _ _ =>
    if h : x - e₁ ≠ 0 ∧ x - e₂ ≠ 0 then
      (sqCl (Units.mk0 (x - e₁) h.1), sqCl (Units.mk0 (x - e₂) h.2))
    else
      (1, 1)
def phi2 {K : Type u} [CommRing K] (E : WeierstrassCurve K) (x : K) : K :=
  x ^ 4 - E.b₄ * x ^ 2 - 2 * E.b₆ * x - E.b₈

def psi2Sq {K : Type u} [CommRing K] (E : WeierstrassCurve K) (x : K) : K :=
  4 * x ^ 3 + E.b₂ * x ^ 2 + 2 * E.b₄ * x + E.b₆

def deg3Eval {K : Type u} [CommRing K] (c3 c2 c1 c0 x : K) : K :=
  c3 * x ^ 3 + c2 * x ^ 2 + c1 * x + c0

def deg3Bound {K : Type u} (u : K → ℝ) (c3 c2 c1 c0 : K) : ℝ :=
  max (u c3) 1 * max (u c2) 1 * max (u c1) 1 * max (u c0) 1

def u7c3 {K : Type u} [CommRing K] (E : WeierstrassCurve K) : K :=
  32 * E.b₄ * E.b₈ + E.b₂ * E.b₄ * E.b₆ - E.b₂ ^ 2 * E.b₈ - 27 * E.b₆ ^ 2

def u7c2 {K : Type u} [CommRing K] (E : WeierstrassCurve K) : K :=
  4 * E.b₆ * E.b₈ + 2 * E.b₄ ^ 2 * E.b₆ + 4 * E.b₂ * E.b₄ * E.b₈ - 6 * E.b₂ * E.b₆ ^ 2

def u7c1 {K : Type u} [CommRing K] (E : WeierstrassCurve K) : K :=
  12 * E.b₄ ^ 2 * E.b₈ - 11 * E.b₄ * E.b₆ ^ 2 - E.b₂ * E.b₆ * E.b₈

def u7c0 {K : Type u} [CommRing K] (E : WeierstrassCurve K) : K :=
  6 * E.b₄ * E.b₆ * E.b₈ - 6 * E.b₆ ^ 3

def v7c3 {K : Type u} [CommRing K] (E : WeierstrassCurve K) : K :=
  5 * E.b₆ * E.b₈ + E.b₄ ^ 2 * E.b₆ - E.b₂ * E.b₄ * E.b₈

def v7c2 {K : Type u} [CommRing K] (E : WeierstrassCurve K) : K :=
  4 * E.b₈ ^ 2 + 6 * E.b₄ ^ 2 * E.b₈ - 4 * E.b₄ * E.b₆ ^ 2 - 2 * E.b₂ * E.b₆ * E.b₈

def v7c1 {K : Type u} [CommRing K] (E : WeierstrassCurve K) : K :=
  13 * E.b₄ * E.b₆ * E.b₈ - E.b₂ * E.b₈ ^ 2 - 12 * E.b₆ ^ 3

def v7c0 {K : Type u} [CommRing K] (E : WeierstrassCurve K) : K :=
  6 * E.b₄ * E.b₈ ^ 2 - 6 * E.b₆ ^ 2 * E.b₈

def doublePlaceBound {K : Type u} [Field K] (E : WeierstrassCurve K) (u : K → ℝ) : ℝ :=
  max (u E.Δ⁻¹) 1 *
    deg3Bound u 0 (-48) (-8 * E.b₂) (E.b₂ ^ 2 - 32 * E.b₄) *
    deg3Bound u 12 (-E.b₂) (-10 * E.b₄) (E.b₂ * E.b₄ - 27 * E.b₆) *
    deg3Bound u (u7c3 E) (u7c2 E) (u7c1 E) (u7c0 E) *
    deg3Bound u (v7c3 E) (v7c2 E) (v7c1 E) (v7c0 E)
def chordNum {K : Type u} [CommRing K] (E : WeierstrassCurve K) (x₀ y₀ x y : K) : K :=
  x₀ * x ^ 2 + (E.a₄ + x₀ ^ 2 + 2 * E.a₂ * x₀ - E.a₁ * y₀) * x -
    (2 * y₀ + E.a₁ * x₀ + E.a₃) * y +
    (E.a₆ + y₀ ^ 2 + E.a₁ * x₀ * y₀ - x₀ ^ 3 - E.a₂ * x₀ ^ 2)

def chordDen {K : Type u} [CommRing K] (x₀ x : K) : K :=
  (x - x₀) ^ 2

def curvePlaceConst {K : Type u} [CommRing K] (E : WeierstrassCurve K) (x₀ y₀ : K) (f : K → ℝ) : ℝ :=
  max 1 (max (f E.a₁) (max (f E.a₂) (max (f E.a₃) (max (f E.a₄) (max (f E.a₆)
    (max (f x₀) (max (f (E.a₄ + x₀ ^ 2 + 2 * E.a₂ * x₀ - E.a₁ * y₀))
      (max (f (2 * y₀ + E.a₁ * x₀ + E.a₃))
        (f (E.a₆ + y₀ ^ 2 + E.a₁ * x₀ * y₀ - x₀ ^ 3 - E.a₂ * x₀ ^ 2))))))))))

theorem abstract_descent_fg {A : Type u} [AddCommGroup A] (h : A → ℝ)
    (h_add : ∀ Q : A, ∃ C₁ : ℝ, ∀ P : A, h (P + Q) ≤ 2 * h P + C₁)
    (h_dbl : ∃ C₂ : ℝ, ∀ P : A, 4 * h P ≤ h (P + P) + C₂)
    (h_fin : ∀ C₃ : ℝ, {P : A | h P ≤ C₃}.Finite)
    (h_weak : ∃ Q₀ : Set A, Q₀.Finite ∧ ∀ P : A, ∃ q ∈ Q₀, ∃ P' : A, P = P' + P' + q) :
    AddGroup.FG A :=
by
  classical
  obtain ⟨C₂, hC₂⟩ := h_dbl
  obtain ⟨Q₀, hQ₀_fin, hQ₀_surj⟩ := h_weak
  choose c₁ hc₁ using fun q : A => h_add (-q)
  let F₀ : Finset A := hQ₀_fin.toFinset
  let C₁_star : ℝ := ∑ q ∈ F₀, |c₁ q|
  have hC₁_nonneg : 0 ≤ C₁_star := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have h_unif : ∀ q ∈ Q₀, ∀ P : A, h (P - q) ≤ 2 * h P + C₁_star := by
    intro q hq P
    have hqF : q ∈ F₀ := hQ₀_fin.mem_toFinset.mpr hq
    have h_le_sum : |c₁ q| ≤ C₁_star :=
      Finset.single_le_sum (f := fun x => |c₁ x|) (fun _ _ => abs_nonneg _) hqF
    have h1 := hc₁ q P
    rw [← sub_eq_add_neg] at h1
    linarith [le_abs_self (c₁ q)]
  let C : ℝ := (C₁_star + |C₂|) / 4
  let B : ℝ := 2 * C + 1
  let S : Set A := Q₀ ∪ {X : A | h X ≤ B}
  have hS_fin : S.Finite := hQ₀_fin.union (h_fin B)
  have h_step : ∀ P : A, ∃ q ∈ Q₀, ∃ P' : A, P = P' + P' + q ∧ 2 * h P' ≤ h P + 2 * C := by
    intro P
    obtain ⟨q, hq, P', hP'⟩ := hQ₀_surj P
    refine ⟨q, hq, P', hP', ?_⟩
    have h_eq : P' + P' = P - q := eq_sub_of_add_eq hP'.symm
    have h_d := hC₂ P'
    rw [h_eq] at h_d
    have h_u := h_unif q hq P
    have h_abs : C₂ ≤ |C₂| := le_abs_self C₂
    change 2 * h P' ≤ h P + 2 * ((C₁_star + |C₂|) / 4)
    linarith
  have h_ind : ∀ n : ℕ, ∀ P : A, 2 * (h P - B) ≤ (n : ℝ) → P ∈ AddSubgroup.closure S := by
    intro n
    induction n with
    | zero =>
      intro P hP
      have hPB : h P ≤ B := by linarith [Nat.cast_zero (R := ℝ)]
      exact AddSubgroup.subset_closure (Or.inr hPB)
    | succ n ih =>
      intro P hP
      by_cases hPB : h P ≤ B
      · exact AddSubgroup.subset_closure (Or.inr hPB)
      · push_neg at hPB
        obtain ⟨q, hq, P', rfl, hP'_bound⟩ := h_step P
        have hP'_ind : 2 * (h P' - B) ≤ (n : ℝ) := by
          push_cast at hP
          change 2 * (h P' - (2 * C + 1)) ≤ (n : ℝ)
          change 2 * C + 1 < h (P' + P' + q) at hPB
          linarith
        have hP'_mem : P' ∈ AddSubgroup.closure S := ih P' hP'_ind
        have hq_mem : q ∈ AddSubgroup.closure S := AddSubgroup.subset_closure (Or.inl hq)
        exact AddSubgroup.add_mem _ (AddSubgroup.add_mem _ hP'_mem hP'_mem) hq_mem
  rw [AddGroup.fg_iff]
  refine ⟨S, ?_, hS_fin⟩
  rw [eq_top_iff]
  intro P _
  obtain ⟨n, hn⟩ := exists_nat_ge (2 * (h P - B))
  exact h_ind n P hn

theorem height_northcott {K : Type u} [Field K] [NumberField K] [DecidableEq K]
    (E : WeierstrassCurve K) (hE : E.IsElliptic) (C₃ : ℝ) :
    {P : E.toAffine.Point | weierstrassHeight E P ≤ C₃}.Finite :=
by
  classical
  have weierstrass_fiber_finite : ∀ x : K,
      {P : E.toAffine.Point | ∃ (y : K) (h : E.toAffine.Nonsingular x y),
        P = WeierstrassCurve.Affine.Point.some h}.Finite := by
    intro x
    by_cases hne : ({P : E.toAffine.Point | ∃ (y : K) (h : E.toAffine.Nonsingular x y),
        P = WeierstrassCurve.Affine.Point.some h}).Nonempty
    · rcases hne with ⟨_, ⟨y₀, h₀, rfl⟩⟩
      let S : Set K := {y₀, -y₀ - E.a₁ * x - E.a₃}
      have hS : S.Finite := (Set.finite_singleton _).insert _
      let f : E.toAffine.Point → K := fun P =>
        match P with
        | .zero => y₀
        | @WeierstrassCurve.Affine.Point.some _ _ _ _ y _ => y
      apply hS.of_injOn (f := f)
      · intro P hP
        rcases hP with ⟨y, h, rfl⟩
        change y ∈ S
        have eq1 := (WeierstrassCurve.Affine.equation_iff x y).mp h.1
        have eq0 := (WeierstrassCurve.Affine.equation_iff x y₀).mp h₀.1
        have hfac : (y - y₀) * (y + y₀ + E.toAffine.a₁ * x + E.toAffine.a₃) = 0 := by
          linear_combination eq1 - eq0
        rcases mul_eq_zero.mp hfac with h1 | h2
        · left; linear_combination h1
        · right; rw [Set.mem_singleton_iff]; linear_combination h2
      · intro P₁ hP₁ P₂ hP₂ hfeq
        rcases hP₁ with ⟨y₁, h₁, rfl⟩
        rcases hP₂ with ⟨y₂, h₂, rfl⟩
        change y₁ = y₂ at hfeq
        subst hfeq
        rfl
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      exact Set.finite_empty
  have fieldLogHeight_bounds : ∀ x : K, fieldLogHeight x ≤ C₃ →
      (∏ᶠ v : NumberField.FinitePlace K, max (v x) 1) ≤ Real.exp C₃ ∧
        ∀ w : NumberField.InfinitePlace K, w x ≤ Real.exp C₃ := by
    intro x hx
    unfold fieldLogHeight at hx
    set H_inf := ∏ w : NumberField.InfinitePlace K, max (w x) 1 ^ w.mult
    set H_fin := ∏ᶠ v : NumberField.FinitePlace K, max (v x) 1
    have h_inf_ge : 1 ≤ H_inf :=
      Finset.one_le_prod Finset.univ (fun w => one_le_pow₀ (le_max_right _ _))
    have h_fin_ge : 1 ≤ H_fin :=
      one_le_finprod (fun v => le_max_right _ _)
    have h_prod_pos : 0 < H_inf * H_fin := by
      have : (1 : ℝ) ≤ H_inf * H_fin := one_le_mul_of_one_le_of_one_le h_inf_ge h_fin_ge
      linarith
    rw [Real.log_le_iff_le_exp h_prod_pos] at hx
    have h_fin_le : H_fin ≤ Real.exp C₃ := by nlinarith
    have h_inf_le : H_inf ≤ Real.exp C₃ := by nlinarith
    refine ⟨h_fin_le, fun w => ?_⟩
    have hw_le_prod : max (w x) 1 ^ w.mult ≤ H_inf := by
      dsimp [H_inf]
      rw [← Finset.mul_prod_erase Finset.univ (fun w' : NumberField.InfinitePlace K => max (w' x) 1 ^ w'.mult) (Finset.mem_univ w)]
      have h_rest : 1 ≤ ∏ x_1 ∈ Finset.univ.erase w, max (x_1 x) 1 ^ x_1.mult :=
        Finset.one_le_prod (Finset.univ.erase w) (fun w' => one_le_pow₀ (le_max_right _ _))
      have h_base : 0 ≤ max (w x) 1 ^ w.mult := by positivity
      nlinarith
    have h_mult_ne : w.mult ≠ 0 := by
      have h1 : (1 : ℝ) ≤ (w.mult : ℝ) := NumberField.InfinitePlace.one_le_mult
      exact_mod_cast (by linarith : (w.mult : ℝ) ≠ 0)
    have hw_le_pow : max (w x) 1 ≤ max (w x) 1 ^ w.mult :=
      le_self_pow₀ (le_max_right (w x) 1) h_mult_ne
    have hw_le_max : w x ≤ max (w x) 1 := le_max_left _ _
    linarith
  have ringOfIntegers_bounded_infinitePlace_finite : ∀ R : ℝ,
      {y : NumberField.RingOfIntegers K |
        ∀ w : NumberField.InfinitePlace K,
          w (algebraMap (NumberField.RingOfIntegers K) K y) ≤ R}.Finite := by
    intro R
    let ι : NumberField.RingOfIntegers K → ((K →+* ℂ) → ℂ) :=
      fun y => NumberField.canonicalEmbedding K (algebraMap (NumberField.RingOfIntegers K) K y)
    have h_inj : Function.Injective ι :=
      (NumberField.canonicalEmbedding_injective K).comp NumberField.RingOfIntegers.coe_injective
    have h_fin := NumberField.canonicalEmbedding.integerLattice.inter_ball_finite K R
    apply h_fin.of_injOn (f := ι)
    · intro y hy
      refine ⟨⟨algebraMap (NumberField.RingOfIntegers K) K y, ⟨y, rfl⟩, rfl⟩, ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      have hR : 0 ≤ R := by
        obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace K) := inferInstance
        exact le_trans (apply_nonneg w _) (hy w)
      rw [pi_norm_le_iff_of_nonempty]
      intro φ
      dsimp [ι]
      exact (NumberField.InfinitePlace.le_iff_le (algebraMap (NumberField.RingOfIntegers K) K y) R).mp hy φ
    · exact h_inj.injOn
  have finitePlace_local_clear_denom : ∀ (v : NumberField.FinitePlace K) (x : K),
      ∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) = max (v x) 1 ∧ v ((n : K) * x) ≤ 1 := by
    intro v x
    let p := v.maximalIdeal
    let N : ℕ := Ideal.absNorm p.asIdeal
    have hN1 : 1 < N := NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm p
    have hN_nn : 1 < (N : NNReal) := NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm_nnreal p
    have hN_ne : (N : NNReal) ≠ 0 := NumberField.RingOfIntegers.HeightOneSpectrum.absNorm_ne_zero p
    have hv_eq : ∀ z : K, v z = ((WithZeroMulInt.toNNReal hN_ne (p.valuation K z) : NNReal) : ℝ) := by
      intro z
      rw [← NumberField.FinitePlace.norm_embedding_eq, NumberField.FinitePlace.norm_def']
    have hv_le_one : ∀ z : K, v z ≤ 1 ↔ p.valuation K z ≤ 1 := by
      intro z
      rw [hv_eq z]
      exact_mod_cast WithZeroMulInt.toNNReal_le_one_iff hN_nn
    by_cases hvx : v x ≤ 1
    · refine ⟨1, le_rfl, ?_, ?_⟩
      · rw [Nat.cast_one, max_eq_right hvx]
      · rw [Nat.cast_one, one_mul]; exact hvx
    · have hval_not_le : ¬ p.valuation K x ≤ 1 := by
        rwa [← hv_le_one x]
      have hval_ne : p.valuation K x ≠ 0 := by
        intro h0
        apply hval_not_le
        rw [h0]
        exact zero_le'
      let m : ℤ := Multiplicative.toAdd (WithZero.unzero hval_ne)
      have hval_eq : p.valuation K x = ((Multiplicative.ofAdd m : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
        simp [m, WithZero.coe_unzero]
      have hm_pos : 0 < m := by
        by_contra hle
        push_neg at hle
        apply hval_not_le
        rw [hval_eq]
        exact WithZero.coe_le_coe.mpr hle
      let k : ℕ := m.toNat
      have hk_eq : (k : ℤ) = m := Int.toNat_of_nonneg (by omega)
      refine ⟨N ^ k, Nat.one_le_pow k N (by omega), ?_, ?_⟩
      · have hvx_gt : 1 < v x := not_le.mp hvx
        rw [max_eq_left (le_of_lt hvx_gt), hv_eq x, WithZeroMulInt.toNNReal_neg_apply hN_ne hval_ne]
        change ((N ^ k : ℕ) : ℝ) = (((N : NNReal) ^ m : NNReal) : ℝ)
        rw [← hk_eq, zpow_natCast]
        push_cast
        rfl
      · rw [hv_le_one]
        have hN_mem : (N : NumberField.RingOfIntegers K) ∈ p.asIdeal := Ideal.absNorm_mem p.asIdeal
        have hN_val_lt : p.valuation K (N : K) < 1 := by
          have h1 := (p.valuation_lt_one_iff_mem (K := K) (N : NumberField.RingOfIntegers K)).mpr hN_mem
          simpa using h1
        have hN_val_le : p.valuation K (N : K) ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
          cases h : p.valuation K (N : K) with
          | zero => exact zero_le'
          | coe a =>
            rw [h] at hN_val_lt
            have ha : Multiplicative.toAdd a < 0 := WithZero.coe_lt_coe.mp hN_val_lt
            have ha' : Multiplicative.toAdd a ≤ -1 := by omega
            exact WithZero.coe_le_coe.mpr ha'
        rw [Nat.cast_pow, map_mul, map_pow, hval_eq]
        calc (p.valuation K (N : K)) ^ k * ↑(Multiplicative.ofAdd m)
          _ ≤ (((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) ^ k * ↑(Multiplicative.ofAdd m) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left' hN_val_le k) zero_le'
          _ = 1 := by
            rw [← WithZero.coe_pow, ← WithZero.coe_mul, ← ofAdd_nsmul, ← ofAdd_add]
            simp [← hk_eq]
  have exists_nat_mul_mem_ringOfIntegers_of_local : ∀ x : K,
      ∃ d : ℕ, 1 ≤ d ∧
        (d : ℝ) ≤ (∏ᶠ v : NumberField.FinitePlace K, max (v x) 1) ∧
        ∃ y : NumberField.RingOfIntegers K,
          algebraMap (NumberField.RingOfIntegers K) K y = (d : K) * x := by
    intro x
    by_cases hx : x = 0
    · refine ⟨1, le_rfl, ?_, 0, by simp [hx]⟩
      rw [Nat.cast_one]
      exact one_le_finprod (fun v => le_max_right _ _)
    · let n : NumberField.FinitePlace K → ℕ := fun v => (finitePlace_local_clear_denom v x).choose
      have hn : ∀ v, 1 ≤ n v ∧ (n v : ℝ) = max (v x) 1 ∧ v ((n v : K) * x) ≤ 1 :=
        fun v => (finitePlace_local_clear_denom v x).choose_spec
      have h_supp_sub : Function.mulSupport (fun v : NumberField.FinitePlace K => max (v x) 1) ⊆
          Function.mulSupport (fun v : NumberField.FinitePlace K => v x) := by
        intro v hv
        rw [Function.mem_mulSupport] at hv ⊢
        intro hv1
        apply hv
        rw [hv1, max_self]
      have hf : (Function.mulSupport (fun v : NumberField.FinitePlace K => max (v x) 1)).Finite :=
        (NumberField.FinitePlace.mulSupport_finite hx).subset h_supp_sub
      let S := hf.toFinset
      let d : ℕ := ∏ v ∈ S, n v
      have hd1 : 1 ≤ d := Finset.one_le_prod S (fun v => (hn v).1)
      have hd_eq : (d : ℝ) = ∏ᶠ v : NumberField.FinitePlace K, max (v x) 1 := by
        rw [finprod_eq_prod _ hf]
        dsimp [d, S]
        rw [Nat.cast_prod]
        exact Finset.prod_congr rfl (fun v _ => (hn v).2.1)
      have hw_nat : ∀ (w : NumberField.FinitePlace K) (m : ℕ), w (m : K) ≤ 1 := by
        intro w m
        rw [← NumberField.FinitePlace.norm_embedding_eq, NumberField.FinitePlace.norm_def]
        exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv_intCast_le_one w.maximalIdeal (m : ℤ)
      have hw_dx : ∀ w : NumberField.FinitePlace K, w ((d : K) * x) ≤ 1 := by
        intro w
        by_cases hw : w ∈ S
        · have hd_split : (d : K) * x = (∏ v ∈ S.erase w, (n v : K)) * ((n w : K) * x) := by
            dsimp [d]
            rw [← Finset.mul_prod_erase S n hw, Nat.cast_mul, Nat.cast_prod]
            ring
          rw [hd_split, map_mul, map_prod]
          have h_prod_le : (∏ v ∈ S.erase w, w (n v : K)) ≤ 1 :=
            Finset.prod_le_one (fun v _ => apply_nonneg w _) (fun v _ => hw_nat w (n v))
          exact mul_le_one₀ h_prod_le (apply_nonneg w _) (hn w).2.2
        · have hwx_le : w x ≤ 1 := by
            have hw_not_supp : w ∉ Function.mulSupport (fun v : NumberField.FinitePlace K => max (v x) 1) := by
              rwa [Set.Finite.mem_toFinset] at hw
            rw [Function.mem_mulSupport, not_not] at hw_not_supp
            calc w x ≤ max (w x) 1 := le_max_left _ _
              _ = 1 := hw_not_supp
          rw [map_mul, show (d : K) = ∏ v ∈ S, (n v : K) by simp [d], map_prod]
          have h_prod_le : (∏ v ∈ S, w (n v : K)) ≤ 1 :=
            Finset.prod_le_one (fun v _ => apply_nonneg w _) (fun v _ => hw_nat w (n v))
          exact mul_le_one₀ h_prod_le (apply_nonneg w _) hwx_le
      have hp_val : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          p.valuation K ((d : K) * x) ≤ 1 := by
        intro p
        have hw := hw_dx (NumberField.FinitePlace.mk p)
        rw [NumberField.FinitePlace.mk_apply, NumberField.FinitePlace.norm_def'] at hw
        have hN_nn : 1 < (Ideal.absNorm p.asIdeal : NNReal) :=
          NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm_nnreal p
        exact (WithZeroMulInt.toNNReal_le_one_iff hN_nn).mp (by exact_mod_cast hw)
      obtain ⟨y, hy⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K ((d : K) * x) hp_val
      exact ⟨d, hd1, hd_eq.le, y, hy⟩
  let M : ℝ := Real.exp C₃
  let S_D : Set ℕ := Set.Icc 1 (Nat.floor M)
  have hS_D : S_D.Finite := Set.finite_Icc 1 (Nat.floor M)
  let S_Y : Set (NumberField.RingOfIntegers K) :=
    {y : NumberField.RingOfIntegers K |
      ∀ w : NumberField.InfinitePlace K,
        w (algebraMap (NumberField.RingOfIntegers K) K y) ≤ M ^ 2}
  have hS_Y : S_Y.Finite := ringOfIntegers_bounded_infinitePlace_finite (M ^ 2)
  let S_X : Set K := {x : K | fieldLogHeight x ≤ C₃}
  have hS_X : S_X.Finite := by
    have h_sub : S_X ⊆ ⋃ d ∈ S_D, ⋃ y ∈ S_Y, {(algebraMap (NumberField.RingOfIntegers K) K y) / (d : K)} := by
      intro x hx
      obtain ⟨h_fin_le, h_inf_le⟩ := fieldLogHeight_bounds x hx
      obtain ⟨d, hd1, hd_le_fin, y, hy⟩ := exists_nat_mul_mem_ringOfIntegers_of_local x
      have hd_le_M : (d : ℝ) ≤ M := le_trans hd_le_fin h_fin_le
      have hd_mem : d ∈ S_D := ⟨hd1, Nat.le_floor hd_le_M⟩
      have hy_mem : y ∈ S_Y := by
        intro w
        rw [hy, map_mul, NumberField.InfinitePlace.map_natCast]
        calc (d : ℝ) * w x ≤ M * M :=
            mul_le_mul hd_le_M (h_inf_le w) (apply_nonneg w x) (by positivity)
          _ = M ^ 2 := by ring
      have hd_ne : (d : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hx_eq : x = (algebraMap (NumberField.RingOfIntegers K) K y) / (d : K) := by
        rw [hy, mul_div_cancel_left₀ x hd_ne]
      exact Set.mem_biUnion hd_mem (Set.mem_biUnion hy_mem hx_eq)
    exact (hS_D.biUnion (fun d _ => hS_Y.biUnion (fun y _ => Set.finite_singleton _))).subset h_sub
  have h_pts_sub : {P : E.toAffine.Point | weierstrassHeight E P ≤ C₃} ⊆
      {.zero} ∪ ⋃ x ∈ S_X, {P : E.toAffine.Point | ∃ (y : K) (h : E.toAffine.Nonsingular x y),
        P = WeierstrassCurve.Affine.Point.some h} := by
    intro P hP
    rcases P with _ | @⟨x, y, h⟩
    · left; rfl
    · right
      have hx : x ∈ S_X := hP
      exact Set.mem_biUnion hx ⟨y, h, rfl⟩
  exact ((Set.finite_singleton _).union (hS_X.biUnion (fun x _ => weierstrass_fiber_finite x))).subset h_pts_sub

theorem height_add_bound {K : Type u} [Field K] [NumberField K] [DecidableEq K]
    (E : WeierstrassCurve K) (hE : E.IsElliptic) (Q : E.toAffine.Point) :
    ∃ C₁ : ℝ, ∀ P : E.toAffine.Point, weierstrassHeight E (P + Q) ≤ 2 * weierstrassHeight E P + C₁ :=
by
  have _ := hE
  have h_chord_eq : ∀ {x₀ y₀ x y : K}, E.toAffine.Equation x y → x ≠ x₀ →
      E.toAffine.addX x x₀ (E.toAffine.slope x x₀ y y₀) =
        chordNum E x₀ y₀ x y / chordDen x₀ x := by
    intro x₀ y₀ x y hP hx
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
    unfold WeierstrassCurve.Affine.addX chordNum chordDen
    have heq : y ^ 2 + E.a₁ * x * y + E.a₃ * y = x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆ :=
      (E.toAffine.equation_iff x y).mp hP
    have hsub : x - x₀ ≠ 0 := sub_ne_zero.mpr hx
    field_simp
    linear_combination heq
  have h_arch : ∀ (x₀ y₀ : K) {x y : K}, E.toAffine.Equation x y →
      ∀ (w : NumberField.InfinitePlace K),
        1 ≤ 8 * curvePlaceConst E x₀ y₀ w ^ 2 ∧
          max (w (chordNum E x₀ y₀ x y)) (w (chordDen x₀ x)) ≤
            (8 * curvePlaceConst E x₀ y₀ w ^ 2) * max (w x) 1 ^ 2 := by
    intro x₀ y₀ x y hP w
    set Kw := curvePlaceConst E x₀ y₀ w
    set M := max (w x) 1
    set α₁ := E.a₄ + x₀ ^ 2 + 2 * E.a₂ * x₀ - E.a₁ * y₀
    set β₀ := 2 * y₀ + E.a₁ * x₀ + E.a₃
    set α₀ := E.a₆ + y₀ ^ 2 + E.a₁ * x₀ * y₀ - x₀ ^ 3 - E.a₂ * x₀ ^ 2
    have hKw1 : 1 ≤ Kw := le_max_left _ _
    have hKw_sub : max (w E.a₁) (max (w E.a₂) (max (w E.a₃) (max (w E.a₄) (max (w E.a₆)
        (max (w x₀) (max (w α₁) (max (w β₀) (w α₀)))))))) ≤ Kw := le_max_right _ _
    have ha1 : w E.a₁ ≤ Kw := le_trans (le_max_left _ _) hKw_sub
    have hKw_sub2 := le_trans (le_max_right _ _) hKw_sub
    have ha2 : w E.a₂ ≤ Kw := le_trans (le_max_left _ _) hKw_sub2
    have hKw_sub3 := le_trans (le_max_right _ _) hKw_sub2
    have ha3 : w E.a₃ ≤ Kw := le_trans (le_max_left _ _) hKw_sub3
    have hKw_sub4 := le_trans (le_max_right _ _) hKw_sub3
    have ha4 : w E.a₄ ≤ Kw := le_trans (le_max_left _ _) hKw_sub4
    have hKw_sub5 := le_trans (le_max_right _ _) hKw_sub4
    have ha6 : w E.a₆ ≤ Kw := le_trans (le_max_left _ _) hKw_sub5
    have hKw_sub6 := le_trans (le_max_right _ _) hKw_sub5
    have hx0 : w x₀ ≤ Kw := le_trans (le_max_left _ _) hKw_sub6
    have hKw_sub7 := le_trans (le_max_right _ _) hKw_sub6
    have hα1 : w α₁ ≤ Kw := le_trans (le_max_left _ _) hKw_sub7
    have hKw_sub8 := le_trans (le_max_right _ _) hKw_sub7
    have hβ0 : w β₀ ≤ Kw := le_trans (le_max_left _ _) hKw_sub8
    have hα0 : w α₀ ≤ Kw := le_trans (le_max_right _ _) hKw_sub8
    have hM1 : 1 ≤ M := le_max_right _ _
    have hxM : w x ≤ M := le_max_left _ _
    have hwx0 : 0 ≤ w x := apply_nonneg w x
    have hwy0 : 0 ≤ w y := apply_nonneg w y
    have hw_add (a b : K) : w (a + b) ≤ w a + w b := by
      rw [w.coe_apply, w.coe_apply, w.coe_apply]
      exact w.1.add_le a b
    have hw_neg (a : K) : w (-a) = w a := by
      rw [w.coe_apply, w.coe_apply]
      exact w.1.map_neg a
    have hw_sub (a b : K) : w (a - b) ≤ w a + w b := by
      rw [sub_eq_add_neg, ← hw_neg b]
      exact hw_add a (-b)
    have heq : y ^ 2 = x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆ - E.a₁ * x * y - E.a₃ * y := by
      have h1 := (E.toAffine.equation_iff x y).mp hP
      linear_combination h1
    have hy2_le : w y ^ 2 ≤ w x ^ 3 + w E.a₂ * w x ^ 2 + w E.a₄ * w x + w E.a₆ +
        w E.a₁ * w x * w y + w E.a₃ * w y := by
      calc w y ^ 2 = w (y ^ 2) := (map_pow w y 2).symm
        _ = w (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆ - E.a₁ * x * y - E.a₃ * y) := by rw [heq]
        _ ≤ w (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆ - E.a₁ * x * y) + w (E.a₃ * y) := hw_sub _ _
        _ ≤ w (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆) + w (E.a₁ * x * y) + w (E.a₃ * y) := by
          linarith [hw_sub (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆) (E.a₁ * x * y)]
        _ ≤ w (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x) + w E.a₆ + w (E.a₁ * x * y) + w (E.a₃ * y) := by
          linarith [hw_add (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x) E.a₆]
        _ ≤ w (x ^ 3 + E.a₂ * x ^ 2) + w (E.a₄ * x) + w E.a₆ + w (E.a₁ * x * y) + w (E.a₃ * y) := by
          linarith [hw_add (x ^ 3 + E.a₂ * x ^ 2) (E.a₄ * x)]
        _ ≤ w (x ^ 3) + w (E.a₂ * x ^ 2) + w (E.a₄ * x) + w E.a₆ + w (E.a₁ * x * y) + w (E.a₃ * y) := by
          linarith [hw_add (x ^ 3) (E.a₂ * x ^ 2)]
        _ = w x ^ 3 + w E.a₂ * w x ^ 2 + w E.a₄ * w x + w E.a₆ + w E.a₁ * w x * w y + w E.a₃ * w y := by
          simp only [map_pow, map_mul]
    have hKw_sq : 1 ≤ Kw ^ 2 := one_le_pow₀ hKw1
    have hKw_le_sq : Kw ≤ Kw ^ 2 := by simpa only [pow_one] using pow_le_pow_right₀ hKw1 (by decide : 1 ≤ 2)
    have hM_sq : 1 ≤ M ^ 2 := one_le_pow₀ hM1
    have hM_le_sq : M ≤ M ^ 2 := by simpa only [pow_one] using pow_le_pow_right₀ hM1 (by decide : 1 ≤ 2)
    have hM_sq_le_4 : M ^ 2 ≤ M ^ 4 := pow_le_pow_right₀ hM1 (by decide : 2 ≤ 4)
    have hM_3_le_4 : M ^ 3 ≤ M ^ 4 := pow_le_pow_right₀ hM1 (by decide : 3 ≤ 4)
    have hM_1_le_4 : M ≤ M ^ 4 := le_trans hM_le_sq hM_sq_le_4
    have hM_4 : 1 ≤ M ^ 4 := le_trans hM1 hM_1_le_4
    have hx2 : w x ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hwx0 hxM 2
    have hx3 : w x ^ 3 ≤ M ^ 3 := pow_le_pow_left₀ hwx0 hxM 3
    have ht_x3 : w x ^ 3 ≤ Kw ^ 2 * M ^ 4 := by
      calc w x ^ 3 ≤ 1 * M ^ 4 := by linarith
        _ ≤ Kw ^ 2 * M ^ 4 := mul_le_mul_of_nonneg_right hKw_sq (by positivity)
    have ht_a2 : w E.a₂ * w x ^ 2 ≤ Kw ^ 2 * M ^ 4 :=
      mul_le_mul (le_trans ha2 hKw_le_sq) (le_trans hx2 hM_sq_le_4) (by positivity) (by positivity)
    have ht_a4 : w E.a₄ * w x ≤ Kw ^ 2 * M ^ 4 :=
      mul_le_mul (le_trans ha4 hKw_le_sq) (le_trans hxM hM_1_le_4) hwx0 (by positivity)
    have ht_a6 : w E.a₆ ≤ Kw ^ 2 * M ^ 4 := by
      calc w E.a₆ ≤ Kw * 1 := by linarith
        _ ≤ Kw ^ 2 * M ^ 4 := mul_le_mul hKw_le_sq hM_4 zero_le_one (by positivity)
    have ht_a1 : w E.a₁ * w x * w y ≤ Kw * M ^ 2 * w y :=
      mul_le_mul_of_nonneg_right (mul_le_mul ha1 (le_trans hxM hM_le_sq) hwx0 (by positivity)) hwy0
    have ht_a3 : w E.a₃ * w y ≤ Kw * M ^ 2 * w y := by
      have h1 : w E.a₃ ≤ Kw * M ^ 2 := by
        calc w E.a₃ ≤ Kw * 1 := by linarith
          _ ≤ Kw * M ^ 2 := mul_le_mul_of_nonneg_left hM_sq (by positivity)
      exact mul_le_mul_of_nonneg_right h1 hwy0
    have hy_quad : w y ^ 2 ≤ 8 * Kw ^ 2 * M ^ 4 + 2 * Kw * M ^ 2 * w y := by
      have hpos : 0 ≤ Kw ^ 2 * M ^ 4 := by positivity
      linarith
    have hy_bound : w y ≤ 4 * Kw * M ^ 2 := by
      by_contra! h_gt
      have h_fac : (w y - 4 * Kw * M ^ 2) * (w y + 2 * Kw * M ^ 2) ≤ 0 := by
        calc (w y - 4 * Kw * M ^ 2) * (w y + 2 * Kw * M ^ 2)
          _ = w y ^ 2 - (8 * Kw ^ 2 * M ^ 4 + 2 * Kw * M ^ 2 * w y) := by ring
          _ ≤ 0 := sub_nonpos.mpr hy_quad
      have h_pos1 : 0 < w y - 4 * Kw * M ^ 2 := sub_pos.mpr h_gt
      have h_pos2 : 0 < w y + 2 * Kw * M ^ 2 := by positivity
      linarith [mul_pos h_pos1 h_pos2]
    have h_num : w (chordNum E x₀ y₀ x y) ≤ 8 * Kw ^ 2 * M ^ 2 := by
      have h1 : w (chordNum E x₀ y₀ x y) ≤ w x₀ * w x ^ 2 + w α₁ * w x + w β₀ * w y + w α₀ := by
        calc w (chordNum E x₀ y₀ x y)
          _ = w (x₀ * x ^ 2 + α₁ * x - β₀ * y + α₀) := rfl
          _ ≤ w (x₀ * x ^ 2 + α₁ * x - β₀ * y) + w α₀ := hw_add _ _
          _ ≤ w (x₀ * x ^ 2 + α₁ * x) + w (β₀ * y) + w α₀ := by linarith [hw_sub (x₀ * x ^ 2 + α₁ * x) (β₀ * y)]
          _ ≤ w (x₀ * x ^ 2) + w (α₁ * x) + w (β₀ * y) + w α₀ := by linarith [hw_add (x₀ * x ^ 2) (α₁ * x)]
          _ = w x₀ * w x ^ 2 + w α₁ * w x + w β₀ * w y + w α₀ := by simp only [map_mul, map_pow]
      have ht1 : w x₀ * w x ^ 2 ≤ Kw ^ 2 * M ^ 2 :=
        mul_le_mul (le_trans hx0 hKw_le_sq) hx2 (by positivity) (by positivity)
      have ht2 : w α₁ * w x ≤ Kw ^ 2 * M ^ 2 :=
        mul_le_mul (le_trans hα1 hKw_le_sq) (le_trans hxM hM_le_sq) hwx0 (by positivity)
      have ht3 : w β₀ * w y ≤ 4 * (Kw ^ 2 * M ^ 2) := by
        calc w β₀ * w y ≤ Kw * (4 * Kw * M ^ 2) := mul_le_mul hβ0 hy_bound hwy0 (by positivity)
          _ = 4 * (Kw ^ 2 * M ^ 2) := by ring
      have ht4 : w α₀ ≤ Kw ^ 2 * M ^ 2 := by
        calc w α₀ ≤ Kw * 1 := by linarith
          _ ≤ Kw ^ 2 * M ^ 2 := mul_le_mul hKw_le_sq hM_sq zero_le_one (by positivity)
      have hpos : 0 ≤ Kw ^ 2 * M ^ 2 := by positivity
      linarith
    have h_den : w (chordDen x₀ x) ≤ 8 * Kw ^ 2 * M ^ 2 := by
      have h1 : w (x - x₀) ≤ 2 * (Kw * M) := by
        have hx_km : w x ≤ Kw * M := by
          calc w x ≤ 1 * M := by linarith
            _ ≤ Kw * M := mul_le_mul_of_nonneg_right hKw1 (by positivity)
        have hx0_km : w x₀ ≤ Kw * M := by
          calc w x₀ ≤ Kw * 1 := by linarith
            _ ≤ Kw * M := mul_le_mul_of_nonneg_left hM1 (by positivity)
        linarith [hw_sub x x₀]
      have h2 : w (chordDen x₀ x) ≤ (2 * (Kw * M)) ^ 2 := by
        rw [chordDen, map_pow]
        exact pow_le_pow_left₀ (apply_nonneg w (x - x₀)) h1 2
      have h3 : (2 * (Kw * M)) ^ 2 = 4 * (Kw ^ 2 * M ^ 2) := by ring
      have hpos : 0 ≤ Kw ^ 2 * M ^ 2 := by positivity
      linarith
    exact ⟨by linarith, max_le h_num h_den⟩
  have h_nonarch : ∀ (x₀ y₀ : K),
      (Function.mulSupport fun v : NumberField.FinitePlace K => curvePlaceConst E x₀ y₀ v ^ 2).Finite ∧
        (∀ v : NumberField.FinitePlace K, 1 ≤ curvePlaceConst E x₀ y₀ v ^ 2) ∧
        (∀ {x y : K}, E.toAffine.Equation x y → ∀ v : NumberField.FinitePlace K,
          max (v (chordNum E x₀ y₀ x y)) (v (chordDen x₀ x)) ≤
            curvePlaceConst E x₀ y₀ v ^ 2 * max (v x) 1 ^ 2) := by
    intro x₀ y₀
    have h_single (c : K) : (Function.mulSupport fun v : NumberField.FinitePlace K => max 1 (v c)).Finite := by
      by_cases hc : c = 0
      · convert Set.finite_empty
        ext v
        simp [hc]
      · refine (NumberField.FinitePlace.mulSupport_finite hc).subset (fun v hv => ?_)
        simp only [Function.mem_mulSupport] at hv ⊢
        intro hvc
        exact hv (by rw [hvc, max_self])
    have h_le_one {c : K} {v : NumberField.FinitePlace K}
        (h : v ∉ Function.mulSupport (fun u : NumberField.FinitePlace K => max 1 (u c))) :
        v c ≤ 1 := by
      simp only [Function.mem_mulSupport, not_not] at h
      exact le_trans (le_max_right 1 (v c)) (le_of_eq h)
    set α₁ := E.a₄ + x₀ ^ 2 + 2 * E.a₂ * x₀ - E.a₁ * y₀
    set β₀ := 2 * y₀ + E.a₁ * x₀ + E.a₃
    set α₀ := E.a₆ + y₀ ^ 2 + E.a₁ * x₀ * y₀ - x₀ ^ 3 - E.a₂ * x₀ ^ 2
    have h_const_supp : (Function.mulSupport fun v : NumberField.FinitePlace K => curvePlaceConst E x₀ y₀ v).Finite := by
      refine (((((((((h_single E.a₁).union (h_single E.a₂)).union (h_single E.a₃)).union
        (h_single E.a₄)).union (h_single E.a₆)).union (h_single x₀)).union
        (h_single α₁)).union (h_single β₀)).union (h_single α₀)).subset (fun v hv => ?_)
      simp only [Function.mem_mulSupport] at hv
      by_contra h_not
      simp only [Set.mem_union, not_or] at h_not
      rcases h_not with ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h6⟩, hx0⟩, hα1⟩, hβ0⟩, hα0⟩
      apply hv
      unfold curvePlaceConst
      exact le_antisymm
        (max_le le_rfl (max_le (h_le_one h1) (max_le (h_le_one h2) (max_le (h_le_one h3)
          (max_le (h_le_one h4) (max_le (h_le_one h6) (max_le (h_le_one hx0)
            (max_le (h_le_one hα1) (max_le (h_le_one hβ0) (h_le_one hα0))))))))))
        (le_max_left _ _)
    have h_sq_supp : (Function.mulSupport fun v : NumberField.FinitePlace K => curvePlaceConst E x₀ y₀ v ^ 2).Finite := by
      refine h_const_supp.subset (fun v hv => ?_)
      simp only [Function.mem_mulSupport] at hv ⊢
      intro h1
      exact hv (by rw [h1, one_pow])
    refine ⟨h_sq_supp, fun v => one_le_pow₀ (le_max_left _ _), fun {x y} hP v => ?_⟩
    set Kv := curvePlaceConst E x₀ y₀ v
    set M := max (v x) 1
    have hKv1 : 1 ≤ Kv := le_max_left _ _
    have hKv_sub : max (v E.a₁) (max (v E.a₂) (max (v E.a₃) (max (v E.a₄) (max (v E.a₆)
        (max (v x₀) (max (v α₁) (max (v β₀) (v α₀)))))))) ≤ Kv := le_max_right _ _
    have ha1 : v E.a₁ ≤ Kv := le_trans (le_max_left _ _) hKv_sub
    have hKv_sub2 := le_trans (le_max_right _ _) hKv_sub
    have ha2 : v E.a₂ ≤ Kv := le_trans (le_max_left _ _) hKv_sub2
    have hKv_sub3 := le_trans (le_max_right _ _) hKv_sub2
    have ha3 : v E.a₃ ≤ Kv := le_trans (le_max_left _ _) hKv_sub3
    have hKv_sub4 := le_trans (le_max_right _ _) hKv_sub3
    have ha4 : v E.a₄ ≤ Kv := le_trans (le_max_left _ _) hKv_sub4
    have hKv_sub5 := le_trans (le_max_right _ _) hKv_sub4
    have ha6 : v E.a₆ ≤ Kv := le_trans (le_max_left _ _) hKv_sub5
    have hKv_sub6 := le_trans (le_max_right _ _) hKv_sub5
    have hx0 : v x₀ ≤ Kv := le_trans (le_max_left _ _) hKv_sub6
    have hKv_sub7 := le_trans (le_max_right _ _) hKv_sub6
    have hα1 : v α₁ ≤ Kv := le_trans (le_max_left _ _) hKv_sub7
    have hKv_sub8 := le_trans (le_max_right _ _) hKv_sub7
    have hβ0 : v β₀ ≤ Kv := le_trans (le_max_left _ _) hKv_sub8
    have hα0 : v α₀ ≤ Kv := le_trans (le_max_right _ _) hKv_sub8
    have hM1 : 1 ≤ M := le_max_right _ _
    have hxM : v x ≤ M := le_max_left _ _
    have hvx0 : 0 ≤ v x := apply_nonneg v x
    have hvy0 : 0 ≤ v y := apply_nonneg v y
    have hv_neg (a : K) : v (-a) = v a := by
      rw [v.coe_apply, v.coe_apply]
      exact v.1.map_neg a
    have hv_sub (a b : K) : v (a - b) ≤ max (v a) (v b) := by
      rw [sub_eq_add_neg, ← hv_neg b]
      exact v.add_le a (-b)
    have hKv_sq : 1 ≤ Kv ^ 2 := one_le_pow₀ hKv1
    have hKv_le_sq : Kv ≤ Kv ^ 2 := by simpa only [pow_one] using pow_le_pow_right₀ hKv1 (by decide : 1 ≤ 2)
    have hM_sq : 1 ≤ M ^ 2 := one_le_pow₀ hM1
    have hM_le_sq : M ≤ M ^ 2 := by simpa only [pow_one] using pow_le_pow_right₀ hM1 (by decide : 1 ≤ 2)
    have hM_sq_le_4 : M ^ 2 ≤ M ^ 4 := pow_le_pow_right₀ hM1 (by decide : 2 ≤ 4)
    have hM_3_le_4 : M ^ 3 ≤ M ^ 4 := pow_le_pow_right₀ hM1 (by decide : 3 ≤ 4)
    have hM_1_le_4 : M ≤ M ^ 4 := le_trans hM_le_sq hM_sq_le_4
    have hM_4 : 1 ≤ M ^ 4 := le_trans hM1 hM_1_le_4
    have hx2 : v x ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hvx0 hxM 2
    have hx3 : v x ^ 3 ≤ M ^ 3 := pow_le_pow_left₀ hvx0 hxM 3
    have ht_x3 : v (x ^ 3) ≤ Kv ^ 2 * M ^ 4 := by
      rw [map_pow]
      calc v x ^ 3 ≤ 1 * M ^ 4 := by linarith
        _ ≤ Kv ^ 2 * M ^ 4 := mul_le_mul_of_nonneg_right hKv_sq (by positivity)
    have ht_a2 : v (E.a₂ * x ^ 2) ≤ Kv ^ 2 * M ^ 4 := by
      rw [map_mul, map_pow]
      exact mul_le_mul (le_trans ha2 hKv_le_sq) (le_trans hx2 hM_sq_le_4) (by positivity) (by positivity)
    have ht_a4 : v (E.a₄ * x) ≤ Kv ^ 2 * M ^ 4 := by
      rw [map_mul]
      exact mul_le_mul (le_trans ha4 hKv_le_sq) (le_trans hxM hM_1_le_4) hvx0 (by positivity)
    have ht_a6 : v E.a₆ ≤ Kv ^ 2 * M ^ 4 := by
      calc v E.a₆ ≤ Kv * 1 := by linarith
        _ ≤ Kv ^ 2 * M ^ 4 := mul_le_mul hKv_le_sq hM_4 zero_le_one (by positivity)
    have ht_a1 : v (E.a₁ * x * y) ≤ Kv * M ^ 2 * v y := by
      rw [map_mul, map_mul]
      exact mul_le_mul_of_nonneg_right (mul_le_mul ha1 (le_trans hxM hM_le_sq) hvx0 (by positivity)) hvy0
    have ht_a3 : v (E.a₃ * y) ≤ Kv * M ^ 2 * v y := by
      rw [map_mul]
      have h1 : v E.a₃ ≤ Kv * M ^ 2 := by
        calc v E.a₃ ≤ Kv * 1 := by linarith
          _ ≤ Kv * M ^ 2 := mul_le_mul_of_nonneg_left hM_sq (by positivity)
      exact mul_le_mul_of_nonneg_right h1 hvy0
    have heq : y ^ 2 = (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆) - (E.a₁ * x * y + E.a₃ * y) := by
      have h1 := (E.toAffine.equation_iff x y).mp hP
      linear_combination h1
    have h_rhs1 : v (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆) ≤ Kv ^ 2 * M ^ 4 := by
      refine le_trans (v.add_le _ _) (max_le ?_ ht_a6)
      refine le_trans (v.add_le _ _) (max_le ?_ ht_a4)
      exact le_trans (v.add_le _ _) (max_le ht_x3 ht_a2)
    have h_rhs2 : v (E.a₁ * x * y + E.a₃ * y) ≤ Kv * M ^ 2 * v y :=
      le_trans (v.add_le _ _) (max_le ht_a1 ht_a3)
    have hy_max : v y ^ 2 ≤ max (Kv ^ 2 * M ^ 4) (Kv * M ^ 2 * v y) := by
      calc v y ^ 2 = v (y ^ 2) := (map_pow v y 2).symm
        _ = v ((x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆) - (E.a₁ * x * y + E.a₃ * y)) := by rw [heq]
        _ ≤ max (v (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆)) (v (E.a₁ * x * y + E.a₃ * y)) := hv_sub _ _
        _ ≤ max (Kv ^ 2 * M ^ 4) (Kv * M ^ 2 * v y) := max_le_max h_rhs1 h_rhs2
    have hy_bound : v y ≤ Kv * M ^ 2 := by
      rcases le_max_iff.mp hy_max with hcase1 | hcase2
      · by_contra! h_gt
        have h_fac : (v y - Kv * M ^ 2) * (v y + Kv * M ^ 2) ≤ 0 := by
          calc (v y - Kv * M ^ 2) * (v y + Kv * M ^ 2)
            _ = v y ^ 2 - Kv ^ 2 * M ^ 4 := by ring
            _ ≤ 0 := sub_nonpos.mpr hcase1
        have h_pos1 : 0 < v y - Kv * M ^ 2 := sub_pos.mpr h_gt
        have h_pos2 : 0 < v y + Kv * M ^ 2 := by positivity
        linarith [mul_pos h_pos1 h_pos2]
      · by_contra! h_gt
        have h_fac : (v y - Kv * M ^ 2) * v y ≤ 0 := by
          calc (v y - Kv * M ^ 2) * v y
            _ = v y ^ 2 - Kv * M ^ 2 * v y := by ring
            _ ≤ 0 := sub_nonpos.mpr hcase2
        have h_pos1 : 0 < v y - Kv * M ^ 2 := sub_pos.mpr h_gt
        have h_pos2 : 0 < v y := lt_of_lt_of_le (by positivity : 0 < Kv * M ^ 2) (le_of_lt h_gt)
        linarith [mul_pos h_pos1 h_pos2]
    have h_num : v (chordNum E x₀ y₀ x y) ≤ Kv ^ 2 * M ^ 2 := by
      change v (x₀ * x ^ 2 + α₁ * x - β₀ * y + α₀) ≤ Kv ^ 2 * M ^ 2
      have ht1 : v (x₀ * x ^ 2) ≤ Kv ^ 2 * M ^ 2 := by
        rw [map_mul, map_pow]
        exact mul_le_mul (le_trans hx0 hKv_le_sq) hx2 (by positivity) (by positivity)
      have ht2 : v (α₁ * x) ≤ Kv ^ 2 * M ^ 2 := by
        rw [map_mul]
        exact mul_le_mul (le_trans hα1 hKv_le_sq) (le_trans hxM hM_le_sq) hvx0 (by positivity)
      have ht3 : v (β₀ * y) ≤ Kv ^ 2 * M ^ 2 := by
        rw [map_mul]
        calc v β₀ * v y ≤ Kv * (Kv * M ^ 2) := mul_le_mul hβ0 hy_bound hvy0 (by positivity)
          _ = Kv ^ 2 * M ^ 2 := by ring
      have ht4 : v α₀ ≤ Kv ^ 2 * M ^ 2 := by
        calc v α₀ ≤ Kv * 1 := by linarith
          _ ≤ Kv ^ 2 * M ^ 2 := mul_le_mul hKv_le_sq hM_sq zero_le_one (by positivity)
      refine le_trans (v.add_le _ _) (max_le ?_ ht4)
      refine le_trans (hv_sub _ _) (max_le ?_ ht3)
      exact le_trans (v.add_le _ _) (max_le ht1 ht2)
    have h_den : v (chordDen x₀ x) ≤ Kv ^ 2 * M ^ 2 := by
      have h1 : v (x - x₀) ≤ Kv * M := by
        refine le_trans (hv_sub x x₀) (max_le ?_ ?_)
        · calc v x ≤ 1 * M := by linarith
            _ ≤ Kv * M := mul_le_mul_of_nonneg_right hKv1 (by positivity)
        · calc v x₀ ≤ Kv * 1 := by linarith
            _ ≤ Kv * M := mul_le_mul_of_nonneg_left hM1 (by positivity)
      have h2 : v (chordDen x₀ x) ≤ (Kv * M) ^ 2 := by
        rw [chordDen, map_pow]
        exact pow_le_pow_left₀ (apply_nonneg v (x - x₀)) h1 2
      have h3 : (Kv * M) ^ 2 = Kv ^ 2 * M ^ 2 := by ring
      linarith
    exact max_le h_num h_den
  have h_div_bound : ∀ (C_inf : NumberField.InfinitePlace K → ℝ) (C_fin : NumberField.FinitePlace K → ℝ),
      (∀ w, 1 ≤ C_inf w) → (∀ v, 1 ≤ C_fin v) → (Function.mulSupport C_fin).Finite →
      ∀ (x N D : K), D ≠ 0 →
      (∀ w : NumberField.InfinitePlace K, max (w N) (w D) ≤ C_inf w * max (w x) 1 ^ 2) →
      (∀ v : NumberField.FinitePlace K, max (v N) (v D) ≤ C_fin v * max (v x) 1 ^ 2) →
      fieldLogHeight (N / D) ≤ 2 * fieldLogHeight x +
        Real.log ((∏ w : NumberField.InfinitePlace K, C_inf w ^ w.mult) *
          (∏ᶠ v : NumberField.FinitePlace K, C_fin v)) := by
    intro C_inf C_fin hC_inf hC_fin hC_fin_supp x N D hD h_inf h_fin
    have hw_step (w : NumberField.InfinitePlace K) :
        max (w (N / D)) 1 ^ w.mult * w D ^ w.mult ≤
          C_inf w ^ w.mult * (max (w x) 1 ^ w.mult) ^ 2 := by
      have h1 : max (w (N / D)) 1 * w D = max (w N) (w D) := by
        rw [mul_comm, mul_max_of_nonneg _ _ (apply_nonneg w D), mul_comm (w D),
          ← map_mul, div_mul_cancel₀ _ hD, mul_one]
      have h2 : max (w (N / D)) 1 * w D ≤ C_inf w * max (w x) 1 ^ 2 := h1.trans_le (h_inf w)
      have h3 : 0 ≤ max (w (N / D)) 1 * w D :=
        mul_nonneg (le_trans zero_le_one (le_max_right _ _)) (apply_nonneg w D)
      calc max (w (N / D)) 1 ^ w.mult * w D ^ w.mult
        _ = (max (w (N / D)) 1 * w D) ^ w.mult := (mul_pow _ _ _).symm
        _ ≤ (C_inf w * max (w x) 1 ^ 2) ^ w.mult := pow_le_pow_left₀ h3 h2 w.mult
        _ = C_inf w ^ w.mult * (max (w x) 1 ^ w.mult) ^ 2 := by
          rw [mul_pow, ← pow_mul, mul_comm 2 w.mult, pow_mul]
    have h_arch_prod :
        (∏ w : NumberField.InfinitePlace K, max (w (N / D)) 1 ^ w.mult) *
          (∏ w : NumberField.InfinitePlace K, w D ^ w.mult) ≤
        (∏ w : NumberField.InfinitePlace K, C_inf w ^ w.mult) *
          (∏ w : NumberField.InfinitePlace K, max (w x) 1 ^ w.mult) ^ 2 := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod
        (fun w _ => mul_nonneg (pow_nonneg (le_trans zero_le_one (le_max_right _ _)) _)
          (pow_nonneg (apply_nonneg w D) _))
        (fun w _ => hw_step w)
    have hv_step (v : NumberField.FinitePlace K) :
        max (v (N / D)) 1 * v D ≤ C_fin v * max (v x) 1 ^ 2 := by
      have h1 : max (v (N / D)) 1 * v D = max (v N) (v D) := by
        rw [mul_comm, mul_max_of_nonneg _ _ (apply_nonneg v D), mul_comm (v D),
          ← map_mul, div_mul_cancel₀ _ hD, mul_one]
      exact h1.trans_le (h_fin v)
    have h_max_supp (z : K) :
        (Function.mulSupport fun v : NumberField.FinitePlace K => max (v z) 1).Finite := by
      by_cases hz : z = 0
      · convert Set.finite_empty
        ext v
        simp [hz]
      · refine (NumberField.FinitePlace.mulSupport_finite hz).subset (fun v hv => ?_)
        simp only [Function.mem_mulSupport] at hv ⊢
        intro hvz
        exact hv (by rw [hvz, max_self])
    have hf1 := h_max_supp (N / D)
    have hf2 := NumberField.FinitePlace.mulSupport_finite hD
    have hg2 := h_max_supp x
    have hS_fin := ((hf1.union hf2).union hC_fin_supp).union hg2
    let S : Finset (NumberField.FinitePlace K) := hS_fin.toFinset
    have h_fin1 : (∏ᶠ v : NumberField.FinitePlace K, max (v (N / D)) 1) =
        ∏ v ∈ S, max (v (N / D)) 1 := by
      refine finprod_eq_prod_of_mulSupport_subset _ (fun v hv => ?_)
      rw [Set.Finite.coe_toFinset]
      exact Or.inl (Or.inl (Or.inl hv))
    have h_fin2 : (∏ᶠ v : NumberField.FinitePlace K, v D) = ∏ v ∈ S, v D := by
      refine finprod_eq_prod_of_mulSupport_subset _ (fun v hv => ?_)
      rw [Set.Finite.coe_toFinset]
      exact Or.inl (Or.inl (Or.inr hv))
    have h_fin3 : (∏ᶠ v : NumberField.FinitePlace K, C_fin v) = ∏ v ∈ S, C_fin v := by
      refine finprod_eq_prod_of_mulSupport_subset _ (fun v hv => ?_)
      rw [Set.Finite.coe_toFinset]
      exact Or.inl (Or.inr hv)
    have h_fin4 : (∏ᶠ v : NumberField.FinitePlace K, max (v x) 1) = ∏ v ∈ S, max (v x) 1 := by
      refine finprod_eq_prod_of_mulSupport_subset _ (fun v hv => ?_)
      rw [Set.Finite.coe_toFinset]
      exact Or.inr hv
    have h_nonarch_prod :
        (∏ᶠ v : NumberField.FinitePlace K, max (v (N / D)) 1) *
          (∏ᶠ v : NumberField.FinitePlace K, v D) ≤
        (∏ᶠ v : NumberField.FinitePlace K, C_fin v) *
          (∏ᶠ v : NumberField.FinitePlace K, max (v x) 1) ^ 2 := by
      rw [h_fin1, h_fin2, h_fin3, h_fin4, ← Finset.prod_mul_distrib, ← Finset.prod_pow,
        ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod
        (fun v _ => mul_nonneg (le_trans zero_le_one (le_max_right _ _)) (apply_nonneg v D))
        (fun v _ => hv_step v)
    set A_ND := ∏ w : NumberField.InfinitePlace K, max (w (N / D)) 1 ^ w.mult
    set F_ND := ∏ᶠ v : NumberField.FinitePlace K, max (v (N / D)) 1
    set A_D := ∏ w : NumberField.InfinitePlace K, w D ^ w.mult
    set F_D := ∏ᶠ v : NumberField.FinitePlace K, v D
    set A_C := ∏ w : NumberField.InfinitePlace K, C_inf w ^ w.mult
    set F_C := ∏ᶠ v : NumberField.FinitePlace K, C_fin v
    set A_x := ∏ w : NumberField.InfinitePlace K, max (w x) 1 ^ w.mult
    set F_x := ∏ᶠ v : NumberField.FinitePlace K, max (v x) 1
    have hA_ND : 1 ≤ A_ND := Finset.prod_const_one.symm.trans_le
      (Finset.prod_le_prod (fun _ _ => zero_le_one) (fun _ _ => one_le_pow₀ (le_max_right _ _)))
    have hF_ND : 1 ≤ F_ND := by
      rw [h_fin1]
      exact Finset.prod_const_one.symm.trans_le
        (Finset.prod_le_prod (fun _ _ => zero_le_one) (fun _ _ => le_max_right _ _))
    have hA_C : 1 ≤ A_C := Finset.prod_const_one.symm.trans_le
      (Finset.prod_le_prod (fun _ _ => zero_le_one) (fun w _ => one_le_pow₀ (hC_inf w)))
    have hF_C : 1 ≤ F_C := by
      rw [h_fin3]
      exact Finset.prod_const_one.symm.trans_le
        (Finset.prod_le_prod (fun _ _ => zero_le_one) (fun v _ => hC_fin v))
    have hA_x : 1 ≤ A_x := Finset.prod_const_one.symm.trans_le
      (Finset.prod_le_prod (fun _ _ => zero_le_one) (fun _ _ => one_le_pow₀ (le_max_right _ _)))
    have hF_x : 1 ≤ F_x := by
      rw [h_fin4]
      exact Finset.prod_const_one.symm.trans_le
        (Finset.prod_le_prod (fun _ _ => zero_le_one) (fun _ _ => le_max_right _ _))
    have hF_D : 0 ≤ F_D := by
      rw [h_fin2]
      exact Finset.prod_nonneg (fun v _ => apply_nonneg v D)
    have h_prod_D : A_D * F_D = 1 := NumberField.prod_abs_eq_one hD
    have h_glob : A_ND * F_ND ≤ (A_C * F_C) * (A_x * F_x) ^ 2 := by
      calc A_ND * F_ND = (A_ND * F_ND) * (A_D * F_D) := by rw [h_prod_D, mul_one]
        _ = (A_ND * A_D) * (F_ND * F_D) := by ring
        _ ≤ (A_C * A_x ^ 2) * (F_C * F_x ^ 2) :=
          mul_le_mul h_arch_prod h_nonarch_prod
            (mul_nonneg (by linarith) hF_D)
            (mul_nonneg (by linarith) (sq_nonneg A_x))
        _ = (A_C * F_C) * (A_x * F_x) ^ 2 := by ring
    unfold fieldLogHeight
    change Real.log (A_ND * F_ND) ≤ 2 * Real.log (A_x * F_x) + Real.log (A_C * F_C)
    have h_log : Real.log (A_ND * F_ND) ≤ Real.log ((A_C * F_C) * (A_x * F_x) ^ 2) :=
      Real.log_le_log (by positivity) h_glob
    have h_rhs : Real.log ((A_C * F_C) * (A_x * F_x) ^ 2) =
        Real.log (A_C * F_C) + 2 * Real.log (A_x * F_x) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
      ring
    linarith
  have h_log_nonneg (x : K) : 0 ≤ fieldLogHeight x := by
    have h_eq : fieldLogHeight x = Height.logHeight₁ x := by
      rw [Height.logHeight₁_eq_log_mulHeight₁, NumberField.mulHeight₁_eq]
      rfl
    rw [h_eq]
    exact Height.zero_le_logHeight₁ x
  have h_nonneg (P : E.toAffine.Point) : 0 ≤ weierstrassHeight E P := by
    rcases P with _ | @⟨x, y, hP⟩
    · exact le_refl 0
    · exact h_log_nonneg x
  rcases Q with _ | @⟨x₀, y₀, hQ⟩
  · refine ⟨0, fun P => ?_⟩
    have hQ0 : (WeierstrassCurve.Affine.Point.zero : E.toAffine.Point) = 0 :=
      WeierstrassCurve.Affine.Point.zero_def.symm
    rw [hQ0, add_zero]
    linarith [h_nonneg P]
  · let C_inf : NumberField.InfinitePlace K → ℝ := fun w => 8 * curvePlaceConst E x₀ y₀ w ^ 2
    let C_fin : NumberField.FinitePlace K → ℝ := fun v => curvePlaceConst E x₀ y₀ v ^ 2
    let C_Q : ℝ := Real.log ((∏ w : NumberField.InfinitePlace K, C_inf w ^ w.mult) *
      (∏ᶠ v : NumberField.FinitePlace K, C_fin v))
    let Q_pt : E.toAffine.Point := WeierstrassCurve.Affine.Point.some hQ
    refine ⟨max C_Q (max (weierstrassHeight E Q_pt) (max (weierstrassHeight E (Q_pt + Q_pt)) 0)),
      fun P => ?_⟩
    have hC1_CQ : C_Q ≤ max C_Q (max (weierstrassHeight E Q_pt) (max (weierstrassHeight E (Q_pt + Q_pt)) 0)) :=
      le_max_left _ _
    have hC1_sub1 := le_max_right C_Q (max (weierstrassHeight E Q_pt) (max (weierstrassHeight E (Q_pt + Q_pt)) 0))
    have hC1_Q : weierstrassHeight E Q_pt ≤
        max C_Q (max (weierstrassHeight E Q_pt) (max (weierstrassHeight E (Q_pt + Q_pt)) 0)) :=
      le_trans (le_max_left _ _) hC1_sub1
    have hC1_sub2 := le_trans (le_max_right _ _) hC1_sub1
    have hC1_2Q : weierstrassHeight E (Q_pt + Q_pt) ≤
        max C_Q (max (weierstrassHeight E Q_pt) (max (weierstrassHeight E (Q_pt + Q_pt)) 0)) :=
      le_trans (le_max_left _ _) hC1_sub2
    have hC1_0 : 0 ≤ max C_Q (max (weierstrassHeight E Q_pt) (max (weierstrassHeight E (Q_pt + Q_pt)) 0)) :=
      le_trans (le_max_right _ _) hC1_sub2
    rcases P with _ | @⟨x, y, hP⟩
    · have hP0 : (WeierstrassCurve.Affine.Point.zero : E.toAffine.Point) = 0 :=
        WeierstrassCurve.Affine.Point.zero_def.symm
      have hadd : WeierstrassCurve.Affine.Point.zero + Q_pt = Q_pt := by
        rw [hP0, zero_add]
      change weierstrassHeight E (WeierstrassCurve.Affine.Point.zero + Q_pt) ≤
        2 * weierstrassHeight E WeierstrassCurve.Affine.Point.zero + _
      rw [hadd]
      change weierstrassHeight E Q_pt ≤ 2 * 0 + _
      linarith
    · by_cases hx : x = x₀
      · by_cases hy : y = E.toAffine.negY x₀ y₀
        · have hadd : WeierstrassCurve.Affine.Point.some hP + Q_pt = 0 :=
            WeierstrassCurve.Affine.Point.add_of_Y_eq hx hy
          have hP_nonneg := h_nonneg (WeierstrassCurve.Affine.Point.some hP)
          change weierstrassHeight E (WeierstrassCurve.Affine.Point.some hP + Q_pt) ≤
            2 * weierstrassHeight E (WeierstrassCurve.Affine.Point.some hP) + _
          rw [hadd, WeierstrassCurve.Affine.Point.zero_def]
          change 0 ≤ 2 * weierstrassHeight E (WeierstrassCurve.Affine.Point.some hP) + _
          linarith
        · have hy_eq : y = y₀ := WeierstrassCurve.Affine.Y_eq_of_Y_ne hP.1 hQ.1 hx hy
          subst hx
          subst hy_eq
          have hPQ : WeierstrassCurve.Affine.Point.some hP = Q_pt := rfl
          have hQ_nonneg := h_nonneg Q_pt
          change weierstrassHeight E (WeierstrassCurve.Affine.Point.some hP + Q_pt) ≤
            2 * weierstrassHeight E (WeierstrassCurve.Affine.Point.some hP) + _
          rw [hPQ]
          linarith
      · change weierstrassHeight E (WeierstrassCurve.Affine.Point.some hP + WeierstrassCurve.Affine.Point.some hQ) ≤
          2 * fieldLogHeight x + _
        rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
        change fieldLogHeight (E.toAffine.addX x x₀ (E.toAffine.slope x x₀ y y₀)) ≤
          2 * fieldLogHeight x + _
        rw [h_chord_eq hP.1 hx]
        have hD : chordDen x₀ x ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hx)
        have h_nonarch_Q := h_nonarch x₀ y₀
        have h_div := h_div_bound C_inf C_fin
          (fun w => (h_arch x₀ y₀ hP.1 w).1)
          h_nonarch_Q.2.1
          h_nonarch_Q.1
          x (chordNum E x₀ y₀ x y) (chordDen x₀ x) hD
          (fun w => (h_arch x₀ y₀ hP.1 w).2)
          (fun v => h_nonarch_Q.2.2 hP.1 v)
        linarith

theorem height_double_bound {K : Type u} [Field K] [NumberField K] [DecidableEq K]
    (E : WeierstrassCurve K) (hE : E.IsElliptic) :
    ∃ C₂ : ℝ, ∀ P : E.toAffine.Point, 4 * weierstrassHeight E P ≤ weierstrassHeight E (P + P) + C₂ :=
by
  have fieldLogHeight_zero : fieldLogHeight (0 : K) = 0 := by
    simp [fieldLogHeight]
  have weierstrassHeight_double_eq : ∀ {x y : K} (h : E.toAffine.Nonsingular x y),
      weierstrassHeight E (WeierstrassCurve.Affine.Point.some h + WeierstrassCurve.Affine.Point.some h) =
        fieldLogHeight (phi2 E x / psi2Sq E x) := by
    intro x y h
    have heq : y ^ 2 + E.a₁ * x * y + E.a₃ * y = x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆ :=
      (WeierstrassCurve.Affine.equation_iff x y).mp h.1
    have hpsi : (y - E.toAffine.negY x y) ^ 2 = psi2Sq E x := by
      dsimp [WeierstrassCurve.Affine.negY, psi2Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆]
      linear_combination 4 * heq
    by_cases hy : y = E.toAffine.negY x y
    · rw [WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy]
      have hD0 : y - E.toAffine.negY x y = 0 := sub_eq_zero.mpr hy
      have hpsi0 : psi2Sq E x = 0 := by
        rw [← hpsi, hD0, sq, mul_zero]
      rw [hpsi0, div_zero, fieldLogHeight_zero]
      rfl
    · rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
      dsimp [weierstrassHeight]
      congr 1
      rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
      have hD : y - E.toAffine.negY x y ≠ 0 := sub_ne_zero.mpr hy
      have hD2 : (y - E.toAffine.negY x y) ^ 2 ≠ 0 := pow_ne_zero 2 hD
      rw [← hpsi, eq_div_iff hD2]
      have hnum : (3 * x ^ 2 + 2 * E.a₂ * x + E.a₄ - E.a₁ * y) ^ 2 +
          E.a₁ * (3 * x ^ 2 + 2 * E.a₂ * x + E.a₄ - E.a₁ * y) * (y - E.toAffine.negY x y) -
          (E.a₂ + 2 * x) * (y - E.toAffine.negY x y) ^ 2 = phi2 E x := by
        dsimp [WeierstrassCurve.Affine.negY, phi2, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
          WeierstrassCurve.b₆, WeierstrassCurve.b₈]
        linear_combination -(E.a₁ ^ 2 + 4 * E.a₂ + 8 * x) * heq
      rw [← hnum]
      change (((3 * x ^ 2 + 2 * E.a₂ * x + E.a₄ - E.a₁ * y) / (y - E.toAffine.negY x y)) ^ 2 +
          E.a₁ * ((3 * x ^ 2 + 2 * E.a₂ * x + E.a₄ - E.a₁ * y) / (y - E.toAffine.negY x y)) -
          E.a₂ - x - x) * (y - E.toAffine.negY x y) ^ 2 = _
      generalize y - E.toAffine.negY x y = D at hD ⊢
      field_simp [hD]
      ring
  have le_mul_r : ∀ {x a b : ℝ}, x ≤ a → 1 ≤ b → 0 ≤ a → x ≤ a * b :=
    fun hxa hb ha => hxa.trans (le_mul_of_one_le_right ha hb)
  have le_mul_l : ∀ {x a b : ℝ}, x ≤ b → 1 ≤ a → 0 ≤ b → x ≤ a * b :=
    fun hxb ha hb => hxb.trans (le_mul_of_one_le_left hb ha)
  have deg3Bound_ge : ∀ (u : K → ℝ) (c3 c2 c1 c0 : K),
      1 ≤ deg3Bound u c3 c2 c1 c0 ∧
      u c3 ≤ deg3Bound u c3 c2 c1 c0 ∧
      u c2 ≤ deg3Bound u c3 c2 c1 c0 ∧
      u c1 ≤ deg3Bound u c3 c2 c1 c0 ∧
      u c0 ≤ deg3Bound u c3 c2 c1 c0 := by
    intro u c3 c2 c1 c0
    have m3 : 1 ≤ max (u c3) 1 := le_max_right _ _
    have m2 : 1 ≤ max (u c2) 1 := le_max_right _ _
    have m1 : 1 ≤ max (u c1) 1 := le_max_right _ _
    have m0 : 1 ≤ max (u c0) 1 := le_max_right _ _
    have p12 : 1 ≤ max (u c3) 1 * max (u c2) 1 := one_le_mul_of_one_le_of_one_le m3 m2
    have p123 : 1 ≤ max (u c3) 1 * max (u c2) 1 * max (u c1) 1 :=
      one_le_mul_of_one_le_of_one_le p12 m1
    have p1234 : 1 ≤ deg3Bound u c3 c2 c1 c0 :=
      one_le_mul_of_one_le_of_one_le p123 m0
    have hc3 : u c3 ≤ deg3Bound u c3 c2 c1 c0 :=
      le_mul_r (le_mul_r (le_mul_r (le_max_left _ _) m2 (by linarith)) m1 (by linarith)) m0 (by linarith)
    have hc2 : u c2 ≤ deg3Bound u c3 c2 c1 c0 :=
      le_mul_r (le_mul_r (le_mul_l (le_max_left _ _) m3 (by linarith)) m1 (by linarith)) m0 (by linarith)
    have hc1 : u c1 ≤ deg3Bound u c3 c2 c1 c0 :=
      le_mul_r (le_mul_l (le_max_left _ _) p12 (by linarith)) m0 (by linarith)
    have hc0 : u c0 ≤ deg3Bound u c3 c2 c1 c0 :=
      le_mul_l (le_max_left _ _) p123 (by linarith)
    exact ⟨p1234, hc3, hc2, hc1, hc0⟩
  have doublePlaceBound_ge : ∀ (u : K → ℝ),
      let B0u := deg3Bound u 0 (-48) (-8 * E.b₂) (E.b₂ ^ 2 - 32 * E.b₄)
      let B0v := deg3Bound u 12 (-E.b₂) (-10 * E.b₄) (E.b₂ * E.b₄ - 27 * E.b₆)
      let B7u := deg3Bound u (u7c3 E) (u7c2 E) (u7c1 E) (u7c0 E)
      let B7v := deg3Bound u (v7c3 E) (v7c2 E) (v7c1 E) (v7c0 E)
      1 ≤ doublePlaceBound E u ∧
      u E.Δ⁻¹ * B0u ≤ doublePlaceBound E u ∧
      u E.Δ⁻¹ * B0v ≤ doublePlaceBound E u ∧
      u E.Δ⁻¹ * B7u ≤ doublePlaceBound E u ∧
      u E.Δ⁻¹ * B7v ≤ doublePlaceBound E u := by
    intro u B0u B0v B7u B7v
    have hd1 : 1 ≤ max (u E.Δ⁻¹) 1 := le_max_right _ _
    have hdl : u E.Δ⁻¹ ≤ max (u E.Δ⁻¹) 1 := le_max_left _ _
    have h0u : 1 ≤ B0u := (deg3Bound_ge u _ _ _ _).1
    have h0v : 1 ≤ B0v := (deg3Bound_ge u _ _ _ _).1
    have h7u : 1 ≤ B7u := (deg3Bound_ge u _ _ _ _).1
    have h7v : 1 ≤ B7v := (deg3Bound_ge u _ _ _ _).1
    have p1 : 1 ≤ max (u E.Δ⁻¹) 1 * B0u := one_le_mul_of_one_le_of_one_le hd1 h0u
    have p2 : 1 ≤ max (u E.Δ⁻¹) 1 * B0u * B0v := one_le_mul_of_one_le_of_one_le p1 h0v
    have p3 : 1 ≤ max (u E.Δ⁻¹) 1 * B0u * B0v * B7u := one_le_mul_of_one_le_of_one_le p2 h7u
    have p4 : 1 ≤ doublePlaceBound E u := one_le_mul_of_one_le_of_one_le p3 h7v
    have q0u : u E.Δ⁻¹ * B0u ≤ doublePlaceBound E u :=
      le_mul_r (le_mul_r (le_mul_r (mul_le_mul_of_nonneg_right hdl (by linarith)) h0v (by linarith)) h7u (by linarith)) h7v (by linarith)
    have hdl1 : u E.Δ⁻¹ ≤ max (u E.Δ⁻¹) 1 * B0u := le_mul_r hdl h0u (by linarith)
    have q0v : u E.Δ⁻¹ * B0v ≤ doublePlaceBound E u :=
      le_mul_r (le_mul_r (mul_le_mul_of_nonneg_right hdl1 (by linarith)) h7u (by linarith)) h7v (by linarith)
    have hdl2 : u E.Δ⁻¹ ≤ max (u E.Δ⁻¹) 1 * B0u * B0v := le_mul_r hdl1 h0v (by linarith)
    have q7u : u E.Δ⁻¹ * B7u ≤ doublePlaceBound E u :=
      le_mul_r (mul_le_mul_of_nonneg_right hdl2 (by linarith)) h7v (by linarith)
    have hdl3 : u E.Δ⁻¹ ≤ max (u E.Δ⁻¹) 1 * B0u * B0v * B7u := le_mul_r hdl2 h7u (by linarith)
    have q7v : u E.Δ⁻¹ * B7v ≤ doublePlaceBound E u :=
      mul_le_mul_of_nonneg_right hdl3 (by linarith)
    exact ⟨p4, q0u, q0v, q7u, q7v⟩
  have x_pow_bounds : ∀ {vx : ℝ}, 0 ≤ vx →
      let M := max vx 1
      0 < M ^ 3 ∧ 1 ≤ M ^ 3 ∧ vx ≤ M ^ 3 ∧ vx ^ 2 ≤ M ^ 3 ∧ vx ^ 3 ≤ M ^ 3 := by
    intro vx hx0 M
    have hM1 : 1 ≤ M := le_max_right _ _
    have hxM : vx ≤ M := le_max_left _ _
    have hM3_1 : 1 ≤ M ^ 3 := one_le_pow₀ hM1
    have hM13 : M ≤ M ^ 3 := by
      simpa using pow_le_pow_right₀ hM1 (by decide : 1 ≤ 3)
    have hM23 : M ^ 2 ≤ M ^ 3 := pow_le_pow_right₀ hM1 (by decide : 2 ≤ 3)
    refine ⟨by linarith, hM3_1, hxM.trans hM13, (pow_le_pow_left₀ hx0 hxM 2).trans hM23,
      pow_le_pow_left₀ hx0 hxM 3⟩
  have inf_deg3Eval_le : ∀ (w : NumberField.InfinitePlace K) (c3 c2 c1 c0 x : K),
      w (deg3Eval c3 c2 c1 c0 x) ≤ 4 * deg3Bound w c3 c2 c1 c0 * max (w x) 1 ^ 3 := by
    intro w c3 c2 c1 c0 x
    obtain ⟨h1B, hc3, hc2, hc1, hc0⟩ := deg3Bound_ge w c3 c2 c1 c0
    obtain ⟨hM3_pos, h1M3, hx1, hx2, hx3⟩ := x_pow_bounds (apply_nonneg w x)
    set B := deg3Bound w c3 c2 c1 c0
    set M := max (w x) 1
    have ht3 : w (c3 * x ^ 3) ≤ B * M ^ 3 := by
      rw [map_mul, map_pow]
      exact mul_le_mul hc3 hx3 (by positivity) (by linarith)
    have ht2 : w (c2 * x ^ 2) ≤ B * M ^ 3 := by
      rw [map_mul, map_pow]
      exact mul_le_mul hc2 hx2 (by positivity) (by linarith)
    have ht1 : w (c1 * x) ≤ B * M ^ 3 := by
      rw [map_mul]
      exact mul_le_mul hc1 hx1 (apply_nonneg w x) (by linarith)
    have ht0 : w c0 ≤ B * M ^ 3 := le_mul_r hc0 h1M3 (by linarith)
    have ha1 : w (c3 * x ^ 3 + c2 * x ^ 2) ≤ w (c3 * x ^ 3) + w (c2 * x ^ 2) := w.1.add_le _ _
    have ha2 : w (c3 * x ^ 3 + c2 * x ^ 2 + c1 * x) ≤ w (c3 * x ^ 3 + c2 * x ^ 2) + w (c1 * x) :=
      w.1.add_le _ _
    have ha3 : w (deg3Eval c3 c2 c1 c0 x) ≤ w (c3 * x ^ 3 + c2 * x ^ 2 + c1 * x) + w c0 :=
      w.1.add_le _ _
    linarith
  have fin_deg3Eval_le : ∀ (v : NumberField.FinitePlace K) (c3 c2 c1 c0 x : K),
      v (deg3Eval c3 c2 c1 c0 x) ≤ deg3Bound v c3 c2 c1 c0 * max (v x) 1 ^ 3 := by
    intro v c3 c2 c1 c0 x
    obtain ⟨h1B, hc3, hc2, hc1, hc0⟩ := deg3Bound_ge v c3 c2 c1 c0
    obtain ⟨hM3_pos, h1M3, hx1, hx2, hx3⟩ := x_pow_bounds (apply_nonneg v x)
    set B := deg3Bound v c3 c2 c1 c0
    set M := max (v x) 1
    have ht3 : v (c3 * x ^ 3) ≤ B * M ^ 3 := by
      rw [map_mul, map_pow]
      exact mul_le_mul hc3 hx3 (by positivity) (by linarith)
    have ht2 : v (c2 * x ^ 2) ≤ B * M ^ 3 := by
      rw [map_mul, map_pow]
      exact mul_le_mul hc2 hx2 (by positivity) (by linarith)
    have ht1 : v (c1 * x) ≤ B * M ^ 3 := by
      rw [map_mul]
      exact mul_le_mul hc1 hx1 (apply_nonneg v x) (by linarith)
    have ht0 : v c0 ≤ B * M ^ 3 := le_mul_r hc0 h1M3 (by linarith)
    dsimp [deg3Eval]
    exact (v.add_le _ _).trans (max_le
      ((v.add_le _ _).trans (max_le
        ((v.add_le _ _).trans (max_le ht3 ht2)) ht1)) ht0)
  have hb8 : 4 * E.b₈ = E.b₂ * E.b₆ - E.b₄ ^ 2 := by
    dsimp [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  have bezout_id_0 : ∀ (x : K),
      deg3Eval 0 (-48) (-8 * E.b₂) (E.b₂ ^ 2 - 32 * E.b₄) x * phi2 E x +
      deg3Eval 12 (-E.b₂) (-10 * E.b₄) (E.b₂ * E.b₄ - 27 * E.b₆) x * psi2Sq E x = E.Δ := by
    intro x
    dsimp [deg3Eval, phi2, psi2Sq, WeierstrassCurve.Δ]
    linear_combination (12 * x ^ 2 + 2 * E.b₂ * x + 8 * E.b₄) * hb8
  have bezout_id_7 : ∀ (x : K),
      deg3Eval (u7c3 E) (u7c2 E) (u7c1 E) (u7c0 E) x * phi2 E x +
      deg3Eval (v7c3 E) (v7c2 E) (v7c1 E) (v7c0 E) x * psi2Sq E x = E.Δ * x ^ 7 := by
    intro x
    dsimp [deg3Eval, u7c3, u7c2, u7c1, u7c0, v7c3, v7c2, v7c1, v7c0, phi2, psi2Sq,
      WeierstrassCurve.Δ]
    linear_combination (8 * E.b₄ * x ^ 7 + 6 * E.b₆ * x ^ 6 + 4 * E.b₈ * x ^ 5) * hb8
  have hΔ : E.Δ ≠ 0 := ((WeierstrassCurve.isElliptic_iff E).mp hE).ne_zero
  have double_local_infinite_bound : ∀ (w : NumberField.InfinitePlace K) (x : K),
      max (w x) 1 ^ 4 ≤ 8 * doublePlaceBound E w * max (w (phi2 E x)) (w (psi2Sq E x)) := by
    intro w x
    obtain ⟨hB1, hB0u, hB0v, hB7u, hB7v⟩ := doublePlaceBound_ge w
    set M := max (w x) 1
    obtain ⟨hM3_pos, _, _, _, _⟩ := x_pow_bounds (apply_nonneg w x)
    set K_pp := max (w (phi2 E x)) (w (psi2Sq E x))
    have hK0 : 0 ≤ K_pp := le_trans (apply_nonneg w _) (le_max_left _ _)
    have hphi : w (phi2 E x) ≤ K_pp := le_max_left _ _
    have hpsi : w (psi2Sq E x) ≤ K_pp := le_max_right _ _
    have h_comb : ∀ (u3 u2 u1 u0 v3 v2 v1 v0 : K),
        w E.Δ⁻¹ * deg3Bound w u3 u2 u1 u0 ≤ doublePlaceBound E w →
        w E.Δ⁻¹ * deg3Bound w v3 v2 v1 v0 ≤ doublePlaceBound E w →
        w (E.Δ⁻¹ * (deg3Eval u3 u2 u1 u0 x * phi2 E x + deg3Eval v3 v2 v1 v0 x * psi2Sq E x)) ≤
          8 * doublePlaceBound E w * K_pp * M ^ 3 := by
      intro u3 u2 u1 u0 v3 v2 v1 v0 hu hv
      rw [map_mul]
      have h_add : w (deg3Eval u3 u2 u1 u0 x * phi2 E x + deg3Eval v3 v2 v1 v0 x * psi2Sq E x) ≤
          w (deg3Eval u3 u2 u1 u0 x * phi2 E x) + w (deg3Eval v3 v2 v1 v0 x * psi2Sq E x) :=
        w.1.add_le _ _
      rw [map_mul, map_mul] at h_add
      have hu_eval := inf_deg3Eval_le w u3 u2 u1 u0 x
      have hv_eval := inf_deg3Eval_le w v3 v2 v1 v0 x
      have ⟨hBu1, _, _, _, _⟩ := deg3Bound_ge w u3 u2 u1 u0
      have ⟨hBv1, _, _, _, _⟩ := deg3Bound_ge w v3 v2 v1 v0
      have h_u_term : w (deg3Eval u3 u2 u1 u0 x) * w (phi2 E x) ≤
          4 * deg3Bound w u3 u2 u1 u0 * M ^ 3 * K_pp :=
        mul_le_mul hu_eval hphi (apply_nonneg w _) (by positivity)
      have h_v_term : w (deg3Eval v3 v2 v1 v0 x) * w (psi2Sq E x) ≤
          4 * deg3Bound w v3 v2 v1 v0 * M ^ 3 * K_pp :=
        mul_le_mul hv_eval hpsi (apply_nonneg w _) (by positivity)
      have h_sum_le : w (deg3Eval u3 u2 u1 u0 x * phi2 E x + deg3Eval v3 v2 v1 v0 x * psi2Sq E x) ≤
          4 * (deg3Bound w u3 u2 u1 u0 + deg3Bound w v3 v2 v1 v0) * (M ^ 3 * K_pp) := by
        linarith
      have h_mul_d := mul_le_mul_of_nonneg_left h_sum_le (apply_nonneg w E.Δ⁻¹)
      have h_d_sum : w E.Δ⁻¹ * (4 * (deg3Bound w u3 u2 u1 u0 + deg3Bound w v3 v2 v1 v0)) ≤
          8 * doublePlaceBound E w := by linarith
      have h_rhs := mul_le_mul_of_nonneg_right h_d_sum (by positivity : 0 ≤ M ^ 3 * K_pp)
      linarith
    have h_id0 : 1 = E.Δ⁻¹ * (deg3Eval 0 (-48) (-8 * E.b₂) (E.b₂ ^ 2 - 32 * E.b₄) x * phi2 E x +
        deg3Eval 12 (-E.b₂) (-10 * E.b₄) (E.b₂ * E.b₄ - 27 * E.b₆) x * psi2Sq E x) := by
      rw [bezout_id_0 x, inv_mul_cancel₀ hΔ]
    have h_id7 : x ^ 7 = E.Δ⁻¹ * (deg3Eval (u7c3 E) (u7c2 E) (u7c1 E) (u7c0 E) x * phi2 E x +
        deg3Eval (v7c3 E) (v7c2 E) (v7c1 E) (v7c0 E) x * psi2Sq E x) := by
      rw [bezout_id_7 x, ← mul_assoc, inv_mul_cancel₀ hΔ, one_mul]
    have h1_le : 1 ≤ 8 * doublePlaceBound E w * K_pp * M ^ 3 := by
      have := h_comb 0 (-48) (-8 * E.b₂) (E.b₂ ^ 2 - 32 * E.b₄)
        12 (-E.b₂) (-10 * E.b₄) (E.b₂ * E.b₄ - 27 * E.b₆) hB0u hB0v
      rwa [← h_id0, map_one] at this
    have hx7_le : w x ^ 7 ≤ 8 * doublePlaceBound E w * K_pp * M ^ 3 := by
      have := h_comb (u7c3 E) (u7c2 E) (u7c1 E) (u7c0 E)
        (v7c3 E) (v7c2 E) (v7c1 E) (v7c0 E) hB7u hB7v
      rwa [← h_id7, map_pow] at this
    have hM7_eq : M ^ 7 = max (w x ^ 7) 1 := by
      dsimp [M]
      rcases le_total (w x) 1 with hle | hge
      · rw [max_eq_right hle, one_pow, max_eq_right (pow_le_one₀ (apply_nonneg w x) hle)]
      · rw [max_eq_left hge, max_eq_left (one_le_pow₀ hge)]
    have hM7_le : M ^ 4 * M ^ 3 ≤ 8 * doublePlaceBound E w * K_pp * M ^ 3 := by
      calc M ^ 4 * M ^ 3 = M ^ 7 := by ring
        _ = max (w x ^ 7) 1 := hM7_eq
        _ ≤ 8 * doublePlaceBound E w * K_pp * M ^ 3 := max_le hx7_le h1_le
    exact le_of_mul_le_mul_right hM7_le hM3_pos
  have double_local_finite_bound : ∀ (v : NumberField.FinitePlace K) (x : K),
      max (v x) 1 ^ 4 ≤ doublePlaceBound E v * max (v (phi2 E x)) (v (psi2Sq E x)) := by
    intro v x
    obtain ⟨hB1, hB0u, hB0v, hB7u, hB7v⟩ := doublePlaceBound_ge v
    set M := max (v x) 1
    obtain ⟨hM3_pos, _, _, _, _⟩ := x_pow_bounds (apply_nonneg v x)
    set K_pp := max (v (phi2 E x)) (v (psi2Sq E x))
    have hK0 : 0 ≤ K_pp := le_trans (apply_nonneg v _) (le_max_left _ _)
    have hphi : v (phi2 E x) ≤ K_pp := le_max_left _ _
    have hpsi : v (psi2Sq E x) ≤ K_pp := le_max_right _ _
    have h_comb : ∀ (u3 u2 u1 u0 v3 v2 v1 v0 : K),
        v E.Δ⁻¹ * deg3Bound v u3 u2 u1 u0 ≤ doublePlaceBound E v →
        v E.Δ⁻¹ * deg3Bound v v3 v2 v1 v0 ≤ doublePlaceBound E v →
        v (E.Δ⁻¹ * (deg3Eval u3 u2 u1 u0 x * phi2 E x + deg3Eval v3 v2 v1 v0 x * psi2Sq E x)) ≤
          doublePlaceBound E v * K_pp * M ^ 3 := by
      intro u3 u2 u1 u0 v3 v2 v1 v0 hu hv
      rw [map_mul]
      have h_add := v.add_le (deg3Eval u3 u2 u1 u0 x * phi2 E x) (deg3Eval v3 v2 v1 v0 x * psi2Sq E x)
      rw [map_mul, map_mul] at h_add
      have hu_eval := fin_deg3Eval_le v u3 u2 u1 u0 x
      have hv_eval := fin_deg3Eval_le v v3 v2 v1 v0 x
      have ⟨hBu1, _, _, _, _⟩ := deg3Bound_ge v u3 u2 u1 u0
      have ⟨hBv1, _, _, _, _⟩ := deg3Bound_ge v v3 v2 v1 v0
      have h_u_term : v (deg3Eval u3 u2 u1 u0 x) * v (phi2 E x) ≤
          deg3Bound v u3 u2 u1 u0 * M ^ 3 * K_pp :=
        mul_le_mul hu_eval hphi (apply_nonneg v _) (by positivity)
      have h_v_term : v (deg3Eval v3 v2 v1 v0 x) * v (psi2Sq E x) ≤
          deg3Bound v v3 v2 v1 v0 * M ^ 3 * K_pp :=
        mul_le_mul hv_eval hpsi (apply_nonneg v _) (by positivity)
      have h_max : v (deg3Eval u3 u2 u1 u0 x * phi2 E x + deg3Eval v3 v2 v1 v0 x * psi2Sq E x) ≤
          max (deg3Bound v u3 u2 u1 u0 * M ^ 3 * K_pp) (deg3Bound v v3 v2 v1 v0 * M ^ 3 * K_pp) :=
        h_add.trans (max_le_max h_u_term h_v_term)
      have h_mul_d := mul_le_mul_of_nonneg_left h_max (apply_nonneg v E.Δ⁻¹)
      rcases le_total (deg3Bound v u3 u2 u1 u0 * M ^ 3 * K_pp)
        (deg3Bound v v3 v2 v1 v0 * M ^ 3 * K_pp) with hle | hge
      · rw [max_eq_right hle] at h_mul_d
        have h_rhs := mul_le_mul_of_nonneg_right hv (by positivity : 0 ≤ M ^ 3 * K_pp)
        linarith
      · rw [max_eq_left hge] at h_mul_d
        have h_rhs := mul_le_mul_of_nonneg_right hu (by positivity : 0 ≤ M ^ 3 * K_pp)
        linarith
    have h_id0 : 1 = E.Δ⁻¹ * (deg3Eval 0 (-48) (-8 * E.b₂) (E.b₂ ^ 2 - 32 * E.b₄) x * phi2 E x +
        deg3Eval 12 (-E.b₂) (-10 * E.b₄) (E.b₂ * E.b₄ - 27 * E.b₆) x * psi2Sq E x) := by
      rw [bezout_id_0 x, inv_mul_cancel₀ hΔ]
    have h_id7 : x ^ 7 = E.Δ⁻¹ * (deg3Eval (u7c3 E) (u7c2 E) (u7c1 E) (u7c0 E) x * phi2 E x +
        deg3Eval (v7c3 E) (v7c2 E) (v7c1 E) (v7c0 E) x * psi2Sq E x) := by
      rw [bezout_id_7 x, ← mul_assoc, inv_mul_cancel₀ hΔ, one_mul]
    have h1_le : 1 ≤ doublePlaceBound E v * K_pp * M ^ 3 := by
      have := h_comb 0 (-48) (-8 * E.b₂) (E.b₂ ^ 2 - 32 * E.b₄)
        12 (-E.b₂) (-10 * E.b₄) (E.b₂ * E.b₄ - 27 * E.b₆) hB0u hB0v
      rwa [← h_id0, map_one] at this
    have hx7_le : v x ^ 7 ≤ doublePlaceBound E v * K_pp * M ^ 3 := by
      have := h_comb (u7c3 E) (u7c2 E) (u7c1 E) (u7c0 E)
        (v7c3 E) (v7c2 E) (v7c1 E) (v7c0 E) hB7u hB7v
      rwa [← h_id7, map_pow] at this
    have hM7_eq : M ^ 7 = max (v x ^ 7) 1 := by
      dsimp [M]
      rcases le_total (v x) 1 with hle | hge
      · rw [max_eq_right hle, one_pow, max_eq_right (pow_le_one₀ (apply_nonneg v x) hle)]
      · rw [max_eq_left hge, max_eq_left (one_le_pow₀ hge)]
    have hM7_le : M ^ 4 * M ^ 3 ≤ doublePlaceBound E v * K_pp * M ^ 3 := by
      calc M ^ 4 * M ^ 3 = M ^ 7 := by ring
        _ = max (v x ^ 7) 1 := hM7_eq
        _ ≤ doublePlaceBound E v * K_pp * M ^ 3 := max_le hx7_le h1_le
    exact le_of_mul_le_mul_right hM7_le hM3_pos
  have mulSupport_max_one_finite : ∀ (y : K),
      (Function.mulSupport (fun v : NumberField.FinitePlace K => max (v y) 1)).Finite := by
    intro y
    by_cases hy : y = 0
    · subst hy
      have : (fun v : NumberField.FinitePlace K => max (v (0 : K)) 1) = fun _ => 1 := by
        ext v; simp
      rw [this]
      simp [Function.mulSupport]
    · refine (NumberField.FinitePlace.mulSupport_finite hy).subset ?_
      intro v hv
      simp only [Function.mem_mulSupport] at hv ⊢
      intro hvy
      apply hv
      rw [hvy, max_self]
  have mulSupport_mul_finite : ∀ {f g : NumberField.FinitePlace K → ℝ},
      (Function.mulSupport f).Finite → (Function.mulSupport g).Finite →
      (Function.mulSupport (fun v => f v * g v)).Finite :=
    fun hf hg => (hf.union hg).subset (Function.mulSupport_mul _ _)
  have mulSupport_deg3Bound_finite : ∀ (c3 c2 c1 c0 : K),
      (Function.mulSupport (fun v : NumberField.FinitePlace K => deg3Bound v c3 c2 c1 c0)).Finite :=
    fun c3 c2 c1 c0 =>
      mulSupport_mul_finite
        (mulSupport_mul_finite
          (mulSupport_mul_finite (mulSupport_max_one_finite c3) (mulSupport_max_one_finite c2))
          (mulSupport_max_one_finite c1))
        (mulSupport_max_one_finite c0)
  have mulSupport_doublePlaceBound_finite :
      (Function.mulSupport (fun v : NumberField.FinitePlace K => doublePlaceBound E v)).Finite :=
    mulSupport_mul_finite
      (mulSupport_mul_finite
        (mulSupport_mul_finite
          (mulSupport_mul_finite (mulSupport_max_one_finite E.Δ⁻¹)
            (mulSupport_deg3Bound_finite _ _ _ _))
          (mulSupport_deg3Bound_finite _ _ _ _))
        (mulSupport_deg3Bound_finite _ _ _ _))
      (mulSupport_deg3Bound_finite _ _ _ _)
  have place_scale_max_eq : ∀ (u : K → ℝ),
      u 0 = 0 → (∀ x y, u (x * y) = u x * u y) → (∀ x, 0 ≤ u x) → ∀ (a b : K),
      max (u a) (u b) = max (u (a / b)) 1 * u (if b = 0 then a else b) := by
    intro u hu0 humul hunonneg a b
    by_cases hb : b = 0
    · simp [hb, hu0, max_eq_left (hunonneg a)]
    · rw [if_neg hb]
      have ha : a = (a / b) * b := (div_mul_cancel₀ a hb).symm
      conv_lhs => rw [ha, humul]
      rw [max_mul_of_nonneg (u (a / b)) 1 (hunonneg b), one_mul]
  have one_le_prod_real : ∀ {α : Type u} (s : Finset α) {f : α → ℝ},
      (∀ a ∈ s, 1 ≤ f a) → 1 ≤ ∏ a ∈ s, f a := by
    intro α s f h
    simpa using Finset.prod_le_prod (fun a _ => zero_le_one' ℝ) h
  have finprod_one_le_of_one_le : ∀ {f : NumberField.FinitePlace K → ℝ},
      (Function.mulSupport f).Finite → (∀ v, 1 ≤ f v) → 1 ≤ ∏ᶠ v, f v := by
    intro f hf h1
    rw [finprod_eq_prod_of_mulSupport_subset f hf.coe_toFinset.ge]
    exact one_le_prod_real _ (fun v _ => h1 v)
  set C_inf : ℝ := ∏ w : NumberField.InfinitePlace K, (8 * doublePlaceBound E w) ^ w.mult
  set C_fin : ℝ := ∏ᶠ v : NumberField.FinitePlace K, doublePlaceBound E v
  set C_glob : ℝ := C_inf * C_fin
  have hC_inf_ge : 1 ≤ C_inf := by
    refine one_le_prod_real _ (fun w _ => ?_)
    have := (doublePlaceBound_ge w).1
    exact one_le_pow₀ (by linarith)
  have hC_fin_ge : 1 ≤ C_fin :=
    finprod_one_le_of_one_le mulSupport_doublePlaceBound_finite
      (fun v => (doublePlaceBound_ge v).1)
  have hC_glob_ge : 1 ≤ C_glob := one_le_mul_of_one_le_of_one_le hC_inf_ge hC_fin_ge
  have hC₂_nonneg : 0 ≤ Real.log C_glob := Real.log_nonneg hC_glob_ge
  have hC₂ : ∀ x : K, 4 * fieldLogHeight x ≤ fieldLogHeight (phi2 E x / psi2Sq E x) + Real.log C_glob := by
    intro x
    set a : K := phi2 E x
    set b : K := psi2Sq E x
    set x2 : K := a / b
    set d : K := if b = 0 then a else b
    have hd : d ≠ 0 := by
      intro hd0
      have hab0 : a = 0 ∧ b = 0 := by
        by_cases hb : b = 0
        · have : d = a := if_pos hb
          exact ⟨this ▸ hd0, hb⟩
        · have : d = b := if_neg hb
          exact absurd (this ▸ hd0) hb
      let w0 : NumberField.InfinitePlace K := Classical.arbitrary (NumberField.InfinitePlace K)
      have hw0 := double_local_infinite_bound w0 x
      change max (w0 x) 1 ^ 4 ≤ 8 * doublePlaceBound E w0 * max (w0 a) (w0 b) at hw0
      rw [hab0.1, hab0.2, map_zero, max_self, mul_zero] at hw0
      have h1 : (1 : ℝ) ≤ max (w0 x) 1 ^ 4 := one_le_pow₀ (le_max_right _ _)
      linarith
    have h_inf_prod : (∏ w : NumberField.InfinitePlace K, max (w x) 1 ^ w.mult) ^ 4 ≤
        C_inf * (∏ w : NumberField.InfinitePlace K, max (w x2) 1 ^ w.mult) *
          (∏ w : NumberField.InfinitePlace K, w d ^ w.mult) := by
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod (fun w _ => by positivity) (fun w _ => ?_)
      have hw := double_local_infinite_bound w x
      change max (w x) 1 ^ 4 ≤ 8 * doublePlaceBound E w * max (w a) (w b) at hw
      rw [place_scale_max_eq w (map_zero w) (map_mul w) (apply_nonneg w) a b] at hw
      change max (w x) 1 ^ 4 ≤ 8 * doublePlaceBound E w * (max (w x2) 1 * w d) at hw
      have hpow := pow_le_pow_left₀ (by positivity) hw w.mult
      calc (max (w x) 1 ^ w.mult) ^ 4 = (max (w x) 1 ^ 4) ^ w.mult := by ring
        _ ≤ (8 * doublePlaceBound E w * (max (w x2) 1 * w d)) ^ w.mult := hpow
        _ = (8 * doublePlaceBound E w) ^ w.mult * max (w x2) 1 ^ w.mult * w d ^ w.mult := by ring
    have hf_x := mulSupport_max_one_finite x
    have hf_B := mulSupport_doublePlaceBound_finite
    have hf_x2 := mulSupport_max_one_finite x2
    have hf_d := NumberField.FinitePlace.mulSupport_finite hd
    let hU := (hf_x.union hf_B).union (hf_x2.union hf_d)
    let S : Finset (NumberField.FinitePlace K) := hU.toFinset
    have hS_x : Function.mulSupport (fun v : NumberField.FinitePlace K => max (v x) 1) ⊆ S := by
      rw [hU.coe_toFinset]
      exact fun v hv => Or.inl (Or.inl hv)
    have hS_B : Function.mulSupport (fun v : NumberField.FinitePlace K => doublePlaceBound E v) ⊆ S := by
      rw [hU.coe_toFinset]
      exact fun v hv => Or.inl (Or.inr hv)
    have hS_x2 : Function.mulSupport (fun v : NumberField.FinitePlace K => max (v x2) 1) ⊆ S := by
      rw [hU.coe_toFinset]
      exact fun v hv => Or.inr (Or.inl hv)
    have hS_d : Function.mulSupport (fun v : NumberField.FinitePlace K => v d) ⊆ S := by
      rw [hU.coe_toFinset]
      exact fun v hv => Or.inr (Or.inr hv)
    have h_fin_prod : (∏ᶠ v : NumberField.FinitePlace K, max (v x) 1) ^ 4 ≤
        C_fin * (∏ᶠ v : NumberField.FinitePlace K, max (v x2) 1) *
          (∏ᶠ v : NumberField.FinitePlace K, v d) := by
      dsimp only [C_fin]
      rw [finprod_eq_prod_of_mulSupport_subset _ hS_x,
        finprod_eq_prod_of_mulSupport_subset _ hS_B,
        finprod_eq_prod_of_mulSupport_subset _ hS_x2,
        finprod_eq_prod_of_mulSupport_subset _ hS_d,
        ← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod (fun v _ => by positivity) (fun v _ => ?_)
      have hv := double_local_finite_bound v x
      change max (v x) 1 ^ 4 ≤ doublePlaceBound E v * max (v a) (v b) at hv
      rw [place_scale_max_eq v (map_zero v) (map_mul v) (apply_nonneg v) a b] at hv
      change max (v x) 1 ^ 4 ≤ doublePlaceBound E v * (max (v x2) 1 * v d) at hv
      linarith
    set I_x := ∏ w : NumberField.InfinitePlace K, max (w x) 1 ^ w.mult
    set F_x := ∏ᶠ v : NumberField.FinitePlace K, max (v x) 1
    set I_x2 := ∏ w : NumberField.InfinitePlace K, max (w x2) 1 ^ w.mult
    set F_x2 := ∏ᶠ v : NumberField.FinitePlace K, max (v x2) 1
    set P_inf_d := ∏ w : NumberField.InfinitePlace K, w d ^ w.mult
    set P_fin_d := ∏ᶠ v : NumberField.FinitePlace K, v d
    have hIx1 : 1 ≤ I_x := one_le_prod_real _ (fun w _ => one_le_pow₀ (le_max_right _ _))
    have hFx1 : 1 ≤ F_x := finprod_one_le_of_one_le hf_x (fun v => le_max_right _ _)
    have hIx21 : 1 ≤ I_x2 := one_le_prod_real _ (fun w _ => one_le_pow₀ (le_max_right _ _))
    have hFx21 : 1 ≤ F_x2 := finprod_one_le_of_one_le hf_x2 (fun v => le_max_right _ _)
    have h_prod_d : P_inf_d * P_fin_d = 1 := NumberField.prod_abs_eq_one hd
    have h_comb_prod : (I_x * F_x) ^ 4 ≤ (I_x2 * F_x2) * C_glob := by
      have h_mul := mul_le_mul h_inf_prod h_fin_prod (by positivity) (by positivity)
      calc (I_x * F_x) ^ 4 = I_x ^ 4 * F_x ^ 4 := by ring
        _ ≤ (C_inf * I_x2 * P_inf_d) * (C_fin * F_x2 * P_fin_d) := h_mul
        _ = (I_x2 * F_x2) * (C_inf * C_fin) * (P_inf_d * P_fin_d) := by ring
        _ = (I_x2 * F_x2) * C_glob * 1 := by rw [h_prod_d]
        _ = (I_x2 * F_x2) * C_glob := by ring
    have hHx_pos : 0 < I_x * F_x := by positivity
    have hHx2_pos : 0 < I_x2 * F_x2 := by positivity
    have hC_pos : 0 < C_glob := by positivity
    have h_log := Real.log_le_log (by positivity) h_comb_prod
    rw [Real.log_pow, Real.log_mul hHx2_pos.ne' hC_pos.ne'] at h_log
    push_cast at h_log
    exact h_log
  refine ⟨Real.log C_glob, fun P => ?_⟩
  rcases P with _ | @⟨x, y, hP⟩
  · change 4 * 0 ≤ 0 + Real.log C_glob
    linarith
  · rw [weierstrassHeight_double_eq hP]
    exact hC₂ x

theorem exists_three_roots_in_splittingField {K : Type u} [Field K] [CharZero K]
    (E : WeierstrassCurve K) (hE : E.IsElliptic) :
    ∃ e₁ e₂ e₃ : (twoTorsionPoly E).SplittingField,
      e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃ ∧
      ∀ x : (twoTorsionPoly E).SplittingField,
        4 * x ^ 3 + (E.baseChange (twoTorsionPoly E).SplittingField).b₂ * x ^ 2 +
          2 * (E.baseChange (twoTorsionPoly E).SplittingField).b₄ * x +
          (E.baseChange (twoTorsionPoly E).SplittingField).b₆ =
        4 * (x - e₁) * (x - e₂) * (x - e₃) :=
by
  have hp3_deg : (Polynomial.X ^ 3 : Polynomial K).natDegree = 3 := Polynomial.natDegree_X_pow 3
  have hp3_monic : (Polynomial.X ^ 3 : Polynomial K).Monic := Polynomial.monic_X_pow 3
  have hq2_deg : (Polynomial.C (E.b₂ / 4) * Polynomial.X ^ 2).natDegree <
      (Polynomial.X ^ 3 : Polynomial K).natDegree := by
    rw [hp3_deg]
    exact Nat.lt_of_le_of_lt (Polynomial.natDegree_C_mul_X_pow_le (E.b₂ / 4) 2) (by decide)
  have hp2_deg : (Polynomial.X ^ 3 + Polynomial.C (E.b₂ / 4) * Polynomial.X ^ 2).natDegree = 3 := by
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hq2_deg, hp3_deg]
  have hp2_monic : (Polynomial.X ^ 3 + Polynomial.C (E.b₂ / 4) * Polynomial.X ^ 2).Monic :=
    hp3_monic.add_of_left (Polynomial.degree_lt_degree hq2_deg)
  have hq1_deg : (Polynomial.C (E.b₄ / 2) * Polynomial.X).natDegree <
      (Polynomial.X ^ 3 + Polynomial.C (E.b₂ / 4) * Polynomial.X ^ 2).natDegree := by
    rw [hp2_deg]
    exact Nat.lt_of_le_of_lt (Polynomial.natDegree_C_mul_le (E.b₄ / 2) Polynomial.X)
      (by rw [Polynomial.natDegree_X]; decide)
  have hp1_deg : (Polynomial.X ^ 3 + Polynomial.C (E.b₂ / 4) * Polynomial.X ^ 2 +
      Polynomial.C (E.b₄ / 2) * Polynomial.X).natDegree = 3 := by
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hq1_deg, hp2_deg]
  have hp1_monic : (Polynomial.X ^ 3 + Polynomial.C (E.b₂ / 4) * Polynomial.X ^ 2 +
      Polynomial.C (E.b₄ / 2) * Polynomial.X).Monic :=
    hp2_monic.add_of_left (Polynomial.degree_lt_degree hq1_deg)
  have hq0_deg : (Polynomial.C (E.b₆ / 4)).natDegree <
      (Polynomial.X ^ 3 + Polynomial.C (E.b₂ / 4) * Polynomial.X ^ 2 +
        Polynomial.C (E.b₄ / 2) * Polynomial.X).natDegree := by
    rw [hp1_deg, Polynomial.natDegree_C]; decide
  have hdeg : (twoTorsionPoly E).natDegree = 3 := by
    dsimp [twoTorsionPoly]
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hq0_deg, hp1_deg]
  have hmonic : (twoTorsionPoly E).Monic := by
    dsimp [twoTorsionPoly]
    exact hp1_monic.add_of_left (Polynomial.degree_lt_degree hq0_deg)
  let L := (twoTorsionPoly E).SplittingField
  haveI : CharZero L := ⟨fun a b h => by
    apply Nat.cast_injective (R := K)
    apply (algebraMap K L).injective
    simpa using h⟩
  let g : Polynomial L := (twoTorsionPoly E).map (algebraMap K L)
  have hs : g.Splits := Polynomial.SplittingField.splits (twoTorsionPoly E)
  have hg_monic : g.Monic := hmonic.map (algebraMap K L)
  have hg_deg : g.natDegree = 3 := (hmonic.natDegree_map (algebraMap K L)).trans hdeg
  have hcard : g.roots.card = 3 := (Polynomial.Splits.natDegree_eq_card_roots hs).symm.trans hg_deg
  obtain ⟨e₁, e₂, e₃, hroots⟩ := Multiset.card_eq_three.mp hcard
  have hg_prod : g = (Polynomial.X - Polynomial.C e₁) * (Polynomial.X - Polynomial.C e₂) *
      (Polynomial.X - Polynomial.C e₃) := by
    have h1 := Polynomial.Splits.eq_prod_roots_of_monic hs hg_monic
    rw [hroots] at h1
    simpa [Multiset.insert_eq_cons, mul_assoc] using h1
  let W : WeierstrassCurve L := E.baseChange L
  have hcubic : ∀ x : L,
      4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ =
      4 * (x - e₁) * (x - e₂) * (x - e₃) := by
    intro x
    have heval : Polynomial.eval x g = (x - e₁) * (x - e₂) * (x - e₃) := by
      rw [hg_prod]; simp
    have heval2 : Polynomial.eval x g = x ^ 3 + W.b₂ / 4 * x ^ 2 + W.b₄ / 2 * x + W.b₆ / 4 := by
      dsimp [g, twoTorsionPoly]
      simp only [Polynomial.eval_map, Polynomial.eval₂_add, Polynomial.eval₂_mul,
        Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, map_div₀, map_ofNat]
      rw [← E.map_b₂ (algebraMap K L), ← E.map_b₄ (algebraMap K L), ← E.map_b₆ (algebraMap K L)]
    have h_eq : x ^ 3 + W.b₂ / 4 * x ^ 2 + W.b₄ / 2 * x + W.b₆ / 4 =
        (x - e₁) * (x - e₂) * (x - e₃) := heval2.symm.trans heval
    linear_combination 4 * h_eq
  have h0 := hcubic 0
  have h1 := hcubic 1
  have hm1 := hcubic (-1)
  have hb6 : W.b₆ = -4 * e₁ * e₂ * e₃ := by linear_combination h0
  have hb2 : W.b₂ = -4 * (e₁ + e₂ + e₃) := by
    linear_combination (1 / 2 : L) * h1 + (1 / 2 : L) * hm1 - h0
  have hb4 : W.b₄ = 2 * (e₁ * e₂ + e₁ * e₃ + e₂ * e₃) := by
    linear_combination (1 / 4 : L) * h1 - (1 / 4 : L) * hm1
  have hΔ_id : W.Δ = 16 * (e₁ - e₂) ^ 2 * (e₁ - e₃) ^ 2 * (e₂ - e₃) ^ 2 := by
    have hΔ_b : 4 * W.Δ = -W.b₂ ^ 2 * (W.b₂ * W.b₆ - W.b₄ ^ 2) - 32 * W.b₄ ^ 3 -
        108 * W.b₆ ^ 2 + 36 * W.b₂ * W.b₄ * W.b₆ := by
      dsimp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring
    rw [hb2, hb4, hb6] at hΔ_b
    linear_combination (1 / 4 : L) * hΔ_b
  have hΔ_unit : IsUnit W.Δ := by
    change IsUnit (E.baseChange L).Δ
    rw [E.map_Δ (algebraMap K L)]
    exact hE.isUnit.map (algebraMap K L)
  have hΔ_ne : W.Δ ≠ 0 := hΔ_unit.ne_zero
  refine ⟨e₁, e₂, e₃, ?_, ?_, ?_, hcubic⟩
  · intro h12; apply hΔ_ne; rw [hΔ_id, h12]; ring
  · intro h13; apply hΔ_ne; rw [hΔ_id, h13]; ring
  · intro h23; apply hΔ_ne; rw [hΔ_id, h23]; ring

theorem kummer_mul_of_not_two_torsion {F : Type u} [Field F] [CharZero F] [DecidableEq F]
    (W : WeierstrassCurve F) (e₁ e₂ e₃ : F)
    (hcubic : ∀ x : F, 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ =
      4 * (x - e₁) * (x - e₂) * (x - e₃))
    (P₁ P₂ : W.toAffine.Point)
    (h₁ : P₁ + P₁ ≠ 0) (h₂ : P₂ + P₂ ≠ 0) (h₁₂ : (P₁ + P₂) + (P₁ + P₂) ≠ 0) :
    pointKummer W e₁ e₂ (P₁ + P₂) = pointKummer W e₁ e₂ P₁ * pointKummer W e₁ e₂ P₂ :=
by
  have pointKummer_some : ∀ {x y : F} (h : W.toAffine.Nonsingular x y)
      (hc : x - e₁ ≠ 0 ∧ x - e₂ ≠ 0),
      pointKummer W e₁ e₂ (WeierstrassCurve.Affine.Point.some h) =
        (sqCl (Units.mk0 (x - e₁) hc.1), sqCl (Units.mk0 (x - e₂) hc.2)) := by
    intro x y h hc
    dsimp [pointKummer]
    exact dif_pos hc
  have sub_root_ne_zero : ∀ {x y : F} (h : W.toAffine.Nonsingular x y),
      WeierstrassCurve.Affine.Point.some h + WeierstrassCurve.Affine.Point.some h ≠ 0 →
      x - e₁ ≠ 0 ∧ x - e₂ ≠ 0 := by
    intro x y h hne
    have hy : y ≠ W.toAffine.negY x y := by
      intro hyeq
      exact hne (WeierstrassCurve.Affine.Point.add_self_of_Y_eq hyeq)
    have h2y : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
      intro h0
      apply hy
      rw [WeierstrassCurve.Affine.negY]
      linear_combination h0
    have heq := (W.toAffine.equation_iff x y).mp h.1
    have hsq : (2 * y + W.a₁ * x + W.a₃) ^ 2 = 4 * (x - e₁) * (x - e₂) * (x - e₃) := by
      calc (2 * y + W.a₁ * x + W.a₃) ^ 2
        _ = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
          dsimp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
          linear_combination 4 * heq
        _ = 4 * (x - e₁) * (x - e₂) * (x - e₃) := hcubic x
    have hprod : 4 * (x - e₁) * (x - e₂) * (x - e₃) ≠ 0 := hsq ▸ pow_ne_zero 2 h2y
    refine ⟨fun h0 => hprod (by rw [h0]; ring), fun h0 => hprod (by rw [h0]; ring)⟩
  have sqCl_of_eval_eq : ∀ (x₁ y₁ x₂ x₃ ℓ e : F),
      Polynomial.eval e (W.toAffine.addPolynomial x₁ y₁ ℓ) =
        -((e - x₁) * (e - x₂) * (e - x₃)) →
      4 * e ^ 3 + W.b₂ * e ^ 2 + 2 * W.b₄ * e + W.b₆ = 0 →
      ∀ (hx₁ : x₁ - e ≠ 0) (hx₂ : x₂ - e ≠ 0) (hx₃ : x₃ - e ≠ 0),
      sqCl (Units.mk0 (x₃ - e) hx₃) =
        sqCl (Units.mk0 (x₁ - e) hx₁) * sqCl (Units.mk0 (x₂ - e) hx₂) := by
    intro x₁ y₁ x₂ x₃ ℓ e hpoly he hx₁ hx₂ hx₃
    rw [WeierstrassCurve.Affine.addPolynomial_eq] at hpoly
    simp only [Cubic.toPoly, Polynomial.eval_neg, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hpoly
    have hid : (x₁ - e) * (x₂ - e) * (x₃ - e) =
        (ℓ * (e - x₁) + y₁ + (W.a₁ * e + W.a₃) / 2) ^ 2 := by
      dsimp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at he
      linear_combination -hpoly - he / 4
    set w : F := ℓ * (e - x₁) + y₁ + (W.a₁ * e + W.a₃) / 2
    have hw2 : w ^ 2 ≠ 0 := hid ▸ mul_ne_zero (mul_ne_zero hx₁ hx₂) hx₃
    have hw : w ≠ 0 := fun h0 => hw2 (by rw [h0, sq, zero_mul])
    dsimp only [sqCl]
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, MonoidHom.mem_range]
    refine ⟨(Units.mk0 (x₃ - e) hx₃)⁻¹ * Units.mk0 w hw, ?_⟩
    ext
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mul,
      Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp
    linear_combination -hid
  cases P₁ with
  | zero => exfalso; apply h₁; rw [← WeierstrassCurve.Affine.Point.zero_def, zero_add]
  | @some x₁ y₁ hP₁ =>
    cases P₂ with
    | zero => exfalso; apply h₂; rw [← WeierstrassCurve.Affine.Point.zero_def, zero_add]
    | @some x₂ y₂ hP₂ =>
      have hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂) := by
        rintro ⟨hx, hy⟩
        apply h₁₂
        rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hx hy, zero_add]
      have hadd := WeierstrassCurve.Affine.Point.add_some hxy (h₁ := hP₁) (h₂ := hP₂)
      have h₁₂' : WeierstrassCurve.Affine.Point.some (W.toAffine.nonsingular_add hP₁ hP₂ hxy) +
          WeierstrassCurve.Affine.Point.some (W.toAffine.nonsingular_add hP₁ hP₂ hxy) ≠ 0 := by
        rwa [← hadd]
      have hc₁ := sub_root_ne_zero hP₁ h₁
      have hc₂ := sub_root_ne_zero hP₂ h₂
      have hc₃ := sub_root_ne_zero (W.toAffine.nonsingular_add hP₁ hP₂ hxy) h₁₂'
      have hpoly : ∀ e : F,
          Polynomial.eval e (W.toAffine.addPolynomial x₁ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂)) =
          -((e - x₁) * (e - x₂) *
            (e - W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))) := by
        intro e
        have H := congr_arg (Polynomial.eval e)
          (WeierstrassCurve.Affine.addPolynomial_slope hP₁.1 hP₂.1 hxy)
        simpa only [Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C] using H
      rw [hadd, pointKummer_some _ hc₃, pointKummer_some _ hc₁, pointKummer_some _ hc₂,
        Prod.mk_mul_mk, Prod.ext_iff]
      have he₁ : 4 * e₁ ^ 3 + W.b₂ * e₁ ^ 2 + 2 * W.b₄ * e₁ + W.b₆ = 0 := by
        rw [hcubic e₁]; ring
      have he₂ : 4 * e₂ ^ 3 + W.b₂ * e₂ ^ 2 + 2 * W.b₄ * e₂ + W.b₆ = 0 := by
        rw [hcubic e₂]; ring
      exact ⟨sqCl_of_eval_eq x₁ y₁ x₂ _ _ e₁ (hpoly e₁) he₁ hc₁.1 hc₂.1 hc₃.1,
        sqCl_of_eval_eq x₁ y₁ x₂ _ _ e₂ (hpoly e₂) he₂ hc₁.2 hc₂.2 hc₃.2⟩

theorem halving_of_kummer_eq_one {F : Type u} [Field F] [CharZero F] [DecidableEq F]
    (W : WeierstrassCurve F) (e₁ e₂ e₃ : F)
    (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃)
    (hcubic : ∀ x : F, 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ =
      4 * (x - e₁) * (x - e₂) * (x - e₃))
    (P : W.toAffine.Point) (hP : P + P ≠ 0)
    (hk : pointKummer W e₁ e₂ P = (1, 1)) :
    ∃ P' : W.toAffine.Point, P = P' + P' :=
by
  have hc0 := hcubic 0
  have hc1 := hcubic 1
  have hcm1 := hcubic (-1)
  have hb₂ : W.b₂ = -4 * (e₁ + e₂ + e₃) := by
    linear_combination (hc1 + hcm1 - 2 * hc0) / 2
  have hb₄ : W.b₄ = 2 * (e₁ * e₂ + e₁ * e₃ + e₂ * e₃) := by
    linear_combination (hc1 - hcm1) / 4
  have hb₆ : W.b₆ = -4 * e₁ * e₂ * e₃ := by
    linear_combination hc0
  have hb₂' : W.a₁ ^ 2 + 4 * W.a₂ = -4 * (e₁ + e₂ + e₃) := hb₂
  have hb₄' : 2 * W.a₄ + W.a₁ * W.a₃ = 2 * (e₁ * e₂ + e₁ * e₃ + e₂ * e₃) := hb₄
  have hb₆' : W.a₃ ^ 2 + 4 * W.a₆ = -4 * e₁ * e₂ * e₃ := hb₆
  have ha₂ : W.a₂ = -(e₁ + e₂ + e₃) - W.a₁ ^ 2 / 4 := by
    linear_combination hb₂' / 4
  have ha₄ : W.a₄ = (e₁ * e₂ + e₁ * e₃ + e₂ * e₃) - W.a₁ * W.a₃ / 2 := by
    linear_combination hb₄' / 2
  rcases P with _ | @⟨x₀, y₀, h₀⟩
  · exfalso
    apply hP
    rw [← WeierstrassCurve.Affine.Point.zero_def, zero_add]
  have hy₀_ne : y₀ ≠ W.toAffine.negY x₀ y₀ := by
    intro hy₀
    exact hP (WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy₀)
  let y₀_tilde : F := y₀ + (W.a₁ * x₀ + W.a₃) / 2
  have hyt₀_ne : y₀_tilde ≠ 0 := by
    intro h
    apply hy₀_ne
    change y₀ = -y₀ - W.a₁ * x₀ - W.a₃
    change y₀ + (W.a₁ * x₀ + W.a₃) / 2 = 0 at h
    linear_combination 2 * h
  have h_eq₀ : y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ = x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆ :=
    (WeierstrassCurve.Affine.equation_iff x₀ y₀).mp h₀.1
  have hyt₀_sq : y₀_tilde ^ 2 = (x₀ - e₁) * (x₀ - e₂) * (x₀ - e₃) := by
    have hc_x₀ : 4 * x₀ ^ 3 + (W.a₁ ^ 2 + 4 * W.a₂) * x₀ ^ 2 + 2 * (2 * W.a₄ + W.a₁ * W.a₃) * x₀ + (W.a₃ ^ 2 + 4 * W.a₆) =
        4 * (x₀ - e₁) * (x₀ - e₂) * (x₀ - e₃) := hcubic x₀
    change (y₀ + (W.a₁ * x₀ + W.a₃) / 2) ^ 2 = (x₀ - e₁) * (x₀ - e₂) * (x₀ - e₃)
    linear_combination h_eq₀ + hc_x₀ / 4
  have hprod_ne : (x₀ - e₁) * (x₀ - e₂) * (x₀ - e₃) ≠ 0 := by
    rw [← hyt₀_sq]
    exact pow_ne_zero 2 hyt₀_ne
  have hx₁₂ : (x₀ - e₁) * (x₀ - e₂) ≠ 0 := left_ne_zero_of_mul hprod_ne
  have hx₁ : x₀ - e₁ ≠ 0 := left_ne_zero_of_mul hx₁₂
  have hx₂ : x₀ - e₂ ≠ 0 := right_ne_zero_of_mul hx₁₂
  dsimp [pointKummer] at hk
  rw [dif_pos ⟨hx₁, hx₂⟩, Prod.mk.injEq] at hk
  rcases hk with ⟨hk₁, hk₂⟩
  unfold sqCl at hk₁ hk₂
  rw [QuotientGroup.eq_one_iff, MonoidHom.mem_range] at hk₁ hk₂
  rcases hk₁ with ⟨v₁, hv₁⟩
  rcases hk₂ with ⟨v₂, hv₂⟩
  rw [powMonoidHom_apply] at hv₁ hv₂
  let u₁ : F := (v₁ : F)
  let u₂ : F := (v₂ : F)
  have hu₁_ne : u₁ ≠ 0 := Units.ne_zero v₁
  have hu₂_ne : u₂ ≠ 0 := Units.ne_zero v₂
  have hv₁_val : u₁ ^ 2 = x₀ - e₁ := by
    simpa [u₁] using congr_arg Units.val hv₁
  have hv₂_val : u₂ ^ 2 = x₀ - e₂ := by
    simpa [u₂] using congr_arg Units.val hv₂
  have hu₁_sq : e₁ = x₀ - u₁ ^ 2 := by linear_combination hv₁_val
  have hu₂_sq : e₂ = x₀ - u₂ ^ 2 := by linear_combination hv₂_val
  let u₃ : F := y₀_tilde / (u₁ * u₂)
  have hu₁₂₃ : u₁ * u₂ * u₃ = y₀_tilde := by
    dsimp [u₃]
    exact mul_div_cancel₀ y₀_tilde (mul_ne_zero hu₁_ne hu₂_ne)
  clear_value u₃
  have hy₀ : y₀ = u₁ * u₂ * u₃ - (W.a₁ * x₀ + W.a₃) / 2 := by
    change u₁ * u₂ * u₃ = y₀ + (W.a₁ * x₀ + W.a₃) / 2 at hu₁₂₃
    linear_combination -hu₁₂₃
  have hu₃_sq_mul : (x₀ - e₁) * (x₀ - e₂) * (e₃ - (x₀ - u₃ ^ 2)) = 0 := by
    calc (x₀ - e₁) * (x₀ - e₂) * (e₃ - (x₀ - u₃ ^ 2))
      _ = (u₁ * u₂ * u₃) ^ 2 - (x₀ - e₁) * (x₀ - e₂) * (x₀ - e₃) := by
          rw [hu₁_sq, hu₂_sq]; ring
      _ = y₀_tilde ^ 2 - y₀_tilde ^ 2 := by rw [hu₁₂₃, hyt₀_sq]
      _ = 0 := sub_self _
  have hu₃_sq : e₃ = x₀ - u₃ ^ 2 := by
    rcases mul_eq_zero.mp hu₃_sq_mul with h_abs | h_eq₃
    · exact False.elim (hx₁₂ h_abs)
    · linear_combination h_eq₃
  let x : F := x₀ + u₁ * u₂ + u₁ * u₃ + u₂ * u₃
  let y_tilde : F := (u₁ + u₂) * (u₁ + u₃) * (u₂ + u₃)
  let y : F := y_tilde - (W.a₁ * x + W.a₃) / 2
  have hu₁₂_ne : u₁ + u₂ ≠ 0 := by
    intro h
    apply h₁₂
    rw [hu₁_sq, hu₂_sq]
    linear_combination -(u₁ - u₂) * h
  have hu₁₃_ne : u₁ + u₃ ≠ 0 := by
    intro h
    apply h₁₃
    rw [hu₁_sq, hu₃_sq]
    linear_combination -(u₁ - u₃) * h
  have hu₂₃_ne : u₂ + u₃ ≠ 0 := by
    intro h
    apply h₂₃
    rw [hu₂_sq, hu₃_sq]
    linear_combination -(u₂ - u₃) * h
  have hyt_ne : y_tilde ≠ 0 := mul_ne_zero (mul_ne_zero hu₁₂_ne hu₁₃_ne) hu₂₃_ne
  have hy_ne : y ≠ W.toAffine.negY x y := by
    intro h
    apply hyt_ne
    change y = -y - W.a₁ * x - W.a₃ at h
    change y_tilde = 0
    have h_rel : y = y_tilde - (W.a₁ * x + W.a₃) / 2 := rfl
    linear_combination h / 2 - h_rel
  have h_eq : W.toAffine.Equation x y := by
    rw [WeierstrassCurve.Affine.equation_iff]
    change y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆
    have hyt_sq : (y + (W.a₁ * x + W.a₃) / 2) ^ 2 = (x - e₁) * (x - e₂) * (x - e₃) := by
      dsimp [y, y_tilde, x]
      rw [hu₁_sq, hu₂_sq, hu₃_sq]
      ring
    have hc_x : 4 * x ^ 3 + (W.a₁ ^ 2 + 4 * W.a₂) * x ^ 2 + 2 * (2 * W.a₄ + W.a₁ * W.a₃) * x + (W.a₃ ^ 2 + 4 * W.a₆) =
        4 * (x - e₁) * (x - e₂) * (x - e₃) := hcubic x
    linear_combination hyt_sq - hc_x / 4
  have h' : W.toAffine.Nonsingular x y := by
    rw [WeierstrassCurve.Affine.nonsingular_iff]
    exact ⟨h_eq, Or.inr hy_ne⟩
  refine ⟨WeierstrassCurve.Affine.Point.some h', ?_⟩
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy_ne, WeierstrassCurve.Affine.Point.some.injEq]
  let ℓ₀ : F := u₁ + u₂ + u₃ - W.a₁ / 2
  have h_slope : W.toAffine.slope x x y y = ℓ₀ := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy_ne, div_eq_iff (sub_ne_zero.mpr hy_ne)]
    change 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y = ℓ₀ * (y - (-y - W.a₁ * x - W.a₃))
    dsimp [x, y, y_tilde, ℓ₀]
    rw [ha₂, ha₄, hu₁_sq, hu₂_sq, hu₃_sq]
    ring
  rw [h_slope]
  have hx₀_eq : W.toAffine.addX x x ℓ₀ = x₀ := by
    change ℓ₀ ^ 2 + W.a₁ * ℓ₀ - W.a₂ - x - x = x₀
    dsimp [x, ℓ₀]
    rw [ha₂, hu₁_sq, hu₂_sq, hu₃_sq]
    ring
  refine ⟨hx₀_eq.symm, ?_⟩
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY WeierstrassCurve.Affine.negY
  rw [hx₀_eq]
  change y₀ = -(ℓ₀ * (x₀ - x) + y) - W.a₁ * x₀ - W.a₃
  dsimp [x, y, y_tilde, ℓ₀]
  rw [hy₀]
  ring

theorem kummer_image_subset_selmerGroup {L : Type u} [Field L] [NumberField L] [DecidableEq L]
    (W : WeierstrassCurve L) (e₁ e₂ e₃ : L)
    (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃)
    (hcubic : ∀ x : L, 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ =
      4 * (x - e₁) * (x - e₂) * (x - e₃)) :
    ∃ T : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)),
      T.Finite ∧
      ∀ P : W.toAffine.Point,
        (pointKummer W e₁ e₂ P).1 ∈
          IsDedekindDomain.selmerGroup (R := NumberField.RingOfIntegers L) (K := L) (S := T) (n := 2) ∧
        (pointKummer W e₁ e₂ P).2 ∈
          IsDedekindDomain.selmerGroup (R := NumberField.RingOfIntegers L) (K := L) (S := T) (n := 2) :=
by
  have h_int : ∀ {r : NumberField.RingOfIntegers L} (hr : r ≠ 0),
      {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) |
        v.intValuation r ≠ 1}.Finite := by
    intro r hr
    have hI : Ideal.span ({r} : Set (NumberField.RingOfIntegers L)) ≠ 0 := by
      rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
      exact hr
    have hfin := Filter.eventually_cofinite.mp (Associates.finite_factors hI)
    refine hfin.subset ?_
    intro v hv
    simp only [Set.mem_setOf_eq] at hv ⊢
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg v hr] at hv
    intro h0
    apply hv
    rw [h0, neg_zero, WithZero.exp_zero]
  have h_fin_val : ∀ {z : L} (hz : z ≠ 0),
      {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) |
        v.valuation L z ≠ 1}.Finite := by
    intro z hz
    obtain ⟨a, b, hb_mem, hab⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers L) z
    have hb : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb_mem
    have ha : a ≠ 0 := by
      rintro rfl
      apply hz
      rw [← hab, map_zero, zero_div]
    refine ((h_int ha).union (h_int hb)).subset ?_
    intro v hv
    simp only [Set.mem_setOf_eq, Set.mem_union] at hv ⊢
    rw [← hab, Valuation.map_div, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap] at hv
    by_contra h_not
    push_neg at h_not
    apply hv
    rw [h_not.1, h_not.2, div_one]
  have h_cube_sq : ∀ (v : Valuation L (WithZero (Multiplicative ℤ))) (a₁ a₂ a₃ x z : L)
      (hz : z ^ 2 = (x - a₁) * (x - a₂) * (x - a₃))
      (ha₁₂ : v (a₁ - a₂) = 1) (ha₁₃ : v (a₁ - a₃) = 1),
      ∃ w : L, (v (x - a₁)) ^ 3 = (v w) ^ 2 := by
    intro v a₁ a₂ a₃ x z hz ha₁₂ ha₁₃
    have hval : (v z) ^ 2 = v (x - a₁) * v (x - a₂) * v (x - a₃) := by
      rw [← v.map_pow, hz, v.map_mul, v.map_mul]
    have hsub₂ : x - a₂ = (x - a₁) + (a₁ - a₂) := (sub_add_sub_cancel x a₁ a₂).symm
    have hsub₃ : x - a₃ = (x - a₁) + (a₁ - a₃) := (sub_add_sub_cancel x a₁ a₃).symm
    rcases lt_trichotomy (v (x - a₁)) 1 with hlt | heq | hgt
    · have hv₂ : v (x - a₂) = 1 := by
        rw [hsub₂, v.map_add_of_distinct_val (by rw [ha₁₂]; exact ne_of_lt hlt), ha₁₂,
          max_eq_right (le_of_lt hlt)]
      have hv₃ : v (x - a₃) = 1 := by
        rw [hsub₃, v.map_add_of_distinct_val (by rw [ha₁₃]; exact ne_of_lt hlt), ha₁₃,
          max_eq_right (le_of_lt hlt)]
      rw [hv₂, hv₃, mul_one, mul_one] at hval
      refine ⟨z ^ 3, ?_⟩
      rw [← hval, v.map_pow, ← pow_mul, ← pow_mul, mul_comm 2 3]
    · refine ⟨1, ?_⟩
      rw [heq, v.map_one, one_pow, one_pow]
    · have hv₂ : v (x - a₂) = v (x - a₁) := by
        rw [hsub₂, v.map_add_of_distinct_val (by rw [ha₁₂]; exact ne_of_gt hgt), ha₁₂,
          max_eq_left (le_of_lt hgt)]
      have hv₃ : v (x - a₃) = v (x - a₁) := by
        rw [hsub₃, v.map_add_of_distinct_val (by rw [ha₁₃]; exact ne_of_gt hgt), ha₁₃,
          max_eq_left (le_of_lt hgt)]
      rw [hv₂, hv₃, ← sq, ← pow_succ] at hval
      exact ⟨z, hval.symm⟩
  have h_mod_two : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
      (u : Lˣ) (h : ∃ w : L, (v.valuation L (u : L)) ^ 3 = (v.valuation L w) ^ 2),
      v.valuationOfNeZeroMod 2 (sqCl u) = 1 := by
    intro v u ⟨w, hw_eq⟩
    have hu_val : v.valuation L (u : L) = ↑(v.valuationOfNeZero u) :=
      (IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq v u).symm
    have hw_ne : w ≠ 0 := by
      rintro rfl
      rw [hu_val, Valuation.map_zero, zero_pow two_ne_zero, ← WithZero.coe_pow] at hw_eq
      exact WithZero.coe_ne_zero hw_eq
    let wu : Lˣ := Units.mk0 w hw_ne
    have hwu_val : v.valuation L w = ↑(v.valuationOfNeZero wu) :=
      (IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq v wu).symm
    rw [hu_val, hwu_val, ← WithZero.coe_pow, ← WithZero.coe_pow] at hw_eq
    have h_mult : (v.valuationOfNeZero u) ^ 3 = (v.valuationOfNeZero wu) ^ 2 :=
      WithZero.coe_inj.mp hw_eq
    let a : ℤ := Multiplicative.toAdd (v.valuationOfNeZero u)
    let b : ℤ := Multiplicative.toAdd (v.valuationOfNeZero wu)
    have h_add : 3 * a = 2 * b := by
      have h1 := congr_arg Multiplicative.toAdd h_mult
      rwa [toAdd_pow, toAdd_pow, nsmul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_ofNat] at h1
    have hdvd : (2 : ℤ) ∣ a := ⟨b - a, by omega⟩
    have hzmod : (a : ZMod 2) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd a 2).mpr hdvd
    change Multiplicative.ofAdd (a : ZMod 2) = 1
    rw [hzmod, ofAdd_zero]
  let T : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :=
    {v | v.valuation L (e₁ - e₂) ≠ 1} ∪
    {v | v.valuation L (e₁ - e₃) ≠ 1} ∪
    {v | v.valuation L (e₂ - e₃) ≠ 1}
  refine ⟨T, ?_, ?_⟩
  · exact ((h_fin_val (sub_ne_zero.mpr h₁₂)).union (h_fin_val (sub_ne_zero.mpr h₁₃))).union
      (h_fin_val (sub_ne_zero.mpr h₂₃))
  · intro P
    match P with
    | .zero =>
      simp only [pointKummer]
      exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
    | @WeierstrassCurve.Affine.Point.some _ _ _ x y hP =>
      simp only [pointKummer]
      split_ifs with hne
      · have heq : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
          (W.toAffine.equation_iff x y).mp hP.1
        have hcubic_x := hcubic x
        have hz : (y + (W.a₁ * x + W.a₃) / 2) ^ 2 = (x - e₁) * (x - e₂) * (x - e₃) := by
          dsimp [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at hcubic_x
          linear_combination 1 * heq + (1 / 4) * hcubic_x
        have hz₂ : (y + (W.a₁ * x + W.a₃) / 2) ^ 2 = (x - e₂) * (x - e₁) * (x - e₃) := by
          rw [hz, mul_comm (x - e₁) (x - e₂)]
        constructor
        · intro v hv
          simp only [T, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hv
          exact h_mod_two v (Units.mk0 (x - e₁) hne.1)
            (h_cube_sq (v.valuation L) e₁ e₂ e₃ x (y + (W.a₁ * x + W.a₃) / 2) hz hv.1.1 hv.1.2)
        · intro v hv
          simp only [T, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hv
          have hv₂₁ : v.valuation L (e₂ - e₁) = 1 := by
            rw [Valuation.map_sub_swap, hv.1.1]
          exact h_mod_two v (Units.mk0 (x - e₂) hne.2)
            (h_cube_sq (v.valuation L) e₂ e₁ e₃ x (y + (W.a₁ * x + W.a₃) / 2) hz₂ hv₂₁ hv.2)
      · exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩

theorem selmerGroup_two_finite {L : Type u} [Field L] [NumberField L]
    (T : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)))
    (hT : T.Finite) :
    (IsDedekindDomain.selmerGroup (R := NumberField.RingOfIntegers L) (K := L) (S := T) (n := 2) :
      Set (SqCl L)).Finite :=
by
  classical
  let R := NumberField.RingOfIntegers L
  let S_0 := IsDedekindDomain.selmerGroup (R := R) (K := L) (S := ∅) (n := 2)
  let S_T := IsDedekindDomain.selmerGroup (R := R) (K := L) (S := T) (n := 2)
  
  have hFG_pow2 : ∀ {G : Type u} [CommGroup G] [Monoid.FG G],
      Finite (G ⧸ (powMonoidHom 2 : G →* G).range) := by
    intro G _ _
    let Q := G ⧸ (powMonoidHom 2 : G →* G).range
    let π : G →* Q := QuotientGroup.mk' (powMonoidHom 2 : G →* G).range
    have hsq : ∀ q : Q, q * q = 1 := by
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      change (QuotientGroup.mk (g * g) : Q) = 1
      rw [QuotientGroup.eq_one_iff]
      exact ⟨g, sq g⟩
    obtain ⟨S, hS_closure, hS_fin⟩ := Monoid.fg_iff.mp ‹Monoid.FG G›
    let s : Finset Q := hS_fin.toFinset.image π
    let F : Finset Q := s.powerset.image (fun t : Finset Q => ∏ z ∈ t, z)
    have hF_mem : ∀ q ∈ Submonoid.closure (s : Set Q), q ∈ F := by
      intro q hq
      induction hq using Submonoid.closure_induction_left with
      | one =>
        rw [Finset.mem_image]
        exact ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset s), Finset.prod_empty⟩
      | mul_left x hx y _ hy =>
        rw [Finset.mem_coe] at hx
        rw [Finset.mem_image] at hy ⊢
        obtain ⟨t, ht, rfl⟩ := hy
        rw [Finset.mem_powerset] at ht
        by_cases hxt : x ∈ t
        · refine ⟨t.erase x, Finset.mem_powerset.mpr ((Finset.erase_subset x t).trans ht), ?_⟩
          have hprod : x * ∏ z ∈ t.erase x, z = ∏ z ∈ t, z :=
            Finset.mul_prod_erase t (fun z => z) hxt
          calc
            (∏ z ∈ t.erase x, z) = 1 * ∏ z ∈ t.erase x, z := (one_mul _).symm
            _ = (x * x) * ∏ z ∈ t.erase x, z := by rw [hsq x]
            _ = x * (x * ∏ z ∈ t.erase x, z) := mul_assoc _ _ _
            _ = x * ∏ z ∈ t, z := by rw [hprod]
        · refine ⟨insert x t, Finset.mem_powerset.mpr (Finset.insert_subset_iff.mpr ⟨hx, ht⟩), ?_⟩
          exact Finset.prod_insert hxt
    have huniv : (Set.univ : Set Q) ⊆ (F : Set Q) := by
      intro q _
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      have hg : g ∈ Submonoid.closure S := by rw [hS_closure]; trivial
      have hqg : π g ∈ Submonoid.map π (Submonoid.closure S) := Submonoid.mem_map_of_mem π hg
      rw [MonoidHom.map_mclosure] at hqg
      have hs_eq : (s : Set Q) = π '' S := by
        simp [s, Finset.coe_image, Set.Finite.coe_toFinset]
      rw [← hs_eq] at hqg
      exact Finset.mem_coe.mpr (hF_mem (π g) hqg)
    exact Set.finite_univ_iff.mp (F.finite_toSet.subset huniv)
  haveI hQ_fin : Finite (Rˣ ⧸ (powMonoidHom 2 : Rˣ →* Rˣ).range) := hFG_pow2 (G := Rˣ)
  
  have hex_rep : ∀ c : ↥S_0,
      ∃ (r : R) (hr : algebraMap R L r ≠ 0) (J : nonZeroDivisors (Ideal R)),
        (c : SqCl L) = sqCl (Units.mk0 (algebraMap R L r) hr) ∧
        Ideal.span {r} = (J : Ideal R) ^ 2 := by
    intro c
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (c : SqCl L)
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors R) (u : L)
    dsimp only at hab
    have hb0 : (b : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b.2
    have hbK : algebraMap R L (b : R) ≠ 0 := (IsFractionRing.to_map_eq_zero_iff (K := L)).not.mpr hb0
    have haK : algebraMap R L a ≠ 0 := by
      rw [← hab]
      exact mul_ne_zero u.ne_zero hbK
    have ha0 : a ≠ 0 := fun h => haK (by rw [h, map_zero])
    let r : R := a * (b : R)
    have hr0 : r ≠ 0 := mul_ne_zero ha0 hb0
    have hr : algebraMap R L r ≠ 0 := (IsFractionRing.to_map_eq_zero_iff (K := L)).not.mpr hr0
    let ru : Lˣ := Units.mk0 (algebraMap R L r) hr
    let bu : Lˣ := Units.mk0 (algebraMap R L (b : R)) hbK
    have hru_eq : u * bu ^ 2 = ru := by
      ext
      calc
        (u : L) * (algebraMap R L (b : R)) ^ 2
          = ((u : L) * algebraMap R L (b : R)) * algebraMap R L (b : R) := by ring
        _ = algebraMap R L a * algebraMap R L (b : R) := by rw [hab]
        _ = algebraMap R L r := (map_mul (algebraMap R L) a (b : R)).symm
    have hc_ru : (c : SqCl L) = sqCl ru := by
      rw [← hu]
      change QuotientGroup.mk u = QuotientGroup.mk ru
      rw [QuotientGroup.eq]
      refine ⟨bu, ?_⟩
      simp only [powMonoidHom_apply, ← hru_eq, inv_mul_cancel_left]
    let I : Ideal R := Ideal.span {r}
    have hI : I ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hr0
    let e : IsDedekindDomain.HeightOneSpectrum R → ℕ :=
      fun v => (Associates.mk v.asIdeal).count (Associates.mk I).factors
    have he_even : ∀ v : IsDedekindDomain.HeightOneSpectrum R, (e v / 2) * 2 = e v := by
      intro v
      have hval1 : (↑(v.valuationOfNeZero ru) : WithZero (Multiplicative ℤ)) =
          WithZero.exp (-(e v : ℤ)) := by
        rw [IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq]
        change (v.valuation L) (algebraMap R L r) = WithZero.exp (-(e v : ℤ))
        rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
          IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg v hr0]
      have hval2 : Multiplicative.toAdd (v.valuationOfNeZero ru) = -(e v : ℤ) :=
        WithZero.exp_inj.mp hval1
      have hmod : v.valuationOfNeZeroMod 2 (QuotientGroup.mk ru) = 1 := by
        have hc_mem := c.2 v (Set.notMem_empty v)
        rwa [hc_ru] at hc_mem
      have hmod_add : ((Multiplicative.toAdd (v.valuationOfNeZero ru) : ℤ) : ZMod 2) = 0 :=
        congr_arg Multiplicative.toAdd hmod
      rw [hval2, Int.cast_neg, Int.cast_natCast, neg_eq_zero] at hmod_add
      have hdvd : 2 ∣ e v := (ZMod.natCast_eq_zero_iff (e v) 2).mp hmod_add
      exact Nat.div_mul_cancel hdvd
    let f : IsDedekindDomain.HeightOneSpectrum R → Ideal R := fun v => v.asIdeal ^ (e v / 2)
    have hf_sq : ∀ v : IsDedekindDomain.HeightOneSpectrum R, f v ^ 2 = v.maxPowDividing I := by
      intro v
      dsimp only [f, IsDedekindDomain.HeightOneSpectrum.maxPowDividing]
      rw [← pow_mul, he_even v]
    have hf_supp : Function.mulSupport f ⊆
        Function.mulSupport (fun v : IsDedekindDomain.HeightOneSpectrum R => v.maxPowDividing I) := by
      intro v hv
      rw [Function.mem_mulSupport] at hv ⊢
      intro hmax
      apply hv
      have hsq_top : f v * f v = ⊤ := by
        rw [← sq, hf_sq v, hmax, Ideal.one_eq_top]
      have hle : (⊤ : Ideal R) ≤ f v := by
        rw [← hsq_top]
        exact Ideal.mul_le_left
      exact (top_unique hle).trans Ideal.one_eq_top.symm
    have hf_fin : (Function.mulSupport f).Finite :=
      (Ideal.finite_mulSupport hI).subset hf_supp
    let J0 : Ideal R := ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum R, f v
    have hJ0_sq : I = J0 ^ 2 := by
      calc
        I = ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum R, v.maxPowDividing I :=
          (Ideal.finprod_heightOneSpectrum_factorization hI).symm
        _ = ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum R, f v ^ 2 := by
          simp only [hf_sq]
        _ = J0 ^ 2 := (finprod_pow hf_fin 2).symm
    have hJ0_ne : J0 ≠ 0 := by
      intro h0
      apply hI
      rw [hJ0_sq, h0, zero_pow (by decide)]
    exact ⟨r, hr, ⟨J0, mem_nonZeroDivisors_of_ne_zero hJ0_ne⟩, hc_ru, hJ0_sq⟩
  
  have hcl_fiber : ∀ (r₁ r₂ : R) (hr₁ : algebraMap R L r₁ ≠ 0) (hr₂ : algebraMap R L r₂ ≠ 0)
      (J₁ J₂ : nonZeroDivisors (Ideal R)),
      Ideal.span {r₁} = (J₁ : Ideal R) ^ 2 →
      Ideal.span {r₂} = (J₂ : Ideal R) ^ 2 →
      ClassGroup.mk0 J₁ = ClassGroup.mk0 J₂ →
      ∃ ε : Rˣ,
        sqCl (Units.mk0 (algebraMap R L r₁) hr₁) =
          sqCl (Units.mk0 (algebraMap R L r₂) hr₂) *
            sqCl (Units.map (algebraMap R L).toMonoidHom ε) := by
    intro r₁ r₂ hr₁ hr₂ J₁ J₂ hJ₁ hJ₂ hcl
    obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp hcl
    have hsq_ideal : Ideal.span {x ^ 2 * r₁} = Ideal.span {y ^ 2 * r₂} := by
      have h2 := congr_arg (fun I : Ideal R => I ^ 2) hxy
      dsimp only at h2
      rw [mul_pow, mul_pow, ← hJ₁, ← hJ₂, sq (Ideal.span {x}), sq (Ideal.span {y}),
        Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton,
        Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton,
        ← sq x, ← sq y] at h2
      exact h2
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hsq_ideal
    refine ⟨u⁻¹, ?_⟩
    have hxK : algebraMap R L x ≠ 0 := (IsFractionRing.to_map_eq_zero_iff (K := L)).not.mpr hx
    have hyK : algebraMap R L y ≠ 0 := (IsFractionRing.to_map_eq_zero_iff (K := L)).not.mpr hy
    let u₁ := Units.mk0 (algebraMap R L r₁) hr₁
    let u₂ := Units.mk0 (algebraMap R L r₂) hr₂
    let xu := Units.mk0 (algebraMap R L x) hxK
    let yu := Units.mk0 (algebraMap R L y) hyK
    let uu := Units.map (algebraMap R L).toMonoidHom u
    have hu_units : xu ^ 2 * u₁ * uu = yu ^ 2 * u₂ := by
      ext
      have huK := congr_arg (algebraMap R L) hu
      simpa [u₁, u₂, xu, yu, uu, map_mul, map_pow] using huK
    change QuotientGroup.mk u₁ = QuotientGroup.mk u₂ * QuotientGroup.mk (uu⁻¹)
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
    refine ⟨xu * yu⁻¹, ?_⟩
    simp only [powMonoidHom_apply]
    rw [eq_inv_mul_iff_mul_eq, mul_pow, inv_pow, ← mul_assoc, mul_inv_eq_iff_eq_mul,
      mul_right_comm u₂ (uu⁻¹) (yu ^ 2), eq_mul_inv_iff_mul_eq]
    calc
      u₁ * xu ^ 2 * uu = xu ^ 2 * u₁ * uu := by rw [mul_comm u₁ (xu ^ 2)]
      _ = yu ^ 2 * u₂ := hu_units
      _ = u₂ * yu ^ 2 := mul_comm _ _
  
  choose r hr J hrc hJ using hex_rep
  let cl : ↥S_0 → ClassGroup R := fun c => ClassGroup.mk0 (J c)
  choose rep hrep_cl using fun γ : Set.range cl => γ.2
  haveI : Fact (0 < 2) := ⟨by decide⟩
  let Ψ : Set.range cl × (Rˣ ⧸ (powMonoidHom 2 : Rˣ →* Rˣ).range) → ↥S_0 :=
    fun p => rep p.1 * IsDedekindDomain.selmerGroup.fromUnitLift p.2
  have hΨ_surj : Function.Surjective Ψ := by
    intro c
    let γ : Set.range cl := ⟨cl c, c, rfl⟩
    have hcl_eq : ClassGroup.mk0 (J c) = ClassGroup.mk0 (J (rep γ)) := (hrep_cl γ).symm
    obtain ⟨ε, hε⟩ := hcl_fiber
      (r c) (r (rep γ)) (hr c) (hr (rep γ)) (J c) (J (rep γ))
      (hJ c) (hJ (rep γ)) hcl_eq
    refine ⟨(γ, QuotientGroup.mk ε), ?_⟩
    ext
    change (rep γ : SqCl L) * sqCl (Units.map (algebraMap R L).toMonoidHom ε) = (c : SqCl L)
    rw [hrc c, hrc (rep γ), hε]
  haveI h0 : Finite ↥S_0 := Finite.of_surjective Ψ hΨ_surj
  let Φ := IsDedekindDomain.selmerGroup.valuation (R := R) (K := L) (S := T) (n := 2)
  haveI : Finite ↥T := hT.to_subtype
  haveI : Finite (↥S_T ⧸ Φ.ker) := Finite.of_injective _ (QuotientGroup.kerLift_injective Φ)
  have hker : Φ.ker = S_0.subgroupOf S_T := IsDedekindDomain.selmerGroup.valuation_ker_eq
  have heq : ↥(S_0.subgroupOf S_T) ≃* ↥S_0 :=
    Subgroup.subgroupOfEquivOfLe (IsDedekindDomain.selmerGroup.monotone (Set.empty_subset T))
  haveI : Finite ↥(S_0.subgroupOf S_T) := Finite.of_equiv ↥S_0 heq.symm.toEquiv
  haveI : Finite ↥Φ.ker := by rw [hker]; infer_instance
  haveI : Finite ↥S_T :=
    Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (α := ↥S_T) (s := Φ.ker)).symm
  exact Set.toFinite (S_T : Set (SqCl L))

theorem galois_descent_from_kummer {K L : Type u} [Field K] [CharZero K] [DecidableEq K]
    [Field L] [CharZero L] [DecidableEq L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (E : WeierstrassCurve K)
    (e₁ e₂ e₃ : L)
    (hcubic : ∀ x : L, 4 * x ^ 3 + (E.baseChange L).b₂ * x ^ 2 +
      2 * (E.baseChange L).b₄ * x + (E.baseChange L).b₆ =
      4 * (x - e₁) * (x - e₂) * (x - e₃))
    (hmul : ∀ P₁ P₂ : (E.baseChange L).toAffine.Point,
      P₁ + P₁ ≠ 0 → P₂ + P₂ ≠ 0 → (P₁ + P₂) + (P₁ + P₂) ≠ 0 →
      pointKummer (E.baseChange L) e₁ e₂ (P₁ + P₂) =
        pointKummer (E.baseChange L) e₁ e₂ P₁ * pointKummer (E.baseChange L) e₁ e₂ P₂)
    (hhalve : ∀ P : (E.baseChange L).toAffine.Point,
      P + P ≠ 0 → pointKummer (E.baseChange L) e₁ e₂ P = (1, 1) →
      ∃ P' : (E.baseChange L).toAffine.Point, P = P' + P')
    (hfin : (Set.range (pointKummer (E.baseChange L) e₁ e₂)).Finite) :
    ∃ Q₀ : Set E.toAffine.Point, Q₀.Finite ∧
      ∀ P : E.toAffine.Point, ∃ q ∈ Q₀, ∃ P' : E.toAffine.Point, P = P' + P' + q :=
by
  classical
  let W := E.baseChange L
  
  have hT₂ : {P : W.toAffine.Point | P + P = 0}.Finite := by
    let ψ : W.toAffine.Point → Option (L × L) := fun P =>
      match P with
      | .zero => none
      | @WeierstrassCurve.Affine.Point.some _ _ _ x y _ => some (x, y)
    have hψ_inj : Function.Injective ψ := by
      intro P₁ P₂ h
      cases P₁ <;> cases P₂
      · rfl
      · contradiction
      · contradiction
      · simp only [ψ, Option.some.injEq, Prod.mk.injEq] at h
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        exact h
    let yW : L → L := fun x => -(W.a₁ * x + W.a₃) / 2
    let S : Set (Option (L × L)) :=
      {none, some (e₁, yW e₁), some (e₂, yW e₂), some (e₃, yW e₃)}
    have hS : S.Finite := (((Set.finite_singleton _).insert _).insert _).insert _
    refine Set.Finite.of_finite_image (hS.subset ?_) hψ_inj.injOn
    rintro _ ⟨P, hP, rfl⟩
    cases P with
    | zero =>
      simp [ψ, S]
    | @some x y hns =>
      simp only [Set.mem_setOf_eq] at hP
      have hy_eq : y = W.toAffine.negY x y := by
        by_contra hne
        have hadd := WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁ := hns) hne
        rw [hP] at hadd
        cases hadd
      have hy_lin : 2 * y + W.a₁ * x + W.a₃ = 0 := by
        have hneg : W.toAffine.negY x y = -y - W.a₁ * x - W.a₃ := rfl
        linear_combination hy_eq.trans hneg
      have hy_val : y = yW x := by
        dsimp [yW]
        linear_combination hy_lin / 2
      have heq := (W.toAffine.equation_iff x y).mp hns.1
      have hb2 : W.b₂ = W.a₁ ^ 2 + 4 * W.a₂ := rfl
      have hb4 : W.b₄ = 2 * W.a₄ + W.a₁ * W.a₃ := rfl
      have hb6 : W.b₆ = W.a₃ ^ 2 + 4 * W.a₆ := rfl
      have hsq : (2 * y + W.a₁ * x + W.a₃) ^ 2 =
          4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
        rw [hb2, hb4, hb6]
        linear_combination 4 * heq
      have hprod : 4 * (x - e₁) * (x - e₂) * (x - e₃) = 0 := by
        rw [← hcubic x, ← hsq, hy_lin, sq, mul_zero]
      have h4 : (4 : L) ≠ 0 := by norm_num
      change some (x, y) ∈ S
      rw [hy_val]
      rcases mul_eq_zero.mp hprod with h12 | h3
      · rcases mul_eq_zero.mp h12 with h1 | h2
        · rcases mul_eq_zero.mp h1 with h40 | h1'
          · exact absurd h40 h4
          · rw [sub_eq_zero.mp h1']; simp [S]
        · rw [sub_eq_zero.mp h2]; simp [S]
      · rw [sub_eq_zero.mp h3]; simp [S]
  
  have hQL : ∃ QL : Set W.toAffine.Point, QL.Finite ∧
      ∀ P : W.toAffine.Point, ∃ q ∈ QL, ∃ P' : W.toAffine.Point, P = P' + P' + q := by
    have hk_neg : ∀ P : W.toAffine.Point, pointKummer W e₁ e₂ (-P) = pointKummer W e₁ e₂ P := by
      intro P
      cases P with
      | zero =>
        change pointKummer W e₁ e₂ (-(0 : W.toAffine.Point)) = pointKummer W e₁ e₂ 0
        rw [neg_zero]
      | @some x y hns =>
        rw [WeierstrassCurve.Affine.Point.neg_some hns]
        rfl
    have hsq_one : ∀ a : SqCl L, a * a = 1 := by
      intro a
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective a
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
      exact ⟨u, sq u⟩
    have hprod_one : ∀ c : SqCl L × SqCl L, c * c = (1, 1) := by
      rintro ⟨c₁, c₂⟩
      exact Prod.ext (hsq_one c₁) (hsq_one c₂)
    let T₂ : Set W.toAffine.Point := {P | P + P = 0}
    let U : Set W.toAffine.Point := {P | P + P ≠ 0}
    let C : Set (SqCl L × SqCl L) := pointKummer W e₁ e₂ '' U
    have hC : C.Finite := hfin.subset (Set.image_subset_range _ _)
    haveI : Fintype C := hC.fintype
    let r : C → W.toAffine.Point := fun c => Classical.choose c.2
    have hr_mem : ∀ c : C, r c ∈ U := fun c => (Classical.choose_spec c.2).1
    have hr_eq : ∀ c : C, pointKummer W e₁ e₂ (r c) = c.1 := fun c => (Classical.choose_spec c.2).2
    let R₀ : Set W.toAffine.Point := {0} ∪ Set.range r
    have hR₀ : R₀.Finite := (Set.finite_singleton 0).union (Set.finite_range r)
    let QL : Set W.toAffine.Point := Set.image2 (· + ·) R₀ T₂
    refine ⟨QL, Set.Finite.image2 _ hR₀ hT₂, ?_⟩
    intro P
    by_cases hP : P + P = 0
    · refine ⟨0 + P, Set.mem_image2_of_mem (Set.mem_union_left _ (Set.mem_singleton 0)) hP, 0, ?_⟩
      abel
    · let c : C := ⟨pointKummer W e₁ e₂ P, P, hP, rfl⟩
      let rc := r c
      have hrc_mem : rc ∈ R₀ := Set.mem_union_right _ ⟨c, rfl⟩
      have hrc_ne : rc + rc ≠ 0 := hr_mem c
      have hrc_k : pointKummer W e₁ e₂ rc = pointKummer W e₁ e₂ P := hr_eq c
      let D := P + (-rc)
      by_cases hD : D + D = 0
      · refine ⟨rc + D, Set.mem_image2_of_mem hrc_mem hD, 0, ?_⟩
        dsimp [D]
        abel
      · have hneg_rc : (-rc) + (-rc) ≠ 0 := by
          rw [← neg_add, neg_ne_zero]
          exact hrc_ne
        have hkD : pointKummer W e₁ e₂ D = (1, 1) := by
          dsimp [D]
          rw [hmul P (-rc) hP hneg_rc hD, hk_neg, hrc_k]
          exact hprod_one (pointKummer W e₁ e₂ P)
        obtain ⟨P', hP'⟩ := hhalve D hD hkD
        have h0T₂ : (0 : W.toAffine.Point) ∈ T₂ := by simp [T₂]
        refine ⟨rc + 0, Set.mem_image2_of_mem hrc_mem h0T₂, P', ?_⟩
        rw [← hP']
        dsimp [D]
        abel
  
  have hfix_surj : ∀ Q : W.toAffine.Point,
      (∀ σ : L ≃ₐ[K] L, WeierstrassCurve.Affine.Point.map (W' := E.toAffine) σ.toAlgHom Q = Q) →
      ∃ P : E.toAffine.Point,
        WeierstrassCurve.Affine.Point.baseChange K L (W' := E.toAffine) P = Q := by
    intro Q hfix
    cases Q with
    | zero =>
      exact ⟨0, map_zero _⟩
    | @some xL yL hL =>
      have hx_fix : ∀ σ : L ≃ₐ[K] L, σ xL = xL := by
        intro σ
        have hσ := hfix σ
        rw [WeierstrassCurve.Affine.Point.map_some (W' := E.toAffine) σ.toAlgHom hL,
          WeierstrassCurve.Affine.Point.some.injEq] at hσ
        exact hσ.1
      have hy_fix : ∀ σ : L ≃ₐ[K] L, σ yL = yL := by
        intro σ
        have hσ := hfix σ
        rw [WeierstrassCurve.Affine.Point.map_some (W' := E.toAffine) σ.toAlgHom hL,
          WeierstrassCurve.Affine.Point.some.injEq] at hσ
        exact hσ.2
      obtain ⟨xK, hxK⟩ := IntermediateField.mem_bot.mp ((IsGalois.mem_bot_iff_fixed xL).mpr hx_fix)
      obtain ⟨yK, hyK⟩ := IntermediateField.mem_bot.mp ((IsGalois.mem_bot_iff_fixed yL).mpr hy_fix)
      have hL' : W.toAffine.Nonsingular (Algebra.ofId K L xK) (Algebra.ofId K L yK) := by
        change W.toAffine.Nonsingular (algebraMap K L xK) (algebraMap K L yK)
        rwa [hxK, hyK]
      have hK : E.toAffine.Nonsingular xK yK :=
        (WeierstrassCurve.Affine.baseChange_nonsingular (W := E.toAffine) (f := Algebra.ofId K L)
          xK yK (RingHom.injective (algebraMap K L))).mp hL'
      refine ⟨WeierstrassCurve.Affine.Point.some hK, ?_⟩
      change WeierstrassCurve.Affine.Point.map (W' := E.toAffine) (Algebra.ofId K L)
        (WeierstrassCurve.Affine.Point.some hK) = _
      rw [WeierstrassCurve.Affine.Point.map_some (W' := E.toAffine) (Algebra.ofId K L) hK,
        WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hxK, hyK⟩
  
  let ι : E.toAffine.Point →+ W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.baseChange K L (W' := E.toAffine)
  have hι : Function.Injective ι :=
    WeierstrassCurve.Affine.Point.map_injective (W' := E.toAffine) (Algebra.ofId K L)
  let ρ : (L ≃ₐ[K] L) → (W.toAffine.Point →+ W.toAffine.Point) :=
    fun σ => WeierstrassCurve.Affine.Point.map (W' := E.toAffine) σ.toAlgHom
  have hfix_im : ∀ (σ : L ≃ₐ[K] L) (P : E.toAffine.Point), ρ σ (ι P) = ι P :=
    fun σ P => WeierstrassCurve.Affine.Point.map_baseChange (W' := E.toAffine) σ.toAlgHom P
  haveI : Finite (L ≃ₐ[K] L) := Finite.of_fintype (L ≃ₐ[K] L)
  obtain ⟨QL, hQL_fin, hQL_mem⟩ := hQL
  let q : E.toAffine.Point → W.toAffine.Point := fun a => Classical.choose (hQL_mem (ι a))
  have hq_mem : ∀ a : E.toAffine.Point, q a ∈ QL :=
    fun a => (Classical.choose_spec (hQL_mem (ι a))).1
  let Q : E.toAffine.Point → W.toAffine.Point :=
    fun a => Classical.choose (Classical.choose_spec (hQL_mem (ι a))).2
  have hQ_eq : ∀ a : E.toAffine.Point, ι a = Q a + Q a + q a :=
    fun a => Classical.choose_spec (Classical.choose_spec (hQL_mem (ι a))).2
  let r : E.toAffine.Point → Set.range q := fun a => ⟨q a, a, rfl⟩
  let a₀ : Set.range q → E.toAffine.Point := fun x => Classical.choose x.2
  have ha₀_eq : ∀ a : E.toAffine.Point, q (a₀ (r a)) = q a :=
    fun a => Classical.choose_spec (r a).2
  let D : E.toAffine.Point → W.toAffine.Point := fun a => Q a - Q (a₀ (r a))
  have hD_two : ∀ a : E.toAffine.Point, D a + D a = ι (a - a₀ (r a)) := by
    intro a
    rw [map_sub, hQ_eq a, hQ_eq (a₀ (r a)), ha₀_eq a]
    dsimp [D]
    abel
  let c : E.toAffine.Point → ((L ≃ₐ[K] L) → W.toAffine.Point) := fun a g => ρ g (D a) - D a
  have hc_mem : ∀ (a : E.toAffine.Point) (g : L ≃ₐ[K] L),
      c a g ∈ {t : W.toAffine.Point | t + t = 0} := by
    intro a g
    simp only [Set.mem_setOf_eq, c]
    have h1 : (ρ g (D a) - D a) + (ρ g (D a) - D a) = ρ g (D a + D a) - (D a + D a) := by
      rw [map_add]
      abel
    rw [h1, hD_two a, hfix_im g (a - a₀ (r a)), sub_self]
  let Φ : E.toAffine.Point → W.toAffine.Point × ((L ≃ₐ[K] L) → W.toAffine.Point) :=
    fun a => (q a, c a)
  have hΦ_range : (Set.range Φ).Finite := by
    refine (hQL_fin.prod (Set.Finite.pi (fun _ : L ≃ₐ[K] L => hT₂))).subset ?_
    rintro _ ⟨a, rfl⟩
    exact ⟨hq_mem a, fun g _ => hc_mem a g⟩
  haveI : Fintype (Set.range Φ) := hΦ_range.fintype
  let rep : Set.range Φ → E.toAffine.Point := fun y => Classical.choose y.2
  have hrep_eq : ∀ y : Set.range Φ, Φ (rep y) = y.1 := fun y => Classical.choose_spec y.2
  let Q₀ : Set E.toAffine.Point := Set.range rep
  refine ⟨Q₀, Set.finite_range rep, ?_⟩
  intro a
  let y : Set.range Φ := ⟨Φ a, a, rfl⟩
  let q₀ := rep y
  have hq₀_mem : q₀ ∈ Q₀ := ⟨y, rfl⟩
  have hΦ_eq : Φ a = Φ q₀ := (hrep_eq y).symm
  have hq_eq : q a = q q₀ := congrArg Prod.fst hΦ_eq
  have hc_eq : c a = c q₀ := congrArg Prod.snd hΦ_eq
  have hr_eq : r a = r q₀ := Subtype.ext hq_eq
  have ha₀_same : a₀ (r a) = a₀ (r q₀) := congrArg a₀ hr_eq
  have hdiff_two : (D a - D q₀) + (D a - D q₀) = ι a - ι q₀ := by
    have h1 : (D a - D q₀) + (D a - D q₀) = (D a + D a) - (D q₀ + D q₀) := by abel
    rw [h1, hD_two a, hD_two q₀, ha₀_same, map_sub, map_sub]
    abel
  have hdiff_fix : ∀ g : L ≃ₐ[K] L, ρ g (D a - D q₀) = D a - D q₀ := by
    intro g
    have hcg : c a g = c q₀ g := congrFun hc_eq g
    dsimp [c] at hcg
    rw [map_sub]
    exact sub_eq_sub_iff_sub_eq_sub.mp hcg
  obtain ⟨a', ha'⟩ := hfix_surj (D a - D q₀) hdiff_fix
  change ι a' = D a - D q₀ at ha'
  refine ⟨q₀, hq₀_mem, a', hι ?_⟩
  rw [map_add, map_add, ha', hdiff_two]
  abel

theorem weak_mordell_weil_two {K : Type u} [Field K] [NumberField K] [DecidableEq K]
    (E : WeierstrassCurve K) (hE : E.IsElliptic) :
    ∃ Q₀ : Set E.toAffine.Point, Q₀.Finite ∧
      ∀ P : E.toAffine.Point, ∃ q ∈ Q₀, ∃ P' : E.toAffine.Point, P = P' + P' + q :=
by
  let L := (twoTorsionPoly E).SplittingField
  haveI : IsGalois K L := IsGalois.mk
  haveI : NumberField L := @NumberField.mk L _ inferInstance (Module.Finite.trans K L)
  classical
  obtain ⟨e₁, e₂, e₃, h₁₂, h₁₃, h₂₃, hcubic⟩ := exists_three_roots_in_splittingField E hE
  obtain ⟨T, hT_fin, hT_mem⟩ := kummer_image_subset_selmerGroup (E.baseChange L) e₁ e₂ e₃ h₁₂ h₁₃ h₂₃ hcubic
  have hS_fin := selmerGroup_two_finite T hT_fin
  have hrange_fin : (Set.range (pointKummer (E.baseChange L) e₁ e₂)).Finite :=
    (hS_fin.prod hS_fin).subset (by rintro _ ⟨P, rfl⟩; exact hT_mem P)
  exact galois_descent_from_kummer E e₁ e₂ e₃ hcubic
    (kummer_mul_of_not_two_torsion (E.baseChange L) e₁ e₂ e₃ hcubic)
    (halving_of_kummer_eq_one (E.baseChange L) e₁ e₂ e₃ h₁₂ h₁₃ h₂₃ hcubic)
    hrange_fin

theorem mordell_weil {K : Type u} [Field K] [NumberField K] [DecidableEq K]
    (E : WeierstrassCurve K) (hE : E.IsElliptic) : AddGroup.FG E.toAffine.Point :=
by
  exact abstract_descent_fg (weierstrassHeight E)
    (height_add_bound E hE)
    (height_double_bound E hE)
    (height_northcott E hE)
    (weak_mordell_weil_two E hE)
