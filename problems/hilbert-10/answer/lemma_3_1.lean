import Mathlib
import Hilbert10Defs
set_option maxHeartbeats 4000000

/-! ### Statement (originally `lemma_3_1.lean`) -/

/--
**Lemma 3.1.** Let `F` be a field of characteristic `0` and `e₁, e₂, e₃ ∈ F` distinct.
For the curve `E : y^2 = (x - e₁)(x - e₂)(x - e₃)` there is a Kummer map
`δ : E(F) → (Fˣ/Fˣ²)²` which is a homomorphism with kernel `2E(F)` and is given
explicitly by `(x, y) ↦ (x - e₁, x - e₂)` for `P ≠ P₁, P₂`, by
`((e₁ - e₂)(e₁ - e₃), e₁ - e₂)` at `P₁ = (e₁, 0)`, and by
`(-(e₁ - e₂), -(e₁ - e₂)(e₂ - e₃))` at `P₂ = (e₂, 0)`.
-/
def sqClOf {F : Type u} [Field F] [DecidableEq F] (a : F) : SqCl F :=
  if h : a = 0 then 1 else sqCl (Units.mk0 a h)

def kummerCompX {F : Type u} [Field F] [DecidableEq F] (r₁ r₂ r₃ x : F) : SqCl F :=
  if x = r₁ then sqClOf ((r₁ - r₂) * (r₁ - r₃)) else sqClOf (x - r₁)

def kummerComp {F : Type u} [Field F] [DecidableEq F] (e₁ e₂ e₃ r₁ r₂ r₃ : F) :
    (threeRootsCurve e₁ e₂ e₃).toAffine.Point → SqCl F
  | 0 => 1
  | @WeierstrassCurve.Affine.Point.some _ _ _ x _ _ => kummerCompX r₁ r₂ r₃ x

def kummerMap {F : Type u} [Field F] [DecidableEq F] (e₁ e₂ e₃ : F)
    (P : (threeRootsCurve e₁ e₂ e₃).toAffine.Point) : SqCl F × SqCl F :=
  (kummerComp e₁ e₂ e₃ e₁ e₂ e₃ P, kummerComp e₁ e₂ e₃ e₂ e₁ e₃ P)

theorem lemma_3_1 {F : Type u} [Field F] [CharZero F] [DecidableEq F]
    (e₁ e₂ e₃ : F) (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃) :
    ∃ δ : (threeRootsCurve e₁ e₂ e₃).toAffine.Point → SqCl F × SqCl F,
      (∀ P Q, δ (P + Q) = δ P * δ Q) ∧
      (∀ P, δ P = 1 ↔ ∃ Q, P = Q + Q) ∧
      (∀ (x y : F) (h : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x y) (u₁ u₂ : Fˣ),
          x ≠ e₁ → x ≠ e₂ → (u₁ : F) = x - e₁ → (u₂ : F) = x - e₂ →
          δ (WeierstrassCurve.Affine.Point.some h) = (sqCl u₁, sqCl u₂)) ∧
      (∀ (h : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular e₁ 0) (u₁ u₂ : Fˣ),
          (u₁ : F) = (e₁ - e₂) * (e₁ - e₃) → (u₂ : F) = e₁ - e₂ →
          δ (WeierstrassCurve.Affine.Point.some h) = (sqCl u₁, sqCl u₂)) ∧
      (∀ (h : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular e₂ 0) (u₁ u₂ : Fˣ),
          (u₁ : F) = -(e₁ - e₂) → (u₂ : F) = -((e₁ - e₂) * (e₂ - e₃)) →
          δ (WeierstrassCurve.Affine.Point.some h) = (sqCl u₁, sqCl u₂)) :=
by
  have sqCl_mul_one : ∀ (z : SqCl F), z * 1 = z := by
    intro z
    induction z using Quotient.inductionOn' with
    | h u =>
      change QuotientGroup.mk u * QuotientGroup.mk 1 = QuotientGroup.mk u
      rw [← QuotientGroup.mk_mul, mul_one]
  have sqCl_one_mul : ∀ (z : SqCl F), 1 * z = z := by
    intro z
    induction z using Quotient.inductionOn' with
    | h u =>
      change QuotientGroup.mk 1 * QuotientGroup.mk u = QuotientGroup.mk u
      rw [← QuotientGroup.mk_mul, one_mul]
  have sqCl_mul_self : ∀ (z : SqCl F), z * z = 1 := by
    intro z
    induction z using Quotient.inductionOn' with
    | h u =>
      change QuotientGroup.mk u * QuotientGroup.mk u = 1
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, MonoidHom.mem_range]
      exact ⟨u, by simp [powMonoidHom_apply, sq]⟩
  have sqClOf_eq_sqCl : ∀ (a : F) (u : Fˣ), (u : F) = a → sqClOf a = sqCl u := by
    intro a u hu
    have ha : a ≠ 0 := by rw [← hu]; exact u.ne_zero
    dsimp [sqClOf]
    rw [dif_neg ha]
    congr 1
    ext
    exact hu.symm
  have sqClOf_mul : ∀ {a b : F}, a ≠ 0 → b ≠ 0 → sqClOf (a * b) = sqClOf a * sqClOf b := by
    intro a b ha hb
    have hab : a * b ≠ 0 := mul_ne_zero ha hb
    dsimp [sqClOf, sqCl]
    rw [dif_neg hab, dif_neg ha, dif_neg hb, ← QuotientGroup.mk_mul]
    congr 1
    ext
    rfl
  have sqClOf_sq : ∀ {s : F}, s ≠ 0 → sqClOf (s ^ 2) = 1 := by
    intro s hs
    have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
    dsimp [sqClOf, sqCl]
    rw [dif_neg hs2, QuotientGroup.eq_one_iff, MonoidHom.mem_range]
    refine ⟨Units.mk0 s hs, ?_⟩
    ext
    simp [powMonoidHom_apply]
  have sqClOf_eq_one_exists_sqrt : ∀ {a : F}, a ≠ 0 → sqClOf a = 1 → ∃ z : F, z ≠ 0 ∧ z ^ 2 = a := by
    intro a ha h
    dsimp [sqClOf, sqCl] at h
    rw [dif_neg ha, QuotientGroup.eq_one_iff, MonoidHom.mem_range] at h
    rcases h with ⟨u, hu⟩
    refine ⟨(u : F), u.ne_zero, ?_⟩
    have hu' : ((powMonoidHom 2 u : Fˣ) : F) = ((Units.mk0 a ha : Fˣ) : F) := by rw [hu]
    simpa [powMonoidHom_apply] using hu'
  have threeRoots_add_some_chord_rel : ∀ (x₁ y₁ x₂ y₂ : F)
      (h₁ : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x₁ y₁)
      (h₂ : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x₂ y₂),
      ¬ (x₁ = x₂ ∧ y₁ = (threeRootsCurve e₁ e₂ e₃).toAffine.negY x₂ y₂) →
      let W := (threeRootsCurve e₁ e₂ e₃).toAffine
      let ℓ := W.slope x₁ x₂ y₁ y₂
      (∃ h₃ : W.Nonsingular (W.addX x₁ x₂ ℓ) (W.addY x₁ x₂ y₁ ℓ),
        WeierstrassCurve.Affine.Point.some h₁ + WeierstrassCurve.Affine.Point.some h₂ =
          WeierstrassCurve.Affine.Point.some h₃) ∧
      ℓ ^ 2 * (x₁ - x₂) - 2 * ℓ * y₁ +
        (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 - (e₁ + e₂ + e₃) * (x₁ + x₂) + (e₁ * e₂ + e₁ * e₃ + e₂ * e₃)) = 0 := by
    intro x₁ y₁ x₂ y₂ h₁ h₂ h_not_neg W ℓ
    have eq₁ : y₁ ^ 2 = x₁ ^ 3 - (e₁ + e₂ + e₃) * x₁ ^ 2 + (e₁ * e₂ + e₁ * e₃ + e₂ * e₃) * x₁ - e₁ * e₂ * e₃ := by
      have h := (WeierstrassCurve.Affine.equation_iff x₁ y₁).mp h₁.left
      dsimp [W, threeRootsCurve] at h
      linear_combination h
    have eq₂ : y₂ ^ 2 = x₂ ^ 3 - (e₁ + e₂ + e₃) * x₂ ^ 2 + (e₁ * e₂ + e₁ * e₃ + e₂ * e₃) * x₂ - e₁ * e₂ * e₃ := by
      have h := (WeierstrassCurve.Affine.equation_iff x₂ y₂).mp h₂.left
      dsimp [W, threeRootsCurve] at h
      linear_combination h
    by_cases hx : x₁ = x₂
    · subst hx
      have hy : y₁ ≠ W.negY x₁ y₂ := fun h => h_not_neg ⟨rfl, h⟩
      refine ⟨⟨_, WeierstrassCurve.Affine.Point.add_of_Y_ne (h₁ := h₁) (h₂ := h₂) hy⟩, ?_⟩
      have h_negY₂ : W.negY x₁ y₂ = -y₂ := by
        dsimp [WeierstrassCurve.Affine.negY, W, threeRootsCurve]
        ring
      have h_negY₁ : W.negY x₁ y₁ = -y₁ := by
        dsimp [WeierstrassCurve.Affine.negY, W, threeRootsCurve]
        ring
      have hy_sum_ne : y₁ + y₂ ≠ 0 := by
        intro h_sum
        apply hy
        rw [h_negY₂]
        linear_combination h_sum
      have hy_diff : (y₁ - y₂) * (y₁ + y₂) = 0 := by
        linear_combination eq₁ - eq₂
      have hy_eq : y₁ = y₂ := by
        cases mul_eq_zero.mp hy_diff with
        | inl h => linear_combination h
        | inr h => exact absurd h hy_sum_ne
      have hy₁_ne : y₁ ≠ W.negY x₁ y₁ := by
        rw [hy_eq] at hy
        rw [hy_eq]
        exact hy
      have h_slope := WeierstrassCurve.Affine.slope_of_Y_ne (W := W) rfl hy
      change ℓ = _ at h_slope
      have h_denom : y₁ - W.negY x₁ y₁ = 2 * y₁ := by
        rw [h_negY₁]; ring
      have h_slope' : ℓ * (2 * y₁) = 3 * x₁ ^ 2 - 2 * (e₁ + e₂ + e₃) * x₁ + (e₁ * e₂ + e₁ * e₃ + e₂ * e₃) := by
        rw [← h_denom, h_slope, div_mul_cancel₀ _ (sub_ne_zero.mpr hy₁_ne)]
        dsimp [W, threeRootsCurve]
        ring
      linear_combination -h_slope'
    · refine ⟨⟨_, WeierstrassCurve.Affine.Point.add_of_X_ne (h₁ := h₁) (h₂ := h₂) hx⟩, ?_⟩
      have h_slope := WeierstrassCurve.Affine.slope_of_X_ne (W := W) hx (y₁ := y₁) (y₂ := y₂)
      change ℓ = (y₁ - y₂) / (x₁ - x₂) at h_slope
      have hx_sub : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
      have hℓ : ℓ * (x₁ - x₂) = y₁ - y₂ := by
        rw [h_slope, div_mul_cancel₀ _ hx_sub]
      have h_prod : (x₁ - x₂) * (ℓ ^ 2 * (x₁ - x₂) - 2 * ℓ * y₁ +
          (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 - (e₁ + e₂ + e₃) * (x₁ + x₂) + (e₁ * e₂ + e₁ * e₃ + e₂ * e₃))) = 0 := by
        linear_combination (ℓ * (x₁ - x₂) - y₁ - y₂) * hℓ - eq₁ + eq₂
      exact (mul_eq_zero.mp h_prod).resolve_left hx_sub
  have kummerCompX_addX_eq_mul : ∀ (r₁ r₂ r₃ x₁ y₁ x₂ ℓ x₃ : F),
      r₁ ≠ r₂ → r₁ ≠ r₃ →
      y₁ ^ 2 = (x₁ - r₁) * (x₁ - r₂) * (x₁ - r₃) →
      x₃ = ℓ ^ 2 + (r₁ + r₂ + r₃) - x₁ - x₂ →
      ℓ ^ 2 * (x₁ - x₂) - 2 * ℓ * y₁ +
        (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 - (r₁ + r₂ + r₃) * (x₁ + x₂) + (r₁ * r₂ + r₁ * r₃ + r₂ * r₃)) = 0 →
      kummerCompX r₁ r₂ r₃ x₃ = kummerCompX r₁ r₂ r₃ x₁ * kummerCompX r₁ r₂ r₃ x₂ := by
    intro r₁ r₂ r₃ x₁ y₁ x₂ ℓ x₃ hr₁₂ hr₁₃ hy₁ hx₃ hM
    have h_rel1 : (x₁ - r₁) * (x₂ - r₁) * (x₃ - r₁) = (ℓ * (x₁ - r₁) - y₁) ^ 2 := by
      linear_combination -hy₁ + (x₁ - r₁) * (x₂ - r₁) * hx₃ - (x₁ - r₁) * hM
    have h_rel2 : (x₁ - r₁) * (x₂ - r₁) + (x₁ - r₁) * (x₃ - r₁) + (x₂ - r₁) * (x₃ - r₁) =
        (r₁ - r₂) * (r₁ - r₃) + 2 * ℓ * (ℓ * (x₁ - r₁) - y₁) := by
      linear_combination (x₁ + x₂ - 2 * r₁) * hx₃ - hM
    have hd : (r₁ - r₂) * (r₁ - r₃) ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hr₁₂) (sub_ne_zero.mpr hr₁₃)
    have h_prod_eq : ∀ {a b : F}, a * b = (r₁ - r₂) * (r₁ - r₃) →
        a ≠ 0 ∧ b ≠ 0 ∧ sqClOf b = sqClOf ((r₁ - r₂) * (r₁ - r₃)) * sqClOf a ∧
          sqClOf b = sqClOf a * sqClOf ((r₁ - r₂) * (r₁ - r₃)) ∧
          sqClOf ((r₁ - r₂) * (r₁ - r₃)) = sqClOf a * sqClOf b := by
      intro a b hab
      have hab_ne : a * b ≠ 0 := by rw [hab]; exact hd
      have ha : a ≠ 0 := left_ne_zero_of_mul hab_ne
      have hb : b ≠ 0 := right_ne_zero_of_mul hab_ne
      have hmul : sqClOf a * sqClOf b = sqClOf ((r₁ - r₂) * (r₁ - r₃)) := by
        rw [← sqClOf_mul ha hb, hab]
      have h1 : sqClOf b = sqClOf ((r₁ - r₂) * (r₁ - r₃)) * sqClOf a := by
        rw [← hmul, mul_comm (sqClOf a) (sqClOf b), mul_assoc, sqCl_mul_self, sqCl_mul_one]
      have h2 : sqClOf b = sqClOf a * sqClOf ((r₁ - r₂) * (r₁ - r₃)) := by
        rw [mul_comm (sqClOf a), h1]
      exact ⟨ha, hb, h1, h2, hmul.symm⟩
    by_cases hx₁ : x₁ = r₁
    · have hs : ℓ * (x₁ - r₁) - y₁ = 0 := by
        have h0 : (ℓ * (x₁ - r₁) - y₁) ^ 2 = 0 := by
          rw [← h_rel1, hx₁]; ring
        exact eq_zero_of_pow_eq_zero h0
      have h_prod : (x₂ - r₁) * (x₃ - r₁) = (r₁ - r₂) * (r₁ - r₃) := by
        rw [hs, hx₁] at h_rel2
        linear_combination h_rel2
      rcases h_prod_eq h_prod with ⟨hx₂_sub, hx₃_sub, h1, _, _⟩
      have hx₂ : x₂ ≠ r₁ := sub_ne_zero.mp hx₂_sub
      have hx₃' : x₃ ≠ r₁ := sub_ne_zero.mp hx₃_sub
      dsimp [kummerCompX]
      rw [if_pos hx₁, if_neg hx₂, if_neg hx₃']
      exact h1
    · by_cases hx₂ : x₂ = r₁
      · have hs : ℓ * (x₁ - r₁) - y₁ = 0 := by
          have h0 : (ℓ * (x₁ - r₁) - y₁) ^ 2 = 0 := by
            rw [← h_rel1, hx₂]; ring
          exact eq_zero_of_pow_eq_zero h0
        have h_prod : (x₁ - r₁) * (x₃ - r₁) = (r₁ - r₂) * (r₁ - r₃) := by
          rw [hs, hx₂] at h_rel2
          linear_combination h_rel2
        rcases h_prod_eq h_prod with ⟨_, hx₃_sub, _, h2, _⟩
        have hx₃' : x₃ ≠ r₁ := sub_ne_zero.mp hx₃_sub
        dsimp [kummerCompX]
        rw [if_neg hx₁, if_pos hx₂, if_neg hx₃']
        exact h2
      · by_cases hx₃' : x₃ = r₁
        · have hs : ℓ * (x₁ - r₁) - y₁ = 0 := by
            have h0 : (ℓ * (x₁ - r₁) - y₁) ^ 2 = 0 := by
              rw [← h_rel1, hx₃']; ring
            exact eq_zero_of_pow_eq_zero h0
          have h_prod : (x₁ - r₁) * (x₂ - r₁) = (r₁ - r₂) * (r₁ - r₃) := by
            rw [hs, hx₃'] at h_rel2
            linear_combination h_rel2
          rcases h_prod_eq h_prod with ⟨_, _, _, _, h3⟩
          dsimp [kummerCompX]
          rw [if_neg hx₁, if_neg hx₂, if_pos hx₃']
          exact h3
        · have hu₁ : x₁ - r₁ ≠ 0 := sub_ne_zero.mpr hx₁
          have hu₂ : x₂ - r₁ ≠ 0 := sub_ne_zero.mpr hx₂
          have hu₃ : x₃ - r₁ ≠ 0 := sub_ne_zero.mpr hx₃'
          have hs2 : (ℓ * (x₁ - r₁) - y₁) ^ 2 ≠ 0 := by
            rw [← h_rel1]
            exact mul_ne_zero (mul_ne_zero hu₁ hu₂) hu₃
          have hs : ℓ * (x₁ - r₁) - y₁ ≠ 0 := fun h => hs2 (by rw [h, zero_pow two_ne_zero])
          have h_sq : sqClOf (x₁ - r₁) * sqClOf (x₂ - r₁) * sqClOf (x₃ - r₁) = 1 := by
            rw [← sqClOf_mul hu₁ hu₂, ← sqClOf_mul (mul_ne_zero hu₁ hu₂) hu₃, h_rel1, sqClOf_sq hs]
          dsimp [kummerCompX]
          rw [if_neg hx₁, if_neg hx₂, if_neg hx₃']
          calc sqClOf (x₃ - r₁)
              = 1 * sqClOf (x₃ - r₁) := (sqCl_one_mul _).symm
            _ = (sqClOf (x₁ - r₁) * sqClOf (x₂ - r₁)) * (sqClOf (x₁ - r₁) * sqClOf (x₂ - r₁)) * sqClOf (x₃ - r₁) := by
                rw [sqCl_mul_self]
            _ = (sqClOf (x₁ - r₁) * sqClOf (x₂ - r₁)) * (sqClOf (x₁ - r₁) * sqClOf (x₂ - r₁) * sqClOf (x₃ - r₁)) := by
                rw [mul_assoc (sqClOf (x₁ - r₁) * sqClOf (x₂ - r₁))]
            _ = sqClOf (x₁ - r₁) * sqClOf (x₂ - r₁) := by
                rw [h_sq, sqCl_mul_one]
  have kummerMap_eq_one_exists_sqrt : ∀ (x₀ y₀ : F)
      (h : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x₀ y₀),
      kummerMap e₁ e₂ e₃ (WeierstrassCurve.Affine.Point.some h) = 1 →
      ∃ z₁ z₂ z₃ : F,
        z₁ ^ 2 = x₀ - e₁ ∧ z₂ ^ 2 = x₀ - e₂ ∧ z₃ ^ 2 = x₀ - e₃ ∧ z₁ * z₂ * z₃ = y₀ := by
    intro x₀ y₀ h hδ
    have hy₀ : y₀ ^ 2 = (x₀ - e₁) * (x₀ - e₂) * (x₀ - e₃) := by
      have heq := (WeierstrassCurve.Affine.equation_iff x₀ y₀).mp h.left
      dsimp [threeRootsCurve] at heq
      linear_combination heq
    have hδ₁ : kummerCompX e₁ e₂ e₃ x₀ = 1 := (Prod.ext_iff.mp hδ).1
    have hδ₂ : kummerCompX e₂ e₁ e₃ x₀ = 1 := (Prod.ext_iff.mp hδ).2
    by_cases hx₁ : x₀ = e₁
    · have hy₀_zero : y₀ = 0 := by
        apply eq_zero_of_pow_eq_zero (n := 2)
        rw [hy₀, hx₁]; ring
      have hx₂ : x₀ ≠ e₂ := by rw [hx₁]; exact h₁₂
      dsimp [kummerCompX] at hδ₁ hδ₂
      rw [if_pos hx₁] at hδ₁
      rw [if_neg hx₂, hx₁] at hδ₂
      have he₁₂ : e₁ - e₂ ≠ 0 := sub_ne_zero.mpr h₁₂
      have he₁₃ : e₁ - e₃ ≠ 0 := sub_ne_zero.mpr h₁₃
      rcases sqClOf_eq_one_exists_sqrt (mul_ne_zero he₁₂ he₁₃) hδ₁ with ⟨w, _, hw⟩
      rcases sqClOf_eq_one_exists_sqrt he₁₂ hδ₂ with ⟨z₂, _, hz₂⟩
      refine ⟨0, z₂, w / z₂, ?_, ?_, ?_, ?_⟩
      · rw [hx₁]; ring
      · rw [hx₁]; exact hz₂
      · rw [hx₁, div_pow, hw, hz₂, mul_div_cancel_left₀ _ he₁₂]
      · rw [hy₀_zero]; ring
    · by_cases hx₂ : x₀ = e₂
      · have hy₀_zero : y₀ = 0 := by
          apply eq_zero_of_pow_eq_zero (n := 2)
          rw [hy₀, hx₂]; ring
        dsimp [kummerCompX] at hδ₁ hδ₂
        rw [if_neg hx₁, hx₂] at hδ₁
        rw [if_pos hx₂] at hδ₂
        have he₂₁ : e₂ - e₁ ≠ 0 := sub_ne_zero.mpr h₁₂.symm
        have he₂₃ : e₂ - e₃ ≠ 0 := sub_ne_zero.mpr h₂₃
        rcases sqClOf_eq_one_exists_sqrt he₂₁ hδ₁ with ⟨z₁, _, hz₁⟩
        rcases sqClOf_eq_one_exists_sqrt (mul_ne_zero he₂₁ he₂₃) hδ₂ with ⟨w, _, hw⟩
        refine ⟨z₁, 0, w / z₁, ?_, ?_, ?_, ?_⟩
        · rw [hx₂]; exact hz₁
        · rw [hx₂]; ring
        · rw [hx₂, div_pow, hw, hz₁, mul_div_cancel_left₀ _ he₂₁]
        · rw [hy₀_zero]; ring
      · dsimp [kummerCompX] at hδ₁ hδ₂
        rw [if_neg hx₁] at hδ₁
        rw [if_neg hx₂] at hδ₂
        have hx₁_sub : x₀ - e₁ ≠ 0 := sub_ne_zero.mpr hx₁
        have hx₂_sub : x₀ - e₂ ≠ 0 := sub_ne_zero.mpr hx₂
        rcases sqClOf_eq_one_exists_sqrt hx₁_sub hδ₁ with ⟨z₁, hz₁_ne, hz₁⟩
        rcases sqClOf_eq_one_exists_sqrt hx₂_sub hδ₂ with ⟨z₂, hz₂_ne, hz₂⟩
        refine ⟨z₁, z₂, y₀ / (z₁ * z₂), hz₁, hz₂, ?_, ?_⟩
        · rw [div_pow, hy₀, mul_pow, hz₁, hz₂, mul_div_cancel_left₀ _ (mul_ne_zero hx₁_sub hx₂_sub)]
        · exact mul_div_cancel₀ y₀ (mul_ne_zero hz₁_ne hz₂_ne)
  have exists_double_of_exists_sqrt : ∀ (x₀ y₀ z₁ z₂ z₃ : F)
      (h : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x₀ y₀),
      z₁ ^ 2 = x₀ - e₁ → z₂ ^ 2 = x₀ - e₂ → z₃ ^ 2 = x₀ - e₃ → z₁ * z₂ * z₃ = y₀ →
      ∃ Q : (threeRootsCurve e₁ e₂ e₃).toAffine.Point,
        WeierstrassCurve.Affine.Point.some h = Q + Q := by
    intro x₀ y₀ z₁ z₂ z₃ h hz₁ hz₂ hz₃ hy₀
    let W := (threeRootsCurve e₁ e₂ e₃).toAffine
    let x := x₀ + z₁ * z₂ + z₁ * z₃ + z₂ * z₃
    let y := (z₁ + z₂) * (z₁ + z₃) * (z₂ + z₃)
    have he₁ : e₁ = x₀ - z₁ ^ 2 := by linear_combination hz₁
    have he₂ : e₂ = x₀ - z₂ ^ 2 := by linear_combination hz₂
    have he₃ : e₃ = x₀ - z₃ ^ 2 := by linear_combination hz₃
    have hz₁₂ : (z₁ + z₂) * (z₁ - z₂) = e₂ - e₁ := by linear_combination hz₁ - hz₂
    have hz₁₃ : (z₁ + z₃) * (z₁ - z₃) = e₃ - e₁ := by linear_combination hz₁ - hz₃
    have hz₂₃ : (z₂ + z₃) * (z₂ - z₃) = e₃ - e₂ := by linear_combination hz₂ - hz₃
    have h_z12_ne : z₁ + z₂ ≠ 0 := left_ne_zero_of_mul (by rw [hz₁₂]; exact sub_ne_zero.mpr h₁₂.symm)
    have h_z13_ne : z₁ + z₃ ≠ 0 := left_ne_zero_of_mul (by rw [hz₁₃]; exact sub_ne_zero.mpr h₁₃.symm)
    have h_z23_ne : z₂ + z₃ ≠ 0 := left_ne_zero_of_mul (by rw [hz₂₃]; exact sub_ne_zero.mpr h₂₃.symm)
    have hy_ne_zero : y ≠ 0 := mul_ne_zero (mul_ne_zero h_z12_ne h_z13_ne) h_z23_ne
    have h_negY : W.negY x y = -y := by
      dsimp [WeierstrassCurve.Affine.negY, W, threeRootsCurve]; ring
    have h_denom : y - W.negY x y = 2 * y := by rw [h_negY]; ring
    have h_2y_ne : 2 * y ≠ 0 := mul_ne_zero two_ne_zero hy_ne_zero
    have hy_ne : y ≠ W.negY x y := sub_ne_zero.mp (by rw [h_denom]; exact h_2y_ne)
    have h_2y_a : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
      have h_eq : 2 * y + W.a₁ * x + W.a₃ = 2 * y := by dsimp [W, threeRootsCurve]; ring
      rw [h_eq]; exact h_2y_ne
    have hQ_eq : W.Equation x y := by
      rw [WeierstrassCurve.Affine.equation_iff]
      dsimp [W, threeRootsCurve, x, y]
      rw [he₁, he₂, he₃]
      ring
    have hQ : W.Nonsingular x y :=
      (WeierstrassCurve.Affine.nonsingular_iff' x y).mpr ⟨hQ_eq, Or.inr h_2y_a⟩
    refine ⟨WeierstrassCurve.Affine.Point.some hQ, ?_⟩
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy_ne]
    have h_slope : W.slope x x y y = z₁ + z₂ + z₃ := by
      rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy_ne, h_denom, div_eq_iff h_2y_ne]
      dsimp [W, threeRootsCurve, x, y]
      rw [he₁, he₂, he₃]
      ring
    have h_addX : W.addX x x (W.slope x x y y) = x₀ := by
      rw [h_slope]
      dsimp [WeierstrassCurve.Affine.addX, W, threeRootsCurve, x]
      rw [he₁, he₂, he₃]
      ring
    have h_addY : W.addY x x y (W.slope x x y y) = y₀ := by
      rw [h_slope]
      dsimp [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.addX, W, threeRootsCurve, x, y]
      rw [he₁, he₂, he₃, ← hy₀]
      ring
    congr 1
    · exact h_addX.symm
    · exact h_addY.symm
  have h_comp_add : ∀ (r₁ r₂ r₃ : F),
      r₁ ≠ r₂ → r₁ ≠ r₃ →
      r₁ + r₂ + r₃ = e₁ + e₂ + e₃ →
      r₁ * r₂ + r₁ * r₃ + r₂ * r₃ = e₁ * e₂ + e₁ * e₃ + e₂ * e₃ →
      (∀ x : F, (x - e₁) * (x - e₂) * (x - e₃) = (x - r₁) * (x - r₂) * (x - r₃)) →
      ∀ P Q : (threeRootsCurve e₁ e₂ e₃).toAffine.Point,
        kummerComp e₁ e₂ e₃ r₁ r₂ r₃ (P + Q) =
          kummerComp e₁ e₂ e₃ r₁ r₂ r₃ P * kummerComp e₁ e₂ e₃ r₁ r₂ r₃ Q := by
    intro r₁ r₂ r₃ hr₁₂ hr₁₃ h_sum h_sym2 h_cub P Q
    rcases P with _ | @⟨x₁, y₁, h₁⟩
    · change kummerComp e₁ e₂ e₃ r₁ r₂ r₃ (0 + Q) = kummerComp e₁ e₂ e₃ r₁ r₂ r₃ 0 * kummerComp e₁ e₂ e₃ r₁ r₂ r₃ Q
      rw [zero_add]
      change kummerComp e₁ e₂ e₃ r₁ r₂ r₃ Q = 1 * kummerComp e₁ e₂ e₃ r₁ r₂ r₃ Q
      exact (sqCl_one_mul _).symm
    · rcases Q with _ | @⟨x₂, y₂, h₂⟩
      · change kummerComp e₁ e₂ e₃ r₁ r₂ r₃ (WeierstrassCurve.Affine.Point.some h₁ + 0) =
            kummerComp e₁ e₂ e₃ r₁ r₂ r₃ (WeierstrassCurve.Affine.Point.some h₁) * kummerComp e₁ e₂ e₃ r₁ r₂ r₃ 0
        rw [add_zero]
        change kummerCompX r₁ r₂ r₃ x₁ = kummerCompX r₁ r₂ r₃ x₁ * 1
        exact (sqCl_mul_one _).symm
      · by_cases h_neg : x₁ = x₂ ∧ y₁ = (threeRootsCurve e₁ e₂ e₃).toAffine.negY x₂ y₂
        · rcases h_neg with ⟨hx, hy⟩
          rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hx hy]
          change 1 = kummerCompX r₁ r₂ r₃ x₁ * kummerCompX r₁ r₂ r₃ x₂
          rw [hx, sqCl_mul_self]
        · rcases threeRoots_add_some_chord_rel x₁ y₁ x₂ y₂ h₁ h₂ h_neg with ⟨⟨h₃, h_add⟩, hM⟩
          rw [h_add]
          change kummerCompX r₁ r₂ r₃ ((threeRootsCurve e₁ e₂ e₃).toAffine.addX x₁ x₂
              ((threeRootsCurve e₁ e₂ e₃).toAffine.slope x₁ x₂ y₁ y₂)) =
            kummerCompX r₁ r₂ r₃ x₁ * kummerCompX r₁ r₂ r₃ x₂
          have hy₁ : y₁ ^ 2 = (x₁ - r₁) * (x₁ - r₂) * (x₁ - r₃) := by
            have heq := (WeierstrassCurve.Affine.equation_iff x₁ y₁).mp h₁.left
            dsimp [threeRootsCurve] at heq
            rw [← h_cub x₁]
            linear_combination heq
          have hx₃ : (threeRootsCurve e₁ e₂ e₃).toAffine.addX x₁ x₂
              ((threeRootsCurve e₁ e₂ e₃).toAffine.slope x₁ x₂ y₁ y₂) =
              ((threeRootsCurve e₁ e₂ e₃).toAffine.slope x₁ x₂ y₁ y₂) ^ 2 + (r₁ + r₂ + r₃) - x₁ - x₂ := by
            dsimp [WeierstrassCurve.Affine.addX, threeRootsCurve]
            rw [h_sum]
            ring
          have hM' : ((threeRootsCurve e₁ e₂ e₃).toAffine.slope x₁ x₂ y₁ y₂) ^ 2 * (x₁ - x₂) -
              2 * ((threeRootsCurve e₁ e₂ e₃).toAffine.slope x₁ x₂ y₁ y₂) * y₁ +
              (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 - (r₁ + r₂ + r₃) * (x₁ + x₂) + (r₁ * r₂ + r₁ * r₃ + r₂ * r₃)) = 0 := by
            rw [h_sum, h_sym2]
            exact hM
          exact kummerCompX_addX_eq_mul r₁ r₂ r₃ x₁ y₁ x₂
            ((threeRootsCurve e₁ e₂ e₃).toAffine.slope x₁ x₂ y₁ y₂)
            ((threeRootsCurve e₁ e₂ e₃).toAffine.addX x₁ x₂
              ((threeRootsCurve e₁ e₂ e₃).toAffine.slope x₁ x₂ y₁ y₂))
            hr₁₂ hr₁₃ hy₁ hx₃ hM'
  have h_hom : ∀ P Q : (threeRootsCurve e₁ e₂ e₃).toAffine.Point,
      kummerMap e₁ e₂ e₃ (P + Q) = kummerMap e₁ e₂ e₃ P * kummerMap e₁ e₂ e₃ Q := by
    intro P Q
    ext
    · exact h_comp_add e₁ e₂ e₃ h₁₂ h₁₃ rfl rfl (fun _ => rfl) P Q
    · exact h_comp_add e₂ e₁ e₃ h₁₂.symm h₂₃ (by ring) (by ring) (fun _ => by ring) P Q
  refine ⟨kummerMap e₁ e₂ e₃, h_hom, ?_, ?_, ?_, ?_⟩
  · intro P
    constructor
    · intro hδ
      rcases P with _ | @⟨x₀, y₀, h⟩
      · exact ⟨0, (zero_add 0).symm⟩
      · rcases kummerMap_eq_one_exists_sqrt x₀ y₀ h hδ with ⟨z₁, z₂, z₃, hz₁, hz₂, hz₃, hy₀⟩
        exact exists_double_of_exists_sqrt x₀ y₀ z₁ z₂ z₃ h hz₁ hz₂ hz₃ hy₀
    · rintro ⟨Q, rfl⟩
      rw [h_hom]
      ext
      · exact sqCl_mul_self _
      · exact sqCl_mul_self _
  · intro x y h u₁ u₂ hx₁ hx₂ hu₁ hu₂
    dsimp [kummerMap, kummerComp, kummerCompX]
    rw [if_neg hx₁, if_neg hx₂, sqClOf_eq_sqCl _ u₁ hu₁, sqClOf_eq_sqCl _ u₂ hu₂]
  · intro h u₁ u₂ hu₁ hu₂
    dsimp [kummerMap, kummerComp, kummerCompX]
    rw [if_pos rfl, if_neg h₁₂, sqClOf_eq_sqCl _ u₁ hu₁, sqClOf_eq_sqCl _ u₂ hu₂]
  · intro h u₁ u₂ hu₁ hu₂
    dsimp [kummerMap, kummerComp, kummerCompX]
    have hu₁' : (u₁ : F) = e₂ - e₁ := by linear_combination hu₁
    have hu₂' : (u₂ : F) = (e₂ - e₁) * (e₂ - e₃) := by linear_combination hu₂
    rw [if_neg h₁₂.symm, if_pos rfl, sqClOf_eq_sqCl _ u₁ hu₁', sqClOf_eq_sqCl _ u₂ hu₂']
