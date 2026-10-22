import Mathlib
import Hilbert10Defs
set_option maxHeartbeats 4000000

/-! ### Statement (originally `proposition_4_1.lean`) -/

/--
**Proposition 4.1.** Let `K` be a number field, `e₁, e₂, e₃ ∈ K` distinct and `v` a finite
place. The image of the local Kummer map `δ(E(K_v)/2E(K_v))` is a maximal isotropic
subspace of `H¹(G_{K_v}, E[2]) ≅ (K_vˣ/K_vˣ²)²`; in particular its cardinality equals
`#(K_vˣ/K_vˣ²)`.
-/
def pointKummerVal {F : Type*} [Field F] [DecidableEq F] {e₁ e₂ e₃ : F}
    (a b c : F) (P : (threeRootsCurve e₁ e₂ e₃).toAffine.Point) : F :=
  match P with
  | .zero => 1
  | .some (x := x) _ => if x = a then (a - b) * (a - c) else x - a
def lutzSet {F : Type*} [Field F] [Valued F (WithZero (Multiplicative ℤ))]
    (e₁ e₂ e₃ : F) (m : ℤ) :
    Set (threeRootsCurve e₁ e₂ e₃).toAffine.Point :=
  { P | match P with
        | WeierstrassCurve.Affine.Point.zero => True
        | WeierstrassCurve.Affine.Point.some (x := x) (y := _) _ =>
            WithZero.exp (2 * m) ≤ Valued.v x }

def lutzParam {F : Type*} [Field F] {W : WeierstrassCurve.Affine F} : W.Point → F
  | WeierstrassCurve.Affine.Point.zero => 0
  | WeierstrassCurve.Affine.Point.some (x := x) (y := y) _ => -x / y

def valBall (F : Type*) [Ring F] [Valued F (WithZero (Multiplicative ℤ))] (k : ℤ) :
    AddSubgroup F where
  carrier := { x : F | Valued.v x ≤ WithZero.exp (-k) }
  add_mem' {a b} ha hb := le_trans (Valuation.map_add Valued.v a b) (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa only [Set.mem_setOf_eq, Valuation.map_neg] using ha

theorem descent_set_ncard_eq_point_mod_two_card {F : Type*} [Field F] [CharZero F] [DecidableEq F]
    (e₁ e₂ e₃ : F) (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃) :
    Set.ncard { c : SqCl F × SqCl F |
        ∃ d₁ d₂ : Fˣ,
          c = (sqCl d₁, sqCl d₂) ∧
          IsDescentClass e₁ e₂ e₃ (d₁ : F) (d₂ : F) }
      = Nat.card ((threeRootsCurve e₁ e₂ e₃).toAffine.Point ⧸
          (AddMonoidHom.id (threeRootsCurve e₁ e₂ e₃).toAffine.Point +
           AddMonoidHom.id (threeRootsCurve e₁ e₂ e₃).toAffine.Point).range) :=
by
  let W := (threeRootsCurve e₁ e₂ e₃).toAffine
  let D := (AddMonoidHom.id W.Point + AddMonoidHom.id W.Point).range
  have h_eq_iff : ∀ x y : F, W.Equation x y ↔ y ^ 2 = (x - e₁) * (x - e₂) * (x - e₃) := by
    intro x y
    rw [WeierstrassCurve.Affine.equation_iff]
    dsimp [W, threeRootsCurve]
    constructor <;> intro h <;> linear_combination h
  have h_ns_iff : ∀ x y : F, W.Nonsingular x y ↔ y ^ 2 = (x - e₁) * (x - e₂) * (x - e₃) := by
    intro x y
    rw [WeierstrassCurve.Affine.nonsingular_iff, h_eq_iff]
    dsimp [W, threeRootsCurve]
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    by_cases hy : y = 0
    · left
      intro hx
      have h0 : (x - e₁) * (x - e₂) * (x - e₃) = 0 := by linear_combination -h + y * hy
      rcases mul_eq_zero.mp h0 with h12 | h3
      · rcases mul_eq_zero.mp h12 with h1 | h2
        · have hx1 : e₁ = x := (sub_eq_zero.mp h1).symm
          subst hx1
          apply h₁₂ (sub_eq_zero.mp ((mul_eq_zero.mp (by linear_combination -hx : (e₁ - e₂) * (e₁ - e₃) = 0)).resolve_right (sub_ne_zero.mpr h₁₃)))
        · have hx2 : e₂ = x := (sub_eq_zero.mp h2).symm
          subst hx2
          apply h₁₂.symm (sub_eq_zero.mp ((mul_eq_zero.mp (by linear_combination -hx : (e₂ - e₁) * (e₂ - e₃) = 0)).resolve_right (sub_ne_zero.mpr h₂₃)))
      · have hx3 : e₃ = x := (sub_eq_zero.mp h3).symm
        subst hx3
        apply h₁₃.symm (sub_eq_zero.mp ((mul_eq_zero.mp (by linear_combination -hx : (e₃ - e₁) * (e₃ - e₂) = 0)).resolve_right (sub_ne_zero.mpr h₂₃.symm)))
    · right
      intro hy'
      apply hy ((mul_eq_zero.mp (by linear_combination hy' : (2 : F) * y = 0)).resolve_left two_ne_zero)
  have isSquare_pointKummerVal_add : ∀ (a b c : F), a ≠ b → a ≠ c →
      (∀ x : F, (x - e₁) * (x - e₂) * (x - e₃) = (x - a) * (x - b) * (x - c)) →
      ∀ (P Q : W.Point),
      IsSquare (pointKummerVal a b c P * pointKummerVal a b c Q * pointKummerVal a b c (P + Q)) := by
    intro a b c hab hac hperm P Q
    have hp0 := hperm 0
    have hp1 := hperm 1
    have hpm1 := hperm (-1)
    have he_sum : e₁ + e₂ + e₃ = a + b + c := by
      apply sub_eq_zero.mp
      refine (mul_eq_zero.mp (by linear_combination -(hp1 + hpm1 - 2 * hp0) :
        (2 : F) * ((e₁ + e₂ + e₃) - (a + b + c)) = 0)).resolve_left two_ne_zero
    have he_sym2 : e₁ * e₂ + e₁ * e₃ + e₂ * e₃ = a * b + a * c + b * c := by
      apply sub_eq_zero.mp
      refine (mul_eq_zero.mp (by linear_combination hp1 - hpm1 :
        (2 : F) * ((e₁ * e₂ + e₁ * e₃ + e₂ * e₃) - (a * b + a * c + b * c)) = 0)).resolve_left two_ne_zero
    have h_eq_abc : ∀ x y : F, W.Nonsingular x y → y ^ 2 = (x - a) * (x - b) * (x - c) := by
      intro x y hns
      have h1 := (h_ns_iff x y).mp hns
      rw [hperm x] at h1
      exact h1
    have hnegY : ∀ x y : F, W.negY x y = -y := by
      intro x y; dsimp [W, threeRootsCurve, WeierstrassCurve.Affine.negY]; ring
    cases P with
    | zero =>
      change IsSquare (pointKummerVal a b c 0 * pointKummerVal a b c Q * pointKummerVal a b c (0 + Q))
      rw [zero_add]
      exact ⟨pointKummerVal a b c Q, by dsimp [pointKummerVal]; ring⟩
    | @some x₁ y₁ h₁ =>
      cases Q with
      | zero =>
        change IsSquare (pointKummerVal a b c (.some h₁) * pointKummerVal a b c 0 * pointKummerVal a b c (.some h₁ + 0))
        rw [add_zero]
        exact ⟨pointKummerVal a b c (.some h₁), by dsimp [pointKummerVal]; ring⟩
      | @some x₂ y₂ h₂ =>
        have E₁ : y₁ ^ 2 = (x₁ - a) * (x₁ - b) * (x₁ - c) := h_eq_abc x₁ y₁ h₁
        have E₂ : y₂ ^ 2 = (x₂ - a) * (x₂ - b) * (x₂ - c) := h_eq_abc x₂ y₂ h₂
        by_cases hx : x₁ = x₂
        · by_cases hy : y₁ = W.negY x₂ y₂
          · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hx hy]
            refine ⟨pointKummerVal a b c (.some h₁), ?_⟩
            dsimp [pointKummerVal]
            subst hx
            ring
          · rw [WeierstrassCurve.Affine.Point.add_of_Y_ne hy]
            subst hx
            have hy_neg : y₁ ≠ -y₂ := by rwa [hnegY] at hy
            have hy_eq : y₁ = y₂ := by
              have hsq : (y₁ - y₂) * (y₁ + y₂) = 0 := by linear_combination E₁ - E₂
              rcases mul_eq_zero.mp hsq with h_eq | h_neg
              · exact sub_eq_zero.mp h_eq
              · exfalso; apply hy_neg; linear_combination h_neg
            subst hy_eq
            have hy₁_ne : y₁ ≠ 0 := by
              intro h0; apply hy_neg; rw [h0, neg_zero]
            let ℓ := W.slope x₁ x₁ y₁ y₁
            let x₃ := W.addX x₁ x₁ ℓ
            have h_tan_slope : 2 * y₁ * ℓ = 3 * x₁ ^ 2 - 2 * (a + b + c) * x₁ + (a * b + a * c + b * c) := by
              dsimp [ℓ]
              rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
              have hden : y₁ - W.negY x₁ y₁ = 2 * y₁ := by rw [hnegY]; ring
              rw [hden, mul_div_cancel₀ _ (mul_ne_zero two_ne_zero hy₁_ne)]
              dsimp [W, threeRootsCurve]
              linear_combination -2 * x₁ * he_sum + he_sym2
            have hx₃_def : x₃ = ℓ ^ 2 + (a + b + c) - 2 * x₁ := by
              dsimp [x₃, WeierstrassCurve.Affine.addX, W, threeRootsCurve]
              linear_combination he_sum
            have id_tan : 4 * y₁ ^ 2 * (x₃ - a) = ((x₁ - a) ^ 2 - (a - b) * (a - c)) ^ 2 := by
              linear_combination (2 * y₁ * ℓ + (3 * x₁ ^ 2 - 2 * (a + b + c) * x₁ + (a * b + a * c + b * c))) * h_tan_slope +
                4 * (b + c - 2 * x₁) * E₁ + 4 * y₁ ^ 2 * hx₃_def
            dsimp [pointKummerVal]
            change IsSquare ((if x₁ = a then (a - b) * (a - c) else x₁ - a) *
              (if x₁ = a then (a - b) * (a - c) else x₁ - a) *
              (if x₃ = a then (a - b) * (a - c) else x₃ - a))
            set v₁ := if x₁ = a then (a - b) * (a - c) else x₁ - a
            by_cases hx₃ : x₃ = a
            · rw [if_pos hx₃]
              have h_zero : ((x₁ - a) ^ 2 - (a - b) * (a - c)) ^ 2 = 0 := by
                linear_combination -id_tan + 4 * y₁ ^ 2 * hx₃
              have h_ab : (a - b) * (a - c) = (x₁ - a) ^ 2 := by
                linear_combination -(eq_zero_of_pow_eq_zero h_zero)
              rw [h_ab]
              exact ⟨v₁ * (x₁ - a), by ring⟩
            · rw [if_neg hx₃]
              refine ⟨v₁ * ((x₁ - a) ^ 2 - (a - b) * (a - c)) / (2 * y₁), ?_⟩
              have h2y : 2 * y₁ ≠ 0 := mul_ne_zero two_ne_zero hy₁_ne
              rw [div_mul_div_comm, ← sq (2 * y₁), eq_div_iff (pow_ne_zero 2 h2y)]
              linear_combination v₁ ^ 2 * id_tan
        · rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
          let ℓ := W.slope x₁ x₂ y₁ y₂
          let x₃ := W.addX x₁ x₂ ℓ
          have L_sec : (x₁ - x₂) * ℓ = y₁ - y₂ := by
            dsimp [ℓ]
            rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
            exact mul_div_cancel₀ (y₁ - y₂) (sub_ne_zero.mpr hx)
          have hx₃_def : x₃ = ℓ ^ 2 + (a + b + c) - x₁ - x₂ := by
            dsimp [x₃, WeierstrassCurve.Affine.addX, W, threeRootsCurve]
            linear_combination he_sum
          have id_sec1 : (x₁ - a) * (x₂ - a) * (x₃ - a) = (ℓ * (a - x₁) + y₁) ^ 2 := by
            apply sub_eq_zero.mp
            refine (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hx)
            linear_combination -(a - x₂) * E₁ + (a - x₁) * E₂ -
              (a - x₁) * (y₁ + y₂ - ℓ * (x₁ - x₂)) * L_sec +
              (x₁ - x₂) * (x₁ - a) * (x₂ - a) * hx₃_def
          have id_sec_x1 : (x₁ - a) * ((x₁ - a) * (x₂ - a) - (a - b) * (a - c) + (x₁ - a) * (x₃ - a)) =
              (ℓ * (x₁ - a) + y₁) * (ℓ * (x₁ - a) - y₁) := by
            linear_combination E₁ + (x₁ - a) ^ 2 * hx₃_def
          have id_sec_x2 : (x₂ - a) * ((x₂ - a) * (x₁ - a) - (a - b) * (a - c) + (x₂ - a) * (x₃ - a)) =
              (ℓ * (x₂ - a) + y₂) * (ℓ * (x₂ - a) - y₂) := by
            linear_combination E₂ + (x₂ - a) ^ 2 * hx₃_def
          dsimp [pointKummerVal]
          change IsSquare ((if x₁ = a then (a - b) * (a - c) else x₁ - a) *
            (if x₂ = a then (a - b) * (a - c) else x₂ - a) *
            (if x₃ = a then (a - b) * (a - c) else x₃ - a))
          by_cases hx₁ : x₁ = a
          · have hx₂ : x₂ ≠ a := fun h => hx (hx₁.trans h.symm)
            have hy₁ : y₁ = 0 := eq_zero_of_pow_eq_zero (by linear_combination E₁ + (x₁ - b) * (x₁ - c) * hx₁ : y₁ ^ 2 = 0)
            have hL2 : ℓ * (x₂ - a) - y₂ = 0 := by linear_combination -L_sec + ℓ * hx₁ - hy₁
            have h_prod : (x₂ - a) * (x₃ - a) = (a - b) * (a - c) := by
              apply sub_eq_zero.mp
              refine (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hx₂)
              linear_combination id_sec_x2 - (x₂ - a) ^ 2 * hx₁ + (ℓ * (x₂ - a) + y₂) * hL2
            have hx₃ : x₃ ≠ a := by
              intro h3
              have : (a - b) * (a - c) = 0 := by linear_combination -h_prod + (x₂ - a) * h3
              exact mul_ne_zero (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hac) this
            rw [if_pos hx₁, if_neg hx₂, if_neg hx₃]
            exact ⟨(a - b) * (a - c), by linear_combination (a - b) * (a - c) * h_prod⟩
          · by_cases hx₂ : x₂ = a
            · have hy₂ : y₂ = 0 := eq_zero_of_pow_eq_zero (by linear_combination E₂ + (x₂ - b) * (x₂ - c) * hx₂ : y₂ ^ 2 = 0)
              have hL1 : ℓ * (x₁ - a) - y₁ = 0 := by linear_combination L_sec + ℓ * hx₂ - hy₂
              have h_prod : (x₁ - a) * (x₃ - a) = (a - b) * (a - c) := by
                apply sub_eq_zero.mp
                refine (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hx₁)
                linear_combination id_sec_x1 - (x₁ - a) ^ 2 * hx₂ + (ℓ * (x₁ - a) + y₁) * hL1
              have hx₃ : x₃ ≠ a := by
                intro h3
                have : (a - b) * (a - c) = 0 := by linear_combination -h_prod + (x₁ - a) * h3
                exact mul_ne_zero (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hac) this
              rw [if_neg hx₁, if_pos hx₂, if_neg hx₃]
              exact ⟨(a - b) * (a - c), by linear_combination (a - b) * (a - c) * h_prod⟩
            · by_cases hx₃ : x₃ = a
              · have hL1_sq : (ℓ * (a - x₁) + y₁) ^ 2 = 0 := by
                  linear_combination -id_sec1 + (x₁ - a) * (x₂ - a) * hx₃
                have hL1 : ℓ * (x₁ - a) - y₁ = 0 := by
                  linear_combination -(eq_zero_of_pow_eq_zero hL1_sq)
                have h_prod : (x₁ - a) * (x₂ - a) = (a - b) * (a - c) := by
                  apply sub_eq_zero.mp
                  refine (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hx₁)
                  linear_combination id_sec_x1 - (x₁ - a) ^ 2 * hx₃ + (ℓ * (x₁ - a) + y₁) * hL1
                rw [if_neg hx₁, if_neg hx₂, if_pos hx₃]
                exact ⟨(a - b) * (a - c), by linear_combination (a - b) * (a - c) * h_prod⟩
              · rw [if_neg hx₁, if_neg hx₂, if_neg hx₃]
                exact ⟨ℓ * (a - x₁) + y₁, by linear_combination id_sec1⟩
  have exists_double_eq_of_isSquare_pointKummerVal : ∀ (P : W.Point),
      IsSquare (pointKummerVal e₁ e₂ e₃ P) →
      IsSquare (pointKummerVal e₂ e₁ e₃ P) →
      ∃ Q : W.Point, Q + Q = P := by
    intro P h₁ h₂
    clear isSquare_pointKummerVal_add
    cases P with
    | zero =>
      exact ⟨0, zero_add 0⟩
    | @some x₀ y₀ h₀ =>
      have heq₀ : y₀ ^ 2 = (x₀ - e₁) * (x₀ - e₂) * (x₀ - e₃) := (h_ns_iff x₀ y₀).mp h₀
      rcases h₁ with ⟨r₁, hr₁⟩
      rcases h₂ with ⟨r₂, hr₂⟩
      dsimp [pointKummerVal] at hr₁ hr₂
      have hu : ∃ u₁ u₂ u₃ : F, u₁ ^ 2 = x₀ - e₁ ∧ u₂ ^ 2 = x₀ - e₂ ∧ u₃ ^ 2 = x₀ - e₃ ∧ u₁ * u₂ * u₃ = y₀ := by
        by_cases hx1 : x₀ = e₁
        · subst hx1
          have hx2 : x₀ ≠ e₂ := h₁₂
          rw [if_pos rfl] at hr₁
          rw [if_neg hx2] at hr₂
          have hy₀ : y₀ = 0 := eq_zero_of_pow_eq_zero (by linear_combination heq₀ : y₀ ^ 2 = 0)
          refine ⟨0, r₂, r₁ / r₂, by ring, by linear_combination -hr₂, ?_, by linear_combination -hy₀⟩
          rw [div_pow, sq r₁, sq r₂, ← hr₁, ← hr₂]
          exact mul_div_cancel_left₀ (x₀ - e₃) (sub_ne_zero.mpr h₁₂)
        · rw [if_neg hx1] at hr₁
          have hr₁_ne : r₁ ≠ 0 := by
            intro h0; rw [h0, mul_zero] at hr₁; exact sub_ne_zero.mpr hx1 hr₁
          by_cases hx2 : x₀ = e₂
          · subst hx2
            rw [if_pos rfl] at hr₂
            have hy₀ : y₀ = 0 := eq_zero_of_pow_eq_zero (by linear_combination heq₀ : y₀ ^ 2 = 0)
            refine ⟨r₁, 0, r₂ / r₁, by linear_combination -hr₁, by ring, ?_, by linear_combination -hy₀⟩
            rw [div_pow, sq r₂, sq r₁, ← hr₂, ← hr₁]
            exact mul_div_cancel_left₀ (x₀ - e₃) (sub_ne_zero.mpr h₁₂.symm)
          · rw [if_neg hx2] at hr₂
            have hr₂_ne : r₂ ≠ 0 := by
              intro h0; rw [h0, mul_zero] at hr₂; exact sub_ne_zero.mpr hx2 hr₂
            refine ⟨r₁, r₂, y₀ / (r₁ * r₂), by linear_combination -hr₁, by linear_combination -hr₂, ?_, ?_⟩
            · rw [div_pow, mul_pow, heq₀, sq r₁, sq r₂, ← hr₁, ← hr₂]
              exact mul_div_cancel_left₀ (x₀ - e₃) (mul_ne_zero (sub_ne_zero.mpr hx1) (sub_ne_zero.mpr hx2))
            · exact mul_div_cancel₀ y₀ (mul_ne_zero hr₁_ne hr₂_ne)
      rcases hu with ⟨u₁, u₂, u₃, hu₁, hu₂, hu₃, hy₀⟩
      have he₁ : e₁ = x₀ - u₁ ^ 2 := by linear_combination hu₁
      have he₂ : e₂ = x₀ - u₂ ^ 2 := by linear_combination hu₂
      have he₃ : e₃ = x₀ - u₃ ^ 2 := by linear_combination hu₃
      let x₁ : F := x₀ + u₁ * u₂ + u₁ * u₃ + u₂ * u₃
      let y₁ : F := (u₁ + u₂) * (u₁ + u₃) * (u₂ + u₃)
      have hns₁ : W.Nonsingular x₁ y₁ := (h_ns_iff x₁ y₁).mpr (by dsimp [x₁, y₁]; rw [he₁, he₂, he₃]; ring)
      have hu12 : u₁ + u₂ ≠ 0 := fun h => h₁₂ (by linear_combination he₁ - he₂ - (u₁ - u₂) * h)
      have hu13 : u₁ + u₃ ≠ 0 := fun h => h₁₃ (by linear_combination he₁ - he₃ - (u₁ - u₃) * h)
      have hu23 : u₂ + u₃ ≠ 0 := fun h => h₂₃ (by linear_combination he₂ - he₃ - (u₂ - u₃) * h)
      have hy₁_ne : y₁ ≠ 0 := mul_ne_zero (mul_ne_zero hu12 hu13) hu23
      have hy₁_neg : y₁ ≠ W.negY x₁ y₁ := by
        intro h; apply hy₁_ne; dsimp [W, threeRootsCurve, WeierstrassCurve.Affine.negY] at h
        exact (mul_eq_zero.mp (by linear_combination h : (2 : F) * y₁ = 0)).resolve_left two_ne_zero
      have hslope : W.slope x₁ x₁ y₁ y₁ = u₁ + u₂ + u₃ := by
        rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy₁_neg, div_eq_iff (sub_ne_zero.mpr hy₁_neg)]
        dsimp [W, threeRootsCurve, WeierstrassCurve.Affine.negY, x₁, y₁]
        rw [he₁, he₂, he₃]; ring
      refine ⟨WeierstrassCurve.Affine.Point.some hns₁, ?_⟩
      rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy₁_neg, WeierstrassCurve.Affine.Point.some.injEq]
      constructor
      · dsimp [WeierstrassCurve.Affine.addX]; rw [hslope]; dsimp [W, threeRootsCurve, x₁]; rw [he₁, he₂, he₃]; ring
      · dsimp [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addX]
        rw [hslope]; dsimp [W, threeRootsCurve, x₁, y₁]; rw [he₁, he₂, he₃, ← hy₀]; ring
  have isDescentClass_iff_exists_point : ∀ (d₁ d₂ : Fˣ),
      IsDescentClass e₁ e₂ e₃ (d₁ : F) (d₂ : F) ↔
        ∃ P : W.Point,
          IsSquare ((d₁ : F) * pointKummerVal e₁ e₂ e₃ P) ∧
          IsSquare ((d₂ : F) * pointKummerVal e₂ e₁ e₃ P) := by
    intro d₁ d₂
    clear isSquare_pointKummerVal_add exists_double_eq_of_isSquare_pointKummerVal
    have hd₁ : (d₁ : F) ≠ 0 := d₁.ne_zero
    have hd₂ : (d₂ : F) ≠ 0 := d₂.ne_zero
    constructor
    · rintro ⟨z₀, z₁, z₂, z₃, h_nz, q₁, q₂⟩
      have q₃ : (d₂ : F) * z₂ ^ 2 - (d₁ : F) * (d₂ : F) * z₃ ^ 2 = (e₃ - e₂) * z₀ ^ 2 := by
        linear_combination q₂ - q₁
      by_cases hz₀ : z₀ = 0
      · have hz₃ : z₃ ≠ 0 := by
          intro h3
          have hz₁ : z₁ = 0 := eq_zero_of_pow_eq_zero ((mul_eq_zero.mp (by linear_combination q₂ + (d₁ : F) * (d₂ : F) * z₃ * h3 + (e₃ - e₁) * z₀ * hz₀ : (d₁ : F) * z₁ ^ 2 = 0)).resolve_left hd₁)
          have hz₂ : z₂ = 0 := eq_zero_of_pow_eq_zero ((mul_eq_zero.mp (by linear_combination -q₁ + (d₁ : F) * z₁ * hz₁ - (e₂ - e₁) * z₀ * hz₀ : (d₂ : F) * z₂ ^ 2 = 0)).resolve_left hd₂)
          exact h_nz ⟨hz₀, hz₁, hz₂, h3⟩
        refine ⟨.zero, ⟨z₂ / z₃, ?_⟩, ⟨z₁ / z₃, ?_⟩⟩
        · dsimp [pointKummerVal]
          rw [div_mul_div_comm, ← sq z₃, eq_div_iff (pow_ne_zero 2 hz₃)]
          apply (mul_right_inj' hd₂).mp
          linear_combination -q₃ - (e₃ - e₂) * z₀ * hz₀
        · dsimp [pointKummerVal]
          rw [div_mul_div_comm, ← sq z₃, eq_div_iff (pow_ne_zero 2 hz₃)]
          apply (mul_right_inj' hd₁).mp
          linear_combination -q₂ - (e₃ - e₁) * z₀ * hz₀
      · by_cases hz₁ : z₁ = 0
        · have hns1 : W.Nonsingular e₁ 0 := (h_ns_iff e₁ 0).mpr (by ring)
          refine ⟨.some hns1, ?_, ?_⟩
          · dsimp [pointKummerVal]
            rw [if_pos rfl]
            refine ⟨(d₁ : F) * (d₂ : F) * z₂ * z₃ / z₀ ^ 2, ?_⟩
            rw [div_mul_div_comm, ← sq (z₀ ^ 2), eq_div_iff (pow_ne_zero 2 (pow_ne_zero 2 hz₀))]
            have hA : (e₁ - e₂) * z₀ ^ 2 = (d₂ : F) * z₂ ^ 2 := by linear_combination q₁ - (d₁ : F) * z₁ * hz₁
            have hB : (e₁ - e₃) * z₀ ^ 2 = (d₁ : F) * (d₂ : F) * z₃ ^ 2 := by linear_combination q₂ - (d₁ : F) * z₁ * hz₁
            linear_combination (d₁ : F) * (e₁ - e₃) * z₀ ^ 2 * hA + (d₁ : F) * (d₂ : F) * z₂ ^ 2 * hB
          · dsimp [pointKummerVal]
            rw [if_neg h₁₂]
            refine ⟨(d₂ : F) * z₂ / z₀, ?_⟩
            rw [div_mul_div_comm, ← sq z₀, eq_div_iff (pow_ne_zero 2 hz₀)]
            linear_combination (d₂ : F) * q₁ - (d₁ : F) * (d₂ : F) * z₁ * hz₁
        · by_cases hz₂ : z₂ = 0
          · have hns2 : W.Nonsingular e₂ 0 := (h_ns_iff e₂ 0).mpr (by ring)
            refine ⟨.some hns2, ?_, ?_⟩
            · dsimp [pointKummerVal]
              rw [if_neg h₁₂.symm]
              refine ⟨(d₁ : F) * z₁ / z₀, ?_⟩
              rw [div_mul_div_comm, ← sq z₀, eq_div_iff (pow_ne_zero 2 hz₀)]
              linear_combination -(d₁ : F) * q₁ - (d₁ : F) * (d₂ : F) * z₂ * hz₂
            · dsimp [pointKummerVal]
              rw [if_pos rfl]
              refine ⟨(d₁ : F) * (d₂ : F) * z₁ * z₃ / z₀ ^ 2, ?_⟩
              rw [div_mul_div_comm, ← sq (z₀ ^ 2), eq_div_iff (pow_ne_zero 2 (pow_ne_zero 2 hz₀))]
              have hA : (e₂ - e₁) * z₀ ^ 2 = (d₁ : F) * z₁ ^ 2 := by linear_combination -q₁ - (d₂ : F) * z₂ * hz₂
              have hB : (e₂ - e₃) * z₀ ^ 2 = (d₁ : F) * (d₂ : F) * z₃ ^ 2 := by linear_combination q₃ - (d₂ : F) * z₂ * hz₂
              linear_combination (d₂ : F) * (e₂ - e₃) * z₀ ^ 2 * hA + (d₁ : F) * (d₂ : F) * z₁ ^ 2 * hB
          · by_cases hz₃ : z₃ = 0
            · have hns3 : W.Nonsingular e₃ 0 := (h_ns_iff e₃ 0).mpr (by ring)
              refine ⟨.some hns3, ?_, ?_⟩
              · dsimp [pointKummerVal]
                rw [if_neg h₁₃.symm]
                refine ⟨(d₁ : F) * z₁ / z₀, ?_⟩
                rw [div_mul_div_comm, ← sq z₀, eq_div_iff (pow_ne_zero 2 hz₀)]
                linear_combination -(d₁ : F) * q₂ - (d₁ : F) ^ 2 * (d₂ : F) * z₃ * hz₃
              · dsimp [pointKummerVal]
                rw [if_neg h₂₃.symm]
                refine ⟨(d₂ : F) * z₂ / z₀, ?_⟩
                rw [div_mul_div_comm, ← sq z₀, eq_div_iff (pow_ne_zero 2 hz₀)]
                linear_combination -(d₂ : F) * q₃ - (d₁ : F) * (d₂ : F) ^ 2 * z₃ * hz₃
            · set x : F := e₁ + (d₁ : F) * (z₁ / z₀) ^ 2
              set y : F := (d₁ : F) * (d₂ : F) * z₁ * z₂ * z₃ / z₀ ^ 3
              have hx1_eq : (x - e₁) * z₀ ^ 2 = (d₁ : F) * z₁ ^ 2 := by
                dsimp [x]
                rw [add_sub_cancel_left, div_pow, mul_assoc, div_mul_cancel₀ _ (pow_ne_zero 2 hz₀)]
              have hy_eq : y * z₀ ^ 3 = (d₁ : F) * (d₂ : F) * z₁ * z₂ * z₃ :=
                div_mul_cancel₀ _ (pow_ne_zero 3 hz₀)
              clear_value x y
              have hx2_eq : (x - e₂) * z₀ ^ 2 = (d₂ : F) * z₂ ^ 2 := by linear_combination hx1_eq + q₁
              have hx3_eq : (x - e₃) * z₀ ^ 2 = (d₁ : F) * (d₂ : F) * z₃ ^ 2 := by linear_combination hx1_eq + q₂
              have hns : W.Nonsingular x y := by
                rw [h_ns_iff]
                apply (mul_left_inj' (pow_ne_zero 6 hz₀)).mp
                linear_combination (y * z₀ ^ 3 + (d₁ : F) * (d₂ : F) * z₁ * z₂ * z₃) * hy_eq -
                  (x - e₂) * (x - e₃) * z₀ ^ 4 * hx1_eq -
                  (d₁ : F) * z₁ ^ 2 * (x - e₃) * z₀ ^ 2 * hx2_eq -
                  (d₁ : F) * (d₂ : F) * z₁ ^ 2 * z₂ ^ 2 * hx3_eq
              have hx1 : x ≠ e₁ := by
                intro h1
                have : (d₁ : F) * z₁ ^ 2 = 0 := by linear_combination -hx1_eq + z₀ ^ 2 * h1
                exact mul_ne_zero hd₁ (pow_ne_zero 2 hz₁) this
              have hx2 : x ≠ e₂ := by
                intro h2
                have : (d₂ : F) * z₂ ^ 2 = 0 := by linear_combination -hx2_eq + z₀ ^ 2 * h2
                exact mul_ne_zero hd₂ (pow_ne_zero 2 hz₂) this
              refine ⟨.some hns, ?_, ?_⟩
              · dsimp [pointKummerVal]
                rw [if_neg hx1]
                refine ⟨(d₁ : F) * z₁ / z₀, ?_⟩
                rw [div_mul_div_comm, ← sq z₀, eq_div_iff (pow_ne_zero 2 hz₀)]
                linear_combination (d₁ : F) * hx1_eq
              · dsimp [pointKummerVal]
                rw [if_neg hx2]
                refine ⟨(d₂ : F) * z₂ / z₀, ?_⟩
                rw [div_mul_div_comm, ← sq z₀, eq_div_iff (pow_ne_zero 2 hz₀)]
                linear_combination (d₂ : F) * hx2_eq
    · rintro ⟨P, ⟨r₁, hr₁⟩, ⟨r₂, hr₂⟩⟩
      cases P with
      | zero =>
        dsimp [pointKummerVal] at hr₁ hr₂
        refine ⟨0, r₂, r₁, 1, by simp, ?_, ?_⟩
        · linear_combination (r₂ ^ 2) * hr₁ - (r₁ ^ 2) * hr₂
        · linear_combination -(d₁ : F) * hr₂
      | @some x y h =>
        have heq : y ^ 2 = (x - e₁) * (x - e₂) * (x - e₃) := (h_ns_iff x y).mp h
        dsimp [pointKummerVal] at hr₁ hr₂
        by_cases hx1 : x = e₁
        · subst hx1
          rw [if_pos rfl] at hr₁
          rw [if_neg h₁₂] at hr₂
          have hr₁_ne : r₁ ≠ 0 := by
            intro h0; rw [h0, mul_zero] at hr₁
            exact mul_ne_zero hd₁ (mul_ne_zero (sub_ne_zero.mpr h₁₂) (sub_ne_zero.mpr h₁₃)) hr₁
          have hr₂_ne : r₂ ≠ 0 := by
            intro h0; rw [h0, mul_zero] at hr₂
            exact mul_ne_zero hd₂ (sub_ne_zero.mpr h₁₂) hr₂
          refine ⟨r₁ * r₂, 0, (x - e₂) * r₁, (x - e₂) * (x - e₃),
            fun h0 => mul_ne_zero hr₁_ne hr₂_ne h0.1, ?_, ?_⟩
          · linear_combination -(x - e₂) * r₁ ^ 2 * hr₂
          · linear_combination -(x - e₃) * r₂ ^ 2 * hr₁ - (d₁ : F) * (x - e₂) * (x - e₃) ^ 2 * hr₂
        · rw [if_neg hx1] at hr₁
          have hr₁_ne : r₁ ≠ 0 := by
            intro h0; rw [h0, mul_zero] at hr₁
            exact mul_ne_zero hd₁ (sub_ne_zero.mpr hx1) hr₁
          by_cases hx2 : x = e₂
          · subst hx2
            rw [if_pos rfl] at hr₂
            have hr₂_ne : r₂ ≠ 0 := by
              intro h0; rw [h0, mul_zero] at hr₂
              exact mul_ne_zero hd₂ (mul_ne_zero (sub_ne_zero.mpr h₁₂.symm) (sub_ne_zero.mpr h₂₃)) hr₂
            refine ⟨r₁ * r₂, (x - e₁) * r₂, 0, (x - e₁) * (x - e₃),
              fun h0 => mul_ne_zero hr₁_ne hr₂_ne h0.1, ?_, ?_⟩
            · linear_combination (x - e₁) * r₂ ^ 2 * hr₁
            · linear_combination (e₃ - e₁) * r₂ ^ 2 * hr₁ - (d₁ : F) * (x - e₁) * (x - e₃) * hr₂
          · rw [if_neg hx2] at hr₂
            have hr₂_ne : r₂ ≠ 0 := by
              intro h0; rw [h0, mul_zero] at hr₂
              exact mul_ne_zero hd₂ (sub_ne_zero.mpr hx2) hr₂
            refine ⟨r₁ * r₂, (x - e₁) * r₂, (x - e₂) * r₁, y,
              fun h0 => mul_ne_zero hr₁_ne hr₂_ne h0.1, ?_, ?_⟩
            · linear_combination (x - e₁) * r₂ ^ 2 * hr₁ - (x - e₂) * r₁ ^ 2 * hr₂
            · linear_combination -(d₁ : F) * (d₂ : F) * heq + (e₃ - e₁) * r₂ ^ 2 * hr₁ -
                (d₁ : F) * (x - e₁) * (x - e₃) * hr₂
  have hv_ne : ∀ (a b c : F), a ≠ b → a ≠ c → ∀ P : W.Point, pointKummerVal a b c P ≠ 0 := by
    intro a b c hab hac P
    cases P with
    | zero => exact one_ne_zero
    | @some x y _ =>
      dsimp [pointKummerVal]
      split_ifs with hx
      · exact mul_ne_zero (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hac)
      · exact sub_ne_zero.mpr hx
  have hv_neg : ∀ (a b c : F) (P : W.Point), pointKummerVal a b c (-P) = pointKummerVal a b c P := by
    intro a b c P
    cases P with
    | zero => rfl
    | @some x y h =>
      rw [WeierstrassCurve.Affine.Point.neg_some]
      rfl
  have hv1_ne : ∀ P : W.Point, pointKummerVal e₁ e₂ e₃ P ≠ 0 := hv_ne e₁ e₂ e₃ h₁₂ h₁₃
  have hv2_ne : ∀ P : W.Point, pointKummerVal e₂ e₁ e₃ P ≠ 0 := hv_ne e₂ e₁ e₃ h₁₂.symm h₂₃
  have h_sqCl_eq : ∀ u v : Fˣ, sqCl u = sqCl v ↔ IsSquare ((u : F) * (v : F)) := by
    intro u v
    dsimp [sqCl]
    rw [QuotientGroup.eq, MonoidHom.mem_range]
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨(u : F) * (w : F), ?_⟩
      have hw' : (u : F) * (w : F) ^ 2 = (v : F) := by
        have h1 : u * w ^ 2 = v := by
          calc u * w ^ 2 = u * (u⁻¹ * v) := by rw [← hw]; rfl
            _ = v := mul_inv_cancel_left u v
        exact_mod_cast h1
      linear_combination -(u : F) * hw'
    · rintro ⟨r, hr⟩
      have hr_ne : r ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hr; exact mul_ne_zero u.ne_zero v.ne_zero hr
      refine ⟨u⁻¹ * Units.mk0 r hr_ne, ?_⟩
      ext
      simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_mk0]
      have hu_inv := Units.mul_inv u
      apply (mul_right_inj' (pow_ne_zero 2 u.ne_zero)).mp
      linear_combination (↑u * ↑u⁻¹ * r ^ 2 + r ^ 2 - ↑u * ↑v) * hu_inv - hr
  have h_isSquare_iff_of_mul : ∀ {A B : F}, A ≠ 0 → B ≠ 0 → IsSquare (A * B) → (IsSquare A ↔ IsSquare B) := by
    intro A B hA hB ⟨s, hs⟩
    constructor
    · rintro ⟨r, rfl⟩
      refine ⟨s / r, ?_⟩
      rw [div_mul_div_comm, ← hs, mul_div_cancel_left₀ B hA]
    · rintro ⟨r, rfl⟩
      refine ⟨s / r, ?_⟩
      rw [div_mul_div_comm, ← hs, mul_div_cancel_right₀ A hB]
  have h_mem_D : ∀ R : W.Point, R ∈ D ↔
      IsSquare (pointKummerVal e₁ e₂ e₃ R) ∧ IsSquare (pointKummerVal e₂ e₁ e₃ R) := by
    intro R
    rw [AddMonoidHom.mem_range]
    constructor
    · rintro ⟨Q, rfl⟩
      change IsSquare (pointKummerVal e₁ e₂ e₃ (Q + Q)) ∧ IsSquare (pointKummerVal e₂ e₁ e₃ (Q + Q))
      have h1 := isSquare_pointKummerVal_add e₁ e₂ e₃ h₁₂ h₁₃ (fun _ => rfl) Q Q
      have h2 := isSquare_pointKummerVal_add e₂ e₁ e₃ h₁₂.symm h₂₃ (fun _ => by ring) Q Q
      exact ⟨(h_isSquare_iff_of_mul (mul_ne_zero (hv1_ne Q) (hv1_ne Q)) (hv1_ne (Q + Q)) h1).mp ⟨pointKummerVal e₁ e₂ e₃ Q, rfl⟩,
             (h_isSquare_iff_of_mul (mul_ne_zero (hv2_ne Q) (hv2_ne Q)) (hv2_ne (Q + Q)) h2).mp ⟨pointKummerVal e₂ e₁ e₃ Q, rfl⟩⟩
    · rintro ⟨h1, h2⟩
      rcases exists_double_eq_of_isSquare_pointKummerVal R h1 h2 with ⟨Q, hQ⟩
      exact ⟨Q, hQ⟩
  let δ : W.Point → SqCl F × SqCl F := fun P =>
    (sqCl (Units.mk0 (pointKummerVal e₁ e₂ e₃ P) (hv1_ne P)),
     sqCl (Units.mk0 (pointKummerVal e₂ e₁ e₃ P) (hv2_ne P)))
  have h_rel : QuotientAddGroup.leftRel D = Setoid.ker δ := by
    ext P Q
    rw [QuotientAddGroup.leftRel_apply, Setoid.ker_def, h_mem_D]
    dsimp [δ]
    rw [Prod.mk.injEq, h_sqCl_eq, h_sqCl_eq]
    dsimp
    have h1 := isSquare_pointKummerVal_add e₁ e₂ e₃ h₁₂ h₁₃ (fun _ => rfl) (-P) Q
    have h2 := isSquare_pointKummerVal_add e₂ e₁ e₃ h₁₂.symm h₂₃ (fun _ => by ring) (-P) Q
    rw [hv_neg e₁ e₂ e₃ P] at h1
    rw [hv_neg e₂ e₁ e₃ P] at h2
    exact and_congr
      (h_isSquare_iff_of_mul (mul_ne_zero (hv1_ne P) (hv1_ne Q)) (hv1_ne (-P + Q)) h1).symm
      (h_isSquare_iff_of_mul (mul_ne_zero (hv2_ne P) (hv2_ne Q)) (hv2_ne (-P + Q)) h2).symm
  have h_range : Set.range δ = { c : SqCl F × SqCl F |
      ∃ d₁ d₂ : Fˣ, c = (sqCl d₁, sqCl d₂) ∧ IsDescentClass e₁ e₂ e₃ (d₁ : F) (d₂ : F) } := by
    ext ⟨c₁, c₂⟩
    simp only [Set.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨P, hP⟩
      injection hP with hP1 hP2
      subst hP1 hP2
      refine ⟨Units.mk0 (pointKummerVal e₁ e₂ e₃ P) (hv1_ne P),
              Units.mk0 (pointKummerVal e₂ e₁ e₃ P) (hv2_ne P), rfl, ?_⟩
      rw [isDescentClass_iff_exists_point]
      exact ⟨P, ⟨pointKummerVal e₁ e₂ e₃ P, rfl⟩, ⟨pointKummerVal e₂ e₁ e₃ P, rfl⟩⟩
    · rintro ⟨d₁, d₂, h_eq, hdesc⟩
      injection h_eq with hc1 hc2
      subst hc1 hc2
      rw [isDescentClass_iff_exists_point] at hdesc
      rcases hdesc with ⟨P, h1, h2⟩
      refine ⟨P, Prod.ext ?_ ?_⟩
      · rw [h_sqCl_eq]; dsimp; rw [mul_comm]; exact h1
      · rw [h_sqCl_eq]; dsimp; rw [mul_comm]; exact h2
  rw [← Nat.card_coe_set_eq, ← h_range]
  change _ = Nat.card (Quotient (QuotientAddGroup.leftRel D))
  rw [h_rel]
  exact (Nat.card_congr (Setoid.quotientKerEquivRange δ)).symm

theorem natCard_sqCl_adicCompletion_eq_two_mul_units_mod_sq {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Nat.card (SqCl (v.adicCompletion K)) =
      2 * Nat.card ((↥(v.adicCompletionIntegers K))ˣ ⧸
        (powMonoidHom 2 : (↥(v.adicCompletionIntegers K))ˣ →* (↥(v.adicCompletionIntegers K))ˣ).range) :=
by
  have h_gen : ∀ (F : Type _) [Field F] [Valued F (WithZero (Multiplicative ℤ))]
      (ϖ : Fˣ), Valued.v (ϖ : F) = WithZero.exp (-1 : ℤ) →
      Nat.card (SqCl F) =
        2 * Nat.card ((↥(Valued.v.valuationSubring : ValuationSubring F))ˣ ⧸
          (powMonoidHom 2 : (↥(Valued.v.valuationSubring : ValuationSubring F))ˣ →*
            (↥(Valued.v.valuationSubring : ValuationSubring F))ˣ).range) := by
    intro F _ _ ϖ hϖ_val
    let A : ValuationSubring F := Valued.v.valuationSubring
    let U : Subgroup Fˣ := A.unitGroup
    let S : Subgroup Fˣ := (powMonoidHom 2 : Fˣ →* Fˣ).range
    let S_A : Subgroup (↥A)ˣ := (powMonoidHom 2 : (↥A)ˣ →* (↥A)ˣ).range
    let ord : Fˣ → ℤ := fun x => WithZero.log (Valued.v (x : F))
    have hv_ne : ∀ x : Fˣ, Valued.v (x : F) ≠ 0 :=
      fun x => (Valuation.ne_zero_iff Valued.v).mpr (Units.ne_zero x)
    have hord_ϖ : ord ϖ = -1 := by
      dsimp [ord]
      rw [hϖ_val, WithZero.log_exp]
    have hord_mul : ∀ x y : Fˣ, ord (x * y) = ord x + ord y := by
      intro x y
      dsimp [ord]
      rw [Valuation.map_mul, WithZero.log_mul (hv_ne x) (hv_ne y)]
    have hord_sq : ∀ x : Fˣ, ord (x ^ 2) = ord x + ord x := by
      intro x
      rw [sq, hord_mul]
    have hord_zpow : ∀ (x : Fˣ) (k : ℤ), ord (x ^ k) = k * ord x := by
      intro x k
      dsimp [ord]
      rw [Units.val_zpow_eq_zpow_val, map_zpow₀, WithZero.log_zpow, smul_eq_mul]
    have hord_ϖ_zpow : ∀ k : ℤ, ord (ϖ ^ k) = -k := by
      intro k
      rw [hord_zpow, hord_ϖ]
      ring
    have hmem_U : ∀ x : Fˣ, x ∈ U ↔ ord x = 0 := by
      intro x
      change x ∈ Valued.v.valuationSubring.unitGroup ↔ ord x = 0
      rw [Valuation.mem_unitGroup_iff]
      dsimp [ord]
      constructor
      · intro h
        rw [h, WithZero.log_one]
      · intro h
        rw [← WithZero.exp_log (hv_ne x), h, WithZero.exp_zero]
    have hmem_sup : ∀ x : Fˣ, x ∈ U ⊔ S ↔ Even (ord x) := by
      intro x
      rw [Subgroup.mem_sup]
      constructor
      · rintro ⟨u, hu, s, hs, rfl⟩
        rcases hs with ⟨y, hy⟩
        rw [powMonoidHom_apply] at hy
        subst hy
        rw [hord_mul, (hmem_U u).mp hu, zero_add, hord_sq]
        exact ⟨ord y, rfl⟩
      · rintro ⟨k, hk⟩
        refine ⟨x * (ϖ ^ k) ^ 2, ?_, (ϖ ^ (-k)) ^ 2, ⟨ϖ ^ (-k), powMonoidHom_apply 2 (ϖ ^ (-k))⟩, ?_⟩
        · rw [hmem_U, hord_mul, hord_sq, hord_ϖ_zpow, hk]
          ring
        · rw [mul_assoc, ← mul_pow, ← zpow_add, add_neg_cancel, zpow_zero, one_pow, mul_one]
    have h_sup_index : (U ⊔ S).index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨ϖ, fun b => ?_⟩
      rw [Xor', hmem_sup, hmem_sup, hord_mul, hord_ϖ]
      rcases Int.even_or_odd (ord b) with ⟨k, hk⟩ | ⟨k, hk⟩
      · right
        refine ⟨⟨k, hk⟩, ?_⟩
        rintro ⟨m, hm⟩
        omega
      · left
        refine ⟨⟨k, by omega⟩, ?_⟩
        rintro ⟨m, hm⟩
        omega
    have h_index_eq : S.index = 2 * S.relIndex U := by
      have h1 := Subgroup.relIndex_mul_index (le_sup_right : S ≤ U ⊔ S)
      have h2 := Subgroup.relIndex_sup_right U S
      rw [h2, h_sup_index, mul_comm] at h1
      exact h1.symm
    let e_A : ↥U ≃* (↥A)ˣ := A.unitGroupMulEquiv
    have h_map : Subgroup.map e_A.toMonoidHom (S.subgroupOf U) = S_A := by
      ext w
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨u, hu, rfl⟩
        rw [Subgroup.mem_subgroupOf] at hu
        rcases hu with ⟨y, hy⟩
        rw [powMonoidHom_apply] at hy
        have hy_ord : ord y = 0 := by
          have h1 : ord (y ^ 2) = ord (u : Fˣ) := congrArg ord hy
          rw [hord_sq, (hmem_U (u : Fˣ)).mp u.2] at h1
          omega
        have hy_U : y ∈ U := (hmem_U y).mpr hy_ord
        let v_u : ↥U := ⟨y, hy_U⟩
        have hv_sq : v_u ^ 2 = u := Subtype.ext hy
        refine ⟨e_A v_u, ?_⟩
        rw [powMonoidHom_apply, ← map_pow, hv_sq]
        rfl
      · rintro ⟨z, hz⟩
        rw [powMonoidHom_apply] at hz
        subst hz
        let v_u : ↥U := e_A.symm z
        refine ⟨v_u ^ 2, ?_, ?_⟩
        · rw [Subgroup.mem_subgroupOf]
          exact ⟨(v_u : Fˣ), powMonoidHom_apply 2 (v_u : Fˣ)⟩
        · change e_A (v_u ^ 2) = z ^ 2
          rw [map_pow]
          simp [v_u]
    have h_relIndex : S.relIndex U = Nat.card ((↥A)ˣ ⧸ S_A) :=
      Nat.card_congr (QuotientGroup.congr (S.subgroupOf U) S_A e_A h_map).toEquiv
    change S.index = 2 * Nat.card ((↥A)ˣ ⧸ S_A)
    rw [h_index_eq, h_relIndex]
  obtain ⟨π₀, hπ₀⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer K v
  let π : v.adicCompletion K := algebraMap K (v.adicCompletion K) π₀
  have hπ_val : Valued.v π = WithZero.exp (-1 : ℤ) := by
    change Valued.v ((π₀ : K) : v.adicCompletion K) = WithZero.exp (-1 : ℤ)
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hπ₀
  have hπ_ne : π ≠ 0 := by
    intro h0
    have hv0 : Valued.v π = 0 := by rw [h0, Valuation.map_zero]
    rw [hπ_val] at hv0
    exact WithZero.exp_ne_zero hv0
  exact h_gen (v.adicCompletion K) (Units.mk0 π hπ_ne) hπ_val

theorem finite_quotient_adicCompletionIntegers_of_ne_zero {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (a : ↥(v.adicCompletionIntegers K)) (ha : a ≠ 0) :
    Finite (↥(v.adicCompletionIntegers K) ⧸ Ideal.span {a}) :=
by
  classical
  let A := NumberField.RingOfIntegers K
  let F := v.adicCompletion K
  let R := ↥(v.adicCompletionIntegers K)
  have h_approx : ∀ (a₀ b₀ : A), b₀ ≠ 0 → v.intValuation a₀ ≤ v.intValuation b₀ →
      ∃ r : A, v.intValuation (a₀ - r * b₀) < v.intValuation b₀ := by
    intro a₀ b₀ hb₀ hle
    let m : ℕ := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {b₀})).factors
    have hb₀_val : v.intValuation b₀ = WithZero.exp (-(m : ℤ)) :=
      v.intValuation_if_neg hb₀
    have ha₀_mem : a₀ ∈ v.asIdeal ^ m := by
      rw [← v.intValuation_le_pow_iff_mem]
      exact hle.trans (le_of_eq hb₀_val)
    have hb₀_mem : b₀ ∈ v.asIdeal ^ m := by
      rw [← v.intValuation_le_pow_iff_mem]
      exact le_of_eq hb₀_val
    have hb₀_not_mem : b₀ ∉ v.asIdeal ^ (m + 1) := by
      rw [← v.intValuation_le_pow_iff_mem, hb₀_val, Nat.cast_add, Nat.cast_one,
          WithZero.exp_le_exp]
      omega
    let I : Ideal A := Ideal.span {b₀} ⊔ v.asIdeal ^ (m + 1)
    have hI_le : I ≤ v.asIdeal ^ m :=
      sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hb₀_mem)
        (Ideal.pow_le_pow_right (Nat.le_succ m))
    obtain ⟨L, hL⟩ := Ideal.dvd_iff_le.mpr hI_le
    have h_dvd : v.asIdeal ^ m * L ∣ v.asIdeal ^ m * v.asIdeal := by
      rw [← hL, ← pow_succ, Ideal.dvd_iff_le]
      exact le_sup_right
    have hv_le_L : v.asIdeal ≤ L := by
      rw [← Ideal.dvd_iff_le]
      exact (mul_dvd_mul_iff_left (pow_ne_zero m v.ne_bot)).mp h_dvd
    have hL_top : L = ⊤ := by
      by_contra hL_ne_top
      have hv_eq_L : v.asIdeal = L := v.isMaximal.eq_of_le hL_ne_top hv_le_L
      have hI_eq : I = v.asIdeal ^ (m + 1) := by
        rw [hL, ← hv_eq_L, pow_succ]
      apply hb₀_not_mem
      rw [← hI_eq]
      exact SetLike.le_def.mp le_sup_left (Ideal.subset_span (Set.mem_singleton b₀))
    have hI_eq_m : I = v.asIdeal ^ m := by
      rw [hL, hL_top, Ideal.mul_top]
    have ha₀_I : a₀ ∈ I := hI_eq_m.symm ▸ ha₀_mem
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp ha₀_I
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hy
    refine ⟨r, ?_⟩
    have h_sub : a₀ - r * b₀ ∈ v.asIdeal ^ (m + 1) := by
      have h_eq : a₀ - r * b₀ = z := by linear_combination -hyz
      rw [h_eq]
      exact hz
    have h_val_le : v.intValuation (a₀ - r * b₀) ≤ WithZero.exp (-((m + 1 : ℕ) : ℤ)) :=
      (v.intValuation_le_pow_iff_mem (a₀ - r * b₀) (m + 1)).mpr h_sub
    apply lt_of_le_of_lt h_val_le
    rw [hb₀_val, Nat.cast_add, Nat.cast_one, WithZero.exp_lt_exp]
    omega
  have h_dense : ∀ x : R, ∃ r : A, algebraMap A R r - x ∈ IsLocalRing.maximalIdeal R := by
    intro x
    have h_nhds : { y : F | Valued.v (y - (x : F)) < 1 } ∈ nhds (x : F) := by
      rw [Valued.mem_nhds]
      exact ⟨1, by intro y hy; simpa only [Units.val_one] using hy⟩
    obtain ⟨k, hk_lt⟩ : ∃ k : K, Valued.v ((k : F) - (x : F)) < 1 :=
      DenseRange.mem_nhds UniformSpace.Completion.denseRange_coe h_nhds
    have hx_le : Valued.v (x : F) ≤ 1 := x.property
    have hk_val_F : Valued.v (k : F) ≤ 1 := by
      have h_eq : (k : F) = ((k : F) - (x : F)) + (x : F) := by ring
      rw [h_eq]
      exact (Valuation.map_add Valued.v _ _).trans (max_le (le_of_lt hk_lt) hx_le)
    have hk_val : v.valuation K k ≤ 1 := by
      rwa [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k] at hk_val_F
    obtain ⟨a₀, b₀, hb₀_mem, hk_div⟩ := IsFractionRing.div_surjective (A := A) k
    have hb₀ : b₀ ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb₀_mem
    have hb₀_val_ne : v.intValuation b₀ ≠ 0 := by
      rw [v.intValuation_if_neg hb₀]
      exact WithZero.exp_ne_zero
    have hle : v.intValuation a₀ ≤ v.intValuation b₀ := by
      rw [← hk_div, Valuation.map_div,
          IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
          IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
          div_le_one₀ (zero_lt_iff.mpr hb₀_val_ne)] at hk_val
      exact hk_val
    obtain ⟨r, hr⟩ := h_approx a₀ b₀ hb₀ hle
    refine ⟨r, ?_⟩
    have hb₀_K : algebraMap A K b₀ ≠ 0 :=
      (IsFractionRing.injective A K).ne hb₀
    have hk_sub : k - algebraMap A K r =
        algebraMap A K (a₀ - r * b₀) / algebraMap A K b₀ := by
      rw [← hk_div, map_sub, map_mul, sub_div, mul_div_cancel_right₀ _ hb₀_K]
    have hr_K : v.valuation K (k - algebraMap A K r) < 1 := by
      rw [hk_sub, Valuation.map_div,
          IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
          IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
          div_lt_one₀ (zero_lt_iff.mpr hb₀_val_ne)]
      exact hr
    have hr_F : Valued.v (((algebraMap A R r : R) : F) - (k : F)) < 1 := by
      have h_coe : ((algebraMap A R r : R) : F) = ((algebraMap A K r : K) : F) := rfl
      rw [h_coe, ← UniformSpace.Completion.coe_sub,
          IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
          Valuation.map_sub_swap]
      exact hr_K
    have h_diff_lt : Valued.v (((algebraMap A R r - x : R) : F)) < 1 := by
      have h_eq : ((algebraMap A R r - x : R) : F) =
          (((algebraMap A R r : R) : F) - (k : F)) + ((k : F) - (x : F)) := by
        change ((algebraMap A R r : R) : F) - (x : F) =
          (((algebraMap A R r : R) : F) - (k : F)) + ((k : F) - (x : F))
        ring
      rw [h_eq]
      exact lt_of_le_of_lt (Valuation.map_add Valued.v _ _) (max_lt hr_F hk_lt)
    change (algebraMap A R r - x : ↥(Valued.v.valuationSubring)) ∈
      IsLocalRing.maximalIdeal ↥(Valued.v.valuationSubring)
    rw [Valuation.mem_maximalIdeal_iff]
    exact h_diff_lt
  have h_ker : ∀ r ∈ v.asIdeal,
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (algebraMap A R r) = 0 := by
    intro r hr
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change (algebraMap A R r : ↥(Valued.v.valuationSubring)) ∈
      IsLocalRing.maximalIdeal ↥(Valued.v.valuationSubring)
    rw [Valuation.mem_maximalIdeal_iff]
    change Valued.v (((algebraMap A K r : K) : F)) < 1
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact (v.intValuation_lt_one_iff_mem r).mpr hr
  let ϕ : A ⧸ v.asIdeal →+* R ⧸ IsLocalRing.maximalIdeal R :=
    Ideal.Quotient.lift v.asIdeal
      ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)).comp (algebraMap A R)) h_ker
  have hϕ_surj : Function.Surjective ϕ := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, hr⟩ := h_dense x
    refine ⟨Ideal.Quotient.mk v.asIdeal r, ?_⟩
    change Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (algebraMap A R r) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) x
    exact Ideal.Quotient.eq.mpr hr
  haveI : Finite (A ⧸ v.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  haveI : Finite (R ⧸ IsLocalRing.maximalIdeal R) :=
    Finite.of_surjective ϕ hϕ_surj
  have ha_span : Ideal.span {a} ≠ ⊥ := mt Ideal.span_singleton_eq_bot.mp ha
  obtain ⟨n, hn⟩ :=
    exists_maximalIdeal_pow_eq_of_principal R inferInstance (Ideal.span {a}) ha_span
  rw [hn]
  exact Ideal.finite_quotient_pow (Submodule.IsPrincipal.fg inferInstance) n

theorem exists_add_mul_sq_eq_adicCompletionIntegers {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (p y : ↥(v.adicCompletionIntegers K))
    (hp : Valued.v (p : v.adicCompletion K) < 1) :
    ∃ z : ↥(v.adicCompletionIntegers K), z + p * z ^ 2 = y :=
by
  let F := v.adicCompletion K
  have hp_le : Valued.v (p : F) ≤ WithZero.exp (-1 : ℤ) := by
    by_cases hp0 : (p : F) = 0
    · simp [hp0]
    · have hv0 : Valued.v (p : F) ≠ 0 := (Valuation.ne_zero_iff Valued.v).mpr hp0
      have hlog : WithZero.log (Valued.v (p : F)) < 0 := by
        rw [← WithZero.exp_lt_exp, WithZero.exp_log hv0, WithZero.exp_zero]
        exact hp
      have hlog_le : WithZero.log (Valued.v (p : F)) ≤ -1 := by omega
      rw [← WithZero.exp_log hv0, WithZero.exp_le_exp]
      exact hlog_le
  let z : ℕ → ↥(v.adicCompletionIntegers K) := fun n => Nat.rec 0 (fun _ zn => y - p * zn ^ 2) n
  let a : ℕ → F := fun n => (z n).1
  have ha_mem : ∀ n : ℕ, Valued.v (a n) ≤ 1 := fun n => (z n).property
  have ha_zero : a 0 = 0 := rfl
  have ha_succ : ∀ n : ℕ, a (n + 1) = (y : F) - (p : F) * a n ^ 2 := fun n => by
    simp [a, z, F]
  have h_diff : ∀ n : ℕ, Valued.v (a (n + 1) - a n) ≤ WithZero.exp (-(n : ℤ)) := by
    intro n
    induction n with
    | zero =>
      have h10 : a (0 + 1) - a 0 = (y : F) := by
        rw [ha_succ 0, ha_zero]
        ring
      rw [h10, Nat.cast_zero, neg_zero, WithZero.exp_zero]
      exact y.property
    | succ n ih =>
      have h_id : a (n + 2) - a (n + 1) = -((p : F) * (a (n + 1) + a n) * (a (n + 1) - a n)) := by
        rw [ha_succ (n + 1), ha_succ n]
        ring
      rw [h_id, Valuation.map_neg, Valuation.map_mul, Valuation.map_mul]
      have h_add : Valued.v (a (n + 1) + a n) ≤ 1 :=
        le_trans (Valuation.map_add Valued.v (a (n + 1)) (a n)) (max_le (ha_mem (n + 1)) (ha_mem n))
      have h_mul1 : Valued.v (p : F) * Valued.v (a (n + 1) + a n) ≤ WithZero.exp (-1 : ℤ) := by
        calc Valued.v (p : F) * Valued.v (a (n + 1) + a n)
          _ ≤ WithZero.exp (-1 : ℤ) * 1 := mul_le_mul' hp_le h_add
          _ = WithZero.exp (-1 : ℤ) := mul_one _
      calc Valued.v (p : F) * Valued.v (a (n + 1) + a n) * Valued.v (a (n + 1) - a n)
        _ ≤ WithZero.exp (-1 : ℤ) * WithZero.exp (-(n : ℤ)) := mul_le_mul' h_mul1 ih
        _ = WithZero.exp (-1 + -(n : ℤ)) := (WithZero.exp_add (-1 : ℤ) (-(n : ℤ))).symm
        _ = WithZero.exp (-((n + 1 : ℕ) : ℤ)) := by congr 1; push_cast; ring
  have h_tail : ∀ n k : ℕ, Valued.v (a (n + k) - a n) ≤ WithZero.exp (-(n : ℤ)) := by
    intro n k
    induction k with
    | zero =>
      simp
    | succ k ih =>
      have h_split : a (n + (k + 1)) - a n = (a (n + k + 1) - a (n + k)) + (a (n + k) - a n) := by
        rw [← Nat.add_assoc]
        ring
      rw [h_split]
      refine le_trans (Valuation.map_add Valued.v _ _) (max_le ?_ ih)
      refine le_trans (h_diff (n + k)) ?_
      rw [WithZero.exp_le_exp]
      omega
  have h_tail2 : ∀ N m n : ℕ, N ≤ m → N ≤ n → Valued.v (a n - a m) ≤ WithZero.exp (-(N : ℤ)) := by
    intro N m n hm hn
    have h_sub : a n - a m = (a n - a N) - (a m - a N) := by ring
    rw [h_sub]
    refine le_trans (Valuation.map_sub Valued.v _ _) (max_le ?_ ?_)
    · have hn' := h_tail N (n - N)
      rwa [Nat.add_sub_of_le hn] at hn'
    · have hm' := h_tail N (m - N)
      rwa [Nat.add_sub_of_le hm] at hm'
  have h_cauchy : CauchySeq a := by
    rw [CauchySeq, Valued.cauchy_iff]
    refine ⟨Filter.map_neBot, fun γ => ?_⟩
    let g : WithZero (Multiplicative ℤ) := (γ : WithZero (Multiplicative ℤ))
    have hg0 : g ≠ 0 := Units.ne_zero γ
    let N : ℕ := (-WithZero.log g + 1).toNat
    have hN_lt : WithZero.exp (-(N : ℤ)) < g := by
      rw [← WithZero.exp_log hg0, WithZero.exp_lt_exp]
      omega
    refine ⟨a '' {n : ℕ | N ≤ n}, Filter.image_mem_map (Filter.mem_atTop N), ?_⟩
    rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩
    exact lt_of_le_of_lt (h_tail2 N m n hm hn) hN_lt
  obtain ⟨a_lim, ha_lim⟩ := cauchySeq_tendsto_of_complete h_cauchy
  have ha_lim_mem : a_lim ∈ v.adicCompletionIntegers K := by
    have h_closed : IsClosed (v.adicCompletionIntegers K : Set F) := Valued.isClosed_integer F
    exact h_closed.mem_of_tendsto ha_lim (Filter.Eventually.of_forall (fun n => (z n).property))
  let z_lim : ↥(v.adicCompletionIntegers K) := ⟨a_lim, ha_lim_mem⟩
  have h_lhs : Filter.Tendsto (fun n => a (n + 1)) Filter.atTop (nhds a_lim) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mpr ha_lim
  have h_rhs : Filter.Tendsto (fun n => (y : F) - (p : F) * a n ^ 2) Filter.atTop
      (nhds ((y : F) - (p : F) * a_lim ^ 2)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul (ha_lim.pow 2))
  have h_seq_eq : (fun n => a (n + 1)) = (fun n => (y : F) - (p : F) * a n ^ 2) :=
    funext ha_succ
  rw [h_seq_eq] at h_lhs
  have h_lim_eq : a_lim = (y : F) - (p : F) * a_lim ^ 2 :=
    tendsto_nhds_unique h_lhs h_rhs
  refine ⟨z_lim, Subtype.ext ?_⟩
  change a_lim + (p : F) * a_lim ^ 2 = (y : F)
  linear_combination h_lim_eq

theorem natCard_units_mod_sq_eq_two_mul_quotient_span_two {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (p : R) (hp₀ : p ≠ 0)
    (hp_unit : ∀ x : R, IsUnit (1 + p * x))
    (hp_hensel : ∀ y : R, ∃ z : R, z + p * z ^ 2 = y)
    (h_fin : Finite (R ⧸ Ideal.span {2 * p})) :
    Nat.card (Rˣ ⧸ (powMonoidHom 2 : Rˣ →* Rˣ).range) =
      2 * Nat.card (R ⧸ Ideal.span {(2 : R)}) :=
by
  let s : Rˣ →* Rˣ := powMonoidHom 2
  let U : R → Subgroup Rˣ := fun c =>
    (Units.map (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom).ker
  have h_mem : ∀ (c : R) (u : Rˣ), u ∈ U c ↔ ∃ z : R, (u : R) = 1 + c * z := by
    intro c u
    rw [MonoidHom.mem_ker, Units.ext_iff]
    change Ideal.Quotient.mk (Ideal.span {c}) (u : R) = Ideal.Quotient.mk (Ideal.span {c}) 1 ↔ _
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z, by linear_combination hz⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, by linear_combination hz⟩
  let U₁ : Subgroup Rˣ := U (2 * p)
  let U₂ : Subgroup Rˣ := U (4 * p)
  let u₁ : R → Rˣ := fun z => (hp_unit (2 * z)).unit
  have hu₁_val : ∀ z : R, ((u₁ z : Rˣ) : R) = 1 + (2 * p) * z := by
    intro z
    dsimp [u₁]
    ring
  have hu₁_mem : ∀ z : R, u₁ z ∈ U₁ := by
    intro z
    rw [h_mem]
    exact ⟨z, hu₁_val z⟩
  have hU₂₁ : U₂ ≤ U₁ := by
    intro u hu
    rw [h_mem] at hu ⊢
    rcases hu with ⟨y, hy⟩
    exact ⟨2 * y, by linear_combination hy⟩
  haveI hU₁_fin : Finite (Rˣ ⧸ U₁) := by
    let φ := Units.map (Ideal.Quotient.mk (Ideal.span {2 * p})).toMonoidHom
    have h_inj : Function.Injective (fun x : Rˣ ⧸ U₁ => ((QuotientGroup.kerLift φ x : (R ⧸ Ideal.span {2 * p})ˣ) : R ⧸ Ideal.span {2 * p})) :=
      Units.val_injective.comp (QuotientGroup.kerLift_injective φ)
    exact Finite.of_injective _ h_inj
  have hU₁_idx : U₁.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h_map : U₁.map s = U₂ := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      intro u hu
      rw [Subgroup.mem_comap, h_mem]
      rw [h_mem] at hu
      rcases hu with ⟨z, hz⟩
      refine ⟨z + p * z ^ 2, ?_⟩
      change ((u ^ 2 : Rˣ) : R) = 1 + (4 * p) * (z + p * z ^ 2)
      rw [Units.val_pow_eq_pow_val, hz]
      ring
    · intro w hw
      rw [h_mem] at hw
      rcases hw with ⟨y, hy⟩
      obtain ⟨z, hz⟩ := hp_hensel y
      rw [Subgroup.mem_map]
      refine ⟨u₁ z, hu₁_mem z, ?_⟩
      apply Units.ext
      change ((u₁ z ^ 2 : Rˣ) : R) = (w : R)
      rw [Units.val_pow_eq_pow_val, hu₁_val z, hy, ← hz]
      ring
  have h_ker_mem : ∀ u : Rˣ, u ∈ s.ker ↔ u = 1 ∨ u = -1 := by
    intro u
    rw [MonoidHom.mem_ker]
    change u ^ 2 = 1 ↔ u = 1 ∨ u = -1
    rw [Units.ext_iff, Units.ext_iff, Units.ext_iff, Units.val_pow_eq_pow_val,
        Units.val_one, Units.val_neg, Units.val_one, sq_eq_one_iff]
  have h_one_ne_neg_one : (1 : Rˣ) ≠ -1 := by
    intro h
    have h' : (1 : R) = -1 := by
      have := congrArg Units.val h
      simpa using this
    have h2 : (2 : R) = 0 := by linear_combination h'
    exact two_ne_zero h2
  have h_neg_one_not_mem : (-1 : Rˣ) ∉ U₁ := by
    intro h
    rw [h_mem] at h
    rcases h with ⟨z, hz⟩
    have hz' : (-1 : R) = 1 + (2 * p) * z := by simpa using hz
    have h0 : (2 : R) * (1 + p * z) = 0 := by linear_combination -hz'
    rcases mul_eq_zero.mp h0 with h2 | hpz
    · exact two_ne_zero h2
    · exact (hp_unit z).ne_zero hpz
  have h_inf_bot : U₁ ⊓ s.ker = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rcases hu with ⟨hu₁, hus⟩
    rw [Subgroup.mem_bot]
    rcases (h_ker_mem u).mp hus with rfl | rfl
    · rfl
    · exact False.elim (h_neg_one_not_mem hu₁)
  have h_neg_one_ker : (-1 : Rˣ) ∈ s.ker := (h_ker_mem (-1)).mpr (Or.inr rfl)
  have h_card_ker : Nat.card ↥s.ker = 2 := by
    let f : Bool → ↥s.ker := fun b =>
      if b then ⟨1, s.ker.one_mem⟩ else ⟨-1, h_neg_one_ker⟩
    have hf_inj : Function.Injective f := by
      rintro (⟨⟩ | ⟨⟩) (⟨⟩ | ⟨⟩) h
      · rfl
      · exfalso
        apply h_one_ne_neg_one
        exact (congrArg Subtype.val h).symm
      · exfalso
        apply h_one_ne_neg_one
        exact congrArg Subtype.val h
      · rfl
    have hf_surj : Function.Surjective f := by
      rintro ⟨u, hu⟩
      rcases (h_ker_mem u).mp hu with rfl | rfl
      · exact ⟨true, rfl⟩
      · exact ⟨false, rfl⟩
    rw [← Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩),
        Nat.card_eq_fintype_card, Fintype.card_bool]
  have h_rel_ker : U₁.relIndex (U₁ ⊔ s.ker) = 2 := by
    rw [Subgroup.relIndex_sup_left, ← Subgroup.inf_relIndex_right, h_inf_bot,
        Subgroup.relIndex_bot_left, h_card_ker]
  have h_idx_U₁ : 2 * (U₁ ⊔ s.ker).index = U₁.index := by
    rw [← h_rel_ker, Subgroup.relIndex_mul_index (le_sup_left : U₁ ≤ U₁ ⊔ s.ker)]
  have h_sup_idx_ne : (U₁ ⊔ s.ker).index ≠ 0 := by
    intro h0
    apply hU₁_idx
    rw [← h_idx_U₁, h0, mul_zero]
  have h_idx_U₂_1 : U₂.index = (U₁ ⊔ s.ker).index * s.range.index := by
    rw [← h_map, Subgroup.index_map]
  have h_idx_U₂_2 : U₂.index = (U₂.relIndex U₁) * U₁.index :=
    (Subgroup.relIndex_mul_index hU₂₁).symm
  have h_range_idx : s.range.index = 2 * (U₂.relIndex U₁) := by
    apply mul_left_cancel₀ h_sup_idx_ne
    calc
      (U₁ ⊔ s.ker).index * s.range.index = U₂.index := h_idx_U₂_1.symm
      _ = (U₂.relIndex U₁) * U₁.index := h_idx_U₂_2
      _ = (U₂.relIndex U₁) * (2 * (U₁ ⊔ s.ker).index) := by rw [← h_idx_U₁]
      _ = (U₁ ⊔ s.ker).index * (2 * (U₂.relIndex U₁)) := by ring
  let θ_tilde : R → ↥U₁ := fun z => ⟨u₁ z, hu₁_mem z⟩
  let θ : R → ↥U₁ ⧸ U₂.subgroupOf U₁ := fun z => QuotientGroup.mk (θ_tilde z)
  have h2p_ne : (2 * p : R) ≠ 0 := mul_ne_zero two_ne_zero hp₀
  have h_rel : ∀ z₁ z₂ : R, θ z₁ = θ z₂ ↔
      Ideal.Quotient.mk (Ideal.span {(2 : R)}) z₁ = Ideal.Quotient.mk (Ideal.span {(2 : R)}) z₂ := by
    intro z₁ z₂
    dsimp [θ]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, h_mem, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, hy⟩
      have hy' : (((u₁ z₁)⁻¹ : Rˣ) : R) * (u₁ z₂ : R) = 1 + (4 * p) * y := by
        simpa using hy
      refine ⟨-(u₁ z₁ : R) * y, ?_⟩
      apply mul_left_cancel₀ h2p_ne
      have h_mul_inv : (u₁ z₁ : R) * (((u₁ z₁)⁻¹ : Rˣ) : R) = 1 := Units.mul_inv (u₁ z₁)
      have h_u₁ : (u₁ z₁ : R) = 1 + (2 * p) * z₁ := hu₁_val z₁
      have h_u₂ : (u₁ z₂ : R) = 1 + (2 * p) * z₂ := hu₁_val z₂
      linear_combination -h_u₁ + h_u₂ + (u₁ z₂ : R) * h_mul_inv - (u₁ z₁ : R) * hy'
    · rintro ⟨w, hw⟩
      refine ⟨-(((u₁ z₁)⁻¹ : Rˣ) : R) * w, ?_⟩
      change (((u₁ z₁)⁻¹ : Rˣ) : R) * (u₁ z₂ : R) = 1 + (4 * p) * (-(((u₁ z₁)⁻¹ : Rˣ) : R) * w)
      have h_inv_mul : (((u₁ z₁)⁻¹ : Rˣ) : R) * (u₁ z₁ : R) = 1 := Units.inv_mul (u₁ z₁)
      have h_u₁ : (u₁ z₁ : R) = 1 + (2 * p) * z₁ := hu₁_val z₁
      have h_u₂ : (u₁ z₂ : R) = 1 + (2 * p) * z₂ := hu₁_val z₂
      linear_combination h_inv_mul + (((u₁ z₁)⁻¹ : Rˣ) : R) * (h_u₂ - h_u₁ - (2 * p) * hw)
  let θ_bar : R ⧸ Ideal.span {(2 : R)} → ↥U₁ ⧸ U₂.subgroupOf U₁ :=
    Quotient.lift θ (fun a b hab => (h_rel a b).mpr (Quotient.sound hab))
  have hθ_inj : Function.Injective θ_bar := by
    refine Quotient.ind₂ (fun a b hab => ?_)
    exact (h_rel a b).mp hab
  have hθ_surj : Function.Surjective θ_bar := by
    refine Quotient.ind (fun ⟨u, hu⟩ => ?_)
    obtain ⟨z, hz⟩ := (h_mem (2 * p) u).mp hu
    refine ⟨Ideal.Quotient.mk (Ideal.span {(2 : R)}) z, ?_⟩
    change QuotientGroup.mk (θ_tilde z) = QuotientGroup.mk ⟨u, hu⟩
    congr 1
    apply Subtype.ext
    apply Units.ext
    rw [hu₁_val z, hz]
  have h_card_quot : U₂.relIndex U₁ = Nat.card (R ⧸ Ideal.span {(2 : R)}) := by
    change Nat.card (↥U₁ ⧸ U₂.subgroupOf U₁) = Nat.card (R ⧸ Ideal.span {(2 : R)})
    exact (Nat.card_congr (Equiv.ofBijective θ_bar ⟨hθ_inj, hθ_surj⟩)).symm
  rw [← h_card_quot]
  exact h_range_idx

theorem natCard_sqCl_adicCompletion_eq {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Nat.card (SqCl (v.adicCompletion K)) =
      4 * Nat.card (↥(v.adicCompletionIntegers K) ⧸
        Ideal.span {(2 : ↥(v.adicCompletionIntegers K))}) :=
by
  let F := v.adicCompletion K
  let R := ↥(v.adicCompletionIntegers K)
  have h_inj_KF : Function.Injective (algebraMap K F) := (algebraMap K F).injective
  haveI : CharZero F := charZero_of_injective_ringHom h_inj_KF
  haveI : CharZero R := SubsemiringClass.instCharZero (v.adicCompletionIntegers K)
  obtain ⟨π₀, hπ₀⟩ := v.intValuation_exists_uniformizer
  let p : R := algebraMap (NumberField.RingOfIntegers K) R π₀
  have hp_val : Valued.v (p : F) = WithZero.exp (-1 : ℤ) := by
    change Valued.v (((algebraMap (NumberField.RingOfIntegers K) K π₀) : K) : F) = WithZero.exp (-1 : ℤ)
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact hπ₀
  have hp₀ : p ≠ 0 := by
    intro h0
    have h0' : (p : F) = 0 := congrArg Subtype.val h0
    have hv0 : Valued.v (p : F) = 0 := by rw [h0', Valuation.map_zero]
    rw [hp_val] at hv0
    exact WithZero.exp_ne_zero hv0
  have hp_lt : Valued.v (p : F) < 1 := by
    rw [hp_val, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hp_unit : ∀ x : R, IsUnit (1 + p * x) := by
    intro x
    have hx_le : Valued.v (x : F) ≤ 1 := x.property
    have hpx_lt : Valued.v ((p : F) * (x : F)) < Valued.v (1 : F) := by
      rw [Valuation.map_mul, Valuation.map_one]
      exact mul_lt_one_of_lt_of_le hp_lt hx_le
    have h1px_val : Valued.v ((1 + p * x : R) : F) = 1 := by
      change Valued.v ((1 : F) + (p : F) * (x : F)) = 1
      rw [Valued.v.map_add_eq_of_lt_left hpx_lt, Valuation.map_one]
    have h1px_ne : ((1 + p * x : R) : F) ≠ 0 := by
      intro h0
      rw [h0, Valuation.map_zero] at h1px_val
      exact zero_ne_one h1px_val
    have h_inv_mem : ((1 + p * x : R) : F)⁻¹ ∈ v.adicCompletionIntegers K := by
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1px_val, inv_one]
    exact ⟨⟨1 + p * x, ⟨((1 + p * x : R) : F)⁻¹, h_inv_mem⟩,
      Subtype.ext (mul_inv_cancel₀ h1px_ne), Subtype.ext (inv_mul_cancel₀ h1px_ne)⟩, rfl⟩
  have hp_hensel : ∀ y : R, ∃ z : R, z + p * z ^ 2 = y :=
    fun y => exists_add_mul_sq_eq_adicCompletionIntegers v p y hp_lt
  have h2p_ne : (2 * p : R) ≠ 0 := mul_ne_zero two_ne_zero hp₀
  have h_fin : Finite (R ⧸ Ideal.span {2 * p}) :=
    finite_quotient_adicCompletionIntegers_of_ne_zero v (2 * p) h2p_ne
  rw [natCard_sqCl_adicCompletion_eq_two_mul_units_mod_sq v,
      natCard_units_mod_sq_eq_two_mul_quotient_span_two p hp₀ hp_unit hp_hensel h_fin]
  ring

theorem lutzSet_add_mem_and_param {F : Type*} [Field F] [CharZero F] [DecidableEq F]
    [Valued F (WithZero (Multiplicative ℤ))]
    (e₁ e₂ e₃ : F) (B : ℕ) (k : ℤ) (hk : (B : ℤ) + 1 ≤ k)
    (he₁ : Valued.v e₁ ≤ WithZero.exp (B : ℤ))
    (he₂ : Valued.v e₂ ≤ WithZero.exp (B : ℤ))
    (he₃ : Valued.v e₃ ≤ WithZero.exp (B : ℤ)) :
    (∀ P Q : (threeRootsCurve e₁ e₂ e₃).toAffine.Point,
      P ∈ lutzSet e₁ e₂ e₃ k → Q ∈ lutzSet e₁ e₂ e₃ k →
        P + Q ∈ lutzSet e₁ e₂ e₃ k ∧
        lutzParam (P + Q) - (lutzParam P + lutzParam Q) ∈ valBall F (2 * k)) ∧
    (∀ P : (threeRootsCurve e₁ e₂ e₃).toAffine.Point,
      P ∈ lutzSet e₁ e₂ e₃ k → ∀ k' : ℤ, k ≤ k' →
        (P ∈ lutzSet e₁ e₂ e₃ k' ↔ lutzParam P ∈ valBall F k')) :=
by
  have h_s2 :
      (∀ P : (threeRootsCurve e₁ e₂ e₃).toAffine.Point,
        P ∈ lutzSet e₁ e₂ e₃ k → ∀ k' : ℤ, k ≤ k' →
          (P ∈ lutzSet e₁ e₂ e₃ k' ↔ lutzParam P ∈ valBall F k')) ∧
      (∀ x y : F, ((threeRootsCurve e₁ e₂ e₃).toAffine).Equation x y →
        (WithZero.exp (2 * k) ≤ Valued.v x →
          y ≠ 0 ∧ Valued.v (-x / y) ≤ WithZero.exp (-k) ∧
          Valued.v (-1 / y) = Valued.v (-x / y) ^ 3 ∧
          (-1 / y) - ((-x / y) ^ 3 + ((threeRootsCurve e₁ e₂ e₃).toAffine).a₂ * (-x / y) ^ 2 * (-1 / y) +
            ((threeRootsCurve e₁ e₂ e₃).toAffine).a₄ * (-x / y) * (-1 / y) ^ 2 +
            ((threeRootsCurve e₁ e₂ e₃).toAffine).a₆ * (-1 / y) ^ 3) = 0) ∧
        (WithZero.exp (3 * k) ≤ Valued.v y → WithZero.exp (2 * k) ≤ Valued.v x)) := by
    have hB_lt : WithZero.exp (B : ℤ) < WithZero.exp (2 * k) :=
      WithZero.exp_lt_exp.mpr (by omega)
    have h_coords : ∀ x y : F, ((threeRootsCurve e₁ e₂ e₃).toAffine).Equation x y →
        (WithZero.exp (2 * k) ≤ Valued.v x →
          y ≠ 0 ∧
          (∀ k' : ℤ, WithZero.exp (2 * k') ≤ Valued.v x ↔ Valued.v (-x / y) ≤ WithZero.exp (-k')) ∧
          Valued.v (-1 / y) = Valued.v (-x / y) ^ 3 ∧
          (-1 / y) - ((-x / y) ^ 3 + ((threeRootsCurve e₁ e₂ e₃).toAffine).a₂ * (-x / y) ^ 2 * (-1 / y) +
            ((threeRootsCurve e₁ e₂ e₃).toAffine).a₄ * (-x / y) * (-1 / y) ^ 2 +
            ((threeRootsCurve e₁ e₂ e₃).toAffine).a₆ * (-1 / y) ^ 3) = 0) ∧
        (WithZero.exp (3 * k) ≤ Valued.v y → WithZero.exp (2 * k) ≤ Valued.v x) := by
      intro x y h_eq
      have heq_fac : y ^ 2 = (x - e₁) * (x - e₂) * (x - e₃) := by
        have h := (WeierstrassCurve.Affine.equation_iff x y).mp h_eq
        dsimp [threeRootsCurve] at h
        linear_combination h
      have heq_exp : y ^ 2 = x ^ 3 + ((threeRootsCurve e₁ e₂ e₃).toAffine).a₂ * x ^ 2 +
          ((threeRootsCurve e₁ e₂ e₃).toAffine).a₄ * x + ((threeRootsCurve e₁ e₂ e₃).toAffine).a₆ := by
        have h := (WeierstrassCurve.Affine.equation_iff x y).mp h_eq
        dsimp [threeRootsCurve] at h ⊢
        linear_combination h
      constructor
      · intro hx
        have hv_sub₁ : Valued.v (x - e₁) = Valued.v x :=
          Valuation.map_sub_eq_of_lt_left Valued.v (lt_of_le_of_lt he₁ (lt_of_lt_of_le hB_lt hx))
        have hv_sub₂ : Valued.v (x - e₂) = Valued.v x :=
          Valuation.map_sub_eq_of_lt_left Valued.v (lt_of_le_of_lt he₂ (lt_of_lt_of_le hB_lt hx))
        have hv_sub₃ : Valued.v (x - e₃) = Valued.v x :=
          Valuation.map_sub_eq_of_lt_left Valued.v (lt_of_le_of_lt he₃ (lt_of_lt_of_le hB_lt hx))
        have hvy_sq : Valued.v y ^ 2 = Valued.v x ^ 3 := by
          calc Valued.v y ^ 2 = Valued.v (y ^ 2) := (Valuation.map_pow Valued.v y 2).symm
            _ = Valued.v ((x - e₁) * (x - e₂) * (x - e₃)) := by rw [heq_fac]
            _ = Valued.v (x - e₁) * Valued.v (x - e₂) * Valued.v (x - e₃) := by
                rw [Valuation.map_mul, Valuation.map_mul]
            _ = Valued.v x ^ 3 := by rw [hv_sub₁, hv_sub₂, hv_sub₃, pow_three']
        have hvx_ne : Valued.v x ≠ 0 :=
          ne_of_gt (lt_of_lt_of_le WithZero.exp_pos hx)
        have hvy2_ne : Valued.v y ^ 2 ≠ 0 := by
          rw [hvy_sq]
          exact pow_ne_zero 3 hvx_ne
        have hvy_ne : Valued.v y ≠ 0 := fun h0 => hvy2_ne (by rw [h0, zero_pow (by norm_num)])
        have hy_ne : y ≠ 0 := (Valuation.ne_zero_iff Valued.v).mp hvy_ne
        rcases WithZero.ne_zero_iff_exists.mp hvx_ne with ⟨gx, hgx⟩
        rcases WithZero.ne_zero_iff_exists.mp hvy_ne with ⟨gy, hgy⟩
        let zx : ℤ := Multiplicative.toAdd gx
        let zy : ℤ := Multiplicative.toAdd gy
        have hvx_eq : Valued.v x = WithZero.exp zx := by rw [← hgx]; rfl
        have hvy_eq : Valued.v y = WithZero.exp zy := by rw [← hgy]; rfl
        have h_2zy_3zx : 2 * zy = 3 * zx := by
          have h1 : WithZero.exp (zy + zy) = WithZero.exp (zx + zx + zx) := by
            rw [WithZero.exp_add, WithZero.exp_add, WithZero.exp_add, ← hvx_eq, ← hvy_eq, ← sq, ← pow_three']
            exact hvy_sq
          have hle1 : zy + zy ≤ zx + zx + zx := WithZero.exp_le_exp.mp (le_of_eq h1)
          have hle2 : zx + zx + zx ≤ zy + zy := WithZero.exp_le_exp.mp (le_of_eq h1.symm)
          omega
        have hvt_eq : Valued.v (-x / y) = WithZero.exp (zx - zy) := by
          rw [Valuation.map_div, Valuation.map_neg, hvx_eq, hvy_eq, ← WithZero.exp_sub]
        have hvw_eq : Valued.v (-1 / y) = WithZero.exp (-zy) := by
          rw [Valuation.map_div, Valuation.map_neg, Valuation.map_one, ← WithZero.exp_zero, hvy_eq,
              ← WithZero.exp_sub, zero_sub]
        refine ⟨hy_ne, ?_, ?_, ?_⟩
        · intro k'
          rw [hvx_eq, hvt_eq, WithZero.exp_le_exp, WithZero.exp_le_exp]
          omega
        · rw [hvw_eq, hvt_eq, pow_three', ← WithZero.exp_add, ← WithZero.exp_add]
          congr 1
          omega
        · have h_mul : y ^ 3 * ((-1 / y) - ((-x / y) ^ 3 +
              ((threeRootsCurve e₁ e₂ e₃).toAffine).a₂ * (-x / y) ^ 2 * (-1 / y) +
              ((threeRootsCurve e₁ e₂ e₃).toAffine).a₄ * (-x / y) * (-1 / y) ^ 2 +
              ((threeRootsCurve e₁ e₂ e₃).toAffine).a₆ * (-1 / y) ^ 3)) = 0 := by
            field_simp
            linear_combination -heq_exp
          exact (mul_eq_zero.mp h_mul).resolve_left (pow_ne_zero 3 hy_ne)
      · intro hy
        by_contra h_not_le
        have hvx_le : Valued.v x ≤ WithZero.exp (2 * k - 1) := by
          rcases eq_or_ne (Valued.v x) 0 with hx0 | hx0
          · rw [hx0]; exact zero_le'
          · rcases WithZero.ne_zero_iff_exists.mp hx0 with ⟨gx, hgx⟩
            let zx : ℤ := Multiplicative.toAdd gx
            have hvx_eq : Valued.v x = WithZero.exp zx := by rw [← hgx]; rfl
            rw [hvx_eq, WithZero.exp_le_exp] at h_not_le ⊢
            omega
        have hB_le : WithZero.exp (B : ℤ) ≤ WithZero.exp (2 * k - 1) :=
          WithZero.exp_le_exp.mpr (by omega)
        have hsub₁ : Valued.v (x - e₁) ≤ WithZero.exp (2 * k - 1) :=
          le_trans (Valuation.map_sub Valued.v x e₁) (max_le hvx_le (le_trans he₁ hB_le))
        have hsub₂ : Valued.v (x - e₂) ≤ WithZero.exp (2 * k - 1) :=
          le_trans (Valuation.map_sub Valued.v x e₂) (max_le hvx_le (le_trans he₂ hB_le))
        have hsub₃ : Valued.v (x - e₃) ≤ WithZero.exp (2 * k - 1) :=
          le_trans (Valuation.map_sub Valued.v x e₃) (max_le hvx_le (le_trans he₃ hB_le))
        have hvy2_le : Valued.v (y ^ 2) ≤ WithZero.exp ((2 * k - 1) + (2 * k - 1) + (2 * k - 1)) := by
          rw [heq_fac, Valuation.map_mul, Valuation.map_mul, WithZero.exp_add, WithZero.exp_add]
          exact mul_le_mul' (mul_le_mul' hsub₁ hsub₂) hsub₃
        have hvy2_ge : WithZero.exp (3 * k + 3 * k) ≤ Valued.v (y ^ 2) := by
          rw [Valuation.map_pow, sq, WithZero.exp_add]
          exact mul_le_mul' hy hy
        have h_contra : 3 * k + 3 * k ≤ (2 * k - 1) + (2 * k - 1) + (2 * k - 1) :=
          WithZero.exp_le_exp.mp (le_trans hvy2_ge hvy2_le)
        omega
    refine ⟨?_, ?_⟩
    · intro P hP k' _
      cases P with
      | zero =>
        change True ↔ Valued.v (0 : F) ≤ WithZero.exp (-k')
        simp
      | @some x y h =>
        exact ((h_coords x y h.1).1 hP).2.1 k'
    · intro x y h_eq
      refine ⟨fun hx => ?_, (h_coords x y h_eq).2⟩
      obtain ⟨hy_ne, h_iff, hvw, hE⟩ := (h_coords x y h_eq).1 hx
      exact ⟨hy_ne, (h_iff k).mp hx, hvw, hE⟩
  have h_s3 : ∀ (x₁ y₁ x₂ y₂ : F),
      ((threeRootsCurve e₁ e₂ e₃).toAffine).Equation x₁ y₁ →
      ((threeRootsCurve e₁ e₂ e₃).toAffine).Equation x₂ y₂ →
      y₁ ≠ 0 → y₂ ≠ 0 →
      ¬(x₁ = x₂ ∧ y₁ = ((threeRootsCurve e₁ e₂ e₃).toAffine).negY x₂ y₂) →
      ∀ (t₁ w₁ t₂ w₂ D C α β c₃ c₂ : F),
        t₁ = -x₁ / y₁ →
        w₁ = -1 / y₁ →
        t₂ = -x₂ / y₂ →
        w₂ = -1 / y₂ →
        D = t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2 + ((threeRootsCurve e₁ e₂ e₃).toAffine).a₂ * (t₁ + t₂) * w₁ +
              ((threeRootsCurve e₁ e₂ e₃).toAffine).a₄ * w₁ ^ 2 →
        C = ((threeRootsCurve e₁ e₂ e₃).toAffine).a₂ * t₂ ^ 2 +
              ((threeRootsCurve e₁ e₂ e₃).toAffine).a₄ * t₂ * (w₁ + w₂) +
              ((threeRootsCurve e₁ e₂ e₃).toAffine).a₆ * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2) →
        1 - C ≠ 0 →
        α = D / (1 - C) →
        β = w₁ - α * t₁ →
        c₃ = -(1 + ((threeRootsCurve e₁ e₂ e₃).toAffine).a₂ * α +
              ((threeRootsCurve e₁ e₂ e₃).toAffine).a₄ * α ^ 2 +
              ((threeRootsCurve e₁ e₂ e₃).toAffine).a₆ * α ^ 3) →
        c₂ = -β * (((threeRootsCurve e₁ e₂ e₃).toAffine).a₂ +
              2 * ((threeRootsCurve e₁ e₂ e₃).toAffine).a₄ * α +
              3 * ((threeRootsCurve e₁ e₂ e₃).toAffine).a₆ * α ^ 2) →
        β ≠ 0 ∧
        ((threeRootsCurve e₁ e₂ e₃).toAffine).addY x₁ x₂ y₁
          (((threeRootsCurve e₁ e₂ e₃).toAffine).slope x₁ x₂ y₁ y₂) = -c₃ * w₁ * w₂ / β ^ 3 ∧
        ((threeRootsCurve e₁ e₂ e₃).toAffine).addX x₁ x₂
          (((threeRootsCurve e₁ e₂ e₃).toAffine).slope x₁ x₂ y₁ y₂) =
          (c₃ * (t₁ + t₂) + c₂) * w₁ * w₂ / β ^ 3 ∧
        (c₃ ≠ 0 →
          -(((threeRootsCurve e₁ e₂ e₃).toAffine).addX x₁ x₂
              (((threeRootsCurve e₁ e₂ e₃).toAffine).slope x₁ x₂ y₁ y₂)) /
            (((threeRootsCurve e₁ e₂ e₃).toAffine).addY x₁ x₂ y₁
              (((threeRootsCurve e₁ e₂ e₃).toAffine).slope x₁ x₂ y₁ y₂)) -
            (t₁ + t₂) = c₂ / c₃) := by
    intro x₁ y₁ x₂ y₂ h₁ h₂ hy₁ hy₂ hxy t₁ w₁ t₂ w₂ D C α β c₃ c₂
      ht₁ hw₁ ht₂ hw₂ hD_def hC_def h1C_ne hα_def hβ_def hc₃_def hc₂_def
    clear h_s2 hk he₁ he₂ he₃
    have heq₁ : y₁ ^ 2 = x₁ ^ 3 + ((threeRootsCurve e₁ e₂ e₃).toAffine).a₂ * x₁ ^ 2 +
        ((threeRootsCurve e₁ e₂ e₃).toAffine).a₄ * x₁ + ((threeRootsCurve e₁ e₂ e₃).toAffine).a₆ := by
      have h := (WeierstrassCurve.Affine.equation_iff x₁ y₁).mp h₁
      dsimp [threeRootsCurve] at h ⊢
      linear_combination h
    have heq₂ : y₂ ^ 2 = x₂ ^ 3 + ((threeRootsCurve e₁ e₂ e₃).toAffine).a₂ * x₂ ^ 2 +
        ((threeRootsCurve e₁ e₂ e₃).toAffine).a₄ * x₂ + ((threeRootsCurve e₁ e₂ e₃).toAffine).a₆ := by
      have h := (WeierstrassCurve.Affine.equation_iff x₂ y₂).mp h₂
      dsimp [threeRootsCurve] at h ⊢
      linear_combination h
    have hw₁_ne : w₁ ≠ 0 := by rw [hw₁]; exact div_ne_zero (neg_ne_zero.mpr one_ne_zero) hy₁
    have hw₂_ne : w₂ ≠ 0 := by rw [hw₂]; exact div_ne_zero (neg_ne_zero.mpr one_ne_zero) hy₂
    have hx₁_tw : x₁ = t₁ / w₁ := by rw [ht₁, hw₁]; field_simp
    have hy₁_tw : y₁ = -1 / w₁ := by rw [hw₁]; field_simp
    have hx₂_tw : x₂ = t₂ / w₂ := by rw [ht₂, hw₂]; field_simp
    have hy₂_tw : y₂ = -1 / w₂ := by rw [hw₂]; field_simp
    have hE₁ : w₁ - (t₁ ^ 3 + ((threeRootsCurve e₁ e₂ e₃).toAffine).a₂ * t₁ ^ 2 * w₁ +
        ((threeRootsCurve e₁ e₂ e₃).toAffine).a₄ * t₁ * w₁ ^ 2 +
        ((threeRootsCurve e₁ e₂ e₃).toAffine).a₆ * w₁ ^ 3) = 0 := by
      have h_mul : y₁ ^ 3 * (w₁ - (t₁ ^ 3 + ((threeRootsCurve e₁ e₂ e₃).toAffine).a₂ * t₁ ^ 2 * w₁ +
          ((threeRootsCurve e₁ e₂ e₃).toAffine).a₄ * t₁ * w₁ ^ 2 +
          ((threeRootsCurve e₁ e₂ e₃).toAffine).a₆ * w₁ ^ 3)) = 0 := by
        rw [ht₁, hw₁]
        field_simp
        linear_combination -heq₁
      exact (mul_eq_zero.mp h_mul).resolve_left (pow_ne_zero 3 hy₁)
    have hE₂ : w₂ - (t₂ ^ 3 + ((threeRootsCurve e₁ e₂ e₃).toAffine).a₂ * t₂ ^ 2 * w₂ +
        ((threeRootsCurve e₁ e₂ e₃).toAffine).a₄ * t₂ * w₂ ^ 2 +
        ((threeRootsCurve e₁ e₂ e₃).toAffine).a₆ * w₂ ^ 3) = 0 := by
      have h_mul : y₂ ^ 3 * (w₂ - (t₂ ^ 3 + ((threeRootsCurve e₁ e₂ e₃).toAffine).a₂ * t₂ ^ 2 * w₂ +
          ((threeRootsCurve e₁ e₂ e₃).toAffine).a₄ * t₂ * w₂ ^ 2 +
          ((threeRootsCurve e₁ e₂ e₃).toAffine).a₆ * w₂ ^ 3)) = 0 := by
        rw [ht₂, hw₂]
        field_simp
        linear_combination -heq₂
      exact (mul_eq_zero.mp h_mul).resolve_left (pow_ne_zero 3 hy₂)
    have hD : α * (1 - C) - D = 0 := by
      rw [hα_def]
      exact sub_eq_zero.mpr (div_mul_cancel₀ D h1C_ne)
    have h_sec : (1 - C) * (w₁ - w₂ - α * (t₁ - t₂)) = 0 := by
      have hD' := hD
      rw [hC_def, hD_def] at hD'
      rw [hC_def]
      linear_combination hE₁ - hE₂ - (t₁ - t₂) * hD'
    have hw₁_sub_w₂ : w₁ - w₂ = α * (t₁ - t₂) :=
      sub_eq_zero.mp ((mul_eq_zero.mp h_sec).resolve_left h1C_ne)
    have hw₂_eq : w₂ = α * t₂ + β := by
      rw [hβ_def]
      linear_combination -hw₁_sub_w₂
    have hY_num : β ^ 2 * w₁ * w₂ -
        α * ((α ^ 2 - ((threeRootsCurve e₁ e₂ e₃).toAffine).a₂ * β ^ 2) * w₁ * w₂ -
          β ^ 2 * (t₁ * w₂ + t₂ * w₁)) = -c₃ * w₁ ^ 2 * w₂ ^ 2 := by
      have hD' := hD
      rw [hC_def, hD_def, hw₂_eq, hβ_def] at hD'
      rw [hc₃_def, hw₂_eq, hβ_def]
      linear_combination -α ^ 3 * (w₁ + (α * t₂ + (w₁ - α * t₁))) * hE₁ + α ^ 2 * w₁ ^ 2 * hD'
    have hX_num : β * ((α ^ 2 - ((threeRootsCurve e₁ e₂ e₃).toAffine).a₂ * β ^ 2) * w₁ * w₂ -
        β ^ 2 * (t₁ * w₂ + t₂ * w₁)) = (c₃ * (t₁ + t₂) + c₂) * w₁ ^ 2 * w₂ ^ 2 := by
      have hD' := hD
      rw [hC_def, hD_def, hw₂_eq, hβ_def] at hD'
      rw [hc₃_def, hc₂_def, hw₂_eq, hβ_def]
      linear_combination
        α ^ 2 * (w₁ * (α * t₂ + (w₁ - α * t₁)) + (w₁ - α * t₁) * (w₁ + (α * t₂ + (w₁ - α * t₁)))) * hE₁ -
        α * w₁ ^ 2 * ((α * t₂ + (w₁ - α * t₁)) + (w₁ - α * t₁)) * hD'
    have h_β_and_slope : β ≠ 0 ∧ ((threeRootsCurve e₁ e₂ e₃).toAffine).slope x₁ x₂ y₁ y₂ = α / β := by
      by_cases hx : x₁ = x₂
      · have hy_ne_neg : y₁ ≠ ((threeRootsCurve e₁ e₂ e₃).toAffine).negY x₂ y₂ := fun hy => hxy ⟨hx, hy⟩
        have hnegY : ((threeRootsCurve e₁ e₂ e₃).toAffine).negY x₂ y₂ = -y₂ := by
          dsimp [threeRootsCurve, WeierstrassCurve.Affine.negY]; ring
        have hy_sum_ne : y₁ + y₂ ≠ 0 := by
          intro hsum
          apply hy_ne_neg
          rw [hnegY]
          linear_combination hsum
        have hy_eq : y₁ = y₂ := by
          have h_diff : (y₁ - y₂) * (y₁ + y₂) = 0 := by
            rw [hx] at heq₁
            linear_combination heq₁ - heq₂
          exact sub_eq_zero.mp ((mul_eq_zero.mp h_diff).resolve_right hy_sum_ne)
        have ht_eq : t₂ = t₁ := by rw [ht₁, ht₂, hx, hy_eq]
        have hw_eq : w₂ = w₁ := by rw [hw₁, hw₂, hy_eq]
        have hCβ : (1 - C) * β = -2 * w₁ := by
          have hD' := hD
          rw [hC_def, hD_def, ht_eq, hw_eq] at hD'
          rw [hC_def, hβ_def, ht_eq, hw_eq]
          linear_combination 3 * hE₁ - t₁ * hD'
        have h2w₁_ne : -2 * w₁ ≠ 0 :=
          mul_ne_zero (neg_ne_zero.mpr two_ne_zero) hw₁_ne
        have hβ_ne : β ≠ 0 := by
          intro hβ0
          apply h2w₁_ne
          rw [← hCβ, hβ0, mul_zero]
        refine ⟨hβ_ne, ?_⟩
        rw [WeierstrassCurve.Affine.slope_of_Y_ne hx hy_ne_neg]
        have ha₁ : ((threeRootsCurve e₁ e₂ e₃).toAffine).a₁ = 0 := rfl
        rw [ha₁]
        have hD_tan : D = 3 * t₁ ^ 2 + 2 * ((threeRootsCurve e₁ e₂ e₃).toAffine).a₂ * t₁ * w₁ +
            ((threeRootsCurve e₁ e₂ e₃).toAffine).a₄ * w₁ ^ 2 := by
          rw [hD_def, ht_eq]
          ring
        have h_num_eq : 3 * x₁ ^ 2 + 2 * ((threeRootsCurve e₁ e₂ e₃).toAffine).a₂ * x₁ +
            ((threeRootsCurve e₁ e₂ e₃).toAffine).a₄ - 0 * y₁ = D / w₁ ^ 2 := by
          rw [hx₁_tw, hD_tan]
          field_simp
          ring
        have h_den_eq : y₁ - ((threeRootsCurve e₁ e₂ e₃).toAffine).negY x₁ y₁ = -2 / w₁ := by
          have hnegY₁ : ((threeRootsCurve e₁ e₂ e₃).toAffine).negY x₁ y₁ = -y₁ := by
            dsimp [threeRootsCurve, WeierstrassCurve.Affine.negY]; ring
          rw [hnegY₁, hy₁_tw]
          field_simp
          ring
        rw [h_num_eq, h_den_eq]
        have hD_eq : D = α * (1 - C) := (sub_eq_zero.mp hD).symm
        have h2w₁_eq : -2 * w₁ = (1 - C) * β := hCβ.symm
        calc (D / w₁ ^ 2) / (-2 / w₁)
            = D / (-2 * w₁) := by field_simp
          _ = (α * (1 - C)) / ((1 - C) * β) := by rw [hD_eq, h2w₁_eq]
          _ = α / β := by field_simp
      · have h_cross : t₁ * w₂ - t₂ * w₁ = (t₁ - t₂) * β := by
          rw [hβ_def]
          linear_combination -t₁ * hw₁_sub_w₂
        have h_cross_ne : t₁ * w₂ - t₂ * w₁ ≠ 0 := by
          intro h0
          apply hx
          rw [hx₁_tw, hx₂_tw, div_eq_div_iff hw₁_ne hw₂_ne]
          exact sub_eq_zero.mp h0
        have ht_sub_ne : t₁ - t₂ ≠ 0 := by
          intro ht0
          apply h_cross_ne
          rw [h_cross, ht0, zero_mul]
        have hβ_ne : β ≠ 0 := by
          intro hβ0
          apply h_cross_ne
          rw [h_cross, hβ0, mul_zero]
        refine ⟨hβ_ne, ?_⟩
        rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
        calc (y₁ - y₂) / (x₁ - x₂)
            = ((-1 / w₁) - (-1 / w₂)) / ((t₁ / w₁) - (t₂ / w₂)) := by
                rw [hx₁_tw, hy₁_tw, hx₂_tw, hy₂_tw]
          _ = (w₁ - w₂) / (t₁ * w₂ - t₂ * w₁) := by field_simp; ring
          _ = (α * (t₁ - t₂)) / ((t₁ - t₂) * β) := by rw [hw₁_sub_w₂, h_cross]
          _ = α / β := by field_simp
    obtain ⟨hβ_ne, h_slope⟩ := h_β_and_slope
    have hy₃_eq : ((threeRootsCurve e₁ e₂ e₃).toAffine).addY x₁ x₂ y₁
        (((threeRootsCurve e₁ e₂ e₃).toAffine).slope x₁ x₂ y₁ y₂) = -c₃ * w₁ * w₂ / β ^ 3 := by
      rw [h_slope]
      dsimp [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addX]
      have ha₁ : ((threeRootsCurve e₁ e₂ e₃).toAffine).a₁ = 0 := rfl
      have ha₃ : ((threeRootsCurve e₁ e₂ e₃).toAffine).a₃ = 0 := rfl
      rw [ha₁, ha₃, hx₁_tw, hx₂_tw, hy₁_tw]
      have hβ_t₁ : β + α * t₁ = w₁ := by rw [hβ_def]; ring
      calc -(α / β * ((α / β) ^ 2 + 0 * (α / β) - ((threeRootsCurve e₁ e₂ e₃).toAffine).a₂ -
                t₁ / w₁ - t₂ / w₂ - t₁ / w₁) + -1 / w₁) -
            0 * ((α / β) ^ 2 + 0 * (α / β) - ((threeRootsCurve e₁ e₂ e₃).toAffine).a₂ - t₁ / w₁ - t₂ / w₂) - 0
          = (β ^ 2 * (β + α * t₁) * w₂ -
              α * ((α ^ 2 - ((threeRootsCurve e₁ e₂ e₃).toAffine).a₂ * β ^ 2) * w₁ * w₂ -
                β ^ 2 * (t₁ * w₂ + t₂ * w₁))) /
              (β ^ 3 * w₁ * w₂) := by
            field_simp
            ring
        _ = (-c₃ * w₁ ^ 2 * w₂ ^ 2) / (β ^ 3 * w₁ * w₂) := by rw [hβ_t₁, hY_num]
        _ = -c₃ * w₁ * w₂ / β ^ 3 := by field_simp
    have hx₃_eq : ((threeRootsCurve e₁ e₂ e₃).toAffine).addX x₁ x₂
        (((threeRootsCurve e₁ e₂ e₃).toAffine).slope x₁ x₂ y₁ y₂) =
        (c₃ * (t₁ + t₂) + c₂) * w₁ * w₂ / β ^ 3 := by
      rw [h_slope]
      dsimp [WeierstrassCurve.Affine.addX]
      have ha₁ : ((threeRootsCurve e₁ e₂ e₃).toAffine).a₁ = 0 := rfl
      rw [ha₁, hx₁_tw, hx₂_tw]
      calc (α / β) ^ 2 + 0 * (α / β) - ((threeRootsCurve e₁ e₂ e₃).toAffine).a₂ - t₁ / w₁ - t₂ / w₂
          = (β * ((α ^ 2 - ((threeRootsCurve e₁ e₂ e₃).toAffine).a₂ * β ^ 2) * w₁ * w₂ -
              β ^ 2 * (t₁ * w₂ + t₂ * w₁))) /
              (β ^ 3 * w₁ * w₂) := by
            field_simp
            ring
        _ = ((c₃ * (t₁ + t₂) + c₂) * w₁ ^ 2 * w₂ ^ 2) / (β ^ 3 * w₁ * w₂) := by rw [hX_num]
        _ = (c₃ * (t₁ + t₂) + c₂) * w₁ * w₂ / β ^ 3 := by field_simp
    refine ⟨hβ_ne, hy₃_eq, hx₃_eq, ?_⟩
    intro hc₃_ne
    rw [hx₃_eq, hy₃_eq]
    field_simp
    ring
  have h_s4 : ∀ (t₁ w₁ t₂ w₂ : F),
      w₁ ≠ 0 → w₂ ≠ 0 →
      Valued.v t₁ ≤ WithZero.exp (-k) →
      Valued.v t₂ ≤ WithZero.exp (-k) →
      Valued.v w₁ = Valued.v t₁ ^ 3 →
      Valued.v w₂ = Valued.v t₂ ^ 3 →
      w₁ - (t₁ ^ 3 + ((threeRootsCurve e₁ e₂ e₃).toAffine).a₂ * t₁ ^ 2 * w₁ +
        ((threeRootsCurve e₁ e₂ e₃).toAffine).a₄ * t₁ * w₁ ^ 2 +
        ((threeRootsCurve e₁ e₂ e₃).toAffine).a₆ * w₁ ^ 3) = 0 →
      let W := (threeRootsCurve e₁ e₂ e₃).toAffine
      let D : F := t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2 + W.a₂ * (t₁ + t₂) * w₁ + W.a₄ * w₁ ^ 2
      let C : F := W.a₂ * t₂ ^ 2 + W.a₄ * t₂ * (w₁ + w₂) + W.a₆ * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2)
      let α : F := D / (1 - C)
      let β : F := w₁ - α * t₁
      let c₃ : F := -(1 + W.a₂ * α + W.a₄ * α ^ 2 + W.a₆ * α ^ 3)
      let c₂ : F := -β * (W.a₂ + 2 * W.a₄ * α + 3 * W.a₆ * α ^ 2)
      1 - C ≠ 0 ∧ c₃ ≠ 0 ∧
      (β ≠ 0 → WithZero.exp (3 * k) ≤ Valued.v (-c₃ * w₁ * w₂ / β ^ 3)) ∧
      Valued.v (c₂ / c₃) ≤ WithZero.exp (-2 * k) := by
    intro t₁ w₁ t₂ w₂ hw₁_ne hw₂_ne ht₁ ht₂ hw₁ hw₂ hE₁ W D C α β c₃ c₂
    clear h_s2 h_s3
    have h_add3 : ∀ {a b c : F} {m : WithZero (Multiplicative ℤ)},
        Valued.v a ≤ m → Valued.v b ≤ m → Valued.v c ≤ m → Valued.v (a + b + c) ≤ m :=
      fun ha hb hc => le_trans (Valuation.map_add Valued.v _ _)
        (max_le (le_trans (Valuation.map_add Valued.v _ _) (max_le ha hb)) hc)
    have h_add4 : ∀ {a b c d : F} {m : WithZero (Multiplicative ℤ)},
        Valued.v a ≤ m → Valued.v b ≤ m → Valued.v c ≤ m → Valued.v d ≤ m →
        Valued.v (a + b + c + d) ≤ m :=
      fun ha hb hc hd => le_trans (Valuation.map_add Valued.v _ _)
        (max_le (h_add3 ha hb hc) hd)
    have h_add5 : ∀ {a b c d e : F} {m : WithZero (Multiplicative ℤ)},
        Valued.v a ≤ m → Valued.v b ≤ m → Valued.v c ≤ m → Valued.v d ≤ m → Valued.v e ≤ m →
        Valued.v (a + b + c + d + e) ≤ m :=
      fun ha hb hc hd he => le_trans (Valuation.map_add Valued.v _ _)
        (max_le (h_add4 ha hb hc hd) he)
    have ha₂ : Valued.v W.a₂ ≤ WithZero.exp (B : ℤ) := by
      change Valued.v (-(e₁ + e₂ + e₃)) ≤ WithZero.exp (B : ℤ)
      rw [Valuation.map_neg]
      exact h_add3 he₁ he₂ he₃
    have ha₄ : Valued.v W.a₄ ≤ WithZero.exp (2 * (B : ℤ)) := by
      change Valued.v (e₁ * e₂ + e₁ * e₃ + e₂ * e₃) ≤ WithZero.exp (2 * (B : ℤ))
      have hBB : WithZero.exp (B : ℤ) * WithZero.exp (B : ℤ) = WithZero.exp (2 * (B : ℤ)) := by
        rw [← WithZero.exp_add]; congr 1; omega
      refine h_add3 ?_ ?_ ?_
      · rw [Valuation.map_mul, ← hBB]; exact mul_le_mul' he₁ he₂
      · rw [Valuation.map_mul, ← hBB]; exact mul_le_mul' he₁ he₃
      · rw [Valuation.map_mul, ← hBB]; exact mul_le_mul' he₂ he₃
    have ha₆ : Valued.v W.a₆ ≤ WithZero.exp (3 * (B : ℤ)) := by
      change Valued.v (-(e₁ * e₂ * e₃)) ≤ WithZero.exp (3 * (B : ℤ))
      rw [Valuation.map_neg, Valuation.map_mul, Valuation.map_mul]
      calc Valued.v e₁ * Valued.v e₂ * Valued.v e₃
          ≤ WithZero.exp (B : ℤ) * WithZero.exp (B : ℤ) * WithZero.exp (B : ℤ) :=
            mul_le_mul' (mul_le_mul' he₁ he₂) he₃
        _ = WithZero.exp ((B : ℤ) + (B : ℤ) + (B : ℤ)) := by
            rw [← WithZero.exp_add, ← WithZero.exp_add]
        _ = WithZero.exp (3 * (B : ℤ)) := by congr 1; omega
    have hv2_le : Valued.v (2 : F) ≤ 1 := by
      have h2 : (2 : F) = 1 + 1 := one_add_one_eq_two.symm
      rw [h2]
      exact le_trans (Valuation.map_add Valued.v 1 1) (max_le (by simp) (by simp))
    have hv3_le : Valued.v (3 : F) ≤ 1 := by
      have h3 : (3 : F) = 2 + 1 := by norm_num
      rw [h3]
      exact le_trans (Valuation.map_add Valued.v 2 1) (max_le hv2_le (by simp))
    have hw₁_le : Valued.v w₁ ≤ WithZero.exp (-3 * k) := by
      calc Valued.v w₁ = Valued.v t₁ ^ 3 := hw₁
        _ = Valued.v t₁ * Valued.v t₁ * Valued.v t₁ := pow_three' _
        _ ≤ WithZero.exp (-k) * WithZero.exp (-k) * WithZero.exp (-k) :=
            mul_le_mul' (mul_le_mul' ht₁ ht₁) ht₁
        _ = WithZero.exp (-k + -k + -k) := by rw [← WithZero.exp_add, ← WithZero.exp_add]
        _ = WithZero.exp (-3 * k) := by congr 1; omega
    have hw₂_le : Valued.v w₂ ≤ WithZero.exp (-3 * k) := by
      calc Valued.v w₂ = Valued.v t₂ ^ 3 := hw₂
        _ = Valued.v t₂ * Valued.v t₂ * Valued.v t₂ := pow_three' _
        _ ≤ WithZero.exp (-k) * WithZero.exp (-k) * WithZero.exp (-k) :=
            mul_le_mul' (mul_le_mul' ht₂ ht₂) ht₂
        _ = WithZero.exp (-k + -k + -k) := by rw [← WithZero.exp_add, ← WithZero.exp_add]
        _ = WithZero.exp (-3 * k) := by congr 1; omega
    have ht_sum : Valued.v (t₁ + t₂) ≤ WithZero.exp (-k) :=
      le_trans (Valuation.map_add Valued.v t₁ t₂) (max_le ht₁ ht₂)
    have hw_sum : Valued.v (w₁ + w₂) ≤ WithZero.exp (-3 * k) :=
      le_trans (Valuation.map_add Valued.v w₁ w₂) (max_le hw₁_le hw₂_le)
    have hw_quad : Valued.v (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2) ≤ WithZero.exp (-6 * k) := by
      have h6 : WithZero.exp (-3 * k) * WithZero.exp (-3 * k) = WithZero.exp (-6 * k) := by
        rw [← WithZero.exp_add]; congr 1; omega
      refine h_add3 ?_ ?_ ?_
      · rw [Valuation.map_pow, sq, ← h6]; exact mul_le_mul' hw₁_le hw₁_le
      · rw [Valuation.map_mul, ← h6]; exact mul_le_mul' hw₁_le hw₂_le
      · rw [Valuation.map_pow, sq, ← h6]; exact mul_le_mul' hw₂_le hw₂_le
    have hC_le : Valued.v C ≤ WithZero.exp (-1 : ℤ) := by
      refine h_add3 ?_ ?_ ?_
      · rw [Valuation.map_mul, Valuation.map_pow, sq]
        calc Valued.v W.a₂ * (Valued.v t₂ * Valued.v t₂)
            ≤ WithZero.exp (B : ℤ) * (WithZero.exp (-k) * WithZero.exp (-k)) :=
              mul_le_mul' ha₂ (mul_le_mul' ht₂ ht₂)
          _ = WithZero.exp ((B : ℤ) + (-k + -k)) := by
              rw [← WithZero.exp_add, ← WithZero.exp_add]
          _ ≤ WithZero.exp (-1 : ℤ) := WithZero.exp_le_exp.mpr (by omega)
      · rw [Valuation.map_mul, Valuation.map_mul]
        calc Valued.v W.a₄ * Valued.v t₂ * Valued.v (w₁ + w₂)
            ≤ WithZero.exp (2 * (B : ℤ)) * WithZero.exp (-k) * WithZero.exp (-3 * k) :=
              mul_le_mul' (mul_le_mul' ha₄ ht₂) hw_sum
          _ = WithZero.exp (2 * (B : ℤ) + -k + -3 * k) := by
              rw [← WithZero.exp_add, ← WithZero.exp_add]
          _ ≤ WithZero.exp (-1 : ℤ) := WithZero.exp_le_exp.mpr (by omega)
      · rw [Valuation.map_mul]
        calc Valued.v W.a₆ * Valued.v (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2)
            ≤ WithZero.exp (3 * (B : ℤ)) * WithZero.exp (-6 * k) :=
              mul_le_mul' ha₆ hw_quad
          _ = WithZero.exp (3 * (B : ℤ) + -6 * k) := by rw [← WithZero.exp_add]
          _ ≤ WithZero.exp (-1 : ℤ) := WithZero.exp_le_exp.mpr (by omega)
    have hC_lt_one : Valued.v C < Valued.v (1 : F) := by
      rw [Valuation.map_one, ← WithZero.exp_zero]
      exact lt_of_le_of_lt hC_le (WithZero.exp_lt_exp.mpr (by omega))
    have hv1C : Valued.v (1 - C) = 1 := by
      rw [Valuation.map_sub_eq_of_lt_left Valued.v hC_lt_one, Valuation.map_one]
    have h1C_ne : 1 - C ≠ 0 := by
      refine (Valuation.ne_zero_iff Valued.v).mp ?_
      rw [hv1C]
      exact one_ne_zero
    have hD_le : Valued.v D ≤ WithZero.exp (-2 * k) := by
      have h2k : WithZero.exp (-k) * WithZero.exp (-k) = WithZero.exp (-2 * k) := by
        rw [← WithZero.exp_add]; congr 1; omega
      refine h_add5 ?_ ?_ ?_ ?_ ?_
      · rw [Valuation.map_pow, sq, ← h2k]; exact mul_le_mul' ht₁ ht₁
      · rw [Valuation.map_mul, ← h2k]; exact mul_le_mul' ht₁ ht₂
      · rw [Valuation.map_pow, sq, ← h2k]; exact mul_le_mul' ht₂ ht₂
      · rw [Valuation.map_mul, Valuation.map_mul]
        calc Valued.v W.a₂ * Valued.v (t₁ + t₂) * Valued.v w₁
            ≤ WithZero.exp (B : ℤ) * WithZero.exp (-k) * WithZero.exp (-3 * k) :=
              mul_le_mul' (mul_le_mul' ha₂ ht_sum) hw₁_le
          _ = WithZero.exp ((B : ℤ) + -k + -3 * k) := by
              rw [← WithZero.exp_add, ← WithZero.exp_add]
          _ ≤ WithZero.exp (-2 * k) := WithZero.exp_le_exp.mpr (by omega)
      · rw [Valuation.map_mul, Valuation.map_pow, sq]
        calc Valued.v W.a₄ * (Valued.v w₁ * Valued.v w₁)
            ≤ WithZero.exp (2 * (B : ℤ)) * (WithZero.exp (-3 * k) * WithZero.exp (-3 * k)) :=
              mul_le_mul' ha₄ (mul_le_mul' hw₁_le hw₁_le)
          _ = WithZero.exp (2 * (B : ℤ) + (-3 * k + -3 * k)) := by
              rw [← WithZero.exp_add, ← WithZero.exp_add]
          _ ≤ WithZero.exp (-2 * k) := WithZero.exp_le_exp.mpr (by omega)
    have hα_le : Valued.v α ≤ WithZero.exp (-2 * k) := by
      change Valued.v (D / (1 - C)) ≤ WithZero.exp (-2 * k)
      rw [Valuation.map_div, hv1C, div_one]
      exact hD_le
    have hc₃_tail : Valued.v (W.a₂ * α + W.a₄ * α ^ 2 + W.a₆ * α ^ 3) ≤ WithZero.exp (-1 : ℤ) := by
      refine h_add3 ?_ ?_ ?_
      · rw [Valuation.map_mul]
        calc Valued.v W.a₂ * Valued.v α
            ≤ WithZero.exp (B : ℤ) * WithZero.exp (-2 * k) := mul_le_mul' ha₂ hα_le
          _ = WithZero.exp ((B : ℤ) + -2 * k) := by rw [← WithZero.exp_add]
          _ ≤ WithZero.exp (-1 : ℤ) := WithZero.exp_le_exp.mpr (by omega)
      · rw [Valuation.map_mul, Valuation.map_pow, sq]
        calc Valued.v W.a₄ * (Valued.v α * Valued.v α)
            ≤ WithZero.exp (2 * (B : ℤ)) * (WithZero.exp (-2 * k) * WithZero.exp (-2 * k)) :=
              mul_le_mul' ha₄ (mul_le_mul' hα_le hα_le)
          _ = WithZero.exp (2 * (B : ℤ) + (-2 * k + -2 * k)) := by
              rw [← WithZero.exp_add, ← WithZero.exp_add]
          _ ≤ WithZero.exp (-1 : ℤ) := WithZero.exp_le_exp.mpr (by omega)
      · rw [Valuation.map_mul, Valuation.map_pow, pow_three']
        calc Valued.v W.a₆ * (Valued.v α * Valued.v α * Valued.v α)
            ≤ WithZero.exp (3 * (B : ℤ)) *
                (WithZero.exp (-2 * k) * WithZero.exp (-2 * k) * WithZero.exp (-2 * k)) :=
              mul_le_mul' ha₆ (mul_le_mul' (mul_le_mul' hα_le hα_le) hα_le)
          _ = WithZero.exp (3 * (B : ℤ) + (-2 * k + -2 * k + -2 * k)) := by
              rw [← WithZero.exp_add, ← WithZero.exp_add, ← WithZero.exp_add]
          _ ≤ WithZero.exp (-1 : ℤ) := WithZero.exp_le_exp.mpr (by omega)
    have hvc₃ : Valued.v c₃ = 1 := by
      have hc₃_eq : c₃ = -(1 + (W.a₂ * α + W.a₄ * α ^ 2 + W.a₆ * α ^ 3)) := by
        dsimp [c₃]; ring
      have h_lt : Valued.v (W.a₂ * α + W.a₄ * α ^ 2 + W.a₆ * α ^ 3) < Valued.v (1 : F) := by
        rw [Valuation.map_one, ← WithZero.exp_zero]
        exact lt_of_le_of_lt hc₃_tail (WithZero.exp_lt_exp.mpr (by omega))
      rw [hc₃_eq, Valuation.map_neg, Valuation.map_add_eq_of_lt_left Valued.v h_lt, Valuation.map_one]
    have hc₃_ne : c₃ ≠ 0 := by
      refine (Valuation.ne_zero_iff Valued.v).mp ?_
      rw [hvc₃]
      exact one_ne_zero
    have hD : α * (1 - C) - D = 0 := by
      dsimp [α]
      exact sub_eq_zero.mpr (div_mul_cancel₀ D h1C_ne)
    have hCβ_id : (1 - C) * β =
        -(t₁ * t₂ * (t₁ + t₂) + W.a₂ * t₂ * (t₁ + t₂) * w₁ +
          W.a₄ * t₂ * w₁ * (w₁ + w₂) + W.a₆ * w₁ * w₂ * (w₁ + w₂)) := by
      dsimp [C, D, β] at hD ⊢
      linear_combination hE₁ - t₁ * hD
    have hβ_prod_le : Valued.v β ≤ Valued.v t₁ * Valued.v t₂ * WithZero.exp (-k) := by
      have hvβ_eq : Valued.v β = Valued.v ((1 - C) * β) := by
        rw [Valuation.map_mul, hv1C, one_mul]
      rw [hvβ_eq, hCβ_id, Valuation.map_neg]
      have hvw₁_3 : Valued.v w₁ = Valued.v t₁ * Valued.v t₁ * Valued.v t₁ := by
        rw [hw₁, pow_three']
      have hvw₂_3 : Valued.v w₂ = Valued.v t₂ * Valued.v t₂ * Valued.v t₂ := by
        rw [hw₂, pow_three']
      refine h_add4 ?_ ?_ ?_ ?_
      · rw [Valuation.map_mul, Valuation.map_mul]
        exact mul_le_mul' (le_refl _) ht_sum
      · rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_mul, hvw₁_3]
        calc Valued.v W.a₂ * Valued.v t₂ * Valued.v (t₁ + t₂) * (Valued.v t₁ * Valued.v t₁ * Valued.v t₁)
            = Valued.v t₁ * Valued.v t₂ *
                (Valued.v W.a₂ * Valued.v (t₁ + t₂) * Valued.v t₁ * Valued.v t₁) := by ac_rfl
          _ ≤ Valued.v t₁ * Valued.v t₂ *
                (WithZero.exp (B : ℤ) * WithZero.exp (-k) * WithZero.exp (-k) * WithZero.exp (-k)) :=
              mul_le_mul' (le_refl _) (mul_le_mul' (mul_le_mul' (mul_le_mul' ha₂ ht_sum) ht₁) ht₁)
          _ = Valued.v t₁ * Valued.v t₂ * WithZero.exp ((B : ℤ) + -k + -k + -k) := by
              rw [← WithZero.exp_add, ← WithZero.exp_add, ← WithZero.exp_add]
          _ ≤ Valued.v t₁ * Valued.v t₂ * WithZero.exp (-k) :=
              mul_le_mul' (le_refl _) (WithZero.exp_le_exp.mpr (by omega))
      · rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_mul, hvw₁_3]
        calc Valued.v W.a₄ * Valued.v t₂ * (Valued.v t₁ * Valued.v t₁ * Valued.v t₁) * Valued.v (w₁ + w₂)
            = Valued.v t₁ * Valued.v t₂ *
                (Valued.v W.a₄ * Valued.v t₁ * Valued.v t₁ * Valued.v (w₁ + w₂)) := by ac_rfl
          _ ≤ Valued.v t₁ * Valued.v t₂ *
                (WithZero.exp (2 * (B : ℤ)) * WithZero.exp (-k) * WithZero.exp (-k) * WithZero.exp (-3 * k)) :=
              mul_le_mul' (le_refl _) (mul_le_mul' (mul_le_mul' (mul_le_mul' ha₄ ht₁) ht₁) hw_sum)
          _ = Valued.v t₁ * Valued.v t₂ * WithZero.exp (2 * (B : ℤ) + -k + -k + -3 * k) := by
              rw [← WithZero.exp_add, ← WithZero.exp_add, ← WithZero.exp_add]
          _ ≤ Valued.v t₁ * Valued.v t₂ * WithZero.exp (-k) :=
              mul_le_mul' (le_refl _) (WithZero.exp_le_exp.mpr (by omega))
      · rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_mul, hvw₁_3, hvw₂_3]
        calc Valued.v W.a₆ * (Valued.v t₁ * Valued.v t₁ * Valued.v t₁) *
              (Valued.v t₂ * Valued.v t₂ * Valued.v t₂) * Valued.v (w₁ + w₂)
            = Valued.v t₁ * Valued.v t₂ *
                (Valued.v W.a₆ * Valued.v t₁ * Valued.v t₁ * Valued.v t₂ * Valued.v t₂ * Valued.v (w₁ + w₂)) := by ac_rfl
          _ ≤ Valued.v t₁ * Valued.v t₂ *
                (WithZero.exp (3 * (B : ℤ)) * WithZero.exp (-k) * WithZero.exp (-k) *
                  WithZero.exp (-k) * WithZero.exp (-k) * WithZero.exp (-3 * k)) :=
              mul_le_mul' (le_refl _)
                (mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul' ha₆ ht₁) ht₁) ht₂) ht₂) hw_sum)
          _ = Valued.v t₁ * Valued.v t₂ * WithZero.exp (3 * (B : ℤ) + -k + -k + -k + -k + -3 * k) := by
              rw [← WithZero.exp_add, ← WithZero.exp_add, ← WithZero.exp_add, ← WithZero.exp_add, ← WithZero.exp_add]
          _ ≤ Valued.v t₁ * Valued.v t₂ * WithZero.exp (-k) :=
              mul_le_mul' (le_refl _) (WithZero.exp_le_exp.mpr (by omega))
    have hβ_le : Valued.v β ≤ WithZero.exp (-3 * k) := by
      calc Valued.v β ≤ Valued.v t₁ * Valued.v t₂ * WithZero.exp (-k) := hβ_prod_le
        _ ≤ WithZero.exp (-k) * WithZero.exp (-k) * WithZero.exp (-k) :=
            mul_le_mul' (mul_le_mul' ht₁ ht₂) (le_refl _)
        _ = WithZero.exp (-k + -k + -k) := by rw [← WithZero.exp_add, ← WithZero.exp_add]
        _ = WithZero.exp (-3 * k) := by congr 1; omega
    have hβ3_le : Valued.v β ^ 3 ≤ Valued.v w₁ * Valued.v w₂ * WithZero.exp (-3 * k) := by
      have hvw₁_3 : Valued.v w₁ = Valued.v t₁ * Valued.v t₁ * Valued.v t₁ := by
        rw [hw₁, pow_three']
      have hvw₂_3 : Valued.v w₂ = Valued.v t₂ * Valued.v t₂ * Valued.v t₂ := by
        rw [hw₂, pow_three']
      have hexp3 : WithZero.exp (-k) * WithZero.exp (-k) * WithZero.exp (-k) = WithZero.exp (-3 * k) := by
        rw [← WithZero.exp_add, ← WithZero.exp_add]; congr 1; omega
      calc Valued.v β ^ 3 = Valued.v β * Valued.v β * Valued.v β := pow_three' _
        _ ≤ (Valued.v t₁ * Valued.v t₂ * WithZero.exp (-k)) *
            (Valued.v t₁ * Valued.v t₂ * WithZero.exp (-k)) *
            (Valued.v t₁ * Valued.v t₂ * WithZero.exp (-k)) :=
            mul_le_mul' (mul_le_mul' hβ_prod_le hβ_prod_le) hβ_prod_le
        _ = (Valued.v t₁ * Valued.v t₁ * Valued.v t₁) *
            (Valued.v t₂ * Valued.v t₂ * Valued.v t₂) *
            (WithZero.exp (-k) * WithZero.exp (-k) * WithZero.exp (-k)) := by ac_rfl
        _ = Valued.v w₁ * Valued.v w₂ * WithZero.exp (-3 * k) := by
            rw [← hvw₁_3, ← hvw₂_3, hexp3]
    have hc₂_div_c₃_le : Valued.v (c₂ / c₃) ≤ WithZero.exp (-2 * k) := by
      rw [Valuation.map_div, hvc₃, div_one]
      change Valued.v (-β * (W.a₂ + 2 * W.a₄ * α + 3 * W.a₆ * α ^ 2)) ≤ WithZero.exp (-2 * k)
      rw [Valuation.map_mul, Valuation.map_neg]
      have h_factor : Valued.v (W.a₂ + 2 * W.a₄ * α + 3 * W.a₆ * α ^ 2) ≤ WithZero.exp (B : ℤ) := by
        refine h_add3 ha₂ ?_ ?_
        · rw [Valuation.map_mul, Valuation.map_mul]
          calc Valued.v (2 : F) * Valued.v W.a₄ * Valued.v α
              ≤ 1 * WithZero.exp (2 * (B : ℤ)) * WithZero.exp (-2 * k) :=
                mul_le_mul' (mul_le_mul' hv2_le ha₄) hα_le
            _ = WithZero.exp (2 * (B : ℤ) + -2 * k) := by rw [one_mul, ← WithZero.exp_add]
            _ ≤ WithZero.exp (B : ℤ) := WithZero.exp_le_exp.mpr (by omega)
        · rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, sq]
          calc Valued.v (3 : F) * Valued.v W.a₆ * (Valued.v α * Valued.v α)
              ≤ 1 * WithZero.exp (3 * (B : ℤ)) * (WithZero.exp (-2 * k) * WithZero.exp (-2 * k)) :=
                mul_le_mul' (mul_le_mul' hv3_le ha₆) (mul_le_mul' hα_le hα_le)
            _ = WithZero.exp (3 * (B : ℤ) + (-2 * k + -2 * k)) := by
                rw [one_mul, ← WithZero.exp_add, ← WithZero.exp_add]
            _ ≤ WithZero.exp (B : ℤ) := WithZero.exp_le_exp.mpr (by omega)
      calc Valued.v β * Valued.v (W.a₂ + 2 * W.a₄ * α + 3 * W.a₆ * α ^ 2)
          ≤ WithZero.exp (-3 * k) * WithZero.exp (B : ℤ) := mul_le_mul' hβ_le h_factor
        _ = WithZero.exp (-3 * k + (B : ℤ)) := by rw [← WithZero.exp_add]
        _ ≤ WithZero.exp (-2 * k) := WithZero.exp_le_exp.mpr (by omega)
    refine ⟨h1C_ne, hc₃_ne, ?_, hc₂_div_c₃_le⟩
    intro hβ_ne
    rw [Valuation.map_div, Valuation.map_mul, Valuation.map_mul,
        Valuation.map_neg, hvc₃, one_mul, Valuation.map_pow]
    have hvβ3_ne : Valued.v β ^ 3 ≠ 0 :=
      pow_ne_zero 3 ((Valuation.ne_zero_iff Valued.v).mpr hβ_ne)
    have h0 : (-3 * k + 3 * k : ℤ) = 0 := by omega
    calc WithZero.exp (3 * k)
        = Valued.v β ^ 3 * (Valued.v β ^ 3)⁻¹ * WithZero.exp (3 * k) := by
            rw [mul_inv_cancel₀ hvβ3_ne, one_mul]
      _ ≤ (Valued.v w₁ * Valued.v w₂ * WithZero.exp (-3 * k)) * (Valued.v β ^ 3)⁻¹ * WithZero.exp (3 * k) :=
          mul_le_mul' (mul_le_mul' hβ3_le (le_refl _)) (le_refl _)
      _ = Valued.v w₁ * Valued.v w₂ * (Valued.v β ^ 3)⁻¹ * (WithZero.exp (-3 * k) * WithZero.exp (3 * k)) := by
          ac_rfl
      _ = Valued.v w₁ * Valued.v w₂ / Valued.v β ^ 3 := by
          rw [← WithZero.exp_add, h0, WithZero.exp_zero, mul_one, div_eq_mul_inv]
  refine ⟨?_, h_s2.1⟩
  intro P Q hP hQ
  cases P with
  | zero =>
    change (0 : (threeRootsCurve e₁ e₂ e₃).toAffine.Point) + Q ∈ lutzSet e₁ e₂ e₃ k ∧
      lutzParam ((0 : (threeRootsCurve e₁ e₂ e₃).toAffine.Point) + Q) - (0 + lutzParam Q) ∈ valBall F (2 * k)
    rw [zero_add, zero_add, sub_self]
    exact ⟨hQ, (valBall F (2 * k)).zero_mem⟩
  | @some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      change WeierstrassCurve.Affine.Point.some h₁ + (0 : (threeRootsCurve e₁ e₂ e₃).toAffine.Point) ∈
          lutzSet e₁ e₂ e₃ k ∧
        lutzParam (WeierstrassCurve.Affine.Point.some h₁ + (0 : (threeRootsCurve e₁ e₂ e₃).toAffine.Point)) -
          (lutzParam (WeierstrassCurve.Affine.Point.some h₁) + 0) ∈ valBall F (2 * k)
      rw [add_zero, add_zero, sub_self]
      exact ⟨hP, (valBall F (2 * k)).zero_mem⟩
    | @some x₂ y₂ h₂ =>
      by_cases hxy : x₁ = x₂ ∧ y₁ = ((threeRootsCurve e₁ e₂ e₃).toAffine).negY x₂ y₂
      · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.1 hxy.2]
        refine ⟨trivial, ?_⟩
        change Valued.v (0 - (-x₁ / y₁ + -x₂ / y₂)) ≤ WithZero.exp (-(2 * k))
        have hnegY : ((threeRootsCurve e₁ e₂ e₃).toAffine).negY x₂ y₂ = -y₂ := by
          dsimp [threeRootsCurve, WeierstrassCurve.Affine.negY]; ring
        have h_zero : (0 : F) - (-x₁ / y₁ + -x₂ / y₂) = 0 := by
          rw [hxy.1, hxy.2, hnegY]
          ring
        rw [h_zero]
        exact (valBall F (2 * k)).zero_mem
      · rw [WeierstrassCurve.Affine.Point.add_some hxy]
        obtain ⟨hy₁_ne, ht₁_le, hw₁_val, hE₁⟩ := (h_s2.2 x₁ y₁ h₁.1).1 hP
        obtain ⟨hy₂_ne, ht₂_le, hw₂_val, _⟩ := (h_s2.2 x₂ y₂ h₂.1).1 hQ
        have hw₁_ne : (-1 / y₁ : F) ≠ 0 := div_ne_zero (neg_ne_zero.mpr one_ne_zero) hy₁_ne
        have hw₂_ne : (-1 / y₂ : F) ≠ 0 := div_ne_zero (neg_ne_zero.mpr one_ne_zero) hy₂_ne
        obtain ⟨h1C_ne, hc₃_ne, hy₃_bound, hc₂_c₃_le⟩ :=
          h_s4 (-x₁ / y₁) (-1 / y₁) (-x₂ / y₂) (-1 / y₂) hw₁_ne hw₂_ne ht₁_le ht₂_le hw₁_val hw₂_val hE₁
        obtain ⟨hβ_ne, hy₃_eq, hx₃_eq, h_param_diff⟩ :=
          h_s3 x₁ y₁ x₂ y₂ h₁.1 h₂.1 hy₁_ne hy₂_ne hxy
            (-x₁ / y₁) (-1 / y₁) (-x₂ / y₂) (-1 / y₂) _ _ _ _ _ _
            rfl rfl rfl rfl rfl rfl h1C_ne rfl rfl rfl rfl
        have h_ns₃ := ((threeRootsCurve e₁ e₂ e₃).toAffine).nonsingular_add h₁ h₂ hxy
        have hy₃_val : WithZero.exp (3 * k) ≤
            Valued.v (((threeRootsCurve e₁ e₂ e₃).toAffine).addY x₁ x₂ y₁
              (((threeRootsCurve e₁ e₂ e₃).toAffine).slope x₁ x₂ y₁ y₂)) := by
          rw [hy₃_eq]
          exact hy₃_bound hβ_ne
        have hx₃_val : WithZero.exp (2 * k) ≤
            Valued.v (((threeRootsCurve e₁ e₂ e₃).toAffine).addX x₁ x₂
              (((threeRootsCurve e₁ e₂ e₃).toAffine).slope x₁ x₂ y₁ y₂)) :=
          (h_s2.2 _ _ h_ns₃.1).2 hy₃_val
        refine ⟨hx₃_val, ?_⟩
        change Valued.v (-(((threeRootsCurve e₁ e₂ e₃).toAffine).addX x₁ x₂
              (((threeRootsCurve e₁ e₂ e₃).toAffine).slope x₁ x₂ y₁ y₂)) /
            (((threeRootsCurve e₁ e₂ e₃).toAffine).addY x₁ x₂ y₁
              (((threeRootsCurve e₁ e₂ e₃).toAffine).slope x₁ x₂ y₁ y₂)) -
            (-x₁ / y₁ + -x₂ / y₂)) ≤ WithZero.exp (-(2 * k))
        rw [h_param_diff hc₃_ne]
        exact le_trans hc₂_c₃_le (WithZero.exp_le_exp.mpr (by omega))

theorem lutzSet_halving_and_param_exists {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    [DecidableEq (v.adicCompletion K)]
    (e₁ e₂ e₃ : v.adicCompletion K) (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃)
    (B e : ℕ) (m : ℤ) (hm : (B : ℤ) + (e : ℤ) + 2 ≤ m)
    (he₁ : Valued.v e₁ ≤ WithZero.exp (B : ℤ))
    (he₂ : Valued.v e₂ ≤ WithZero.exp (B : ℤ))
    (he₃ : Valued.v e₃ ≤ WithZero.exp (B : ℤ))
    (he : Valued.v (2 : v.adicCompletion K) = WithZero.exp (-(e : ℤ))) :
    (∀ t ∈ valBall (v.adicCompletion K) m,
      ∃ P ∈ lutzSet e₁ e₂ e₃ m,
        lutzParam P - t ∈ valBall (v.adicCompletion K) (m + (e : ℤ))) ∧
    (∀ P ∈ lutzSet e₁ e₂ e₃ (m + (e : ℤ)),
      ∃ Q ∈ lutzSet e₁ e₂ e₃ m, Q + Q = P) :=
by
  have h_param_gen : ∀ {F : Type _} (_ : (F = K) = (F = K)) [Field F] [CharZero F]
      [Valued F (WithZero (Multiplicative ℤ))]
      (e₁ e₂ e₃ : F) (B e : ℕ) (m : ℤ) (hm : (B : ℤ) + (e : ℤ) + 2 ≤ m)
      (he₁ : Valued.v e₁ ≤ WithZero.exp (B : ℤ))
      (he₂ : Valued.v e₂ ≤ WithZero.exp (B : ℤ))
      (he₃ : Valued.v e₃ ≤ WithZero.exp (B : ℤ))
      (h_sqrt : ∀ w : F, Valued.v w ≤ WithZero.exp (-2 * (e : ℤ) - 1) →
        ∃ u : F, u ^ 2 = 1 + w ∧ Valued.v (u - 1) ≤ WithZero.exp (-(e : ℤ) - 1)),
      ∀ t ∈ valBall F m,
        ∃ P ∈ lutzSet e₁ e₂ e₃ m,
          lutzParam P - t ∈ valBall F (m + (e : ℤ)) := by
    intro F _ _ _ _ e₁ e₂ e₃ B e m hm he₁ he₂ he₃ h_sqrt t ht
    let W := (threeRootsCurve e₁ e₂ e₃).toAffine
    by_cases ht0 : t = 0
    · subst ht0
      refine ⟨0, trivial, ?_⟩
      change (0 : F) - 0 ∈ valBall F (m + (e : ℤ))
      rw [sub_self]
      exact (valBall F (m + (e : ℤ))).zero_mem
    · have ht_val : Valued.v t ≤ WithZero.exp (-m) := ht
      have ht2_val : Valued.v (t ^ 2) ≤ WithZero.exp (-2 * m) := by
        rw [sq, Valuation.map_mul]
        calc Valued.v t * Valued.v t
          _ ≤ WithZero.exp (-m) * WithZero.exp (-m) := mul_le_mul' ht_val ht_val
          _ = WithZero.exp (-m + -m) := (WithZero.exp_add (-m) (-m)).symm
          _ = WithZero.exp (-2 * m) := by congr 1; ring
      let C : WithZero (Multiplicative ℤ) := WithZero.exp (-2 * (e : ℤ) - 1)
      have hC_le_one : C ≤ 1 := by
        rw [← WithZero.exp_zero, WithZero.exp_le_exp]
        omega
      have h_et2 : ∀ {a : F}, Valued.v a ≤ WithZero.exp (B : ℤ) → Valued.v ((1 - a * t ^ 2) - 1) ≤ C := by
        intro a ha
        have h_eq : (1 - a * t ^ 2) - 1 = -(a * t ^ 2) := by ring
        rw [h_eq, Valuation.map_neg, Valuation.map_mul]
        calc Valued.v a * Valued.v (t ^ 2)
          _ ≤ WithZero.exp (B : ℤ) * WithZero.exp (-2 * m) := mul_le_mul' ha ht2_val
          _ = WithZero.exp ((B : ℤ) + -2 * m) := (WithZero.exp_add (B : ℤ) (-2 * m)).symm
          _ ≤ WithZero.exp (-2 * (e : ℤ) - 1) := by rw [WithZero.exp_le_exp]; omega
      have h_mul_one : ∀ {x y : F}, Valued.v (x - 1) ≤ C → Valued.v (y - 1) ≤ C → Valued.v (x * y - 1) ≤ C := by
        intro x y hx hy
        have hy_val : Valued.v y ≤ 1 := by
          have hy_eq : y = (y - 1) + 1 := by ring
          rw [hy_eq]
          refine le_trans (Valuation.map_add Valued.v (y - 1) 1) (max_le (le_trans hy hC_le_one) ?_)
          rw [Valuation.map_one]
        have hxy_eq : x * y - 1 = (x - 1) * y + (y - 1) := by ring
        rw [hxy_eq]
        refine le_trans (Valuation.map_add Valued.v _ _) (max_le ?_ hy)
        rw [Valuation.map_mul]
        calc Valued.v (x - 1) * Valued.v y
          _ ≤ C * 1 := mul_le_mul' hx hy_val
          _ = C := mul_one C
      let w : F := (1 - e₁ * t ^ 2) * (1 - e₂ * t ^ 2) * (1 - e₃ * t ^ 2) - 1
      have hw : Valued.v w ≤ C :=
        h_mul_one (h_mul_one (h_et2 he₁) (h_et2 he₂)) (h_et2 he₃)
      obtain ⟨u, hu_sq, hu_one⟩ := h_sqrt w hw
      have hu_sq' : u ^ 2 = (1 - e₁ * t ^ 2) * (1 - e₂ * t ^ 2) * (1 - e₃ * t ^ 2) := by
        dsimp [w] at hu_sq
        linear_combination hu_sq
      have hu_one_lt : Valued.v (u - 1) < Valued.v (1 : F) := by
        rw [Valuation.map_one, ← WithZero.exp_zero]
        exact lt_of_le_of_lt hu_one (WithZero.exp_lt_exp.mpr (by omega))
      have hvu : Valued.v u = 1 := by
        have hu_eq : u = 1 + (u - 1) := by ring
        rw [hu_eq, Valuation.map_add_eq_of_lt_left Valued.v hu_one_lt, Valuation.map_one]
      have hu0 : u ≠ 0 := by
        intro hu0
        rw [hu0, Valuation.map_zero] at hvu
        exact zero_ne_one hvu
      let x : F := (t ^ 2)⁻¹
      let y : F := -(t ^ 3)⁻¹ * u
      have hxt2 : x * t ^ 2 = 1 := inv_mul_cancel₀ (pow_ne_zero 2 ht0)
      have hyt3 : y * t ^ 3 = -u := by
        dsimp [y]
        field_simp [ht0]
      have heq_xy : y ^ 2 = (x - e₁) * (x - e₂) * (x - e₃) := by
        have h_mul_t6 : t ^ 6 * (y ^ 2 - (x - e₁) * (x - e₂) * (x - e₃)) = 0 := by
          calc t ^ 6 * (y ^ 2 - (x - e₁) * (x - e₂) * (x - e₃))
            _ = (y * t ^ 3) ^ 2 - (x * t ^ 2 - e₁ * t ^ 2) * (x * t ^ 2 - e₂ * t ^ 2) * (x * t ^ 2 - e₃ * t ^ 2) := by ring
            _ = (-u) ^ 2 - (1 - e₁ * t ^ 2) * (1 - e₂ * t ^ 2) * (1 - e₃ * t ^ 2) := by rw [hyt3, hxt2]
            _ = u ^ 2 - (1 - e₁ * t ^ 2) * (1 - e₂ * t ^ 2) * (1 - e₃ * t ^ 2) := by ring
            _ = 0 := sub_eq_zero.mpr hu_sq'
        exact sub_eq_zero.mp ((mul_eq_zero.mp h_mul_t6).resolve_left (pow_ne_zero 6 ht0))
      have h_weq : W.Equation x y := by
        rw [WeierstrassCurve.Affine.equation_iff]
        dsimp [W, threeRootsCurve]
        linear_combination heq_xy
      have hy0 : y ≠ 0 := by
        dsimp [y]
        exact mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 3 ht0))) hu0
      have h_ns : W.Nonsingular x y := by
        rw [WeierstrassCurve.Affine.nonsingular_iff]
        refine ⟨h_weq, Or.inr ?_⟩
        dsimp [W, threeRootsCurve]
        intro hy_eq
        have h2y : (2 : F) * y = 0 := by linear_combination hy_eq
        exact mul_ne_zero two_ne_zero hy0 h2y
      let P : W.Point := WeierstrassCurve.Affine.Point.some h_ns
      have hP_mem : P ∈ lutzSet e₁ e₂ e₃ m := by
        change WithZero.exp (2 * m) ≤ Valued.v x
        calc WithZero.exp (2 * m)
          _ = WithZero.exp (2 * m) * (Valued.v (t ^ 2) * Valued.v x) := by
            rw [← Valuation.map_mul, mul_comm (t ^ 2) x, hxt2, Valuation.map_one, mul_one]
          _ = (WithZero.exp (2 * m) * Valued.v (t ^ 2)) * Valued.v x := (mul_assoc _ _ _).symm
          _ ≤ (WithZero.exp (2 * m) * WithZero.exp (-2 * m)) * Valued.v x :=
            mul_le_mul' (mul_le_mul' le_rfl ht2_val) le_rfl
          _ = WithZero.exp (2 * m + -2 * m) * Valued.v x := by rw [← WithZero.exp_add]
          _ = Valued.v x := by
            have h0 : (2 * m + -2 * m : ℤ) = 0 := by ring
            rw [h0, WithZero.exp_zero, one_mul]
      refine ⟨P, hP_mem, ?_⟩
      change Valued.v (-x / y - t) ≤ WithZero.exp (-(m + (e : ℤ)))
      have h_param_eq : -x / y - t = -(t * (u - 1) / u) := by
        dsimp [x, y]
        field_simp [ht0, hu0]
        ring
      rw [h_param_eq, Valuation.map_neg, Valuation.map_div, hvu, div_one, Valuation.map_mul]
      calc Valued.v t * Valued.v (u - 1)
        _ ≤ WithZero.exp (-m) * WithZero.exp (-(e : ℤ) - 1) := mul_le_mul' ht_val hu_one
        _ = WithZero.exp (-m + (-(e : ℤ) - 1)) := (WithZero.exp_add (-m) (-(e : ℤ) - 1)).symm
        _ ≤ WithZero.exp (-(m + (e : ℤ))) := by rw [WithZero.exp_le_exp]; omega
  have h_half_gen : ∀ {F : Type _} (_ : (F = K) = (F = K)) [Field F] [CharZero F] [DecidableEq F]
      [Valued F (WithZero (Multiplicative ℤ))]
      (e₁ e₂ e₃ : F) (B e : ℕ) (m : ℤ) (hm : (B : ℤ) + (e : ℤ) + 2 ≤ m)
      (he₁ : Valued.v e₁ ≤ WithZero.exp (B : ℤ))
      (he₂ : Valued.v e₂ ≤ WithZero.exp (B : ℤ))
      (he₃ : Valued.v e₃ ≤ WithZero.exp (B : ℤ))
      (he : Valued.v (2 : F) = WithZero.exp (-(e : ℤ)))
      (h_sqrt : ∀ w : F, Valued.v w ≤ WithZero.exp (-2 * (e : ℤ) - 1) →
        ∃ u : F, u ^ 2 = 1 + w ∧ Valued.v (u - 1) ≤ WithZero.exp (-(e : ℤ) - 1)),
      ∀ P ∈ lutzSet e₁ e₂ e₃ (m + (e : ℤ)),
        ∃ Q ∈ lutzSet e₁ e₂ e₃ m, Q + Q = P := by
    intro F _ _ _ _ _ e₁ e₂ e₃ B e m hm he₁ he₂ he₃ he h_sqrt P₀ hP₀
    clear h_param_gen
    let W := (threeRootsCurve e₁ e₂ e₃).toAffine
    cases P₀ with
    | zero =>
      exact ⟨0, trivial, rfl⟩
    | @some x₀ y₀ h₀ =>
      have hx₀_val : WithZero.exp (2 * (m + (e : ℤ))) ≤ Valued.v x₀ := hP₀
      have h_curve₀ : y₀ ^ 2 = (x₀ - e₁) * (x₀ - e₂) * (x₀ - e₃) := by
        have heq := h₀.1
        rw [WeierstrassCurve.Affine.equation_iff] at heq
        dsimp [W, threeRootsCurve] at heq
        linear_combination heq
      have hx₀_ne : x₀ ≠ 0 := by
        intro hx₀
        rw [hx₀, Valuation.map_zero] at hx₀_val
        exact not_lt_of_ge hx₀_val WithZero.exp_pos
      have h_w_bound : ∀ {a : F}, Valued.v a ≤ WithZero.exp (B : ℤ) →
          Valued.v (-a / x₀) ≤ WithZero.exp (-2 * (e : ℤ) - 1) := by
        intro a ha
        have h_mul : Valued.v (-a / x₀) * WithZero.exp (2 * (m + (e : ℤ))) ≤ WithZero.exp (B : ℤ) := by
          calc Valued.v (-a / x₀) * WithZero.exp (2 * (m + (e : ℤ)))
            _ ≤ Valued.v (-a / x₀) * Valued.v x₀ := mul_le_mul' le_rfl hx₀_val
            _ = Valued.v (-a / x₀ * x₀) := (Valuation.map_mul Valued.v _ _).symm
            _ = Valued.v (-a) := by rw [div_mul_cancel₀ (-a) hx₀_ne]
            _ = Valued.v a := Valuation.map_neg Valued.v a
            _ ≤ WithZero.exp (B : ℤ) := ha
        calc Valued.v (-a / x₀)
          _ = (Valued.v (-a / x₀) * WithZero.exp (2 * (m + (e : ℤ)))) * WithZero.exp (-2 * (m + (e : ℤ))) := by
            rw [mul_assoc, ← WithZero.exp_add]
            have h0 : 2 * (m + (e : ℤ)) + -2 * (m + (e : ℤ)) = 0 := by ring
            rw [h0, WithZero.exp_zero, mul_one]
          _ ≤ WithZero.exp (B : ℤ) * WithZero.exp (-2 * (m + (e : ℤ))) :=
            mul_le_mul' h_mul le_rfl
          _ = WithZero.exp ((B : ℤ) + -2 * (m + (e : ℤ))) := (WithZero.exp_add _ _).symm
          _ ≤ WithZero.exp (-2 * (e : ℤ) - 1) := by rw [WithZero.exp_le_exp]; omega
      obtain ⟨v₁, hv₁_sq, hv₁_one⟩ := h_sqrt (-e₁ / x₀) (h_w_bound he₁)
      obtain ⟨v₂, hv₂_sq, hv₂_one⟩ := h_sqrt (-e₂ / x₀) (h_w_bound he₂)
      obtain ⟨v₃, hv₃_sq, hv₃_one⟩ := h_sqrt (-e₃ / x₀) (h_w_bound he₃)
      have h_v_ne : ∀ {v : F}, Valued.v (v - 1) ≤ WithZero.exp (-(e : ℤ) - 1) → v ≠ 0 := by
        intro v hv hv0
        have hv_lt : Valued.v (v - 1) < 1 := by
          rw [← WithZero.exp_zero]
          exact lt_of_le_of_lt hv (WithZero.exp_lt_exp.mpr (by omega))
        rw [hv0, zero_sub, Valuation.map_neg, Valuation.map_one] at hv_lt
        exact lt_irrefl 1 hv_lt
      have hv₁_ne : v₁ ≠ 0 := h_v_ne hv₁_one
      have hv₂_ne : v₂ ≠ 0 := h_v_ne hv₂_one
      have hv₃_ne : v₃ ≠ 0 := h_v_ne hv₃_one
      have h_x₀_v_sq : ∀ {v a : F}, v ^ 2 = 1 + -a / x₀ → x₀ * v ^ 2 = x₀ - a := by
        intro v a hv
        rw [hv]
        field_simp [hx₀_ne]
        ring
      have hx₀_v₁ : x₀ * v₁ ^ 2 = x₀ - e₁ := h_x₀_v_sq hv₁_sq
      have hx₀_v₂ : x₀ * v₂ ^ 2 = x₀ - e₂ := h_x₀_v_sq hv₂_sq
      have hx₀_v₃ : x₀ * v₃ ^ 2 = x₀ - e₃ := h_x₀_v_sq hv₃_sq
      let D₀ : F := x₀ * v₁ * v₂ * v₃
      have hD₀_ne : D₀ ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hx₀_ne hv₁_ne) hv₂_ne) hv₃_ne
      let s : F := -y₀ / D₀
      have hD₀_s : D₀ * s = -y₀ := mul_div_cancel₀ (-y₀) hD₀_ne
      have hs_sq : s ^ 2 = x₀ := by
        have h_eq : D₀ ^ 2 * (s ^ 2 - x₀) = 0 := by
          calc D₀ ^ 2 * (s ^ 2 - x₀)
            _ = (D₀ * s) ^ 2 - (x₀ * v₁ ^ 2) * (x₀ * v₂ ^ 2) * (x₀ * v₃ ^ 2) := by
              dsimp [D₀]; ring
            _ = (-y₀) ^ 2 - (x₀ - e₁) * (x₀ - e₂) * (x₀ - e₃) := by
              rw [hD₀_s, hx₀_v₁, hx₀_v₂, hx₀_v₃]
            _ = y₀ ^ 2 - (x₀ - e₁) * (x₀ - e₂) * (x₀ - e₃) := by ring
            _ = 0 := sub_eq_zero.mpr h_curve₀
        exact sub_eq_zero.mp ((mul_eq_zero.mp h_eq).resolve_left (pow_ne_zero 2 hD₀_ne))
      have hs_ne : s ≠ 0 := by
        intro hs0
        apply hx₀_ne
        rw [← hs_sq, hs0, sq, zero_mul]
      let u₁ : F := -s * v₁
      let u₂ : F := -s * v₂
      let u₃ : F := -s * v₃
      have hu₁_sq : u₁ ^ 2 = x₀ - e₁ := by
        calc u₁ ^ 2 = s ^ 2 * v₁ ^ 2 := by dsimp [u₁]; ring
          _ = x₀ * v₁ ^ 2 := by rw [hs_sq]
          _ = x₀ - e₁ := hx₀_v₁
      have hu₂_sq : u₂ ^ 2 = x₀ - e₂ := by
        calc u₂ ^ 2 = s ^ 2 * v₂ ^ 2 := by dsimp [u₂]; ring
          _ = x₀ * v₂ ^ 2 := by rw [hs_sq]
          _ = x₀ - e₂ := hx₀_v₂
      have hu₃_sq : u₃ ^ 2 = x₀ - e₃ := by
        calc u₃ ^ 2 = s ^ 2 * v₃ ^ 2 := by dsimp [u₃]; ring
          _ = x₀ * v₃ ^ 2 := by rw [hs_sq]
          _ = x₀ - e₃ := hx₀_v₃
      have he₁_eq : e₁ = x₀ - u₁ ^ 2 := by linear_combination hu₁_sq
      have he₂_eq : e₂ = x₀ - u₂ ^ 2 := by linear_combination hu₂_sq
      have he₃_eq : e₃ = x₀ - u₃ ^ 2 := by linear_combination hu₃_sq
      have hu₁₂₃ : u₁ * u₂ * u₃ = y₀ := by
        calc u₁ * u₂ * u₃
          _ = -(s ^ 2 * (v₁ * v₂ * v₃ * s)) := by dsimp [u₁, u₂, u₃]; ring
          _ = -(x₀ * (v₁ * v₂ * v₃ * s)) := by rw [hs_sq]
          _ = -(D₀ * s) := by dsimp [D₀]; ring
          _ = -(-y₀) := by rw [hD₀_s]
          _ = y₀ := neg_neg y₀
      have h_vij_val : ∀ {a b : F},
          Valued.v (a - 1) ≤ WithZero.exp (-(e : ℤ) - 1) →
          Valued.v (b - 1) ≤ WithZero.exp (-(e : ℤ) - 1) →
          Valued.v (a + b) = WithZero.exp (-(e : ℤ)) := by
        intro a b ha hb
        have h_eq : a + b = (2 : F) + ((a - 1) + (b - 1)) := by ring
        have h_lt : Valued.v ((a - 1) + (b - 1)) < Valued.v (2 : F) := by
          rw [he]
          refine lt_of_le_of_lt (le_trans (Valuation.map_add Valued.v _ _) (max_le ha hb)) ?_
          rw [WithZero.exp_lt_exp]
          omega
        rw [h_eq, Valuation.map_add_eq_of_lt_left Valued.v h_lt, he]
      have hv₁₂_val : Valued.v (v₁ + v₂) = WithZero.exp (-(e : ℤ)) := h_vij_val hv₁_one hv₂_one
      have hv₁₃_val : Valued.v (v₁ + v₃) = WithZero.exp (-(e : ℤ)) := h_vij_val hv₁_one hv₃_one
      have hv₂₃_val : Valued.v (v₂ + v₃) = WithZero.exp (-(e : ℤ)) := h_vij_val hv₂_one hv₃_one
      have h_uij_ne : ∀ {a b : F}, Valued.v (a + b) = WithZero.exp (-(e : ℤ)) → (-s * a + -s * b) ≠ 0 := by
        intro a b hab h0
        have h_ab : a + b = 0 := by
          have h_mul : (-s) * (a + b) = 0 := by linear_combination h0
          exact (mul_eq_zero.mp h_mul).resolve_left (neg_ne_zero.mpr hs_ne)
        rw [h_ab, Valuation.map_zero] at hab
        exact WithZero.exp_ne_zero hab.symm
      have hu₁₂_ne : u₁ + u₂ ≠ 0 := h_uij_ne hv₁₂_val
      have hu₁₃_ne : u₁ + u₃ ≠ 0 := h_uij_ne hv₁₃_val
      have hu₂₃_ne : u₂ + u₃ ≠ 0 := h_uij_ne hv₂₃_val
      let x₁ : F := x₀ + u₁ * u₂ + u₁ * u₃ + u₂ * u₃
      let y₁ : F := (u₁ + u₂) * (u₁ + u₃) * (u₂ + u₃)
      have hy₁_ne : y₁ ≠ 0 := mul_ne_zero (mul_ne_zero hu₁₂_ne hu₁₃_ne) hu₂₃_ne
      have heq₁ : y₁ ^ 2 = (x₁ - e₁) * (x₁ - e₂) * (x₁ - e₃) := by
        dsimp [x₁, y₁]
        rw [he₁_eq, he₂_eq, he₃_eq]
        ring
      have h_weq₁ : W.Equation x₁ y₁ := by
        rw [WeierstrassCurve.Affine.equation_iff]
        dsimp [W, threeRootsCurve]
        linear_combination heq₁
      have hy₁_negY : y₁ ≠ W.negY x₁ y₁ := by
        dsimp [W, threeRootsCurve, WeierstrassCurve.Affine.negY]
        intro hy_eq
        have h2y₁ : (2 : F) * y₁ = 0 := by linear_combination hy_eq
        exact mul_ne_zero two_ne_zero hy₁_ne h2y₁
      have h_ns₁ : W.Nonsingular x₁ y₁ :=
        (WeierstrassCurve.Affine.nonsingular_iff x₁ y₁).mpr ⟨h_weq₁, Or.inr hy₁_negY⟩
      let Q : W.Point := WeierstrassCurve.Affine.Point.some h_ns₁
      have hQ_mem : Q ∈ lutzSet e₁ e₂ e₃ m := by
        change WithZero.exp (2 * m) ≤ Valued.v x₁
        have hx₁_e₁ : x₁ - e₁ = x₀ * (v₁ + v₂) * (v₁ + v₃) := by
          calc x₁ - e₁
            _ = (u₁ + u₂) * (u₁ + u₃) := by dsimp [x₁]; rw [he₁_eq]; ring
            _ = s ^ 2 * (v₁ + v₂) * (v₁ + v₃) := by dsimp [u₁, u₂, u₃]; ring
            _ = x₀ * (v₁ + v₂) * (v₁ + v₃) := by rw [hs_sq]
        have hx₁_e₁_val : WithZero.exp (2 * m) ≤ Valued.v (x₁ - e₁) := by
          rw [hx₁_e₁, Valuation.map_mul, Valuation.map_mul, hv₁₂_val, hv₁₃_val]
          calc WithZero.exp (2 * m)
            _ = WithZero.exp (2 * (m + (e : ℤ))) * WithZero.exp (-(e : ℤ)) * WithZero.exp (-(e : ℤ)) := by
              rw [← WithZero.exp_add, ← WithZero.exp_add]
              congr 1
              ring
            _ ≤ Valued.v x₀ * WithZero.exp (-(e : ℤ)) * WithZero.exp (-(e : ℤ)) :=
              mul_le_mul' (mul_le_mul' hx₀_val le_rfl) le_rfl
        have he₁_lt : Valued.v e₁ < Valued.v (x₁ - e₁) := by
          refine lt_of_le_of_lt he₁ (lt_of_lt_of_le ?_ hx₁_e₁_val)
          rw [WithZero.exp_lt_exp]
          omega
        have hx₁_eq : x₁ = (x₁ - e₁) + e₁ := by ring
        rw [hx₁_eq, Valuation.map_add_eq_of_lt_left Valued.v he₁_lt]
        exact hx₁_e₁_val
      refine ⟨Q, hQ_mem, ?_⟩
      dsimp [Q]
      rw [WeierstrassCurve.Affine.Point.add_of_Y_ne hy₁_negY,
          WeierstrassCurve.Affine.Point.some.injEq]
      have h_slope : W.slope x₁ x₁ y₁ y₁ = u₁ + u₂ + u₃ := by
        rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy₁_negY]
        have h_num : 3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁ =
            (u₁ + u₂ + u₃) * (y₁ - W.negY x₁ y₁) := by
          dsimp [W, threeRootsCurve, WeierstrassCurve.Affine.negY, x₁, y₁]
          rw [he₁_eq, he₂_eq, he₃_eq]
          ring
        rw [h_num, mul_div_cancel_right₀ _ (sub_ne_zero.mpr hy₁_negY)]
      rw [h_slope]
      have h_addX : W.addX x₁ x₁ (u₁ + u₂ + u₃) = x₀ := by
        dsimp [W, threeRootsCurve, WeierstrassCurve.Affine.addX, x₁]
        rw [he₁_eq, he₂_eq, he₃_eq]
        ring
      refine ⟨h_addX, ?_⟩
      dsimp [W, threeRootsCurve, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.addX,
        WeierstrassCurve.Affine.negY, x₁, y₁]
      rw [he₁_eq, he₂_eq, he₃_eq, ← hu₁₂₃]
      ring
  have h_inj : Function.Injective (algebraMap K (v.adicCompletion K)) :=
    (algebraMap K (v.adicCompletion K)).injective
  haveI : CharZero (v.adicCompletion K) := charZero_of_injective_ringHom h_inj
  have h_hensel : ∀ (p y : ↥(v.adicCompletionIntegers K)),
      Valued.v (p : v.adicCompletion K) < 1 →
      ∃ z : ↥(v.adicCompletionIntegers K), z + p * z ^ 2 = y :=
    fun p y hp => exists_add_mul_sq_eq_adicCompletionIntegers v p y hp
  let F := v.adicCompletion K
  have h_sqrt : ∀ w : F, Valued.v w ≤ WithZero.exp (-2 * (e : ℤ) - 1) →
      ∃ u : F, u ^ 2 = 1 + w ∧ Valued.v (u - 1) ≤ WithZero.exp (-(e : ℤ) - 1) := by
    intro w hw
    have h2_ne : (2 : F) ≠ 0 := two_ne_zero
    let p_F : F := w / ((2 : F) * (2 : F))
    have hp_val : Valued.v p_F ≤ WithZero.exp (-1 : ℤ) := by
      have h_mul : Valued.v p_F * WithZero.exp (-2 * (e : ℤ)) = Valued.v w := by
        have h4 : Valued.v ((2 : F) * (2 : F)) = WithZero.exp (-2 * (e : ℤ)) := by
          rw [Valuation.map_mul, he, ← WithZero.exp_add]
          congr 1
          ring
        rw [← h4, ← Valuation.map_mul]
        dsimp [p_F]
        rw [div_mul_cancel₀ w (mul_ne_zero h2_ne h2_ne)]
      calc Valued.v p_F
        _ = (Valued.v p_F * WithZero.exp (-2 * (e : ℤ))) * WithZero.exp (2 * (e : ℤ)) := by
          rw [mul_assoc, ← WithZero.exp_add]
          have h0 : -2 * (e : ℤ) + 2 * (e : ℤ) = 0 := by ring
          rw [h0, WithZero.exp_zero, mul_one]
        _ = Valued.v w * WithZero.exp (2 * (e : ℤ)) := by rw [h_mul]
        _ ≤ WithZero.exp (-2 * (e : ℤ) - 1) * WithZero.exp (2 * (e : ℤ)) :=
          mul_le_mul' hw le_rfl
        _ = WithZero.exp ((-2 * (e : ℤ) - 1) + 2 * (e : ℤ)) := (WithZero.exp_add _ _).symm
        _ = WithZero.exp (-1 : ℤ) := by congr 1; ring
    have hp_lt : Valued.v p_F < 1 := by
      rw [← WithZero.exp_zero]
      exact lt_of_le_of_lt hp_val (WithZero.exp_lt_exp.mpr (by omega))
    have hp_mem : p_F ∈ v.adicCompletionIntegers K := le_of_lt hp_lt
    obtain ⟨z, hz⟩ := h_hensel ⟨p_F, hp_mem⟩ 1 hp_lt
    have hz_F : z.1 + p_F * z.1 ^ 2 = 1 := congrArg Subtype.val hz
    let u : F := 1 + (w / 2) * z.1
    refine ⟨u, ?_, ?_⟩
    · have h_u_sq : u ^ 2 - (1 + w) = w * (z.1 + p_F * z.1 ^ 2 - 1) := by
        dsimp [u, p_F]
        field_simp [h2_ne]
        ring
      have h_rhs_zero : z.1 + p_F * z.1 ^ 2 - 1 = 0 := sub_eq_zero.mpr hz_F
      rw [h_rhs_zero, mul_zero] at h_u_sq
      exact sub_eq_zero.mp h_u_sq
    · have hu_sub : u - 1 = (w / 2) * z.1 := by dsimp [u]; ring
      have hw2_val : Valued.v (w / 2) ≤ WithZero.exp (-(e : ℤ) - 1) := by
        have h_mul : Valued.v (w / 2) * WithZero.exp (-(e : ℤ)) = Valued.v w := by
          rw [← he, ← Valuation.map_mul, div_mul_cancel₀ w h2_ne]
        calc Valued.v (w / 2)
          _ = (Valued.v (w / 2) * WithZero.exp (-(e : ℤ))) * WithZero.exp (e : ℤ) := by
            rw [mul_assoc, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, mul_one]
          _ = Valued.v w * WithZero.exp (e : ℤ) := by rw [h_mul]
          _ ≤ WithZero.exp (-2 * (e : ℤ) - 1) * WithZero.exp (e : ℤ) :=
            mul_le_mul' hw le_rfl
          _ = WithZero.exp ((-2 * (e : ℤ) - 1) + (e : ℤ)) := (WithZero.exp_add _ _).symm
          _ = WithZero.exp (-(e : ℤ) - 1) := by congr 1; ring
      rw [hu_sub, Valuation.map_mul]
      calc Valued.v (w / 2) * Valued.v z.1
        _ ≤ WithZero.exp (-(e : ℤ) - 1) * 1 := mul_le_mul' hw2_val z.property
        _ = WithZero.exp (-(e : ℤ) - 1) := mul_one _
  exact ⟨h_param_gen rfl e₁ e₂ e₃ B e m hm he₁ he₂ he₃ h_sqrt,
         h_half_gen rfl e₁ e₂ e₃ B e m hm he₁ he₂ he₃ he h_sqrt⟩

theorem lutzSet_finite_index_adicCompletion {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    [DecidableEq (v.adicCompletion K)]
    (e₁ e₂ e₃ : v.adicCompletion K) (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃)
    (B : ℕ) (m : ℤ) (hm : (B : ℤ) + 1 ≤ m)
    (he₁ : Valued.v e₁ ≤ WithZero.exp (B : ℤ))
    (he₂ : Valued.v e₂ ≤ WithZero.exp (B : ℤ))
    (he₃ : Valued.v e₃ ≤ WithZero.exp (B : ℤ)) :
    ∃ (n : ℕ) (f : (threeRootsCurve e₁ e₂ e₃).toAffine.Point → Fin n),
      ∀ P Q : (threeRootsCurve e₁ e₂ e₃).toAffine.Point,
        f P = f Q → P - Q ∈ lutzSet e₁ e₂ e₃ m :=
by
  classical
  have exp_not_le_iff_le_sub_one : ∀ {v₀ : WithZero (Multiplicative ℤ)} {k : ℤ},
      ¬ WithZero.exp k ≤ v₀ → v₀ ≤ WithZero.exp (k - 1) := by
    intro v₀ k h
    rcases eq_or_ne v₀ 0 with rfl | hv
    · exact zero_le'
    · rcases WithZero.ne_zero_iff_exists.mp hv with ⟨g, hg⟩
      let z : ℤ := Multiplicative.toAdd g
      have hz : v₀ = WithZero.exp z := by rw [← hg]; rfl
      rw [hz, WithZero.exp_le_exp] at h ⊢
      omega
  have sq_le_sq_imp_le : ∀ {u w : WithZero (Multiplicative ℤ)}, u * u ≤ w * w → u ≤ w := by
    intro u w h
    by_contra hlt
    have hle : w ≤ u := le_of_not_ge hlt
    have hne : u ≠ w := fun heq => hlt (le_of_eq heq)
    have hw_lt_u : w < u := lt_of_le_of_ne hle hne.symm
    have hu_ne : u ≠ 0 := by
      intro hu0
      rw [hu0] at hw_lt_u
      exact not_lt_of_ge zero_le' hw_lt_u
    rcases WithZero.ne_zero_iff_exists.mp hu_ne with ⟨gu, hgu⟩
    let zu : ℤ := Multiplicative.toAdd gu
    have hzu : u = WithZero.exp zu := by rw [← hgu]; rfl
    rcases eq_or_ne w 0 with rfl | hw_ne
    · rw [mul_zero, hzu, ← WithZero.exp_add] at h
      exact not_lt_of_ge h WithZero.exp_pos
    · rcases WithZero.ne_zero_iff_exists.mp hw_ne with ⟨gw, hgw⟩
      let zw : ℤ := Multiplicative.toAdd gw
      have hzw : w = WithZero.exp zw := by rw [← hgw]; rfl
      rw [hzu, hzw, WithZero.exp_lt_exp] at hw_lt_u
      rw [hzu, hzw, ← WithZero.exp_add, ← WithZero.exp_add, WithZero.exp_le_exp] at h
      omega
  have not_mem_lutzSet_val_le : ∀ {F' : Type _} (_ : (F' = K) = (F' = K)) [Field F']
      [Valued F' (WithZero (Multiplicative ℤ))]
      (e₁ e₂ e₃ : F') (B : ℕ) (m : ℤ) (hm : (B : ℤ) + 1 ≤ m)
      (he₁ : Valued.v e₁ ≤ WithZero.exp (B : ℤ))
      (he₂ : Valued.v e₂ ≤ WithZero.exp (B : ℤ))
      (he₃ : Valued.v e₃ ≤ WithZero.exp (B : ℤ))
      {x y : F'} (h : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x y)
      (hP : WeierstrassCurve.Affine.Point.some h ∉ lutzSet e₁ e₂ e₃ m),
      Valued.v x ≤ WithZero.exp (2 * m - 1) ∧
      Valued.v (y * y) ≤ WithZero.exp (6 * m - 3) ∧
      Valued.v x ≤ WithZero.exp (2 * m) ∧
      Valued.v y ≤ WithZero.exp (3 * m) := by
    intro F' _ _ _ e₁ e₂ e₃ B m hm he₁ he₂ he₃ x y h hP
    have hx1 : Valued.v x ≤ WithZero.exp (2 * m - 1) := exp_not_le_iff_le_sub_one hP
    have hx : Valued.v x ≤ WithZero.exp (2 * m) :=
      le_trans hx1 (WithZero.exp_le_exp.mpr (by omega))
    have hB : WithZero.exp (B : ℤ) ≤ WithZero.exp (2 * m - 1) :=
      WithZero.exp_le_exp.mpr (by omega)
    have hxe1 : Valued.v (x - e₁) ≤ WithZero.exp (2 * m - 1) :=
      le_trans (Valuation.map_sub Valued.v x e₁) (max_le hx1 (le_trans he₁ hB))
    have hxe2 : Valued.v (x - e₂) ≤ WithZero.exp (2 * m - 1) :=
      le_trans (Valuation.map_sub Valued.v x e₂) (max_le hx1 (le_trans he₂ hB))
    have hxe3 : Valued.v (x - e₃) ≤ WithZero.exp (2 * m - 1) :=
      le_trans (Valuation.map_sub Valued.v x e₃) (max_le hx1 (le_trans he₃ hB))
    have heq : y * y = (x - e₁) * (x - e₂) * (x - e₃) := by
      have h0 := (WeierstrassCurve.Affine.equation_iff x y).mp h.1
      dsimp [threeRootsCurve] at h0
      linear_combination h0
    have hyy : Valued.v (y * y) ≤ WithZero.exp (6 * m - 3) := by
      rw [heq, Valuation.map_mul, Valuation.map_mul]
      calc
        Valued.v (x - e₁) * Valued.v (x - e₂) * Valued.v (x - e₃) ≤
            WithZero.exp (2 * m - 1) * WithZero.exp (2 * m - 1) * WithZero.exp (2 * m - 1) :=
          mul_le_mul' (mul_le_mul' hxe1 hxe2) hxe3
        _ = WithZero.exp (6 * m - 3) := by
          rw [← WithZero.exp_add, ← WithZero.exp_add]
          congr 1
          omega
    have hy : Valued.v y ≤ WithZero.exp (3 * m) := by
      apply sq_le_sq_imp_le
      rw [← Valuation.map_mul, ← WithZero.exp_add]
      exact le_trans hyy (WithZero.exp_le_exp.mpr (by omega))
    exact ⟨hx1, hyy, hx, hy⟩
  have unified_slope_eq : ∀ {F' : Type _} (_ : (F' = K) = (F' = K)) [Field F'] [DecidableEq F']
      (e₁ e₂ e₃ : F') {x₁ y₁ x₂ y₂ : F'}
      (h₁ : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x₁ y₁)
      (h₂ : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x₂ y₂)
      (hne : ¬ (x₁ = x₂ ∧ y₁ = (threeRootsCurve e₁ e₂ e₃).toAffine.negY x₂
        ((threeRootsCurve e₁ e₂ e₃).toAffine.negY x₂ y₂))),
      let W := (threeRootsCurve e₁ e₂ e₃).toAffine
      let lam := W.slope x₁ x₂ y₁ (W.negY x₂ y₂)
      let M := (x₁ - e₁) * (x₁ - e₂) + (x₁ - e₁) * (x₂ - e₃) + (x₂ - e₂) * (x₂ - e₃)
      lam * (x₁ - x₂) = y₁ + y₂ ∧ lam * (y₁ - y₂) = M := by
    intro F' _ _ _ e₁ e₂ e₃ x₁ y₁ x₂ y₂ h₁ h₂ hne W lam M
    have heq1 : y₁ ^ 2 = (x₁ - e₁) * (x₁ - e₂) * (x₁ - e₃) := by
      have h0 := (WeierstrassCurve.Affine.equation_iff x₁ y₁).mp h₁.1
      dsimp [threeRootsCurve] at h0
      linear_combination h0
    have heq2 : y₂ ^ 2 = (x₂ - e₁) * (x₂ - e₂) * (x₂ - e₃) := by
      have h0 := (WeierstrassCurve.Affine.equation_iff x₂ y₂).mp h₂.1
      dsimp [threeRootsCurve] at h0
      linear_combination h0
    have hnegY : ∀ x y : F', W.negY x y = -y := by
      intro x y
      dsimp [W, threeRootsCurve, WeierstrassCurve.Affine.negY]
      ring
    have hM_diff : (x₁ - x₂) * M = (y₁ - y₂) * (y₁ + y₂) := by
      dsimp [M]
      linear_combination -heq1 + heq2
    by_cases hx : x₁ = x₂
    · subst hx
      have hy_ne : y₁ ≠ W.negY x₁ (W.negY x₁ y₂) := fun hy => hne ⟨rfl, hy⟩
      have hy_ne' : y₁ ≠ y₂ := by
        rwa [hnegY, hnegY, neg_neg] at hy_ne
      have hy_sub_ne : y₁ - y₂ ≠ 0 := sub_ne_zero.mpr hy_ne'
      have hy_sum : y₁ + y₂ = 0 := by
        have hprod : (y₁ - y₂) * (y₁ + y₂) = 0 := by
          linear_combination -hM_diff
        exact (mul_eq_zero.mp hprod).resolve_left hy_sub_ne
      have hA : lam * (x₁ - x₁) = y₁ + y₂ := by
        linear_combination -hy_sum
      have hlam : lam = (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) / (y₁ - W.negY x₁ y₁) :=
        WeierstrassCurve.Affine.slope_of_Y_ne rfl hy_ne
      have hdenom : y₁ - W.negY x₁ y₁ = y₁ - y₂ := by
        rw [hnegY]
        linear_combination hy_sum
      have hnum : 3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁ = M := by
        dsimp [W, threeRootsCurve, M]
        ring
      rw [hdenom, hnum] at hlam
      have hB : lam * (y₁ - y₂) = M := by
        rw [hlam, div_mul_cancel₀ M hy_sub_ne]
      exact ⟨hA, hB⟩
    · have hx_sub_ne : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
      have hlam : lam = (y₁ - W.negY x₂ y₂) / (x₁ - x₂) :=
        WeierstrassCurve.Affine.slope_of_X_ne hx
      have hnum : y₁ - W.negY x₂ y₂ = y₁ + y₂ := by
        rw [hnegY]
        ring
      rw [hnum] at hlam
      have hA : lam * (x₁ - x₂) = y₁ + y₂ := by
        rw [hlam, div_mul_cancel₀ (y₁ + y₂) hx_sub_ne]
      have hB_mul : (x₁ - x₂) * (lam * (y₁ - y₂) - M) = 0 := by
        linear_combination (y₁ - y₂) * hA - hM_diff
      have hB : lam * (y₁ - y₂) = M :=
        sub_eq_zero.mp ((mul_eq_zero.mp hB_mul).resolve_left hx_sub_ne)
      exact ⟨hA, hB⟩
  have sub_mem_lutzSet_of_val_le_of_sub_le : ∀ {F' : Type _} (_ : (F' = K) = (F' = K))
      [Field F'] [DecidableEq F'] [Valued F' (WithZero (Multiplicative ℤ))]
      (e₁ e₂ e₃ : F') (B δ : ℕ) (m : ℤ) (hm : (B : ℤ) + 1 ≤ m)
      (he₁ : Valued.v e₁ ≤ WithZero.exp (B : ℤ))
      (he₂ : Valued.v e₂ ≤ WithZero.exp (B : ℤ))
      (he₃ : Valued.v e₃ ≤ WithZero.exp (B : ℤ))
      (hΔ : WithZero.exp (-(δ : ℤ)) ≤
        Valued.v ((4 * (e₁ - e₂) ^ 2 * (e₁ - e₃) ^ 2 * (e₂ - e₃) ^ 2 : F')))
      {x₁ y₁ x₂ y₂ : F'}
      (h₁ : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x₁ y₁)
      (h₂ : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x₂ y₂)
      (hx₁ : Valued.v x₁ ≤ WithZero.exp (2 * m))
      (hx₂ : Valued.v x₂ ≤ WithZero.exp (2 * m))
      (hx_sub : Valued.v (x₁ - x₂) ≤ WithZero.exp (-(5 * m + (δ : ℤ) + 1)))
      (hy_sub : Valued.v (y₁ - y₂) ≤ WithZero.exp (-(5 * m + (δ : ℤ) + 1))),
      WeierstrassCurve.Affine.Point.some h₁ - WeierstrassCurve.Affine.Point.some h₂ ∈
        lutzSet e₁ e₂ e₃ m := by
    intro F' _ _ _ _ e₁ e₂ e₃ B δ m hm he₁ he₂ he₃ hΔ x₁ y₁ x₂ y₂ h₁ h₂ hx₁ hx₂ hx_sub hy_sub
    let W := (threeRootsCurve e₁ e₂ e₃).toAffine
    let N₀ : ℤ := 5 * m + (δ : ℤ) + 1
    rw [sub_eq_add_neg, WeierstrassCurve.Affine.Point.neg_some]
    by_cases hne : x₁ = x₂ ∧ y₁ = W.negY x₂ (W.negY x₂ y₂)
    · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hne.1 hne.2]
      exact trivial
    · rw [WeierstrassCurve.Affine.Point.add_some hne]
      by_contra hP₃
      rcases not_mem_lutzSet_val_le rfl e₁ e₂ e₃ B m hm he₁ he₂ he₃ _ hP₃ with ⟨_, _, hx₃, _⟩
      have h_slope := unified_slope_eq rfl e₁ e₂ e₃ h₁ h₂ hne
      let lam := W.slope x₁ x₂ y₁ (W.negY x₂ y₂)
      let x₃ := W.addX x₁ x₂ lam
      have hA : lam * (x₁ - x₂) = y₁ + y₂ := h_slope.1
      have hB : lam * (y₁ - y₂) =
          (x₁ - e₁) * (x₁ - e₂) + (x₁ - e₁) * (x₂ - e₃) + (x₂ - e₂) * (x₂ - e₃) := h_slope.2
      have heq1 : y₁ ^ 2 = (x₁ - e₁) * (x₁ - e₂) * (x₁ - e₃) := by
        have h0 := (WeierstrassCurve.Affine.equation_iff x₁ y₁).mp h₁.1
        dsimp [threeRootsCurve] at h0
        linear_combination h0
      have he_2m : ∀ {a : F'}, Valued.v a ≤ WithZero.exp (B : ℤ) → Valued.v a ≤ WithZero.exp (2 * m) :=
        fun ha => le_trans ha (WithZero.exp_le_exp.mpr (by omega))
      have he₁_2m : Valued.v e₁ ≤ WithZero.exp (2 * m) := he_2m he₁
      have he₂_2m : Valued.v e₂ ≤ WithZero.exp (2 * m) := he_2m he₂
      have he₃_2m : Valued.v e₃ ≤ WithZero.exp (2 * m) := he_2m he₃
      have hlam_sq_eq : lam * lam = x₃ - (e₁ + e₂ + e₃) + x₁ + x₂ := by
        dsimp [x₃, W, threeRootsCurve, WeierstrassCurve.Affine.addX]
        ring
      have hlam_le : Valued.v lam ≤ WithZero.exp (2 * m) := by
        apply sq_le_sq_imp_le
        rw [← Valuation.map_mul, hlam_sq_eq, ← WithZero.exp_add]
        have h_sum : Valued.v (x₃ - (e₁ + e₂ + e₃) + x₁ + x₂) ≤ WithZero.exp (2 * m) := by
          refine le_trans (Valuation.map_add Valued.v _ _) (max_le ?_ hx₂)
          refine le_trans (Valuation.map_add Valued.v _ _) (max_le ?_ hx₁)
          refine le_trans (Valuation.map_sub Valued.v _ _) (max_le hx₃ ?_)
          refine le_trans (Valuation.map_add Valued.v _ _) (max_le ?_ he₃_2m)
          exact le_trans (Valuation.map_add Valued.v _ _) (max_le he₁_2m he₂_2m)
        exact le_trans h_sum (WithZero.exp_le_exp.mpr (by omega))
      have h2y₁_eq : 2 * y₁ = lam * (x₁ - x₂) + (y₁ - y₂) := by
        linear_combination -hA
      have h2y₁_le : Valued.v (2 * y₁) ≤ WithZero.exp (2 * m - N₀) := by
        rw [h2y₁_eq]
        have h1 : Valued.v (lam * (x₁ - x₂)) ≤ WithZero.exp (2 * m - N₀) := by
          rw [Valuation.map_mul]
          calc
            Valued.v lam * Valued.v (x₁ - x₂) ≤ WithZero.exp (2 * m) * WithZero.exp (-N₀) :=
              mul_le_mul' hlam_le hx_sub
            _ = WithZero.exp (2 * m - N₀) := by
              rw [← WithZero.exp_add]
              congr 1
        have h2 : Valued.v (y₁ - y₂) ≤ WithZero.exp (2 * m - N₀) :=
          le_trans hy_sub (WithZero.exp_le_exp.mpr (by omega))
        exact le_trans (Valuation.map_add Valued.v _ _) (max_le h1 h2)
      let D₁ := (x₁ - e₁) * (x₁ - e₂) + (x₁ - e₁) * (x₁ - e₃) + (x₁ - e₂) * (x₁ - e₃)
      have hD₁_eq : D₁ = lam * (y₁ - y₂) + (x₁ - x₂) * (x₁ + x₁ + x₂ - e₁ - e₂ - e₃) := by
        dsimp [D₁]
        linear_combination -hB
      have hD₁_le : Valued.v D₁ ≤ WithZero.exp (2 * m - N₀) := by
        rw [hD₁_eq]
        have h1 : Valued.v (lam * (y₁ - y₂)) ≤ WithZero.exp (2 * m - N₀) := by
          rw [Valuation.map_mul]
          calc
            Valued.v lam * Valued.v (y₁ - y₂) ≤ WithZero.exp (2 * m) * WithZero.exp (-N₀) :=
              mul_le_mul' hlam_le hy_sub
            _ = WithZero.exp (2 * m - N₀) := by
              rw [← WithZero.exp_add]
              congr 1
        have h_lin : Valued.v (x₁ + x₁ + x₂ - e₁ - e₂ - e₃) ≤ WithZero.exp (2 * m) := by
          refine le_trans (Valuation.map_sub Valued.v _ _) (max_le ?_ he₃_2m)
          refine le_trans (Valuation.map_sub Valued.v _ _) (max_le ?_ he₂_2m)
          refine le_trans (Valuation.map_sub Valued.v _ _) (max_le ?_ he₁_2m)
          refine le_trans (Valuation.map_add Valued.v _ _) (max_le ?_ hx₂)
          exact le_trans (Valuation.map_add Valued.v _ _) (max_le hx₁ hx₁)
        have h2 : Valued.v ((x₁ - x₂) * (x₁ + x₁ + x₂ - e₁ - e₂ - e₃)) ≤ WithZero.exp (2 * m - N₀) := by
          rw [Valuation.map_mul]
          calc
            Valued.v (x₁ - x₂) * Valued.v (x₁ + x₁ + x₂ - e₁ - e₂ - e₃) ≤
                WithZero.exp (-N₀) * WithZero.exp (2 * m) :=
              mul_le_mul' hx_sub h_lin
            _ = WithZero.exp (2 * m - N₀) := by
              rw [← WithZero.exp_add]
              congr 1
              omega
        exact le_trans (Valuation.map_add Valued.v _ _) (max_le h1 h2)
      let S := (e₁ - e₂) * (e₁ - e₃) + (e₂ - e₁) * (e₂ - e₃) + (e₃ - e₁) * (e₃ - e₂)
      let L₁ := x₁ + x₁ + x₁ + e₁ - (e₂ + e₂) - (e₃ + e₃)
      let L₂ := x₁ + x₁ + x₁ - (e₁ + e₁) + e₂ - (e₃ + e₃)
      let L₃ := x₁ + x₁ + x₁ - (e₁ + e₁) - (e₂ + e₂) + e₃
      have h_res : 4 * (e₁ - e₂) ^ 2 * (e₁ - e₃) ^ 2 * (e₂ - e₃) ^ 2 =
          (2 * y₁) * (2 * y₁) * (L₁ * L₂ * L₃) - 4 * (D₁ * D₁) * (D₁ - S) := by
        dsimp [D₁, S, L₁, L₂, L₃]
        linear_combination -4 * (3 * x₁ + e₁ - 2 * e₂ - 2 * e₃) *
          (3 * x₁ - 2 * e₁ + e₂ - 2 * e₃) * (3 * x₁ - 2 * e₁ - 2 * e₂ + e₃) * heq1
      have hL_bound : ∀ a b c : F', Valued.v a ≤ WithZero.exp (2 * m) →
          Valued.v b ≤ WithZero.exp (2 * m) → Valued.v c ≤ WithZero.exp (2 * m) →
          Valued.v (x₁ + x₁ + x₁ + a - (b + b) - (c + c)) ≤ WithZero.exp (2 * m) := by
        intro a b c ha hb hc
        refine le_trans (Valuation.map_sub Valued.v _ _) (max_le ?_
          (le_trans (Valuation.map_add Valued.v c c) (max_le hc hc)))
        refine le_trans (Valuation.map_sub Valued.v _ _) (max_le ?_
          (le_trans (Valuation.map_add Valued.v b b) (max_le hb hb)))
        refine le_trans (Valuation.map_add Valued.v _ _) (max_le ?_ ha)
        refine le_trans (Valuation.map_add Valued.v _ _) (max_le ?_ hx₁)
        exact le_trans (Valuation.map_add Valued.v _ _) (max_le hx₁ hx₁)
      have hL₁_le : Valued.v L₁ ≤ WithZero.exp (2 * m) := hL_bound e₁ e₂ e₃ he₁_2m he₂_2m he₃_2m
      have hL₂_le : Valued.v L₂ ≤ WithZero.exp (2 * m) := by
        have h_eq : L₂ = x₁ + x₁ + x₁ + e₂ - (e₁ + e₁) - (e₃ + e₃) := by dsimp [L₂]; ring
        rw [h_eq]
        exact hL_bound e₂ e₁ e₃ he₂_2m he₁_2m he₃_2m
      have hL₃_le : Valued.v L₃ ≤ WithZero.exp (2 * m) := by
        have h_eq : L₃ = x₁ + x₁ + x₁ + e₃ - (e₁ + e₁) - (e₂ + e₂) := by dsimp [L₃]; ring
        rw [h_eq]
        exact hL_bound e₃ e₁ e₂ he₃_2m he₁_2m he₂_2m
      have hL123_le : Valued.v (L₁ * L₂ * L₃) ≤ WithZero.exp (6 * m) := by
        rw [Valuation.map_mul, Valuation.map_mul]
        calc
          Valued.v L₁ * Valued.v L₂ * Valued.v L₃ ≤
              WithZero.exp (2 * m) * WithZero.exp (2 * m) * WithZero.exp (2 * m) :=
            mul_le_mul' (mul_le_mul' hL₁_le hL₂_le) hL₃_le
          _ = WithZero.exp (6 * m) := by
            rw [← WithZero.exp_add, ← WithZero.exp_add]
            congr 1
            omega
      have hS_le : Valued.v S ≤ WithZero.exp (6 * m) := by
        have h_sub_prod : ∀ {a b c : F'}, Valued.v a ≤ WithZero.exp (2 * m) →
            Valued.v b ≤ WithZero.exp (2 * m) → Valued.v c ≤ WithZero.exp (2 * m) →
            Valued.v ((a - b) * (a - c)) ≤ WithZero.exp (6 * m) := by
          intro a b c ha hb hc
          rw [Valuation.map_mul]
          calc
            Valued.v (a - b) * Valued.v (a - c) ≤
                WithZero.exp (2 * m) * WithZero.exp (2 * m) :=
              mul_le_mul' (le_trans (Valuation.map_sub Valued.v a b) (max_le ha hb))
                (le_trans (Valuation.map_sub Valued.v a c) (max_le ha hc))
            _ ≤ WithZero.exp (6 * m) := by
              rw [← WithZero.exp_add, WithZero.exp_le_exp]
              omega
        dsimp [S]
        refine le_trans (Valuation.map_add Valued.v _ _)
          (max_le ?_ (h_sub_prod he₃_2m he₁_2m he₂_2m))
        exact le_trans (Valuation.map_add Valued.v _ _)
          (max_le (h_sub_prod he₁_2m he₂_2m he₃_2m) (h_sub_prod he₂_2m he₁_2m he₃_2m))
      have h4_le : ∀ u : F', Valued.v (4 * u) ≤ Valued.v u := by
        intro u
        have h4u : 4 * u = (u + u) + (u + u) := by ring
        rw [h4u]
        have h2u : Valued.v (u + u) ≤ Valued.v u :=
          le_trans (Valuation.map_add Valued.v u u) (max_le (le_refl _) (le_refl _))
        exact le_trans (Valuation.map_add Valued.v (u + u) (u + u)) (max_le h2u h2u)
      have h_term1 : Valued.v ((2 * y₁) * (2 * y₁) * (L₁ * L₂ * L₃)) ≤
          WithZero.exp (10 * m - 2 * N₀) := by
        rw [Valuation.map_mul, Valuation.map_mul]
        calc
          Valued.v (2 * y₁) * Valued.v (2 * y₁) * Valued.v (L₁ * L₂ * L₃) ≤
              WithZero.exp (2 * m - N₀) * WithZero.exp (2 * m - N₀) * WithZero.exp (6 * m) :=
            mul_le_mul' (mul_le_mul' h2y₁_le h2y₁_le) hL123_le
          _ = WithZero.exp (10 * m - 2 * N₀) := by
            rw [← WithZero.exp_add, ← WithZero.exp_add]
            congr 1
            omega
      have h_term2 : Valued.v (4 * (D₁ * D₁) * (D₁ - S)) ≤
          WithZero.exp (10 * m - 2 * N₀) := by
        rw [mul_assoc]
        refine le_trans (h4_le _) ?_
        rw [Valuation.map_mul, Valuation.map_mul]
        have hD₁S : Valued.v (D₁ - S) ≤ WithZero.exp (6 * m) := by
          refine le_trans (Valuation.map_sub Valued.v D₁ S) (max_le ?_ hS_le)
          exact le_trans hD₁_le (WithZero.exp_le_exp.mpr (by omega))
        calc
          Valued.v D₁ * Valued.v D₁ * Valued.v (D₁ - S) ≤
              WithZero.exp (2 * m - N₀) * WithZero.exp (2 * m - N₀) * WithZero.exp (6 * m) :=
            mul_le_mul' (mul_le_mul' hD₁_le hD₁_le) hD₁S
          _ = WithZero.exp (10 * m - 2 * N₀) := by
            rw [← WithZero.exp_add, ← WithZero.exp_add]
            congr 1
            omega
      have hΔ_upper : Valued.v ((4 * (e₁ - e₂) ^ 2 * (e₁ - e₃) ^ 2 * (e₂ - e₃) ^ 2 : F')) ≤
          WithZero.exp (10 * m - 2 * N₀) := by
        rw [h_res]
        exact le_trans (Valuation.map_sub Valued.v _ _) (max_le h_term1 h_term2)
      have h_contra : WithZero.exp (-(δ : ℤ)) ≤ WithZero.exp (10 * m - 2 * N₀) :=
        le_trans hΔ hΔ_upper
      rw [WithZero.exp_le_exp] at h_contra
      omega
  have finite_quotient_adicCompletionIntegers_of_ne_zero :
      ∀ (a : ↥(v.adicCompletionIntegers K)), a ≠ 0 →
        Finite (↥(v.adicCompletionIntegers K) ⧸ Ideal.span {a}) :=
    fun a ha => _root_.finite_quotient_adicCompletionIntegers_of_ne_zero v a ha
  let F := v.adicCompletion K
  let R := ↥(v.adicCompletionIntegers K)
  let W := (threeRootsCurve e₁ e₂ e₃).toAffine
  have h_inj : Function.Injective (algebraMap K F) := (algebraMap K F).injective
  haveI : CharZero F := charZero_of_injective_ringHom h_inj
  let c₀ : F := 4 * (e₁ - e₂) ^ 2 * (e₁ - e₃) ^ 2 * (e₂ - e₃) ^ 2
  have hc₀_ne : c₀ ≠ 0 := by
    dsimp [c₀]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 (sub_ne_zero.mpr h₁₂)))
      (pow_ne_zero 2 (sub_ne_zero.mpr h₁₃))) (pow_ne_zero 2 (sub_ne_zero.mpr h₂₃))
  have hvc₀_ne : Valued.v c₀ ≠ 0 := (Valuation.ne_zero_iff Valued.v).mpr hc₀_ne
  rcases WithZero.ne_zero_iff_exists.mp hvc₀_ne with ⟨gc₀, hgc₀⟩
  let zc₀ : ℤ := Multiplicative.toAdd gc₀
  have hzc₀_eq : Valued.v c₀ = WithZero.exp zc₀ := by rw [← hgc₀]; rfl
  let δ : ℕ := (-zc₀).toNat
  have hΔ : WithZero.exp (-(δ : ℤ)) ≤ Valued.v c₀ := by
    rw [hzc₀_eq, WithZero.exp_le_exp]
    omega
  obtain ⟨π_K, hπ_K⟩ := v.valuation_exists_uniformizer K
  let π : F := (π_K : F)
  have hπ_val : Valued.v π = WithZero.exp (-1 : ℤ) := by
    change Valued.v (π_K : F) = WithZero.exp (-1 : ℤ)
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π_K, hπ_K]
  have hπ_pow : ∀ k : ℕ, Valued.v (π ^ k) = WithZero.exp (-(k : ℤ)) := by
    intro k
    induction k with
    | zero => simp [WithZero.exp_zero]
    | succ k ih =>
      rw [pow_succ, Valuation.map_mul, ih, hπ_val, ← WithZero.exp_add]
      congr 1
      omega
  have hπ_mem : π ∈ v.adicCompletionIntegers K := by
    change Valued.v π ≤ 1
    rw [hπ_val, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  let ϖ : R := ⟨π, hπ_mem⟩
  let M : ℕ := m.toNat
  have hM : (M : ℤ) = m := Int.toNat_of_nonneg (by omega)
  let N₀ : ℕ := 5 * M + δ + 1
  let N : ℕ := 3 * M + N₀
  let a : R := ϖ ^ N
  have ha : a ≠ 0 := by
    intro ha0
    have haF : (a : F) = 0 := congr_arg Subtype.val ha0
    have hpow : (a : F) = π ^ N := by
      change ((ϖ ^ N : R) : F) = π ^ N
      rw [Subring.coe_pow]
    rw [hpow] at haF
    have hv0 : Valued.v (π ^ N) = 0 := by rw [haF, Valuation.map_zero]
    rw [hπ_pow N] at hv0
    exact WithZero.exp_pos.ne' hv0
  haveI : Finite (R ⧸ Ideal.span {a}) :=
    finite_quotient_adicCompletionIntegers_of_ne_zero a ha
  let Q := R ⧸ Ideal.span {a}
  let T := Option (Q × Q)
  letI : Fintype T := Fintype.ofFinite T
  let toQuot : F → Q := fun u =>
    if hu : Valued.v (π ^ (3 * M) * u) ≤ 1 then
      Ideal.Quotient.mk (Ideal.span {a}) ⟨π ^ (3 * M) * u, hu⟩
    else 0
  have h_scale_mem : ∀ {u : F}, Valued.v u ≤ WithZero.exp (3 * m) →
      Valued.v (π ^ (3 * M) * u) ≤ 1 := by
    intro u hu
    rw [Valuation.map_mul, hπ_pow (3 * M), ← WithZero.exp_zero]
    calc
      WithZero.exp (-((3 * M : ℕ) : ℤ)) * Valued.v u ≤
          WithZero.exp (-((3 * M : ℕ) : ℤ)) * WithZero.exp (3 * m) :=
        mul_le_mul' (le_refl _) hu
      _ = WithZero.exp 0 := by
        rw [← WithZero.exp_add]
        congr 1
        omega
  have h_toQuot : ∀ {u₁ u₂ : F},
      Valued.v u₁ ≤ WithZero.exp (3 * m) →
      Valued.v u₂ ≤ WithZero.exp (3 * m) →
      toQuot u₁ = toQuot u₂ →
      Valued.v (u₁ - u₂) ≤ WithZero.exp (-(5 * m + (δ : ℤ) + 1)) := by
    intro u₁ u₂ hu₁ hu₂ heq
    have hm1 : Valued.v (π ^ (3 * M) * u₁) ≤ 1 := h_scale_mem hu₁
    have hm2 : Valued.v (π ^ (3 * M) * u₂) ≤ 1 := h_scale_mem hu₂
    dsimp [toQuot] at heq
    rw [dif_pos hm1, dif_pos hm2] at heq
    have h_mem := Ideal.Quotient.eq.mp heq
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp h_mem
    have hzF : π ^ (3 * M) * u₁ - π ^ (3 * M) * u₂ = π ^ N * (z : F) := by
      have h0 : (((⟨π ^ (3 * M) * u₁, hm1⟩ : R) - (⟨π ^ (3 * M) * u₂, hm2⟩ : R) : R) : F) =
          ((a * z : R) : F) := congr_arg Subtype.val hz
      simpa [a, ϖ] using h0
    have h_mul_sub : π ^ (3 * M) * (u₁ - u₂) = π ^ N * (z : F) := by
      linear_combination hzF
    have h_val_eq : WithZero.exp (-((3 * M : ℕ) : ℤ)) * Valued.v (u₁ - u₂) ≤
        WithZero.exp (-(N : ℤ)) := by
      rw [← hπ_pow (3 * M), ← Valuation.map_mul, h_mul_sub, Valuation.map_mul, hπ_pow N]
      calc
        WithZero.exp (-(N : ℤ)) * Valued.v (z : F) ≤
            WithZero.exp (-(N : ℤ)) * 1 := mul_le_mul' (le_refl _) z.property
        _ = WithZero.exp (-(N : ℤ)) := mul_one _
    have h_mul := mul_le_mul' (le_refl (WithZero.exp ((3 * M : ℕ) : ℤ))) h_val_eq
    have h_lhs : WithZero.exp ((3 * M : ℕ) : ℤ) *
        (WithZero.exp (-((3 * M : ℕ) : ℤ)) * Valued.v (u₁ - u₂)) = Valued.v (u₁ - u₂) := by
      rw [← mul_assoc, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero, one_mul]
    have h_rhs : WithZero.exp ((3 * M : ℕ) : ℤ) * WithZero.exp (-(N : ℤ)) =
        WithZero.exp (-(5 * m + (δ : ℤ) + 1)) := by
      rw [← WithZero.exp_add]
      congr 1
      omega
    rwa [h_lhs, h_rhs] at h_mul
  let g : W.Point → T := fun P =>
    if P ∈ lutzSet e₁ e₂ e₃ m then none
    else
      match P with
      | WeierstrassCurve.Affine.Point.zero => none
      | WeierstrassCurve.Affine.Point.some (x := x) (y := y) _ => some (toQuot x, toQuot y)
  refine ⟨Fintype.card T, fun P => Fintype.equivFin T (g P), ?_⟩
  intro P₁ P₂ hf
  have hg : g P₁ = g P₂ := (Fintype.equivFin T).injective hf
  by_cases hP₁ : P₁ ∈ lutzSet e₁ e₂ e₃ m
  · have hg₁ : g P₁ = none := if_pos hP₁
    have hP₂ : P₂ ∈ lutzSet e₁ e₂ e₃ m := by
      by_contra hP₂
      cases P₂ with
      | zero => exact hP₂ trivial
      | @some x₂ y₂ h₂ =>
        have hg₂ : g (WeierstrassCurve.Affine.Point.some h₂) = some (toQuot x₂, toQuot y₂) :=
          if_neg hP₂
        rw [hg₁, hg₂] at hg
        cases hg
    have h_neg_P₂ : -P₂ ∈ lutzSet e₁ e₂ e₃ m := by
      cases P₂ with
      | zero => exact trivial
      | @some x₂ y₂ h₂ =>
        rw [WeierstrassCurve.Affine.Point.neg_some]
        exact hP₂
    rw [sub_eq_add_neg]
    exact ((lutzSet_add_mem_and_param e₁ e₂ e₃ B m hm he₁ he₂ he₃).1 P₁ (-P₂) hP₁ h_neg_P₂).1
  · cases P₁ with
    | zero => exact False.elim (hP₁ trivial)
    | @some x₁ y₁ h₁ =>
      have hg₁ : g (WeierstrassCurve.Affine.Point.some h₁) = some (toQuot x₁, toQuot y₁) :=
        if_neg hP₁
      have hP₂ : P₂ ∉ lutzSet e₁ e₂ e₃ m := by
        intro hP₂
        have hg₂ : g P₂ = none := if_pos hP₂
        rw [hg₁, hg₂] at hg
        cases hg
      cases P₂ with
      | zero => exact False.elim (hP₂ trivial)
      | @some x₂ y₂ h₂ =>
        have hg₂ : g (WeierstrassCurve.Affine.Point.some h₂) = some (toQuot x₂, toQuot y₂) :=
          if_neg hP₂
        rw [hg₁, hg₂, Option.some.injEq, Prod.mk.injEq] at hg
        rcases not_mem_lutzSet_val_le rfl e₁ e₂ e₃ B m hm he₁ he₂ he₃ h₁ hP₁ with
          ⟨_, _, hx₁_2m, hy₁_3m⟩
        rcases not_mem_lutzSet_val_le rfl e₁ e₂ e₃ B m hm he₁ he₂ he₃ h₂ hP₂ with
          ⟨_, _, hx₂_2m, hy₂_3m⟩
        have hx₁_3m : Valued.v x₁ ≤ WithZero.exp (3 * m) :=
          le_trans hx₁_2m (WithZero.exp_le_exp.mpr (by omega))
        have hx₂_3m : Valued.v x₂ ≤ WithZero.exp (3 * m) :=
          le_trans hx₂_2m (WithZero.exp_le_exp.mpr (by omega))
        have hx_sub := h_toQuot hx₁_3m hx₂_3m hg.1
        have hy_sub := h_toQuot hy₁_3m hy₂_3m hg.2
        exact sub_mem_lutzSet_of_val_le_of_sub_le rfl e₁ e₂ e₃ B δ m hm he₁ he₂ he₃ hΔ h₁ h₂
          hx₁_2m hx₂_2m hx_sub hy_sub
theorem valBall_relIndex_eq_card_quotient_span_two {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (m : ℤ) (e : ℕ)
    (he : Valued.v (2 : v.adicCompletion K) = WithZero.exp (-(e : ℤ))) :
    (valBall (v.adicCompletion K) (m + (e : ℤ))).relIndex (valBall (v.adicCompletion K) m) =
      Nat.card (↥(v.adicCompletionIntegers K) ⧸
        Ideal.span {(2 : ↥(v.adicCompletionIntegers K))}) :=
by
  have h_gen : ∀ {R : Type _} (_ : (R = K) = (R = K)) [CommRing R]
      (ψ₀ : valBall (v.adicCompletion K) m →+ R)
      (H : AddSubgroup (valBall (v.adicCompletion K) m))
      (h_surj : Function.Surjective ψ₀)
      (h_ker : ∀ x : valBall (v.adicCompletion K) m, (2 : R) ∣ ψ₀ x ↔ x ∈ H),
      H.index = Nat.card (R ⧸ Ideal.span {(2 : R)}) := by
    intro R _ _ ψ₀ H h_surj h_ker
    let I : Ideal R := Ideal.span {(2 : R)}
    let ψ : valBall (v.adicCompletion K) m →+ R ⧸ I :=
      (Ideal.Quotient.mk I).toAddMonoidHom.comp ψ₀
    have hψ_surj : Function.Surjective ψ :=
      (Ideal.Quotient.mk_surjective).comp h_surj
    have hψ_ker : ψ.ker = H := by
      ext x
      rw [AddMonoidHom.mem_ker]
      change Ideal.Quotient.mk I (ψ₀ x) = 0 ↔ x ∈ H
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact h_ker x
    rw [AddSubgroup.index_eq_card, ← hψ_ker]
    exact Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective ψ hψ_surj).toEquiv
  obtain ⟨π_K, hπ_K⟩ := v.valuation_exists_uniformizer K
  let π : v.adicCompletion K := (π_K : v.adicCompletion K)
  have hπ : Valued.v π = WithZero.exp (-1 : ℤ) := by
    change Valued.v (π_K : v.adicCompletion K) = WithZero.exp (-1 : ℤ)
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π_K, hπ_K]
  let c : v.adicCompletion K := π ^ m
  have hc_val : Valued.v c = WithZero.exp (-m) := by
    change Valued.v (π ^ m) = WithZero.exp (-m)
    rw [map_zpow₀, hπ, ← WithZero.exp_zsmul, zsmul_eq_mul, mul_neg_one, Int.cast_id]
  have hc_inv_val : Valued.v c⁻¹ = WithZero.exp m := by
    rw [map_inv₀, hc_val, ← WithZero.exp_neg, neg_neg]
  have hc₀ : c ≠ 0 := by
    rw [← Valuation.ne_zero_iff Valued.v, hc_val]
    exact WithZero.coe_ne_zero
  have h2₀ : (2 : v.adicCompletion K) ≠ 0 := by
    rw [← Valuation.ne_zero_iff Valued.v, he]
    exact WithZero.coe_ne_zero
  have h2_inv_val : Valued.v (2 : v.adicCompletion K)⁻¹ = WithZero.exp (e : ℤ) := by
    rw [map_inv₀, he, ← WithZero.exp_neg, neg_neg]
  have h_mem : ∀ x : valBall (v.adicCompletion K) m, c⁻¹ * x.1 ∈ v.adicCompletionIntegers K := by
    intro x
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    have hx : Valued.v x.1 ≤ WithZero.exp (-m) := x.2
    rw [Valuation.map_mul, hc_inv_val]
    calc
      WithZero.exp m * Valued.v x.1 ≤ WithZero.exp m * WithZero.exp (-m) :=
        mul_le_mul_right hx (WithZero.exp m)
      _ = 1 := by
        rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  let ψ₀ : valBall (v.adicCompletion K) m →+ ↥(v.adicCompletionIntegers K) :=
    { toFun := fun x => ⟨c⁻¹ * x.1, h_mem x⟩
      map_zero' := by ext; exact mul_zero c⁻¹
      map_add' := by intro x y; ext; exact mul_add c⁻¹ x.1 y.1 }
  have hψ₀_surj : Function.Surjective ψ₀ := by
    intro y
    have hy : Valued.v y.1 ≤ 1 := by
      rw [← IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      exact y.2
    have hx₀ : c * y.1 ∈ valBall (v.adicCompletion K) m := by
      change Valued.v (c * y.1) ≤ WithZero.exp (-m)
      rw [Valuation.map_mul, hc_val]
      calc
        WithZero.exp (-m) * Valued.v y.1 ≤ WithZero.exp (-m) * 1 :=
          mul_le_mul_right hy (WithZero.exp (-m))
        _ = WithZero.exp (-m) := mul_one _
    refine ⟨⟨c * y.1, hx₀⟩, ?_⟩
    ext
    exact inv_mul_cancel_left₀ hc₀ y.1
  refine h_gen rfl ψ₀ ((valBall (v.adicCompletion K) (m + (e : ℤ))).addSubgroupOf (valBall (v.adicCompletion K) m)) hψ₀_surj (fun x => ?_)
  rw [AddSubgroup.mem_addSubgroupOf]
  constructor
  · rintro ⟨z, hz⟩
    have hz_eq : c⁻¹ * x.1 = (2 : v.adicCompletion K) * z.1 := congr_arg Subtype.val hz
    have hx_eq : x.1 = c * ((2 : v.adicCompletion K) * z.1) := by
      rw [← hz_eq, mul_inv_cancel_left₀ hc₀]
    have hz_val : Valued.v z.1 ≤ 1 := by
      rw [← IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      exact z.2
    change Valued.v x.1 ≤ WithZero.exp (-(m + (e : ℤ)))
    rw [hx_eq, Valuation.map_mul, Valuation.map_mul, hc_val, he]
    have h2z : WithZero.exp (-(e : ℤ)) * Valued.v z.1 ≤ WithZero.exp (-(e : ℤ)) := by
      calc
        WithZero.exp (-(e : ℤ)) * Valued.v z.1 ≤ WithZero.exp (-(e : ℤ)) * 1 :=
          mul_le_mul_right hz_val (WithZero.exp (-(e : ℤ)))
        _ = WithZero.exp (-(e : ℤ)) := mul_one _
    calc
      WithZero.exp (-m) * (WithZero.exp (-(e : ℤ)) * Valued.v z.1) ≤
          WithZero.exp (-m) * WithZero.exp (-(e : ℤ)) :=
        mul_le_mul_right h2z (WithZero.exp (-m))
      _ = WithZero.exp (-(m + (e : ℤ))) := by
        rw [← WithZero.exp_add]
        congr 1
        omega
  · intro hx
    have hx' : Valued.v x.1 ≤ WithZero.exp (-(m + (e : ℤ))) := hx
    have hz₀ : (2 : v.adicCompletion K)⁻¹ * (c⁻¹ * x.1) ∈ v.adicCompletionIntegers K := by
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      rw [Valuation.map_mul, Valuation.map_mul, h2_inv_val, hc_inv_val]
      have hcx : WithZero.exp m * Valued.v x.1 ≤ WithZero.exp m * WithZero.exp (-(m + (e : ℤ))) :=
        mul_le_mul_right hx' (WithZero.exp m)
      calc
        WithZero.exp (e : ℤ) * (WithZero.exp m * Valued.v x.1) ≤
            WithZero.exp (e : ℤ) * (WithZero.exp m * WithZero.exp (-(m + (e : ℤ)))) :=
          mul_le_mul_right hcx (WithZero.exp (e : ℤ))
        _ = 1 := by
          rw [← WithZero.exp_add, ← WithZero.exp_add]
          have h_zero : (e : ℤ) + (m + -(m + (e : ℤ))) = 0 := by omega
          rw [h_zero, WithZero.exp_zero]
    refine ⟨⟨(2 : v.adicCompletion K)⁻¹ * (c⁻¹ * x.1), hz₀⟩, ?_⟩
    ext
    change c⁻¹ * x.1 = (2 : v.adicCompletion K) * ((2 : v.adicCompletion K)⁻¹ * (c⁻¹ * x.1))
    exact (mul_inv_cancel_left₀ h2₀ (c⁻¹ * x.1)).symm

theorem card_point_mod_two_adicCompletion_eq {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    [DecidableEq (v.adicCompletion K)]
    (e₁ e₂ e₃ : v.adicCompletion K) (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃) :
    Nat.card ((threeRootsCurve e₁ e₂ e₃).toAffine.Point ⧸
        (AddMonoidHom.id (threeRootsCurve e₁ e₂ e₃).toAffine.Point +
         AddMonoidHom.id (threeRootsCurve e₁ e₂ e₃).toAffine.Point).range) =
      Nat.card (AddMonoidHom.id (threeRootsCurve e₁ e₂ e₃).toAffine.Point +
                AddMonoidHom.id (threeRootsCurve e₁ e₂ e₃).toAffine.Point).ker *
      Nat.card (↥(v.adicCompletionIntegers K) ⧸
        Ideal.span {(2 : ↥(v.adicCompletionIntegers K))}) :=
by
  have h_abstract : ∀ {F : Type _} (_ : (F = K) = (F = K)) [Field F] [CharZero F] [DecidableEq F]
      [Valued F (WithZero (Multiplicative ℤ))]
      (e₁ e₂ e₃ : F) (B e : ℕ) (m : ℤ) (hm : (B : ℤ) + (e : ℤ) + 2 ≤ m)
      (he₁ : Valued.v e₁ ≤ WithZero.exp (B : ℤ))
      (he₂ : Valued.v e₂ ≤ WithZero.exp (B : ℤ))
      (he₃ : Valued.v e₃ ≤ WithZero.exp (B : ℤ))
      (he : Valued.v (2 : F) = WithZero.exp (-(e : ℤ)))
      (h_param : ∀ t ∈ valBall F m,
        ∃ P ∈ lutzSet e₁ e₂ e₃ m, lutzParam P - t ∈ valBall F (m + (e : ℤ)))
      (h_half : ∀ P ∈ lutzSet e₁ e₂ e₃ (m + (e : ℤ)),
        ∃ Q ∈ lutzSet e₁ e₂ e₃ m, Q + Q = P)
      (h_fin : ∃ (n : ℕ) (f : (threeRootsCurve e₁ e₂ e₃).toAffine.Point → Fin n),
        ∀ P Q : (threeRootsCurve e₁ e₂ e₃).toAffine.Point,
          f P = f Q → P - Q ∈ lutzSet e₁ e₂ e₃ m),
      Nat.card ((threeRootsCurve e₁ e₂ e₃).toAffine.Point ⧸
          (AddMonoidHom.id (threeRootsCurve e₁ e₂ e₃).toAffine.Point +
           AddMonoidHom.id (threeRootsCurve e₁ e₂ e₃).toAffine.Point).range) =
        Nat.card (AddMonoidHom.id (threeRootsCurve e₁ e₂ e₃).toAffine.Point +
                  AddMonoidHom.id (threeRootsCurve e₁ e₂ e₃).toAffine.Point).ker *
        (valBall F (m + (e : ℤ))).relIndex (valBall F m) := by
    intro F _ _ _ _ _ e₁ e₂ e₃ B e m hm he₁ he₂ he₃ he h_param h_half h_fin
    let W := (threeRootsCurve e₁ e₂ e₃).toAffine
    let d : W.Point →+ W.Point := AddMonoidHom.id W.Point + AddMonoidHom.id W.Point
    have hm1 : (B : ℤ) + 1 ≤ m := by omega
    have hme1 : (B : ℤ) + 1 ≤ m + (e : ℤ) := by omega
    have h_lutz_m := lutzSet_add_mem_and_param e₁ e₂ e₃ B m hm1 he₁ he₂ he₃
    have h_lutz_me := lutzSet_add_mem_and_param e₁ e₂ e₃ B (m + (e : ℤ)) hme1 he₁ he₂ he₃
    have h_neg : ∀ (k : ℤ) (P : W.Point), P ∈ lutzSet e₁ e₂ e₃ k → -P ∈ lutzSet e₁ e₂ e₃ k := by
      intro k P hP
      cases P with
      | zero => exact trivial
      | @some x y h =>
        rw [WeierstrassCurve.Affine.Point.neg_some]
        exact hP
    let Hm : AddSubgroup W.Point :=
      { carrier := lutzSet e₁ e₂ e₃ m
        add_mem' := fun {P Q} hP hQ => (h_lutz_m.1 P Q hP hQ).1
        zero_mem' := trivial
        neg_mem' := fun {P} hP => h_neg m P hP }
    let Hme : AddSubgroup W.Point :=
      { carrier := lutzSet e₁ e₂ e₃ (m + (e : ℤ))
        add_mem' := fun {P Q} hP hQ => (h_lutz_me.1 P Q hP hQ).1
        zero_mem' := trivial
        neg_mem' := fun {P} hP => h_neg (m + (e : ℤ)) P hP }
    have hHme_le : Hme ≤ Hm := by
      intro P hP
      cases P with
      | zero => exact trivial
      | @some x y h =>
        exact le_trans (WithZero.exp_le_exp.mpr (by omega)) hP
    have h_valBall_le : ∀ {k₁ k₂ : ℤ}, k₁ ≤ k₂ → valBall F k₂ ≤ valBall F k₁ := by
      intro k₁ k₂ hk x hx
      exact le_trans hx (WithZero.exp_le_exp.mpr (by omega))
    have h_two_mul_mem : ∀ {k : ℤ} {x : F}, x ∈ valBall F k → 2 * x ∈ valBall F (k + (e : ℤ)) := by
      intro k x hx
      change Valued.v (2 * x) ≤ WithZero.exp (-(k + (e : ℤ)))
      rw [Valuation.map_mul, he]
      calc
        WithZero.exp (-(e : ℤ)) * Valued.v x ≤
            WithZero.exp (-(e : ℤ)) * WithZero.exp (-k) :=
          mul_le_mul_right hx (WithZero.exp (-(e : ℤ)))
        _ = WithZero.exp (-(k + (e : ℤ))) := by
          rw [← WithZero.exp_add]
          congr 1
          omega
    have h_two_div_mem : ∀ {k : ℤ} {x : F}, 2 * x ∈ valBall F (k + (e : ℤ)) → x ∈ valBall F k := by
      intro k x hx
      change Valued.v x ≤ WithZero.exp (-k)
      have hx' : WithZero.exp (-(e : ℤ)) * Valued.v x ≤ WithZero.exp (-(k + (e : ℤ))) := by
        rwa [← he, ← Valuation.map_mul]
      have h_mul := mul_le_mul_right hx' (WithZero.exp (e : ℤ))
      have h_lhs : WithZero.exp (e : ℤ) * (WithZero.exp (-(e : ℤ)) * Valued.v x) = Valued.v x := by
        rw [← mul_assoc, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero, one_mul]
      have h_rhs : WithZero.exp (e : ℤ) * WithZero.exp (-(k + (e : ℤ))) = WithZero.exp (-k) := by
        rw [← WithZero.exp_add]
        congr 1
        omega
      rwa [h_lhs, h_rhs] at h_mul
    have h_disj : Hm ⊓ d.ker = ⊥ := by
      rw [eq_bot_iff]
      intro P ⟨hPm, hPker⟩
      change P ∈ (⊥ : AddSubgroup W.Point)
      rw [AddSubgroup.mem_bot]
      have hPP : P + P = 0 := by
        simpa [d] using AddMonoidHom.mem_ker.mp hPker
      have hP_all : ∀ n : ℕ, P ∈ lutzSet e₁ e₂ e₃ (m + (n : ℤ)) := by
        intro n
        induction n with
        | zero => simpa using hPm
        | succ n ih =>
          have hk : (B : ℤ) + 1 ≤ m + (n : ℤ) := by omega
          have hl := (lutzSet_add_mem_and_param e₁ e₂ e₃ B (m + (n : ℤ)) hk he₁ he₂ he₃)
          have hdiff := (hl.1 P P ih ih).2
          rw [hPP] at hdiff
          have hdiff0 : lutzParam (0 : W.Point) - (lutzParam P + lutzParam P) = -(2 * lutzParam P) := by
            change (0 : F) - (lutzParam P + lutzParam P) = -(2 * lutzParam P)
            ring
          rw [hdiff0] at hdiff
          have h2t : 2 * lutzParam P ∈ valBall F (2 * (m + (n : ℤ))) := by
            simpa using (valBall F (2 * (m + (n : ℤ)))).neg_mem hdiff
          have h2t' : 2 * lutzParam P ∈ valBall F ((m + ((n + 1 : ℕ) : ℤ)) + (e : ℤ)) :=
            h_valBall_le (by omega) h2t
          have ht : lutzParam P ∈ valBall F (m + ((n + 1 : ℕ) : ℤ)) := h_two_div_mem h2t'
          exact (hl.2 P ih (m + ((n + 1 : ℕ) : ℤ)) (by omega)).mpr ht
      cases P with
      | zero => rfl
      | @some x y h =>
        rcases eq_or_ne (Valued.v x) 0 with hx0 | hx0
        · have h0 := hP_all 0
          change WithZero.exp (2 * (m + (0 : ℤ))) ≤ Valued.v x at h0
          rw [hx0] at h0
          exact False.elim (not_lt_of_ge h0 WithZero.exp_pos)
        · rcases WithZero.ne_zero_iff_exists.mp hx0 with ⟨g, hg⟩
          let z : ℤ := Multiplicative.toAdd g
          have hz : Valued.v x = WithZero.exp z := by
            rw [← hg]
            rfl
          let n : ℕ := z.toNat
          have hn := hP_all n
          change WithZero.exp (2 * (m + (n : ℤ))) ≤ Valued.v x at hn
          rw [hz, WithZero.exp_le_exp] at hn
          omega
    have h_map : AddSubgroup.map d Hm = Hme := by
      ext P
      constructor
      · rintro ⟨Q, hQm, rfl⟩
        have hQQ := h_lutz_m.1 Q Q hQm hQm
        have hQ_param : lutzParam Q ∈ valBall F m := (h_lutz_m.2 Q hQm m (le_refl m)).mp hQm
        have h2Q_param : 2 * lutzParam Q ∈ valBall F (m + (e : ℤ)) := h_two_mul_mem hQ_param
        have hdiff : lutzParam (Q + Q) - 2 * lutzParam Q ∈ valBall F (m + (e : ℤ)) := by
          have h1 : lutzParam (Q + Q) - (lutzParam Q + lutzParam Q) ∈ valBall F (m + (e : ℤ)) :=
            h_valBall_le (by omega) hQQ.2
          have h2 : lutzParam Q + lutzParam Q = 2 * lutzParam Q := by ring
          rwa [h2] at h1
        have h_sum := (valBall F (m + (e : ℤ))).add_mem hdiff h2Q_param
        rw [sub_add_cancel] at h_sum
        exact (h_lutz_m.2 (Q + Q) hQQ.1 (m + (e : ℤ)) (by omega)).mpr h_sum
      · intro hPme
        rcases h_half P hPme with ⟨Q, hQm, hQQ⟩
        exact ⟨Q, hQm, hQQ⟩
    let Vm := valBall F m
    let Vme := (valBall F (m + (e : ℤ))).addSubgroupOf Vm
    have h_param_mem : ∀ P : Hm, lutzParam P.1 ∈ Vm := by
      intro P
      exact (h_lutz_m.2 P.1 P.2 m (le_refl m)).mp P.2
    let φ : Hm →+ Vm ⧸ Vme :=
      { toFun := fun P => QuotientAddGroup.mk ⟨lutzParam P.1, h_param_mem P⟩
        map_zero' := by
          rw [QuotientAddGroup.eq_zero_iff]
          exact (valBall F (m + (e : ℤ))).zero_mem
        map_add' := by
          intro P Q
          rw [← QuotientAddGroup.mk_add, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
          change -lutzParam (P.1 + Q.1) + (lutzParam P.1 + lutzParam Q.1) ∈ valBall F (m + (e : ℤ))
          have h_eq : -lutzParam (P.1 + Q.1) + (lutzParam P.1 + lutzParam Q.1) =
              -(lutzParam (P.1 + Q.1) - (lutzParam P.1 + lutzParam Q.1)) := by ring
          rw [h_eq]
          refine (valBall F (m + (e : ℤ))).neg_mem ?_
          exact h_valBall_le (by omega) (h_lutz_m.1 P.1 Q.1 P.2 Q.2).2 }
    have hφ_surj : Function.Surjective φ := by
      intro q
      refine Quotient.inductionOn' q (fun t => ?_)
      rcases h_param t.1 t.2 with ⟨P, hPm, hPt⟩
      refine ⟨⟨P, hPm⟩, ?_⟩
      change QuotientAddGroup.mk ⟨lutzParam P, _⟩ = QuotientAddGroup.mk t
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      change -lutzParam P + t.1 ∈ valBall F (m + (e : ℤ))
      have h_eq : -lutzParam P + t.1 = -(lutzParam P - t.1) := by ring
      rw [h_eq]
      exact (valBall F (m + (e : ℤ))).neg_mem hPt
    have hφ_ker : φ.ker = Hme.addSubgroupOf Hm := by
      ext P
      rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
      change (QuotientAddGroup.mk (⟨lutzParam P.1, h_param_mem P⟩ : Vm) : Vm ⧸ Vme) = 0 ↔ P.1 ∈ Hme
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      exact (h_lutz_m.2 P.1 P.2 (m + (e : ℤ)) (by omega)).symm
    have h_relIndex_eq : Hme.relIndex Hm = (valBall F (m + (e : ℤ))).relIndex (valBall F m) := by
      dsimp [AddSubgroup.relIndex, AddSubgroup.index]
      rw [← hφ_ker]
      exact Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hφ_surj).toEquiv
    rcases h_fin with ⟨n, f, hf⟩
    have h_inj_quot : Function.Injective (fun c : W.Point ⧸ Hm => f (Quotient.out c)) := by
      intro c₁ c₂ hc
      have hdiff : Quotient.out c₁ - Quotient.out c₂ ∈ Hm := hf _ _ hc
      have hdiff' : -(Quotient.out c₁) + Quotient.out c₂ ∈ Hm := by
        have : -(Quotient.out c₁) + Quotient.out c₂ = -(Quotient.out c₁ - Quotient.out c₂) := by
          abel
        rw [this]
        exact Hm.neg_mem hdiff
      have heq : (QuotientAddGroup.mk (Quotient.out c₁) : W.Point ⧸ Hm) =
          QuotientAddGroup.mk (Quotient.out c₂) :=
        QuotientAddGroup.eq.mpr hdiff'
      simpa [Quotient.out_eq] using heq
    haveI : Finite (W.Point ⧸ Hm) := Finite.of_injective _ h_inj_quot
    have hHm_ne_zero : Hm.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
    have h1 : Hme.relIndex Hm * Hm.index = (Hm ⊔ d.ker).index * d.range.index := by
      rw [AddSubgroup.relIndex_mul_index hHme_le, ← h_map, AddSubgroup.index_map]
    have h2 : Hm.relIndex (Hm ⊔ d.ker) = Nat.card d.ker := by
      rw [AddSubgroup.relIndex_sup_left, ← AddSubgroup.inf_relIndex_right, h_disj,
          AddSubgroup.relIndex_bot_left]
    have h3 : Nat.card d.ker * (Hm ⊔ d.ker).index = Hm.index := by
      rw [← h2, AddSubgroup.relIndex_mul_index le_sup_left]
    have h4 : Hm.index * d.range.index = Hm.index * (Nat.card d.ker * Hme.relIndex Hm) := by
      calc
        Hm.index * d.range.index = (Nat.card d.ker * (Hm ⊔ d.ker).index) * d.range.index := by
          rw [h3]
        _ = Nat.card d.ker * ((Hm ⊔ d.ker).index * d.range.index) := by ring
        _ = Nat.card d.ker * (Hme.relIndex Hm * Hm.index) := by rw [← h1]
        _ = Hm.index * (Nat.card d.ker * Hme.relIndex Hm) := by ring
    have h5 : d.range.index = Nat.card d.ker * Hme.relIndex Hm :=
      mul_left_cancel₀ hHm_ne_zero h4
    rw [← AddSubgroup.index_eq_card, h5, h_relIndex_eq]
  have h_inj : Function.Injective (algebraMap K (v.adicCompletion K)) :=
    (algebraMap K (v.adicCompletion K)).injective
  haveI : CharZero (v.adicCompletion K) := charZero_of_injective_ringHom h_inj
  have h_bound : ∀ x : v.adicCompletion K, ∃ b : ℕ, Valued.v x ≤ WithZero.exp (b : ℤ) := by
    intro x
    rcases eq_or_ne (Valued.v x) 0 with hx0 | hx0
    · refine ⟨0, ?_⟩
      rw [hx0]
      exact zero_le'
    · rcases WithZero.ne_zero_iff_exists.mp hx0 with ⟨g, hg⟩
      let z : ℤ := Multiplicative.toAdd g
      refine ⟨z.toNat, ?_⟩
      rw [← hg]
      exact WithZero.exp_le_exp.mpr (Int.self_le_toNat z)
  rcases h_bound e₁ with ⟨b₁, hb₁⟩
  rcases h_bound e₂ with ⟨b₂, hb₂⟩
  rcases h_bound e₃ with ⟨b₃, hb₃⟩
  let B : ℕ := max b₁ (max b₂ b₃)
  have he₁ : Valued.v e₁ ≤ WithZero.exp (B : ℤ) :=
    le_trans hb₁ (WithZero.exp_le_exp.mpr (by omega))
  have he₂ : Valued.v e₂ ≤ WithZero.exp (B : ℤ) :=
    le_trans hb₂ (WithZero.exp_le_exp.mpr (by omega))
  have he₃ : Valued.v e₃ ≤ WithZero.exp (B : ℤ) :=
    le_trans hb₃ (WithZero.exp_le_exp.mpr (by omega))
  have h2_ne : (2 : v.adicCompletion K) ≠ 0 := two_ne_zero
  have hv2_ne : Valued.v (2 : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff Valued.v).mpr h2_ne
  have hv2_le_one : Valued.v (2 : v.adicCompletion K) ≤ WithZero.exp (0 : ℤ) := by
    rw [WithZero.exp_zero]
    have h2_eq : (2 : v.adicCompletion K) = 1 + 1 := one_add_one_eq_two.symm
    rw [h2_eq]
    refine le_trans (Valuation.map_add Valued.v 1 1) ?_
    simp [Valuation.map_one]
  rcases WithZero.ne_zero_iff_exists.mp hv2_ne with ⟨g₂, hg₂⟩
  let z₂ : ℤ := Multiplicative.toAdd g₂
  have hz₂_eq : Valued.v (2 : v.adicCompletion K) = WithZero.exp z₂ := by
    rw [← hg₂]
    rfl
  have hz₂_le : z₂ ≤ 0 := by
    rw [hz₂_eq, WithZero.exp_le_exp] at hv2_le_one
    exact hv2_le_one
  let e : ℕ := (-z₂).toNat
  have he : Valued.v (2 : v.adicCompletion K) = WithZero.exp (-(e : ℤ)) := by
    rw [hz₂_eq]
    congr 1
    omega
  let m : ℤ := (B : ℤ) + (e : ℤ) + 2
  have hm : (B : ℤ) + (e : ℤ) + 2 ≤ m := le_refl m
  have hm1 : (B : ℤ) + 1 ≤ m := by omega
  have h_halving := lutzSet_halving_and_param_exists v e₁ e₂ e₃ h₁₂ h₁₃ h₂₃ B e m hm he₁ he₂ he₃ he
  have h_fin := lutzSet_finite_index_adicCompletion v e₁ e₂ e₃ h₁₂ h₁₃ h₂₃ B m hm1 he₁ he₂ he₃
  have h_eq := h_abstract rfl e₁ e₂ e₃ B e m hm he₁ he₂ he₃ he h_halving.1 h_halving.2 h_fin
  rw [h_eq, valBall_relIndex_eq_card_quotient_span_two v m e he]

theorem proposition_4_1 {K : Type u} [Field K] [NumberField K]
    (e₁ e₂ e₃ : K) (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Set.ncard { c : SqCl (v.adicCompletion K) × SqCl (v.adicCompletion K) |
        ∃ d₁ d₂ : (v.adicCompletion K)ˣ,
          c = (sqCl d₁, sqCl d₂) ∧
          IsDescentClass (algebraMap K (v.adicCompletion K) e₁)
            (algebraMap K (v.adicCompletion K) e₂)
            (algebraMap K (v.adicCompletion K) e₃)
            ((d₁ : v.adicCompletion K)) ((d₂ : v.adicCompletion K)) }
      = Nat.card (SqCl (v.adicCompletion K)) :=
by
  classical
  have h_torsion_gen : ∀ {F : Type u} [Field F] [CharZero F] [DecidableEq F]
      (e₁ e₂ e₃ : F) (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃),
      Nat.card (AddMonoidHom.id (threeRootsCurve e₁ e₂ e₃).toAffine.Point +
                AddMonoidHom.id (threeRootsCurve e₁ e₂ e₃).toAffine.Point).ker = 4 := by
    intro F _ _ _ e₁ e₂ e₃ h₁₂ h₁₃ h₂₃
    let W := (threeRootsCurve e₁ e₂ e₃).toAffine
    have h_eq_iff : ∀ x y : F, W.Equation x y ↔ y ^ 2 = (x - e₁) * (x - e₂) * (x - e₃) := by
      intro x y
      rw [WeierstrassCurve.Affine.equation_iff]
      dsimp [W, threeRootsCurve]
      constructor <;> intro h <;> linear_combination h
    have h_ns_iff : ∀ x y : F, W.Nonsingular x y ↔ y ^ 2 = (x - e₁) * (x - e₂) * (x - e₃) := by
      intro x y
      rw [WeierstrassCurve.Affine.nonsingular_iff, h_eq_iff]
      dsimp [W, threeRootsCurve]
      refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
      by_cases hy : y = 0
      · left
        intro hx
        have h0 : (x - e₁) * (x - e₂) * (x - e₃) = 0 := by linear_combination -h + y * hy
        rcases mul_eq_zero.mp h0 with h12 | h3
        · rcases mul_eq_zero.mp h12 with h1 | h2
          · have hx1 : e₁ = x := (sub_eq_zero.mp h1).symm
            subst hx1
            apply h₁₂
            apply sub_eq_zero.mp
            have : (e₁ - e₂) * (e₁ - e₃) = 0 := by linear_combination -hx
            exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr h₁₃)
          · have hx2 : e₂ = x := (sub_eq_zero.mp h2).symm
            subst hx2
            apply h₁₂.symm
            apply sub_eq_zero.mp
            have : (e₂ - e₁) * (e₂ - e₃) = 0 := by linear_combination -hx
            exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr h₂₃)
        · have hx3 : e₃ = x := (sub_eq_zero.mp h3).symm
          subst hx3
          apply h₁₃.symm
          apply sub_eq_zero.mp
          have : (e₃ - e₁) * (e₃ - e₂) = 0 := by linear_combination -hx
          exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr h₂₃.symm)
      · right
        intro hy'
        apply hy
        have : (2 : F) * y = 0 := by linear_combination hy'
        exact (mul_eq_zero.mp this).resolve_left two_ne_zero
    have hns1 : W.Nonsingular e₁ 0 := (h_ns_iff e₁ 0).mpr (by ring)
    have hns2 : W.Nonsingular e₂ 0 := (h_ns_iff e₂ 0).mpr (by ring)
    have hns3 : W.Nonsingular e₃ 0 := (h_ns_iff e₃ 0).mpr (by ring)
    let P₁ : W.Point := WeierstrassCurve.Affine.Point.some hns1
    let P₂ : W.Point := WeierstrassCurve.Affine.Point.some hns2
    let P₃ : W.Point := WeierstrassCurve.Affine.Point.some hns3
    have hker : ∀ P : W.Point, P ∈ (AddMonoidHom.id W.Point + AddMonoidHom.id W.Point).ker ↔
        P = 0 ∨ P = P₁ ∨ P = P₂ ∨ P = P₃ := by
      intro P
      rw [AddMonoidHom.mem_ker, AddMonoidHom.add_apply, AddMonoidHom.id_apply, add_eq_zero_iff_eq_neg]
      cases P with
      | zero =>
        change (0 : W.Point) = -(0 : W.Point) ↔
          (0 : W.Point) = 0 ∨ (0 : W.Point) = P₁ ∨ (0 : W.Point) = P₂ ∨ (0 : W.Point) = P₃
        simp [P₁, P₂, P₃]
      | @some x y h =>
        rw [WeierstrassCurve.Affine.Point.neg_some]
        simp only [WeierstrassCurve.Affine.Point.some.injEq, P₁, P₂, P₃,
          reduceCtorEq, false_or, true_and]
        have hnegY : W.negY x y = -y := by
          dsimp [W, threeRootsCurve, WeierstrassCurve.Affine.negY]
          ring
        rw [hnegY]
        have hy0 : y = -y ↔ y = 0 :=
          ⟨fun hy => (mul_eq_zero.mp (by linear_combination hy : (2 : F) * y = 0)).resolve_left two_ne_zero,
           fun hy => by rw [hy, neg_zero]⟩
        rw [hy0]
        constructor
        · intro hy
          have heq := (h_ns_iff x y).mp h
          have h0 : (x - e₁) * (x - e₂) * (x - e₃) = 0 := by linear_combination -heq + y * hy
          rcases mul_eq_zero.mp h0 with (h12 | h3)
          · rcases mul_eq_zero.mp h12 with (h1 | h2)
            · left; exact ⟨sub_eq_zero.mp h1, hy⟩
            · right; left; exact ⟨sub_eq_zero.mp h2, hy⟩
          · right; right; exact ⟨sub_eq_zero.mp h3, hy⟩
        · rintro (⟨rfl, hy⟩ | ⟨rfl, hy⟩ | ⟨rfl, hy⟩) <;> exact hy
    let S : Finset W.Point := {0, P₁, P₂, P₃}
    have hS_card : S.card = 4 := by
      dsimp [S]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [P₂, P₃, h₂₃]
      · simp [P₁, P₂, P₃, h₁₂, h₁₃]
      · intro h0
        simp only [Finset.mem_insert, Finset.mem_singleton, P₁, P₂, P₃] at h0
        rcases h0 with h0 | h0 | h0 <;> cases h0
    have h_equiv : ↥(AddMonoidHom.id W.Point + AddMonoidHom.id W.Point).ker ≃ ↥S :=
      Equiv.subtypeEquivRight (by
        intro P
        simp only [Finset.mem_insert, Finset.mem_singleton, S]
        exact hker P)
    rw [Nat.card_congr h_equiv, Nat.card_eq_fintype_card, Fintype.card_coe, hS_card]
  have h_inj : Function.Injective (algebraMap K (v.adicCompletion K)) :=
    (algebraMap K (v.adicCompletion K)).injective
  haveI : CharZero (v.adicCompletion K) := charZero_of_injective_ringHom h_inj
  have h₁₂' : algebraMap K (v.adicCompletion K) e₁ ≠ algebraMap K (v.adicCompletion K) e₂ :=
    h_inj.ne h₁₂
  have h₁₃' : algebraMap K (v.adicCompletion K) e₁ ≠ algebraMap K (v.adicCompletion K) e₃ :=
    h_inj.ne h₁₃
  have h₂₃' : algebraMap K (v.adicCompletion K) e₂ ≠ algebraMap K (v.adicCompletion K) e₃ :=
    h_inj.ne h₂₃
  rw [descent_set_ncard_eq_point_mod_two_card _ _ _ h₁₂' h₁₃' h₂₃',
      card_point_mod_two_adicCompletion_eq v _ _ _ h₁₂' h₁₃' h₂₃',
      h_torsion_gen _ _ _ h₁₂' h₁₃' h₂₃',
      natCard_sqCl_adicCompletion_eq v]

