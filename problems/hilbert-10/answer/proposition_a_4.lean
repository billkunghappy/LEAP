import Mathlib
import Hilbert10Defs
set_option maxHeartbeats 4000000

/-! ### Statement (originally `proposition_a_4.lean`) -/

/--
**Proposition A.4 ([5, Proposition 3.1]).** Let `K` be a number field. Then there is a
constant `C > 1` and a `C`-norm-length compatible `ℤ`-basis of `𝓞_K`.
-/

theorem proposition_a_4 (K : Type u) [Field K] [NumberField K] :
    ∃ (C : ℝ) (ω : Module.Basis (Fin (Module.finrank ℚ K)) ℤ
        (NumberField.RingOfIntegers K)), IsNormLengthCompatible C ω :=
by
  classical
  let ι := Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K)
  let ν := Module.finrank ℚ K
  have h_card : Fintype.card ι = ν := by
    rw [← Module.finrank_eq_card_chooseBasisIndex ℤ (NumberField.RingOfIntegers K),
      NumberField.RingOfIntegers.rank K]
  let e : ι ≃ Fin ν := Fintype.equivFinOfCardEq h_card
  let ω : Module.Basis (Fin ν) ℤ (NumberField.RingOfIntegers K) :=
    (NumberField.RingOfIntegers.basis K).reindex e
  have hν_pos : 0 < ν := Module.finrank_pos
  haveI : Nonempty (Fin ν) := Fin.pos_iff_nonempty.mp hν_pos
  let E := NumberField.mixedEmbedding.mixedSpace K
  let B₀ : Module.Basis ι ℝ E := NumberField.mixedEmbedding.latticeBasis K
  let ϕ : E ≃L[ℝ] (ι → ℝ) := B₀.equivFun.toContinuousLinearEquiv
  let C : ℝ := 2 + ‖(ϕ : E →L[ℝ] (ι → ℝ))‖ + ‖(ϕ.symm : (ι → ℝ) →L[ℝ] E)‖
  have hϕ_nn : 0 ≤ ‖(ϕ : E →L[ℝ] (ι → ℝ))‖ := norm_nonneg _
  have hϕs_nn : 0 ≤ ‖(ϕ.symm : (ι → ℝ) →L[ℝ] E)‖ := norm_nonneg _
  have hC1 : 1 < C := by dsimp [C]; linarith
  have hC_pos : 0 < C := by linarith
  have hC_ne : C ≠ 0 := ne_of_gt hC_pos
  refine ⟨C, ω, hC1, ?_⟩
  intro x
  let y : K := algebraMap (NumberField.RingOfIntegers K) K x
  let v_x : E := NumberField.mixedEmbedding K y
  have h_can : canNorm K y = ‖v_x‖ := by
    dsimp [canNorm, v_x]
    rw [NumberField.mixedEmbedding.norm_eq_sup'_normAtPlace]
    have h_eq : (fun w : NumberField.InfinitePlace K =>
        NumberField.mixedEmbedding.normAtPlace w (NumberField.mixedEmbedding K y)) =
        (fun w : NumberField.InfinitePlace K => w y) := by
      ext w
      exact NumberField.mixedEmbedding.normAtPlace_apply w y
    rw [h_eq, Finset.sup'_univ_eq_ciSup]
  have h_coord : ∀ i : ι, ϕ v_x i = (((NumberField.RingOfIntegers.basis K).repr x i : ℤ) : ℝ) := by
    intro i
    change (B₀.equivFun v_x) i = _
    rw [Module.Basis.equivFun_apply]
    dsimp [B₀, v_x, y]
    rw [NumberField.mixedEmbedding.latticeBasis_repr_apply, NumberField.integralBasis_repr_apply]
    simp
  have h_repr_j : ∀ j : Fin ν, ((ω.repr x j : ℤ) : ℝ) = ϕ v_x (e.symm j) := by
    intro j
    rw [h_coord (e.symm j)]
    congr 1
  have h_repr_i : ∀ i : ι, ϕ v_x i = ((ω.repr x (e i) : ℤ) : ℝ) := by
    intro i
    rw [h_repr_j (e i), Equiv.symm_apply_apply]
  have h_sup_le : basisSupNorm ω x ≤ C * ‖v_x‖ := by
    dsimp [basisSupNorm]
    refine ciSup_le (fun j => ?_)
    rw [h_repr_j j, ← Real.norm_eq_abs]
    have h1 : ‖ϕ v_x (e.symm j)‖ ≤ ‖ϕ v_x‖ := norm_le_pi_norm (ϕ v_x) (e.symm j)
    have h2 : ‖ϕ v_x‖ ≤ ‖(ϕ : E →L[ℝ] (ι → ℝ))‖ * ‖v_x‖ :=
      ContinuousLinearMap.le_opNorm (ϕ : E →L[ℝ] (ι → ℝ)) v_x
    have h3 : ‖(ϕ : E →L[ℝ] (ι → ℝ))‖ * ‖v_x‖ ≤ C * ‖v_x‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg v_x)
      dsimp [C]; linarith
    linarith
  have h_lower : C⁻¹ * basisSupNorm ω x ≤ canNorm K y := by
    rw [h_can]
    calc C⁻¹ * basisSupNorm ω x ≤ C⁻¹ * (C * ‖v_x‖) :=
          mul_le_mul_of_nonneg_left h_sup_le (inv_nonneg.mpr (le_of_lt hC_pos))
      _ = ‖v_x‖ := inv_mul_cancel_left₀ hC_ne ‖v_x‖
  have h_sup_nn : 0 ≤ basisSupNorm ω x := by
    obtain ⟨j₀⟩ := ‹Nonempty (Fin ν)›
    have hj₀ : |((ω.repr x j₀ : ℤ) : ℝ)| ≤ basisSupNorm ω x :=
      Finite.le_ciSup (fun j : Fin ν => |((ω.repr x j : ℤ) : ℝ)|) j₀
    exact le_trans (abs_nonneg _) hj₀
  have h_pi_le : ‖ϕ v_x‖ ≤ basisSupNorm ω x := by
    refine (pi_norm_le_iff_of_nonneg h_sup_nn).mpr (fun i => ?_)
    rw [Real.norm_eq_abs, h_repr_i i]
    exact Finite.le_ciSup (fun j : Fin ν => |((ω.repr x j : ℤ) : ℝ)|) (e i)
  have h_upper : canNorm K y ≤ C * basisSupNorm ω x := by
    rw [h_can]
    have h1 : ‖v_x‖ = ‖ϕ.symm (ϕ v_x)‖ := by rw [ContinuousLinearEquiv.symm_apply_apply]
    have h2 : ‖ϕ.symm (ϕ v_x)‖ ≤ ‖(ϕ.symm : (ι → ℝ) →L[ℝ] E)‖ * ‖ϕ v_x‖ :=
      ContinuousLinearMap.le_opNorm (ϕ.symm : (ι → ℝ) →L[ℝ] E) (ϕ v_x)
    have h3 : ‖(ϕ.symm : (ι → ℝ) →L[ℝ] E)‖ * ‖ϕ v_x‖ ≤
        ‖(ϕ.symm : (ι → ℝ) →L[ℝ] E)‖ * basisSupNorm ω x :=
      mul_le_mul_of_nonneg_left h_pi_le hϕs_nn
    have h4 : ‖(ϕ.symm : (ι → ℝ) →L[ℝ] E)‖ * basisSupNorm ω x ≤ C * basisSupNorm ω x := by
      apply mul_le_mul_of_nonneg_right _ h_sup_nn
      dsimp [C]; linarith
    linarith
  exact ⟨h_lower, h_upper⟩
