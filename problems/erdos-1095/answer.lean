import Mathlib
set_option maxHeartbeats 4000000

open Nat hiding log
open Real Filter
open scoped Asymptotics Topology
namespace Erdos1095
/--
Let $g(k)>k+1$ be the smallest $n$ such that all prime factors of $\binom{n}{k}$ are $>k$.
-/
noncomputable def g (k : ℕ) : ℕ := sInf {m | k + 1 < m ∧ k < (m.choose k).minFac}
open MeasureTheory
open Polynomial
open scoped BigOperators
open scoped Classical
open scoped ENNReal
open scoped EuclideanGeometry
open scoped InnerProductSpace
open scoped intervalIntegral
open scoped List
open scoped Matrix
open scoped Nat
open scoped NNReal
open scoped Pointwise
open scoped ProbabilityTheory
open scoped Real
open scoped symmDiff
open scoped Topology

theorem mellin_psi_eq_LSeries_vonMangoldt_div (s : ℂ) (hs : 1 < s.re) :
    MeasureTheory.IntegrableOn
        (fun u : ℝ => (Chebyshev.psi (Real.exp u) : ℂ) * Complex.exp (-s * (u : ℂ)))
        (Set.Ioi (0 : ℝ)) ∧
      (∫ u in Set.Ioi (0 : ℝ),
          (Chebyshev.psi (Real.exp u) : ℂ) * Complex.exp (-s * (u : ℂ)))
        = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s / s :=
by
  have hσ : (0 : ℝ) < s.re := by linarith
  have hσ0 : s.re ≠ 0 := ne_of_gt hσ
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hσ; simp at hσ

  
  have hnormg : ∀ (w : ℂ) (v : ℝ), ‖Complex.exp (-w * (v : ℂ))‖ = Real.exp (-w.re * v) := by
    intro w v
    rw [Complex.norm_exp]
    congr 1
    simp

  have hcont_e : ∀ w : ℂ, Continuous (fun v : ℝ => Complex.exp (-w * (v : ℂ))) := by
    intro w
    exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

  
  have hexp_int : ∀ w : ℂ, 0 < w.re → ∀ b : ℝ,
      MeasureTheory.IntegrableOn (fun v : ℝ => Complex.exp (-w * (v : ℂ))) (Set.Ioi b) := by
    intro w hw b
    have hdom : MeasureTheory.IntegrableOn (fun v : ℝ => Real.exp (-w.re * v)) (Set.Ioi b) :=
      exp_neg_integrableOn_Ioi b hw
    refine MeasureTheory.Integrable.mono' hdom (hcont_e w).aestronglyMeasurable ?_
    filter_upwards with v
    exact le_of_eq (hnormg w v)

  
  have hexp_val : ∀ w : ℂ, 0 < w.re → ∀ b : ℝ,
      (∫ v in Set.Ioi b, Complex.exp (-w * (v : ℂ))) = Complex.exp (-w * (b : ℂ)) / w := by
    intro w hw b
    have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
    have hderiv : ∀ v : ℝ,
        HasDerivAt (fun v : ℝ => -Complex.exp (-w * (v : ℂ)) / w)
          (Complex.exp (-w * (v : ℂ))) v := by
      intro v
      have h0 : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 v := Complex.ofRealCLM.hasDerivAt
      have h1 : HasDerivAt (fun v : ℝ => -w * (v : ℂ)) (-w) v := by
        simpa using h0.const_mul (-w)
      have h3 := (h1.cexp.neg).div_const w
      convert h3 using 1
      field_simp
    have hcontG : Continuous (fun v : ℝ => -Complex.exp (-w * (v : ℂ)) / w) :=
      ((hcont_e w).neg).div_const w
    have htend : Filter.Tendsto (fun v : ℝ => -Complex.exp (-w * (v : ℂ)) / w)
        Filter.atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hnorm : ∀ v : ℝ, ‖-Complex.exp (-w * (v : ℂ)) / w‖ = Real.exp (-w.re * v) / ‖w‖ := by
        intro v
        rw [norm_div, norm_neg, hnormg w v]
      simp only [hnorm]
      have h1 : Filter.Tendsto (fun v : ℝ => w.re * v) Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop hw Filter.tendsto_id
      have h2 : Filter.Tendsto (fun v : ℝ => -w.re * v) Filter.atTop Filter.atBot := by
        have h2' := tendsto_neg_atTop_atBot.comp h1
        have heq : (fun v : ℝ => -w.re * v) = (Neg.neg ∘ fun v : ℝ => w.re * v) := by
          funext v; simp [Function.comp]
        rw [heq]; exact h2'
      have h3 : Filter.Tendsto (fun v : ℝ => Real.exp (-w.re * v)) Filter.atTop (nhds 0) :=
        Real.tendsto_exp_atBot.comp h2
      simpa using h3.div_const ‖w‖
    have key := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
      hcontG.continuousWithinAt (fun x _ => hderiv x) (hexp_int w hw b) htend
    rw [key]
    ring

  
  have hRexp_val : ∀ b : ℝ,
      (∫ v in Set.Ioi b, Real.exp (-s.re * v)) = Real.exp (-s.re * b) / s.re := by
    intro b
    have hderiv : ∀ v : ℝ,
        HasDerivAt (fun v : ℝ => -Real.exp (-s.re * v) / s.re) (Real.exp (-s.re * v)) v := by
      intro v
      have h1 : HasDerivAt (fun v : ℝ => -s.re * v) (-s.re) v := by
        simpa using (hasDerivAt_id v).const_mul (-s.re)
      have h3 := (h1.exp.neg).div_const s.re
      convert h3 using 1
      field_simp
    have hcontG : Continuous (fun v : ℝ => -Real.exp (-s.re * v) / s.re) :=
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).neg).div_const s.re
    have htend : Filter.Tendsto (fun v : ℝ => -Real.exp (-s.re * v) / s.re)
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun v : ℝ => s.re * v) Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop hσ Filter.tendsto_id
      have h2 : Filter.Tendsto (fun v : ℝ => -s.re * v) Filter.atTop Filter.atBot := by
        have h2' := tendsto_neg_atTop_atBot.comp h1
        have heq : (fun v : ℝ => -s.re * v) = (Neg.neg ∘ fun v : ℝ => s.re * v) := by
          funext v; simp [Function.comp]
        rw [heq]; exact h2'
      have h3 : Filter.Tendsto (fun v : ℝ => Real.exp (-s.re * v)) Filter.atTop (nhds 0) :=
        Real.tendsto_exp_atBot.comp h2
      simpa using (h3.neg).div_const s.re
    have key := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
      hcontG.continuousWithinAt (fun x _ => hderiv x) (exp_neg_integrableOn_Ioi b hσ) htend
    rw [key]
    ring

  
  have hdomred : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (h : ℝ → E) (a : ℝ), 0 ≤ a →
      (∫ u in Set.Ioi (0 : ℝ), (Set.Ici a).indicator h u) = ∫ u in Set.Ioi a, h u := by
    intro E _ _ _ h a ha
    rw [MeasureTheory.integral_indicator measurableSet_Ici,
      MeasureTheory.Measure.restrict_restrict measurableSet_Ici]
    rcases eq_or_lt_of_le ha with h0 | h0
    · have hset : Set.Ici a ∩ Set.Ioi (0 : ℝ) = Set.Ioi a := by
        rw [← h0]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioi]
        exact ⟨fun hx => hx.2, fun hx => ⟨le_of_lt hx, hx⟩⟩
      rw [hset]
    · have hsub : Set.Ici a ⊆ Set.Ioi (0 : ℝ) := Set.Ici_subset_Ioi.mpr h0
      rw [Set.inter_eq_self_of_subset_left hsub, MeasureTheory.integral_Ici_eq_integral_Ioi]

  
  have hind_int : ∀ a : ℝ, MeasureTheory.IntegrableOn
      ((Set.Ici a).indicator (fun v : ℝ => Complex.exp (-s * (v : ℂ)))) (Set.Ioi (0 : ℝ)) := by
    intro a
    exact (hexp_int s hσ 0).indicator measurableSet_Ici

  
  have hs2 : ∀ u : ℝ,
      (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
          (Set.Ici (Real.log n)).indicator (fun v : ℝ => Complex.exp (-s * (v : ℂ))) u)
        = (Chebyshev.psi (Real.exp u) : ℂ) * Complex.exp (-s * (u : ℂ)) := by
    intro u
    have hmem : ∀ n : ℕ, 0 < n → (n ≤ ⌊Real.exp u⌋₊ ↔ Real.log (n : ℝ) ≤ u) := by
      intro n hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      rw [Nat.le_floor_iff (Real.exp_nonneg u)]
      exact (Real.log_le_iff_le_exp hn0).symm
    have hvanish : ∀ n : ℕ, n ∉ Finset.Icc 0 ⌊Real.exp u⌋₊ →
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          (Set.Ici (Real.log n)).indicator (fun v : ℝ => Complex.exp (-s * (v : ℂ))) u = 0 := by
      intro n hn
      have hgt : ⌊Real.exp u⌋₊ < n := by
        by_contra hc
        exact hn (Finset.mem_Icc.mpr ⟨Nat.zero_le n, not_lt.mp hc⟩)
      have hn1 : 0 < n := by omega
      have hnot : ¬ (Real.log (n : ℝ) ≤ u) := by
        rw [← hmem n hn1]
        omega
      simp [hnot]
    rw [tsum_eq_sum hvanish]
    have hterm : ∀ n ∈ Finset.Icc 0 ⌊Real.exp u⌋₊,
        (ArithmeticFunction.vonMangoldt n : ℂ) *
            (Set.Ici (Real.log n)).indicator (fun v : ℝ => Complex.exp (-s * (v : ℂ))) u
          = (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.exp (-s * (u : ℂ)) := by
      intro n hn
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0
        simp
      · have hle : n ≤ ⌊Real.exp u⌋₊ := (Finset.mem_Icc.mp hn).2
        have hin : Real.log (n : ℝ) ≤ u := (hmem n h0).mp hle
        simp [hin]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
    congr 1
    rw [Chebyshev.psi_eq_sum_Icc, Complex.ofReal_sum]

  
  have psi_le_six : ∀ x : ℝ, 1 ≤ x → Chebyshev.psi x ≤ 6 * x := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    have hsq : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hxpos
    have hlogsqrt : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hsq
    have hls : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx0
    have hlogx : Real.log x ≤ 2 * Real.sqrt x := by rw [hls] at hlogsqrt; linarith
    have hlog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    have hlog4 : Real.log 4 ≤ 2 := by
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast
        ring
      rw [h4]; linarith
    have hA : Real.log 4 * x ≤ 2 * x := mul_le_mul_of_nonneg_right hlog4 hx0
    have hsqsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
    have hB : 2 * Real.sqrt x * Real.log x ≤ 4 * x := by
      calc 2 * Real.sqrt x * Real.log x
          ≤ 2 * Real.sqrt x * (2 * Real.sqrt x) :=
            mul_le_mul_of_nonneg_left hlogx (by positivity)
        _ = 4 * Real.sqrt x ^ 2 := by ring
        _ = 4 * x := by rw [hsqsq]
    have hpsi := Chebyshev.psi_le hx
    linarith

  have hs3 : MeasureTheory.IntegrableOn
      (fun u : ℝ => (Chebyshev.psi (Real.exp u) : ℂ) * Complex.exp (-s * (u : ℂ)))
      (Set.Ioi (0 : ℝ)) := by
    have hmeas : Measurable
        (fun u : ℝ => (Chebyshev.psi (Real.exp u) : ℂ) * Complex.exp (-s * (u : ℂ))) := by
      have h1 : Measurable Chebyshev.psi := Chebyshev.psi_mono.measurable
      have h2 : Measurable (fun u : ℝ => Chebyshev.psi (Real.exp u)) :=
        h1.comp Real.continuous_exp.measurable
      have h3 : Measurable (fun u : ℝ => ((Chebyshev.psi (Real.exp u) : ℝ) : ℂ)) :=
        Complex.measurable_ofReal.comp h2
      exact h3.mul (hcont_e s).measurable
    have hdom : MeasureTheory.IntegrableOn
        (fun u : ℝ => 6 * Real.exp (-(s.re - 1) * u)) (Set.Ioi (0 : ℝ)) :=
      (exp_neg_integrableOn_Ioi 0 (by linarith : (0 : ℝ) < s.re - 1)).const_mul 6
    refine MeasureTheory.Integrable.mono' hdom hmeas.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := hu
    have he1 : (1 : ℝ) ≤ Real.exp u := by
      simpa using Real.exp_le_exp.mpr hu0.le
    have hpsi := psi_le_six (Real.exp u) he1
    have hnn := Chebyshev.psi_nonneg (Real.exp u)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn, hnormg s u]
    have hexp_pos : (0 : ℝ) < Real.exp (-s.re * u) := Real.exp_pos _
    calc Chebyshev.psi (Real.exp u) * Real.exp (-s.re * u)
        ≤ (6 * Real.exp u) * Real.exp (-s.re * u) :=
          mul_le_mul_of_nonneg_right hpsi hexp_pos.le
      _ = 6 * Real.exp (-(s.re - 1) * u) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 1
          ring

  
  have hFint : ∀ n : ℕ, MeasureTheory.IntegrableOn
      (fun u : ℝ => (ArithmeticFunction.vonMangoldt n : ℂ) *
        (Set.Ici (Real.log n)).indicator (fun v : ℝ => Complex.exp (-s * (v : ℂ))) u)
      (Set.Ioi (0 : ℝ)) := by
    intro n
    exact (hind_int (Real.log (n : ℝ))).const_mul _

  have hFval : ∀ n : ℕ,
      (∫ u in Set.Ioi (0 : ℝ), (ArithmeticFunction.vonMangoldt n : ℂ) *
          (Set.Ici (Real.log n)).indicator (fun v : ℝ => Complex.exp (-s * (v : ℂ))) u)
        = LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) s n / s := by
    intro n
    rw [MeasureTheory.integral_const_mul,
      hdomred ℂ (fun v : ℝ => Complex.exp (-s * (v : ℂ))) (Real.log (n : ℝ))
        (Real.log_natCast_nonneg n),
      hexp_val s hσ (Real.log (n : ℝ))]
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      simp
    · have hn0 : n ≠ 0 := by omega
      have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
      have hlogc : Complex.log (n : ℂ) = ((Real.log (n : ℝ) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (Nat.cast_nonneg n)]
      have hcpow : ((n : ℂ)) ^ s = Complex.exp (((Real.log (n : ℝ) : ℝ) : ℂ) * s) := by
        rw [Complex.cpow_def_of_ne_zero hnC, hlogc]
      have hkey : Complex.exp (-s * ((Real.log (n : ℝ) : ℝ) : ℂ)) = ((n : ℂ) ^ s)⁻¹ := by
        rw [hcpow, ← Complex.exp_neg]
        congr 1
        ring
      rw [LSeries.term_of_ne_zero hn0, hkey]
      ring

  have hFnorm : ∀ n : ℕ,
      (∫ u in Set.Ioi (0 : ℝ), ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
          (Set.Ici (Real.log n)).indicator (fun v : ℝ => Complex.exp (-s * (v : ℂ))) u‖)
        = ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) s n‖ / s.re := by
    intro n
    have hpt : ∀ u : ℝ, ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
        (Set.Ici (Real.log n)).indicator (fun v : ℝ => Complex.exp (-s * (v : ℂ))) u‖
      = ArithmeticFunction.vonMangoldt n *
        (Set.Ici (Real.log (n : ℝ))).indicator (fun v : ℝ => Real.exp (-s.re * v)) u := by
      intro u
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      congr 1
      by_cases hu : u ∈ Set.Ici (Real.log (n : ℝ))
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, hnormg s u]
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, norm_zero]
    simp only [hpt]
    rw [MeasureTheory.integral_const_mul,
      hdomred ℝ (fun v : ℝ => Real.exp (-s.re * v)) (Real.log (n : ℝ))
        (Real.log_natCast_nonneg n),
      hRexp_val (Real.log (n : ℝ))]
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      simp
    · have hn0 : n ≠ 0 := by omega
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h0
      have hrpow : ((n : ℝ) ^ s.re) = Real.exp (Real.log (n : ℝ) * s.re) :=
        Real.rpow_def_of_pos hnR _
      have hexpeq : Real.exp (-s.re * Real.log (n : ℝ)) = ((n : ℝ) ^ s.re)⁻¹ := by
        rw [hrpow, ← Real.exp_neg]
        congr 1
        ring
      rw [LSeries.term_of_ne_zero hn0, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        Complex.norm_natCast_cpow_of_pos h0, hexpeq]
      ring

  
  have hLSsum : Summable (LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) s) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs

  have hsum : Summable (fun n : ℕ => ∫ u in Set.Ioi (0 : ℝ),
      ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
        (Set.Ici (Real.log n)).indicator (fun v : ℝ => Complex.exp (-s * (v : ℂ))) u‖) := by
    have hnorm : Summable (fun n : ℕ =>
        ‖LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) s n‖) :=
      summable_norm_iff.mpr hLSsum
    have h2 := hnorm.div_const s.re
    simpa only [hFnorm] using h2

  
  have hTonelli := MeasureTheory.hasSum_integral_of_summable_integral_norm
      (F := fun (n : ℕ) (u : ℝ) => (ArithmeticFunction.vonMangoldt n : ℂ) *
        (Set.Ici (Real.log n)).indicator (fun v : ℝ => Complex.exp (-s * (v : ℂ))) u)
      (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) hFint hsum

  have hP : HasSum
      (fun n : ℕ => LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) s n / s)
      (∫ u in Set.Ioi (0 : ℝ),
        (Chebyshev.psi (Real.exp u) : ℂ) * Complex.exp (-s * (u : ℂ))) := by
    simpa only [hFval, hs2] using hTonelli

  have hQ : HasSum
      (fun n : ℕ => LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) s n / s)
      (LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) s / s) :=
    hLSsum.hasSum.div_const s

  exact ⟨hs3, hP.unique hQ⟩

theorem zeta_logDeriv_sub_pole_extends : ∃ (U : Set ℂ) (H : ℂ → ℂ), IsOpen U ∧ {s : ℂ | 1 ≤ s.re} ⊆ U ∧
      DifferentiableOn ℂ H U ∧
      ∀ s : ℂ, 1 < s.re → H s = -deriv riemannZeta s / riemannZeta s - 1 / (s - 1) :=
by
  classical
  
  have main : ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 = 1 ∧
      ∀ s : ℂ, s ≠ 1 → Z s = (s - 1) * riemannZeta s := by
    have hWeq : ∀ s : ℂ, s ≠ 1 →
        (if s = 1 then (1 : ℂ) else (s - 1) * riemannZeta s) = (s - 1) * riemannZeta s :=
      fun s hs => if_neg hs
    have hW1 : (if (1 : ℂ) = 1 then (1 : ℂ) else ((1 : ℂ) - 1) * riemannZeta 1) = 1 := if_pos rfl
    
    have hdiff_ne : ∀ z : ℂ, z ≠ 1 →
        DifferentiableAt ℂ
          (fun s : ℂ => if s = 1 then (1 : ℂ) else (s - 1) * riemannZeta s) z := by
      intro z hz
      have hV : {w : ℂ | w ≠ 1} ∈ 𝓝 z := isOpen_ne.mem_nhds hz
      have heq : (fun s : ℂ => if s = 1 then (1 : ℂ) else (s - 1) * riemannZeta s)
          =ᶠ[𝓝 z] (fun w : ℂ => (w - 1) * riemannZeta w) :=
        Filter.eventuallyEq_of_mem hV (fun w hw => hWeq w hw)
      have hd : DifferentiableAt ℂ (fun w : ℂ => (w - 1) * riemannZeta w) z :=
        (differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hz)
      exact hd.congr_of_eventuallyEq heq
    refine ⟨fun s : ℂ => if s = 1 then (1 : ℂ) else (s - 1) * riemannZeta s, ?_, hW1, hWeq⟩
    intro z
    by_cases hz : z = 1
    · 
      subst hz
      have h1 : ∀ᶠ w in 𝓝[{(1 : ℂ)}ᶜ] (1 : ℂ),
          DifferentiableAt ℂ
            (fun s : ℂ => if s = 1 then (1 : ℂ) else (s - 1) * riemannZeta s) w := by
        filter_upwards [self_mem_nhdsWithin] with w hw
        exact hdiff_ne w hw
      have hfe : (fun s : ℂ => (s - 1) * riemannZeta s)
          =ᶠ[𝓝[{(1 : ℂ)}ᶜ] (1 : ℂ)]
            (fun s : ℂ => if s = 1 then (1 : ℂ) else (s - 1) * riemannZeta s) :=
        Filter.eventuallyEq_of_mem self_mem_nhdsWithin (fun w hw => (hWeq w hw).symm)
      have ht : Filter.Tendsto
          (fun s : ℂ => if s = 1 then (1 : ℂ) else (s - 1) * riemannZeta s)
          (𝓝[{(1 : ℂ)}ᶜ] (1 : ℂ)) (𝓝 (1 : ℂ)) :=
        Filter.Tendsto.congr' hfe riemannZeta_residue_one
      have h2 : ContinuousAt
          (fun s : ℂ => if s = 1 then (1 : ℂ) else (s - 1) * riemannZeta s) 1 := by
        rw [← continuousWithinAt_compl_self]
        show Filter.Tendsto _ _ (𝓝 ((fun s : ℂ =>
          if s = 1 then (1 : ℂ) else (s - 1) * riemannZeta s) (1 : ℂ)))
        simpa using ht
      exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
        h1 h2).differentiableAt
    · exact hdiff_ne z hz
  obtain ⟨Z, hZdiff, hZ1, hZeq⟩ := main
  
  have hderivZ : Differentiable ℂ (deriv Z) := fun z =>
    ((hZdiff.analyticAt z).deriv).differentiableAt
  
  refine ⟨{s : ℂ | Z s ≠ 0}, fun s : ℂ => -deriv Z s / Z s, ?_, ?_, ?_, ?_⟩
  · exact isOpen_ne.preimage hZdiff.continuous
  · intro s hs
    have hsre : (1 : ℝ) ≤ s.re := hs
    show Z s ≠ 0
    by_cases h1 : s = 1
    · rw [h1, hZ1]; exact one_ne_zero
    · rw [hZeq s h1]
      exact mul_ne_zero (sub_ne_zero.mpr h1) (riemannZeta_ne_zero_of_one_le_re hsre)
  · intro s hs
    have hs' : Z s ≠ 0 := hs
    exact (((hderivZ s).neg).div (hZdiff s) hs').differentiableWithinAt
  · intro s hs
    have hs1 : s ≠ 1 := by
      intro h
      rw [h] at hs
      simp at hs
    have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have hzne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
    have hZs : Z s = (s - 1) * riemannZeta s := hZeq s hs1
    have hdZ : deriv Z s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
      have hV : {w : ℂ | w ≠ 1} ∈ 𝓝 s := isOpen_ne.mem_nhds hs1
      have heq : Z =ᶠ[𝓝 s] (fun w : ℂ => (w - 1) * riemannZeta w) :=
        Filter.eventuallyEq_of_mem hV (fun w hw => hZeq w hw)
      rw [heq.deriv_eq]
      have h1 : HasDerivAt (fun w : ℂ => w - 1) 1 s := (hasDerivAt_id s).sub_const 1
      have h2 : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
        (differentiableAt_riemannZeta hs1).hasDerivAt
      simpa using (h1.mul h2).deriv
    show -deriv Z s / Z s = -deriv riemannZeta s / riemannZeta s - 1 / (s - 1)
    rw [hdZ, hZs]
    field_simp
    ring

theorem rect_cauchy_formula_at_zero (a b c d : ℝ)
    (ha : a < 0) (hb : 0 < b) (hc : c < 0) (hd : 0 < d)
    (Ω : Set ℂ) (hΩ : IsOpen Ω) (h : ℂ → ℂ)
    (hsub : {z : ℂ | z.re ∈ Set.uIcc a b ∧ z.im ∈ Set.uIcc c d} ⊆ Ω)
    (hh : DifferentiableOn ℂ h Ω) :
    (((∫ x : ℝ in a..b, h ((x : ℂ) + (c : ℂ) * Complex.I) / ((x : ℂ) + (c : ℂ) * Complex.I))
        - ∫ x : ℝ in a..b, h ((x : ℂ) + (d : ℂ) * Complex.I) / ((x : ℂ) + (d : ℂ) * Complex.I))
      + Complex.I * ∫ y : ℝ in c..d,
          h ((b : ℂ) + (y : ℂ) * Complex.I) / ((b : ℂ) + (y : ℂ) * Complex.I))
      - Complex.I * ∫ y : ℝ in c..d,
          h ((a : ℂ) + (y : ℂ) * Complex.I) / ((a : ℂ) + (y : ℂ) * Complex.I)
    = 2 * (Real.pi : ℂ) * Complex.I * h 0 :=
by
  
  have HI : ∀ p q t : ℝ, t ≠ 0 →
      (∫ x : ℝ in p..q, ((x : ℂ) + (t : ℂ) * Complex.I)⁻¹)
        = (((Real.log (q ^ 2 + t ^ 2) - Real.log (p ^ 2 + t ^ 2)) / 2 : ℝ) : ℂ)
          - Complex.I * ((Real.arctan (q / t) - Real.arctan (p / t) : ℝ) : ℂ) := by
    intro p q t ht
    have ht2 : (0:ℝ) < t ^ 2 := by positivity
    have hpos : ∀ x : ℝ, (0:ℝ) < x ^ 2 + t ^ 2 := by
      intro x; nlinarith [sq_nonneg x]
    have hne : ∀ x : ℝ, ((x : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro x hz
      exact ht (by simpa using congrArg Complex.im hz)
    have hderiv : ∀ x : ℝ, HasDerivAt
        (fun x : ℝ => ((Real.log (x ^ 2 + t ^ 2) / 2 : ℝ) : ℂ)
          - Complex.I * ((Real.arctan (x / t) : ℝ) : ℂ))
        (((x : ℂ) + (t : ℂ) * Complex.I)⁻¹) x := by
      intro x
      have hx2 : (x ^ 2 + t ^ 2) ≠ 0 := ne_of_gt (hpos x)
      have h1 : HasDerivAt (fun x : ℝ => x ^ 2 + t ^ 2) (2 * x) x := by
        simpa using (hasDerivAt_pow 2 x).add_const (t ^ 2)
      have h2 : HasDerivAt (fun x : ℝ => Real.log (x ^ 2 + t ^ 2))
          (2 * x / (x ^ 2 + t ^ 2)) x := h1.log hx2
      have h3 : HasDerivAt (fun x : ℝ => Real.log (x ^ 2 + t ^ 2) / 2)
          (x / (x ^ 2 + t ^ 2)) x := by
        have hq := h2.div_const 2
        convert hq using 1
        field_simp
        try ring
      have h4 : HasDerivAt (fun x : ℝ => x / t) (1 / t) x := by
        simpa using (hasDerivAt_id x).div_const t
      have h5 : HasDerivAt (fun x : ℝ => Real.arctan (x / t)) (t / (x ^ 2 + t ^ 2)) x := by
        have hq := (Real.hasDerivAt_arctan (x / t)).comp x h4
        convert hq using 1
        field_simp
        try ring
      have h3c := h3.ofReal_comp
      have h5c := h5.ofReal_comp
      have h6 := h5c.const_mul Complex.I
      have h7 := h3c.sub h6
      convert h7 using 1
      have hre : ((x : ℂ) + (t : ℂ) * Complex.I).re = x := by simp
      have him : ((x : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
      apply Complex.ext
      · simp only [Complex.inv_re, Complex.normSq_apply, Complex.sub_re, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, hre, him]
        ring
      · simp only [Complex.inv_im, Complex.normSq_apply, Complex.sub_im, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, hre, him]
        ring
    have hint : IntervalIntegrable
        (fun x : ℝ => ((x : ℂ) + (t : ℂ) * Complex.I)⁻¹) MeasureTheory.volume p q := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.inv₀
      · exact (Complex.continuous_ofReal.add continuous_const).continuousOn
      · intro x _; exact hne x
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) hint]
    push_cast
    ring
  
  have VI : ∀ p q r : ℝ, r ≠ 0 →
      (∫ y : ℝ in p..q, ((r : ℂ) + (y : ℂ) * Complex.I)⁻¹)
        = ((Real.arctan (q / r) - Real.arctan (p / r) : ℝ) : ℂ)
          - Complex.I
              * (((Real.log (r ^ 2 + q ^ 2) - Real.log (r ^ 2 + p ^ 2)) / 2 : ℝ) : ℂ) := by
    intro p q r hr
    have hr2 : (0:ℝ) < r ^ 2 := by positivity
    have hpos : ∀ y : ℝ, (0:ℝ) < r ^ 2 + y ^ 2 := by
      intro y; nlinarith [sq_nonneg y]
    have hne : ∀ y : ℝ, ((r : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
      intro y hz
      exact hr (by simpa using congrArg Complex.re hz)
    have hderiv : ∀ y : ℝ, HasDerivAt
        (fun y : ℝ => ((Real.arctan (y / r) : ℝ) : ℂ)
          - Complex.I * ((Real.log (r ^ 2 + y ^ 2) / 2 : ℝ) : ℂ))
        (((r : ℂ) + (y : ℂ) * Complex.I)⁻¹) y := by
      intro y
      have hy2 : (r ^ 2 + y ^ 2) ≠ 0 := ne_of_gt (hpos y)
      have h4 : HasDerivAt (fun y : ℝ => y / r) (1 / r) y := by
        simpa using (hasDerivAt_id y).div_const r
      have h5 : HasDerivAt (fun y : ℝ => Real.arctan (y / r)) (r / (r ^ 2 + y ^ 2)) y := by
        have hq := (Real.hasDerivAt_arctan (y / r)).comp y h4
        convert hq using 1
        field_simp
        try ring
      have h1 : HasDerivAt (fun y : ℝ => r ^ 2 + y ^ 2) (2 * y) y := by
        simpa using (hasDerivAt_pow 2 y).const_add (r ^ 2)
      have h2 : HasDerivAt (fun y : ℝ => Real.log (r ^ 2 + y ^ 2))
          (2 * y / (r ^ 2 + y ^ 2)) y := h1.log hy2
      have h3 : HasDerivAt (fun y : ℝ => Real.log (r ^ 2 + y ^ 2) / 2)
          (y / (r ^ 2 + y ^ 2)) y := by
        have hq := h2.div_const 2
        convert hq using 1
        field_simp
        try ring
      have h5c := h5.ofReal_comp
      have h3c := h3.ofReal_comp
      have h6 := h3c.const_mul Complex.I
      have h7 := h5c.sub h6
      convert h7 using 1
      have hre : ((r : ℂ) + (y : ℂ) * Complex.I).re = r := by simp
      have him : ((r : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
      apply Complex.ext
      · simp only [Complex.inv_re, Complex.normSq_apply, Complex.sub_re, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, hre, him]
        ring
      · simp only [Complex.inv_im, Complex.normSq_apply, Complex.sub_im, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, hre, him]
        ring
    have hint : IntervalIntegrable
        (fun y : ℝ => ((r : ℂ) + (y : ℂ) * Complex.I)⁻¹) MeasureTheory.volume p q := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.inv₀
      · exact (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
      · intro y _; exact hne y
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y) hint]
    push_cast
    ring
  
  have ha0 : a ≠ 0 := ne_of_lt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hc0 : c ≠ 0 := ne_of_lt hc
  have hd0 : d ≠ 0 := ne_of_gt hd
  have h0ab : (0:ℝ) ∈ Set.uIcc a b := Set.mem_uIcc.mpr (Or.inl ⟨ha.le, hb.le⟩)
  have h0cd : (0:ℝ) ∈ Set.uIcc c d := Set.mem_uIcc.mpr (Or.inl ⟨hc.le, hd.le⟩)
  have hreP : ∀ x t : ℝ, ((x : ℂ) + (t : ℂ) * Complex.I).re = x := by intro x t; simp
  have himP : ∀ x t : ℝ, ((x : ℂ) + (t : ℂ) * Complex.I).im = t := by intro x t; simp
  have hneI : ∀ x t : ℝ, t ≠ 0 → ((x : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro x t ht hz; exact ht (by simpa using congrArg Complex.im hz)
  have hneR : ∀ r y : ℝ, r ≠ 0 → ((r : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
    intro r y hr hz; exact hr (by simpa using congrArg Complex.re hz)
  have hmemQ : ∀ z : ℂ, z.re ∈ Set.uIcc a b → z.im ∈ Set.uIcc c d → z ∈ Ω := by
    intro z h1 h2; exact hsub ⟨h1, h2⟩
  
  have hcontH : ContinuousOn h Ω := hh.continuousOn
  have hsplit : ∀ (p q : ℝ) (γ : ℝ → ℂ), Continuous γ →
      (∀ x ∈ Set.uIcc p q, γ x ∈ Ω) → (∀ x ∈ Set.uIcc p q, γ x ≠ 0) →
      (∫ x : ℝ in p..q, h (γ x) / γ x)
        = (∫ x : ℝ in p..q, (h (γ x) - h 0) / γ x) + h 0 * ∫ x : ℝ in p..q, (γ x)⁻¹ := by
    intro p q γ hγ hmaps hnz
    have hc1 : ContinuousOn (fun x : ℝ => h (γ x)) (Set.uIcc p q) :=
      hcontH.comp hγ.continuousOn hmaps
    have hc2 : ContinuousOn (fun x : ℝ => (γ x)⁻¹) (Set.uIcc p q) :=
      hγ.continuousOn.inv₀ hnz
    have hi1 : IntervalIntegrable (fun x : ℝ => (h (γ x) - h 0) / γ x)
        MeasureTheory.volume p q :=
      ((hc1.sub continuousOn_const).div hγ.continuousOn hnz).intervalIntegrable
    have hi2 : IntervalIntegrable (fun x : ℝ => h 0 * (γ x)⁻¹)
        MeasureTheory.volume p q :=
      (continuousOn_const.mul hc2).intervalIntegrable
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hi1 hi2]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    have hx0 : γ x ≠ 0 := hnz x hx
    field_simp
    ring
  
  have hQeq : {z : ℂ | z.re ∈ Set.uIcc a b ∧ z.im ∈ Set.uIcc c d}
      = Set.uIcc a b ×ℂ Set.uIcc c d := by
    ext z; simp [Complex.mem_reProdIm]
  have h0Ω : (0 : ℂ) ∈ Ω := hmemQ 0 (by simpa using h0ab) (by simpa using h0cd)
  have hnhds : Ω ∈ nhds (0 : ℂ) := hΩ.mem_nhds h0Ω
  have hdsl : DifferentiableOn ℂ (dslope h 0) Ω :=
    (Complex.differentiableOn_dslope hnhds).mpr hh
  have hdrect : DifferentiableOn ℂ (dslope h 0)
      (Set.uIcc ((a : ℂ) + (c : ℂ) * Complex.I).re ((b : ℂ) + (d : ℂ) * Complex.I).re ×ℂ
        Set.uIcc ((a : ℂ) + (c : ℂ) * Complex.I).im ((b : ℂ) + (d : ℂ) * Complex.I).im) := by
    rw [hreP, himP, hreP, himP, ← hQeq]
    exact hdsl.mono hsub
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (dslope h 0) ((a : ℂ) + (c : ℂ) * Complex.I) ((b : ℂ) + (d : ℂ) * Complex.I) hdrect
  rw [hreP, himP, hreP, himP] at hrect
  simp only [smul_eq_mul] at hrect
  have hdsl_eq : ∀ z : ℂ, z ≠ 0 → dslope h 0 z = (h z - h 0) / z := by
    intro z hz
    rw [dslope_of_ne _ hz, slope_def_field, sub_zero]
  have hcg1 : (∫ x : ℝ in a..b, dslope h 0 ((x : ℂ) + (c : ℂ) * Complex.I))
      = ∫ x : ℝ in a..b, (h ((x : ℂ) + (c : ℂ) * Complex.I) - h 0)
          / ((x : ℂ) + (c : ℂ) * Complex.I) :=
    intervalIntegral.integral_congr (fun x _ => hdsl_eq _ (hneI x c hc0))
  have hcg2 : (∫ x : ℝ in a..b, dslope h 0 ((x : ℂ) + (d : ℂ) * Complex.I))
      = ∫ x : ℝ in a..b, (h ((x : ℂ) + (d : ℂ) * Complex.I) - h 0)
          / ((x : ℂ) + (d : ℂ) * Complex.I) :=
    intervalIntegral.integral_congr (fun x _ => hdsl_eq _ (hneI x d hd0))
  have hcg3 : (∫ y : ℝ in c..d, dslope h 0 ((b : ℂ) + (y : ℂ) * Complex.I))
      = ∫ y : ℝ in c..d, (h ((b : ℂ) + (y : ℂ) * Complex.I) - h 0)
          / ((b : ℂ) + (y : ℂ) * Complex.I) :=
    intervalIntegral.integral_congr (fun y _ => hdsl_eq _ (hneR b y hb0))
  have hcg4 : (∫ y : ℝ in c..d, dslope h 0 ((a : ℂ) + (y : ℂ) * Complex.I))
      = ∫ y : ℝ in c..d, (h ((a : ℂ) + (y : ℂ) * Complex.I) - h 0)
          / ((a : ℂ) + (y : ℂ) * Complex.I) :=
    intervalIntegral.integral_congr (fun y _ => hdsl_eq _ (hneR a y ha0))
  rw [hcg1, hcg2, hcg3, hcg4] at hrect
  
  have hS : (-(Real.arctan (b / c) - Real.arctan (a / c))
        + (Real.arctan (b / d) - Real.arctan (a / d)))
      + (Real.arctan (d / b) - Real.arctan (c / b))
      - (Real.arctan (d / a) - Real.arctan (c / a)) = 2 * Real.pi := by
    have e1 : (d : ℝ) / b = (b / d)⁻¹ := (inv_div b d).symm
    have e2 : (c : ℝ) / b = (b / c)⁻¹ := (inv_div b c).symm
    have e3 : (c : ℝ) / a = (a / c)⁻¹ := (inv_div a c).symm
    have e4 : (d : ℝ) / a = (a / d)⁻¹ := (inv_div a d).symm
    rw [e1, e2, e3, e4,
      Real.arctan_inv_of_pos (div_pos hb hd),
      Real.arctan_inv_of_neg (div_neg_of_pos_of_neg hb hc),
      Real.arctan_inv_of_pos (div_pos_of_neg_of_neg ha hc),
      Real.arctan_inv_of_neg (div_neg_of_neg_of_pos ha hd)]
    ring
  
  have hE : ((∫ x : ℝ in a..b, ((x : ℂ) + (c : ℂ) * Complex.I)⁻¹)
        - ∫ x : ℝ in a..b, ((x : ℂ) + (d : ℂ) * Complex.I)⁻¹)
      + Complex.I * (∫ y : ℝ in c..d, ((b : ℂ) + (y : ℂ) * Complex.I)⁻¹)
      - Complex.I * (∫ y : ℝ in c..d, ((a : ℂ) + (y : ℂ) * Complex.I)⁻¹)
      = 2 * (Real.pi : ℂ) * Complex.I := by
    rw [HI a b c hc0, HI a b d hd0, VI c d b hb0, VI c d a ha0]
    have hSC : (((-(Real.arctan (b / c) - Real.arctan (a / c))
          + (Real.arctan (b / d) - Real.arctan (a / d)))
          + (Real.arctan (d / b) - Real.arctan (c / b))
          - (Real.arctan (d / a) - Real.arctan (c / a)) : ℝ) : ℂ)
        = ((2 * Real.pi : ℝ) : ℂ) := congrArg (fun r : ℝ => (r : ℂ)) hS
    push_cast at hSC ⊢
    linear_combination Complex.I * hSC
      + (((Real.log (b ^ 2 + c ^ 2) : ℝ) : ℂ) - ((Real.log (a ^ 2 + c ^ 2) : ℝ) : ℂ)
          - ((Real.log (b ^ 2 + d ^ 2) : ℝ) : ℂ) + ((Real.log (a ^ 2 + d ^ 2) : ℝ) : ℂ)) / 2
        * Complex.I_sq
  
  have hcont1 : Continuous (fun x : ℝ => (x : ℂ) + (c : ℂ) * Complex.I) :=
    Complex.continuous_ofReal.add continuous_const
  have hcont2 : Continuous (fun x : ℝ => (x : ℂ) + (d : ℂ) * Complex.I) :=
    Complex.continuous_ofReal.add continuous_const
  have hcont3 : Continuous (fun y : ℝ => (b : ℂ) + (y : ℂ) * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hcont4 : Continuous (fun y : ℝ => (a : ℂ) + (y : ℂ) * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hs1 : (∫ x : ℝ in a..b,
        h ((x : ℂ) + (c : ℂ) * Complex.I) / ((x : ℂ) + (c : ℂ) * Complex.I))
      = (∫ x : ℝ in a..b, (h ((x : ℂ) + (c : ℂ) * Complex.I) - h 0)
            / ((x : ℂ) + (c : ℂ) * Complex.I))
        + h 0 * ∫ x : ℝ in a..b, ((x : ℂ) + (c : ℂ) * Complex.I)⁻¹ :=
    hsplit a b (fun x : ℝ => (x : ℂ) + (c : ℂ) * Complex.I) hcont1
      (fun x hx => hmemQ _ (by rw [hreP]; exact hx) (by rw [himP]; exact Set.left_mem_uIcc))
      (fun x _ => hneI x c hc0)
  have hs2 : (∫ x : ℝ in a..b,
        h ((x : ℂ) + (d : ℂ) * Complex.I) / ((x : ℂ) + (d : ℂ) * Complex.I))
      = (∫ x : ℝ in a..b, (h ((x : ℂ) + (d : ℂ) * Complex.I) - h 0)
            / ((x : ℂ) + (d : ℂ) * Complex.I))
        + h 0 * ∫ x : ℝ in a..b, ((x : ℂ) + (d : ℂ) * Complex.I)⁻¹ :=
    hsplit a b (fun x : ℝ => (x : ℂ) + (d : ℂ) * Complex.I) hcont2
      (fun x hx => hmemQ _ (by rw [hreP]; exact hx) (by rw [himP]; exact Set.right_mem_uIcc))
      (fun x _ => hneI x d hd0)
  have hs3 : (∫ y : ℝ in c..d,
        h ((b : ℂ) + (y : ℂ) * Complex.I) / ((b : ℂ) + (y : ℂ) * Complex.I))
      = (∫ y : ℝ in c..d, (h ((b : ℂ) + (y : ℂ) * Complex.I) - h 0)
            / ((b : ℂ) + (y : ℂ) * Complex.I))
        + h 0 * ∫ y : ℝ in c..d, ((b : ℂ) + (y : ℂ) * Complex.I)⁻¹ :=
    hsplit c d (fun y : ℝ => (b : ℂ) + (y : ℂ) * Complex.I) hcont3
      (fun y hy => hmemQ _ (by rw [hreP]; exact Set.right_mem_uIcc) (by rw [himP]; exact hy))
      (fun y _ => hneR b y hb0)
  have hs4 : (∫ y : ℝ in c..d,
        h ((a : ℂ) + (y : ℂ) * Complex.I) / ((a : ℂ) + (y : ℂ) * Complex.I))
      = (∫ y : ℝ in c..d, (h ((a : ℂ) + (y : ℂ) * Complex.I) - h 0)
            / ((a : ℂ) + (y : ℂ) * Complex.I))
        + h 0 * ∫ y : ℝ in c..d, ((a : ℂ) + (y : ℂ) * Complex.I)⁻¹ :=
    hsplit c d (fun y : ℝ => (a : ℂ) + (y : ℂ) * Complex.I) hcont4
      (fun y hy => hmemQ _ (by rw [hreP]; exact Set.left_mem_uIcc) (by rw [himP]; exact hy))
      (fun y _ => hneR a y ha0)
  rw [hs1, hs2, hs3, hs4]
  linear_combination hrect + h 0 * hE

theorem truncated_laplace_differentiable (f : ℝ → ℝ) (M T : ℝ) (hf : Measurable f)
    (hM : ∀ t : ℝ, 0 ≤ t → |f t| ≤ M) (hT : 0 ≤ T) :
    Differentiable ℂ
      (fun z : ℂ => ∫ t in Set.Ioc (0 : ℝ) T, (f t : ℂ) * Complex.exp (-z * (t : ℂ))) :=
by
  
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (f 0)) (hM 0 le_rfl)
  
  have hre : ∀ (x : ℂ) (t : ℝ), (-x * (t : ℂ)).re = -x.re * t := by
    intro x t; simp
  
  have hEm : ∀ x : ℂ, Measurable (fun t : ℝ => Complex.exp (-x * (t : ℂ))) := by
    intro x
    exact (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)).measurable
  have hFm : ∀ x : ℂ,
      Measurable (fun t : ℝ => ((f t : ℝ) : ℂ) * Complex.exp (-x * (t : ℂ))) := by
    intro x
    exact (Complex.measurable_ofReal.comp hf).mul (hEm x)
  have hF'm : ∀ x : ℂ,
      Measurable (fun t : ℝ =>
        -(t : ℂ) * ((f t : ℝ) : ℂ) * Complex.exp (-x * (t : ℂ))) := by
    intro x
    exact ((Complex.measurable_ofReal.neg).mul
      (Complex.measurable_ofReal.comp hf)).mul (hEm x)
  
  have hderiv : ∀ (x : ℂ) (t : ℝ),
      HasDerivAt (fun y : ℂ => ((f t : ℝ) : ℂ) * Complex.exp (-y * (t : ℂ)))
        (-(t : ℂ) * ((f t : ℝ) : ℂ) * Complex.exp (-x * (t : ℂ))) x := by
    intro x t
    have h1 : HasDerivAt (fun y : ℂ => -y * (t : ℂ)) (-(t : ℂ)) x := by
      simpa using (hasDerivAt_id x).mul_const (-(t : ℂ))
    have h2 := (h1.cexp).const_mul (((f t : ℝ)) : ℂ)
    have heq : ((f t : ℝ) : ℂ) * (Complex.exp (-x * (t : ℂ)) * -(t : ℂ))
        = -(t : ℂ) * ((f t : ℝ) : ℂ) * Complex.exp (-x * (t : ℂ)) := by ring
    rw [heq] at h2
    exact h2
  intro z₀
  
  have hint : MeasureTheory.IntegrableOn
      (fun t : ℝ => ((f t : ℝ) : ℂ) * Complex.exp (-z₀ * (t : ℂ)))
      (Set.Ioc (0 : ℝ) T) := by
    have hc : MeasureTheory.IntegrableOn
        (fun _ : ℝ => M * Real.exp (|z₀.re| * T)) (Set.Ioc (0 : ℝ) T) := by
      apply MeasureTheory.integrableOn_const
      · rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
      · exact enorm_ne_top
    refine MeasureTheory.Integrable.mono' hc
      (hFm z₀).aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    rw [norm_mul, Complex.norm_exp, hre, Complex.norm_real, Real.norm_eq_abs]
    have ht0 : 0 < t := ht.1
    have htT : t ≤ T := ht.2
    have hfM : |f t| ≤ M := hM t ht0.le
    have hexp : Real.exp (-z₀.re * t) ≤ Real.exp (|z₀.re| * T) := by
      apply Real.exp_le_exp.mpr
      nlinarith [neg_le_abs z₀.re, abs_nonneg z₀.re, ht0.le, htT]
    exact mul_le_mul hfM hexp (Real.exp_pos _).le hM0
  
  have hbound : ∀ x ∈ Metric.ball z₀ 1, ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) T →
      ‖-(t : ℂ) * ((f t : ℝ) : ℂ) * Complex.exp (-x * (t : ℂ))‖
        ≤ T * M * Real.exp ((1 + |z₀.re|) * T) := by
    intro x hx t ht
    have ht0 : 0 < t := ht.1
    have htT : t ≤ T := ht.2
    have hT0 : (0 : ℝ) ≤ T := le_trans ht0.le htT
    have hd : ‖x - z₀‖ < 1 := by
      have hb := Metric.mem_ball.mp hx
      rwa [dist_eq_norm] at hb
    have hrele : |x.re - z₀.re| ≤ ‖x - z₀‖ := by
      have h := Complex.abs_re_le_norm (x - z₀)
      simpa using h
    have hneg : -x.re ≤ 1 + |z₀.re| := by
      have h1 : |x.re - z₀.re| < 1 := lt_of_le_of_lt hrele hd
      have h2 := (abs_lt.mp h1).1
      have h3 : -z₀.re ≤ |z₀.re| := neg_le_abs _
      linarith
    have hA1 : (1 : ℝ) ≤ 1 + |z₀.re| := by linarith [abs_nonneg z₀.re]
    have hexp : Real.exp (-x.re * t) ≤ Real.exp ((1 + |z₀.re|) * T) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hneg, ht0.le, htT, hA1]
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, hre, abs_of_pos ht0]
    have hfM : |f t| ≤ M := hM t ht0.le
    have step1 : t * |f t| ≤ T * M := mul_le_mul htT hfM (abs_nonneg _) hT0
    exact mul_le_mul step1 hexp (Real.exp_pos _).le (mul_nonneg hT0 hM0)
  
  have hbint : MeasureTheory.IntegrableOn
      (fun _ : ℝ => T * M * Real.exp ((1 + |z₀.re|) * T)) (Set.Ioc (0 : ℝ) T) := by
    apply MeasureTheory.integrableOn_const
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
    · exact enorm_ne_top
  
  have hbd : ∀ᵐ (a : ℝ) ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) T)),
      ∀ x ∈ Metric.ball z₀ 1,
        ‖-(a : ℂ) * ((f a : ℝ) : ℂ) * Complex.exp (-x * (a : ℂ))‖
          ≤ T * M * Real.exp ((1 + |z₀.re|) * T) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with a ha x hx
    exact hbound x hx a ha
  have hdrv : ∀ᵐ (a : ℝ) ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) T)),
      ∀ x ∈ Metric.ball z₀ 1,
        HasDerivAt (fun y : ℂ => ((f a : ℝ) : ℂ) * Complex.exp (-y * (a : ℂ)))
          (-(a : ℂ) * ((f a : ℝ) : ℂ) * Complex.exp (-x * (a : ℂ))) x :=
    Filter.Eventually.of_forall (fun a x _ => hderiv x a)
  
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) T))
    (F := fun (z : ℂ) (t : ℝ) => ((f t : ℝ) : ℂ) * Complex.exp (-z * (t : ℂ)))
    (F' := fun (z : ℂ) (t : ℝ) =>
      -(t : ℂ) * ((f t : ℝ) : ℂ) * Complex.exp (-z * (t : ℂ)))
    (x₀ := z₀) (s := Metric.ball z₀ 1)
    (bound := fun _ : ℝ => T * M * Real.exp ((1 + |z₀.re|) * T))
    (Metric.ball_mem_nhds z₀ one_pos)
    (Filter.Eventually.of_forall (fun x => (hFm x).aestronglyMeasurable))
    hint
    (hF'm z₀).aestronglyMeasurable
    hbd
    hbint
    hdrv
  exact key.2.differentiableAt

theorem laplace_tail_bound (f : ℝ → ℝ) (M T : ℝ) (hf : Measurable f)
    (hM : ∀ t : ℝ, 0 ≤ t → |f t| ≤ M) (hT : 0 ≤ T) (z : ℂ) (hz : 0 < z.re) :
    ‖(∫ t in Set.Ioi (0 : ℝ), (f t : ℂ) * Complex.exp (-z * (t : ℂ)))
        - ∫ t in Set.Ioc (0 : ℝ) T, (f t : ℂ) * Complex.exp (-z * (t : ℂ))‖
      ≤ M * Real.exp (-z.re * T) / z.re :=
by
  
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (f 0)) (hM 0 le_rfl)
  
  have hnorm : ∀ t : ℝ, ‖(f t : ℂ) * Complex.exp (-z * (t : ℂ))‖
      = |f t| * Real.exp (-z.re * t) := by
    intro t
    have hre : (-z * (t : ℂ)).re = -z.re * t := by simp
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, hre]
  have hbd : ∀ t : ℝ, 0 ≤ t → ‖(f t : ℂ) * Complex.exp (-z * (t : ℂ))‖
      ≤ M * Real.exp (-z.re * t) := by
    intro t ht
    rw [hnorm t]
    exact mul_le_mul_of_nonneg_right (hM t ht) (Real.exp_pos _).le
  
  have hmeas : Measurable (fun t : ℝ => (f t : ℂ) * Complex.exp (-z * (t : ℂ))) := by
    have h1 : Measurable (fun t : ℝ => ((f t : ℝ) : ℂ)) := Complex.measurable_ofReal.comp hf
    have h2 : Measurable (fun t : ℝ => Complex.exp (-z * (t : ℂ))) := by
      have hc : Continuous (fun t : ℝ => Complex.exp (-z * (t : ℂ))) := by fun_prop
      exact hc.measurable
    exact h1.mul h2
  have hint : MeasureTheory.IntegrableOn
      (fun t : ℝ => (f t : ℂ) * Complex.exp (-z * (t : ℂ))) (Set.Ioi (0 : ℝ)) := by
    have hdom : MeasureTheory.IntegrableOn (fun t : ℝ => M * Real.exp (-z.re * t))
        (Set.Ioi (0 : ℝ)) := (exp_neg_integrableOn_Ioi (0 : ℝ) hz).const_mul M
    refine MeasureTheory.Integrable.mono' hdom hmeas.aestronglyMeasurable ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_)
    exact hbd t (le_of_lt ht)
  
  have hIoc : MeasureTheory.IntegrableOn
      (fun t : ℝ => (f t : ℂ) * Complex.exp (-z * (t : ℂ))) (Set.Ioc (0 : ℝ) T) :=
    hint.mono_set Set.Ioc_subset_Ioi_self
  have hIoiT : MeasureTheory.IntegrableOn
      (fun t : ℝ => (f t : ℂ) * Complex.exp (-z * (t : ℂ))) (Set.Ioi T) :=
    hint.mono_set (Set.Ioi_subset_Ioi hT)
  have hsplit : (∫ t in Set.Ioi (0 : ℝ), (f t : ℂ) * Complex.exp (-z * (t : ℂ)))
      = (∫ t in Set.Ioc (0 : ℝ) T, (f t : ℂ) * Complex.exp (-z * (t : ℂ)))
        + ∫ t in Set.Ioi T, (f t : ℂ) * Complex.exp (-z * (t : ℂ)) := by
    rw [← MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      hIoc hIoiT, Set.Ioc_union_Ioi_eq_Ioi hT]
  have hdiff : (∫ t in Set.Ioi (0 : ℝ), (f t : ℂ) * Complex.exp (-z * (t : ℂ)))
        - (∫ t in Set.Ioc (0 : ℝ) T, (f t : ℂ) * Complex.exp (-z * (t : ℂ)))
      = ∫ t in Set.Ioi T, (f t : ℂ) * Complex.exp (-z * (t : ℂ)) := by
    rw [hsplit]; ring
  
  have hexp_tail : ∀ b : ℝ, 0 < b →
      (∫ t in Set.Ioi T, Real.exp (-b * t)) = Real.exp (-b * T) / b := by
    intro b hb
    have hbne : b ≠ 0 := ne_of_gt hb
    have hderiv : ∀ t : ℝ,
        HasDerivAt (fun s : ℝ => -Real.exp (-b * s) / b) (Real.exp (-b * t)) t := by
      intro t
      have h1 : HasDerivAt (fun s : ℝ => -b * s) (-b) t := by
        simpa using (hasDerivAt_id t).const_mul (-b)
      have h2 : HasDerivAt (fun s : ℝ => Real.exp (-b * s)) (Real.exp (-b * t) * (-b)) t :=
        h1.exp
      have h3 := (h2.neg).div_const b
      convert h3 using 1
      field_simp
    have hcont : Continuous (fun s : ℝ => -Real.exp (-b * s) / b) := by fun_prop
    have htend : Filter.Tendsto (fun s : ℝ => -Real.exp (-b * s) / b)
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun s : ℝ => b * s) Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop hb Filter.tendsto_id
      have h2 : Filter.Tendsto (fun s : ℝ => -b * s) Filter.atTop Filter.atBot := by
        have h2' := tendsto_neg_atTop_atBot.comp h1
        have heq : (fun s : ℝ => -b * s) = (Neg.neg ∘ fun s : ℝ => b * s) := by
          funext s; simp [Function.comp]
        rw [heq]
        exact h2'
      have h3 : Filter.Tendsto (fun s : ℝ => Real.exp (-b * s)) Filter.atTop (nhds 0) :=
        Real.tendsto_exp_atBot.comp h2
      simpa using (h3.neg).div_const b
    have key := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
      hcont.continuousWithinAt (fun x _ => hderiv x) (exp_neg_integrableOn_Ioi T hb) htend
    rw [key]
    ring
  
  have hdom2 : MeasureTheory.IntegrableOn (fun t : ℝ => M * Real.exp (-z.re * t))
      (Set.Ioi T) := (exp_neg_integrableOn_Ioi T hz).const_mul M
  have hbound : ‖∫ t in Set.Ioi T, (f t : ℂ) * Complex.exp (-z * (t : ℂ))‖
      ≤ ∫ t in Set.Ioi T, M * Real.exp (-z.re * t) := by
    refine MeasureTheory.norm_integral_le_of_norm_le hdom2 ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_)
    exact hbd t (le_trans hT (le_of_lt ht))
  
  have heval : (∫ t in Set.Ioi T, M * Real.exp (-z.re * t))
      = M * Real.exp (-z.re * T) / z.re := by
    rw [MeasureTheory.integral_const_mul, hexp_tail z.re hz, mul_div_assoc]
  
  rw [hdiff]
  rw [heval] at hbound
  exact hbound

theorem truncated_laplace_bound_of_re_neg (f : ℝ → ℝ) (M T : ℝ) (hf : Measurable f)
    (hM : ∀ t : ℝ, 0 ≤ t → |f t| ≤ M) (hT : 0 ≤ T) (z : ℂ) (hz : z.re < 0) :
    ‖(∫ t in Set.Ioc (0 : ℝ) T, (f t : ℂ) * Complex.exp (-z * (t : ℂ)))
        * Complex.exp (z * (T : ℂ))‖ ≤ M / |z.re| :=
by
  classical
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = -z.re := ⟨_, rfl⟩
  have hcpos : 0 < c := by rw [hcdef]; linarith
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (f 0)) (hM 0 le_rfl)
  have habs : |z.re| = c := by rw [hcdef]; exact abs_of_neg hz
  
  have hre : ∀ t : ℝ, (-z * (t : ℂ)).re = c * t := by
    intro t
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, hcdef]
    ring
  have hnormpt : ∀ t : ℝ,
      ‖(f t : ℂ) * Complex.exp (-z * (t : ℂ))‖ = |f t| * Real.exp (c * t) := by
    intro t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, hre t]
  
  have hintexp : (∫ t in Set.Ioc (0 : ℝ) T, Real.exp (c * t))
      = (Real.exp (c * T) - 1) / c := by
    have hcontE : Continuous (fun t : ℝ => Real.exp (c * t)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have hii : IntervalIntegrable (fun t : ℝ => Real.exp (c * t))
        MeasureTheory.volume 0 T := hcontE.intervalIntegrable _ _
    have hd : ∀ x ∈ Set.uIcc (0 : ℝ) T,
        HasDerivAt (fun t : ℝ => Real.exp (c * t) / c) (Real.exp (c * x)) x := by
      intro x _
      have h1 : HasDerivAt (fun t : ℝ => c * t) c x := by
        simpa using (hasDerivAt_id x).const_mul c
      have h2 : HasDerivAt (fun t : ℝ => Real.exp (c * t)) (Real.exp (c * x) * c) x := h1.exp
      have h3 := h2.div_const c
      have he : Real.exp (c * x) * c / c = Real.exp (c * x) := by field_simp
      rwa [he] at h3
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hii
    rw [← intervalIntegral.integral_of_le hT, hftc]
    simp only [mul_zero, Real.exp_zero]
    ring
  
  have h1 : ‖(∫ t in Set.Ioc (0 : ℝ) T, (f t : ℂ) * Complex.exp (-z * (t : ℂ)))‖
      ≤ ∫ t in Set.Ioc (0 : ℝ) T, ‖(f t : ℂ) * Complex.exp (-z * (t : ℂ))‖ :=
    MeasureTheory.norm_integral_le_integral_norm _
  
  have hcont : Continuous (fun t : ℝ => M * Real.exp (c * t)) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hgint : MeasureTheory.IntegrableOn (fun t : ℝ => M * Real.exp (c * t))
      (Set.Ioc (0 : ℝ) T) := hcont.integrableOn_Ioc
  have h2 : (∫ t in Set.Ioc (0 : ℝ) T, ‖(f t : ℂ) * Complex.exp (-z * (t : ℂ))‖)
      ≤ ∫ t in Set.Ioc (0 : ℝ) T, M * Real.exp (c * t) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hgint ?_
    · filter_upwards with t using norm_nonneg _
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      rw [hnormpt t]
      exact mul_le_mul_of_nonneg_right (hM t ht.1.le) (Real.exp_pos _).le
  have h3 : (∫ t in Set.Ioc (0 : ℝ) T, M * Real.exp (c * t))
      = M * ((Real.exp (c * T) - 1) / c) := by
    rw [MeasureTheory.integral_const_mul, hintexp]
  have hIle : ‖(∫ t in Set.Ioc (0 : ℝ) T, (f t : ℂ) * Complex.exp (-z * (t : ℂ)))‖
      ≤ M * ((Real.exp (c * T) - 1) / c) := by
    rw [← h3]; exact h1.trans h2
  
  have hexpnorm : ‖Complex.exp (z * (T : ℂ))‖ = Real.exp (-(c * T)) := by
    rw [Complex.norm_exp]
    congr 1
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hcdef]
    ring
  have hEpos : (0 : ℝ) < Real.exp (-(c * T)) := Real.exp_pos _
  have hprod : Real.exp (c * T) * Real.exp (-(c * T)) = 1 := by
    rw [← Real.exp_add]; simp
  rw [norm_mul, hexpnorm, habs]
  have hstep : ‖(∫ t in Set.Ioc (0 : ℝ) T, (f t : ℂ) * Complex.exp (-z * (t : ℂ)))‖
        * Real.exp (-(c * T))
      ≤ (M * ((Real.exp (c * T) - 1) / c)) * Real.exp (-(c * T)) :=
    mul_le_mul_of_nonneg_right hIle hEpos.le
  refine hstep.trans ?_
  have hmul : (Real.exp (c * T) - 1) * Real.exp (-(c * T)) = 1 - Real.exp (-(c * T)) := by
    rw [sub_mul, hprod, one_mul]
  have hnum : M * (1 - Real.exp (-(c * T))) ≤ M := by nlinarith
  calc (M * ((Real.exp (c * T) - 1) / c)) * Real.exp (-(c * T))
      = M * ((Real.exp (c * T) - 1) * Real.exp (-(c * T))) / c := by ring
    _ = M * (1 - Real.exp (-(c * T))) / c := by rw [hmul]
    _ ≤ M / c := by gcongr

theorem newman_kernel_bound (R : ℝ) (hR : 0 < R) (z : ℂ)
    (h1 : |z.re| ≤ R) (h2 : |z.im| ≤ R) (h3 : |z.re| = R ∨ |z.im| = R) :
    ‖1 / z + z / ((R : ℂ) ^ 2)‖ ≤ 4 * |z.re| / R ^ 2 :=
by
  have hRne : R ≠ 0 := ne_of_gt hR
  
  have hP : (0 : ℝ) < R ^ 2 := by positivity
  have hu2 : z.re ^ 2 ≤ R ^ 2 := by nlinarith [sq_abs z.re, abs_nonneg z.re, h1]
  have hv2 : z.im ^ 2 ≤ R ^ 2 := by nlinarith [sq_abs z.im, abs_nonneg z.im, h2]
  have hua : z.re ^ 2 ≤ |z.re| * R := by nlinarith [sq_abs z.re, abs_nonneg z.re, h1]
  
  have hPs : R ^ 2 ≤ z.re ^ 2 + z.im ^ 2 := by
    rcases h3 with h | h
    · have hq : z.re ^ 2 = R ^ 2 := by rw [← sq_abs z.re, h]
      nlinarith [sq_nonneg z.im]
    · have hq : z.im ^ 2 = R ^ 2 := by rw [← sq_abs z.im, h]
      nlinarith [sq_nonneg z.re]
  
  have hs : (0 : ℝ) < z.re ^ 2 + z.im ^ 2 := lt_of_lt_of_le hP hPs
  
  have hgap : z.re ^ 2 + z.im ^ 2 - R ^ 2 ≤ z.re ^ 2 := by linarith
  
  have hre : (1 / z + z / ((R : ℂ) ^ 2)).re
      = z.re * (1 / (z.re ^ 2 + z.im ^ 2) + 1 / R ^ 2) := by
    rw [Complex.add_re, one_div, Complex.inv_re, ← Complex.ofReal_pow,
      Complex.div_ofReal_re, Complex.normSq_apply]
    ring
  have him : (1 / z + z / ((R : ℂ) ^ 2)).im
      = z.im * (1 / R ^ 2 - 1 / (z.re ^ 2 + z.im ^ 2)) := by
    rw [Complex.add_im, one_div, Complex.inv_im, ← Complex.ofReal_pow,
      Complex.div_ofReal_im, Complex.normSq_apply]
    ring
  
  have hinv : 1 / (z.re ^ 2 + z.im ^ 2) ≤ 1 / R ^ 2 := one_div_le_one_div_of_le hP hPs
  have hinvs : (0 : ℝ) < 1 / (z.re ^ 2 + z.im ^ 2) := by positivity
  have hinvP : (0 : ℝ) < 1 / R ^ 2 := by positivity
  
  have hbre : |(1 / z + z / ((R : ℂ) ^ 2)).re| ≤ 2 * |z.re| / R ^ 2 := by
    rw [hre, abs_mul,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 / (z.re ^ 2 + z.im ^ 2) + 1 / R ^ 2)]
    calc |z.re| * (1 / (z.re ^ 2 + z.im ^ 2) + 1 / R ^ 2)
        ≤ |z.re| * (1 / R ^ 2 + 1 / R ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ = 2 * |z.re| / R ^ 2 := by ring
  
  have hgapk : 1 / R ^ 2 - 1 / (z.re ^ 2 + z.im ^ 2) ≤ z.re ^ 2 / (R ^ 2) ^ 2 := by
    have ha : (z.re ^ 2 + z.im ^ 2 - R ^ 2) * (R ^ 2 * R ^ 2)
        ≤ (z.re ^ 2 + z.im ^ 2 - R ^ 2) * (R ^ 2 * (z.re ^ 2 + z.im ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPs hP.le) (by linarith)
    have hb : (z.re ^ 2 + z.im ^ 2 - R ^ 2) * (R ^ 2 * (z.re ^ 2 + z.im ^ 2))
        ≤ z.re ^ 2 * (R ^ 2 * (z.re ^ 2 + z.im ^ 2)) :=
      mul_le_mul_of_nonneg_right hgap (by positivity)
    have hsne : z.re ^ 2 + z.im ^ 2 ≠ 0 := ne_of_gt hs
    rw [← sub_nonneg]
    have key : z.re ^ 2 / (R ^ 2) ^ 2 - (1 / R ^ 2 - 1 / (z.re ^ 2 + z.im ^ 2))
        = (z.re ^ 2 * (R ^ 2 * (z.re ^ 2 + z.im ^ 2))
            - (z.re ^ 2 + z.im ^ 2 - R ^ 2) * (R ^ 2 * R ^ 2))
          / ((R ^ 2) ^ 3 * (z.re ^ 2 + z.im ^ 2)) := by
      field_simp
      try ring
    rw [key]
    refine div_nonneg ?_ (by positivity)
    linarith
  
  have hbim : |(1 / z + z / ((R : ℂ) ^ 2)).im| ≤ |z.re| / R ^ 2 := by
    rw [him, abs_mul,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 / R ^ 2 - 1 / (z.re ^ 2 + z.im ^ 2))]
    have hstep : |z.im| * (1 / R ^ 2 - 1 / (z.re ^ 2 + z.im ^ 2))
        ≤ R * (z.re ^ 2 / (R ^ 2) ^ 2) :=
      mul_le_mul h2 hgapk (by linarith) hR.le
    have hfin : R * (z.re ^ 2 / (R ^ 2) ^ 2) ≤ |z.re| / R ^ 2 := by
      rw [← sub_nonneg]
      have key : |z.re| / R ^ 2 - R * (z.re ^ 2 / (R ^ 2) ^ 2)
          = (|z.re| * R - z.re ^ 2) / R ^ 3 := by
        field_simp
        try ring
      rw [key]
      exact div_nonneg (by linarith) (by positivity)
    linarith
  
  calc ‖1 / z + z / ((R : ℂ) ^ 2)‖
      ≤ |(1 / z + z / ((R : ℂ) ^ 2)).re| + |(1 / z + z / ((R : ℂ) ^ 2)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 * |z.re| / R ^ 2 + |z.re| / R ^ 2 := add_le_add hbre hbim
    _ ≤ 4 * |z.re| / R ^ 2 := by
        have hnn : (0 : ℝ) ≤ |z.re| / R ^ 2 := div_nonneg (abs_nonneg _) hP.le
        have heq : 4 * |z.re| / R ^ 2
            = 2 * |z.re| / R ^ 2 + |z.re| / R ^ 2 + |z.re| / R ^ 2 := by ring
        linarith

theorem rect_contour_push_left (R δ : ℝ) (hδ : 0 < δ) (hδR : δ < R) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F {z : ℂ | z ≠ 0}) :
    ((∫ x : ℝ in (-δ)..0, F ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
        - ∫ x : ℝ in (-δ)..0, F ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
      - Complex.I * ∫ y : ℝ in (-R)..R, F (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I)
    = ((∫ x : ℝ in (-R)..0, F ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
        - ∫ x : ℝ in (-R)..0, F ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
      - Complex.I * ∫ y : ℝ in (-R)..R, F (((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I) :=
by
  
  have hR : (0:ℝ) < R := lt_trans hδ hδR
  have hRne : R ≠ 0 := ne_of_gt hR
  have hnRne : (-R : ℝ) ≠ 0 := by intro h; exact hRne (by linarith)
  
  have hne_im : ∀ x c : ℝ, c ≠ 0 → ((x : ℂ) + (c : ℂ) * Complex.I) ≠ 0 := by
    intro x c hc hz
    exact hc (by simpa using congrArg Complex.im hz)
  
  have hcont : ∀ c : ℝ, c ≠ 0 →
      Continuous (fun x : ℝ => F ((x : ℂ) + (c : ℂ) * Complex.I)) := by
    intro c hc
    have hγ : Continuous (fun x : ℝ => (x : ℂ) + (c : ℂ) * Complex.I) :=
      Complex.continuous_ofReal.add continuous_const
    refine continuous_iff_continuousAt.mpr (fun x => ?_)
    have hmem : ((x : ℂ) + (c : ℂ) * Complex.I) ∈ {z : ℂ | z ≠ 0} := hne_im x c hc
    have hca : ContinuousAt F ((x : ℂ) + (c : ℂ) * Complex.I) :=
      (hF.differentiableAt (isOpen_ne.mem_nhds hmem)).continuousAt
    have hcomp : ContinuousAt (F ∘ fun x : ℝ => (x : ℂ) + (c : ℂ) * Complex.I) x :=
      ContinuousAt.comp hca hγ.continuousAt
    simpa [Function.comp] using hcomp
  
  have hii : ∀ (c a b : ℝ), c ≠ 0 →
      IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + (c : ℂ) * Complex.I))
        MeasureTheory.volume a b :=
    fun c a b hc => ((hcont c hc).continuousOn).intervalIntegrable
  
  have hclub_minus := intervalIntegral.integral_add_adjacent_intervals
      (hii (-R) (-R) (-δ) hnRne) (hii (-R) (-δ) 0 hnRne)
  have hclub_plus := intervalIntegral.integral_add_adjacent_intervals
      (hii R (-R) (-δ) hRne) (hii R (-δ) 0 hRne)
  
  have hd : DifferentiableOn ℂ F (Set.uIcc (-R : ℝ) (-δ) ×ℂ Set.uIcc (-R : ℝ) R) := by
    refine hF.mono ?_
    rw [Set.uIcc_of_le (by linarith : (-R:ℝ) ≤ -δ),
        Set.uIcc_of_le (by linarith : (-R:ℝ) ≤ R)]
    rintro w hw
    rw [Complex.mem_reProdIm, Set.mem_Icc, Set.mem_Icc] at hw
    show w ≠ 0
    intro hw0
    have hre0 : w.re = 0 := by rw [hw0]; simp
    linarith [hw.1.2]
  
  have hdia :
      ((∫ x : ℝ in (-R)..(-δ), F ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
          - ∫ x : ℝ in (-R)..(-δ), F ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
        + Complex.I * (∫ y : ℝ in (-R)..R, F (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I))
        - Complex.I * (∫ y : ℝ in (-R)..R, F (((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I)) = 0 :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
      (⟨-R, -R⟩ : ℂ) (⟨-δ, R⟩ : ℂ) hd
  
  linear_combination hclub_minus - hclub_plus - hdia

theorem newman_analytic_theorem (f : ℝ → ℝ) (M : ℝ) (hf : Measurable f)
    (hM : ∀ t : ℝ, 0 ≤ t → |f t| ≤ M)
    (U : Set ℂ) (G : ℂ → ℂ) (hU : IsOpen U) (hU0 : {z : ℂ | 0 ≤ z.re} ⊆ U)
    (hG : DifferentiableOn ℂ G U)
    (hlap : ∀ z : ℂ, 0 < z.re →
      (∫ t in Set.Ioi (0 : ℝ), (f t : ℂ) * Complex.exp (-z * (t : ℂ))) = G z) :
    ∃ L : ℝ,
      Filter.Tendsto (fun T : ℝ => ∫ t in Set.Ioc (0 : ℝ) T, f t) Filter.atTop (nhds L) :=
by
  classical
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (f 0)) (hM 0 le_rfl)
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hpine : Real.pi ≠ 0 := ne_of_gt hpi
  
  have hre_pt : ∀ x c : ℝ, ((x : ℂ) + (c : ℂ) * Complex.I).re = x := by intro x c; simp
  have him_pt : ∀ x c : ℝ, ((x : ℂ) + (c : ℂ) * Complex.I).im = c := by intro x c; simp
  have hne_im : ∀ x c : ℝ, c ≠ 0 → ((x : ℂ) + (c : ℂ) * Complex.I) ≠ 0 := by
    intro x c hc hz
    exact hc (by simpa using congrArg Complex.im hz)
  have hne_re : ∀ x c : ℝ, x ≠ 0 → ((x : ℂ) + (c : ℂ) * Complex.I) ≠ 0 := by
    intro x c hx hz
    exact hx (by simpa using congrArg Complex.re hz)
  have hGat : ∀ z ∈ U, ContinuousAt G z := fun z hz =>
    (hG.differentiableAt (hU.mem_nhds hz)).continuousAt
  have hsegcont : ∀ (F : ℂ → ℂ) (p : ℝ → ℂ), Continuous p → ∀ s : Set ℝ,
      (∀ x ∈ s, ContinuousAt F (p x)) → ContinuousOn (fun x : ℝ => F (p x)) s := by
    intro F p hp s h x hx
    exact (h x hx).comp_continuousWithinAt hp.continuousWithinAt
  
  have tri : ∀ (X Y Z : ℂ) (u v w : ℝ), ‖X‖ ≤ u → ‖Y‖ ≤ v → ‖Z‖ ≤ w →
      ‖(X - Y) + Complex.I * Z‖ ≤ u + v + w := by
    intro X Y Z u v w h1 h2 h3
    have e1 : ‖(X - Y) + Complex.I * Z‖ ≤ ‖X - Y‖ + ‖Complex.I * Z‖ := norm_add_le _ _
    have e2 : ‖X - Y‖ ≤ ‖X‖ + ‖Y‖ := norm_sub_le _ _
    have e3 : ‖Complex.I * Z‖ = ‖Z‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    linarith
  have tri' : ∀ (X Y Z : ℂ) (u v w : ℝ), ‖X‖ ≤ u → ‖Y‖ ≤ v → ‖Z‖ ≤ w →
      ‖(X - Y) - Complex.I * Z‖ ≤ u + v + w := by
    intro X Y Z u v w h1 h2 h3
    have e1 : ‖(X - Y) - Complex.I * Z‖ ≤ ‖X - Y‖ + ‖Complex.I * Z‖ := norm_sub_le _ _
    have e2 : ‖X - Y‖ ≤ ‖X‖ + ‖Y‖ := norm_sub_le _ _
    have e3 : ‖Complex.I * Z‖ = ‖Z‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    linarith
  
  obtain ⟨gT, hgT⟩ : ∃ gT : ℝ → ℂ → ℂ,
      gT = fun T z => ∫ t in Set.Ioc (0 : ℝ) T, (f t : ℂ) * Complex.exp (-z * (t : ℂ)) :=
    ⟨_, rfl⟩
  have hgTdiff : ∀ T : ℝ, 0 ≤ T → Differentiable ℂ (gT T) := by
    intro T hT
    simpa only [hgT] using truncated_laplace_differentiable f M T hf hM hT
  have hfInt : ∀ T : ℝ, MeasureTheory.IntegrableOn f (Set.Ioc (0 : ℝ) T) := by
    intro T
    have hc : MeasureTheory.IntegrableOn (fun _ : ℝ => M) (Set.Ioc (0 : ℝ) T) := by
      apply MeasureTheory.integrableOn_const
      · rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
      · exact enorm_ne_top
    refine MeasureTheory.Integrable.mono' hc hf.aestronglyMeasurable.restrict ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    simpa [Real.norm_eq_abs] using hM t (le_of_lt ht.1)
  have hreal : ∀ T : ℝ, (gT T 0).re = ∫ t in Set.Ioc (0 : ℝ) T, f t := by
    intro T
    have h1 : gT T 0 = ∫ t in Set.Ioc (0 : ℝ) T, ((f t : ℝ) : ℂ) := by simp [hgT]
    have h2 : (∫ t in Set.Ioc (0 : ℝ) T, ((f t : ℝ) : ℂ))
        = ((∫ t in Set.Ioc (0 : ℝ) T, f t : ℝ) : ℂ) := by
      simpa using ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM (hfInt T)
    rw [h1, h2, Complex.ofReal_re]
  
  have key : Filter.Tendsto (fun T : ℝ => gT T 0) Filter.atTop (nhds (G 0)) := by
    rw [Metric.tendsto_atTop]
    intro η hη
    have hηne : η ≠ 0 := ne_of_gt hη
    
    obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 32 * M / (Real.pi * η) + 1 := ⟨_, rfl⟩
    have hRnn : (0:ℝ) ≤ 32 * M / (Real.pi * η) :=
      div_nonneg (by linarith) (le_of_lt (mul_pos hpi hη))
    have hRpos : (0:ℝ) < R := by rw [hRdef]; linarith
    have hRne : R ≠ 0 := ne_of_gt hRpos
    have hRneC : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hRne
    have hpiR : Real.pi * η * R = 32 * M + Real.pi * η := by
      have hne : Real.pi * η ≠ 0 := ne_of_gt (mul_pos hpi hη)
      have h1 : Real.pi * η * (32 * M / (Real.pi * η)) = 32 * M := by field_simp
      rw [hRdef, mul_add, h1, mul_one]
    have h32 : 32 * M / R < Real.pi * η := by
      rw [div_lt_iff₀ hRpos]
      nlinarith [mul_pos hpi hη]
    
    obtain ⟨δ, hδpos, hδR, hδU⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < R ∧
        ∀ w : ℂ, -δ ≤ w.re → w.re < 0 → -R ≤ w.im → w.im ≤ R → w ∈ U := by
      have hJc : IsCompact ((fun y : ℝ => (y : ℂ) * Complex.I) '' Set.Icc (-R) R) :=
        isCompact_Icc.image (Complex.continuous_ofReal.mul continuous_const)
      have hJU : (fun y : ℝ => (y : ℂ) * Complex.I) '' Set.Icc (-R) R ⊆ U := by
        rintro _ ⟨y, _, rfl⟩
        exact hU0 (by simp)
      obtain ⟨δ₀, hδ₀, hδ₀U⟩ := hJc.exists_cthickening_subset_open hU hJU
      refine ⟨min δ₀ (R / 2), lt_min hδ₀ (by linarith),
        lt_of_le_of_lt (min_le_right _ _) (by linarith), ?_⟩
      intro w h1 h2 h3 h4
      refine hδ₀U (Metric.cthickening_mono (min_le_left δ₀ (R / 2)) _ ?_)
      refine Metric.mem_cthickening_of_dist_le w ((w.im : ℂ) * Complex.I) _ _
        ⟨w.im, ⟨h3, h4⟩, rfl⟩ ?_
      have hw : w - (w.im : ℂ) * Complex.I = ((w.re : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [dist_eq_norm, hw, Complex.norm_real, Real.norm_eq_abs, abs_of_neg h2]
      linarith
    have hδne : δ ≠ 0 := ne_of_gt hδpos
    
    have hQU : {z : ℂ | z.re ∈ Set.uIcc (-δ) R ∧ z.im ∈ Set.uIcc (-R) R} ⊆ U := by
      rintro w ⟨hw1, hw2⟩
      rw [Set.uIcc_of_le (by linarith : (-δ:ℝ) ≤ R), Set.mem_Icc] at hw1
      rw [Set.uIcc_of_le (by linarith : (-R:ℝ) ≤ R), Set.mem_Icc] at hw2
      by_cases h : 0 ≤ w.re
      · exact hU0 h
      · push_neg at h
        exact hδU w hw1.1 h hw2.1 hw2.2
    have hmemU : ∀ x c : ℝ, -δ ≤ x → x ≤ R → -R ≤ c → c ≤ R →
        ((x : ℂ) + (c : ℂ) * Complex.I) ∈ U := by
      intro x c h1 h2 h3 h4
      refine hQU ⟨?_, ?_⟩
      · rw [Set.uIcc_of_le (by linarith : (-δ:ℝ) ≤ R), hre_pt, Set.mem_Icc]
        exact ⟨h1, h2⟩
      · rw [Set.uIcc_of_le (by linarith : (-R:ℝ) ≤ R), him_pt, Set.mem_Icc]
        exact ⟨h3, h4⟩
    
    obtain ⟨kR, hkR⟩ : ∃ kR : ℂ → ℂ, kR = fun z : ℂ => 1 / z + z / (R : ℂ) ^ 2 := ⟨_, rfl⟩
    have hkRat : ∀ z : ℂ, z ≠ 0 → ContinuousAt kR z := by
      intro z hz
      rw [hkR]
      exact (continuousAt_const.div continuousAt_id hz).add (continuousAt_id.div_const _)
    have hkRbd : ∀ z : ℂ, |z.re| ≤ R → |z.im| ≤ R → (|z.re| = R ∨ |z.im| = R) →
        ‖kR z‖ ≤ 4 * |z.re| / R ^ 2 := by
      intro z h1 h2 h3
      simp only [hkR]
      exact newman_kernel_bound R hRpos z h1 h2 h3
    
    have hcm : Continuous (fun x : ℝ => (x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I) :=
      Complex.continuous_ofReal.add continuous_const
    have hcp : Continuous (fun x : ℝ => (x : ℂ) + ((R : ℝ) : ℂ) * Complex.I) :=
      Complex.continuous_ofReal.add continuous_const
    have hcvd : Continuous (fun y : ℝ => ((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hcvR : Continuous (fun y : ℝ => ((R : ℝ) : ℂ) + (y : ℂ) * Complex.I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    
    have rngA : ∀ x ∈ Set.uIcc (-δ) (0 : ℝ), -δ ≤ x ∧ x ≤ R := by
      intro x hx
      rw [Set.uIcc_of_le (by linarith : (-δ:ℝ) ≤ 0), Set.mem_Icc] at hx
      exact ⟨hx.1, by linarith [hx.2]⟩
    have rngB : ∀ x ∈ Set.uIcc (0 : ℝ) R, -δ ≤ x ∧ x ≤ R := by
      intro x hx
      rw [Set.uIcc_of_le hRpos.le, Set.mem_Icc] at hx
      exact ⟨by linarith [hx.1], hx.2⟩
    have okm : ∀ (a b : ℝ), (∀ x ∈ Set.uIcc a b, -δ ≤ x ∧ x ≤ R) →
        ∀ x ∈ Set.uIcc a b, ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I) ∈ U ∧
          ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I) ≠ 0 := by
      intro a b h x hx
      exact ⟨hmemU x (-R) (h x hx).1 (h x hx).2 le_rfl (by linarith),
        hne_im x (-R) (by intro hh; linarith)⟩
    have okp : ∀ (a b : ℝ), (∀ x ∈ Set.uIcc a b, -δ ≤ x ∧ x ≤ R) →
        ∀ x ∈ Set.uIcc a b, ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I) ∈ U ∧
          ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I) ≠ 0 := by
      intro a b h x hx
      exact ⟨hmemU x R (h x hx).1 (h x hx).2 (by linarith) le_rfl, hne_im x R hRne⟩
    have okv : ∀ y ∈ Set.uIcc (-R) R, (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I) ∈ U ∧
        (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
      intro y hy
      rw [Set.uIcc_of_le (by linarith : (-R:ℝ) ≤ R), Set.mem_Icc] at hy
      exact ⟨hmemU (-δ) y le_rfl (by linarith) hy.1 hy.2,
        hne_re (-δ) y (by intro hh; linarith)⟩
    
    obtain ⟨C, hC0, hCa, hCb, hCc⟩ : ∃ C : ℝ, 0 ≤ C ∧
        (∀ x ∈ Set.uIcc (-δ) (0 : ℝ),
          ‖G ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I) *
            kR ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)‖ ≤ C) ∧
        (∀ x ∈ Set.uIcc (-δ) (0 : ℝ),
          ‖G ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I) *
            kR ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I)‖ ≤ C) ∧
        (∀ y ∈ Set.uIcc (-R) R,
          ‖G (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I) *
            kR (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C) := by
      have cgk : ∀ (p : ℝ → ℂ) (s : Set ℝ), Continuous p →
          (∀ x ∈ s, p x ∈ U ∧ p x ≠ 0) →
          ContinuousOn (fun x : ℝ => G (p x) * kR (p x)) s := by
        intro p s hp h
        exact hsegcont (fun z => G z * kR z) p hp s
          (fun x hx => (hGat (p x) (h x hx).1).mul (hkRat (p x) (h x hx).2))
      obtain ⟨C1, hC1⟩ := isCompact_uIcc.exists_bound_of_continuousOn
        (cgk _ (Set.uIcc (-δ) (0:ℝ)) hcm (okm _ _ rngA))
      obtain ⟨C2, hC2⟩ := isCompact_uIcc.exists_bound_of_continuousOn
        (cgk _ (Set.uIcc (-δ) (0:ℝ)) hcp (okp _ _ rngA))
      obtain ⟨C3, hC3⟩ := isCompact_uIcc.exists_bound_of_continuousOn
        (cgk _ (Set.uIcc (-R) R) hcvd okv)
      have hle1 : C1 ≤ max 0 (max C1 (max C2 C3)) := le_max_of_le_right (le_max_left _ _)
      have hle2 : C2 ≤ max 0 (max C1 (max C2 C3)) :=
        le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
      have hle3 : C3 ≤ max 0 (max C1 (max C2 C3)) :=
        le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
      refine ⟨max 0 (max C1 (max C2 C3)), le_max_left _ _, ?_, ?_, ?_⟩
      · exact fun x hx => le_trans (hC1 x hx) hle1
      · exact fun x hx => le_trans (hC2 x hx) hle2
      · exact fun y hy => le_trans (hC3 y hy) hle3
    obtain ⟨C', hC'def⟩ : ∃ C' : ℝ, C' = 2 * C + 2 * R * C / δ := ⟨_, rfl⟩
    have hC'0 : 0 ≤ C' := by
      rw [hC'def]
      have : (0:ℝ) ≤ 2 * R * C / δ := div_nonneg (by nlinarith) hδpos.le
      linarith
    
    refine ⟨max 1 (C' / (Real.pi * η) + 1), ?_⟩
    intro T hT
    have hT1 : (1:ℝ) ≤ T := le_trans (le_max_left _ _) hT
    have hTpos : (0:ℝ) < T := by linarith
    have hT0 : (0:ℝ) ≤ T := le_of_lt hTpos
    have hTne : T ≠ 0 := ne_of_gt hTpos
    
    obtain ⟨PG, hPG⟩ : ∃ F : ℂ → ℂ,
        F = fun z : ℂ => G z * Complex.exp (z * (T : ℂ)) * kR z := ⟨_, rfl⟩
    obtain ⟨Pg, hPg⟩ : ∃ F : ℂ → ℂ,
        F = fun z : ℂ => gT T z * Complex.exp (z * (T : ℂ)) * kR z := ⟨_, rfl⟩
    obtain ⟨Hfun, hHfun⟩ : ∃ F : ℂ → ℂ,
        F = fun z : ℂ => (G z - gT T z) * Complex.exp (z * (T : ℂ)) *
          (1 + z ^ 2 / (R : ℂ) ^ 2) := ⟨_, rfl⟩
    have hexpc : Continuous (fun w : ℂ => Complex.exp (w * (T : ℂ))) :=
      Complex.continuous_exp.comp (continuous_id.mul continuous_const)
    have hPGat : ∀ z : ℂ, z ∈ U → z ≠ 0 → ContinuousAt PG z := by
      intro z hzU hz
      rw [hPG]
      exact ((hGat z hzU).mul hexpc.continuousAt).mul (hkRat z hz)
    have hPgat : ∀ z : ℂ, z ≠ 0 → ContinuousAt Pg z := by
      intro z hz
      rw [hPg]
      exact ((((hgTdiff T hT0) z).continuousAt).mul hexpc.continuousAt).mul (hkRat z hz)
    have hPgdiff : DifferentiableOn ℂ Pg {z : ℂ | z ≠ 0} := by
      rw [hPg]
      intro z hz
      have hz0 : z ≠ 0 := hz
      refine DifferentiableAt.differentiableWithinAt ?_
      have h1 : DifferentiableAt ℂ (gT T) z := hgTdiff T hT0 z
      have h2 : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (w * (T : ℂ))) z :=
        (Complex.differentiable_exp.comp (differentiable_id.mul_const ((T : ℂ)))) z
      have h3 : DifferentiableAt ℂ kR z := by
        simp only [hkR]
        exact ((differentiableAt_const (1:ℂ)).div differentiableAt_id hz0).add
          (differentiableAt_id.div_const _)
      exact (h1.mul h2).mul h3
    have hHdiff : DifferentiableOn ℂ Hfun U := by
      rw [hHfun]
      apply DifferentiableOn.mul
      · apply DifferentiableOn.mul
        · exact hG.sub (hgTdiff T hT0).differentiableOn
        · exact (Complex.differentiable_exp.comp (differentiable_id.mul_const _)).differentiableOn
      · exact (differentiableOn_const 1).add
          (((differentiable_id.pow 2).div_const _).differentiableOn)
    have hHfun0 : Hfun 0 = G 0 - gT T 0 := by simp [hHfun]
    
    have hcauchy := rect_cauchy_formula_at_zero (-δ) R (-R) R (by linarith) hRpos
      (by linarith) hRpos U hU Hfun hQU hHdiff
    
    have hPtEq : ∀ z : ℂ, z ≠ 0 → Hfun z / z = PG z - Pg z := by
      intro z hz
      simp only [hHfun, hPG, hPg, hkR]
      field_simp
    have hdiff_eq : ∀ z : ℂ, PG z - Pg z
        = (G z - gT T z) * Complex.exp (z * (T : ℂ)) * kR z := by
      intro z; simp only [hPG, hPg]; ring
    have hPGnorm : ∀ z : ℂ, ‖PG z‖ = ‖G z * kR z‖ * Real.exp (z.re * T) := by
      intro z
      have he : PG z = (G z * kR z) * Complex.exp (z * (T : ℂ)) := by
        simp only [hPG]; ring
      have hr : (z * (T : ℂ)).re = z.re * T := by simp
      rw [he, norm_mul, Complex.norm_exp, hr]
    
    have hbdplus : ∀ z : ℂ, 0 ≤ z.re → |z.re| ≤ R → |z.im| ≤ R →
        (|z.re| = R ∨ |z.im| = R) → ‖PG z - Pg z‖ ≤ 4 * M / R ^ 2 := by
      intro z hz0 h1 h2 h3
      have hker := hkRbd z h1 h2 h3
      rcases eq_or_lt_of_le hz0 with hre | hre
      · have hk0 : kR z = 0 := by
          have h4 : ‖kR z‖ ≤ 0 := by rw [← hre] at hker; simpa using hker
          exact norm_le_zero_iff.mp h4
        rw [hdiff_eq, hk0, mul_zero, norm_zero]
        exact div_nonneg (by linarith) (sq_nonneg R)
      · have hzne : z.re ≠ 0 := ne_of_gt hre
        have hGg : G z - gT T z
            = (∫ t in Set.Ioi (0:ℝ), (f t : ℂ) * Complex.exp (-z * (t : ℂ)))
              - ∫ t in Set.Ioc (0:ℝ) T, (f t : ℂ) * Complex.exp (-z * (t : ℂ)) := by
          rw [← hlap z hre, hgT]
        have htail := laplace_tail_bound f M T hf hM hT0 z hre
        rw [← hGg] at htail
        have hexpn : ‖Complex.exp (z * (T : ℂ))‖ = Real.exp (z.re * T) := by
          rw [Complex.norm_exp]
          congr 1
          simp
        have hkb : ‖kR z‖ ≤ 4 * z.re / R ^ 2 := by rwa [abs_of_pos hre] at hker
        have hBpos : (0:ℝ) < Real.exp (z.re * T) := Real.exp_pos _
        have hnn : (0:ℝ) ≤ M * Real.exp (-z.re * T) / z.re :=
          div_nonneg (mul_nonneg hM0 (Real.exp_pos _).le) hre.le
        have he1 : Real.exp (-z.re * T) * Real.exp (z.re * T) = 1 := by
          rw [← Real.exp_add]; simp
        rw [hdiff_eq, norm_mul, norm_mul, hexpn]
        calc ‖G z - gT T z‖ * Real.exp (z.re * T) * ‖kR z‖
            ≤ (M * Real.exp (-z.re * T) / z.re) * Real.exp (z.re * T) * (4 * z.re / R ^ 2) := by
              refine mul_le_mul ?_ hkb (norm_nonneg _) (mul_nonneg hnn hBpos.le)
              exact mul_le_mul_of_nonneg_right htail hBpos.le
          _ = (M * (Real.exp (-z.re * T) * Real.exp (z.re * T)) * (4 * z.re))
                / (z.re * R ^ 2) := by ring
          _ = 4 * M / R ^ 2 := by rw [he1]; field_simp
    have hbdminus : ∀ z : ℂ, z.re ≤ 0 → |z.re| ≤ R → |z.im| ≤ R →
        (|z.re| = R ∨ |z.im| = R) → ‖Pg z‖ ≤ 4 * M / R ^ 2 := by
      intro z hz0 h1 h2 h3
      have hker := hkRbd z h1 h2 h3
      rcases eq_or_lt_of_le hz0 with hre | hre
      · have hk0 : kR z = 0 := by
          have h4 : ‖kR z‖ ≤ 0 := by rw [hre] at hker; simpa using hker
          exact norm_le_zero_iff.mp h4
        simp only [hPg]
        rw [hk0, mul_zero, norm_zero]
        exact div_nonneg (by linarith) (sq_nonneg R)
      · have habs : (0:ℝ) < |z.re| := abs_pos.mpr (ne_of_lt hre)
        have hs4 := truncated_laplace_bound_of_re_neg f M T hf hM hT0 z hre
        have heq : gT T z * Complex.exp (z * (T : ℂ))
            = (∫ t in Set.Ioc (0:ℝ) T, (f t : ℂ) * Complex.exp (-z * (t : ℂ)))
              * Complex.exp (z * (T : ℂ)) := by rw [hgT]
        have hsplit : Pg z = (gT T z * Complex.exp (z * (T : ℂ))) * kR z := by
          simp only [hPg]
        rw [hsplit, norm_mul]
        calc ‖gT T z * Complex.exp (z * (T : ℂ))‖ * ‖kR z‖
            ≤ (M / |z.re|) * (4 * |z.re| / R ^ 2) := by
              refine mul_le_mul ?_ hker (norm_nonneg _) (div_nonneg hM0 habs.le)
              rw [heq]; exact hs4
          _ = 4 * M / R ^ 2 := by
              field_simp
    
    have hbd_h : ∀ c x : ℝ, |c| = R → |x| ≤ R → 0 ≤ x →
        ‖PG ((x : ℂ) + (c : ℂ) * Complex.I) - Pg ((x : ℂ) + (c : ℂ) * Complex.I)‖
          ≤ 4 * M / R ^ 2 := by
      intro c x hc hx hx0
      refine hbdplus _ ?_ ?_ ?_ ?_
      · rw [hre_pt]; exact hx0
      · rw [hre_pt]; exact hx
      · rw [him_pt]; exact le_of_eq hc
      · rw [him_pt]; exact Or.inr hc
    have hbd_v : ∀ y : ℝ, |y| ≤ R →
        ‖PG (((R : ℝ) : ℂ) + (y : ℂ) * Complex.I)
          - Pg (((R : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖ ≤ 4 * M / R ^ 2 := by
      intro y hy
      refine hbdplus _ ?_ ?_ ?_ ?_
      · rw [hre_pt]; exact hRpos.le
      · rw [hre_pt, abs_of_pos hRpos]
      · rw [him_pt]; exact hy
      · rw [hre_pt, abs_of_pos hRpos]; exact Or.inl rfl
    have hbdg_h : ∀ c x : ℝ, |c| = R → |x| ≤ R → x ≤ 0 →
        ‖Pg ((x : ℂ) + (c : ℂ) * Complex.I)‖ ≤ 4 * M / R ^ 2 := by
      intro c x hc hx hx0
      refine hbdminus _ ?_ ?_ ?_ ?_
      · rw [hre_pt]; exact hx0
      · rw [hre_pt]; exact hx
      · rw [him_pt]; exact le_of_eq hc
      · rw [him_pt]; exact Or.inr hc
    have hbdg_v : ∀ y : ℝ, |y| ≤ R →
        ‖Pg (((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖ ≤ 4 * M / R ^ 2 := by
      intro y hy
      have hRabs : |(-R : ℝ)| = R := by rw [abs_neg, abs_of_pos hRpos]
      refine hbdminus _ ?_ ?_ ?_ ?_
      · rw [hre_pt]; linarith
      · rw [hre_pt]; exact le_of_eq hRabs
      · rw [him_pt]; exact hy
      · rw [hre_pt]; exact Or.inl hRabs
    
    have contG : ∀ (p : ℝ → ℂ) (a b : ℝ), Continuous p →
        (∀ x ∈ Set.uIcc a b, p x ∈ U ∧ p x ≠ 0) →
        ContinuousOn (fun x : ℝ => PG (p x)) (Set.uIcc a b) :=
      fun p a b hp h => hsegcont PG p hp _ (fun x hx => hPGat (p x) (h x hx).1 (h x hx).2)
    have contg : ∀ (p : ℝ → ℂ) (a b : ℝ), Continuous p →
        (∀ x ∈ Set.uIcc a b, p x ≠ 0) →
        ContinuousOn (fun x : ℝ => Pg (p x)) (Set.uIcc a b) :=
      fun p a b hp h => hsegcont Pg p hp _ (fun x hx => hPgat (p x) (h x hx))
    have cGmA := contG _ (-δ) (0:ℝ) hcm (okm _ _ rngA)
    have cgmA := contg _ (-δ) (0:ℝ) hcm (fun x hx => (okm _ _ rngA x hx).2)
    have cGmB := contG _ (0:ℝ) R hcm (okm _ _ rngB)
    have cgmB := contg _ (0:ℝ) R hcm (fun x hx => (okm _ _ rngB x hx).2)
    have cGpA := contG _ (-δ) (0:ℝ) hcp (okp _ _ rngA)
    have cgpA := contg _ (-δ) (0:ℝ) hcp (fun x hx => (okp _ _ rngA x hx).2)
    have cGpB := contG _ (0:ℝ) R hcp (okp _ _ rngB)
    have cgpB := contg _ (0:ℝ) R hcp (fun x hx => (okp _ _ rngB x hx).2)
    have cGv := contG _ (-R) R hcvd okv
    have cgv := contg _ (-R) R hcvd (fun y hy => (okv y hy).2)
    
    have hcong1 : (∫ x : ℝ in (-δ)..R, Hfun ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)
          / ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
        = ∫ x : ℝ in (-δ)..R, (PG ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)
            - Pg ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)) := by
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      exact hPtEq _ (hne_im x (-R) (by intro hh; linarith))
    have hcong2 : (∫ x : ℝ in (-δ)..R, Hfun ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I)
          / ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
        = ∫ x : ℝ in (-δ)..R, (PG ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I)
            - Pg ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I)) := by
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      exact hPtEq _ (hne_im x R hRne)
    have hcong3 : (∫ y : ℝ in (-R)..R, Hfun (((R : ℝ) : ℂ) + (y : ℂ) * Complex.I)
          / (((R : ℝ) : ℂ) + (y : ℂ) * Complex.I))
        = ∫ y : ℝ in (-R)..R, (PG (((R : ℝ) : ℂ) + (y : ℂ) * Complex.I)
            - Pg (((R : ℝ) : ℂ) + (y : ℂ) * Complex.I)) := by
      refine intervalIntegral.integral_congr (fun y _ => ?_)
      exact hPtEq _ (hne_re R y hRne)
    have hcong4 : (∫ y : ℝ in (-R)..R, Hfun (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I)
          / (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I))
        = ∫ y : ℝ in (-R)..R, (PG (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I)
            - Pg (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I)) := by
      refine intervalIntegral.integral_congr (fun y _ => ?_)
      exact hPtEq _ (hne_re (-δ) y (by intro hh; linarith))
    
    have hadjm : ((∫ x : ℝ in (-δ)..(0:ℝ), (PG ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)
            - Pg ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)))
          + ∫ x : ℝ in (0:ℝ)..R, (PG ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)
            - Pg ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)))
        = ∫ x : ℝ in (-δ)..R, (PG ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)
            - Pg ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)) :=
      intervalIntegral.integral_add_adjacent_intervals
        (cGmA.sub cgmA).intervalIntegrable (cGmB.sub cgmB).intervalIntegrable
    have hadjp : ((∫ x : ℝ in (-δ)..(0:ℝ), (PG ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I)
            - Pg ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I)))
          + ∫ x : ℝ in (0:ℝ)..R, (PG ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I)
            - Pg ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I)))
        = ∫ x : ℝ in (-δ)..R, (PG ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I)
            - Pg ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I)) :=
      intervalIntegral.integral_add_adjacent_intervals
        (cGpA.sub cgpA).intervalIntegrable (cGpB.sub cgpB).intervalIntegrable
    
    have hsubA : (∫ x : ℝ in (-δ)..(0:ℝ), (PG ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)
          - Pg ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)))
        = (∫ x : ℝ in (-δ)..(0:ℝ), PG ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
          - ∫ x : ℝ in (-δ)..(0:ℝ), Pg ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I) :=
      intervalIntegral.integral_sub cGmA.intervalIntegrable cgmA.intervalIntegrable
    have hsubB : (∫ x : ℝ in (-δ)..(0:ℝ), (PG ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I)
          - Pg ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I)))
        = (∫ x : ℝ in (-δ)..(0:ℝ), PG ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
          - ∫ x : ℝ in (-δ)..(0:ℝ), Pg ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I) :=
      intervalIntegral.integral_sub cGpA.intervalIntegrable cgpA.intervalIntegrable
    have hsubV : (∫ y : ℝ in (-R)..R, (PG (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I)
          - Pg (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I)))
        = (∫ y : ℝ in (-R)..R, PG (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I))
          - ∫ y : ℝ in (-R)..R, Pg (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I) :=
      intervalIntegral.integral_sub cGv.intervalIntegrable cgv.intervalIntegrable
    
    obtain ⟨Aplus, hAplus⟩ : ∃ w : ℂ, w =
        ((∫ x : ℝ in (0:ℝ)..R, (PG ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)
            - Pg ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)))
          - ∫ x : ℝ in (0:ℝ)..R, (PG ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I)
            - Pg ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I)))
        + Complex.I * ∫ y : ℝ in (-R)..R, (PG (((R : ℝ) : ℂ) + (y : ℂ) * Complex.I)
            - Pg (((R : ℝ) : ℂ) + (y : ℂ) * Complex.I)) := ⟨_, rfl⟩
    obtain ⟨AmG, hAmG⟩ : ∃ w : ℂ, w =
        ((∫ x : ℝ in (-δ)..(0:ℝ), PG ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
          - ∫ x : ℝ in (-δ)..(0:ℝ), PG ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
        - Complex.I * ∫ y : ℝ in (-R)..R, PG (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I) := ⟨_, rfl⟩
    obtain ⟨Amg, hAmg⟩ : ∃ w : ℂ, w =
        ((∫ x : ℝ in (-δ)..(0:ℝ), Pg ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
          - ∫ x : ℝ in (-δ)..(0:ℝ), Pg ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
        - Complex.I * ∫ y : ℝ in (-R)..R, Pg (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I) := ⟨_, rfl⟩
    
    have hApbd : ‖Aplus‖ ≤ 16 * M / R := by
      have hb1 : ‖∫ x : ℝ in (0:ℝ)..R, (PG ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)
            - Pg ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))‖ ≤ (4 * M / R ^ 2) * |R - 0| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => ?_)
        rw [Set.uIoc_of_le hRpos.le] at hx
        exact hbd_h (-R) x (by rw [abs_neg, abs_of_pos hRpos])
          (by rw [abs_of_pos hx.1]; exact hx.2) hx.1.le
      have hb2 : ‖∫ x : ℝ in (0:ℝ)..R, (PG ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I)
            - Pg ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))‖ ≤ (4 * M / R ^ 2) * |R - 0| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => ?_)
        rw [Set.uIoc_of_le hRpos.le] at hx
        exact hbd_h R x (abs_of_pos hRpos) (by rw [abs_of_pos hx.1]; exact hx.2) hx.1.le
      have hb3 : ‖∫ y : ℝ in (-R)..R, (PG (((R : ℝ) : ℂ) + (y : ℂ) * Complex.I)
            - Pg (((R : ℝ) : ℂ) + (y : ℂ) * Complex.I))‖
          ≤ (4 * M / R ^ 2) * |R - (-R)| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const (fun y hy => ?_)
        rw [Set.uIoc_of_le (by linarith : (-R:ℝ) ≤ R)] at hy
        exact hbd_v y (abs_le.mpr ⟨hy.1.le, hy.2⟩)
      rw [hAplus]
      refine le_trans (tri _ _ _ _ _ _ hb1 hb2 hb3) (le_of_eq ?_)
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ R - 0),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ R - -R)]
      field_simp
      ring
    
    have hAmgbd : ‖Amg‖ ≤ 16 * M / R := by
      rw [hAmg, rect_contour_push_left R δ hδpos hδR Pg hPgdiff]
      have hb1 : ‖∫ x : ℝ in (-R)..(0:ℝ), Pg ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)‖
          ≤ (4 * M / R ^ 2) * |0 - (-R)| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => ?_)
        rw [Set.uIoc_of_le (by linarith : (-R:ℝ) ≤ 0)] at hx
        exact hbdg_h (-R) x (by rw [abs_neg, abs_of_pos hRpos])
          (abs_le.mpr ⟨hx.1.le, by linarith [hx.2]⟩) hx.2
      have hb2 : ‖∫ x : ℝ in (-R)..(0:ℝ), Pg ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I)‖
          ≤ (4 * M / R ^ 2) * |0 - (-R)| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => ?_)
        rw [Set.uIoc_of_le (by linarith : (-R:ℝ) ≤ 0)] at hx
        exact hbdg_h R x (abs_of_pos hRpos)
          (abs_le.mpr ⟨hx.1.le, by linarith [hx.2]⟩) hx.2
      have hb3 : ‖∫ y : ℝ in (-R)..R, Pg (((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖
          ≤ (4 * M / R ^ 2) * |R - (-R)| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const (fun y hy => ?_)
        rw [Set.uIoc_of_le (by linarith : (-R:ℝ) ≤ R)] at hy
        exact hbdg_v y (abs_le.mpr ⟨hy.1.le, hy.2⟩)
      refine le_trans (tri' _ _ _ _ _ _ hb1 hb2 hb3) (le_of_eq ?_)
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 0 - -R),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ R - -R)]
      field_simp
      ring
    
    have hexple : Real.exp (-δ * T) ≤ 1 / (δ * T) := by
      have h2 : (0:ℝ) < δ * T := mul_pos hδpos hTpos
      have h1 : δ * T ≤ Real.exp (δ * T) := by linarith [Real.add_one_le_exp (δ * T)]
      have h3 : Real.exp (-δ * T) = (Real.exp (δ * T))⁻¹ := by
        rw [show (-δ) * T = -(δ * T) by ring, Real.exp_neg]
      rw [h3, one_div]
      exact inv_anti₀ h2 h1
    have hhoriz : ∀ c : ℝ,
        (∀ x ∈ Set.uIcc (-δ) (0:ℝ),
          ‖G ((x : ℂ) + (c : ℂ) * Complex.I) * kR ((x : ℂ) + (c : ℂ) * Complex.I)‖ ≤ C) →
        ContinuousOn (fun x : ℝ => PG ((x : ℂ) + (c : ℂ) * Complex.I)) (Set.uIcc (-δ) (0:ℝ)) →
        ‖∫ x : ℝ in (-δ)..(0:ℝ), PG ((x : ℂ) + (c : ℂ) * Complex.I)‖ ≤ C / T := by
      intro c hCbd hcont
      have hδ0 : (-δ:ℝ) ≤ 0 := by linarith
      have hcE : Continuous (fun x : ℝ => C * Real.exp (x * T)) :=
        continuous_const.mul (Real.continuous_exp.comp (continuous_id.mul continuous_const))
      have hii1 : IntervalIntegrable (fun x : ℝ => ‖PG ((x : ℂ) + (c : ℂ) * Complex.I)‖)
          MeasureTheory.volume (-δ) 0 := hcont.norm.intervalIntegrable
      have hii2 : IntervalIntegrable (fun x : ℝ => C * Real.exp (x * T))
          MeasureTheory.volume (-δ) 0 := hcE.intervalIntegrable _ _
      have step1 : ‖∫ x : ℝ in (-δ)..(0:ℝ), PG ((x : ℂ) + (c : ℂ) * Complex.I)‖
          ≤ ∫ x : ℝ in (-δ)..(0:ℝ), ‖PG ((x : ℂ) + (c : ℂ) * Complex.I)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hδ0
      have step2 : (∫ x : ℝ in (-δ)..(0:ℝ), ‖PG ((x : ℂ) + (c : ℂ) * Complex.I)‖)
          ≤ ∫ x : ℝ in (-δ)..(0:ℝ), C * Real.exp (x * T) := by
        refine intervalIntegral.integral_mono_on hδ0 hii1 hii2 (fun x hx => ?_)
        have hxu : x ∈ Set.uIcc (-δ) (0:ℝ) := by rw [Set.uIcc_of_le hδ0]; exact hx
        rw [hPGnorm, hre_pt]
        exact mul_le_mul_of_nonneg_right (hCbd x hxu) (Real.exp_pos _).le
      have step3 : (∫ x : ℝ in (-δ)..(0:ℝ), C * Real.exp (x * T))
          = C * (1 - Real.exp (-δ * T)) / T := by
        have hd : ∀ x ∈ Set.uIcc (-δ) (0:ℝ),
            HasDerivAt (fun x : ℝ => C * Real.exp (x * T) / T) (C * Real.exp (x * T)) x := by
          intro x _
          have h1 : HasDerivAt (fun x : ℝ => x * T) T x := by
            simpa using (hasDerivAt_id x).mul_const T
          have h2 : HasDerivAt (fun x : ℝ => Real.exp (x * T)) (Real.exp (x * T) * T) x := h1.exp
          have h3 := (h2.const_mul C).div_const T
          simpa [mul_comm, mul_assoc, mul_div_assoc, hTne] using h3
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hii2]
        simp only [zero_mul, Real.exp_zero, mul_one]
        ring
      have step4 : C * (1 - Real.exp (-δ * T)) / T ≤ C / T := by
        have h1 : C * (1 - Real.exp (-δ * T)) ≤ C := by
          nlinarith [Real.exp_pos (-δ * T), hC0]
        have hTi : (0:ℝ) ≤ T⁻¹ := (inv_pos.mpr hTpos).le
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right h1 hTi
      linarith [step1, step2, step3, step4]
    have hvert : ‖∫ y : ℝ in (-R)..R, PG (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ 2 * R * C / (δ * T) := by
      have hb : ‖∫ y : ℝ in (-R)..R, PG (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖
          ≤ (C * Real.exp (-δ * T)) * |R - (-R)| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const (fun y hy => ?_)
        rw [Set.uIoc_of_le (by linarith : (-R:ℝ) ≤ R)] at hy
        have hyu : y ∈ Set.uIcc (-R) R := by
          rw [Set.uIcc_of_le (by linarith : (-R:ℝ) ≤ R), Set.mem_Icc]
          exact ⟨hy.1.le, hy.2⟩
        rw [hPGnorm, hre_pt]
        exact mul_le_mul_of_nonneg_right (hCc y hyu) (Real.exp_pos _).le
      have habs : |R - (-R)| = 2 * R := by
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ R - -R)]; ring
      rw [habs] at hb
      have hstep : (C * Real.exp (-δ * T)) * (2 * R) ≤ (C * (1 / (δ * T))) * (2 * R) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexple hC0) (by linarith)
      have heq : (C * (1 / (δ * T))) * (2 * R) = 2 * R * C / (δ * T) := by
        field_simp
      linarith [hb, hstep, heq]
    have hAmGbd : ‖AmG‖ ≤ C' / T := by
      rw [hAmG]
      refine le_trans (tri' _ _ _ _ _ _ (hhoriz (-R) hCa cGmA) (hhoriz R hCb cGpA) hvert)
        (le_of_eq ?_)
      rw [hC'def]
      field_simp
      ring
    
    have hmain : ‖(2:ℂ) * (Real.pi : ℂ) * Complex.I * (G 0 - gT T 0)‖
        ≤ 32 * M / R + C' / T := by
      have h0 : (2:ℂ) * (Real.pi : ℂ) * Complex.I * (G 0 - gT T 0) = Aplus + AmG - Amg := by
        rw [← hHfun0, ← hcauchy, hAplus, hAmG, hAmg, hcong1, hcong2, hcong3, hcong4,
          ← hadjm, ← hadjp, hsubA, hsubB, hsubV]
        ring
      rw [h0]
      calc ‖Aplus + AmG - Amg‖ ≤ ‖Aplus + AmG‖ + ‖Amg‖ := norm_sub_le _ _
        _ ≤ (‖Aplus‖ + ‖AmG‖) + ‖Amg‖ := by linarith [norm_add_le Aplus AmG]
        _ ≤ (16 * M / R + C' / T) + 16 * M / R :=
            add_le_add (add_le_add hApbd hAmGbd) hAmgbd
        _ = 32 * M / R + C' / T := by ring
    have hnorm2pi : ‖(2:ℂ) * (Real.pi : ℂ) * Complex.I * (G 0 - gT T 0)‖
        = 2 * Real.pi * ‖G 0 - gT T 0‖ := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hpi]
      norm_num
    rw [hnorm2pi] at hmain
    
    have hC'lt : C' < Real.pi * η * T := by
      have h1 : C' / (Real.pi * η) + 1 ≤ T := le_trans (le_max_right _ _) hT
      have h2 : (0:ℝ) < Real.pi * η := mul_pos hpi hη
      have h3 : C' / (Real.pi * η) * (Real.pi * η) = C' := by field_simp
      nlinarith [h1, h2, h3]
    have hC'2 : C' / T < Real.pi * η := by
      rw [div_lt_iff₀ hTpos]
      nlinarith [hC'lt]
    
    rw [dist_eq_norm, norm_sub_rev]
    nlinarith [hmain, h32, hC'2, hpi, norm_nonneg (G 0 - gT T 0)]
  refine ⟨(G 0).re, ?_⟩
  have hcomp : Filter.Tendsto (fun T : ℝ => (gT T 0).re) Filter.atTop (nhds (G 0).re) :=
    (Complex.continuous_re.tendsto (G 0)).comp key
  have hfe : (fun T : ℝ => (gT T 0).re) = fun T : ℝ => ∫ t in Set.Ioc (0:ℝ) T, f t :=
    funext hreal
  rwa [hfe] at hcomp

theorem upper_bound_of_tendsto_log_integral (h : ℝ → ℝ) (hmono : Monotone h) (L : ℝ)
    (hconv : Filter.Tendsto
      (fun T : ℝ => ∫ u in Set.Ioc (0 : ℝ) T, (h (Real.exp u) * Real.exp (-u) - 1))
      Filter.atTop (nhds L))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in Filter.atTop, h x ≤ (1 + ε) * x :=
by
  have hone : (0 : ℝ) < 1 + ε := by linarith
  have hcontE : Continuous (fun u : ℝ => Real.exp (-u)) :=
    Real.continuous_exp.comp continuous_neg
  
  have hmono2 : Monotone (fun u : ℝ => h (Real.exp u)) := hmono.comp Real.exp_monotone
  have s1 : ∀ a b : ℝ,
      IntervalIntegrable (fun u : ℝ => h (Real.exp u) * Real.exp (-u) - 1)
        MeasureTheory.volume a b := by
    intro a b
    have h1 : IntervalIntegrable (fun u : ℝ => h (Real.exp u)) MeasureTheory.volume a b :=
      (hmono2.monotoneOn (Set.uIcc a b)).intervalIntegrable
    have hc : ContinuousOn (fun u : ℝ => Real.exp (-u)) (Set.uIcc a b) := hcontE.continuousOn
    exact (h1.mul_continuousOn hc).sub intervalIntegrable_const
  
  have s2 : ∀ C a b : ℝ,
      (∫ u in a..b, (C * Real.exp (-u) - 1))
        = C * (Real.exp (-a) - Real.exp (-b)) - (b - a) := by
    intro C a b
    have hG : ∀ u : ℝ,
        HasDerivAt (fun v : ℝ => -C * Real.exp (-v) - v) (C * Real.exp (-u) - 1) u := by
      intro u
      have hn : HasDerivAt (fun v : ℝ => -v) (-1 : ℝ) u := (hasDerivAt_id u).neg
      have he : HasDerivAt (fun v : ℝ => Real.exp (-v)) (Real.exp (-u) * (-1)) u := hn.exp
      have h2 : HasDerivAt (fun v : ℝ => -C * Real.exp (-v) - v)
          (-C * (Real.exp (-u) * (-1)) - 1) u := (he.const_mul (-C)).sub (hasDerivAt_id u)
      convert h2 using 1
      ring
    have hcont : Continuous (fun u : ℝ => C * Real.exp (-u) - 1) :=
      (continuous_const.mul hcontE).sub continuous_const
    have key := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun v : ℝ => -C * Real.exp (-v) - v)
      (f' := fun u : ℝ => C * Real.exp (-u) - 1)
      (fun x _ => hG x) (hcont.intervalIntegrable a b)
    rw [key]
    ring
  
  have s3 : ∀ M a b : ℝ, a ≤ b → M ≤ h (Real.exp a) →
      (∫ u in a..b, (M * Real.exp (-u) - 1))
        ≤ ∫ u in a..b, (h (Real.exp u) * Real.exp (-u) - 1) := by
    intro M a b hab hM
    have hg : IntervalIntegrable (fun u : ℝ => M * Real.exp (-u) - 1)
        MeasureTheory.volume a b :=
      ((continuous_const.mul hcontE).sub continuous_const).intervalIntegrable a b
    refine intervalIntegral.integral_mono_on hab hg (s1 a b) ?_
    intro u hu
    have h1 : Real.exp a ≤ Real.exp u := Real.exp_le_exp.mpr hu.1
    have h2 : M ≤ h (Real.exp u) := le_trans hM (hmono h1)
    have h3 : (0 : ℝ) ≤ Real.exp (-u) := (Real.exp_pos _).le
    have h4 := mul_le_mul_of_nonneg_right h2 h3
    linarith
  
  have hlogpos : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
  have hne1 : (1 : ℝ) + ε ≠ 1 := by intro hh; linarith
  have hlogsub : Real.log (1 + ε) < (1 + ε) - 1 := Real.log_lt_sub_one_of_pos hone hne1
  have hcpos : 0 < ε - Real.log (1 + ε) := by linarith
  
  have s5 : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      (∫ u in a..b, (h (Real.exp u) * Real.exp (-u) - 1))
        = (∫ u in Set.Ioc (0 : ℝ) b, (h (Real.exp u) * Real.exp (-u) - 1))
          - ∫ u in Set.Ioc (0 : ℝ) a, (h (Real.exp u) * Real.exp (-u) - 1) := by
    intro a b ha hab
    have hb : (0 : ℝ) ≤ b := le_trans ha hab
    have hadj := intervalIntegral.integral_add_adjacent_intervals (s1 0 a) (s1 a b)
    rw [intervalIntegral.integral_of_le ha, intervalIntegral.integral_of_le hb] at hadj
    linarith
  
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hconv ((ε - Real.log (1 + ε)) / 2) (by linarith)
  
  have block : ∀ a : ℝ, 0 ≤ a → N ≤ a → (1 + ε) * Real.exp a ≤ h (Real.exp a) → False := by
    intro a h0a hNa hM
    have hab : a ≤ a + Real.log (1 + ε) := by linarith
    have hNb : N ≤ a + Real.log (1 + ε) := le_trans hNa hab
    have hexppos : (0 : ℝ) < Real.exp a := Real.exp_pos a
    have hexpne : Real.exp a ≠ 0 := ne_of_gt hexppos
    have honene : (1 : ℝ) + ε ≠ 0 := ne_of_gt hone
    have hlow := s3 ((1 + ε) * Real.exp a) a (a + Real.log (1 + ε)) hab hM
    rw [s2] at hlow
    have hcomp : (1 + ε) * Real.exp a *
        (Real.exp (-a) - Real.exp (-(a + Real.log (1 + ε))))
          - (a + Real.log (1 + ε) - a) = ε - Real.log (1 + ε) := by
      simp only [Real.exp_neg, Real.exp_add, Real.exp_log hone]
      field_simp
      ring
    have hs5 := s5 a (a + Real.log (1 + ε)) h0a hab
    have hA := hN a hNa
    have hB := hN (a + Real.log (1 + ε)) hNb
    simp only [Real.dist_eq, abs_lt] at hA hB
    linarith [hA.1, hA.2, hB.1, hB.2]
  
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  obtain ⟨x, hxge, hxlt⟩ := Filter.frequently_atTop.mp hcon (Real.exp (max N 0))
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hxge
  have hla : max N 0 ≤ Real.log x := by
    have h1 : Real.log (Real.exp (max N 0)) ≤ Real.log x :=
      Real.log_le_log (Real.exp_pos _) hxge
    rwa [Real.log_exp] at h1
  refine block (Real.log x) (le_trans (le_max_right _ _) hla)
    (le_trans (le_max_left _ _) hla) ?_
  rw [Real.exp_log hxpos]
  exact le_of_lt (not_le.mp hxlt)

theorem chebyshev_theta_le_one_add_eps (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Chebyshev.theta x ≤ (1 + ε) * x :=
by
  
  
  
  have psi_le_six : ∀ x : ℝ, 1 ≤ x → Chebyshev.psi x ≤ 6 * x := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    have hsq : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hxpos
    have hlogsqrt : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hsq
    have hls : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx0
    have hlogx : Real.log x ≤ 2 * Real.sqrt x := by rw [hls] at hlogsqrt; linarith
    have hlog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    have hlog4 : Real.log 4 ≤ 2 := by
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast
        ring
      rw [h4]; linarith
    have hA : Real.log 4 * x ≤ 2 * x := mul_le_mul_of_nonneg_right hlog4 hx0
    have hsqsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
    have hB : 2 * Real.sqrt x * Real.log x ≤ 4 * x := by
      calc 2 * Real.sqrt x * Real.log x
          ≤ 2 * Real.sqrt x * (2 * Real.sqrt x) :=
            mul_le_mul_of_nonneg_left hlogx (by positivity)
        _ = 4 * Real.sqrt x ^ 2 := by ring
        _ = 4 * x := by rw [hsqsq]
    have hpsi := Chebyshev.psi_le hx
    linarith
  have hFbound : ∀ t : ℝ, 0 ≤ t →
      |Chebyshev.psi (Real.exp t) * Real.exp (-t) - 1| ≤ 5 := by
    intro t ht
    have he1 : (1 : ℝ) ≤ Real.exp t := by simpa using Real.exp_le_exp.mpr ht
    have hpsi := psi_le_six (Real.exp t) he1
    have hnn := Chebyshev.psi_nonneg (Real.exp t)
    have hpos : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
    have hexp : Real.exp t * Real.exp (-t) = 1 := by
      rw [← Real.exp_add]; simp
    have h1 : Chebyshev.psi (Real.exp t) * Real.exp (-t) ≤ 6 * Real.exp t * Real.exp (-t) :=
      mul_le_mul_of_nonneg_right hpsi hpos.le
    have h2 : 6 * Real.exp t * Real.exp (-t) = 6 := by
      rw [mul_assoc, hexp]; norm_num
    have h3 : 0 ≤ Chebyshev.psi (Real.exp t) * Real.exp (-t) := mul_nonneg hnn hpos.le
    rw [abs_le]
    constructor <;> linarith
  have hFmeas : Measurable (fun u : ℝ => Chebyshev.psi (Real.exp u) * Real.exp (-u) - 1) := by
    have h1 : Measurable Chebyshev.psi := Chebyshev.psi_mono.measurable
    have h2 : Measurable (fun u : ℝ => Chebyshev.psi (Real.exp u)) :=
      h1.comp Real.continuous_exp.measurable
    have h3 : Measurable (fun u : ℝ => Real.exp (-u)) :=
      (Real.continuous_exp.comp continuous_neg).measurable
    exact (h2.mul h3).sub measurable_const
  
  
  
  have hexp_int : ∀ w : ℂ, 0 < w.re →
      MeasureTheory.IntegrableOn (fun t : ℝ => Complex.exp (-w * (t : ℂ)))
        (Set.Ioi (0 : ℝ)) := by
    intro w hw
    have hcont : Continuous (fun t : ℝ => Complex.exp (-w * (t : ℂ))) := by
      continuity
    have hdom : MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-w.re * t))
        (Set.Ioi (0 : ℝ)) := exp_neg_integrableOn_Ioi 0 hw
    refine MeasureTheory.Integrable.mono' hdom hcont.aestronglyMeasurable ?_
    filter_upwards with t
    have hre : (-w * (t : ℂ)).re = -w.re * t := by simp
    rw [Complex.norm_exp, hre]
  have hexp_tendsto : ∀ c : ℝ, 0 < c →
      Filter.Tendsto (fun t : ℝ => Real.exp (-c * t)) Filter.atTop (nhds 0) := by
    intro c hc
    have h1 : Filter.Tendsto (fun t : ℝ => c * t) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop hc Filter.tendsto_id
    have h2 : Filter.Tendsto (fun t : ℝ => -c * t) Filter.atTop Filter.atBot := by
      have h2' := tendsto_neg_atTop_atBot.comp h1
      have heq : (fun t : ℝ => -c * t) = (Neg.neg ∘ fun t : ℝ => c * t) := by
        funext t; simp [Function.comp]
      rw [heq]
      exact h2'
    exact Real.tendsto_exp_atBot.comp h2
  have hexp_val : ∀ w : ℂ, 0 < w.re →
      (∫ t in Set.Ioi (0 : ℝ), Complex.exp (-w * (t : ℂ))) = 1 / w := by
    intro w hw
    have hw0 : w ≠ 0 := by
      intro h; rw [h] at hw; simp at hw
    have hderiv : ∀ t : ℝ,
        HasDerivAt (fun t : ℝ => -Complex.exp (-w * (t : ℂ)) / w)
          (Complex.exp (-w * (t : ℂ))) t := by
      intro t
      have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
      have h1 : HasDerivAt (fun t : ℝ => -w * (t : ℂ)) (-w) t := by
        simpa using h0.const_mul (-w)
      have h3 := (h1.cexp.neg).div_const w
      convert h3 using 1
      field_simp
    have hcont : Continuous (fun t : ℝ => -Complex.exp (-w * (t : ℂ)) / w) := by
      continuity
    have hcw : ContinuousWithinAt (fun t : ℝ => -Complex.exp (-w * (t : ℂ)) / w)
        (Set.Ici (0 : ℝ)) 0 := hcont.continuousWithinAt
    have htend : Filter.Tendsto (fun t : ℝ => -Complex.exp (-w * (t : ℂ)) / w)
        Filter.atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hnorm : ∀ t : ℝ,
          ‖-Complex.exp (-w * (t : ℂ)) / w‖ = Real.exp (-w.re * t) / ‖w‖ := by
        intro t
        have hre : (-w * (t : ℂ)).re = -w.re * t := by simp
        rw [norm_div, norm_neg, Complex.norm_exp, hre]
      simp only [hnorm]
      simpa using (hexp_tendsto w.re hw).div_const ‖w‖
    have key := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcw
      (fun x _ => hderiv x) (hexp_int w hw) htend
    rw [key]
    simp
    ring
  
  
  
  obtain ⟨U, H, hUopen, hUsub, hHdiff, hHeq⟩ := zeta_logDeriv_sub_pole_extends
  
  
  
  have hU'open : IsOpen ((fun z : ℂ => 1 + z) ⁻¹' U ∩ {z : ℂ | z ≠ -1}) :=
    (hUopen.preimage (continuous_const.add continuous_id)).inter isOpen_ne
  have hU'sub : {z : ℂ | 0 ≤ z.re} ⊆ (fun z : ℂ => 1 + z) ⁻¹' U ∩ {z : ℂ | z ≠ -1} := by
    intro z hz
    have hzre : 0 ≤ z.re := hz
    refine ⟨?_, ?_⟩
    · show (1 : ℂ) + z ∈ U
      apply hUsub
      show 1 ≤ ((1 : ℂ) + z).re
      simp only [Complex.add_re, Complex.one_re]
      linarith
    · show z ≠ -1
      intro h
      rw [h] at hzre
      simp only [Complex.neg_re, Complex.one_re] at hzre
      linarith
  have hne : ∀ z ∈ (fun z : ℂ => 1 + z) ⁻¹' U ∩ {z : ℂ | z ≠ -1}, (1 : ℂ) + z ≠ 0 := by
    intro z hz h
    exact hz.2 (by linear_combination h)
  have hGdiff : DifferentiableOn ℂ (fun z : ℂ => (H (1 + z) - 1) / (1 + z))
      ((fun z : ℂ => 1 + z) ⁻¹' U ∩ {z : ℂ | z ≠ -1}) := by
    intro z hz
    have hmaps : Set.MapsTo (fun z : ℂ => 1 + z)
        ((fun z : ℂ => 1 + z) ⁻¹' U ∩ {z : ℂ | z ≠ -1}) U := fun y hy => hy.1
    have hlin : DifferentiableWithinAt ℂ (fun z : ℂ => 1 + z)
        ((fun z : ℂ => 1 + z) ⁻¹' U ∩ {z : ℂ | z ≠ -1}) z := by
      have hda : DifferentiableAt ℂ (fun z : ℂ => 1 + z) z :=
        (differentiableAt_const (1 : ℂ)).add differentiableAt_id
      exact hda.differentiableWithinAt
    have hHw : DifferentiableWithinAt ℂ H U (1 + z) := hHdiff _ hz.1
    have hcomp : DifferentiableWithinAt ℂ (fun z : ℂ => H (1 + z))
        ((fun z : ℂ => 1 + z) ⁻¹' U ∩ {z : ℂ | z ≠ -1}) z := by
      have hc := hHw.comp z hlin hmaps
      simpa [Function.comp] using hc
    exact (hcomp.sub (differentiableWithinAt_const 1)).div hlin (hne z hz)
  have hlap : ∀ z : ℂ, 0 < z.re →
      (∫ t in Set.Ioi (0 : ℝ),
          ((Chebyshev.psi (Real.exp t) * Real.exp (-t) - 1 : ℝ) : ℂ) *
            Complex.exp (-z * (t : ℂ)))
        = (H (1 + z) - 1) / (1 + z) := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h; rw [h] at hz; simp at hz
    have hsre : 1 < ((1 : ℂ) + z).re := by
      simp only [Complex.add_re, Complex.one_re]
      linarith
    have h1z : (1 : ℂ) + z ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hre
      linarith
    obtain ⟨hint1, heq1⟩ := mellin_psi_eq_LSeries_vonMangoldt_div (1 + z) hsre
    have hint2 := hexp_int z hz
    have hpt : ∀ t : ℝ,
        ((Chebyshev.psi (Real.exp t) * Real.exp (-t) - 1 : ℝ) : ℂ) *
            Complex.exp (-z * (t : ℂ))
          = (Chebyshev.psi (Real.exp t) : ℂ) * Complex.exp (-(1 + z) * (t : ℂ))
            - Complex.exp (-z * (t : ℂ)) := by
      intro t
      have e2 : Complex.exp (-(t : ℂ)) * Complex.exp (-z * (t : ℂ))
          = Complex.exp (-(1 + z) * (t : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      push_cast
      rw [sub_mul, one_mul, mul_assoc, e2]
    have hLS : LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 + z)
        = H (1 + z) + 1 / z := by
      rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hsre,
        hHeq (1 + z) hsre, show (1 : ℂ) + z - 1 = z by ring]
      ring
    calc (∫ t in Set.Ioi (0 : ℝ),
            ((Chebyshev.psi (Real.exp t) * Real.exp (-t) - 1 : ℝ) : ℂ) *
              Complex.exp (-z * (t : ℂ)))
        = ∫ t in Set.Ioi (0 : ℝ),
            ((Chebyshev.psi (Real.exp t) : ℂ) * Complex.exp (-(1 + z) * (t : ℂ))
              - Complex.exp (-z * (t : ℂ))) := by
          simp only [hpt]
      _ = (∫ t in Set.Ioi (0 : ℝ),
              (Chebyshev.psi (Real.exp t) : ℂ) * Complex.exp (-(1 + z) * (t : ℂ)))
            - ∫ t in Set.Ioi (0 : ℝ), Complex.exp (-z * (t : ℂ)) :=
          MeasureTheory.integral_sub hint1 hint2
      _ = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 + z) / (1 + z)
            - 1 / z := by rw [heq1, hexp_val z hz]
      _ = (H (1 + z) - 1) / (1 + z) := by
          rw [hLS]
          field_simp
          ring
  
  
  
  obtain ⟨L, hL⟩ := newman_analytic_theorem
    (fun u : ℝ => Chebyshev.psi (Real.exp u) * Real.exp (-u) - 1) 5 hFmeas hFbound
    ((fun z : ℂ => 1 + z) ⁻¹' U ∩ {z : ℂ | z ≠ -1})
    (fun z : ℂ => (H (1 + z) - 1) / (1 + z)) hU'open hU'sub hGdiff hlap
  have hpsi := upper_bound_of_tendsto_log_integral Chebyshev.psi Chebyshev.psi_mono L hL ε hε
  filter_upwards [hpsi] with x hx
  exact le_trans (Chebyshev.theta_le_psi x) hx

theorem minFac_choose_gt_of_digits_le {n k : ℕ} (hk : 1 ≤ k) (hn : k + 2 ≤ n)
    (h : ∀ p : ℕ, p.Prime → p ≤ k → ∀ i : ℕ, k / p ^ i % p ≤ n / p ^ i % p) :
    k < (n.choose k).minFac :=
by
  
  have hkn : k ≤ n := by omega
  
  have hC1 : n.choose k ≠ 1 := by
    intro e
    rcases Nat.choose_eq_one_iff.mp e with h0 | h0 <;> omega
  
  have hq : Nat.Prime (n.choose k).minFac := Nat.minFac_prime hC1
  have hqC : (n.choose k).minFac ∣ n.choose k := Nat.minFac_dvd _
  
  by_contra hcon
  have hqk : (n.choose k).minFac ≤ k := Nat.not_lt.mp hcon
  have hdig := h _ hq hqk
  haveI : Fact (Nat.Prime (n.choose k).minFac) := ⟨hq⟩
  
  have hna : n < (n.choose k).minFac ^ (Nat.log (n.choose k).minFac n).succ :=
    Nat.lt_pow_succ_log_self hq.one_lt n
  have hka : k < (n.choose k).minFac ^ (Nat.log (n.choose k).minFac n).succ :=
    lt_of_le_of_lt hkn hna
  
  have hluc := _root_.Choose.lucas_theorem_nat hna hka
  
  have hcop : Nat.Coprime (n.choose k).minFac
      (∏ i ∈ Finset.range (Nat.log (n.choose k).minFac n).succ,
        (n / (n.choose k).minFac ^ i % (n.choose k).minFac).choose
          (k / (n.choose k).minFac ^ i % (n.choose k).minFac)) :=
    Nat.Coprime.prod_right (fun i _ => hq.coprime_choose_of_lt (Nat.mod_lt _ hq.pos) (hdig i))
  
  exact (hq.coprime_iff_not_dvd.mp hcop)
    (Nat.modEq_zero_iff_dvd.mp ((hluc.symm).trans (Nat.modEq_zero_iff_dvd.mpr hqC)))

theorem digits_of_pred_of_pow_dvd {p M : ℕ} (hp : 2 ≤ p) (hM : 1 ≤ M) {a : ℕ}
    (hdvd : p ^ a ∣ M) :
    (∀ i, i < a → (M - 1) / p ^ i % p = p - 1) ∧ (M - 1) / p ^ a = M / p ^ a - 1 :=
by
  have hp0 : 0 < p := by omega
  
  
  have hid : ∀ b c : ℕ, 0 < b → 0 < c → b * c - 1 = b * (c - 1) + (b - 1) := by
    intro b c hb hc
    have hbc : b ≤ b * c := Nat.le_mul_of_pos_right b hc
    have h1 : b * (c - 1) = b * c - b := by
      cases c with
      | zero => omega
      | succ n => simp [Nat.mul_succ]
    omega
  have hdiv : ∀ b c : ℕ, 0 < b → 0 < c → (b * c - 1) / b = c - 1 := by
    intro b c hb hc
    rw [hid b c hb hc, Nat.mul_add_div hb, Nat.div_eq_of_lt (by omega : b - 1 < b),
      Nat.add_zero]
  have hmod : ∀ b c : ℕ, 0 < b → 0 < c → (b * c - 1) % b = b - 1 := by
    intro b c hb hc
    rw [hid b c hb hc, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega : b - 1 < b)]
  obtain ⟨q, hq⟩ := hdvd
  have hPpos : 0 < p ^ a := Nat.pow_pos hp0
  have hqpos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h
      rw [Nat.mul_zero] at hq
      omega
    · exact h
  have hMq : M / p ^ a = q := by
    rw [hq]
    exact Nat.mul_div_cancel_left q hPpos
  constructor
  · intro i hi
    have hipos : 0 < p ^ i := Nat.pow_pos hp0
    have hdpos : 0 < p ^ (a - i - 1) * q := Nat.mul_pos (Nat.pow_pos hp0) hqpos
    have he : i + 1 + (a - i - 1) = a := by omega
    have hMd : p ^ i * (p * (p ^ (a - i - 1) * q)) = M := by
      calc p ^ i * (p * (p ^ (a - i - 1) * q))
          = p ^ (i + 1 + (a - i - 1)) * q := by
            rw [pow_add, pow_add, pow_one]; ring
        _ = p ^ a * q := by rw [he]
        _ = M := hq.symm
    have h1 : (M - 1) / p ^ i = p * (p ^ (a - i - 1) * q) - 1 := by
      rw [← hMd, hdiv (p ^ i) (p * (p ^ (a - i - 1) * q)) hipos (Nat.mul_pos hp0 hdpos)]
    rw [h1, hmod p (p ^ (a - i - 1) * q) hp0 hdpos]
  · rw [hMq, hq, hdiv (p ^ a) q hPpos hqpos]

theorem le_mod_pred_of_not_mem_Icc {p z d : ℕ} (hp : 0 < p) (hz : 1 ≤ z) (hd : d < p)
    (h : z % p ∉ Finset.Icc 1 d) : d ≤ (z - 1) % p :=
by
  
  
  obtain ⟨w, rfl⟩ : ∃ w, z = w + 1 := ⟨z - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  
  by_contra hcon
  push_neg at hcon
  
  have ht1 : w % p + 1 < p := lt_of_le_of_lt hcon hd
  
  have hdm : p * (w / p) + w % p = w := Nat.div_add_mod w p
  
  have hzmod : (w + 1) % p = w % p + 1 := by
    calc (w + 1) % p = (p * (w / p) + (w % p + 1)) % p := by rw [← Nat.add_assoc, hdm]
      _ = (w % p + 1) % p := Nat.mul_add_mod _ _ _
      _ = w % p + 1 := Nat.mod_eq_of_lt ht1
  
  apply h
  rw [Finset.mem_Icc, hzmod]
  exact ⟨Nat.le_add_left 1 _, hcon⟩

theorem exists_multiplier_avoiding {L : Finset ℕ} {u d : ℕ → ℕ} {T : ℕ}
    (hp : ∀ p ∈ L, Nat.Prime p) (hu : ∀ p ∈ L, ¬ p ∣ u p)
    (hsum : ∑ p ∈ L, d p * (T / p + 1) < T) :
    ∃ s, 1 ≤ s ∧ s ≤ T ∧ ∀ p ∈ L, s * u p % p ∉ Finset.Icc 1 (d p) :=
by
  classical
  
  
  have hcard : ∀ p ∈ L,
      ((Finset.Icc 1 T).filter (fun s => s * u p % p ∈ Finset.Icc 1 (d p))).card
        ≤ d p * (T / p + 1) := by
    intro p hpL
    have hpp : Nat.Prime p := hp p hpL
    have hpu : ¬ p ∣ u p := hu p hpL
    have hcop : Nat.Coprime p (u p) := (Nat.Prime.coprime_iff_not_dvd hpp).mpr hpu
    have hmaps : Set.MapsTo (fun s => (s * u p % p, s / p))
        (↑((Finset.Icc 1 T).filter (fun s => s * u p % p ∈ Finset.Icc 1 (d p))) : Set ℕ)
        (↑(Finset.Icc 1 (d p) ×ˢ Finset.range (T / p + 1)) : Set (ℕ × ℕ)) := by
      intro s hs
      have hs' : s ∈ (Finset.Icc 1 T).filter (fun s => s * u p % p ∈ Finset.Icc 1 (d p)) := hs
      rw [Finset.mem_filter] at hs'
      have hsT : s ≤ T := (Finset.mem_Icc.mp hs'.1).2
      have hmem : (s * u p % p, s / p) ∈ Finset.Icc 1 (d p) ×ˢ Finset.range (T / p + 1) := by
        rw [Finset.mem_product]
        exact ⟨hs'.2, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hsT))⟩
      exact Finset.mem_coe.mpr hmem
    have hinj : Set.InjOn (fun s => (s * u p % p, s / p))
        (↑((Finset.Icc 1 T).filter (fun s => s * u p % p ∈ Finset.Icc 1 (d p))) : Set ℕ) := by
      intro s _ t _ hst
      have h1 : s * u p % p = t * u p % p := congrArg Prod.fst hst
      have h2 : s / p = t / p := congrArg Prod.snd hst
      have hmod : s ≡ t [MOD p] := Nat.ModEq.cancel_right_of_coprime hcop h1
      have hmod' : s % p = t % p := hmod
      calc s = p * (s / p) + s % p := (Nat.div_add_mod s p).symm
        _ = p * (t / p) + t % p := by rw [h2, hmod']
        _ = t := Nat.div_add_mod t p
    have hle := Finset.card_le_card_of_injOn (fun s => (s * u p % p, s / p)) hmaps hinj
    have hcardP : (Finset.Icc 1 (d p) ×ˢ Finset.range (T / p + 1)).card
        = d p * (T / p + 1) := by
      rw [Finset.card_product, Nat.card_Icc, Finset.card_range]
      simp
    exact le_trans hle (le_of_eq hcardP)
  
  have hsumB : ∑ p ∈ L,
      ((Finset.Icc 1 T).filter (fun s => s * u p % p ∈ Finset.Icc 1 (d p))).card < T :=
    lt_of_le_of_lt (Finset.sum_le_sum hcard) hsum
  have hU : (L.biUnion
      (fun p => (Finset.Icc 1 T).filter (fun s => s * u p % p ∈ Finset.Icc 1 (d p)))).card < T :=
    lt_of_le_of_lt Finset.card_biUnion_le hsumB
  
  have hIccT : (Finset.Icc 1 T).card = T := by
    rw [Nat.card_Icc]; omega
  have hlt : (L.biUnion
      (fun p => (Finset.Icc 1 T).filter (fun s => s * u p % p ∈ Finset.Icc 1 (d p)))).card
      < (Finset.Icc 1 T).card := by
    rw [hIccT]; exact hU
  obtain ⟨e, heIcc, heU⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have heIcc' := Finset.mem_Icc.mp heIcc
  
  refine ⟨e, heIcc'.1, heIcc'.2, ?_⟩
  intro p hpL hmemIcc
  exact heU (Finset.mem_biUnion.mpr ⟨p, hpL, Finset.mem_filter.mpr ⟨heIcc, hmemIcc⟩⟩)

theorem sum_log_least_prime_pow_le (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    ∀ᶠ k : ℕ in Filter.atTop,
      ∑ p ∈ (Finset.Ioc 0 ⌊η * (k : ℝ)⌋₊).filter Nat.Prime,
          ((Nat.log p k : ℝ) + 1) * Real.log p ≤ 10 * η * k :=
by
  classical
  
  have htheta : ∀ y : ℕ,
      ∑ p ∈ (Finset.Ioc 0 y).filter Nat.Prime, Real.log (p : ℝ) ≤ (y : ℝ) * Real.log 4 := by
    intro y
    have hEq : Chebyshev.theta (y : ℝ)
        = ∑ p ∈ (Finset.Ioc 0 y).filter Nat.Prime, Real.log (p : ℝ) := by
      simp [Chebyshev.theta]
    rw [← hEq, Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]
    have hprimpos : 0 < primorial y := by
      unfold primorial
      exact Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.pos)
    have h2 : (0 : ℝ) < ((primorial y : ℕ) : ℝ) := by exact_mod_cast hprimpos
    have h1 : ((primorial y : ℕ) : ℝ) ≤ (4 : ℝ) ^ y := by
      have h := primorial_le_4_pow y
      exact_mod_cast h
    calc Real.log ((primorial y : ℕ) : ℝ) ≤ Real.log ((4 : ℝ) ^ y) := Real.log_le_log h2 h1
      _ = (y : ℝ) * Real.log 4 := by rw [Real.log_pow]
  
  have hlog4 : Real.log 4 ≤ 3 / 2 := by
    have h : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    have h2 := Real.log_two_lt_d9
    linarith
  have hlog40 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  
  have hE2 : ∀ᶠ k : ℕ in Filter.atTop,
      2 * Real.sqrt (k : ℝ) * Real.log (k : ℝ) ≤ 7 * η * (k : ℝ) := by
    have hc : (0 : ℝ) < 7 * η := by linarith
    have htend : Filter.Tendsto (fun k : ℕ => Real.sqrt (Real.sqrt (k : ℝ)))
        Filter.atTop Filter.atTop :=
      Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    filter_upwards [htend.eventually_ge_atTop (8 / (7 * η)), Filter.eventually_ge_atTop 1]
      with k hkt hk1
    have hkn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    set t : ℝ := Real.sqrt (Real.sqrt (k : ℝ)) with ht_def
    have ht0 : (0 : ℝ) ≤ t := by rw [ht_def]; exact Real.sqrt_nonneg _
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le (div_pos (by norm_num) hc) hkt
    have hct : (8 : ℝ) ≤ 7 * η * t := by
      rw [div_le_iff₀ hc] at hkt; linarith
    have hsk : Real.sqrt (k : ℝ) = t ^ 2 := by
      rw [ht_def, Real.sq_sqrt (Real.sqrt_nonneg _)]
    have hk4 : (k : ℝ) = t ^ 4 := by
      have h1 : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt hkn
      rw [hsk] at h1
      rw [← h1]; ring
    have hlogt : Real.log t = Real.log (k : ℝ) / 4 := by
      rw [ht_def, Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt hkn]
      ring
    have hlt : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos htpos
    have hlogk : Real.log (k : ℝ) ≤ 4 * t := by linarith
    calc 2 * Real.sqrt (k : ℝ) * Real.log (k : ℝ)
        = 2 * t ^ 2 * Real.log (k : ℝ) := by rw [hsk]
      _ ≤ 2 * t ^ 2 * (4 * t) := mul_le_mul_of_nonneg_left hlogk (by positivity)
      _ = 8 * t ^ 3 := by ring
      _ ≤ (7 * η * t) * t ^ 3 := mul_le_mul_of_nonneg_right hct (pow_nonneg ht0 3)
      _ = 7 * η * t ^ 4 := by ring
      _ = 7 * η * (k : ℝ) := by rw [← hk4]
  
  filter_upwards [hE2, Filter.eventually_ge_atTop 2] with k hkan hk2
  have hk0 : k ≠ 0 := by omega
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
  have hkn : (0 : ℝ) ≤ (k : ℝ) := by linarith
  have hlogk0 : (0 : ℝ) ≤ Real.log (k : ℝ) := Real.log_nonneg hkR
  set y : ℕ := ⌊η * (k : ℝ)⌋₊ with hy_def
  set S : Finset ℕ := (Finset.Ioc 0 y).filter Nat.Prime with hS_def
  have hSprime : ∀ p ∈ S, Nat.Prime p := by
    intro p hp
    rw [hS_def] at hp
    exact (Finset.mem_filter.mp hp).2
  
  have hsplit :
      ∑ p ∈ S.filter (fun p => p * p ≤ k), ((Nat.log p k : ℝ) + 1) * Real.log (p : ℝ)
        + ∑ p ∈ S.filter (fun p => ¬ (p * p ≤ k)), ((Nat.log p k : ℝ) + 1) * Real.log (p : ℝ)
      = ∑ p ∈ S, ((Nat.log p k : ℝ) + 1) * Real.log (p : ℝ) :=
    Finset.sum_filter_add_sum_filter_not S _ _
  
  have hsmall :
      ∑ p ∈ S.filter (fun p => p * p ≤ k), ((Nat.log p k : ℝ) + 1) * Real.log (p : ℝ)
        ≤ 2 * Real.sqrt (k : ℝ) * Real.log (k : ℝ) := by
    have hterm : ∀ p ∈ S.filter (fun p => p * p ≤ k),
        ((Nat.log p k : ℝ) + 1) * Real.log (p : ℝ) ≤ 2 * Real.log (k : ℝ) := by
      intro p hp
      obtain ⟨hpS, hpp2⟩ := Finset.mem_filter.mp hp
      have hpp : Nat.Prime p := hSprime p hpS
      have hppos : 0 < p := hpp.pos
      have hpR1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_lt.le
      have hpRpos : (0 : ℝ) < (p : ℝ) := by linarith
      have hpk : p ≤ k := le_trans (Nat.le_mul_of_pos_left p hppos) hpp2
      have hlogpk : Real.log (p : ℝ) ≤ Real.log (k : ℝ) :=
        Real.log_le_log hpRpos (by exact_mod_cast hpk)
      have hpow : p ^ (Nat.log p k) ≤ k := Nat.pow_log_le_self p hk0
      have hpowR : (p : ℝ) ^ (Nat.log p k) ≤ (k : ℝ) := by exact_mod_cast hpow
      have h1 : (Nat.log p k : ℝ) * Real.log (p : ℝ) ≤ Real.log (k : ℝ) := by
        have h := Real.log_le_log (pow_pos hpRpos (Nat.log p k)) hpowR
        rwa [Real.log_pow] at h
      linarith
    have hcard : (S.filter (fun p => p * p ≤ k)).card ≤ Nat.sqrt k := by
      have hsub : S.filter (fun p => p * p ≤ k) ⊆ Finset.Ioc 0 (Nat.sqrt k) := by
        intro p hp
        obtain ⟨hpS, hpp2⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_Ioc.mpr ⟨(hSprime p hpS).pos, Nat.le_sqrt.mpr hpp2⟩
      calc (S.filter (fun p => p * p ≤ k)).card
          ≤ (Finset.Ioc 0 (Nat.sqrt k)).card := Finset.card_le_card hsub
        _ = Nat.sqrt k := by simp
    have hsqrtcast : ((Nat.sqrt k : ℕ) : ℝ) ≤ Real.sqrt (k : ℝ) := by
      have h : ((Nat.sqrt k : ℕ) : ℝ) ^ 2 ≤ (k : ℝ) := by exact_mod_cast Nat.sqrt_le' k
      calc ((Nat.sqrt k : ℕ) : ℝ) = Real.sqrt (((Nat.sqrt k : ℕ) : ℝ) ^ 2) :=
            (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt (k : ℝ) := Real.sqrt_le_sqrt h
    have hcardR : (((S.filter (fun p => p * p ≤ k)).card : ℕ) : ℝ) ≤ Real.sqrt (k : ℝ) := by
      refine le_trans ?_ hsqrtcast
      exact_mod_cast hcard
    calc ∑ p ∈ S.filter (fun p => p * p ≤ k), ((Nat.log p k : ℝ) + 1) * Real.log (p : ℝ)
        ≤ (S.filter (fun p => p * p ≤ k)).card • (2 * Real.log (k : ℝ)) :=
          Finset.sum_le_card_nsmul _ _ _ hterm
      _ = (((S.filter (fun p => p * p ≤ k)).card : ℕ) : ℝ) * (2 * Real.log (k : ℝ)) :=
          nsmul_eq_mul _ _
      _ ≤ Real.sqrt (k : ℝ) * (2 * Real.log (k : ℝ)) :=
          mul_le_mul_of_nonneg_right hcardR (by linarith)
      _ = 2 * Real.sqrt (k : ℝ) * Real.log (k : ℝ) := by ring
  
  have hlarge :
      ∑ p ∈ S.filter (fun p => ¬ (p * p ≤ k)), ((Nat.log p k : ℝ) + 1) * Real.log (p : ℝ)
        ≤ 2 * ∑ p ∈ S.filter (fun p => ¬ (p * p ≤ k)), Real.log (p : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro p hp
    obtain ⟨hpS, hpp2⟩ := Finset.mem_filter.mp hp
    have hpp : Nat.Prime p := hSprime p hpS
    have hlog1 : Nat.log p k ≤ 1 := by
      by_contra hcon
      push_neg at hcon
      have h1 : p ^ 2 ≤ p ^ (Nat.log p k) :=
        Nat.pow_le_pow_right hpp.pos (by omega : 2 ≤ Nat.log p k)
      have h2 : p ^ (Nat.log p k) ≤ k := Nat.pow_log_le_self p hk0
      have h4 : p * p ≤ k := by
        calc p * p = p ^ 2 := by ring
          _ ≤ p ^ (Nat.log p k) := h1
          _ ≤ k := h2
      exact absurd h4 hpp2
    have hpR1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_lt.le
    have hlogp0 : (0 : ℝ) ≤ Real.log (p : ℝ) := Real.log_nonneg hpR1
    have hle2 : ((Nat.log p k : ℝ) + 1) ≤ 2 := by
      have h : (Nat.log p k : ℝ) ≤ 1 := by exact_mod_cast hlog1
      linarith
    exact mul_le_mul_of_nonneg_right hle2 hlogp0
  
  have hBsub : S.filter (fun p => ¬ (p * p ≤ k)) ⊆ S := Finset.filter_subset _ _
  have hBlog : ∑ p ∈ S.filter (fun p => ¬ (p * p ≤ k)), Real.log (p : ℝ)
      ≤ ∑ p ∈ S, Real.log (p : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hBsub ?_
    intro p hpS _
    exact Real.log_nonneg (by exact_mod_cast (hSprime p hpS).one_lt.le)
  have hSlog : ∑ p ∈ S, Real.log (p : ℝ) ≤ (y : ℝ) * Real.log 4 := by
    rw [hS_def]; exact htheta y
  have hyle : (y : ℝ) ≤ η * (k : ℝ) := by
    rw [hy_def]; exact Nat.floor_le (mul_nonneg hη.le hkn)
  have hy0 : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
  have hthree : 2 * ∑ p ∈ S.filter (fun p => ¬ (p * p ≤ k)), Real.log (p : ℝ)
      ≤ 3 * (η * (k : ℝ)) := by
    have h1 : (y : ℝ) * Real.log 4 ≤ (η * (k : ℝ)) * (3 / 2) :=
      mul_le_mul hyle hlog4 hlog40 (mul_nonneg hη.le hkn)
    linarith
  linarith [hsplit, hsmall, hkan, hlarge, hthree]

theorem g_le_exp_theta_add_eps (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, (g k : ℝ) ≤ Real.exp (Chebyshev.theta k + ε * k) :=
by
  classical
  set η : ℝ := (min ε 1) / 11 with hη_def
  have hmin_pos : 0 < min ε 1 := lt_min hε one_pos
  have hη0 : 0 < η := by rw [hη_def]; linarith
  have hη11 : η ≤ 1 / 11 := by
    have h1 : min ε 1 ≤ 1 := min_le_right _ _
    rw [hη_def]; linarith
  have hηε : 11 * η ≤ ε := by
    have h1 : min ε 1 ≤ ε := min_le_left _ _
    rw [hη_def]; linarith
  have hηlt1 : η < 1 := by linarith
  
  have hcast : Filter.Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hE1 : ∀ᶠ k : ℕ in atTop, (8 : ℝ) ≤ η ^ 2 * k :=
    (Filter.Tendsto.const_mul_atTop (by positivity) hcast).eventually_ge_atTop 8
  have hE2 : ∀ᶠ k : ℕ in atTop, (3 : ℝ) ≤ η * k :=
    (Filter.Tendsto.const_mul_atTop hη0 hcast).eventually_ge_atTop 3
  have hE3 : ∀ᶠ k : ℕ in atTop, 4 * Real.log 4 ≤ η ^ 2 * Real.log (η * k) := by
    have h1 : Filter.Tendsto (fun k : ℕ => η * (k : ℝ)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hη0 hcast
    have h2 : Filter.Tendsto (fun k : ℕ => Real.log (η * (k : ℝ))) atTop atTop :=
      Real.tendsto_log_atTop.comp h1
    exact (Filter.Tendsto.const_mul_atTop (by positivity) h2).eventually_ge_atTop _
  have hE4 := sum_log_least_prime_pow_le η hη0 hηlt1
  have hE5 : ∀ᶠ k : ℕ in atTop, 4 ≤ k := eventually_ge_atTop 4
  filter_upwards [hE1, hE2, hE3, hE4, hE5] with k hH1 hH2 hH3 hH4 hH5
  
  have hkpos : 0 < k := by omega
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkR
  have hηne : η ≠ 0 := ne_of_gt hη0
  have hηkpos : (0 : ℝ) < η * k := mul_pos hη0 hkR
  
  set y : ℕ := ⌊η * (k : ℝ)⌋₊ with hy_def
  set S : Finset ℕ := (Finset.Ioc 0 y).filter Nat.Prime with hS_def
  set L : Finset ℕ := (Finset.Ioc y k).filter Nat.Prime with hL_def
  set RS : ℕ := ∏ p ∈ S, p ^ (Nat.log p k + 1) with hRS_def
  set RL : ℕ := ∏ p ∈ L, p with hRL_def
  set R : ℕ := RS * RL with hR_def
  set T : ℕ := 2 * k with hT_def
  have hSprime : ∀ p ∈ S, Nat.Prime p := by
    intro p hp; rw [hS_def] at hp; exact (Finset.mem_filter.mp hp).2
  have hLprime : ∀ p ∈ L, Nat.Prime p := by
    intro p hp; rw [hL_def] at hp; exact (Finset.mem_filter.mp hp).2
  have hRSpos : 0 < RS := by
    rw [hRS_def]; exact Finset.prod_pos (fun p hp => pow_pos (hSprime p hp).pos _)
  have hRLpos : 0 < RL := by
    rw [hRL_def]; exact Finset.prod_pos (fun p hp => (hLprime p hp).pos)
  have hRpos : 0 < R := by rw [hR_def]; exact Nat.mul_pos hRSpos hRLpos
  have hTpos : 0 < T := by rw [hT_def]; omega
  
  have hy3 : 3 ≤ y := by
    rw [hy_def]; exact Nat.le_floor (by push_cast; linarith)
  have hyk : y ≤ k := by
    rw [hy_def]
    have h1 : η * (k : ℝ) ≤ (k : ℝ) := by nlinarith
    calc ⌊η * (k : ℝ)⌋₊ ≤ ⌊(k : ℝ)⌋₊ := Nat.floor_le_floor h1
      _ = k := Nat.floor_natCast k
  
  have hF2 : ∀ p ∈ L, η * (k : ℝ) < (p : ℝ) := by
    intro p hp
    have hpy : y < p := by
      rw [hL_def] at hp; exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
    have h1 : η * (k : ℝ) < (y : ℝ) + 1 := by rw [hy_def]; exact Nat.lt_floor_add_one _
    have h2 : (y : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hpy
    linarith
  
  have hF3 : ∀ p ∈ L, k < p * p := by
    intro p hp
    have h2 := hF2 p hp
    have h5 : (η * (k : ℝ)) * (η * (k : ℝ)) ≤ (p : ℝ) * (p : ℝ) :=
      mul_le_mul h2.le h2.le hηkpos.le (by positivity)
    have h6 : (η * (k : ℝ)) * (η * (k : ℝ)) = (η ^ 2 * k) * k := by ring
    have : (k : ℝ) < (p : ℝ) * (p : ℝ) := by nlinarith
    exact_mod_cast this
  
  have hF4 : ∀ p ∈ L, k / p < p := by
    intro p hp
    have hppos : 0 < p := (hLprime p hp).pos
    have h1 : k / p * p ≤ k := Nat.div_mul_le_self k p
    have h2 := hF3 p hp
    by_contra hc
    push_neg at hc
    have h3 : p * p ≤ k / p * p := Nat.mul_le_mul_right p hc
    omega
  
  have hF5 : ∀ p ∈ L, p ∣ R ∧ ¬ p ∣ (R / p) := by
    intro p hp
    have hpp : Nat.Prime p := hLprime p hp
    have hppos : 0 < p := hpp.pos
    have hpy : y < p := by
      rw [hL_def] at hp; exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
    have hRLeq : RL = p * ∏ q ∈ L.erase p, q := by
      rw [hRL_def]; exact (Finset.mul_prod_erase L (fun q => q) hp).symm
    have hReq : R = p * (RS * ∏ q ∈ L.erase p, q) := by
      rw [hR_def, hRLeq]; ring
    have hpR : p ∣ R := ⟨RS * ∏ q ∈ L.erase p, q, hReq⟩
    have hdiv : R / p = RS * ∏ q ∈ L.erase p, q := by
      rw [hReq]; exact Nat.mul_div_cancel_left _ hppos
    have hnRS : ¬ p ∣ RS := by
      intro hd
      rw [hRS_def] at hd
      obtain ⟨q, hq, hdq⟩ := (hpp.prime.dvd_finset_prod_iff _).mp hd
      have hqp : Nat.Prime q := hSprime q hq
      have : p ∣ q := hpp.dvd_of_dvd_pow hdq
      have heq : p = q := (Nat.prime_dvd_prime_iff_eq hpp hqp).mp this
      have hqy : q ≤ y := by
        rw [hS_def] at hq; exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).2
      omega
    have hnP : ¬ p ∣ ∏ q ∈ L.erase p, q := by
      intro hd
      obtain ⟨q, hq, hdq⟩ := (hpp.prime.dvd_finset_prod_iff _).mp hd
      have hqne : q ≠ p := Finset.ne_of_mem_erase hq
      have hqL : q ∈ L := Finset.mem_of_mem_erase hq
      have hqp : Nat.Prime q := hLprime q hqL
      have heq : p = q := (Nat.prime_dvd_prime_iff_eq hpp hqp).mp hdq
      exact hqne heq.symm
    refine ⟨hpR, ?_⟩
    rw [hdiv]
    intro hd
    rcases (Nat.Prime.dvd_mul hpp).mp hd with h | h
    · exact hnRS h
    · exact hnP h
  
  have hlogL : ∀ p ∈ L, Real.log (η * k) ≤ Real.log (p : ℝ) := by
    intro p hp
    exact Real.log_le_log hηkpos (hF2 p hp).le
  have hLsum : (L.card : ℝ) * Real.log (η * k) ≤ ∑ p ∈ L, Real.log (p : ℝ) := by
    calc (L.card : ℝ) * Real.log (η * k) = ∑ _p ∈ L, Real.log (η * k) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ L, Real.log (p : ℝ) := Finset.sum_le_sum hlogL
  have hthetaEq : Chebyshev.theta (k : ℝ)
      = ∑ p ∈ (Finset.Ioc 0 k).filter Nat.Prime, Real.log (p : ℝ) := by
    simp [Chebyshev.theta]
  have hsubL : L ⊆ (Finset.Ioc 0 k).filter Nat.Prime := by
    intro p hp
    have hp' := hp
    rw [hL_def] at hp'
    have h1 := Finset.mem_filter.mp hp'
    have h2 := Finset.mem_Ioc.mp h1.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, h2.2⟩, h1.2⟩
  have hthetaL : ∑ p ∈ L, Real.log (p : ℝ) ≤ Chebyshev.theta (k : ℝ) := by
    rw [hthetaEq]
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubL ?_
    intro p hp _
    have h1 : 1 ≤ p := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
    exact Real.log_nonneg (by exact_mod_cast h1)
  have hthetaUb : Chebyshev.theta (k : ℝ) ≤ (k : ℝ) * Real.log 4 := by
    rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]
    have hprimpos : 0 < primorial k := by
      unfold primorial
      exact Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.pos)
    have h1 : ((primorial k : ℕ) : ℝ) ≤ (4 : ℝ) ^ k := by
      have := primorial_le_4_pow k
      exact_mod_cast this
    have h2 : (0 : ℝ) < ((primorial k : ℕ) : ℝ) := by exact_mod_cast hprimpos
    calc Real.log ((primorial k : ℕ) : ℝ) ≤ Real.log ((4 : ℝ) ^ k) := Real.log_le_log h2 h1
      _ = (k : ℝ) * Real.log 4 := by rw [Real.log_pow]
  
  have hlogηk : 0 < Real.log (η * k) := Real.log_pos (by linarith)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hLcard : (L.card : ℝ) ≤ η ^ 2 * k / 4 := by
    have h1 : (L.card : ℝ) * Real.log (η * k) ≤ (k : ℝ) * Real.log 4 :=
      le_trans hLsum (le_trans hthetaL hthetaUb)
    have hc0 : (0 : ℝ) ≤ (L.card : ℝ) := Nat.cast_nonneg _
    have e1 : (L.card : ℝ) * (4 * Real.log 4) ≤ (L.card : ℝ) * (η ^ 2 * Real.log (η * k)) :=
      mul_le_mul_of_nonneg_left hH3 hc0
    have e2 : η ^ 2 * ((L.card : ℝ) * Real.log (η * k)) ≤ η ^ 2 * ((k : ℝ) * Real.log 4) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith [hlog4]
  
  have hsieve : ∑ p ∈ L, (k / p) * (T / p + 1) < T := by
    have hbound : ∀ p ∈ L, ((k / p : ℕ) : ℝ) * (((T / p : ℕ) : ℝ) + 1)
        ≤ (T : ℝ) / (η ^ 2 * k) + 1 / η := by
      intro p hp
      have hx : η * (k : ℝ) < (p : ℝ) := hF2 p hp
      have hxpos : (0 : ℝ) < (p : ℝ) := lt_trans hηkpos hx
      have h1 : ((k / p : ℕ) : ℝ) ≤ (k : ℝ) / (p : ℝ) := Nat.cast_div_le
      have h2 : ((T / p : ℕ) : ℝ) ≤ (T : ℝ) / (p : ℝ) := Nat.cast_div_le
      have h3 : (k : ℝ) / (p : ℝ) ≤ (k : ℝ) / (η * (k : ℝ)) := by gcongr
      have h4 : (T : ℝ) / (p : ℝ) ≤ (T : ℝ) / (η * k) := by
        have hTnn : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg _
        gcongr
      have hkp0 : (0 : ℝ) ≤ (k : ℝ) / (p : ℝ) := by positivity
      calc ((k / p : ℕ) : ℝ) * (((T / p : ℕ) : ℝ) + 1)
          ≤ ((k : ℝ) / (p : ℝ)) * ((T : ℝ) / (η * k) + 1) := by
            refine mul_le_mul h1 (by linarith) (by positivity) hkp0
        _ ≤ ((k : ℝ) / (η * (k : ℝ))) * ((T : ℝ) / (η * k) + 1) := by
            refine mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = (T : ℝ) / (η ^ 2 * k) + 1 / η := by field_simp <;> ring
    have hsum1 : ((∑ p ∈ L, (k / p) * (T / p + 1) : ℕ) : ℝ)
        ≤ (L.card : ℝ) * ((T : ℝ) / (η ^ 2 * k) + 1 / η) := by
      push_cast
      calc ∑ p ∈ L, ((k / p : ℕ) : ℝ) * (((T / p : ℕ) : ℝ) + 1)
          ≤ ∑ _p ∈ L, ((T : ℝ) / (η ^ 2 * k) + 1 / η) := Finset.sum_le_sum hbound
        _ = (L.card : ℝ) * ((T : ℝ) / (η ^ 2 * k) + 1 / η) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hTR : ((T : ℕ) : ℝ) = 2 * (k : ℝ) := by rw [hT_def]; push_cast; ring
    have hfin : (L.card : ℝ) * ((T : ℝ) / (η ^ 2 * k) + 1 / η) < (T : ℝ) := by
      rw [hTR]
      have hfac : (0 : ℝ) ≤ (2 * (k : ℝ)) / (η ^ 2 * k) + 1 / η := by positivity
      calc (L.card : ℝ) * ((2 * (k : ℝ)) / (η ^ 2 * k) + 1 / η)
          ≤ (η ^ 2 * k / 4) * ((2 * (k : ℝ)) / (η ^ 2 * k) + 1 / η) :=
            mul_le_mul_of_nonneg_right hLcard hfac
        _ = (k : ℝ) / 2 + η * k / 4 := by field_simp; ring
        _ < 2 * (k : ℝ) := by nlinarith
    have : ((∑ p ∈ L, (k / p) * (T / p + 1) : ℕ) : ℝ) < ((T : ℕ) : ℝ) :=
      lt_of_le_of_lt hsum1 hfin
    exact_mod_cast this
  
  obtain ⟨s, hs1, hsT, hsavoid⟩ :=
    exists_multiplier_avoiding (L := L) (u := fun p => R / p) (d := fun p => k / p) (T := T)
      hLprime (fun p hp => (hF5 p hp).2) hsieve
  
  have h23 : ({2, 3} : Finset ℕ) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · rw [hS_def]
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by norm_num, by omega⟩, Nat.prime_two⟩
    · rw [hS_def]
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by norm_num, by omega⟩, Nat.prime_three⟩
  have hprod23 : (2 : ℕ) ^ (Nat.log 2 k + 1) * 3 ^ (Nat.log 3 k + 1) ≤ RS := by
    rw [hRS_def]
    have hstep := Finset.prod_le_prod_of_subset_of_one_le'
      (f := fun p : ℕ => p ^ (Nat.log p k + 1)) h23
      (fun i hi _ => Nat.one_le_pow _ _ (hSprime i hi).pos)
    simpa using hstep
  have hA : k < 2 ^ (Nat.log 2 k + 1) := Nat.lt_pow_succ_log_self (by norm_num) k
  have hB : 3 ≤ 3 ^ (Nat.log 3 k + 1) := by
    have h1 : (3 : ℕ) ^ 1 ≤ 3 ^ (Nat.log 3 k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using h1
  have hRSbig : k + 3 ≤ RS := by
    calc k + 3 ≤ (k + 1) * 3 := by omega
      _ ≤ 2 ^ (Nat.log 2 k + 1) * 3 ^ (Nat.log 3 k + 1) := Nat.mul_le_mul (by omega) hB
      _ ≤ RS := hprod23
  have hRbig : k + 3 ≤ R := by
    rw [hR_def]
    calc k + 3 ≤ RS := hRSbig
      _ = RS * 1 := (mul_one RS).symm
      _ ≤ RS * RL := Nat.mul_le_mul (le_refl RS) hRLpos
  set M : ℕ := s * R with hM_def
  have hMbig : k + 3 ≤ M := by
    rw [hM_def]
    calc k + 3 ≤ R := hRbig
      _ = 1 * R := (one_mul R).symm
      _ ≤ s * R := Nat.mul_le_mul hs1 (le_refl R)
  set n : ℕ := M - 1 with hn_def
  have hnbig : k + 2 ≤ n := by rw [hn_def]; omega
  have hM1 : 1 ≤ M := by omega
  
  have hdig : ∀ p : ℕ, p.Prime → p ≤ k → ∀ i : ℕ, k / p ^ i % p ≤ n / p ^ i % p := by
    intro p hpp hpk i
    have hp2 : 2 ≤ p := hpp.two_le
    have hppos : 0 < p := hpp.pos
    by_cases hcase : p ≤ y
    · 
      have hpS : p ∈ S := by
        rw [hS_def]
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hppos, hcase⟩, hpp⟩
      have hdvdRS : p ^ (Nat.log p k + 1) ∣ RS := by
        rw [hRS_def]
        exact Finset.dvd_prod_of_mem (fun q => q ^ (Nat.log q k + 1)) hpS
      have hdvdM : p ^ (Nat.log p k + 1) ∣ M := by
        rw [hM_def, hR_def]
        exact Dvd.dvd.mul_left (Dvd.dvd.mul_right hdvdRS RL) s
      obtain ⟨hd1, -⟩ := digits_of_pred_of_pow_dvd hp2 hM1 hdvdM
      by_cases hi : i < Nat.log p k + 1
      · rw [hn_def, hd1 i hi]
        exact Nat.le_pred_of_lt (Nat.mod_lt _ hppos)
      · push_neg at hi
        have hbig : k < p ^ i := by
          calc k < p ^ (Nat.log p k + 1) := Nat.lt_pow_succ_log_self (by omega) k
            _ ≤ p ^ i := Nat.pow_le_pow_right (by omega) hi
        rw [Nat.div_eq_of_lt hbig]
        simp
    · 
      push_neg at hcase
      have hpL : p ∈ L := by
        rw [hL_def]
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hcase, hpk⟩, hpp⟩
      have hpR : p ∣ R := (hF5 p hpL).1
      have hpM : p ^ 1 ∣ M := by
        rw [pow_one, hM_def]
        exact Dvd.dvd.mul_left hpR s
      obtain ⟨hd1, hd2⟩ := digits_of_pred_of_pow_dvd hp2 hM1 hpM
      match i with
      | 0 =>
        rw [hn_def, hd1 0 (by norm_num)]
        exact Nat.le_pred_of_lt (Nat.mod_lt _ hppos)
      | 1 =>
        have hRppos : 0 < R / p := Nat.one_le_div_iff hppos |>.mpr (Nat.le_of_dvd hRpos hpR)
        have hu1 : 1 ≤ s * (R / p) := Nat.mul_pos hs1 hRppos
        have hMp : M / p ^ 1 = s * (R / p) := by
          rw [pow_one, hM_def]; exact Nat.mul_div_assoc s hpR
        have hs3 := le_mod_pred_of_not_mem_Icc (p := p) (z := s * (R / p)) (d := k / p)
          hppos hu1 (hF4 p hpL) (hsavoid p hpL)
        rw [hn_def, hd2, hMp, pow_one, Nat.mod_eq_of_lt (hF4 p hpL)]
        exact hs3
      | (j + 2) =>
        have hbig : k < p ^ (j + 2) := by
          calc k < p * p := hF3 p hpL
            _ = p ^ 2 := by ring
            _ ≤ p ^ (j + 2) := Nat.pow_le_pow_right (by omega) (by omega)
        rw [Nat.div_eq_of_lt hbig]
        simp
  
  have hgle : g k ≤ n := by
    have hmem : n ∈ {m | k + 1 < m ∧ k < (m.choose k).minFac} := by
      refine ⟨by omega, ?_⟩
      exact minFac_choose_gt_of_digits_le (by omega) hnbig hdig
    exact Nat.sInf_le hmem
  
  have hlogRS : Real.log ((RS : ℕ) : ℝ) = ∑ p ∈ S, ((Nat.log p k : ℝ) + 1) * Real.log (p : ℝ) := by
    rw [hRS_def]
    push_cast
    rw [Real.log_prod]
    · refine Finset.sum_congr rfl ?_
      intro p hp
      rw [Real.log_pow]
      push_cast
      ring
    · intro p hp
      have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (hSprime p hp).pos
      exact pow_ne_zero _ (ne_of_gt hp0)
  have hlogRL : Real.log ((RL : ℕ) : ℝ) = ∑ p ∈ L, Real.log (p : ℝ) := by
    rw [hRL_def]
    push_cast
    rw [Real.log_prod]
    intro p hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (hLprime p hp).pos
    exact ne_of_gt hp0
  have hRSne : ((RS : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < ((RS : ℕ) : ℝ) := by exact_mod_cast hRSpos
    exact ne_of_gt this
  have hRLne : ((RL : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < ((RL : ℕ) : ℝ) := by exact_mod_cast hRLpos
    exact ne_of_gt this
  have hRne : ((R : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < ((R : ℕ) : ℝ) := by exact_mod_cast hRpos
    exact ne_of_gt this
  have hTne : ((T : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < ((T : ℕ) : ℝ) := by exact_mod_cast hTpos
    exact ne_of_gt this
  have hRcast : ((R : ℕ) : ℝ) = ((RS : ℕ) : ℝ) * ((RL : ℕ) : ℝ) := by
    rw [hR_def]; push_cast; ring
  have hlogR : Real.log ((R : ℕ) : ℝ)
      = (∑ p ∈ S, ((Nat.log p k : ℝ) + 1) * Real.log (p : ℝ)) + ∑ p ∈ L, Real.log (p : ℝ) := by
    rw [hRcast, Real.log_mul hRSne hRLne, hlogRS, hlogRL]
  have hlogT : Real.log ((T : ℕ) : ℝ) ≤ η * k := by
    have hTR : ((T : ℕ) : ℝ) = 2 * (k : ℝ) := by rw [hT_def]; push_cast; ring
    rw [hTR]
    have hx : (0 : ℝ) < 2 * (k : ℝ) := by linarith
    have h1 : Real.log (Real.sqrt (2 * (k : ℝ))) ≤ Real.sqrt (2 * (k : ℝ)) - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx)
    have h2 : Real.log (Real.sqrt (2 * (k : ℝ))) = Real.log (2 * (k : ℝ)) / 2 :=
      Real.log_sqrt hx.le
    have hge : 2 * (k : ℝ) ≤ (η * k / 2) ^ 2 := by nlinarith
    have hstep : Real.sqrt (2 * (k : ℝ)) ≤ η * k / 2 := by
      calc Real.sqrt (2 * (k : ℝ)) ≤ Real.sqrt ((η * k / 2) ^ 2) := Real.sqrt_le_sqrt hge
        _ = η * k / 2 := Real.sqrt_sq (by positivity)
    linarith
  have hgTR : ((g k : ℕ) : ℝ) ≤ ((T : ℕ) : ℝ) * ((R : ℕ) : ℝ) := by
    have h2 : n ≤ T * R := by
      calc n = M - 1 := hn_def
        _ ≤ M := Nat.sub_le _ _
        _ = s * R := hM_def
        _ ≤ T * R := Nat.mul_le_mul hsT (le_refl R)
    have h3 : g k ≤ T * R := le_trans hgle h2
    have h4 : ((g k : ℕ) : ℝ) ≤ ((T * R : ℕ) : ℝ) := by exact_mod_cast h3
    rwa [Nat.cast_mul] at h4
  have hlogTR : Real.log (((T : ℕ) : ℝ) * ((R : ℕ) : ℝ)) ≤ Chebyshev.theta (k : ℝ) + ε * k := by
    rw [Real.log_mul hTne hRne, hlogR]
    have hkc : (0 : ℝ) ≤ (k : ℝ) := hkR.le
    nlinarith [hH4, hthetaL, hlogT, hηε, hkc]
  have hpos : (0 : ℝ) < ((T : ℕ) : ℝ) * ((R : ℕ) : ℝ) := by
    have h1 : (0 : ℝ) < ((T : ℕ) : ℝ) := by exact_mod_cast hTpos
    have h2 : (0 : ℝ) < ((R : ℕ) : ℝ) := by exact_mod_cast hRpos
    exact mul_pos h1 h2
  calc ((g k : ℕ) : ℝ) ≤ ((T : ℕ) : ℝ) * ((R : ℕ) : ℝ) := hgTR
    _ = Real.exp (Real.log (((T : ℕ) : ℝ) * ((R : ℕ) : ℝ))) := (Real.exp_log hpos).symm
    _ ≤ Real.exp (Chebyshev.theta (k : ℝ) + ε * k) := Real.exp_le_exp.mpr hlogTR

theorem erdos_1095.variants.upper_conjecture : ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧ ∀ᶠ k in atTop, g k ≤ exp (k * (1 + f k)) :=
by
  
  
  have cast_le_exp : ∀ (m : ℕ) (y : ℝ), Real.log m ≤ y → (m : ℝ) ≤ Real.exp y := by
    intro m y hy
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simpa using (Real.exp_pos y).le
    · have hm : (0 : ℝ) < m := by exact_mod_cast h0
      exact (Real.log_le_iff_le_exp hm).mp hy
  have log_le_of_le_exp :
      ∀ (m : ℕ) (y : ℝ), 0 ≤ y → (m : ℝ) ≤ Real.exp y → Real.log m ≤ y := by
    intro m y hy hm
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simpa using hy
    · have hmp : (0 : ℝ) < m := by exact_mod_cast h0
      exact (Real.log_le_iff_le_exp hmp).mpr hm
  
  have key : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (g k : ℝ) ≤ Real.exp ((1 + ε) * k) := by
    intro ε hε
    have hhalf : (0 : ℝ) < ε / 2 := by positivity
    have h1 := g_le_exp_theta_add_eps (ε / 2) hhalf
    have h2 : ∀ᶠ k : ℕ in atTop, Chebyshev.theta k ≤ (1 + ε / 2) * k :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
        (chebyshev_theta_le_one_add_eps (ε / 2) hhalf)
    filter_upwards [h1, h2] with k hk1 hk2
    refine hk1.trans (Real.exp_le_exp.mpr ?_)
    linarith
  
  refine ⟨fun k => max 0 (Real.log (g k) / (k : ℝ) - 1), ?_, ?_⟩
  · 
    rw [NormedAddCommGroup.tendsto_nhds_zero]
    intro ε hε
    have hhalf : (0 : ℝ) < ε / 2 := by positivity
    filter_upwards [key (ε / 2) hhalf, eventually_ge_atTop 1] with k hk hk1
    show ‖max 0 (Real.log (g k) / (k : ℝ) - 1)‖ < ε
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hnonneg : (0 : ℝ) ≤ (1 + ε / 2) * (k : ℝ) :=
      mul_nonneg (by linarith) hkpos.le
    have hlog : Real.log (g k) ≤ (1 + ε / 2) * (k : ℝ) :=
      log_le_of_le_exp _ _ hnonneg hk
    have hub : max 0 (Real.log (g k) / (k : ℝ) - 1) ≤ ε / 2 := by
      refine max_le hhalf.le ?_
      have hd : Real.log (g k) / (k : ℝ) ≤ 1 + ε / 2 := by
        rw [div_le_iff₀ hkpos]; linarith
      linarith
    have hnn : (0 : ℝ) ≤ max 0 (Real.log (g k) / (k : ℝ) - 1) := le_max_left _ _
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    linarith
  · 
    filter_upwards [eventually_ge_atTop 1] with k hk1
    show (g k : ℝ) ≤ Real.exp ((k : ℝ) * (1 + max 0 (Real.log (g k) / (k : ℝ) - 1)))
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
    refine cast_le_exp _ _ ?_
    by_cases hc : Real.log (g k) / (k : ℝ) - 1 ≤ 0
    · have hF : max 0 (Real.log (g k) / (k : ℝ) - 1) = 0 := max_eq_left hc
      rw [hF]
      have hle : Real.log (g k) ≤ (k : ℝ) :=
        (div_le_one hkpos).mp (by linarith)
      nlinarith [hle]
    · have hc' : (0 : ℝ) ≤ Real.log (g k) / (k : ℝ) - 1 := le_of_lt (not_le.mp hc)
      have hF : max 0 (Real.log (g k) / (k : ℝ) - 1) = Real.log (g k) / (k : ℝ) - 1 :=
        max_eq_right hc'
      rw [hF]
      have heq : (k : ℝ) * (1 + (Real.log (g k) / (k : ℝ) - 1)) = Real.log (g k) := by
        field_simp
        ring
      rw [heq]
