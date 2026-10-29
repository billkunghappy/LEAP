-- [START_IMMUTABLE_CONTEXT]
import Mathlib
set_option maxHeartbeats 4000000

open Nat Filter Finset
open scoped Asymptotics Topology Nat
namespace Erdos394
/--
Let $t_k(n)$ denote the least $m$ such that $n\mid m(m+1)(m+2)\cdots (m+k-1).$
-/
noncomputable def t (k n : ℕ) : ℕ :=
  sInf { m : ℕ | 0 < m ∧ n ∣ ∏ i ∈ range k, (m + i) }
/-- `t k n = v` when `v` works and nothing positive below it does. -/

theorem t_eq_of {n k v : ℕ} (hv : 0 < v)
    (hdvd : n ∣ ∏ i ∈ range k, (v + i))
    (hlt : ∀ m ∈ range v, 0 < m → ¬ (n ∣ ∏ i ∈ range k, (m + i))) :
    t k n = v := by
  refine le_antisymm (Nat.sInf_le ⟨hv, hdvd⟩) ?_
  by_contra hc
  push_neg at hc
  have hne : { m : ℕ | 0 < m ∧ n ∣ ∏ i ∈ range k, (m + i) }.Nonempty := ⟨v, hv, hdvd⟩
  obtain ⟨hpos, hd⟩ := Nat.sInf_mem hne
  exact hlt _ (mem_range.mpr hc) hpos hd
/-- The least positive multiple of `n` is `n`, so `t 1 n = n`. -/

theorem t_one {n : ℕ} (hn : 0 < n) : t 1 n = n := by
  refine le_antisymm (Nat.sInf_le ⟨hn, by simp⟩) ?_
  have hne : { m : ℕ | 0 < m ∧ n ∣ ∏ i ∈ range 1, (m + i) }.Nonempty := ⟨n, hn, by simp⟩
  obtain ⟨hpos, hd⟩ := Nat.sInf_mem hne
  rw [prod_range_one, add_zero] at hd
  exact Nat.le_of_dvd hpos hd
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

-- Target under refutation. It is assumed here so that deriving `False`
-- below refutes it. Nothing proved from it may leave this file.
axiom erdos_394.variants.hall_conjecture : ∀ c < Real.log 2, (fun x ↦ ∑ n ∈ Icc 1 ⌊x⌋₊, (t 2 n : ℝ)) =o[atTop] (fun x ↦ x ^ 2 / (Real.log x) ^ c)
-- [END_IMMUTABLE_CONTEXT]

-- [START_PROOF]
theorem erdos_394.variants.hall_conjecture_disproof : False :=
by
  ------------------------------------------------------------------
  have hall := erdos_394.variants.hall_conjecture
  have hc : (2/3:ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 ((hall (2/3) hc).bound (show (0:ℝ) < 1 by norm_num))
  obtain ⟨Y2, hY2⟩ := K3
  obtain ⟨Y1, hY1⟩ := Filter.eventually_atTop.1 K4
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9
  have hnat : Tendsto (fun M : ℕ => (M:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hE : Tendsto (fun M : ℕ => Real.exp (2 * (M:ℝ))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (hnat.const_mul_atTop (by norm_num))
  have ev1 : ∀ᶠ M : ℕ in atTop, X ≤ Real.exp (Real.exp (2 * (M:ℝ))) :=
    (Real.tendsto_exp_atTop.comp hE).eventually_ge_atTop X
  have ev2 : ∀ᶠ M : ℕ in atTop, max Y1 Y2 ≤ Real.exp (3/4 * Real.exp (2 * (M:ℝ))) :=
    (Real.tendsto_exp_atTop.comp (hE.const_mul_atTop (by norm_num))).eventually_ge_atTop _
  have ev3 : ∀ᶠ M : ℕ in atTop, 200 ≤ M := eventually_ge_atTop 200
  have ev4 : ∀ᶠ M : ℕ in atTop, Real.log (4 * (M:ℝ)) ≤ 4 * (M:ℝ) / 100 := by
    have h := Real.isLittleO_log_id_atTop.bound (show (0:ℝ) < 1/100 by norm_num)
    have h4 : Tendsto (fun M : ℕ => 4 * (M:ℝ)) atTop atTop := hnat.const_mul_atTop (by norm_num)
    filter_upwards [h4.eventually h, h4.eventually (eventually_ge_atTop 1)] with M hM hM1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hM1),
      abs_of_nonneg (show (0:ℝ) ≤ id (4 * (M:ℝ)) by simp only [id]; linarith)] at hM
    simp only [id] at hM; linarith
  have ev5 : ∀ᶠ M : ℕ in atTop, 20 * (M:ℝ) ≤ Real.exp (2 * (M:ℝ)) := by
    have h := (isLittleO_pow_exp_pos_mul_atTop 1 (show (0:ℝ) < 2 by norm_num)).bound
      (show (0:ℝ) < 1/20 by norm_num)
    filter_upwards [hnat.eventually h] with M hM
    rw [Real.norm_eq_abs, Real.norm_eq_abs, pow_one, abs_of_nonneg (Nat.cast_nonneg M),
      abs_of_nonneg (Real.exp_pos _).le] at hM
    linarith
  have ev6 : ∀ᶠ M : ℕ in atTop, 334234 * (M:ℝ)^2 * (1.95:ℝ)^M < (2.5:ℝ)^M := by
    have h := tendsto_pow_const_div_const_pow_of_one_lt 2 (show (1:ℝ) < 2.5/1.95 by norm_num)
    filter_upwards [(h.eventually (gt_mem_nhds (show (0:ℝ) < 1/334234 by norm_num)))] with M hM
    rw [div_pow, div_div_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)] at hM
    linarith
  obtain ⟨M, hM1, hM2, hM3, hM4, hM5, hM6⟩ :=
    (ev1.and (ev2.and (ev3.and (ev4.and (ev5.and ev6))))).exists
  set Mr : ℝ := (M:ℝ) with hMr
  have hMr200 : (200:ℝ) ≤ Mr := by rw [hMr]; exact_mod_cast hM3
  have hMr0 : 0 < Mr := by linarith
  set E := Real.exp (2 * Mr) with hEdef
  have hE20 : 20 * Mr ≤ E := hM5
  have hE0 : 0 < E := Real.exp_pos _
  set x := Real.exp E with hxdef
  have hx0 : 0 < x := Real.exp_pos _
  have hlogx : Real.log x = E := Real.log_exp E
  set y := Real.exp (E / (4 * Mr)) with hydef
  have hy0 : 0 < y := Real.exp_pos _
  have hlogy : Real.log y = E / (4 * Mr) := Real.log_exp _
  set δ : ℝ := 1 / (1920 * Mr * (2.02:ℝ)^M) with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδdef, div_le_one (by positivity)]
    have : (1:ℝ) ≤ (2.02:ℝ)^M := one_le_pow₀ (by norm_num)
    nlinarith
  have hδx : 8 ≤ δ * x := by
    rw [hδdef, one_div_mul_eq_div, le_div_iff₀ (by positivity)]
    have h1 : (15360:ℝ) ≤ Real.exp 10 := by
      have h : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h]
      have h5 : (2.7:ℝ)^10 ≤ Real.exp 1 ^ 10 := pow_le_pow_left₀ (by norm_num) (by linarith) 10
      norm_num at h5; linarith
    have h2 : Mr ≤ Real.exp Mr := by have := Real.add_one_le_exp Mr; linarith
    have h3 : (2.02:ℝ)^M ≤ Real.exp Mr := by
      rw [hMr, ← Real.exp_one_pow]
      exact pow_le_pow_left₀ (by norm_num) (by linarith) M
    have h4 : Real.exp 10 * Real.exp Mr * Real.exp Mr ≤ x := by
      rw [← Real.exp_add, ← Real.exp_add, hxdef]
      apply Real.exp_le_exp.2; linarith
    calc 8 * (1920 * Mr * (2.02:ℝ)^M) = 15360 * Mr * (2.02:ℝ)^M := by ring
      _ ≤ Real.exp 10 * Real.exp Mr * Real.exp Mr := by
          apply mul_le_mul (mul_le_mul h1 h2 hMr0.le (Real.exp_pos _).le) h3 (by positivity)
            (by positivity)
      _ ≤ x := h4
  set P := (Finset.range (⌊y⌋₊+1)).filter (fun p => p.Prime ∧ 101 < p) with hPdef
  set DD := P.powersetCard M with hDD
  have hPmem : ∀ p ∈ P, p.Prime ∧ 101 < p ∧ (p:ℝ) ≤ y := by
    intro p hp
    rw [hPdef, Finset.mem_filter, Finset.mem_range] at hp
    refine ⟨hp.2.1, hp.2.2, ?_⟩
    have : p ≤ ⌊y⌋₊ := by omega
    exact (Nat.le_floor_iff hy0.le).1 this
  have hyY : 4 * y < Real.exp (3/4 * E) := by
    have h4 : (4:ℝ) < Real.exp 2 := by
      have h : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h]; nlinarith
    have h5 : E / (4 * Mr) + 2 ≤ 3/4 * E := by
      rw [div_add' _ _ _ (by positivity), div_le_iff₀ (by positivity)]; nlinarith
    calc 4 * y < Real.exp 2 * y := mul_lt_mul_of_pos_right h4 hy0
      _ = Real.exp (E / (4 * Mr) + 2) := by rw [Real.exp_add, hydef]; ring
      _ ≤ Real.exp (3/4 * E) := Real.exp_le_exp.2 h5
  have hDmem : ∀ D ∈ DD, D ⊆ P ∧ D.card = M := fun D hD => Finset.mem_powersetCard.1 hD
  have hbpos : ∀ D ∈ DD, 0 < ∏ p ∈ D, p := fun D hD =>
    Finset.prod_pos (fun p hp => (hPmem p ((hDmem D hD).1 hp)).1.pos)
  have hbR : ∀ D ∈ DD, ((∏ p ∈ D, p : ℕ) : ℝ) ≤ Real.exp (E/4) := by
    intro D hD
    push_cast
    calc ∏ p ∈ D, (p:ℝ) ≤ ∏ p ∈ D, y :=
          Finset.prod_le_prod (fun p _ => Nat.cast_nonneg p)
            (fun p hp => (hPmem p ((hDmem D hD).1 hp)).2.2)
      _ = y^M := by rw [Finset.prod_const, (hDmem D hD).2]
      _ = Real.exp (E/4) := by
          rw [hydef, ← Real.exp_nat_mul]; congr 1; rw [← hMr]; field_simp
  have hb1 : ∀ D ∈ DD, (1:ℝ) ≤ ((∏ p ∈ D, p : ℕ) : ℝ) := fun D hD => by
    exact_mod_cast hbpos D hD
  set GG : Finset ℕ → Finset ℕ := fun D =>
    ((Finset.Ioc ⌊x / ((∏ p ∈ D, p : ℕ):ℝ) / 4⌋₊ ⌊x / ((∏ p ∈ D, p : ℕ):ℝ)⌋₊).filter Nat.Prime).filter
      (fun a => ¬ ∃ d ∈ (∏ p ∈ D, p).divisors, ∃ u : ℕ, 1 ≤ u ∧ u < (∏ p ∈ D, p)/d ∧
        (∏ p ∈ D, p)/d ∣ a*d*u+1 ∧ ((u:ℝ) < δ * (((∏ p ∈ D, p)/d:ℕ):ℝ) ∨
          (((∏ p ∈ D, p)/d:ℕ):ℝ) < u + δ * (((∏ p ∈ D, p)/d:ℕ):ℝ))) with hGG
  have hper : ∀ D ∈ DD, x / (8 * ((∏ p ∈ D, p : ℕ):ℝ) * E) ≤ ((GG D).card : ℝ) ∧
      ∀ a ∈ GG D, a.Prime ∧ ⌊y⌋₊ < a ∧ a * (∏ p ∈ D, p) ∈ Finset.Icc 1 ⌊x⌋₊ ∧
        δ * x / 8 ≤ (t 2 (a * ∏ p ∈ D, p) : ℝ) := by
    intro D hD
    obtain ⟨hDP, hDc⟩ := hDmem D hD
    have hDprime : ∀ p ∈ D, p.Prime := fun p hp => (hPmem p (hDP hp)).1
    have hb0 : 0 < ∏ p ∈ D, p := hbpos D hD
    have hbR' := hbR D hD
    have hb1' := hb1 D hD
    have hGGeq : GG D = ((Finset.Ioc ⌊x / ((∏ p ∈ D, p : ℕ):ℝ) / 4⌋₊ ⌊x / ((∏ p ∈ D, p : ℕ):ℝ)⌋₊).filter
        Nat.Prime).filter
      (fun a => ¬ ∃ d ∈ (∏ p ∈ D, p).divisors, ∃ u : ℕ, 1 ≤ u ∧ u < (∏ p ∈ D, p)/d ∧
        (∏ p ∈ D, p)/d ∣ a*d*u+1 ∧ ((u:ℝ) < δ * (((∏ p ∈ D, p)/d:ℕ):ℝ) ∨
          (((∏ p ∈ D, p)/d:ℕ):ℝ) < u + δ * (((∏ p ∈ D, p)/d:ℕ):ℝ))) := rfl
    rw [hGGeq]
    generalize hbdef : ∏ p ∈ D, p = b at *
    set Y := x / (b:ℝ) with hY
    have hYge : Real.exp (3/4 * E) ≤ Y := by
      rw [hY, le_div_iff₀ (by linarith)]
      calc Real.exp (3/4*E) * b ≤ Real.exp (3/4*E) * Real.exp (E/4) :=
            mul_le_mul_of_nonneg_left hbR' (Real.exp_pos _).le
        _ = x := by rw [← Real.exp_add, hxdef]; ring_nf
    have hY0 : 0 < Y := lt_of_lt_of_le (Real.exp_pos _) hYge
    have hYx : Y ≤ x := by rw [hY]; exact div_le_self hx0.le hb1'
    have hlogY : Real.log Y ≤ E := by rw [← hlogx]; exact Real.log_le_log hY0 hYx
    have hlogY' : 3/4 * E ≤ Real.log Y := by
      rw [← Real.log_exp (3/4*E)]; exact Real.log_le_log (Real.exp_pos _) hYge
    have hlogY1 : 1 ≤ Real.log Y := by linarith
    have hlogY0 : 0 < Real.log Y := by linarith
    have hllY : Real.log (Real.log Y) ≤ 2 * Mr := by
      calc Real.log (Real.log Y) ≤ Real.log E := Real.log_le_log hlogY0 hlogY
        _ = 2 * Mr := Real.log_exp _
    have hllY0 : 0 ≤ Real.log (Real.log Y) := Real.log_nonneg hlogY1
    have hYY1 : Y1 ≤ Y := le_trans (le_trans (le_max_left _ _) hM2) hYge
    have hYY2 : Y2 ≤ Y := le_trans (le_trans (le_max_right _ _) hM2) hYge
    set A := (Finset.Ioc ⌊Y/4⌋₊ ⌊Y⌋₊).filter Nat.Prime with hA
    have hAcard := hY1 Y hYY1
    set U : ℕ → ℝ := fun B => 60 * (101/100:ℝ)^(B.primeFactors.card) * Real.log (Real.log Y) * Y /
      (B * Real.log Y) with hU
    have hUbound : ∀ d ∈ b.divisors, ∀ r : ℕ,
        ((A.filter (fun a => a ≡ r [MOD b/d])).card : ℝ) ≤ U (b/d) := by
      intro d hd r
      have hdb : d ∣ b := Nat.dvd_of_mem_divisors hd
      have hB0 : 0 < b/d := Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)
      have hBle : b/d ≤ b := Nat.div_le_self _ _
      have hB3 : ((b/d : ℕ):ℝ)^3 ≤ Y := by
        have h1 : ((b/d : ℕ):ℝ) ≤ Real.exp (E/4) := le_trans (by exact_mod_cast hBle) hbR'
        calc ((b/d : ℕ):ℝ)^3 ≤ (Real.exp (E/4))^3 := pow_le_pow_left₀ (Nat.cast_nonneg _) h1 3
          _ = Real.exp (3/4 * E) := by rw [← Real.exp_nat_mul]; ring_nf
          _ ≤ Y := hYge
      have hBpf : ∀ p ∈ (b/d).primeFactors, 101 < p := by
        intro p hp
        have : p ∈ b.primeFactors := Nat.primeFactors_mono (Nat.div_dvd_of_dvd hdb) hb0.ne' hp
        rw [← hbdef, Nat.primeFactors_prod hDprime] at this
        exact (hPmem p (hDP this)).2.1
      refine le_trans ?_ (hY2 Y hYY2 (b/d) r hB0 hB3 hBpf)
      exact_mod_cast Finset.card_le_card (by
        intro a ha
        simp only [hA, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at ha ⊢
        exact ⟨by omega, ha.1.2, ha.2⟩)
    have hbad := K2 A b hb0 δ hδ0.le U hUbound
    have hsum : ∑ d ∈ b.divisors, 2 * δ * ((b/d:ℕ):ℝ) * U (b/d) ≤ Y / (8 * Real.log Y) := by
      have hterm : ∀ d ∈ b.divisors, 2 * δ * ((b/d:ℕ):ℝ) * U (b/d) ≤
          120 * δ * (101/100:ℝ)^M * (2 * Mr) * Y / Real.log Y := by
        intro d hd
        have hdb : d ∣ b := Nat.dvd_of_mem_divisors hd
        have hB0 : (0:ℝ) < ((b/d:ℕ):ℝ) := by
          exact_mod_cast Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)
        have hω : (b/d).primeFactors.card ≤ M := by
          have : (b/d).primeFactors ⊆ D := by
            intro p hp
            have := Nat.primeFactors_mono (Nat.div_dvd_of_dvd hdb) hb0.ne' hp
            rwa [← hbdef, Nat.primeFactors_prod hDprime] at this
          rw [← hDc]; exact Finset.card_le_card this
        have hρ : (101/100:ℝ)^((b/d).primeFactors.card) ≤ (101/100:ℝ)^M :=
          pow_le_pow_right₀ (by norm_num) hω
        simp only [hU]
        have e : 2 * δ * ((b/d:ℕ):ℝ) * (60 * (101/100:ℝ)^((b/d).primeFactors.card) *
            Real.log (Real.log Y) * Y / (((b/d:ℕ):ℝ) * Real.log Y))
            = 120 * δ * ((101/100:ℝ)^((b/d).primeFactors.card) * Real.log (Real.log Y)) * Y /
              Real.log Y := by
          field_simp; ring
        rw [e]
        apply div_le_div_of_nonneg_right _ hlogY0.le
        have h1 := mul_le_mul hρ hllY hllY0 (by positivity)
        have h2 : 0 ≤ 120 * δ := by positivity
        have h3 := mul_le_mul_of_nonneg_left h1 h2
        have h4 := mul_le_mul_of_nonneg_right h3 hY0.le
        calc 120 * δ * ((101/100:ℝ)^((b/d).primeFactors.card) * Real.log (Real.log Y)) * Y
            ≤ 120 * δ * ((101/100:ℝ)^M * (2 * Mr)) * Y := h4
          _ = 120 * δ * (101/100:ℝ)^M * (2 * Mr) * Y := by ring
      calc ∑ d ∈ b.divisors, 2 * δ * ((b/d:ℕ):ℝ) * U (b/d)
          ≤ ∑ d ∈ b.divisors, 120 * δ * (101/100:ℝ)^M * (2 * Mr) * Y / Real.log Y :=
            Finset.sum_le_sum hterm
        _ = (b.divisors.card : ℝ) * (120 * δ * (101/100:ℝ)^M * (2 * Mr) * Y / Real.log Y) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2:ℝ)^M * (120 * δ * (101/100:ℝ)^M * (2 * Mr) * Y / Real.log Y) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have := Kdiv D hDprime
            rw [hDc, hbdef] at this
            exact_mod_cast this
        _ = Y / (8 * Real.log Y) := by
            rw [hδdef]
            have : (2.02:ℝ)^M = (2:ℝ)^M * (101/100:ℝ)^M := by rw [← mul_pow]; norm_num
            rw [this]
            field_simp
            ring
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card (s := A)
      (fun a => ∃ d ∈ b.divisors, ∃ u : ℕ, 1 ≤ u ∧ u < b/d ∧ b/d ∣ a*d*u+1 ∧
        ((u:ℝ) < δ * ((b/d:ℕ):ℝ) ∨ ((b/d:ℕ):ℝ) < u + δ * ((b/d:ℕ):ℝ)))
    constructor
    · have h1 : ((A.filter (fun a => ∃ d ∈ b.divisors, ∃ u : ℕ, 1 ≤ u ∧ u < b/d ∧ b/d ∣ a*d*u+1 ∧
          ((u:ℝ) < δ * ((b/d:ℕ):ℝ) ∨ ((b/d:ℕ):ℝ) < u + δ * ((b/d:ℕ):ℝ)))).card : ℝ) +
          ((A.filter (fun a => ¬ ∃ d ∈ b.divisors, ∃ u : ℕ, 1 ≤ u ∧ u < b/d ∧ b/d ∣ a*d*u+1 ∧
          ((u:ℝ) < δ * ((b/d:ℕ):ℝ) ∨ ((b/d:ℕ):ℝ) < u + δ * ((b/d:ℕ):ℝ)))).card : ℝ) = (A.card : ℝ) := by
        exact_mod_cast hsplit
      have h3 : x / (8 * (b:ℝ) * E) ≤ Y / (8 * Real.log Y) := by
        rw [hY, div_div]
        apply div_le_div_of_nonneg_left hx0.le (by positivity)
        have := mul_le_mul_of_nonneg_left hlogY (show (0:ℝ) ≤ b * 8 by positivity)
        linarith
      have h2 : Y / (4 * Real.log Y) = 2 * (Y / (8 * Real.log Y)) := by field_simp; ring
      linarith
    · intro a ha
      rw [Finset.mem_filter] at ha
      obtain ⟨haA, hgood⟩ := ha
      rw [Finset.mem_filter, Finset.mem_Ioc] at haA
      obtain ⟨⟨ha1, ha2⟩, hap⟩ := haA
      have haY4 : Y/4 < a := (Nat.floor_lt (by positivity)).1 ha1
      have haY : (a:ℝ) ≤ Y := (Nat.le_floor_iff hY0.le).1 ha2
      have hay : ⌊y⌋₊ < a := by
        apply (Nat.floor_lt hy0.le).2
        linarith
      have hab_le : ((a * b : ℕ):ℝ) ≤ x := by
        push_cast
        calc (a:ℝ) * b ≤ Y * b := mul_le_mul_of_nonneg_right haY (by linarith)
          _ = x := by rw [hY]; field_simp
      have hab_gt : x / 4 < ((a * b : ℕ):ℝ) := by
        push_cast
        calc x / 4 = Y / 4 * b := by rw [hY]; field_simp
          _ < a * b := mul_lt_mul_of_pos_right haY4 (by linarith)
      refine ⟨hap, hay, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        refine ⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hap.ne_zero hb0.ne'), ?_⟩
        exact Nat.le_floor hab_le
      · have hG : ∀ d ∈ b.divisors, ∀ u : ℕ, 1 ≤ u → u < b/d → b/d ∣ a*d*u+1 →
            δ * ((b/d : ℕ) : ℝ) ≤ u ∧ (u:ℝ) + δ * ((b/d : ℕ) : ℝ) ≤ ((b/d : ℕ) : ℝ) := by
          intro d hd u hu1 hu2 hu3
          by_contra hcon
          apply hgood
          refine ⟨d, hd, u, hu1, hu2, hu3, ?_⟩
          rw [not_and_or, not_le, not_le] at hcon
          exact hcon
        have hK1 := K1 a b δ hap hb0 hδ1 hG
        have : δ * (x/4) ≤ δ * ((a * b : ℕ):ℝ) := mul_le_mul_of_nonneg_left hab_gt.le hδ0.le
        linarith
  have hinj : Set.InjOn (fun σ : (Σ _ : Finset ℕ, ℕ) => σ.2 * ∏ p ∈ σ.1, p)
      (DD.sigma GG : Set (Σ _ : Finset ℕ, ℕ)) := by
    rintro ⟨D, a⟩ h1 ⟨D', a'⟩ h2 heq
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe] at h1 h2
    simp only at heq
    obtain ⟨hap, hay, -, -⟩ := (hper D h1.1).2 a h1.2
    obtain ⟨hap', hay', -, -⟩ := (hper D' h2.1).2 a' h2.2
    have haa : a = a' := by
      have hdvd : a ∣ a' * ∏ p ∈ D', p := ⟨_, heq.symm⟩
      rcases (Nat.Prime.dvd_mul hap).1 hdvd with h | h
      · exact (Nat.prime_dvd_prime_iff_eq hap hap').1 h
      · exfalso
        obtain ⟨p, hp, hap_dvd⟩ := (Prime.dvd_finset_prod_iff hap.prime _).1 h
        have hpP := hPmem p ((hDmem D' h2.1).1 hp)
        have hap_eq := (Nat.prime_dvd_prime_iff_eq hap hpP.1).1 hap_dvd
        have hpy : p ≤ ⌊y⌋₊ := Nat.le_floor hpP.2.2
        omega
    subst haa
    have hprod : ∏ p ∈ D, p = ∏ p ∈ D', p := Nat.eq_of_mul_eq_mul_left hap.pos heq
    have hDD' : D = D' := by
      rw [← Nat.primeFactors_prod (fun p hp => (hPmem p ((hDmem D h1.1).1 hp)).1),
        ← Nat.primeFactors_prod (fun p hp => (hPmem p ((hDmem D' h2.1).1 hp)).1), hprod]
    subst hDD'; rfl
  have hF : ∑ D ∈ DD, ((GG D).card : ℝ) * (δ * x / 8) ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (t 2 n : ℝ) := by
    calc ∑ D ∈ DD, ((GG D).card : ℝ) * (δ * x / 8) = ∑ D ∈ DD, ∑ a ∈ GG D, (δ * x / 8) := by
          apply Finset.sum_congr rfl; intro D _; rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ D ∈ DD, ∑ a ∈ GG D, (t 2 (a * ∏ p ∈ D, p) : ℝ) := by
          apply Finset.sum_le_sum; intro D hD; apply Finset.sum_le_sum; intro a ha
          exact ((hper D hD).2 a ha).2.2.2
      _ = ∑ σ ∈ DD.sigma GG, (t 2 (σ.2 * ∏ p ∈ σ.1, p) : ℝ) :=
          (Finset.sum_sigma DD GG (fun σ => (t 2 (σ.2 * ∏ p ∈ σ.1, p) : ℝ))).symm
      _ = ∑ n ∈ (DD.sigma GG).image (fun σ : (Σ _ : Finset ℕ, ℕ) => σ.2 * ∏ p ∈ σ.1, p), (t 2 n : ℝ) :=
          (Finset.sum_image (f := fun n => (t 2 n : ℝ)) hinj).symm
      _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (t 2 n : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            rw [Finset.mem_image] at hn
            obtain ⟨⟨D, a⟩, hσ, rfl⟩ := hn
            rw [Finset.mem_sigma] at hσ
            exact ((hper D hσ.1).2 a hσ.2).2.2.1
          · intro n _ _; exact Nat.cast_nonneg _
  have hlow : δ * x^2 / (64 * E) * ∑ D ∈ DD, ∏ p ∈ D, (1/(p:ℝ)) ≤
      ∑ D ∈ DD, ((GG D).card : ℝ) * (δ * x / 8) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro D hD
    have h1 := (hper D hD).1
    have hprod : ∏ p ∈ D, (1/(p:ℝ)) = 1 / ((∏ p ∈ D, p : ℕ):ℝ) := by
      push_cast; rw [Finset.prod_div_distrib, Finset.prod_const_one]
    rw [hprod]
    have hb := hb1 D hD
    calc δ * x^2 / (64 * E) * (1 / ((∏ p ∈ D, p : ℕ):ℝ)) =
          x / (8 * ((∏ p ∈ D, p : ℕ):ℝ) * E) * (δ * x / 8) := by
          field_simp; ring
      _ ≤ ((GG D).card : ℝ) * (δ * x / 8) := mul_le_mul_of_nonneg_right h1 (by positivity)
  have hy1 : 1 ≤ y := by rw [hydef]; exact Real.one_le_exp (by positivity)
  have hfy : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy1)
  have hS : 2 * Mr - Real.log (4 * Mr) - 7 ≤ ∑ p ∈ P, (1/(p:ℝ)) := by
    have h5 := K5 ⌊y⌋₊ hfy
    have hsplit := Finset.sum_filter_add_sum_filter_not ((Finset.range (⌊y⌋₊+1)).filter Nat.Prime)
      (fun p => 101 < p) (fun p => 1/(p:ℝ))
    have hP' : ((Finset.range (⌊y⌋₊+1)).filter Nat.Prime).filter (fun p => 101 < p) = P := by
      rw [hPdef, Finset.filter_filter]
    rw [hP'] at hsplit
    have hsmall : ∑ p ∈ ((Finset.range (⌊y⌋₊+1)).filter Nat.Prime).filter (fun p => ¬ 101 < p),
        (1/(p:ℝ)) ≤ 6 := by
      refine le_trans ?_ Ksmall
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
        exact ⟨by omega, hp.1.2⟩
      · intro p _ _; positivity
    have hll : 2 * Mr - Real.log (4 * Mr) ≤ Real.log (Real.log ((⌊y⌋₊:ℝ) + 1)) := by
      have hy1' : y < (⌊y⌋₊:ℝ) + 1 := Nat.lt_floor_add_one y
      have hlogy0 : 0 < Real.log y := by rw [hlogy]; positivity
      have h1 : Real.log y ≤ Real.log ((⌊y⌋₊:ℝ) + 1) := Real.log_le_log hy0 hy1'.le
      calc 2 * Mr - Real.log (4 * Mr) = Real.log (Real.log y) := by
            rw [hlogy, Real.log_div hE0.ne' (by positivity), hEdef, Real.log_exp]
        _ ≤ _ := Real.log_le_log hlogy0 h1
    linarith
  have hSM : 1.9 * Mr ≤ ∑ p ∈ P, (1/(p:ℝ)) - (M:ℝ) * (1/102) := by
    rw [← hMr]; linarith
  have hK6 := K6 P (fun p => 1/(p:ℝ)) (1/102) (by norm_num) (fun p _ => by positivity)
      (fun p hp => by
        have := (hPmem p hp).2.1
        have h102 : (102:ℝ) ≤ p := by exact_mod_cast this
        exact one_div_le_one_div_of_le (by norm_num) h102) M (by rw [← hMr]; linarith)
  have hK7 := K7 M (by omega)
  have hsqrt : Real.sqrt Mr ≤ Mr :=
    (Real.sqrt_le_sqrt (show Mr ≤ Mr^2 by nlinarith)).trans_eq (Real.sqrt_sq hMr0.le)
  have heM : (1.9 * Real.exp 1)^M / (Real.exp 1 * Mr) ≤ ∑ D ∈ DD, ∏ p ∈ D, (1/(p:ℝ)) := by
    have hfact : (M ! : ℝ) ≤ Real.exp 1 * Mr * (Mr / Real.exp 1)^M := by
      calc (M ! : ℝ) ≤ Real.exp 1 * Real.sqrt M * (M / Real.exp 1)^M := hK7
        _ = Real.exp 1 * Real.sqrt Mr * (Mr / Real.exp 1)^M := by rw [hMr]
        _ ≤ Real.exp 1 * Mr * (Mr / Real.exp 1)^M := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left hsqrt (Real.exp_pos 1).le
    have hpow : (1.9 * Mr)^M ≤ (∑ p ∈ P, (1/(p:ℝ)) - (M:ℝ) * (1/102))^M :=
      pow_le_pow_left₀ (by positivity) hSM M
    have hfpos : (0:ℝ) < (M ! : ℝ) := by exact_mod_cast Nat.factorial_pos M
    calc (1.9 * Real.exp 1)^M / (Real.exp 1 * Mr) =
          (1.9 * Mr)^M / (Real.exp 1 * Mr * (Mr / Real.exp 1)^M) := by
          rw [mul_pow, mul_pow, div_pow]; field_simp
      _ ≤ (1.9 * Mr)^M / (M ! : ℝ) := div_le_div_of_nonneg_left (by positivity) hfpos hfact
      _ ≤ (∑ p ∈ P, (1/(p:ℝ)) - (M:ℝ) * (1/102))^M / (M ! : ℝ) :=
          div_le_div_of_nonneg_right hpow hfpos.le
      _ ≤ _ := hK6
  have hFx : x^2 * (2.5:ℝ)^M / (334234 * Mr^2 * E) ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (t 2 n : ℝ) := by
    refine le_trans ?_ (hlow.trans hF)
    have h1 : (2.5:ℝ)^M * (2.02:ℝ)^M ≤ (1.9 * Real.exp 1)^M := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by norm_num) (by linarith) M
    have h2 : 122880 * Real.exp 1 ≤ 334234 := by linarith
    have key : (2.5:ℝ)^M * (2.02:ℝ)^M * (122880 * Real.exp 1) ≤ (1.9 * Real.exp 1)^M * 334234 := by
      have := mul_le_mul_of_nonneg_right h1 (show (0:ℝ) ≤ 122880 * Real.exp 1 by positivity)
      have h3 := mul_le_mul_of_nonneg_left h2 (show (0:ℝ) ≤ (1.9 * Real.exp 1)^M by positivity)
      linarith
    have eq : δ * x^2 / (64 * E) * ((1.9 * Real.exp 1)^M / (Real.exp 1 * Mr)) =
        x^2 * (1.9 * Real.exp 1)^M / (122880 * Real.exp 1 * Mr^2 * (2.02:ℝ)^M * E) := by
      rw [hδdef]; field_simp; ring
    calc x^2 * (2.5:ℝ)^M / (334234 * Mr^2 * E)
        ≤ x^2 * (1.9 * Real.exp 1)^M / (122880 * Real.exp 1 * Mr^2 * (2.02:ℝ)^M * E) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hc : 0 ≤ x^2 * Mr^2 * E := by positivity
          have := mul_le_mul_of_nonneg_left key hc
          calc x^2 * (2.5:ℝ)^M * (122880 * Real.exp 1 * Mr^2 * (2.02:ℝ)^M * E)
              = x^2 * Mr^2 * E * ((2.5:ℝ)^M * (2.02:ℝ)^M * (122880 * Real.exp 1)) := by ring
            _ ≤ x^2 * Mr^2 * E * ((1.9 * Real.exp 1)^M * 334234) := this
            _ = x^2 * (1.9 * Real.exp 1)^M * (334234 * Mr^2 * E) := by ring
      _ = δ * x^2 / (64 * E) * ((1.9 * Real.exp 1)^M / (Real.exp 1 * Mr)) := eq.symm
      _ ≤ δ * x^2 / (64 * E) * ∑ D ∈ DD, ∏ p ∈ D, (1/(p:ℝ)) :=
          mul_le_mul_of_nonneg_left heM (by positivity)
  have hbound := hX x hM1
  change ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (t 2 n : ℝ)‖ ≤ 1 * ‖x^2 / (Real.log x)^(2/3:ℝ)‖ at hbound
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul] at hbound
  have hFnn : 0 ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (t 2 n : ℝ) :=
    Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)
  have hrpow : (Real.log x)^(2/3:ℝ) = Real.exp (4/3 * Mr) := by
    rw [hlogx, hEdef, ← Real.exp_mul]; ring_nf
  rw [abs_of_nonneg hFnn, hrpow, abs_of_nonneg (by positivity)] at hbound
  have hc1 := hFx.trans hbound
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at hc1
  have hx2 : 0 < x^2 := by positivity
  have hc2 : (2.5:ℝ)^M * Real.exp (4/3 * Mr) ≤ 334234 * Mr^2 * E := by
    have e1 : x^2 * (2.5:ℝ)^M * Real.exp (4/3 * Mr) = x^2 * ((2.5:ℝ)^M * Real.exp (4/3 * Mr)) := by ring
    rw [e1] at hc1
    exact le_of_mul_le_mul_left hc1 hx2
  have hE' : E = Real.exp (4/3 * Mr) * Real.exp (2/3 * Mr) := by
    rw [← Real.exp_add, hEdef]; ring_nf
  have he23 : Real.exp (2/3 * Mr) ≤ (1.95:ℝ)^M := by
    have h1 : Real.exp (2/3) ≤ 1.95 := by
      by_contra h
      push_neg at h
      have h3 : (1.95:ℝ)^3 < Real.exp (2/3) ^ 3 := pow_lt_pow_left₀ h (by norm_num) (by norm_num)
      rw [← Real.exp_nat_mul] at h3
      have h4 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      have h5 : ((3:ℕ):ℝ) * (2/3) = 2 := by norm_num
      rw [h5, h4] at h3
      nlinarith
    have : 2/3 * Mr = (M:ℝ) * (2/3) := by rw [hMr]; ring
    rw [this, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le h1 M
  rw [hE'] at hc2
  have hpos := Real.exp_pos (4/3 * Mr)
  have hc3 : (2.5:ℝ)^M ≤ 334234 * Mr^2 * Real.exp (2/3 * Mr) := by
    have : (2.5:ℝ)^M * Real.exp (4/3 * Mr) ≤
        (334234 * Mr^2 * Real.exp (2/3 * Mr)) * Real.exp (4/3 * Mr) := by
      calc _ ≤ _ := hc2
        _ = _ := by ring
    exact le_of_mul_le_mul_right this hpos
  have hc4 : 334234 * Mr^2 * Real.exp (2/3 * Mr) ≤ 334234 * Mr^2 * (1.95:ℝ)^M :=
    mul_le_mul_of_nonneg_left he23 (by positivity)
  linarith [hM6]
where
  -- K1: root structure of m(m+1) ≡ 0 mod ab, and GOOD ⇒ t₂(ab) large
  ------------------------------------------------------------------
  K1a (a b m : ℕ) (ha : 0 < a) (hb : 0 < b) (hm1 : 1 ≤ m) (hmn : m < a*b)
      (hdvd : a*b ∣ m*(m+1)) (ham : a ∣ m) :
      ∃ d ∈ b.divisors, ∃ u, m = a*d*u ∧ 1 ≤ u ∧ u < b/d ∧ b/d ∣ a*d*u+1 := by
    have hn0 : 0 < a*b := Nat.mul_pos ha hb
    have hA0 : 0 < Nat.gcd (a*b) m := Nat.gcd_pos_of_pos_left _ hn0
    have haA : a ∣ Nat.gcd (a*b) m := Nat.dvd_gcd (Dvd.intro b rfl) ham
    have hcop0 := Nat.coprime_div_gcd_div_gcd hA0
    obtain ⟨d, hd⟩ := haA
    obtain ⟨B, hB⟩ : Nat.gcd (a*b) m ∣ a*b := Nat.gcd_dvd_left _ _
    obtain ⟨u, hu⟩ : Nat.gcd (a*b) m ∣ m := Nat.gcd_dvd_right _ _
    set A := Nat.gcd (a*b) m with hA
    have hcop : Nat.Coprime B u := by
      have h1 : a * b / A = B := by rw [hB]; exact Nat.mul_div_cancel_left B hA0
      have h2 : m / A = u := by rw [hu]; exact Nat.mul_div_cancel_left u hA0
      rwa [h1, h2] at hcop0
    have hbd : b = d * B := by
      have : a * b = a * (d * B) := by rw [hB, hd, mul_assoc]
      exact Nat.eq_of_mul_eq_mul_left ha this
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h | h
      · subst h; simp at hbd; omega
      · exact h
    have hbdB : b / d = B := by rw [hbd]; exact Nat.mul_div_cancel_left B hd0
    refine ⟨d, Nat.mem_divisors.2 ⟨⟨B, hbd⟩, hb.ne'⟩, u, ?_, ?_, ?_, ?_⟩
    · rw [hu, hd]
    · rcases Nat.eq_zero_or_pos u with h | h
      · rw [h, mul_zero] at hu; omega
      · exact h
    · rw [hbdB]
      have : A * u < A * B := by rw [← hu, ← hB]; exact hmn
      exact Nat.lt_of_mul_lt_mul_left this
    · rw [hbdB, ← hd, ← hu]
      have : A * B ∣ A * (u * (m+1)) := by rw [← hB, ← mul_assoc, ← hu]; exact hdvd
      have := Nat.dvd_of_mul_dvd_mul_left hA0 this
      exact hcop.dvd_of_dvd_mul_left this
  K1 (a b : ℕ) (δ : ℝ) (ha : a.Prime) (hb : 0 < b) (hδ : δ ≤ 1)
      (hgood : ∀ d ∈ b.divisors, ∀ u : ℕ, 1 ≤ u → u < b/d → b/d ∣ a*d*u+1 →
        δ * ((b/d : ℕ) : ℝ) ≤ u ∧ (u:ℝ) + δ * ((b/d : ℕ) : ℝ) ≤ ((b/d : ℕ) : ℝ)) :
      δ * ((a*b : ℕ) : ℝ) ≤ (t 2 (a*b) : ℝ) + 1 := by
    have ha1 := ha.two_le
    have ha0 : 0 < a := by omega
    have hn2 : 2 ≤ a*b := by nlinarith
    have hmem : a*b - 1 ∈ {m : ℕ | 0 < m ∧ a*b ∣ ∏ i ∈ range 2, (m + i)} := by
      refine ⟨by omega, ?_⟩
      simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, add_zero]
      rw [Nat.sub_add_cancel (by omega)]
      exact Dvd.intro_left _ rfl
    have hle : t 2 (a*b) ≤ a*b - 1 := Nat.sInf_le hmem
    have hm : t 2 (a*b) ∈ {m : ℕ | 0 < m ∧ a*b ∣ ∏ i ∈ range 2, (m + i)} := Nat.sInf_mem ⟨_, hmem⟩
    obtain ⟨hmpos, hmdvd⟩ := hm
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, add_zero] at hmdvd
    set m := t 2 (a*b) with hmdef
    have hδn : δ * ((a*b : ℕ) : ℝ) ≤ ((a*b : ℕ) : ℝ) := by
      have : (0:ℝ) ≤ ((a*b : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    by_cases ham : a ∣ m
    · obtain ⟨d, hd, u, hmu, hu1, huB, hBd⟩ := K1a a b m ha0 hb hmpos (by omega) hmdvd ham
      have h1 := (hgood d hd u hu1 huB hBd).1
      have hdb : d ∣ b := Nat.dvd_of_mem_divisors hd
      have hb' : ((a*b : ℕ) : ℝ) = (a:ℝ) * d * ((b/d : ℕ) : ℝ) := by
        rw [← Nat.cast_mul, ← Nat.cast_mul, mul_assoc, Nat.mul_div_cancel' hdb]
      have hm' : (m:ℝ) = (a:ℝ) * d * u := by rw [hmu]; push_cast; ring
      have had : (0:ℝ) ≤ (a:ℝ) * d := by positivity
      rw [hb', hm']
      nlinarith
    · have ham1 : a ∣ m + 1 := by
        rcases (Nat.Prime.dvd_mul ha).1 (dvd_trans (Dvd.intro b rfl) hmdvd) with h | h
        · exact absurd h ham
        · exact h
      by_cases hm' : a*b - 1 - m = 0
      · have : m = a*b - 1 := by omega
        have : ((a*b : ℕ) : ℝ) = (m:ℝ) + 1 := by
          rw [this]; rw [Nat.cast_sub (by omega)]; push_cast; ring
        linarith
      · set m' := a*b - 1 - m with hm'def
        have hm'1 : 1 ≤ m' := by omega
        have hm'n : m' < a*b := by omega
        have ham' : a ∣ m' := by
          have : m' = a*b - (m+1) := by omega
          rw [this]; exact Nat.dvd_sub (Dvd.intro b rfl) ham1
        have hdvd' : a*b ∣ m'*(m'+1) := by
          have hz : ((m'*(m'+1) : ℕ) : ℤ) = ((a*b : ℕ) : ℤ) * (((a*b : ℕ) : ℤ) - 2*m - 1) + ((m*(m+1) : ℕ) : ℤ) := by
            have : (m' : ℤ) = ((a*b : ℕ) : ℤ) - 1 - m := by
              rw [hm'def]; push_cast [Nat.cast_sub (show m ≤ a*b - 1 by omega), Nat.cast_sub (show 1 ≤ a*b by omega)]
              ring
            push_cast
            rw [this]; push_cast; ring
          have : ((a*b : ℕ) : ℤ) ∣ ((m'*(m'+1) : ℕ) : ℤ) := by
            rw [hz]
            exact dvd_add (dvd_mul_right _ _) (Int.natCast_dvd_natCast.mpr hmdvd)
          exact Int.natCast_dvd_natCast.mp this
        obtain ⟨d, hd, u, hmu, hu1, huB, hBd⟩ := K1a a b m' ha0 hb hm'1 hm'n hdvd' ham'
        have h1 := (hgood d hd u hu1 huB hBd).2
        have hdb : d ∣ b := Nat.dvd_of_mem_divisors hd
        have hb' : ((a*b : ℕ) : ℝ) = (a:ℝ) * d * ((b/d : ℕ) : ℝ) := by
          rw [← Nat.cast_mul, ← Nat.cast_mul, mul_assoc, Nat.mul_div_cancel' hdb]
        have hmm : (m:ℝ) + 1 + (a:ℝ) * d * u = ((a*b : ℕ) : ℝ) := by
          have : m + 1 + m' = a*b := by omega
          rw [hmu] at this
          rw [← this]; push_cast; ring
        have had : (0:ℝ) ≤ (a:ℝ) * d := by positivity
        have key : (a:ℝ) * d * u + δ * ((a:ℝ) * d * ((b/d : ℕ) : ℝ)) ≤ (a:ℝ) * d * ((b/d : ℕ) : ℝ) := by
          nlinarith
        rw [← hb'] at key
        linarith
  ------------------------------------------------------------------
  -- K2: counting non-good primes via residue classes
  ------------------------------------------------------------------
  K2 (A : Finset ℕ) (b : ℕ) (hb : 0 < b) (δ : ℝ) (hδ : 0 ≤ δ) (U : ℕ → ℝ)
      (hU : ∀ d ∈ b.divisors, ∀ r : ℕ, ((A.filter (fun a => a ≡ r [MOD b/d])).card : ℝ) ≤ U (b/d)) :
      ((A.filter (fun a => ∃ d ∈ b.divisors, ∃ u : ℕ, 1 ≤ u ∧ u < b/d ∧ b/d ∣ a*d*u+1 ∧
          ((u:ℝ) < δ * ((b/d:ℕ):ℝ) ∨ ((b/d:ℕ):ℝ) < u + δ * ((b/d:ℕ):ℝ)))).card : ℝ)
        ≤ ∑ d ∈ b.divisors, 2 * δ * ((b/d:ℕ):ℝ) * U (b/d) := by
    have hclass : ∀ d ∈ b.divisors, ∀ u : ℕ,
        ((A.filter (fun a => b/d ∣ a*d*u+1)).card : ℝ) ≤ U (b/d) := by
      intro d hd u
      by_cases hne : (A.filter (fun a => b/d ∣ a*d*u+1)).Nonempty
      · obtain ⟨a0, ha0⟩ := hne
        have ha0' := (Finset.mem_filter.1 ha0).2
        refine le_trans ?_ (hU d hd a0)
        exact_mod_cast Finset.card_le_card (by
          intro a ha
          rw [Finset.mem_filter] at ha ⊢
          refine ⟨ha.1, ?_⟩
          have hcop : Nat.Coprime (b/d) (d*u) := by
            have h1 : Nat.gcd (b/d) (d*u) ∣ a0*(d*u) + 1 := by
              rw [← mul_assoc]; exact dvd_trans (Nat.gcd_dvd_left _ _) ha0'
            have h2 : Nat.gcd (b/d) (d*u) ∣ a0*(d*u) := dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) _
            exact Nat.dvd_one.mp ((Nat.dvd_add_right h2).mp h1)
          have h3 : a*d*u + 1 ≡ a0*d*u + 1 [MOD b/d] := by
            exact (Nat.modEq_zero_iff_dvd.2 ha.2).trans (Nat.modEq_zero_iff_dvd.2 ha0').symm
          have h4 : (d*u) * a ≡ (d*u) * a0 [MOD b/d] := by
            have := Nat.ModEq.add_right_cancel' 1 h3
            simpa [mul_comm, mul_assoc, mul_left_comm] using this
          exact Nat.ModEq.cancel_left_of_coprime hcop h4)
      · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.card_empty, Nat.cast_zero]
        have := hU d hd 0
        exact le_trans (Nat.cast_nonneg _) this
    have hbadu : ∀ B : ℕ, 0 < B → (((Finset.Ico 1 B).filter (fun u : ℕ => (u:ℝ) < δ * (B:ℝ) ∨
          (B:ℝ) < u + δ * (B:ℝ))).card : ℝ) ≤ 2 * δ * B := by
      intro B hB
      have hlow : (((Finset.Ico 1 B).filter (fun u : ℕ => (u:ℝ) < δ * (B:ℝ))).card : ℝ) ≤ δ * B := by
        have hsub : (Finset.Ico 1 B).filter (fun u : ℕ => (u:ℝ) < δ * (B:ℝ)) ⊆ Finset.Ico 1 ⌈δ * (B:ℝ)⌉₊ := by
          intro u hu
          rw [Finset.mem_filter, Finset.mem_Ico] at hu
          rw [Finset.mem_Ico]
          exact ⟨hu.1.1, Nat.lt_ceil.2 hu.2⟩
        have hc := Finset.card_le_card hsub
        rw [Nat.card_Ico] at hc
        have hδB : 0 ≤ δ * (B:ℝ) := by positivity
        rcases Nat.eq_zero_or_pos ⌈δ * (B:ℝ)⌉₊ with h0 | h0
        · have hc0 : ((Finset.Ico 1 B).filter (fun u : ℕ => (u:ℝ) < δ * (B:ℝ))).card = 0 := by
            rw [h0] at hc; omega
          rw [hc0]; simpa using hδB
        · have h1 : (⌈δ * (B:ℝ)⌉₊ : ℝ) < δ * B + 1 := Nat.ceil_lt_add_one hδB
          have h2 : ((⌈δ * (B:ℝ)⌉₊ - 1 : ℕ) : ℝ) = (⌈δ * (B:ℝ)⌉₊ : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega)]; simp
          have h3 : (((Finset.Ico 1 B).filter (fun u : ℕ => (u:ℝ) < δ * (B:ℝ))).card : ℝ) ≤
              ((⌈δ * (B:ℝ)⌉₊ - 1 : ℕ) : ℝ) := by exact_mod_cast hc
          linarith
      have hhigh : ((Finset.Ico 1 B).filter (fun u : ℕ => (B:ℝ) < u + δ * (B:ℝ))).card ≤
          ((Finset.Ico 1 B).filter (fun u : ℕ => (u:ℝ) < δ * (B:ℝ))).card := by
        apply Finset.card_le_card_of_injOn (fun u => B - u)
        · intro u hu
          simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ico] at hu ⊢
          refine ⟨⟨by omega, by omega⟩, ?_⟩
          rw [Nat.cast_sub (by omega)]
          linarith [hu.2]
        · intro u1 hu1 u2 hu2 h
          simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ico] at hu1 hu2
          simp only at h
          omega
      rw [Finset.filter_or]
      have := Finset.card_union_le ((Finset.Ico 1 B).filter (fun u : ℕ => (u:ℝ) < δ * (B:ℝ)))
        ((Finset.Ico 1 B).filter (fun u : ℕ => (B:ℝ) < u + δ * (B:ℝ)))
      have h5 : ((((Finset.Ico 1 B).filter (fun u : ℕ => (u:ℝ) < δ * (B:ℝ))) ∪
        ((Finset.Ico 1 B).filter (fun u : ℕ => (B:ℝ) < u + δ * (B:ℝ)))).card : ℝ) ≤
        (((Finset.Ico 1 B).filter (fun u : ℕ => (u:ℝ) < δ * (B:ℝ))).card : ℝ) +
        (((Finset.Ico 1 B).filter (fun u : ℕ => (B:ℝ) < u + δ * (B:ℝ))).card : ℝ) := by
        exact_mod_cast this
      have h6 : (((Finset.Ico 1 B).filter (fun u : ℕ => (B:ℝ) < u + δ * (B:ℝ))).card : ℝ) ≤
          (((Finset.Ico 1 B).filter (fun u : ℕ => (u:ℝ) < δ * (B:ℝ))).card : ℝ) := by exact_mod_cast hhigh
      linarith
    have hsub : A.filter (fun a => ∃ d ∈ b.divisors, ∃ u : ℕ, 1 ≤ u ∧ u < b/d ∧ b/d ∣ a*d*u+1 ∧
          ((u:ℝ) < δ * ((b/d:ℕ):ℝ) ∨ ((b/d:ℕ):ℝ) < u + δ * ((b/d:ℕ):ℝ))) ⊆
        b.divisors.biUnion (fun d => ((Finset.Ico 1 (b/d)).filter (fun u : ℕ => (u:ℝ) < δ * ((b/d:ℕ):ℝ) ∨
          ((b/d:ℕ):ℝ) < u + δ * ((b/d:ℕ):ℝ))).biUnion (fun u => A.filter (fun a => b/d ∣ a*d*u+1))) := by
      intro a ha
      rw [Finset.mem_filter] at ha
      obtain ⟨haA, d, hd, u, hu1, huB, hdvd, hbad⟩ := ha
      rw [Finset.mem_biUnion]
      refine ⟨d, hd, ?_⟩
      rw [Finset.mem_biUnion]
      refine ⟨u, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_Ico]; exact ⟨⟨hu1, huB⟩, hbad⟩
      · rw [Finset.mem_filter]; exact ⟨haA, hdvd⟩
    calc ((A.filter _).card : ℝ)
        ≤ ((b.divisors.biUnion (fun d => ((Finset.Ico 1 (b/d)).filter (fun u : ℕ => (u:ℝ) < δ * ((b/d:ℕ):ℝ) ∨
          ((b/d:ℕ):ℝ) < u + δ * ((b/d:ℕ):ℝ))).biUnion (fun u => A.filter (fun a => b/d ∣ a*d*u+1)))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ d ∈ b.divisors, ((((Finset.Ico 1 (b/d)).filter (fun u : ℕ => (u:ℝ) < δ * ((b/d:ℕ):ℝ) ∨
          ((b/d:ℕ):ℝ) < u + δ * ((b/d:ℕ):ℝ))).biUnion (fun u => A.filter (fun a => b/d ∣ a*d*u+1))).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ d ∈ b.divisors, ∑ u ∈ (Finset.Ico 1 (b/d)).filter (fun u : ℕ => (u:ℝ) < δ * ((b/d:ℕ):ℝ) ∨
          ((b/d:ℕ):ℝ) < u + δ * ((b/d:ℕ):ℝ)), ((A.filter (fun a => b/d ∣ a*d*u+1)).card : ℝ) := by
          apply Finset.sum_le_sum; intro d hd
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ d ∈ b.divisors, ∑ u ∈ (Finset.Ico 1 (b/d)).filter (fun u : ℕ => (u:ℝ) < δ * ((b/d:ℕ):ℝ) ∨
          ((b/d:ℕ):ℝ) < u + δ * ((b/d:ℕ):ℝ)), U (b/d) := by
          apply Finset.sum_le_sum; intro d hd
          apply Finset.sum_le_sum; intro u _
          exact hclass d hd u
      _ ≤ ∑ d ∈ b.divisors, 2 * δ * ((b/d:ℕ):ℝ) * U (b/d) := by
          apply Finset.sum_le_sum; intro d hd
          rw [Finset.sum_const, nsmul_eq_mul]
          have hU0 : 0 ≤ U (b/d) := le_trans (Nat.cast_nonneg _) (hU d hd 0)
          have hB : 0 < b/d := Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)
          exact mul_le_mul_of_nonneg_right (hbadu (b/d) hB) hU0
  ------------------------------------------------------------------
  -- K3a–K3g: Brun's pure sieve ingredients
  ------------------------------------------------------------------
  K3a (E : Finset ℕ) (s : ℕ) :
      (if E = ∅ then (1:ℤ) else 0) ≤ ∑ D ∈ E.powerset.filter (fun D => D.card ≤ 2*s), (-1:ℤ)^D.card := by
    rw [Finset.sum_filter]
    have h := Finset.sum_powerset_apply_card (fun j => if j ≤ 2*s then (-1:ℤ)^j else 0) (x := E)
    simp only at h
    rw [h]
    simp only [nsmul_eq_mul, mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    rcases Nat.lt_or_ge (2*s) E.card with hlt | hge
    · have hfil : (Finset.range (E.card + 1)).filter (fun j => j ≤ 2*s) = Finset.range (2*s+1) := by
        ext j; simp; omega
      rw [hfil]
      have hE : E ≠ ∅ := by intro h; rw [h] at hlt; simp at hlt
      rw [if_neg hE]
      obtain ⟨n, hn⟩ : ∃ n, E.card = n + 1 := ⟨E.card - 1, by omega⟩
      rw [hn]
      have := Int.alternating_sum_range_choose_eq_choose (n := n) (m := 2*s)
      have h2 : ∑ x ∈ Finset.range (2*s+1), ((n+1).choose x : ℤ) * (-1)^x =
          ∑ x ∈ Finset.range (2*s+1), (-1:ℤ)^x * ((n+1).choose x : ℤ) := by
        apply Finset.sum_congr rfl; intro x _; ring
      rw [h2, this]
      rw [pow_mul]; simp
    · have hfil : (Finset.range (E.card + 1)).filter (fun j => j ≤ 2*s) = Finset.range (E.card+1) := by
        ext j; simp; omega
      rw [hfil]
      have := Int.alternating_sum_range_choose (n := E.card)
      have h2 : ∑ x ∈ Finset.range (E.card+1), ((E.card).choose x : ℤ) * (-1)^x =
          ∑ x ∈ Finset.range (E.card+1), (-1:ℤ)^x * ((E.card).choose x : ℤ) := by
        apply Finset.sum_congr rfl; intro x _; ring
      rw [h2, this]
      by_cases hE : E = ∅
      · simp [hE]
      · rw [if_neg hE, if_neg (by rwa [Finset.card_eq_zero])]
  hcnt (N M c : ℕ) (hM : 0 < M) :
      ((((Finset.Icc 1 N).filter (fun n => n ≡ c [MOD M])).card : ℝ) ≤ (N:ℝ)/M + 1) ∧
      ((N:ℝ)/M - 1 ≤ (((Finset.Icc 1 N).filter (fun n => n ≡ c [MOD M])).card : ℝ)) := by
    have h := Nat.Ioc_filter_modEq_card 0 N hM c
    have hI : Finset.Icc 1 N = Finset.Ioc 0 N := by ext; simp; omega
    rw [← hI] at h
    set C := ((Finset.Icc 1 N).filter (fun n => n ≡ c [MOD M])).card
    have hM' : (0:ℚ) < M := by exact_mod_cast hM
    have e1 := Int.floor_le (((N:ℚ) - c)/M)
    have e2 := Int.lt_floor_add_one (((N:ℚ) - c)/M)
    have e3 := Int.floor_le ((((0:ℕ):ℚ) - c)/M)
    have e4 := Int.lt_floor_add_one ((((0:ℕ):ℚ) - c)/M)
    have hdiff : ((N:ℚ) - c)/M - (((0:ℕ):ℚ) - c)/M = (N:ℚ)/M := by
      field_simp; push_cast; ring
    have hC : (C:ℚ) = ((max (⌊((N:ℚ) - c)/M⌋ - ⌊(((0:ℕ):ℚ) - c)/M⌋) 0 : ℤ) : ℚ) := by
      exact_mod_cast h
    have hup : (C:ℚ) ≤ (N:ℚ)/M + 1 := by
      rw [hC]
      push_cast
      apply max_le
      · linarith
      · have : (0:ℚ) ≤ (N:ℚ)/M := by positivity
        linarith
    have hlo : (N:ℚ)/M - 1 ≤ (C:ℚ) := by
      rw [hC]
      push_cast
      exact le_trans (by linarith) (le_max_left _ _)
    constructor
    · have : ((C:ℚ):ℝ) ≤ (((N:ℚ)/M + 1 : ℚ) : ℝ) := by exact_mod_cast hup
      push_cast at this; exact this
    · have : ((((N:ℚ)/M - 1 : ℚ)) : ℝ) ≤ ((C:ℚ):ℝ) := by exact_mod_cast hlo
      push_cast at this; exact this
  K3b (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (q : ℕ) (hq : 0 < q)
      (hQq : ∀ p ∈ Q, Nat.Coprime p q) (N r s : ℕ) :
      ((((Finset.Icc 1 N).filter (fun n => n ≡ r [MOD q] ∧ ∀ p ∈ Q, ¬ p ∣ n)).card : ℝ) ≤
        (N:ℝ)/q * (∑ D ∈ Q.powerset.filter (fun D => D.card ≤ 2*s), (-1:ℝ)^D.card / ∏ p ∈ D, (p:ℝ))
        + ((Q.powerset.filter (fun D => D.card ≤ 2*s)).card : ℝ)) := by
    set S := Q.powerset.filter (fun D => D.card ≤ 2*s) with hS
    set A := (Finset.Icc 1 N).filter (fun n => n ≡ r [MOD q]) with hA
    have hpt : ∀ n : ℕ, (if ∀ p ∈ Q, ¬ p ∣ n then (1:ℝ) else 0) ≤
        ∑ D ∈ S, (-1:ℝ)^D.card * (if ∏ p ∈ D, p ∣ n then 1 else 0) := by
      intro n
      have hset : S.filter (fun D => ∏ p ∈ D, p ∣ n) =
          (Q.filter (fun p => p ∣ n)).powerset.filter (fun D => D.card ≤ 2*s) := by
        ext D
        simp only [hS, Finset.mem_filter, Finset.mem_powerset]
        constructor
        · rintro ⟨⟨hDQ, hc⟩, hdvd⟩
          refine ⟨fun p hp => Finset.mem_filter.2 ⟨hDQ hp, ?_⟩, hc⟩
          exact dvd_trans (Finset.dvd_prod_of_mem _ hp) hdvd
        · rintro ⟨hD, hc⟩
          refine ⟨⟨fun p hp => (Finset.mem_filter.1 (hD hp)).1, hc⟩, ?_⟩
          apply Finset.prod_primes_dvd
          · intro p hp; exact (hQ p (Finset.mem_filter.1 (hD hp)).1).prime
          · intro p hp; exact (Finset.mem_filter.1 (hD hp)).2
      have hrhs : ∑ D ∈ S, (-1:ℝ)^D.card * (if ∏ p ∈ D, p ∣ n then 1 else 0) =
          ((∑ D ∈ (Q.filter (fun p => p ∣ n)).powerset.filter (fun D => D.card ≤ 2*s), (-1:ℤ)^D.card : ℤ) : ℝ) := by
        simp only [mul_ite, mul_one, mul_zero]
        rw [← Finset.sum_filter, hset]
        push_cast; rfl
      rw [hrhs]
      have hb := K3a (Q.filter (fun p => p ∣ n)) s
      have hlhs : (if ∀ p ∈ Q, ¬ p ∣ n then (1:ℝ) else 0) =
          (((if Q.filter (fun p => p ∣ n) = ∅ then (1:ℤ) else 0) : ℤ) : ℝ) := by
        by_cases h : ∀ p ∈ Q, ¬ p ∣ n
        · have h' : Q.filter (fun p => p ∣ n) = ∅ := Finset.filter_eq_empty_iff.2 h
          rw [if_pos h, if_pos h']; simp
        · have h' : Q.filter (fun p => p ∣ n) ≠ ∅ := fun h' => h (Finset.filter_eq_empty_iff.1 h')
          rw [if_neg h, if_neg h']; simp
      rw [hlhs]
      exact_mod_cast hb
    have hD : ∀ D ∈ S, (-1:ℝ)^D.card * ((A.filter (fun n => ∏ p ∈ D, p ∣ n)).card : ℝ) ≤
        (-1:ℝ)^D.card * ((N:ℝ)/q / ∏ p ∈ D, (p:ℝ)) + 1 := by
      intro D hDS
      have hDQ : D ⊆ Q := Finset.mem_powerset.1 (Finset.mem_filter.1 hDS).1
      set P := ∏ p ∈ D, p with hP
      have hP0 : 0 < P := Finset.prod_pos (fun p hp => (hQ p (hDQ hp)).pos)
      have hcop : Nat.Coprime q P := (Nat.Coprime.prod_left (fun p hp => hQq p (hDQ hp))).symm
      obtain ⟨c, hc1, hc2⟩ := Nat.chineseRemainder hcop r 0
      have hfil : A.filter (fun n => P ∣ n) = (Finset.Icc 1 N).filter (fun n => n ≡ c [MOD q*P]) := by
        ext n
        simp only [hA, Finset.mem_filter]
        rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop]
        constructor
        · rintro ⟨⟨hn, h1⟩, h2⟩
          exact ⟨hn, h1.trans hc1.symm, ((Nat.modEq_zero_iff_dvd.2 h2)).trans hc2.symm⟩
        · rintro ⟨hn, h1, h2⟩
          exact ⟨⟨hn, h1.trans hc1⟩, Nat.modEq_zero_iff_dvd.1 (h2.trans hc2)⟩
      rw [hfil]
      have hqP : 0 < q * P := Nat.mul_pos hq hP0
      obtain ⟨hup, hlo⟩ := hcnt N (q*P) c hqP
      have hPr : ((q*P : ℕ) : ℝ) = (q:ℝ) * ∏ p ∈ D, (p:ℝ) := by rw [hP]; push_cast; ring
      have hdiv : (N:ℝ)/q / ∏ p ∈ D, (p:ℝ) = (N:ℝ) / ((q*P : ℕ) : ℝ) := by rw [hPr, div_div]
      rw [hdiv]
      rcases neg_one_pow_eq_or ℝ D.card with h | h
      · rw [h]; linarith
      · rw [h]; linarith
    calc (((Finset.Icc 1 N).filter (fun n => n ≡ r [MOD q] ∧ ∀ p ∈ Q, ¬ p ∣ n)).card : ℝ)
        = ∑ n ∈ A, (if ∀ p ∈ Q, ¬ p ∣ n then (1:ℝ) else 0) := by
          rw [Finset.sum_boole, hA, Finset.filter_filter]
      _ ≤ ∑ n ∈ A, ∑ D ∈ S, (-1:ℝ)^D.card * (if ∏ p ∈ D, p ∣ n then 1 else 0) :=
          Finset.sum_le_sum (fun n _ => hpt n)
      _ = ∑ D ∈ S, (-1:ℝ)^D.card * ((A.filter (fun n => ∏ p ∈ D, p ∣ n)).card : ℝ) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro D _
          rw [← Finset.mul_sum, Finset.sum_boole]
      _ ≤ ∑ D ∈ S, ((-1:ℝ)^D.card * ((N:ℝ)/q / ∏ p ∈ D, (p:ℝ)) + 1) := Finset.sum_le_sum hD
      _ = (N:ℝ)/q * (∑ D ∈ S, (-1:ℝ)^D.card / ∏ p ∈ D, (p:ℝ)) + (S.card : ℝ) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
          congr 1
          apply Finset.sum_congr rfl; intro D _; ring
  K3c (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 0 < p) (s : ℕ) (t : ℝ) (ht : 1 ≤ t) :
      (∑ D ∈ Q.powerset.filter (fun D => D.card ≤ 2*s), (-1:ℝ)^D.card / ∏ p ∈ D, (p:ℝ)) ≤
        (∏ p ∈ Q, (1 - 1/(p:ℝ))) + (∏ p ∈ Q, (1 + t/(p:ℝ))) / t^(2*s+1) := by
    have hpos : ∀ D ∈ Q.powerset, 0 < ∏ p ∈ D, (p:ℝ) := by
      intro D hD
      exact Finset.prod_pos (fun p hp => by exact_mod_cast hQ p (Finset.mem_powerset.1 hD hp))
    have hfull : ∑ D ∈ Q.powerset, (-1:ℝ)^D.card / ∏ p ∈ D, (p:ℝ) = ∏ p ∈ Q, (1 - 1/(p:ℝ)) := by
      have h2 : (∏ p ∈ Q, (1 - 1/(p:ℝ))) = ∏ p ∈ Q, (1 + (-1)/(p:ℝ)) := by
        apply Finset.prod_congr rfl; intro p _; ring
      rw [h2, Finset.prod_one_add]
      apply Finset.sum_congr rfl; intro D _
      rw [← Finset.prod_const, ← Finset.prod_div_distrib]
    have hfull2 : ∑ D ∈ Q.powerset, t^D.card / ∏ p ∈ D, (p:ℝ) = ∏ p ∈ Q, (1 + t/(p:ℝ)) := by
      rw [Finset.prod_one_add]
      apply Finset.sum_congr rfl; intro D _
      rw [← Finset.prod_const, ← Finset.prod_div_distrib]
    rw [← hfull, ← Finset.sum_filter_add_sum_filter_not Q.powerset (fun D => D.card ≤ 2*s)]
    have htail : -(∑ D ∈ Q.powerset.filter (fun D => ¬ D.card ≤ 2*s), (-1:ℝ)^D.card / ∏ p ∈ D, (p:ℝ)) ≤
        (∏ p ∈ Q, (1 + t/(p:ℝ))) / t^(2*s+1) := by
      rw [← hfull2, Finset.sum_div, ← Finset.sum_neg_distrib]
      calc ∑ D ∈ Q.powerset.filter (fun D => ¬ D.card ≤ 2*s), -((-1:ℝ)^D.card / ∏ p ∈ D, (p:ℝ))
          ≤ ∑ D ∈ Q.powerset.filter (fun D => ¬ D.card ≤ 2*s), t^D.card / (∏ p ∈ D, (p:ℝ)) / t^(2*s+1) := by
            apply Finset.sum_le_sum; intro D hD
            have hD' := Finset.mem_filter.1 hD
            have hP := hpos D hD'.1
            have ht1 : t^(2*s+1) ≤ t^D.card := pow_le_pow_right₀ ht (by omega)
            have ht0 : 0 < t^(2*s+1) := by positivity
            have e1 : -((-1:ℝ)^D.card / ∏ p ∈ D, (p:ℝ)) ≤ 1 / ∏ p ∈ D, (p:ℝ) := by
              have : 0 < 1 / ∏ p ∈ D, (p:ℝ) := by positivity
              rcases neg_one_pow_eq_or ℝ D.card with h | h <;> rw [h]
              · linarith
              · rw [neg_div, neg_neg]
            have e2 : 1 / ∏ p ∈ D, (p:ℝ) ≤ t^D.card / (∏ p ∈ D, (p:ℝ)) / t^(2*s+1) := by
              rw [div_div, div_le_div_iff₀ hP (by positivity)]; nlinarith
            linarith
        _ ≤ ∑ D ∈ Q.powerset, t^D.card / (∏ p ∈ D, (p:ℝ)) / t^(2*s+1) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro D hD _
            have := hpos D hD
            positivity
    linarith
  K3d (Q : Finset ℕ) (s : ℕ) :
      (Q.powerset.filter (fun D => D.card ≤ 2*s)).card ≤ (Q.card + 1)^(2*s) := by
    have hsub : Q.powerset.filter (fun D => D.card ≤ 2*s) ⊆
        (Finset.range (2*s+1)).biUnion (fun j => Q.powersetCard j) := by
      intro D hD
      rw [Finset.mem_filter, Finset.mem_powerset] at hD
      rw [Finset.mem_biUnion]
      exact ⟨D.card, Finset.mem_range.2 (by omega), Finset.mem_powersetCard.2 ⟨hD.1, rfl⟩⟩
    calc (Q.powerset.filter (fun D => D.card ≤ 2*s)).card
        ≤ ((Finset.range (2*s+1)).biUnion (fun j => Q.powersetCard j)).card := Finset.card_le_card hsub
      _ ≤ ∑ j ∈ Finset.range (2*s+1), (Q.powersetCard j).card := Finset.card_biUnion_le
      _ = ∑ j ∈ Finset.range (2*s+1), Q.card.choose j := by
          apply Finset.sum_congr rfl; intro j _; exact Finset.card_powersetCard _ _
      _ ≤ ∑ j ∈ Finset.range (2*s+1), Q.card^j * 1^(2*s-j) * (2*s).choose j := by
          apply Finset.sum_le_sum; intro j hj
          rw [one_pow, mul_one]
          have h1 := Nat.choose_le_pow Q.card j
          have h2 : 1 ≤ (2*s).choose j := Nat.choose_pos (by rw [Finset.mem_range] at hj; omega)
          nlinarith
      _ = (Q.card + 1)^(2*s) := (add_pow _ _ _).symm
  K3e (N : ℕ) (hN : 2 ≤ N) :
      ∑ p ∈ (Finset.range (N+1)).filter Nat.Prime, (1/(p:ℝ)) ≤ 4 * Real.log (Real.log N) + 6 := by
    set J := Nat.log 2 N with hJ
    set P := (Finset.range (N+1)).filter Nat.Prime with hP
    have hJ1 : 1 ≤ J := by
      rw [hJ]; exact Nat.le_log_of_pow_le (by norm_num) (by simpa using hN)
    have hmaps : ∀ p ∈ P, Nat.log 2 p ∈ Finset.Icc 1 J := by
      intro p hp
      rw [hP, Finset.mem_filter, Finset.mem_range] at hp
      rw [Finset.mem_Icc]
      exact ⟨Nat.le_log_of_pow_le (by norm_num) (by simpa using hp.2.two_le),
        Nat.log_mono_right (by omega)⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    have hblock : ∀ j ∈ Finset.Icc 1 J, ∑ p ∈ P.filter (fun p => Nat.log 2 p = j), (1/(p:ℝ)) ≤ 4 / j := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      set Bj := P.filter (fun p => Nat.log 2 p = j) with hBj
      have hmem : ∀ p ∈ Bj, p.Prime ∧ 2^j ≤ p ∧ p < 2^(j+1) := by
        intro p hp
        rw [hBj, hP, Finset.mem_filter, Finset.mem_filter] at hp
        have hp0 : p ≠ 0 := hp.1.2.ne_zero
        refine ⟨hp.1.2, ?_, ?_⟩
        · rw [← hp.2]; exact Nat.pow_log_le_self 2 hp0
        · rw [← hp.2]; exact Nat.lt_pow_succ_log_self (by norm_num) p
      have hcard : j * Bj.card ≤ 2^(j+2) := by
        have h1 : (2^j)^Bj.card ≤ ∏ p ∈ Bj, p := by
          rw [← Finset.prod_const]
          exact Finset.prod_le_prod' (fun p hp => (hmem p hp).2.1)
        have h2 : ∏ p ∈ Bj, p ≤ primorial (2^(j+1)) := by
          unfold primorial
          apply Finset.prod_le_prod_of_subset_of_one_le'
          · intro p hp
            rw [Finset.mem_filter, Finset.mem_range]
            exact ⟨by have := (hmem p hp).2.2; omega, (hmem p hp).1⟩
          · intro p hp _
            exact (Finset.mem_filter.1 hp).2.one_lt.le
        have h3 := primorial_le_4_pow (2^(j+1))
        have h4 : (2:ℕ)^(j * Bj.card) ≤ 2^(2^(j+2)) := by
          calc (2:ℕ)^(j * Bj.card) = (2^j)^Bj.card := by rw [pow_mul]
            _ ≤ 4^(2^(j+1)) := h1.trans (h2.trans h3)
            _ = 2^(2^(j+2)) := by
                rw [show (4:ℕ) = 2^2 by norm_num, ← pow_mul]; congr 1; ring
        exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h4
      have hj0 : (0:ℝ) < j := by exact_mod_cast (show 0 < j by omega)
      calc ∑ p ∈ Bj, (1/(p:ℝ)) ≤ ∑ p ∈ Bj, (1/(2:ℝ)^j) := by
            apply Finset.sum_le_sum; intro p hp
            apply one_div_le_one_div_of_le (by positivity)
            exact_mod_cast (hmem p hp).2.1
        _ = Bj.card / (2:ℝ)^j := by rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ 4 / j := by
            rw [div_le_div_iff₀ (by positivity) hj0]
            have : ((j * Bj.card : ℕ) : ℝ) ≤ ((2^(j+2) : ℕ) : ℝ) := by exact_mod_cast hcard
            push_cast at this
            rw [pow_succ, pow_succ] at this
            nlinarith
    calc ∑ j ∈ Finset.Icc 1 J, ∑ p ∈ P.filter (fun p => Nat.log 2 p = j), (1/(p:ℝ))
        ≤ ∑ j ∈ Finset.Icc 1 J, 4 / (j:ℝ) := Finset.sum_le_sum hblock
      _ = 4 * (harmonic J : ℝ) := by
          rw [harmonic_eq_sum_Icc]; push_cast; rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro j _; ring
      _ ≤ 4 * (1 + Real.log J) := by
          have := harmonic_le_one_add_log J; linarith
      _ ≤ 4 * Real.log (Real.log N) + 6 := by
          have hJpos : (0:ℝ) < J := by exact_mod_cast (show 0 < J by omega)
          have hNpos : (1:ℝ) < N := by exact_mod_cast (show 1 < N by omega)
          have hlogN : 0 < Real.log N := Real.log_pos hNpos
          have h2J : (2:ℝ)^J ≤ N := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
          have hJlog : (J:ℝ) * Real.log 2 ≤ Real.log N := by
            rw [← Real.log_pow]; exact Real.log_le_log (by positivity) h2J
          have hlog2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
          have hJle : (J:ℝ) ≤ Real.log N / Real.log 2 := by
            rw [le_div_iff₀ (by linarith)]; exact hJlog
          have h5 : Real.log J ≤ Real.log (Real.log N / Real.log 2) := Real.log_le_log hJpos hJle
          rw [Real.log_div hlogN.ne' (by linarith)] at h5
          have h6 : -Real.log (Real.log 2) ≤ 1/2 := by
            have hl2 : 0 < Real.log 2 := by linarith
            have e1 := Real.one_sub_inv_le_log_of_pos hl2
            have e2 : (Real.log 2)⁻¹ ≤ (0.6931471803:ℝ)⁻¹ := inv_anti₀ (by norm_num) hlog2.le
            have e3 : (0.6931471803:ℝ)⁻¹ < 1.5 := by norm_num
            linarith
          linarith
  K3f (N : ℕ) : ∑ n ∈ Finset.Icc 1 N, (1/(n:ℝ)) ≤
      ∏ p ∈ (Finset.range (N+1)).filter Nat.Prime, (1 - 1/(p:ℝ))⁻¹ := by
    set P := (Finset.range (N+1)).filter Nat.Prime with hP
    have hgeom : ∀ p ∈ P, ∑ j ∈ Finset.range (N+1), (1/(p:ℝ))^j ≤ (1 - 1/(p:ℝ))⁻¹ := by
      intro p hp
      have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.1 hp).2.two_le
      have hx0 : 0 ≤ 1/(p:ℝ) := by positivity
      have hx1 : 1/(p:ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
      rw [geom_sum_eq hx1.ne, ← neg_div_neg_eq, neg_sub, neg_sub, ← one_div]
      apply div_le_div_of_nonneg_right _ (by linarith)
      have : 0 ≤ (1/(p:ℝ))^(N+1) := by positivity
      linarith
    have hprod : ∏ p ∈ P, ∑ j ∈ Finset.range (N+1), (1/(p:ℝ))^j ≤ ∏ p ∈ P, (1 - 1/(p:ℝ))⁻¹ :=
      Finset.prod_le_prod (fun p hp => Finset.sum_nonneg (fun j _ => by positivity)) hgeom
    refine le_trans ?_ hprod
    rw [Finset.prod_sum]
    set phi : ℕ → ((a : ℕ) → a ∈ P → ℕ) := fun n p _ => n.factorization p with hphi
    have hmaps : ∀ n ∈ Finset.Icc 1 N, phi n ∈ P.pi (fun _ => Finset.range (N+1)) := by
      intro n hn
      rw [Finset.mem_pi]; intro p hp
      rw [Finset.mem_range]
      rw [Finset.mem_Icc] at hn
      have := Nat.factorization_lt p (show n ≠ 0 by omega)
      simp only [phi]; omega
    have hinj : Set.InjOn phi (Finset.Icc 1 N : Set ℕ) := by
      intro n hn m hm h
      simp only [Finset.coe_Icc, Set.mem_Icc] at hn hm
      apply Nat.eq_of_factorization_eq (by omega) (by omega)
      intro p
      by_cases hpP : p ∈ P
      · exact congrFun (congrFun h p) hpP
      · rw [hP, Finset.mem_filter, Finset.mem_range, not_and_or] at hpP
        rcases hpP with h1 | h1
        · rw [Nat.factorization_eq_zero_of_not_dvd, Nat.factorization_eq_zero_of_not_dvd]
          · intro hd; have := Nat.le_of_dvd (by omega) hd; omega
          · intro hd; have := Nat.le_of_dvd (by omega) hd; omega
        · rw [Nat.factorization_eq_zero_of_non_prime _ h1, Nat.factorization_eq_zero_of_non_prime _ h1]
    have hval : ∀ n ∈ Finset.Icc 1 N, ∏ x ∈ P.attach, (1/(x.1:ℝ))^(phi n x.1 x.2) = 1/(n:ℝ) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      simp only [phi]
      rw [Finset.prod_attach P (fun p => (1/(p:ℝ))^(n.factorization p))]
      have hsupp : n.factorization.support ⊆ P := by
        intro p hp
        rw [Nat.support_factorization] at hp
        rw [hP, Finset.mem_filter, Finset.mem_range]
        exact ⟨by have := Nat.le_of_mem_primeFactors hp; omega, Nat.prime_of_mem_primeFactors hp⟩
      have hn' : ((∏ p ∈ P, p^(n.factorization p) : ℕ) : ℝ) = n := by
        congr 1
        conv_rhs => rw [← Nat.factorization_prod_pow_eq_self (show n ≠ 0 by omega)]
        rw [Finsupp.prod_of_support_subset _ hsupp]
        intro p _; simp
      rw [← hn']; push_cast
      simp only [one_div, inv_pow, Finset.prod_inv_distrib]
    calc ∑ n ∈ Finset.Icc 1 N, 1/(n:ℝ)
        = ∑ n ∈ Finset.Icc 1 N, ∏ x ∈ P.attach, (1/(x.1:ℝ))^(phi n x.1 x.2) :=
          (Finset.sum_congr rfl (fun n hn => (hval n hn).symm))
      _ = ∑ g ∈ (Finset.Icc 1 N).image phi, ∏ x ∈ P.attach, (1/(x.1:ℝ))^(g x.1 x.2) :=
          (Finset.sum_image (f := fun g => ∏ x ∈ P.attach, (1/(x.1:ℝ))^(g x.1 x.2)) hinj).symm
      _ ≤ ∑ g ∈ P.pi (fun _ => Finset.range (N+1)), ∏ x ∈ P.attach, (1/(x.1:ℝ))^(g x.1 x.2) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro g hg; rw [Finset.mem_image] at hg; obtain ⟨n, hn, rfl⟩ := hg; exact hmaps n hn
          · intro g _ _; exact Finset.prod_nonneg (fun x _ => by positivity)
  K3f' (N : ℕ) (hN : 1 ≤ N) :
      ∏ p ∈ (Finset.range (N+1)).filter Nat.Prime, (1 - 1/(p:ℝ)) ≤ 1 / Real.log (N+1) := by
    have h1 := K3f N
    have h2 : ∑ n ∈ Finset.Icc 1 N, (1/(n:ℝ)) = (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc]; push_cast; simp [one_div]
    have h3 := log_add_one_le_harmonic N
    have hpos : 0 < Real.log (N+1) := Real.log_pos (by have h0 : (1:ℝ) ≤ N := (by exact_mod_cast hN); linarith)
    have hfac : ∀ p ∈ (Finset.range (N+1)).filter Nat.Prime, 0 < 1 - 1/(p:ℝ) := by
      intro p hp
      have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.1 hp).2.two_le
      have : 1/(p:ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
      linarith
    have hprodpos : 0 < ∏ p ∈ (Finset.range (N+1)).filter Nat.Prime, (1 - 1/(p:ℝ)) :=
      Finset.prod_pos hfac
    rw [Finset.prod_inv_distrib] at h1
    push_cast at h3
    rw [le_div_iff₀ hpos]
    have h4 : Real.log (N+1) ≤ (∏ p ∈ (Finset.range (N+1)).filter Nat.Prime, (1 - 1/(p:ℝ)))⁻¹ := by
      linarith
    calc (∏ p ∈ (Finset.range (N+1)).filter Nat.Prime, (1 - 1/(p:ℝ))) * Real.log (N+1)
        ≤ (∏ p ∈ (Finset.range (N+1)).filter Nat.Prime, (1 - 1/(p:ℝ))) *
          (∏ p ∈ (Finset.range (N+1)).filter Nat.Prime, (1 - 1/(p:ℝ)))⁻¹ :=
          mul_le_mul_of_nonneg_left h4 hprodpos.le
      _ = 1 := mul_inv_cancel₀ hprodpos.ne'
  K3g (Z q : ℕ) (hq : 0 < q) (hq101 : ∀ p ∈ q.primeFactors, 101 < p) :
      ∏ p ∈ (Finset.range (Z+1)).filter (fun p => p.Prime ∧ ¬ p ∣ q), (1 - 1/(p:ℝ)) ≤
        (101/100:ℝ)^(q.primeFactors.card) * ∏ p ∈ (Finset.range (Z+1)).filter Nat.Prime, (1 - 1/(p:ℝ)) := by
    set P := (Finset.range (Z+1)).filter Nat.Prime with hP
    have hsplit := Finset.prod_filter_mul_prod_filter_not P (fun p => p ∣ q) (fun p => (1 - 1/(p:ℝ)))
    have hfac : ∀ p ∈ P, 0 < 1 - 1/(p:ℝ) := by
      intro p hp
      have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.1 hp).2.two_le
      have : 1/(p:ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
      linarith
    have hQ : P.filter (fun p => ¬ p ∣ q) = (Finset.range (Z+1)).filter (fun p => p.Prime ∧ ¬ p ∣ q) := by
      rw [hP, Finset.filter_filter]
    rw [hQ] at hsplit
    set A := ∏ p ∈ P.filter (fun p => p ∣ q), (1 - 1/(p:ℝ))
    set B := ∏ p ∈ (Finset.range (Z+1)).filter (fun p => p.Prime ∧ ¬ p ∣ q), (1 - 1/(p:ℝ))
    have hB : 0 ≤ B := Finset.prod_nonneg (fun p hp => by
      have hp' := Finset.mem_filter.1 hp
      exact (hfac p (Finset.mem_filter.2 ⟨hp'.1, hp'.2.1⟩)).le)
    have hA : (100/101:ℝ)^(q.primeFactors.card) ≤ A := by
      have hsub : P.filter (fun p => p ∣ q) ⊆ q.primeFactors := by
        intro p hp
        rw [Finset.mem_filter, hP, Finset.mem_filter] at hp
        exact Nat.mem_primeFactors.2 ⟨hp.1.2, hp.2, hq.ne'⟩
      calc (100/101:ℝ)^(q.primeFactors.card) ≤ (100/101:ℝ)^((P.filter (fun p => p ∣ q)).card) :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (Finset.card_le_card hsub)
        _ = ∏ p ∈ P.filter (fun p => p ∣ q), (100/101:ℝ) := (Finset.prod_const _).symm
        _ ≤ A := by
            apply Finset.prod_le_prod (fun _ _ => by norm_num)
            intro p hp
            have hp' := Finset.mem_filter.1 hp
            have h101 := hq101 p (Nat.mem_primeFactors.2 ⟨(Finset.mem_filter.1 hp'.1).2, hp'.2, hq.ne'⟩)
            have : (102:ℝ) ≤ p := by exact_mod_cast h101
            have : 1/(p:ℝ) ≤ 1/102 := one_div_le_one_div_of_le (by norm_num) this
            linarith
    rw [← hsplit]
    have h1 : (101/100:ℝ)^(q.primeFactors.card) * (100/101:ℝ)^(q.primeFactors.card) = 1 := by
      rw [← mul_pow]; norm_num
    have h2 : 0 ≤ (101/100:ℝ)^(q.primeFactors.card) := by positivity
    calc B = (101/100:ℝ)^(q.primeFactors.card) * (100/101:ℝ)^(q.primeFactors.card) * B := by rw [h1, one_mul]
      _ ≤ (101/100:ℝ)^(q.primeFactors.card) * A * B := by gcongr
      _ = (101/100:ℝ)^(q.primeFactors.card) * (A * B) := by ring
  ------------------------------------------------------------------
  -- K3: Brun–Titchmarsh-type upper bound (with loglog loss)
  ------------------------------------------------------------------
  K3 : ∃ Y2 : ℝ, ∀ Y : ℝ, Y2 ≤ Y → ∀ q r : ℕ, 0 < q → (q:ℝ)^3 ≤ Y →
      (∀ p ∈ q.primeFactors, 101 < p) →
      ((((Finset.range (⌊Y⌋₊+1)).filter (fun a => a.Prime ∧ a ≡ r [MOD q])).card : ℝ) ≤
        60 * (101/100:ℝ)^(q.primeFactors.card) * Real.log (Real.log Y) * Y / (q * Real.log Y)) := by
    have ev1 : ∀ᶠ lam : ℝ in atTop, 30 ≤ Real.log lam := Real.tendsto_log_atTop.eventually_ge_atTop 30
    have ev2 : ∀ᶠ lam : ℝ in atTop, 2 * lam ≤ Real.exp (lam/10) := by
      have := (isLittleO_pow_exp_pos_mul_atTop 1 (show (0:ℝ) < 1/10 by norm_num)).bound
        (show (0:ℝ) < 1/2 by norm_num)
      filter_upwards [this, eventually_ge_atTop 0] with lam h h0
      rw [Real.norm_eq_abs, Real.norm_eq_abs, pow_one, abs_of_nonneg h0,
        abs_of_nonneg (Real.exp_pos _).le] at h
      have : 1/10 * lam = lam/10 := by ring
      rw [this] at h; linarith
    have ev3 : ∀ᶠ lam : ℝ in atTop, 48 * Real.log lam ≤ lam := by
      have := Real.isLittleO_log_id_atTop.bound (show (0:ℝ) < 1/48 by norm_num)
      filter_upwards [this, eventually_ge_atTop 1] with lam h h1
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg h1),
        abs_of_nonneg (show (0:ℝ) ≤ id lam by simp; linarith)] at h
      simp only [id] at h; linarith
    obtain ⟨L0, hL0⟩ := Filter.eventually_atTop.1 (ev1.and (ev2.and (ev3.and (eventually_ge_atTop 1))))
    refine ⟨Real.exp L0, ?_⟩
    intro Y hY q r hq hq3 hq101
    have hYpos : 0 < Y := lt_of_lt_of_le (Real.exp_pos _) hY
    set lam := Real.log Y with hlam
    have hlamL0 : L0 ≤ lam := by rw [hlam, ← Real.log_exp L0]; exact Real.log_le_log (Real.exp_pos _) hY
    obtain ⟨hl30, hl2, hl48, hl1⟩ := hL0 lam hlamL0
    have hlam0 : 0 < lam := by linarith
    have hYexp : Y = Real.exp lam := (Real.exp_log hYpos).symm
    set ell := Real.log lam with hell
    have hell0 : 0 < ell := by linarith
    set z := Real.exp (lam / (48 * ell)) with hz
    have hlogz : Real.log z = lam / (48 * ell) := Real.log_exp _
    have hlogz1 : 1 ≤ lam / (48 * ell) := by rw [le_div_iff₀ (by positivity)]; linarith
    have hz2 : 2 ≤ z := by
      have : Real.exp 1 ≤ z := Real.exp_le_exp.2 hlogz1
      have := Real.exp_one_gt_d9
      linarith
    set Z := ⌊z⌋₊ with hZ
    have hZle : (Z:ℝ) ≤ z := Nat.floor_le (by linarith)
    have hZlt : z < (Z:ℝ) + 1 := Nat.lt_floor_add_one z
    have hZ2 : 2 ≤ Z := by rw [hZ]; exact Nat.le_floor (by push_cast; linarith)
    have hZ2r : (2:ℝ) ≤ Z := by exact_mod_cast hZ2
    set s := ⌈6 * ell⌉₊ + 15 with hs
    have hs1 : 6 * ell + 15 ≤ (s:ℝ) := by
      rw [hs]; push_cast; have := Nat.le_ceil (6 * ell); linarith
    have hs2 : (s:ℝ) ≤ 6 * ell + 16 := by
      rw [hs]; push_cast; have := Nat.ceil_lt_add_one (show 0 ≤ 6 * ell by linarith); linarith
    set Q := (Finset.range (Z+1)).filter (fun p => p.Prime ∧ ¬ p ∣ q) with hQ
    set N := ⌊Y⌋₊ with hN
    have hNY : (N:ℝ) ≤ Y := Nat.floor_le hYpos.le
    have hQprime : ∀ p ∈ Q, p.Prime := fun p hp => (Finset.mem_filter.1 hp).2.1
    have step1 : (((Finset.range (N+1)).filter (fun a => a.Prime ∧ a ≡ r [MOD q])).card : ℝ) ≤
        (Z + 1 : ℝ) + (((Finset.Icc 1 N).filter (fun n => n ≡ r [MOD q] ∧ ∀ p ∈ Q, ¬ p ∣ n)).card : ℝ) := by
      have hsub : (Finset.range (N+1)).filter (fun a => a.Prime ∧ a ≡ r [MOD q]) ⊆
          Finset.range (Z+1) ∪ (Finset.Icc 1 N).filter (fun n => n ≡ r [MOD q] ∧ ∀ p ∈ Q, ¬ p ∣ n) := by
        intro a ha
        simp only [Finset.mem_filter, Finset.mem_range] at ha
        rw [Finset.mem_union]
        by_cases haZ : a ≤ Z
        · left; rw [Finset.mem_range]; omega
        · right
          simp only [Finset.mem_filter, Finset.mem_Icc]
          refine ⟨⟨ha.2.1.one_lt.le, by omega⟩, ha.2.2, ?_⟩
          intro p hp hpa
          have hp' := Finset.mem_filter.1 hp
          rcases ha.2.1.eq_one_or_self_of_dvd p hpa with h | h
          · exact hp'.2.1.one_lt.ne' h
          · have := Finset.mem_range.1 hp'.1; omega
      have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      rw [Finset.card_range] at this
      exact_mod_cast this
    have hQq : ∀ p ∈ Q, Nat.Coprime p q := fun p hp =>
      (Nat.Prime.coprime_iff_not_dvd (hQprime p hp)).2 (Finset.mem_filter.1 hp).2.2
    have step2 := K3b Q hQprime q hq hQq N r s
    have step3 := K3c Q (fun p hp => (hQprime p hp).pos) s (Real.exp 1) (by
      have := Real.add_one_le_exp 1; linarith)
    have hlogZ1 : lam / (48 * ell) ≤ Real.log ((Z:ℝ)+1) := by
      rw [← hlogz]; exact Real.log_le_log (by linarith) hZlt.le
    have step4 : ∏ p ∈ Q, (1 - 1/(p:ℝ)) ≤ (101/100:ℝ)^(q.primeFactors.card) * (48 * ell / lam) := by
      have h1 := K3g Z q hq hq101
      have h2 := K3f' Z (by omega)
      push_cast at h2
      have h3 : 1 / Real.log ((Z:ℝ)+1) ≤ 48 * ell / lam := by
        rw [div_le_div_iff₀ (by linarith) hlam0]
        rw [div_le_iff₀ (by positivity)] at hlogZ1
        linarith
      have hρ : 0 ≤ (101/100:ℝ)^(q.primeFactors.card) := by positivity
      calc ∏ p ∈ Q, (1 - 1/(p:ℝ)) ≤ _ := h1
        _ ≤ (101/100:ℝ)^(q.primeFactors.card) * (48 * ell / lam) :=
            mul_le_mul_of_nonneg_left (h2.trans h3) hρ
    have hsumQ : ∑ p ∈ Q, (1/(p:ℝ)) ≤ 4 * ell + 6 := by
      have h1 : ∑ p ∈ Q, (1/(p:ℝ)) ≤ ∑ p ∈ (Finset.range (Z+1)).filter Nat.Prime, (1/(p:ℝ)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp; have := Finset.mem_filter.1 hp; exact Finset.mem_filter.2 ⟨this.1, this.2.1⟩
        · intro p _ _; positivity
      have h2 := K3e Z hZ2
      have h3 : Real.log (Real.log Z) ≤ ell := by
        have hlZ : 0 < Real.log Z := Real.log_pos (by linarith)
        have e1 : Real.log Z ≤ Real.log z := Real.log_le_log (by linarith) hZle
        have e2 : Real.log z ≤ lam := by
          rw [hlogz, div_le_iff₀ (by positivity)]
          have := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ 48 * ell by linarith) hlam0.le
          linarith
        exact Real.log_le_log hlZ (e1.trans e2)
      linarith
    have step5 : (∏ p ∈ Q, (1 + Real.exp 1/(p:ℝ))) / (Real.exp 1)^(2*s+1) ≤ 1 / lam := by
      have h1 : ∏ p ∈ Q, (1 + Real.exp 1/(p:ℝ)) ≤ Real.exp (Real.exp 1 * (4 * ell + 6)) := by
        calc ∏ p ∈ Q, (1 + Real.exp 1/(p:ℝ)) ≤ ∏ p ∈ Q, Real.exp (Real.exp 1 * (1/(p:ℝ))) := by
              apply Finset.prod_le_prod
              · intro p _; positivity
              · intro p _
                have := Real.add_one_le_exp (Real.exp 1 * (1/(p:ℝ)))
                have e : Real.exp 1 / (p:ℝ) = Real.exp 1 * (1/(p:ℝ)) := by ring
                rw [e]; linarith
          _ = Real.exp (Real.exp 1 * ∑ p ∈ Q, (1/(p:ℝ))) := by
              rw [← Real.exp_sum, Finset.mul_sum]
          _ ≤ Real.exp (Real.exp 1 * (4 * ell + 6)) := by
              apply Real.exp_le_exp.2
              exact mul_le_mul_of_nonneg_left hsumQ (Real.exp_pos 1).le
      have h2 : (Real.exp 1)^(2*s+1) = Real.exp ((2*s+1 : ℕ) : ℝ) := by
        rw [← Real.exp_nat_mul]; ring_nf
      rw [h2, div_le_iff₀ (Real.exp_pos _)]
      have he := Real.exp_one_lt_d9
      have h3 : Real.exp (Real.exp 1 * (4 * ell + 6)) ≤ Real.exp (((2*s+1 : ℕ) : ℝ) - ell) := by
        apply Real.exp_le_exp.2
        push_cast
        have : Real.exp 1 * (4 * ell + 6) ≤ 2.72 * (4 * ell + 6) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
        linarith
      have h4 : Real.exp (((2*s+1 : ℕ) : ℝ) - ell) = Real.exp ((2*s+1 : ℕ) : ℝ) / lam := by
        rw [Real.exp_sub, hell, Real.exp_log hlam0]
      calc ∏ p ∈ Q, (1 + Real.exp 1/(p:ℝ)) ≤ _ := h1
        _ ≤ _ := h3
        _ = 1 / lam * Real.exp ((2*s+1 : ℕ) : ℝ) := by rw [h4]; ring
    have step6 : ((Q.powerset.filter (fun D => D.card ≤ 2*s)).card : ℝ) ≤ Real.exp (0.55 * lam) := by
      have h1 := K3d Q s
      have hQc : Q.card ≤ Z + 1 := by
        have := Finset.card_le_card (Finset.filter_subset (fun p => p.Prime ∧ ¬ p ∣ q) (Finset.range (Z+1)))
        rwa [Finset.card_range] at this
      have h2 : ((Q.card + 1 : ℕ) : ℝ) ≤ z^2 := by
        push_cast
        have : (Q.card : ℝ) ≤ Z + 1 := by exact_mod_cast hQc
        have h6 : 0 ≤ (z - 2) * (z + 1) := mul_nonneg (by linarith) (by linarith)
        have h7 : (z - 2) * (z + 1) = z^2 - z - 2 := by ring
        linarith
      have h3 : ((Q.powerset.filter (fun D => D.card ≤ 2*s)).card : ℝ) ≤ (z^2)^(2*s) := by
        calc ((Q.powerset.filter (fun D => D.card ≤ 2*s)).card : ℝ) ≤ (((Q.card + 1)^(2*s) : ℕ) : ℝ) := by
              exact_mod_cast h1
          _ = (((Q.card + 1 : ℕ) : ℝ))^(2*s) := by push_cast; ring
          _ ≤ (z^2)^(2*s) := pow_le_pow_left₀ (Nat.cast_nonneg _) h2 _
      have h4 : (z^2)^(2*s) = Real.exp ((4 * s : ℝ) * (lam / (48 * ell))) := by
        rw [← pow_mul, hz, ← Real.exp_nat_mul]; push_cast; ring_nf
      have h5 : (4 * s : ℝ) * (lam / (48 * ell)) ≤ 0.55 * lam := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ (by positivity)]
        have h7 : 4 * (s:ℝ) ≤ 26.4 * ell := by linarith
        have := mul_le_mul_of_nonneg_left h7 hlam0.le
        linarith
      rw [h4] at h3
      exact h3.trans (Real.exp_le_exp.2 h5)
    have hZexp : (Z:ℝ) + 1 ≤ Real.exp (0.55 * lam) := by
      have h1 : (Z:ℝ) + 1 ≤ z^2 := by
        have h6 : 0 ≤ (z - 2) * (z + 1) := mul_nonneg (by linarith) (by linarith)
        have h7 : (z - 2) * (z + 1) = z^2 - z - 2 := by ring
        linarith
      have h2 : z^2 = Real.exp (2 * (lam / (48 * ell))) := by
        rw [hz, ← Real.exp_nat_mul]; push_cast; ring_nf
      have h3 : 2 * (lam / (48 * ell)) ≤ 0.55 * lam := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        have := mul_le_mul_of_nonneg_left (show (2:ℝ) ≤ 26.4 * ell by linarith) hlam0.le
        linarith
      rw [h2] at h1; exact h1.trans (Real.exp_le_exp.2 h3)
    have hρ1 : 1 ≤ (101/100:ℝ)^(q.primeFactors.card) := one_le_pow₀ (by norm_num)
    set ρw := (101/100:ℝ)^(q.primeFactors.card) with hρw
    have hqpos : (0:ℝ) < q := by exact_mod_cast hq
    have hU : (∑ D ∈ Q.powerset.filter (fun D => D.card ≤ 2*s), (-1:ℝ)^D.card / ∏ p ∈ D, (p:ℝ)) ≤
        ρw * (48 * ell / lam) + 1 / lam := by linarith
    have hU0 : 0 ≤ ρw * (48 * ell / lam) + 1 / lam := by positivity
    have hNq : (N:ℝ)/q * (∑ D ∈ Q.powerset.filter (fun D => D.card ≤ 2*s), (-1:ℝ)^D.card / ∏ p ∈ D, (p:ℝ)) ≤
        Y/q * (ρw * (48 * ell / lam) + 1 / lam) := by
      calc (N:ℝ)/q * _ ≤ (N:ℝ)/q * (ρw * (48 * ell / lam) + 1 / lam) :=
            mul_le_mul_of_nonneg_left hU (by positivity)
        _ ≤ Y/q * (ρw * (48 * ell / lam) + 1 / lam) := by
            apply mul_le_mul_of_nonneg_right _ hU0
            exact div_le_div_of_nonneg_right hNY hqpos.le
    have hqexp : (q:ℝ) ≤ Real.exp (lam / 3) := by
      have h1 : Real.log ((q:ℝ)^3) ≤ lam := Real.log_le_log (by positivity) hq3
      rw [Real.log_pow] at h1
      rw [← Real.exp_log hqpos]
      apply Real.exp_le_exp.2; push_cast at h1; linarith
    have hsmall : 2 * Real.exp (0.55 * lam) ≤ Y / (q * lam) := by
      rw [le_div_iff₀ (by positivity), hYexp]
      calc 2 * Real.exp (0.55 * lam) * (q * lam) ≤ 2 * Real.exp (0.55 * lam) * (Real.exp (lam/3) * lam) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_right hqexp hlam0.le
        _ = Real.exp (0.55 * lam) * Real.exp (lam/3) * (2 * lam) := by ring
        _ ≤ Real.exp (0.55 * lam) * Real.exp (lam/3) * Real.exp (lam/10) :=
            mul_le_mul_of_nonneg_left hl2 (by positivity)
        _ = Real.exp (0.55 * lam + lam/3 + lam/10) := by rw [Real.exp_add, Real.exp_add]
        _ ≤ Real.exp lam := Real.exp_le_exp.2 (by linarith)
    have hfinal : Y/q * (ρw * (48 * ell / lam) + 1 / lam) + Y / (q * lam) ≤
        60 * ρw * ell * Y / (q * lam) := by
      have e1 : Y/q * (ρw * (48 * ell / lam) + 1 / lam) + Y / (q * lam) =
          (48 * ρw * ell + 2) * (Y / (q * lam)) := by
        field_simp; ring
      rw [e1]
      have e2 : 60 * ρw * ell * Y / (q * lam) = (60 * ρw * ell) * (Y / (q * lam)) := by ring
      rw [e2]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have := mul_le_mul hρ1 hl30 (by norm_num) (by linarith)
      linarith
    calc (((Finset.range (N+1)).filter (fun a => a.Prime ∧ a ≡ r [MOD q])).card : ℝ)
        ≤ (Z + 1 : ℝ) + (((Finset.Icc 1 N).filter (fun n => n ≡ r [MOD q] ∧ ∀ p ∈ Q, ¬ p ∣ n)).card : ℝ) := step1
      _ ≤ Real.exp (0.55 * lam) + (Y/q * (ρw * (48 * ell / lam) + 1 / lam) + Real.exp (0.55 * lam)) := by
          linarith
      _ = Y/q * (ρw * (48 * ell / lam) + 1 / lam) + 2 * Real.exp (0.55 * lam) := by ring
      _ ≤ Y/q * (ρw * (48 * ell / lam) + 1 / lam) + Y / (q * lam) := by linarith
      _ ≤ 60 * ρw * ell * Y / (q * lam) := hfinal
  ------------------------------------------------------------------
  -- K4: Chebyshev window
  ------------------------------------------------------------------
  K4a (n : ℕ) (hn : 0 < n) :
      (4:ℕ)^n ≤ (2*n) * (2*n)^(((Finset.range (2*n+1)).filter Nat.Prime).card) := by
    have h1 := Nat.four_pow_le_two_mul_self_mul_centralBinom n hn
    have h2 : n.centralBinom ≤ (2*n)^(((Finset.range (2*n+1)).filter Nat.Prime).card) := by
      rw [← Nat.prod_pow_factorization_centralBinom n]
      rw [← Finset.prod_filter_mul_prod_filter_not (Finset.range (2*n+1)) Nat.Prime]
      have h3 : ∏ p ∈ (Finset.range (2*n+1)).filter (fun p => ¬ Nat.Prime p),
          p^(n.centralBinom.factorization p) = 1 := by
        apply Finset.prod_eq_one; intro p hp
        rw [Nat.factorization_eq_zero_of_non_prime _ (Finset.mem_filter.1 hp).2, pow_zero]
      rw [h3, mul_one, ← Finset.prod_const]
      apply Finset.prod_le_prod'; intro p _
      rw [Nat.centralBinom_eq_two_mul_choose]
      exact Nat.pow_factorization_choose_le (by omega)
    exact h1.trans (Nat.mul_le_mul_left _ h2)
  K4 : ∀ᶠ Y : ℝ in atTop,
      Y / (4 * Real.log Y) ≤ (((Finset.Ioc ⌊Y/4⌋₊ ⌊Y⌋₊).filter Nat.Prime).card : ℝ) := by
    have hC := Chebyshev.eventually_primeCounting_le (ε := 0.01) (by norm_num)
    have hC4 : ∀ᶠ Y : ℝ in atTop,
        (⌊Y/4⌋₊.primeCounting : ℝ) ≤ (Real.log 4 + 0.01) * (Y/4) / Real.log (Y/4) :=
      (tendsto_id.atTop_div_const (by norm_num : (0:ℝ) < 4)).eventually hC
    have hlog : ∀ᶠ Y : ℝ in atTop, 139 ≤ Real.log Y := Real.tendsto_log_atTop.eventually_ge_atTop 139
    have hlo : ∀ᶠ Y : ℝ in atTop, Real.log Y ≤ Y / 23 := by
      have := Real.isLittleO_log_id_atTop.bound (show (0:ℝ) < 1/23 by norm_num)
      filter_upwards [this, eventually_ge_atTop 1] with Y hY hY1
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hY1),
        abs_of_nonneg (show (0:ℝ) ≤ id Y by simp; linarith)] at hY
      simp only [id] at hY; linarith
    filter_upwards [hC4, hlog, hlo, eventually_ge_atTop 4] with Y h1 h2 h3 h4
    have hpc : ∀ M : ℕ, Nat.primeCounting M = ((Finset.range (M+1)).filter Nat.Prime).card := by
      intro M; rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting']; rfl
    have hle : ⌊Y/4⌋₊ ≤ ⌊Y⌋₊ := Nat.floor_le_floor (by linarith)
    have hcount : (((Finset.Ioc ⌊Y/4⌋₊ ⌊Y⌋₊).filter Nat.Prime).card : ℝ) =
        (Nat.primeCounting ⌊Y⌋₊ : ℝ) - (Nat.primeCounting ⌊Y/4⌋₊ : ℝ) := by
      rw [hpc, hpc]
      have hunion : (Finset.range (⌊Y⌋₊+1)).filter Nat.Prime =
          (Finset.range (⌊Y/4⌋₊+1)).filter Nat.Prime ∪ (Finset.Ioc ⌊Y/4⌋₊ ⌊Y⌋₊).filter Nat.Prime := by
        ext p; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
        constructor
        · rintro ⟨hp, hpr⟩
          by_cases h : p ≤ ⌊Y/4⌋₊
          · left; exact ⟨by omega, hpr⟩
          · right; exact ⟨⟨by omega, by omega⟩, hpr⟩
        · rintro (⟨hp, hpr⟩ | ⟨⟨hp1, hp2⟩, hpr⟩)
          · exact ⟨by omega, hpr⟩
          · exact ⟨by omega, hpr⟩
      have hdisj : Disjoint ((Finset.range (⌊Y/4⌋₊+1)).filter Nat.Prime)
          ((Finset.Ioc ⌊Y/4⌋₊ ⌊Y⌋₊).filter Nat.Prime) := by
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc] at hp1 hp2
        omega
      rw [hunion, Finset.card_union_of_disjoint hdisj]
      push_cast; ring
    rw [hcount]
    set lam := Real.log Y with hlam
    have hlam0 : 0 < lam := by linarith
    set n := ⌊Y/2⌋₊ with hn
    have hn1 : 1 ≤ n := by
      rw [hn]; apply Nat.le_floor; push_cast; linarith
    have hn2 : (Y/2 - 1 : ℝ) ≤ n := by
      have := Nat.lt_floor_add_one (Y/2); rw [← hn] at this; linarith
    have hn3 : (2*n : ℝ) ≤ Y := by
      have := Nat.floor_le (show 0 ≤ Y/2 by linarith); rw [← hn] at this; linarith
    have h2nle : 2*n ≤ ⌊Y⌋₊ := by
      apply Nat.le_floor; push_cast; exact hn3
    have hmono : ((Finset.range (2*n+1)).filter Nat.Prime).card ≤ Nat.primeCounting ⌊Y⌋₊ := by
      rw [hpc]; apply Finset.card_le_card
      intro p hp; simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢; exact ⟨by omega, hp.2⟩
    set k := ((Finset.range (2*n+1)).filter Nat.Prime).card with hk
    have hK := K4a n (by omega)
    have hKr : ((4:ℕ)^n : ℝ) ≤ ((2*n) * (2*n)^k : ℕ) := by exact_mod_cast hK
    push_cast at hKr
    have hn1r : (1:ℝ) ≤ n := by exact_mod_cast hn1
    have h2n0 : (0:ℝ) < 2*n := by linarith
    have hlogK : (n:ℝ) * Real.log 4 ≤ Real.log (2*n) + k * Real.log (2*n) := by
      have := Real.log_le_log (by positivity) hKr
      rw [Real.log_mul h2n0.ne' (by positivity), Real.log_pow, Real.log_pow] at this
      exact this
    have hlog2n : Real.log (2*n) ≤ lam := Real.log_le_log h2n0 hn3
    have hlog2n0 : 0 < Real.log (2*n) := Real.log_pos (by linarith)
    have hl2 := Real.log_two_gt_d9
    have hl2' := Real.log_two_lt_d9
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
    have hk1 : (n:ℝ) * Real.log 4 - lam ≤ k * lam := by
      have : (k:ℝ) * Real.log (2*n) ≤ k * lam := mul_le_mul_of_nonneg_left hlog2n (Nat.cast_nonneg _)
      linarith
    have hπY : (k:ℝ) ≤ (Nat.primeCounting ⌊Y⌋₊ : ℝ) := by exact_mod_cast hmono
    have hlogY4 : Real.log (Y/4) = lam - Real.log 4 := Real.log_div (by linarith) (by norm_num)
    have hlogY4' : 0.99 * lam ≤ Real.log (Y/4) := by rw [hlogY4, hlog4]; linarith
    have hup : (Nat.primeCounting ⌊Y/4⌋₊ : ℝ) * (0.99 * lam) ≤ (Real.log 4 + 0.01) * (Y/4) := by
      have hpos : 0 < Real.log (Y/4) := by linarith
      rw [le_div_iff₀ hpos] at h1
      calc (Nat.primeCounting ⌊Y/4⌋₊ : ℝ) * (0.99 * lam) ≤ (Nat.primeCounting ⌊Y/4⌋₊ : ℝ) * Real.log (Y/4) :=
            mul_le_mul_of_nonneg_left hlogY4' (Nat.cast_nonneg _)
        _ ≤ _ := h1
    rw [div_le_iff₀ (by positivity)]
    rw [hlog4] at hk1 hup
    have hY23 : 23 * lam ≤ Y := by linarith
    nlinarith
  ------------------------------------------------------------------
  -- K5–K7, Kdiv, Ksmall
  ------------------------------------------------------------------
  K5 (N : ℕ) (hN : 1 ≤ N) :
      Real.log (Real.log (N+1)) - 1 ≤ ∑ p ∈ (Finset.range (N+1)).filter Nat.Prime, (1/(p:ℝ)) := by
    set P := (Finset.range (N+1)).filter Nat.Prime with hP
    have h1 := K3f N
    have h2 : ∑ n ∈ Finset.Icc 1 N, (1/(n:ℝ)) = (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc]; push_cast; simp [one_div]
    have h3 := log_add_one_le_harmonic N
    push_cast at h3
    have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
    have hlogpos : 0 < Real.log (N+1) := Real.log_pos (by linarith)
    have hp2 : ∀ p ∈ P, (2:ℝ) ≤ p := fun p hp => by exact_mod_cast (Finset.mem_filter.1 hp).2.two_le
    have hfac : ∀ p ∈ P, 0 < 1 - 1/(p:ℝ) := by
      intro p hp
      have := hp2 p hp
      have : 1/(p:ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
      linarith
    have h4 : Real.log (Real.log (N+1)) ≤ ∑ p ∈ P, Real.log ((1 - 1/(p:ℝ))⁻¹) := by
      rw [← Real.log_prod (fun p hp => (inv_pos.2 (hfac p hp)).ne')]
      exact Real.log_le_log hlogpos (by linarith)
    have h5 : ∀ p ∈ P, Real.log ((1 - 1/(p:ℝ))⁻¹) ≤ 1/(p:ℝ) + (1/((p:ℝ)-1) - 1/p) := by
      intro p hp
      have hp2' := hp2 p hp
      have := Real.log_le_sub_one_of_pos (inv_pos.2 (hfac p hp))
      have hp1 : (p:ℝ) - 1 ≠ 0 := by linarith
      have hp0 : (p:ℝ) ≠ 0 := by linarith
      have e : (1 - 1/(p:ℝ))⁻¹ - 1 = 1/((p:ℝ)-1) := by
        field_simp
        ring
      linarith
    have htel : ∀ M : ℕ, 1 ≤ M → ∑ n ∈ Finset.Icc 2 M, (1/((n:ℝ)-1) - 1/n) = 1 - 1/M := by
      intro M hM
      induction M, hM using Nat.le_induction with
      | base => simp
      | succ M hM ih =>
        rw [Finset.sum_Icc_succ_top (by omega), ih]
        have hM0 : (M:ℝ) ≠ 0 := by have : (1:ℝ) ≤ M := by exact_mod_cast hM
                                   linarith
        push_cast
        have : (M:ℝ) + 1 - 1 = M := by ring
        rw [this]
        field_simp
        ring
    have h6 : ∑ p ∈ P, (1/((p:ℝ)-1) - 1/p) ≤ 1 := by
      calc ∑ p ∈ P, (1/((p:ℝ)-1) - 1/p) ≤ ∑ n ∈ Finset.Icc 2 N, (1/((n:ℝ)-1) - 1/n) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro p hp
              rw [Finset.mem_Icc]
              have := (Finset.mem_filter.1 hp)
              exact ⟨this.2.two_le, by have := Finset.mem_range.1 this.1; omega⟩
            · intro n hn _
              rw [Finset.mem_Icc] at hn
              have : (2:ℝ) ≤ n := by exact_mod_cast hn.1
              have : 1/(n:ℝ) ≤ 1/((n:ℝ)-1) := one_div_le_one_div_of_le (by linarith) (by linarith)
              linarith
        _ = 1 - 1/N := htel N hN
        _ ≤ 1 := by have : 0 ≤ 1/(N:ℝ) := by positivity
                    linarith
    have h7 := Finset.sum_le_sum h5
    rw [Finset.sum_add_distrib] at h7
    linarith
  K6 (P : Finset ℕ) (w : ℕ → ℝ) (ε : ℝ) (hε : 0 ≤ ε) (hw0 : ∀ p ∈ P, 0 ≤ w p)
      (hwε : ∀ p ∈ P, w p ≤ ε) :
      ∀ k : ℕ, k * ε ≤ ∑ p ∈ P, w p →
        (∑ p ∈ P, w p - k * ε)^k / (k ! : ℝ) ≤ ∑ D ∈ P.powersetCard k, ∏ p ∈ D, w p := by
    set S := ∑ p ∈ P, w p with hS
    have hrec : ∀ j : ℕ, (∑ D ∈ P.powersetCard j, ∏ p ∈ D, w p) * (S - j * ε) ≤
        (j+1) * ∑ E ∈ P.powersetCard (j+1), ∏ p ∈ E, w p := by
      intro j
      have hdc : ∑ E ∈ P.powersetCard (j+1), ∑ p ∈ E, ∏ q ∈ E, w q =
          ∑ D ∈ P.powersetCard j, ∑ p ∈ P \ D, ∏ q ∈ insert p D, w q := by
        rw [Finset.sum_sigma', Finset.sum_sigma']
        apply Finset.sum_nbij' (fun x => ⟨x.1.erase x.2, x.2⟩) (fun y => ⟨insert y.2 y.1, y.2⟩)
        · intro x hx
          simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hx ⊢
          refine ⟨⟨(Finset.erase_subset _ _).trans hx.1.1, ?_⟩, ?_⟩
          · rw [Finset.card_erase_of_mem hx.2, hx.1.2]; rfl
          · rw [Finset.mem_sdiff]; exact ⟨hx.1.1 hx.2, Finset.notMem_erase _ _⟩
        · intro y hy
          simp only [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_sdiff] at hy ⊢
          refine ⟨⟨Finset.insert_subset hy.2.1 hy.1.1, ?_⟩, Finset.mem_insert_self _ _⟩
          rw [Finset.card_insert_of_notMem hy.2.2, hy.1.2]
        · intro x hx
          simp only [Finset.mem_sigma] at hx
          simp [Finset.insert_erase hx.2]
        · intro y hy
          simp only [Finset.mem_sigma, Finset.mem_sdiff] at hy
          simp [Finset.erase_insert hy.2.2]
        · intro x hx
          simp only [Finset.mem_sigma] at hx
          simp [Finset.insert_erase hx.2]
      have hL : ∑ E ∈ P.powersetCard (j+1), ∑ p ∈ E, ∏ q ∈ E, w q =
          (j+1) * ∑ E ∈ P.powersetCard (j+1), ∏ p ∈ E, w p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro E hE
        rw [Finset.sum_const, (Finset.mem_powersetCard.1 hE).2, nsmul_eq_mul]; push_cast; ring
      rw [← hL, hdc, Finset.sum_mul]
      apply Finset.sum_le_sum; intro D hD
      have hD' := Finset.mem_powersetCard.1 hD
      have hins : ∀ p ∈ P \ D, ∏ q ∈ insert p D, w q = w p * ∏ q ∈ D, w q := by
        intro p hp
        rw [Finset.prod_insert (Finset.mem_sdiff.1 hp).2]
      rw [Finset.sum_congr rfl hins, ← Finset.sum_mul]
      have hsd : ∑ p ∈ P \ D, w p = S - ∑ p ∈ D, w p := by
        rw [hS, ← Finset.sum_sdiff hD'.1]; ring
      have hDle : ∑ p ∈ D, w p ≤ j * ε := by
        calc ∑ p ∈ D, w p ≤ ∑ p ∈ D, ε := Finset.sum_le_sum (fun p hp => hwε p (hD'.1 hp))
          _ = j * ε := by rw [Finset.sum_const, hD'.2, nsmul_eq_mul]
      have hprod : 0 ≤ ∏ q ∈ D, w q := Finset.prod_nonneg (fun q hq => hw0 q (hD'.1 hq))
      rw [hsd]
      nlinarith
    intro k
    induction k with
    | zero =>
      intro _
      simp
    | succ k ih =>
      intro hk
      have hk' : (k:ℝ) * ε ≤ S := by push_cast at hk; nlinarith
      have ih' := ih hk'
      have hr := hrec k
      push_cast at hk ⊢
      have hA : 0 ≤ S - (k+1) * ε := by linarith
      have hB : S - (k+1) * ε ≤ S - k * ε := by linarith
      have hpow : (S - (k+1)*ε)^k ≤ (S - k*ε)^k := pow_le_pow_left₀ hA hB k
      have hfact : ((k+1)! : ℝ) = (k+1) * (k ! : ℝ) := by push_cast [Nat.factorial_succ]; ring
      have hkf : (0:ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
      rw [hfact, pow_succ]
      rw [div_le_iff₀ (by positivity)]
      have ih'' : (S - k*ε)^k ≤ (∑ D ∈ P.powersetCard k, ∏ p ∈ D, w p) * (k ! : ℝ) := by
        rwa [div_le_iff₀ hkf] at ih'
      calc (S - (k+1)*ε)^k * (S - (k+1)*ε) ≤ (S - k*ε)^k * (S - k*ε) := by
            apply mul_le_mul hpow hB hA (pow_nonneg (by linarith) k)
        _ ≤ (∑ D ∈ P.powersetCard k, ∏ p ∈ D, w p) * (k ! : ℝ) * (S - k*ε) :=
            mul_le_mul_of_nonneg_right ih'' (by linarith)
        _ = ((∑ D ∈ P.powersetCard k, ∏ p ∈ D, w p) * (S - k*ε)) * (k ! : ℝ) := by ring
        _ ≤ ((k+1) * ∑ E ∈ P.powersetCard (k+1), ∏ p ∈ E, w p) * (k ! : ℝ) :=
            mul_le_mul_of_nonneg_right hr hkf.le
        _ = (∑ E ∈ P.powersetCard (k+1), ∏ p ∈ E, w p) * ((k+1) * (k ! : ℝ)) := by ring
  K7 (k : ℕ) (hk : 1 ≤ k) :
      (k ! : ℝ) ≤ Real.exp 1 * Real.sqrt k * (k / Real.exp 1)^k := by
    have h1 : Stirling.stirlingSeq k ≤ Stirling.stirlingSeq 1 := by
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      exact Stirling.stirlingSeq'_antitone (Nat.zero_le m)
    rw [Stirling.stirlingSeq_one] at h1
    unfold Stirling.stirlingSeq at h1
    have hk0 : (0:ℝ) < k := by exact_mod_cast hk
    have hpos : 0 < Real.sqrt (2 * k) * (k / Real.exp 1)^k := by positivity
    rw [div_le_iff₀ hpos] at h1
    have hs : Real.sqrt (2 * (k:ℝ)) = Real.sqrt 2 * Real.sqrt k := Real.sqrt_mul (by norm_num) _
    have hs2 : Real.sqrt 2 ≠ 0 := by positivity
    calc (k ! : ℝ) ≤ Real.exp 1 / Real.sqrt 2 * (Real.sqrt (2 * k) * (k / Real.exp 1)^k) := h1
      _ = Real.exp 1 * Real.sqrt k * (k / Real.exp 1)^k := by
          rw [hs]; field_simp
  Kdiv (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) :
      ((∏ p ∈ D, p).divisors.card) ≤ 2^D.card := by
    induction D using Finset.induction_on with
    | empty => simp
    | insert p D hpD ih =>
      rw [Finset.prod_insert hpD, Nat.divisors_mul, Finset.card_insert_of_notMem hpD, pow_succ]
      have hp := hD p (Finset.mem_insert_self _ _)
      have ih' := ih (fun q hq => hD q (Finset.mem_insert_of_mem hq))
      calc (p.divisors * (∏ q ∈ D, q).divisors).card ≤ p.divisors.card * (∏ q ∈ D, q).divisors.card :=
            Finset.card_mul_le
        _ ≤ 2 * 2^D.card := by
            rw [Nat.Prime.divisors hp]
            apply Nat.mul_le_mul _ ih'
            exact (Finset.card_insert_le _ _).trans (by simp)
        _ = 2^D.card * 2 := by ring
  Ksmall : ∑ p ∈ (Finset.range 102).filter Nat.Prime, (1/(p:ℝ)) ≤ 6 := by
    have h1 : ∑ p ∈ (Finset.range 102).filter Nat.Prime, (1/(p:ℝ)) ≤
        ∑ n ∈ (Finset.Icc 1 101 : Finset ℕ), (1/(n:ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        rw [Finset.mem_filter, Finset.mem_range] at hp
        rw [Finset.mem_Icc]; exact ⟨hp.2.one_lt.le, by omega⟩
      · intro n _ _; positivity
    have h2 : ∑ n ∈ (Finset.Icc 1 101 : Finset ℕ), (1/(n:ℝ)) = (harmonic 101 : ℝ) := by
      rw [harmonic_eq_sum_Icc]; push_cast; simp [one_div]
    have h3 := harmonic_le_one_add_log 101
    have h4 : Real.log 101 ≤ 5 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have := Real.exp_one_gt_d9
      have h : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h]
      have h5 : (2.7:ℝ)^5 ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) (by linarith) 5
      norm_num at h5
      linarith
    push_cast at h3
    linarith
-- [END_PROOF]