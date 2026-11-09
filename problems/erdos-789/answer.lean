-- [START_IMMUTABLE_CONTEXT]
import Mathlib
set_option maxHeartbeats 4000000

open Filter
open scoped Asymptotics Finset
namespace Erdos789
/-- Given a non-negative integer $n$, we say $m$ is a separating cardinality of
subset sums if, for any set $A$ of $n$ integers, there is some $B\subseteq A$ of
size $\geq m$ such that subset sums of $B$ can only ever coincide when the
subsets have the same cardinality. -/
def IsSubsetSumSeparatingCard (n m : ℕ) : Prop :=
  ∀ A : Finset ℤ, #A = n → ∃ B : Finset ℤ, B ⊆ A ∧ m ≤ #B ∧
    (∀ᵉ (T ⊆ B) (S ⊆ B), S.Nonempty → T.Nonempty → ∑ a ∈ T, a = ∑ b ∈ S, b → #T = #S)
/-- The subset sum threshold $h(n)$, for each positive $n$, is the maximal separating
cardinality of subset sums for $n$. -/
noncomputable def subsetSumThreshold (n : ℕ): ℕ :=
  sSup { m | IsSubsetSumSeparatingCard n m }
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
axiom erdos_789.variants.cube_root_linearithmic : (fun n ↦ (subsetSumThreshold n : ℝ)) =Θ[atTop] fun n ↦ (n * Real.log n) ^ ((1 : ℝ) / 3)
-- [END_IMMUTABLE_CONTEXT]

-- [START_PROOF]
theorem erdos_789.variants.cube_root_linearithmic_disproof : False :=
by
  classical
  ------------------------------------------------------------------
  -- Determinant bound: |det M| ≤ r! k^r for entries bounded by k.
  ------------------------------------------------------------------
  have det_bound : ∀ (r k : ℕ) (M : Matrix (Fin r) (Fin r) ℤ), (∀ i j, |M i j| ≤ k) →
      |M.det| ≤ ((r.factorial * k ^ r : ℕ) : ℤ) := by
    intro r k M hM
    rw [Matrix.det_apply]
    calc |∑ σ : Equiv.Perm (Fin r), Equiv.Perm.sign σ • ∏ i, M (σ i) i|
        ≤ ∑ σ : Equiv.Perm (Fin r), |Equiv.Perm.sign σ • ∏ i, M (σ i) i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ σ : Equiv.Perm (Fin r), ((k : ℤ) ^ r) := by
          apply Finset.sum_le_sum
          intro σ _
          have h1 : |Equiv.Perm.sign σ • ∏ i, M (σ i) i| = ∏ i, |M (σ i) i| := by
            rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
              simp [h, Finset.abs_prod]
          rw [h1]
          calc ∏ i, |M (σ i) i| ≤ ∏ _i : Fin r, (k : ℤ) :=
                Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => hM _ _)
            _ = (k : ℤ) ^ r := by simp
      _ = ((r.factorial * k ^ r : ℕ) : ℤ) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_perm]
  ------------------------------------------------------------------
  -- [CRUX s4] Linear algebra: small integer vectors orthogonal to all
  -- relation vectors, spanning enough to see 𝐝 (maximal nonsingular minor,
  -- Schur complement, Cramer's rule).
  ------------------------------------------------------------------
  have LA : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (W : (ι → ℤ) → Prop) (k : ℕ), 1 ≤ k →
      (∀ w, W w → ∀ i, |w i| ≤ k) → ∀ (dd : ι → ℤ), (∀ w, W w → ∑ i, w i * dd i = 0) →
      ∃ Δ : ℤ, Δ ≠ 0 ∧ ∃ z : ι → ι → ℤ, (∀ j w, W w → ∑ i, w i * z j i = 0) ∧
        (∀ i, ∑ j, dd j * z j i = Δ * dd i) ∧
        (∀ j i, |z j i| ≤ (((Fintype.card ι + 1).factorial * k ^ Fintype.card ι : ℕ) : ℤ)) := by
    intro ι _ _ W k hk hW dd hWd
    let Q : ℕ → Prop := fun r => ∃ R : Fin r → ι → ℤ, (∀ m, W (R m)) ∧
      ∃ c : Fin r → ι, (Matrix.of fun m l => R m (c l)).det ≠ 0
    have hQ0 : Q 0 := ⟨Fin.elim0, fun m => m.elim0, Fin.elim0, by simp⟩
    have hQle : ∀ r, Q r → r ≤ Fintype.card ι := by
      rintro r ⟨R, -, c, hc⟩
      have hinj : Function.Injective c := by
        intro l1 l2 h
        by_contra hne
        exact hc (Matrix.det_zero_of_column_eq hne (fun m => by simp [h]))
      simpa using Fintype.card_le_of_injective c hinj
    obtain ⟨r, hQr, hQr1⟩ : ∃ r, Q r ∧ ¬ Q (r+1) := by
      refine ⟨Nat.findGreatest Q (Fintype.card ι), Nat.findGreatest_spec (Nat.zero_le _) hQ0, ?_⟩
      intro h
      exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (hQle _ h) h
    have hrd : r ≤ Fintype.card ι := hQle r hQr
    obtain ⟨R, hRW, c, hc⟩ := hQr
    obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin r) (Fin r) ℤ, A = Matrix.of fun m l => R m (c l) :=
      ⟨_, rfl⟩
    rw [← hA] at hc
    have hbord : ∀ w, W w → ∀ j : ι,
        (Matrix.of fun (x y : Fin r ⊕ Unit) =>
          (Sum.elim R (fun _ => w) x) (Sum.elim c (fun _ => j) y)).det = 0 := by
      intro w hw j
      by_contra hne
      apply hQr1
      let e : Fin r ⊕ Unit ≃ Fin (r+1) := Fintype.equivFinOfCardEq (by simp)
      refine ⟨fun m => Sum.elim R (fun _ => w) (e.symm m), ?_,
        fun l => Sum.elim c (fun _ => j) (e.symm l), ?_⟩
      · intro m
        dsimp only
        cases e.symm m with
        | inl x => exact hRW x
        | inr x => exact hw
      · rw [← Matrix.det_reindex_self e] at hne
        exact hne
    let Aq : Matrix (Fin r) (Fin r) ℚ := A.map (fun x => (x : ℚ))
    have hAq : Aq.det ≠ 0 := by
      have : Aq.det = ((A.det : ℤ) : ℚ) := (Int.cast_det A).symm
      rw [this]; exact_mod_cast hc
    haveI : Invertible Aq := Matrix.invertibleOfIsUnitDet Aq (isUnit_iff_ne_zero.mpr hAq)
    have hspan : ∀ w, W w → ∃ μ : Fin r → ℚ, ∀ j, ((w j : ℤ) : ℚ) = ∑ m, μ m * (R m j : ℚ) := by
      intro w hw
      refine ⟨fun m => ∑ l, (w (c l) : ℚ) * Aq⁻¹ l m, fun j => ?_⟩
      have h0 := hbord w hw j
      have h1 : ((Matrix.of fun (x y : Fin r ⊕ Unit) =>
          (Sum.elim R (fun _ => w) x) (Sum.elim c (fun _ => j) y)).map (fun x => (x : ℚ))) =
          Matrix.fromBlocks Aq (Matrix.of fun m (_ : Unit) => (R m j : ℚ))
            (Matrix.of fun (_ : Unit) l => (w (c l) : ℚ)) (Matrix.of fun _ _ => (w j : ℚ)) := by
        ext x y
        rcases x with x | x <;> rcases y with y | y <;> simp [Aq, hA]
      have h2 := Matrix.det_fromBlocks₁₁ Aq (Matrix.of fun m (_ : Unit) => (R m j : ℚ))
        (Matrix.of fun (_ : Unit) l => (w (c l) : ℚ)) (Matrix.of fun _ _ => (w j : ℚ))
      rw [← h1, ← Int.cast_det, h0, Int.cast_zero] at h2
      have h3 := (mul_eq_zero.mp h2.symm).resolve_left hAq
      rw [Matrix.det_unique] at h3
      simp [Matrix.sub_apply, Matrix.mul_apply] at h3
      linarith
    obtain ⟨y, hy⟩ : ∃ y : ι → Fin r → ℤ, ∀ j, y j = A.cramer (fun m => R m j) :=
      ⟨_, fun _ => rfl⟩
    obtain ⟨z, hz⟩ : ∃ z : ι → ι → ℤ, ∀ j i,
        z j i = (if i = j then A.det else 0) - ∑ l, (if i = c l then y j l else 0) :=
      ⟨_, fun _ _ => rfl⟩
    have hRz : ∀ m j, ∑ i, R m i * z j i = 0 := by
      intro m j
      have hc' := congrFun (Matrix.mulVec_cramer A (fun m => R m j)) m
      rw [← hy] at hc'
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hA,
        Matrix.of_apply] at hc'
      rw [← hA] at hc'
      simp only [hz, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hc']; ring
    refine ⟨A.det, hc, z, ?_, ?_, ?_⟩
    · intro j w hw
      obtain ⟨μ, hμ⟩ := hspan w hw
      have : ((∑ i, w i * z j i : ℤ) : ℚ) = 0 := by
        push_cast
        calc ∑ i, (w i : ℚ) * (z j i : ℚ) = ∑ i, (∑ m, μ m * (R m i : ℚ)) * (z j i : ℚ) :=
              Finset.sum_congr rfl (fun i _ => by rw [hμ i])
          _ = ∑ m, μ m * ∑ i, (R m i : ℚ) * (z j i : ℚ) := by
              simp_rw [Finset.sum_mul, Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro m _
              apply Finset.sum_congr rfl; intro i _
              ring
          _ = 0 := by
              apply Finset.sum_eq_zero
              intro m _
              have hq : (∑ i, (R m i : ℚ) * (z j i : ℚ)) = 0 := by exact_mod_cast hRz m j
              rw [hq, mul_zero]
      exact_mod_cast this
    · intro i
      have hy0 : ∀ l, ∑ j, dd j * y j l = 0 := by
        intro l
        have h0 : (∑ j, dd j • fun m => R m j) = 0 := by
          funext m
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
          rw [← hWd (R m) (hRW m)]
          apply Finset.sum_congr rfl; intro _ _; ring
        have h2 : A.cramer (∑ j, dd j • fun m => R m j) =
            ∑ j, dd j • A.cramer (fun m => R m j) := by
          rw [map_sum]
          exact Finset.sum_congr rfl (fun j _ => LinearMap.map_smul _ _ _)
        rw [h0, map_zero] at h2
        have := congrFun h2 l
        simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
        simp only [hy]
        linarith
      simp only [hz, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_ite, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [Finset.sum_comm]
      have : ∀ l, ∑ j, (if i = c l then dd j * y j l else 0) = 0 := by
        intro l
        split_ifs
        · exact hy0 l
        · simp
      simp only [this, Finset.sum_const_zero, sub_zero]
      ring
    · intro j i
      have hbd : ∀ M : Matrix (Fin r) (Fin r) ℤ, (∀ a b, |M a b| ≤ k) →
          |M.det| ≤ ((r.factorial * k ^ r : ℕ) : ℤ) := fun M hM => det_bound r k M hM
      have hAb : ∀ a b, |A a b| ≤ k := by
        intro a b; rw [hA]; exact hW _ (hRW a) _
      have hΔ := hbd A hAb
      have hyb : ∀ l, |y j l| ≤ ((r.factorial * k ^ r : ℕ) : ℤ) := by
        intro l
        rw [hy, Matrix.cramer_apply]
        apply hbd
        intro a b
        rw [Matrix.updateCol_apply]
        split_ifs
        · exact hW _ (hRW a) _
        · exact hAb a b
      rw [hz]
      have e1 : |(if i = j then A.det else 0)| ≤ ((r.factorial * k ^ r : ℕ) : ℤ) := by
        split_ifs
        · exact hΔ
        · simp only [abs_zero]; positivity
      have e2 : |∑ l, (if i = c l then y j l else 0)| ≤ r * ((r.factorial * k ^ r : ℕ) : ℤ) := by
        calc |∑ l, (if i = c l then y j l else 0)| ≤ ∑ l, |(if i = c l then y j l else 0)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _l : Fin r, ((r.factorial * k ^ r : ℕ) : ℤ) := by
              apply Finset.sum_le_sum; intro l _
              split_ifs
              · exact hyb l
              · simp only [abs_zero]; positivity
          _ = r * ((r.factorial * k ^ r : ℕ) : ℤ) := by simp
      have e3 : ((r + 1).factorial * k ^ r : ℕ) ≤
          ((Fintype.card ι + 1).factorial * k ^ Fintype.card ι : ℕ) :=
        Nat.mul_le_mul (Nat.factorial_le (by omega)) (Nat.pow_le_pow_right hk hrd)
      have e4 : ((r + 1).factorial * k ^ r : ℕ) = (r + 1) * (r.factorial * k ^ r) := by
        rw [Nat.factorial_succ]; ring
      calc |(if i = j then A.det else 0) - ∑ l, (if i = c l then y j l else 0)|
          ≤ |(if i = j then A.det else 0)| + |∑ l, (if i = c l then y j l else 0)| :=
            abs_sub _ _
        _ ≤ ((r.factorial * k ^ r : ℕ) : ℤ) + r * ((r.factorial * k ^ r : ℕ) : ℤ) :=
            add_le_add e1 e2
        _ = (((r + 1).factorial * k ^ r : ℕ) : ℤ) := by rw [e4]; push_cast; ring
        _ ≤ _ := by exact_mod_cast e3
  ------------------------------------------------------------------
  -- Averaging over {0,1}-combinations.
  ------------------------------------------------------------------
  have AVG : ∀ {ι α : Type} [Fintype ι] [DecidableEq ι] (P : Finset α) (v : α → ι → ℤ),
      (∀ a ∈ P, ∃ j, v a j ≠ 0) →
      ∃ S : Finset ι, P.card ≤ 2 * (P.filter fun a => ¬ ∑ j ∈ S, v a j = 0).card := by
    intro ι α _ _ P v hv
    have key : ∀ a ∈ P, (Finset.univ : Finset (Finset ι)).card ≤
        2 * ((Finset.univ : Finset (Finset ι)).filter fun S => ¬ ∑ j ∈ S, v a j = 0).card := by
      intro a ha
      obtain ⟨j0, hj0⟩ := hv a ha
      let f : Finset ι → Finset ι := fun S => if j0 ∈ S then S.erase j0 else insert j0 S
      have hf : ∀ S, f (f S) = S := by
        intro S; by_cases h : j0 ∈ S <;> simp [f, h, Finset.insert_erase]
      have hle : ((Finset.univ : Finset (Finset ι)).filter fun S => ∑ j ∈ S, v a j = 0).card ≤
          ((Finset.univ : Finset (Finset ι)).filter fun S => ¬ ∑ j ∈ S, v a j = 0).card := by
        apply Finset.card_le_card_of_injOn f
        · intro S hS
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hS ⊢
          by_cases h : j0 ∈ S
          · simp only [f, h, if_true]
            rw [← Finset.add_sum_erase S _ h] at hS
            intro h2; apply hj0; linarith
          · simp only [f, h, if_false]
            rw [Finset.sum_insert h, hS]; simpa using hj0
        · intro S1 _ S2 _ h
          rw [← hf S1, ← hf S2, h]
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Finset ι)))
        (fun S => ∑ j ∈ S, v a j = 0)
      omega
    by_contra hcon
    push_neg at hcon
    have h1 : ∑ S : Finset ι, 2 * (P.filter fun a => ¬ ∑ j ∈ S, v a j = 0).card <
        ∑ S : Finset ι, P.card :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun S _ => hcon S)
    have h2 : ∑ S : Finset ι, (P.filter fun a => ¬ ∑ j ∈ S, v a j = 0).card =
        ∑ a ∈ P, ((Finset.univ : Finset (Finset ι)).filter
          fun S => ¬ ∑ j ∈ S, v a j = 0).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    have h3 : ∑ a ∈ P, (Finset.univ : Finset (Finset ι)).card ≤ ∑ a ∈ P, 2 *
        ((Finset.univ : Finset (Finset ι)).filter fun S => ¬ ∑ j ∈ S, v a j = 0).card :=
      Finset.sum_le_sum key
    rw [← Finset.mul_sum, ← h2] at h3
    rw [← Finset.mul_sum] at h1
    simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ] at h1 h3
    nlinarith
  ------------------------------------------------------------------
  -- [s6] few large prime factors.
  ------------------------------------------------------------------
  have SIX : ∀ (k K T : ℕ), 1 ≤ k → 1 ≤ T → ∀ (b : ℤ), b ≠ 0 → |b| ≤ ((k ^ T : ℕ) : ℤ) →
      ((Finset.Ioc k K).filter fun p => Nat.Prime p ∧ (p : ℤ) ∣ b).card < T := by
    intro k K T hk hT b hb0 hb
    set S := (Finset.Ioc k K).filter fun p => Nat.Prime p ∧ (p : ℤ) ∣ b
    have hdvd : ∏ p ∈ S, p ∣ b.natAbs := by
      apply Finset.prod_primes_dvd
      · intro p hp
        simp only [S, Finset.mem_filter] at hp
        exact Nat.prime_iff.mp hp.2.1
      · intro p hp
        simp only [S, Finset.mem_filter] at hp
        exact Int.natCast_dvd.mp hp.2.2
    have hpos : 0 < b.natAbs := Int.natAbs_pos.mpr hb0
    have h1 : ∏ p ∈ S, p ≤ b.natAbs := Nat.le_of_dvd hpos hdvd
    have h2 : (k + 1) ^ S.card ≤ ∏ p ∈ S, p := by
      apply Finset.pow_card_le_prod
      intro p hp
      simp only [S, Finset.mem_filter, Finset.mem_Ioc] at hp
      omega
    have h3 : b.natAbs ≤ k ^ T := by
      have : ((b.natAbs : ℕ) : ℤ) ≤ ((k ^ T : ℕ) : ℤ) := by
        rw [Int.natCast_natAbs]; exact hb
      exact_mod_cast this
    have h4 : k ^ T < (k + 1) ^ T := Nat.pow_lt_pow_left (by omega) (by omega)
    have h5 : (k + 1) ^ S.card < (k + 1) ^ T := by omega
    exact (Nat.pow_lt_pow_iff_right (by omega)).mp h5
  ------------------------------------------------------------------
  -- [s7] Chebyshev-type lower bound via the central binomial coefficient.
  ------------------------------------------------------------------
  have CHEB : ∀ k : ℕ, 1 ≤ k →
      12 * k ≤ ((Finset.range (24 * k * (Nat.log 2 k + 10) + 1)).filter Nat.Prime).card := by
    intro k hk
    set L := Nat.log 2 k
    set m := 12 * k * (L + 10) with hm
    have hK : 24 * k * (L + 10) = 2 * m := by rw [hm]; ring
    rw [hK]
    set π' := ((Finset.range (2 * m + 1)).filter Nat.Prime).card
    have hmpos : 0 < m := by positivity
    have hcb : (2 * m).choose m ≤ (2 * m) ^ π' := by
      rw [← Nat.centralBinom_eq_two_mul_choose, ← Nat.prod_pow_factorization_centralBinom]
      calc ∏ p ∈ Finset.range (2 * m + 1), p ^ (Nat.centralBinom m).factorization p
          ≤ ∏ p ∈ Finset.range (2 * m + 1), (if Nat.Prime p then 2 * m else 1) := by
            apply Finset.prod_le_prod'
            intro p _
            split_ifs with hp
            · rw [Nat.centralBinom_eq_two_mul_choose]
              exact Nat.pow_factorization_choose_le (by omega)
            · rw [Nat.factorization_eq_zero_of_not_prime _ hp, pow_zero]
        _ = (2 * m) ^ π' := by
            rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    have h4 := Nat.four_pow_le_two_mul_add_one_mul_central_binom m
    by_contra hlt
    push_neg at hlt
    have h5 : (2 * m) ^ π' ≤ (2 * m + 1) ^ (12 * k - 1) :=
      le_trans (Nat.pow_le_pow_left (by omega) _) (Nat.pow_le_pow_right (by omega) (by omega))
    have h6 : 4 ^ m ≤ (2 * m + 1) ^ (12 * k) := by
      calc 4 ^ m ≤ (2 * m + 1) * (2 * m).choose m := h4
        _ ≤ (2 * m + 1) * (2 * m + 1) ^ (12 * k - 1) := Nat.mul_le_mul_left _ (hcb.trans h5)
        _ = (2 * m + 1) ^ (12 * k) := by
            rw [← pow_succ']; congr 1; omega
    have hkL : k < 2 * 2 ^ L := by
      have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) k
      rw [pow_succ] at this; linarith
    have hLL : L < 2 ^ L := Nat.lt_two_pow_self
    have hX : 1 ≤ 2 ^ L := Nat.one_le_two_pow
    have h7 : 2 * m + 1 < 4 ^ (L + 10) := by
      have e : 4 ^ (L + 10) = (2 ^ L) * (2 ^ L) * 1048576 := by
        rw [show (4:ℕ) = 2 ^ 2 by norm_num, ← pow_mul, show 2 * (L + 10) = L + L + 20 by ring,
          pow_add, pow_add]; norm_num
      rw [e, hm]
      nlinarith
    have h8 : (2 * m + 1) ^ (12 * k) < 4 ^ m := by
      calc (2 * m + 1) ^ (12 * k) < (4 ^ (L + 10)) ^ (12 * k) :=
            Nat.pow_lt_pow_left h7 (by omega)
        _ = 4 ^ m := by rw [← pow_mul, hm]; ring_nf
    omega
  ------------------------------------------------------------------
  -- [s8] double counting.
  ------------------------------------------------------------------
  have COUNT : ∀ {α : Type} [DecidableEq α] (A' : Finset α) (b : α → ℤ) (d k K T : ℕ),
      (∀ p, Nat.Prime p → k < p → p ≤ K →
        (A'.filter fun a => ¬ (p : ℤ) ∣ b a).card ≤ (p - 1) * d) →
      (∀ a ∈ A', ((Finset.Ioc k K).filter fun p => Nat.Prime p ∧ (p : ℤ) ∣ b a).card ≤ T) →
      2 * T ≤ ((Finset.Ioc k K).filter Nat.Prime).card → 1 ≤ T →
      A'.card ≤ 2 * K * d := by
    intro α _ A' b d k K T hres hsix hN hT
    set PK := (Finset.Ioc k K).filter Nat.Prime
    set N := PK.card
    have hper : ∀ p ∈ PK, A'.card ≤ (A'.filter fun a => (p : ℤ) ∣ b a).card + K * d := by
      intro p hp
      simp only [PK, Finset.mem_filter, Finset.mem_Ioc] at hp
      have e := Finset.card_filter_add_card_filter_not (s := A') (fun a => (p : ℤ) ∣ b a)
      have := hres p hp.2 hp.1.1 hp.1.2
      have : (p - 1) * d ≤ K * d := Nat.mul_le_mul_right _ (by omega)
      omega
    have hsum : N * A'.card ≤
        ∑ p ∈ PK, (A'.filter fun a => (p : ℤ) ∣ b a).card + N * (K * d) := by
      have := Finset.sum_le_sum hper
      simp only [Finset.sum_const, smul_eq_mul, Finset.sum_add_distrib] at this
      exact this
    have hswap : ∑ p ∈ PK, (A'.filter fun a => (p : ℤ) ∣ b a).card =
        ∑ a ∈ A', (PK.filter fun p : ℕ => (p : ℤ) ∣ b a).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    have hPK : ∀ a ∈ A', (PK.filter fun p : ℕ => (p : ℤ) ∣ b a).card ≤ T := by
      intro a ha
      have := hsix a ha
      simp only [PK, Finset.filter_filter]
      exact this
    have hle : ∑ a ∈ A', (PK.filter fun p : ℕ => (p : ℤ) ∣ b a).card ≤ A'.card * T := by
      have := Finset.sum_le_sum hPK
      simpa [Finset.sum_const, smul_eq_mul] using this
    rw [hswap] at hsum
    have hNpos : 0 < N := by omega
    have : N * A'.card ≤ N * (2 * K * d) := by nlinarith
    exact Nat.le_of_mul_le_mul_left this hNpos
  ------------------------------------------------------------------
  -- Main combinatorial bound: every A has a separating D with
  -- (|A|-1)^2 ≤ 921600 (|D|+1)^5.
  ------------------------------------------------------------------
  have MAIN : ∀ A : Finset ℤ, ∃ D ⊆ A, (∀ T, T ⊆ D → ∀ S, S ⊆ D → S.Nonempty → T.Nonempty →
      ∑ a ∈ T, a = ∑ b ∈ S, b → T.card = S.card) ∧
      (A.card - 1) ^ 2 ≤ 921600 * (D.card + 1) ^ 5 := by
    intro A
    set P := A.erase 0 with hP
    have hPA : P ⊆ A := Finset.erase_subset 0 A
    have h0P : (0:ℤ) ∉ P := Finset.notMem_erase 0 A
    have hAP : A.card - 1 ≤ P.card := by
      rw [hP, Finset.card_erase_eq_ite]; split_ifs <;> omega
    obtain ⟨good, hgood⟩ : ∃ good : Finset ℤ → Prop, ∀ B, good B ↔
        ∀ ε : ℤ → ℤ, (∀ b ∈ B, ε b = -1 ∨ ε b = 0 ∨ ε b = 1) →
          ∑ b ∈ B, ε b * b = 0 → ∑ b ∈ B, ε b = 0 := ⟨_, fun _ => Iff.rfl⟩
    have hgl : ∀ B, good B → ∀ T, T ⊆ B → ∀ S, S ⊆ B → S.Nonempty → T.Nonempty →
        ∑ a ∈ T, a = ∑ b ∈ S, b → T.card = S.card := by
      intro B hB T hT S hS _ _ hsum
      have e1 : ∀ U ⊆ B, ∑ b ∈ B, (if b ∈ U then (1:ℤ) else 0) * b = ∑ b ∈ U, b := by
        intro U hU
        simp only [ite_mul, one_mul, zero_mul]
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hU]
      have e2 : ∀ U ⊆ B, ∑ b ∈ B, (if b ∈ U then (1:ℤ) else 0) = U.card := by
        intro U hU
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hU]; simp
      have := (hgood B).mp hB
        (fun b => (if b ∈ T then 1 else 0) - (if b ∈ S then 1 else 0))
        (by intro b _; dsimp only; split_ifs <;> simp)
        (by simp only [sub_mul, Finset.sum_sub_distrib]; rw [e1 T hT, e1 S hS, hsum, sub_self])
      simp only [Finset.sum_sub_distrib] at this
      rw [e2 T hT, e2 S hS] at this
      omega
    have hGne : (P.powerset.filter good).Nonempty := ⟨∅, by simp [hgood]⟩
    obtain ⟨D, hDmem, hDmax⟩ := Finset.exists_max_image _ Finset.card hGne
    simp only [Finset.mem_filter, Finset.mem_powerset] at hDmem hDmax
    obtain ⟨hDP, hDgood⟩ := hDmem
    have hmax : ∀ B, B ⊆ P → good B → B.card ≤ D.card := fun B h1 h2 => hDmax B ⟨h1, h2⟩
    refine ⟨D, hDP.trans hPA, hgl D hDgood, ?_⟩
    rcases Nat.eq_zero_or_pos P.card with hP0 | hPpos
    · have : A.card - 1 = 0 := by omega
      rw [this]; simp
    set d := D.card with hd
    have hd1 : 1 ≤ d := by
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hPpos
      have hag : good {a} := by
        rw [hgood]; intro ε _ hsum
        simp only [Finset.sum_singleton] at hsum ⊢
        rcases mul_eq_zero.mp hsum with h | h
        · exact h
        · exact absurd (h ▸ ha) h0P
      have := hmax {a} (Finset.singleton_subset_iff.mpr ha) hag
      simpa using this
    set k := d + 1 with hk
    -- [s3] representation over D
    have hrep : ∀ a, ∃ η : D → ℤ, a ∈ P →
        (∀ i, η i = -1 ∨ η i = 0 ∨ η i = 1) ∧ ∑ i, η i * (i : ℤ) = a := by
      intro a
      by_cases ha : a ∈ P
      swap
      · exact ⟨0, fun h => absurd h ha⟩
      by_cases haD : a ∈ D
      · refine ⟨fun i => if (i : ℤ) = a then 1 else 0, fun _ => ⟨?_, ?_⟩⟩
        · intro i; dsimp only; split_ifs <;> simp
        · rw [Finset.sum_coe_sort D (fun x => (if x = a then (1:ℤ) else 0) * x)]
          simp [haD]
      · have hng : ¬ good (insert a D) := by
          intro hg
          have := hmax (insert a D) (Finset.insert_subset ha hDP) hg
          rw [Finset.card_insert_of_notMem haD] at this
          omega
        rw [hgood] at hng
        push_neg at hng
        obtain ⟨ε, hε, hrel, hne⟩ := hng
        rw [Finset.sum_insert haD] at hrel hne
        rcases hε a (Finset.mem_insert_self a D) with h | h | h
        · refine ⟨fun i => ε i, fun _ => ⟨fun i => hε i (Finset.mem_insert_of_mem i.2), ?_⟩⟩
          rw [Finset.sum_coe_sort D (fun x => ε x * x)]
          rw [h] at hrel; linarith
        · exfalso
          apply hne
          rw [h, zero_add]
          rw [h, zero_mul, zero_add] at hrel
          exact (hgood D).mp hDgood ε (fun b hb => hε b (Finset.mem_insert_of_mem hb)) hrel
        · refine ⟨fun i => -ε i, fun _ => ⟨?_, ?_⟩⟩
          · intro i
            rcases hε i (Finset.mem_insert_of_mem i.2) with h' | h' | h' <;> simp [h']
          · rw [Finset.sum_coe_sort D (fun x => -ε x * x)]
            rw [h] at hrel
            simp only [neg_mul, Finset.sum_neg_distrib]
            linarith
    choose η hη using hrep
    -- relation vectors of short relations
    obtain ⟨W, hWdef⟩ : ∃ W : (D → ℤ) → Prop, ∀ w, W w ↔ ∃ E : Finset ℤ, ∃ ε : ℤ → ℤ,
        E ⊆ P ∧ E.card ≤ k ∧ (∀ a ∈ E, ε a = -1 ∨ ε a = 0 ∨ ε a = 1) ∧
        ∑ a ∈ E, ε a * a = 0 ∧ w = fun i => ∑ a ∈ E, ε a * η a i := ⟨_, fun _ => Iff.rfl⟩
    have hWb : ∀ w, W w → ∀ i, |w i| ≤ k := by
      intro w hw i
      obtain ⟨E, ε, hE, hEk, hε, -, rfl⟩ := (hWdef w).mp hw
      calc |∑ a ∈ E, ε a * η a i| ≤ ∑ a ∈ E, |ε a * η a i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _a ∈ E, (1:ℤ) := by
            apply Finset.sum_le_sum
            intro a ha
            rcases hε a ha with h | h | h <;>
              rcases (hη a (hE ha)).1 i with h' | h' | h' <;> simp [h, h']
        _ = E.card := by simp
        _ ≤ k := by exact_mod_cast hEk
    have hWd : ∀ w, W w → ∑ i, w i * ((i : ℤ)) = 0 := by
      intro w hw
      obtain ⟨E, ε, hE, hEk, hε, hrel, rfl⟩ := (hWdef w).mp hw
      calc ∑ i : D, (∑ a ∈ E, ε a * η a i) * (i : ℤ)
          = ∑ a ∈ E, ε a * ∑ i : D, η a i * (i : ℤ) := by
            simp_rw [Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro a _
            apply Finset.sum_congr rfl; intro i _
            ring
        _ = ∑ a ∈ E, ε a * a := by
            apply Finset.sum_congr rfl; intro a ha
            rw [(hη a (hE ha)).2]
        _ = 0 := hrel
    -- [s4] the crux
    obtain ⟨Δ, hΔ, z, hzW, hzd, hzb⟩ := LA W k (by omega) hWb (fun i => (i : ℤ)) hWd
    rw [Fintype.card_coe] at hzb
    have hv : ∀ a ∈ P, ∃ j, ∑ i, η a i * z j i ≠ 0 := by
      intro a ha
      by_contra hcon
      push_neg at hcon
      have : Δ * a = 0 := by
        calc Δ * a = Δ * ∑ i, η a i * (i : ℤ) := by rw [(hη a ha).2]
          _ = ∑ i, η a i * (Δ * (i : ℤ)) := by
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
          _ = ∑ i, η a i * ∑ j : D, (j : ℤ) * z j i := by
              apply Finset.sum_congr rfl; intro i _; rw [hzd i]
          _ = ∑ j : D, (j : ℤ) * ∑ i, η a i * z j i := by
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro j _
              apply Finset.sum_congr rfl; intro i _
              ring
          _ = 0 := Finset.sum_eq_zero (fun j _ => by rw [hcon j, mul_zero])
      rcases mul_eq_zero.mp this with h | h
      · exact hΔ h
      · exact h0P (h ▸ ha)
    obtain ⟨S, hS⟩ := AVG P (fun a j => ∑ i, η a i * z j i) hv
    obtain ⟨b, hb⟩ : ∃ b : ℤ → ℤ, ∀ a, b a = ∑ j ∈ S, ∑ i, η a i * z j i := ⟨_, fun _ => rfl⟩
    set A' := P.filter fun a => ¬ b a = 0 with hA'
    have hPA' : P.card ≤ 2 * A'.card := by
      simp only [hA', hb]; exact hS
    have hA'P : A' ⊆ P := Finset.filter_subset _ _
    have hpres : ∀ E, E ⊆ P → E.card ≤ k → ∀ ε : ℤ → ℤ,
        (∀ a ∈ E, ε a = -1 ∨ ε a = 0 ∨ ε a = 1) → ∑ a ∈ E, ε a * a = 0 →
        ∑ a ∈ E, ε a * b a = 0 := by
      intro E hE hEk ε hε hrel
      have hw : W (fun i => ∑ a ∈ E, ε a * η a i) :=
        (hWdef _).mpr ⟨E, ε, hE, hEk, hε, hrel, rfl⟩
      calc ∑ a ∈ E, ε a * b a
          = ∑ j ∈ S, ∑ i, (∑ a ∈ E, ε a * η a i) * z j i := by
            simp_rw [hb, Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro j _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro i _
            apply Finset.sum_congr rfl; intro a _
            ring
        _ = 0 := by
            apply Finset.sum_eq_zero; intro j _
            exact hzW j _ hw
    have hbb : ∀ a ∈ P, |b a| ≤ ((k ^ (2 * k + 1) : ℕ) : ℤ) := by
      intro a ha
      have hSd : S.card ≤ d := by
        have := Finset.card_le_univ S
        rwa [Fintype.card_coe] at this
      have h1 : |b a| ≤ ∑ j ∈ S, ∑ i : D, (((d + 1).factorial * k ^ d : ℕ) : ℤ) := by
        rw [hb]
        calc |∑ j ∈ S, ∑ i, η a i * z j i| ≤ ∑ j ∈ S, |∑ i, η a i * z j i| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j ∈ S, ∑ i : D, |η a i * z j i| := by
              apply Finset.sum_le_sum; intro j _; exact Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j ∈ S, ∑ i : D, (((d + 1).factorial * k ^ d : ℕ) : ℤ) := by
              apply Finset.sum_le_sum; intro j _
              apply Finset.sum_le_sum; intro i _
              rw [abs_mul]
              have h1 : |η a i| ≤ 1 := by
                rcases (hη a ha).1 i with h | h | h <;> simp [h]
              calc |η a i| * |z j i| ≤ 1 * |z j i| :=
                    mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
                _ = |z j i| := one_mul _
                _ ≤ _ := hzb j i
      have h2 : ∑ j ∈ S, ∑ i : D, (((d + 1).factorial * k ^ d : ℕ) : ℤ) =
          ((S.card * d * ((d + 1).factorial * k ^ d) : ℕ) : ℤ) := by
        simp [Finset.sum_const]; ring
      have h3 : S.card * d * ((d + 1).factorial * k ^ d) ≤ k ^ (2 * k + 1) := by
        calc S.card * d * ((d + 1).factorial * k ^ d) ≤ k * k * (k ^ k * k ^ d) := by
              gcongr
              · omega
              · omega
              · exact Nat.factorial_le_pow k
          _ = k ^ (2 * k + 1) := by
              rw [hk]; ring
      rw [h2] at h1
      exact h1.trans (by exact_mod_cast h3)
    -- [s5] residue classes
    have hres0 : ∀ p, Nat.Prime p → k < p →
        (A'.filter fun a => ¬ (p : ℤ) ∣ b a).card ≤ (p - 1) * d := by
      intro p hp hkp
      have hp0 : (0:ℤ) < p := by exact_mod_cast hp.pos
      set s := A'.filter fun a => ¬ (p : ℤ) ∣ b a with hs
      have hfib : ∀ u ∈ s.image (fun a => b a % p),
          (s.filter fun a => b a % p = u).card ≤ d := by
        intro u hu
        by_contra hlt
        push_neg at hlt
        obtain ⟨E, hEsub, hEcard⟩ := Finset.exists_subset_card_eq (show d + 1 ≤ _ from hlt)
        have hEs : ∀ a ∈ E, a ∈ P ∧ ¬ (p:ℤ) ∣ b a ∧ b a % p = u := by
          intro a ha
          have := hEsub ha
          simp only [hs, hA', Finset.mem_filter] at this
          exact ⟨this.1.1.1, this.1.2, this.2⟩
        have hEP : E ⊆ P := fun a ha => (hEs a ha).1
        have hEgood : good E := by
          rw [hgood]
          intro ε hε hrel
          have h1 := hpres E hEP (by omega) ε hε hrel
          obtain ⟨a0, ha0, hu0⟩ := Finset.mem_image.mp hu
          have ha0' : ¬ (p:ℤ) ∣ b a0 := (Finset.mem_filter.mp ha0).2
          have h2 : ∑ a ∈ E, ε a * b a =
              p * ∑ a ∈ E, ε a * (b a / p) + u * ∑ a ∈ E, ε a := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl; intro a ha
            rw [← (hEs a ha).2.2]
            conv_lhs => rw [← Int.emod_add_ediv (b a) p]
            ring
          rw [h1] at h2
          have h3 : (p:ℤ) ∣ u * ∑ a ∈ E, ε a := ⟨-(∑ a ∈ E, ε a * (b a / p)), by linarith⟩
          have hpz : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
          rcases hpz.dvd_or_dvd h3 with h4 | h4
          · exfalso; apply ha0'
            rw [← hu0] at h4
            have := dvd_add h4 (dvd_mul_right (p:ℤ) (b a0 / p))
            rwa [Int.emod_add_ediv] at this
          · apply Int.eq_zero_of_abs_lt_dvd h4
            calc |∑ a ∈ E, ε a| ≤ ∑ a ∈ E, |ε a| := Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ _a ∈ E, (1:ℤ) := by
                  apply Finset.sum_le_sum; intro a ha
                  rcases hε a ha with h | h | h <;> simp [h]
              _ = E.card := by simp
              _ < p := by rw [hEcard]; exact_mod_cast hkp
        have := hmax E hEP hEgood
        omega
      have himg : s.image (fun a => b a % p) ⊆ Finset.Ioo (0:ℤ) p := by
        intro u hu
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
        have ha' : ¬ (p:ℤ) ∣ b a := (Finset.mem_filter.mp ha).2
        rw [Finset.mem_Ioo]
        refine ⟨lt_of_le_of_ne (Int.emod_nonneg _ hp0.ne') ?_, Int.emod_lt_of_pos _ hp0⟩
        intro h; exact ha' (Int.dvd_of_emod_eq_zero h.symm)
      have hcard : (Finset.Ioo (0:ℤ) p).card = p - 1 := by
        rw [Int.card_Ioo]; omega
      have h1 := Finset.card_le_mul_card_image s d hfib
      have h2 := Finset.card_le_card himg
      rw [hcard] at h2
      calc s.card ≤ d * (s.image fun a => b a % p).card := h1
        _ ≤ d * (p - 1) := Nat.mul_le_mul_left _ h2
        _ = (p - 1) * d := mul_comm _ _
    set L := Nat.log 2 k with hL
    set K := 24 * k * (L + 10) with hK
    have hcheb : 12 * k ≤ ((Finset.range (K + 1)).filter Nat.Prime).card := CHEB k (by omega)
    have hN : 2 * (2 * k + 1) ≤ ((Finset.Ioc k K).filter Nat.Prime).card := by
      have hsub : (Finset.range (K + 1)).filter Nat.Prime ⊆
          ((Finset.Ioc k K).filter Nat.Prime) ∪ Finset.range (k + 1) := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union,
          Finset.mem_Ioc] at hp ⊢
        by_cases h : p ≤ k
        · right; omega
        · left; exact ⟨⟨by omega, by omega⟩, hp.2⟩
      have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      simp only [Finset.card_range] at this
      omega
    have hsix : ∀ a ∈ A', ((Finset.Ioc k K).filter
        fun p => Nat.Prime p ∧ (p : ℤ) ∣ b a).card ≤ 2 * k + 1 := by
      intro a ha
      have ha' := Finset.mem_filter.mp ha
      exact (SIX k K (2 * k + 1) (by omega) (by omega) (b a) ha'.2 (hbb a ha'.1)).le
    have hcount := COUNT A' b d k K (2 * k + 1) (fun p hp h1 _ => hres0 p hp h1) hsix hN
      (by omega)
    have hLk : 2 ^ L ≤ k := Nat.pow_log_le_self 2 (by omega)
    have hL10 : ∀ n : ℕ, (n + 10) ^ 2 ≤ 100 * 2 ^ n := by
      intro n
      induction n with
      | zero => norm_num
      | succ n ih =>
        have e : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
        rw [e]
        have e2 : (n + 1 + 10) ^ 2 ≤ 2 * (n + 10) ^ 2 := by
          have : (n + 1 + 10) ^ 2 = (n + 10) ^ 2 + (2 * n + 21) := by ring
          have h' : 2 * n + 21 ≤ (n + 10) ^ 2 := by nlinarith
          omega
        omega
    have hPb : P.card ≤ 96 * k * (L + 10) * d := by
      calc P.card ≤ 2 * (2 * K * d) := hPA'.trans (Nat.mul_le_mul_left 2 hcount)
        _ = 96 * k * (L + 10) * d := by rw [hK]; ring
    have h1 : (A.card - 1) ^ 2 ≤ (96 * k * (L + 10) * d) ^ 2 :=
      Nat.pow_le_pow_left (hAP.trans hPb) 2
    have h2 : (96 * k * (L + 10) * d) ^ 2 = 9216 * k ^ 2 * d ^ 2 * (L + 10) ^ 2 := by ring
    have h3 : (L + 10) ^ 2 ≤ 100 * k := (hL10 L).trans (by omega)
    have h4 : d ≤ k := by omega
    calc (A.card - 1) ^ 2 ≤ 9216 * k ^ 2 * d ^ 2 * (L + 10) ^ 2 := h2 ▸ h1
      _ ≤ 9216 * k ^ 2 * k ^ 2 * (100 * k) := by gcongr
      _ = 921600 * (d + 1) ^ 5 := by rw [hk]; ring
  ------------------------------------------------------------------
  -- Lower bound for the threshold, then contradiction with the IsBigO half.
  ------------------------------------------------------------------
  have hlow : ∀ n : ℕ, (n - 1) ^ 2 ≤ 921600 * (subsetSumThreshold n + 1) ^ 5 := by
    intro n
    have hex : ∃ m : ℕ, (n - 1) ^ 2 ≤ 921600 * (m + 1) ^ 5 := ⟨n, by
      have : (n - 1) ^ 2 ≤ (n + 1) ^ 5 :=
        calc (n - 1) ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
          _ ≤ (n + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
      omega⟩
    have hsep : IsSubsetSumSeparatingCard n (Nat.find hex) := by
      intro A hA
      obtain ⟨D, hDA, hDl, hDb⟩ := MAIN A
      refine ⟨D, hDA, Nat.find_min' hex (by rw [← hA]; exact hDb), ?_⟩
      exact hDl
    have hbdd : BddAbove { m | IsSubsetSumSeparatingCard n m } := by
      refine ⟨n, fun m hm => ?_⟩
      obtain ⟨B, hB, hmB, -⟩ := hm ((Finset.range n).image (fun i : ℕ => (i : ℤ))) (by
        rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range])
      have := Finset.card_le_card hB
      rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range] at this
      omega
    have hle : Nat.find hex ≤ subsetSumThreshold n := le_csSup hbdd hsep
    calc (n - 1) ^ 2 ≤ 921600 * (Nat.find hex + 1) ^ 5 := Nat.find_spec hex
      _ ≤ 921600 * (subsetSumThreshold n + 1) ^ 5 := by gcongr
  have hO := erdos_789.variants.cube_root_linearithmic.1
  obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp hO
  obtain ⟨C0, hC0⟩ : ∃ C0 : ℝ, C0 = 64 * 921600 ^ 3 * (|c| + 1) ^ 15 := ⟨_, rfl⟩
  have hC0pos : 0 < C0 := by rw [hC0]; positivity
  have hlog := (Real.isLittleO_pow_log_id_atTop (n := 5)).comp_tendsto
    tendsto_natCast_atTop_atTop
  have hε := hlog.def (show (0:ℝ) < 1 / (2 * C0) by positivity)
  obtain ⟨n, hn1, hn2, hn3⟩ := (hc.and (hε.and (eventually_ge_atTop 3))).exists
  simp only [Function.comp, id] at hn2
  have hx3 : (3:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hxpos : (0:ℝ) < n := by linarith
  have hlg : 2 / 3 ≤ Real.log n := by
    have h1 := Real.one_sub_inv_le_log_of_pos hxpos
    have h2 : (n : ℝ)⁻¹ ≤ 1 / 3 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hx3
    linarith
  have hxl : 1 ≤ (n : ℝ) * Real.log n := by nlinarith
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ((n : ℝ) * Real.log n) ^ ((1 : ℝ) / 3) := ⟨_, rfl⟩
  have ht1 : 1 ≤ t := by rw [ht]; exact Real.one_le_rpow hxl (by norm_num)
  have ht3 : t ^ 3 = (n : ℝ) * Real.log n := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have hh : (subsetSumThreshold n : ℝ) ≤ |c| * t := by
    have h1 := hn1
    simp only [Real.norm_natCast] at h1
    rw [Real.norm_of_nonneg (by positivity), ← ht] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self c) (by linarith))
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (subsetSumThreshold n : ℝ) + 1 := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hyle : y ≤ (|c| + 1) * t := by rw [hy]; nlinarith
  have hy15 : y ^ 15 ≤ (|c| + 1) ^ 15 * ((n : ℝ) * Real.log n) ^ 5 := by
    calc y ^ 15 ≤ ((|c| + 1) * t) ^ 15 := pow_le_pow_left₀ hy0 hyle 15
      _ = (|c| + 1) ^ 15 * (t ^ 3) ^ 5 := by ring
      _ = _ := by rw [ht3]
  have hlowr : ((n : ℝ) - 1) ^ 2 ≤ 921600 * y ^ 5 := by
    have h1 : (((n - 1) ^ 2 : ℕ) : ℝ) ≤
        ((921600 * (subsetSumThreshold n + 1) ^ 5 : ℕ) : ℝ) := by
      exact_mod_cast hlow n
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [Nat.cast_pow, hcast] at h1
    rw [hy]; push_cast at h1; exact h1
  have h6 : ((n : ℝ) / 2) ^ 6 ≤ 921600 ^ 3 * y ^ 15 := by
    calc ((n : ℝ) / 2) ^ 6 = (((n : ℝ) / 2) ^ 2) ^ 3 := by ring
      _ ≤ (((n : ℝ) - 1) ^ 2) ^ 3 := by
          gcongr
          linarith
      _ ≤ (921600 * y ^ 5) ^ 3 := by
          gcongr
      _ = 921600 ^ 3 * y ^ 15 := by ring
  have h7 : (n : ℝ) ^ 6 ≤ C0 * (n : ℝ) ^ 5 * (Real.log n) ^ 5 := by
    calc (n : ℝ) ^ 6 = 64 * ((n : ℝ) / 2) ^ 6 := by ring
      _ ≤ 64 * (921600 ^ 3 * y ^ 15) := by linarith
      _ ≤ 64 * (921600 ^ 3 * ((|c| + 1) ^ 15 * ((n : ℝ) * Real.log n) ^ 5)) := by gcongr
      _ = C0 * (n : ℝ) ^ 5 * (Real.log n) ^ 5 := by rw [hC0]; ring
  have h8 : (n : ℝ) ≤ C0 * (Real.log n) ^ 5 := by
    have hx5 : 0 < (n : ℝ) ^ 5 := by positivity
    have : (n : ℝ) ^ 5 * n ≤ (n : ℝ) ^ 5 * (C0 * (Real.log n) ^ 5) := by
      calc (n : ℝ) ^ 5 * n = (n : ℝ) ^ 6 := by ring
        _ ≤ C0 * (n : ℝ) ^ 5 * (Real.log n) ^ 5 := h7
        _ = (n : ℝ) ^ 5 * (C0 * (Real.log n) ^ 5) := by ring
    exact le_of_mul_le_mul_left this hx5
  have h9 : (Real.log n) ^ 5 ≤ 1 / (2 * C0) * n := by
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at hn2
    exact hn2
  have h10 : C0 * (1 / (2 * C0) * n) = (n : ℝ) / 2 := by field_simp
  have h11 : C0 * (Real.log n) ^ 5 ≤ C0 * (1 / (2 * C0) * n) :=
    mul_le_mul_of_nonneg_left h9 hC0pos.le
  linarith
-- [END_PROOF]