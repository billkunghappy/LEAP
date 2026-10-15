import Mathlib
set_option maxHeartbeats 4000000

/-!
# Erdős Problem 1063

*References:*
 * erdosproblems.com/1063
 * Erdos, P. and Selfridge, J. L., Problem 6447. Amer. Math. Monthly 1983, 710.
 * Guy, Richard K., Unsolved problems in number theory. 2004, Problem B31.
 * Monier, Jean-Marie, Problems and Solutions: Solutions of Advanced Problems: 6447.
   Amer. Math. Monthly 92, 1985, 435-436.
-/

open Filter Real
open scoped Nat Topology

namespace Erdos1063

/--
Let $n_k$ be the least $n \ge 2k$ such that all but one of the integers $n - i$ with
$0 \le i < k$ divide $\binom{n}{k}$.
-/
noncomputable def n (k : ℕ) : ℕ :=
  sInf {m | 2 * k ≤ m ∧ ∃ i0 < k, ¬ (m - i0) ∣ m.choose k ∧
    ∀ i < k, i ≠ i0 → (m - i) ∣ m.choose k}

/-- The initial values satisfy $n_2 = 4$, $n_3 = 6$, $n_4 = 9$, and $n_5 = 12$. -/
theorem erdos_1063.variants.small_values :
    n 2 = 4 ∧ n 3 = 6 ∧ n 4 = 9 ∧ n 5 = 12 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply le_antisymm
    · exact Nat.sInf_le (by decide)
    · apply le_csInf ⟨4, by decide⟩
      rintro b hb
      have : 2 * 2 ≤ b := hb.1
      omega
  · apply le_antisymm
    · exact Nat.sInf_le (by decide)
    · apply le_csInf ⟨6, by decide⟩
      rintro b hb
      have : 2 * 3 ≤ b := hb.1
      omega
  · apply le_antisymm
    · exact Nat.sInf_le (by decide)
    · apply le_csInf ⟨9, by decide⟩
      rintro b hb
      have hb8 : 8 ≤ b := by have := hb.1; omega
      by_contra! h
      interval_cases b
      · exact absurd hb (by decide)
  · apply le_antisymm
    · exact Nat.sInf_le (by decide)
    · apply le_csInf ⟨12, by decide⟩
      rintro b hb
      have hb10 : 10 ≤ b := by have := hb.1; omega
      by_contra! h
      interval_cases b
      · exact absurd hb (by decide)
      · exact absurd hb (by decide)

/--
Combined statement of Erdős Problem 1063 (`erdos_1063.better_upper`) and its four companion
theorems (`exists_exception`, `monier_upper_bound`, `cambie_upper_bound`, `exp_upper_bound`).
-/
theorem erdos_1063_all :
    (let upper_bound : ℕ → ℝ := fun k =>
      Real.exp ((k : ℝ) / Real.log k *
        (Real.log (Real.log k) + Real.log (Real.log (Real.log k)) + Real.log 2))
    (fun k => (n k : ℝ)) =O[atTop] upper_bound ∧
    upper_bound =o[atTop] fun k =>
      (k : ℝ) * (((Finset.Icc 1 (k - 1)).lcm id : ℕ) : ℝ)) ∧
    (∀ {n_val k : ℕ}, 2 ≤ k → 2 * k ≤ n_val → ∃ i < k, ¬ (n_val - i) ∣ n_val.choose k) ∧
    (∀ {k : ℕ}, 3 ≤ k → n k ≤ k !) ∧
    (∀ {k : ℕ}, 3 ≤ k → n k ≤ k * (Finset.Icc 1 (k - 1)).lcm id) ∧
    (∃ f : ℕ → ℝ, Tendsto f atTop (nhds 0) ∧
      ∀ k, (n k : ℝ) ≤ exp ((1 + f k) * k)) := by
  sorry

end Erdos1063
