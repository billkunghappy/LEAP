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

theorem erdos_394.variants.hall_conjecture : ∀ c < Real.log 2, (fun x ↦ ∑ n ∈ Icc 1 ⌊x⌋₊, (t 2 n : ℝ)) =o[atTop] (fun x ↦ x ^ 2 / (Real.log x) ^ c) := sorry