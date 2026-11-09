import Mathlib
set_option maxHeartbeats 4000000

open Nat Filter
namespace Erdos1101
/-- The set of integers not divisible by any u_i. -/
def ASet (u : ℕ → ℕ) : Set ℕ :=
  { a | ∀ i, ¬ u i ∣ a }
/-- The sequence of integers A_u which are not divisible by any u_i
arranged in a monotonic sequence. -/
noncomputable def A (u : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.nth (fun a => a ∈ ASet u) n
/-- t_x such that u_0 ... u_{t_x-1} ≤ x < u_0 ... u_{t_x}.
-/
noncomputable def t (u : ℕ → ℕ) (x : ℕ) : ℕ :=
  sSup { k | ∏ i ∈ Finset.range k, u i ≤ x }
/-- A sequence is "good" if
1. it is strictly monotone
2. it is pairwise coprime
3. the sum of reciprocals converges
4. the gap between consecutive elements in A(u) is bounded relative to t_x. -/
def IsGood (u : ℕ → ℕ) : Prop :=
  StrictMono u ∧
  (∀ i j, i ≠ j → Coprime (u i) (u j)) ∧
  Summable (fun n => 1 / (u n : ℝ)) ∧
  ∀ ε > 0, ∀ᶠ x in atTop,
    ∀ k, A u k < x →
      (A u (k + 1) : ℝ) - A u k < (1 + ε) * (t u x : ℝ) * (∏' i : ℕ, (1 - 1 / (u i : ℝ)))⁻¹
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

theorem erdos_1101.parts.ii : ∃ u, IsGood u ∧ (fun n => Real.log (u n : ℝ)) =o[atTop] (fun n => (n : ℝ)) := sorry