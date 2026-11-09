import Mathlib
set_option maxHeartbeats 4000000

namespace Erdos357
open Filter Asymptotics
def HasDistinctSums {ι α : Type*} [Preorder ι] [AddCommMonoid α] (a : ι → α) : Prop :=
  {J : Finset ι | (J : Set ι).OrdConnected}.InjOn (fun J ↦ ∑ x ∈ J, a x)
/-- Let $f(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 < \dotsc < a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : Fin k → ℤ, Set.range a ⊆ Set.Icc 1 n ∧ StrictMono a ∧ HasDistinctSums a}
/-- Let $g(n)$ be the maximal $k$ such that there exist integers $1 \le a_1, \dotsc, a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. -/
noncomputable def g (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : Fin k → ℕ, (Set.range a ⊆ Set.Icc 1 n) ∧ HasDistinctSums a}
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

theorem erdos_357.variants.hegyvari : ∃ (o o' : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧ o' =o[atTop] (1 : ℕ → ℝ) ∧ ∀ᶠ n in atTop, (g n : ℝ) ∈ Set.Icc ((1 / 3 + o n) * n) ((2 / 3 + o' n) * n) := sorry