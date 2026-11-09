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

theorem erdos_1095.variants.upper_conjecture : ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧ ∀ᶠ k in atTop, g k ≤ exp (k * (1 + f k)) := sorry