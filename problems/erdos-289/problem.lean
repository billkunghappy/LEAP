import Mathlib
set_option maxHeartbeats 4000000

/-!
# Erdős Problem 289

*References:*
 - [erdosproblems.com/289](https://www.erdosproblems.com/289)
 - [ErGr80] Erdős, P. and Graham, R., Old and new problems and results in combinatorial
    number theory (1980).
-/

open Filter Finset

namespace Erdos289

/-- Is it true that, for all sufficiently large $k$, there exist finite intervals
$I_1, \dotsc, I_k \subset \mathbb{N}$, distinct, not overlapping or adjacent, with
$|I_i| \geq 2$ for $1 \leq i \leq k$ such that
$$
1 = \sum_{i=1}^k \sum_{n \in I_i} \frac{1}{n}?
$$
Here two intervals are adjacent if their union is again an interval, so any two of the
$I_i$ must be separated by at least one integer.
-/
theorem erdos_289 :
    (∀ᶠ k : ℕ in atTop, ∃ I : Fin k → ℕ × ℕ,
    (∀ i, (I i).1 < (I i).2) ∧
    (∀ i j, i ≠ j → (I i).2 + 1 < (I j).1 ∨ (I j).2 + 1 < (I i).1) ∧
    ∑ i, ∑ n ∈ .Icc (I i).1 (I i).2, (n⁻¹ : ℚ) = 1) := by
  sorry

end Erdos289
