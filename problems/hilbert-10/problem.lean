import Mathlib

set_option maxHeartbeats 4000000

open Polynomial

/-- The polynomial whose adjoined root is denoted by i. -/
noncomputable def gaussianPolynomial (K : Type u) [Ring K] : Polynomial K :=
  X ^ 2 + 1

/--
IsGaussianExtension K L means that L is obtained from K by adjoining
a specified root of X^2 + 1. Thus it is a model of the extension K(i)/K.
-/
abbrev IsGaussianExtension
    (K L : Type u)
    [Field K] [Field L] [Algebra K L] :=
  IsAdjoinRoot L (gaussianPolynomial K)

/--
The cardinal-valued rank of the abelian group of rational points of a
Weierstrass curve over a field.
-/
noncomputable def mordellWeilRank
    {F : Type u} [Field F]
    (E : WeierstrassCurve F) : Cardinal := by
  classical
  exact Module.rank ℤ E.toAffine.Point

/--
Let K be a number field with at least 32 real places, and let L be a
model of K(i). Then there exists an elliptic curve E/K whose rank is
positive and does not grow after base change from K to K(i).
-/
theorem exists_ellipticCurve_rank_stable
    (K L : Type u)
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    (hreal : 32 ≤ NumberField.InfinitePlace.nrRealPlaces K)
    (hKi : IsGaussianExtension K L) :
    ∃ E : WeierstrassCurve K,
      E.IsElliptic ∧
      mordellWeilRank (E.baseChange L) = mordellWeilRank E ∧
      0 < mordellWeilRank E := by
  sorry