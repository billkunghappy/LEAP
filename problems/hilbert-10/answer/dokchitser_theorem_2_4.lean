import Mathlib
import Hilbert10Defs

/-! ### Statement (originally `dokchitser_theorem_2_4.lean`) -/

/--
**Dokchitser–Dokchitser, Theorem 2.4, case `p = 2`** (T. & V. Dokchitser, *Root numbers and
parity of ranks of elliptic curves*, J. reine angew. Math. 658 (2011), Theorem 2.4 = Theorem 1.7;
informal source `dokchitser_informal.md`, §2). Let `K` be a totally real number field and `E/K`
an elliptic curve with non-integral `j`-invariant. Then the `2`-parity conjecture holds for
`E/K`: `(-1)^{rk₂ E/K} = w(E/K)`, where `rk₂ E/K` is the `2^∞`-Selmer rank and `w(E/K)` the
global root number.

**Formal rendering in the language of Corollary 3.6.** The vocabulary shared with
`corollary_3_6.lean` has the `2`-Selmer group `twoSelmerSet` (for curves with full
rational `2`-torsion) and the genuine global root number `globalRootNumber`, but no
`2^∞`-Selmer rank. The statement is therefore made for the curves this vocabulary covers, with
`rk₂` expressed through the `2`-Selmer group:

* *Curves.* `E = threeRootsCurve e₁ e₂ e₃ : y² = (x - e₁)(x - e₂)(x - e₃)` with
  `e₁, e₂, e₃ ∈ K` distinct, i.e. an elliptic curve with `E(K)[2] ≅ 𝔽₂²`. (In characteristic
  `0`, every elliptic curve over `K` with full rational `2`-torsion is `K`-isomorphic to such a
  model, and the root number is an isomorphism invariant.)
* *Totally real.* `[NumberField.IsTotallyReal K]`: every infinite place of `K` is real.
* *Non-integral `j`-invariant.* `j(E) = c₄³ / Δ ∉ 𝓞_K`, where
  `Δ = 16 ((e₁ - e₂)(e₁ - e₃)(e₂ - e₃))² ≠ 0`. It is stated (equivalently, by
  `IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one`) as: there is a finite
  place `v` of `K` with `|j(E)|_v > 1`, i.e. `ord_v j(E) < 0`, which is the form used in the
  proof of Theorem 2.4 ("let `𝔭` be a prime of `K` with `ord_𝔭 j(E) < 0`").
* *`2`-parity.* `(-1)^{rk₂ E/K}` is expressed as `(-1)^{dim_{𝔽₂} Sel²(E/K)}`, with
  `#Sel²(E/K) = 2^d`. These agree: from `0 → E(K)/2 → Sel²(E/K) → Ш(E/K)[2] → 0`,
  `dim_{𝔽₂} Sel²(E/K) = rk₂ E/K + dim_{𝔽₂} E(K)[2] + 2t`, the term `2t` coming from the
  non-divisible part of `Ш(E/K)[2^∞]`, which has square order by the Cassels–Tate pairing; and
  `dim_{𝔽₂} E(K)[2] = 2` here (cf. Dokchitser–Dokchitser, Remark 4.9, (c) ⇔ (d)).

So the statement below is exactly Theorem 2.4 for `p = 2`, restricted to the curves with full
rational `2`-torsion, with `rk₂` read through the `2`-Selmer group. Its conclusion is, word for
word, the conclusion of `corollary_3_6`; it adds the two hypotheses "`K` totally real"
and "`j(E)` non-integral".
-/
theorem dokchitser_theorem_2_4 {K : Type u} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]
    (e₁ e₂ e₃ : K) (h₁₂ : e₁ ≠ e₂) (h₁₃ : e₁ ≠ e₃) (h₂₃ : e₂ ≠ e₃)
    (hj : ∃ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      1 < IsDedekindDomain.HeightOneSpectrum.valuation K v
        ((threeRootsCurve e₁ e₂ e₃).c₄ ^ 3 / (threeRootsCurve e₁ e₂ e₃).Δ)) :
    ∃ d : ℕ, (twoSelmerSet K e₁ e₂ e₃).encard = 2 ^ d ∧
      (-1 : ℤˣ) ^ d = globalRootNumber (threeRootsCurve e₁ e₂ e₃) := by
  sorry
