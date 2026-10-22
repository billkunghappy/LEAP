import Mathlib
import RootNumberDefs
set_option maxHeartbeats 4000000

/-! ## §11 Shared definitions of the Hilbert 10 assumptions (originally `Hilbert10Defs.lean`) -/

/--
The Weierstrass curve `y^2 = (x - e₁)(x - e₂)(x - e₃)` with three prescribed
roots `e₁, e₂, e₃`, written in long Weierstrass form.
-/
def threeRootsCurve {F : Type*} [Field F] (e₁ e₂ e₃ : F) : WeierstrassCurve F where
  a₁ := 0
  a₂ := -(e₁ + e₂ + e₃)
  a₃ := 0
  a₄ := e₁ * e₂ + e₁ * e₃ + e₂ * e₃
  a₆ := -(e₁ * e₂ * e₃)

/--
The group `Fˣ / Fˣ²` of square classes of a field `F`.
-/
abbrev SqCl (F : Type*) [Field F] := Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range

/--
The square class of a unit `u : Fˣ` in `SqCl F`.
-/
def sqCl {F : Type*} [Field F] (u : Fˣ) : SqCl F := QuotientGroup.mk u

/--
`IsDescentClass e₁ e₂ e₃ d₁ d₂` says that the pair of quadrics attached to
`(d₁, d₂)` in the 2-descent for `y^2 = (x - e₁)(x - e₂)(x - e₃)` has a nontrivial
common solution, i.e. `(d₁, d₂)` lies in the image of the local Kummer map.
-/
def IsDescentClass {F : Type*} [Field F] (e₁ e₂ e₃ d₁ d₂ : F) : Prop :=
  ∃ z₀ z₁ z₂ z₃ : F,
    ¬ (z₀ = 0 ∧ z₁ = 0 ∧ z₂ = 0 ∧ z₃ = 0) ∧
    d₁ * z₁ ^ 2 - d₂ * z₂ ^ 2 = (e₂ - e₁) * z₀ ^ 2 ∧
    d₁ * z₁ ^ 2 - d₁ * d₂ * z₃ ^ 2 = (e₃ - e₁) * z₀ ^ 2

/--
The 2-Selmer set of `y^2 = (x - e₁)(x - e₂)(x - e₃)` over a number field `K`,
realised inside `SqCl K × SqCl K`: the classes that are everywhere locally in the
image of the Kummer map (at all finite and all infinite places).
-/
def twoSelmerSet (K : Type u) [Field K] [NumberField K] (e₁ e₂ e₃ : K) :
    Set (SqCl K × SqCl K) :=
  (fun p : Kˣ × Kˣ => (sqCl p.1, sqCl p.2)) ''
    { p : Kˣ × Kˣ |
      (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          IsDescentClass
            (algebraMap K (v.adicCompletion K) e₁)
            (algebraMap K (v.adicCompletion K) e₂)
            (algebraMap K (v.adicCompletion K) e₃)
            (algebraMap K (v.adicCompletion K) (p.1 : K))
            (algebraMap K (v.adicCompletion K) (p.2 : K))) ∧
      (∀ w : NumberField.InfinitePlace K,
          IsDescentClass
            (algebraMap K w.Completion e₁)
            (algebraMap K w.Completion e₂)
            (algebraMap K w.Completion e₃)
            (algebraMap K w.Completion (p.1 : K))
            (algebraMap K w.Completion (p.2 : K))) }

/--
`EvenVal v x` says that the `v`-adic valuation of the unit `x : Kˣ` is even.
-/
def EvenVal {K : Type u} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (x : Kˣ) : Prop :=
  Even (Multiplicative.toAdd (v.valuationOfNeZero x))

/--
`IsGoodT a₁ a₂ a₃ T` says that the finite set `T` of primes of `K` is exactly the set
of primes at which `6 (a₁ - a₂)(a₁ - a₃)(a₂ - a₃)` fails to be a unit.
-/
def IsGoodT {K : Type u} [Field K] [NumberField K] (a₁ a₂ a₃ : K)
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) : Prop :=
  ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
    v ∈ T ↔
      (IsDedekindDomain.HeightOneSpectrum.valuation K v)
        (6 * (a₁ - a₂) * (a₁ - a₃) * (a₂ - a₃)) ≠ 1

/--
`IsLocalUnif v π` says that `π ∈ K_v` has odd valuation (so that it can play the role
of a local uniformiser up to squares).
-/
def IsLocalUnif {K : Type u} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (π : v.adicCompletion K) : Prop :=
  ∃ n : ℤ, Odd n ∧ Valued.v π = ((Multiplicative.ofAdd n : Multiplicative ℤ) :
      WithZero (Multiplicative ℤ))

/--
The ramified local condition at a prime `v ∈ S` with local parameter `π`: the pair
`(x₁, x₂)` lies in one of the four square classes cut out by the images of the
2-torsion points of the twisted curve.
-/
def RamLocal {K : Type u} [Field K] [NumberField K] (a₁ a₂ a₃ : K)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (π : v.adicCompletion K) (x₁ x₂ : Kˣ) : Prop :=
  ( IsSquare (algebraMap K (v.adicCompletion K) (x₁ : K)) ∧
    IsSquare (algebraMap K (v.adicCompletion K) (x₂ : K)) ) ∨
  ( IsSquare (algebraMap K (v.adicCompletion K) ((x₁ : K) * (a₁ - a₂) * (a₁ - a₃))) ∧
    IsSquare (π * algebraMap K (v.adicCompletion K) ((x₂ : K) * (a₁ - a₂))) ) ∨
  ( IsSquare (-(π * algebraMap K (v.adicCompletion K) ((x₁ : K) * (a₁ - a₂)))) ∧
    IsSquare (algebraMap K (v.adicCompletion K) (-((x₂ : K) * (a₁ - a₂) * (a₂ - a₃)))) ) ∨
  ( IsSquare (-(π * algebraMap K (v.adicCompletion K) ((x₁ : K) * (a₁ - a₃)))) ∧
    IsSquare (-(π * algebraMap K (v.adicCompletion K) ((x₂ : K) * (a₂ - a₃)))) )

/-! `CurveClass`, `rootNumberCl`, `rootNumber` and `globalRootNumber` are defined in
`RootNumberDefs.lean` (imported above). -/

/--
The Hilbert symbol `(a, b)_v ∈ {±1}` on the completion `K_v` at a finite place `v`:
it is `1` iff `a x^2 + b y^2 = 1` has a solution.
-/
noncomputable def hilbLoc {K : Type u} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (a b : v.adicCompletion K) : ℤˣ := by
  classical
  exact if (∃ x y : v.adicCompletion K, a * x ^ 2 + b * y ^ 2 = 1) then 1 else -1

/--
The Hilbert symbol `(a, b)_w ∈ {±1}` on the completion `K_w` at an infinite place `w`:
it is `1` iff `a x^2 + b y^2 = 1` has a solution.
-/
noncomputable def hilbInfLoc {K : Type u} [Field K] [NumberField K]
    (w : NumberField.InfinitePlace K) (a b : w.Completion) : ℤˣ := by
  classical
  exact if (∃ x y : w.Completion, a * x ^ 2 + b * y ^ 2 = 1) then 1 else -1

/--
The Hilbert symbol `(a, b)_v` of two elements `a, b ∈ K` at a finite place `v`.
-/
noncomputable def hilbFin {K : Type u} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (a b : K) : ℤˣ :=
  hilbLoc v (algebraMap K (v.adicCompletion K) a) (algebraMap K (v.adicCompletion K) b)

/--
The Hilbert symbol `(a, b)_w` of two elements `a, b ∈ K` at an infinite place `w`.
-/
noncomputable def hilbInf {K : Type u} [Field K] [NumberField K]
    (w : NumberField.InfinitePlace K) (a b : K) : ℤˣ :=
  hilbInfLoc w (algebraMap K w.Completion a) (algebraMap K w.Completion b)

/--
The Selmer group attached to the Selmer structure `(T, S, π)`, relaxed at the single
prime `v₀` (no condition is imposed at `v₀`), realised inside `SqCl K × SqCl K`.
-/
def selmerStructRelax (K : Type u) [Field K] [NumberField K] (a₁ a₂ a₃ : K)
    (T S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (π : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        v.adicCompletion K)
    (v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Set (SqCl K × SqCl K) :=
  (fun p : Kˣ × Kˣ => (sqCl p.1, sqCl p.2)) ''
    { p : Kˣ × Kˣ |
      (∀ v ∈ T, IsDescentClass
            (algebraMap K (v.adicCompletion K) a₁)
            (algebraMap K (v.adicCompletion K) a₂)
            (algebraMap K (v.adicCompletion K) a₃)
            (algebraMap K (v.adicCompletion K) (p.1 : K))
            (algebraMap K (v.adicCompletion K) (p.2 : K))) ∧
      (∀ w : NumberField.InfinitePlace K, IsDescentClass
            (algebraMap K w.Completion a₁)
            (algebraMap K w.Completion a₂)
            (algebraMap K w.Completion a₃)
            (algebraMap K w.Completion (p.1 : K))
            (algebraMap K w.Completion (p.2 : K))) ∧
      (∀ v ∈ S, RamLocal a₁ a₂ a₃ v (π v) p.1 p.2) ∧
      (∀ v, v ∉ T → v ∉ S → v ≠ v₀ → EvenVal v p.1 ∧ EvenVal v p.2) }

/--
The Frobenius class `Frob_𝔭 ⊆ Gal(L/K)`: the set of `g` for which there is a prime
`Q` of `L` above `𝔭` with `g x ≡ x ^ N(𝔭) (mod Q)` for all `x ∈ 𝓞_L`.
-/
def FrobeniusClassAt (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Set (L ≃ₐ[K] L) :=
  { g | ∃ Q : Ideal (NumberField.RingOfIntegers L), Q.IsPrime ∧
      Ideal.under (NumberField.RingOfIntegers K) Q = p.asIdeal ∧
      ∀ x z : NumberField.RingOfIntegers L, (z : L) = g ((x : L)) →
        z - x ^ (Nat.card (NumberField.RingOfIntegers K ⧸ p.asIdeal)) ∈ Q }

/--
`IsUnramifiedAtPrime K L 𝔭` says that the prime `𝔭` of `K` is unramified in `L`,
i.e. every prime of `L` above `𝔭` has ramification index `1`.
-/
def IsUnramifiedAtPrime (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) : Prop :=
  ∀ Q : Ideal (NumberField.RingOfIntegers L), Q.IsPrime →
    Ideal.under (NumberField.RingOfIntegers K) Q = p.asIdeal →
      Ideal.ramificationIdx
        (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L))
        p.asIdeal Q = 1

/--
The quotient `(∑_{𝔭 ∈ S} N(𝔭)^{-s}) / log (1/(s - 1))` whose limit as `s → 1⁺`
is the Dirichlet density of the set `S` of primes.
-/
noncomputable def dirichletQuot {K : Type u} [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (s : ℝ) : ENNReal :=
  (∑' p : S, ENNReal.ofReal
      ((Nat.card (NumberField.RingOfIntegers K ⧸
          (p : IsDedekindDomain.HeightOneSpectrum
            (NumberField.RingOfIntegers K)).asIdeal) : ℝ) ^ (-s)))
    / ENNReal.ofReal (Real.log (1 / (s - 1)))

/--
`HasDirichletDensity S d` says that the set `S` of primes of `K` has Dirichlet
density `d`.
-/
def HasDirichletDensity {K : Type u} [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (d : ℝ) : Prop :=
  Filter.Tendsto (dirichletQuot S) (nhdsWithin (1 : ℝ) (Set.Ioi 1))
    (nhds (ENNReal.ofReal d))

/--
The canonical norm `‖x‖ = max_w |x|_w` of `x ∈ K`, the maximum over all infinite
places.
-/
noncomputable def canNorm (K : Type u) [Field K] [NumberField K] (x : K) : ℝ :=
  ⨆ w : NumberField.InfinitePlace K, w x

/--
The sup-norm of the coordinate vector of `x ∈ 𝓞_K` with respect to the `ℤ`-basis `ω`.
-/
noncomputable def basisSupNorm {K : Type u} [Field K] [NumberField K] {ν : ℕ}
    (ω : Module.Basis (Fin ν) ℤ (NumberField.RingOfIntegers K))
    (x : NumberField.RingOfIntegers K) : ℝ :=
  ⨆ j : Fin ν, |((ω.repr x j : ℤ) : ℝ)|

/--
`IsNormLengthCompatible C ω` says that the `ℤ`-basis `ω` of `𝓞_K` is
`C`-norm-length compatible: `C⁻¹ ‖x‖_ω ≤ ‖x‖ ≤ C ‖x‖_ω` for all `x ∈ 𝓞_K`.
-/
def IsNormLengthCompatible {K : Type u} [Field K] [NumberField K] {ν : ℕ}
    (C : ℝ) (ω : Module.Basis (Fin ν) ℤ (NumberField.RingOfIntegers K)) : Prop :=
  1 < C ∧ ∀ x : NumberField.RingOfIntegers K,
    C⁻¹ * basisSupNorm ω x
        ≤ canNorm K (algebraMap (NumberField.RingOfIntegers K) K x) ∧
    canNorm K (algebraMap (NumberField.RingOfIntegers K) K x)
        ≤ C * basisSupNorm ω x

/--
Evaluation `c₀ + ∑ z_k c_k` of the affine linear form with constant term `c₀` and
linear coefficients `c` at `z ∈ ℤ^d`.
-/
def affEval {K : Type u} [Field K] [NumberField K] {d : ℕ}
    (c₀ : NumberField.RingOfIntegers K) (c : Fin d → NumberField.RingOfIntegers K)
    (z : Fin d → ℤ) : NumberField.RingOfIntegers K :=
  c₀ + ∑ k, z k • c k

/--
The homogeneous part `ψ^hom : ℤ^d → 𝓞_K`, `z ↦ ∑ z_k c_k`, of an affine linear form
with linear coefficients `c`.
-/
def homMap {K : Type u} [Field K] [NumberField K] {d : ℕ}
    (c : Fin d → NumberField.RingOfIntegers K) :
    (Fin d → ℤ) →ₗ[ℤ] NumberField.RingOfIntegers K where
  toFun z := ∑ k, z k • c k
  map_add' := by intro z z'; simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by intro m z; simp [mul_smul, Finset.smul_sum]

/--
The norm `‖ψ‖_N = max(‖c₀‖_ω / N, max_k ‖c_k‖_ω)` of an affine linear form at scale `N`.
-/
noncomputable def kaiFormNorm {K : Type u} [Field K] [NumberField K] {ν d : ℕ}
    (ω : Module.Basis (Fin ν) ℤ (NumberField.RingOfIntegers K))
    (c₀ : NumberField.RingOfIntegers K) (c : Fin d → NumberField.RingOfIntegers K)
    (N : ℝ) : ℝ :=
  max (basisSupNorm ω c₀ / N) (⨆ k : Fin d, basisSupNorm ω (c k))

open scoped Classical in
/--
The von Mangoldt function on `𝓞_K`: `Λ(x) = log N(𝔭)` if `(x) = 𝔭^m` is a prime power
with `m ≥ 1`, and `0` otherwise.
-/
noncomputable def vonMangoldtO {K : Type u} [Field K] [NumberField K]
    (x : NumberField.RingOfIntegers K) : ℝ :=
  if h : ∃ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      ∃ m : ℕ, 0 < m ∧ Ideal.span {x} = p.asIdeal ^ m
  then Real.log (Ideal.absNorm h.choose.asIdeal) else 0

/--
`KaiLocalSolvable c₀ c` says that for every rational prime `p` there is `z ∈ ℤ^d` at
which none of the four affine linear forms lies in any prime of `𝓞_K` above `p`
(i.e. the local factors `β_p` are nonzero).
-/
def KaiLocalSolvable {K : Type u} [Field K] [NumberField K] {d : ℕ}
    (c₀ : Fin 4 → NumberField.RingOfIntegers K)
    (c : Fin 4 → Fin d → NumberField.RingOfIntegers K) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ z : Fin d → ℤ, ∀ i : Fin 4,
    ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (p : NumberField.RingOfIntegers K) ∈ 𝔭.asIdeal →
        affEval (c₀ i) (c i) z ∉ 𝔭.asIdeal

/--
The integer box `[-M, M]^d ⊆ ℤ^d`.
-/
def intBox (d : ℕ) (M : ℕ) : Finset (Fin d → ℤ) :=
  Finset.Icc (fun _ => -(M : ℤ)) (fun _ => (M : ℤ))

/--
The real box `[-N, N]^d ⊆ ℝ^d`.
-/
def realBox (d : ℕ) (N : ℝ) : Set (Fin d → ℝ) := {z | ∀ k, |z k| ≤ N}

open scoped Classical in
/--
The sum `∑_{z ∈ Ω ∩ ℤ^d} ∏_{i=1}^{4} Λ(ψ_i(z))` (truncated to the box `[-M, M]^d`) of
the product of the four von Mangoldt weights over the convex region `Ω`.
-/
noncomputable def kaiSum {K : Type u} [Field K] [NumberField K] {d : ℕ}
    (c₀ : Fin 4 → NumberField.RingOfIntegers K)
    (c : Fin 4 → Fin d → NumberField.RingOfIntegers K)
    (Ω : Set (Fin d → ℝ)) (M : ℕ) : ℝ :=
  ∑ z ∈ intBox d M,
    if (fun k => ((z k : ℤ) : ℝ)) ∈ Ω
    then ∏ i : Fin 4, vonMangoldtO (affEval (c₀ i) (c i) z) else 0

