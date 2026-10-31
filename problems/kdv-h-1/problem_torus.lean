import Mathlib
import KdVLine
set_option maxHeartbeats 4000000

/-!
# KdV is well-posed in `H⁻¹(ℝ/ℤ)` (Killip–Vişan, Theorem 1.1, circle case)

Formal statement of the circle (periodic) case of

> **Theorem 1.1 (Global well-posedness).** The equation (KdV)
> `d/dt q = -q''' + 6 q q'` is globally well-posed for initial data in `H⁻¹(ℝ/ℤ)` in the
> following sense: the solution map extends uniquely from Schwartz space to a jointly
> continuous map `Φ : ℝ × H⁻¹ → H⁻¹`. Moreover, for each initial data `q ∈ H⁻¹`, the orbit
> `{Φ(t,q) : t ∈ ℝ}` is uniformly bounded and equicontinuous in `H⁻¹`.

The paper treats this case in §6 ("The periodic case"). There it says that Sections 3–5 carry
over once Section 2 (the diagonal Green's function) has been redone, and once the lack of
scaling symmetry has been handled by the coupled condition (6.1)
`κ ≥ 1, κ^{-1/2} ‖q‖_{H⁻¹(ℝ/ℤ)} ≤ δ`.

R. Killip and M. Vişan, *KdV is well-posed in `H⁻¹`*, Ann. of Math. (2) **190** (2019),
249–305, arXiv:1802.04851. The informal source is `KdV_killip_visan_informal.md` in this
folder. This file is the circle analogue of `KdV_well_posed.lean`, the line case.

## Layout of this file

* **Part I: line-case results, imported.** `import KdVLine` brings in the complete, verified
  proof of the line case (`KdV_well_posed_final_proof.lean`, built as the module `KdVLine`):
  every definition of `KdV_well_posed.lean`, the auxiliary definitions (`GreenODE`, …, `RegN`)
  and all 115 theorems, including `KdV.kdv_well_posed_H_minus_one`, in namespace `KdV`. They
  are *proved* there, not assumed, so they may be used freely and add no axioms beyond
  `propext`, `Classical.choice`, `Quot.sound`. Only `kdvRHS` appears in the torus statement.
  (This replaces the earlier verbatim copy of the line-case definitions.)

* **Part II: the circle `ℝ/ℤ`.** These are the torus definitions and the main theorem. All
  torus names end in `T` (or are `fourierCircle`), so they cannot be confused with the line
  names of Part I.

## Notion of solution on the circle (as in the paper)

* **Schwartz space on `ℝ/ℤ`.** As the paper says, "On the circle `ℝ/ℤ`, Schwartz space is
  coincident with `C^∞(ℝ/ℤ)`". We realise `C^∞(ℝ/ℤ)` as the set `CinfT` of smooth,
  1-periodic, real-valued functions on `ℝ`.

* **Smooth solutions.** A *smooth solution* is a curve `u : ℝ → C^∞(ℝ/ℤ)` such that
  `(t, x) ↦ u(t)(x)` is jointly `C^∞` on `ℝ × ℝ`, and `∂ₜ u(t,x) = -∂ₓ³u(t,x) + 6 u ∂ₓu` holds at
  every point. The circle is compact, so joint smoothness on `ℝ × ℝ/ℤ` is the same as `u`
  being a `C^∞` curve in the Fréchet space `C^∞(ℝ/ℤ)`. This is the same notion as "curve in
  Schwartz space" in the line file. Mathlib has no Fréchet-space type for `C^∞(ℝ/ℤ)`, so
  joint smoothness is the cleanest faithful encoding.

* **`H⁻¹` solutions** are unique limits of smooth solutions, exactly as in the line case.

* **Classical input is assumed, not proved (conditional statement).** As on the line, the
  paper takes classical well-posedness of (KdV) for smooth periodic data for granted
  (Bona–Smith, Kato, Sjöberg, Temam; Bourgain covers even `L²(ℝ/ℤ)`). The main theorem
  therefore takes global existence (`h_exists`) and uniqueness (`h_unique`) of smooth
  solutions as *hypotheses*. Both are true classical theorems, so the statement is not
  vacuous. They are deliberately theorem hypotheses rather than `axiom`s. As on the line,
  smooth dependence on the data is *not* assumed.

## How `H⁻¹(ℝ/ℤ)` and equicontinuity are encoded

* **Fourier convention (paper §1.2).** `q̂(ξ) = ∫₀¹ e^{-iξx} q(x) dx` for `ξ ∈ 2πℤ`. We index
  by `n ∈ ℤ`, with `ξ = 2πn`.

* **The space.** The paper's norm is `‖q‖²_{H⁻¹(ℝ/ℤ)} = ∑_{ξ ∈ 2πℤ} (4 + ξ²)⁻¹ |q̂(ξ)|²`, so
  `q ↦ (n ↦ (4 + (2πn)²)^{-1/2} q̂(2πn))` is a linear isometry from real `H⁻¹(ℝ/ℤ)` into
  `ℓ²(ℤ; ℂ)`. We realise `H⁻¹(ℝ/ℤ)` as the closure of the image of `C^∞(ℝ/ℤ)` under this
  isometry. Smooth functions are dense, so this is isometrically isomorphic to the paper's
  `H⁻¹(ℝ/ℤ)`, and it is literally the completion of `C^∞(ℝ/ℤ)` in the `H⁻¹` norm.

* **Equicontinuity (paper Definition 4.1, (4.1)).** Translation by `h` multiplies `q̂(ξ)` by
  `e^{iξh}`. So, for the profile `f` of `q`,
  `‖q(· + h) - q‖²_{H⁻¹} = ∑ₙ |e^{2πinh} - 1|² |f(n)|²`. This is (4.1) on the circle.

* **Junk value.** The embedding is defined with a `dite` on `Memℓp`, returning `0` otherwise.
  For smooth periodic inputs the membership always holds.

Remark: the circle is compact, so bounded + equicontinuous orbits are exactly precompact
orbits (paper, after Theorem 1.1). We state Theorem 1.1 as written, with bounded +
equicontinuous.
-/

open MeasureTheory Complex
open scoped Real SchwartzMap Classical

noncomputable section

namespace KdV

/-! # Part I. Line-case results

Imported from `KdVLine` (see the module docstring). Nothing to declare here. -/

/-! # Part II. The circle `ℝ/ℤ`

## The phase space `C^∞(ℝ/ℤ)` and smooth solutions -/

open scoped ContDiff in
/-- `C^∞(ℝ/ℤ)`, the paper's "Schwartz space" on the circle, realised as the smooth 1-periodic
real-valued functions on `ℝ`. -/
def CinfT : Set (ℝ → ℝ) :=
  {f | ContDiff ℝ ∞ f ∧ Function.Periodic f 1}

open scoped ContDiff in
/-- A global smooth solution of (KdV) on the circle: a curve `u : ℝ → C^∞(ℝ/ℤ)` such that
`(t, x) ↦ u(t)(x)` is jointly `C^∞` on `ℝ × ℝ` (equivalently, since `ℝ/ℤ` is compact, `u` is
a `C^∞` curve in the Fréchet space `C^∞(ℝ/ℤ)`). It must satisfy
`∂ₜ u(t,x) = -∂ₓ³u(t,x) + 6 u(t,x) ∂ₓu(t,x)` at every `(t, x)`. -/
def IsSmoothSolutionT (u : ℝ → CinfT) : Prop :=
  ContDiff ℝ ∞ (fun p : ℝ × ℝ => (u p.1 : ℝ → ℝ) p.2) ∧
    ∀ t x : ℝ, HasDerivAt (fun s : ℝ => (u s : ℝ → ℝ) x) (kdvRHS (u t : ℝ → ℝ) x) t

/-! ## The space `H⁻¹(ℝ/ℤ)` -/

/-- The Fourier coefficient on the circle with the paper's normalisation
`q̂(ξ) = ∫₀¹ e^{-iξx} q(x) dx`, evaluated at `ξ = 2πn`. -/
def fourierCircle (q : ℝ → ℝ) (n : ℤ) : ℂ :=
  ∫ x in (0 : ℝ)..1, Complex.exp (-(((2 * π * n : ℝ) : ℂ) * (x : ℂ)) * I) * (q x : ℂ)

/-- The `H⁻¹(ℝ/ℤ)` profile `n ↦ (4 + (2πn)²)^{-1/2} q̂(2πn)`. Its `ℓ²(ℤ)` norm is
`‖q‖_{H⁻¹(ℝ/ℤ)}`. -/
def hm1ProfileT (q : ℝ → ℝ) (n : ℤ) : ℂ :=
  ((Real.sqrt (4 + (2 * π * n) ^ 2))⁻¹ : ℂ) * fourierCircle q n

/-- The isometric embedding of a smooth periodic function into `ℓ²(ℤ; ℂ)` via its `H⁻¹`
profile (junk value `0` if the profile were not square summable, which never happens). -/
def toHm1T (q : CinfT) : lp (fun _ : ℤ => ℂ) 2 :=
  if h : Memℓp (hm1ProfileT (q : ℝ → ℝ)) 2 then ⟨hm1ProfileT (q : ℝ → ℝ), h⟩ else 0

/-- Real `H⁻¹(ℝ/ℤ)`, realised (isometrically) as the closure in `ℓ²(ℤ; ℂ)` of the `H⁻¹`
profiles of real smooth 1-periodic functions, i.e. the completion of `C^∞(ℝ/ℤ)` in the `H⁻¹`
norm. -/
def Hm1T : Submodule ℝ (lp (fun _ : ℤ => ℂ) 2) :=
  (Submodule.span ℝ (Set.range toHm1T)).topologicalClosure

/-- The embedding `C^∞(ℝ/ℤ) → H⁻¹(ℝ/ℤ)`. -/
def ιT (q : CinfT) : Hm1T :=
  ⟨toHm1T q, Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨q, rfl⟩)⟩

/-! ## Equicontinuity and the extension property -/

/-- `‖q(· + h) - q‖²_{H⁻¹(ℝ/ℤ)}` expressed through the `H⁻¹` profile `f` of `q`:
`∑ₙ |e^{2πinh} - 1|² |f(n)|²`. -/
def translateDiffSqT (f : lp (fun _ : ℤ => ℂ) 2) (h : ℝ) : ℝ :=
  ∑' n : ℤ, ‖(Complex.exp (((2 * π * n : ℝ) : ℂ) * (h : ℂ) * I) - 1) * f n‖ ^ 2

/-- Equicontinuity in `H⁻¹(ℝ/ℤ)` (paper Definition 4.1): `q(· + h) → q` in `H⁻¹` as
`h → 0`, uniformly for `q ∈ Q`. -/
def EquicontinuousHm1T (Q : Set Hm1T) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ q ∈ Q, ∀ h : ℝ, |h| < δ →
    translateDiffSqT (q : lp (fun _ : ℤ => ℂ) 2) h < ε

/-- `Φ` extends the smooth solution map: for every smooth solution `u`,
`Φ(t, u(0)) = u(t)` in `H⁻¹(ℝ/ℤ)` for all `t`. -/
def ExtendsSmoothFlowT (Φ : ℝ × Hm1T → Hm1T) : Prop :=
  ∀ u : ℝ → CinfT, IsSmoothSolutionT u → ∀ t : ℝ, Φ (t, ιT (u 0)) = ιT (u t)

/-! ## Main theorem -/

/-- **Killip–Vişan, Theorem 1.1 (circle case).** KdV is globally well-posed in `H⁻¹(ℝ/ℤ)`.
Assume the classical theory for smooth periodic data, which the paper takes for granted:
global existence `h_exists` and uniqueness `h_unique` of smooth solutions. Then the solution
map extends uniquely from `C^∞(ℝ/ℤ)` to a jointly continuous map
`Φ : ℝ × H⁻¹(ℝ/ℤ) → H⁻¹(ℝ/ℤ)`. Moreover, for each `q ∈ H⁻¹(ℝ/ℤ)` the orbit
`{Φ(t, q) : t ∈ ℝ}` is uniformly bounded and equicontinuous in `H⁻¹(ℝ/ℤ)`. -/
theorem kdv_well_posed_H_minus_one_torus
    (h_exists : ∀ q : CinfT, ∃ u : ℝ → CinfT, IsSmoothSolutionT u ∧ u 0 = q)
    (h_unique : ∀ u v : ℝ → CinfT,
      IsSmoothSolutionT u → IsSmoothSolutionT v → u 0 = v 0 → u = v) :
    ∃ Φ : ℝ × Hm1T → Hm1T,
      Continuous Φ ∧ ExtendsSmoothFlowT Φ ∧
      (∀ Ψ : ℝ × Hm1T → Hm1T, Continuous Ψ → ExtendsSmoothFlowT Ψ → Ψ = Φ) ∧
      (∀ q : Hm1T, Bornology.IsBounded (Set.range fun t : ℝ => Φ (t, q))) ∧
      (∀ q : Hm1T, EquicontinuousHm1T (Set.range fun t : ℝ => Φ (t, q))) := by
  sorry

end KdV
