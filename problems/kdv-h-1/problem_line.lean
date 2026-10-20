import Mathlib

/-!
# KdV is well-posed in `H⁻¹(ℝ)` (Killip–Vişan, Theorem 1.1, line case)

Formal statement of the line case of

> **Theorem 1.1 (Global well-posedness).** The equation (KdV)
> `d/dt q = -q''' + 6 q q'` is globally well-posed for initial data in `H⁻¹(ℝ)` in the
> following sense: the solution map extends uniquely from Schwartz space to a jointly
> continuous map `Φ : ℝ × H⁻¹ → H⁻¹`. Moreover, for each initial data `q ∈ H⁻¹`, the orbit
> `{Φ(t,q) : t ∈ ℝ}` is uniformly bounded and equicontinuous in `H⁻¹`.

(See also Corollary 5.2, which is the line case as the paper proves it.)

R. Killip and M. Vişan, *KdV is well-posed in `H⁻¹`*, Ann. of Math. (2) **190** (2019),
249–305, arXiv:1802.04851. The informal source is `KdV_killip_visan_informal.md` in this
folder.

## Notion of solution (as in the paper)

* **Schwartz solutions.** The paper takes classical well-posedness in Schwartz space for
  granted (Bona–Smith, Kato, Sjöberg, Temam): "Schwartz-space initial data leads to unique
  global solutions to (KdV) that remain in Schwartz class … the solution map is … infinitely
  differentiable in both variables". Accordingly, a *Schwartz solution* here is a curve
  `u : ℝ → 𝓢(ℝ, ℝ)` that is differentiable *as a curve in Schwartz space*, i.e. for the
  Fréchet topology of `𝓢(ℝ, ℝ)`. Its derivative at every time `t` must be the Schwartz
  function `x ↦ -∂ₓ³u(t,x) + 6 u(t,x) ∂ₓu(t,x)`. Such a curve is automatically `C^∞` in time
  with values in `𝓢`, since the right-hand side is a smooth function of `u(t)` in `𝓢`.

* **`H⁻¹` solutions.** As in the paper, solutions with `H⁻¹` data are *unique limits of
  Schwartz solutions*: `Φ` is required to be continuous on `ℝ × H⁻¹` and to agree with the
  Schwartz flow, `Φ(t, u(0)) = u(t)`, for every Schwartz solution `u`.

* **Classical input is assumed, not proved (conditional statement).** The paper does not
  prove Schwartz-class well-posedness; it cites it (Bona–Smith [5], Kato [34], Sjöberg
  [63, 64], Temam [65]) and relies on it ("We shall rely on this result"). Accordingly, the
  main theorem takes as *hypotheses* global existence (`h_exists`) and uniqueness
  (`h_unique`) of Schwartz solutions, so that "the solution map on Schwartz space" is a
  well-defined map on all of `𝓢`. Both hypotheses are true classical theorems, so the
  statement is not vacuous. They are deliberately theorem hypotheses rather than `axiom`s.
  Any result proved from this file is Theorem 1.1 (line case) *conditional on* classical
  Schwartz well-posedness, exactly as in the paper.

  Note: the paper additionally uses that the Schwartz solution map is `C^∞` in time and data
  (e.g. to pass from `{H_κ, H_KdV} = 0` to commuting flows). This is *not* assumed here, so
  a proof following the paper must establish whatever it needs of that fact.

## How `H⁻¹(ℝ)` and equicontinuity are encoded

* **Unknown.** `q` is real-valued, as in the paper.

* **Fourier convention (paper §1.2).** `q̂(ξ) = (2π)^{-1/2} ∫ e^{-iξx} q(x) dx`.

* **The space.** The paper's norm is `‖q‖²_{H⁻¹(ℝ)} = ∫ |q̂(ξ)|² (4 + ξ²)⁻¹ dξ`, so
  `q ↦ (4 + ξ²)^{-1/2} q̂(ξ)` is a linear isometry from real `H⁻¹(ℝ)` into `L²(ℝ, dξ; ℂ)`.
  We realise `H⁻¹(ℝ)` as the closure of the image of `𝓢(ℝ, ℝ)` under this isometry. Since
  Schwartz functions are dense in `H⁻¹(ℝ)`, this is isometrically isomorphic to the paper's
  `H⁻¹(ℝ)`, and it is literally the completion of Schwartz space in the `H⁻¹` norm, which is
  the space to which "the solution map extends".

* **Equicontinuity (paper Definition 4.1, (4.1)).** `Q ⊆ H⁻¹` is equicontinuous if
  `q(· + h) → q` in `H⁻¹` as `h → 0`, uniformly for `q ∈ Q`. Translation by `h` multiplies
  `q̂(ξ)` by `e^{iξh}`. So, for the profile `f` of `q`,
  `‖q(· + h) - q‖²_{H⁻¹} = ∫ |e^{iξh} - 1|² |f(ξ)|² dξ`. This is literally (4.1), not the
  equivalent Fourier-tightness form (4.2).

* **Junk value.** The embedding is defined with a `dite` on `MemLp`, returning `0` otherwise.
  For Schwartz inputs the membership always holds.
-/

open MeasureTheory Complex
open scoped Real SchwartzMap Classical

noncomputable section

namespace KdV

/-! ## The KdV equation `d/dt q = -q''' + 6 q q'` -/

/-- Right-hand side of (KdV) for a profile `f : ℝ → ℝ` at the point `x`:
`-f'''(x) + 6 f(x) f'(x)`. -/
def kdvRHS (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(iteratedDeriv 3 f x) + 6 * f x * deriv f x

/-- A global Schwartz solution of (KdV) on the line: a curve `u : ℝ → 𝓢(ℝ, ℝ)` that is
differentiable in the Schwartz-space (Fréchet) topology at every time `t`. Its derivative is
the Schwartz function `x ↦ -∂ₓ³u(t,x) + 6 u(t,x) ∂ₓu(t,x)`. -/
def IsSchwartzSolution (u : ℝ → 𝓢(ℝ, ℝ)) : Prop :=
  ∀ t : ℝ, ∃ v : 𝓢(ℝ, ℝ), HasDerivAt u v t ∧ ∀ x : ℝ, v x = kdvRHS (u t) x

/-! ## The space `H⁻¹(ℝ)` -/

/-- The Fourier transform on the line with the paper's normalisation
`q̂(ξ) = (2π)^{-1/2} ∫ e^{-iξx} q(x) dx`. -/
def fourierLine (q : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ((Real.sqrt (2 * π))⁻¹ : ℂ) * ∫ x : ℝ, Complex.exp (-((ξ : ℂ) * (x : ℂ)) * I) * (q x : ℂ)

/-- The `H⁻¹(ℝ)` profile `ξ ↦ (4 + ξ²)^{-1/2} q̂(ξ)`. Its `L²(dξ)` norm is `‖q‖_{H⁻¹(ℝ)}`. -/
def hm1Profile (q : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ((Real.sqrt (4 + ξ ^ 2))⁻¹ : ℂ) * fourierLine q ξ

/-- The isometric embedding of a Schwartz function into `L²(ℝ, dξ; ℂ)` via its `H⁻¹` profile
(junk value `0` if the profile were not square integrable, which never happens). -/
def toHm1 (q : 𝓢(ℝ, ℝ)) : Lp ℂ 2 (volume : Measure ℝ) :=
  if h : MemLp (hm1Profile q) 2 volume then h.toLp _ else 0

/-- Real `H⁻¹(ℝ)`, realised (isometrically) as the closure in `L²(ℝ, dξ; ℂ)` of the `H⁻¹`
profiles of real Schwartz functions, i.e. the completion of `𝓢(ℝ, ℝ)` in the `H⁻¹` norm. -/
def Hm1 : Submodule ℝ (Lp ℂ 2 (volume : Measure ℝ)) :=
  (Submodule.span ℝ (Set.range toHm1)).topologicalClosure

/-- The embedding `𝓢(ℝ, ℝ) → H⁻¹(ℝ)`. -/
def ι (q : 𝓢(ℝ, ℝ)) : Hm1 :=
  ⟨toHm1 q, Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨q, rfl⟩)⟩

/-! ## Equicontinuity and the extension property -/

/-- `‖q(· + h) - q‖²_{H⁻¹(ℝ)}` expressed through the `H⁻¹` profile `f` of `q`:
`∫ |e^{iξh} - 1|² |f(ξ)|² dξ`. -/
def translateDiffSq (f : Lp ℂ 2 (volume : Measure ℝ)) (h : ℝ) : ℝ :=
  ∫ ξ : ℝ, ‖(Complex.exp ((ξ : ℂ) * (h : ℂ) * I) - 1) * (f : ℝ → ℂ) ξ‖ ^ 2

/-- Equicontinuity in `H⁻¹(ℝ)` (paper Definition 4.1): `q(· + h) → q` in `H⁻¹` as `h → 0`,
uniformly for `q ∈ Q`. -/
def EquicontinuousHm1 (Q : Set Hm1) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ q ∈ Q, ∀ h : ℝ, |h| < δ →
    translateDiffSq (q : Lp ℂ 2 (volume : Measure ℝ)) h < ε

/-- `Φ` extends the Schwartz solution map: for every Schwartz solution `u`,
`Φ(t, u(0)) = u(t)` in `H⁻¹(ℝ)` for all `t`. -/
def ExtendsSchwartzFlow (Φ : ℝ × Hm1 → Hm1) : Prop :=
  ∀ u : ℝ → 𝓢(ℝ, ℝ), IsSchwartzSolution u → ∀ t : ℝ, Φ (t, ι (u 0)) = ι (u t)

/-! ## Main theorem -/

/-- **Killip–Vişan, Theorem 1.1 (line case).** KdV is globally well-posed in `H⁻¹(ℝ)`:
assuming the classical Schwartz-class theory (global existence `h_exists` and uniqueness
`h_unique` of Schwartz solutions, which the paper takes for granted), the solution map
extends uniquely from Schwartz space to a jointly continuous map
`Φ : ℝ × H⁻¹(ℝ) → H⁻¹(ℝ)`. Moreover, for each `q ∈ H⁻¹(ℝ)` the orbit `{Φ(t, q) : t ∈ ℝ}` is
uniformly bounded and equicontinuous in `H⁻¹(ℝ)`. -/
theorem kdv_well_posed_H_minus_one
    (h_exists : ∀ q : 𝓢(ℝ, ℝ), ∃ u : ℝ → 𝓢(ℝ, ℝ), IsSchwartzSolution u ∧ u 0 = q)
    (h_unique : ∀ u v : ℝ → 𝓢(ℝ, ℝ),
      IsSchwartzSolution u → IsSchwartzSolution v → u 0 = v 0 → u = v) :
    ∃ Φ : ℝ × Hm1 → Hm1,
      Continuous Φ ∧ ExtendsSchwartzFlow Φ ∧
      (∀ Ψ : ℝ × Hm1 → Hm1, Continuous Ψ → ExtendsSchwartzFlow Ψ → Ψ = Φ) ∧
      (∀ q : Hm1, Bornology.IsBounded (Set.range fun t : ℝ => Φ (t, q))) ∧
      (∀ q : Hm1, EquicontinuousHm1 (Set.range fun t : ℝ => Φ (t, q))) := by
  sorry

end KdV
