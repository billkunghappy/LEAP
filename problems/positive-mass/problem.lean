import Mathlib
set_option maxHeartbeats 4000000

/-!
# The Riemannian positive mass theorem in dimension three

This file contains **only the statement** of Theorem 1.1 of

> H. L. Bray, D. P. Kazaras, M. A. Khuri, D. L. Stern,
> *Harmonic functions and the mass of 3-dimensional asymptotically flat Riemannian manifolds*,
> J. Geom. Anal. (2022), arXiv:1911.06754,

(originally due to Schoen–Yau, 1979), with the proof left as `sorry`.

## Informal statement (BKKS, §1)

> Let `(M, g)` be a smooth connected 3-dimensional Riemannian manifold. It is *asymptotically
> flat* if there is a compact set `K ⊂ M` such that `M \ K = ⋃ₖ M_endᵏ`, where the ends
> `M_endᵏ` are finitely many, pairwise disjoint and diffeomorphic to the complement of a ball in
> `ℝ³`, and in each end there is a coordinate system with
> `|∂ˡ (g_ij - δ_ij)(x)| = O(|x|^(-q-l))`, `l = 0, 1, 2`, for some `q > 1/2`.
> The scalar curvature is assumed integrable, `R_g ∈ L¹(M)`, so that the ADM mass of each end
> `m = lim_{r→∞} (1/16π) ∫_{S_r} ∑_{i,j} (g_ij,i - g_ii,j) υ^j dA`
> is well defined (`υ` the unit outer normal of the coordinate sphere `S_r`, `dA` its area
> element).
>
> **Theorem 1.1.** If `(M, g)` is complete and asymptotically flat with nonnegative scalar
> curvature then `m ≥ 0`, and `m = 0` if and only if `(M, g) ≅ (ℝ³, δ)`.

## Why the ingredients have to be built here

Mathlib (as of the pinned version) has smooth manifolds, `mfderiv`, partial diffeomorphisms,
diffeomorphisms and the surface measure `Measure.toSphere` on the unit sphere, but it has **no**
Levi-Civita connection, curvature tensors, scalar curvature, asymptotically flat manifolds or ADM
mass. We therefore define the needed notions below, directly and transparently, in local
coordinates — exactly as in any textbook treatment.

## Conventions

* `E3 = EuclideanSpace ℝ (Fin 3)` is the model space `ℝ³`; `M` is a smooth (`C^∞`) manifold
  modelled on `E3` (`IsManifold 𝓘(ℝ, E3) ∞ M`), Hausdorff and connected.
* Following Mathlib, the tangent space at `x : M` is `TangentSpace 𝓘(ℝ, E3) x`, which is by
  definition `E3`, identified with the tangent space via the preferred chart `chartAt E3 x`.
  A Riemannian metric is therefore a family `g x : E3 →L[ℝ] E3 →L[ℝ] ℝ` of symmetric positive
  definite bilinear forms (in the coordinates of `chartAt E3 x`). Its coefficient matrix in any
  local parametrisation `φ : E3 → M` is
  `g_ij(y) = g (φ y) (dφ_y eᵢ) (dφ_y eⱼ)`, where `dφ_y = mfderiv 𝓘(ℝ,E3) 𝓘(ℝ,E3) φ y`
  (see `coeffMatrix`). Smoothness of `g` means smoothness of all these coefficients in all charts.
* The scalar curvature is computed from the coefficient matrix by the classical formulas
  `Γᵏᵢⱼ = ½ gᵏˡ (∂ᵢ gⱼₗ + ∂ⱼ gᵢₗ - ∂ₗ gᵢⱼ)`,
  `Rⱼₖ = ∂ᵢ Γⁱⱼₖ - ∂ⱼ Γⁱᵢₖ + Γⁱᵢₚ Γᵖⱼₖ - Γⁱⱼₚ Γᵖᵢₖ`,
  `R = gʲᵏ Rⱼₖ` (summation convention), in the preferred chart `chartAt E3 p` at `p`.
  (This is chart-independent; with this sign convention the round sphere has `R > 0`.)
* **Ends.** An end chart is a partial diffeomorphism `Φ : E3 → M` with source `{x : 1 < ‖x‖}`
  (the asymptotic coordinate system). Asymptotic flatness asks for finitely many end charts with
  pairwise disjoint images such that `M \ ⋃ₖ Φₖ({‖x‖ > 2})` is compact; this is the compact set
  `K` of the paper, and each `Φₖ({‖x‖ > 2})` is an end diffeomorphic to `ℝ³ \ B̄₂`.
  (Requiring the coordinates to extend a bit inside, to `{‖x‖ > 1}`, encodes that the paper's ends
  are diffeomorphic to the complement of an *open* ball, i.e. they include their boundary sphere;
  this rules out e.g. an extra cylindrical end hidden near the inner boundary of a chart.)
* **Decay.** `|∂ˡ (g_ij - δ_ij)(x)| = O(|x|^(-q-l))` as `|x| → ∞` for `l = 0, 1, 2`, expressed
  with `iteratedFDeriv` and `Asymptotics.IsBigO` along `Bornology.cobounded E3`.
* **Integrability of `R_g`.** Since `M \ ⋃ₖ Φₖ({‖x‖ > 2})` is compact and `R_g` is continuous,
  `R_g ∈ L¹(M, dV_g)` is equivalent to integrability of `R_g ∘ Φₖ · √(det g_ij)` over
  `{‖x‖ > 2}` (Lebesgue measure) for each end; this is how it is stated.
* **ADM mass.** With `∂ᵢ` the coordinate partial derivatives in the end, `υ = x/|x|` and
  `dA` the Euclidean area element of the coordinate sphere `S_r = {|x| = r}` (as in (1.2) of the
  paper), the flux is
  `(1/16π) ∫_{S_r} ∑_{i,j} (∂ᵢ g_ij - ∂ⱼ g_ii) υ^j dA
     = (1/16π) r² ∫_{S²} ∑_{i,j} (∂ᵢ g_ij - ∂ⱼ g_ii)(r ω) ω^j dσ(ω)`,
  where `σ = volume.toSphere` is the standard surface measure on the unit sphere `S² ⊂ ℝ³`
  (total mass `3 · vol(B₁) = 4π`). The mass is the limit as `r → ∞`. The theorem asserts in
  particular that this limit exists (Bartnik's well-definedness theorem).
  Sanity check: for `g = (1 + m/2r)⁴ δ` the flux tends to `m`.
* **Completeness** of `(M, g)` is a hypothesis of Theorem 1.1 and is stated explicitly. To this
  end the Riemannian distance is defined:
  - the speed of a `C¹` curve `γ : ℝ → M` at `t` is `|γ'(t)|_g = √(g_{γ t}(γ'(t), γ'(t)))`, where
    `γ'(t) = mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E3) γ t 1` (in the coordinates of `chartAt E3 (γ t)`, matching
    the convention for `g`);
  - the length of `γ` on `[0, 1]` is `L_g(γ) = ∫₀¹ |γ'(t)|_g dt` (see `curveLength`);
  - `d_g(p, q) = inf { L_g(γ) | γ : ℝ → M is C¹, γ 0 = p, γ 1 = q }` (see `riemannianDist`).
    Taking `C¹` curves rather than piecewise `C¹` ones gives the same infimum: a piecewise `C¹`
    path can be reparametrised, without changing its length, so that its velocity vanishes at
    the corners and at the endpoints, and then extended by constants outside `[0, 1]`.
  `(M, g)` is complete if `(M, d_g)` is a complete metric space, i.e. every `d_g`-Cauchy sequence
  `d_g`-converges (see `IsCompleteRiemannian`). By Hopf–Rinow this is the same as geodesic
  completeness. (With the definition of asymptotic flatness used here, completeness would actually
  follow from the other hypotheses; it is nevertheless stated, as in the paper.)
* **`(M, g) ≅ (ℝ³, δ)`** means there is a smooth diffeomorphism `F : M → ℝ³` with
  `g_p(v, w) = ⟪dF_p v, dF_p w⟫` for all `p, v, w`.
* The rigidity statement is per end: for every end `k` with mass `mₖ`, `mₖ = 0` iff
  `(M, g) ≅ (ℝ³, δ)`.
-/

noncomputable section

open Manifold Filter Topology MeasureTheory Metric
open scoped ContDiff

namespace PositiveMass

/-- The model space `ℝ³`. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The `i`-th standard basis vector of `ℝ³`. -/
abbrev e (i : Fin 3) : E3 := EuclideanSpace.single i (1 : ℝ)

/-- The coordinate partial derivative `∂ᵢ f (y)` of a function `f : ℝ³ → ℝ`. -/
def partialDeriv (i : Fin 3) (f : E3 → ℝ) (y : E3) : ℝ :=
  fderiv ℝ f y (e i)

/-! ### Curvature of a metric given by its coefficient matrix in local coordinates -/

section LocalCoordinates

/-- Christoffel symbols `Γᵏᵢⱼ = ½ ∑ₗ gᵏˡ (∂ᵢ gⱼₗ + ∂ⱼ gᵢₗ - ∂ₗ gᵢⱼ)` of a metric whose coefficient
matrix in local coordinates is `G : ℝ³ → Matrix (Fin 3) (Fin 3) ℝ`. -/
def christoffel (G : E3 → Matrix (Fin 3) (Fin 3) ℝ) (k i j : Fin 3) (y : E3) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin 3, (G y)⁻¹ k l *
    (partialDeriv i (fun z => G z j l) y + partialDeriv j (fun z => G z i l) y
      - partialDeriv l (fun z => G z i j) y)

/-- Ricci tensor `Rⱼₖ = ∂ᵢ Γⁱⱼₖ - ∂ⱼ Γⁱᵢₖ + Γⁱᵢₚ Γᵖⱼₖ - Γⁱⱼₚ Γᵖᵢₖ` in local coordinates. -/
def ricci (G : E3 → Matrix (Fin 3) (Fin 3) ℝ) (j k : Fin 3) (y : E3) : ℝ :=
  ∑ i : Fin 3, (partialDeriv i (christoffel G i j k) y - partialDeriv j (christoffel G i i k) y)
    + ∑ i : Fin 3, ∑ p : Fin 3,
        (christoffel G i i p y * christoffel G p j k y
          - christoffel G i j p y * christoffel G p i k y)

/-- Scalar curvature `R = ∑ⱼₖ gʲᵏ Rⱼₖ` in local coordinates. -/
def scalarCurvatureLocal (G : E3 → Matrix (Fin 3) (Fin 3) ℝ) (y : E3) : ℝ :=
  ∑ j : Fin 3, ∑ k : Fin 3, (G y)⁻¹ j k * ricci G j k y

end LocalCoordinates

/-! ### Riemannian metrics on a 3-manifold -/

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]

/-- The coefficient matrix `g_ij(y) = g (φ y) (dφ_y eᵢ) (dφ_y eⱼ)` of a field of bilinear forms
`g` (in Mathlib's tangent-space convention) with respect to a local parametrisation `φ : ℝ³ → M`. -/
def coeffMatrix (g : M → E3 →L[ℝ] E3 →L[ℝ] ℝ) (φ : E3 → M) (y : E3) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => g (φ y) (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) φ y (e i))
    (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) φ y (e j))

/-- A smooth Riemannian metric on the 3-manifold `M`. At each point `x`, `g x` is a bilinear form on
`T_x M = E3` (expressed in the coordinates of `chartAt E3 x`, as in Mathlib's convention for tangent
spaces). -/
structure RiemannianMetric3 (M : Type*) [TopologicalSpace M] [ChartedSpace E3 M] where
  /-- The metric tensor. -/
  g : M → E3 →L[ℝ] E3 →L[ℝ] ℝ
  /-- Symmetry. -/
  symm : ∀ x v w, g x v w = g x w v
  /-- Positive definiteness. -/
  posDef : ∀ x v, v ≠ 0 → 0 < g x v v
  /-- Smoothness: the coefficients in every chart are `C^∞` on the chart's target. -/
  smooth : ∀ x₀ : M, ∀ i j : Fin 3,
    ContDiffOn ℝ ∞ (fun y => coeffMatrix g (chartAt E3 x₀).symm y i j) (chartAt E3 x₀).target

namespace RiemannianMetric3

/-- The coefficient matrix of the metric in a local parametrisation `φ : ℝ³ → M`. -/
def coeff (g : RiemannianMetric3 M) (φ : E3 → M) : E3 → Matrix (Fin 3) (Fin 3) ℝ :=
  coeffMatrix g.g φ

/-- The scalar curvature `R_g(p)`, computed in the preferred chart at `p`. -/
def scalarCurvature (g : RiemannianMetric3 M) (p : M) : ℝ :=
  scalarCurvatureLocal (g.coeff (chartAt E3 p).symm) (chartAt E3 p p)

end RiemannianMetric3

/-! ### The Riemannian distance and completeness -/

namespace RiemannianMetric3

/-- The velocity `γ'(t) ∈ T_{γ t} M` of a curve `γ : ℝ → M`, i.e. `dγ_t (1)`. -/
def velocity (γ : ℝ → M) (t : ℝ) : E3 :=
  mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E3) γ t (1 : ℝ)

/-- The `g`-length `L_g(γ) = ∫₀¹ √(g_{γ t}(γ'(t), γ'(t))) dt` of a curve `γ` on `[0, 1]`. -/
def curveLength (g : RiemannianMetric3 M) (γ : ℝ → M) : ℝ :=
  ∫ t in (0 : ℝ)..1, Real.sqrt (g.g (γ t) (velocity γ t) (velocity γ t))

/-- The Riemannian distance `d_g(p, q)`: the infimum of the `g`-lengths of the `C¹` curves
`γ : ℝ → M` with `γ 0 = p` and `γ 1 = q`. -/
def riemannianDist (g : RiemannianMetric3 M) (p q : M) : ℝ :=
  ⨅ (γ : {γ : ℝ → M // ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E3) 1 γ ∧ γ 0 = p ∧ γ 1 = q}),
    g.curveLength γ.1

/-- `(M, g)` is complete: `(M, d_g)` is a complete metric space, i.e. every `d_g`-Cauchy sequence
converges with respect to `d_g`. -/
def IsCompleteRiemannian (g : RiemannianMetric3 M) : Prop :=
  ∀ u : ℕ → M,
    (∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, g.riemannianDist (u m) (u n) < ε) →
      ∃ p : M, Tendsto (fun n => g.riemannianDist (u n) p) atTop (𝓝 0)

end RiemannianMetric3

/-! ### Asymptotically flat ends and the ADM mass -/

/-- An end chart: an asymptotic coordinate system `Φ : {x ∈ ℝ³ : ‖x‖ > 1} → M`, i.e. a smooth
partial diffeomorphism with source `{x | 1 < ‖x‖}`. -/
structure EndChart (M : Type*) [TopologicalSpace M] [ChartedSpace E3 M] where
  /-- The coordinate parametrisation of the end. -/
  Φ : PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 M ∞
  /-- It is defined exactly on the complement of the closed unit ball. -/
  source_eq : Φ.source = {x : E3 | 1 < ‖x‖}

/-- The ADM flux through the coordinate sphere of radius `r` in an end:
`(1/16π) ∫_{S_r} ∑_{i,j} (∂ᵢ g_ij - ∂ⱼ g_ii) υ^j dA`, written as
`(1/16π) r² ∫_{S²} ∑_{i,j} (∂ᵢ g_ij - ∂ⱼ g_ii)(r θ) θ^j dσ(θ)`. -/
def admFlux (g : RiemannianMetric3 M) (Φ : EndChart M) (r : ℝ) : ℝ :=
  1 / (16 * Real.pi) * r ^ 2 *
    ∫ (θ : sphere (0 : E3) 1),
      ∑ i : Fin 3, ∑ j : Fin 3,
        (partialDeriv i (fun x => g.coeff Φ.Φ x i j) (r • (θ : E3))
          - partialDeriv j (fun x => g.coeff Φ.Φ x i i) (r • (θ : E3))) * (θ : E3) j
      ∂(volume : Measure E3).toSphere

/-- `(M, g)` is asymptotically flat (BKKS (1.1)), with integrable scalar curvature. -/
structure AsymptoticallyFlat (g : RiemannianMetric3 M) where
  /-- The number of ends. -/
  numEnds : ℕ
  /-- The asymptotic coordinate systems of the ends. -/
  ends : Fin numEnds → EndChart M
  /-- The decay rate. -/
  q : ℝ
  q_gt : 1 / 2 < q
  /-- The ends are pairwise disjoint. -/
  disjoint : Pairwise fun k l => Disjoint (ends k).Φ.target (ends l).Φ.target
  /-- Outside the ends `{‖x‖ > 2}`, the manifold is compact: this is the compact set `K`. -/
  isCompact_core : IsCompact (⋃ k, (ends k).Φ '' {x : E3 | 2 < ‖x‖})ᶜ
  /-- `|∂ˡ (g_ij - δ_ij)(x)| = O(|x|^(-q-l))` as `|x| → ∞`, for `l = 0, 1, 2`. -/
  decay : ∀ k, ∀ i j : Fin 3, ∀ l : ℕ, l ≤ 2 →
    (fun x : E3 => ‖iteratedFDeriv ℝ l
        (fun y => g.coeff (ends k).Φ y i j - if i = j then (1 : ℝ) else 0) x‖)
      =O[Bornology.cobounded E3] fun x : E3 => ‖x‖ ^ (-q - (l : ℝ))
  /-- The scalar curvature is integrable, `R_g ∈ L¹(M, dV_g)` (stated end by end; on the compact
  core integrability is automatic). -/
  integrable_scalarCurvature : ∀ k,
    IntegrableOn
      (fun x : E3 => g.scalarCurvature ((ends k).Φ x) * Real.sqrt (g.coeff (ends k).Φ x).det)
      {x : E3 | 2 < ‖x‖}

/-- `(M, g)` is isometric to Euclidean space `(ℝ³, δ)`. -/
def IsometricToEuclidean [IsManifold 𝓘(ℝ, E3) ∞ M] (g : RiemannianMetric3 M) : Prop :=
  ∃ F : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) M E3 ∞,
    ∀ (p : M) (v w : E3),
      g.g p v w = @inner ℝ E3 _ (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) F p v)
        (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) F p w)

/-- **Positive mass theorem** (BKKS, Theorem 1.1; Schoen–Yau). Let `(M, g)` be a smooth connected
complete asymptotically flat Riemannian 3-manifold with nonnegative scalar curvature. Then for every
end the ADM mass `m` exists and satisfies `m ≥ 0`, and `m = 0` if and only if `(M, g)` is isometric
to `(ℝ³, δ)`. -/
theorem positive_mass [T2Space M] [ConnectedSpace M] [IsManifold 𝓘(ℝ, E3) ∞ M]
    (g : RiemannianMetric3 M) (hComplete : g.IsCompleteRiemannian) (hAF : AsymptoticallyFlat g)
    (hR : ∀ p : M, 0 ≤ g.scalarCurvature p) :
    ∀ k : Fin hAF.numEnds, ∃ m : ℝ,
      Tendsto (fun r : ℝ => admFlux g (hAF.ends k) r) atTop (𝓝 m) ∧
      0 ≤ m ∧ (m = 0 ↔ IsometricToEuclidean g) := by
  sorry

end PositiveMass
