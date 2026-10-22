import Mathlib
import WeilDeligneDefs
import local_reciprocity
import langlands_deligne
set_option maxHeartbeats 4000000

noncomputable section

set_option linter.unusedSectionVars false

open scoped Classical
open ValuativeRel

universe u

/-!
# Local and global root numbers of elliptic curves, from first principles

This file gives a *genuine* definition of the local root number `w(E/F)` of a Weierstrass
curve over a local field and of the global root number `w(E/K) = ∏_v w(E/K_v)` over a number
field, following Deligne's theory of local constants (ε‑factors) applied to the
Weil–Deligne representation attached to `E` (Deligne, *Les constantes des équations
fonctionnelles des fonctions L*, 1973; Rohrlich, *Elliptic curves and the Weil–Deligne group*,
1994; Tate, *Number theoretic background*, Corvallis 1979).

This file is the home of the (root-namespace) declarations

* `CurveClass F` — isomorphism classes of Weierstrass curves over `F`;
* `rootNumberCl F : CurveClass F → ℤˣ` — the local root number on isomorphism classes;
* `rootNumber : WeierstrassCurve F → ℤˣ` — the local root number, *definitionally*
  `rootNumberCl F ⟦E⟧`;
* `globalRootNumber : WeierstrassCurve K → ℤˣ` — the product `∏_v w(E/K_v)` over all places,

which `Hilbert10Defs.lean` imports and re-exposes (so that `theorem_3_4.lean`,
`corollary_3_6.lean` and the main file see them under `import Hilbert10Defs`, with the
statements unchanged). These four declarations used to live in `Hilbert10Defs.lean`, with
`rootNumberCl` defined as an *arbitrary* sign (`Classical.choice`); they are now the genuine
objects.

## Structure

* All the vocabulary (Weil groups, Tate modules, the Weil–Deligne representation `σ'_E`,
  Tate's local constants of characters, induced representations, and the two structures
  `LocalReciprocity` and `LocalConstants` recording the characterising properties of the local
  reciprocity map and of Deligne's local constants) lives in `WeilDeligneDefs.lean`.
* The two classical existence theorems on which the definition rests are stated in
  `local_reciprocity.lean` (**local class field theory**,
  `local_reciprocity : Nonempty (LocalReciprocity F)`) and
  `langlands_deligne.lean` (**Langlands–Deligne**,
  `langlands_deligne rec : Nonempty (LocalConstants F rec)`). They are the only
  non-definitional content behind the root number: once they are proved, no axiom beyond
  Lean's standard foundations (`propext`, `Classical.choice`, `Quot.sound`) is used.
* This file picks the reciprocity map and the local constants by `Classical.choice` on these
  two theorems and defines the local and global root numbers.

## Mathematical content

* For a Weil–Deligne representation, `ε(σ') = ε(ρ) · det(-Φ_geom | V^{I}/V_N^{I})`
  (Deligne (8.12)), and the **local root number** is
  `w(E/F) = ε(σ'_E, ψ₀, dx₀)` for `ψ₀` an additive character of conductor `𝒪_F` and
  `dx₀(𝒪_F) = 1`; with these normalisations `ε(σ'_E, ψ₀, dx₀) ∈ {±1}` because `σ'_E` is
  symplectic with determinant `‖·‖` (Weil pairing), and it is independent of `ψ₀` and `ℓ`.
* At an archimedean place `w(E/ℝ) = w(E/ℂ) = -1` (Deligne's archimedean constant of the
  Hodge structure of `E`: `ε = i · i`).
* `w(E/K) = ∏_v w(E/K_v)` over all places of the number field `K`.

## Conventions

See `WeilDeligneDefs.lean`: `‖Φ_arith‖ = q`, uniformisers correspond to *geometric* Frobenius
elements under the reciprocity map, and `dx(𝒪_L) = 1` on every finite extension `L/F`.
-/

namespace EllipticRootNumber

section LocalField

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The algebraic closure `F̄` of `F`. -/
local notation "F̄" => AlgebraicClosure F

variable (E : WeierstrassCurve F) (L : IntermediateField F (AlgebraicClosure F))

/-! ## §8' Local class field theory and Langlands–Deligne as a hypothesis

`RootNumberDefs.lean` picks the reciprocity map and the local constants once and for all by
`Classical.choice` on the two assumed theorems

* `local_reciprocity F : Nonempty (LocalReciprocity F)` (local class field theory), and
* `langlands_deligne F rec : Nonempty (LocalConstants F rec)` (Langlands–Deligne),

stated in `local_reciprocity.lean` and `langlands_deligne.lean`. This
self-contained problem file declares **no axiom**: the existence of these data is packaged as
the proposition `HasLocalConstants F` below, and the local root number is defined conditionally
on it (§9), with the irrelevant value `1` when it fails. The two assumed theorems are the
*permitted assumptions* of this problem (see the accompanying manifest
`root_number_assumed_results.md`): once they are available, `HasLocalConstants F` is
`⟨Classical.choice (local_reciprocity F), langlands_deligne F _⟩`. -/

/-- The local reciprocity map, chosen from `local_reciprocity` (local class field
theory). -/
def localReciprocity : LocalReciprocity F := Classical.choice (local_reciprocity F)

/-- Deligne's local constants, chosen from `langlands_deligne` (Langlands–Deligne). -/
def localConstants : LocalConstants F (localReciprocity F) :=
  Classical.choice (langlands_deligne F (localReciprocity F))

/-- `HasLocalConstants F` says that there is a local reciprocity map `rec` for `F` (local class
field theory) together with Deligne's local constants for `rec` (Langlands–Deligne); it is the
conjunction of the two assumed theorems `local_reciprocity` and
`langlands_deligne`. -/
def HasLocalConstants : Prop := ∃ rec : LocalReciprocity F, Nonempty (LocalConstants F rec)

/-! ## §9 The local constant of a Weil–Deligne representation and the local root number -/

/-- The inertia invariants `V^{I_L}` of a Weil–Deligne representation. -/
def inertiaInvariants (σ' : WDRep F L) : Submodule (Ω F) σ'.V where
  carrier := {v | ∀ w : relWeil F L, (w : AbsGal F) ∈ inertia F → σ'.ρ w v = v}
  zero_mem' := fun _ _ => map_zero _
  add_mem' := fun {a b} ha hb w hw => by rw [map_add, ha w hw, hb w hw]
  smul_mem' := fun c v hv w hw => by rw [map_smul, hv w hw]

/-- `det(-Φ_geom | V^{I}/V_N^{I})`, the correction factor of Deligne (8.12) for a Weil–Deligne
representation (`V_N = ker N`; the factor is `1` in the degenerate case where `V^I` or
`V_N^I` is not `Φ`-stable, which does not happen for admissible representations). -/
def frobDet (σ' : WDRep F L) : Ω F :=
  let Φ := geomFrobL F L (resDeg F L)
  let VI := inertiaInvariants F L σ'
  if hI : ∀ v ∈ VI, σ'.ρ Φ v ∈ VI then
    let fI : VI →ₗ[Ω F] VI := (σ'.ρ Φ).restrict hI
    let K : Submodule (Ω F) VI := (LinearMap.ker σ'.N).comap VI.subtype
    if hK : K ≤ K.comap fI then LinearMap.det (-(Submodule.mapQ K K fI hK)) else 1
  else 1

/-- The local constant `ε(σ', ψ, dx) = ε(ρ, ψ, dx) · det(-Φ_geom | V^{I}/V_N^{I})` of a
Weil–Deligne representation (Deligne (8.12)), with `dx(𝒪_L) = 1`, computed with respect to
Deligne's local constants `lc` (for a reciprocity map `rec`). -/
def epsWD {rec : LocalReciprocity F} (lc : LocalConstants F rec) (σ' : WDRep F L)
    (ψ : AddChar L (Ω F)) : Ω F :=
  (lc.eps L σ'.ρ ψ : Ω F) * frobDet F L σ'

/-- A standard additive character `ψ₀` of `F` (viewed as `⊥ ⊆ F̄`): trivial on `𝒪_F` and
nontrivial on `𝔭_F^{-1}`, i.e. `n(ψ₀) = 0`. -/
def stdChar : AddChar (⊥ : IntermediateField F (AlgebraicClosure F)) (Ω F) :=
  Classical.epsilon fun ψ : AddChar (⊥ : IntermediateField F (AlgebraicClosure F)) (Ω F) =>
    (∀ x, 0 ≤ valL F ⊥ x → ψ x = 1) ∧ ∃ x, valL F ⊥ x = -1 ∧ ψ x ≠ 1

/-- The local constant `ε(σ'_E, ψ₀, dx₀) ∈ Ω` of `E/F`; it lies in `{±1}` because `σ'_E` is
symplectic with determinant `‖·‖` (Weil pairing), and it does not depend on the choice of
`ψ₀` (any other choice is `ψ₀(a·)` with `a ∈ 𝒪_F^×`, which multiplies `ε` by
`det σ'_E(a) = ‖a‖ = 1`) nor on `ℓ`. Computed with respect to Deligne's local constants `lc`. -/
def localEps {rec : LocalReciprocity F} (lc : LocalConstants F rec) : Ω F :=
  epsWD F ⊥ lc (wdRep F E) (stdChar F)

/-- **The local root number `w(E/F) ∈ {±1}`** of `E` over the non-archimedean local field `F`:
the sign `ε(σ'_E, ψ₀, dx₀)`, computed with respect to a reciprocity map and Deligne's local
constants chosen by `Classical.choice` from `HasLocalConstants F` (the value does not depend on
this choice, both objects being unique). In the branch where `HasLocalConstants F` fails the
value is set to `1`; that branch is excluded by the two permitted assumptions
`local_reciprocity` and `langlands_deligne`. -/
def rootNumberNonarch : ℤˣ :=
  if localEps F E (localConstants F) = -1 then -1 else 1

/-- Under `HasLocalConstants F`, `rootNumberNonarch` is the sign of `ε(σ'_E, ψ₀, dx₀)` for the
chosen reciprocity map and local constants. -/
theorem rootNumberNonarch_of_hasLocalConstants (_h : HasLocalConstants F) :
    rootNumberNonarch F E =
      if localEps F E (localConstants F) = -1 then -1 else 1 :=
  rfl

end LocalField

end EllipticRootNumber

/-! ## §10 Root numbers over an arbitrary field, and the global root number

The declarations of this section live in the **root namespace**: they are the definitions
`CurveClass`, `rootNumberCl`, `rootNumber`, `globalRootNumber` that `Hilbert10Defs.lean` used to
contain (with `rootNumberCl` an arbitrary `Classical.choice`), now defined genuinely. -/

open EllipticRootNumber

/--
Isomorphism classes of Weierstrass curves over `F`, i.e. the quotient of
`WeierstrassCurve F` by the action of admissible variable changes.
-/
abbrev CurveClass (F : Type u) [Field F] :=
  MulAction.orbitRel.Quotient (WeierstrassCurve.VariableChange F) (WeierstrassCurve F)

/-- The local root number `w(E/F)` of a Weierstrass curve over an arbitrary field `F`:
* if `F ≅ ℝ` or `F ≅ ℂ`, `w(E/F) = -1` (Deligne's archimedean local constant of the weight-one
  Hodge structure `H_1(E(ℂ))`: `ε = i · i = -1`);
* otherwise, if `F` admits a structure of non-archimedean local field, `w(E/F)` is
  `rootNumberNonarch` for (the chosen) such structure (the structure is unique, by
  F. K. Schmidt's theorem, and the two cases are disjoint);
* otherwise (a field which is not a local field) the value is irrelevant and set to `1`. -/
noncomputable def rootNumberRaw {F : Type u} [Field F] (E : WeierstrassCurve F) : ℤˣ :=
  if Nonempty (F ≃+* ℝ) ∨ Nonempty (F ≃+* ℂ) then -1
  else if h : Nonempty (LocalFieldStructure F) then
    letI := (Classical.choice h).rel
    letI := (Classical.choice h).top
    haveI := (Classical.choice h).isLocalField
    rootNumberNonarch F E
  else 1

/--
The local root number `w(E/F) ∈ {±1}` on isomorphism classes of Weierstrass curves over `F`:
the root number of a chosen representative. (`rootNumberRaw` is an isomorphism invariant, so
this agrees with `rootNumberRaw` on every representative.)
-/
noncomputable def rootNumberCl (F : Type u) [Field F] : CurveClass F → ℤˣ :=
  fun c => rootNumberRaw (Quotient.out c)

/--
The root number `w(E/F) ∈ {±1}` of a Weierstrass curve, factoring through its
isomorphism class.
-/
noncomputable def rootNumber {F : Type u} [Field F] (E : WeierstrassCurve F) : ℤˣ :=
  rootNumberCl F (Quotient.mk (MulAction.orbitRel (WeierstrassCurve.VariableChange F)
    (WeierstrassCurve F)) E)

/-- `rootNumber` is invariant under admissible changes of variables. -/
theorem rootNumber_variableChange {F : Type u} [Field F]
    (C : WeierstrassCurve.VariableChange F) (E : WeierstrassCurve F) :
    rootNumber (C • E) = rootNumber E :=
  congrArg (rootNumberCl F) (Quotient.sound (MulAction.mem_orbit _ _))

/--
The global root number `w(E/K) = ∏_v w(E/K_v)` of a Weierstrass curve over a number
field `K`, the product running over all finite and infinite places.
-/
noncomputable def globalRootNumber {K : Type u} [Field K] [NumberField K]
    (E : WeierstrassCurve K) : ℤˣ :=
  (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      rootNumber (E.baseChange (v.adicCompletion K))) *
  (∏ w : NumberField.InfinitePlace K, rootNumber (E.baseChange w.Completion))

/-- At a field isomorphic to `ℝ` or `ℂ` the raw root number is `-1`. -/
theorem rootNumberRaw_of_archimedean {F : Type u} [Field F] (E : WeierstrassCurve F)
    (hF : Nonempty (F ≃+* ℝ) ∨ Nonempty (F ≃+* ℂ)) :
    rootNumberRaw E = -1 := by
  unfold rootNumberRaw
  rw [if_pos hF]

end  -- the `noncomputable section` opened at the top of the `WeilDeligneDefs.lean` part
