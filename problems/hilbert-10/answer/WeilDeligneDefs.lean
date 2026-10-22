import Mathlib
set_option maxHeartbeats 4000000

/-!
# Weil groups, Weil–Deligne representations and local constants: the vocabulary

This file contains the *definitions* underlying the first-principles definition of the local
root number `w(E/F)` of a Weierstrass curve over a non-archimedean local field `F`
(`RootNumberDefs.lean`). It contains no axioms and no `sorry`. It is shared by

* `local_reciprocity.lean` — the statement of **local class field theory** (existence
  of the local Artin reciprocity map), `local_reciprocity : Nonempty (LocalReciprocity F)`;
* `langlands_deligne.lean` — the statement of the **Langlands–Deligne theorem** on the
  existence of local constants (ε-factors),
  `langlands_deligne : Nonempty (LocalConstants F rec)`;
* `RootNumberDefs.lean` — which imports both and defines `rootNumber'`, `globalRootNumber'`
  by `Classical.choice` on the two theorems.

## Mathematical content

For a non-archimedean local field `F` (a `IsNonarchimedeanLocalField`), an algebraic closure
`F̄`, residue field of cardinality `q` and characteristic `p`:

* `F^{nr} = F(μ_{p'})` (all roots of unity of order prime to `p`) is the maximal unramified
  extension, `I_F = Gal(F̄/F^{nr})` the inertia group, and the **Weil group** `W_F` consists of
  the `σ ∈ Gal(F̄/F)` acting on `μ_{p'}` as `ζ ↦ ζ^{q^n}` for some `n ∈ ℤ` (`weilDegree σ = n`,
  `‖σ‖ = q^n`; the arithmetic Frobenius has degree `1`).
* `ℓ` is a prime `≠ p`, `T_ℓ E = lim_n E(F̄)[ℓ^n]` is the Tate module (a `ℤ_ℓ`-module with a
  `Gal(F̄/F)`-action), and `V_ℓ E ⊗ Q̄_ℓ` is the associated `Q̄_ℓ`-linear Galois representation
  (`ellAdicRep`).
* The **Weil–Deligne representation** `σ'_E = (ρ, N)` is `(V_ℓ E, 0)` if `E` has potentially
  good reduction (`v(j) ≥ 0`), and `χ ⊗ sp(2)` with `χ` the quadratic character of
  `F(√(-c₆))/F` if `E` has potentially multiplicative reduction (`v(j) < 0`) (Serre–Tate,
  Tate curve; Rohrlich 1994, §§15–16).
* For every finite extension `L/F` inside `F̄`: the Weil group `W_L = W_F ∩ G_L`, the residue
  degree `f_L`, the normalised valuation `v_L`, the higher unit groups `U_L^{(a)}`, admissible
  additive characters `ψ` and their conductor exponents `n(ψ)`, conductor exponents `a(χ)` of
  characters `χ` of `L^×`, and **Tate's local constant** `ε(χ, ψ, dx)` of a character of `L^×`
  (Tate, *Number theoretic background*, (3.2.6)).
* Induced representations `Ind_{W_M}^{W_L}` and the one-dimensional representation attached to
  a character of `W_L`.
* The two structures `LocalReciprocity` and `LocalConstants` record exactly the characterising
  properties of the **local reciprocity map** (Milne, *Class Field Theory*, Thm I.1.1) and of
  Deligne's **local constants** (Langlands–Deligne; Deligne 1973, Thm 4.1; Tate 1979,
  Thm 3.4.1; Dokchitser, *Notes on the parity conjecture*, Thm 3.12).

## Conventions

* `‖·‖ : W_F → q^ℤ` is normalised by `‖Φ_arith‖ = q`, so `‖·‖` is the cyclotomic character
  and the Weil–Deligne relation reads `ρ(w) N ρ(w)⁻¹ = ‖w‖ N`.
* The reciprocity map is normalised so that uniformisers correspond to *geometric*
  Frobenius elements (Deligne's convention).
* The Haar measure is normalised by `dx(𝒪_L) = 1` on every finite extension `L/F`; this is
  harmless because the inductivity property only involves virtual representations of degree
  `0`, for which the measure cancels.
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Classical
open ValuativeRel

universe u

namespace EllipticRootNumber

/-! ## §0 Local-field structures on an abstract field -/

/-- A structure of non-archimedean local field on an abstract field `F`: a valuative relation
and a topology making `F` a `IsNonarchimedeanLocalField`. (On a field that admits one, this
structure is unique up to equivalence, by F. K. Schmidt's theorem; we only ever use it through
`Classical.choice`.) -/
structure LocalFieldStructure (F : Type u) [Field F] where
  /-- the valuative relation -/
  rel : ValuativeRel F
  /-- the topology -/
  top : TopologicalSpace F
  /-- `F` is a non-archimedean local field for these data -/
  isLocalField : @IsNonarchimedeanLocalField F _ rel top

section LocalField

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-! ## §1 Arithmetic of the local field -/

/-- The cardinality `q` of the residue field of `F`. -/
def q : ℕ := Nat.card 𝓀[F]

/-- The residue characteristic `p` of `F`. -/
def p : ℕ := ringChar 𝓀[F]

/-- The normalised additive valuation `v : F → ℤ` of the local field `F` (`v 0 = 0` by
convention), obtained from the value group `ValueGroupWithZero F ≃ ℤᵐ⁰`. -/
def addVal (x : F) : ℤ :=
  if h : x = 0 then 0
  else
    -Multiplicative.toAdd (WithZero.unzero
      (x := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F (valuation F x))
      (by
        have hx : valuation F x ≠ 0 := (Valuation.ne_zero_iff _).mpr h
        exact (map_ne_zero _).mpr hx))

/-- The algebraic closure `F̄` of `F`. -/
local notation "F̄" => AlgebraicClosure F

/-- The absolute Galois group `G_F = Gal(F̄/F)` (with its Krull topology). -/
abbrev AbsGal : Type u := F̄ ≃ₐ[F] F̄

/-- `ζ ∈ F̄` is a root of unity of order prime to the residue characteristic `p`. -/
def IsPrimeToPRootOfUnity (ζ : F̄) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ¬ p F ∣ n ∧ ζ ^ n = 1

/-- The maximal unramified extension `F^{nr} = F(μ_{p'}) ⊆ F̄` of `F`. -/
def unramifiedClosure : IntermediateField F F̄ :=
  IntermediateField.adjoin F {ζ | IsPrimeToPRootOfUnity F ζ}

/-- The (absolute) inertia subgroup `I_F = Gal(F̄/F^{nr}) ≤ G_F`. -/
def inertia : Subgroup (AbsGal F) := (unramifiedClosure F).fixingSubgroup

/-- `σ ∈ G_F` acts on the prime-to-`p` roots of unity as `ζ ↦ ζ^{q^n}` (`n ∈ ℤ`); for `n < 0`
this means `σ(ζ)^{q^{-n}} = ζ`. -/
def ActsAsFrobPow (σ : AbsGal F) (n : ℤ) : Prop :=
  ∀ ζ : F̄, IsPrimeToPRootOfUnity F ζ → σ ζ ^ (q F ^ (-n).toNat) = ζ ^ (q F ^ n.toNat)

/-- The **Weil group** `W_F ≤ G_F`: the elements acting on `μ_{p'}` by an integral power of
Frobenius. (The set of such elements is already a subgroup; we take its closure so that no
proof obligation is needed.) -/
def weilGroup : Subgroup (AbsGal F) :=
  Subgroup.closure {σ | ∃ n : ℤ, ActsAsFrobPow F σ n}

/-- The degree `deg σ ∈ ℤ` of `σ ∈ W_F`, i.e. the `n` with `σ|_{μ_{p'}} = (ζ ↦ ζ^{q^n})`
(`0` outside `W_F`). -/
def weilDegree (σ : AbsGal F) : ℤ :=
  if h : ∃ n : ℤ, ActsAsFrobPow F σ n then h.choose else 0

/-- An arithmetic Frobenius element `Φ ∈ W_F` (`deg Φ = 1`). -/
def arithFrob : AbsGal F := Classical.epsilon fun σ => ActsAsFrobPow F σ 1

/-- A geometric Frobenius element `Φ_geom = Φ⁻¹`. -/
def geomFrob : AbsGal F := (arithFrob F)⁻¹

/-! ## §2 The auxiliary prime `ℓ` and the coefficient field `Ω = Q̄_ℓ` -/

/-- A prime `ℓ ≠ p` (the least prime `> p`). -/
def ell : ℕ := (Nat.exists_infinite_primes (p F + 1)).choose

instance ell_prime : Fact (ell F).Prime :=
  ⟨(Nat.exists_infinite_primes (p F + 1)).choose_spec.2⟩

theorem ell_ne_p : ell F ≠ p F := by
  have h := (Nat.exists_infinite_primes (p F + 1)).choose_spec.1
  unfold ell
  omega

/-- The coefficient field `Ω = Q̄_ℓ`, an algebraic closure of `ℚ_ℓ`. -/
abbrev Ω : Type := AlgebraicClosure ℚ_[ell F]

/-- `‖σ‖ = q^{deg σ} ∈ Ω` for `σ ∈ W_F` (normalised by `‖Φ_arith‖ = q`; this is the cyclotomic
character of `W_F`). -/
def weilNorm (σ : AbsGal F) : Ω F := (q F : Ω F) ^ weilDegree F σ

/-! ## §3 Galois action on points, torsion and the Tate module -/

variable (E : WeierstrassCurve F)

/-- The group `E(F̄)` of `F̄`-points of `E`. -/
abbrev Pts : Type u := (E.baseChange F̄).toAffine.Point

/-- The action of `σ ∈ G_F` on `E(F̄)`. -/
def galHom (σ : AbsGal F) : Pts F E →+ Pts F E :=
  WeierstrassCurve.Affine.Point.map (W' := E) (σ : F̄ →ₐ[F] F̄)

theorem galHom_one (P : Pts F E) : galHom F E 1 P = P := by
  cases P <;> rfl

theorem galHom_mul (σ τ : AbsGal F) (P : Pts F E) :
    galHom F E (σ * τ) P = galHom F E σ (galHom F E τ P) := by
  cases P <;> rfl

/-- The `n`-torsion subgroup `E(F̄)[n]`. -/
def torsion (n : ℕ) : AddSubgroup (Pts F E) where
  carrier := {P | n • P = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [nsmul_add, ha, hb, add_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    simp [ha]

theorem mem_torsion {n : ℕ} {P : Pts F E} : P ∈ torsion F E n ↔ n • P = 0 := Iff.rfl

theorem galHom_mem_torsion (σ : AbsGal F) {n : ℕ} {P : Pts F E} (hP : P ∈ torsion F E n) :
    galHom F E σ P ∈ torsion F E n := by
  rw [mem_torsion] at *
  rw [← map_nsmul, hP, map_zero]

/-- `E(F̄)[ℓ^{n+1}]` is a `ℤ/ℓ^{n+1}`-module. -/
instance torsionZModModule (n : ℕ) :
    Module (ZMod (ell F ^ (n + 1))) (torsion F E (ell F ^ (n + 1))) :=
  AddCommGroup.zmodModule fun x => Subtype.ext (by
    rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]
    exact (mem_torsion F E).mp x.2)

/-- `E(F̄)[ℓ^{n+1}]` is a `ℤ_ℓ`-module through `ℤ_ℓ → ℤ/ℓ^{n+1}`. -/
instance torsionPadicModule (n : ℕ) : Module ℤ_[ell F] (torsion F E (ell F ^ (n + 1))) :=
  Module.compHom _ (PadicInt.toZModPow (n + 1))

theorem padic_smul_torsion (n : ℕ) (a : ℤ_[ell F]) (P : torsion F E (ell F ^ (n + 1))) :
    ((a • P : torsion F E (ell F ^ (n + 1))) : Pts F E) =
      (PadicInt.toZModPow (n + 1) a).val • (P : Pts F E) := by
  change (((PadicInt.toZModPow (n + 1) a) • P : torsion F E (ell F ^ (n + 1))) : Pts F E) = _
  conv_lhs => rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow (n + 1) a),
    Nat.cast_smul_eq_nsmul]
  rw [AddSubgroup.coe_nsmul]

/-- Multiples of a point of order dividing `m` only depend on the multiplier modulo `m`. -/
theorem nsmul_eq_of_modEq {m k₁ k₂ : ℕ} {P : Pts F E} (hP : m • P = 0) (h : k₁ ≡ k₂ [MOD m]) :
    k₁ • P = k₂ • P := by
  have e : ∀ k : ℕ, k • P = (k % m) • P := by
    intro k
    conv_lhs => rw [← Nat.mod_add_div k m]
    rw [add_nsmul, mul_nsmul, hP, nsmul_zero, add_zero]
  rw [e k₁, e k₂, h]

/-- Compatibility of the `ℤ_ℓ`-structures with multiplication by `ℓ`. -/
theorem padic_smul_compat (n : ℕ) (a : ℤ_[ell F]) (P : torsion F E (ell F ^ (n + 2)))
    (Q : torsion F E (ell F ^ (n + 1))) (h : ell F • (P : Pts F E) = (Q : Pts F E)) :
    ell F • ((a • P : torsion F E (ell F ^ (n + 2))) : Pts F E) =
      ((a • Q : torsion F E (ell F ^ (n + 1))) : Pts F E) := by
  rw [padic_smul_torsion, padic_smul_torsion, ← h, ← mul_nsmul, ← mul_nsmul]
  have hcast : PadicInt.toZModPow (n + 1) a = ZMod.cast (PadicInt.toZModPow (n + 2) a) :=
    (PadicInt.cast_toZModPow (n + 1) (n + 2) (by omega) a).symm
  rw [hcast, ZMod.cast_eq_val, ZMod.val_natCast]
  apply nsmul_eq_of_modEq F E ((mem_torsion F E).mp P.2)
  set c := (PadicInt.toZModPow (n + 2) a).val
  have hm : ell F ^ (n + 2) = ell F ^ (n + 1) * ell F := by ring
  rw [hm]
  calc c * ell F ≡ c % ell F ^ (n + 1) * ell F [MOD ell F ^ (n + 1) * ell F] :=
        Nat.ModEq.mul_right' _ (Nat.mod_modEq c _).symm
    _ = ell F * (c % ell F ^ (n + 1)) := mul_comm _ _

/-- The **Tate module** `T_ℓ E = lim_n E(F̄)[ℓ^{n+1}]` (compatible sequences under
multiplication by `ℓ`), as a `ℤ_ℓ`-submodule of `∏_n E(F̄)[ℓ^{n+1}]`. -/
def tateModule : Submodule ℤ_[ell F] (∀ n : ℕ, torsion F E (ell F ^ (n + 1))) where
  carrier := {x | ∀ n, ell F • ((x (n + 1) : torsion F E _) : Pts F E) = (x n : Pts F E)}
  zero_mem' := by intro n; simp
  add_mem' := by
    intro x y hx hy n
    simp only [Set.mem_setOf_eq] at *
    rw [Pi.add_apply, Pi.add_apply, AddSubgroup.coe_add, AddSubgroup.coe_add, nsmul_add, hx, hy]
  smul_mem' := by
    intro a x hx n
    simp only [Set.mem_setOf_eq] at *
    rw [Pi.smul_apply, Pi.smul_apply]
    exact padic_smul_compat F E n a _ _ (hx n)

theorem mem_tateModule {x : ∀ n : ℕ, torsion F E (ell F ^ (n + 1))} :
    x ∈ tateModule F E ↔
      ∀ n, ell F • ((x (n + 1) : torsion F E _) : Pts F E) = (x n : Pts F E) := Iff.rfl

/-- The (`ℤ_ℓ`-linear) action of `σ ∈ G_F` on `E(F̄)[ℓ^{n+1}]`. -/
def galTorsion (σ : AbsGal F) (n : ℕ) :
    torsion F E (ell F ^ (n + 1)) →ₗ[ℤ_[ell F]] torsion F E (ell F ^ (n + 1)) where
  toFun P := ⟨galHom F E σ P, galHom_mem_torsion F E σ P.2⟩
  map_add' P Q := Subtype.ext (map_add _ _ _)
  map_smul' a P := Subtype.ext (by
    change galHom F E σ ((a • P : torsion F E _) : Pts F E) =
      ((a • (⟨galHom F E σ P, galHom_mem_torsion F E σ P.2⟩ : torsion F E _) :
        torsion F E _) : Pts F E)
    rw [padic_smul_torsion, padic_smul_torsion, map_nsmul])

/-- The action of `σ ∈ G_F` on `∏_n E(F̄)[ℓ^{n+1}]`. -/
def galPi (σ : AbsGal F) :
    (∀ n : ℕ, torsion F E (ell F ^ (n + 1))) →ₗ[ℤ_[ell F]]
      (∀ n : ℕ, torsion F E (ell F ^ (n + 1))) :=
  LinearMap.pi fun n => (galTorsion F E σ n).comp (LinearMap.proj n)

theorem galPi_mem_tateModule (σ : AbsGal F) {x : ∀ n : ℕ, torsion F E (ell F ^ (n + 1))}
    (hx : x ∈ tateModule F E) : galPi F E σ x ∈ tateModule F E := by
  intro n
  change ell F • galHom F E σ (x (n + 1) : Pts F E) = galHom F E σ (x n : Pts F E)
  rw [← map_nsmul, hx n]

/-- The action of `σ ∈ G_F` on the Tate module `T_ℓ E`. -/
def galTate (σ : AbsGal F) : tateModule F E →ₗ[ℤ_[ell F]] tateModule F E :=
  (galPi F E σ).restrict fun _ hx => galPi_mem_tateModule F E σ hx

/-- The **`ℓ`-adic Tate representation** `G_F → Aut_{ℤ_ℓ}(T_ℓ E)`. -/
def tateRep : Representation ℤ_[ell F] (AbsGal F) (tateModule F E) where
  toFun := galTate F E
  map_one' := LinearMap.ext fun _ =>
    Subtype.ext (funext fun _ => Subtype.ext (galHom_one F E _))
  map_mul' σ τ := LinearMap.ext fun _ =>
    Subtype.ext (funext fun _ => Subtype.ext (galHom_mul F E σ τ _))

/-- `V_ℓ E = ℚ_ℓ ⊗_{ℤ_ℓ} T_ℓ E`. -/
abbrev VQ : Type u := TensorProduct ℤ_[ell F] ℚ_[ell F] (tateModule F E)

/-- `V̄_ℓ E = Q̄_ℓ ⊗_{ℚ_ℓ} V_ℓ E`. -/
abbrev VBar : Type u := TensorProduct ℚ_[ell F] (Ω F) (VQ F E)

/-- The **`ℓ`-adic Galois representation** of `G_F` on `V̄_ℓ E = Q̄_ℓ ⊗ V_ℓ E`. -/
def ellAdicRep : Representation (Ω F) (AbsGal F) (VBar F E) where
  toFun σ := LinearMap.baseChange (Ω F) (LinearMap.baseChange ℚ_[ell F] (tateRep F E σ))
  map_one' := by
    rw [map_one, Module.End.one_eq_id, LinearMap.baseChange_id, LinearMap.baseChange_id]
    rfl
  map_mul' σ τ := by
    rw [map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp, LinearMap.baseChange_comp]
    rfl

/-! ## §4 Weil groups of the finite extensions of `F` inside `F̄` -/

variable (L : IntermediateField F (AlgebraicClosure F))

/-- The Weil group `W_L = W_F ∩ G_L` of the intermediate field `L`. -/
def relWeil : Subgroup (AbsGal F) := weilGroup F ⊓ L.fixingSubgroup

theorem relWeil_le_weilGroup : relWeil F L ≤ weilGroup F := inf_le_left

theorem relWeil_antitone {L M : IntermediateField F F̄} (h : L ≤ M) :
    relWeil F M ≤ relWeil F L :=
  inf_le_inf_left _ (IntermediateField.fixingSubgroup_le h)

/-- The degree homomorphism `deg : W_F → ℤ`: the (unique) homomorphism agreeing with the
Frobenius-power degree `ActsAsFrobPow` on the generators of `W_F`. -/
def weilDegreeHom : weilGroup F →* Multiplicative ℤ :=
  Classical.epsilon fun f : weilGroup F →* Multiplicative ℤ =>
    ∀ (σ : weilGroup F) (n : ℤ), ActsAsFrobPow F σ n → f σ = Multiplicative.ofAdd n

theorem q_pos : 0 < q F := Nat.card_pos

/-- `q` as a unit of `Ω`. -/
def qUnit : (Ω F)ˣ :=
  Units.mk0 (q F : Ω F) (by exact_mod_cast (q_pos F).ne')

/-- The norm character `‖·‖ : W_F → Ωˣ`, `‖w‖ = q^{deg w}` (so `‖Φ_arith‖ = q`; this is the
cyclotomic character). -/
def weilNormHom : weilGroup F →* (Ω F)ˣ :=
  (zpowersHom (Ω F)ˣ (qUnit F)).comp (weilDegreeHom F)

/-- The norm character restricted to `W_L`. -/
def relNorm : relWeil F L →* (Ω F)ˣ :=
  (weilNormHom F).comp (Subgroup.inclusion (relWeil_le_weilGroup F L))

/-- A geometric Frobenius element `Φ_L ∈ W_L` (an element of degree `-f_L` where `f_L` is the
residue degree, see `resDeg`). Only used through Deligne's formula (8.12), which does not
depend on the choice. -/
def geomFrobL (f : ℕ) : relWeil F L :=
  Classical.epsilon fun w : relWeil F L =>
    weilDegreeHom F (Subgroup.inclusion (relWeil_le_weilGroup F L) w) =
      Multiplicative.ofAdd (-(f : ℤ))

/-! ## §5 The Weil–Deligne representation `σ'_E` -/

/-- A **Weil–Deligne representation** of `W_L` over `Ω`: a representation `ρ` of `W_L` on an
`Ω`-vector space `V` together with an endomorphism `N` (the monodromy operator). The conditions
(finite dimensionality, `ρ` trivial on an open subgroup of inertia, `N` nilpotent,
`ρ(w) N ρ(w)⁻¹ = ‖w‖ N`) are recorded by the predicates `IsWeilRep` and `IsWDRep`. -/
structure WDRep where
  /-- the underlying vector space -/
  V : Type u
  [addCommGroup : AddCommGroup V]
  [module : Module (Ω F) V]
  /-- the representation of the Weil group -/
  ρ : Representation (Ω F) (relWeil F L) V
  /-- the monodromy operator -/
  N : V →ₗ[Ω F] V

attribute [instance] WDRep.addCommGroup WDRep.module

/-- A representation of `W_L` is a *Weil representation* if it is finite dimensional and trivial
on an open subgroup of the inertia group `I_L = I_F ∩ G_L`. -/
def IsWeilRep {V : Type u} [AddCommGroup V] [Module (Ω F) V]
    (ρ : Representation (Ω F) (relWeil F L) V) : Prop :=
  FiniteDimensional (Ω F) V ∧
    ∃ U ∈ nhds (1 : AbsGal F), ∀ w : relWeil F L, (w : AbsGal F) ∈ U →
      (w : AbsGal F) ∈ inertia F → ρ w = 1

/-- A Weil–Deligne representation is *admissible* if `ρ` is a Weil representation, `N` is
nilpotent and `ρ(w) N ρ(w)⁻¹ = ‖w‖ N`. -/
def IsWDRep (σ' : WDRep F L) : Prop :=
  IsWeilRep F L σ'.ρ ∧ IsNilpotent σ'.N ∧
    ∀ w : relWeil F L, σ'.ρ w ∘ₗ σ'.N ∘ₗ σ'.ρ w⁻¹ = (relNorm F L w : Ω F) • σ'.N

/-- `E` has *potentially good reduction*: the `j`-invariant `c₄³/Δ` is integral. -/
def IsPotentiallyGood : Prop := valuation F (E.c₄ ^ 3 / E.Δ) ≤ 1

/-- A square root `s ∈ F̄` of `-c₆(E)`. -/
def sqrtNegC₆ : F̄ :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (algebraMap F F̄ (-E.c₆)) two_pos)

theorem sqrtNegC₆_sq : sqrtNegC₆ F E ^ 2 = algebraMap F F̄ (-E.c₆) :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (algebraMap F F̄ (-E.c₆)) two_pos)

theorem apply_sqrtNegC₆ (σ : AbsGal F) :
    σ (sqrtNegC₆ F E) = sqrtNegC₆ F E ∨ σ (sqrtNegC₆ F E) = -sqrtNegC₆ F E := by
  have h : σ (sqrtNegC₆ F E) ^ 2 = sqrtNegC₆ F E ^ 2 := by
    rw [← map_pow, sqrtNegC₆_sq, AlgEquiv.commutes]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp h

/-- The sign `χ(σ) = σ(s)/s ∈ {±1}` for `s = √(-c₆)`. -/
def quadSign (σ : AbsGal F) : ℤˣ := if σ (sqrtNegC₆ F E) = sqrtNegC₆ F E then 1 else -1

theorem quadSign_mul (σ τ : AbsGal F) :
    quadSign F E (σ * τ) = quadSign F E σ * quadSign F E τ := by
  unfold quadSign
  rw [AlgEquiv.mul_apply]
  rcases apply_sqrtNegC₆ F E τ with hτ | hτ
  · rw [hτ]
    simp
  · rw [hτ, map_neg]
    by_cases hns : -sqrtNegC₆ F E = sqrtNegC₆ F E
    · have h1 : -σ (sqrtNegC₆ F E) = σ (sqrtNegC₆ F E) := by rw [← map_neg, hns]
      rw [h1, if_pos hns, mul_one]
    · rw [if_neg hns, mul_neg_one]
      rcases apply_sqrtNegC₆ F E σ with hσ | hσ
      · rw [hσ, if_neg hns]
        simp
      · rw [hσ, neg_neg, if_neg hns]
        simp

/-- The **quadratic character** `χ : G_F → {±1}` of `F(√(-c₆(E)))/F`. -/
def quadChar : AbsGal F →* ℤˣ where
  toFun := quadSign F E
  map_one' := by simp [quadSign]
  map_mul' := quadSign_mul F E

/-- The special representation `sp(2)` twisted by a character `χ`, on `V = Ω e₀ ⊕ Ω e₁`
(realised as `Fin 2 → ULift Ω` for universe reasons):
`ρ(w) e₀ = χ(w) e₀`, `ρ(w) e₁ = χ(w) ‖w‖ e₁`. -/
def spTwistRep (χ : relWeil F L →* (Ω F)ˣ) :
    Representation (Ω F) (relWeil F L) (Fin 2 → ULift.{u} (Ω F)) where
  toFun w := LinearMap.pi fun i =>
    ((χ w : Ω F) * if i = 0 then 1 else (relNorm F L w : Ω F)) • LinearMap.proj i
  map_one' := by
    apply LinearMap.ext
    intro v
    funext i
    simp
  map_mul' σ τ := by
    apply LinearMap.ext
    intro v
    funext i
    simp only [LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      Module.End.mul_apply, map_mul, Units.val_mul, smul_smul]
    congr 1
    split_ifs <;> ring

/-- The monodromy operator of `sp(2)`: `N e₀ = e₁`, `N e₁ = 0`. -/
def spN : (Fin 2 → ULift.{u} (Ω F)) →ₗ[Ω F] (Fin 2 → ULift.{u} (Ω F)) :=
  LinearMap.pi fun i => if i = 1 then LinearMap.proj 0 else 0

/-- The quadratic character of `F(√(-c₆))` as a character of `W_L` with values in `Ωˣ`. -/
def quadCharΩ : relWeil F L →* (Ω F)ˣ :=
  ((Units.map (Int.castRingHom (Ω F)).toMonoidHom).comp (quadChar F E)).comp
    (relWeil F L).subtype

/-- The **Weil–Deligne representation `σ'_E`** of `E/F` (as a representation of
`W_F = W_{⊥}`):
* if `E` has potentially good reduction, `σ'_E = (V̄_ℓ E, N = 0)` (the `ℓ`-adic representation
  restricted to `W_F`; by Serre–Tate the inertia group acts through a finite quotient);
* otherwise (`v(j) < 0`, potentially multiplicative reduction), `σ'_E = χ ⊗ sp(2)` where `χ` is
  the quadratic character of `F(√(-c₆))/F` (Tate curve).
(Rohrlich, *Elliptic curves and the Weil–Deligne group*, §§15–16.) -/
def wdRep : WDRep F ⊥ :=
  if IsPotentiallyGood F E then
    { V := VBar F E
      ρ := (ellAdicRep F E).comp (relWeil F ⊥).subtype
      N := 0 }
  else
    { V := Fin 2 → ULift.{u} (Ω F)
      ρ := spTwistRep F ⊥ (quadCharΩ F E ⊥)
      N := spN F }

/-! ## §6 Arithmetic of the finite extensions `L/F` inside `F̄`

All the invariants of `L` are expressed through `F`: `ṽ_L(x) = v_F(N_{L/F} x)` is `f_L` times the
normalised valuation `v_L` of `L`, where the residue degree `f_L` is the positive generator of
`ṽ_L(L^×) ⊆ ℤ`; `q_L = q^{f_L}`. -/

/-- `ṽ_L(x) = v_F(N_{L/F}(x)) ∈ ℤ`. -/
def relVal (x : L) : ℤ := addVal F (Algebra.norm F x)

/-- The residue degree `f_L` of `L/F`: the positive generator of `ṽ_L(L^×)`. -/
def resDeg : ℕ := sInf {k : ℕ | 0 < k ∧ ∃ x : L, x ≠ 0 ∧ relVal F L x = k}

/-- The normalised valuation `v_L = ṽ_L / f_L` of `L`. -/
def valL (x : L) : ℤ := relVal F L x / resDeg F L

/-- The residue cardinality `q_L = q^{f_L}` of `L`. -/
def qL : ℕ := q F ^ resDeg F L

/-- The higher unit groups `U_L^{(a)} ≤ L^×`: `U^{(0)} = 𝒪_L^×` and `U^{(a)} = 1 + 𝔭_L^a` for
`a ≥ 1` (as the subgroup generated by the corresponding set, which is already a subgroup). -/
def unitGroup (a : ℕ) : Subgroup Lˣ :=
  Subgroup.closure {u : Lˣ |
    if a = 0 then valL F L u = 0 else ((u : L) = 1 ∨ (a : ℤ) ≤ valL F L ((u : L) - 1))}

/-- An additive character `ψ : L → Ω^×` is *admissible* if it is nontrivial and locally constant
(trivial on some `𝔭_L^d`). -/
def IsAdmissibleChar (ψ : AddChar L (Ω F)) : Prop :=
  ψ ≠ 1 ∧ ∃ d : ℤ, ∀ x : L, d ≤ valL F L x → ψ x = 1

/-- The conductor exponent `n(ψ)` of an additive character: the largest `d` such that `ψ` is
trivial on `𝔭_L^{-d}`. -/
def condExpChar (ψ : AddChar L (Ω F)) : ℤ :=
  sSup {d : ℤ | ∀ x : L, -d ≤ valL F L x → ψ x = 1}

/-- The conductor exponent `a(χ)` of a character `χ : L^× → Ω^×`: the least `a` with `χ` trivial
on `U_L^{(a)}`. -/
def condExp (χ : Lˣ →* (Ω F)ˣ) : ℕ := sInf {a : ℕ | ∀ u ∈ unitGroup F L a, χ u = 1}

/-- A chosen representative of a coset in `G ⧸ H`. -/
def cosetRep {G : Type*} [Group G] {H : Subgroup G} (u : G ⧸ H) : G :=
  @Quotient.out G (QuotientGroup.leftRel H) u

/-- An element `c ∈ L^×` with `v_L(c) = a(χ) + n(ψ)`. -/
def tateElt (χ : Lˣ →* (Ω F)ˣ) (ψ : AddChar L (Ω F)) : Lˣ :=
  Classical.epsilon fun c : Lˣ => valL F L c = condExp F L χ + condExpChar F L ψ

/-- **Tate's local constant** `ε(χ, ψ, dx)` of a character `χ` of `L^×`, for the Haar measure
with `dx(𝒪_L) = 1` (Tate, *Number theoretic background*, (3.2.6)): with `v_L(c) = a(χ) + n(ψ)`,
* `ε = χ(c) q_L^{n(ψ)}` if `χ` is unramified,
* `ε = q_L^{n(ψ)} ∑_{u ∈ 𝒪_L^×/U^{(a(χ))}} χ⁻¹(c⁻¹u) ψ(c⁻¹u)` otherwise (a Gauss sum). -/
def tateEps (χ : Lˣ →* (Ω F)ˣ) (ψ : AddChar L (Ω F)) : Ω F :=
  (qL F L : Ω F) ^ condExpChar F L ψ *
    if condExp F L χ = 0 then (χ (tateElt F L χ ψ) : Ω F)
    else
      ∑ᶠ (u : Lˣ ⧸ unitGroup F L (condExp F L χ)) (_ : valL F L ((cosetRep u : Lˣ) : L) = 0),
        ((χ ((tateElt F L χ ψ)⁻¹ * (cosetRep u : Lˣ)) : Ω F)⁻¹ *
          ψ ((((tateElt F L χ ψ)⁻¹ * (cosetRep u : Lˣ) : Lˣ) : L)))

/-- For `L ≤ M`, the element `y ∈ M` viewed in `M` as an `L`-algebra (`M.extendScalars h`). -/
def toExtendScalars {L M : IntermediateField F (AlgebraicClosure F)} (h : L ≤ M) :
    M →+* (IntermediateField.extendScalars h) where
  toFun y := ⟨y.1, (IntermediateField.mem_extendScalars h).mpr y.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The trace `Tr_{M/L} : M → L` for `L ≤ M`. -/
def traceLM {L M : IntermediateField F (AlgebraicClosure F)} (h : L ≤ M) : M →+ L :=
  (Algebra.trace L (IntermediateField.extendScalars h)).toAddMonoidHom.comp
    (toExtendScalars F h).toAddMonoidHom

/-- The norm `N_{M/L} : M → L` for `L ≤ M`. -/
def normLM {L M : IntermediateField F (AlgebraicClosure F)} (h : L ≤ M) : M →* L :=
  (Algebra.norm L (S := IntermediateField.extendScalars h)).comp (toExtendScalars F h).toMonoidHom

/-- `ψ ∘ Tr_{M/L}`. -/
def traceChar {L M : IntermediateField F (AlgebraicClosure F)} (h : L ≤ M)
    (ψ : AddChar L (Ω F)) : AddChar M (Ω F) :=
  ψ.compAddMonoidHom (traceLM F h)

/-- `M/L` is a finite abelian (Galois) extension, expressed inside `G_F`: `G_M` is normal in `G_L`
with abelian quotient, and `M/L` is separable. -/
def IsAbelianExt {L M : IntermediateField F (AlgebraicClosure F)} (h : L ≤ M) : Prop :=
  (∀ σ ∈ L.fixingSubgroup, ∀ τ ∈ M.fixingSubgroup, σ * τ * σ⁻¹ ∈ M.fixingSubgroup) ∧
  (∀ σ ∈ L.fixingSubgroup, ∀ τ ∈ L.fixingSubgroup, σ * τ * σ⁻¹ * τ⁻¹ ∈ M.fixingSubgroup) ∧
  Algebra.IsSeparable L (IntermediateField.extendScalars h)

/-! ## §7 Induced representations and one-dimensional representations -/

section Induced

variable {k : Type*} [Field k] {G : Type u} [Group G] (H : Subgroup G)
  {V : Type u} [AddCommGroup V] [Module k V]

/-- The space of the induced representation `Ind_H^G V`: functions `f : G → V` with
`f(h g) = ρ(h) f(g)`. -/
def indSpace (ρ : Representation k H V) : Submodule k (G → V) where
  carrier := {f | ∀ (h : H) (g : G), f ((h : G) * g) = ρ h (f g)}
  zero_mem' := fun _ _ => by simp
  add_mem' := fun {f₁ f₂} h₁ h₂ h g => by simp [h₁ h g, h₂ h g]
  smul_mem' := fun c f hf h g => by simp [hf h g]

/-- The induced representation `Ind_H^G ρ`, `G` acting by right translation. -/
def indRep (ρ : Representation k H V) : Representation k G (indSpace H ρ) where
  toFun g := (LinearMap.funLeft k V fun x => x * g).restrict fun f hf h x => by
    change f ((h : G) * x * g) = ρ h (f (x * g))
    rw [mul_assoc]
    exact hf h (x * g)
  map_one' := LinearMap.ext fun f => Subtype.ext (funext fun x => by
    simp [LinearMap.funLeft_apply])
  map_mul' g₁ g₂ := LinearMap.ext fun f => Subtype.ext (funext fun x => by
    simp [LinearMap.funLeft_apply, mul_assoc])

end Induced

/-- `Ind_{W_M}^{W_L}` of a representation of `W_M`, for `L ≤ M`. -/
def indLM {L M : IntermediateField F (AlgebraicClosure F)} (h : L ≤ M) {V : Type u}
    [AddCommGroup V] [Module (Ω F) V] (σ : Representation (Ω F) (relWeil F M) V) :
    Representation (Ω F) (relWeil F L)
      (indSpace ((relWeil F M).subgroupOf (relWeil F L))
        (σ.comp (Subgroup.subgroupOfEquivOfLe (relWeil_antitone F h)).toMonoidHom)) :=
  indRep _ _

/-- The one-dimensional representation attached to a character `χ : W_L → Ω^×`. -/
def charRep (χ : relWeil F L →* (Ω F)ˣ) :
    Representation (Ω F) (relWeil F L) (ULift.{u} (Ω F)) where
  toFun w := (χ w : Ω F) • LinearMap.id
  map_one' := by
    rw [map_one, Units.val_one, one_smul]
    rfl
  map_mul' σ τ := LinearMap.ext fun v => by
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_apply, map_mul,
      Units.val_mul, smul_smul]

/-! ## §8 Local class field theory and Deligne's local constants (the two assumed theorems)

The definition of the root number rests on two classical existence theorems, which are stated
(with `sorry`) in `local_reciprocity.lean` and `langlands_deligne.lean` in terms
of the two structures below. Each structure records exactly the characterising properties of
the object whose existence is asserted, so that `Nonempty (LocalReciprocity F)` *is* the
statement of local class field theory and `Nonempty (LocalConstants F rec)` *is* the
statement of the Langlands–Deligne theorem. -/

/-- **The local reciprocity map** (local class field theory: Milne, *Class Field Theory*,
Thm I.1.1; Serre, *Local class field theory*, §2.3 in Cassels–Fröhlich; Neukirch, *Algebraic
Number Theory*, Thm V.1.3), in Deligne's normalisation (uniformisers ↦ geometric Frobenius).

For every finite extension `L/F` inside `F̄`, the reciprocity homomorphism
`rec_L : L^× → W_L^{ab}` is recorded through a set-theoretic lift `recMap L : L^× → W_L`
(the lift is only well defined modulo the closed commutator subgroup of `W_L`, and only its
images in the finite quotients `W_L/W_M = Gal(M/L)`, `M/L` finite abelian, are ever used, so
the choice of lift is immaterial). The characterising properties are:
* `deg (rec_L x) = -ṽ_L(x) = -f_L · v_L(x)` (so units go to inertia and uniformisers to
  geometric Frobenius elements of `L`) — `degree_rec`;
* for every finite abelian `M/L`, `x ↦ rec_L x mod W_M` is a homomorphism
  `L^× → W_L/W_M = Gal(M/L)` (`mul_rec`), which is surjective (`surj_rec`) with kernel the
  norm group `N_{M/L}(M^×)` (`ker_rec`).
These properties determine `x ↦ rec_L x mod W_M` uniquely for every finite abelian `M/L`
(Milne, loc. cit.). -/
structure LocalReciprocity where
  /-- a lift to `W_L` of the reciprocity map `rec_L : L^× → W_L^{ab}` -/
  recMap : ∀ L : IntermediateField F (AlgebraicClosure F), Lˣ → relWeil F L
  /-- `deg (rec_L x) = -ṽ_L(x)` -/
  degree_rec : ∀ (L : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F L]
    (x : Lˣ), weilDegreeHom F (Subgroup.inclusion (relWeil_le_weilGroup F L) (recMap L x)) =
      Multiplicative.ofAdd (-relVal F L x)
  /-- `rec_L` is multiplicative modulo `W_M` for every finite abelian `M/L` -/
  mul_rec : ∀ (L M : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F M]
    (h : L ≤ M), IsAbelianExt F h → ∀ x y : Lˣ,
      (((recMap L (x * y))⁻¹ * (recMap L x * recMap L y) : relWeil F L) : AbsGal F) ∈
        M.fixingSubgroup
  /-- the kernel of `L^× → Gal(M/L)` is the norm group `N_{M/L}(M^×)` -/
  ker_rec : ∀ (L M : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F M]
    (h : L ≤ M), IsAbelianExt F h → ∀ x : Lˣ,
      (recMap L x : AbsGal F) ∈ M.fixingSubgroup ↔ (x : L) ∈ Set.range (normLM F h)
  /-- `L^× → Gal(M/L)` is surjective -/
  surj_rec : ∀ (L M : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F M]
    (h : L ≤ M), IsAbelianExt F h → ∀ w : relWeil F L, ∃ x : Lˣ,
      (((recMap L x)⁻¹ * w : relWeil F L) : AbsGal F) ∈ M.fixingSubgroup

/-- **Deligne's local constants** (Langlands–Deligne; Deligne 1973, Théorème 4.1; Tate 1979,
Theorem 3.4.1; Dokchitser, *Notes on the parity conjecture*, Theorem 3.12), for the Haar
measures normalised by `dx(𝒪_L) = 1`: a rule `ε` assigning to every finite extension `L/F`
inside `F̄`, every representation of `W_L` on an `Ω`-vector space and every additive character
`ψ` of `L` a constant `ε(σ, ψ) ∈ Ω^×`, such that on Weil representations and admissible `ψ`
* `ε` is multiplicative in short exact sequences (`eps_exact`);
* `ε` is inductive in degree `0` for finite separable `M/L` (`eps_ind`);
* on one-dimensional representations `ε` is given by Tate's formula, via the local reciprocity
  map (`eps_char`).
These properties characterise `ε` uniquely (Deligne 1973, §4; Dokchitser, Remark 3.13). -/
structure LocalConstants (rec : LocalReciprocity F) where
  /-- the local constant `ε(σ, ψ, dx)` -/
  eps : ∀ (L : IntermediateField F (AlgebraicClosure F)) {V : Type u} [AddCommGroup V]
    [Module (Ω F) V], Representation (Ω F) (relWeil F L) V → AddChar L (Ω F) → (Ω F)ˣ
  /-- multiplicativity in short exact sequences `0 → σ₁ → σ → σ₂ → 0` -/
  eps_exact : ∀ (L : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F L]
    (ψ : AddChar L (Ω F)), IsAdmissibleChar F L ψ →
    ∀ {V₁ V V₂ : Type u} [AddCommGroup V₁] [Module (Ω F) V₁] [AddCommGroup V] [Module (Ω F) V]
      [AddCommGroup V₂] [Module (Ω F) V₂]
      (σ₁ : Representation (Ω F) (relWeil F L) V₁) (σ : Representation (Ω F) (relWeil F L) V)
      (σ₂ : Representation (Ω F) (relWeil F L) V₂),
      IsWeilRep F L σ₁ → IsWeilRep F L σ → IsWeilRep F L σ₂ →
      ∀ (f : V₁ →ₗ[Ω F] V) (g : V →ₗ[Ω F] V₂),
        (∀ w, f ∘ₗ σ₁ w = σ w ∘ₗ f) → (∀ w, g ∘ₗ σ w = σ₂ w ∘ₗ g) →
        Function.Injective f → Function.Surjective g → LinearMap.range f = LinearMap.ker g →
        eps L σ ψ = eps L σ₁ ψ * eps L σ₂ ψ
  /-- inductivity in degree `0`: for `L ≤ M` finite separable and `σ₁, σ₂` of the same
  dimension, `ε(Ind σ₁, ψ) / ε(Ind σ₂, ψ) = ε(σ₁, ψ ∘ Tr) / ε(σ₂, ψ ∘ Tr)` -/
  eps_ind : ∀ (L M : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F M]
    (h : L ≤ M), Algebra.IsSeparable L (IntermediateField.extendScalars h) →
    ∀ (ψ : AddChar L (Ω F)), IsAdmissibleChar F L ψ →
    ∀ {V₁ V₂ : Type u} [AddCommGroup V₁] [Module (Ω F) V₁] [AddCommGroup V₂] [Module (Ω F) V₂]
      (σ₁ : Representation (Ω F) (relWeil F M) V₁) (σ₂ : Representation (Ω F) (relWeil F M) V₂),
      IsWeilRep F M σ₁ → IsWeilRep F M σ₂ →
      Module.finrank (Ω F) V₁ = Module.finrank (Ω F) V₂ →
      eps L (indLM F h σ₁) ψ * eps M σ₂ (traceChar F h ψ) =
        eps L (indLM F h σ₂) ψ * eps M σ₁ (traceChar F h ψ)
  /-- Tate's formula on characters: if `χ : W_L → Ω^×` is a Weil character and
  `χ' : L^× → Ω^×` is the character `χ ∘ rec_L`, then `ε(χ, ψ, dx) = ε_Tate(χ', ψ, dx)` -/
  eps_char : ∀ (L : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F L]
    (ψ : AddChar L (Ω F)), IsAdmissibleChar F L ψ →
    ∀ χ : relWeil F L →* (Ω F)ˣ, IsWeilRep F L (charRep F L χ) →
    ∀ χ' : Lˣ →* (Ω F)ˣ, (∀ x : Lˣ, χ' x = χ (rec.recMap L x)) →
      (eps L (charRep F L χ) ψ : Ω F) = tateEps F L χ' ψ

end LocalField

end EllipticRootNumber
