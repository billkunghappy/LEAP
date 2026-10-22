import Mathlib
import Hilbert10Defs
set_option maxHeartbeats 4000000

/-! ### Statement (originally `northcott_theorem.lean`) -/

/--
**Northcott's theorem.** For a number field `K` and a bound `B`, there are only
finitely many `x ∈ K` of logarithmic height at most `B`.
-/

theorem northcott_theorem {K : Type u} [Field K] [NumberField K] (B : ℝ) :
    {x : K | Height.logHeight₁ x ≤ B}.Finite :=
by
  classical
  let R := NumberField.RingOfIntegers K
  have h_arch : ∀ (x : K) (φ : K →+* ℂ), ‖φ x‖ ≤ Height.mulHeight₁ x := by
    intro x φ
    let v₀ : NumberField.InfinitePlace K := NumberField.InfinitePlace.mk φ
    have hv₀ : v₀ x = ‖φ x‖ := NumberField.InfinitePlace.apply φ x
    let f : NumberField.InfinitePlace K → ℝ := fun v => max (v x) 1 ^ v.mult
    have hf_one : ∀ v, 1 ≤ f v := fun v => one_le_pow₀ (le_max_right _ _)
    have h1 : ‖φ x‖ ≤ f v₀ := by
      calc ‖φ x‖ = v₀ x := hv₀.symm
        _ ≤ max (v₀ x) 1 := le_max_left _ _
        _ ≤ max (v₀ x) 1 ^ v₀.mult :=
          le_self_pow₀ (le_max_right _ _) NumberField.InfinitePlace.mult_ne_zero
    have h2 : f v₀ ≤ ∏ v : NumberField.InfinitePlace K, f v := by
      rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ v₀)]
      have hprod : 1 ≤ ∏ v ∈ Finset.univ.erase v₀, f v :=
        Finset.one_le_prod (Finset.univ.erase v₀) hf_one
      nlinarith [hf_one v₀]
    have h3 : 1 ≤ ∏ᶠ w : NumberField.FinitePlace K, max (w x) 1 :=
      one_le_finprod (fun w => le_max_right _ _)
    have hprod_inf : 1 ≤ ∏ v : NumberField.InfinitePlace K, f v :=
      Finset.one_le_prod Finset.univ hf_one
    rw [NumberField.mulHeight₁_eq x]
    change ‖φ x‖ ≤ (∏ v : NumberField.InfinitePlace K, f v) * ∏ᶠ w : NumberField.FinitePlace K, max (w x) 1
    nlinarith
  have h_ideal_den : ∀ {a b : R}, a ≠ 0 → b ≠ 0 →
      ∃ D : Ideal R, D ≠ ⊥ ∧
        D * Ideal.span {a} ≤ Ideal.span {b} ∧
        ∀ v : IsDedekindDomain.HeightOneSpectrum R,
          v.maxPowDividing D = 1 ∨
          v.maxPowDividing D * v.maxPowDividing (Ideal.span {a}) = v.maxPowDividing (Ideal.span {b}) := by
    intro a b ha hb
    let Ia : Ideal R := Ideal.span {a}
    let Ib : Ideal R := Ideal.span {b}
    have hIa : Ia ≠ ⊥ := by simpa [Ia, Ideal.span_singleton_eq_bot] using ha
    have hIb : Ib ≠ ⊥ := by simpa [Ib, Ideal.span_singleton_eq_bot] using hb
    let M : Multiset (Ideal R) :=
      UniqueFactorizationMonoid.normalizedFactors Ib - UniqueFactorizationMonoid.normalizedFactors Ia
    let D : Ideal R := M.prod
    have hD_sup : D * (Ib ⊔ Ia) = Ib := by
      rw [sup_eq_prod_inf_factors hIb hIa]
      dsimp [D, M]
      rw [← Multiset.prod_add, Multiset.sub_add_inter,
        prod_normalizedFactors_eq_self hIb]
    have hD_ne : D ≠ ⊥ := by
      intro h0
      apply hIb
      rw [← hD_sup, h0, Ideal.bot_mul]
    have hD_le : D * Ia ≤ Ib := by
      calc D * Ia ≤ D * (Ib ⊔ Ia) := Ideal.mul_mono_right le_sup_right
        _ = Ib := hD_sup
    have hM_prime : ∀ p ∈ M, Prime p := by
      intro p hp
      exact UniqueFactorizationMonoid.prime_of_normalized_factor p
        (Multiset.mem_of_le (Multiset.sub_le_self _ _) hp)
    have hD_factors : UniqueFactorizationMonoid.normalizedFactors D = M :=
      UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hM_prime
    refine ⟨D, hD_ne, hD_le, fun v => ?_⟩
    rw [v.maxPowDividing_eq_pow_multiset_count hD_ne,
      v.maxPowDividing_eq_pow_multiset_count hIa,
      v.maxPowDividing_eq_pow_multiset_count hIb, hD_factors]
    dsimp [M]
    rw [Multiset.count_sub]
    set ea := Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors Ia)
    set eb := Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors Ib)
    rcases Nat.le_total eb ea with hle | hle
    · left
      rw [Nat.sub_eq_zero_of_le hle, pow_zero]
    · right
      rw [← pow_add, Nat.sub_add_cancel hle]
  have h_absNorm_le : ∀ {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) {D : Ideal R} (hD : D ≠ ⊥),
      (∀ v : IsDedekindDomain.HeightOneSpectrum R,
        v.maxPowDividing D = 1 ∨
        v.maxPowDividing D * v.maxPowDividing (Ideal.span {a}) = v.maxPowDividing (Ideal.span {b})) →
      (Ideal.absNorm D : ℝ) ≤ Height.mulHeight₁ (algebraMap R K a / algebraMap R K b) := by
    intro a b ha hb D hD hD_dich
    let x : K := algebraMap R K a / algebraMap R K b
    have ha_K : algebraMap R K a ≠ 0 :=
      (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr ha
    have hb_K : algebraMap R K b ≠ 0 :=
      (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr hb
    have hx : x ≠ 0 := div_ne_zero ha_K hb_K
    let f : IsDedekindDomain.HeightOneSpectrum R → ℝ :=
      fun v => (Ideal.absNorm (v.maxPowDividing D) : ℝ)
    let g : IsDedekindDomain.HeightOneSpectrum R → ℝ :=
      fun v => max ((NumberField.FinitePlace.mk v) x) 1
    have h_loc : ∀ v : IsDedekindDomain.HeightOneSpectrum R, f v ≤ g v := by
      intro v
      rcases hD_dich v with h1 | hmul
      · dsimp [f, g]
        rw [h1, map_one, Nat.cast_one]
        exact le_max_right _ _
      · dsimp [f, g]
        have h_norm_mul : (Ideal.absNorm (v.maxPowDividing D) : ℝ) *
            (Ideal.absNorm (v.maxPowDividing (Ideal.span {a})) : ℝ) =
            (Ideal.absNorm (v.maxPowDividing (Ideal.span {b})) : ℝ) := by
          exact_mod_cast congrArg Ideal.absNorm hmul ▸ map_mul Ideal.absNorm _ _ |>.symm
        have ha_emb : (NumberField.FinitePlace.mk v) (algebraMap R K a) *
            (Ideal.absNorm (v.maxPowDividing (Ideal.span {a})) : ℝ) = 1 := by
          rw [NumberField.FinitePlace.mk_apply]
          exact IsDedekindDomain.HeightOneSpectrum.embedding_mul_absNorm v (x := a) ha
        have hb_emb : (NumberField.FinitePlace.mk v) (algebraMap R K b) *
            (Ideal.absNorm (v.maxPowDividing (Ideal.span {b})) : ℝ) = 1 := by
          rw [NumberField.FinitePlace.mk_apply]
          exact IsDedekindDomain.HeightOneSpectrum.embedding_mul_absNorm v (x := b) hb
        have h_vx : (NumberField.FinitePlace.mk v) x =
            (NumberField.FinitePlace.mk v) (algebraMap R K a) /
            (NumberField.FinitePlace.mk v) (algebraMap R K b) := map_div₀ _ _ _
        have hvb_ne : (NumberField.FinitePlace.mk v) (algebraMap R K b) ≠ 0 :=
          left_ne_zero_of_mul_eq_one hb_emb
        have h_eq : (Ideal.absNorm (v.maxPowDividing D) : ℝ) = (NumberField.FinitePlace.mk v) x := by
          rw [h_vx, eq_div_iff hvb_ne]
          calc (Ideal.absNorm (v.maxPowDividing D) : ℝ) *
                (NumberField.FinitePlace.mk v) (algebraMap R K b)
            _ = (Ideal.absNorm (v.maxPowDividing D) : ℝ) *
                (NumberField.FinitePlace.mk v) (algebraMap R K b) *
                ((NumberField.FinitePlace.mk v) (algebraMap R K a) *
                  (Ideal.absNorm (v.maxPowDividing (Ideal.span {a})) : ℝ)) := by
                rw [ha_emb, mul_one]
            _ = ((Ideal.absNorm (v.maxPowDividing D) : ℝ) *
                  (Ideal.absNorm (v.maxPowDividing (Ideal.span {a})) : ℝ)) *
                (NumberField.FinitePlace.mk v) (algebraMap R K b) *
                (NumberField.FinitePlace.mk v) (algebraMap R K a) := by ring
            _ = (NumberField.FinitePlace.mk v) (algebraMap R K b) *
                (Ideal.absNorm (v.maxPowDividing (Ideal.span {b})) : ℝ) *
                (NumberField.FinitePlace.mk v) (algebraMap R K a) := by
                rw [h_norm_mul]; ring
            _ = (NumberField.FinitePlace.mk v) (algebraMap R K a) := by
                rw [hb_emb, one_mul]
        rw [h_eq]
        exact le_max_left _ _
    have hf_fin : (Function.mulSupport f).Finite := by
      refine (Ideal.finite_mulSupport hD).subset (fun v hv => ?_)
      intro h1
      apply hv
      dsimp at h1
      dsimp [f]
      rw [h1, map_one, Nat.cast_one]
    have hmk_inj : Function.Injective (NumberField.FinitePlace.mk :
        IsDedekindDomain.HeightOneSpectrum R → NumberField.FinitePlace K) :=
      Function.LeftInverse.injective NumberField.FinitePlace.maximalIdeal_mk
    have hg_fin : (Function.mulSupport g).Finite := by
      have h_w : (Function.mulSupport (fun w : NumberField.FinitePlace K => w x)).Finite :=
        NumberField.FinitePlace.mulSupport_finite hx
      refine (h_w.preimage hmk_inj.injOn).subset (fun v hv => ?_)
      intro h1
      apply hv
      change (NumberField.FinitePlace.mk v) x = 1 at h1
      dsimp [g]
      change max ((NumberField.FinitePlace.mk v) x) 1 = 1
      rw [h1, max_self]
    let φ : Ideal R →* ℝ := (Nat.castRingHom ℝ).toMonoidHom.comp Ideal.absNorm.toMonoidHom
    have hD_norm : (Ideal.absNorm D : ℝ) = ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum R, f v := by
      have h_fact := Ideal.finprod_heightOneSpectrum_factorization hD
      have h_map := map_finprod φ (Ideal.finite_mulSupport hD)
      simpa [φ, f, h_fact] using h_map
    let S := hf_fin.toFinset ∪ hg_fin.toFinset
    have hf_prod : ∏ᶠ v, f v = ∏ v ∈ S, f v :=
      finprod_eq_prod_of_mulSupport_subset f (by
        intro v hv
        exact Finset.mem_coe.mpr (Finset.mem_union_left _ (hf_fin.mem_toFinset.mpr hv)))
    have hg_prod : ∏ᶠ v, g v = ∏ v ∈ S, g v :=
      finprod_eq_prod_of_mulSupport_subset g (by
        intro v hv
        exact Finset.mem_coe.mpr (Finset.mem_union_right _ (hg_fin.mem_toFinset.mpr hv)))
    have hfg_le : ∏ᶠ v, f v ≤ ∏ᶠ v, g v := by
      rw [hf_prod, hg_prod]
      exact Finset.prod_le_prod (fun v _ => Nat.cast_nonneg _) (fun v _ => h_loc v)
    let e : IsDedekindDomain.HeightOneSpectrum R ≃ NumberField.FinitePlace K :=
      { toFun := NumberField.FinitePlace.mk
        invFun := NumberField.FinitePlace.maximalIdeal
        left_inv := NumberField.FinitePlace.maximalIdeal_mk
        right_inv := NumberField.FinitePlace.mk_maximalIdeal }
    have hg_reindex : ∏ᶠ v, g v = ∏ᶠ w : NumberField.FinitePlace K, max (w x) 1 :=
      finprod_comp_equiv e (f := fun w => max (w x) 1)
    have h_inf : 1 ≤ ∏ v : NumberField.InfinitePlace K, max (v x) 1 ^ v.mult :=
      Finset.one_le_prod Finset.univ (fun v => one_le_pow₀ (le_max_right _ _))
    have h_fin : 1 ≤ ∏ᶠ w : NumberField.FinitePlace K, max (w x) 1 :=
      one_le_finprod (fun w => le_max_right _ _)
    rw [NumberField.mulHeight₁_eq x]
    change (Ideal.absNorm D : ℝ) ≤
      (∏ v : NumberField.InfinitePlace K, max (v x) 1 ^ v.mult) *
      ∏ᶠ w : NumberField.FinitePlace K, max (w x) 1
    nlinarith [hD_norm, hfg_le, hg_reindex]
  have h_clear_den : ∀ {a b : R} (hb : b ≠ 0) {D : Ideal R} (hD : D ≠ ⊥),
      D * Ideal.span {a} ≤ Ideal.span {b} →
      1 ≤ Ideal.absNorm D ∧
      IsIntegral ℤ ((Ideal.absNorm D : K) * (algebraMap R K a / algebraMap R K b)) := by
    intro a b hb D hD hD_le
    let m := Ideal.absNorm D
    have hm_pos : 0 < m :=
      Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hD)
    refine ⟨Nat.succ_le_of_lt hm_pos, ?_⟩
    have hm_mem : (m : R) ∈ D := Ideal.absNorm_mem D
    have ha_mem : a ∈ Ideal.span ({a} : Set R) := Ideal.mem_span_singleton_self a
    have hma_mem : (m : R) * a ∈ Ideal.span ({b} : Set R) :=
      hD_le (Submodule.mul_mem_mul hm_mem ha_mem)
    rcases Ideal.mem_span_singleton.mp hma_mem with ⟨y, hy⟩
    have hb_K : algebraMap R K b ≠ 0 :=
      (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr hb
    have hy_K : (m : K) * algebraMap R K a = algebraMap R K b * algebraMap R K y := by
      have h := congrArg (algebraMap R K) hy
      simpa [map_mul, map_natCast] using h
    have h_eq : (m : K) * (algebraMap R K a / algebraMap R K b) = algebraMap R K y := by
      rw [← mul_div_assoc, hy_K, mul_div_cancel_left₀ _ hb_K]
    rw [h_eq]
    exact NumberField.RingOfIntegers.isIntegral_coe y
  let C : ℝ := Real.exp B
  let S : Set K := {y : K | IsIntegral ℤ y ∧ ∀ φ : K →+* ℂ, ‖φ y‖ ≤ C ^ 2}
  let M : Set ℕ := Set.Icc 1 (Nat.floor C)
  have hS_fin : S.Finite := NumberField.Embeddings.finite_of_norm_le K ℂ (C ^ 2)
  have hM_fin : M.Finite := Set.finite_Icc 1 (Nat.floor C)
  have hT_fin : ((fun p : K × ℕ => p.1 / (p.2 : K)) '' (S ×ˢ M)).Finite :=
    (hS_fin.prod hM_fin).image _
  refine hT_fin.subset (fun x hx => ?_)
  have hx_mul : Height.mulHeight₁ x ≤ C := by
    have h_log : Real.log (Height.mulHeight₁ x) ≤ B := by
      rwa [← Height.logHeight₁_eq_log_mulHeight₁]
    exact (Real.log_le_iff_le_exp (Height.mulHeight₁_pos x)).mp h_log
  have hC_one : 1 ≤ C := le_trans (Height.one_le_mulHeight₁ x) hx_mul
  have h_exists_m : ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C ∧ IsIntegral ℤ ((m : K) * x) := by
    by_cases hx0 : x = 0
    · refine ⟨1, le_rfl, by simpa using hC_one, ?_⟩
      rw [hx0, mul_zero]
      exact isIntegral_zero
    · obtain ⟨a, b, hb_mem, hab⟩ := IsFractionRing.div_surjective (A := R) x
      have hb : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb_mem
      have ha : a ≠ 0 := by
        intro ha0
        apply hx0
        rw [← hab, ha0, map_zero, zero_div]
      obtain ⟨D, hD_ne, hD_le, hD_dich⟩ := h_ideal_den ha hb
      have h_clear := h_clear_den hb hD_ne hD_le
      have h_norm := h_absNorm_le ha hb hD_ne hD_dich
      rw [hab] at h_clear h_norm
      exact ⟨Ideal.absNorm D, h_clear.1, le_trans h_norm hx_mul, h_clear.2⟩
  obtain ⟨m, hm_one, hm_le, hm_int⟩ := h_exists_m
  refine ⟨((m : K) * x, m), ⟨⟨hm_int, fun φ => ?_⟩, ⟨hm_one, Nat.le_floor hm_le⟩⟩, ?_⟩
  · rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
    have h_phi_x : ‖φ x‖ ≤ C := le_trans (h_arch x φ) hx_mul
    calc (m : ℝ) * ‖φ x‖ ≤ C * C :=
          mul_le_mul hm_le h_phi_x (norm_nonneg _) (le_trans (Nat.cast_nonneg _) hm_le)
      _ = C ^ 2 := (sq C).symm
  · dsimp
    have hm_ne : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm_one)
    exact mul_div_cancel_left₀ x hm_ne
