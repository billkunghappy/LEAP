import Mathlib
import Hilbert10Defs
import hilbert_reciprocity
set_option maxHeartbeats 4000000

/-! ### Statement (originally `theorem_4_5.lean`) -/

/--
**Theorem 4.5 ([26, Theorem 2.3.4]).** Let `𝓛 ⊆ 𝓕` be Selmer structures agreeing
outside the single prime `v₀`. Then the images of `Sel_𝓕` and `Sel_{𝓛^∨}` are
orthogonal complements under the local Tate pairing at `v₀`. Concretely: a local class
`(d₁, d₂)` at `v₀` pairs trivially (via Hilbert symbols) with every element of the
relaxed Selmer group iff it is the restriction of some element of that group.
-/

theorem hilbFin_eq_one_of_evenVal_outside_T {K : Type u} [Field K] [NumberField K]
    (a₁ a₂ a₃ : K) (h₁₂ : a₁ ≠ a₂) (h₁₃ : a₁ ≠ a₃) (h₂₃ : a₂ ≠ a₃)
    (hint₁ : IsIntegral ℤ a₁) (hint₂ : IsIntegral ℤ a₂) (hint₃ : IsIntegral ℤ a₃)
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hT : IsGoodT a₁ a₂ a₃ T)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hvT : v ∉ T) (x y : Kˣ) (hx : EvenVal v x) (hy : EvenVal v y) :
    hilbFin v (x : K) (y : K) = 1 :=
by
  classical
  have exists_ringOfIntegers_approx_of_valuation_le_one :
      ∀ (a : K), IsDedekindDomain.HeightOneSpectrum.valuation K v a ≤ 1 →
      ∃ r : NumberField.RingOfIntegers K,
        IsDedekindDomain.HeightOneSpectrum.valuation K v
          (a - algebraMap (NumberField.RingOfIntegers K) K r) < 1 := by
    intro a ha
    obtain ⟨xa, ya, hya, hxya⟩ :=
      IsFractionRing.div_surjective (A := NumberField.RingOfIntegers K) (K := K) a
    have hy0 : ya ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hya
    have hiy : algebraMap (NumberField.RingOfIntegers K) K ya ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hya
    have hstar : a * algebraMap (NumberField.RingOfIntegers K) K ya
        = algebraMap (NumberField.RingOfIntegers K) K xa := by
      rw [← hxya]
      exact div_mul_cancel₀ _ hiy
    obtain ⟨m, hym, hym1⟩ : ∃ m : ℕ, ya ∈ v.asIdeal ^ m ∧ ya ∉ v.asIdeal ^ (m + 1) := by
      have ht0 : v.intValuation ya ≠ 0 :=
        IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero v ya hy0
      have ht1 : v.intValuation ya ≤ 1 :=
        IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v ya
      obtain ⟨k, hk⟩ : ∃ k : ℤ, WithZero.exp k = v.intValuation ya := ⟨_, WithZero.exp_log ht0⟩
      have hkle : k ≤ 0 := by
        have hstep : WithZero.exp k ≤ WithZero.exp (0 : ℤ) := by
          rw [hk, WithZero.exp_zero]; exact ht1
        exact WithZero.exp_le_exp.mp hstep
      have hcast : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      have hexpm : WithZero.exp (-(((-k).toNat : ℕ) : ℤ)) = v.intValuation ya := by
        rw [hcast, neg_neg, hk]
      refine ⟨(-k).toNat, ?_, ?_⟩
      · exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya _).mp
          (le_of_eq hexpm.symm)
      · intro hcon
        have hle :=
          (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya
            ((-k).toNat + 1)).mpr hcon
        have he : (-(((-k).toNat + 1 : ℕ) : ℤ)) = k - 1 := by
          rw [Nat.cast_add, Nat.cast_one, hcast]; ring
        rw [he, ← hk] at hle
        have := WithZero.exp_le_exp.mp hle
        omega
    have hivy : v.intValuation ya ≤ WithZero.exp (-(m : ℤ)) :=
      (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya m).mpr hym
    have hxm : xa ∈ v.asIdeal ^ m := by
      refine (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v xa m).mp ?_
      have e1 : v.intValuation xa
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K xa) :=
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v xa).symm
      have e2 : v.intValuation ya
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K ya) :=
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v ya).symm
      calc v.intValuation xa
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (a * algebraMap (NumberField.RingOfIntegers K) K ya) := by
            rw [hstar]; exact e1
        _ = IsDedekindDomain.HeightOneSpectrum.valuation K v a *
              IsDedekindDomain.HeightOneSpectrum.valuation K v
                (algebraMap (NumberField.RingOfIntegers K) K ya) := Valuation.map_mul _ _ _
        _ ≤ 1 * IsDedekindDomain.HeightOneSpectrum.valuation K v
                (algebraMap (NumberField.RingOfIntegers K) K ya) := mul_le_mul_left ha _
        _ = v.intValuation ya := by rw [one_mul, ← e2]
        _ ≤ WithZero.exp (-(m : ℤ)) := hivy
    have hPprime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
    have hJdvd : (Ideal.span {ya} ⊔ v.asIdeal ^ (m + 1)) ∣ v.asIdeal ^ (m + 1) :=
      Ideal.dvd_iff_le.mpr le_sup_right
    obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow hPprime (m + 1)).mp hJdvd
    have hJ : Ideal.span {ya} ⊔ v.asIdeal ^ (m + 1) = v.asIdeal ^ i := associated_iff_eq.mp hassoc
    have hyJ : ya ∈ v.asIdeal ^ i := by
      rw [← hJ]
      exact Ideal.dvd_span_singleton.mp (Ideal.dvd_iff_le.mpr le_sup_left)
    have him : i ≤ m := by
      by_contra hcon
      have hii : i = m + 1 := by omega
      rw [hii] at hyJ
      exact hym1 hyJ
    have hxJ : xa ∈ Ideal.span {ya} ⊔ v.asIdeal ^ (m + 1) := by
      rw [hJ]
      exact Ideal.pow_le_pow_right him hxm
    obtain ⟨p, hp, w, hw, hpw⟩ := Submodule.mem_sup.mp hxJ
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hp
    refine ⟨r, ?_⟩
    have hxrw : xa = r * ya + w := by rw [← hpw, hr]
    have key : (a - algebraMap (NumberField.RingOfIntegers K) K r)
        * algebraMap (NumberField.RingOfIntegers K) K ya
        = algebraMap (NumberField.RingOfIntegers K) K w := by
      have h1 : algebraMap (NumberField.RingOfIntegers K) K xa
          = algebraMap (NumberField.RingOfIntegers K) K r
              * algebraMap (NumberField.RingOfIntegers K) K ya
            + algebraMap (NumberField.RingOfIntegers K) K w := by
        rw [hxrw, map_add, map_mul]
      rw [sub_mul, hstar, h1]; ring
    have hV : IsDedekindDomain.HeightOneSpectrum.valuation K v
          (a - algebraMap (NumberField.RingOfIntegers K) K r) * v.intValuation ya
        = v.intValuation w := by
      rw [← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v ya,
        ← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v w,
        ← Valuation.map_mul, key]
    have hwb : v.intValuation w ≤ WithZero.exp (-((m + 1 : ℕ) : ℤ)) :=
      (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v w (m + 1)).mpr hw
    have hyb : WithZero.exp (-((m + 1 : ℕ) : ℤ)) < v.intValuation ya := by
      by_contra hcon
      push_neg at hcon
      exact hym1
        ((IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya (m + 1)).mp hcon)
    by_contra hcon
    push_neg at hcon
    have hchain : v.intValuation ya ≤ v.intValuation w := by
      calc v.intValuation ya = 1 * v.intValuation ya := (one_mul _).symm
        _ ≤ IsDedekindDomain.HeightOneSpectrum.valuation K v
              (a - algebraMap (NumberField.RingOfIntegers K) K r) * v.intValuation ya :=
            mul_le_mul_left hcon _
        _ = v.intValuation w := hV
    exact absurd (lt_of_le_of_lt (le_trans hchain hwb) hyb) (lt_irrefl _)
  have exists_sol_quadratic_mod_heightOneSpectrum :
      (2 : NumberField.RingOfIntegers K) ∉ v.asIdeal →
      ∀ (r s : NumberField.RingOfIntegers K), r ∉ v.asIdeal → s ∉ v.asIdeal →
      ∃ x₀ y₀ : NumberField.RingOfIntegers K, r * x₀ ^ 2 + s * y₀ ^ 2 - 1 ∈ v.asIdeal := by
    intro h2 r s hr hs
    letI : Field (NumberField.RingOfIntegers K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
    letI : Fintype (NumberField.RingOfIntegers K ⧸ v.asIdeal) := Fintype.ofFinite _
    have hr' : Ideal.Quotient.mk v.asIdeal r ≠ 0 := fun h =>
      hr (Ideal.Quotient.eq_zero_iff_mem.mp h)
    have hs' : Ideal.Quotient.mk v.asIdeal s ≠ 0 := fun h =>
      hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
    have h2' : (2 : NumberField.RingOfIntegers K ⧸ v.asIdeal) ≠ 0 := by
      intro h
      refine h2 (Ideal.Quotient.eq_zero_iff_mem.mp ?_)
      rw [map_ofNat]
      exact h
    have hchar : ringChar (NumberField.RingOfIntegers K ⧸ v.asIdeal) ≠ 2 := by
      intro h
      refine h2' ?_
      have h4 : ((2 : ℕ) : NumberField.RingOfIntegers K ⧸ v.asIdeal) = 0 :=
        (ringChar.spec _ 2).mpr (by rw [h])
      simpa using h4
    have hcard : Fintype.card (NumberField.RingOfIntegers K ⧸ v.asIdeal) % 2 = 1 :=
      FiniteField.odd_card_of_char_ne_two hchar
    obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
      (f := Polynomial.C (Ideal.Quotient.mk v.asIdeal r) * Polynomial.X ^ 2
        + Polynomial.C 0 * Polynomial.X + Polynomial.C 0)
      (g := Polynomial.C (Ideal.Quotient.mk v.asIdeal s) * Polynomial.X ^ 2
        + Polynomial.C 0 * Polynomial.X + Polynomial.C (-1))
      (Polynomial.degree_quadratic hr') (Polynomial.degree_quadratic hs') hcard
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, zero_mul, add_zero] at hab
    obtain ⟨x₀, hx₀⟩ := Ideal.Quotient.mk_surjective (I := v.asIdeal) a
    obtain ⟨y₀, hy₀⟩ := Ideal.Quotient.mk_surjective (I := v.asIdeal) b
    refine ⟨x₀, y₀, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
    simp only [map_sub, map_add, map_mul, map_pow, map_one]
    rw [hx₀, hy₀]
    linear_combination hab
  have exists_sq_of_valued_sub_sq_lt_one :
      Valued.v (2 : v.adicCompletion K) = (1 : WithZero (Multiplicative ℤ)) →
      ∀ (c x₀ : v.adicCompletion K),
      Valued.v x₀ = (1 : WithZero (Multiplicative ℤ)) →
      Valued.v (c - x₀ ^ 2) < (1 : WithZero (Multiplicative ℤ)) →
      ∃ z : v.adicCompletion K, z ^ 2 = c := by
    intro h2 c x₀ hx₀ hc
    have hstep : ∀ y : v.adicCompletion K,
        Valued.v y = (1 : WithZero (Multiplicative ℤ)) →
        Valued.v (y ^ 2 - c) < (1 : WithZero (Multiplicative ℤ)) →
        Valued.v (y - (y ^ 2 - c) / (2 * y)) = (1 : WithZero (Multiplicative ℤ)) ∧
        Valued.v ((y - (y ^ 2 - c) / (2 * y)) ^ 2 - c) = Valued.v (y ^ 2 - c) ^ 2 ∧
        Valued.v (y - (y ^ 2 - c) / (2 * y) - y) = Valued.v (y ^ 2 - c) := by
      intro y hy hd
      have h2ne : (2 : v.adicCompletion K) ≠ 0 := by
        intro hcon
        rw [hcon, map_zero] at h2
        exact zero_ne_one h2
      have hyne : y ≠ 0 := by
        intro hcon
        rw [hcon, map_zero] at hy
        exact zero_ne_one hy
      have ht : Valued.v ((y ^ 2 - c) / (2 * y)) = Valued.v (y ^ 2 - c) := by
        rw [map_div₀, map_mul, h2, hy, one_mul, div_one]
      have hlt' : Valued.v ((y ^ 2 - c) / (2 * y)) < Valued.v y := by
        rw [ht, hy]; exact hd
      refine ⟨?_, ?_, ?_⟩
      · rw [Valuation.map_sub_eq_of_lt_left _ hlt', hy]
      · have key : (y - (y ^ 2 - c) / (2 * y)) ^ 2 - c = ((y ^ 2 - c) / (2 * y)) ^ 2 := by
          field_simp
          ring
        rw [key, Valuation.map_pow, ht]
      · have key : y - (y ^ 2 - c) / (2 * y) - y = -((y ^ 2 - c) / (2 * y)) := by ring
        rw [key, Valuation.map_neg, ht]
    have hdecay : ∀ δ γ : WithZero (Multiplicative ℤ), δ < 1 → γ ≠ 0 →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → δ ^ (2 ^ n) < γ := by
      intro δ γ hδ hγ
      rcases eq_or_ne δ 0 with h0 | h0
      · refine ⟨0, fun n _ => ?_⟩
        rw [h0, zero_pow (Nat.two_pow_pos n).ne']
        exact zero_lt_iff.mpr hγ
      · obtain ⟨a, rfl⟩ : ∃ a : ℤ, δ = ((Multiplicative.ofAdd a : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
          obtain ⟨g, hg⟩ := WithZero.ne_zero_iff_exists.mp h0
          exact ⟨Multiplicative.toAdd g, hg.symm⟩
        obtain ⟨b, rfl⟩ : ∃ b : ℤ, γ = ((Multiplicative.ofAdd b : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
          obtain ⟨g, hg⟩ := WithZero.ne_zero_iff_exists.mp hγ
          exact ⟨Multiplicative.toAdd g, hg.symm⟩
        have ha : a < 0 := by
          have h1 : (Multiplicative.ofAdd a : Multiplicative ℤ) < 1 := WithZero.coe_lt_one.mp hδ
          exact h1
        have hpow : ∀ k : ℕ,
            ((Multiplicative.ofAdd a : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ k
              = ((Multiplicative.ofAdd ((k : ℤ) * a) : Multiplicative ℤ) :
                  WithZero (Multiplicative ℤ)) := by
          intro k
          rw [← WithZero.coe_pow]
          congr 1
        refine ⟨(-b).toNat + 1, fun n hn => ?_⟩
        rw [hpow, WithZero.coe_lt_coe]
        have hbk : -b < ((2 ^ n : ℕ) : ℤ) := by
          have hx : (-b).toNat < n := by omega
          have h1 : (-b).toNat < 2 ^ n := lt_trans hx Nat.lt_two_pow_self
          have h2' : ((-b).toNat : ℤ) < ((2 ^ n : ℕ) : ℤ) := by exact_mod_cast h1
          exact lt_of_le_of_lt (Int.self_le_toNat _) h2'
        have hkpos : (0 : ℤ) ≤ ((2 ^ n : ℕ) : ℤ) := Int.natCast_nonneg _
        have ha1 : a ≤ -1 := by omega
        have hle : ((2 ^ n : ℕ) : ℤ) * a ≤ ((2 ^ n : ℕ) : ℤ) * (-1) :=
          mul_le_mul_of_nonneg_left ha1 hkpos
        have hgoal : ((2 ^ n : ℕ) : ℤ) * a < b := by linarith
        exact hgoal
    obtain ⟨ε, hεdef⟩ : ∃ ε : WithZero (Multiplicative ℤ), ε = Valued.v (x₀ ^ 2 - c) := ⟨_, rfl⟩
    have hε : ε < (1 : WithZero (Multiplicative ℤ)) := by
      rw [hεdef, Valuation.map_sub_swap]
      exact hc
    obtain ⟨f, hf0, hfs⟩ : ∃ f : ℕ → v.adicCompletion K, f 0 = x₀ ∧
        ∀ n : ℕ, f (n + 1) = f n - (f n ^ 2 - c) / (2 * f n) :=
      ⟨fun n => Nat.rec (motive := fun _ => v.adicCompletion K) x₀
        (fun _ y => y - (y ^ 2 - c) / (2 * y)) n, rfl, fun _ => rfl⟩
    have hinv : ∀ n : ℕ, Valued.v (f n) = (1 : WithZero (Multiplicative ℤ)) ∧
        Valued.v (f n ^ 2 - c) = ε ^ (2 ^ n) := by
      intro n
      induction n with
      | zero =>
        refine ⟨by rw [hf0]; exact hx₀, ?_⟩
        rw [hf0, pow_zero, pow_one, hεdef]
      | succ n ih =>
        have hlt : Valued.v (f n ^ 2 - c) < (1 : WithZero (Multiplicative ℤ)) := by
          rw [ih.2]
          exact pow_lt_one₀ zero_le' hε (Nat.two_pow_pos n).ne'
        obtain ⟨s1, s2, -⟩ := hstep (f n) ih.1 hlt
        refine ⟨by rw [hfs n]; exact s1, ?_⟩
        rw [hfs n, s2, ih.2, ← pow_mul]
        congr 1
    have hdiff : ∀ n : ℕ, Valued.v (f (n + 1) - f n) = ε ^ (2 ^ n) := by
      intro n
      have hlt : Valued.v (f n ^ 2 - c) < (1 : WithZero (Multiplicative ℤ)) := by
        rw [(hinv n).2]
        exact pow_lt_one₀ zero_le' hε (Nat.two_pow_pos n).ne'
      obtain ⟨-, -, s3⟩ := hstep (f n) (hinv n).1 hlt
      rw [hfs n, s3, (hinv n).2]
    have hCauchy : Cauchy (Filter.map f Filter.atTop) := by
      refine Valued.cauchy_iff.mpr ⟨inferInstance, ?_⟩
      intro γ
      obtain ⟨N, hN⟩ := hdecay ε (γ : WithZero (Multiplicative ℤ)) hε (Units.ne_zero γ)
      have htel : ∀ m : ℕ, N ≤ m → Valued.v (f m - f N) < (γ : WithZero (Multiplicative ℤ)) := by
        intro m hm
        induction m, hm using Nat.le_induction with
        | base =>
          rw [sub_self, map_zero]
          exact zero_lt_iff.mpr (Units.ne_zero γ)
        | succ m hm ih =>
          have e : f (m + 1) - f N = (f (m + 1) - f m) + (f m - f N) := by ring
          rw [e]
          refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ih)
          rw [hdiff m]
          exact hN m hm
      refine ⟨f '' (Set.Ici N), Filter.image_mem_map (Filter.Ici_mem_atTop N), ?_⟩
      rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
      have e : f j - f i = (f j - f N) - (f i - f N) := by ring
      rw [e]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt (htel j hj) (htel i hi))
    obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hCauchy
    have hsq : Filter.Tendsto (fun n : ℕ => f n ^ 2 - c) Filter.atTop (nhds (z ^ 2 - c)) :=
      (hz.pow 2).sub tendsto_const_nhds
    have hzero : Filter.Tendsto (fun n : ℕ => f n ^ 2 - c) Filter.atTop
        (nhds (0 : v.adicCompletion K)) := by
      rw [Filter.tendsto_def]
      intro s hs
      obtain ⟨γ, hγs⟩ := Valued.mem_nhds_zero.mp hs
      obtain ⟨N, hN⟩ := hdecay ε (γ : WithZero (Multiplicative ℤ)) hε (Units.ne_zero γ)
      refine Filter.mem_of_superset (Filter.Ici_mem_atTop N) ?_
      intro n hn
      apply hγs
      show Valued.v (f n ^ 2 - c) < (γ : WithZero (Multiplicative ℤ))
      rw [(hinv n).2]
      exact hN n hn
    exact ⟨z, eq_of_sub_eq_zero (tendsto_nhds_unique hsq hzero)⟩
  have hilbFin_eq_one_of_units :
      ∀ (a b : K),
      IsDedekindDomain.HeightOneSpectrum.valuation K v a = 1 →
      IsDedekindDomain.HeightOneSpectrum.valuation K v b = 1 →
      IsDedekindDomain.HeightOneSpectrum.valuation K v (2 : K) = 1 →
      hilbFin v a b = 1 := by
    intro a b ha hb h2
    have hval : ∀ k : K, Valued.v (algebraMap K (v.adicCompletion K) k)
        = IsDedekindDomain.HeightOneSpectrum.valuation K v k := fun k =>
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
    have h2v : Valued.v (2 : v.adicCompletion K) = (1 : WithZero (Multiplicative ℤ)) := by
      rw [(map_ofNat (algebraMap K (v.adicCompletion K)) 2).symm, hval, h2]
    have key : ∀ a' b' X Y : K,
        IsDedekindDomain.HeightOneSpectrum.valuation K v a' = 1 →
        IsDedekindDomain.HeightOneSpectrum.valuation K v X = 1 →
        IsDedekindDomain.HeightOneSpectrum.valuation K v (a' * X ^ 2 + b' * Y ^ 2 - 1) < 1 →
        ∃ Z W : v.adicCompletion K,
          algebraMap K (v.adicCompletion K) a' * Z ^ 2
            + algebraMap K (v.adicCompletion K) b' * W ^ 2 = 1 := by
      intro a' b' X Y ha' hX hlt
      have ha'0 : a' ≠ 0 := by
        intro h; rw [h] at ha'; simp at ha'
      obtain ⟨c, hac⟩ : ∃ c : K, a' * c = 1 - b' * Y ^ 2 :=
        ⟨(1 - b' * Y ^ 2) / a', by field_simp⟩
      have hid : a' * (c - X ^ 2) = -(a' * X ^ 2 + b' * Y ^ 2 - 1) := by
        rw [mul_sub, hac]; ring
      have hlt2 : IsDedekindDomain.HeightOneSpectrum.valuation K v (c - X ^ 2) < 1 := by
        have h := congrArg (IsDedekindDomain.HeightOneSpectrum.valuation K v) hid
        rw [Valuation.map_mul, ha', one_mul, Valuation.map_neg] at h
        rw [h]; exact hlt
      have hx0v : Valued.v (algebraMap K (v.adicCompletion K) X)
          = (1 : WithZero (Multiplicative ℤ)) := by rw [hval, hX]
      have hcv : Valued.v (algebraMap K (v.adicCompletion K) c
          - (algebraMap K (v.adicCompletion K) X) ^ 2) < (1 : WithZero (Multiplicative ℤ)) := by
        have e : algebraMap K (v.adicCompletion K) c
            - (algebraMap K (v.adicCompletion K) X) ^ 2
            = algebraMap K (v.adicCompletion K) (c - X ^ 2) := by
          simp only [map_sub, map_pow]
        rw [e, hval]; exact hlt2
      obtain ⟨Z, hZ⟩ := exists_sq_of_valued_sub_sq_lt_one h2v
        (algebraMap K (v.adicCompletion K) c) (algebraMap K (v.adicCompletion K) X) hx0v hcv
      refine ⟨Z, algebraMap K (v.adicCompletion K) Y, ?_⟩
      have hsum : a' * c + b' * Y ^ 2 = 1 := by rw [hac]; ring
      have hmap : algebraMap K (v.adicCompletion K) a' * algebraMap K (v.adicCompletion K) c
          + algebraMap K (v.adicCompletion K) b' * (algebraMap K (v.adicCompletion K) Y) ^ 2
          = algebraMap K (v.adicCompletion K) (a' * c + b' * Y ^ 2) := by
        simp only [map_add, map_mul, map_pow]
      rw [hZ, hmap, hsum, map_one]
    obtain ⟨r, hr⟩ := exists_ringOfIntegers_approx_of_valuation_le_one a (le_of_eq ha)
    obtain ⟨s, hs⟩ := exists_ringOfIntegers_approx_of_valuation_le_one b (le_of_eq hb)
    have hrv : IsDedekindDomain.HeightOneSpectrum.valuation K v
        (algebraMap (NumberField.RingOfIntegers K) K r) = 1 := by
      have e : algebraMap (NumberField.RingOfIntegers K) K r
          = a - (a - algebraMap (NumberField.RingOfIntegers K) K r) := by ring
      rw [e, Valuation.map_sub_eq_of_lt_left _ (by rw [ha]; exact hr), ha]
    have hsv : IsDedekindDomain.HeightOneSpectrum.valuation K v
        (algebraMap (NumberField.RingOfIntegers K) K s) = 1 := by
      have e : algebraMap (NumberField.RingOfIntegers K) K s
          = b - (b - algebraMap (NumberField.RingOfIntegers K) K s) := by ring
      rw [e, Valuation.map_sub_eq_of_lt_left _ (by rw [hb]; exact hs), hb]
    have hrnot : r ∉ v.asIdeal := by
      refine IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mp ?_
      rw [← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v r]
      exact hrv
    have hsnot : s ∉ v.asIdeal := by
      refine IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mp ?_
      rw [← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v s]
      exact hsv
    have h2not : (2 : NumberField.RingOfIntegers K) ∉ v.asIdeal := by
      refine IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mp ?_
      have e : IsDedekindDomain.HeightOneSpectrum.valuation K v
          (algebraMap (NumberField.RingOfIntegers K) K (2 : NumberField.RingOfIntegers K))
          = IsDedekindDomain.HeightOneSpectrum.intValuation v
            (2 : NumberField.RingOfIntegers K) :=
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v 2
      rw [← e, map_ofNat (algebraMap (NumberField.RingOfIntegers K) K) 2]
      exact h2
    obtain ⟨x₀, y₀, hxy⟩ := exists_sol_quadratic_mod_heightOneSpectrum h2not r s hrnot hsnot
    have halpha : IsDedekindDomain.HeightOneSpectrum.valuation K v
        ((algebraMap (NumberField.RingOfIntegers K) K) r
            * ((algebraMap (NumberField.RingOfIntegers K) K) x₀) ^ 2
          + (algebraMap (NumberField.RingOfIntegers K) K) s
            * ((algebraMap (NumberField.RingOfIntegers K) K) y₀) ^ 2 - 1) < 1 := by
      have e : (algebraMap (NumberField.RingOfIntegers K) K) r
            * ((algebraMap (NumberField.RingOfIntegers K) K) x₀) ^ 2
          + (algebraMap (NumberField.RingOfIntegers K) K) s
            * ((algebraMap (NumberField.RingOfIntegers K) K) y₀) ^ 2 - 1
          = (algebraMap (NumberField.RingOfIntegers K) K) (r * x₀ ^ 2 + s * y₀ ^ 2 - 1) := by
        simp only [map_add, map_mul, map_pow, map_sub, map_one]
      rw [e, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v,
        IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem]
      exact hxy
    have hXle : IsDedekindDomain.HeightOneSpectrum.valuation K v
        ((algebraMap (NumberField.RingOfIntegers K) K) x₀) ≤ 1 :=
      IsDedekindDomain.HeightOneSpectrum.valuation_le_one v x₀
    have hYle : IsDedekindDomain.HeightOneSpectrum.valuation K v
        ((algebraMap (NumberField.RingOfIntegers K) K) y₀) ≤ 1 :=
      IsDedekindDomain.HeightOneSpectrum.valuation_le_one v y₀
    have hbeta : IsDedekindDomain.HeightOneSpectrum.valuation K v
        (a * ((algebraMap (NumberField.RingOfIntegers K) K) x₀) ^ 2
          + b * ((algebraMap (NumberField.RingOfIntegers K) K) y₀) ^ 2 - 1) < 1 := by
      have t1 : IsDedekindDomain.HeightOneSpectrum.valuation K v
          ((a - (algebraMap (NumberField.RingOfIntegers K) K) r)
            * ((algebraMap (NumberField.RingOfIntegers K) K) x₀) ^ 2) < 1 := by
        rw [Valuation.map_mul, Valuation.map_pow]
        calc IsDedekindDomain.HeightOneSpectrum.valuation K v
                (a - (algebraMap (NumberField.RingOfIntegers K) K) r)
              * IsDedekindDomain.HeightOneSpectrum.valuation K v
                ((algebraMap (NumberField.RingOfIntegers K) K) x₀) ^ 2
            ≤ IsDedekindDomain.HeightOneSpectrum.valuation K v
                (a - (algebraMap (NumberField.RingOfIntegers K) K) r) * 1 :=
              mul_le_mul_right (pow_le_one' hXle 2) _
          _ = IsDedekindDomain.HeightOneSpectrum.valuation K v
                (a - (algebraMap (NumberField.RingOfIntegers K) K) r) := mul_one _
          _ < 1 := hr
      have t2 : IsDedekindDomain.HeightOneSpectrum.valuation K v
          ((b - (algebraMap (NumberField.RingOfIntegers K) K) s)
            * ((algebraMap (NumberField.RingOfIntegers K) K) y₀) ^ 2) < 1 := by
        rw [Valuation.map_mul, Valuation.map_pow]
        calc IsDedekindDomain.HeightOneSpectrum.valuation K v
                (b - (algebraMap (NumberField.RingOfIntegers K) K) s)
              * IsDedekindDomain.HeightOneSpectrum.valuation K v
                ((algebraMap (NumberField.RingOfIntegers K) K) y₀) ^ 2
            ≤ IsDedekindDomain.HeightOneSpectrum.valuation K v
                (b - (algebraMap (NumberField.RingOfIntegers K) K) s) * 1 :=
              mul_le_mul_right (pow_le_one' hYle 2) _
          _ = IsDedekindDomain.HeightOneSpectrum.valuation K v
                (b - (algebraMap (NumberField.RingOfIntegers K) K) s) := mul_one _
          _ < 1 := hs
      have t3 : IsDedekindDomain.HeightOneSpectrum.valuation K v
          ((a - (algebraMap (NumberField.RingOfIntegers K) K) r)
              * ((algebraMap (NumberField.RingOfIntegers K) K) x₀) ^ 2
            + (b - (algebraMap (NumberField.RingOfIntegers K) K) s)
              * ((algebraMap (NumberField.RingOfIntegers K) K) y₀) ^ 2) < 1 :=
        lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt t1 t2)
      have e : a * ((algebraMap (NumberField.RingOfIntegers K) K) x₀) ^ 2
          + b * ((algebraMap (NumberField.RingOfIntegers K) K) y₀) ^ 2 - 1
          = ((algebraMap (NumberField.RingOfIntegers K) K) r
              * ((algebraMap (NumberField.RingOfIntegers K) K) x₀) ^ 2
            + (algebraMap (NumberField.RingOfIntegers K) K) s
              * ((algebraMap (NumberField.RingOfIntegers K) K) y₀) ^ 2 - 1)
            + ((a - (algebraMap (NumberField.RingOfIntegers K) K) r)
                * ((algebraMap (NumberField.RingOfIntegers K) K) x₀) ^ 2
              + (b - (algebraMap (NumberField.RingOfIntegers K) K) s)
                * ((algebraMap (NumberField.RingOfIntegers K) K) y₀) ^ 2) := by ring
      rw [e]
      exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt halpha t3)
    have hcase : x₀ ∉ v.asIdeal ∨ y₀ ∉ v.asIdeal := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨hx₀, hy₀⟩ := hcon
      have h1 : r * x₀ ^ 2 + s * y₀ ^ 2 ∈ v.asIdeal :=
        Ideal.add_mem _
          (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hx₀ 2 (by norm_num)))
          (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hy₀ 2 (by norm_num)))
      have hone : (1 : NumberField.RingOfIntegers K) ∈ v.asIdeal := by
        have h3 := Ideal.sub_mem _ h1 hxy
        simpa using h3
      exact v.isPrime.ne_top (Ideal.eq_top_iff_one _ |>.mpr hone)
    have hex : ∃ Z W : v.adicCompletion K,
        algebraMap K (v.adicCompletion K) a * Z ^ 2
          + algebraMap K (v.adicCompletion K) b * W ^ 2 = 1 := by
      rcases hcase with hx₀ | hy₀
      · have hXv : IsDedekindDomain.HeightOneSpectrum.valuation K v
            ((algebraMap (NumberField.RingOfIntegers K) K) x₀) = 1 := by
          rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v x₀]
          exact IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr hx₀
        exact key a b ((algebraMap (NumberField.RingOfIntegers K) K) x₀)
          ((algebraMap (NumberField.RingOfIntegers K) K) y₀) ha hXv hbeta
      · have hYv : IsDedekindDomain.HeightOneSpectrum.valuation K v
            ((algebraMap (NumberField.RingOfIntegers K) K) y₀) = 1 := by
          rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v y₀]
          exact IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr hy₀
        have hbeta' : IsDedekindDomain.HeightOneSpectrum.valuation K v
            (b * ((algebraMap (NumberField.RingOfIntegers K) K) y₀) ^ 2
              + a * ((algebraMap (NumberField.RingOfIntegers K) K) x₀) ^ 2 - 1) < 1 := by
          rw [show b * ((algebraMap (NumberField.RingOfIntegers K) K) y₀) ^ 2
                + a * ((algebraMap (NumberField.RingOfIntegers K) K) x₀) ^ 2 - 1
              = a * ((algebraMap (NumberField.RingOfIntegers K) K) x₀) ^ 2
                + b * ((algebraMap (NumberField.RingOfIntegers K) K) y₀) ^ 2 - 1 from by ring]
          exact hbeta
        obtain ⟨Z, W, hZW⟩ := key b a ((algebraMap (NumberField.RingOfIntegers K) K) y₀)
          ((algebraMap (NumberField.RingOfIntegers K) K) x₀) hb hYv hbeta'
        exact ⟨W, Z, by rw [← hZW]; ring⟩
    simp only [hilbFin, hilbLoc]
    rw [if_pos hex]
  have h2_val : IsDedekindDomain.HeightOneSpectrum.valuation K v (2 : K) = 1 := by
    let A₁ : NumberField.RingOfIntegers K := ⟨a₁, hint₁⟩
    let A₂ : NumberField.RingOfIntegers K := ⟨a₂, hint₂⟩
    let A₃ : NumberField.RingOfIntegers K := ⟨a₃, hint₃⟩
    let W : NumberField.RingOfIntegers K := 3 * (A₁ - A₂) * (A₁ - A₃) * (A₂ - A₃)
    have h2_le : IsDedekindDomain.HeightOneSpectrum.valuation K v (2 : K) ≤ 1 := by
      rw [← map_ofNat (algebraMap (NumberField.RingOfIntegers K) K) 2]
      exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one v 2
    have hW_le : IsDedekindDomain.HeightOneSpectrum.valuation K v
        (algebraMap (NumberField.RingOfIntegers K) K W) ≤ 1 :=
      IsDedekindDomain.HeightOneSpectrum.valuation_le_one v W
    have hprod_eq : 6 * (a₁ - a₂) * (a₁ - a₃) * (a₂ - a₃) =
        (2 : K) * algebraMap (NumberField.RingOfIntegers K) K W := by
      change 6 * (a₁ - a₂) * (a₁ - a₃) * (a₂ - a₃) =
        (2 : K) * algebraMap (NumberField.RingOfIntegers K) K (3 * (A₁ - A₂) * (A₁ - A₃) * (A₂ - A₃))
      simp only [map_mul, map_sub, map_ofNat]
      change 6 * (a₁ - a₂) * (a₁ - a₃) * (a₂ - a₃) = 2 * (3 * (a₁ - a₂) * (a₁ - a₃) * (a₂ - a₃))
      ring
    have hv_prod : IsDedekindDomain.HeightOneSpectrum.valuation K v
        (6 * (a₁ - a₂) * (a₁ - a₃) * (a₂ - a₃)) = 1 := by
      have h := (hT v).not.mp hvT
      push_neg at h
      exact h
    rw [hprod_eq, Valuation.map_mul] at hv_prod
    refine le_antisymm h2_le ?_
    calc (1 : WithZero (Multiplicative ℤ))
        = IsDedekindDomain.HeightOneSpectrum.valuation K v (2 : K) *
            IsDedekindDomain.HeightOneSpectrum.valuation K v (algebraMap (NumberField.RingOfIntegers K) K W) := hv_prod.symm
      _ ≤ IsDedekindDomain.HeightOneSpectrum.valuation K v (2 : K) * 1 :=
          mul_le_mul_right hW_le _
      _ = IsDedekindDomain.HeightOneSpectrum.valuation K v (2 : K) := mul_one _
  have h_even_factor : ∀ (w : Kˣ), EvenVal v w →
      ∃ u z : K, IsDedekindDomain.HeightOneSpectrum.valuation K v u = 1 ∧ z ≠ 0 ∧ (w : K) = u * z ^ 2 := by
    intro w hw
    obtain ⟨π₀, hπ₀⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer K v
    have hπ₀_ne : π₀ ≠ 0 := by
      intro h0
      rw [h0, Valuation.map_zero] at hπ₀
      exact WithZero.coe_ne_zero hπ₀.symm
    rcases hw with ⟨k, hk⟩
    have hval_w : IsDedekindDomain.HeightOneSpectrum.valuation K v (w : K) = WithZero.exp (k + k) := by
      rw [← IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq v w]
      have hk' : v.valuationOfNeZero w = Multiplicative.ofAdd (k + k) := by
        rw [← hk, ofAdd_toAdd]
      rw [hk']
      rfl
    refine ⟨(w : K) * π₀ ^ (k + k), π₀ ^ (-k), ?_, zpow_ne_zero (-k) hπ₀_ne, ?_⟩
    · rw [Valuation.map_mul, map_zpow₀, hval_w, hπ₀, ← WithZero.exp_zsmul, ← WithZero.exp_add]
      have hzero : k + k + (k + k) • (-1 : ℤ) = 0 := by
        rw [smul_eq_mul]
        ring
      rw [hzero, WithZero.exp_zero]
    · rw [sq, mul_assoc, ← zpow_add₀ hπ₀_ne, ← zpow_add₀ hπ₀_ne]
      have hzero : (k + k) + (-k + -k) = 0 := by ring
      rw [hzero, zpow_zero, mul_one]
  obtain ⟨u_x, z_x, hux, hzx, hxeq⟩ := h_even_factor x hx
  obtain ⟨u_y, z_y, huy, hzy, hyeq⟩ := h_even_factor y hy
  have h_units : hilbFin v u_x u_y = 1 := hilbFin_eq_one_of_units u_x u_y hux huy h2_val
  simp only [hilbFin, hilbLoc] at h_units ⊢
  split_ifs at h_units with hsol
  · rcases hsol with ⟨Z, W, hZW⟩
    have hZx : algebraMap K (v.adicCompletion K) z_x ≠ 0 := by
      rw [ne_eq, map_eq_zero]
      exact hzx
    have hZy : algebraMap K (v.adicCompletion K) z_y ≠ 0 := by
      rw [ne_eq, map_eq_zero]
      exact hzy
    have hsol' : ∃ X Y : v.adicCompletion K,
        algebraMap K (v.adicCompletion K) (x : K) * X ^ 2 +
          algebraMap K (v.adicCompletion K) (y : K) * Y ^ 2 = 1 := by
      refine ⟨Z / algebraMap K (v.adicCompletion K) z_x,
        W / algebraMap K (v.adicCompletion K) z_y, ?_⟩
      rw [hxeq, hyeq, map_mul, map_mul, map_pow, map_pow]
      have h1 : algebraMap K (v.adicCompletion K) u_x *
          (algebraMap K (v.adicCompletion K) z_x) ^ 2 *
          (Z / algebraMap K (v.adicCompletion K) z_x) ^ 2 =
          algebraMap K (v.adicCompletion K) u_x * Z ^ 2 := by
        field_simp [hZx]
      have h2 : algebraMap K (v.adicCompletion K) u_y *
          (algebraMap K (v.adicCompletion K) z_y) ^ 2 *
          (W / algebraMap K (v.adicCompletion K) z_y) ^ 2 =
          algebraMap K (v.adicCompletion K) u_y * W ^ 2 := by
        field_simp [hZy]
      rw [h1, h2, hZW]
    rw [if_pos hsol']
  · exfalso
    revert h_units
    decide

theorem hilbFin_pairing_eq_one_of_ramLocal {K : Type u} [Field K] [NumberField K]
    (a₁ a₂ a₃ : K) (h₁₂ : a₁ ≠ a₂) (h₁₃ : a₁ ≠ a₃) (h₂₃ : a₂ ≠ a₃)
    (hint₁ : IsIntegral ℤ a₁) (hint₂ : IsIntegral ℤ a₂) (hint₃ : IsIntegral ℤ a₃)
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hT : IsGoodT a₁ a₂ a₃ T)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hvT : v ∉ T) (πv : v.adicCompletion K) (hπv : IsLocalUnif v πv)
    (q₁ q₂ p₁ p₂ : Kˣ)
    (hq : RamLocal a₁ a₂ a₃ v πv q₁ q₂) (hp : RamLocal a₁ a₂ a₃ v πv p₁ p₂) :
    hilbFin v (q₁ : K) (p₂ : K) * hilbFin v (q₂ : K) (p₁ : K) = 1 :=
by
  let α : v.adicCompletion K := algebraMap K (v.adicCompletion K) (a₁ - a₂)
  let β : v.adicCompletion K := algebraMap K (v.adicCompletion K) (a₁ - a₃)
  let γ : v.adicCompletion K := algebraMap K (v.adicCompletion K) (a₂ - a₃)
  have h2 : (2 : v.adicCompletion K) ≠ 0 := by
    rw [← map_ofNat (algebraMap K (v.adicCompletion K)) 2, ne_eq, map_eq_zero]
    exact two_ne_zero
  have hα : α ≠ 0 := by
    change algebraMap K (v.adicCompletion K) (a₁ - a₂) ≠ 0
    rw [ne_eq, map_eq_zero, sub_eq_zero]
    exact h₁₂
  have hβ : β ≠ 0 := by
    change algebraMap K (v.adicCompletion K) (a₁ - a₃) ≠ 0
    rw [ne_eq, map_eq_zero, sub_eq_zero]
    exact h₁₃
  have hγ : γ ≠ 0 := by
    change algebraMap K (v.adicCompletion K) (a₂ - a₃) ≠ 0
    rw [ne_eq, map_eq_zero, sub_eq_zero]
    exact h₂₃
  have hsub : β - γ = α := by
    change algebraMap K (v.adicCompletion K) (a₁ - a₃) -
      algebraMap K (v.adicCompletion K) (a₂ - a₃) =
      algebraMap K (v.adicCompletion K) (a₁ - a₂)
    rw [← map_sub]
    congr 1
    ring
  have hπ_ne : πv ≠ 0 := by
    rcases hπv with ⟨n, _, hn⟩
    intro h0
    rw [h0, Valuation.map_zero] at hn
    exact WithZero.coe_ne_zero hn.symm
  have unit_map_ne_zero : ∀ (u : Kˣ), algebraMap K (v.adicCompletion K) (u : K) ≠ 0 := by
    intro u
    rw [ne_eq, map_eq_zero]
    exact u.ne_zero
  have hilbLoc_symm : ∀ (a b : v.adicCompletion K), hilbLoc v a b = hilbLoc v b a := by
    intro a b
    simp only [hilbLoc]
    congr 1
    exact propext ⟨fun ⟨x, y, hxy⟩ => ⟨y, x, by linear_combination hxy⟩,
      fun ⟨x, y, hxy⟩ => ⟨y, x, by linear_combination hxy⟩⟩
  have hilbLoc_mul_symm : ∀ (a b : v.adicCompletion K), hilbLoc v a b * hilbLoc v b a = 1 := by
    intro a b
    rw [hilbLoc_symm a b]
    exact Int.units_mul_self _
  have hilbLoc_congr_left : ∀ (d q b : v.adicCompletion K),
      d ≠ 0 → q ≠ 0 → IsSquare (d * q) → hilbLoc v d b = hilbLoc v q b := by
    have aux : ∀ (d q b : v.adicCompletion K), d ≠ 0 → q ≠ 0 → IsSquare (d * q) →
        (∃ x y : v.adicCompletion K, d * x ^ 2 + b * y ^ 2 = 1) →
        (∃ x y : v.adicCompletion K, q * x ^ 2 + b * y ^ 2 = 1) := by
      intro d q b hd hq ⟨s, hs⟩ ⟨x, y, hxy⟩
      refine ⟨s * x / q, y, ?_⟩
      have hsq : s ^ 2 = d * q := by linear_combination -hs
      have h1 : q * (s * x / q) ^ 2 = d * x ^ 2 := by
        calc q * (s * x / q) ^ 2 = s ^ 2 * x ^ 2 / q := by field_simp [hq]
          _ = (d * q) * x ^ 2 / q := by rw [hsq]
          _ = d * x ^ 2 := by field_simp [hq]
      linear_combination h1 + hxy
    intro d q b hd hq hsq
    have hsq' : IsSquare (q * d) := by rwa [mul_comm]
    simp only [hilbLoc]
    congr 1
    exact propext ⟨aux d q b hd hq hsq, aux q d b hq hd hsq'⟩
  have hilbLoc_congr_right : ∀ (a d q : v.adicCompletion K),
      d ≠ 0 → q ≠ 0 → IsSquare (d * q) → hilbLoc v a d = hilbLoc v a q := by
    intro a d q hd hq hsq
    rw [hilbLoc_symm a d, hilbLoc_symm a q]
    exact hilbLoc_congr_left d q a hd hq hsq
  have hilbLoc_one_left : ∀ (b : v.adicCompletion K), hilbLoc v 1 b = 1 := by
    intro b
    simp only [hilbLoc]
    rw [if_pos ⟨1, 0, by ring⟩]
  have hilbLoc_one_right : ∀ (a : v.adicCompletion K), hilbLoc v a 1 = 1 := by
    intro a
    rw [hilbLoc_symm]
    exact hilbLoc_one_left a
  have hilbLoc_self_neg : ∀ (c : v.adicCompletion K), c ≠ 0 → hilbLoc v c (-c) = 1 := by
    intro c hc
    simp only [hilbLoc]
    rw [if_pos]
    refine ⟨(c + 1) / (2 * c), (c - 1) / (2 * c), ?_⟩
    field_simp [hc, h2]
    ring
  have hilbLoc_ab_neg_ag : hilbLoc v (α * β) (-(α * γ)) = 1 := by
    simp only [hilbLoc]
    rw [if_pos]
    refine ⟨1 / α, 1 / α, ?_⟩
    have hβ_eq : β = α + γ := by linear_combination hsub
    rw [hβ_eq]
    field_simp [hα]
    ring
  have hilbLoc_mul_eq_one_of_sub_eq : ∀ (α' β' γ' : v.adicCompletion K),
      α' ≠ 0 → β' ≠ 0 → γ' ≠ 0 → β' - γ' = α' →
      hilbLoc v (α' * β') (-(πv * γ')) * hilbLoc v (πv * α') (-(πv * β')) = 1 := by
    intro α' β' γ' hα' hβ' hγ' hsub'
    have heq : hilbLoc v (α' * β') (-(πv * γ')) = hilbLoc v (πv * α') (-(πv * β')) := by
      simp only [hilbLoc]
      congr 1
      apply propext
      constructor
      · rintro ⟨x, y, hxy⟩
        by_cases hy : y = 0
        · refine ⟨(πv * α' + 1) / (2 * (πv * α')), α' * x * (πv * α' - 1) / (2 * (πv * α')), ?_⟩
          have hxy0 : (α' * β') * x ^ 2 = 1 := by
            rw [hy] at hxy
            linear_combination hxy
          have hden : 2 * (πv * α') ≠ 0 := mul_ne_zero h2 (mul_ne_zero hπ_ne hα')
          apply mul_right_cancel₀ (pow_ne_zero 2 hden)
          calc ((πv * α') * ((πv * α' + 1) / (2 * (πv * α'))) ^ 2 +
                -(πv * β') * (α' * x * (πv * α' - 1) / (2 * (πv * α'))) ^ 2) * (2 * (πv * α')) ^ 2
            _ = (πv * α') * (πv * α' + 1) ^ 2 - (πv * β') * (α' * x) ^ 2 * (πv * α' - 1) ^ 2 := by
                field_simp [h2, hπ_ne, hα']
                ring
            _ = 1 * (2 * (πv * α')) ^ 2 := by
                linear_combination -(πv * α' * (πv * α' - 1) ^ 2) * hxy0
        · refine ⟨(1 - β' * x) / (πv * γ' * y), (1 - α' * x) / (πv * γ' * y), ?_⟩
          have hden : πv * γ' * y ≠ 0 := mul_ne_zero (mul_ne_zero hπ_ne hγ') hy
          apply mul_right_cancel₀ (pow_ne_zero 2 hden)
          calc ((πv * α') * ((1 - β' * x) / (πv * γ' * y)) ^ 2 +
                -(πv * β') * ((1 - α' * x) / (πv * γ' * y)) ^ 2) * (πv * γ' * y) ^ 2
            _ = (πv * α') * (1 - β' * x) ^ 2 - (πv * β') * (1 - α' * x) ^ 2 := by
                field_simp [hπ_ne, hγ', hy]
                ring
            _ = 1 * (πv * γ' * y) ^ 2 := by
                linear_combination (πv * γ') * hxy - πv * (1 - α' * β' * x ^ 2) * hsub'
      · rintro ⟨u, w, huw⟩
        have hu' : ∃ u' : v.adicCompletion K,
            (πv * α') * u' ^ 2 + -(πv * β') * w ^ 2 = 1 ∧ α' * u' - β' * w ≠ 0 := by
          by_cases hden : α' * u - β' * w = 0
          · refine ⟨-u, by linear_combination huw, ?_⟩
            intro hden2
            have hu0 : u = 0 := by
              apply mul_left_cancel₀ (mul_ne_zero h2 hα')
              linear_combination hden - hden2
            have hw0 : w = 0 := by
              apply mul_left_cancel₀ (mul_ne_zero h2 hβ')
              linear_combination -(hden + hden2)
            have h01 : (0 : v.adicCompletion K) = 1 := by
              rw [hu0, hw0] at huw
              linear_combination huw
            exact zero_ne_one h01
          · exact ⟨u, huw, hden⟩
        rcases hu' with ⟨u', hu'w, hden'⟩
        refine ⟨(u' - w) / (α' * u' - β' * w), 1 / (πv * (α' * u' - β' * w)), ?_⟩
        have hden : πv * (α' * u' - β' * w) ≠ 0 := mul_ne_zero hπ_ne hden'
        apply mul_right_cancel₀ (pow_ne_zero 2 hden)
        calc ((α' * β') * ((u' - w) / (α' * u' - β' * w)) ^ 2 +
              -(πv * γ') * (1 / (πv * (α' * u' - β' * w))) ^ 2) * (πv * (α' * u' - β' * w)) ^ 2
          _ = (α' * β') * πv ^ 2 * (u' - w) ^ 2 - πv * γ' := by
              field_simp [hπ_ne, hden']
              ring
          _ = 1 * (πv * (α' * u' - β' * w)) ^ 2 := by
              linear_combination (πv * γ') * hu'w + πv ^ 2 * (α' * u' ^ 2 - β' * w ^ 2) * hsub'
    rw [heq]
    exact Int.units_mul_self _
  have hg11 : α * β ≠ 0 := mul_ne_zero hα hβ
  have hg12 : πv * α ≠ 0 := mul_ne_zero hπ_ne hα
  have hg21 : -(πv * α) ≠ 0 := neg_ne_zero.mpr hg12
  have hg22 : -(α * γ) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero hα hγ)
  have hg31 : -(πv * β) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero hπ_ne hβ)
  have hg32 : -(πv * γ) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero hπ_ne hγ)
  have hpair12 : hilbLoc v (α * β) (-(α * γ)) * hilbLoc v (πv * α) (-(πv * α)) = 1 := by
    rw [hilbLoc_ab_neg_ag, hilbLoc_self_neg (πv * α) hg12, mul_one]
  have hpair21 : hilbLoc v (-(πv * α)) (πv * α) * hilbLoc v (-(α * γ)) (α * β) = 1 := by
    rw [hilbLoc_symm (-(πv * α)) (πv * α), hilbLoc_symm (-(α * γ)) (α * β), mul_comm]
    exact hpair12
  have hpair13 : hilbLoc v (α * β) (-(πv * γ)) * hilbLoc v (πv * α) (-(πv * β)) = 1 :=
    hilbLoc_mul_eq_one_of_sub_eq α β γ hα hβ hγ hsub
  have hpair31 : hilbLoc v (-(πv * β)) (πv * α) * hilbLoc v (-(πv * γ)) (α * β) = 1 := by
    rw [hilbLoc_symm (-(πv * β)) (πv * α), hilbLoc_symm (-(πv * γ)) (α * β), mul_comm]
    exact hpair13
  have hpair23 : hilbLoc v (-(πv * α)) (-(πv * γ)) * hilbLoc v (-(α * γ)) (-(πv * β)) = 1 := by
    have h23' := hilbLoc_mul_eq_one_of_sub_eq (-α) γ β (neg_ne_zero.mpr hα) hγ hβ
      (by linear_combination -hsub)
    rw [neg_mul, mul_neg] at h23'
    rw [mul_comm]
    exact h23'
  have hpair32 : hilbLoc v (-(πv * β)) (-(α * γ)) * hilbLoc v (-(πv * γ)) (-(πv * α)) = 1 := by
    rw [hilbLoc_symm (-(πv * β)) (-(α * γ)), hilbLoc_symm (-(πv * γ)) (-(πv * α)), mul_comm]
    exact hpair23
  have ramLocal_cases : ∀ (x₁ x₂ : Kˣ), RamLocal a₁ a₂ a₃ v πv x₁ x₂ →
      let X₁ := algebraMap K (v.adicCompletion K) (x₁ : K)
      let X₂ := algebraMap K (v.adicCompletion K) (x₂ : K)
      (IsSquare (X₁ * 1) ∧ IsSquare (X₂ * 1)) ∨
      (IsSquare (X₁ * (α * β)) ∧ IsSquare (X₂ * (πv * α))) ∨
      (IsSquare (X₁ * -(πv * α)) ∧ IsSquare (X₂ * -(α * γ))) ∨
      (IsSquare (X₁ * -(πv * β)) ∧ IsSquare (X₂ * -(πv * γ))) := by
    intro x₁ x₂ hx
    dsimp only
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      exact ⟨by simpa only [mul_one] using h1, by simpa only [mul_one] using h2⟩
    · right; left
      refine ⟨?_, ?_⟩
      · rcases h1 with ⟨s, hs⟩
        refine ⟨s, ?_⟩
        change algebraMap K (v.adicCompletion K) (x₁ : K) *
          (algebraMap K (v.adicCompletion K) (a₁ - a₂) *
            algebraMap K (v.adicCompletion K) (a₁ - a₃)) = s * s
        rw [← hs]
        push_cast
        ring
      · rcases h2 with ⟨s, hs⟩
        refine ⟨s, ?_⟩
        change algebraMap K (v.adicCompletion K) (x₂ : K) *
          (πv * algebraMap K (v.adicCompletion K) (a₁ - a₂)) = s * s
        rw [← hs]
        push_cast
        ring
    · right; right; left
      refine ⟨?_, ?_⟩
      · rcases h1 with ⟨s, hs⟩
        refine ⟨s, ?_⟩
        change algebraMap K (v.adicCompletion K) (x₁ : K) *
          -(πv * algebraMap K (v.adicCompletion K) (a₁ - a₂)) = s * s
        rw [← hs]
        push_cast
        ring
      · rcases h2 with ⟨s, hs⟩
        refine ⟨s, ?_⟩
        change algebraMap K (v.adicCompletion K) (x₂ : K) *
          -(algebraMap K (v.adicCompletion K) (a₁ - a₂) *
            algebraMap K (v.adicCompletion K) (a₂ - a₃)) = s * s
        rw [← hs]
        push_cast
        ring
    · right; right; right
      refine ⟨?_, ?_⟩
      · rcases h1 with ⟨s, hs⟩
        refine ⟨s, ?_⟩
        change algebraMap K (v.adicCompletion K) (x₁ : K) *
          -(πv * algebraMap K (v.adicCompletion K) (a₁ - a₃)) = s * s
        rw [← hs]
        push_cast
        ring
      · rcases h2 with ⟨s, hs⟩
        refine ⟨s, ?_⟩
        change algebraMap K (v.adicCompletion K) (x₂ : K) *
          -(πv * algebraMap K (v.adicCompletion K) (a₂ - a₃)) = s * s
        rw [← hs]
        push_cast
        ring
  simp only [hilbFin]
  have hq' := ramLocal_cases q₁ q₂ hq
  have hp' := ramLocal_cases p₁ p₂ hp
  dsimp only at hq' hp'
  rcases hq' with ⟨hq1, hq2⟩ | ⟨hq1, hq2⟩ | ⟨hq1, hq2⟩ | ⟨hq1, hq2⟩
  · rw [hilbLoc_congr_left _ _ _ (unit_map_ne_zero q₁) one_ne_zero hq1,
        hilbLoc_congr_left _ _ _ (unit_map_ne_zero q₂) one_ne_zero hq2,
        hilbLoc_one_left, hilbLoc_one_left, mul_one]
  · rw [hilbLoc_congr_left _ _ _ (unit_map_ne_zero q₁) hg11 hq1,
        hilbLoc_congr_left _ _ _ (unit_map_ne_zero q₂) hg12 hq2]
    rcases hp' with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
    · rw [hilbLoc_congr_right _ _ _ (unit_map_ne_zero p₂) one_ne_zero hp2,
          hilbLoc_congr_right _ _ _ (unit_map_ne_zero p₁) one_ne_zero hp1,
          hilbLoc_one_right, hilbLoc_one_right, mul_one]
    · rw [hilbLoc_congr_right _ _ _ (unit_map_ne_zero p₂) hg12 hp2,
          hilbLoc_congr_right _ _ _ (unit_map_ne_zero p₁) hg11 hp1]
      exact hilbLoc_mul_symm _ _
    · rw [hilbLoc_congr_right _ _ _ (unit_map_ne_zero p₂) hg22 hp2,
          hilbLoc_congr_right _ _ _ (unit_map_ne_zero p₁) hg21 hp1]
      exact hpair12
    · rw [hilbLoc_congr_right _ _ _ (unit_map_ne_zero p₂) hg32 hp2,
          hilbLoc_congr_right _ _ _ (unit_map_ne_zero p₁) hg31 hp1]
      exact hpair13
  · rw [hilbLoc_congr_left _ _ _ (unit_map_ne_zero q₁) hg21 hq1,
        hilbLoc_congr_left _ _ _ (unit_map_ne_zero q₂) hg22 hq2]
    rcases hp' with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
    · rw [hilbLoc_congr_right _ _ _ (unit_map_ne_zero p₂) one_ne_zero hp2,
          hilbLoc_congr_right _ _ _ (unit_map_ne_zero p₁) one_ne_zero hp1,
          hilbLoc_one_right, hilbLoc_one_right, mul_one]
    · rw [hilbLoc_congr_right _ _ _ (unit_map_ne_zero p₂) hg12 hp2,
          hilbLoc_congr_right _ _ _ (unit_map_ne_zero p₁) hg11 hp1]
      exact hpair21
    · rw [hilbLoc_congr_right _ _ _ (unit_map_ne_zero p₂) hg22 hp2,
          hilbLoc_congr_right _ _ _ (unit_map_ne_zero p₁) hg21 hp1]
      exact hilbLoc_mul_symm _ _
    · rw [hilbLoc_congr_right _ _ _ (unit_map_ne_zero p₂) hg32 hp2,
          hilbLoc_congr_right _ _ _ (unit_map_ne_zero p₁) hg31 hp1]
      exact hpair23
  · rw [hilbLoc_congr_left _ _ _ (unit_map_ne_zero q₁) hg31 hq1,
        hilbLoc_congr_left _ _ _ (unit_map_ne_zero q₂) hg32 hq2]
    rcases hp' with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
    · rw [hilbLoc_congr_right _ _ _ (unit_map_ne_zero p₂) one_ne_zero hp2,
          hilbLoc_congr_right _ _ _ (unit_map_ne_zero p₁) one_ne_zero hp1,
          hilbLoc_one_right, hilbLoc_one_right, mul_one]
    · rw [hilbLoc_congr_right _ _ _ (unit_map_ne_zero p₂) hg12 hp2,
          hilbLoc_congr_right _ _ _ (unit_map_ne_zero p₁) hg11 hp1]
      exact hpair31
    · rw [hilbLoc_congr_right _ _ _ (unit_map_ne_zero p₂) hg22 hp2,
          hilbLoc_congr_right _ _ _ (unit_map_ne_zero p₁) hg21 hp1]
      exact hpair32
    · rw [hilbLoc_congr_right _ _ _ (unit_map_ne_zero p₂) hg32 hp2,
          hilbLoc_congr_right _ _ _ (unit_map_ne_zero p₁) hg31 hp1]
      exact hilbLoc_mul_symm _ _

theorem hilbInf_pairing_eq_one_of_isDescentClass {K : Type u} [Field K] [NumberField K]
    (a₁ a₂ a₃ : K) (h₁₂ : a₁ ≠ a₂) (h₁₃ : a₁ ≠ a₃) (h₂₃ : a₂ ≠ a₃)
    (w : NumberField.InfinitePlace K) (q₁ q₂ p₁ p₂ : Kˣ)
    (hq : IsDescentClass
      (algebraMap K w.Completion a₁)
      (algebraMap K w.Completion a₂)
      (algebraMap K w.Completion a₃)
      (algebraMap K w.Completion (q₁ : K))
      (algebraMap K w.Completion (q₂ : K)))
    (hp : IsDescentClass
      (algebraMap K w.Completion a₁)
      (algebraMap K w.Completion a₂)
      (algebraMap K w.Completion a₃)
      (algebraMap K w.Completion (p₁ : K))
      (algebraMap K w.Completion (p₂ : K))) :
    hilbInf w (q₁ : K) (p₂ : K) * hilbInf w (q₂ : K) (p₁ : K) = 1 :=
by
  classical
  by_cases hw : w.IsReal
  · set σ := NumberField.InfinitePlace.embedding_of_isReal hw
    set Φ := NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
    have hbij : Function.Bijective (⇑Φ) :=
      NumberField.InfinitePlace.Completion.bijective_extensionEmbeddingOfIsReal hw
    have hcoe : ∀ x : K, Φ (algebraMap K w.Completion x) = σ x := fun x =>
      NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw x
    have hilbInf_pos_left : ∀ (a b : K), 0 < σ a → hilbInf w a b = 1 := by
      intro a b ha
      obtain ⟨x, hx⟩ := hbij.surjective (Real.sqrt (σ a)⁻¹)
      have hex : ∃ x y : w.Completion,
          algebraMap K w.Completion a * x ^ 2 + algebraMap K w.Completion b * y ^ 2 = 1 := by
        refine ⟨x, 0, hbij.injective ?_⟩
        simp only [map_add, map_mul, map_pow, hcoe, hx, map_zero,
          zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero, map_one]
        rw [Real.sq_sqrt (inv_nonneg.mpr ha.le)]
        exact mul_inv_cancel₀ (ne_of_gt ha)
      simp only [hilbInf, hilbInfLoc]
      exact if_pos hex
    have hilbInf_pos_right : ∀ (a b : K), 0 < σ b → hilbInf w a b = 1 := by
      intro a b hb
      obtain ⟨y, hy⟩ := hbij.surjective (Real.sqrt (σ b)⁻¹)
      have hex : ∃ x y : w.Completion,
          algebraMap K w.Completion a * x ^ 2 + algebraMap K w.Completion b * y ^ 2 = 1 := by
        refine ⟨0, y, hbij.injective ?_⟩
        simp only [map_add, map_mul, map_pow, hcoe, hy, map_zero,
          zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add, map_one]
        rw [Real.sq_sqrt (inv_nonneg.mpr hb.le)]
        exact mul_inv_cancel₀ (ne_of_gt hb)
      simp only [hilbInf, hilbInfLoc]
      exact if_pos hex
    have hilbInf_neg : ∀ (a b : K), σ a < 0 → σ b < 0 → hilbInf w a b = -1 := by
      intro a b ha hb
      have hne : ¬ (∃ x y : w.Completion,
          algebraMap K w.Completion a * x ^ 2 + algebraMap K w.Completion b * y ^ 2 = 1) := by
        rintro ⟨x, y, hxy⟩
        have hR : Φ (algebraMap K w.Completion a * x ^ 2 + algebraMap K w.Completion b * y ^ 2) = Φ 1 :=
          congrArg Φ hxy
        simp only [map_add, map_mul, map_pow, hcoe, map_one] at hR
        nlinarith [sq_nonneg (Φ x), sq_nonneg (Φ y),
          mul_nonpos_of_nonpos_of_nonneg ha.le (sq_nonneg (Φ x)),
          mul_nonpos_of_nonpos_of_nonneg hb.le (sq_nonneg (Φ y))]
      simp only [hilbInf, hilbInfLoc]
      exact if_neg hne
    have hA12 : σ a₁ ≠ σ a₂ := fun h => h₁₂ (σ.injective h)
    have hA13 : σ a₁ ≠ σ a₃ := fun h => h₁₃ (σ.injective h)
    have hA23 : σ a₂ ≠ σ a₃ := fun h => h₂₃ (σ.injective h)
    have descent_signs : ∀ (d₁ d₂ : Kˣ),
        IsDescentClass
          (algebraMap K w.Completion a₁)
          (algebraMap K w.Completion a₂)
          (algebraMap K w.Completion a₃)
          (algebraMap K w.Completion (d₁ : K))
          (algebraMap K w.Completion (d₂ : K)) →
        (0 < σ (d₁ : K) ∧ 0 < σ (d₂ : K)) ∨
        (σ (d₁ : K) < 0 ∧ 0 < σ (d₂ : K) ∧ σ a₂ < σ a₁ ∧ σ a₂ < σ a₃) ∨
        (0 < σ (d₁ : K) ∧ σ (d₂ : K) < 0 ∧ σ a₁ < σ a₂ ∧ σ a₁ < σ a₃) ∨
        (σ (d₁ : K) < 0 ∧ σ (d₂ : K) < 0 ∧ σ a₃ < σ a₁ ∧ σ a₃ < σ a₂) := by
      intro d₁ d₂ ⟨z₀, z₁, z₂, z₃, hnz, heq1, heq2⟩
      have hD1 : σ (d₁ : K) ≠ 0 := fun h => d₁.ne_zero (σ.injective (by rw [h, map_zero]))
      have hD2 : σ (d₂ : K) ≠ 0 := fun h => d₂.ne_zero (σ.injective (by rw [h, map_zero]))
      set Z₀ := Φ z₀
      set Z₁ := Φ z₁
      set Z₂ := Φ z₂
      set Z₃ := Φ z₃
      have hZ_nz : ¬ (Z₀ = 0 ∧ Z₁ = 0 ∧ Z₂ = 0 ∧ Z₃ = 0) := by
        rintro ⟨h0, h1, h2, h3⟩
        apply hnz
        exact ⟨hbij.injective (by rw [map_zero]; exact h0),
               hbij.injective (by rw [map_zero]; exact h1),
               hbij.injective (by rw [map_zero]; exact h2),
               hbij.injective (by rw [map_zero]; exact h3)⟩
      have hE1 : σ (d₁ : K) * Z₁ ^ 2 - σ (d₂ : K) * Z₂ ^ 2 = (σ a₂ - σ a₁) * Z₀ ^ 2 := by
        have h := congrArg Φ heq1
        simpa only [map_sub, map_mul, map_pow, hcoe] using h
      have hE2 : σ (d₁ : K) * Z₁ ^ 2 - σ (d₁ : K) * σ (d₂ : K) * Z₃ ^ 2 = (σ a₃ - σ a₁) * Z₀ ^ 2 := by
        have h := congrArg Φ heq2
        simpa only [map_sub, map_mul, map_pow, hcoe] using h
      have hE3 : σ (d₂ : K) * Z₂ ^ 2 - σ (d₁ : K) * σ (d₂ : K) * Z₃ ^ 2 = (σ a₃ - σ a₂) * Z₀ ^ 2 := by
        linear_combination hE2 - hE1
      have hZ0_zero : Z₀ = 0 → 0 < σ (d₁ : K) ∧ 0 < σ (d₂ : K) := by
        intro hZ0
        have h1 : σ (d₁ : K) * (Z₁ ^ 2 - σ (d₂ : K) * Z₃ ^ 2) = 0 := by
          calc σ (d₁ : K) * (Z₁ ^ 2 - σ (d₂ : K) * Z₃ ^ 2)
            _ = (σ a₃ - σ a₁) * Z₀ ^ 2 := by linear_combination hE2
            _ = 0 := by rw [hZ0]; ring
        have h2 : σ (d₂ : K) * (Z₂ ^ 2 - σ (d₁ : K) * Z₃ ^ 2) = 0 := by
          calc σ (d₂ : K) * (Z₂ ^ 2 - σ (d₁ : K) * Z₃ ^ 2)
            _ = (σ a₃ - σ a₂) * Z₀ ^ 2 := by linear_combination hE3
            _ = 0 := by rw [hZ0]; ring
        have h1' : Z₁ ^ 2 = σ (d₂ : K) * Z₃ ^ 2 :=
          sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hD1)
        have h2' : Z₂ ^ 2 = σ (d₁ : K) * Z₃ ^ 2 :=
          sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hD2)
        have hZ3_nz : Z₃ ≠ 0 := by
          intro hZ3
          have hZ1 : Z₁ = 0 := sq_eq_zero_iff.mp (by rw [h1', hZ3]; ring)
          have hZ2 : Z₂ = 0 := sq_eq_zero_iff.mp (by rw [h2', hZ3]; ring)
          exact hZ_nz ⟨hZ0, hZ1, hZ2, hZ3⟩
        have hZ3_pos : 0 < Z₃ ^ 2 := sq_pos_of_ne_zero hZ3_nz
        have hD1_nonneg : 0 ≤ σ (d₁ : K) := by
          nlinarith [sq_nonneg Z₂, h2', hZ3_pos]
        have hD2_nonneg : 0 ≤ σ (d₂ : K) := by
          nlinarith [sq_nonneg Z₁, h1', hZ3_pos]
        exact ⟨lt_of_le_of_ne hD1_nonneg hD1.symm, lt_of_le_of_ne hD2_nonneg hD2.symm⟩
      by_cases hZ0 : Z₀ = 0
      · exact Or.inl (hZ0_zero hZ0)
      · have hZ0_pos : 0 < Z₀ ^ 2 := sq_pos_of_ne_zero hZ0
        rcases lt_or_gt_of_ne hD1 with hD1_neg | hD1_pos <;>
          rcases lt_or_gt_of_ne hD2 with hD2_neg | hD2_pos
        · right; right; right
          have hle1 : σ a₃ ≤ σ a₁ := by
            nlinarith [hE2, hZ0_pos, sq_nonneg Z₁, sq_nonneg Z₃,
              mul_nonpos_of_nonpos_of_nonneg hD1_neg.le (sq_nonneg Z₁),
              mul_nonneg (mul_pos_of_neg_of_neg hD1_neg hD2_neg).le (sq_nonneg Z₃)]
          have hle2 : σ a₃ ≤ σ a₂ := by
            nlinarith [hE3, hZ0_pos, sq_nonneg Z₂, sq_nonneg Z₃,
              mul_nonpos_of_nonpos_of_nonneg hD2_neg.le (sq_nonneg Z₂),
              mul_nonneg (mul_pos_of_neg_of_neg hD1_neg hD2_neg).le (sq_nonneg Z₃)]
          exact ⟨hD1_neg, hD2_neg, lt_of_le_of_ne hle1 hA13.symm, lt_of_le_of_ne hle2 hA23.symm⟩
        · right; left
          have hle1 : σ a₂ ≤ σ a₁ := by
            nlinarith [hE1, hZ0_pos, sq_nonneg Z₁, sq_nonneg Z₂,
              mul_nonpos_of_nonpos_of_nonneg hD1_neg.le (sq_nonneg Z₁),
              mul_nonneg hD2_pos.le (sq_nonneg Z₂)]
          have hle2 : σ a₂ ≤ σ a₃ := by
            nlinarith [hE3, hZ0_pos, sq_nonneg Z₂, sq_nonneg Z₃,
              mul_nonneg hD2_pos.le (sq_nonneg Z₂),
              mul_nonpos_of_nonpos_of_nonneg (mul_neg_of_neg_of_pos hD1_neg hD2_pos).le (sq_nonneg Z₃)]
          exact ⟨hD1_neg, hD2_pos, lt_of_le_of_ne hle1 hA12.symm, lt_of_le_of_ne hle2 hA23⟩
        · right; right; left
          have hle1 : σ a₁ ≤ σ a₂ := by
            nlinarith [hE1, hZ0_pos, sq_nonneg Z₁, sq_nonneg Z₂,
              mul_nonneg hD1_pos.le (sq_nonneg Z₁),
              mul_nonpos_of_nonpos_of_nonneg hD2_neg.le (sq_nonneg Z₂)]
          have hle2 : σ a₁ ≤ σ a₃ := by
            nlinarith [hE2, hZ0_pos, sq_nonneg Z₁, sq_nonneg Z₃,
              mul_nonneg hD1_pos.le (sq_nonneg Z₁),
              mul_nonpos_of_nonpos_of_nonneg (mul_neg_of_pos_of_neg hD1_pos hD2_neg).le (sq_nonneg Z₃)]
          exact ⟨hD1_pos, hD2_neg, lt_of_le_of_ne hle1 hA12, lt_of_le_of_ne hle2 hA13⟩
        · exact Or.inl ⟨hD1_pos, hD2_pos⟩
    rcases descent_signs q₁ q₂ hq with
      ⟨hq1, hq2⟩ | ⟨hq1, hq2, hqA1, hqA2⟩ | ⟨hq1, hq2, hqA1, hqA2⟩ | ⟨hq1, hq2, hqA1, hqA2⟩
    · rw [hilbInf_pos_left (q₁ : K) (p₂ : K) hq1, hilbInf_pos_left (q₂ : K) (p₁ : K) hq2, mul_one]
    · rcases descent_signs p₁ p₂ hp with
        ⟨hp1, hp2⟩ | ⟨hp1, hp2, hpA1, hpA2⟩ | ⟨hp1, hp2, hpA1, hpA2⟩ | ⟨hp1, hp2, hpA1, hpA2⟩
      · rw [hilbInf_pos_right (q₁ : K) (p₂ : K) hp2, hilbInf_pos_right (q₂ : K) (p₁ : K) hp1, mul_one]
      · rw [hilbInf_pos_right (q₁ : K) (p₂ : K) hp2, hilbInf_pos_left (q₂ : K) (p₁ : K) hq2, mul_one]
      · linarith
      · linarith
    · rcases descent_signs p₁ p₂ hp with
        ⟨hp1, hp2⟩ | ⟨hp1, hp2, hpA1, hpA2⟩ | ⟨hp1, hp2, hpA1, hpA2⟩ | ⟨hp1, hp2, hpA1, hpA2⟩
      · rw [hilbInf_pos_right (q₁ : K) (p₂ : K) hp2, hilbInf_pos_right (q₂ : K) (p₁ : K) hp1, mul_one]
      · linarith
      · rw [hilbInf_pos_left (q₁ : K) (p₂ : K) hq1, hilbInf_pos_right (q₂ : K) (p₁ : K) hp1, mul_one]
      · linarith
    · rcases descent_signs p₁ p₂ hp with
        ⟨hp1, hp2⟩ | ⟨hp1, hp2, hpA1, hpA2⟩ | ⟨hp1, hp2, hpA1, hpA2⟩ | ⟨hp1, hp2, hpA1, hpA2⟩
      · rw [hilbInf_pos_right (q₁ : K) (p₂ : K) hp2, hilbInf_pos_right (q₂ : K) (p₁ : K) hp1, mul_one]
      · linarith
      · linarith
      · rw [hilbInf_neg (q₁ : K) (p₂ : K) hq1 hp2, hilbInf_neg (q₂ : K) (p₁ : K) hq2 hp1]
        decide
  · have hc : w.IsComplex := NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw
    have e : w.Completion ≃+* ℂ :=
      NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hc
    have hcomplex : ∀ (a : Kˣ) (b : K), hilbInf w (a : K) b = 1 := by
      intro a b
      have ha0 : e (algebraMap K w.Completion (a : K)) ≠ 0 := by
        intro h
        apply a.ne_zero
        apply (algebraMap K w.Completion).injective
        apply e.injective
        rw [h, map_zero, map_zero]
      obtain ⟨c, hc2⟩ :=
        IsAlgClosed.exists_pow_nat_eq (e (algebraMap K w.Completion (a : K)))⁻¹ (n := 2) (by norm_num)
      have hex : ∃ x y : w.Completion,
          algebraMap K w.Completion (a : K) * x ^ 2 + algebraMap K w.Completion b * y ^ 2 = 1 := by
        refine ⟨e.symm c, 0, e.injective ?_⟩
        simp only [map_add, map_mul, map_pow, RingEquiv.apply_symm_apply, map_zero,
          zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero, map_one, hc2]
        exact mul_inv_cancel₀ ha0
      simp only [hilbInf, hilbInfLoc]
      exact if_pos hex
    rw [hcomplex q₁ (p₂ : K), hcomplex q₂ (p₁ : K), mul_one]

theorem hilbFin_pairing_eq_one_of_isDescentClass {K : Type u} [Field K] [NumberField K]
    (a₁ a₂ a₃ : K) (h₁₂ : a₁ ≠ a₂) (h₁₃ : a₁ ≠ a₃) (h₂₃ : a₂ ≠ a₃)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q₁ q₂ p₁ p₂ : Kˣ)
    (hq : IsDescentClass
      (algebraMap K (v.adicCompletion K) a₁)
      (algebraMap K (v.adicCompletion K) a₂)
      (algebraMap K (v.adicCompletion K) a₃)
      (algebraMap K (v.adicCompletion K) (q₁ : K))
      (algebraMap K (v.adicCompletion K) (q₂ : K)))
    (hp : IsDescentClass
      (algebraMap K (v.adicCompletion K) a₁)
      (algebraMap K (v.adicCompletion K) a₂)
      (algebraMap K (v.adicCompletion K) a₃)
      (algebraMap K (v.adicCompletion K) (p₁ : K))
      (algebraMap K (v.adicCompletion K) (p₂ : K))) :
    hilbFin v (q₁ : K) (p₂ : K) * hilbFin v (q₂ : K) (p₁ : K) = 1 :=
by
  let F := v.adicCompletion K
  let ι : K →+* F := algebraMap K F
  have hF2 : (2 : F) ≠ 0 := by
    have h2K : (2 : K) ≠ 0 := two_ne_zero
    intro h2F
    apply h2K
    apply ι.injective
    rw [map_ofNat, h2F, map_zero]
  let e₁ : F := ι a₁
  let e₂ : F := ι a₂
  let e₃ : F := ι a₃
  have h₁₂' : e₁ ≠ e₂ := ι.injective.ne h₁₂
  have h₁₃' : e₁ ≠ e₃ := ι.injective.ne h₁₃
  have h₂₃' : e₂ ≠ e₃ := ι.injective.ne h₂₃
  let Q₁ : F := ι (q₁ : K)
  let Q₂ : F := ι (q₂ : K)
  let P₁ : F := ι (p₁ : K)
  let P₂ : F := ι (p₂ : K)
  have hQ₁ : Q₁ ≠ 0 := by
    rw [ne_eq, map_eq_zero]
    exact q₁.ne_zero
  have hQ₂ : Q₂ ≠ 0 := by
    rw [ne_eq, map_eq_zero]
    exact q₂.ne_zero
  have hP₁ : P₁ ≠ 0 := by
    rw [ne_eq, map_eq_zero]
    exact p₁.ne_zero
  have hP₂ : P₂ ≠ 0 := by
    rw [ne_eq, map_eq_zero]
    exact p₂.ne_zero
  have quat_norm_sol : ∀ (q₂ p₁ C₀ C₁ C₂ C₃ : F),
      q₂ ≠ 0 → p₁ ≠ 0 →
      ¬ (C₀ = 0 ∧ C₁ = 0 ∧ C₂ = 0 ∧ C₃ = 0) →
      C₀ ^ 2 - q₂ * C₁ ^ 2 - p₁ * C₂ ^ 2 + q₂ * p₁ * C₃ ^ 2 = 0 →
      ∃ u w : F, q₂ * u ^ 2 + p₁ * w ^ 2 = 1 := by
    intro q₂ p₁ C₀ C₁ C₂ C₃ hq₂ hp₁ hCne hQ
    let A : F := C₀ * C₂ - q₂ * C₁ * C₃
    let B : F := C₀ * C₃ - C₁ * C₂
    let N : F := C₂ ^ 2 - q₂ * C₃ ^ 2
    have h_Brahma : q₂ * B ^ 2 + p₁ * N ^ 2 - A ^ 2 = 0 := by
      dsimp [A, B, N]
      linear_combination -(C₂ ^ 2 - q₂ * C₃ ^ 2) * hQ
    by_cases hN : N = 0
    · have h_N : C₂ ^ 2 - q₂ * C₃ ^ 2 = 0 := hN
      have h_M : C₀ ^ 2 - q₂ * C₁ ^ 2 = 0 := by
        linear_combination hQ + p₁ * h_N
      by_cases hC₀ : C₀ = 0
      · have hC₁ : C₁ = 0 := by
          have h1 : q₂ * C₁ ^ 2 = 0 := by linear_combination -h_M + C₀ * hC₀
          rcases mul_eq_zero.mp h1 with h | h
          · exact False.elim (hq₂ h)
          · exact pow_eq_zero h
        have hC₂ : C₂ ≠ 0 := by
          intro hC₂
          have hC₃ : C₃ = 0 := by
            have h1 : q₂ * C₃ ^ 2 = 0 := by linear_combination -h_N + C₂ * hC₂
            rcases mul_eq_zero.mp h1 with h | h
            · exact False.elim (hq₂ h)
            · exact pow_eq_zero h
          exact hCne ⟨hC₀, hC₁, hC₂, hC₃⟩
        refine ⟨C₃ / C₂, 0, ?_⟩
        have h_eq : q₂ * C₃ ^ 2 = C₂ ^ 2 := by linear_combination -h_N
        calc q₂ * (C₃ / C₂) ^ 2 + p₁ * 0 ^ 2
          _ = q₂ * C₃ ^ 2 / C₂ ^ 2 := by ring
          _ = C₂ ^ 2 / C₂ ^ 2 := by rw [h_eq]
          _ = 1 := div_self (pow_ne_zero 2 hC₂)
      · refine ⟨C₁ / C₀, 0, ?_⟩
        have h_eq : q₂ * C₁ ^ 2 = C₀ ^ 2 := by linear_combination -h_M
        calc q₂ * (C₁ / C₀) ^ 2 + p₁ * 0 ^ 2
          _ = q₂ * C₁ ^ 2 / C₀ ^ 2 := by ring
          _ = C₀ ^ 2 / C₀ ^ 2 := by rw [h_eq]
          _ = 1 := div_self (pow_ne_zero 2 hC₀)
    · by_cases hA : A = 0
      · have h_BN : q₂ * B ^ 2 + p₁ * N ^ 2 = 0 := by
          linear_combination h_Brahma + A * hA
        have hB : B ≠ 0 := by
          intro hB0
          have h1 : p₁ * N ^ 2 = 0 := by linear_combination h_BN - q₂ * B * hB0
          rcases mul_eq_zero.mp h1 with h | h
          · exact hp₁ h
          · exact hN (pow_eq_zero h)
        refine ⟨B * (q₂ * B ^ 2 + 1) / (2 * q₂ * B ^ 2),
          (q₂ * B ^ 2 - 1) * N / (2 * q₂ * B ^ 2), ?_⟩
        have h_den : (2 * q₂ * B ^ 2) ^ 2 ≠ 0 := by
          apply pow_ne_zero 2
          exact mul_ne_zero (mul_ne_zero hF2 hq₂) (pow_ne_zero 2 hB)
        have h_num : q₂ * (B * (q₂ * B ^ 2 + 1)) ^ 2 + p₁ * ((q₂ * B ^ 2 - 1) * N) ^ 2 =
            (2 * q₂ * B ^ 2) ^ 2 := by
          linear_combination (q₂ * B ^ 2 - 1) ^ 2 * h_BN
        calc q₂ * (B * (q₂ * B ^ 2 + 1) / (2 * q₂ * B ^ 2)) ^ 2 +
              p₁ * ((q₂ * B ^ 2 - 1) * N / (2 * q₂ * B ^ 2)) ^ 2
          _ = (q₂ * (B * (q₂ * B ^ 2 + 1)) ^ 2 + p₁ * ((q₂ * B ^ 2 - 1) * N) ^ 2) /
                (2 * q₂ * B ^ 2) ^ 2 := by
              rw [div_pow, div_pow, ← mul_div_assoc, ← mul_div_assoc, ← add_div]
          _ = (2 * q₂ * B ^ 2) ^ 2 / (2 * q₂ * B ^ 2) ^ 2 := by rw [h_num]
          _ = 1 := div_self h_den
      · refine ⟨B / A, N / A, ?_⟩
        have h_eq : q₂ * B ^ 2 + p₁ * N ^ 2 = A ^ 2 := by linear_combination h_Brahma
        calc q₂ * (B / A) ^ 2 + p₁ * (N / A) ^ 2
          _ = (q₂ * B ^ 2 + p₁ * N ^ 2) / A ^ 2 := by
              rw [div_pow, div_pow, ← mul_div_assoc, ← mul_div_assoc, ← add_div]
          _ = A ^ 2 / A ^ 2 := by rw [h_eq]
          _ = 1 := div_self (pow_ne_zero 2 hA)
  have descent_sol_imp : ∀ (q₁ q₂ p₁ p₂ : F),
      q₁ ≠ 0 → q₂ ≠ 0 → p₁ ≠ 0 → p₂ ≠ 0 →
      IsDescentClass e₁ e₂ e₃ q₁ q₂ →
      IsDescentClass e₁ e₂ e₃ p₁ p₂ →
      (∃ x y : F, q₁ * x ^ 2 + p₂ * y ^ 2 = 1) →
      (∃ u w : F, q₂ * u ^ 2 + p₁ * w ^ 2 = 1) := by
    intro q₁ q₂ p₁ p₂ hq₁ hq₂ hp₁ hp₂ hq_desc hp_desc ⟨x, y, hxy⟩
    rcases hq_desc with ⟨z₀, z₁, z₂, z₃, hzne, hz12, hz13⟩
    rcases hp_desc with ⟨w₀, w₁, w₂, w₃, hwne, hw12, hw13⟩
    by_cases hz₀ : z₀ = 0
    · have hz₁ : z₁ ≠ 0 := by
        intro hz₁
        have hz₂ : z₂ = 0 := by
          have h1 : q₂ * z₂ ^ 2 = 0 := by
            linear_combination -hz12 + q₁ * z₁ * hz₁ - (e₂ - e₁) * z₀ * hz₀
          rcases mul_eq_zero.mp h1 with h | h
          · exact False.elim (hq₂ h)
          · exact pow_eq_zero h
        have hz₃ : z₃ = 0 := by
          have h1 : q₁ * (q₂ * z₃ ^ 2) = 0 := by
            linear_combination -hz13 + q₁ * z₁ * hz₁ - (e₃ - e₁) * z₀ * hz₀
          rcases mul_eq_zero.mp h1 with h | h
          · exact False.elim (hq₁ h)
          · rcases mul_eq_zero.mp h with h' | h'
            · exact False.elim (hq₂ h')
            · exact pow_eq_zero h'
        exact hzne ⟨hz₀, hz₁, hz₂, hz₃⟩
      refine ⟨z₃ / z₁, 0, ?_⟩
      have h_eq : q₁ * (q₂ * z₃ ^ 2 - z₁ ^ 2) = 0 := by
        linear_combination -hz13 - (e₃ - e₁) * z₀ * hz₀
      have h_eq2 : q₂ * z₃ ^ 2 = z₁ ^ 2 := by
        rcases mul_eq_zero.mp h_eq with h | h
        · exact False.elim (hq₁ h)
        · linear_combination h
      calc q₂ * (z₃ / z₁) ^ 2 + p₁ * 0 ^ 2
        _ = q₂ * z₃ ^ 2 / z₁ ^ 2 := by ring
        _ = z₁ ^ 2 / z₁ ^ 2 := by rw [h_eq2]
        _ = 1 := div_self (pow_ne_zero 2 hz₁)
    · by_cases hw₀ : w₀ = 0
      · have hw₂ : w₂ ≠ 0 := by
          intro hw₂
          have hw₁ : w₁ = 0 := by
            have h1 : p₁ * w₁ ^ 2 = 0 := by
              linear_combination hw12 + p₂ * w₂ * hw₂ + (e₂ - e₁) * w₀ * hw₀
            rcases mul_eq_zero.mp h1 with h | h
            · exact False.elim (hp₁ h)
            · exact pow_eq_zero h
          have hw₃ : w₃ = 0 := by
            have h1 : p₁ * (p₂ * w₃ ^ 2) = 0 := by
              linear_combination -hw13 + p₁ * w₁ * hw₁ - (e₃ - e₁) * w₀ * hw₀
            rcases mul_eq_zero.mp h1 with h | h
            · exact False.elim (hp₁ h)
            · rcases mul_eq_zero.mp h with h' | h'
              · exact False.elim (hp₂ h')
              · exact pow_eq_zero h'
          exact hwne ⟨hw₀, hw₁, hw₂, hw₃⟩
        refine ⟨0, w₃ / w₂, ?_⟩
        have h_eq : p₂ * (p₁ * w₃ ^ 2 - w₂ ^ 2) = 0 := by
          linear_combination hw12 - hw13 + (e₂ - e₃) * w₀ * hw₀
        have h_eq2 : p₁ * w₃ ^ 2 = w₂ ^ 2 := by
          rcases mul_eq_zero.mp h_eq with h | h
          · exact False.elim (hp₂ h)
          · linear_combination h
        calc q₂ * 0 ^ 2 + p₁ * (w₃ / w₂) ^ 2
          _ = p₁ * w₃ ^ 2 / w₂ ^ 2 := by ring
          _ = w₂ ^ 2 / w₂ ^ 2 := by rw [h_eq2]
          _ = 1 := div_self (pow_ne_zero 2 hw₂)
      · let Z₁ : F := z₁ * w₀
        let Z₂ : F := z₂ * w₀
        let Z₃ : F := z₃ * w₀
        let W₁ : F := w₁ * z₀
        let W₂ : F := w₂ * z₀
        let W₃ : F := w₃ * z₀
        have h₁ : q₁ * Z₁ ^ 2 - p₁ * W₁ ^ 2 - q₂ * Z₂ ^ 2 + p₂ * W₂ ^ 2 = 0 := by
          dsimp [Z₁, Z₂, W₁, W₂]
          linear_combination w₀ ^ 2 * hz12 - z₀ ^ 2 * hw12
        have h₂ : q₁ * q₂ * Z₃ ^ 2 - p₁ * p₂ * W₃ ^ 2 - q₂ * Z₂ ^ 2 + p₂ * W₂ ^ 2 = 0 := by
          dsimp [Z₂, Z₃, W₂, W₃]
          linear_combination w₀ ^ 2 * hz12 - w₀ ^ 2 * hz13 - z₀ ^ 2 * hw12 + z₀ ^ 2 * hw13
        have hZ₁_imp : Z₁ = 0 → Z₂ ≠ 0 ∧ Z₃ ≠ 0 := by
          intro hZ₁0
          have hz₁0 : z₁ = 0 := by
            rcases mul_eq_zero.mp hZ₁0 with h | h
            · exact h
            · exact False.elim (hw₀ h)
          constructor
          · intro hZ₂0
            have hz₂0 : z₂ = 0 := by
              rcases mul_eq_zero.mp hZ₂0 with h | h
              · exact h
              · exact False.elim (hw₀ h)
            have h1 : (e₂ - e₁) * z₀ ^ 2 = 0 := by
              linear_combination -hz12 + q₁ * z₁ * hz₁0 - q₂ * z₂ * hz₂0
            rcases mul_eq_zero.mp h1 with h | h
            · exact h₁₂' (sub_eq_zero.mp h).symm
            · exact hz₀ (pow_eq_zero h)
          · intro hZ₃0
            have hz₃0 : z₃ = 0 := by
              rcases mul_eq_zero.mp hZ₃0 with h | h
              · exact h
              · exact False.elim (hw₀ h)
            have h1 : (e₃ - e₁) * z₀ ^ 2 = 0 := by
              linear_combination -hz13 + q₁ * z₁ * hz₁0 - q₁ * q₂ * z₃ * hz₃0
            rcases mul_eq_zero.mp h1 with h | h
            · exact h₁₃' (sub_eq_zero.mp h).symm
            · exact hz₀ (pow_eq_zero h)
        have hW₂_imp : W₂ = 0 → W₁ ≠ 0 ∧ W₃ ≠ 0 := by
          intro hW₂0
          have hw₂0 : w₂ = 0 := by
            rcases mul_eq_zero.mp hW₂0 with h | h
            · exact h
            · exact False.elim (hz₀ h)
          constructor
          · intro hW₁0
            have hw₁0 : w₁ = 0 := by
              rcases mul_eq_zero.mp hW₁0 with h | h
              · exact h
              · exact False.elim (hz₀ h)
            have h1 : (e₂ - e₁) * w₀ ^ 2 = 0 := by
              linear_combination -hw12 + p₁ * w₁ * hw₁0 - p₂ * w₂ * hw₂0
            rcases mul_eq_zero.mp h1 with h | h
            · exact h₁₂' (sub_eq_zero.mp h).symm
            · exact hw₀ (pow_eq_zero h)
          · intro hW₃0
            have hw₃0 : w₃ = 0 := by
              rcases mul_eq_zero.mp hW₃0 with h | h
              · exact h
              · exact False.elim (hz₀ h)
            have h1 : (e₃ - e₂) * w₀ ^ 2 = 0 := by
              linear_combination hw12 - hw13 + p₂ * w₂ * hw₂0 - p₁ * p₂ * w₃ * hw₃0
            rcases mul_eq_zero.mp h1 with h | h
            · exact h₂₃' (sub_eq_zero.mp h).symm
            · exact hw₀ (pow_eq_zero h)
        have h_quat_id : ∀ (x' y' : F), q₁ * x' ^ 2 + p₂ * y' ^ 2 = 1 →
            (W₂ * Z₁ + q₂ * y' * Z₂ * Z₃ + p₁ * x' * W₁ * W₃) ^ 2 -
            q₂ * (W₂ * Z₃ + y' * Z₁ * Z₂) ^ 2 -
            p₁ * (W₃ * Z₁ + x' * W₁ * W₂) ^ 2 +
            q₂ * p₁ * (W₁ * y' * Z₃ - x' * W₃ * Z₂) ^ 2 = 0 := by
          intro x' y' hxy'
          linear_combination
            -(q₂ * Z₃ ^ 2 * y' ^ 2 - (W₂ ^ 2 - p₁ * W₃ ^ 2) * x' ^ 2) * h₁ -
            (W₂ ^ 2 * x' ^ 2 - Z₁ ^ 2 * y' ^ 2) * h₂ -
            (Z₁ ^ 2 * (W₂ ^ 2 - p₁ * W₃ ^ 2) - q₂ * W₂ ^ 2 * Z₃ ^ 2) * hxy'
        by_cases h_c1 : ¬ (W₂ * Z₁ + q₂ * y * Z₂ * Z₃ + p₁ * x * W₁ * W₃ = 0 ∧
            W₂ * Z₃ + y * Z₁ * Z₂ = 0 ∧
            W₃ * Z₁ + x * W₁ * W₂ = 0 ∧
            W₁ * y * Z₃ - x * W₃ * Z₂ = 0)
        · exact quat_norm_sol q₂ p₁
            (W₂ * Z₁ + q₂ * y * Z₂ * Z₃ + p₁ * x * W₁ * W₃)
            (W₂ * Z₃ + y * Z₁ * Z₂)
            (W₃ * Z₁ + x * W₁ * W₂)
            (W₁ * y * Z₃ - x * W₃ * Z₂)
            hq₂ hp₁ h_c1 (h_quat_id x y hxy)
        · push_neg at h_c1
          by_cases h_c2 : ¬ (W₂ * Z₁ + q₂ * y * Z₂ * Z₃ + p₁ * (-x) * W₁ * W₃ = 0 ∧
              W₂ * Z₃ + y * Z₁ * Z₂ = 0 ∧
              W₃ * Z₁ + (-x) * W₁ * W₂ = 0 ∧
              W₁ * y * Z₃ - (-x) * W₃ * Z₂ = 0)
          · have hxy2 : q₁ * (-x) ^ 2 + p₂ * y ^ 2 = 1 := by linear_combination hxy
            exact quat_norm_sol q₂ p₁
              (W₂ * Z₁ + q₂ * y * Z₂ * Z₃ + p₁ * (-x) * W₁ * W₃)
              (W₂ * Z₃ + y * Z₁ * Z₂)
              (W₃ * Z₁ + (-x) * W₁ * W₂)
              (W₁ * y * Z₃ - (-x) * W₃ * Z₂)
              hq₂ hp₁ h_c2 (h_quat_id (-x) y hxy2)
          · push_neg at h_c2
            have h_c3 : ¬ (W₂ * Z₁ + q₂ * (-y) * Z₂ * Z₃ + p₁ * (-x) * W₁ * W₃ = 0 ∧
                W₂ * Z₃ + (-y) * Z₁ * Z₂ = 0 ∧
                W₃ * Z₁ + (-x) * W₁ * W₂ = 0 ∧
                W₁ * (-y) * Z₃ - (-x) * W₃ * Z₂ = 0) := by
              rintro ⟨hc3_0, hc3_1, hc3_2, hc3_3⟩
              rcases h_c1 with ⟨hc1_0, hc1_1, hc1_2, hc1_3⟩
              rcases h_c2 with ⟨hc2_0, hc2_1, hc2_2, hc2_3⟩
              have hWZ : 2 * (W₂ * Z₁) = 0 := by linear_combination hc1_0 + hc3_0
              have hWZ' : W₂ * Z₁ = 0 := by
                rcases mul_eq_zero.mp hWZ with h | h
                · exact False.elim (hF2 h)
                · exact h
              by_cases hZ₁ : Z₁ = 0
              · obtain ⟨hZ₂, hZ₃⟩ := hZ₁_imp hZ₁
                by_cases hW₂ : W₂ = 0
                · obtain ⟨hW₁, hW₃⟩ := hW₂_imp hW₂
                  have hy0 : y = 0 := by
                    have h1 : (2 * W₁ * Z₃) * y = 0 := by linear_combination hc1_3 + hc2_3
                    rcases mul_eq_zero.mp h1 with h | h
                    · exact False.elim (mul_ne_zero (mul_ne_zero hF2 hW₁) hZ₃ h)
                    · exact h
                  have hx0 : x = 0 := by
                    have h1 : (2 * W₃ * Z₂) * x = 0 := by linear_combination hc2_3 - hc1_3
                    rcases mul_eq_zero.mp h1 with h | h
                    · exact False.elim (mul_ne_zero (mul_ne_zero hF2 hW₃) hZ₂ h)
                    · exact h
                  have h_one : (1 : F) = 0 := by
                    linear_combination -hxy + q₁ * x * hx0 + p₂ * y * hy0
                  exact one_ne_zero h_one
                · have h1 : W₂ * Z₃ = 0 := by
                    linear_combination hc1_1 - y * Z₂ * hZ₁
                  exact mul_ne_zero hW₂ hZ₃ h1
              · have hW₂ : W₂ = 0 := by
                  rcases mul_eq_zero.mp hWZ' with h | h
                  · exact h
                  · exact False.elim (hZ₁ h)
                obtain ⟨hW₁, hW₃⟩ := hW₂_imp hW₂
                have h1 : W₃ * Z₁ = 0 := by
                  linear_combination hc1_2 - x * W₁ * hW₂
                exact mul_ne_zero hW₃ hZ₁ h1
            have hxy3 : q₁ * (-x) ^ 2 + p₂ * (-y) ^ 2 = 1 := by linear_combination hxy
            exact quat_norm_sol q₂ p₁
              (W₂ * Z₁ + q₂ * (-y) * Z₂ * Z₃ + p₁ * (-x) * W₁ * W₃)
              (W₂ * Z₃ + (-y) * Z₁ * Z₂)
              (W₃ * Z₁ + (-x) * W₁ * W₂)
              (W₁ * (-y) * Z₃ - (-x) * W₃ * Z₂)
              hq₂ hp₁ h_c3 (h_quat_id (-x) (-y) hxy3)
  have h_iff : (∃ x y : F, Q₁ * x ^ 2 + P₂ * y ^ 2 = 1) ↔
      (∃ u w : F, Q₂ * u ^ 2 + P₁ * w ^ 2 = 1) := by
    constructor
    · exact descent_sol_imp Q₁ Q₂ P₁ P₂ hQ₁ hQ₂ hP₁ hP₂ hq hp
    · intro ⟨u, w, huw⟩
      have hwu : P₁ * w ^ 2 + Q₂ * u ^ 2 = 1 := by linear_combination huw
      obtain ⟨y, x, hyx⟩ := descent_sol_imp P₁ P₂ Q₁ Q₂ hP₁ hP₂ hQ₁ hQ₂ hp hq ⟨w, u, hwu⟩
      exact ⟨x, y, by linear_combination hyx⟩
  classical
  simp only [hilbFin, hilbLoc]
  change (if (∃ x y : F, Q₁ * x ^ 2 + P₂ * y ^ 2 = 1) then (1 : ℤˣ) else -1) *
    (if (∃ x y : F, Q₂ * x ^ 2 + P₁ * y ^ 2 = 1) then (1 : ℤˣ) else -1) = 1
  rw [h_iff]
  split_ifs <;> rfl

theorem selmerStructRelax_mul_mem {K : Type u} [Field K] [NumberField K]
    (a₁ a₂ a₃ : K) (h₁₂ : a₁ ≠ a₂) (h₁₃ : a₁ ≠ a₃) (h₂₃ : a₂ ≠ a₃)
    (hint₁ : IsIntegral ℤ a₁) (hint₂ : IsIntegral ℤ a₂) (hint₃ : IsIntegral ℤ a₃)
    (T S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hT : IsGoodT a₁ a₂ a₃ T) (hSdisj : Disjoint S T)
    (π : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        v.adicCompletion K)
    (hπ : ∀ v ∈ S, IsLocalUnif v (π v))
    (v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (sqCl (1 : Kˣ), sqCl (1 : Kˣ)) ∈ selmerStructRelax K a₁ a₂ a₃ T S π v₀ ∧
    (∀ p q : Kˣ × Kˣ,
      (sqCl p.1, sqCl p.2) ∈ selmerStructRelax K a₁ a₂ a₃ T S π v₀ →
      (sqCl q.1, sqCl q.2) ∈ selmerStructRelax K a₁ a₂ a₃ T S π v₀ →
      (sqCl (p.1 * q.1), sqCl (p.2 * q.2)) ∈ selmerStructRelax K a₁ a₂ a₃ T S π v₀) :=
by
  have isSquare_mul_scale : ∀ {F : Type u} [Field F] {A B C X Y : F} (s : F),
      s ≠ 0 → A * B = C * s ^ 2 → IsSquare (A * X) → IsSquare (B * Y) →
      IsSquare (C * (X * Y)) := by
    intro F _ A B C X Y s hs hrel ⟨r₁, hr₁⟩ ⟨r₂, hr₂⟩
    refine ⟨r₁ * r₂ / s, ?_⟩
    have h1 : A * X = r₁ ^ 2 := by linear_combination hr₁
    have h2 : B * Y = r₂ ^ 2 := by linear_combination hr₂
    have h3 : C * (X * Y) * s ^ 2 = (r₁ * r₂) ^ 2 := by
      linear_combination -X * Y * hrel + B * Y * h1 + r₁ ^ 2 * h2
    calc C * (X * Y) = C * (X * Y) * s ^ 2 / s ^ 2 := by field_simp [hs]
      _ = (r₁ * r₂) ^ 2 / s ^ 2 := by rw [h3]
      _ = (r₁ * r₂ / s) * (r₁ * r₂ / s) := by ring
  have isSquare_scale_iff : ∀ {F : Type u} [Field F] (u s : F), s ≠ 0 →
      (IsSquare (u * s ^ 2) ↔ IsSquare u) := by
    intro F _ u s hs
    constructor
    · rintro ⟨r, hr⟩
      refine ⟨r / s, ?_⟩
      have h1 : u * s ^ 2 = r ^ 2 := by linear_combination hr
      calc u = u * s ^ 2 / s ^ 2 := by field_simp [hs]
        _ = r ^ 2 / s ^ 2 := by rw [h1]
        _ = (r / s) * (r / s) := by ring
    · rintro ⟨r, rfl⟩
      exact ⟨r * s, by ring⟩
  have ramLocal_mul_aux : ∀ {F : Type u} [Field F] (α β γ πv P₁ P₂ Q₁ Q₂ : F),
      α ≠ 0 → β ≠ 0 → γ ≠ 0 → πv ≠ 0 →
      ((IsSquare P₁ ∧ IsSquare P₂) ∨
       (IsSquare (P₁ * α * β) ∧ IsSquare (πv * (P₂ * α))) ∨
       (IsSquare (-(πv * (P₁ * α))) ∧ IsSquare (-(P₂ * α * γ))) ∨
       (IsSquare (-(πv * (P₁ * β))) ∧ IsSquare (-(πv * (P₂ * γ))))) →
      ((IsSquare Q₁ ∧ IsSquare Q₂) ∨
       (IsSquare (Q₁ * α * β) ∧ IsSquare (πv * (Q₂ * α))) ∨
       (IsSquare (-(πv * (Q₁ * α))) ∧ IsSquare (-(Q₂ * α * γ))) ∨
       (IsSquare (-(πv * (Q₁ * β))) ∧ IsSquare (-(πv * (Q₂ * γ))))) →
      ((IsSquare (P₁ * Q₁) ∧ IsSquare (P₂ * Q₂)) ∨
       (IsSquare ((P₁ * Q₁) * α * β) ∧ IsSquare (πv * ((P₂ * Q₂) * α))) ∨
       (IsSquare (-(πv * ((P₁ * Q₁) * α))) ∧ IsSquare (-((P₂ * Q₂) * α * γ))) ∨
       (IsSquare (-(πv * ((P₁ * Q₁) * β))) ∧ IsSquare (-(πv * ((P₂ * Q₂) * γ))))) := by
    intro F _ α β γ πv P₁ P₂ Q₁ Q₂ hα hβ hγ hπ_ne hp hq
    let c₁ (b₁ b₂ : Bool) : F := (if b₁ then α * β else 1) * (if b₂ then -(πv * α) else 1)
    let c₂ (b₁ b₂ : Bool) : F := (if b₁ then πv * α else 1) * (if b₂ then -(α * γ) else 1)
    have hiff : ∀ X₁ X₂ : F,
        ((IsSquare X₁ ∧ IsSquare X₂) ∨
         (IsSquare (X₁ * α * β) ∧ IsSquare (πv * (X₂ * α))) ∨
         (IsSquare (-(πv * (X₁ * α))) ∧ IsSquare (-(X₂ * α * γ))) ∨
         (IsSquare (-(πv * (X₁ * β))) ∧ IsSquare (-(πv * (X₂ * γ))))) ↔
        ∃ b₁ b₂ : Bool, IsSquare (c₁ b₁ b₂ * X₁) ∧ IsSquare (c₂ b₁ b₂ * X₂) := by
      intro X₁ X₂
      have eq0_1 : X₁ = c₁ false false * X₁ := by dsimp [c₁]; ring
      have eq0_2 : X₂ = c₂ false false * X₂ := by dsimp [c₂]; ring
      have eq1_1 : X₁ * α * β = c₁ true false * X₁ := by dsimp [c₁]; ring
      have eq1_2 : πv * (X₂ * α) = c₂ true false * X₂ := by dsimp [c₂]; ring
      have eq2_1 : -(πv * (X₁ * α)) = c₁ false true * X₁ := by dsimp [c₁]; ring
      have eq2_2 : -(X₂ * α * γ) = c₂ false true * X₂ := by dsimp [c₂]; ring
      have eq3_1 : c₁ true true * X₁ = -(πv * (X₁ * β)) * α ^ 2 := by dsimp [c₁]; ring
      have eq3_2 : c₂ true true * X₂ = -(πv * (X₂ * γ)) * α ^ 2 := by dsimp [c₂]; ring
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨false, false, by rwa [← eq0_1], by rwa [← eq0_2]⟩
        · exact ⟨true, false, by rwa [← eq1_1], by rwa [← eq1_2]⟩
        · exact ⟨false, true, by rwa [← eq2_1], by rwa [← eq2_2]⟩
        · refine ⟨true, true, ?_, ?_⟩
          · rw [eq3_1, isSquare_scale_iff _ α hα]; exact h1
          · rw [eq3_2, isSquare_scale_iff _ α hα]; exact h2
      · rintro ⟨b₁, b₂, h1, h2⟩
        cases b₁ <;> cases b₂
        · left; exact ⟨by rwa [eq0_1], by rwa [eq0_2]⟩
        · right; right; left; exact ⟨by rwa [eq2_1], by rwa [eq2_2]⟩
        · right; left; exact ⟨by rwa [eq1_1], by rwa [eq1_2]⟩
        · right; right; right
          rw [eq3_1, isSquare_scale_iff _ α hα] at h1
          rw [eq3_2, isSquare_scale_iff _ α hα] at h2
          exact ⟨h1, h2⟩
    obtain ⟨b₁, b₂, hp1, hp2⟩ := (hiff P₁ P₂).mp hp
    obtain ⟨b₁', b₂', hq1, hq2⟩ := (hiff Q₁ Q₂).mp hq
    rw [hiff]
    refine ⟨xor b₁ b₁', xor b₂ b₂', ?_, ?_⟩
    · let s₁ : F := (if b₁ && b₁' then α * β else 1) * (if b₂ && b₂' then -(πv * α) else 1)
      have hs₁ : s₁ ≠ 0 := by
        apply mul_ne_zero
        · split_ifs; exact mul_ne_zero hα hβ; exact one_ne_zero
        · split_ifs; exact neg_ne_zero.mpr (mul_ne_zero hπ_ne hα); exact one_ne_zero
      have hrel₁ : c₁ b₁ b₂ * c₁ b₁' b₂' = c₁ (xor b₁ b₁') (xor b₂ b₂') * s₁ ^ 2 := by
        cases b₁ <;> cases b₂ <;> cases b₁' <;> cases b₂' <;> dsimp [c₁, s₁] <;> ring
      exact isSquare_mul_scale s₁ hs₁ hrel₁ hp1 hq1
    · let s₂ : F := (if b₁ && b₁' then πv * α else 1) * (if b₂ && b₂' then -(α * γ) else 1)
      have hs₂ : s₂ ≠ 0 := by
        apply mul_ne_zero
        · split_ifs; exact mul_ne_zero hπ_ne hα; exact one_ne_zero
        · split_ifs; exact neg_ne_zero.mpr (mul_ne_zero hα hγ); exact one_ne_zero
      have hrel₂ : c₂ b₁ b₂ * c₂ b₁' b₂' = c₂ (xor b₁ b₁') (xor b₂ b₂') * s₂ ^ 2 := by
        cases b₁ <;> cases b₂ <;> cases b₁' <;> cases b₂' <;> dsimp [c₂, s₂] <;> ring
      exact isSquare_mul_scale s₂ hs₂ hrel₂ hp2 hq2
  have ramLocal_mul : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
      (πv : v.adicCompletion K), IsLocalUnif v πv →
      ∀ (p₁ p₂ q₁ q₂ : Kˣ),
      RamLocal a₁ a₂ a₃ v πv p₁ p₂ →
      RamLocal a₁ a₂ a₃ v πv q₁ q₂ →
      RamLocal a₁ a₂ a₃ v πv (p₁ * q₁) (p₂ * q₂) := by
    intro v πv hπv p₁ p₂ q₁ q₂ hp hq
    have hα : algebraMap K (v.adicCompletion K) (a₁ - a₂) ≠ 0 := by
      rw [ne_eq, map_eq_zero, sub_eq_zero]; exact h₁₂
    have hβ : algebraMap K (v.adicCompletion K) (a₁ - a₃) ≠ 0 := by
      rw [ne_eq, map_eq_zero, sub_eq_zero]; exact h₁₃
    have hγ : algebraMap K (v.adicCompletion K) (a₂ - a₃) ≠ 0 := by
      rw [ne_eq, map_eq_zero, sub_eq_zero]; exact h₂₃
    have hπ_ne : πv ≠ 0 := by
      rcases hπv with ⟨n, _, hn⟩
      intro h0
      rw [h0, map_zero] at hn
      exact WithZero.coe_ne_zero hn.symm
    unfold RamLocal at hp hq ⊢
    simp only [Units.val_mul, map_mul, map_neg] at hp hq ⊢
    exact ramLocal_mul_aux
      (algebraMap K (v.adicCompletion K) (a₁ - a₂))
      (algebraMap K (v.adicCompletion K) (a₁ - a₃))
      (algebraMap K (v.adicCompletion K) (a₂ - a₃))
      πv
      (algebraMap K (v.adicCompletion K) (p₁ : K))
      (algebraMap K (v.adicCompletion K) (p₂ : K))
      (algebraMap K (v.adicCompletion K) (q₁ : K))
      (algebraMap K (v.adicCompletion K) (q₂ : K))
      hα hβ hγ hπ_ne hp hq
  have isDescentClass_of_isSquare : ∀ {F : Type u} [Field F] (e₁ e₂ e₃ d₁ d₂ : F),
      IsSquare d₁ → IsSquare d₂ → IsDescentClass e₁ e₂ e₃ d₁ d₂ := by
    rintro F _ e₁ e₂ e₃ d₁ d₂ ⟨s₁, rfl⟩ ⟨s₂, rfl⟩
    refine ⟨0, s₂, s₁, 1, ?_, by ring, by ring⟩
    intro h
    exact one_ne_zero h.2.2.2
  have isSquare_of_z0_eq_zero : ∀ {F : Type u} [Field F] {e₁ e₂ e₃ d₁ d₂ z₁ z₂ z₃ : F},
      d₁ ≠ 0 → d₂ ≠ 0 →
      ¬ ((0 : F) = 0 ∧ z₁ = 0 ∧ z₂ = 0 ∧ z₃ = 0) →
      d₁ * z₁ ^ 2 - d₂ * z₂ ^ 2 = (e₂ - e₁) * 0 ^ 2 →
      d₁ * z₁ ^ 2 - d₁ * d₂ * z₃ ^ 2 = (e₃ - e₁) * 0 ^ 2 →
      IsSquare d₁ ∧ IsSquare d₂ := by
    intro F _ e₁ e₂ e₃ d₁ d₂ z₁ z₂ z₃ hd₁ hd₂ hne hz1 hz2
    have hz3 : z₃ ≠ 0 := by
      intro h3
      have h1 : d₁ * z₁ ^ 2 = 0 := by linear_combination hz2 + d₁ * d₂ * z₃ * h3
      have h2 : d₂ * z₂ ^ 2 = 0 := by linear_combination h1 - hz1
      have hz1_0 : z₁ = 0 := by
        cases mul_eq_zero.mp h1 with
        | inl h => exact absurd h hd₁
        | inr h => exact pow_eq_zero h
      have hz2_0 : z₂ = 0 := by
        cases mul_eq_zero.mp h2 with
        | inl h => exact absurd h hd₂
        | inr h => exact pow_eq_zero h
      exact hne ⟨rfl, hz1_0, hz2_0, h3⟩
    have hd1_eq : d₂ * (d₁ * z₃ ^ 2 - z₂ ^ 2) = 0 := by linear_combination hz1 - hz2
    have hd1_sq : d₁ * z₃ ^ 2 = z₂ ^ 2 := by
      cases mul_eq_zero.mp hd1_eq with
      | inl h => exact absurd h hd₂
      | inr h => linear_combination h
    have hd2_eq : d₁ * (d₂ * z₃ ^ 2 - z₁ ^ 2) = 0 := by linear_combination -hz2
    have hd2_sq : d₂ * z₃ ^ 2 = z₁ ^ 2 := by
      cases mul_eq_zero.mp hd2_eq with
      | inl h => exact absurd h hd₁
      | inr h => linear_combination h
    constructor
    · refine ⟨z₂ / z₃, ?_⟩
      calc d₁ = d₁ * z₃ ^ 2 / z₃ ^ 2 := by field_simp [hz3]
        _ = z₂ ^ 2 / z₃ ^ 2 := by rw [hd1_sq]
        _ = (z₂ / z₃) * (z₂ / z₃) := by ring
    · refine ⟨z₁ / z₃, ?_⟩
      calc d₂ = d₂ * z₃ ^ 2 / z₃ ^ 2 := by field_simp [hz3]
        _ = z₁ ^ 2 / z₃ ^ 2 := by rw [hd2_sq]
        _ = (z₁ / z₃) * (z₁ / z₃) := by ring
  have isDescentClass_mul_of_isSquare_left : ∀ {F : Type u} [Field F] (e₁ e₂ e₃ d₁ d₂ c₁ c₂ : F),
      d₁ ≠ 0 → d₂ ≠ 0 → IsSquare d₁ → IsSquare d₂ →
      IsDescentClass e₁ e₂ e₃ c₁ c₂ →
      IsDescentClass e₁ e₂ e₃ (d₁ * c₁) (d₂ * c₂) := by
    rintro F _ e₁ e₂ e₃ d₁ d₂ c₁ c₂ hd₁ hd₂ ⟨s₁, rfl⟩ ⟨s₂, rfl⟩ ⟨w₀, w₁, w₂, w₃, hw_ne, hw1, hw2⟩
    have hs₁ : s₁ ≠ 0 := fun h => hd₁ (by simp [h])
    have hs₂ : s₂ ≠ 0 := fun h => hd₂ (by simp [h])
    refine ⟨w₀, w₁ / s₁, w₂ / s₂, w₃ / (s₁ * s₂), ?_, ?_, ?_⟩
    · intro ⟨h0, h1, h2, h3⟩
      apply hw_ne
      refine ⟨h0, ?_, ?_, ?_⟩
      · exact (div_eq_zero_iff.mp h1).resolve_right hs₁
      · exact (div_eq_zero_iff.mp h2).resolve_right hs₂
      · exact (div_eq_zero_iff.mp h3).resolve_right (mul_ne_zero hs₁ hs₂)
    · have h1 : s₁ * s₁ * c₁ * (w₁ / s₁) ^ 2 = c₁ * w₁ ^ 2 := by field_simp [hs₁]
      have h2 : s₂ * s₂ * c₂ * (w₂ / s₂) ^ 2 = c₂ * w₂ ^ 2 := by field_simp [hs₂]
      linear_combination h1 - h2 + hw1
    · have h1 : s₁ * s₁ * c₁ * (w₁ / s₁) ^ 2 = c₁ * w₁ ^ 2 := by field_simp [hs₁]
      have h3 : s₁ * s₁ * c₁ * (s₂ * s₂ * c₂) * (w₃ / (s₁ * s₂)) ^ 2 = c₁ * c₂ * w₃ ^ 2 := by
        field_simp [hs₁, hs₂]
      linear_combination h1 - h3 + hw2
  have isDescentClass_mul : ∀ {F : Type u} [Field F] (e₁ e₂ e₃ : F),
      e₁ ≠ e₂ → e₁ ≠ e₃ → e₂ ≠ e₃ →
      ∀ (d₁ d₂ c₁ c₂ : F), d₁ ≠ 0 → d₂ ≠ 0 → c₁ ≠ 0 → c₂ ≠ 0 →
      IsDescentClass e₁ e₂ e₃ d₁ d₂ →
      IsDescentClass e₁ e₂ e₃ c₁ c₂ →
      IsDescentClass e₁ e₂ e₃ (d₁ * c₁) (d₂ * c₂) := by
    intro F _ e₁ e₂ e₃ he₁₂ he₁₃ he₂₃ d₁ d₂ c₁ c₂ hd₁ hd₂ hc₁ hc₂ hd hc
    rcases hd with ⟨z₀, z₁, z₂, z₃, hz_ne, hz1, hz2⟩
    by_cases hz0 : z₀ = 0
    · subst hz0
      obtain ⟨hsq1, hsq2⟩ := isSquare_of_z0_eq_zero hd₁ hd₂ hz_ne hz1 hz2
      exact isDescentClass_mul_of_isSquare_left e₁ e₂ e₃ d₁ d₂ c₁ c₂ hd₁ hd₂ hsq1 hsq2 hc
    rcases hc with ⟨w₀, w₁, w₂, w₃, hw_ne, hw1, hw2⟩
    by_cases hw0 : w₀ = 0
    · subst hw0
      obtain ⟨hsq1, hsq2⟩ := isSquare_of_z0_eq_zero hc₁ hc₂ hw_ne hw1 hw2
      rw [mul_comm d₁ c₁, mul_comm d₂ c₂]
      exact isDescentClass_mul_of_isSquare_left e₁ e₂ e₃ c₁ c₂ d₁ d₂ hc₁ hc₂ hsq1 hsq2
        ⟨z₀, z₁, z₂, z₃, hz_ne, hz1, hz2⟩
    let u₀ : F := d₁ * z₁ ^ 2 * w₀ ^ 2 - c₁ * w₁ ^ 2 * z₀ ^ 2
    let u₁ : F := d₂ * z₂ * z₃ * w₁ * w₀ - c₂ * w₂ * w₃ * z₁ * z₀
    let u₂ : F := d₁ * z₁ * z₃ * w₂ * w₀ - c₁ * w₁ * w₃ * z₂ * z₀
    let u₃ : F := z₁ * z₂ * w₃ * w₀ - w₁ * w₂ * z₃ * z₀
    have hA2 : d₂ * z₂ ^ 2 * w₀ ^ 2 - c₂ * w₂ ^ 2 * z₀ ^ 2 = u₀ := by
      dsimp [u₀]; linear_combination -w₀ ^ 2 * hz1 + z₀ ^ 2 * hw1
    have hA3 : d₁ * d₂ * z₃ ^ 2 * w₀ ^ 2 - c₁ * c₂ * w₃ ^ 2 * z₀ ^ 2 = u₀ := by
      dsimp [u₀]; linear_combination -w₀ ^ 2 * hz2 + z₀ ^ 2 * hw2
    have hB2 : d₂ * z₂ ^ 2 * (c₁ * w₁ ^ 2) - d₁ * z₁ ^ 2 * (c₂ * w₂ ^ 2) = (e₂ - e₁) * u₀ := by
      dsimp [u₀]; linear_combination -c₁ * w₁ ^ 2 * hz1 + d₁ * z₁ ^ 2 * hw1
    have hB3 : d₁ * d₂ * z₃ ^ 2 * (c₁ * w₁ ^ 2) - d₁ * z₁ ^ 2 * (c₁ * c₂ * w₃ ^ 2) = (e₃ - e₁) * u₀ := by
      dsimp [u₀]; linear_combination -c₁ * w₁ ^ 2 * hz2 + d₁ * z₁ ^ 2 * hw2
    by_cases hu0 : u₀ ≠ 0
    · refine ⟨u₀, u₁, u₂, u₃, fun h => hu0 h.1, ?_, ?_⟩
      · calc (d₁ * c₁) * u₁ ^ 2 - (d₂ * c₂) * u₂ ^ 2
          _ = (d₁ * d₂ * z₃ ^ 2 * w₀ ^ 2 - c₁ * c₂ * w₃ ^ 2 * z₀ ^ 2) *
              (d₂ * z₂ ^ 2 * (c₁ * w₁ ^ 2) - d₁ * z₁ ^ 2 * (c₂ * w₂ ^ 2)) := by
            dsimp [u₁, u₂]; ring
          _ = u₀ * ((e₂ - e₁) * u₀) := by rw [hA3, hB2]
          _ = (e₂ - e₁) * u₀ ^ 2 := by ring
      · calc (d₁ * c₁) * u₁ ^ 2 - (d₁ * c₁) * (d₂ * c₂) * u₃ ^ 2
          _ = (d₂ * z₂ ^ 2 * w₀ ^ 2 - c₂ * w₂ ^ 2 * z₀ ^ 2) *
              (d₁ * d₂ * z₃ ^ 2 * (c₁ * w₁ ^ 2) - d₁ * z₁ ^ 2 * (c₁ * c₂ * w₃ ^ 2)) := by
            dsimp [u₁, u₃]; ring
          _ = u₀ * ((e₃ - e₁) * u₀) := by rw [hA2, hB3]
          _ = (e₃ - e₁) * u₀ ^ 2 := by ring
    · push_neg at hu0
      have hsq_from_eq : ∀ (D C Z W : F), Z ≠ 0 → D * Z ^ 2 * w₀ ^ 2 - C * W ^ 2 * z₀ ^ 2 = 0 →
          IsSquare (D * C) := by
        intro D C Z W hZ heq
        have hZW : Z * w₀ ≠ 0 := mul_ne_zero hZ hw0
        have h1 : D * C * (Z * w₀) ^ 2 = (C * W * z₀) ^ 2 := by
          linear_combination C * heq
        refine ⟨C * W * z₀ / (Z * w₀), ?_⟩
        calc D * C = D * C * (Z * w₀) ^ 2 / (Z * w₀) ^ 2 := by field_simp [hZW]
          _ = (C * W * z₀) ^ 2 / (Z * w₀) ^ 2 := by rw [h1]
          _ = (C * W * z₀ / (Z * w₀)) * (C * W * z₀ / (Z * w₀)) := by ring
      have h1_eq : d₁ * z₁ ^ 2 * w₀ ^ 2 - c₁ * w₁ ^ 2 * z₀ ^ 2 = 0 := hu0
      have h2_eq : d₂ * z₂ ^ 2 * w₀ ^ 2 - c₂ * w₂ ^ 2 * z₀ ^ 2 = 0 := by rw [hA2, hu0]
      have h3_eq : (d₁ * d₂) * z₃ ^ 2 * w₀ ^ 2 - (c₁ * c₂) * w₃ ^ 2 * z₀ ^ 2 = 0 := by
        rw [hA3, hu0]
      have h_not_z12 : ¬ (z₁ = 0 ∧ z₂ = 0) := by
        rintro ⟨h1, h2⟩
        have he : (e₂ - e₁) * z₀ ^ 2 = 0 := by linear_combination -hz1 + d₁ * z₁ * h1 - d₂ * z₂ * h2
        exact mul_ne_zero (sub_ne_zero.mpr he₁₂.symm) (pow_ne_zero 2 hz0) he
      have h_not_z13 : ¬ (z₁ = 0 ∧ z₃ = 0) := by
        rintro ⟨h1, h3⟩
        have he : (e₃ - e₁) * z₀ ^ 2 = 0 := by linear_combination -hz2 + d₁ * z₁ * h1 - d₁ * d₂ * z₃ * h3
        exact mul_ne_zero (sub_ne_zero.mpr he₁₃.symm) (pow_ne_zero 2 hz0) he
      have h_not_z23 : ¬ (z₂ = 0 ∧ z₃ = 0) := by
        rintro ⟨h2, h3⟩
        have he : (e₃ - e₂) * z₀ ^ 2 = 0 := by linear_combination hz1 - hz2 + d₂ * z₂ * h2 - d₁ * d₂ * z₃ * h3
        exact mul_ne_zero (sub_ne_zero.mpr he₂₃.symm) (pow_ne_zero 2 hz0) he
      have hsq_div : ∀ (A B : F), A ≠ 0 → IsSquare A → IsSquare (A * B) → IsSquare B := by
        rintro A B hA ⟨r₁, rfl⟩ ⟨r₂, hr₂⟩
        have hr₁ : r₁ ≠ 0 := fun h => hA (by simp [h])
        refine ⟨r₂ / r₁, ?_⟩
        have h1 : r₁ ^ 2 * B = r₂ ^ 2 := by linear_combination hr₂
        calc B = r₁ ^ 2 * B / r₁ ^ 2 := by field_simp [hr₁]
          _ = r₂ ^ 2 / r₁ ^ 2 := by rw [h1]
          _ = (r₂ / r₁) * (r₂ / r₁) := by ring
      by_cases hz1_ne : z₁ ≠ 0
      · have hsq1 : IsSquare (d₁ * c₁) := hsq_from_eq d₁ c₁ z₁ w₁ hz1_ne h1_eq
        by_cases hz2_ne : z₂ ≠ 0
        · have hsq2 : IsSquare (d₂ * c₂) := hsq_from_eq d₂ c₂ z₂ w₂ hz2_ne h2_eq
          exact isDescentClass_of_isSquare e₁ e₂ e₃ (d₁ * c₁) (d₂ * c₂) hsq1 hsq2
        · push_neg at hz2_ne
          have hz3_ne : z₃ ≠ 0 := fun h3 => h_not_z23 ⟨hz2_ne, h3⟩
          have hsq3 : IsSquare ((d₁ * d₂) * (c₁ * c₂)) := hsq_from_eq (d₁ * d₂) (c₁ * c₂) z₃ w₃ hz3_ne h3_eq
          have hsq3' : IsSquare ((d₁ * c₁) * (d₂ * c₂)) := by
            convert hsq3 using 1; ring
          have hsq2 : IsSquare (d₂ * c₂) := hsq_div (d₁ * c₁) (d₂ * c₂) (mul_ne_zero hd₁ hc₁) hsq1 hsq3'
          exact isDescentClass_of_isSquare e₁ e₂ e₃ (d₁ * c₁) (d₂ * c₂) hsq1 hsq2
      · push_neg at hz1_ne
        have hz2_ne : z₂ ≠ 0 := fun h2 => h_not_z12 ⟨hz1_ne, h2⟩
        have hz3_ne : z₃ ≠ 0 := fun h3 => h_not_z13 ⟨hz1_ne, h3⟩
        have hsq2 : IsSquare (d₂ * c₂) := hsq_from_eq d₂ c₂ z₂ w₂ hz2_ne h2_eq
        have hsq3 : IsSquare ((d₁ * d₂) * (c₁ * c₂)) := hsq_from_eq (d₁ * d₂) (c₁ * c₂) z₃ w₃ hz3_ne h3_eq
        have hsq3' : IsSquare ((d₂ * c₂) * (d₁ * c₁)) := by
          convert hsq3 using 1; ring
        have hsq1 : IsSquare (d₁ * c₁) := hsq_div (d₂ * c₂) (d₁ * c₁) (mul_ne_zero hd₂ hc₂) hsq2 hsq3'
        exact isDescentClass_of_isSquare e₁ e₂ e₃ (d₁ * c₁) (d₂ * c₂) hsq1 hsq2
  constructor
  · refine ⟨((1 : Kˣ), (1 : Kˣ)), ⟨?_, ?_, ?_, ?_⟩, rfl⟩
    · intro v _
      exact isDescentClass_of_isSquare _ _ _ _ _
        (by simp only [Units.val_one, map_one]; exact IsSquare.one)
        (by simp only [Units.val_one, map_one]; exact IsSquare.one)
    · intro w
      exact isDescentClass_of_isSquare _ _ _ _ _
        (by simp only [Units.val_one, map_one]; exact IsSquare.one)
        (by simp only [Units.val_one, map_one]; exact IsSquare.one)
    · intro v _
      left
      exact ⟨by simp only [Units.val_one, map_one]; exact IsSquare.one,
             by simp only [Units.val_one, map_one]; exact IsSquare.one⟩
    · intro v _ _ _
      refine ⟨?_, ?_⟩ <;>
      · unfold EvenVal
        rw [map_one, toAdd_one]
        exact Even.zero
  · intro p q hp hq
    rcases hp with ⟨p', ⟨hp'T, hp'Inf, hp'S, hp'U⟩, hp'eq⟩
    rcases hq with ⟨q', ⟨hq'T, hq'Inf, hq'S, hq'U⟩, hq'eq⟩
    injection hp'eq with hp'1 hp'2
    injection hq'eq with hq'1 hq'2
    refine ⟨(p'.1 * q'.1, p'.2 * q'.2), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro v hvT
      simp only [Units.val_mul, map_mul]
      exact isDescentClass_mul
        (algebraMap K (v.adicCompletion K) a₁)
        (algebraMap K (v.adicCompletion K) a₂)
        (algebraMap K (v.adicCompletion K) a₃)
        ((algebraMap K (v.adicCompletion K)).injective.ne h₁₂)
        ((algebraMap K (v.adicCompletion K)).injective.ne h₁₃)
        ((algebraMap K (v.adicCompletion K)).injective.ne h₂₃)
        (algebraMap K (v.adicCompletion K) (p'.1 : K))
        (algebraMap K (v.adicCompletion K) (p'.2 : K))
        (algebraMap K (v.adicCompletion K) (q'.1 : K))
        (algebraMap K (v.adicCompletion K) (q'.2 : K))
        (by rw [ne_eq, map_eq_zero]; exact p'.1.ne_zero)
        (by rw [ne_eq, map_eq_zero]; exact p'.2.ne_zero)
        (by rw [ne_eq, map_eq_zero]; exact q'.1.ne_zero)
        (by rw [ne_eq, map_eq_zero]; exact q'.2.ne_zero)
        (hp'T v hvT) (hq'T v hvT)
    · intro w
      simp only [Units.val_mul, map_mul]
      exact isDescentClass_mul
        (algebraMap K w.Completion a₁)
        (algebraMap K w.Completion a₂)
        (algebraMap K w.Completion a₃)
        ((algebraMap K w.Completion).injective.ne h₁₂)
        ((algebraMap K w.Completion).injective.ne h₁₃)
        ((algebraMap K w.Completion).injective.ne h₂₃)
        (algebraMap K w.Completion (p'.1 : K))
        (algebraMap K w.Completion (p'.2 : K))
        (algebraMap K w.Completion (q'.1 : K))
        (algebraMap K w.Completion (q'.2 : K))
        (by rw [ne_eq, map_eq_zero]; exact p'.1.ne_zero)
        (by rw [ne_eq, map_eq_zero]; exact p'.2.ne_zero)
        (by rw [ne_eq, map_eq_zero]; exact q'.1.ne_zero)
        (by rw [ne_eq, map_eq_zero]; exact q'.2.ne_zero)
        (hp'Inf w) (hq'Inf w)
    · intro v hvS
      exact ramLocal_mul v (π v) (hπ v hvS) p'.1 p'.2 q'.1 q'.2 (hp'S v hvS) (hq'S v hvS)
    · intro v hvT hvS hv₀
      have hpU := hp'U v hvT hvS hv₀
      have hqU := hq'U v hvT hvS hv₀
      refine ⟨?_, ?_⟩
      · unfold EvenVal
        rw [map_mul, toAdd_mul]
        exact hpU.1.add hqU.1
      · unfold EvenVal
        rw [map_mul, toAdd_mul]
        exact hpU.2.add hqU.2
    · unfold sqCl at *
      ext <;> simp only [QuotientGroup.mk_mul, hp'1, hp'2, hq'1, hq'2]

theorem isSquare_of_hilbLoc_orth_of_independent {K : Type u} [Field K] [NumberField K]
    (a₁ a₂ a₃ : K) (h₁₂ : a₁ ≠ a₂) (h₁₃ : a₁ ≠ a₃) (h₂₃ : a₂ ≠ a₃)
    (hint₁ : IsIntegral ℤ a₁) (hint₂ : IsIntegral ℤ a₂) (hint₃ : IsIntegral ℤ a₃)
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hT : IsGoodT a₁ a₂ a₃ T)
    (v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hv₀T : v₀ ∉ T) (g₁ g₂ h₁ h₂ d₁ d₂ : v₀.adicCompletion K)
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (hh₁ : h₁ ≠ 0) (hh₂ : h₂ ≠ 0)
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0)
    (hg_nsq : ¬ (IsSquare g₁ ∧ IsSquare g₂))
    (hh_nsq : ¬ (IsSquare h₁ ∧ IsSquare h₂))
    (hgh_nsq : ¬ (IsSquare (g₁ * h₁) ∧ IsSquare (g₂ * h₂)))
    (hgh_orth : hilbLoc v₀ g₁ h₂ * hilbLoc v₀ g₂ h₁ = 1)
    (hdg_orth : hilbLoc v₀ d₁ g₂ * hilbLoc v₀ d₂ g₁ = 1)
    (hdh_orth : hilbLoc v₀ d₁ h₂ * hilbLoc v₀ d₂ h₁ = 1) :
    (IsSquare d₁ ∧ IsSquare d₂) ∨
    (IsSquare (d₁ * g₁) ∧ IsSquare (d₂ * g₂)) ∨
    (IsSquare (d₁ * h₁) ∧ IsSquare (d₂ * h₂)) ∨
    (IsSquare (d₁ * (g₁ * h₁)) ∧ IsSquare (d₂ * (g₂ * h₂))) :=
by
  let hilbBool (e ax bx ay by_ : Bool) : Bool :=
    xor (xor (ax && by_) (bx && ay)) (e && bx && by_)
  have sign_mul_eq_one_iff : ∀ (b₁ b₂ : Bool),
      ((if b₁ then (-1 : ℤˣ) else 1) * (if b₂ then (-1 : ℤˣ) else 1) = 1) ↔
      xor b₁ b₂ = false := by
    decide
  have and4_eq_false : ∀ (a1 b1 a2 b2 : Bool),
      ((a1 = false ∧ b1 = false) ∧ (a2 = false ∧ b2 = false)) ↔
      (a1 || b1 || a2 || b2) = false := by
    decide
  have h_imp_bridge : ∀ (p1 p2 p3 o1 o2 o3 q1 q2 q3 q4 : Bool),
      ((!p1 || !p2 || !p3 || o1 || o2 || o3) || (!q1 || !q2 || !q3 || !q4)) = true →
      ¬ (p1 = false) → ¬ (p2 = false) → ¬ (p3 = false) →
      o1 = false → o2 = false → o3 = false →
      q1 = false ∨ q2 = false ∨ q3 = false ∨ q4 = false := by
    decide
  have h_bool_core : ∀ (ε ag1 bg1 ag2 bg2 ah1 bh1 ah2 bh2 ad1 bd1 ad2 bd2 : Bool),
      ((!(ag1 || bg1 || ag2 || bg2) ||
        !(ah1 || bh1 || ah2 || bh2) ||
        !((xor ag1 ah1) || (xor bg1 bh1) || (xor ag2 ah2) || (xor bg2 bh2)) ||
        xor (hilbBool ε ag1 bg1 ah2 bh2) (hilbBool ε ag2 bg2 ah1 bh1) ||
        xor (hilbBool ε ad1 bd1 ag2 bg2) (hilbBool ε ad2 bd2 ag1 bg1) ||
        xor (hilbBool ε ad1 bd1 ah2 bh2) (hilbBool ε ad2 bd2 ah1 bh1)) ||
       (!(ad1 || bd1 || ad2 || bd2) ||
        !((xor ad1 ag1) || (xor bd1 bg1) || (xor ad2 ag2) || (xor bd2 bg2)) ||
        !((xor ad1 ah1) || (xor bd1 bh1) || (xor ad2 ah2) || (xor bd2 bh2)) ||
        !((xor ad1 (xor ag1 ah1)) || (xor bd1 (xor bg1 bh1)) ||
          (xor ad2 (xor ag2 ah2)) || (xor bd2 (xor bg2 bh2))))) = true := by
    decide
  have h_bool_main : ∀ (ε ag1 bg1 ag2 bg2 ah1 bh1 ah2 bh2 ad1 bd1 ad2 bd2 : Bool),
      ¬ ((ag1 = false ∧ bg1 = false) ∧ (ag2 = false ∧ bg2 = false)) →
      ¬ ((ah1 = false ∧ bh1 = false) ∧ (ah2 = false ∧ bh2 = false)) →
      ¬ ((xor ag1 ah1 = false ∧ xor bg1 bh1 = false) ∧
        (xor ag2 ah2 = false ∧ xor bg2 bh2 = false)) →
      (if hilbBool ε ag1 bg1 ah2 bh2 then (-1 : ℤˣ) else 1) *
        (if hilbBool ε ag2 bg2 ah1 bh1 then (-1 : ℤˣ) else 1) = 1 →
      (if hilbBool ε ad1 bd1 ag2 bg2 then (-1 : ℤˣ) else 1) *
        (if hilbBool ε ad2 bd2 ag1 bg1 then (-1 : ℤˣ) else 1) = 1 →
      (if hilbBool ε ad1 bd1 ah2 bh2 then (-1 : ℤˣ) else 1) *
        (if hilbBool ε ad2 bd2 ah1 bh1 then (-1 : ℤˣ) else 1) = 1 →
      ((ad1 = false ∧ bd1 = false) ∧ (ad2 = false ∧ bd2 = false)) ∨
      ((xor ad1 ag1 = false ∧ xor bd1 bg1 = false) ∧
        (xor ad2 ag2 = false ∧ xor bd2 bg2 = false)) ∨
      ((xor ad1 ah1 = false ∧ xor bd1 bh1 = false) ∧
        (xor ad2 ah2 = false ∧ xor bd2 bh2 = false)) ∨
      ((xor ad1 (xor ag1 ah1) = false ∧ xor bd1 (xor bg1 bh1) = false) ∧
        (xor ad2 (xor ag2 ah2) = false ∧ xor bd2 (xor bg2 bh2) = false)) := by
    intro ε ag1 bg1 ag2 bg2 ah1 bh1 ah2 bh2 ad1 bd1 ad2 bd2 h1 h2 h3 o1 o2 o3
    rw [and4_eq_false] at h1 h2 h3
    rw [sign_mul_eq_one_iff] at o1 o2 o3
    rw [and4_eq_false, and4_eq_false, and4_eq_false, and4_eq_false]
    exact h_imp_bridge _ _ _ _ _ _ _ _ _ _
      (h_bool_core ε ag1 bg1 ag2 bg2 ah1 bh1 ah2 bh2 ad1 bd1 ad2 bd2)
      h1 h2 h3 o1 o2 o3
  classical
  have h2_val : IsDedekindDomain.HeightOneSpectrum.valuation K v₀ (2 : K) = 1 := by
    let A₁ : NumberField.RingOfIntegers K := ⟨a₁, hint₁⟩
    let A₂ : NumberField.RingOfIntegers K := ⟨a₂, hint₂⟩
    let A₃ : NumberField.RingOfIntegers K := ⟨a₃, hint₃⟩
    let W : NumberField.RingOfIntegers K := 3 * (A₁ - A₂) * (A₁ - A₃) * (A₂ - A₃)
    have h2_le : IsDedekindDomain.HeightOneSpectrum.valuation K v₀ (2 : K) ≤ 1 := by
      rw [← map_ofNat (algebraMap (NumberField.RingOfIntegers K) K) 2]
      exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one v₀ 2
    have hW_le : IsDedekindDomain.HeightOneSpectrum.valuation K v₀
        (algebraMap (NumberField.RingOfIntegers K) K W) ≤ 1 :=
      IsDedekindDomain.HeightOneSpectrum.valuation_le_one v₀ W
    have hprod_eq : 6 * (a₁ - a₂) * (a₁ - a₃) * (a₂ - a₃) =
        (2 : K) * algebraMap (NumberField.RingOfIntegers K) K W := by
      change 6 * (a₁ - a₂) * (a₁ - a₃) * (a₂ - a₃) =
        (2 : K) * algebraMap (NumberField.RingOfIntegers K) K
          (3 * (A₁ - A₂) * (A₁ - A₃) * (A₂ - A₃))
      simp only [map_mul, map_sub, map_ofNat]
      change 6 * (a₁ - a₂) * (a₁ - a₃) * (a₂ - a₃) =
        2 * (3 * (a₁ - a₂) * (a₁ - a₃) * (a₂ - a₃))
      ring
    have hv_prod : IsDedekindDomain.HeightOneSpectrum.valuation K v₀
        (6 * (a₁ - a₂) * (a₁ - a₃) * (a₂ - a₃)) = 1 := by
      have h := (hT v₀).not.mp hv₀T
      push_neg at h
      exact h
    rw [hprod_eq, Valuation.map_mul] at hv_prod
    refine le_antisymm h2_le ?_
    calc (1 : WithZero (Multiplicative ℤ))
        = IsDedekindDomain.HeightOneSpectrum.valuation K v₀ (2 : K) *
            IsDedekindDomain.HeightOneSpectrum.valuation K v₀
              (algebraMap (NumberField.RingOfIntegers K) K W) := hv_prod.symm
      _ ≤ IsDedekindDomain.HeightOneSpectrum.valuation K v₀ (2 : K) * 1 :=
          mul_le_mul_right hW_le _
      _ = IsDedekindDomain.HeightOneSpectrum.valuation K v₀ (2 : K) := mul_one _
  have h2 : Valued.v (2 : v₀.adicCompletion K) = 1 := by
    rw [← map_ofNat (algebraMap K (v₀.adicCompletion K)) 2]
    exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v₀ (2 : K)).trans h2_val
  have exists_ringOfIntegers_approx_of_valuation_le_one :
      ∀ (a : K), IsDedekindDomain.HeightOneSpectrum.valuation K v₀ a ≤ 1 →
      ∃ r : NumberField.RingOfIntegers K,
        IsDedekindDomain.HeightOneSpectrum.valuation K v₀
          (a - algebraMap (NumberField.RingOfIntegers K) K r) < 1 := by
    intro a ha
    obtain ⟨xa, ya, hya, hxya⟩ :=
      IsFractionRing.div_surjective (A := NumberField.RingOfIntegers K) (K := K) a
    have hy0 : ya ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hya
    have hiy : algebraMap (NumberField.RingOfIntegers K) K ya ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hya
    have hstar : a * algebraMap (NumberField.RingOfIntegers K) K ya
        = algebraMap (NumberField.RingOfIntegers K) K xa := by
      rw [← hxya]
      exact div_mul_cancel₀ _ hiy
    obtain ⟨m, hym, hym1⟩ : ∃ m : ℕ, ya ∈ v₀.asIdeal ^ m ∧ ya ∉ v₀.asIdeal ^ (m + 1) := by
      have ht0 : v₀.intValuation ya ≠ 0 :=
        IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero v₀ ya hy0
      have ht1 : v₀.intValuation ya ≤ 1 :=
        IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v₀ ya
      obtain ⟨k, hk⟩ : ∃ k : ℤ, WithZero.exp k = v₀.intValuation ya := ⟨_, WithZero.exp_log ht0⟩
      have hkle : k ≤ 0 := by
        have hstep : WithZero.exp k ≤ WithZero.exp (0 : ℤ) := by
          rw [hk, WithZero.exp_zero]; exact ht1
        exact WithZero.exp_le_exp.mp hstep
      have hcast : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      have hexpm : WithZero.exp (-(((-k).toNat : ℕ) : ℤ)) = v₀.intValuation ya := by
        rw [hcast, neg_neg, hk]
      refine ⟨(-k).toNat, ?_, ?_⟩
      · exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v₀ ya _).mp
          (le_of_eq hexpm.symm)
      · intro hcon
        have hle :=
          (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v₀ ya
            ((-k).toNat + 1)).mpr hcon
        have he : (-(((-k).toNat + 1 : ℕ) : ℤ)) = k - 1 := by
          rw [Nat.cast_add, Nat.cast_one, hcast]; ring
        rw [he, ← hk] at hle
        have := WithZero.exp_le_exp.mp hle
        omega
    have hivy : v₀.intValuation ya ≤ WithZero.exp (-(m : ℤ)) :=
      (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v₀ ya m).mpr hym
    have hxm : xa ∈ v₀.asIdeal ^ m := by
      refine (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v₀ xa m).mp ?_
      have e1 : v₀.intValuation xa
          = IsDedekindDomain.HeightOneSpectrum.valuation K v₀
              (algebraMap (NumberField.RingOfIntegers K) K xa) :=
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v₀ xa).symm
      have e2 : v₀.intValuation ya
          = IsDedekindDomain.HeightOneSpectrum.valuation K v₀
              (algebraMap (NumberField.RingOfIntegers K) K ya) :=
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v₀ ya).symm
      calc v₀.intValuation xa
          = IsDedekindDomain.HeightOneSpectrum.valuation K v₀
              (a * algebraMap (NumberField.RingOfIntegers K) K ya) := by
            rw [hstar]; exact e1
        _ = IsDedekindDomain.HeightOneSpectrum.valuation K v₀ a *
              IsDedekindDomain.HeightOneSpectrum.valuation K v₀
                (algebraMap (NumberField.RingOfIntegers K) K ya) := Valuation.map_mul _ _ _
        _ ≤ 1 * IsDedekindDomain.HeightOneSpectrum.valuation K v₀
                (algebraMap (NumberField.RingOfIntegers K) K ya) := mul_le_mul_left ha _
        _ = v₀.intValuation ya := by rw [one_mul, ← e2]
        _ ≤ WithZero.exp (-(m : ℤ)) := hivy
    have hPprime : Prime v₀.asIdeal := Ideal.prime_of_isPrime v₀.ne_bot v₀.isPrime
    have hJdvd : (Ideal.span {ya} ⊔ v₀.asIdeal ^ (m + 1)) ∣ v₀.asIdeal ^ (m + 1) :=
      Ideal.dvd_iff_le.mpr le_sup_right
    obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow hPprime (m + 1)).mp hJdvd
    have hJ : Ideal.span {ya} ⊔ v₀.asIdeal ^ (m + 1) = v₀.asIdeal ^ i := associated_iff_eq.mp hassoc
    have hyJ : ya ∈ v₀.asIdeal ^ i := by
      rw [← hJ]
      exact Ideal.dvd_span_singleton.mp (Ideal.dvd_iff_le.mpr le_sup_left)
    have him : i ≤ m := by
      by_contra hcon
      have hii : i = m + 1 := by omega
      rw [hii] at hyJ
      exact hym1 hyJ
    have hxJ : xa ∈ Ideal.span {ya} ⊔ v₀.asIdeal ^ (m + 1) := by
      rw [hJ]
      exact Ideal.pow_le_pow_right him hxm
    obtain ⟨p, hp, w, hw, hpw⟩ := Submodule.mem_sup.mp hxJ
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hp
    refine ⟨r, ?_⟩
    have hxrw : xa = r * ya + w := by rw [← hpw, hr]
    have key : (a - algebraMap (NumberField.RingOfIntegers K) K r)
        * algebraMap (NumberField.RingOfIntegers K) K ya
        = algebraMap (NumberField.RingOfIntegers K) K w := by
      have h1 : algebraMap (NumberField.RingOfIntegers K) K xa
          = algebraMap (NumberField.RingOfIntegers K) K r
              * algebraMap (NumberField.RingOfIntegers K) K ya
            + algebraMap (NumberField.RingOfIntegers K) K w := by
        rw [hxrw, map_add, map_mul]
      rw [sub_mul, hstar, h1]; ring
    have hV : IsDedekindDomain.HeightOneSpectrum.valuation K v₀
          (a - algebraMap (NumberField.RingOfIntegers K) K r) * v₀.intValuation ya
        = v₀.intValuation w := by
      rw [← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v₀ ya,
        ← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v₀ w,
        ← Valuation.map_mul, key]
    have hwb : v₀.intValuation w ≤ WithZero.exp (-((m + 1 : ℕ) : ℤ)) :=
      (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v₀ w (m + 1)).mpr hw
    have hyb : WithZero.exp (-((m + 1 : ℕ) : ℤ)) < v₀.intValuation ya := by
      by_contra hcon
      push_neg at hcon
      exact hym1
        ((IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v₀ ya (m + 1)).mp hcon)
    by_contra hcon
    push_neg at hcon
    have hchain : v₀.intValuation ya ≤ v₀.intValuation w := by
      calc v₀.intValuation ya = 1 * v₀.intValuation ya := (one_mul _).symm
        _ ≤ IsDedekindDomain.HeightOneSpectrum.valuation K v₀
              (a - algebraMap (NumberField.RingOfIntegers K) K r) * v₀.intValuation ya :=
            mul_le_mul_left hcon _
        _ = v₀.intValuation w := hV
    exact absurd (lt_of_le_of_lt (le_trans hchain hwb) hyb) (lt_irrefl _)
  have h_approx : ∀ z : v₀.adicCompletion K, Valued.v z ≤ 1 →
      ∃ r : NumberField.RingOfIntegers K,
        Valued.v (z - algebraMap K (v₀.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K r)) < 1 := by
    intro z hz
    have hdense : DenseRange (fun y : K => algebraMap K (v₀.adicCompletion K) y) := by
      letI : Valued K (WithZero (Multiplicative ℤ)) :=
        IsDedekindDomain.HeightOneSpectrum.adicValued (K := K) v₀
      exact UniformSpace.Completion.denseRange_coe
    have hnhds : {y : v₀.adicCompletion K |
        Valued.v (y - z) < ((1 : (WithZero (Multiplicative ℤ))ˣ) :
          WithZero (Multiplicative ℤ))} ∈ nhds z :=
      Valued.mem_nhds.mpr ⟨1, subset_rfl⟩
    obtain ⟨u, hu1, k, hk⟩ := mem_closure_iff_nhds.mp (hdense z) _ hnhds
    have hkl : Valued.v (z - algebraMap K (v₀.adicCompletion K) k) < 1 := by
      dsimp only at hk
      rw [Valuation.map_sub_swap, hk]
      exact hu1
    have hvc : ∀ x : K, Valued.v (algebraMap K (v₀.adicCompletion K) x) =
        IsDedekindDomain.HeightOneSpectrum.valuation K v₀ x :=
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v₀
    have hvk : IsDedekindDomain.HeightOneSpectrum.valuation K v₀ k ≤ 1 := by
      rw [← hvc k]
      have hsplit : algebraMap K (v₀.adicCompletion K) k =
          z - (z - algebraMap K (v₀.adicCompletion K) k) := by ring
      rw [hsplit]
      exact le_trans (Valuation.map_sub Valued.v _ _) (max_le hz (le_of_lt hkl))
    obtain ⟨r, hr⟩ := exists_ringOfIntegers_approx_of_valuation_le_one k hvk
    refine ⟨r, ?_⟩
    have hsplit2 : z - algebraMap K (v₀.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K r) =
        (z - algebraMap K (v₀.adicCompletion K) k) +
          algebraMap K (v₀.adicCompletion K)
            (k - algebraMap (NumberField.RingOfIntegers K) K r) := by
      rw [map_sub]; ring
    rw [hsplit2]
    refine lt_of_le_of_lt (Valuation.map_add Valued.v _ _) (max_lt hkl ?_)
    rw [hvc]
    exact hr
  have exists_sol_quadratic_mod_heightOneSpectrum :
      (2 : NumberField.RingOfIntegers K) ∉ v₀.asIdeal →
      ∀ (r s : NumberField.RingOfIntegers K), r ∉ v₀.asIdeal → s ∉ v₀.asIdeal →
      ∃ x₀ y₀ : NumberField.RingOfIntegers K, r * x₀ ^ 2 + s * y₀ ^ 2 - 1 ∈ v₀.asIdeal := by
    intro h2not r s hr hs
    letI : Field (NumberField.RingOfIntegers K ⧸ v₀.asIdeal) := Ideal.Quotient.field v₀.asIdeal
    letI : Fintype (NumberField.RingOfIntegers K ⧸ v₀.asIdeal) := Fintype.ofFinite _
    have hr' : Ideal.Quotient.mk v₀.asIdeal r ≠ 0 := fun h =>
      hr (Ideal.Quotient.eq_zero_iff_mem.mp h)
    have hs' : Ideal.Quotient.mk v₀.asIdeal s ≠ 0 := fun h =>
      hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
    have h2' : (2 : NumberField.RingOfIntegers K ⧸ v₀.asIdeal) ≠ 0 := by
      intro h
      refine h2not (Ideal.Quotient.eq_zero_iff_mem.mp ?_)
      rw [map_ofNat]
      exact h
    have hchar : ringChar (NumberField.RingOfIntegers K ⧸ v₀.asIdeal) ≠ 2 := by
      intro h
      refine h2' ?_
      have h4 : ((2 : ℕ) : NumberField.RingOfIntegers K ⧸ v₀.asIdeal) = 0 :=
        (ringChar.spec _ 2).mpr (by rw [h])
      simpa using h4
    have hcard : Fintype.card (NumberField.RingOfIntegers K ⧸ v₀.asIdeal) % 2 = 1 :=
      FiniteField.odd_card_of_char_ne_two hchar
    obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
      (f := Polynomial.C (Ideal.Quotient.mk v₀.asIdeal r) * Polynomial.X ^ 2
        + Polynomial.C 0 * Polynomial.X + Polynomial.C 0)
      (g := Polynomial.C (Ideal.Quotient.mk v₀.asIdeal s) * Polynomial.X ^ 2
        + Polynomial.C 0 * Polynomial.X + Polynomial.C (-1))
      (Polynomial.degree_quadratic hr') (Polynomial.degree_quadratic hs') hcard
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, zero_mul, add_zero] at hab
    obtain ⟨x₀, hx₀⟩ := Ideal.Quotient.mk_surjective (I := v₀.asIdeal) a
    obtain ⟨y₀, hy₀⟩ := Ideal.Quotient.mk_surjective (I := v₀.asIdeal) b
    refine ⟨x₀, y₀, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
    simp only [map_sub, map_add, map_mul, map_pow, map_one]
    rw [hx₀, hy₀]
    linear_combination hab
  have h_hensel : ∀ (c x₀ : v₀.adicCompletion K),
      Valued.v x₀ = (1 : WithZero (Multiplicative ℤ)) →
      Valued.v (c - x₀ ^ 2) < (1 : WithZero (Multiplicative ℤ)) →
      ∃ z : v₀.adicCompletion K, z ^ 2 = c := by
    intro c x₀ hx₀ hc
    have hstep : ∀ y : v₀.adicCompletion K,
        Valued.v y = (1 : WithZero (Multiplicative ℤ)) →
        Valued.v (y ^ 2 - c) < (1 : WithZero (Multiplicative ℤ)) →
        Valued.v (y - (y ^ 2 - c) / (2 * y)) = (1 : WithZero (Multiplicative ℤ)) ∧
        Valued.v ((y - (y ^ 2 - c) / (2 * y)) ^ 2 - c) = Valued.v (y ^ 2 - c) ^ 2 ∧
        Valued.v (y - (y ^ 2 - c) / (2 * y) - y) = Valued.v (y ^ 2 - c) := by
      intro y hy hd
      have h2ne : (2 : v₀.adicCompletion K) ≠ 0 := by
        intro hcon; rw [hcon, map_zero] at h2; exact zero_ne_one h2
      have hyne : y ≠ 0 := by
        intro hcon; rw [hcon, map_zero] at hy; exact zero_ne_one hy
      have ht : Valued.v ((y ^ 2 - c) / (2 * y)) = Valued.v (y ^ 2 - c) := by
        rw [map_div₀, map_mul, h2, hy, one_mul, div_one]
      have hlt' : Valued.v ((y ^ 2 - c) / (2 * y)) < Valued.v y := by
        rw [ht, hy]; exact hd
      refine ⟨?_, ?_, ?_⟩
      · rw [Valuation.map_sub_eq_of_lt_left _ hlt', hy]
      · have key : (y - (y ^ 2 - c) / (2 * y)) ^ 2 - c = ((y ^ 2 - c) / (2 * y)) ^ 2 := by
          field_simp; ring
        rw [key, Valuation.map_pow, ht]
      · have key : y - (y ^ 2 - c) / (2 * y) - y = -((y ^ 2 - c) / (2 * y)) := by ring
        rw [key, Valuation.map_neg, ht]
    have hdecay : ∀ δ γ : WithZero (Multiplicative ℤ), δ < 1 → γ ≠ 0 →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → δ ^ (2 ^ n) < γ := by
      intro δ γ hδ hγ
      rcases eq_or_ne δ 0 with h0 | h0
      · refine ⟨0, fun n _ => ?_⟩
        rw [h0, zero_pow (Nat.two_pow_pos n).ne']
        exact zero_lt_iff.mpr hγ
      · obtain ⟨a, rfl⟩ : ∃ a : ℤ, δ = ((Multiplicative.ofAdd a : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
          obtain ⟨g, hg⟩ := WithZero.ne_zero_iff_exists.mp h0
          exact ⟨Multiplicative.toAdd g, hg.symm⟩
        obtain ⟨b, rfl⟩ : ∃ b : ℤ, γ = ((Multiplicative.ofAdd b : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
          obtain ⟨g, hg⟩ := WithZero.ne_zero_iff_exists.mp hγ
          exact ⟨Multiplicative.toAdd g, hg.symm⟩
        have ha : a < 0 := WithZero.coe_lt_one.mp hδ
        have hpow : ∀ k : ℕ,
            ((Multiplicative.ofAdd a : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ k
              = ((Multiplicative.ofAdd ((k : ℤ) * a) : Multiplicative ℤ) :
                  WithZero (Multiplicative ℤ)) := by
          intro k; rw [← WithZero.coe_pow]; congr 1
        refine ⟨(-b).toNat + 1, fun n hn => ?_⟩
        rw [hpow, WithZero.coe_lt_coe]
        have hbk : -b < ((2 ^ n : ℕ) : ℤ) := by
          have hx : (-b).toNat < n := by omega
          have h1 : (-b).toNat < 2 ^ n := lt_trans hx Nat.lt_two_pow_self
          have h2' : ((-b).toNat : ℤ) < ((2 ^ n : ℕ) : ℤ) := by exact_mod_cast h1
          exact lt_of_le_of_lt (Int.self_le_toNat _) h2'
        have hkpos : (0 : ℤ) ≤ ((2 ^ n : ℕ) : ℤ) := Int.natCast_nonneg _
        have ha1 : a ≤ -1 := by omega
        have hle : ((2 ^ n : ℕ) : ℤ) * a ≤ ((2 ^ n : ℕ) : ℤ) * (-1) :=
          mul_le_mul_of_nonneg_left ha1 hkpos
        have hgoal : ((2 ^ n : ℕ) : ℤ) * a < b := by linarith
        exact hgoal
    obtain ⟨ε, hεdef⟩ : ∃ ε : WithZero (Multiplicative ℤ), ε = Valued.v (x₀ ^ 2 - c) := ⟨_, rfl⟩
    have hε : ε < (1 : WithZero (Multiplicative ℤ)) := by
      rw [hεdef, Valuation.map_sub_swap]; exact hc
    obtain ⟨f, hf0, hfs⟩ : ∃ f : ℕ → v₀.adicCompletion K, f 0 = x₀ ∧
        ∀ n : ℕ, f (n + 1) = f n - (f n ^ 2 - c) / (2 * f n) :=
      ⟨fun n => Nat.rec (motive := fun _ => v₀.adicCompletion K) x₀
        (fun _ y => y - (y ^ 2 - c) / (2 * y)) n, rfl, fun _ => rfl⟩
    have hinv : ∀ n : ℕ, Valued.v (f n) = (1 : WithZero (Multiplicative ℤ)) ∧
        Valued.v (f n ^ 2 - c) = ε ^ (2 ^ n) := by
      intro n
      induction n with
      | zero =>
        refine ⟨by rw [hf0]; exact hx₀, ?_⟩
        rw [hf0, pow_zero, pow_one, hεdef]
      | succ n ih =>
        have hlt : Valued.v (f n ^ 2 - c) < (1 : WithZero (Multiplicative ℤ)) := by
          rw [ih.2]; exact pow_lt_one₀ zero_le' hε (Nat.two_pow_pos n).ne'
        obtain ⟨s1, s2, -⟩ := hstep (f n) ih.1 hlt
        refine ⟨by rw [hfs n]; exact s1, ?_⟩
        rw [hfs n, s2, ih.2, ← pow_mul, ← pow_succ]
    have hdiff : ∀ n : ℕ, Valued.v (f (n + 1) - f n) = ε ^ (2 ^ n) := by
      intro n
      have hlt : Valued.v (f n ^ 2 - c) < (1 : WithZero (Multiplicative ℤ)) := by
        rw [(hinv n).2]; exact pow_lt_one₀ zero_le' hε (Nat.two_pow_pos n).ne'
      obtain ⟨-, -, s3⟩ := hstep (f n) (hinv n).1 hlt
      rw [hfs n, s3, (hinv n).2]
    have hCauchy : Cauchy (Filter.map f Filter.atTop) := by
      refine Valued.cauchy_iff.mpr ⟨inferInstance, ?_⟩
      intro γ
      obtain ⟨N, hN⟩ := hdecay ε (γ : WithZero (Multiplicative ℤ)) hε (Units.ne_zero γ)
      have htel : ∀ m : ℕ, N ≤ m → Valued.v (f m - f N) < (γ : WithZero (Multiplicative ℤ)) := by
        intro m hm
        induction m, hm using Nat.le_induction with
        | base =>
          rw [sub_self, map_zero]; exact zero_lt_iff.mpr (Units.ne_zero γ)
        | succ m hm ih =>
          have e : f (m + 1) - f N = (f (m + 1) - f m) + (f m - f N) := by ring
          rw [e]
          refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ih)
          rw [hdiff m]; exact hN m hm
      refine ⟨f '' (Set.Ici N), Filter.image_mem_map (Filter.Ici_mem_atTop N), ?_⟩
      rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
      have e : f j - f i = (f j - f N) - (f i - f N) := by ring
      rw [e]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt (htel j hj) (htel i hi))
    obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hCauchy
    have hsq : Filter.Tendsto (fun n : ℕ => f n ^ 2 - c) Filter.atTop (nhds (z ^ 2 - c)) :=
      (hz.pow 2).sub tendsto_const_nhds
    have hzero : Filter.Tendsto (fun n : ℕ => f n ^ 2 - c) Filter.atTop
        (nhds (0 : v₀.adicCompletion K)) := by
      rw [Filter.tendsto_def]
      intro s hs
      obtain ⟨γ, hγs⟩ := Valued.mem_nhds_zero.mp hs
      obtain ⟨N, hN⟩ := hdecay ε (γ : WithZero (Multiplicative ℤ)) hε (Units.ne_zero γ)
      refine Filter.mem_of_superset (Filter.Ici_mem_atTop N) ?_
      intro n hn
      apply hγs
      show Valued.v (f n ^ 2 - c) < (γ : WithZero (Multiplicative ℤ))
      rw [(hinv n).2]; exact hN n hn
    exact ⟨z, eq_of_sub_eq_zero (tendsto_nhds_unique hsq hzero)⟩
  have s2 : ∀ (r s : v₀.adicCompletion K),
      Valued.v r = 1 → Valued.v s = 1 → hilbLoc v₀ r s = 1 := by
    intro r s hr hs
    have hT_int : ∀ a : NumberField.RingOfIntegers K,
        Valued.v (algebraMap K (v₀.adicCompletion K)
            (algebraMap (NumberField.RingOfIntegers K) K a))
          = IsDedekindDomain.HeightOneSpectrum.intValuation v₀ a := by
      intro a
      exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v₀
        (algebraMap (NumberField.RingOfIntegers K) K a)).trans
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v₀ a)
    have h2not : (2 : NumberField.RingOfIntegers K) ∉ v₀.asIdeal := by
      refine IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mp ?_
      rw [← hT_int (2 : NumberField.RingOfIntegers K),
        map_ofNat (algebraMap (NumberField.RingOfIntegers K) K) 2,
        map_ofNat (algebraMap K (v₀.adicCompletion K)) 2]
      exact h2
    obtain ⟨R₀, hA1⟩ := h_approx r (le_of_eq hr)
    obtain ⟨S₀, hA2⟩ := h_approx s (le_of_eq hs)
    have hR0v : Valued.v (algebraMap K (v₀.adicCompletion K)
        (algebraMap (NumberField.RingOfIntegers K) K R₀)) = 1 := by
      have e : (algebraMap K (v₀.adicCompletion K)
            (algebraMap (NumberField.RingOfIntegers K) K R₀))
          = r - (r - algebraMap K (v₀.adicCompletion K)
              (algebraMap (NumberField.RingOfIntegers K) K R₀)) := by ring
      rw [e, Valuation.map_sub_eq_of_lt_left _ (by rw [hr]; exact hA1), hr]
    have hS0v : Valued.v (algebraMap K (v₀.adicCompletion K)
        (algebraMap (NumberField.RingOfIntegers K) K S₀)) = 1 := by
      have e : (algebraMap K (v₀.adicCompletion K)
            (algebraMap (NumberField.RingOfIntegers K) K S₀))
          = s - (s - algebraMap K (v₀.adicCompletion K)
              (algebraMap (NumberField.RingOfIntegers K) K S₀)) := by ring
      rw [e, Valuation.map_sub_eq_of_lt_left _ (by rw [hs]; exact hA2), hs]
    have hR0not : R₀ ∉ v₀.asIdeal := by
      refine IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mp ?_
      rw [← hT_int R₀]; exact hR0v
    have hS0not : S₀ ∉ v₀.asIdeal := by
      refine IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mp ?_
      rw [← hT_int S₀]; exact hS0v
    obtain ⟨A, B, hAB⟩ :=
      exists_sol_quadratic_mod_heightOneSpectrum h2not R₀ S₀ hR0not hS0not
    let ρR := algebraMap K (v₀.adicCompletion K) (algebraMap (NumberField.RingOfIntegers K) K R₀)
    let ρS := algebraMap K (v₀.adicCompletion K) (algebraMap (NumberField.RingOfIntegers K) K S₀)
    let X := algebraMap K (v₀.adicCompletion K) (algebraMap (NumberField.RingOfIntegers K) K A)
    let Y := algebraMap K (v₀.adicCompletion K) (algebraMap (NumberField.RingOfIntegers K) K B)
    have hXle : Valued.v X ≤ 1 := by
      change Valued.v (algebraMap K (v₀.adicCompletion K)
        (algebraMap (NumberField.RingOfIntegers K) K A)) ≤ 1
      rw [hT_int A]; exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v₀ A
    have hYle : Valued.v Y ≤ 1 := by
      change Valued.v (algebraMap K (v₀.adicCompletion K)
        (algebraMap (NumberField.RingOfIntegers K) K B)) ≤ 1
      rw [hT_int B]; exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v₀ B
    have hmod : Valued.v (ρR * X ^ 2 + ρS * Y ^ 2 - 1) < 1 := by
      have e : ρR * X ^ 2 + ρS * Y ^ 2 - 1 =
          algebraMap K (v₀.adicCompletion K)
            (algebraMap (NumberField.RingOfIntegers K) K (R₀ * A ^ 2 + S₀ * B ^ 2 - 1)) := by
        simp only [ρR, ρS, X, Y, map_add, map_mul, map_pow, map_sub, map_one]
      rw [e, hT_int, IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem]
      exact hAB
    have hunit : Valued.v X = 1 ∨ Valued.v Y = 1 := by
      have hcase : A ∉ v₀.asIdeal ∨ B ∉ v₀.asIdeal := by
        by_contra hcon
        push_neg at hcon
        obtain ⟨hA, hB⟩ := hcon
        have h1 : R₀ * A ^ 2 + S₀ * B ^ 2 ∈ v₀.asIdeal :=
          Ideal.add_mem _
            (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hA 2 (by norm_num)))
            (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hB 2 (by norm_num)))
        have hone : (1 : NumberField.RingOfIntegers K) ∈ v₀.asIdeal := by
          have h3 := Ideal.sub_mem _ h1 hAB
          simpa using h3
        exact v₀.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)
      rcases hcase with h | h
      · refine Or.inl ?_
        change Valued.v (algebraMap K (v₀.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K A)) = 1
        rw [hT_int A]; exact IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr h
      · refine Or.inr ?_
        change Valued.v (algebraMap K (v₀.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K B)) = 1
        rw [hT_int B]; exact IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr h
    have hbeta : Valued.v (r * X ^ 2 + s * Y ^ 2 - 1) < 1 := by
      have t1 : Valued.v ((r - ρR) * X ^ 2) < 1 := by
        rw [Valuation.map_mul, Valuation.map_pow]
        calc Valued.v (r - ρR) * Valued.v X ^ 2
            ≤ Valued.v (r - ρR) * 1 := mul_le_mul_left' (pow_le_one' hXle 2) _
          _ = Valued.v (r - ρR) := mul_one _
          _ < 1 := hA1
      have t2 : Valued.v ((s - ρS) * Y ^ 2) < 1 := by
        rw [Valuation.map_mul, Valuation.map_pow]
        calc Valued.v (s - ρS) * Valued.v Y ^ 2
            ≤ Valued.v (s - ρS) * 1 := mul_le_mul_left' (pow_le_one' hYle 2) _
          _ = Valued.v (s - ρS) := mul_one _
          _ < 1 := hA2
      have t3 : Valued.v ((r - ρR) * X ^ 2 + (s - ρS) * Y ^ 2) < 1 :=
        lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt t1 t2)
      have e : r * X ^ 2 + s * Y ^ 2 - 1
          = (ρR * X ^ 2 + ρS * Y ^ 2 - 1)
            + ((r - ρR) * X ^ 2 + (s - ρS) * Y ^ 2) := by ring
      rw [e]
      exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hmod t3)
    have key : ∀ a b P Q : v₀.adicCompletion K, Valued.v a = 1 → Valued.v P = 1 →
        Valued.v (a * P ^ 2 + b * Q ^ 2 - 1) < 1 →
        ∃ x y : v₀.adicCompletion K, a * x ^ 2 + b * y ^ 2 = 1 := by
      intro a b P Q ha hP hlt
      have ha0 : a ≠ 0 := by
        intro hzero; rw [hzero, Valuation.map_zero] at ha; exact zero_ne_one ha
      have hac : a * ((1 - b * Q ^ 2) / a) = 1 - b * Q ^ 2 := mul_div_cancel₀ _ ha0
      have hid : a * ((1 - b * Q ^ 2) / a - P ^ 2)
          = -(a * P ^ 2 + b * Q ^ 2 - 1) := by
        rw [mul_sub, hac]; ring
      have hlt2 : Valued.v ((1 - b * Q ^ 2) / a - P ^ 2) < 1 := by
        have h : Valued.v (a * ((1 - b * Q ^ 2) / a - P ^ 2))
            = Valued.v (-(a * P ^ 2 + b * Q ^ 2 - 1)) := by rw [hid]
        rw [Valuation.map_mul, ha, one_mul, Valuation.map_neg] at h
        rw [h]; exact hlt
      obtain ⟨x, hx⟩ := h_hensel ((1 - b * Q ^ 2) / a) P hP hlt2
      exact ⟨x, Q, by rw [hx]; linear_combination hac⟩
    have hex : ∃ x y : v₀.adicCompletion K, r * x ^ 2 + s * y ^ 2 = 1 := by
      rcases hunit with hX1 | hY1
      · exact key r s X Y hr hX1 hbeta
      · have hbeta' : Valued.v (s * Y ^ 2 + r * X ^ 2 - 1) < 1 := by
          have e : s * Y ^ 2 + r * X ^ 2 - 1 = r * X ^ 2 + s * Y ^ 2 - 1 := by ring
          rw [e]; exact hbeta
        obtain ⟨x, y, hxy⟩ := key s r Y X hs hY1 hbeta'
        exact ⟨y, x, by linear_combination hxy⟩
    simp only [hilbLoc, if_pos hex]
  have s3 : ∀ (u w : v₀.adicCompletion K),
      Valued.v u = 1 → Valued.v w = 1 → (IsSquare (u * w) ↔ (IsSquare u ↔ IsSquare w)) := by
    intro u w hu hw
    have hu0 : u ≠ 0 := by intro h; rw [h, Valuation.map_zero] at hu; exact zero_ne_one hu
    have hw0 : w ≠ 0 := by intro h; rw [h, Valuation.map_zero] at hw; exact zero_ne_one hw
    constructor
    · rintro ⟨t, ht⟩
      constructor
      · rintro ⟨s, rfl⟩
        have hs0 : s ≠ 0 := by rintro rfl; rw [mul_zero] at hu0; exact hu0 rfl
        refine ⟨t / s, ?_⟩
        field_simp [hs0]
        linear_combination ht
      · rintro ⟨s, rfl⟩
        have hs0 : s ≠ 0 := by rintro rfl; rw [mul_zero] at hw0; exact hw0 rfl
        refine ⟨t / s, ?_⟩
        field_simp [hs0]
        linear_combination ht
    · intro hiff
      by_cases hu_sq : IsSquare u
      · exact IsSquare.mul hu_sq (hiff.mp hu_sq)
      · have hw_nsq : ¬ IsSquare w := fun hw_sq => hu_sq (hiff.mpr hw_sq)
        let ι : NumberField.RingOfIntegers K →+* v₀.adicCompletion K :=
          (algebraMap K (v₀.adicCompletion K)).comp (algebraMap (NumberField.RingOfIntegers K) K)
        have V0 : ∀ c : NumberField.RingOfIntegers K, Valued.v (ι c) = v₀.intValuation c := by
          intro c
          exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v₀
            (algebraMap (NumberField.RingOfIntegers K) K c)).trans
            (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v₀ c)
        have Vlt : ∀ c : NumberField.RingOfIntegers K, Valued.v (ι c) < 1 ↔ c ∈ v₀.asIdeal := by
          intro c; rw [V0 c]
          exact IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem v₀ c
        have Vle : ∀ c : NumberField.RingOfIntegers K, Valued.v (ι c) ≤ 1 := by
          intro c; rw [V0 c]
          exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v₀ c
        have HB : ∀ m : v₀.adicCompletion K, Valued.v m = 1 →
            ∀ a s : NumberField.RingOfIntegers K, Valued.v (m - ι a) < 1 →
            s ^ 2 - a ∈ v₀.asIdeal → IsSquare m := by
          intro m hm a s hma hs
          have hanm : a ∉ v₀.asIdeal := by
            intro hmem
            have h1 : Valued.v (ι a) < 1 := (Vlt a).mpr hmem
            have e : m = (m - ι a) + ι a := by ring
            have h3 : Valued.v m < 1 := by
              rw [e]; exact lt_of_le_of_lt (Valuation.map_add Valued.v _ _) (max_lt hma h1)
            rw [hm] at h3; exact lt_irrefl _ h3
          have hsnm : s ∉ v₀.asIdeal := by
            intro hmem
            apply hanm
            have e : a = s ^ 2 - (s ^ 2 - a) := by ring
            rw [e]
            exact Ideal.sub_mem _ (Ideal.pow_mem_of_mem _ hmem 2 (by norm_num)) hs
          have hs1 : Valued.v (ι s) = 1 := by
            rcases lt_or_eq_of_le (Vle s) with h | h
            · exact absurd ((Vlt s).mp h) hsnm
            · exact h
          have hd : Valued.v (m - (ι s) ^ 2) < 1 := by
            have e : m - (ι s) ^ 2 = (m - ι a) - ι (s ^ 2 - a) := by
              rw [map_sub, map_pow]; ring
            have h1 : Valued.v (ι (s ^ 2 - a)) < 1 := (Vlt _).mpr hs
            rw [e]
            exact lt_of_le_of_lt (Valuation.map_sub Valued.v _ _) (max_lt hma h1)
          obtain ⟨x, hx⟩ := h_hensel m (ι s) hs1 hd
          exact ⟨x, by rw [← sq]; exact hx.symm⟩
        have core : ∀ (F : Type u) [Field F] [Finite F] (x y : F),
            ¬ IsSquare x → ¬ IsSquare y → IsSquare (x * y) := by
          intro F _ _ x y hx hy
          letI : Fintype F := Fintype.ofFinite F
          letI : DecidableEq F := Classical.decEq F
          by_contra hxy
          have e1 : quadraticChar F x = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hx
          have e2 : quadraticChar F y = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hy
          have e3 : quadraticChar F (x * y) = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hxy
          rw [map_mul, e1, e2] at e3
          norm_num at e3
        obtain ⟨a, haU⟩ := h_approx u (le_of_eq hu)
        obtain ⟨b, hbW⟩ := h_approx w (le_of_eq hw)
        have hib : Valued.v (ι b) = 1 := by
          rcases lt_or_eq_of_le (Vle b) with h | h
          · exfalso
            have e : w = ι b + (w - ι b) := by ring
            have h3 : Valued.v w < 1 := by
              rw [e]; exact lt_of_le_of_lt (Valuation.map_add Valued.v _ _) (max_lt h hbW)
            rw [hw] at h3; exact lt_irrefl _ h3
          · exact h
        letI : Field (NumberField.RingOfIntegers K ⧸ v₀.asIdeal) := Ideal.Quotient.field v₀.asIdeal
        have hnsq_a : ¬ IsSquare (Ideal.Quotient.mk v₀.asIdeal a) := by
          rintro ⟨y, hy⟩
          obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
          refine hu_sq (HB u hu a s haU ?_)
          rw [← Ideal.Quotient.eq_zero_iff_mem]
          have hy' : Ideal.Quotient.mk v₀.asIdeal a =
              Ideal.Quotient.mk v₀.asIdeal s * Ideal.Quotient.mk v₀.asIdeal s := hy
          rw [map_sub, map_pow, hy']; ring
        have hnsq_b : ¬ IsSquare (Ideal.Quotient.mk v₀.asIdeal b) := by
          rintro ⟨y, hy⟩
          obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
          refine hw_nsq (HB w hw b s hbW ?_)
          rw [← Ideal.Quotient.eq_zero_iff_mem]
          have hy' : Ideal.Quotient.mk v₀.asIdeal b =
              Ideal.Quotient.mk v₀.asIdeal s * Ideal.Quotient.mk v₀.asIdeal s := hy
          rw [map_sub, map_pow, hy']; ring
        obtain ⟨y, hy⟩ := core (NumberField.RingOfIntegers K ⧸ v₀.asIdeal)
          (Ideal.Quotient.mk v₀.asIdeal a) (Ideal.Quotient.mk v₀.asIdeal b) hnsq_a hnsq_b
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
        have hsab : s ^ 2 - a * b ∈ v₀.asIdeal := by
          rw [← Ideal.Quotient.eq_zero_iff_mem]
          have hy' : Ideal.Quotient.mk v₀.asIdeal a * Ideal.Quotient.mk v₀.asIdeal b =
              Ideal.Quotient.mk v₀.asIdeal s * Ideal.Quotient.mk v₀.asIdeal s := hy
          rw [map_sub, map_pow, map_mul, hy']; ring
        have hmw : Valued.v (u * w) = 1 := by rw [Valuation.map_mul, hu, hw, one_mul]
        have hmab : Valued.v (u * w - ι (a * b)) < 1 := by
          have e : u * w - ι a * ι b = u * (w - ι b) + ι b * (u - ι a) := by ring
          have h1 : Valued.v (u * (w - ι b)) < 1 := by rw [Valuation.map_mul, hu, one_mul]; exact hbW
          have h3 : Valued.v (ι b * (u - ι a)) < 1 := by rw [Valuation.map_mul, hib, one_mul]; exact haU
          rw [map_mul ι a b, e]
          exact lt_of_le_of_lt (Valuation.map_add Valued.v _ _) (max_lt h1 h3)
        exact HB (u * w) hmw (a * b) s hmab hsab
  have s5 : ∃ ϖ : v₀.adicCompletion K,
      Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) ∧
      ∀ x : v₀.adicCompletion K, x ≠ 0 →
        ∃ z u : v₀.adicCompletion K, z ≠ 0 ∧ Valued.v u = 1 ∧
          (x = z ^ 2 * u ∨ x = z ^ 2 * (ϖ * u)) := by
    obtain ⟨π₀, hπ₀⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer K v₀
    let ϖ : v₀.adicCompletion K := algebraMap K (v₀.adicCompletion K) π₀
    have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) :=
      (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v₀ π₀).trans hπ₀
    have hϖ0 : ϖ ≠ 0 := by
      intro h; rw [h, Valuation.map_zero] at hϖ; exact WithZero.coe_ne_zero hϖ.symm
    refine ⟨ϖ, hϖ, ?_⟩
    intro x hx
    have hvx : Valued.v x ≠ 0 := fun h => hx ((Valuation.zero_iff _).mp h)
    obtain ⟨k, hexp⟩ : ∃ k : ℤ, WithZero.exp k = Valued.v x :=
      ⟨(Valued.v x).log, WithZero.exp_log hvx⟩
    have hvpow : Valued.v (ϖ ^ (-k)) = Valued.v x := by
      have h2' : ((-k : ℤ)) • (-1 : ℤ) = k := by simp
      calc Valued.v (ϖ ^ (-k)) = Valued.v ϖ ^ (-k) := map_zpow₀ _ _ _
        _ = WithZero.exp (-1 : ℤ) ^ (-k) := by rw [hϖ]
        _ = WithZero.exp ((-k : ℤ) • (-1 : ℤ)) := (WithZero.exp_zsmul _ _).symm
        _ = WithZero.exp k := by rw [h2']
        _ = Valued.v x := hexp
    let u : v₀.adicCompletion K := x / ϖ ^ (-k)
    have hu : Valued.v u = 1 := by
      change Valued.v (x / ϖ ^ (-k)) = 1
      rw [Valuation.map_div, hvpow, div_self hvx]
    have hx_eq : x = ϖ ^ (-k) * u := (mul_div_cancel₀ x (zpow_ne_zero _ hϖ0)).symm
    rcases Int.even_or_odd (-k) with ⟨r, hr⟩ | ⟨r, hr⟩
    · refine ⟨ϖ ^ r, u, zpow_ne_zero r hϖ0, hu, Or.inl ?_⟩
      rw [hx_eq, hr, zpow_add₀ hϖ0, ← sq]
    · refine ⟨ϖ ^ r, u, zpow_ne_zero r hϖ0, hu, Or.inr ?_⟩
      have hrr : 2 * r + 1 = (r + r) + 1 := by ring
      rw [hx_eq, hr, hrr, zpow_add₀ hϖ0, zpow_add₀ hϖ0, zpow_one, ← sq, mul_assoc]
  obtain ⟨ϖ, hϖ, hdecomp⟩ := s5
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, Valuation.map_zero] at hϖ; exact WithZero.coe_ne_zero hϖ.symm
  have s4 : ∀ (u w : v₀.adicCompletion K),
      Valued.v u = 1 → Valued.v w = 1 →
      ¬ IsSquare (ϖ * u) ∧
      (hilbLoc v₀ u (ϖ * w) = 1 ↔ IsSquare u) ∧
      (hilbLoc v₀ (ϖ * u) (ϖ * w) = 1 ↔ IsSquare (-(u * w))) := by
    intro u w hu hw
    have hilb_solvable_iff_norm_form : ∀ (a b : v₀.adicCompletion K),
        (2 : v₀.adicCompletion K) ≠ 0 → a ≠ 0 →
        ((∃ x y : v₀.adicCompletion K, a * x ^ 2 + b * y ^ 2 = 1) ↔
          (∃ z t : v₀.adicCompletion K, z ^ 2 - b * t ^ 2 = a)) := by
      intro a b h2ne ha
      constructor
      · rintro ⟨x, y, h⟩
        by_cases hx : x = 0
        · subst hx
          have hb : b * y ^ 2 = 1 := by linear_combination h
          have h2i : 2 * (2 : v₀.adicCompletion K)⁻¹ = 1 := mul_inv_cancel₀ h2ne
          refine ⟨(a + 1) * (2 : v₀.adicCompletion K)⁻¹,
            (1 - a) * y * (2 : v₀.adicCompletion K)⁻¹, ?_⟩
          linear_combination (-(1 - a) ^ 2 * ((2 : v₀.adicCompletion K)⁻¹) ^ 2) * hb +
            (a * (2 * (2 : v₀.adicCompletion K)⁻¹ + 1)) * h2i
        · have hu' : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
          refine ⟨x⁻¹, y * x⁻¹, ?_⟩
          linear_combination (-(x⁻¹) ^ 2) * h + (a * (x * x⁻¹ + 1)) * hu'
      · rintro ⟨z, t, h⟩
        by_cases hz : z = 0
        · subst hz
          have hbt : b * t ^ 2 = -a := by linear_combination -h
          have h2a : 2 * a * (2 * a)⁻¹ = 1 := mul_inv_cancel₀ (mul_ne_zero h2ne ha)
          refine ⟨(1 + a) * (2 * a)⁻¹, t * (a - 1) * (2 * a)⁻¹, ?_⟩
          linear_combination ((a - 1) ^ 2 * ((2 * a)⁻¹) ^ 2) * hbt +
            (2 * a * (2 * a)⁻¹ + 1) * h2a
        · have hw' : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
          refine ⟨z⁻¹, t * z⁻¹, ?_⟩
          linear_combination (-(z⁻¹) ^ 2) * h + (z * z⁻¹ + 1) * hw'
    have h_parity : ∀ (m y z : v₀.adicCompletion K),
        Valued.v m = WithZero.exp (-1 : ℤ) → z ≠ 0 →
        Valued.v (m * y ^ 2) ≠ Valued.v z ^ 2 := by
      intro m y z hm hz heq
      have hvz : Valued.v z ≠ 0 := fun h => hz ((Valuation.zero_iff _).mp h)
      have hvy : Valued.v y ≠ 0 := by
        intro h
        rw [Valuation.map_mul, Valuation.map_pow, h, zero_pow (by norm_num), mul_zero] at heq
        exact pow_ne_zero 2 hvz heq.symm
      obtain ⟨a, ha⟩ : ∃ a : ℤ, WithZero.exp a = Valued.v y :=
        ⟨(Valued.v y).log, WithZero.exp_log hvy⟩
      obtain ⟨b, hb⟩ : ∃ b : ℤ, WithZero.exp b = Valued.v z :=
        ⟨(Valued.v z).log, WithZero.exp_log hvz⟩
      rw [Valuation.map_mul, Valuation.map_pow, hm, ← ha, ← hb, sq, sq,
        ← WithZero.exp_add, ← WithZero.exp_add, ← WithZero.exp_add, WithZero.exp_inj] at heq
      omega
    have h_unit_unif : ∀ (u' w' : v₀.adicCompletion K),
        Valued.v u' = 1 → Valued.v w' = 1 →
        (hilbLoc v₀ u' (ϖ * w') = 1 ↔ IsSquare u') := by
      intro u' w' hu' hw'
      constructor
      · intro hhilb
        have hsol : ∃ x y : v₀.adicCompletion K, u' * x ^ 2 + (ϖ * w') * y ^ 2 = 1 := by
          simp only [hilbLoc] at hhilb
          split_ifs at hhilb with h
          · exact h
          · exfalso; revert hhilb; decide
        rcases hsol with ⟨x, y, hxy⟩
        have hm : Valued.v (ϖ * w') = WithZero.exp (-1 : ℤ) := by
          rw [Valuation.map_mul, hϖ, hw', mul_one]; rfl
        have hmy : (ϖ * w') * y ^ 2 = 1 - u' * x ^ 2 := by linear_combination hxy
        have hvx : Valued.v x = 1 := by
          rcases lt_trichotomy (Valued.v x) 1 with hlt | heq | hgt
          · exfalso
            refine h_parity (ϖ * w') y 1 hm one_ne_zero ?_
            have hux : Valued.v (u' * x ^ 2) < Valued.v (1 : v₀.adicCompletion K) := by
              rw [Valuation.map_mul, hu', one_mul, Valuation.map_pow, Valuation.map_one]
              exact pow_lt_one₀ zero_le' hlt (by norm_num)
            rw [hmy, Valuation.map_sub_eq_of_lt_left _ hux, Valuation.map_one, one_pow]
          · exact heq
          · exfalso
            have hx0 : x ≠ 0 := by
              rintro rfl; rw [Valuation.map_zero] at hgt; exact not_lt_of_ge zero_le' hgt
            refine h_parity (ϖ * w') y x hm hx0 ?_
            have hux : Valued.v (1 : v₀.adicCompletion K) < Valued.v (u' * x ^ 2) := by
              rw [Valuation.map_mul, hu', one_mul, Valuation.map_pow, Valuation.map_one]
              exact one_lt_pow₀ hgt (by norm_num)
            rw [hmy, Valuation.map_sub_eq_of_lt_right _ hux, Valuation.map_mul, hu', one_mul,
              Valuation.map_pow]
        have hx0 : x ≠ 0 := by
          rintro rfl; rw [Valuation.map_zero] at hvx; exact zero_ne_one hvx
        have hmy_le : Valued.v ((ϖ * w') * y ^ 2) ≤ 1 := by
          rw [hmy]
          refine le_trans (Valuation.map_sub _ _ _) (max_le (by rw [Valuation.map_one]) ?_)
          rw [Valuation.map_mul, hu', Valuation.map_pow, hvx, one_pow, mul_one]
        have hmy_ne : Valued.v ((ϖ * w') * y ^ 2) ≠ 1 := by
          intro h1
          refine h_parity (ϖ * w') y 1 hm one_ne_zero ?_
          rw [h1, Valuation.map_one, one_pow]
        have hmy_lt : Valued.v ((ϖ * w') * y ^ 2) < 1 := lt_of_le_of_ne hmy_le hmy_ne
        have hxinv : Valued.v (x⁻¹) = 1 := by rw [map_inv₀, hvx, inv_one]
        have hdiff : u' - (x⁻¹) ^ 2 = -(((ϖ * w') * y ^ 2) / x ^ 2) := by
          field_simp [hx0]; linear_combination hxy
        have hdiff_lt : Valued.v (u' - (x⁻¹) ^ 2) < 1 := by
          rw [hdiff, Valuation.map_neg, Valuation.map_div, Valuation.map_pow, hvx, one_pow, div_one]
          exact hmy_lt
        obtain ⟨t, ht⟩ := h_hensel u' (x⁻¹) hxinv hdiff_lt
        exact ⟨t, by rw [← sq]; exact ht.symm⟩
      · rintro ⟨s, rfl⟩
        have hs0 : s ≠ 0 := by
          rintro rfl; rw [mul_zero, Valuation.map_zero] at hu'; exact zero_ne_one hu'
        simp only [hilbLoc]
        rw [if_pos ⟨s⁻¹, 0, by field_simp [hs0]; ring⟩]
    refine ⟨?_, h_unit_unif u w hu hw, ?_⟩
    · rintro ⟨z, hz⟩
      have hvu : Valued.v (ϖ * u) = WithZero.exp (-1 : ℤ) := by
        rw [Valuation.map_mul, hϖ, hu, mul_one]; rfl
      have hz0 : z ≠ 0 := by
        rintro rfl; rw [mul_zero] at hz; rw [hz, Valuation.map_zero] at hvu
        exact WithZero.coe_ne_zero hvu.symm
      refine h_parity (ϖ * u) 1 z hvu hz0 ?_
      rw [one_pow, mul_one, hz, Valuation.map_mul, sq]
    · have h2ne : (2 : v₀.adicCompletion K) ≠ 0 := by
        intro h0; rw [h0, Valuation.map_zero] at h2; exact zero_ne_one h2
      have hu0 : u ≠ 0 := by
        intro h0; rw [h0, Valuation.map_zero] at hu; exact zero_ne_one hu
      have hϖu0 : ϖ * u ≠ 0 := mul_ne_zero hϖ0 hu0
      have hequiv : (∃ x y : v₀.adicCompletion K, (ϖ * u) * x ^ 2 + (ϖ * w) * y ^ 2 = 1) ↔
          (∃ X Y : v₀.adicCompletion K, -(u * w) * X ^ 2 + (ϖ * u) * Y ^ 2 = 1) := by
        rw [hilb_solvable_iff_norm_form (ϖ * u) (ϖ * w) h2ne hϖu0]
        constructor
        · rintro ⟨z, t, hzt⟩
          refine ⟨t / u, z / (ϖ * u), ?_⟩
          field_simp [hu0, hϖ0]
          linear_combination hzt
        · rintro ⟨X, Y, hXY⟩
          refine ⟨(ϖ * u) * Y, u * X, ?_⟩
          linear_combination (ϖ * u) * hXY
      have hhilb_eq : hilbLoc v₀ (ϖ * u) (ϖ * w) = hilbLoc v₀ (-(u * w)) (ϖ * u) := by
        simp only [hilbLoc]
        congr 1
        exact propext hequiv
      rw [hhilb_eq]
      have hvuw : Valued.v (-(u * w)) = 1 := by
        rw [Valuation.map_neg, Valuation.map_mul, hu, hw, one_mul]
      exact h_unit_unif (-(u * w)) u hvuw hu
  let HasRep (x : v₀.adicCompletion K) (a b : Bool) : Prop :=
    ∃ z u : v₀.adicCompletion K, z ≠ 0 ∧ Valued.v u = 1 ∧
      (IsSquare u ↔ a = false) ∧
      x = z ^ 2 * (if b then ϖ * u else u)
  have exists_hasRep : ∀ x : v₀.adicCompletion K, x ≠ 0 → ∃ a b : Bool, HasRep x a b := by
    intro x hx
    obtain ⟨z, u, hz, hu, hxu | hxu⟩ := hdecomp x hx
    · exact ⟨!decide (IsSquare u), false, z, u, hz, hu, by simp, hxu⟩
    · exact ⟨!decide (IsSquare u), true, z, u, hz, hu, by simp, hxu⟩
  have hasRep_isSquare_iff : ∀ (x : v₀.adicCompletion K) (a b : Bool),
      HasRep x a b → (IsSquare x ↔ (a = false ∧ b = false)) := by
    rintro x a b ⟨z, u, hz, hu, hua, rfl⟩
    have hsq_scale : ∀ w : v₀.adicCompletion K, IsSquare (z ^ 2 * w) ↔ IsSquare w := by
      intro w; constructor
      · rintro ⟨s, hs⟩; refine ⟨s / z, ?_⟩; field_simp [hz]; linear_combination hs
      · rintro ⟨s, rfl⟩; refine ⟨z * s, ?_⟩; ring
    rw [hsq_scale]
    cases b
    · simp [hua]
    · simp [(s4 u u hu hu).1]
  have hasRep_mul : ∀ (x y : v₀.adicCompletion K) (ax bx ay by_ : Bool),
      HasRep x ax bx → HasRep y ay by_ → HasRep (x * y) (xor ax ay) (xor bx by_) := by
    rintro x y ax bx ay by_ ⟨zx, ux, hzx, hux, huax, rfl⟩ ⟨zy, uy, hzy, huy, huay, rfl⟩
    refine ⟨if bx && by_ then zx * zy * ϖ else zx * zy, ux * uy, ?_, ?_, ?_, ?_⟩
    · split_ifs
      · exact mul_ne_zero (mul_ne_zero hzx hzy) hϖ0
      · exact mul_ne_zero hzx hzy
    · rw [Valuation.map_mul, hux, huy, one_mul]
    · rw [s3 ux uy hux huy, huax, huay]
      cases ax <;> cases ay <;> decide
    · cases bx <;> cases by_ <;> simp <;> ring
  obtain ⟨ε, hε⟩ : ∃ ε : Bool, (IsSquare (-1 : v₀.adicCompletion K) ↔ ε = false) :=
    ⟨!decide (IsSquare (-1 : v₀.adicCompletion K)), by simp⟩
  have hilbLoc_symm : ∀ (p q : v₀.adicCompletion K), hilbLoc v₀ p q = hilbLoc v₀ q p := by
    intro p q
    simp only [hilbLoc]
    congr 1
    exact propext ⟨fun ⟨x, y, hxy⟩ => ⟨y, x, by linear_combination hxy⟩,
      fun ⟨x, y, hxy⟩ => ⟨y, x, by linear_combination hxy⟩⟩
  have hilbLoc_scale_left : ∀ (z p q : v₀.adicCompletion K), z ≠ 0 →
      hilbLoc v₀ (z ^ 2 * p) q = hilbLoc v₀ p q := by
    intro z p q hz
    simp only [hilbLoc]
    congr 1
    refine propext ⟨?_, ?_⟩
    · rintro ⟨x, y, hxy⟩
      refine ⟨z * x, y, ?_⟩
      linear_combination hxy
    · rintro ⟨x, y, hxy⟩
      refine ⟨x / z, y, ?_⟩
      field_simp [hz]
      linear_combination hxy
  have hilbLoc_eq_iff : ∀ (p q : v₀.adicCompletion K) (b : Bool),
      (hilbLoc v₀ p q = 1 ↔ b = false) →
      hilbLoc v₀ p q = (if b then (-1 : ℤˣ) else 1) := by
    intro p q b hb
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact hb.mpr rfl
    · simp only [↓reduceIte]
      have hne : hilbLoc v₀ p q ≠ 1 := fun h => Bool.noConfusion (hb.mp h)
      simp only [hilbLoc] at hne ⊢
      split_ifs with h
      · exfalso; exact hne (if_pos h)
      · rfl
  have hasRep_hilbLoc : ∀ (x y : v₀.adicCompletion K) (ax bx ay by_ : Bool),
      HasRep x ax bx → HasRep y ay by_ →
      hilbLoc v₀ x y = (if hilbBool ε ax bx ay by_ then (-1 : ℤˣ) else 1) := by
    rintro x y ax bx ay by_ ⟨zx, ux, hzx, hux, huax, rfl⟩ ⟨zy, uy, hzy, huy, huay, rfl⟩
    rw [hilbLoc_scale_left zx _ _ hzx, hilbLoc_symm, hilbLoc_scale_left zy _ _ hzy, hilbLoc_symm]
    apply hilbLoc_eq_iff
    cases bx <;> cases by_
    · simp only [Bool.false_eq_true, ↓reduceIte, hilbBool]
      rw [s2 ux uy hux huy]
      simp
    · simp only [Bool.false_eq_true, ↓reduceIte, hilbBool]
      rw [(s4 ux uy hux huy).2.1, huax]
      cases ax <;> simp
    · simp only [Bool.false_eq_true, ↓reduceIte, hilbBool]
      rw [hilbLoc_symm, (s4 uy ux huy hux).2.1, huay]
      cases ay <;> simp
    · simp only [↓reduceIte, hilbBool]
      rw [(s4 ux uy hux huy).2.2]
      have hneg : -(ux * uy) = (-1 : v₀.adicCompletion K) * (ux * uy) := by ring
      have hv1 : Valued.v (-1 : v₀.adicCompletion K) = 1 := by
        rw [Valuation.map_neg, Valuation.map_one]
      have hvuw : Valued.v (ux * uy) = 1 := by rw [Valuation.map_mul, hux, huy, one_mul]
      rw [hneg, s3 (-1) (ux * uy) hv1 hvuw, s3 ux uy hux huy, hε, huax, huay]
      cases ε <;> cases ax <;> cases ay <;> simp
  obtain ⟨ag1, bg1, hg1_rep⟩ := exists_hasRep g₁ hg₁
  obtain ⟨ag2, bg2, hg2_rep⟩ := exists_hasRep g₂ hg₂
  obtain ⟨ah1, bh1, hh1_rep⟩ := exists_hasRep h₁ hh₁
  obtain ⟨ah2, bh2, hh2_rep⟩ := exists_hasRep h₂ hh₂
  obtain ⟨ad1, bd1, hd1_rep⟩ := exists_hasRep d₁ hd₁
  obtain ⟨ad2, bd2, hd2_rep⟩ := exists_hasRep d₂ hd₂
  have hgh1_rep := hasRep_mul g₁ h₁ ag1 bg1 ah1 bh1 hg1_rep hh1_rep
  have hgh2_rep := hasRep_mul g₂ h₂ ag2 bg2 ah2 bh2 hg2_rep hh2_rep
  have hdg1_rep := hasRep_mul d₁ g₁ ad1 bd1 ag1 bg1 hd1_rep hg1_rep
  have hdg2_rep := hasRep_mul d₂ g₂ ad2 bd2 ag2 bg2 hd2_rep hg2_rep
  have hdh1_rep := hasRep_mul d₁ h₁ ad1 bd1 ah1 bh1 hd1_rep hh1_rep
  have hdh2_rep := hasRep_mul d₂ h₂ ad2 bd2 ah2 bh2 hd2_rep hh2_rep
  have hdgh1_rep := hasRep_mul d₁ (g₁ * h₁) ad1 bd1 (xor ag1 ah1) (xor bg1 bh1) hd1_rep hgh1_rep
  have hdgh2_rep := hasRep_mul d₂ (g₂ * h₂) ad2 bd2 (xor ag2 ah2) (xor bg2 bh2) hd2_rep hgh2_rep
  rw [hasRep_isSquare_iff g₁ ag1 bg1 hg1_rep,
      hasRep_isSquare_iff g₂ ag2 bg2 hg2_rep] at hg_nsq
  rw [hasRep_isSquare_iff h₁ ah1 bh1 hh1_rep,
      hasRep_isSquare_iff h₂ ah2 bh2 hh2_rep] at hh_nsq
  rw [hasRep_isSquare_iff (g₁ * h₁) _ _ hgh1_rep,
      hasRep_isSquare_iff (g₂ * h₂) _ _ hgh2_rep] at hgh_nsq
  rw [hasRep_hilbLoc g₁ h₂ ag1 bg1 ah2 bh2 hg1_rep hh2_rep,
      hasRep_hilbLoc g₂ h₁ ag2 bg2 ah1 bh1 hg2_rep hh1_rep] at hgh_orth
  rw [hasRep_hilbLoc d₁ g₂ ad1 bd1 ag2 bg2 hd1_rep hg2_rep,
      hasRep_hilbLoc d₂ g₁ ad2 bd2 ag1 bg1 hd2_rep hg1_rep] at hdg_orth
  rw [hasRep_hilbLoc d₁ h₂ ad1 bd1 ah2 bh2 hd1_rep hh2_rep,
      hasRep_hilbLoc d₂ h₁ ad2 bd2 ah1 bh1 hd2_rep hh1_rep] at hdh_orth
  rw [hasRep_isSquare_iff d₁ ad1 bd1 hd1_rep,
      hasRep_isSquare_iff d₂ ad2 bd2 hd2_rep,
      hasRep_isSquare_iff (d₁ * g₁) _ _ hdg1_rep,
      hasRep_isSquare_iff (d₂ * g₂) _ _ hdg2_rep,
      hasRep_isSquare_iff (d₁ * h₁) _ _ hdh1_rep,
      hasRep_isSquare_iff (d₂ * h₂) _ _ hdh2_rep,
      hasRep_isSquare_iff (d₁ * (g₁ * h₁)) _ _ hdgh1_rep,
      hasRep_isSquare_iff (d₂ * (g₂ * h₂)) _ _ hdgh2_rep]
  exact h_bool_main ε ag1 bg1 ag2 bg2 ah1 bh1 ah2 bh2 ad1 bd1 ad2 bd2
    hg_nsq hh_nsq hgh_nsq hgh_orth hdg_orth hdh_orth

theorem exists_finset_classGroup_gen_disjoint {F : Type u} [Field F] [NumberField F]
    (T_avoid S_init : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (hdisj : Disjoint S_init T_avoid) :
    ∃ S_out : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
      S_init ⊆ S_out ∧ Disjoint S_out T_avoid ∧
      ∀ c : ClassGroup (NumberField.RingOfIntegers F),
        ∃ I : nonZeroDivisors (Ideal (NumberField.RingOfIntegers F)),
          ClassGroup.mk0 I = c ∧
          ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
            v ∉ T_avoid → v ∉ S_out → ¬ (v.asIdeal ∣ (I : Ideal (NumberField.RingOfIntegers F))) :=
by
  classical
  haveI : Fintype (ClassGroup (NumberField.RingOfIntegers F)) :=
    NumberField.RingOfIntegers.instFintypeClassGroup F
  choose I hI using (ClassGroup.mk0_surjective :
    Function.Surjective (ClassGroup.mk0 :
      nonZeroDivisors (Ideal (NumberField.RingOfIntegers F)) →*
        ClassGroup (NumberField.RingOfIntegers F)))
  have hfin : ∀ c : ClassGroup (NumberField.RingOfIntegers F),
      {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) |
        v.asIdeal ∣ (I c : Ideal (NumberField.RingOfIntegers F))}.Finite :=
    fun c => Ideal.finite_factors (nonZeroDivisors.coe_ne_zero (I c))
  let F_all : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :=
    Finset.univ.biUnion (fun c => (hfin c).toFinset)
  let S_out : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :=
    S_init ∪ (F_all \ T_avoid)
  refine ⟨S_out, Finset.subset_union_left,
    Finset.disjoint_union_left.mpr ⟨hdisj, Finset.sdiff_disjoint⟩, ?_⟩
  intro c
  refine ⟨I c, hI c, ?_⟩
  intro v hvT hvS hdiv
  apply hvS
  apply Finset.mem_union_right
  rw [Finset.mem_sdiff]
  refine ⟨?_, hvT⟩
  rw [Finset.mem_biUnion]
  exact ⟨c, Finset.mem_univ c, (hfin c).mem_toFinset.mpr hdiv⟩

theorem unit_sqCl_basis {F : Type u} [Field F] [NumberField F] :
    ∃ u_unit : Fin (NumberField.InfinitePlace.nrRealPlaces F +
        NumberField.InfinitePlace.nrComplexPlaces F) → Fˣ,
      (∀ i, ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
        v.valuationOfNeZero (u_unit i) = 1) ∧
      (∀ c : Fin (NumberField.InfinitePlace.nrRealPlaces F +
          NumberField.InfinitePlace.nrComplexPlaces F) → ZMod 2,
        IsSquare ((∏ i, u_unit i ^ (c i).val : Fˣ) : F) → c = 0) ∧
      (∀ x : Fˣ,
        (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
          v.valuationOfNeZero x = 1) →
        ∃ c : Fin (NumberField.InfinitePlace.nrRealPlaces F +
            NumberField.InfinitePlace.nrComplexPlaces F) → ZMod 2,
          IsSquare ((x : F) * ((∏ i, u_unit i ^ (c i).val : Fˣ) : F))) :=
by
  classical
  let ι : (NumberField.RingOfIntegers F)ˣ →* Fˣ :=
    Units.map (algebraMap (NumberField.RingOfIntegers F) F).toMonoidHom
  have hι_inj : Function.Injective ι :=
    Units.map_injective (IsFractionRing.injective (NumberField.RingOfIntegers F) F)
  have h_val_le_one : ∀ (ε : (NumberField.RingOfIntegers F)ˣ)
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
      v.valuationOfNeZero (ι ε) ≤ 1 := by
    intro ε v
    have hcoe : ((v.valuationOfNeZero (ι ε) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤
        ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
      rw [v.valuationOfNeZero_eq (ι ε)]
      change (IsDedekindDomain.HeightOneSpectrum.valuation F v)
          (algebraMap (NumberField.RingOfIntegers F) F (ε : NumberField.RingOfIntegers F)) ≤ 1
      rw [v.valuation_of_algebraMap (ε : NumberField.RingOfIntegers F)]
      exact v.intValuation_le_one (ε : NumberField.RingOfIntegers F)
    exact WithZero.coe_le_coe.mp hcoe
  have h_val : ∀ (ε : (NumberField.RingOfIntegers F)ˣ)
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
      v.valuationOfNeZero (ι ε) = 1 := by
    intro ε v
    have h1 : v.valuationOfNeZero (ι ε) ≤ 1 := h_val_le_one ε v
    have h2 : (v.valuationOfNeZero (ι ε))⁻¹ ≤ 1 := by
      rw [← map_inv, ← map_inv]
      exact h_val_le_one ε⁻¹ v
    exact le_antisymm h1 (inv_le_one'.mp h2)
  have h_lift : ∀ x : Fˣ,
      (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
        v.valuationOfNeZero x = 1) →
      ∃ ε : (NumberField.RingOfIntegers F)ˣ, ι ε = x := by
    intro x hx
    have hx_int : (x : F) ∈ (algebraMap (NumberField.RingOfIntegers F) F).range := by
      apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one F (x : F)
      intro v
      rw [← v.valuationOfNeZero_eq x, hx v]
      rfl
    have hx_inv_int : ((x⁻¹ : Fˣ) : F) ∈ (algebraMap (NumberField.RingOfIntegers F) F).range := by
      apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one F ((x⁻¹ : Fˣ) : F)
      intro v
      rw [← v.valuationOfNeZero_eq x⁻¹, map_inv, hx v, inv_one]
      rfl
    rcases hx_int with ⟨a, ha⟩
    rcases hx_inv_int with ⟨b, hb⟩
    have hab : a * b = 1 := by
      apply IsFractionRing.injective (NumberField.RingOfIntegers F) F
      rw [map_mul, map_one, ha, hb, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hba : b * a = 1 := by rw [mul_comm, hab]
    refine ⟨⟨a, b, hab, hba⟩, ?_⟩
    ext
    exact ha
  have h_sq : ∀ ε : (NumberField.RingOfIntegers F)ˣ,
      IsSquare ((ι ε : Fˣ) : F) ↔ IsSquare ε := by
    intro ε
    constructor
    · rintro ⟨s, hs⟩
      have hs_ne : s ≠ 0 := by
        rintro rfl
        exact (ι ε).ne_zero (by rw [hs, mul_zero])
      let y : Fˣ := Units.mk0 s hs_ne
      have hy_sq : y * y = ι ε := by
        ext
        exact hs.symm
      have hy_val : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
          v.valuationOfNeZero y = 1 := by
        intro v
        have hv2 : v.valuationOfNeZero y * v.valuationOfNeZero y = 1 := by
          rw [← map_mul, hy_sq, h_val ε v]
        have hadd : Multiplicative.toAdd (v.valuationOfNeZero y) +
            Multiplicative.toAdd (v.valuationOfNeZero y) = 0 := by
          rw [← toAdd_mul, hv2, toAdd_one]
        have hzero : Multiplicative.toAdd (v.valuationOfNeZero y) = 0 := by omega
        rw [← ofAdd_toAdd (v.valuationOfNeZero y), hzero, ofAdd_zero]
      obtain ⟨η, hη⟩ := h_lift y hy_val
      refine ⟨η, ?_⟩
      apply hι_inj
      rw [map_mul, hη, hy_sq]
    · rintro ⟨η, rfl⟩
      refine ⟨((ι η : Fˣ) : F), ?_⟩
      simp only [map_mul, Units.val_mul]
  obtain ⟨ζ₀, hζ_mem⟩ := IsCyclic.exists_generator (α := ↥(NumberField.Units.torsion F))
  have hζ_gen : ∀ ζ : NumberField.Units.torsion F, ∃ k : ℤ, ζ₀ ^ k = ζ :=
    fun ζ => Subgroup.mem_zpowers_iff.mp (hζ_mem ζ)
  have h_ord_even : Even (orderOf ζ₀) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ_mem, Nat.card_eq_fintype_card,
        ← NumberField.Units.torsionOrder.eq_1 F]
    exact NumberField.Units.even_torsionOrder F
  have hζ_indep : ∀ c₀ : ZMod 2,
      (∃ ζ_η : NumberField.Units.torsion F, ζ₀ ^ (c₀.val : ℤ) = ζ_η * ζ_η) → c₀ = 0 := by
    rintro c₀ ⟨ζ_η, hζ_eq⟩
    obtain ⟨k, rfl⟩ := hζ_gen ζ_η
    rcases h_ord_even with ⟨m, hm⟩
    have hzpow_one : ζ₀ ^ ((c₀.val : ℤ) - (k + k)) = 1 := by
      rw [zpow_sub, zpow_add, hζ_eq, mul_inv_cancel]
    have hdvd : (orderOf ζ₀ : ℤ) ∣ (c₀.val : ℤ) - (k + k) :=
      orderOf_dvd_iff_zpow_eq_one.mpr hzpow_one
    rw [hm] at hdvd
    rcases hdvd with ⟨q, hq⟩
    let mq : ℤ := (m : ℤ) * q
    have hq2 : (c₀.val : ℤ) - (k + k) = 2 * mq := by
      dsimp [mq]
      rw [hq]
      push_cast
      ring
    have hlt : c₀.val < 2 := ZMod.val_lt c₀
    have hval0 : c₀.val = 0 := by omega
    exact (ZMod.val_eq_zero c₀).mp hval0
  let r₀ := NumberField.Units.rank F
  let u₀ : Fin (r₀ + 1) → (NumberField.RingOfIntegers F)ˣ :=
    Fin.cons (ζ₀ : (NumberField.RingOfIntegers F)ˣ) (NumberField.Units.fundSystem F)
  have hprod_zpow : ∀ f : Fin (r₀ + 1) → ℤ,
      (∏ i : Fin (r₀ + 1), u₀ i ^ f i) =
        ((ζ₀ ^ f 0 : NumberField.Units.torsion F) : (NumberField.RingOfIntegers F)ˣ) *
          ∏ j : Fin r₀, (NumberField.Units.fundSystem F j) ^ f j.succ := by
    intro f
    rw [Fin.prod_univ_succ]
    simp only [u₀, Fin.cons_zero, Fin.cons_succ, Subgroup.coe_zpow]
  have hprod_natCast : ∀ c : Fin (r₀ + 1) → ZMod 2,
      (∏ i : Fin (r₀ + 1), u₀ i ^ (c i).val) =
        ∏ i : Fin (r₀ + 1), u₀ i ^ ((c i).val : ℤ) := by
    intro c
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [zpow_natCast]
  have hex_zpow : ∀ ε : (NumberField.RingOfIntegers F)ˣ,
      ∃ f : Fin (r₀ + 1) → ℤ, ε = ∏ i : Fin (r₀ + 1), u₀ i ^ f i := by
    intro ε
    obtain ⟨⟨ζ, e⟩, hε⟩ := (NumberField.Units.exist_unique_eq_mul_prod F ε).exists
    obtain ⟨k, rfl⟩ := hζ_gen ζ
    refine ⟨Fin.cons k e, ?_⟩
    rw [hprod_zpow]
    simpa only [Fin.cons_zero, Fin.cons_succ] using hε
  have hu₀_indep : ∀ c : Fin (r₀ + 1) → ZMod 2,
      IsSquare (∏ i : Fin (r₀ + 1), u₀ i ^ (c i).val) → c = 0 := by
    rintro c ⟨η, hη⟩
    obtain ⟨g, rfl⟩ := hex_zpow η
    have hη2 : (∏ i : Fin (r₀ + 1), u₀ i ^ g i) * (∏ i : Fin (r₀ + 1), u₀ i ^ g i) =
        ∏ i : Fin (r₀ + 1), u₀ i ^ (g i + g i) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [← zpow_add]
    let p₁ : ↥(NumberField.Units.torsion F) × (Fin r₀ → ℤ) :=
      ⟨ζ₀ ^ ((c 0).val : ℤ), fun j => ((c j.succ).val : ℤ)⟩
    let p₂ : ↥(NumberField.Units.torsion F) × (Fin r₀ → ℤ) :=
      ⟨ζ₀ ^ g 0 * ζ₀ ^ g 0, fun j => g j.succ + g j.succ⟩
    have hp₁ : (∏ i : Fin (r₀ + 1), u₀ i ^ (c i).val) =
        (p₁.1 : (NumberField.RingOfIntegers F)ˣ) *
          ∏ j : Fin r₀, NumberField.Units.fundSystem F j ^ p₁.2 j := by
      rw [hprod_natCast, hprod_zpow]
    have hp₂ : (∏ i : Fin (r₀ + 1), u₀ i ^ (c i).val) =
        (p₂.1 : (NumberField.RingOfIntegers F)ˣ) *
          ∏ j : Fin r₀, NumberField.Units.fundSystem F j ^ p₂.2 j := by
      rw [hη, hη2, hprod_zpow]
      dsimp [p₂]
      rw [← zpow_add]
    have hp_eq : p₁ = p₂ :=
      (NumberField.Units.exist_unique_eq_mul_prod F
        (∏ i : Fin (r₀ + 1), u₀ i ^ (c i).val)).unique hp₁ hp₂
    have h1 : ζ₀ ^ ((c 0).val : ℤ) = ζ₀ ^ g 0 * ζ₀ ^ g 0 := congr_arg Prod.fst hp_eq
    have h2 : (fun j : Fin r₀ => ((c j.succ).val : ℤ)) =
        (fun j : Fin r₀ => g j.succ + g j.succ) := congr_arg Prod.snd hp_eq
    have hc0 : c 0 = 0 := hζ_indep (c 0) ⟨ζ₀ ^ g 0, h1⟩
    have hcs : ∀ j : Fin r₀, c j.succ = 0 := by
      intro j
      have hj : ((c j.succ).val : ℤ) = g j.succ + g j.succ := congr_fun h2 j
      have hlt : (c j.succ).val < 2 := ZMod.val_lt (c j.succ)
      have hval0 : (c j.succ).val = 0 := by omega
      exact (ZMod.val_eq_zero (c j.succ)).mp hval0
    funext i
    exact Fin.cases hc0 hcs i
  have hu₀_span : ∀ ε : (NumberField.RingOfIntegers F)ˣ,
      ∃ c : Fin (r₀ + 1) → ZMod 2,
        IsSquare (ε * ∏ i : Fin (r₀ + 1), u₀ i ^ (c i).val) := by
    intro ε
    obtain ⟨f, rfl⟩ := hex_zpow ε
    let c : Fin (r₀ + 1) → ZMod 2 := fun i => (f i : ZMod 2)
    let d : Fin (r₀ + 1) → ℤ := fun i => (f i + ((c i).val : ℤ)) / 2
    have hfd : ∀ i : Fin (r₀ + 1), f i + ((c i).val : ℤ) = d i + d i := by
      intro i
      have hmod : ((c i).val : ℤ) = f i % (2 : ℕ) := ZMod.val_intCast (n := 2) (f i)
      dsimp [d]
      omega
    refine ⟨c, ∏ i : Fin (r₀ + 1), u₀ i ^ d i, ?_⟩
    rw [hprod_natCast, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [← zpow_add, ← zpow_add, hfd i]
  let r := NumberField.InfinitePlace.nrRealPlaces F +
    NumberField.InfinitePlace.nrComplexPlaces F
  have h_rank : r₀ + 1 = r := by
    have hcard_pos : 0 < Fintype.card (NumberField.InfinitePlace F) :=
      Fintype.card_pos_iff.mpr ⟨NumberField.Units.dirichletUnitTheorem.w₀⟩
    dsimp [r₀, r]
    rw [NumberField.Units.rank.eq_1 F, Nat.sub_add_cancel hcard_pos,
        NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F]
  let e : Fin r ≃ Fin (r₀ + 1) := finCongr h_rank.symm
  let u_unit : Fin r → Fˣ := fun i => ι (u₀ (e i))
  refine ⟨u_unit, ?_, ?_, ?_⟩
  · intro i v
    exact h_val (u₀ (e i)) v
  · intro c hsq
    let c₀ : Fin (r₀ + 1) → ZMod 2 := fun j => c (e.symm j)
    have hprod_eq : (∏ i : Fin r, u_unit i ^ (c i).val) =
        ι (∏ j : Fin (r₀ + 1), u₀ j ^ (c₀ j).val) := by
      rw [map_prod]
      dsimp [u_unit, c₀]
      rw [← Equiv.prod_comp e (fun j => ι (u₀ j ^ (c (e.symm j)).val))]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [map_pow, Equiv.symm_apply_apply]
    rw [hprod_eq, h_sq] at hsq
    have hc₀ : c₀ = 0 := hu₀_indep c₀ hsq
    funext i
    have hi := congr_fun hc₀ (e i)
    simpa [c₀] using hi
  · intro x hx
    obtain ⟨ε, rfl⟩ := h_lift x hx
    obtain ⟨c₀, hsq₀⟩ := hu₀_span ε
    let c : Fin r → ZMod 2 := fun i => c₀ (e i)
    refine ⟨c, ?_⟩
    have hprod_eq : (∏ i : Fin r, u_unit i ^ (c i).val) =
        ι (∏ j : Fin (r₀ + 1), u₀ j ^ (c₀ j).val) := by
      rw [map_prod]
      dsimp [u_unit, c]
      rw [← Equiv.prod_comp e (fun j => ι (u₀ j ^ (c₀ j).val))]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [map_pow]
    rw [hprod_eq, ← Units.val_mul, ← map_mul, h_sq]
    exact hsq₀

theorem sUnit_sqCl_basis_of_classGroup_gen {F : Type u} [Field F] [NumberField F]
    (u_unit : Fin (NumberField.InfinitePlace.nrRealPlaces F +
        NumberField.InfinitePlace.nrComplexPlaces F) → Fˣ)
    (hu_val : ∀ i, ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      v.valuationOfNeZero (u_unit i) = 1)
    (hu_indep : ∀ c : Fin (NumberField.InfinitePlace.nrRealPlaces F +
        NumberField.InfinitePlace.nrComplexPlaces F) → ZMod 2,
      IsSquare ((∏ i, u_unit i ^ (c i).val : Fˣ) : F) → c = 0)
    (hu_span : ∀ x : Fˣ,
      (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
        v.valuationOfNeZero x = 1) →
      ∃ c : Fin (NumberField.InfinitePlace.nrRealPlaces F +
          NumberField.InfinitePlace.nrComplexPlaces F) → ZMod 2,
        IsSquare ((x : F) * ((∏ i, u_unit i ^ (c i).val : Fˣ) : F)))
    (S_fin : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (hS_fin : ∀ c : ClassGroup (NumberField.RingOfIntegers F),
      ∃ I : nonZeroDivisors (Ideal (NumberField.RingOfIntegers F)),
        ClassGroup.mk0 I = c ∧
        ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
          v ∉ S_fin → ¬ (v.asIdeal ∣ (I : Ideal (NumberField.RingOfIntegers F)))) :
    ∃ g : Fin (NumberField.InfinitePlace.nrRealPlaces F +
        NumberField.InfinitePlace.nrComplexPlaces F + S_fin.card) → Fˣ,
      (∀ i, ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
        v ∉ S_fin → v.valuationOfNeZero (g i) = 1) ∧
      (∀ c : Fin (NumberField.InfinitePlace.nrRealPlaces F +
          NumberField.InfinitePlace.nrComplexPlaces F + S_fin.card) → ZMod 2,
        IsSquare ((∏ i, g i ^ (c i).val : Fˣ) : F) → c = 0) ∧
      (∀ x : Fˣ,
        (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
          v ∉ S_fin → EvenVal v x) →
        ∃ c : Fin (NumberField.InfinitePlace.nrRealPlaces F +
            NumberField.InfinitePlace.nrComplexPlaces F + S_fin.card) → ZMod 2,
          IsSquare ((x : F) * ((∏ i, g i ^ (c i).val : Fˣ) : F))) :=
by
  generalize NumberField.InfinitePlace.nrRealPlaces F +
    NumberField.InfinitePlace.nrComplexPlaces F = r at u_unit hu_val hu_indep hu_span ⊢
  classical
  have submodule_int_pi_basis_of_pi_single_mem : ∀ (s : ℕ) (Λ : Submodule ℤ (Fin s → ℤ))
      (h : ℕ) (hh : 0 < h) (hsingle : ∀ j : Fin s, Pi.single j (h : ℤ) ∈ Λ),
      ∃ b : Fin s → (Fin s → ℤ),
        (∀ j, b j ∈ Λ) ∧
        (∀ e : Fin s → ℤ, (∑ j, e j • b j) = 0 → e = 0) ∧
        (∀ d ∈ Λ, ∃ e : Fin s → ℤ, (∑ j, e j • b j) = d) := by
    intro s Λ h hh hsingle
    have hle : Module.finrank ℤ Λ ≤ s := by
      calc Module.finrank ℤ Λ ≤ Module.finrank ℤ (Fin s → ℤ) := Submodule.finrank_le Λ
        _ = s := Module.finrank_fin_fun ℤ
    have h_smul_eq : ∀ d : Fin s → ℤ, (h : ℤ) • d = ∑ j : Fin s, d j • Pi.single j (h : ℤ) := by
      intro d
      funext k
      simp [Finset.sum_apply, Pi.single_apply, mul_comm]
    have h_smul_mem : ∀ d : Fin s → ℤ, (h : ℤ) • d ∈ Λ := by
      intro d
      rw [h_smul_eq d]
      exact Submodule.sum_mem Λ (fun j _ => Submodule.smul_mem Λ (d j) (hsingle j))
    let φ : (Fin s → ℤ) →ₗ[ℤ] Λ := {
      toFun := fun d => ⟨(h : ℤ) • d, h_smul_mem d⟩
      map_add' := fun d₁ d₂ => Subtype.ext (smul_add (h : ℤ) d₁ d₂)
      map_smul' := fun c d => Subtype.ext (smul_comm (h : ℤ) c d)
    }
    have hφ_inj : Function.Injective φ := by
      intro d₁ d₂ heq
      have heq' : (h : ℤ) • d₁ = (h : ℤ) • d₂ := congr_arg Subtype.val heq
      funext j
      have hj : (h : ℤ) * d₁ j = (h : ℤ) * d₂ j := congr_fun heq' j
      have hh_ne : (h : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hh.ne'
      exact mul_left_cancel₀ hh_ne hj
    have hge : s ≤ Module.finrank ℤ Λ := by
      calc s = Module.finrank ℤ (Fin s → ℤ) := (Module.finrank_fin_fun ℤ).symm
        _ ≤ Module.finrank ℤ Λ := LinearMap.finrank_le_finrank_of_injective hφ_inj
    have hrank : Module.finrank ℤ Λ = s := le_antisymm hle hge
    let B : Module.Basis (Fin s) ℤ Λ := (Module.finBasis ℤ Λ).reindex (finCongr hrank)
    let b : Fin s → (Fin s → ℤ) := fun j => (B j : Fin s → ℤ)
    refine ⟨b, fun j => (B j).2, ?_, ?_⟩
    · intro e he
      have he' : ∑ j : Fin s, e j • B j = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        simpa [b] using he
      have hall := Fintype.linearIndependent_iff.mp B.linearIndependent e he'
      funext j
      exact hall j
    · intro d hd
      refine ⟨B.repr ⟨d, hd⟩, ?_⟩
      have hrepr := B.sum_repr ⟨d, hd⟩
      have hval := congr_arg Subtype.val hrepr
      rw [Submodule.coe_sum] at hval
      simpa [b] using hval
  have exists_sUnit_of_prime_pow_classGroup_card :
      ∃ h : ℕ, 0 < h ∧
        ∀ v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
          ∃ u : Fˣ,
            Multiplicative.toAdd (v₀.valuationOfNeZero u) = (h : ℤ) ∧
            ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
              v ≠ v₀ → v.valuationOfNeZero u = 1 := by
    let h := Fintype.card (ClassGroup (NumberField.RingOfIntegers F))
    have hh : 0 < h := Fintype.card_pos
    refine ⟨h, hh, fun v₀ => ?_⟩
    have hv₀_nzd : v₀.asIdeal ∈ nonZeroDivisors (Ideal (NumberField.RingOfIntegers F)) :=
      mem_nonZeroDivisors_of_ne_zero v₀.ne_bot
    have hv₀h_ne : v₀.asIdeal ^ h ≠ 0 := pow_ne_zero h v₀.ne_bot
    have hv₀h_nzd : v₀.asIdeal ^ h ∈ nonZeroDivisors (Ideal (NumberField.RingOfIntegers F)) :=
      mem_nonZeroDivisors_of_ne_zero hv₀h_ne
    have hmk0_eq : (⟨v₀.asIdeal ^ h, hv₀h_nzd⟩ : nonZeroDivisors (Ideal (NumberField.RingOfIntegers F))) =
        (⟨v₀.asIdeal, hv₀_nzd⟩ : nonZeroDivisors (Ideal (NumberField.RingOfIntegers F))) ^ h := by
      ext
      rfl
    have hcl_one : ClassGroup.mk0 ⟨v₀.asIdeal ^ h, hv₀h_nzd⟩ = 1 := by
      rw [hmk0_eq, map_pow, pow_card_eq_one]
    have hprin : (v₀.asIdeal ^ h).IsPrincipal := (ClassGroup.mk0_eq_one_iff hv₀h_nzd).mp hcl_one
    let a : NumberField.RingOfIntegers F := Submodule.IsPrincipal.generator (v₀.asIdeal ^ h)
    have ha_span : Ideal.span {a} = v₀.asIdeal ^ h :=
      Submodule.IsPrincipal.span_singleton_generator (v₀.asIdeal ^ h)
    have ha_ne : a ≠ 0 := by
      intro ha0
      rw [ha0, Ideal.span_singleton_zero] at ha_span
      exact hv₀h_ne ha_span.symm
    have ha_F : algebraMap (NumberField.RingOfIntegers F) F a ≠ 0 :=
      (map_ne_zero_iff (algebraMap (NumberField.RingOfIntegers F) F)
        (IsFractionRing.injective (NumberField.RingOfIntegers F) F)).mpr ha_ne
    let u₀ : Fˣ := Units.mk0 (algebraMap (NumberField.RingOfIntegers F) F a) ha_F
    let u : Fˣ := u₀⁻¹
    have hp₀_ne : Associates.mk v₀.asIdeal ≠ 0 := Associates.mk_ne_zero.mpr v₀.ne_bot
    have hp₀_irr : Irreducible (Associates.mk v₀.asIdeal) :=
      Associates.irreducible_mk.mpr v₀.prime.irreducible
    have hu₀_val_eq : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
        (v.valuationOfNeZero u₀ : WithZero (Multiplicative ℤ)) = v.intValuation a := by
      intro v
      rw [v.valuationOfNeZero_eq u₀]
      exact v.valuation_of_algebraMap a
    refine ⟨u, ?_, ?_⟩
    · have hv₀_int : v₀.intValuation a = WithZero.exp (-(h : ℤ)) := by
        rw [v₀.intValuation_if_neg ha_ne, ha_span, Associates.mk_pow,
            Associates.count_pow hp₀_ne hp₀_irr, Associates.count_self hp₀_irr, mul_one]
      have hv₀_u₀ : v₀.valuationOfNeZero u₀ = Multiplicative.ofAdd (-(h : ℤ)) := by
        apply WithZero.coe_inj.mp
        rw [hu₀_val_eq v₀, hv₀_int]
        rfl
      have hv₀_u : v₀.valuationOfNeZero u = Multiplicative.ofAdd (h : ℤ) := by
        dsimp [u]
        rw [map_inv, hv₀_u₀, ← ofAdd_neg, neg_neg]
      rw [hv₀_u, toAdd_ofAdd]
    · intro v hv
      have hp_irr : Irreducible (Associates.mk v.asIdeal) :=
        Associates.irreducible_mk.mpr v.prime.irreducible
      have hp_ne : Associates.mk v.asIdeal ≠ Associates.mk v₀.asIdeal := by
        intro heq
        have hassoc : Associated v.asIdeal v₀.asIdeal := Associates.mk_eq_mk_iff_associated.mp heq
        have hideal : v.asIdeal = v₀.asIdeal := associated_iff_eq.mp hassoc
        exact hv (IsDedekindDomain.HeightOneSpectrum.ext hideal)
      have hv_int : v.intValuation a = 1 := by
        rw [v.intValuation_if_neg ha_ne, ha_span, Associates.mk_pow,
            Associates.count_pow hp₀_ne hp_irr,
            Associates.count_eq_zero_of_ne hp_irr hp₀_irr hp_ne, mul_zero]
        rfl
      have hv_u₀ : v.valuationOfNeZero u₀ = 1 := by
        apply WithZero.coe_inj.mp
        rw [hu₀_val_eq v, hv_int]
        rfl
      dsimp [u]
      rw [map_inv, hv_u₀, inv_one]
  have exists_sUnit_mul_isSquare_of_evenVal :
      ∀ (x : Fˣ),
        (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
          v ∉ S_fin → EvenVal v x) →
        ∃ u : Fˣ,
          (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
            v ∉ S_fin → v.valuationOfNeZero u = 1) ∧
          IsSquare ((x : F) * (u : F)) := by
    intro x hx
    obtain ⟨a, b, hb_mem, hab⟩ :=
      IsFractionRing.div_surjective (A := NumberField.RingOfIntegers F) (x : F)
    have hb_ne : b ≠ 0 := nonZeroDivisors.ne_zero hb_mem
    have hinj : Function.Injective (algebraMap (NumberField.RingOfIntegers F) F) :=
      IsFractionRing.injective (NumberField.RingOfIntegers F) F
    have hb_F : algebraMap (NumberField.RingOfIntegers F) F b ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr hb_ne
    have ha_ne : a ≠ 0 := by
      intro ha0
      apply x.ne_zero
      rw [← hab, ha0, map_zero, zero_div]
    let r₀ : NumberField.RingOfIntegers F := a * b
    have hr₀_ne : r₀ ≠ 0 := mul_ne_zero ha_ne hb_ne
    have hr₀_F_ne : algebraMap (NumberField.RingOfIntegers F) F r₀ ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr hr₀_ne
    have ha_F_eq : algebraMap (NumberField.RingOfIntegers F) F a =
        (x : F) * algebraMap (NumberField.RingOfIntegers F) F b :=
      (div_eq_iff hb_F).mp hab
    have hr₀_F : algebraMap (NumberField.RingOfIntegers F) F r₀ =
        (x : F) * (algebraMap (NumberField.RingOfIntegers F) F b) ^ 2 := by
      dsimp [r₀]
      rw [map_mul, ha_F_eq]
      ring
    let I₀ : Ideal (NumberField.RingOfIntegers F) := Ideal.span {r₀}
    have hI₀_ne : I₀ ≠ 0 := by
      rw [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]
      exact hr₀_ne
    let N : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) → ℕ :=
      fun v => (Associates.mk v.asIdeal).count (Associates.mk I₀).factors
    let K_b : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) → ℕ :=
      fun v => (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {b})).factors
    have hN_even : ∀ v ∉ S_fin, N v = 2 * (N v / 2) := by
      intro v hv
      have hr₀_val : (IsDedekindDomain.HeightOneSpectrum.valuation F v)
          (algebraMap (NumberField.RingOfIntegers F) F r₀) = WithZero.exp (-(N v : ℤ)) := by
        rw [v.valuation_of_algebraMap r₀, v.intValuation_if_neg hr₀_ne]
      have hb_val : (IsDedekindDomain.HeightOneSpectrum.valuation F v)
          (algebraMap (NumberField.RingOfIntegers F) F b) = WithZero.exp (-(K_b v : ℤ)) := by
        rw [v.valuation_of_algebraMap b, v.intValuation_if_neg hb_ne]
      have hx_val : (IsDedekindDomain.HeightOneSpectrum.valuation F v) (x : F) =
          WithZero.exp (Multiplicative.toAdd (v.valuationOfNeZero x)) := by
        rw [← v.valuationOfNeZero_eq x]
        rfl
      have hval_eq : WithZero.exp (-(N v : ℤ)) =
          WithZero.exp (Multiplicative.toAdd (v.valuationOfNeZero x) +
            (-(K_b v : ℤ) + -(K_b v : ℤ))) := by
        rw [← hr₀_val, hr₀_F, map_mul, sq, map_mul, hx_val, hb_val,
            ← WithZero.exp_add, ← WithZero.exp_add]
      have hexp_eq : -(N v : ℤ) =
          Multiplicative.toAdd (v.valuationOfNeZero x) + (-(K_b v : ℤ) + -(K_b v : ℤ)) :=
        WithZero.exp_inj.mp hval_eq
      rcases hx v hv with ⟨k, hk⟩
      omega
    let F₀ := (Ideal.finite_factors hI₀_ne).toFinset
    let D := F₀ \ S_fin
    have hsupp : Function.mulSupport
        (fun v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) =>
          v.maxPowDividing I₀) ⊆
        ((D ∪ S_fin : Finset _) : Set _) := by
      intro v hv
      rw [Function.mem_mulSupport] at hv
      by_contra hv_not
      rw [Finset.mem_coe, Finset.mem_union, Finset.mem_sdiff] at hv_not
      have hvF₀ : v ∉ F₀ := fun h => hv_not (by tauto)
      have hndvd : ¬ (v.asIdeal ∣ I₀) := by
        simpa [F₀, Set.Finite.mem_toFinset] using hvF₀
      have hN0 : N v = 0 := by
        by_contra hne
        exact hndvd ((Associates.count_ne_zero_iff_dvd hI₀_ne v.prime.irreducible).mp hne)
      apply hv
      change v.asIdeal ^ N v = 1
      rw [hN0, pow_zero]
    let J : Ideal (NumberField.RingOfIntegers F) := ∏ v ∈ D, v.asIdeal ^ (N v / 2)
    let I_in : Ideal (NumberField.RingOfIntegers F) := ∏ v ∈ S_fin, v.asIdeal ^ (N v)
    have hI₀_eq : I₀ = J ^ 2 * I_in := by
      have hfact := (Ideal.finprod_heightOneSpectrum_factorization hI₀_ne).symm
      rw [finprod_eq_prod_of_mulSupport_subset _ hsupp,
          Finset.prod_union Finset.sdiff_disjoint] at hfact
      have hD_eq : (∏ v ∈ D, v.maxPowDividing I₀) = J ^ 2 := by
        dsimp [J]
        rw [← Finset.prod_pow]
        refine Finset.prod_congr rfl (fun v hv => ?_)
        have hvS : v ∉ S_fin := (Finset.mem_sdiff.mp hv).2
        change v.asIdeal ^ (N v) = (v.asIdeal ^ (N v / 2)) ^ 2
        rw [← pow_mul', ← hN_even v hvS]
      exact hfact.trans (by rw [hD_eq]; rfl)
    have prod_ne_zero : ∀ (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
        (f : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) → ℕ),
        (∏ v ∈ S, v.asIdeal ^ (f v)) ≠ 0 := by
      intro S f
      induction S using Finset.induction_on with
      | empty => simp
      | @insert v s hv ih =>
        rw [Finset.prod_insert hv]
        exact mul_ne_zero (pow_ne_zero (f v) v.ne_bot) ih
    have hJ_ne : J ≠ 0 := prod_ne_zero D (fun v => N v / 2)
    have hI_in_ne : I_in ≠ 0 := prod_ne_zero S_fin N
    let J_nzd : nonZeroDivisors (Ideal (NumberField.RingOfIntegers F)) :=
      ⟨J, mem_nonZeroDivisors_of_ne_zero hJ_ne⟩
    obtain ⟨I_c, hIc_cl, hIc_div⟩ := hS_fin (ClassGroup.mk0 J_nzd)⁻¹
    have hJIc_one : ClassGroup.mk0 (J_nzd * I_c) = 1 := by
      rw [map_mul, hIc_cl, mul_inv_cancel]
    have hJIc_prin : (J * (I_c : Ideal (NumberField.RingOfIntegers F))).IsPrincipal :=
      (ClassGroup.mk0_eq_one_iff (J_nzd * I_c).2).mp hJIc_one
    let y : NumberField.RingOfIntegers F :=
      Submodule.IsPrincipal.generator (J * (I_c : Ideal (NumberField.RingOfIntegers F)))
    have hy_span : Ideal.span {y} = J * (I_c : Ideal (NumberField.RingOfIntegers F)) :=
      Submodule.IsPrincipal.span_singleton_generator (J * (I_c : Ideal (NumberField.RingOfIntegers F)))
    have hy2_span : Ideal.span {y ^ 2} = J ^ 2 * (I_c : Ideal (NumberField.RingOfIntegers F)) ^ 2 := by
      rw [← Ideal.span_singleton_pow, hy_span, mul_pow]
    have hIc_ne : (I_c : Ideal (NumberField.RingOfIntegers F)) ≠ 0 := nonZeroDivisors.coe_ne_zero I_c
    have hy_ne : y ≠ 0 := by
      intro hy0
      rw [hy0, Ideal.span_singleton_zero] at hy_span
      exact mul_ne_zero hJ_ne hIc_ne hy_span.symm
    have hy2_ne : y ^ 2 ≠ 0 := pow_ne_zero 2 hy_ne
    have hy2_F_ne : algebraMap (NumberField.RingOfIntegers F) F (y ^ 2) ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr hy2_ne
    have hy_F_ne : algebraMap (NumberField.RingOfIntegers F) F y ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr hy_ne
    let u_r₀ : Fˣ := Units.mk0 (algebraMap (NumberField.RingOfIntegers F) F r₀) hr₀_F_ne
    let u_y2 : Fˣ := Units.mk0 (algebraMap (NumberField.RingOfIntegers F) F (y ^ 2)) hy2_F_ne
    let u : Fˣ := u_r₀ * u_y2⁻¹
    refine ⟨u, ?_, ?_⟩
    · intro v hv
      have hnot_dvd_in : ¬ (v.asIdeal ∣ I_in) := by
        intro hdvd
        obtain ⟨w, hwS, hvw_pow⟩ := v.prime.exists_mem_finset_dvd hdvd
        have hvw_dvd : v.asIdeal ∣ w.asIdeal := v.prime.dvd_of_dvd_pow hvw_pow
        have hvw_le : w.asIdeal ≤ v.asIdeal := Ideal.dvd_iff_le.mp hvw_dvd
        have hvw_eq : w.asIdeal = v.asIdeal := w.isMaximal.eq_of_le v.isPrime.ne_top hvw_le
        have hwv : w = v := IsDedekindDomain.HeightOneSpectrum.ext hvw_eq
        exact hv (hwv ▸ hwS)
      have hnot_dvd_Ic2 : ¬ (v.asIdeal ∣ (I_c : Ideal (NumberField.RingOfIntegers F)) ^ 2) := by
        intro hdvd
        exact hIc_div v hv (v.prime.dvd_of_dvd_pow hdvd)
      have hJ2_mk_ne : Associates.mk (J ^ 2) ≠ 0 := Associates.mk_ne_zero.mpr (pow_ne_zero 2 hJ_ne)
      have hI_in_mk_ne : Associates.mk I_in ≠ 0 := Associates.mk_ne_zero.mpr hI_in_ne
      have hIc2_ne : (I_c : Ideal (NumberField.RingOfIntegers F)) ^ 2 ≠ 0 := pow_ne_zero 2 hIc_ne
      have hIc2_mk_ne : Associates.mk ((I_c : Ideal (NumberField.RingOfIntegers F)) ^ 2) ≠ 0 :=
        Associates.mk_ne_zero.mpr hIc2_ne
      have hp_irr : Irreducible (Associates.mk v.asIdeal) :=
        Associates.irreducible_mk.mpr v.prime.irreducible
      have hcount_in : (Associates.mk v.asIdeal).count (Associates.mk I_in).factors = 0 := by
        by_contra hne
        exact hnot_dvd_in ((Associates.count_ne_zero_iff_dvd hI_in_ne v.prime.irreducible).mp hne)
      have hcount_Ic2 : (Associates.mk v.asIdeal).count
          (Associates.mk ((I_c : Ideal (NumberField.RingOfIntegers F)) ^ 2)).factors = 0 := by
        by_contra hne
        exact hnot_dvd_Ic2 ((Associates.count_ne_zero_iff_dvd hIc2_ne v.prime.irreducible).mp hne)
      have hcount_eq : (Associates.mk v.asIdeal).count (Associates.mk I₀).factors =
          (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {y ^ 2})).factors := by
        rw [hI₀_eq, hy2_span, ← Associates.mk_mul_mk, ← Associates.mk_mul_mk,
            Associates.count_mul hJ2_mk_ne hI_in_mk_ne hp_irr,
            Associates.count_mul hJ2_mk_ne hIc2_mk_ne hp_irr,
            hcount_in, hcount_Ic2]
      have hint_eq : v.intValuation r₀ = v.intValuation (y ^ 2) := by
        rw [v.intValuation_if_neg hr₀_ne, v.intValuation_if_neg hy2_ne]
        exact congr_arg WithZero.exp (congr_arg Neg.neg (congr_arg Nat.cast hcount_eq))
      have hu_r₀_val : v.valuationOfNeZero u_r₀ = v.valuationOfNeZero u_y2 := by
        apply WithZero.coe_inj.mp
        rw [v.valuationOfNeZero_eq u_r₀, v.valuationOfNeZero_eq u_y2]
        change (IsDedekindDomain.HeightOneSpectrum.valuation F v)
            (algebraMap (NumberField.RingOfIntegers F) F r₀) =
          (IsDedekindDomain.HeightOneSpectrum.valuation F v)
            (algebraMap (NumberField.RingOfIntegers F) F (y ^ 2))
        rw [v.valuation_of_algebraMap r₀, v.valuation_of_algebraMap (y ^ 2), hint_eq]
      dsimp [u]
      rw [map_mul, map_inv, hu_r₀_val, mul_inv_cancel]
    · refine ⟨(x : F) * algebraMap (NumberField.RingOfIntegers F) F b /
        algebraMap (NumberField.RingOfIntegers F) F y, ?_⟩
      have hu_val : (u : F) = algebraMap (NumberField.RingOfIntegers F) F r₀ /
          (algebraMap (NumberField.RingOfIntegers F) F y) ^ 2 := by
        change algebraMap (NumberField.RingOfIntegers F) F r₀ *
          (algebraMap (NumberField.RingOfIntegers F) F (y ^ 2))⁻¹ = _
        rw [map_pow, div_eq_mul_inv]
      rw [hu_val, hr₀_F]
      field_simp [hy_F_ne]
  let s := S_fin.card
  let e_S : Fin s ≃ S_fin := S_fin.equivFin.symm
  let ν : Fˣ → (Fin s → ℤ) :=
    fun x j => Multiplicative.toAdd ((e_S j).1.valuationOfNeZero x)
  have hν_one : ν 1 = 0 := by
    funext j
    dsimp [ν]
    rw [map_one, toAdd_one]
  have hν_mul : ∀ x y : Fˣ, ν (x * y) = ν x + ν y := by
    intro x y
    funext j
    dsimp [ν]
    rw [map_mul, toAdd_mul]
  have hν_inv : ∀ x : Fˣ, ν x⁻¹ = - ν x := by
    intro x
    funext j
    dsimp [ν]
    rw [map_inv, toAdd_inv]
  have hν_zpow : ∀ (x : Fˣ) (n : ℤ), ν (x ^ n) = n • ν x := by
    intro x n
    funext j
    dsimp [ν]
    rw [map_zpow, toAdd_zpow]
    rfl
  have hν_npow : ∀ (x : Fˣ) (n : ℕ), ν (x ^ n) = (n : ℤ) • ν x := by
    intro x n
    rw [← zpow_natCast, hν_zpow]
  have hν_prod : ∀ {α : Type} (S : Finset α) (f : α → Fˣ),
      ν (∏ j ∈ S, f j) = ∑ j ∈ S, ν (f j) := by
    intro α S f
    induction S using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.sum_empty, hν_one]
    | @insert j s' hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, hν_mul, ih]
  have hex_g_fin : ∃ (b : Fin s → (Fin s → ℤ)) (g_fin : Fin s → Fˣ),
      (∀ j, ∀ v ∉ S_fin, v.valuationOfNeZero (g_fin j) = 1) ∧
      (∀ j, ν (g_fin j) = b j) ∧
      (∀ e : Fin s → ℤ, (∑ j, e j • b j) = 0 → e = 0) ∧
      (∀ u : Fˣ, (∀ v ∉ S_fin, v.valuationOfNeZero u = 1) →
        ∃ e : Fin s → ℤ, (∑ j, e j • b j) = ν u) := by
    let Λ : Submodule ℤ (Fin s → ℤ) := {
      carrier := { d | ∃ u : Fˣ, (∀ v ∉ S_fin, v.valuationOfNeZero u = 1) ∧ ν u = d }
      zero_mem' := ⟨1, fun v _ => map_one _, hν_one⟩
      add_mem' := by
        rintro d₁ d₂ ⟨u₁, hu₁_val, rfl⟩ ⟨u₂, hu₂_val, rfl⟩
        refine ⟨u₁ * u₂, fun v hv => ?_, hν_mul u₁ u₂⟩
        rw [map_mul, hu₁_val v hv, hu₂_val v hv, mul_one]
      smul_mem' := by
        rintro n d ⟨u, hu_val, rfl⟩
        refine ⟨u ^ n, fun v hv => ?_, hν_zpow u n⟩
        rw [map_zpow, hu_val v hv, one_zpow]
    }
    obtain ⟨h, hh, h_single_u⟩ := exists_sUnit_of_prime_pow_classGroup_card
    have hsingle : ∀ j : Fin s, Pi.single j (h : ℤ) ∈ Λ := by
      intro j
      obtain ⟨u_j, hu_j_eq, hu_j_ne⟩ := h_single_u (e_S j).1
      refine ⟨u_j, fun v hv => hu_j_ne v (fun hveq => hv (hveq ▸ (e_S j).2)), ?_⟩
      funext k
      dsimp [ν]
      by_cases hkj : k = j
      · subst hkj
        rw [hu_j_eq, Pi.single_eq_same]
      · have hvk : (e_S k).1 ≠ (e_S j).1 := fun heq => hkj (e_S.injective (Subtype.ext heq))
        rw [hu_j_ne (e_S k).1 hvk, toAdd_one, Pi.single_eq_of_ne hkj]
    obtain ⟨b, hb_mem, hb_indep, hb_span⟩ :=
      submodule_int_pi_basis_of_pi_single_mem s Λ h hh hsingle
    choose g_fin hg_fin_val hg_fin_ν using hb_mem
    exact ⟨b, g_fin, hg_fin_val, hg_fin_ν, hb_indep, fun u hu => hb_span (ν u) ⟨u, hu, rfl⟩⟩
  obtain ⟨b, g_fin, hg_fin_val, hg_fin_ν, hb_indep, hb_span⟩ := hex_g_fin
  let g : Fin (r + s) → Fˣ := Fin.append u_unit g_fin
  have hg_val_out : ∀ i : Fin (r + s), ∀ v ∉ S_fin, v.valuationOfNeZero (g i) = 1 := by
    intro i v hv
    refine Fin.addCases (fun i₁ => ?_) (fun j => ?_) i
    · dsimp [g]
      rw [Fin.append_left]
      exact hu_val i₁ v
    · dsimp [g]
      rw [Fin.append_right]
      exact hg_fin_val j v hv
  have hν_u_unit : ∀ i : Fin r, ν (u_unit i) = 0 := by
    intro i
    funext j
    dsimp [ν]
    rw [hu_val i (e_S j).1, toAdd_one]
  refine ⟨g, hg_val_out, ?_, ?_⟩
  · intro c hsq
    let c₁ : Fin r → ZMod 2 := fun i => c (Fin.castAdd s i)
    let c₂ : Fin s → ZMod 2 := fun j => c (Fin.natAdd r j)
    have hprod_split : (∏ m : Fin (r + s), g m ^ (c m).val) =
        (∏ i : Fin r, u_unit i ^ (c₁ i).val) * (∏ j : Fin s, g_fin j ^ (c₂ j).val) := by
      rw [Fin.prod_univ_add]
      refine congr_arg₂ (· * ·) ?_ ?_
      · refine Finset.prod_congr rfl (fun i _ => ?_)
        dsimp [g, c₁]
        rw [Fin.append_left]
      · refine Finset.prod_congr rfl (fun j _ => ?_)
        dsimp [g, c₂]
        rw [Fin.append_right]
    rcases hsq with ⟨y₀, hy₀⟩
    have hy₀_ne : y₀ ≠ 0 := by
      intro hy₀0
      apply Units.ne_zero (∏ m : Fin (r + s), g m ^ (c m).val)
      rw [hy₀, hy₀0, mul_zero]
    let y : Fˣ := Units.mk0 y₀ hy₀_ne
    have hy_eq : (∏ i : Fin r, u_unit i ^ (c₁ i).val) * (∏ j : Fin s, g_fin j ^ (c₂ j).val) =
        y * y := by
      ext
      rw [← hprod_split]
      exact hy₀
    have hy_val_out : ∀ v ∉ S_fin, v.valuationOfNeZero y = 1 := by
      intro v hv
      have hprod_val : v.valuationOfNeZero (∏ m : Fin (r + s), g m ^ (c m).val) = 1 := by
        rw [map_prod]
        refine Finset.prod_eq_one (fun m _ => ?_)
        rw [map_pow, hg_val_out m v hv, one_pow]
      have hy2_val : v.valuationOfNeZero (y * y) = 1 := by
        rw [← hy_eq, ← hprod_split, hprod_val]
      have htoAdd : 2 * Multiplicative.toAdd (v.valuationOfNeZero y) = 0 := by
        have h1 : Multiplicative.toAdd (v.valuationOfNeZero (y * y)) = 0 := by
          rw [hy2_val, toAdd_one]
        rw [map_mul, toAdd_mul] at h1
        omega
      have htoAdd0 : Multiplicative.toAdd (v.valuationOfNeZero y) = 0 := by omega
      exact Multiplicative.toAdd.injective (htoAdd0.trans toAdd_one.symm)
    obtain ⟨e, he⟩ := hb_span y hy_val_out
    have hν_lhs1 : ν (∏ i : Fin r, u_unit i ^ (c₁ i).val) = 0 := by
      rw [hν_prod]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [hν_npow, hν_u_unit i, smul_zero]
    have hν_lhs2 : ν (∏ j : Fin s, g_fin j ^ (c₂ j).val) =
        ∑ j : Fin s, ((c₂ j).val : ℤ) • b j := by
      rw [hν_prod]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hν_npow, hg_fin_ν j]
    have hν_eq : ∑ j : Fin s, ((c₂ j).val : ℤ) • b j =
        ∑ j : Fin s, (2 * e j) • b j := by
      have h1 := congr_arg ν hy_eq
      rw [hν_mul, hν_lhs1, hν_lhs2, zero_add, hν_mul, ← he, ← Finset.sum_add_distrib] at h1
      refine h1.trans (Finset.sum_congr rfl (fun j _ => ?_))
      rw [← add_smul, two_mul]
    have hν_sub : ∑ j : Fin s, (((c₂ j).val : ℤ) - 2 * e j) • b j = 0 := by
      have hsub_eq : (∑ j : Fin s, (((c₂ j).val : ℤ) - 2 * e j) • b j) =
          (∑ j : Fin s, ((c₂ j).val : ℤ) • b j) - (∑ j : Fin s, (2 * e j) • b j) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun j _ => sub_smul _ _ _)
      rw [hsub_eq, hν_eq, sub_self]
    have hcoeff_zero := hb_indep (fun j => ((c₂ j).val : ℤ) - 2 * e j) hν_sub
    have hc₂ : c₂ = 0 := by
      funext j
      have hj : ((c₂ j).val : ℤ) - 2 * e j = 0 := congr_fun hcoeff_zero j
      have hlt : (c₂ j).val < 2 := ZMod.val_lt (c₂ j)
      have hval0 : (c₂ j).val = 0 := by omega
      exact (ZMod.val_eq_zero (c₂ j)).mp hval0
    have hprod2_one : (∏ j : Fin s, g_fin j ^ (c₂ j).val) = 1 := by
      refine Finset.prod_eq_one (fun j _ => ?_)
      rw [hc₂, Pi.zero_apply, ZMod.val_zero, pow_zero]
    have hc₁_sq : IsSquare ((∏ i : Fin r, u_unit i ^ (c₁ i).val : Fˣ) : F) := by
      refine ⟨(y : F), ?_⟩
      have hy_eq' := congr_arg (Units.val : Fˣ → F) hy_eq
      rw [hprod2_one, mul_one, Units.val_mul] at hy_eq'
      exact hy_eq'
    have hc₁ : c₁ = 0 := hu_indep c₁ hc₁_sq
    funext m
    refine Fin.addCases (fun i => ?_) (fun j => ?_) m
    · exact congr_fun hc₁ i
    · exact congr_fun hc₂ j
  · intro x hx
    obtain ⟨u, hu_val_out, hxu_sq⟩ := exists_sUnit_mul_isSquare_of_evenVal x hx
    obtain ⟨e, he⟩ := hb_span u hu_val_out
    let c₂ : Fin s → ZMod 2 := fun j => (e j : ZMod 2)
    let k : Fin s → ℤ := fun j => (e j + ((c₂ j).val : ℤ)) / 2
    have hk : ∀ j : Fin s, e j + ((c₂ j).val : ℤ) = 2 * k j := by
      intro j
      have hmod : ((c₂ j).val : ℤ) = e j % 2 := ZMod.val_intCast (e j)
      dsimp [k]
      omega
    let w : Fˣ := ∏ j : Fin s, g_fin j ^ (k j)
    let u₀ : Fˣ := u * (∏ j : Fin s, g_fin j ^ (c₂ j).val) * (w * w)⁻¹
    have hu₀_val_all : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
        v.valuationOfNeZero u₀ = 1 := by
      intro v
      by_cases hv : v ∈ S_fin
      · let j : Fin s := S_fin.equivFin ⟨v, hv⟩
        have heS_j : (e_S j).1 = v := by
          dsimp [e_S, j]
          exact congr_arg Subtype.val (S_fin.equivFin.symm_apply_apply ⟨v, hv⟩)
        have hν_w : ν w = ∑ l : Fin s, (k l) • b l := by
          dsimp [w]
          rw [hν_prod]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [hν_zpow, hg_fin_ν l]
        have hν_c2 : ν (∏ l : Fin s, g_fin l ^ (c₂ l).val) =
            ∑ l : Fin s, ((c₂ l).val : ℤ) • b l := by
          rw [hν_prod]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [hν_npow, hg_fin_ν l]
        have hν_u₀ : ν u₀ = 0 := by
          dsimp [u₀]
          rw [hν_mul, hν_mul, hν_inv, hν_mul, ← he, hν_c2, hν_w]
          ext m
          simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply, Finset.sum_apply, Pi.smul_apply,
            smul_eq_mul]
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
              ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
          refine Finset.sum_eq_zero (fun l _ => ?_)
          linear_combination (b l m) * (hk l)
        have htoAdd : Multiplicative.toAdd (v.valuationOfNeZero u₀) = 0 := by
          rw [← heS_j]
          exact congr_fun hν_u₀ j
        exact Multiplicative.toAdd.injective (htoAdd.trans toAdd_one.symm)
      · have hw_val : v.valuationOfNeZero w = 1 := by
          dsimp [w]
          rw [map_prod]
          refine Finset.prod_eq_one (fun l _ => ?_)
          rw [map_zpow, hg_fin_val l v hv, one_zpow]
        have hc2_val : v.valuationOfNeZero (∏ l : Fin s, g_fin l ^ (c₂ l).val) = 1 := by
          rw [map_prod]
          refine Finset.prod_eq_one (fun l _ => ?_)
          rw [map_pow, hg_fin_val l v hv, one_pow]
        dsimp [u₀]
        rw [map_mul, map_mul, map_inv, map_mul, hu_val_out v hv, hc2_val, hw_val,
            mul_one, inv_one, mul_one]
    obtain ⟨c₁, hc₁_sq⟩ := hu_span u₀ hu₀_val_all
    let c : Fin (r + s) → ZMod 2 := Fin.append c₁ c₂
    have hprod_split : (∏ m : Fin (r + s), g m ^ (c m).val) =
        (∏ i : Fin r, u_unit i ^ (c₁ i).val) * (∏ j : Fin s, g_fin j ^ (c₂ j).val) := by
      rw [Fin.prod_univ_add]
      refine congr_arg₂ (· * ·) ?_ ?_
      · refine Finset.prod_congr rfl (fun i _ => ?_)
        dsimp [g, c]
        rw [Fin.append_left, Fin.append_left]
      · refine Finset.prod_congr rfl (fun j _ => ?_)
        dsimp [g, c]
        rw [Fin.append_right, Fin.append_right]
    refine ⟨c, ?_⟩
    rcases hxu_sq with ⟨s₁, hs₁⟩
    rcases hc₁_sq with ⟨s₂, hs₂⟩
    have hu_F_ne : (u : F) ≠ 0 := u.ne_zero
    have hw_F_ne : (w : F) ≠ 0 := w.ne_zero
    refine ⟨s₁ * s₂ * (w : F) / (u : F), ?_⟩
    have hu₀_val : (u₀ : F) = (u : F) * ((∏ j : Fin s, g_fin j ^ (c₂ j).val : Fˣ) : F) *
        ((w : F) * (w : F))⁻¹ := by
      dsimp [u₀]
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    rw [hprod_split, Units.val_mul]
    have h1 : (s₁ * s₁) * (s₂ * s₂) =
        ((x : F) * (u : F)) * ((u₀ : F) * ((∏ i : Fin r, u_unit i ^ (c₁ i).val : Fˣ) : F)) := by
      rw [← hs₁, ← hs₂]
    rw [hu₀_val] at h1
    calc (x : F) * (((∏ i : Fin r, u_unit i ^ (c₁ i).val : Fˣ) : F) *
          ((∏ j : Fin s, g_fin j ^ (c₂ j).val : Fˣ) : F))
      _ = ((x : F) * (u : F)) *
            ((u : F) * ((∏ j : Fin s, g_fin j ^ (c₂ j).val : Fˣ) : F) * ((w : F) * (w : F))⁻¹ *
              ((∏ i : Fin r, u_unit i ^ (c₁ i).val : Fˣ) : F)) *
            ((w : F) * (w : F)) / ((u : F) * (u : F)) := by
          field_simp [hu_F_ne, hw_F_ne]
      _ = (s₁ * s₁) * (s₂ * s₂) * ((w : F) * (w : F)) / ((u : F) * (u : F)) := by
          rw [← h1]
      _ = (s₁ * s₂ * (w : F) / (u : F)) * (s₁ * s₂ * (w : F) / (u : F)) := by
          ring

theorem isSquare_everywhere_of_isSquare_on_sFin {K : Type u} [Field K] [NumberField K]
    (a₁ a₂ a₃ : K) (h₁₂ : a₁ ≠ a₂) (h₁₃ : a₁ ≠ a₃) (h₂₃ : a₂ ≠ a₃)
    (hint₁ : IsIntegral ℤ a₁) (hint₂ : IsIntegral ℤ a₂) (hint₃ : IsIntegral ℤ a₃)
    (T S_fin : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hT : IsGoodT a₁ a₂ a₃ T) (hT_sub : T ⊆ S_fin)
    (hS_fin : ∀ c : ClassGroup (NumberField.RingOfIntegers K),
      ∃ I : nonZeroDivisors (Ideal (NumberField.RingOfIntegers K)),
        ClassGroup.mk0 I = c ∧
        ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          v ∉ S_fin → ¬ (v.asIdeal ∣ (I : Ideal (NumberField.RingOfIntegers K))))
    (u : Kˣ)
    (hu_even : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      v ∉ S_fin → EvenVal v u)
    (hu_fin : ∀ v ∈ S_fin, IsSquare (algebraMap K (v.adicCompletion K) (u : K)))
    (hu_inf : ∀ w : NumberField.InfinitePlace K, IsSquare (algebraMap K w.Completion (u : K))) :
    ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      IsSquare (algebraMap K (v.adicCompletion K) (u : K)) :=
by
  classical
  have h2_val_outside_T : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      v ∉ T → IsDedekindDomain.HeightOneSpectrum.valuation K v (2 : K) = 1 := by
    intro v hvT
    let A₁ : NumberField.RingOfIntegers K := ⟨a₁, hint₁⟩
    let A₂ : NumberField.RingOfIntegers K := ⟨a₂, hint₂⟩
    let A₃ : NumberField.RingOfIntegers K := ⟨a₃, hint₃⟩
    let W : NumberField.RingOfIntegers K := 3 * (A₁ - A₂) * (A₁ - A₃) * (A₂ - A₃)
    have h2_le : IsDedekindDomain.HeightOneSpectrum.valuation K v (2 : K) ≤ 1 := by
      rw [← map_ofNat (algebraMap (NumberField.RingOfIntegers K) K) 2]
      exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one v 2
    have hW_le : IsDedekindDomain.HeightOneSpectrum.valuation K v
        (algebraMap (NumberField.RingOfIntegers K) K W) ≤ 1 :=
      IsDedekindDomain.HeightOneSpectrum.valuation_le_one v W
    have hprod_eq : 6 * (a₁ - a₂) * (a₁ - a₃) * (a₂ - a₃) =
        (2 : K) * algebraMap (NumberField.RingOfIntegers K) K W := by
      change 6 * (a₁ - a₂) * (a₁ - a₃) * (a₂ - a₃) =
        (2 : K) * algebraMap (NumberField.RingOfIntegers K) K
          (3 * (A₁ - A₂) * (A₁ - A₃) * (A₂ - A₃))
      simp only [map_mul, map_sub, map_ofNat]
      change 6 * (a₁ - a₂) * (a₁ - a₃) * (a₂ - a₃) =
        2 * (3 * (a₁ - a₂) * (a₁ - a₃) * (a₂ - a₃))
      ring
    have hv_prod : IsDedekindDomain.HeightOneSpectrum.valuation K v
        (6 * (a₁ - a₂) * (a₁ - a₃) * (a₂ - a₃)) = 1 := by
      have h := (hT v).not.mp hvT
      push_neg at h
      exact h
    rw [hprod_eq, Valuation.map_mul] at hv_prod
    refine le_antisymm h2_le ?_
    calc (1 : WithZero (Multiplicative ℤ))
        = IsDedekindDomain.HeightOneSpectrum.valuation K v (2 : K) *
            IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K W) := hv_prod.symm
      _ ≤ IsDedekindDomain.HeightOneSpectrum.valuation K v (2 : K) * 1 :=
          mul_le_mul_right hW_le _
      _ = IsDedekindDomain.HeightOneSpectrum.valuation K v (2 : K) := mul_one _
  have exists_sq_of_valued_sub_sq_lt_one :
      ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      Valued.v (2 : v.adicCompletion K) = (1 : WithZero (Multiplicative ℤ)) →
      ∀ (c x₀ : v.adicCompletion K),
      Valued.v x₀ = (1 : WithZero (Multiplicative ℤ)) →
      Valued.v (c - x₀ ^ 2) < (1 : WithZero (Multiplicative ℤ)) →
      ∃ z : v.adicCompletion K, z ^ 2 = c := by
    intro v h2 c x₀ hx₀ hc
    have hstep : ∀ y : v.adicCompletion K,
        Valued.v y = (1 : WithZero (Multiplicative ℤ)) →
        Valued.v (y ^ 2 - c) < (1 : WithZero (Multiplicative ℤ)) →
        Valued.v (y - (y ^ 2 - c) / (2 * y)) = (1 : WithZero (Multiplicative ℤ)) ∧
        Valued.v ((y - (y ^ 2 - c) / (2 * y)) ^ 2 - c) = Valued.v (y ^ 2 - c) ^ 2 ∧
        Valued.v (y - (y ^ 2 - c) / (2 * y) - y) = Valued.v (y ^ 2 - c) := by
      intro y hy hd
      have h2ne : (2 : v.adicCompletion K) ≠ 0 := by
        intro hcon; rw [hcon, map_zero] at h2; exact zero_ne_one h2
      have hyne : y ≠ 0 := by
        intro hcon; rw [hcon, map_zero] at hy; exact zero_ne_one hy
      have ht : Valued.v ((y ^ 2 - c) / (2 * y)) = Valued.v (y ^ 2 - c) := by
        rw [map_div₀, map_mul, h2, hy, one_mul, div_one]
      have hlt' : Valued.v ((y ^ 2 - c) / (2 * y)) < Valued.v y := by
        rw [ht, hy]; exact hd
      refine ⟨?_, ?_, ?_⟩
      · rw [Valuation.map_sub_eq_of_lt_left _ hlt', hy]
      · have key : (y - (y ^ 2 - c) / (2 * y)) ^ 2 - c = ((y ^ 2 - c) / (2 * y)) ^ 2 := by
          field_simp; ring
        rw [key, Valuation.map_pow, ht]
      · have key : y - (y ^ 2 - c) / (2 * y) - y = -((y ^ 2 - c) / (2 * y)) := by ring
        rw [key, Valuation.map_neg, ht]
    have hdecay : ∀ δ γ : WithZero (Multiplicative ℤ), δ < 1 → γ ≠ 0 →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → δ ^ (2 ^ n) < γ := by
      intro δ γ hδ hγ
      rcases eq_or_ne δ 0 with h0 | h0
      · refine ⟨0, fun n _ => ?_⟩
        rw [h0, zero_pow (Nat.two_pow_pos n).ne']
        exact zero_lt_iff.mpr hγ
      · obtain ⟨a, rfl⟩ : ∃ a : ℤ, δ = ((Multiplicative.ofAdd a : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
          obtain ⟨g, hg⟩ := WithZero.ne_zero_iff_exists.mp h0
          exact ⟨Multiplicative.toAdd g, hg.symm⟩
        obtain ⟨b, rfl⟩ : ∃ b : ℤ, γ = ((Multiplicative.ofAdd b : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
          obtain ⟨g, hg⟩ := WithZero.ne_zero_iff_exists.mp hγ
          exact ⟨Multiplicative.toAdd g, hg.symm⟩
        have ha : a < 0 := WithZero.coe_lt_one.mp hδ
        have hpow : ∀ k : ℕ,
            ((Multiplicative.ofAdd a : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ k
              = ((Multiplicative.ofAdd ((k : ℤ) * a) : Multiplicative ℤ) :
                  WithZero (Multiplicative ℤ)) := by
          intro k; rw [← WithZero.coe_pow]; congr 1
        refine ⟨(-b).toNat + 1, fun n hn => ?_⟩
        rw [hpow, WithZero.coe_lt_coe]
        have hbk : -b < ((2 ^ n : ℕ) : ℤ) := by
          have hx : (-b).toNat < n := by omega
          have h1 : (-b).toNat < 2 ^ n := lt_trans hx Nat.lt_two_pow_self
          have h2' : ((-b).toNat : ℤ) < ((2 ^ n : ℕ) : ℤ) := by exact_mod_cast h1
          exact lt_of_le_of_lt (Int.self_le_toNat _) h2'
        have hkpos : (0 : ℤ) ≤ ((2 ^ n : ℕ) : ℤ) := Int.natCast_nonneg _
        have ha1 : a ≤ -1 := by omega
        have hle : ((2 ^ n : ℕ) : ℤ) * a ≤ ((2 ^ n : ℕ) : ℤ) * (-1) :=
          mul_le_mul_of_nonneg_left ha1 hkpos
        have hgoal : ((2 ^ n : ℕ) : ℤ) * a < b := by linarith
        exact hgoal
    obtain ⟨ε, hεdef⟩ : ∃ ε : WithZero (Multiplicative ℤ), ε = Valued.v (x₀ ^ 2 - c) := ⟨_, rfl⟩
    have hε : ε < (1 : WithZero (Multiplicative ℤ)) := by
      rw [hεdef, Valuation.map_sub_swap]; exact hc
    obtain ⟨f, hf0, hfs⟩ : ∃ f : ℕ → v.adicCompletion K, f 0 = x₀ ∧
        ∀ n : ℕ, f (n + 1) = f n - (f n ^ 2 - c) / (2 * f n) :=
      ⟨fun n => Nat.rec (motive := fun _ => v.adicCompletion K) x₀
        (fun _ y => y - (y ^ 2 - c) / (2 * y)) n, rfl, fun _ => rfl⟩
    have hinv : ∀ n : ℕ, Valued.v (f n) = (1 : WithZero (Multiplicative ℤ)) ∧
        Valued.v (f n ^ 2 - c) = ε ^ (2 ^ n) := by
      intro n
      induction n with
      | zero =>
        refine ⟨by rw [hf0]; exact hx₀, ?_⟩
        rw [hf0, pow_zero, pow_one, hεdef]
      | succ n ih =>
        have hlt : Valued.v (f n ^ 2 - c) < (1 : WithZero (Multiplicative ℤ)) := by
          rw [ih.2]; exact pow_lt_one₀ zero_le' hε (Nat.two_pow_pos n).ne'
        obtain ⟨s1, s2, -⟩ := hstep (f n) ih.1 hlt
        refine ⟨by rw [hfs n]; exact s1, ?_⟩
        rw [hfs n, s2, ih.2, ← pow_mul, ← pow_succ]
    have hdiff : ∀ n : ℕ, Valued.v (f (n + 1) - f n) = ε ^ (2 ^ n) := by
      intro n
      have hlt : Valued.v (f n ^ 2 - c) < (1 : WithZero (Multiplicative ℤ)) := by
        rw [(hinv n).2]; exact pow_lt_one₀ zero_le' hε (Nat.two_pow_pos n).ne'
      obtain ⟨-, -, s3⟩ := hstep (f n) (hinv n).1 hlt
      rw [hfs n, s3, (hinv n).2]
    have hCauchy : Cauchy (Filter.map f Filter.atTop) := by
      refine Valued.cauchy_iff.mpr ⟨inferInstance, ?_⟩
      intro γ
      obtain ⟨N, hN⟩ := hdecay ε (γ : WithZero (Multiplicative ℤ)) hε (Units.ne_zero γ)
      have htel : ∀ m : ℕ, N ≤ m → Valued.v (f m - f N) < (γ : WithZero (Multiplicative ℤ)) := by
        intro m hm
        induction m, hm using Nat.le_induction with
        | base =>
          rw [sub_self, map_zero]; exact zero_lt_iff.mpr (Units.ne_zero γ)
        | succ m hm ih =>
          have e : f (m + 1) - f N = (f (m + 1) - f m) + (f m - f N) := by ring
          rw [e]
          refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ih)
          rw [hdiff m]; exact hN m hm
      refine ⟨f '' (Set.Ici N), Filter.image_mem_map (Filter.Ici_mem_atTop N), ?_⟩
      rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
      have e : f j - f i = (f j - f N) - (f i - f N) := by ring
      rw [e]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt (htel j hj) (htel i hi))
    obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hCauchy
    have hsq : Filter.Tendsto (fun n : ℕ => f n ^ 2 - c) Filter.atTop (nhds (z ^ 2 - c)) :=
      (hz.pow 2).sub tendsto_const_nhds
    have hzero : Filter.Tendsto (fun n : ℕ => f n ^ 2 - c) Filter.atTop
        (nhds (0 : v.adicCompletion K)) := by
      rw [Filter.tendsto_def]
      intro s hs
      obtain ⟨γ, hγs⟩ := Valued.mem_nhds_zero.mp hs
      obtain ⟨N, hN⟩ := hdecay ε (γ : WithZero (Multiplicative ℤ)) hε (Units.ne_zero γ)
      refine Filter.mem_of_superset (Filter.Ici_mem_atTop N) ?_
      intro n hn
      apply hγs
      show Valued.v (f n ^ 2 - c) < (γ : WithZero (Multiplicative ℤ))
      rw [(hinv n).2]; exact hN n hn
    exact ⟨z, eq_of_sub_eq_zero (tendsto_nhds_unique hsq hzero)⟩
  have h_even_factor : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
      (w : Kˣ), EvenVal v w →
      ∃ u₀ z₀ : K, IsDedekindDomain.HeightOneSpectrum.valuation K v u₀ = 1 ∧ z₀ ≠ 0 ∧ (w : K) = u₀ * z₀ ^ 2 := by
    intro v w hw
    obtain ⟨π₀, hπ₀⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer K v
    have hπ₀_ne : π₀ ≠ 0 := by
      intro h0
      rw [h0, Valuation.map_zero] at hπ₀
      exact WithZero.coe_ne_zero hπ₀.symm
    rcases hw with ⟨k, hk⟩
    have hval_w : IsDedekindDomain.HeightOneSpectrum.valuation K v (w : K) = WithZero.exp (k + k) := by
      rw [← IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq v w]
      have hk' : v.valuationOfNeZero w = Multiplicative.ofAdd (k + k) := by
        rw [← hk, ofAdd_toAdd]
      rw [hk']
      rfl
    refine ⟨(w : K) * π₀ ^ (k + k), π₀ ^ (-k), ?_, zpow_ne_zero (-k) hπ₀_ne, ?_⟩
    · rw [Valuation.map_mul, map_zpow₀, hval_w, hπ₀, ← WithZero.exp_zsmul, ← WithZero.exp_add]
      have hzero : k + k + (k + k) • (-1 : ℤ) = 0 := by
        rw [smul_eq_mul]
        ring
      rw [hzero, WithZero.exp_zero]
    · rw [sq, mul_assoc, ← zpow_add₀ hπ₀_ne, ← zpow_add₀ hπ₀_ne]
      have hzero : (k + k) + (-k + -k) = 0 := by ring
      rw [hzero, zpow_zero, mul_one]
  have h_hilbFin_evenVal :
      ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      v ∉ T → ∀ (x y : Kˣ), EvenVal v x → EvenVal v y → hilbFin v (x : K) (y : K) = 1 := by
    intro v hvT x y hx hy
    have exists_ringOfIntegers_approx_of_valuation_le_one :
        ∀ (a : K), IsDedekindDomain.HeightOneSpectrum.valuation K v a ≤ 1 →
        ∃ r : NumberField.RingOfIntegers K,
          IsDedekindDomain.HeightOneSpectrum.valuation K v
            (a - algebraMap (NumberField.RingOfIntegers K) K r) < 1 := by
      intro a ha
      obtain ⟨xa, ya, hya, hxya⟩ :=
        IsFractionRing.div_surjective (A := NumberField.RingOfIntegers K) (K := K) a
      have hy0 : ya ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hya
      have hiy : algebraMap (NumberField.RingOfIntegers K) K ya ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hya
      have hstar : a * algebraMap (NumberField.RingOfIntegers K) K ya
          = algebraMap (NumberField.RingOfIntegers K) K xa := by
        rw [← hxya]
        exact div_mul_cancel₀ _ hiy
      obtain ⟨m, hym, hym1⟩ : ∃ m : ℕ, ya ∈ v.asIdeal ^ m ∧ ya ∉ v.asIdeal ^ (m + 1) := by
        have ht0 : v.intValuation ya ≠ 0 :=
          IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero v ya hy0
        have ht1 : v.intValuation ya ≤ 1 :=
          IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v ya
        obtain ⟨k, hk⟩ : ∃ k : ℤ, WithZero.exp k = v.intValuation ya := ⟨_, WithZero.exp_log ht0⟩
        have hkle : k ≤ 0 := by
          have hstep : WithZero.exp k ≤ WithZero.exp (0 : ℤ) := by
            rw [hk, WithZero.exp_zero]; exact ht1
          exact WithZero.exp_le_exp.mp hstep
        have hcast : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
        have hexpm : WithZero.exp (-(((-k).toNat : ℕ) : ℤ)) = v.intValuation ya := by
          rw [hcast, neg_neg, hk]
        refine ⟨(-k).toNat, ?_, ?_⟩
        · exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya _).mp
            (le_of_eq hexpm.symm)
        · intro hcon
          have hle :=
            (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya
              ((-k).toNat + 1)).mpr hcon
          have he : (-(((-k).toNat + 1 : ℕ) : ℤ)) = k - 1 := by
            rw [Nat.cast_add, Nat.cast_one, hcast]; ring
          rw [he, ← hk] at hle
          have := WithZero.exp_le_exp.mp hle
          omega
      have hivy : v.intValuation ya ≤ WithZero.exp (-(m : ℤ)) :=
        (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya m).mpr hym
      have hxm : xa ∈ v.asIdeal ^ m := by
        refine (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v xa m).mp ?_
        have e1 : v.intValuation xa
            = IsDedekindDomain.HeightOneSpectrum.valuation K v
                (algebraMap (NumberField.RingOfIntegers K) K xa) :=
          (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v xa).symm
        have e2 : v.intValuation ya
            = IsDedekindDomain.HeightOneSpectrum.valuation K v
                (algebraMap (NumberField.RingOfIntegers K) K ya) :=
          (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v ya).symm
        calc v.intValuation xa
            = IsDedekindDomain.HeightOneSpectrum.valuation K v
                (a * algebraMap (NumberField.RingOfIntegers K) K ya) := by
              rw [hstar]; exact e1
          _ = IsDedekindDomain.HeightOneSpectrum.valuation K v a *
                IsDedekindDomain.HeightOneSpectrum.valuation K v
                  (algebraMap (NumberField.RingOfIntegers K) K ya) := Valuation.map_mul _ _ _
          _ ≤ 1 * IsDedekindDomain.HeightOneSpectrum.valuation K v
                  (algebraMap (NumberField.RingOfIntegers K) K ya) := mul_le_mul_left ha _
          _ = v.intValuation ya := by rw [one_mul, ← e2]
          _ ≤ WithZero.exp (-(m : ℤ)) := hivy
      have hPprime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
      have hJdvd : (Ideal.span {ya} ⊔ v.asIdeal ^ (m + 1)) ∣ v.asIdeal ^ (m + 1) :=
        Ideal.dvd_iff_le.mpr le_sup_right
      obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow hPprime (m + 1)).mp hJdvd
      have hJ : Ideal.span {ya} ⊔ v.asIdeal ^ (m + 1) = v.asIdeal ^ i := associated_iff_eq.mp hassoc
      have hyJ : ya ∈ v.asIdeal ^ i := by
        rw [← hJ]
        exact Ideal.dvd_span_singleton.mp (Ideal.dvd_iff_le.mpr le_sup_left)
      have him : i ≤ m := by
        by_contra hcon
        have hii : i = m + 1 := by omega
        rw [hii] at hyJ
        exact hym1 hyJ
      have hxJ : xa ∈ Ideal.span {ya} ⊔ v.asIdeal ^ (m + 1) := by
        rw [hJ]
        exact Ideal.pow_le_pow_right him hxm
      obtain ⟨p, hp, w, hw, hpw⟩ := Submodule.mem_sup.mp hxJ
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hp
      refine ⟨r, ?_⟩
      have hxrw : xa = r * ya + w := by rw [← hpw, hr]
      have key : (a - algebraMap (NumberField.RingOfIntegers K) K r)
          * algebraMap (NumberField.RingOfIntegers K) K ya
          = algebraMap (NumberField.RingOfIntegers K) K w := by
        have h1 : algebraMap (NumberField.RingOfIntegers K) K xa
            = algebraMap (NumberField.RingOfIntegers K) K r
                * algebraMap (NumberField.RingOfIntegers K) K ya
              + algebraMap (NumberField.RingOfIntegers K) K w := by
          rw [hxrw, map_add, map_mul]
        rw [sub_mul, hstar, h1]; ring
      have hV : IsDedekindDomain.HeightOneSpectrum.valuation K v
            (a - algebraMap (NumberField.RingOfIntegers K) K r) * v.intValuation ya
          = v.intValuation w := by
        rw [← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v ya,
          ← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v w,
          ← Valuation.map_mul, key]
      have hwb : v.intValuation w ≤ WithZero.exp (-((m + 1 : ℕ) : ℤ)) :=
        (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v w (m + 1)).mpr hw
      have hyb : WithZero.exp (-((m + 1 : ℕ) : ℤ)) < v.intValuation ya := by
        by_contra hcon
        push_neg at hcon
        exact hym1
          ((IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya (m + 1)).mp hcon)
      by_contra hcon
      push_neg at hcon
      have hchain : v.intValuation ya ≤ v.intValuation w := by
        calc v.intValuation ya = 1 * v.intValuation ya := (one_mul _).symm
          _ ≤ IsDedekindDomain.HeightOneSpectrum.valuation K v
                (a - algebraMap (NumberField.RingOfIntegers K) K r) * v.intValuation ya :=
              mul_le_mul_left hcon _
          _ = v.intValuation w := hV
      exact absurd (lt_of_le_of_lt (le_trans hchain hwb) hyb) (lt_irrefl _)
    have exists_sol_quadratic_mod_heightOneSpectrum :
        (2 : NumberField.RingOfIntegers K) ∉ v.asIdeal →
        ∀ (r s : NumberField.RingOfIntegers K), r ∉ v.asIdeal → s ∉ v.asIdeal →
        ∃ x₀ y₀ : NumberField.RingOfIntegers K, r * x₀ ^ 2 + s * y₀ ^ 2 - 1 ∈ v.asIdeal := by
      intro h2 r s hr hs
      letI : Field (NumberField.RingOfIntegers K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
      letI : Fintype (NumberField.RingOfIntegers K ⧸ v.asIdeal) := Fintype.ofFinite _
      have hr' : Ideal.Quotient.mk v.asIdeal r ≠ 0 := fun h =>
        hr (Ideal.Quotient.eq_zero_iff_mem.mp h)
      have hs' : Ideal.Quotient.mk v.asIdeal s ≠ 0 := fun h =>
        hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
      have h2' : (2 : NumberField.RingOfIntegers K ⧸ v.asIdeal) ≠ 0 := by
        intro h
        refine h2 (Ideal.Quotient.eq_zero_iff_mem.mp ?_)
        rw [map_ofNat]
        exact h
      have hchar : ringChar (NumberField.RingOfIntegers K ⧸ v.asIdeal) ≠ 2 := by
        intro h
        refine h2' ?_
        have h4 : ((2 : ℕ) : NumberField.RingOfIntegers K ⧸ v.asIdeal) = 0 :=
          (ringChar.spec _ 2).mpr (by rw [h])
        simpa using h4
      have hcard : Fintype.card (NumberField.RingOfIntegers K ⧸ v.asIdeal) % 2 = 1 :=
        FiniteField.odd_card_of_char_ne_two hchar
      obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
        (f := Polynomial.C (Ideal.Quotient.mk v.asIdeal r) * Polynomial.X ^ 2
          + Polynomial.C 0 * Polynomial.X + Polynomial.C 0)
        (g := Polynomial.C (Ideal.Quotient.mk v.asIdeal s) * Polynomial.X ^ 2
          + Polynomial.C 0 * Polynomial.X + Polynomial.C (-1))
        (Polynomial.degree_quadratic hr') (Polynomial.degree_quadratic hs') hcard
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_X, zero_mul, add_zero] at hab
      obtain ⟨x₀, hx₀⟩ := Ideal.Quotient.mk_surjective (I := v.asIdeal) a
      obtain ⟨y₀, hy₀⟩ := Ideal.Quotient.mk_surjective (I := v.asIdeal) b
      refine ⟨x₀, y₀, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
      simp only [map_sub, map_add, map_mul, map_pow, map_one]
      rw [hx₀, hy₀]
      linear_combination hab
    have hilbFin_eq_one_of_units :
        ∀ (a b : K),
        IsDedekindDomain.HeightOneSpectrum.valuation K v a = 1 →
        IsDedekindDomain.HeightOneSpectrum.valuation K v b = 1 →
        IsDedekindDomain.HeightOneSpectrum.valuation K v (2 : K) = 1 →
        hilbFin v a b = 1 := by
      intro a b ha hb h2
      have hval : ∀ k : K, Valued.v (algebraMap K (v.adicCompletion K) k)
          = IsDedekindDomain.HeightOneSpectrum.valuation K v k := fun k =>
        IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
      have h2v : Valued.v (2 : v.adicCompletion K) = (1 : WithZero (Multiplicative ℤ)) := by
        rw [(map_ofNat (algebraMap K (v.adicCompletion K)) 2).symm, hval, h2]
      have key : ∀ a' b' X Y : K,
          IsDedekindDomain.HeightOneSpectrum.valuation K v a' = 1 →
          IsDedekindDomain.HeightOneSpectrum.valuation K v X = 1 →
          IsDedekindDomain.HeightOneSpectrum.valuation K v (a' * X ^ 2 + b' * Y ^ 2 - 1) < 1 →
          ∃ Z W : v.adicCompletion K,
            algebraMap K (v.adicCompletion K) a' * Z ^ 2
              + algebraMap K (v.adicCompletion K) b' * W ^ 2 = 1 := by
        intro a' b' X Y ha' hX hlt
        have ha'0 : a' ≠ 0 := by
          intro h; rw [h] at ha'; simp at ha'
        obtain ⟨c, hac⟩ : ∃ c : K, a' * c = 1 - b' * Y ^ 2 :=
          ⟨(1 - b' * Y ^ 2) / a', by field_simp⟩
        have hid : a' * (c - X ^ 2) = -(a' * X ^ 2 + b' * Y ^ 2 - 1) := by
          rw [mul_sub, hac]; ring
        have hlt2 : IsDedekindDomain.HeightOneSpectrum.valuation K v (c - X ^ 2) < 1 := by
          have h := congrArg (IsDedekindDomain.HeightOneSpectrum.valuation K v) hid
          rw [Valuation.map_mul, ha', one_mul, Valuation.map_neg] at h
          rw [h]; exact hlt
        have hx0v : Valued.v (algebraMap K (v.adicCompletion K) X)
            = (1 : WithZero (Multiplicative ℤ)) := by rw [hval, hX]
        have hcv : Valued.v (algebraMap K (v.adicCompletion K) c
            - (algebraMap K (v.adicCompletion K) X) ^ 2) < (1 : WithZero (Multiplicative ℤ)) := by
          have e : algebraMap K (v.adicCompletion K) c
              - (algebraMap K (v.adicCompletion K) X) ^ 2
              = algebraMap K (v.adicCompletion K) (c - X ^ 2) := by
            simp only [map_sub, map_pow]
          rw [e, hval]; exact hlt2
        obtain ⟨Z, hZ⟩ := exists_sq_of_valued_sub_sq_lt_one v h2v
          (algebraMap K (v.adicCompletion K) c) (algebraMap K (v.adicCompletion K) X) hx0v hcv
        refine ⟨Z, algebraMap K (v.adicCompletion K) Y, ?_⟩
        have hsum : a' * c + b' * Y ^ 2 = 1 := by rw [hac]; ring
        have hmap : algebraMap K (v.adicCompletion K) a' * algebraMap K (v.adicCompletion K) c
            + algebraMap K (v.adicCompletion K) b' * (algebraMap K (v.adicCompletion K) Y) ^ 2
            = algebraMap K (v.adicCompletion K) (a' * c + b' * Y ^ 2) := by
          simp only [map_add, map_mul, map_pow]
        rw [hZ, hmap, hsum, map_one]
      obtain ⟨r, hr⟩ := exists_ringOfIntegers_approx_of_valuation_le_one a (le_of_eq ha)
      obtain ⟨s, hs⟩ := exists_ringOfIntegers_approx_of_valuation_le_one b (le_of_eq hb)
      have hrv : IsDedekindDomain.HeightOneSpectrum.valuation K v
          (algebraMap (NumberField.RingOfIntegers K) K r) = 1 := by
        have e : algebraMap (NumberField.RingOfIntegers K) K r
            = a - (a - algebraMap (NumberField.RingOfIntegers K) K r) := by ring
        rw [e, Valuation.map_sub_eq_of_lt_left _ (by rw [ha]; exact hr), ha]
      have hsv : IsDedekindDomain.HeightOneSpectrum.valuation K v
          (algebraMap (NumberField.RingOfIntegers K) K s) = 1 := by
        have e : algebraMap (NumberField.RingOfIntegers K) K s
            = b - (b - algebraMap (NumberField.RingOfIntegers K) K s) := by ring
        rw [e, Valuation.map_sub_eq_of_lt_left _ (by rw [hb]; exact hs), hb]
      have hrnot : r ∉ v.asIdeal := by
        refine IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mp ?_
        rw [← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v r]
        exact hrv
      have hsnot : s ∉ v.asIdeal := by
        refine IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mp ?_
        rw [← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v s]
        exact hsv
      have h2not : (2 : NumberField.RingOfIntegers K) ∉ v.asIdeal := by
        refine IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mp ?_
        have e : IsDedekindDomain.HeightOneSpectrum.valuation K v
            (algebraMap (NumberField.RingOfIntegers K) K (2 : NumberField.RingOfIntegers K))
            = IsDedekindDomain.HeightOneSpectrum.intValuation v
              (2 : NumberField.RingOfIntegers K) :=
          IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v 2
        rw [← e, map_ofNat (algebraMap (NumberField.RingOfIntegers K) K) 2]
        exact h2
      obtain ⟨x₀, y₀, hxy⟩ := exists_sol_quadratic_mod_heightOneSpectrum h2not r s hrnot hsnot
      have halpha : IsDedekindDomain.HeightOneSpectrum.valuation K v
          ((algebraMap (NumberField.RingOfIntegers K) K) r
              * ((algebraMap (NumberField.RingOfIntegers K) K) x₀) ^ 2
            + (algebraMap (NumberField.RingOfIntegers K) K) s
              * ((algebraMap (NumberField.RingOfIntegers K) K) y₀) ^ 2 - 1) < 1 := by
        have e : (algebraMap (NumberField.RingOfIntegers K) K) r
              * ((algebraMap (NumberField.RingOfIntegers K) K) x₀) ^ 2
            + (algebraMap (NumberField.RingOfIntegers K) K) s
              * ((algebraMap (NumberField.RingOfIntegers K) K) y₀) ^ 2 - 1
            = (algebraMap (NumberField.RingOfIntegers K) K) (r * x₀ ^ 2 + s * y₀ ^ 2 - 1) := by
          simp only [map_add, map_mul, map_pow, map_sub, map_one]
        rw [e, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v,
          IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem]
        exact hxy
      have hXle : IsDedekindDomain.HeightOneSpectrum.valuation K v
          ((algebraMap (NumberField.RingOfIntegers K) K) x₀) ≤ 1 :=
        IsDedekindDomain.HeightOneSpectrum.valuation_le_one v x₀
      have hYle : IsDedekindDomain.HeightOneSpectrum.valuation K v
          ((algebraMap (NumberField.RingOfIntegers K) K) y₀) ≤ 1 :=
        IsDedekindDomain.HeightOneSpectrum.valuation_le_one v y₀
      have hbeta : IsDedekindDomain.HeightOneSpectrum.valuation K v
          (a * ((algebraMap (NumberField.RingOfIntegers K) K) x₀) ^ 2
            + b * ((algebraMap (NumberField.RingOfIntegers K) K) y₀) ^ 2 - 1) < 1 := by
        have t1 : IsDedekindDomain.HeightOneSpectrum.valuation K v
            ((a - (algebraMap (NumberField.RingOfIntegers K) K) r)
              * ((algebraMap (NumberField.RingOfIntegers K) K) x₀) ^ 2) < 1 := by
          rw [Valuation.map_mul, Valuation.map_pow]
          calc IsDedekindDomain.HeightOneSpectrum.valuation K v
                  (a - (algebraMap (NumberField.RingOfIntegers K) K) r)
                * IsDedekindDomain.HeightOneSpectrum.valuation K v
                  ((algebraMap (NumberField.RingOfIntegers K) K) x₀) ^ 2
              ≤ IsDedekindDomain.HeightOneSpectrum.valuation K v
                  (a - (algebraMap (NumberField.RingOfIntegers K) K) r) * 1 :=
                mul_le_mul_right (pow_le_one' hXle 2) _
            _ = IsDedekindDomain.HeightOneSpectrum.valuation K v
                  (a - (algebraMap (NumberField.RingOfIntegers K) K) r) := mul_one _
            _ < 1 := hr
        have t2 : IsDedekindDomain.HeightOneSpectrum.valuation K v
            ((b - (algebraMap (NumberField.RingOfIntegers K) K) s)
              * ((algebraMap (NumberField.RingOfIntegers K) K) y₀) ^ 2) < 1 := by
          rw [Valuation.map_mul, Valuation.map_pow]
          calc IsDedekindDomain.HeightOneSpectrum.valuation K v
                  (b - (algebraMap (NumberField.RingOfIntegers K) K) s)
                * IsDedekindDomain.HeightOneSpectrum.valuation K v
                  ((algebraMap (NumberField.RingOfIntegers K) K) y₀) ^ 2
              ≤ IsDedekindDomain.HeightOneSpectrum.valuation K v
                  (b - (algebraMap (NumberField.RingOfIntegers K) K) s) * 1 :=
                mul_le_mul_right (pow_le_one' hYle 2) _
            _ = IsDedekindDomain.HeightOneSpectrum.valuation K v
                  (b - (algebraMap (NumberField.RingOfIntegers K) K) s) := mul_one _
            _ < 1 := hs
        have t3 : IsDedekindDomain.HeightOneSpectrum.valuation K v
            ((a - (algebraMap (NumberField.RingOfIntegers K) K) r)
                * ((algebraMap (NumberField.RingOfIntegers K) K) x₀) ^ 2
              + (b - (algebraMap (NumberField.RingOfIntegers K) K) s)
                * ((algebraMap (NumberField.RingOfIntegers K) K) y₀) ^ 2) < 1 :=
          lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt t1 t2)
        have e : a * ((algebraMap (NumberField.RingOfIntegers K) K) x₀) ^ 2
            + b * ((algebraMap (NumberField.RingOfIntegers K) K) y₀) ^ 2 - 1
            = ((algebraMap (NumberField.RingOfIntegers K) K) r
                * ((algebraMap (NumberField.RingOfIntegers K) K) x₀) ^ 2
              + (algebraMap (NumberField.RingOfIntegers K) K) s
                * ((algebraMap (NumberField.RingOfIntegers K) K) y₀) ^ 2 - 1)
              + ((a - (algebraMap (NumberField.RingOfIntegers K) K) r)
                  * ((algebraMap (NumberField.RingOfIntegers K) K) x₀) ^ 2
                + (b - (algebraMap (NumberField.RingOfIntegers K) K) s)
                  * ((algebraMap (NumberField.RingOfIntegers K) K) y₀) ^ 2) := by ring
        rw [e]
        exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt halpha t3)
      have hcase : x₀ ∉ v.asIdeal ∨ y₀ ∉ v.asIdeal := by
        by_contra hcon
        push_neg at hcon
        obtain ⟨hx₀, hy₀⟩ := hcon
        have h1 : r * x₀ ^ 2 + s * y₀ ^ 2 ∈ v.asIdeal :=
          Ideal.add_mem _
            (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hx₀ 2 (by norm_num)))
            (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hy₀ 2 (by norm_num)))
        have hone : (1 : NumberField.RingOfIntegers K) ∈ v.asIdeal := by
          have h3 := Ideal.sub_mem _ h1 hxy
          simpa using h3
        exact v.isPrime.ne_top (Ideal.eq_top_iff_one _ |>.mpr hone)
      have hex : ∃ Z W : v.adicCompletion K,
          algebraMap K (v.adicCompletion K) a * Z ^ 2
            + algebraMap K (v.adicCompletion K) b * W ^ 2 = 1 := by
        rcases hcase with hx₀ | hy₀
        · have hXv : IsDedekindDomain.HeightOneSpectrum.valuation K v
              ((algebraMap (NumberField.RingOfIntegers K) K) x₀) = 1 := by
            rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v x₀]
            exact IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr hx₀
          exact key a b ((algebraMap (NumberField.RingOfIntegers K) K) x₀)
            ((algebraMap (NumberField.RingOfIntegers K) K) y₀) ha hXv hbeta
        · have hYv : IsDedekindDomain.HeightOneSpectrum.valuation K v
              ((algebraMap (NumberField.RingOfIntegers K) K) y₀) = 1 := by
            rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v y₀]
            exact IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr hy₀
          have hbeta' : IsDedekindDomain.HeightOneSpectrum.valuation K v
              (b * ((algebraMap (NumberField.RingOfIntegers K) K) y₀) ^ 2
                + a * ((algebraMap (NumberField.RingOfIntegers K) K) x₀) ^ 2 - 1) < 1 := by
            rw [show b * ((algebraMap (NumberField.RingOfIntegers K) K) y₀) ^ 2
                  + a * ((algebraMap (NumberField.RingOfIntegers K) K) x₀) ^ 2 - 1
                = a * ((algebraMap (NumberField.RingOfIntegers K) K) x₀) ^ 2
                  + b * ((algebraMap (NumberField.RingOfIntegers K) K) y₀) ^ 2 - 1 from by ring]
            exact hbeta
          obtain ⟨Z, W, hZW⟩ := key b a ((algebraMap (NumberField.RingOfIntegers K) K) y₀)
            ((algebraMap (NumberField.RingOfIntegers K) K) x₀) hb hYv hbeta'
          exact ⟨W, Z, by rw [← hZW]; ring⟩
      simp only [hilbFin, hilbLoc]
      rw [if_pos hex]
    obtain ⟨u_x, z_x, hux, hzx, hxeq⟩ := h_even_factor v x hx
    obtain ⟨u_y, z_y, huy, hzy, hyeq⟩ := h_even_factor v y hy
    have h_units : hilbFin v u_x u_y = 1 :=
      hilbFin_eq_one_of_units u_x u_y hux huy (h2_val_outside_T v hvT)
    simp only [hilbFin, hilbLoc] at h_units ⊢
    split_ifs at h_units with hsol
    · rcases hsol with ⟨Z, W, hZW⟩
      have hZx : algebraMap K (v.adicCompletion K) z_x ≠ 0 := by
        rw [ne_eq, map_eq_zero]
        exact hzx
      have hZy : algebraMap K (v.adicCompletion K) z_y ≠ 0 := by
        rw [ne_eq, map_eq_zero]
        exact hzy
      have hsol' : ∃ X Y : v.adicCompletion K,
          algebraMap K (v.adicCompletion K) (x : K) * X ^ 2 +
            algebraMap K (v.adicCompletion K) (y : K) * Y ^ 2 = 1 := by
        refine ⟨Z / algebraMap K (v.adicCompletion K) z_x,
          W / algebraMap K (v.adicCompletion K) z_y, ?_⟩
        rw [hxeq, hyeq, map_mul, map_mul, map_pow, map_pow]
        have h1 : algebraMap K (v.adicCompletion K) u_x *
            (algebraMap K (v.adicCompletion K) z_x) ^ 2 *
            (Z / algebraMap K (v.adicCompletion K) z_x) ^ 2 =
            algebraMap K (v.adicCompletion K) u_x * Z ^ 2 := by
          field_simp [hZx]
        have h2 : algebraMap K (v.adicCompletion K) u_y *
            (algebraMap K (v.adicCompletion K) z_y) ^ 2 *
            (W / algebraMap K (v.adicCompletion K) z_y) ^ 2 =
            algebraMap K (v.adicCompletion K) u_y * W ^ 2 := by
          field_simp [hZy]
        rw [h1, h2, hZW]
      rw [if_pos hsol']
    · exfalso
      revert h_units
      decide
  have hilbFin_eq_one_of_isSquare_right :
      ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (a b : Kˣ),
      IsSquare (algebraMap K (v.adicCompletion K) (b : K)) →
      hilbFin v (a : K) (b : K) = 1 := by
    rintro v a b ⟨s, hs⟩
    have hb0 : algebraMap K (v.adicCompletion K) (b : K) ≠ 0 := by
      rw [ne_eq, map_eq_zero]
      exact b.ne_zero
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hs
      exact hb0 hs
    simp only [hilbFin, hilbLoc]
    rw [if_pos ⟨0, s⁻¹, by rw [hs]; field_simp [hs0]; ring⟩]
  have hilbInf_eq_one_of_isSquare_right :
      ∀ (w : NumberField.InfinitePlace K) (a b : Kˣ),
      IsSquare (algebraMap K w.Completion (b : K)) →
      hilbInf w (a : K) (b : K) = 1 := by
    rintro w a b ⟨s, hs⟩
    have hb0 : algebraMap K w.Completion (b : K) ≠ 0 := by
      rw [ne_eq, map_eq_zero]
      exact b.ne_zero
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hs
      exact hb0 hs
    simp only [hilbInf, hilbInfLoc]
    rw [if_pos ⟨0, s⁻¹, by rw [hs]; field_simp [hs0]; ring⟩]
  intro v₁
  by_cases hv₁ : v₁ ∈ S_fin
  · exact hu_fin v₁ hv₁
  · have hv₁T : v₁ ∉ T := fun h => hv₁ (hT_sub h)
    have h2_v₁ : Valued.v (2 : v₁.adicCompletion K) = 1 := by
      rw [← map_ofNat (algebraMap K (v₁.adicCompletion K)) 2]
      exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v₁ (2 : K)).trans
        (h2_val_outside_T v₁ hv₁T)
    have hex_x : ∃ x : Kˣ,
        Valued.v (algebraMap K (v₁.adicCompletion K) (x : K)) = WithZero.exp (-1 : ℤ) ∧
        (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          v ∉ S_fin → v ≠ v₁ → EvenVal v x) := by
      let R := NumberField.RingOfIntegers K
      have hv₁_nzd : v₁.asIdeal ∈ nonZeroDivisors (Ideal R) :=
        mem_nonZeroDivisors_of_ne_zero v₁.ne_bot
      let J : nonZeroDivisors (Ideal R) := ⟨v₁.asIdeal, hv₁_nzd⟩
      obtain ⟨I, hIc, hI_supp⟩ := hS_fin (ClassGroup.mk0 J)⁻¹
      have hJI_mk0 : ClassGroup.mk0 (J * I) = 1 := by
        rw [map_mul, hIc, mul_inv_cancel]
      have hJI_princ : ((J * I : nonZeroDivisors (Ideal R)) : Ideal R).IsPrincipal :=
        (ClassGroup.mk0_eq_one_iff (J * I).2).mp hJI_mk0
      let x₀ : R := @Submodule.IsPrincipal.generator R R _ _ _
        ((J * I : nonZeroDivisors (Ideal R)) : Ideal R) hJI_princ
      have hx₀_span : Ideal.span ({x₀} : Set R) = v₁.asIdeal * (I : Ideal R) := by
        have hgen := @Ideal.span_singleton_generator R _
          ((J * I : nonZeroDivisors (Ideal R)) : Ideal R) hJI_princ
        exact hgen
      have hx₀_ne : x₀ ≠ 0 := by
        intro h0
        have hbot : Ideal.span ({x₀} : Set R) = ⊥ :=
          Ideal.span_singleton_eq_bot.mpr h0
        have hJI_ne : ((J * I : nonZeroDivisors (Ideal R)) : Ideal R) ≠ 0 :=
          nonZeroDivisors.coe_ne_zero (J * I)
        apply hJI_ne
        change v₁.asIdeal * (I : Ideal R) = 0
        rw [← hx₀_span, hbot, Ideal.zero_eq_bot]
      have hx_K_ne : algebraMap R K x₀ ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hx₀_ne)
      let x : Kˣ := Units.mk0 (algebraMap R K x₀) hx_K_ne
      refine ⟨x, ?_, ?_⟩
      · have hx₀_mem1 : x₀ ∈ v₁.asIdeal ^ 1 := by
          rw [pow_one, ← Ideal.dvd_span_singleton, hx₀_span]
          exact dvd_mul_right v₁.asIdeal (I : Ideal R)
        have hle1 : v₁.intValuation x₀ ≤ WithZero.exp (-(1 : ℕ) : ℤ) :=
          (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v₁ x₀ 1).mpr hx₀_mem1
        have hx₀_not_mem2 : x₀ ∉ v₁.asIdeal ^ 2 := by
          intro hmem2
          have hdvd2 : v₁.asIdeal ^ 2 ∣ Ideal.span ({x₀} : Set R) := by
            rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
            exact hmem2
          rw [hx₀_span, sq] at hdvd2
          have hdvdI : v₁.asIdeal ∣ (I : Ideal R) :=
            (mul_dvd_mul_iff_left v₁.ne_bot).mp hdvd2
          exact hI_supp v₁ hv₁ hdvdI
        have hnot_le2 : ¬ (v₁.intValuation x₀ ≤ WithZero.exp (-(2 : ℕ) : ℤ)) :=
          fun hle2 => hx₀_not_mem2
            ((IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v₁ x₀ 2).mp hle2)
        have hv₁_ne0 : v₁.intValuation x₀ ≠ 0 :=
          IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero v₁ x₀ hx₀_ne
        obtain ⟨k, hk⟩ : ∃ k : ℤ, WithZero.exp k = v₁.intValuation x₀ :=
          ⟨(v₁.intValuation x₀).log, WithZero.exp_log hv₁_ne0⟩
        have hk_le : k ≤ -1 := by
          rw [← hk, Nat.cast_one, WithZero.exp_le_exp] at hle1
          exact hle1
        have hk_gt : ¬ (k ≤ -2) := by
          intro hk2
          apply hnot_le2
          rw [← hk, Nat.cast_ofNat, WithZero.exp_le_exp]
          exact hk2
        have hk_eq : k = -1 := by omega
        have hval_x₀ : v₁.intValuation x₀ = WithZero.exp (-1 : ℤ) := by
          rw [← hk, hk_eq]
        calc Valued.v (algebraMap K (v₁.adicCompletion K) (x : K))
            = IsDedekindDomain.HeightOneSpectrum.valuation K v₁ (algebraMap R K x₀) :=
              IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v₁ (algebraMap R K x₀)
          _ = v₁.intValuation x₀ :=
              IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap v₁ x₀
          _ = WithZero.exp (-1 : ℤ) := hval_x₀
      · intro v hvS hvv₁
        have hx₀_not_mem : x₀ ∉ v.asIdeal := by
          intro hmem
          have hdvd : v.asIdeal ∣ v₁.asIdeal * (I : Ideal R) := by
            rw [← hx₀_span, Ideal.dvd_span_singleton]
            exact hmem
          have hprime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
          rcases hprime.dvd_or_dvd hdvd with hdvd_v₁ | hdvd_I
          · have hle : v₁.asIdeal ≤ v.asIdeal := Ideal.dvd_iff_le.mp hdvd_v₁
            have heq_ideal : v₁.asIdeal = v.asIdeal :=
              v₁.isMaximal.eq_of_le v.isPrime.ne_top hle
            exact hvv₁ (IsDedekindDomain.HeightOneSpectrum.ext heq_ideal.symm)
          · exact hI_supp v hvS hdvd_I
        have hval1 : v.intValuation x₀ = 1 :=
          IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr hx₀_not_mem
        have hval_x : v.valuationOfNeZero x = 1 := by
          rw [← WithZero.coe_inj, IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq]
          change IsDedekindDomain.HeightOneSpectrum.valuation K v (algebraMap R K x₀) = 1
          rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hval1]
        unfold EvenVal
        rw [hval_x, toAdd_one]
        exact Even.zero
    obtain ⟨x, hx_v₁, hx_even⟩ := hex_x
    have hrec := (hilbert_reciprocity x u).2
    have hinf_one : (∏ w : NumberField.InfinitePlace K, hilbInf w (x : K) (u : K)) = 1 := by
      apply Finset.prod_eq_one
      intro w _
      exact hilbInf_eq_one_of_isSquare_right w x u (hu_inf w)
    have hfin_one : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        v ≠ v₁ → hilbFin v (x : K) (u : K) = 1 := by
      intro v hvv₁
      by_cases hvS : v ∈ S_fin
      · exact hilbFin_eq_one_of_isSquare_right v x u (hu_fin v hvS)
      · exact h_hilbFin_evenVal v (fun h => hvS (hT_sub h)) x u
          (hx_even v hvS hvv₁) (hu_even v hvS)
    have hhilb_v₁ : hilbFin v₁ (x : K) (u : K) = 1 := by
      rw [finprod_eq_single _ v₁ hfin_one, hinf_one, mul_one] at hrec
      exact hrec
    obtain ⟨u₀, z₀, hu₀_val, hz₀_ne, hueq⟩ := h_even_factor v₁ u (hu_even v₁ hv₁)
    let X : v₁.adicCompletion K := algebraMap K (v₁.adicCompletion K) (x : K)
    let u' : v₁.adicCompletion K := algebraMap K (v₁.adicCompletion K) u₀
    let z : v₁.adicCompletion K := algebraMap K (v₁.adicCompletion K) z₀
    have hu' : Valued.v u' = 1 :=
      (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v₁ u₀).trans hu₀_val
    have hm : Valued.v X = WithZero.exp (-1 : ℤ) := hx_v₁
    have h_parity : ∀ (m y w : v₁.adicCompletion K),
        Valued.v m = WithZero.exp (-1 : ℤ) → w ≠ 0 →
        Valued.v (m * y ^ 2) ≠ Valued.v w ^ 2 := by
      intro m y w hm_arg hw heq
      have hvw : Valued.v w ≠ 0 := fun h => hw ((Valuation.zero_iff _).mp h)
      have hvy : Valued.v y ≠ 0 := by
        intro h
        rw [Valuation.map_mul, Valuation.map_pow, h, zero_pow (by norm_num), mul_zero] at heq
        exact pow_ne_zero 2 hvw heq.symm
      obtain ⟨a, ha⟩ : ∃ a : ℤ, WithZero.exp a = Valued.v y :=
        ⟨(Valued.v y).log, WithZero.exp_log hvy⟩
      obtain ⟨b, hb⟩ : ∃ b : ℤ, WithZero.exp b = Valued.v w :=
        ⟨(Valued.v w).log, WithZero.exp_log hvw⟩
      rw [Valuation.map_mul, Valuation.map_pow, hm_arg, ← ha, ← hb, sq, sq,
        ← WithZero.exp_add, ← WithZero.exp_add, ← WithZero.exp_add, WithZero.exp_inj] at heq
      omega
    have hsol0 : ∃ y₁ y₂ : v₁.adicCompletion K,
        X * y₁ ^ 2 + algebraMap K (v₁.adicCompletion K) (u : K) * y₂ ^ 2 = 1 := by
      simp only [hilbFin, hilbLoc] at hhilb_v₁
      split_ifs at hhilb_v₁ with h
      · exact h
      · exfalso; revert hhilb_v₁; decide
    rcases hsol0 with ⟨y₁, y₂, hy₁₂⟩
    let x₁ : v₁.adicCompletion K := z * y₂
    have hxy : u' * x₁ ^ 2 + X * y₁ ^ 2 = 1 := by
      have hU_eq : algebraMap K (v₁.adicCompletion K) (u : K) = u' * z ^ 2 := by
        change algebraMap K (v₁.adicCompletion K) (u : K) =
          algebraMap K (v₁.adicCompletion K) u₀ * (algebraMap K (v₁.adicCompletion K) z₀) ^ 2
        rw [hueq, map_mul, map_pow]
      dsimp [x₁]
      linear_combination hy₁₂ - hU_eq * y₂ ^ 2
    have hmy : X * y₁ ^ 2 = 1 - u' * x₁ ^ 2 := by linear_combination hxy
    have hvx₁ : Valued.v x₁ = 1 := by
      rcases lt_trichotomy (Valued.v x₁) 1 with hlt | heq | hgt
      · exfalso
        refine h_parity X y₁ 1 hm one_ne_zero ?_
        have hux : Valued.v (u' * x₁ ^ 2) < Valued.v (1 : v₁.adicCompletion K) := by
          rw [Valuation.map_mul, hu', one_mul, Valuation.map_pow, Valuation.map_one]
          exact pow_lt_one₀ zero_le' hlt (by norm_num)
        rw [hmy, Valuation.map_sub_eq_of_lt_left _ hux, Valuation.map_one, one_pow]
      · exact heq
      · exfalso
        have hx₁0 : x₁ ≠ 0 := by
          intro h; rw [h, Valuation.map_zero] at hgt; exact not_lt_of_ge zero_le' hgt
        refine h_parity X y₁ x₁ hm hx₁0 ?_
        have hux : Valued.v (1 : v₁.adicCompletion K) < Valued.v (u' * x₁ ^ 2) := by
          rw [Valuation.map_mul, hu', one_mul, Valuation.map_pow, Valuation.map_one]
          exact one_lt_pow₀ hgt (by norm_num)
        rw [hmy, Valuation.map_sub_eq_of_lt_right _ hux, Valuation.map_mul, hu', one_mul,
          Valuation.map_pow]
    have hx₁0 : x₁ ≠ 0 := by
      intro h; rw [h, Valuation.map_zero] at hvx₁; exact zero_ne_one hvx₁
    have hmy_le : Valued.v (X * y₁ ^ 2) ≤ 1 := by
      rw [hmy]
      refine le_trans (Valuation.map_sub _ _ _) (max_le (by rw [Valuation.map_one]) ?_)
      rw [Valuation.map_mul, hu', Valuation.map_pow, hvx₁, one_pow, mul_one]
    have hmy_ne : Valued.v (X * y₁ ^ 2) ≠ 1 := by
      intro h1
      refine h_parity X y₁ 1 hm one_ne_zero ?_
      rw [h1, Valuation.map_one, one_pow]
    have hmy_lt : Valued.v (X * y₁ ^ 2) < 1 := lt_of_le_of_ne hmy_le hmy_ne
    have hx₁inv : Valued.v (x₁⁻¹) = 1 := by rw [map_inv₀, hvx₁, inv_one]
    have hdiff : u' - (x₁⁻¹) ^ 2 = -((X * y₁ ^ 2) / x₁ ^ 2) := by
      field_simp [hx₁0]; linear_combination hxy
    have hdiff_lt : Valued.v (u' - (x₁⁻¹) ^ 2) < 1 := by
      rw [hdiff, Valuation.map_neg, Valuation.map_div, Valuation.map_pow, hvx₁, one_pow, div_one]
      exact hmy_lt
    obtain ⟨t, ht⟩ := exists_sq_of_valued_sub_sq_lt_one v₁ h2_v₁ u' (x₁⁻¹) hx₁inv hdiff_lt
    refine ⟨t * z, ?_⟩
    change algebraMap K (v₁.adicCompletion K) (u : K) = (t * z) * (t * z)
    rw [hueq, map_mul, map_pow]
    change u' * z ^ 2 = (t * z) * (t * z)
    rw [← ht]
    ring

theorem exists_quadratic_extension_and_involution {K : Type u} [Field K] [NumberField K]
    (u : Kˣ) (hu_not_sq : ¬ IsSquare (u : K)) :
    ∃ (L : Type u) (instF : Field L) (instNF : NumberField L) (instAlg : Algebra K L),
      letI := instF; letI := instNF; letI := instAlg;
      ∃ (θ : L) (σ : L ≃ₐ[K] L) (N : Lˣ →* Kˣ),
        Module.finrank K L = 2 ∧
        θ ^ 2 = algebraMap K L (u : K) ∧
        σ θ = -θ ∧
        (∀ z : L, σ (σ z) = z) ∧
        (∀ z : L, ∃ a b : K, z = algebraMap K L a + algebraMap K L b * θ) ∧
        (∀ (φ₀ : K →+* ℂ) (s : ℂ), s ^ 2 = φ₀ (u : K) →
          ∃ φ : L →+* ℂ, φ.comp (algebraMap K L) = φ₀ ∧ φ θ = s) ∧
        (∀ y : Lˣ, algebraMap K L ((N y : Kˣ) : K) = (y : L) * σ (y : L)) :=
by
  classical
  let f : Polynomial K := Polynomial.X ^ 2 - Polynomial.C (u : K)
  have hf_monic : f.Monic := Polynomial.monic_X_pow_sub_C (u : K) (by decide : (2 : ℕ) ≠ 0)
  have hf_deg : f.natDegree = 2 := Polynomial.natDegree_X_pow_sub_C
  have hf_ne_zero : f ≠ 0 := hf_monic.ne_zero
  have hf_roots : f.roots = 0 := by
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro r hr
    rw [Polynomial.mem_roots hf_ne_zero, Polynomial.IsRoot.def] at hr
    simp only [f, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at hr
    apply hu_not_sq
    refine ⟨r, ?_⟩
    linear_combination -hr
  have hf_irr : Irreducible f :=
    (hf_monic.irreducible_iff_roots_eq_zero_of_degree_le_three
      (by omega) (by omega)).mpr hf_roots
  haveI : Fact (Irreducible f) := ⟨hf_irr⟩
  let L : Type u := AdjoinRoot f
  let instF : Field L := inferInstance
  let instAlg : Algebra K L := inferInstance
  let θ : L := AdjoinRoot.root f
  let pb : PowerBasis K L := AdjoinRoot.powerBasis hf_ne_zero
  have hpb_gen : pb.gen = θ := AdjoinRoot.powerBasis_gen hf_ne_zero
  have hpb_dim : pb.dim = 2 := by
    rw [AdjoinRoot.powerBasis_dim hf_ne_zero, hf_deg]
  have hfinrank : Module.finrank K L = 2 := by
    rw [PowerBasis.finrank pb, hpb_dim]
  haveI : CharZero L := charZero_of_injective_algebraMap (RingHom.injective (algebraMap K L))
  haveI : Module.Finite K L := PowerBasis.finite pb
  haveI : Module.Finite ℚ L := Module.Finite.trans K L
  let instNF : NumberField L := NumberField.mk
  have hθ : θ ^ 2 = algebraMap K L (u : K) := by
    have h0 : Polynomial.eval₂ (AdjoinRoot.of f) θ f = 0 := AdjoinRoot.eval₂_root f
    simp only [f, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, ← AdjoinRoot.algebraMap_eq f] at h0
    exact sub_eq_zero.mp h0
  have hspan : ∀ z : L, ∃ a b : K, z = algebraMap K L a + algebraMap K L b * θ := by
    intro z
    let e : Fin 2 ≃ Fin pb.dim := (finCongr hpb_dim).symm
    have hz_sum := (Module.Basis.sum_equivFun pb.basis z).symm
    rw [← Equiv.sum_comp e] at hz_sum
    rw [Fin.sum_univ_two] at hz_sum
    have hb0 : pb.basis (e 0) = 1 := by
      have he0 : (e 0 : ℕ) = 0 := by simp [e]
      rw [PowerBasis.basis_eq_pow, he0, pow_zero]
    have hb1 : pb.basis (e 1) = θ := by
      have he1 : (e 1 : ℕ) = 1 := by simp [e]
      rw [PowerBasis.basis_eq_pow, he1, pow_one, hpb_gen]
    rw [hb0, hb1, Algebra.smul_def, Algebra.smul_def, mul_one] at hz_sum
    exact ⟨pb.basis.equivFun z (e 0), pb.basis.equivFun z (e 1), hz_sum⟩
  have hlift : ∀ (φ₀ : K →+* ℂ) (s : ℂ), s ^ 2 = φ₀ (u : K) →
      ∃ φ : L →+* ℂ, φ.comp (algebraMap K L) = φ₀ ∧ φ θ = s := by
    intro φ₀ s hs
    have heval : Polynomial.eval₂ φ₀ s f = 0 := by
      simp only [f, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, hs, sub_self]
    refine ⟨AdjoinRoot.lift φ₀ s heval, ?_, AdjoinRoot.lift_root heval⟩
    ext x
    exact AdjoinRoot.lift_of heval
  have heval_neg : Polynomial.eval₂ (Algebra.ofId K L : K →+* L) (-θ) f = 0 := by
    change Polynomial.eval₂ (Algebra.ofId K L : K →+* L) (-θ)
      (Polynomial.X ^ 2 - Polynomial.C (u : K)) = 0
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, neg_sq]
    change θ ^ 2 - algebraMap K L (u : K) = 0
    rw [hθ, sub_self]
  let σ₀ : L →ₐ[K] L := AdjoinRoot.liftAlgHom f (Algebra.ofId K L) (-θ) heval_neg
  have hσ₀_θ : σ₀ θ = -θ := AdjoinRoot.liftAlgHom_root f (Algebra.ofId K L) (-θ) heval_neg
  have hσ₀_comp : σ₀.comp σ₀ = AlgHom.id K L := by
    apply AdjoinRoot.algHom_ext
    change σ₀ (σ₀ θ) = θ
    rw [hσ₀_θ, map_neg, hσ₀_θ, neg_neg]
  let σ : L ≃ₐ[K] L := AlgEquiv.ofAlgHom σ₀ σ₀ hσ₀_comp hσ₀_comp
  have hσθ : σ θ = -θ := hσ₀_θ
  have hσ_inv : ∀ z : L, σ (σ z) = z := by
    intro z
    exact AlgHom.congr_fun hσ₀_comp z
  have h_norm_ex : ∀ z : L, ∃ k : K, algebraMap K L k = z * σ z := by
    intro z
    obtain ⟨a, b, rfl⟩ := hspan z
    refine ⟨a ^ 2 - b ^ 2 * (u : K), ?_⟩
    have hσz : σ (algebraMap K L a + algebraMap K L b * θ) =
        algebraMap K L a + algebraMap K L b * (-θ) := by
      rw [map_add, map_mul, σ.commutes a, σ.commutes b, hσθ]
    rw [hσz, map_sub, map_mul, map_pow, map_pow, ← hθ]
    ring
  let N₀ : L → K := fun z => Classical.choose (h_norm_ex z)
  have hN₀ : ∀ z : L, algebraMap K L (N₀ z) = z * σ z :=
    fun z => Classical.choose_spec (h_norm_ex z)
  have hN₀_one : N₀ 1 = 1 := by
    apply (algebraMap K L).injective
    rw [hN₀ 1, map_one, one_mul, map_one]
  have hN₀_mul : ∀ z w : L, N₀ (z * w) = N₀ z * N₀ w := by
    intro z w
    apply (algebraMap K L).injective
    rw [map_mul, hN₀ (z * w), hN₀ z, hN₀ w, map_mul]
    ring
  let N₀_hom : L →* K :=
    { toFun := N₀
      map_one' := hN₀_one
      map_mul' := hN₀_mul }
  let N : Lˣ →* Kˣ := Units.map N₀_hom
  have hN : ∀ y : Lˣ, algebraMap K L ((N y : Kˣ) : K) = (y : L) * σ (y : L) := by
    intro y
    exact hN₀ (y : L)
  exact ⟨L, instF, instNF, instAlg, θ, σ, N, hfinrank, hθ, hσθ, hσ_inv, hspan, hlift, hN⟩

theorem quadratic_extension_nrRealPlaces_add_nrComplexPlaces {K L : Type u}
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hfinrank : Module.finrank K L = 2)
    (u : Kˣ)
    (hu_inf : ∀ w : NumberField.InfinitePlace K, IsSquare (algebraMap K w.Completion (u : K)))
    (θ : L) (hθ : θ ^ 2 = algebraMap K L (u : K))
    (hspan : ∀ z : L, ∃ a b : K, z = algebraMap K L a + algebraMap K L b * θ)
    (hlift : ∀ (φ₀ : K →+* ℂ) (s : ℂ), s ^ 2 = φ₀ (u : K) →
      ∃ φ : L →+* ℂ, φ.comp (algebraMap K L) = φ₀ ∧ φ θ = s) :
    NumberField.InfinitePlace.nrRealPlaces L + NumberField.InfinitePlace.nrComplexPlaces L =
      2 * (NumberField.InfinitePlace.nrRealPlaces K + NumberField.InfinitePlace.nrComplexPlaces K) :=
by
  classical
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hdeg : NumberField.InfinitePlace.nrRealPlaces L + 2 * NumberField.InfinitePlace.nrComplexPlaces L =
      2 * (NumberField.InfinitePlace.nrRealPlaces K + 2 * NumberField.InfinitePlace.nrComplexPlaces K) := by
    have hK := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
    have hL := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank L
    have hmul := Module.finrank_mul_finrank ℚ K L
    rw [hfinrank] at hmul
    omega
  have isReal_iff_conj : ∀ {F : Type u} [Field F] (ψ : F →+* ℂ),
      NumberField.ComplexEmbedding.IsReal ψ ↔ ∀ x : F, starRingEnd ℂ (ψ x) = ψ x := by
    intro F _ ψ
    rw [NumberField.ComplexEmbedding.isReal_iff, RingHom.ext_iff]
    simp only [NumberField.ComplexEmbedding.conjugate_coe_eq]
  have isReal_comp : ∀ (φ : L →+* ℂ),
      NumberField.ComplexEmbedding.IsReal φ →
      NumberField.ComplexEmbedding.IsReal (φ.comp (algebraMap K L)) := by
    intro φ hφ
    rw [isReal_iff_conj] at hφ ⊢
    intro a
    exact hφ (algebraMap K L a)
  have isReal_of_comp_and_theta : ∀ (φ : L →+* ℂ),
      NumberField.ComplexEmbedding.IsReal (φ.comp (algebraMap K L)) →
      starRingEnd ℂ (φ θ) = φ θ →
      NumberField.ComplexEmbedding.IsReal φ := by
    intro φ hφ₀ hφθ
    rw [isReal_iff_conj] at hφ₀ ⊢
    intro z
    obtain ⟨a, b, rfl⟩ := hspan z
    have ha : starRingEnd ℂ (φ (algebraMap K L a)) = φ (algebraMap K L a) := hφ₀ a
    have hb : starRingEnd ℂ (φ (algebraMap K L b)) = φ (algebraMap K L b) := hφ₀ b
    simp only [map_add, map_mul, ha, hb, hφθ]
  have hom_ext_of_comp_and_theta : ∀ (φ₁ φ₂ : L →+* ℂ),
      φ₁.comp (algebraMap K L) = φ₂.comp (algebraMap K L) →
      φ₁ θ = φ₂ θ → φ₁ = φ₂ := by
    intro φ₁ φ₂ hcomp hθ_eq
    ext z
    obtain ⟨a, b, rfl⟩ := hspan z
    have ha : φ₁ (algebraMap K L a) = φ₂ (algebraMap K L a) :=
      RingHom.congr_fun hcomp a
    have hb : φ₁ (algebraMap K L b) = φ₂ (algebraMap K L b) :=
      RingHom.congr_fun hcomp b
    simp only [map_add, map_mul, ha, hb, hθ_eq]
  have hr_ex : ∀ φ₀ : { φ₀ : K →+* ℂ // NumberField.ComplexEmbedding.IsReal φ₀ },
      ∃ r : ℝ, 0 < r ∧ ((r : ℝ) : ℂ) ^ 2 = φ₀.1 (u : K) := by
    rintro ⟨φ₀, hφ₀⟩
    let w : NumberField.InfinitePlace K := NumberField.InfinitePlace.mk φ₀
    have hw : w.IsReal := NumberField.InfinitePlace.isReal_mk_iff.mpr hφ₀
    have hw_emb : w.embedding = φ₀ := NumberField.InfinitePlace.embedding_mk_eq_of_isReal hφ₀
    let ψ : K →+* ℝ := NumberField.InfinitePlace.embedding_of_isReal hw
    let Φ : w.Completion →+* ℝ := NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
    obtain ⟨z, hz⟩ := hu_inf w
    have hΦ : ψ (u : K) = Φ z * Φ z := by
      have h1 : Φ (algebraMap K w.Completion (u : K)) = ψ (u : K) :=
        NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw (u : K)
      rw [← h1, hz, map_mul]
    have hψ_nonneg : 0 ≤ ψ (u : K) := by
      rw [hΦ]
      exact mul_self_nonneg (Φ z)
    have hψ_ne : ψ (u : K) ≠ 0 := (map_ne_zero ψ).mpr u.ne_zero
    have hψ_pos : 0 < ψ (u : K) := lt_of_le_of_ne hψ_nonneg hψ_ne.symm
    refine ⟨Real.sqrt (ψ (u : K)), Real.sqrt_pos.mpr hψ_pos, ?_⟩
    have hsq : Real.sqrt (ψ (u : K)) ^ 2 = ψ (u : K) := Real.sq_sqrt hψ_nonneg
    have h_emb : ((ψ (u : K) : ℝ) : ℂ) = φ₀ (u : K) := by
      rw [← hw_emb]
      exact NumberField.InfinitePlace.embedding_of_isReal_apply hw (u : K)
    rw [← Complex.ofReal_pow, hsq, h_emb]
  choose r hr_pos hr_sq using hr_ex
  let s : { φ₀ : K →+* ℂ // NumberField.ComplexEmbedding.IsReal φ₀ } → Bool → ℂ :=
    fun φ₀ b => if b then ((r φ₀ : ℝ) : ℂ) else -((r φ₀ : ℝ) : ℂ)
  have hs_sq : ∀ φ₀ b, (s φ₀ b) ^ 2 = φ₀.1 (u : K) := by
    intro φ₀ b
    cases b <;> simp [s, hr_sq φ₀]
  have hs_conj : ∀ φ₀ b, starRingEnd ℂ (s φ₀ b) = s φ₀ b := by
    intro φ₀ b
    cases b <;> simp [s, Complex.conj_ofReal]
  have hlift_ex : ∀ φ₀ b, ∃ φ : L →+* ℂ,
      φ.comp (algebraMap K L) = φ₀.1 ∧ φ θ = s φ₀ b :=
    fun φ₀ b => hlift φ₀.1 (s φ₀ b) (hs_sq φ₀ b)
  choose lift hlift_comp hlift_θ using hlift_ex
  have hlift_real : ∀ φ₀ b, NumberField.ComplexEmbedding.IsReal (lift φ₀ b) := by
    intro φ₀ b
    apply isReal_of_comp_and_theta (lift φ₀ b)
    · rw [hlift_comp φ₀ b]
      exact φ₀.2
    · rw [hlift_θ φ₀ b]
      exact hs_conj φ₀ b
  let e : { φ : L →+* ℂ // NumberField.ComplexEmbedding.IsReal φ } ≃
      { φ₀ : K →+* ℂ // NumberField.ComplexEmbedding.IsReal φ₀ } × Bool :=
    { toFun := fun φ => (⟨φ.1.comp (algebraMap K L), isReal_comp φ.1 φ.2⟩, decide (0 < (φ.1 θ).re))
      invFun := fun p => ⟨lift p.1 p.2, hlift_real p.1 p.2⟩
      left_inv := by
        rintro ⟨φ, hφ⟩
        ext1
        let φ₀ : { φ₀ : K →+* ℂ // NumberField.ComplexEmbedding.IsReal φ₀ } :=
          ⟨φ.comp (algebraMap K L), isReal_comp φ hφ⟩
        let b : Bool := decide (0 < (φ θ).re)
        apply hom_ext_of_comp_and_theta (lift φ₀ b) φ (hlift_comp φ₀ b)
        rw [hlift_θ φ₀ b]
        have hθ_sq : (φ θ) ^ 2 = ((r φ₀ : ℝ) : ℂ) ^ 2 := by
          calc (φ θ) ^ 2 = φ (θ ^ 2) := (map_pow φ θ 2).symm
            _ = φ (algebraMap K L (u : K)) := by rw [hθ]
            _ = φ₀.1 (u : K) := rfl
            _ = ((r φ₀ : ℝ) : ℂ) ^ 2 := (hr_sq φ₀).symm
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hθ_sq with h_pos | h_neg
        · have hre : 0 < (φ θ).re := by
            rw [h_pos, Complex.ofReal_re]
            exact hr_pos φ₀
          have hb : b = true := decide_eq_true_eq.mpr hre
          dsimp [s]
          rw [hb, if_pos rfl, h_pos]
        · have hre : ¬ (0 < (φ θ).re) := by
            rw [h_neg, Complex.neg_re, Complex.ofReal_re, not_lt]
            linarith [hr_pos φ₀]
          have hb : b = false := decide_eq_false_iff_not.mpr hre
          dsimp [s]
          rw [hb]
          simp [h_neg]
      right_inv := by
        rintro ⟨φ₀, b⟩
        ext1
        · ext1
          exact hlift_comp φ₀ b
        · dsimp
          rw [hlift_θ φ₀ b]
          cases b
          · dsimp [s]
            rw [decide_eq_false_iff_not, not_lt]
            linarith [hr_pos φ₀]
          · dsimp [s]
            rw [decide_eq_true_eq]
            exact hr_pos φ₀ }
  have hreal_card : NumberField.InfinitePlace.nrRealPlaces L =
      2 * NumberField.InfinitePlace.nrRealPlaces K := by
    rw [← NumberField.InfinitePlace.card_real_embeddings L,
        ← NumberField.InfinitePlace.card_real_embeddings K,
        Fintype.card_congr e, Fintype.card_prod, Fintype.card_bool, Nat.mul_comm]
  omega

theorem exists_integral_splitting_elem_of_local_square {K L : Type u}
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (u : Kˣ)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hu_v : IsSquare (algebraMap K (v.adicCompletion K) (u : K)))
    (θ : L) (hθ : θ ^ 2 = algebraMap K L (u : K))
    (σ : L ≃ₐ[K] L) (hσθ : σ θ = -θ) :
    ∃ (d_v m_v : NumberField.RingOfIntegers K) (η : NumberField.RingOfIntegers L),
      d_v ∉ v.asIdeal ∧
      m_v ∈ v.asIdeal ∧
      η + (NumberField.RingOfIntegers.mapRingEquiv σ.toRingEquiv) η =
        algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) d_v ∧
      η * (NumberField.RingOfIntegers.mapRingEquiv σ.toRingEquiv) η =
        algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) m_v :=
by
  classical
  let F_v := v.adicCompletion K
  obtain ⟨s_v, hs_v_sq⟩ := hu_v
  have hu_ne : algebraMap K F_v (u : K) ≠ 0 := (map_ne_zero _).mpr u.ne_zero
  have hs_v : s_v ≠ 0 := by
    intro h0
    apply hu_ne
    rw [hs_v_sq, h0, mul_zero]
  have hs_v_inv : s_v⁻¹ ≠ 0 := inv_ne_zero hs_v
  have h4_K : (4 : K) ≠ 0 := by norm_num
  have h4_Fv_ne : (4 : F_v) ≠ 0 := by
    rw [show (4 : F_v) = algebraMap K F_v 4 from (map_ofNat _ 4).symm]
    exact (map_ne_zero _).mpr h4_K
  let γ : WithZero (Multiplicative ℤ) := Valued.v (s_v⁻¹) * Valued.v (4 : F_v)
  have hγ_ne : γ ≠ 0 :=
    mul_ne_zero ((Valuation.ne_zero_iff Valued.v).mpr hs_v_inv)
      ((Valuation.ne_zero_iff Valued.v).mpr h4_Fv_ne)
  have hγ_pos : 0 < γ := zero_lt_iff.mpr hγ_ne
  have hopen : IsOpen {z : F_v | Valued.v (z - s_v⁻¹) < γ} :=
    (Valued.isOpen_ball F_v γ).preimage (continuous_sub_right s_v⁻¹)
  have hne : {z : F_v | Valued.v (z - s_v⁻¹) < γ}.Nonempty := by
    refine ⟨s_v⁻¹, ?_⟩
    simp only [Set.mem_setOf_eq, sub_self, map_zero]
    exact hγ_pos
  have hdense : DenseRange (fun y : K => algebraMap K F_v y) := by
    have h1 := IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion
        (NumberField.RingOfIntegers K) K (S := K) v
    have hsurj : Function.Surjective (⇑(algebraMap K K)) := fun a =>
      ⟨a, by rw [Algebra.algebraMap_self, RingHom.id_apply]⟩
    have h2 : Set.range (⇑(algebraMap K F_v)) =
        Set.range (UniformSpace.Completion.coe' :
          WithVal (IsDedekindDomain.HeightOneSpectrum.valuation K v) → F_v) := by
      rw [h1]
      exact hsurj.range_comp _
    have h3 : DenseRange (UniformSpace.Completion.coe' :
        WithVal (IsDedekindDomain.HeightOneSpectrum.valuation K v) → F_v) :=
      UniformSpace.Completion.denseRange_coe
    show Dense (Set.range (fun y : K => algebraMap K F_v y))
    rw [show Set.range (fun y : K => algebraMap K F_v y)
        = Set.range (⇑(algebraMap K F_v)) from rfl, h2]
    exact h3
  obtain ⟨c₀, hc₀⟩ := hdense.exists_mem_open hopen hne
  simp only [Set.mem_setOf_eq] at hc₀
  let b_v : K := ((u : K) * c₀ ^ 2 - 1) / 4
  let δ : F_v := algebraMap K F_v c₀ * s_v - 1
  have hδ_eq : δ = (algebraMap K F_v c₀ - s_v⁻¹) * s_v := by
    dsimp [δ]
    rw [sub_mul, inv_mul_cancel₀ hs_v]
  have hsv_pos : 0 < Valued.v s_v :=
    zero_lt_iff.mpr ((Valuation.ne_zero_iff Valued.v).mpr hs_v)
  have hsv_inv_mul : Valued.v (s_v⁻¹) * Valued.v s_v = 1 := by
    rw [← Valuation.map_mul, inv_mul_cancel₀ hs_v, Valuation.map_one]
  have hδ_lt_4 : Valued.v δ < Valued.v (4 : F_v) := by
    calc Valued.v δ
      _ = Valued.v (algebraMap K F_v c₀ - s_v⁻¹) * Valued.v s_v := by
        rw [hδ_eq, Valuation.map_mul]
      _ < γ * Valued.v s_v := mul_lt_mul_of_pos_right hc₀ hsv_pos
      _ = Valued.v (4 : F_v) * (Valued.v (s_v⁻¹) * Valued.v s_v) := by
        dsimp [γ]; ac_rfl
      _ = Valued.v (4 : F_v) := by rw [hsv_inv_mul, mul_one]
  have hval1_le_1 : Valued.v (1 : F_v) ≤ 1 := le_of_eq (Valuation.map_one _)
  have hval2_le_1 : Valued.v (2 : F_v) ≤ 1 := by
    rw [show (2 : F_v) = 1 + 1 by ring]
    exact le_trans (Valuation.map_add _ 1 1) (max_le hval1_le_1 hval1_le_1)
  have hval4_le_1 : Valued.v (4 : F_v) ≤ 1 := by
    rw [show (4 : F_v) = 2 + 2 by ring]
    exact le_trans (Valuation.map_add _ 2 2) (max_le hval2_le_1 hval2_le_1)
  have hδ_le_1 : Valued.v δ ≤ 1 := le_trans (le_of_lt hδ_lt_4) hval4_le_1
  have h2δ_le_1 : Valued.v ((2 : F_v) + δ) ≤ 1 := by
    calc Valued.v ((2 : F_v) + δ)
      _ ≤ max (Valued.v (2 : F_v)) (Valued.v δ) := Valuation.map_add _ _ _
      _ ≤ 1 := max_le hval2_le_1 hδ_le_1
  have hbv_4_eq : algebraMap K F_v b_v * (4 : F_v) = δ * ((2 : F_v) + δ) := by
    have hb4 : b_v * 4 = (u : K) * c₀ ^ 2 - 1 := by
      dsimp [b_v]
      exact div_mul_cancel₀ _ h4_K
    calc algebraMap K F_v b_v * (4 : F_v)
      _ = algebraMap K F_v (b_v * 4) := by rw [map_mul, map_ofNat]
      _ = algebraMap K F_v ((u : K) * c₀ ^ 2 - 1) := by rw [hb4]
      _ = algebraMap K F_v (u : K) * (algebraMap K F_v c₀) ^ 2 - 1 := by
        rw [map_sub, map_mul, map_pow, map_one]
      _ = (s_v * s_v) * (algebraMap K F_v c₀) ^ 2 - 1 := by rw [hs_v_sq]
      _ = δ * ((2 : F_v) + δ) := by dsimp [δ]; ring
  have hb_v_lt_1 : (IsDedekindDomain.HeightOneSpectrum.valuation K v) b_v < 1 := by
    rw [← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v b_v]
    apply lt_of_mul_lt_mul_right' (a := Valued.v (4 : F_v))
    calc Valued.v (algebraMap K F_v b_v) * Valued.v (4 : F_v)
      _ = Valued.v (algebraMap K F_v b_v * (4 : F_v)) := (Valuation.map_mul _ _ _).symm
      _ = Valued.v (δ * ((2 : F_v) + δ)) := by rw [hbv_4_eq]
      _ = Valued.v δ * Valued.v ((2 : F_v) + δ) := Valuation.map_mul _ _ _
      _ ≤ Valued.v δ * 1 := mul_le_mul_right h2δ_le_1 (Valued.v δ)
      _ = Valued.v δ := mul_one _
      _ < Valued.v (4 : F_v) := hδ_lt_4
      _ = 1 * Valued.v (4 : F_v) := (one_mul _).symm
  obtain ⟨α₀, β₀, hβ₀_mem, hαβ⟩ :=
    IsFractionRing.div_surjective (A := NumberField.RingOfIntegers K) b_v
  have hβ₀_ne : β₀ ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hβ₀_mem
  have hβ₀_K_ne : algebraMap (NumberField.RingOfIntegers K) K β₀ ≠ 0 :=
    IsFractionRing.to_map_eq_zero_iff.not.mpr hβ₀_ne
  have hα₀_eq : algebraMap (NumberField.RingOfIntegers K) K α₀ =
      b_v * algebraMap (NumberField.RingOfIntegers K) K β₀ := by
    rw [← hαβ, div_mul_cancel₀ _ hβ₀_K_ne]
  let n : ℕ := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {β₀})).factors
  have hv_β₀ : v.intValuation β₀ = WithZero.exp (-(n : ℤ)) := by
    rw [v.intValuation_if_neg hβ₀_ne]
  have hdvd_n : v.asIdeal ^ n ∣ Ideal.span {β₀} := by
    rw [← v.intValuation_le_pow_iff_dvd β₀ n, hv_β₀]
  obtain ⟨I₀, hI₀⟩ := hdvd_n
  have hnot_dvd_succ : ¬ (v.asIdeal ^ (n + 1) ∣ Ideal.span {β₀}) := by
    rw [← v.intValuation_le_pow_iff_dvd β₀ (n + 1), hv_β₀, WithZero.exp_le_exp]
    omega
  have hI₀_not_le : ¬ (I₀ ≤ v.asIdeal) := by
    intro hle
    apply hnot_dvd_succ
    rw [hI₀, pow_succ]
    exact mul_dvd_mul_left (v.asIdeal ^ n) (Ideal.dvd_iff_le.mpr hle)
  obtain ⟨d_v, hd_v_I₀, hd_v_not_mem⟩ := Set.not_subset.mp hI₀_not_le
  have hα₀_mem : α₀ ∈ v.asIdeal ^ n := by
    rw [← v.intValuation_le_pow_iff_mem α₀ n]
    have hval_α₀ : v.intValuation α₀ =
        (IsDedekindDomain.HeightOneSpectrum.valuation K v) b_v * v.intValuation β₀ := by
      calc v.intValuation α₀
        _ = (IsDedekindDomain.HeightOneSpectrum.valuation K v)
              (algebraMap (NumberField.RingOfIntegers K) K α₀) :=
          (v.valuation_of_algebraMap α₀).symm
        _ = (IsDedekindDomain.HeightOneSpectrum.valuation K v)
              (b_v * algebraMap (NumberField.RingOfIntegers K) K β₀) := by rw [hα₀_eq]
        _ = (IsDedekindDomain.HeightOneSpectrum.valuation K v) b_v *
              (IsDedekindDomain.HeightOneSpectrum.valuation K v)
                (algebraMap (NumberField.RingOfIntegers K) K β₀) := Valuation.map_mul _ _ _
        _ = (IsDedekindDomain.HeightOneSpectrum.valuation K v) b_v * v.intValuation β₀ := by
          rw [v.valuation_of_algebraMap]
    rw [hval_α₀, hv_β₀]
    calc (IsDedekindDomain.HeightOneSpectrum.valuation K v) b_v * WithZero.exp (-(n : ℤ))
      _ ≤ 1 * WithZero.exp (-(n : ℤ)) :=
        mul_le_mul_left (le_of_lt hb_v_lt_1) _
      _ = WithZero.exp (-(n : ℤ)) := one_mul _
  have hαd_mem : α₀ * d_v ∈ Ideal.span {β₀} := by
    rw [hI₀]
    exact Ideal.mul_mem_mul hα₀_mem hd_v_I₀
  obtain ⟨a_v, ha_v_eq⟩ := Ideal.mem_span_singleton.mp hαd_mem
  have ha_v_K : algebraMap (NumberField.RingOfIntegers K) K a_v =
      algebraMap (NumberField.RingOfIntegers K) K d_v * b_v := by
    apply mul_left_cancel₀ hβ₀_K_ne
    calc algebraMap (NumberField.RingOfIntegers K) K β₀ *
          algebraMap (NumberField.RingOfIntegers K) K a_v
      _ = algebraMap (NumberField.RingOfIntegers K) K (β₀ * a_v) := (map_mul _ _ _).symm
      _ = algebraMap (NumberField.RingOfIntegers K) K (α₀ * d_v) := by rw [← ha_v_eq]
      _ = algebraMap (NumberField.RingOfIntegers K) K α₀ *
          algebraMap (NumberField.RingOfIntegers K) K d_v := map_mul _ _ _
      _ = (b_v * algebraMap (NumberField.RingOfIntegers K) K β₀) *
          algebraMap (NumberField.RingOfIntegers K) K d_v := by rw [hα₀_eq]
      _ = algebraMap (NumberField.RingOfIntegers K) K β₀ *
          (algebraMap (NumberField.RingOfIntegers K) K d_v * b_v) := by ring
  have ha_v_val_lt : (IsDedekindDomain.HeightOneSpectrum.valuation K v) (a_v : K) < 1 := by
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, ha_v_K, Valuation.map_mul]
    calc (IsDedekindDomain.HeightOneSpectrum.valuation K v)
          (algebraMap (NumberField.RingOfIntegers K) K d_v) *
          (IsDedekindDomain.HeightOneSpectrum.valuation K v) b_v
      _ ≤ 1 * (IsDedekindDomain.HeightOneSpectrum.valuation K v) b_v :=
        mul_le_mul_left (v.valuation_le_one d_v) _
      _ = (IsDedekindDomain.HeightOneSpectrum.valuation K v) b_v := one_mul _
      _ < 1 := hb_v_lt_1
  have ha_v_mem : a_v ∈ v.asIdeal := (v.valuation_lt_one_iff_mem a_v).mp ha_v_val_lt
  have hd_v_rel_K : algebraMap (NumberField.RingOfIntegers K) K d_v * ((u : K) * c₀ ^ 2 - 1) =
      4 * algebraMap (NumberField.RingOfIntegers K) K a_v := by
    rw [ha_v_K]
    dsimp [b_v]
    ring
  let m_v : NumberField.RingOfIntegers K := -d_v * a_v
  have hm_v_mem : m_v ∈ v.asIdeal := v.asIdeal.mul_mem_left (-d_v) ha_v_mem
  let η₀ : L := algebraMap (NumberField.RingOfIntegers K) L d_v * (algebraMap K L c₀ * θ + 1) / 2
  have hOK_L_eq : ∀ r : NumberField.RingOfIntegers K,
      algebraMap (NumberField.RingOfIntegers K) L r =
      algebraMap K L (algebraMap (NumberField.RingOfIntegers K) K r) :=
    fun r => IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers K) K L r
  have hσ_OK : ∀ r : NumberField.RingOfIntegers K,
      σ (algebraMap (NumberField.RingOfIntegers K) L r) =
      algebraMap (NumberField.RingOfIntegers K) L r := by
    intro r
    rw [hOK_L_eq r, σ.commutes]
  have hσ_η₀ : σ η₀ =
      algebraMap (NumberField.RingOfIntegers K) L d_v * (algebraMap K L c₀ * (-θ) + 1) / 2 := by
    dsimp [η₀]
    rw [map_div₀, map_mul, hσ_OK d_v, map_add, map_mul, σ.commutes c₀, hσθ, map_one, map_ofNat]
  have hη₀_tr : η₀ + σ η₀ = algebraMap (NumberField.RingOfIntegers K) L d_v := by
    rw [hσ_η₀]
    dsimp [η₀]
    ring
  have hd_v_rel_L : algebraMap (NumberField.RingOfIntegers K) L d_v *
      (algebraMap K L (u : K) * (algebraMap K L c₀) ^ 2 - 1) =
      4 * algebraMap (NumberField.RingOfIntegers K) L a_v := by
    have h := congr_arg (algebraMap K L) hd_v_rel_K
    simpa only [map_mul, map_sub, map_pow, map_one, map_ofNat, ← hOK_L_eq] using h
  have hη₀_norm : η₀ * σ η₀ = algebraMap (NumberField.RingOfIntegers K) L m_v := by
    rw [hσ_η₀]
    dsimp [η₀, m_v]
    rw [map_mul, map_neg]
    linear_combination
      -(algebraMap (NumberField.RingOfIntegers K) L d_v) * (algebraMap K L c₀) ^ 2 *
        (algebraMap (NumberField.RingOfIntegers K) L d_v) / 4 * hθ -
      (algebraMap (NumberField.RingOfIntegers K) L d_v) / 4 * hd_v_rel_L
  have hη₀_sq : η₀ ^ 2 =
      algebraMap (NumberField.RingOfIntegers K) L d_v * η₀ -
      algebraMap (NumberField.RingOfIntegers K) L m_v := by
    calc η₀ ^ 2
      _ = η₀ * (η₀ + σ η₀) - η₀ * σ η₀ := by ring
      _ = algebraMap (NumberField.RingOfIntegers K) L d_v * η₀ -
          algebraMap (NumberField.RingOfIntegers K) L m_v := by
        rw [hη₀_tr, hη₀_norm, mul_comm]
  have hη₀_val_le_one : ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      (IsDedekindDomain.HeightOneSpectrum.valuation L w) η₀ ≤ 1 := by
    intro w
    have hw_OK : ∀ r : NumberField.RingOfIntegers K,
        (IsDedekindDomain.HeightOneSpectrum.valuation L w)
          (algebraMap (NumberField.RingOfIntegers K) L r) ≤ 1 := by
      intro r
      rw [IsScalarTower.algebraMap_apply
        (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) L r]
      exact w.valuation_le_one _
    by_contra hnot
    have hgt : 1 < (IsDedekindDomain.HeightOneSpectrum.valuation L w) η₀ := not_le.mp hnot
    set γw := (IsDedekindDomain.HeightOneSpectrum.valuation L w) η₀
    have hγw_pos : 0 < γw := lt_trans zero_lt_one hgt
    have hlt_sq : γw < (IsDedekindDomain.HeightOneSpectrum.valuation L w) (η₀ ^ 2) := by
      rw [sq, Valuation.map_mul]
      calc γw = 1 * γw := (one_mul _).symm
        _ < γw * γw := mul_lt_mul_of_pos_right hgt hγw_pos
    have hle_sq : (IsDedekindDomain.HeightOneSpectrum.valuation L w) (η₀ ^ 2) ≤ γw := by
      rw [hη₀_sq]
      calc (IsDedekindDomain.HeightOneSpectrum.valuation L w)
            (algebraMap (NumberField.RingOfIntegers K) L d_v * η₀ -
              algebraMap (NumberField.RingOfIntegers K) L m_v)
        _ ≤ max ((IsDedekindDomain.HeightOneSpectrum.valuation L w)
              (algebraMap (NumberField.RingOfIntegers K) L d_v * η₀))
            ((IsDedekindDomain.HeightOneSpectrum.valuation L w)
              (algebraMap (NumberField.RingOfIntegers K) L m_v)) := Valuation.map_sub _ _ _
        _ ≤ γw := by
          apply max_le
          · rw [Valuation.map_mul]
            calc (IsDedekindDomain.HeightOneSpectrum.valuation L w)
                  (algebraMap (NumberField.RingOfIntegers K) L d_v) * γw
              _ ≤ 1 * γw := mul_le_mul_left (hw_OK d_v) _
              _ = γw := one_mul _
          · exact le_trans (hw_OK m_v) (le_of_lt hgt)
    exact (not_lt_of_ge hle_sq) hlt_sq
  obtain ⟨η, hη⟩ :=
    IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one L η₀ hη₀_val_le_one
  have hσ_η : algebraMap (NumberField.RingOfIntegers L) L
      ((NumberField.RingOfIntegers.mapRingEquiv σ.toRingEquiv) η) = σ η₀ := by
    rw [← NumberField.RingOfIntegers.coe_eq_algebraMap,
        NumberField.RingOfIntegers.mapRingEquiv_apply]
    change σ (η : L) = σ η₀
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, hη]
  refine ⟨d_v, m_v, η, hd_v_not_mem, hm_v_mem, ?_, ?_⟩
  · apply IsFractionRing.injective (NumberField.RingOfIntegers L) L
    rw [map_add, hη, hσ_η,
        ← IsScalarTower.algebraMap_apply
          (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) L d_v]
    exact hη₀_tr
  · apply IsFractionRing.injective (NumberField.RingOfIntegers L) L
    rw [map_mul, hη, hσ_η,
        ← IsScalarTower.algebraMap_apply
          (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) L m_v]
    exact hη₀_norm

theorem split_primes_over_and_valuation_of_integral_splitting {K L : Type u}
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hfinrank : Module.finrank K L = 2)
    (σ : L ≃ₐ[K] L) (hσ_inv : ∀ z : L, σ (σ z) = z)
    (hsplit : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      ∃ (d_v m_v : NumberField.RingOfIntegers K) (η : NumberField.RingOfIntegers L),
        d_v ∉ v.asIdeal ∧
        m_v ∈ v.asIdeal ∧
        η + (NumberField.RingOfIntegers.mapRingEquiv σ.toRingEquiv) η =
          algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) d_v ∧
        η * (NumberField.RingOfIntegers.mapRingEquiv σ.toRingEquiv) η =
          algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) m_v) :
    ∃ w₁ w₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) →
        IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      (∀ v, w₁ v ≠ w₂ v) ∧
      (∀ v (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)),
        Ideal.under (NumberField.RingOfIntegers K) w.asIdeal = v.asIdeal ↔ (w = w₁ v ∨ w = w₂ v)) ∧
      (∀ v (y : Lˣ),
        (w₂ v).valuationOfNeZero y = (w₁ v).valuationOfNeZero (Units.map σ.toMonoidHom y)) ∧
      (∀ v (x : Kˣ),
        (w₁ v).valuationOfNeZero (Units.map (algebraMap K L).toMonoidHom x) = v.valuationOfNeZero x ∧
        (w₂ v).valuationOfNeZero (Units.map (algebraMap K L).toMonoidHom x) = v.valuationOfNeZero x) :=
by
  classical
  have hs1 : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      ∃ w₁ w₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
        w₁ ≠ w₂ ∧
        Ideal.under (NumberField.RingOfIntegers K) w₁.asIdeal = v.asIdeal ∧
        Ideal.under (NumberField.RingOfIntegers K) w₂.asIdeal = v.asIdeal ∧
        (∀ y : Lˣ, w₂.valuationOfNeZero y = w₁.valuationOfNeZero (Units.map σ.toMonoidHom y)) := by
    intro v
    obtain ⟨d_v, m_v, η, hd_v, hm_v, h_tr, h_nm⟩ := hsplit v
    let σ_O : NumberField.RingOfIntegers L ≃+* NumberField.RingOfIntegers L :=
      NumberField.RingOfIntegers.mapRingEquiv σ.toRingEquiv
    have hσ_O_inv : ∀ a : NumberField.RingOfIntegers L, σ_O (σ_O a) = a := by
      intro a
      ext
      exact hσ_inv (a : L)
    have hσ_O_symm : σ_O.symm = σ_O :=
      RingEquiv.ext (fun a => σ_O.symm_apply_eq.mpr (hσ_O_inv a).symm)
    have hσ_O_alg : ∀ r : NumberField.RingOfIntegers K,
        σ_O (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) r) =
          algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) r := by
      intro r
      ext
      change σ (algebraMap (NumberField.RingOfIntegers L) L
        (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) r)) =
        algebraMap (NumberField.RingOfIntegers L) L
          (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) r)
      rw [← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) L,
          IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers K) K L,
          σ.commutes]
    haveI : v.asIdeal.IsPrime := v.isPrime
    obtain ⟨P₁, hP₁_prime, hP₁_over⟩ :=
      Ideal.nonempty_primesOver (P := v.asIdeal) (S := NumberField.RingOfIntegers L)
    have hw₁_under : Ideal.under (NumberField.RingOfIntegers K) P₁ = v.asIdeal :=
      ((Ideal.liesOver_iff P₁ v.asIdeal).mp hP₁_over).symm
    have hP₁_ne_bot : P₁ ≠ ⊥ := by
      intro hbot
      apply v.ne_bot
      rw [← hw₁_under, hbot]
      exact Ideal.comap_bot_of_injective (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L))
        (FaithfulSMul.algebraMap_injective _ _)
    let w₁ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) :=
      ⟨P₁, hP₁_prime, hP₁_ne_bot⟩
    let P₂ : Ideal (NumberField.RingOfIntegers L) :=
      Ideal.comap (σ_O : NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L) w₁.asIdeal
    have hP₂_prime : P₂.IsPrime :=
      Ideal.IsPrime.comap (σ_O : NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L)
    have hP₂_ne_bot : P₂ ≠ ⊥ := by
      rw [Submodule.ne_bot_iff] at hP₁_ne_bot ⊢
      obtain ⟨x, hx_mem, hx_ne⟩ := hP₁_ne_bot
      refine ⟨σ_O x, ?_, σ_O.map_ne_zero_iff.mpr hx_ne⟩
      change σ_O (σ_O x) ∈ w₁.asIdeal
      rwa [hσ_O_inv]
    let w₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) :=
      ⟨P₂, hP₂_prime, hP₂_ne_bot⟩
    have hw₂_under : Ideal.under (NumberField.RingOfIntegers K) w₂.asIdeal = v.asIdeal := by
      rw [← hw₁_under]
      ext r
      change σ_O (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) r) ∈ w₁.asIdeal ↔
        algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) r ∈ w₁.asIdeal
      rw [hσ_O_alg]
    have hw_ne : w₁ ≠ w₂ := by
      intro h_eq
      have h_id : w₁.asIdeal = w₂.asIdeal := congr_arg IsDedekindDomain.HeightOneSpectrum.asIdeal h_eq
      have h_iff : ∀ z : NumberField.RingOfIntegers L, z ∈ w₁.asIdeal ↔ σ_O z ∈ w₁.asIdeal := by
        intro z
        exact ⟨fun hz => by rwa [h_id] at hz, fun hz => by rwa [h_id]⟩
      have hm_L : algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) m_v ∈ w₁.asIdeal := by
        change m_v ∈ Ideal.under (NumberField.RingOfIntegers K) w₁.asIdeal
        rwa [hw₁_under]
      rw [← h_nm] at hm_L
      have hη_both : η ∈ w₁.asIdeal ∧ σ_O η ∈ w₁.asIdeal := by
        rcases w₁.isPrime.mem_or_mem hm_L with h1 | h2
        · exact ⟨h1, (h_iff η).mp h1⟩
        · exact ⟨(h_iff η).mpr h2, h2⟩
      have hd_L : algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) d_v ∈ w₁.asIdeal := by
        rw [← h_tr]
        exact Ideal.add_mem _ hη_both.1 hη_both.2
      have hd_K : d_v ∈ v.asIdeal := by
        rw [← hw₁_under]
        exact hd_L
      exact hd_v hd_K
    have h_map_eq_comap : ∀ I : Ideal (NumberField.RingOfIntegers L),
        Ideal.comap (σ_O : NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L) I =
          Ideal.map (σ_O : NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L) I := by
      intro I
      have h1 := Ideal.comap_symm σ_O (I := I)
      rwa [hσ_O_symm] at h1
    have hP₂_pow : ∀ n : ℕ,
        w₂.asIdeal ^ n = Ideal.comap (σ_O : NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L) (w₁.asIdeal ^ n) := by
      intro n
      change (Ideal.comap (σ_O : NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L) w₁.asIdeal) ^ n = _
      rw [h_map_eq_comap w₁.asIdeal, ← Ideal.map_pow, h_map_eq_comap (w₁.asIdeal ^ n)]
    have h_le_iff : ∀ (a : NumberField.RingOfIntegers L) (n : ℕ),
        w₂.intValuation a ≤ WithZero.exp (-(n : ℤ)) ↔
          w₁.intValuation (σ_O a) ≤ WithZero.exp (-(n : ℤ)) := by
      intro a n
      rw [w₂.intValuation_le_pow_iff_mem, w₁.intValuation_le_pow_iff_mem, hP₂_pow n]
      rfl
    have hint_val : ∀ a : NumberField.RingOfIntegers L,
        w₂.intValuation a = w₁.intValuation (σ_O a) := by
      intro a
      by_cases ha : a = 0
      · subst ha
        simp
      · have hσa : σ_O a ≠ 0 := σ_O.map_ne_zero_iff.mpr ha
        obtain ⟨m₂, hm₂⟩ : ∃ m₂ : ℕ, w₂.intValuation a = WithZero.exp (-(m₂ : ℤ)) :=
          ⟨_, w₂.intValuation_if_neg ha⟩
        obtain ⟨m₁, hm₁⟩ : ∃ m₁ : ℕ, w₁.intValuation (σ_O a) = WithZero.exp (-(m₁ : ℤ)) :=
          ⟨_, w₁.intValuation_if_neg hσa⟩
        apply le_antisymm
        · rw [hm₁]
          exact (h_le_iff a m₁).mpr (le_of_eq hm₁)
        · rw [hm₂]
          exact (h_le_iff a m₂).mp (le_of_eq hm₂)
    refine ⟨w₁, w₂, hw_ne, hw₁_under, hw₂_under, ?_⟩
    intro y
    obtain ⟨a, b, hb_mem, hab⟩ :=
      IsFractionRing.div_surjective (A := NumberField.RingOfIntegers L) (y : L)
    have hσ_div : ((Units.map σ.toMonoidHom y : Lˣ) : L) =
        algebraMap (NumberField.RingOfIntegers L) L (σ_O a) /
        algebraMap (NumberField.RingOfIntegers L) L (σ_O b) := by
      change σ (y : L) = algebraMap (NumberField.RingOfIntegers L) L (σ_O a) /
        algebraMap (NumberField.RingOfIntegers L) L (σ_O b)
      rw [← hab, map_div₀]
      rfl
    apply WithZero.coe_inj.mp
    rw [w₂.valuationOfNeZero_eq, w₁.valuationOfNeZero_eq, ← hab, hσ_div,
        Valuation.map_div, Valuation.map_div,
        w₂.valuation_of_algebraMap, w₂.valuation_of_algebraMap,
        w₁.valuation_of_algebraMap, w₁.valuation_of_algebraMap,
        hint_val a, hint_val b]
  have hs2 : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
      (w₁ w₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)),
      w₁ ≠ w₂ →
      Ideal.under (NumberField.RingOfIntegers K) w₁.asIdeal = v.asIdeal →
      Ideal.under (NumberField.RingOfIntegers K) w₂.asIdeal = v.asIdeal →
      (∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
        Ideal.under (NumberField.RingOfIntegers K) w.asIdeal = v.asIdeal ↔ (w = w₁ ∨ w = w₂)) ∧
      Ideal.map (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)) v.asIdeal =
        w₁.asIdeal * w₂.asIdeal := by
    intro v w₁ w₂ hne hw₁ hw₂
    haveI : v.asIdeal.IsMaximal := v.isMaximal
    let F_v := primesOverFinset v.asIdeal (NumberField.RingOfIntegers L)
    have hmem_Fv : ∀ P : Ideal (NumberField.RingOfIntegers L),
        P ∈ F_v ↔ P.IsPrime ∧ Ideal.under (NumberField.RingOfIntegers K) P = v.asIdeal := by
      intro P
      rw [mem_primesOverFinset_iff v.ne_bot (NumberField.RingOfIntegers L)]
      change P.IsPrime ∧ P.LiesOver v.asIdeal ↔ P.IsPrime ∧ Ideal.under (NumberField.RingOfIntegers K) P = v.asIdeal
      rw [Ideal.liesOver_iff, eq_comm]
    have hP₁_mem : w₁.asIdeal ∈ F_v := (hmem_Fv w₁.asIdeal).mpr ⟨w₁.isPrime, hw₁⟩
    have hP₂_mem : w₂.asIdeal ∈ F_v := (hmem_Fv w₂.asIdeal).mpr ⟨w₂.isPrime, hw₂⟩
    have hP_ne : w₁.asIdeal ≠ w₂.asIdeal := fun h => hne (IsDedekindDomain.HeightOneSpectrum.ext h)
    let e : Ideal (NumberField.RingOfIntegers L) → ℕ :=
      fun P => Ideal.ramificationIdx (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)) v.asIdeal P
    let f : Ideal (NumberField.RingOfIntegers L) → ℕ :=
      fun P => v.asIdeal.inertiaDeg P
    have hef_pos : ∀ P ∈ F_v, 1 ≤ e P * f P := by
      intro P hP
      haveI : P.IsPrime := ((mem_primesOverFinset_iff v.ne_bot _).mp hP).1
      haveI : P.LiesOver v.asIdeal := ((mem_primesOverFinset_iff v.ne_bot _).mp hP).2
      have he : 1 ≤ e P := Nat.one_le_iff_ne_zero.mpr
        (Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P v.ne_bot)
      have hf : 1 ≤ f P := Ideal.inertiaDeg_pos v.asIdeal P
      exact Nat.mul_pos he hf
    have hsum : ∑ P ∈ F_v, e P * f P = 2 := by
      have h := Ideal.sum_ramification_inertia (NumberField.RingOfIntegers L) K L v.ne_bot
      rwa [hfinrank] at h
    have hFv_eq : F_v = {w₁.asIdeal, w₂.asIdeal} := by
      ext P
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hP
        by_contra h_not
        push_neg at h_not
        rcases h_not with ⟨hP1, hP2⟩
        have hsub : ({P, w₁.asIdeal, w₂.asIdeal} : Finset _) ⊆ F_v := by
          intro Q hQ
          simp only [Finset.mem_insert, Finset.mem_singleton] at hQ
          rcases hQ with rfl | rfl | rfl
          · exact hP
          · exact hP₁_mem
          · exact hP₂_mem
        have hle : ∑ Q ∈ ({P, w₁.asIdeal, w₂.asIdeal} : Finset _), e Q * f Q ≤ ∑ Q ∈ F_v, e Q * f Q :=
          Finset.sum_le_sum_of_subset hsub
        have h1 : P ∉ ({w₁.asIdeal, w₂.asIdeal} : Finset _) := by simp [hP1, hP2]
        have h2 : w₁.asIdeal ∉ ({w₂.asIdeal} : Finset _) := by simp [hP_ne]
        rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton, hsum] at hle
        have := hef_pos P hP
        have := hef_pos w₁.asIdeal hP₁_mem
        have := hef_pos w₂.asIdeal hP₂_mem
        omega
      · rintro (rfl | rfl)
        · exact hP₁_mem
        · exact hP₂_mem
    have hsum_pair : e w₁.asIdeal * f w₁.asIdeal + e w₂.asIdeal * f w₂.asIdeal = 2 := by
      rw [← hsum, hFv_eq, Finset.sum_pair hP_ne]
    have he1 : e w₁.asIdeal = 1 := by
      have h1 := hef_pos w₁.asIdeal hP₁_mem
      have h2 := hef_pos w₂.asIdeal hP₂_mem
      have hprod : e w₁.asIdeal * f w₁.asIdeal = 1 := by omega
      exact Nat.eq_one_of_mul_eq_one_right hprod
    have he2 : e w₂.asIdeal = 1 := by
      have h1 := hef_pos w₁.asIdeal hP₁_mem
      have h2 := hef_pos w₂.asIdeal hP₂_mem
      have hprod : e w₂.asIdeal * f w₂.asIdeal = 1 := by omega
      exact Nat.eq_one_of_mul_eq_one_right hprod
    refine ⟨?_, ?_⟩
    · intro w
      have hw_iff : Ideal.under (NumberField.RingOfIntegers K) w.asIdeal = v.asIdeal ↔ w.asIdeal ∈ F_v := by
        rw [hmem_Fv]
        exact ⟨fun h => ⟨w.isPrime, h⟩, fun h => h.2⟩
      rw [hw_iff, hFv_eq, Finset.mem_insert, Finset.mem_singleton,
          IsDedekindDomain.HeightOneSpectrum.ext_iff, IsDedekindDomain.HeightOneSpectrum.ext_iff]
    · have htoFinset : (v.asIdeal.primesOver (NumberField.RingOfIntegers L)).toFinset = {w₁.asIdeal, w₂.asIdeal} := by
        ext P
        rw [Set.mem_toFinset, ← mem_primesOverFinset_iff v.ne_bot]
        change P ∈ F_v ↔ P ∈ {w₁.asIdeal, w₂.asIdeal}
        rw [hFv_eq]
      rw [Ideal.map_algebraMap_eq_finset_prod_pow v.ne_bot, htoFinset, Finset.prod_pair hP_ne]
      change w₁.asIdeal ^ e w₁.asIdeal * w₂.asIdeal ^ e w₂.asIdeal = w₁.asIdeal * w₂.asIdeal
      rw [he1, he2, pow_one, pow_one]
  have hs3 : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
      (w₁ w₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)),
      w₁ ≠ w₂ →
      Ideal.under (NumberField.RingOfIntegers K) w₁.asIdeal = v.asIdeal →
      Ideal.map (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)) v.asIdeal =
        w₁.asIdeal * w₂.asIdeal →
      ∀ x : Kˣ,
        w₁.valuationOfNeZero (Units.map (algebraMap K L).toMonoidHom x) = v.valuationOfNeZero x := by
    intro v w₁ w₂ hne hw₁ hmap x
    let f := algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)
    have hint_val : ∀ a : NumberField.RingOfIntegers K, w₁.intValuation (f a) = v.intValuation a := by
      intro a
      by_cases ha : a = 0
      · subst ha
        simp
      · obtain ⟨n, hn⟩ : ∃ n : ℕ, v.intValuation a = WithZero.exp (-(n : ℤ)) :=
          ⟨_, v.intValuation_if_neg ha⟩
        have hdvd_n : v.asIdeal ^ n ∣ Ideal.span {a} :=
          (v.intValuation_le_pow_iff_dvd a n).mp (le_of_eq hn)
        obtain ⟨I₀, hI₀⟩ := hdvd_n
        have hnot_dvd_succ : ¬ (v.asIdeal ^ (n + 1) ∣ Ideal.span {a}) := by
          rw [← v.intValuation_le_pow_iff_dvd a (n + 1), hn, WithZero.exp_le_exp]
          omega
        have hnot_dvd_I₀ : ¬ (v.asIdeal ∣ I₀) := by
          rintro ⟨J, rfl⟩
          apply hnot_dvd_succ
          refine ⟨J, ?_⟩
          rw [hI₀, pow_succ, mul_assoc]
        have hnot_le_I₀ : ¬ (I₀ ≤ v.asIdeal) := by
          rwa [← Ideal.dvd_iff_le]
        obtain ⟨c, hc_mem, hc_not_mem⟩ := SetLike.not_le_iff_exists.mp hnot_le_I₀
        have hspan_f : Ideal.span {f a} = (w₁.asIdeal ^ n * w₂.asIdeal ^ n) * Ideal.map f I₀ := by
          calc Ideal.span {f a}
            _ = Ideal.map f (Ideal.span {a}) := by
              rw [Ideal.map_span, Set.image_singleton]
            _ = Ideal.map f (v.asIdeal ^ n * I₀) := by rw [hI₀]
            _ = (Ideal.map f v.asIdeal) ^ n * Ideal.map f I₀ := by
              rw [Ideal.map_mul, Ideal.map_pow]
            _ = (w₁.asIdeal * w₂.asIdeal) ^ n * Ideal.map f I₀ := by rw [hmap]
            _ = (w₁.asIdeal ^ n * w₂.asIdeal ^ n) * Ideal.map f I₀ := by rw [mul_pow]
        have h_le : w₁.intValuation (f a) ≤ WithZero.exp (-(n : ℤ)) := by
          rw [w₁.intValuation_le_pow_iff_dvd]
          refine ⟨w₂.asIdeal ^ n * Ideal.map f I₀, ?_⟩
          rw [hspan_f, mul_assoc]
        have h_ge : WithZero.exp (-(n : ℤ)) ≤ w₁.intValuation (f a) := by
          obtain ⟨π₁, hπ₁_val⟩ := w₁.intValuation_exists_uniformizer
          have hπ₁_mem : π₁ ∈ w₁.asIdeal := by
            simpa using (w₁.intValuation_le_pow_iff_mem π₁ 1).mp (le_of_eq hπ₁_val)
          have hnot_w₂_le_w₁ : ¬ (w₂.asIdeal ≤ w₁.asIdeal) := by
            intro hle
            have heq := (w₂.isMaximal.eq_of_le w₁.isPrime.ne_top hle).symm
            exact hne (IsDedekindDomain.HeightOneSpectrum.ext heq)
          obtain ⟨s, hs_w₂, hs_not_w₁⟩ := SetLike.not_le_iff_exists.mp hnot_w₂_le_w₁
          have hs_val : w₁.intValuation s = 1 := w₁.intValuation_eq_one_iff.mpr hs_not_w₁
          have hfc_not_w₁ : f c ∉ w₁.asIdeal := by
            change c ∉ Ideal.under (NumberField.RingOfIntegers K) w₁.asIdeal
            rwa [hw₁]
          have hfc_val : w₁.intValuation (f c) = 1 := w₁.intValuation_eq_one_iff.mpr hfc_not_w₁
          have hz_mem : (π₁ ^ n * s ^ n) * f c ∈ Ideal.span {f a} := by
            rw [hspan_f]
            exact Ideal.mul_mem_mul
              (Ideal.mul_mem_mul (Ideal.pow_mem_pow hπ₁_mem n) (Ideal.pow_mem_pow hs_w₂ n))
              (Ideal.mem_map_of_mem f hc_mem)
          obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hz_mem
          have hz_val : w₁.intValuation ((π₁ ^ n * s ^ n) * f c) = WithZero.exp (-(n : ℤ)) := by
            rw [map_mul, map_mul, map_pow, map_pow, hπ₁_val, hs_val, hfc_val, one_pow, mul_one, mul_one,
                ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg_one]
          calc WithZero.exp (-(n : ℤ))
            _ = w₁.intValuation ((π₁ ^ n * s ^ n) * f c) := hz_val.symm
            _ = w₁.intValuation (f a) * w₁.intValuation q := by rw [hq, map_mul]
            _ ≤ w₁.intValuation (f a) * 1 := by gcongr; exact w₁.intValuation_le_one q
            _ = w₁.intValuation (f a) := mul_one _
        rw [hn]
        exact le_antisymm h_le h_ge
    obtain ⟨a, b, hb_mem, hab⟩ :=
      IsFractionRing.div_surjective (A := NumberField.RingOfIntegers K) (x : K)
    have hmap_div : ((Units.map (algebraMap K L).toMonoidHom x : Lˣ) : L) =
        algebraMap (NumberField.RingOfIntegers L) L (f a) /
        algebraMap (NumberField.RingOfIntegers L) L (f b) := by
      change algebraMap K L (x : K) = _
      rw [← hab, map_div₀, ← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers K) K L,
          ← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers K) K L,
          IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) L,
          IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) L]
    apply WithZero.coe_inj.mp
    rw [w₁.valuationOfNeZero_eq, v.valuationOfNeZero_eq, ← hab, hmap_div,
        Valuation.map_div, Valuation.map_div,
        w₁.valuation_of_algebraMap, w₁.valuation_of_algebraMap,
        v.valuation_of_algebraMap, v.valuation_of_algebraMap,
        hint_val a, hint_val b]
  choose w₁ w₂ hw_ne hw₁_under hw₂_under hw₂_val using hs1
  refine ⟨w₁, w₂, hw_ne, ?_, hw₂_val, ?_⟩
  · intro v w
    exact (hs2 v (w₁ v) (w₂ v) (hw_ne v) (hw₁_under v) (hw₂_under v)).1 w
  · intro v x
    have hmap := (hs2 v (w₁ v) (w₂ v) (hw_ne v) (hw₁_under v) (hw₂_under v)).2
    refine ⟨hs3 v (w₁ v) (w₂ v) (hw_ne v) (hw₁_under v) hmap x,
            hs3 v (w₂ v) (w₁ v) (hw_ne v).symm (hw₂_under v) (hmap.trans (mul_comm _ _)) x⟩

theorem exists_quadratic_split_extension_of_isSquare_everywhere {K : Type u} [Field K] [NumberField K]
    (u : Kˣ) (hu_not_sq : ¬ IsSquare (u : K))
    (hu_fin : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      IsSquare (algebraMap K (v.adicCompletion K) (u : K)))
    (hu_inf : ∀ w : NumberField.InfinitePlace K, IsSquare (algebraMap K w.Completion (u : K)))
    (S_fin₀ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hS_fin₀ : ∀ c : ClassGroup (NumberField.RingOfIntegers K),
      ∃ I : nonZeroDivisors (Ideal (NumberField.RingOfIntegers K)),
        ClassGroup.mk0 I = c ∧
        ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          v ∉ S_fin₀ → ¬ (v.asIdeal ∣ (I : Ideal (NumberField.RingOfIntegers K)))) :
    ∃ (L : Type u) (instF : Field L) (instNF : NumberField L) (instAlg : Algebra K L),
      letI := instF; letI := instNF; letI := instAlg;
      ∃ (N : Lˣ →* Kˣ)
        (S_fin : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
        (S_fin_L : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))),
        S_fin₀ ⊆ S_fin ∧
        (∀ c : ClassGroup (NumberField.RingOfIntegers L),
          ∃ I : nonZeroDivisors (Ideal (NumberField.RingOfIntegers L)),
            ClassGroup.mk0 I = c ∧
            ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
              w ∉ S_fin_L → ¬ (w.asIdeal ∣ (I : Ideal (NumberField.RingOfIntegers L)))) ∧
        NumberField.InfinitePlace.nrRealPlaces L + NumberField.InfinitePlace.nrComplexPlaces L +
          S_fin_L.card =
          2 * (NumberField.InfinitePlace.nrRealPlaces K +
            NumberField.InfinitePlace.nrComplexPlaces K + S_fin.card) ∧
        IsSquare (algebraMap K L (u : K)) ∧
        (∀ y : Lˣ,
          (∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
            w ∉ S_fin_L → w.valuationOfNeZero y = 1) →
          (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
            v ∉ S_fin → EvenVal v (N y)) ∧
          (IsSquare ((N y : Kˣ) : K) →
            ∃ x : Kˣ,
              (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
                v ∉ S_fin → EvenVal v x) ∧
              IsSquare ((y : L) * algebraMap K L (x : K)))) ∧
        (∀ x : Kˣ,
          (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
            v ∉ S_fin → v.valuationOfNeZero x = 1) →
          ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
            w ∉ S_fin_L → EvenVal w (Units.map (algebraMap K L).toMonoidHom x)) :=
by
  classical
  obtain ⟨L, instF, instNF, instAlg, θ, σ, N, hfinrank, hθ, hσθ, hσ_inv, hspan, hlift, hN⟩ :=
    exists_quadratic_extension_and_involution u hu_not_sq
  letI := instF
  letI := instNF
  letI := instAlg
  have h_arch : NumberField.InfinitePlace.nrRealPlaces L +
      NumberField.InfinitePlace.nrComplexPlaces L =
      2 * (NumberField.InfinitePlace.nrRealPlaces K +
        NumberField.InfinitePlace.nrComplexPlaces K) :=
    quadratic_extension_nrRealPlaces_add_nrComplexPlaces hfinrank u hu_inf θ hθ hspan hlift
  have hsplit_all : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      ∃ (d_v m_v : NumberField.RingOfIntegers K) (η : NumberField.RingOfIntegers L),
        d_v ∉ v.asIdeal ∧
        m_v ∈ v.asIdeal ∧
        η + (NumberField.RingOfIntegers.mapRingEquiv σ.toRingEquiv) η =
          algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) d_v ∧
        η * (NumberField.RingOfIntegers.mapRingEquiv σ.toRingEquiv) η =
          algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) m_v :=
    fun v => exists_integral_splitting_elem_of_local_square u v (hu_fin v) θ hθ σ hσθ
  obtain ⟨w₁, w₂, hw_ne, hw_under, hw₂_val, hw_ext⟩ :=
    split_primes_over_and_valuation_of_integral_splitting hfinrank σ hσ_inv hsplit_all
  let π : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) →
      IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) :=
    fun w => ⟨Ideal.under (NumberField.RingOfIntegers K) w.asIdeal,
      Ideal.IsPrime.under (NumberField.RingOfIntegers K) w.asIdeal,
      Ideal.under_ne_bot (NumberField.RingOfIntegers K) w.ne_bot⟩
  have hπ_w₁ : ∀ v, π (w₁ v) = v := by
    intro v
    apply IsDedekindDomain.HeightOneSpectrum.ext
    exact (hw_under v (w₁ v)).mpr (Or.inl rfl)
  have hπ_w₂ : ∀ v, π (w₂ v) = v := by
    intro v
    apply IsDedekindDomain.HeightOneSpectrum.ext
    exact (hw_under v (w₂ v)).mpr (Or.inr rfl)
  have hw_or : ∀ w, w = w₁ (π w) ∨ w = w₂ (π w) :=
    fun w => (hw_under (π w) w).mp rfl
  have hw₁_inj : Function.Injective w₁ := Function.LeftInverse.injective hπ_w₁
  have hw₂_inj : Function.Injective w₂ := Function.LeftInverse.injective hπ_w₂
  have hw₁_ne_w₂ : ∀ v₁ v₂, w₁ v₁ ≠ w₂ v₂ := by
    intro v₁ v₂ h
    have hv : v₁ = v₂ := by rw [← hπ_w₁ v₁, h, hπ_w₂ v₂]
    subst hv
    exact hw_ne v₁ h
  obtain ⟨S_L₀, _, _, hS_L₀_gen⟩ :=
    exists_finset_classGroup_gen_disjoint (F := L) ∅ ∅ (Finset.disjoint_empty_right ∅)
  let S_fin : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
    S_fin₀ ∪ S_L₀.image π
  let S_fin_L : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :=
    S_fin.image w₁ ∪ S_fin.image w₂
  have hmem_S_fin_L : ∀ w, w ∈ S_fin_L ↔ π w ∈ S_fin := by
    intro w
    simp only [S_fin_L, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
      · rwa [hπ_w₁]
      · rwa [hπ_w₂]
    · intro hπw
      rcases hw_or w with hw1 | hw2
      · exact Or.inl ⟨π w, hπw, hw1.symm⟩
      · exact Or.inr ⟨π w, hπw, hw2.symm⟩
  have hS_fin_L_card : S_fin_L.card = 2 * S_fin.card := by
    have hdisj : Disjoint (S_fin.image w₁) (S_fin.image w₂) := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      rw [Finset.mem_image] at hw1 hw2
      rcases hw1 with ⟨v₁, _, rfl⟩
      rcases hw2 with ⟨v₂, _, h_eq⟩
      exact hw₁_ne_w₂ v₁ v₂ h_eq.symm
    rw [Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective S_fin hw₁_inj,
        Finset.card_image_of_injective S_fin hw₂_inj,
        Nat.two_mul]
  let ι_K : Kˣ →* Lˣ := Units.map (algebraMap K L).toMonoidHom
  let σ_u : Lˣ →* Lˣ := Units.map σ.toMonoidHom
  have hN_units : ∀ y₀ : Lˣ, ι_K (N y₀) = y₀ * σ_u y₀ := by
    intro y₀
    ext
    exact hN y₀
  have hN_val : ∀ v (y₀ : Lˣ),
      v.valuationOfNeZero (N y₀) = (w₁ v).valuationOfNeZero y₀ * (w₂ v).valuationOfNeZero y₀ := by
    intro v y₀
    rw [← (hw_ext v (N y₀)).1, hN_units y₀, map_mul, hw₂_val v y₀]
  have evenVal_of_val_eq_one : ∀ {F : Type u} [Field F] [NumberField F]
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (x : Fˣ),
      v.valuationOfNeZero x = 1 → EvenVal v x := by
    intro F _ _ v x hx
    unfold EvenVal
    rw [hx, toAdd_one]
    exact Even.zero
  refine ⟨L, instF, instNF, instAlg, N, S_fin, S_fin_L, Finset.subset_union_left, ?_, ?_, ?_, ?_, ?_⟩
  · intro c
    obtain ⟨I, hIc, hIdiv⟩ := hS_L₀_gen c
    refine ⟨I, hIc, fun w hw => hIdiv w (Finset.notMem_empty w) (fun hw₀ => hw ?_)⟩
    rw [hmem_S_fin_L]
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem π hw₀)
  · rw [h_arch, hS_fin_L_card, ← Nat.mul_add]
  · refine ⟨θ, ?_⟩
    rw [← sq, hθ]
  · intro y hy_val
    have hNy_val_one : ∀ v ∉ S_fin, v.valuationOfNeZero (N y) = 1 := by
      intro v hv
      have hw1 : w₁ v ∉ S_fin_L := by rwa [hmem_S_fin_L, hπ_w₁]
      have hw2 : w₂ v ∉ S_fin_L := by rwa [hmem_S_fin_L, hπ_w₂]
      rw [hN_val v y, hy_val (w₁ v) hw1, hy_val (w₂ v) hw2, mul_one]
    refine ⟨fun v hv => evenVal_of_val_eq_one v (N y) (hNy_val_one v hv), ?_⟩
    rintro ⟨x₀_K, hx₀_K⟩
    have hx₀_ne : x₀_K ≠ 0 := by
      intro h0
      have hNy0 : ((N y : Kˣ) : K) = 0 := by rw [hx₀_K, h0, mul_zero]
      exact (N y).ne_zero hNy0
    let x₀ : Kˣ := Units.mk0 x₀_K hx₀_ne
    have hx₀_eq : N y = x₀ * x₀ := by
      ext
      exact hx₀_K
    have hx₀_val : ∀ v ∉ S_fin, v.valuationOfNeZero x₀ = 1 := by
      intro v hv
      have hsq1 : v.valuationOfNeZero x₀ * v.valuationOfNeZero x₀ = 1 := by
        rw [← map_mul, ← hx₀_eq]
        exact hNy_val_one v hv
      have h_add : Multiplicative.toAdd (v.valuationOfNeZero x₀) = 0 := by
        have h2 : Multiplicative.toAdd (v.valuationOfNeZero x₀ * v.valuationOfNeZero x₀) = 0 := by
          rw [hsq1, toAdd_one]
        rw [toAdd_mul] at h2
        omega
      exact Multiplicative.toAdd.injective (h_add.trans toAdd_one.symm)
    let z : Lˣ := y * (ι_K x₀)⁻¹
    have hσ_ι : ∀ a : Kˣ, σ_u (ι_K a) = ι_K a := by
      intro a
      ext
      exact σ.commutes (a : K)
    have hz_norm : z * σ_u z = 1 := by
      dsimp [z]
      rw [map_mul, map_inv, hσ_ι x₀]
      calc y * (ι_K x₀)⁻¹ * (σ_u y * (ι_K x₀)⁻¹)
        _ = (y * σ_u y) * ((ι_K x₀)⁻¹ * (ι_K x₀)⁻¹) := mul_mul_mul_comm _ _ _ _
        _ = ι_K (x₀ * x₀) * (ι_K x₀ * ι_K x₀)⁻¹ := by rw [← hN_units y, hx₀_eq, mul_inv_rev]
        _ = 1 := by rw [map_mul, mul_inv_cancel]
    have hw₀_ex : ∃ w₀ : Lˣ, w₀ = z * σ_u w₀ := by
      by_cases hz : (z : L) = -1
      · have hθ_ne : θ ≠ 0 := by
          intro h0
          have hu0 : algebraMap K L (u : K) = 0 := by
            rw [← hθ, h0, sq, mul_zero]
          exact (map_ne_zero (algebraMap K L)).mpr u.ne_zero hu0
        let w₀ : Lˣ := Units.mk0 θ hθ_ne
        refine ⟨w₀, ?_⟩
        ext
        change θ = (z : L) * σ θ
        rw [hz, hσθ, neg_one_mul, neg_neg]
      · have hz1_ne : (z : L) + 1 ≠ 0 := by
          intro h0
          apply hz
          linear_combination h0
        let w₀ : Lˣ := Units.mk0 ((z : L) + 1) hz1_ne
        refine ⟨w₀, ?_⟩
        ext
        change (z : L) + 1 = (z : L) * σ ((z : L) + 1)
        have hzz : (z : L) * σ (z : L) = 1 := congr_arg Units.val hz_norm
        rw [map_add, map_one, mul_add, mul_one, hzz, add_comm]
    obtain ⟨w₀, hw₀⟩ := hw₀_ex
    let x : Kˣ := x₀⁻¹ * N w₀
    refine ⟨x, ?_, ?_⟩
    · intro v hv
      have hw1_not : w₁ v ∉ S_fin_L := by rwa [hmem_S_fin_L, hπ_w₁]
      have hz_val : (w₁ v).valuationOfNeZero z = 1 := by
        dsimp [z]
        rw [map_mul, map_inv, hy_val (w₁ v) hw1_not, (hw_ext v x₀).1, hx₀_val v hv, inv_one, mul_one]
      have hw₀_val_eq : (w₁ v).valuationOfNeZero w₀ = (w₂ v).valuationOfNeZero w₀ := by
        calc (w₁ v).valuationOfNeZero w₀
          _ = (w₁ v).valuationOfNeZero (z * σ_u w₀) := by rw [← hw₀]
          _ = (w₁ v).valuationOfNeZero z * (w₁ v).valuationOfNeZero (σ_u w₀) := map_mul _ _ _
          _ = 1 * (w₂ v).valuationOfNeZero w₀ := by rw [hz_val, ← hw₂_val v w₀]
          _ = (w₂ v).valuationOfNeZero w₀ := one_mul _
      have hx_val_sq : v.valuationOfNeZero x =
          (w₁ v).valuationOfNeZero w₀ * (w₁ v).valuationOfNeZero w₀ := by
        dsimp [x]
        rw [map_mul, map_inv, hx₀_val v hv, inv_one, one_mul, hN_val v w₀, ← hw₀_val_eq]
      unfold EvenVal
      rw [hx_val_sq, toAdd_mul]
      exact ⟨Multiplicative.toAdd ((w₁ v).valuationOfNeZero w₀), rfl⟩
    · have hyx_eq : y * ι_K x = w₀ * w₀ := by
        dsimp [x, z] at hw₀ ⊢
        rw [map_mul, map_inv, hN_units w₀]
        calc y * ((ι_K x₀)⁻¹ * (w₀ * σ_u w₀))
          _ = (y * (ι_K x₀)⁻¹ * σ_u w₀) * w₀ := by ac_rfl
          _ = w₀ * w₀ := by rw [← hw₀]
      refine ⟨(w₀ : L), ?_⟩
      exact congr_arg Units.val hyx_eq
  · intro x hx_val w hw
    have hv : π w ∉ S_fin := by rwa [← hmem_S_fin_L]
    rcases hw_or w with hw1 | hw2
    · rw [hw1]
      apply evenVal_of_val_eq_one
      rw [(hw_ext (π w) x).1]
      exact hx_val (π w) hv
    · rw [hw2]
      apply evenVal_of_val_eq_one
      rw [(hw_ext (π w) x).2]
      exact hx_val (π w) hv

theorem exists_sUnit_basis_and_loc_inj {K : Type u} [Field K] [NumberField K]
    (a₁ a₂ a₃ : K) (h₁₂ : a₁ ≠ a₂) (h₁₃ : a₁ ≠ a₃) (h₂₃ : a₂ ≠ a₃)
    (hint₁ : IsIntegral ℤ a₁) (hint₂ : IsIntegral ℤ a₂) (hint₃ : IsIntegral ℤ a₃)
    (T S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hT : IsGoodT a₁ a₂ a₃ T) (hSdisj : Disjoint S T)
    (v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hv₀T : v₀ ∉ T) (hv₀S : v₀ ∉ S) :
    ∃ (S_out : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
      (P : (Fin (2 * (NumberField.InfinitePlace.nrRealPlaces K +
        NumberField.InfinitePlace.nrComplexPlaces K + T.card + S_out.card + 1)) → ZMod 2) → Kˣ × Kˣ),
      S ⊆ S_out ∧ Disjoint S_out T ∧ v₀ ∉ S_out ∧
      P 0 = (1, 1) ∧
      (∀ α β, IsSquare (((P (α + β)).1 : K) * (((P α).1 * (P β).1 : Kˣ) : K)) ∧
              IsSquare (((P (α + β)).2 : K) * (((P α).2 * (P β).2 : Kˣ) : K))) ∧
      (∀ α v, v ∉ T → v ∉ S_out → v ≠ v₀ → EvenVal v (P α).1 ∧ EvenVal v (P α).2) ∧
      (∀ α β,
        (∀ v, (v ∈ T ∨ v ∈ S_out ∨ v = v₀) →
          IsSquare (algebraMap K (v.adicCompletion K) (((P α).1 * (P β).1 : Kˣ) : K)) ∧
          IsSquare (algebraMap K (v.adicCompletion K) (((P α).2 * (P β).2 : Kˣ) : K))) →
        (∀ w : NumberField.InfinitePlace K,
          IsSquare (algebraMap K w.Completion (((P α).1 * (P β).1 : Kˣ) : K)) ∧
          IsSquare (algebraMap K w.Completion (((P α).2 * (P β).2 : Kˣ) : K))) →
        α = β) :=
by
  have zmod2_val_add_even : ∀ a b : ZMod 2, ∃ k : ℕ, (a + b).val + (a.val + b.val) = 2 * k := by
    intro a b
    fin_cases a <;> fin_cases b
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨1, rfl⟩
  have zmod2_fun_add_cancel_left : ∀ {n : ℕ} (a b : Fin n → ZMod 2),
      a + (b + a) = b := by
    intro n a b
    funext i
    change a i + (b i + a i) = b i
    generalize a i = x
    generalize b i = y
    fin_cases x <;> fin_cases y <;> decide
  have zmod2_fun_eq_of_add_eq_zero : ∀ {n : ℕ} (δ₁ δ₂ : Fin n → ZMod 2),
      δ₁ + δ₂ = 0 → δ₁ = δ₂ := by
    intro n δ₁ δ₂ h
    calc δ₁ = δ₂ + (δ₁ + δ₂) := (zmod2_fun_add_cancel_left δ₂ δ₁).symm
      _ = δ₂ + 0 := by rw [h]
      _ = δ₂ := add_zero δ₂
  classical
  have isSquare_unit_trans : ∀ {F : Type u} [Field F] (a b c : Fˣ),
      IsSquare ((a : F) * (b : F)) → IsSquare ((b : F) * (c : F)) → IsSquare ((a : F) * (c : F)) := by
    intro F _ a b c ⟨x, hx⟩ ⟨y, hy⟩
    have hb : (b : F) ≠ 0 := b.ne_zero
    refine ⟨x * y / (b : F), ?_⟩
    calc (a : F) * (c : F)
      _ = ((a : F) * (b : F)) * ((b : F) * (c : F)) / ((b : F) * (b : F)) := by field_simp [hb]
      _ = (x * x) * (y * y) / ((b : F) * (b : F)) := by rw [hx, hy]
      _ = (x * y / (b : F)) * (x * y / (b : F)) := by ring
  have isSquare_unit_left_of_mul_of_right : ∀ {F : Type u} [Field F] (a b : Fˣ),
      IsSquare ((a : F) * (b : F)) → IsSquare (b : F) → IsSquare (a : F) := by
    intro F _ a b hab hb
    have h1 : IsSquare ((b : F) * ((1 : Fˣ) : F)) := by simpa using hb
    simpa using isSquare_unit_trans a b 1 hab h1
  have isSquare_unit_right_of_mul_of_left : ∀ {F : Type u} [Field F] (a b : Fˣ),
      IsSquare ((a : F) * (b : F)) → IsSquare (a : F) → IsSquare (b : F) := by
    intro F _ a b hab ha
    rw [mul_comm] at hab
    exact isSquare_unit_left_of_mul_of_right b a hab ha
  have prodBasis_add_isSquare : ∀ {F : Type u} [Field F] {n : ℕ} (g : Fin n → Fˣ)
      (δ₁ δ₂ : Fin n → ZMod 2),
      IsSquare (((∏ i, g i ^ ((δ₁ + δ₂) i).val : Fˣ) : F) *
        (((∏ i, g i ^ (δ₁ i).val : Fˣ) * (∏ i, g i ^ (δ₂ i).val : Fˣ) : Fˣ) : F)) := by
    intro F _ n g δ₁ δ₂
    have hk : ∀ i : Fin n, ∃ k : ℕ, ((δ₁ + δ₂) i).val + ((δ₁ i).val + (δ₂ i).val) = 2 * k :=
      fun i => zmod2_val_add_even (δ₁ i) (δ₂ i)
    choose k hk using hk
    refine ⟨((∏ i : Fin n, g i ^ k i : Fˣ) : F), ?_⟩
    norm_cast
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [← pow_add, ← pow_add, hk i, two_mul, pow_add]
  have prodBasis_unique : ∀ {F : Type u} [Field F] {n : ℕ} (g : Fin n → Fˣ)
      (hg_indep : ∀ c : Fin n → ZMod 2, IsSquare ((∏ i, g i ^ (c i).val : Fˣ) : F) → c = 0)
      (δ₁ δ₂ : Fin n → ZMod 2),
      IsSquare (((∏ i, g i ^ (δ₁ i).val : Fˣ) : F) * ((∏ i, g i ^ (δ₂ i).val : Fˣ) : F)) →
      δ₁ = δ₂ := by
    intro F _ n g hg_indep δ₁ δ₂ hsq
    have hadd := prodBasis_add_isSquare g δ₁ δ₂
    have hsq' : IsSquare ((((∏ i, g i ^ (δ₁ i).val : Fˣ) * (∏ i, g i ^ (δ₂ i).val : Fˣ) : Fˣ) : F)) := by
      simpa only [Units.val_mul] using hsq
    have hsum_sq := isSquare_unit_left_of_mul_of_right _ _ hadd hsq'
    exact zmod2_fun_eq_of_add_eq_zero δ₁ δ₂ (hg_indep (δ₁ + δ₂) hsum_sq)
  have prodBasis_val_eq_one : ∀ {F : Type u} [Field F] [NumberField F] {n : ℕ}
      (g : Fin n → Fˣ)
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
      (∀ i, v.valuationOfNeZero (g i) = 1) →
      ∀ δ : Fin n → ZMod 2, v.valuationOfNeZero (∏ i, g i ^ (δ i).val) = 1 := by
    intro F _ _ n g v hg δ
    rw [map_prod]
    refine Finset.prod_eq_one (fun i _ => ?_)
    rw [map_pow, hg i, one_pow]
  have evenVal_of_val_eq_one : ∀ {F : Type u} [Field F] [NumberField F]
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (x : Fˣ),
      v.valuationOfNeZero x = 1 → EvenVal v x := by
    intro F _ _ v x hx
    unfold EvenVal
    rw [hx, toAdd_one]
    exact Even.zero
  have hS_disj_insert : Disjoint S (insert v₀ T) :=
    Finset.disjoint_insert_right.mpr ⟨hv₀S, hSdisj⟩
  obtain ⟨S_out, hS_sub, hS_out_disj_insert, hS_out_gen⟩ :=
    exists_finset_classGroup_gen_disjoint (insert v₀ T) S hS_disj_insert
  have hv₀S_out : v₀ ∉ S_out := (Finset.disjoint_insert_right.mp hS_out_disj_insert).1
  have hS_out_disj : Disjoint S_out T := (Finset.disjoint_insert_right.mp hS_out_disj_insert).2
  let S_fin₀ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
    insert v₀ (T ∪ S_out)
  have hmem_S_fin₀ : ∀ v, v ∈ S_fin₀ ↔ (v ∈ T ∨ v ∈ S_out ∨ v = v₀) := by
    intro v
    simp only [S_fin₀, Finset.mem_insert, Finset.mem_union]
    tauto
  have hS_fin₀_gen : ∀ c : ClassGroup (NumberField.RingOfIntegers K),
      ∃ I : nonZeroDivisors (Ideal (NumberField.RingOfIntegers K)),
        ClassGroup.mk0 I = c ∧
        ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          v ∉ S_fin₀ → ¬ (v.asIdeal ∣ (I : Ideal (NumberField.RingOfIntegers K))) := by
    intro c
    obtain ⟨I, hI_c, hI_div⟩ := hS_out_gen c
    refine ⟨I, hI_c, fun v hv => hI_div v ?_ ?_⟩
    · intro hv_ins
      apply hv
      rw [hmem_S_fin₀]
      rcases Finset.mem_insert.mp hv_ins with rfl | hvT
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl hvT
    · intro hvS_out
      apply hv
      rw [hmem_S_fin₀]
      exact Or.inr (Or.inl hvS_out)
  have hS_fin₀_card : S_fin₀.card = T.card + S_out.card + 1 := by
    have hv₀_not_union : v₀ ∉ T ∪ S_out := by
      rw [Finset.mem_union, not_or]
      exact ⟨hv₀T, hv₀S_out⟩
    rw [Finset.card_insert_of_notMem hv₀_not_union,
        Finset.card_union_of_disjoint hS_out_disj.symm]
  obtain ⟨u_unit_K, hu_K_val, hu_K_indep, hu_K_span⟩ := unit_sqCl_basis (F := K)
  obtain ⟨g₀, hg₀_val, hg₀_indep, hg₀_span⟩ :=
    sUnit_sqCl_basis_of_classGroup_gen u_unit_K hu_K_val hu_K_indep hu_K_span S_fin₀ hS_fin₀_gen
  let R := NumberField.InfinitePlace.nrRealPlaces K +
    NumberField.InfinitePlace.nrComplexPlaces K + T.card + S_out.card + 1
  have hR_eq : NumberField.InfinitePlace.nrRealPlaces K +
      NumberField.InfinitePlace.nrComplexPlaces K + S_fin₀.card = R := by
    dsimp [R]
    rw [hS_fin₀_card]
    ac_rfl
  let eR : Fin R ≃ Fin (NumberField.InfinitePlace.nrRealPlaces K +
      NumberField.InfinitePlace.nrComplexPlaces K + S_fin₀.card) :=
    finCongr hR_eq.symm
  let g : Fin R → Kˣ := fun i => g₀ (eR i)
  have hg_val : ∀ i, ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      v ∉ S_fin₀ → v.valuationOfNeZero (g i) = 1 :=
    fun i v hv => hg₀_val (eR i) v hv
  have hg_indep : ∀ c : Fin R → ZMod 2,
      IsSquare ((∏ i, g i ^ (c i).val : Kˣ) : K) → c = 0 := by
    intro c hsq
    have hsq' : IsSquare ((∏ j, g₀ j ^ (c (eR.symm j)).val : Kˣ) : K) := by
      have hprod : (∏ i, g i ^ (c i).val : Kˣ) = ∏ j, g₀ j ^ (c (eR.symm j)).val := by
        dsimp [g]
        exact Equiv.prod_comp eR (fun j => g₀ j ^ (c (eR.symm j)).val) |>.symm.trans
          (Finset.prod_congr rfl (fun i _ => by simp)) |>.symm
      rwa [← hprod]
    have hc0 := hg₀_indep (fun j => c (eR.symm j)) hsq'
    funext i
    have hi := congr_fun hc0 (eR i)
    simpa using hi
  let U : (Fin R → ZMod 2) → Kˣ := fun δ => ∏ i, g i ^ (δ i).val
  let e2R : Fin R ⊕ Fin R ≃ Fin (2 * R) :=
    finSumFinEquiv.trans (finCongr (Nat.two_mul R).symm)
  let P : (Fin (2 * R) → ZMod 2) → Kˣ × Kˣ :=
    fun α => (U (fun i => α (e2R (Sum.inl i))), U (fun i => α (e2R (Sum.inr i))))
  refine ⟨S_out, P, hS_sub, hS_out_disj, hv₀S_out, ?_, ?_, ?_, ?_⟩
  · dsimp [P, U]
    ext <;> simp [ZMod.val_zero]
  · intro α β
    exact ⟨prodBasis_add_isSquare g (fun i => α (e2R (Sum.inl i))) (fun i => β (e2R (Sum.inl i))),
           prodBasis_add_isSquare g (fun i => α (e2R (Sum.inr i))) (fun i => β (e2R (Sum.inr i)))⟩
  · intro α v hvT hvS_out hv₀
    have hv_not : v ∉ S_fin₀ := by
      rw [hmem_S_fin₀, not_or, not_or]
      exact ⟨hvT, hvS_out, hv₀⟩
    exact ⟨evenVal_of_val_eq_one v _ (prodBasis_val_eq_one g v (fun i => hg_val i v hv_not) _),
           evenVal_of_val_eq_one v _ (prodBasis_val_eq_one g v (fun i => hg_val i v hv_not) _)⟩
  · have hU_inj : ∀ δ₁ δ₂ : Fin R → ZMod 2,
        (∀ v ∈ S_fin₀, IsSquare (algebraMap K (v.adicCompletion K) ((U δ₁ * U δ₂ : Kˣ) : K))) →
        (∀ w : NumberField.InfinitePlace K,
          IsSquare (algebraMap K w.Completion ((U δ₁ * U δ₂ : Kˣ) : K))) →
        δ₁ = δ₂ := by
      intro δ₁ δ₂ hloc_fin hloc_inf
      let δ := δ₁ + δ₂
      let u : Kˣ := U δ
      have hu_diff_sq : IsSquare ((u : K) * ((U δ₁ * U δ₂ : Kˣ) : K)) :=
        prodBasis_add_isSquare g δ₁ δ₂
      have hu_val_one : ∀ v ∉ S_fin₀, v.valuationOfNeZero u = 1 :=
        fun v hv => prodBasis_val_eq_one g v (fun i => hg_val i v hv) δ
      have hu_even : ∀ v ∉ S_fin₀, EvenVal v u :=
        fun v hv => evenVal_of_val_eq_one v u (hu_val_one v hv)
      have hu_fin₀ : ∀ v ∈ S_fin₀, IsSquare (algebraMap K (v.adicCompletion K) (u : K)) := by
        intro v hv
        have hmap_diff : IsSquare (((Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom u :
            (v.adicCompletion K)ˣ) : v.adicCompletion K) *
            ((Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom (U δ₁ * U δ₂) :
              (v.adicCompletion K)ˣ) : v.adicCompletion K)) := by
          change IsSquare (algebraMap K (v.adicCompletion K) (u : K) *
            algebraMap K (v.adicCompletion K) ((U δ₁ * U δ₂ : Kˣ) : K))
          rw [← map_mul]
          exact hu_diff_sq.map (algebraMap K (v.adicCompletion K))
        exact isSquare_unit_left_of_mul_of_right
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom u)
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom (U δ₁ * U δ₂))
          hmap_diff (hloc_fin v hv)
      have hu_inf : ∀ w : NumberField.InfinitePlace K, IsSquare (algebraMap K w.Completion (u : K)) := by
        intro w
        have hmap_diff : IsSquare (((Units.map (algebraMap K w.Completion).toMonoidHom u :
            (w.Completion)ˣ) : w.Completion) *
            ((Units.map (algebraMap K w.Completion).toMonoidHom (U δ₁ * U δ₂) :
              (w.Completion)ˣ) : w.Completion)) := by
          change IsSquare (algebraMap K w.Completion (u : K) *
            algebraMap K w.Completion ((U δ₁ * U δ₂ : Kˣ) : K))
          rw [← map_mul]
          exact hu_diff_sq.map (algebraMap K w.Completion)
        exact isSquare_unit_left_of_mul_of_right
          (Units.map (algebraMap K w.Completion).toMonoidHom u)
          (Units.map (algebraMap K w.Completion).toMonoidHom (U δ₁ * U δ₂))
          hmap_diff (hloc_inf w)
      have hT_sub_S_fin₀ : T ⊆ S_fin₀ := by
        intro v hvT
        rw [hmem_S_fin₀]
        exact Or.inl hvT
      have hu_fin_all : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          IsSquare (algebraMap K (v.adicCompletion K) (u : K)) :=
        isSquare_everywhere_of_isSquare_on_sFin a₁ a₂ a₃ h₁₂ h₁₃ h₂₃ hint₁ hint₂ hint₃
          T S_fin₀ hT hT_sub_S_fin₀ hS_fin₀_gen u hu_even hu_fin₀ hu_inf
      have hu_global_sq : IsSquare (u : K) := by
        by_contra hu_not_sq
        obtain ⟨L, instF_L, instNF_L, instAlg_L, N, S_fin, S_fin_L,
            hS_fin₀_sub, hS_fin_L_gen, hR_L_eq, hu_sq_L, hH90, hval_KL⟩ :=
          exists_quadratic_split_extension_of_isSquare_everywhere u hu_not_sq hu_fin_all hu_inf
            S_fin₀ hS_fin₀_gen
        letI := instF_L
        letI := instNF_L
        letI := instAlg_L
        have hS_fin_gen : ∀ c : ClassGroup (NumberField.RingOfIntegers K),
            ∃ I : nonZeroDivisors (Ideal (NumberField.RingOfIntegers K)),
              ClassGroup.mk0 I = c ∧
              ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
                v ∉ S_fin → ¬ (v.asIdeal ∣ (I : Ideal (NumberField.RingOfIntegers K))) := by
          intro c
          obtain ⟨I, hIc, hIdiv⟩ := hS_fin₀_gen c
          exact ⟨I, hIc, fun v hv => hIdiv v (fun hv₀ => hv (hS_fin₀_sub hv₀))⟩
        obtain ⟨g_K, hg_K_val, hg_K_indep, hg_K_span⟩ :=
          sUnit_sqCl_basis_of_classGroup_gen u_unit_K hu_K_val hu_K_indep hu_K_span S_fin hS_fin_gen
        obtain ⟨u_unit_L, hu_L_val, hu_L_indep, hu_L_span⟩ := unit_sqCl_basis (F := L)
        obtain ⟨g_L, hg_L_val, hg_L_indep, hg_L_span⟩ :=
          sUnit_sqCl_basis_of_classGroup_gen u_unit_L hu_L_val hu_L_indep hu_L_span S_fin_L hS_fin_L_gen
        let R_K := NumberField.InfinitePlace.nrRealPlaces K +
          NumberField.InfinitePlace.nrComplexPlaces K + S_fin.card
        let R_L := NumberField.InfinitePlace.nrRealPlaces L +
          NumberField.InfinitePlace.nrComplexPlaces L + S_fin_L.card
        let X : (Fin R_K → ZMod 2) → Kˣ := fun ξ => ∏ i, g_K i ^ (ξ i).val
        let Y : (Fin R_L → ZMod 2) → Lˣ := fun γ => ∏ i, g_L i ^ (γ i).val
        have hY_val : ∀ γ : Fin R_L → ZMod 2, ∀ w ∉ S_fin_L, w.valuationOfNeZero (Y γ) = 1 :=
          fun γ w hw => prodBasis_val_eq_one g_L w (fun i => hg_L_val i w hw) γ
        have hX_val : ∀ ξ : Fin R_K → ZMod 2, ∀ v ∉ S_fin, v.valuationOfNeZero (X ξ) = 1 :=
          fun ξ v hv => prodBasis_val_eq_one g_K v (fun i => hg_K_val i v hv) ξ
        have hNY_span : ∀ γ : Fin R_L → ZMod 2,
            ∃ c : Fin R_K → ZMod 2, IsSquare (((N (Y γ) : Kˣ) : K) * (X c : K)) :=
          fun γ => hg_K_span (N (Y γ)) (hH90 (Y γ) (hY_val γ)).1
        choose ν hν using hNY_span
        have hX_L_span : ∀ ξ : Fin R_K → ZMod 2,
            ∃ γ : Fin R_L → ZMod 2,
              IsSquare (((Units.map (algebraMap K L).toMonoidHom (X ξ) : Lˣ) : L) * (Y γ : L)) :=
          fun ξ => hg_L_span (Units.map (algebraMap K L).toMonoidHom (X ξ))
            (hval_KL (X ξ) (hX_val ξ))
        choose μ hμ using hX_L_span
        let sec : (Fin R_K → ZMod 2) → (Fin R_L → ZMod 2) :=
          fun c => if h : ∃ γ : Fin R_L → ZMod 2, ν γ = c then Classical.choose h else 0
        let Φ : (Fin R_K → ZMod 2) × (Fin R_K → ZMod 2) → (Fin R_L → ZMod 2) :=
          fun p => sec p.1 + μ p.2
        have hΦ_surj : Function.Surjective Φ := by
          intro γ
          let c := ν γ
          have hc_ex : ∃ γ' : Fin R_L → ZMod 2, ν γ' = c := ⟨γ, rfl⟩
          have hsec_c : ν (sec c) = c := by
            dsimp [sec]
            rw [dif_pos hc_ex]
            exact Classical.choose_spec hc_ex
          let γ' := sec c
          have hNY_γ_γ' : IsSquare (((N (Y γ) : Kˣ) : K) * ((N (Y γ') : Kˣ) : K)) := by
            have h1 : IsSquare (((N (Y γ) : Kˣ) : K) * (X c : K)) := hν γ
            have h2 : IsSquare ((X c : K) * ((N (Y γ') : Kˣ) : K)) := by
              rw [mul_comm, ← hsec_c]
              exact hν γ'
            exact isSquare_unit_trans (N (Y γ)) (X c) (N (Y γ')) h1 h2
          have hY_add_sq : IsSquare (((Y (γ + γ') : Lˣ) : L) * (((Y γ * Y γ' : Lˣ) : L))) :=
            prodBasis_add_isSquare g_L γ γ'
          have hNY_add_diff : IsSquare (((N (Y (γ + γ')) : Kˣ) : K) *
              (((N (Y γ) * N (Y γ') : Kˣ) : K))) := by
            rcases hY_add_sq with ⟨s, hs⟩
            have hs_ne : s ≠ 0 := by
              intro hs0
              have h0 : ((Y (γ + γ') : Lˣ) : L) * (((Y γ * Y γ' : Lˣ) : L)) = 0 := by
                rw [hs, hs0, mul_zero]
              exact mul_ne_zero (Y (γ + γ')).ne_zero (Y γ * Y γ').ne_zero h0
            let s_u : Lˣ := Units.mk0 s hs_ne
            have hu_eq : Y (γ + γ') * (Y γ * Y γ') = s_u * s_u := by
              ext
              exact hs
            refine ⟨((N s_u : Kˣ) : K), ?_⟩
            norm_cast
            rw [← map_mul, ← map_mul, hu_eq, map_mul]
          have hNY_sum_sq : IsSquare ((N (Y (γ + γ')) : Kˣ) : K) := by
            have hmul_sq : IsSquare ((((N (Y γ) * N (Y γ') : Kˣ) : K))) := by
              simpa only [Units.val_mul] using hNY_γ_γ'
            exact isSquare_unit_left_of_mul_of_right (N (Y (γ + γ'))) (N (Y γ) * N (Y γ'))
              hNY_add_diff hmul_sq
          obtain ⟨x, hx_even, hx_sq_L⟩ := (hH90 (Y (γ + γ')) (hY_val (γ + γ'))).2 hNY_sum_sq
          obtain ⟨ξ, hξ_sq_K⟩ := hg_K_span x hx_even
          have hξ_sq_L : IsSquare (((Units.map (algebraMap K L).toMonoidHom x : Lˣ) : L) *
              ((Units.map (algebraMap K L).toMonoidHom (X ξ) : Lˣ) : L)) := by
            change IsSquare (algebraMap K L (x : K) * algebraMap K L (X ξ : K))
            rw [← map_mul]
            exact hξ_sq_K.map (algebraMap K L)
          have hY_Xξ_sq : IsSquare (((Y (γ + γ') : Lˣ) : L) *
              ((Units.map (algebraMap K L).toMonoidHom (X ξ) : Lˣ) : L)) :=
            isSquare_unit_trans (Y (γ + γ'))
              (Units.map (algebraMap K L).toMonoidHom x)
              (Units.map (algebraMap K L).toMonoidHom (X ξ))
              hx_sq_L hξ_sq_L
          have hY_μξ_sq : IsSquare (((Y (γ + γ') : Lˣ) : L) * ((Y (μ ξ) : Lˣ) : L)) :=
            isSquare_unit_trans (Y (γ + γ'))
              (Units.map (algebraMap K L).toMonoidHom (X ξ))
              (Y (μ ξ))
              hY_Xξ_sq (hμ ξ)
          have h_eq : γ + γ' = μ ξ := prodBasis_unique g_L hg_L_indep (γ + γ') (μ ξ) hY_μξ_sq
          refine ⟨(c, ξ), ?_⟩
          dsimp [Φ]
          change γ' + μ ξ = γ
          rw [← h_eq]
          exact zmod2_fun_add_cancel_left γ' γ
        have hcard_eq : Fintype.card ((Fin R_K → ZMod 2) × (Fin R_K → ZMod 2)) =
            Fintype.card (Fin R_L → ZMod 2) := by
          rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin,
              Fintype.card_fin, ZMod.card 2, ← pow_add, ← Nat.two_mul]
          dsimp [R_L, R_K] at hR_L_eq ⊢
          rw [hR_L_eq]
        have hΦ_inj : Function.Injective Φ :=
          ((Fintype.bijective_iff_surjective_and_card Φ).mpr ⟨hΦ_surj, hcard_eq⟩).1
        have hu_even_S_fin : ∀ v ∉ S_fin, EvenVal v u :=
          fun v hv => hu_even v (fun hv₀ => hv (hS_fin₀_sub hv₀))
        obtain ⟨ξ_u, hξ_u_sq⟩ := hg_K_span u hu_even_S_fin
        have hξ_u_ne_zero : ξ_u ≠ 0 := by
          intro h0
          apply hu_not_sq
          have hX0 : (X ξ_u : K) = 1 := by
            rw [h0]
            dsimp [X]
            simp [ZMod.val_zero]
          rw [hX0, mul_one] at hξ_u_sq
          exact hξ_u_sq
        have hμ_ξ_u : μ ξ_u = 0 := by
          have hu_X_L : IsSquare (((Units.map (algebraMap K L).toMonoidHom u : Lˣ) : L) *
              ((Units.map (algebraMap K L).toMonoidHom (X ξ_u) : Lˣ) : L)) := by
            change IsSquare (algebraMap K L (u : K) * algebraMap K L (X ξ_u : K))
            rw [← map_mul]
            exact hξ_u_sq.map (algebraMap K L)
          have hX_L_sq : IsSquare (((Units.map (algebraMap K L).toMonoidHom (X ξ_u) : Lˣ) : L)) :=
            isSquare_unit_right_of_mul_of_left
              (Units.map (algebraMap K L).toMonoidHom u)
              (Units.map (algebraMap K L).toMonoidHom (X ξ_u))
              hu_X_L hu_sq_L
          have hY_sq : IsSquare ((Y (μ ξ_u) : Lˣ) : L) :=
            isSquare_unit_right_of_mul_of_left
              (Units.map (algebraMap K L).toMonoidHom (X ξ_u))
              (Y (μ ξ_u))
              (hμ ξ_u) hX_L_sq
          exact hg_L_indep (μ ξ_u) hY_sq
        have hμ_zero : μ 0 = 0 := by
          have hX0 : ((Units.map (algebraMap K L).toMonoidHom (X 0) : Lˣ) : L) = 1 := by
            change algebraMap K L (X 0 : K) = 1
            have : (X 0 : Kˣ) = 1 := by
              dsimp [X]
              simp [ZMod.val_zero]
            rw [this, Units.val_one, map_one]
          have hY0_sq : IsSquare ((Y (μ 0) : Lˣ) : L) := by
            have h := hμ 0
            rwa [hX0, one_mul] at h
          exact hg_L_indep (μ 0) hY0_sq
        have hΦ_eq : Φ (0, ξ_u) = Φ (0, 0) := by
          dsimp [Φ]
          rw [hμ_ξ_u, hμ_zero]
        have hpair_eq := hΦ_inj hΦ_eq
        injection hpair_eq with _ hξ_eq
        exact hξ_u_ne_zero hξ_eq
      exact zmod2_fun_eq_of_add_eq_zero δ₁ δ₂ (hg_indep δ hu_global_sq)
    intro α β hfin hinf
    have h1 : (fun i => α (e2R (Sum.inl i))) = (fun i => β (e2R (Sum.inl i))) :=
      hU_inj _ _ (fun v hv => (hfin v ((hmem_S_fin₀ v).mp hv)).1) (fun w => (hinf w).1)
    have h2 : (fun i => α (e2R (Sum.inr i))) = (fun i => β (e2R (Sum.inr i))) :=
      hU_inj _ _ (fun v hv => (hfin v ((hmem_S_fin₀ v).mp hv)).2) (fun w => (hinf w).2)
    funext j
    obtain ⟨s, rfl⟩ := e2R.surjective j
    rcases s with i | i
    · exact congr_fun h1 i
    · exact congr_fun h2 i

theorem archimedean_selmer_basis {K : Type u} [Field K] [NumberField K]
    (a₁ a₂ a₃ : K) (h₁₂ : a₁ ≠ a₂) (h₁₃ : a₁ ≠ a₃) (h₂₃ : a₂ ≠ a₃) :
    ∃ (Φ_inf Ψ_inf : Kˣ × Kˣ → (Fin (NumberField.InfinitePlace.nrRealPlaces K) → ZMod 2)),
      (∀ p q : Kˣ × Kˣ,
        IsSquare ((p.1 : K) * (q.1 : K)) → IsSquare ((p.2 : K) * (q.2 : K)) →
        Φ_inf p = Φ_inf q) ∧
      (∀ p q : Kˣ × Kˣ, Φ_inf (p.1 * q.1, p.2 * q.2) = Φ_inf p + Φ_inf q) ∧
      (∀ p : Kˣ × Kˣ, Φ_inf p = 0 ↔
        ∀ w : NumberField.InfinitePlace K, IsDescentClass
          (algebraMap K w.Completion a₁) (algebraMap K w.Completion a₂) (algebraMap K w.Completion a₃)
          (algebraMap K w.Completion (p.1 : K)) (algebraMap K w.Completion (p.2 : K))) ∧
      (∀ q₁ q₂ : Kˣ × Kˣ, Φ_inf q₁ = 0 → Φ_inf q₂ = 0 → Ψ_inf q₁ = Ψ_inf q₂ →
        ∀ w : NumberField.InfinitePlace K,
          IsSquare (algebraMap K w.Completion ((q₁.1 * q₂.1 : Kˣ) : K)) ∧
          IsSquare (algebraMap K w.Completion ((q₁.2 * q₂.2 : Kˣ) : K))) ∧
      (∀ q p : Kˣ × Kˣ, Φ_inf q = 0 →
        (∏ w : NumberField.InfinitePlace K, (hilbInf w (q.1 : K) (p.2 : K) * hilbInf w (q.2 : K) (p.1 : K))) =
          (-1 : ℤˣ) ^ (dotProduct (Ψ_inf q) (Φ_inf p)).val) :=
by
  classical
  have h_complex : ∀ (w : NumberField.InfinitePlace K), ¬ w.IsReal →
      (∀ z : w.Completion, IsSquare z) ∧
      (∀ p : Kˣ × Kˣ, IsDescentClass
        (algebraMap K w.Completion a₁) (algebraMap K w.Completion a₂) (algebraMap K w.Completion a₃)
        (algebraMap K w.Completion (p.1 : K)) (algebraMap K w.Completion (p.2 : K))) ∧
      (∀ q p : Kˣ × Kˣ, hilbInf w (q.1 : K) (p.2 : K) * hilbInf w (q.2 : K) (p.1 : K) = 1) := by
    intro w hw
    have hc : w.IsComplex := NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw
    have e : w.Completion ≃+* ℂ :=
      NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hc
    have hsq : ∀ z : w.Completion, IsSquare z := by
      intro z
      obtain ⟨c, hc2⟩ := IsAlgClosed.exists_pow_nat_eq (e z) (n := 2) (by norm_num)
      refine ⟨e.symm c, e.injective ?_⟩
      rw [map_mul, RingEquiv.apply_symm_apply, ← sq, hc2]
    refine ⟨hsq, ?_, ?_⟩
    · intro p
      obtain ⟨s₁, hs₁⟩ := hsq (algebraMap K w.Completion (p.1 : K))
      obtain ⟨s₂, hs₂⟩ := hsq (algebraMap K w.Completion (p.2 : K))
      refine ⟨0, s₂, s₁, 1, ?_, ?_, ?_⟩
      · rintro ⟨_, _, _, h⟩
        exact one_ne_zero h
      · rw [hs₁, hs₂]
        ring
      · rw [hs₁, hs₂]
        ring
    · intro q p
      have hcomplex_one : ∀ (a : Kˣ) (b : K), hilbInf w (a : K) b = 1 := by
        intro a b
        obtain ⟨s, hs⟩ := hsq (algebraMap K w.Completion (a : K))⁻¹
        have ha0 : algebraMap K w.Completion (a : K) ≠ 0 := by
          rw [ne_eq, map_eq_zero]
          exact a.ne_zero
        have hex : ∃ x y : w.Completion,
            algebraMap K w.Completion (a : K) * x ^ 2 + algebraMap K w.Completion b * y ^ 2 = 1 := by
          refine ⟨s, 0, ?_⟩
          calc algebraMap K w.Completion (a : K) * s ^ 2 + algebraMap K w.Completion b * 0 ^ 2
              = algebraMap K w.Completion (a : K) * (s * s) := by ring
            _ = algebraMap K w.Completion (a : K) * (algebraMap K w.Completion (a : K))⁻¹ := by rw [← hs]
            _ = 1 := mul_inv_cancel₀ ha0
        simp only [hilbInf, hilbInfLoc]
        exact if_pos hex
      rw [hcomplex_one q.1 (p.2 : K), hcomplex_one q.2 (p.1 : K), mul_one]
  let s_w (w : NumberField.InfinitePlace K) (hw : w.IsReal) (u : Kˣ) : Bool :=
    decide (NumberField.InfinitePlace.embedding_of_isReal hw (u : K) < 0)
  have s_w_isSquare : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal) (u : Kˣ),
      IsSquare (algebraMap K w.Completion (u : K)) ↔ s_w w hw u = false := by
    intro w hw u
    set σ := NumberField.InfinitePlace.embedding_of_isReal hw
    set Φ := NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
    have hbij : Function.Bijective (⇑Φ) :=
      NumberField.InfinitePlace.Completion.bijective_extensionEmbeddingOfIsReal hw
    have hcoe : ∀ x : K, Φ (algebraMap K w.Completion x) = σ x := fun x =>
      NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw x
    dsimp [s_w]
    rw [decide_eq_false_iff_not, not_lt]
    constructor
    · rintro ⟨z, hz⟩
      have hR : Φ (algebraMap K w.Completion (u : K)) = Φ (z * z) := congrArg Φ hz
      rw [hcoe, map_mul] at hR
      rw [hR]
      exact mul_self_nonneg (Φ z)
    · intro hnonneg
      obtain ⟨z, hz⟩ := hbij.surjective (Real.sqrt (σ (u : K)))
      refine ⟨z, hbij.injective ?_⟩
      rw [hcoe, map_mul, hz, Real.mul_self_sqrt hnonneg]
  have s_w_mul : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal) (u v : Kˣ),
      s_w w hw (u * v) = xor (s_w w hw u) (s_w w hw v) := by
    intro w hw u v
    set σ := NumberField.InfinitePlace.embedding_of_isReal hw
    have hu0 : σ (u : K) ≠ 0 := fun h => u.ne_zero (σ.injective (by rw [h, map_zero]))
    have hv0 : σ (v : K) ≠ 0 := fun h => v.ne_zero (σ.injective (by rw [h, map_zero]))
    change decide (σ (((u * v : Kˣ) : K)) < 0) =
      xor (decide (σ (u : K) < 0)) (decide (σ (v : K) < 0))
    rw [Units.val_mul, map_mul]
    rcases lt_or_gt_of_ne hu0 with hun | hup <;> rcases lt_or_gt_of_ne hv0 with hvn | hvp
    · have hpos : ¬ (σ (u : K) * σ (v : K) < 0) := not_lt.mpr (mul_pos_of_neg_of_neg hun hvn).le
      simp [hun, hvn, hpos]
    · have hneg : σ (u : K) * σ (v : K) < 0 := mul_neg_of_neg_of_pos hun hvp
      have hvp' : ¬ (σ (v : K) < 0) := not_lt.mpr hvp.le
      simp [hun, hvp', hneg]
    · have hneg : σ (u : K) * σ (v : K) < 0 := mul_neg_of_pos_of_neg hup hvn
      have hup' : ¬ (σ (u : K) < 0) := not_lt.mpr hup.le
      simp [hup', hvn, hneg]
    · have hpos : ¬ (σ (u : K) * σ (v : K) < 0) := not_lt.mpr (mul_pos hup hvp).le
      have hup' : ¬ (σ (u : K) < 0) := not_lt.mpr hup.le
      have hvp' : ¬ (σ (v : K) < 0) := not_lt.mpr hvp.le
      simp [hup', hvp', hpos]
  have xor_eq_false_iff : ∀ a b : Bool, xor a b = false ↔ a = b := by decide
  have s_w_congr_of_isSquare : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal) (u v : Kˣ),
      IsSquare ((u : K) * (v : K)) → s_w w hw u = s_w w hw v := by
    intro w hw u v hsq
    have hsq_loc : IsSquare (algebraMap K w.Completion (((u * v : Kˣ) : K))) := by
      rw [Units.val_mul]
      exact hsq.map (algebraMap K w.Completion)
    have h1 := (s_w_isSquare w hw (u * v)).mp hsq_loc
    rw [s_w_mul] at h1
    exact (xor_eq_false_iff _ _).mp h1
  have hilbInf_eq_if_s_w : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal) (u v : Kˣ),
      hilbInf w (u : K) (v : K) = if (s_w w hw u && s_w w hw v) then (-1 : ℤˣ) else 1 := by
    intro w hw u v
    set σ := NumberField.InfinitePlace.embedding_of_isReal hw
    set Φ := NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
    have hbij : Function.Bijective (⇑Φ) :=
      NumberField.InfinitePlace.Completion.bijective_extensionEmbeddingOfIsReal hw
    have hcoe : ∀ x : K, Φ (algebraMap K w.Completion x) = σ x := fun x =>
      NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw x
    have hilbInf_pos_left : ∀ (a b : K), 0 < σ a → hilbInf w a b = 1 := by
      intro a b ha
      obtain ⟨x, hx⟩ := hbij.surjective (Real.sqrt (σ a)⁻¹)
      have hex : ∃ x y : w.Completion,
          algebraMap K w.Completion a * x ^ 2 + algebraMap K w.Completion b * y ^ 2 = 1 := by
        refine ⟨x, 0, hbij.injective ?_⟩
        simp only [map_add, map_mul, map_pow, hcoe, hx, map_zero,
          zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero, map_one]
        rw [Real.sq_sqrt (inv_nonneg.mpr ha.le)]
        exact mul_inv_cancel₀ (ne_of_gt ha)
      simp only [hilbInf, hilbInfLoc]
      exact if_pos hex
    have hilbInf_pos_right : ∀ (a b : K), 0 < σ b → hilbInf w a b = 1 := by
      intro a b hb
      obtain ⟨y, hy⟩ := hbij.surjective (Real.sqrt (σ b)⁻¹)
      have hex : ∃ x y : w.Completion,
          algebraMap K w.Completion a * x ^ 2 + algebraMap K w.Completion b * y ^ 2 = 1 := by
        refine ⟨0, y, hbij.injective ?_⟩
        simp only [map_add, map_mul, map_pow, hcoe, hy, map_zero,
          zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add, map_one]
        rw [Real.sq_sqrt (inv_nonneg.mpr hb.le)]
        exact mul_inv_cancel₀ (ne_of_gt hb)
      simp only [hilbInf, hilbInfLoc]
      exact if_pos hex
    have hilbInf_neg : ∀ (a b : K), σ a < 0 → σ b < 0 → hilbInf w a b = -1 := by
      intro a b ha hb
      have hne : ¬ (∃ x y : w.Completion,
          algebraMap K w.Completion a * x ^ 2 + algebraMap K w.Completion b * y ^ 2 = 1) := by
        rintro ⟨x, y, hxy⟩
        have hR : Φ (algebraMap K w.Completion a * x ^ 2 + algebraMap K w.Completion b * y ^ 2) = Φ 1 :=
          congrArg Φ hxy
        simp only [map_add, map_mul, map_pow, hcoe, map_one] at hR
        nlinarith [sq_nonneg (Φ x), sq_nonneg (Φ y),
          mul_nonpos_of_nonpos_of_nonneg ha.le (sq_nonneg (Φ x)),
          mul_nonpos_of_nonpos_of_nonneg hb.le (sq_nonneg (Φ y))]
      simp only [hilbInf, hilbInfLoc]
      exact if_neg hne
    have hu0 : σ (u : K) ≠ 0 := fun h => u.ne_zero (σ.injective (by rw [h, map_zero]))
    have hv0 : σ (v : K) ≠ 0 := fun h => v.ne_zero (σ.injective (by rw [h, map_zero]))
    change hilbInf w (u : K) (v : K) =
      if (decide (σ (u : K) < 0) && decide (σ (v : K) < 0)) then (-1 : ℤˣ) else 1
    rcases lt_or_gt_of_ne hu0 with hun | hup <;> rcases lt_or_gt_of_ne hv0 with hvn | hvp
    · rw [hilbInf_neg (u : K) (v : K) hun hvn]
      simp [hun, hvn]
    · rw [hilbInf_pos_right (u : K) (v : K) hvp]
      have hvp' : ¬ (σ (v : K) < 0) := not_lt.mpr hvp.le
      simp [hun, hvp']
    · rw [hilbInf_pos_left (u : K) (v : K) hup]
      have hup' : ¬ (σ (u : K) < 0) := not_lt.mpr hup.le
      simp [hup', hvn]
    · rw [hilbInf_pos_left (u : K) (v : K) hup]
      have hup' : ¬ (σ (u : K) < 0) := not_lt.mpr hup.le
      simp [hup']
  let φ_bool (w : NumberField.InfinitePlace K) (hw : w.IsReal) (p : Kˣ × Kˣ) : Bool :=
    if NumberField.InfinitePlace.embedding_of_isReal hw a₁ <
         NumberField.InfinitePlace.embedding_of_isReal hw a₂ ∧
       NumberField.InfinitePlace.embedding_of_isReal hw a₁ <
         NumberField.InfinitePlace.embedding_of_isReal hw a₃ then
      s_w w hw p.1
    else if NumberField.InfinitePlace.embedding_of_isReal hw a₂ <
         NumberField.InfinitePlace.embedding_of_isReal hw a₁ ∧
       NumberField.InfinitePlace.embedding_of_isReal hw a₂ <
         NumberField.InfinitePlace.embedding_of_isReal hw a₃ then
      s_w w hw p.2
    else
      xor (s_w w hw p.1) (s_w w hw p.2)
  let ψ_bool (w : NumberField.InfinitePlace K) (hw : w.IsReal) (q : Kˣ × Kˣ) : Bool :=
    if NumberField.InfinitePlace.embedding_of_isReal hw a₁ <
         NumberField.InfinitePlace.embedding_of_isReal hw a₂ ∧
       NumberField.InfinitePlace.embedding_of_isReal hw a₁ <
         NumberField.InfinitePlace.embedding_of_isReal hw a₃ then
      s_w w hw q.2
    else if NumberField.InfinitePlace.embedding_of_isReal hw a₂ <
         NumberField.InfinitePlace.embedding_of_isReal hw a₁ ∧
       NumberField.InfinitePlace.embedding_of_isReal hw a₂ <
         NumberField.InfinitePlace.embedding_of_isReal hw a₃ then
      s_w w hw q.1
    else
      s_w w hw q.1
  have h_real_descent : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal) (p : Kˣ × Kˣ),
      IsDescentClass
        (algebraMap K w.Completion a₁) (algebraMap K w.Completion a₂) (algebraMap K w.Completion a₃)
        (algebraMap K w.Completion (p.1 : K)) (algebraMap K w.Completion (p.2 : K)) ↔
      φ_bool w hw p = false := by
    intro w hw p
    set σ := NumberField.InfinitePlace.embedding_of_isReal hw
    set Φ := NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
    have hbij : Function.Bijective (⇑Φ) :=
      NumberField.InfinitePlace.Completion.bijective_extensionEmbeddingOfIsReal hw
    have hcoe : ∀ x : K, Φ (algebraMap K w.Completion x) = σ x := fun x =>
      NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw x
    have hA12 : σ a₁ ≠ σ a₂ := fun h => h₁₂ (σ.injective h)
    have hA13 : σ a₁ ≠ σ a₃ := fun h => h₁₃ (σ.injective h)
    have hA23 : σ a₂ ≠ σ a₃ := fun h => h₂₃ (σ.injective h)
    have hD1 : σ (p.1 : K) ≠ 0 := fun h => p.1.ne_zero (σ.injective (by rw [h, map_zero]))
    have hD2 : σ (p.2 : K) ≠ 0 := fun h => p.2.ne_zero (σ.injective (by rw [h, map_zero]))
    have descent_signs :
        IsDescentClass
          (algebraMap K w.Completion a₁) (algebraMap K w.Completion a₂) (algebraMap K w.Completion a₃)
          (algebraMap K w.Completion (p.1 : K)) (algebraMap K w.Completion (p.2 : K)) →
        (0 < σ (p.1 : K) ∧ 0 < σ (p.2 : K)) ∨
        (σ (p.1 : K) < 0 ∧ 0 < σ (p.2 : K) ∧ σ a₂ < σ a₁ ∧ σ a₂ < σ a₃) ∨
        (0 < σ (p.1 : K) ∧ σ (p.2 : K) < 0 ∧ σ a₁ < σ a₂ ∧ σ a₁ < σ a₃) ∨
        (σ (p.1 : K) < 0 ∧ σ (p.2 : K) < 0 ∧ σ a₃ < σ a₁ ∧ σ a₃ < σ a₂) := by
      rintro ⟨z₀, z₁, z₂, z₃, hnz, heq1, heq2⟩
      set Z₀ := Φ z₀
      set Z₁ := Φ z₁
      set Z₂ := Φ z₂
      set Z₃ := Φ z₃
      have hZ_nz : ¬ (Z₀ = 0 ∧ Z₁ = 0 ∧ Z₂ = 0 ∧ Z₃ = 0) := by
        rintro ⟨h0, h1, h2, h3⟩
        apply hnz
        exact ⟨hbij.injective (by rw [map_zero]; exact h0),
               hbij.injective (by rw [map_zero]; exact h1),
               hbij.injective (by rw [map_zero]; exact h2),
               hbij.injective (by rw [map_zero]; exact h3)⟩
      have hE1 : σ (p.1 : K) * Z₁ ^ 2 - σ (p.2 : K) * Z₂ ^ 2 = (σ a₂ - σ a₁) * Z₀ ^ 2 := by
        have h := congrArg Φ heq1
        simpa only [map_sub, map_mul, map_pow, hcoe] using h
      have hE2 : σ (p.1 : K) * Z₁ ^ 2 - σ (p.1 : K) * σ (p.2 : K) * Z₃ ^ 2 = (σ a₃ - σ a₁) * Z₀ ^ 2 := by
        have h := congrArg Φ heq2
        simpa only [map_sub, map_mul, map_pow, hcoe] using h
      have hE3 : σ (p.2 : K) * Z₂ ^ 2 - σ (p.1 : K) * σ (p.2 : K) * Z₃ ^ 2 = (σ a₃ - σ a₂) * Z₀ ^ 2 := by
        linear_combination hE2 - hE1
      have hZ0_zero : Z₀ = 0 → 0 < σ (p.1 : K) ∧ 0 < σ (p.2 : K) := by
        intro hZ0
        have h1 : σ (p.1 : K) * (Z₁ ^ 2 - σ (p.2 : K) * Z₃ ^ 2) = 0 := by
          calc σ (p.1 : K) * (Z₁ ^ 2 - σ (p.2 : K) * Z₃ ^ 2)
            _ = (σ a₃ - σ a₁) * Z₀ ^ 2 := by linear_combination hE2
            _ = 0 := by rw [hZ0]; ring
        have h2 : σ (p.2 : K) * (Z₂ ^ 2 - σ (p.1 : K) * Z₃ ^ 2) = 0 := by
          calc σ (p.2 : K) * (Z₂ ^ 2 - σ (p.1 : K) * Z₃ ^ 2)
            _ = (σ a₃ - σ a₂) * Z₀ ^ 2 := by linear_combination hE3
            _ = 0 := by rw [hZ0]; ring
        have h1' : Z₁ ^ 2 = σ (p.2 : K) * Z₃ ^ 2 :=
          sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hD1)
        have h2' : Z₂ ^ 2 = σ (p.1 : K) * Z₃ ^ 2 :=
          sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hD2)
        have hZ3_nz : Z₃ ≠ 0 := by
          intro hZ3
          have hZ1 : Z₁ = 0 := sq_eq_zero_iff.mp (by rw [h1', hZ3]; ring)
          have hZ2 : Z₂ = 0 := sq_eq_zero_iff.mp (by rw [h2', hZ3]; ring)
          exact hZ_nz ⟨hZ0, hZ1, hZ2, hZ3⟩
        have hZ3_pos : 0 < Z₃ ^ 2 := sq_pos_of_ne_zero hZ3_nz
        have hD1_nonneg : 0 ≤ σ (p.1 : K) := by
          nlinarith [sq_nonneg Z₂, h2', hZ3_pos]
        have hD2_nonneg : 0 ≤ σ (p.2 : K) := by
          nlinarith [sq_nonneg Z₁, h1', hZ3_pos]
        exact ⟨lt_of_le_of_ne hD1_nonneg hD1.symm, lt_of_le_of_ne hD2_nonneg hD2.symm⟩
      by_cases hZ0 : Z₀ = 0
      · exact Or.inl (hZ0_zero hZ0)
      · have hZ0_pos : 0 < Z₀ ^ 2 := sq_pos_of_ne_zero hZ0
        rcases lt_or_gt_of_ne hD1 with hD1_neg | hD1_pos <;>
          rcases lt_or_gt_of_ne hD2 with hD2_neg | hD2_pos
        · right; right; right
          have hle1 : σ a₃ ≤ σ a₁ := by
            nlinarith [hE2, hZ0_pos, sq_nonneg Z₁, sq_nonneg Z₃,
              mul_nonpos_of_nonpos_of_nonneg hD1_neg.le (sq_nonneg Z₁),
              mul_nonneg (mul_pos_of_neg_of_neg hD1_neg hD2_neg).le (sq_nonneg Z₃)]
          have hle2 : σ a₃ ≤ σ a₂ := by
            nlinarith [hE3, hZ0_pos, sq_nonneg Z₂, sq_nonneg Z₃,
              mul_nonpos_of_nonpos_of_nonneg hD2_neg.le (sq_nonneg Z₂),
              mul_nonneg (mul_pos_of_neg_of_neg hD1_neg hD2_neg).le (sq_nonneg Z₃)]
          exact ⟨hD1_neg, hD2_neg, lt_of_le_of_ne hle1 hA13.symm, lt_of_le_of_ne hle2 hA23.symm⟩
        · right; left
          have hle1 : σ a₂ ≤ σ a₁ := by
            nlinarith [hE1, hZ0_pos, sq_nonneg Z₁, sq_nonneg Z₂,
              mul_nonpos_of_nonpos_of_nonneg hD1_neg.le (sq_nonneg Z₁),
              mul_nonneg hD2_pos.le (sq_nonneg Z₂)]
          have hle2 : σ a₂ ≤ σ a₃ := by
            nlinarith [hE3, hZ0_pos, sq_nonneg Z₂, sq_nonneg Z₃,
              mul_nonneg hD2_pos.le (sq_nonneg Z₂),
              mul_nonpos_of_nonpos_of_nonneg (mul_neg_of_neg_of_pos hD1_neg hD2_pos).le (sq_nonneg Z₃)]
          exact ⟨hD1_neg, hD2_pos, lt_of_le_of_ne hle1 hA12.symm, lt_of_le_of_ne hle2 hA23⟩
        · right; right; left
          have hle1 : σ a₁ ≤ σ a₂ := by
            nlinarith [hE1, hZ0_pos, sq_nonneg Z₁, sq_nonneg Z₂,
              mul_nonneg hD1_pos.le (sq_nonneg Z₁),
              mul_nonpos_of_nonpos_of_nonneg hD2_neg.le (sq_nonneg Z₂)]
          have hle2 : σ a₁ ≤ σ a₃ := by
            nlinarith [hE2, hZ0_pos, sq_nonneg Z₁, sq_nonneg Z₃,
              mul_nonneg hD1_pos.le (sq_nonneg Z₁),
              mul_nonpos_of_nonpos_of_nonneg (mul_neg_of_pos_of_neg hD1_pos hD2_neg).le (sq_nonneg Z₃)]
          exact ⟨hD1_pos, hD2_neg, lt_of_le_of_ne hle1 hA12, lt_of_le_of_ne hle2 hA13⟩
        · exact Or.inl ⟨hD1_pos, hD2_pos⟩
    have real_descent_of_real_sol : ∀ (Z₀ Z₁ Z₂ Z₃ : ℝ),
        (Z₀ ≠ 0 ∨ Z₃ ≠ 0) →
        σ (p.1 : K) * Z₁ ^ 2 - σ (p.2 : K) * Z₂ ^ 2 = (σ a₂ - σ a₁) * Z₀ ^ 2 →
        σ (p.1 : K) * Z₁ ^ 2 - σ (p.1 : K) * σ (p.2 : K) * Z₃ ^ 2 = (σ a₃ - σ a₁) * Z₀ ^ 2 →
        IsDescentClass
          (algebraMap K w.Completion a₁) (algebraMap K w.Completion a₂) (algebraMap K w.Completion a₃)
          (algebraMap K w.Completion (p.1 : K)) (algebraMap K w.Completion (p.2 : K)) := by
      intro Z₀ Z₁ Z₂ Z₃ hnz h1 h2
      obtain ⟨z₀, hz₀⟩ := hbij.surjective Z₀
      obtain ⟨z₁, hz₁⟩ := hbij.surjective Z₁
      obtain ⟨z₂, hz₂⟩ := hbij.surjective Z₂
      obtain ⟨z₃, hz₃⟩ := hbij.surjective Z₃
      refine ⟨z₀, z₁, z₂, z₃, ?_, hbij.injective ?_, hbij.injective ?_⟩
      · rintro ⟨rz0, _, _, rz3⟩
        rcases hnz with hZ0 | hZ3
        · apply hZ0
          rw [← hz₀, rz0, map_zero]
        · apply hZ3
          rw [← hz₃, rz3, map_zero]
      · simp only [map_sub, map_mul, map_pow, hcoe, hz₀, hz₁, hz₂]
        exact h1
      · simp only [map_sub, map_mul, map_pow, hcoe, hz₀, hz₁, hz₃]
        exact h2
    have h_case_A : 0 < σ (p.1 : K) → 0 < σ (p.2 : K) →
        IsDescentClass
          (algebraMap K w.Completion a₁) (algebraMap K w.Completion a₂) (algebraMap K w.Completion a₃)
          (algebraMap K w.Completion (p.1 : K)) (algebraMap K w.Completion (p.2 : K)) := by
      intro h1 h2
      refine real_descent_of_real_sol 0 (Real.sqrt (σ (p.2 : K))) (Real.sqrt (σ (p.1 : K))) 1
        (Or.inr one_ne_zero) ?_ ?_
      · rw [Real.sq_sqrt h2.le, Real.sq_sqrt h1.le]
        ring
      · rw [Real.sq_sqrt h2.le]
        ring
    have h_case_B : σ a₁ < σ a₂ → σ a₁ < σ a₃ → 0 < σ (p.1 : K) → σ (p.2 : K) < 0 →
        IsDescentClass
          (algebraMap K w.Completion a₁) (algebraMap K w.Completion a₂) (algebraMap K w.Completion a₃)
          (algebraMap K w.Completion (p.1 : K)) (algebraMap K w.Completion (p.2 : K)) := by
      intro h12 h13 h1 h2
      refine real_descent_of_real_sol 1 0
        (Real.sqrt ((σ a₂ - σ a₁) / (-σ (p.2 : K))))
        (Real.sqrt ((σ a₃ - σ a₁) / (-(σ (p.1 : K) * σ (p.2 : K)))))
        (Or.inl one_ne_zero) ?_ ?_
      · have hdiv : 0 ≤ (σ a₂ - σ a₁) / (-σ (p.2 : K)) :=
          div_nonneg (sub_nonneg.mpr h12.le) (neg_nonneg.mpr h2.le)
        rw [Real.sq_sqrt hdiv]
        field_simp [hD2]
        ring
      · have hdiv : 0 ≤ (σ a₃ - σ a₁) / (-(σ (p.1 : K) * σ (p.2 : K))) :=
          div_nonneg (sub_nonneg.mpr h13.le) (neg_nonneg.mpr (mul_neg_of_pos_of_neg h1 h2).le)
        rw [Real.sq_sqrt hdiv]
        field_simp [hD1, hD2]
        ring
    have h_case_C : σ a₂ < σ a₁ → σ a₂ < σ a₃ → σ (p.1 : K) < 0 → 0 < σ (p.2 : K) →
        IsDescentClass
          (algebraMap K w.Completion a₁) (algebraMap K w.Completion a₂) (algebraMap K w.Completion a₃)
          (algebraMap K w.Completion (p.1 : K)) (algebraMap K w.Completion (p.2 : K)) := by
      intro h21 h23 h1 h2
      refine real_descent_of_real_sol 1
        (Real.sqrt ((σ a₁ - σ a₂) / (-σ (p.1 : K)))) 0
        (Real.sqrt ((σ a₃ - σ a₂) / (-(σ (p.1 : K) * σ (p.2 : K)))))
        (Or.inl one_ne_zero) ?_ ?_
      · have hdiv : 0 ≤ (σ a₁ - σ a₂) / (-σ (p.1 : K)) :=
          div_nonneg (sub_nonneg.mpr h21.le) (neg_nonneg.mpr h1.le)
        rw [Real.sq_sqrt hdiv]
        field_simp [hD1]
        ring
      · have hdiv1 : 0 ≤ (σ a₁ - σ a₂) / (-σ (p.1 : K)) :=
          div_nonneg (sub_nonneg.mpr h21.le) (neg_nonneg.mpr h1.le)
        have hdiv2 : 0 ≤ (σ a₃ - σ a₂) / (-(σ (p.1 : K) * σ (p.2 : K))) :=
          div_nonneg (sub_nonneg.mpr h23.le) (neg_nonneg.mpr (mul_neg_of_neg_of_pos h1 h2).le)
        rw [Real.sq_sqrt hdiv1, Real.sq_sqrt hdiv2]
        field_simp [hD1, hD2]
        ring
    have h_case_D : σ a₃ < σ a₁ → σ a₃ < σ a₂ → σ (p.1 : K) < 0 → σ (p.2 : K) < 0 →
        IsDescentClass
          (algebraMap K w.Completion a₁) (algebraMap K w.Completion a₂) (algebraMap K w.Completion a₃)
          (algebraMap K w.Completion (p.1 : K)) (algebraMap K w.Completion (p.2 : K)) := by
      intro h31 h32 h1 h2
      refine real_descent_of_real_sol 1
        (Real.sqrt ((σ a₁ - σ a₃) / (-σ (p.1 : K))))
        (Real.sqrt ((σ a₂ - σ a₃) / (-σ (p.2 : K)))) 0
        (Or.inl one_ne_zero) ?_ ?_
      · have hdiv1 : 0 ≤ (σ a₁ - σ a₃) / (-σ (p.1 : K)) :=
          div_nonneg (sub_nonneg.mpr h31.le) (neg_nonneg.mpr h1.le)
        have hdiv2 : 0 ≤ (σ a₂ - σ a₃) / (-σ (p.2 : K)) :=
          div_nonneg (sub_nonneg.mpr h32.le) (neg_nonneg.mpr h2.le)
        rw [Real.sq_sqrt hdiv1, Real.sq_sqrt hdiv2]
        field_simp [hD1, hD2]
        ring
      · have hdiv1 : 0 ≤ (σ a₁ - σ a₃) / (-σ (p.1 : K)) :=
          div_nonneg (sub_nonneg.mpr h31.le) (neg_nonneg.mpr h1.le)
        rw [Real.sq_sqrt hdiv1]
        field_simp [hD1]
        ring
    dsimp [φ_bool, s_w]
    change _ ↔ (if σ a₁ < σ a₂ ∧ σ a₁ < σ a₃ then decide (σ (p.1 : K) < 0)
      else if σ a₂ < σ a₁ ∧ σ a₂ < σ a₃ then decide (σ (p.2 : K) < 0)
      else xor (decide (σ (p.1 : K) < 0)) (decide (σ (p.2 : K) < 0))) = false
    split_ifs with hmin1 hmin2
    · rw [decide_eq_false_iff_not, not_lt]
      constructor
      · intro hdesc
        rcases descent_signs hdesc with ⟨h1, _⟩ | ⟨_, _, h21, _⟩ | ⟨h1, _, _, _⟩ | ⟨_, _, h31, _⟩ <;> linarith
      · intro h1_nonneg
        have h1_pos : 0 < σ (p.1 : K) := lt_of_le_of_ne h1_nonneg hD1.symm
        rcases lt_or_gt_of_ne hD2 with h2_neg | h2_pos
        · exact h_case_B hmin1.1 hmin1.2 h1_pos h2_neg
        · exact h_case_A h1_pos h2_pos
    · rw [decide_eq_false_iff_not, not_lt]
      constructor
      · intro hdesc
        rcases descent_signs hdesc with ⟨_, h2⟩ | ⟨_, h2, _, _⟩ | ⟨_, _, h12, _⟩ | ⟨_, _, _, h32⟩ <;> linarith
      · intro h2_nonneg
        have h2_pos : 0 < σ (p.2 : K) := lt_of_le_of_ne h2_nonneg hD2.symm
        rcases lt_or_gt_of_ne hD1 with h1_neg | h1_pos
        · exact h_case_C hmin2.1 hmin2.2 h1_neg h2_pos
        · exact h_case_A h1_pos h2_pos
    · have hmin3 : σ a₃ < σ a₁ ∧ σ a₃ < σ a₂ := by
        rcases lt_or_gt_of_ne hA12 with h12 | h21 <;>
          rcases lt_or_gt_of_ne hA13 with h13 | h31 <;>
          rcases lt_or_gt_of_ne hA23 with h23 | h32
        · exfalso; exact hmin1 ⟨h12, h13⟩
        · exfalso; exact hmin1 ⟨h12, h13⟩
        · linarith
        · exact ⟨h31, h32⟩
        · exfalso; exact hmin2 ⟨h21, h23⟩
        · linarith
        · exfalso; exact hmin2 ⟨h21, h23⟩
        · exact ⟨h31, h32⟩
      rw [xor_eq_false_iff]
      constructor
      · intro hdesc
        rcases descent_signs hdesc with ⟨h1, h2⟩ | ⟨_, _, h21, h23⟩ | ⟨_, _, h12, h13⟩ | ⟨h1, h2, _, _⟩
        · have h1' : ¬ (σ (p.1 : K) < 0) := not_lt.mpr h1.le
          have h2' : ¬ (σ (p.2 : K) < 0) := not_lt.mpr h2.le
          simp [h1', h2']
        · linarith
        · linarith
        · simp [h1, h2]
      · intro h_eq
        rcases lt_or_gt_of_ne hD1 with h1_neg | h1_pos <;>
          rcases lt_or_gt_of_ne hD2 with h2_neg | h2_pos
        · exact h_case_D hmin3.1 hmin3.2 h1_neg h2_neg
        · have h2' : ¬ (σ (p.2 : K) < 0) := not_lt.mpr h2_pos.le
          simp [h1_neg, h2'] at h_eq
        · have h1' : ¬ (σ (p.1 : K) < 0) := not_lt.mpr h1_pos.le
          simp [h1', h2_neg] at h_eq
        · exact h_case_A h1_pos h2_pos
  let e_real : { w : NumberField.InfinitePlace K // w.IsReal } ≃
      Fin (NumberField.InfinitePlace.nrRealPlaces K) :=
    Fintype.equivFin { w : NumberField.InfinitePlace K // w.IsReal }
  let b2z (b : Bool) : ZMod 2 := if b then 1 else 0
  let Φ_inf : Kˣ × Kˣ → (Fin (NumberField.InfinitePlace.nrRealPlaces K) → ZMod 2) :=
    fun p i => b2z (φ_bool (e_real.symm i).1 (e_real.symm i).2 p)
  let Ψ_inf : Kˣ × Kˣ → (Fin (NumberField.InfinitePlace.nrRealPlaces K) → ZMod 2) :=
    fun q i => b2z (ψ_bool (e_real.symm i).1 (e_real.symm i).2 q)
  have b2z_xor : ∀ a b : Bool, b2z (xor a b) = b2z a + b2z b := by decide
  have b2z_eq_zero : ∀ b : Bool, b2z b = 0 ↔ b = false := by decide
  have b2z_inj : ∀ a b : Bool, b2z a = b2z b ↔ a = b := by decide
  have xor_xor_xor : ∀ a b c d : Bool, xor (xor a b) (xor c d) = xor (xor a c) (xor b d) := by decide
  have h_inj_branch1 : ∀ a₁ b₁ a₂ b₂ : Bool,
      a₁ = false → a₂ = false → b₁ = b₂ → (xor a₁ a₂ = false ∧ xor b₁ b₂ = false) := by decide
  have h_inj_branch2 : ∀ a₁ b₁ a₂ b₂ : Bool,
      b₁ = false → b₂ = false → a₁ = a₂ → (xor a₁ a₂ = false ∧ xor b₁ b₂ = false) := by decide
  have h_inj_branch3 : ∀ a₁ b₁ a₂ b₂ : Bool,
      xor a₁ b₁ = false → xor a₂ b₂ = false → a₁ = a₂ → (xor a₁ a₂ = false ∧ xor b₁ b₂ = false) := by decide
  have h_pair_branch1 : ∀ sq1 sq2 sp1 sp2 : Bool,
      sq1 = false →
      (if (sq1 && sp2) then (-1 : ℤˣ) else 1) * (if (sq2 && sp1) then (-1 : ℤˣ) else 1) =
        (-1 : ℤˣ) ^ (b2z sq2 * b2z sp1).val := by decide
  have h_pair_branch2 : ∀ sq1 sq2 sp1 sp2 : Bool,
      sq2 = false →
      (if (sq1 && sp2) then (-1 : ℤˣ) else 1) * (if (sq2 && sp1) then (-1 : ℤˣ) else 1) =
        (-1 : ℤˣ) ^ (b2z sq1 * b2z sp2).val := by decide
  have h_pair_branch3 : ∀ sq1 sq2 sp1 sp2 : Bool,
      xor sq1 sq2 = false →
      (if (sq1 && sp2) then (-1 : ℤˣ) else 1) * (if (sq2 && sp1) then (-1 : ℤˣ) else 1) =
        (-1 : ℤˣ) ^ (b2z sq1 * b2z (xor sp1 sp2)).val := by decide
  have hΦ_inf_zero_iff : ∀ p : Kˣ × Kˣ, Φ_inf p = 0 ↔
      ∀ w : { w : NumberField.InfinitePlace K // w.IsReal }, φ_bool w.1 w.2 p = false := by
    intro p
    constructor
    · intro h w
      have hi := congr_fun h (e_real w)
      simpa only [Φ_inf, Equiv.symm_apply_apply, Pi.zero_apply, b2z_eq_zero] using hi
    · intro h
      ext i
      simp only [Φ_inf, Pi.zero_apply, b2z_eq_zero]
      exact h (e_real.symm i)
  refine ⟨Φ_inf, Ψ_inf, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q hp1 hp2
    ext i
    set w := e_real.symm i
    dsimp [Φ_inf, φ_bool]
    rw [s_w_congr_of_isSquare w.1 w.2 p.1 q.1 hp1, s_w_congr_of_isSquare w.1 w.2 p.2 q.2 hp2]
  · intro p q
    ext i
    set w := e_real.symm i
    simp only [Φ_inf, Pi.add_apply, φ_bool]
    split_ifs
    · rw [s_w_mul w.1 w.2 p.1 q.1, b2z_xor]
    · rw [s_w_mul w.1 w.2 p.2 q.2, b2z_xor]
    · rw [s_w_mul w.1 w.2 p.1 q.1, s_w_mul w.1 w.2 p.2 q.2, xor_xor_xor, b2z_xor]
  · intro p
    rw [hΦ_inf_zero_iff]
    constructor
    · intro h w
      by_cases hw : w.IsReal
      · exact (h_real_descent w hw p).mpr (h ⟨w, hw⟩)
      · exact (h_complex w hw).2.1 p
    · intro h ⟨w, hw⟩
      exact (h_real_descent w hw p).mp (h w)
  · intro q₁ q₂ hq₁ hq₂ hΨ w
    by_cases hw : w.IsReal
    · have hq₁_w := (hΦ_inf_zero_iff q₁).mp hq₁ ⟨w, hw⟩
      have hq₂_w := (hΦ_inf_zero_iff q₂).mp hq₂ ⟨w, hw⟩
      have hΨ_w : ψ_bool w hw q₁ = ψ_bool w hw q₂ := by
        have hi := congr_fun hΨ (e_real ⟨w, hw⟩)
        simpa only [Ψ_inf, Equiv.symm_apply_apply, b2z_inj] using hi
      dsimp [φ_bool] at hq₁_w hq₂_w
      dsimp [ψ_bool] at hΨ_w
      have h_xor : xor (s_w w hw q₁.1) (s_w w hw q₂.1) = false ∧
          xor (s_w w hw q₁.2) (s_w w hw q₂.2) = false := by
        split_ifs at hq₁_w hq₂_w hΨ_w
        · exact h_inj_branch1 _ _ _ _ hq₁_w hq₂_w hΨ_w
        · exact h_inj_branch2 _ _ _ _ hq₁_w hq₂_w hΨ_w
        · exact h_inj_branch3 _ _ _ _ hq₁_w hq₂_w hΨ_w
      rw [s_w_isSquare w hw (q₁.1 * q₂.1), s_w_isSquare w hw (q₁.2 * q₂.2),
          s_w_mul w hw q₁.1 q₂.1, s_w_mul w hw q₁.2 q₂.2]
      exact h_xor
    · exact ⟨(h_complex w hw).1 _, (h_complex w hw).1 _⟩
  · intro q p hq
    have hq_real := (hΦ_inf_zero_iff q).mp hq
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun w : NumberField.InfinitePlace K => w.IsReal)
      (fun w => hilbInf w (q.1 : K) (p.2 : K) * hilbInf w (q.2 : K) (p.1 : K))]
    have h_comp_prod : (∏ w : { w : NumberField.InfinitePlace K // ¬ w.IsReal },
        (hilbInf w.1 (q.1 : K) (p.2 : K) * hilbInf w.1 (q.2 : K) (p.1 : K))) = 1 := by
      apply Finset.prod_eq_one
      intro w _
      exact (h_complex w.1 w.2).2.2 q p
    rw [h_comp_prod, mul_one]
    have h_real_term : ∀ w : { w : NumberField.InfinitePlace K // w.IsReal },
        hilbInf w.1 (q.1 : K) (p.2 : K) * hilbInf w.1 (q.2 : K) (p.1 : K) =
          (-1 : ℤˣ) ^ (b2z (ψ_bool w.1 w.2 q) * b2z (φ_bool w.1 w.2 p)).val := by
      intro ⟨w, hw⟩
      have hq_w := hq_real ⟨w, hw⟩
      dsimp [φ_bool] at hq_w ⊢
      dsimp [ψ_bool]
      split_ifs at hq_w ⊢ <;>
        rw [hilbInf_eq_if_s_w w hw q.1 p.2, hilbInf_eq_if_s_w w hw q.2 p.1]
      · exact h_pair_branch1 _ _ _ _ hq_w
      · exact h_pair_branch2 _ _ _ _ hq_w
      · exact h_pair_branch3 _ _ _ _ hq_w
    have h_real_prod : (∏ w : { w : NumberField.InfinitePlace K // w.IsReal },
        (hilbInf w.1 (q.1 : K) (p.2 : K) * hilbInf w.1 (q.2 : K) (p.1 : K))) =
        ∏ i : Fin (NumberField.InfinitePlace.nrRealPlaces K), (-1 : ℤˣ) ^ (Ψ_inf q i * Φ_inf p i).val := by
      calc (∏ w : { w : NumberField.InfinitePlace K // w.IsReal },
            (hilbInf w.1 (q.1 : K) (p.2 : K) * hilbInf w.1 (q.2 : K) (p.1 : K)))
          = ∏ w : { w : NumberField.InfinitePlace K // w.IsReal },
              (-1 : ℤˣ) ^ (b2z (ψ_bool w.1 w.2 q) * b2z (φ_bool w.1 w.2 p)).val := by
            refine Finset.prod_congr rfl fun w _ => h_real_term w
        _ = ∏ i : Fin (NumberField.InfinitePlace.nrRealPlaces K),
              (-1 : ℤˣ) ^ (Ψ_inf q i * Φ_inf p i).val := by
            refine Fintype.prod_equiv e_real _ _ fun w => ?_
            simp only [Ψ_inf, Φ_inf, Equiv.symm_apply_apply]
    rw [h_real_prod]
    have neg_one_pow_val_add : ∀ x y : ZMod 2,
        (-1 : ℤˣ) ^ (x + y).val = (-1 : ℤˣ) ^ x.val * (-1 : ℤˣ) ^ y.val := by
      intro x y
      fin_cases x <;> fin_cases y <;> decide
    have neg_one_pow_val_sum : ∀ {α : Type} (s : Finset α) (f : α → ZMod 2),
        (-1 : ℤˣ) ^ (∑ a ∈ s, f a).val = ∏ a ∈ s, (-1 : ℤˣ) ^ (f a).val := by
      intro α s f
      induction s using Finset.cons_induction with
      | empty => rfl
      | cons a s ha ih =>
        rw [Finset.sum_cons, Finset.prod_cons, neg_one_pow_val_add, ih]
    simp only [dotProduct]
    exact (neg_one_pow_val_sum Finset.univ (fun i => Ψ_inf q i * Φ_inf p i)).symm

theorem ramLocal_selmer_basis_at_v {K : Type u} [Field K] [NumberField K]
    (a₁ a₂ a₃ : K) (h₁₂ : a₁ ≠ a₂) (h₁₃ : a₁ ≠ a₃) (h₂₃ : a₂ ≠ a₃)
    (hint₁ : IsIntegral ℤ a₁) (hint₂ : IsIntegral ℤ a₂) (hint₃ : IsIntegral ℤ a₃)
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hT : IsGoodT a₁ a₂ a₃ T)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hvT : v ∉ T) (πv : v.adicCompletion K) (hπv : IsLocalUnif v πv) :
    ∃ (φ_v ψ_v : Kˣ × Kˣ → (Fin 2 → ZMod 2)),
      (∀ p q : Kˣ × Kˣ,
        IsSquare ((p.1 : K) * (q.1 : K)) → IsSquare ((p.2 : K) * (q.2 : K)) →
        φ_v p = φ_v q) ∧
      (∀ p q : Kˣ × Kˣ, φ_v (p.1 * q.1, p.2 * q.2) = φ_v p + φ_v q) ∧
      (∀ p : Kˣ × Kˣ, φ_v p = 0 ↔ RamLocal a₁ a₂ a₃ v πv p.1 p.2) ∧
      (∀ q₁ q₂ : Kˣ × Kˣ, φ_v q₁ = 0 → φ_v q₂ = 0 → ψ_v q₁ = ψ_v q₂ →
        IsSquare (algebraMap K (v.adicCompletion K) ((q₁.1 * q₂.1 : Kˣ) : K)) ∧
        IsSquare (algebraMap K (v.adicCompletion K) ((q₁.2 * q₂.2 : Kˣ) : K))) ∧
      (∀ q p : Kˣ × Kˣ, φ_v q = 0 →
        hilbFin v (q.1 : K) (p.2 : K) * hilbFin v (q.2 : K) (p.1 : K) =
          (-1 : ℤˣ) ^ (dotProduct (ψ_v q) (φ_v p)).val) :=
by
  classical
  let hilbBool (e ax bx ay by_ : Bool) : Bool :=
    xor (xor (ax && by_) (bx && ay)) (e && bx && by_)
  let b2z (b : Bool) : ZMod 2 := if b then 1 else 0
  let φ₀ (ε c₀₁ c₀₂ : Bool) (a₁ b₁ a₂ b₂ : Bool) : Bool :=
    xor a₁ (xor ((xor ε c₀₂) && b₁) (c₀₁ && b₂))
  let φ₁ (c₀₂ c₁₂ : Bool) (a₁ b₁ a₂ b₂ : Bool) : Bool :=
    xor a₂ (xor (c₁₂ && b₁) (c₀₂ && b₂))
  have b2z_xor : ∀ b₁ b₂ : Bool, b2z (xor b₁ b₂) = b2z b₁ + b2z b₂ := by decide
  have b2z_eq_zero_iff : ∀ b : Bool, b2z b = 0 ↔ b = false := by decide
  have b2z_inj : ∀ b₁ b₂ : Bool, b2z b₁ = b2z b₂ ↔ b₁ = b₂ := by decide
  have xor_eq_false_inj : ∀ (a₁ a₂ x : Bool),
      xor a₁ x = false → xor a₂ x = false → a₁ = a₂ := by decide
  have h_φ₀_xor : ∀ (ε c₀₁ c₀₂ a₁ b₁ a₂ b₂ a₁' b₁' a₂' b₂' : Bool),
      φ₀ ε c₀₁ c₀₂ (xor a₁ a₁') (xor b₁ b₁') (xor a₂ a₂') (xor b₂ b₂') =
        xor (φ₀ ε c₀₁ c₀₂ a₁ b₁ a₂ b₂) (φ₀ ε c₀₁ c₀₂ a₁' b₁' a₂' b₂') := by
    decide
  have h_φ₁_xor : ∀ (c₀₂ c₁₂ a₁ b₁ a₂ b₂ a₁' b₁' a₂' b₂' : Bool),
      φ₁ c₀₂ c₁₂ (xor a₁ a₁') (xor b₁ b₁') (xor a₂ a₂') (xor b₂ b₂') =
        xor (φ₁ c₀₂ c₁₂ a₁ b₁ a₂ b₂) (φ₁ c₀₂ c₁₂ a₁' b₁' a₂' b₂') := by
    decide
  have h_zero_iff : ∀ (ε c₀₁ c₀₂ c₁₂ a₁ b₁ a₂ b₂ : Bool),
      (φ₀ ε c₀₁ c₀₂ a₁ b₁ a₂ b₂ = false ∧ φ₁ c₀₂ c₁₂ a₁ b₁ a₂ b₂ = false) ↔
      (((a₁ = false ∧ b₁ = false) ∧ (a₂ = false ∧ b₂ = false)) ∨
       ((xor a₁ c₀₁ = false ∧ xor b₁ false = false) ∧
        (xor a₂ c₀₂ = false ∧ xor b₂ true = false)) ∨
       ((xor a₁ (xor ε c₀₂) = false ∧ xor b₁ true = false) ∧
        (xor a₂ c₁₂ = false ∧ xor b₂ false = false)) ∨
       ((xor a₁ (xor c₀₁ (xor ε c₀₂)) = false ∧ xor b₁ true = false) ∧
        (xor a₂ (xor c₀₂ c₁₂) = false ∧ xor b₂ true = false))) := by
    decide
  have h_pair_core : ∀ (ε c₀₁ c₀₂ c₁₂ aq1 bq1 aq2 bq2 ap1 bp1 ap2 bp2 : Bool),
      (φ₀ ε c₀₁ c₀₂ aq1 bq1 aq2 bq2 || φ₁ c₀₂ c₁₂ aq1 bq1 aq2 bq2 ||
       !(xor (xor (hilbBool ε aq1 bq1 ap2 bp2) (hilbBool ε aq2 bq2 ap1 bp1))
             (xor (bq2 && φ₀ ε c₀₁ c₀₂ ap1 bp1 ap2 bp2)
                  (bq1 && φ₁ c₀₂ c₁₂ ap1 bp1 ap2 bp2)))) = true := by
    decide
  have h_pair_bridge : ∀ (f₀ f₁ h₁ h₂ r : Bool),
      (f₀ || f₁ || !(xor (xor h₁ h₂) r)) = true →
      (f₀ = false ∧ f₁ = false) →
      xor h₁ h₂ = r := by
    decide
  have h_sign_exp : ∀ (h₁ h₂ b₁ f₀ b₂ f₁ : Bool),
      xor h₁ h₂ = xor (b₁ && f₀) (b₂ && f₁) →
      (if h₁ then (-1 : ℤˣ) else 1) * (if h₂ then (-1 : ℤˣ) else 1) =
        (-1 : ℤˣ) ^ (b2z b₁ * b2z f₀ + b2z b₂ * b2z f₁).val := by
    decide
  have val_eq_one_of_mul_eq_one : ∀ (x y : NumberField.RingOfIntegers K),
      IsDedekindDomain.HeightOneSpectrum.valuation K v
        (algebraMap (NumberField.RingOfIntegers K) K (x * y)) = 1 →
      IsDedekindDomain.HeightOneSpectrum.valuation K v
        (algebraMap (NumberField.RingOfIntegers K) K x) = 1 ∧
      IsDedekindDomain.HeightOneSpectrum.valuation K v
        (algebraMap (NumberField.RingOfIntegers K) K y) = 1 := by
    intro x y hxy
    have hx_le : IsDedekindDomain.HeightOneSpectrum.valuation K v
        (algebraMap (NumberField.RingOfIntegers K) K x) ≤ 1 :=
      IsDedekindDomain.HeightOneSpectrum.valuation_le_one v x
    have hy_le : IsDedekindDomain.HeightOneSpectrum.valuation K v
        (algebraMap (NumberField.RingOfIntegers K) K y) ≤ 1 :=
      IsDedekindDomain.HeightOneSpectrum.valuation_le_one v y
    rw [map_mul, Valuation.map_mul] at hxy
    refine ⟨le_antisymm hx_le ?_, le_antisymm hy_le ?_⟩
    · calc (1 : WithZero (Multiplicative ℤ))
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K x) *
            IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K y) := hxy.symm
        _ ≤ IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K x) * 1 := mul_le_mul_right hy_le _
        _ = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K x) := mul_one _
    · calc (1 : WithZero (Multiplicative ℤ))
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K x) *
            IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K y) := hxy.symm
        _ ≤ 1 * IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K y) := mul_le_mul_left hx_le _
        _ = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K y) := one_mul _
  let A₁ : NumberField.RingOfIntegers K := ⟨a₁, hint₁⟩
  let A₂ : NumberField.RingOfIntegers K := ⟨a₂, hint₂⟩
  let A₃ : NumberField.RingOfIntegers K := ⟨a₃, hint₃⟩
  have hv_prod : IsDedekindDomain.HeightOneSpectrum.valuation K v
      (algebraMap (NumberField.RingOfIntegers K) K
        ((((2 : NumberField.RingOfIntegers K) * 3) * (A₁ - A₂)) * (A₁ - A₃) * (A₂ - A₃))) = 1 := by
    have h := (hT v).not.mp hvT
    push_neg at h
    have heq : algebraMap (NumberField.RingOfIntegers K) K
        ((((2 : NumberField.RingOfIntegers K) * 3) * (A₁ - A₂)) * (A₁ - A₃) * (A₂ - A₃)) =
        6 * (a₁ - a₂) * (a₁ - a₃) * (a₂ - a₃) := by
      simp only [map_mul, map_sub, map_ofNat]
      change ((2 : K) * 3 * (a₁ - a₂)) * (a₁ - a₃) * (a₂ - a₃) =
        6 * (a₁ - a₂) * (a₁ - a₃) * (a₂ - a₃)
      ring
    rw [heq]
    exact h
  obtain ⟨h123, h23_val⟩ := val_eq_one_of_mul_eq_one _ _ hv_prod
  obtain ⟨h12, h13_val⟩ := val_eq_one_of_mul_eq_one _ _ h123
  obtain ⟨h6, h12_val⟩ := val_eq_one_of_mul_eq_one _ _ h12
  obtain ⟨h2_val, _⟩ := val_eq_one_of_mul_eq_one _ _ h6
  have hvc : ∀ x : K, Valued.v (algebraMap K (v.adicCompletion K) x) =
      IsDedekindDomain.HeightOneSpectrum.valuation K v x :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v
  have h2 : Valued.v (2 : v.adicCompletion K) = 1 := by
    rw [← map_ofNat (algebraMap K (v.adicCompletion K)) 2, hvc]
    simpa only [map_ofNat] using h2_val
  let α : v.adicCompletion K := algebraMap K (v.adicCompletion K) (a₁ - a₂)
  let β : v.adicCompletion K := algebraMap K (v.adicCompletion K) (a₁ - a₃)
  let γ : v.adicCompletion K := algebraMap K (v.adicCompletion K) (a₂ - a₃)
  have hα_val : Valued.v α = 1 := by
    change Valued.v (algebraMap K (v.adicCompletion K) (a₁ - a₂)) = 1
    rw [hvc]
    simpa only [map_sub] using h12_val
  have hβ_val : Valued.v β = 1 := by
    change Valued.v (algebraMap K (v.adicCompletion K) (a₁ - a₃)) = 1
    rw [hvc]
    simpa only [map_sub] using h13_val
  have hγ_val : Valued.v γ = 1 := by
    change Valued.v (algebraMap K (v.adicCompletion K) (a₂ - a₃)) = 1
    rw [hvc]
    simpa only [map_sub] using h23_val
  have hα_ne : α ≠ 0 := by
    intro h
    rw [h, Valuation.map_zero] at hα_val
    exact zero_ne_one hα_val
  have exists_ringOfIntegers_approx_of_valuation_le_one :
      ∀ (a : K), IsDedekindDomain.HeightOneSpectrum.valuation K v a ≤ 1 →
      ∃ r : NumberField.RingOfIntegers K,
        IsDedekindDomain.HeightOneSpectrum.valuation K v
          (a - algebraMap (NumberField.RingOfIntegers K) K r) < 1 := by
    intro a ha
    obtain ⟨xa, ya, hya, hxya⟩ :=
      IsFractionRing.div_surjective (A := NumberField.RingOfIntegers K) (K := K) a
    have hy0 : ya ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hya
    have hiy : algebraMap (NumberField.RingOfIntegers K) K ya ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hya
    have hstar : a * algebraMap (NumberField.RingOfIntegers K) K ya
        = algebraMap (NumberField.RingOfIntegers K) K xa := by
      rw [← hxya]
      exact div_mul_cancel₀ _ hiy
    obtain ⟨m, hym, hym1⟩ : ∃ m : ℕ, ya ∈ v.asIdeal ^ m ∧ ya ∉ v.asIdeal ^ (m + 1) := by
      have ht0 : v.intValuation ya ≠ 0 :=
        IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero v ya hy0
      have ht1 : v.intValuation ya ≤ 1 :=
        IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v ya
      obtain ⟨k, hk⟩ : ∃ k : ℤ, WithZero.exp k = v.intValuation ya := ⟨_, WithZero.exp_log ht0⟩
      have hkle : k ≤ 0 := by
        have hstep : WithZero.exp k ≤ WithZero.exp (0 : ℤ) := by
          rw [hk, WithZero.exp_zero]; exact ht1
        exact WithZero.exp_le_exp.mp hstep
      have hcast : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      have hexpm : WithZero.exp (-(((-k).toNat : ℕ) : ℤ)) = v.intValuation ya := by
        rw [hcast, neg_neg, hk]
      refine ⟨(-k).toNat, ?_, ?_⟩
      · exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya _).mp
          (le_of_eq hexpm.symm)
      · intro hcon
        have hle :=
          (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya
            ((-k).toNat + 1)).mpr hcon
        have he : (-(((-k).toNat + 1 : ℕ) : ℤ)) = k - 1 := by
          rw [Nat.cast_add, Nat.cast_one, hcast]; ring
        rw [he, ← hk] at hle
        have := WithZero.exp_le_exp.mp hle
        omega
    have hivy : v.intValuation ya ≤ WithZero.exp (-(m : ℤ)) :=
      (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya m).mpr hym
    have hxm : xa ∈ v.asIdeal ^ m := by
      refine (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v xa m).mp ?_
      have e1 : v.intValuation xa
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K xa) :=
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v xa).symm
      have e2 : v.intValuation ya
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K ya) :=
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v ya).symm
      calc v.intValuation xa
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (a * algebraMap (NumberField.RingOfIntegers K) K ya) := by
            rw [hstar]; exact e1
        _ = IsDedekindDomain.HeightOneSpectrum.valuation K v a *
              IsDedekindDomain.HeightOneSpectrum.valuation K v
                (algebraMap (NumberField.RingOfIntegers K) K ya) := Valuation.map_mul _ _ _
        _ ≤ 1 * IsDedekindDomain.HeightOneSpectrum.valuation K v
                (algebraMap (NumberField.RingOfIntegers K) K ya) := mul_le_mul_left ha _
        _ = v.intValuation ya := by rw [one_mul, ← e2]
        _ ≤ WithZero.exp (-(m : ℤ)) := hivy
    have hPprime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
    have hJdvd : (Ideal.span {ya} ⊔ v.asIdeal ^ (m + 1)) ∣ v.asIdeal ^ (m + 1) :=
      Ideal.dvd_iff_le.mpr le_sup_right
    obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow hPprime (m + 1)).mp hJdvd
    have hJ : Ideal.span {ya} ⊔ v.asIdeal ^ (m + 1) = v.asIdeal ^ i := associated_iff_eq.mp hassoc
    have hyJ : ya ∈ v.asIdeal ^ i := by
      rw [← hJ]
      exact Ideal.dvd_span_singleton.mp (Ideal.dvd_iff_le.mpr le_sup_left)
    have him : i ≤ m := by
      by_contra hcon
      have hii : i = m + 1 := by omega
      rw [hii] at hyJ
      exact hym1 hyJ
    have hxJ : xa ∈ Ideal.span {ya} ⊔ v.asIdeal ^ (m + 1) := by
      rw [hJ]
      exact Ideal.pow_le_pow_right him hxm
    obtain ⟨p, hp, w, hw, hpw⟩ := Submodule.mem_sup.mp hxJ
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hp
    refine ⟨r, ?_⟩
    have hxrw : xa = r * ya + w := by rw [← hpw, hr]
    have key : (a - algebraMap (NumberField.RingOfIntegers K) K r)
        * algebraMap (NumberField.RingOfIntegers K) K ya
        = algebraMap (NumberField.RingOfIntegers K) K w := by
      have h1 : algebraMap (NumberField.RingOfIntegers K) K xa
          = algebraMap (NumberField.RingOfIntegers K) K r
              * algebraMap (NumberField.RingOfIntegers K) K ya
            + algebraMap (NumberField.RingOfIntegers K) K w := by
        rw [hxrw, map_add, map_mul]
      rw [sub_mul, hstar, h1]; ring
    have hV : IsDedekindDomain.HeightOneSpectrum.valuation K v
          (a - algebraMap (NumberField.RingOfIntegers K) K r) * v.intValuation ya
        = v.intValuation w := by
      rw [← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v ya,
        ← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v w,
        ← Valuation.map_mul, key]
    have hwb : v.intValuation w ≤ WithZero.exp (-((m + 1 : ℕ) : ℤ)) :=
      (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v w (m + 1)).mpr hw
    have hyb : WithZero.exp (-((m + 1 : ℕ) : ℤ)) < v.intValuation ya := by
      by_contra hcon
      push_neg at hcon
      exact hym1
        ((IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya (m + 1)).mp hcon)
    by_contra hcon
    push_neg at hcon
    have hchain : v.intValuation ya ≤ v.intValuation w := by
      calc v.intValuation ya = 1 * v.intValuation ya := (one_mul _).symm
        _ ≤ IsDedekindDomain.HeightOneSpectrum.valuation K v
              (a - algebraMap (NumberField.RingOfIntegers K) K r) * v.intValuation ya :=
            mul_le_mul_left hcon _
        _ = v.intValuation w := hV
    exact absurd (lt_of_le_of_lt (le_trans hchain hwb) hyb) (lt_irrefl _)
  have h_approx : ∀ z : v.adicCompletion K, Valued.v z ≤ 1 →
      ∃ r : NumberField.RingOfIntegers K,
        Valued.v (z - algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K r)) < 1 := by
    intro z hz
    have hdense : DenseRange (fun y : K => algebraMap K (v.adicCompletion K) y) := by
      letI : Valued K (WithZero (Multiplicative ℤ)) :=
        IsDedekindDomain.HeightOneSpectrum.adicValued (K := K) v
      exact UniformSpace.Completion.denseRange_coe
    have hnhds : {y : v.adicCompletion K |
        Valued.v (y - z) < ((1 : (WithZero (Multiplicative ℤ))ˣ) :
          WithZero (Multiplicative ℤ))} ∈ nhds z :=
      Valued.mem_nhds.mpr ⟨1, subset_rfl⟩
    obtain ⟨u, hu1, k, hk⟩ := mem_closure_iff_nhds.mp (hdense z) _ hnhds
    have hkl : Valued.v (z - algebraMap K (v.adicCompletion K) k) < 1 := by
      dsimp only at hk
      rw [Valuation.map_sub_swap, hk]
      exact hu1
    have hvk : IsDedekindDomain.HeightOneSpectrum.valuation K v k ≤ 1 := by
      rw [← hvc k]
      have hsplit : algebraMap K (v.adicCompletion K) k =
          z - (z - algebraMap K (v.adicCompletion K) k) := by ring
      rw [hsplit]
      exact le_trans (Valuation.map_sub Valued.v _ _) (max_le hz (le_of_lt hkl))
    obtain ⟨r, hr⟩ := exists_ringOfIntegers_approx_of_valuation_le_one k hvk
    refine ⟨r, ?_⟩
    have hsplit2 : z - algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K r) =
        (z - algebraMap K (v.adicCompletion K) k) +
          algebraMap K (v.adicCompletion K)
            (k - algebraMap (NumberField.RingOfIntegers K) K r) := by
      rw [map_sub]; ring
    rw [hsplit2]
    refine lt_of_le_of_lt (Valuation.map_add Valued.v _ _) (max_lt hkl ?_)
    rw [hvc]
    exact hr
  have exists_sol_quadratic_mod_heightOneSpectrum :
      (2 : NumberField.RingOfIntegers K) ∉ v.asIdeal →
      ∀ (r s : NumberField.RingOfIntegers K), r ∉ v.asIdeal → s ∉ v.asIdeal →
      ∃ x₀ y₀ : NumberField.RingOfIntegers K, r * x₀ ^ 2 + s * y₀ ^ 2 - 1 ∈ v.asIdeal := by
    intro h2not r s hr hs
    letI : Field (NumberField.RingOfIntegers K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
    letI : Fintype (NumberField.RingOfIntegers K ⧸ v.asIdeal) := Fintype.ofFinite _
    have hr' : Ideal.Quotient.mk v.asIdeal r ≠ 0 := fun h =>
      hr (Ideal.Quotient.eq_zero_iff_mem.mp h)
    have hs' : Ideal.Quotient.mk v.asIdeal s ≠ 0 := fun h =>
      hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
    have h2' : (2 : NumberField.RingOfIntegers K ⧸ v.asIdeal) ≠ 0 := by
      intro h
      refine h2not (Ideal.Quotient.eq_zero_iff_mem.mp ?_)
      rw [map_ofNat]
      exact h
    have hchar : ringChar (NumberField.RingOfIntegers K ⧸ v.asIdeal) ≠ 2 := by
      intro h
      refine h2' ?_
      have h4 : ((2 : ℕ) : NumberField.RingOfIntegers K ⧸ v.asIdeal) = 0 :=
        (ringChar.spec _ 2).mpr (by rw [h])
      simpa using h4
    have hcard : Fintype.card (NumberField.RingOfIntegers K ⧸ v.asIdeal) % 2 = 1 :=
      FiniteField.odd_card_of_char_ne_two hchar
    obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
      (f := Polynomial.C (Ideal.Quotient.mk v.asIdeal r) * Polynomial.X ^ 2
        + Polynomial.C 0 * Polynomial.X + Polynomial.C 0)
      (g := Polynomial.C (Ideal.Quotient.mk v.asIdeal s) * Polynomial.X ^ 2
        + Polynomial.C 0 * Polynomial.X + Polynomial.C (-1))
      (Polynomial.degree_quadratic hr') (Polynomial.degree_quadratic hs') hcard
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, zero_mul, add_zero] at hab
    obtain ⟨x₀, hx₀⟩ := Ideal.Quotient.mk_surjective (I := v.asIdeal) a
    obtain ⟨y₀, hy₀⟩ := Ideal.Quotient.mk_surjective (I := v.asIdeal) b
    refine ⟨x₀, y₀, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
    simp only [map_sub, map_add, map_mul, map_pow, map_one]
    rw [hx₀, hy₀]
    linear_combination hab
  have h_hensel : ∀ (c x₀ : v.adicCompletion K),
      Valued.v x₀ = (1 : WithZero (Multiplicative ℤ)) →
      Valued.v (c - x₀ ^ 2) < (1 : WithZero (Multiplicative ℤ)) →
      ∃ z : v.adicCompletion K, z ^ 2 = c := by
    intro c x₀ hx₀ hc
    have hstep : ∀ y : v.adicCompletion K,
        Valued.v y = (1 : WithZero (Multiplicative ℤ)) →
        Valued.v (y ^ 2 - c) < (1 : WithZero (Multiplicative ℤ)) →
        Valued.v (y - (y ^ 2 - c) / (2 * y)) = (1 : WithZero (Multiplicative ℤ)) ∧
        Valued.v ((y - (y ^ 2 - c) / (2 * y)) ^ 2 - c) = Valued.v (y ^ 2 - c) ^ 2 ∧
        Valued.v (y - (y ^ 2 - c) / (2 * y) - y) = Valued.v (y ^ 2 - c) := by
      intro y hy hd
      have h2ne : (2 : v.adicCompletion K) ≠ 0 := by
        intro hcon; rw [hcon, map_zero] at h2; exact zero_ne_one h2
      have hyne : y ≠ 0 := by
        intro hcon; rw [hcon, map_zero] at hy; exact zero_ne_one hy
      have ht : Valued.v ((y ^ 2 - c) / (2 * y)) = Valued.v (y ^ 2 - c) := by
        rw [map_div₀, map_mul, h2, hy, one_mul, div_one]
      have hlt' : Valued.v ((y ^ 2 - c) / (2 * y)) < Valued.v y := by
        rw [ht, hy]; exact hd
      refine ⟨?_, ?_, ?_⟩
      · rw [Valuation.map_sub_eq_of_lt_left _ hlt', hy]
      · have key : (y - (y ^ 2 - c) / (2 * y)) ^ 2 - c = ((y ^ 2 - c) / (2 * y)) ^ 2 := by
          field_simp; ring
        rw [key, Valuation.map_pow, ht]
      · have key : y - (y ^ 2 - c) / (2 * y) - y = -((y ^ 2 - c) / (2 * y)) := by ring
        rw [key, Valuation.map_neg, ht]
    have hdecay : ∀ δ γ : WithZero (Multiplicative ℤ), δ < 1 → γ ≠ 0 →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → δ ^ (2 ^ n) < γ := by
      intro δ γ hδ hγ
      rcases eq_or_ne δ 0 with h0 | h0
      · refine ⟨0, fun n _ => ?_⟩
        rw [h0, zero_pow (Nat.two_pow_pos n).ne']
        exact zero_lt_iff.mpr hγ
      · obtain ⟨a, rfl⟩ : ∃ a : ℤ, δ = ((Multiplicative.ofAdd a : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
          obtain ⟨g, hg⟩ := WithZero.ne_zero_iff_exists.mp h0
          exact ⟨Multiplicative.toAdd g, hg.symm⟩
        obtain ⟨b, rfl⟩ : ∃ b : ℤ, γ = ((Multiplicative.ofAdd b : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
          obtain ⟨g, hg⟩ := WithZero.ne_zero_iff_exists.mp hγ
          exact ⟨Multiplicative.toAdd g, hg.symm⟩
        have ha : a < 0 := WithZero.coe_lt_one.mp hδ
        have hpow : ∀ k : ℕ,
            ((Multiplicative.ofAdd a : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ k
              = ((Multiplicative.ofAdd ((k : ℤ) * a) : Multiplicative ℤ) :
                  WithZero (Multiplicative ℤ)) := by
          intro k; rw [← WithZero.coe_pow]; congr 1
        refine ⟨(-b).toNat + 1, fun n hn => ?_⟩
        rw [hpow, WithZero.coe_lt_coe]
        have hbk : -b < ((2 ^ n : ℕ) : ℤ) := by
          have hx : (-b).toNat < n := by omega
          have h1 : (-b).toNat < 2 ^ n := lt_trans hx Nat.lt_two_pow_self
          have h2' : ((-b).toNat : ℤ) < ((2 ^ n : ℕ) : ℤ) := by exact_mod_cast h1
          exact lt_of_le_of_lt (Int.self_le_toNat _) h2'
        have hkpos : (0 : ℤ) ≤ ((2 ^ n : ℕ) : ℤ) := Int.natCast_nonneg _
        have ha1 : a ≤ -1 := by omega
        have hle : ((2 ^ n : ℕ) : ℤ) * a ≤ ((2 ^ n : ℕ) : ℤ) * (-1) :=
          mul_le_mul_of_nonneg_left ha1 hkpos
        have hgoal : ((2 ^ n : ℕ) : ℤ) * a < b := by linarith
        exact hgoal
    obtain ⟨ε, hεdef⟩ : ∃ ε : WithZero (Multiplicative ℤ), ε = Valued.v (x₀ ^ 2 - c) := ⟨_, rfl⟩
    have hε : ε < (1 : WithZero (Multiplicative ℤ)) := by
      rw [hεdef, Valuation.map_sub_swap]; exact hc
    obtain ⟨f, hf0, hfs⟩ : ∃ f : ℕ → v.adicCompletion K, f 0 = x₀ ∧
        ∀ n : ℕ, f (n + 1) = f n - (f n ^ 2 - c) / (2 * f n) :=
      ⟨fun n => Nat.rec (motive := fun _ => v.adicCompletion K) x₀
        (fun _ y => y - (y ^ 2 - c) / (2 * y)) n, rfl, fun _ => rfl⟩
    have hinv : ∀ n : ℕ, Valued.v (f n) = (1 : WithZero (Multiplicative ℤ)) ∧
        Valued.v (f n ^ 2 - c) = ε ^ (2 ^ n) := by
      intro n
      induction n with
      | zero =>
        refine ⟨by rw [hf0]; exact hx₀, ?_⟩
        rw [hf0, pow_zero, pow_one, hεdef]
      | succ n ih =>
        have hlt : Valued.v (f n ^ 2 - c) < (1 : WithZero (Multiplicative ℤ)) := by
          rw [ih.2]; exact pow_lt_one₀ zero_le' hε (Nat.two_pow_pos n).ne'
        obtain ⟨s1, s2, -⟩ := hstep (f n) ih.1 hlt
        refine ⟨by rw [hfs n]; exact s1, ?_⟩
        rw [hfs n, s2, ih.2, ← pow_mul, ← pow_succ]
    have hdiff : ∀ n : ℕ, Valued.v (f (n + 1) - f n) = ε ^ (2 ^ n) := by
      intro n
      have hlt : Valued.v (f n ^ 2 - c) < (1 : WithZero (Multiplicative ℤ)) := by
        rw [(hinv n).2]; exact pow_lt_one₀ zero_le' hε (Nat.two_pow_pos n).ne'
      obtain ⟨-, -, s3⟩ := hstep (f n) (hinv n).1 hlt
      rw [hfs n, s3, (hinv n).2]
    have hCauchy : Cauchy (Filter.map f Filter.atTop) := by
      refine Valued.cauchy_iff.mpr ⟨inferInstance, ?_⟩
      intro γ
      obtain ⟨N, hN⟩ := hdecay ε (γ : WithZero (Multiplicative ℤ)) hε (Units.ne_zero γ)
      have htel : ∀ m : ℕ, N ≤ m → Valued.v (f m - f N) < (γ : WithZero (Multiplicative ℤ)) := by
        intro m hm
        induction m, hm using Nat.le_induction with
        | base =>
          rw [sub_self, map_zero]; exact zero_lt_iff.mpr (Units.ne_zero γ)
        | succ m hm ih =>
          have e : f (m + 1) - f N = (f (m + 1) - f m) + (f m - f N) := by ring
          rw [e]
          refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ih)
          rw [hdiff m]; exact hN m hm
      refine ⟨f '' (Set.Ici N), Filter.image_mem_map (Filter.Ici_mem_atTop N), ?_⟩
      rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
      have e : f j - f i = (f j - f N) - (f i - f N) := by ring
      rw [e]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt (htel j hj) (htel i hi))
    obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hCauchy
    have hsq : Filter.Tendsto (fun n : ℕ => f n ^ 2 - c) Filter.atTop (nhds (z ^ 2 - c)) :=
      (hz.pow 2).sub tendsto_const_nhds
    have hzero : Filter.Tendsto (fun n : ℕ => f n ^ 2 - c) Filter.atTop
        (nhds (0 : v.adicCompletion K)) := by
      rw [Filter.tendsto_def]
      intro s hs
      obtain ⟨γ, hγs⟩ := Valued.mem_nhds_zero.mp hs
      obtain ⟨N, hN⟩ := hdecay ε (γ : WithZero (Multiplicative ℤ)) hε (Units.ne_zero γ)
      refine Filter.mem_of_superset (Filter.Ici_mem_atTop N) ?_
      intro n hn
      apply hγs
      show Valued.v (f n ^ 2 - c) < (γ : WithZero (Multiplicative ℤ))
      rw [(hinv n).2]; exact hN n hn
    exact ⟨z, eq_of_sub_eq_zero (tendsto_nhds_unique hsq hzero)⟩
  have s2 : ∀ (r s : v.adicCompletion K),
      Valued.v r = 1 → Valued.v s = 1 → hilbLoc v r s = 1 := by
    intro r s hr hs
    have hT_int : ∀ a : NumberField.RingOfIntegers K,
        Valued.v (algebraMap K (v.adicCompletion K)
            (algebraMap (NumberField.RingOfIntegers K) K a))
          = IsDedekindDomain.HeightOneSpectrum.intValuation v a := by
      intro a
      exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v
        (algebraMap (NumberField.RingOfIntegers K) K a)).trans
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v a)
    have h2not : (2 : NumberField.RingOfIntegers K) ∉ v.asIdeal := by
      refine IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mp ?_
      rw [← hT_int (2 : NumberField.RingOfIntegers K),
        map_ofNat (algebraMap (NumberField.RingOfIntegers K) K) 2,
        map_ofNat (algebraMap K (v.adicCompletion K)) 2]
      exact h2
    obtain ⟨R₀, hA1⟩ := h_approx r (le_of_eq hr)
    obtain ⟨S₀, hA2⟩ := h_approx s (le_of_eq hs)
    have hR0v : Valued.v (algebraMap K (v.adicCompletion K)
        (algebraMap (NumberField.RingOfIntegers K) K R₀)) = 1 := by
      have e : (algebraMap K (v.adicCompletion K)
            (algebraMap (NumberField.RingOfIntegers K) K R₀))
          = r - (r - algebraMap K (v.adicCompletion K)
              (algebraMap (NumberField.RingOfIntegers K) K R₀)) := by ring
      rw [e, Valuation.map_sub_eq_of_lt_left _ (by rw [hr]; exact hA1), hr]
    have hS0v : Valued.v (algebraMap K (v.adicCompletion K)
        (algebraMap (NumberField.RingOfIntegers K) K S₀)) = 1 := by
      have e : (algebraMap K (v.adicCompletion K)
            (algebraMap (NumberField.RingOfIntegers K) K S₀))
          = s - (s - algebraMap K (v.adicCompletion K)
              (algebraMap (NumberField.RingOfIntegers K) K S₀)) := by ring
      rw [e, Valuation.map_sub_eq_of_lt_left _ (by rw [hs]; exact hA2), hs]
    have hR0not : R₀ ∉ v.asIdeal := by
      refine IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mp ?_
      rw [← hT_int R₀]; exact hR0v
    have hS0not : S₀ ∉ v.asIdeal := by
      refine IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mp ?_
      rw [← hT_int S₀]; exact hS0v
    obtain ⟨A, B, hAB⟩ :=
      exists_sol_quadratic_mod_heightOneSpectrum h2not R₀ S₀ hR0not hS0not
    let ρR := algebraMap K (v.adicCompletion K) (algebraMap (NumberField.RingOfIntegers K) K R₀)
    let ρS := algebraMap K (v.adicCompletion K) (algebraMap (NumberField.RingOfIntegers K) K S₀)
    let X := algebraMap K (v.adicCompletion K) (algebraMap (NumberField.RingOfIntegers K) K A)
    let Y := algebraMap K (v.adicCompletion K) (algebraMap (NumberField.RingOfIntegers K) K B)
    have hXle : Valued.v X ≤ 1 := by
      change Valued.v (algebraMap K (v.adicCompletion K)
        (algebraMap (NumberField.RingOfIntegers K) K A)) ≤ 1
      rw [hT_int A]; exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v A
    have hYle : Valued.v Y ≤ 1 := by
      change Valued.v (algebraMap K (v.adicCompletion K)
        (algebraMap (NumberField.RingOfIntegers K) K B)) ≤ 1
      rw [hT_int B]; exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v B
    have hmod : Valued.v (ρR * X ^ 2 + ρS * Y ^ 2 - 1) < 1 := by
      have e : ρR * X ^ 2 + ρS * Y ^ 2 - 1 =
          algebraMap K (v.adicCompletion K)
            (algebraMap (NumberField.RingOfIntegers K) K (R₀ * A ^ 2 + S₀ * B ^ 2 - 1)) := by
        simp only [ρR, ρS, X, Y, map_add, map_mul, map_pow, map_sub, map_one]
      rw [e, hT_int, IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem]
      exact hAB
    have hunit : Valued.v X = 1 ∨ Valued.v Y = 1 := by
      have hcase : A ∉ v.asIdeal ∨ B ∉ v.asIdeal := by
        by_contra hcon
        push_neg at hcon
        obtain ⟨hA, hB⟩ := hcon
        have h1 : R₀ * A ^ 2 + S₀ * B ^ 2 ∈ v.asIdeal :=
          Ideal.add_mem _
            (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hA 2 (by norm_num)))
            (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hB 2 (by norm_num)))
        have hone : (1 : NumberField.RingOfIntegers K) ∈ v.asIdeal := by
          have h3 := Ideal.sub_mem _ h1 hAB
          simpa using h3
        exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)
      rcases hcase with h | h
      · refine Or.inl ?_
        change Valued.v (algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K A)) = 1
        rw [hT_int A]; exact IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr h
      · refine Or.inr ?_
        change Valued.v (algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K B)) = 1
        rw [hT_int B]; exact IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr h
    have hbeta : Valued.v (r * X ^ 2 + s * Y ^ 2 - 1) < 1 := by
      have t1 : Valued.v ((r - ρR) * X ^ 2) < 1 := by
        rw [Valuation.map_mul, Valuation.map_pow]
        calc Valued.v (r - ρR) * Valued.v X ^ 2
            ≤ Valued.v (r - ρR) * 1 := mul_le_mul_left' (pow_le_one' hXle 2) _
          _ = Valued.v (r - ρR) := mul_one _
          _ < 1 := hA1
      have t2 : Valued.v ((s - ρS) * Y ^ 2) < 1 := by
        rw [Valuation.map_mul, Valuation.map_pow]
        calc Valued.v (s - ρS) * Valued.v Y ^ 2
            ≤ Valued.v (s - ρS) * 1 := mul_le_mul_left' (pow_le_one' hYle 2) _
          _ = Valued.v (s - ρS) := mul_one _
          _ < 1 := hA2
      have t3 : Valued.v ((r - ρR) * X ^ 2 + (s - ρS) * Y ^ 2) < 1 :=
        lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt t1 t2)
      have e : r * X ^ 2 + s * Y ^ 2 - 1
          = (ρR * X ^ 2 + ρS * Y ^ 2 - 1)
            + ((r - ρR) * X ^ 2 + (s - ρS) * Y ^ 2) := by ring
      rw [e]
      exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hmod t3)
    have key : ∀ a b P Q : v.adicCompletion K, Valued.v a = 1 → Valued.v P = 1 →
        Valued.v (a * P ^ 2 + b * Q ^ 2 - 1) < 1 →
        ∃ x y : v.adicCompletion K, a * x ^ 2 + b * y ^ 2 = 1 := by
      intro a b P Q ha hP hlt
      have ha0 : a ≠ 0 := by
        intro hzero; rw [hzero, Valuation.map_zero] at ha; exact zero_ne_one ha
      have hac : a * ((1 - b * Q ^ 2) / a) = 1 - b * Q ^ 2 := mul_div_cancel₀ _ ha0
      have hid : a * ((1 - b * Q ^ 2) / a - P ^ 2)
          = -(a * P ^ 2 + b * Q ^ 2 - 1) := by
        rw [mul_sub, hac]; ring
      have hlt2 : Valued.v ((1 - b * Q ^ 2) / a - P ^ 2) < 1 := by
        have h : Valued.v (a * ((1 - b * Q ^ 2) / a - P ^ 2))
            = Valued.v (-(a * P ^ 2 + b * Q ^ 2 - 1)) := by rw [hid]
        rw [Valuation.map_mul, ha, one_mul, Valuation.map_neg] at h
        rw [h]; exact hlt
      obtain ⟨x, hx⟩ := h_hensel ((1 - b * Q ^ 2) / a) P hP hlt2
      exact ⟨x, Q, by rw [hx]; linear_combination hac⟩
    have hex : ∃ x y : v.adicCompletion K, r * x ^ 2 + s * y ^ 2 = 1 := by
      rcases hunit with hX1 | hY1
      · exact key r s X Y hr hX1 hbeta
      · have hbeta' : Valued.v (s * Y ^ 2 + r * X ^ 2 - 1) < 1 := by
          have e : s * Y ^ 2 + r * X ^ 2 - 1 = r * X ^ 2 + s * Y ^ 2 - 1 := by ring
          rw [e]; exact hbeta
        obtain ⟨x, y, hxy⟩ := key s r Y X hs hY1 hbeta'
        exact ⟨y, x, by linear_combination hxy⟩
    simp only [hilbLoc, if_pos hex]
  have s3 : ∀ (u w : v.adicCompletion K),
      Valued.v u = 1 → Valued.v w = 1 → (IsSquare (u * w) ↔ (IsSquare u ↔ IsSquare w)) := by
    intro u w hu hw
    have hu0 : u ≠ 0 := by intro h; rw [h, Valuation.map_zero] at hu; exact zero_ne_one hu
    have hw0 : w ≠ 0 := by intro h; rw [h, Valuation.map_zero] at hw; exact zero_ne_one hw
    constructor
    · rintro ⟨t, ht⟩
      constructor
      · rintro ⟨s, rfl⟩
        have hs0 : s ≠ 0 := by rintro rfl; rw [mul_zero] at hu0; exact hu0 rfl
        refine ⟨t / s, ?_⟩
        field_simp [hs0]
        linear_combination ht
      · rintro ⟨s, rfl⟩
        have hs0 : s ≠ 0 := by rintro rfl; rw [mul_zero] at hw0; exact hw0 rfl
        refine ⟨t / s, ?_⟩
        field_simp [hs0]
        linear_combination ht
    · intro hiff
      by_cases hu_sq : IsSquare u
      · exact IsSquare.mul hu_sq (hiff.mp hu_sq)
      · have hw_nsq : ¬ IsSquare w := fun hw_sq => hu_sq (hiff.mpr hw_sq)
        let ι : NumberField.RingOfIntegers K →+* v.adicCompletion K :=
          (algebraMap K (v.adicCompletion K)).comp (algebraMap (NumberField.RingOfIntegers K) K)
        have V0 : ∀ c : NumberField.RingOfIntegers K, Valued.v (ι c) = v.intValuation c := by
          intro c
          exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v
            (algebraMap (NumberField.RingOfIntegers K) K c)).trans
            (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v c)
        have Vlt : ∀ c : NumberField.RingOfIntegers K, Valued.v (ι c) < 1 ↔ c ∈ v.asIdeal := by
          intro c; rw [V0 c]
          exact IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem v c
        have Vle : ∀ c : NumberField.RingOfIntegers K, Valued.v (ι c) ≤ 1 := by
          intro c; rw [V0 c]
          exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v c
        have HB : ∀ m : v.adicCompletion K, Valued.v m = 1 →
            ∀ a s : NumberField.RingOfIntegers K, Valued.v (m - ι a) < 1 →
            s ^ 2 - a ∈ v.asIdeal → IsSquare m := by
          intro m hm a s hma hs
          have hanm : a ∉ v.asIdeal := by
            intro hmem
            have h1 : Valued.v (ι a) < 1 := (Vlt a).mpr hmem
            have e : m = (m - ι a) + ι a := by ring
            have h3 : Valued.v m < 1 := by
              rw [e]; exact lt_of_le_of_lt (Valuation.map_add Valued.v _ _) (max_lt hma h1)
            rw [hm] at h3; exact lt_irrefl _ h3
          have hsnm : s ∉ v.asIdeal := by
            intro hmem
            apply hanm
            have e : a = s ^ 2 - (s ^ 2 - a) := by ring
            rw [e]
            exact Ideal.sub_mem _ (Ideal.pow_mem_of_mem _ hmem 2 (by norm_num)) hs
          have hs1 : Valued.v (ι s) = 1 := by
            rcases lt_or_eq_of_le (Vle s) with h | h
            · exact absurd ((Vlt s).mp h) hsnm
            · exact h
          have hd : Valued.v (m - (ι s) ^ 2) < 1 := by
            have e : m - (ι s) ^ 2 = (m - ι a) - ι (s ^ 2 - a) := by
              rw [map_sub, map_pow]; ring
            have h1 : Valued.v (ι (s ^ 2 - a)) < 1 := (Vlt _).mpr hs
            rw [e]
            exact lt_of_le_of_lt (Valuation.map_sub Valued.v _ _) (max_lt hma h1)
          obtain ⟨x, hx⟩ := h_hensel m (ι s) hs1 hd
          exact ⟨x, by rw [← sq]; exact hx.symm⟩
        have core : ∀ (F : Type u) [Field F] [Finite F] (x y : F),
            ¬ IsSquare x → ¬ IsSquare y → IsSquare (x * y) := by
          intro F _ _ x y hx hy
          letI : Fintype F := Fintype.ofFinite F
          letI : DecidableEq F := Classical.decEq F
          by_contra hxy
          have e1 : quadraticChar F x = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hx
          have e2 : quadraticChar F y = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hy
          have e3 : quadraticChar F (x * y) = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hxy
          rw [map_mul, e1, e2] at e3
          norm_num at e3
        obtain ⟨a, haU⟩ := h_approx u (le_of_eq hu)
        obtain ⟨b, hbW⟩ := h_approx w (le_of_eq hw)
        have hib : Valued.v (ι b) = 1 := by
          rcases lt_or_eq_of_le (Vle b) with h | h
          · exfalso
            have e : w = ι b + (w - ι b) := by ring
            have h3 : Valued.v w < 1 := by
              rw [e]; exact lt_of_le_of_lt (Valuation.map_add Valued.v _ _) (max_lt h hbW)
            rw [hw] at h3; exact lt_irrefl _ h3
          · exact h
        letI : Field (NumberField.RingOfIntegers K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
        have hnsq_a : ¬ IsSquare (Ideal.Quotient.mk v.asIdeal a) := by
          rintro ⟨y, hy⟩
          obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
          refine hu_sq (HB u hu a s haU ?_)
          rw [← Ideal.Quotient.eq_zero_iff_mem]
          have hy' : Ideal.Quotient.mk v.asIdeal a =
              Ideal.Quotient.mk v.asIdeal s * Ideal.Quotient.mk v.asIdeal s := hy
          rw [map_sub, map_pow, hy']; ring
        have hnsq_b : ¬ IsSquare (Ideal.Quotient.mk v.asIdeal b) := by
          rintro ⟨y, hy⟩
          obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
          refine hw_nsq (HB w hw b s hbW ?_)
          rw [← Ideal.Quotient.eq_zero_iff_mem]
          have hy' : Ideal.Quotient.mk v.asIdeal b =
              Ideal.Quotient.mk v.asIdeal s * Ideal.Quotient.mk v.asIdeal s := hy
          rw [map_sub, map_pow, hy']; ring
        obtain ⟨y, hy⟩ := core (NumberField.RingOfIntegers K ⧸ v.asIdeal)
          (Ideal.Quotient.mk v.asIdeal a) (Ideal.Quotient.mk v.asIdeal b) hnsq_a hnsq_b
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
        have hsab : s ^ 2 - a * b ∈ v.asIdeal := by
          rw [← Ideal.Quotient.eq_zero_iff_mem]
          have hy' : Ideal.Quotient.mk v.asIdeal a * Ideal.Quotient.mk v.asIdeal b =
              Ideal.Quotient.mk v.asIdeal s * Ideal.Quotient.mk v.asIdeal s := hy
          rw [map_sub, map_pow, map_mul, hy']; ring
        have hmw : Valued.v (u * w) = 1 := by rw [Valuation.map_mul, hu, hw, one_mul]
        have hmab : Valued.v (u * w - ι (a * b)) < 1 := by
          have e : u * w - ι a * ι b = u * (w - ι b) + ι b * (u - ι a) := by ring
          have h1 : Valued.v (u * (w - ι b)) < 1 := by rw [Valuation.map_mul, hu, one_mul]; exact hbW
          have h3 : Valued.v (ι b * (u - ι a)) < 1 := by rw [Valuation.map_mul, hib, one_mul]; exact haU
          rw [map_mul ι a b, e]
          exact lt_of_le_of_lt (Valuation.map_add Valued.v _ _) (max_lt h1 h3)
        exact HB (u * w) hmw (a * b) s hmab hsab
  have s5 : ∃ ϖ : v.adicCompletion K,
      Valued.v ϖ = WithZero.exp (-1 : ℤ) ∧
      ∀ x : v.adicCompletion K, x ≠ 0 →
        ∃ z u : v.adicCompletion K, z ≠ 0 ∧ Valued.v u = 1 ∧
          (x = z ^ 2 * u ∨ x = z ^ 2 * (ϖ * u)) := by
    obtain ⟨π₀, hπ₀⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer K v
    let ϖ : v.adicCompletion K := algebraMap K (v.adicCompletion K) π₀
    have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) :=
      (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π₀).trans hπ₀
    have hϖ0 : ϖ ≠ 0 := by
      intro h; rw [h, Valuation.map_zero] at hϖ; exact WithZero.coe_ne_zero hϖ.symm
    refine ⟨ϖ, hϖ, ?_⟩
    intro x hx
    have hvx : Valued.v x ≠ 0 := fun h => hx ((Valuation.zero_iff _).mp h)
    obtain ⟨k, hexp⟩ : ∃ k : ℤ, WithZero.exp k = Valued.v x :=
      ⟨(Valued.v x).log, WithZero.exp_log hvx⟩
    have hvpow : Valued.v (ϖ ^ (-k)) = Valued.v x := by
      have h2' : ((-k : ℤ)) • (-1 : ℤ) = k := by simp
      calc Valued.v (ϖ ^ (-k)) = Valued.v ϖ ^ (-k) := map_zpow₀ _ _ _
        _ = WithZero.exp (-1 : ℤ) ^ (-k) := by rw [hϖ]
        _ = WithZero.exp ((-k : ℤ) • (-1 : ℤ)) := (WithZero.exp_zsmul _ _).symm
        _ = WithZero.exp k := by rw [h2']
        _ = Valued.v x := hexp
    let u : v.adicCompletion K := x / ϖ ^ (-k)
    have hu : Valued.v u = 1 := by
      change Valued.v (x / ϖ ^ (-k)) = 1
      rw [Valuation.map_div, hvpow, div_self hvx]
    have hx_eq : x = ϖ ^ (-k) * u := (mul_div_cancel₀ x (zpow_ne_zero _ hϖ0)).symm
    rcases Int.even_or_odd (-k) with ⟨r, hr⟩ | ⟨r, hr⟩
    · refine ⟨ϖ ^ r, u, zpow_ne_zero r hϖ0, hu, Or.inl ?_⟩
      rw [hx_eq, hr, zpow_add₀ hϖ0, ← sq]
    · refine ⟨ϖ ^ r, u, zpow_ne_zero r hϖ0, hu, Or.inr ?_⟩
      have hrr : 2 * r + 1 = (r + r) + 1 := by ring
      rw [hx_eq, hr, hrr, zpow_add₀ hϖ0, zpow_add₀ hϖ0, zpow_one, ← sq, mul_assoc]
  obtain ⟨ϖ, hϖ, hdecomp⟩ := s5
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, Valuation.map_zero] at hϖ; exact WithZero.coe_ne_zero hϖ.symm
  have h_unif_pa : ∃ z u : v.adicCompletion K,
      z ≠ 0 ∧ Valued.v u = 1 ∧ πv * α = z ^ 2 * (ϖ * u) := by
    rcases hπv with ⟨n, ⟨r, hr⟩, hn⟩
    have hvpa : Valued.v (πv * α) = WithZero.exp n := by
      rw [Valuation.map_mul, hn, hα_val, mul_one]
      rfl
    have hvpa_ne : Valued.v (πv * α) ≠ 0 := by
      rw [hvpa]
      exact WithZero.coe_ne_zero
    have hvpow : Valued.v (ϖ ^ (-n)) = Valued.v (πv * α) := by
      have h2' : ((-n : ℤ)) • (-1 : ℤ) = n := by simp
      calc Valued.v (ϖ ^ (-n)) = Valued.v ϖ ^ (-n) := map_zpow₀ _ _ _
        _ = WithZero.exp (-1 : ℤ) ^ (-n) := by rw [hϖ]
        _ = WithZero.exp ((-n : ℤ) • (-1 : ℤ)) := (WithZero.exp_zsmul _ _).symm
        _ = WithZero.exp n := by rw [h2']
        _ = Valued.v (πv * α) := hvpa.symm
    let u : v.adicCompletion K := (πv * α) / ϖ ^ (-n)
    have hu : Valued.v u = 1 := by
      change Valued.v ((πv * α) / ϖ ^ (-n)) = 1
      rw [Valuation.map_div, hvpow, div_self hvpa_ne]
    have hpa_eq : πv * α = ϖ ^ (-n) * u := (mul_div_cancel₀ (πv * α) (zpow_ne_zero _ hϖ0)).symm
    have hm_eq : -n = ((-r - 1) + (-r - 1)) + 1 := by omega
    refine ⟨ϖ ^ (-r - 1), u, zpow_ne_zero (-r - 1) hϖ0, hu, ?_⟩
    rw [hpa_eq, hm_eq, zpow_add₀ hϖ0, zpow_add₀ hϖ0, zpow_one, ← sq, mul_assoc]
  have s4 : ∀ (u w : v.adicCompletion K),
      Valued.v u = 1 → Valued.v w = 1 →
      ¬ IsSquare (ϖ * u) ∧
      (hilbLoc v u (ϖ * w) = 1 ↔ IsSquare u) ∧
      (hilbLoc v (ϖ * u) (ϖ * w) = 1 ↔ IsSquare (-(u * w))) := by
    intro u w hu hw
    have hilb_solvable_iff_norm_form : ∀ (a b : v.adicCompletion K),
        (2 : v.adicCompletion K) ≠ 0 → a ≠ 0 →
        ((∃ x y : v.adicCompletion K, a * x ^ 2 + b * y ^ 2 = 1) ↔
          (∃ z t : v.adicCompletion K, z ^ 2 - b * t ^ 2 = a)) := by
      intro a b h2ne ha
      constructor
      · rintro ⟨x, y, h⟩
        by_cases hx : x = 0
        · subst hx
          have hb : b * y ^ 2 = 1 := by linear_combination h
          have h2i : 2 * (2 : v.adicCompletion K)⁻¹ = 1 := mul_inv_cancel₀ h2ne
          refine ⟨(a + 1) * (2 : v.adicCompletion K)⁻¹,
            (1 - a) * y * (2 : v.adicCompletion K)⁻¹, ?_⟩
          linear_combination (-(1 - a) ^ 2 * ((2 : v.adicCompletion K)⁻¹) ^ 2) * hb +
            (a * (2 * (2 : v.adicCompletion K)⁻¹ + 1)) * h2i
        · have hu' : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
          refine ⟨x⁻¹, y * x⁻¹, ?_⟩
          linear_combination (-(x⁻¹) ^ 2) * h + (a * (x * x⁻¹ + 1)) * hu'
      · rintro ⟨z, t, h⟩
        by_cases hz : z = 0
        · subst hz
          have hbt : b * t ^ 2 = -a := by linear_combination -h
          have h2a : 2 * a * (2 * a)⁻¹ = 1 := mul_inv_cancel₀ (mul_ne_zero h2ne ha)
          refine ⟨(1 + a) * (2 * a)⁻¹, t * (a - 1) * (2 * a)⁻¹, ?_⟩
          linear_combination ((a - 1) ^ 2 * ((2 * a)⁻¹) ^ 2) * hbt +
            (2 * a * (2 * a)⁻¹ + 1) * h2a
        · have hw' : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
          refine ⟨z⁻¹, t * z⁻¹, ?_⟩
          linear_combination (-(z⁻¹) ^ 2) * h + (z * z⁻¹ + 1) * hw'
    have h_parity : ∀ (m y z : v.adicCompletion K),
        Valued.v m = WithZero.exp (-1 : ℤ) → z ≠ 0 →
        Valued.v (m * y ^ 2) ≠ Valued.v z ^ 2 := by
      intro m y z hm hz heq
      have hvz : Valued.v z ≠ 0 := fun h => hz ((Valuation.zero_iff _).mp h)
      have hvy : Valued.v y ≠ 0 := by
        intro h
        rw [Valuation.map_mul, Valuation.map_pow, h, zero_pow (by norm_num), mul_zero] at heq
        exact pow_ne_zero 2 hvz heq.symm
      obtain ⟨a, ha⟩ : ∃ a : ℤ, WithZero.exp a = Valued.v y :=
        ⟨(Valued.v y).log, WithZero.exp_log hvy⟩
      obtain ⟨b, hb⟩ : ∃ b : ℤ, WithZero.exp b = Valued.v z :=
        ⟨(Valued.v z).log, WithZero.exp_log hvz⟩
      rw [Valuation.map_mul, Valuation.map_pow, hm, ← ha, ← hb, sq, sq,
        ← WithZero.exp_add, ← WithZero.exp_add, ← WithZero.exp_add, WithZero.exp_inj] at heq
      omega
    have h_unit_unif : ∀ (u' w' : v.adicCompletion K),
        Valued.v u' = 1 → Valued.v w' = 1 →
        (hilbLoc v u' (ϖ * w') = 1 ↔ IsSquare u') := by
      intro u' w' hu' hw'
      constructor
      · intro hhilb
        have hsol : ∃ x y : v.adicCompletion K, u' * x ^ 2 + (ϖ * w') * y ^ 2 = 1 := by
          simp only [hilbLoc] at hhilb
          split_ifs at hhilb with h
          · exact h
          · exfalso; revert hhilb; decide
        rcases hsol with ⟨x, y, hxy⟩
        have hm : Valued.v (ϖ * w') = WithZero.exp (-1 : ℤ) := by
          rw [Valuation.map_mul, hϖ, hw', mul_one]
        have hmy : (ϖ * w') * y ^ 2 = 1 - u' * x ^ 2 := by linear_combination hxy
        have hvx : Valued.v x = 1 := by
          rcases lt_trichotomy (Valued.v x) 1 with hlt | heq | hgt
          · exfalso
            refine h_parity (ϖ * w') y 1 hm one_ne_zero ?_
            have hux : Valued.v (u' * x ^ 2) < Valued.v (1 : v.adicCompletion K) := by
              rw [Valuation.map_mul, hu', one_mul, Valuation.map_pow, Valuation.map_one]
              exact pow_lt_one₀ zero_le' hlt (by norm_num)
            rw [hmy, Valuation.map_sub_eq_of_lt_left _ hux, Valuation.map_one, one_pow]
          · exact heq
          · exfalso
            have hx0 : x ≠ 0 := by
              rintro rfl; rw [Valuation.map_zero] at hgt; exact not_lt_of_ge zero_le' hgt
            refine h_parity (ϖ * w') y x hm hx0 ?_
            have hux : Valued.v (1 : v.adicCompletion K) < Valued.v (u' * x ^ 2) := by
              rw [Valuation.map_mul, hu', one_mul, Valuation.map_pow, Valuation.map_one]
              exact one_lt_pow₀ hgt (by norm_num)
            rw [hmy, Valuation.map_sub_eq_of_lt_right _ hux, Valuation.map_mul, hu', one_mul,
              Valuation.map_pow]
        have hx0 : x ≠ 0 := by
          rintro rfl; rw [Valuation.map_zero] at hvx; exact zero_ne_one hvx
        have hmy_le : Valued.v ((ϖ * w') * y ^ 2) ≤ 1 := by
          rw [hmy]
          refine le_trans (Valuation.map_sub _ _ _) (max_le (by rw [Valuation.map_one]) ?_)
          rw [Valuation.map_mul, hu', Valuation.map_pow, hvx, one_pow, mul_one]
        have hmy_ne : Valued.v ((ϖ * w') * y ^ 2) ≠ 1 := by
          intro h1
          refine h_parity (ϖ * w') y 1 hm one_ne_zero ?_
          rw [h1, Valuation.map_one, one_pow]
        have hmy_lt : Valued.v ((ϖ * w') * y ^ 2) < 1 := lt_of_le_of_ne hmy_le hmy_ne
        have hxinv : Valued.v (x⁻¹) = 1 := by rw [map_inv₀, hvx, inv_one]
        have hdiff : u' - (x⁻¹) ^ 2 = -(((ϖ * w') * y ^ 2) / x ^ 2) := by
          field_simp [hx0]; linear_combination hxy
        have hdiff_lt : Valued.v (u' - (x⁻¹) ^ 2) < 1 := by
          rw [hdiff, Valuation.map_neg, Valuation.map_div, Valuation.map_pow, hvx, one_pow, div_one]
          exact hmy_lt
        obtain ⟨t, ht⟩ := h_hensel u' (x⁻¹) hxinv hdiff_lt
        exact ⟨t, by rw [← sq]; exact ht.symm⟩
      · rintro ⟨s, rfl⟩
        have hs0 : s ≠ 0 := by
          rintro rfl; rw [mul_zero, Valuation.map_zero] at hu'; exact zero_ne_one hu'
        simp only [hilbLoc]
        rw [if_pos ⟨s⁻¹, 0, by field_simp [hs0]; ring⟩]
    refine ⟨?_, h_unit_unif u w hu hw, ?_⟩
    · rintro ⟨z, hz⟩
      have hvu : Valued.v (ϖ * u) = WithZero.exp (-1 : ℤ) := by
        rw [Valuation.map_mul, hϖ, hu, mul_one]
      have hz0 : z ≠ 0 := by
        rintro rfl; rw [mul_zero] at hz; rw [hz, Valuation.map_zero] at hvu
        exact WithZero.coe_ne_zero hvu.symm
      refine h_parity (ϖ * u) 1 z hvu hz0 ?_
      rw [one_pow, mul_one, hz, Valuation.map_mul, sq]
    · have h2ne : (2 : v.adicCompletion K) ≠ 0 := by
        intro h0; rw [h0, Valuation.map_zero] at h2; exact zero_ne_one h2
      have hu0 : u ≠ 0 := by
        intro h0; rw [h0, Valuation.map_zero] at hu; exact zero_ne_one hu
      have hϖu0 : ϖ * u ≠ 0 := mul_ne_zero hϖ0 hu0
      have hequiv : (∃ x y : v.adicCompletion K, (ϖ * u) * x ^ 2 + (ϖ * w) * y ^ 2 = 1) ↔
          (∃ X Y : v.adicCompletion K, -(u * w) * X ^ 2 + (ϖ * u) * Y ^ 2 = 1) := by
        rw [hilb_solvable_iff_norm_form (ϖ * u) (ϖ * w) h2ne hϖu0]
        constructor
        · rintro ⟨z, t, hzt⟩
          refine ⟨t / u, z / (ϖ * u), ?_⟩
          field_simp [hu0, hϖ0]
          linear_combination hzt
        · rintro ⟨X, Y, hXY⟩
          refine ⟨(ϖ * u) * Y, u * X, ?_⟩
          linear_combination (ϖ * u) * hXY
      have hhilb_eq : hilbLoc v (ϖ * u) (ϖ * w) = hilbLoc v (-(u * w)) (ϖ * u) := by
        simp only [hilbLoc]
        congr 1
        exact propext hequiv
      rw [hhilb_eq]
      have hvuw : Valued.v (-(u * w)) = 1 := by
        rw [Valuation.map_neg, Valuation.map_mul, hu, hw, one_mul]
      exact h_unit_unif (-(u * w)) u hvuw hu
  let HasRep (x : v.adicCompletion K) (a b : Bool) : Prop :=
    ∃ z u : v.adicCompletion K, z ≠ 0 ∧ Valued.v u = 1 ∧
      (IsSquare u ↔ a = false) ∧
      x = z ^ 2 * (if b then ϖ * u else u)
  have exists_hasRep : ∀ x : v.adicCompletion K, x ≠ 0 → ∃ a b : Bool, HasRep x a b := by
    intro x hx
    obtain ⟨z, u, hz, hu, hxu | hxu⟩ := hdecomp x hx
    · exact ⟨!decide (IsSquare u), false, z, u, hz, hu, by simp, hxu⟩
    · exact ⟨!decide (IsSquare u), true, z, u, hz, hu, by simp, hxu⟩
  have hasRep_isSquare_iff : ∀ (x : v.adicCompletion K) (a b : Bool),
      HasRep x a b → (IsSquare x ↔ (a = false ∧ b = false)) := by
    rintro x a b ⟨z, u, hz, hu, hua, rfl⟩
    have hsq_scale : ∀ w : v.adicCompletion K, IsSquare (z ^ 2 * w) ↔ IsSquare w := by
      intro w; constructor
      · rintro ⟨s, hs⟩; refine ⟨s / z, ?_⟩; field_simp [hz]; linear_combination hs
      · rintro ⟨s, rfl⟩; refine ⟨z * s, ?_⟩; ring
    rw [hsq_scale]
    cases b
    · simp [hua]
    · simp [(s4 u u hu hu).1]
  have hasRep_mul : ∀ (x y : v.adicCompletion K) (ax bx ay by_ : Bool),
      HasRep x ax bx → HasRep y ay by_ → HasRep (x * y) (xor ax ay) (xor bx by_) := by
    rintro x y ax bx ay by_ ⟨zx, ux, hzx, hux, huax, rfl⟩ ⟨zy, uy, hzy, huy, huay, rfl⟩
    refine ⟨if bx && by_ then zx * zy * ϖ else zx * zy, ux * uy, ?_, ?_, ?_, ?_⟩
    · split_ifs
      · exact mul_ne_zero (mul_ne_zero hzx hzy) hϖ0
      · exact mul_ne_zero hzx hzy
    · rw [Valuation.map_mul, hux, huy, one_mul]
    · rw [s3 ux uy hux huy, huax, huay]
      cases ax <;> cases ay <;> decide
    · cases bx <;> cases by_ <;> simp <;> ring
  have hasRep_unique : ∀ (x : v.adicCompletion K) (a₁ b₁ a₂ b₂ : Bool),
      HasRep x a₁ b₁ → HasRep x a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂ := by
    intro x a₁ b₁ a₂ b₂ h1 h2
    have hmul := hasRep_mul x x a₁ b₁ a₂ b₂ h1 h2
    have hsq : IsSquare (x * x) := ⟨x, rfl⟩
    have hab := (hasRep_isSquare_iff (x * x) (xor a₁ a₂) (xor b₁ b₂) hmul).mp hsq
    cases a₁ <;> cases b₁ <;> cases a₂ <;> cases b₂ <;> revert hab <;> decide
  have hasRep_of_val_eq_one : ∀ x : v.adicCompletion K, Valued.v x = 1 →
      HasRep x (!decide (IsSquare x)) false := by
    intro x hx
    exact ⟨1, x, one_ne_zero, hx, by simp, by simp⟩
  have hasRep_sq_mul : ∀ (s x : v.adicCompletion K) (a b : Bool),
      s ≠ 0 → HasRep x a b → HasRep (s ^ 2 * x) a b := by
    rintro s x a b hs ⟨z, u, hz, hu, hua, rfl⟩
    exact ⟨s * z, u, mul_ne_zero hs hz, hu, hua, by ring⟩
  let ε : Bool := !decide (IsSquare (-1 : v.adicCompletion K))
  have hε : IsSquare (-1 : v.adicCompletion K) ↔ ε = false := by simp [ε]
  have hilbLoc_symm : ∀ (p q : v.adicCompletion K), hilbLoc v p q = hilbLoc v q p := by
    intro p q
    simp only [hilbLoc]
    congr 1
    exact propext ⟨fun ⟨x, y, hxy⟩ => ⟨y, x, by linear_combination hxy⟩,
      fun ⟨x, y, hxy⟩ => ⟨y, x, by linear_combination hxy⟩⟩
  have hilbLoc_scale_left : ∀ (z p q : v.adicCompletion K), z ≠ 0 →
      hilbLoc v (z ^ 2 * p) q = hilbLoc v p q := by
    intro z p q hz
    simp only [hilbLoc]
    congr 1
    refine propext ⟨?_, ?_⟩
    · rintro ⟨x, y, hxy⟩
      refine ⟨z * x, y, ?_⟩
      linear_combination hxy
    · rintro ⟨x, y, hxy⟩
      refine ⟨x / z, y, ?_⟩
      field_simp [hz]
      linear_combination hxy
  have hilbLoc_eq_iff : ∀ (p q : v.adicCompletion K) (b : Bool),
      (hilbLoc v p q = 1 ↔ b = false) →
      hilbLoc v p q = (if b then (-1 : ℤˣ) else 1) := by
    intro p q b hb
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact hb.mpr rfl
    · simp only [↓reduceIte]
      have hne : hilbLoc v p q ≠ 1 := fun h => Bool.noConfusion (hb.mp h)
      simp only [hilbLoc] at hne ⊢
      split_ifs with h
      · exfalso; exact hne (if_pos h)
      · rfl
  have hasRep_hilbLoc : ∀ (x y : v.adicCompletion K) (ax bx ay by_ : Bool),
      HasRep x ax bx → HasRep y ay by_ →
      hilbLoc v x y = (if hilbBool ε ax bx ay by_ then (-1 : ℤˣ) else 1) := by
    rintro x y ax bx ay by_ ⟨zx, ux, hzx, hux, huax, rfl⟩ ⟨zy, uy, hzy, huy, huay, rfl⟩
    rw [hilbLoc_scale_left zx _ _ hzx, hilbLoc_symm, hilbLoc_scale_left zy _ _ hzy, hilbLoc_symm]
    apply hilbLoc_eq_iff
    cases bx <;> cases by_
    · simp only [Bool.false_eq_true, ↓reduceIte, hilbBool]
      rw [s2 ux uy hux huy]
      simp
    · simp only [Bool.false_eq_true, ↓reduceIte, hilbBool]
      rw [(s4 ux uy hux huy).2.1, huax]
      cases ax <;> simp
    · simp only [Bool.false_eq_true, ↓reduceIte, hilbBool]
      rw [hilbLoc_symm, (s4 uy ux huy hux).2.1, huay]
      cases ay <;> simp
    · simp only [↓reduceIte, hilbBool]
      rw [(s4 ux uy hux huy).2.2]
      have hneg : -(ux * uy) = (-1 : v.adicCompletion K) * (ux * uy) := by ring
      have hv1 : Valued.v (-1 : v.adicCompletion K) = 1 := by
        rw [Valuation.map_neg, Valuation.map_one]
      have hvuw : Valued.v (ux * uy) = 1 := by rw [Valuation.map_mul, hux, huy, one_mul]
      rw [hneg, s3 (-1) (ux * uy) hv1 hvuw, s3 ux uy hux huy, hε, huax, huay]
      cases ε <;> cases ax <;> cases ay <;> simp
  have hv_neg_one : Valued.v (-1 : v.adicCompletion K) = 1 := by
    rw [Valuation.map_neg, Valuation.map_one]
  have hrep_neg_one : HasRep (-1 : v.adicCompletion K) ε false :=
    hasRep_of_val_eq_one (-1) hv_neg_one
  let c₀₁ : Bool := !decide (IsSquare (α * β))
  have hv_ab : Valued.v (α * β) = 1 := by
    rw [Valuation.map_mul, hα_val, hβ_val, one_mul]
  have hrep_ab : HasRep (α * β) c₀₁ false :=
    hasRep_of_val_eq_one (α * β) hv_ab
  let c₁₂ : Bool := !decide (IsSquare (-(α * γ)))
  have hv_nag : Valued.v (-(α * γ)) = 1 := by
    rw [Valuation.map_neg, Valuation.map_mul, hα_val, hγ_val, one_mul]
  have hrep_nag : HasRep (-(α * γ)) c₁₂ false :=
    hasRep_of_val_eq_one (-(α * γ)) hv_nag
  obtain ⟨z_pa, u_pa, hz_pa, hu_pa, hpa_eq⟩ := h_unif_pa
  let c₀₂ : Bool := !decide (IsSquare u_pa)
  have hrep_pa : HasRep (πv * α) c₀₂ true :=
    ⟨z_pa, u_pa, hz_pa, hu_pa, by simp [c₀₂], by simpa using hpa_eq⟩
  have hrep_npa : HasRep (-(πv * α)) (xor ε c₀₂) true := by
    have heq : -(πv * α) = (-1 : v.adicCompletion K) * (πv * α) := by ring
    rw [heq]
    exact hasRep_mul (-1) (πv * α) ε false c₀₂ true hrep_neg_one hrep_pa
  have hrep_npb : HasRep (-(πv * β)) (xor c₀₁ (xor ε c₀₂)) true := by
    have heq : -(πv * β) = (α⁻¹) ^ 2 * ((α * β) * (-(πv * α))) := by
      field_simp [hα_ne]
    rw [heq]
    exact hasRep_sq_mul (α⁻¹) _ _ _ (inv_ne_zero hα_ne)
      (hasRep_mul (α * β) (-(πv * α)) c₀₁ false (xor ε c₀₂) true hrep_ab hrep_npa)
  have hrep_npg : HasRep (-(πv * γ)) (xor c₀₂ c₁₂) true := by
    have heq : -(πv * γ) = (α⁻¹) ^ 2 * ((πv * α) * (-(α * γ))) := by
      field_simp [hα_ne]
    rw [heq]
    exact hasRep_sq_mul (α⁻¹) _ _ _ (inv_ne_zero hα_ne)
      (hasRep_mul (πv * α) (-(α * γ)) c₀₂ true c₁₂ false hrep_pa hrep_nag)
  let ι (u : Kˣ) : v.adicCompletion K := algebraMap K (v.adicCompletion K) (u : K)
  have unit_map_ne_zero : ∀ u : Kˣ, ι u ≠ 0 := by
    intro u
    change algebraMap K (v.adicCompletion K) (u : K) ≠ 0
    rw [ne_eq, map_eq_zero]
    exact u.ne_zero
  choose a_v b_v h_rep_v using fun (u : Kˣ) => exists_hasRep (ι u) (unit_map_ne_zero u)
  have h_ab_mul : ∀ u w : Kˣ,
      a_v (u * w) = xor (a_v u) (a_v w) ∧ b_v (u * w) = xor (b_v u) (b_v w) := by
    intro u w
    have h1 : HasRep (ι (u * w)) (a_v (u * w)) (b_v (u * w)) := h_rep_v (u * w)
    have h2 : HasRep (ι u * ι w) (xor (a_v u) (a_v w)) (xor (b_v u) (b_v w)) :=
      hasRep_mul (ι u) (ι w) (a_v u) (b_v u) (a_v w) (b_v w) (h_rep_v u) (h_rep_v w)
    have heq : ι (u * w) = ι u * ι w := by
      change algebraMap K (v.adicCompletion K) ((u * w : Kˣ) : K) = _
      rw [Units.val_mul, map_mul]
    rw [heq] at h1
    exact hasRep_unique _ _ _ _ _ h1 h2
  have h_sq_mul_iff : ∀ u w : Kˣ,
      IsSquare (algebraMap K (v.adicCompletion K) ((u * w : Kˣ) : K)) ↔
        (a_v u = a_v w ∧ b_v u = b_v w) := by
    intro u w
    have h2 : HasRep (algebraMap K (v.adicCompletion K) ((u * w : Kˣ) : K))
        (xor (a_v u) (a_v w)) (xor (b_v u) (b_v w)) := by
      rw [Units.val_mul, map_mul]
      exact hasRep_mul (ι u) (ι w) (a_v u) (b_v u) (a_v w) (b_v w) (h_rep_v u) (h_rep_v w)
    rw [hasRep_isSquare_iff _ _ _ h2]
    generalize a_v u = au, a_v w = aw, b_v u = bu, b_v w = bw
    revert au aw bu bw
    decide
  have h_ab_sq_K : ∀ u w : Kˣ, IsSquare ((u : K) * (w : K)) → a_v u = a_v w ∧ b_v u = b_v w := by
    intro u w hsq
    refine (h_sq_mul_iff u w).mp ?_
    rw [Units.val_mul]
    exact hsq.map (algebraMap K (v.adicCompletion K))
  have h_ram_iff : ∀ x₁ x₂ : Kˣ,
      RamLocal a₁ a₂ a₃ v πv x₁ x₂ ↔
      (((a_v x₁ = false ∧ b_v x₁ = false) ∧ (a_v x₂ = false ∧ b_v x₂ = false)) ∨
       ((xor (a_v x₁) c₀₁ = false ∧ xor (b_v x₁) false = false) ∧
        (xor (a_v x₂) c₀₂ = false ∧ xor (b_v x₂) true = false)) ∨
       ((xor (a_v x₁) (xor ε c₀₂) = false ∧ xor (b_v x₁) true = false) ∧
        (xor (a_v x₂) c₁₂ = false ∧ xor (b_v x₂) false = false)) ∨
       ((xor (a_v x₁) (xor c₀₁ (xor ε c₀₂)) = false ∧ xor (b_v x₁) true = false) ∧
        (xor (a_v x₂) (xor c₀₂ c₁₂) = false ∧ xor (b_v x₂) true = false))) := by
    intro x₁ x₂
    unfold RamLocal
    have e11 : algebraMap K (v.adicCompletion K) ((x₁ : K) * (a₁ - a₂) * (a₁ - a₃)) =
        ι x₁ * (α * β) := by
      dsimp [ι, α, β]; push_cast; ring
    have e12 : πv * algebraMap K (v.adicCompletion K) ((x₂ : K) * (a₁ - a₂)) =
        ι x₂ * (πv * α) := by
      dsimp [ι, α]; push_cast; ring
    have e21 : -(πv * algebraMap K (v.adicCompletion K) ((x₁ : K) * (a₁ - a₂))) =
        ι x₁ * -(πv * α) := by
      dsimp [ι, α]; push_cast; ring
    have e22 : algebraMap K (v.adicCompletion K) (-((x₂ : K) * (a₁ - a₂) * (a₂ - a₃))) =
        ι x₂ * -(α * γ) := by
      dsimp [ι, α, γ]; push_cast; ring
    have e31 : -(πv * algebraMap K (v.adicCompletion K) ((x₁ : K) * (a₁ - a₃))) =
        ι x₁ * -(πv * β) := by
      dsimp [ι, β]; push_cast; ring
    have e32 : -(πv * algebraMap K (v.adicCompletion K) ((x₂ : K) * (a₂ - a₃))) =
        ι x₂ * -(πv * γ) := by
      dsimp [ι, γ]; push_cast; ring
    rw [e11, e12, e21, e22, e31, e32]
    rw [hasRep_isSquare_iff (ι x₁) (a_v x₁) (b_v x₁) (h_rep_v x₁),
        hasRep_isSquare_iff (ι x₂) (a_v x₂) (b_v x₂) (h_rep_v x₂),
        hasRep_isSquare_iff _ _ _ (hasRep_mul _ _ _ _ _ _ (h_rep_v x₁) hrep_ab),
        hasRep_isSquare_iff _ _ _ (hasRep_mul _ _ _ _ _ _ (h_rep_v x₂) hrep_pa),
        hasRep_isSquare_iff _ _ _ (hasRep_mul _ _ _ _ _ _ (h_rep_v x₁) hrep_npa),
        hasRep_isSquare_iff _ _ _ (hasRep_mul _ _ _ _ _ _ (h_rep_v x₂) hrep_nag),
        hasRep_isSquare_iff _ _ _ (hasRep_mul _ _ _ _ _ _ (h_rep_v x₁) hrep_npb),
        hasRep_isSquare_iff _ _ _ (hasRep_mul _ _ _ _ _ _ (h_rep_v x₂) hrep_npg)]
  let φ_v : Kˣ × Kˣ → (Fin 2 → ZMod 2) :=
    fun p i => if i = 0 then b2z (φ₀ ε c₀₁ c₀₂ (a_v p.1) (b_v p.1) (a_v p.2) (b_v p.2))
               else b2z (φ₁ c₀₂ c₁₂ (a_v p.1) (b_v p.1) (a_v p.2) (b_v p.2))
  let ψ_v : Kˣ × Kˣ → (Fin 2 → ZMod 2) :=
    fun q i => if i = 0 then b2z (b_v q.2) else b2z (b_v q.1)
  have vec2_eq_zero_iff : ∀ x y : Bool,
      (fun i : Fin 2 => if i = 0 then b2z x else b2z y) = 0 ↔ (x = false ∧ y = false) := by
    intro x y
    constructor
    · intro h
      have h0 : b2z x = 0 := by simpa using congr_fun h 0
      have h1 : b2z y = 0 := by simpa using congr_fun h 1
      exact ⟨(b2z_eq_zero_iff x).mp h0, (b2z_eq_zero_iff y).mp h1⟩
    · rintro ⟨rfl, rfl⟩
      ext i
      fin_cases i <;> rfl
  have vec2_eq_iff : ∀ x₁ y₁ x₂ y₂ : Bool,
      (fun i : Fin 2 => if i = 0 then b2z x₁ else b2z y₁) =
      (fun i : Fin 2 => if i = 0 then b2z x₂ else b2z y₂) ↔ (x₁ = x₂ ∧ y₁ = y₂) := by
    intro x₁ y₁ x₂ y₂
    constructor
    · intro h
      have h0 : b2z x₁ = b2z x₂ := by simpa using congr_fun h 0
      have h1 : b2z y₁ = b2z y₂ := by simpa using congr_fun h 1
      exact ⟨(b2z_inj x₁ x₂).mp h0, (b2z_inj y₁ y₂).mp h1⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  refine ⟨φ_v, ψ_v, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q hpq1 hpq2
    dsimp [φ_v]
    rw [(h_ab_sq_K p.1 q.1 hpq1).1, (h_ab_sq_K p.1 q.1 hpq1).2,
        (h_ab_sq_K p.2 q.2 hpq2).1, (h_ab_sq_K p.2 q.2 hpq2).2]
  · intro p q
    ext i
    fin_cases i <;>
      simp [φ_v, (h_ab_mul p.1 q.1).1, (h_ab_mul p.1 q.1).2,
        (h_ab_mul p.2 q.2).1, (h_ab_mul p.2 q.2).2, h_φ₀_xor, h_φ₁_xor, b2z_xor]
  · intro p
    dsimp [φ_v]
    rw [vec2_eq_zero_iff, h_ram_iff p.1 p.2]
    exact h_zero_iff ε c₀₁ c₀₂ c₁₂ (a_v p.1) (b_v p.1) (a_v p.2) (b_v p.2)
  · intro q₁ q₂ hq₁ hq₂ hψ
    dsimp [φ_v] at hq₁ hq₂
    dsimp [ψ_v] at hψ
    rw [vec2_eq_zero_iff] at hq₁ hq₂
    rw [vec2_eq_iff] at hψ
    rw [h_sq_mul_iff q₁.1 q₂.1, h_sq_mul_iff q₁.2 q₂.2]
    rcases hq₁ with ⟨hq₁0, hq₁1⟩
    rcases hq₂ with ⟨hq₂0, hq₂1⟩
    dsimp [φ₀] at hq₁0 hq₂0
    dsimp [φ₁] at hq₁1 hq₂1
    rw [hψ.2, hψ.1] at hq₁0 hq₁1
    exact ⟨⟨xor_eq_false_inj _ _ _ hq₁0 hq₂0, hψ.2⟩,
      ⟨xor_eq_false_inj _ _ _ hq₁1 hq₂1, hψ.1⟩⟩
  · intro q p hq
    dsimp [φ_v] at hq
    rw [vec2_eq_zero_iff] at hq
    change hilbLoc v (ι q.1) (ι p.2) * hilbLoc v (ι q.2) (ι p.1) = _
    rw [hasRep_hilbLoc (ι q.1) (ι p.2) (a_v q.1) (b_v q.1) (a_v p.2) (b_v p.2)
          (h_rep_v q.1) (h_rep_v p.2),
        hasRep_hilbLoc (ι q.2) (ι p.1) (a_v q.2) (b_v q.2) (a_v p.1) (b_v p.1)
          (h_rep_v q.2) (h_rep_v p.1)]
    have hdot : dotProduct (ψ_v q) (φ_v p) =
        b2z (b_v q.2) * b2z (φ₀ ε c₀₁ c₀₂ (a_v p.1) (b_v p.1) (a_v p.2) (b_v p.2)) +
        b2z (b_v q.1) * b2z (φ₁ c₀₂ c₁₂ (a_v p.1) (b_v p.1) (a_v p.2) (b_v p.2)) := by
      simp [dotProduct, Fin.sum_univ_two, ψ_v, φ_v]
    rw [hdot]
    apply h_sign_exp
    exact h_pair_bridge _ _ _ _ _
      (h_pair_core ε c₀₁ c₀₂ c₁₂ (a_v q.1) (b_v q.1) (a_v q.2) (b_v q.2)
        (a_v p.1) (b_v p.1) (a_v p.2) (b_v p.2))
      hq

theorem evenVal_selmer_basis_at_v {K : Type u} [Field K] [NumberField K]
    (a₁ a₂ a₃ : K) (h₁₂ : a₁ ≠ a₂) (h₁₃ : a₁ ≠ a₃) (h₂₃ : a₂ ≠ a₃)
    (hint₁ : IsIntegral ℤ a₁) (hint₂ : IsIntegral ℤ a₂) (hint₃ : IsIntegral ℤ a₃)
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hT : IsGoodT a₁ a₂ a₃ T)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hvT : v ∉ T) :
    ∃ (φ_v ψ_v : Kˣ × Kˣ → (Fin 2 → ZMod 2)),
      (∀ p q : Kˣ × Kˣ,
        IsSquare ((p.1 : K) * (q.1 : K)) → IsSquare ((p.2 : K) * (q.2 : K)) →
        φ_v p = φ_v q) ∧
      (∀ p q : Kˣ × Kˣ, φ_v (p.1 * q.1, p.2 * q.2) = φ_v p + φ_v q) ∧
      (∀ p : Kˣ × Kˣ, φ_v p = 0 ↔ EvenVal v p.1 ∧ EvenVal v p.2) ∧
      (∀ q₁ q₂ : Kˣ × Kˣ, φ_v q₁ = 0 → φ_v q₂ = 0 → ψ_v q₁ = ψ_v q₂ →
        IsSquare (algebraMap K (v.adicCompletion K) ((q₁.1 * q₂.1 : Kˣ) : K)) ∧
        IsSquare (algebraMap K (v.adicCompletion K) ((q₁.2 * q₂.2 : Kˣ) : K))) ∧
      (∀ q p : Kˣ × Kˣ, φ_v q = 0 →
        hilbFin v (q.1 : K) (p.2 : K) * hilbFin v (q.2 : K) (p.1 : K) =
          (-1 : ℤˣ) ^ (dotProduct (ψ_v q) (φ_v p)).val) :=
by
  classical
  have h2_val : IsDedekindDomain.HeightOneSpectrum.valuation K v (2 : K) = 1 := by
    let A₁ : NumberField.RingOfIntegers K := ⟨a₁, hint₁⟩
    let A₂ : NumberField.RingOfIntegers K := ⟨a₂, hint₂⟩
    let A₃ : NumberField.RingOfIntegers K := ⟨a₃, hint₃⟩
    let W : NumberField.RingOfIntegers K := 3 * (A₁ - A₂) * (A₁ - A₃) * (A₂ - A₃)
    have h2_le : IsDedekindDomain.HeightOneSpectrum.valuation K v (2 : K) ≤ 1 := by
      rw [← map_ofNat (algebraMap (NumberField.RingOfIntegers K) K) 2]
      exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one v 2
    have hW_le : IsDedekindDomain.HeightOneSpectrum.valuation K v
        (algebraMap (NumberField.RingOfIntegers K) K W) ≤ 1 :=
      IsDedekindDomain.HeightOneSpectrum.valuation_le_one v W
    have hprod_eq : 6 * (a₁ - a₂) * (a₁ - a₃) * (a₂ - a₃) =
        (2 : K) * algebraMap (NumberField.RingOfIntegers K) K W := by
      change 6 * (a₁ - a₂) * (a₁ - a₃) * (a₂ - a₃) =
        (2 : K) * algebraMap (NumberField.RingOfIntegers K) K
          (3 * (A₁ - A₂) * (A₁ - A₃) * (A₂ - A₃))
      simp only [map_mul, map_sub, map_ofNat]
      change 6 * (a₁ - a₂) * (a₁ - a₃) * (a₂ - a₃) =
        2 * (3 * (a₁ - a₂) * (a₁ - a₃) * (a₂ - a₃))
      ring
    have hv_prod : IsDedekindDomain.HeightOneSpectrum.valuation K v
        (6 * (a₁ - a₂) * (a₁ - a₃) * (a₂ - a₃)) = 1 := by
      have h := (hT v).not.mp hvT
      push_neg at h
      exact h
    rw [hprod_eq, Valuation.map_mul] at hv_prod
    refine le_antisymm h2_le ?_
    calc (1 : WithZero (Multiplicative ℤ))
        = IsDedekindDomain.HeightOneSpectrum.valuation K v (2 : K) *
            IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K W) := hv_prod.symm
      _ ≤ IsDedekindDomain.HeightOneSpectrum.valuation K v (2 : K) * 1 :=
          mul_le_mul_right hW_le _
      _ = IsDedekindDomain.HeightOneSpectrum.valuation K v (2 : K) := mul_one _
  have h2 : Valued.v (2 : v.adicCompletion K) = 1 := by
    rw [← map_ofNat (algebraMap K (v.adicCompletion K)) 2]
    exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (2 : K)).trans h2_val
  have exists_ringOfIntegers_approx_of_valuation_le_one :
      ∀ (a : K), IsDedekindDomain.HeightOneSpectrum.valuation K v a ≤ 1 →
      ∃ r : NumberField.RingOfIntegers K,
        IsDedekindDomain.HeightOneSpectrum.valuation K v
          (a - algebraMap (NumberField.RingOfIntegers K) K r) < 1 := by
    intro a ha
    obtain ⟨xa, ya, hya, hxya⟩ :=
      IsFractionRing.div_surjective (A := NumberField.RingOfIntegers K) (K := K) a
    have hy0 : ya ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hya
    have hiy : algebraMap (NumberField.RingOfIntegers K) K ya ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hya
    have hstar : a * algebraMap (NumberField.RingOfIntegers K) K ya
        = algebraMap (NumberField.RingOfIntegers K) K xa := by
      rw [← hxya]
      exact div_mul_cancel₀ _ hiy
    obtain ⟨m, hym, hym1⟩ : ∃ m : ℕ, ya ∈ v.asIdeal ^ m ∧ ya ∉ v.asIdeal ^ (m + 1) := by
      have ht0 : v.intValuation ya ≠ 0 :=
        IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero v ya hy0
      have ht1 : v.intValuation ya ≤ 1 :=
        IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v ya
      obtain ⟨k, hk⟩ : ∃ k : ℤ, WithZero.exp k = v.intValuation ya := ⟨_, WithZero.exp_log ht0⟩
      have hkle : k ≤ 0 := by
        have hstep : WithZero.exp k ≤ WithZero.exp (0 : ℤ) := by
          rw [hk, WithZero.exp_zero]; exact ht1
        exact WithZero.exp_le_exp.mp hstep
      have hcast : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      have hexpm : WithZero.exp (-(((-k).toNat : ℕ) : ℤ)) = v.intValuation ya := by
        rw [hcast, neg_neg, hk]
      refine ⟨(-k).toNat, ?_, ?_⟩
      · exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya _).mp
          (le_of_eq hexpm.symm)
      · intro hcon
        have hle :=
          (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya
            ((-k).toNat + 1)).mpr hcon
        have he : (-(((-k).toNat + 1 : ℕ) : ℤ)) = k - 1 := by
          rw [Nat.cast_add, Nat.cast_one, hcast]; ring
        rw [he, ← hk] at hle
        have := WithZero.exp_le_exp.mp hle
        omega
    have hivy : v.intValuation ya ≤ WithZero.exp (-(m : ℤ)) :=
      (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya m).mpr hym
    have hxm : xa ∈ v.asIdeal ^ m := by
      refine (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v xa m).mp ?_
      have e1 : v.intValuation xa
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K xa) :=
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v xa).symm
      have e2 : v.intValuation ya
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K ya) :=
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v ya).symm
      calc v.intValuation xa
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (a * algebraMap (NumberField.RingOfIntegers K) K ya) := by
            rw [hstar]; exact e1
        _ = IsDedekindDomain.HeightOneSpectrum.valuation K v a *
              IsDedekindDomain.HeightOneSpectrum.valuation K v
                (algebraMap (NumberField.RingOfIntegers K) K ya) := Valuation.map_mul _ _ _
        _ ≤ 1 * IsDedekindDomain.HeightOneSpectrum.valuation K v
                (algebraMap (NumberField.RingOfIntegers K) K ya) := mul_le_mul_left ha _
        _ = v.intValuation ya := by rw [one_mul, ← e2]
        _ ≤ WithZero.exp (-(m : ℤ)) := hivy
    have hPprime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
    have hJdvd : (Ideal.span {ya} ⊔ v.asIdeal ^ (m + 1)) ∣ v.asIdeal ^ (m + 1) :=
      Ideal.dvd_iff_le.mpr le_sup_right
    obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow hPprime (m + 1)).mp hJdvd
    have hJ : Ideal.span {ya} ⊔ v.asIdeal ^ (m + 1) = v.asIdeal ^ i := associated_iff_eq.mp hassoc
    have hyJ : ya ∈ v.asIdeal ^ i := by
      rw [← hJ]
      exact Ideal.dvd_span_singleton.mp (Ideal.dvd_iff_le.mpr le_sup_left)
    have him : i ≤ m := by
      by_contra hcon
      have hii : i = m + 1 := by omega
      rw [hii] at hyJ
      exact hym1 hyJ
    have hxJ : xa ∈ Ideal.span {ya} ⊔ v.asIdeal ^ (m + 1) := by
      rw [hJ]
      exact Ideal.pow_le_pow_right him hxm
    obtain ⟨p, hp, w, hw, hpw⟩ := Submodule.mem_sup.mp hxJ
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hp
    refine ⟨r, ?_⟩
    have hxrw : xa = r * ya + w := by rw [← hpw, hr]
    have key : (a - algebraMap (NumberField.RingOfIntegers K) K r)
        * algebraMap (NumberField.RingOfIntegers K) K ya
        = algebraMap (NumberField.RingOfIntegers K) K w := by
      have h1 : algebraMap (NumberField.RingOfIntegers K) K xa
          = algebraMap (NumberField.RingOfIntegers K) K r
              * algebraMap (NumberField.RingOfIntegers K) K ya
            + algebraMap (NumberField.RingOfIntegers K) K w := by
        rw [hxrw, map_add, map_mul]
      rw [sub_mul, hstar, h1]; ring
    have hV : IsDedekindDomain.HeightOneSpectrum.valuation K v
          (a - algebraMap (NumberField.RingOfIntegers K) K r) * v.intValuation ya
        = v.intValuation w := by
      rw [← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v ya,
        ← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v w,
        ← Valuation.map_mul, key]
    have hwb : v.intValuation w ≤ WithZero.exp (-((m + 1 : ℕ) : ℤ)) :=
      (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v w (m + 1)).mpr hw
    have hyb : WithZero.exp (-((m + 1 : ℕ) : ℤ)) < v.intValuation ya := by
      by_contra hcon
      push_neg at hcon
      exact hym1
        ((IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya (m + 1)).mp hcon)
    by_contra hcon
    push_neg at hcon
    have hchain : v.intValuation ya ≤ v.intValuation w := by
      calc v.intValuation ya = 1 * v.intValuation ya := (one_mul _).symm
        _ ≤ IsDedekindDomain.HeightOneSpectrum.valuation K v
              (a - algebraMap (NumberField.RingOfIntegers K) K r) * v.intValuation ya :=
            mul_le_mul_left hcon _
        _ = v.intValuation w := hV
    exact absurd (lt_of_le_of_lt (le_trans hchain hwb) hyb) (lt_irrefl _)
  have h_approx : ∀ z : v.adicCompletion K, Valued.v z ≤ 1 →
      ∃ r : NumberField.RingOfIntegers K,
        Valued.v (z - algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K r)) < 1 := by
    intro z hz
    have hdense : DenseRange (fun y : K => algebraMap K (v.adicCompletion K) y) := by
      letI : Valued K (WithZero (Multiplicative ℤ)) :=
        IsDedekindDomain.HeightOneSpectrum.adicValued (K := K) v
      exact UniformSpace.Completion.denseRange_coe
    have hnhds : {y : v.adicCompletion K |
        Valued.v (y - z) < ((1 : (WithZero (Multiplicative ℤ))ˣ) :
          WithZero (Multiplicative ℤ))} ∈ nhds z :=
      Valued.mem_nhds.mpr ⟨1, subset_rfl⟩
    obtain ⟨u, hu1, k, hk⟩ := mem_closure_iff_nhds.mp (hdense z) _ hnhds
    have hkl : Valued.v (z - algebraMap K (v.adicCompletion K) k) < 1 := by
      dsimp only at hk
      rw [Valuation.map_sub_swap, hk]
      exact hu1
    have hvc : ∀ x : K, Valued.v (algebraMap K (v.adicCompletion K) x) =
        IsDedekindDomain.HeightOneSpectrum.valuation K v x :=
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v
    have hvk : IsDedekindDomain.HeightOneSpectrum.valuation K v k ≤ 1 := by
      rw [← hvc k]
      have hsplit : algebraMap K (v.adicCompletion K) k =
          z - (z - algebraMap K (v.adicCompletion K) k) := by ring
      rw [hsplit]
      exact le_trans (Valuation.map_sub Valued.v _ _) (max_le hz (le_of_lt hkl))
    obtain ⟨r, hr⟩ := exists_ringOfIntegers_approx_of_valuation_le_one k hvk
    refine ⟨r, ?_⟩
    have hsplit2 : z - algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K r) =
        (z - algebraMap K (v.adicCompletion K) k) +
          algebraMap K (v.adicCompletion K)
            (k - algebraMap (NumberField.RingOfIntegers K) K r) := by
      rw [map_sub]; ring
    rw [hsplit2]
    refine lt_of_le_of_lt (Valuation.map_add Valued.v _ _) (max_lt hkl ?_)
    rw [hvc]
    exact hr
  have exists_sol_quadratic_mod_heightOneSpectrum :
      (2 : NumberField.RingOfIntegers K) ∉ v.asIdeal →
      ∀ (r s : NumberField.RingOfIntegers K), r ∉ v.asIdeal → s ∉ v.asIdeal →
      ∃ x₀ y₀ : NumberField.RingOfIntegers K, r * x₀ ^ 2 + s * y₀ ^ 2 - 1 ∈ v.asIdeal := by
    intro h2not r s hr hs
    letI : Field (NumberField.RingOfIntegers K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
    letI : Fintype (NumberField.RingOfIntegers K ⧸ v.asIdeal) := Fintype.ofFinite _
    have hr' : Ideal.Quotient.mk v.asIdeal r ≠ 0 := fun h =>
      hr (Ideal.Quotient.eq_zero_iff_mem.mp h)
    have hs' : Ideal.Quotient.mk v.asIdeal s ≠ 0 := fun h =>
      hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
    have h2' : (2 : NumberField.RingOfIntegers K ⧸ v.asIdeal) ≠ 0 := by
      intro h
      refine h2not (Ideal.Quotient.eq_zero_iff_mem.mp ?_)
      rw [map_ofNat]
      exact h
    have hchar : ringChar (NumberField.RingOfIntegers K ⧸ v.asIdeal) ≠ 2 := by
      intro h
      refine h2' ?_
      have h4 : ((2 : ℕ) : NumberField.RingOfIntegers K ⧸ v.asIdeal) = 0 :=
        (ringChar.spec _ 2).mpr (by rw [h])
      simpa using h4
    have hcard : Fintype.card (NumberField.RingOfIntegers K ⧸ v.asIdeal) % 2 = 1 :=
      FiniteField.odd_card_of_char_ne_two hchar
    obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
      (f := Polynomial.C (Ideal.Quotient.mk v.asIdeal r) * Polynomial.X ^ 2
        + Polynomial.C 0 * Polynomial.X + Polynomial.C 0)
      (g := Polynomial.C (Ideal.Quotient.mk v.asIdeal s) * Polynomial.X ^ 2
        + Polynomial.C 0 * Polynomial.X + Polynomial.C (-1))
      (Polynomial.degree_quadratic hr') (Polynomial.degree_quadratic hs') hcard
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, zero_mul, add_zero] at hab
    obtain ⟨x₀, hx₀⟩ := Ideal.Quotient.mk_surjective (I := v.asIdeal) a
    obtain ⟨y₀, hy₀⟩ := Ideal.Quotient.mk_surjective (I := v.asIdeal) b
    refine ⟨x₀, y₀, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
    simp only [map_sub, map_add, map_mul, map_pow, map_one]
    rw [hx₀, hy₀]
    linear_combination hab
  have h_hensel : ∀ (c x₀ : v.adicCompletion K),
      Valued.v x₀ = (1 : WithZero (Multiplicative ℤ)) →
      Valued.v (c - x₀ ^ 2) < (1 : WithZero (Multiplicative ℤ)) →
      ∃ z : v.adicCompletion K, z ^ 2 = c := by
    intro c x₀ hx₀ hc
    have hstep : ∀ y : v.adicCompletion K,
        Valued.v y = (1 : WithZero (Multiplicative ℤ)) →
        Valued.v (y ^ 2 - c) < (1 : WithZero (Multiplicative ℤ)) →
        Valued.v (y - (y ^ 2 - c) / (2 * y)) = (1 : WithZero (Multiplicative ℤ)) ∧
        Valued.v ((y - (y ^ 2 - c) / (2 * y)) ^ 2 - c) = Valued.v (y ^ 2 - c) ^ 2 ∧
        Valued.v (y - (y ^ 2 - c) / (2 * y) - y) = Valued.v (y ^ 2 - c) := by
      intro y hy hd
      have h2ne : (2 : v.adicCompletion K) ≠ 0 := by
        intro hcon; rw [hcon, map_zero] at h2; exact zero_ne_one h2
      have hyne : y ≠ 0 := by
        intro hcon; rw [hcon, map_zero] at hy; exact zero_ne_one hy
      have ht : Valued.v ((y ^ 2 - c) / (2 * y)) = Valued.v (y ^ 2 - c) := by
        rw [map_div₀, map_mul, h2, hy, one_mul, div_one]
      have hlt' : Valued.v ((y ^ 2 - c) / (2 * y)) < Valued.v y := by
        rw [ht, hy]; exact hd
      refine ⟨?_, ?_, ?_⟩
      · rw [Valuation.map_sub_eq_of_lt_left _ hlt', hy]
      · have key : (y - (y ^ 2 - c) / (2 * y)) ^ 2 - c = ((y ^ 2 - c) / (2 * y)) ^ 2 := by
          field_simp; ring
        rw [key, Valuation.map_pow, ht]
      · have key : y - (y ^ 2 - c) / (2 * y) - y = -((y ^ 2 - c) / (2 * y)) := by ring
        rw [key, Valuation.map_neg, ht]
    have hdecay : ∀ δ γ : WithZero (Multiplicative ℤ), δ < 1 → γ ≠ 0 →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → δ ^ (2 ^ n) < γ := by
      intro δ γ hδ hγ
      rcases eq_or_ne δ 0 with h0 | h0
      · refine ⟨0, fun n _ => ?_⟩
        rw [h0, zero_pow (Nat.two_pow_pos n).ne']
        exact zero_lt_iff.mpr hγ
      · obtain ⟨a, rfl⟩ : ∃ a : ℤ, δ = ((Multiplicative.ofAdd a : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
          obtain ⟨g, hg⟩ := WithZero.ne_zero_iff_exists.mp h0
          exact ⟨Multiplicative.toAdd g, hg.symm⟩
        obtain ⟨b, rfl⟩ : ∃ b : ℤ, γ = ((Multiplicative.ofAdd b : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
          obtain ⟨g, hg⟩ := WithZero.ne_zero_iff_exists.mp hγ
          exact ⟨Multiplicative.toAdd g, hg.symm⟩
        have ha : a < 0 := WithZero.coe_lt_one.mp hδ
        have hpow : ∀ k : ℕ,
            ((Multiplicative.ofAdd a : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ k
              = ((Multiplicative.ofAdd ((k : ℤ) * a) : Multiplicative ℤ) :
                  WithZero (Multiplicative ℤ)) := by
          intro k; rw [← WithZero.coe_pow]; congr 1
        refine ⟨(-b).toNat + 1, fun n hn => ?_⟩
        rw [hpow, WithZero.coe_lt_coe]
        have hbk : -b < ((2 ^ n : ℕ) : ℤ) := by
          have hx : (-b).toNat < n := by omega
          have h1 : (-b).toNat < 2 ^ n := lt_trans hx Nat.lt_two_pow_self
          have h2' : ((-b).toNat : ℤ) < ((2 ^ n : ℕ) : ℤ) := by exact_mod_cast h1
          exact lt_of_le_of_lt (Int.self_le_toNat _) h2'
        have hkpos : (0 : ℤ) ≤ ((2 ^ n : ℕ) : ℤ) := Int.natCast_nonneg _
        have ha1 : a ≤ -1 := by omega
        have hle : ((2 ^ n : ℕ) : ℤ) * a ≤ ((2 ^ n : ℕ) : ℤ) * (-1) :=
          mul_le_mul_of_nonneg_left ha1 hkpos
        have hgoal : ((2 ^ n : ℕ) : ℤ) * a < b := by linarith
        exact hgoal
    obtain ⟨ε, hεdef⟩ : ∃ ε : WithZero (Multiplicative ℤ), ε = Valued.v (x₀ ^ 2 - c) := ⟨_, rfl⟩
    have hε : ε < (1 : WithZero (Multiplicative ℤ)) := by
      rw [hεdef, Valuation.map_sub_swap]; exact hc
    obtain ⟨f, hf0, hfs⟩ : ∃ f : ℕ → v.adicCompletion K, f 0 = x₀ ∧
        ∀ n : ℕ, f (n + 1) = f n - (f n ^ 2 - c) / (2 * f n) :=
      ⟨fun n => Nat.rec (motive := fun _ => v.adicCompletion K) x₀
        (fun _ y => y - (y ^ 2 - c) / (2 * y)) n, rfl, fun _ => rfl⟩
    have hinv : ∀ n : ℕ, Valued.v (f n) = (1 : WithZero (Multiplicative ℤ)) ∧
        Valued.v (f n ^ 2 - c) = ε ^ (2 ^ n) := by
      intro n
      induction n with
      | zero =>
        refine ⟨by rw [hf0]; exact hx₀, ?_⟩
        rw [hf0, pow_zero, pow_one, hεdef]
      | succ n ih =>
        have hlt : Valued.v (f n ^ 2 - c) < (1 : WithZero (Multiplicative ℤ)) := by
          rw [ih.2]; exact pow_lt_one₀ zero_le' hε (Nat.two_pow_pos n).ne'
        obtain ⟨s1, s2, -⟩ := hstep (f n) ih.1 hlt
        refine ⟨by rw [hfs n]; exact s1, ?_⟩
        rw [hfs n, s2, ih.2, ← pow_mul, ← pow_succ]
    have hdiff : ∀ n : ℕ, Valued.v (f (n + 1) - f n) = ε ^ (2 ^ n) := by
      intro n
      have hlt : Valued.v (f n ^ 2 - c) < (1 : WithZero (Multiplicative ℤ)) := by
        rw [(hinv n).2]; exact pow_lt_one₀ zero_le' hε (Nat.two_pow_pos n).ne'
      obtain ⟨-, -, s3⟩ := hstep (f n) (hinv n).1 hlt
      rw [hfs n, s3, (hinv n).2]
    have hCauchy : Cauchy (Filter.map f Filter.atTop) := by
      refine Valued.cauchy_iff.mpr ⟨inferInstance, ?_⟩
      intro γ
      obtain ⟨N, hN⟩ := hdecay ε (γ : WithZero (Multiplicative ℤ)) hε (Units.ne_zero γ)
      have htel : ∀ m : ℕ, N ≤ m → Valued.v (f m - f N) < (γ : WithZero (Multiplicative ℤ)) := by
        intro m hm
        induction m, hm using Nat.le_induction with
        | base =>
          rw [sub_self, map_zero]; exact zero_lt_iff.mpr (Units.ne_zero γ)
        | succ m hm ih =>
          have e : f (m + 1) - f N = (f (m + 1) - f m) + (f m - f N) := by ring
          rw [e]
          refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ih)
          rw [hdiff m]; exact hN m hm
      refine ⟨f '' (Set.Ici N), Filter.image_mem_map (Filter.Ici_mem_atTop N), ?_⟩
      rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
      have e : f j - f i = (f j - f N) - (f i - f N) := by ring
      rw [e]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt (htel j hj) (htel i hi))
    obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hCauchy
    have hsq : Filter.Tendsto (fun n : ℕ => f n ^ 2 - c) Filter.atTop (nhds (z ^ 2 - c)) :=
      (hz.pow 2).sub tendsto_const_nhds
    have hzero : Filter.Tendsto (fun n : ℕ => f n ^ 2 - c) Filter.atTop
        (nhds (0 : v.adicCompletion K)) := by
      rw [Filter.tendsto_def]
      intro s hs
      obtain ⟨γ, hγs⟩ := Valued.mem_nhds_zero.mp hs
      obtain ⟨N, hN⟩ := hdecay ε (γ : WithZero (Multiplicative ℤ)) hε (Units.ne_zero γ)
      refine Filter.mem_of_superset (Filter.Ici_mem_atTop N) ?_
      intro n hn
      apply hγs
      show Valued.v (f n ^ 2 - c) < (γ : WithZero (Multiplicative ℤ))
      rw [(hinv n).2]; exact hN n hn
    exact ⟨z, eq_of_sub_eq_zero (tendsto_nhds_unique hsq hzero)⟩
  have s2 : ∀ (r s : v.adicCompletion K),
      Valued.v r = 1 → Valued.v s = 1 → hilbLoc v r s = 1 := by
    intro r s hr hs
    have hT_int : ∀ a : NumberField.RingOfIntegers K,
        Valued.v (algebraMap K (v.adicCompletion K)
            (algebraMap (NumberField.RingOfIntegers K) K a))
          = IsDedekindDomain.HeightOneSpectrum.intValuation v a := by
      intro a
      exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v
        (algebraMap (NumberField.RingOfIntegers K) K a)).trans
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v a)
    have h2not : (2 : NumberField.RingOfIntegers K) ∉ v.asIdeal := by
      refine IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mp ?_
      rw [← hT_int (2 : NumberField.RingOfIntegers K),
        map_ofNat (algebraMap (NumberField.RingOfIntegers K) K) 2,
        map_ofNat (algebraMap K (v.adicCompletion K)) 2]
      exact h2
    obtain ⟨R₀, hA1⟩ := h_approx r (le_of_eq hr)
    obtain ⟨S₀, hA2⟩ := h_approx s (le_of_eq hs)
    have hR0v : Valued.v (algebraMap K (v.adicCompletion K)
        (algebraMap (NumberField.RingOfIntegers K) K R₀)) = 1 := by
      have e : (algebraMap K (v.adicCompletion K)
            (algebraMap (NumberField.RingOfIntegers K) K R₀))
          = r - (r - algebraMap K (v.adicCompletion K)
              (algebraMap (NumberField.RingOfIntegers K) K R₀)) := by ring
      rw [e, Valuation.map_sub_eq_of_lt_left _ (by rw [hr]; exact hA1), hr]
    have hS0v : Valued.v (algebraMap K (v.adicCompletion K)
        (algebraMap (NumberField.RingOfIntegers K) K S₀)) = 1 := by
      have e : (algebraMap K (v.adicCompletion K)
            (algebraMap (NumberField.RingOfIntegers K) K S₀))
          = s - (s - algebraMap K (v.adicCompletion K)
              (algebraMap (NumberField.RingOfIntegers K) K S₀)) := by ring
      rw [e, Valuation.map_sub_eq_of_lt_left _ (by rw [hs]; exact hA2), hs]
    have hR0not : R₀ ∉ v.asIdeal := by
      refine IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mp ?_
      rw [← hT_int R₀]; exact hR0v
    have hS0not : S₀ ∉ v.asIdeal := by
      refine IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mp ?_
      rw [← hT_int S₀]; exact hS0v
    obtain ⟨A, B, hAB⟩ :=
      exists_sol_quadratic_mod_heightOneSpectrum h2not R₀ S₀ hR0not hS0not
    let ρR := algebraMap K (v.adicCompletion K) (algebraMap (NumberField.RingOfIntegers K) K R₀)
    let ρS := algebraMap K (v.adicCompletion K) (algebraMap (NumberField.RingOfIntegers K) K S₀)
    let X := algebraMap K (v.adicCompletion K) (algebraMap (NumberField.RingOfIntegers K) K A)
    let Y := algebraMap K (v.adicCompletion K) (algebraMap (NumberField.RingOfIntegers K) K B)
    have hXle : Valued.v X ≤ 1 := by
      change Valued.v (algebraMap K (v.adicCompletion K)
        (algebraMap (NumberField.RingOfIntegers K) K A)) ≤ 1
      rw [hT_int A]; exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v A
    have hYle : Valued.v Y ≤ 1 := by
      change Valued.v (algebraMap K (v.adicCompletion K)
        (algebraMap (NumberField.RingOfIntegers K) K B)) ≤ 1
      rw [hT_int B]; exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v B
    have hmod : Valued.v (ρR * X ^ 2 + ρS * Y ^ 2 - 1) < 1 := by
      have e : ρR * X ^ 2 + ρS * Y ^ 2 - 1 =
          algebraMap K (v.adicCompletion K)
            (algebraMap (NumberField.RingOfIntegers K) K (R₀ * A ^ 2 + S₀ * B ^ 2 - 1)) := by
        simp only [ρR, ρS, X, Y, map_add, map_mul, map_pow, map_sub, map_one]
      rw [e, hT_int, IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem]
      exact hAB
    have hunit : Valued.v X = 1 ∨ Valued.v Y = 1 := by
      have hcase : A ∉ v.asIdeal ∨ B ∉ v.asIdeal := by
        by_contra hcon
        push_neg at hcon
        obtain ⟨hA, hB⟩ := hcon
        have h1 : R₀ * A ^ 2 + S₀ * B ^ 2 ∈ v.asIdeal :=
          Ideal.add_mem _
            (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hA 2 (by norm_num)))
            (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hB 2 (by norm_num)))
        have hone : (1 : NumberField.RingOfIntegers K) ∈ v.asIdeal := by
          have h3 := Ideal.sub_mem _ h1 hAB
          simpa using h3
        exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)
      rcases hcase with h | h
      · refine Or.inl ?_
        change Valued.v (algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K A)) = 1
        rw [hT_int A]; exact IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr h
      · refine Or.inr ?_
        change Valued.v (algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K B)) = 1
        rw [hT_int B]; exact IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr h
    have hbeta : Valued.v (r * X ^ 2 + s * Y ^ 2 - 1) < 1 := by
      have t1 : Valued.v ((r - ρR) * X ^ 2) < 1 := by
        rw [Valuation.map_mul, Valuation.map_pow]
        calc Valued.v (r - ρR) * Valued.v X ^ 2
            ≤ Valued.v (r - ρR) * 1 := mul_le_mul_left' (pow_le_one' hXle 2) _
          _ = Valued.v (r - ρR) := mul_one _
          _ < 1 := hA1
      have t2 : Valued.v ((s - ρS) * Y ^ 2) < 1 := by
        rw [Valuation.map_mul, Valuation.map_pow]
        calc Valued.v (s - ρS) * Valued.v Y ^ 2
            ≤ Valued.v (s - ρS) * 1 := mul_le_mul_left' (pow_le_one' hYle 2) _
          _ = Valued.v (s - ρS) := mul_one _
          _ < 1 := hA2
      have t3 : Valued.v ((r - ρR) * X ^ 2 + (s - ρS) * Y ^ 2) < 1 :=
        lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt t1 t2)
      have e : r * X ^ 2 + s * Y ^ 2 - 1
          = (ρR * X ^ 2 + ρS * Y ^ 2 - 1)
            + ((r - ρR) * X ^ 2 + (s - ρS) * Y ^ 2) := by ring
      rw [e]
      exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hmod t3)
    have key : ∀ a b P Q : v.adicCompletion K, Valued.v a = 1 → Valued.v P = 1 →
        Valued.v (a * P ^ 2 + b * Q ^ 2 - 1) < 1 →
        ∃ x y : v.adicCompletion K, a * x ^ 2 + b * y ^ 2 = 1 := by
      intro a b P Q ha hP hlt
      have ha0 : a ≠ 0 := by
        intro hzero; rw [hzero, Valuation.map_zero] at ha; exact zero_ne_one ha
      have hac : a * ((1 - b * Q ^ 2) / a) = 1 - b * Q ^ 2 := mul_div_cancel₀ _ ha0
      have hid : a * ((1 - b * Q ^ 2) / a - P ^ 2)
          = -(a * P ^ 2 + b * Q ^ 2 - 1) := by
        rw [mul_sub, hac]; ring
      have hlt2 : Valued.v ((1 - b * Q ^ 2) / a - P ^ 2) < 1 := by
        have h : Valued.v (a * ((1 - b * Q ^ 2) / a - P ^ 2))
            = Valued.v (-(a * P ^ 2 + b * Q ^ 2 - 1)) := by rw [hid]
        rw [Valuation.map_mul, ha, one_mul, Valuation.map_neg] at h
        rw [h]; exact hlt
      obtain ⟨x, hx⟩ := h_hensel ((1 - b * Q ^ 2) / a) P hP hlt2
      exact ⟨x, Q, by rw [hx]; linear_combination hac⟩
    have hex : ∃ x y : v.adicCompletion K, r * x ^ 2 + s * y ^ 2 = 1 := by
      rcases hunit with hX1 | hY1
      · exact key r s X Y hr hX1 hbeta
      · have hbeta' : Valued.v (s * Y ^ 2 + r * X ^ 2 - 1) < 1 := by
          have e : s * Y ^ 2 + r * X ^ 2 - 1 = r * X ^ 2 + s * Y ^ 2 - 1 := by ring
          rw [e]; exact hbeta
        obtain ⟨x, y, hxy⟩ := key s r Y X hs hY1 hbeta'
        exact ⟨y, x, by linear_combination hxy⟩
    simp only [hilbLoc, if_pos hex]
  have s3 : ∀ (u w : v.adicCompletion K),
      Valued.v u = 1 → Valued.v w = 1 → (IsSquare (u * w) ↔ (IsSquare u ↔ IsSquare w)) := by
    intro u w hu hw
    have hu0 : u ≠ 0 := by intro h; rw [h, Valuation.map_zero] at hu; exact zero_ne_one hu
    have hw0 : w ≠ 0 := by intro h; rw [h, Valuation.map_zero] at hw; exact zero_ne_one hw
    constructor
    · rintro ⟨t, ht⟩
      constructor
      · rintro ⟨s, rfl⟩
        have hs0 : s ≠ 0 := by rintro rfl; rw [mul_zero] at hu0; exact hu0 rfl
        refine ⟨t / s, ?_⟩
        field_simp [hs0]
        linear_combination ht
      · rintro ⟨s, rfl⟩
        have hs0 : s ≠ 0 := by rintro rfl; rw [mul_zero] at hw0; exact hw0 rfl
        refine ⟨t / s, ?_⟩
        field_simp [hs0]
        linear_combination ht
    · intro hiff
      by_cases hu_sq : IsSquare u
      · exact IsSquare.mul hu_sq (hiff.mp hu_sq)
      · have hw_nsq : ¬ IsSquare w := fun hw_sq => hu_sq (hiff.mpr hw_sq)
        let ι : NumberField.RingOfIntegers K →+* v.adicCompletion K :=
          (algebraMap K (v.adicCompletion K)).comp (algebraMap (NumberField.RingOfIntegers K) K)
        have V0 : ∀ c : NumberField.RingOfIntegers K, Valued.v (ι c) = v.intValuation c := by
          intro c
          exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v
            (algebraMap (NumberField.RingOfIntegers K) K c)).trans
            (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v c)
        have Vlt : ∀ c : NumberField.RingOfIntegers K, Valued.v (ι c) < 1 ↔ c ∈ v.asIdeal := by
          intro c; rw [V0 c]
          exact IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem v c
        have Vle : ∀ c : NumberField.RingOfIntegers K, Valued.v (ι c) ≤ 1 := by
          intro c; rw [V0 c]
          exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v c
        have HB : ∀ m : v.adicCompletion K, Valued.v m = 1 →
            ∀ a s : NumberField.RingOfIntegers K, Valued.v (m - ι a) < 1 →
            s ^ 2 - a ∈ v.asIdeal → IsSquare m := by
          intro m hm a s hma hs
          have hanm : a ∉ v.asIdeal := by
            intro hmem
            have h1 : Valued.v (ι a) < 1 := (Vlt a).mpr hmem
            have e : m = (m - ι a) + ι a := by ring
            have h3 : Valued.v m < 1 := by
              rw [e]; exact lt_of_le_of_lt (Valuation.map_add Valued.v _ _) (max_lt hma h1)
            rw [hm] at h3; exact lt_irrefl _ h3
          have hsnm : s ∉ v.asIdeal := by
            intro hmem
            apply hanm
            have e : a = s ^ 2 - (s ^ 2 - a) := by ring
            rw [e]
            exact Ideal.sub_mem _ (Ideal.pow_mem_of_mem _ hmem 2 (by norm_num)) hs
          have hs1 : Valued.v (ι s) = 1 := by
            rcases lt_or_eq_of_le (Vle s) with h | h
            · exact absurd ((Vlt s).mp h) hsnm
            · exact h
          have hd : Valued.v (m - (ι s) ^ 2) < 1 := by
            have e : m - (ι s) ^ 2 = (m - ι a) - ι (s ^ 2 - a) := by
              rw [map_sub, map_pow]; ring
            have h1 : Valued.v (ι (s ^ 2 - a)) < 1 := (Vlt _).mpr hs
            rw [e]
            exact lt_of_le_of_lt (Valuation.map_sub Valued.v _ _) (max_lt hma h1)
          obtain ⟨x, hx⟩ := h_hensel m (ι s) hs1 hd
          exact ⟨x, by rw [← sq]; exact hx.symm⟩
        have core : ∀ (F : Type u) [Field F] [Finite F] (x y : F),
            ¬ IsSquare x → ¬ IsSquare y → IsSquare (x * y) := by
          intro F _ _ x y hx hy
          letI : Fintype F := Fintype.ofFinite F
          letI : DecidableEq F := Classical.decEq F
          by_contra hxy
          have e1 : quadraticChar F x = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hx
          have e2 : quadraticChar F y = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hy
          have e3 : quadraticChar F (x * y) = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hxy
          rw [map_mul, e1, e2] at e3
          norm_num at e3
        obtain ⟨a, haU⟩ := h_approx u (le_of_eq hu)
        obtain ⟨b, hbW⟩ := h_approx w (le_of_eq hw)
        have hib : Valued.v (ι b) = 1 := by
          rcases lt_or_eq_of_le (Vle b) with h | h
          · exfalso
            have e : w = ι b + (w - ι b) := by ring
            have h3 : Valued.v w < 1 := by
              rw [e]; exact lt_of_le_of_lt (Valuation.map_add Valued.v _ _) (max_lt h hbW)
            rw [hw] at h3; exact lt_irrefl _ h3
          · exact h
        letI : Field (NumberField.RingOfIntegers K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
        have hnsq_a : ¬ IsSquare (Ideal.Quotient.mk v.asIdeal a) := by
          rintro ⟨y, hy⟩
          obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
          refine hu_sq (HB u hu a s haU ?_)
          rw [← Ideal.Quotient.eq_zero_iff_mem]
          have hy' : Ideal.Quotient.mk v.asIdeal a =
              Ideal.Quotient.mk v.asIdeal s * Ideal.Quotient.mk v.asIdeal s := hy
          rw [map_sub, map_pow, hy']; ring
        have hnsq_b : ¬ IsSquare (Ideal.Quotient.mk v.asIdeal b) := by
          rintro ⟨y, hy⟩
          obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
          refine hw_nsq (HB w hw b s hbW ?_)
          rw [← Ideal.Quotient.eq_zero_iff_mem]
          have hy' : Ideal.Quotient.mk v.asIdeal b =
              Ideal.Quotient.mk v.asIdeal s * Ideal.Quotient.mk v.asIdeal s := hy
          rw [map_sub, map_pow, hy']; ring
        obtain ⟨y, hy⟩ := core (NumberField.RingOfIntegers K ⧸ v.asIdeal)
          (Ideal.Quotient.mk v.asIdeal a) (Ideal.Quotient.mk v.asIdeal b) hnsq_a hnsq_b
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
        have hsab : s ^ 2 - a * b ∈ v.asIdeal := by
          rw [← Ideal.Quotient.eq_zero_iff_mem]
          have hy' : Ideal.Quotient.mk v.asIdeal a * Ideal.Quotient.mk v.asIdeal b =
              Ideal.Quotient.mk v.asIdeal s * Ideal.Quotient.mk v.asIdeal s := hy
          rw [map_sub, map_pow, map_mul, hy']; ring
        have hmw : Valued.v (u * w) = 1 := by rw [Valuation.map_mul, hu, hw, one_mul]
        have hmab : Valued.v (u * w - ι (a * b)) < 1 := by
          have e : u * w - ι a * ι b = u * (w - ι b) + ι b * (u - ι a) := by ring
          have h1 : Valued.v (u * (w - ι b)) < 1 := by rw [Valuation.map_mul, hu, one_mul]; exact hbW
          have h3 : Valued.v (ι b * (u - ι a)) < 1 := by rw [Valuation.map_mul, hib, one_mul]; exact haU
          rw [map_mul ι a b, e]
          exact lt_of_le_of_lt (Valuation.map_add Valued.v _ _) (max_lt h1 h3)
        exact HB (u * w) hmw (a * b) s hmab hsab
  have s5 : ∃ ϖ : v.adicCompletion K,
      Valued.v ϖ = WithZero.exp (-1 : ℤ) ∧
      ∀ x : v.adicCompletion K, x ≠ 0 →
        ∃ z u : v.adicCompletion K, z ≠ 0 ∧ Valued.v u = 1 ∧
          (x = z ^ 2 * u ∨ x = z ^ 2 * (ϖ * u)) := by
    obtain ⟨π₀, hπ₀⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer K v
    let ϖ : v.adicCompletion K := algebraMap K (v.adicCompletion K) π₀
    have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) :=
      (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π₀).trans hπ₀
    have hϖ0 : ϖ ≠ 0 := by
      intro h; rw [h, Valuation.map_zero] at hϖ; exact WithZero.coe_ne_zero hϖ.symm
    refine ⟨ϖ, hϖ, ?_⟩
    intro x hx
    have hvx : Valued.v x ≠ 0 := fun h => hx ((Valuation.zero_iff _).mp h)
    obtain ⟨k, hexp⟩ : ∃ k : ℤ, WithZero.exp k = Valued.v x :=
      ⟨(Valued.v x).log, WithZero.exp_log hvx⟩
    have hvpow : Valued.v (ϖ ^ (-k)) = Valued.v x := by
      have h2' : ((-k : ℤ)) • (-1 : ℤ) = k := by simp
      calc Valued.v (ϖ ^ (-k)) = Valued.v ϖ ^ (-k) := map_zpow₀ _ _ _
        _ = WithZero.exp (-1 : ℤ) ^ (-k) := by rw [hϖ]
        _ = WithZero.exp ((-k : ℤ) • (-1 : ℤ)) := (WithZero.exp_zsmul _ _).symm
        _ = WithZero.exp k := by rw [h2']
        _ = Valued.v x := hexp
    let u : v.adicCompletion K := x / ϖ ^ (-k)
    have hu : Valued.v u = 1 := by
      change Valued.v (x / ϖ ^ (-k)) = 1
      rw [Valuation.map_div, hvpow, div_self hvx]
    have hx_eq : x = ϖ ^ (-k) * u := (mul_div_cancel₀ x (zpow_ne_zero _ hϖ0)).symm
    rcases Int.even_or_odd (-k) with ⟨r, hr⟩ | ⟨r, hr⟩
    · refine ⟨ϖ ^ r, u, zpow_ne_zero r hϖ0, hu, Or.inl ?_⟩
      rw [hx_eq, hr, zpow_add₀ hϖ0, ← sq]
    · refine ⟨ϖ ^ r, u, zpow_ne_zero r hϖ0, hu, Or.inr ?_⟩
      have hrr : 2 * r + 1 = (r + r) + 1 := by ring
      rw [hx_eq, hr, hrr, zpow_add₀ hϖ0, zpow_add₀ hϖ0, zpow_one, ← sq, mul_assoc]
  obtain ⟨ϖ, hϖ, hdecomp⟩ := s5
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, Valuation.map_zero] at hϖ; exact WithZero.coe_ne_zero hϖ.symm
  have s4 : ∀ (u w : v.adicCompletion K),
      Valued.v u = 1 → Valued.v w = 1 →
      ¬ IsSquare (ϖ * u) ∧
      (hilbLoc v u (ϖ * w) = 1 ↔ IsSquare u) := by
    intro u w hu hw
    have h_parity : ∀ (m y z : v.adicCompletion K),
        Valued.v m = WithZero.exp (-1 : ℤ) → z ≠ 0 →
        Valued.v (m * y ^ 2) ≠ Valued.v z ^ 2 := by
      intro m y z hm hz heq
      have hvz : Valued.v z ≠ 0 := fun h => hz ((Valuation.zero_iff _).mp h)
      have hvy : Valued.v y ≠ 0 := by
        intro h
        rw [Valuation.map_mul, Valuation.map_pow, h, zero_pow (by norm_num), mul_zero] at heq
        exact pow_ne_zero 2 hvz heq.symm
      obtain ⟨a, ha⟩ : ∃ a : ℤ, WithZero.exp a = Valued.v y :=
        ⟨(Valued.v y).log, WithZero.exp_log hvy⟩
      obtain ⟨b, hb⟩ : ∃ b : ℤ, WithZero.exp b = Valued.v z :=
        ⟨(Valued.v z).log, WithZero.exp_log hvz⟩
      rw [Valuation.map_mul, Valuation.map_pow, hm, ← ha, ← hb, sq, sq,
        ← WithZero.exp_add, ← WithZero.exp_add, ← WithZero.exp_add, WithZero.exp_inj] at heq
      omega
    have h_unit_unif : ∀ (u' w' : v.adicCompletion K),
        Valued.v u' = 1 → Valued.v w' = 1 →
        (hilbLoc v u' (ϖ * w') = 1 ↔ IsSquare u') := by
      intro u' w' hu' hw'
      constructor
      · intro hhilb
        have hsol : ∃ x y : v.adicCompletion K, u' * x ^ 2 + (ϖ * w') * y ^ 2 = 1 := by
          simp only [hilbLoc] at hhilb
          split_ifs at hhilb with h
          · exact h
          · exfalso; revert hhilb; decide
        rcases hsol with ⟨x, y, hxy⟩
        have hm : Valued.v (ϖ * w') = WithZero.exp (-1 : ℤ) := by
          rw [Valuation.map_mul, hϖ, hw', mul_one]
        have hmy : (ϖ * w') * y ^ 2 = 1 - u' * x ^ 2 := by linear_combination hxy
        have hvx : Valued.v x = 1 := by
          rcases lt_trichotomy (Valued.v x) 1 with hlt | heq | hgt
          · exfalso
            refine h_parity (ϖ * w') y 1 hm one_ne_zero ?_
            have hux : Valued.v (u' * x ^ 2) < Valued.v (1 : v.adicCompletion K) := by
              rw [Valuation.map_mul, hu', one_mul, Valuation.map_pow, Valuation.map_one]
              exact pow_lt_one₀ zero_le' hlt (by norm_num)
            rw [hmy, Valuation.map_sub_eq_of_lt_left _ hux, Valuation.map_one, one_pow]
          · exact heq
          · exfalso
            have hx0 : x ≠ 0 := by
              rintro rfl; rw [Valuation.map_zero] at hgt; exact not_lt_of_ge zero_le' hgt
            refine h_parity (ϖ * w') y x hm hx0 ?_
            have hux : Valued.v (1 : v.adicCompletion K) < Valued.v (u' * x ^ 2) := by
              rw [Valuation.map_mul, hu', one_mul, Valuation.map_pow, Valuation.map_one]
              exact one_lt_pow₀ hgt (by norm_num)
            rw [hmy, Valuation.map_sub_eq_of_lt_right _ hux, Valuation.map_mul, hu', one_mul,
              Valuation.map_pow]
        have hx0 : x ≠ 0 := by
          rintro rfl; rw [Valuation.map_zero] at hvx; exact zero_ne_one hvx
        have hmy_le : Valued.v ((ϖ * w') * y ^ 2) ≤ 1 := by
          rw [hmy]
          refine le_trans (Valuation.map_sub _ _ _) (max_le (by rw [Valuation.map_one]) ?_)
          rw [Valuation.map_mul, hu', Valuation.map_pow, hvx, one_pow, mul_one]
        have hmy_ne : Valued.v ((ϖ * w') * y ^ 2) ≠ 1 := by
          intro h1
          refine h_parity (ϖ * w') y 1 hm one_ne_zero ?_
          rw [h1, Valuation.map_one, one_pow]
        have hmy_lt : Valued.v ((ϖ * w') * y ^ 2) < 1 := lt_of_le_of_ne hmy_le hmy_ne
        have hxinv : Valued.v (x⁻¹) = 1 := by rw [map_inv₀, hvx, inv_one]
        have hdiff : u' - (x⁻¹) ^ 2 = -(((ϖ * w') * y ^ 2) / x ^ 2) := by
          field_simp [hx0]; linear_combination hxy
        have hdiff_lt : Valued.v (u' - (x⁻¹) ^ 2) < 1 := by
          rw [hdiff, Valuation.map_neg, Valuation.map_div, Valuation.map_pow, hvx, one_pow, div_one]
          exact hmy_lt
        obtain ⟨t, ht⟩ := h_hensel u' (x⁻¹) hxinv hdiff_lt
        exact ⟨t, by rw [← sq]; exact ht.symm⟩
      · rintro ⟨s, rfl⟩
        have hs0 : s ≠ 0 := by
          rintro rfl; rw [mul_zero, Valuation.map_zero] at hu'; exact zero_ne_one hu'
        simp only [hilbLoc]
        rw [if_pos ⟨s⁻¹, 0, by field_simp [hs0]; ring⟩]
    refine ⟨?_, h_unit_unif u w hu hw⟩
    rintro ⟨z, hz⟩
    have hvu : Valued.v (ϖ * u) = WithZero.exp (-1 : ℤ) := by
      rw [Valuation.map_mul, hϖ, hu, mul_one]
    have hz0 : z ≠ 0 := by
      rintro rfl; rw [mul_zero] at hz; rw [hz, Valuation.map_zero] at hvu
      exact WithZero.coe_ne_zero hvu.symm
    refine h_parity (ϖ * u) 1 z hvu hz0 ?_
    rw [one_pow, mul_one, hz, Valuation.map_mul, sq]
  let HasRep (x : v.adicCompletion K) (a b : Bool) : Prop :=
    ∃ z u : v.adicCompletion K, z ≠ 0 ∧ Valued.v u = 1 ∧
      (IsSquare u ↔ a = false) ∧
      x = z ^ 2 * (if b then ϖ * u else u)
  have exists_hasRep : ∀ x : v.adicCompletion K, x ≠ 0 → ∃ a b : Bool, HasRep x a b := by
    intro x hx
    obtain ⟨z, u, hz, hu, hxu | hxu⟩ := hdecomp x hx
    · exact ⟨!decide (IsSquare u), false, z, u, hz, hu, by simp, hxu⟩
    · exact ⟨!decide (IsSquare u), true, z, u, hz, hu, by simp, hxu⟩
  have hasRep_isSquare_iff : ∀ (x : v.adicCompletion K) (a b : Bool),
      HasRep x a b → (IsSquare x ↔ (a = false ∧ b = false)) := by
    rintro x a b ⟨z, u, hz, hu, hua, rfl⟩
    have hsq_scale : ∀ w : v.adicCompletion K, IsSquare (z ^ 2 * w) ↔ IsSquare w := by
      intro w; constructor
      · rintro ⟨s, hs⟩; refine ⟨s / z, ?_⟩; field_simp [hz]; linear_combination hs
      · rintro ⟨s, rfl⟩; refine ⟨z * s, ?_⟩; ring
    rw [hsq_scale]
    cases b
    · simp [hua]
    · simp [(s4 u u hu hu).1]
  have hasRep_mul : ∀ (x y : v.adicCompletion K) (ax bx ay by_ : Bool),
      HasRep x ax bx → HasRep y ay by_ → HasRep (x * y) (xor ax ay) (xor bx by_) := by
    rintro x y ax bx ay by_ ⟨zx, ux, hzx, hux, huax, rfl⟩ ⟨zy, uy, hzy, huy, huay, rfl⟩
    refine ⟨if bx && by_ then zx * zy * ϖ else zx * zy, ux * uy, ?_, ?_, ?_, ?_⟩
    · split_ifs
      · exact mul_ne_zero (mul_ne_zero hzx hzy) hϖ0
      · exact mul_ne_zero hzx hzy
    · rw [Valuation.map_mul, hux, huy, one_mul]
    · rw [s3 ux uy hux huy, huax, huay]
      cases ax <;> cases ay <;> decide
    · cases bx <;> cases by_ <;> simp <;> ring
  have hasRep_unique : ∀ (x : v.adicCompletion K) (a₁ b₁ a₂ b₂ : Bool),
      HasRep x a₁ b₁ → HasRep x a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂ := by
    intro x a₁ b₁ a₂ b₂ h1 h2
    have hmul := hasRep_mul x x a₁ b₁ a₂ b₂ h1 h2
    have hsq : IsSquare (x * x) := ⟨x, rfl⟩
    have hab := (hasRep_isSquare_iff (x * x) (xor a₁ a₂) (xor b₁ b₂) hmul).mp hsq
    cases a₁ <;> cases b₁ <;> cases a₂ <;> cases b₂ <;> revert hab <;> decide
  have hasRep_evenVal_iff : ∀ (x : Kˣ) (a b : Bool),
      HasRep (algebraMap K (v.adicCompletion K) (x : K)) a b → (EvenVal v x ↔ b = false) := by
    rintro x a b ⟨z, u, hz, hu, -, hx_eq⟩
    have hvz : Valued.v z ≠ 0 := fun h => hz ((Valuation.zero_iff _).mp h)
    obtain ⟨m, hm⟩ : ∃ m : ℤ, WithZero.exp m = Valued.v z :=
      ⟨(Valued.v z).log, WithZero.exp_log hvz⟩
    let n : ℤ := Multiplicative.toAdd (v.valuationOfNeZero x)
    have hval_x : Valued.v (algebraMap K (v.adicCompletion K) (x : K)) = WithZero.exp n := by
      refine (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : K)).trans ?_
      rw [← IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq v x]
      have hn : v.valuationOfNeZero x = Multiplicative.ofAdd n := (ofAdd_toAdd _).symm
      rw [hn]
      rfl
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte] at hx_eq
      have hval_eq : Valued.v (algebraMap K (v.adicCompletion K) (x : K)) =
          Valued.v (z ^ 2 * u) := congr_arg Valued.v hx_eq
      rw [hval_x, Valuation.map_mul, sq, Valuation.map_mul, ← hm, hu, mul_one,
          ← WithZero.exp_add] at hval_eq
      have hn_eq : n = m + m := WithZero.exp_inj.mp hval_eq
      simp only [EvenVal, iff_true]
      exact ⟨m, hn_eq⟩
    · simp only [↓reduceIte] at hx_eq
      have hval_eq : Valued.v (algebraMap K (v.adicCompletion K) (x : K)) =
          Valued.v (z ^ 2 * (ϖ * u)) := congr_arg Valued.v hx_eq
      rw [hval_x, Valuation.map_mul, sq, Valuation.map_mul, Valuation.map_mul, ← hm, hϖ, hu, mul_one,
          ← WithZero.exp_add, ← WithZero.exp_add] at hval_eq
      have hn_eq : n = m + m + -1 := WithZero.exp_inj.mp hval_eq
      simp only [EvenVal, Bool.true_eq_false, iff_false]
      rintro ⟨k, hk⟩
      change n = k + k at hk
      omega
  have hilbLoc_symm : ∀ (p q : v.adicCompletion K), hilbLoc v p q = hilbLoc v q p := by
    intro p q
    simp only [hilbLoc]
    congr 1
    exact propext ⟨fun ⟨x, y, hxy⟩ => ⟨y, x, by linear_combination hxy⟩,
      fun ⟨x, y, hxy⟩ => ⟨y, x, by linear_combination hxy⟩⟩
  have hilbLoc_scale_left : ∀ (z p q : v.adicCompletion K), z ≠ 0 →
      hilbLoc v (z ^ 2 * p) q = hilbLoc v p q := by
    intro z p q hz
    simp only [hilbLoc]
    congr 1
    refine propext ⟨?_, ?_⟩
    · rintro ⟨x, y, hxy⟩
      refine ⟨z * x, y, ?_⟩
      linear_combination hxy
    · rintro ⟨x, y, hxy⟩
      refine ⟨x / z, y, ?_⟩
      field_simp [hz]
      linear_combination hxy
  have hilbLoc_eq_iff : ∀ (p q : v.adicCompletion K) (b : Bool),
      (hilbLoc v p q = 1 ↔ b = false) →
      hilbLoc v p q = (if b then (-1 : ℤˣ) else 1) := by
    intro p q b hb
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact hb.mpr rfl
    · simp only [↓reduceIte]
      have hne : hilbLoc v p q ≠ 1 := fun h => Bool.noConfusion (hb.mp h)
      simp only [hilbLoc] at hne ⊢
      split_ifs with h
      · exfalso; exact hne (if_pos h)
      · rfl
  have hasRep_hilbLoc_of_even : ∀ (x y : v.adicCompletion K) (ax ay by_ : Bool),
      HasRep x ax false → HasRep y ay by_ →
      hilbLoc v x y = (if (ax && by_) then (-1 : ℤˣ) else 1) := by
    rintro x y ax ay by_ ⟨zx, ux, hzx, hux, huax, rfl⟩ ⟨zy, uy, hzy, huy, huay, rfl⟩
    rw [hilbLoc_scale_left zx _ _ hzx, hilbLoc_symm, hilbLoc_scale_left zy _ _ hzy, hilbLoc_symm]
    apply hilbLoc_eq_iff
    cases by_
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_false]
      rw [s2 ux uy hux huy]
      simp
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_true]
      rw [(s4 ux uy hux huy).2, huax]
  let ι (u : Kˣ) : v.adicCompletion K := algebraMap K (v.adicCompletion K) (u : K)
  have unit_map_ne_zero : ∀ u : Kˣ, ι u ≠ 0 := by
    intro u
    change algebraMap K (v.adicCompletion K) (u : K) ≠ 0
    rw [ne_eq, map_eq_zero]
    exact u.ne_zero
  choose a_v b_v h_rep_v using fun (u : Kˣ) => exists_hasRep (ι u) (unit_map_ne_zero u)
  have h_ab_mul : ∀ u w : Kˣ,
      a_v (u * w) = xor (a_v u) (a_v w) ∧ b_v (u * w) = xor (b_v u) (b_v w) := by
    intro u w
    have h1 : HasRep (ι (u * w)) (a_v (u * w)) (b_v (u * w)) := h_rep_v (u * w)
    have h2 : HasRep (ι u * ι w) (xor (a_v u) (a_v w)) (xor (b_v u) (b_v w)) :=
      hasRep_mul (ι u) (ι w) (a_v u) (b_v u) (a_v w) (b_v w) (h_rep_v u) (h_rep_v w)
    have heq : ι (u * w) = ι u * ι w := by
      change algebraMap K (v.adicCompletion K) ((u * w : Kˣ) : K) = _
      rw [Units.val_mul, map_mul]
    rw [heq] at h1
    exact hasRep_unique _ _ _ _ _ h1 h2
  have h_sq_mul_iff : ∀ u w : Kˣ,
      IsSquare (algebraMap K (v.adicCompletion K) ((u * w : Kˣ) : K)) ↔
        (a_v u = a_v w ∧ b_v u = b_v w) := by
    intro u w
    have h2 : HasRep (algebraMap K (v.adicCompletion K) ((u * w : Kˣ) : K))
        (xor (a_v u) (a_v w)) (xor (b_v u) (b_v w)) := by
      rw [Units.val_mul, map_mul]
      exact hasRep_mul (ι u) (ι w) (a_v u) (b_v u) (a_v w) (b_v w) (h_rep_v u) (h_rep_v w)
    rw [hasRep_isSquare_iff _ _ _ h2]
    generalize a_v u = au, a_v w = aw, b_v u = bu, b_v w = bw
    revert au aw bu bw
    decide
  have h_ab_sq_K : ∀ u w : Kˣ, IsSquare ((u : K) * (w : K)) → a_v u = a_v w ∧ b_v u = b_v w := by
    intro u w hsq
    refine (h_sq_mul_iff u w).mp ?_
    rw [Units.val_mul]
    exact hsq.map (algebraMap K (v.adicCompletion K))
  have h_even_iff : ∀ u : Kˣ, EvenVal v u ↔ b_v u = false :=
    fun u => hasRep_evenVal_iff u (a_v u) (b_v u) (h_rep_v u)
  let b2z (b : Bool) : ZMod 2 := if b then 1 else 0
  let φ_v : Kˣ × Kˣ → (Fin 2 → ZMod 2) :=
    fun p i => if i = 0 then b2z (b_v p.2) else b2z (b_v p.1)
  let ψ_v : Kˣ × Kˣ → (Fin 2 → ZMod 2) :=
    fun q i => if i = 0 then b2z (a_v q.1) else b2z (a_v q.2)
  have b2z_xor : ∀ b₁ b₂ : Bool, b2z (xor b₁ b₂) = b2z b₁ + b2z b₂ := by decide
  have b2z_eq_zero_iff : ∀ b : Bool, b2z b = 0 ↔ b = false := by decide
  have b2z_inj : ∀ b₁ b₂ : Bool, b2z b₁ = b2z b₂ ↔ b₁ = b₂ := by decide
  have vec2_eq_zero_iff : ∀ x y : Bool,
      (fun i : Fin 2 => if i = 0 then b2z x else b2z y) = 0 ↔ (x = false ∧ y = false) := by
    intro x y
    constructor
    · intro h
      have h0 : b2z x = 0 := by simpa using congr_fun h 0
      have h1 : b2z y = 0 := by simpa using congr_fun h 1
      exact ⟨(b2z_eq_zero_iff x).mp h0, (b2z_eq_zero_iff y).mp h1⟩
    · rintro ⟨rfl, rfl⟩
      ext i
      fin_cases i <;> rfl
  have vec2_eq_iff : ∀ x₁ y₁ x₂ y₂ : Bool,
      (fun i : Fin 2 => if i = 0 then b2z x₁ else b2z y₁) =
      (fun i : Fin 2 => if i = 0 then b2z x₂ else b2z y₂) ↔ (x₁ = x₂ ∧ y₁ = y₂) := by
    intro x₁ y₁ x₂ y₂
    constructor
    · intro h
      have h0 : b2z x₁ = b2z x₂ := by simpa using congr_fun h 0
      have h1 : b2z y₁ = b2z y₂ := by simpa using congr_fun h 1
      exact ⟨(b2z_inj x₁ x₂).mp h0, (b2z_inj y₁ y₂).mp h1⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  refine ⟨φ_v, ψ_v, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q hpq1 hpq2
    dsimp [φ_v]
    rw [(h_ab_sq_K p.1 q.1 hpq1).2, (h_ab_sq_K p.2 q.2 hpq2).2]
  · intro p q
    ext i
    fin_cases i <;> simp [φ_v, (h_ab_mul p.1 q.1).2, (h_ab_mul p.2 q.2).2, b2z_xor]
  · intro p
    dsimp [φ_v]
    rw [vec2_eq_zero_iff, h_even_iff p.1, h_even_iff p.2, and_comm]
  · intro q₁ q₂ hq₁ hq₂ hψ
    dsimp [φ_v] at hq₁ hq₂
    dsimp [ψ_v] at hψ
    rw [vec2_eq_zero_iff] at hq₁ hq₂
    rw [vec2_eq_iff] at hψ
    rw [h_sq_mul_iff q₁.1 q₂.1, h_sq_mul_iff q₁.2 q₂.2]
    exact ⟨⟨hψ.1, hq₁.2.trans hq₂.2.symm⟩, ⟨hψ.2, hq₁.1.trans hq₂.1.symm⟩⟩
  · intro q p hq
    dsimp [φ_v] at hq
    rw [vec2_eq_zero_iff] at hq
    have hrep_q1 : HasRep (ι q.1) (a_v q.1) false := by
      rw [← hq.2]; exact h_rep_v q.1
    have hrep_q2 : HasRep (ι q.2) (a_v q.2) false := by
      rw [← hq.1]; exact h_rep_v q.2
    change hilbLoc v (ι q.1) (ι p.2) * hilbLoc v (ι q.2) (ι p.1) = _
    rw [hasRep_hilbLoc_of_even (ι q.1) (ι p.2) (a_v q.1) (a_v p.2) (b_v p.2) hrep_q1 (h_rep_v p.2),
        hasRep_hilbLoc_of_even (ι q.2) (ι p.1) (a_v q.2) (a_v p.1) (b_v p.1) hrep_q2 (h_rep_v p.1)]
    have hdot : dotProduct (ψ_v q) (φ_v p) =
        b2z (a_v q.1) * b2z (b_v p.2) + b2z (a_v q.2) * b2z (b_v p.1) := by
      simp [dotProduct, Fin.sum_univ_two, ψ_v, φ_v]
    rw [hdot]
    have h_pair_bool : ∀ (aq1 aq2 bp1 bp2 : Bool),
        (if (aq1 && bp2) then (-1 : ℤˣ) else 1) *
          (if (aq2 && bp1) then (-1 : ℤˣ) else 1) =
        (-1 : ℤˣ) ^ (b2z aq1 * b2z bp2 + b2z aq2 * b2z bp1).val := by
      decide
    exact h_pair_bool (a_v q.1) (a_v q.2) (b_v p.1) (b_v p.2)

theorem local_selmer_basis_outside_T {K : Type u} [Field K] [NumberField K]
    (a₁ a₂ a₃ : K) (h₁₂ : a₁ ≠ a₂) (h₁₃ : a₁ ≠ a₃) (h₂₃ : a₂ ≠ a₃)
    (hint₁ : IsIntegral ℤ a₁) (hint₂ : IsIntegral ℤ a₂) (hint₃ : IsIntegral ℤ a₃)
    (T S S_out : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hT : IsGoodT a₁ a₂ a₃ T) (hS : S ⊆ S_out) (hdisj : Disjoint S_out T)
    (π : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        v.adicCompletion K)
    (hπ : ∀ v ∈ S, IsLocalUnif v (π v)) :
    ∃ (Φ_out Ψ_out : Kˣ × Kˣ → (Fin (NumberField.InfinitePlace.nrRealPlaces K + 2 * S_out.card) → ZMod 2)),
      (∀ p q : Kˣ × Kˣ,
        IsSquare ((p.1 : K) * (q.1 : K)) → IsSquare ((p.2 : K) * (q.2 : K)) →
        Φ_out p = Φ_out q) ∧
      (∀ p q : Kˣ × Kˣ, Φ_out (p.1 * q.1, p.2 * q.2) = Φ_out p + Φ_out q) ∧
      (∀ p : Kˣ × Kˣ, Φ_out p = 0 ↔
        (∀ w : NumberField.InfinitePlace K, IsDescentClass
          (algebraMap K w.Completion a₁) (algebraMap K w.Completion a₂) (algebraMap K w.Completion a₃)
          (algebraMap K w.Completion (p.1 : K)) (algebraMap K w.Completion (p.2 : K))) ∧
        (∀ v ∈ S, RamLocal a₁ a₂ a₃ v (π v) p.1 p.2) ∧
        (∀ v ∈ S_out, v ∉ S → EvenVal v p.1 ∧ EvenVal v p.2)) ∧
      (∀ q₁ q₂ : Kˣ × Kˣ, Φ_out q₁ = 0 → Φ_out q₂ = 0 → Ψ_out q₁ = Ψ_out q₂ →
        (∀ v ∈ S_out,
          IsSquare (algebraMap K (v.adicCompletion K) ((q₁.1 * q₂.1 : Kˣ) : K)) ∧
          IsSquare (algebraMap K (v.adicCompletion K) ((q₁.2 * q₂.2 : Kˣ) : K))) ∧
        (∀ w : NumberField.InfinitePlace K,
          IsSquare (algebraMap K w.Completion ((q₁.1 * q₂.1 : Kˣ) : K)) ∧
          IsSquare (algebraMap K w.Completion ((q₁.2 * q₂.2 : Kˣ) : K)))) ∧
      (∀ q p : Kˣ × Kˣ, Φ_out q = 0 →
        (∏ v ∈ S_out, (hilbFin v (q.1 : K) (p.2 : K) * hilbFin v (q.2 : K) (p.1 : K))) *
        (∏ w : NumberField.InfinitePlace K, (hilbInf w (q.1 : K) (p.2 : K) * hilbInf w (q.2 : K) (p.1 : K))) =
          (-1 : ℤˣ) ^ (dotProduct (Ψ_out q) (Φ_out p)).val) :=
by
  classical
  obtain ⟨Φ_inf, Ψ_inf, hΦ_inf_sq, hΦ_inf_mul, hΦ_inf_zero, hΨ_inf_inj, hΦ_inf_pair⟩ :=
    archimedean_selmer_basis a₁ a₂ a₃ h₁₂ h₁₃ h₂₃
  have hv_not_T : ∀ v : S_out, v.1 ∉ T := fun v => Finset.disjoint_left.mp hdisj v.2
  have h_loc_exists : ∀ v : S_out,
      ∃ (φ_v ψ_v : Kˣ × Kˣ → (Fin 2 → ZMod 2)),
        (∀ p q : Kˣ × Kˣ,
          IsSquare ((p.1 : K) * (q.1 : K)) → IsSquare ((p.2 : K) * (q.2 : K)) →
          φ_v p = φ_v q) ∧
        (∀ p q : Kˣ × Kˣ, φ_v (p.1 * q.1, p.2 * q.2) = φ_v p + φ_v q) ∧
        (∀ p : Kˣ × Kˣ, φ_v p = 0 ↔
          if v.1 ∈ S then RamLocal a₁ a₂ a₃ v.1 (π v.1) p.1 p.2
          else (EvenVal v.1 p.1 ∧ EvenVal v.1 p.2)) ∧
        (∀ q₁ q₂ : Kˣ × Kˣ, φ_v q₁ = 0 → φ_v q₂ = 0 → ψ_v q₁ = ψ_v q₂ →
          IsSquare (algebraMap K (v.1.adicCompletion K) ((q₁.1 * q₂.1 : Kˣ) : K)) ∧
          IsSquare (algebraMap K (v.1.adicCompletion K) ((q₁.2 * q₂.2 : Kˣ) : K))) ∧
        (∀ q p : Kˣ × Kˣ, φ_v q = 0 →
          hilbFin v.1 (q.1 : K) (p.2 : K) * hilbFin v.1 (q.2 : K) (p.1 : K) =
            (-1 : ℤˣ) ^ (dotProduct (ψ_v q) (φ_v p)).val) := by
    intro v
    by_cases hvS : v.1 ∈ S
    · obtain ⟨φ_v, ψ_v, h1, h2, h3, h4, h5⟩ :=
        ramLocal_selmer_basis_at_v a₁ a₂ a₃ h₁₂ h₁₃ h₂₃ hint₁ hint₂ hint₃ T hT
          v.1 (hv_not_T v) (π v.1) (hπ v.1 hvS)
      refine ⟨φ_v, ψ_v, h1, h2, fun p => ?_, h4, h5⟩
      rw [if_pos hvS]
      exact h3 p
    · obtain ⟨φ_v, ψ_v, h1, h2, h3, h4, h5⟩ :=
        evenVal_selmer_basis_at_v a₁ a₂ a₃ h₁₂ h₁₃ h₂₃ hint₁ hint₂ hint₃ T hT
          v.1 (hv_not_T v)
      refine ⟨φ_v, ψ_v, h1, h2, fun p => ?_, h4, h5⟩
      rw [if_neg hvS]
      exact h3 p
  choose φ_loc ψ_loc hφ_sq hφ_mul hφ_zero hψ_inj hφ_pair using h_loc_exists
  let e_fin : Fin 2 × S_out ≃ Fin (2 * S_out.card) :=
    ((Equiv.refl (Fin 2)).prodCongr S_out.equivFin).trans finProdFinEquiv
  let Φ_fin : Kˣ × Kˣ → (Fin (2 * S_out.card) → ZMod 2) :=
    fun p k => φ_loc (e_fin.symm k).2 p (e_fin.symm k).1
  let Ψ_fin : Kˣ × Kˣ → (Fin (2 * S_out.card) → ZMod 2) :=
    fun q k => ψ_loc (e_fin.symm k).2 q (e_fin.symm k).1
  let Φ_out : Kˣ × Kˣ → (Fin (NumberField.InfinitePlace.nrRealPlaces K + 2 * S_out.card) → ZMod 2) :=
    fun p => Fin.append (Φ_inf p) (Φ_fin p)
  let Ψ_out : Kˣ × Kˣ → (Fin (NumberField.InfinitePlace.nrRealPlaces K + 2 * S_out.card) → ZMod 2) :=
    fun q => Fin.append (Ψ_inf q) (Ψ_fin q)
  have h_append_eq : ∀ {m n : ℕ} (a₁ a₂ : Fin m → ZMod 2) (b₁ b₂ : Fin n → ZMod 2),
      Fin.append a₁ b₁ = Fin.append a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
    intro m n a₁ a₂ b₁ b₂
    constructor
    · intro h
      refine ⟨funext fun i => ?_, funext fun j => ?_⟩
      · simpa only [Fin.append_left] using congr_fun h (Fin.castAdd n i)
      · simpa only [Fin.append_right] using congr_fun h (Fin.natAdd m j)
    · rintro ⟨rfl, rfl⟩
      rfl
  have h_append_zero : ∀ {m n : ℕ} (a : Fin m → ZMod 2) (b : Fin n → ZMod 2),
      Fin.append a b = 0 ↔ a = 0 ∧ b = 0 := by
    intro m n a b
    have h0 : (0 : Fin (m + n) → ZMod 2) = Fin.append (0 : Fin m → ZMod 2) (0 : Fin n → ZMod 2) := by
      ext idx
      refine Fin.addCases (fun i => ?_) (fun j => ?_) idx
      · simp only [Fin.append_left, Pi.zero_apply]
      · simp only [Fin.append_right, Pi.zero_apply]
    rw [h0, h_append_eq]
  have hΦ_fin_zero : ∀ p : Kˣ × Kˣ, Φ_fin p = 0 ↔ ∀ v : S_out, φ_loc v p = 0 := by
    intro p
    constructor
    · intro h v
      ext i
      have hk := congr_fun h (e_fin (i, v))
      simpa only [Φ_fin, Equiv.symm_apply_apply, Pi.zero_apply] using hk
    · intro h
      ext k
      simp only [Φ_fin, h (e_fin.symm k).2, Pi.zero_apply]
  have hΨ_fin_eq : ∀ q₁ q₂ : Kˣ × Kˣ, Ψ_fin q₁ = Ψ_fin q₂ → ∀ v : S_out, ψ_loc v q₁ = ψ_loc v q₂ := by
    intro q₁ q₂ h v
    ext i
    have hk := congr_fun h (e_fin (i, v))
    simpa only [Ψ_fin, Equiv.symm_apply_apply] using hk
  refine ⟨Φ_out, Ψ_out, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q hp1 hp2
    dsimp [Φ_out]
    rw [h_append_eq]
    refine ⟨hΦ_inf_sq p q hp1 hp2, ?_⟩
    ext k
    simp only [Φ_fin, hφ_sq (e_fin.symm k).2 p q hp1 hp2]
  · intro p q
    ext idx
    refine Fin.addCases (fun i => ?_) (fun k => ?_) idx
    · simp only [Φ_out, Pi.add_apply, Fin.append_left, hΦ_inf_mul p q]
    · simp only [Φ_out, Pi.add_apply, Fin.append_right, Φ_fin, hφ_mul (e_fin.symm k).2 p q]
  · intro p
    dsimp [Φ_out]
    rw [h_append_zero, hΦ_inf_zero, hΦ_fin_zero]
    apply and_congr_right
    intro _
    constructor
    · intro h
      refine ⟨fun v hvS => ?_, fun v hvS_out hvS => ?_⟩
      · have hv := (hφ_zero ⟨v, hS hvS⟩ p).mp (h ⟨v, hS hvS⟩)
        rwa [if_pos hvS] at hv
      · have hv := (hφ_zero ⟨v, hvS_out⟩ p).mp (h ⟨v, hvS_out⟩)
        rwa [if_neg hvS] at hv
    · rintro ⟨h_ram, h_even⟩ ⟨v, hvS_out⟩
      rw [hφ_zero]
      split_ifs with hvS
      · exact h_ram v hvS
      · exact h_even v hvS_out hvS
  · intro q₁ q₂ hq₁ hq₂ hΨ
    dsimp [Φ_out] at hq₁ hq₂
    dsimp [Ψ_out] at hΨ
    rw [h_append_zero] at hq₁ hq₂
    rw [h_append_eq] at hΨ
    have hq₁_fin := (hΦ_fin_zero q₁).mp hq₁.2
    have hq₂_fin := (hΦ_fin_zero q₂).mp hq₂.2
    have hΨ_fin := hΨ_fin_eq q₁ q₂ hΨ.2
    refine ⟨fun v hv => hψ_inj ⟨v, hv⟩ q₁ q₂ (hq₁_fin ⟨v, hv⟩) (hq₂_fin ⟨v, hv⟩) (hΨ_fin ⟨v, hv⟩),
      hΨ_inf_inj q₁ q₂ hq₁.1 hq₂.1 hΨ.1⟩
  · intro q p hq
    dsimp [Φ_out] at hq
    rw [h_append_zero] at hq
    have hq_loc := (hΦ_fin_zero q).mp hq.2
    have h_dot_out : dotProduct (Ψ_out q) (Φ_out p) =
        dotProduct (Ψ_inf q) (Φ_inf p) + ∑ v ∈ S_out.attach, dotProduct (ψ_loc v q) (φ_loc v p) := by
      simp only [dotProduct, Ψ_out, Φ_out]
      rw [Fin.sum_univ_add]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Fin.append_left]
      · have h_right : (∑ k : Fin (2 * S_out.card),
            Fin.append (Ψ_inf q) (Ψ_fin q) (Fin.natAdd (NumberField.InfinitePlace.nrRealPlaces K) k) *
            Fin.append (Φ_inf p) (Φ_fin p) (Fin.natAdd (NumberField.InfinitePlace.nrRealPlaces K) k)) =
            ∑ k : Fin (2 * S_out.card), Ψ_fin q k * Φ_fin p k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [Fin.append_right]
        rw [h_right]
        have h_equiv : (∑ k : Fin (2 * S_out.card), Ψ_fin q k * Φ_fin p k) =
            ∑ x : Fin 2 × S_out, ψ_loc x.2 q x.1 * φ_loc x.2 p x.1 := by
          refine Fintype.sum_equiv e_fin.symm _ _ fun k => rfl
        rw [h_equiv, Fintype.sum_prod_type, Finset.sum_comm]
        rfl
    have neg_one_pow_val_add : ∀ x y : ZMod 2,
        (-1 : ℤˣ) ^ (x + y).val = (-1 : ℤˣ) ^ x.val * (-1 : ℤˣ) ^ y.val := by
      intro x y
      fin_cases x <;> fin_cases y <;> decide
    have neg_one_pow_val_sum : ∀ {α : Type u} (s : Finset α) (f : α → ZMod 2),
        (-1 : ℤˣ) ^ (∑ a ∈ s, f a).val = ∏ a ∈ s, (-1 : ℤˣ) ^ (f a).val := by
      intro α s f
      induction s using Finset.cons_induction with
      | empty => rfl
      | cons a s ha ih =>
        rw [Finset.sum_cons, Finset.prod_cons, neg_one_pow_val_add, ih]
    rw [h_dot_out, neg_one_pow_val_add, neg_one_pow_val_sum, ← hΦ_inf_pair q p hq.1, mul_comm]
    congr 1
    rw [← Finset.prod_attach S_out (fun v => hilbFin v (q.1 : K) (p.2 : K) * hilbFin v (q.2 : K) (p.1 : K))]
    refine Finset.prod_congr rfl fun v _ => ?_
    exact hφ_pair v q p (hq_loc v)

theorem dyadic_valuation_norm_sum_on_T {K : Type u} [Field K] [NumberField K]
    (a₁ a₂ a₃ : K) (h₁₂ : a₁ ≠ a₂) (h₁₃ : a₁ ≠ a₃) (h₂₃ : a₂ ≠ a₃)
    (hint₁ : IsIntegral ℤ a₁) (hint₂ : IsIntegral ℤ a₂) (hint₃ : IsIntegral ℤ a₃)
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hT : IsGoodT a₁ a₂ a₃ T) :
    ∃ (e k : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℕ),
      (∀ v, Valued.v (2 : v.adicCompletion K) = WithZero.exp (-(e v : ℤ))) ∧
      (∀ v, Nat.card (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (e v)) = 2 ^ (k v)) ∧
      (∑ v ∈ T, (2 + k v) = 2 * T.card + NumberField.InfinitePlace.nrRealPlaces K +
        2 * NumberField.InfinitePlace.nrComplexPlaces K) :=
by
  classical
  let I₂ : Ideal (NumberField.RingOfIntegers K) :=
    Ideal.span {(2 : NumberField.RingOfIntegers K)}
  let e : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℕ :=
    fun v => (Associates.mk v.asIdeal).count (Associates.mk I₂).factors
  have h2_ne_zero : (2 : NumberField.RingOfIntegers K) ≠ 0 := two_ne_zero
  have hval2 : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      v.intValuation (2 : NumberField.RingOfIntegers K) = WithZero.exp (-(e v : ℤ)) :=
    fun v => IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg v h2_ne_zero
  have he : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      Valued.v (2 : v.adicCompletion K) = WithZero.exp (-(e v : ℤ)) := by
    intro v
    have hval : ∀ k : K, Valued.v (algebraMap K (v.adicCompletion K) k) =
        IsDedekindDomain.HeightOneSpectrum.valuation K v k :=
      fun k => IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
    have hval_int : ∀ x : NumberField.RingOfIntegers K,
        IsDedekindDomain.HeightOneSpectrum.valuation K v
          (algebraMap (NumberField.RingOfIntegers K) K x) = v.intValuation x :=
      fun x => IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v x
    rw [← map_ofNat (algebraMap K (v.adicCompletion K)) 2, hval,
        ← map_ofNat (algebraMap (NumberField.RingOfIntegers K) K) 2, hval_int]
    exact hval2 v
  have he_zero : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      v ∉ T → e v = 0 := by
    intro v hvT
    have h2_val : IsDedekindDomain.HeightOneSpectrum.valuation K v (2 : K) = 1 := by
      let A₁ : NumberField.RingOfIntegers K := ⟨a₁, hint₁⟩
      let A₂ : NumberField.RingOfIntegers K := ⟨a₂, hint₂⟩
      let A₃ : NumberField.RingOfIntegers K := ⟨a₃, hint₃⟩
      let W : NumberField.RingOfIntegers K := 3 * (A₁ - A₂) * (A₁ - A₃) * (A₂ - A₃)
      have h2_le : IsDedekindDomain.HeightOneSpectrum.valuation K v (2 : K) ≤ 1 := by
        rw [← map_ofNat (algebraMap (NumberField.RingOfIntegers K) K) 2]
        exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one v 2
      have hW_le : IsDedekindDomain.HeightOneSpectrum.valuation K v
          (algebraMap (NumberField.RingOfIntegers K) K W) ≤ 1 :=
        IsDedekindDomain.HeightOneSpectrum.valuation_le_one v W
      have hprod_eq : 6 * (a₁ - a₂) * (a₁ - a₃) * (a₂ - a₃) =
          (2 : K) * algebraMap (NumberField.RingOfIntegers K) K W := by
        change 6 * (a₁ - a₂) * (a₁ - a₃) * (a₂ - a₃) =
          (2 : K) * algebraMap (NumberField.RingOfIntegers K) K (3 * (A₁ - A₂) * (A₁ - A₃) * (A₂ - A₃))
        simp only [map_mul, map_sub, map_ofNat]
        change 6 * (a₁ - a₂) * (a₁ - a₃) * (a₂ - a₃) = 2 * (3 * (a₁ - a₂) * (a₁ - a₃) * (a₂ - a₃))
        ring
      have hv_prod : IsDedekindDomain.HeightOneSpectrum.valuation K v
          (6 * (a₁ - a₂) * (a₁ - a₃) * (a₂ - a₃)) = 1 := by
        have h := (hT v).not.mp hvT
        push_neg at h
        exact h
      rw [hprod_eq, Valuation.map_mul] at hv_prod
      refine le_antisymm h2_le ?_
      calc (1 : WithZero (Multiplicative ℤ))
          = IsDedekindDomain.HeightOneSpectrum.valuation K v (2 : K) *
              IsDedekindDomain.HeightOneSpectrum.valuation K v (algebraMap (NumberField.RingOfIntegers K) K W) := hv_prod.symm
        _ ≤ IsDedekindDomain.HeightOneSpectrum.valuation K v (2 : K) * 1 :=
            mul_le_mul_right hW_le _
        _ = IsDedekindDomain.HeightOneSpectrum.valuation K v (2 : K) := mul_one _
    have hval_int : ∀ x : NumberField.RingOfIntegers K,
        IsDedekindDomain.HeightOneSpectrum.valuation K v
          (algebraMap (NumberField.RingOfIntegers K) K x) = v.intValuation x :=
      fun x => IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v x
    have hint_one : v.intValuation (2 : NumberField.RingOfIntegers K) = 1 := by
      rw [← hval_int 2, map_ofNat]
      exact h2_val
    have hexp : WithZero.exp (-(e v : ℤ)) = WithZero.exp (0 : ℤ) := by
      rw [← hval2 v, hint_one, WithZero.exp_zero]
    have hinj := WithZero.exp_inj.mp hexp
    omega
  have hI₂_ne : I₂ ≠ 0 := by
    simpa [I₂, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] using h2_ne_zero
  have hsupp : Function.mulSupport
      (fun v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
        v.maxPowDividing I₂) ⊆
      (T : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) := by
    intro v hv
    simp only [Function.mem_mulSupport] at hv
    by_contra hvT
    simp only [Finset.mem_coe] at hvT
    apply hv
    change v.asIdeal ^ (e v) = 1
    rw [he_zero v hvT, pow_zero]
  have hI₂_prod : I₂ = ∏ v ∈ T, v.asIdeal ^ (e v) := by
    calc I₂
        = ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
            v.maxPowDividing I₂ :=
          (Ideal.finprod_heightOneSpectrum_factorization hI₂_ne).symm
      _ = ∏ v ∈ T, v.maxPowDividing I₂ :=
          finprod_eq_prod_of_mulSupport_subset _ hsupp
      _ = ∏ v ∈ T, v.asIdeal ^ (e v) :=
          Finset.prod_congr rfl (fun v _ => rfl)
  let dK := NumberField.InfinitePlace.nrRealPlaces K +
    2 * NumberField.InfinitePlace.nrComplexPlaces K
  have hdK : Fintype.card (Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K)) = dK := by
    rw [← Module.finrank_eq_card_chooseBasisIndex ℤ (NumberField.RingOfIntegers K),
        NumberField.RingOfIntegers.rank K,
        ← NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K]
  have hnorm2 : Algebra.norm ℤ (2 : NumberField.RingOfIntegers K) = (2 : ℤ) ^ dK := by
    have h := Algebra.norm_algebraMap_of_basis
      (Module.Free.chooseBasis ℤ (NumberField.RingOfIntegers K)) (2 : ℤ)
    rw [map_ofNat, hdK] at h
    exact h
  have habsNorm_I₂ : Ideal.absNorm I₂ = 2 ^ dK := by
    dsimp [I₂]
    rw [Ideal.absNorm_span_singleton, hnorm2, Int.natAbs_pow]
    rfl
  have hprod_card :
      (∏ v ∈ T, Nat.card (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (e v))) = 2 ^ dK := by
    have h := congr_arg Ideal.absNorm hI₂_prod
    rw [habsNorm_I₂,
        map_prod (Ideal.absNorm : Ideal (NumberField.RingOfIntegers K) →*₀ ℕ)] at h
    rw [h]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hk_ex : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      ∃ kv : ℕ, Nat.card (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (e v)) = 2 ^ kv := by
    intro v
    by_cases hvT : v ∈ T
    · have hdvd : Nat.card (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (e v)) ∣ 2 ^ dK := by
        rw [← hprod_card]
        exact Finset.dvd_prod_of_mem _ hvT
      obtain ⟨kv, _, hkv⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      exact ⟨kv, hkv⟩
    · refine ⟨0, ?_⟩
      rw [he_zero v hvT, pow_zero, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
          map_one Ideal.absNorm, pow_zero]
  choose k hk using hk_ex
  have hpow_sum : 2 ^ (∑ v ∈ T, k v) = 2 ^ dK := by
    rw [← Finset.prod_pow_eq_pow_sum, ← hprod_card]
    exact Finset.prod_congr rfl (fun v _ => (hk v).symm)
  have hsum_k : ∑ v ∈ T, k v = dK :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow_sum
  have hsum : ∑ v ∈ T, (2 + k v) = 2 * T.card + NumberField.InfinitePlace.nrRealPlaces K +
      2 * NumberField.InfinitePlace.nrComplexPlaces K := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, hsum_k]
    dsimp [dK]
    ring
  exact ⟨e, k, he, hk, hsum⟩

theorem quotient_units_sqCl_coord {K : Type u} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (ev kv : ℕ)
    (hev : v.intValuation (2 : NumberField.RingOfIntegers K) = WithZero.exp (-(ev : ℤ)))
    (hkv : Nat.card (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ ev) = 2 ^ kv) :
    ∃ (φ_q : (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (2 * ev + 1))ˣ → (Fin (1 + kv) → ZMod 2)),
      (∀ a b : (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (2 * ev + 1))ˣ, φ_q (a * b) = φ_q a + φ_q b) ∧
      (∀ a : (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (2 * ev + 1))ˣ, φ_q a = 0 ↔ IsSquare a) ∧
      Function.Surjective φ_q :=
by
  classical
  let 𝓞_K := NumberField.RingOfIntegers K
  let R := 𝓞_K ⧸ v.asIdeal ^ (2 * ev + 1)
  let R₁ := 𝓞_K ⧸ v.asIdeal ^ (ev + 1)
  let R₀ := 𝓞_K ⧸ v.asIdeal ^ ev
  let A := Rˣ
  have hfinq : ∀ m : ℕ, Finite (𝓞_K ⧸ v.asIdeal ^ m) := fun m =>
    Ideal.finiteQuotientOfFreeOfNeBot (v.asIdeal ^ m) (pow_ne_zero m v.ne_bot)
  haveI : Finite R := hfinq (2 * ev + 1)
  haveI : Finite R₁ := hfinq (ev + 1)
  haveI : Finite R₀ := hfinq ev
  haveI : Finite A := inferInstance
  let sq : A →* A := powMonoidHom 2
  have hcard_A_range : Nat.card A = Nat.card (A ⧸ sq.range) * Nat.card sq.range :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup sq.range
  have hcard_A_ker : Nat.card A = Nat.card (A ⧸ sq.ker) * Nat.card sq.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup sq.ker
  have hiso_ker : Nat.card (A ⧸ sq.ker) = Nat.card sq.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange sq).toEquiv
  have hrange_pos : 0 < Nat.card sq.range := Nat.card_pos
  have hcard_quot_eq_ker : Nat.card (A ⧸ sq.range) = Nat.card sq.ker := by
    apply Nat.eq_of_mul_eq_mul_left hrange_pos
    calc Nat.card sq.range * Nat.card (A ⧸ sq.range)
      _ = Nat.card (A ⧸ sq.range) * Nat.card sq.range := Nat.mul_comm _ _
      _ = Nat.card A := hcard_A_range.symm
      _ = Nat.card (A ⧸ sq.ker) * Nat.card sq.ker := hcard_A_ker
      _ = Nat.card sq.range * Nat.card sq.ker := by rw [hiso_ker]
  have e_ker : sq.ker ≃ {x : R // x ^ 2 = 1} :=
    { toFun := fun a => ⟨(a.1 : R), by
        have ha : a.1 ^ 2 = 1 := MonoidHom.mem_ker.mp a.2
        rw [← Units.val_pow_eq_pow_val, ha, Units.val_one]⟩
      invFun := fun x =>
        let u : A := Units.mkOfMulEqOne x.1 x.1 (by rw [← pow_two]; exact x.2)
        ⟨u, by
          rw [MonoidHom.mem_ker]
          change u ^ 2 = 1
          ext
          exact x.2⟩
      left_inv := fun a => by
        ext
        rfl
      right_inv := fun x => by
        ext
        rfl }
  have hcard_quot_eq_sq1 : Nat.card (A ⧸ sq.range) = Nat.card {x : R // x ^ 2 = 1} :=
    hcard_quot_eq_ker.trans (Nat.card_congr e_ker)
  have hval_ge_of_not_mem : ∀ r : 𝓞_K, r ∉ v.asIdeal ^ (ev + 1) →
      WithZero.exp (-(ev : ℤ)) ≤ v.intValuation r := by
    intro r hr
    rw [← IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem] at hr
    revert hr
    refine WithZero.cases_on (v.intValuation r) ?_ ?_
    · intro hr
      exfalso
      exact hr (WithZero.zero_le _)
    · intro g hr
      have hg : (g : WithZero (Multiplicative ℤ)) = WithZero.exp (Multiplicative.toAdd g) := rfl
      rw [hg, WithZero.exp_le_exp] at hr ⊢
      omega
  have h2_mem : (2 : 𝓞_K) ∈ v.asIdeal ^ ev := by
    rw [← IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem, hev]
  have h2_not_mem : (2 : 𝓞_K) ∉ v.asIdeal ^ (ev + 1) := by
    rw [← IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem, hev, WithZero.exp_le_exp]
    omega
  have hle : v.asIdeal ^ (2 * ev + 1) ≤ v.asIdeal ^ (ev + 1) :=
    Ideal.pow_le_pow_right (by omega)
  let fac : R →+* R₁ := Ideal.Quotient.factor hle
  have hsq1_iff : ∀ x : R, x ^ 2 = 1 ↔ fac x = 1 ∨ fac x = -1 := by
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hfac_mk : fac (Ideal.Quotient.mk (v.asIdeal ^ (2 * ev + 1)) r) =
        Ideal.Quotient.mk (v.asIdeal ^ (ev + 1)) r :=
      Ideal.Quotient.factor_mk hle r
    rw [hfac_mk]
    have h1 : (Ideal.Quotient.mk (v.asIdeal ^ (2 * ev + 1)) r) ^ 2 = 1 ↔
        r ^ 2 - 1 ∈ v.asIdeal ^ (2 * ev + 1) := by
      rw [← map_pow, ← map_one (Ideal.Quotient.mk (v.asIdeal ^ (2 * ev + 1))), Ideal.Quotient.eq]
    have h2 : Ideal.Quotient.mk (v.asIdeal ^ (ev + 1)) r = 1 ↔
        r - 1 ∈ v.asIdeal ^ (ev + 1) := by
      rw [← map_one (Ideal.Quotient.mk (v.asIdeal ^ (ev + 1))), Ideal.Quotient.eq]
    have h3 : Ideal.Quotient.mk (v.asIdeal ^ (ev + 1)) r = -1 ↔
        r + 1 ∈ v.asIdeal ^ (ev + 1) := by
      rw [← map_one (Ideal.Quotient.mk (v.asIdeal ^ (ev + 1))), ← map_neg, Ideal.Quotient.eq, sub_neg_eq_add]
    rw [h1, h2, h3]
    constructor
    · intro hmem
      by_contra hnot
      rw [not_or] at hnot
      rcases hnot with ⟨hnot1, hnot2⟩
      have hv1 := hval_ge_of_not_mem (r - 1) hnot1
      have hv2 := hval_ge_of_not_mem (r + 1) hnot2
      have hmul : (r - 1) * (r + 1) = r ^ 2 - 1 := by ring
      have hv_prod : WithZero.exp (-(ev : ℤ) + -(ev : ℤ)) ≤ v.intValuation (r ^ 2 - 1) := by
        calc WithZero.exp (-(ev : ℤ) + -(ev : ℤ))
          _ = WithZero.exp (-(ev : ℤ)) * WithZero.exp (-(ev : ℤ)) := WithZero.exp_add _ _
          _ ≤ v.intValuation (r - 1) * v.intValuation (r + 1) := mul_le_mul' hv1 hv2
          _ = v.intValuation ((r - 1) * (r + 1)) := (Valuation.map_mul _ _ _).symm
          _ = v.intValuation (r ^ 2 - 1) := by rw [hmul]
      have hv_ub : v.intValuation (r ^ 2 - 1) ≤ WithZero.exp (-((2 * ev + 1 : ℕ) : ℤ)) :=
        (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v (r ^ 2 - 1) (2 * ev + 1)).mpr hmem
      have h_ineq : WithZero.exp (-(ev : ℤ) + -(ev : ℤ)) ≤ WithZero.exp (-((2 * ev + 1 : ℕ) : ℤ)) :=
        le_trans hv_prod hv_ub
      rw [WithZero.exp_le_exp] at h_ineq
      omega
    · have hle0 : v.asIdeal ^ (ev + 1) ≤ v.asIdeal ^ ev := Ideal.pow_le_pow_right (by omega)
      rintro (hmem1 | hmem2)
      · have hr2 : r + 1 ∈ v.asIdeal ^ ev := by
          have : r + 1 = (r - 1) + 2 := by ring
          rw [this]
          exact Ideal.add_mem _ (hle0 hmem1) h2_mem
        have hmul : r ^ 2 - 1 = (r - 1) * (r + 1) := by ring
        have hpow : (ev + 1) + ev = 2 * ev + 1 := by omega
        rw [hmul, ← hpow, pow_add]
        exact Ideal.mul_mem_mul hmem1 hr2
      · have hr1 : r - 1 ∈ v.asIdeal ^ ev := by
          have : r - 1 = (r + 1) - 2 := by ring
          rw [this]
          exact Ideal.sub_mem _ (hle0 hmem2) h2_mem
        have hmul : r ^ 2 - 1 = (r + 1) * (r - 1) := by ring
        have hpow : (ev + 1) + ev = 2 * ev + 1 := by omega
        rw [hmul, ← hpow, pow_add]
        exact Ideal.mul_mem_mul hmem2 hr1
  have hone_ne_neg_one : (1 : R₁) ≠ (-1 : R₁) := by
    intro h
    apply h2_not_mem
    have h' : Ideal.Quotient.mk (v.asIdeal ^ (ev + 1)) (1 : 𝓞_K) =
        Ideal.Quotient.mk (v.asIdeal ^ (ev + 1)) (-1 : 𝓞_K) := by
      simpa using h
    rw [Ideal.Quotient.eq] at h'
    have h2 : (1 : 𝓞_K) - (-1 : 𝓞_K) = 2 := by ring
    rwa [h2] at h'
  have e_split : {x : R // x ^ 2 = 1} ≃ {x : R // fac x = 1} ⊕ {x : R // fac x = -1} :=
    { toFun := fun x =>
        if h1 : fac x.1 = 1 then Sum.inl ⟨x.1, h1⟩
        else Sum.inr ⟨x.1, ((hsq1_iff x.1).mp x.2).resolve_left h1⟩
      invFun := fun s =>
        match s with
        | Sum.inl x => ⟨x.1, (hsq1_iff x.1).mpr (Or.inl x.2)⟩
        | Sum.inr x => ⟨x.1, (hsq1_iff x.1).mpr (Or.inr x.2)⟩
      left_inv := fun x => by
        dsimp only
        split_ifs with h1 <;> rfl
      right_inv := fun s => by
        rcases s with ⟨x, hx⟩ | ⟨x, hx⟩
        · dsimp only
          rw [dif_pos hx]
        · dsimp only
          have hnot1 : fac x ≠ 1 := fun h1 => hone_ne_neg_one (h1.symm.trans hx)
          rw [dif_neg hnot1] }
  have hcard_sq1_split : Nat.card {x : R // x ^ 2 = 1} =
      Nat.card {x : R // fac x = 1} + Nat.card {x : R // fac x = -1} := by
    rw [Nat.card_congr e_split, Nat.card_sum]
  have hcardpow : ∀ m : ℕ, Nat.card (𝓞_K ⧸ v.asIdeal ^ m) = (Ideal.absNorm v.asIdeal) ^ m := by
    intro m
    rw [← map_pow Ideal.absNorm v.asIdeal m, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hcardmul : Nat.card R = 2 ^ kv * Nat.card R₁ := by
    change Nat.card (𝓞_K ⧸ v.asIdeal ^ (2 * ev + 1)) = 2 ^ kv * Nat.card (𝓞_K ⧸ v.asIdeal ^ (ev + 1))
    rw [← hkv, hcardpow (2 * ev + 1), hcardpow ev, hcardpow (ev + 1), ← pow_add]
    congr 1
    omega
  have hfac_surj : Function.Surjective fac := Ideal.Quotient.factor_surjective hle
  have hfib : ∀ y : R₁, Nat.card {x : R // fac x = y} = 2 ^ kv := by
    intro y
    let Φ : R →+ R₁ := fac.toAddMonoidHom
    have hΦ_surj : Function.Surjective Φ := hfac_surj
    have hlag : Nat.card R = Nat.card (R ⧸ Φ.ker) * Nat.card Φ.ker :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup Φ.ker
    have hiso : Nat.card (R ⧸ Φ.ker) = Nat.card R₁ :=
      Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective Φ hΦ_surj).toEquiv
    rw [hiso] at hlag
    have hR1_pos : 0 < Nat.card R₁ := Nat.card_pos
    have hker : Nat.card Φ.ker = 2 ^ kv := by
      apply Nat.eq_of_mul_eq_mul_left hR1_pos
      rw [← hlag, hcardmul, Nat.mul_comm]
    obtain ⟨x₀, hx₀⟩ := hfac_surj y
    have e_fib : Φ.ker ≃ {x : R // fac x = y} :=
      { toFun := fun k => ⟨(k : R) + x₀, by
          change Φ ((k : R) + x₀) = y
          rw [map_add, AddMonoidHom.mem_ker.mp k.2, zero_add]
          exact hx₀⟩
        invFun := fun x => ⟨(x : R) - x₀, by
          rw [AddMonoidHom.mem_ker, map_sub]
          change fac x.1 - fac x₀ = 0
          rw [x.2, hx₀, sub_self]⟩
        left_inv := fun k => Subtype.ext (by simp)
        right_inv := fun x => Subtype.ext (by simp) }
    rw [← Nat.card_congr e_fib, hker]
  have hcard_quot : Nat.card (A ⧸ sq.range) = 2 ^ (1 + kv) := by
    rw [hcard_quot_eq_sq1, hcard_sq1_split, hfib 1, hfib (-1), pow_add, pow_one, two_mul]
  have h_extract : ∀ (G : Type u) [CommGroup G] [Finite G],
      Nat.card (G ⧸ (powMonoidHom 2 : G →* G).range) = 2 ^ (1 + kv) →
      ∃ φ : G → (Fin (1 + kv) → ZMod 2),
        (∀ a b : G, φ (a * b) = φ a + φ b) ∧
        (∀ a : G, φ a = 0 ↔ IsSquare a) ∧
        Function.Surjective φ := by
    intro G _ _ hcard
    let sqG : G →* G := powMonoidHom 2
    have h_two_smul : ∀ q : Additive (G ⧸ sqG.range), (2 : ℕ) • q = 0 := by
      intro q
      obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul q)
      have hq : q = Additive.ofMul (QuotientGroup.mk a) := by
        rw [ha, ofMul_toMul]
      rw [hq, two_nsmul, ← ofMul_mul, ← QuotientGroup.mk_mul]
      change Additive.ofMul (QuotientGroup.mk (a * a)) = Additive.ofMul (1 : G ⧸ sqG.range)
      congr 1
      rw [QuotientGroup.eq_one_iff]
      exact ⟨a, by simp [sqG, pow_two]⟩
    letI instMod := AddCommGroup.zmodModule h_two_smul
    haveI : Finite (Additive (G ⧸ sqG.range)) := inferInstanceAs (Finite (G ⧸ sqG.range))
    haveI : Fintype (Additive (G ⧸ sqG.range)) := Fintype.ofFinite (Additive (G ⧸ sqG.range))
    let B_Q := Module.Basis.ofVectorSpace (ZMod 2) (Additive (G ⧸ sqG.range))
    haveI : Fintype (Module.Basis.ofVectorSpaceIndex (ZMod 2) (Additive (G ⧸ sqG.range))) := Fintype.ofFinite _
    have hcard_Q : Fintype.card (Additive (G ⧸ sqG.range)) = 2 ^ (1 + kv) := by
      rw [Fintype.card_eq_nat_card]
      exact hcard
    have hfinrank_Q : Module.finrank (ZMod 2) (Additive (G ⧸ sqG.range)) = 1 + kv := by
      have h1 : Fintype.card (Additive (G ⧸ sqG.range)) =
          (Fintype.card (ZMod 2)) ^ (Module.finrank (ZMod 2) (Additive (G ⧸ sqG.range))) :=
        Module.card_eq_pow_finrank
      rw [hcard_Q, ZMod.card 2] at h1
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h1.symm
    have hcard_idx : Fintype.card (Module.Basis.ofVectorSpaceIndex (ZMod 2) (Additive (G ⧸ sqG.range))) = 1 + kv := by
      rw [← Module.finrank_eq_card_basis B_Q, hfinrank_Q]
    let e_idx : Module.Basis.ofVectorSpaceIndex (ZMod 2) (Additive (G ⧸ sqG.range)) ≃ Fin (1 + kv) :=
      Fintype.equivFinOfCardEq hcard_idx
    let e_Q : Additive (G ⧸ sqG.range) ≃ₗ[ZMod 2] (Fin (1 + kv) → ZMod 2) :=
      (B_Q.reindex e_idx).equivFun
    let φ_q : G → (Fin (1 + kv) → ZMod 2) :=
      fun a => e_Q (Additive.ofMul (QuotientGroup.mk a))
    refine ⟨φ_q, ?_, ?_, ?_⟩
    · intro a b
      dsimp [φ_q]
      rw [map_add]
    · intro a
      dsimp [φ_q]
      rw [LinearEquiv.map_eq_zero_iff]
      change Additive.ofMul (QuotientGroup.mk a) = Additive.ofMul (1 : G ⧸ sqG.range) ↔ IsSquare a
      rw [Additive.ofMul.injective.eq_iff, QuotientGroup.eq_one_iff]
      constructor
      · rintro ⟨b, hb⟩
        refine ⟨b, ?_⟩
        change a = b * b
        rw [← pow_two]
        exact hb.symm
      · rintro ⟨b, rfl⟩
        refine ⟨b, ?_⟩
        change b ^ 2 = b * b
        exact pow_two b
    · intro c
      obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul (e_Q.symm c))
      refine ⟨a, ?_⟩
      dsimp [φ_q]
      rw [ha, ofMul_toMul, LinearEquiv.apply_symm_apply]
  exact h_extract A hcard_quot

theorem adicCompletion_unit_reduction_to_quotient_units {K : Type u} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (ev : ℕ)
    (hev : Valued.v (2 : v.adicCompletion K) = WithZero.exp (-(ev : ℤ))) :
    ∃ (red : v.adicCompletion K → (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (2 * ev + 1))ˣ),
      (∀ u w : v.adicCompletion K, Valued.v u = 1 → Valued.v w = 1 → red (u * w) = red u * red w) ∧
      (∀ u : v.adicCompletion K, Valued.v u = 1 → (IsSquare (red u) ↔ IsSquare u)) ∧
      (∀ a : (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (2 * ev + 1))ˣ,
        ∃ r : NumberField.RingOfIntegers K,
          r ∉ v.asIdeal ∧
          red (algebraMap K (v.adicCompletion K) (algebraMap (NumberField.RingOfIntegers K) K r)) = a) :=
by
  classical
  have h_isUnit_quotient : ∀ (M : ℕ), 0 < M → ∀ (r : NumberField.RingOfIntegers K),
      IsUnit (Ideal.Quotient.mk (v.asIdeal ^ M) r) ↔ r ∉ v.asIdeal := by
    intro M hM r
    constructor
    · intro hu hr
      have hle : v.asIdeal ^ M ≤ v.asIdeal := Ideal.pow_le_self (by omega)
      have hu' : IsUnit (Ideal.Quotient.factor hle (Ideal.Quotient.mk (v.asIdeal ^ M) r)) :=
        hu.map (Ideal.Quotient.factor hle)
      rw [Ideal.Quotient.factor_mk hle r, Ideal.Quotient.eq_zero_iff_mem.mpr hr] at hu'
      haveI : v.asIdeal.IsMaximal := v.isMaximal
      letI : Field (NumberField.RingOfIntegers K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
      exact not_isUnit_zero hu'
    · intro hr
      haveI : v.asIdeal.IsMaximal := v.isMaximal
      obtain ⟨y, i, hi, hyi⟩ := Ideal.IsMaximal.exists_inv v.isMaximal hr
      have htop : Ideal.span {r} ⊔ v.asIdeal = ⊤ := by
        rw [Ideal.eq_top_iff_one]
        refine Submodule.mem_sup.mpr ⟨y * r, Ideal.mem_span_singleton'.mpr ⟨y, rfl⟩, i, hi, hyi⟩
      have htopM : Ideal.span {r} ⊔ v.asIdeal ^ M = ⊤ := Ideal.sup_pow_eq_top htop
      have h1M : (1 : NumberField.RingOfIntegers K) ∈ Ideal.span {r} ⊔ v.asIdeal ^ M := by
        rw [htopM]; trivial
      obtain ⟨p, hp, w, hw, hpw⟩ := Submodule.mem_sup.mp h1M
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hp
      have hsub : r * s - 1 ∈ v.asIdeal ^ M := by
        have heq : r * s - 1 = -w := by linear_combination hpw
        rw [heq]
        exact (v.asIdeal ^ M).neg_mem hw
      have hmk0 : Ideal.Quotient.mk (v.asIdeal ^ M) (r * s - 1) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hsub
      rw [map_sub, map_mul, map_one, sub_eq_zero] at hmk0
      exact isUnit_of_mul_eq_one _ hmk0
  have h_approx_K : ∀ (a : K), IsDedekindDomain.HeightOneSpectrum.valuation K v a ≤ 1 →
      ∀ (M : ℕ), ∃ r : NumberField.RingOfIntegers K,
        IsDedekindDomain.HeightOneSpectrum.valuation K v
          (a - algebraMap (NumberField.RingOfIntegers K) K r) ≤ WithZero.exp (-(M : ℤ)) := by
    intro a ha M
    obtain ⟨xa, ya, hya, hxya⟩ :=
      IsFractionRing.div_surjective (A := NumberField.RingOfIntegers K) (K := K) a
    have hy0 : ya ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hya
    have hiy : algebraMap (NumberField.RingOfIntegers K) K ya ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hya
    have hstar : a * algebraMap (NumberField.RingOfIntegers K) K ya
        = algebraMap (NumberField.RingOfIntegers K) K xa := by
      rw [← hxya]
      exact div_mul_cancel₀ _ hiy
    obtain ⟨m, hym, hym1, hexpm⟩ :
        ∃ m : ℕ, ya ∈ v.asIdeal ^ m ∧ ya ∉ v.asIdeal ^ (m + 1) ∧
          WithZero.exp (-(m : ℤ)) = v.intValuation ya := by
      have ht0 : v.intValuation ya ≠ 0 :=
        IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero v ya hy0
      have ht1 : v.intValuation ya ≤ 1 :=
        IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v ya
      obtain ⟨k, hk⟩ : ∃ k : ℤ, WithZero.exp k = v.intValuation ya := ⟨_, WithZero.exp_log ht0⟩
      have hkle : k ≤ 0 := by
        have hstep : WithZero.exp k ≤ WithZero.exp (0 : ℤ) := by
          rw [hk, WithZero.exp_zero]; exact ht1
        exact WithZero.exp_le_exp.mp hstep
      have hcast : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      have hexpm : WithZero.exp (-(((-k).toNat : ℕ) : ℤ)) = v.intValuation ya := by
        rw [hcast, neg_neg, hk]
      refine ⟨(-k).toNat, ?_, ?_, hexpm⟩
      · exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya _).mp
          (le_of_eq hexpm.symm)
      · intro hcon
        have hle :=
          (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya
            ((-k).toNat + 1)).mpr hcon
        have he : (-(((-k).toNat + 1 : ℕ) : ℤ)) = k - 1 := by
          rw [Nat.cast_add, Nat.cast_one, hcast]; ring
        rw [he, ← hk] at hle
        have := WithZero.exp_le_exp.mp hle
        omega
    have hivy : v.intValuation ya ≤ WithZero.exp (-(m : ℤ)) :=
      (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya m).mpr hym
    have hxm : xa ∈ v.asIdeal ^ m := by
      refine (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v xa m).mp ?_
      have e1 : v.intValuation xa
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K xa) :=
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v xa).symm
      have e2 : v.intValuation ya
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K ya) :=
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v ya).symm
      calc v.intValuation xa
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (a * algebraMap (NumberField.RingOfIntegers K) K ya) := by
            rw [hstar]; exact e1
        _ = IsDedekindDomain.HeightOneSpectrum.valuation K v a *
              IsDedekindDomain.HeightOneSpectrum.valuation K v
                (algebraMap (NumberField.RingOfIntegers K) K ya) := Valuation.map_mul _ _ _
        _ ≤ 1 * IsDedekindDomain.HeightOneSpectrum.valuation K v
                (algebraMap (NumberField.RingOfIntegers K) K ya) := mul_le_mul_left ha _
        _ = v.intValuation ya := by rw [one_mul, ← e2]
        _ ≤ WithZero.exp (-(m : ℤ)) := hivy
    have hPprime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
    have hJdvd : (Ideal.span {ya} ⊔ v.asIdeal ^ (m + M)) ∣ v.asIdeal ^ (m + M) :=
      Ideal.dvd_iff_le.mpr le_sup_right
    obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow hPprime (m + M)).mp hJdvd
    have hJ : Ideal.span {ya} ⊔ v.asIdeal ^ (m + M) = v.asIdeal ^ i := associated_iff_eq.mp hassoc
    have hyJ : ya ∈ v.asIdeal ^ i := by
      rw [← hJ]
      exact Ideal.dvd_span_singleton.mp (Ideal.dvd_iff_le.mpr le_sup_left)
    have him : i ≤ m := by
      by_contra hcon
      have hle : m + 1 ≤ i := by omega
      exact hym1 (Ideal.pow_le_pow_right hle hyJ)
    have hxJ : xa ∈ Ideal.span {ya} ⊔ v.asIdeal ^ (m + M) := by
      rw [hJ]
      exact Ideal.pow_le_pow_right him hxm
    obtain ⟨p, hp, w, hw, hpw⟩ := Submodule.mem_sup.mp hxJ
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hp
    refine ⟨r, ?_⟩
    have hxrw : xa = r * ya + w := by rw [← hpw, hr]
    have key : (a - algebraMap (NumberField.RingOfIntegers K) K r)
        * algebraMap (NumberField.RingOfIntegers K) K ya
        = algebraMap (NumberField.RingOfIntegers K) K w := by
      have h1 : algebraMap (NumberField.RingOfIntegers K) K xa
          = algebraMap (NumberField.RingOfIntegers K) K r
              * algebraMap (NumberField.RingOfIntegers K) K ya
            + algebraMap (NumberField.RingOfIntegers K) K w := by
        rw [hxrw, map_add, map_mul]
      rw [sub_mul, hstar, h1]; ring
    have hV : IsDedekindDomain.HeightOneSpectrum.valuation K v
          (a - algebraMap (NumberField.RingOfIntegers K) K r) * v.intValuation ya
        = v.intValuation w := by
      rw [← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v ya,
        ← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v w,
        ← Valuation.map_mul, key]
    have hwb : v.intValuation w ≤ WithZero.exp (-((m + M : ℕ) : ℤ)) :=
      (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v w (m + M)).mpr hw
    calc IsDedekindDomain.HeightOneSpectrum.valuation K v
          (a - algebraMap (NumberField.RingOfIntegers K) K r)
        = IsDedekindDomain.HeightOneSpectrum.valuation K v
            (a - algebraMap (NumberField.RingOfIntegers K) K r) *
            (WithZero.exp (-(m : ℤ)) * WithZero.exp (m : ℤ)) := by
          rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, mul_one]
      _ = (IsDedekindDomain.HeightOneSpectrum.valuation K v
            (a - algebraMap (NumberField.RingOfIntegers K) K r) * v.intValuation ya) *
            WithZero.exp (m : ℤ) := by
          rw [← hexpm, mul_assoc]
      _ = v.intValuation w * WithZero.exp (m : ℤ) := by rw [hV]
      _ ≤ WithZero.exp (-((m + M : ℕ) : ℤ)) * WithZero.exp (m : ℤ) :=
          mul_le_mul_left hwb _
      _ = WithZero.exp (-(M : ℤ)) := by
          rw [← WithZero.exp_add]
          congr 1
          push_cast
          ring
  have h_approx_int : ∀ (z : v.adicCompletion K), Valued.v z ≤ 1 → ∀ (M : ℕ),
      ∃ r : NumberField.RingOfIntegers K,
        Valued.v (z - algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K r)) ≤ WithZero.exp (-(M : ℤ)) := by
    intro z hz M
    have hdense : DenseRange (fun y : K => algebraMap K (v.adicCompletion K) y) := by
      letI : Valued K (WithZero (Multiplicative ℤ)) :=
        IsDedekindDomain.HeightOneSpectrum.adicValued (K := K) v
      exact UniformSpace.Completion.denseRange_coe
    let γ : (WithZero (Multiplicative ℤ))ˣ :=
      Units.mk0 (WithZero.exp (-(M : ℤ))) WithZero.exp_ne_zero
    have hnhds : {y : v.adicCompletion K |
        Valued.v (y - z) < (γ : WithZero (Multiplicative ℤ))} ∈ nhds z :=
      Valued.mem_nhds.mpr ⟨γ, subset_rfl⟩
    obtain ⟨u, hu1, k, hk⟩ := mem_closure_iff_nhds.mp (hdense z) _ hnhds
    have hkl : Valued.v (z - algebraMap K (v.adicCompletion K) k) ≤ WithZero.exp (-(M : ℤ)) := by
      dsimp only at hk
      rw [Valuation.map_sub_swap, hk]
      exact le_of_lt hu1
    have hexple : WithZero.exp (-(M : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
      rw [← WithZero.exp_zero]
      exact WithZero.exp_le_exp.mpr (by omega)
    have hvc : ∀ x : K, Valued.v (algebraMap K (v.adicCompletion K) x) =
        IsDedekindDomain.HeightOneSpectrum.valuation K v x :=
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v
    have hvk : IsDedekindDomain.HeightOneSpectrum.valuation K v k ≤ 1 := by
      rw [← hvc k]
      have hsplit : algebraMap K (v.adicCompletion K) k =
          z - (z - algebraMap K (v.adicCompletion K) k) := by ring
      rw [hsplit]
      exact le_trans (Valuation.map_sub Valued.v _ _) (max_le hz (le_trans hkl hexple))
    obtain ⟨r, hr⟩ := h_approx_K k hvk M
    refine ⟨r, ?_⟩
    have hsplit2 : z - algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K r) =
        (z - algebraMap K (v.adicCompletion K) k) +
          algebraMap K (v.adicCompletion K)
            (k - algebraMap (NumberField.RingOfIntegers K) K r) := by
      rw [map_sub]; ring
    rw [hsplit2]
    refine le_trans (Valuation.map_add Valued.v _ _) (max_le hkl ?_)
    rw [hvc]
    exact hr
  have h_quad_root : ∀ (b c x₀ : v.adicCompletion K),
      Valued.v (2 * x₀ + b) = (1 : WithZero (Multiplicative ℤ)) →
      Valued.v (x₀ ^ 2 + b * x₀ + c) < (1 : WithZero (Multiplicative ℤ)) →
      ∃ x : v.adicCompletion K, x ^ 2 + b * x + c = 0 := by
    intro b c x₀ hder hval
    have hdbl : ∀ t : v.adicCompletion K, Valued.v (2 * t) ≤ Valued.v t := by
      intro t
      have e : (2 : v.adicCompletion K) * t = t + t := by ring
      have h : Valued.v (t + t) ≤ max (Valued.v t) (Valued.v t) := Valuation.map_add _ _ _
      rw [max_self] at h
      rw [e]
      exact h
    have hstep : ∀ y : v.adicCompletion K,
        Valued.v (2 * y + b) = (1 : WithZero (Multiplicative ℤ)) →
        Valued.v (y ^ 2 + b * y + c) < (1 : WithZero (Multiplicative ℤ)) →
        Valued.v (2 * (y - (y ^ 2 + b * y + c) / (2 * y + b)) + b)
            = (1 : WithZero (Multiplicative ℤ)) ∧
        Valued.v ((y - (y ^ 2 + b * y + c) / (2 * y + b)) ^ 2
              + b * (y - (y ^ 2 + b * y + c) / (2 * y + b)) + c)
            = Valued.v (y ^ 2 + b * y + c) ^ 2 ∧
        Valued.v (y - (y ^ 2 + b * y + c) / (2 * y + b) - y)
            = Valued.v (y ^ 2 + b * y + c) := by
      intro y hD hP
      have hDne : (2 : v.adicCompletion K) * y + b ≠ 0 := by
        intro hcon
        rw [hcon, map_zero] at hD
        exact zero_ne_one hD
      have ht : Valued.v ((y ^ 2 + b * y + c) / (2 * y + b))
          = Valued.v (y ^ 2 + b * y + c) := by
        rw [map_div₀, hD, div_one]
      refine ⟨?_, ?_, ?_⟩
      · have e : 2 * (y - (y ^ 2 + b * y + c) / (2 * y + b)) + b
            = (2 * y + b) - 2 * ((y ^ 2 + b * y + c) / (2 * y + b)) := by ring
        have hlt : Valued.v (2 * ((y ^ 2 + b * y + c) / (2 * y + b)))
            < Valued.v (2 * y + b) := by
          refine lt_of_le_of_lt (hdbl _) ?_
          rw [ht, hD]
          exact hP
        rw [e, Valuation.map_sub_eq_of_lt_left _ hlt, hD]
      · have hcancel : (y ^ 2 + b * y + c) / (2 * y + b) * (2 * y + b)
            = y ^ 2 + b * y + c := div_mul_cancel₀ _ hDne
        have key : (y - (y ^ 2 + b * y + c) / (2 * y + b)) ^ 2
              + b * (y - (y ^ 2 + b * y + c) / (2 * y + b)) + c
            = ((y ^ 2 + b * y + c) / (2 * y + b)) ^ 2 := by
          linear_combination -hcancel
        rw [key, Valuation.map_pow, ht]
      · have key : y - (y ^ 2 + b * y + c) / (2 * y + b) - y
            = -((y ^ 2 + b * y + c) / (2 * y + b)) := by ring
        rw [key, Valuation.map_neg, ht]
    have hdecay : ∀ δ γ : WithZero (Multiplicative ℤ), δ < 1 → γ ≠ 0 →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → δ ^ (2 ^ n) < γ := by
      intro δ γ hδ hγ
      rcases eq_or_ne δ 0 with h0 | h0
      · refine ⟨0, fun n _ => ?_⟩
        rw [h0, zero_pow (Nat.two_pow_pos n).ne']
        exact zero_lt_iff.mpr hγ
      · obtain ⟨a, rfl⟩ : ∃ a : ℤ, δ = ((Multiplicative.ofAdd a : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
          obtain ⟨g, hg⟩ := WithZero.ne_zero_iff_exists.mp h0
          exact ⟨Multiplicative.toAdd g, hg.symm⟩
        obtain ⟨β, rfl⟩ : ∃ β : ℤ, γ = ((Multiplicative.ofAdd β : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
          obtain ⟨g, hg⟩ := WithZero.ne_zero_iff_exists.mp hγ
          exact ⟨Multiplicative.toAdd g, hg.symm⟩
        have ha : a < 0 := WithZero.coe_lt_one.mp hδ
        have hpow : ∀ k : ℕ,
            ((Multiplicative.ofAdd a : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ k
              = ((Multiplicative.ofAdd ((k : ℤ) * a) : Multiplicative ℤ) :
                  WithZero (Multiplicative ℤ)) := by
          intro k
          rw [← WithZero.coe_pow]
          congr 1
        refine ⟨(-β).toNat + 1, fun n hn => ?_⟩
        rw [hpow, WithZero.coe_lt_coe]
        have hbk : -β < ((2 ^ n : ℕ) : ℤ) := by
          have hx : (-β).toNat < n := by omega
          have h1 : (-β).toNat < 2 ^ n := lt_trans hx Nat.lt_two_pow_self
          have h2' : ((-β).toNat : ℤ) < ((2 ^ n : ℕ) : ℤ) := by exact_mod_cast h1
          exact lt_of_le_of_lt (Int.self_le_toNat _) h2'
        have hkpos : (0 : ℤ) ≤ ((2 ^ n : ℕ) : ℤ) := Int.natCast_nonneg _
        have ha1 : a ≤ -1 := by omega
        have hle : ((2 ^ n : ℕ) : ℤ) * a ≤ ((2 ^ n : ℕ) : ℤ) * (-1) :=
          mul_le_mul_of_nonneg_left ha1 hkpos
        have hgoal : ((2 ^ n : ℕ) : ℤ) * a < β := by linarith
        exact hgoal
    obtain ⟨ε, hεdef⟩ : ∃ ε : WithZero (Multiplicative ℤ),
        ε = Valued.v (x₀ ^ 2 + b * x₀ + c) := ⟨_, rfl⟩
    have hε : ε < (1 : WithZero (Multiplicative ℤ)) := by rw [hεdef]; exact hval
    obtain ⟨f, hf0, hfs⟩ : ∃ f : ℕ → v.adicCompletion K, f 0 = x₀ ∧
        ∀ n : ℕ, f (n + 1) = f n - (f n ^ 2 + b * f n + c) / (2 * f n + b) :=
      ⟨fun n => Nat.rec (motive := fun _ => v.adicCompletion K) x₀
        (fun _ y => y - (y ^ 2 + b * y + c) / (2 * y + b)) n, rfl, fun _ => rfl⟩
    have hinv : ∀ n : ℕ, Valued.v (2 * f n + b) = (1 : WithZero (Multiplicative ℤ)) ∧
        Valued.v (f n ^ 2 + b * f n + c) = ε ^ (2 ^ n) := by
      intro n
      induction n with
      | zero =>
        refine ⟨by rw [hf0]; exact hder, ?_⟩
        rw [hf0, pow_zero, pow_one, hεdef]
      | succ n ih =>
        have hlt : Valued.v (f n ^ 2 + b * f n + c) < (1 : WithZero (Multiplicative ℤ)) := by
          rw [ih.2]
          exact pow_lt_one₀ zero_le' hε (Nat.two_pow_pos n).ne'
        obtain ⟨s1, s2, -⟩ := hstep (f n) ih.1 hlt
        refine ⟨by rw [hfs n]; exact s1, ?_⟩
        rw [hfs n, s2, ih.2, ← pow_mul]
        congr 1
    have hdiff : ∀ n : ℕ, Valued.v (f (n + 1) - f n) = ε ^ (2 ^ n) := by
      intro n
      have hlt : Valued.v (f n ^ 2 + b * f n + c) < (1 : WithZero (Multiplicative ℤ)) := by
        rw [(hinv n).2]
        exact pow_lt_one₀ zero_le' hε (Nat.two_pow_pos n).ne'
      obtain ⟨-, -, s3⟩ := hstep (f n) (hinv n).1 hlt
      rw [hfs n, s3, (hinv n).2]
    have hCauchy : Cauchy (Filter.map f Filter.atTop) := by
      refine Valued.cauchy_iff.mpr ⟨inferInstance, ?_⟩
      intro γ
      obtain ⟨N, hN⟩ := hdecay ε (γ : WithZero (Multiplicative ℤ)) hε (Units.ne_zero γ)
      have htel : ∀ m : ℕ, N ≤ m → Valued.v (f m - f N) < (γ : WithZero (Multiplicative ℤ)) := by
        intro m hm
        induction m, hm using Nat.le_induction with
        | base =>
          rw [sub_self, map_zero]
          exact zero_lt_iff.mpr (Units.ne_zero γ)
        | succ m hm ih =>
          have e : f (m + 1) - f N = (f (m + 1) - f m) + (f m - f N) := by ring
          rw [e]
          refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ih)
          rw [hdiff m]
          exact hN m hm
      refine ⟨f '' (Set.Ici N), Filter.image_mem_map (Filter.Ici_mem_atTop N), ?_⟩
      rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
      have e : f j - f i = (f j - f N) - (f i - f N) := by ring
      rw [e]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt (htel j hj) (htel i hi))
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hCauchy
    have hPlim : Filter.Tendsto (fun n : ℕ => f n ^ 2 + b * f n + c) Filter.atTop
        (nhds (x ^ 2 + b * x + c)) :=
      ((hx.pow 2).add (tendsto_const_nhds.mul hx)).add tendsto_const_nhds
    have hzero : Filter.Tendsto (fun n : ℕ => f n ^ 2 + b * f n + c) Filter.atTop
        (nhds (0 : v.adicCompletion K)) := by
      rw [Filter.tendsto_def]
      intro s hs
      obtain ⟨γ, hγs⟩ := Valued.mem_nhds_zero.mp hs
      obtain ⟨N, hN⟩ := hdecay ε (γ : WithZero (Multiplicative ℤ)) hε (Units.ne_zero γ)
      refine Filter.mem_of_superset (Filter.Ici_mem_atTop N) ?_
      intro n hn
      apply hγs
      show Valued.v (f n ^ 2 + b * f n + c) < (γ : WithZero (Multiplicative ℤ))
      rw [(hinv n).2]
      exact hN n hn
    exact ⟨x, tendsto_nhds_unique hPlim hzero⟩
  have h_sq_lt_four : ∀ (b x : v.adicCompletion K), Valued.v x = 1 →
      Valued.v (b - x ^ 2) < Valued.v (4 : v.adicCompletion K) →
      ∃ y : v.adicCompletion K, y ^ 2 = b := by
    intro b x hx hb
    have h4pos : (0 : WithZero (Multiplicative ℤ)) < Valued.v (4 : v.adicCompletion K) :=
      lt_of_le_of_lt zero_le' hb
    have h4ne : (4 : v.adicCompletion K) ≠ 0 :=
      (Valuation.ne_zero_iff Valued.v).mp (ne_of_gt h4pos)
    have hx0 : x ≠ 0 := by
      refine (Valuation.ne_zero_iff Valued.v).mp ?_
      rw [hx]
      exact one_ne_zero
    have hv4x : Valued.v ((4 : v.adicCompletion K) * x ^ 2)
        = Valued.v (4 : v.adicCompletion K) := by
      rw [map_mul, map_pow, hx, one_pow, mul_one]
    obtain ⟨ζ, hζdef⟩ :
        ∃ z : v.adicCompletion K, z = (b - x ^ 2) / ((4 : v.adicCompletion K) * x ^ 2) :=
      ⟨_, rfl⟩
    have hζ : Valued.v ζ < (1 : WithZero (Multiplicative ℤ)) := by
      rw [hζdef, map_div₀, hv4x]
      exact (div_lt_one₀ h4pos).mpr hb
    obtain ⟨W, hW⟩ := h_quad_root 1 (-ζ) 0
      (by
        rw [show (2 : v.adicCompletion K) * 0 + 1 = 1 by ring]
        exact map_one _)
      (by
        rw [show (0 : v.adicCompletion K) ^ 2 + 1 * 0 + -ζ = -ζ by ring, Valuation.map_neg]
        exact hζ)
    have hWz : W ^ 2 + W = ζ := by linear_combination hW
    have key : (4 : v.adicCompletion K) * x ^ 2 * (W ^ 2 + W) = b - x ^ 2 := by
      rw [hWz, hζdef]
      field_simp
    exact ⟨x * (1 + 2 * W), by linear_combination key⟩
  let M : ℕ := 2 * ev + 1
  have hM : 0 < M := by omega
  let ι_hom : NumberField.RingOfIntegers K →+* v.adicCompletion K :=
    (algebraMap K (v.adicCompletion K)).comp (algebraMap (NumberField.RingOfIntegers K) K)
  have hval_int : ∀ r : NumberField.RingOfIntegers K, Valued.v (ι_hom r) = v.intValuation r := by
    intro r
    have h1 : Valued.v (algebraMap K (v.adicCompletion K)
        (algebraMap (NumberField.RingOfIntegers K) K r))
        = IsDedekindDomain.HeightOneSpectrum.valuation K v
            (algebraMap (NumberField.RingOfIntegers K) K r) :=
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v
        (algebraMap (NumberField.RingOfIntegers K) K r)
    change Valued.v (algebraMap K (v.adicCompletion K)
      (algebraMap (NumberField.RingOfIntegers K) K r)) = v.intValuation r
    rw [h1]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v r
  have hval_le_one : ∀ r : NumberField.RingOfIntegers K, Valued.v (ι_hom r) ≤ 1 := by
    intro r
    rw [hval_int r]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v r
  have hval_eq_one_iff : ∀ r : NumberField.RingOfIntegers K,
      Valued.v (ι_hom r) = 1 ↔ r ∉ v.asIdeal := by
    intro r
    rw [hval_int r]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff
  have hval_le_exp_iff : ∀ r : NumberField.RingOfIntegers K,
      Valued.v (ι_hom r) ≤ WithZero.exp (-(M : ℤ)) ↔ r ∈ v.asIdeal ^ M := by
    intro r
    rw [hval_int r]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v r M
  have hexp_lt_one : WithZero.exp (-(M : ℤ)) < (1 : WithZero (Multiplicative ℤ)) := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  let IsRed : v.adicCompletion K →
      (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ M)ˣ → Prop :=
    fun u a => ∃ r : NumberField.RingOfIntegers K,
      Ideal.Quotient.mk (v.asIdeal ^ M) r =
        (a : NumberField.RingOfIntegers K ⧸ v.asIdeal ^ M) ∧
      Valued.v (u - ι_hom r) ≤ WithZero.exp (-(M : ℤ))
  have hex_red : ∀ u : v.adicCompletion K, Valued.v u = 1 →
      ∃ a : (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ M)ˣ, IsRed u a := by
    intro u hu
    obtain ⟨r, hr_approx⟩ := h_approx_int u (le_of_eq hu) M
    have hr_val : Valued.v (ι_hom r) = 1 := by
      have heq : ι_hom r = u - (u - ι_hom r) := by ring
      have hlt : Valued.v (u - ι_hom r) < Valued.v u := by
        rw [hu]
        exact lt_of_le_of_lt hr_approx hexp_lt_one
      rw [heq, Valuation.map_sub_eq_of_lt_left _ hlt, hu]
    have hr_not_mem : r ∉ v.asIdeal := (hval_eq_one_iff r).mp hr_val
    have hu_mk : IsUnit (Ideal.Quotient.mk (v.asIdeal ^ M) r) :=
      (h_isUnit_quotient M hM r).mpr hr_not_mem
    exact ⟨hu_mk.unit, r, IsUnit.unit_spec hu_mk, hr_approx⟩
  have huniq_red : ∀ (u : v.adicCompletion K)
      (a₁ a₂ : (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ M)ˣ),
      IsRed u a₁ → IsRed u a₂ → a₁ = a₂ := by
    rintro u a₁ a₂ ⟨r₁, hr₁_mk, hr₁_val⟩ ⟨r₂, hr₂_mk, hr₂_val⟩
    have hsub_val : Valued.v (ι_hom (r₁ - r₂)) ≤ WithZero.exp (-(M : ℤ)) := by
      have heq : ι_hom (r₁ - r₂) = (u - ι_hom r₂) - (u - ι_hom r₁) := by
        rw [map_sub]; ring
      rw [heq]
      exact le_trans (Valuation.map_sub _ _ _) (max_le hr₂_val hr₁_val)
    have hmem : r₁ - r₂ ∈ v.asIdeal ^ M := (hval_le_exp_iff (r₁ - r₂)).mp hsub_val
    have hmk_eq : Ideal.Quotient.mk (v.asIdeal ^ M) r₁ =
        Ideal.Quotient.mk (v.asIdeal ^ M) r₂ := by
      rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact hmem
    apply Units.ext
    rw [← hr₁_mk, ← hr₂_mk, hmk_eq]
  let red : v.adicCompletion K → (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ M)ˣ :=
    fun u => if h : Valued.v u = 1 then (hex_red u h).choose else 1
  have hred_spec : ∀ u : v.adicCompletion K, Valued.v u = 1 → IsRed u (red u) := by
    intro u hu
    dsimp [red]
    rw [dif_pos hu]
    exact (hex_red u hu).choose_spec
  have hred_eq : ∀ (u : v.adicCompletion K) (hu : Valued.v u = 1)
      (a : (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ M)ˣ),
      IsRed u a → red u = a := by
    intro u hu a ha
    exact huniq_red u (red u) a (hred_spec u hu) ha
  have hred_mul : ∀ u w : v.adicCompletion K,
      Valued.v u = 1 → Valued.v w = 1 → red (u * w) = red u * red w := by
    intro u w hu hw
    have huw : Valued.v (u * w) = 1 := by rw [map_mul, hu, hw, mul_one]
    obtain ⟨r₁, hr₁_mk, hr₁_val⟩ := hred_spec u hu
    obtain ⟨r₂, hr₂_mk, hr₂_val⟩ := hred_spec w hw
    apply hred_eq (u * w) huw (red u * red w)
    refine ⟨r₁ * r₂, ?_, ?_⟩
    · rw [map_mul, hr₁_mk, hr₂_mk, Units.val_mul]
    · have heq : u * w - ι_hom (r₁ * r₂) =
          u * (w - ι_hom r₂) + ι_hom r₂ * (u - ι_hom r₁) := by
        rw [map_mul]; ring
      rw [heq]
      refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
      · rw [map_mul, hu, one_mul]
        exact hr₂_val
      · rw [map_mul]
        calc Valued.v (ι_hom r₂) * Valued.v (u - ι_hom r₁)
            ≤ 1 * WithZero.exp (-(M : ℤ)) := mul_le_mul' (hval_le_one r₂) hr₁_val
          _ = WithZero.exp (-(M : ℤ)) := one_mul _
  refine ⟨red, hred_mul, ?_, ?_⟩
  · intro u hu
    constructor
    · rintro ⟨b, hb⟩
      obtain ⟨s, hs_mk⟩ := Ideal.Quotient.mk_surjective (I := v.asIdeal ^ M)
        (b : NumberField.RingOfIntegers K ⧸ v.asIdeal ^ M)
      have hs_unit : IsUnit (Ideal.Quotient.mk (v.asIdeal ^ M) s) := by
        rw [hs_mk]; exact b.isUnit
      have hs_not_mem : s ∉ v.asIdeal := (h_isUnit_quotient M hM s).mp hs_unit
      have hs_val : Valued.v (ι_hom s) = 1 := (hval_eq_one_iff s).mpr hs_not_mem
      obtain ⟨r, hr_mk, hr_val⟩ := hred_spec u hu
      have hrs_mk : Ideal.Quotient.mk (v.asIdeal ^ M) (r - s ^ 2) = 0 := by
        rw [map_sub, map_pow, hr_mk, hs_mk, hb, Units.val_mul, sq, sub_self]
      have hrs_mem : r - s ^ 2 ∈ v.asIdeal ^ M := Ideal.Quotient.eq_zero_iff_mem.mp hrs_mk
      have hrs_val : Valued.v (ι_hom r - (ι_hom s) ^ 2) ≤ WithZero.exp (-(M : ℤ)) := by
        rw [← map_pow, ← map_sub]
        exact (hval_le_exp_iff (r - s ^ 2)).mpr hrs_mem
      have hus_val : Valued.v (u - (ι_hom s) ^ 2) ≤ WithZero.exp (-(M : ℤ)) := by
        have heq : u - (ι_hom s) ^ 2 = (u - ι_hom r) + (ι_hom r - (ι_hom s) ^ 2) := by ring
        rw [heq]
        exact le_trans (Valuation.map_add _ _ _) (max_le hr_val hrs_val)
      have hv4 : Valued.v (4 : v.adicCompletion K) = WithZero.exp (-(2 * (ev : ℤ))) := by
        have h4eq : (4 : v.adicCompletion K) = 2 * 2 := by norm_num
        rw [h4eq, map_mul, hev, ← WithZero.exp_add]
        congr 1; ring
      have hlt4 : Valued.v (u - (ι_hom s) ^ 2) < Valued.v (4 : v.adicCompletion K) := by
        refine lt_of_le_of_lt hus_val ?_
        rw [hv4, WithZero.exp_lt_exp]
        dsimp [M]; omega
      obtain ⟨y, hy⟩ := h_sq_lt_four u (ι_hom s) hs_val hlt4
      exact ⟨y, by rw [← sq, hy]⟩
    · rintro ⟨z, rfl⟩
      have hz0 : Valued.v z ≠ 0 := by
        intro h
        rw [map_mul, h, zero_mul] at hu
        exact zero_ne_one hu
      obtain ⟨k, hk⟩ : ∃ k : ℤ, WithZero.exp k = Valued.v z := ⟨_, WithZero.exp_log hz0⟩
      have hk2 : WithZero.exp (k + k) = WithZero.exp (0 : ℤ) := by
        rw [WithZero.exp_add, hk, ← map_mul, hu, WithZero.exp_zero]
      have hk0 : k = 0 := by
        have h1 : k + k ≤ 0 := WithZero.exp_le_exp.mp (le_of_eq hk2)
        have h2 : 0 ≤ k + k := WithZero.exp_le_exp.mp (le_of_eq hk2.symm)
        omega
      have hz : Valued.v z = 1 := by
        rw [← hk, hk0, WithZero.exp_zero]
      exact ⟨red z, hred_mul z z hz hz⟩
  · intro a
    obtain ⟨r, hr_mk⟩ := Ideal.Quotient.mk_surjective (I := v.asIdeal ^ M)
      (a : NumberField.RingOfIntegers K ⧸ v.asIdeal ^ M)
    have hr_unit : IsUnit (Ideal.Quotient.mk (v.asIdeal ^ M) r) := by
      rw [hr_mk]; exact a.isUnit
    have hr_not_mem : r ∉ v.asIdeal := (h_isUnit_quotient M hM r).mp hr_unit
    have hr_val : Valued.v (ι_hom r) = 1 := (hval_eq_one_iff r).mpr hr_not_mem
    refine ⟨r, hr_not_mem, hred_eq (ι_hom r) hr_val a ⟨r, hr_mk, ?_⟩⟩
    rw [sub_self, map_zero]
    exact zero_le'

theorem hilbLoc_nondeg {K : Type u} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : v.adicCompletion K) (hx : x ≠ 0)
    (horth : ∀ y : v.adicCompletion K, y ≠ 0 → hilbLoc v x y = 1) :
    IsSquare x :=
by
  classical
  have h_approx_K : ∀ (a : K), IsDedekindDomain.HeightOneSpectrum.valuation K v a ≤ 1 →
      ∀ (M : ℕ), ∃ r : NumberField.RingOfIntegers K,
        IsDedekindDomain.HeightOneSpectrum.valuation K v
          (a - algebraMap (NumberField.RingOfIntegers K) K r) ≤ WithZero.exp (-(M : ℤ)) := by
    intro a ha M
    obtain ⟨xa, ya, hya, hxya⟩ :=
      IsFractionRing.div_surjective (A := NumberField.RingOfIntegers K) (K := K) a
    have hy0 : ya ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hya
    have hiy : algebraMap (NumberField.RingOfIntegers K) K ya ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hya
    have hstar : a * algebraMap (NumberField.RingOfIntegers K) K ya
        = algebraMap (NumberField.RingOfIntegers K) K xa := by
      rw [← hxya]
      exact div_mul_cancel₀ _ hiy
    obtain ⟨m, hym, hym1, hexpm⟩ :
        ∃ m : ℕ, ya ∈ v.asIdeal ^ m ∧ ya ∉ v.asIdeal ^ (m + 1) ∧
          WithZero.exp (-(m : ℤ)) = v.intValuation ya := by
      have ht0 : v.intValuation ya ≠ 0 :=
        IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero v ya hy0
      have ht1 : v.intValuation ya ≤ 1 :=
        IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v ya
      obtain ⟨k, hk⟩ : ∃ k : ℤ, WithZero.exp k = v.intValuation ya := ⟨_, WithZero.exp_log ht0⟩
      have hkle : k ≤ 0 := by
        have hstep : WithZero.exp k ≤ WithZero.exp (0 : ℤ) := by
          rw [hk, WithZero.exp_zero]; exact ht1
        exact WithZero.exp_le_exp.mp hstep
      have hcast : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      have hexpm : WithZero.exp (-(((-k).toNat : ℕ) : ℤ)) = v.intValuation ya := by
        rw [hcast, neg_neg, hk]
      refine ⟨(-k).toNat, ?_, ?_, hexpm⟩
      · exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya _).mp
          (le_of_eq hexpm.symm)
      · intro hcon
        have hle :=
          (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya
            ((-k).toNat + 1)).mpr hcon
        have he : (-(((-k).toNat + 1 : ℕ) : ℤ)) = k - 1 := by
          rw [Nat.cast_add, Nat.cast_one, hcast]; ring
        rw [he, ← hk] at hle
        have := WithZero.exp_le_exp.mp hle
        omega
    have hivy : v.intValuation ya ≤ WithZero.exp (-(m : ℤ)) :=
      (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya m).mpr hym
    have hxm : xa ∈ v.asIdeal ^ m := by
      refine (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v xa m).mp ?_
      have e1 : v.intValuation xa
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K xa) :=
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v xa).symm
      have e2 : v.intValuation ya
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K ya) :=
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v ya).symm
      calc v.intValuation xa
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (a * algebraMap (NumberField.RingOfIntegers K) K ya) := by
            rw [hstar]; exact e1
        _ = IsDedekindDomain.HeightOneSpectrum.valuation K v a *
              IsDedekindDomain.HeightOneSpectrum.valuation K v
                (algebraMap (NumberField.RingOfIntegers K) K ya) := Valuation.map_mul _ _ _
        _ ≤ 1 * IsDedekindDomain.HeightOneSpectrum.valuation K v
                (algebraMap (NumberField.RingOfIntegers K) K ya) := mul_le_mul_left ha _
        _ = v.intValuation ya := by rw [one_mul, ← e2]
        _ ≤ WithZero.exp (-(m : ℤ)) := hivy
    have hPprime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
    have hJdvd : (Ideal.span {ya} ⊔ v.asIdeal ^ (m + M)) ∣ v.asIdeal ^ (m + M) :=
      Ideal.dvd_iff_le.mpr le_sup_right
    obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow hPprime (m + M)).mp hJdvd
    have hJ : Ideal.span {ya} ⊔ v.asIdeal ^ (m + M) = v.asIdeal ^ i := associated_iff_eq.mp hassoc
    have hyJ : ya ∈ v.asIdeal ^ i := by
      rw [← hJ]
      exact Ideal.dvd_span_singleton.mp (Ideal.dvd_iff_le.mpr le_sup_left)
    have him : i ≤ m := by
      by_contra hcon
      have hle : m + 1 ≤ i := by omega
      exact hym1 (Ideal.pow_le_pow_right hle hyJ)
    have hxJ : xa ∈ Ideal.span {ya} ⊔ v.asIdeal ^ (m + M) := by
      rw [hJ]
      exact Ideal.pow_le_pow_right him hxm
    obtain ⟨p, hp, w, hw, hpw⟩ := Submodule.mem_sup.mp hxJ
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hp
    refine ⟨r, ?_⟩
    have hxrw : xa = r * ya + w := by rw [← hpw, hr]
    have key : (a - algebraMap (NumberField.RingOfIntegers K) K r)
        * algebraMap (NumberField.RingOfIntegers K) K ya
        = algebraMap (NumberField.RingOfIntegers K) K w := by
      have h1 : algebraMap (NumberField.RingOfIntegers K) K xa
          = algebraMap (NumberField.RingOfIntegers K) K r
              * algebraMap (NumberField.RingOfIntegers K) K ya
            + algebraMap (NumberField.RingOfIntegers K) K w := by
        rw [hxrw, map_add, map_mul]
      rw [sub_mul, hstar, h1]; ring
    have hV : IsDedekindDomain.HeightOneSpectrum.valuation K v
          (a - algebraMap (NumberField.RingOfIntegers K) K r) * v.intValuation ya
        = v.intValuation w := by
      rw [← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v ya,
        ← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v w,
        ← Valuation.map_mul, key]
    have hwb : v.intValuation w ≤ WithZero.exp (-((m + M : ℕ) : ℤ)) :=
      (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v w (m + M)).mpr hw
    calc IsDedekindDomain.HeightOneSpectrum.valuation K v
          (a - algebraMap (NumberField.RingOfIntegers K) K r)
        = IsDedekindDomain.HeightOneSpectrum.valuation K v
            (a - algebraMap (NumberField.RingOfIntegers K) K r) *
            (WithZero.exp (-(m : ℤ)) * WithZero.exp (m : ℤ)) := by
          rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, mul_one]
      _ = (IsDedekindDomain.HeightOneSpectrum.valuation K v
            (a - algebraMap (NumberField.RingOfIntegers K) K r) * v.intValuation ya) *
            WithZero.exp (m : ℤ) := by
          rw [← hexpm, mul_assoc]
      _ = v.intValuation w * WithZero.exp (m : ℤ) := by rw [hV]
      _ ≤ WithZero.exp (-((m + M : ℕ) : ℤ)) * WithZero.exp (m : ℤ) :=
          mul_le_mul_left hwb _
      _ = WithZero.exp (-(M : ℤ)) := by
          rw [← WithZero.exp_add]
          congr 1
          push_cast
          ring
  have h_approx_int : ∀ (z : v.adicCompletion K), Valued.v z ≤ 1 → ∀ (M : ℕ),
      ∃ r : NumberField.RingOfIntegers K,
        Valued.v (z - algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K r)) ≤ WithZero.exp (-(M : ℤ)) := by
    intro z hz M
    have hdense : DenseRange (fun y : K => algebraMap K (v.adicCompletion K) y) := by
      letI : Valued K (WithZero (Multiplicative ℤ)) :=
        IsDedekindDomain.HeightOneSpectrum.adicValued (K := K) v
      exact UniformSpace.Completion.denseRange_coe
    let γ : (WithZero (Multiplicative ℤ))ˣ :=
      Units.mk0 (WithZero.exp (-(M : ℤ))) WithZero.exp_ne_zero
    have hnhds : {y : v.adicCompletion K |
        Valued.v (y - z) < (γ : WithZero (Multiplicative ℤ))} ∈ nhds z :=
      Valued.mem_nhds.mpr ⟨γ, subset_rfl⟩
    obtain ⟨u, hu1, k, hk⟩ := mem_closure_iff_nhds.mp (hdense z) _ hnhds
    have hkl : Valued.v (z - algebraMap K (v.adicCompletion K) k) ≤ WithZero.exp (-(M : ℤ)) := by
      dsimp only at hk
      rw [Valuation.map_sub_swap, hk]
      exact le_of_lt hu1
    have hexple : WithZero.exp (-(M : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
      rw [← WithZero.exp_zero]
      exact WithZero.exp_le_exp.mpr (by omega)
    have hvc : ∀ x : K, Valued.v (algebraMap K (v.adicCompletion K) x) =
        IsDedekindDomain.HeightOneSpectrum.valuation K v x :=
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v
    have hvk : IsDedekindDomain.HeightOneSpectrum.valuation K v k ≤ 1 := by
      rw [← hvc k]
      have hsplit : algebraMap K (v.adicCompletion K) k =
          z - (z - algebraMap K (v.adicCompletion K) k) := by ring
      rw [hsplit]
      exact le_trans (Valuation.map_sub Valued.v _ _) (max_le hz (le_trans hkl hexple))
    obtain ⟨r, hr⟩ := h_approx_K k hvk M
    refine ⟨r, ?_⟩
    have hsplit2 : z - algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K r) =
        (z - algebraMap K (v.adicCompletion K) k) +
          algebraMap K (v.adicCompletion K)
            (k - algebraMap (NumberField.RingOfIntegers K) K r) := by
      rw [map_sub]; ring
    rw [hsplit2]
    refine le_trans (Valuation.map_add Valued.v _ _) (max_le hkl ?_)
    rw [hvc]
    exact hr
  clear h_approx_K
  have h_quad_root : ∀ (b c x₀ : v.adicCompletion K),
      Valued.v (2 * x₀ + b) = (1 : WithZero (Multiplicative ℤ)) →
      Valued.v (x₀ ^ 2 + b * x₀ + c) < (1 : WithZero (Multiplicative ℤ)) →
      ∃ x : v.adicCompletion K, x ^ 2 + b * x + c = 0 := by
    intro b c x₀ hder hval
    have hdbl : ∀ t : v.adicCompletion K, Valued.v (2 * t) ≤ Valued.v t := by
      intro t
      have e : (2 : v.adicCompletion K) * t = t + t := by ring
      have h : Valued.v (t + t) ≤ max (Valued.v t) (Valued.v t) := Valuation.map_add _ _ _
      rw [max_self] at h
      rw [e]
      exact h
    have hstep : ∀ y : v.adicCompletion K,
        Valued.v (2 * y + b) = (1 : WithZero (Multiplicative ℤ)) →
        Valued.v (y ^ 2 + b * y + c) < (1 : WithZero (Multiplicative ℤ)) →
        Valued.v (2 * (y - (y ^ 2 + b * y + c) / (2 * y + b)) + b)
            = (1 : WithZero (Multiplicative ℤ)) ∧
        Valued.v ((y - (y ^ 2 + b * y + c) / (2 * y + b)) ^ 2
              + b * (y - (y ^ 2 + b * y + c) / (2 * y + b)) + c)
            = Valued.v (y ^ 2 + b * y + c) ^ 2 ∧
        Valued.v (y - (y ^ 2 + b * y + c) / (2 * y + b) - y)
            = Valued.v (y ^ 2 + b * y + c) := by
      intro y hD hP
      have hDne : (2 : v.adicCompletion K) * y + b ≠ 0 := by
        intro hcon
        rw [hcon, map_zero] at hD
        exact zero_ne_one hD
      have ht : Valued.v ((y ^ 2 + b * y + c) / (2 * y + b))
          = Valued.v (y ^ 2 + b * y + c) := by
        rw [map_div₀, hD, div_one]
      refine ⟨?_, ?_, ?_⟩
      · have e : 2 * (y - (y ^ 2 + b * y + c) / (2 * y + b)) + b
            = (2 * y + b) - 2 * ((y ^ 2 + b * y + c) / (2 * y + b)) := by ring
        have hlt : Valued.v (2 * ((y ^ 2 + b * y + c) / (2 * y + b)))
            < Valued.v (2 * y + b) := by
          refine lt_of_le_of_lt (hdbl _) ?_
          rw [ht, hD]
          exact hP
        rw [e, Valuation.map_sub_eq_of_lt_left _ hlt, hD]
      · have hcancel : (y ^ 2 + b * y + c) / (2 * y + b) * (2 * y + b)
            = y ^ 2 + b * y + c := div_mul_cancel₀ _ hDne
        have key : (y - (y ^ 2 + b * y + c) / (2 * y + b)) ^ 2
              + b * (y - (y ^ 2 + b * y + c) / (2 * y + b)) + c
            = ((y ^ 2 + b * y + c) / (2 * y + b)) ^ 2 := by
          linear_combination -hcancel
        rw [key, Valuation.map_pow, ht]
      · have key : y - (y ^ 2 + b * y + c) / (2 * y + b) - y
            = -((y ^ 2 + b * y + c) / (2 * y + b)) := by ring
        rw [key, Valuation.map_neg, ht]
    have hdecay : ∀ δ γ : WithZero (Multiplicative ℤ), δ < 1 → γ ≠ 0 →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → δ ^ (2 ^ n) < γ := by
      intro δ γ hδ hγ
      rcases eq_or_ne δ 0 with h0 | h0
      · refine ⟨0, fun n _ => ?_⟩
        rw [h0, zero_pow (Nat.two_pow_pos n).ne']
        exact zero_lt_iff.mpr hγ
      · obtain ⟨a, rfl⟩ : ∃ a : ℤ, δ = ((Multiplicative.ofAdd a : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
          obtain ⟨g, hg⟩ := WithZero.ne_zero_iff_exists.mp h0
          exact ⟨Multiplicative.toAdd g, hg.symm⟩
        obtain ⟨β, rfl⟩ : ∃ β : ℤ, γ = ((Multiplicative.ofAdd β : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
          obtain ⟨g, hg⟩ := WithZero.ne_zero_iff_exists.mp hγ
          exact ⟨Multiplicative.toAdd g, hg.symm⟩
        have ha : a < 0 := WithZero.coe_lt_one.mp hδ
        have hpow : ∀ k : ℕ,
            ((Multiplicative.ofAdd a : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ k
              = ((Multiplicative.ofAdd ((k : ℤ) * a) : Multiplicative ℤ) :
                  WithZero (Multiplicative ℤ)) := by
          intro k
          rw [← WithZero.coe_pow]
          congr 1
        refine ⟨(-β).toNat + 1, fun n hn => ?_⟩
        rw [hpow, WithZero.coe_lt_coe]
        have hbk : -β < ((2 ^ n : ℕ) : ℤ) := by
          have hx : (-β).toNat < n := by omega
          have h1 : (-β).toNat < 2 ^ n := lt_trans hx Nat.lt_two_pow_self
          have h2' : ((-β).toNat : ℤ) < ((2 ^ n : ℕ) : ℤ) := by exact_mod_cast h1
          exact lt_of_le_of_lt (Int.self_le_toNat _) h2'
        have hkpos : (0 : ℤ) ≤ ((2 ^ n : ℕ) : ℤ) := Int.natCast_nonneg _
        have ha1 : a ≤ -1 := by omega
        have hle : ((2 ^ n : ℕ) : ℤ) * a ≤ ((2 ^ n : ℕ) : ℤ) * (-1) :=
          mul_le_mul_of_nonneg_left ha1 hkpos
        have hgoal : ((2 ^ n : ℕ) : ℤ) * a < β := by linarith
        exact hgoal
    obtain ⟨ε, hεdef⟩ : ∃ ε : WithZero (Multiplicative ℤ),
        ε = Valued.v (x₀ ^ 2 + b * x₀ + c) := ⟨_, rfl⟩
    have hε : ε < (1 : WithZero (Multiplicative ℤ)) := by rw [hεdef]; exact hval
    obtain ⟨f, hf0, hfs⟩ : ∃ f : ℕ → v.adicCompletion K, f 0 = x₀ ∧
        ∀ n : ℕ, f (n + 1) = f n - (f n ^ 2 + b * f n + c) / (2 * f n + b) :=
      ⟨fun n => Nat.rec (motive := fun _ => v.adicCompletion K) x₀
        (fun _ y => y - (y ^ 2 + b * y + c) / (2 * y + b)) n, rfl, fun _ => rfl⟩
    have hinv : ∀ n : ℕ, Valued.v (2 * f n + b) = (1 : WithZero (Multiplicative ℤ)) ∧
        Valued.v (f n ^ 2 + b * f n + c) = ε ^ (2 ^ n) := by
      intro n
      induction n with
      | zero =>
        refine ⟨by rw [hf0]; exact hder, ?_⟩
        rw [hf0, pow_zero, pow_one, hεdef]
      | succ n ih =>
        have hlt : Valued.v (f n ^ 2 + b * f n + c) < (1 : WithZero (Multiplicative ℤ)) := by
          rw [ih.2]
          exact pow_lt_one₀ zero_le' hε (Nat.two_pow_pos n).ne'
        obtain ⟨s1, s2, -⟩ := hstep (f n) ih.1 hlt
        refine ⟨by rw [hfs n]; exact s1, ?_⟩
        rw [hfs n, s2, ih.2, ← pow_mul]
        congr 1
    have hdiff : ∀ n : ℕ, Valued.v (f (n + 1) - f n) = ε ^ (2 ^ n) := by
      intro n
      have hlt : Valued.v (f n ^ 2 + b * f n + c) < (1 : WithZero (Multiplicative ℤ)) := by
        rw [(hinv n).2]
        exact pow_lt_one₀ zero_le' hε (Nat.two_pow_pos n).ne'
      obtain ⟨-, -, s3⟩ := hstep (f n) (hinv n).1 hlt
      rw [hfs n, s3, (hinv n).2]
    have hCauchy : Cauchy (Filter.map f Filter.atTop) := by
      refine Valued.cauchy_iff.mpr ⟨inferInstance, ?_⟩
      intro γ
      obtain ⟨N, hN⟩ := hdecay ε (γ : WithZero (Multiplicative ℤ)) hε (Units.ne_zero γ)
      have htel : ∀ m : ℕ, N ≤ m → Valued.v (f m - f N) < (γ : WithZero (Multiplicative ℤ)) := by
        intro m hm
        induction m, hm using Nat.le_induction with
        | base =>
          rw [sub_self, map_zero]
          exact zero_lt_iff.mpr (Units.ne_zero γ)
        | succ m hm ih =>
          have e : f (m + 1) - f N = (f (m + 1) - f m) + (f m - f N) := by ring
          rw [e]
          refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ih)
          rw [hdiff m]
          exact hN m hm
      refine ⟨f '' (Set.Ici N), Filter.image_mem_map (Filter.Ici_mem_atTop N), ?_⟩
      rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
      have e : f j - f i = (f j - f N) - (f i - f N) := by ring
      rw [e]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt (htel j hj) (htel i hi))
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hCauchy
    have hPlim : Filter.Tendsto (fun n : ℕ => f n ^ 2 + b * f n + c) Filter.atTop
        (nhds (x ^ 2 + b * x + c)) :=
      ((hx.pow 2).add (tendsto_const_nhds.mul hx)).add tendsto_const_nhds
    have hzero : Filter.Tendsto (fun n : ℕ => f n ^ 2 + b * f n + c) Filter.atTop
        (nhds (0 : v.adicCompletion K)) := by
      rw [Filter.tendsto_def]
      intro s hs
      obtain ⟨γ, hγs⟩ := Valued.mem_nhds_zero.mp hs
      obtain ⟨N, hN⟩ := hdecay ε (γ : WithZero (Multiplicative ℤ)) hε (Units.ne_zero γ)
      refine Filter.mem_of_superset (Filter.Ici_mem_atTop N) ?_
      intro n hn
      apply hγs
      show Valued.v (f n ^ 2 + b * f n + c) < (γ : WithZero (Multiplicative ℤ))
      rw [(hinv n).2]
      exact hN n hn
    exact ⟨x, tendsto_nhds_unique hPlim hzero⟩
  have h_sq_lt_four : ∀ (b x : v.adicCompletion K), Valued.v x = 1 →
      Valued.v (b - x ^ 2) < Valued.v (4 : v.adicCompletion K) →
      ∃ y : v.adicCompletion K, y ^ 2 = b := by
    intro b x hx hb
    have h4pos : (0 : WithZero (Multiplicative ℤ)) < Valued.v (4 : v.adicCompletion K) :=
      lt_of_le_of_lt zero_le' hb
    have h4ne : (4 : v.adicCompletion K) ≠ 0 :=
      (Valuation.ne_zero_iff Valued.v).mp (ne_of_gt h4pos)
    have hx0 : x ≠ 0 := by
      refine (Valuation.ne_zero_iff Valued.v).mp ?_
      rw [hx]
      exact one_ne_zero
    have hv4x : Valued.v ((4 : v.adicCompletion K) * x ^ 2)
        = Valued.v (4 : v.adicCompletion K) := by
      rw [map_mul, map_pow, hx, one_pow, mul_one]
    obtain ⟨ζ, hζdef⟩ :
        ∃ z : v.adicCompletion K, z = (b - x ^ 2) / ((4 : v.adicCompletion K) * x ^ 2) :=
      ⟨_, rfl⟩
    have hζ : Valued.v ζ < (1 : WithZero (Multiplicative ℤ)) := by
      rw [hζdef, map_div₀, hv4x]
      exact (div_lt_one₀ h4pos).mpr hb
    obtain ⟨W, hW⟩ := h_quad_root 1 (-ζ) 0
      (by
        rw [show (2 : v.adicCompletion K) * 0 + 1 = 1 by ring]
        exact map_one _)
      (by
        rw [show (0 : v.adicCompletion K) ^ 2 + 1 * 0 + -ζ = -ζ by ring, Valuation.map_neg]
        exact hζ)
    have hWz : W ^ 2 + W = ζ := by linear_combination hW
    have key : (4 : v.adicCompletion K) * x ^ 2 * (W ^ 2 + W) = b - x ^ 2 := by
      rw [hWz, hζdef]
      field_simp
    exact ⟨x * (1 + 2 * W), by linear_combination key⟩
  clear h_quad_root
  have h2ne : (2 : v.adicCompletion K) ≠ 0 := by
    have hK2 : (2 : K) ≠ 0 := by norm_num
    intro hcon
    apply hK2
    apply (algebraMap K (v.adicCompletion K)).injective
    rw [map_ofNat, map_zero]
    exact hcon
  have h_hilb_solv : ∀ (a b : v.adicCompletion K), a ≠ 0 →
      ((∃ x₀ y₀ : v.adicCompletion K, a * x₀ ^ 2 + b * y₀ ^ 2 = 1) ↔
        (∃ z t : v.adicCompletion K, z ^ 2 - b * t ^ 2 = a)) := by
    intro a b ha
    constructor
    · rintro ⟨x₀, y₀, h⟩
      by_cases hx₀ : x₀ = 0
      · subst hx₀
        have hb : b * y₀ ^ 2 = 1 := by linear_combination h
        have h2i : 2 * (2 : v.adicCompletion K)⁻¹ = 1 := mul_inv_cancel₀ h2ne
        refine ⟨(a + 1) * (2 : v.adicCompletion K)⁻¹,
          (1 - a) * y₀ * (2 : v.adicCompletion K)⁻¹, ?_⟩
        linear_combination (-(1 - a) ^ 2 * ((2 : v.adicCompletion K)⁻¹) ^ 2) * hb +
          (a * (2 * (2 : v.adicCompletion K)⁻¹ + 1)) * h2i
      · have hu : x₀ * x₀⁻¹ = 1 := mul_inv_cancel₀ hx₀
        refine ⟨x₀⁻¹, y₀ * x₀⁻¹, ?_⟩
        linear_combination (-(x₀⁻¹) ^ 2) * h + (a * (x₀ * x₀⁻¹ + 1)) * hu
    · rintro ⟨z, t, h⟩
      by_cases hz : z = 0
      · subst hz
        have hbt : b * t ^ 2 = -a := by linear_combination -h
        have h2a : 2 * a * (2 * a)⁻¹ = 1 := mul_inv_cancel₀ (mul_ne_zero h2ne ha)
        refine ⟨(1 + a) * (2 * a)⁻¹, t * (a - 1) * (2 * a)⁻¹, ?_⟩
        linear_combination ((a - 1) ^ 2 * ((2 * a)⁻¹) ^ 2) * hbt +
          (2 * a * (2 * a)⁻¹ + 1) * h2a
      · have hw : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
        refine ⟨z⁻¹, t * z⁻¹, ?_⟩
        linear_combination (-(z⁻¹) ^ 2) * h + (z * z⁻¹ + 1) * hw
  have h_hilb_eq_one_iff : ∀ (a b : v.adicCompletion K), a ≠ 0 →
      (hilbLoc v a b = 1 ↔ ∃ z t : v.adicCompletion K, z ^ 2 - b * t ^ 2 = a) := by
    intro a b ha
    rw [← h_hilb_solv a b ha]
    dsimp [hilbLoc]
    split_ifs with h
    · exact ⟨fun _ => h, fun _ => rfl⟩
    · refine ⟨fun hcon => absurd hcon (by decide), fun h' => absurd h' h⟩
  clear h_hilb_solv
  have hilbLoc_symm : ∀ (a b : v.adicCompletion K), hilbLoc v a b = hilbLoc v b a := by
    intro a b
    simp only [hilbLoc]
    congr 1
    exact propext ⟨fun ⟨x₀, y₀, hxy⟩ => ⟨y₀, x₀, by linear_combination hxy⟩,
      fun ⟨x₀, y₀, hxy⟩ => ⟨y₀, x₀, by linear_combination hxy⟩⟩
  have hv2ne : Valued.v (2 : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).mpr h2ne
  have hv2le : Valued.v (2 : v.adicCompletion K) ≤ 1 := by
    have h11 : (2 : v.adicCompletion K) = 1 + 1 := by norm_num
    rw [h11]
    refine le_trans (Valuation.map_add _ _ _) ?_
    rw [Valuation.map_one, max_self]
  let m2 : ℤ := WithZero.log (Valued.v (2 : v.adicCompletion K))
  have hm2_exp : (WithZero.exp m2 : WithZero (Multiplicative ℤ))
      = Valued.v (2 : v.adicCompletion K) := WithZero.exp_log hv2ne
  have hm2_le : m2 ≤ 0 := by
    refine WithZero.exp_le_exp.mp ?_
    rw [hm2_exp, WithZero.exp_zero]
    exact hv2le
  let e : ℕ := (-m2).toNat
  have h2e : Valued.v (2 : v.adicCompletion K) = WithZero.exp (-(e : ℤ)) := by
    have hMe : -(e : ℤ) = m2 := by dsimp [e]; omega
    rw [hMe, hm2_exp]
  have h4e : Valued.v (4 : v.adicCompletion K) = WithZero.exp (-(2 * (e : ℤ))) := by
    have h44 : (4 : v.adicCompletion K) = 2 * 2 := by norm_num
    rw [h44, map_mul, h2e, ← WithZero.exp_add]
    congr 1
    ring
  have hcoe : ∀ k : K, Valued.v (algebraMap K (v.adicCompletion K) k)
      = IsDedekindDomain.HeightOneSpectrum.valuation K v k :=
    fun k => IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
  have hN1 : ∀ y : NumberField.RingOfIntegers K,
      Valued.v (algebraMap K (v.adicCompletion K)
        (algebraMap (NumberField.RingOfIntegers K) K y)) ≤ 1 := by
    intro y
    rw [hcoe]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one v y
  have hN2 : ∀ y : NumberField.RingOfIntegers K, y ∉ v.asIdeal →
      Valued.v (algebraMap K (v.adicCompletion K)
        (algebraMap (NumberField.RingOfIntegers K) K y)) = 1 := by
    intro y hy
    have hle := hN1 y
    have hnlt : ¬ (IsDedekindDomain.HeightOneSpectrum.valuation K v
        (algebraMap (NumberField.RingOfIntegers K) K y) < 1) := by
      intro hcon
      exact hy ((IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem v y).mp hcon)
    rw [hcoe] at hle ⊢
    exact le_antisymm hle (not_lt.mp hnlt)
  have hexp1 : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  have hN0 : ∀ z : v.adicCompletion K, z ≠ 0 → ∃ m : ℤ, Valued.v z = WithZero.exp m := by
    intro z hz
    have hvne : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).mpr hz
    exact ⟨WithZero.log (Valued.v z), (WithZero.exp_log hvne).symm⟩
  have h_exists_AS : ∃ r : NumberField.RingOfIntegers K,
      ∀ s : NumberField.RingOfIntegers K, s ^ 2 + s - r ∉ v.asIdeal := by
    haveI : v.asIdeal.IsMaximal := v.isMaximal
    letI : Field (NumberField.RingOfIntegers K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
    haveI : Finite (NumberField.RingOfIntegers K ⧸ v.asIdeal) :=
      Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
    obtain ⟨rbar, hrbar⟩ :
        ∃ rbar : NumberField.RingOfIntegers K ⧸ v.asIdeal,
          ∀ sbar : NumberField.RingOfIntegers K ⧸ v.asIdeal, sbar ^ 2 + sbar ≠ rbar := by
      by_contra hcon
      push_neg at hcon
      have hsurj : Function.Surjective
          (fun x : NumberField.RingOfIntegers K ⧸ v.asIdeal => x ^ 2 + x) := by
        intro b
        obtain ⟨a, ha⟩ := hcon b
        exact ⟨a, ha⟩
      have hinj : Function.Injective
          (fun x : NumberField.RingOfIntegers K ⧸ v.asIdeal => x ^ 2 + x) :=
        Finite.injective_iff_surjective.mpr hsurj
      have hcoll : ((0 : NumberField.RingOfIntegers K ⧸ v.asIdeal) ^ 2 + 0)
          = ((-1 : NumberField.RingOfIntegers K ⧸ v.asIdeal) ^ 2 + (-1)) := by
        ring
      have h01 : (0 : NumberField.RingOfIntegers K ⧸ v.asIdeal) = -1 := hinj hcoll
      exact one_ne_zero
        (show (1 : NumberField.RingOfIntegers K ⧸ v.asIdeal) = 0 by linear_combination h01)
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective rbar
    refine ⟨r, ?_⟩
    intro s hmem
    have h0 : (Ideal.Quotient.mk v.asIdeal) (s ^ 2 + s - r) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [map_sub, map_add, map_pow, hr, sub_eq_zero] at h0
    exact hrbar (Ideal.Quotient.mk v.asIdeal s) h0
  obtain ⟨r_AS, hr_AS⟩ := h_exists_AS
  let ρ : v.adicCompletion K := algebraMap K (v.adicCompletion K)
    (algebraMap (NumberField.RingOfIntegers K) K r_AS)
  have hρ1 : Valued.v ρ ≤ 1 := hN1 r_AS
  let b : v.adicCompletion K := 1 + 4 * ρ
  have hb_val : Valued.v b = 1 := by
    have hr14 : 1 + 4 * r_AS ∉ v.asIdeal := by
      intro hmem
      have hmul : r_AS * (1 + 4 * r_AS) ∈ v.asIdeal := v.asIdeal.mul_mem_left r_AS hmem
      have heq : r_AS * (1 + 4 * r_AS) = (2 * r_AS) ^ 2 + (2 * r_AS) - r_AS := by ring
      rw [heq] at hmul
      exact hr_AS (2 * r_AS) hmul
    have hbeq : b = algebraMap K (v.adicCompletion K)
        (algebraMap (NumberField.RingOfIntegers K) K (1 + 4 * r_AS)) := by
      simp only [b, ρ, map_add, map_one, map_mul, map_ofNat]
    rw [hbeq]
    exact hN2 (1 + 4 * r_AS) hr14
  have hb0 : b ≠ 0 :=
    (Valuation.ne_zero_iff Valued.v).mp (by rw [hb_val]; exact one_ne_zero)
  have hb1 : Valued.v (b - 1) ≤ WithZero.exp (-(2 * (e : ℤ))) := by
    have hb1_eq : b - 1 = 4 * ρ := by dsimp [b]; ring
    rw [hb1_eq, map_mul, h4e]
    calc WithZero.exp (-(2 * (e : ℤ))) * Valued.v ρ
        ≤ WithZero.exp (-(2 * (e : ℤ))) * 1 := mul_le_mul' le_rfl hρ1
      _ = WithZero.exp (-(2 * (e : ℤ))) := mul_one _
  have hAS : ∀ ζ : v.adicCompletion K, Valued.v ζ ≤ 1 →
      Valued.v (ζ ^ 2 + ζ - ρ) = 1 := by
    intro ζ hζ
    obtain ⟨y, hy⟩ := h_approx_int ζ hζ 1
    let u : v.adicCompletion K := algebraMap K (v.adicCompletion K)
      (algebraMap (NumberField.RingOfIntegers K) K y)
    have hy1 : Valued.v (ζ - u) ≤ WithZero.exp (-1 : ℤ) := by
      simpa [u] using hy
    have hu1 : Valued.v u ≤ 1 := hN1 y
    have hA1 : Valued.v (u ^ 2 + u - ρ) = 1 := by
      have hAeq : u ^ 2 + u - ρ = algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K (y ^ 2 + y - r_AS)) := by
        dsimp [u, ρ]
        simp only [map_sub, map_add, map_pow]
      rw [hAeq]
      exact hN2 _ (hr_AS y)
    have hsum : Valued.v (ζ + u + 1) ≤ 1 := by
      refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
      · exact le_trans (Valuation.map_add _ _ _) (max_le hζ hu1)
      · simp
    have hD : Valued.v ((ζ ^ 2 + ζ - ρ) - (u ^ 2 + u - ρ))
        < Valued.v (u ^ 2 + u - ρ) := by
      have hfac : (ζ ^ 2 + ζ - ρ) - (u ^ 2 + u - ρ) = (ζ - u) * (ζ + u + 1) := by ring
      rw [hfac, map_mul, hA1]
      calc Valued.v (ζ - u) * Valued.v (ζ + u + 1)
          ≤ WithZero.exp (-1 : ℤ) * 1 := mul_le_mul' hy1 hsum
        _ = WithZero.exp (-1 : ℤ) := mul_one _
        _ < 1 := hexp1
    have hsplit : ζ ^ 2 + ζ - ρ
        = (u ^ 2 + u - ρ) + ((ζ ^ 2 + ζ - ρ) - (u ^ 2 + u - ρ)) := by ring
    rw [hsplit, Valuation.map_add_eq_of_lt_left _ hD, hA1]
  have hPar : ∀ w : v.adicCompletion K, ∃ k : ℤ,
      Valued.v (w ^ 2 - b) = WithZero.exp (2 * k) := by
    intro w
    obtain ⟨ζ, hζw⟩ : ∃ ζ : v.adicCompletion K, w = 1 + 2 * ζ :=
      ⟨(w - 1) / 2, by field_simp; ring⟩
    have hid : w ^ 2 - b = 4 * (ζ ^ 2 + ζ - ρ) := by
      dsimp [b]; rw [hζw]; ring
    rw [hid, map_mul, h4e]
    by_cases hle : Valued.v ζ ≤ 1
    · refine ⟨-(e : ℤ), ?_⟩
      rw [hAS ζ hle, mul_one]
      congr 1
      ring
    · have hgt : (1 : WithZero (Multiplicative ℤ)) < Valued.v ζ := not_le.mp hle
      have hζ0 : ζ ≠ 0 := by
        intro h
        rw [h, map_zero] at hgt
        exact absurd hgt (not_lt.mpr zero_le')
      obtain ⟨j, hj⟩ := hN0 ζ hζ0
      have hj0 : 0 < j := by
        rw [hj, ← WithZero.exp_zero] at hgt
        exact WithZero.exp_lt_exp.mp hgt
      have hsq : Valued.v (ζ ^ 2) = WithZero.exp (j + j) := by
        rw [map_pow, hj, pow_two, ← WithZero.exp_add]
      have hlt1 : Valued.v ζ < Valued.v (ζ ^ 2) := by
        rw [hj, hsq, WithZero.exp_lt_exp]
        omega
      have hs1 : Valued.v (ζ ^ 2 + ζ) = WithZero.exp (j + j) := by
        rw [Valuation.map_add_eq_of_lt_left _ hlt1, hsq]
      have hρlt : Valued.v ρ < Valued.v (ζ ^ 2 + ζ) := by
        refine lt_of_le_of_lt hρ1 ?_
        rw [hs1, ← WithZero.exp_zero, WithZero.exp_lt_exp]
        omega
      have hfin : Valued.v (ζ ^ 2 + ζ - ρ) = WithZero.exp (j + j) := by
        rw [Valuation.map_sub_eq_of_lt_left _ hρlt, hs1]
      refine ⟨j - (e : ℤ), ?_⟩
      rw [hfin, ← WithZero.exp_add]
      congr 1
      ring
  clear hAS
  have hbeven : ∀ z t : v.adicCompletion K, z ^ 2 - b * t ^ 2 ≠ 0 →
      ∃ k : ℤ, Valued.v (z ^ 2 - b * t ^ 2) = WithZero.exp (2 * k) := by
    intro z t hzt
    rcases eq_or_ne t 0 with ht | ht
    · subst ht
      have hz2 : z ^ 2 - b * (0 : v.adicCompletion K) ^ 2 = z ^ 2 := by ring
      rw [hz2] at hzt ⊢
      have hz : z ≠ 0 := fun h => hzt (by rw [h]; ring)
      obtain ⟨m, hm⟩ := hN0 z hz
      refine ⟨m, ?_⟩
      rw [map_pow, hm, pow_two, ← WithZero.exp_add]
      congr 1
      ring
    · obtain ⟨w, hw⟩ : ∃ w : v.adicCompletion K, z = w * t := ⟨z / t, by field_simp⟩
      have hzt2 : z ^ 2 - b * t ^ 2 = t ^ 2 * (w ^ 2 - b) := by rw [hw]; ring
      obtain ⟨k₀, hk₀⟩ := hPar w
      obtain ⟨n, hn⟩ := hN0 t ht
      refine ⟨n + k₀, ?_⟩
      rw [hzt2, map_mul, hk₀, map_pow, hn, pow_two, ← WithZero.exp_add, ← WithZero.exp_add]
      congr 1
      ring
  clear hPar hr_AS hρ1
  have h_even_defect : ∀ (s : ℕ) (a c : v.adicCompletion K),
      Valued.v a = 1 →
      (∀ u : v.adicCompletion K, Valued.v u = 1 →
        ∃ z t : v.adicCompletion K, z ^ 2 - a * t ^ 2 = u) →
      Valued.v (a - c ^ 2) = WithZero.exp (-(s : ℤ)) →
      s < 2 * e →
      Even s := by
    intro s a c ha haur hs hlt
    have mulN : ∀ x p q : v.adicCompletion K,
        (∃ z t : v.adicCompletion K, z ^ 2 - x * t ^ 2 = p) →
        (∃ z t : v.adicCompletion K, z ^ 2 - x * t ^ 2 = q) →
        ∃ z t : v.adicCompletion K, z ^ 2 - x * t ^ 2 = p * q := by
      rintro x p q ⟨z₁, t₁, hp⟩ ⟨z₂, t₂, hq⟩
      refine ⟨z₁ * z₂ + x * t₁ * t₂, z₁ * t₂ + z₂ * t₁, ?_⟩
      rw [← hp, ← hq]
      ring
    have invN : ∀ x p : v.adicCompletion K, p ≠ 0 →
        (∃ z t : v.adicCompletion K, z ^ 2 - x * t ^ 2 = p) →
        ∃ z t : v.adicCompletion K, z ^ 2 - x * t ^ 2 = 1 / p := by
      rintro x p hp ⟨z₁, t₁, h₁⟩
      refine ⟨z₁ / p, t₁ / p, ?_⟩
      field_simp
      linear_combination h₁
    have recip : ∀ x y : v.adicCompletion K, y ≠ 0 →
        (∃ z t : v.adicCompletion K, z ^ 2 - x * t ^ 2 = y) →
        ∃ z t : v.adicCompletion K, z ^ 2 - y * t ^ 2 = x := by
      rintro x y hy ⟨z₀, t₀, h₀⟩
      by_cases ht : t₀ = 0
      · subst ht
        have hy' : y = z₀ ^ 2 := by linear_combination -h₀
        have hz₀ : z₀ ≠ 0 := by
          intro hcon
          apply hy
          rw [hy', hcon]
          ring
        refine ⟨(x + 1) / 2, (x - 1) / (2 * z₀), ?_⟩
        rw [hy']
        field_simp
        ring
      · refine ⟨z₀ / t₀, 1 / t₀, ?_⟩
        field_simp
        linear_combination h₀
    have hexp_lt : WithZero.exp (-(2 * (e : ℤ)))
        < (WithZero.exp (-(s : ℤ)) : WithZero (Multiplicative ℤ)) := by
      rw [WithZero.exp_lt_exp]
      omega
    have ha0 : a ≠ 0 :=
      (Valuation.ne_zero_iff Valued.v).mp (by rw [ha]; exact one_ne_zero)
    have hθ : Valued.v (c ^ 2 - a) = WithZero.exp (-(s : ℤ)) := by
      have hneg : c ^ 2 - a = -(a - c ^ 2) := by ring
      rw [hneg, Valuation.map_neg, hs]
    have hθ0 : c ^ 2 - a ≠ 0 :=
      (Valuation.ne_zero_iff Valued.v).mp (by rw [hθ]; exact WithZero.exp_ne_zero)
    have hdiffval : Valued.v (-(a * (b - 1))) < Valued.v (c ^ 2 - a) := by
      rw [Valuation.map_neg, map_mul, ha, one_mul, hθ]
      exact lt_of_le_of_lt hb1 hexp_lt
    have hy : Valued.v (c ^ 2 - a * b) = WithZero.exp (-(s : ℤ)) := by
      have heq : c ^ 2 - a * b = (c ^ 2 - a) + (-(a * (b - 1))) := by ring
      rw [heq, Valuation.map_add_eq_of_lt_left Valued.v hdiffval, hθ]
    have hy0 : c ^ 2 - a * b ≠ 0 :=
      (Valuation.ne_zero_iff Valued.v).mp (by rw [hy]; exact WithZero.exp_ne_zero)
    have huval : Valued.v ((c ^ 2 - a * b) / (c ^ 2 - a)) = 1 := by
      rw [map_div₀, hy, hθ, div_self WithZero.exp_ne_zero]
    have huNa : ∃ z t : v.adicCompletion K,
        z ^ 2 - a * t ^ 2 = (c ^ 2 - a * b) / (c ^ 2 - a) := haur _ huval
    have hθNa : ∃ z t : v.adicCompletion K, z ^ 2 - a * t ^ 2 = c ^ 2 - a := ⟨c, 1, by ring⟩
    have hyNa : ∃ z t : v.adicCompletion K, z ^ 2 - a * t ^ 2 = c ^ 2 - a * b := by
      have hprod := mulN a _ _ huNa hθNa
      have heq : (c ^ 2 - a * b) / (c ^ 2 - a) * (c ^ 2 - a) = c ^ 2 - a * b :=
        div_mul_cancel₀ _ hθ0
      rwa [heq] at hprod
    have haNy : ∃ z t : v.adicCompletion K, z ^ 2 - (c ^ 2 - a * b) * t ^ 2 = a :=
      recip a (c ^ 2 - a * b) hy0 hyNa
    have hyNab : ∃ z t : v.adicCompletion K, z ^ 2 - a * b * t ^ 2 = c ^ 2 - a * b :=
      ⟨c, 1, by ring⟩
    have habNy : ∃ z t : v.adicCompletion K, z ^ 2 - (c ^ 2 - a * b) * t ^ 2 = a * b :=
      recip (a * b) (c ^ 2 - a * b) hy0 hyNab
    have hinvaNy : ∃ z t : v.adicCompletion K, z ^ 2 - (c ^ 2 - a * b) * t ^ 2 = 1 / a :=
      invN (c ^ 2 - a * b) a ha0 haNy
    have hbNy : ∃ z t : v.adicCompletion K, z ^ 2 - (c ^ 2 - a * b) * t ^ 2 = b := by
      have hprod := mulN (c ^ 2 - a * b) _ _ habNy hinvaNy
      have heq : a * b * (1 / a) = b := by field_simp
      rwa [heq] at hprod
    obtain ⟨z₅, t₅, h₅⟩ := recip (c ^ 2 - a * b) b hb0 hbNy
    have hne : z₅ ^ 2 - b * t₅ ^ 2 ≠ 0 := by
      rw [h₅]
      exact hy0
    obtain ⟨k, hk⟩ := hbeven z₅ t₅ hne
    rw [h₅, hy] at hk
    have hkk : -(s : ℤ) = 2 * k := WithZero.exp_inj.mp hk
    exact Nat.even_iff.mpr (by omega)
  have htors : ∀ γ : WithZero (Multiplicative ℤ), γ ^ 2 = 1 → γ = 1 := by
    intro γ hγ
    have h0 : γ ≠ 0 := by
      intro hh
      rw [hh] at hγ
      simp at hγ
    have hk := WithZero.exp_log h0
    rw [← hk] at hγ ⊢
    rw [← WithZero.exp_nsmul, ← WithZero.exp_zero] at hγ
    have hz := WithZero.exp_inj.mp hγ
    simp only [nsmul_eq_mul, Nat.cast_ofNat] at hz
    rw [show WithZero.log γ = 0 by omega, WithZero.exp_zero]
  have h_even_step : ∀ (m : ℕ), m < e →
      ∀ (a c : v.adicCompletion K), Valued.v a = 1 → Valued.v c = 1 →
      Valued.v (a - c ^ 2) ≤ WithZero.exp (-(2 * (m : ℤ))) →
      ∃ c' : v.adicCompletion K, Valued.v c' = 1 ∧
        Valued.v (a - c' ^ 2) ≤ WithZero.exp (-(2 * (m : ℤ) + 1)) := by
    intro m hm a c ha hc hac
    have hone : (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) := WithZero.exp_zero.symm
    have hdisc : ∀ γ : WithZero (Multiplicative ℤ), γ < 1 → γ ≤ WithZero.exp (-1 : ℤ) := by
      intro γ hγ
      rcases eq_or_ne γ 0 with rfl | h0
      · exact zero_le'
      · have hk := WithZero.exp_log h0
        rw [← hk] at hγ ⊢
        rw [hone, WithZero.exp_lt_exp] at hγ
        rw [WithZero.exp_le_exp]
        omega
    have hexpe : (WithZero.exp (-(e : ℤ)) : WithZero (Multiplicative ℤ))
        ≤ WithZero.exp (-1 : ℤ) := by
      rw [WithZero.exp_le_exp]
      omega
    have hint : ∀ y : NumberField.RingOfIntegers K,
        IsDedekindDomain.HeightOneSpectrum.valuation K v
            (algebraMap (NumberField.RingOfIntegers K) K y)
          = IsDedekindDomain.HeightOneSpectrum.intValuation v y :=
      fun y => IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap v y
    have hivlt : ∀ y : NumberField.RingOfIntegers K,
        IsDedekindDomain.HeightOneSpectrum.intValuation v y < 1 ↔ y ∈ v.asIdeal :=
      fun y => IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem v y
    have hbridge : ∀ y : NumberField.RingOfIntegers K,
        Valued.v (algebraMap K (v.adicCompletion K)
            (algebraMap (NumberField.RingOfIntegers K) K y)) ≤ WithZero.exp (-1 : ℤ)
          ↔ y ∈ v.asIdeal := by
      intro y
      rw [hcoe, hint]
      constructor
      · intro h
        exact (hivlt y).mp (lt_of_le_of_lt h hexp1)
      · intro h
        exact hdisc _ ((hivlt y).mpr h)
    have h2mem : (2 : NumberField.RingOfIntegers K) ∈ v.asIdeal := by
      rw [← hbridge]
      have hcast : algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K (2 : NumberField.RingOfIntegers K))
          = (2 : v.adicCompletion K) := by
        simp only [map_ofNat]
      rw [hcast, h2e]
      exact hexpe
    have hressq : ∀ y : NumberField.RingOfIntegers K,
        ∃ s : NumberField.RingOfIntegers K, s ^ 2 - y ∈ v.asIdeal := by
      intro y
      haveI : v.asIdeal.IsMaximal := v.isMaximal
      letI : Field (NumberField.RingOfIntegers K ⧸ v.asIdeal) :=
        Ideal.Quotient.field v.asIdeal
      haveI : Finite (NumberField.RingOfIntegers K ⧸ v.asIdeal) :=
        Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
      letI : Fintype (NumberField.RingOfIntegers K ⧸ v.asIdeal) := Fintype.ofFinite _
      haveI : CharP (NumberField.RingOfIntegers K ⧸ v.asIdeal)
          (ringChar (NumberField.RingOfIntegers K ⧸ v.asIdeal)) := ringChar.charP _
      have hzero : ((2 : ℕ) : NumberField.RingOfIntegers K ⧸ v.asIdeal) = 0 := by
        have h := (Ideal.Quotient.eq_zero_iff_mem (I := v.asIdeal)
          (a := (2 : NumberField.RingOfIntegers K))).mpr h2mem
        simpa using h
      have hdvd : ringChar (NumberField.RingOfIntegers K ⧸ v.asIdeal) ∣ 2 := ringChar.dvd hzero
      have hprime : Nat.Prime (ringChar (NumberField.RingOfIntegers K ⧸ v.asIdeal)) :=
        CharP.char_is_prime (NumberField.RingOfIntegers K ⧸ v.asIdeal) _
      have hchar : ringChar (NumberField.RingOfIntegers K ⧸ v.asIdeal) = 2 :=
        (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp hdvd
      obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two hchar (Ideal.Quotient.mk v.asIdeal y)
      obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective r
      refine ⟨s, ?_⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hs, hr]
      ring
    obtain ⟨π, hπ⟩ : ∃ π : v.adicCompletion K, Valued.v π = WithZero.exp (-1 : ℤ) := by
      obtain ⟨π₀, hπ₀⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer K v
      exact ⟨algebraMap K (v.adicCompletion K) π₀, by rw [hcoe, hπ₀]⟩
    have hπ0 : π ≠ 0 := by
      intro h
      rw [h, Valuation.map_zero] at hπ
      exact WithZero.exp_ne_zero hπ.symm
    have hπpow : ∀ k : ℕ, Valued.v (π ^ k) = WithZero.exp (-(k : ℤ)) := by
      intro k
      have hk : k • (-1 : ℤ) = -(k : ℤ) := by simp
      rw [map_pow, hπ, ← WithZero.exp_nsmul, hk]
    have hcast2m : -((2 * m : ℕ) : ℤ) = -(2 * (m : ℤ)) := by push_cast; ring
    have hpow2m : Valued.v (π ^ (2 * m)) = WithZero.exp (-(2 * (m : ℤ))) := by
      rw [hπpow, hcast2m]
    have hπ2m0 : (π ^ (2 * m) : v.adicCompletion K) ≠ 0 := pow_ne_zero _ hπ0
    obtain ⟨u, hu, hueq⟩ : ∃ u : v.adicCompletion K,
        Valued.v u ≤ 1 ∧ π ^ (2 * m) * u = a - c ^ 2 := by
      refine ⟨(a - c ^ 2) / π ^ (2 * m), ?_, ?_⟩
      · rw [map_div₀, hpow2m, div_le_iff₀ (zero_lt_iff.mpr WithZero.exp_ne_zero), one_mul]
        exact hac
      · field_simp
    obtain ⟨y, hy⟩ := h_approx_int u hu 1
    have hy' : Valued.v (u - algebraMap K (v.adicCompletion K)
        (algebraMap (NumberField.RingOfIntegers K) K y)) ≤ WithZero.exp (-1 : ℤ) := by
      simpa using hy
    obtain ⟨z, hz1, hzy⟩ : ∃ z : v.adicCompletion K, Valued.v z ≤ 1 ∧
        Valued.v (algebraMap K (v.adicCompletion K)
            (algebraMap (NumberField.RingOfIntegers K) K y) - z ^ 2)
          ≤ WithZero.exp (-1 : ℤ) := by
      obtain ⟨s, hs⟩ := hressq y
      refine ⟨algebraMap K (v.adicCompletion K)
        (algebraMap (NumberField.RingOfIntegers K) K s), hN1 s, ?_⟩
      have hmem := (hbridge (s ^ 2 - y)).mpr hs
      have hrw : algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K (s ^ 2 - y))
          = (algebraMap K (v.adicCompletion K)
              (algebraMap (NumberField.RingOfIntegers K) K s)) ^ 2
            - algebraMap K (v.adicCompletion K)
              (algebraMap (NumberField.RingOfIntegers K) K y) := by
        simp only [map_sub, map_pow]
      rw [hrw] at hmem
      rw [show algebraMap K (v.adicCompletion K)
            (algebraMap (NumberField.RingOfIntegers K) K y)
            - (algebraMap K (v.adicCompletion K)
                (algebraMap (NumberField.RingOfIntegers K) K s)) ^ 2
          = -((algebraMap K (v.adicCompletion K)
                (algebraMap (NumberField.RingOfIntegers K) K s)) ^ 2
              - algebraMap K (v.adicCompletion K)
                (algebraMap (NumberField.RingOfIntegers K) K y)) by ring,
        Valuation.map_neg]
      exact hmem
    have huz : Valued.v (u - z ^ 2) ≤ WithZero.exp (-1 : ℤ) := by
      have hsplit : u - z ^ 2 = (u - algebraMap K (v.adicCompletion K)
            (algebraMap (NumberField.RingOfIntegers K) K y))
          + (algebraMap K (v.adicCompletion K)
              (algebraMap (NumberField.RingOfIntegers K) K y) - z ^ 2) := by ring
      rw [hsplit]
      exact le_trans (Valuation.map_add _ _ _) (max_le hy' hzy)
    have hw : Valued.v (π ^ m * z) ≤ WithZero.exp (-(m : ℤ)) := by
      rw [map_mul, hπpow]
      calc (WithZero.exp (-(m : ℤ)) : WithZero (Multiplicative ℤ)) * Valued.v z
          ≤ WithZero.exp (-(m : ℤ)) * 1 := mul_le_mul_right hz1 _
        _ = WithZero.exp (-(m : ℤ)) := mul_one _
    have hwsq : a - c ^ 2 - (π ^ m * z) ^ 2 = π ^ (2 * m) * (u - z ^ 2) := by
      have hp : (π ^ m * z) ^ 2 = π ^ (2 * m) * z ^ 2 := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm m 2]
      rw [hp, ← hueq]
      ring
    have hwsqval : Valued.v (a - c ^ 2 - (π ^ m * z) ^ 2)
        ≤ WithZero.exp (-(2 * (m : ℤ) + 1)) := by
      rw [hwsq, map_mul, hpow2m]
      calc (WithZero.exp (-(2 * (m : ℤ))) : WithZero (Multiplicative ℤ)) * Valued.v (u - z ^ 2)
          ≤ WithZero.exp (-(2 * (m : ℤ))) * WithZero.exp (-1 : ℤ) := mul_le_mul_right huz _
        _ = WithZero.exp (-(2 * (m : ℤ)) + (-1 : ℤ)) := (WithZero.exp_add _ _).symm
        _ = WithZero.exp (-(2 * (m : ℤ) + 1)) := by congr 1; ring
    have hcross : Valued.v (2 * c * (π ^ m * z)) ≤ WithZero.exp (-(2 * (m : ℤ) + 1)) := by
      rw [map_mul, map_mul, h2e, hc, mul_one]
      calc (WithZero.exp (-(e : ℤ)) : WithZero (Multiplicative ℤ)) * Valued.v (π ^ m * z)
          ≤ WithZero.exp (-(e : ℤ)) * WithZero.exp (-(m : ℤ)) := mul_le_mul_right hw _
        _ = WithZero.exp (-(e : ℤ) + -(m : ℤ)) := (WithZero.exp_add _ _).symm
        _ ≤ WithZero.exp (-(2 * (m : ℤ) + 1)) := by
            rw [WithZero.exp_le_exp]
            omega
    have hmain : Valued.v (a - (c + π ^ m * z) ^ 2) ≤ WithZero.exp (-(2 * (m : ℤ) + 1)) := by
      have hid : a - (c + π ^ m * z) ^ 2
          = (a - c ^ 2 - (π ^ m * z) ^ 2) - 2 * c * (π ^ m * z) := by ring
      rw [hid]
      exact le_trans (Valuation.map_sub _ _ _) (max_le hwsqval hcross)
    refine ⟨c + π ^ m * z, ?_, hmain⟩
    have hlt : Valued.v (a - (c + π ^ m * z) ^ 2) < Valued.v a := by
      rw [ha]
      calc Valued.v (a - (c + π ^ m * z) ^ 2)
          ≤ WithZero.exp (-(2 * (m : ℤ) + 1)) := hmain
        _ ≤ WithZero.exp (-1 : ℤ) := by
            rw [WithZero.exp_le_exp]
            omega
        _ < 1 := hexp1
    have hsq : Valued.v ((c + π ^ m * z) ^ 2) = 1 := by
      have hid2 : (c + π ^ m * z) ^ 2 = a + -(a - (c + π ^ m * z) ^ 2) := by ring
      have hne : Valued.v a ≠ Valued.v (-(a - (c + π ^ m * z) ^ 2)) := by
        rw [Valuation.map_neg]
        exact ne_of_gt hlt
      rw [hid2, Valuation.map_add_of_distinct_val _ hne, Valuation.map_neg,
        max_eq_left (le_of_lt hlt), ha]
    refine htors _ ?_
    rw [← map_pow]
    exact hsq
  clear h_approx_int hN1 hN2
  obtain ⟨z₀, t₀, hzt₀⟩ := (h_hilb_eq_one_iff x b hx).mp (horth b hb0)
  have hzt₀_ne : z₀ ^ 2 - b * t₀ ^ 2 ≠ 0 := by rw [hzt₀]; exact hx
  obtain ⟨k, hk⟩ := hbeven z₀ t₀ hzt₀_ne
  rw [hzt₀] at hk
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : v.adicCompletion K, Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
    obtain ⟨π₀, hπ₀⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer K v
    exact ⟨algebraMap K (v.adicCompletion K) π₀, by rw [hcoe, hπ₀]⟩
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, Valuation.map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  have hϖ_zpow : ∀ n : ℤ, Valued.v (ϖ ^ n) = WithZero.exp (-n) := by
    intro n
    have h1 : (n : ℤ) • (-1 : ℤ) = -n := by simp
    calc Valued.v (ϖ ^ n) = Valued.v ϖ ^ n := map_zpow₀ _ _ _
      _ = WithZero.exp (-1 : ℤ) ^ n := by rw [hϖ]
      _ = WithZero.exp ((n : ℤ) • (-1 : ℤ)) := (WithZero.exp_zsmul _ _).symm
      _ = WithZero.exp (-n) := by rw [h1]
  let q : v.adicCompletion K := ϖ ^ (-k)
  have hq0 : q ≠ 0 := zpow_ne_zero _ hϖ0
  have hq_val : Valued.v q = WithZero.exp k := by
    dsimp [q]
    rw [hϖ_zpow (-k), neg_neg]
  have hq2_val : Valued.v (q ^ 2) = WithZero.exp (2 * k) := by
    rw [map_pow, hq_val, pow_two, ← WithZero.exp_add, two_mul]
  let a : v.adicCompletion K := x / q ^ 2
  have ha : Valued.v a = 1 := by
    dsimp [a]
    rw [map_div₀, hk, hq2_val, div_self WithZero.exp_ne_zero]
  have hx_eq : x = q ^ 2 * a := (mul_div_cancel₀ x (pow_ne_zero 2 hq0)).symm
  have haur_all : ∀ y : v.adicCompletion K, y ≠ 0 →
      ∃ z t : v.adicCompletion K, z ^ 2 - a * t ^ 2 = y := by
    intro y hy
    have h1 : hilbLoc v y x = 1 := by rw [hilbLoc_symm, horth y hy]
    obtain ⟨z₁, t₁, hzt₁⟩ := (h_hilb_eq_one_iff y x hy).mp h1
    refine ⟨z₁, q * t₁, ?_⟩
    rw [← hzt₁, hx_eq]
    ring
  have haur : ∀ u : v.adicCompletion K, Valued.v u = 1 →
      ∃ z t : v.adicCompletion K, z ^ 2 - a * t ^ 2 = u := by
    intro u hu
    have hu0 : u ≠ 0 := (Valuation.ne_zero_iff Valued.v).mp (by rw [hu]; exact one_ne_zero)
    exact haur_all u hu0
  have key : ∃ (s : ℕ) (w : v.adicCompletion K), Valued.v w = 1 ∧
      Valued.v (a - w ^ 2) ≤ WithZero.exp (-(s : ℤ)) ∧ s ≤ 2 * e ∧
      (∀ n : ℕ, n ≤ 2 * e →
        (∃ w' : v.adicCompletion K, Valued.v w' = 1 ∧
          Valued.v (a - w' ^ 2) ≤ WithZero.exp (-(n : ℤ))) → n ≤ s) := by
    have hP0 : ∃ w' : v.adicCompletion K, Valued.v w' = 1 ∧
        Valued.v (a - w' ^ 2) ≤ WithZero.exp (-((0 : ℕ) : ℤ)) := by
      refine ⟨1, Valuation.map_one _, ?_⟩
      have hb_sub : Valued.v (a - (1 : v.adicCompletion K) ^ 2)
          ≤ max (Valued.v a) (Valued.v ((1 : v.adicCompletion K) ^ 2)) :=
        Valuation.map_sub _ _ _
      have hm1 : max (Valued.v a) (Valued.v ((1 : v.adicCompletion K) ^ 2)) = 1 := by
        rw [ha, one_pow, Valuation.map_one, max_self]
      rw [hm1] at hb_sub
      simpa only [Nat.cast_zero, neg_zero, WithZero.exp_zero] using hb_sub
    refine ⟨Nat.findGreatest (fun n : ℕ => ∃ w' : v.adicCompletion K, Valued.v w' = 1 ∧
        Valued.v (a - w' ^ 2) ≤ WithZero.exp (-(n : ℤ))) (2 * e), ?_⟩
    obtain ⟨w, hw, haw⟩ :=
      Nat.findGreatest_spec (P := fun n : ℕ => ∃ w' : v.adicCompletion K, Valued.v w' = 1 ∧
        Valued.v (a - w' ^ 2) ≤ WithZero.exp (-(n : ℤ))) (Nat.zero_le (2 * e)) hP0
    exact ⟨w, hw, haw, Nat.findGreatest_le _,
      fun n hn hPn => Nat.le_findGreatest
        (P := fun n : ℕ => ∃ w' : v.adicCompletion K, Valued.v w' = 1 ∧
          Valued.v (a - w' ^ 2) ≤ WithZero.exp (-(n : ℤ))) hn hPn⟩
  obtain ⟨s, w, hw, haw, hsle, hmax⟩ := key
  have hs2e : s = 2 * e := by
    by_contra hne
    have hlt : s < 2 * e := lt_of_le_of_ne hsle hne
    have hne0 : a - w ^ 2 ≠ 0 := by
      intro h0
      have hge : 2 * e ≤ s := by
        refine hmax (2 * e) le_rfl ⟨w, hw, ?_⟩
        rw [h0, Valuation.map_zero]
        exact zero_le'
      omega
    have hexact : Valued.v (a - w ^ 2) = WithZero.exp (-(s : ℤ)) := by
      have hvne : Valued.v (a - w ^ 2) ≠ 0 := (Valuation.ne_zero_iff _).mpr hne0
      have hlog : WithZero.exp (WithZero.log (Valued.v (a - w ^ 2)))
          = Valued.v (a - w ^ 2) := WithZero.exp_log hvne
      have hMle : WithZero.log (Valued.v (a - w ^ 2)) ≤ -(s : ℤ) := by
        rw [← WithZero.exp_le_exp, hlog]
        exact haw
      have hMgt : ¬ (WithZero.log (Valued.v (a - w ^ 2)) ≤ -(s : ℤ) - 1) := by
        intro hcon
        have hstep : Valued.v (a - w ^ 2) ≤ WithZero.exp (-((s + 1 : ℕ) : ℤ)) := by
          rw [← hlog, WithZero.exp_le_exp]
          omega
        have hle : s + 1 ≤ s := hmax (s + 1) (by omega) ⟨w, hw, hstep⟩
        omega
      have hMeq : WithZero.log (Valued.v (a - w ^ 2)) = -(s : ℤ) := by omega
      rw [← hlog, hMeq]
    have hEven : Even s := h_even_defect s a w ha haur hexact hlt
    obtain ⟨m, hm⟩ := hEven
    have hmlt : m < e := by omega
    have haw' : Valued.v (a - w ^ 2) ≤ WithZero.exp (-(2 * (m : ℤ))) := by
      rw [hexact, WithZero.exp_le_exp]
      omega
    obtain ⟨w', hw', haw''⟩ := h_even_step m hmlt a w ha hw haw'
    have hle : s + 1 ≤ s := by
      refine hmax (s + 1) (by omega) ⟨w', hw', ?_⟩
      refine le_trans haw'' (le_of_eq ?_)
      exact WithZero.exp_inj.mpr (by omega)
    omega
  clear h_even_defect h_even_step hmax hsle hb_val hb0 hb1 hbeven
  have haw2e : Valued.v (a - w ^ 2) ≤ WithZero.exp (-(2 * (e : ℤ))) := by
    have hcast : (-((2 * e : ℕ) : ℤ)) = -(2 * (e : ℤ)) := by omega
    rwa [hs2e, hcast] at haw
  obtain ⟨z, t, hzt_pi⟩ := haur_all ϖ hϖ0
  have ht0 : t ≠ 0 := by
    intro ht
    subst ht
    have hz2 : z ^ 2 = ϖ := by linear_combination hzt_pi
    have hz0 : z ≠ 0 := by
      intro hz
      rw [hz] at hz2
      exact hϖ0 (by linear_combination -hz2)
    obtain ⟨mz, hmz⟩ := hN0 z hz0
    have hmz2 : WithZero.exp (mz + mz) = WithZero.exp (-1 : ℤ) := by
      rw [WithZero.exp_add, ← hmz, ← pow_two, ← map_pow, hz2, hϖ]
    have := WithZero.exp_inj.mp hmz2
    omega
  obtain ⟨n, hn⟩ := hN0 t ht0
  have ht2_val : Valued.v (t ^ 2) = WithZero.exp (2 * n) := by
    rw [map_pow, hn, pow_two, ← WithZero.exp_add, two_mul]
  let u : v.adicCompletion K := z / t
  have hu_eq : t ^ 2 * (u ^ 2 - a) = ϖ := by
    dsimp [u]
    field_simp [ht0]
    linear_combination hzt_pi
  have hu2a_val : Valued.v (u ^ 2 - a) = WithZero.exp (-(2 * n + 1)) := by
    have hmul_val : Valued.v (t ^ 2) * Valued.v (u ^ 2 - a) = WithZero.exp (-1 : ℤ) := by
      rw [← map_mul, hu_eq, hϖ]
    rw [ht2_val] at hmul_val
    have hdiv : Valued.v (u ^ 2 - a) = WithZero.exp (-1 : ℤ) / WithZero.exp (2 * n) :=
      eq_div_of_mul_eq WithZero.exp_ne_zero (by rw [mul_comm]; exact hmul_val)
    rw [hdiv, ← WithZero.exp_sub]
    congr 1
    ring
  have hau_val : Valued.v (a - u ^ 2) = WithZero.exp (-(2 * n + 1)) := by
    rw [show a - u ^ 2 = -(u ^ 2 - a) by ring, Valuation.map_neg, hu2a_val]
  have h2w_val : Valued.v (2 * w) = WithZero.exp (-(e : ℤ)) := by
    rw [map_mul, h2e, hw, mul_one]
  have huw_le : Valued.v (u - w) ≤ WithZero.exp (-(e : ℤ)) := by
    by_contra hnot
    have hgt : WithZero.exp (-(e : ℤ)) < Valued.v (u - w) := not_le.mp hnot
    have huw0 : u - w ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hgt
      exact absurd hgt (not_lt.mpr zero_le')
    obtain ⟨mu, hmu⟩ := hN0 (u - w) huw0
    have hmu_gt : -(e : ℤ) < mu := by
      rw [hmu, WithZero.exp_lt_exp] at hgt
      exact hgt
    have hlt_2w : Valued.v (2 * w) < Valued.v (u - w) := by
      rw [h2w_val]
      exact hgt
    have huw_add : Valued.v (u + w) = WithZero.exp mu := by
      have heq : u + w = (u - w) + 2 * w := by ring
      rw [heq, Valuation.map_add_eq_of_lt_left _ hlt_2w, hmu]
    have hu2w2_val : Valued.v (u ^ 2 - w ^ 2) = WithZero.exp (2 * mu) := by
      have hfac : u ^ 2 - w ^ 2 = (u - w) * (u + w) := by ring
      rw [hfac, map_mul, hmu, huw_add, ← WithZero.exp_add, two_mul]
    have haw_lt : Valued.v (a - w ^ 2) < Valued.v (u ^ 2 - w ^ 2) := by
      refine lt_of_le_of_lt haw2e ?_
      rw [hu2w2_val, WithZero.exp_lt_exp]
      omega
    have hu2a_even : Valued.v (u ^ 2 - a) = WithZero.exp (2 * mu) := by
      have heq : u ^ 2 - a = (u ^ 2 - w ^ 2) - (a - w ^ 2) := by ring
      rw [heq, Valuation.map_sub_eq_of_lt_left _ haw_lt, hu2w2_val]
    rw [hu2a_val] at hu2a_even
    have := WithZero.exp_inj.mp hu2a_even
    omega
  have huw_add_le : Valued.v (u + w) ≤ WithZero.exp (-(e : ℤ)) := by
    have heq : u + w = (u - w) + 2 * w := by ring
    rw [heq]
    refine le_trans (Valuation.map_add _ _ _) (max_le huw_le ?_)
    rw [h2w_val]
  have hu2w2_le : Valued.v (u ^ 2 - w ^ 2) ≤ WithZero.exp (-(2 * (e : ℤ))) := by
    have hfac : u ^ 2 - w ^ 2 = (u - w) * (u + w) := by ring
    rw [hfac, map_mul]
    calc Valued.v (u - w) * Valued.v (u + w)
        ≤ WithZero.exp (-(e : ℤ)) * WithZero.exp (-(e : ℤ)) := mul_le_mul' huw_le huw_add_le
      _ = WithZero.exp (-(2 * (e : ℤ))) := by
          rw [← WithZero.exp_add]
          congr 1
          ring
  have hau_le : Valued.v (a - u ^ 2) ≤ WithZero.exp (-(2 * (e : ℤ))) := by
    have heq : a - u ^ 2 = (a - w ^ 2) - (u ^ 2 - w ^ 2) := by ring
    rw [heq]
    exact le_trans (Valuation.map_sub _ _ _) (max_le haw2e hu2w2_le)
  have h_exp_le : -(2 * n + 1) ≤ -(2 * (e : ℤ)) := by
    rw [hau_val, WithZero.exp_le_exp] at hau_le
    exact hau_le
  have hlt4 : Valued.v (a - u ^ 2) < Valued.v (4 : v.adicCompletion K) := by
    rw [hau_val, h4e, WithZero.exp_lt_exp]
    omega
  have hu1 : Valued.v u = 1 := by
    have hlt_a : Valued.v (a - u ^ 2) < Valued.v a := by
      rw [hau_val, ha, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    have hu2_val : Valued.v (u ^ 2) = 1 := by
      have heq : u ^ 2 = a - (a - u ^ 2) := by ring
      rw [heq, Valuation.map_sub_eq_of_lt_left _ hlt_a, ha]
    exact htors (Valued.v u) (by rw [← map_pow]; exact hu2_val)
  obtain ⟨ra, hra⟩ := h_sq_lt_four a u hu1 hlt4
  exact ⟨q * ra, by rw [hx_eq, ← hra]; ring⟩

theorem norm_mul_mem_of_common_pure_repr {F : Type u} [Field F]
    (hF2 : (2 : F) ≠ 0)
    (a δ x y : F) (ha0 : a ≠ 0) (hδ : δ ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (hns : ∀ t : F, t ^ 2 ≠ δ)
    (hans : ∀ t : F, t ^ 2 ≠ a)
    (hxn : ¬ ∃ z t : F, z ^ 2 - δ * t ^ 2 = x)
    (hyn : ¬ ∃ z t : F, z ^ 2 - δ * t ^ 2 = y)
    (hax : ∃ p q r : F, δ * p ^ 2 + x * q ^ 2 - δ * x * r ^ 2 = a)
    (hay : ∃ p q r : F, δ * p ^ 2 + y * q ^ 2 - δ * y * r ^ 2 = a)
    (hmul : ∀ μ₁ μ₂ : F, μ₁ ≠ 0 → μ₂ ≠ 0 →
        (¬ ∃ z t : F, z ^ 2 - a * t ^ 2 = μ₁) →
        (¬ ∃ z t : F, z ^ 2 - a * t ^ 2 = μ₂) →
        ∃ z t : F, z ^ 2 - a * t ^ 2 = μ₁ * μ₂) :
    ∃ z t : F, z ^ 2 - δ * t ^ 2 = x * y :=
by
  classical
  have hS1 : ∀ c : F, c ≠ 0 → (¬ ∃ z t : F, z ^ 2 - δ * t ^ 2 = c) →
      ∀ p q r : F, δ * p ^ 2 + c * q ^ 2 - δ * c * r ^ 2 = 0 →
        p = 0 ∧ q = 0 ∧ r = 0 := by
    intro c hc hcn p q r h
    by_cases hn : q ^ 2 - δ * r ^ 2 = 0
    · have hr : r = 0 := by
        by_contra hr
        exact hns (q / r) (by field_simp; linear_combination hn)
      have hq : q = 0 := by
        have h2 : q ^ 2 = 0 := by rw [hr] at hn; linear_combination hn
        exact sq_eq_zero_iff.mp h2
      have hp : p = 0 := by
        have h2 : δ * p ^ 2 = 0 := by rw [hq, hr] at h; linear_combination h
        rcases mul_eq_zero.mp h2 with h' | h'
        · exact absurd h' hδ
        · exact sq_eq_zero_iff.mp h'
      exact ⟨hp, hq, hr⟩
    · exfalso
      apply hcn
      refine ⟨δ * p * r / (q ^ 2 - δ * r ^ 2), p * q / (q ^ 2 - δ * r ^ 2), ?_⟩
      field_simp
      linear_combination (-(q ^ 2 - δ * r ^ 2)) * h
  have hS2 : ∀ c b : F, b ≠ 0 →
      (∀ p q r : F, δ * p ^ 2 + c * q ^ 2 - δ * c * r ^ 2 = 0 → p = 0 ∧ q = 0 ∧ r = 0) →
      ∀ u₁ u₂ u₃ v₁ v₂ v₃ : F,
        δ * u₁ ^ 2 + c * u₂ ^ 2 - δ * c * u₃ ^ 2 = a →
        δ * v₁ ^ 2 + c * v₂ ^ 2 - δ * c * v₃ ^ 2 = b →
        δ * u₁ * v₁ + c * u₂ * v₂ - δ * c * u₃ * v₃ = 0 →
        ¬ ∃ z t : F, z ^ 2 - a * t ^ 2 = b := by
    intro c b hb haniso u₁ u₂ u₃ v₁ v₂ v₃ hu hv huv
    rintro ⟨s, t, hst⟩
    have hTw : δ * (c * (u₃ * v₂ - u₂ * v₃)) ^ 2 + c * (δ * (u₁ * v₃ - u₃ * v₁)) ^ 2
        - δ * c * (u₁ * v₂ - u₂ * v₁) ^ 2 = -(a * b) := by
      linear_combination (-(δ * v₁ ^ 2 + c * v₂ ^ 2 - δ * c * v₃ ^ 2)) * hu + (-a) * hv
        + (δ * u₁ * v₁ + c * u₂ * v₂ - δ * c * u₃ * v₃) * huv
    obtain ⟨hZ1, hZ2, hZ3⟩ := haniso
      (-b * u₁ + a * t * v₁ + s * (c * (u₃ * v₂ - u₂ * v₃)))
      (-b * u₂ + a * t * v₂ + s * (δ * (u₁ * v₃ - u₃ * v₁)))
      (-b * u₃ + a * t * v₃ + s * (u₁ * v₂ - u₂ * v₁))
      (by linear_combination b ^ 2 * hu + (a * t) ^ 2 * hv + s ^ 2 * hTw
            + (2 * (-b) * (a * t)) * huv + (-(a * b)) * hst)
    have h0 : δ * (-b * u₁ + a * t * v₁ + s * (c * (u₃ * v₂ - u₂ * v₃))) * u₁
        + c * (-b * u₂ + a * t * v₂ + s * (δ * (u₁ * v₃ - u₃ * v₁))) * u₂
        - δ * c * (-b * u₃ + a * t * v₃ + s * (u₁ * v₂ - u₂ * v₁)) * u₃ = 0 := by
      rw [hZ1, hZ2, hZ3]; ring
    have hba : b * a = 0 := by
      linear_combination -h0 - b * hu + (a * t) * huv
    rcases mul_eq_zero.mp hba with h' | h'
    · exact hb h'
    · exact ha0 h'
  have hS5 : ∀ c : F, c ≠ 0 →
      (∀ p q r : F, δ * p ^ 2 + c * q ^ 2 - δ * c * r ^ 2 = 0 → p = 0 ∧ q = 0 ∧ r = 0) →
      (∃ p q r : F, δ * p ^ 2 + c * q ^ 2 - δ * c * r ^ 2 = a) →
      ∃ u₁ u₂ u₃ v₁ v₂ v₃ b : F,
        δ * u₁ ^ 2 + c * u₂ ^ 2 - δ * c * u₃ ^ 2 = a ∧
        δ * v₁ ^ 2 + c * v₂ ^ 2 - δ * c * v₃ ^ 2 = b ∧
        δ * u₁ * v₁ + c * u₂ * v₂ - δ * c * u₃ * v₃ = 0 ∧ b ≠ 0 := by
    intro c hc haniso hrep
    obtain ⟨p, q, r, hpqr⟩ := hrep
    by_cases hpq : p = 0 ∧ q = 0
    · exact ⟨p, q, r, 1, 0, 0, δ, hpqr, by ring, by rw [hpq.1]; ring, hδ⟩
    · refine ⟨p, q, r, c * q, -(δ * p), 0, δ * (c * q) ^ 2 + c * (δ * p) ^ 2,
        hpqr, by ring, by ring, ?_⟩
      intro hb0
      obtain ⟨e1, e2, _⟩ := haniso (c * q) (-(δ * p)) 0 (by linear_combination hb0)
      apply hpq
      refine ⟨?_, ?_⟩
      · have hdp : δ * p = 0 := by linear_combination -e2
        rcases mul_eq_zero.mp hdp with h' | h'
        · exact absurd h' hδ
        · exact h'
      · rcases mul_eq_zero.mp e1 with h' | h'
        · exact absurd h' hc
        · exact h'
  have hS3 : ∀ c b : F, b ≠ 0 → ∀ u₁ u₂ u₃ v₁ v₂ v₃ : F,
      δ * u₁ ^ 2 + c * u₂ ^ 2 - δ * c * u₃ ^ 2 = a →
      δ * v₁ ^ 2 + c * v₂ ^ 2 - δ * c * v₃ ^ 2 = b →
      δ * u₁ * v₁ + c * u₂ * v₂ - δ * c * u₃ * v₃ = 0 →
      ∃ e₁ e₂ e₃ f₁ f₂ f₃ : F,
        a * e₁ ^ 2 + b * e₂ ^ 2 - a * b * e₃ ^ 2 = δ ∧
        a * f₁ ^ 2 + b * f₂ ^ 2 - a * b * f₃ ^ 2 = c ∧
        a * e₁ * f₁ + b * e₂ * f₂ - a * b * e₃ * f₃ = 0 := by
    intro c b hb u₁ u₂ u₃ v₁ v₂ v₃ hu hv huv
    have hK1 : δ * (b * u₁ ^ 2 + a * v₁ ^ 2 - (c * (u₃ * v₂ - u₂ * v₃)) ^ 2) = a * b := by
      linear_combination (c * v₂ ^ 2 - δ * c * v₃ ^ 2) * hu + (a - δ * u₁ ^ 2) * hv
        + (δ * u₁ * v₁ - c * u₂ * v₂ + δ * c * u₃ * v₃) * huv
    have hK2 : c * (b * u₂ ^ 2 + a * v₂ ^ 2 - (δ * (u₁ * v₃ - u₃ * v₁)) ^ 2) = a * b := by
      linear_combination (δ * v₁ ^ 2 - δ * c * v₃ ^ 2) * hu + (a - c * u₂ ^ 2) * hv
        + (c * u₂ * v₂ - δ * u₁ * v₁ + δ * c * u₃ * v₃) * huv
    have hK3 : b * u₁ * u₂ + a * v₁ * v₂
        - (c * (u₃ * v₂ - u₂ * v₃)) * (δ * (u₁ * v₃ - u₃ * v₁)) = 0 := by
      linear_combination (-(v₁ * v₂)) * hu + (-(u₁ * u₂)) * hv + (u₁ * v₂ + u₂ * v₁) * huv
    refine ⟨δ * u₁ / a, δ * v₁ / b, δ * (c * (u₃ * v₂ - u₂ * v₃)) / (a * b),
      c * u₂ / a, c * v₂ / b, c * (δ * (u₁ * v₃ - u₃ * v₁)) / (a * b), ?_, ?_, ?_⟩
    · field_simp
      linear_combination hK1
    · field_simp
      linear_combination c * hK2
    · field_simp
      linear_combination δ * c * hK3
  have hS4 : ∀ c b μ ν : F, ∀ u₁ u₂ u₃ v₁ v₂ v₃ : F,
      δ * u₁ ^ 2 + c * u₂ ^ 2 - δ * c * u₃ ^ 2 = a →
      δ * v₁ ^ 2 + c * v₂ ^ 2 - δ * c * v₃ ^ 2 = b →
      δ * u₁ * v₁ + c * u₂ * v₂ - δ * c * u₃ * v₃ = 0 →
      ∀ e₁ e₂ e₃ f₁ f₂ f₃ : F,
        a * e₁ ^ 2 + b * e₂ ^ 2 - a * b * e₃ ^ 2 = μ →
        a * f₁ ^ 2 + b * f₂ ^ 2 - a * b * f₃ ^ 2 = ν →
        a * e₁ * f₁ + b * e₂ * f₂ - a * b * e₃ * f₃ = 0 →
      ∃ P₁ P₂ P₃ Q₁ Q₂ Q₃ : F,
        δ * P₁ ^ 2 + c * P₂ ^ 2 - δ * c * P₃ ^ 2 = μ ∧
        δ * Q₁ ^ 2 + c * Q₂ ^ 2 - δ * c * Q₃ ^ 2 = ν ∧
        δ * P₁ * Q₁ + c * P₂ * Q₂ - δ * c * P₃ * Q₃ = 0 := by
    intro c b μ ν u₁ u₂ u₃ v₁ v₂ v₃ hu hv huv e₁ e₂ e₃ f₁ f₂ f₃ he hf hef
    have hTw : δ * (c * (u₃ * v₂ - u₂ * v₃)) ^ 2 + c * (δ * (u₁ * v₃ - u₃ * v₁)) ^ 2
        - δ * c * (u₁ * v₂ - u₂ * v₁) ^ 2 = -(a * b) := by
      linear_combination (-(δ * v₁ ^ 2 + c * v₂ ^ 2 - δ * c * v₃ ^ 2)) * hu + (-a) * hv
        + (δ * u₁ * v₁ + c * u₂ * v₂ - δ * c * u₃ * v₃) * huv
    refine ⟨e₁ * u₁ + e₂ * v₁ + e₃ * (c * (u₃ * v₂ - u₂ * v₃)),
      e₁ * u₂ + e₂ * v₂ + e₃ * (δ * (u₁ * v₃ - u₃ * v₁)),
      e₁ * u₃ + e₂ * v₃ + e₃ * (u₁ * v₂ - u₂ * v₁),
      f₁ * u₁ + f₂ * v₁ + f₃ * (c * (u₃ * v₂ - u₂ * v₃)),
      f₁ * u₂ + f₂ * v₂ + f₃ * (δ * (u₁ * v₃ - u₃ * v₁)),
      f₁ * u₃ + f₂ * v₃ + f₃ * (u₁ * v₂ - u₂ * v₁), ?_, ?_, ?_⟩
    · linear_combination e₁ ^ 2 * hu + e₂ ^ 2 * hv + e₃ ^ 2 * hTw + (2 * e₁ * e₂) * huv + he
    · linear_combination f₁ ^ 2 * hu + f₂ ^ 2 * hv + f₃ ^ 2 * hTw + (2 * f₁ * f₂) * huv + hf
    · linear_combination e₁ * f₁ * hu + e₂ * f₂ * hv + e₃ * f₃ * hTw
        + (e₁ * f₂ + e₂ * f₁) * huv + hef
  have hS7 : ∀ α β γ α' β' γ' : F,
      δ * α ^ 2 + x * β ^ 2 - δ * x * γ ^ 2 = δ →
      δ * α * α' + x * β * β' - δ * x * γ * γ' = 0 →
      δ * α' ^ 2 + x * β' ^ 2 - δ * x * γ' ^ 2 = y →
      ∃ z t : F, z ^ 2 - δ * t ^ 2 = x * y := by
    intro α β γ α' β' γ' h1 h2 h3
    by_cases hα : α + 1 = 0
    · have hxbg : x * (β ^ 2 - δ * γ ^ 2) = 0 := by
        linear_combination h1 - (δ * (α - 1)) * hα
      have hbg : β ^ 2 - δ * γ ^ 2 = 0 := by
        rcases mul_eq_zero.mp hxbg with h' | h'
        · exact absurd h' hx
        · exact h'
      have hγ0 : γ = 0 := by
        by_contra hg
        exact hns (β / γ) (by field_simp; linear_combination hbg)
      have hβ0 : β = 0 := by
        have h2' : β ^ 2 = 0 := by rw [hγ0] at hbg; linear_combination hbg
        exact sq_eq_zero_iff.mp h2'
      have hα'0 : α' = 0 := by
        have hd : δ * α' = 0 := by
          linear_combination -h2 + (δ * α') * hα + (x * β') * hβ0 - (δ * x * γ') * hγ0
        rcases mul_eq_zero.mp hd with h' | h'
        · exact absurd h' hδ
        · exact h'
      exact ⟨x * β', x * γ', by linear_combination x * h3 - (x * δ * α') * hα'0⟩
    · have hkey : x * (α' * β - (α + 1) * β') ^ 2 - δ * x * (α' * γ - (α + 1) * γ') ^ 2
          = y * (α + 1) ^ 2 := by
        linear_combination (α' ^ 2) * h1 - (2 * (α + 1) * α') * h2 + ((α + 1) ^ 2) * h3
      refine ⟨x * (α' * β - (α + 1) * β') / (α + 1),
        x * (α' * γ - (α + 1) * γ') / (α + 1), ?_⟩
      field_simp
      linear_combination hkey
  have hAx : ∀ p q r : F, δ * p ^ 2 + x * q ^ 2 - δ * x * r ^ 2 = 0 →
      p = 0 ∧ q = 0 ∧ r = 0 := hS1 x hx hxn
  have hAy : ∀ p q r : F, δ * p ^ 2 + y * q ^ 2 - δ * y * r ^ 2 = 0 →
      p = 0 ∧ q = 0 ∧ r = 0 := hS1 y hy hyn
  obtain ⟨u₁, u₂, u₃, v₁, v₂, v₃, b₁, hu, hv, huv, hb₁⟩ := hS5 x hx hAx hax
  obtain ⟨U₁, U₂, U₃, W₁, W₂, W₃, b₂, hU, hW, hUW, hb₂⟩ := hS5 y hy hAy hay
  have hn₁ : ¬ ∃ z t : F, z ^ 2 - a * t ^ 2 = b₁ := hS2 x b₁ hb₁ hAx u₁ u₂ u₃ v₁ v₂ v₃ hu hv huv
  have hn₂ : ¬ ∃ z t : F, z ^ 2 - a * t ^ 2 = b₂ := hS2 y b₂ hb₂ hAy U₁ U₂ U₃ W₁ W₂ W₃ hU hW hUW
  obtain ⟨z₀, t₀, hz₀⟩ := hmul b₁ b₂ hb₁ hb₂ hn₁ hn₂
  have hS : b₁ * ((z₀ / b₁) ^ 2 - a * (t₀ / b₁) ^ 2) = b₂ := by
    field_simp
    linear_combination hz₀
  have hTwx : δ * (x * (u₃ * v₂ - u₂ * v₃)) ^ 2 + x * (δ * (u₁ * v₃ - u₃ * v₁)) ^ 2
      - δ * x * (u₁ * v₂ - u₂ * v₁) ^ 2 = -(a * b₁) := by
    linear_combination (-(δ * v₁ ^ 2 + x * v₂ ^ 2 - δ * x * v₃ ^ 2)) * hu + (-a) * hv
      + (δ * u₁ * v₁ + x * u₂ * v₂ - δ * x * u₃ * v₃) * huv
  have hVval : δ * ((z₀ / b₁) * v₁ + (t₀ / b₁) * (x * (u₃ * v₂ - u₂ * v₃))) ^ 2
      + x * ((z₀ / b₁) * v₂ + (t₀ / b₁) * (δ * (u₁ * v₃ - u₃ * v₁))) ^ 2
      - δ * x * ((z₀ / b₁) * v₃ + (t₀ / b₁) * (u₁ * v₂ - u₂ * v₁)) ^ 2 = b₂ := by
    linear_combination (z₀ / b₁) ^ 2 * hv + (t₀ / b₁) ^ 2 * hTwx + hS
  have hVorth : δ * u₁ * ((z₀ / b₁) * v₁ + (t₀ / b₁) * (x * (u₃ * v₂ - u₂ * v₃)))
      + x * u₂ * ((z₀ / b₁) * v₂ + (t₀ / b₁) * (δ * (u₁ * v₃ - u₃ * v₁)))
      - δ * x * u₃ * ((z₀ / b₁) * v₃ + (t₀ / b₁) * (u₁ * v₂ - u₂ * v₁)) = 0 := by
    linear_combination (z₀ / b₁) * huv
  obtain ⟨e₁, e₂, e₃, f₁, f₂, f₃, he, hf, hef⟩ := hS3 y b₂ hb₂ U₁ U₂ U₃ W₁ W₂ W₃ hU hW hUW
  obtain ⟨P₁, P₂, P₃, Q₁, Q₂, Q₃, hP, hQ, hPQ⟩ :=
    hS4 x b₂ δ y u₁ u₂ u₃
      ((z₀ / b₁) * v₁ + (t₀ / b₁) * (x * (u₃ * v₂ - u₂ * v₃)))
      ((z₀ / b₁) * v₂ + (t₀ / b₁) * (δ * (u₁ * v₃ - u₃ * v₁)))
      ((z₀ / b₁) * v₃ + (t₀ / b₁) * (u₁ * v₂ - u₂ * v₁))
      hu hVval hVorth e₁ e₂ e₃ f₁ f₂ f₃ he hf hef
  exact hS7 P₁ P₂ P₃ Q₁ Q₂ Q₃ hP hPQ hQ

theorem exists_unramified_artinSchreier_unit {K : Type u} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ ρa : v.adicCompletion K,
      Valued.v ρa = 1 ∧
      Valued.v (1 + 4 * ρa) = 1 ∧
      (∀ t : v.adicCompletion K, t ^ 2 ≠ 1 + 4 * ρa) ∧
      (∀ u : v.adicCompletion K, Valued.v u = 1 →
        ∃ z t : v.adicCompletion K, z ^ 2 - (1 + 4 * ρa) * t ^ 2 = u) :=
by
  classical
  have h_not_sq_add_self : ∃ r : NumberField.RingOfIntegers K,
      ∀ s : NumberField.RingOfIntegers K, s ^ 2 + s - r ∉ v.asIdeal := by
    obtain ⟨rbar, hrbar⟩ :
        ∃ rbar : NumberField.RingOfIntegers K ⧸ v.asIdeal,
          ∀ sbar : NumberField.RingOfIntegers K ⧸ v.asIdeal, sbar ^ 2 + sbar ≠ rbar := by
      by_contra hcon
      push_neg at hcon
      have hsurj : Function.Surjective
          (fun x : NumberField.RingOfIntegers K ⧸ v.asIdeal => x ^ 2 + x) := by
        intro b
        obtain ⟨a, ha⟩ := hcon b
        exact ⟨a, ha⟩
      have hinj : Function.Injective
          (fun x : NumberField.RingOfIntegers K ⧸ v.asIdeal => x ^ 2 + x) :=
        Finite.injective_iff_surjective.mpr hsurj
      have hcoll : ((0 : NumberField.RingOfIntegers K ⧸ v.asIdeal) ^ 2 + 0)
          = ((-1 : NumberField.RingOfIntegers K ⧸ v.asIdeal) ^ 2 + (-1)) := by
        ring
      have h01 : (0 : NumberField.RingOfIntegers K ⧸ v.asIdeal) = -1 := hinj hcoll
      exact one_ne_zero
        (show (1 : NumberField.RingOfIntegers K ⧸ v.asIdeal) = 0 by linear_combination h01)
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective rbar
    refine ⟨r, ?_⟩
    intro s hmem
    have h0 : (Ideal.Quotient.mk v.asIdeal) (s ^ 2 + s - r) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [map_sub, map_add, map_pow, hr, sub_eq_zero] at h0
    exact hrbar (Ideal.Quotient.mk v.asIdeal s) h0
  have h_approx_K : ∀ (a : K), IsDedekindDomain.HeightOneSpectrum.valuation K v a ≤ 1 →
      ∀ (M : ℕ), ∃ r : NumberField.RingOfIntegers K,
        IsDedekindDomain.HeightOneSpectrum.valuation K v
          (a - algebraMap (NumberField.RingOfIntegers K) K r) ≤ WithZero.exp (-(M : ℤ)) := by
    intro a ha M
    obtain ⟨xa, ya, hya, hxya⟩ :=
      IsFractionRing.div_surjective (A := NumberField.RingOfIntegers K) (K := K) a
    have hy0 : ya ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hya
    have hiy : algebraMap (NumberField.RingOfIntegers K) K ya ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hya
    have hstar : a * algebraMap (NumberField.RingOfIntegers K) K ya
        = algebraMap (NumberField.RingOfIntegers K) K xa := by
      rw [← hxya]
      exact div_mul_cancel₀ _ hiy
    obtain ⟨m, hym, hym1, hexpm⟩ :
        ∃ m : ℕ, ya ∈ v.asIdeal ^ m ∧ ya ∉ v.asIdeal ^ (m + 1) ∧
          WithZero.exp (-(m : ℤ)) = v.intValuation ya := by
      have ht0 : v.intValuation ya ≠ 0 :=
        IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero v ya hy0
      have ht1 : v.intValuation ya ≤ 1 :=
        IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v ya
      obtain ⟨k, hk⟩ : ∃ k : ℤ, WithZero.exp k = v.intValuation ya := ⟨_, WithZero.exp_log ht0⟩
      have hkle : k ≤ 0 := by
        have hstep : WithZero.exp k ≤ WithZero.exp (0 : ℤ) := by
          rw [hk, WithZero.exp_zero]; exact ht1
        exact WithZero.exp_le_exp.mp hstep
      have hcast : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      have hexpm : WithZero.exp (-(((-k).toNat : ℕ) : ℤ)) = v.intValuation ya := by
        rw [hcast, neg_neg, hk]
      refine ⟨(-k).toNat, ?_, ?_, hexpm⟩
      · exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya _).mp
          (le_of_eq hexpm.symm)
      · intro hcon
        have hle :=
          (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya
            ((-k).toNat + 1)).mpr hcon
        have he : (-(((-k).toNat + 1 : ℕ) : ℤ)) = k - 1 := by
          rw [Nat.cast_add, Nat.cast_one, hcast]; ring
        rw [he, ← hk] at hle
        have := WithZero.exp_le_exp.mp hle
        omega
    have hivy : v.intValuation ya ≤ WithZero.exp (-(m : ℤ)) :=
      (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya m).mpr hym
    have hxm : xa ∈ v.asIdeal ^ m := by
      refine (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v xa m).mp ?_
      have e1 : v.intValuation xa
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K xa) :=
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v xa).symm
      have e2 : v.intValuation ya
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K ya) :=
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v ya).symm
      calc v.intValuation xa
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (a * algebraMap (NumberField.RingOfIntegers K) K ya) := by
            rw [hstar]; exact e1
        _ = IsDedekindDomain.HeightOneSpectrum.valuation K v a *
              IsDedekindDomain.HeightOneSpectrum.valuation K v
                (algebraMap (NumberField.RingOfIntegers K) K ya) := Valuation.map_mul _ _ _
        _ ≤ 1 * IsDedekindDomain.HeightOneSpectrum.valuation K v
                (algebraMap (NumberField.RingOfIntegers K) K ya) := mul_le_mul_left ha _
        _ = v.intValuation ya := by rw [one_mul, ← e2]
        _ ≤ WithZero.exp (-(m : ℤ)) := hivy
    have hPprime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
    have hJdvd : (Ideal.span {ya} ⊔ v.asIdeal ^ (m + M)) ∣ v.asIdeal ^ (m + M) :=
      Ideal.dvd_iff_le.mpr le_sup_right
    obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow hPprime (m + M)).mp hJdvd
    have hJ : Ideal.span {ya} ⊔ v.asIdeal ^ (m + M) = v.asIdeal ^ i := associated_iff_eq.mp hassoc
    have hyJ : ya ∈ v.asIdeal ^ i := by
      rw [← hJ]
      exact Ideal.dvd_span_singleton.mp (Ideal.dvd_iff_le.mpr le_sup_left)
    have him : i ≤ m := by
      by_contra hcon
      have hle : m + 1 ≤ i := by omega
      exact hym1 (Ideal.pow_le_pow_right hle hyJ)
    have hxJ : xa ∈ Ideal.span {ya} ⊔ v.asIdeal ^ (m + M) := by
      rw [hJ]
      exact Ideal.pow_le_pow_right him hxm
    obtain ⟨p, hp, w, hw, hpw⟩ := Submodule.mem_sup.mp hxJ
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hp
    refine ⟨r, ?_⟩
    have hxrw : xa = r * ya + w := by rw [← hpw, hr]
    have key : (a - algebraMap (NumberField.RingOfIntegers K) K r)
        * algebraMap (NumberField.RingOfIntegers K) K ya
        = algebraMap (NumberField.RingOfIntegers K) K w := by
      have h1 : algebraMap (NumberField.RingOfIntegers K) K xa
          = algebraMap (NumberField.RingOfIntegers K) K r
              * algebraMap (NumberField.RingOfIntegers K) K ya
            + algebraMap (NumberField.RingOfIntegers K) K w := by
        rw [hxrw, map_add, map_mul]
      rw [sub_mul, hstar, h1]; ring
    have hV : IsDedekindDomain.HeightOneSpectrum.valuation K v
          (a - algebraMap (NumberField.RingOfIntegers K) K r) * v.intValuation ya
        = v.intValuation w := by
      rw [← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v ya,
        ← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v w,
        ← Valuation.map_mul, key]
    have hwb : v.intValuation w ≤ WithZero.exp (-((m + M : ℕ) : ℤ)) :=
      (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v w (m + M)).mpr hw
    calc IsDedekindDomain.HeightOneSpectrum.valuation K v
          (a - algebraMap (NumberField.RingOfIntegers K) K r)
        = IsDedekindDomain.HeightOneSpectrum.valuation K v
            (a - algebraMap (NumberField.RingOfIntegers K) K r) *
            (WithZero.exp (-(m : ℤ)) * WithZero.exp (m : ℤ)) := by
          rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, mul_one]
      _ = (IsDedekindDomain.HeightOneSpectrum.valuation K v
            (a - algebraMap (NumberField.RingOfIntegers K) K r) * v.intValuation ya) *
            WithZero.exp (m : ℤ) := by
          rw [← hexpm, mul_assoc]
      _ = v.intValuation w * WithZero.exp (m : ℤ) := by rw [hV]
      _ ≤ WithZero.exp (-((m + M : ℕ) : ℤ)) * WithZero.exp (m : ℤ) :=
          mul_le_mul_left hwb _
      _ = WithZero.exp (-(M : ℤ)) := by
          rw [← WithZero.exp_add]
          congr 1
          push_cast
          ring
  have h_approx_int : ∀ (z : v.adicCompletion K), Valued.v z ≤ 1 → ∀ (M : ℕ),
      ∃ r : NumberField.RingOfIntegers K,
        Valued.v (z - algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K r)) ≤ WithZero.exp (-(M : ℤ)) := by
    intro z hz M
    have hdense : DenseRange (fun y : K => algebraMap K (v.adicCompletion K) y) := by
      letI : Valued K (WithZero (Multiplicative ℤ)) :=
        IsDedekindDomain.HeightOneSpectrum.adicValued (K := K) v
      exact UniformSpace.Completion.denseRange_coe
    let γ : (WithZero (Multiplicative ℤ))ˣ :=
      Units.mk0 (WithZero.exp (-(M : ℤ))) WithZero.exp_ne_zero
    have hnhds : {y : v.adicCompletion K |
        Valued.v (y - z) < (γ : WithZero (Multiplicative ℤ))} ∈ nhds z :=
      Valued.mem_nhds.mpr ⟨γ, subset_rfl⟩
    obtain ⟨u, hu1, k, hk⟩ := mem_closure_iff_nhds.mp (hdense z) _ hnhds
    have hkl : Valued.v (z - algebraMap K (v.adicCompletion K) k) ≤ WithZero.exp (-(M : ℤ)) := by
      dsimp only at hk
      rw [Valuation.map_sub_swap, hk]
      exact le_of_lt hu1
    have hexple : WithZero.exp (-(M : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
      rw [← WithZero.exp_zero]
      exact WithZero.exp_le_exp.mpr (by omega)
    have hvc : ∀ x : K, Valued.v (algebraMap K (v.adicCompletion K) x) =
        IsDedekindDomain.HeightOneSpectrum.valuation K v x :=
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v
    have hvk : IsDedekindDomain.HeightOneSpectrum.valuation K v k ≤ 1 := by
      rw [← hvc k]
      have hsplit : algebraMap K (v.adicCompletion K) k =
          z - (z - algebraMap K (v.adicCompletion K) k) := by ring
      rw [hsplit]
      exact le_trans (Valuation.map_sub Valued.v _ _) (max_le hz (le_trans hkl hexple))
    obtain ⟨r, hr⟩ := h_approx_K k hvk M
    refine ⟨r, ?_⟩
    have hsplit2 : z - algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K r) =
        (z - algebraMap K (v.adicCompletion K) k) +
          algebraMap K (v.adicCompletion K)
            (k - algebraMap (NumberField.RingOfIntegers K) K r) := by
      rw [map_sub]; ring
    rw [hsplit2]
    refine le_trans (Valuation.map_add Valued.v _ _) (max_le hkl ?_)
    rw [hvc]
    exact hr
  have h_quad_repr_mod : ∀ (r : NumberField.RingOfIntegers K),
      (∀ s : NumberField.RingOfIntegers K, s ^ 2 + s - r ∉ v.asIdeal) →
      ∀ (u : NumberField.RingOfIntegers K),
        ∃ x y : NumberField.RingOfIntegers K,
          x ^ 2 - x * y - r * y ^ 2 - u ∈ v.asIdeal := by
    intro r hr u
    have key : ∀ (F : Type u) [Field F] [Finite F] (ρ w : F),
        (∀ σ : F, σ ^ 2 + σ ≠ ρ) → ∃ A B : F, A ^ 2 - A * B - ρ * B ^ 2 = w := by
      intro F _ _ ρ w hρ
      letI := Fintype.ofFinite F
      by_cases hch : ringChar F = 2
      · obtain ⟨t, ht⟩ := FiniteField.isSquare_of_char_two hch w
        exact ⟨t, 0, by rw [ht]; ring⟩
      · have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hch
        set c : F := (2 : F)⁻¹ with hcdef
        have hc : 2 * c = 1 := mul_inv_cancel₀ h2
        have hd : c ^ 2 + ρ ≠ 0 := fun h => hρ (-c) (by linear_combination (-1 : F) * h + c * hc)
        have hdeg1 : (Polynomial.C (1 : F) * Polynomial.X ^ 2 + Polynomial.C (0 : F) * Polynomial.X
            + Polynomial.C (0 : F)).degree = 2 := Polynomial.degree_quadratic one_ne_zero
        have hdeg2 : (Polynomial.C (-(c ^ 2 + ρ)) * Polynomial.X ^ 2
            + Polynomial.C (0 : F) * Polynomial.X + Polynomial.C (-w)).degree = 2 :=
          Polynomial.degree_quadratic (neg_ne_zero.mpr hd)
        have hcard : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two hch
        obtain ⟨s, t, hst⟩ := FiniteField.exists_root_sum_quadratic hdeg1 hdeg2 hcard
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_C] at hst
        exact ⟨s + c * t, t, by linear_combination hst + (s * t + c * t ^ 2) * hc⟩
    haveI : Finite (NumberField.RingOfIntegers K ⧸ v.asIdeal) := inferInstance
    letI : Field (NumberField.RingOfIntegers K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
    have hsurj : Function.Surjective (Ideal.Quotient.mk v.asIdeal :
        NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K ⧸ v.asIdeal) :=
      Ideal.Quotient.mk_surjective
    have hAS : ∀ σ : NumberField.RingOfIntegers K ⧸ v.asIdeal,
        σ ^ 2 + σ ≠ Ideal.Quotient.mk v.asIdeal r := by
      intro σ hσ
      obtain ⟨s, rfl⟩ := hsurj σ
      refine hr s ?_
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add, map_pow, hσ, sub_self]
    obtain ⟨A, B, hAB⟩ := key (NumberField.RingOfIntegers K ⧸ v.asIdeal)
      (Ideal.Quotient.mk v.asIdeal r) (Ideal.Quotient.mk v.asIdeal u) hAS
    obtain ⟨x, hx⟩ := hsurj A
    obtain ⟨y, hy⟩ := hsurj B
    refine ⟨x, y, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [map_sub, map_mul, map_pow, hx, hy]
    linear_combination hAB
  have h_quad_root : ∀ (b c x₀ : v.adicCompletion K),
      Valued.v (2 * x₀ + b) = (1 : WithZero (Multiplicative ℤ)) →
      Valued.v (x₀ ^ 2 + b * x₀ + c) < (1 : WithZero (Multiplicative ℤ)) →
      ∃ x : v.adicCompletion K, x ^ 2 + b * x + c = 0 := by
    intro b c x₀ hder hval
    have hdbl : ∀ t : v.adicCompletion K, Valued.v (2 * t) ≤ Valued.v t := by
      intro t
      have e : (2 : v.adicCompletion K) * t = t + t := by ring
      have h : Valued.v (t + t) ≤ max (Valued.v t) (Valued.v t) := Valuation.map_add _ _ _
      rw [max_self] at h
      rw [e]
      exact h
    have hstep : ∀ y : v.adicCompletion K,
        Valued.v (2 * y + b) = (1 : WithZero (Multiplicative ℤ)) →
        Valued.v (y ^ 2 + b * y + c) < (1 : WithZero (Multiplicative ℤ)) →
        Valued.v (2 * (y - (y ^ 2 + b * y + c) / (2 * y + b)) + b)
            = (1 : WithZero (Multiplicative ℤ)) ∧
        Valued.v ((y - (y ^ 2 + b * y + c) / (2 * y + b)) ^ 2
              + b * (y - (y ^ 2 + b * y + c) / (2 * y + b)) + c)
            = Valued.v (y ^ 2 + b * y + c) ^ 2 ∧
        Valued.v (y - (y ^ 2 + b * y + c) / (2 * y + b) - y)
            = Valued.v (y ^ 2 + b * y + c) := by
      intro y hD hP
      have hDne : (2 : v.adicCompletion K) * y + b ≠ 0 := by
        intro hcon
        rw [hcon, map_zero] at hD
        exact zero_ne_one hD
      have ht : Valued.v ((y ^ 2 + b * y + c) / (2 * y + b))
          = Valued.v (y ^ 2 + b * y + c) := by
        rw [map_div₀, hD, div_one]
      refine ⟨?_, ?_, ?_⟩
      · have e : 2 * (y - (y ^ 2 + b * y + c) / (2 * y + b)) + b
            = (2 * y + b) - 2 * ((y ^ 2 + b * y + c) / (2 * y + b)) := by ring
        have hlt : Valued.v (2 * ((y ^ 2 + b * y + c) / (2 * y + b)))
            < Valued.v (2 * y + b) := by
          refine lt_of_le_of_lt (hdbl _) ?_
          rw [ht, hD]
          exact hP
        rw [e, Valuation.map_sub_eq_of_lt_left _ hlt, hD]
      · have hcancel : (y ^ 2 + b * y + c) / (2 * y + b) * (2 * y + b)
            = y ^ 2 + b * y + c := div_mul_cancel₀ _ hDne
        have key : (y - (y ^ 2 + b * y + c) / (2 * y + b)) ^ 2
              + b * (y - (y ^ 2 + b * y + c) / (2 * y + b)) + c
            = ((y ^ 2 + b * y + c) / (2 * y + b)) ^ 2 := by
          linear_combination -hcancel
        rw [key, Valuation.map_pow, ht]
      · have key : y - (y ^ 2 + b * y + c) / (2 * y + b) - y
            = -((y ^ 2 + b * y + c) / (2 * y + b)) := by ring
        rw [key, Valuation.map_neg, ht]
    have hdecay : ∀ δ γ : WithZero (Multiplicative ℤ), δ < 1 → γ ≠ 0 →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → δ ^ (2 ^ n) < γ := by
      intro δ γ hδ hγ
      rcases eq_or_ne δ 0 with h0 | h0
      · refine ⟨0, fun n _ => ?_⟩
        rw [h0, zero_pow (Nat.two_pow_pos n).ne']
        exact zero_lt_iff.mpr hγ
      · obtain ⟨a, rfl⟩ : ∃ a : ℤ, δ = ((Multiplicative.ofAdd a : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
          obtain ⟨g, hg⟩ := WithZero.ne_zero_iff_exists.mp h0
          exact ⟨Multiplicative.toAdd g, hg.symm⟩
        obtain ⟨β, rfl⟩ : ∃ β : ℤ, γ = ((Multiplicative.ofAdd β : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
          obtain ⟨g, hg⟩ := WithZero.ne_zero_iff_exists.mp hγ
          exact ⟨Multiplicative.toAdd g, hg.symm⟩
        have ha : a < 0 := by
          have h1 : (Multiplicative.ofAdd a : Multiplicative ℤ) < 1 := WithZero.coe_lt_one.mp hδ
          exact h1
        have hpow : ∀ k : ℕ,
            ((Multiplicative.ofAdd a : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ k
              = ((Multiplicative.ofAdd ((k : ℤ) * a) : Multiplicative ℤ) :
                  WithZero (Multiplicative ℤ)) := by
          intro k
          rw [← WithZero.coe_pow]
          congr 1
        refine ⟨(-β).toNat + 1, fun n hn => ?_⟩
        rw [hpow, WithZero.coe_lt_coe]
        have hbk : -β < ((2 ^ n : ℕ) : ℤ) := by
          have hx : (-β).toNat < n := by omega
          have h1 : (-β).toNat < 2 ^ n := lt_trans hx Nat.lt_two_pow_self
          have h2' : ((-β).toNat : ℤ) < ((2 ^ n : ℕ) : ℤ) := by exact_mod_cast h1
          exact lt_of_le_of_lt (Int.self_le_toNat _) h2'
        have hkpos : (0 : ℤ) ≤ ((2 ^ n : ℕ) : ℤ) := Int.natCast_nonneg _
        have ha1 : a ≤ -1 := by omega
        have hle : ((2 ^ n : ℕ) : ℤ) * a ≤ ((2 ^ n : ℕ) : ℤ) * (-1) :=
          mul_le_mul_of_nonneg_left ha1 hkpos
        have hgoal : ((2 ^ n : ℕ) : ℤ) * a < β := by linarith
        exact hgoal
    obtain ⟨ε, hεdef⟩ : ∃ ε : WithZero (Multiplicative ℤ),
        ε = Valued.v (x₀ ^ 2 + b * x₀ + c) := ⟨_, rfl⟩
    have hε : ε < (1 : WithZero (Multiplicative ℤ)) := by
      rw [hεdef]
      exact hval
    obtain ⟨f, hf0, hfs⟩ : ∃ f : ℕ → v.adicCompletion K, f 0 = x₀ ∧
        ∀ n : ℕ, f (n + 1) = f n - (f n ^ 2 + b * f n + c) / (2 * f n + b) :=
      ⟨fun n => Nat.rec (motive := fun _ => v.adicCompletion K) x₀
        (fun _ y => y - (y ^ 2 + b * y + c) / (2 * y + b)) n, rfl, fun _ => rfl⟩
    have hinv : ∀ n : ℕ, Valued.v (2 * f n + b) = (1 : WithZero (Multiplicative ℤ)) ∧
        Valued.v (f n ^ 2 + b * f n + c) = ε ^ (2 ^ n) := by
      intro n
      induction n with
      | zero =>
        refine ⟨by rw [hf0]; exact hder, ?_⟩
        rw [hf0, pow_zero, pow_one, hεdef]
      | succ n ih =>
        have hlt : Valued.v (f n ^ 2 + b * f n + c) < (1 : WithZero (Multiplicative ℤ)) := by
          rw [ih.2]
          exact pow_lt_one₀ zero_le' hε (Nat.two_pow_pos n).ne'
        obtain ⟨s1, s2, -⟩ := hstep (f n) ih.1 hlt
        refine ⟨by rw [hfs n]; exact s1, ?_⟩
        rw [hfs n, s2, ih.2, ← pow_mul]
        congr 1
    have hdiff : ∀ n : ℕ, Valued.v (f (n + 1) - f n) = ε ^ (2 ^ n) := by
      intro n
      have hlt : Valued.v (f n ^ 2 + b * f n + c) < (1 : WithZero (Multiplicative ℤ)) := by
        rw [(hinv n).2]
        exact pow_lt_one₀ zero_le' hε (Nat.two_pow_pos n).ne'
      obtain ⟨-, -, s3⟩ := hstep (f n) (hinv n).1 hlt
      rw [hfs n, s3, (hinv n).2]
    have hCauchy : Cauchy (Filter.map f Filter.atTop) := by
      refine Valued.cauchy_iff.mpr ⟨inferInstance, ?_⟩
      intro γ
      obtain ⟨N, hN⟩ := hdecay ε (γ : WithZero (Multiplicative ℤ)) hε (Units.ne_zero γ)
      have htel : ∀ m : ℕ, N ≤ m → Valued.v (f m - f N) < (γ : WithZero (Multiplicative ℤ)) := by
        intro m hm
        induction m, hm using Nat.le_induction with
        | base =>
          rw [sub_self, map_zero]
          exact zero_lt_iff.mpr (Units.ne_zero γ)
        | succ m hm ih =>
          have e : f (m + 1) - f N = (f (m + 1) - f m) + (f m - f N) := by ring
          rw [e]
          refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ih)
          rw [hdiff m]
          exact hN m hm
      refine ⟨f '' (Set.Ici N), Filter.image_mem_map (Filter.Ici_mem_atTop N), ?_⟩
      rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
      have e : f j - f i = (f j - f N) - (f i - f N) := by ring
      rw [e]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt (htel j hj) (htel i hi))
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hCauchy
    have hPlim : Filter.Tendsto (fun n : ℕ => f n ^ 2 + b * f n + c) Filter.atTop
        (nhds (x ^ 2 + b * x + c)) :=
      ((hx.pow 2).add (tendsto_const_nhds.mul hx)).add tendsto_const_nhds
    have hzero : Filter.Tendsto (fun n : ℕ => f n ^ 2 + b * f n + c) Filter.atTop
        (nhds (0 : v.adicCompletion K)) := by
      rw [Filter.tendsto_def]
      intro s hs
      obtain ⟨γ, hγs⟩ := Valued.mem_nhds_zero.mp hs
      obtain ⟨N, hN⟩ := hdecay ε (γ : WithZero (Multiplicative ℤ)) hε (Units.ne_zero γ)
      refine Filter.mem_of_superset (Filter.Ici_mem_atTop N) ?_
      intro n hn
      apply hγs
      show Valued.v (f n ^ 2 + b * f n + c) < (γ : WithZero (Multiplicative ℤ))
      rw [(hinv n).2]
      exact hN n hn
    exact ⟨x, tendsto_nhds_unique hPlim hzero⟩
  obtain ⟨emb, hemb⟩ : ∃ emb : NumberField.RingOfIntegers K →+* v.adicCompletion K,
      ∀ w : NumberField.RingOfIntegers K, emb w = algebraMap K (v.adicCompletion K)
        (algebraMap (NumberField.RingOfIntegers K) K w) :=
    ⟨(algebraMap K (v.adicCompletion K)).comp
      (algebraMap (NumberField.RingOfIntegers K) K), fun _ => rfl⟩
  have h2ne : (2 : v.adicCompletion K) ≠ 0 := by
    intro hcon
    have hK2 : (2 : K) ≠ 0 := by norm_num
    apply hK2
    apply (algebraMap K (v.adicCompletion K)).injective
    rw [map_ofNat, map_zero]
    exact hcon
  have N1 : ∀ w : NumberField.RingOfIntegers K, Valued.v (emb w) ≤ 1 := by
    intro w
    rw [hemb]
    have hcoe : Valued.v (algebraMap K (v.adicCompletion K)
        (algebraMap (NumberField.RingOfIntegers K) K w))
        = IsDedekindDomain.HeightOneSpectrum.valuation K v
            (algebraMap (NumberField.RingOfIntegers K) K w) :=
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
    rw [hcoe]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one v w
  have N2 : ∀ w : NumberField.RingOfIntegers K,
      Valued.v (emb w) < 1 ↔ w ∈ v.asIdeal := by
    intro w
    rw [hemb]
    have hcoe : Valued.v (algebraMap K (v.adicCompletion K)
        (algebraMap (NumberField.RingOfIntegers K) K w))
        = IsDedekindDomain.HeightOneSpectrum.valuation K v
            (algebraMap (NumberField.RingOfIntegers K) K w) :=
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
    rw [hcoe]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem v w
  have N2' : ∀ w : NumberField.RingOfIntegers K, w ∉ v.asIdeal → Valued.v (emb w) = 1 := by
    intro w hw
    rcases lt_or_eq_of_le (N1 w) with h | h
    · exact absurd ((N2 w).mp h) hw
    · exact h
  have hlift : ∀ ρ X Y u : v.adicCompletion K, Valued.v ρ = 1 →
      Valued.v (X ^ 2 - X * Y - ρ * Y ^ 2 - u) < 1 →
      (Valued.v (2 * X - Y) = 1 ∨ Valued.v (X + 2 * ρ * Y) = 1) →
      ∃ z t : v.adicCompletion K, z ^ 2 - (1 + 4 * ρ) * t ^ 2 = u := by
    intro ρ X Y u hρ1 hstar hdich
    have hρ0 : ρ ≠ 0 := by
      intro h
      rw [h, Valuation.map_zero] at hρ1
      exact zero_ne_one hρ1
    have hXY : ∃ X₁ Y₁ : v.adicCompletion K, X₁ ^ 2 - X₁ * Y₁ - ρ * Y₁ ^ 2 = u := by
      rcases hdich with hA | hB
      · have hder : Valued.v (2 * X + -Y) = (1 : WithZero (Multiplicative ℤ)) := by
          have he : 2 * X + -Y = 2 * X - Y := by ring
          rw [he]
          exact hA
        have hval : Valued.v (X ^ 2 + -Y * X + -(ρ * Y ^ 2 + u))
            < (1 : WithZero (Multiplicative ℤ)) := by
          have he : X ^ 2 + -Y * X + -(ρ * Y ^ 2 + u)
              = X ^ 2 - X * Y - ρ * Y ^ 2 - u := by ring
          rw [he]
          exact hstar
        obtain ⟨x, hx⟩ := h_quad_root (-Y) (-(ρ * Y ^ 2 + u)) X hder hval
        exact ⟨x, Y, by linear_combination hx⟩
      · have hder : Valued.v (2 * Y + X / ρ) = (1 : WithZero (Multiplicative ℤ)) := by
          have he : 2 * Y + X / ρ = (X + 2 * ρ * Y) / ρ := by
            field_simp
            ring
          rw [he, map_div₀, hB, hρ1, div_one]
        have hval : Valued.v (Y ^ 2 + X / ρ * Y + -((X ^ 2 - u) / ρ))
            < (1 : WithZero (Multiplicative ℤ)) := by
          have he : Y ^ 2 + X / ρ * Y + -((X ^ 2 - u) / ρ)
              = -((X ^ 2 - X * Y - ρ * Y ^ 2 - u) / ρ) := by
            field_simp
            ring
          rw [he, Valuation.map_neg, map_div₀, hρ1, div_one]
          exact hstar
        obtain ⟨y, hy⟩ := h_quad_root (X / ρ) (-((X ^ 2 - u) / ρ)) Y hder hval
        refine ⟨X, y, ?_⟩
        have hexp : ρ * (y ^ 2 + X / ρ * y + -((X ^ 2 - u) / ρ))
            = ρ * y ^ 2 + X * y - X ^ 2 + u := by
          field_simp
          ring
        have h4 : ρ * y ^ 2 + X * y - X ^ 2 + u = 0 := by
          rw [← hexp, hy, mul_zero]
        linear_combination -h4
    obtain ⟨X₁, Y₁, hXY1⟩ := hXY
    refine ⟨X₁ - Y₁ / 2, Y₁ / 2, ?_⟩
    have hkey : (X₁ - Y₁ / 2) ^ 2 - (1 + 4 * ρ) * (Y₁ / 2) ^ 2
        = X₁ ^ 2 - X₁ * Y₁ - ρ * Y₁ ^ 2 := by
      field_simp
      ring
    rw [hkey]
    exact hXY1
  obtain ⟨r, hr⟩ := h_not_sq_add_self
  have hrp : r ∉ v.asIdeal := by
    intro hmem
    refine hr 0 ?_
    have he : (0 : NumberField.RingOfIntegers K) ^ 2 + 0 - r = 0 - r := by ring
    rw [he]
    exact Submodule.sub_mem _ (Submodule.zero_mem _) hmem
  have h14 : (1 + 4 * r : NumberField.RingOfIntegers K) ∉ v.asIdeal := by
    intro hmem
    refine hr (2 * r) ?_
    have he : (2 * r : NumberField.RingOfIntegers K) ^ 2 + 2 * r - r = r * (1 + 4 * r) := by
      ring
    rw [he]
    exact Ideal.mul_mem_left _ _ hmem
  have hρ1 : Valued.v (emb r) = 1 := N2' r hrp
  refine ⟨emb r, hρ1, ?_, ?_, ?_⟩
  · have he : (1 : v.adicCompletion K) + 4 * emb r = emb (1 + 4 * r) := by
      simp only [map_add, map_mul, map_one, map_ofNat]
    rw [he]
    exact N2' _ h14
  · intro t ht
    have h2le : Valued.v (2 : v.adicCompletion K) ≤ 1 := by
      have he : (2 : v.adicCompletion K) = emb 2 := by
        rw [map_ofNat]
      rw [he]
      exact N1 2
    have h2v0 : Valued.v (2 : v.adicCompletion K) ≠ 0 := by
      intro hcon
      exact h2ne ((Valuation.zero_iff _).mp hcon)
    have h2pos : (0 : WithZero (Multiplicative ℤ)) < Valued.v (2 : v.adicCompletion K) :=
      zero_lt_iff.mpr h2v0
    have hρ : Valued.v (emb r) ≤ 1 := N1 r
    have hstep2 : Valued.v (t - 1) ≤ Valued.v (2 : v.adicCompletion K) := by
      by_contra hcon
      push_neg at hcon
      have hplus : Valued.v (t + 1) = Valued.v (t - 1) := by
        have he : t + 1 = 2 + (t - 1) := by ring
        rw [he]
        exact Valuation.map_add_eq_of_lt_right _ hcon
      have hprod : (t - 1) * (t + 1) = 2 * 2 * emb r := by linear_combination ht
      have hval : Valued.v (t - 1) * Valued.v (t - 1)
          = Valued.v (2 : v.adicCompletion K) * Valued.v (2 : v.adicCompletion K)
              * Valued.v (emb r) := by
        calc Valued.v (t - 1) * Valued.v (t - 1)
            = Valued.v (t - 1) * Valued.v (t + 1) := by rw [hplus]
          _ = Valued.v ((t - 1) * (t + 1)) := (Valuation.map_mul _ _ _).symm
          _ = Valued.v (2 * 2 * emb r) := by rw [hprod]
          _ = Valued.v (2 : v.adicCompletion K) * Valued.v (2 : v.adicCompletion K)
                * Valued.v (emb r) := by
                rw [Valuation.map_mul, Valuation.map_mul]
      have hle : Valued.v (t - 1) * Valued.v (t - 1)
          ≤ Valued.v (2 : v.adicCompletion K) * Valued.v (2 : v.adicCompletion K) := by
        rw [hval]
        calc Valued.v (2 : v.adicCompletion K) * Valued.v (2 : v.adicCompletion K)
                * Valued.v (emb r)
            ≤ Valued.v (2 : v.adicCompletion K) * Valued.v (2 : v.adicCompletion K) * 1 :=
              mul_le_mul_left' hρ _
          _ = Valued.v (2 : v.adicCompletion K) * Valued.v (2 : v.adicCompletion K) := mul_one _
      exact absurd hle (not_le.mpr (mul_self_lt_mul_self zero_le' hcon))
    obtain ⟨s, hs1, hs2⟩ :
        ∃ s : v.adicCompletion K, Valued.v s ≤ 1 ∧ s ^ 2 + s = emb r := by
      refine ⟨(t - 1) / 2, ?_, ?_⟩
      · have hsmul : (t - 1) / 2 * 2 = t - 1 := by field_simp
        by_contra hcon
        push_neg at hcon
        have hlt : Valued.v (2 : v.adicCompletion K)
            < Valued.v ((t - 1) / 2) * Valued.v (2 : v.adicCompletion K) := by
          calc Valued.v (2 : v.adicCompletion K)
              = 1 * Valued.v (2 : v.adicCompletion K) := (one_mul _).symm
            _ < Valued.v ((t - 1) / 2) * Valued.v (2 : v.adicCompletion K) :=
                mul_lt_mul_of_pos_right hcon h2pos
        rw [← Valuation.map_mul, hsmul] at hlt
        exact absurd hstep2 (not_le.mpr hlt)
      · field_simp
        linear_combination ht
    obtain ⟨y, hy⟩ := h_approx_int s hs1 1
    rw [← hemb y] at hy
    have hd : Valued.v (s - emb y) < 1 := by
      refine lt_of_le_of_lt hy ?_
      rw [← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by norm_num)
    have hid : emb (y ^ 2 + y - r) = (s - emb y) * ((s - emb y) - 2 * s - 1) := by
      simp only [map_sub, map_add, map_pow]
      linear_combination hs2
    have h2s1 : Valued.v (2 * s + 1) ≤ 1 := by
      refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
      · rw [Valuation.map_mul]
        calc Valued.v (2 : v.adicCompletion K) * Valued.v s ≤ 1 * 1 := mul_le_mul' h2le hs1
          _ = 1 := one_mul 1
      · exact le_of_eq (Valuation.map_one _)
    have herr : Valued.v ((s - emb y) - 2 * s - 1) ≤ 1 := by
      have he : (s - emb y) - 2 * s - 1 = (s - emb y) - (2 * s + 1) := by ring
      rw [he]
      exact le_trans (Valuation.map_sub _ _ _) (max_le (le_of_lt hd) h2s1)
    have hfinal : Valued.v (emb (y ^ 2 + y - r)) < 1 := by
      rw [hid, Valuation.map_mul]
      calc Valued.v (s - emb y) * Valued.v ((s - emb y) - 2 * s - 1)
          ≤ Valued.v (s - emb y) * 1 := mul_le_mul_left' herr _
        _ = Valued.v (s - emb y) := mul_one _
        _ < 1 := hd
    exact hr y ((N2 (y ^ 2 + y - r)).mp hfinal)
  · intro u hu
    obtain ⟨u₀, hu₀⟩ := h_approx_int u (le_of_eq hu) 1
    rw [← hemb u₀] at hu₀
    have hdu : Valued.v (u - emb u₀) < 1 := by
      refine lt_of_le_of_lt hu₀ ?_
      rw [← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by norm_num)
    have hw0 : Valued.v (emb u₀) = 1 := by
      rcases lt_or_eq_of_le (N1 u₀) with h | h
      · exfalso
        have hmax : Valued.v (emb u₀ + (u - emb u₀))
            ≤ max (Valued.v (emb u₀)) (Valued.v (u - emb u₀)) := Valuation.map_add _ _ _
        have he : emb u₀ + (u - emb u₀) = u := by ring
        rw [he, hu] at hmax
        exact absurd hmax (not_le.mpr (max_lt h hdu))
      · exact h
    have hu0p : u₀ ∉ v.asIdeal := by
      intro hmem
      have h' := (N2 u₀).mpr hmem
      rw [hw0] at h'
      exact lt_irrefl _ h'
    obtain ⟨x₀, y₀, hP⟩ := h_quad_repr_mod r hr u₀
    have hPlt : Valued.v (emb x₀ ^ 2 - emb x₀ * emb y₀ - emb r * emb y₀ ^ 2 - emb u₀) < 1 := by
      have he : emb x₀ ^ 2 - emb x₀ * emb y₀ - emb r * emb y₀ ^ 2 - emb u₀
          = emb (x₀ ^ 2 - x₀ * y₀ - r * y₀ ^ 2 - u₀) := by
        simp only [map_sub, map_mul, map_pow]
      rw [he]
      exact (N2 _).mpr hP
    have hstar : Valued.v (emb x₀ ^ 2 - emb x₀ * emb y₀ - emb r * emb y₀ ^ 2 - u) < 1 := by
      have he : emb x₀ ^ 2 - emb x₀ * emb y₀ - emb r * emb y₀ ^ 2 - u
          = (emb x₀ ^ 2 - emb x₀ * emb y₀ - emb r * emb y₀ ^ 2 - emb u₀)
            + (emb u₀ - u) := by ring
      rw [he]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hPlt ?_)
      rw [Valuation.map_sub_swap]
      exact hdu
    have hdichI : (2 * x₀ - y₀) ∉ v.asIdeal ∨ (x₀ + 2 * r * y₀) ∉ v.asIdeal := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨hA, hB⟩ := hcon
      have hmulmem : x₀ * (1 + 4 * r) ∈ v.asIdeal := by
        have he : x₀ * (1 + 4 * r) = (x₀ + 2 * r * y₀) + 2 * r * (2 * x₀ - y₀) := by ring
        rw [he]
        exact Submodule.add_mem _ hB (Ideal.mul_mem_left _ _ hA)
      have hx0p : x₀ ∈ v.asIdeal := by
        rcases Ideal.IsPrime.mem_or_mem inferInstance hmulmem with h | h
        · exact h
        · exact absurd h h14
      have hy0p : y₀ ∈ v.asIdeal := by
        have he : y₀ = 2 * x₀ - (2 * x₀ - y₀) := by ring
        rw [he]
        exact Submodule.sub_mem _ (Ideal.mul_mem_left _ _ hx0p) hA
      have hq : x₀ ^ 2 - x₀ * y₀ - r * y₀ ^ 2 ∈ v.asIdeal := by
        have he : x₀ ^ 2 - x₀ * y₀ - r * y₀ ^ 2 = x₀ * (x₀ - y₀) - r * y₀ * y₀ := by ring
        rw [he]
        exact Submodule.sub_mem _ (Ideal.mul_mem_right _ _ hx0p) (Ideal.mul_mem_left _ _ hy0p)
      refine hu0p ?_
      have he : u₀ = (x₀ ^ 2 - x₀ * y₀ - r * y₀ ^ 2)
          - (x₀ ^ 2 - x₀ * y₀ - r * y₀ ^ 2 - u₀) := by ring
      rw [he]
      exact Submodule.sub_mem _ hq hP
    have hdich : Valued.v (2 * emb x₀ - emb y₀) = 1
        ∨ Valued.v (emb x₀ + 2 * emb r * emb y₀) = 1 := by
      rcases hdichI with hA | hB
      · left
        have he : 2 * emb x₀ - emb y₀ = emb (2 * x₀ - y₀) := by
          simp only [map_sub, map_mul, map_ofNat]
        rw [he]
        exact N2' _ hA
      · right
        have he : emb x₀ + 2 * emb r * emb y₀ = emb (x₀ + 2 * r * y₀) := by
          simp only [map_add, map_mul, map_ofNat]
        rw [he]
        exact N2' _ hB
    exact hlift (emb r) (emb x₀) (emb y₀) u hρ1 hstar hdich

theorem exists_pure_repr_one_add_four_mul_nonsquare {K : Type u} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (δ x : v.adicCompletion K) (hδ : δ ≠ 0) (hx : x ≠ 0)
    (hns : ∀ t : v.adicCompletion K, t ^ 2 ≠ δ)
    (hxn : ¬ ∃ z t : v.adicCompletion K, z ^ 2 - δ * t ^ 2 = x) :
    ∃ p q r ρd : v.adicCompletion K,
      Valued.v ρd ≤ 1 ∧
      Valued.v (1 + 4 * ρd) = 1 ∧
      (∀ t : v.adicCompletion K, t ^ 2 ≠ 1 + 4 * ρd) ∧
      δ * p ^ 2 + x * q ^ 2 - δ * x * r ^ 2 = 1 + 4 * ρd :=
by
  classical
  have h_approx_K : ∀ (a : K), IsDedekindDomain.HeightOneSpectrum.valuation K v a ≤ 1 →
      ∀ (M : ℕ), ∃ r : NumberField.RingOfIntegers K,
        IsDedekindDomain.HeightOneSpectrum.valuation K v
          (a - algebraMap (NumberField.RingOfIntegers K) K r) ≤ WithZero.exp (-(M : ℤ)) := by
    intro a ha M
    obtain ⟨xa, ya, hya, hxya⟩ :=
      IsFractionRing.div_surjective (A := NumberField.RingOfIntegers K) (K := K) a
    have hy0 : ya ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hya
    have hiy : algebraMap (NumberField.RingOfIntegers K) K ya ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hya
    have hstar : a * algebraMap (NumberField.RingOfIntegers K) K ya
        = algebraMap (NumberField.RingOfIntegers K) K xa := by
      rw [← hxya]
      exact div_mul_cancel₀ _ hiy
    obtain ⟨m, hym, hym1, hexpm⟩ :
        ∃ m : ℕ, ya ∈ v.asIdeal ^ m ∧ ya ∉ v.asIdeal ^ (m + 1) ∧
          WithZero.exp (-(m : ℤ)) = v.intValuation ya := by
      have ht0 : v.intValuation ya ≠ 0 :=
        IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero v ya hy0
      have ht1 : v.intValuation ya ≤ 1 :=
        IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v ya
      obtain ⟨k, hk⟩ : ∃ k : ℤ, WithZero.exp k = v.intValuation ya := ⟨_, WithZero.exp_log ht0⟩
      have hkle : k ≤ 0 := by
        have hstep : WithZero.exp k ≤ WithZero.exp (0 : ℤ) := by
          rw [hk, WithZero.exp_zero]; exact ht1
        exact WithZero.exp_le_exp.mp hstep
      have hcast : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      have hexpm : WithZero.exp (-(((-k).toNat : ℕ) : ℤ)) = v.intValuation ya := by
        rw [hcast, neg_neg, hk]
      refine ⟨(-k).toNat, ?_, ?_, hexpm⟩
      · exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya _).mp
          (le_of_eq hexpm.symm)
      · intro hcon
        have hle :=
          (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya
            ((-k).toNat + 1)).mpr hcon
        have he : (-(((-k).toNat + 1 : ℕ) : ℤ)) = k - 1 := by
          rw [Nat.cast_add, Nat.cast_one, hcast]; ring
        rw [he, ← hk] at hle
        have := WithZero.exp_le_exp.mp hle
        omega
    have hivy : v.intValuation ya ≤ WithZero.exp (-(m : ℤ)) :=
      (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya m).mpr hym
    have hxm : xa ∈ v.asIdeal ^ m := by
      refine (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v xa m).mp ?_
      have e1 : v.intValuation xa
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K xa) :=
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v xa).symm
      have e2 : v.intValuation ya
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K ya) :=
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v ya).symm
      calc v.intValuation xa
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (a * algebraMap (NumberField.RingOfIntegers K) K ya) := by
            rw [hstar]; exact e1
        _ = IsDedekindDomain.HeightOneSpectrum.valuation K v a *
              IsDedekindDomain.HeightOneSpectrum.valuation K v
                (algebraMap (NumberField.RingOfIntegers K) K ya) := Valuation.map_mul _ _ _
        _ ≤ 1 * IsDedekindDomain.HeightOneSpectrum.valuation K v
                (algebraMap (NumberField.RingOfIntegers K) K ya) := mul_le_mul_left ha _
        _ = v.intValuation ya := by rw [one_mul, ← e2]
        _ ≤ WithZero.exp (-(m : ℤ)) := hivy
    have hPprime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
    have hJdvd : (Ideal.span {ya} ⊔ v.asIdeal ^ (m + M)) ∣ v.asIdeal ^ (m + M) :=
      Ideal.dvd_iff_le.mpr le_sup_right
    obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow hPprime (m + M)).mp hJdvd
    have hJ : Ideal.span {ya} ⊔ v.asIdeal ^ (m + M) = v.asIdeal ^ i := associated_iff_eq.mp hassoc
    have hyJ : ya ∈ v.asIdeal ^ i := by
      rw [← hJ]
      exact Ideal.dvd_span_singleton.mp (Ideal.dvd_iff_le.mpr le_sup_left)
    have him : i ≤ m := by
      by_contra hcon
      have hle : m + 1 ≤ i := by omega
      exact hym1 (Ideal.pow_le_pow_right hle hyJ)
    have hxJ : xa ∈ Ideal.span {ya} ⊔ v.asIdeal ^ (m + M) := by
      rw [hJ]
      exact Ideal.pow_le_pow_right him hxm
    obtain ⟨p, hp, w, hw, hpw⟩ := Submodule.mem_sup.mp hxJ
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hp
    refine ⟨r, ?_⟩
    have hxrw : xa = r * ya + w := by rw [← hpw, hr]
    have key : (a - algebraMap (NumberField.RingOfIntegers K) K r)
        * algebraMap (NumberField.RingOfIntegers K) K ya
        = algebraMap (NumberField.RingOfIntegers K) K w := by
      have h1 : algebraMap (NumberField.RingOfIntegers K) K xa
          = algebraMap (NumberField.RingOfIntegers K) K r
              * algebraMap (NumberField.RingOfIntegers K) K ya
            + algebraMap (NumberField.RingOfIntegers K) K w := by
        rw [hxrw, map_add, map_mul]
      rw [sub_mul, hstar, h1]; ring
    have hV : IsDedekindDomain.HeightOneSpectrum.valuation K v
          (a - algebraMap (NumberField.RingOfIntegers K) K r) * v.intValuation ya
        = v.intValuation w := by
      rw [← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v ya,
        ← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v w,
        ← Valuation.map_mul, key]
    have hwb : v.intValuation w ≤ WithZero.exp (-((m + M : ℕ) : ℤ)) :=
      (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v w (m + M)).mpr hw
    calc IsDedekindDomain.HeightOneSpectrum.valuation K v
          (a - algebraMap (NumberField.RingOfIntegers K) K r)
        = IsDedekindDomain.HeightOneSpectrum.valuation K v
            (a - algebraMap (NumberField.RingOfIntegers K) K r) *
            (WithZero.exp (-(m : ℤ)) * WithZero.exp (m : ℤ)) := by
          rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, mul_one]
      _ = (IsDedekindDomain.HeightOneSpectrum.valuation K v
            (a - algebraMap (NumberField.RingOfIntegers K) K r) * v.intValuation ya) *
            WithZero.exp (m : ℤ) := by
          rw [← hexpm, mul_assoc]
      _ = v.intValuation w * WithZero.exp (m : ℤ) := by rw [hV]
      _ ≤ WithZero.exp (-((m + M : ℕ) : ℤ)) * WithZero.exp (m : ℤ) :=
          mul_le_mul_left hwb _
      _ = WithZero.exp (-(M : ℤ)) := by
          rw [← WithZero.exp_add]
          congr 1
          push_cast
          ring
  have h_approx_int : ∀ (z : v.adicCompletion K), Valued.v z ≤ 1 → ∀ (M : ℕ),
      ∃ r : NumberField.RingOfIntegers K,
        Valued.v (z - algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K r)) ≤ WithZero.exp (-(M : ℤ)) := by
    intro z hz M
    have hdense : DenseRange (fun y : K => algebraMap K (v.adicCompletion K) y) := by
      letI : Valued K (WithZero (Multiplicative ℤ)) :=
        IsDedekindDomain.HeightOneSpectrum.adicValued (K := K) v
      exact UniformSpace.Completion.denseRange_coe
    let γ : (WithZero (Multiplicative ℤ))ˣ :=
      Units.mk0 (WithZero.exp (-(M : ℤ))) WithZero.exp_ne_zero
    have hnhds : {y : v.adicCompletion K |
        Valued.v (y - z) < (γ : WithZero (Multiplicative ℤ))} ∈ nhds z :=
      Valued.mem_nhds.mpr ⟨γ, subset_rfl⟩
    obtain ⟨u, hu1, k, hk⟩ := mem_closure_iff_nhds.mp (hdense z) _ hnhds
    have hkl : Valued.v (z - algebraMap K (v.adicCompletion K) k) ≤ WithZero.exp (-(M : ℤ)) := by
      dsimp only at hk
      rw [Valuation.map_sub_swap, hk]
      exact le_of_lt hu1
    have hexple : WithZero.exp (-(M : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
      rw [← WithZero.exp_zero]
      exact WithZero.exp_le_exp.mpr (by omega)
    have hvc : ∀ x : K, Valued.v (algebraMap K (v.adicCompletion K) x) =
        IsDedekindDomain.HeightOneSpectrum.valuation K v x :=
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v
    have hvk : IsDedekindDomain.HeightOneSpectrum.valuation K v k ≤ 1 := by
      rw [← hvc k]
      have hsplit : algebraMap K (v.adicCompletion K) k =
          z - (z - algebraMap K (v.adicCompletion K) k) := by ring
      rw [hsplit]
      exact le_trans (Valuation.map_sub Valued.v _ _) (max_le hz (le_trans hkl hexple))
    obtain ⟨r, hr⟩ := h_approx_K k hvk M
    refine ⟨r, ?_⟩
    have hsplit2 : z - algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K r) =
        (z - algebraMap K (v.adicCompletion K) k) +
          algebraMap K (v.adicCompletion K)
            (k - algebraMap (NumberField.RingOfIntegers K) K r) := by
      rw [map_sub]; ring
    rw [hsplit2]
    refine le_trans (Valuation.map_add Valued.v _ _) (max_le hkl ?_)
    rw [hvc]
    exact hr
  have h_unitSq_approx : ∀ (e m : ℕ), m < e →
      Valued.v (2 : v.adicCompletion K) = WithZero.exp (-(e : ℤ)) →
      ∀ (a : v.adicCompletion K), Valued.v a = 1 →
      ∀ (c : v.adicCompletion K), Valued.v c = 1 →
      Valued.v (a - c ^ 2) ≤ WithZero.exp (-(2 * (m : ℤ))) →
      ∃ c' : v.adicCompletion K, Valued.v c' = 1 ∧
        Valued.v (a - c' ^ 2) ≤ WithZero.exp (-(2 * (m : ℤ) + 1)) := by
    intro e m hm h2 a ha c hc hac
    have hone : (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) := WithZero.exp_zero.symm
    have hexplt1 : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
      rw [hone, WithZero.exp_lt_exp]
      omega
    have hdisc : ∀ γ : WithZero (Multiplicative ℤ), γ < 1 → γ ≤ WithZero.exp (-1 : ℤ) := by
      intro γ hγ
      rcases eq_or_ne γ 0 with rfl | h0
      · exact zero_le'
      · have hk := WithZero.exp_log h0
        rw [← hk] at hγ ⊢
        rw [hone, WithZero.exp_lt_exp] at hγ
        rw [WithZero.exp_le_exp]
        omega
    have htors : ∀ γ : WithZero (Multiplicative ℤ), γ ^ 2 = 1 → γ = 1 := by
      intro γ hγ
      have h0 : γ ≠ 0 := by
        intro hh
        rw [hh] at hγ
        simp at hγ
      have hk := WithZero.exp_log h0
      rw [← hk] at hγ ⊢
      rw [← WithZero.exp_nsmul, hone] at hγ
      have hz := WithZero.exp_inj.mp hγ
      simp only [nsmul_eq_mul, Nat.cast_ofNat] at hz
      rw [show WithZero.log γ = 0 by omega, WithZero.exp_zero]
    have hexpe : (WithZero.exp (-(e : ℤ)) : WithZero (Multiplicative ℤ))
        ≤ WithZero.exp (-1 : ℤ) := by
      rw [WithZero.exp_le_exp]
      omega
    have hcoe : ∀ k : K, Valued.v (algebraMap K (v.adicCompletion K) k)
        = IsDedekindDomain.HeightOneSpectrum.valuation K v k :=
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v
    have hint : ∀ x : NumberField.RingOfIntegers K,
        IsDedekindDomain.HeightOneSpectrum.valuation K v
            (algebraMap (NumberField.RingOfIntegers K) K x)
          = IsDedekindDomain.HeightOneSpectrum.intValuation v x :=
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v
    have hivlt : ∀ x : NumberField.RingOfIntegers K,
        IsDedekindDomain.HeightOneSpectrum.intValuation v x < 1 ↔ x ∈ v.asIdeal :=
      fun x => IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem v x
    have hvle1 : ∀ x : NumberField.RingOfIntegers K,
        IsDedekindDomain.HeightOneSpectrum.valuation K v
          (algebraMap (NumberField.RingOfIntegers K) K x) ≤ 1 :=
      IsDedekindDomain.HeightOneSpectrum.valuation_le_one v
    have hbridge : ∀ x : NumberField.RingOfIntegers K,
        Valued.v (algebraMap K (v.adicCompletion K)
            (algebraMap (NumberField.RingOfIntegers K) K x)) ≤ WithZero.exp (-1 : ℤ)
          ↔ x ∈ v.asIdeal := by
      intro x
      rw [hcoe, hint]
      constructor
      · intro h
        exact (hivlt x).mp (lt_of_le_of_lt h hexplt1)
      · intro h
        exact hdisc _ ((hivlt x).mpr h)
    have h2mem : (2 : NumberField.RingOfIntegers K) ∈ v.asIdeal := by
      rw [← hbridge]
      have hcast : algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K (2 : NumberField.RingOfIntegers K))
          = (2 : v.adicCompletion K) := by
        simp only [map_ofNat]
      rw [hcast, h2]
      exact hexpe
    have hressq : ∀ y : NumberField.RingOfIntegers K,
        ∃ s : NumberField.RingOfIntegers K, s ^ 2 - y ∈ v.asIdeal := by
      intro y
      letI : Field (NumberField.RingOfIntegers K ⧸ v.asIdeal) :=
        Ideal.Quotient.field v.asIdeal
      haveI : CharP (NumberField.RingOfIntegers K ⧸ v.asIdeal)
          (ringChar (NumberField.RingOfIntegers K ⧸ v.asIdeal)) := ringChar.charP _
      have hzero : ((2 : ℕ) : NumberField.RingOfIntegers K ⧸ v.asIdeal) = 0 := by
        have h := (Ideal.Quotient.eq_zero_iff_mem (I := v.asIdeal)
          (a := (2 : NumberField.RingOfIntegers K))).mpr h2mem
        simpa using h
      have hdvd : ringChar (NumberField.RingOfIntegers K ⧸ v.asIdeal) ∣ 2 := ringChar.dvd hzero
      have hprime : Nat.Prime (ringChar (NumberField.RingOfIntegers K ⧸ v.asIdeal)) :=
        CharP.char_is_prime (NumberField.RingOfIntegers K ⧸ v.asIdeal) _
      have hchar : ringChar (NumberField.RingOfIntegers K ⧸ v.asIdeal) = 2 :=
        (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp hdvd
      obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two hchar (Ideal.Quotient.mk v.asIdeal y)
      obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective r
      refine ⟨s, ?_⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hs, hr]
      ring
    obtain ⟨π, hπ⟩ : ∃ π : v.adicCompletion K, Valued.v π = WithZero.exp (-1 : ℤ) := by
      obtain ⟨π₀, hπ₀⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer K v
      exact ⟨algebraMap K (v.adicCompletion K) π₀, by rw [hcoe, hπ₀]⟩
    have hπ0 : π ≠ 0 := by
      intro h
      rw [h, Valuation.map_zero] at hπ
      exact WithZero.exp_ne_zero hπ.symm
    have hπpow : ∀ k : ℕ, Valued.v (π ^ k) = WithZero.exp (-(k : ℤ)) := by
      intro k
      have hk : k • (-1 : ℤ) = -(k : ℤ) := by simp
      rw [map_pow, hπ, ← WithZero.exp_nsmul, hk]
    have hcast2m : -((2 * m : ℕ) : ℤ) = -(2 * (m : ℤ)) := by
      push_cast
      ring
    have hpow2m : Valued.v (π ^ (2 * m)) = WithZero.exp (-(2 * (m : ℤ))) := by
      rw [hπpow, hcast2m]
    have hπ2m0 : (π ^ (2 * m) : v.adicCompletion K) ≠ 0 := pow_ne_zero _ hπ0
    obtain ⟨u, hu, hueq⟩ : ∃ u : v.adicCompletion K,
        Valued.v u ≤ 1 ∧ π ^ (2 * m) * u = a - c ^ 2 := by
      refine ⟨(a - c ^ 2) / π ^ (2 * m), ?_, ?_⟩
      · rw [map_div₀, hpow2m, div_le_iff₀ (zero_lt_iff.mpr WithZero.exp_ne_zero), one_mul]
        exact hac
      · field_simp
    obtain ⟨y, hy⟩ := h_approx_int u hu 1
    have hy' : Valued.v (u - algebraMap K (v.adicCompletion K)
        (algebraMap (NumberField.RingOfIntegers K) K y)) ≤ WithZero.exp (-1 : ℤ) := by
      have hc1 : ((1 : ℕ) : ℤ) = 1 := Nat.cast_one
      rwa [hc1] at hy
    obtain ⟨z, hz1, hzy⟩ : ∃ z : v.adicCompletion K, Valued.v z ≤ 1 ∧
        Valued.v (algebraMap K (v.adicCompletion K)
            (algebraMap (NumberField.RingOfIntegers K) K y) - z ^ 2)
          ≤ WithZero.exp (-1 : ℤ) := by
      obtain ⟨s, hs⟩ := hressq y
      refine ⟨algebraMap K (v.adicCompletion K)
        (algebraMap (NumberField.RingOfIntegers K) K s), ?_, ?_⟩
      · rw [hcoe]
        exact hvle1 s
      · have hmem := (hbridge (s ^ 2 - y)).mpr hs
        have hrw : algebraMap K (v.adicCompletion K)
            (algebraMap (NumberField.RingOfIntegers K) K (s ^ 2 - y))
            = (algebraMap K (v.adicCompletion K)
                (algebraMap (NumberField.RingOfIntegers K) K s)) ^ 2
              - algebraMap K (v.adicCompletion K)
                (algebraMap (NumberField.RingOfIntegers K) K y) := by
          simp only [map_sub, map_pow]
        rw [hrw] at hmem
        rw [show algebraMap K (v.adicCompletion K)
              (algebraMap (NumberField.RingOfIntegers K) K y)
              - (algebraMap K (v.adicCompletion K)
                  (algebraMap (NumberField.RingOfIntegers K) K s)) ^ 2
            = -((algebraMap K (v.adicCompletion K)
                  (algebraMap (NumberField.RingOfIntegers K) K s)) ^ 2
                - algebraMap K (v.adicCompletion K)
                  (algebraMap (NumberField.RingOfIntegers K) K y)) by ring,
          Valuation.map_neg]
        exact hmem
    have huz : Valued.v (u - z ^ 2) ≤ WithZero.exp (-1 : ℤ) := by
      have hsplit : u - z ^ 2 = (u - algebraMap K (v.adicCompletion K)
            (algebraMap (NumberField.RingOfIntegers K) K y))
          + (algebraMap K (v.adicCompletion K)
              (algebraMap (NumberField.RingOfIntegers K) K y) - z ^ 2) := by ring
      rw [hsplit]
      exact le_trans (Valuation.map_add _ _ _) (max_le hy' hzy)
    have hw : Valued.v (π ^ m * z) ≤ WithZero.exp (-(m : ℤ)) := by
      rw [map_mul, hπpow]
      calc (WithZero.exp (-(m : ℤ)) : WithZero (Multiplicative ℤ)) * Valued.v z
          ≤ WithZero.exp (-(m : ℤ)) * 1 := mul_le_mul_left' hz1 _
        _ = WithZero.exp (-(m : ℤ)) := mul_one _
    have hwsq : a - c ^ 2 - (π ^ m * z) ^ 2 = π ^ (2 * m) * (u - z ^ 2) := by
      have hp : (π ^ m * z) ^ 2 = π ^ (2 * m) * z ^ 2 := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm m 2]
      rw [hp, ← hueq]
      ring
    have hwsqval : Valued.v (a - c ^ 2 - (π ^ m * z) ^ 2)
        ≤ WithZero.exp (-(2 * (m : ℤ) + 1)) := by
      rw [hwsq, map_mul, hpow2m]
      calc (WithZero.exp (-(2 * (m : ℤ))) : WithZero (Multiplicative ℤ)) * Valued.v (u - z ^ 2)
          ≤ WithZero.exp (-(2 * (m : ℤ))) * WithZero.exp (-1 : ℤ) := mul_le_mul_left' huz _
        _ = WithZero.exp (-(2 * (m : ℤ)) + (-1 : ℤ)) := (WithZero.exp_add _ _).symm
        _ = WithZero.exp (-(2 * (m : ℤ) + 1)) := by
            congr 1
            ring
    have hcross : Valued.v (2 * c * (π ^ m * z)) ≤ WithZero.exp (-(2 * (m : ℤ) + 1)) := by
      rw [map_mul, map_mul, h2, hc, mul_one]
      calc (WithZero.exp (-(e : ℤ)) : WithZero (Multiplicative ℤ)) * Valued.v (π ^ m * z)
          ≤ WithZero.exp (-(e : ℤ)) * WithZero.exp (-(m : ℤ)) := mul_le_mul_left' hw _
        _ = WithZero.exp (-(e : ℤ) + -(m : ℤ)) := (WithZero.exp_add _ _).symm
        _ ≤ WithZero.exp (-(2 * (m : ℤ) + 1)) := by
            rw [WithZero.exp_le_exp]
            omega
    have hmain : Valued.v (a - (c + π ^ m * z) ^ 2) ≤ WithZero.exp (-(2 * (m : ℤ) + 1)) := by
      have hid : a - (c + π ^ m * z) ^ 2
          = (a - c ^ 2 - (π ^ m * z) ^ 2) - 2 * c * (π ^ m * z) := by ring
      rw [hid]
      exact le_trans (Valuation.map_sub _ _ _) (max_le hwsqval hcross)
    refine ⟨c + π ^ m * z, ?_, hmain⟩
    have hlt : Valued.v (a - (c + π ^ m * z) ^ 2) < Valued.v a := by
      rw [ha]
      calc Valued.v (a - (c + π ^ m * z) ^ 2)
          ≤ WithZero.exp (-(2 * (m : ℤ) + 1)) := hmain
        _ ≤ WithZero.exp (-1 : ℤ) := by
            rw [WithZero.exp_le_exp]
            omega
        _ < 1 := hexplt1
    have hsq : Valued.v ((c + π ^ m * z) ^ 2) = 1 := by
      have hid2 : (c + π ^ m * z) ^ 2 = a + -(a - (c + π ^ m * z) ^ 2) := by ring
      have hne : Valued.v a ≠ Valued.v (-(a - (c + π ^ m * z) ^ 2)) := by
        rw [Valuation.map_neg]
        exact ne_of_gt hlt
      rw [hid2, Valuation.map_add_of_distinct_val _ hne, Valuation.map_neg,
        max_eq_left (le_of_lt hlt), ha]
    refine htors _ ?_
    rw [← map_pow]
    exact hsq
  have h_level_succ : ∀ (e n : ℕ), n < 2 * e →
      Valued.v (2 : v.adicCompletion K) = WithZero.exp (-(e : ℤ)) →
      ∀ (A B : v.adicCompletion K), A ≠ 0 → B ≠ 0 →
      ∀ (y : v.adicCompletion K), Valued.v y = 1 →
      Valued.v (y - 1) ≤ WithZero.exp (-(n : ℤ)) →
      ∀ (b : v.adicCompletion K), b ≠ 0 →
      (∀ P Q R : v.adicCompletion K, ∃ p q r : v.adicCompletion K,
        A * p ^ 2 + B * q ^ 2 - A * B * r ^ 2
          = y * P ^ 2 + b * Q ^ 2 - y * b * R ^ 2) →
      ∃ y' : v.adicCompletion K, Valued.v y' = 1 ∧
        Valued.v (y' - 1) ≤ WithZero.exp (-((n : ℤ) + 1)) ∧
        ∃ p q r : v.adicCompletion K, A * p ^ 2 + B * q ^ 2 - A * B * r ^ 2 = y' := by
    intro e n hn h2 A B hA hB y hy hlev b hb hsplit
    have he : 0 < e := by omega
    have hval : ∀ c : v.adicCompletion K, c ≠ 0 → ∃ μ : ℤ, Valued.v c = WithZero.exp μ := by
      intro c hc
      have h : Valued.v c ≠ 0 := (Valuation.ne_zero_iff Valued.v).mpr hc
      exact ⟨WithZero.log (Valued.v c), (WithZero.exp_log h).symm⟩
    have hexpinv : ∀ a : ℤ, (WithZero.exp a)⁻¹ = WithZero.exp (-a) := by
      intro a
      have h : WithZero.exp a * WithZero.exp (-a) = (1 : WithZero (Multiplicative ℤ)) := by
        rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
      exact inv_eq_of_mul_eq_one_right h
    obtain ⟨ϖ, hϖ⟩ : ∃ w : v.adicCompletion K, Valued.v w = WithZero.exp (-1 : ℤ) := by
      obtain ⟨π₀, hπ₀⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer K v
      refine ⟨algebraMap K (v.adicCompletion K) π₀, ?_⟩
      have hcoe : Valued.v (algebraMap K (v.adicCompletion K) π₀)
          = IsDedekindDomain.HeightOneSpectrum.valuation K v π₀ :=
        IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π₀
      rw [hcoe, hπ₀]
    have hϖ0 : ϖ ≠ 0 := by
      intro hc
      rw [hc, map_zero] at hϖ
      exact WithZero.exp_ne_zero hϖ.symm
    have hvp : ∀ j : ℤ, Valued.v (ϖ ^ j) = WithZero.exp (-j) := by
      intro j
      induction j using Int.induction_on with
      | zero => simp
      | succ k ih =>
          rw [zpow_add_one₀ hϖ0, map_mul, ih, hϖ, ← WithZero.exp_add]
          congr 1
          ring
      | pred k ih =>
          rw [zpow_sub_one₀ hϖ0, map_mul, ih, map_inv₀, hϖ, hexpinv, ← WithZero.exp_add]
          congr 1
          ring
    have hs3 : ∀ (θ β : v.adicCompletion K) (m κ : ℤ),
        Valued.v θ = WithZero.exp m → Valued.v β = WithZero.exp κ → Even (m - κ) →
        ∃ Q : v.adicCompletion K, Valued.v (θ + β * Q ^ 2) ≤ WithZero.exp (m - 1) := by
      intro θ β m κ hθ hβ hpar
      obtain ⟨i, hi⟩ := hpar
      obtain ⟨q₀, hq0v⟩ : ∃ q₀ : v.adicCompletion K, Valued.v q₀ = WithZero.exp i :=
        ⟨ϖ ^ (-i), by rw [hvp (-i), neg_neg]⟩
      have hq00 : q₀ ≠ 0 := by
        intro h
        rw [h, map_zero] at hq0v
        exact WithZero.exp_ne_zero hq0v.symm
      have hβ0 : β ≠ 0 := by
        intro h
        rw [h, map_zero] at hβ
        exact WithZero.exp_ne_zero hβ.symm
      have hsq : (WithZero.exp i : WithZero (Multiplicative ℤ)) ^ 2 = WithZero.exp (i + i) := by
        rw [WithZero.exp_add, pow_two]
      have hbq : Valued.v (β * q₀ ^ 2) = WithZero.exp m := by
        rw [map_mul, hβ, Valuation.map_pow, hq0v, hsq, ← WithZero.exp_add]
        congr 1
        omega
      obtain ⟨cc, hcmul⟩ : ∃ cc : v.adicCompletion K, (β * q₀ ^ 2) * cc = -θ :=
        ⟨-θ / (β * q₀ ^ 2), by field_simp⟩
      have hccv : Valued.v cc = 1 := by
        have h1 : Valued.v ((β * q₀ ^ 2) * cc) = Valued.v (-θ) := by rw [hcmul]
        rw [map_mul, hbq, Valuation.map_neg, hθ] at h1
        refine mul_left_cancel₀ (show (WithZero.exp m : WithZero (Multiplicative ℤ)) ≠ 0 from
          WithZero.exp_ne_zero) ?_
        rw [mul_one]
        exact h1
      have hone : Valued.v (1 : v.adicCompletion K) = 1 := Valuation.map_one Valued.v
      have hac : Valued.v (cc - 1 ^ 2) ≤ WithZero.exp (-(2 * ((0 : ℕ) : ℤ))) := by
        have hz : (-(2 * (((0 : ℕ)) : ℤ))) = (0 : ℤ) := by push_cast
        rw [hz, WithZero.exp_zero, one_pow]
        have h := Valuation.map_sub Valued.v cc 1
        rw [hccv, hone, max_self] at h
        exact h
      obtain ⟨t, ht1, ht2⟩ :=
        h_unitSq_approx e 0 he h2 cc hccv 1 hone hac
      have ht2' : Valued.v (cc - t ^ 2) ≤ WithZero.exp (-1 : ℤ) := by
        have hz : (-(2 * (((0 : ℕ)) : ℤ) + 1)) = (-1 : ℤ) := by push_cast
        rwa [hz] at ht2
      refine ⟨q₀ * t, ?_⟩
      have hid : θ + β * (q₀ * t) ^ 2 = (β * q₀ ^ 2) * (t ^ 2 - cc) := by
        linear_combination hcmul
      rw [hid, map_mul, hbq, Valuation.map_sub_swap]
      calc (WithZero.exp m : WithZero (Multiplicative ℤ)) * Valued.v (cc - t ^ 2)
          ≤ WithZero.exp m * WithZero.exp (-1 : ℤ) := mul_le_mul' le_rfl ht2'
        _ = WithZero.exp (m - 1) := by rw [← WithZero.exp_add]; congr 1
    by_cases hdone : Valued.v (y - 1) ≤ WithZero.exp (-((n : ℤ) + 1))
    · obtain ⟨p, q, r, hpqr⟩ := hsplit 1 0 0
      exact ⟨y, hy, hdone, p, q, r, by rw [hpqr]; ring⟩
    have hθ0 : y - 1 ≠ 0 := by
      intro h
      apply hdone
      rw [h, map_zero]
      exact zero_le'
    obtain ⟨ℓ, hℓ⟩ := hval (y - 1) hθ0
    have hℓ1 : ℓ ≤ -(n : ℤ) := by
      apply WithZero.exp_le_exp.mp
      rw [← hℓ]
      exact hlev
    have hℓ2 : ¬ (ℓ ≤ -((n : ℤ) + 1)) := by
      intro hcon
      apply hdone
      rw [hℓ]
      exact WithZero.exp_le_exp.mpr hcon
    have hθex : Valued.v (y - 1) = WithZero.exp (-(n : ℤ)) := by
      rw [hℓ]
      congr 1
      omega
    obtain ⟨κ, hκ⟩ := hval b hb
    have hlt1 : (WithZero.exp (-((n : ℤ) + 1)) : WithZero (Multiplicative ℤ)) < 1 := by
      rw [← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by omega)
    rcases Nat.even_or_odd n with hne | hno
    · obtain ⟨m, hm⟩ := hne
      have hnm : (n : ℤ) = 2 * (m : ℤ) := by rw [hm]; push_cast; ring
      have hmlt : m < e := by omega
      have hone : Valued.v (1 : v.adicCompletion K) = 1 := Valuation.map_one Valued.v
      have hac : Valued.v (y - 1 ^ 2) ≤ WithZero.exp (-(2 * (m : ℤ))) := by
        rw [one_pow, ← hnm]
        exact hlev
      obtain ⟨c', hc'1, hc'2⟩ :=
        h_unitSq_approx e m hmlt h2 y hy 1 hone hac
      have hc'0 : c' ≠ 0 := by
        intro h
        rw [h, map_zero] at hc'1
        exact zero_ne_one hc'1
      obtain ⟨p, q, r, hpqr⟩ := hsplit (1 / c') 0 0
      have heq : y * (1 / c') ^ 2 + b * 0 ^ 2 - y * b * 0 ^ 2 = y / c' ^ 2 := by
        field_simp
        ring
      have heq2 : y * (1 / c') ^ 2 + b * 0 ^ 2 - y * b * 0 ^ 2 - 1
          = (y - c' ^ 2) / c' ^ 2 := by
        field_simp
        ring
      refine ⟨y * (1 / c') ^ 2 + b * 0 ^ 2 - y * b * 0 ^ 2, ?_, ?_, p, q, r, hpqr⟩
      · rw [heq, map_div₀, hy, Valuation.map_pow, hc'1, one_pow, div_one]
      · rw [heq2, map_div₀, Valuation.map_pow, hc'1, one_pow, div_one]
        have hz : (-(2 * (m : ℤ) + 1)) = -((n : ℤ) + 1) := by omega
        rw [← hz]
        exact hc'2
    · rcases Int.even_or_odd κ with hke | hko
      · have hm1 : Valued.v (-1 : v.adicCompletion K) = WithZero.exp (0 : ℤ) := by
          rw [Valuation.map_neg, Valuation.map_one, WithZero.exp_zero]
        have hpar : Even ((0 : ℤ) - κ) := by
          have h := hke.neg
          simpa using h
        obtain ⟨Q, hQ⟩ := hs3 (-1) b 0 κ hm1 hκ hpar
        have hβ : Valued.v (b * Q ^ 2 - 1) ≤ WithZero.exp (-1 : ℤ) := by
          have heq : b * Q ^ 2 - 1 = -1 + b * Q ^ 2 := by ring
          rw [heq, show (-1 : ℤ) = (0 : ℤ) - 1 by ring]
          exact hQ
        obtain ⟨p, q, r, hpqr⟩ := hsplit 1 Q Q
        have hid : y * 1 ^ 2 + b * Q ^ 2 - y * b * Q ^ 2 - 1
            = -((y - 1) * (b * Q ^ 2 - 1)) := by ring
        have hlevel : Valued.v (y * 1 ^ 2 + b * Q ^ 2 - y * b * Q ^ 2 - 1)
            ≤ WithZero.exp (-((n : ℤ) + 1)) := by
          rw [hid, Valuation.map_neg, map_mul]
          calc Valued.v (y - 1) * Valued.v (b * Q ^ 2 - 1)
              ≤ WithZero.exp (-(n : ℤ)) * WithZero.exp (-1 : ℤ) := mul_le_mul' hlev hβ
            _ = WithZero.exp (-((n : ℤ) + 1)) := by
                rw [← WithZero.exp_add]; congr 1; ring
        have hunit : Valued.v (y * 1 ^ 2 + b * Q ^ 2 - y * b * Q ^ 2) = 1 := by
          have hlt : Valued.v (-((y - 1) * (b * Q ^ 2 - 1))) < 1 := by
            rw [← hid]
            exact lt_of_le_of_lt hlevel hlt1
          rw [show y * 1 ^ 2 + b * Q ^ 2 - y * b * Q ^ 2
              = 1 + -((y - 1) * (b * Q ^ 2 - 1)) by ring]
          exact Valuation.map_one_add_of_lt Valued.v hlt
        exact ⟨y * 1 ^ 2 + b * Q ^ 2 - y * b * Q ^ 2, hunit, hlevel, p, q, r, hpqr⟩
      · obtain ⟨k, hk⟩ := hno
        obtain ⟨l, hl⟩ := hko
        have hpar : Even (-(n : ℤ) - κ) :=
          ⟨-((k : ℤ) + l + 1), by rw [hk, hl]; push_cast; ring⟩
        obtain ⟨Q, hQ⟩ := hs3 (y - 1) b (-(n : ℤ)) κ hθex hκ hpar
        obtain ⟨p, q, r, hpqr⟩ := hsplit 1 Q 0
        have hid : y * 1 ^ 2 + b * Q ^ 2 - y * b * 0 ^ 2 - 1 = (y - 1) + b * Q ^ 2 := by ring
        have hlevel : Valued.v (y * 1 ^ 2 + b * Q ^ 2 - y * b * 0 ^ 2 - 1)
            ≤ WithZero.exp (-((n : ℤ) + 1)) := by
          rw [hid, show (-((n : ℤ) + 1)) = -(n : ℤ) - 1 by ring]
          exact hQ
        have hunit : Valued.v (y * 1 ^ 2 + b * Q ^ 2 - y * b * 0 ^ 2) = 1 := by
          have hlt : Valued.v ((y - 1) + b * Q ^ 2) < 1 := by
            rw [← hid]
            exact lt_of_le_of_lt hlevel hlt1
          rw [show y * 1 ^ 2 + b * Q ^ 2 - y * b * 0 ^ 2
              = 1 + ((y - 1) + b * Q ^ 2) by ring]
          exact Valuation.map_one_add_of_lt Valued.v hlt
        exact ⟨y * 1 ^ 2 + b * Q ^ 2 - y * b * 0 ^ 2, hunit, hlevel, p, q, r, hpqr⟩
  have hK2 : (2 : K) ≠ 0 := by norm_num
  have h20 : (2 : v.adicCompletion K) ≠ 0 := by
    intro hcon
    apply hK2
    apply (algebraMap K (v.adicCompletion K)).injective
    rw [map_ofNat, map_zero]
    exact hcon
  have h40 : (4 : v.adicCompletion K) ≠ 0 := by
    intro hcon
    have hmm : (2 : v.adicCompletion K) * 2 = 0 := by linear_combination hcon
    rcases mul_eq_zero.mp hmm with h | h <;> exact h20 h
  have hani4 : ∀ z₀ z₁ z₂ z₃ : v.adicCompletion K,
      δ * z₀ ^ 2 + x * z₁ ^ 2 - z₂ ^ 2 - δ * x * z₃ ^ 2 = 0 →
        z₀ = 0 ∧ z₁ = 0 ∧ z₂ = 0 ∧ z₃ = 0 := by
    have hzero : ∀ a b : v.adicCompletion K, a ^ 2 - δ * b ^ 2 = 0 → a = 0 ∧ b = 0 := by
      intro a b h
      have hb : b = 0 := by
        by_contra hb0
        refine hns (a / b) ?_
        field_simp
        linear_combination h
      subst hb
      refine ⟨?_, rfl⟩
      have ha : a ^ 2 = 0 := by linear_combination h
      exact sq_eq_zero_iff.mp ha
    intro z₀ z₁ z₂ z₃ hz
    have key : z₂ ^ 2 - δ * z₀ ^ 2 = x * (z₁ ^ 2 - δ * z₃ ^ 2) := by linear_combination -hz
    have hM : z₁ ^ 2 - δ * z₃ ^ 2 = 0 := by
      by_contra hM0
      apply hxn
      refine ⟨(z₂ * z₁ - δ * z₀ * z₃) / (z₁ ^ 2 - δ * z₃ ^ 2),
        (z₀ * z₁ - z₂ * z₃) / (z₁ ^ 2 - δ * z₃ ^ 2), ?_⟩
      field_simp
      linear_combination (z₁ ^ 2 - δ * z₃ ^ 2) * key
    obtain ⟨h1, h3⟩ := hzero z₁ z₃ hM
    have key2 : z₂ ^ 2 - δ * z₀ ^ 2 = 0 := by rw [key, hM, mul_zero]
    obtain ⟨h2, h0⟩ := hzero z₂ z₀ key2
    exact ⟨h0, h1, h2, h3⟩
  have hani3 : ∀ z₁ z₂ z₃ : v.adicCompletion K,
      δ * z₁ ^ 2 + x * z₂ ^ 2 - δ * x * z₃ ^ 2 = 0 → z₁ = 0 ∧ z₂ = 0 ∧ z₃ = 0 := by
    intro z₁ z₂ z₃ hz
    obtain ⟨e0, e1, -, e3⟩ := hani4 z₁ z₂ 0 z₃ (by linear_combination hz)
    exact ⟨e0, e1, e3⟩
  have h_ternary_split : ∀ (y p q r : v.adicCompletion K), y ≠ 0 →
      δ * p ^ 2 + x * q ^ 2 - δ * x * r ^ 2 = y →
      ∃ b : v.adicCompletion K, b ≠ 0 ∧ ∀ P Q R : v.adicCompletion K,
        ∃ p' q' r' : v.adicCompletion K,
          δ * p' ^ 2 + x * q' ^ 2 - δ * x * r' ^ 2
            = y * P ^ 2 + b * Q ^ 2 - y * b * R ^ 2 := by
    intro y p q r hy hpqr
    obtain ⟨n₁, n₂, n₃, horth, hn⟩ :
        ∃ n₁ n₂ n₃ : v.adicCompletion K,
          δ * p * n₁ + x * q * n₂ - δ * x * r * n₃ = 0 ∧
            ¬ (n₁ = 0 ∧ n₂ = 0 ∧ n₃ = 0) := by
      by_cases hp : p = 0
      · refine ⟨1, 0, 0, ?_, ?_⟩
        · rw [hp]; ring
        · rintro ⟨h1, -, -⟩
          exact one_ne_zero h1
      · refine ⟨-(x * q), δ * p, 0, by ring, ?_⟩
        rintro ⟨-, h2, -⟩
        exact (mul_ne_zero hδ hp) h2
    refine ⟨δ * n₁ ^ 2 + x * n₂ ^ 2 - δ * x * n₃ ^ 2, fun hb => hn (hani3 n₁ n₂ n₃ hb), ?_⟩
    intro P Q R
    refine ⟨P * p + Q * n₁ + R * (x * (r * n₂ - q * n₃)),
            P * q + Q * n₂ + R * (δ * (p * n₃ - r * n₁)),
            P * r + Q * n₃ + R * (p * n₂ - q * n₁), ?_⟩
    linear_combination (P ^ 2 - (δ * n₁ ^ 2 + x * n₂ ^ 2 - δ * x * n₃ ^ 2) * R ^ 2) * hpqr
      + (2 * P * Q + R ^ 2 * (δ * p * n₁ + x * q * n₂ - δ * x * r * n₃)) * horth
  have hexpinv : ∀ a : ℤ, (WithZero.exp a)⁻¹ = WithZero.exp (-a) := by
    intro a
    have h : WithZero.exp a * WithZero.exp (-a) = (1 : WithZero (Multiplicative ℤ)) := by
      rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
    exact inv_eq_of_mul_eq_one_right h
  obtain ⟨ϖ, hϖ⟩ : ∃ w : v.adicCompletion K, Valued.v w = WithZero.exp (-1 : ℤ) := by
    obtain ⟨π₀, hπ₀⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer K v
    refine ⟨algebraMap K (v.adicCompletion K) π₀, ?_⟩
    have hcoe : Valued.v (algebraMap K (v.adicCompletion K) π₀)
        = IsDedekindDomain.HeightOneSpectrum.valuation K v π₀ :=
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π₀
    rw [hcoe, hπ₀]
  have hϖ0 : ϖ ≠ 0 := by
    intro hc
    rw [hc, map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  have hvp : ∀ j : ℤ, Valued.v (ϖ ^ j) = WithZero.exp (-j) := by
    intro j
    induction j using Int.induction_on with
    | zero => simp
    | succ k ih =>
        rw [zpow_add_one₀ hϖ0, map_mul, ih, hϖ, ← WithZero.exp_add]
        congr 1
        ring
    | pred k ih =>
        rw [zpow_sub_one₀ hϖ0, map_mul, ih, map_inv₀, hϖ, hexpinv, ← WithZero.exp_add]
        congr 1
        ring
  have hvsq : ∀ j : ℤ, Valued.v ((ϖ ^ j) ^ 2) = WithZero.exp (-(j + j)) := by
    intro j
    rw [map_pow, hvp j, pow_two, ← WithZero.exp_add]
    congr 1
    ring
  have hval : ∀ c : v.adicCompletion K, c ≠ 0 → ∃ m : ℤ, Valued.v c = WithZero.exp m := by
    intro c hc
    have h : Valued.v c ≠ 0 := (Valuation.ne_zero_iff Valued.v).mpr hc
    exact ⟨WithZero.log (Valued.v c), (WithZero.exp_log h).symm⟩
  have hunit : ∀ (c : v.adicCompletion K) (mc k : ℤ), Valued.v c = WithZero.exp mc →
      mc = k + k → Valued.v (c * (ϖ ^ k) ^ 2) = 1 := by
    intro c mc k hc hmc
    rw [map_mul, hc, hvsq k, ← WithZero.exp_add, hmc,
      show (k + k) + -(k + k) = (0 : ℤ) from by ring, WithZero.exp_zero]
  have h2le : Valued.v (2 : v.adicCompletion K) ≤ 1 := by
    have hsplit2 : (2 : v.adicCompletion K) = 1 + 1 := by norm_num
    rw [hsplit2]
    calc Valued.v ((1 : v.adicCompletion K) + 1)
        ≤ max (Valued.v (1 : v.adicCompletion K)) (Valued.v (1 : v.adicCompletion K)) :=
          Valuation.map_add _ _ _
      _ = 1 := by simp
  obtain ⟨m, hm⟩ := hval 2 h20
  have hmle : m ≤ 0 := by
    have hle : WithZero.exp m ≤ WithZero.exp (0 : ℤ) := by
      rw [WithZero.exp_zero, ← hm]
      exact h2le
    exact WithZero.exp_le_exp.mp hle
  obtain ⟨e, hem⟩ : ∃ e : ℕ, (e : ℤ) = -m := ⟨(-m).toNat, Int.toNat_of_nonneg (by omega)⟩
  have h2e : Valued.v (2 : v.adicCompletion K) = WithZero.exp (-(e : ℤ)) := by
    rw [hm]
    congr 1
    omega
  have h4e : Valued.v (4 : v.adicCompletion K) = WithZero.exp (-(2 * (e : ℤ))) := by
    have h4 : (4 : v.adicCompletion K) = 2 * 2 := by norm_num
    rw [h4, map_mul, h2e, ← WithZero.exp_add]
    congr 1
    ring
  have hsub1 : ∀ z : v.adicCompletion K, Valued.v z = 1 → Valued.v (z - 1) ≤ 1 := by
    intro z hz
    have h := Valuation.map_sub Valued.v z 1
    rw [hz] at h
    simpa using h
  have key : ∀ n : ℕ, n ≤ 2 * e → ∃ y : v.adicCompletion K,
      Valued.v y = 1 ∧ Valued.v (y - 1) ≤ WithZero.exp (-(n : ℤ)) ∧
      ∃ p q r : v.adicCompletion K, δ * p ^ 2 + x * q ^ 2 - δ * x * r ^ 2 = y := by
    intro n
    induction n with
    | zero =>
        intro _
        have hzero : WithZero.exp (-((0 : ℕ) : ℤ)) = (1 : WithZero (Multiplicative ℤ)) := by
          simp
        obtain ⟨m₁, hm₁⟩ := hval δ hδ
        obtain ⟨m₂, hm₂⟩ := hval x hx
        rcases Int.even_or_odd m₁ with ⟨k, hk⟩ | ho₁
        · have hy1 : Valued.v (δ * (ϖ ^ k) ^ 2) = 1 := hunit δ m₁ k hm₁ hk
          exact ⟨δ * (ϖ ^ k) ^ 2, hy1, by rw [hzero]; exact hsub1 _ hy1,
            ϖ ^ k, 0, 0, by ring⟩
        · rcases Int.even_or_odd m₂ with ⟨k, hk⟩ | ho₂
          · have hy1 : Valued.v (x * (ϖ ^ k) ^ 2) = 1 := hunit x m₂ k hm₂ hk
            exact ⟨x * (ϖ ^ k) ^ 2, hy1, by rw [hzero]; exact hsub1 _ hy1,
              0, ϖ ^ k, 0, by ring⟩
          · obtain ⟨k, hk⟩ : Even (m₁ + m₂) := ho₁.add_odd ho₂
            have hdx : Valued.v (δ * x) = WithZero.exp (m₁ + m₂) := by
              rw [map_mul, hm₁, hm₂, ← WithZero.exp_add]
            have hy1 : Valued.v (-(δ * x * (ϖ ^ k) ^ 2)) = 1 := by
              rw [Valuation.map_neg]
              exact hunit (δ * x) (m₁ + m₂) k hdx hk
            exact ⟨-(δ * x * (ϖ ^ k) ^ 2), hy1, by rw [hzero]; exact hsub1 _ hy1,
              0, 0, ϖ ^ k, by ring⟩
    | succ n ih =>
        intro hle
        have hn : n ≤ 2 * e := Nat.le_of_succ_le hle
        have hnlt : n < 2 * e := lt_of_lt_of_le (Nat.lt_succ_self n) hle
        obtain ⟨y, hy1, hylev, p, q, r, hpqr⟩ := ih hn
        have hy0 : y ≠ 0 := by
          intro h
          rw [h, map_zero] at hy1
          exact zero_ne_one hy1
        obtain ⟨b, hb0, hsplit⟩ :=
          h_ternary_split y p q r hy0 hpqr
        obtain ⟨y', hy'1, hy'lev, hy'V⟩ :=
          h_level_succ e n hnlt h2e δ x hδ hx y hy1 hylev b hb0 hsplit
        refine ⟨y', hy'1, ?_, hy'V⟩
        have hcast : (((n + 1 : ℕ) : ℤ)) = (n : ℤ) + 1 := by push_cast; ring
        rw [hcast]
        exact hy'lev
  obtain ⟨y, hy1, hylev, p, q, r, hpqr⟩ := key (2 * e) le_rfl
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, map_zero] at hy1
    exact zero_ne_one hy1
  have hylev' : Valued.v (y - 1) ≤ WithZero.exp (-(2 * (e : ℤ))) := by
    have hcast : (((2 * e : ℕ) : ℤ)) = 2 * (e : ℤ) := by push_cast; ring
    rwa [hcast] at hylev
  have hy4 : (1 : v.adicCompletion K) + 4 * ((y - 1) / 4) = y := by
    field_simp
    ring
  refine ⟨p, q, r, (y - 1) / 4, ?_, ?_, ?_, ?_⟩
  · rw [map_div₀, h4e]
    exact (div_le_one₀ (zero_lt_iff.mpr WithZero.exp_ne_zero)).mpr hylev'
  · rw [hy4]
    exact hy1
  · intro t ht
    rw [hy4] at ht
    obtain ⟨-, -, ht0, -⟩ := hani4 p q t r (by linear_combination hpqr - ht)
    exact hy0 (by rw [← ht, ht0]; norm_num)
  · rw [hy4]
    exact hpqr

theorem sq_mul_of_one_add_four_mul_not_isSquare {K : Type u} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (ρ₁ ρ₂ : v.adicCompletion K)
    (hρ₁ : Valued.v ρ₁ ≤ 1) (hρ₂ : Valued.v ρ₂ ≤ 1)
    (hu₁ : Valued.v (1 + 4 * ρ₁) = 1) (hu₂ : Valued.v (1 + 4 * ρ₂) = 1)
    (hn₁ : ∀ t : v.adicCompletion K, t ^ 2 ≠ 1 + 4 * ρ₁)
    (hn₂ : ∀ t : v.adicCompletion K, t ^ 2 ≠ 1 + 4 * ρ₂) :
    ∃ t : v.adicCompletion K, t ^ 2 = (1 + 4 * ρ₁) * (1 + 4 * ρ₂) :=
by
  classical
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : v.asIdeal ≠ ⊥ := v.ne_bot
  set ι : NumberField.RingOfIntegers K →+* v.adicCompletion K :=
    (algebraMap K (v.adicCompletion K)).comp
      (algebraMap (NumberField.RingOfIntegers K) K) with hιdef
  have hιapp : ∀ z : NumberField.RingOfIntegers K, ι z
      = algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K z) := fun _ => rfl
  have hdict0 : ∀ z : NumberField.RingOfIntegers K,
      Valued.v (ι z) = v.intValuation z := by
    intro z
    have e1 : Valued.v (algebraMap K (v.adicCompletion K)
        (algebraMap (NumberField.RingOfIntegers K) K z))
        = IsDedekindDomain.HeightOneSpectrum.valuation K v
            (algebraMap (NumberField.RingOfIntegers K) K z) :=
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
    have e2 : IsDedekindDomain.HeightOneSpectrum.valuation K v
        (algebraMap (NumberField.RingOfIntegers K) K z) = v.intValuation z :=
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap v z
    rw [hιapp z, e1, e2]
  have hdictLe : ∀ z : NumberField.RingOfIntegers K,
      Valued.v (ι z) ≤ (1 : WithZero (Multiplicative ℤ)) := by
    intro z
    rw [hdict0 z]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v z
  have hdictLt : ∀ z : NumberField.RingOfIntegers K,
      (Valued.v (ι z) < (1 : WithZero (Multiplicative ℤ)) ↔ z ∈ v.asIdeal) := by
    intro z
    rw [hdict0 z]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem v z
  have h_approx_K : ∀ (a : K), IsDedekindDomain.HeightOneSpectrum.valuation K v a ≤ 1 →
      ∀ (M : ℕ), ∃ r : NumberField.RingOfIntegers K,
        IsDedekindDomain.HeightOneSpectrum.valuation K v
          (a - algebraMap (NumberField.RingOfIntegers K) K r) ≤ WithZero.exp (-(M : ℤ)) := by
    intro a ha M
    obtain ⟨xa, ya, hya, hxya⟩ :=
      IsFractionRing.div_surjective (A := NumberField.RingOfIntegers K) (K := K) a
    have hy0 : ya ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hya
    have hiy : algebraMap (NumberField.RingOfIntegers K) K ya ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hya
    have hstar : a * algebraMap (NumberField.RingOfIntegers K) K ya
        = algebraMap (NumberField.RingOfIntegers K) K xa := by
      rw [← hxya]
      exact div_mul_cancel₀ _ hiy
    obtain ⟨m, hym, hym1, hexpm⟩ :
        ∃ m : ℕ, ya ∈ v.asIdeal ^ m ∧ ya ∉ v.asIdeal ^ (m + 1) ∧
          WithZero.exp (-(m : ℤ)) = v.intValuation ya := by
      have ht0 : v.intValuation ya ≠ 0 :=
        IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero v ya hy0
      have ht1 : v.intValuation ya ≤ 1 :=
        IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v ya
      obtain ⟨k, hk⟩ : ∃ k : ℤ, WithZero.exp k = v.intValuation ya := ⟨_, WithZero.exp_log ht0⟩
      have hkle : k ≤ 0 := by
        have hstep : WithZero.exp k ≤ WithZero.exp (0 : ℤ) := by
          rw [hk, WithZero.exp_zero]; exact ht1
        exact WithZero.exp_le_exp.mp hstep
      have hcast : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      have hexpm : WithZero.exp (-(((-k).toNat : ℕ) : ℤ)) = v.intValuation ya := by
        rw [hcast, neg_neg, hk]
      refine ⟨(-k).toNat, ?_, ?_, hexpm⟩
      · exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya _).mp
          (le_of_eq hexpm.symm)
      · intro hcon
        have hle :=
          (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya
            ((-k).toNat + 1)).mpr hcon
        have he : (-(((-k).toNat + 1 : ℕ) : ℤ)) = k - 1 := by
          rw [Nat.cast_add, Nat.cast_one, hcast]; ring
        rw [he, ← hk] at hle
        have := WithZero.exp_le_exp.mp hle
        omega
    have hivy : v.intValuation ya ≤ WithZero.exp (-(m : ℤ)) :=
      (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya m).mpr hym
    have hxm : xa ∈ v.asIdeal ^ m := by
      refine (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v xa m).mp ?_
      have e1 : v.intValuation xa
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K xa) :=
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v xa).symm
      have e2 : v.intValuation ya
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K ya) :=
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v ya).symm
      calc v.intValuation xa
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (a * algebraMap (NumberField.RingOfIntegers K) K ya) := by
            rw [hstar]; exact e1
        _ = IsDedekindDomain.HeightOneSpectrum.valuation K v a *
              IsDedekindDomain.HeightOneSpectrum.valuation K v
                (algebraMap (NumberField.RingOfIntegers K) K ya) := Valuation.map_mul _ _ _
        _ ≤ 1 * IsDedekindDomain.HeightOneSpectrum.valuation K v
                (algebraMap (NumberField.RingOfIntegers K) K ya) := mul_le_mul_left ha _
        _ = v.intValuation ya := by rw [one_mul, ← e2]
        _ ≤ WithZero.exp (-(m : ℤ)) := hivy
    have hPprime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
    have hJdvd : (Ideal.span {ya} ⊔ v.asIdeal ^ (m + M)) ∣ v.asIdeal ^ (m + M) :=
      Ideal.dvd_iff_le.mpr le_sup_right
    obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow hPprime (m + M)).mp hJdvd
    have hJ : Ideal.span {ya} ⊔ v.asIdeal ^ (m + M) = v.asIdeal ^ i := associated_iff_eq.mp hassoc
    have hyJ : ya ∈ v.asIdeal ^ i := by
      rw [← hJ]
      exact Ideal.dvd_span_singleton.mp (Ideal.dvd_iff_le.mpr le_sup_left)
    have him : i ≤ m := by
      by_contra hcon
      have hle : m + 1 ≤ i := by omega
      exact hym1 (Ideal.pow_le_pow_right hle hyJ)
    have hxJ : xa ∈ Ideal.span {ya} ⊔ v.asIdeal ^ (m + M) := by
      rw [hJ]
      exact Ideal.pow_le_pow_right him hxm
    obtain ⟨p, hp, w, hw, hpw⟩ := Submodule.mem_sup.mp hxJ
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hp
    refine ⟨r, ?_⟩
    have hxrw : xa = r * ya + w := by rw [← hpw, hr]
    have key : (a - algebraMap (NumberField.RingOfIntegers K) K r)
        * algebraMap (NumberField.RingOfIntegers K) K ya
        = algebraMap (NumberField.RingOfIntegers K) K w := by
      have h1 : algebraMap (NumberField.RingOfIntegers K) K xa
          = algebraMap (NumberField.RingOfIntegers K) K r
              * algebraMap (NumberField.RingOfIntegers K) K ya
            + algebraMap (NumberField.RingOfIntegers K) K w := by
        rw [hxrw, map_add, map_mul]
      rw [sub_mul, hstar, h1]; ring
    have hV : IsDedekindDomain.HeightOneSpectrum.valuation K v
          (a - algebraMap (NumberField.RingOfIntegers K) K r) * v.intValuation ya
        = v.intValuation w := by
      rw [← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v ya,
        ← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v w,
        ← Valuation.map_mul, key]
    have hwb : v.intValuation w ≤ WithZero.exp (-((m + M : ℕ) : ℤ)) :=
      (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v w (m + M)).mpr hw
    calc IsDedekindDomain.HeightOneSpectrum.valuation K v
          (a - algebraMap (NumberField.RingOfIntegers K) K r)
        = IsDedekindDomain.HeightOneSpectrum.valuation K v
            (a - algebraMap (NumberField.RingOfIntegers K) K r) *
            (WithZero.exp (-(m : ℤ)) * WithZero.exp (m : ℤ)) := by
          rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, mul_one]
      _ = (IsDedekindDomain.HeightOneSpectrum.valuation K v
            (a - algebraMap (NumberField.RingOfIntegers K) K r) * v.intValuation ya) *
            WithZero.exp (m : ℤ) := by
          rw [← hexpm, mul_assoc]
      _ = v.intValuation w * WithZero.exp (m : ℤ) := by rw [hV]
      _ ≤ WithZero.exp (-((m + M : ℕ) : ℤ)) * WithZero.exp (m : ℤ) :=
          mul_le_mul_left hwb _
      _ = WithZero.exp (-(M : ℤ)) := by
          rw [← WithZero.exp_add]
          congr 1
          push_cast
          ring
  have h_approx_int : ∀ (z : v.adicCompletion K), Valued.v z ≤ 1 → ∀ (M : ℕ),
      ∃ r : NumberField.RingOfIntegers K,
        Valued.v (z - algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K r)) ≤ WithZero.exp (-(M : ℤ)) := by
    intro z hz M
    have hdense : DenseRange (fun y : K => algebraMap K (v.adicCompletion K) y) := by
      letI : Valued K (WithZero (Multiplicative ℤ)) :=
        IsDedekindDomain.HeightOneSpectrum.adicValued (K := K) v
      exact UniformSpace.Completion.denseRange_coe
    let γ : (WithZero (Multiplicative ℤ))ˣ :=
      Units.mk0 (WithZero.exp (-(M : ℤ))) WithZero.exp_ne_zero
    have hnhds : {y : v.adicCompletion K |
        Valued.v (y - z) < (γ : WithZero (Multiplicative ℤ))} ∈ nhds z :=
      Valued.mem_nhds.mpr ⟨γ, subset_rfl⟩
    obtain ⟨u, hu1, k, hk⟩ := mem_closure_iff_nhds.mp (hdense z) _ hnhds
    have hkl : Valued.v (z - algebraMap K (v.adicCompletion K) k) ≤ WithZero.exp (-(M : ℤ)) := by
      dsimp only at hk
      rw [Valuation.map_sub_swap, hk]
      exact le_of_lt hu1
    have hexple : WithZero.exp (-(M : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
      rw [← WithZero.exp_zero]
      exact WithZero.exp_le_exp.mpr (by omega)
    have hvc : ∀ x : K, Valued.v (algebraMap K (v.adicCompletion K) x) =
        IsDedekindDomain.HeightOneSpectrum.valuation K v x :=
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v
    have hvk : IsDedekindDomain.HeightOneSpectrum.valuation K v k ≤ 1 := by
      rw [← hvc k]
      have hsplit : algebraMap K (v.adicCompletion K) k =
          z - (z - algebraMap K (v.adicCompletion K) k) := by ring
      rw [hsplit]
      exact le_trans (Valuation.map_sub Valued.v _ _) (max_le hz (le_trans hkl hexple))
    obtain ⟨r, hr⟩ := h_approx_K k hvk M
    refine ⟨r, ?_⟩
    have hsplit2 : z - algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K r) =
        (z - algebraMap K (v.adicCompletion K) k) +
          algebraMap K (v.adicCompletion K)
            (k - algebraMap (NumberField.RingOfIntegers K) K r) := by
      rw [map_sub]; ring
    rw [hsplit2]
    refine le_trans (Valuation.map_add Valued.v _ _) (max_le hkl ?_)
    rw [hvc]
    exact hr
  have h_quad_root : ∀ (b c x₀ : v.adicCompletion K),
      Valued.v (2 * x₀ + b) = (1 : WithZero (Multiplicative ℤ)) →
      Valued.v (x₀ ^ 2 + b * x₀ + c) < (1 : WithZero (Multiplicative ℤ)) →
      ∃ x : v.adicCompletion K, x ^ 2 + b * x + c = 0 := by
    intro b c x₀ hder hval
    have hdbl : ∀ t : v.adicCompletion K, Valued.v (2 * t) ≤ Valued.v t := by
      intro t
      have e : (2 : v.adicCompletion K) * t = t + t := by ring
      have h : Valued.v (t + t) ≤ max (Valued.v t) (Valued.v t) := Valuation.map_add _ _ _
      rw [max_self] at h
      rw [e]
      exact h
    have hstep : ∀ y : v.adicCompletion K,
        Valued.v (2 * y + b) = (1 : WithZero (Multiplicative ℤ)) →
        Valued.v (y ^ 2 + b * y + c) < (1 : WithZero (Multiplicative ℤ)) →
        Valued.v (2 * (y - (y ^ 2 + b * y + c) / (2 * y + b)) + b)
            = (1 : WithZero (Multiplicative ℤ)) ∧
        Valued.v ((y - (y ^ 2 + b * y + c) / (2 * y + b)) ^ 2
              + b * (y - (y ^ 2 + b * y + c) / (2 * y + b)) + c)
            = Valued.v (y ^ 2 + b * y + c) ^ 2 ∧
        Valued.v (y - (y ^ 2 + b * y + c) / (2 * y + b) - y)
            = Valued.v (y ^ 2 + b * y + c) := by
      intro y hD hP
      have hDne : (2 : v.adicCompletion K) * y + b ≠ 0 := by
        intro hcon
        rw [hcon, map_zero] at hD
        exact zero_ne_one hD
      have ht : Valued.v ((y ^ 2 + b * y + c) / (2 * y + b))
          = Valued.v (y ^ 2 + b * y + c) := by
        rw [map_div₀, hD, div_one]
      refine ⟨?_, ?_, ?_⟩
      · have e : 2 * (y - (y ^ 2 + b * y + c) / (2 * y + b)) + b
            = (2 * y + b) - 2 * ((y ^ 2 + b * y + c) / (2 * y + b)) := by ring
        have hlt : Valued.v (2 * ((y ^ 2 + b * y + c) / (2 * y + b)))
            < Valued.v (2 * y + b) := by
          refine lt_of_le_of_lt (hdbl _) ?_
          rw [ht, hD]
          exact hP
        rw [e, Valuation.map_sub_eq_of_lt_left _ hlt, hD]
      · have hcancel : (y ^ 2 + b * y + c) / (2 * y + b) * (2 * y + b)
            = y ^ 2 + b * y + c := div_mul_cancel₀ _ hDne
        have key : (y - (y ^ 2 + b * y + c) / (2 * y + b)) ^ 2
              + b * (y - (y ^ 2 + b * y + c) / (2 * y + b)) + c
            = ((y ^ 2 + b * y + c) / (2 * y + b)) ^ 2 := by
          linear_combination -hcancel
        rw [key, Valuation.map_pow, ht]
      · have key : y - (y ^ 2 + b * y + c) / (2 * y + b) - y
            = -((y ^ 2 + b * y + c) / (2 * y + b)) := by ring
        rw [key, Valuation.map_neg, ht]
    have hdecay : ∀ δ γ : WithZero (Multiplicative ℤ), δ < 1 → γ ≠ 0 →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → δ ^ (2 ^ n) < γ := by
      intro δ γ hδ hγ
      rcases eq_or_ne δ 0 with h0 | h0
      · refine ⟨0, fun n _ => ?_⟩
        rw [h0, zero_pow (Nat.two_pow_pos n).ne']
        exact zero_lt_iff.mpr hγ
      · obtain ⟨a, rfl⟩ : ∃ a : ℤ, δ = ((Multiplicative.ofAdd a : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
          obtain ⟨g, hg⟩ := WithZero.ne_zero_iff_exists.mp h0
          exact ⟨Multiplicative.toAdd g, hg.symm⟩
        obtain ⟨β, rfl⟩ : ∃ β : ℤ, γ = ((Multiplicative.ofAdd β : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
          obtain ⟨g, hg⟩ := WithZero.ne_zero_iff_exists.mp hγ
          exact ⟨Multiplicative.toAdd g, hg.symm⟩
        have ha : a < 0 := WithZero.coe_lt_one.mp hδ
        have hpow : ∀ k : ℕ,
            ((Multiplicative.ofAdd a : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ k
              = ((Multiplicative.ofAdd ((k : ℤ) * a) : Multiplicative ℤ) :
                  WithZero (Multiplicative ℤ)) := by
          intro k
          rw [← WithZero.coe_pow]
          congr 1
        refine ⟨(-β).toNat + 1, fun n hn => ?_⟩
        rw [hpow, WithZero.coe_lt_coe]
        have hbk : -β < ((2 ^ n : ℕ) : ℤ) := by
          have hx : (-β).toNat < n := by omega
          have h1 : (-β).toNat < 2 ^ n := lt_trans hx Nat.lt_two_pow_self
          have h2' : ((-β).toNat : ℤ) < ((2 ^ n : ℕ) : ℤ) := by exact_mod_cast h1
          exact lt_of_le_of_lt (Int.self_le_toNat _) h2'
        have hkpos : (0 : ℤ) ≤ ((2 ^ n : ℕ) : ℤ) := Int.natCast_nonneg _
        have ha1 : a ≤ -1 := by omega
        have hle : ((2 ^ n : ℕ) : ℤ) * a ≤ ((2 ^ n : ℕ) : ℤ) * (-1) :=
          mul_le_mul_of_nonneg_left ha1 hkpos
        have hgoal : ((2 ^ n : ℕ) : ℤ) * a < β := by linarith
        exact hgoal
    obtain ⟨ε, hεdef⟩ : ∃ ε : WithZero (Multiplicative ℤ),
        ε = Valued.v (x₀ ^ 2 + b * x₀ + c) := ⟨_, rfl⟩
    have hε : ε < (1 : WithZero (Multiplicative ℤ)) := by rw [hεdef]; exact hval
    obtain ⟨f, hf0, hfs⟩ : ∃ f : ℕ → v.adicCompletion K, f 0 = x₀ ∧
        ∀ n : ℕ, f (n + 1) = f n - (f n ^ 2 + b * f n + c) / (2 * f n + b) :=
      ⟨fun n => Nat.rec (motive := fun _ => v.adicCompletion K) x₀
        (fun _ y => y - (y ^ 2 + b * y + c) / (2 * y + b)) n, rfl, fun _ => rfl⟩
    have hinv : ∀ n : ℕ, Valued.v (2 * f n + b) = (1 : WithZero (Multiplicative ℤ)) ∧
        Valued.v (f n ^ 2 + b * f n + c) = ε ^ (2 ^ n) := by
      intro n
      induction n with
      | zero =>
        refine ⟨by rw [hf0]; exact hder, ?_⟩
        rw [hf0, pow_zero, pow_one, hεdef]
      | succ n ih =>
        have hlt : Valued.v (f n ^ 2 + b * f n + c) < (1 : WithZero (Multiplicative ℤ)) := by
          rw [ih.2]
          exact pow_lt_one₀ zero_le' hε (Nat.two_pow_pos n).ne'
        obtain ⟨s1, s2, -⟩ := hstep (f n) ih.1 hlt
        refine ⟨by rw [hfs n]; exact s1, ?_⟩
        rw [hfs n, s2, ih.2, ← pow_mul]
        congr 1
    have hdiff : ∀ n : ℕ, Valued.v (f (n + 1) - f n) = ε ^ (2 ^ n) := by
      intro n
      have hlt : Valued.v (f n ^ 2 + b * f n + c) < (1 : WithZero (Multiplicative ℤ)) := by
        rw [(hinv n).2]
        exact pow_lt_one₀ zero_le' hε (Nat.two_pow_pos n).ne'
      obtain ⟨-, -, s3⟩ := hstep (f n) (hinv n).1 hlt
      rw [hfs n, s3, (hinv n).2]
    have hCauchy : Cauchy (Filter.map f Filter.atTop) := by
      refine Valued.cauchy_iff.mpr ⟨inferInstance, ?_⟩
      intro γ
      obtain ⟨N, hN⟩ := hdecay ε (γ : WithZero (Multiplicative ℤ)) hε (Units.ne_zero γ)
      have htel : ∀ m : ℕ, N ≤ m → Valued.v (f m - f N) < (γ : WithZero (Multiplicative ℤ)) := by
        intro m hm
        induction m, hm using Nat.le_induction with
        | base =>
          rw [sub_self, map_zero]
          exact zero_lt_iff.mpr (Units.ne_zero γ)
        | succ m hm ih =>
          have e : f (m + 1) - f N = (f (m + 1) - f m) + (f m - f N) := by ring
          rw [e]
          refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ih)
          rw [hdiff m]
          exact hN m hm
      refine ⟨f '' (Set.Ici N), Filter.image_mem_map (Filter.Ici_mem_atTop N), ?_⟩
      rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
      have e : f j - f i = (f j - f N) - (f i - f N) := by ring
      rw [e]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt (htel j hj) (htel i hi))
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hCauchy
    have hPlim : Filter.Tendsto (fun n : ℕ => f n ^ 2 + b * f n + c) Filter.atTop
        (nhds (x ^ 2 + b * x + c)) :=
      ((hx.pow 2).add (tendsto_const_nhds.mul hx)).add tendsto_const_nhds
    have hzero : Filter.Tendsto (fun n : ℕ => f n ^ 2 + b * f n + c) Filter.atTop
        (nhds (0 : v.adicCompletion K)) := by
      rw [Filter.tendsto_def]
      intro s hs
      obtain ⟨γ, hγs⟩ := Valued.mem_nhds_zero.mp hs
      obtain ⟨N, hN⟩ := hdecay ε (γ : WithZero (Multiplicative ℤ)) hε (Units.ne_zero γ)
      refine Filter.mem_of_superset (Filter.Ici_mem_atTop N) ?_
      intro n hn
      apply hγs
      show Valued.v (f n ^ 2 + b * f n + c) < (γ : WithZero (Multiplicative ℤ))
      rw [(hinv n).2]
      exact hN n hn
    exact ⟨x, tendsto_nhds_unique hPlim hzero⟩
  have hexp1 : (WithZero.exp (-(1 : ℤ)) : WithZero (Multiplicative ℤ)) < 1 := by
    have h := WithZero.exp_lt_exp.mpr (show (-1 : ℤ) < 0 by norm_num)
    rwa [WithZero.exp_zero] at h
  by_cases h2 : Valued.v (2 : v.adicCompletion K) = 1
  · let u : v.adicCompletion K := 1 + 4 * ρ₁
    let w : v.adicCompletion K := 1 + 4 * ρ₂
    have hu : Valued.v u = 1 := hu₁
    have hw : Valued.v w = 1 := hu₂
    have hnu : ∀ t : v.adicCompletion K, t ^ 2 ≠ u := hn₁
    have hnw : ∀ t : v.adicCompletion K, t ^ 2 ≠ w := hn₂
    have HB : ∀ m : v.adicCompletion K, Valued.v m = 1 →
        ∀ a s : NumberField.RingOfIntegers K, Valued.v (m - ι a) < 1 →
        s ^ 2 - a ∈ v.asIdeal → ∃ t : v.adicCompletion K, t ^ 2 = m := by
      intro m hm a s hma hs
      have hanm : a ∉ v.asIdeal := by
        intro hmem
        have h1 : Valued.v (ι a) < 1 := (hdictLt a).mpr hmem
        have e : m = (m - ι a) + ι a := by ring
        have h3 : Valued.v m < 1 := by
          rw [e]
          exact lt_of_le_of_lt (Valuation.map_add Valued.v _ _) (max_lt hma h1)
        rw [hm] at h3
        exact lt_irrefl _ h3
      have hsnm : s ∉ v.asIdeal := by
        intro hmem
        apply hanm
        have e : a = s ^ 2 - (s ^ 2 - a) := by ring
        rw [e]
        exact Ideal.sub_mem _ (Ideal.pow_mem_of_mem _ hmem 2 (by norm_num)) hs
      have hs1 : Valued.v (ι s) = 1 := by
        rcases lt_or_eq_of_le (hdictLe s) with h | h
        · exact absurd ((hdictLt s).mp h) hsnm
        · exact h
      have hd : Valued.v ((ι s) ^ 2 - m) < 1 := by
        have e : (ι s) ^ 2 - m = ι (s ^ 2 - a) + (ι a - m) := by
          rw [map_sub, map_pow]; ring
        have h1 : Valued.v (ι (s ^ 2 - a)) < 1 := (hdictLt _).mpr hs
        have h3 : Valued.v (ι a - m) < 1 := by
          rw [Valuation.map_sub_swap]; exact hma
        rw [e]
        exact lt_of_le_of_lt (Valuation.map_add Valued.v _ _) (max_lt h1 h3)
      have hder : Valued.v (2 * ι s + 0) = (1 : WithZero (Multiplicative ℤ)) := by
        rw [add_zero, Valuation.map_mul, h2, hs1, one_mul]
      have hval : Valued.v ((ι s) ^ 2 + 0 * (ι s) + (-m))
          < (1 : WithZero (Multiplicative ℤ)) := by
        have e : (ι s) ^ 2 + 0 * (ι s) + (-m) = (ι s) ^ 2 - m := by ring
        rw [e]
        exact hd
      obtain ⟨x, hx⟩ := h_quad_root 0 (-m) (ι s) hder hval
      exact ⟨x, by linear_combination hx⟩
    have core : ∀ (F : Type u) [Field F] [Finite F] (x y : F),
        ¬ IsSquare x → ¬ IsSquare y → IsSquare (x * y) := by
      intro F _ _ x y hx hy
      letI : Fintype F := Fintype.ofFinite F
      letI : DecidableEq F := Classical.decEq F
      by_contra hxy
      have e1 : quadraticChar F x = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hx
      have e2 : quadraticChar F y = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hy
      have e3 : quadraticChar F (x * y) = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hxy
      rw [map_mul, e1, e2] at e3
      norm_num at e3
    obtain ⟨a, ha0⟩ := h_approx_int u (le_of_eq hu) 1
    obtain ⟨b, hb0⟩ := h_approx_int w (le_of_eq hw) 1
    have haU : Valued.v (u - ι a) < 1 := by
      rw [hιapp a]
      exact lt_of_le_of_lt ha0 hexp1
    have hbW : Valued.v (w - ι b) < 1 := by
      rw [hιapp b]
      exact lt_of_le_of_lt hb0 hexp1
    have hib : Valued.v (ι b) = 1 := by
      rcases lt_or_eq_of_le (hdictLe b) with h | h
      · exfalso
        have e : w = ι b + (w - ι b) := by ring
        have h3 : Valued.v w < 1 := by
          rw [e]
          exact lt_of_le_of_lt (Valuation.map_add Valued.v _ _) (max_lt h hbW)
        rw [hw] at h3
        exact lt_irrefl _ h3
      · exact h
    have hA : ∀ s : NumberField.RingOfIntegers K, s ^ 2 - a ∉ v.asIdeal := by
      intro s hs
      obtain ⟨t, ht⟩ := HB u hu a s haU hs
      exact hnu t ht
    have hBb : ∀ s : NumberField.RingOfIntegers K, s ^ 2 - b ∉ v.asIdeal := by
      intro s hs
      obtain ⟨t, ht⟩ := HB w hw b s hbW hs
      exact hnw t ht
    letI : Field (NumberField.RingOfIntegers K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
    have hnsq : ∀ c : NumberField.RingOfIntegers K,
        (∀ s : NumberField.RingOfIntegers K, s ^ 2 - c ∉ v.asIdeal) →
        ¬ IsSquare (Ideal.Quotient.mk v.asIdeal c) := by
      intro c hc hsq
      obtain ⟨y, hy⟩ := hsq
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
      apply hc s
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have hy' : Ideal.Quotient.mk v.asIdeal c
          = Ideal.Quotient.mk v.asIdeal s * Ideal.Quotient.mk v.asIdeal s := hy
      rw [map_sub, map_pow, hy']
      ring
    obtain ⟨y, hy⟩ := core (NumberField.RingOfIntegers K ⧸ v.asIdeal)
        (Ideal.Quotient.mk v.asIdeal a) (Ideal.Quotient.mk v.asIdeal b)
        (hnsq a hA) (hnsq b hBb)
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hsab : s ^ 2 - a * b ∈ v.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have hy' : Ideal.Quotient.mk v.asIdeal a * Ideal.Quotient.mk v.asIdeal b
          = Ideal.Quotient.mk v.asIdeal s * Ideal.Quotient.mk v.asIdeal s := hy
      rw [map_sub, map_pow, map_mul, hy']
      ring
    have hmw : Valued.v (u * w) = 1 := by
      rw [Valuation.map_mul, hu, hw, one_mul]
    have hmab : Valued.v (u * w - ι (a * b)) < 1 := by
      have e : u * w - ι a * ι b = u * (w - ι b) + ι b * (u - ι a) := by ring
      have h1 : Valued.v (u * (w - ι b)) < 1 := by
        rw [Valuation.map_mul, hu, one_mul]
        exact hbW
      have h3 : Valued.v (ι b * (u - ι a)) < 1 := by
        rw [Valuation.map_mul, hib, one_mul]
        exact haU
      rw [map_mul ι a b, e]
      exact lt_of_le_of_lt (Valuation.map_add Valued.v _ _) (max_lt h1 h3)
    exact HB (u * w) hmw (a * b) s hmab hsab
  · have hmul_lt : ∀ x y : v.adicCompletion K,
        Valued.v x < (1 : WithZero (Multiplicative ℤ)) → Valued.v y ≤ 1 →
        Valued.v (x * y) < (1 : WithZero (Multiplicative ℤ)) := by
      intro x y hx hy
      rw [map_mul]
      calc Valued.v x * Valued.v y ≤ Valued.v x * 1 := mul_le_mul_left' hy _
        _ = Valued.v x := mul_one _
        _ < 1 := hx
    have hι2 : ι (2 : NumberField.RingOfIntegers K) = (2 : v.adicCompletion K) := map_ofNat ι 2
    have hv2le : Valued.v (2 : v.adicCompletion K) ≤ 1 := by
      have h := hdictLe 2
      rwa [hι2] at h
    have hv2lt : Valued.v (2 : v.adicCompletion K) < 1 := lt_of_le_of_ne hv2le h2
    have h2P : (2 : NumberField.RingOfIntegers K) ∈ v.asIdeal := by
      refine (hdictLt 2).mp ?_
      rw [hι2]
      exact hv2lt
    have hv4lt : Valued.v (4 : v.adicCompletion K) < 1 := by
      have h4 : (4 : v.adicCompletion K) = 2 * 2 := by norm_num
      rw [h4]
      exact hmul_lt 2 2 hv2lt hv2le
    have hv4ρ : Valued.v (4 * ρ₁ * ρ₂ : v.adicCompletion K) < 1 :=
      hmul_lt _ _ (hmul_lt _ _ hv4lt hρ₁) hρ₂
    have hv4ρneg : Valued.v (-(4 * ρ₁ * ρ₂) : v.adicCompletion K) < 1 := by
      rw [Valuation.map_neg]
      exact hv4ρ
    have hensel : ∀ ρ x₀ : v.adicCompletion K, Valued.v x₀ ≤ 1 →
        Valued.v (x₀ ^ 2 + x₀ - ρ) < (1 : WithZero (Multiplicative ℤ)) →
        ∃ x : v.adicCompletion K, x ^ 2 + x = ρ := by
      intro ρ x₀ hx₀ hlt
      have hd1 : Valued.v (2 * x₀ : v.adicCompletion K) < 1 := hmul_lt 2 x₀ hv2lt hx₀
      have hd2 : Valued.v (2 * x₀ : v.adicCompletion K) ≠ Valued.v (1 : v.adicCompletion K) := by
        rw [map_one]
        exact ne_of_lt hd1
      have hder : Valued.v (2 * x₀ + 1) = (1 : WithZero (Multiplicative ℤ)) := by
        rw [Valuation.map_add_of_distinct_val _ hd2, map_one]
        exact max_eq_right (le_of_lt hd1)
      have hval : Valued.v (x₀ ^ 2 + 1 * x₀ + (-ρ)) < (1 : WithZero (Multiplicative ℤ)) := by
        have e : x₀ ^ 2 + 1 * x₀ + (-ρ) = x₀ ^ 2 + x₀ - ρ := by ring
        rw [e]
        exact hlt
      obtain ⟨x, hx⟩ := h_quad_root 1 (-ρ) x₀ hder hval
      exact ⟨x, by linear_combination hx⟩
    have hAS : ∀ ρ : v.adicCompletion K, (∀ t : v.adicCompletion K, t ^ 2 ≠ 1 + 4 * ρ) →
        ∀ x : v.adicCompletion K, x ^ 2 + x ≠ ρ := by
      intro ρ hnr x hx
      exact hnr (1 + 2 * x) (by linear_combination 4 * hx)
    have hnoapprox : ∀ ρ : v.adicCompletion K, (∀ x : v.adicCompletion K, x ^ 2 + x ≠ ρ) →
        ∀ x₀ : v.adicCompletion K, Valued.v x₀ ≤ 1 →
          ¬ (Valued.v (x₀ ^ 2 + x₀ - ρ) < (1 : WithZero (Multiplicative ℤ))) := by
      intro ρ hρ x₀ hx₀ hlt
      obtain ⟨x, hx⟩ := hensel ρ x₀ hx₀ hlt
      exact hρ x hx
    have happrox : ∀ ρ : v.adicCompletion K, Valued.v ρ ≤ 1 →
        ∃ y : NumberField.RingOfIntegers K,
          Valued.v (ι y - ρ) < (1 : WithZero (Multiplicative ℤ)) := by
      intro ρ hρ
      obtain ⟨y, hy⟩ := h_approx_int ρ hρ 1
      refine ⟨y, ?_⟩
      rw [← hιapp y] at hy
      rw [Valuation.map_sub_swap]
      refine lt_of_le_of_lt ?_ hexp1
      simpa using hy
    have hnonres : ∀ (ρ : v.adicCompletion K) (y : NumberField.RingOfIntegers K),
        (∀ x : v.adicCompletion K, x ^ 2 + x ≠ ρ) →
        Valued.v (ι y - ρ) < (1 : WithZero (Multiplicative ℤ)) →
        ∀ s : NumberField.RingOfIntegers K, s ^ 2 + s - y ∉ v.asIdeal := by
      intro ρ y hρ hyρ s hs
      have h1 : Valued.v (ι (s ^ 2 + s - y)) < 1 := (hdictLt _).mpr hs
      have e1 : ι (s ^ 2 + s - y) = (ι s) ^ 2 + ι s - ι y := by
        simp only [map_sub, map_add, map_pow]
      rw [e1] at h1
      have e2 : (ι s) ^ 2 + ι s - ρ = ((ι s) ^ 2 + ι s - ι y) + (ι y - ρ) := by ring
      have h3 : Valued.v ((ι s) ^ 2 + ι s - ρ) < 1 := by
        rw [e2]
        exact Valuation.map_add_lt _ h1 hyρ
      exact hnoapprox ρ hρ (ι s) (hdictLe s) h3
    have hcrux : ∀ a b : NumberField.RingOfIntegers K,
        (∀ s : NumberField.RingOfIntegers K, s ^ 2 + s - a ∉ v.asIdeal) →
        (∀ s : NumberField.RingOfIntegers K, s ^ 2 + s - b ∉ v.asIdeal) →
        ∃ s : NumberField.RingOfIntegers K, s ^ 2 + s - (a + b) ∈ v.asIdeal := by
      intro a b ha hb
      letI : Field (NumberField.RingOfIntegers K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
      have h2k : (2 : NumberField.RingOfIntegers K ⧸ v.asIdeal) = 0 := by
        have h := Ideal.Quotient.eq_zero_iff_mem.mpr h2P
        simpa using h
      have hadd : ∀ y z : NumberField.RingOfIntegers K ⧸ v.asIdeal,
          (y + z) ^ 2 + (y + z) = (y ^ 2 + y) + (z ^ 2 + z) := by
        intro y z
        linear_combination (y * z) * h2k
      set φ : (NumberField.RingOfIntegers K ⧸ v.asIdeal) →+
          (NumberField.RingOfIntegers K ⧸ v.asIdeal) :=
        AddMonoidHom.mk' (fun y => y ^ 2 + y) hadd with hφdef
      have hφ : ∀ y : NumberField.RingOfIntegers K ⧸ v.asIdeal, φ y = y ^ 2 + y := fun _ => rfl
      have hkermem : ∀ y : NumberField.RingOfIntegers K ⧸ v.asIdeal,
          y ∈ φ.ker ↔ (y = 0 ∨ y = 1) := by
        intro y
        rw [AddMonoidHom.mem_ker, hφ]
        constructor
        · intro hy
          have hfac : y * (y + 1) = 0 := by linear_combination hy
          rcases mul_eq_zero.mp hfac with h | h
          · exact Or.inl h
          · exact Or.inr (by linear_combination h - h2k)
        · rintro (rfl | rfl)
          · ring
          · linear_combination h2k
      have hkercard : Nat.card φ.ker = 2 := by
        rw [Nat.card_eq_two_iff]
        refine ⟨⟨0, (hkermem 0).mpr (Or.inl rfl)⟩, ⟨1, (hkermem 1).mpr (Or.inr rfl)⟩, ?_, ?_⟩
        · simp [Subtype.ext_iff]
        · rw [Set.eq_univ_iff_forall]
          intro z
          rcases (hkermem z.1).mp z.2 with h | h
          · exact Or.inl (Subtype.ext h)
          · exact Or.inr (Subtype.ext h)
      haveI : Nonempty φ.range := ⟨⟨0, φ.range.zero_mem⟩⟩
      have hcard : Nat.card φ.ker * Nat.card φ.range
          = Nat.card (NumberField.RingOfIntegers K ⧸ v.asIdeal) := by
        have e1 : Nat.card ((NumberField.RingOfIntegers K ⧸ v.asIdeal) ⧸ φ.ker)
            = Nat.card φ.range :=
          Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv
        have e2 : φ.ker.index = Nat.card ((NumberField.RingOfIntegers K ⧸ v.asIdeal) ⧸ φ.ker) :=
          AddSubgroup.index_eq_card _
        have e3 := AddSubgroup.card_mul_index φ.ker
        rw [← e1, ← e2]
        exact e3
      have hrpos : 0 < Nat.card φ.range := Nat.card_pos
      have hidx : φ.range.index = 2 := by
        have h4 : Nat.card φ.range * φ.range.index = Nat.card φ.range * 2 := by
          rw [AddSubgroup.card_mul_index, ← hcard, hkercard]
          ring
        exact Nat.eq_of_mul_eq_mul_left hrpos h4
      have hmem : ∀ c : NumberField.RingOfIntegers K,
          (Ideal.Quotient.mk v.asIdeal) c ∈ φ.range → ∃ s : NumberField.RingOfIntegers K,
            s ^ 2 + s - c ∈ v.asIdeal := by
        intro c hc
        obtain ⟨y, hy⟩ := AddMonoidHom.mem_range.mp hc
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
        refine ⟨s, ?_⟩
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        have h1 : (Ideal.Quotient.mk v.asIdeal) (s ^ 2 + s - c)
            = ((Ideal.Quotient.mk v.asIdeal) s) ^ 2 + (Ideal.Quotient.mk v.asIdeal) s
              - (Ideal.Quotient.mk v.asIdeal) c := by
          simp
        rw [h1, ← hy, hφ]
        ring
      have hA : (Ideal.Quotient.mk v.asIdeal) a ∉ φ.range := by
        intro hcon
        obtain ⟨s, hs⟩ := hmem a hcon
        exact ha s hs
      have hB : (Ideal.Quotient.mk v.asIdeal) b ∉ φ.range := by
        intro hcon
        obtain ⟨s, hs⟩ := hmem b hcon
        exact hb s hs
      have hsum : (Ideal.Quotient.mk v.asIdeal) a + (Ideal.Quotient.mk v.asIdeal) b ∈ φ.range :=
        (AddSubgroup.add_mem_iff_of_index_two hidx).mpr (iff_of_false hA hB)
      refine hmem (a + b) ?_
      rwa [map_add]
    obtain ⟨y₁, hy₁⟩ := happrox ρ₁ hρ₁
    obtain ⟨y₂, hy₂⟩ := happrox ρ₂ hρ₂
    have hnr₁ := hnonres ρ₁ y₁ (hAS ρ₁ hn₁) hy₁
    have hnr₂ := hnonres ρ₂ y₂ (hAS ρ₂ hn₂) hy₂
    obtain ⟨s, hs⟩ := hcrux y₁ y₂ hnr₁ hnr₂
    have hE : Valued.v ((ι s) ^ 2 + ι s - ι y₁ - ι y₂) < (1 : WithZero (Multiplicative ℤ)) := by
      have h1 : Valued.v (ι (s ^ 2 + s - (y₁ + y₂))) < 1 := (hdictLt _).mpr hs
      have e1 : ι (s ^ 2 + s - (y₁ + y₂)) = (ι s) ^ 2 + ι s - ι y₁ - ι y₂ := by
        simp only [map_sub, map_add, map_pow]
        ring
      rwa [e1] at h1
    have hFinal : Valued.v ((ι s) ^ 2 + ι s - (ρ₁ + ρ₂ + 4 * ρ₁ * ρ₂))
        < (1 : WithZero (Multiplicative ℤ)) := by
      have hid : (ι s) ^ 2 + ι s - (ρ₁ + ρ₂ + 4 * ρ₁ * ρ₂)
          = ((ι s) ^ 2 + ι s - ι y₁ - ι y₂)
            + ((ι y₁ - ρ₁) + ((ι y₂ - ρ₂) + (-(4 * ρ₁ * ρ₂)))) := by ring
      rw [hid]
      exact Valuation.map_add_lt _ hE
        (Valuation.map_add_lt _ hy₁ (Valuation.map_add_lt _ hy₂ hv4ρneg))
    obtain ⟨x, hx⟩ := hensel (ρ₁ + ρ₂ + 4 * ρ₁ * ρ₂) (ι s) (hdictLe s) hFinal
    exact ⟨1 + 2 * x, by linear_combination 4 * hx⟩

theorem hilbLoc_mul_left {K : Type u} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x₁ x₂ y : v.adicCompletion K) (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) (hy : y ≠ 0) :
    hilbLoc v (x₁ * x₂) y = hilbLoc v x₁ y * hilbLoc v x₂ y :=
by
  classical
  have hK2 : (2 : K) ≠ 0 := by norm_num
  have h2ne : (2 : v.adicCompletion K) ≠ 0 := by
    intro hcon
    apply hK2
    apply (algebraMap K (v.adicCompletion K)).injective
    rw [map_ofNat, map_zero]
    exact hcon
  have h_hilb_solv : ∀ (a b : v.adicCompletion K), a ≠ 0 →
      ((∃ x₀ y₀ : v.adicCompletion K, a * x₀ ^ 2 + b * y₀ ^ 2 = 1) ↔
       (∃ z t : v.adicCompletion K, z ^ 2 - b * t ^ 2 = a)) := by
    intro a b ha
    constructor
    · rintro ⟨x₀, y₀, h⟩
      by_cases hx₀ : x₀ = 0
      · subst hx₀
        have hb : b * y₀ ^ 2 = 1 := by linear_combination h
        have h2i : 2 * (2 : v.adicCompletion K)⁻¹ = 1 := mul_inv_cancel₀ h2ne
        refine ⟨(a + 1) * (2 : v.adicCompletion K)⁻¹, (1 - a) * y₀ * (2 : v.adicCompletion K)⁻¹, ?_⟩
        linear_combination (-(1 - a) ^ 2 * ((2 : v.adicCompletion K)⁻¹) ^ 2) * hb +
          (a * (2 * (2 : v.adicCompletion K)⁻¹ + 1)) * h2i
      · have hu : x₀ * x₀⁻¹ = 1 := mul_inv_cancel₀ hx₀
        refine ⟨x₀⁻¹, y₀ * x₀⁻¹, ?_⟩
        linear_combination (-(x₀⁻¹) ^ 2) * h + (a * (x₀ * x₀⁻¹ + 1)) * hu
    · rintro ⟨z, t, h⟩
      by_cases hz : z = 0
      · subst hz
        have hbt : b * t ^ 2 = -a := by linear_combination -h
        have h2a : 2 * a * (2 * a)⁻¹ = 1 := mul_inv_cancel₀ (mul_ne_zero h2ne ha)
        refine ⟨(1 + a) * (2 * a)⁻¹, t * (a - 1) * (2 * a)⁻¹, ?_⟩
        linear_combination ((a - 1) ^ 2 * ((2 * a)⁻¹) ^ 2) * hbt +
          (2 * a * (2 * a)⁻¹ + 1) * h2a
      · have hw : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
        refine ⟨z⁻¹, t * z⁻¹, ?_⟩
        linear_combination (-(z⁻¹) ^ 2) * h + (z * z⁻¹ + 1) * hw
  have h_hilb_eq_one : ∀ (a b : v.adicCompletion K), a ≠ 0 →
      (∃ z t : v.adicCompletion K, z ^ 2 - b * t ^ 2 = a) → hilbLoc v a b = 1 := by
    intro a b ha hnorm
    dsimp [hilbLoc]
    rw [if_pos ((h_hilb_solv a b ha).mpr hnorm)]
  have h_hilb_eq_neg_one : ∀ (a b : v.adicCompletion K), a ≠ 0 →
      (¬ ∃ z t : v.adicCompletion K, z ^ 2 - b * t ^ 2 = a) → hilbLoc v a b = -1 := by
    intro a b ha hnnorm
    dsimp [hilbLoc]
    rw [if_neg (fun h => hnnorm ((h_hilb_solv a b ha).mp h))]
  have mulN : ∀ (b p q : v.adicCompletion K),
      (∃ z t : v.adicCompletion K, z ^ 2 - b * t ^ 2 = p) →
      (∃ z t : v.adicCompletion K, z ^ 2 - b * t ^ 2 = q) →
      (∃ z t : v.adicCompletion K, z ^ 2 - b * t ^ 2 = p * q) := by
    rintro b p q ⟨z₁, t₁, h₁⟩ ⟨z₂, t₂, h₂⟩
    exact ⟨z₁ * z₂ + b * t₁ * t₂, z₁ * t₂ + t₁ * z₂,
      by linear_combination (z₂ ^ 2 - b * t₂ ^ 2) * h₁ + p * h₂⟩
  have invN : ∀ (b p : v.adicCompletion K), p ≠ 0 →
      (∃ z t : v.adicCompletion K, z ^ 2 - b * t ^ 2 = p) →
      (∃ z t : v.adicCompletion K, z ^ 2 - b * t ^ 2 = p⁻¹) := by
    rintro b p hp ⟨z, t, h⟩
    refine ⟨z / p, t / p, ?_⟩
    field_simp
    linear_combination h
  have hx₁₂ : x₁ * x₂ ≠ 0 := mul_ne_zero hx₁ hx₂
  by_cases h1 : ∃ z t : v.adicCompletion K, z ^ 2 - y * t ^ 2 = x₁
  · by_cases h2 : ∃ z t : v.adicCompletion K, z ^ 2 - y * t ^ 2 = x₂
    · rw [h_hilb_eq_one (x₁ * x₂) y hx₁₂ (mulN y x₁ x₂ h1 h2),
          h_hilb_eq_one x₁ y hx₁ h1, h_hilb_eq_one x₂ y hx₂ h2, mul_one]
    · have hn12 : ¬ ∃ z t : v.adicCompletion K, z ^ 2 - y * t ^ 2 = x₁ * x₂ := by
        intro h12
        apply h2
        have h2' := mulN y x₁⁻¹ (x₁ * x₂) (invN y x₁ hx₁ h1) h12
        rwa [inv_mul_cancel_left₀ hx₁ x₂] at h2'
      rw [h_hilb_eq_neg_one (x₁ * x₂) y hx₁₂ hn12,
          h_hilb_eq_one x₁ y hx₁ h1, h_hilb_eq_neg_one x₂ y hx₂ h2, one_mul]
  · by_cases h2 : ∃ z t : v.adicCompletion K, z ^ 2 - y * t ^ 2 = x₂
    · have hn12 : ¬ ∃ z t : v.adicCompletion K, z ^ 2 - y * t ^ 2 = x₁ * x₂ := by
        intro h12
        apply h1
        have h1' := mulN y (x₁ * x₂) x₂⁻¹ h12 (invN y x₂ hx₂ h2)
        rwa [mul_inv_cancel_right₀ hx₂ x₁] at h1'
      rw [h_hilb_eq_neg_one (x₁ * x₂) y hx₁₂ hn12,
          h_hilb_eq_neg_one x₁ y hx₁ h1, h_hilb_eq_one x₂ y hx₂ h2, mul_one]
    · have hns : ∀ t : v.adicCompletion K, t ^ 2 ≠ y := by
        intro t ht
        have ht0 : t ≠ 0 := by
          intro hc
          apply hy
          rw [← ht, hc, zero_pow two_ne_zero]
        apply h1
        refine ⟨(x₁ + 1) / 2, (x₁ - 1) / (2 * t), ?_⟩
        rw [← ht]
        field_simp
        ring
      obtain ⟨ρa, hρa1, ha1, hans, haU⟩ := exists_unramified_artinSchreier_unit v
      let a : v.adicCompletion K := 1 + 4 * ρa
      have ha0 : a ≠ 0 := by
        intro hc
        change Valued.v a = 1 at ha1
        rw [hc, map_zero] at ha1
        exact zero_ne_one ha1
      obtain ⟨π₀, hπ₀⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer K v
      let ϖ : v.adicCompletion K := algebraMap K (v.adicCompletion K) π₀
      have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
        have hcoe : Valued.v (algebraMap K (v.adicCompletion K) π₀) =
            IsDedekindDomain.HeightOneSpectrum.valuation K v π₀ :=
          IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π₀
        change Valued.v (algebraMap K (v.adicCompletion K) π₀) = _
        rw [hcoe, hπ₀]
      have hϖ0 : ϖ ≠ 0 := by
        intro hc
        rw [hc, map_zero] at hϖ
        exact WithZero.exp_ne_zero hϖ.symm
      have hϖ_zpow : ∀ n : ℤ, Valued.v (ϖ ^ n) = WithZero.exp (-n) := by
        intro n
        have h1' : (n : ℤ) • (-1 : ℤ) = -n := by simp
        calc Valued.v (ϖ ^ n) = Valued.v ϖ ^ n := map_zpow₀ _ _ _
          _ = WithZero.exp (-1 : ℤ) ^ n := by rw [hϖ]
          _ = WithZero.exp ((n : ℤ) • (-1 : ℤ)) := (WithZero.exp_zsmul _ _).symm
          _ = WithZero.exp (-n) := by rw [h1']
      let ord_v : v.adicCompletion K → ℤ := fun x => -(Valued.v x).log
      let unitPart : v.adicCompletion K → v.adicCompletion K := fun x => x / ϖ ^ (ord_v x)
      have hval_exp_ord : ∀ x : v.adicCompletion K, x ≠ 0 →
          Valued.v x = WithZero.exp (-(ord_v x)) := by
        intro x hx
        have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff Valued.v).mpr hx
        have h1' : -(ord_v x) = (Valued.v x).log := neg_neg _
        rw [h1', WithZero.exp_log hvx]
      have hunitPart_val : ∀ x : v.adicCompletion K, x ≠ 0 → Valued.v (unitPart x) = 1 := by
        intro x hx
        have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff Valued.v).mpr hx
        dsimp [unitPart]
        rw [map_div₀, hϖ_zpow (ord_v x), ← hval_exp_ord x hx, div_self hvx]
      have hunitPart_spec : ∀ x : v.adicCompletion K, x = ϖ ^ (ord_v x) * unitPart x := by
        intro x
        dsimp [unitPart]
        exact (mul_div_cancel₀ x (zpow_ne_zero _ hϖ0)).symm
      have hstep : ∀ (k : ℤ) (u : v.adicCompletion K), Valued.v u = 1 →
          ∃ z t : v.adicCompletion K, z ^ 2 - a * t ^ 2 = ϖ ^ (k + k) * u := by
        intro k u hu
        have hsq : ϖ ^ (k + k) = (ϖ ^ k) ^ 2 := by
          rw [zpow_add₀ hϖ0, sq]
        rw [hsq]
        exact mulN a ((ϖ ^ k) ^ 2) u ⟨ϖ ^ k, 0, by ring⟩ (haU u hu)
      have hmul : ∀ μ₁ μ₂ : v.adicCompletion K, μ₁ ≠ 0 → μ₂ ≠ 0 →
          (¬ ∃ z t : v.adicCompletion K, z ^ 2 - a * t ^ 2 = μ₁) →
          (¬ ∃ z t : v.adicCompletion K, z ^ 2 - a * t ^ 2 = μ₂) →
          ∃ z t : v.adicCompletion K, z ^ 2 - a * t ^ 2 = μ₁ * μ₂ := by
        intro μ₁ μ₂ hμ1 hμ2 hn1 hn2
        have hodd₁ : Odd (ord_v μ₁) := by
          rcases Int.even_or_odd (ord_v μ₁) with ⟨k, hk⟩ | hod
          · exfalso
            apply hn1
            rw [hunitPart_spec μ₁, hk]
            exact hstep k (unitPart μ₁) (hunitPart_val μ₁ hμ1)
          · exact hod
        have hodd₂ : Odd (ord_v μ₂) := by
          rcases Int.even_or_odd (ord_v μ₂) with ⟨k, hk⟩ | hod
          · exfalso
            apply hn2
            rw [hunitPart_spec μ₂, hk]
            exact hstep k (unitPart μ₂) (hunitPart_val μ₂ hμ2)
          · exact hod
        obtain ⟨k, hk⟩ := hodd₁.add_odd hodd₂
        have hprod : μ₁ * μ₂ = ϖ ^ (k + k) * (unitPart μ₁ * unitPart μ₂) := by
          calc μ₁ * μ₂ = (ϖ ^ (ord_v μ₁) * unitPart μ₁) * (ϖ ^ (ord_v μ₂) * unitPart μ₂) := by
                rw [← hunitPart_spec μ₁, ← hunitPart_spec μ₂]
            _ = (ϖ ^ (ord_v μ₁) * ϖ ^ (ord_v μ₂)) * (unitPart μ₁ * unitPart μ₂) := by ring
            _ = ϖ ^ (ord_v μ₁ + ord_v μ₂) * (unitPart μ₁ * unitPart μ₂) := by
                rw [← zpow_add₀ hϖ0]
            _ = ϖ ^ (k + k) * (unitPart μ₁ * unitPart μ₂) := by rw [hk]
        rw [hprod]
        refine hstep k (unitPart μ₁ * unitPart μ₂) ?_
        rw [map_mul, hunitPart_val μ₁ hμ1, hunitPart_val μ₂ hμ2, mul_one]
      have h_pure_a : ∀ (x : v.adicCompletion K), x ≠ 0 →
          (¬ ∃ z t : v.adicCompletion K, z ^ 2 - y * t ^ 2 = x) →
          ∃ p q r : v.adicCompletion K, y * p ^ 2 + x * q ^ 2 - y * x * r ^ 2 = a := by
        intro x hx hxn
        obtain ⟨p₀, q₀, r₀, ρd, hρd, hd1, hQns, hDeq⟩ :=
          exists_pure_repr_one_add_four_mul_nonsquare v y x hy hx hns hxn
        have hQ0 : (1 : v.adicCompletion K) + 4 * ρd ≠ 0 := by
          intro hc
          rw [hc, map_zero] at hd1
          exact zero_ne_one hd1
        obtain ⟨σ, hσ⟩ :=
          sq_mul_of_one_add_four_mul_not_isSquare v ρa ρd (le_of_eq hρa1) hρd ha1 hd1 hans hQns
        refine ⟨p₀ * (σ / (1 + 4 * ρd)),
                q₀ * (σ / (1 + 4 * ρd)),
                r₀ * (σ / (1 + 4 * ρd)), ?_⟩
        have hhom : y * (p₀ * (σ / (1 + 4 * ρd))) ^ 2
              + x * (q₀ * (σ / (1 + 4 * ρd))) ^ 2
              - y * x * (r₀ * (σ / (1 + 4 * ρd))) ^ 2
            = (σ / (1 + 4 * ρd)) ^ 2 * (1 + 4 * ρd) := by
          linear_combination (σ / (1 + 4 * ρd)) ^ 2 * hDeq
        rw [hhom, div_pow, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 hQ0)]
        change σ ^ 2 * (1 + 4 * ρd) = (1 + 4 * ρa) * (1 + 4 * ρd) ^ 2
        linear_combination (1 + 4 * ρd) * hσ
      have h12 : ∃ z t : v.adicCompletion K, z ^ 2 - y * t ^ 2 = x₁ * x₂ :=
        norm_mul_mem_of_common_pure_repr h2ne a y x₁ x₂ ha0 hy hx₁ hx₂ hns hans h1 h2
          (h_pure_a x₁ hx₁ h1) (h_pure_a x₂ hx₂ h2) hmul
      rw [h_hilb_eq_one (x₁ * x₂) y hx₁₂ h12,
          h_hilb_eq_neg_one x₁ y hx₁ h1, h_hilb_eq_neg_one x₂ y hx₂ h2]
      rfl

theorem local_sqCl_coord_and_hilbLoc_pairing {K : Type u} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (ev kv : ℕ)
    (hev : Valued.v (2 : v.adicCompletion K) = WithZero.exp (-(ev : ℤ)))
    (hkv : Nat.card (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ ev) = 2 ^ kv) :
    ∃ (cl : v.adicCompletion K → (Fin (2 + kv) → ZMod 2))
      (B : (Fin (2 + kv) → ZMod 2) → (Fin (2 + kv) → ZMod 2) → ZMod 2),
      (∀ x y : v.adicCompletion K, x ≠ 0 → y ≠ 0 → cl (x * y) = cl x + cl y) ∧
      (∀ x : v.adicCompletion K, x ≠ 0 → (cl x = 0 ↔ IsSquare x)) ∧
      (∀ c : Fin (2 + kv) → ZMod 2, ∃ u : Kˣ, cl (algebraMap K (v.adicCompletion K) (u : K)) = c) ∧
      (∀ α₁ α₂ β : Fin (2 + kv) → ZMod 2, B (α₁ + α₂) β = B α₁ β + B α₂ β) ∧
      (∀ α β : Fin (2 + kv) → ZMod 2, B α β = B β α) ∧
      (∀ α : Fin (2 + kv) → ZMod 2, (∀ β : Fin (2 + kv) → ZMod 2, B α β = 0) → α = 0) ∧
      (∀ x y : v.adicCompletion K, x ≠ 0 → y ≠ 0 →
        hilbLoc v x y = (-1 : ℤˣ) ^ (B (cl x) (cl y)).val) :=
by
  classical
  have hval_int : ∀ a : NumberField.RingOfIntegers K,
      Valued.v (algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K a))
        = v.intValuation a := by
    intro a
    have h1 : Valued.v (algebraMap K (v.adicCompletion K)
        (algebraMap (NumberField.RingOfIntegers K) K a))
        = IsDedekindDomain.HeightOneSpectrum.valuation K v
            (algebraMap (NumberField.RingOfIntegers K) K a) :=
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v
        (algebraMap (NumberField.RingOfIntegers K) K a)
    rw [h1]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v a
  have hev_int : v.intValuation (2 : NumberField.RingOfIntegers K) = WithZero.exp (-(ev : ℤ)) := by
    rw [← hval_int (2 : NumberField.RingOfIntegers K),
      map_ofNat (algebraMap (NumberField.RingOfIntegers K) K) 2,
      map_ofNat (algebraMap K (v.adicCompletion K)) 2]
    exact hev
  obtain ⟨φ_q, hφ_mul, hφ_sq, hφ_surj⟩ := quotient_units_sqCl_coord v ev kv hev_int hkv
  obtain ⟨red, hred_mul, hred_sq, hred_surj⟩ := adicCompletion_unit_reduction_to_quotient_units v ev hev
  obtain ⟨π₀, hπ₀⟩ := IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer v
  let π_K : K := algebraMap (NumberField.RingOfIntegers K) K π₀
  let ϖ : v.adicCompletion K := algebraMap K (v.adicCompletion K) π_K
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
    change Valued.v (algebraMap K (v.adicCompletion K) (algebraMap (NumberField.RingOfIntegers K) K π₀)) = _
    rw [hval_int π₀, hπ₀]
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  have hπ_K0 : π_K ≠ 0 := by
    intro h
    apply hϖ0
    change algebraMap K (v.adicCompletion K) π_K = 0
    rw [h, map_zero]
  have hϖ_zpow : ∀ n : ℤ, Valued.v (ϖ ^ n) = WithZero.exp (-n) := by
    intro n
    have h1 : (n : ℤ) • (-1 : ℤ) = -n := by simp
    calc Valued.v (ϖ ^ n) = Valued.v ϖ ^ n := map_zpow₀ _ _ _
      _ = WithZero.exp (-1 : ℤ) ^ n := by rw [hϖ]
      _ = WithZero.exp ((n : ℤ) • (-1 : ℤ)) := (WithZero.exp_zsmul _ _).symm
      _ = WithZero.exp (-n) := by rw [h1]
  let ord_v : v.adicCompletion K → ℤ := fun x => -(Valued.v x).log
  let unitPart : v.adicCompletion K → v.adicCompletion K := fun x => x / ϖ ^ (ord_v x)
  have hval_exp_ord : ∀ x : v.adicCompletion K, x ≠ 0 →
      Valued.v x = WithZero.exp (-(ord_v x)) := by
    intro x hx
    have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff Valued.v).mpr hx
    have h1 : -(ord_v x) = (Valued.v x).log := neg_neg _
    rw [h1, WithZero.exp_log hvx]
  have hunitPart_val : ∀ x : v.adicCompletion K, x ≠ 0 → Valued.v (unitPart x) = 1 := by
    intro x hx
    have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff Valued.v).mpr hx
    dsimp [unitPart]
    rw [map_div₀, hϖ_zpow (ord_v x), ← hval_exp_ord x hx, div_self hvx]
  have hunitPart_spec : ∀ x : v.adicCompletion K, x = ϖ ^ (ord_v x) * unitPart x := by
    intro x
    dsimp [unitPart]
    exact (mul_div_cancel₀ x (zpow_ne_zero _ hϖ0)).symm
  have hord_mul : ∀ x y : v.adicCompletion K, x ≠ 0 → y ≠ 0 →
      ord_v (x * y) = ord_v x + ord_v y := by
    intro x y hx hy
    have hxy : Valued.v (x * y) = WithZero.exp (-(ord_v x + ord_v y)) := by
      rw [map_mul, hval_exp_ord x hx, hval_exp_ord y hy, ← WithZero.exp_add, neg_add]
    dsimp [ord_v]
    rw [hxy, WithZero.log_exp, neg_neg]
  have hunitPart_mul : ∀ x y : v.adicCompletion K, x ≠ 0 → y ≠ 0 →
      unitPart (x * y) = unitPart x * unitPart y := by
    intro x y hx hy
    dsimp [unitPart]
    rw [hord_mul x y hx hy, zpow_add₀ hϖ0, div_mul_div_comm]
  let cl : v.adicCompletion K → (Fin (2 + kv) → ZMod 2) := fun x i =>
    if x = 0 then 0
    else if h : i.val = 0 then (ord_v x : ZMod 2)
    else φ_q (red (unitPart x)) ⟨i.val - 1, by omega⟩
  have hcl_mul : ∀ x y : v.adicCompletion K, x ≠ 0 → y ≠ 0 → cl (x * y) = cl x + cl y := by
    intro x y hx hy
    have hxy : x * y ≠ 0 := mul_ne_zero hx hy
    ext i
    change cl (x * y) i = cl x i + cl y i
    dsimp [cl]
    rw [if_neg hxy, if_neg hx, if_neg hy]
    split_ifs with hi
    · rw [hord_mul x y hx hy, Int.cast_add]
    · rw [hunitPart_mul x y hx hy,
          hred_mul _ _ (hunitPart_val x hx) (hunitPart_val y hy),
          hφ_mul]
      rfl
  have zmod2_add_self : ∀ a : ZMod 2, a + a = 0 := by decide
  have hcl_sq : ∀ x : v.adicCompletion K, x ≠ 0 → (cl x = 0 ↔ IsSquare x) := by
    intro x hx
    constructor
    · intro hcl0
      have hi0 : cl x ⟨0, by omega⟩ = 0 := congr_fun hcl0 ⟨0, by omega⟩
      dsimp [cl] at hi0
      rw [if_neg hx] at hi0
      have hdvd : (2 : ℤ) ∣ ord_v x :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd (ord_v x) 2).mp hi0
      obtain ⟨k, hk⟩ := hdvd
      have hφ0 : φ_q (red (unitPart x)) = 0 := by
        ext j
        have hj : cl x ⟨j.val + 1, by omega⟩ = 0 := congr_fun hcl0 ⟨j.val + 1, by omega⟩
        dsimp [cl] at hj
        rw [if_neg hx] at hj
        exact hj
      have hsq_unit : IsSquare (unitPart x) :=
        (hred_sq (unitPart x) (hunitPart_val x hx)).mp ((hφ_sq (red (unitPart x))).mp hφ0)
      rcases hsq_unit with ⟨w, hw⟩
      refine ⟨ϖ ^ k * w, ?_⟩
      calc x = ϖ ^ (ord_v x) * unitPart x := hunitPart_spec x
        _ = ϖ ^ (2 * k) * (w * w) := by rw [hk, hw]
        _ = (ϖ ^ k * ϖ ^ k) * (w * w) := by rw [two_mul, zpow_add₀ hϖ0]
        _ = (ϖ ^ k * w) * (ϖ ^ k * w) := by ring
    · rintro ⟨z, rfl⟩
      have hz : z ≠ 0 := fun h => hx (by rw [h, mul_zero])
      rw [hcl_mul z z hz hz]
      ext i
      exact zmod2_add_self (cl z i)
  have hcl_surj : ∀ c : Fin (2 + kv) → ZMod 2,
      ∃ u : Kˣ, cl (algebraMap K (v.adicCompletion K) (u : K)) = c := by
    intro c
    let c₀ : ZMod 2 := c ⟨0, by omega⟩
    let c' : Fin (1 + kv) → ZMod 2 := fun j => c ⟨j.val + 1, by omega⟩
    obtain ⟨a, ha⟩ := hφ_surj c'
    obtain ⟨r, hr_not_mem, hr_red⟩ := hred_surj a
    have hr_intval : v.intValuation r = 1 :=
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr hr_not_mem
    let r_K : K := algebraMap (NumberField.RingOfIntegers K) K r
    let r_v : v.adicCompletion K := algebraMap K (v.adicCompletion K) r_K
    have hr_v_val : Valued.v r_v = 1 := by
      change Valued.v (algebraMap K (v.adicCompletion K) (algebraMap (NumberField.RingOfIntegers K) K r)) = 1
      rw [hval_int r, hr_intval]
    have hr_v_ne : r_v ≠ 0 := by
      intro h
      rw [h, map_zero] at hr_v_val
      exact zero_ne_one hr_v_val
    have hr_K_ne : r_K ≠ 0 := by
      intro h
      apply hr_v_ne
      change algebraMap K (v.adicCompletion K) r_K = 0
      rw [h, map_zero]
    let u : Kˣ := Units.mk0 (π_K ^ c₀.val * r_K) (mul_ne_zero (pow_ne_zero c₀.val hπ_K0) hr_K_ne)
    refine ⟨u, ?_⟩
    let xu : v.adicCompletion K := algebraMap K (v.adicCompletion K) (u : K)
    have hxu_eq : xu = ϖ ^ (c₀.val : ℤ) * r_v := by
      change algebraMap K (v.adicCompletion K) (π_K ^ c₀.val * r_K) = _
      rw [map_mul, map_pow, zpow_natCast]
    have hxu_val : Valued.v xu = WithZero.exp (-(c₀.val : ℤ)) := by
      rw [hxu_eq, map_mul, hϖ_zpow (c₀.val : ℤ), hr_v_val, mul_one]
    have hxu_ne : xu ≠ 0 := by
      intro h
      rw [h, map_zero] at hxu_val
      exact WithZero.exp_ne_zero hxu_val.symm
    have hxu_ord : ord_v xu = (c₀.val : ℤ) := by
      dsimp [ord_v]
      rw [hxu_val, WithZero.log_exp, neg_neg]
    have hxu_unit : unitPart xu = r_v := by
      dsimp [unitPart]
      rw [hxu_ord, hxu_eq, mul_div_cancel_left₀ r_v (zpow_ne_zero _ hϖ0)]
    ext i
    change cl xu i = c i
    dsimp [cl]
    rw [if_neg hxu_ne]
    split_ifs with hi
    · rw [hxu_ord, Int.cast_natCast, ZMod.natCast_zmod_val]
      have hi_eq : i = ⟨0, by omega⟩ := Fin.ext hi
      rw [hi_eq]
    · rw [hxu_unit, hr_red, ha]
      dsimp [c']
      congr 1
      ext
      dsimp
      omega
  have hcl_surj' := hcl_surj
  choose rep hrep using hcl_surj'
  let r : (Fin (2 + kv) → ZMod 2) → v.adicCompletion K :=
    fun α => algebraMap K (v.adicCompletion K) (rep α : K)
  have hr_ne : ∀ α, r α ≠ 0 := by
    intro α
    change algebraMap K (v.adicCompletion K) (rep α : K) ≠ 0
    rw [ne_eq, map_eq_zero]
    exact (rep α).ne_zero
  let B : (Fin (2 + kv) → ZMod 2) → (Fin (2 + kv) → ZMod 2) → ZMod 2 :=
    fun α β => if hilbLoc v (r α) (r β) = 1 then 0 else 1
  have hilbLoc_symm : ∀ (a b : v.adicCompletion K), hilbLoc v a b = hilbLoc v b a := by
    intro a b
    simp only [hilbLoc]
    congr 1
    exact propext ⟨fun ⟨x, y, hxy⟩ => ⟨y, x, by linear_combination hxy⟩,
      fun ⟨x, y, hxy⟩ => ⟨y, x, by linear_combination hxy⟩⟩
  have hilbLoc_congr_left : ∀ (d q b : v.adicCompletion K),
      d ≠ 0 → q ≠ 0 → IsSquare (d * q) → hilbLoc v d b = hilbLoc v q b := by
    have aux : ∀ (d q b : v.adicCompletion K), d ≠ 0 → q ≠ 0 → IsSquare (d * q) →
        (∃ x y : v.adicCompletion K, d * x ^ 2 + b * y ^ 2 = 1) →
        (∃ x y : v.adicCompletion K, q * x ^ 2 + b * y ^ 2 = 1) := by
      intro d q b hd hq ⟨s, hs⟩ ⟨x, y, hxy⟩
      refine ⟨s * x / q, y, ?_⟩
      have hsq : s ^ 2 = d * q := by linear_combination -hs
      have h1 : q * (s * x / q) ^ 2 = d * x ^ 2 := by
        calc q * (s * x / q) ^ 2 = s ^ 2 * x ^ 2 / q := by
              field_simp [hq]
          _ = (d * q) * x ^ 2 / q := by rw [hsq]
          _ = d * x ^ 2 := by field_simp [hq]
      linear_combination h1 + hxy
    intro d q b hd hq hsq
    have hsq' : IsSquare (q * d) := by rwa [mul_comm]
    simp only [hilbLoc]
    congr 1
    exact propext ⟨aux d q b hd hq hsq, aux q d b hq hd hsq'⟩
  have hilbLoc_congr_right : ∀ (a d q : v.adicCompletion K),
      d ≠ 0 → q ≠ 0 → IsSquare (d * q) → hilbLoc v a d = hilbLoc v a q := by
    intro a d q hd hq hsq
    rw [hilbLoc_symm a d, hilbLoc_symm a q]
    exact hilbLoc_congr_left d q a hd hq hsq
  have hB_rep : ∀ α β : Fin (2 + kv) → ZMod 2,
      hilbLoc v (r α) (r β) = (-1 : ℤˣ) ^ (B α β).val := by
    intro α β
    dsimp [B]
    by_cases h : hilbLoc v (r α) (r β) = 1
    · rw [if_pos h, h]; rfl
    · have hneg : hilbLoc v (r α) (r β) = -1 := by
        dsimp [hilbLoc] at h ⊢
        split_ifs at h ⊢
        · exact absurd rfl h
        · rfl
      rw [if_neg h, hneg]; rfl
  have hsq_mul_rep : ∀ x : v.adicCompletion K, x ≠ 0 → IsSquare (x * r (cl x)) := by
    intro x hx
    rw [← hcl_sq (x * r (cl x)) (mul_ne_zero hx (hr_ne (cl x))),
        hcl_mul x (r (cl x)) hx (hr_ne (cl x)), hrep (cl x)]
    ext i
    exact zmod2_add_self (cl x i)
  have hB_hilb : ∀ x y : v.adicCompletion K, x ≠ 0 → y ≠ 0 →
      hilbLoc v x y = (-1 : ℤˣ) ^ (B (cl x) (cl y)).val := by
    intro x y hx hy
    rw [hilbLoc_congr_left x (r (cl x)) y hx (hr_ne (cl x)) (hsq_mul_rep x hx),
        hilbLoc_congr_right (r (cl x)) y (r (cl y)) hy (hr_ne (cl y)) (hsq_mul_rep y hy)]
    exact hB_rep (cl x) (cl y)
  have zmod2_neg_one_pow_add : ∀ (x y : ZMod 2),
      (-1 : ℤˣ) ^ (x + y).val = (-1 : ℤˣ) ^ x.val * (-1 : ℤˣ) ^ y.val := by
    intro x y
    fin_cases x <;> fin_cases y <;> decide
  have zmod2_eq_of_neg_one_pow_eq : ∀ (x y : ZMod 2),
      (-1 : ℤˣ) ^ x.val = (-1 : ℤˣ) ^ y.val → x = y := by
    intro x y hxy
    fin_cases x <;> fin_cases y
    · rfl
    · exfalso; revert hxy; decide
    · exfalso; revert hxy; decide
    · rfl
  have hB_add : ∀ α₁ α₂ β : Fin (2 + kv) → ZMod 2, B (α₁ + α₂) β = B α₁ β + B α₂ β := by
    intro α₁ α₂ β
    apply zmod2_eq_of_neg_one_pow_eq
    rw [zmod2_neg_one_pow_add, ← hB_rep α₁ β, ← hB_rep α₂ β,
        ← hilbLoc_mul_left v (r α₁) (r α₂) (r β) (hr_ne α₁) (hr_ne α₂) (hr_ne β),
        hB_hilb (r α₁ * r α₂) (r β) (mul_ne_zero (hr_ne α₁) (hr_ne α₂)) (hr_ne β),
        hcl_mul (r α₁) (r α₂) (hr_ne α₁) (hr_ne α₂), hrep α₁, hrep α₂, hrep β]
  have hB_symm : ∀ α β : Fin (2 + kv) → ZMod 2, B α β = B β α := by
    intro α β
    dsimp [B]
    rw [hilbLoc_symm (r α) (r β)]
  have hB_nondeg : ∀ α : Fin (2 + kv) → ZMod 2,
      (∀ β : Fin (2 + kv) → ZMod 2, B α β = 0) → α = 0 := by
    intro α hα
    have horth : ∀ y : v.adicCompletion K, y ≠ 0 → hilbLoc v (r α) y = 1 := by
      intro y hy
      rw [hB_hilb (r α) y (hr_ne α) hy, hrep α, hα (cl y)]
      rfl
    have hsq : IsSquare (r α) := hilbLoc_nondeg v (r α) (hr_ne α) horth
    rw [← hrep α]
    exact (hcl_sq (r α) (hr_ne α)).mpr hsq
  exact ⟨cl, B, hcl_mul, hcl_sq, hcl_surj, hB_add, hB_symm, hB_nondeg, hB_hilb⟩

theorem isDescentClass_one_and_congr_and_mul {F : Type u} [Field F] (e₁ e₂ e₃ : F)
    (he₁₂ : e₁ ≠ e₂) (he₁₃ : e₁ ≠ e₃) (he₂₃ : e₂ ≠ e₃) :
    IsDescentClass e₁ e₂ e₃ 1 1 ∧
    (∀ d₁ d₂ c₁ c₂ : F, d₁ ≠ 0 → d₂ ≠ 0 → c₁ ≠ 0 → c₂ ≠ 0 →
      IsSquare (d₁ * c₁) → IsSquare (d₂ * c₂) →
      IsDescentClass e₁ e₂ e₃ d₁ d₂ → IsDescentClass e₁ e₂ e₃ c₁ c₂) ∧
    (∀ d₁ d₂ c₁ c₂ : F, d₁ ≠ 0 → d₂ ≠ 0 → c₁ ≠ 0 → c₂ ≠ 0 →
      IsDescentClass e₁ e₂ e₃ d₁ d₂ → IsDescentClass e₁ e₂ e₃ c₁ c₂ →
      IsDescentClass e₁ e₂ e₃ (d₁ * c₁) (d₂ * c₂)) :=
by
  have isDescentClass_of_isSquare : ∀ (d₁ d₂ : F),
      IsSquare d₁ → IsSquare d₂ → IsDescentClass e₁ e₂ e₃ d₁ d₂ := by
    rintro d₁ d₂ ⟨s₁, rfl⟩ ⟨s₂, rfl⟩
    refine ⟨0, s₂, s₁, 1, ?_, by ring, by ring⟩
    intro h
    exact one_ne_zero h.2.2.2
  have h_one : IsDescentClass e₁ e₂ e₃ 1 1 :=
    isDescentClass_of_isSquare 1 1 IsSquare.one IsSquare.one
  have h_congr : ∀ d₁ d₂ c₁ c₂ : F, d₁ ≠ 0 → d₂ ≠ 0 → c₁ ≠ 0 → c₂ ≠ 0 →
      IsSquare (d₁ * c₁) → IsSquare (d₂ * c₂) →
      IsDescentClass e₁ e₂ e₃ d₁ d₂ → IsDescentClass e₁ e₂ e₃ c₁ c₂ := by
    rintro d₁ d₂ c₁ c₂ hd₁ hd₂ hc₁ hc₂ ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩ ⟨z₀, z₁, z₂, z₃, hz_ne, hz1, hz2⟩
    have hs₁_ne : s₁ ≠ 0 := fun h => mul_ne_zero hd₁ hc₁ (by rw [hs₁, h, mul_zero])
    have hs₂_ne : s₂ ≠ 0 := fun h => mul_ne_zero hd₂ hc₂ (by rw [hs₂, h, mul_zero])
    refine ⟨s₁ * s₂ * z₀, d₁ * s₂ * z₁, d₂ * s₁ * z₂, d₁ * d₂ * z₃, ?_, ?_, ?_⟩
    · rintro ⟨h0, h1, h2, h3⟩
      apply hz_ne
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero hs₁_ne hs₂_ne)
      · exact (mul_eq_zero.mp h1).resolve_left (mul_ne_zero hd₁ hs₂_ne)
      · exact (mul_eq_zero.mp h2).resolve_left (mul_ne_zero hd₂ hs₁_ne)
      · exact (mul_eq_zero.mp h3).resolve_left (mul_ne_zero hd₁ hd₂)
    · linear_combination s₁ ^ 2 * s₂ ^ 2 * hz1 + d₁ * s₂ ^ 2 * z₁ ^ 2 * hs₁ - d₂ * s₁ ^ 2 * z₂ ^ 2 * hs₂
    · linear_combination s₁ ^ 2 * s₂ ^ 2 * hz2 +
        (d₁ * s₂ ^ 2 * z₁ ^ 2 - d₁ * d₂ * s₂ ^ 2 * z₃ ^ 2) * hs₁ -
        d₁ ^ 2 * d₂ * c₁ * z₃ ^ 2 * hs₂
  have isSquare_of_z0_eq_zero : ∀ {d₁ d₂ z₁ z₂ z₃ : F},
      d₁ ≠ 0 → d₂ ≠ 0 →
      ¬ ((0 : F) = 0 ∧ z₁ = 0 ∧ z₂ = 0 ∧ z₃ = 0) →
      d₁ * z₁ ^ 2 - d₂ * z₂ ^ 2 = (e₂ - e₁) * 0 ^ 2 →
      d₁ * z₁ ^ 2 - d₁ * d₂ * z₃ ^ 2 = (e₃ - e₁) * 0 ^ 2 →
      IsSquare d₁ ∧ IsSquare d₂ := by
    intro d₁ d₂ z₁ z₂ z₃ hd₁ hd₂ hne hz1 hz2
    have hz3 : z₃ ≠ 0 := by
      intro h3
      have h1 : d₁ * z₁ ^ 2 = 0 := by linear_combination hz2 + d₁ * d₂ * z₃ * h3
      have h2 : d₂ * z₂ ^ 2 = 0 := by linear_combination h1 - hz1
      have hz1_0 : z₁ = 0 := by
        cases mul_eq_zero.mp h1 with
        | inl h => exact absurd h hd₁
        | inr h => exact pow_eq_zero h
      have hz2_0 : z₂ = 0 := by
        cases mul_eq_zero.mp h2 with
        | inl h => exact absurd h hd₂
        | inr h => exact pow_eq_zero h
      exact hne ⟨rfl, hz1_0, hz2_0, h3⟩
    have hd1_eq : d₂ * (d₁ * z₃ ^ 2 - z₂ ^ 2) = 0 := by linear_combination hz1 - hz2
    have hd1_sq : d₁ * z₃ ^ 2 = z₂ ^ 2 := by
      cases mul_eq_zero.mp hd1_eq with
      | inl h => exact absurd h hd₂
      | inr h => linear_combination h
    have hd2_eq : d₁ * (d₂ * z₃ ^ 2 - z₁ ^ 2) = 0 := by linear_combination -hz2
    have hd2_sq : d₂ * z₃ ^ 2 = z₁ ^ 2 := by
      cases mul_eq_zero.mp hd2_eq with
      | inl h => exact absurd h hd₁
      | inr h => linear_combination h
    constructor
    · refine ⟨z₂ / z₃, ?_⟩
      calc d₁ = d₁ * z₃ ^ 2 / z₃ ^ 2 := by field_simp [hz3]
        _ = z₂ ^ 2 / z₃ ^ 2 := by rw [hd1_sq]
        _ = (z₂ / z₃) * (z₂ / z₃) := by ring
    · refine ⟨z₁ / z₃, ?_⟩
      calc d₂ = d₂ * z₃ ^ 2 / z₃ ^ 2 := by field_simp [hz3]
        _ = z₁ ^ 2 / z₃ ^ 2 := by rw [hd2_sq]
        _ = (z₁ / z₃) * (z₁ / z₃) := by ring
  have isDescentClass_mul_of_isSquare_left : ∀ (d₁ d₂ c₁ c₂ : F),
      d₁ ≠ 0 → d₂ ≠ 0 → IsSquare d₁ → IsSquare d₂ →
      IsDescentClass e₁ e₂ e₃ c₁ c₂ →
      IsDescentClass e₁ e₂ e₃ (d₁ * c₁) (d₂ * c₂) := by
    rintro d₁ d₂ c₁ c₂ hd₁ hd₂ ⟨s₁, rfl⟩ ⟨s₂, rfl⟩ ⟨w₀, w₁, w₂, w₃, hw_ne, hw1, hw2⟩
    have hs₁ : s₁ ≠ 0 := fun h => hd₁ (by simp [h])
    have hs₂ : s₂ ≠ 0 := fun h => hd₂ (by simp [h])
    refine ⟨w₀, w₁ / s₁, w₂ / s₂, w₃ / (s₁ * s₂), ?_, ?_, ?_⟩
    · intro ⟨h0, h1, h2, h3⟩
      apply hw_ne
      refine ⟨h0, ?_, ?_, ?_⟩
      · exact (div_eq_zero_iff.mp h1).resolve_right hs₁
      · exact (div_eq_zero_iff.mp h2).resolve_right hs₂
      · exact (div_eq_zero_iff.mp h3).resolve_right (mul_ne_zero hs₁ hs₂)
    · have h1 : s₁ * s₁ * c₁ * (w₁ / s₁) ^ 2 = c₁ * w₁ ^ 2 := by field_simp [hs₁]
      have h2 : s₂ * s₂ * c₂ * (w₂ / s₂) ^ 2 = c₂ * w₂ ^ 2 := by field_simp [hs₂]
      linear_combination h1 - h2 + hw1
    · have h1 : s₁ * s₁ * c₁ * (w₁ / s₁) ^ 2 = c₁ * w₁ ^ 2 := by field_simp [hs₁]
      have h3 : s₁ * s₁ * c₁ * (s₂ * s₂ * c₂) * (w₃ / (s₁ * s₂)) ^ 2 = c₁ * c₂ * w₃ ^ 2 := by
        field_simp [hs₁, hs₂]
      linear_combination h1 - h3 + hw2
  have h_mul : ∀ d₁ d₂ c₁ c₂ : F, d₁ ≠ 0 → d₂ ≠ 0 → c₁ ≠ 0 → c₂ ≠ 0 →
      IsDescentClass e₁ e₂ e₃ d₁ d₂ → IsDescentClass e₁ e₂ e₃ c₁ c₂ →
      IsDescentClass e₁ e₂ e₃ (d₁ * c₁) (d₂ * c₂) := by
    intro d₁ d₂ c₁ c₂ hd₁ hd₂ hc₁ hc₂ hd hc
    rcases hd with ⟨z₀, z₁, z₂, z₃, hz_ne, hz1, hz2⟩
    by_cases hz0 : z₀ = 0
    · subst hz0
      obtain ⟨hsq1, hsq2⟩ := isSquare_of_z0_eq_zero hd₁ hd₂ hz_ne hz1 hz2
      exact isDescentClass_mul_of_isSquare_left d₁ d₂ c₁ c₂ hd₁ hd₂ hsq1 hsq2 hc
    rcases hc with ⟨w₀, w₁, w₂, w₃, hw_ne, hw1, hw2⟩
    by_cases hw0 : w₀ = 0
    · subst hw0
      obtain ⟨hsq1, hsq2⟩ := isSquare_of_z0_eq_zero hc₁ hc₂ hw_ne hw1 hw2
      rw [mul_comm d₁ c₁, mul_comm d₂ c₂]
      exact isDescentClass_mul_of_isSquare_left c₁ c₂ d₁ d₂ hc₁ hc₂ hsq1 hsq2
        ⟨z₀, z₁, z₂, z₃, hz_ne, hz1, hz2⟩
    let u₀ : F := d₁ * z₁ ^ 2 * w₀ ^ 2 - c₁ * w₁ ^ 2 * z₀ ^ 2
    let u₁ : F := d₂ * z₂ * z₃ * w₁ * w₀ - c₂ * w₂ * w₃ * z₁ * z₀
    let u₂ : F := d₁ * z₁ * z₃ * w₂ * w₀ - c₁ * w₁ * w₃ * z₂ * z₀
    let u₃ : F := z₁ * z₂ * w₃ * w₀ - w₁ * w₂ * z₃ * z₀
    have hA2 : d₂ * z₂ ^ 2 * w₀ ^ 2 - c₂ * w₂ ^ 2 * z₀ ^ 2 = u₀ := by
      dsimp [u₀]; linear_combination -w₀ ^ 2 * hz1 + z₀ ^ 2 * hw1
    have hA3 : d₁ * d₂ * z₃ ^ 2 * w₀ ^ 2 - c₁ * c₂ * w₃ ^ 2 * z₀ ^ 2 = u₀ := by
      dsimp [u₀]; linear_combination -w₀ ^ 2 * hz2 + z₀ ^ 2 * hw2
    have hB2 : d₂ * z₂ ^ 2 * (c₁ * w₁ ^ 2) - d₁ * z₁ ^ 2 * (c₂ * w₂ ^ 2) = (e₂ - e₁) * u₀ := by
      dsimp [u₀]; linear_combination -c₁ * w₁ ^ 2 * hz1 + d₁ * z₁ ^ 2 * hw1
    have hB3 : d₁ * d₂ * z₃ ^ 2 * (c₁ * w₁ ^ 2) - d₁ * z₁ ^ 2 * (c₁ * c₂ * w₃ ^ 2) = (e₃ - e₁) * u₀ := by
      dsimp [u₀]; linear_combination -c₁ * w₁ ^ 2 * hz2 + d₁ * z₁ ^ 2 * hw2
    by_cases hu0 : u₀ ≠ 0
    · refine ⟨u₀, u₁, u₂, u₃, fun h => hu0 h.1, ?_, ?_⟩
      · calc (d₁ * c₁) * u₁ ^ 2 - (d₂ * c₂) * u₂ ^ 2
          _ = (d₁ * d₂ * z₃ ^ 2 * w₀ ^ 2 - c₁ * c₂ * w₃ ^ 2 * z₀ ^ 2) *
              (d₂ * z₂ ^ 2 * (c₁ * w₁ ^ 2) - d₁ * z₁ ^ 2 * (c₂ * w₂ ^ 2)) := by
            dsimp [u₁, u₂]; ring
          _ = u₀ * ((e₂ - e₁) * u₀) := by rw [hA3, hB2]
          _ = (e₂ - e₁) * u₀ ^ 2 := by ring
      · calc (d₁ * c₁) * u₁ ^ 2 - (d₁ * c₁) * (d₂ * c₂) * u₃ ^ 2
          _ = (d₂ * z₂ ^ 2 * w₀ ^ 2 - c₂ * w₂ ^ 2 * z₀ ^ 2) *
              (d₁ * d₂ * z₃ ^ 2 * (c₁ * w₁ ^ 2) - d₁ * z₁ ^ 2 * (c₁ * c₂ * w₃ ^ 2)) := by
            dsimp [u₁, u₃]; ring
          _ = u₀ * ((e₃ - e₁) * u₀) := by rw [hA2, hB3]
          _ = (e₃ - e₁) * u₀ ^ 2 := by ring
    · push_neg at hu0
      have hsq_from_eq : ∀ (D C Z W : F), Z ≠ 0 → D * Z ^ 2 * w₀ ^ 2 - C * W ^ 2 * z₀ ^ 2 = 0 →
          IsSquare (D * C) := by
        intro D C Z W hZ heq
        have hZW : Z * w₀ ≠ 0 := mul_ne_zero hZ hw0
        have h1 : D * C * (Z * w₀) ^ 2 = (C * W * z₀) ^ 2 := by
          linear_combination C * heq
        refine ⟨C * W * z₀ / (Z * w₀), ?_⟩
        calc D * C = D * C * (Z * w₀) ^ 2 / (Z * w₀) ^ 2 := by field_simp [hZW]
          _ = (C * W * z₀) ^ 2 / (Z * w₀) ^ 2 := by rw [h1]
          _ = (C * W * z₀ / (Z * w₀)) * (C * W * z₀ / (Z * w₀)) := by ring
      have h1_eq : d₁ * z₁ ^ 2 * w₀ ^ 2 - c₁ * w₁ ^ 2 * z₀ ^ 2 = 0 := hu0
      have h2_eq : d₂ * z₂ ^ 2 * w₀ ^ 2 - c₂ * w₂ ^ 2 * z₀ ^ 2 = 0 := by rw [hA2, hu0]
      have h3_eq : (d₁ * d₂) * z₃ ^ 2 * w₀ ^ 2 - (c₁ * c₂) * w₃ ^ 2 * z₀ ^ 2 = 0 := by
        rw [hA3, hu0]
      have h_not_z12 : ¬ (z₁ = 0 ∧ z₂ = 0) := by
        rintro ⟨h1, h2⟩
        have he : (e₂ - e₁) * z₀ ^ 2 = 0 := by linear_combination -hz1 + d₁ * z₁ * h1 - d₂ * z₂ * h2
        exact mul_ne_zero (sub_ne_zero.mpr he₁₂.symm) (pow_ne_zero 2 hz0) he
      have h_not_z13 : ¬ (z₁ = 0 ∧ z₃ = 0) := by
        rintro ⟨h1, h3⟩
        have he : (e₃ - e₁) * z₀ ^ 2 = 0 := by linear_combination -hz2 + d₁ * z₁ * h1 - d₁ * d₂ * z₃ * h3
        exact mul_ne_zero (sub_ne_zero.mpr he₁₃.symm) (pow_ne_zero 2 hz0) he
      have h_not_z23 : ¬ (z₂ = 0 ∧ z₃ = 0) := by
        rintro ⟨h2, h3⟩
        have he : (e₃ - e₂) * z₀ ^ 2 = 0 := by linear_combination hz1 - hz2 + d₂ * z₂ * h2 - d₁ * d₂ * z₃ * h3
        exact mul_ne_zero (sub_ne_zero.mpr he₂₃.symm) (pow_ne_zero 2 hz0) he
      have hsq_div : ∀ (A B : F), A ≠ 0 → IsSquare A → IsSquare (A * B) → IsSquare B := by
        rintro A B hA ⟨r₁, rfl⟩ ⟨r₂, hr₂⟩
        have hr₁ : r₁ ≠ 0 := fun h => hA (by simp [h])
        refine ⟨r₂ / r₁, ?_⟩
        have h1 : r₁ ^ 2 * B = r₂ ^ 2 := by linear_combination hr₂
        calc B = r₁ ^ 2 * B / r₁ ^ 2 := by field_simp [hr₁]
          _ = r₂ ^ 2 / r₁ ^ 2 := by rw [h1]
          _ = (r₂ / r₁) * (r₂ / r₁) := by ring
      by_cases hz1_ne : z₁ ≠ 0
      · have hsq1 : IsSquare (d₁ * c₁) := hsq_from_eq d₁ c₁ z₁ w₁ hz1_ne h1_eq
        by_cases hz2_ne : z₂ ≠ 0
        · have hsq2 : IsSquare (d₂ * c₂) := hsq_from_eq d₂ c₂ z₂ w₂ hz2_ne h2_eq
          exact isDescentClass_of_isSquare (d₁ * c₁) (d₂ * c₂) hsq1 hsq2
        · push_neg at hz2_ne
          have hz3_ne : z₃ ≠ 0 := fun h3 => h_not_z23 ⟨hz2_ne, h3⟩
          have hsq3 : IsSquare ((d₁ * d₂) * (c₁ * c₂)) := hsq_from_eq (d₁ * d₂) (c₁ * c₂) z₃ w₃ hz3_ne h3_eq
          have hsq3' : IsSquare ((d₁ * c₁) * (d₂ * c₂)) := by
            convert hsq3 using 1; ring
          have hsq2 : IsSquare (d₂ * c₂) := hsq_div (d₁ * c₁) (d₂ * c₂) (mul_ne_zero hd₁ hc₁) hsq1 hsq3'
          exact isDescentClass_of_isSquare (d₁ * c₁) (d₂ * c₂) hsq1 hsq2
      · push_neg at hz1_ne
        have hz2_ne : z₂ ≠ 0 := fun h2 => h_not_z12 ⟨hz1_ne, h2⟩
        have hz3_ne : z₃ ≠ 0 := fun h3 => h_not_z13 ⟨hz1_ne, h3⟩
        have hsq2 : IsSquare (d₂ * c₂) := hsq_from_eq d₂ c₂ z₂ w₂ hz2_ne h2_eq
        have hsq3 : IsSquare ((d₁ * d₂) * (c₁ * c₂)) := hsq_from_eq (d₁ * d₂) (c₁ * c₂) z₃ w₃ hz3_ne h3_eq
        have hsq3' : IsSquare ((d₂ * c₂) * (d₁ * c₁)) := by
          convert hsq3 using 1; ring
        have hsq1 : IsSquare (d₁ * c₁) := hsq_div (d₂ * c₂) (d₁ * c₁) (mul_ne_zero hd₂ hc₂) hsq2 hsq3'
        exact isDescentClass_of_isSquare (d₁ * c₁) (d₂ * c₂) hsq1 hsq2
  exact ⟨h_one, h_congr, h_mul⟩

theorem threeRootsCurve_kummer_inj_mod_two {F : Type u} [Field F] [DecidableEq F]
    (hchar : (2 : F) ≠ 0) (e₁ e₂ e₃ : F)
    (he₁₂ : e₁ ≠ e₂) (he₁₃ : e₁ ≠ e₃) (he₂₃ : e₂ ≠ e₃)
    (d : ℕ) (cl : F → (Fin d → ZMod 2))
    (hcl_mul : ∀ x y : F, x ≠ 0 → y ≠ 0 → cl (x * y) = cl x + cl y)
    (hcl_sq : ∀ x : F, x ≠ 0 → (cl x = 0 ↔ IsSquare x)) :
    ∃ δ : (threeRootsCurve e₁ e₂ e₃).toAffine.Point → (Fin d → ZMod 2) × (Fin d → ZMod 2),
      (∀ P : (threeRootsCurve e₁ e₂ e₃).toAffine.Point,
        ∃ x₁ x₂ : F, x₁ ≠ 0 ∧ x₂ ≠ 0 ∧ cl x₁ = (δ P).1 ∧ cl x₂ = (δ P).2 ∧
          IsDescentClass e₁ e₂ e₃ x₁ x₂) ∧
      (∀ P Q : (threeRootsCurve e₁ e₂ e₃).toAffine.Point,
        δ P = δ Q → ∃ R : (threeRootsCurve e₁ e₂ e₃).toAffine.Point, R + R = P - Q) :=
by
  have kummer_coord_ne_zero_and_isDescentClass_and_prod_isSquare :
      ∀ (e₁ e₂ e₃ x y : F) (he₁₂ : e₁ ≠ e₂) (he₁₃ : e₁ ≠ e₃) (he₂₃ : e₂ ≠ e₃)
        (heq : y ^ 2 = (x - e₁) * (x - e₂) * (x - e₃)),
        (if x = e₁ then (e₁ - e₂) * (e₁ - e₃) else x - e₁) ≠ 0 ∧
        (if x = e₂ then (e₂ - e₁) * (e₂ - e₃) else x - e₂) ≠ 0 ∧
        (if x = e₃ then (e₃ - e₁) * (e₃ - e₂) else x - e₃) ≠ 0 ∧
        IsDescentClass e₁ e₂ e₃
          (if x = e₁ then (e₁ - e₂) * (e₁ - e₃) else x - e₁)
          (if x = e₂ then (e₂ - e₁) * (e₂ - e₃) else x - e₂) ∧
        IsSquare
          ((if x = e₁ then (e₁ - e₂) * (e₁ - e₃) else x - e₁) *
           (if x = e₂ then (e₂ - e₁) * (e₂ - e₃) else x - e₂) *
           (if x = e₃ then (e₃ - e₁) * (e₃ - e₂) else x - e₃)) := by
    intro e₁ e₂ e₃ x y he₁₂ he₁₃ he₂₃ heq
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · split_ifs with h
      · exact mul_ne_zero (sub_ne_zero.mpr he₁₂) (sub_ne_zero.mpr he₁₃)
      · exact sub_ne_zero.mpr h
    · split_ifs with h
      · exact mul_ne_zero (sub_ne_zero.mpr he₁₂.symm) (sub_ne_zero.mpr he₂₃)
      · exact sub_ne_zero.mpr h
    · split_ifs with h
      · exact mul_ne_zero (sub_ne_zero.mpr he₁₃.symm) (sub_ne_zero.mpr he₂₃.symm)
      · exact sub_ne_zero.mpr h
    · by_cases hx₁ : x = e₁
      · have hx₂ : x ≠ e₂ := by rintro rfl; exact he₁₂ hx₁.symm
        rw [if_pos hx₁, if_neg hx₂, hx₁]
        refine ⟨1, 0, 1, (e₁ - e₂)⁻¹, by simp, by ring, ?_⟩
        have h12 : e₁ - e₂ ≠ 0 := sub_ne_zero.mpr he₁₂
        field_simp [h12]
        ring
      · by_cases hx₂ : x = e₂
        · rw [if_neg hx₁, if_pos hx₂, hx₂]
          refine ⟨1, 1, 0, (e₂ - e₁)⁻¹, by simp, by ring, ?_⟩
          have h21 : e₂ - e₁ ≠ 0 := sub_ne_zero.mpr he₁₂.symm
          field_simp [h21]
          ring
        · rw [if_neg hx₁, if_neg hx₂]
          refine ⟨1, 1, 1, y / ((x - e₁) * (x - e₂)), by simp, by ring, ?_⟩
          have h1 : x - e₁ ≠ 0 := sub_ne_zero.mpr hx₁
          have h2 : x - e₂ ≠ 0 := sub_ne_zero.mpr hx₂
          field_simp [h1, h2]
          linear_combination -heq
    · by_cases hx₁ : x = e₁
      · have hx₂ : x ≠ e₂ := by rintro rfl; exact he₁₂ hx₁.symm
        have hx₃ : x ≠ e₃ := by rintro rfl; exact he₁₃ hx₁.symm
        rw [if_pos hx₁, if_neg hx₂, if_neg hx₃, hx₁]
        exact ⟨(e₁ - e₂) * (e₁ - e₃), by ring⟩
      · by_cases hx₂ : x = e₂
        · have hx₃ : x ≠ e₃ := by rintro rfl; exact he₂₃ hx₂.symm
          rw [if_neg hx₁, if_pos hx₂, if_neg hx₃, hx₂]
          exact ⟨(e₂ - e₁) * (e₂ - e₃), by ring⟩
        · by_cases hx₃ : x = e₃
          · rw [if_neg hx₁, if_neg hx₂, if_pos hx₃, hx₃]
            exact ⟨(e₃ - e₁) * (e₃ - e₂), by ring⟩
          · rw [if_neg hx₁, if_neg hx₂, if_neg hx₃]
            exact ⟨y, by linear_combination -heq⟩
  have single_root_chord_isSquare :
      ∀ (e₁ e₂ e₃ x₁ y₁ x₂ y₂ : F) (he₁₂ : e₁ ≠ e₂) (he₁₃ : e₁ ≠ e₃) (hx : x₁ ≠ x₂)
        (h₁ : y₁ ^ 2 = (x₁ - e₁) * (x₁ - e₂) * (x₁ - e₃))
        (h₂ : y₂ ^ 2 = (x₂ - e₁) * (x₂ - e₂) * (x₂ - e₃))
        (hsq : IsSquare
          ((if x₁ = e₁ then (e₁ - e₂) * (e₁ - e₃) else x₁ - e₁) *
           (if x₂ = e₁ then (e₁ - e₂) * (e₁ - e₃) else x₂ - e₁))),
        IsSquare (((y₁ + y₂) / (x₁ - x₂)) ^ 2 + (e₁ + e₂ + e₃) - x₁ - x₂ - e₁) := by
    intro e₁ e₂ e₃ x₁ y₁ x₂ y₂ he₁₂ he₁₃ hx h₁ h₂ ⟨s, hs⟩
    have hx12 : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    by_cases hx₁ : x₁ = e₁
    · have hx₂ : x₂ ≠ e₁ := by rintro rfl; exact hx hx₁
      rw [if_pos hx₁, if_neg hx₂] at hs
      subst hx₁
      have hy₁ : y₁ = 0 := by
        apply eq_zero_of_pow_eq_zero (n := 2)
        linear_combination h₁
      subst hy₁
      refine ⟨s / (x₁ - x₂), ?_⟩
      field_simp [hx12]
      linear_combination h₂ + hs
    · by_cases hx₂ : x₂ = e₁
      · rw [if_neg hx₁, if_pos hx₂] at hs
        subst hx₂
        have hy₂ : y₂ = 0 := by
          apply eq_zero_of_pow_eq_zero (n := 2)
          linear_combination h₂
        subst hy₂
        refine ⟨s / (x₁ - x₂), ?_⟩
        field_simp [hx12]
        linear_combination h₁ + hs
      · rw [if_neg hx₁, if_neg hx₂] at hs
        have hx₁e₁ : x₁ - e₁ ≠ 0 := sub_ne_zero.mpr hx₁
        have hx₂e₁ : x₂ - e₁ ≠ 0 := sub_ne_zero.mpr hx₂
        have hs_ne : s ≠ 0 := by
          rintro rfl
          exact mul_ne_zero hx₁e₁ hx₂e₁ (by linear_combination hs)
        have h_chord : s * s * ((y₁ + y₂) ^ 2 + (e₁ + e₂ + e₃ - x₁ - x₂ - e₁) * (x₁ - x₂) ^ 2) =
            (y₁ * (x₂ - e₁) + y₂ * (x₁ - e₁)) ^ 2 := by
          rw [← hs]
          linear_combination (x₂ - e₁) * (x₁ - x₂) * h₁ - (x₁ - e₁) * (x₁ - x₂) * h₂
        refine ⟨(y₁ * (x₂ - e₁) + y₂ * (x₁ - e₁)) / (s * (x₁ - x₂)), ?_⟩
        field_simp [hx12, hs_ne]
        linear_combination h_chord
  have knapp_halving_of_isSquare_sub_roots :
      ∀ {x y : F} (hS : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x y),
        IsSquare (x - e₁) → IsSquare (x - e₂) → IsSquare (x - e₃) →
        ∃ R : (threeRootsCurve e₁ e₂ e₃).toAffine.Point,
          R + R = WeierstrassCurve.Affine.Point.some hS := by
    intro x y hS ⟨v₁, hv₁⟩ ⟨v₂, hv₂⟩ ⟨v₃, hv₃⟩
    let W := (threeRootsCurve e₁ e₂ e₃).toAffine
    have heq : y ^ 2 = (x - e₁) * (x - e₂) * (x - e₃) := by
      have hW := (WeierstrassCurve.Affine.equation_iff x y).mp hS.1
      dsimp [W, threeRootsCurve] at hW
      linear_combination hW
    have h_exists_u : ∃ u₁ u₂ u₃ : F,
        u₁ ^ 2 = x - e₁ ∧ u₂ ^ 2 = x - e₂ ∧ u₃ ^ 2 = x - e₃ ∧ u₁ * u₂ * u₃ = y := by
      have hy_sq : y ^ 2 = (v₁ * v₂ * v₃) ^ 2 := by
        calc y ^ 2 = (x - e₁) * (x - e₂) * (x - e₃) := heq
          _ = (v₁ * v₁) * (v₂ * v₂) * (v₃ * v₃) := by rw [hv₁, hv₂, hv₃]
          _ = (v₁ * v₂ * v₃) ^ 2 := by ring
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy_sq with hy | hy
      · exact ⟨v₁, v₂, v₃, by linear_combination -hv₁, by linear_combination -hv₂,
          by linear_combination -hv₃, hy.symm⟩
      · refine ⟨-v₁, v₂, v₃, by linear_combination -hv₁, by linear_combination -hv₂,
          by linear_combination -hv₃, ?_⟩
        linear_combination -hy
    rcases h_exists_u with ⟨u₁, u₂, u₃, hu₁, hu₂, hu₃, hy⟩
    let x₀ : F := x + u₁ * u₂ + u₁ * u₃ + u₂ * u₃
    let y₀ : F := (u₁ + u₂) * (u₁ + u₃) * (u₂ + u₃)
    have hx₀₁ : x₀ - e₁ = (u₁ + u₂) * (u₁ + u₃) := by
      dsimp [x₀]
      linear_combination -hu₁
    have hx₀₂ : x₀ - e₂ = (u₁ + u₂) * (u₂ + u₃) := by
      dsimp [x₀]
      linear_combination -hu₂
    have hx₀₃ : x₀ - e₃ = (u₁ + u₃) * (u₂ + u₃) := by
      dsimp [x₀]
      linear_combination -hu₃
    have hu12 : u₁ + u₂ ≠ 0 := by
      intro h0
      apply sub_ne_zero.mpr he₁₂.symm
      linear_combination -hu₁ + hu₂ + (u₁ - u₂) * h0
    have hu13 : u₁ + u₃ ≠ 0 := by
      intro h0
      apply sub_ne_zero.mpr he₁₃.symm
      linear_combination -hu₁ + hu₃ + (u₁ - u₃) * h0
    have hu23 : u₂ + u₃ ≠ 0 := by
      intro h0
      apply sub_ne_zero.mpr he₂₃.symm
      linear_combination -hu₂ + hu₃ + (u₂ - u₃) * h0
    have hy₀_ne : y₀ ≠ 0 := mul_ne_zero (mul_ne_zero hu12 hu13) hu23
    have hy₀_negY : y₀ ≠ W.negY x₀ y₀ := by
      intro h0
      have h2y₀ : (2 : F) * y₀ = 0 := by
        dsimp [W, threeRootsCurve, WeierstrassCurve.Affine.negY] at h0
        linear_combination h0
      exact mul_ne_zero hchar hy₀_ne h2y₀
    have hR_eq : W.Equation x₀ y₀ := by
      rw [WeierstrassCurve.Affine.equation_iff]
      have h_prod : y₀ ^ 2 = (x₀ - e₁) * (x₀ - e₂) * (x₀ - e₃) := by
        rw [hx₀₁, hx₀₂, hx₀₃]
        dsimp [y₀]
        ring
      dsimp [W, threeRootsCurve]
      linear_combination h_prod
    have hR : W.Nonsingular x₀ y₀ := by
      rw [WeierstrassCurve.Affine.nonsingular_iff]
      refine ⟨hR_eq, Or.inr ?_⟩
      dsimp [W, threeRootsCurve, WeierstrassCurve.Affine.negY] at hy₀_negY ⊢
      exact hy₀_negY
    refine ⟨WeierstrassCurve.Affine.Point.some hR, ?_⟩
    rw [WeierstrassCurve.Affine.Point.add_of_Y_ne hy₀_negY,
        WeierstrassCurve.Affine.Point.some.injEq]
    have hslope : W.slope x₀ x₀ y₀ y₀ = u₁ + u₂ + u₃ := by
      rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy₀_negY,
          div_eq_iff (sub_ne_zero.mpr hy₀_negY)]
      have h_num : 3 * x₀ ^ 2 + 2 * -(e₁ + e₂ + e₃) * x₀ + (e₁ * e₂ + e₁ * e₃ + e₂ * e₃) - 0 * y₀ =
          (x₀ - e₁) * (x₀ - e₂) + (x₀ - e₁) * (x₀ - e₃) + (x₀ - e₂) * (x₀ - e₃) := by ring
      dsimp [W, threeRootsCurve, WeierstrassCurve.Affine.negY]
      rw [h_num, hx₀₁, hx₀₂, hx₀₃]
      dsimp [y₀]
      ring
    rw [hslope]
    constructor
    · dsimp [W, threeRootsCurve, WeierstrassCurve.Affine.addX, x₀]
      linear_combination hu₁ + hu₂ + hu₃
    · dsimp [W, threeRootsCurve, WeierstrassCurve.Affine.addY,
             WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
             WeierstrassCurve.Affine.addX, x₀, y₀]
      linear_combination hy - (u₁ + u₂ + u₃) * (hu₁ + hu₂ + hu₃)
  let W := (threeRootsCurve e₁ e₂ e₃).toAffine
  let μ : F → F → F → F → F := fun ea eb ec x =>
    if x = ea then (ea - eb) * (ea - ec) else x - ea
  let κ₁ : W.Point → F := fun P =>
    WeierstrassCurve.Affine.Point.casesOn P 1 (fun {x _} _ => μ e₁ e₂ e₃ x)
  let κ₂ : W.Point → F := fun P =>
    WeierstrassCurve.Affine.Point.casesOn P 1 (fun {x _} _ => μ e₂ e₁ e₃ x)
  let δ : W.Point → (Fin d → ZMod 2) × (Fin d → ZMod 2) :=
    fun P => (cl (κ₁ P), cl (κ₂ P))
  have heq_of_nonsingular : ∀ {x y : F}, W.Nonsingular x y →
      y ^ 2 = (x - e₁) * (x - e₂) * (x - e₃) := by
    intro x y h
    have hW := (WeierstrassCurve.Affine.equation_iff x y).mp h.1
    dsimp [W, threeRootsCurve] at hW
    linear_combination hW
  have zmod2_fun_add_self : ∀ (z : Fin d → ZMod 2), z + z = 0 := by
    intro z
    ext i
    change z i + z i = 0
    have h_self : ∀ a : ZMod 2, a + a = 0 := by decide
    exact h_self (z i)
  have isSquare_mul_of_cl_eq : ∀ {a b : F}, a ≠ 0 → b ≠ 0 → cl a = cl b → IsSquare (a * b) := by
    intro a b ha hb hab
    rw [← hcl_sq (a * b) (mul_ne_zero ha hb), hcl_mul a b ha hb, hab]
    exact zmod2_fun_add_self (cl b)
  have isSquare_of_isSquare_mul_three : ∀ {a b c : F},
      a ≠ 0 → b ≠ 0 → IsSquare a → IsSquare b → IsSquare (a * b * c) → IsSquare c := by
    rintro a b c ha hb ⟨r, rfl⟩ ⟨s, rfl⟩ ⟨t, ht⟩
    have hr : r ≠ 0 := fun h => ha (by rw [h, mul_zero])
    have hs : s ≠ 0 := fun h => hb (by rw [h, mul_zero])
    refine ⟨t / (r * s), ?_⟩
    field_simp [hr, hs]
    linear_combination ht
  have isSquare_sub_of_kummer_isSquare : ∀ (ea eb ec x : F),
      IsSquare (μ ea eb ec x) → IsSquare (x - ea) := by
    intro ea eb ec x hsq
    dsimp [μ] at hsq
    by_cases h : x = ea
    · rw [h, sub_self]
      exact IsSquare.zero
    · rwa [if_neg h] at hsq
  have exists_double_of_kummer_sq : ∀ {x y : F} (hS : W.Nonsingular x y),
      IsSquare (μ e₁ e₂ e₃ x) → IsSquare (μ e₂ e₁ e₃ x) →
      ∃ R : W.Point, R + R = WeierstrassCurve.Affine.Point.some hS := by
    intro x y hS hsq1 hsq2
    obtain ⟨hne1, hne2, _, _, hprod⟩ :=
      kummer_coord_ne_zero_and_isDescentClass_and_prod_isSquare e₁ e₂ e₃ x y he₁₂ he₁₃ he₂₃
        (heq_of_nonsingular hS)
    have hsq3 : IsSquare (μ e₃ e₁ e₂ x) :=
      isSquare_of_isSquare_mul_three hne1 hne2 hsq1 hsq2 hprod
    exact knapp_halving_of_isSquare_sub_roots hS
      (isSquare_sub_of_kummer_isSquare e₁ e₂ e₃ x hsq1)
      (isSquare_sub_of_kummer_isSquare e₂ e₁ e₃ x hsq2)
      (isSquare_sub_of_kummer_isSquare e₃ e₁ e₂ x hsq3)
  refine ⟨δ, ?_, ?_⟩
  · intro P
    refine ⟨κ₁ P, κ₂ P, ?_⟩
    cases P with
    | zero =>
      refine ⟨one_ne_zero, one_ne_zero, rfl, rfl, ?_⟩
      exact ⟨0, 1, 1, 1, by simp, by ring, by ring⟩
    | @some x y h =>
      obtain ⟨h1, h2, _, hdesc, _⟩ :=
        kummer_coord_ne_zero_and_isDescentClass_and_prod_isSquare e₁ e₂ e₃ x y he₁₂ he₁₃ he₂₃
          (heq_of_nonsingular h)
      exact ⟨h1, h2, rfl, rfl, hdesc⟩
  · intro P Q hδ
    have hδ1 : cl (κ₁ P) = cl (κ₁ Q) := congr_arg Prod.fst hδ
    have hδ2 : cl (κ₂ P) = cl (κ₂ Q) := congr_arg Prod.snd hδ
    cases P with
    | zero =>
      cases Q with
      | zero =>
        exact ⟨0, by abel⟩
      | @some x₂ y₂ h₂ =>
        change ∃ R : W.Point, R + R = 0 - WeierstrassCurve.Affine.Point.some h₂
        rw [zero_sub, WeierstrassCurve.Affine.Point.neg_some]
        obtain ⟨hne1, hne2, _, _, _⟩ :=
          kummer_coord_ne_zero_and_isDescentClass_and_prod_isSquare e₁ e₂ e₃ x₂ y₂ he₁₂ he₁₃ he₂₃
            (heq_of_nonsingular h₂)
        have hsq1 : IsSquare (μ e₁ e₂ e₃ x₂) := by
          simpa only [one_mul] using isSquare_mul_of_cl_eq one_ne_zero hne1 hδ1
        have hsq2 : IsSquare (μ e₂ e₁ e₃ x₂) := by
          simpa only [one_mul] using isSquare_mul_of_cl_eq one_ne_zero hne2 hδ2
        exact exists_double_of_kummer_sq ((W.nonsingular_neg x₂ y₂).mpr h₂) hsq1 hsq2
    | @some x₁ y₁ h₁ =>
      cases Q with
      | zero =>
        change ∃ R : W.Point, R + R = WeierstrassCurve.Affine.Point.some h₁ - 0
        rw [sub_zero]
        obtain ⟨hne1, hne2, _, _, _⟩ :=
          kummer_coord_ne_zero_and_isDescentClass_and_prod_isSquare e₁ e₂ e₃ x₁ y₁ he₁₂ he₁₃ he₂₃
            (heq_of_nonsingular h₁)
        have hsq1 : IsSquare (μ e₁ e₂ e₃ x₁) := by
          simpa only [mul_one] using isSquare_mul_of_cl_eq hne1 one_ne_zero hδ1
        have hsq2 : IsSquare (μ e₂ e₁ e₃ x₁) := by
          simpa only [mul_one] using isSquare_mul_of_cl_eq hne2 one_ne_zero hδ2
        exact exists_double_of_kummer_sq h₁ hsq1 hsq2
      | @some x₂ y₂ h₂ =>
        by_cases hx : x₁ = x₂
        · have hy_sq : y₁ ^ 2 = y₂ ^ 2 := by
            rw [heq_of_nonsingular h₁, heq_of_nonsingular h₂, hx]
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy_sq with hy | hy
          · have hPQ : WeierstrassCurve.Affine.Point.some h₁ =
                WeierstrassCurve.Affine.Point.some h₂ := by
              rw [WeierstrassCurve.Affine.Point.some.injEq]
              exact ⟨hx, hy⟩
            rw [hPQ, sub_self]
            exact ⟨0, add_zero 0⟩
          · have hnegQ : -WeierstrassCurve.Affine.Point.some h₂ =
                WeierstrassCurve.Affine.Point.some h₁ := by
              rw [WeierstrassCurve.Affine.Point.neg_some,
                  WeierstrassCurve.Affine.Point.some.injEq]
              refine ⟨hx.symm, ?_⟩
              dsimp [W, threeRootsCurve, WeierstrassCurve.Affine.negY]
              linear_combination -hy
            refine ⟨WeierstrassCurve.Affine.Point.some h₁, ?_⟩
            rw [sub_eq_add_neg, hnegQ]
        · rw [sub_eq_add_neg, WeierstrassCurve.Affine.Point.neg_some,
              WeierstrassCurve.Affine.Point.add_of_X_ne hx]
          have hx₃ : W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂)) =
              ((y₁ + y₂) / (x₁ - x₂)) ^ 2 + (e₁ + e₂ + e₃) - x₁ - x₂ := by
            rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
            dsimp [W, threeRootsCurve, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY]
            ring
          have heq₁ := heq_of_nonsingular h₁
          have heq₂ := heq_of_nonsingular h₂
          obtain ⟨hne1_1, hne2_1, _, _, hprod1⟩ :=
            kummer_coord_ne_zero_and_isDescentClass_and_prod_isSquare e₁ e₂ e₃ x₁ y₁ he₁₂ he₁₃ he₂₃ heq₁
          obtain ⟨hne1_2, hne2_2, _, _, hprod2⟩ :=
            kummer_coord_ne_zero_and_isDescentClass_and_prod_isSquare e₁ e₂ e₃ x₂ y₂ he₁₂ he₁₃ he₂₃ heq₂
          have hsq_μ1 : IsSquare (μ e₁ e₂ e₃ x₁ * μ e₁ e₂ e₃ x₂) :=
            isSquare_mul_of_cl_eq hne1_1 hne1_2 hδ1
          have hsq_μ2 : IsSquare (μ e₂ e₁ e₃ x₁ * μ e₂ e₁ e₃ x₂) :=
            isSquare_mul_of_cl_eq hne2_1 hne2_2 hδ2
          have hprod12 : IsSquare
              ((μ e₁ e₂ e₃ x₁ * μ e₁ e₂ e₃ x₂) *
               (μ e₂ e₁ e₃ x₁ * μ e₂ e₁ e₃ x₂) *
               (μ e₃ e₁ e₂ x₁ * μ e₃ e₁ e₂ x₂)) := by
            rcases hprod1 with ⟨r₁, hr₁⟩
            rcases hprod2 with ⟨r₂, hr₂⟩
            refine ⟨r₁ * r₂, ?_⟩
            change (μ e₁ e₂ e₃ x₁ * μ e₁ e₂ e₃ x₂) *
              (μ e₂ e₁ e₃ x₁ * μ e₂ e₁ e₃ x₂) *
              (μ e₃ e₁ e₂ x₁ * μ e₃ e₁ e₂ x₂) = (r₁ * r₂) * (r₁ * r₂)
            have hr₁' : μ e₁ e₂ e₃ x₁ * μ e₂ e₁ e₃ x₁ * μ e₃ e₁ e₂ x₁ = r₁ * r₁ := hr₁
            have hr₂' : μ e₁ e₂ e₃ x₂ * μ e₂ e₁ e₃ x₂ * μ e₃ e₁ e₂ x₂ = r₂ * r₂ := hr₂
            linear_combination
              (μ e₁ e₂ e₃ x₂ * μ e₂ e₁ e₃ x₂ * μ e₃ e₁ e₂ x₂) * hr₁' +
              (r₁ * r₁) * hr₂'
          have hsq_μ3 : IsSquare (μ e₃ e₁ e₂ x₁ * μ e₃ e₁ e₂ x₂) :=
            isSquare_of_isSquare_mul_three
              (mul_ne_zero hne1_1 hne1_2) (mul_ne_zero hne2_1 hne2_2) hsq_μ1 hsq_μ2 hprod12
          have hsq_x₃_1 : IsSquare (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂)) - e₁) := by
            rw [hx₃]
            exact single_root_chord_isSquare e₁ e₂ e₃ x₁ y₁ x₂ y₂ he₁₂ he₁₃ hx heq₁ heq₂ hsq_μ1
          have hsq_x₃_2 : IsSquare (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂)) - e₂) := by
            have h := single_root_chord_isSquare e₂ e₁ e₃ x₁ y₁ x₂ y₂ he₁₂.symm he₂₃ hx
              (by linear_combination heq₁) (by linear_combination heq₂) hsq_μ2
            rwa [hx₃, show e₁ + e₂ + e₃ = e₂ + e₁ + e₃ by ring]
          have hsq_x₃_3 : IsSquare (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂)) - e₃) := by
            have h := single_root_chord_isSquare e₃ e₁ e₂ x₁ y₁ x₂ y₂ he₁₃.symm he₂₃.symm hx
              (by linear_combination heq₁) (by linear_combination heq₂) hsq_μ3
            rwa [hx₃, show e₁ + e₂ + e₃ = e₃ + e₁ + e₂ by ring]
          exact knapp_halving_of_isSquare_sub_roots _
            hsq_x₃_1 hsq_x₃_2 hsq_x₃_3

theorem herbrand_quotient_card_le_of_finite_quotient {G : Type u} [AddCommGroup G]
    {α : Type*} [DecidableEq α]
    (H₀ : AddSubgroup G) (D : AddSubgroup H₀)
    (hD : ∀ h : H₀, h ∈ D ↔ ∃ h₀ : H₀, h₀ + h₀ = h)
    (L : Finset α) (δ : G → α)
    (hδ_mem : ∀ P : G, δ P ∈ L)
    (hδ_inj : ∀ P Q : G, δ P = δ Q → ∃ R : G, R + R = P - Q)
    (htors : ∀ P : G, P + P = 0 → P ∈ H₀)
    (hfin : Finite (G ⧸ H₀)) :
    Nat.card (H₀ ⧸ D) ≤ L.card :=
by
  let f : G →+ G :=
    { toFun := fun P => P + P
      map_zero' := add_zero 0
      map_add' := fun P Q => add_add_add_comm P Q P Q }
  have h_map_eq : AddSubgroup.map H₀.subtype D = AddSubgroup.map f H₀ := by
    ext x
    simp only [AddSubgroup.mem_map, AddSubgroup.subtype_apply, hD]
    constructor
    · rintro ⟨h, ⟨h₀, hh₀⟩, rfl⟩
      refine ⟨(h₀ : G), h₀.2, ?_⟩
      change (h₀ : G) + (h₀ : G) = (h : G)
      exact congr_arg Subtype.val hh₀
    · rintro ⟨y, hy, rfl⟩
      let h₀ : H₀ := ⟨y, hy⟩
      refine ⟨h₀ + h₀, ⟨h₀, rfl⟩, rfl⟩
  have h_sup_ker : H₀ ⊔ f.ker = H₀ := by
    apply sup_eq_left.mpr
    intro P hP
    exact htors P (AddMonoidHom.mem_ker.mp hP)
  have h_idx_mul : D.index * H₀.index = f.range.index * H₀.index := by
    calc D.index * H₀.index
        = (AddSubgroup.map H₀.subtype D).index := (AddSubgroup.index_map_subtype D).symm
      _ = (AddSubgroup.map f H₀).index := by rw [h_map_eq]
      _ = (H₀ ⊔ f.ker).index * f.range.index := AddSubgroup.index_map H₀ f
      _ = H₀.index * f.range.index := by rw [h_sup_ker]
      _ = f.range.index * H₀.index := mul_comm _ _
  have h_H₀_pos : 0 < H₀.index := by
    rw [AddSubgroup.index_eq_card]
    exact Nat.card_pos
  have h_card_eq : Nat.card (H₀ ⧸ D) = Nat.card (G ⧸ f.range) := by
    rw [← AddSubgroup.index_eq_card D, ← AddSubgroup.index_eq_card f.range]
    exact Nat.mul_right_cancel h_H₀_pos h_idx_mul
  let ι : (G ⧸ f.range) → ↥L := fun q => ⟨δ (Quotient.out q), hδ_mem (Quotient.out q)⟩
  have hι_inj : Function.Injective ι := by
    intro q₁ q₂ hq
    have hδ_eq : δ (Quotient.out q₁) = δ (Quotient.out q₂) := congr_arg Subtype.val hq
    obtain ⟨R, hR⟩ := hδ_inj (Quotient.out q₁) (Quotient.out q₂) hδ_eq
    have h_mem : -Quotient.out q₁ + Quotient.out q₂ ∈ f.range := by
      rw [AddMonoidHom.mem_range]
      refine ⟨-R, ?_⟩
      change (-R) + (-R) = -Quotient.out q₁ + Quotient.out q₂
      have hR' : (-R) + (-R) = -(R + R) := by abel
      rw [hR', hR]
      abel
    have h_q_eq := (QuotientAddGroup.eq (s := f.range)).mpr h_mem
    rwa [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at h_q_eq
  have h_card_le : Nat.card (G ⧸ f.range) ≤ Nat.card ↥L :=
    Nat.card_le_card_of_injective ι hι_inj
  have hL_card : Nat.card ↥L = L.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [h_card_eq, ← hL_card]
  exact h_card_le

theorem threeRootsCurve_add_tw_formulas {F : Type u} [Field F] [DecidableEq F]
    (hchar : (2 : F) ≠ 0) (e₁ e₂ e₃ A B : F)
    (hA : A = (e₁ - e₂) + (e₁ - e₃)) (hB : B = (e₁ - e₂) * (e₁ - e₃)) :
    (∀ x y : F,
      ((threeRootsCurve e₁ e₂ e₃).toAffine.Equation x y ↔
        y ^ 2 = (x - e₁) * (x - e₂) * (x - e₃)) ∧
      ((threeRootsCurve e₁ e₂ e₃).toAffine.Equation x y ↔
        y ^ 2 = (x - e₁) ^ 3 + A * (x - e₁) ^ 2 + B * (x - e₁)) ∧
      (y ≠ 0 →
        ((threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x y ↔
          y ^ 2 = (x - e₁) * (x - e₂) * (x - e₃)))) ∧
    (∀ (x y : F) (h : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x y),
      (threeRootsCurve e₁ e₂ e₃).toAffine.negY x y = -y ∧
      (∃ h_neg : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x (-y),
        -WeierstrassCurve.Affine.Point.some h = WeierstrassCurve.Affine.Point.some h_neg) ∧
      (WeierstrassCurve.Affine.Point.some h + WeierstrassCurve.Affine.Point.some h = 0 ↔ y = 0)) ∧
    (∀ (x₁ y₁ x₂ y₂ : F)
      (h₁ : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x₁ y₁)
      (h₂ : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x₂ y₂),
      y₁ ≠ 0 → y₂ ≠ 0 → ¬ (x₁ = x₂ ∧ y₁ = -y₂) →
      ∃ (lam nu x₃ y₃ : F) (h₃ : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x₃ y₃),
        WeierstrassCurve.Affine.Point.some h₁ + WeierstrassCurve.Affine.Point.some h₂ =
          WeierstrassCurve.Affine.Point.some h₃ ∧
        lam * ((x₁ - e₁) / y₁) + nu * (1 / y₁) = 1 ∧
        lam * (1 - A * ((x₁ - e₁) / y₁) ^ 2 - B * ((x₁ - e₁) / y₁) * (1 / y₁ + 1 / y₂)) =
          -nu * (((x₁ - e₁) / y₁) ^ 2 + ((x₁ - e₁) / y₁) * ((x₂ - e₁) / y₂) +
            ((x₂ - e₁) / y₂) ^ 2 + A * ((x₁ - e₁) / y₁ + (x₂ - e₁) / y₂) * (1 / y₂) +
            B * (1 / y₂) ^ 2) ∧
        y₁ * y₂ * (-y₃) = nu * (nu ^ 2 - A * lam * nu + B * lam ^ 2) ∧
        (x₁ - e₁) * y₂ * (-y₃) + (x₂ - e₁) * y₁ * (-y₃) + (x₃ - e₁) * y₁ * y₂ =
          nu * (2 * B * lam - A * nu) ∧
        -y₃ = lam * (x₃ - e₁) + nu) :=
by
  let W := (threeRootsCurve e₁ e₂ e₃).toAffine
  have h_negY : ∀ x y : F, W.negY x y = -y := by
    intro x y
    dsimp [W, threeRootsCurve, WeierstrassCurve.Affine.negY]
    ring
  have h_eq_roots : ∀ x y : F, W.Equation x y ↔ y ^ 2 = (x - e₁) * (x - e₂) * (x - e₃) := by
    intro x y
    rw [WeierstrassCurve.Affine.equation_iff]
    dsimp [W, threeRootsCurve]
    constructor <;> intro h <;> linear_combination h
  have h_eq_shift : ∀ x y : F,
      W.Equation x y ↔ y ^ 2 = (x - e₁) ^ 3 + A * (x - e₁) ^ 2 + B * (x - e₁) := by
    intro x y
    rw [h_eq_roots x y, hA, hB]
    constructor <;> intro h <;> linear_combination h
  have h_ns_iff : ∀ x y : F, y ≠ 0 →
      (W.Nonsingular x y ↔ y ^ 2 = (x - e₁) * (x - e₂) * (x - e₃)) := by
    intro x y hy
    rw [WeierstrassCurve.Affine.nonsingular_iff, h_eq_roots x y]
    have hy_or : W.a₁ * y ≠ 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ∨ y ≠ -y - W.a₁ * x - W.a₃ := by
      right
      intro h_eq
      have h2y : (2 : F) * y = 0 := by
        dsimp [W, threeRootsCurve] at h_eq
        linear_combination h_eq
      exact mul_ne_zero hchar hy h2y
    exact ⟨fun h => h.1, fun h => ⟨h, hy_or⟩⟩
  refine ⟨fun x y => ⟨h_eq_roots x y, h_eq_shift x y, h_ns_iff x y⟩, ?_, ?_⟩
  · intro x y h
    refine ⟨h_negY x y, ?_, ?_⟩
    · have h_neg : W.Nonsingular x (-y) := by
        rw [← h_negY x y]
        exact (WeierstrassCurve.Affine.nonsingular_neg x y).mpr h
      refine ⟨h_neg, ?_⟩
      rw [WeierstrassCurve.Affine.Point.neg_some h, WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨rfl, h_negY x y⟩
    · constructor
      · intro h2P
        by_contra hy
        have hy_neg : y ≠ W.negY x y := by
          rw [h_negY x y]
          intro h_eq
          exact mul_ne_zero hchar hy (by linear_combination h_eq)
        rw [WeierstrassCurve.Affine.Point.add_of_Y_ne hy_neg] at h2P
        nomatch h2P
      · intro hy
        have hy_neg : y = W.negY x y := by
          rw [h_negY x y, hy, neg_zero]
        exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy_neg
  · intro x₁ y₁ x₂ y₂ h₁ h₂ hy₁ hy₂ h_not_opp
    have hxy : ¬ (x₁ = x₂ ∧ y₁ = W.negY x₂ y₂) := by
      rwa [h_negY x₂ y₂]
    let lam : F := W.slope x₁ x₂ y₁ y₂
    let nu : F := y₁ - lam * (x₁ - e₁)
    let x₃ : F := W.addX x₁ x₂ lam
    let y₃ : F := W.addY x₁ x₂ y₁ lam
    have h₃ : W.Nonsingular x₃ y₃ := WeierstrassCurve.Affine.nonsingular_add h₁ h₂ hxy
    have h_sum_eq : WeierstrassCurve.Affine.Point.some h₁ + WeierstrassCurve.Affine.Point.some h₂ =
        WeierstrassCurve.Affine.Point.some h₃ :=
      WeierstrassCurve.Affine.Point.add_some hxy
    have hnu : nu = y₁ - lam * (x₁ - e₁) := rfl
    have hX₃ : x₃ - e₁ = lam ^ 2 - A - (x₁ - e₁) - (x₂ - e₁) := by
      dsimp [x₃, W, threeRootsCurve, WeierstrassCurve.Affine.addX]
      rw [hA]
      ring
    have hy₃ : -y₃ = lam * (x₃ - e₁) + nu := by
      dsimp [x₃, y₃, nu, W, threeRootsCurve, WeierstrassCurve.Affine.addX,
        WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
        WeierstrassCurve.Affine.negY]
      ring
    have heq₁ : y₁ ^ 2 = (x₁ - e₁) ^ 3 + A * (x₁ - e₁) ^ 2 + B * (x₁ - e₁) :=
      (h_eq_shift x₁ y₁).mp h₁.1
    have heq₂ : y₂ ^ 2 = (x₂ - e₁) ^ 3 + A * (x₂ - e₁) ^ 2 + B * (x₂ - e₁) :=
      (h_eq_shift x₂ y₂).mp h₂.1
    have hg₃_and_g₄ : lam * ((x₁ - e₁) - (x₂ - e₁)) = y₁ - y₂ ∧
        lam * (y₁ + y₂) = (x₁ - e₁) ^ 2 + (x₁ - e₁) * (x₂ - e₁) + (x₂ - e₁) ^ 2 +
          A * ((x₁ - e₁) + (x₂ - e₁)) + B := by
      by_cases hx : x₁ = x₂
      · have hy_ne : y₁ ≠ -y₂ := fun hy => h_not_opp ⟨hx, hy⟩
        have hy_sq : y₁ ^ 2 = y₂ ^ 2 := by
          rw [heq₁, heq₂, hx]
        have hy_eq : y₁ = y₂ :=
          (sq_eq_sq_iff_eq_or_eq_neg.mp hy_sq).resolve_right hy_ne
        refine ⟨by rw [hx, hy_eq]; ring, ?_⟩
        have hy_neg₂ : y₁ ≠ W.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
        have hy_neg₁ : y₁ ≠ W.negY x₁ y₁ := by
          rw [h_negY x₁ y₁]
          intro h_eq
          exact mul_ne_zero hchar hy₁ (by linear_combination h_eq)
        have hy_sub : y₁ - W.negY x₁ y₁ ≠ 0 := sub_ne_zero.mpr hy_neg₁
        have hsl : lam * (y₁ - W.negY x₁ y₁) =
            3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁ := by
          dsimp [lam]
          rw [WeierstrassCurve.Affine.slope_of_Y_ne hx hy_neg₂]
          exact div_mul_cancel₀ _ hy_sub
        rw [h_negY x₁ y₁] at hsl
        dsimp [W, threeRootsCurve] at hsl
        rw [← hx, ← hy_eq, hA, hB]
        linear_combination hsl
      · have hx_sub : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
        have hg₃ : lam * ((x₁ - e₁) - (x₂ - e₁)) = y₁ - y₂ := by
          dsimp [lam]
          rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
          have h_sub_eq : (x₁ - e₁) - (x₂ - e₁) = x₁ - x₂ := by ring
          rw [h_sub_eq]
          exact div_mul_cancel₀ (y₁ - y₂) hx_sub
        refine ⟨hg₃, ?_⟩
        apply mul_left_cancel₀ hx_sub
        linear_combination (y₁ + y₂) * hg₃ + heq₁ - heq₂
    obtain ⟨hg₃, hg₄⟩ := hg₃_and_g₄
    refine ⟨lam, nu, x₃, y₃, h₃, h_sum_eq, ?_, ?_, ?_, ?_, hy₃⟩
    · field_simp [hy₁]
      linear_combination -hnu
    · field_simp [hy₁, hy₂]
      rw [hnu]
      linear_combination (lam * (y₁ ^ 2 + y₁ * y₂ + y₂ ^ 2)) * heq₁ +
        ((x₁ - e₁) * y₁ * (A * y₁ + (x₁ - e₁) * y₁ + (x₁ - e₁) * y₂ + (x₂ - e₁) * y₁)) * hg₃ -
        y₁ ^ 3 * hg₄
    · rw [hy₃, hX₃, hnu]
      linear_combination (-lam ^ 3) * heq₁ +
        (-lam ^ 3 * y₁ + y₁ * (lam * (lam ^ 2 - A - (x₁ - e₁) - (x₂ - e₁)) +
          (y₁ - lam * (x₁ - e₁)))) * hg₃ +
        (lam ^ 2 * y₁) * hg₄
    · rw [hy₃, hX₃, hnu]
      linear_combination (-3 * lam ^ 2) * heq₁ +
        (-3 * lam ^ 3 * (x₁ - e₁) - 2 * lam ^ 2 * (y₁ - lam * (x₁ - e₁)) +
          (x₁ - e₁) * (lam * (lam ^ 2 - A - (x₁ - e₁) - (x₂ - e₁)) + (y₁ - lam * (x₁ - e₁))) +
          (lam ^ 2 - A - (x₁ - e₁) - (x₂ - e₁)) * y₁) * hg₃ +
        (3 * lam ^ 2 * (x₁ - e₁) + 2 * lam * (y₁ - lam * (x₁ - e₁))) * hg₄

theorem threeRootsCurve_inv_param_and_halving {F : Type u} [Field F] [DecidableEq F]
    (hchar : (2 : F) ≠ 0) (e₁ e₂ e₃ A B : F)
    (he₁₂ : e₁ ≠ e₂) (he₁₃ : e₁ ≠ e₃) (he₂₃ : e₂ ≠ e₃)
    (hA : A = (e₁ - e₂) + (e₁ - e₃)) (hB : B = (e₁ - e₂) * (e₁ - e₃)) :
    (∀ (t s : F), t ≠ 0 → s ^ 2 = (1 - A * t ^ 2) ^ 2 - 4 * B * t ^ 4 →
      1 - A * t ^ 2 + s ≠ 0 →
      ∃ (x y : F) (h : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x y),
        x - e₁ = (1 - A * t ^ 2 + s) / (2 * t ^ 2) ∧ (x - e₁) / y = t) ∧
    (∀ (x y : F) (h : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x y),
      x - e₁ ≠ 0 → y ≠ 0 →
      ∀ (v₂ v₃ : F), v₂ ≠ 0 → v₃ ≠ 0 →
      v₂ ^ 2 = 1 + (e₁ - e₂) / (x - e₁) → v₃ ^ 2 = 1 + (e₁ - e₃) / (x - e₁) →
      ∃ (x₀ y₀ : F) (h₀ : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x₀ y₀),
        x₀ - e₁ = (x - e₁) * (1 + v₂) * (1 + v₃) ∧
        WeierstrassCurve.Affine.Point.some h₀ + WeierstrassCurve.Affine.Point.some h₀ =
          WeierstrassCurve.Affine.Point.some h) :=
by
  let W := (threeRootsCurve e₁ e₂ e₃).toAffine
  constructor
  · intro t s ht hs hnum
    let X : F := (1 - A * t ^ 2 + s) / (2 * t ^ 2)
    let x : F := e₁ + X
    let y : F := X / t
    have h2t2_ne : 2 * t ^ 2 ≠ 0 := mul_ne_zero hchar (pow_ne_zero 2 ht)
    have hX_ne : X ≠ 0 := div_ne_zero hnum h2t2_ne
    have hy_ne : y ≠ 0 := div_ne_zero hX_ne ht
    have hX_eq : 2 * t ^ 2 * X = 1 - A * t ^ 2 + s := by
      dsimp [X]
      field_simp [hchar, ht]
    have hy_eq : t * y = X := by
      dsimp [y]
      field_simp [ht]
    have hy2_X : y ^ 2 = X ^ 3 + A * X ^ 2 + B * X := by
      have h_4t4 : 4 * t ^ 4 * (y ^ 2 - (X ^ 3 + A * X ^ 2 + B * X)) = 0 := by
        linear_combination 4 * t ^ 2 * (t * y + X) * hy_eq -
          X * (2 * t ^ 2 * X - (1 - A * t ^ 2) + s) * hX_eq - X * hs
      have h4t4_ne : 4 * t ^ 4 ≠ 0 := by
        have h_eq4 : 4 * t ^ 4 = (2 * t ^ 2) * (2 * t ^ 2) := by ring
        rw [h_eq4]
        exact mul_ne_zero h2t2_ne h2t2_ne
      have h_sub : y ^ 2 - (X ^ 3 + A * X ^ 2 + B * X) = 0 :=
        (mul_eq_zero.mp h_4t4).resolve_left h4t4_ne
      linear_combination h_sub
    have h_eq : W.Equation x y := by
      rw [WeierstrassCurve.Affine.equation_iff]
      have h_prod : y ^ 2 = (x - e₁) * (x - e₂) * (x - e₃) := by
        rw [hy2_X, hA, hB]
        dsimp [x]
        ring
      dsimp [W, threeRootsCurve]
      linear_combination h_prod
    have hy_negY : y ≠ W.negY x y := by
      intro h0
      have h2y : (2 : F) * y = 0 := by
        dsimp [W, threeRootsCurve, WeierstrassCurve.Affine.negY] at h0
        linear_combination h0
      exact mul_ne_zero hchar hy_ne h2y
    have h_ns : W.Nonsingular x y := by
      rw [WeierstrassCurve.Affine.nonsingular_iff]
      refine ⟨h_eq, Or.inr ?_⟩
      dsimp [W, threeRootsCurve, WeierstrassCurve.Affine.negY] at hy_negY ⊢
      exact hy_negY
    refine ⟨x, y, h_ns, ?_, ?_⟩
    · dsimp [x, X]
      ring
    · have hx_sub : x - e₁ = X := by dsimp [x]; ring
      rw [hx_sub]
      dsimp [y]
      field_simp [hX_ne, ht]
  · intro x y h hX hy v₂ v₃ hv₂_ne hv₃_ne hv₂ hv₃
    have heq : y ^ 2 = (x - e₁) * (x - e₂) * (x - e₃) := by
      have hW := (WeierstrassCurve.Affine.equation_iff x y).mp h.1
      dsimp [W, threeRootsCurve] at hW
      linear_combination hW
    have hv₂' : (x - e₁) * v₂ ^ 2 = x - e₂ := by
      have h1 : (x - e₁) * v₂ ^ 2 = (x - e₁) * (1 + (e₁ - e₂) / (x - e₁)) := by rw [hv₂]
      have h2 : (x - e₁) * (1 + (e₁ - e₂) / (x - e₁)) = x - e₂ := by
        field_simp [hX]
        ring
      exact h1.trans h2
    have hv₃' : (x - e₁) * v₃ ^ 2 = x - e₃ := by
      have h1 : (x - e₁) * v₃ ^ 2 = (x - e₁) * (1 + (e₁ - e₃) / (x - e₁)) := by rw [hv₃]
      have h2 : (x - e₁) * (1 + (e₁ - e₃) / (x - e₁)) = x - e₃ := by
        field_simp [hX]
        ring
      exact h1.trans h2
    let u₁ : F := y / ((x - e₁) * v₂ * v₃)
    let u₂ : F := u₁ * v₂
    let u₃ : F := u₁ * v₃
    have hu₁_mul : u₁ * (x - e₁) * v₂ * v₃ = y := by
      dsimp [u₁]
      field_simp [hX, hv₂_ne, hv₃_ne]
    have hu₁ : u₁ ^ 2 = x - e₁ := by
      dsimp [u₁]
      field_simp [hX, hv₂_ne, hv₃_ne]
      linear_combination heq - (x - e₁) * (x - e₃) * hv₂' - (x - e₁) ^ 2 * v₂ ^ 2 * hv₃'
    have hu₂ : u₂ ^ 2 = x - e₂ := by
      dsimp [u₂]
      linear_combination v₂ ^ 2 * hu₁ + hv₂'
    have hu₃ : u₃ ^ 2 = x - e₃ := by
      dsimp [u₃]
      linear_combination v₃ ^ 2 * hu₁ + hv₃'
    have hu_prod : u₁ * u₂ * u₃ = y := by
      dsimp [u₂, u₃]
      linear_combination u₁ * v₂ * v₃ * hu₁ + hu₁_mul
    let x₀ : F := x + u₁ * u₂ + u₁ * u₃ + u₂ * u₃
    let y₀ : F := (u₁ + u₂) * (u₁ + u₃) * (u₂ + u₃)
    have hx₀₁ : x₀ - e₁ = (u₁ + u₂) * (u₁ + u₃) := by
      dsimp [x₀]
      linear_combination -hu₁
    have hx₀₂ : x₀ - e₂ = (u₁ + u₂) * (u₂ + u₃) := by
      dsimp [x₀]
      linear_combination -hu₂
    have hx₀₃ : x₀ - e₃ = (u₁ + u₃) * (u₂ + u₃) := by
      dsimp [x₀]
      linear_combination -hu₃
    have hu12 : u₁ + u₂ ≠ 0 := by
      intro h0
      apply sub_ne_zero.mpr he₁₂.symm
      linear_combination -hu₁ + hu₂ + (u₁ - u₂) * h0
    have hu13 : u₁ + u₃ ≠ 0 := by
      intro h0
      apply sub_ne_zero.mpr he₁₃.symm
      linear_combination -hu₁ + hu₃ + (u₁ - u₃) * h0
    have hu23 : u₂ + u₃ ≠ 0 := by
      intro h0
      apply sub_ne_zero.mpr he₂₃.symm
      linear_combination -hu₂ + hu₃ + (u₂ - u₃) * h0
    have hy₀_ne : y₀ ≠ 0 := mul_ne_zero (mul_ne_zero hu12 hu13) hu23
    have hy₀_negY : y₀ ≠ W.negY x₀ y₀ := by
      intro h0
      have h2y₀ : (2 : F) * y₀ = 0 := by
        dsimp [W, threeRootsCurve, WeierstrassCurve.Affine.negY] at h0
        linear_combination h0
      exact mul_ne_zero hchar hy₀_ne h2y₀
    have h₀_eq : W.Equation x₀ y₀ := by
      rw [WeierstrassCurve.Affine.equation_iff]
      have h_prod : y₀ ^ 2 = (x₀ - e₁) * (x₀ - e₂) * (x₀ - e₃) := by
        rw [hx₀₁, hx₀₂, hx₀₃]
        dsimp [y₀]
        ring
      dsimp [W, threeRootsCurve]
      linear_combination h_prod
    have h₀ : W.Nonsingular x₀ y₀ := by
      rw [WeierstrassCurve.Affine.nonsingular_iff]
      refine ⟨h₀_eq, Or.inr ?_⟩
      dsimp [W, threeRootsCurve, WeierstrassCurve.Affine.negY] at hy₀_negY ⊢
      exact hy₀_negY
    refine ⟨x₀, y₀, h₀, ?_, ?_⟩
    · rw [hx₀₁]
      dsimp [u₂, u₃]
      linear_combination (1 + v₂) * (1 + v₃) * hu₁
    · rw [WeierstrassCurve.Affine.Point.add_of_Y_ne hy₀_negY,
          WeierstrassCurve.Affine.Point.some.injEq]
      have hslope : W.slope x₀ x₀ y₀ y₀ = u₁ + u₂ + u₃ := by
        rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy₀_negY,
            div_eq_iff (sub_ne_zero.mpr hy₀_negY)]
        have h_num : 3 * x₀ ^ 2 + 2 * -(e₁ + e₂ + e₃) * x₀ + (e₁ * e₂ + e₁ * e₃ + e₂ * e₃) - 0 * y₀ =
            (x₀ - e₁) * (x₀ - e₂) + (x₀ - e₁) * (x₀ - e₃) + (x₀ - e₂) * (x₀ - e₃) := by ring
        dsimp [W, threeRootsCurve, WeierstrassCurve.Affine.negY]
        rw [h_num, hx₀₁, hx₀₂, hx₀₃]
        dsimp [y₀]
        ring
      rw [hslope]
      constructor
      · dsimp [W, threeRootsCurve, WeierstrassCurve.Affine.addX, x₀]
        linear_combination hu₁ + hu₂ + hu₃
      · dsimp [W, threeRootsCurve, WeierstrassCurve.Affine.addY,
               WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
               WeierstrassCurve.Affine.addX, x₀, y₀]
        linear_combination hu_prod - (u₁ + u₂ + u₃) * (hu₁ + hu₂ + hu₃)

theorem adicCompletion_hensel_one_plus_and_scaled_red {K : Type u} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (ev m₀ : ℕ)
    (hev : Valued.v (2 : v.adicCompletion K) = WithZero.exp (-(ev : ℤ))) :
    (∀ z : v.adicCompletion K,
      Valued.v z < Valued.v (4 : v.adicCompletion K) →
      ∃ s : v.adicCompletion K,
        s ^ 2 = 1 + z ∧ Valued.v (1 + s) = Valued.v (2 : v.adicCompletion K)) ∧
    (∃ red : v.adicCompletion K → NumberField.RingOfIntegers K ⧸ v.asIdeal ^ ev,
      red 0 = 0 ∧
      (∀ q : NumberField.RingOfIntegers K ⧸ v.asIdeal ^ ev, q + q = 0) ∧
      (∀ t₁ t₂ t₃ : v.adicCompletion K,
        Valued.v t₁ ≤ WithZero.exp (-(m₀ : ℤ)) →
        Valued.v t₂ ≤ WithZero.exp (-(m₀ : ℤ)) →
        Valued.v t₃ ≤ WithZero.exp (-(m₀ : ℤ)) →
        Valued.v (t₁ + t₂ - t₃) ≤ WithZero.exp (-((m₀ + ev : ℕ) : ℤ)) →
        red t₁ + red t₂ = red t₃) ∧
      (∀ t : v.adicCompletion K,
        Valued.v t ≤ WithZero.exp (-(m₀ : ℤ)) →
        (red t = 0 ↔ Valued.v t ≤ WithZero.exp (-((m₀ + ev : ℕ) : ℤ)))) ∧
      (∀ q : NumberField.RingOfIntegers K ⧸ v.asIdeal ^ ev,
        q ≠ 0 →
        ∃ t : v.adicCompletion K,
          t ≠ 0 ∧ Valued.v t ≤ WithZero.exp (-(m₀ : ℤ)) ∧ red t = q)) :=
by
  classical
  have h_approx_K : ∀ (a : K), IsDedekindDomain.HeightOneSpectrum.valuation K v a ≤ 1 →
      ∀ (M : ℕ), ∃ r : NumberField.RingOfIntegers K,
        IsDedekindDomain.HeightOneSpectrum.valuation K v
          (a - algebraMap (NumberField.RingOfIntegers K) K r) ≤ WithZero.exp (-(M : ℤ)) := by
    intro a ha M
    obtain ⟨xa, ya, hya, hxya⟩ :=
      IsFractionRing.div_surjective (A := NumberField.RingOfIntegers K) (K := K) a
    have hy0 : ya ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hya
    have hiy : algebraMap (NumberField.RingOfIntegers K) K ya ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hya
    have hstar : a * algebraMap (NumberField.RingOfIntegers K) K ya
        = algebraMap (NumberField.RingOfIntegers K) K xa := by
      rw [← hxya]
      exact div_mul_cancel₀ _ hiy
    obtain ⟨m, hym, hym1, hexpm⟩ :
        ∃ m : ℕ, ya ∈ v.asIdeal ^ m ∧ ya ∉ v.asIdeal ^ (m + 1) ∧
          WithZero.exp (-(m : ℤ)) = v.intValuation ya := by
      have ht0 : v.intValuation ya ≠ 0 :=
        IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero v ya hy0
      have ht1 : v.intValuation ya ≤ 1 :=
        IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v ya
      obtain ⟨k, hk⟩ : ∃ k : ℤ, WithZero.exp k = v.intValuation ya := ⟨_, WithZero.exp_log ht0⟩
      have hkle : k ≤ 0 := by
        have hstep : WithZero.exp k ≤ WithZero.exp (0 : ℤ) := by
          rw [hk, WithZero.exp_zero]; exact ht1
        exact WithZero.exp_le_exp.mp hstep
      have hcast : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      have hexpm : WithZero.exp (-(((-k).toNat : ℕ) : ℤ)) = v.intValuation ya := by
        rw [hcast, neg_neg, hk]
      refine ⟨(-k).toNat, ?_, ?_, hexpm⟩
      · exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya _).mp
          (le_of_eq hexpm.symm)
      · intro hcon
        have hle :=
          (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya
            ((-k).toNat + 1)).mpr hcon
        have he : (-(((-k).toNat + 1 : ℕ) : ℤ)) = k - 1 := by
          rw [Nat.cast_add, Nat.cast_one, hcast]; ring
        rw [he, ← hk] at hle
        have := WithZero.exp_le_exp.mp hle
        omega
    have hivy : v.intValuation ya ≤ WithZero.exp (-(m : ℤ)) :=
      (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya m).mpr hym
    have hxm : xa ∈ v.asIdeal ^ m := by
      refine (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v xa m).mp ?_
      have e1 : v.intValuation xa
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K xa) :=
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v xa).symm
      have e2 : v.intValuation ya
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K ya) :=
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v ya).symm
      calc v.intValuation xa
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (a * algebraMap (NumberField.RingOfIntegers K) K ya) := by
            rw [hstar]; exact e1
        _ = IsDedekindDomain.HeightOneSpectrum.valuation K v a *
              IsDedekindDomain.HeightOneSpectrum.valuation K v
                (algebraMap (NumberField.RingOfIntegers K) K ya) := Valuation.map_mul _ _ _
        _ ≤ 1 * IsDedekindDomain.HeightOneSpectrum.valuation K v
                (algebraMap (NumberField.RingOfIntegers K) K ya) := mul_le_mul_left ha _
        _ = v.intValuation ya := by rw [one_mul, ← e2]
        _ ≤ WithZero.exp (-(m : ℤ)) := hivy
    have hPprime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
    have hJdvd : (Ideal.span {ya} ⊔ v.asIdeal ^ (m + M)) ∣ v.asIdeal ^ (m + M) :=
      Ideal.dvd_iff_le.mpr le_sup_right
    obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow hPprime (m + M)).mp hJdvd
    have hJ : Ideal.span {ya} ⊔ v.asIdeal ^ (m + M) = v.asIdeal ^ i := associated_iff_eq.mp hassoc
    have hyJ : ya ∈ v.asIdeal ^ i := by
      rw [← hJ]
      exact Ideal.dvd_span_singleton.mp (Ideal.dvd_iff_le.mpr le_sup_left)
    have him : i ≤ m := by
      by_contra hcon
      have hle : m + 1 ≤ i := by omega
      exact hym1 (Ideal.pow_le_pow_right hle hyJ)
    have hxJ : xa ∈ Ideal.span {ya} ⊔ v.asIdeal ^ (m + M) := by
      rw [hJ]
      exact Ideal.pow_le_pow_right him hxm
    obtain ⟨p, hp, w, hw, hpw⟩ := Submodule.mem_sup.mp hxJ
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hp
    refine ⟨r, ?_⟩
    have hxrw : xa = r * ya + w := by rw [← hpw, hr]
    have key : (a - algebraMap (NumberField.RingOfIntegers K) K r)
        * algebraMap (NumberField.RingOfIntegers K) K ya
        = algebraMap (NumberField.RingOfIntegers K) K w := by
      have h1 : algebraMap (NumberField.RingOfIntegers K) K xa
          = algebraMap (NumberField.RingOfIntegers K) K r
              * algebraMap (NumberField.RingOfIntegers K) K ya
            + algebraMap (NumberField.RingOfIntegers K) K w := by
        rw [hxrw, map_add, map_mul]
      rw [sub_mul, hstar, h1]; ring
    have hV : IsDedekindDomain.HeightOneSpectrum.valuation K v
          (a - algebraMap (NumberField.RingOfIntegers K) K r) * v.intValuation ya
        = v.intValuation w := by
      rw [← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v ya,
        ← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v w,
        ← Valuation.map_mul, key]
    have hwb : v.intValuation w ≤ WithZero.exp (-((m + M : ℕ) : ℤ)) :=
      (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v w (m + M)).mpr hw
    calc IsDedekindDomain.HeightOneSpectrum.valuation K v
          (a - algebraMap (NumberField.RingOfIntegers K) K r)
        = IsDedekindDomain.HeightOneSpectrum.valuation K v
            (a - algebraMap (NumberField.RingOfIntegers K) K r) *
            (WithZero.exp (-(m : ℤ)) * WithZero.exp (m : ℤ)) := by
          rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, mul_one]
      _ = (IsDedekindDomain.HeightOneSpectrum.valuation K v
            (a - algebraMap (NumberField.RingOfIntegers K) K r) * v.intValuation ya) *
            WithZero.exp (m : ℤ) := by
          rw [← hexpm, mul_assoc]
      _ = v.intValuation w * WithZero.exp (m : ℤ) := by rw [hV]
      _ ≤ WithZero.exp (-((m + M : ℕ) : ℤ)) * WithZero.exp (m : ℤ) :=
          mul_le_mul_left hwb _
      _ = WithZero.exp (-(M : ℤ)) := by
          rw [← WithZero.exp_add]
          congr 1
          push_cast
          ring
  have h_approx_int : ∀ (z : v.adicCompletion K), Valued.v z ≤ 1 → ∀ (M : ℕ),
      ∃ r : NumberField.RingOfIntegers K,
        Valued.v (z - algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K r)) ≤ WithZero.exp (-(M : ℤ)) := by
    intro z hz M
    have hdense : DenseRange (fun y : K => algebraMap K (v.adicCompletion K) y) := by
      letI : Valued K (WithZero (Multiplicative ℤ)) :=
        IsDedekindDomain.HeightOneSpectrum.adicValued (K := K) v
      exact UniformSpace.Completion.denseRange_coe
    let γ : (WithZero (Multiplicative ℤ))ˣ :=
      Units.mk0 (WithZero.exp (-(M : ℤ))) WithZero.exp_ne_zero
    have hnhds : {y : v.adicCompletion K |
        Valued.v (y - z) < (γ : WithZero (Multiplicative ℤ))} ∈ nhds z :=
      Valued.mem_nhds.mpr ⟨γ, subset_rfl⟩
    obtain ⟨u, hu1, k, hk⟩ := mem_closure_iff_nhds.mp (hdense z) _ hnhds
    have hkl : Valued.v (z - algebraMap K (v.adicCompletion K) k) ≤ WithZero.exp (-(M : ℤ)) := by
      dsimp only at hk
      rw [Valuation.map_sub_swap, hk]
      exact le_of_lt hu1
    have hexple : WithZero.exp (-(M : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
      rw [← WithZero.exp_zero]
      exact WithZero.exp_le_exp.mpr (by omega)
    have hvc : ∀ x : K, Valued.v (algebraMap K (v.adicCompletion K) x) =
        IsDedekindDomain.HeightOneSpectrum.valuation K v x :=
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v
    have hvk : IsDedekindDomain.HeightOneSpectrum.valuation K v k ≤ 1 := by
      rw [← hvc k]
      have hsplit : algebraMap K (v.adicCompletion K) k =
          z - (z - algebraMap K (v.adicCompletion K) k) := by ring
      rw [hsplit]
      exact le_trans (Valuation.map_sub Valued.v _ _) (max_le hz (le_trans hkl hexple))
    obtain ⟨r, hr⟩ := h_approx_K k hvk M
    refine ⟨r, ?_⟩
    have hsplit2 : z - algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K r) =
        (z - algebraMap K (v.adicCompletion K) k) +
          algebraMap K (v.adicCompletion K)
            (k - algebraMap (NumberField.RingOfIntegers K) K r) := by
      rw [map_sub]; ring
    rw [hsplit2]
    refine le_trans (Valuation.map_add Valued.v _ _) (max_le hkl ?_)
    rw [hvc]
    exact hr
  have h_quad_root : ∀ (b c x₀ : v.adicCompletion K),
      Valued.v (2 * x₀ + b) = (1 : WithZero (Multiplicative ℤ)) →
      Valued.v (x₀ ^ 2 + b * x₀ + c) < (1 : WithZero (Multiplicative ℤ)) →
      ∃ x : v.adicCompletion K, x ^ 2 + b * x + c = 0 := by
    intro b c x₀ hder hval
    have hdbl : ∀ t : v.adicCompletion K, Valued.v (2 * t) ≤ Valued.v t := by
      intro t
      have e : (2 : v.adicCompletion K) * t = t + t := by ring
      have h : Valued.v (t + t) ≤ max (Valued.v t) (Valued.v t) := Valuation.map_add _ _ _
      rw [max_self] at h
      rw [e]
      exact h
    have hstep : ∀ y : v.adicCompletion K,
        Valued.v (2 * y + b) = (1 : WithZero (Multiplicative ℤ)) →
        Valued.v (y ^ 2 + b * y + c) < (1 : WithZero (Multiplicative ℤ)) →
        Valued.v (2 * (y - (y ^ 2 + b * y + c) / (2 * y + b)) + b)
            = (1 : WithZero (Multiplicative ℤ)) ∧
        Valued.v ((y - (y ^ 2 + b * y + c) / (2 * y + b)) ^ 2
              + b * (y - (y ^ 2 + b * y + c) / (2 * y + b)) + c)
            = Valued.v (y ^ 2 + b * y + c) ^ 2 ∧
        Valued.v (y - (y ^ 2 + b * y + c) / (2 * y + b) - y)
            = Valued.v (y ^ 2 + b * y + c) := by
      intro y hD hP
      have hDne : (2 : v.adicCompletion K) * y + b ≠ 0 := by
        intro hcon
        rw [hcon, map_zero] at hD
        exact zero_ne_one hD
      have ht : Valued.v ((y ^ 2 + b * y + c) / (2 * y + b))
          = Valued.v (y ^ 2 + b * y + c) := by
        rw [map_div₀, hD, div_one]
      refine ⟨?_, ?_, ?_⟩
      · have e : 2 * (y - (y ^ 2 + b * y + c) / (2 * y + b)) + b
            = (2 * y + b) - 2 * ((y ^ 2 + b * y + c) / (2 * y + b)) := by ring
        have hlt : Valued.v (2 * ((y ^ 2 + b * y + c) / (2 * y + b)))
            < Valued.v (2 * y + b) := by
          refine lt_of_le_of_lt (hdbl _) ?_
          rw [ht, hD]
          exact hP
        rw [e, Valuation.map_sub_eq_of_lt_left _ hlt, hD]
      · have hcancel : (y ^ 2 + b * y + c) / (2 * y + b) * (2 * y + b)
            = y ^ 2 + b * y + c := div_mul_cancel₀ _ hDne
        have key : (y - (y ^ 2 + b * y + c) / (2 * y + b)) ^ 2
              + b * (y - (y ^ 2 + b * y + c) / (2 * y + b)) + c
            = ((y ^ 2 + b * y + c) / (2 * y + b)) ^ 2 := by
          linear_combination -hcancel
        rw [key, Valuation.map_pow, ht]
      · have key : y - (y ^ 2 + b * y + c) / (2 * y + b) - y
            = -((y ^ 2 + b * y + c) / (2 * y + b)) := by ring
        rw [key, Valuation.map_neg, ht]
    have hdecay : ∀ δ γ : WithZero (Multiplicative ℤ), δ < 1 → γ ≠ 0 →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → δ ^ (2 ^ n) < γ := by
      intro δ γ hδ hγ
      rcases eq_or_ne δ 0 with h0 | h0
      · refine ⟨0, fun n _ => ?_⟩
        rw [h0, zero_pow (Nat.two_pow_pos n).ne']
        exact zero_lt_iff.mpr hγ
      · obtain ⟨a, rfl⟩ : ∃ a : ℤ, δ = ((Multiplicative.ofAdd a : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
          obtain ⟨g, hg⟩ := WithZero.ne_zero_iff_exists.mp h0
          exact ⟨Multiplicative.toAdd g, hg.symm⟩
        obtain ⟨β, rfl⟩ : ∃ β : ℤ, γ = ((Multiplicative.ofAdd β : Multiplicative ℤ) :
            WithZero (Multiplicative ℤ)) := by
          obtain ⟨g, hg⟩ := WithZero.ne_zero_iff_exists.mp hγ
          exact ⟨Multiplicative.toAdd g, hg.symm⟩
        have ha : a < 0 := WithZero.coe_lt_one.mp hδ
        have hpow : ∀ k : ℕ,
            ((Multiplicative.ofAdd a : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ k
              = ((Multiplicative.ofAdd ((k : ℤ) * a) : Multiplicative ℤ) :
                  WithZero (Multiplicative ℤ)) := by
          intro k
          rw [← WithZero.coe_pow]
          congr 1
        refine ⟨(-β).toNat + 1, fun n hn => ?_⟩
        rw [hpow, WithZero.coe_lt_coe]
        have hbk : -β < ((2 ^ n : ℕ) : ℤ) := by
          have hx : (-β).toNat < n := by omega
          have h1 : (-β).toNat < 2 ^ n := lt_trans hx Nat.lt_two_pow_self
          have h2' : ((-β).toNat : ℤ) < ((2 ^ n : ℕ) : ℤ) := by exact_mod_cast h1
          exact lt_of_le_of_lt (Int.self_le_toNat _) h2'
        have hkpos : (0 : ℤ) ≤ ((2 ^ n : ℕ) : ℤ) := Int.natCast_nonneg _
        have ha1 : a ≤ -1 := by omega
        have hle : ((2 ^ n : ℕ) : ℤ) * a ≤ ((2 ^ n : ℕ) : ℤ) * (-1) :=
          mul_le_mul_of_nonneg_left ha1 hkpos
        have hgoal : ((2 ^ n : ℕ) : ℤ) * a < β := by linarith
        exact hgoal
    obtain ⟨ε, hεdef⟩ : ∃ ε : WithZero (Multiplicative ℤ),
        ε = Valued.v (x₀ ^ 2 + b * x₀ + c) := ⟨_, rfl⟩
    have hε : ε < (1 : WithZero (Multiplicative ℤ)) := by rw [hεdef]; exact hval
    obtain ⟨f, hf0, hfs⟩ : ∃ f : ℕ → v.adicCompletion K, f 0 = x₀ ∧
        ∀ n : ℕ, f (n + 1) = f n - (f n ^ 2 + b * f n + c) / (2 * f n + b) :=
      ⟨fun n => Nat.rec (motive := fun _ => v.adicCompletion K) x₀
        (fun _ y => y - (y ^ 2 + b * y + c) / (2 * y + b)) n, rfl, fun _ => rfl⟩
    have hinv : ∀ n : ℕ, Valued.v (2 * f n + b) = (1 : WithZero (Multiplicative ℤ)) ∧
        Valued.v (f n ^ 2 + b * f n + c) = ε ^ (2 ^ n) := by
      intro n
      induction n with
      | zero =>
        refine ⟨by rw [hf0]; exact hder, ?_⟩
        rw [hf0, pow_zero, pow_one, hεdef]
      | succ n ih =>
        have hlt : Valued.v (f n ^ 2 + b * f n + c) < (1 : WithZero (Multiplicative ℤ)) := by
          rw [ih.2]
          exact pow_lt_one₀ zero_le' hε (Nat.two_pow_pos n).ne'
        obtain ⟨s1, s2, -⟩ := hstep (f n) ih.1 hlt
        refine ⟨by rw [hfs n]; exact s1, ?_⟩
        rw [hfs n, s2, ih.2, ← pow_mul]
        congr 1
    have hdiff : ∀ n : ℕ, Valued.v (f (n + 1) - f n) = ε ^ (2 ^ n) := by
      intro n
      have hlt : Valued.v (f n ^ 2 + b * f n + c) < (1 : WithZero (Multiplicative ℤ)) := by
        rw [(hinv n).2]
        exact pow_lt_one₀ zero_le' hε (Nat.two_pow_pos n).ne'
      obtain ⟨-, -, s3⟩ := hstep (f n) (hinv n).1 hlt
      rw [hfs n, s3, (hinv n).2]
    have hCauchy : Cauchy (Filter.map f Filter.atTop) := by
      refine Valued.cauchy_iff.mpr ⟨inferInstance, ?_⟩
      intro γ
      obtain ⟨N, hN⟩ := hdecay ε (γ : WithZero (Multiplicative ℤ)) hε (Units.ne_zero γ)
      have htel : ∀ m : ℕ, N ≤ m → Valued.v (f m - f N) < (γ : WithZero (Multiplicative ℤ)) := by
        intro m hm
        induction m, hm using Nat.le_induction with
        | base =>
          rw [sub_self, map_zero]
          exact zero_lt_iff.mpr (Units.ne_zero γ)
        | succ m hm ih =>
          have e : f (m + 1) - f N = (f (m + 1) - f m) + (f m - f N) := by ring
          rw [e]
          refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ih)
          rw [hdiff m]
          exact hN m hm
      refine ⟨f '' (Set.Ici N), Filter.image_mem_map (Filter.Ici_mem_atTop N), ?_⟩
      rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
      have e : f j - f i = (f j - f N) - (f i - f N) := by ring
      rw [e]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt (htel j hj) (htel i hi))
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hCauchy
    have hPlim : Filter.Tendsto (fun n : ℕ => f n ^ 2 + b * f n + c) Filter.atTop
        (nhds (x ^ 2 + b * x + c)) :=
      ((hx.pow 2).add (tendsto_const_nhds.mul hx)).add tendsto_const_nhds
    have hzero : Filter.Tendsto (fun n : ℕ => f n ^ 2 + b * f n + c) Filter.atTop
        (nhds (0 : v.adicCompletion K)) := by
      rw [Filter.tendsto_def]
      intro s hs
      obtain ⟨γ, hγs⟩ := Valued.mem_nhds_zero.mp hs
      obtain ⟨N, hN⟩ := hdecay ε (γ : WithZero (Multiplicative ℤ)) hε (Units.ne_zero γ)
      refine Filter.mem_of_superset (Filter.Ici_mem_atTop N) ?_
      intro n hn
      apply hγs
      show Valued.v (f n ^ 2 + b * f n + c) < (γ : WithZero (Multiplicative ℤ))
      rw [(hinv n).2]
      exact hN n hn
    exact ⟨x, tendsto_nhds_unique hPlim hzero⟩
  constructor
  · intro z hz
    have h4pos : (0 : WithZero (Multiplicative ℤ)) < Valued.v (4 : v.adicCompletion K) :=
      lt_of_le_of_lt zero_le' hz
    have h4ne : (4 : v.adicCompletion K) ≠ 0 :=
      (Valuation.ne_zero_iff Valued.v).mp (ne_of_gt h4pos)
    let ζ : v.adicCompletion K := z / (4 : v.adicCompletion K)
    have hζ : Valued.v ζ < (1 : WithZero (Multiplicative ℤ)) := by
      dsimp [ζ]
      rw [map_div₀]
      exact (div_lt_one₀ h4pos).mpr hz
    obtain ⟨W, hW⟩ := h_quad_root 1 (-ζ) 0
      (by
        rw [show (2 : v.adicCompletion K) * 0 + 1 = 1 by ring]
        exact map_one _)
      (by
        rw [show (0 : v.adicCompletion K) ^ 2 + 1 * 0 + -ζ = -ζ by ring, Valuation.map_neg]
        exact hζ)
    have hWz : W ^ 2 + W = ζ := by linear_combination hW
    have key : (4 : v.adicCompletion K) * (W ^ 2 + W) = z := by
      rw [hWz]
      dsimp [ζ]
      exact mul_div_cancel₀ z h4ne
    let s₁ : v.adicCompletion K := 1 + 2 * W
    have hs₁_sq : s₁ ^ 2 = 1 + z := by
      dsimp [s₁]
      linear_combination key
    have h_prod : (1 - s₁) * (1 + s₁) = -z := by
      linear_combination -hs₁_sq
    have h_val_prod : Valued.v (1 - s₁) * Valued.v (1 + s₁) = Valued.v z := by
      rw [← map_mul, h_prod, Valuation.map_neg]
    have h4_eq : Valued.v (4 : v.adicCompletion K) =
        Valued.v (2 : v.adicCompletion K) * Valued.v (2 : v.adicCompletion K) := by
      have h42 : (4 : v.adicCompletion K) = 2 * 2 := by norm_num
      rw [h42, map_mul]
    rcases lt_or_ge (Valued.v (1 - s₁)) (Valued.v (2 : v.adicCompletion K)) with hlt | hge
    · refine ⟨s₁, hs₁_sq, ?_⟩
      have heq : 1 + s₁ = (2 : v.adicCompletion K) - (1 - s₁) := by ring
      rw [heq, Valuation.map_sub_eq_of_lt_left _ hlt]
    · have hlt2 : Valued.v (1 + s₁) < Valued.v (2 : v.adicCompletion K) := by
        by_contra hge2
        rw [not_lt] at hge2
        have hle : Valued.v (4 : v.adicCompletion K) ≤ Valued.v z := by
          rw [h4_eq, ← h_val_prod]
          exact mul_le_mul' hge hge2
        exact not_lt_of_ge hle hz
      refine ⟨-s₁, ?_, ?_⟩
      · rw [neg_sq, hs₁_sq]
      · have heq : 1 + -s₁ = (2 : v.adicCompletion K) - (1 + s₁) := by ring
        rw [heq, Valuation.map_sub_eq_of_lt_left _ hlt2]
  · let ι_hom : NumberField.RingOfIntegers K →+* v.adicCompletion K :=
      (algebraMap K (v.adicCompletion K)).comp (algebraMap (NumberField.RingOfIntegers K) K)
    have hval_int : ∀ r : NumberField.RingOfIntegers K, Valued.v (ι_hom r) = v.intValuation r := by
      intro r
      have h1 : Valued.v (algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K r))
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K r) :=
        IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v
          (algebraMap (NumberField.RingOfIntegers K) K r)
      change Valued.v (algebraMap K (v.adicCompletion K)
        (algebraMap (NumberField.RingOfIntegers K) K r)) = v.intValuation r
      rw [h1]
      exact IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v r
    have hval_le_one : ∀ r : NumberField.RingOfIntegers K, Valued.v (ι_hom r) ≤ 1 := by
      intro r
      rw [hval_int r]
      exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v r
    have hval_le_exp_iff : ∀ r : NumberField.RingOfIntegers K,
        Valued.v (ι_hom r) ≤ WithZero.exp (-(ev : ℤ)) ↔ r ∈ v.asIdeal ^ ev := by
      intro r
      rw [hval_int r]
      exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v r ev
    obtain ⟨π₀, hπ₀⟩ := IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer v
    let ϖ : v.adicCompletion K := ι_hom π₀
    have hϖ_val : Valued.v ϖ = WithZero.exp (-1 : ℤ) :=
      (hval_int π₀).trans hπ₀
    have hϖ_pow_val : Valued.v (ϖ ^ m₀) = WithZero.exp (-(m₀ : ℤ)) := by
      rw [map_pow, hϖ_val, ← WithZero.exp_nsmul]
      congr 1
      simp
    have hϖ_pow_ne : ϖ ^ m₀ ≠ 0 := by
      intro h0
      have hval0 : Valued.v (ϖ ^ m₀) = 0 := by rw [h0, map_zero]
      rw [hϖ_pow_val] at hval0
      exact WithZero.exp_ne_zero hval0
    have hexp_add_m₀_ev :
        WithZero.exp (-(m₀ : ℤ)) * WithZero.exp (-(ev : ℤ)) =
          WithZero.exp (-((m₀ + ev : ℕ) : ℤ)) := by
      rw [← WithZero.exp_add]
      congr 1
      push_cast
      ring
    let IsScaledRed : v.adicCompletion K →
        (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ ev) → Prop :=
      fun t q => ∃ r : NumberField.RingOfIntegers K,
        Ideal.Quotient.mk (v.asIdeal ^ ev) r = q ∧
        Valued.v (t - ϖ ^ m₀ * ι_hom r) ≤ WithZero.exp (-((m₀ + ev : ℕ) : ℤ))
    have hex_scaledRed : ∀ t : v.adicCompletion K,
        Valued.v t ≤ WithZero.exp (-(m₀ : ℤ)) →
        ∃ q : NumberField.RingOfIntegers K ⧸ v.asIdeal ^ ev, IsScaledRed t q := by
      intro t ht
      let u : v.adicCompletion K := t / ϖ ^ m₀
      have hu : Valued.v u ≤ 1 := by
        dsimp only [u]
        rw [map_div₀, hϖ_pow_val]
        exact div_le_one_of_le₀ ht zero_le'
      obtain ⟨r, hr⟩ := h_approx_int u hu ev
      refine ⟨Ideal.Quotient.mk (v.asIdeal ^ ev) r, r, rfl, ?_⟩
      have heq : t - ϖ ^ m₀ * ι_hom r = ϖ ^ m₀ * (u - ι_hom r) := by
        dsimp only [u]
        have h1 : ϖ ^ m₀ * (t / ϖ ^ m₀) = t := mul_div_cancel₀ t hϖ_pow_ne
        linear_combination -h1
      rw [heq, map_mul, hϖ_pow_val, ← hexp_add_m₀_ev]
      exact mul_le_mul' le_rfl hr
    have huniq_scaledRed : ∀ (t : v.adicCompletion K)
        (q₁ q₂ : NumberField.RingOfIntegers K ⧸ v.asIdeal ^ ev),
        IsScaledRed t q₁ → IsScaledRed t q₂ → q₁ = q₂ := by
      rintro t q₁ q₂ ⟨r₁, hr₁_mk, hr₁_val⟩ ⟨r₂, hr₂_mk, hr₂_val⟩
      have hdiff : Valued.v (ϖ ^ m₀ * ι_hom (r₁ - r₂)) ≤
          WithZero.exp (-((m₀ + ev : ℕ) : ℤ)) := by
        have heq : ϖ ^ m₀ * ι_hom (r₁ - r₂) =
            (t - ϖ ^ m₀ * ι_hom r₂) - (t - ϖ ^ m₀ * ι_hom r₁) := by
          rw [map_sub]
          ring
        rw [heq]
        exact le_trans (Valuation.map_sub _ _ _) (max_le hr₂_val hr₁_val)
      have hr_val : Valued.v (ι_hom (r₁ - r₂)) ≤ WithZero.exp (-(ev : ℤ)) := by
        calc Valued.v (ι_hom (r₁ - r₂))
            = (WithZero.exp (m₀ : ℤ) * WithZero.exp (-(m₀ : ℤ))) *
                Valued.v (ι_hom (r₁ - r₂)) := by
              rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero, one_mul]
          _ = WithZero.exp (m₀ : ℤ) *
                (Valued.v (ϖ ^ m₀) * Valued.v (ι_hom (r₁ - r₂))) := by
              rw [hϖ_pow_val, mul_assoc]
          _ = WithZero.exp (m₀ : ℤ) * Valued.v (ϖ ^ m₀ * ι_hom (r₁ - r₂)) := by
              rw [map_mul]
          _ ≤ WithZero.exp (m₀ : ℤ) * WithZero.exp (-((m₀ + ev : ℕ) : ℤ)) :=
              mul_le_mul' le_rfl hdiff
          _ = WithZero.exp (-(ev : ℤ)) := by
              rw [← WithZero.exp_add]
              congr 1
              push_cast
              ring
      have hmem : r₁ - r₂ ∈ v.asIdeal ^ ev := (hval_le_exp_iff (r₁ - r₂)).mp hr_val
      have hmk_eq : Ideal.Quotient.mk (v.asIdeal ^ ev) r₁ =
          Ideal.Quotient.mk (v.asIdeal ^ ev) r₂ := by
        rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
        exact hmem
      rw [← hr₁_mk, ← hr₂_mk, hmk_eq]
    let red : v.adicCompletion K → NumberField.RingOfIntegers K ⧸ v.asIdeal ^ ev :=
      fun t => if h : Valued.v t ≤ WithZero.exp (-(m₀ : ℤ)) then (hex_scaledRed t h).choose else 0
    have hred_spec : ∀ t : v.adicCompletion K,
        Valued.v t ≤ WithZero.exp (-(m₀ : ℤ)) → IsScaledRed t (red t) := by
      intro t ht
      dsimp only [red]
      rw [dif_pos ht]
      exact (hex_scaledRed t ht).choose_spec
    have hred_eq : ∀ (t : v.adicCompletion K) (ht : Valued.v t ≤ WithZero.exp (-(m₀ : ℤ)))
        (q : NumberField.RingOfIntegers K ⧸ v.asIdeal ^ ev),
        IsScaledRed t q → red t = q := by
      intro t ht q hq
      exact huniq_scaledRed t (red t) q (hred_spec t ht) hq
    have hred_zero_elem : red 0 = 0 := by
      have h0_val : Valued.v (0 : v.adicCompletion K) ≤ WithZero.exp (-(m₀ : ℤ)) := by
        rw [map_zero]
        exact zero_le'
      apply hred_eq 0 h0_val 0
      refine ⟨0, map_zero _, ?_⟩
      rw [map_zero, mul_zero, sub_self, map_zero]
      exact zero_le'
    have hred_two_tors : ∀ q : NumberField.RingOfIntegers K ⧸ v.asIdeal ^ ev, q + q = 0 := by
      intro q
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
      rw [← map_add, Ideal.Quotient.eq_zero_iff_mem, ← hval_le_exp_iff (r + r)]
      have heq : ι_hom (r + r) = (2 : v.adicCompletion K) * ι_hom r := by
        rw [map_add]
        ring
      rw [heq, map_mul, hev]
      calc WithZero.exp (-(ev : ℤ)) * Valued.v (ι_hom r)
          ≤ WithZero.exp (-(ev : ℤ)) * 1 := mul_le_mul' le_rfl (hval_le_one r)
        _ = WithZero.exp (-(ev : ℤ)) := mul_one _
    have hred_add : ∀ t₁ t₂ t₃ : v.adicCompletion K,
        Valued.v t₁ ≤ WithZero.exp (-(m₀ : ℤ)) →
        Valued.v t₂ ≤ WithZero.exp (-(m₀ : ℤ)) →
        Valued.v t₃ ≤ WithZero.exp (-(m₀ : ℤ)) →
        Valued.v (t₁ + t₂ - t₃) ≤ WithZero.exp (-((m₀ + ev : ℕ) : ℤ)) →
        red t₁ + red t₂ = red t₃ := by
      intro t₁ t₂ t₃ ht₁ ht₂ ht₃ hdiff
      obtain ⟨r₁, hr₁_mk, hr₁_val⟩ := hred_spec t₁ ht₁
      obtain ⟨r₂, hr₂_mk, hr₂_val⟩ := hred_spec t₂ ht₂
      symm
      apply hred_eq t₃ ht₃ (red t₁ + red t₂)
      refine ⟨r₁ + r₂, ?_, ?_⟩
      · rw [map_add, hr₁_mk, hr₂_mk]
      · have heq : t₃ - ϖ ^ m₀ * ι_hom (r₁ + r₂) =
            ((t₁ - ϖ ^ m₀ * ι_hom r₁) + (t₂ - ϖ ^ m₀ * ι_hom r₂)) - (t₁ + t₂ - t₃) := by
          rw [map_add]
          ring
        rw [heq]
        refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ hdiff)
        exact le_trans (Valuation.map_add _ _ _) (max_le hr₁_val hr₂_val)
    have hred_zero : ∀ t : v.adicCompletion K,
        Valued.v t ≤ WithZero.exp (-(m₀ : ℤ)) →
        (red t = 0 ↔ Valued.v t ≤ WithZero.exp (-((m₀ + ev : ℕ) : ℤ))) := by
      intro t ht
      constructor
      · intro h0
        obtain ⟨r, hr_mk, hr_val⟩ := hred_spec t ht
        rw [h0] at hr_mk
        have hmem : r ∈ v.asIdeal ^ ev := Ideal.Quotient.eq_zero_iff_mem.mp hr_mk
        have hr_val' : Valued.v (ι_hom r) ≤ WithZero.exp (-(ev : ℤ)) :=
          (hval_le_exp_iff r).mpr hmem
        have hϖr_val : Valued.v (ϖ ^ m₀ * ι_hom r) ≤
            WithZero.exp (-((m₀ + ev : ℕ) : ℤ)) := by
          rw [map_mul, hϖ_pow_val, ← hexp_add_m₀_ev]
          exact mul_le_mul' le_rfl hr_val'
        have heq : t = (t - ϖ ^ m₀ * ι_hom r) + ϖ ^ m₀ * ι_hom r := by ring
        rw [heq]
        exact le_trans (Valuation.map_add _ _ _) (max_le hr_val hϖr_val)
      · intro ht'
        apply hred_eq t ht 0
        refine ⟨0, map_zero _, ?_⟩
        rw [map_zero, mul_zero, sub_zero]
        exact ht'
    have hred_surj : ∀ q : NumberField.RingOfIntegers K ⧸ v.asIdeal ^ ev,
        q ≠ 0 →
        ∃ t : v.adicCompletion K,
          t ≠ 0 ∧ Valued.v t ≤ WithZero.exp (-(m₀ : ℤ)) ∧ red t = q := by
      intro q hq
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
      let t : v.adicCompletion K := ϖ ^ m₀ * ι_hom r
      have ht_val : Valued.v t ≤ WithZero.exp (-(m₀ : ℤ)) := by
        dsimp [t]
        rw [map_mul, hϖ_pow_val]
        calc WithZero.exp (-(m₀ : ℤ)) * Valued.v (ι_hom r)
            ≤ WithZero.exp (-(m₀ : ℤ)) * 1 := mul_le_mul' le_rfl (hval_le_one r)
          _ = WithZero.exp (-(m₀ : ℤ)) := mul_one _
      have ht_red : red t = Ideal.Quotient.mk (v.asIdeal ^ ev) r := by
        apply hred_eq t ht_val (Ideal.Quotient.mk (v.asIdeal ^ ev) r)
        refine ⟨r, rfl, ?_⟩
        dsimp [t]
        rw [sub_self, map_zero]
        exact zero_le'
      have ht_ne : t ≠ 0 := by
        intro h0
        apply hq
        rw [← ht_red, h0, hred_zero_elem]
      exact ⟨t, ht_ne, ht_val, ht_red⟩
    exact ⟨red, hred_zero_elem, hred_two_tors, hred_add, hred_zero, hred_surj⟩

theorem lutz_ultrametric_step_estimates {K : Type u} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (e₁ e₂ e₃ A B : v.adicCompletion K)
    (hA : A = (e₁ - e₂) + (e₁ - e₃)) (hB : B = (e₁ - e₂) * (e₁ - e₃))
    (ev : ℕ)
    (hev : Valued.v (2 : v.adicCompletion K) = WithZero.exp (-(ev : ℤ))) :
    ∃ m₀ : ℕ,
      0 < m₀ ∧
      Valued.v (e₁ - e₂) < WithZero.exp (2 * (m₀ : ℤ)) ∧
      Valued.v (e₁ - e₃) < WithZero.exp (2 * (m₀ : ℤ)) ∧
      (∀ x y : v.adicCompletion K,
        y ^ 2 = (x - e₁) * (x - e₂) * (x - e₃) →
        (WithZero.exp (2 * (m₀ : ℤ)) ≤ Valued.v (x - e₁) ↔
          y ≠ 0 ∧ Valued.v ((x - e₁) / y) ≤ WithZero.exp (-(m₀ : ℤ)) ∧
            Valued.v (1 / y) ≤ WithZero.exp (-3 * (m₀ : ℤ))) ∧
        (WithZero.exp (2 * (m₀ : ℤ)) ≤ Valued.v (x - e₁) →
          x - e₁ ≠ 0 ∧ Valued.v (x - e₁) * Valued.v ((x - e₁) / y) ^ 2 = 1)) ∧
      (∀ x₁ y₁ x₂ y₂ lam nu x₃ y₃ : v.adicCompletion K,
        y₁ ≠ 0 → y₂ ≠ 0 →
        Valued.v ((x₁ - e₁) / y₁) ≤ WithZero.exp (-(m₀ : ℤ)) →
        Valued.v (1 / y₁) ≤ WithZero.exp (-3 * (m₀ : ℤ)) →
        Valued.v ((x₂ - e₁) / y₂) ≤ WithZero.exp (-(m₀ : ℤ)) →
        Valued.v (1 / y₂) ≤ WithZero.exp (-3 * (m₀ : ℤ)) →
        lam * ((x₁ - e₁) / y₁) + nu * (1 / y₁) = 1 →
        lam * (1 - A * ((x₁ - e₁) / y₁) ^ 2 - B * ((x₁ - e₁) / y₁) * (1 / y₁ + 1 / y₂)) =
          -nu * (((x₁ - e₁) / y₁) ^ 2 + ((x₁ - e₁) / y₁) * ((x₂ - e₁) / y₂) +
            ((x₂ - e₁) / y₂) ^ 2 + A * ((x₁ - e₁) / y₁ + (x₂ - e₁) / y₂) * (1 / y₂) +
            B * (1 / y₂) ^ 2) →
        y₁ * y₂ * (-y₃) = nu * (nu ^ 2 - A * lam * nu + B * lam ^ 2) →
        (x₁ - e₁) * y₂ * (-y₃) + (x₂ - e₁) * y₁ * (-y₃) + (x₃ - e₁) * y₁ * y₂ =
          nu * (2 * B * lam - A * nu) →
        -y₃ = lam * (x₃ - e₁) + nu →
        y₃ ≠ 0 ∧
        Valued.v ((x₃ - e₁) / y₃) ≤ WithZero.exp (-(m₀ : ℤ)) ∧
        Valued.v (1 / y₃) ≤ WithZero.exp (-3 * (m₀ : ℤ)) ∧
        Valued.v ((x₁ - e₁) / y₁ + (x₂ - e₁) / y₂ - (x₃ - e₁) / y₃) ≤
          WithZero.exp (-((m₀ + ev : ℕ) : ℤ))) ∧
      (∀ t : v.adicCompletion K,
        t ≠ 0 → Valued.v t ≤ WithZero.exp (-(m₀ : ℤ)) →
        1 - A * t ^ 2 ≠ 0 ∧
        Valued.v (-4 * B * t ^ 4 / (1 - A * t ^ 2) ^ 2) < Valued.v (4 : v.adicCompletion K) ∧
        ∀ s₀ : v.adicCompletion K,
          s₀ ^ 2 = 1 + (-4 * B * t ^ 4 / (1 - A * t ^ 2) ^ 2) →
          Valued.v (1 + s₀) = Valued.v (2 : v.adicCompletion K) →
          ((1 - A * t ^ 2) * s₀) ^ 2 = (1 - A * t ^ 2) ^ 2 - 4 * B * t ^ 4 ∧
          1 - A * t ^ 2 + (1 - A * t ^ 2) * s₀ ≠ 0 ∧
          WithZero.exp (2 * (m₀ : ℤ)) ≤
            Valued.v ((1 - A * t ^ 2 + (1 - A * t ^ 2) * s₀) / (2 * t ^ 2))) ∧
      (∀ X t : v.adicCompletion K,
        Valued.v X * Valued.v t ^ 2 = 1 →
        Valued.v t ≤ WithZero.exp (-((m₀ + ev : ℕ) : ℤ)) →
        Valued.v ((e₁ - e₂) / X) < Valued.v (4 : v.adicCompletion K) ∧
        Valued.v ((e₁ - e₃) / X) < Valued.v (4 : v.adicCompletion K) ∧
        ∀ v₂ v₃ : v.adicCompletion K,
          v₂ ^ 2 = 1 + (e₁ - e₂) / X →
          v₃ ^ 2 = 1 + (e₁ - e₃) / X →
          Valued.v (1 + v₂) = Valued.v (2 : v.adicCompletion K) →
          Valued.v (1 + v₃) = Valued.v (2 : v.adicCompletion K) →
          v₂ ≠ 0 ∧ v₃ ≠ 0 ∧
          WithZero.exp (2 * (m₀ : ℤ)) ≤ Valued.v (X * (1 + v₂) * (1 + v₃))) :=
by
  let val : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ)) := Valued.v
  have exp_sq : ∀ (a : ℤ), (WithZero.exp a) ^ 2 = WithZero.exp (2 * a) := by
    intro a
    rw [sq, ← WithZero.exp_add, two_mul]
  have val_le_exp_toNat_log : ∀ (x : v.adicCompletion K),
      val x ≤ WithZero.exp ((Int.toNat (val x).log : ℕ) : ℤ) := by
    intro x
    by_cases hx : val x = 0
    · rw [hx]
      exact zero_le'
    · conv_lhs => rw [← WithZero.exp_log hx]
      rw [WithZero.exp_le_exp]
      omega
  have val_four_eq : val (4 : v.adicCompletion K) = WithZero.exp (-2 * (ev : ℤ)) := by
    have h4 : (4 : v.adicCompletion K) = (2 : v.adicCompletion K) ^ 2 := by norm_num
    rw [h4, val.map_pow, hev, exp_sq]
    congr 1
    omega
  have val_mul_le_exp : ∀ {x y : v.adicCompletion K} {a b c : ℤ},
      val x ≤ WithZero.exp a → val y ≤ WithZero.exp b → a + b ≤ c →
      val (x * y) ≤ WithZero.exp c := by
    intro x y a b c hx hy h
    rw [val.map_mul]
    refine le_trans (mul_le_mul' hx hy) ?_
    rw [← WithZero.exp_add, WithZero.exp_le_exp]
    exact h
  have val_add_le_exp : ∀ {x y : v.adicCompletion K} {c : ℤ},
      val x ≤ WithZero.exp c → val y ≤ WithZero.exp c →
      val (x + y) ≤ WithZero.exp c :=
    fun hx hy => le_trans (val.map_add _ _) (max_le hx hy)
  have val_sub_le_exp : ∀ {x y : v.adicCompletion K} {c : ℤ},
      val x ≤ WithZero.exp c → val y ≤ WithZero.exp c →
      val (x - y) ≤ WithZero.exp c :=
    fun hx hy => le_trans (val.map_sub _ _) (max_le hx hy)
  let C₁ : ℕ := Int.toNat (val (e₁ - e₂)).log
  let C₂ : ℕ := Int.toNat (val (e₁ - e₃)).log
  let C : ℕ := max C₁ C₂
  let m₀ : ℕ := C + ev + 2
  have hm₀_pos : 0 < m₀ := by omega
  have hm₀ : C + ev + 2 ≤ m₀ := le_rfl
  have hα_val : val (e₁ - e₂) ≤ WithZero.exp (C : ℤ) :=
    le_trans (val_le_exp_toNat_log (e₁ - e₂))
      (WithZero.exp_le_exp.mpr (by dsimp [C, C₁]; omega))
  have hβ_val : val (e₁ - e₃) ≤ WithZero.exp (C : ℤ) :=
    le_trans (val_le_exp_toNat_log (e₁ - e₃))
      (WithZero.exp_le_exp.mpr (by dsimp [C, C₂]; omega))
  have hα : val (e₁ - e₂) < WithZero.exp (2 * (m₀ : ℤ)) :=
    lt_of_le_of_lt hα_val (WithZero.exp_lt_exp.mpr (by omega))
  have hβ : val (e₁ - e₃) < WithZero.exp (2 * (m₀ : ℤ)) :=
    lt_of_le_of_lt hβ_val (WithZero.exp_lt_exp.mpr (by omega))
  have hA_val : val A ≤ WithZero.exp (C : ℤ) := by
    rw [hA]; exact val_add_le_exp hα_val hβ_val
  have hB_val : val B ≤ WithZero.exp (2 * (C : ℤ)) := by
    rw [hB]; exact val_mul_le_exp hα_val hβ_val (by omega)
  refine ⟨m₀, hm₀_pos, hα, hβ, ?_, ?_, ?_, ?_⟩
  · 
    intro x y hy_sq
    have h_fwd : WithZero.exp (2 * (m₀ : ℤ)) ≤ val (x - e₁) →
        y ≠ 0 ∧ val ((x - e₁) / y) ≤ WithZero.exp (-(m₀ : ℤ)) ∧
        val (1 / y) ≤ WithZero.exp (-3 * (m₀ : ℤ)) ∧
        x - e₁ ≠ 0 ∧ val (x - e₁) * val ((x - e₁) / y) ^ 2 = 1 := by
      intro hx
      have hval_x_ne : val (x - e₁) ≠ 0 := by
        intro h0
        rw [h0] at hx
        exact WithZero.exp_ne_zero (le_antisymm hx zero_le')
      have hx_ne : x - e₁ ≠ 0 := (val.ne_zero_iff).mp hval_x_ne
      have hx2_eq : x - e₂ = (x - e₁) + (e₁ - e₂) := by ring
      have hx3_eq : x - e₃ = (x - e₁) + (e₁ - e₃) := by ring
      have hval_x2 : val (x - e₂) = val (x - e₁) := by
        rw [hx2_eq]
        exact val.map_add_eq_of_lt_left (lt_of_lt_of_le hα hx)
      have hval_x3 : val (x - e₃) = val (x - e₁) := by
        rw [hx3_eq]
        exact val.map_add_eq_of_lt_left (lt_of_lt_of_le hβ hx)
      have hval_y2 : val y ^ 2 = val (x - e₁) * val (x - e₁) * val (x - e₁) := by
        calc val y ^ 2 = val (y ^ 2) := (val.map_pow y 2).symm
          _ = val ((x - e₁) * (x - e₂) * (x - e₃)) := by rw [hy_sq]
          _ = val (x - e₁) * val (x - e₂) * val (x - e₃) := by rw [val.map_mul, val.map_mul]
          _ = val (x - e₁) * val (x - e₁) * val (x - e₁) := by rw [hval_x2, hval_x3]
      have hval_y_ne : val y ≠ 0 := by
        intro hy0
        have h0 : val (x - e₁) * val (x - e₁) * val (x - e₁) = 0 := by
          rw [← hval_y2, hy0, zero_pow two_ne_zero]
        exact hval_x_ne (mul_eq_zero.mp (mul_eq_zero.mp h0 |>.resolve_right hval_x_ne) |>.resolve_right hval_x_ne)
      have hy_ne : y ≠ 0 := (val.ne_zero_iff).mp hval_y_ne
      set k := (val (x - e₁)).log
      set l := (val y).log
      have hkx : val (x - e₁) = WithZero.exp k := (WithZero.exp_log hval_x_ne).symm
      have hly : val y = WithZero.exp l := (WithZero.exp_log hval_y_ne).symm
      have hk_ge : 2 * (m₀ : ℤ) ≤ k := by
        rw [hkx, WithZero.exp_le_exp] at hx
        exact hx
      have h2l_3k : 2 * l = k + k + k := by
        rw [hkx, hly, exp_sq, ← WithZero.exp_add, ← WithZero.exp_add, WithZero.exp_inj] at hval_y2
        exact hval_y2
      have h_t : val ((x - e₁) / y) ≤ WithZero.exp (-(m₀ : ℤ)) := by
        rw [val.map_div, hkx, hly, ← WithZero.exp_sub, WithZero.exp_le_exp]
        omega
      have h_w : val (1 / y) ≤ WithZero.exp (-3 * (m₀ : ℤ)) := by
        rw [val.map_div, val.map_one, ← WithZero.exp_zero, hly, ← WithZero.exp_sub, WithZero.exp_le_exp]
        omega
      have h_xt2 : val (x - e₁) * val ((x - e₁) / y) ^ 2 = 1 := by
        rw [val.map_div, hkx, hly, ← WithZero.exp_sub, exp_sq, ← WithZero.exp_add, ← WithZero.exp_zero,
            WithZero.exp_inj]
        omega
      exact ⟨hy_ne, h_t, h_w, hx_ne, h_xt2⟩
    refine ⟨⟨fun hx => ⟨(h_fwd hx).1, (h_fwd hx).2.1, (h_fwd hx).2.2.1⟩, ?_⟩,
            fun hx => (h_fwd hx).2.2.2⟩
    rintro ⟨hy_ne, h_t, h_w⟩
    by_contra h_lt
    push_neg at h_lt
    have hx2_eq : x - e₂ = (x - e₁) + (e₁ - e₂) := by ring
    have hx3_eq : x - e₃ = (x - e₁) + (e₁ - e₃) := by ring
    have hval_x2_lt : val (x - e₂) < WithZero.exp (2 * (m₀ : ℤ)) := by
      rw [hx2_eq]
      exact lt_of_le_of_lt (val.map_add _ _) (max_lt h_lt hα)
    have hval_x3_lt : val (x - e₃) < WithZero.exp (2 * (m₀ : ℤ)) := by
      rw [hx3_eq]
      exact lt_of_le_of_lt (val.map_add _ _) (max_lt h_lt hβ)
    have hval_y_ne : val y ≠ 0 := (val.ne_zero_iff).mpr hy_ne
    have hy2_ne : y ^ 2 ≠ 0 := pow_ne_zero 2 hy_ne
    rw [hy_sq] at hy2_ne
    have hx12_ne : (x - e₁) * (x - e₂) ≠ 0 := left_ne_zero_of_mul hy2_ne
    have hx1_ne : val (x - e₁) ≠ 0 := (val.ne_zero_iff).mpr (left_ne_zero_of_mul hx12_ne)
    have hx2_ne : val (x - e₂) ≠ 0 := (val.ne_zero_iff).mpr (right_ne_zero_of_mul hx12_ne)
    have hx3_ne : val (x - e₃) ≠ 0 := (val.ne_zero_iff).mpr (right_ne_zero_of_mul hy2_ne)
    set k₁ := (val (x - e₁)).log
    set k₂ := (val (x - e₂)).log
    set k₃ := (val (x - e₃)).log
    set l := (val y).log
    have hk₁ : val (x - e₁) = WithZero.exp k₁ := (WithZero.exp_log hx1_ne).symm
    have hk₂ : val (x - e₂) = WithZero.exp k₂ := (WithZero.exp_log hx2_ne).symm
    have hk₃ : val (x - e₃) = WithZero.exp k₃ := (WithZero.exp_log hx3_ne).symm
    have hly : val y = WithZero.exp l := (WithZero.exp_log hval_y_ne).symm
    rw [hk₁, WithZero.exp_lt_exp] at h_lt
    rw [hk₂, WithZero.exp_lt_exp] at hval_x2_lt
    rw [hk₃, WithZero.exp_lt_exp] at hval_x3_lt
    rw [val.map_div, val.map_one, ← WithZero.exp_zero, hly, ← WithZero.exp_sub, WithZero.exp_le_exp] at h_w
    have h_y2 : val y ^ 2 = val (x - e₁) * val (x - e₂) * val (x - e₃) := by
      rw [← val.map_pow, hy_sq, val.map_mul, val.map_mul]
    rw [hly, hk₁, hk₂, hk₃, exp_sq, ← WithZero.exp_add, ← WithZero.exp_add, WithZero.exp_inj] at h_y2
    omega
  · 
    intro x₁ y₁ x₂ y₂ lam nu x₃ y₃ hy₁ hy₂ ht₁ hw₁ ht₂ hw₂ h_lw h_ln h_y₃ h_x₃ h_line
    let t₁ := (x₁ - e₁) / y₁
    let w₁ := 1 / y₁
    let t₂ := (x₂ - e₁) / y₂
    let w₂ := 1 / y₂
    let D := 1 - A * t₁ ^ 2 - B * t₁ * (w₁ + w₂)
    let N := t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2 + A * (t₁ + t₂) * w₂ + B * w₂ ^ 2
    have ht₁_sq : val (t₁ ^ 2) ≤ WithZero.exp (-2 * (m₀ : ℤ)) := by
      rw [sq]; exact val_mul_le_exp ht₁ ht₁ (by omega)
    have hAt₁_sq : val (A * t₁ ^ 2) ≤ WithZero.exp (-1 : ℤ) :=
      val_mul_le_exp hA_val ht₁_sq (by omega)
    have hw₁₂ : val (w₁ + w₂) ≤ WithZero.exp (-3 * (m₀ : ℤ)) :=
      val_add_le_exp hw₁ hw₂
    have hBt₁ : val (B * t₁) ≤ WithZero.exp (2 * (C : ℤ) - (m₀ : ℤ)) :=
      val_mul_le_exp hB_val ht₁ (by omega)
    have hBt₁w : val (B * t₁ * (w₁ + w₂)) ≤ WithZero.exp (-1 : ℤ) :=
      val_mul_le_exp hBt₁ hw₁₂ (by omega)
    have hD_sub_lt : val (A * t₁ ^ 2 + B * t₁ * (w₁ + w₂)) < val (1 : v.adicCompletion K) := by
      rw [val.map_one, ← WithZero.exp_zero]
      exact lt_of_le_of_lt (val_add_le_exp hAt₁_sq hBt₁w) (WithZero.exp_lt_exp.mpr (by omega))
    have hD_eq : D = 1 - (A * t₁ ^ 2 + B * t₁ * (w₁ + w₂)) := by dsimp [D]; ring
    have hD_val : val D = 1 := by
      rw [hD_eq, val.map_sub_eq_of_lt_left hD_sub_lt, val.map_one]
    have hD_ne : D ≠ 0 := by
      apply (val.ne_zero_iff).mp; rw [hD_val]; exact one_ne_zero
    have ht₁₂_mul : val (t₁ * t₂) ≤ WithZero.exp (-2 * (m₀ : ℤ)) :=
      val_mul_le_exp ht₁ ht₂ (by omega)
    have ht₂_sq : val (t₂ ^ 2) ≤ WithZero.exp (-2 * (m₀ : ℤ)) := by
      rw [sq]; exact val_mul_le_exp ht₂ ht₂ (by omega)
    have ht₁₂_add : val (t₁ + t₂) ≤ WithZero.exp (-(m₀ : ℤ)) :=
      val_add_le_exp ht₁ ht₂
    have hAt₁₂ : val (A * (t₁ + t₂)) ≤ WithZero.exp ((C : ℤ) - (m₀ : ℤ)) :=
      val_mul_le_exp hA_val ht₁₂_add (by omega)
    have hAt₁₂w₂ : val (A * (t₁ + t₂) * w₂) ≤ WithZero.exp (-2 * (m₀ : ℤ)) :=
      val_mul_le_exp hAt₁₂ hw₂ (by omega)
    have hw₂_sq : val (w₂ ^ 2) ≤ WithZero.exp (-6 * (m₀ : ℤ)) := by
      rw [sq]; exact val_mul_le_exp hw₂ hw₂ (by omega)
    have hBw₂_sq : val (B * w₂ ^ 2) ≤ WithZero.exp (-2 * (m₀ : ℤ)) :=
      val_mul_le_exp hB_val hw₂_sq (by omega)
    have hN_val : val N ≤ WithZero.exp (-2 * (m₀ : ℤ)) :=
      val_add_le_exp
        (val_add_le_exp
          (val_add_le_exp (val_add_le_exp ht₁_sq ht₁₂_mul) ht₂_sq)
          hAt₁₂w₂)
        hBw₂_sq
    have h_ln' : lam * D = -nu * N := h_ln
    have hnu_ne : nu ≠ 0 := by
      intro hnu0
      have hlamD : lam * D = 0 := by rw [h_ln', hnu0, neg_zero, zero_mul]
      have hlam0 : lam = 0 := (mul_eq_zero.mp hlamD).resolve_right hD_ne
      have h10 : (1 : v.adicCompletion K) = 0 := by
        calc (1 : v.adicCompletion K) = lam * t₁ + nu * w₁ := h_lw.symm
          _ = 0 := by rw [hlam0, hnu0, zero_mul, zero_mul, add_zero]
      exact one_ne_zero h10
    let mu := lam / nu
    have hmu_eq : mu = -N / D := by
      dsimp [mu]
      rw [div_eq_div_iff hnu_ne hD_ne]
      linear_combination h_ln'
    have hmu_val : val mu ≤ WithZero.exp (-2 * (m₀ : ℤ)) := by
      rw [hmu_eq, val.map_div, val.map_neg, hD_val, div_one]
      exact hN_val
    have hnu_inv_eq : 1 / nu = mu * t₁ + w₁ := by
      dsimp [mu]
      field_simp [hnu_ne]
      linear_combination -h_lw
    have hnu_inv_val : val (1 / nu) ≤ WithZero.exp (-3 * (m₀ : ℤ)) := by
      rw [hnu_inv_eq]
      exact val_add_le_exp (val_mul_le_exp hmu_val ht₁ (by omega)) hw₁
    let Q := 1 - A * mu + B * mu ^ 2
    have hAmu : val (A * mu) ≤ WithZero.exp (-1 : ℤ) :=
      val_mul_le_exp hA_val hmu_val (by omega)
    have hmu_sq : val (mu ^ 2) ≤ WithZero.exp (-4 * (m₀ : ℤ)) := by
      rw [sq]; exact val_mul_le_exp hmu_val hmu_val (by omega)
    have hBmu_sq : val (B * mu ^ 2) ≤ WithZero.exp (-1 : ℤ) :=
      val_mul_le_exp hB_val hmu_sq (by omega)
    have hQ_sub_lt : val (A * mu - B * mu ^ 2) < val (1 : v.adicCompletion K) := by
      rw [val.map_one, ← WithZero.exp_zero]
      exact lt_of_le_of_lt (val_sub_le_exp hAmu hBmu_sq) (WithZero.exp_lt_exp.mpr (by omega))
    have hQ_eq : Q = 1 - (A * mu - B * mu ^ 2) := by dsimp [Q]; ring
    have hQ_val : val Q = 1 := by
      rw [hQ_eq, val.map_sub_eq_of_lt_left hQ_sub_lt, val.map_one]
    have hQ_ne : Q ≠ 0 := by
      apply (val.ne_zero_iff).mp; rw [hQ_val]; exact one_ne_zero
    have hy₃_Q : y₁ * y₂ * (-y₃) = nu ^ 3 * Q := by
      dsimp [Q, mu]
      field_simp [hnu_ne]
      linear_combination h_y₃
    have h_prod_ne : y₁ * y₂ * (-y₃) ≠ 0 := by
      rw [hy₃_Q]
      exact mul_ne_zero (pow_ne_zero 3 hnu_ne) hQ_ne
    have hy₃_ne : y₃ ≠ 0 := neg_ne_zero.mp (right_ne_zero_of_mul h_prod_ne)
    have ht_diff_eq : t₁ + t₂ - (x₃ - e₁) / y₃ = (2 * B * mu - A) * (1 / nu) / Q := by
      apply mul_right_cancel₀ h_prod_ne
      have h_lhs : (t₁ + t₂ - (x₃ - e₁) / y₃) * (y₁ * y₂ * (-y₃)) = nu * (2 * B * lam - A * nu) := by
        dsimp [t₁, t₂]
        rw [← h_x₃]
        field_simp [hy₁, hy₂, hy₃_ne]
        ring
      have h_rhs : ((2 * B * mu - A) * (1 / nu) / Q) * (y₁ * y₂ * (-y₃)) = nu * (2 * B * lam - A * nu) := by
        rw [hy₃_Q]
        dsimp [mu]
        field_simp [hnu_ne, hQ_ne]
      rw [h_lhs, h_rhs]
    have h2_le : val (2 : v.adicCompletion K) ≤ WithZero.exp (0 : ℤ) := by
      rw [hev, WithZero.exp_le_exp]; omega
    have hBmu : val (B * mu) ≤ WithZero.exp (C : ℤ) :=
      val_mul_le_exp hB_val hmu_val (by omega)
    have h2Bmu : val (2 * B * mu) ≤ WithZero.exp (C : ℤ) := by
      rw [mul_assoc]; exact val_mul_le_exp h2_le hBmu (by omega)
    have h2BmuA : val (2 * B * mu - A) ≤ WithZero.exp (C : ℤ) :=
      val_sub_le_exp h2Bmu hA_val
    have ht_diff_val : val (t₁ + t₂ - (x₃ - e₁) / y₃) ≤ WithZero.exp (-((m₀ + ev : ℕ) : ℤ)) := by
      rw [ht_diff_eq, val.map_div, hQ_val, div_one]
      exact val_mul_le_exp h2BmuA hnu_inv_val (by omega)
    have ht_diff_val_m₀ : val (t₁ + t₂ - (x₃ - e₁) / y₃) ≤ WithZero.exp (-(m₀ : ℤ)) :=
      le_trans ht_diff_val (WithZero.exp_le_exp.mpr (by omega))
    have ht₃_eq : (x₃ - e₁) / y₃ = (t₁ + t₂) - (t₁ + t₂ - (x₃ - e₁) / y₃) := by ring
    have ht₃_val : val ((x₃ - e₁) / y₃) ≤ WithZero.exp (-(m₀ : ℤ)) := by
      rw [ht₃_eq]
      exact val_sub_le_exp ht₁₂_add ht_diff_val_m₀
    have hw₃_eq : 1 / y₃ = -(mu * ((x₃ - e₁) / y₃)) - 1 / nu := by
      dsimp [mu]
      field_simp [hnu_ne, hy₃_ne]
      linear_combination -h_line
    have hw₃_val : val (1 / y₃) ≤ WithZero.exp (-3 * (m₀ : ℤ)) := by
      rw [hw₃_eq]
      refine val_sub_le_exp ?_ hnu_inv_val
      rw [val.map_neg]
      exact val_mul_le_exp hmu_val ht₃_val (by omega)
    exact ⟨hy₃_ne, ht₃_val, hw₃_val, ht_diff_val⟩
  · 
    intro t ht_ne ht_val
    have ht2_val : val (t ^ 2) ≤ WithZero.exp (-2 * (m₀ : ℤ)) := by
      rw [sq]; exact val_mul_le_exp ht_val ht_val (by omega)
    have hAt2_val : val (A * t ^ 2) ≤ WithZero.exp (-1 : ℤ) :=
      val_mul_le_exp hA_val ht2_val (by omega)
    have hAt2_lt : val (A * t ^ 2) < val (1 : v.adicCompletion K) := by
      rw [val.map_one, ← WithZero.exp_zero]
      exact lt_of_le_of_lt hAt2_val (WithZero.exp_lt_exp.mpr (by omega))
    have h1At_val : val (1 - A * t ^ 2) = 1 := by
      rw [val.map_sub_eq_of_lt_left hAt2_lt, val.map_one]
    have h1At_ne : 1 - A * t ^ 2 ≠ 0 := by
      apply (val.ne_zero_iff).mp; rw [h1At_val]; exact one_ne_zero
    have ht4_val : val (t ^ 4) ≤ WithZero.exp (-4 * (m₀ : ℤ)) := by
      rw [show (4 : ℕ) = 2 + 2 by rfl, pow_add]
      exact val_mul_le_exp ht2_val ht2_val (by omega)
    have hz_lt : val (-4 * B * t ^ 4 / (1 - A * t ^ 2) ^ 2) < val (4 : v.adicCompletion K) := by
      have h_neg4 : (-4 : v.adicCompletion K) = -(4 : v.adicCompletion K) := by ring
      rw [val.map_div, val.map_pow, h1At_val, one_pow, div_one,
          val.map_mul, val.map_mul, h_neg4, val.map_neg, val_four_eq]
      refine lt_of_le_of_lt (mul_le_mul' (mul_le_mul' le_rfl hB_val) ht4_val) ?_
      rw [← WithZero.exp_add, ← WithZero.exp_add, WithZero.exp_lt_exp]
      omega
    refine ⟨h1At_ne, hz_lt, ?_⟩
    intro s₀ hs₀_sq hs₀_val
    have h_sq : ((1 - A * t ^ 2) * s₀) ^ 2 = (1 - A * t ^ 2) ^ 2 - 4 * B * t ^ 4 := by
      rw [mul_pow, hs₀_sq]
      field_simp [h1At_ne]
      ring
    have h_num_eq : 1 - A * t ^ 2 + (1 - A * t ^ 2) * s₀ = (1 - A * t ^ 2) * (1 + s₀) := by ring
    have h_num_val : val (1 - A * t ^ 2 + (1 - A * t ^ 2) * s₀) = WithZero.exp (-(ev : ℤ)) := by
      rw [h_num_eq, val.map_mul, h1At_val, one_mul, hs₀_val, hev]
    have h_num_ne : 1 - A * t ^ 2 + (1 - A * t ^ 2) * s₀ ≠ 0 := by
      apply (val.ne_zero_iff).mp; rw [h_num_val]; exact WithZero.exp_ne_zero
    have hval_t_ne : val t ≠ 0 := (val.ne_zero_iff).mpr ht_ne
    set k := (val t).log
    have hkt : val t = WithZero.exp k := (WithZero.exp_log hval_t_ne).symm
    have hk_le : k ≤ -(m₀ : ℤ) := by
      rw [hkt, WithZero.exp_le_exp] at ht_val
      exact ht_val
    have h_quot : WithZero.exp (2 * (m₀ : ℤ)) ≤
        val ((1 - A * t ^ 2 + (1 - A * t ^ 2) * s₀) / (2 * t ^ 2)) := by
      rw [val.map_div, h_num_val, val.map_mul, hev, val.map_pow, hkt, exp_sq,
          ← WithZero.exp_add, ← WithZero.exp_sub, WithZero.exp_le_exp]
      omega
    exact ⟨h_sq, h_num_ne, h_quot⟩
  · 
    intro X t hXt ht_val
    have hXt_ne : val X * val t ^ 2 ≠ 0 := by rw [hXt]; exact one_ne_zero
    have hval_X_ne : val X ≠ 0 := left_ne_zero_of_mul hXt_ne
    have hval_t_ne : val t ≠ 0 := by
      intro ht0
      apply right_ne_zero_of_mul hXt_ne
      rw [ht0, zero_pow two_ne_zero]
    set k := (val X).log
    set l := (val t).log
    have hkX : val X = WithZero.exp k := (WithZero.exp_log hval_X_ne).symm
    have hlt : val t = WithZero.exp l := (WithZero.exp_log hval_t_ne).symm
    have hkl : k + 2 * l = 0 := by
      rw [hkX, hlt, exp_sq, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_inj] at hXt
      exact hXt
    have hl_le : l ≤ -((m₀ + ev : ℕ) : ℤ) := by
      rw [hlt, WithZero.exp_le_exp] at ht_val
      exact ht_val
    have hX_inv : (val X)⁻¹ = WithZero.exp (-k) := by rw [hkX, WithZero.exp_neg]
    have hz₂_lt : val ((e₁ - e₂) / X) < val (4 : v.adicCompletion K) := by
      rw [val.map_div, div_eq_mul_inv, hX_inv, val_four_eq]
      refine lt_of_le_of_lt (mul_le_mul' hα_val le_rfl) ?_
      rw [← WithZero.exp_add, WithZero.exp_lt_exp]
      omega
    have hz₃_lt : val ((e₁ - e₃) / X) < val (4 : v.adicCompletion K) := by
      rw [val.map_div, div_eq_mul_inv, hX_inv, val_four_eq]
      refine lt_of_le_of_lt (mul_le_mul' hβ_val le_rfl) ?_
      rw [← WithZero.exp_add, WithZero.exp_lt_exp]
      omega
    refine ⟨hz₂_lt, hz₃_lt, ?_⟩
    intro v₂ v₃ hv₂_sq hv₃_sq hv₂_val hv₃_val
    have h4_le_one : val (4 : v.adicCompletion K) ≤ val (1 : v.adicCompletion K) := by
      rw [val_four_eq, val.map_one, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    have hv₂_ne : v₂ ≠ 0 := by
      intro hv0
      have h0 : val (v₂ ^ 2) = 0 := by rw [hv0, zero_pow two_ne_zero, val.map_zero]
      rw [hv₂_sq, val.map_add_eq_of_lt_left (lt_of_lt_of_le hz₂_lt h4_le_one), val.map_one] at h0
      exact one_ne_zero h0
    have hv₃_ne : v₃ ≠ 0 := by
      intro hv0
      have h0 : val (v₃ ^ 2) = 0 := by rw [hv0, zero_pow two_ne_zero, val.map_zero]
      rw [hv₃_sq, val.map_add_eq_of_lt_left (lt_of_lt_of_le hz₃_lt h4_le_one), val.map_one] at h0
      exact one_ne_zero h0
    have h_prod : WithZero.exp (2 * (m₀ : ℤ)) ≤ val (X * (1 + v₂) * (1 + v₃)) := by
      rw [val.map_mul, val.map_mul, hkX, hv₂_val, hv₃_val, hev,
          ← WithZero.exp_add, ← WithZero.exp_add, WithZero.exp_le_exp]
      omega
    exact ⟨hv₂_ne, hv₃_ne, h_prod⟩

theorem lutz_subgroup_and_mod_two_card {K : Type u} [Field K] [NumberField K]
    (a₁ a₂ a₃ : K) (h₁₂ : a₁ ≠ a₂) (h₁₃ : a₁ ≠ a₃) (h₂₃ : a₂ ≠ a₃)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    [DecidableEq (v.adicCompletion K)]
    (ev kv : ℕ)
    (hev : Valued.v (2 : v.adicCompletion K) = WithZero.exp (-(ev : ℤ)))
    (hkv : Nat.card (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ ev) = 2 ^ kv) :
    ∃ (m₀ : ℕ) (E₀ : AddSubgroup (threeRootsCurve
        (algebraMap K (v.adicCompletion K) a₁)
        (algebraMap K (v.adicCompletion K) a₂)
        (algebraMap K (v.adicCompletion K) a₃)).toAffine.Point),
      0 < m₀ ∧
      Valued.v (algebraMap K (v.adicCompletion K) a₁ -
        algebraMap K (v.adicCompletion K) a₂) < WithZero.exp (2 * (m₀ : ℤ)) ∧
      Valued.v (algebraMap K (v.adicCompletion K) a₁ -
        algebraMap K (v.adicCompletion K) a₃) < WithZero.exp (2 * (m₀ : ℤ)) ∧
      (∀ x y : v.adicCompletion K,
        ∀ h : (threeRootsCurve
          (algebraMap K (v.adicCompletion K) a₁)
          (algebraMap K (v.adicCompletion K) a₂)
          (algebraMap K (v.adicCompletion K) a₃)).toAffine.Nonsingular x y,
        WeierstrassCurve.Affine.Point.some h ∈ E₀ ↔
          WithZero.exp (2 * (m₀ : ℤ)) ≤
            Valued.v (x - algebraMap K (v.adicCompletion K) a₁)) ∧
      (∀ P ∈ E₀, P + P = 0 → P = 0) ∧
      (∀ (D₀ : AddSubgroup E₀),
        (∀ p : E₀, p ∈ D₀ ↔ ∃ q : E₀, q + q = p) →
        Nat.card (E₀ ⧸ D₀) = 2 ^ kv) :=
by
  let e₁ : v.adicCompletion K := algebraMap K (v.adicCompletion K) a₁
  let e₂ : v.adicCompletion K := algebraMap K (v.adicCompletion K) a₂
  let e₃ : v.adicCompletion K := algebraMap K (v.adicCompletion K) a₃
  let A : v.adicCompletion K := (e₁ - e₂) + (e₁ - e₃)
  let B : v.adicCompletion K := (e₁ - e₂) * (e₁ - e₃)
  have he₁₂ : e₁ ≠ e₂ := (algebraMap K (v.adicCompletion K)).injective.ne h₁₂
  have he₁₃ : e₁ ≠ e₃ := (algebraMap K (v.adicCompletion K)).injective.ne h₁₃
  have he₂₃ : e₂ ≠ e₃ := (algebraMap K (v.adicCompletion K)).injective.ne h₂₃
  have hchar : (2 : v.adicCompletion K) ≠ 0 := by
    intro h2
    have h0 : Valued.v (2 : v.adicCompletion K) = 0 := by rw [h2, map_zero]
    rw [hev] at h0
    exact WithZero.exp_ne_zero h0
  obtain ⟨m₀, hm₀_pos, hα_lt, hβ_lt, h_pt, h_add, h_surj_val, h_halve_val⟩ :=
    lutz_ultrametric_step_estimates v e₁ e₂ e₃ A B rfl rfl ev hev
  obtain ⟨h_eq, h_neg_tors, h_add_tw⟩ :=
    threeRootsCurve_add_tw_formulas hchar e₁ e₂ e₃ A B rfl rfl
  obtain ⟨h_inv_param, h_halve_pt⟩ :=
    threeRootsCurve_inv_param_and_halving hchar e₁ e₂ e₃ A B he₁₂ he₁₃ he₂₃ rfl rfl
  obtain ⟨h_hensel, red, hred_0, hred_2, hred_add, hred_zero, hred_surj⟩ :=
    adicCompletion_hensel_one_plus_and_scaled_red v ev m₀ hev
  have h_ns_eq : ∀ (x y : v.adicCompletion K),
      (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x y →
      y ^ 2 = (x - e₁) * (x - e₂) * (x - e₃) := by
    intro x y h
    exact (h_eq x y).1.mp h.1
  let E₀_pred : (threeRootsCurve e₁ e₂ e₃).toAffine.Point → Prop := fun P =>
    match P with
    | .zero => True
    | @WeierstrassCurve.Affine.Point.some _ _ _ x _ _ =>
        WithZero.exp (2 * (m₀ : ℤ)) ≤ Valued.v (x - e₁)
  have hE₀_zero : E₀_pred 0 := trivial
  have hE₀_neg : ∀ {P}, E₀_pred P → E₀_pred (-P) := by
    intro P hP
    rcases P with _ | @⟨x, y, h⟩
    · change E₀_pred (-0)
      rw [neg_zero]
      exact trivial
    · obtain ⟨h_neg, h_neg_eq⟩ := (h_neg_tors x y h).2.1
      rw [h_neg_eq]
      exact hP
  have h_opp_add_zero : ∀ {x₁ y₁ x₂ y₂ : v.adicCompletion K}
      (h₁ : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x₁ y₁)
      (h₂ : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x₂ y₂),
      x₁ = x₂ ∧ y₁ = -y₂ →
      WeierstrassCurve.Affine.Point.some h₁ + WeierstrassCurve.Affine.Point.some h₂ = 0 := by
    intro x₁ y₁ x₂ y₂ h₁ h₂ ⟨hx, hy⟩
    have hy₂ : y₂ = -y₁ := by linear_combination hy
    subst hx
    subst hy₂
    obtain ⟨h_neg, h_neg_eq⟩ := (h_neg_tors x₁ y₁ h₁).2.1
    have h_eq_pt : WeierstrassCurve.Affine.Point.some h₂ =
        -WeierstrassCurve.Affine.Point.some h₁ := by
      rw [h_neg_eq]
    rw [h_eq_pt, add_neg_cancel]
  have hE₀_add : ∀ {P₁ P₂}, E₀_pred P₁ → E₀_pred P₂ → E₀_pred (P₁ + P₂) := by
    intro P₁ P₂ hP₁ hP₂
    rcases P₁ with _ | @⟨x₁, y₁, h₁⟩
    · change E₀_pred (0 + P₂)
      rwa [zero_add]
    · rcases P₂ with _ | @⟨x₂, y₂, h₂⟩
      · change E₀_pred (WeierstrassCurve.Affine.Point.some h₁ + 0)
        rwa [add_zero]
      · by_cases h_opp : x₁ = x₂ ∧ y₁ = -y₂
        · rw [h_opp_add_zero h₁ h₂ h_opp]
          exact trivial
        · obtain ⟨hy₁, ht₁, hw₁⟩ := (h_pt x₁ y₁ (h_ns_eq x₁ y₁ h₁)).1.mp hP₁
          obtain ⟨hy₂, ht₂, hw₂⟩ := (h_pt x₂ y₂ (h_ns_eq x₂ y₂ h₂)).1.mp hP₂
          obtain ⟨lam, nu, x₃, y₃, h₃, h_sum_eq, h_lw, h_ln, h_y₃, h_x₃, h_line⟩ :=
            h_add_tw x₁ y₁ x₂ y₂ h₁ h₂ hy₁ hy₂ h_opp
          obtain ⟨hy₃, ht₃, hw₃, _⟩ :=
            h_add x₁ y₁ x₂ y₂ lam nu x₃ y₃ hy₁ hy₂ ht₁ hw₁ ht₂ hw₂ h_lw h_ln h_y₃ h_x₃ h_line
          rw [h_sum_eq]
          exact (h_pt x₃ y₃ (h_ns_eq x₃ y₃ h₃)).1.mpr ⟨hy₃, ht₃, hw₃⟩
  let E₀ : AddSubgroup (threeRootsCurve e₁ e₂ e₃).toAffine.Point :=
    { carrier := {P | E₀_pred P}
      zero_mem' := hE₀_zero
      add_mem' := fun hP₁ hP₂ => hE₀_add hP₁ hP₂
      neg_mem' := fun hP => hE₀_neg hP }
  have hE₀_tors : ∀ P ∈ E₀, P + P = 0 → P = 0 := by
    intro P hP h2P
    rcases P with _ | @⟨x, y, h⟩
    · rfl
    · obtain ⟨hy, _, _⟩ := (h_pt x y (h_ns_eq x y h)).1.mp hP
      exact absurd ((h_neg_tors x y h).2.2.mp h2P) hy
  let t_W : (threeRootsCurve e₁ e₂ e₃).toAffine.Point → v.adicCompletion K := fun P =>
    match P with
    | .zero => 0
    | @WeierstrassCurve.Affine.Point.some _ _ _ x y _ => (x - e₁) / y
  have ht_W_val : ∀ p : E₀, Valued.v (t_W p.1) ≤ WithZero.exp (-(m₀ : ℤ)) := by
    rintro ⟨P, hP⟩
    rcases P with _ | @⟨x, y, h⟩
    · change Valued.v (0 : v.adicCompletion K) ≤ WithZero.exp (-(m₀ : ℤ))
      rw [map_zero]
      exact zero_le'
    · exact ((h_pt x y (h_ns_eq x y h)).1.mp hP).2.1
  have ht_W_add_diff : ∀ p₁ p₂ : E₀,
      Valued.v (t_W p₁.1 + t_W p₂.1 - t_W (p₁ + p₂).1) ≤
        WithZero.exp (-((m₀ + ev : ℕ) : ℤ)) := by
    rintro ⟨P₁, hP₁⟩ ⟨P₂, hP₂⟩
    change Valued.v (t_W P₁ + t_W P₂ - t_W (P₁ + P₂)) ≤ WithZero.exp (-((m₀ + ev : ℕ) : ℤ))
    rcases P₁ with _ | @⟨x₁, y₁, h₁⟩
    · change Valued.v (0 + t_W P₂ - t_W (0 + P₂)) ≤ _
      rw [zero_add, zero_add, sub_self, map_zero]
      exact zero_le'
    · rcases P₂ with _ | @⟨x₂, y₂, h₂⟩
      · change Valued.v (t_W (WeierstrassCurve.Affine.Point.some h₁) + 0 -
            t_W (WeierstrassCurve.Affine.Point.some h₁ + 0)) ≤ _
        rw [add_zero, add_zero, sub_self, map_zero]
        exact zero_le'
      · by_cases h_opp : x₁ = x₂ ∧ y₁ = -y₂
        · rw [h_opp_add_zero h₁ h₂ h_opp]
          rcases h_opp with ⟨rfl, hy⟩
          have hy₂ : y₂ = -y₁ := by linear_combination hy
          subst hy₂
          change Valued.v ((x₁ - e₁) / y₁ + (x₁ - e₁) / (-y₁) - 0) ≤ _
          have h_cancel : (x₁ - e₁) / y₁ + (x₁ - e₁) / (-y₁) - 0 = 0 := by ring
          rw [h_cancel, map_zero]
          exact zero_le'
        · obtain ⟨hy₁, ht₁, hw₁⟩ := (h_pt x₁ y₁ (h_ns_eq x₁ y₁ h₁)).1.mp hP₁
          obtain ⟨hy₂, ht₂, hw₂⟩ := (h_pt x₂ y₂ (h_ns_eq x₂ y₂ h₂)).1.mp hP₂
          obtain ⟨lam, nu, x₃, y₃, h₃, h_sum_eq, h_lw, h_ln, h_y₃, h_x₃, h_line⟩ :=
            h_add_tw x₁ y₁ x₂ y₂ h₁ h₂ hy₁ hy₂ h_opp
          rw [h_sum_eq]
          exact (h_add x₁ y₁ x₂ y₂ lam nu x₃ y₃ hy₁ hy₂ ht₁ hw₁ ht₂ hw₂
            h_lw h_ln h_y₃ h_x₃ h_line).2.2.2
  let Φ : E₀ →+ (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ ev) :=
    { toFun := fun p => red (t_W p.1)
      map_zero' := hred_0
      map_add' := fun p₁ p₂ =>
        (hred_add (t_W p₁.1) (t_W p₂.1) (t_W (p₁ + p₂).1)
          (ht_W_val p₁) (ht_W_val p₂) (ht_W_val (p₁ + p₂))
          (ht_W_add_diff p₁ p₂)).symm }
  have hΦ_surj : Function.Surjective Φ := by
    intro q
    by_cases hq : q = 0
    · exact ⟨0, by rw [map_zero, hq]⟩
    · obtain ⟨t, ht_ne, ht_val, ht_red⟩ := hred_surj q hq
      obtain ⟨h1At, hz_lt, h_s₀⟩ := h_surj_val t ht_ne ht_val
      obtain ⟨s₀, hs₀_sq, hs₀_val⟩ := h_hensel (-4 * B * t ^ 4 / (1 - A * t ^ 2) ^ 2) hz_lt
      obtain ⟨hs_sq, hs_ne, hX_val⟩ := h_s₀ s₀ hs₀_sq hs₀_val
      obtain ⟨x, y, h, hx_eq, hxy_t⟩ :=
        h_inv_param t ((1 - A * t ^ 2) * s₀) ht_ne hs_sq hs_ne
      have hp_mem : WeierstrassCurve.Affine.Point.some h ∈ E₀ := by
        change WithZero.exp (2 * (m₀ : ℤ)) ≤ Valued.v (x - e₁)
        rwa [hx_eq]
      refine ⟨⟨WeierstrassCurve.Affine.Point.some h, hp_mem⟩, ?_⟩
      change red ((x - e₁) / y) = q
      rw [hxy_t, ht_red]
  have hΦ_ker : ∀ p : E₀, p ∈ Φ.ker ↔ ∃ q : E₀, q + q = p := by
    intro p
    rw [AddMonoidHom.mem_ker]
    constructor
    · intro hp_ker
      rcases p with ⟨P, hP⟩
      rcases P with _ | @⟨x, y, h⟩
      · exact ⟨0, add_zero 0⟩
      · have ht_val : Valued.v ((x - e₁) / y) ≤ WithZero.exp (-((m₀ + ev : ℕ) : ℤ)) :=
          (hred_zero ((x - e₁) / y) (ht_W_val ⟨WeierstrassCurve.Affine.Point.some h, hP⟩)).mp hp_ker
        obtain ⟨hy, _, _⟩ := (h_pt x y (h_ns_eq x y h)).1.mp hP
        obtain ⟨hX_ne, hXt_one⟩ := (h_pt x y (h_ns_eq x y h)).2 hP
        obtain ⟨hz₂_lt, hz₃_lt, h_v⟩ := h_halve_val (x - e₁) ((x - e₁) / y) hXt_one ht_val
        obtain ⟨v₂, hv₂_sq, hv₂_val⟩ := h_hensel ((e₁ - e₂) / (x - e₁)) hz₂_lt
        obtain ⟨v₃, hv₃_sq, hv₃_val⟩ := h_hensel ((e₁ - e₃) / (x - e₁)) hz₃_lt
        obtain ⟨hv₂_ne, hv₃_ne, hX₀_val⟩ :=
          h_v v₂ v₃ hv₂_sq hv₃_sq hv₂_val hv₃_val
        obtain ⟨x₀, y₀, h₀, hx₀_eq, h2P₀⟩ :=
          h_halve_pt x y h hX_ne hy v₂ v₃ hv₂_ne hv₃_ne hv₂_sq hv₃_sq
        have hq_mem : WeierstrassCurve.Affine.Point.some h₀ ∈ E₀ := by
          change WithZero.exp (2 * (m₀ : ℤ)) ≤ Valued.v (x₀ - e₁)
          rwa [hx₀_eq]
        refine ⟨⟨WeierstrassCurve.Affine.Point.some h₀, hq_mem⟩, ?_⟩
        exact Subtype.ext h2P₀
    · rintro ⟨q, rfl⟩
      rw [map_add]
      exact hred_2 (Φ q)
  refine ⟨m₀, E₀, hm₀_pos, hα_lt, hβ_lt, fun _ _ _ => Iff.rfl, hE₀_tors, ?_⟩
  intro D₀ hD₀
  have hD₀_eq : D₀ = Φ.ker := by
    ext p
    rw [hD₀ p, hΦ_ker p]
  rw [hD₀_eq]
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective Φ hΦ_surj).toEquiv]
  exact hkv

theorem addSubgroup_sup_two_torsion_card_and_mem {G : Type u} [AddCommGroup G]
    (kv : ℕ) (E₀ : AddSubgroup G) (P₁ P₂ P₃ : G)
    (hP_ne : P₁ ≠ 0 ∧ P₂ ≠ 0 ∧ P₃ ≠ 0 ∧ P₁ ≠ P₂ ∧ P₁ ≠ P₃ ∧ P₂ ≠ P₃)
    (hP_tors : ∀ P : G, P + P = 0 ↔ P = 0 ∨ P = P₁ ∨ P = P₂ ∨ P = P₃)
    (hE₀_tors : ∀ P ∈ E₀, P + P = 0 → P = 0)
    (hE₀_card : ∀ (D₀ : AddSubgroup E₀),
      (∀ p : E₀, p ∈ D₀ ↔ ∃ q : E₀, q + q = p) →
      Nat.card (E₀ ⧸ D₀) = 2 ^ kv) :
    ∃ (H₀ : AddSubgroup G) (D : AddSubgroup H₀),
      (∀ h : H₀, h ∈ D ↔ ∃ h₀ : H₀, h₀ + h₀ = h) ∧
      (∀ P : G, P + P = 0 → P ∈ H₀) ∧
      (∀ P : G, P ∈ E₀ → P ∈ H₀) ∧
      (∀ P : G, P ∉ H₀ →
        P + P ≠ 0 ∧ P ∉ E₀ ∧ P - P₁ ∉ E₀ ∧ P - P₂ ∉ E₀ ∧ P - P₃ ∉ E₀) ∧
      2 ^ (2 + kv) ≤ Nat.card (H₀ ⧸ D) :=
by
  let H₀ : AddSubgroup G :=
    { carrier := {P : G | ∃ e ∈ E₀, ∃ t : G, t + t = 0 ∧ e + t = P}
      zero_mem' := ⟨0, E₀.zero_mem, 0, add_zero 0, add_zero 0⟩
      add_mem' := by
        rintro _ _ ⟨e₁, he₁, t₁, ht₁, rfl⟩ ⟨e₂, he₂, t₂, ht₂, rfl⟩
        refine ⟨e₁ + e₂, E₀.add_mem he₁ he₂, t₁ + t₂, ?_, by abel⟩
        calc (t₁ + t₂) + (t₁ + t₂) = (t₁ + t₁) + (t₂ + t₂) := by abel
          _ = 0 + 0 := by rw [ht₁, ht₂]
          _ = 0 := add_zero 0
      neg_mem' := by
        rintro _ ⟨e, he, t, ht, rfl⟩
        refine ⟨-e, E₀.neg_mem he, -t, ?_, by abel⟩
        calc (-t) + (-t) = -(t + t) := by abel
          _ = -0 := by rw [ht]
          _ = 0 := neg_zero }
  let D : AddSubgroup H₀ :=
    { carrier := {h : H₀ | ∃ h₀ : H₀, h₀ + h₀ = h}
      zero_mem' := ⟨0, add_zero 0⟩
      add_mem' := by
        rintro _ _ ⟨h₁, rfl⟩ ⟨h₂, rfl⟩
        exact ⟨h₁ + h₂, by abel⟩
      neg_mem' := by
        rintro _ ⟨h₀, rfl⟩
        exact ⟨-h₀, by abel⟩ }
  let D₀ : AddSubgroup E₀ :=
    { carrier := {p : E₀ | ∃ q : E₀, q + q = p}
      zero_mem' := ⟨0, add_zero 0⟩
      add_mem' := by
        rintro _ _ ⟨q₁, rfl⟩ ⟨q₂, rfl⟩
        exact ⟨q₁ + q₂, by abel⟩
      neg_mem' := by
        rintro _ ⟨q, rfl⟩
        exact ⟨-q, by abel⟩ }
  have hD : ∀ h : H₀, h ∈ D ↔ ∃ h₀ : H₀, h₀ + h₀ = h := fun _ => Iff.rfl
  have hcard_E₀ : Nat.card (E₀ ⧸ D₀) = 2 ^ kv := hE₀_card D₀ (fun _ => Iff.rfl)
  have htors : ∀ P : G, P + P = 0 → P ∈ H₀ :=
    fun P hP => ⟨0, E₀.zero_mem, P, hP, zero_add P⟩
  have hE₀_sub : ∀ P : G, P ∈ E₀ → P ∈ H₀ :=
    fun P hP => ⟨P, hP, 0, add_zero 0, add_zero P⟩
  have hP₁_tors : P₁ + P₁ = 0 := (hP_tors P₁).mpr (Or.inr (Or.inl rfl))
  have hP₂_tors : P₂ + P₂ = 0 := (hP_tors P₂).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hP₃_tors : P₃ + P₃ = 0 := (hP_tors P₃).mpr (Or.inr (Or.inr (Or.inr rfl)))
  have hnot_mem : ∀ P : G, P ∉ H₀ →
      P + P ≠ 0 ∧ P ∉ E₀ ∧ P - P₁ ∉ E₀ ∧ P - P₂ ∉ E₀ ∧ P - P₃ ∉ E₀ := by
    intro P hnot
    refine ⟨fun h => hnot (htors P h), fun h => hnot (hE₀_sub P h), ?_, ?_, ?_⟩
    · intro h
      apply hnot
      have hsub : (P - P₁) + P₁ = P := sub_add_cancel P P₁
      rw [← hsub]
      exact H₀.add_mem (hE₀_sub _ h) (htors P₁ hP₁_tors)
    · intro h
      apply hnot
      have hsub : (P - P₂) + P₂ = P := sub_add_cancel P P₂
      rw [← hsub]
      exact H₀.add_mem (hE₀_sub _ h) (htors P₂ hP₂_tors)
    · intro h
      apply hnot
      have hsub : (P - P₃) + P₃ = P := sub_add_cancel P P₃
      rw [← hsub]
      exact H₀.add_mem (hE₀_sub _ h) (htors P₃ hP₃_tors)
  let τ_G : Fin 4 → G := ![0, P₁, P₂, P₃]
  have hτ_tors : ∀ i : Fin 4, τ_G i + τ_G i = 0 := by
    intro i
    fin_cases i
    · exact add_zero 0
    · exact hP₁_tors
    · exact hP₂_tors
    · exact hP₃_tors
  have hτ_surj : ∀ t : G, t + t = 0 → ∃ i : Fin 4, τ_G i = t := by
    intro t ht
    rcases (hP_tors t).mp ht with rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  have hτ_inj : ∀ i₁ i₂ : Fin 4, τ_G i₁ = τ_G i₂ → i₁ = i₂ := by
    rcases hP_ne with ⟨h10, h20, h30, h12, h13, h23⟩
    intro i₁ i₂ h
    fin_cases i₁ <;> fin_cases i₂ <;> dsimp [τ_G] at h
    · rfl
    · exact False.elim (h10 h.symm)
    · exact False.elim (h20 h.symm)
    · exact False.elim (h30 h.symm)
    · exact False.elim (h10 h)
    · rfl
    · exact False.elim (h12 h)
    · exact False.elim (h13 h)
    · exact False.elim (h20 h)
    · exact False.elim (h12 h.symm)
    · rfl
    · exact False.elim (h23 h)
    · exact False.elim (h30 h)
    · exact False.elim (h13 h.symm)
    · exact False.elim (h23 h.symm)
    · rfl
  let τ_H₀ : Fin 4 → H₀ := fun i => ⟨τ_G i, htors (τ_G i) (hτ_tors i)⟩
  let ι_E : E₀ →+ H₀ :=
    { toFun := fun p => ⟨p.1, hE₀_sub p.1 p.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let ψ₀ : E₀ →+ H₀ ⧸ D := (QuotientAddGroup.mk' D).comp ι_E
  have h_ker : ∀ x ∈ D₀, x ∈ ψ₀.ker := by
    rintro p ⟨q, rfl⟩
    rw [AddMonoidHom.mem_ker]
    dsimp [ψ₀]
    rw [QuotientAddGroup.eq_zero_iff]
    exact ⟨ι_E q, rfl⟩
  let ψ_bar : E₀ ⧸ D₀ →+ H₀ ⧸ D := QuotientAddGroup.lift D₀ ψ₀ h_ker
  let F : (E₀ ⧸ D₀) × Fin 4 → H₀ ⧸ D :=
    fun x => ψ_bar x.1 + QuotientAddGroup.mk (τ_H₀ x.2)
  have hF_mk : ∀ (p : E₀) (i : Fin 4),
      F (QuotientAddGroup.mk p, i) = QuotientAddGroup.mk (ι_E p + τ_H₀ i) := by
    intro p i
    rfl
  have hF_surj : Function.Surjective F := by
    intro y
    refine QuotientAddGroup.induction_on y fun h => ?_
    rcases h.2 with ⟨e, he, t, ht, het⟩
    obtain ⟨i, rfl⟩ := hτ_surj t ht
    let p : E₀ := ⟨e, he⟩
    refine ⟨(QuotientAddGroup.mk p, i), ?_⟩
    rw [hF_mk]
    congr 1
    exact Subtype.ext het
  have hF_inj : Function.Injective F := by
    rintro ⟨x₁, i₁⟩ ⟨x₂, i₂⟩ hF_eq
    refine QuotientAddGroup.induction_on x₁ (fun p₁ => ?_) hF_eq
    refine QuotientAddGroup.induction_on x₂ (fun p₂ hF_eq => ?_)
    rw [hF_mk, hF_mk, QuotientAddGroup.eq] at hF_eq
    rcases hF_eq with ⟨h₀, hh₀⟩
    rcases h₀.2 with ⟨e₀, he₀, t₀, ht₀, het₀⟩
    have hh₀_val : (h₀ + h₀ : H₀).1 = (-(ι_E p₁ + τ_H₀ i₁) + (ι_E p₂ + τ_H₀ i₂) : H₀).1 :=
      congr_arg Subtype.val hh₀
    change (h₀.1 + h₀.1 : G) = -(p₁.1 + τ_G i₁) + (p₂.1 + τ_G i₂) at hh₀_val
    rw [← het₀] at hh₀_val
    have h2e₀ : (e₀ + t₀) + (e₀ + t₀) = e₀ + e₀ := by
      calc (e₀ + t₀) + (e₀ + t₀) = (e₀ + e₀) + (t₀ + t₀) := by abel
        _ = (e₀ + e₀) + 0 := by rw [ht₀]
        _ = e₀ + e₀ := add_zero _
    rw [h2e₀] at hh₀_val
    have hτ_diff_eq : -τ_G i₁ + τ_G i₂ = (e₀ + e₀) - (-p₁.1 + p₂.1) := by
      calc -τ_G i₁ + τ_G i₂ = (-(p₁.1 + τ_G i₁) + (p₂.1 + τ_G i₂)) - (-p₁.1 + p₂.1) := by abel
        _ = (e₀ + e₀) - (-p₁.1 + p₂.1) := by rw [← hh₀_val]
    have hτ_diff_mem : -τ_G i₁ + τ_G i₂ ∈ E₀ := by
      rw [hτ_diff_eq]
      exact E₀.sub_mem (E₀.add_mem he₀ he₀) (E₀.add_mem (E₀.neg_mem p₁.2) p₂.2)
    have hτ_diff_tors : (-τ_G i₁ + τ_G i₂) + (-τ_G i₁ + τ_G i₂) = 0 := by
      calc (-τ_G i₁ + τ_G i₂) + (-τ_G i₁ + τ_G i₂)
          = -(τ_G i₁ + τ_G i₁) + (τ_G i₂ + τ_G i₂) := by abel
        _ = -0 + 0 := by rw [hτ_tors i₁, hτ_tors i₂]
        _ = 0 := by abel
    have hτ_diff_zero : -τ_G i₁ + τ_G i₂ = 0 :=
      hE₀_tors (-τ_G i₁ + τ_G i₂) hτ_diff_mem hτ_diff_tors
    have hτ_eq : τ_G i₁ = τ_G i₂ := by
      calc τ_G i₁ = τ_G i₁ + (-τ_G i₁ + τ_G i₂) := by rw [hτ_diff_zero, add_zero]
        _ = τ_G i₂ := by abel
    have hi_eq : i₁ = i₂ := hτ_inj i₁ i₂ hτ_eq
    have hp_diff : e₀ + e₀ = -p₁.1 + p₂.1 := by
      calc e₀ + e₀ = -(p₁.1 + τ_G i₁) + (p₂.1 + τ_G i₂) := hh₀_val
        _ = (-p₁.1 + p₂.1) + (-τ_G i₁ + τ_G i₂) := by abel
        _ = (-p₁.1 + p₂.1) + 0 := by rw [hτ_diff_zero]
        _ = -p₁.1 + p₂.1 := add_zero _
    have hp_eq : (QuotientAddGroup.mk p₁ : E₀ ⧸ D₀) = QuotientAddGroup.mk p₂ := by
      rw [QuotientAddGroup.eq]
      exact ⟨⟨e₀, he₀⟩, Subtype.ext hp_diff⟩
    exact Prod.ext hp_eq hi_eq
  have hcard_H₀ : Nat.card (H₀ ⧸ D) = 2 ^ (2 + kv) := by
    calc Nat.card (H₀ ⧸ D)
        = Nat.card ((E₀ ⧸ D₀) × Fin 4) :=
          Nat.card_congr (Equiv.ofBijective F ⟨hF_inj, hF_surj⟩).symm
      _ = Nat.card (E₀ ⧸ D₀) * Nat.card (Fin 4) := Nat.card_prod (E₀ ⧸ D₀) (Fin 4)
      _ = 2 ^ kv * 4 := by rw [hcard_E₀, Nat.card_fin]
      _ = 2 ^ (2 + kv) := by ring
  exact ⟨H₀, D, hD, htors, hE₀_sub, hnot_mem, le_of_eq hcard_H₀.symm⟩

theorem threeRootsCurve_two_torsion_and_sub_formulas {F : Type u} [Field F] [DecidableEq F]
    (hchar : (2 : F) ≠ 0) (e₁ e₂ e₃ : F)
    (he₁₂ : e₁ ≠ e₂) (he₁₃ : e₁ ≠ e₃) (he₂₃ : e₂ ≠ e₃) :
    (∀ x y : F,
      (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x y →
      y ^ 2 = (x - e₁) * (x - e₂) * (x - e₃)) ∧
    (∃ P₁ P₂ P₃ : (threeRootsCurve e₁ e₂ e₃).toAffine.Point,
      (P₁ ≠ 0 ∧ P₂ ≠ 0 ∧ P₃ ≠ 0 ∧ P₁ ≠ P₂ ∧ P₁ ≠ P₃ ∧ P₂ ≠ P₃) ∧
      (∀ P : (threeRootsCurve e₁ e₂ e₃).toAffine.Point,
        P + P = 0 ↔ P = 0 ∨ P = P₁ ∨ P = P₂ ∨ P = P₃) ∧
      (∀ (x y : F) (h : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x y),
        WeierstrassCurve.Affine.Point.some h + WeierstrassCurve.Affine.Point.some h ≠ 0 →
        (∃ (x₁' y₁' : F) (h₁' : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x₁' y₁'),
          WeierstrassCurve.Affine.Point.some h - P₁ = WeierstrassCurve.Affine.Point.some h₁' ∧
          (x₁' - e₁) * (x - e₁) = (e₁ - e₂) * (e₁ - e₃)) ∧
        (∃ (x₂' y₂' : F) (h₂' : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x₂' y₂'),
          WeierstrassCurve.Affine.Point.some h - P₂ = WeierstrassCurve.Affine.Point.some h₂' ∧
          (x₂' - e₂) * (x - e₂) = (e₂ - e₁) * (e₂ - e₃)) ∧
        (∃ (x₃' y₃' : F) (h₃' : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x₃' y₃'),
          WeierstrassCurve.Affine.Point.some h - P₃ = WeierstrassCurve.Affine.Point.some h₃' ∧
          (x₃' - e₃) * (x - e₃) = (e₃ - e₁) * (e₃ - e₂)))) ∧
    (∀ (x₁ y₁ x₂ y₂ : F)
      (h₁ : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x₁ y₁)
      (h₂ : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x₂ y₂),
      (x₁ = x₂ → y₁ + y₂ ≠ 0 →
        WeierstrassCurve.Affine.Point.some h₁ = WeierstrassCurve.Affine.Point.some h₂) ∧
      (x₁ ≠ x₂ →
        ∃ (x₃ y₃ : F) (h₃ : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x₃ y₃),
          WeierstrassCurve.Affine.Point.some h₁ - WeierstrassCurve.Affine.Point.some h₂ =
            WeierstrassCurve.Affine.Point.some h₃ ∧
          x₃ - e₁ = ((y₁ + y₂) / (x₁ - x₂)) ^ 2 + (e₂ + e₃ - x₁ - x₂))) :=
by
  let W := (threeRootsCurve e₁ e₂ e₃).toAffine
  have h_negY : ∀ x y : F, W.negY x y = -y := by
    intro x y
    dsimp [W, threeRootsCurve, WeierstrassCurve.Affine.negY]
    ring
  have h_eq_roots : ∀ x y : F, W.Equation x y ↔ y ^ 2 = (x - e₁) * (x - e₂) * (x - e₃) := by
    intro x y
    rw [WeierstrassCurve.Affine.equation_iff]
    dsimp [W, threeRootsCurve]
    constructor <;> intro h <;> linear_combination h
  have h_two_tors_iff : ∀ (x y : F) (h : W.Nonsingular x y),
      WeierstrassCurve.Affine.Point.some h + WeierstrassCurve.Affine.Point.some h = 0 ↔ y = 0 := by
    intro x y h
    constructor
    · intro h2P
      by_contra hy
      have hy_neg : y ≠ W.negY x y := by
        rw [h_negY x y]
        intro h_eq
        exact mul_ne_zero hchar hy (by linear_combination h_eq)
      rw [WeierstrassCurve.Affine.Point.add_of_Y_ne hy_neg] at h2P
      nomatch h2P
    · intro hy
      have hy_neg : y = W.negY x y := by
        rw [h_negY x y, hy, neg_zero]
      exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy_neg
  have hns_eq : ∀ x y : F, W.Nonsingular x y → y ^ 2 = (x - e₁) * (x - e₂) * (x - e₃) := by
    intro x y h
    exact (h_eq_roots x y).mp h.1
  have hns₁ : W.Nonsingular e₁ 0 := by
    rw [WeierstrassCurve.Affine.nonsingular_iff, h_eq_roots e₁ 0]
    refine ⟨by ring, Or.inl ?_⟩
    intro h_eq
    dsimp [W, threeRootsCurve] at h_eq
    exact mul_ne_zero (sub_ne_zero.mpr he₁₂) (sub_ne_zero.mpr he₁₃) (by linear_combination -h_eq)
  have hns₂ : W.Nonsingular e₂ 0 := by
    rw [WeierstrassCurve.Affine.nonsingular_iff, h_eq_roots e₂ 0]
    refine ⟨by ring, Or.inl ?_⟩
    intro h_eq
    dsimp [W, threeRootsCurve] at h_eq
    exact mul_ne_zero (sub_ne_zero.mpr he₁₂.symm) (sub_ne_zero.mpr he₂₃) (by linear_combination -h_eq)
  have hns₃ : W.Nonsingular e₃ 0 := by
    rw [WeierstrassCurve.Affine.nonsingular_iff, h_eq_roots e₃ 0]
    refine ⟨by ring, Or.inl ?_⟩
    intro h_eq
    dsimp [W, threeRootsCurve] at h_eq
    exact mul_ne_zero (sub_ne_zero.mpr he₁₃.symm) (sub_ne_zero.mpr he₂₃.symm) (by linear_combination -h_eq)
  let P₁ : W.Point := WeierstrassCurve.Affine.Point.some hns₁
  let P₂ : W.Point := WeierstrassCurve.Affine.Point.some hns₂
  let P₃ : W.Point := WeierstrassCurve.Affine.Point.some hns₃
  have hsub : ∀ (x₁ y₁ x₂ y₂ : F) (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂),
      (x₁ = x₂ → y₁ + y₂ ≠ 0 →
        WeierstrassCurve.Affine.Point.some h₁ = WeierstrassCurve.Affine.Point.some h₂) ∧
      (x₁ ≠ x₂ →
        ∃ (x₃ y₃ : F) (h₃ : W.Nonsingular x₃ y₃),
          WeierstrassCurve.Affine.Point.some h₁ - WeierstrassCurve.Affine.Point.some h₂ =
            WeierstrassCurve.Affine.Point.some h₃ ∧
          x₃ - e₁ = ((y₁ + y₂) / (x₁ - x₂)) ^ 2 + (e₂ + e₃ - x₁ - x₂)) := by
    intro x₁ y₁ x₂ y₂ h₁ h₂
    constructor
    · intro hx hy_sum
      have hy_sq : y₁ ^ 2 = y₂ ^ 2 := by
        rw [hns_eq x₁ y₁ h₁, hns_eq x₂ y₂ h₂, hx]
      have hy_eq : y₁ = y₂ := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy_sq with h | h
        · exact h
        · exfalso
          exact hy_sum (by linear_combination h)
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hx, hy_eq⟩
    · intro hx
      refine ⟨_, _,
        WeierstrassCurve.Affine.nonsingular_add h₁ ((W.nonsingular_neg x₂ y₂).mpr h₂)
          (fun h => hx h.1),
        by rw [sub_eq_add_neg, WeierstrassCurve.Affine.Point.neg_some,
               WeierstrassCurve.Affine.Point.add_of_X_ne hx],
        ?_⟩
      rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
      dsimp [W, threeRootsCurve, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY]
      ring
  refine ⟨hns_eq, ⟨P₁, P₂, P₃, ?_, ?_, ?_⟩, hsub⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h; nomatch h
    · intro h; nomatch h
    · intro h; nomatch h
    · intro h
      rw [WeierstrassCurve.Affine.Point.some.injEq] at h
      exact he₁₂ h.1
    · intro h
      rw [WeierstrassCurve.Affine.Point.some.injEq] at h
      exact he₁₃ h.1
    · intro h
      rw [WeierstrassCurve.Affine.Point.some.injEq] at h
      exact he₂₃ h.1
  · intro P
    cases P with
    | zero =>
      change (0 : W.Point) + 0 = 0 ↔ (0 : W.Point) = 0 ∨ (0 : W.Point) = P₁ ∨ (0 : W.Point) = P₂ ∨ (0 : W.Point) = P₃
      simp
    | @some x y h =>
      rw [h_two_tors_iff x y h]
      constructor
      · intro hy
        have heq := hns_eq x y h
        rw [hy, zero_pow (by decide)] at heq
        rcases mul_eq_zero.mp heq.symm with h12 | h3
        · rcases mul_eq_zero.mp h12 with h1 | h2
          · right; left
            rw [WeierstrassCurve.Affine.Point.some.injEq]
            exact ⟨sub_eq_zero.mp h1, hy⟩
          · right; right; left
            rw [WeierstrassCurve.Affine.Point.some.injEq]
            exact ⟨sub_eq_zero.mp h2, hy⟩
        · right; right; right
          rw [WeierstrassCurve.Affine.Point.some.injEq]
          exact ⟨sub_eq_zero.mp h3, hy⟩
      · rintro (h0 | h1 | h2 | h3)
        · nomatch h0
        · rw [WeierstrassCurve.Affine.Point.some.injEq] at h1
          exact h1.2
        · rw [WeierstrassCurve.Affine.Point.some.injEq] at h2
          exact h2.2
        · rw [WeierstrassCurve.Affine.Point.some.injEq] at h3
          exact h3.2
  · intro x y h h2P
    have hy : y ≠ 0 := mt (h_two_tors_iff x y h).mpr h2P
    have heq : y ^ 2 = (x - e₁) * (x - e₂) * (x - e₃) := hns_eq x y h
    have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
    have hxe₁ : x ≠ e₁ := by
      rintro rfl
      exact hy2 (by linear_combination heq)
    have hxe₂ : x ≠ e₂ := by
      rintro rfl
      exact hy2 (by linear_combination heq)
    have hxe₃ : x ≠ e₃ := by
      rintro rfl
      exact hy2 (by linear_combination heq)
    obtain ⟨x₁', y₁', h₁', hsub₁, hx₁'⟩ := (hsub x y e₁ 0 h hns₁).2 hxe₁
    obtain ⟨x₂', y₂', h₂', hsub₂, hx₂'⟩ := (hsub x y e₂ 0 h hns₂).2 hxe₂
    obtain ⟨x₃', y₃', h₃', hsub₃, hx₃'⟩ := (hsub x y e₃ 0 h hns₃).2 hxe₃
    refine ⟨⟨x₁', y₁', h₁', hsub₁, ?_⟩, ⟨x₂', y₂', h₂', hsub₂, ?_⟩, ⟨x₃', y₃', h₃', hsub₃, ?_⟩⟩
    · rw [hx₁']
      field_simp [sub_ne_zero.mpr hxe₁]
      linear_combination heq
    · have hx₂'' : x₂' - e₂ = ((y + 0) / (x - e₂)) ^ 2 + (e₁ + e₃ - x - e₂) := by
        linear_combination hx₂'
      rw [hx₂'']
      field_simp [sub_ne_zero.mpr hxe₂]
      linear_combination heq
    · have hx₃'' : x₃' - e₃ = ((y + 0) / (x - e₃)) ^ 2 + (e₁ + e₂ - x - e₃) := by
        linear_combination hx₃'
      rw [hx₃'']
      field_simp [sub_ne_zero.mpr hxe₃]
      linear_combination heq

theorem lutz_outside_ultrametric_bounds {K : Type u} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (e₁ e₂ e₃ : v.adicCompletion K)
    (he₁₂ : e₁ ≠ e₂) (he₁₃ : e₁ ≠ e₃) (he₂₃ : e₂ ≠ e₃)
    (ev m₀ : ℕ)
    (hev : Valued.v (2 : v.adicCompletion K) = WithZero.exp (-(ev : ℤ)))
    (hm₀_pos : 0 < m₀)
    (hα_lt : Valued.v (e₁ - e₂) < WithZero.exp (2 * (m₀ : ℤ)))
    (hβ_lt : Valued.v (e₁ - e₃) < WithZero.exp (2 * (m₀ : ℤ))) :
    ∃ N : ℕ,
      (∀ x y x₁' x₂' x₃' : v.adicCompletion K,
        y ^ 2 = (x - e₁) * (x - e₂) * (x - e₃) →
        Valued.v (x - e₁) < WithZero.exp (2 * (m₀ : ℤ)) →
        (x₁' - e₁) * (x - e₁) = (e₁ - e₂) * (e₁ - e₃) →
        Valued.v (x₁' - e₁) < WithZero.exp (2 * (m₀ : ℤ)) →
        (x₂' - e₂) * (x - e₂) = (e₂ - e₁) * (e₂ - e₃) →
        Valued.v (x₂' - e₁) < WithZero.exp (2 * (m₀ : ℤ)) →
        (x₃' - e₃) * (x - e₃) = (e₃ - e₁) * (e₃ - e₂) →
        Valued.v (x₃' - e₁) < WithZero.exp (2 * (m₀ : ℤ)) →
        Valued.v (x - e₁) ≤ WithZero.exp (3 * (m₀ : ℤ)) ∧
        Valued.v y ≤ WithZero.exp (3 * (m₀ : ℤ)) ∧
        WithZero.exp ((m₀ : ℤ) + 1 - (N : ℤ)) ≤ Valued.v (2 * y)) ∧
      (∀ x₁ y₁ x₂ y₂ : v.adicCompletion K,
        Valued.v (x₁ - e₁) < WithZero.exp (2 * (m₀ : ℤ)) →
        Valued.v (x₂ - e₁) < WithZero.exp (2 * (m₀ : ℤ)) →
        WithZero.exp ((m₀ : ℤ) + 1 - (N : ℤ)) ≤ Valued.v (2 * y₁) →
        Valued.v ((x₁ - e₁) - (x₂ - e₁)) ≤ WithZero.exp (-(N : ℤ)) →
        Valued.v (y₁ - y₂) ≤ WithZero.exp (-(N : ℤ)) →
        y₁ + y₂ ≠ 0 ∧
        (x₁ ≠ x₂ →
          WithZero.exp (2 * (m₀ : ℤ)) ≤
            Valued.v (((y₁ + y₂) / (x₁ - x₂)) ^ 2 + (e₂ + e₃ - x₁ - x₂)))) :=
by
  let val : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ)) := Valued.v
  have exp_sq : ∀ (a : ℤ), (WithZero.exp a) ^ 2 = WithZero.exp (2 * a) := by
    intro a
    rw [sq, ← WithZero.exp_add, two_mul]
  have le_of_sq_le_sq : ∀ {a b : WithZero (Multiplicative ℤ)}, a ^ 2 ≤ b ^ 2 → a ≤ b := by
    intro a b h
    by_cases ha : a = 0
    · rw [ha]
      exact zero_le'
    · have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
      have hb : b ≠ 0 := by
        intro hb0
        have hb2 : b ^ 2 = 0 := by rw [hb0, zero_pow two_ne_zero]
        rw [hb2] at h
        exact ha2 (le_antisymm h zero_le')
      have h_ea : a = WithZero.exp a.log := (WithZero.exp_log ha).symm
      have h_eb : b = WithZero.exp b.log := (WithZero.exp_log hb).symm
      rw [h_ea, h_eb] at h ⊢
      rw [exp_sq, exp_sq, WithZero.exp_le_exp] at h
      rw [WithZero.exp_le_exp]
      omega
  have val_mul_le_exp : ∀ {x y : v.adicCompletion K} {a b c : ℤ},
      val x ≤ WithZero.exp a → val y ≤ WithZero.exp b → a + b ≤ c →
      val (x * y) ≤ WithZero.exp c := by
    intro x y a b c hx hy h
    rw [val.map_mul]
    refine le_trans (mul_le_mul' hx hy) ?_
    rw [← WithZero.exp_add, WithZero.exp_le_exp]
    exact h
  have val_add_le_exp : ∀ {x y : v.adicCompletion K} {c : ℤ},
      val x ≤ WithZero.exp c → val y ≤ WithZero.exp c →
      val (x + y) ≤ WithZero.exp c :=
    fun hx hy => le_trans (val.map_add _ _) (max_le hx hy)
  let Δ₀ : v.adicCompletion K := (e₁ - e₂) * (e₁ - e₃) * (e₂ - e₃)
  have hΔ₀_ne : Δ₀ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr he₁₂) (sub_ne_zero.mpr he₁₃))
      (sub_ne_zero.mpr he₂₃)
  have hval_Δ₀_ne : val Δ₀ ≠ 0 := (val.ne_zero_iff).mpr hΔ₀_ne
  let d₀ : ℤ := (val Δ₀).log
  let C₀ : ℕ := Int.toNat (-d₀)
  have hΔ₀_eq : val Δ₀ = WithZero.exp d₀ := (WithZero.exp_log hval_Δ₀_ne).symm
  have hΔ₀_ge : WithZero.exp (-(C₀ : ℤ)) ≤ val Δ₀ := by
    rw [hΔ₀_eq, WithZero.exp_le_exp]
    dsimp [C₀]
    omega
  let N : ℕ := C₀ + 4 * m₀ + ev + 1
  have hα_le : val (e₁ - e₂) ≤ WithZero.exp (2 * (m₀ : ℤ)) := le_of_lt hα_lt
  have hβ_le : val (e₁ - e₃) ≤ WithZero.exp (2 * (m₀ : ℤ)) := le_of_lt hβ_lt
  refine ⟨N, ?_, ?_⟩
  · intro x y x₁' x₂' x₃' h_curve hx_lt h₁ hx₁'_lt h₂ hx₂'_lt h₃ hx₃'_lt
    have hx_le : val (x - e₁) ≤ WithZero.exp (2 * (m₀ : ℤ)) := le_of_lt hx_lt
    have hx₁'_le : val (x₁' - e₁) ≤ WithZero.exp (2 * (m₀ : ℤ)) := le_of_lt hx₁'_lt
    have hx₂'_le : val (x₂' - e₁) ≤ WithZero.exp (2 * (m₀ : ℤ)) := le_of_lt hx₂'_lt
    have hx₃'_le : val (x₃' - e₁) ≤ WithZero.exp (2 * (m₀ : ℤ)) := le_of_lt hx₃'_lt
    have hb_x : val (x - e₁) ≤ WithZero.exp (3 * (m₀ : ℤ)) :=
      le_trans hx_le (WithZero.exp_le_exp.mpr (by omega))
    have hx2_eq : x - e₂ = (x - e₁) + (e₁ - e₂) := by ring
    have hx3_eq : x - e₃ = (x - e₁) + (e₁ - e₃) := by ring
    have hx2_le : val (x - e₂) ≤ WithZero.exp (2 * (m₀ : ℤ)) := by
      rw [hx2_eq]; exact val_add_le_exp hx_le hα_le
    have hx3_le : val (x - e₃) ≤ WithZero.exp (2 * (m₀ : ℤ)) := by
      rw [hx3_eq]; exact val_add_le_exp hx_le hβ_le
    have hy2_le : val y ^ 2 ≤ (WithZero.exp (3 * (m₀ : ℤ))) ^ 2 := by
      rw [← val.map_pow, h_curve, exp_sq]
      refine val_mul_le_exp (val_mul_le_exp hx_le hx2_le (by rfl)) hx3_le ?_
      omega
    have hb_y : val y ≤ WithZero.exp (3 * (m₀ : ℤ)) := le_of_sq_le_sq hy2_le
    have hx₂'2_eq : x₂' - e₂ = (x₂' - e₁) + (e₁ - e₂) := by ring
    have hx₃'3_eq : x₃' - e₃ = (x₃' - e₁) + (e₁ - e₃) := by ring
    have hx₂'2_le : val (x₂' - e₂) ≤ WithZero.exp (2 * (m₀ : ℤ)) := by
      rw [hx₂'2_eq]; exact val_add_le_exp hx₂'_le hα_le
    have hx₃'3_le : val (x₃' - e₃) ≤ WithZero.exp (2 * (m₀ : ℤ)) := by
      rw [hx₃'3_eq]; exact val_add_le_exp hx₃'_le hβ_le
    have hx'_prod_le : val ((x₁' - e₁) * (x₂' - e₂) * (x₃' - e₃)) ≤
        (WithZero.exp (3 * (m₀ : ℤ))) ^ 2 := by
      rw [exp_sq]
      refine val_mul_le_exp (val_mul_le_exp hx₁'_le hx₂'2_le (by rfl)) hx₃'3_le ?_
      omega
    have h_prod_id : (x₁' - e₁) * (x₂' - e₂) * (x₃' - e₃) * y ^ 2 = -Δ₀ ^ 2 := by
      dsimp [Δ₀]
      linear_combination
        (x₁' - e₁) * (x₂' - e₂) * (x₃' - e₃) * h_curve +
        (x₂' - e₂) * (x₃' - e₃) * (x - e₂) * (x - e₃) * h₁ +
        (e₁ - e₂) * (e₁ - e₃) * (x₃' - e₃) * (x - e₃) * h₂ +
        (e₁ - e₂) * (e₁ - e₃) * (e₂ - e₁) * (e₂ - e₃) * h₃
    have h_val_sq : val Δ₀ ^ 2 ≤ (WithZero.exp (3 * (m₀ : ℤ)) * val y) ^ 2 := by
      calc val Δ₀ ^ 2 = val (-Δ₀ ^ 2) := by rw [val.map_neg, val.map_pow]
        _ = val ((x₁' - e₁) * (x₂' - e₂) * (x₃' - e₃) * y ^ 2) := by rw [← h_prod_id]
        _ = val ((x₁' - e₁) * (x₂' - e₂) * (x₃' - e₃)) * val y ^ 2 := by
            rw [val.map_mul, val.map_pow]
        _ ≤ (WithZero.exp (3 * (m₀ : ℤ))) ^ 2 * val y ^ 2 :=
            mul_le_mul' hx'_prod_le le_rfl
        _ = (WithZero.exp (3 * (m₀ : ℤ)) * val y) ^ 2 := (mul_pow _ _ 2).symm
    have hy_mul_ge : WithZero.exp (-(C₀ : ℤ)) ≤ WithZero.exp (3 * (m₀ : ℤ)) * val y :=
      le_trans hΔ₀_ge (le_of_sq_le_sq h_val_sq)
    have hval_y_ne : val y ≠ 0 := by
      intro hy0
      rw [hy0, mul_zero] at hy_mul_ge
      exact WithZero.exp_ne_zero (le_antisymm hy_mul_ge zero_le')
    set ky : ℤ := (val y).log
    have hky_eq : val y = WithZero.exp ky := (WithZero.exp_log hval_y_ne).symm
    have hky_ge : -(C₀ : ℤ) ≤ 3 * (m₀ : ℤ) + ky := by
      rw [hky_eq, ← WithZero.exp_add, WithZero.exp_le_exp] at hy_mul_ge
      exact hy_mul_ge
    have hb_2y : WithZero.exp ((m₀ : ℤ) + 1 - (N : ℤ)) ≤ val (2 * y) := by
      rw [val.map_mul, hev, hky_eq, ← WithZero.exp_add, WithZero.exp_le_exp]
      dsimp [N]
      omega
    exact ⟨hb_x, hb_y, hb_2y⟩
  · intro x₁ y₁ x₂ y₂ hx₁_lt hx₂_lt h2y₁ hdx hdy
    have hdy_lt : val (y₁ - y₂) < val (2 * y₁) := by
      refine lt_of_le_of_lt hdy (lt_of_lt_of_le ?_ h2y₁)
      rw [WithZero.exp_lt_exp]
      omega
    have hsy_eq_sub : y₁ + y₂ = 2 * y₁ - (y₁ - y₂) := by ring
    have hsy_val : val (y₁ + y₂) = val (2 * y₁) := by
      rw [hsy_eq_sub]
      exact val.map_sub_eq_of_lt_left hdy_lt
    have hsy_ge : WithZero.exp ((m₀ : ℤ) + 1 - (N : ℤ)) ≤ val (y₁ + y₂) := by
      rw [hsy_val]
      exact h2y₁
    have hval_sy_ne : val (y₁ + y₂) ≠ 0 := by
      intro h0
      rw [h0] at hsy_ge
      exact WithZero.exp_ne_zero (le_antisymm hsy_ge zero_le')
    have hsy_ne : y₁ + y₂ ≠ 0 := (val.ne_zero_iff).mp hval_sy_ne
    refine ⟨hsy_ne, ?_⟩
    intro hx_ne
    have hdx_sub : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx_ne
    have hval_dx_ne : val (x₁ - x₂) ≠ 0 := (val.ne_zero_iff).mpr hdx_sub
    have hdx_eq : (x₁ - e₁) - (x₂ - e₁) = x₁ - x₂ := by ring
    have hdx' : val (x₁ - x₂) ≤ WithZero.exp (-(N : ℤ)) := by
      rw [← hdx_eq]
      exact hdx
    set ksy : ℤ := (val (y₁ + y₂)).log
    set kdx : ℤ := (val (x₁ - x₂)).log
    have hksy_eq : val (y₁ + y₂) = WithZero.exp ksy := (WithZero.exp_log hval_sy_ne).symm
    have hkdx_eq : val (x₁ - x₂) = WithZero.exp kdx := (WithZero.exp_log hval_dx_ne).symm
    have hksy_ge : (m₀ : ℤ) + 1 - (N : ℤ) ≤ ksy := by
      rw [hksy_eq, WithZero.exp_le_exp] at hsy_ge
      exact hsy_ge
    have hkdx_le : kdx ≤ -(N : ℤ) := by
      rw [hkdx_eq, WithZero.exp_le_exp] at hdx'
      exact hdx'
    have h_slope_sq : WithZero.exp (2 * (m₀ : ℤ)) ≤ val (((y₁ + y₂) / (x₁ - x₂)) ^ 2) := by
      rw [val.map_pow, val.map_div, hksy_eq, hkdx_eq, ← WithZero.exp_sub, exp_sq,
          WithZero.exp_le_exp]
      omega
    have h_rem_eq : e₂ + e₃ - x₁ - x₂ = -(((x₁ - e₁) + (x₂ - e₁)) + ((e₁ - e₂) + (e₁ - e₃))) := by
      ring
    have h_x12_lt : val ((x₁ - e₁) + (x₂ - e₁)) < WithZero.exp (2 * (m₀ : ℤ)) :=
      lt_of_le_of_lt (val.map_add _ _) (max_lt hx₁_lt hx₂_lt)
    have h_e23_lt : val ((e₁ - e₂) + (e₁ - e₃)) < WithZero.exp (2 * (m₀ : ℤ)) :=
      lt_of_le_of_lt (val.map_add _ _) (max_lt hα_lt hβ_lt)
    have h_rem_lt : val (e₂ + e₃ - x₁ - x₂) < WithZero.exp (2 * (m₀ : ℤ)) := by
      rw [h_rem_eq, val.map_neg]
      exact lt_of_le_of_lt (val.map_add _ _) (max_lt h_x12_lt h_e23_lt)
    have h_rem_lt_slope : val (e₂ + e₃ - x₁ - x₂) < val (((y₁ + y₂) / (x₁ - x₂)) ^ 2) :=
      lt_of_lt_of_le h_rem_lt h_slope_sq
    rw [val.map_add_eq_of_lt_left h_rem_lt_slope]
    exact h_slope_sq

theorem adicCompletion_bounded_ball_finite_approx {K : Type u} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (B N : ℕ) :
    Finite (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (B + N)) ∧
    ∃ approx : v.adicCompletion K → (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (B + N)),
      ∀ z₁ z₂ : v.adicCompletion K,
        Valued.v z₁ ≤ WithZero.exp (B : ℤ) →
        Valued.v z₂ ≤ WithZero.exp (B : ℤ) →
        approx z₁ = approx z₂ →
        Valued.v (z₁ - z₂) ≤ WithZero.exp (-(N : ℤ)) :=
by
  refine ⟨Ideal.finiteQuotientOfFreeOfNeBot (v.asIdeal ^ (B + N)) (pow_ne_zero (B + N) v.ne_bot), ?_⟩
  have h_approx_K : ∀ (a : K), IsDedekindDomain.HeightOneSpectrum.valuation K v a ≤ 1 →
      ∀ (M : ℕ), ∃ r : NumberField.RingOfIntegers K,
        IsDedekindDomain.HeightOneSpectrum.valuation K v
          (a - algebraMap (NumberField.RingOfIntegers K) K r) ≤ WithZero.exp (-(M : ℤ)) := by
    intro a ha M
    obtain ⟨xa, ya, hya, hxya⟩ :=
      IsFractionRing.div_surjective (A := NumberField.RingOfIntegers K) (K := K) a
    have hy0 : ya ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hya
    have hiy : algebraMap (NumberField.RingOfIntegers K) K ya ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hya
    have hstar : a * algebraMap (NumberField.RingOfIntegers K) K ya
        = algebraMap (NumberField.RingOfIntegers K) K xa := by
      rw [← hxya]
      exact div_mul_cancel₀ _ hiy
    obtain ⟨m, hym, hym1, hexpm⟩ :
        ∃ m : ℕ, ya ∈ v.asIdeal ^ m ∧ ya ∉ v.asIdeal ^ (m + 1) ∧
          WithZero.exp (-(m : ℤ)) = v.intValuation ya := by
      have ht0 : v.intValuation ya ≠ 0 :=
        IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero v ya hy0
      have ht1 : v.intValuation ya ≤ 1 :=
        IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v ya
      obtain ⟨k, hk⟩ : ∃ k : ℤ, WithZero.exp k = v.intValuation ya := ⟨_, WithZero.exp_log ht0⟩
      have hkle : k ≤ 0 := by
        have hstep : WithZero.exp k ≤ WithZero.exp (0 : ℤ) := by
          rw [hk, WithZero.exp_zero]; exact ht1
        exact WithZero.exp_le_exp.mp hstep
      have hcast : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      have hexpm : WithZero.exp (-(((-k).toNat : ℕ) : ℤ)) = v.intValuation ya := by
        rw [hcast, neg_neg, hk]
      refine ⟨(-k).toNat, ?_, ?_, hexpm⟩
      · exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya _).mp
          (le_of_eq hexpm.symm)
      · intro hcon
        have hle :=
          (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya
            ((-k).toNat + 1)).mpr hcon
        have he : (-(((-k).toNat + 1 : ℕ) : ℤ)) = k - 1 := by
          rw [Nat.cast_add, Nat.cast_one, hcast]; ring
        rw [he, ← hk] at hle
        have := WithZero.exp_le_exp.mp hle
        omega
    have hivy : v.intValuation ya ≤ WithZero.exp (-(m : ℤ)) :=
      (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v ya m).mpr hym
    have hxm : xa ∈ v.asIdeal ^ m := by
      refine (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v xa m).mp ?_
      have e1 : v.intValuation xa
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K xa) :=
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v xa).symm
      have e2 : v.intValuation ya
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (algebraMap (NumberField.RingOfIntegers K) K ya) :=
        (IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v ya).symm
      calc v.intValuation xa
          = IsDedekindDomain.HeightOneSpectrum.valuation K v
              (a * algebraMap (NumberField.RingOfIntegers K) K ya) := by
            rw [hstar]; exact e1
        _ = IsDedekindDomain.HeightOneSpectrum.valuation K v a *
              IsDedekindDomain.HeightOneSpectrum.valuation K v
                (algebraMap (NumberField.RingOfIntegers K) K ya) := Valuation.map_mul _ _ _
        _ ≤ 1 * IsDedekindDomain.HeightOneSpectrum.valuation K v
                (algebraMap (NumberField.RingOfIntegers K) K ya) := mul_le_mul_left ha _
        _ = v.intValuation ya := by rw [one_mul, ← e2]
        _ ≤ WithZero.exp (-(m : ℤ)) := hivy
    have hPprime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
    have hJdvd : (Ideal.span {ya} ⊔ v.asIdeal ^ (m + M)) ∣ v.asIdeal ^ (m + M) :=
      Ideal.dvd_iff_le.mpr le_sup_right
    obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow hPprime (m + M)).mp hJdvd
    have hJ : Ideal.span {ya} ⊔ v.asIdeal ^ (m + M) = v.asIdeal ^ i := associated_iff_eq.mp hassoc
    have hyJ : ya ∈ v.asIdeal ^ i := by
      rw [← hJ]
      exact Ideal.dvd_span_singleton.mp (Ideal.dvd_iff_le.mpr le_sup_left)
    have him : i ≤ m := by
      by_contra hcon
      have hle : m + 1 ≤ i := by omega
      exact hym1 (Ideal.pow_le_pow_right hle hyJ)
    have hxJ : xa ∈ Ideal.span {ya} ⊔ v.asIdeal ^ (m + M) := by
      rw [hJ]
      exact Ideal.pow_le_pow_right him hxm
    obtain ⟨p, hp, w, hw, hpw⟩ := Submodule.mem_sup.mp hxJ
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hp
    refine ⟨r, ?_⟩
    have hxrw : xa = r * ya + w := by rw [← hpw, hr]
    have key : (a - algebraMap (NumberField.RingOfIntegers K) K r)
        * algebraMap (NumberField.RingOfIntegers K) K ya
        = algebraMap (NumberField.RingOfIntegers K) K w := by
      have h1 : algebraMap (NumberField.RingOfIntegers K) K xa
          = algebraMap (NumberField.RingOfIntegers K) K r
              * algebraMap (NumberField.RingOfIntegers K) K ya
            + algebraMap (NumberField.RingOfIntegers K) K w := by
        rw [hxrw, map_add, map_mul]
      rw [sub_mul, hstar, h1]; ring
    have hV : IsDedekindDomain.HeightOneSpectrum.valuation K v
          (a - algebraMap (NumberField.RingOfIntegers K) K r) * v.intValuation ya
        = v.intValuation w := by
      rw [← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v ya,
        ← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v w,
        ← Valuation.map_mul, key]
    have hwb : v.intValuation w ≤ WithZero.exp (-((m + M : ℕ) : ℤ)) :=
      (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v w (m + M)).mpr hw
    calc IsDedekindDomain.HeightOneSpectrum.valuation K v
          (a - algebraMap (NumberField.RingOfIntegers K) K r)
        = IsDedekindDomain.HeightOneSpectrum.valuation K v
            (a - algebraMap (NumberField.RingOfIntegers K) K r) *
            (WithZero.exp (-(m : ℤ)) * WithZero.exp (m : ℤ)) := by
          rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, mul_one]
      _ = (IsDedekindDomain.HeightOneSpectrum.valuation K v
            (a - algebraMap (NumberField.RingOfIntegers K) K r) * v.intValuation ya) *
            WithZero.exp (m : ℤ) := by
          rw [← hexpm, mul_assoc]
      _ = v.intValuation w * WithZero.exp (m : ℤ) := by rw [hV]
      _ ≤ WithZero.exp (-((m + M : ℕ) : ℤ)) * WithZero.exp (m : ℤ) :=
          mul_le_mul_left hwb _
      _ = WithZero.exp (-(M : ℤ)) := by
          rw [← WithZero.exp_add]
          congr 1
          push_cast
          ring
  have h_approx_int : ∀ (z : v.adicCompletion K), Valued.v z ≤ 1 → ∀ (M : ℕ),
      ∃ r : NumberField.RingOfIntegers K,
        Valued.v (z - algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K r)) ≤ WithZero.exp (-(M : ℤ)) := by
    intro z hz M
    have hdense : DenseRange (fun y : K => algebraMap K (v.adicCompletion K) y) := by
      letI : Valued K (WithZero (Multiplicative ℤ)) :=
        IsDedekindDomain.HeightOneSpectrum.adicValued (K := K) v
      exact UniformSpace.Completion.denseRange_coe
    let γ : (WithZero (Multiplicative ℤ))ˣ :=
      Units.mk0 (WithZero.exp (-(M : ℤ))) WithZero.exp_ne_zero
    have hnhds : {y : v.adicCompletion K |
        Valued.v (y - z) < (γ : WithZero (Multiplicative ℤ))} ∈ nhds z :=
      Valued.mem_nhds.mpr ⟨γ, subset_rfl⟩
    obtain ⟨u, hu1, k, hk⟩ := mem_closure_iff_nhds.mp (hdense z) _ hnhds
    have hkl : Valued.v (z - algebraMap K (v.adicCompletion K) k) ≤ WithZero.exp (-(M : ℤ)) := by
      dsimp only at hk
      rw [Valuation.map_sub_swap, hk]
      exact le_of_lt hu1
    have hexple : WithZero.exp (-(M : ℤ)) ≤ (1 : WithZero (Multiplicative ℤ)) := by
      rw [← WithZero.exp_zero]
      exact WithZero.exp_le_exp.mpr (by omega)
    have hvc : ∀ x : K, Valued.v (algebraMap K (v.adicCompletion K) x) =
        IsDedekindDomain.HeightOneSpectrum.valuation K v x :=
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v
    have hvk : IsDedekindDomain.HeightOneSpectrum.valuation K v k ≤ 1 := by
      rw [← hvc k]
      have hsplit : algebraMap K (v.adicCompletion K) k =
          z - (z - algebraMap K (v.adicCompletion K) k) := by ring
      rw [hsplit]
      exact le_trans (Valuation.map_sub Valued.v _ _) (max_le hz (le_trans hkl hexple))
    obtain ⟨r, hr⟩ := h_approx_K k hvk M
    refine ⟨r, ?_⟩
    have hsplit2 : z - algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K r) =
        (z - algebraMap K (v.adicCompletion K) k) +
          algebraMap K (v.adicCompletion K)
            (k - algebraMap (NumberField.RingOfIntegers K) K r) := by
      rw [map_sub]; ring
    rw [hsplit2]
    refine le_trans (Valuation.map_add Valued.v _ _) (max_le hkl ?_)
    rw [hvc]
    exact hr
  let ι_hom : NumberField.RingOfIntegers K →+* v.adicCompletion K :=
    (algebraMap K (v.adicCompletion K)).comp (algebraMap (NumberField.RingOfIntegers K) K)
  have hval_int : ∀ r : NumberField.RingOfIntegers K, Valued.v (ι_hom r) = v.intValuation r := by
    intro r
    have h1 : Valued.v (algebraMap K (v.adicCompletion K)
        (algebraMap (NumberField.RingOfIntegers K) K r))
        = IsDedekindDomain.HeightOneSpectrum.valuation K v
            (algebraMap (NumberField.RingOfIntegers K) K r) :=
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v
        (algebraMap (NumberField.RingOfIntegers K) K r)
    change Valued.v (algebraMap K (v.adicCompletion K)
      (algebraMap (NumberField.RingOfIntegers K) K r)) = v.intValuation r
    rw [h1]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := K) v r
  have hval_le_exp_iff : ∀ r : NumberField.RingOfIntegers K,
      Valued.v (ι_hom r) ≤ WithZero.exp (-((B + N : ℕ) : ℤ)) ↔ r ∈ v.asIdeal ^ (B + N) := by
    intro r
    rw [hval_int r]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v r (B + N)
  obtain ⟨π₀, hπ₀⟩ := IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer v
  let ϖ : v.adicCompletion K := ι_hom π₀
  have hϖ_val : Valued.v ϖ = WithZero.exp (-1 : ℤ) :=
    (hval_int π₀).trans hπ₀
  have hϖ_pow_val : Valued.v (ϖ ^ B) = WithZero.exp (-(B : ℤ)) := by
    rw [map_pow, hϖ_val, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hex_approx : ∀ z : v.adicCompletion K,
      Valued.v z ≤ WithZero.exp (B : ℤ) →
      ∃ r : NumberField.RingOfIntegers K,
        Valued.v (z * ϖ ^ B - ι_hom r) ≤ WithZero.exp (-((B + N : ℕ) : ℤ)) := by
    intro z hz
    have hu : Valued.v (z * ϖ ^ B) ≤ 1 := by
      calc Valued.v (z * ϖ ^ B)
          = Valued.v z * Valued.v (ϖ ^ B) := map_mul _ _ _
        _ ≤ WithZero.exp (B : ℤ) * WithZero.exp (-(B : ℤ)) := by
            rw [hϖ_pow_val]
            exact mul_le_mul' hz le_rfl
        _ = 1 := by
            rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
    exact h_approx_int (z * ϖ ^ B) hu (B + N)
  classical
  let approx : v.adicCompletion K → (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (B + N)) :=
    fun z =>
      if hz : Valued.v z ≤ WithZero.exp (B : ℤ) then
        Ideal.Quotient.mk (v.asIdeal ^ (B + N)) (hex_approx z hz).choose
      else 0
  refine ⟨approx, ?_⟩
  intro z₁ z₂ hz₁ hz₂ heq
  let r₁ : NumberField.RingOfIntegers K := (hex_approx z₁ hz₁).choose
  let r₂ : NumberField.RingOfIntegers K := (hex_approx z₂ hz₂).choose
  have hr₁ : Valued.v (z₁ * ϖ ^ B - ι_hom r₁) ≤ WithZero.exp (-((B + N : ℕ) : ℤ)) :=
    (hex_approx z₁ hz₁).choose_spec
  have hr₂ : Valued.v (z₂ * ϖ ^ B - ι_hom r₂) ≤ WithZero.exp (-((B + N : ℕ) : ℤ)) :=
    (hex_approx z₂ hz₂).choose_spec
  have hmk_eq : Ideal.Quotient.mk (v.asIdeal ^ (B + N)) r₁ =
      Ideal.Quotient.mk (v.asIdeal ^ (B + N)) r₂ := by
    dsimp only [approx] at heq
    rw [dif_pos hz₁, dif_pos hz₂] at heq
    exact heq
  have hmem : r₁ - r₂ ∈ v.asIdeal ^ (B + N) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
    exact hmk_eq
  have hr₁₂ : Valued.v (ι_hom (r₁ - r₂)) ≤ WithZero.exp (-((B + N : ℕ) : ℤ)) :=
    (hval_le_exp_iff (r₁ - r₂)).mpr hmem
  have hdiff : Valued.v ((z₁ - z₂) * ϖ ^ B) ≤ WithZero.exp (-((B + N : ℕ) : ℤ)) := by
    have hid : (z₁ - z₂) * ϖ ^ B =
        ((z₁ * ϖ ^ B - ι_hom r₁) - (z₂ * ϖ ^ B - ι_hom r₂)) + ι_hom (r₁ - r₂) := by
      rw [map_sub]
      ring
    rw [hid]
    exact le_trans (Valuation.map_add _ _ _)
      (max_le (le_trans (Valuation.map_sub _ _ _) (max_le hr₁ hr₂)) hr₁₂)
  calc Valued.v (z₁ - z₂)
      = Valued.v (z₁ - z₂) * (WithZero.exp (-(B : ℤ)) * WithZero.exp (B : ℤ)) := by
        rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, mul_one]
    _ = (Valued.v (z₁ - z₂) * Valued.v (ϖ ^ B)) * WithZero.exp (B : ℤ) := by
        rw [hϖ_pow_val, mul_assoc]
    _ = Valued.v ((z₁ - z₂) * ϖ ^ B) * WithZero.exp (B : ℤ) := by
        rw [map_mul]
    _ ≤ WithZero.exp (-((B + N : ℕ) : ℤ)) * WithZero.exp (B : ℤ) :=
        mul_le_mul' hdiff le_rfl
    _ = WithZero.exp (-(N : ℤ)) := by
        rw [← WithZero.exp_add]
        congr 1
        push_cast
        ring

theorem finite_quotient_of_lutz_plus_two_torsion {K : Type u} [Field K] [NumberField K]
    (a₁ a₂ a₃ : K) (h₁₂ : a₁ ≠ a₂) (h₁₃ : a₁ ≠ a₃) (h₂₃ : a₂ ≠ a₃)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    [DecidableEq (v.adicCompletion K)]
    (ev kv m₀ : ℕ)
    (hev : Valued.v (2 : v.adicCompletion K) = WithZero.exp (-(ev : ℤ)))
    (hm₀_pos : 0 < m₀)
    (hα_lt : Valued.v (algebraMap K (v.adicCompletion K) a₁ -
      algebraMap K (v.adicCompletion K) a₂) < WithZero.exp (2 * (m₀ : ℤ)))
    (hβ_lt : Valued.v (algebraMap K (v.adicCompletion K) a₁ -
      algebraMap K (v.adicCompletion K) a₃) < WithZero.exp (2 * (m₀ : ℤ)))
    (E₀ : AddSubgroup (threeRootsCurve
        (algebraMap K (v.adicCompletion K) a₁)
        (algebraMap K (v.adicCompletion K) a₂)
        (algebraMap K (v.adicCompletion K) a₃)).toAffine.Point)
    (hE₀_mem : ∀ x y : v.adicCompletion K,
      ∀ h : (threeRootsCurve
        (algebraMap K (v.adicCompletion K) a₁)
        (algebraMap K (v.adicCompletion K) a₂)
        (algebraMap K (v.adicCompletion K) a₃)).toAffine.Nonsingular x y,
      WeierstrassCurve.Affine.Point.some h ∈ E₀ ↔
        WithZero.exp (2 * (m₀ : ℤ)) ≤
          Valued.v (x - algebraMap K (v.adicCompletion K) a₁))
    (hE₀_tors : ∀ P ∈ E₀, P + P = 0 → P = 0)
    (hE₀_card : ∀ (D₀ : AddSubgroup E₀),
      (∀ p : E₀, p ∈ D₀ ↔ ∃ q : E₀, q + q = p) →
      Nat.card (E₀ ⧸ D₀) = 2 ^ kv) :
    ∃ (H₀ : AddSubgroup (threeRootsCurve
        (algebraMap K (v.adicCompletion K) a₁)
        (algebraMap K (v.adicCompletion K) a₂)
        (algebraMap K (v.adicCompletion K) a₃)).toAffine.Point)
      (D : AddSubgroup H₀),
      (∀ h : H₀, h ∈ D ↔ ∃ h₀ : H₀, h₀ + h₀ = h) ∧
      (∀ P, P + P = 0 → P ∈ H₀) ∧
      Finite ((threeRootsCurve
        (algebraMap K (v.adicCompletion K) a₁)
        (algebraMap K (v.adicCompletion K) a₂)
        (algebraMap K (v.adicCompletion K) a₃)).toAffine.Point ⧸ H₀) ∧
      2 ^ (2 + kv) ≤ Nat.card (H₀ ⧸ D) :=
by
  classical
  let e₁ : v.adicCompletion K := algebraMap K (v.adicCompletion K) a₁
  let e₂ : v.adicCompletion K := algebraMap K (v.adicCompletion K) a₂
  let e₃ : v.adicCompletion K := algebraMap K (v.adicCompletion K) a₃
  have he₁₂ : e₁ ≠ e₂ := (algebraMap K (v.adicCompletion K)).injective.ne h₁₂
  have he₁₃ : e₁ ≠ e₃ := (algebraMap K (v.adicCompletion K)).injective.ne h₁₃
  have he₂₃ : e₂ ≠ e₃ := (algebraMap K (v.adicCompletion K)).injective.ne h₂₃
  have hchar : (2 : v.adicCompletion K) ≠ 0 := by
    intro h2
    have h0 : Valued.v (2 : v.adicCompletion K) = 0 := by rw [h2, map_zero]
    rw [hev] at h0
    exact WithZero.exp_ne_zero h0
  obtain ⟨hns_eq, ⟨P₁, P₂, P₃, hP_ne, hP_tors, hP_trans⟩, hsub⟩ :=
    threeRootsCurve_two_torsion_and_sub_formulas hchar e₁ e₂ e₃ he₁₂ he₁₃ he₂₃
  obtain ⟨H₀, D, hD, htors, hE₀_sub, hnot_mem, hH₀_card⟩ :=
    addSubgroup_sup_two_torsion_card_and_mem kv E₀ P₁ P₂ P₃ hP_ne hP_tors hE₀_tors hE₀_card
  obtain ⟨N, hbound, hchord⟩ :=
    lutz_outside_ultrametric_bounds v e₁ e₂ e₃ he₁₂ he₁₃ he₂₃ ev m₀ hev hm₀_pos hα_lt hβ_lt
  obtain ⟨hfin_quot, approx, happrox⟩ :=
    adicCompletion_bounded_ball_finite_approx v (3 * m₀) N
  haveI : Finite (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (3 * m₀ + N)) := hfin_quot
  have h_outside_bounds : ∀ (x y : v.adicCompletion K)
      (h : (threeRootsCurve e₁ e₂ e₃).toAffine.Nonsingular x y),
      WeierstrassCurve.Affine.Point.some h ∉ H₀ →
      Valued.v (x - e₁) < WithZero.exp (2 * (m₀ : ℤ)) ∧
      Valued.v (x - e₁) ≤ WithZero.exp (3 * (m₀ : ℤ)) ∧
      Valued.v y ≤ WithZero.exp (3 * (m₀ : ℤ)) ∧
      WithZero.exp ((m₀ : ℤ) + 1 - (N : ℤ)) ≤ Valued.v (2 * y) := by
    intro x y h hnot
    obtain ⟨h2P, hPE₀, hP₁E₀, hP₂E₀, hP₃E₀⟩ := hnot_mem _ hnot
    obtain ⟨⟨x₁', y₁', h₁', hsub₁, heq₁⟩,
            ⟨x₂', y₂', h₂', hsub₂, heq₂⟩,
            ⟨x₃', y₃', h₃', hsub₃, heq₃⟩⟩ := hP_trans x y h h2P
    have hx_lt : Valued.v (x - e₁) < WithZero.exp (2 * (m₀ : ℤ)) :=
      not_le.mp (fun hle => hPE₀ ((hE₀_mem x y h).mpr hle))
    have hx₁'_lt : Valued.v (x₁' - e₁) < WithZero.exp (2 * (m₀ : ℤ)) := by
      rw [hsub₁] at hP₁E₀
      exact not_le.mp (fun hle => hP₁E₀ ((hE₀_mem x₁' y₁' h₁').mpr hle))
    have hx₂'_lt : Valued.v (x₂' - e₁) < WithZero.exp (2 * (m₀ : ℤ)) := by
      rw [hsub₂] at hP₂E₀
      exact not_le.mp (fun hle => hP₂E₀ ((hE₀_mem x₂' y₂' h₂').mpr hle))
    have hx₃'_lt : Valued.v (x₃' - e₁) < WithZero.exp (2 * (m₀ : ℤ)) := by
      rw [hsub₃] at hP₃E₀
      exact not_le.mp (fun hle => hP₃E₀ ((hE₀_mem x₃' y₃' h₃').mpr hle))
    have hb := hbound x y x₁' x₂' x₃' (hns_eq x y h) hx_lt heq₁ hx₁'_lt heq₂ hx₂'_lt heq₃ hx₃'_lt
    exact ⟨hx_lt, hb.1, hb.2.1, hb.2.2⟩
  let ptApprox : (threeRootsCurve e₁ e₂ e₃).toAffine.Point →
      (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (3 * m₀ + N)) ×
      (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (3 * m₀ + N)) :=
    fun P => match P with
      | .zero => (0, 0)
      | @WeierstrassCurve.Affine.Point.some _ _ _ x y _ => (approx (x - e₁), approx y)
  let ι : (threeRootsCurve e₁ e₂ e₃).toAffine.Point ⧸ H₀ →
      Option ((NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (3 * m₀ + N)) ×
              (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ (3 * m₀ + N))) :=
    fun c => if c = 0 then none else some (ptApprox (Quotient.out c))
  have hι_inj : Function.Injective ι := by
    intro c₁ c₂ hc
    dsimp [ι] at hc
    by_cases hc₁ : c₁ = 0 <;> by_cases hc₂ : c₂ = 0
    · rw [hc₁, hc₂]
    · rw [if_pos hc₁, if_neg hc₂] at hc
      nomatch hc
    · rw [if_neg hc₁, if_pos hc₂] at hc
      nomatch hc
    · rw [if_neg hc₁, if_neg hc₂, Option.some.injEq] at hc
      have hout₁ : (QuotientAddGroup.mk (Quotient.out c₁) :
          (threeRootsCurve e₁ e₂ e₃).toAffine.Point ⧸ H₀) = c₁ :=
        QuotientAddGroup.out_eq' c₁
      have hout₂ : (QuotientAddGroup.mk (Quotient.out c₂) :
          (threeRootsCurve e₁ e₂ e₃).toAffine.Point ⧸ H₀) = c₂ :=
        QuotientAddGroup.out_eq' c₂
      have hnot₁ : Quotient.out c₁ ∉ H₀ := by
        intro hmem
        apply hc₁
        rw [← hout₁]
        exact (QuotientAddGroup.eq_zero_iff (Quotient.out c₁)).mpr hmem
      have hnot₂ : Quotient.out c₂ ∉ H₀ := by
        intro hmem
        apply hc₂
        rw [← hout₂]
        exact (QuotientAddGroup.eq_zero_iff (Quotient.out c₂)).mpr hmem
      rcases hp₁ : Quotient.out c₁ with _ | @⟨x₁, y₁, h₁⟩
      · exfalso
        apply hnot₁
        rw [hp₁]
        exact H₀.zero_mem
      · rcases hp₂ : Quotient.out c₂ with _ | @⟨x₂, y₂, h₂⟩
        · exfalso
          apply hnot₂
          rw [hp₂]
          exact H₀.zero_mem
        · rw [hp₁] at hnot₁ hout₁ hc
          rw [hp₂] at hnot₂ hout₂ hc
          dsimp [ptApprox] at hc
          injection hc with happrox_x happrox_y
          obtain ⟨hx₁_lt, hx₁_le, hy₁_le, h2y₁⟩ := h_outside_bounds x₁ y₁ h₁ hnot₁
          obtain ⟨hx₂_lt, hx₂_le, hy₂_le, _⟩ := h_outside_bounds x₂ y₂ h₂ hnot₂
          have hdx : Valued.v ((x₁ - e₁) - (x₂ - e₁)) ≤ WithZero.exp (-(N : ℤ)) := by
            have hle₁ : Valued.v (x₁ - e₁) ≤ WithZero.exp ((3 * m₀ : ℕ) : ℤ) := by
              simpa [Nat.cast_mul] using hx₁_le
            have hle₂ : Valued.v (x₂ - e₁) ≤ WithZero.exp ((3 * m₀ : ℕ) : ℤ) := by
              simpa [Nat.cast_mul] using hx₂_le
            exact happrox (x₁ - e₁) (x₂ - e₁) hle₁ hle₂ happrox_x
          have hdy : Valued.v (y₁ - y₂) ≤ WithZero.exp (-(N : ℤ)) := by
            have hle₁ : Valued.v y₁ ≤ WithZero.exp ((3 * m₀ : ℕ) : ℤ) := by
              simpa [Nat.cast_mul] using hy₁_le
            have hle₂ : Valued.v y₂ ≤ WithZero.exp ((3 * m₀ : ℕ) : ℤ) := by
              simpa [Nat.cast_mul] using hy₂_le
            exact happrox y₁ y₂ hle₁ hle₂ happrox_y
          obtain ⟨hy_sum_ne, hchord_val⟩ :=
            hchord x₁ y₁ x₂ y₂ hx₁_lt hx₂_lt h2y₁ hdx hdy
          by_cases hx_eq : x₁ = x₂
          · have hpt_eq := (hsub x₁ y₁ x₂ y₂ h₁ h₂).1 hx_eq hy_sum_ne
            rw [← hout₁, ← hout₂, hpt_eq]
          · obtain ⟨x₃, y₃, h₃, hpt_sub, hx₃_eq⟩ :=
              (hsub x₁ y₁ x₂ y₂ h₁ h₂).2 hx_eq
            have hx₃_val : WithZero.exp (2 * (m₀ : ℤ)) ≤ Valued.v (x₃ - e₁) := by
              rw [hx₃_eq]
              exact hchord_val hx_eq
            have hmem_E₀ : WeierstrassCurve.Affine.Point.some h₃ ∈ E₀ :=
              (hE₀_mem x₃ y₃ h₃).mpr hx₃_val
            have hsub_H₀ : WeierstrassCurve.Affine.Point.some h₁ -
                WeierstrassCurve.Affine.Point.some h₂ ∈ H₀ := by
              rw [hpt_sub]
              exact hE₀_sub _ hmem_E₀
            rw [← hout₁, ← hout₂, QuotientAddGroup.eq]
            have hneg : -WeierstrassCurve.Affine.Point.some h₁ +
                WeierstrassCurve.Affine.Point.some h₂ =
                -(WeierstrassCurve.Affine.Point.some h₁ -
                  WeierstrassCurve.Affine.Point.some h₂) := by abel
            rw [hneg]
            exact H₀.neg_mem hsub_H₀
  have hfin : Finite ((threeRootsCurve e₁ e₂ e₃).toAffine.Point ⧸ H₀) :=
    Finite.of_injective ι hι_inj
  exact ⟨H₀, D, hD, htors, hfin, hH₀_card⟩

theorem local_descent_subgroup_and_card_ge {K : Type u} [Field K] [NumberField K]
    (a₁ a₂ a₃ : K) (h₁₂ : a₁ ≠ a₂) (h₁₃ : a₁ ≠ a₃) (h₂₃ : a₂ ≠ a₃)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (ev kv : ℕ)
    (hev : Valued.v (2 : v.adicCompletion K) = WithZero.exp (-(ev : ℤ)))
    (hkv : Nat.card (NumberField.RingOfIntegers K ⧸ v.asIdeal ^ ev) = 2 ^ kv)
    (cl : v.adicCompletion K → (Fin (2 + kv) → ZMod 2))
    (hcl_mul : ∀ x y : v.adicCompletion K, x ≠ 0 → y ≠ 0 → cl (x * y) = cl x + cl y)
    (hcl_sq : ∀ x : v.adicCompletion K, x ≠ 0 → (cl x = 0 ↔ IsSquare x)) :
    ∃ (L : Finset ((Fin (2 + kv) → ZMod 2) × (Fin (2 + kv) → ZMod 2))),
      (0, 0) ∈ L ∧
      (∀ c₁ ∈ L, ∀ c₂ ∈ L, c₁ + c₂ ∈ L) ∧
      (∀ x₁ x₂ : v.adicCompletion K, x₁ ≠ 0 → x₂ ≠ 0 →
        ((cl x₁, cl x₂) ∈ L ↔ IsDescentClass
          (algebraMap K (v.adicCompletion K) a₁)
          (algebraMap K (v.adicCompletion K) a₂)
          (algebraMap K (v.adicCompletion K) a₃)
          x₁ x₂)) ∧
      2 ^ (2 + kv) ≤ L.card :=
by
  classical
  let e₁ : v.adicCompletion K := algebraMap K (v.adicCompletion K) a₁
  let e₂ : v.adicCompletion K := algebraMap K (v.adicCompletion K) a₂
  let e₃ : v.adicCompletion K := algebraMap K (v.adicCompletion K) a₃
  have he₁₂ : e₁ ≠ e₂ := (algebraMap K (v.adicCompletion K)).injective.ne h₁₂
  have he₁₃ : e₁ ≠ e₃ := (algebraMap K (v.adicCompletion K)).injective.ne h₁₃
  have he₂₃ : e₂ ≠ e₃ := (algebraMap K (v.adicCompletion K)).injective.ne h₂₃
  have hchar : (2 : v.adicCompletion K) ≠ 0 := by
    intro h2
    have h0 : Valued.v (2 : v.adicCompletion K) = 0 := by rw [h2, map_zero]
    rw [hev] at h0
    exact WithZero.exp_ne_zero h0
  obtain ⟨h_one, h_congr, h_mul⟩ := isDescentClass_one_and_congr_and_mul e₁ e₂ e₃ he₁₂ he₁₃ he₂₃
  let L : Finset ((Fin (2 + kv) → ZMod 2) × (Fin (2 + kv) → ZMod 2)) :=
    Finset.univ.filter (fun c =>
      ∃ x₁ x₂ : v.adicCompletion K, x₁ ≠ 0 ∧ x₂ ≠ 0 ∧
        cl x₁ = c.1 ∧ cl x₂ = c.2 ∧ IsDescentClass e₁ e₂ e₃ x₁ x₂)
  have hcl_one : cl 1 = 0 := (hcl_sq 1 one_ne_zero).mpr IsSquare.one
  have zmod2_fun_add_self : ∀ {n : ℕ} (z : Fin n → ZMod 2), z + z = 0 := by
    intro n z
    ext i
    change z i + z i = 0
    have h_self : ∀ a : ZMod 2, a + a = 0 := by decide
    exact h_self (z i)
  have hL_zero : (0, 0) ∈ L := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, 1, 1, one_ne_zero, one_ne_zero, hcl_one, hcl_one, h_one⟩
  have hL_add : ∀ c₁ ∈ L, ∀ c₂ ∈ L, c₁ + c₂ ∈ L := by
    intro c₁ hc₁ c₂ hc₂
    rw [Finset.mem_filter] at hc₁ hc₂ ⊢
    rcases hc₁ with ⟨_, x₁, x₂, hx₁, hx₂, hcx₁, hcx₂, hdesc_x⟩
    rcases hc₂ with ⟨_, y₁, y₂, hy₁, hy₂, hcy₁, hcy₂, hdesc_y⟩
    refine ⟨Finset.mem_univ _, x₁ * y₁, x₂ * y₂, mul_ne_zero hx₁ hy₁, mul_ne_zero hx₂ hy₂,
      ?_, ?_, h_mul x₁ x₂ y₁ y₂ hx₁ hx₂ hy₁ hy₂ hdesc_x hdesc_y⟩
    · rw [hcl_mul x₁ y₁ hx₁ hy₁, hcx₁, hcy₁]
      rfl
    · rw [hcl_mul x₂ y₂ hx₂ hy₂, hcx₂, hcy₂]
      rfl
  have hL_iff : ∀ x₁ x₂ : v.adicCompletion K, x₁ ≠ 0 → x₂ ≠ 0 →
      ((cl x₁, cl x₂) ∈ L ↔ IsDescentClass e₁ e₂ e₃ x₁ x₂) := by
    intro x₁ x₂ hx₁ hx₂
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨_, y₁, y₂, hy₁, hy₂, hcy₁, hcy₂, hdesc_y⟩
      have hsq₁ : IsSquare (y₁ * x₁) := by
        rw [← hcl_sq (y₁ * x₁) (mul_ne_zero hy₁ hx₁), hcl_mul y₁ x₁ hy₁ hx₁, hcy₁]
        exact zmod2_fun_add_self (cl x₁)
      have hsq₂ : IsSquare (y₂ * x₂) := by
        rw [← hcl_sq (y₂ * x₂) (mul_ne_zero hy₂ hx₂), hcl_mul y₂ x₂ hy₂ hx₂, hcy₂]
        exact zmod2_fun_add_self (cl x₂)
      exact h_congr y₁ y₂ x₁ x₂ hy₁ hy₂ hx₁ hx₂ hsq₁ hsq₂ hdesc_y
    · intro hdesc_x
      exact ⟨Finset.mem_univ _, x₁, x₂, hx₁, hx₂, rfl, rfl, hdesc_x⟩
  obtain ⟨δ, hδ_desc, hδ_inj⟩ :=
    threeRootsCurve_kummer_inj_mod_two hchar e₁ e₂ e₃ he₁₂ he₁₃ he₂₃ (2 + kv) cl hcl_mul hcl_sq
  have hδ_mem : ∀ P : (threeRootsCurve e₁ e₂ e₃).toAffine.Point, δ P ∈ L := by
    intro P
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hδ_desc P⟩
  obtain ⟨m₀, E₀, hm₀_pos, hα_lt, hβ_lt, hE₀_mem, hE₀_tors, hE₀_card⟩ :=
    lutz_subgroup_and_mod_two_card a₁ a₂ a₃ h₁₂ h₁₃ h₂₃ v ev kv hev hkv
  obtain ⟨H₀, D, hD, htors, hfin, hH₀_card⟩ :=
    finite_quotient_of_lutz_plus_two_torsion a₁ a₂ a₃ h₁₂ h₁₃ h₂₃ v ev kv m₀
      hev hm₀_pos hα_lt hβ_lt E₀ hE₀_mem hE₀_tors hE₀_card
  have hcard_le : Nat.card (H₀ ⧸ D) ≤ L.card :=
    herbrand_quotient_card_le_of_finite_quotient H₀ D hD L δ hδ_mem hδ_inj htors hfin
  exact ⟨L, hL_zero, hL_add, hL_iff, le_trans hH₀_card hcard_le⟩

theorem lagrangian_syndrome_and_coord_family {ι : Type u} [DecidableEq ι]
    (T : Finset ι) (d : ι → ℕ) (M : ℕ) (hM : ∑ v ∈ T, d v = M)
    (B : ∀ v, (Fin (d v) → ZMod 2) → (Fin (d v) → ZMod 2) → ZMod 2)
    (L : ∀ v, Finset ((Fin (d v) → ZMod 2) × (Fin (d v) → ZMod 2)))
    (hB_add : ∀ v ∈ T, ∀ α₁ α₂ β, B v (α₁ + α₂) β = B v α₁ β + B v α₂ β)
    (hB_symm : ∀ v ∈ T, ∀ α β, B v α β = B v β α)
    (hB_nondeg : ∀ v ∈ T, ∀ α, (∀ β, B v α β = 0) → α = 0)
    (hL_zero : ∀ v ∈ T, (0, 0) ∈ L v)
    (hL_add : ∀ v ∈ T, ∀ c₁ ∈ L v, ∀ c₂ ∈ L v, c₁ + c₂ ∈ L v)
    (hL_iso : ∀ v ∈ T, ∀ c₁ ∈ L v, ∀ c₂ ∈ L v, B v c₁.1 c₂.2 + B v c₁.2 c₂.1 = 0)
    (hL_card : ∀ v ∈ T, 2 ^ (d v) ≤ (L v).card) :
    ∃ (Φ Ψ : (∀ v, (Fin (d v) → ZMod 2) × (Fin (d v) → ZMod 2)) → (Fin M → ZMod 2)),
      (∀ c₁ c₂, (∀ v ∈ T, c₁ v = c₂ v) → Φ c₁ = Φ c₂) ∧
      (∀ c₁ c₂, Φ (c₁ + c₂) = Φ c₁ + Φ c₂) ∧
      (∀ c, Φ c = 0 ↔ ∀ v ∈ T, c v ∈ L v) ∧
      (∀ c₁ c₂, Φ c₁ = 0 → Φ c₂ = 0 → Ψ c₁ = Ψ c₂ → ∀ v ∈ T, c₁ v = c₂ v) ∧
      (∀ q p, Φ q = 0 →
        (∏ v ∈ T, (-1 : ℤˣ) ^ (B v (q v).1 (p v).2 + B v (q v).2 (p v).1).val) =
          (-1 : ℤˣ) ^ (dotProduct (Ψ q) (Φ p)).val) :=
by
  classical
  have single_lagrangian : ∀ (n : ℕ)
      (B : (Fin n → ZMod 2) → (Fin n → ZMod 2) → ZMod 2)
      (L : Finset ((Fin n → ZMod 2) × (Fin n → ZMod 2)))
      (hB_add : ∀ α₁ α₂ β, B (α₁ + α₂) β = B α₁ β + B α₂ β)
      (hB_symm : ∀ α β, B α β = B β α)
      (hB_nondeg : ∀ α, (∀ β, B α β = 0) → α = 0)
      (hL_zero : (0, 0) ∈ L)
      (hL_add : ∀ c₁ ∈ L, ∀ c₂ ∈ L, c₁ + c₂ ∈ L)
      (hL_iso : ∀ c₁ ∈ L, ∀ c₂ ∈ L, B c₁.1 c₂.2 + B c₁.2 c₂.1 = 0)
      (hL_card : 2 ^ n ≤ L.card),
      ∃ (φ ψ : ((Fin n → ZMod 2) × (Fin n → ZMod 2)) → (Fin n → ZMod 2)),
        (∀ c₁ c₂, φ (c₁ + c₂) = φ c₁ + φ c₂) ∧
        (∀ c, φ c = 0 ↔ c ∈ L) ∧
        (∀ c₁ ∈ L, ∀ c₂ ∈ L, ψ c₁ = ψ c₂ → c₁ = c₂) ∧
        (∀ q ∈ L, ∀ p, dotProduct (ψ q) (φ p) = B q.1 p.2 + B q.2 p.1) := by
    intro n B L hB_add hB_symm hB_nondeg hL_zero hL_add hL_iso hL_card
    have hV_neg : ∀ x : (Fin n → ZMod 2) × (Fin n → ZMod 2), -x = x := by
      intro x
      exact Prod.ext (funext fun i => CharTwo.neg_eq (x.1 i))
        (funext fun i => CharTwo.neg_eq (x.2 i))
    have hV_add_self : ∀ x : (Fin n → ZMod 2) × (Fin n → ZMod 2), x + x = 0 := by
      intro x
      exact Prod.ext (funext fun i => CharTwo.add_self_eq_zero (x.1 i))
        (funext fun i => CharTwo.add_self_eq_zero (x.2 i))
    have hV_eq_of_add_eq_zero :
        ∀ x y : (Fin n → ZMod 2) × (Fin n → ZMod 2), x + y = 0 → x = y := by
      intro x y hxy
      calc x = x + 0 := (add_zero x).symm
        _ = x + (y + y) := by rw [hV_add_self y]
        _ = (x + y) + y := (add_assoc x y y).symm
        _ = 0 + y := by rw [hxy]
        _ = y := zero_add y
    have hB_add_right : ∀ α β₁ β₂ : Fin n → ZMod 2, B α (β₁ + β₂) = B α β₁ + B α β₂ := by
      intro α β₁ β₂
      rw [hB_symm α (β₁ + β₂), hB_add β₁ β₂ α, hB_symm β₁ α, hB_symm β₂ α]
    have hB_zero_left : ∀ β : Fin n → ZMod 2, B 0 β = 0 := by
      intro β
      have h : B 0 β + B 0 β = B 0 β := by
        rw [← hB_add 0 0 β, zero_add]
      rw [CharTwo.add_self_eq_zero] at h
      exact h.symm
    have hB_zero_right : ∀ α : Fin n → ZMod 2, B α 0 = 0 := by
      intro α
      rw [hB_symm α 0, hB_zero_left α]
    let Ω : ((Fin n → ZMod 2) × (Fin n → ZMod 2)) →
        ((Fin n → ZMod 2) × (Fin n → ZMod 2)) → ZMod 2 :=
      fun x y => B x.1 y.2 + B x.2 y.1
    have hΩ_add_left : ∀ x₁ x₂ y, Ω (x₁ + x₂) y = Ω x₁ y + Ω x₂ y := by
      intro x₁ x₂ y
      dsimp [Ω]
      rw [hB_add, hB_add, add_add_add_comm]
    have hΩ_add_right : ∀ x y₁ y₂, Ω x (y₁ + y₂) = Ω x y₁ + Ω x y₂ := by
      intro x y₁ y₂
      dsimp [Ω]
      rw [hB_add_right, hB_add_right, add_add_add_comm]
    have hΩ_symm : ∀ x y, Ω x y = Ω y x := by
      intro x y
      dsimp [Ω]
      rw [hB_symm x.1 y.2, hB_symm x.2 y.1, add_comm]
    have hΩ_zero_left : ∀ y, Ω 0 y = 0 := by
      intro y
      dsimp [Ω]
      rw [hB_zero_left, hB_zero_left, add_zero]
    have hΩ_nondeg : ∀ x, (∀ y, Ω x y = 0) → x = 0 := by
      intro x hx
      apply Prod.ext
      · apply hB_nondeg x.1
        intro β
        have h1 := hx (0, β)
        dsimp [Ω] at h1
        rw [hB_zero_right x.2, add_zero] at h1
        exact h1
      · apply hB_nondeg x.2
        intro β
        have h2 := hx (β, 0)
        dsimp [Ω] at h2
        rw [hB_zero_right x.1, zero_add] at h2
        exact h2
    let L_add : AddSubgroup ((Fin n → ZMod 2) × (Fin n → ZMod 2)) :=
      { carrier := { x | x ∈ L }
        zero_mem' := hL_zero
        add_mem' := fun {x y} hx hy => hL_add x hx y hy
        neg_mem' := fun {x} hx => by
          change -x ∈ L
          rwa [hV_neg] }
    let L_sub : Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin n → ZMod 2)) :=
      AddSubgroup.toZModSubmodule 2 L_add
    let L_perp_add : AddSubgroup ((Fin n → ZMod 2) × (Fin n → ZMod 2)) :=
      { carrier := { x | ∀ y ∈ L, Ω x y = 0 }
        zero_mem' := fun y _ => hΩ_zero_left y
        add_mem' := fun {x₁ x₂} hx₁ hx₂ y hy => by
          rw [hΩ_add_left, hx₁ y hy, hx₂ y hy, add_zero]
        neg_mem' := fun {x} hx y hy => by
          change Ω (-x) y = 0
          rw [hV_neg]
          exact hx y hy }
    let L_perp : Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin n → ZMod 2)) :=
      AddSubgroup.toZModSubmodule 2 L_perp_add
    have hL_le_perp : L_sub ≤ L_perp := by
      intro x hx y hy
      exact hL_iso x hx y hy
    have h_rk_le_perp :
        Module.finrank (ZMod 2) ↥L_sub ≤ Module.finrank (ZMod 2) ↥L_perp :=
      Submodule.finrank_mono hL_le_perp
    have h_card_L_sub : Nat.card ↥L_sub = L.card := by
      rw [Nat.card_eq_fintype_card, ← Fintype.card_coe L]
      exact Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => Iff.rfl))
    have h_pow_le : 2 ^ n ≤ 2 ^ Module.finrank (ZMod 2) ↥L_sub := by
      have h1 : Nat.card ↥L_sub = 2 ^ Module.finrank (ZMod 2) ↥L_sub := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥L_sub), Nat.card_zmod]
      omega
    have h_rk_ge : n ≤ Module.finrank (ZMod 2) ↥L_sub :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h_pow_le
    let ω (x : (Fin n → ZMod 2) × (Fin n → ZMod 2)) :
        ((Fin n → ZMod 2) × (Fin n → ZMod 2)) →ₗ[ZMod 2] ZMod 2 :=
      AddMonoidHom.toZModLinearMap 2
        (AddMonoidHom.mk' (fun y => Ω x y) (fun y₁ y₂ => hΩ_add_right x y₁ y₂))
    let θ : ↥L_perp → ↥L_sub.dualAnnihilator := fun x =>
      ⟨ω x.1, by
        rw [Submodule.mem_dualAnnihilator]
        intro y hy
        exact x.2 y hy⟩
    have hθ_inj : Function.Injective θ := by
      intro x₁ x₂ hθ
      have h_eq : ∀ y, Ω x₁.1 y = Ω x₂.1 y := by
        intro y
        exact congrFun (congrArg DFunLike.coe (Subtype.mk.inj hθ)) y
      have h_sum_zero : x₁.1 + x₂.1 = 0 := by
        apply hΩ_nondeg (x₁.1 + x₂.1)
        intro y
        rw [hΩ_add_left, h_eq y, CharTwo.add_self_eq_zero]
      exact Subtype.ext (hV_eq_of_add_eq_zero x₁.1 x₂.1 h_sum_zero)
    haveI : Finite ↥L_sub.dualAnnihilator := DFunLike.finite ↥L_sub.dualAnnihilator
    have h_card_perp_le : Nat.card ↥L_perp ≤ Nat.card ↥L_sub.dualAnnihilator :=
      Nat.card_le_card_of_injective θ hθ_inj
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥L_perp),
        Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥L_sub.dualAnnihilator),
        Nat.card_zmod] at h_card_perp_le
    have h_rk_perp_le_da :
        Module.finrank (ZMod 2) ↥L_perp ≤ Module.finrank (ZMod 2) ↥L_sub.dualAnnihilator :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h_card_perp_le
    have h_da :
        Module.finrank (ZMod 2) ↥L_sub +
          Module.finrank (ZMod 2) ↥L_sub.dualAnnihilator = n + n := by
      rw [Subspace.finrank_add_finrank_dualAnnihilator_eq L_sub,
          Module.finrank_prod, Module.finrank_fin_fun (ZMod 2)]
    have h_rk : Module.finrank (ZMod 2) ↥L_sub = n := by omega
    have h_rk_eq : Module.finrank (ZMod 2) ↥L_sub = Module.finrank (ZMod 2) ↥L_perp := by omega
    have hL_eq_perp : L_sub = L_perp := Submodule.eq_of_le_of_finrank_eq hL_le_perp h_rk_eq
    let b : Module.Basis (Fin n) (ZMod 2) ↥L_sub :=
      Module.finBasisOfFinrankEq (ZMod 2) ↥L_sub h_rk
    let φ : ((Fin n → ZMod 2) × (Fin n → ZMod 2)) → (Fin n → ZMod 2) :=
      fun p j => Ω (b j).1 p
    let ψ : ((Fin n → ZMod 2) × (Fin n → ZMod 2)) → (Fin n → ZMod 2) :=
      fun q => if hq : q ∈ L then b.equivFun ⟨q, hq⟩ else 0
    have h_pair_local : ∀ q ∈ L, ∀ p, dotProduct (ψ q) (φ p) = Ω q p := by
      intro q hq p
      let lam_p : ↥L_sub →ₗ[ZMod 2] ZMod 2 :=
        AddMonoidHom.toZModLinearMap 2
          (AddMonoidHom.mk' (fun x : ↥L_sub => Ω x.1 p) (fun x₁ x₂ => hΩ_add_left x₁.1 x₂.1 p))
      have hlam_apply (x : ↥L_sub) : lam_p x = Ω x.1 p := rfl
      have h_sum := congrArg lam_p (b.sum_equivFun ⟨q, hq⟩)
      rw [map_sum, hlam_apply] at h_sum
      change ∑ j : Fin n, (if hq : q ∈ L then b.equivFun ⟨q, hq⟩ else 0) j * Ω (b j).1 p = Ω q p
      rw [dif_pos hq, ← h_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, hlam_apply]
    refine ⟨φ, ψ, ?_, ?_, ?_, h_pair_local⟩
    · intro c₁ c₂
      funext j
      exact hΩ_add_right (b j).1 c₁ c₂
    · intro p
      constructor
      · intro hp
        have hp_perp : p ∈ L_perp := by
          intro q hq
          rw [hΩ_symm, ← h_pair_local q hq p, hp, dotProduct_zero]
        rw [← hL_eq_perp] at hp_perp
        exact hp_perp
      · intro hp
        funext j
        exact hL_iso (b j).1 (b j).2 p hp
    · intro c₁ hc₁ c₂ hc₂ hψ
      dsimp [ψ] at hψ
      rw [dif_pos hc₁, dif_pos hc₂] at hψ
      exact congrArg Subtype.val (b.equivFun.injective hψ)
  choose φ_loc ψ_loc hφ_add hφ_zero hψ_inj h_pair_loc using
    fun v : ↥T => single_lagrangian (d v.1) (B v.1) (L v.1)
      (hB_add v.1 v.2) (hB_symm v.1 v.2) (hB_nondeg v.1 v.2)
      (hL_zero v.1 v.2) (hL_add v.1 v.2) (hL_iso v.1 v.2) (hL_card v.1 v.2)
  have h_card_sigma : Fintype.card (Σ v : ↥T, Fin (d v.1)) = M := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin, Finset.univ_eq_attach]
    rw [Finset.sum_attach T d, hM]
  let σ : (Σ v : ↥T, Fin (d v.1)) ≃ Fin M := Fintype.equivFinOfCardEq h_card_sigma
  let Φ : (∀ v, (Fin (d v) → ZMod 2) × (Fin (d v) → ZMod 2)) → (Fin M → ZMod 2) :=
    fun c i => φ_loc (σ.symm i).1 (c (σ.symm i).1.1) (σ.symm i).2
  let Ψ : (∀ v, (Fin (d v) → ZMod 2) × (Fin (d v) → ZMod 2)) → (Fin M → ZMod 2) :=
    fun c i => ψ_loc (σ.symm i).1 (c (σ.symm i).1.1) (σ.symm i).2
  have hΦ_sigma (c) (v : ↥T) (j : Fin (d v.1)) :
      Φ c (σ ⟨v, j⟩) = φ_loc v (c v.1) j := by
    change φ_loc (σ.symm (σ ⟨v, j⟩)).1 (c (σ.symm (σ ⟨v, j⟩)).1.1) (σ.symm (σ ⟨v, j⟩)).2 = _
    rw [Equiv.symm_apply_apply]
  have hΨ_sigma (c) (v : ↥T) (j : Fin (d v.1)) :
      Ψ c (σ ⟨v, j⟩) = ψ_loc v (c v.1) j := by
    change ψ_loc (σ.symm (σ ⟨v, j⟩)).1 (c (σ.symm (σ ⟨v, j⟩)).1.1) (σ.symm (σ ⟨v, j⟩)).2 = _
    rw [Equiv.symm_apply_apply]
  have hΦ_zero_iff : ∀ c, Φ c = 0 ↔ ∀ v ∈ T, c v ∈ L v := by
    intro c
    constructor
    · intro hΦ v hv
      rw [← hφ_zero ⟨v, hv⟩ (c v)]
      funext j
      have hi : Φ c (σ ⟨⟨v, hv⟩, j⟩) = 0 := congr_fun hΦ (σ ⟨⟨v, hv⟩, j⟩)
      rw [hΦ_sigma] at hi
      exact hi
    · intro hc
      funext i
      dsimp [Φ]
      have h_zero : φ_loc (σ.symm i).1 (c (σ.symm i).1.1) = 0 :=
        (hφ_zero (σ.symm i).1 (c (σ.symm i).1.1)).mpr (hc (σ.symm i).1.1 (σ.symm i).1.2)
      exact congr_fun h_zero (σ.symm i).2
  have zmod2_neg_one_pow_add : ∀ x y : ZMod 2,
      (-1 : ℤˣ) ^ (x + y).val = (-1 : ℤˣ) ^ x.val * (-1 : ℤˣ) ^ y.val := by
    intro x y
    fin_cases x <;> fin_cases y <;> decide
  have prod_neg_one_pow_val : ∀ (s : Finset ι) (f : ι → ZMod 2),
      (∏ v ∈ s, (-1 : ℤˣ) ^ (f v).val) = (-1 : ℤˣ) ^ (∑ v ∈ s, f v).val := by
    intro s f
    induction s using Finset.cons_induction with
    | empty => rfl
    | cons a s ha ih =>
      rw [Finset.prod_cons, Finset.sum_cons, zmod2_neg_one_pow_add, ih]
  refine ⟨Φ, Ψ, ?_, ?_, hΦ_zero_iff, ?_, ?_⟩
  · intro c₁ c₂ hc
    funext i
    dsimp [Φ]
    rw [hc (σ.symm i).1.1 (σ.symm i).1.2]
  · intro c₁ c₂
    funext i
    dsimp [Φ]
    exact congr_fun (hφ_add (σ.symm i).1 (c₁ (σ.symm i).1.1) (c₂ (σ.symm i).1.1)) (σ.symm i).2
  · intro c₁ c₂ hΦ₁ hΦ₂ hΨ v hv
    have hc₁ : c₁ v ∈ L v := (hΦ_zero_iff c₁).mp hΦ₁ v hv
    have hc₂ : c₂ v ∈ L v := (hΦ_zero_iff c₂).mp hΦ₂ v hv
    apply hψ_inj ⟨v, hv⟩ (c₁ v) hc₁ (c₂ v) hc₂
    funext j
    have hi : Ψ c₁ (σ ⟨⟨v, hv⟩, j⟩) = Ψ c₂ (σ ⟨⟨v, hv⟩, j⟩) := congr_fun hΨ (σ ⟨⟨v, hv⟩, j⟩)
    rw [hΨ_sigma, hΨ_sigma] at hi
    exact hi
  · intro q p hq
    have hq_mem : ∀ v ∈ T, q v ∈ L v := (hΦ_zero_iff q).mp hq
    rw [prod_neg_one_pow_val]
    congr 1
    congr 1
    symm
    calc dotProduct (Ψ q) (Φ p)
      _ = ∑ i : Fin M, Ψ q i * Φ p i := rfl
      _ = ∑ x : (Σ v : ↥T, Fin (d v.1)), Ψ q (σ x) * Φ p (σ x) :=
        (Fintype.sum_equiv σ _ _ (fun _ => rfl)).symm
      _ = ∑ v : ↥T, ∑ j : Fin (d v.1),
            ψ_loc v (q v.1) j * φ_loc v (p v.1) j := by
        rw [Fintype.sum_sigma]
        refine Finset.sum_congr rfl fun v _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hΨ_sigma, hΦ_sigma]
      _ = ∑ v : ↥T, (B v.1 (q v.1).1 (p v.1).2 + B v.1 (q v.1).2 (p v.1).1) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        exact h_pair_loc v (q v.1) (hq_mem v.1 v.2) (p v.1)
      _ = ∑ v ∈ T, (B v (q v).1 (p v).2 + B v (q v).2 (p v).1) := by
        rw [Finset.univ_eq_attach]
        exact Finset.sum_attach T (fun v => B v (q v).1 (p v).2 + B v (q v).2 (p v).1)

theorem local_selmer_basis_on_T {K : Type u} [Field K] [NumberField K]
    (a₁ a₂ a₃ : K) (h₁₂ : a₁ ≠ a₂) (h₁₃ : a₁ ≠ a₃) (h₂₃ : a₂ ≠ a₃)
    (hint₁ : IsIntegral ℤ a₁) (hint₂ : IsIntegral ℤ a₂) (hint₃ : IsIntegral ℤ a₃)
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hT : IsGoodT a₁ a₂ a₃ T) :
    ∃ (Φ_T Ψ_T : Kˣ × Kˣ → (Fin (2 * T.card + NumberField.InfinitePlace.nrRealPlaces K +
        2 * NumberField.InfinitePlace.nrComplexPlaces K) → ZMod 2)),
      (∀ p q : Kˣ × Kˣ,
        IsSquare ((p.1 : K) * (q.1 : K)) → IsSquare ((p.2 : K) * (q.2 : K)) →
        Φ_T p = Φ_T q) ∧
      (∀ p q : Kˣ × Kˣ, Φ_T (p.1 * q.1, p.2 * q.2) = Φ_T p + Φ_T q) ∧
      (∀ p : Kˣ × Kˣ, Φ_T p = 0 ↔
        ∀ v ∈ T, IsDescentClass
          (algebraMap K (v.adicCompletion K) a₁)
          (algebraMap K (v.adicCompletion K) a₂)
          (algebraMap K (v.adicCompletion K) a₃)
          (algebraMap K (v.adicCompletion K) (p.1 : K))
          (algebraMap K (v.adicCompletion K) (p.2 : K))) ∧
      (∀ q₁ q₂ : Kˣ × Kˣ, Φ_T q₁ = 0 → Φ_T q₂ = 0 → Ψ_T q₁ = Ψ_T q₂ →
        ∀ v ∈ T,
          IsSquare (algebraMap K (v.adicCompletion K) ((q₁.1 * q₂.1 : Kˣ) : K)) ∧
          IsSquare (algebraMap K (v.adicCompletion K) ((q₁.2 * q₂.2 : Kˣ) : K))) ∧
      (∀ q p : Kˣ × Kˣ, Φ_T q = 0 →
        (∏ v ∈ T, (hilbFin v (q.1 : K) (p.2 : K) * hilbFin v (q.2 : K) (p.1 : K))) =
          (-1 : ℤˣ) ^ (dotProduct (Ψ_T q) (Φ_T p)).val) :=
by
  classical
  obtain ⟨e, k, he, hk, h_sum⟩ :=
    dyadic_valuation_norm_sum_on_T a₁ a₂ a₃ h₁₂ h₁₃ h₂₃ hint₁ hint₂ hint₃ T hT
  choose cl B hcl_mul hcl_sq hcl_surj hB_add hB_symm hB_nondeg hB_hilb using
    fun v => local_sqCl_coord_and_hilbLoc_pairing v (e v) (k v) (he v) (hk v)
  choose L hL_zero hL_add hL_iff hL_card using
    fun v => local_descent_subgroup_and_card_ge a₁ a₂ a₃ h₁₂ h₁₃ h₂₃ v (e v) (k v)
      (he v) (hk v) (cl v) (hcl_mul v) (hcl_sq v)
  have unit_map_ne_zero : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
      (u : Kˣ), algebraMap K (v.adicCompletion K) (u : K) ≠ 0 := by
    intro v u
    rw [ne_eq, map_eq_zero]
    exact u.ne_zero
  have zmod2_add_eq_zero_of_neg_one_pow_mul : ∀ (x y : ZMod 2),
      (-1 : ℤˣ) ^ x.val * (-1 : ℤˣ) ^ y.val = 1 → x + y = 0 := by
    intro x y
    fin_cases x <;> fin_cases y <;> decide
  have zmod2_neg_one_pow_add : ∀ (x y : ZMod 2),
      (-1 : ℤˣ) ^ (x + y).val = (-1 : ℤˣ) ^ x.val * (-1 : ℤˣ) ^ y.val := by
    intro x y
    fin_cases x <;> fin_cases y <;> decide
  have zmod2_fun_eq_of_add_eq_zero : ∀ {n : ℕ} (x y : Fin n → ZMod 2),
      x + y = 0 → x = y := by
    intro n x y hxy
    ext i
    have hi : x i + y i = 0 := congr_fun hxy i
    have h_eq : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
    exact h_eq (x i) (y i) hi
  have zmod2_fun_add_self : ∀ {n : ℕ} (x : Fin n → ZMod 2), x + x = 0 := by
    intro n x
    ext i
    change x i + x i = 0
    have h_self : ∀ a : ZMod 2, a + a = 0 := by decide
    exact h_self (x i)
  have hL_iso : ∀ v ∈ T, ∀ c₁ ∈ L v, ∀ c₂ ∈ L v,
      B v c₁.1 c₂.2 + B v c₁.2 c₂.1 = 0 := by
    intro v _ c₁ hc₁ c₂ hc₂
    obtain ⟨q₁, hq₁⟩ := hcl_surj v c₁.1
    obtain ⟨q₂, hq₂⟩ := hcl_surj v c₁.2
    obtain ⟨p₁, hp₁⟩ := hcl_surj v c₂.1
    obtain ⟨p₂, hp₂⟩ := hcl_surj v c₂.2
    have hq_desc : IsDescentClass
        (algebraMap K (v.adicCompletion K) a₁)
        (algebraMap K (v.adicCompletion K) a₂)
        (algebraMap K (v.adicCompletion K) a₃)
        (algebraMap K (v.adicCompletion K) (q₁ : K))
        (algebraMap K (v.adicCompletion K) (q₂ : K)) := by
      rw [← hL_iff v _ _ (unit_map_ne_zero v q₁) (unit_map_ne_zero v q₂), hq₁, hq₂]
      exact hc₁
    have hp_desc : IsDescentClass
        (algebraMap K (v.adicCompletion K) a₁)
        (algebraMap K (v.adicCompletion K) a₂)
        (algebraMap K (v.adicCompletion K) a₃)
        (algebraMap K (v.adicCompletion K) (p₁ : K))
        (algebraMap K (v.adicCompletion K) (p₂ : K)) := by
      rw [← hL_iff v _ _ (unit_map_ne_zero v p₁) (unit_map_ne_zero v p₂), hp₁, hp₂]
      exact hc₂
    have h_pair := hilbFin_pairing_eq_one_of_isDescentClass a₁ a₂ a₃ h₁₂ h₁₃ h₂₃
      v q₁ q₂ p₁ p₂ hq_desc hp_desc
    simp only [hilbFin] at h_pair
    rw [hB_hilb v _ _ (unit_map_ne_zero v q₁) (unit_map_ne_zero v p₂),
        hB_hilb v _ _ (unit_map_ne_zero v q₂) (unit_map_ne_zero v p₁),
        hq₁, hp₂, hq₂, hp₁] at h_pair
    exact zmod2_add_eq_zero_of_neg_one_pow_mul _ _ h_pair
  obtain ⟨Φ, Ψ, hΦ_congr, hΦ_add, hΦ_zero, hΨ_inj, hΦ_pair⟩ :=
    lagrangian_syndrome_and_coord_family T (fun v => 2 + k v)
      (2 * T.card + NumberField.InfinitePlace.nrRealPlaces K +
        2 * NumberField.InfinitePlace.nrComplexPlaces K)
      h_sum B L
      (fun v _ => hB_add v) (fun v _ => hB_symm v) (fun v _ => hB_nondeg v)
      (fun v _ => hL_zero v) (fun v _ => hL_add v) hL_iso (fun v _ => hL_card v)
  let loc : Kˣ × Kˣ → ∀ v, (Fin (2 + k v) → ZMod 2) × (Fin (2 + k v) → ZMod 2) :=
    fun p v => (cl v (algebraMap K (v.adicCompletion K) (p.1 : K)),
                cl v (algebraMap K (v.adicCompletion K) (p.2 : K)))
  let Φ_T : Kˣ × Kˣ → (Fin (2 * T.card + NumberField.InfinitePlace.nrRealPlaces K +
      2 * NumberField.InfinitePlace.nrComplexPlaces K) → ZMod 2) :=
    fun p => Φ (loc p)
  let Ψ_T : Kˣ × Kˣ → (Fin (2 * T.card + NumberField.InfinitePlace.nrRealPlaces K +
      2 * NumberField.InfinitePlace.nrComplexPlaces K) → ZMod 2) :=
    fun q => Ψ (loc q)
  have h_loc_mul : ∀ p q : Kˣ × Kˣ, loc (p.1 * q.1, p.2 * q.2) = loc p + loc q := by
    intro p q
    ext v : 1
    apply Prod.ext
    · change cl v (algebraMap K (v.adicCompletion K) ((p.1 * q.1 : Kˣ) : K)) =
        cl v (algebraMap K (v.adicCompletion K) (p.1 : K)) +
        cl v (algebraMap K (v.adicCompletion K) (q.1 : K))
      rw [Units.val_mul, map_mul]
      exact hcl_mul v _ _ (unit_map_ne_zero v p.1) (unit_map_ne_zero v q.1)
    · change cl v (algebraMap K (v.adicCompletion K) ((p.2 * q.2 : Kˣ) : K)) =
        cl v (algebraMap K (v.adicCompletion K) (p.2 : K)) +
        cl v (algebraMap K (v.adicCompletion K) (q.2 : K))
      rw [Units.val_mul, map_mul]
      exact hcl_mul v _ _ (unit_map_ne_zero v p.2) (unit_map_ne_zero v q.2)
  refine ⟨Φ_T, Ψ_T, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q hp1 hp2
    apply hΦ_congr
    intro v _
    apply Prod.ext
    · apply zmod2_fun_eq_of_add_eq_zero
      rw [← hcl_mul v _ _ (unit_map_ne_zero v p.1) (unit_map_ne_zero v q.1),
          hcl_sq v _ (mul_ne_zero (unit_map_ne_zero v p.1) (unit_map_ne_zero v q.1)),
          ← map_mul]
      exact hp1.map (algebraMap K (v.adicCompletion K))
    · apply zmod2_fun_eq_of_add_eq_zero
      rw [← hcl_mul v _ _ (unit_map_ne_zero v p.2) (unit_map_ne_zero v q.2),
          hcl_sq v _ (mul_ne_zero (unit_map_ne_zero v p.2) (unit_map_ne_zero v q.2)),
          ← map_mul]
      exact hp2.map (algebraMap K (v.adicCompletion K))
  · intro p q
    dsimp [Φ_T]
    rw [h_loc_mul p q]
    exact hΦ_add (loc p) (loc q)
  · intro p
    dsimp [Φ_T]
    rw [hΦ_zero]
    refine forall₂_congr fun v _ => ?_
    exact hL_iff v _ _ (unit_map_ne_zero v p.1) (unit_map_ne_zero v p.2)
  · intro q₁ q₂ hq₁ hq₂ hΨ v hv
    have h_eq := hΨ_inj (loc q₁) (loc q₂) hq₁ hq₂ hΨ v hv
    have h1 : cl v (algebraMap K (v.adicCompletion K) (q₁.1 : K)) =
        cl v (algebraMap K (v.adicCompletion K) (q₂.1 : K)) := congr_arg Prod.fst h_eq
    have h2 : cl v (algebraMap K (v.adicCompletion K) (q₁.2 : K)) =
        cl v (algebraMap K (v.adicCompletion K) (q₂.2 : K)) := congr_arg Prod.snd h_eq
    constructor
    · rw [← hcl_sq v _ (unit_map_ne_zero v (q₁.1 * q₂.1)), Units.val_mul, map_mul,
          hcl_mul v _ _ (unit_map_ne_zero v q₁.1) (unit_map_ne_zero v q₂.1), h1]
      exact zmod2_fun_add_self _
    · rw [← hcl_sq v _ (unit_map_ne_zero v (q₁.2 * q₂.2)), Units.val_mul, map_mul,
          hcl_mul v _ _ (unit_map_ne_zero v q₁.2) (unit_map_ne_zero v q₂.2), h2]
      exact zmod2_fun_add_self _
  · intro q p hq
    rw [← hΦ_pair (loc q) (loc p) hq]
    refine Finset.prod_congr rfl fun v _ => ?_
    simp only [hilbFin]
    rw [hB_hilb v _ _ (unit_map_ne_zero v q.1) (unit_map_ne_zero v p.2),
        hB_hilb v _ _ (unit_map_ne_zero v q.2) (unit_map_ne_zero v p.1),
        ← zmod2_neg_one_pow_add]

theorem exists_independent_of_orthogonal_syndrome (N M₁ M₂ : ℕ) (hM : M₁ + M₂ + 2 = N)
    (f₁ g₁ : (Fin N → ZMod 2) → (Fin M₁ → ZMod 2))
    (f₂ g₂ : (Fin N → ZMod 2) → (Fin M₂ → ZMod 2))
    (Sq₀ : (Fin N → ZMod 2) → Prop)
    (hf₁ : ∀ α β, f₁ (α + β) = f₁ α + f₁ β)
    (hf₂ : ∀ α β, f₂ (α + β) = f₂ α + f₂ β)
    (hSq_zero : Sq₀ 0)
    (hSq_add : ∀ α β, Sq₀ α → Sq₀ β → Sq₀ (α + β))
    (hinj : ∀ β₁ β₂, f₁ β₁ = 0 → f₂ β₁ = 0 → f₁ β₂ = 0 → f₂ β₂ = 0 →
      Sq₀ (β₁ + β₂) → g₁ β₁ = g₁ β₂ → g₂ β₁ = g₂ β₂ → β₁ = β₂)
    (horth : ∀ β α, f₁ β = 0 → f₂ β = 0 → Sq₀ β →
      dotProduct (g₁ β) (f₁ α) + dotProduct (g₂ β) (f₂ α) = 0) :
    ∃ α₁ α₂ : Fin N → ZMod 2,
      f₁ α₁ = 0 ∧ f₂ α₁ = 0 ∧
      f₁ α₂ = 0 ∧ f₂ α₂ = 0 ∧
      ¬ Sq₀ α₁ ∧ ¬ Sq₀ α₂ ∧ ¬ Sq₀ (α₁ + α₂) :=
by
  classical
  let F₁ : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin M₁ → ZMod 2) :=
    AddMonoidHom.toZModLinearMap 2 (AddMonoidHom.mk' f₁ hf₁)
  let F₂ : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin M₂ → ZMod 2) :=
    AddMonoidHom.toZModLinearMap 2 (AddMonoidHom.mk' f₂ hf₂)
  let F : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin M₁ → ZMod 2) × (Fin M₂ → ZMod 2) :=
    F₁.prod F₂
  have hF_apply : ∀ α, F α = (f₁ α, f₂ α) := fun _ => rfl
  have hF_ker : ∀ α, α ∈ F.ker ↔ f₁ α = 0 ∧ f₂ α = 0 := by
    intro α
    rw [LinearMap.mem_ker, hF_apply, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]
  have h_neg : ∀ α : Fin N → ZMod 2, -α = α := by
    intro α
    funext i
    exact CharTwo.neg_eq (α i)
  have h_sub : ∀ α β : Fin N → ZMod 2, α - β = α + β := by
    intro α β
    funext i
    exact CharTwo.sub_eq_add (α i) (β i)
  let K₀_add : AddSubgroup ↥F.ker :=
    { carrier := { x : ↥F.ker | Sq₀ x.1 }
      zero_mem' := hSq_zero
      add_mem' := fun {x y} hx hy => hSq_add x.1 y.1 hx hy
      neg_mem' := by
        intro x hx
        change Sq₀ (-x.1)
        rwa [h_neg] }
  let K₀ : Submodule (ZMod 2) ↥F.ker := AddSubgroup.toZModSubmodule 2 K₀_add
  let φ (β : Fin N → ZMod 2) :
      ((Fin M₁ → ZMod 2) × (Fin M₂ → ZMod 2)) →ₗ[ZMod 2] ZMod 2 :=
    AddMonoidHom.toZModLinearMap 2
      (AddMonoidHom.mk'
        (fun u => dotProduct (g₁ β) u.1 + dotProduct (g₂ β) u.2)
        (fun u v => by
          change dotProduct (g₁ β) (u.1 + v.1) + dotProduct (g₂ β) (u.2 + v.2) = _
          rw [dotProduct_add, dotProduct_add, add_add_add_comm]))
  have hφ_apply (β : Fin N → ZMod 2) (u : (Fin M₁ → ZMod 2) × (Fin M₂ → ZMod 2)) :
      φ β u = dotProduct (g₁ β) u.1 + dotProduct (g₂ β) u.2 := rfl
  let ψ : ↥K₀ → ↥F.range.dualAnnihilator := fun x =>
    ⟨φ x.1.1, by
      rw [Submodule.mem_dualAnnihilator]
      rintro w ⟨α, rfl⟩
      have hx_ker := (hF_ker x.1.1).mp x.1.2
      exact horth x.1.1 α hx_ker.1 hx_ker.2 x.2⟩
  have hψ_inj : Function.Injective ψ := by
    intro x y hxy
    have hφ_eq : ∀ u, φ x.1.1 u = φ y.1.1 u := by
      intro u
      exact congrFun (congrArg DFunLike.coe (Subtype.mk.inj hxy)) u
    have hg₁_eq : g₁ x.1.1 = g₁ y.1.1 := by
      funext i
      have h := hφ_eq (Pi.single i 1, 0)
      simpa only [hφ_apply, dotProduct_zero, add_zero, dotProduct_single, mul_one] using h
    have hg₂_eq : g₂ x.1.1 = g₂ y.1.1 := by
      funext j
      have h := hφ_eq (0, Pi.single j 1)
      simpa only [hφ_apply, dotProduct_zero, zero_add, dotProduct_single, mul_one] using h
    have hx_ker := (hF_ker x.1.1).mp x.1.2
    have hy_ker := (hF_ker y.1.1).mp y.1.2
    have hxy_val : x.1.1 = y.1.1 :=
      hinj x.1.1 y.1.1 hx_ker.1 hx_ker.2 hy_ker.1 hy_ker.2
        (hSq_add x.1.1 y.1.1 x.2 y.2) hg₁_eq hg₂_eq
    exact Subtype.ext (Subtype.ext hxy_val)
  haveI : Finite ↥F.range.dualAnnihilator := DFunLike.finite ↥F.range.dualAnnihilator
  have h_card_le : Nat.card ↥K₀ ≤ Nat.card ↥F.range.dualAnnihilator :=
    Nat.card_le_card_of_injective ψ hψ_inj
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥K₀),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥F.range.dualAnnihilator),
      Nat.card_zmod] at h_card_le
  have h_finrank_K₀_le :
      Module.finrank (ZMod 2) ↥K₀ ≤ Module.finrank (ZMod 2) ↥F.range.dualAnnihilator :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h_card_le
  have h_rn :
      Module.finrank (ZMod 2) ↥F.range + Module.finrank (ZMod 2) ↥F.ker = N := by
    rw [LinearMap.finrank_range_add_finrank_ker F, Module.finrank_fin_fun (ZMod 2)]
  have h_da :
      Module.finrank (ZMod 2) ↥F.range +
        Module.finrank (ZMod 2) ↥F.range.dualAnnihilator = M₁ + M₂ := by
    rw [Subspace.finrank_add_finrank_dualAnnihilator_eq F.range,
        Module.finrank_prod, Module.finrank_fin_fun (ZMod 2), Module.finrank_fin_fun (ZMod 2)]
  have h_quot :
      Module.finrank (ZMod 2) (↥F.ker ⧸ K₀) + Module.finrank (ZMod 2) ↥K₀ =
        Module.finrank (ZMod 2) ↥F.ker :=
    Submodule.finrank_quotient_add_finrank K₀
  have h_finrank_Q : 2 ≤ Module.finrank (ZMod 2) (↥F.ker ⧸ K₀) := by omega
  have h_card_Q : 4 ≤ Fintype.card (↥F.ker ⧸ K₀) := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card 2]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ Module.finrank (ZMod 2) (↥F.ker ⧸ K₀) :=
        Nat.pow_le_pow_right (by norm_num) h_finrank_Q
  let S_ne : Finset (↥F.ker ⧸ K₀) := (Finset.univ : Finset (↥F.ker ⧸ K₀)).erase 0
  have hS_card : 1 < S_ne.card := by
    have h_erase : S_ne.card = Fintype.card (↥F.ker ⧸ K₀) - 1 := by
      dsimp [S_ne]
      rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
    omega
  obtain ⟨q₁, q₂, hq₁, hq₂, hq₁₂⟩ := Finset.one_lt_card_iff.mp hS_card
  have hq₁_ne : q₁ ≠ 0 := (Finset.mem_erase.mp hq₁).1
  have hq₂_ne : q₂ ≠ 0 := (Finset.mem_erase.mp hq₂).1
  obtain ⟨x₁, rfl⟩ := Submodule.Quotient.mk_surjective K₀ q₁
  obtain ⟨x₂, rfl⟩ := Submodule.Quotient.mk_surjective K₀ q₂
  have hx₁_ker := (hF_ker x₁.1).mp x₁.2
  have hx₂_ker := (hF_ker x₂.1).mp x₂.2
  refine ⟨x₁.1, x₂.1, hx₁_ker.1, hx₁_ker.2, hx₂_ker.1, hx₂_ker.2, ?_, ?_, ?_⟩
  · intro hSq₁
    exact hq₁_ne ((Submodule.Quotient.mk_eq_zero K₀).mpr hSq₁)
  · intro hSq₂
    exact hq₂_ne ((Submodule.Quotient.mk_eq_zero K₀).mpr hSq₂)
  · intro hSq₁₂
    apply hq₁₂
    rw [Submodule.Quotient.eq]
    change Sq₀ (x₁.1 - x₂.1)
    rwa [h_sub]

theorem exists_independent_in_selmerStructRelax_at_v0 {K : Type u} [Field K] [NumberField K]
    (a₁ a₂ a₃ : K) (h₁₂ : a₁ ≠ a₂) (h₁₃ : a₁ ≠ a₃) (h₂₃ : a₂ ≠ a₃)
    (hint₁ : IsIntegral ℤ a₁) (hint₂ : IsIntegral ℤ a₂) (hint₃ : IsIntegral ℤ a₃)
    (T S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hT : IsGoodT a₁ a₂ a₃ T) (hSdisj : Disjoint S T)
    (π : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        v.adicCompletion K)
    (hπ : ∀ v ∈ S, IsLocalUnif v (π v))
    (v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hv₀T : v₀ ∉ T) (hv₀S : v₀ ∉ S) :
    ∃ p q : Kˣ × Kˣ,
      (sqCl p.1, sqCl p.2) ∈ selmerStructRelax K a₁ a₂ a₃ T S π v₀ ∧
      (sqCl q.1, sqCl q.2) ∈ selmerStructRelax K a₁ a₂ a₃ T S π v₀ ∧
      ¬ (IsSquare (algebraMap K (v₀.adicCompletion K) (p.1 : K)) ∧
         IsSquare (algebraMap K (v₀.adicCompletion K) (p.2 : K))) ∧
      ¬ (IsSquare (algebraMap K (v₀.adicCompletion K) (q.1 : K)) ∧
         IsSquare (algebraMap K (v₀.adicCompletion K) (q.2 : K))) ∧
      ¬ (IsSquare (algebraMap K (v₀.adicCompletion K) ((p.1 * q.1 : Kˣ) : K)) ∧
         IsSquare (algebraMap K (v₀.adicCompletion K) ((p.2 * q.2 : Kˣ) : K))) :=
by
  classical
  obtain ⟨S_out, P, hS_sub, hS_disj, hv₀S_out, hP_zero, hP_add, hP_even, hP_inj⟩ :=
    exists_sUnit_basis_and_loc_inj a₁ a₂ a₃ h₁₂ h₁₃ h₂₃ hint₁ hint₂ hint₃ T S hT hSdisj v₀ hv₀T hv₀S
  obtain ⟨Φ_out, Ψ_out, hΦ_out_sq, hΦ_out_mul, hΦ_out_zero, hΨ_out_inj, hΦ_out_pair⟩ :=
    local_selmer_basis_outside_T a₁ a₂ a₃ h₁₂ h₁₃ h₂₃ hint₁ hint₂ hint₃ T S S_out hT hS_sub hS_disj π hπ
  obtain ⟨Φ_T, Ψ_T, hΦ_T_sq, hΦ_T_mul, hΦ_T_zero, hΨ_T_inj, hΦ_T_pair⟩ :=
    local_selmer_basis_on_T a₁ a₂ a₃ h₁₂ h₁₃ h₂₃ hint₁ hint₂ hint₃ T hT
  let N := 2 * (NumberField.InfinitePlace.nrRealPlaces K +
    NumberField.InfinitePlace.nrComplexPlaces K + T.card + S_out.card + 1)
  let M₁ := 2 * T.card + NumberField.InfinitePlace.nrRealPlaces K +
    2 * NumberField.InfinitePlace.nrComplexPlaces K
  let M₂ := NumberField.InfinitePlace.nrRealPlaces K + 2 * S_out.card
  have hM : M₁ + M₂ + 2 = N := by
    dsimp [N, M₁, M₂]
    ring
  let f₁ : (Fin N → ZMod 2) → (Fin M₁ → ZMod 2) := fun α => Φ_T (P α)
  let g₁ : (Fin N → ZMod 2) → (Fin M₁ → ZMod 2) := fun α => Ψ_T (P α)
  let f₂ : (Fin N → ZMod 2) → (Fin M₂ → ZMod 2) := fun α => Φ_out (P α)
  let g₂ : (Fin N → ZMod 2) → (Fin M₂ → ZMod 2) := fun α => Ψ_out (P α)
  let Sq₀ : (Fin N → ZMod 2) → Prop := fun α =>
    IsSquare (algebraMap K (v₀.adicCompletion K) ((P α).1 : K)) ∧
    IsSquare (algebraMap K (v₀.adicCompletion K) ((P α).2 : K))
  have unit_map_ne_zero : ∀ (u : Kˣ), algebraMap K (v₀.adicCompletion K) (u : K) ≠ 0 := by
    intro u
    rw [ne_eq, map_eq_zero]
    exact u.ne_zero
  have isSquare_iff_of_isSquare_mul : ∀ {a b : v₀.adicCompletion K},
      a ≠ 0 → b ≠ 0 → IsSquare (a * b) → (IsSquare a ↔ IsSquare b) := by
    intro a b ha hb ⟨s, hs⟩
    constructor
    · rintro ⟨r, rfl⟩
      have hr : r ≠ 0 := fun h => ha (by rw [h, mul_zero])
      refine ⟨s / r, ?_⟩
      calc b = (r * r * b) / (r * r) := by field_simp [hr]
        _ = (s * s) / (r * r) := by rw [hs]
        _ = (s / r) * (s / r) := by ring
    · rintro ⟨r, rfl⟩
      have hr : r ≠ 0 := fun h => hb (by rw [h, mul_zero])
      refine ⟨s / r, ?_⟩
      calc a = (a * (r * r)) / (r * r) := by field_simp [hr]
        _ = (s * s) / (r * r) := by rw [hs]
        _ = (s / r) * (s / r) := by ring
  have hSq_iff : ∀ α β : Fin N → ZMod 2,
      Sq₀ (α + β) ↔
        IsSquare (algebraMap K (v₀.adicCompletion K) (((P α).1 * (P β).1 : Kˣ) : K)) ∧
        IsSquare (algebraMap K (v₀.adicCompletion K) (((P α).2 * (P β).2 : Kˣ) : K)) := by
    intro α β
    obtain ⟨h1, h2⟩ := hP_add α β
    have h1' : IsSquare (algebraMap K (v₀.adicCompletion K) ((P (α + β)).1 : K) *
        algebraMap K (v₀.adicCompletion K) (((P α).1 * (P β).1 : Kˣ) : K)) := by
      rw [← map_mul]
      exact h1.map (algebraMap K (v₀.adicCompletion K))
    have h2' : IsSquare (algebraMap K (v₀.adicCompletion K) ((P (α + β)).2 : K) *
        algebraMap K (v₀.adicCompletion K) (((P α).2 * (P β).2 : Kˣ) : K)) := by
      rw [← map_mul]
      exact h2.map (algebraMap K (v₀.adicCompletion K))
    exact and_congr
      (isSquare_iff_of_isSquare_mul (unit_map_ne_zero _) (unit_map_ne_zero _) h1')
      (isSquare_iff_of_isSquare_mul (unit_map_ne_zero _) (unit_map_ne_zero _) h2')
  have hf₁ : ∀ α β, f₁ (α + β) = f₁ α + f₁ β := by
    intro α β
    dsimp [f₁]
    rw [hΦ_T_sq (P (α + β)) ((P α).1 * (P β).1, (P α).2 * (P β).2) (hP_add α β).1 (hP_add α β).2]
    exact hΦ_T_mul (P α) (P β)
  have hf₂ : ∀ α β, f₂ (α + β) = f₂ α + f₂ β := by
    intro α β
    dsimp [f₂]
    rw [hΦ_out_sq (P (α + β)) ((P α).1 * (P β).1, (P α).2 * (P β).2) (hP_add α β).1 (hP_add α β).2]
    exact hΦ_out_mul (P α) (P β)
  have hSq_zero : Sq₀ 0 := by
    dsimp [Sq₀]
    rw [hP_zero]
    simp only [Units.val_one, map_one, IsSquare.one, and_self]
  have hSq_add : ∀ α β, Sq₀ α → Sq₀ β → Sq₀ (α + β) := by
    intro α β hα hβ
    rw [hSq_iff]
    simp only [Units.val_mul, map_mul]
    exact ⟨hα.1.mul hβ.1, hα.2.mul hβ.2⟩
  have hinj : ∀ β₁ β₂, f₁ β₁ = 0 → f₂ β₁ = 0 → f₁ β₂ = 0 → f₂ β₂ = 0 →
      Sq₀ (β₁ + β₂) → g₁ β₁ = g₁ β₂ → g₂ β₁ = g₂ β₂ → β₁ = β₂ := by
    intro β₁ β₂ hf1_1 hf2_1 hf1_2 hf2_2 hSq12 hg1 hg2
    have hT_sq := hΨ_T_inj (P β₁) (P β₂) hf1_1 hf1_2 hg1
    have hout_sq := hΨ_out_inj (P β₁) (P β₂) hf2_1 hf2_2 hg2
    have hv0_sq := (hSq_iff β₁ β₂).mp hSq12
    apply hP_inj β₁ β₂
    · intro v hv
      rcases hv with hvT | hvS | rfl
      · exact hT_sq v hvT
      · exact hout_sq.1 v hvS
      · exact hv0_sq
    · exact hout_sq.2
  have hilbLoc_of_isSquare_left : ∀ (a b : v₀.adicCompletion K),
      a ≠ 0 → IsSquare a → hilbLoc v₀ a b = 1 := by
    rintro a b ha ⟨r, rfl⟩
    have hr : r ≠ 0 := fun h => ha (by rw [h, mul_zero])
    simp only [hilbLoc]
    rw [if_pos]
    refine ⟨1 / r, 0, ?_⟩
    field_simp [hr]
    ring
  have hilbFin_v0_of_isSquare_left : ∀ (u w : Kˣ),
      IsSquare (algebraMap K (v₀.adicCompletion K) (u : K)) →
      hilbFin v₀ (u : K) (w : K) = 1 := by
    intro u w hsq
    exact hilbLoc_of_isSquare_left _ _ (unit_map_ne_zero u) hsq
  have zmod2_add_eq_zero_of_neg_one_pow_mul : ∀ (x y : ZMod 2),
      (-1 : ℤˣ) ^ x.val * (-1 : ℤˣ) ^ y.val = 1 → x + y = 0 := by
    intro x y
    fin_cases x <;> fin_cases y <;> decide
  have horth : ∀ β α, f₁ β = 0 → f₂ β = 0 → Sq₀ β →
      dotProduct (g₁ β) (f₁ α) + dotProduct (g₂ β) (f₂ α) = 0 := by
    intro β α hf1 hf2 hSq
    let q := P β
    let p := P α
    have hrec1 := hilbert_reciprocity q.1 p.2
    have hrec2 := hilbert_reciprocity q.2 p.1
    have hprod_global :
        (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          (hilbFin v (q.1 : K) (p.2 : K) * hilbFin v (q.2 : K) (p.1 : K))) *
        (∏ w : NumberField.InfinitePlace K,
          (hilbInf w (q.1 : K) (p.2 : K) * hilbInf w (q.2 : K) (p.1 : K))) = 1 := by
      rw [finprod_mul_distrib hrec1.1 hrec2.1, Finset.prod_mul_distrib]
      calc
        ((∏ᶠ v, hilbFin v (q.1 : K) (p.2 : K)) * (∏ᶠ v, hilbFin v (q.2 : K) (p.1 : K))) *
          ((∏ w, hilbInf w (q.1 : K) (p.2 : K)) * (∏ w, hilbInf w (q.2 : K) (p.1 : K)))
        = ((∏ᶠ v, hilbFin v (q.1 : K) (p.2 : K)) * (∏ w, hilbInf w (q.1 : K) (p.2 : K))) *
          ((∏ᶠ v, hilbFin v (q.2 : K) (p.1 : K)) * (∏ w, hilbInf w (q.2 : K) (p.1 : K))) :=
            mul_mul_mul_comm _ _ _ _
        _ = 1 * 1 := by rw [hrec1.2, hrec2.2]
        _ = 1 := mul_one 1
    have hsupp : Function.mulSupport
        (fun v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
          hilbFin v (q.1 : K) (p.2 : K) * hilbFin v (q.2 : K) (p.1 : K)) ⊆
        ((T ∪ S_out : Finset _) : Set _) := by
      intro v hv
      rw [Function.mem_mulSupport] at hv
      by_contra hv_not
      rw [Finset.mem_coe, Finset.mem_union, not_or] at hv_not
      rcases hv_not with ⟨hvT, hvS_out⟩
      apply hv
      by_cases hv₀ : v = v₀
      · subst hv₀
        rw [hilbFin_v0_of_isSquare_left q.1 p.2 hSq.1,
            hilbFin_v0_of_isSquare_left q.2 p.1 hSq.2, mul_one]
      · have hq_ev := hP_even β v hvT hvS_out hv₀
        have hp_ev := hP_even α v hvT hvS_out hv₀
        rw [hilbFin_eq_one_of_evenVal_outside_T a₁ a₂ a₃ h₁₂ h₁₃ h₂₃ hint₁ hint₂ hint₃ T hT
              v hvT q.1 p.2 hq_ev.1 hp_ev.2,
            hilbFin_eq_one_of_evenVal_outside_T a₁ a₂ a₃ h₁₂ h₁₃ h₂₃ hint₁ hint₂ hint₃ T hT
              v hvT q.2 p.1 hq_ev.2 hp_ev.1, mul_one]
    rw [finprod_eq_prod_of_mulSupport_subset _ hsupp, Finset.prod_union hS_disj.symm,
        mul_assoc, hΦ_T_pair q p hf1, hΦ_out_pair q p hf2] at hprod_global
    exact zmod2_add_eq_zero_of_neg_one_pow_mul _ _ hprod_global
  obtain ⟨α₁, α₂, hf1_α₁, hf2_α₁, hf1_α₂, hf2_α₂, hnsq_α₁, hnsq_α₂, hnsq_α₁₂⟩ :=
    exists_independent_of_orthogonal_syndrome N M₁ M₂ hM f₁ g₁ f₂ g₂ Sq₀
      hf₁ hf₂ hSq_zero hSq_add hinj horth
  refine ⟨P α₁, P α₂, ?_, ?_, hnsq_α₁, hnsq_α₂, ?_⟩
  · refine ⟨P α₁, ⟨(hΦ_T_zero (P α₁)).mp hf1_α₁, ((hΦ_out_zero (P α₁)).mp hf2_α₁).1,
      ((hΦ_out_zero (P α₁)).mp hf2_α₁).2.1, ?_⟩, rfl⟩
    intro v hvT hvS hv₀
    by_cases hvS_out : v ∈ S_out
    · exact ((hΦ_out_zero (P α₁)).mp hf2_α₁).2.2 v hvS_out hvS
    · exact hP_even α₁ v hvT hvS_out hv₀
  · refine ⟨P α₂, ⟨(hΦ_T_zero (P α₂)).mp hf1_α₂, ((hΦ_out_zero (P α₂)).mp hf2_α₂).1,
      ((hΦ_out_zero (P α₂)).mp hf2_α₂).2.1, ?_⟩, rfl⟩
    intro v hvT hvS hv₀
    by_cases hvS_out : v ∈ S_out
    · exact ((hΦ_out_zero (P α₂)).mp hf2_α₂).2.2 v hvS_out hvS
    · exact hP_even α₂ v hvT hvS_out hv₀
  · rwa [← hSq_iff α₁ α₂]

theorem theorem_4_5 {K : Type u} [Field K] [NumberField K] (a₁ a₂ a₃ : K)
    (h₁₂ : a₁ ≠ a₂) (h₁₃ : a₁ ≠ a₃) (h₂₃ : a₂ ≠ a₃)
    (hint₁ : IsIntegral ℤ a₁) (hint₂ : IsIntegral ℤ a₂) (hint₃ : IsIntegral ℤ a₃)
    (T S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hT : IsGoodT a₁ a₂ a₃ T) (hSdisj : Disjoint S T)
    (π : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        v.adicCompletion K)
    (hπ : ∀ v ∈ S, IsLocalUnif v (π v))
    (v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hv₀T : v₀ ∉ T) (hv₀S : v₀ ∉ S)
    (d₁ d₂ : v₀.adicCompletion K) (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) :
    ((∀ p : Kˣ × Kˣ,
        (sqCl p.1, sqCl p.2) ∈ selmerStructRelax K a₁ a₂ a₃ T S π v₀ →
        hilbLoc v₀ d₁ (algebraMap K (v₀.adicCompletion K) (p.2 : K)) *
          hilbLoc v₀ d₂ (algebraMap K (v₀.adicCompletion K) (p.1 : K)) = 1)
     ↔ (∃ p : Kˣ × Kˣ,
        (sqCl p.1, sqCl p.2) ∈ selmerStructRelax K a₁ a₂ a₃ T S π v₀ ∧
        IsSquare (d₁ * algebraMap K (v₀.adicCompletion K) (p.1 : K)) ∧
        IsSquare (d₂ * algebraMap K (v₀.adicCompletion K) (p.2 : K)))) :=
by
  have unit_map_ne_zero : ∀ (u : Kˣ), algebraMap K (v₀.adicCompletion K) (u : K) ≠ 0 := by
    intro u
    rw [ne_eq, map_eq_zero]
    exact u.ne_zero
  have hilbLoc_symm : ∀ (a b : v₀.adicCompletion K), hilbLoc v₀ a b = hilbLoc v₀ b a := by
    intro a b
    simp only [hilbLoc]
    congr 1
    exact propext ⟨fun ⟨x, y, hxy⟩ => ⟨y, x, by linear_combination hxy⟩,
      fun ⟨x, y, hxy⟩ => ⟨y, x, by linear_combination hxy⟩⟩
  have hilbLoc_congr_left : ∀ (d q b : v₀.adicCompletion K),
      d ≠ 0 → q ≠ 0 → IsSquare (d * q) → hilbLoc v₀ d b = hilbLoc v₀ q b := by
    have aux : ∀ (d q b : v₀.adicCompletion K), d ≠ 0 → q ≠ 0 → IsSquare (d * q) →
        (∃ x y : v₀.adicCompletion K, d * x ^ 2 + b * y ^ 2 = 1) →
        (∃ x y : v₀.adicCompletion K, q * x ^ 2 + b * y ^ 2 = 1) := by
      intro d q b hd hq ⟨s, hs⟩ ⟨x, y, hxy⟩
      refine ⟨s * x / q, y, ?_⟩
      have hsq : s ^ 2 = d * q := by linear_combination -hs
      have h1 : q * (s * x / q) ^ 2 = d * x ^ 2 := by
        calc q * (s * x / q) ^ 2 = s ^ 2 * x ^ 2 / q := by
              field_simp [hq]
          _ = (d * q) * x ^ 2 / q := by rw [hsq]
          _ = d * x ^ 2 := by field_simp [hq]
      linear_combination h1 + hxy
    intro d q b hd hq hsq
    have hsq' : IsSquare (q * d) := by rwa [mul_comm]
    simp only [hilbLoc]
    congr 1
    exact propext ⟨aux d q b hd hq hsq, aux q d b hq hd hsq'⟩
  have hilbLoc_congr_right : ∀ (a d q : v₀.adicCompletion K),
      d ≠ 0 → q ≠ 0 → IsSquare (d * q) → hilbLoc v₀ a d = hilbLoc v₀ a q := by
    intro a d q hd hq hsq
    rw [hilbLoc_symm a d, hilbLoc_symm a q]
    exact hilbLoc_congr_left d q a hd hq hsq
  have isSquare_mul_of_sqCl_eq : ∀ (x y : Kˣ), sqCl x = sqCl y →
      IsSquare (algebraMap K (v₀.adicCompletion K) (x : K) *
        algebraMap K (v₀.adicCompletion K) (y : K)) := by
    intro x y hxy
    unfold sqCl at hxy
    rw [QuotientGroup.eq] at hxy
    rcases hxy with ⟨u, hu⟩
    change u ^ 2 = x⁻¹ * y at hu
    have hy : (y : K) = (x : K) * (u : K) ^ 2 := by
      have hu' : y = x * u ^ 2 := by
        calc y = x * (x⁻¹ * y) := by group
          _ = x * u ^ 2 := by rw [← hu]
      exact_mod_cast hu'
    refine ⟨algebraMap K (v₀.adicCompletion K) ((x : K) * (u : K)), ?_⟩
    rw [hy]
    push_cast
    ring
  have selmer_orth_at_v0 : ∀ (q p : Kˣ × Kˣ),
      (sqCl q.1, sqCl q.2) ∈ selmerStructRelax K a₁ a₂ a₃ T S π v₀ →
      (sqCl p.1, sqCl p.2) ∈ selmerStructRelax K a₁ a₂ a₃ T S π v₀ →
      hilbLoc v₀ (algebraMap K (v₀.adicCompletion K) (q.1 : K))
        (algebraMap K (v₀.adicCompletion K) (p.2 : K)) *
      hilbLoc v₀ (algebraMap K (v₀.adicCompletion K) (q.2 : K))
        (algebraMap K (v₀.adicCompletion K) (p.1 : K)) = 1 := by
    intro q p hq hp
    rcases hq with ⟨q', ⟨hq'T, hq'Inf, hq'S, hq'U⟩, hq'eq⟩
    rcases hp with ⟨p', ⟨hp'T, hp'Inf, hp'S, hp'U⟩, hp'eq⟩
    injection hq'eq with hq'1 hq'2
    injection hp'eq with hp'1 hp'2
    have hrec1 := hilbert_reciprocity q'.1 p'.2
    have hrec2 := hilbert_reciprocity q'.2 p'.1
    have hprod_global :
        (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          (hilbFin v (q'.1 : K) (p'.2 : K) * hilbFin v (q'.2 : K) (p'.1 : K))) *
        (∏ w : NumberField.InfinitePlace K,
          (hilbInf w (q'.1 : K) (p'.2 : K) * hilbInf w (q'.2 : K) (p'.1 : K))) = 1 := by
      rw [finprod_mul_distrib hrec1.1 hrec2.1, Finset.prod_mul_distrib]
      calc
        ((∏ᶠ v, hilbFin v (q'.1 : K) (p'.2 : K)) * (∏ᶠ v, hilbFin v (q'.2 : K) (p'.1 : K))) *
          ((∏ w, hilbInf w (q'.1 : K) (p'.2 : K)) * (∏ w, hilbInf w (q'.2 : K) (p'.1 : K)))
        = ((∏ᶠ v, hilbFin v (q'.1 : K) (p'.2 : K)) * (∏ w, hilbInf w (q'.1 : K) (p'.2 : K))) *
          ((∏ᶠ v, hilbFin v (q'.2 : K) (p'.1 : K)) * (∏ w, hilbInf w (q'.2 : K) (p'.1 : K))) :=
            mul_mul_mul_comm _ _ _ _
        _ = 1 * 1 := by rw [hrec1.2, hrec2.2]
        _ = 1 := mul_one 1
    have hinf_one : (∏ w : NumberField.InfinitePlace K,
        (hilbInf w (q'.1 : K) (p'.2 : K) * hilbInf w (q'.2 : K) (p'.1 : K))) = 1 := by
      apply Finset.prod_eq_one
      intro w _
      exact hilbInf_pairing_eq_one_of_isDescentClass a₁ a₂ a₃ h₁₂ h₁₃ h₂₃ w
        q'.1 q'.2 p'.1 p'.2 (hq'Inf w) (hp'Inf w)
    have hfin_one : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        v ≠ v₀ → hilbFin v (q'.1 : K) (p'.2 : K) * hilbFin v (q'.2 : K) (p'.1 : K) = 1 := by
      intro v hv₀
      by_cases hvT : v ∈ T
      · exact hilbFin_pairing_eq_one_of_isDescentClass a₁ a₂ a₃ h₁₂ h₁₃ h₂₃ v
          q'.1 q'.2 p'.1 p'.2 (hq'T v hvT) (hp'T v hvT)
      · by_cases hvS : v ∈ S
        · exact hilbFin_pairing_eq_one_of_ramLocal a₁ a₂ a₃ h₁₂ h₁₃ h₂₃ hint₁ hint₂ hint₃
            T hT v hvT (π v) (hπ v hvS) q'.1 q'.2 p'.1 p'.2 (hq'S v hvS) (hp'S v hvS)
        · have hq'v := hq'U v hvT hvS hv₀
          have hp'v := hp'U v hvT hvS hv₀
          have h1 := hilbFin_eq_one_of_evenVal_outside_T a₁ a₂ a₃ h₁₂ h₁₃ h₂₃
            hint₁ hint₂ hint₃ T hT v hvT q'.1 p'.2 hq'v.1 hp'v.2
          have h2 := hilbFin_eq_one_of_evenVal_outside_T a₁ a₂ a₃ h₁₂ h₁₃ h₂₃
            hint₁ hint₂ hint₃ T hT v hvT q'.2 p'.1 hq'v.2 hp'v.1
          rw [h1, h2, mul_one]
    have hv0_q'p' : hilbFin v₀ (q'.1 : K) (p'.2 : K) * hilbFin v₀ (q'.2 : K) (p'.1 : K) = 1 := by
      rw [finprod_eq_single _ v₀ hfin_one, hinf_one, mul_one] at hprod_global
      exact hprod_global
    simp only [hilbFin] at hv0_q'p'
    have hcongr1 : hilbLoc v₀ (algebraMap K (v₀.adicCompletion K) (q.1 : K))
        (algebraMap K (v₀.adicCompletion K) (p.2 : K)) =
      hilbLoc v₀ (algebraMap K (v₀.adicCompletion K) (q'.1 : K))
        (algebraMap K (v₀.adicCompletion K) (p'.2 : K)) := by
      rw [hilbLoc_congr_left _ _ _ (unit_map_ne_zero q.1) (unit_map_ne_zero q'.1)
        (isSquare_mul_of_sqCl_eq q.1 q'.1 hq'1.symm)]
      exact hilbLoc_congr_right _ _ _ (unit_map_ne_zero p.2) (unit_map_ne_zero p'.2)
        (isSquare_mul_of_sqCl_eq p.2 p'.2 hp'2.symm)
    have hcongr2 : hilbLoc v₀ (algebraMap K (v₀.adicCompletion K) (q.2 : K))
        (algebraMap K (v₀.adicCompletion K) (p.1 : K)) =
      hilbLoc v₀ (algebraMap K (v₀.adicCompletion K) (q'.2 : K))
        (algebraMap K (v₀.adicCompletion K) (p'.1 : K)) := by
      rw [hilbLoc_congr_left _ _ _ (unit_map_ne_zero q.2) (unit_map_ne_zero q'.2)
        (isSquare_mul_of_sqCl_eq q.2 q'.2 hq'2.symm)]
      exact hilbLoc_congr_right _ _ _ (unit_map_ne_zero p.1) (unit_map_ne_zero p'.1)
        (isSquare_mul_of_sqCl_eq p.1 p'.1 hp'1.symm)
    rw [hcongr1, hcongr2]
    exact hv0_q'p'
  constructor
  · intro horth
    obtain ⟨p, q, hp_mem, hq_mem, hp_nsq, hq_nsq, hpq_nsq⟩ :=
      exists_independent_in_selmerStructRelax_at_v0 a₁ a₂ a₃ h₁₂ h₁₃ h₂₃
        hint₁ hint₂ hint₃ T S hT hSdisj π hπ v₀ hv₀T hv₀S
    have hmul := selmerStructRelax_mul_mem a₁ a₂ a₃ h₁₂ h₁₃ h₂₃
      hint₁ hint₂ hint₃ T S hT hSdisj π hπ v₀
    have hpq_nsq' : ¬ (IsSquare (algebraMap K (v₀.adicCompletion K) (p.1 : K) *
        algebraMap K (v₀.adicCompletion K) (q.1 : K)) ∧
      IsSquare (algebraMap K (v₀.adicCompletion K) (p.2 : K) *
        algebraMap K (v₀.adicCompletion K) (q.2 : K))) := by
      simpa only [Units.val_mul, map_mul] using hpq_nsq
    have hcases := isSquare_of_hilbLoc_orth_of_independent a₁ a₂ a₃ h₁₂ h₁₃ h₂₃
      hint₁ hint₂ hint₃ T hT v₀ hv₀T
      (algebraMap K (v₀.adicCompletion K) (p.1 : K))
      (algebraMap K (v₀.adicCompletion K) (p.2 : K))
      (algebraMap K (v₀.adicCompletion K) (q.1 : K))
      (algebraMap K (v₀.adicCompletion K) (q.2 : K))
      d₁ d₂
      (unit_map_ne_zero p.1) (unit_map_ne_zero p.2)
      (unit_map_ne_zero q.1) (unit_map_ne_zero q.2)
      hd₁ hd₂
      hp_nsq hq_nsq hpq_nsq'
      (selmer_orth_at_v0 p q hp_mem hq_mem)
      (horth p hp_mem) (horth q hq_mem)
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨(1, 1), hmul.1, ?_, ?_⟩
      · simpa only [Units.val_one, map_one, mul_one] using h1
      · simpa only [Units.val_one, map_one, mul_one] using h2
    · exact ⟨p, hp_mem, h1, h2⟩
    · exact ⟨q, hq_mem, h1, h2⟩
    · refine ⟨(p.1 * q.1, p.2 * q.2), hmul.2 p q hp_mem hq_mem, ?_, ?_⟩
      · simpa only [Units.val_mul, map_mul] using h1
      · simpa only [Units.val_mul, map_mul] using h2
  · rintro ⟨q, hq_mem, hq1, hq2⟩ p hp_mem
    rw [hilbLoc_congr_left d₁ (algebraMap K (v₀.adicCompletion K) (q.1 : K))
          (algebraMap K (v₀.adicCompletion K) (p.2 : K)) hd₁ (unit_map_ne_zero q.1) hq1,
        hilbLoc_congr_left d₂ (algebraMap K (v₀.adicCompletion K) (q.2 : K))
          (algebraMap K (v₀.adicCompletion K) (p.1 : K)) hd₂ (unit_map_ne_zero q.2) hq2]
    exact selmer_orth_at_v0 q p hq_mem hp_mem
