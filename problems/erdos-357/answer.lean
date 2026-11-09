import Mathlib
set_option maxHeartbeats 4000000

namespace Erdos357
open Filter Asymptotics
def HasDistinctSums {ι α : Type*} [Preorder ι] [AddCommMonoid α] (a : ι → α) : Prop :=
  {J : Finset ι | (J : Set ι).OrdConnected}.InjOn (fun J ↦ ∑ x ∈ J, a x)
/-- Let $f(n)$ be the maximal $k$ such that there exist integers $1 \le a_1 < \dotsc < a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : Fin k → ℤ, Set.range a ⊆ Set.Icc 1 n ∧ StrictMono a ∧ HasDistinctSums a}
/-- Let $g(n)$ be the maximal $k$ such that there exist integers $1 \le a_1, \dotsc, a_k \le n$
such that all sums of the shape $\sum_{u \le i \le v} a_i$ are distinct. -/
noncomputable def g (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : Fin k → ℕ, (Set.range a ⊆ Set.Icc 1 n) ∧ HasDistinctSums a}
open MeasureTheory
open Polynomial
open scoped BigOperators
open scoped Classical
open scoped ENNReal
open scoped EuclideanGeometry
open scoped InnerProductSpace
open scoped intervalIntegral
open scoped List
open scoped Matrix
open scoped Nat
open scoped NNReal
open scoped Pointwise
open scoped ProbabilityTheory
open scoped Real
open scoped symmDiff
open scoped Topology

theorem erdos357_g_spec (n : ℕ) :
    g n ≤ n ∧
    (∀ (k : ℕ) (a : Fin k → ℕ), Set.range a ⊆ Set.Icc 1 n → HasDistinctSums a → k ≤ g n) ∧
    (∃ a : Fin (g n) → ℕ, Set.range a ⊆ Set.Icc 1 n ∧ HasDistinctSums a) :=
by
  classical
  
  have hinj : ∀ (k : ℕ) (a : Fin k → ℕ), HasDistinctSums a → Function.Injective a := by
    intro k a hd i j hij
    have hmi : ({i} : Finset (Fin k)) ∈ {J : Finset (Fin k) | (J : Set (Fin k)).OrdConnected} := by
      show ((({i} : Finset (Fin k)) : Set (Fin k))).OrdConnected
      rw [Finset.coe_singleton]
      exact Set.ordConnected_singleton
    have hmj : ({j} : Finset (Fin k)) ∈ {J : Finset (Fin k) | (J : Set (Fin k)).OrdConnected} := by
      show ((({j} : Finset (Fin k)) : Set (Fin k))).OrdConnected
      rw [Finset.coe_singleton]
      exact Set.ordConnected_singleton
    have hsum : (∑ x ∈ ({i} : Finset (Fin k)), a x) = ∑ x ∈ ({j} : Finset (Fin k)), a x := by
      rw [Finset.sum_singleton, Finset.sum_singleton]
      exact hij
    have hEq : ({i} : Finset (Fin k)) = ({j} : Finset (Fin k)) := hd hmi hmj hsum
    exact Finset.singleton_inj.mp hEq
  
  have hcard : ∀ (k : ℕ) (a : Fin k → ℕ), Function.Injective a →
      Set.range a ⊆ Set.Icc 1 n → k ≤ n := by
    intro k a hai ha
    have hsub : (Finset.univ.image a) ⊆ Finset.Icc 1 n := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      have hmem : a i ∈ Set.Icc 1 n := ha (Set.mem_range_self i)
      rw [Set.mem_Icc] at hmem
      exact Finset.mem_Icc.mpr hmem
    have hc := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injective _ hai, Finset.card_fin, Nat.card_Icc,
      Nat.add_sub_cancel] at hc
  have hbound : ∀ (k : ℕ) (a : Fin k → ℕ), Set.range a ⊆ Set.Icc 1 n →
      HasDistinctSums a → k ≤ n := fun k a ha hd => hcard k a (hinj k a hd) ha
  set S : Set ℕ := {k : ℕ | ∃ a : Fin k → ℕ, (Set.range a ⊆ Set.Icc 1 n) ∧ HasDistinctSums a}
    with hSdef
  have hgS : g n = sSup S := rfl
  
  have hne : S.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨fun i => i.elim0, ?_, ?_⟩
    · rintro x ⟨i, rfl⟩
      exact i.elim0
    · intro J₁ _ J₂ _ _
      rw [Finset.eq_empty_of_isEmpty J₁, Finset.eq_empty_of_isEmpty J₂]
  
  have hbdd : BddAbove S := by
    refine ⟨n, ?_⟩
    intro k hk
    obtain ⟨a, ha, hd⟩ := hk
    exact hbound k a ha hd
  
  have hmem : sSup S ∈ S := Nat.sSup_mem hne hbdd
  rw [hgS]
  obtain ⟨a, ha, hd⟩ := hmem
  refine ⟨hbound _ a ha hd, ?_, ⟨a, ha, hd⟩⟩
  intro k b hb hdb
  exact le_csSup hbdd ⟨b, hb, hdb⟩

theorem erdos357_distinctSums_card_bound (n k r : ℕ) (hr : 1 ≤ r) (a : Fin k → ℕ)
    (ha : Set.range a ⊆ Set.Icc 1 n) (hd : HasDistinctSums a) :
    (3 * r + 1) * k ≤ 2 * (r + 1) * n + 4 * r ^ 2 :=
by
  classical
  
  
  
  have gaussZ : ∀ m : ℕ, 2 * (∑ t ∈ Finset.range m, (t : ℤ)) = (m : ℤ) ^ 2 - (m : ℤ) := by
    intro m
    induction m with
    | zero => simp
    | succ p ih =>
        rw [Finset.sum_range_succ]
        push_cast
        push_cast at ih
        linarith
  
  
  
  have gaussN : ∀ R : ℕ, 2 * (∑ u ∈ Finset.Icc 1 R, u) = R * (R + 1) := by
    intro R
    induction R with
    | zero => simp
    | succ p ih =>
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ p + 1)]
        calc 2 * ((∑ u ∈ Finset.Icc 1 p, u) + (p + 1))
            = 2 * (∑ u ∈ Finset.Icc 1 p, u) + 2 * (p + 1) := by ring
          _ = p * (p + 1) + 2 * (p + 1) := by rw [ih]
          _ = (p + 1) * (p + 1 + 1) := by ring
  
  
  
  have triN : ∀ D : Finset ℕ, (∀ d ∈ D, 1 ≤ d) → D.card * (D.card + 1) ≤ 2 * ∑ d ∈ D, d := by
    intro D h1
    have hinj : Set.InjOn (fun d : ℕ => (d : ℤ)) ↑D := by
      intro x _ y _ h
      have h' : (x : ℤ) = (y : ℤ) := h
      exact_mod_cast h'
    have hcard : (D.image (fun d : ℕ => (d : ℤ))).card = D.card :=
      Finset.card_image_of_injOn hinj
    have hsum : ∑ e ∈ D.image (fun d : ℕ => (d : ℤ)), e = ((∑ d ∈ D, d : ℕ) : ℤ) := by
      rw [Finset.sum_image hinj]
      push_cast
      ring
    have hge : ∀ x ∈ D.image (fun d : ℕ => (d : ℤ)), (1 : ℤ) ≤ x := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨d, hd', rfl⟩ := hx
      exact_mod_cast h1 d hd'
    have key := Finset.sum_range_le_sum hge
    rw [hcard, hsum] at key
    have hexp : 2 * (∑ t ∈ Finset.range D.card, ((1 : ℤ) + (t : ℤ)))
        = (D.card : ℤ) * ((D.card : ℤ) + 1) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      have hg := gaussZ D.card
      ring_nf
      ring_nf at hg
      linarith
    have final : (D.card : ℤ) * ((D.card : ℤ) + 1) ≤ 2 * ((∑ d ∈ D, d : ℕ) : ℤ) := by
      rw [← hexp]
      linarith
    exact_mod_cast final
  
  
  
  have shortLB : ∀ (c : ℕ → ℕ) (K R : ℕ), (∀ m, m < K → 1 ≤ c m) →
      (∀ i₁ j₁ i₂ j₂ : ℕ, i₁ < j₁ → j₁ ≤ K → i₂ < j₂ → j₂ ≤ K →
        (∑ m ∈ Finset.Ico i₁ j₁, c m) = (∑ m ∈ Finset.Ico i₂ j₂, c m) → i₁ = i₂ ∧ j₁ = j₂) →
      (∑ u ∈ Finset.Icc 1 R, (K + 1 - u)) * ((∑ u ∈ Finset.Icc 1 R, (K + 1 - u)) + 1)
        ≤ 2 * (∑ u ∈ Finset.Icc 1 R, ∑ i ∈ Finset.range (K + 1 - u),
                 ∑ m ∈ Finset.Ico i (i + u), c m) := by
    intro c K R hc hcinj
    have hQcard : ((Finset.Icc 1 R).sigma (fun u => Finset.range (K + 1 - u))).card
        = ∑ u ∈ Finset.Icc 1 R, (K + 1 - u) := by
      rw [Finset.card_sigma]
      exact Finset.sum_congr rfl (fun u _ => Finset.card_range _)
    have hQsum : ∑ q ∈ (Finset.Icc 1 R).sigma (fun u => Finset.range (K + 1 - u)),
        (∑ m ∈ Finset.Ico q.2 (q.2 + q.1), c m)
        = ∑ u ∈ Finset.Icc 1 R, ∑ i ∈ Finset.range (K + 1 - u),
            ∑ m ∈ Finset.Ico i (i + u), c m := by
      rw [Finset.sum_sigma]
    have hmem : ∀ q ∈ (Finset.Icc 1 R).sigma (fun u => Finset.range (K + 1 - u)),
        1 ≤ q.1 ∧ q.1 ≤ R ∧ q.2 + q.1 ≤ K := by
      intro q hq
      rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_range] at hq
      obtain ⟨⟨hx, hy⟩, hz⟩ := hq
      exact ⟨hx, hy, by omega⟩
    have hFpos : ∀ q ∈ (Finset.Icc 1 R).sigma (fun u => Finset.range (K + 1 - u)),
        1 ≤ (∑ m ∈ Finset.Ico q.2 (q.2 + q.1), c m) := by
      intro q hq
      obtain ⟨h1, h2, h3⟩ := hmem q hq
      have hq2 : q.2 ∈ Finset.Ico q.2 (q.2 + q.1) := by
        simp only [Finset.mem_Ico]
        omega
      have hle : c q.2 ≤ ∑ m ∈ Finset.Ico q.2 (q.2 + q.1), c m :=
        Finset.single_le_sum (f := c) (fun i _ => Nat.zero_le _) hq2
      have hb2 : 1 ≤ c q.2 := hc q.2 (by omega)
      omega
    have hFinj : Set.InjOn (fun q : (_ : ℕ) × ℕ => ∑ m ∈ Finset.Ico q.2 (q.2 + q.1), c m)
        ↑((Finset.Icc 1 R).sigma (fun u => Finset.range (K + 1 - u))) := by
      rintro ⟨u, i⟩ hq ⟨u', i'⟩ hq' h
      obtain ⟨ha1, ha2, ha3⟩ := hmem ⟨u, i⟩ (Finset.mem_coe.1 hq)
      obtain ⟨hb1, hb2, hb3⟩ := hmem ⟨u', i'⟩ (Finset.mem_coe.1 hq')
      simp only at h ha1 ha2 ha3 hb1 hb2 hb3
      obtain ⟨hA, hB⟩ :=
        hcinj i (i + u) i' (i' + u') (by omega) (by omega) (by omega) (by omega) h
      have hu : u = u' := by omega
      subst hu
      subst hA
      rfl
    have hDcard : (((Finset.Icc 1 R).sigma (fun u => Finset.range (K + 1 - u))).image
        (fun q : (_ : ℕ) × ℕ => ∑ m ∈ Finset.Ico q.2 (q.2 + q.1), c m)).card
        = ((Finset.Icc 1 R).sigma (fun u => Finset.range (K + 1 - u))).card :=
      Finset.card_image_of_injOn hFinj
    have hDsum : ∑ d ∈ (((Finset.Icc 1 R).sigma (fun u => Finset.range (K + 1 - u))).image
        (fun q : (_ : ℕ) × ℕ => ∑ m ∈ Finset.Ico q.2 (q.2 + q.1), c m)), d
        = ∑ q ∈ (Finset.Icc 1 R).sigma (fun u => Finset.range (K + 1 - u)),
            (∑ m ∈ Finset.Ico q.2 (q.2 + q.1), c m) :=
      Finset.sum_image hFinj
    have hD1 : ∀ d ∈ (((Finset.Icc 1 R).sigma (fun u => Finset.range (K + 1 - u))).image
        (fun q : (_ : ℕ) × ℕ => ∑ m ∈ Finset.Ico q.2 (q.2 + q.1), c m)), 1 ≤ d := by
      intro d hd'
      rw [Finset.mem_image] at hd'
      obtain ⟨q, hq, rfl⟩ := hd'
      exact hFpos q hq
    have hres := triN _ hD1
    rw [hDcard, hDsum, hQcard, hQsum] at hres
    exact hres
  
  
  
  have windowUB : ∀ (c : ℕ → ℕ) (K R : ℕ),
      2 * (∑ u ∈ Finset.Icc 1 R, ∑ i ∈ Finset.range (K + 1 - u),
             ∑ m ∈ Finset.Ico i (i + u), c m)
        ≤ R * (R + 1) * (∑ m ∈ Finset.range K, c m) := by
    intro c K R
    have hA : ∀ u : ℕ, (∑ i ∈ Finset.range (K + 1 - u), ∑ m ∈ Finset.Ico i (i + u), c m)
        ≤ u * (∑ m ∈ Finset.range K, c m) := by
      intro u
      have hrw : ∀ i : ℕ, (∑ m ∈ Finset.Ico i (i + u), c m) = ∑ d ∈ Finset.range u, c (i + d) := by
        intro i
        rw [Finset.sum_Ico_eq_sum_range]
        simp
      calc (∑ i ∈ Finset.range (K + 1 - u), ∑ m ∈ Finset.Ico i (i + u), c m)
          = ∑ i ∈ Finset.range (K + 1 - u), ∑ d ∈ Finset.range u, c (i + d) :=
            Finset.sum_congr rfl (fun i _ => hrw i)
        _ = ∑ d ∈ Finset.range u, ∑ i ∈ Finset.range (K + 1 - u), c (i + d) := Finset.sum_comm
        _ ≤ ∑ _d ∈ Finset.range u, (∑ m ∈ Finset.range K, c m) := by
            refine Finset.sum_le_sum ?_
            intro d hd'
            have hdu : d < u := Finset.mem_range.1 hd'
            have hinj : Set.InjOn (fun i => i + d) ↑(Finset.range (K + 1 - u)) := by
              intro x _ y _ h
              simpa using h
            have himg : (Finset.range (K + 1 - u)).image (fun i => i + d) ⊆ Finset.range K := by
              intro m hm
              simp only [Finset.mem_image, Finset.mem_range] at hm ⊢
              obtain ⟨i, hi, rfl⟩ := hm
              omega
            calc (∑ i ∈ Finset.range (K + 1 - u), c (i + d))
                = ∑ m ∈ (Finset.range (K + 1 - u)).image (fun i => i + d), c m :=
                  (Finset.sum_image hinj).symm
              _ ≤ ∑ m ∈ Finset.range K, c m := Finset.sum_le_sum_of_subset himg
        _ = u * (∑ m ∈ Finset.range K, c m) := by
            rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have hstep : (∑ u ∈ Finset.Icc 1 R, ∑ i ∈ Finset.range (K + 1 - u),
        ∑ m ∈ Finset.Ico i (i + u), c m)
        ≤ (∑ u ∈ Finset.Icc 1 R, u) * (∑ m ∈ Finset.range K, c m) := by
      calc (∑ u ∈ Finset.Icc 1 R, ∑ i ∈ Finset.range (K + 1 - u),
              ∑ m ∈ Finset.Ico i (i + u), c m)
          ≤ ∑ u ∈ Finset.Icc 1 R, u * (∑ m ∈ Finset.range K, c m) :=
            Finset.sum_le_sum (fun u _ => hA u)
        _ = (∑ u ∈ Finset.Icc 1 R, u) * (∑ m ∈ Finset.range K, c m) := by
            rw [Finset.sum_mul]
    calc 2 * (∑ u ∈ Finset.Icc 1 R, ∑ i ∈ Finset.range (K + 1 - u),
              ∑ m ∈ Finset.Ico i (i + u), c m)
        ≤ 2 * ((∑ u ∈ Finset.Icc 1 R, u) * (∑ m ∈ Finset.range K, c m)) :=
          Nat.mul_le_mul_left 2 hstep
      _ = (2 * (∑ u ∈ Finset.Icc 1 R, u)) * (∑ m ∈ Finset.range K, c m) := by ring
      _ = R * (R + 1) * (∑ m ∈ Finset.range K, c m) := by rw [gaussN R]
  
  
  
  have distSumUB : ∀ (N K : ℕ) (fa : Fin K → ℕ), Function.Injective fa → (∀ i, fa i ≤ N) →
      2 * (∑ i, fa i) + K * K ≤ K * (2 * N + 1) := by
    intro N K fa hfainj hle
    have hinj' : Set.InjOn (fun i : Fin K => (fa i : ℤ)) ↑(Finset.univ : Finset (Fin K)) := by
      intro x _ y _ h
      have h' : (fa x : ℤ) = (fa y : ℤ) := h
      exact hfainj (by exact_mod_cast h')
    have hcard : ((Finset.univ : Finset (Fin K)).image (fun i : Fin K => (fa i : ℤ))).card = K := by
      rw [Finset.card_image_of_injOn hinj', Finset.card_univ, Fintype.card_fin]
    have hsum : ∑ e ∈ (Finset.univ : Finset (Fin K)).image (fun i : Fin K => (fa i : ℤ)), e
        = ((∑ i, fa i : ℕ) : ℤ) := by
      rw [Finset.sum_image hinj']
      push_cast
      ring
    have hbd : ∀ x ∈ (Finset.univ : Finset (Fin K)).image (fun i : Fin K => (fa i : ℤ)),
        x ≤ (N : ℤ) := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, _, rfl⟩ := hx
      exact_mod_cast hle i
    have key := Finset.sum_le_sum_range hbd
    rw [hcard, hsum] at key
    have hexp : ∑ t ∈ Finset.range K, ((N : ℤ) - (t : ℤ))
        = (K : ℤ) * (N : ℤ) - (∑ t ∈ Finset.range K, (t : ℤ)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hg := gaussZ K
    have final : 2 * ((∑ i, fa i : ℕ) : ℤ) + (K : ℤ) * (K : ℤ) ≤ (K : ℤ) * (2 * (N : ℤ) + 1) := by
      rw [hexp] at key
      linarith
    exact_mod_cast final
  
  
  
  have pairCount : ∀ K R : ℕ, R ≤ K →
      2 * (∑ u ∈ Finset.Icc 1 R, (K + 1 - u)) + R * (R + 1) = 2 * R * (K + 1) := by
    intro K R hRK
    have h1 : ∑ u ∈ Finset.Icc 1 R, ((K + 1 - u) + u) = R * (K + 1) := by
      have h2 : ∑ u ∈ Finset.Icc 1 R, ((K + 1 - u) + u) = ∑ _u ∈ Finset.Icc 1 R, (K + 1) := by
        refine Finset.sum_congr rfl (fun u hu => ?_)
        rw [Finset.mem_Icc] at hu
        omega
      rw [h2, Finset.sum_const, Nat.card_Icc, smul_eq_mul]
      simp
    rw [Finset.sum_add_distrib] at h1
    have hg := gaussN R
    linarith
  
  
  
  have countArith : ∀ N K R M S T : ℕ, 1 ≤ R → R ≤ K →
      2 * M + R * (R + 1) = 2 * R * (K + 1) →
      M * (M + 1) ≤ 2 * T →
      2 * T ≤ R * (R + 1) * S →
      2 * S + K * K ≤ K * (2 * N + 1) →
      (3 * R + 1) * K ≤ 2 * (R + 1) * N + 4 * R ^ 2 := by
    intro N K R M S T hR hRK hM hMT hTS hS
    have hR1 : (1 : ℤ) ≤ (R : ℤ) := by exact_mod_cast hR
    have hKR : (R : ℤ) ≤ (K : ℤ) := by exact_mod_cast hRK
    have hK1 : (1 : ℤ) ≤ (K : ℤ) := le_trans hR1 hKR
    have hMnn : (0 : ℤ) ≤ (M : ℤ) := Int.natCast_nonneg M
    have hSnn : (0 : ℤ) ≤ (S : ℤ) := Int.natCast_nonneg S
    have hNnn : (0 : ℤ) ≤ (N : ℤ) := Int.natCast_nonneg N
    have hMZ : 2 * (M : ℤ) + (R : ℤ) * ((R : ℤ) + 1) = 2 * (R : ℤ) * ((K : ℤ) + 1) := by
      exact_mod_cast hM
    have hMTZ : (M : ℤ) * ((M : ℤ) + 1) ≤ 2 * (T : ℤ) := by exact_mod_cast hMT
    have hTSZ : 2 * (T : ℤ) ≤ (R : ℤ) * ((R : ℤ) + 1) * (S : ℤ) := by exact_mod_cast hTS
    have hSZ : 2 * (S : ℤ) + (K : ℤ) * (K : ℤ) ≤ (K : ℤ) * (2 * (N : ℤ) + 1) := by
      exact_mod_cast hS
    set Rz : ℤ := (R : ℤ)
    set Kz : ℤ := (K : ℤ)
    set Nz : ℤ := (N : ℤ)
    set Mz : ℤ := (M : ℤ)
    set Sz : ℤ := (S : ℤ)
    set Tz : ℤ := (T : ℤ)
    have h2M : 2 * Mz = Rz * (2 * Kz + 1 - Rz) := by linarith [hMZ]
    have h4M2 : 4 * (Mz * Mz) = Rz * Rz * ((2 * Kz + 1 - Rz) * (2 * Kz + 1 - Rz)) := by
      linear_combination (2 * Mz + Rz * (2 * Kz + 1 - Rz)) * h2M
    have hM2T : Mz * Mz ≤ 2 * Tz := by nlinarith [hMTZ, hMnn]
    have hRnn : (0 : ℤ) ≤ 2 * Rz * (Rz + 1) := by nlinarith
    have hchain : 4 * (Mz * Mz) ≤ 2 * Rz * (Rz + 1) * (Kz * (2 * Nz + 1) - Kz * Kz) := by
      have step1 : 4 * (Mz * Mz) ≤ 2 * Rz * (Rz + 1) * (2 * Sz) := by nlinarith [hM2T, hTSZ]
      have step2 : 2 * Rz * (Rz + 1) * (2 * Sz)
          ≤ 2 * Rz * (Rz + 1) * (Kz * (2 * Nz + 1) - Kz * Kz) := by
        have hh : 2 * Sz ≤ Kz * (2 * Nz + 1) - Kz * Kz := by linarith
        exact mul_le_mul_of_nonneg_left hh hRnn
      linarith
    have hRpos : (0 : ℤ) < Rz := by linarith
    have hcancelR : Rz * ((2 * Kz + 1 - Rz) * (2 * Kz + 1 - Rz))
        ≤ Rz * (2 * (Rz + 1) * (Kz * (2 * Nz + 1) - Kz * Kz)) := by nlinarith [hchain, h4M2]
    have hstep6 : (2 * Kz + 1 - Rz) * (2 * Kz + 1 - Rz)
        ≤ 2 * (Rz + 1) * (Kz * (2 * Nz + 1) - Kz * Kz) :=
      le_of_mul_le_mul_left hcancelR hRpos
    have hsq : 4 * Kz * (Kz - Rz + 1) ≤ (2 * Kz + 1 - Rz) * (2 * Kz + 1 - Rz) := by
      nlinarith [sq_nonneg (Rz - 1)]
    have hstep7 : 4 * Kz * (Kz - Rz + 1) ≤ 2 * (Rz + 1) * (Kz * (2 * Nz + 1) - Kz * Kz) := by
      linarith
    have hKpos : (0 : ℤ) < 2 * Kz := by linarith
    have hcancelK : (2 * Kz) * (2 * Rz * (Kz - Rz + 1))
        ≤ (2 * Kz) * ((Rz + 1) * (2 * Nz + 1 - Kz)) := by nlinarith [hstep7]
    have hstep8 : 2 * Rz * (Kz - Rz + 1) ≤ (Rz + 1) * (2 * Nz + 1 - Kz) :=
      le_of_mul_le_mul_left hcancelK hKpos
    have hfin : (3 * Rz + 1) * Kz ≤ 2 * (Rz + 1) * Nz + 4 * Rz ^ 2 := by
      nlinarith [hstep8, hR1, sq_nonneg (Rz - 1)]
    have hfin' : (3 * (R : ℤ) + 1) * (K : ℤ)
        ≤ 2 * ((R : ℤ) + 1) * (N : ℤ) + 4 * (R : ℤ) ^ 2 := hfin
    exact_mod_cast hfin'
  
  
  
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0; simp
  by_cases hrk : r ≤ k
  · 
    have ha1 : ∀ i : Fin k, 1 ≤ a i := by
      intro i
      have hmem := ha ⟨i, rfl⟩
      rw [Set.mem_Icc] at hmem
      exact hmem.1
    have han : ∀ i : Fin k, a i ≤ n := by
      intro i
      have hmem := ha ⟨i, rfl⟩
      rw [Set.mem_Icc] at hmem
      exact hmem.2
    set b : ℕ → ℕ := fun m => if h : m < k then a ⟨m, h⟩ else 0 with hbdef
    have hb : ∀ i : Fin k, b (i : ℕ) = a i := by
      intro i
      simp only [hbdef, dif_pos i.isLt]
    have hbpos : ∀ m, m < k → 1 ≤ b m := by
      intro m hm
      have hbm : b m = a ⟨m, hm⟩ := by simp only [hbdef, dif_pos hm]
      rw [hbm]
      exact ha1 _
    
    have hinj : ∀ i₁ j₁ i₂ j₂ : ℕ, i₁ < j₁ → j₁ ≤ k → i₂ < j₂ → j₂ ≤ k →
        (∑ m ∈ Finset.Ico i₁ j₁, b m) = (∑ m ∈ Finset.Ico i₂ j₂, b m) → i₁ = i₂ ∧ j₁ = j₂ := by
      have key : ∀ i j : ℕ, i < j → j ≤ k →
          ∃ u v : Fin k, (u : ℕ) = i ∧ (v : ℕ) = j - 1 ∧ u ≤ v ∧
            (∑ x ∈ Finset.Icc u v, a x) = ∑ m ∈ Finset.Ico i j, b m := by
        intro i j hij hjk
        have hi : i < k := by omega
        have hj : j - 1 < k := by omega
        refine ⟨⟨i, hi⟩, ⟨j - 1, hj⟩, rfl, rfl, ?_, ?_⟩
        · simp only [Fin.le_def]
          omega
        · have h1 : ∑ x ∈ Finset.Icc (⟨i, hi⟩ : Fin k) ⟨j - 1, hj⟩, a x
              = ∑ x ∈ Finset.Icc (⟨i, hi⟩ : Fin k) ⟨j - 1, hj⟩, b (x : ℕ) :=
            Finset.sum_congr rfl (fun x _ => (hb x).symm)
          have h2 : ∑ x ∈ Finset.Icc (⟨i, hi⟩ : Fin k) ⟨j - 1, hj⟩, b (x : ℕ)
              = ∑ m ∈ Finset.map Fin.valEmbedding
                  (Finset.Icc (⟨i, hi⟩ : Fin k) ⟨j - 1, hj⟩), b m :=
            (Finset.sum_map (Finset.Icc (⟨i, hi⟩ : Fin k) ⟨j - 1, hj⟩) Fin.valEmbedding b).symm
          have h3 : Finset.map Fin.valEmbedding (Finset.Icc (⟨i, hi⟩ : Fin k) ⟨j - 1, hj⟩)
              = Finset.Icc i (j - 1) := Fin.map_valEmbedding_Icc _ _
          have hj1 : j - 1 + 1 = j := by omega
          rw [h1, h2, h3, ← Finset.Ico_add_one_right_eq_Icc, hj1]
      intro i₁ j₁ i₂ j₂ h₁ h₂ h₃ h₄ heq
      obtain ⟨u₁, v₁, hu₁, hv₁, huv₁, hs₁⟩ := key i₁ j₁ h₁ h₂
      obtain ⟨u₂, v₂, hu₂, hv₂, huv₂, hs₂⟩ := key i₂ j₂ h₃ h₄
      have hmem : ∀ u v : Fin k,
          (Finset.Icc u v) ∈ {J : Finset (Fin k) | (J : Set (Fin k)).OrdConnected} := by
        intro u v
        simp only [Set.mem_setOf_eq, Finset.coe_Icc]
        exact Set.ordConnected_Icc
      have hEq : Finset.Icc u₁ v₁ = Finset.Icc u₂ v₂ :=
        hd (hmem u₁ v₁) (hmem u₂ v₂) (hs₁.trans (heq.trans hs₂.symm))
      have hcoe : Set.Icc u₁ v₁ = Set.Icc u₂ v₂ := by
        rw [← Finset.coe_Icc, ← Finset.coe_Icc, hEq]
      obtain ⟨e1, e2⟩ := (Set.Icc_eq_Icc_iff huv₁).1 hcoe
      have ev : (v₁ : ℕ) = (v₂ : ℕ) := by rw [e2]
      have eu : (u₁ : ℕ) = (u₂ : ℕ) := by rw [e1]
      rw [hu₁, hu₂] at eu
      rw [hv₁, hv₂] at ev
      exact ⟨eu, by omega⟩
    have hone : ∀ i : ℕ, ∑ m ∈ Finset.Ico i (i + 1), b m = b i := by
      intro i
      rw [Finset.sum_Ico_eq_sum_range]
      simp
    have hainj : Function.Injective a := by
      intro i₁ i₂ hii
      have hsum : ∑ m ∈ Finset.Ico (i₁ : ℕ) ((i₁ : ℕ) + 1), b m
          = ∑ m ∈ Finset.Ico (i₂ : ℕ) ((i₂ : ℕ) + 1), b m := by
        rw [hone, hone, hb, hb, hii]
      have hres := hinj (i₁ : ℕ) ((i₁ : ℕ) + 1) (i₂ : ℕ) ((i₂ : ℕ) + 1)
        (by omega) (by omega : (i₁ : ℕ) + 1 ≤ k) (by omega) (by omega : (i₂ : ℕ) + 1 ≤ k) hsum
      exact Fin.ext hres.1
    have hSa : ∑ m ∈ Finset.range k, b m = ∑ i, a i := by
      rw [← Fin.sum_univ_eq_sum_range b k]
      exact Finset.sum_congr rfl (fun i _ => hb i)
    have h5 := distSumUB n k a hainj han
    rw [← hSa] at h5
    have h6 := pairCount k r hrk
    have h3 := shortLB b k r hbpos hinj
    have h4 := windowUB b k r
    exact countArith n k r (∑ u ∈ Finset.Icc 1 r, (k + 1 - u))
      (∑ m ∈ Finset.range k, b m)
      (∑ u ∈ Finset.Icc 1 r, ∑ i ∈ Finset.range (k + 1 - u), ∑ m ∈ Finset.Ico i (i + u), b m)
      hr hrk h6 h3 h4 h5
  · 
    have hk1 : k + 1 ≤ r := by omega
    have hsmall : (3 * r + 1) * k ≤ 4 * r ^ 2 := by nlinarith [hk1]
    exact le_trans hsmall (Nat.le_add_left _ _)

theorem erdos357_erdosTuran_witness (p : ℕ) (hp : Nat.Prime p) (hp3 : 3 ≤ p) :
    ∃ a : Fin (p - 1) → ℕ, Set.range a ⊆ Set.Icc 1 (3 * p - 2) ∧ HasDistinctSums a :=
by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hp0 : 0 < p := by omega
  
  obtain ⟨r, hrdef⟩ : ∃ r : ℕ → ℕ, ∀ i, r i = i ^ 2 % p := ⟨fun i => i ^ 2 % p, fun _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℕ → ℕ, ∀ i, B i = 2 * p * i + r i := ⟨fun i => 2 * p * i + r i, fun _ => rfl⟩
  have hrlt : ∀ i : ℕ, r i < p := by
    intro i; rw [hrdef]; exact Nat.mod_lt _ hp0
  
  have key : ∀ m : ℕ, B m + (2 * p + r (m + 1)) = B (m + 1) + r m := by
    intro m
    rw [hB m, hB (m + 1)]
    ring
  have hBmono : Monotone B := by
    apply monotone_nat_of_le_succ
    intro m
    have h1 := key m
    have h2 := hrlt m
    omega
  
  have hrne : ∀ j : ℕ, 0 < j → j < p → r j ≠ 0 := by
    intro j hj0 hjp h0
    rw [hrdef] at h0
    have hdvd : p ∣ j ^ 2 := Nat.dvd_of_mod_eq_zero h0
    have hdj : p ∣ j := hp.dvd_of_dvd_pow hdvd
    have := Nat.le_of_dvd hj0 hdj
    omega
  
  have hlower : ∀ j : ℕ, j < p - 1 → 1 ≤ B (j + 1) - B j := by
    intro j _
    have h1 := key j
    have h2 := hrlt j
    omega
  have hupper : ∀ j : ℕ, j < p - 1 → B (j + 1) - B j ≤ 3 * p - 2 := by
    intro j hj
    have h1 := key j
    have h2 := hrlt j
    have h3 := hrlt (j + 1)
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have e0 : r 0 = 0 := by rw [hrdef]; norm_num
      have e1 : r (0 + 1) = 1 := by
        rw [hrdef]
        norm_num
        exact Nat.mod_eq_of_lt (by omega)
      omega
    · have h4 : r j ≠ 0 := hrne j hj0 (by omega)
      omega
  
  have htel : ∀ u v : ℕ, u ≤ v →
      ∑ m ∈ Finset.Icc u v, (B (m + 1) - B m) = B (v + 1) - B u := by
    intro u v huv
    induction v, huv using Nat.le_induction with
    | base => simp
    | succ w hw ih =>
      have hsplit : ∑ m ∈ Finset.Icc u (w + 1), (B (m + 1) - B m)
          = (∑ m ∈ Finset.Icc u w, (B (m + 1) - B m)) + (B (w + 1 + 1) - B (w + 1)) :=
        Finset.sum_Icc_succ_top (by omega) (fun m => B (m + 1) - B m)
      rw [hsplit, ih]
      have h1 : B u ≤ B (w + 1) := hBmono (by omega)
      have h2 : B (w + 1) ≤ B (w + 1 + 1) := hBmono (by omega)
      omega
  
  have hsumFin : ∀ u v : Fin (p - 1), u ≤ v →
      ∑ x ∈ Finset.Icc u v, (B ((x : ℕ) + 1) - B (x : ℕ)) = B ((v : ℕ) + 1) - B (u : ℕ) := by
    intro u v huv
    have h1 : ∑ m ∈ Finset.Icc ((u : ℕ)) ((v : ℕ)), (B (m + 1) - B m)
        = ∑ x ∈ Finset.Icc u v, (B ((x : ℕ) + 1) - B (x : ℕ)) := by
      rw [← Fin.map_valEmbedding_Icc u v, Finset.sum_map]
      rfl
    rw [← h1]
    exact htel _ _ (Fin.le_def.mp huv)
  
  have hoc : ∀ (J : Finset (Fin (p - 1))), ((J : Set (Fin (p - 1))).OrdConnected) →
      ∀ (hne : J.Nonempty), J = Finset.Icc (J.min' hne) (J.max' hne) := by
    intro J hJ hne
    apply Finset.Subset.antisymm
    · intro x hx
      exact Finset.mem_Icc.mpr ⟨J.min'_le x hx, J.le_max' x hx⟩
    · intro x hx
      rw [Finset.mem_Icc] at hx
      have hsub := hJ.out (Finset.mem_coe.mpr (J.min'_mem hne))
        (Finset.mem_coe.mpr (J.max'_mem hne))
      exact Finset.mem_coe.mp (hsub (Set.mem_Icc.mpr hx))
  
  have hsidon : ∀ i j k l : ℕ, i < p → j < p → k < p → l < p →
      B i + B j = B k + B l → (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
    intro i j k l hi hj hk hl h
    have h2p : 0 < 2 * p := by omega
    have hsij : r i + r j < 2 * p := by have := hrlt i; have := hrlt j; omega
    have hskl : r k + r l < 2 * p := by have := hrlt k; have := hrlt l; omega
    have heq : (r i + r j) + 2 * p * (i + j) = (r k + r l) + 2 * p * (k + l) := by
      have e1 : 2 * p * (i + j) = 2 * p * i + 2 * p * j := by ring
      have e2 : 2 * p * (k + l) = 2 * p * k + 2 * p * l := by ring
      rw [hB i, hB j, hB k, hB l] at h
      omega
    have hA1 : i + j = k + l := by
      have d1 : ((r i + r j) + 2 * p * (i + j)) / (2 * p) = 0 + (i + j) := by
        rw [Nat.add_mul_div_left _ _ h2p, Nat.div_eq_of_lt hsij]
      have d2 : ((r k + r l) + 2 * p * (k + l)) / (2 * p) = 0 + (k + l) := by
        rw [Nat.add_mul_div_left _ _ h2p, Nat.div_eq_of_lt hskl]
      rw [heq] at d1
      omega
    have hA2 : r i + r j = r k + r l := by
      rw [hA1] at heq
      omega
    
    have hcast1 : ((i : ZMod p)) + ((j : ZMod p)) = ((k : ZMod p)) + ((l : ZMod p)) := by
      have hh := congrArg (fun n : ℕ => (n : ZMod p)) hA1
      push_cast at hh
      exact hh
    have hcast2 : ((i : ZMod p)) ^ 2 + ((j : ZMod p)) ^ 2
        = ((k : ZMod p)) ^ 2 + ((l : ZMod p)) ^ 2 := by
      have hh := congrArg (fun n : ℕ => (n : ZMod p)) hA2
      simp only [hrdef, Nat.cast_add, ZMod.natCast_mod, Nat.cast_pow] at hh
      exact hh
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro hcon
      have h20 : ((2 : ℕ) : ZMod p) = 0 := by push_cast; exact hcon
      have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h20
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    have hfac : (2 : ZMod p) * (((i : ZMod p) - (k : ZMod p)) * ((j : ZMod p) - (k : ZMod p)))
        = 0 := by
      linear_combination ((i : ZMod p) + (j : ZMod p) + (l : ZMod p) - (k : ZMod p)) * hcast1
        - hcast2
    have hprod : ((i : ZMod p) - (k : ZMod p)) * ((j : ZMod p) - (k : ZMod p)) = 0 := by
      rcases mul_eq_zero.mp hfac with hh | hh
      · exact absurd hh h2ne
      · exact hh
    rcases mul_eq_zero.mp hprod with hh | hh
    · have hik : (i : ZMod p) = (k : ZMod p) := eq_of_sub_eq_zero hh
      have hik' : i = k := by
        have h1 := congrArg ZMod.val hik
        rwa [ZMod.val_cast_of_lt hi, ZMod.val_cast_of_lt hk] at h1
      exact Or.inl ⟨hik', by omega⟩
    · have hjk : (j : ZMod p) = (k : ZMod p) := eq_of_sub_eq_zero hh
      have hjk' : j = k := by
        have h1 := congrArg ZMod.val hjk
        rwa [ZMod.val_cast_of_lt hj, ZMod.val_cast_of_lt hk] at h1
      exact Or.inr ⟨by omega, hjk'⟩
  
  refine ⟨fun x => B ((x : ℕ) + 1) - B (x : ℕ), ?_, ?_⟩
  · rw [Set.range_subset_iff]
    intro x
    exact Set.mem_Icc.mpr ⟨hlower _ x.isLt, hupper _ x.isLt⟩
  · intro J hJ K hK hsum
    simp only [Set.mem_setOf_eq] at hJ hK
    dsimp only at hsum
    have hapos : ∀ x : Fin (p - 1), 0 < B ((x : ℕ) + 1) - B (x : ℕ) := by
      intro x
      have := hlower _ x.isLt
      omega
    rcases Finset.eq_empty_or_nonempty J with rfl | hJne
    · rcases Finset.eq_empty_or_nonempty K with rfl | hKne
      · rfl
      · exfalso
        have hpos : 0 < ∑ x ∈ K, (B ((x : ℕ) + 1) - B (x : ℕ)) :=
          Finset.sum_pos (fun x _ => hapos x) hKne
        rw [Finset.sum_empty] at hsum
        omega
    · rcases Finset.eq_empty_or_nonempty K with rfl | hKne
      · exfalso
        have hpos : 0 < ∑ x ∈ J, (B ((x : ℕ) + 1) - B (x : ℕ)) :=
          Finset.sum_pos (fun x _ => hapos x) hJne
        rw [Finset.sum_empty] at hsum
        omega
      · obtain ⟨u, v, hJI, huv⟩ : ∃ u v : Fin (p - 1), J = Finset.Icc u v ∧ u ≤ v :=
          ⟨J.min' hJne, J.max' hJne, hoc J hJ hJne, J.min'_le _ (J.max'_mem hJne)⟩
        obtain ⟨u', v', hKI, hu'v'⟩ : ∃ u v : Fin (p - 1), K = Finset.Icc u v ∧ u ≤ v :=
          ⟨K.min' hKne, K.max' hKne, hoc K hK hKne, K.min'_le _ (K.max'_mem hKne)⟩
        rw [hJI, hKI] at hsum ⊢
        rw [hsumFin u v huv, hsumFin u' v' hu'v'] at hsum
        have hmu : (u : ℕ) ≤ (v : ℕ) := Fin.le_def.mp huv
        have hmu' : (u' : ℕ) ≤ (v' : ℕ) := Fin.le_def.mp hu'v'
        have hb1 : B (u : ℕ) ≤ B ((v : ℕ) + 1) := hBmono (by omega)
        have hb2 : B (u' : ℕ) ≤ B ((v' : ℕ) + 1) := hBmono (by omega)
        have hadd : B ((v : ℕ) + 1) + B (u' : ℕ) = B ((v' : ℕ) + 1) + B (u : ℕ) := by omega
        have hvp : (v : ℕ) + 1 < p := by have := v.isLt; omega
        have hv'p : (v' : ℕ) + 1 < p := by have := v'.isLt; omega
        have hup : (u : ℕ) < p := by have := u.isLt; omega
        have hu'p : (u' : ℕ) < p := by have := u'.isLt; omega
        rcases hsidon _ _ _ _ hvp hu'p hv'p hup hadd with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · have hu : u = u' := Fin.val_injective (by omega)
          have hv : v = v' := Fin.val_injective (by omega)
          rw [hu, hv]
        · exfalso; omega

theorem erdos357_rect_residue_simple_pole (F : ℂ → ℂ) (V : Set ℂ) (a b c d : ℝ)
    (hV : IsOpen V) (hF : DifferentiableOn ℂ F V)
    (ha : a < 0) (hb : 0 < b) (hc : c < 0) (hd : 0 < d)
    (hsub : Set.uIcc a b ×ℂ Set.uIcc c d ⊆ V) :
    (((∫ x in a..b, F (↑x + ↑c * Complex.I) / (↑x + ↑c * Complex.I))
        - ∫ x in a..b, F (↑x + ↑d * Complex.I) / (↑x + ↑d * Complex.I))
      + Complex.I • ∫ y in c..d, F (↑b + ↑y * Complex.I) / (↑b + ↑y * Complex.I))
      - Complex.I • ∫ y in c..d, F (↑a + ↑y * Complex.I) / (↑a + ↑y * Complex.I)
    = 2 * (Real.pi : ℂ) * Complex.I * F 0 :=
by
  
  have hs1 : ∀ p q r : ℝ, r ≠ 0 →
      (∫ x in p..q, ((x : ℂ) + (r : ℂ) * Complex.I)⁻¹)
        = (((Real.log (q ^ 2 + r ^ 2) - Real.log (p ^ 2 + r ^ 2)) / 2 : ℝ) : ℂ)
          - Complex.I * (((Real.arctan (q / r) - Real.arctan (p / r)) : ℝ) : ℂ) := by
    intro p q r hr
    have hpos : ∀ x : ℝ, 0 < x ^ 2 + r ^ 2 := fun x => by positivity
    have hne : ∀ x : ℝ, (x : ℂ) + (r : ℂ) * Complex.I ≠ 0 := by
      intro x h
      have := congrArg Complex.im h
      simp at this
      exact hr this
    have hderiv : ∀ x : ℝ, HasDerivAt
        (fun x : ℝ => ((Real.log (x ^ 2 + r ^ 2) / 2 : ℝ) : ℂ)
          - Complex.I * ((Real.arctan (x / r) : ℝ) : ℂ))
        ((x : ℂ) + (r : ℂ) * Complex.I)⁻¹ x := by
      intro x
      have h1 : HasDerivAt (fun x : ℝ => Real.log (x ^ 2 + r ^ 2) / 2)
          (x / (x ^ 2 + r ^ 2)) x := by
        have := (((hasDerivAt_pow 2 x).add_const (r ^ 2)).log (hpos x).ne').div_const 2
        convert this using 1
        field_simp
        ring
      have h2 : HasDerivAt (fun x : ℝ => Real.arctan (x / r)) (r / (x ^ 2 + r ^ 2)) x := by
        have := (Real.hasDerivAt_arctan (x / r)).comp x ((hasDerivAt_id x).div_const r)
        convert this using 1
        field_simp
        ring
      have h3 := h1.ofReal_comp.sub (h2.ofReal_comp.const_mul Complex.I)
      convert h3 using 1
      have hc : ((x : ℂ)) ^ 2 + ((r : ℂ)) ^ 2 ≠ 0 := by exact_mod_cast (hpos x).ne'
      apply inv_eq_of_mul_eq_one_right
      push_cast
      field_simp
      linear_combination (-(r : ℂ) ^ 2) * Complex.I_sq
    have hint : IntervalIntegrable (fun x : ℝ => ((x : ℂ) + (r : ℂ) * Complex.I)⁻¹)
        MeasureTheory.volume p q :=
      ((Complex.continuous_ofReal.add continuous_const).inv₀ hne).intervalIntegrable p q
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) hint]
    push_cast
    ring
  
  have hs2 : (Real.arctan (b / c) - Real.arctan (a / c))
        - (Real.arctan (b / d) - Real.arctan (a / d))
        + (Real.arctan (d / (-b)) - Real.arctan (c / (-b)))
        - (Real.arctan (d / (-a)) - Real.arctan (c / (-a)))
      = -(2 * Real.pi) := by
    have key : ∀ u v : ℝ, 0 < u → 0 < v →
        Real.arctan (u / v) + Real.arctan (v / u) = Real.pi / 2 := by
      intro u v hu hv
      have h := Real.arctan_inv_of_pos (div_pos hu hv)
      rw [inv_div] at h
      linarith
    obtain ⟨A, rfl⟩ : ∃ A : ℝ, a = -A := ⟨-a, by ring⟩
    obtain ⟨C, rfl⟩ : ∃ C : ℝ, c = -C := ⟨-c, by ring⟩
    have hA : 0 < A := by linarith
    have hC : 0 < C := by linarith
    simp only [div_neg, neg_div, neg_neg, Real.arctan_neg]
    have k1 := key b C hb hC
    have k2 := key A C hA hC
    have k3 := key b d hb hd
    have k4 := key A d hA hd
    linarith
  
  have hrot : ∀ u : ℝ, u ≠ 0 →
      Complex.I * (∫ y in c..d, ((u : ℂ) + (y : ℂ) * Complex.I)⁻¹)
        = ∫ y in c..d, ((y : ℂ) + ((-u : ℝ) : ℂ) * Complex.I)⁻¹ := by
    intro u hu
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext y
    have hne1 : (u : ℂ) + (y : ℂ) * Complex.I ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      exact hu this
    have hmul : ((y : ℂ) + ((-u : ℝ) : ℂ) * Complex.I) * Complex.I
        = (u : ℂ) + (y : ℂ) * Complex.I := by
      push_cast
      linear_combination (-(u : ℂ)) * Complex.I_sq
    symm
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, hmul, mul_inv_cancel₀ hne1]
  
  have h0 : (0 : ℂ) ∈ V := by
    apply hsub
    rw [Complex.mem_reProdIm]
    exact ⟨by simpa using Set.mem_uIcc.mpr (Or.inl ⟨ha.le, hb.le⟩),
      by simpa using Set.mem_uIcc.mpr (Or.inl ⟨hc.le, hd.le⟩)⟩
  have hD : DifferentiableOn ℂ (dslope F 0) V :=
    (Complex.differentiableOn_dslope (hV.mem_nhds h0)).mpr hF
  have hpt : ∀ z : ℂ, z ≠ 0 → F z / z = dslope F 0 z + F 0 * z⁻¹ := by
    intro z hz
    rw [dslope_of_ne _ hz, slope_def_field, sub_zero]
    field_simp
    ring
  have hsplit : ∀ (γ : ℝ → ℂ) (p q : ℝ), Continuous γ → (∀ t, γ t ≠ 0) →
      (∀ t ∈ Set.uIcc p q, γ t ∈ V) →
      (∫ t in p..q, F (γ t) / γ t)
        = (∫ t in p..q, dslope F 0 (γ t)) + F 0 * ∫ t in p..q, (γ t)⁻¹ := by
    intro γ p q hγ hne hmem
    have hi1 : IntervalIntegrable (fun t => dslope F 0 (γ t)) MeasureTheory.volume p q :=
      (hD.continuousOn.comp hγ.continuousOn hmem).intervalIntegrable
    have hi2 : IntervalIntegrable (fun t => F 0 * (γ t)⁻¹) MeasureTheory.volume p q :=
      (continuous_const.mul (hγ.inv₀ hne)).intervalIntegrable p q
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hi1 hi2]
    exact intervalIntegral.integral_congr (fun t _ => hpt (γ t) (hne t))
  have hmemQ : ∀ x y : ℝ, x ∈ Set.uIcc a b → y ∈ Set.uIcc c d →
      ((x : ℂ) + (y : ℂ) * Complex.I) ∈ V := by
    intro x y hx hy
    apply hsub
    rw [Complex.mem_reProdIm]
    exact ⟨by simpa using hx, by simpa using hy⟩
  have hne_im : ∀ x y : ℝ, y ≠ 0 → (x : ℂ) + (y : ℂ) * Complex.I ≠ 0 := by
    intro x y hy h
    have := congrArg Complex.im h
    simp at this
    exact hy this
  have hne_re : ∀ x y : ℝ, x ≠ 0 → (x : ℂ) + (y : ℂ) * Complex.I ≠ 0 := by
    intro x y hx h
    have := congrArg Complex.re h
    simp at this
    exact hx this
  have e1 := hsplit (fun x : ℝ => (x : ℂ) + (c : ℂ) * Complex.I) a b (by fun_prop)
    (fun x => hne_im x c hc.ne) (fun x hx => hmemQ x c hx Set.left_mem_uIcc)
  have e2 := hsplit (fun x : ℝ => (x : ℂ) + (d : ℂ) * Complex.I) a b (by fun_prop)
    (fun x => hne_im x d hd.ne') (fun x hx => hmemQ x d hx Set.right_mem_uIcc)
  have e3 := hsplit (fun y : ℝ => (b : ℂ) + (y : ℂ) * Complex.I) c d (by fun_prop)
    (fun y => hne_re b y hb.ne') (fun y hy => hmemQ b y Set.right_mem_uIcc hy)
  have e4 := hsplit (fun y : ℝ => (a : ℂ) + (y : ℂ) * Complex.I) c d (by fun_prop)
    (fun y => hne_re a y ha.ne) (fun y hy => hmemQ a y Set.left_mem_uIcc hy)
  have hzre : ((a : ℂ) + (c : ℂ) * Complex.I).re = a := by simp
  have hzim : ((a : ℂ) + (c : ℂ) * Complex.I).im = c := by simp
  have hwre : ((b : ℂ) + (d : ℂ) * Complex.I).re = b := by simp
  have hwim : ((b : ℂ) + (d : ℂ) * Complex.I).im = d := by simp
  have hR := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (dslope F 0)
    ((a : ℂ) + (c : ℂ) * Complex.I) ((b : ℂ) + (d : ℂ) * Complex.I)
    (by rw [hzre, hzim, hwre, hwim]; exact hD.mono hsub)
  rw [hzre, hzim, hwre, hwim] at hR
  have hK : (∫ x in a..b, ((x : ℂ) + (c : ℂ) * Complex.I)⁻¹)
      - (∫ x in a..b, ((x : ℂ) + (d : ℂ) * Complex.I)⁻¹)
      + Complex.I * (∫ y in c..d, ((b : ℂ) + (y : ℂ) * Complex.I)⁻¹)
      - Complex.I * (∫ y in c..d, ((a : ℂ) + (y : ℂ) * Complex.I)⁻¹)
      = 2 * (Real.pi : ℂ) * Complex.I := by
    rw [hrot b hb.ne', hrot a ha.ne, hs1 a b c hc.ne, hs1 a b d hd.ne',
      hs1 c d (-b) (neg_ne_zero.mpr hb.ne'), hs1 c d (-a) (neg_ne_zero.mpr ha.ne)]
    have hX : (Real.log (b ^ 2 + c ^ 2) - Real.log (a ^ 2 + c ^ 2)) / 2
        - (Real.log (b ^ 2 + d ^ 2) - Real.log (a ^ 2 + d ^ 2)) / 2
        + (Real.log (d ^ 2 + (-b) ^ 2) - Real.log (c ^ 2 + (-b) ^ 2)) / 2
        - (Real.log (d ^ 2 + (-a) ^ 2) - Real.log (c ^ 2 + (-a) ^ 2)) / 2 = 0 := by
      rw [show d ^ 2 + (-b) ^ 2 = b ^ 2 + d ^ 2 by ring,
        show c ^ 2 + (-b) ^ 2 = b ^ 2 + c ^ 2 by ring,
        show d ^ 2 + (-a) ^ 2 = a ^ 2 + d ^ 2 by ring,
        show c ^ 2 + (-a) ^ 2 = a ^ 2 + c ^ 2 by ring]
      ring
    have hXc := congrArg (fun r : ℝ => (r : ℂ)) hX
    have hYc := congrArg (fun r : ℝ => (r : ℂ)) hs2
    simp only at hXc hYc
    push_cast at hXc hYc ⊢
    linear_combination hXc - Complex.I * hYc
  rw [e1, e2, e3, e4]
  simp only [smul_eq_mul] at hR ⊢
  linear_combination hR + F 0 * hK

theorem erdos357_truncated_laplace_differentiable (f : ℝ → ℂ) (B T : ℝ) (hT : 0 ≤ T)
    (hmeas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    (hbdd : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B) :
    Differentiable ℂ (fun z : ℂ => ∫ t in (0:ℝ)..T, f t * Complex.exp (-(z * (t : ℂ)))) :=
by
  
  have hB0 : 0 ≤ B := le_trans (norm_nonneg (f 0)) (hbdd 0 le_rfl)
  
  have hfII : IntervalIntegrable f MeasureTheory.volume 0 T := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hT]
    refine MeasureTheory.Measure.integrableOn_of_bounded (M := B) measure_Ioc_lt_top.ne hmeas ?_
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    exact MeasureTheory.ae_of_all _ (fun t ht => hbdd t ht.1.le)
  
  have hFII : ∀ w : ℂ, IntervalIntegrable
      (fun t : ℝ => f t * Complex.exp (-(w * (t : ℂ)))) MeasureTheory.volume 0 T := fun w =>
    hfII.mul_continuousOn (Continuous.continuousOn (by fun_prop))
  have hfmulII : IntervalIntegrable (fun t : ℝ => f t * (-(t : ℂ))) MeasureTheory.volume 0 T :=
    hfII.mul_continuousOn (Continuous.continuousOn (by fun_prop))
  have hF'II : ∀ w : ℂ, IntervalIntegrable
      (fun t : ℝ => f t * (-(t : ℂ)) * Complex.exp (-(w * (t : ℂ))))
      MeasureTheory.volume 0 T := fun w =>
    hfmulII.mul_continuousOn (Continuous.continuousOn (by fun_prop))
  intro z₀
  
  have hmeasF : ∀ᶠ (w : ℂ) in nhds z₀, MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => f t * Complex.exp (-(w * (t : ℂ))))
      (MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) T)) :=
    Filter.Eventually.of_forall fun w =>
      MeasureTheory.Integrable.aestronglyMeasurable (intervalIntegrable_iff.mp (hFII w))
  
  have hmeasF' : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => f t * (-(t : ℂ)) * Complex.exp (-(z₀ * (t : ℂ))))
      (MeasureTheory.volume.restrict (Set.uIoc (0:ℝ) T)) :=
    MeasureTheory.Integrable.aestronglyMeasurable (intervalIntegrable_iff.mp (hF'II z₀))
  
  have hbound : ∀ᵐ (t : ℝ) ∂MeasureTheory.volume, t ∈ Set.uIoc (0:ℝ) T →
      ∀ z ∈ Metric.ball z₀ 1,
        ‖f t * (-(t : ℂ)) * Complex.exp (-(z * (t : ℂ)))‖
          ≤ B * T * Real.exp ((‖z₀‖ + 1) * T) := by
    refine MeasureTheory.ae_of_all _ (fun t ht z hz => ?_)
    rw [Set.uIoc_of_le hT] at ht
    obtain ⟨ht0, htT⟩ := ht
    have ht0' : (0:ℝ) ≤ t := ht0.le
    have h1 : ‖(-(t : ℂ))‖ = t := by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0']
    have hre : (-(z * (t : ℂ))).re = -(z.re * t) := by
      simp [Complex.mul_re]
    have h2 : ‖Complex.exp (-(z * (t : ℂ)))‖ = Real.exp (-(z.re * t)) := by
      rw [Complex.norm_exp, hre]
    have hzd : ‖z - z₀‖ < 1 := by
      have hdd := Metric.mem_ball.mp hz
      rwa [Complex.dist_eq] at hdd
    have hznorm : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have hsn := norm_sub_norm_le z z₀
      linarith
    have hz0 : (0:ℝ) ≤ ‖z₀‖ := norm_nonneg _
    have hzre : -z.re ≤ ‖z₀‖ + 1 := by
      have hab := abs_le.mp (Complex.abs_re_le_norm z)
      linarith [hab.1]
    have hexp : Real.exp (-(z.re * t)) ≤ Real.exp ((‖z₀‖ + 1) * T) := by
      refine Real.exp_le_exp.mpr ?_
      have h3 : -(z.re * t) = (-z.re) * t := by ring
      rw [h3]
      calc (-z.re) * t ≤ (‖z₀‖ + 1) * t := by nlinarith
        _ ≤ (‖z₀‖ + 1) * T := by nlinarith
    have hft : ‖f t‖ ≤ B := hbdd t ht0'
    have hstep1 : ‖f t‖ * t ≤ B * T := mul_le_mul hft htT ht0' hB0
    have hE' : (0:ℝ) < Real.exp (-(z.re * t)) := Real.exp_pos _
    have hBT : (0:ℝ) ≤ B * T := mul_nonneg hB0 hT
    rw [norm_mul, norm_mul, h1, h2]
    calc ‖f t‖ * t * Real.exp (-(z.re * t))
        ≤ B * T * Real.exp (-(z.re * t)) := mul_le_mul_of_nonneg_right hstep1 hE'.le
      _ ≤ B * T * Real.exp ((‖z₀‖ + 1) * T) := mul_le_mul_of_nonneg_left hexp hBT
  
  have hderiv : ∀ᵐ (t : ℝ) ∂MeasureTheory.volume, t ∈ Set.uIoc (0:ℝ) T →
      ∀ z ∈ Metric.ball z₀ 1,
        HasDerivAt (fun w : ℂ => f t * Complex.exp (-(w * (t : ℂ))))
          (f t * (-(t : ℂ)) * Complex.exp (-(z * (t : ℂ)))) z := by
    refine MeasureTheory.ae_of_all _ (fun t _ z _ => ?_)
    have h1 : HasDerivAt (fun w : ℂ => -(w * (t : ℂ))) (-(t : ℂ)) z := by
      have h0 := (hasDerivAt_id z).mul_const (-(t : ℂ))
      simpa using h0
    have h3 := (h1.cexp).const_mul (f t)
    convert h3 using 1
    ring
  
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℂ) (E := ℂ) (μ := MeasureTheory.volume) (a := (0:ℝ)) (b := T)
    (F := fun (w : ℂ) (t : ℝ) => f t * Complex.exp (-(w * (t : ℂ))))
    (F' := fun (w : ℂ) (t : ℝ) => f t * (-(t : ℂ)) * Complex.exp (-(w * (t : ℂ))))
    (x₀ := z₀) (s := Metric.ball z₀ 1)
    (bound := fun _ : ℝ => B * T * Real.exp ((‖z₀‖ + 1) * T))
    (Metric.ball_mem_nhds z₀ one_pos) hmeasF (hFII z₀) hmeasF' hbound
    intervalIntegrable_const hderiv
  exact key.2.differentiableAt

theorem erdos357_laplace_tail_bound (f : ℝ → ℂ) (B : ℝ)
    (hmeas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    (hbdd : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (z : ℂ) (hz : 0 < z.re) (T : ℝ) (hT : 0 ≤ T) :
    ‖((∫ t in Set.Ioi (0:ℝ), f t * Complex.exp (-(z * (t : ℂ))))
        - ∫ t in (0:ℝ)..T, f t * Complex.exp (-(z * (t : ℂ))))
      * Complex.exp (z * (T : ℂ))‖ ≤ B / z.re :=
by
  
  have hB0 : 0 ≤ B := le_trans (norm_nonneg (f 0)) (hbdd 0 le_rfl)
  have hnegre : ∀ t : ℝ, (-(z * (t : ℂ))).re = -(z.re * t) := by
    intro t
    simp [Complex.mul_re]
  have hnormexp : ∀ t : ℝ, ‖Complex.exp (-(z * (t : ℂ)))‖ = Real.exp (-(z.re * t)) := by
    intro t
    rw [Complex.norm_exp, hnegre t]
  have hmaj : ∀ t : ℝ, 0 ≤ t →
      ‖f t * Complex.exp (-(z * (t : ℂ)))‖ ≤ B * Real.exp (-(z.re * t)) := by
    intro t ht
    rw [norm_mul, hnormexp t]
    exact mul_le_mul_of_nonneg_right (hbdd t ht) (Real.exp_pos _).le
  
  have hgint : ∀ a : ℝ,
      MeasureTheory.IntegrableOn (fun t : ℝ => B * Real.exp (-(z.re * t)))
        (Set.Ioi a) MeasureTheory.volume := by
    intro a
    have h := (exp_neg_integrableOn_Ioi a hz).const_mul B
    simpa only [neg_mul] using h
  
  have hcont : Continuous (fun t : ℝ => Complex.exp (-(z * (t : ℂ)))) := by fun_prop
  have hmeasphi : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => f t * Complex.exp (-(z * (t : ℂ)))) MeasureTheory.volume :=
    hmeas.mul hcont.aestronglyMeasurable
  have hphi0 : MeasureTheory.IntegrableOn
      (fun t : ℝ => f t * Complex.exp (-(z * (t : ℂ)))) (Set.Ioi (0:ℝ)) MeasureTheory.volume := by
    refine (hgint 0).mono' hmeasphi.restrict ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
    intro t ht
    exact hmaj t (le_of_lt ht)
  have hphiT : MeasureTheory.IntegrableOn
      (fun t : ℝ => f t * Complex.exp (-(z * (t : ℂ)))) (Set.Ioi T) MeasureTheory.volume :=
    hphi0.mono_set (Set.Ioi_subset_Ioi hT)
  have hphiIoc : MeasureTheory.IntegrableOn
      (fun t : ℝ => f t * Complex.exp (-(z * (t : ℂ)))) (Set.Ioc (0:ℝ) T) MeasureTheory.volume :=
    hphi0.mono_set Set.Ioc_subset_Ioi_self
  
  have hsplit : (∫ t in Set.Ioi (0:ℝ), f t * Complex.exp (-(z * (t : ℂ))))
      - (∫ t in (0:ℝ)..T, f t * Complex.exp (-(z * (t : ℂ))))
      = ∫ t in Set.Ioi T, f t * Complex.exp (-(z * (t : ℂ))) := by
    have hunion : (∫ t in Set.Ioc (0:ℝ) T, f t * Complex.exp (-(z * (t : ℂ))))
        + (∫ t in Set.Ioi T, f t * Complex.exp (-(z * (t : ℂ))))
        = ∫ t in Set.Ioi (0:ℝ), f t * Complex.exp (-(z * (t : ℂ))) := by
      rw [← MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        hphiIoc hphiT, Set.Ioc_union_Ioi_eq_Ioi hT]
    rw [intervalIntegral.integral_of_le hT, ← hunion]
    ring
  
  have hexpval : (∫ t in Set.Ioi T, Real.exp (-(z.re * t))) = Real.exp (-(z.re * T)) / z.re := by
    have h := integral_exp_mul_Ioi (a := -z.re) (by linarith) T
    simpa only [neg_mul, neg_div_neg_eq] using h
  have htail : ‖∫ t in Set.Ioi T, f t * Complex.exp (-(z * (t : ℂ)))‖
      ≤ B * Real.exp (-(z.re * T)) / z.re := by
    have h1 : ‖∫ t in Set.Ioi T, f t * Complex.exp (-(z * (t : ℂ)))‖
        ≤ ∫ t in Set.Ioi T, B * Real.exp (-(z.re * t)) := by
      refine MeasureTheory.norm_integral_le_of_norm_le (hgint T) ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro t ht
      exact hmaj t (le_trans hT (le_of_lt ht))
    have h2 : (∫ t in Set.Ioi T, B * Real.exp (-(z.re * t)))
        = B * Real.exp (-(z.re * T)) / z.re := by
      rw [MeasureTheory.integral_const_mul, hexpval, mul_div_assoc]
    linarith [h1, h2.le, h2.ge]
  
  have hexpT : ‖Complex.exp (z * (T : ℂ))‖ = Real.exp (z.re * T) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  have hcancel : Real.exp (-(z.re * T)) * Real.exp (z.re * T) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hsplit, norm_mul, hexpT]
  have hstep := mul_le_mul_of_nonneg_right htail (Real.exp_pos (z.re * T)).le
  refine le_trans hstep (le_of_eq ?_)
  calc B * Real.exp (-(z.re * T)) / z.re * Real.exp (z.re * T)
      = B * (Real.exp (-(z.re * T)) * Real.exp (z.re * T)) / z.re := by ring
    _ = B * 1 / z.re := by rw [hcancel]
    _ = B / z.re := by ring

theorem erdos357_truncated_laplace_bound (f : ℝ → ℂ) (B : ℝ)
    (hmeas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    (hbdd : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (z : ℂ) (hz : z.re < 0) (T : ℝ) (hT : 0 ≤ T) :
    ‖(∫ t in (0:ℝ)..T, f t * Complex.exp (-(z * (t : ℂ)))) * Complex.exp (z * (T : ℂ))‖
      ≤ B / (-z.re) :=
by
  
  have hB0 : 0 ≤ B := le_trans (norm_nonneg (f 0)) (hbdd 0 le_rfl)
  
  have hc : (0:ℝ) < -z.re := neg_pos.mpr hz
  have hcne : (-z.re) ≠ 0 := ne_of_gt hc
  have hzne : z.re ≠ 0 := ne_of_lt hz
  
  have hre1 : ∀ t : ℝ, (-(z * (t : ℂ))).re = (-z.re) * t := by
    intro t
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hptwise : ∀ t : ℝ, 0 ≤ t →
      ‖f t * Complex.exp (-(z * (t : ℂ)))‖ ≤ B * Real.exp ((-z.re) * t) := by
    intro t ht
    rw [norm_mul, Complex.norm_exp, hre1 t]
    exact mul_le_mul_of_nonneg_right (hbdd t ht) (Real.exp_pos _).le
  have hcont : Continuous (fun t : ℝ => B * Real.exp ((-z.re) * t)) := by fun_prop
  
  have hnormint : ‖∫ t in (0:ℝ)..T, f t * Complex.exp (-(z * (t : ℂ)))‖
      ≤ ∫ t in (0:ℝ)..T, B * Real.exp ((-z.re) * t) :=
    intervalIntegral.norm_integral_le_of_norm_le hT
      (Filter.Eventually.of_forall (fun t ht => hptwise t (le_of_lt ht.1)))
      (hcont.intervalIntegrable 0 T)
  
  have hint : (∫ t in (0:ℝ)..T, B * Real.exp ((-z.re) * t))
      = B * (Real.exp ((-z.re) * T) - 1) / (-z.re) := by
    have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) T,
        HasDerivAt (fun s : ℝ => B * Real.exp ((-z.re) * s) / (-z.re))
          (B * Real.exp ((-z.re) * t)) t := by
      intro t _
      have h1 : HasDerivAt (fun s : ℝ => (-z.re) * s) (-z.re) t := by
        simpa using (hasDerivAt_id t).const_mul (-z.re)
      have h2 : HasDerivAt (fun s : ℝ => Real.exp ((-z.re) * s))
          (Real.exp ((-z.re) * t) * (-z.re)) t := h1.exp
      have h3 := (h2.const_mul B).div_const (-z.re)
      have heq : B * (Real.exp ((-z.re) * t) * (-z.re)) / (-z.re)
          = B * Real.exp ((-z.re) * t) := by
        field_simp
      rwa [heq] at h3
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 T)]
    rw [mul_zero, Real.exp_zero, mul_one]
    ring
  
  have hexpnorm : ‖Complex.exp (z * (T : ℂ))‖ = Real.exp (-((-z.re) * T)) := by
    rw [Complex.norm_exp]
    congr 1
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hEpos : (0:ℝ) < Real.exp ((-z.re) * T) := Real.exp_pos _
  have hEne : Real.exp ((-z.re) * T) ≠ 0 := ne_of_gt hEpos
  have hkey : B * (Real.exp ((-z.re) * T) - 1) / (-z.re) * (Real.exp ((-z.re) * T))⁻¹
      = B / (-z.re) - B / ((-z.re) * Real.exp ((-z.re) * T)) := by
    field_simp
    ring
  
  rw [norm_mul, hexpnorm]
  calc ‖∫ t in (0:ℝ)..T, f t * Complex.exp (-(z * (t : ℂ)))‖ * Real.exp (-((-z.re) * T))
      ≤ (∫ t in (0:ℝ)..T, B * Real.exp ((-z.re) * t)) * Real.exp (-((-z.re) * T)) :=
        mul_le_mul_of_nonneg_right hnormint (Real.exp_nonneg _)
    _ = B * (Real.exp ((-z.re) * T) - 1) / (-z.re) * (Real.exp ((-z.re) * T))⁻¹ := by
        rw [hint, Real.exp_neg]
    _ = B / (-z.re) - B / ((-z.re) * Real.exp ((-z.re) * T)) := hkey
    _ ≤ B / (-z.re) := sub_le_self _ (div_nonneg hB0 (le_of_lt (mul_pos hc hEpos)))

theorem erdos357_newman_left_contour_bound (g : ℂ → ℂ) (B R a T : ℝ)
    (hB : 0 ≤ B) (hR : 1 ≤ R) (ha0 : a < 0) (haR : -R ≤ a)
    (hg : Differentiable ℂ g)
    (hgb : ∀ z : ℂ, z.re < 0 →
      ‖g z * Complex.exp (z * (T : ℂ))‖ ≤ B / (-z.re)) :
    ‖∫ y in (-R)..R,
        g ((a : ℂ) + (y : ℂ) * Complex.I)
          * Complex.exp (((a : ℂ) + (y : ℂ) * Complex.I) * (T : ℂ))
          * (1 + ((a : ℂ) + (y : ℂ) * Complex.I) ^ 2 / (R : ℂ) ^ 2)
          / ((a : ℂ) + (y : ℂ) * Complex.I)‖
      ≤ 14 * B / R :=
by
  have hR0 : (0:ℝ) < R := by linarith
  have hnormRI : ∀ (p q c : ℝ), 0 ≤ c → p ^ 2 + q ^ 2 ≤ c ^ 2 →
      ‖((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I‖ ≤ c := by
    intro p q c hc h
    have h1 : ‖((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I‖ ^ 2 = p ^ 2 + q ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      ring
    nlinarith [norm_nonneg (((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I)]
  have hquot : ∀ (p q w : ℂ) (P Q S : ℝ), ‖p‖ ≤ P → ‖q‖ ≤ Q → 0 < S → S ≤ ‖w‖ → 0 ≤ Q →
      ‖p * q / w‖ ≤ P * Q / S := by
    intro p q w P Q S hp hq hS hw hQ
    have hP : 0 ≤ P := le_trans (norm_nonneg p) hp
    rw [norm_div, norm_mul]
    exact div_le_div₀ (by positivity) (mul_le_mul hp hq (norm_nonneg q) hP) hS hw
  have hreP : ∀ p q : ℝ, (((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I).re = p := by
    intro p q; simp
  have hlowIm : ∀ p q : ℝ, |q| ≤ ‖((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I‖ := by
    intro p q
    simpa using Complex.abs_im_le_norm (((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I)
  have hlowRe : ∀ p q : ℝ, |p| ≤ ‖((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I‖ := by
    intro p q
    simpa using Complex.abs_re_le_norm (((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I)
  have hkerA : ∀ (x s : ℝ), s ^ 2 = R ^ 2 → |x| ≤ R →
      ‖1 + (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I) ^ 2 / ((R : ℝ) : ℂ) ^ 2‖
        ≤ 3 * |x| / R := by
    intro x s hs hx
    have heq : (1 : ℂ) + (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I) ^ 2 / ((R : ℝ) : ℂ) ^ 2
        = (((R : ℝ) : ℂ) ^ 2 + (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I) ^ 2)
          / ((R : ℝ) : ℂ) ^ 2 := by
      have hRne : ((R : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hR0)
      field_simp
    have hcanon : ((R : ℝ) : ℂ) ^ 2 + (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I) ^ 2
        = (((R ^ 2 + x ^ 2 - s ^ 2 : ℝ)) : ℂ) + (((2 * x * s : ℝ)) : ℂ) * Complex.I := by
      push_cast
      linear_combination (((s : ℝ) : ℂ) ^ 2) * Complex.I_sq
    have hden : ‖((R : ℝ) : ℂ) ^ 2‖ = R ^ 2 := by simp [abs_of_pos hR0]
    have hx2 : x ^ 2 ≤ R ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
    have hnum : ‖(((R ^ 2 + x ^ 2 - s ^ 2 : ℝ)) : ℂ) + (((2 * x * s : ℝ)) : ℂ) * Complex.I‖
        ≤ 3 * |x| * R := by
      apply hnormRI
      · positivity
      · have key : (R ^ 2 + x ^ 2 - s ^ 2) ^ 2 + (2 * x * s) ^ 2 = x ^ 4 + 4 * x ^ 2 * R ^ 2 := by
          calc (R ^ 2 + x ^ 2 - s ^ 2) ^ 2 + (2 * x * s) ^ 2
              = (R ^ 2 + x ^ 2 - s ^ 2) ^ 2 + 4 * x ^ 2 * s ^ 2 := by ring
            _ = (R ^ 2 + x ^ 2 - R ^ 2) ^ 2 + 4 * x ^ 2 * R ^ 2 := by rw [hs]
            _ = x ^ 4 + 4 * x ^ 2 * R ^ 2 := by ring
        rw [key]
        nlinarith [sq_abs x, mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx2), sq_nonneg x]
    rw [heq, norm_div, hcanon, hden, div_le_div_iff₀ (by positivity) hR0]
    nlinarith [hnum, hR0, abs_nonneg x]
  have hkerB : ∀ (u v : ℝ), |u| ≤ R → |v| ≤ R →
      ‖1 + (((u : ℝ) : ℂ) + ((v : ℝ) : ℂ) * Complex.I) ^ 2 / ((R : ℝ) : ℂ) ^ 2‖ ≤ 4 := by
    intro u v hu hv
    have heq : (1 : ℂ) + (((u : ℝ) : ℂ) + ((v : ℝ) : ℂ) * Complex.I) ^ 2 / ((R : ℝ) : ℂ) ^ 2
        = (((R : ℝ) : ℂ) ^ 2 + (((u : ℝ) : ℂ) + ((v : ℝ) : ℂ) * Complex.I) ^ 2)
          / ((R : ℝ) : ℂ) ^ 2 := by
      have hRne : ((R : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hR0)
      field_simp
    have hcanon : ((R : ℝ) : ℂ) ^ 2 + (((u : ℝ) : ℂ) + ((v : ℝ) : ℂ) * Complex.I) ^ 2
        = (((R ^ 2 + u ^ 2 - v ^ 2 : ℝ)) : ℂ) + (((2 * u * v : ℝ)) : ℂ) * Complex.I := by
      push_cast
      linear_combination (((v : ℝ) : ℂ) ^ 2) * Complex.I_sq
    have hden : ‖((R : ℝ) : ℂ) ^ 2‖ = R ^ 2 := by simp [abs_of_pos hR0]
    have hu2 : u ^ 2 ≤ R ^ 2 := by nlinarith [sq_abs u, abs_nonneg u]
    have hv2 : v ^ 2 ≤ R ^ 2 := by nlinarith [sq_abs v, abs_nonneg v]
    have hnum : ‖(((R ^ 2 + u ^ 2 - v ^ 2 : ℝ)) : ℂ) + (((2 * u * v : ℝ)) : ℂ) * Complex.I‖
        ≤ 4 * R ^ 2 := by
      apply hnormRI
      · positivity
      · have hA1 : 0 ≤ R ^ 2 + u ^ 2 - v ^ 2 := by nlinarith [sq_nonneg u]
        have hA2 : R ^ 2 + u ^ 2 - v ^ 2 ≤ 2 * R ^ 2 := by nlinarith [sq_nonneg v]
        have hA3 : (R ^ 2 + u ^ 2 - v ^ 2) ^ 2 ≤ 4 * R ^ 4 := by nlinarith
        have hA4 : u ^ 2 * v ^ 2 ≤ R ^ 2 * R ^ 2 := by nlinarith [sq_nonneg u, sq_nonneg v]
        nlinarith [hA3, hA4, sq_nonneg (R ^ 2)]
    rw [heq, norm_div, hcanon, hden]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hnum]
  have key : ∀ A Bt C D : ℂ, ((A - Bt) + Complex.I • C) - Complex.I • D = 0 →
      ‖C‖ ≤ ‖A‖ + ‖Bt‖ + ‖D‖ := by
    intro A Bt C D hEq
    rw [smul_eq_mul, smul_eq_mul] at hEq
    have heq : Complex.I * C = Complex.I * D - (A - Bt) := by linear_combination hEq
    have hn : ‖C‖ = ‖Complex.I * D - (A - Bt)‖ := by
      rw [← heq, norm_mul, Complex.norm_I, one_mul]
    rw [hn]
    calc ‖Complex.I * D - (A - Bt)‖ ≤ ‖Complex.I * D‖ + ‖A - Bt‖ := norm_sub_le _ _
      _ ≤ ‖D‖ + (‖A‖ + ‖Bt‖) := by
          rw [norm_mul, Complex.norm_I, one_mul]
          gcongr
          exact norm_sub_le _ _
      _ = ‖A‖ + ‖Bt‖ + ‖D‖ := by ring
  set h : ℂ → ℂ := fun z : ℂ =>
    g z * Complex.exp (z * (T : ℂ)) * (1 + z ^ 2 / (R : ℂ) ^ 2) / z with hdef
  have hdiff : DifferentiableOn ℂ h (Set.uIcc (-R) a ×ℂ Set.uIcc (-R) R) := by
    have hnum : Differentiable ℂ
        (fun z : ℂ => g z * Complex.exp (z * (T : ℂ)) * (1 + z ^ 2 / (R : ℂ) ^ 2)) := by
      fun_prop
    rw [hdef]
    apply DifferentiableOn.div
    · exact hnum.differentiableOn
    · exact differentiableOn_id
    · intro z hz
      rw [Complex.mem_reProdIm, Set.uIcc_of_le haR] at hz
      intro h0
      have hz2 := hz.1.2
      rw [h0, Complex.zero_re] at hz2
      linarith
  have hrect : (((∫ x in (-R)..a, h ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
        - ∫ x in (-R)..a, h ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
      + Complex.I • ∫ y in (-R)..R, h ((a : ℂ) + (y : ℂ) * Complex.I))
      - Complex.I • ∫ y in (-R)..R, h (((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I) = 0 :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn h ⟨-R, -R⟩ ⟨a, R⟩ hdiff
  have hhor : ∀ s : ℝ, s ^ 2 = R ^ 2 → |s| = R →
      ‖∫ x in (-R)..a, h ((x : ℂ) + ((s : ℝ) : ℂ) * Complex.I)‖ ≤ 3 * B / R := by
    intro s hs2 hsabs
    have hbnd : ∀ x ∈ Set.uIoc (-R) a,
        ‖h ((x : ℂ) + ((s : ℝ) : ℂ) * Complex.I)‖ ≤ 3 * B / R ^ 2 := by
      intro x hx
      rw [Set.uIoc_of_le haR] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have hxneg : x < 0 := lt_of_le_of_lt hx2 ha0
      have hxabs : |x| ≤ R := abs_le.mpr ⟨by linarith, by linarith⟩
      have hznorm : R ≤ ‖((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I‖ := by
        have h1 := hlowIm x s
        rwa [hsabs] at h1
      have hker := hkerA x s hs2 hxabs
      have hzre : (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I).re < 0 := by
        rw [hreP]; exact hxneg
      have h4 := hgb _ hzre
      rw [hreP] at h4
      simp only [hdef]
      refine le_trans (hquot _ _ _ (B / (-x)) (3 * |x| / R) R h4 hker hR0 hznorm
        (by positivity)) ?_
      rw [abs_of_neg hxneg]
      have hnxne : (-x) ≠ 0 := ne_of_gt (by linarith)
      have hxne : x ≠ 0 := ne_of_lt hxneg
      apply le_of_eq
      field_simp
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const hbnd) ?_
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ a - -R)]
    have h3 : 0 ≤ 3 * B / R ^ 2 := by positivity
    calc 3 * B / R ^ 2 * (a - -R) ≤ 3 * B / R ^ 2 * R :=
          mul_le_mul_of_nonneg_left (by linarith) h3
      _ = 3 * B / R := by field_simp
  have hleft : ‖∫ y in (-R)..R, h (((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖ ≤ 8 * B / R := by
    have hbnd : ∀ y ∈ Set.uIoc (-R) R,
        ‖h (((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖ ≤ 4 * B / R ^ 2 := by
      intro y hy
      rw [Set.uIoc_of_le (by linarith : (-R:ℝ) ≤ R)] at hy
      obtain ⟨hy1, hy2⟩ := hy
      have hyabs : |y| ≤ R := abs_le.mpr ⟨by linarith, hy2⟩
      have hRabs : |(-R)| ≤ R := by rw [abs_neg, abs_of_pos hR0]
      have hker := hkerB (-R) y hRabs hyabs
      have hznorm : R ≤ ‖(((-R : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖ := by
        have h1 := hlowRe (-R) y
        rwa [abs_neg, abs_of_pos hR0] at h1
      have hzre : (((-R : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I).re < 0 := by
        rw [hreP]; linarith
      have h4 := hgb _ hzre
      rw [hreP, neg_neg] at h4
      simp only [hdef]
      refine le_trans (hquot _ _ _ (B / R) 4 R h4 hker hR0 hznorm (by norm_num)) ?_
      apply le_of_eq
      field_simp
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const hbnd) ?_
    rw [show |R - -R| = 2 * R from by rw [abs_of_pos (by linarith : (0:ℝ) < R - -R)]; ring]
    apply le_of_eq
    field_simp
    ring
  have hb := hhor (-R) (by ring) (by rw [abs_neg, abs_of_pos hR0])
  have ht := hhor R rfl (abs_of_pos hR0)
  have hc := key _ _ _ _ hrect
  show ‖∫ y in (-R)..R, h ((a : ℂ) + (y : ℂ) * Complex.I)‖ ≤ 14 * B / R
  have h14 : 3 * B / R + 3 * B / R + 8 * B / R = 14 * B / R := by ring
  linarith

theorem erdos357_newman_analytic_theorem (f : ℝ → ℂ) (B : ℝ)
    (hmeas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    (hbdd : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (G : ℂ → ℂ) (U : Set ℂ)
    (hU : IsOpen U) (hsub : {z : ℂ | 0 ≤ z.re} ⊆ U)
    (hGdiff : DifferentiableOn ℂ G U)
    (hrep : ∀ z : ℂ, 0 < z.re →
      G z = ∫ t in Set.Ioi (0:ℝ), f t * Complex.exp (-(z * (t : ℂ)))) :
    Filter.Tendsto (fun T : ℝ => ∫ t in (0:ℝ)..T, f t) Filter.atTop (nhds (G 0)) :=
by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg (f 0)) (hbdd 0 le_rfl)
  
  
  
  have hnormRI : ∀ (p q c : ℝ), 0 ≤ c → p ^ 2 + q ^ 2 ≤ c ^ 2 →
      ‖((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I‖ ≤ c := by
    intro p q c hc h
    have h1 : ‖((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I‖ ^ 2 = p ^ 2 + q ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      ring
    nlinarith [norm_nonneg (((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I)]
  have hquot : ∀ (p q w : ℂ) (P Q S : ℝ), ‖p‖ ≤ P → ‖q‖ ≤ Q → 0 < S → S ≤ ‖w‖ → 0 ≤ Q →
      ‖p * q / w‖ ≤ P * Q / S := by
    intro p q w P Q S hp hq hS hw hQ
    have hP : 0 ≤ P := le_trans (norm_nonneg p) hp
    rw [norm_div, norm_mul]
    exact div_le_div₀ (by positivity) (mul_le_mul hp hq (norm_nonneg q) hP) hS hw
  have htri : ∀ a b c d : ℂ,
      ‖((a - b) + Complex.I • c) - Complex.I • d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    intro a b c d
    have h1 : ‖Complex.I • c‖ = ‖c‖ := by rw [smul_eq_mul, norm_mul, Complex.norm_I, one_mul]
    have h2 : ‖Complex.I • d‖ = ‖d‖ := by rw [smul_eq_mul, norm_mul, Complex.norm_I, one_mul]
    calc ‖((a - b) + Complex.I • c) - Complex.I • d‖
        ≤ ‖(a - b) + Complex.I • c‖ + ‖Complex.I • d‖ := norm_sub_le _ _
      _ ≤ (‖a - b‖ + ‖Complex.I • c‖) + ‖Complex.I • d‖ := by
          gcongr
          exact norm_add_le _ _
      _ ≤ ((‖a‖ + ‖b‖) + ‖Complex.I • c‖) + ‖Complex.I • d‖ := by
          gcongr
          exact norm_sub_le _ _
      _ = ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by rw [h1, h2]
  have hreP : ∀ p q : ℝ, (((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I).re = p := by
    intro p q; simp
  have himP : ∀ p q : ℝ, (((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I).im = q := by
    intro p q; simp
  have hlowIm : ∀ p q : ℝ, |q| ≤ ‖((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I‖ := by
    intro p q
    simpa using Complex.abs_im_le_norm (((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I)
  have hlowRe : ∀ p q : ℝ, |p| ≤ ‖((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I‖ := by
    intro p q
    simpa using Complex.abs_re_le_norm (((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I)
  
  
  
  have main : ∀ R : ℝ, 1 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : ℝ, 1 ≤ T → ‖G 0 - ∫ t in (0:ℝ)..T, f t‖ ≤ 6 * B / R + C / T := by
    intro R hR
    have hR0 : (0:ℝ) < R := by linarith
    have hRne : ((R : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hR0)
    have hRne' : R ≠ 0 := ne_of_gt hR0
    
    have hkerA : ∀ (x s : ℝ), s ^ 2 = R ^ 2 → |x| ≤ R →
        ‖1 + (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I) ^ 2 / ((R : ℝ) : ℂ) ^ 2‖
          ≤ 3 * |x| / R := by
      intro x s hs hx
      have heq : (1 : ℂ) + (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I) ^ 2 / ((R : ℝ) : ℂ) ^ 2
          = (((R : ℝ) : ℂ) ^ 2 + (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I) ^ 2)
            / ((R : ℝ) : ℂ) ^ 2 := by
        field_simp
      have hcanon : ((R : ℝ) : ℂ) ^ 2 + (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I) ^ 2
          = (((R ^ 2 + x ^ 2 - s ^ 2 : ℝ)) : ℂ) + (((2 * x * s : ℝ)) : ℂ) * Complex.I := by
        push_cast
        linear_combination (((s : ℝ) : ℂ) ^ 2) * Complex.I_sq
      have hden : ‖((R : ℝ) : ℂ) ^ 2‖ = R ^ 2 := by simp [abs_of_pos hR0]
      have hx2 : x ^ 2 ≤ R ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
      have hnum : ‖(((R ^ 2 + x ^ 2 - s ^ 2 : ℝ)) : ℂ) + (((2 * x * s : ℝ)) : ℂ) * Complex.I‖
          ≤ 3 * |x| * R := by
        apply hnormRI
        · positivity
        · have key : (R ^ 2 + x ^ 2 - s ^ 2) ^ 2 + (2 * x * s) ^ 2 = x ^ 4 + 4 * x ^ 2 * R ^ 2 := by
            calc (R ^ 2 + x ^ 2 - s ^ 2) ^ 2 + (2 * x * s) ^ 2
                = (R ^ 2 + x ^ 2 - s ^ 2) ^ 2 + 4 * x ^ 2 * s ^ 2 := by ring
              _ = (R ^ 2 + x ^ 2 - R ^ 2) ^ 2 + 4 * x ^ 2 * R ^ 2 := by rw [hs]
              _ = x ^ 4 + 4 * x ^ 2 * R ^ 2 := by ring
          rw [key]
          nlinarith [sq_abs x, mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx2), sq_nonneg x]
      rw [heq, norm_div, hcanon, hden, div_le_div_iff₀ (by positivity) hR0]
      nlinarith [hnum, hR0, abs_nonneg x]
    
    have hkerB : ∀ (u v : ℝ), |u| ≤ R → |v| ≤ R →
        ‖1 + (((u : ℝ) : ℂ) + ((v : ℝ) : ℂ) * Complex.I) ^ 2 / ((R : ℝ) : ℂ) ^ 2‖ ≤ 4 := by
      intro u v hu hv
      have heq : (1 : ℂ) + (((u : ℝ) : ℂ) + ((v : ℝ) : ℂ) * Complex.I) ^ 2 / ((R : ℝ) : ℂ) ^ 2
          = (((R : ℝ) : ℂ) ^ 2 + (((u : ℝ) : ℂ) + ((v : ℝ) : ℂ) * Complex.I) ^ 2)
            / ((R : ℝ) : ℂ) ^ 2 := by
        field_simp
      have hcanon : ((R : ℝ) : ℂ) ^ 2 + (((u : ℝ) : ℂ) + ((v : ℝ) : ℂ) * Complex.I) ^ 2
          = (((R ^ 2 + u ^ 2 - v ^ 2 : ℝ)) : ℂ) + (((2 * u * v : ℝ)) : ℂ) * Complex.I := by
        push_cast
        linear_combination (((v : ℝ) : ℂ) ^ 2) * Complex.I_sq
      have hden : ‖((R : ℝ) : ℂ) ^ 2‖ = R ^ 2 := by simp [abs_of_pos hR0]
      have hu2 : u ^ 2 ≤ R ^ 2 := by nlinarith [sq_abs u, abs_nonneg u]
      have hv2 : v ^ 2 ≤ R ^ 2 := by nlinarith [sq_abs v, abs_nonneg v]
      have hnum : ‖(((R ^ 2 + u ^ 2 - v ^ 2 : ℝ)) : ℂ) + (((2 * u * v : ℝ)) : ℂ) * Complex.I‖
          ≤ 4 * R ^ 2 := by
        apply hnormRI
        · positivity
        · have hA1 : 0 ≤ R ^ 2 + u ^ 2 - v ^ 2 := by nlinarith [sq_nonneg u]
          have hA2 : R ^ 2 + u ^ 2 - v ^ 2 ≤ 2 * R ^ 2 := by nlinarith [sq_nonneg v]
          have hA3 : (R ^ 2 + u ^ 2 - v ^ 2) ^ 2 ≤ 4 * R ^ 4 := by nlinarith
          have hA4 : u ^ 2 * v ^ 2 ≤ R ^ 2 * R ^ 2 := by nlinarith [sq_nonneg u, sq_nonneg v]
          nlinarith [hA3, hA4, sq_nonneg (R ^ 2)]
      rw [heq, norm_div, hcanon, hden]
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hnum]
    
    
    
    obtain ⟨δ, hδ0, hδ1, hRectU⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
        Set.uIcc (-δ) R ×ℂ Set.uIcc (-R) R ⊆ U := by
      have hScomp : IsCompact (Set.Icc (0:ℝ) R ×ℂ Set.Icc (-R) R) :=
        isCompact_Icc.reProdIm isCompact_Icc
      have hSU : (Set.Icc (0:ℝ) R ×ℂ Set.Icc (-R) R) ⊆ U := by
        intro z hz
        rw [Complex.mem_reProdIm] at hz
        exact hsub hz.1.1
      obtain ⟨η, hη, hηU⟩ := hScomp.exists_thickening_subset_open hU hSU
      refine ⟨min 1 (η / 2), lt_min one_pos (by linarith), min_le_left _ _, ?_⟩
      intro z hz
      rw [Complex.mem_reProdIm] at hz
      obtain ⟨hzre, hzim⟩ := hz
      have hd0 : (0:ℝ) < min 1 (η / 2) := lt_min one_pos (by linarith)
      rw [Set.uIcc_of_le (by linarith : -min 1 (η / 2) ≤ R)] at hzre
      rw [Set.uIcc_of_le (by linarith : (-R:ℝ) ≤ R)] at hzim
      obtain ⟨hzre1, hzre2⟩ := hzre
      obtain ⟨hzim1, hzim2⟩ := hzim
      by_cases hc : 0 ≤ z.re
      · exact hSU (by rw [Complex.mem_reProdIm]; exact ⟨⟨hc, hzre2⟩, ⟨hzim1, hzim2⟩⟩)
      · push_neg at hc
        apply hηU
        rw [Metric.mem_thickening_iff]
        refine ⟨((z.im : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
        · rw [Complex.mem_reProdIm]
          constructor
          · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
              Complex.I_im]
            constructor <;> [skip; linarith] <;> norm_num
          · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
              Complex.I_im]
            constructor <;> [linarith; linarith] <;> norm_num
        · have hzw : z - ((z.im : ℝ) : ℂ) * Complex.I = ((z.re : ℝ) : ℂ) := by
            simp [Complex.ext_iff]
          rw [dist_eq_norm, hzw, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hc]
          have : min 1 (η / 2) ≤ η / 2 := min_le_right _ _
          linarith
    have hδR : δ ≤ R := le_trans hδ1 hR
    have hδne : δ ≠ 0 := ne_of_gt hδ0
    
    
    
    obtain ⟨M, hM0, hMbd⟩ : ∃ M : ℝ, 0 ≤ M ∧
        ∀ z ∈ Set.uIcc (-δ) (0:ℝ) ×ℂ Set.uIcc (-R) R, ‖G z‖ ≤ M := by
      have hcomp : IsCompact (Set.uIcc (-δ) (0:ℝ) ×ℂ Set.uIcc (-R) R) :=
        isCompact_uIcc.reProdIm isCompact_uIcc
      have hsub2 : Set.uIcc (-δ) (0:ℝ) ×ℂ Set.uIcc (-R) R
          ⊆ Set.uIcc (-δ) R ×ℂ Set.uIcc (-R) R := by
        intro z hz
        rw [Complex.mem_reProdIm] at hz ⊢
        refine ⟨?_, hz.2⟩
        exact Set.uIcc_subset_uIcc Set.left_mem_uIcc
          (Set.mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩)) hz.1
      obtain ⟨M0, hM0'⟩ := hcomp.exists_bound_of_continuousOn
        (hGdiff.continuousOn.mono (hsub2.trans hRectU))
      exact ⟨max M0 0, le_max_right _ _, fun z hz => le_trans (hM0' z hz) (le_max_left _ _)⟩
    refine ⟨2 * M + 2 * R * M / δ ^ 2, by positivity, ?_⟩
    intro T hT
    have hT0 : (0:ℝ) < T := by linarith
    have hTne : T ≠ 0 := ne_of_gt hT0
    
    have hexpbnd : ∀ u : ℝ, 0 ≤ u → u * Real.exp (-(u * T)) ≤ 1 / T := by
      intro u hu
      have h2 : (0 : ℝ) < Real.exp (u * T) := Real.exp_pos _
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ h2 hT0]
      nlinarith [Real.add_one_le_exp (u * T)]
    have hexpn : ∀ p q : ℝ,
        ‖Complex.exp (((((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I)) * ((T : ℝ) : ℂ))‖
          = Real.exp (p * T) := by
      intro p q
      have h : (((((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I)) * ((T : ℝ) : ℂ)).re = p * T := by
        simp [Complex.mul_re]
      rw [Complex.norm_exp, h]
    have hgTdiff : Differentiable ℂ
        (fun z : ℂ => ∫ t in (0:ℝ)..T, f t * Complex.exp (-(z * (t : ℂ)))) :=
      erdos357_truncated_laplace_differentiable f B T hT0.le hmeas hbdd
    
    
    
    set F : ℂ → ℂ := fun z : ℂ =>
      (G z - ∫ t in (0:ℝ)..T, f t * Complex.exp (-(z * (t : ℂ))))
        * Complex.exp (z * ((T : ℝ) : ℂ)) * (1 + z ^ 2 / ((R : ℝ) : ℂ) ^ 2) with hFdef
    have hsplitgen : ∀ z : ℂ, F z / z
        = G z * Complex.exp (z * ((T : ℝ) : ℂ)) * (1 + z ^ 2 / ((R : ℝ) : ℂ) ^ 2) / z
          - (∫ t in (0:ℝ)..T, f t * Complex.exp (-(z * (t : ℂ))))
              * Complex.exp (z * ((T : ℝ) : ℂ)) * (1 + z ^ 2 / ((R : ℝ) : ℂ) ^ 2) / z := by
      intro z
      simp only [hFdef]
      ring
    have hFdiff : DifferentiableOn ℂ F U := by
      rw [hFdef]
      apply DifferentiableOn.mul
      · apply DifferentiableOn.mul
        · exact hGdiff.sub hgTdiff.differentiableOn
        · exact (Complex.differentiable_exp.comp (differentiable_id.mul_const _)).differentiableOn
      · exact ((differentiable_const 1).add
          ((differentiable_id.pow 2).div_const _)).differentiableOn
    have hcontour := erdos357_rect_residue_simple_pole F U (-δ) R (-R) R hU hFdiff
      (by linarith) hR0 (by linarith) hR0 hRectU
    have hF0 : F 0 = G 0 - ∫ t in (0:ℝ)..T, f t := by
      rw [hFdef]; simp
    
    
    
    have hhoriz : ∀ s : ℝ, s ^ 2 = R ^ 2 → |s| = R →
        ‖∫ x in (-δ)..R, F (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)
            / (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)‖
          ≤ (3 * B / R ^ 2 + 3 * M / (R ^ 2 * T)) * (R + δ) := by
      intro s hs2 hsabs
      have hsle := abs_le.mp (le_of_eq hsabs)
      have hbnd : ∀ x ∈ Set.uIoc (-δ) R,
          ‖F (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)
            / (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)‖
            ≤ 3 * B / R ^ 2 + 3 * M / (R ^ 2 * T) := by
        intro x hx
        rw [Set.uIoc_of_le (by linarith : (-δ:ℝ) ≤ R)] at hx
        obtain ⟨hx1, hx2⟩ := hx
        have hxabs : |x| ≤ R := abs_le.mpr ⟨by linarith, hx2⟩
        have hznorm : R ≤ ‖((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I‖ := by
          have h := hlowIm x s
          rwa [hsabs] at h
        have hker := hkerA x s hs2 hxabs
        by_cases hx0 : 0 < x
        case pos =>
          
          have hxne : x ≠ 0 := ne_of_gt hx0
          have hzpos : (0:ℝ) < (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I).re := by
            rw [hreP]; exact hx0
          have h3 := erdos357_laplace_tail_bound f B hmeas hbdd
            (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I) hzpos T hT0.le
          rw [← hrep _ hzpos, hreP] at h3
          simp only [hFdef]
          refine le_trans (hquot _ _ _ (B / x) (3 * |x| / R) R h3 hker hR0 hznorm
            (by positivity)) ?_
          rw [abs_of_pos hx0]
          have heq : B / x * (3 * x / R) / R = 3 * B / R ^ 2 := by field_simp <;> ring
          rw [heq]
          have hnn : (0:ℝ) ≤ 3 * M / (R ^ 2 * T) := div_nonneg (by linarith) (by positivity)
          linarith
        case neg =>
          
          push_neg at hx0
          have hzmem : (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)
              ∈ Set.uIcc (-δ) (0:ℝ) ×ℂ Set.uIcc (-R) R := by
            rw [Complex.mem_reProdIm, hreP, himP]
            exact ⟨Set.mem_uIcc.mpr (Or.inl ⟨by linarith, hx0⟩),
              Set.mem_uIcc.mpr (Or.inl ⟨hsle.1, hsle.2⟩)⟩
          rw [hsplitgen]
          refine le_trans (norm_sub_le _ _) ?_
          have hGz : ‖G (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)‖ ≤ M := hMbd _ hzmem
          have hGpart : ‖G (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)
              * Complex.exp ((((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I) * ((T : ℝ) : ℂ))
              * (1 + (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I) ^ 2 / ((R : ℝ) : ℂ) ^ 2)
              / (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)‖ ≤ 3 * M / (R ^ 2 * T) := by
            have hp : ‖G (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)
                * Complex.exp ((((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I) * ((T : ℝ) : ℂ))‖
                ≤ M * Real.exp (x * T) := by
              rw [norm_mul, hexpn x s]
              exact mul_le_mul_of_nonneg_right hGz (Real.exp_pos _).le
            refine le_trans (hquot _ _ _ (M * Real.exp (x * T)) (3 * |x| / R) R hp hker hR0
              hznorm (by positivity)) ?_
            rw [abs_of_nonpos hx0, show x * T = -(-x * T) from by ring]
            have hkey : (-x) * Real.exp (-(-x * T)) ≤ 1 / T := hexpbnd (-x) (by linarith)
            have hgoal : M * Real.exp (-(-x * T)) * (3 * -x / R) / R
                = (3 * M / R ^ 2) * ((-x) * Real.exp (-(-x * T))) := by field_simp <;> ring
            rw [hgoal]
            calc (3 * M / R ^ 2) * ((-x) * Real.exp (-(-x * T)))
                ≤ (3 * M / R ^ 2) * (1 / T) :=
                  mul_le_mul_of_nonneg_left hkey (by positivity)
              _ = 3 * M / (R ^ 2 * T) := by field_simp <;> ring
          have hgpart : ‖(∫ t in (0:ℝ)..T, f t * Complex.exp
                (-((((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I) * (t : ℂ))))
              * Complex.exp ((((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I) * ((T : ℝ) : ℂ))
              * (1 + (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I) ^ 2 / ((R : ℝ) : ℂ) ^ 2)
              / (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)‖ ≤ 3 * B / R ^ 2 := by
            rcases lt_or_eq_of_le hx0 with hlt | heqx
            · have hzneg : (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I).re < 0 := by
                rw [hreP]; exact hlt
              have h4 := erdos357_truncated_laplace_bound f B hmeas hbdd
                (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I) hzneg T hT0.le
              rw [hreP] at h4
              refine le_trans (hquot _ _ _ (B / (-x)) (3 * |x| / R) R h4 hker hR0 hznorm
                (by positivity)) ?_
              rw [abs_of_nonpos hx0]
              have hxne : x ≠ 0 := ne_of_lt hlt
              have hnxne : (-x) ≠ 0 := neg_ne_zero.mpr hxne
              have heq3 : B / (-x) * (3 * -x / R) / R = 3 * B / R ^ 2 := by field_simp <;> ring
              rw [heq3]
            · have habs0 : |x| = 0 := by simp [heqx]
              have hk0 : ‖1 + (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I) ^ 2
                  / ((R : ℝ) : ℂ) ^ 2‖ ≤ 0 := by
                rw [habs0] at hker; simpa using hker
              have hz0 : (1 + (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I) ^ 2
                  / ((R : ℝ) : ℂ) ^ 2) = 0 := norm_le_zero_iff.mp hk0
              rw [hz0]
              simp only [mul_zero, zero_div, norm_zero]
              exact div_nonneg (by linarith) (by positivity)
          linarith
      refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const hbnd) ?_
      rw [show |R - -δ| = R + δ from by rw [abs_of_pos (by linarith : (0:ℝ) < R - -δ)]; ring]
    
    
    
    have hright : ‖∫ y in (-R)..R, F (((R : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)
        / (((R : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖ ≤ (4 * B / R ^ 2) * (2 * R) := by
      have hbnd : ∀ y ∈ Set.uIoc (-R) R,
          ‖F (((R : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)
            / (((R : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖ ≤ 4 * B / R ^ 2 := by
        intro y hy
        rw [Set.uIoc_of_le (by linarith : (-R:ℝ) ≤ R)] at hy
        obtain ⟨hy1, hy2⟩ := hy
        have hyabs : |y| ≤ R := abs_le.mpr ⟨by linarith, hy2⟩
        have hRabs : |R| ≤ R := le_of_eq (abs_of_pos hR0)
        have hker := hkerB R y hRabs hyabs
        have hznorm : R ≤ ‖((R : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I‖ := by
          have h := hlowRe R y
          rwa [abs_of_pos hR0] at h
        have hzpos : (0:ℝ) < (((R : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I).re := by
          rw [hreP]; exact hR0
        have h3 := erdos357_laplace_tail_bound f B hmeas hbdd
          (((R : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I) hzpos T hT0.le
        rw [← hrep _ hzpos, hreP] at h3
        simp only [hFdef]
        refine le_trans (hquot _ _ _ (B / R) 4 R h3 hker hR0 hznorm (by norm_num)) ?_
        rw [show B / R * 4 / R = 4 * B / R ^ 2 from by field_simp <;> ring]
      refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const hbnd) ?_
      rw [show |R - -R| = 2 * R from by rw [abs_of_pos (by linarith : (0:ℝ) < R - -R)]; ring]
    
    
    
    have hpne : ∀ y : ℝ, (((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I) ≠ 0 := by
      intro y hy
      have h1 : (((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I).re = -δ := hreP (-δ) y
      rw [hy, Complex.zero_re] at h1
      linarith
    have hpcont : Continuous (fun y : ℝ => (((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) := by
      fun_prop
    have hmapsU : Set.MapsTo (fun y : ℝ => (((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
        (Set.uIcc (-R) R) U := by
      intro y hy
      show (((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I) ∈ U
      apply hRectU
      rw [Complex.mem_reProdIm, hreP, himP]
      exact ⟨Set.left_mem_uIcc, hy⟩
    have hIG : IntervalIntegrable
        (fun y : ℝ => G ((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
          * Complex.exp (((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) * ((T : ℝ) : ℂ))
          * (1 + ((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) ^ 2 / ((R : ℝ) : ℂ) ^ 2)
          / ((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))) MeasureTheory.volume (-R) R := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div
      · apply ContinuousOn.mul
        · apply ContinuousOn.mul
          · exact hGdiff.continuousOn.comp hpcont.continuousOn hmapsU
          · exact (Complex.continuous_exp.comp (hpcont.mul continuous_const)).continuousOn
        · exact (continuous_const.add ((hpcont.pow 2).div_const _)).continuousOn
      · exact hpcont.continuousOn
      · intro y _
        exact hpne y
    have hIg : IntervalIntegrable
        (fun y : ℝ => (∫ t in (0:ℝ)..T, f t * Complex.exp
              (-(((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) * (t : ℂ))))
          * Complex.exp (((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) * ((T : ℝ) : ℂ))
          * (1 + ((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) ^ 2 / ((R : ℝ) : ℂ) ^ 2)
          / ((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))) MeasureTheory.volume (-R) R := by
      apply Continuous.intervalIntegrable
      apply Continuous.div
      · exact ((hgTdiff.continuous.comp hpcont).mul
          (Complex.continuous_exp.comp (hpcont.mul continuous_const))).mul
          (continuous_const.add ((hpcont.pow 2).div_const _))
      · exact hpcont
      · exact hpne
    have hleftsplit :
        (∫ y in (-R)..R, F ((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
            / ((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)))
        = (∫ y in (-R)..R, G ((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
            * Complex.exp (((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) * ((T : ℝ) : ℂ))
            * (1 + ((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) ^ 2 / ((R : ℝ) : ℂ) ^ 2)
            / ((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)))
          - (∫ y in (-R)..R, (∫ t in (0:ℝ)..T, f t * Complex.exp
                (-(((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) * (t : ℂ))))
            * Complex.exp (((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) * ((T : ℝ) : ℂ))
            * (1 + ((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) ^ 2 / ((R : ℝ) : ℂ) ^ 2)
            / ((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))) := by
      rw [← intervalIntegral.integral_sub hIG hIg]
      exact intervalIntegral.integral_congr (fun y _ => hsplitgen _)
    have hA4G : ‖∫ y in (-R)..R, G ((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
            * Complex.exp (((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) * ((T : ℝ) : ℂ))
            * (1 + ((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) ^ 2 / ((R : ℝ) : ℂ) ^ 2)
            / ((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))‖
        ≤ (4 * M * Real.exp (-(δ * T)) / δ) * (2 * R) := by
      have hbnd : ∀ y ∈ Set.uIoc (-R) R,
          ‖G ((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
            * Complex.exp (((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) * ((T : ℝ) : ℂ))
            * (1 + ((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) ^ 2 / ((R : ℝ) : ℂ) ^ 2)
            / ((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))‖
            ≤ 4 * M * Real.exp (-(δ * T)) / δ := by
        intro y hy
        rw [Set.uIoc_of_le (by linarith : (-R:ℝ) ≤ R)] at hy
        obtain ⟨hy1, hy2⟩ := hy
        have hyabs : |y| ≤ R := abs_le.mpr ⟨by linarith, hy2⟩
        have hdabs : |(-δ)| ≤ R := by rw [abs_neg, abs_of_pos hδ0]; linarith
        have hker := hkerB (-δ) y hdabs hyabs
        have hznorm : δ ≤ ‖(((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖ := by
          have h := hlowRe (-δ) y
          rwa [abs_neg, abs_of_pos hδ0] at h
        have hzmem : (((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)
            ∈ Set.uIcc (-δ) (0:ℝ) ×ℂ Set.uIcc (-R) R := by
          rw [Complex.mem_reProdIm, hreP, himP]
          exact ⟨Set.left_mem_uIcc, Set.mem_uIcc.mpr (Or.inl ⟨by linarith, hy2⟩)⟩
        have hGz : ‖G (((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖ ≤ M := hMbd _ hzmem
        have hp : ‖G (((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)
            * Complex.exp (((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) * ((T : ℝ) : ℂ))‖
            ≤ M * Real.exp (-δ * T) := by
          rw [norm_mul, hexpn (-δ) y]
          exact mul_le_mul_of_nonneg_right hGz (Real.exp_pos _).le
        refine le_trans (hquot _ _ _ (M * Real.exp (-δ * T)) 4 δ hp hker hδ0 hznorm
          (by norm_num)) ?_
        rw [show (-δ) * T = -(δ * T) from by ring]
        apply le_of_eq
        ring
      refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const hbnd) ?_
      rw [show |R - -R| = 2 * R from by rw [abs_of_pos (by linarith : (0:ℝ) < R - -R)]; ring]
    have hA4g : ‖∫ y in (-R)..R, (∫ t in (0:ℝ)..T, f t * Complex.exp
              (-(((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) * (t : ℂ))))
            * Complex.exp (((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) * ((T : ℝ) : ℂ))
            * (1 + ((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) ^ 2 / ((R : ℝ) : ℂ) ^ 2)
            / ((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))‖ ≤ 14 * B / R := by
      have hgb : ∀ z : ℂ, z.re < 0 →
          ‖(∫ t in (0:ℝ)..T, f t * Complex.exp (-(z * (t : ℂ))))
            * Complex.exp (z * ((T : ℝ) : ℂ))‖ ≤ B / (-z.re) :=
        fun z hz => erdos357_truncated_laplace_bound f B hmeas hbdd z hz T hT0.le
      exact erdos357_newman_left_contour_bound
        (fun z : ℂ => ∫ t in (0:ℝ)..T, f t * Complex.exp (-(z * (t : ℂ))))
        B R (-δ) T hB0 hR (by linarith) (by linarith) hgTdiff hgb
    have hA4 : ‖∫ y in (-R)..R, F ((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
        / ((((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))‖
        ≤ (4 * M * Real.exp (-(δ * T)) / δ) * (2 * R) + 14 * B / R := by
      rw [hleftsplit]
      exact le_trans (norm_sub_le _ _) (add_le_add hA4G hA4g)
    
    
    
    have hnorm2 : ‖(2:ℂ)‖ = (2:ℝ) := by norm_num
    have hnormpi : ‖((Real.pi : ℝ) : ℂ)‖ = Real.pi := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hE : ‖2 * ((Real.pi : ℝ) : ℂ) * Complex.I * F 0‖
        = 2 * Real.pi * ‖G 0 - ∫ t in (0:ℝ)..T, f t‖ := by
      rw [hF0, norm_mul, norm_mul, norm_mul, Complex.norm_I, hnorm2, hnormpi, mul_one]
    have hstep1 : 2 * Real.pi * ‖G 0 - ∫ t in (0:ℝ)..T, f t‖
        ≤ ‖∫ x in (-δ)..R, F (((x : ℝ) : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)
              / (((x : ℝ) : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)‖
          + ‖∫ x in (-δ)..R, F (((x : ℝ) : ℂ) + ((R : ℝ) : ℂ) * Complex.I)
              / (((x : ℝ) : ℂ) + ((R : ℝ) : ℂ) * Complex.I)‖
          + ‖∫ y in (-R)..R, F (((R : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)
              / (((R : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖
          + ‖∫ y in (-R)..R, F (((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)
              / (((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖ := by
      rw [← hE, ← hcontour]
      exact htri _ _ _ _
    have hh1 := hhoriz (-R) (by ring) (by rw [abs_neg, abs_of_pos hR0])
    have hh2 := hhoriz R (by ring) (abs_of_pos hR0)
    
    have hEdT : Real.exp (-(δ * T)) * (δ * T) ≤ 1 := by
      have h := hexpbnd δ hδ0.le
      have hTT : (1 / T) * T = 1 := by field_simp
      have h2 := mul_le_mul_of_nonneg_right h hT0.le
      rw [hTT] at h2
      calc Real.exp (-(δ * T)) * (δ * T) = δ * Real.exp (-(δ * T)) * T := by ring
        _ ≤ 1 := h2
    have hEb : (4 * M * Real.exp (-(δ * T)) / δ) * (2 * R) ≤ 8 * (R * M / (δ ^ 2 * T)) := by
      have heq : (4 * M * Real.exp (-(δ * T)) / δ) * (2 * R)
          = (8 * R * M / δ) * Real.exp (-(δ * T)) := by field_simp <;> ring
      have heq2 : (8:ℝ) * (R * M / (δ ^ 2 * T)) = (8 * R * M / δ) * (1 / (δ * T)) := by
        field_simp <;> ring
      rw [heq, heq2]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [le_div_iff₀ (by positivity)]
      exact hEdT
    have hcnn : (0:ℝ) ≤ 3 * B / R ^ 2 + 3 * M / (R ^ 2 * T) :=
      add_nonneg (div_nonneg (by linarith) (by positivity))
        (div_nonneg (by linarith) (by positivity))
    have hhb : (3 * B / R ^ 2 + 3 * M / (R ^ 2 * T)) * (R + δ)
        ≤ 6 * (B / R) + 6 * (M / (R * T)) := by
      calc (3 * B / R ^ 2 + 3 * M / (R ^ 2 * T)) * (R + δ)
          ≤ (3 * B / R ^ 2 + 3 * M / (R ^ 2 * T)) * (2 * R) :=
            mul_le_mul_of_nonneg_left (by linarith) hcnn
        _ = 6 * (B / R) + 6 * (M / (R * T)) := by field_simp <;> ring
    have hrb : (4 * B / R ^ 2) * (2 * R) = 8 * (B / R) := by field_simp <;> ring
    have hcomb : 2 * Real.pi * ‖G 0 - ∫ t in (0:ℝ)..T, f t‖
        ≤ 34 * (B / R) + 12 * (M / (R * T)) + 8 * (R * M / (δ ^ 2 * T)) := by
      have h14 : (14:ℝ) * B / R = 14 * (B / R) := by ring
      linarith [hstep1, hh1, hh2, hright, hA4, hhb, hEb, hrb]
    have hXnn : (0:ℝ) ≤ ‖G 0 - ∫ t in (0:ℝ)..T, f t‖ := norm_nonneg _
    have h6 : 6 * ‖G 0 - ∫ t in (0:ℝ)..T, f t‖
        ≤ 2 * Real.pi * ‖G 0 - ∫ t in (0:ℝ)..T, f t‖ := by
      nlinarith [Real.pi_gt_three]
    have hmrt : M / (R * T) ≤ M / T := div_le_div₀ hM0 le_rfl hT0 (by nlinarith)
    have hb1 : (0:ℝ) ≤ B / R := div_nonneg hB0 hR0.le
    have hb3 : (0:ℝ) ≤ R * M / (δ ^ 2 * T) :=
      div_nonneg (mul_nonneg hR0.le hM0) (by positivity)
    have hCeq : (2 * M + 2 * R * M / δ ^ 2) / T = 2 * (M / T) + 2 * (R * M / (δ ^ 2 * T)) := by
      field_simp <;> ring
    rw [hCeq, show (6:ℝ) * B / R = 6 * (B / R) from by ring]
    linarith
  
  
  
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  set R : ℝ := max 1 (24 * (B + 1) / ε) with hRdef
  have hR1 : (1:ℝ) ≤ R := le_max_left _ _
  have hR0 : (0:ℝ) < R := by linarith
  have hRge : 24 * (B + 1) / ε ≤ R := le_max_right _ _
  obtain ⟨C, hC0, hCk⟩ := main R hR1
  refine ⟨max 1 (4 * C / ε + 1), fun T hT => ?_⟩
  have hT1 : (1:ℝ) ≤ T := le_trans (le_max_left _ _) hT
  have hT2 : 4 * C / ε + 1 ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : (0:ℝ) < T := by linarith
  have hkey := hCk T hT1
  have hb : 6 * B / R ≤ ε / 4 := by
    rw [div_le_iff₀ hR0]
    rw [div_le_iff₀ hε] at hRge
    linarith
  have hc : C / T ≤ ε / 4 := by
    rw [div_le_iff₀ hT0]
    have h : 4 * C / ε ≤ T - 1 := by linarith
    rw [div_le_iff₀ hε] at h
    nlinarith
  have hfin : ‖(∫ t in (0:ℝ)..T, f t) - G 0‖ < ε := by
    rw [norm_sub_rev]
    linarith
  simpa [dist_eq_norm] using hfin

theorem erdos357_primeLogSeries_sub_pole_analytic : ∃ (H : ℂ → ℂ) (U : Set ℂ), IsOpen U ∧ {s : ℂ | 1 ≤ s.re} ⊆ U ∧
      DifferentiableOn ℂ H U ∧
      ∀ s : ℂ, 1 < s.re →
        H s = (∑' p : Nat.Primes, (Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-s))
                - 1 / (s - 1) :=
by
  classical
  
  
  
  
  have partA :
      ∃ (Z : ℂ → ℂ) (V : Set ℂ), IsOpen V ∧ {s : ℂ | 1 ≤ s.re} ⊆ V ∧
        DifferentiableOn ℂ Z V ∧
        ∀ s : ℂ, 1 < s.re → Z s = -deriv riemannZeta s / riemannZeta s - 1 / (s - 1) := by
    have hTC : DirichletCharacter.LFunctionTrivChar 1 = riemannZeta := by
      simp only [DirichletCharacter.LFunctionTrivChar]
      exact DirichletCharacter.LFunction_modOne_eq
    set ζ₁ : ℂ → ℂ := DirichletCharacter.LFunctionTrivChar₁ 1 with hζdef
    have hdiff : Differentiable ℂ ζ₁ := DirichletCharacter.differentiable_LFunctionTrivChar₁ 1
    have hone : ζ₁ 1 ≠ 0 := DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero 1
    have hupd : ∀ z : ℂ, z ≠ 1 → ζ₁ z = (z - 1) * riemannZeta z := by
      intro z hz
      rw [hζdef]
      simp only [DirichletCharacter.LFunctionTrivChar₁]
      rw [Function.update_of_ne hz]
      rw [hTC]
    refine ⟨fun s => -deriv ζ₁ s / ζ₁ s, {s : ℂ | ζ₁ s ≠ 0}, ?_, ?_, ?_, ?_⟩
    · exact IsOpen.preimage hdiff.continuous isOpen_compl_singleton
    · intro s hs
      simp only [Set.mem_setOf_eq] at hs ⊢
      by_cases h1 : s = 1
      · subst h1; exact hone
      · rw [hupd s h1]
        exact mul_ne_zero (sub_ne_zero.mpr h1) (riemannZeta_ne_zero_of_one_le_re hs)
    · have hd2 : Differentiable ℂ (deriv ζ₁) :=
        fun z => ((hdiff.analyticAt z).deriv).differentiableAt
      exact DifferentiableOn.div hd2.neg.differentiableOn hdiff.differentiableOn
        (fun z hz => hz)
    · intro s hs
      have h1 : s ≠ 1 := by
        intro h; rw [h] at hs; simp at hs
      have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (le_of_lt hs)
      have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
      have hmem : s ∈ ({(1:ℂ)}ᶜ : Set ℂ) := by simpa using h1
      have hev : ζ₁ =ᶠ[nhds s] (fun z => (z - 1) * riemannZeta z) := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hmem] with z hz'
        exact hupd z (by simpa using hz')
      have hderiv : deriv ζ₁ s = deriv (fun z : ℂ => (z - 1) * riemannZeta z) s := hev.deriv_eq
      have hdb : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta h1
      have hmul : deriv (fun z : ℂ => (z - 1) * riemannZeta z) s
          = riemannZeta s + (s - 1) * deriv riemannZeta s := by
        have hh : HasDerivAt (fun z : ℂ => (z - 1) * riemannZeta z)
            (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s :=
          ((hasDerivAt_id s).sub_const 1).mul hdb.hasDerivAt
        simpa using hh.deriv
      show -deriv ζ₁ s / ζ₁ s = _
      rw [hderiv, hmul, hupd s h1]
      field_simp
      ring
  
  
  
  
  have partB :
      LSeries.abscissaOfAbsConv
          (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
                          - (if Nat.Prime n then ((Real.log (n : ℝ) : ℝ) : ℂ) else 0))
        ≤ ((1 / 2 : ℝ) : EReal) := by
    set b : ℕ → ℂ := fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
                          - (if Nat.Prime n then ((Real.log (n : ℝ) : ℝ) : ℂ) else 0) with hbdef
    set i : Nat.Primes × ℕ → ℕ := fun x => ((x.1 : ℕ)) ^ (x.2 + 2) with hidef
    
    have hinj : Function.Injective i := by
      rintro ⟨⟨p, hp⟩, k⟩ ⟨⟨q, hq⟩, l⟩ h
      simp only [hidef] at h
      have hpq : p = q := by
        have hdvd : p ∣ q ^ (l + 2) := by
          rw [← h]; exact dvd_pow_self p (by omega)
        exact (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd)
      subst hpq
      have hkl : k + 2 = l + 2 := Nat.pow_right_injective hp.two_le h
      obtain rfl : k = l := by omega
      rfl
    
    have hb0 : ∀ n : ℕ, n ∉ Set.range i → b n = 0 := by
      intro n hn
      by_cases hp : Nat.Prime n
      · have hv : ArithmeticFunction.vonMangoldt n = Real.log (n : ℝ) :=
          ArithmeticFunction.vonMangoldt_apply_prime hp
        simp [hbdef, hp, hv]
      · have hL : ArithmeticFunction.vonMangoldt n = 0 := by
          rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
          intro hpp
          obtain ⟨p, k, hpprime, hk, hpk⟩ := (isPrimePow_nat_iff n).mp hpp
          have hk2 : 2 ≤ k := by
            rcases Nat.lt_or_ge k 2 with h | h
            · exfalso
              have hk1 : k = 1 := by omega
              subst hk1
              rw [pow_one] at hpk
              exact hp (by rw [← hpk]; exact hpprime)
            · exact h
          refine hn ⟨(⟨p, hpprime⟩, k - 2), ?_⟩
          show p ^ (k - 2 + 2) = n
          rw [Nat.sub_add_cancel hk2]
          exact hpk
        simp [hbdef, hp, hL]
    
    refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable ?_
    intro y hy
    have hy0 : (0:ℝ) < y := by linarith
    set F : ℕ → ℝ := fun n => ‖LSeries.term b (y : ℂ) n‖ with hFdef
    have hFsupp : ∀ n ∉ Set.range i, F n = 0 := by
      intro n hn
      simp [hFdef, LSeries.norm_term_eq, hb0 n hn]
    have hsum : Summable F := by
      rw [← Function.Injective.summable_iff hinj hFsupp]
      set ε : ℝ := y - 1/2 with hεdef
      have hε : (0:ℝ) < ε := by rw [hεdef]; linarith
      set ρ : ℝ := (2:ℝ) ^ (-y) with hρdef
      have hρ0 : (0:ℝ) < ρ := Real.rpow_pos_of_pos (by norm_num) _
      have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
      
      have hu : Summable (fun p : Nat.Primes => (1/ε) * ((p : ℕ) : ℝ) ^ (ε - 2*y)) := by
        apply Summable.mul_left
        rw [Nat.Primes.summable_rpow]
        rw [hεdef]; linarith
      have hv : Summable (fun k : ℕ => ρ ^ k) := summable_geometric_of_lt_one hρ0.le hρ1
      have hprod : Summable
          (fun x : Nat.Primes × ℕ => (1/ε) * ((x.1 : ℕ) : ℝ) ^ (ε - 2*y) * ρ ^ x.2) := by
        refine Summable.mul_of_nonneg hu hv ?_ ?_
        · intro p
          have h0 : (0:ℝ) ≤ ((p : ℕ) : ℝ) ^ (ε - 2*y) := Real.rpow_nonneg (by positivity) _
          have h1 : (0:ℝ) ≤ 1/ε := by positivity
          exact mul_nonneg h1 h0
        · intro k
          exact pow_nonneg hρ0.le k
      refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) ?_ hprod
      rintro ⟨⟨p, hp⟩, k⟩
      have hP2 : (2:ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
      have hP0 : (0:ℝ) < (p : ℝ) := by linarith
      have hlogP : (0:ℝ) ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
      have hbv : b (p ^ (k + 2)) = ((Real.log (p : ℝ) : ℝ) : ℂ) := by
        have hnp : ¬ Nat.Prime (p ^ (k + 2)) := Nat.Prime.not_prime_pow (by omega)
        have hmf : (p ^ (k + 2)).minFac = p := hp.pow_minFac (by omega)
        have hipp : IsPrimePow (p ^ (k + 2)) :=
          (isPrimePow_nat_iff _).mpr ⟨p, k + 2, hp, by omega, rfl⟩
        simp [hbdef, hnp, ArithmeticFunction.vonMangoldt_apply, hipp, hmf]
      have hne : (p ^ (k + 2) : ℕ) ≠ 0 := by
        have hpp : 0 < p := hp.pos
        positivity
      have hnorm : F (p ^ (k + 2)) = Real.log (p : ℝ) / ((p ^ (k + 2) : ℕ) : ℝ) ^ y := by
        rw [hFdef]
        simp only [LSeries.norm_term_eq, hne, Complex.ofReal_re]
        rw [hbv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogP]
        simp
      have hcast : (((p ^ (k + 2) : ℕ)) : ℝ) = (p : ℝ) ^ (((k : ℝ) + 2)) := by
        rw [show ((k : ℝ) + 2) = ((k + 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
        push_cast
        ring
      have hden : (((p ^ (k + 2) : ℕ)) : ℝ) ^ y = (p : ℝ) ^ (((k : ℝ) + 2) * y) := by
        rw [hcast, ← Real.rpow_mul hP0.le]
      have hCk : ((p : ℝ) ^ (-y)) ^ k = (p : ℝ) ^ (-(y * (k : ℝ))) := by
        rw [← Real.rpow_natCast ((p : ℝ) ^ (-y)) k, ← Real.rpow_mul hP0.le]
        congr 1
        ring
      have e1 : (p : ℝ) ^ (-ε) * (p : ℝ) ^ (ε - 2*y) = (p : ℝ) ^ (-(2*y)) := by
        rw [← Real.rpow_add hP0]; congr 1; ring
      have e2 : (p : ℝ) ^ (-(2*y)) * (p : ℝ) ^ (-(y * (k : ℝ)))
          = (p : ℝ) ^ (-(((k : ℝ) + 2) * y)) := by
        rw [← Real.rpow_add hP0]; congr 1; ring
      have e3 : Real.log (p : ℝ) / (p : ℝ) ^ (((k : ℝ) + 2) * y)
          = Real.log (p : ℝ) * (p : ℝ) ^ (-(((k : ℝ) + 2) * y)) := by
        rw [Real.rpow_neg hP0.le, div_eq_mul_inv]
      have hid : Real.log (p : ℝ) / (p : ℝ) ^ (((k : ℝ) + 2) * y)
          = (Real.log (p : ℝ) * (p : ℝ) ^ (-ε)) * (p : ℝ) ^ (ε - 2*y)
              * ((p : ℝ) ^ (-y)) ^ k := by
        rw [e3, hCk, ← e2, ← e1]; ring
      have hPε : (0:ℝ) < (p : ℝ) ^ ε := Real.rpow_pos_of_pos hP0 _
      have hlogb : Real.log (p : ℝ) ≤ (p : ℝ) ^ ε / ε := Real.log_le_rpow_div hP0.le hε
      have hA : Real.log (p : ℝ) * (p : ℝ) ^ (-ε) ≤ 1/ε := by
        have h1 : Real.log (p : ℝ) * (p : ℝ) ^ (-ε) ≤ ((p : ℝ) ^ ε / ε) * (p : ℝ) ^ (-ε) :=
          mul_le_mul_of_nonneg_right hlogb (Real.rpow_nonneg hP0.le _)
        have h2 : ((p : ℝ) ^ ε / ε) * (p : ℝ) ^ (-ε) = 1/ε := by
          rw [Real.rpow_neg hP0.le]
          field_simp
        linarith [h1, h2.le, h2.ge]
      have hPy : (p : ℝ) ^ (-y) ≤ ρ := by
        rw [hρdef]
        exact Real.rpow_le_rpow_of_nonpos (by norm_num) hP2 (by linarith)
      have hB0 : (0:ℝ) ≤ (p : ℝ) ^ (ε - 2*y) := Real.rpow_nonneg hP0.le _
      have hC0 : (0:ℝ) ≤ ((p : ℝ) ^ (-y)) ^ k := pow_nonneg (Real.rpow_nonneg hP0.le _) k
      have h2 : ((p : ℝ) ^ (-y)) ^ k ≤ ρ ^ k := by
        have hnn : (0:ℝ) ≤ (p : ℝ) ^ (-y) := Real.rpow_nonneg hP0.le _
        gcongr
      have h1 : (Real.log (p : ℝ) * (p : ℝ) ^ (-ε)) * (p : ℝ) ^ (ε - 2*y)
          ≤ (1/ε) * (p : ℝ) ^ (ε - 2*y) := mul_le_mul_of_nonneg_right hA hB0
      have hfin : (Real.log (p : ℝ) * (p : ℝ) ^ (-ε)) * (p : ℝ) ^ (ε - 2*y)
            * ((p : ℝ) ^ (-y)) ^ k
          ≤ (1/ε) * (p : ℝ) ^ (ε - 2*y) * ρ ^ k := by
        calc (Real.log (p : ℝ) * (p : ℝ) ^ (-ε)) * (p : ℝ) ^ (ε - 2*y) * ((p : ℝ) ^ (-y)) ^ k
            ≤ ((1/ε) * (p : ℝ) ^ (ε - 2*y)) * ((p : ℝ) ^ (-y)) ^ k :=
              mul_le_mul_of_nonneg_right h1 hC0
          _ ≤ ((1/ε) * (p : ℝ) ^ (ε - 2*y)) * ρ ^ k := by
              refine mul_le_mul_of_nonneg_left h2 ?_
              exact mul_nonneg (by positivity) hB0
      show F (i (⟨p, hp⟩, k)) ≤ _
      simp only [hidef]
      rw [hnorm, hden, hid]
      exact hfin
    exact summable_norm_iff.mp hsum
  
  
  
  have partC : ∀ s : ℂ,
      LSeries (fun n : ℕ => if Nat.Prime n then ((Real.log (n : ℝ) : ℝ) : ℂ) else 0) s
        = ∑' p : Nat.Primes, (Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-s) := by
    intro s
    have key : ∀ n : ℕ,
        LSeries.term (fun n : ℕ => if Nat.Prime n then ((Real.log (n : ℝ) : ℝ) : ℂ) else 0) s n
          = Set.indicator {n : ℕ | Nat.Prime n}
              (fun n : ℕ => ((Real.log (n : ℝ) : ℝ) : ℂ) * ((n : ℂ)) ^ (-s)) n := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · simp [LSeries.term, Nat.not_prime_zero]
      · rw [LSeries.term_of_ne_zero hn]
        by_cases hp : Nat.Prime n
        · simp [hp, Complex.cpow_neg, div_eq_mul_inv]
        · simp [hp]
    rw [LSeries, tsum_congr key, ← tsum_subtype]
    rfl
  
  
  
  obtain ⟨Z, V, hVopen, hVsub, hZdiff, hZeq⟩ := partA
  set b : ℕ → ℂ := fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
      - (if Nat.Prime n then ((Real.log (n : ℝ) : ℝ) : ℂ) else 0) with hbdef
  have habs : LSeries.abscissaOfAbsConv b ≤ ((1 / 2 : ℝ) : EReal) := partB
  refine ⟨fun s => Z s - LSeries b s, V ∩ {s : ℂ | (1:ℝ)/2 < s.re}, ?_, ?_, ?_, ?_⟩
  · exact hVopen.inter (isOpen_lt continuous_const Complex.continuous_re)
  · intro s hs
    refine ⟨hVsub hs, ?_⟩
    have h1 : (1:ℝ) ≤ s.re := hs
    simp only [Set.mem_setOf_eq]
    linarith
  · have hsub : V ∩ {s : ℂ | (1:ℝ)/2 < s.re}
        ⊆ {s : ℂ | LSeries.abscissaOfAbsConv b < (s.re : EReal)} := by
      rintro s ⟨-, hs2⟩
      have h2 : (1:ℝ)/2 < s.re := hs2
      have h1 : ((1/2 : ℝ) : EReal) < ((s.re : ℝ) : EReal) := EReal.coe_lt_coe_iff.mpr h2
      exact lt_of_le_of_lt habs h1
    exact DifferentiableOn.sub (hZdiff.mono Set.inter_subset_left)
      ((LSeries_differentiableOn b).mono hsub)
  · intro s hs
    have hs2 : (1:ℝ)/2 < s.re := by linarith
    have hbsum : LSeriesSummable b s := by
      apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
      exact lt_of_le_of_lt habs (EReal.coe_lt_coe_iff.mpr hs2)
    have hLsum : LSeriesSummable (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s :=
      ArithmeticFunction.LSeriesSummable_vonMangoldt hs
    have hfun : (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) - b
        = (fun n : ℕ => if Nat.Prime n then ((Real.log (n : ℝ) : ℝ) : ℂ) else 0) := by
      funext n
      simp only [hbdef, Pi.sub_apply]
      ring
    have hsplit := LSeries_sub hLsum hbsum
    rw [hfun] at hsplit
    have hL : LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s
        = -deriv riemannZeta s / riemannZeta s :=
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
    have ha := partC s
    show Z s - LSeries b s = _
    rw [hZeq s hs, ← ha, hsplit, hL]
    ring

theorem erdos357_theta_exp_eq_tsum_indicator (t : ℝ) :
    ((Chebyshev.theta (Real.exp t) : ℝ) : ℂ)
      = ∑' p : Nat.Primes,
          Set.indicator (Set.Ici (Real.log ((p : ℕ) : ℝ)))
            (fun _ : ℝ => ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ)) t :=
by
  classical
  
  have hmem : ∀ p : Nat.Primes,
      p ∈ Finset.subtype Nat.Prime (Finset.Icc 0 ⌊Real.exp t⌋₊)
        ↔ Real.log ((p : ℕ) : ℝ) ≤ t := by
    intro p
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    rw [Finset.mem_subtype, Finset.mem_Icc]
    constructor
    · rintro ⟨-, h⟩
      exact (Real.log_le_iff_le_exp hp0).mpr ((Nat.le_floor_iff (Real.exp_pos t).le).mp h)
    · intro h
      exact ⟨Nat.zero_le _, (Nat.le_floor_iff (Real.exp_pos t).le).mpr
        ((Real.log_le_iff_le_exp hp0).mp h)⟩
  
  have hzero : ∀ p : Nat.Primes,
      p ∉ Finset.subtype Nat.Prime (Finset.Icc 0 ⌊Real.exp t⌋₊) →
      Set.indicator (Set.Ici (Real.log ((p : ℕ) : ℝ)))
        (fun _ : ℝ => ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ)) t = 0 := by
    intro p hp
    refine Set.indicator_of_notMem ?_ _
    simpa [Set.mem_Ici] using fun h => hp ((hmem p).mpr h)
  
  have hE : ∑ p ∈ Finset.subtype Nat.Prime (Finset.Icc 0 ⌊Real.exp t⌋₊),
        Real.log ((p : ℕ) : ℝ)
      = Chebyshev.theta (Real.exp t) := by
    rw [Chebyshev.theta_eq_sum_Icc]
    exact Finset.sum_subtype_eq_sum_filter (fun q : ℕ => Real.log (q : ℝ))
  
  have hterm : ∀ p ∈ Finset.subtype Nat.Prime (Finset.Icc 0 ⌊Real.exp t⌋₊),
      Set.indicator (Set.Ici (Real.log ((p : ℕ) : ℝ)))
        (fun _ : ℝ => ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ)) t
        = ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) := fun p hp =>
    Set.indicator_of_mem (Set.mem_Ici.mpr ((hmem p).mp hp)) _
  
  calc ((Chebyshev.theta (Real.exp t) : ℝ) : ℂ)
      = ((∑ p ∈ Finset.subtype Nat.Prime (Finset.Icc 0 ⌊Real.exp t⌋₊),
            Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) := by rw [hE]
    _ = ∑ p ∈ Finset.subtype Nat.Prime (Finset.Icc 0 ⌊Real.exp t⌋₊),
            ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) := Complex.ofReal_sum _ _
    _ = ∑ p ∈ Finset.subtype Nat.Prime (Finset.Icc 0 ⌊Real.exp t⌋₊),
            Set.indicator (Set.Ici (Real.log ((p : ℕ) : ℝ)))
              (fun _ : ℝ => ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ)) t :=
          (Finset.sum_congr rfl hterm).symm
    _ = ∑' p : Nat.Primes,
            Set.indicator (Set.Ici (Real.log ((p : ℕ) : ℝ)))
              (fun _ : ℝ => ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ)) t :=
          (tsum_eq_sum hzero).symm

theorem erdos357_logPrime_rpow_summable (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes => Real.log ((p : ℕ) : ℝ) * ((p : ℕ) : ℝ) ^ (-σ)) :=
by
  
  have hε0 : (0 : ℝ) < (σ - 1) / 2 := by linarith
  have hlt : (σ - 1) / 2 - σ < -1 := by linarith
  have hrp : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ ((σ - 1) / 2 - σ)) :=
    Nat.Primes.summable_rpow.mpr hlt
  have hmaj : Summable (fun p : Nat.Primes =>
      (1 / ((σ - 1) / 2)) * ((p : ℕ) : ℝ) ^ ((σ - 1) / 2 - σ)) :=
    hrp.mul_left (1 / ((σ - 1) / 2))
  refine Summable.of_nonneg_of_le ?_ ?_ hmaj
  · intro p
    have hP1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt.le
    exact mul_nonneg (Real.log_nonneg hP1) (Real.rpow_nonneg (by linarith) _)
  · intro p
    have hP0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    have hlog : Real.log ((p : ℕ) : ℝ) ≤ ((p : ℕ) : ℝ) ^ ((σ - 1) / 2) / ((σ - 1) / 2) :=
      Real.log_le_rpow_div hP0.le hε0
    have hpos : (0 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-σ) := (Real.rpow_pos_of_pos hP0 (-σ)).le
    calc Real.log ((p : ℕ) : ℝ) * ((p : ℕ) : ℝ) ^ (-σ)
        ≤ (((p : ℕ) : ℝ) ^ ((σ - 1) / 2) / ((σ - 1) / 2)) * ((p : ℕ) : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_right hlog hpos
      _ = (1 / ((σ - 1) / 2)) *
            (((p : ℕ) : ℝ) ^ ((σ - 1) / 2) * ((p : ℕ) : ℝ) ^ (-σ)) := by ring
      _ = (1 / ((σ - 1) / 2)) * ((p : ℕ) : ℝ) ^ ((σ - 1) / 2 + (-σ)) := by
          rw [Real.rpow_add hP0]
      _ = (1 / ((σ - 1) / 2)) * ((p : ℕ) : ℝ) ^ ((σ - 1) / 2 - σ) := by
          rw [← sub_eq_add_neg]

theorem erdos357_tsum_indicator_laplace {ι : Type*} [Countable ι]
    (A a : ι → ℝ) (hA : ∀ i, 0 ≤ A i) (ha : ∀ i, 0 < a i)
    (w : ℂ) (hw : 0 < w.re)
    (hsum : Summable (fun i => A i * Real.exp (-(w.re * a i)))) :
    (∫ t in Set.Ioi (0:ℝ),
        (∑' i : ι, Set.indicator (Set.Ici (a i)) (fun _ : ℝ => ((A i : ℝ) : ℂ)) t)
          * Complex.exp (-(w * (t : ℂ))))
      = ∑' i : ι, ((A i : ℝ) : ℂ) * Complex.exp (-(w * ((a i : ℝ) : ℂ))) / w :=
by
  
  have hneg : (-w).re < 0 := by
    simp only [Complex.neg_re]
    linarith
  
  have hset : ∀ b : ℝ, 0 < b → Set.Ici b ∩ Set.Ioi (0:ℝ) = Set.Ici b := fun b hb =>
    Set.inter_eq_left.mpr (Set.Ici_subset_Ioi.mpr hb)
  
  have hfun : ∀ (c : ℂ) (b : ℝ) (t : ℝ),
      Set.indicator (Set.Ici b) (fun _ : ℝ => c) t * Complex.exp (-(w * (t : ℂ)))
        = Set.indicator (Set.Ici b) (fun s : ℝ => c * Complex.exp (-(w * (s : ℂ)))) t := by
    intro c b t
    by_cases h : t ∈ Set.Ici b
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
  
  have hintg : ∀ (c : ℂ) (b : ℝ),
      MeasureTheory.IntegrableOn
        (fun t : ℝ => Set.indicator (Set.Ici b) (fun _ : ℝ => c) t * Complex.exp (-(w * (t : ℂ))))
        (Set.Ioi (0:ℝ)) MeasureTheory.volume := by
    intro c b
    have hg : MeasureTheory.IntegrableOn
        (fun t : ℝ => c * Complex.exp (-(w * (t : ℂ)))) (Set.Ioi b) MeasureTheory.volume := by
      simpa only [← neg_mul] using (integrableOn_exp_mul_complex_Ioi hneg b).const_mul c
    have hIci : MeasureTheory.IntegrableOn
        (fun t : ℝ => c * Complex.exp (-(w * (t : ℂ)))) (Set.Ici b) MeasureTheory.volume :=
      hg.congr_set_ae (MeasureTheory.Ioi_ae_eq_Ici).symm
    have hall : MeasureTheory.Integrable
        (Set.indicator (Set.Ici b) (fun t : ℝ => c * Complex.exp (-(w * (t : ℂ)))))
        MeasureTheory.volume :=
      (MeasureTheory.integrable_indicator_iff measurableSet_Ici).mpr hIci
    have hEq : (fun t : ℝ =>
          Set.indicator (Set.Ici b) (fun _ : ℝ => c) t * Complex.exp (-(w * (t : ℂ))))
        = Set.indicator (Set.Ici b) (fun s : ℝ => c * Complex.exp (-(w * (s : ℂ)))) :=
      funext (hfun c b)
    rw [hEq]
    exact hall.integrableOn
  
  have hval : ∀ (c : ℂ) (b : ℝ), 0 < b →
      (∫ t in Set.Ioi (0:ℝ),
          Set.indicator (Set.Ici b) (fun _ : ℝ => c) t * Complex.exp (-(w * (t : ℂ))))
        = c * Complex.exp (-(w * (b : ℂ))) / w := by
    intro c b hb
    simp only [hfun c b]
    rw [MeasureTheory.integral_indicator measurableSet_Ici,
      MeasureTheory.Measure.restrict_restrict measurableSet_Ici, hset b hb,
      integral_Ici_eq_integral_Ioi]
    simp only [← neg_mul]
    rw [MeasureTheory.integral_const_mul, integral_exp_mul_complex_Ioi hneg b, neg_div_neg_eq]
    ring
  
  have hnormpt : ∀ (c : ℂ) (b : ℝ) (t : ℝ),
      ‖Set.indicator (Set.Ici b) (fun _ : ℝ => c) t * Complex.exp (-(w * (t : ℂ)))‖
        = Set.indicator (Set.Ici b) (fun s : ℝ => ‖c‖ * Real.exp (-(w.re * s))) t := by
    intro c b t
    have hre : (-(w * (t : ℂ))).re = -(w.re * t) := by
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    by_cases h : t ∈ Set.Ici b
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, norm_mul, Complex.norm_exp, hre]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul, norm_zero]
  have hnorm : ∀ (c : ℂ) (b : ℝ), 0 < b →
      (∫ t in Set.Ioi (0:ℝ),
          ‖Set.indicator (Set.Ici b) (fun _ : ℝ => c) t * Complex.exp (-(w * (t : ℂ)))‖)
        = ‖c‖ * Real.exp (-(w.re * b)) / w.re := by
    intro c b hb
    simp only [hnormpt c b]
    rw [MeasureTheory.integral_indicator measurableSet_Ici,
      MeasureTheory.Measure.restrict_restrict measurableSet_Ici, hset b hb,
      integral_Ici_eq_integral_Ioi]
    simp only [← neg_mul]
    rw [MeasureTheory.integral_const_mul,
      integral_exp_mul_Ioi (show -w.re < 0 by linarith) b, neg_div_neg_eq]
    ring
  
  have hintF : ∀ i : ι, MeasureTheory.Integrable
      (fun t : ℝ => Set.indicator (Set.Ici (a i)) (fun _ : ℝ => ((A i : ℝ) : ℂ)) t
        * Complex.exp (-(w * (t : ℂ))))
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) :=
    fun i => hintg ((A i : ℝ) : ℂ) (a i)
  have hsummable : Summable (fun i : ι => ∫ t in Set.Ioi (0:ℝ),
      ‖Set.indicator (Set.Ici (a i)) (fun _ : ℝ => ((A i : ℝ) : ℂ)) t
        * Complex.exp (-(w * (t : ℂ)))‖) := by
    refine (hsum.div_const w.re).congr (fun i => ?_)
    rw [hnorm ((A i : ℝ) : ℂ) (a i) (ha i), Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hA i)]
  have hmain := MeasureTheory.integral_tsum_of_summable_integral_norm hintF hsummable
  have hint_eq : (fun t : ℝ =>
        (∑' i : ι, Set.indicator (Set.Ici (a i)) (fun _ : ℝ => ((A i : ℝ) : ℂ)) t)
          * Complex.exp (-(w * (t : ℂ))))
      = (fun t : ℝ => ∑' i : ι,
          Set.indicator (Set.Ici (a i)) (fun _ : ℝ => ((A i : ℝ) : ℂ)) t
            * Complex.exp (-(w * (t : ℂ)))) :=
    funext fun t => tsum_mul_right.symm
  rw [hint_eq]
  exact hmain.symm.trans (tsum_congr fun i => hval ((A i : ℝ) : ℂ) (a i) (ha i))

theorem erdos357_theta_laplace_eq (z : ℂ) (hz : 0 < z.re) :
    (∫ t in Set.Ioi (0:ℝ),
        ((Chebyshev.theta (Real.exp t) * Real.exp (-t) - 1 : ℝ) : ℂ) *
          Complex.exp (-(z * (t : ℂ))))
      = (∑' p : Nat.Primes, (Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-(z + 1))) / (z + 1)
          - 1 / z :=
by
  have hnegz : (-z).re < 0 := by simp only [Complex.neg_re]; linarith
  have hwre : (0:ℝ) < (z + 1).re := by
    simp only [Complex.add_re, Complex.one_re]; linarith
  have hwre1 : (1:ℝ) < (z + 1).re := by
    simp only [Complex.add_re, Complex.one_re]; linarith
  
  have hVint : MeasureTheory.IntegrableOn
      (fun t : ℝ => Complex.exp (-(z * (t : ℂ)))) (Set.Ioi (0:ℝ)) MeasureTheory.volume := by
    simpa only [neg_mul] using integrableOn_exp_mul_complex_Ioi hnegz (0:ℝ)
  
  have hVval : (∫ t in Set.Ioi (0:ℝ), Complex.exp (-(z * (t : ℂ)))) = 1 / z := by
    have h := integral_exp_mul_complex_Ioi hnegz (0:ℝ)
    simp only [neg_mul] at h
    rw [h]
    simp [neg_div_neg_eq]
  
  have hre : ∀ t : ℝ, (-((z + 1) * (t : ℂ))).re = -((z.re + 1) * t) := by
    intro t
    simp only [Complex.neg_re, Complex.mul_re, Complex.add_re, Complex.one_re, Complex.add_im,
      Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hUmeas : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => ((Chebyshev.theta (Real.exp t) : ℝ) : ℂ) * Complex.exp (-((z + 1) * (t : ℂ))))
      (MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))) := by
    have h1 : Measurable (fun t : ℝ => Chebyshev.theta (Real.exp t)) :=
      Chebyshev.theta_mono.measurable.comp Real.measurable_exp
    have h2 : Measurable (fun t : ℝ => ((Chebyshev.theta (Real.exp t) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp h1
    have h3 : Continuous (fun t : ℝ => Complex.exp (-((z + 1) * (t : ℂ)))) := by fun_prop
    exact h2.aestronglyMeasurable.mul h3.aestronglyMeasurable
  have hbound : ∀ t : ℝ,
      ‖((Chebyshev.theta (Real.exp t) : ℝ) : ℂ) * Complex.exp (-((z + 1) * (t : ℂ)))‖
        ≤ Real.log 4 * Real.exp (-z.re * t) := by
    intro t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Chebyshev.theta_nonneg _), Complex.norm_exp, hre t]
    have hth : Chebyshev.theta (Real.exp t) ≤ Real.log 4 * Real.exp t :=
      Chebyshev.theta_le_log4_mul_x (Real.exp_pos t).le
    have hpos : (0:ℝ) ≤ Real.exp (-((z.re + 1) * t)) := (Real.exp_pos _).le
    calc Chebyshev.theta (Real.exp t) * Real.exp (-((z.re + 1) * t))
        ≤ (Real.log 4 * Real.exp t) * Real.exp (-((z.re + 1) * t)) :=
          mul_le_mul_of_nonneg_right hth hpos
      _ = Real.log 4 * Real.exp (-z.re * t) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
  have hG : MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.log 4 * Real.exp (-z.re * t)) (Set.Ioi (0:ℝ)) MeasureTheory.volume :=
    (exp_neg_integrableOn_Ioi (0:ℝ) hz).const_mul (Real.log 4)
  have hUint : MeasureTheory.IntegrableOn
      (fun t : ℝ => ((Chebyshev.theta (Real.exp t) : ℝ) : ℂ) * Complex.exp (-((z + 1) * (t : ℂ))))
      (Set.Ioi (0:ℝ)) MeasureTheory.volume :=
    MeasureTheory.Integrable.mono' hG hUmeas (Filter.Eventually.of_forall hbound)
  
  have hAnn : ∀ p : Nat.Primes, 0 ≤ Real.log ((p : ℕ) : ℝ) := fun p =>
    Real.log_nonneg (by exact_mod_cast p.2.one_lt.le)
  have hapos : ∀ p : Nat.Primes, 0 < Real.log ((p : ℕ) : ℝ) := fun p =>
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hconv : ∀ p : Nat.Primes,
      Real.log ((p : ℕ) : ℝ) * ((p : ℕ) : ℝ) ^ (-((z + 1).re))
        = Real.log ((p : ℕ) : ℝ) * Real.exp (-((z + 1).re * Real.log ((p : ℕ) : ℝ))) := by
    intro p
    have hp : (0:ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    have hcomm : Real.log ((p : ℕ) : ℝ) * (-((z + 1).re))
        = -((z + 1).re * Real.log ((p : ℕ) : ℝ)) := by ring
    rw [Real.rpow_def_of_pos hp, hcomm]
  have hsum : Summable
      (fun p : Nat.Primes =>
        Real.log ((p : ℕ) : ℝ) * Real.exp (-((z + 1).re * Real.log ((p : ℕ) : ℝ)))) :=
    (erdos357_logPrime_rpow_summable ((z + 1).re) hwre1).congr hconv
  have h6 : (∫ t in Set.Ioi (0:ℝ),
        (∑' p : Nat.Primes,
            Set.indicator (Set.Ici (Real.log ((p : ℕ) : ℝ)))
              (fun _ : ℝ => ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ)) t)
          * Complex.exp (-((z + 1) * (t : ℂ))))
      = ∑' p : Nat.Primes, ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ)
          * Complex.exp (-((z + 1) * ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ))) / (z + 1) :=
    erdos357_tsum_indicator_laplace _ _ hAnn hapos (z + 1) hwre hsum
  have hcpow : ∀ p : Nat.Primes,
      ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ)
          * Complex.exp (-((z + 1) * ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ))) / (z + 1)
        = (Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-(z + 1)) / (z + 1) := by
    intro p
    have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
    have hlog : Complex.log ((p : ℕ) : ℂ) = ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_log (Nat.cast_nonneg _), Complex.ofReal_natCast]
    have hex : -((z + 1) * ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ))
        = ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) * (-(z + 1)) := by ring
    rw [Complex.cpow_def_of_ne_zero hp0, hlog, ← hex]
  have hUval : (∫ t in Set.Ioi (0:ℝ),
        ((Chebyshev.theta (Real.exp t) : ℝ) : ℂ) * Complex.exp (-((z + 1) * (t : ℂ))))
      = (∑' p : Nat.Primes, (Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-(z + 1))) / (z + 1) := by
    have hstep : (∫ t in Set.Ioi (0:ℝ),
          ((Chebyshev.theta (Real.exp t) : ℝ) : ℂ) * Complex.exp (-((z + 1) * (t : ℂ))))
        = (∫ t in Set.Ioi (0:ℝ),
            (∑' p : Nat.Primes,
                Set.indicator (Set.Ici (Real.log ((p : ℕ) : ℝ)))
                  (fun _ : ℝ => ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ)) t)
              * Complex.exp (-((z + 1) * (t : ℂ)))) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
      simp only [erdos357_theta_exp_eq_tsum_indicator t]
    rw [hstep, h6, tsum_congr hcpow]
    exact tsum_div_const
  
  have hsplit : ∀ t : ℝ,
      ((Chebyshev.theta (Real.exp t) * Real.exp (-t) - 1 : ℝ) : ℂ) * Complex.exp (-(z * (t : ℂ)))
        = ((Chebyshev.theta (Real.exp t) : ℝ) : ℂ) * Complex.exp (-((z + 1) * (t : ℂ)))
            - Complex.exp (-(z * (t : ℂ))) := by
    intro t
    have he : ((Real.exp (-t) : ℝ) : ℂ) = Complex.exp (-(t : ℂ)) := by
      rw [Complex.ofReal_exp, Complex.ofReal_neg]
    have hexp : -(t : ℂ) + -(z * (t : ℂ)) = -((z + 1) * (t : ℂ)) := by ring
    rw [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_one, he, sub_mul, one_mul,
      mul_assoc, ← Complex.exp_add, hexp]
  have hI : (∫ t in Set.Ioi (0:ℝ),
        ((Chebyshev.theta (Real.exp t) * Real.exp (-t) - 1 : ℝ) : ℂ) *
          Complex.exp (-(z * (t : ℂ))))
      = ∫ t in Set.Ioi (0:ℝ),
          (((Chebyshev.theta (Real.exp t) : ℝ) : ℂ) * Complex.exp (-((z + 1) * (t : ℂ)))
            - Complex.exp (-(z * (t : ℂ)))) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsplit)
  rw [hI, MeasureTheory.integral_sub hUint hVint, hUval, hVval]

theorem erdos357_theta_div_id_tendsto_one (L : ℝ)
    (h : Filter.Tendsto
      (fun T : ℝ => ∫ t in (0:ℝ)..T, (Chebyshev.theta (Real.exp t) * Real.exp (-t) - 1))
      Filter.atTop (nhds L)) :
    Filter.Tendsto (fun x : ℝ => Chebyshev.theta x / x) Filter.atTop (nhds 1) :=
by
  
  have hmono : Monotone (fun t : ℝ => Chebyshev.theta (Real.exp t)) :=
    fun s t hst => Chebyshev.theta_mono (Real.exp_le_exp.mpr hst)
  have hII : ∀ a b : ℝ, IntervalIntegrable
      (fun t : ℝ => Chebyshev.theta (Real.exp t) * Real.exp (-t) - 1)
      MeasureTheory.volume a b := by
    intro a b
    have h1 : IntervalIntegrable (fun t : ℝ => Chebyshev.theta (Real.exp t))
        MeasureTheory.volume a b := hmono.intervalIntegrable
    have h2 : ContinuousOn (fun t : ℝ => Real.exp (-t)) (Set.uIcc a b) := by fun_prop
    exact (h1.mul_continuousOn h2).sub intervalIntegrable_const
  
  
  have hcf : ∀ C a b : ℝ, (∫ t in a..b, (C * Real.exp (-t) - 1))
      = (-C * Real.exp (-b) - b) - (-C * Real.exp (-a) - a) := by
    intro C a b
    have key : (∫ t in a..b, (C * Real.exp (-t) - 1))
        = (fun s : ℝ => -C * Real.exp (-s) - s) b
          - (fun s : ℝ => -C * Real.exp (-s) - s) a := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro t _
        have h0 : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) t := (hasDerivAt_id t).neg
        have h1 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (Real.exp (-t) * (-1)) t := h0.exp
        have h2 : HasDerivAt (fun s : ℝ => -C * Real.exp (-s))
            (-C * (Real.exp (-t) * (-1))) t := h1.const_mul (-C)
        have h3 : HasDerivAt (fun s : ℝ => -C * Real.exp (-s) - s)
            (-C * (Real.exp (-t) * (-1)) - 1) t := h2.sub (hasDerivAt_id t)
        have heq : (-C * (Real.exp (-t) * (-1)) - 1) = C * Real.exp (-t) - 1 := by ring
        rw [heq] at h3
        exact h3
      · exact Continuous.intervalIntegrable (by fun_prop) a b
    exact key
  
  have hA : ∀ a lam : ℝ, 0 < lam →
      lam * Real.exp a * Real.exp (-(a + Real.log lam)) = 1 := by
    intro a lam hlam0
    have hlne : lam ≠ 0 := ne_of_gt hlam0
    have hene : Real.exp a ≠ 0 := Real.exp_ne_zero a
    have hrw : -(a + Real.log lam) = (-a) + (-(Real.log lam)) := by ring
    rw [hrw, Real.exp_add]
    simp only [Real.exp_neg]
    rw [Real.exp_log hlam0]
    field_simp
  have hB : ∀ a lam : ℝ, lam * Real.exp a * Real.exp (-a) = lam := by
    intro a lam
    rw [Real.exp_neg, mul_assoc, mul_inv_cancel₀ (Real.exp_ne_zero a), mul_one]
  
  have hup : ∀ a lam : ℝ, 1 < lam → lam * Real.exp a ≤ Chebyshev.theta (Real.exp a) →
      lam - 1 - Real.log lam ≤ ∫ t in a..(a + Real.log lam),
        (Chebyshev.theta (Real.exp t) * Real.exp (-t) - 1) := by
    intro a lam hlam hge
    have hlam0 : (0:ℝ) < lam := lt_trans zero_lt_one hlam
    have hlog : 0 < Real.log lam := Real.log_pos hlam
    have hab : a ≤ a + Real.log lam := by linarith
    have hcmp : (∫ t in a..(a + Real.log lam), (lam * Real.exp a * Real.exp (-t) - 1))
        ≤ ∫ t in a..(a + Real.log lam),
            (Chebyshev.theta (Real.exp t) * Real.exp (-t) - 1) := by
      refine intervalIntegral.integral_mono_on hab
        (Continuous.intervalIntegrable (by fun_prop) _ _) (hII _ _) ?_
      intro t ht
      have hat : a ≤ t := ht.1
      have hexp : Real.exp a ≤ Real.exp t := Real.exp_le_exp.mpr hat
      have hth : Chebyshev.theta (Real.exp a) ≤ Chebyshev.theta (Real.exp t) :=
        Chebyshev.theta_mono hexp
      have hkey : lam * Real.exp a ≤ Chebyshev.theta (Real.exp t) := le_trans hge hth
      have hpos : (0:ℝ) < Real.exp (-t) := Real.exp_pos _
      have hmul := mul_le_mul_of_nonneg_right hkey (le_of_lt hpos)
      linarith
    have heval : (∫ t in a..(a + Real.log lam), (lam * Real.exp a * Real.exp (-t) - 1))
        = lam - 1 - Real.log lam := by
      rw [hcf]
      linear_combination -(hA a lam hlam0) + hB a lam
    linarith
  
  have hdown : ∀ a lam : ℝ, 0 < lam → lam < 1 →
      Chebyshev.theta (Real.exp a) ≤ lam * Real.exp a →
      (∫ t in (a + Real.log lam)..a,
          (Chebyshev.theta (Real.exp t) * Real.exp (-t) - 1))
        ≤ 1 - lam + Real.log lam := by
    intro a lam hlam0 hlam1 hle
    have hlog : Real.log lam < 0 := Real.log_neg hlam0 hlam1
    have hab : a + Real.log lam ≤ a := by linarith
    have hcmp : (∫ t in (a + Real.log lam)..a,
          (Chebyshev.theta (Real.exp t) * Real.exp (-t) - 1))
        ≤ ∫ t in (a + Real.log lam)..a, (lam * Real.exp a * Real.exp (-t) - 1) := by
      refine intervalIntegral.integral_mono_on hab (hII _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _) ?_
      intro t ht
      have hta : t ≤ a := ht.2
      have hexp : Real.exp t ≤ Real.exp a := Real.exp_le_exp.mpr hta
      have hth : Chebyshev.theta (Real.exp t) ≤ Chebyshev.theta (Real.exp a) :=
        Chebyshev.theta_mono hexp
      have hkey : Chebyshev.theta (Real.exp t) ≤ lam * Real.exp a := le_trans hth hle
      have hpos : (0:ℝ) < Real.exp (-t) := Real.exp_pos _
      have hmul := mul_le_mul_of_nonneg_right hkey (le_of_lt hpos)
      linarith
    have heval : (∫ t in (a + Real.log lam)..a, (lam * Real.exp a * Real.exp (-t) - 1))
        = 1 - lam + Real.log lam := by
      rw [hcf]
      linear_combination (hA a lam hlam0) - hB a lam
    linarith
  
  have hsplit : ∀ u v : ℝ,
      (∫ t in u..v, (Chebyshev.theta (Real.exp t) * Real.exp (-t) - 1))
      = (∫ t in (0:ℝ)..v, (Chebyshev.theta (Real.exp t) * Real.exp (-t) - 1))
        - (∫ t in (0:ℝ)..u, (Chebyshev.theta (Real.exp t) * Real.exp (-t) - 1)) := by
    intro u v
    have hadd := intervalIntegral.integral_add_adjacent_intervals (hII 0 u) (hII u v)
    linarith
  
  rw [Metric.tendsto_atTop]
  intro e0 he0
  set ε : ℝ := min e0 (1/2) with hεdef
  have hε : 0 < ε := lt_min he0 (by norm_num)
  have hεle : ε ≤ e0 := min_le_left _ _
  have hεhalf : ε ≤ 1/2 := min_le_right _ _
  have hp1 : (0:ℝ) < 1 + ε := by linarith
  have hm1 : (0:ℝ) < 1 - ε := by linarith
  have hlogp : Real.log (1 + ε) < ε := by
    have := Real.log_lt_sub_one_of_pos hp1 (by linarith : (1:ℝ) < 1 + ε).ne'
    linarith
  have hlogm : Real.log (1 - ε) < -ε := by
    have := Real.log_lt_sub_one_of_pos hm1 (by linarith : (1:ℝ) - ε < 1).ne
    linarith
  set c : ℝ := min (ε - Real.log (1 + ε)) (-(ε + Real.log (1 - ε))) with hcdef
  have hc1 : c ≤ ε - Real.log (1 + ε) := min_le_left _ _
  have hc2 : c ≤ -(ε + Real.log (1 - ε)) := min_le_right _ _
  have hc0 : 0 < c := lt_min (by linarith) (by linarith)
  obtain ⟨T₀, hT₀⟩ := Metric.tendsto_atTop.mp h (c / 2) (by linarith)
  have hT₀' : ∀ T : ℝ, T₀ ≤ T →
      |(∫ t in (0:ℝ)..T, (Chebyshev.theta (Real.exp t) * Real.exp (-t) - 1)) - L| < c / 2 := by
    intro T hT
    have hd := hT₀ T hT
    rwa [Real.dist_eq] at hd
  have hF : ∀ u v : ℝ, T₀ ≤ u → T₀ ≤ v →
      |∫ t in u..v, (Chebyshev.theta (Real.exp t) * Real.exp (-t) - 1)| < c := by
    intro u v hu hv
    have h1 := hT₀' u hu
    have h2 := hT₀' v hv
    rw [abs_lt] at h1 h2
    rw [hsplit u v, abs_lt]
    constructor <;> linarith
  
  have hlogm0 : Real.log (1 - ε) < 0 := Real.log_neg hm1 (by linarith)
  refine ⟨Real.exp (T₀ - Real.log (1 - ε)), fun x hx => ?_⟩
  have hNpos : (0:ℝ) < Real.exp (T₀ - Real.log (1 - ε)) := Real.exp_pos _
  have hxpos : (0:ℝ) < x := lt_of_lt_of_le hNpos hx
  have haA : T₀ - Real.log (1 - ε) ≤ Real.log x := by
    have h' := Real.log_le_log hNpos hx
    rwa [Real.log_exp] at h'
  have hexpa : Real.exp (Real.log x) = x := Real.exp_log hxpos
  have haT : T₀ ≤ Real.log x := by linarith
  
  have hi : Chebyshev.theta x < (1 + ε) * x := by
    by_contra hcon
    push_neg at hcon
    have hge : (1 + ε) * Real.exp (Real.log x) ≤ Chebyshev.theta (Real.exp (Real.log x)) := by
      rw [hexpa]; exact hcon
    have h2 := hup (Real.log x) (1 + ε) (by linarith) hge
    have hlogpos : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
    have h3 := hF (Real.log x) (Real.log x + Real.log (1 + ε)) haT (by linarith)
    rw [abs_lt] at h3
    linarith [h3.2]
  
  have hii : (1 - ε) * x < Chebyshev.theta x := by
    by_contra hcon
    push_neg at hcon
    have hle : Chebyshev.theta (Real.exp (Real.log x)) ≤ (1 - ε) * Real.exp (Real.log x) := by
      rw [hexpa]; exact hcon
    have h2 := hdown (Real.log x) (1 - ε) hm1 (by linarith) hle
    have h3 := hF (Real.log x + Real.log (1 - ε)) (Real.log x) (by linarith) haT
    rw [abs_lt] at h3
    linarith [h3.1]
  
  rw [Real.dist_eq, abs_lt]
  constructor
  · have hlow : (1 - ε) < Chebyshev.theta x / x := by
      rw [lt_div_iff₀ hxpos]; linarith
    linarith
  · have hhigh : Chebyshev.theta x / x < (1 + ε) := by
      rw [div_lt_iff₀ hxpos]; linarith
    linarith

theorem erdos357_exists_prime_in_short_interval (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, Nat.Prime p ∧ (1 - ε) * x ≤ (p : ℝ) ∧ (p : ℝ) ≤ x :=
by
  
  have hPNT : Filter.Tendsto (fun x : ℝ => Chebyshev.theta x / x) Filter.atTop (nhds 1) := by
    
    have hθmeas : Measurable Chebyshev.theta := Chebyshev.theta_mono.measurable
    have hFmeas : Measurable
        (fun t : ℝ => Chebyshev.theta (Real.exp t) * Real.exp (-t) - 1) :=
      ((hθmeas.comp Real.measurable_exp).mul
        (Real.measurable_exp.comp measurable_neg)).sub measurable_const
    have hmeas : MeasureTheory.AEStronglyMeasurable
        (fun t : ℝ => ((Chebyshev.theta (Real.exp t) * Real.exp (-t) - 1 : ℝ) : ℂ))
        MeasureTheory.volume :=
      (Complex.continuous_ofReal.measurable.comp hFmeas).aestronglyMeasurable
    
    have hbdd : ∀ t : ℝ, 0 ≤ t →
        ‖((Chebyshev.theta (Real.exp t) * Real.exp (-t) - 1 : ℝ) : ℂ)‖ ≤ 3 := by
      intro t _
      have hexp : (0:ℝ) < Real.exp t := Real.exp_pos t
      have hexpn : (0:ℝ) < Real.exp (-t) := Real.exp_pos (-t)
      have hmul : Real.exp t * Real.exp (-t) = 1 := by
        rw [← Real.exp_add]; simp
      have h1 : 0 ≤ Chebyshev.theta (Real.exp t) := Chebyshev.theta_nonneg _
      have h2 : Chebyshev.theta (Real.exp t) ≤ Real.log 4 * Real.exp t :=
        Chebyshev.theta_le_log4_mul_x (le_of_lt hexp)
      have h3 : Real.log 4 ≤ 3 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num)
        linarith
      have hupper : Chebyshev.theta (Real.exp t) * Real.exp (-t) ≤ 3 := by
        have hstep := mul_le_mul_of_nonneg_right h2 (le_of_lt hexpn)
        calc Chebyshev.theta (Real.exp t) * Real.exp (-t)
            ≤ Real.log 4 * Real.exp t * Real.exp (-t) := hstep
          _ = Real.log 4 * (Real.exp t * Real.exp (-t)) := by ring
          _ = Real.log 4 := by rw [hmul]; ring
          _ ≤ 3 := h3
      have hlower : 0 ≤ Chebyshev.theta (Real.exp t) * Real.exp (-t) :=
        mul_nonneg h1 (le_of_lt hexpn)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    
    obtain ⟨H, U1, hU1open, hU1sub, hHdiff, hHeq⟩ := erdos357_primeLogSeries_sub_pole_analytic
    set U : Set ℂ := {z : ℂ | z + 1 ∈ U1} \ {(-1 : ℂ)} with hUdef
    have hUopen : IsOpen U := by
      rw [hUdef]
      exact IsOpen.sdiff (hU1open.preimage (by fun_prop)) isClosed_singleton
    have hsub : {z : ℂ | 0 ≤ z.re} ⊆ U := by
      intro z hz
      have hz' : (0:ℝ) ≤ z.re := hz
      rw [hUdef]
      refine ⟨?_, ?_⟩
      · show z + 1 ∈ U1
        apply hU1sub
        show (1:ℝ) ≤ (z + 1).re
        simp only [Complex.add_re, Complex.one_re]
        linarith
      · intro hmem
        have hzz : z = -1 := hmem
        rw [hzz] at hz'
        simp at hz'
        linarith
    have hmaps : Set.MapsTo (fun z : ℂ => z + 1) U U1 := by
      intro z hz
      rw [hUdef] at hz
      exact hz.1
    have hcomp : DifferentiableOn ℂ (fun z : ℂ => H (z + 1)) U :=
      DifferentiableOn.comp hHdiff (by fun_prop) hmaps
    have hGdiff : DifferentiableOn ℂ (fun z : ℂ => (H (z + 1) - 1) / (z + 1)) U := by
      apply DifferentiableOn.div (hcomp.sub_const 1) (by fun_prop)
      intro z hz
      rw [hUdef] at hz
      simp only [Set.mem_diff, Set.mem_singleton_iff] at hz
      intro hcon
      exact hz.2 (by linear_combination hcon)
    
    have hrep : ∀ z : ℂ, 0 < z.re →
        (H (z + 1) - 1) / (z + 1)
          = ∫ t in Set.Ioi (0:ℝ),
              ((Chebyshev.theta (Real.exp t) * Real.exp (-t) - 1 : ℝ) : ℂ) *
                Complex.exp (-(z * (t : ℂ))) := by
      intro z hz
      rw [erdos357_theta_laplace_eq z hz]
      have hz0 : z ≠ 0 := by
        intro h; rw [h] at hz; simp at hz
      have hz1 : z + 1 ≠ 0 := by
        intro h
        have hre : z.re = -1 := by
          have := congrArg Complex.re h
          simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
          linarith
        rw [hre] at hz; linarith
      have hzre1 : 1 < (z + 1).re := by
        simp only [Complex.add_re, Complex.one_re]; linarith
      rw [hHeq (z + 1) hzre1, show z + 1 - 1 = z from by ring]
      field_simp
      ring
    
    have key := erdos357_newman_analytic_theorem
      (fun t : ℝ => ((Chebyshev.theta (Real.exp t) * Real.exp (-t) - 1 : ℝ) : ℂ)) 3 hmeas hbdd
      (fun z : ℂ => (H (z + 1) - 1) / (z + 1)) U hUopen hsub hGdiff hrep
    have hEq : ∀ T : ℝ,
        (∫ t in (0:ℝ)..T, ((Chebyshev.theta (Real.exp t) * Real.exp (-t) - 1 : ℝ) : ℂ))
          = ((∫ t in (0:ℝ)..T, (Chebyshev.theta (Real.exp t) * Real.exp (-t) - 1) : ℝ) : ℂ) := by
      intro T
      exact intervalIntegral.integral_ofReal
    simp only [hEq] at key
    have key3 := (Complex.continuous_re.tendsto _).comp key
    simp only [Function.comp_def, Complex.ofReal_re] at key3
    exact erdos357_theta_div_id_tendsto_one _ key3
  
  set e : ℝ := min ε (1/2) with he
  have he0 : 0 < e := lt_min hε (by norm_num)
  have he2 : e ≤ 1/2 := min_le_right _ _
  have hee : e ≤ ε := min_le_left _ _
  set δ : ℝ := e / 4 with hd
  have hδ0 : 0 < δ := by positivity
  obtain ⟨X0, hX0⟩ := Metric.tendsto_atTop.mp hPNT δ hδ0
  set X1 : ℝ := max X0 1 with hX1
  have hX1a : X0 ≤ X1 := le_max_left _ _
  have hX1b : (1:ℝ) ≤ X1 := le_max_right _ _
  refine Filter.eventually_atTop.2 ⟨max (2 * X1) 2, fun x hx => ?_⟩
  have hx2 : (2:ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hxX : 2 * X1 ≤ x := le_trans (le_max_left _ _) hx
  have hxpos : (0:ℝ) < x := by linarith
  set y : ℝ := (1 - e) * x with hy
  have hylb : x / 2 ≤ y := by
    have h12 : (1:ℝ)/2 ≤ 1 - e := by linarith
    rw [hy]; nlinarith
  have hyX1 : X1 ≤ y := by linarith
  have hypos : (0:ℝ) < y := by linarith
  have hyx : y ≤ x := by rw [hy]; nlinarith
  have hbx : |Chebyshev.theta x / x - 1| < δ := by
    have := hX0 x (le_trans hX1a (by linarith))
    rwa [Real.dist_eq] at this
  have hby : |Chebyshev.theta y / y - 1| < δ := by
    have := hX0 y (le_trans hX1a hyX1)
    rwa [Real.dist_eq] at this
  have hbx' : (1 - δ) * x < Chebyshev.theta x := by
    have h1 : -δ < Chebyshev.theta x / x - 1 := (abs_lt.mp hbx).1
    have h2 : (1 - δ) * x < (Chebyshev.theta x / x) * x := by nlinarith
    rwa [div_mul_cancel₀ _ (ne_of_gt hxpos)] at h2
  have hby' : Chebyshev.theta y < (1 + δ) * y := by
    have h1 : Chebyshev.theta y / y - 1 < δ := (abs_lt.mp hby).2
    have h2 : (Chebyshev.theta y / y) * y < (1 + δ) * y := by nlinarith
    rwa [div_mul_cancel₀ _ (ne_of_gt hypos)] at h2
  have hkey : Chebyshev.theta y < Chebyshev.theta x := by
    have hmid : (1 + δ) * y < (1 - δ) * x := by
      rw [hy, hd]; nlinarith
    linarith
  by_contra hcon
  push_neg at hcon
  have hsets : (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime = (Finset.Icc 0 ⌊y⌋₊).filter Nat.Prime := by
    apply Finset.Subset.antisymm
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      obtain ⟨⟨_, hple⟩, hpp⟩ := hp
      refine ⟨⟨Nat.zero_le _, ?_⟩, hpp⟩
      by_contra hgt
      push_neg at hgt
      have h1 : y < (p : ℝ) := by
        have hc : (⌊y⌋₊ : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hgt
        have := Nat.lt_floor_add_one y
        linarith
      have h2 : (p : ℝ) ≤ x := by
        have hc : (p : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hple
        have := Nat.floor_le (le_of_lt hxpos)
        linarith
      have hlow : (1 - ε) * x ≤ (p : ℝ) := by
        have hle : (1 - ε) * x ≤ y := by rw [hy]; nlinarith
        linarith
      exact absurd h2 (not_le.mpr (hcon p hpp hlow))
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
      obtain ⟨⟨_, hple⟩, hpp⟩ := hp
      exact ⟨⟨Nat.zero_le _, le_trans hple (Nat.floor_le_floor hyx)⟩, hpp⟩
  rw [Chebyshev.theta_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc, hsets] at hkey
  exact lt_irrefl _ hkey

theorem erdos_357.variants.hegyvari : ∃ (o o' : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧ o' =o[atTop] (1 : ℕ → ℝ) ∧ ∀ᶠ n in atTop, (g n : ℝ) ∈ Set.Icc ((1 / 3 + o n) * n) ((2 / 3 + o' n) * n) :=
by
  
  
  
  have hUB : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (g n : ℝ) ≤ (2 / 3 + ε) * n := by
    intro ε hε
    set r : ℕ := ⌈2 / ε⌉₊ + 1 with hrdef
    have hr1 : 1 ≤ r := Nat.le_add_left 1 _
    have hRpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
    have hR2 : 2 / ε ≤ (r : ℝ) := by
      have h1 : 2 / ε ≤ ((⌈2 / ε⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have h2 : ((⌈2 / ε⌉₊ : ℕ) : ℝ) ≤ (r : ℝ) := by
        have : (⌈2 / ε⌉₊ : ℕ) ≤ r := by omega
        exact_mod_cast this
      linarith
    have hεr : (2 : ℝ) ≤ ε * (r : ℝ) := by
      rw [div_le_iff₀ hε] at hR2
      linarith
    refine Filter.eventually_atTop.2 ⟨r ^ 2, fun n hn => ?_⟩
    obtain ⟨a, ha, hd⟩ := (erdos357_g_spec n).2.2
    have hbound := erdos357_distinctSums_card_bound n (g n) r hr1 a ha hd
    have hcast : (3 * (r : ℝ) + 1) * (g n : ℝ)
        ≤ 2 * ((r : ℝ) + 1) * (n : ℝ) + 4 * (r : ℝ) ^ 2 := by exact_mod_cast hbound
    have hNR : ((r : ℝ)) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hn
    have hN : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h1 : (14 / 3 : ℝ) ≤ 3 * ε * (r : ℝ) + ε - 4 / 3 := by nlinarith
    have h2 : (14 / 3 : ℝ) * (n : ℝ) ≤ (3 * ε * (r : ℝ) + ε - 4 / 3) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right h1 hN
    have h3 : 4 * (r : ℝ) ^ 2 ≤ (14 / 3 : ℝ) * (n : ℝ) := by nlinarith
    have hfinal : 2 * ((r : ℝ) + 1) * (n : ℝ) + 4 * (r : ℝ) ^ 2
        ≤ (3 * (r : ℝ) + 1) * ((2 / 3 + ε) * (n : ℝ)) := by nlinarith [h2, h3]
    have hkey : (3 * (r : ℝ) + 1) * (g n : ℝ) ≤ (3 * (r : ℝ) + 1) * ((2 / 3 + ε) * (n : ℝ)) :=
      le_trans hcast hfinal
    exact le_of_mul_le_mul_left hkey (by linarith)
  
  
  
  have hLBsmall : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 6 →
      ∀ᶠ n : ℕ in atTop, (1 / 3 - ε) * n ≤ (g n : ℝ) := by
    intro ε hε hε6
    obtain ⟨X, hX⟩ := Filter.eventually_atTop.1
      (erdos357_exists_prime_in_short_interval (3 * ε / 2) (by linarith))
    refine Filter.eventually_atTop.2 ⟨max (max 10 ⌈2 / ε⌉₊) ⌈3 * X⌉₊, fun n hn => ?_⟩
    have hn10 : 10 ≤ n := le_trans (le_trans (le_max_left 10 _) (le_max_left _ _)) hn
    have hnceil : ⌈2 / ε⌉₊ ≤ n := le_trans (le_trans (le_max_right 10 _) (le_max_left _ _)) hn
    have hnX : ⌈3 * X⌉₊ ≤ n := le_trans (le_max_right _ _) hn
    have hN10 : (10 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn10
    have h2ε : 2 / ε ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hnceil)
    have h3X : 3 * X ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hnX)
    have hxge : X ≤ ((n : ℝ) + 2) / 3 := by linarith
    obtain ⟨p, hp, hp1, hp2⟩ := hX (((n : ℝ) + 2) / 3) hxge
    have h3pR : (3 : ℝ) * (p : ℝ) ≤ (n : ℝ) + 2 := by linarith
    have h3p : 3 * p ≤ n + 2 := by exact_mod_cast h3pR
    have hc1 : (3 : ℝ) / 4 ≤ 1 - 3 * ε / 2 := by linarith
    have hc2 : (4 : ℝ) ≤ ((n : ℝ) + 2) / 3 := by linarith
    have hc3 : (3 : ℝ) ≤ (1 - 3 * ε / 2) * (((n : ℝ) + 2) / 3) := by nlinarith
    have hp3R : (3 : ℝ) ≤ (p : ℝ) := le_trans hc3 hp1
    have hp3 : 3 ≤ p := by exact_mod_cast hp3R
    obtain ⟨a, ha, hd⟩ := erdos357_erdosTuran_witness p hp hp3
    have hsub : Set.Icc 1 (3 * p - 2) ⊆ Set.Icc 1 n :=
      Set.Icc_subset_Icc le_rfl (by omega)
    have hgn : p - 1 ≤ g n := (erdos357_g_spec n).2.1 (p - 1) a (ha.trans hsub) hd
    have hgnR : (p : ℝ) - 1 ≤ (g n : ℝ) := by
      have hcc : ((p - 1 : ℕ) : ℝ) ≤ (g n : ℝ) := by exact_mod_cast hgn
      have hp1' : 1 ≤ p := by omega
      rwa [Nat.cast_sub hp1', Nat.cast_one] at hcc
    have hεn : (2 : ℝ) ≤ ε * (n : ℝ) := by
      rw [div_le_iff₀ hε] at h2ε
      linarith
    nlinarith [hp1, hgnR, hεn]
  
  have hLB : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (1 / 3 - ε) * n ≤ (g n : ℝ) := by
    intro ε hε
    have h := hLBsmall (min ε (1 / 6)) (lt_min hε (by norm_num)) (min_le_right _ _)
    filter_upwards [h] with n hn
    have hmin : min ε (1 / 6) ≤ ε := min_le_left _ _
    have hcast : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [hn, hmin, hcast]
  
  refine ⟨fun n => min 0 ((g n : ℝ) / (n : ℝ) - 1 / 3),
          fun n => max 0 ((g n : ℝ) / (n : ℝ) - 2 / 3), ?_, ?_, ?_⟩
  · rw [show (1 : ℕ → ℝ) = fun _ : ℕ => (1 : ℝ) from rfl,
        Asymptotics.isLittleO_one_iff ℝ, NormedAddCommGroup.tendsto_nhds_zero]
    intro ε hε
    filter_upwards [hLB (ε / 2) (by linarith), Filter.eventually_ge_atTop (1 : ℕ)] with n h1 h2
    have hn0 : 0 < n := h2
    have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
    have hq : 1 / 3 - ε / 2 ≤ (g n : ℝ) / (n : ℝ) := by
      rw [le_div_iff₀ hN]; linarith
    simp only [Real.norm_eq_abs, abs_lt]
    exact ⟨lt_min (by linarith) (by linarith), lt_of_le_of_lt (min_le_left _ _) hε⟩
  · rw [show (1 : ℕ → ℝ) = fun _ : ℕ => (1 : ℝ) from rfl,
        Asymptotics.isLittleO_one_iff ℝ, NormedAddCommGroup.tendsto_nhds_zero]
    intro ε hε
    filter_upwards [hUB (ε / 2) (by linarith), Filter.eventually_ge_atTop (1 : ℕ)] with n h1 h2
    have hn0 : 0 < n := h2
    have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
    have hq : (g n : ℝ) / (n : ℝ) ≤ 2 / 3 + ε / 2 := by
      rw [div_le_iff₀ hN]; linarith
    simp only [Real.norm_eq_abs, abs_lt]
    exact ⟨lt_of_lt_of_le (by linarith) (le_max_left _ _), max_lt (by linarith) (by linarith)⟩
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n h2
    have hn0 : 0 < n := h2
    have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
    have hdiv : ((g n : ℝ) / (n : ℝ)) * (n : ℝ) = (g n : ℝ) :=
      div_mul_cancel₀ _ (ne_of_gt hN)
    rw [Set.mem_Icc]
    constructor
    · have hle : 1 / 3 + min 0 ((g n : ℝ) / (n : ℝ) - 1 / 3) ≤ (g n : ℝ) / (n : ℝ) := by
        have := min_le_right (0 : ℝ) ((g n : ℝ) / (n : ℝ) - 1 / 3)
        linarith
      calc (1 / 3 + min 0 ((g n : ℝ) / (n : ℝ) - 1 / 3)) * (n : ℝ)
          ≤ ((g n : ℝ) / (n : ℝ)) * (n : ℝ) := mul_le_mul_of_nonneg_right hle (le_of_lt hN)
        _ = (g n : ℝ) := hdiv
    · have hle : (g n : ℝ) / (n : ℝ) ≤ 2 / 3 + max 0 ((g n : ℝ) / (n : ℝ) - 2 / 3) := by
        have := le_max_right (0 : ℝ) ((g n : ℝ) / (n : ℝ) - 2 / 3)
        linarith
      calc (g n : ℝ) = ((g n : ℝ) / (n : ℝ)) * (n : ℝ) := hdiv.symm
        _ ≤ (2 / 3 + max 0 ((g n : ℝ) / (n : ℝ) - 2 / 3)) * (n : ℝ) :=
            mul_le_mul_of_nonneg_right hle (le_of_lt hN)
