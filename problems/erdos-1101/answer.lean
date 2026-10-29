import Mathlib
set_option maxHeartbeats 4000000

open Nat Filter
namespace Erdos1101
/-- The set of integers not divisible by any u_i. -/
def ASet (u : ℕ → ℕ) : Set ℕ :=
  { a | ∀ i, ¬ u i ∣ a }
/-- The sequence of integers A_u which are not divisible by any u_i
arranged in a monotonic sequence. -/
noncomputable def A (u : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.nth (fun a => a ∈ ASet u) n
/-- t_x such that u_0 ... u_{t_x-1} ≤ x < u_0 ... u_{t_x}.
-/
noncomputable def t (u : ℕ → ℕ) (x : ℕ) : ℕ :=
  sSup { k | ∏ i ∈ Finset.range k, u i ≤ x }
/-- A sequence is "good" if
1. it is strictly monotone
2. it is pairwise coprime
3. the sum of reciprocals converges
4. the gap between consecutive elements in A(u) is bounded relative to t_x. -/
def IsGood (u : ℕ → ℕ) : Prop :=
  StrictMono u ∧
  (∀ i j, i ≠ j → Coprime (u i) (u j)) ∧
  Summable (fun n => 1 / (u n : ℝ)) ∧
  ∀ ε > 0, ∀ᶠ x in atTop,
    ∀ k, A u k < x →
      (A u (k + 1) : ℝ) - A u k < (1 + ε) * (t u x : ℝ) * (∏' i : ℕ, (1 - 1 / (u i : ℝ)))⁻¹
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
def witnessF (n : ℕ) : ℕ := 2 ^ Nat.sqrt n * (n + 2) ^ 2


noncomputable def witnessU (n : ℕ) : ℕ := Nat.nth Nat.Prime (witnessF n)
def HasCert (u : ℕ → ℕ) (N M K Q : ℕ) : Prop :=
  ∃ n : ℕ, n < N ∧ ∃ S : Finset ℕ, ∃ j : ℕ → ℕ,
    S.card = M ∧ (∀ i ∈ S, K < i) ∧ (∀ i ∈ S, 1 ≤ j i ∧ j i ≤ Q) ∧
    (∀ i ∈ S, u i ∣ n + j i)


def IsPools (P : ℕ → Finset ℕ) : Prop :=
  (∀ n, (P n).Nonempty) ∧ (∀ n, ∀ p ∈ P n, Nat.Prime p) ∧
  (∀ n, ∀ p ∈ P n, ∀ q ∈ P (n + 1), p < q)


def PoolsLog (P : ℕ → Finset ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    ∀ p ∈ P n, |Real.log p - Real.sqrt n| ≤ δ * Real.sqrt n


def PoolsBig (P : ℕ → Finset ℕ) : Prop :=
  ∀ β : ℝ, β < 1 → ∀ᶠ n : ℕ in atTop, ∀ p ∈ P n, (p : ℝ) ^ β ≤ ((P n).card : ℝ)

theorem nth_prime_linearithmic : ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 2 ≤ k → (Nat.nth Nat.Prime k : ℝ) ≤ C * k * Real.log k :=
by
  
  
  
  
  have hA : ∀ n : ℕ, 0 < n →
      Nat.centralBinom n ≤ (2 * n) ^ (Nat.centralBinom n).primeFactors.card := by
    intro n hn
    have hBne : Nat.centralBinom n ≠ 0 := Nat.centralBinom_ne_zero n
    have hprod := Nat.factorization_prod_pow_eq_self hBne
    rw [Finsupp.prod, Nat.support_factorization] at hprod
    have hle : ∀ p ∈ (Nat.centralBinom n).primeFactors,
        p ^ ((Nat.centralBinom n).factorization p) ≤ 2 * n := by
      intro p _
      have h := Nat.pow_factorization_choose_le (p := p) (n := 2 * n) (k := n) (by omega)
      simpa [Nat.centralBinom] using h
    calc Nat.centralBinom n
        = ∏ p ∈ (Nat.centralBinom n).primeFactors,
            p ^ ((Nat.centralBinom n).factorization p) := hprod.symm
      _ ≤ (2 * n) ^ (Nat.centralBinom n).primeFactors.card :=
          Finset.prod_le_pow_card _ _ _ hle
  
  have hB : ∀ n : ℕ, 0 < n →
      (Nat.centralBinom n).primeFactors.card ≤ Nat.count Nat.Prime (2 * n + 1) := by
    intro n hn
    rw [Nat.count_eq_card_filter_range]
    apply Finset.card_le_card
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hd : p ∣ Nat.centralBinom n := Nat.dvd_of_mem_primeFactors hp
    have he : 0 < (Nat.centralBinom n).factorization p :=
      hpp.factorization_pos_of_dvd (Nat.centralBinom_ne_zero n) hd
    have h1 : p ^ 1 ≤ p ^ ((Nat.centralBinom n).factorization p) :=
      Nat.pow_le_pow_right hpp.pos he
    have h2 : p ^ ((Nat.centralBinom n).factorization p) ≤ 2 * n := by
      have h := Nat.pow_factorization_choose_le (p := p) (n := 2 * n) (k := n) (by omega)
      simpa [Nat.centralBinom] using h
    rw [pow_one] at h1
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hpp⟩
  
  have hstar : ∀ n : ℕ, 0 < n →
      (4:ℕ) ^ n ≤ (2 * n) ^ (Nat.count Nat.Prime (2 * n + 1) + 1) := by
    intro n hn
    have hNpos : 0 < 2 * n := by omega
    have hi := Nat.four_pow_le_two_mul_self_mul_centralBinom n hn
    have hii := hA n hn
    have hiii := hB n hn
    have hpow : (2 * n) ^ (Nat.centralBinom n).primeFactors.card
        ≤ (2 * n) ^ (Nat.count Nat.Prime (2 * n + 1)) := Nat.pow_le_pow_right hNpos hiii
    calc (4:ℕ) ^ n ≤ 2 * n * Nat.centralBinom n := hi
      _ ≤ 2 * n * ((2 * n) ^ (Nat.count Nat.Prime (2 * n + 1))) :=
          Nat.mul_le_mul_left _ (le_trans hii hpow)
      _ = (2 * n) ^ (Nat.count Nat.Prime (2 * n + 1) + 1) := by ring
  
  have hinv : ∀ n k : ℕ, 0 < n → (2 * n) ^ (k + 1) < 4 ^ n → Nat.nth Nat.Prime k ≤ 2 * n := by
    intro n k hn hlt
    have hcount : k < Nat.count Nat.Prime (2 * n + 1) := by
      by_contra hcon
      push_neg at hcon
      have h1 : (2 * n) ^ (Nat.count Nat.Prime (2 * n + 1) + 1) ≤ (2 * n) ^ (k + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have h2 := hstar n hn
      exact absurd (lt_of_le_of_lt (le_trans h2 h1) hlt) (lt_irrefl _)
    have h3 := Nat.nth_lt_of_lt_count hcount
    omega
  
  
  
  have hklone : ∀ k : ℕ, 2 ≤ k → (1:ℝ) ≤ (k:ℝ) * Real.log k := by
    intro k hk
    have hK2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    have hlogle : Real.log 2 ≤ Real.log k := Real.log_le_log (by norm_num) hK2
    have hl2 : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (k:ℝ) - 2)
      (by linarith : (0:ℝ) ≤ Real.log k)]
  
  
  
  have hmain : ∀ k : ℕ, 20 ≤ k → (Nat.nth Nat.Prime k : ℝ) ≤ 8 * (k:ℝ) * Real.log k := by
    intro k hk
    have hK20 : (20:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    have hKpos : (0:ℝ) < (k:ℝ) := by linarith
    
    have hL2 : (2:ℝ) < Real.log k := by
      have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      have he : Real.exp 2 < 20 := by nlinarith [Real.exp_pos 1]
      exact (Real.lt_log_iff_exp_lt hKpos).2 (by linarith)
    have hLpos : (0:ℝ) < Real.log k := by linarith
    
    have hKL40 : (40:ℝ) < (k:ℝ) * Real.log k := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (k:ℝ) - 20)
        (by linarith : (0:ℝ) ≤ Real.log k - 2)]
    have hKL1 : (1:ℝ) ≤ (k:ℝ) * Real.log k := by linarith
    have hKLpos : (0:ℝ) < (k:ℝ) * Real.log k := by linarith
    have h3KLnn : (0:ℝ) ≤ 3 * (k:ℝ) * Real.log k := by nlinarith
    
    obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ,
        3 * (k:ℝ) * Real.log k ≤ (n:ℝ) ∧ (n:ℝ) < 3 * (k:ℝ) * Real.log k + 1 :=
      ⟨⌈3 * (k:ℝ) * Real.log k⌉₊, Nat.le_ceil _, Nat.ceil_lt_add_one h3KLnn⟩
    have hmlow : (120:ℝ) < (n:ℝ) := by nlinarith
    have hnposR : (0:ℝ) < (n:ℝ) := by linarith
    have hnpos : 0 < n := by exact_mod_cast hnposR
    have hmnn : (0:ℝ) ≤ (n:ℝ) := le_of_lt hnposR
    have h2m : 2 * (n:ℝ) ≤ 8 * ((k:ℝ) * Real.log k) := by linarith
    have h2mpos : (0:ℝ) < 2 * (n:ℝ) := by linarith
    have h2mge1 : (1:ℝ) ≤ 2 * (n:ℝ) := by linarith
    have hlog2m_nn : (0:ℝ) ≤ Real.log (2 * (n:ℝ)) := Real.log_nonneg h2mge1
    
    have hlog8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2 ^ (3:ℕ) by norm_num, Real.log_pow]; norm_num
    have hKne : ((k:ℝ)) ≠ 0 := ne_of_gt hKpos
    have hLne : Real.log k ≠ 0 := ne_of_gt hLpos
    have h8Kne : ((8:ℝ) * (k:ℝ)) ≠ 0 := ne_of_gt (by linarith : (0:ℝ) < 8 * (k:ℝ))
    have hlogprod : Real.log (8 * (k:ℝ) * Real.log k)
        = 3 * Real.log 2 + Real.log k + Real.log (Real.log k) := by
      rw [Real.log_mul h8Kne hLne, Real.log_mul (by norm_num : (8:ℝ) ≠ 0) hKne, hlog8]
    have hlogle : Real.log (2 * (n:ℝ)) ≤ Real.log (8 * (k:ℝ) * Real.log k) := by
      apply Real.log_le_log h2mpos
      linarith
    rw [hlogprod] at hlogle
    
    have hlogL : Real.log (Real.log k) ≤ Real.log k - 1 := Real.log_le_sub_one_of_pos hLpos
    have hlog2lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hlog2m_ub : Real.log (2 * (n:ℝ)) ≤ (26/10 : ℝ) * Real.log k := by linarith
    
    have hK1 : (k:ℝ) + 1 ≤ (105/100 : ℝ) * (k:ℝ) := by linarith
    
    have hlhs : ((k:ℝ) + 1) * Real.log (2 * (n:ℝ))
        ≤ ((105/100 : ℝ) * (k:ℝ)) * ((26/10 : ℝ) * Real.log k) :=
      mul_le_mul hK1 hlog2m_ub hlog2m_nn (by linarith)
    
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.log_pow]; norm_num
    have hlog2gt : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hlog4ge : (1386/1000 : ℝ) ≤ Real.log 4 := by rw [hlog4]; linarith
    have hrhs : (3 * (k:ℝ) * Real.log k) * (1386/1000 : ℝ) ≤ (n:ℝ) * Real.log 4 :=
      mul_le_mul hn1 hlog4ge (by norm_num) hmnn
    
    have e1 : ((105/100 : ℝ) * (k:ℝ)) * ((26/10 : ℝ) * Real.log k)
        = (273/100 : ℝ) * ((k:ℝ) * Real.log k) := by ring
    have e2 : (3 * (k:ℝ) * Real.log k) * (1386/1000 : ℝ)
        = (2079/500 : ℝ) * ((k:ℝ) * Real.log k) := by ring
    rw [e1] at hlhs
    rw [e2] at hrhs
    have hkey : ((k:ℝ) + 1) * Real.log (2 * (n:ℝ)) < (n:ℝ) * Real.log 4 := by
      linarith
    
    have hnpow : ((2:ℝ) * (n:ℝ)) ^ (k + 1) < (4:ℝ) ^ n := by
      have hl1 : Real.log (((2:ℝ) * (n:ℝ)) ^ (k + 1))
          = ((k:ℝ) + 1) * Real.log (2 * (n:ℝ)) := by
        rw [Real.log_pow]; push_cast; ring
      have hl2 : Real.log ((4:ℝ) ^ n) = (n:ℝ) * Real.log 4 := by
        rw [Real.log_pow]
      have hp1 : (0:ℝ) < ((2:ℝ) * (n:ℝ)) ^ (k + 1) := pow_pos h2mpos (k + 1)
      have hp2 : (0:ℝ) < (4:ℝ) ^ n := pow_pos (by norm_num) n
      refine (Real.log_lt_log_iff hp1 hp2).1 ?_
      rw [hl1, hl2]
      exact hkey
    have hnatpow : (2 * n) ^ (k + 1) < 4 ^ n := by
      have hc : (((2 * n) ^ (k + 1) : ℕ) : ℝ) < ((4 ^ n : ℕ) : ℝ) := by
        push_cast
        exact hnpow
      exact_mod_cast hc
    have hple : Nat.nth Nat.Prime k ≤ 2 * n := hinv n k hnpos hnatpow
    have hpleR : (Nat.nth Nat.Prime k : ℝ) ≤ 2 * (n:ℝ) := by
      have hc : ((Nat.nth Nat.Prime k : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) := Nat.cast_le.2 hple
      push_cast at hc
      exact hc
    linarith
  
  
  
  refine ⟨8 + (Nat.nth Nat.Prime 20 : ℝ), by positivity, ?_⟩
  intro k hk
  have hP20 : (0:ℝ) ≤ (Nat.nth Nat.Prime 20 : ℝ) := Nat.cast_nonneg _
  have hKL1 : (1:ℝ) ≤ (k:ℝ) * Real.log k := hklone k hk
  have hKLnn : (0:ℝ) ≤ (k:ℝ) * Real.log k := by linarith
  by_cases h20 : 20 ≤ k
  · have h := hmain k h20
    nlinarith [h, mul_nonneg hP20 hKLnn]
  · push_neg at h20
    have hle20 : Nat.nth Nat.Prime k ≤ Nat.nth Nat.Prime 20 :=
      (Nat.nth_le_nth Nat.infinite_setOf_prime).2 (by omega)
    have hleR : (Nat.nth Nat.Prime k : ℝ) ≤ (Nat.nth Nat.Prime 20 : ℝ) := by exact_mod_cast hle20
    nlinarith [hleR, hKL1,
      mul_nonneg hP20 (by linarith : (0:ℝ) ≤ (k:ℝ) * Real.log k - 1)]

theorem good_seq_pools_exist (C : ℝ) (hC : 0 < C)
    (hp : ∀ k : ℕ, 2 ≤ k → (Nat.nth Nat.Prime k : ℝ) ≤ C * k * Real.log k) :
    ∃ P : ℕ → Finset ℕ, IsPools P ∧ PoolsLog P ∧ PoolsBig P :=
by
  classical
  
  
  
  have key1 : ∀ x : ℝ, 0 ≤ x →
      Real.exp (Real.sqrt x) / (2 * (Real.sqrt x + 1))
        ≤ Real.exp (Real.sqrt (x + 1)) - Real.exp (Real.sqrt x) := by
    intro x hx
    have ha0 : (0:ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg _
    have hb0 : (0:ℝ) ≤ Real.sqrt (x + 1) := Real.sqrt_nonneg _
    have ha2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
    have hb2 : Real.sqrt (x + 1) ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
    have hab : Real.sqrt x < Real.sqrt (x + 1) := by nlinarith
    have hba : Real.sqrt (x + 1) ≤ Real.sqrt x + 1 := by nlinarith
    have hkey : (Real.sqrt (x + 1) - Real.sqrt x) * (Real.sqrt (x + 1) + Real.sqrt x) = 1 := by
      nlinarith
    have hden : (0:ℝ) < 2 * (Real.sqrt x + 1) := by linarith
    have hgap : 1 / (2 * (Real.sqrt x + 1)) ≤ Real.sqrt (x + 1) - Real.sqrt x := by
      rw [div_le_iff₀ hden]
      nlinarith [hkey, mul_le_mul_of_nonneg_left
        (show Real.sqrt (x+1) + Real.sqrt x ≤ 2 * (Real.sqrt x + 1) by linarith)
        (show (0:ℝ) ≤ Real.sqrt (x+1) - Real.sqrt x by linarith)]
    have hea : (0:ℝ) < Real.exp (Real.sqrt x) := Real.exp_pos _
    have hexp : Real.exp (Real.sqrt (x + 1))
        = Real.exp (Real.sqrt x) * Real.exp (Real.sqrt (x + 1) - Real.sqrt x) := by
      rw [← Real.exp_add]; ring_nf
    have h1 : (Real.sqrt (x + 1) - Real.sqrt x) + 1
        ≤ Real.exp (Real.sqrt (x + 1) - Real.sqrt x) := Real.add_one_le_exp _
    have hmul : Real.exp (Real.sqrt x) * (1 / (2 * (Real.sqrt x + 1)))
        ≤ Real.exp (Real.sqrt x) * (Real.sqrt (x + 1) - Real.sqrt x) :=
      mul_le_mul_of_nonneg_left hgap hea.le
    have hfin : Real.exp (Real.sqrt x) * (Real.sqrt (x + 1) - Real.sqrt x)
        ≤ Real.exp (Real.sqrt (x + 1)) - Real.exp (Real.sqrt x) := by
      rw [hexp]; nlinarith [h1, hea]
    have hdiv : Real.exp (Real.sqrt x) / (2 * (Real.sqrt x + 1))
        = Real.exp (Real.sqrt x) * (1 / (2 * (Real.sqrt x + 1))) := by ring
    linarith [hdiv ▸ hmul]
  
  
  
  have key2 : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) + 2 ≤ Real.exp (Real.sqrt (n : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop 258] with n hn
    have hnR : (258:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hn0 : (0:ℝ) ≤ (n:ℝ) := by linarith
    have ha0 : (0:ℝ) ≤ Real.sqrt (n:ℝ) := Real.sqrt_nonneg _
    have ha2 : Real.sqrt (n:ℝ) ^ 2 = (n:ℝ) := Real.sq_sqrt hn0
    have haa : Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) = (n:ℝ) := by nlinarith [ha2]
    have hq : (0:ℝ) ≤ Real.sqrt (n:ℝ) / 4 := by linarith
    have h1 : Real.sqrt (n:ℝ) / 4 + 1 ≤ Real.exp (Real.sqrt (n:ℝ) / 4) := Real.add_one_le_exp _
    have h2 : Real.sqrt (n:ℝ) / 4 ≤ Real.exp (Real.sqrt (n:ℝ) / 4) := by linarith
    have he : (0:ℝ) ≤ Real.exp (Real.sqrt (n:ℝ) / 4) := (Real.exp_pos _).le
    have hm1 : (Real.sqrt (n:ℝ) / 4) * (Real.sqrt (n:ℝ) / 4)
        ≤ Real.exp (Real.sqrt (n:ℝ) / 4) * Real.exp (Real.sqrt (n:ℝ) / 4) :=
      mul_le_mul h2 h2 hq he
    have hm2 : ((Real.sqrt (n:ℝ) / 4) * (Real.sqrt (n:ℝ) / 4))
          * ((Real.sqrt (n:ℝ) / 4) * (Real.sqrt (n:ℝ) / 4))
        ≤ (Real.exp (Real.sqrt (n:ℝ) / 4) * Real.exp (Real.sqrt (n:ℝ) / 4))
          * (Real.exp (Real.sqrt (n:ℝ) / 4) * Real.exp (Real.sqrt (n:ℝ) / 4)) :=
      mul_le_mul hm1 hm1 (by positivity) (by positivity)
    have hexp4 : (Real.exp (Real.sqrt (n:ℝ) / 4) * Real.exp (Real.sqrt (n:ℝ) / 4))
          * (Real.exp (Real.sqrt (n:ℝ) / 4) * Real.exp (Real.sqrt (n:ℝ) / 4))
        = Real.exp (Real.sqrt (n:ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have h4 : ((Real.sqrt (n:ℝ) / 4) * (Real.sqrt (n:ℝ) / 4))
          * ((Real.sqrt (n:ℝ) / 4) * (Real.sqrt (n:ℝ) / 4)) = (n:ℝ)^2 / 256 := by
      have hr : ((Real.sqrt (n:ℝ) / 4) * (Real.sqrt (n:ℝ) / 4))
            * ((Real.sqrt (n:ℝ) / 4) * (Real.sqrt (n:ℝ) / 4))
          = ((Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ)) * (Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ))) / 256 := by
        ring
      rw [hr, haa]
      ring
    rw [hexp4, h4] at hm2
    nlinarith [hm2, hnR, sq_nonneg ((n:ℝ) - 258)]
  
  
  
  have key3 : ∀ A c : ℝ, 0 ≤ A → 0 < c → ∀ᶠ n : ℕ in Filter.atTop,
      A + Real.log (Real.sqrt (n : ℝ) + 2) ≤ c * Real.sqrt (n : ℝ) := by
    intro A c hA hc
    have hz₀1 : (1:ℝ) ≤ max 1 ((A + 6)/c) := le_max_left _ _
    have hz₀c : A + 6 ≤ c * max 1 ((A + 6)/c) := by
      have h := le_max_right (1:ℝ) ((A+6)/c)
      have hh : c * ((A+6)/c) ≤ c * max 1 ((A + 6)/c) := mul_le_mul_of_nonneg_left h hc.le
      have he : c * ((A+6)/c) = A + 6 := by field_simp
      linarith [he ▸ hh]
    filter_upwards [Filter.eventually_ge_atTop ⌈(max 1 ((A + 6)/c))^4⌉₊] with n hn
    have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg _
    have hnR : (max 1 ((A + 6)/c))^4 ≤ (n:ℝ) := by
      have h1 : (max 1 ((A + 6)/c))^4 ≤ ((⌈(max 1 ((A + 6)/c))^4⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have h2 : ((⌈(max 1 ((A + 6)/c))^4⌉₊ : ℕ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      linarith
    have hy0 : (0:ℝ) ≤ Real.sqrt (n:ℝ) := Real.sqrt_nonneg _
    have hy2 : Real.sqrt (n:ℝ) ^ 2 = (n:ℝ) := Real.sq_sqrt hn0
    have hz0 : (0:ℝ) ≤ Real.sqrt (Real.sqrt (n:ℝ)) := Real.sqrt_nonneg _
    have hz2 : Real.sqrt (Real.sqrt (n:ℝ)) ^ 2 = Real.sqrt (n:ℝ) := Real.sq_sqrt hy0
    have hz4 : Real.sqrt (Real.sqrt (n:ℝ)) ^ 4 = (n:ℝ) := by
      have hr : Real.sqrt (Real.sqrt (n:ℝ)) ^ 4 = (Real.sqrt (Real.sqrt (n:ℝ)) ^ 2) ^ 2 := by ring
      rw [hr, hz2, hy2]
    have hzz : max 1 ((A + 6)/c) ≤ Real.sqrt (Real.sqrt (n:ℝ)) := by
      by_contra hcon
      push_neg at hcon
      have hzsq : Real.sqrt (Real.sqrt (n:ℝ)) ^ 2 < (max 1 ((A + 6)/c)) ^ 2 := by
        nlinarith [hz0, hcon, hz₀1]
      have hz2nn : (0:ℝ) ≤ Real.sqrt (Real.sqrt (n:ℝ)) ^ 2 := sq_nonneg _
      have hlt : Real.sqrt (Real.sqrt (n:ℝ)) ^ 4 < (max 1 ((A + 6)/c))^4 := by
        have e1 : Real.sqrt (Real.sqrt (n:ℝ)) ^ 4
            = (Real.sqrt (Real.sqrt (n:ℝ)) ^ 2) ^ 2 := by ring
        have e2 : (max 1 ((A + 6)/c))^4 = ((max 1 ((A + 6)/c)) ^ 2) ^ 2 := by ring
        rw [e1, e2]
        nlinarith [hzsq, hz2nn]
      rw [hz4] at hlt
      linarith
    have hz1 : (1:ℝ) ≤ Real.sqrt (Real.sqrt (n:ℝ)) := le_trans hz₀1 hzz
    have hlog : Real.log (Real.sqrt (n:ℝ) + 2) ≤ 2 * Real.sqrt (Real.sqrt (n:ℝ)) + 4 := by
      have hpos : (0:ℝ) < Real.sqrt (n:ℝ) + 2 := by linarith
      have hsq : Real.sqrt (Real.sqrt (n:ℝ) + 2) ≤ Real.sqrt (Real.sqrt (n:ℝ)) + 2 := by
        have h1 : Real.sqrt (n:ℝ) + 2 ≤ (Real.sqrt (Real.sqrt (n:ℝ)) + 2)^2 := by
          nlinarith [hz2, hz0]
        have h2 := Real.sqrt_le_sqrt h1
        rwa [Real.sqrt_sq (by linarith)] at h2
      have hl : Real.log (Real.sqrt (n:ℝ) + 2)
          = 2 * Real.log (Real.sqrt (Real.sqrt (n:ℝ) + 2)) := by
        rw [Real.log_sqrt hpos.le]; ring
      have hsp : (0:ℝ) < Real.sqrt (Real.sqrt (n:ℝ) + 2) := Real.sqrt_pos.2 hpos
      have h3 : Real.log (Real.sqrt (Real.sqrt (n:ℝ) + 2))
          ≤ Real.sqrt (Real.sqrt (n:ℝ) + 2) - 1 := Real.log_le_sub_one_of_pos hsp
      linarith
    have hcz : A + 6 ≤ c * Real.sqrt (Real.sqrt (n:ℝ)) :=
      le_trans hz₀c (mul_le_mul_of_nonneg_left hzz hc.le)
    have hcore : (A + 6) * Real.sqrt (Real.sqrt (n:ℝ))
        ≤ (c * Real.sqrt (Real.sqrt (n:ℝ))) * Real.sqrt (Real.sqrt (n:ℝ)) :=
      mul_le_mul_of_nonneg_right hcz hz0
    have heq : (c * Real.sqrt (Real.sqrt (n:ℝ))) * Real.sqrt (Real.sqrt (n:ℝ))
        = c * Real.sqrt (n:ℝ) := by
      have hr : (c * Real.sqrt (Real.sqrt (n:ℝ))) * Real.sqrt (Real.sqrt (n:ℝ))
          = c * (Real.sqrt (Real.sqrt (n:ℝ)) ^ 2) := by ring
      rw [hr, hz2]
    rw [heq] at hcore
    nlinarith [hcore, hlog, hA, hz1,
      mul_nonneg (show (0:ℝ) ≤ A + 4 by linarith)
        (show (0:ℝ) ≤ Real.sqrt (Real.sqrt (n:ℝ)) - 1 by linarith)]
  
  
  
  have key4 : ∀ s : ℝ, 0 ≤ s → ∀ k : ℕ, 2 ≤ k → (k : ℝ) ≤ 2 * Real.exp (s + 1) →
      Real.log (Nat.nth Nat.Prime k : ℝ) ≤ s + (Real.log C + 2 + Real.log (s + 2)) := by
    intro s _hs k hk hks
    have hkR : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    have hk0 : (0:ℝ) < (k:ℝ) := by linarith
    have hlogk : Real.log 2 ≤ Real.log (k:ℝ) := Real.log_le_log (by norm_num) hkR
    have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlogkpos : (0:ℝ) < Real.log (k:ℝ) := lt_of_lt_of_le hlog2pos hlogk
    have h2p : 2 ≤ Nat.nth Nat.Prime k := (Nat.prime_nth_prime k).two_le
    have hppos : (0:ℝ) < (Nat.nth Nat.Prime k : ℝ) := by
      have h : 0 < Nat.nth Nat.Prime k := lt_of_lt_of_le (by norm_num) h2p
      exact_mod_cast h
    have hrhs : Real.log (Nat.nth Nat.Prime k : ℝ) ≤ Real.log (C * (k:ℝ) * Real.log (k:ℝ)) :=
      Real.log_le_log hppos (hp k hk)
    have hsplit : Real.log (C * (k:ℝ) * Real.log (k:ℝ))
        = Real.log C + Real.log (k:ℝ) + Real.log (Real.log (k:ℝ)) := by
      rw [Real.log_mul (mul_ne_zero (ne_of_gt hC) (ne_of_gt hk0)) (ne_of_gt hlogkpos),
        Real.log_mul (ne_of_gt hC) (ne_of_gt hk0)]
    have hklog : Real.log (k:ℝ) ≤ Real.log 2 + (s + 1) := by
      have h1 : Real.log (k:ℝ) ≤ Real.log (2 * Real.exp (s+1)) := Real.log_le_log hk0 hks
      rwa [Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at h1
    have hlog2lt : Real.log 2 < 1 := by
      have h := Real.log_two_lt_d9
      linarith
    have hkle : Real.log (k:ℝ) ≤ s + 2 := by linarith
    have hloglog : Real.log (Real.log (k:ℝ)) ≤ Real.log (s + 2) :=
      Real.log_le_log hlogkpos hkle
    linarith [hrhs, hsplit.le, hsplit.ge, hklog, hloglog]
  
  
  
  have hsm : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOf_prime
  have hinj : Function.Injective (Nat.nth Nat.Prime) := hsm.injective
  obtain ⟨M, hM⟩ : ∃ M : ℕ → ℕ, ∀ n : ℕ, M n = ⌈Real.exp (Real.sqrt (n : ℝ))⌉₊ + n :=
    ⟨fun n => ⌈Real.exp (Real.sqrt (n : ℝ))⌉₊ + n, fun _ => rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℕ → Finset ℕ,
      ∀ n : ℕ, P n = (Finset.Ico (M n) (M (n + 1))).image (Nat.nth Nat.Prime) :=
    ⟨fun n => (Finset.Ico (M n) (M (n + 1))).image (Nat.nth Nat.Prime), fun _ => rfl⟩
  have hcast : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
    intro n; push_cast; ring
  have hMsucc : ∀ n : ℕ, M (n + 1) = ⌈Real.exp (Real.sqrt ((n : ℝ) + 1))⌉₊ + (n + 1) := by
    intro n; rw [hM (n + 1), hcast n]
  
  have hMmono : ∀ n : ℕ, M n < M (n + 1) := by
    intro n
    rw [hM n, hMsucc n]
    have h1 : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.exp (Real.sqrt (n : ℝ)) ≤ Real.exp (Real.sqrt ((n : ℝ) + 1)) :=
      Real.exp_le_exp.2 h1
    have h3 : ⌈Real.exp (Real.sqrt (n : ℝ))⌉₊ ≤ ⌈Real.exp (Real.sqrt ((n : ℝ) + 1))⌉₊ :=
      Nat.ceil_le_ceil h2
    omega
  have hMge : ∀ n : ℕ, n + 1 ≤ M n := by
    intro n
    rw [hM n]
    have h : 1 ≤ ⌈Real.exp (Real.sqrt (n : ℝ))⌉₊ := Nat.one_le_ceil_iff.2 (Real.exp_pos _)
    omega
  
  have hmem_of : ∀ n q : ℕ, q ∈ P n →
      ∃ k : ℕ, M n ≤ k ∧ k < M (n + 1) ∧ Nat.nth Nat.Prime k = q := by
    intro n q hq
    rw [hP n, Finset.mem_image] at hq
    obtain ⟨k, hk, hk2⟩ := hq
    rw [Finset.mem_Ico] at hk
    exact ⟨k, hk.1, hk.2, hk2⟩
  have hne : ∀ n : ℕ, (P n).Nonempty := by
    intro n
    rw [hP n]
    exact (Finset.nonempty_Ico.2 (hMmono n)).image _
  have hpr : ∀ n : ℕ, ∀ q ∈ P n, Nat.Prime q := by
    intro n q hq
    obtain ⟨k, _, _, rfl⟩ := hmem_of n q hq
    exact Nat.prime_nth_prime k
  have hord : ∀ n : ℕ, ∀ q ∈ P n, ∀ r ∈ P (n + 1), q < r := by
    intro n q hq r hr
    obtain ⟨k, _, hk2, rfl⟩ := hmem_of n q hq
    obtain ⟨l, hl1, _, rfl⟩ := hmem_of (n + 1) r hr
    exact hsm (lt_of_lt_of_le hk2 hl1)
  have hcard : ∀ n : ℕ, ((P n).card : ℝ) = (M (n + 1) : ℝ) - (M n : ℝ) := by
    intro n
    rw [hP n, Finset.card_image_of_injective _ hinj, Nat.card_Ico,
      Nat.cast_sub (hMmono n).le]
  have hcard1 : ∀ n : ℕ, (1:ℝ) ≤ ((P n).card : ℝ) := by
    intro n
    have h : 1 ≤ (P n).card := Finset.card_pos.2 (hne n)
    exact_mod_cast h
  
  have hidxub : ∀ n : ℕ, (n : ℝ) + 2 ≤ Real.exp (Real.sqrt (n : ℝ)) →
      ∀ k : ℕ, k < M (n + 1) → (k : ℝ) ≤ 2 * Real.exp (Real.sqrt (n : ℝ) + 1) := by
    intro n hn k hk
    rw [hMsucc n] at hk
    have hkR : (k : ℝ) ≤ (⌈Real.exp (Real.sqrt ((n : ℝ) + 1))⌉₊ : ℝ) + (n : ℝ) := by
      have h : k ≤ ⌈Real.exp (Real.sqrt ((n : ℝ) + 1))⌉₊ + n := by omega
      exact_mod_cast h
    have hceil : ((⌈Real.exp (Real.sqrt ((n : ℝ) + 1))⌉₊ : ℕ) : ℝ)
        < Real.exp (Real.sqrt ((n : ℝ) + 1)) + 1 := Nat.ceil_lt_add_one (Real.exp_pos _).le
    have hmono : Real.exp (Real.sqrt (n : ℝ)) ≤ Real.exp (Real.sqrt ((n : ℝ) + 1)) :=
      Real.exp_le_exp.2 (Real.sqrt_le_sqrt (by linarith))
    have hs0 : (0:ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    have hs2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
    have hsq : Real.sqrt ((n : ℝ) + 1) ≤ Real.sqrt (n : ℝ) + 1 := by
      have hle : (n : ℝ) + 1 ≤ (Real.sqrt (n : ℝ) + 1) ^ 2 := by nlinarith
      have h := Real.sqrt_le_sqrt hle
      rwa [Real.sqrt_sq (by linarith)] at h
    have hfin : Real.exp (Real.sqrt ((n : ℝ) + 1)) ≤ Real.exp (Real.sqrt (n : ℝ) + 1) :=
      Real.exp_le_exp.2 hsq
    linarith
  
  have hlogp : ∀ n : ℕ, 1 ≤ n → (n : ℝ) + 2 ≤ Real.exp (Real.sqrt (n : ℝ)) →
      ∀ q ∈ P n, Real.sqrt (n : ℝ) ≤ Real.log (q : ℝ) ∧
        Real.log (q : ℝ)
          ≤ Real.sqrt (n : ℝ) + (Real.log C + 2 + Real.log (Real.sqrt (n : ℝ) + 2)) := by
    intro n hn1 hn q hq
    obtain ⟨k, hk1, hk2, rfl⟩ := hmem_of n q hq
    have hs0 : (0:ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    have hk1' : ⌈Real.exp (Real.sqrt (n : ℝ))⌉₊ + n ≤ k := by rw [← hM n]; exact hk1
    have hk2n : 2 ≤ k := le_trans (by omega : 2 ≤ n + 1) (le_trans (hMge n) hk1)
    have hexple : Real.exp (Real.sqrt (n : ℝ)) ≤ (k : ℝ) := by
      have h1 : Real.exp (Real.sqrt (n : ℝ)) ≤ ((⌈Real.exp (Real.sqrt (n : ℝ))⌉₊ : ℕ) : ℝ) :=
        Nat.le_ceil _
      have h2 : ((⌈Real.exp (Real.sqrt (n : ℝ))⌉₊ : ℕ) : ℝ) ≤ (k : ℝ) := by
        have h3 : ⌈Real.exp (Real.sqrt (n : ℝ))⌉₊ ≤ k := by omega
        exact_mod_cast h3
      linarith
    have hkp0 : k ≤ Nat.nth Nat.Prime k := hsm.le_apply
    have hkp : (k : ℝ) ≤ (Nat.nth Nat.Prime k : ℝ) := by exact_mod_cast hkp0
    have hlow : Real.sqrt (n : ℝ) ≤ Real.log (Nat.nth Nat.Prime k : ℝ) := by
      have h1 : Real.exp (Real.sqrt (n : ℝ)) ≤ (Nat.nth Nat.Prime k : ℝ) := le_trans hexple hkp
      have h2 := Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp] at h2
    exact ⟨hlow, key4 (Real.sqrt (n : ℝ)) hs0 k hk2n (hidxub n hn k hk2)⟩
  
  have hpoolsize : ∀ n : ℕ,
      Real.exp (Real.sqrt (n : ℝ)) / (2 * (Real.sqrt (n : ℝ) + 1)) ≤ ((P n).card : ℝ) := by
    intro n
    rw [hcard n, hM n, hMsucc n]
    push_cast
    have h1 : Real.exp (Real.sqrt ((n : ℝ) + 1))
        ≤ ((⌈Real.exp (Real.sqrt ((n : ℝ) + 1))⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Real.exp (Real.sqrt (n : ℝ))⌉₊ : ℕ) : ℝ)
        < Real.exp (Real.sqrt (n : ℝ)) + 1 := Nat.ceil_lt_add_one (Real.exp_pos _).le
    have h3 := key1 (n : ℝ) (Nat.cast_nonneg n)
    linarith
  
  have hPoolsLog : PoolsLog P := by
    intro δ hδ
    have hA0 : (0:ℝ) ≤ |Real.log C + 2| := abs_nonneg _
    filter_upwards [Filter.eventually_ge_atTop 1, key2,
      key3 (|Real.log C + 2|) δ hA0 hδ] with n hn1 hn2 hn3
    intro q hq
    obtain ⟨hlow, hup⟩ := hlogp n hn1 hn2 q hq
    have hs0 : (0:ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    have habs : Real.log C + 2 ≤ |Real.log C + 2| := le_abs_self _
    have hδs : (0:ℝ) ≤ δ * Real.sqrt (n : ℝ) := mul_nonneg hδ.le hs0
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  
  have hPoolsBig : PoolsBig P := by
    intro β hβ
    by_cases hβ0 : β ≤ 0
    · refine Filter.Eventually.of_forall ?_
      intro n q hq
      have hpp := hpr n q hq
      have hq1 : (1:ℝ) ≤ (q : ℝ) := by exact_mod_cast hpp.one_lt.le
      have h1 : (q : ℝ) ^ β ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq1 hβ0
      linarith [hcard1 n]
    · push_neg at hβ0
      have hA0 : (0:ℝ) ≤ |Real.log C + 2| := abs_nonneg _
      have hc3 : (0:ℝ) < (1 - β) / 3 := by linarith
      filter_upwards [Filter.eventually_ge_atTop 1, key2,
        key3 (|Real.log C + 2|) ((1 - β) / 3) hA0 hc3]
        with n hn1 hn2 hn3
      intro q hq
      have hs0 : (0:ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
      have hQ1 : (1:ℝ) ≤ ((P n).card : ℝ) := hcard1 n
      have hQ0 : (0:ℝ) < ((P n).card : ℝ) := by linarith
      have hden : (0:ℝ) < 2 * (Real.sqrt (n : ℝ) + 1) := by linarith
      have hEpos : (0:ℝ) < Real.exp (Real.sqrt (n : ℝ)) / (2 * (Real.sqrt (n : ℝ) + 1)) :=
        div_pos (Real.exp_pos _) hden
      have hloga : Real.sqrt (n : ℝ) - Real.log (2 * (Real.sqrt (n : ℝ) + 1))
          ≤ Real.log ((P n).card : ℝ) := by
        have h := Real.log_le_log hEpos (hpoolsize n)
        rwa [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hden), Real.log_exp] at h
      have hlogs2 : (0:ℝ) ≤ Real.log (Real.sqrt (n : ℝ) + 2) := Real.log_nonneg (by linarith)
      have hb : Real.log (2 * (Real.sqrt (n : ℝ) + 1))
          ≤ 2 * Real.log (Real.sqrt (n : ℝ) + 2) := by
        have h2 : 2 * (Real.sqrt (n : ℝ) + 1) ≤ (Real.sqrt (n : ℝ) + 2) ^ 2 := by nlinarith
        have h3 := Real.log_le_log hden h2
        rw [Real.log_pow] at h3
        push_cast at h3
        linarith
      have hN : |Real.log C + 2| + Real.log (Real.sqrt (n : ℝ) + 2)
          + Real.log (2 * (Real.sqrt (n : ℝ) + 1)) ≤ (1 - β) * Real.sqrt (n : ℝ) := by
        linarith
      obtain ⟨hlow, hup⟩ := hlogp n hn1 hn2 q hq
      have habs : Real.log C + 2 ≤ |Real.log C + 2| := le_abs_self _
      have hXle : Real.log (q : ℝ)
          ≤ Real.sqrt (n : ℝ) + (|Real.log C + 2| + Real.log (Real.sqrt (n : ℝ) + 2)) := by
        linarith
      have hXnn : (0:ℝ) ≤ |Real.log C + 2| + Real.log (Real.sqrt (n : ℝ) + 2) := by linarith
      have hd1 : β * Real.log (q : ℝ)
          ≤ β * (Real.sqrt (n : ℝ)
              + (|Real.log C + 2| + Real.log (Real.sqrt (n : ℝ) + 2))) :=
        mul_le_mul_of_nonneg_left hXle hβ0.le
      have hd2 : β * (|Real.log C + 2| + Real.log (Real.sqrt (n : ℝ) + 2))
          ≤ |Real.log C + 2| + Real.log (Real.sqrt (n : ℝ) + 2) := by
        nlinarith [mul_nonneg (show (0:ℝ) ≤ 1 - β by linarith) hXnn]
      have hd : β * Real.log (q : ℝ) ≤ Real.log ((P n).card : ℝ) := by
        nlinarith [hd1, hd2, hN, hloga]
      have hqpos : (0:ℝ) < (q : ℝ) := by
        have h := (hpr n q hq).pos
        exact_mod_cast h
      rw [Real.rpow_def_of_pos hqpos, mul_comm]
      calc Real.exp (β * Real.log (q : ℝ))
          ≤ Real.exp (Real.log ((P n).card : ℝ)) := Real.exp_le_exp.2 hd
        _ = ((P n).card : ℝ) := Real.exp_log hQ0
  exact ⟨P, ⟨hne, hpr, hord⟩, hPoolsLog, hPoolsBig⟩

theorem prime_divisor_count_bound (N m : ℕ) (hN : 1 ≤ N) (hm : 2 ≤ m) :
    ((N.primeFactors.filter (fun p => m ≤ p)).card : ℝ) ≤ Real.log N / Real.log m :=
by
  
  set S := N.primeFactors.filter (fun p => m ≤ p) with hSdef
  
  have hsub : S ⊆ N.primeFactors := Finset.filter_subset _ _
  have hmem : ∀ p ∈ S, m ≤ p := fun p hp => (Finset.mem_filter.mp hp).2
  
  have h1 : m ^ S.card ≤ ∏ p ∈ S, p := Finset.pow_card_le_prod S (fun p => p) m hmem
  
  have h2 : (∏ p ∈ S, p) ∣ N :=
    dvd_trans (Finset.prod_dvd_prod_of_subset S N.primeFactors (fun p => p) hsub)
      (Nat.prod_primeFactors_dvd N)
  have h3 : (∏ p ∈ S, p) ≤ N := Nat.le_of_dvd (by omega) h2
  
  have hpow : m ^ S.card ≤ N := le_trans h1 h3
  
  
  have hmR : (1:ℝ) < (m:ℝ) := by
    have h : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    linarith
  have hlogm : 0 < Real.log (m:ℝ) := Real.log_pos hmR
  have hcast : ((m:ℝ)) ^ (S.card) ≤ (N:ℝ) := by
    have h := (Nat.cast_le (α := ℝ)).mpr hpow
    push_cast at h
    exact h
  have hpos : (0:ℝ) < (m:ℝ) ^ (S.card) := pow_pos (by linarith) _
  have hlog := Real.log_le_log hpos hcast
  rw [Real.log_pow] at hlog
  rw [le_div_iff₀ hlogm]
  exact hlog

theorem esym_geom_bound (b δ : ℝ) (hb : 0 < b) (hδ : 0 < δ) :
    ∀ᶠ M : ℕ in atTop, ∀ I : Finset ℕ,
      ∑ S ∈ I.powersetCard M, ∏ i ∈ S, Real.exp (-(b * Real.sqrt i))
        ≤ Real.exp (-(1 - δ) * (2 * b / 3) * (M : ℝ) ^ ((3:ℝ)/2)) :=
by
  classical
  
  have hrp : ∀ y : ℝ, 0 ≤ y → y ^ ((3:ℝ)/2) = (Real.sqrt y) ^ 3 := by
    intro y hy
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (y ^ ((1:ℝ)/2)) 3, ← Real.rpow_mul hy]
    norm_num
  have hrp3 : ∀ y : ℝ, 0 ≤ y → y ^ ((3:ℝ)/2) = Real.sqrt y * y := by
    intro y hy
    have h1 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
    calc y ^ ((3:ℝ)/2) = Real.sqrt y ^ 3 := hrp y hy
      _ = Real.sqrt y * (Real.sqrt y ^ 2) := by ring
      _ = Real.sqrt y * y := by rw [h1]
  
  have hstepR : ∀ x : ℝ, 0 ≤ x →
      (2/3:ℝ) * (x+1) ^ ((3:ℝ)/2) ≤ (2/3:ℝ) * x ^ ((3:ℝ)/2) + Real.sqrt (x+1) := by
    intro x hx
    have hx1 : (0:ℝ) ≤ x + 1 := by linarith
    have ha0 : (0:ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg _
    have hd0 : (0:ℝ) ≤ Real.sqrt (x+1) := Real.sqrt_nonneg _
    have ha2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
    have hd2 : Real.sqrt (x+1) ^ 2 = x + 1 := Real.sq_sqrt hx1
    have had : Real.sqrt x ≤ Real.sqrt (x+1) := Real.sqrt_le_sqrt (by linarith)
    have hd1 : (1:ℝ) ≤ Real.sqrt (x+1) := by nlinarith [hd2, hd0, hx]
    have hpos : (0:ℝ) < Real.sqrt (x+1) + Real.sqrt x := by linarith
    have hdiff : Real.sqrt (x+1)^2 - Real.sqrt x^2 = 1 := by rw [hd2, ha2]; ring
    have hmul : (2*(Real.sqrt (x+1)^3 - Real.sqrt x^3)) * (Real.sqrt (x+1) + Real.sqrt x)
        ≤ (3*Real.sqrt (x+1)) * (Real.sqrt (x+1) + Real.sqrt x) := by
      have he : (2*(Real.sqrt (x+1)^3 - Real.sqrt x^3)) * (Real.sqrt (x+1) + Real.sqrt x)
          = 2 * ((Real.sqrt (x+1)^2 - Real.sqrt x^2)
              * (Real.sqrt (x+1)^2 + Real.sqrt (x+1)*Real.sqrt x + Real.sqrt x^2)) := by ring
      rw [he, hdiff, one_mul]
      nlinarith [mul_nonneg ha0 (sub_nonneg.2 had), ha2, hd2]
    have hkey : 2*(Real.sqrt (x+1)^3 - Real.sqrt x^3) ≤ 3*Real.sqrt (x+1) :=
      le_of_mul_le_mul_right hmul hpos
    rw [hrp (x+1) hx1, hrp x hx]
    linarith
  
  have s6 : ∀ m : ℕ, (2/3:ℝ) * (m:ℝ) ^ ((3:ℝ)/2)
      ≤ (∑ i ∈ Finset.range m, Real.sqrt i) + Real.sqrt m := by
    intro m
    induction m with
    | zero =>
      have h0 : ((0:ℕ):ℝ) ^ ((3:ℝ)/2) = 0 := by
        rw [Nat.cast_zero, Real.zero_rpow (by norm_num)]
      rw [h0]
      simp
    | succ n ih =>
      have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      have h := hstepR (n:ℝ) hn0
      rw [Finset.sum_range_succ]
      push_cast
      push_cast at h
      linarith
  
  have s5 : ∀ A B : ℝ, 0 ≤ A → 0 < B →
      ∀ᶠ M : ℕ in atTop, A + Real.sqrt M ≤ B * (M:ℝ) ^ ((3:ℝ)/2) := by
    intro A B hA hB
    filter_upwards [eventually_ge_atTop (max 1 (Nat.ceil ((A+1)/B)))] with M hM
    have hM1 : 1 ≤ M := le_trans (le_max_left _ _) hM
    have hMc : Nat.ceil ((A+1)/B) ≤ M := le_trans (le_max_right _ _) hM
    have hM1R : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM1
    have hM0 : (0:ℝ) ≤ (M:ℝ) := by linarith
    have hs1 : (1:ℝ) ≤ Real.sqrt M := by
      have h := Real.sqrt_le_sqrt hM1R
      simpa using h
    have hMcR : ((Nat.ceil ((A+1)/B) : ℕ) : ℝ) ≤ (M:ℝ) := by exact_mod_cast hMc
    have hdiv : (A+1)/B ≤ (M:ℝ) := le_trans (Nat.le_ceil _) hMcR
    have hAB : A + 1 ≤ (M:ℝ) * B := (div_le_iff₀ hB).1 hdiv
    have hid : (M:ℝ) ^ ((3:ℝ)/2) = Real.sqrt M * (M:ℝ) := hrp3 _ hM0
    rw [hid]
    calc A + Real.sqrt M ≤ (A+1) * Real.sqrt M := by
          nlinarith [mul_nonneg hA (by linarith : (0:ℝ) ≤ Real.sqrt M - 1)]
      _ ≤ ((M:ℝ)*B) * Real.sqrt M := mul_le_mul_of_nonneg_right hAB (Real.sqrt_nonneg _)
      _ = B * (Real.sqrt M * (M:ℝ)) := by ring
  
  have s4 : ∀ (y : ℕ → ℝ), (∀ i, 0 ≤ y i) → ∀ (I : Finset ℕ) (M : ℕ),
      ∑ S ∈ I.powersetCard M, ∏ i ∈ S, y i ≤ Real.exp (∑ i ∈ I, y i) := by
    intro y hy I M
    have h1 : ∑ S ∈ I.powersetCard M, ∏ i ∈ S, y i ≤ ∑ S ∈ I.powerset, ∏ i ∈ S, y i := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_
        (fun S _ _ => Finset.prod_nonneg (fun i _ => hy i))
      rw [Finset.powersetCard_eq_filter]
      exact Finset.filter_subset _ _
    have h2 : ∑ S ∈ I.powerset, ∏ i ∈ S, y i = ∏ i ∈ I, (y i + 1) := by
      rw [Finset.prod_add]
      simp
    have h3 : ∏ i ∈ I, (y i + 1) ≤ ∏ i ∈ I, Real.exp (y i) := by
      refine Finset.prod_le_prod (fun i _ => by linarith [hy i]) (fun i _ => ?_)
      linarith [Real.add_one_le_exp (y i)]
    calc ∑ S ∈ I.powersetCard M, ∏ i ∈ S, y i
        ≤ ∑ S ∈ I.powerset, ∏ i ∈ S, y i := h1
      _ = ∏ i ∈ I, (y i + 1) := h2
      _ ≤ ∏ i ∈ I, Real.exp (y i) := h3
      _ = Real.exp (∑ i ∈ I, y i) := (Real.exp_sum _ _).symm
  
  have s3 : ∀ (n : ℕ) (S : Finset ℕ), S.card = n →
      ∑ i ∈ Finset.range n, Real.sqrt i ≤ ∑ i ∈ S, Real.sqrt i := by
    intro n
    induction n with
    | zero =>
      intro S _
      simp only [Finset.range_zero, Finset.sum_empty]
      exact Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
    | succ n ih =>
      intro S hS
      have hne : S.Nonempty := Finset.card_pos.1 (by omega)
      have hmS : S.max' hne ∈ S := S.max'_mem hne
      have hsub : S ⊆ Finset.range (S.max' hne + 1) := by
        intro x hx
        exact Finset.mem_range_succ_iff.2 (S.le_max' x hx)
      have hcard : n + 1 ≤ S.max' hne + 1 := by
        have h1 : S.card ≤ (Finset.range (S.max' hne + 1)).card := Finset.card_le_card hsub
        rw [Finset.card_range, hS] at h1
        exact h1
      have hnm : (n:ℝ) ≤ ((S.max' hne : ℕ):ℝ) := by
        have h2 : n ≤ S.max' hne := by omega
        exact_mod_cast h2
      have hsq : Real.sqrt n ≤ Real.sqrt (S.max' hne) := Real.sqrt_le_sqrt hnm
      have hT : (S.erase (S.max' hne)).card = n := by
        have h3 := Finset.card_erase_of_mem hmS
        omega
      have hIH := ih (S.erase (S.max' hne)) hT
      have hsplit : ∑ i ∈ S.erase (S.max' hne), Real.sqrt i + Real.sqrt (S.max' hne)
          = ∑ i ∈ S, Real.sqrt i := Finset.sum_erase_add S _ hmS
      rw [Finset.sum_range_succ]
      linarith [hIH, hsq, hsplit]
  
  have s2 : ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 ≤ C ∧
      ∀ I : Finset ℕ, ∑ i ∈ I, Real.exp (-(c * Real.sqrt i)) ≤ C := by
    intro c hc
    have hcne : c ≠ 0 := ne_of_gt hc
    have hpt : ∀ i : ℕ, 1 ≤ i →
        Real.exp (-(c * Real.sqrt i)) ≤ (256/c^4) * (1/((i:ℝ)^2)) := by
      intro i hi
      have hi0 : (1:ℝ) ≤ (i:ℝ) := by exact_mod_cast hi
      have hipos : (0:ℝ) < (i:ℝ) := by linarith
      have hine : ((i:ℕ):ℝ) ≠ 0 := ne_of_gt hipos
      have hs0 : (0:ℝ) ≤ Real.sqrt i := Real.sqrt_nonneg _
      have hs2 : Real.sqrt i ^ 2 = (i:ℝ) := Real.sq_sqrt (le_of_lt hipos)
      have hz0 : (0:ℝ) ≤ c * Real.sqrt i / 4 := by positivity
      have hez : c * Real.sqrt i / 4 ≤ Real.exp (c * Real.sqrt i / 4) := by
        linarith [Real.add_one_le_exp (c * Real.sqrt i / 4)]
      have hez4 : (c * Real.sqrt i / 4)^4 ≤ (Real.exp (c * Real.sqrt i / 4))^4 := by
        gcongr
      have hexp4 : (Real.exp (c * Real.sqrt i / 4))^4 = Real.exp (c * Real.sqrt i) := by
        have h1 : Real.exp (c * Real.sqrt i / 4 + c * Real.sqrt i / 4)
            = Real.exp (c * Real.sqrt i / 4) * Real.exp (c * Real.sqrt i / 4) :=
          Real.exp_add _ _
        have h2 : Real.exp ((c * Real.sqrt i / 4 + c * Real.sqrt i / 4)
              + (c * Real.sqrt i / 4 + c * Real.sqrt i / 4))
            = Real.exp (c * Real.sqrt i / 4 + c * Real.sqrt i / 4)
              * Real.exp (c * Real.sqrt i / 4 + c * Real.sqrt i / 4) := Real.exp_add _ _
        have h3 : (c * Real.sqrt i / 4 + c * Real.sqrt i / 4)
              + (c * Real.sqrt i / 4 + c * Real.sqrt i / 4) = c * Real.sqrt i := by ring
        rw [h3, h1] at h2
        rw [h2]; ring
      have hs4 : (Real.sqrt i)^4 = (i:ℝ)^2 := by
        have h : (Real.sqrt i)^4 = ((Real.sqrt i)^2)^2 := by ring
        rw [h, hs2]
      have hlow : (c^4 * (i:ℝ)^2)/256 ≤ Real.exp (c * Real.sqrt i) := by
        rw [← hexp4]
        refine le_trans (le_of_eq ?_) hez4
        rw [← hs4]; ring
      have hposlow : (0:ℝ) < (c^4 * (i:ℝ)^2)/256 := by positivity
      have hinv : Real.exp (-(c * Real.sqrt i)) ≤ 256/(c^4 * (i:ℝ)^2) := by
        rw [Real.exp_neg, inv_eq_one_div]
        refine le_trans (one_div_le_one_div_of_le hposlow hlow) (le_of_eq ?_)
        field_simp
      refine le_trans hinv (le_of_eq ?_)
      field_simp
      try ring
    have hbase : Summable (fun n : ℕ => 1/((n:ℝ)^2)) :=
      (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
    have hmaj : Summable (fun n : ℕ => (256/c^4) * (1/(((n+1:ℕ)):ℝ)^2)) := by
      have h1 : Summable (fun n : ℕ => 1/((((n+1:ℕ)):ℝ)^2)) :=
        (summable_nat_add_iff (f := fun n : ℕ => 1/((n:ℝ)^2)) 1).2 hbase
      exact h1.mul_left _
    have hgsum : Summable (fun i : ℕ => Real.exp (-(c * Real.sqrt i))) := by
      rw [← summable_nat_add_iff (f := fun i : ℕ => Real.exp (-(c * Real.sqrt i))) 1]
      refine Summable.of_nonneg_of_le (fun n => Real.exp_nonneg _) (fun n => ?_) hmaj
      exact hpt (n+1) (by omega)
    refine ⟨∑' i : ℕ, Real.exp (-(c * Real.sqrt i)),
      tsum_nonneg (fun i => Real.exp_nonneg _), ?_⟩
    intro I
    exact hgsum.sum_le_tsum I (fun i _ => Real.exp_nonneg _)
  
  obtain ⟨η, hη0, hηle, hη2δ⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1/2 ∧ 2*η ≤ δ := by
    refine ⟨min δ 1 / 2, ?_, ?_, ?_⟩
    · have h := lt_min hδ (by norm_num : (0:ℝ) < 1); linarith
    · have h := min_le_right δ (1:ℝ); linarith
    · have h := min_le_left δ (1:ℝ); linarith
  have hηb : 0 < η * b := mul_pos hη0 hb
  obtain ⟨C, hC0, hC⟩ := s2 (η*b) hηb
  have hAnn : (0:ℝ) ≤ C/b := div_nonneg hC0 hb.le
  have hBpos : (0:ℝ) < 2*η/3 := by positivity
  have hu0 : (0:ℝ) ≤ (1-η)*b := mul_nonneg (by linarith) hb.le
  filter_upwards [s5 (C/b) (2*η/3) hAnn hBpos] with M hM
  intro I
  have hterm : ∀ S ∈ I.powersetCard M,
      ∏ i ∈ S, Real.exp (-(b * Real.sqrt i))
        ≤ Real.exp (-((1-η)*b) * (∑ i ∈ Finset.range M, Real.sqrt i))
            * ∏ i ∈ S, Real.exp (-((η*b) * Real.sqrt i)) := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    obtain ⟨hSsub, hScard⟩ := hS
    have hSig : ∑ i ∈ Finset.range M, Real.sqrt i ≤ ∑ i ∈ S, Real.sqrt i := by
      have h := s3 S.card S rfl
      rwa [hScard] at h
    have e1 : ∏ i ∈ S, Real.exp (-(b * Real.sqrt i))
        = Real.exp (-(b * ∑ i ∈ S, Real.sqrt i)) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      simp
    have e2 : ∏ i ∈ S, Real.exp (-((η*b) * Real.sqrt i))
        = Real.exp (-((η*b) * ∑ i ∈ S, Real.sqrt i)) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      simp
    rw [e1, e2, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h2 : -((1-η)*b) * (∑ i ∈ S, Real.sqrt i)
        ≤ -((1-η)*b) * (∑ i ∈ Finset.range M, Real.sqrt i) := by
      nlinarith [mul_nonneg hu0 (sub_nonneg.2 hSig)]
    nlinarith [h2]
  have hsum1 := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum1
  have hs4' : ∑ S ∈ I.powersetCard M, ∏ i ∈ S, Real.exp (-((η*b) * Real.sqrt i))
      ≤ Real.exp C :=
    le_trans (s4 (fun i => Real.exp (-((η*b) * Real.sqrt i)))
      (fun i => Real.exp_nonneg _) I M) (Real.exp_le_exp.2 (hC I))
  have hchain : ∑ S ∈ I.powersetCard M, ∏ i ∈ S, Real.exp (-(b * Real.sqrt i))
      ≤ Real.exp (-((1-η)*b) * (∑ i ∈ Finset.range M, Real.sqrt i)) * Real.exp C :=
    le_trans hsum1 (mul_le_mul_of_nonneg_left hs4' (Real.exp_nonneg _))
  rw [← Real.exp_add] at hchain
  refine le_trans hchain (Real.exp_le_exp.2 ?_)
  have hX0 : (0:ℝ) ≤ (M:ℝ) ^ ((3:ℝ)/2) := Real.rpow_nonneg (Nat.cast_nonneg M) _
  have hR0 : (0:ℝ) ≤ Real.sqrt M := Real.sqrt_nonneg _
  have hF1 : (2/3:ℝ) * (M:ℝ)^((3:ℝ)/2) - Real.sqrt M
      ≤ ∑ i ∈ Finset.range M, Real.sqrt i := by
    linarith [s6 M]
  have hA1 : -((1-η)*b) * (∑ i ∈ Finset.range M, Real.sqrt i)
      ≤ -((1-η)*b) * ((2/3:ℝ) * (M:ℝ)^((3:ℝ)/2) - Real.sqrt M) := by
    nlinarith [mul_nonneg hu0 (sub_nonneg.2 hF1)]
  have hC1 : (0:ℝ) ≤ η * b * Real.sqrt M := by positivity
  have hbCb : b * (C/b) = C := by field_simp
  have F2' : C + b * Real.sqrt M ≤ (2*η*b/3) * (M:ℝ) ^ ((3:ℝ)/2) := by
    have h := mul_le_mul_of_nonneg_left hM hb.le
    rw [mul_add, hbCb] at h
    nlinarith [h]
  have hE : (0:ℝ) ≤ (δ - 2*η) * ((2*b/3) * (M:ℝ) ^ ((3:ℝ)/2)) :=
    mul_nonneg (by linarith) (by positivity)
  nlinarith [hA1, hC1, F2', hE]

theorem sum_sqrt_bounds (m : ℕ) :
    (2/3 : ℝ) * (m : ℝ) ^ ((3:ℝ)/2) - Real.sqrt m ≤ ∑ i ∈ Finset.range m, Real.sqrt i ∧
    ∑ i ∈ Finset.range m, Real.sqrt i ≤ (2/3 : ℝ) * (m : ℝ) ^ ((3:ℝ)/2) :=
by
  
  have hrp : ∀ z : ℝ, 0 ≤ z → z ^ ((3:ℝ)/2) = Real.sqrt z ^ 3 := by
    intro z hz
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (z ^ ((1:ℝ)/2)) 3, ← Real.rpow_mul hz]
    norm_num
  
  have key : ∀ a b : ℝ, 0 ≤ a → a ≤ b → 1 ≤ b → b ^ 2 = a ^ 2 + 1 →
      3 * a ≤ 2 * (b ^ 3 - a ^ 3) ∧ 2 * (b ^ 3 - a ^ 3) ≤ 3 * b := by
    intro a b ha0 hab hb1 hbsq
    have hpos : (0:ℝ) < a + b := by linarith
    have hid1 : (2 * (b ^ 3 - a ^ 3) - 3 * a) * (a + b) = (b - a) * (a + 2 * b) := by
      linear_combination (2 * (a * b + a ^ 2 + b ^ 2)) * hbsq
    have hid2 : (3 * b - 2 * (b ^ 3 - a ^ 3)) * (a + b) = (b - a) * (b + 2 * a) := by
      linear_combination (-(2 * (a * b + a ^ 2 + b ^ 2))) * hbsq
    have hn1 : (0:ℝ) ≤ (b - a) * (a + 2 * b) :=
      mul_nonneg (by linarith) (by linarith)
    have hn2 : (0:ℝ) ≤ (b - a) * (b + 2 * a) :=
      mul_nonneg (by linarith) (by linarith)
    constructor
    · nlinarith [hid1, hn1, hpos]
    · nlinarith [hid2, hn2, hpos]
  
  have hstep : ∀ y : ℝ, 0 ≤ y →
      Real.sqrt y ≤ 2 / 3 * ((y + 1) ^ ((3:ℝ)/2) - y ^ ((3:ℝ)/2)) ∧
      2 / 3 * ((y + 1) ^ ((3:ℝ)/2) - y ^ ((3:ℝ)/2)) ≤ Real.sqrt (y + 1) := by
    intro y hy
    have hy1 : (0:ℝ) ≤ y + 1 := by linarith
    have ha0 : (0:ℝ) ≤ Real.sqrt y := Real.sqrt_nonneg _
    have hb0 : (0:ℝ) ≤ Real.sqrt (y + 1) := Real.sqrt_nonneg _
    have hab : Real.sqrt y ≤ Real.sqrt (y + 1) := Real.sqrt_le_sqrt (by linarith)
    have ha2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
    have hb2 : Real.sqrt (y + 1) ^ 2 = y + 1 := Real.sq_sqrt hy1
    have hb1 : (1:ℝ) ≤ Real.sqrt (y + 1) := by nlinarith [hb2, hb0, hy]
    have hbsq : Real.sqrt (y + 1) ^ 2 = Real.sqrt y ^ 2 + 1 := by rw [ha2, hb2]
    obtain ⟨k1, k2⟩ := key (Real.sqrt y) (Real.sqrt (y + 1)) ha0 hab hb1 hbsq
    rw [hrp y hy, hrp (y + 1) hy1]
    constructor
    · linarith
    · linarith
  induction m with
  | zero =>
      norm_num [Real.zero_rpow (by norm_num : ((3:ℝ)/2) ≠ 0)]
  | succ n ih =>
      obtain ⟨ihl, ihu⟩ := ih
      have hn0 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      obtain ⟨hA, hB⟩ := hstep (n : ℝ) hn0
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [Finset.sum_range_succ, hcast]
      exact ⟨by linarith, by linarith⟩

theorem aset_infinite (u : ℕ → ℕ) (hmono : StrictMono u) (h2 : 2 ≤ u 0)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (u i) (u j))
    (hsum : Summable (fun n => 1 / (u n : ℝ))) : (ASet u).Infinite :=
by
  
  have hu2 : ∀ i, 2 ≤ u i := fun i => le_trans h2 (hmono.monotone (Nat.zero_le i))
  
  have hgnn : ∀ a : ℕ, (0:ℝ) ≤ 1 / (a : ℝ) := fun a =>
    one_div_nonneg.2 (Nat.cast_nonneg a)
  have hindnn : ∀ (S : Set ℕ) (n : ℕ),
      (0:ℝ) ≤ S.indicator (fun m : ℕ => 1 / (m : ℝ)) n := fun S n =>
    Set.indicator_nonneg (fun a _ => hgnn a) n
  
  have hS : Summable ((Set.range u).indicator (fun n : ℕ => 1 / (n : ℝ))) := by
    have hzero : ∀ x ∉ Set.range u,
        (Set.range u).indicator (fun n : ℕ => 1 / (n : ℝ)) x = 0 :=
      fun x hx => Set.indicator_of_notMem hx _
    have hcomp :
        Summable (((Set.range u).indicator (fun n : ℕ => 1 / (n : ℝ))) ∘ u) := by
      refine hsum.congr ?_
      intro n
      rw [Function.comp_apply, Set.indicator_of_mem (Set.mem_range_self n)]
    exact (hmono.injective.summable_iff hzero).1 hcomp
  by_contra hcon
  rw [Set.not_infinite] at hcon
  
  have hT : Summable ((ASet u).indicator (fun n : ℕ => 1 / (n : ℝ))) :=
    summable_subtype_iff_indicator.mp (hcon.summable (fun n : ℕ => 1 / (n : ℝ)))
  
  have hsub : {p : ℕ | Nat.Prime p} ⊆ Set.range u ∪ ASet u := by
    intro p hp
    by_cases hr : p ∈ Set.range u
    · exact Or.inl hr
    · refine Or.inr ?_
      have hmem : ∀ i, ¬ u i ∣ p := by
        intro i hdvd
        rcases (hp : Nat.Prime p).eq_one_or_self_of_dvd (u i) hdvd with h1 | h1
        · have := hu2 i; omega
        · exact hr ⟨i, h1⟩
      exact hmem
  
  refine not_summable_one_div_on_primes ?_
  have hadd : Summable (fun n : ℕ =>
      (Set.range u).indicator (fun m : ℕ => 1 / (m : ℝ)) n
        + (ASet u).indicator (fun m : ℕ => 1 / (m : ℝ)) n) := hS.add hT
  refine Summable.of_nonneg_of_le (fun n => hindnn _ n) (fun n => ?_) hadd
  by_cases hn : n ∈ {p : ℕ | Nat.Prime p}
  · rw [Set.indicator_of_mem hn]
    rcases hsub hn with h | h
    · rw [Set.indicator_of_mem h]
      linarith [hindnn (ASet u) n]
    · rw [Set.indicator_of_mem h]
      linarith [hindnn (Set.range u) n]
  · rw [Set.indicator_of_notMem hn]
    linarith [hindnn (Set.range u) n, hindnn (ASet u) n]

theorem pool_divisor_ratio_bound (P : ℕ → Finset ℕ) (hP : IsPools P)
    (hlog : PoolsLog P) (hbig : PoolsBig P)
    (hdiv : ∀ N m : ℕ, 1 ≤ N → 2 ≤ m →
      ((N.primeFactors.filter (fun p => m ≤ p)).card : ℝ) ≤ Real.log N / Real.log m)
    (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    ∃ K : ℕ, ∀ i : ℕ, K < i →
      (∀ p ∈ P i, Real.exp (Real.sqrt i / 2) ≤ (p : ℝ)) ∧
      (∀ m : ℕ, 1 ≤ m →
        (((P i).filter (fun p => p ∣ m)).card : ℝ)
          ≤ Real.log m * ((P i).card : ℝ) * Real.exp (-(b * Real.sqrt i))) :=
by
  
  
  
  set ρ : ℝ := Real.sqrt b with hρdef
  have hρ0 : (0:ℝ) < ρ := Real.sqrt_pos.2 hb0
  have hρ1 : ρ < 1 := by
    have h : Real.sqrt b < Real.sqrt 1 := Real.sqrt_lt_sqrt hb0.le hb1
    rwa [Real.sqrt_one] at h
  have hρρ : ρ * ρ = b := Real.mul_self_sqrt hb0.le
  
  have hL1 : ∀ᶠ n : ℕ in atTop,
      ∀ p ∈ P n, |Real.log p - Real.sqrt n| ≤ (1 - ρ) * Real.sqrt n :=
    hlog (1 - ρ) (by linarith)
  have hL2 : ∀ᶠ n : ℕ in atTop,
      ∀ p ∈ P n, |Real.log p - Real.sqrt n| ≤ (1/2 : ℝ) * Real.sqrt n :=
    hlog (1/2) (by norm_num)
  have hBB : ∀ᶠ n : ℕ in atTop, ∀ p ∈ P n, (p : ℝ) ^ ρ ≤ ((P n).card : ℝ) :=
    hbig ρ hρ1
  have hTT : ∀ᶠ n : ℕ in atTop, ⌈(1:ℝ)/b⌉₊ ≤ n := eventually_ge_atTop _
  obtain ⟨K, hK⟩ := eventually_atTop.1 (((hL1.and hL2).and hBB).and hTT)
  refine ⟨K, ?_⟩
  intro i hi
  obtain ⟨⟨⟨hl1, hl2⟩, hbb⟩, ht⟩ := hK i hi.le
  set x : ℝ := Real.sqrt (i : ℝ) with hxdef
  have hx0 : (0:ℝ) ≤ x := Real.sqrt_nonneg _
  have hxx : x * x = (i : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg i)
  have hppos : ∀ p ∈ P i, (0:ℝ) < (p : ℝ) := by
    intro p hp
    have h2 : 2 ≤ p := (hP.2.1 i p hp).two_le
    have h2R : (2:ℝ) ≤ (p : ℝ) := by exact_mod_cast h2
    linarith
  constructor
  · 
    intro p hp
    have h := (abs_le.1 (hl2 p hp)).1
    have hlogp : x / 2 ≤ Real.log (p : ℝ) := by linarith
    calc Real.exp (x / 2) ≤ Real.exp (Real.log (p : ℝ)) := Real.exp_le_exp.2 hlogp
      _ = (p : ℝ) := Real.exp_log (hppos p hp)
  · 
    
    have hplow : ∀ p ∈ P i, Real.exp (ρ * x) ≤ (p : ℝ) := by
      intro p hp
      have h := (abs_le.1 (hl1 p hp)).1
      have hring : (1 - ρ) * x = x - ρ * x := by ring
      rw [hring] at h
      have hlogp : ρ * x ≤ Real.log (p : ℝ) := by linarith
      calc Real.exp (ρ * x) ≤ Real.exp (Real.log (p : ℝ)) := Real.exp_le_exp.2 hlogp
        _ = (p : ℝ) := Real.exp_log (hppos p hp)
    
    have hbi : (1:ℝ) ≤ b * (i : ℝ) := by
      have h1 : ((⌈(1:ℝ)/b⌉₊ : ℕ) : ℝ) ≤ (i : ℝ) := by exact_mod_cast ht
      have h2 : (1:ℝ)/b ≤ ((⌈(1:ℝ)/b⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have h3 : (1:ℝ)/b ≤ (i : ℝ) := le_trans h2 h1
      have h4 : (1:ℝ) ≤ (i : ℝ) * b := (div_le_iff₀ hb0).1 h3
      linarith
    have hρx1 : (1:ℝ) ≤ ρ * x := by
      by_contra hcon
      push_neg at hcon
      have hnn : (0:ℝ) ≤ ρ * x := mul_nonneg hρ0.le hx0
      have hsq : (ρ * x) * (ρ * x) < 1 := by nlinarith
      have heq : (ρ * x) * (ρ * x) = b * (i : ℝ) := by
        rw [← hρρ, ← hxx]; ring
      rw [heq] at hsq
      linarith
    
    have hexpq : Real.exp (ρ * x) ≤ ((⌈Real.exp (ρ * x)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have hq2 : 2 ≤ ⌈Real.exp (ρ * x)⌉₊ := by
      have h1 : Real.exp 1 ≤ Real.exp (ρ * x) := Real.exp_le_exp.2 hρx1
      have h2 : (1:ℝ) + 1 ≤ Real.exp 1 := Real.add_one_le_exp 1
      have h3 : (2:ℝ) ≤ ((⌈Real.exp (ρ * x)⌉₊ : ℕ) : ℝ) := by linarith
      exact_mod_cast h3
    have hqS : ∀ p ∈ P i, ⌈Real.exp (ρ * x)⌉₊ ≤ p := by
      intro p hp
      exact Nat.ceil_le.2 (hplow p hp)
    have hlogq : (1:ℝ) ≤ Real.log ((⌈Real.exp (ρ * x)⌉₊ : ℕ) : ℝ) := by
      have h1 : Real.log (Real.exp (ρ * x)) ≤ Real.log ((⌈Real.exp (ρ * x)⌉₊ : ℕ) : ℝ) :=
        Real.log_le_log (Real.exp_pos _) hexpq
      rw [Real.log_exp] at h1
      linarith
    
    obtain ⟨p₀, hp₀⟩ := hP.1 i
    have hstep1 : (Real.exp (ρ * x)) ^ ρ ≤ ((P i).card : ℝ) :=
      le_trans (Real.rpow_le_rpow (Real.exp_nonneg _) (hplow p₀ hp₀) hρ0.le) (hbb p₀ hp₀)
    have hstep2 : Real.exp (b * x) ≤ ((P i).card : ℝ) := by
      have he : Real.exp ((ρ * x) * ρ) = (Real.exp (ρ * x)) ^ ρ := Real.exp_mul (ρ * x) ρ
      have harg : (ρ * x) * ρ = b * x := by rw [← hρρ]; ring
      rw [harg] at he
      rw [he]
      exact hstep1
    have hone : (1:ℝ) ≤ ((P i).card : ℝ) * Real.exp (-(b * x)) := by
      have hpos : (0:ℝ) < Real.exp (-(b * x)) := Real.exp_pos _
      have hid : Real.exp (b * x) * Real.exp (-(b * x)) = 1 := by
        rw [← Real.exp_add]; simp
      have h := mul_le_mul_of_nonneg_right hstep2 hpos.le
      rw [hid] at h
      exact h
    
    intro m hm
    have hm0 : m ≠ 0 := by omega
    have hmR : (1:ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hlogm : (0:ℝ) ≤ Real.log (m : ℝ) := Real.log_nonneg hmR
    
    have hsub : (P i).filter (fun p => p ∣ m)
        ⊆ m.primeFactors.filter (fun p => ⌈Real.exp (ρ * x)⌉₊ ≤ p) := by
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      obtain ⟨hpP, hpd⟩ := hp
      exact ⟨Nat.mem_primeFactors.2 ⟨hP.2.1 i p hpP, hpd, hm0⟩, hqS p hpP⟩
    have hI : (((P i).filter (fun p => p ∣ m)).card : ℝ) ≤ Real.log (m : ℝ) := by
      have hc : ((P i).filter (fun p => p ∣ m)).card
          ≤ (m.primeFactors.filter (fun p => ⌈Real.exp (ρ * x)⌉₊ ≤ p)).card :=
        Finset.card_le_card hsub
      have hcR : (((P i).filter (fun p => p ∣ m)).card : ℝ)
          ≤ ((m.primeFactors.filter (fun p => ⌈Real.exp (ρ * x)⌉₊ ≤ p)).card : ℝ) := by
        exact_mod_cast hc
      have hd := hdiv m (⌈Real.exp (ρ * x)⌉₊) hm hq2
      have hdd : Real.log (m : ℝ) / Real.log ((⌈Real.exp (ρ * x)⌉₊ : ℕ) : ℝ)
          ≤ Real.log (m : ℝ) := _root_.div_le_self hlogm hlogq
      linarith
    
    have hII : Real.log (m : ℝ)
        ≤ Real.log (m : ℝ) * ((P i).card : ℝ) * Real.exp (-(b * x)) := by
      have h := mul_le_mul_of_nonneg_left hone hlogm
      calc Real.log (m : ℝ) = Real.log (m : ℝ) * 1 := by ring
        _ ≤ Real.log (m : ℝ) * (((P i).card : ℝ) * Real.exp (-(b * x))) := h
        _ = Real.log (m : ℝ) * ((P i).card : ℝ) * Real.exp (-(b * x)) := by ring
    linarith

theorem cert_event_measure_le (P : ℕ → Finset ℕ) (hne : ∀ n, (P n).Nonempty)
    (N M K L Q : ℕ) (w : ℕ → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hfil : ∀ i : ℕ, K < i → ∀ m : ℕ, 1 ≤ m → m < N + Q →
      (((P i).filter (fun p => p ∣ m)).card : ℝ) ≤ w i * ((P i).card : ℝ))
    (hout : ∀ i : ℕ, L < i → ∀ p ∈ P i, N + Q ≤ p) :
    (MeasureTheory.Measure.infinitePi
        (fun n => (PMF.uniformOfFinset (P n) (hne n)).toMeasure))
      {ω : ℕ → ℕ | (∀ n, ω n ∈ P n) ∧ HasCert ω N M K Q}
      ≤ ENNReal.ofReal ((N : ℝ) * (Q : ℝ) ^ M
          * ∑ S ∈ (Finset.Ioc K L).powersetCard M, ∏ i ∈ S, w i) :=
by
  
  
  
  
  

  
  have hQw : ∀ i : ℕ, (0:ℝ) ≤ (Q : ℝ) * w i :=
    fun i => mul_nonneg (Nat.cast_nonneg Q) (hw0 i)
  have hprodnn : ∀ S : Finset ℕ, (0:ℝ) ≤ (Q : ℝ) ^ M * ∏ i ∈ S, w i := by
    intro S
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg Q) M)
      (Finset.prod_nonneg (fun i _ => hw0 i))

  
  
  
  have hcover : {ω : ℕ → ℕ | (∀ n, ω n ∈ P n) ∧ HasCert ω N M K Q}
      ⊆ ⋃ n ∈ Finset.range N, ⋃ S ∈ (Finset.Ioc K L).powersetCard M,
          Set.pi (↑S : Set ℕ) (fun i =>
            (↑((Finset.Icc 1 Q).biUnion
                (fun j => (P i).filter (fun p => p ∣ n + j))) : Set ℕ)) := by
    rintro ω ⟨hmem, n, hn, S, j, hcard, hK, hj, hdvd⟩
    simp only [Set.mem_iUnion, exists_prop]
    refine ⟨n, Finset.mem_range.2 hn, S, Finset.mem_powersetCard.2 ⟨?_, hcard⟩, ?_⟩
    · 
      intro i hi
      refine Finset.mem_Ioc.2 ⟨hK i hi, ?_⟩
      by_contra hcon
      push_neg at hcon
      
      have h1 : N + Q ≤ ω i := hout i hcon (ω i) (hmem i)
      have h2 : 1 ≤ j i := (hj i hi).1
      have h3 : j i ≤ Q := (hj i hi).2
      have h4 : ω i ≤ n + j i := Nat.le_of_dvd (by omega) (hdvd i hi)
      omega
    · 
      intro i hi
      have hiS : i ∈ S := hi
      exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨j i, Finset.mem_Icc.2 (hj i hiS),
        Finset.mem_filter.2 ⟨hmem i, hdvd i hiS⟩⟩)

  
  have hunif : ∀ (s T : Finset ℕ) (hs : s.Nonempty) (c : ℝ), 0 ≤ c → T ⊆ s →
      (T.card : ℝ) ≤ c * (s.card : ℝ) →
      (PMF.uniformOfFinset s hs).toMeasure (↑T : Set ℕ) ≤ ENNReal.ofReal c := by
    intro s T hs c hc hT hcard
    rw [PMF.toMeasure_apply_finset]
    have hpt : ∀ x ∈ T, (PMF.uniformOfFinset s hs) x = ((s.card : ℝ≥0∞))⁻¹ := by
      intro x hx
      simp [PMF.uniformOfFinset_apply, hT hx]
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, nsmul_eq_mul, ← div_eq_mul_inv]
    rw [ENNReal.div_le_iff_le_mul (Or.inr ENNReal.ofReal_ne_top)
      (Or.inl (ENNReal.natCast_ne_top _))]
    rw [show ((T.card : ℝ≥0∞)) = ENNReal.ofReal ((T.card : ℝ)) from
        (ENNReal.ofReal_natCast _).symm,
      show ((s.card : ℝ≥0∞)) = ENNReal.ofReal ((s.card : ℝ)) from
        (ENNReal.ofReal_natCast _).symm,
      ← ENNReal.ofReal_mul hc]
    exact ENNReal.ofReal_le_ofReal hcard

  
  have hcoord : ∀ n : ℕ, n < N → ∀ i : ℕ, K < i →
      (PMF.uniformOfFinset (P i) (hne i)).toMeasure
        (↑((Finset.Icc 1 Q).biUnion
            (fun j => (P i).filter (fun p => p ∣ n + j))) : Set ℕ)
        ≤ ENNReal.ofReal ((Q : ℝ) * w i) := by
    intro n hn i hi
    refine hunif (P i)
      ((Finset.Icc 1 Q).biUnion (fun j => (P i).filter (fun p => p ∣ n + j)))
      (hne i) ((Q : ℝ) * w i) (hQw i) ?_ ?_
    · 
      intro p hp
      rw [Finset.mem_biUnion] at hp
      obtain ⟨j, -, hj⟩ := hp
      exact (Finset.mem_filter.1 hj).1
    · 
      have h1 : (((Finset.Icc 1 Q).biUnion
            (fun j => (P i).filter (fun p => p ∣ n + j))).card)
          ≤ ∑ j ∈ Finset.Icc 1 Q, ((P i).filter (fun p => p ∣ n + j)).card :=
        Finset.card_biUnion_le
      have h2 : ((((Finset.Icc 1 Q).biUnion
            (fun j => (P i).filter (fun p => p ∣ n + j))).card : ℝ))
          ≤ ∑ j ∈ Finset.Icc 1 Q, (((P i).filter (fun p => p ∣ n + j)).card : ℝ) := by
        calc ((((Finset.Icc 1 Q).biUnion
                (fun j => (P i).filter (fun p => p ∣ n + j))).card : ℝ))
            ≤ ((∑ j ∈ Finset.Icc 1 Q,
                  ((P i).filter (fun p => p ∣ n + j)).card : ℕ) : ℝ) := by
              exact_mod_cast h1
          _ = ∑ j ∈ Finset.Icc 1 Q,
                (((P i).filter (fun p => p ∣ n + j)).card : ℝ) := by push_cast; ring
      have h3 : ∑ j ∈ Finset.Icc 1 Q, (((P i).filter (fun p => p ∣ n + j)).card : ℝ)
          ≤ ∑ _j ∈ Finset.Icc 1 Q, (w i * ((P i).card : ℝ)) := by
        refine Finset.sum_le_sum ?_
        intro j hj
        rw [Finset.mem_Icc] at hj
        exact hfil i hi (n + j) (by omega) (by omega)
      have h4 : ∑ _j ∈ Finset.Icc 1 Q, (w i * ((P i).card : ℝ))
          = ((Q : ℝ) * w i) * ((P i).card : ℝ) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        push_cast
        ring
      linarith

  
  have hcyl : ∀ n : ℕ, n ∈ Finset.range N → ∀ S : Finset ℕ,
      S ∈ (Finset.Ioc K L).powersetCard M →
      (MeasureTheory.Measure.infinitePi
          (fun k => (PMF.uniformOfFinset (P k) (hne k)).toMeasure))
        (Set.pi (↑S : Set ℕ) (fun i =>
          (↑((Finset.Icc 1 Q).biUnion
              (fun j => (P i).filter (fun p => p ∣ n + j))) : Set ℕ)))
        ≤ ENNReal.ofReal ((Q : ℝ) ^ M * ∏ i ∈ S, w i) := by
    intro n hn S hS
    obtain ⟨hsubS, hScard⟩ := Finset.mem_powersetCard.1 hS
    have hn' : n < N := Finset.mem_range.1 hn
    rw [MeasureTheory.Measure.infinitePi_pi _ (fun i _ => MeasurableSet.of_discrete)]
    have hstep : ∏ i ∈ S, (PMF.uniformOfFinset (P i) (hne i)).toMeasure
          (↑((Finset.Icc 1 Q).biUnion
              (fun j => (P i).filter (fun p => p ∣ n + j))) : Set ℕ)
        ≤ ∏ i ∈ S, ENNReal.ofReal ((Q : ℝ) * w i) :=
      Finset.prod_le_prod' (fun i hiS =>
        hcoord n hn' i (Finset.mem_Ioc.1 (hsubS hiS)).1)
    have heq : ∏ i ∈ S, ENNReal.ofReal ((Q : ℝ) * w i)
        = ENNReal.ofReal ((Q : ℝ) ^ M * ∏ i ∈ S, w i) := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => hQw i)]
      congr 1
      rw [Finset.prod_mul_distrib, Finset.prod_const, hScard]
    rw [← heq]
    exact hstep

  
  refine le_trans (MeasureTheory.measure_mono hcover) ?_
  refine le_trans (MeasureTheory.measure_biUnion_finset_le (Finset.range N) _) ?_
  refine le_trans (Finset.sum_le_sum (fun n _ =>
    MeasureTheory.measure_biUnion_finset_le ((Finset.Ioc K L).powersetCard M) _)) ?_
  refine le_trans (Finset.sum_le_sum (fun n hn =>
    Finset.sum_le_sum (fun S hS => hcyl n hn S hS))) ?_
  have hinner : (∑ S ∈ (Finset.Ioc K L).powersetCard M,
        ENNReal.ofReal ((Q : ℝ) ^ M * ∏ i ∈ S, w i))
      = ENNReal.ofReal ((Q : ℝ) ^ M
          * ∑ S ∈ (Finset.Ioc K L).powersetCard M, ∏ i ∈ S, w i) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun S _ => hprodnn S), Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun n _ => hinner), Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, show ((N : ℝ≥0∞)) = ENNReal.ofReal ((N : ℝ)) from
      (ENNReal.ofReal_natCast _).symm,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg N), mul_assoc]

theorem exists_pool_point_avoiding (P : ℕ → Finset ℕ) (hne : ∀ n, (P n).Nonempty)
    (B : ℕ → ℕ → ℕ → Set (ℕ → ℕ))
    (hB : ∀ C k : ℕ, ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ᶠ s : ℕ in atTop,
      (MeasureTheory.Measure.infinitePi
          (fun n => (PMF.uniformOfFinset (P n) (hne n)).toMeasure)) (B C k s)
        ≤ ENNReal.ofReal (r ^ s)) :
    ∃ u : ℕ → ℕ, (∀ n, u n ∈ P n) ∧
      ∀ C k : ℕ, ∀ᶠ s : ℕ in atTop, u ∉ B C k s :=
by
  classical
  
  
  haveI hprob : ∀ n : ℕ, MeasureTheory.IsProbabilityMeasure
      ((PMF.uniformOfFinset (P n) (hne n)).toMeasure) :=
    fun n => PMF.toMeasure.isProbabilityMeasure _
  haveI hPM : MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.Measure.infinitePi
        (fun n => (PMF.uniformOfFinset (P n) (hne n)).toMeasure)) := inferInstance
  
  have hcoord : ∀ n : ℕ, ∀ᵐ ω ∂(MeasureTheory.Measure.infinitePi
      (fun m => (PMF.uniformOfFinset (P m) (hne m)).toMeasure)), ω n ∈ P n := by
    intro n
    have hPm : MeasurableSet ((P n : Set ℕ)) := MeasurableSet.of_discrete
    have hmeas : Measurable (fun ω : ℕ → ℕ => ω n) := measurable_pi_apply n
    have hS : MeasurableSet {ω : ℕ → ℕ | ω n ∈ P n} := hmeas hPm
    have hmass : (MeasureTheory.Measure.infinitePi
        (fun m => (PMF.uniformOfFinset (P m) (hne m)).toMeasure))
          {ω : ℕ → ℕ | ω n ∈ P n} = 1 := by
      have h1 : {ω : ℕ → ℕ | ω n ∈ P n} = (fun ω : ℕ → ℕ => ω n) ⁻¹' ((P n : Set ℕ)) := rfl
      rw [h1, ← MeasureTheory.Measure.map_apply hmeas hPm,
        MeasureTheory.Measure.infinitePi_map_eval _ n]
      refine (PMF.toMeasure_apply_eq_one_iff _ hPm).2 ?_
      simp [PMF.support_uniformOfFinset]
    rw [MeasureTheory.ae_iff]
    have hc : {ω : ℕ → ℕ | ¬ (ω n ∈ P n)} = {ω : ℕ → ℕ | ω n ∈ P n}ᶜ := rfl
    rw [hc]
    exact (MeasureTheory.prob_compl_eq_zero_iff hS).2 hmass
  
  choose r hr0 hr1 hrB using hB
  have havoid : ∀ C k : ℕ, ∀ᵐ ω ∂(MeasureTheory.Measure.infinitePi
      (fun m => (PMF.uniformOfFinset (P m) (hne m)).toMeasure)),
      ∀ᶠ s : ℕ in atTop, ω ∉ B C k s := by
    intro C k
    refine MeasureTheory.ae_eventually_notMem ?_
    obtain ⟨s₀, hs₀⟩ := Filter.eventually_atTop.1 (hrB C k)
    have hρ1 : ENNReal.ofReal (r C k) < 1 := ENNReal.ofReal_lt_one.2 (hr1 C k)
    have hbound : ∀ s : ℕ, (MeasureTheory.Measure.infinitePi
        (fun m => (PMF.uniformOfFinset (P m) (hne m)).toMeasure)) (B C k s)
        ≤ (if s < s₀ then (1 : ℝ≥0∞) else 0) + (ENNReal.ofReal (r C k)) ^ s := by
      intro s
      by_cases h : s < s₀
      · simp only [h, if_true]
        exact le_trans MeasureTheory.prob_le_one le_self_add
      · simp only [h, if_false, zero_add]
        have h2 := hs₀ s (not_lt.1 h)
        rwa [ENNReal.ofReal_pow (hr0 C k)] at h2
    have hmaj : (∑' s : ℕ, (MeasureTheory.Measure.infinitePi
          (fun m => (PMF.uniformOfFinset (P m) (hne m)).toMeasure)) (B C k s))
        ≤ (∑' s : ℕ, (if s < s₀ then (1 : ℝ≥0∞) else 0))
          + ∑' s : ℕ, (ENNReal.ofReal (r C k)) ^ s := by
      rw [← ENNReal.tsum_add]
      exact ENNReal.tsum_le_tsum hbound
    refine ne_top_of_le_ne_top ?_ hmaj
    refine ENNReal.add_ne_top.2 ⟨?_, ?_⟩
    · have hfin : ∑' s : ℕ, (if s < s₀ then (1 : ℝ≥0∞) else 0)
          = ∑ s ∈ Finset.range s₀, (if s < s₀ then (1 : ℝ≥0∞) else 0) := by
        refine tsum_eq_sum ?_
        intro b hb
        rw [Finset.mem_range] at hb
        simp [hb]
      rw [hfin]
      exact ENNReal.sum_ne_top.2 (fun i _ => by split <;> simp)
    · rw [ENNReal.tsum_geometric]
      refine ENNReal.inv_ne_top.2 ?_
      intro hcz
      exact absurd (tsub_eq_zero_iff_le.1 hcz) (not_le.2 hρ1)
  
  have hall1 : ∀ᵐ ω ∂(MeasureTheory.Measure.infinitePi
      (fun m => (PMF.uniformOfFinset (P m) (hne m)).toMeasure)), ∀ n : ℕ, ω n ∈ P n :=
    MeasureTheory.ae_all_iff.2 hcoord
  have hall2 : ∀ᵐ ω ∂(MeasureTheory.Measure.infinitePi
      (fun m => (PMF.uniformOfFinset (P m) (hne m)).toMeasure)),
      ∀ C k : ℕ, ∀ᶠ s : ℕ in atTop, ω ∉ B C k s :=
    MeasureTheory.ae_all_iff.2
      (fun C => MeasureTheory.ae_all_iff.2 (fun k => havoid C k))
  haveI hne_bot : (MeasureTheory.ae (MeasureTheory.Measure.infinitePi
      (fun m => (PMF.uniformOfFinset (P m) (hne m)).toMeasure))).NeBot :=
    MeasureTheory.IsProbabilityMeasure.ae_neBot
  obtain ⟨u, hu1, hu2⟩ := (hall1.and hall2).exists
  exact ⟨u, hu1, hu2⟩

theorem cert_decay_bound (η b δ' θ : ℝ)
    (hη : 0 < η) (hb0 : 0 < b) (hδ'0 : 0 < δ') (hδ'1 : δ' < 1)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1/4)
    (hkey : 2/3 + 2*θ ≤ (1 - δ') * (2 * b / 3) * (1 + η) ^ ((3:ℝ)/2))
    (hesym : ∀ᶠ M : ℕ in atTop, ∀ I : Finset ℕ,
      ∑ S ∈ I.powersetCard M, ∏ i ∈ S, Real.exp (-(b * Real.sqrt i))
        ≤ Real.exp (-(1 - δ') * (2 * b / 3) * (M : ℝ) ^ ((3:ℝ)/2))) :
    ∀ᶠ s : ℕ in atTop, ∀ (I : Finset ℕ) (V : ℝ), 0 ≤ V → V ≤ (s : ℝ) ^ (3:ℕ) →
      Real.exp ((2/3 + θ) * (s : ℝ) ^ ((3:ℝ)/2)) * V ^ (⌈(1 + η) * (s:ℝ)⌉₊)
        * (∑ S ∈ I.powersetCard (⌈(1 + η) * (s:ℝ)⌉₊),
             ∏ i ∈ S, Real.exp (-(b * Real.sqrt i)))
        ≤ Real.exp (-(θ * (s : ℝ))) :=
by
  
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.1 hesym
  have hη1 : (0:ℝ) < 1 + η := by linarith
  have hK0 : (0:ℝ) < (1 - δ') * (2 * b / 3) := mul_pos (by linarith) (by linarith)
  
  obtain ⟨W, hW2, hWc⟩ : ∃ W : ℝ, 2 ≤ W ∧ 8 * (6 * (1 + η)) ≤ θ * W := by
    refine ⟨max 2 (8 * (6 * (1 + η)) / θ), le_max_left _ _, ?_⟩
    have h := le_max_right (2:ℝ) (8 * (6 * (1 + η)) / θ)
    rw [div_le_iff₀ hθ0] at h
    linarith
  have hW0 : (0:ℝ) ≤ W := by linarith
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (W ^ 4)
  filter_upwards [Filter.eventually_ge_atTop M₀, Filter.eventually_ge_atTop n₀,
    Filter.eventually_ge_atTop 1] with s hsM₀ hsn₀ hs1
  intro I V hV0 hVs
  have hsR : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs1
  have hs0 : (0:ℝ) ≤ (s:ℝ) := by linarith
  have hspos : (0:ℝ) < (s:ℝ) := by linarith
  have hn₀R : ((n₀ : ℕ) : ℝ) ≤ (s:ℝ) := by exact_mod_cast hsn₀
  have hW4s : W ^ 4 ≤ (s:ℝ) := le_trans hn₀.le hn₀R
  have ht0 : (0:ℝ) ≤ Real.sqrt (s:ℝ) := Real.sqrt_nonneg _
  
  obtain ⟨w, hw0, hs_eq, hX_eq, hWw⟩ :
      ∃ w : ℝ, 0 ≤ w ∧ (s:ℝ) = w ^ 4 ∧ (s:ℝ) ^ ((3:ℝ)/2) = w ^ 6 ∧ W ≤ w := by
    refine ⟨Real.sqrt (Real.sqrt (s:ℝ)), Real.sqrt_nonneg _, ?_, ?_, ?_⟩
    · rw [show Real.sqrt (Real.sqrt (s:ℝ)) ^ 4
            = (Real.sqrt (Real.sqrt (s:ℝ)) ^ 2) ^ 2 from by ring,
        Real.sq_sqrt ht0, Real.sq_sqrt hs0]
    · have hrp : (s:ℝ) ^ ((3:ℝ)/2) = Real.sqrt (s:ℝ) ^ (3:ℕ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((s:ℝ) ^ ((1:ℝ)/2)) 3,
          ← Real.rpow_mul hs0]
        norm_num
      rw [hrp, show Real.sqrt (Real.sqrt (s:ℝ)) ^ 6
            = (Real.sqrt (Real.sqrt (s:ℝ)) ^ 2) ^ 3 from by ring,
        Real.sq_sqrt ht0]
    · have hWt : W ^ 2 ≤ Real.sqrt (s:ℝ) := by
        have h1 : Real.sqrt (W ^ 4) ≤ Real.sqrt (s:ℝ) := Real.sqrt_le_sqrt hW4s
        rwa [show W ^ 4 = (W ^ 2) ^ 2 from by ring,
          Real.sqrt_sq (by positivity : (0:ℝ) ≤ W ^ 2)] at h1
      have h2 : Real.sqrt (W ^ 2) ≤ Real.sqrt (Real.sqrt (s:ℝ)) := Real.sqrt_le_sqrt hWt
      rwa [Real.sqrt_sq hW0] at h2
  have hw2ge : (2:ℝ) ≤ w := le_trans hW2 hWw
  have hwpos : (0:ℝ) < w := by linarith
  have hwsq : (4:ℝ) ≤ w ^ 2 := by nlinarith
  have hθw : 8 * (6 * (1 + η)) ≤ θ * w :=
    le_trans hWc (mul_le_mul_of_nonneg_left hWw hθ0.le)
  
  have hlogs : Real.log (s:ℝ) ≤ 4 * w := by
    have h1 : Real.log (s:ℝ) = 4 * Real.log w := by
      rw [hs_eq, Real.log_pow]; push_cast; ring
    have h2 : Real.log w ≤ w - 1 := Real.log_le_sub_one_of_pos hwpos
    rw [h1]; linarith
  have hlog0 : (0:ℝ) ≤ Real.log (s:ℝ) := Real.log_nonneg hsR
  
  have hrace : 6 * (1 + η) * (s:ℝ) * Real.log (s:ℝ)
      ≤ θ * ((s:ℝ) ^ ((3:ℝ)/2) - (s:ℝ)) := by
    have hcw4 : (0:ℝ) ≤ 6 * (1 + η) * w ^ 4 :=
      mul_nonneg (by linarith) (by positivity)
    have e0 : 6 * (1 + η) * (s:ℝ) * Real.log (s:ℝ) ≤ 4 * (6 * (1 + η)) * w ^ 5 := by
      calc 6 * (1 + η) * (s:ℝ) * Real.log (s:ℝ)
          = (6 * (1 + η) * w ^ 4) * Real.log (s:ℝ) := by rw [hs_eq]
        _ ≤ (6 * (1 + η) * w ^ 4) * (4 * w) := mul_le_mul_of_nonneg_left hlogs hcw4
        _ = 4 * (6 * (1 + η)) * w ^ 5 := by ring
    have e1 : 4 * (6 * (1 + η)) * w ^ 5 ≤ θ * w ^ 6 / 2 := by
      have h := mul_le_mul_of_nonneg_right hθw (by positivity : (0:ℝ) ≤ w ^ 5 / 2)
      nlinarith [h]
    have e2 : θ * w ^ 6 / 2 ≤ θ * (w ^ 6 - w ^ 4) := by
      have h := mul_nonneg (mul_nonneg hθ0.le (by positivity : (0:ℝ) ≤ w ^ 4))
        (by linarith : (0:ℝ) ≤ w ^ 2 - 2)
      nlinarith [h]
    have e3 : θ * (w ^ 6 - w ^ 4) = θ * ((s:ℝ) ^ ((3:ℝ)/2) - (s:ℝ)) := by
      rw [hX_eq, hs_eq]
    linarith
  
  have hX0 : (0:ℝ) ≤ (s:ℝ) ^ ((3:ℝ)/2) := Real.rpow_nonneg hs0 _
  have hcs0 : (0:ℝ) ≤ (1 + η) * (s:ℝ) := mul_nonneg hη1.le hs0
  have hceil1 : (1 + η) * (s:ℝ) ≤ ((⌈(1 + η) * (s:ℝ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hηs : (0:ℝ) ≤ η * (s:ℝ) := mul_nonneg hη.le hs0
  have hsMcast : (s:ℝ) ≤ ((⌈(1 + η) * (s:ℝ)⌉₊ : ℕ) : ℝ) := by linarith [hceil1, hηs]
  have hsM : s ≤ ⌈(1 + η) * (s:ℝ)⌉₊ := by exact_mod_cast hsMcast
  have hM₀M : M₀ ≤ ⌈(1 + η) * (s:ℝ)⌉₊ := le_trans hsM₀ hsM
  have hceil2 : ((⌈(1 + η) * (s:ℝ)⌉₊ : ℕ) : ℝ) < (1 + η) * (s:ℝ) + 1 :=
    Nat.ceil_lt_add_one hcs0
  have hMle : ((⌈(1 + η) * (s:ℝ)⌉₊ : ℕ) : ℝ) ≤ 2 * (1 + η) * (s:ℝ) := by
    linarith [hceil2, hsR, hηs]
  
  have hsum := hM₀ (⌈(1 + η) * (s:ℝ)⌉₊) hM₀M I
  have hrpow : ((1 + η) * (s:ℝ)) ^ ((3:ℝ)/2)
      ≤ (((⌈(1 + η) * (s:ℝ)⌉₊ : ℕ) : ℝ)) ^ ((3:ℝ)/2) :=
    Real.rpow_le_rpow hcs0 hceil1 (by norm_num)
  have hmulrpow : ((1 + η) * (s:ℝ)) ^ ((3:ℝ)/2)
      = (1 + η) ^ ((3:ℝ)/2) * (s:ℝ) ^ ((3:ℝ)/2) := Real.mul_rpow hη1.le hs0
  have hexpo : (1 - δ') * (2 * b / 3) * (1 + η) ^ ((3:ℝ)/2) * (s:ℝ) ^ ((3:ℝ)/2)
      ≤ (1 - δ') * (2 * b / 3) * (((⌈(1 + η) * (s:ℝ)⌉₊ : ℕ) : ℝ)) ^ ((3:ℝ)/2) := by
    have h := mul_le_mul_of_nonneg_left hrpow hK0.le
    rw [hmulrpow] at h
    calc (1 - δ') * (2 * b / 3) * (1 + η) ^ ((3:ℝ)/2) * (s:ℝ) ^ ((3:ℝ)/2)
        = (1 - δ') * (2 * b / 3) * ((1 + η) ^ ((3:ℝ)/2) * (s:ℝ) ^ ((3:ℝ)/2)) := by ring
      _ ≤ (1 - δ') * (2 * b / 3) * (((⌈(1 + η) * (s:ℝ)⌉₊ : ℕ) : ℝ)) ^ ((3:ℝ)/2) := h
  have hsum2 : (∑ S ∈ I.powersetCard (⌈(1 + η) * (s:ℝ)⌉₊),
        ∏ i ∈ S, Real.exp (-(b * Real.sqrt i)))
      ≤ Real.exp (-((1 - δ') * (2 * b / 3) * (1 + η) ^ ((3:ℝ)/2)
          * (s:ℝ) ^ ((3:ℝ)/2))) :=
    le_trans hsum (Real.exp_le_exp.2 (by linarith [hexpo]))
  
  have hVM : V ^ (⌈(1 + η) * (s:ℝ)⌉₊)
      ≤ Real.exp (3 * ((⌈(1 + η) * (s:ℝ)⌉₊ : ℕ) : ℝ) * Real.log (s:ℝ)) := by
    have h1 : V ^ (⌈(1 + η) * (s:ℝ)⌉₊) ≤ ((s:ℝ) ^ (3:ℕ)) ^ (⌈(1 + η) * (s:ℝ)⌉₊) :=
      pow_le_pow_left₀ hV0 hVs _
    have h2 : ((s:ℝ) ^ (3:ℕ)) ^ (⌈(1 + η) * (s:ℝ)⌉₊)
        = (s:ℝ) ^ (3 * ⌈(1 + η) * (s:ℝ)⌉₊) := (pow_mul (s:ℝ) 3 _).symm
    have h3 : (0:ℝ) < (s:ℝ) ^ (3 * ⌈(1 + η) * (s:ℝ)⌉₊) := pow_pos hspos _
    have h4 : Real.log ((s:ℝ) ^ (3 * ⌈(1 + η) * (s:ℝ)⌉₊))
        = 3 * ((⌈(1 + η) * (s:ℝ)⌉₊ : ℕ) : ℝ) * Real.log (s:ℝ) := by
      rw [Real.log_pow]; push_cast; ring
    calc V ^ (⌈(1 + η) * (s:ℝ)⌉₊)
        ≤ (s:ℝ) ^ (3 * ⌈(1 + η) * (s:ℝ)⌉₊) := by rw [← h2]; exact h1
      _ = Real.exp (Real.log ((s:ℝ) ^ (3 * ⌈(1 + η) * (s:ℝ)⌉₊))) := (Real.exp_log h3).symm
      _ = Real.exp (3 * ((⌈(1 + η) * (s:ℝ)⌉₊ : ℕ) : ℝ) * Real.log (s:ℝ)) := by rw [h4]
  
  have hSig0 : (0:ℝ) ≤ ∑ S ∈ I.powersetCard (⌈(1 + η) * (s:ℝ)⌉₊),
      ∏ i ∈ S, Real.exp (-(b * Real.sqrt i)) :=
    Finset.sum_nonneg (fun S _ => Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le))
  have h3M : 3 * ((⌈(1 + η) * (s:ℝ)⌉₊ : ℕ) : ℝ) * Real.log (s:ℝ)
      ≤ 6 * (1 + η) * (s:ℝ) * Real.log (s:ℝ) := by
    have h := mul_le_mul_of_nonneg_right hMle
      (by linarith : (0:ℝ) ≤ 3 * Real.log (s:ℝ))
    linarith [h]
  have hkeyX := mul_le_mul_of_nonneg_right hkey hX0
  have hfin : (2/3 + θ) * (s:ℝ) ^ ((3:ℝ)/2)
      + 3 * ((⌈(1 + η) * (s:ℝ)⌉₊ : ℕ) : ℝ) * Real.log (s:ℝ)
      + (-((1 - δ') * (2 * b / 3) * (1 + η) ^ ((3:ℝ)/2) * (s:ℝ) ^ ((3:ℝ)/2)))
      ≤ -(θ * (s:ℝ)) := by linarith [hkeyX, h3M, hrace]
  calc Real.exp ((2/3 + θ) * (s:ℝ) ^ ((3:ℝ)/2)) * V ^ (⌈(1 + η) * (s:ℝ)⌉₊)
        * (∑ S ∈ I.powersetCard (⌈(1 + η) * (s:ℝ)⌉₊),
             ∏ i ∈ S, Real.exp (-(b * Real.sqrt i)))
      ≤ Real.exp ((2/3 + θ) * (s:ℝ) ^ ((3:ℝ)/2))
          * Real.exp (3 * ((⌈(1 + η) * (s:ℝ)⌉₊ : ℕ) : ℝ) * Real.log (s:ℝ))
          * Real.exp (-((1 - δ') * (2 * b / 3) * (1 + η) ^ ((3:ℝ)/2)
              * (s:ℝ) ^ ((3:ℝ)/2))) := by
        refine mul_le_mul ?_ hsum2 hSig0 (by positivity)
        exact mul_le_mul_of_nonneg_left hVM (Real.exp_pos _).le
    _ = Real.exp ((2/3 + θ) * (s:ℝ) ^ ((3:ℝ)/2)
          + 3 * ((⌈(1 + η) * (s:ℝ)⌉₊ : ℕ) : ℝ) * Real.log (s:ℝ)
          + (-((1 - δ') * (2 * b / 3) * (1 + η) ^ ((3:ℝ)/2)
              * (s:ℝ) ^ ((3:ℝ)/2)))) := by
        rw [Real.exp_add, Real.exp_add]
    _ ≤ Real.exp (-(θ * (s:ℝ))) := Real.exp_le_exp.2 hfin

theorem random_pool_selection (P : ℕ → Finset ℕ)
    (hP : IsPools P) (hlog : PoolsLog P) (hbig : PoolsBig P)
    (hesym : ∀ b δ : ℝ, 0 < b → 0 < δ → ∀ᶠ M : ℕ in atTop, ∀ I : Finset ℕ,
      ∑ S ∈ I.powersetCard M, ∏ i ∈ S, Real.exp (-(b * Real.sqrt i))
        ≤ Real.exp (-(1 - δ) * (2 * b / 3) * (M : ℝ) ^ ((3:ℝ)/2)))
    (hdiv : ∀ N m : ℕ, 1 ≤ N → 2 ≤ m →
      ((N.primeFactors.filter (fun p => m ≤ p)).card : ℝ) ≤ Real.log N / Real.log m) :
    ∃ u : ℕ → ℕ, (∀ n, u n ∈ P n) ∧
      ∀ (C : ℕ) (η : ℝ), 1 ≤ C → 0 < η → ∃ (θ : ℝ) (K : ℕ), 0 < θ ∧
        ∀ᶠ s : ℕ in atTop, ∀ N : ℕ,
          (N : ℝ) ≤ Real.exp ((2/3 + θ) * (s : ℝ) ^ ((3:ℝ)/2)) →
          ¬ HasCert u N (Nat.ceil ((1 + η) * (s : ℝ))) K (C * s) :=
by
  classical
  have hne : ∀ n, (P n).Nonempty := hP.1
  
  have hcertN : ∀ (v : ℕ → ℕ) (N N' M K Q : ℕ), HasCert v N M K Q → N ≤ N' →
      HasCert v N' M K Q := by
    rintro v N N' M K Q ⟨n, hn, S, j, h1, h2, h3, h4⟩ hNN
    exact ⟨n, lt_of_lt_of_le hn hNN, S, j, h1, h2, h3, h4⟩
  
  have hcertM : ∀ (v : ℕ → ℕ) (N M M' K Q : ℕ), HasCert v N M K Q → M' ≤ M →
      HasCert v N M' K Q := by
    rintro v N M M' K Q ⟨n, hn, S, j, h1, h2, h3, h4⟩ hMM
    obtain ⟨S', hsub, hcard⟩ := Finset.exists_subset_card_eq (show M' ≤ S.card by omega)
    exact ⟨n, hn, S', j, hcard, fun i hi => h2 i (hsub hi),
      fun i hi => h3 i (hsub hi), fun i hi => h4 i (hsub hi)⟩
  
  have hconst : ∀ k : ℕ, ∃ bk dk θk : ℝ, 0 < bk ∧ bk < 1 ∧ 0 < dk ∧ dk < 1 ∧
      0 < θk ∧ θk ≤ 1/4 ∧
      2/3 + 2*θk ≤ (1 - dk) * (2 * bk / 3) * (1 + 1/((k:ℝ)+1)) ^ ((3:ℝ)/2) := by
    intro k
    have hk1 : (0:ℝ) < (k:ℝ) + 1 := by positivity
    have hη0 : (0:ℝ) < 1/((k:ℝ)+1) := by positivity
    have hbase : (0:ℝ) < 1 + 1/((k:ℝ)+1) := by linarith
    have hbase1 : (1:ℝ) < 1 + 1/((k:ℝ)+1) := by linarith
    obtain ⟨g, hgdef⟩ : ∃ g : ℝ, g = (1 + 1/((k:ℝ)+1)) ^ ((3:ℝ)/8) := ⟨_, rfl⟩
    have hg1 : (1:ℝ) < g := by
      rw [hgdef]
      have h := Real.rpow_lt_rpow (by norm_num : (0:ℝ) ≤ 1) hbase1
        (by norm_num : (0:ℝ) < (3:ℝ)/8)
      simpa using h
    have hg0 : (0:ℝ) < g := lt_trans one_pos hg1
    have hgne : g ≠ 0 := ne_of_gt hg0
    have hgi0 : (0:ℝ) < g⁻¹ := inv_pos.2 hg0
    have hgig : g⁻¹ * g = 1 := inv_mul_cancel₀ hgne
    have hgi1 : g⁻¹ < 1 := by nlinarith [hgig, hgi0, hg1]
    refine ⟨g⁻¹ * g⁻¹, 1 - g⁻¹, min ((g-1)/3) (1/4), mul_pos hgi0 hgi0, by nlinarith,
      by linarith, by linarith, lt_min (by linarith) (by norm_num), min_le_right _ _, ?_⟩
    have h9 : g * (g * g) = (1 + 1/((k:ℝ)+1)) ^ ((9:ℝ)/8) := by
      rw [hgdef, ← Real.rpow_add hbase, ← Real.rpow_add hbase]
      norm_num
    have hsplit : (1 + 1/((k:ℝ)+1)) ^ ((3:ℝ)/2)
        = (1 + 1/((k:ℝ)+1)) ^ ((9:ℝ)/8) * (1 + 1/((k:ℝ)+1)) ^ ((3:ℝ)/8) := by
      rw [← Real.rpow_add hbase]; norm_num
    have hRHS : (1 - (1 - g⁻¹)) * (2 * (g⁻¹ * g⁻¹) / 3) * (1 + 1/((k:ℝ)+1)) ^ ((3:ℝ)/2)
        = 2/3 * g := by
      rw [hsplit, ← h9, ← hgdef]
      field_simp
      ring
    rw [hRHS]
    have hmin : min ((g-1)/3) (1/4) ≤ (g-1)/3 := min_le_left _ _
    linarith
  choose bb dd tt hbb0 hbb1 hdd0 hdd1 htt0 htt1 hkeyk using hconst
  
  have hKex : ∀ k : ℕ, ∃ K : ℕ, ∀ i : ℕ, K < i →
      (∀ p ∈ P i, Real.exp (Real.sqrt i / 2) ≤ (p : ℝ)) ∧
      (∀ m : ℕ, 1 ≤ m →
        (((P i).filter (fun p => p ∣ m)).card : ℝ)
          ≤ Real.log m * ((P i).card : ℝ) * Real.exp (-(bb k * Real.sqrt i))) :=
    fun k => pool_divisor_ratio_bound P hP hlog hbig hdiv (bb k) (hbb0 k) (hbb1 k)
  choose KK hKK using hKex
  
  have hdecay : ∀ k : ℕ, ∀ᶠ s : ℕ in atTop,
      ∀ (I : Finset ℕ) (V : ℝ), 0 ≤ V → V ≤ (s : ℝ) ^ (3:ℕ) →
      Real.exp ((2/3 + tt k) * (s : ℝ) ^ ((3:ℝ)/2)) * V ^ (⌈(1 + 1/((k:ℝ)+1)) * (s:ℝ)⌉₊)
        * (∑ S ∈ I.powersetCard (⌈(1 + 1/((k:ℝ)+1)) * (s:ℝ)⌉₊),
             ∏ i ∈ S, Real.exp (-(bb k * Real.sqrt i)))
        ≤ Real.exp (-(tt k * (s : ℝ))) := by
    intro k
    exact cert_decay_bound (1/((k:ℝ)+1)) (bb k) (dd k) (tt k) (by positivity)
      (hbb0 k) (hdd0 k) (hdd1 k) (htt0 k) (htt1 k) (hkeyk k)
      (hesym (bb k) (dd k) (hbb0 k) (hdd0 k))
  
  have hBmain : ∀ C k : ℕ, ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ᶠ s : ℕ in atTop,
      (MeasureTheory.Measure.infinitePi
          (fun n => (PMF.uniformOfFinset (P n) (hne n)).toMeasure))
        ((fun (C k s : ℕ) => {ω : ℕ → ℕ | (∀ n, ω n ∈ P n) ∧
          HasCert ω (⌊Real.exp ((2/3 + tt k) * (s:ℝ) ^ ((3:ℝ)/2))⌋₊)
            (⌈(1 + 1/((k:ℝ)+1)) * (s:ℝ)⌉₊) (KK k) (C * s)}) C k s)
        ≤ ENNReal.ofReal (r ^ s) := by
    intro C k
    refine ⟨Real.exp (-(tt k)), (Real.exp_pos _).le, ?_, ?_⟩
    · rw [Real.exp_lt_one_iff]; linarith [htt0 k]
    filter_upwards [hdecay k, eventually_ge_atTop (144 * C ^ 2 + 1)] with s hs hsge
    show (MeasureTheory.Measure.infinitePi
          (fun n => (PMF.uniformOfFinset (P n) (hne n)).toMeasure))
        {ω : ℕ → ℕ | (∀ n, ω n ∈ P n) ∧
          HasCert ω (⌊Real.exp ((2/3 + tt k) * (s:ℝ) ^ ((3:ℝ)/2))⌋₊)
            (⌈(1 + 1/((k:ℝ)+1)) * (s:ℝ)⌉₊) (KK k) (C * s)}
        ≤ ENNReal.ofReal ((Real.exp (-(tt k))) ^ s)
    set X : ℝ := (s:ℝ) ^ ((3:ℝ)/2) with hXdef
    set M : ℕ := ⌈(1 + 1/((k:ℝ)+1)) * (s:ℝ)⌉₊ with hMdef
    set N : ℕ := ⌊Real.exp ((2/3 + tt k) * X)⌋₊ with hNdef
    set Q : ℕ := C * s with hQdef
    set L : ℕ := KK k + 4 * s ^ 3 with hLdef
    
    have hs1 : 1 ≤ s := by omega
    have hsR : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs1
    have hsR0 : (0:ℝ) < (s:ℝ) := by linarith
    have hsqrt0 : (0:ℝ) ≤ Real.sqrt (s:ℝ) := Real.sqrt_nonneg _
    have hsqrt : Real.sqrt (s:ℝ) * Real.sqrt (s:ℝ) = (s:ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have hX : X = Real.sqrt (s:ℝ) * (s:ℝ) := by
      rw [hXdef]
      have h2 : ((s:ℝ)) ^ ((3:ℝ)/2) = Real.sqrt (s:ℝ) ^ (3:ℕ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((s:ℝ) ^ ((1:ℝ)/2)) 3,
          ← Real.rpow_mul (by positivity)]
        norm_num
      rw [h2]
      calc Real.sqrt (s:ℝ) ^ (3:ℕ)
          = Real.sqrt (s:ℝ) * (Real.sqrt (s:ℝ) * Real.sqrt (s:ℝ)) := by ring
        _ = Real.sqrt (s:ℝ) * (s:ℝ) := by rw [hsqrt]
    have hX0 : (0:ℝ) ≤ X := by rw [hX]; positivity
    have hX2 : X ^ 2 = (s:ℝ) ^ (3:ℕ) := by
      rw [hX]
      calc (Real.sqrt (s:ℝ) * (s:ℝ)) ^ 2
          = (Real.sqrt (s:ℝ) * Real.sqrt (s:ℝ)) * (s:ℝ) ^ 2 := by ring
        _ = (s:ℝ) * (s:ℝ) ^ 2 := by rw [hsqrt]
        _ = (s:ℝ) ^ (3:ℕ) := by ring
    
    have hC0 : (0:ℝ) ≤ (C:ℝ) := Nat.cast_nonneg _
    have h144 : (144:ℝ) * (C:ℝ) ^ 2 ≤ (s:ℝ) := by
      have hnat : 144 * C ^ 2 ≤ s := by omega
      exact_mod_cast hnat
    have hCs : 12 * (C:ℝ) ≤ Real.sqrt (s:ℝ) := by
      by_contra hcon
      push_neg at hcon
      have hp1 : (0:ℝ) < 12 * (C:ℝ) - Real.sqrt (s:ℝ) := by linarith
      have hp2 : (0:ℝ) < 12 * (C:ℝ) + Real.sqrt (s:ℝ) := by linarith
      nlinarith [mul_pos hp1 hp2, hsqrt, h144]
    have hCle : (C:ℝ) ≤ Real.sqrt (s:ℝ) := by linarith
    
    have hd1 : (N:ℝ) ≤ Real.exp ((2/3 + tt k) * X) := by
      rw [hNdef]; exact Nat.floor_le (Real.exp_pos _).le
    have hd1b : (N:ℝ) ≤ Real.exp ((11/12) * X) := by
      refine le_trans hd1 (Real.exp_le_exp.2 ?_)
      nlinarith [htt1 k, hX0]
    
    have hQR : (Q:ℝ) = (C:ℝ) * (s:ℝ) := by rw [hQdef]; push_cast; ring
    have hQX : (Q:ℝ) ≤ X / 12 := by
      rw [hQR, hX]
      nlinarith [mul_le_mul_of_nonneg_right hCs (le_of_lt hsR0)]
    
    have hd2 : (N:ℝ) + (Q:ℝ) ≤ Real.exp X := by
      have e3 : (1:ℝ) ≤ Real.exp ((11/12) * X) := by
        have h := Real.exp_le_exp.2 (show (0:ℝ) ≤ (11/12) * X by linarith)
        simpa using h
      have e2 : 1 + X/12 ≤ Real.exp (X/12) := by
        have h := Real.add_one_le_exp (X/12); linarith
      have e4 : Real.exp ((11/12) * X) * (1 + X/12) ≤ Real.exp X := by
        calc Real.exp ((11/12) * X) * (1 + X/12)
            ≤ Real.exp ((11/12) * X) * Real.exp (X/12) :=
              mul_le_mul_of_nonneg_left e2 (Real.exp_pos _).le
          _ = Real.exp X := by rw [← Real.exp_add]; congr 1; ring
      have e6 : Real.exp ((11/12) * X) + X/12 ≤ Real.exp ((11/12) * X) * (1 + X/12) := by
        nlinarith [mul_nonneg (sub_nonneg.2 e3) (show (0:ℝ) ≤ X/12 by linarith)]
      linarith
    
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by
      have hNn : 1 ≤ N := by
        rw [hNdef]
        refine Nat.le_floor ?_
        push_cast
        have h := Real.exp_le_exp.2
          (show (0:ℝ) ≤ (2/3 + tt k) * X by nlinarith [htt0 k, hX0])
        simpa using h
      exact_mod_cast hNn
    have hQ0 : (0:ℝ) ≤ (Q:ℝ) := Nat.cast_nonneg _
    have hNQ1 : (1:ℝ) ≤ (N:ℝ) + (Q:ℝ) := by linarith
    set V0 : ℝ := Real.log ((N:ℝ) + (Q:ℝ)) with hV0def
    have hV0nn : (0:ℝ) ≤ V0 := Real.log_nonneg hNQ1
    have hV0X : V0 ≤ X := by
      have h1 : Real.log ((N:ℝ) + (Q:ℝ)) ≤ Real.log (Real.exp X) :=
        Real.log_le_log (by linarith) hd2
      rw [Real.log_exp] at h1
      exact h1
    
    have hfil : ∀ i : ℕ, KK k < i → ∀ m : ℕ, 1 ≤ m → m < N + Q →
        (((P i).filter (fun p => p ∣ m)).card : ℝ)
          ≤ (V0 * Real.exp (-(bb k * Real.sqrt i))) * ((P i).card : ℝ) := by
      intro i hi m hm1 hm2
      have hb := (hKK k i hi).2 m hm1
      have hmR : (m:ℝ) ≤ (N:ℝ) + (Q:ℝ) := by
        have h : ((m:ℕ):ℝ) ≤ ((N + Q : ℕ) : ℝ) := by exact_mod_cast le_of_lt hm2
        push_cast at h; linarith
      have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
      have hlogm : Real.log (m:ℝ) ≤ V0 := Real.log_le_log hm0 hmR
      have hcard : (0:ℝ) ≤ ((P i).card : ℝ) := Nat.cast_nonneg _
      have hexp : (0:ℝ) < Real.exp (-(bb k * Real.sqrt i)) := Real.exp_pos _
      nlinarith [hb, mul_nonneg (mul_nonneg (sub_nonneg.2 hlogm) hcard) hexp.le]
    
    have hout : ∀ i : ℕ, L < i → ∀ p ∈ P i, N + Q ≤ p := by
      intro i hi p hp
      have hiK : KK k < i := by omega
      have hexp := (hKK k i hiK).1 p hp
      have hi4 : 4 * s ^ 3 < i := by omega
      have hi4R : 4 * X ^ 2 < (i:ℝ) := by
        have h : ((4 * s ^ 3 : ℕ) : ℝ) < (i:ℝ) := by exact_mod_cast hi4
        push_cast at h
        rw [hX2]
        push_cast
        linarith
      have hii : Real.sqrt (i:ℝ) * Real.sqrt (i:ℝ) = (i:ℝ) :=
        Real.mul_self_sqrt (by positivity)
      have hsq : 2 * X < Real.sqrt (i:ℝ) := by
        by_contra hcon
        push_neg at hcon
        have h0 : (0:ℝ) ≤ Real.sqrt (i:ℝ) := Real.sqrt_nonneg _
        nlinarith [mul_nonneg (sub_nonneg.2 hcon)
          (show (0:ℝ) ≤ 2 * X + Real.sqrt (i:ℝ) by linarith), hii, hi4R]
      have hlt : Real.exp X < Real.exp (Real.sqrt (i:ℝ) / 2) :=
        Real.exp_lt_exp.2 (by linarith)
      have hpR : (N:ℝ) + (Q:ℝ) < (p:ℝ) := lt_of_le_of_lt hd2 (lt_of_lt_of_le hlt hexp)
      have hcast : ((N + Q : ℕ) : ℝ) < (p:ℝ) := by push_cast; linarith
      have hlt2 : N + Q < p := by exact_mod_cast hcast
      omega
    have hw0 : ∀ i : ℕ, (0:ℝ) ≤ V0 * Real.exp (-(bb k * Real.sqrt i)) :=
      fun i => mul_nonneg hV0nn (Real.exp_pos _).le
    
    have hmeas := cert_event_measure_le P hne N M (KK k) L Q
      (fun i => V0 * Real.exp (-(bb k * Real.sqrt i))) hw0 hfil hout
    refine le_trans hmeas (ENNReal.ofReal_le_ofReal ?_)
    
    have hVnn : (0:ℝ) ≤ (Q:ℝ) * V0 := mul_nonneg hQ0 hV0nn
    have hVle : (Q:ℝ) * V0 ≤ (s:ℝ) ^ (3:ℕ) := by
      calc (Q:ℝ) * V0 ≤ (Q:ℝ) * X := mul_le_mul_of_nonneg_left hV0X hQ0
        _ = ((C:ℝ) * (s:ℝ)) * (Real.sqrt (s:ℝ) * (s:ℝ)) := by rw [hQR, hX]
        _ ≤ (Real.sqrt (s:ℝ) * (s:ℝ)) * (Real.sqrt (s:ℝ) * (s:ℝ)) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right hCle (le_of_lt hsR0)
        _ = (s:ℝ) ^ (3:ℕ) := by
            calc (Real.sqrt (s:ℝ) * (s:ℝ)) * (Real.sqrt (s:ℝ) * (s:ℝ))
                = (Real.sqrt (s:ℝ) * Real.sqrt (s:ℝ)) * ((s:ℝ) * (s:ℝ)) := by ring
              _ = (s:ℝ) * ((s:ℝ) * (s:ℝ)) := by rw [hsqrt]
              _ = (s:ℝ) ^ (3:ℕ) := by ring
    have hdec := hs (Finset.Ioc (KK k) L) ((Q:ℝ) * V0) hVnn hVle
    set SI : ℝ := ∑ S ∈ (Finset.Ioc (KK k) L).powersetCard M,
      ∏ i ∈ S, Real.exp (-(bb k * Real.sqrt i)) with hSIdef
    have hSI0 : (0:ℝ) ≤ SI := by
      rw [hSIdef]
      exact Finset.sum_nonneg (fun S _ =>
        Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le))
    have hsum : (∑ S ∈ (Finset.Ioc (KK k) L).powersetCard M,
        ∏ i ∈ S, (V0 * Real.exp (-(bb k * Real.sqrt i)))) = V0 ^ M * SI := by
      rw [hSIdef, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro S hS
      rw [Finset.prod_mul_distrib, Finset.prod_const, (Finset.mem_powersetCard.1 hS).2]
    have hrs : (Real.exp (-(tt k))) ^ s = Real.exp (-(tt k * (s:ℝ))) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have hnn : (0:ℝ) ≤ ((Q:ℝ) * V0) ^ M * SI := mul_nonneg (pow_nonneg hVnn M) hSI0
    show (N:ℝ) * (Q:ℝ) ^ M * (∑ S ∈ (Finset.Ioc (KK k) L).powersetCard M,
        ∏ i ∈ S, (V0 * Real.exp (-(bb k * Real.sqrt i))))
        ≤ (Real.exp (-(tt k))) ^ s
    rw [hsum, hrs]
    calc (N:ℝ) * (Q:ℝ) ^ M * (V0 ^ M * SI)
        = (N:ℝ) * (((Q:ℝ) * V0) ^ M * SI) := by rw [mul_pow]; ring
      _ ≤ Real.exp ((2/3 + tt k) * X) * (((Q:ℝ) * V0) ^ M * SI) :=
          mul_le_mul_of_nonneg_right hd1 hnn
      _ = Real.exp ((2/3 + tt k) * X) * ((Q:ℝ) * V0) ^ M * SI := by ring
      _ ≤ Real.exp (-(tt k * (s:ℝ))) := hdec
  
  obtain ⟨u, humem, huavoid⟩ := exists_pool_point_avoiding P hne
    (fun (C k s : ℕ) => {ω : ℕ → ℕ | (∀ n, ω n ∈ P n) ∧
      HasCert ω (⌊Real.exp ((2/3 + tt k) * (s:ℝ) ^ ((3:ℝ)/2))⌋₊)
        (⌈(1 + 1/((k:ℝ)+1)) * (s:ℝ)⌉₊) (KK k) (C * s)}) hBmain
  refine ⟨u, humem, ?_⟩
  intro C η hC hη
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hη
  refine ⟨tt k, KK k, htt0 k, ?_⟩
  filter_upwards [huavoid C k, eventually_ge_atTop 1] with s hsav hs1
  intro N hN hcert
  apply hsav
  refine ⟨humem, ?_⟩
  have hNle : N ≤ ⌊Real.exp ((2/3 + tt k) * (s:ℝ) ^ ((3:ℝ)/2))⌋₊ := Nat.le_floor hN
  have hstep1 := hcertN u N (⌊Real.exp ((2/3 + tt k) * (s:ℝ) ^ ((3:ℝ)/2))⌋₊)
    (Nat.ceil ((1 + η) * (s : ℝ))) (KK k) (C * s) hcert hNle
  have hmono : ⌈(1 + 1/((k:ℝ)+1)) * (s:ℝ)⌉₊ ≤ Nat.ceil ((1 + η) * (s : ℝ)) := by
    refine Nat.ceil_mono ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg s)
  exact hcertM u (⌊Real.exp ((2/3 + tt k) * (s:ℝ) ^ ((3:ℝ)/2))⌋₊)
    (Nat.ceil ((1 + η) * (s : ℝ))) (⌈(1 + 1/((k:ℝ)+1)) * (s:ℝ)⌉₊) (KK k) (C * s)
    hstep1 hmono

theorem card_Ioc_filter_dvd (a b d : ℕ) (hab : a ≤ b) :
    ((Finset.Ioc a b).filter (fun m => d ∣ m)).card = b / d - a / d :=
by
  classical
  
  have hsplit : Finset.Ioc 0 a ∪ Finset.Ioc a b = Finset.Ioc 0 b :=
    Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le a) hab
  
  have hdisj : Disjoint (Finset.Ioc 0 a) (Finset.Ioc a b) := by
    rw [Finset.disjoint_left]
    intro m hm hm'
    rw [Finset.mem_Ioc] at hm hm'
    omega
  
  have hcard :
      ((Finset.Ioc 0 b).filter (fun m => d ∣ m)).card
        = ((Finset.Ioc 0 a).filter (fun m => d ∣ m)).card
          + ((Finset.Ioc a b).filter (fun m => d ∣ m)).card := by
    rw [← hsplit, Finset.filter_union,
      Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)]
  
  rw [Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div] at hcard
  
  omega

theorem sieve_interval_count (v : ℕ → ℕ) (hv : ∀ i, 2 ≤ v i)
    (hvcop : ∀ i j, i ≠ j → Nat.Coprime (v i) (v j)) (K a L : ℕ) :
    |((((Finset.Ioc a (a + L)).filter (fun m => ∀ i < K, ¬ v i ∣ m)).card : ℝ))
        - (L : ℝ) * ∏ i ∈ Finset.range K, (1 - 1 / (v i : ℝ))| ≤ (2:ℝ) ^ K - 1 :=
by
  classical
  
  have hfac : ∀ i : ℕ, (0:ℝ) ≤ 1 - 1 / (v i : ℝ) ∧ 1 - 1 / (v i : ℝ) ≤ 1 := by
    intro i
    have h2 : (2:ℝ) ≤ (v i : ℝ) := by exact_mod_cast hv i
    have hpos : (0:ℝ) < (v i : ℝ) := by linarith
    have hle : 1 / (v i : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
    have h0 : (0:ℝ) < 1 / (v i : ℝ) := by positivity
    constructor <;> linarith
  have hP : ∀ n : ℕ, (0:ℝ) ≤ ∏ i ∈ Finset.range n, (1 - 1 / (v i : ℝ)) ∧
      ∏ i ∈ Finset.range n, (1 - 1 / (v i : ℝ)) ≤ 1 := by
    intro n
    exact ⟨Finset.prod_nonneg (fun i _ => (hfac i).1),
      Finset.prod_le_one (fun i _ => (hfac i).1) (fun i _ => (hfac i).2)⟩
  
  have key : ∀ (s : Finset ℕ) (n : ℕ),
      (s.filter (fun m => ∀ i < n + 1, ¬ v i ∣ m)).card
        + (s.filter (fun m => (∀ i < n, ¬ v i ∣ m) ∧ v n ∣ m)).card
        = (s.filter (fun m => ∀ i < n, ¬ v i ∣ m)).card := by
    intro s n
    have h1 : s.filter (fun m => ∀ i < n + 1, ¬ v i ∣ m)
        = (s.filter (fun m => ∀ i < n, ¬ v i ∣ m)).filter (fun m => ¬ v n ∣ m) := by
      ext m
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hm, h⟩
        exact ⟨⟨hm, fun i hi => h i (by omega)⟩, h n (by omega)⟩
      · rintro ⟨⟨hm, h⟩, hn⟩
        refine ⟨hm, fun i hi => ?_⟩
        rcases (by omega : i < n ∨ i = n) with hi' | rfl
        · exact h i hi'
        · exact hn
    have h2 : s.filter (fun m => (∀ i < n, ¬ v i ∣ m) ∧ v n ∣ m)
        = (s.filter (fun m => ∀ i < n, ¬ v i ∣ m)).filter (fun m => v n ∣ m) := by
      ext m
      simp only [Finset.mem_filter]
      tauto
    rw [h1, h2, add_comm]
    exact Finset.card_filter_add_card_filter_not _
  
  have hbij : ∀ (n a b : ℕ), (∀ i, i < n → Nat.Coprime (v i) (v n)) →
      ((Finset.Ioc a b).filter (fun m => (∀ i < n, ¬ v i ∣ m) ∧ v n ∣ m)).card
        = ((Finset.Ioc (a / v n) (b / v n)).filter (fun m => ∀ i < n, ¬ v i ∣ m)).card := by
    intro n a b hcop
    have hw : 0 < v n := lt_of_lt_of_le (by norm_num) (hv n)
    refine Finset.card_nbij' (fun m => m / v n) (fun m => m * v n) ?_ ?_ ?_ ?_
    · intro m hm
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at hm ⊢
      obtain ⟨⟨hlo, hhi⟩, hsieve, hdvd⟩ := hm
      have hmw : m / v n * v n = m := Nat.div_mul_cancel hdvd
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul hw, hmw]; exact hlo
      · rw [Nat.le_div_iff_mul_le hw, hmw]; exact hhi
      · intro i hi hd'
        have hd2 : v i ∣ m / v n * v n := dvd_mul_of_dvd_left hd' (v n)
        rw [hmw] at hd2
        exact hsieve i hi hd2
    · intro m hm
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at hm ⊢
      obtain ⟨⟨hlo, hhi⟩, hsieve⟩ := hm
      refine ⟨⟨?_, ?_⟩, ?_, dvd_mul_left (v n) m⟩
      · exact (Nat.div_lt_iff_lt_mul hw).mp hlo
      · exact (Nat.le_div_iff_mul_le hw).mp hhi
      · intro i hi hd'
        exact hsieve i hi ((hcop i hi).dvd_of_dvd_mul_right hd')
    · intro m hm
      simp only [Finset.mem_coe, Finset.mem_filter] at hm
      exact Nat.div_mul_cancel hm.2.2
    · intro m _
      exact Nat.mul_div_cancel m hw
  
  have hdiv : ∀ (x l d : ℕ), 0 < d →
      |(((x + l) / d : ℕ) : ℝ) - ((x / d : ℕ) : ℝ) - (l : ℝ) / (d : ℝ)| ≤ 1 := by
    intro x l d hd
    have hd0 : (0:ℝ) < (d : ℝ) := by exact_mod_cast hd
    have e1 : (d : ℝ) * ((x / d : ℕ) : ℝ) + ((x % d : ℕ) : ℝ) = (x : ℝ) := by
      exact_mod_cast Nat.div_add_mod x d
    have e2 : (d : ℝ) * (((x + l) / d : ℕ) : ℝ) + (((x + l) % d : ℕ) : ℝ)
        = (x : ℝ) + (l : ℝ) := by
      have h := Nat.div_add_mod (x + l) d
      exact_mod_cast h
    have m1 : ((x % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast Nat.mod_lt x hd
    have m2 : (((x + l) % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast Nat.mod_lt (x + l) hd
    have n1 : (0:ℝ) ≤ ((x % d : ℕ) : ℝ) := Nat.cast_nonneg _
    have n2 : (0:ℝ) ≤ (((x + l) % d : ℕ) : ℝ) := Nat.cast_nonneg _
    have hl : (l : ℝ) = (d : ℝ) * ((l : ℝ) / (d : ℝ)) := by
      field_simp
    rw [abs_le]
    constructor
    · nlinarith [e1, e2, m1, m2, n1, n2, hl, hd0]
    · nlinarith [e1, e2, m1, m2, n1, n2, hl, hd0]
  
  induction K generalizing a L with
  | zero =>
    have hzero : ∀ m : ℕ, (∀ i < 0, ¬ v i ∣ m) := fun m i hi => absurd hi (Nat.not_lt_zero i)
    simp [hzero, Nat.card_Ioc]
  | succ n ih =>
    have hw : 0 < v n := lt_of_lt_of_le (by norm_num) (hv n)
    obtain ⟨L', hL'⟩ : ∃ L' : ℕ, (a + L) / v n = a / v n + L' := by
      refine ⟨(a + L) / v n - a / v n, ?_⟩
      have hle : a / v n ≤ (a + L) / v n := Nat.div_le_div_right (Nat.le_add_right a L)
      omega
    have e1 := key (Finset.Ioc a (a + L)) n
    have e2 := hbij n a (a + L) (fun i hi => hvcop i n (by omega))
    rw [hL'] at e2
    rw [e2] at e1
    have e1R : (((Finset.Ioc a (a + L)).filter (fun m => ∀ i < n + 1, ¬ v i ∣ m)).card : ℝ)
        = (((Finset.Ioc a (a + L)).filter (fun m => ∀ i < n, ¬ v i ∣ m)).card : ℝ)
          - (((Finset.Ioc (a / v n) (a / v n + L')).filter
              (fun m => ∀ i < n, ¬ v i ∣ m)).card : ℝ) := by
      have hc := congrArg (fun k : ℕ => (k : ℝ)) e1
      push_cast at hc
      linarith
    have hX := ih a L
    have hY := ih (a / v n) L'
    have h3 := hdiv a L (v n) hw
    rw [hL'] at h3
    have h3' : |(L' : ℝ) - (L : ℝ) / (v n : ℝ)| ≤ 1 := by
      have heq : (((a / v n + L' : ℕ)) : ℝ) - ((a / v n : ℕ) : ℝ) - (L : ℝ) / (v n : ℝ)
          = (L' : ℝ) - (L : ℝ) / (v n : ℝ) := by push_cast; ring
      rwa [heq] at h3
    obtain ⟨hp0, hp1⟩ := hP n
    obtain ⟨hX1, hX2⟩ := abs_le.mp hX
    obtain ⟨hY1, hY2⟩ := abs_le.mp hY
    obtain ⟨hZ1, hZ2⟩ := abs_le.mp h3'
    rw [Finset.prod_range_succ]
    have hid : (((Finset.Ioc a (a + L)).filter (fun m => ∀ i < n + 1, ¬ v i ∣ m)).card : ℝ)
          - (L : ℝ) * ((∏ i ∈ Finset.range n, (1 - 1 / (v i : ℝ))) * (1 - 1 / (v n : ℝ)))
        = ((((Finset.Ioc a (a + L)).filter (fun m => ∀ i < n, ¬ v i ∣ m)).card : ℝ)
              - (L : ℝ) * ∏ i ∈ Finset.range n, (1 - 1 / (v i : ℝ)))
          - ((((Finset.Ioc (a / v n) (a / v n + L')).filter
                (fun m => ∀ i < n, ¬ v i ∣ m)).card : ℝ)
              - (L' : ℝ) * ∏ i ∈ Finset.range n, (1 - 1 / (v i : ℝ)))
          - ((L' : ℝ) - (L : ℝ) / (v n : ℝ)) * ∏ i ∈ Finset.range n, (1 - 1 / (v i : ℝ)) := by
      rw [e1R]; ring
    have hZa : ((L' : ℝ) - (L : ℝ) / (v n : ℝ))
        * ∏ i ∈ Finset.range n, (1 - 1 / (v i : ℝ)) ≤ 1 := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - ((L' : ℝ) - (L : ℝ) / (v n : ℝ))) hp0]
    have hZb : -1 ≤ ((L' : ℝ) - (L : ℝ) / (v n : ℝ))
        * ∏ i ∈ Finset.range n, (1 - 1 / (v i : ℝ)) := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ ((L' : ℝ) - (L : ℝ) / (v n : ℝ)) + 1) hp0]
    rw [hid, abs_le, pow_succ]
    constructor <;> linarith

theorem nth_gap_covered (u : ℕ → ℕ) (hinf : (ASet u).Infinite) (k m : ℕ)
    (h1 : A u k < m) (h2 : m < A u (k + 1)) : ∃ i, u i ∣ m :=
by
  
  by_contra hcon
  push_neg at hcon
  
  
  have hp : (setOf fun a => a ∈ ASet u).Infinite := hinf
  
  have hmem : m ∈ Set.range (Nat.nth (fun a => a ∈ ASet u)) := by
    rw [Nat.range_nth_of_infinite hp]
    exact hcon
  obtain ⟨j, hj⟩ := hmem
  
  unfold A at h1 h2
  rw [← hj] at h1 h2
  
  have hkj : k < j := (Nat.nth_lt_nth hp).1 h1
  have hjk : j < k + 1 := (Nat.nth_lt_nth hp).1 h2
  
  omega

theorem tprod_le_prod_range (u : ℕ → ℕ) (hu2 : ∀ i, 2 ≤ u i)
    (hsum : Summable (fun n => 1 / (u n : ℝ))) (m : ℕ) :
    (∏' i : ℕ, (1 - 1 / (u i : ℝ))) ≤ ∏ i ∈ Finset.range m, (1 - 1 / (u i : ℝ)) :=
by
  
  have hu2R : ∀ i, (2:ℝ) ≤ (u i : ℝ) := fun i => by exact_mod_cast hu2 i
  have huposR : ∀ i, (0:ℝ) < (u i : ℝ) := fun i => by linarith [hu2R i]
  have hhalf : ∀ i, 1 / (u i : ℝ) ≤ 1 / 2 :=
    fun i => one_div_le_one_div_of_le (by norm_num) (hu2R i)
  have h0 : ∀ i, (0:ℝ) ≤ 1 - 1 / (u i : ℝ) := fun i => by linarith [hhalf i]
  have h1 : ∀ i, 1 - 1 / (u i : ℝ) ≤ 1 := fun i => by
    have hp : (0:ℝ) < 1 / (u i : ℝ) := div_pos one_pos (huposR i)
    linarith
  
  
  
  have hanti : ∀ n : ℕ, m ≤ n →
      ∏ i ∈ Finset.range n, (1 - 1 / (u i : ℝ))
        ≤ ∏ i ∈ Finset.range m, (1 - 1 / (u i : ℝ)) := by
    intro n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih =>
        rw [Finset.prod_range_succ]
        have hnn : (0:ℝ) ≤ ∏ i ∈ Finset.range n, (1 - 1 / (u i : ℝ)) :=
          Finset.prod_nonneg (fun i _ => h0 i)
        exact le_trans (mul_le_of_le_one_right hnn (h1 n)) ih
  
  have hmul : Multipliable (fun i : ℕ => 1 - 1 / (u i : ℝ)) := by
    have h : Multipliable (fun i : ℕ => 1 + -(1 / (u i : ℝ))) :=
      Real.multipliable_one_add_of_summable hsum.neg
    have heq : (fun i : ℕ => 1 + -(1 / (u i : ℝ)))
        = fun i : ℕ => 1 - 1 / (u i : ℝ) := by
      funext i; ring
    rwa [heq] at h
  
  have htend : Filter.Tendsto (fun n => ∏ i ∈ Finset.range n, (1 - 1 / (u i : ℝ)))
      atTop (nhds (∏' i : ℕ, (1 - 1 / (u i : ℝ)))) := hmul.hasProd.tendsto_prod_nat
  
  
  refine le_of_tendsto htend ?_
  filter_upwards [eventually_ge_atTop m] with n hn
  exact hanti n hn

theorem certificate_of_large_gap (u : ℕ → ℕ) (hmono : StrictMono u) (h2 : 2 ≤ u 0)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (u i) (u j))
    (hsum : Summable (fun n => 1 / (u n : ℝ)))
    (hinf : (ASet u).Infinite)
    (hD : 0 < ∏' i : ℕ, (1 - 1 / (u i : ℝ)))
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (Cc : ℕ) (hCc1 : 1 ≤ Cc) (hCc : (2:ℝ) / (∏' i : ℕ, (1 - 1 / (u i : ℝ))) ≤ (Cc : ℝ))
    (K₀ : ℕ) :
    ∃ K : ℕ, K₀ ≤ K ∧ ∀ᶠ x : ℕ in atTop, ∀ k : ℕ, A u k < x →
      (1 + ε) * (t u x : ℝ) * (∏' i : ℕ, (1 - 1 / (u i : ℝ)))⁻¹
          ≤ (A u (k + 1) : ℝ) - (A u k : ℝ) →
      HasCert u x (Nat.ceil ((1 + ε/6) * (t u x : ℝ))) K (Cc * t u x) :=
by
  classical
  
  have hu2 : ∀ i, 2 ≤ u i := fun i => le_trans h2 (hmono.monotone (Nat.zero_le i))
  have hu2R : ∀ i, (2:ℝ) ≤ (u i : ℝ) := fun i => by exact_mod_cast hu2 i
  have huposR : ∀ i, (0:ℝ) < (u i : ℝ) := fun i => by linarith [hu2R i]
  have hfpos : ∀ i, (0:ℝ) < 1 / (u i : ℝ) := fun i => div_pos one_pos (huposR i)
  
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, ∏' i : ℕ, (1 - 1 / (u i : ℝ)) = D := ⟨_, rfl⟩
  rw [hDdef] at hD hCc ⊢
  have hDne : D ≠ 0 := ne_of_gt hD
  have hDinvpos : (0:ℝ) < D⁻¹ := inv_pos.2 hD
  have hDmul : D * D⁻¹ = 1 := mul_inv_cancel₀ hDne
  have hD1 : D ≤ 1 := by
    have h := tprod_le_prod_range u hu2 hsum 0
    rw [hDdef] at h
    simpa using h
  have hDinv1 : (1:ℝ) ≤ D⁻¹ := by
    by_contra hcon
    push_neg at hcon
    nlinarith [hDmul, hD, hD1]
  
  have hpow_le : ∀ m : ℕ, 2 ^ m ≤ ∏ i ∈ Finset.range m, u i := by
    intro m
    calc 2 ^ m = 2 ^ (Finset.range m).card := by rw [Finset.card_range]
      _ ≤ ∏ i ∈ Finset.range m, u i :=
          Finset.pow_card_le_prod _ _ _ (fun i _ => hu2 i)
  have hbdd : ∀ y : ℕ, BddAbove {k | ∏ i ∈ Finset.range k, u i ≤ y} := by
    intro y
    refine ⟨y, ?_⟩
    intro k hk
    have hk1 : k < 2 ^ k := Nat.lt_two_pow_self
    have hk2 : (2:ℕ) ^ k ≤ y := le_trans (hpow_le k) hk
    omega
  have hT3 : ∀ m y : ℕ, (∏ i ∈ Finset.range m, u i) ≤ y → m ≤ t u y :=
    fun m y hy => le_csSup (hbdd y) hy
  have hTtend : Filter.Tendsto (fun y : ℕ => t u y) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro m
    filter_upwards [eventually_ge_atTop (∏ i ∈ Finset.range m, u i)] with y hy
    exact hT3 m y hy
  
  have htend0 : Filter.Tendsto (fun i : ℕ => ∑' k : ℕ, (1:ℝ) / (u (k + i) : ℝ))
      atTop (nhds 0) := tendsto_sum_nat_add (fun n : ℕ => (1:ℝ) / (u n : ℝ))
  have hEv : ∀ᶠ j : ℕ in atTop, (∑' k : ℕ, (1:ℝ) / (u (k + j) : ℝ)) ≤ ε * D / 8 :=
    htend0.eventually_le_const (div_pos (mul_pos hε0 hD) (by norm_num))
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hEv
  obtain ⟨K, hKK₀, hKJ⟩ : ∃ K : ℕ, K₀ ≤ K ∧ J ≤ K + 1 :=
    ⟨max K₀ (J + 1), le_max_left _ _, by have := le_max_right K₀ (J + 1); omega⟩
  refine ⟨K, hKK₀, ?_⟩
  obtain ⟨σ, hσdef⟩ : ∃ s : ℝ, (∑' k : ℕ, (1:ℝ) / (u (k + (K + 1)) : ℝ)) = s := ⟨_, rfl⟩
  have hσle : σ ≤ ε * D / 8 := by
    rw [← hσdef]; exact hJ (K + 1) hKJ
  have hσnn : (0:ℝ) ≤ σ := by
    rw [← hσdef]; exact tsum_nonneg (fun k => (hfpos (k + (K + 1))).le)
  have hsplit : (∑ i ∈ Finset.range (K + 1), (1:ℝ) / (u i : ℝ)) + σ
      = ∑' i : ℕ, (1:ℝ) / (u i : ℝ) := by
    rw [← hσdef]; exact hsum.sum_add_tsum_nat_add (K + 1)
  have hsumS : ∀ T : Finset ℕ, (∀ i ∈ T, K < i) →
      ∑ i ∈ T, (1:ℝ) / (u i : ℝ) ≤ σ := by
    intro T hT
    have hdisj : Disjoint T (Finset.range (K + 1)) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      have h1 := hT a ha
      have h3 := Finset.mem_range.1 hb
      omega
    have hun : ∑ i ∈ T ∪ Finset.range (K + 1), (1:ℝ) / (u i : ℝ)
        = ∑ i ∈ T, (1:ℝ) / (u i : ℝ) + ∑ i ∈ Finset.range (K + 1), (1:ℝ) / (u i : ℝ) :=
      Finset.sum_union hdisj
    have hle : ∑ i ∈ T ∪ Finset.range (K + 1), (1:ℝ) / (u i : ℝ)
        ≤ ∑' i : ℕ, (1:ℝ) / (u i : ℝ) :=
      hsum.sum_le_tsum _ (fun i _ => (hfpos i).le)
    linarith
  
  filter_upwards [hTtend.eventually (eventually_ge_atTop
      (⌈(2:ℝ)/ε⌉₊ + ⌈48 * (2 + (2:ℝ) ^ (K + 1)) / (7 * ε)⌉₊ + 1))] with x hx
  intro k hk hgap
  have hTnat1 : ⌈(2:ℝ)/ε⌉₊ ≤ t u x := by omega
  have hTnat2 : ⌈48 * (2 + (2:ℝ) ^ (K + 1)) / (7 * ε)⌉₊ ≤ t u x := by omega
  have hTnat3 : 1 ≤ t u x := by omega
  have hTnn : (0:ℝ) ≤ (t u x : ℝ) := Nat.cast_nonneg _
  have hA1 : (2:ℝ)/ε ≤ (t u x : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hTnat1)
  have hA2 : 48 * (2 + (2:ℝ) ^ (K + 1)) / (7 * ε) ≤ (t u x : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hTnat2)
  have hA3 : (1:ℝ) ≤ (t u x : ℝ) := by exact_mod_cast hTnat3
  have hB1 : (1:ℝ) ≤ ε/2 * (t u x : ℝ) := by
    rw [div_le_iff₀ hε0] at hA1; linarith
  have hB2 : (2:ℝ) + (2:ℝ) ^ (K + 1) ≤ 7 * ε / 48 * (t u x : ℝ) := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 7 * ε)] at hA2; linarith
  
  have hynn : (0:ℝ) ≤ (1 + ε/2) * (t u x : ℝ) * D⁻¹ :=
    mul_nonneg (mul_nonneg (by linarith) hTnn) hDinvpos.le
  obtain ⟨L, hLdef⟩ : ∃ L : ℕ, ⌊(1 + ε/2) * (t u x : ℝ) * D⁻¹⌋₊ = L := ⟨_, rfl⟩
  have hLle : (L:ℝ) ≤ (1 + ε/2) * (t u x : ℝ) * D⁻¹ := by
    rw [← hLdef]; exact Nat.floor_le hynn
  have hLgt : (1 + ε/2) * (t u x : ℝ) * D⁻¹ - 1 < (L:ℝ) := by
    rw [← hLdef]; exact Nat.sub_one_lt_floor _
  have hLnn : (0:ℝ) ≤ (L:ℝ) := Nat.cast_nonneg _
  have hq : (1:ℝ) ≤ (1 + ε/2) * D⁻¹ := by
    nlinarith [mul_nonneg (le_of_lt (half_pos hε0)) hDinvpos.le, hDinv1]
  have hyT : (t u x : ℝ) ≤ (1 + ε/2) * (t u x : ℝ) * D⁻¹ := by
    nlinarith [mul_nonneg hTnn (sub_nonneg.2 hq)]
  
  have hgapL : ((A u k : ℕ) : ℝ) + (L:ℝ) < (A u (k + 1) : ℝ) := by
    have hh : ε/2 * (t u x : ℝ) ≤ ε/2 * (t u x : ℝ) * D⁻¹ := by
      nlinarith [mul_nonneg (mul_nonneg (le_of_lt (half_pos hε0)) hTnn)
        (sub_nonneg.2 hDinv1)]
    linarith
  have hgapN : A u k + L < A u (k + 1) := by exact_mod_cast hgapL
  
  have hDinvCc : D⁻¹ ≤ (Cc:ℝ)/2 := by
    have hh : D⁻¹ = (2/D)/2 := by field_simp
    rw [hh]; linarith
  have hCcnn : (0:ℝ) ≤ (Cc:ℝ) := Nat.cast_nonneg _
  have hLCc : (L:ℝ) ≤ (Cc:ℝ) * (t u x : ℝ) := by
    have s1 : (1 + ε/2) * (t u x : ℝ) * D⁻¹ ≤ (3/2) * (t u x : ℝ) * D⁻¹ := by
      have hb : (1 + ε/2) * (t u x : ℝ) ≤ (3/2) * (t u x : ℝ) := by nlinarith
      exact mul_le_mul_of_nonneg_right hb hDinvpos.le
    have s2 : (3/2) * (t u x : ℝ) * D⁻¹ ≤ (3/2) * (t u x : ℝ) * ((Cc:ℝ)/2) :=
      mul_le_mul_of_nonneg_left hDinvCc (by linarith)
    have s3 : (3/2) * (t u x : ℝ) * ((Cc:ℝ)/2) ≤ (Cc:ℝ) * (t u x : ℝ) := by
      nlinarith [mul_nonneg hCcnn hTnn]
    linarith
  have hLCcN : L ≤ Cc * t u x := by
    have hh : ((L:ℕ):ℝ) ≤ ((Cc * t u x : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast hh
  
  obtain ⟨W, hW⟩ : ∃ W : Finset ℕ, W = Finset.Ioc (A u k) (A u k + L) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Finset ℕ, B = W.filter (fun m => ∀ i < K + 1, ¬ u i ∣ m) :=
    ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S = (Finset.range (A u k + L + 1)).filter
      (fun i => K < i ∧ ∃ m ∈ W, u i ∣ m) := ⟨_, rfl⟩
  have hmemW : ∀ m, m ∈ W ↔ (A u k < m ∧ m ≤ A u k + L) := by
    intro m; rw [hW, Finset.mem_Ioc]
  have hmemB : ∀ m, m ∈ B ↔ (m ∈ W ∧ ∀ i < K + 1, ¬ u i ∣ m) := by
    intro m; rw [hB, Finset.mem_filter]
  have hmemS : ∀ i, i ∈ S ↔ (i < A u k + L + 1 ∧ (K < i ∧ ∃ m ∈ W, u i ∣ m)) := by
    intro i; rw [hS, Finset.mem_filter, Finset.mem_range]
  
  have hcov : ∀ m ∈ W, ∃ i, u i ∣ m := by
    intro m hm
    rw [hmemW] at hm
    exact nth_gap_covered u hinf k m hm.1 (lt_of_le_of_lt hm.2 hgapN)
  
  have hsieve : |((B.card : ℝ)) - (L:ℝ) * ∏ i ∈ Finset.range (K + 1), (1 - 1 / (u i : ℝ))|
      ≤ (2:ℝ) ^ (K + 1) - 1 := by
    rw [hB, hW]
    exact sieve_interval_count u hu2 hcop (K + 1) (A u k) L
  have hPiD : D ≤ ∏ i ∈ Finset.range (K + 1), (1 - 1 / (u i : ℝ)) := by
    have h := tprod_le_prod_range u hu2 hsum (K + 1)
    rw [hDdef] at h
    exact h
  have hBlow : (L:ℝ) * D - (2:ℝ) ^ (K + 1) ≤ ((B.card : ℝ)) := by
    have h1 := abs_le.1 hsieve
    have h3 : (L:ℝ) * D ≤ (L:ℝ) * ∏ i ∈ Finset.range (K + 1), (1 - 1 / (u i : ℝ)) :=
      mul_le_mul_of_nonneg_left hPiD hLnn
    linarith [h1.1]
  
  have hsub : B ⊆ S.biUnion (fun i => W.filter (fun m => u i ∣ m)) := by
    intro m hm
    obtain ⟨hmW, hmB⟩ := (hmemB m).1 hm
    obtain ⟨i, hi⟩ := hcov m hmW
    obtain ⟨hlo, hhi⟩ := (hmemW m).1 hmW
    have hKi : K < i := by
      by_contra hcon
      push_neg at hcon
      exact hmB i (by omega) hi
    have hmpos : 0 < m := by omega
    have hui : u i ≤ m := Nat.le_of_dvd hmpos hi
    have hiu : i ≤ u i := hmono.le_apply
    rw [Finset.mem_biUnion]
    exact ⟨i, (hmemS i).2 ⟨by omega, hKi, ⟨m, hmW, hi⟩⟩,
      Finset.mem_filter.2 ⟨hmW, hi⟩⟩
  have hcard1 : B.card ≤ ∑ i ∈ S, (W.filter (fun m => u i ∣ m)).card :=
    le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  have hterm : ∀ i ∈ S, (((W.filter (fun m => u i ∣ m)).card : ℝ))
      ≤ (L:ℝ) * (1 / (u i : ℝ)) + 1 := by
    intro i _
    have hle : A u k ≤ A u k + L := Nat.le_add_right _ _
    have hc : (W.filter (fun m => u i ∣ m)).card
        = (A u k + L) / u i - (A u k) / u i := by
      rw [hW]; exact card_Ioc_filter_dvd (A u k) (A u k + L) (u i) hle
    rw [hc]
    have hdiv : (A u k) / u i ≤ (A u k + L) / u i := Nat.div_le_div_right hle
    rw [Nat.cast_sub hdiv]
    have h1 : (((A u k + L) / u i : ℕ) : ℝ) ≤ ((A u k + L : ℕ) : ℝ) / (u i : ℝ) :=
      Nat.cast_div_le
    have hcast : (((A u k + L : ℕ)) : ℝ) = ((A u k : ℕ):ℝ) + (L:ℝ) := by push_cast; ring
    rw [hcast] at h1
    have hui0 : 0 < u i := by have := hu2 i; omega
    have hR : ((A u k : ℕ) : ℝ) < (u i : ℝ) * (((A u k) / u i : ℕ) : ℝ) + (u i : ℝ) := by
      have hmod := Nat.div_add_mod (A u k) (u i)
      have hlt := Nat.mod_lt (A u k) hui0
      have hnn : (A u k) < u i * ((A u k) / u i) + u i := by omega
      exact_mod_cast hnn
    have h4 : ((A u k : ℕ) : ℝ) / (u i : ℝ) < (((A u k) / u i : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ (huposR i)]
      nlinarith [hR]
    have hd : (((A u k : ℕ):ℝ) + (L:ℝ)) / (u i : ℝ)
        = ((A u k : ℕ):ℝ) / (u i : ℝ) + (L:ℝ) * (1 / (u i : ℝ)) := by
      field_simp
    rw [hd] at h1
    linarith
  have hupper : ((B.card : ℝ)) ≤ (L:ℝ) * σ + (S.card : ℝ) := by
    have h1 : ((B.card : ℝ)) ≤ ∑ i ∈ S, (((W.filter (fun m => u i ∣ m)).card : ℝ)) := by
      have hh : ((B.card : ℕ) : ℝ)
          ≤ (((∑ i ∈ S, (W.filter (fun m => u i ∣ m)).card : ℕ)) : ℝ) := by
        exact_mod_cast hcard1
      push_cast at hh
      exact hh
    have h3 : ∑ i ∈ S, (((W.filter (fun m => u i ∣ m)).card : ℝ))
        ≤ ∑ i ∈ S, ((L:ℝ) * (1 / (u i : ℝ)) + 1) := Finset.sum_le_sum hterm
    have h4 : ∑ i ∈ S, ((L:ℝ) * (1 / (u i : ℝ)) + 1)
        = (L:ℝ) * (∑ i ∈ S, (1:ℝ) / (u i : ℝ)) + (S.card : ℝ) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
        mul_one]
    have h5 : ∑ i ∈ S, (1:ℝ) / (u i : ℝ) ≤ σ :=
      hsumS S (fun i hi => ((hmemS i).1 hi).2.1)
    have h6 : (L:ℝ) * (∑ i ∈ S, (1:ℝ) / (u i : ℝ)) ≤ (L:ℝ) * σ :=
      mul_le_mul_of_nonneg_left h5 hLnn
    linarith
  
  have hScard : (L:ℝ) * (D - σ) - (2:ℝ) ^ (K + 1) ≤ (S.card : ℝ) := by
    nlinarith [hBlow, hupper]
  have hDsig : D * (1 - ε/8) ≤ D - σ := by nlinarith [hσle]
  have hDsigpos : (0:ℝ) < D * (1 - ε/8) := mul_pos hD (by linarith)
  have hynn1 : (0:ℝ) ≤ (1 + ε/2) * (t u x : ℝ) * D⁻¹ - 1 := by linarith
  have hkey1 : ((1 + ε/2) * (t u x : ℝ) * D⁻¹ - 1) * (D * (1 - ε/8))
      ≤ (L:ℝ) * (D - σ) := by
    have a1 : ((1 + ε/2) * (t u x : ℝ) * D⁻¹ - 1) * (D * (1 - ε/8))
        ≤ (L:ℝ) * (D * (1 - ε/8)) :=
      mul_le_mul_of_nonneg_right (le_of_lt hLgt) hDsigpos.le
    have a2 : (L:ℝ) * (D * (1 - ε/8)) ≤ (L:ℝ) * (D - σ) :=
      mul_le_mul_of_nonneg_left hDsig hLnn
    linarith
  have hident : ((1 + ε/2) * (t u x : ℝ) * D⁻¹ - 1) * (D * (1 - ε/8))
      = ((1 + ε/2) * (t u x : ℝ) - D) * (1 - ε/8) := by
    field_simp
  have hkey2 : ((1 + ε/2) * (t u x : ℝ) - D) * (1 - ε/8) ≤ (L:ℝ) * (D - σ) := by
    rw [← hident]; exact hkey1
  have c0 : (0:ℝ) ≤ ε * (1 - ε) := mul_nonneg hε0.le (by linarith)
  have c1 : (0:ℝ) ≤ (ε * (1 - ε)) * (t u x : ℝ) := mul_nonneg c0 hTnn
  have c2 : D * (1 - ε/8) ≤ 1 := by
    have hh : (0:ℝ) ≤ D * (ε/8) := mul_nonneg hD.le (by linarith)
    nlinarith
  have hstep : (1 + 5*ε/16) * (t u x : ℝ) - 1
      ≤ ((1 + ε/2) * (t u x : ℝ) - D) * (1 - ε/8) := by nlinarith [c1, c2]
  have hSlow : (1 + 5*ε/16) * (t u x : ℝ) - 1 - (2:ℝ) ^ (K + 1) ≤ (S.card : ℝ) := by
    linarith
  have hMlt : ((Nat.ceil ((1 + ε/6) * (t u x : ℝ)) : ℕ) : ℝ)
      < (1 + ε/6) * (t u x : ℝ) + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg (by linarith) hTnn)
  have hMle : Nat.ceil ((1 + ε/6) * (t u x : ℝ)) ≤ S.card := by
    have hh : ((Nat.ceil ((1 + ε/6) * (t u x : ℝ)) : ℕ) : ℝ) ≤ (S.card : ℝ) := by
      nlinarith [hMlt, hSlow, hB2]
    exact_mod_cast hh
  
  obtain ⟨S', hS'sub, hS'card⟩ := Finset.exists_subset_card_eq hMle
  have hjex : ∀ i : ℕ, ∃ q : ℕ, i ∈ S → (1 ≤ q ∧ q ≤ L ∧ u i ∣ (A u k) + q) := by
    intro i
    by_cases hi : i ∈ S
    · obtain ⟨-, -, m, hmW, hdvd⟩ := (hmemS i).1 hi
      obtain ⟨hlo, hhi⟩ := (hmemW m).1 hmW
      refine ⟨m - A u k, fun _ => ⟨by omega, by omega, ?_⟩⟩
      rwa [Nat.add_sub_cancel' hlo.le]
    · exact ⟨0, fun h => absurd h hi⟩
  choose jf hjf using hjex
  refine ⟨A u k, hk, S', jf, hS'card, ?_, ?_, ?_⟩
  · intro i hi
    exact ((hmemS i).1 (hS'sub hi)).2.1
  · intro i hi
    have h := hjf i (hS'sub hi)
    exact ⟨h.1, le_trans h.2.1 hLCcN⟩
  · intro i hi
    exact (hjf i (hS'sub hi)).2.2

theorem erdos_1101.parts.ii : ∃ u, IsGood u ∧ (fun n => Real.log (u n : ℝ)) =o[atTop] (fun n => (n : ℝ)) :=
by
  
  
  
  obtain ⟨Cp, hCp0, hCp⟩ := nth_prime_linearithmic
  obtain ⟨P, hP, hPlog, hPbig⟩ := good_seq_pools_exist Cp hCp0 hCp
  obtain ⟨u, hmem, hsel⟩ := random_pool_selection P hP hPlog hPbig
    (fun b δ hb hδ => esym_geom_bound b δ hb hδ)
    (fun N m hN hm => prime_divisor_count_bound N m hN hm)
  
  
  
  have hprime : ∀ n, Nat.Prime (u n) := fun n => hP.2.1 n (u n) (hmem n)
  have hu2 : ∀ n, 2 ≤ u n := fun n => (hprime n).two_le
  have hupos : ∀ n, 0 < u n := fun n => lt_of_lt_of_le (by norm_num) (hu2 n)
  have hu2R : ∀ n, (2:ℝ) ≤ (u n : ℝ) := by
    intro n; exact_mod_cast hu2 n
  have huposR : ∀ n, (0:ℝ) < (u n : ℝ) := fun n => by linarith [hu2R n]
  have hmono : StrictMono u :=
    strictMono_nat_of_lt_succ (fun n => hP.2.2 n (u n) (hmem n) (u (n + 1)) (hmem (n + 1)))
  have hcop : ∀ i j : ℕ, i ≠ j → Nat.Coprime (u i) (u j) := by
    intro i j hij
    exact (Nat.coprime_primes (hprime i) (hprime j)).2 (fun h => hij (hmono.injective h))
  have hlognn : ∀ n, (0:ℝ) ≤ Real.log (u n : ℝ) :=
    fun n => Real.log_nonneg (by linarith [hu2R n])
  
  
  
  have hlogub : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      Real.log (u n : ℝ) ≤ (1 + δ) * Real.sqrt n := by
    intro δ hδ
    filter_upwards [hPlog δ hδ] with n hn
    have h := abs_le.1 (hn (u n) (hmem n))
    have hexp : (1 + δ) * Real.sqrt n = Real.sqrt n + δ * Real.sqrt n := by ring
    linarith [h.2]
  have hloglb : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      (1 - δ) * Real.sqrt n ≤ Real.log (u n : ℝ) := by
    intro δ hδ
    filter_upwards [hPlog δ hδ] with n hn
    have h := abs_le.1 (hn (u n) (hmem n))
    have hexp : (1 - δ) * Real.sqrt n = Real.sqrt n - δ * Real.sqrt n := by ring
    linarith [h.1]
  
  
  
  have hulow : ∀ᶠ n : ℕ in atTop, ((n:ℝ)^2) / 4096 ≤ (u n : ℝ) := by
    filter_upwards [hloglb (1/2) (by norm_num)] with n hn
    have hs : (0:ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
    have h1 : Real.sqrt n / 2 ≤ Real.log (u n : ℝ) := by linarith
    have h2 : Real.exp (Real.sqrt n / 2) ≤ (u n : ℝ) := by
      rw [← Real.exp_log (huposR n)]
      exact Real.exp_le_exp.2 h1
    have hsplit : Real.exp (Real.sqrt n / 2)
        = Real.exp (Real.sqrt n / 8) * Real.exp (Real.sqrt n / 8)
          * Real.exp (Real.sqrt n / 8) * Real.exp (Real.sqrt n / 8) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      ring_nf
    have h3 : Real.sqrt n / 8 ≤ Real.exp (Real.sqrt n / 8) := by
      have := Real.add_one_le_exp (Real.sqrt n / 8)
      linarith
    have h4 : (Real.sqrt n / 8) ^ 4 ≤ (Real.exp (Real.sqrt n / 8)) ^ 4 := by
      have hz : (0:ℝ) ≤ Real.sqrt n / 8 := by positivity
      have he : (0:ℝ) ≤ Real.exp (Real.sqrt n / 8) := (Real.exp_pos _).le
      have hq : (Real.sqrt n / 8) * (Real.sqrt n / 8)
          ≤ (Real.exp (Real.sqrt n / 8)) * (Real.exp (Real.sqrt n / 8)) :=
        mul_le_mul h3 h3 hz he
      have hq2 : ((Real.sqrt n / 8) * (Real.sqrt n / 8)) * ((Real.sqrt n / 8) * (Real.sqrt n / 8))
          ≤ ((Real.exp (Real.sqrt n / 8)) * (Real.exp (Real.sqrt n / 8)))
            * ((Real.exp (Real.sqrt n / 8)) * (Real.exp (Real.sqrt n / 8))) :=
        mul_le_mul hq hq (by positivity) (by positivity)
      calc (Real.sqrt n / 8) ^ 4
          = ((Real.sqrt n / 8) * (Real.sqrt n / 8)) * ((Real.sqrt n / 8) * (Real.sqrt n / 8)) := by
            ring
        _ ≤ ((Real.exp (Real.sqrt n / 8)) * (Real.exp (Real.sqrt n / 8)))
            * ((Real.exp (Real.sqrt n / 8)) * (Real.exp (Real.sqrt n / 8))) := hq2
        _ = (Real.exp (Real.sqrt n / 8)) ^ 4 := by ring
    have h5 : (Real.exp (Real.sqrt n / 8)) ^ 4 = Real.exp (Real.sqrt n / 2) := by
      rw [hsplit]; ring
    have h6 : Real.sqrt n ^ 4 = (n:ℝ)^2 := by
      have h7 : Real.sqrt n ^ 2 = (n:ℝ) := Real.sq_sqrt (by positivity)
      calc Real.sqrt n ^ 4 = (Real.sqrt n ^ 2) ^ 2 := by ring
        _ = (n:ℝ)^2 := by rw [h7]
    have h8 : (Real.sqrt n / 8) ^ 4 = (n:ℝ)^2 / 4096 := by
      rw [div_pow, h6]; norm_num
    rw [h8, h5] at h4
    linarith
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 hulow
  have hSummable : Summable (fun n : ℕ => 1 / (u n : ℝ)) := by
    have hmaj : Summable (fun n : ℕ => 4096 * (1 / (((n + (n₁ + 1) : ℕ)) : ℝ) ^ 2)) := by
      refine (summable_nat_add_iff (f := fun n : ℕ => 4096 * (1 / ((n:ℝ) ^ 2))) (n₁ + 1)).2 ?_
      exact ((Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)).mul_left 4096
    have hcomp : Summable (fun n : ℕ => 1 / (u (n + (n₁ + 1)) : ℝ)) := by
      refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hmaj
      have hge : n₁ ≤ n + (n₁ + 1) := by omega
      have hb := hn₁ (n + (n₁ + 1)) hge
      have hpos : (0:ℝ) < ((n + (n₁ + 1) : ℕ) : ℝ) := by
        have : 0 < n + (n₁ + 1) := by omega
        exact_mod_cast this
      have hb2 : (((n + (n₁ + 1) : ℕ)) : ℝ) ^ 2 / 4096 ≤ (u (n + (n₁ + 1)) : ℝ) := hb
      have hnum : (0:ℝ) < (((n + (n₁ + 1) : ℕ)) : ℝ) ^ 2 / 4096 := by positivity
      have hle := one_div_le_one_div_of_le hnum hb2
      calc 1 / (u (n + (n₁ + 1)) : ℝ)
          ≤ 1 / ((((n + (n₁ + 1) : ℕ)) : ℝ) ^ 2 / 4096) := hle
        _ = 4096 * (1 / (((n + (n₁ + 1) : ℕ)) : ℝ) ^ 2) := by
            field_simp
    exact (summable_nat_add_iff (f := fun n : ℕ => 1 / (u n : ℝ)) (n₁ + 1)).1 hcomp
  
  
  
  have hsqrto : (fun n : ℕ => Real.sqrt n) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    obtain ⟨m, hm⟩ := exists_nat_gt (1 / c ^ 2)
    filter_upwards [eventually_ge_atTop m] with n hn
    have hnm : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hn0 : (0:ℝ) ≤ (n:ℝ) := by positivity
    have h0 : (0:ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
    have hnn : Real.sqrt n * Real.sqrt n = (n:ℝ) := Real.mul_self_sqrt hn0
    have hcn : (1 / c ^ 2 : ℝ) ≤ (n:ℝ) := le_of_lt (lt_of_lt_of_le hm hnm)
    have hsq : (1 / c) ≤ Real.sqrt n := by
      have hb : ((1:ℝ)/c) ^ 2 ≤ (n:ℝ) := by
        rw [div_pow, one_pow]; exact hcn
      have := Real.sqrt_le_sqrt hb
      rwa [Real.sqrt_sq (by positivity)] at this
    have h1 : 1 ≤ Real.sqrt n * c := (div_le_iff₀ hc).1 hsq
    have key : Real.sqrt n ≤ c * (n:ℝ) := by
      nlinarith [mul_nonneg h0 (sub_nonneg.2 h1), hnn]
    rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg hn0]
    exact key
  have hgrowth : (fun n : ℕ => Real.log (u n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
    have hbig : (fun n : ℕ => Real.log (u n : ℝ)) =O[atTop] (fun n : ℕ => Real.sqrt n) := by
      refine Asymptotics.IsBigO.of_bound (3/2) ?_
      filter_upwards [hlogub (1/2) (by norm_num)] with n hn
      rw [Real.norm_of_nonneg (hlognn n), Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      linarith
    exact hbig.trans_isLittleO hsqrto
  
  
  
  have ha_pos : ∀ i : ℕ, (0:ℝ) < 1 / (u i : ℝ) := fun i => div_pos one_pos (huposR i)
  have ha_le : ∀ i : ℕ, 1 / (u i : ℝ) ≤ 1 / 2 :=
    fun i => one_div_le_one_div_of_le (by norm_num) (hu2R i)
  have hsubpos : ∀ i : ℕ, (0:ℝ) < 1 - 1 / (u i : ℝ) := by
    intro i; have := ha_le i; linarith
  have hlogle0 : ∀ i : ℕ, Real.log (1 - 1 / (u i : ℝ)) ≤ 0 := by
    intro i
    have h := Real.log_le_log (hsubpos i)
      (by linarith [ha_pos i] : 1 - 1 / (u i : ℝ) ≤ 1)
    rwa [Real.log_one] at h
  have hloglow : ∀ i : ℕ,
      -(2 * (1 / (u i : ℝ))) ≤ Real.log (1 - 1 / (u i : ℝ)) := by
    intro i
    have h0 : (0:ℝ) ≤ 1 / (u i : ℝ) := (ha_pos i).le
    have h1 : 1 / (u i : ℝ) ≤ 1 / 2 := ha_le i
    have hexp : Real.exp (-(2 * (1 / (u i : ℝ)))) ≤ 1 - 1 / (u i : ℝ) := by
      set tt := 1 / (u i : ℝ) with htt
      have he : 2 * tt + 1 ≤ Real.exp (2 * tt) := Real.add_one_le_exp (2 * tt)
      have hid : Real.exp (-(2 * tt)) * Real.exp (2 * tt) = 1 := by
        rw [← Real.exp_add]; simp
      have hp1 : (0:ℝ) < Real.exp (-(2 * tt)) := Real.exp_pos _
      have hp2 : (0:ℝ) < Real.exp (2 * tt) := Real.exp_pos _
      nlinarith [hid, he, hp1, hp2, mul_nonneg h0 (by linarith : (0:ℝ) ≤ 1 - 2 * tt)]
    exact (Real.le_log_iff_exp_le (hsubpos i)).2 hexp
  have hsumneg : Summable (fun i : ℕ => -(Real.log (1 - 1 / (u i : ℝ)))) := by
    refine Summable.of_nonneg_of_le (fun i => by linarith [hlogle0 i]) (fun i => ?_)
      (hSummable.mul_left 2)
    have := hloglow i
    linarith
  have hsumlog : Summable (fun i : ℕ => Real.log (1 - 1 / (u i : ℝ))) := by
    have h := hsumneg.neg
    simpa using h
  have hDpos : (0:ℝ) < ∏' i : ℕ, (1 - 1 / (u i : ℝ)) := by
    have hhs : HasSum (fun i : ℕ => Real.log (1 - 1 / (u i : ℝ)))
        (∑' i : ℕ, Real.log (1 - 1 / (u i : ℝ))) := hsumlog.hasSum
    have hp := hhs.rexp
    have heq : (Real.exp ∘ fun i : ℕ => Real.log (1 - 1 / (u i : ℝ)))
        = fun i : ℕ => 1 - 1 / (u i : ℝ) := by
      funext i
      simp only [Function.comp_apply]
      exact Real.exp_log (hsubpos i)
    rw [heq] at hp
    rw [hp.tprod_eq]
    exact Real.exp_pos _
  
  
  
  have hpow_le : ∀ k : ℕ, 2 ^ k ≤ ∏ i ∈ Finset.range k, u i := by
    intro k
    calc 2 ^ k = 2 ^ (Finset.range k).card := by rw [Finset.card_range]
      _ ≤ ∏ i ∈ Finset.range k, u i :=
          Finset.pow_card_le_prod _ _ _ (fun i _ => hu2 i)
  have hbdd : ∀ x : ℕ, BddAbove {k | ∏ i ∈ Finset.range k, u i ≤ x} := by
    intro x
    refine ⟨x, ?_⟩
    intro k hk
    have h1 : k < 2 ^ k := Nat.lt_two_pow_self
    have h2 : (2:ℕ) ^ k ≤ x := le_trans (hpow_le k) hk
    omega
  have hnonempty : ∀ x : ℕ, 1 ≤ x → Set.Nonempty {k | ∏ i ∈ Finset.range k, u i ≤ x} := by
    intro x hx
    exact ⟨0, by simpa using hx⟩
  have hT1 : ∀ x : ℕ, 1 ≤ x → (∏ i ∈ Finset.range (t u x), u i) ≤ x := by
    intro x hx
    exact Nat.sSup_mem (hnonempty x hx) (hbdd x)
  have hT2 : ∀ x : ℕ, 1 ≤ x → x < ∏ i ∈ Finset.range (t u x + 1), u i := by
    intro x hx
    by_contra hcon
    push_neg at hcon
    have hle : t u x + 1 ≤ t u x := le_csSup (hbdd x) hcon
    omega
  have hT3 : ∀ m x : ℕ, (∏ i ∈ Finset.range m, u i) ≤ x → m ≤ t u x :=
    fun m x hx => le_csSup (hbdd x) hx
  have hTtend : Filter.Tendsto (fun x : ℕ => t u x) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro m
    filter_upwards [eventually_ge_atTop (∏ i ∈ Finset.range m, u i)] with x hx
    exact hT3 m x hx
  
  
  
  have hrp : ∀ y : ℝ, 0 ≤ y → y ^ ((3:ℝ)/2) = (Real.sqrt y) ^ 3 := by
    intro y hy
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (y ^ ((1:ℝ)/2)) 3, ← Real.rpow_mul hy]
    norm_num
  have hrp3 : ∀ y : ℝ, 0 ≤ y → y ^ ((3:ℝ)/2) = Real.sqrt y * y := by
    intro y hy
    have h1 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
    calc y ^ ((3:ℝ)/2) = Real.sqrt y ^ 3 := hrp y hy
      _ = Real.sqrt y * (Real.sqrt y ^ 2) := by ring
      _ = Real.sqrt y * y := by rw [h1]
  have hcube : ∀ y : ℝ, 1 ≤ y →
      (y + 1) ^ ((3:ℝ)/2) ≤ y ^ ((3:ℝ)/2) + 3 * Real.sqrt y := by
    intro y hy
    have hy0 : (0:ℝ) ≤ y := by linarith
    have hy1 : (0:ℝ) ≤ y + 1 := by linarith
    have ha : (0:ℝ) ≤ Real.sqrt y := Real.sqrt_nonneg _
    have hc : (0:ℝ) ≤ Real.sqrt (y + 1) := Real.sqrt_nonneg _
    have ha2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy0
    have hc2 : Real.sqrt (y + 1) ^ 2 = y + 1 := Real.sq_sqrt hy1
    have hac : Real.sqrt y ≤ Real.sqrt (y + 1) := Real.sqrt_le_sqrt (by linarith)
    have ha1 : (1:ℝ) ≤ Real.sqrt y := by nlinarith
    have hcpos : (0:ℝ) < Real.sqrt (y + 1) + Real.sqrt y := by linarith
    have hid : (Real.sqrt (y+1) ^ 3 - Real.sqrt y ^ 3) * (Real.sqrt (y+1) + Real.sqrt y)
        = (Real.sqrt (y+1) ^ 2 - Real.sqrt y ^ 2)
          * (Real.sqrt (y+1) ^ 2 + Real.sqrt (y+1) * Real.sqrt y + Real.sqrt y ^ 2) := by
      ring
    have hdiff : Real.sqrt (y+1) ^ 2 - Real.sqrt y ^ 2 = 1 := by rw [hc2, ha2]; ring
    have hb : Real.sqrt (y+1) ^ 2 + Real.sqrt (y+1) * Real.sqrt y + Real.sqrt y ^ 2
        ≤ ((3/2) * Real.sqrt (y+1)) * (Real.sqrt (y+1) + Real.sqrt y) := by
      nlinarith [mul_nonneg ha (sub_nonneg.2 hac), mul_nonneg hc (sub_nonneg.2 hac)]
    have h4 : (Real.sqrt (y+1) ^ 3 - Real.sqrt y ^ 3) * (Real.sqrt (y+1) + Real.sqrt y)
        ≤ ((3/2) * Real.sqrt (y+1)) * (Real.sqrt (y+1) + Real.sqrt y) := by
      rw [hid, hdiff, one_mul]; exact hb
    have h5 : Real.sqrt (y+1) ^ 3 - Real.sqrt y ^ 3 ≤ (3/2) * Real.sqrt (y+1) :=
      le_of_mul_le_mul_right h4 hcpos
    have h6 : Real.sqrt (y+1) ≤ 2 * Real.sqrt y := by nlinarith
    rw [hrp (y+1) hy1, hrp y hy0]
    linarith
  
  
  
  have hlogprod : ∀ m : ℕ, Real.log ((∏ i ∈ Finset.range m, u i : ℕ) : ℝ)
      = ∑ i ∈ Finset.range m, Real.log (u i : ℝ) := by
    intro m
    rw [Nat.cast_prod, Real.log_prod]
    intro i _
    exact ne_of_gt (huposR i)
  have hxbound : ∀ θ₀ : ℝ, 0 < θ₀ → ∀ᶠ x : ℕ in atTop,
      (x:ℝ) ≤ Real.exp ((2/3 + θ₀) * (t u x : ℝ) ^ ((3:ℝ)/2)) := by
    intro θ₀ hθ₀
    obtain ⟨θ, hθ, hθ1, hθle⟩ : ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ θ ≤ θ₀ :=
      ⟨min θ₀ 1, lt_min hθ₀ one_pos, min_le_right _ _, min_le_left _ _⟩
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hlogub (θ/4) (by positivity))
    set Λ : ℝ := ∑ i ∈ Finset.range n₀, Real.log (u i : ℝ) with hΛdef
    have hΛ0 : (0:ℝ) ≤ Λ := Finset.sum_nonneg (fun i _ => hlognn i)
    have hsumb : ∀ m : ℕ, n₀ ≤ m → ∑ i ∈ Finset.range m, Real.log (u i : ℝ)
        ≤ Λ + (1 + θ/4) * ((2/3) * ((m:ℝ) ^ ((3:ℝ)/2))) := by
      intro m hm
      have hsplit : ∑ i ∈ Finset.range m, Real.log (u i : ℝ)
          = Λ + ∑ i ∈ Finset.Ico n₀ m, Real.log (u i : ℝ) := by
        rw [hΛdef]
        simp only [Finset.range_eq_Ico]
        exact (Finset.sum_Ico_consecutive _ (Nat.zero_le n₀) hm).symm
      have hb1 : ∑ i ∈ Finset.Ico n₀ m, Real.log (u i : ℝ)
          ≤ ∑ i ∈ Finset.Ico n₀ m, (1 + θ/4) * Real.sqrt i :=
        Finset.sum_le_sum (fun i hi => hn₀ i (Finset.mem_Ico.1 hi).1)
      have hb2 : ∑ i ∈ Finset.Ico n₀ m, (1 + θ/4) * Real.sqrt i
          ≤ ∑ i ∈ Finset.range m, (1 + θ/4) * Real.sqrt i := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity)
        rw [Finset.range_eq_Ico]
        exact Finset.Ico_subset_Ico (Nat.zero_le _) le_rfl
      have hb3 : ∑ i ∈ Finset.range m, (1 + θ/4) * Real.sqrt i
          = (1 + θ/4) * ∑ i ∈ Finset.range m, Real.sqrt i := by
        rw [Finset.mul_sum]
      have hb4 : ∑ i ∈ Finset.range m, Real.sqrt i ≤ (2/3 : ℝ) * ((m:ℝ) ^ ((3:ℝ)/2)) :=
        (sum_sqrt_bounds m).2
      have hb5 : (1 + θ/4) * ∑ i ∈ Finset.range m, Real.sqrt i
          ≤ (1 + θ/4) * ((2/3 : ℝ) * ((m:ℝ) ^ ((3:ℝ)/2))) :=
        mul_le_mul_of_nonneg_left hb4 (by positivity)
      rw [hsplit]
      linarith [hb1, hb2, hb3 ▸ hb5]
    obtain ⟨T, hT⟩ := exists_nat_gt (max 1 (6 * (Λ + 3) / (5 * θ)))
    have hT1R : (1:ℝ) < (T:ℝ) := lt_of_le_of_lt (le_max_left _ _) hT
    have hT2R : 6 * (Λ + 3) / (5 * θ) < (T:ℝ) := lt_of_le_of_lt (le_max_right _ _) hT
    filter_upwards [hTtend.eventually (eventually_ge_atTop (max n₀ T)), eventually_ge_atTop 1]
      with x hx1 hx2
    have hn₀t : n₀ ≤ t u x := le_trans (le_max_left _ _) hx1
    have hTt : T ≤ t u x := le_trans (le_max_right _ _) hx1
    have hTtR : (T:ℝ) ≤ (t u x : ℝ) := by exact_mod_cast hTt
    have hs1 : (1:ℝ) ≤ (t u x : ℝ) := le_of_lt (lt_of_lt_of_le hT1R hTtR)
    have ht0 : (0:ℝ) ≤ (t u x : ℝ) := by linarith
    set a : ℝ := Real.sqrt (t u x) with hadef
    have ha0 : (0:ℝ) ≤ a := Real.sqrt_nonneg _
    have ha2 : a ^ 2 = (t u x : ℝ) := Real.sq_sqrt ht0
    have ha1 : (1:ℝ) ≤ a := by nlinarith
    
    have hA := hsumb (t u x + 1) (by omega)
    have hcast : (((t u x + 1 : ℕ)) : ℝ) = (t u x : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hA
    have hB := hcube (t u x : ℝ) hs1
    have hL3 : ((t u x : ℝ)) ^ ((3:ℝ)/2) = a * (t u x : ℝ) := hrp3 _ ht0
    
    have hlt : (x:ℝ) < ((∏ i ∈ Finset.range (t u x + 1), u i : ℕ) : ℝ) := by
      exact_mod_cast hT2 x hx2
    have hxpos : (0:ℝ) < (x:ℝ) := by
      have : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx2
      linarith
    have hlogx : Real.log x ≤ ∑ i ∈ Finset.range (t u x + 1), Real.log (u i : ℝ) := by
      have h1 : Real.log x ≤ Real.log ((∏ i ∈ Finset.range (t u x + 1), u i : ℕ) : ℝ) :=
        Real.log_le_log hxpos hlt.le
      rwa [hlogprod] at h1
    
    have h6 : 6 * (Λ + 3) < (T:ℝ) * (5 * θ) := (div_lt_iff₀ (by positivity)).1 hT2R
    have h7 : (T:ℝ) * (5 * θ) ≤ (t u x : ℝ) * (5 * θ) :=
      mul_le_mul_of_nonneg_right hTtR (by positivity)
    have htt : Λ ≤ (5 * θ / 6) * (t u x : ℝ) - 3 := by linarith
    have hq : (0:ℝ) ≤ (5 * θ / 6) * (t u x : ℝ) - 3 := by linarith
    have hprod : (0:ℝ) ≤ (a - 1) * ((5 * θ / 6) * (t u x : ℝ) - 3) :=
      mul_nonneg (by linarith) hq
    have hfin : Λ + 3 * a ≤ (5 * θ / 6) * (a * (t u x : ℝ)) := by nlinarith [hprod, htt]
    have htha : (θ/2) * a ≤ a := by nlinarith [mul_nonneg ha0 (by linarith : (0:ℝ) ≤ 1 - θ/2)]
    rw [hL3] at hB
    have hgoal : Real.log x ≤ (2/3 + θ) * (a * (t u x : ℝ)) := by
      nlinarith [hlogx, hA, hB, hfin, htha, hΛ0]
    have hfinal : (x:ℝ) ≤ Real.exp ((2/3 + θ) * ((t u x : ℝ) ^ ((3:ℝ)/2))) := by
      rw [hL3]
      calc (x:ℝ) = Real.exp (Real.log x) := (Real.exp_log hxpos).symm
        _ ≤ Real.exp ((2/3 + θ) * (a * (t u x : ℝ))) := Real.exp_le_exp.2 hgoal
    refine le_trans hfinal (Real.exp_le_exp.2 ?_)
    have hnn : (0:ℝ) ≤ ((t u x : ℝ)) ^ ((3:ℝ)/2) := by
      rw [hL3]; positivity
    nlinarith [hnn, hθle]
  
  
  
  have hinf : (ASet u).Infinite := aset_infinite u hmono (hu2 0) hcop hSummable
  have hmain : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ᶠ x : ℕ in atTop, ∀ k : ℕ, A u k < x →
      (A u (k + 1) : ℝ) - A u k
        < (1 + ε) * (t u x : ℝ) * (∏' i : ℕ, (1 - 1 / (u i : ℝ)))⁻¹ := by
    intro ε hε0 hε1
    obtain ⟨Cc, hCc1, hCcR⟩ : ∃ Cc : ℕ, 1 ≤ Cc ∧
        (2:ℝ) / (∏' i : ℕ, (1 - 1 / (u i : ℝ))) ≤ (Cc : ℝ) := by
      refine ⟨Nat.ceil ((2:ℝ) / (∏' i : ℕ, (1 - 1 / (u i : ℝ)))) + 1,
        Nat.le_add_left 1 _, ?_⟩
      have h1 : (2:ℝ) / (∏' i : ℕ, (1 - 1 / (u i : ℝ)))
          ≤ (Nat.ceil ((2:ℝ) / (∏' i : ℕ, (1 - 1 / (u i : ℝ)))) : ℝ) := Nat.le_ceil _
      push_cast
      linarith
    obtain ⟨θ, K, hθ, hsel'⟩ := hsel Cc (ε/6) hCc1 (by linarith)
    obtain ⟨K', hKK', hcert⟩ := certificate_of_large_gap u hmono (hu2 0) hcop hSummable
      hinf hDpos ε hε0 hε1 Cc hCc1 hCcR K
    filter_upwards [hcert, hTtend.eventually hsel', hxbound θ hθ] with x hx1 hx2 hx3
    intro k hk
    by_contra hcon
    push_neg at hcon
    have hc1 := hx1 k hk hcon
    have hc2 : HasCert u x (Nat.ceil ((1 + ε/6) * (t u x : ℝ))) K (Cc * t u x) := by
      obtain ⟨n, hn, S, j, h1, h2, h3, h4⟩ := hc1
      exact ⟨n, hn, S, j, h1, fun i hi => lt_of_le_of_lt hKK' (h2 i hi), h3, h4⟩
    exact hx2 x hx3 hc2
  have hconj4 : ∀ ε > 0, ∀ᶠ x : ℕ in atTop, ∀ k : ℕ, A u k < x →
      (A u (k + 1) : ℝ) - A u k
        < (1 + ε) * (t u x : ℝ) * (∏' i : ℕ, (1 - 1 / (u i : ℝ)))⁻¹ := by
    intro ε hε
    by_cases h : ε ≤ 1
    · exact hmain ε hε h
    · push_neg at h
      filter_upwards [hmain 1 one_pos le_rfl] with x hx
      intro k hk
      have hlt := hx k hk
      have ht0 : (0:ℝ) ≤ (t u x : ℝ) := Nat.cast_nonneg _
      have hDi : (0:ℝ) < (∏' i : ℕ, (1 - 1 / (u i : ℝ)))⁻¹ := inv_pos.2 hDpos
      nlinarith [hlt, mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ ε - 1) ht0) hDi.le]
  
  
  
  exact ⟨u, ⟨hmono, hcop, hSummable, hconj4⟩, hgrowth⟩
