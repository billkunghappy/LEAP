# Blueprint: erdos_394.variants.hall_conjecture
Revision: 4  (REFUTATION — target is FALSE and this is KERNEL-CHECKED; action: refute.)

## Revision 4 note (dispatch #7)
Re-checked on disk: `logs/verification/1790552138_005993_disproof.json` (second, independent
submit-time check) also reports `is_valid: true`, 1652 lines, 0 sorry, axioms propext /
Classical.choice / Quot.sound / `Erdos394.erdos_394.variants.hall_conjecture`. The certificate
`disproof_scaffold.lean` is present in the node dir. Independent literature confirmation:
erdosproblems.com/forum/thread/394/proof-claims (Pickhardt & Omniscience Research Agent,
"Erdős Problem 394 and the average order of t_2: a counterexample to the strong form") proves
∑_{n≤x} t_2(n) ≫ x²/((log x)^{1/2} loglog x), so the strong form fails for every c ∈ (1/2, log 2).
Nothing in the mathematics changed; action is again `refute` with witness c = 2/3.

## Revision 3 note (dispatch #5)
The refutation below has already been formalized and accepted by the kernel:
`nodes/erdos_394.variants.hall_conjecture/disproof_scaffold.lean` (1652 lines, 0 sorry),
verification record `logs/verification/1790550348_943559_disproof.json`: `is_valid: true`,
target `erdos_394.variants.hall_conjecture_disproof : False`, axioms = propext, Classical.choice,
Quot.sound + the target axiom. Witness c = 2/3 < log 2 (Real.log_two_gt_d9). No `planned` action is
possible (a false statement has no proof); re-dispatching the disproof phase should simply re-submit
the existing certificate.

Revision 2 steps r1–r7 kept by id below;
r5 is now fully discharged by elementary proofs from named Mathlib lemmas, new ids r5a–r5f.

## 0. Why this revision exists
Round 1 refuted with witness c = 2/3; the disprove phase agreed the counterexample is real but could
not formalize it because r5 (Chebyshev lower bound, Mertens, Brun–Titchmarsh) was a black box "not
in Mathlib". This revision removes the black box: every analytic input is reduced to a short
elementary argument whose Mathlib ingredients were confirmed by `#check` (Section 3, r5a–r5f).
Main economies vs Revision 1:
* Mertens-type lower bounds come from the finite EULER PRODUCT ∏_{p≤N}(1−1/p)^{-1} ≥ H_N ≥ log N
  (no partial summation, exact exponent 1): gives both ∏_{p≤z}(1−1/p) ≤ 1/log z and
  ∑_{p≤y}1/p ≥ loglog y − 1.
* Chebyshev lower bound from `Nat.four_pow_le_two_mul_self_mul_centralBinom` +
  `Nat.pow_factorization_choose_le`; upper from `Chebyshev.eventually_primeCounting_le`.
* Brun–Titchmarsh replaced by BRUN'S PURE SIEVE (Bonferroni truncation), losing only a factor
  loglog Y (harmless: exponent unchanged). Needs ∑_{p≤z}1/p ≤ 6 loglog z + 7, from the Legendre /
  von Mangoldt identity (`ArithmeticFunction.vonMangoldt_sum`) + `Chebyshev.theta_le_log4_mul_x`
  + a dyadic-exponent block argument.
* BT is applied with modulus B = b/d (per divisor), not b — no lifting of classes needed.
* e_k lower bound by the one-line recursion k·e_k ≥ e_{k−1}(S − (k−1)/P0) (no tuple counting).
* Only ONE x is needed: pick x = exp(exp L) with L ∈ 20ℕ huge, so loglog x = L and k = 9L/20 exactly.

## 1. Statement
Target: ∀ c < log 2, F =o[atTop] (x ↦ x²/(log x)^c), F(x) := ∑_{n=1}^{⌊x⌋} t_2(n),
t_2(n) = sInf{m | 0 < m ∧ n ∣ m(m+1)} (Lean: `∏ i ∈ range 2, (m+i) = m*(m+1)`).
It is FALSE. Witness c = 2/3 (2/3 < 0.6931471803 < log 2, `Real.log_two_gt_d9`).
We prove: for all sufficiently large L ∈ 20ℕ, with x = exp(exp L),
   F(x) > x²/(log x)^{2/3},                                                     (★)
contradicting the little-o at ε = 1 (which gives F(x) ≤ x²/(log x)^{2/3} for all x ≥ X).
True order (Pickhardt–Omniscience, erdosproblems.com/forum/thread/394/proof-claims):
F(x) ≫ x²/((log x)^{1/2} loglog x); we prove the weaker F(x) ≥ x²(log x)^{−0.53} for large L.
Calibration: a genuine analytic-number-theory theorem (Chebyshev + Mertens-lite + Brun pure sieve +
CRT combinatorics + parameter bookkeeping); ~8 separable components, each textbook-level.

## 2. Strategy
Restrict to n = a·b, b a product of exactly k ≈ 0.45 loglog x distinct primes in (101, x^{1/(4k)}],
a prime in (Y/4, Y], Y = x/b. For such n every root of n | m(m+1) in [1, n−1] is n−1, or a·d·u,
or n−1−a·d·u, where d | b, d ≠ b, B = b/d, 1 ≤ u ≤ B−1, B | a·d·u + 1 (CRT, r2). If every such u
lies in [δB, (1−δ)B] then t_2(ab) ≥ δab − 1 (r3). For fixed (d,u) the condition B | adu+1 is ONE
residue class of a mod B, and ≤ 2δB values of u are "bad" (r4), so bad primes a number
≤ 2^{k+1}δ·max_B(B·BT(Y;B)) ≲ 2^{k+1}δρ^k·loglog Y·Y/log Y (Brun sieve r5d/r5e). With
δ ≍ 1/(2^{k+1}ρ^k loglog x) half the primes in (Y/4,Y] (≥ 0.3Y/log Y, r5a) are good. Summing over b:
F ≥ c δ x²/log x · e_k, e_k = ∑1/b ≥ (S−k/101)^k/k!, S ≥ loglog y − 6 (r5b); Stirling finishes
(exponent 1 − 0.479 = 0.521 < 2/3).

## 3. Proof (of ¬target)

Notation. ℙ = primes. π(t) = #{p ≤ t}. log = natural log. P0 = 101, ρ = 101/100. L ∈ 20ℕ large,
x = exp(e^L) (so log x = e^L, loglog x = L), k = 9L/20 ∈ ℕ, y = x^{1/(4k)} = exp(e^L/(4k)),
𝒫 = ℙ ∩ (P0, y], 𝓑 = {∏D : D ⊆ 𝒫, |D| = k} (squarefree, k prime factors, b ≤ y^k = x^{1/4}),
S = ∑_{p∈𝒫} 1/p, e_k = ∑_{b∈𝓑} 1/b, C_BT = 203, c1 = 3/10,
δ = c1/(8·C_BT·2^{k+1}·ρ^k·L).

1. [r1] [ELEM] Reduction. Assume the target; instantiate c = 2/3 (< log 2 by `Real.log_two_gt_d9`),
   use `IsLittleO.bound` with ε = 1: ∃X, ∀x ≥ X, |F x| ≤ |x²/(log x)^{2/3}|. Choose L ∈ 20ℕ with
   L ≥ L* (the max of all thresholds below) and exp(e^L) ≥ X; (★) at x = exp(e^L) contradicts.
   Note x²/(log x)^{2/3} = x²·e^{−2L/3} > 0 and F x ≥ 0.

2. [r2] [ELEM] roots_of_prime_times_squarefree. Let a prime, b squarefree, a ∤ b, n = ab,
   1 ≤ m ≤ n−1, n | m(m+1). Put A = gcd(n, m). Then:
   (i) if a | A: d := A/a divides b, d ≠ b, B := b/d ≥ 2, u := m/A ∈ [1, B−1] and B | a·d·u + 1,
       and m = a·d·u;
   (ii) if a ∤ A and A = 1: m = n − 1;
   (iii) if a ∤ A and A ≠ 1: m' := n−1−m ∈ [1, n−2] falls under (i): m' = a·d·u with d | b,
       d ≠ b, B = b/d, u ∈ [1,B−1], B | adu+1.
   Proof. n squarefree (a ∤ b, b squarefree, a prime). Claim n/A | m+1: n/A and m are coprime
   (a prime q dividing both divides A = gcd(n,m) and n/A, so q² | n, impossible), and n | m(m+1)
   gives n/A | (m/A)·... precisely: A·(n/A) | m(m+1), A | m, so (n/A) | (m/A)(m+1); gcd(n/A, m/A)=1
   ⇒ n/A | m+1. (i) a | A ⇒ A = a·d with d = A/a | n/a = b. d = b would give n | m, impossible for
   1 ≤ m < n. m = A·u with 1 ≤ u (m ≥ 1) and u < B (m < n = A·B). B = n/A | m+1 = adu+1.
   (ii) A = 1 ⇒ n | m+1, and 2 ≤ m+1 ≤ n ⇒ m+1 = n.
   (iii) A | m and n/A | m+1 with A | b (a ∤ A, A | n = ab, gcd(a,A)=1). m' + 1 = n − m ≡ −m ≡ 0
   (mod A); m' = n − (m+1) ≡ 0 (mod n/A). A ≠ 1 ⇒ m ≠ n−1 (gcd(n,n−1)=1 would force A=1) ⇒ m' ≥ 1;
   m ≥ 1 ⇒ m' ≤ n−2. gcd(n, m') ⊇ n/A = a·(b/A) and a | n/A so apply (i) to m' (which is a root:
   n | m'(m'+1) since n/A | m', A | m'+1, coprime): d = gcd(n,m')/a etc. [Simplest formal route:
   prove (i) as a standalone statement "if a | gcd(n,m) then …" and apply it to m and to m'.]

3. [r3] [ELEM] good_implies_large. Call a prime a GOOD for b (a ∤ b, b squarefree) with parameter
   δ ∈ (0,1/2) if: ∀ d | b, d ≠ b, with B = b/d, ∀ u ∈ [1, B−1], B | a·d·u + 1 ⇒ δB ≤ u ≤ (1−δ)B.
   Then t_2(ab) ≥ δ·ab − 1.
   Proof. n = ab ≥ 2 (a ≥ 2): m = n−1 satisfies 0 < m and n | (n−1)n, so t_2(n) ≤ n−1 and
   t_2(n) ∈ {m : 0 < m ∧ n | m(m+1)} (`Nat.sInf_mem`), m := t_2(n) ∈ [1, n−1]. Apply r2:
   (i) m = adu ≥ ad·δB = δn; (ii) m = n−1 ≥ δn − 1; (iii) m' = adu ≤ ad(1−δ)B = (1−δ)n, so
   m = n−1−m' ≥ δn − 1.

4. [r4] [ELEM] bad_prime_count. Fix b squarefree, d | b, d ≠ b, B = b/d, and Y > 0. Let
   U_bad = {u ∈ [1, B−1] : u < δB ∨ u > (1−δ)B}. Then |U_bad| ≤ 2δB, and
   #{a ≤ Y prime, a not GOOD-at-(d)} ≤ ∑_{u ∈ U_bad} #{a ≤ Y prime : B | a·d·u + 1}, and for each
   u the set {a : B | adu+1} is empty or a single residue class r_u mod B (if gcd(du,B)=1, take
   r_u ≡ −(du)^{-1}; otherwise empty since any common prime of du and B cannot divide adu+1).
   Proof. #{u ∈ ℤ : 1 ≤ u < δB} ≤ δB (they are 1..⌈δB⌉−1). u ↦ B − u maps
   {u ≤ B−1 : u > (1−δ)B} injectively into {1 ≤ v < δB}. Union bound over u. Class: if
   B | adu+1 and B | a'du+1 then B | du(a − a') and gcd(du,B)=1 (from B | adu+1) ⇒ a ≡ a' (mod B).
   Summing over the ≤ 2^k divisors d of b (b has k prime factors): the number of primes a ≤ Y that
   are not GOOD for b is ≤ ∑_{d|b, d≠b} 2δ(b/d)·max_r #{a ≤ Y prime : a ≡ r (mod b/d)}.

5. [r5a] [ELEM] chebyshev_window. ∃Y1, ∀ real Y ≥ Y1: #{p prime : Y/4 < p ≤ Y} ≥ 0.3·Y/log Y.
   Proof. Lower: n := ⌊Y/2⌋ ≥ 1. `Nat.four_pow_le_two_mul_self_mul_centralBinom`: 4^n ≤ 2n·C(2n,n).
   `Nat.prod_pow_factorization_centralBinom`: C(2n,n) = ∏_{p<2n+1} p^{v_p}; each factor ≤ 2n if p
   prime (`Nat.pow_factorization_choose_le`) and = 1 if p not prime (factorization 0). Hence
   C(2n,n) ≤ (2n)^{π(2n)}, so π(2n) ≥ (n log 4 − log 2n)/log 2n. With Y−2 < 2n ≤ Y:
   π(Y) ≥ (Y−2)·log 2/log Y − 1 ≥ 0.69·Y/log Y once 0.0031·Y ≥ 2 log 2 + log Y (Y ≥ 10^4 suffices).
   Upper: `Chebyshev.eventually_primeCounting_le` (ε = 0.01): π(Y/4) ≤ (log 4 + 0.01)(Y/4)/log(Y/4)
   ≤ 0.3491·Y/(0.95 log Y) ≤ 0.368·Y/log Y for large Y (log(Y/4) ≥ 0.95 log Y ⇔ Y ≥ 4^{20}).
   Difference ≥ 0.322·Y/log Y ≥ 0.3·Y/log Y. (Primes in (Y/4,Y] = π(⌊Y⌋) − π(⌊Y/4⌋).)

6. [r5b] [ELEM] euler_product_bounds. For every integer N ≥ 2:
   (EP) ∏_{p≤N prime} (1 − 1/p)^{-1} ≥ ∑_{n=1}^{N} 1/n ≥ log(N+1)   (`log_add_one_le_harmonic`);
   (EP1) ∏_{p≤z}(1 − 1/p) ≤ 1/log z for real z ≥ 2;
   (EP2) ∑_{p≤y} 1/p ≥ log log y − 1 for real y ≥ 3; hence S = ∑_{P0<p≤y} 1/p ≥ loglog y − 6.
   Proof of (EP): (1−1/p)^{-1} = ∑_{j≥0} p^{−j} ≥ ∑_{j=0}^{N} p^{−j}; expand the finite product
   (`Finset.prod_sum`/induction over the primes): ∏_{p≤N}∑_{j≤N}p^{−j} = ∑ over exponent vectors
   (j_p) of 1/∏p^{j_p}; the map n ↦ (v_p(n))_{p≤N} is injective on [1,N] (unique factorization,
   v_p(n) ≤ N, all prime factors of n are ≤ N) with ∏ p^{v_p(n)} = n, so the sum is ≥ ∑_{n≤N}1/n.
   [Alternative: `EulerProduct.prod_filter_prime_geometric_eq_tsum_factoredNumbers` with
   f(n) = n^{−σ}, σ > 1, then σ → 1⁺ by continuity of the finite product and finite sum.]
   (EP1) apply (EP) with N = ⌊z⌋, log(⌊z⌋+1) ≥ log z. (EP2) log of (EP): ∑_{p≤N} log(p/(p−1))
   ≥ log log(N+1) ≥ loglog y; log(p/(p−1)) ≤ 1/(p−1) = 1/p + 1/(p(p−1)) (`Real.log_le_sub_one_of_pos`);
   ∑_{p≤N} 1/(p(p−1)) ≤ ∑_{n=2}^{N} (1/(n−1) − 1/n) ≤ 1. Finally ∑_{p≤101} 1/p ≤ ∑_{n=2}^{101}1/n
   ≤ log 101 < 5.

7. [r5c] [ELEM] mertens_upper_and_T. (M) For integer N ≥ 1: ∑_{p≤N} log p/p ≤ log N + log 4.
   (T) For real z ≥ 16: T_z := ∑_{p≤z} 1/p ≤ 6·log log z + 7.
   Proof (M): ∑_{n≤N} log n = ∑_{n≤N}∑_{d|n}Λ(d) (`ArithmeticFunction.vonMangoldt_sum`)
   = ∑_{d≤N} Λ(d)⌊N/d⌋ ≥ ∑_{p≤N} log p·(N/p − 1) = N·∑_{p≤N} log p/p − θ(N). Also
   ∑_{n≤N} log n = log N! ≤ N log N (`Nat.factorial_le_pow`). With θ(N) ≤ N log 4
   (`Chebyshev.theta_le_log4_mul_x`) divide by N.
   Proof (T): blocks I_i = ℙ ∩ (2^{2^i}, 2^{2^{i+1}}], i ≥ 0. For p ∈ I_i, log p ≥ 2^i log 2 so
   1/p ≤ (log p/p)/(2^i log 2); by (M) at N = 2^{2^{i+1}}: ∑_{I_i} log p/p ≤ 2^{i+1}log 2 + 2 log 2, so
   ∑_{I_i} 1/p ≤ 2 + 2^{1−i} ≤ 4. Primes ≤ z lie in {2} ∪ I_0 ∪ … ∪ I_J with J = ⌈log_2 log_2 z⌉−1
   ≤ log_2 log_2 z. So T_z ≤ 1/2 + 4(log_2 log_2 z + 1) ≤ 4.5 + 4(1.443·loglog z + 0.53) ≤ 6 loglog z + 7.

8. [r5d] [ELEM] brun_pure_sieve. For integers q ≥ 1, r, s ≥ 0, reals Y ≥ 1, z ≥ 2, with
   𝒬 = {p prime ≤ z : p ∤ q}, m = |𝒬|, T = ∑_{p∈𝒬}1/p:
   #{p ≤ Y prime : p ≡ r (mod q)} ≤ z + (Y/q)·(∏_{p∈𝒬}(1−1/p) + ∑_{j=2s+1}^{m} T^j/j!) + (m+1)^{2s}.
   Proof. (a) primes ≤ z: at most z. A prime p > z has no divisor in 𝒬. So LHS ≤ z + N_sift,
   N_sift = #{n ∈ [1,Y] : n ≡ r (q), no p ∈ 𝒬 divides n}.
   (b) Bonferroni: for a finite set E (E = {p ∈ 𝒬 : p | n}), ∑_{D⊆E,|D|≤2s}(−1)^{|D|} ≥ [E = ∅].
   Indeed it equals ∑_{j=0}^{2s}(−1)^j C(|E|,j); for |E| = M ≥ 1, ∑_{j=0}^{t}(−1)^j C(M,j) =
   (−1)^t C(M−1,t) (induction on t via Pascal C(M,j) = C(M−1,j) + C(M−1,j−1)), which is ≥ 0 at
   t = 2s; for E = ∅ it is 1. (`Finset.card_powersetCard`, `Int.alternating_sum_range_choose` for
   the full sum.)
   (c) Summing (b) over n and swapping: N_sift ≤ ∑_{D⊆𝒬,|D|≤2s}(−1)^{|D|}·N_D,
   N_D = #{n ∈ [1,Y] : n ≡ r (q), ∏D | n}. gcd(∏D, q) = 1 ⇒ (CRT, `Nat.chineseRemainder`) the two
   conditions are one residue class mod q∏D ⇒ |N_D − Y/(q∏D)| ≤ 1 (`Nat.count_modEq_card` /
   `Nat.Ico_filter_modEq_card`). Hence N_sift ≤ (Y/q)∑_{|D|≤2s}(−1)^{|D|}/∏D + #{D : |D| ≤ 2s}.
   (d) ∑_{D⊆𝒬}(−1)^{|D|}/∏D = ∏_{p∈𝒬}(1 − 1/p) (`Finset.prod_one_add`, f = −1/p). So the
   truncated sum = ∏(1−1/p) − ∑_{|D|>2s}(−1)^{|D|}/∏D ≤ ∏(1−1/p) + ∑_{j>2s} e_j(𝒬), and
   e_j(𝒬) = ∑_{|D|=j}1/∏D ≤ T^j/j! (T^j = ∑ over j-tuples ≥ j!·e_j, or by the recursion
   j·e_j ≤ T·e_{j−1}).
   (e) #{D ⊆ 𝒬 : |D| ≤ 2s} = ∑_{j≤2s} C(m,j) ≤ (m+1)^{2s}.

9. [r5e] [ELEM] brun_titchmarsh_weak. ∃Y2, ∀ real Y ≥ Y2, ∀ integers q with 1 ≤ q ≤ Y^{1/3}, ∀ r:
   #{p ≤ Y prime : p ≡ r (mod q)} ≤ C_BT·(loglog Y)·Y/(φ(q)·log Y),  C_BT = 203.
   Proof. ℓ := loglog Y. Apply r5d with z = Y^{1/(200ℓ)} (log z = log Y/(200ℓ)) and
   2s := 2⌈25ℓ⌉ + 52 (so 50ℓ + 52 ≤ 2s ≤ 50ℓ + 54).
   * Product: ∏_{p∈𝒬}(1−1/p) = ∏_{p≤z}(1−1/p) / ∏_{p≤z,p|q}(1−1/p) ≤ (1/log z)·(q/φ(q))
     [(EP1); ∏_{p|q,p≤z}(1−1/p) ≥ ∏_{p|q}(1−1/p) = φ(q)/q, `Nat.totient_mul_prod_primeFactors`]
     = (q/φ(q))·200ℓ/log Y.
   * Tail: T ≤ T_z ≤ 6 loglog z + 7 ≤ 6ℓ + 7 (r5c), so every j ≥ 2s+1 has j ≥ e²T (e² < 7.39,
     7.39(6ℓ+7) < 50ℓ + 52). j! ≥ (j/e)^j (`Real.pow_div_factorial_le_exp` at x = j) ⇒
     T^j/j! ≤ (eT/j)^j ≤ e^{−j}. ∑_{j≥2s+1} e^{−j} ≤ 2e^{−2s} ≤ 2(log Y)^{−50} ≤ 1/log Y.
   * Error: (m+1)^{2s} ≤ z^{2s} = Y^{2s/(200ℓ)} ≤ Y^{(50ℓ+54)/(200ℓ)} ≤ Y^{1/2} (ℓ ≥ 2).
   * Total ≤ z + Y^{1/2} + (Y/φ(q))(200ℓ + 1)/log Y. Since φ(q) ≤ q ≤ Y^{1/3},
     Y/(φ(q) log Y) ≥ Y^{2/3}/log Y ≥ Y^{1/2} ≥ z for large Y, so total ≤ (200ℓ + 3)·Y/(φ(q)log Y)
     ≤ 203ℓ·Y/(φ(q) log Y).

10. [r5f] [ELEM] stirling_upper. For k ≥ 1: k! ≤ e·√k·(k/e)^k.
   Proof. `Stirling.stirlingSeq'_antitone` (stirlingSeq ∘ succ antitone) and
   `Stirling.stirlingSeq_one` (= e/√2): stirlingSeq k ≤ e/√2, i.e.
   k! ≤ (e/√2)·√(2k)·(k/e)^k = e√k(k/e)^k.

11. [r6] [ELEM] esymm_lower. For a finite set 𝒫 of primes all > P0 with S = ∑_{p∈𝒫}1/p ≥ k/P0,
   e_j := ∑_{D⊆𝒫,|D|=j} ∏_{p∈D}1/p satisfies j·e_j ≥ e_{j−1}·(S − (j−1)/P0) for 1 ≤ j, hence
   e_k ≥ (S − k/P0)^k / k!.
   Proof. ∑_{D:|D|=j−1} (∏_D 1/p)·∑_{p∈𝒫∖D} 1/p = j·e_j (each j-set E arises from exactly j pairs
   (E∖{p}, p)); and ∑_{p∉D}1/p = S − ∑_{p∈D}1/p ≥ S − (j−1)/P0. Induct; each factor
   S − (j−1)/P0 ≥ S − k/P0 ≥ 0.

12. [r7] [CRUX] [ELEM-assembly] lower_bound (★). Fix L ∈ 20ℕ, L ≥ L*, x = exp(e^L), notation above.
   (a) Sizes: k = 9L/20 ≥ 1; y = exp(e^L/(4k)) > 10^4 > P0; b ≤ y^k = x^{1/4}; Y = x/b ≥ x^{3/4};
       every divisor B of b satisfies B ≤ x^{1/4} ≤ Y^{1/3}; Y/4 ≥ x^{3/4}/4 > y.
   (b) For b ∈ 𝓑: primes a ∈ (Y/4, Y] number ≥ c1·Y/log Y (r5a, Y ≥ Y1). Non-GOOD ones (r4 + r5e,
       modulus B = b/d, B/φ(B) = ∏_{p|B} p/(p−1) ≤ ρ^k since all p > P0, loglog Y ≤ L):
       ≤ ∑_{d} 2δB·C_BT·L·Y/(φ(B) log Y) ≤ 2^k·2δρ^k C_BT L·Y/log Y = (c1/8)·Y/log Y.
       So GOOD primes in (Y/4, Y] ≥ (7/8)c1 Y/log Y ≥ (c1/2)·x/(b·log x) (log Y ≤ log x).
   (c) Each GOOD a satisfies a > y (so a ∤ b) and n = ab ∈ (x/4, x], and by r3
       t_2(n) ≥ δn − 1 ≥ δx/4 − 1 ≥ δx/8 (needs δx ≥ 8; δ ≥ e^{−L} for large L since
       2^{k+1}ρ^k·8·C_BT·L/c1 = O(L·(2.02)^{0.45L}) = O(L e^{0.317L})).
   (d) (a,b) ↦ ab is injective on {(a,b) : b ∈ 𝓑, a prime > y}: if ab = a'b', a | a'b', a ∤ b'
       (all primes of b' are ≤ y < a) ⇒ a = a' ⇒ b = b'. t_2 ≥ 0 on the rest of Icc 1 ⌊x⌋.
       F(x) ≥ ∑_{b∈𝓑} (c1/2)(x/(b log x))·(δx/8) = (c1δ/16)·(x²/log x)·e_k.
   (e) S ≥ loglog y − 6 = L − log(4k) − 6 = L − log(9L/5) − 6 (r5b). For L ≥ L*: S ≥ 0.99L ≥ k,
       and S − k/P0 ≥ 0.99L − 0.0045L ≥ 0.985L. By r6 and r5f:
       e_k ≥ (0.985L)^k/k! ≥ (0.985L·e/k)^k/(e√k) = (0.985·e·20/9)^k/(e√k) = (5.950)^k/(e√k).
   (f) δ·e_k ≥ c1/(16·C_BT·L·e√k)·(5.950/(2ρ))^k ≥ c1/(16·203·e·L^{3/2})·(2.945)^k.
       (2.945)^k = exp(k·log 2.945) ≥ exp(0.45L·1.080) = (log x)^{0.486}.
   (g) F(x) ≥ (c1²/(256·203·e))·x²·(log x)^{−1+0.486}/L^{3/2} = c'·x²(log x)^{−0.514}/L^{3/2}.
       Since (log x)^{2/3−0.514} = e^{0.152L} > L^{3/2}/c' for L ≥ L*, F(x) > x²/(log x)^{2/3}. ∎

   Lean hints. Work with the single variable L: all "large x" thresholds (Y1 from r5a, Y2 from
   r5e, the inequalities in (a),(c),(e),(g)) become "L ≥ L_i", each an eventual statement in L
   (`Filter.eventually_atTop`, `tendsto` of polynomial·exp). Everything auxiliary can be stated
   as universally-quantified `have` blocks inside the single disproof declaration, in the order
   r2, r3, r4, r5a, r5b, r5c, r5d, r5e, r5f, r6, r7.

## 4. Supporting Evidence & Positive Test Cases
Round-1 evidence (still valid): scratch/numerics.py, scratch/structure_check.py — r2's root formula
vs brute force on 281 random pairs; r4 class bound e.g. b = 7·11·13·17·19, δ = 2^{-8}: bad 28802 ≤
80830.8; F(x)/x²·(log x)^{log 2} ≈ 0.70 non-decreasing up to 3·10^6.
New (scratch/checks_r2.py, all asserts pass):
* E1 Bonferroni ∑_{j≤2s}(−1)^jC(m,j) = C(m−1,2s) ≥ 0 (m ≥ 1), = 1 (m = 0): m < 30, s < 16.
* E2 z = 3,10,…,10^6: ∏_{p≤z}(1−1/p) = 0.3333, 0.2286, 0.1203, 0.0810, 0.0609, 0.0488, 0.0406
  ≤ 1/log z = 0.910, 0.434, 0.217, 0.145, 0.109, 0.087, 0.072; ∑_{p≤z}1/p ≥ loglog z − 1
  (e.g. z=10^6: 2.887 ≥ 1.626); T-bound 1/2+4(log2log2 z+1) holds (21.77 ≥ 2.887).
* E3 ∑_{p≤N} log p/p ≤ log N + log 4 for N = 2..10^6 (e.g. 12.48 ≤ 15.20 at 10^6).
* E4 min_{100≤Y<10^6} (π(Y) − π(Y/4))/(Y/log Y) = 0.7368 ≥ 0.3.
* E5 e_k recursion and e_k ≥ (S−k/P0)^k/k!, e_k ≤ S^k/k! exactly (Fractions) for primes in (101,400].
* E6 Brun pure sieve inequality (r5d) checked directly: (q,Y,z,s) = (7,2·10^4,30,3): 526 ≤ 999.3;
  (143,5·10^4,20,2): 71 ≤ 140.8; (1,3·10^4,40,4): 4456 ≤ 8265.1; (105,4·10^4,25,3): 138 ≤ 200.3.
* E7 ∏_{p≤z,p∤q}(1−1/p) ≤ (q/φ(q))∏_{p≤z}(1−1/p) for q ∈ {1,6,105,1001,30030}.
* E8 log k! ≤ 1 + ½log k + k log k − k for k < 200.
* E9 r3 with the per-divisor GOOD definition: 136 random good (a prime, b squarefree) pairs, all
  t_2(ab) ≥ δab − 1; and t_2(n) ≤ n−1 on all 300 samples.
Exponent arithmetic: 0.985·e·20/9 = 5.950; /(2·1.01) = 2.945; log 2.945 = 1.0802;
0.45·1.0802 = 0.4861; 1 − 0.4861 = 0.514 < 2/3 (margin 0.152).

## 5. Adversarial Refutation & Falsification Attempts
* Lean loopholes: t 2 n uses m > 0, so t_2(1) = 1 and t_2(n) ≥ 1; n = 0 excluded by Icc 1.
  (log x)^{2/3} is rpow of a positive base for x > 1. No degenerate reading makes the target true.
* Could the target hold after all? No: every step is either exact CRT (r2–r4, brute-force checked)
  or an upper bound for primes in progressions (only upper bounds used), plus a Chebyshev lower
  bound; no equidistribution assumption anywhere.
* r4 when δB < 1 (small B): U_bad = ∅ (u ≥ 1 > δB and u ≤ B−1 < (1−δ)B); bound 2δB still true.
* r5e uniformity: q ranges up to Y^{1/3}; the "+1" error per class is absorbed because
  Y/(q∏D) terms are summed with (m+1)^{2s} ≤ Y^{1/2} total error; checked E6 at small scale.
* r5e tail: requires 2s + 1 ≥ e²·T with T ≤ 6ℓ + 7; with 2s ≥ 50ℓ + 52 > 7.39(6ℓ+7) = 44.3ℓ + 51.7 ✓.
  Error: needs 2s/(200ℓ) ≤ 1/2, i.e. 50ℓ + 54 ≤ 100ℓ ⇔ ℓ ≥ 1.08 ✓ for large Y.
* Crude k! ≤ k^k would lose e^k and kill the gain (0.45·log(0.985·20/(9·2.02)) ≈ 0.036): Stirling
  (r5f) is necessary and available.
* Mertens with only α·loglog (α < 1) would still work if α > 0.62, but (EP2) gives α = 1 cheaply.
* Brun loses loglog Y only: absorbed by L in δ (costs L^{3/2} in (g), dominated by e^{0.152L}).
* Choosing x = exp(e^L) is legitimate: the little-o bound holds for ALL x ≥ X, so one x suffices.

## 6. Freshness & Anti-Recycling Audit
Root node; no children ever created; get_accessible_nodes returns none; §10 empty. No citations of
unproved nodes. This is a refutation plan (the target is false), so no [LEMMA] children can be
proposed: a planned decomposition would require proving the false target from true lemmas.

## 7. Open Risks
* Size: the full formalization is still large (est. 1500–2500 lines) and must live in ONE
  disproof declaration (4M heartbeats, no subgoal block). The mathematics is complete; the risk is
  purely engineering. If the pipeline could accept auxiliary proved lemmas for a disproof, the
  natural lemmas are r2/r3, r4, r5a, r5b, r5c+r5d+r5e, r5f+r6, each independent.
* r5b (EP) finite Euler-product expansion is the most fiddly formal step; two routes given.
* Asymptotic bookkeeping in r7 — reduce everything to "∀ᶠ L in atTop".
