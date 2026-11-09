# Blueprint: `erdos_1101.parts.ii`
Revision: 2

> **What changed from revision 1.** Revision 1 committed to an explicit witness
> (`refine ⟨witnessU, …⟩`). The reviewer retired it with `SHAPE:`, and
> `nodes/witnessU_gap_bound/findings.md` now *proves* that this is fatal for
> **every** explicit witness (R2‑degenerate G3, Lemma M G9, Lemma S + Corollary T
> G10, R5‑closed G11, R6‑closed G12). Revision 2 therefore **never names a
> witness**: the sequence is produced by a probabilistic existence argument, and
> every step id below is new. No step of revision 1 survives except the already
> **proved** `nth_prime_poly_bound`, which is *not* re‑derived (it is superseded
> by the strictly stronger `[s1]`; see §6 for why re‑deriving is unavoidable and
> why it is not recycling).

---

## 1. Statement

```lean
theorem erdos_1101.parts.ii :
  ∃ u, IsGood u ∧ (fun n => Real.log (u n : ℝ)) =o[atTop] (fun n => (n : ℝ))
```
with, from `problem.lean`,

* `ASet u = {a : ℕ | ∀ i, ¬ u i ∣ a}`, `A u n = Nat.nth (· ∈ ASet u) n`,
* `t u x = sSup {k | ∏_{i ∈ range k} u i ≤ x}`,
* `IsGood u` = `StrictMono u` ∧ pairwise `Coprime` ∧ `Summable (1/u n)` ∧
  `∀ ε>0, ∀ᶠ x, ∀ k, A u k < x → A u (k+1) − A u k < (1+ε)·t_x·(∏'(1−1/u_i))⁻¹`.

In ordinary mathematics: **there is a strictly increasing, pairwise coprime
sequence of integers with convergent reciprocal sum, whose sieved complement
`A(u)` has maximal gap below `x` at most `(1+ε)·t_x/D` for every `ε>0` and all
large `x`, and which satisfies `log u_n = o(n)`.** This is Erdős problem
**#1101, part (ii)** verbatim.

**Calibration.** This is *not* "one solid lemma". erdosproblems.com listed it
OPEN with "Proof claims (0)" as of 2026‑09‑27 (findings F0, G0); the only known
proof is **Peter Li, "A Subexponential Good Sequence", 27 Apr 2026** (attached at
`erdosproblems.com/1101` by user `lipet2k`, **unrefereed**, AI‑assisted), text
recovered at `nodes/witnessU_gap_bound/scratch/proof_text5.txt`. The proof has
two clearly separated halves (a deterministic sieve reduction and a
first‑moment/Borel–Cantelli argument) plus three genuinely independent technical
inputs (a Chebyshev prime bound, an elementary‑symmetric Chernoff bound, a
divisor count). It is comparable in size to a short research paper, not to a
textbook exercise. **Eight separable claims is the honest count**, and that is
what §3 produces. The difficulty is *not* uniformly distributed: it sits in
`[s7]`, which is tagged `[CRUX]`.

---

## 2. Strategy

**One sentence:** do not choose the sequence — choose a *pool* `P_n` of primes for
each `n`, pick `u_n ∈ P_n` at random and independently, and show by a first
moment plus Borel–Cantelli that almost every outcome is good.

Why this and nothing else. A covered window of length `L ≈ (1+ε)t_x/D` forces a
CRT system on `r ≥ (1+ε)t_x` distinct moduli whose modulus `U = ∏ u_{i_ν}`
satisfies **`U > x`** (Theorem R2‑degenerate, `witnessU_gap_bound/findings.md`
G3). For a *fixed* sequence the number of solutions below `x` is `⌊x/U⌋+θ ∈
{0,1}` — the main term `x/U` is *gone*, and every deterministic method
(multiplicativity R1, union bound R2, upper‑bound sieve R3, the whole factorial
moment hierarchy R5, Gallagher's larger sieve R6) is thereby closed **by proof**,
for every admissible `u`, in G2–G12. Randomising the moduli restores the main
term: the weight of a certificate becomes a genuine product of independent
probabilities `∏_ν P(u_{i_ν} ∣ n+j_ν) ≈ 1/U`, and the heuristic that G3 verified
numerically becomes a theorem. **Randomness is the missing arithmetic input, not
a convenience.**

Two deviations from Li that I own (both verified below, §4/§5):

1. **No prime number theorem.** Li's pools are the primes in the short interval
   `[e^{√n}, e^{√n+1/(10√n)}]`, counted with PNT + de la Vallée Poussin.
   **Mathlib has no PNT** (probed: `Nat.primeCounting_isEquivalent`,
   `Nat.primeCounting_asymptotic` unknown). I replace the pools by **consecutive
   blocks of the prime sequence**: with `M n := ⌈e^{√n}⌉ + n`, put
   `P_n := {p_k : M n ≤ k < M (n+1)}`. Ordering, disjointness and `|P_n| = M(n+1)−M n`
   are then *definitional*, and the **only** prime‑counting input left is the
   Chebyshev bound `p_k ≤ C·k·log k` (`[s1]`). This is strictly simpler than the
   dyadic block cut of G17, which still needed `π(4Y)−π(Y) ≫ Y/log Y`.
2. **Repaired Chernoff step.** Li's `e_M` summation uses `log(1+w) ≤ w`, which is
   invalid for `i ≤ M` where `z·y_i ≥ 1`. `[s4]` uses the correct split
   `log(1+w) ≤ log 2 + log w` for `w ≥ 1`, which gives the same exponent
   `−(2b/3)M^{3/2} + O(M)` (numerically confirmed, §4 Table E4/E4b).

Sources: Li (2026) as above for §3.7/§3.8; the closure of all deterministic
routes is `nodes/witnessU_gap_bound/findings.md` G2–G13; the Chebyshev
ingredients are the ones already used in the **proved** `nth_prime_poly_bound`
(`nodes/nth_prime_poly_bound/proof_scaffold.lean`).

**Indexing translation table (mandatory — Li is 1‑indexed, Lean is 0‑indexed).**

| Li | Lean | note |
|---|---|---|
| `u_1 < u_2 < ⋯` | `u 0 < u 1 < ⋯` | `u_n` (Li) `= u (n−1)` (Lean) |
| `P_t = u_1⋯u_t` | `∏ i ∈ Finset.range t, u i` | same number of factors ⇒ `t_x` identical |
| `P_{t_x} ≤ x < P_{t_x+1}` | `t u x = sSup {k | ∏_{i<k} u i ≤ x}` | identical (findings F1: the `sSup` is an honest max) |
| `log u_n = √n + O(n^{−1/2})` | `log (u n) = √n·(1+o(1))` | our pools give relative, not additive, accuracy — §4 Table E1c; §5 FP‑2 shows relative accuracy is enough |
| `Σ_{n≤t} log u_n = (2/3)t^{3/2}+O(√t)` | `Σ_{i ∈ range t} log (u i) ≤ (2/3+o(1))t^{3/2}` | `[s5]` |
| `max_{a_k<x}(a_{k+1}−a_k) < (1+ε)t_xD^{−1}` | conjunct 4 of `IsGood` | character‑for‑character (G14) |

---

## 3. Proof

### 3.0 New definitions (to be placed in the `START_DEFINITIONS` block)

```lean
/-- A *certificate* for `u` with parameters `(N, M, K, Q)`: an integer `n < N`,
a set `S` of exactly `M` indices, all `> K`, and for each `i ∈ S` a position
`j i ∈ [1, Q]` with `u i ∣ n + j i`.  (Positions need not be distinct.) -/
def HasCert (u : ℕ → ℕ) (N M K Q : ℕ) : Prop :=
  ∃ n : ℕ, n < N ∧ ∃ S : Finset ℕ, ∃ j : ℕ → ℕ,
    S.card = M ∧ (∀ i ∈ S, K < i) ∧ (∀ i ∈ S, 1 ≤ j i ∧ j i ≤ Q) ∧
    (∀ i ∈ S, u i ∣ n + j i)

/-- `P n` is a nonempty finite set of primes and every element of `P n` is
smaller than every element of `P (n+1)`. -/
def IsPools (P : ℕ → Finset ℕ) : Prop :=
  (∀ n, (P n).Nonempty) ∧ (∀ n, ∀ p ∈ P n, Nat.Prime p) ∧
  (∀ n, ∀ p ∈ P n, ∀ q ∈ P (n + 1), p < q)

/-- Every element of `P n` has logarithm `√n·(1+o(1))`. -/
def PoolsLog (P : ℕ → Finset ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    ∀ p ∈ P n, |Real.log p - Real.sqrt n| ≤ δ * Real.sqrt n

/-- The pools are almost as large as their largest element. -/
def PoolsBig (P : ℕ → Finset ℕ) : Prop :=
  ∀ β : ℝ, β < 1 → ∀ᶠ n : ℕ in atTop, ∀ p ∈ P n, (p : ℝ) ^ β ≤ ((P n).card : ℝ)
```

Three elementary monotonicity facts about `HasCert`, used in the glue and proved
inline in one line each:

* **(H1)** `HasCert u N M K Q → N ≤ N' → HasCert u N' M K Q` (weaken `n < N`).
* **(H2)** `HasCert u N M K' Q → K ≤ K' → HasCert u N M K Q` (`K < i` follows from `K' < i`).
* **(H3)** `HasCert u N M K Q → M' ≤ M → HasCert u N M' K Q` (take `S' ⊆ S` with `|S'| = M'`,
  `Finset.exists_subset_card_eq`).

---

### 3.1 Step list

1. **[s1] [LEMMA]** `nth_prime_linearithmic : ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 2 ≤ k → (Nat.nth Nat.Prime k : ℝ) ≤ C * k * Real.log k`

   *Why it is needed and why `nth_prime_poly_bound` does not suffice.* §6 of the
   plan requires pools with `|P_n| ≥ (max P_n)^β` for **every** `β < 1`; §5 FP‑1
   proves that a fixed `β₀ < 1` makes the decisive inequality unsolvable. The
   block‑cut pools satisfy `|P_n| ≥ (max P_n)^β` iff `p_k ≤ k^{1+o(1)}`, and
   `p_k ≤ k^C` (the proved lemma) only gives `p_k ≤ k^6`, hence only `β < 1/6`.
   So the strictly stronger Chebyshev bound is forced. It is **not** a
   re‑derivation of the proved lemma: it is a different, stronger statement, and
   the proved one is a corollary.

   *Full proof.* All ingredients are already assembled, kernel‑checked, in
   `nodes/nth_prime_poly_bound/proof_scaffold.lean`; steps (A),(B) below are
   **verbatim** that file's `hA`, `hB`.

   (A) For `n > 0`, `Nat.centralBinom n ≤ (2n)^{|primeFactors (centralBinom n)|}`.
   Proof: `Nat.factorization_prod_pow_eq_self` writes `centralBinom n = ∏_{p ∈ primeFactors} p^{ν_p}`,
   `Nat.pow_factorization_choose_le` gives `p^{ν_p} ≤ 2n`, and
   `Finset.prod_le_pow_card` finishes.

   (B) `|primeFactors (centralBinom n)| ≤ Nat.count Nat.Prime (2n+1)`:
   every such `p` is prime and `p ≤ p^{ν_p} ≤ 2n < 2n+1`.

   (C) `Nat.four_pow_le_two_mul_self_mul_centralBinom : 0 < n → 4^n ≤ 2n·centralBinom n`.
   Combining (A),(B),(C) with `π* := Nat.count Nat.Prime (2n+1)`:
   `4^n ≤ 2n·(2n)^{π*} = (2n)^{π*+1}`, hence over `ℝ`
   `n·log 4 ≤ (π*+1)·log(2n)`.   (★1)

   (D) Fix `k ≥ 2` and put `L := ⌈log(k+2)⌉₊ + 1 ≥ 1`, `n := 3(k+1)L`. Then
   `n·log 4 > (k+1)·log(2n)`. Indeed `log 4 > 1.386` so
   `n log 4 > 4.15(k+1)L`, while
   `log(2n) = log 6 + log(k+1) + log L ≤ 1.792 + (L−1) + log L`
   (using `log(k+1) ≤ log(k+2) ≤ L−1`), so it suffices that
   `4.15 L > 0.792 + L + log L`, i.e. `3.15 L > 0.792 + log L`, true for every
   `L ≥ 1` (at `L = 1`: `3.15 > 0.792`; the left side grows faster since
   `3.15 > 1/L`). Combining with (★1), `π* + 1 > k + 1`, i.e.
   `Nat.count Nat.Prime (2n+1) > k`, so by `Nat.nth_lt_of_lt_count`,
   `p_k < 2n+1`.

   (E) `2n+1 = 6(k+1)L + 1 ≤ 50·k·log k` for `k ≥ 2`: `k+1 ≤ 1.5k`, and
   `L ≤ log(k+2)+2 ≤ log k + 3 ≤ (1 + 3/log 2)·log k ≤ 5.4 log k` for `k ≥ 2`,
   and `k log k ≥ 2 log 2 > 1`, so
   `6(k+1)L + 1 ≤ 6·1.5k·5.4 log k + 1 ≤ 48.6 k log k + k log k = 49.6 k log k`.
   Take `C := 50`. ∎  *(Table E5 verifies (D) and (E) numerically for
   `k = 2,3,5,10,50,200,1000,5000` and checks the ratio in (D) stays ≥ 2.9 up to
   `k = 10^16`.)*

2. **[s2] [LEMMA]** `good_seq_pools_exist (C : ℝ) (hC : 0 < C) (hp : ∀ k : ℕ, 2 ≤ k → (Nat.nth Nat.Prime k : ℝ) ≤ C * k * Real.log k) : ∃ P : ℕ → Finset ℕ, IsPools P ∧ PoolsLog P ∧ PoolsBig P`

   *Full proof (explicit construction).* Put

   ```
   M n := ⌈exp (√n)⌉₊ + n ,        P n := (Finset.Ico (M n) (M (n+1))).image (Nat.nth Nat.Prime).
   ```

   * **`M` strictly monotone.** `√·` is monotone and `exp` is monotone, so
     `⌈exp √n⌉₊ ≤ ⌈exp √(n+1)⌉₊`; adding `n < n+1` gives `M n < M (n+1)`.
     *(This is why the `+ n` is there: it removes any need to check
     `exp √(n+1) − exp √n > 1` by hand. Table E1 confirms strict monotonicity of
     `⌈exp √n⌉₊` alone for `n ≤ 20000`, but we do not rely on it.)*
   * **`IsPools P`.** Nonempty: `Finset.Ico (M n) (M (n+1))` is nonempty and
     images of nonempty sets are nonempty. Primes: `Nat.prime_nth_prime`.
     Ordered: if `p = p_a` with `a < M (n+1)` and `q = p_b` with `M (n+1) ≤ b`,
     then `a < b`, so `p < q` by `Nat.nth_strictMono Nat.infinite_setOf_prime`.
   * **Cardinality.** `Nat.nth Nat.Prime` is injective (strictly monotone), so
     `|P n| = M (n+1) − M n` (`Finset.card_image_of_injective`, `Nat.card_Ico`).
   * **Two‑sided size of `M`.** `exp √n ≤ M n ≤ exp √n + 1 + n ≤ 3 exp √n`
     (the last step for `n ≥ 1`, since `n + 1 ≤ 2 exp √n`; check `n=1`: `2 ≤ 2e`).
   * **Lower bound for `|P n|`.**
     `M(n+1) − M n ≥ exp √(n+1) − (exp √n + 1 + n) + (n+1) = exp √(n+1) − exp √n ≥ exp(√n)·(√(n+1) − √n) = exp(√n)/(√(n+1)+√n) ≥ exp(√n)/(3√n)` for `n ≥ 1`
     (using `e^a − e^b ≥ e^b(a−b)` from `Real.add_one_le_exp`, and `√(n+1) ≤ 2√n`
     for `n ≥ 1`). Hence
     **`log |P n| ≥ √n − log(3√n)`.**  (★2)
   * **`PoolsLog P`.** Let `p ∈ P n`, `p = p_a` with `M n ≤ a < M (n+1)`.
     Lower: `p_a ≥ a ≥ M n ≥ exp √n` (`Nat.nth_strictMono.le_apply`), so
     `log p ≥ √n`.
     Upper: by `hp`, `p_a ≤ C·a·log a ≤ C·M(n+1)·log M(n+1) ≤ 3C·exp(√(n+1))·(√(n+1)+log 3)`,
     so `log p ≤ √(n+1) + log(3C) + log(√(n+1) + log 3) ≤ √n + 1 + log(3C) + log(√n + 2)`.
     Therefore `0 ≤ log p − √n ≤ log(√n+2) + 1 + log(3C) = O(log n)`, which is
     `≤ δ√n` for all `n ≥ n₁(δ, C)`. ✔ *(Table E1c: the worst relative error drops
     from `1.80` at `n=10` to `1.3·10⁻³` at `n=10⁸` and `1.8·10⁻⁵` at `n=10¹²`.)*
   * **`PoolsBig P`.** If `β ≤ 0` then `p^β ≤ 1 ≤ |P n|`. If `0 < β < 1`, use (★2)
     and the `PoolsLog` upper bound: we need
     `√n − log(3√n) ≥ β(√n + 1 + log(3C) + log(√n+2))`,
     i.e. `(1−β)√n ≥ log(3√n) + β(1 + log 3C + log(√n+2))`.
     The left side is `≍ (1−β)√n`, the right side is `O(log n)`, so this holds for
     all `n ≥ n₂(β, C)`. ✔ *(Table E1b, in log space: at `β = 0.99` the crossover is
     near `n = 10⁷`, at `β = 0.5` near `n = 500`. The crossover moving right as
     `β ↑ 1` is exactly the `∀β<1, ∀ᶠ n` shape, and is why the statement cannot be
     strengthened to a uniform `n`.)* ∎

3. **[s3] [LEMMA]** `prime_divisor_count_bound (N m : ℕ) (hN : 1 ≤ N) (hm : 2 ≤ m) : ((N.primeFactors.filter (fun p => m ≤ p)).card : ℝ) ≤ Real.log N / Real.log m`

   *Full proof.* Let `T := N.primeFactors.filter (m ≤ ·)` and `r := |T|`. The
   elements of `T` are distinct primes each dividing `N`, so
   `∏_{p ∈ T} p ∣ N` (`Nat.prod_primeFactors_dvd` restricted to a subset, or
   `Finset.prod_primes_dvd`), hence `∏_{p ∈ T} p ≤ N` (as `N ≥ 1`). Each factor is
   `≥ m`, so `m^r ≤ ∏_{p∈T} p ≤ N` (`Finset.pow_card_le_prod`). Taking `Real.log`
   (monotone, `m ≥ 2 > 1` so `log m > 0`): `r·log m ≤ log N`, i.e.
   `r ≤ log N / log m`. ∎

4. **[s4] [LEMMA]** `esym_geom_bound (b δ : ℝ) (hb : 0 < b) (hδ : 0 < δ) : ∀ᶠ M : ℕ in atTop, ∀ I : Finset ℕ, ∑ S ∈ I.powersetCard M, ∏ i ∈ S, Real.exp (-(b * Real.sqrt i)) ≤ Real.exp (-(1 - δ) * (2 * b / 3) * (M : ℝ) ^ ((3:ℝ)/2))`

   *Full proof.* Write `y_i := exp(−b√i) ∈ (0,1]` and set `z := exp(b√M) > 0`.

   (a) **Algebraic Chernoff.** For every finite `I`,
   `z^M · Σ_{S ∈ I.powersetCard M} ∏_{i∈S} y_i = Σ_{|S|=M} ∏_{i∈S}(z y_i) ≤ Σ_{S ⊆ I} ∏_{i∈S}(z y_i) = ∏_{i∈I}(1 + z y_i)`,
   the last equality being `Finset.prod_add` with `f i := z y_i`, `g i := 1` (all
   terms nonnegative, so dropping the subsets of size `≠ M` only increases).
   Hence `Σ_{|S|=M} ∏_{i∈S} y_i ≤ z^{−M} ∏_{i∈I}(1 + z y_i)`.

   (b) **Uniformity in `I`.** `log(1+z y_i) ≥ 0` and `Σ_{i∈ℕ} log(1+z y_i) ≤ Σ_i z e^{−b√i} < ∞`
   (comparison with `Σ e^{−b√i}`, convergent since `e^{b√i} ≥ (b√i/4)^4/4!`‑type
   growth beats `i²`). So by `Summable.sum_le_tsum` (probed: the name
   `Finset.sum_le_tsum` does **not** exist; the real signature is
   `Summable.sum_le_tsum (s : Finset ι) : (∀ i ∉ s, 0 ≤ f i) → Summable f → ∑ i ∈ s, f i ≤ ∑' i, f i`),
   `Σ_{i∈I} log(1+z y_i) ≤ Σ_{i=0}^{∞} log(1 + z y_i) =: Λ(M)` for **every** `I`.

   (c) **Bounding `Λ(M)`.** Put `w_i := z y_i = exp(b(√M − √i))`.
   * `i ≤ M`: `w_i ≥ 1`, so `log(1+w_i) ≤ log(2w_i) = log 2 + b(√M − √i)`. Summing,
     `Σ_{i=0}^{M} log(1+w_i) ≤ (M+1)log 2 + b[(M+1)√M − Σ_{i=0}^{M}√i]`.
     By `[s5]` (lower half, with `m = M+1`), `Σ_{i=0}^{M}√i ≥ (2/3)(M+1)^{3/2} − √(M+1) ≥ (2/3)M^{3/2} − √(M+1)`,
     so this is `≤ (M+1)log 2 + b[M√M + √M − (2/3)M^{3/2} + √(M+1)] = (b/3)M^{3/2} + O(M)`.
   * `i > M`: `log(1+w_i) ≤ w_i = e^{−b(√i−√M)}`, and
     `√i − √M = (i−M)/(√i+√M) ≥ (i−M)/(2√i)`. Comparing the decreasing function
     `x ↦ e^{−b(√x−√M)}` with its integral from `M`,
     `Σ_{i>M} e^{−b(√i−√M)} ≤ ∫_M^∞ e^{−b(√x−√M)}dx = ∫_0^∞ e^{−bs}·2(√M+s)ds = 2√M/b + 2/b²`.
   * Total: `Λ(M) ≤ (b/3)M^{3/2} + K_b·(M+1)` with the explicit constant
     `K_b := log 2 + 2b + 2/b + 2/b² + 1`.

   (d) **Conclusion.** `z^{−M} = e^{−bM^{3/2}}`, so
   `log(bound) ≤ −bM^{3/2} + (b/3)M^{3/2} + K_b(M+1) = −(2b/3)M^{3/2} + K_b(M+1)`.
   The claim `≤ −(1−δ)(2b/3)M^{3/2}` therefore holds as soon as
   `δ(2b/3)M^{3/2} ≥ K_b(M+1)`, i.e. for all `M ≥ (3K_b/(bδ))² + 1`. ∎
   *(Tables E4 and E4b: the exact `e_M` is below the Chernoff bound in every
   sampled case, and `(log e_M − (−(2b/3)M^{3/2}))/M` is bounded — it decreases
   from `2.48` at `M=1` to `0.145` at `M=800` — confirming the excess is `O(M)`,
   i.e. `o(M^{3/2})`. The naive `log(1+w) ≤ w` step is genuinely wrong here: at
   `b = 0.5, M = 10` it would predict `Λ ≤ Σ z y_i` which already exceeds the true
   `Λ` bound's leading term.)*

5. **[s5] [LEMMA]** `sum_sqrt_bounds (m : ℕ) : (2/3 : ℝ) * (m:ℝ)^((3:ℝ)/2) - Real.sqrt m ≤ ∑ i ∈ Finset.range m, Real.sqrt i ∧ ∑ i ∈ Finset.range m, Real.sqrt i ≤ (2/3 : ℝ) * (m:ℝ)^((3:ℝ)/2)`

   *Full proof by induction on `m`.* Write `Φ(m) := (2/3)m^{3/2}`.
   Both halves reduce to the single inequality
   **(★3)** `√m ≤ Φ(m+1) − Φ(m) ≤ √(m+1)` for every `m ≥ 0`.
   (★3) is `(3/2)√m ≤ (m+1)^{3/2} − m^{3/2} ≤ (3/2)√(m+1)`, which follows from the
   mean value theorem for `x ↦ x^{3/2}` on `[m, m+1]` (derivative `(3/2)√x`,
   monotone). A Lean‑friendly route avoiding MVT: put `a = √m`, `c = √(m+1)`, so
   `c² = a²+1`, `c ≥ a ≥ 0`, and `(m+1)^{3/2} − m^{3/2} = c³ − a³ = (c−a)(c²+ca+a²)`
   with `c − a = 1/(c+a)`; hence the quantity equals `(c²+ca+a²)/(c+a)`, and
   * `(c²+ca+a²)/(c+a) ≥ (3/2)a ⟺ 2c²+2ca+2a² ≥ 3ac+3a² ⟺ 2c² ≥ ac + a² ⟸ c ≥ a`;
   * `(c²+ca+a²)/(c+a) ≤ (3/2)c ⟺ 2c²+2ca+2a² ≤ 3c²+3ac ⟺ 2a² ≤ c² + ac ⟸ c ≥ a`.
   Both are `nlinarith`‑shaped given `c ≥ a ≥ 0`.
   *Upper half:* induction — `Σ_{i<m+1}√i = Σ_{i<m}√i + √m ≤ Φ(m) + √m ≤ Φ(m+1)` by
   the left half of (★3). Base `m=0`: `0 ≤ 0`.
   *Lower half:* induction — `Σ_{i<m+1}√i = Σ_{i<m}√i + √m ≥ Φ(m) − √m + √m = Φ(m) ≥ Φ(m+1) − √(m+1)`
   by the right half of (★3). Base `m=0`: `−0 ≤ 0`. ∎
   *(Table E6 checks both bounds at `m = 0,1,2,3,10,100,1000,10000`; note `m=1`
   needs the lower bound to be negative, `−1/3 ≤ 0`, which it is.)*

6. **[s6] [LEMMA]** `aset_infinite (u : ℕ → ℕ) (hmono : StrictMono u) (h2 : 2 ≤ u 0) (hcop : ∀ i j, i ≠ j → Nat.Coprime (u i) (u j)) (hsum : Summable (fun n => 1 / (u n : ℝ))) : (ASet u).Infinite`

   *Full proof.* Let `D_k := ∏_{i<k}(1 − 1/u_i)` and `σ_k := Σ_{i≥k} 1/u_i`.
   Since `u_i ≥ 2` for all `i` (`StrictMono` + `u 0 ≥ 2`), `D_k ∈ (0,1]` and `D_k ↓ D`
   with `D > 0` (the `HasSum.rexp` argument of findings F8, which needs only
   `0 < 1/u_i ≤ 1/2`). Since `σ_k → 0`, fix `k` with `σ_k < D/2 ≤ D_k/2`.
   For any `N`, by inclusion–exclusion over the pairwise coprime `u_0,…,u_{k−1}`,
   `#{a ≤ N : ∀ i<k, u_i ∤ a} = Σ_{T ⊆ [k]} (−1)^{|T|}⌊N/∏_{i∈T}u_i⌋ ≥ N·D_k − 2^k`.
   Among those, the ones divisible by some `u_i` with `i ≥ k` number at most
   `Σ_{i≥k} N/u_i = N σ_k`. Hence
   `#(ASet u ∩ [1,N]) ≥ N D_k − 2^k − N σ_k ≥ N D/2 − 2^k → ∞`.
   So `ASet u` is infinite. ∎ *(Used only to know that `A u` really enumerates
   `ASet u` in increasing order; see findings F1, which reaches the same
   conclusion and also rules out the degenerate `u 0 ∈ {0,1}` cases.)*

7. **[s7] [LEMMA] [CRUX]** `random_pool_selection (P : ℕ → Finset ℕ) (hP : IsPools P) (hlog : PoolsLog P) (hbig : PoolsBig P) (hesym : <the statement of [s4], universally quantified over b δ>) (hdiv : <the statement of [s3], universally quantified over N m>) : ∃ u : ℕ → ℕ, (∀ n, u n ∈ P n) ∧ ∀ (C : ℕ) (η : ℝ), 1 ≤ C → 0 < η → ∃ (θ : ℝ) (K : ℕ), 0 < θ ∧ ∀ᶠ t : ℕ in atTop, ∀ N : ℕ, (N : ℝ) ≤ Real.exp ((2/3 + θ) * (t:ℝ)^((3:ℝ)/2)) → ¬ HasCert u N (Nat.ceil ((1 + η) * (t:ℝ))) K (C * t)`

   This is the crux: it is where Li's probabilistic idea lives, and it is the only
   step that is not routine. Its **proof sketch, in full**:

   *(i) The space.* `Ω := ℕ → ℕ`, `μ := MeasureTheory.Measure.infinitePi (fun n => (PMF.uniformOfFinset (P n) (hP.1 n)).toMeasure)`.
   All of `Measure.infinitePi`, the `IsProbabilityMeasure` instance,
   `PMF.uniformOfFinset`, `PMF.toMeasure` were `#check`‑probed present
   (`scratch/probe5.lean`, `scratch/probe6.lean`). Every subset of `ℕ` is
   measurable (`MeasurableSet.of_discrete`). Put
   `Π := Set.univ.pi (fun n => (↑(P n) : Set ℕ))`; by
   `Measure.infinitePi_pi_univ`, `μ Π = ∏' n, μ_n(P n) = ∏' n, 1 = 1`.

   *(ii) Independence, as a single Mathlib call.* For a finite `S ⊆ ℕ` and integers
   `N_i`,
   `{ω | ∀ i ∈ S, ω i ∣ N_i} = (↑S : Set ℕ).pi (fun i => {p | p ∣ N_i})`,
   so `Measure.infinitePi_pi_of_countable` gives **exactly**
   `μ {ω | ∀ i ∈ S, ω i ∣ N_i} = ∏_{i ∈ S} ( #{p ∈ P i : p ∣ N_i} / |P i| )`.
   *(This one lemma replaces the whole `ProbabilityTheory.iIndepFun` apparatus; it
   is the single most important probe result of this revision.)*

   *(iii) Choice of constants (order matters — G16.3).* Given `C ≥ 1` and `η > 0`:
   `A := (1+η)^{3/2} > 1`; `ρ := A^{−1/4} ∈ (0,1)`; `β := ρ`, `δ := 1−ρ`, `δ' := 1−ρ`;
   `b := β(1−δ) = ρ²`; `θ := (A^{1/4} − 1)/3 > 0`.
   Then `(1−δ')·(2b/3)·A = (2/3)ρ³A = (2/3)A^{1/4} = 2/3 + 2(A^{1/4}−1)/3 = 2/3 + 2θ > 2/3 + θ`.
   **This single line is the entire content of the proof** (Table E2).
   Finally choose `K` so large that: `PoolsLog` holds with `δ` from `K` on,
   `PoolsBig` holds with `β` from `K` on, and `[s4]`'s `∀ᶠ M` threshold for
   `(b, δ')` is passed.

   *(iv) One‑step probability bound.* Let `t` be large, `N ≤ e^{(2/3+θ)t^{3/2}}`,
   `Q = C t`, `i > K`, `1 ≤ j ≤ Q`. Every `p ∈ P i` has `p ≥ e^{(1−δ)√i}`, so by
   `hdiv`, `#{p ∈ P i : p ∣ N+j} ≤ log(N+j)/((1−δ)√i) ≤ t²` for `t` large
   (`log(N+j) ≤ (2/3+θ)t^{3/2} + log(Ct+1) ≤ t^{3/2}` once `2/3+θ < 1`, which we may
   assume by shrinking `θ`; and `√i ≥ 1`). Also `|P i| ≥ (max P i)^β ≥ (u_i)^β ≥ e^{β(1−δ)√i} = e^{b√i}`.
   Hence
   **`μ {ω | ω i ∣ N+j} ≤ t²·e^{−b√i}`.**  (★4)

   *(v) First moment.* Let `B_t := Π ∩ {ω | HasCert ω N M K Q}` with
   `M := ⌈(1+η)t⌉`. Any certificate has all `u_{i} ≤ n + j i ≤ N + Q`, so the
   index set `S` is contained in the finite set `I_t := {i ≤ K' : min P i ≤ N+Q}`
   with `K < i`; thus `B_t` is a **finite** union of the cylinder events of (ii)
   and is measurable. By (ii), (★4) and independence,
   `μ B_t ≤ Σ_{n<N} Σ_{j : S → [1,Q]} Σ_{S ∈ I_t.powersetCard M} ∏_{i∈S} t² e^{−b√i}`
   `= N·Q^M·t^{2M}·Σ_{S ∈ I_t.powersetCard M} ∏_{i∈S} e^{−b√i}`
   `≤ N·(Ct)^M·t^{2M}·exp(−(1−δ')(2b/3)M^{3/2})`  (by `hesym`, valid for **every** `I_t`)
   so, taking logs and using `M ≥ (1+η)t` hence `M^{3/2} ≥ A t^{3/2}`,
   `log μ B_t ≤ (2/3+θ)t^{3/2} + M log(Ct) + 2M log t − (1−δ')(2b/3)A t^{3/2}`
   `= [(2/3+θ) − (2/3)A^{1/4}]·t^{3/2} + O(t log t) = −θ t^{3/2} + O(t log t)`.
   Hence `μ B_t ≤ e^{−(θ/2)t^{3/2}}` for all large `t`, and `Σ_t μ B_t < ∞`
   (Tables E7/E7b: the `t^{3/2}` coefficient is `−5.5·10⁻²` at `η = 0.5`,
   `−1.2·10⁻²` at `η = 0.1`, `−1.2·10⁻³` at `η = 0.01`; crossovers
   `3.5·10⁶ / 4.8·10⁷ / 5.4·10⁹` — finite, as it must be, since the claim is
   asymptotic).

   *(vi) Borel–Cantelli.* `MeasureTheory.measure_limsup_atTop_eq_zero` gives
   `μ (limsup B_t) = 0`, i.e. almost surely `ω ∉ B_t` for all large `t`. Call this
   full‑measure event `G_{C,η}`.

   *(vii) Countable intersection and extraction.* The conclusion is required for
   every `C ∈ ℕ` and every real `η > 0`. By (H3), `¬HasCert` at `M' = ⌈(1+η')t⌉`
   with `η' ≤ η` implies `¬HasCert` at `M = ⌈(1+η)t⌉`; so it suffices to secure
   the rational `η' ∈ ℚ_{>0}`. `ℕ × ℚ_{>0}` is countable, so
   `G := Π ∩ ⋂_{(C,η') ∈ ℕ × ℚ_{>0}} G_{C,η'}` has `μ G = 1 > 0`, hence `G ≠ ∅`.
   Any `ω ∈ G` is the required `u`. ∎

   **Why this is massively easier than the parent.** It has *no* `ASet`, no `A`,
   no `t u x`, no infinite product `D`, no `IsGood`, and no `IsLittleO`; it is a
   statement about a random sequence drawn from given pools. Its difficulty is
   concentrated in one first‑moment computation whose decisive inequality is the
   single scalar fact `A^{1/4} > 1`. The parent, by contrast, must additionally
   produce the pools, discharge three `IsGood` conjuncts, run the deterministic
   sieve reduction and do the asymptotic bookkeeping — all of which are `[s1]`,
   `[s2]`, `[s8]` and the glue below, none of which this step sees.

8. **[s8] [LEMMA]** `certificate_of_large_gap (u : ℕ → ℕ) (hmono : StrictMono u) (h2 : 2 ≤ u 0) (hcop : ∀ i j, i ≠ j → Nat.Coprime (u i) (u j)) (hsum : Summable (fun n => 1 / (u n : ℝ))) (hinf : (ASet u).Infinite) (hD : 0 < ∏' i : ℕ, (1 - 1 / (u i : ℝ))) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (Cc : ℕ) (hCc1 : 1 ≤ Cc) (hCc : (2:ℝ) / (∏' i, (1 - 1/(u i:ℝ))) ≤ Cc) (K₀ : ℕ) : ∃ K : ℕ, K₀ ≤ K ∧ ∀ᶠ x : ℕ in atTop, ∀ k : ℕ, A u k < x → (1 + ε) * (t u x : ℝ) * (∏' i, (1 - 1/(u i:ℝ)))⁻¹ ≤ (A u (k+1) : ℝ) - (A u k : ℝ) → HasCert u x (Nat.ceil ((1 + ε/6) * (t u x : ℝ))) K (Cc * t u x)`

   *Full proof* (this is Li pp. 6–7, re‑derived; every constant checked in Table E3).
   Write `D := ∏'(1−1/u_i) ∈ (0,1]`, `σ_K := Σ_{i>K} 1/u_i`, `D_K := ∏_{i≤K}(1−1/u_i)`.
   Choose `K ≥ K₀` with `σ_K ≤ εD/16` (possible: `σ_K → 0`). Let `x` be large,
   `t := t u x`; note `t → ∞` as `x → ∞`, because for every `m`, `x ≥ ∏_{i<m}u_i`
   forces `t u x ≥ m`.

   Assume `n := A u k < x` and `(1+ε)tD^{−1} ≤ A u (k+1) − n`. Put
   `L := ⌊(1+ε/2)tD^{−1}⌋`.
   * **Every one of `n+1, …, n+L` is divisible by some `u_i`.** The difference
     between `(1+ε)tD^{−1}` and `(1+ε/2)tD^{−1}` is `(ε/2)tD^{−1} ≥ (ε/2)t > 1` for
     `t` large, so `n + L < A u (k+1)`. Since `ASet u` is infinite (`hinf`),
     `A u` enumerates it increasingly, so no integer strictly between `A u k` and
     `A u (k+1)` lies in `ASet u`; by definition of `ASet`, each is divisible by
     some `u_i`.
   * **`L ≤ Cc·t`.** `D^{−1} ≤ Cc/2` by `hCc`, so `L ≤ (1+ε/2)t·Cc/2 ≤ (3/2)(Cc/2)t = (3Cc/4)t ≤ Cc·t`.
   * **`R ≥ (1+ε/3)t`,** where `R := #{1 ≤ j ≤ L : ∀ i ≤ K, u_i ∤ n+j}`. By CRT with
     the pairwise coprime moduli `u_0,…,u_K` and inclusion–exclusion,
     `R ≥ D_K·L − 2^{K+1}`. Now `D_K ≥ D` and `L ≥ (1+ε/2)tD^{−1} − 1`, so
     `R ≥ D((1+ε/2)tD^{−1} − 1) − 2^{K+1} = (1+ε/2)t − D − 2^{K+1} ≥ (1+ε/3)t`
     as soon as `(ε/6)t ≥ 1 + 2^{K+1}`, i.e. for `t` large (`K` is already fixed).
   * **`|S₀| ≥ (1 + 23ε/96)t`,** where `S₀ := {i > K : ∃ j ≤ L, u_i ∣ n+j, and j is one of the R positions}`.
     Every one of the `R` positions is covered by some `u_i` with `i > K`, and for
     a fixed `i` the number of `1 ≤ j ≤ L` with `u_i ∣ n+j` is at most `1 + L/u_i`.
     Hence `R ≤ Σ_{i ∈ S₀}(1 + L/u_i) ≤ |S₀| + L σ_K`. With `L ≤ (3/2)tD^{−1}` and
     `σ_K ≤ εD/16`, `L σ_K ≤ (3/2)tD^{−1}·εD/16 = (3ε/32)t`. So
     `|S₀| ≥ (1+ε/3)t − (3ε/32)t = (1 + 23ε/96)t` (since `1/3 − 3/32 = 32/96 − 9/96 = 23/96`).
   * **Extract the certificate.** `M := ⌈(1+ε/6)t⌉ ≤ (1+ε/6)t + 1`. Since
     `23/96 − 1/6 = 7/96 > 0`, `(1+23ε/96)t ≥ (1+ε/6)t + (7ε/96)t ≥ M` as soon as
     `(7ε/96)t ≥ 1`, i.e. for `t` large. So `|S₀| ≥ M`; pick `S ⊆ S₀` with `|S| = M`
     (`Finset.exists_subset_card_eq`; `S₀` is finite, being of size `≤ L`), and for
     each `i ∈ S` a position `j i ∈ [1, L] ⊆ [1, Cc·t]` with `u_i ∣ n + j i`.
     Together with `n < x`, this is exactly `HasCert u x M K (Cc·t)`. ∎

9. **[s9] [ELEM]** *Assemble the pools and the sequence.*
   `obtain ⟨Cp, hCp0, hCp⟩ := nth_prime_linearithmic` (`[s1]`);
   `obtain ⟨P, hP, hlog, hbig⟩ := good_seq_pools_exist Cp hCp0 hCp` (`[s2]`);
   `obtain ⟨u, hmem, hsel⟩ := random_pool_selection P hP hlog hbig (fun b δ hb hδ => esym_geom_bound b δ hb hδ) prime_divisor_count_bound` (`[s7]`, fed by `[s4]`, `[s3]`).
   `refine ⟨u, ⟨?_, ?_, ?_, ?_⟩, ?_⟩` — **no explicit witness is ever named.**

10. **[s10] [ELEM]** *Conjuncts 1, 2 of `IsGood`, and `2 ≤ u 0`.*
    `u n ∈ P n` and `u (n+1) ∈ P (n+1)` with `hP.2.2` give `u n < u (n+1)`, so
    `StrictMono u` by `strictMono_nat_of_lt_succ`. Each `u n` is prime (`hP.2.1`),
    they are pairwise distinct (injectivity of a `StrictMono`), so
    `Nat.coprime_primes` gives pairwise coprimality. `2 ≤ u 0` from
    `Nat.Prime.two_le`.

11. **[s11] [ELEM]** *Conjunct 3 (`Summable`) and the growth condition.*
    Apply `hlog` with `δ = 1/2`: eventually `√n/2 ≤ log (u n) ≤ (3/2)√n`.
    * *Summable.* From `log (u n) ≥ √n/2`, `u n ≥ exp(√n/2) = (exp(√n/8))^4 ≥ (1 + √n/8)^4 ≥ n²/4096`
      (using `Real.add_one_le_exp` four times), so `1/u n ≤ 4096/n²` eventually;
      comparison with `Real.summable_one_div_nat_pow` (p = 2) plus
      `summable_nat_add_iff` gives `Summable (fun n => 1/(u n : ℝ))`. *(This is the
      retired glue's `hSummable` with `(n+2)²` replaced by `n²/4096`.)*
    * *Growth.* From `log (u n) ≤ (3/2)√n` and the from‑scratch fact
      `(fun n => (Real.sqrt n : ℝ)) =o[atTop] (fun n => (n:ℝ))` — the retired glue's
      `hsqrtO`, kernel‑accepted, reusable verbatim — plus
      `Asymptotics.IsLittleO.const_mul_left` and `Asymptotics.isLittleO_iff` with
      `0 ≤ log (u n)` (as `u n ≥ 2`), we get
      `(fun n => Real.log (u n : ℝ)) =o[atTop] (fun n => (n : ℝ))`.
    * *`0 < D`.* Exactly the retired glue's `hDpos` (findings F8): from `u i ≥ 2`,
      `0 < 1/u i ≤ 1/2`; the `nlinarith` certificate `exp(−2s) ≤ 1 − s` for
      `0 ≤ s ≤ 1/2`; `Real.le_log_iff_exp_le`; summability of `log(1−1/u_i)` by
      comparison with `2Σ1/u_i`; `HasSum.rexp` (**note**: produces
      `HasProd (Real.exp ∘ f)`, with an explicit `Function.comp`) and
      `Real.exp_log`; hence `D = exp(Σ log(1−1/u_i)) > 0`.

12. **[s12] [ELEM]** *A uniform upper bound for `x` in terms of `t_x`.*
    Claim: for every `θ ∈ (0,1]`, `∀ᶠ x, (x:ℝ) ≤ exp((2/3+θ)·(t u x)^{3/2})`.
    Proof: put `δ := θ/8` and let `n_δ` be the `PoolsLog` threshold, `Λ := Σ_{i<n_δ} log (u i)`
    (a constant). By the definition of `t := t u x`, `x < ∏_{i<t+1} u i`, hence
    `log x ≤ Σ_{i≤t} log (u i) ≤ Λ + (1+δ)Σ_{i<t+1}√i ≤ Λ + (1+δ)(2/3)(t+1)^{3/2}`
    by `[s5]` (upper half). Since `(t+1)^{3/2} ≤ (1 + 1/t)^{3/2} t^{3/2}` and
    `(1+1/t)^{3/2} ≤ 1 + θ/8` for `t` large, and `(1+θ/8)²(2/3) ≤ 2/3 + θ/2` for
    `θ ≤ 1`, we get `log x ≤ Λ + (2/3+θ/2)t^{3/2} ≤ (2/3+θ)t^{3/2}` once
    `(θ/2)t^{3/2} ≥ Λ`. Finally `t u x → ∞` as `x → ∞` (for each `m`, `x ≥ ∏_{i<m}u_i ⟹ t u x ≥ m`),
    so "for `t` large" is "for `x` large". ∎

13. **[s13] [ELEM]** *Conjunct 4 of `IsGood` — the contradiction.*
    Fix `ε > 0`. If `ε > 1` replace it by `1` (the conclusion for `ε = 1` implies
    the one for `ε > 1`, since `t_x ≥ 0` and `D⁻¹ > 0`). So assume `0 < ε ≤ 1`.
    Set `η := ε/6 > 0` and `Cc := ⌈2/D⌉₊ + 1` (so `1 ≤ Cc` and `2/D ≤ Cc`).
    **Order of constants (G16.3 — any other order is circular):**
    `η ← ε/6`, then `Cc ← ⌈2/D⌉₊+1`, then `(θ, K) ← hsel Cc η`, then
    `K' ← certificate_of_large_gap … K` (so `K ≤ K'`).
    Now let `x` be large enough that all of the following hold simultaneously:
    the `∀ᶠ x` of `[s8]`; `t u x` exceeds the `∀ᶠ t` threshold of `hsel Cc η`;
    and `[s12]` for `min(θ,1)`.
    Take `k` with `A u k < x` and suppose, for contradiction, that
    `¬ (A u (k+1) − A u k < (1+ε)·t_x·D⁻¹)`, i.e. `(1+ε)t_xD⁻¹ ≤ A u (k+1) − A u k`.
    `[s8]` yields `HasCert u x ⌈(1+ε/6)t_x⌉ K' (Cc·t_x)`; by **(H2)** (since `K ≤ K'`)
    this gives `HasCert u x ⌈(1+η)t_x⌉ K (Cc·t_x)`. But `[s12]` gives
    `(x:ℝ) ≤ exp((2/3+θ)t_x^{3/2})`, so `hsel` says `¬ HasCert u x ⌈(1+η)t_x⌉ K (Cc·t_x)`.
    Contradiction. Hence `A u (k+1) − A u k < (1+ε)·t_x·D⁻¹`, which is conjunct 4. ∎

---

## 4. Supporting Evidence & Positive Test Cases

All produced by `scratch/evidence5.py` (run this round); Mathlib existence probes
are `scratch/probe5.lean`, `scratch/probe6.lean` (both run, results below).

**E1 — the pools `M n = ⌈e^{√n}⌉+n`, `P_n = {p_k : M n ≤ k < M(n+1)}` (exact primes).**

| n | M n | \|P_n\| | min P_n | max P_n | log min | log max | √n |
|---|---|---|---|---|---|---|---|
| 0 | 1 | 3 | 3 | 7 | 1.0986 | 1.9459 | 0.0000 |
| 1 | 4 | 3 | 11 | 17 | 2.3979 | 2.8332 | 1.0000 |
| 2 | 7 | 2 | 19 | 23 | 2.9444 | 3.1355 | 1.4142 |
| 5 | 15 | 3 | 53 | 61 | 3.9703 | 4.1109 | 2.2361 |
| 10 | 34 | 5 | 149 | 167 | 5.0039 | 5.1180 | 3.1623 |
| 16 | 71 | 8 | 359 | 401 | 5.8833 | 5.9940 | 4.0000 |
| 20 | 108 | 11 | 599 | 653 | 6.3953 | 6.4816 | 4.4721 |
| 24 | 159 | 15 | 941 | 1033 | 6.8469 | 6.9402 | 4.8990 |

`M` is strictly increasing on every sampled `n` (and structurally, by the `+n`);
`⌈e^{√n}⌉` alone is already nondecreasing for all `n ≤ 20000` (checked). The pools
are consecutive primes, so ordering/disjointness/coprimality are definitional.
Larger `n` (exact `M n`, log‑space primes): `n = 640`: `|P_n| = 1.9·10⁹`,
`log(min) ≈ 25.30` vs `√n = 25.298`; `n = 20000`: `|P_n| ≈ 9.3·10⁵⁸`,
`log(min) ≈ 141.42` vs `√n = 141.4214`.

**E1b — `PoolsBig`: `log|P_n| ≥ β·log(max P_n)`** (log space, `max P_n ≤ 50·M(n+1)·log M(n+1)` from `[s1]`):

| n | log\|P_n\| ≥ | β=.5 | β=.8 | β=.9 | β=.95 | β=.99 |
|---|---|---|---|---|---|---|
| 160 | 8.38 | 9.63 ✗ | 15.41 ✗ | 17.34 ✗ | 18.30 ✗ | 19.07 ✗ |
| 640 | 20.36 | 16.26 ✓ | 26.02 ✗ | 29.27 ✗ | 30.90 ✗ | 32.20 ✗ |
| 10⁴ | 93.70 | 54.27 ✓ | 86.83 ✓ | 97.69 ✗ | 103.11 ✗ | 107.45 ✗ |
| 10⁶ | 991.40 | 505.41 ✓ | 808.66 ✓ | 909.74 ✓ | 960.28 ✓ | 1000.71 ✗ |
| 10⁷ | 3152.53 | 1587.12 ✓ | 2539.40 ✓ | 2856.82 ✓ | 3015.54 ✓ | 3142.51 ✓ |
| 10¹⁰ | 99986.79 | 50007.71 ✓ | 80012.34 ✓ | 90013.88 ✓ | 95014.65 ✓ | 99015.27 ✓ |

The crossover moves right as `β ↑ 1` — **this is exactly why `PoolsBig` is stated
as `∀ β<1, ∀ᶠ n` and not uniformly**, and it is the boundary condition a careless
formulation would get wrong.

**E1c — `PoolsLog`: worst relative error `|log p − √n|/√n` over `p ∈ P_n`.**

| n | 10 | 160 | 2560 | 10⁴ | 10⁶ | 10⁸ | 10¹² |
|---|---|---|---|---|---|---|---|
| rel. err ≤ | 1.795 | 0.523 | 0.156 | 0.0854 | 0.0108 | 0.00131 | 1.8·10⁻⁵ |

Decays like `log n/√n`, confirming `log (u n) = √n(1+o(1))` — relative, not
additive, accuracy (see the translation table; §5 FP‑2 shows this suffices).

**E2 — the decisive inequality, i.e. the whole proof in one table.**
`A := (1+η)^{3/2}`, `ρ := A^{−1/4}`, `θ := (A^{1/4}−1)/3`.

| η | A | ρ (<1 ✓) | ρ³A = A^{1/4} (>1 ✓) | θ (>0 ✓) |
|---|---|---|---|---|
| 0.5 | 1.837117307 | 0.8589458 | 1.164217765 | 5.474·10⁻² |
| 0.2 | 1.314534138 | 0.9339143 | 1.070762042 | 2.359·10⁻² |
| 0.1 | 1.153689733 | 0.9648899 | 1.036387716 | 1.213·10⁻² |
| 0.05 | 1.075929830 | 0.9818700 | 1.018464715 | 6.155·10⁻³ |
| 0.01 | 1.015037438 | 0.9962756 | 1.003738344 | 1.246·10⁻³ |
| 10⁻³ | 1.001500375 | 0.9996253 | 1.000374883 | 1.250·10⁻⁴ |
| 10⁻⁶ | 1.000001500 | 0.9999996 | 1.000000375 | 1.250·10⁻⁷ |

`A^{1/4} > 1` for **every** `η > 0`, so a legal `β = ρ < 1` and a legal `θ > 0`
always exist. No other step in `[s7]` is tight.

**E3 — the deterministic constants of `[s8]` (Li pp. 6–7), with `η = ε/6`.**

| ε | R/t ≥ 1+ε/3 | Lσ_K/t ≤ 3ε/32 | \|S₀\|/t ≥ 1+23ε/96 | M/t = 1+ε/6 | margin 7ε/96 |
|---|---|---|---|---|---|
| 1.00 | 1.333333 | 0.093750 | 1.239583 | 1.166667 | 0.072917 |
| 0.50 | 1.166667 | 0.046875 | 1.119792 | 1.083333 | 0.036458 |
| 0.10 | 1.033333 | 0.009375 | 1.023958 | 1.016667 | 0.007292 |
| 0.01 | 1.003333 | 0.000937 | 1.002396 | 1.001667 | 0.000729 |

`23/96 − 1/6 = 7/96 = 0.0729 > 0`, so the margin is strictly positive for every
`ε ∈ (0,1]`. (This is why `η < ε/5` in Li; `η = ε/6` is inside that range and is
a concrete rational choice, which matters for the countable intersection in
`[s7](vii)`.)

**E4 — the elementary‑symmetric Chernoff bound (`[s4]`), exact vs. bound.**
`e_M` computed exactly by DP over `i < 4000`, `y_i = e^{−b√i}`, `z = e^{b√M}`.

`b = 0.9`:

| M | exact `e_M` | `z^{−M}∏(1+zy)` | `e^{−(2b/3)M^{3/2}}` | `(log e_M − main)/M` |
|---|---|---|---|---|
| 1 | 3.1255e+00 | 1.1674e+02 | 5.4881e−01 | 1.7396 |
| 3 | 3.3015e+00 | 1.1496e+02 | 4.4259e−02 | 1.4374 |
| 8 | 7.6833e−03 | 2.0929e−01 | 1.2701e−06 | 1.0885 |
| 20 | 2.7304e−17 | 5.8810e−16 | 4.9353e−24 | 0.7763 |

Every sampled case satisfies `exact ≤ Chernoff`; the excess over `−(2b/3)M^{3/2}`
is bounded per unit of `M` (max over all samples `2.4844`), i.e. genuinely `O(M)`.

**E4b — the Chernoff exponent itself.**

| b | M | `log(z^{−M}∏(1+zy))` | `−(2b/3)M^{3/2}` | excess/M |
|---|---|---|---|---|
| 0.5 | 10 | 12.8408 | −10.5409 | 2.3382 |
| 0.5 | 800 | −7349.1943 | −7542.4723 | 0.2416 |
| 0.9 | 10 | −5.6457 | −18.9737 | 1.3328 |
| 0.9 | 800 | −13460.1446 | −13576.4502 | 0.1454 |

Excess/M is **decreasing**, so `K_b` in `[s4](c)` is a genuine constant.

**E5 — Chebyshev (`[s1]`): `n := 3(k+1)(⌈log(k+2)⌉+1)`.**

| k | n | 2n+1 | `count Prime (2n+1)` | p_k | 50·k·log k | all ok |
|---|---|---|---|---|---|---|
| 2 | 27 | 55 | 16 | 5 | 69.3 | ✓ |
| 10 | 132 | 265 | 56 | 31 | 1151.3 | ✓ |
| 200 | 4221 | 8443 | 1055 | 1229 | 52983.2 | ✓ |
| 5000 | 150030 | 300061 | 26001 | 48619 | 2129298.3 | ✓ |

and the analytic ratio `n log 4 / ((k+1)log 2n)` is `3.13, 2.92, 2.98, 3.04, 3.41,
3.58, 3.74` at `k = 2, 3, 10, 10², 10⁴, 10⁸, 10¹⁶` — always `> 1`, with the minimum
`2.92` at `k = 3`. So step (D) is comfortable, not marginal.

**E6 — `[s5]`: `(2/3)m^{3/2} − √m ≤ Σ_{i<m}√i ≤ (2/3)m^{3/2}`.**

| m | 0 | 1 | 2 | 3 | 100 | 10000 |
|---|---|---|---|---|---|---|
| lower | 0.000 | −0.333 | 0.471 | 1.732 | 656.667 | 666566.667 |
| sum | 0.000 | 0.000 | 1.000 | 2.414 | 661.463 | 666616.459 |
| upper | 0.000 | 0.667 | 1.886 | 3.464 | 666.667 | 666666.667 |

Both bounds hold at every sampled `m`, **including the degenerate `m = 0` and
`m = 1`** (where the lower bound is `≤ 0`).

**E7 / E7b — the first moment of `[s7](v)`,**
`log E X_t ≤ (2/3+θ)t^{3/2} + M log(Ct) + 2M log t − ρ(2b/3)M^{3/2}` with `C = 3`:

| η | ρ | θ | b | coeff of `t^{3/2}` | crossover `t₀` |
|---|---|---|---|---|---|
| 0.5 | 0.858946 | 0.054739 | 0.737788 | −5.474·10⁻² | 3.5·10⁶ |
| 0.1 | 0.964890 | 0.012129 | 0.931012 | −1.213·10⁻² | 4.8·10⁷ |
| 0.01 | 0.996276 | 0.001246 | 0.992565 | −1.246·10⁻³ | 5.4·10⁹ |

Negative in every row, as required, with a finite crossover — consistent with
erdosproblems.com's "cannot be resolved with a finite computation" and with
round 1's independently computed crossover scale (findings G3).

**E8 — the resulting sequence.** `Σ 1/u_n < ∞` (crude bound `1.6228`, using the
worst‑case `u_n ≥ M n`; the true value is much smaller) and, since every
`u_n ≥ 2`, `D = ∏(1−1/u_n) ≥ e^{−2S} ≥ 0.0389 > 0`. *(`S < 1` is neither claimed
nor needed anywhere; only `S < ∞` and `D > 0` are used.)*

**Mathlib probes (run this round; full output in `scratch/probe5.lean`, `probe6.lean`).**
PRESENT, with the signatures the plan assumes:
`MeasureTheory.Measure.infinitePi`, `Measure.infinitePiNat`,
`Measure.infinitePi_pi_of_countable` (`μ (s.pi t) = ∏' i:s, μ i (t i)` — **the
independence step of `[s7](ii)`**), `Measure.infinitePi_pi_univ`,
`Measure.infinitePi_cylinder`, `Measure.isProjectiveLimit_infinitePi`,
`MeasureTheory.measure_limsup_atTop_eq_zero` (Borel–Cantelli I),
`MeasureTheory.measure_iUnion_le`, `PMF.uniformOfFinset`, `PMF.toMeasure`,
`PMF.uniformOfFinset_apply`, `PMF.toMeasure_apply_finset`,
`MeasurableSet.of_discrete`, and — checked by `#check (inferInstance : IsProbabilityMeasure (Measure.infinitePi …))` —
the `IsProbabilityMeasure` **instance is found automatically**.
`Finset.prod_add` (the `[s4](a)` expansion), `Finset.powersetCard`,
`Finset.card_powersetCard`, `Finset.prod_le_pow_card`, `Finset.prod_le_prod`,
`Nat.four_pow_le_two_mul_self_mul_centralBinom`, `Nat.pow_factorization_choose_le`,
`Nat.factorization_prod_pow_eq_self`, `Nat.count_eq_card_filter_range`,
`Nat.nth_lt_of_lt_count`, `Nat.nth_strictMono`, `Nat.infinite_setOf_prime`,
`Real.exp_sum`, `Real.rpow_natCast`, `Real.isLittleO_log_id_atTop`,
`Real.summable_one_div_nat_rpow`, `Real.log_le_sub_one_of_pos`,
`nonempty_sections_of_finite_inverse_system` (a fallback for `[s7](vii)` if the
measure route is abandoned for a König argument).
ABSENT: `Finset.esymm` (so `[s4]` must phrase the elementary symmetric function
as `∑ S ∈ I.powersetCard M, ∏ i ∈ S, y i`, which it does), any PNT
(`Nat.primeCounting_isEquivalent`, `Nat.primeCounting_asymptotic`),
`ProbabilityTheory.borel_cantelli` (the *name*; the content is
`measure_limsup_atTop_eq_zero`), `Finset.sum_le_tsum` (the real name is
`Summable.sum_le_tsum`), `sum_le_tsum`, `tsum_le_tsum`.

**The independence step of `[s7](ii)` was elaborated end to end** (`scratch/probe8.lean`,
a `#check` of a term, no tactics): with
`μ := Measure.infinitePi (fun n => (PMF.uniformOfFinset (P n) (hne n)).toMeasure)`,
Lean returns

```
Measure.infinitePi_pi_of_countable … :
  μ ((↑S).pi fun i => {p | p ∣ N i}) = ∏' (i : ↑↑S), (PMF.uniformOfFinset (P ↑i) _).toMeasure {p | p ∣ N ↑i}
```

i.e. **exactly** `μ {ω | ∀ i ∈ S, ω i ∣ N i} = ∏_{i∈S} P_i(p ∣ N i)`, with the
countability side condition discharged by `(S.finite_toSet.countable).to_subtype`
and measurability by `MeasurableSet.of_discrete`. This is the one step whose
absence would have sunk the whole plan; it is present and it type‑checks.

**All eight subgoal statements of §3.1 were elaborated as `Prop`‑valued terms**
(`scratch/probe7.lean`): every one is accepted, including the `Real.rpow`
exponent `(3:ℝ)/2`, `Finset.powersetCard`, `Nat.primeFactors.filter`,
`Nat.ceil` and the `∀ᶠ … in atTop` shapes.

---

## 5. Adversarial Refutation & Falsification Attempts

**FP‑1. Could a weaker prime input do, so that `[s1]` can be replaced by the
already‑proved `nth_prime_poly_bound`?** No — and this is a *theorem*, not a
preference. Suppose the pools only satisfy `|P_n| ≥ (max P_n)^{β₀}` for one fixed
`β₀ < 1`. Write `Ψ(t) := Σ_{i<t} log u_i`. The first moment needs
`Ψ(t) < β₀·Ψ((1+η)t)` for *every* `η > 0` and all large `t`, i.e.
`liminf_t Ψ((1+η)t)/Ψ(t) > 1/β₀`. But if `Ψ((1+η)t) ≥ κ·Ψ(t)` for all large `t`,
iterating gives `Ψ(t) ≫ t^{log κ/log(1+η)}`, while `log u_n = o(n)` forces
`Ψ(t) = o(t²)`; hence `log κ/log(1+η) ≤ 2`, i.e. `κ ≤ (1+η)²`. Letting `η → 0`
forces `1/β₀ < 1`, i.e. `β₀ > 1` — a contradiction. **So `β` must be allowed
arbitrarily close to 1, hence `p_k = k^{1+o(1)}`, hence Chebyshev strength.**
`p_k ≤ k^6` gives only `β < 1/6`, which by the computation above would need
`(1+η)² > 6`, i.e. `η > 1.449` — useless. This probe is what killed the "just
re‑use the proved lemma" shortcut, and it also reproves (independently) Erdős's
belief that part (i) is false: polynomial `u_n = n^A` has `Ψ(t) ≍ A t log t`,
`Ψ((1+η)t)/Ψ(t) → 1+η`, and the same computation needs `β₀ ≥ 1/(1+η) → 1` with
pools of size `n^{Aβ₀}` which exhaust the primes once `Aβ₀ + 1 > A`.

**FP‑2. Is the *relative* accuracy `log u_n = √n(1+o(1))` (all our pools give)
enough, or does the proof need Li's additive `√n + O(n^{−1/2})`?** Relative is
enough. Everything enters through the comparison
`(2/3+θ) < (1−δ')(2b/3)(1+η)^{3/2}` with `b = β(1−δ)`; a relative error `δ` in
`log u_n` multiplies the right side by `(1−δ)` and the left side by at most
`(1+δ)`, both of which are absorbed by the *strict* inequality `A^{1/4} > 1`,
with the explicit choice `β = 1−δ = 1−δ' = A^{−1/4}` (§3.1 `[s7](iii)`; Table E2).
Had the inequality been non‑strict, this would have failed — it is strict only
because `(1+η)^{−3/2} < 1` for `η > 0`.

**FP‑3. Does the target become FALSE for some `ε`, so that `--action=refute`
applies?** No, twice over. (i) Corollary T (`witnessU_gap_bound/findings.md` G10)
proves `limsup G(x)·D/t_x ≥ 1` for **every** admissible `u`, so the `(1+ε)` is
exactly at the threshold: the statement is true‑and‑tight and no fixed constant
`< 1/D` works. (ii) The extremal/LP computation (blueprint rev 3 FP‑A of that
node) shows the optimum ratio is exactly `1`, approached from below. Hence
`refute` is unavailable.

**FP‑4. Degenerate `u`: could the plan accidentally produce `u 0 ∈ {0,1}` or a
finite `ASet u`?** No. `u 0 ∈ P 0` is prime, so `u 0 ≥ 2`; findings F1 shows
`u 0 = 0` contradicts coprimality and `u 0 = 1` makes both sides of conjunct 4
zero. `ASet u` is infinite by `[s6]`. Concretely, with the pools of Table E1,
`u 0 ∈ {3,5,7}`.

**FP‑5. `t u x = sSup {…}` junk values.** `{k | ∏_{i<k} u i ≤ x}` contains `k = 0`
(empty product `1 ≤ x` for `x ≥ 1`) and is bounded above (`∏_{i<k} u i ≥ 2^k`), so
the `sSup` is an honest maximum (`Nat.sSup_mem`) and never the junk `0`
(findings F1). Similarly `∏'(1−1/u_i)` is a genuine convergent product by
`[s11]`, so `(∏')⁻¹` is not `0⁻¹ = 0`.

**FP‑6. `m = 0, 1` in `[s5]`.** At `m = 0` both bounds read `0 ≤ 0 ≤ 0`; at `m = 1`
the lower bound is `2/3 − 1 = −1/3 ≤ 0` ✓ and the upper is `0 ≤ 2/3` ✓ (Table E6).
A statement without the `−√m` slack would be FALSE at `m = 1`.

**FP‑7. `M = 0` in `[s4]`.** `I.powersetCard 0 = {∅}` and the empty product is `1`,
while the right side is `exp(0) = 1`; so the inequality is an equality, not a
failure. The statement is `∀ᶠ M`, so this case is free anyway.

**FP‑8. `I` arbitrary in `[s4]` — is the bound really uniform over `I`?** Yes,
because all factors `1 + z y_i ≥ 1`, so `Σ_{i∈I} log(1+zy_i) ≤ Σ_{i∈ℕ} log(1+zy_i)`,
and that infinite sum converges for each fixed `z`. If it did not, the bound
would be vacuous for large `I`; §3.1 `[s4](b)` is exactly this check. Crucially
the bound must hold for `I` containing small indices (where `y_i ≈ 1`), which is
why the `i ≤ M` / `i > M` split in `[s4](c)` is not optional.

**FP‑9. Could `θ` in `[s7]` be taken *arbitrary* positive instead of existential?**
**No — and this is the one place where a plausible‑looking strengthening is
FALSE.** If `θ` is large, `N_t = e^{(2/3+θ)t^{3/2}}` vastly exceeds `P_{t+1}`, and
certificates with `n` in `(P_{t+1}, N_t]` genuinely exist (they are counted with a
weight the first moment cannot beat: the `t^{3/2}` coefficient
`(2/3+θ) − (2/3)A^{1/4}` turns positive as soon as `θ > (2/3)(A^{1/4}−1) = 2θ_0`).
Hence `[s7]` **must** state `∃ θ > 0`, and `[s12]` must supply `x ≤ e^{(2/3+θ)t^{3/2}}`
for *that* `θ` — which it does, because `log x ≤ (2/3+o(1))t^{3/2}` for **every**
positive slack. A plan that wrote `∀ θ > 0` would be proposing a false lemma.

**FP‑10. Is `HasCert` monotone the way the glue uses it?** Checked all three
directions in §3.0: (H1) in `N` (weaker constraint on `n`), (H2) **decreasing** in
`K` (a set of indices `> K'` is a set of indices `> K` when `K ≤ K'`), (H3)
**decreasing** in `M` (pass to a subset). The glue uses (H2) with `K ≤ K'` and
(H3) only inside `[s7](vii)` with `η' ≤ η`. Getting either direction backwards
would break `[s13]`; they were re‑derived from the definition, not assumed.

**FP‑11. Is Li's paper wrong?** It is unrefereed and AI‑assisted, so it was
attacked (findings G16). Three defects, all repaired here and **none** taken on
trust: (1) the `e_M` summation — repaired in `[s4]` and verified numerically
(E4/E4b); (2) the PNT dependence — removed entirely by the block‑cut pools of
`[s2]`, which need only `[s1]`; (3) the order of constants — pinned down
explicitly in `[s13]`. Neither equation (5) nor equation (9) of the paper is
cited: `[s7](iii)` and `[s7](iv)` derive them from scratch.

**FP‑12. Does anything here reuse a route already proved closed?** No. R1–R6 are
all *deterministic* routes for a *fixed* `u`; every one of them is refuted by
G2–G12 precisely because a fixed modulus gives weight `⌊x/U⌋+θ ∈ {0,1}` with
`U > x`. `[s7]` never fixes `u`; the weight it uses is `∏_i (#divisors in pool)/|P_i|`,
which is `≈ 1/U` and is the quantity G3 showed the heuristic (correctly) predicts.
The one *deterministic* ingredient retained, `[s8]`, is precisely the part G18
identifies as "the only piece the present node could ever have contributed, and
it is easy".

---

## 6. Freshness & Anti-Recycling Audit

* **§6 of `context.md` lists one retired subgoal set: `[nth_prime_poly_bound, witnessU_gap_bound]`.**
  The set proposed here is `[s1] nth_prime_linearithmic`, `[s2] good_seq_pools_exist`,
  `[s3] prime_divisor_count_bound`, `[s4] esym_geom_bound`, `[s5] sum_sqrt_bounds`,
  `[s6] aset_infinite`, `[s7] random_pool_selection`, `[s8] certificate_of_large_gap`.
  **It contains neither retired name, and is not that set padded.** In particular
  `witnessU_gap_bound` is *gone*, together with the definitions `witnessF` /
  `witnessU` (released with the retired plan) and every trace of an explicit
  witness. The reviewer's `SHAPE:` instruction — "do NOT re‑plan with a different
  `witnessF`, a different `ε`-shape, or a constant in place of `(1+ε)/D`" — is
  complied with: no explicit witness appears anywhere, the `ε`‑shape is untouched,
  and no fixed‑constant reformulation is proposed.
* **`nth_prime_poly_bound` (status `FORMAL_PROVED`, §10) is neither re‑proposed nor
  re‑derived.** `[s1]` is a *different and strictly stronger* statement
  (`p_k ≤ C·k·log k`, real‑valued) which the proved lemma does not imply; FP‑1
  proves the strengthening is *forced*, so this is not duplication. The proved
  lemma's own proof script is reused as the template for `[s1]` steps (A)–(C).
* **No unproved sibling is cited.** The only other node in the graph,
  `witnessU_gap_bound`, is retired and is used solely as a source of *findings*
  (its G2–G18 diagnostics and its `proof_text5.txt`), never as a lemma. No `[CITE]`
  step names it. Steps `[s3]`, `[s4]`, `[s5]` are consumed by `[s7]` as **explicit
  hypotheses** supplied by the root, not as citations, so `[s7]` is dispatchable in
  parallel with them and never references a name that is not in its own scope.
* **Every child is genuinely used by the root.** `[s1] → [s2] → [s7]`;
  `[s3], [s4] → [s7]` (as hypotheses passed by the root); `[s5] → [s4]`'s proof and
  the root's `[s12]`; `[s6] → [s8]`; `[s7], [s8] → [s13]`. No decorative children.
* **Findings files read before drafting** (Phase 1): `nodes/erdos_1101.parts.ii/findings.md`
  (own, incl. the reviewer note), `nodes/witnessU_gap_bound/findings.md` (all three
  rounds, G0–G19), `nodes/witnessU_gap_bound/scratch/blueprint.md` rev 3,
  `nodes/witnessU_gap_bound/scratch/proof_text5.txt`,
  `nodes/nth_prime_poly_bound/proof_scaffold.lean`. **Why the previous attempt did
  not work**, in one sentence: it named an explicit witness, which makes `IsGood`'s
  fourth conjunct strictly harder than the open problem, because the only known
  proof is a probabilistic existence argument that cannot name its witness.

---

## 7. Open Risks

1. **`[s7]` is the crux and it is large.** It bundles the measure space, the
   independence identity, the first moment, Borel–Cantelli and the countable
   intersection. Its planner should split it further; the natural cut is
   (a) measurability + the finite‑union description of `B_t`, (b) the first‑moment
   inequality `log μ B_t ≤ −θt^{3/2} + O(t log t)`, (c) the Borel–Cantelli +
   countable‑intersection extraction. What would falsify it: if
   `Measure.infinitePi_pi_of_countable` turns out to require a measurability side
   condition the discrete `ℕ` does not satisfy — probed, it requires only
   `∀ i ∈ s, MeasurableSet (t i)`, which `MeasurableSet.of_discrete` gives.
   *Fallback if the measure route stalls:* replace `μ` by normalised counting on
   the finite products `∏_{i<m} P i` and use
   `nonempty_sections_of_finite_inverse_system` (probed present) — the densities
   and the union bound are identical, only the limit apparatus changes.
2. **`[s2]`'s `PoolsBig` is asymptotic in a way that hides a large constant.**
   Table E1b shows the crossover for `β = 0.99` is near `n = 10⁷`. This is fine for
   an `∀ᶠ n` statement but means no finite check can validate it; the proof must be
   the analytic one written in §3.1, not a computation. What would falsify it:
   if `log|P_n| ≥ √n − log(3√n)` were wrong, e.g. if `M(n+1) − M n` could be
   `O(1)` infinitely often. It cannot: the displayed bound
   `M(n+1) − M n ≥ exp(√n)/(3√n)` is proved from `Real.add_one_le_exp`, and the
   `+ n` in `M` only helps.
3. **`[s8]`'s inclusion–exclusion error term `2^{K+1}` is exponential in `K`, and
   `K` depends on `ε` and on `[s7]`'s `K`.** This is harmless because `K` is fixed
   *before* `t → ∞`, but the formalizer must keep that order (`[s13]` pins it).
   If the order is inverted the argument is circular — this is defect (3) of
   findings G16 and the single most likely place for a downstream failure.
4. **Li (2026) is unrefereed and the site still records "Proof claims (0)".**
   The blueprint does not depend on the paper's correctness: `[s1]`–`[s8]` are
   each self‑contained and re‑derived, and §5 records the three defects found.
   But a reader should treat the *architecture* as adapted from Li, with the
   PNT‑free pools and the repaired Chernoff step as this node's own contribution.
5. **`[s12]` needs `t u x → ∞`, which needs `∏_{i<m} u i` to be finite and
   increasing — true, but it is the kind of step that is easy to state and fiddly
   in Lean** (`Nat.sSup_mem` for the non‑junk `sSup`, plus monotonicity of `k ↦ ∏_{i<k}u i`).
   If the prover finds `[s12]` is not `[ELEM]`, it should come back as a `[LEMMA]`
   — it is small and self‑contained.
