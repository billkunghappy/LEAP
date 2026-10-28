# Blueprint: erdos_357.variants.hegyvari
Revision: 1

## 1. Statement

Ambient definitions (from `problem.lean`, namespace `Erdos357`):

```lean
def HasDistinctSums {ι α : Type*} [Preorder ι] [AddCommMonoid α] (a : ι → α) : Prop :=
  {J : Finset ι | (J : Set ι).OrdConnected}.InjOn (fun J ↦ ∑ x ∈ J, a x)

noncomputable def g (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : Fin k → ℕ, (Set.range a ⊆ Set.Icc 1 n) ∧ HasDistinctSums a}
```

Target:

```lean
theorem erdos_357.variants.hegyvari :
  ∃ (o o' : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧ o' =o[atTop] (1 : ℕ → ℝ) ∧
    ∀ᶠ n in atTop, (g n : ℝ) ∈ Set.Icc ((1 / 3 + o n) * n) ((2 / 3 + o' n) * n)
```

**Plain mathematics.** `g n` is the largest `k` for which there exist integers
`a_1, …, a_k ∈ [1,n]` (repetitions allowed, no monotonicity required) such that all
"run sums" `a_u + a_{u+1} + ⋯ + a_v` (`1 ≤ u ≤ v ≤ k`) are pairwise distinct.
Since `o` and `o'` are *existentially* quantified and are only required to tend to `0`,
the statement is **exactly equivalent** to the pair of asymptotic inequalities

  (LB)  `liminf_{n→∞} g(n)/n ≥ 1/3`,  (UB)  `limsup_{n→∞} g(n)/n ≤ 2/3`.

(Section 3 step s6 gives the explicit `o`, `o'` realising this; Section 5 explains
why no cheaper choice of `o, o'` can dodge (LB)/(UB).)

This is Hegyvári's theorem, N. Hegyvári, *On consecutive sums in sequences*,
Acta Math. Acad. Sci. Hungar. **48** (1986); it is the reference `[He86]` attached
to Erdős Problem #357 at <https://www.erdosproblems.com/357>. The formal statement
comes from `FormalConjectures/ErdosProblems/357.lean` in
<https://github.com/google-deepmind/formal-conjectures>.

**Calibration.** This is a *real theorem*, not a lemma: it is a published research
result of a professional additive combinatorialist. It is strictly harder than a
textbook exercise but strictly easier than the open part of Erdős #357 (which asks
whether `f(n) = o(n)` for the strictly-increasing variant `f`). It genuinely
separates into four independent claims (one bookkeeping lemma about the `sSup`,
one purely finite counting theorem, one explicit algebraic construction, and one
classical analytic-number-theory input), so a four-child plan is the right shape.
For comparison: the counting theorem (s2) is of the difficulty of a hard olympiad
combinatorics problem; the construction (s3) is the Erdős–Turán Sidon set, a
standard textbook construction; the analytic input (s4) is a corollary of the
Prime Number Theorem, which Mathlib does **not** have (verified, Section 5.6).

## 2. Strategy

**The single idea: pass from the sequence to its partial sums and recognise a Sidon set.**

Put `s_0 = 0`, `s_i = a_1 + ⋯ + a_i`. Then the run sum `a_u + ⋯ + a_v` equals
`s_v − s_{u−1}`, so

> *all run sums of `a` are distinct*  ⟺  *all pairwise differences of `{s_0,…,s_k}` are distinct*
> ⟺  *`{s_0, …, s_k}` is a Sidon set*,

and the constraint `a_i ∈ [1,n]` says exactly that the consecutive gaps of that Sidon
set lie in `[1,n]`. Hence

> **`g(n)` = max `k` such that there is a Sidon set `0 = s_0 < s_1 < ⋯ < s_k` all of whose
> consecutive gaps lie in `[1,n]`.**

Everything else follows from this representation change.

*Upper bound (`2/3`).* For each fixed `r ≥ 1` count the `M_r = rk − r(r−1)/2` differences
`s_j − s_i` with `1 ≤ j − i ≤ r`. They are **distinct positive integers**, so their sum is
at least `M_r(M_r+1)/2`. On the other hand each gap `d_m` is used at most `u` times among
the index-gap-`u` differences, so the same sum is at most `(r(r+1)/2)·S` where `S = Σ d_m`.
Finally the gaps `d_m` are themselves `k` **distinct** integers in `[1,n]`, so
`S ≤ kn − k(k−1)/2`. Combining and letting `r → ∞` gives `k ≤ (2(r+1)/(3r+1))·n + O_r(1) → (2/3)n`.
This argument is elementary and self-contained; it is (a clean repackaging of) the standard
counting bound and was re-derived here from scratch and verified exhaustively by computer
(Section 4.2).

*Lower bound (`1/3`).* Use the **Erdős–Turán Sidon set**: for an odd prime `p`,
`s_j = (2p−1)·j + (j² mod p)`, `j = 0, …, p−1`. The `mod p` term lives in `[0,p−1]`, which is
strictly smaller than half of the "carrier" `2p−1`, so the set is Sidon; and every gap
lies in `[p, 3p−2]`. So `p` points with all gaps `≤ 3p−2`: exactly the ratio `1/3`.
Feeding `n ≈ 3p` therefore gives `g(n) ≥ p − 1 ≈ n/3`, **provided a prime exists at the
right scale**, i.e. provided `max{p prime : p ≤ x} ≥ (1−ε)x` for large `x`. That is the
only non-elementary ingredient and it is a standard corollary of the Prime Number Theorem.

*Where the difficulty sits.* It is genuinely **distributed**, but the single step whose
proof route is longest is the prime-density input s4 (PNT), which Mathlib lacks; it carries
the `[CRUX]` tag for that reason. Steps s2 and s3 carry the combinatorial/algebraic content
and both have complete proofs written out below.

## 3. Proof

Throughout, for `a : Fin k → ℕ` set
`d : ℕ → ℕ , d m = if h : m < k then a ⟨m,h⟩ else 0`, and `S i = ∑_{m < i} d m`
(so `S 0 = 0` and `S (m+1) − S m = a m` for `m < k`).

---

1. **[s0] [ELEM] Intervals of `Fin k` and the interval-sum dictionary.**

   A `Finset J` of a linear order is *order connected* iff it is `∅` or a closed interval:
   if `J ≠ ∅` and `(J : Set _).OrdConnected`, put `u = J.min' _`, `v = J.max' _`; then
   `J ⊆ Finset.Icc u v` trivially, and `Set.ordConnected_iff` applied to `u, v ∈ J`, `u ≤ v`
   gives `Set.Icc u v ⊆ J`, i.e. `J = Finset.Icc u v`. Conversely
   `Set.ordConnected_Icc` + `Finset.coe_Icc` show every `Finset.Icc u v` is order connected,
   and `∅` is order connected vacuously.

   For `u ≤ v` in `Fin k`, `∑_{x ∈ Finset.Icc u v} a x = S (v+1) − S u` (reindex by
   `Fin.val`, then `Finset.sum_Ico_eq_sum_range`). Distinct intervals `[u,v]` correspond
   bijectively to distinct pairs `(u, v+1)` with `0 ≤ u < v+1 ≤ k`. Therefore, if all
   `a i ≥ 1` (so every nonempty interval sum is `≥ 1 > 0 = ∑_∅`):

   > `HasDistinctSums a` ⟺ the map `(i,j) ↦ S j − S i` is injective on `{(i,j) : 0 ≤ i < j ≤ k}`.

   The `⟸` direction is what s3 needs, the `⟹` direction is what s1 and s2 need.
   *(This step is not a child: it is 20 lines of routine order/`Finset` manipulation, and
   it is re-proved inside each of s1, s2, s3, which are dispatched in parallel anyway.)*

2. **[s1] [LEMMA] `erdos357_g_spec` : for every `n : ℕ`,**
   ```lean
   Erdos357.g n ≤ n ∧
   (∀ (k : ℕ) (a : Fin k → ℕ), Set.range a ⊆ Set.Icc 1 n → Erdos357.HasDistinctSums a →
        k ≤ Erdos357.g n) ∧
   (∃ a : Fin (Erdos357.g n) → ℕ, Set.range a ⊆ Set.Icc 1 n ∧ Erdos357.HasDistinctSums a)
   ```

   *Why it is needed.* `g` is a `sSup` over `ℕ`; nothing can be done with it until we know
   the set is nonempty and bounded (otherwise Mathlib's `sSup` is `0`). This lemma packages
   "bounded", "attained" and "universal" once and for all.

   *Proof sketch (complete).* Write `G n = {k | ∃ a : Fin k → ℕ, Set.range a ⊆ Set.Icc 1 n ∧ HasDistinctSums a}`.
   * **Nonempty:** `0 ∈ G n` via the empty family `a : Fin 0 → ℕ`; `Set.range a = ∅ ⊆ _`, and
     the only order connected `Finset (Fin 0)` is `∅`, so `InjOn` is trivial.
   * **Bounded by `n`:** let `k ∈ G n` with witness `a`. Each singleton `{i}` (`i : Fin k`) is
     order connected (`Finset.Icc i i`), with sum `a i`. By `HasDistinctSums` the map
     `i ↦ a i` is injective, so `a` is an injection of `Fin k` into
     `Set.Icc 1 n ∩ ℕ`, a set of cardinality `n`. Hence `k ≤ n`.
     *(This uses only the singleton part of `HasDistinctSums`; no partial sums needed.)*
   * Therefore `BddAbove (G n)` (bound `n`) and `(G n).Nonempty`, so
     `Nat.sSup_mem` gives `g n ∈ G n` (third conjunct), `le_csSup` gives the second
     conjunct, and `g n ≤ n` is the first conjunct since `g n ∈ G n`.

   *Massive-simplification evidence.* This is a statement about one fixed `n`, with no
   asymptotics, no reals, no filters, no quantifier over `ε`. It is the `sSup` bookkeeping
   only; it contains none of the combinatorics of the target. See Section 4.1.

3. **[s2] [LEMMA] `erdos357_distinctSums_card_bound` :**
   ```lean
   ∀ (n k r : ℕ), 1 ≤ r → ∀ a : Fin k → ℕ,
     Set.range a ⊆ Set.Icc 1 n → Erdos357.HasDistinctSums a →
       (3 * r + 1) * k ≤ 2 * (r + 1) * n + 4 * r ^ 2
   ```

   *Complete proof.*

   **(0) Degenerate cases.** If `k = 0` the left side is `0`. If `r > k`, then `k ≤ r − 1`
   and `(3r+1)k ≤ (3r+1)(r−1) = 3r² − 2r − 1 ≤ 4r²` (because `r² + 2r + 1 ≥ 0`), so the
   bound holds. **Assume from now on `1 ≤ r ≤ k`.**

   **(1) Set-up.** By `Set.range a ⊆ Set.Icc 1 n`, `1 ≤ a i ≤ n` for all `i`. With
   `d, S` as above, `S` is strictly increasing on `{0,…,k}` and `S j − S i ≥ j − i ≥ 1`
   for `i < j`. By step s0, `(i,j) ↦ S j − S i` is **injective** on `P := {(i,j) : 0 ≤ i < j ≤ k}`.

   **(2) The gaps are `k` distinct elements of `[1,n]`.** `d_m := S(m+1) − S(m) = a m ∈ [1,n]`
   for `m < k`, and they are pairwise distinct because `(m, m+1) ∈ P` and the map in (1) is
   injective. Consequently `k ≤ n`.

   **(3) Bound on the total `S := S k = Σ_{m<k} d_m`.** Let `D ⊆ ℤ` be the image finset
   `{d_0,…,d_{k−1}}`; `|D| = k` by (2) and every element is `≤ n`. Mathlib's
   `Finset.sum_le_sum_range : (∀ x ∈ s, x ≤ c) → ∑_{x∈s} x ≤ ∑_{t < s.card} (c − t)` with
   `c = n` gives
   ```
        S ≤ Σ_{t=0}^{k−1} (n − t) = k·n − k(k−1)/2,     i.e.   2S ≤ 2kn − k(k−1).      (A)
   ```

   **(4) The short differences.** Put
   `P_r := {(i,j) ∈ P : j − i ≤ r}` and `M := |P_r| = Σ_{u=1}^{r} (k+1−u) = r(k+1) − r(r+1)/2`,
   so that
   ```
        2M = r(2k − r + 1).                                                            (B)
   ```
   (The count is legitimate because `r ≤ k`, so each `u ∈ [1,r]` contributes `k+1−u ≥ 1` pairs.)
   By (1) the `M` values `{S j − S i : (i,j) ∈ P_r}` are **distinct positive integers**, so
   Mathlib's `Finset.sum_range_le_sum : (∀ x ∈ s, c ≤ x) → ∑_{t<s.card}(c+t) ≤ ∑_{x∈s} x`
   with `c = 1` gives, for `Σ := Σ_{(i,j)∈P_r} (S j − S i)`,
   ```
        2Σ ≥ M(M+1) ≥ M².                                                              (C)
   ```

   **(5) Double counting `Σ` from above.** Group by index gap `u = j − i`:
   ```
        Σ = Σ_{u=1}^{r} Σ_{i=0}^{k−u} (S(i+u) − S(i)) ,     S(i+u) − S(i) = Σ_{m=i}^{i+u−1} d_m .
   ```
   For a fixed `u`, the coefficient of `d_m` in the inner sum is
   `#{i ∈ [0,k−u] : i ≤ m ≤ i+u−1} = #([m−u+1, m] ∩ [0, k−u]) ≤ u`. Hence the inner sum is
   `≤ u·S`, and
   ```
        2Σ ≤ r(r+1)·S.                                                                 (D)
   ```

   **(6) Combine.** From (C), (D), (A):
   ```
        2M² ≤ 2·(2Σ) − ... more directly:  M² ≤ 2Σ ≤ r(r+1)S  and  2S ≤ 2kn − k(k−1)
        ⟹ 2M² ≤ r(r+1)(2kn − k(k−1)) = r(r+1)·k·(2n − k + 1).
   ```
   Multiplying by `2` and substituting `2M = r(2k−r+1)` from (B):
   ```
        r²(2k − r + 1)² ≤ 2r(r+1)·k·(2n − k + 1),
   ```
   and dividing by `r ≥ 1`:
   ```
        r(2k − r + 1)² ≤ 2(r+1)·k·(2n − k + 1).                                        (★)
   ```
   (All quantities are positive: `2k − r + 1 ≥ k + 1 > 0` since `r ≤ k`, and `2n − k + 1 > 0`
   since `k ≤ n`.)

   **(7) Finish.** `(2k − r + 1)² = 4k² − 4k(r−1) + (r−1)² ≥ 4k(k − r + 1)`. Plugging into (★):
   ```
        4rk(k − r + 1) ≤ 2(r+1)k(2n − k + 1) ;
   ```
   divide by `2k > 0`:
   ```
        2r(k − r + 1) ≤ (r+1)(2n − k + 1)
        2rk − 2r(r−1) ≤ 2(r+1)n − (r+1)k + (r+1)
        (3r + 1)k ≤ 2(r+1)n + 2r² − r + 1 ≤ 2(r+1)n + 4r²      (since r ≥ 1).           ∎
   ```

   *Verification.* Every inequality (A)–(★) and the final bound were checked exhaustively
   against **all 1102 valid configurations with `n ≤ 7`** and all `r ≤ min(8,k)`; see
   Section 4.2. The consequence `2(r+1)/(3r+1) → 2/3` is tabulated in Section 4.3.

   *Massive-simplification evidence.* Purely finite and quantifier-free in the analytic
   sense: one `∀ n k r`, no reals, no limits, no `sSup`, no existential over functions
   `ℕ → ℝ`. It is a statement about a *single given witness*, whereas the target quantifies
   over all `n` simultaneously and asserts an asymptotic two-sided estimate.

4. **[s3] [LEMMA] `erdos357_erdosTuran_witness` :**
   ```lean
   ∀ p : ℕ, Nat.Prime p → 3 ≤ p →
     ∃ a : Fin (p - 1) → ℕ,
       Set.range a ⊆ Set.Icc 1 (3 * p - 2) ∧ Erdos357.HasDistinctSums a
   ```

   *The explicit object.* Let `C := 2p − 1`, `r_j := j² mod p ∈ [0, p−1]`, and
   ```
        S_j := C·j + r_j          (j = 0, 1, …, p−1),
        a_i := S_{i+1} − S_i      (i = 0, 1, …, p−2,  i.e. i : Fin (p−1)).
   ```
   Explicitly `a_i = (2p−1) + r_{i+1} − r_i`.
   *Example `p = 5`*: `r = (0,1,4,4,1)`, `C = 9`, `S = (0,10,22,31,37)`, `a = (10,12,9,6)`,
   all in `[5,13] = [p, 3p−2]`; the ten differences are
   `{10,22,31,37,12,21,27,9,15,6}` — all distinct. Hence `g(13) ≥ 4`.

   *Complete proof.*

   **(i) Range.** `r_j ∈ [0,p−1]`, so `a_i = (2p−1) + (r_{i+1} − r_i) ∈ [(2p−1)−(p−1), (2p−1)+(p−1)] = [p, 3p−2]`.
   Since `p ≥ 3 ≥ 1`, `1 ≤ a_i ≤ 3p−2`, i.e. `Set.range a ⊆ Set.Icc 1 (3p−2)`.
   In particular `S` is strictly increasing, so the ℕ-subtraction above is honest.

   **(ii) Reduction to injectivity (step s0, `⟸` direction).** Since all `a_i ≥ 1`, by s0 it
   suffices to prove: for `0 ≤ i₁ < j₁ ≤ p−1` and `0 ≤ i₂ < j₂ ≤ p−1`,
   `S_{j₁} − S_{i₁} = S_{j₂} − S_{i₂}` implies `i₁ = i₂ ∧ j₁ = j₂`.
   (Note that the index range of `a` is `Fin (p−1)`, so the interval endpoints `(u, v+1)`
   range exactly over pairs `0 ≤ u < v+1 ≤ p−1`.)

   **(iii) Splitting off the carrier.** Rewrite the hypothesis additively:
   `S_{j₁} + S_{i₂} = S_{j₂} + S_{i₁}`, i.e.
   ```
        C·(j₁ + i₂) + (r_{j₁} + r_{i₂}) = C·(j₂ + i₁) + (r_{j₂} + r_{i₁}).
   ```
   Both `r`-sums lie in `[0, 2p−2]`, so their difference has absolute value `≤ 2p−2 < 2p−1 = C`.
   Hence `C·|(j₁+i₂) − (j₂+i₁)| ≤ 2p−2 < C`, forcing
   ```
        j₁ + i₂ = j₂ + i₁        and        r_{j₁} + r_{i₂} = r_{j₂} + r_{i₁}.          (E)
   ```

   **(iv) The quadratic identity mod `p`.** Since `r_j ≡ j² (mod p)`, the second half of (E)
   gives `j₁² + i₂² ≡ j₂² + i₁² (mod p)`. Let `A := j₁ + i₂ = j₂ + i₁`. Expanding
   `A² = j₁² + 2 j₁ i₂ + i₂² = j₂² + 2 j₂ i₁ + i₁²` and subtracting,
   ```
        2(j₁ i₂ − j₂ i₁) ≡ 0 (mod p) ,   and `p` is odd, so   j₁ i₂ ≡ j₂ i₁ (mod p).
   ```

   **(v) Factorisation.** Substitute `j₂ = j₁ + i₂ − i₁` (from (E)) into `j₁i₂ ≡ j₂i₁`:
   ```
        j₁ i₂ ≡ (j₁ + i₂ − i₁) i₁ = j₁ i₁ + i₂ i₁ − i₁²
        ⟹ j₁(i₂ − i₁) − i₁(i₂ − i₁) ≡ 0
        ⟹ p ∣ (i₂ − i₁)(j₁ − i₁)      (in ℤ).
   ```
   Now `0 < j₁ − i₁ ≤ p − 1 < p`, so `p ∤ (j₁ − i₁)`; as `p` is prime, `p ∣ (i₂ − i₁)`.
   Since `|i₂ − i₁| ≤ p − 1 < p`, we get `i₁ = i₂`, and then `j₁ = j₂` from (E). ∎

   *Verification.* The construction was checked by computer to be Sidon, with
   `min gap ≥ p` and `max gap ≤ 3p−2`, for `p = 3,5,7,11,13,17,19,23,31,101,211`;
   the ratio `k/n = (p−1)/(3p−2)` increases to `1/3` (Section 4.4).

   *Massive-simplification evidence.* This is a single explicit finite construction for one
   prime; it involves no asymptotics, no `sSup`, no `ε`. Its proof is four lines of
   modular arithmetic (steps (iii)–(v)). It is incomparably smaller than the target.

5. **[s4] [LEMMA] [CRUX] `exists_prime_in_short_interval` :**
   ```lean
   ∀ ε : ℝ, 0 < ε →
     ∀ᶠ x : ℝ in Filter.atTop, ∃ p : ℕ, Nat.Prime p ∧ (1 - ε) * x ≤ (p : ℝ) ∧ (p : ℝ) ≤ x
   ```

   *Why this exact statement.* The construction s3 produces `p − 1` terms bounded by `3p − 2`.
   To conclude `g(n) ≥ (1/3 − ε)n` we need a prime `p` with `3p − 2 ≤ n` and `p ≥ (1−δ)n/3`,
   i.e. a prime in `[(1−δ)x, x]` with `x = (n+2)/3`. **Nothing weaker suffices**: by the
   analysis in Section 5.3, the whole lower bound is equivalent to
   `limsup_x (max{p prime : p ≤ x}) / x = 1`, i.e. `p_{m+1}/p_m → 1`.

   *Proof sketch / route.* This is the standard corollary of the **Prime Number Theorem**:
   `π(x) ∼ x / log x` gives `π(x) − π((1−ε)x) ∼ ε x / log x → ∞`, so the interval contains
   a prime for `x` large. Equivalently, via Chebyshev's `θ`: `θ(x) ∼ x` gives
   `θ(x) − θ((1−ε)x) ∼ εx > 0`.
   **Mathlib status (probed, Section 5.6): Mathlib has `Mathlib.NumberTheory.Chebyshev`
   (`Chebyshev.theta`, `Chebyshev.psi`, `Chebyshev.theta_le_log4_mul_x`,
   `Chebyshev.eventually_primeCounting_le`) and `Nat.exists_prime_lt_and_le_two_mul`
   (Bertrand), but it does NOT contain `θ(x) ∼ x` or `π(x) ∼ x/log x`.**
   Chebyshev-type bounds alone cannot give this statement: they yield
   `c₁ x ≤ θ(x) ≤ c₂ x` with `c₂/c₁ ≥ 2` in Mathlib (`log 4` vs `log 2`), hence only primes
   in `(x, 2x]`, which yields the weaker `liminf g(n)/n ≥ 1/6`.
   So the sub-decomposition of this node must formalise `θ(x) ∼ x`, e.g. by the
   Wiener–Ikehara/Newman contour route (as in the `PrimeNumberTheoremAnd` project of
   Kontorovich–Tao, <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd>) or by the
   Erdős–Selberg elementary route. This is a long but entirely standard development; it is
   the honest bottleneck of the problem and is flagged again in Section 7.

   *Massive-simplification evidence.* It is a statement about primes alone: it mentions
   neither `g` nor `HasDistinctSums` nor any combinatorics. It is a named classical theorem
   with a fully documented proof, and is strictly weaker than PNT.

6. **[s5] [ELEM] Monotonicity of `g`.**
   For `m ≤ n`: by s1(m) third conjunct take a witness `a : Fin (g m) → ℕ` with
   `Set.range a ⊆ Set.Icc 1 m ⊆ Set.Icc 1 n` and `HasDistinctSums a`; by s1(n) second
   conjunct, `g m ≤ g n`. Hence `Monotone g`.

7. **[s6] [ELEM] Assembly.**

   **(a) Upper asymptotic.** *Claim:* `∀ ε > 0, ∀ᶠ n : ℕ in atTop, (g n : ℝ) ≤ (2/3 + ε) * n`.
   Fix `ε > 0` and choose `r : ℕ` with `r ≥ 1` and `4 / (3(3r+1)) ≤ ε/2`, e.g.
   `r := max 1 ⌈8/(9ε)⌉`. By s1(n) third conjunct pick a witness for `k = g n`; s2 gives
   `(3r+1)·g n ≤ 2(r+1)·n + 4r²`. Dividing by `3r+1 > 0` in `ℝ` and using the identity
   `2(r+1)/(3r+1) = 2/3 + 4/(3(3r+1))`:
   ```
        g n ≤ (2/3 + 4/(3(3r+1)))·n + 4r²/(3r+1) ≤ (2/3 + ε/2)·n + 4r².
   ```
   For all `n ≥ 8r²/ε` we have `4r² ≤ (ε/2)·n`, hence `g n ≤ (2/3 + ε)·n`. ∎

   **(b) Lower asymptotic.** *Claim:* `∀ ε > 0, ∀ᶠ n : ℕ in atTop, (1/3 − ε)·n ≤ (g n : ℝ)`.
   We may assume `ε ≤ 1/3` (a smaller `ε` gives a stronger statement). Put `δ := 3ε/2 ≤ 1/2`.
   Apply s4 with `δ`: there is `X` such that every real `x ≥ X` admits a prime `p` with
   `(1−δ)x ≤ p ≤ x`. Take `x := (n+2)/3`; for `n` large, `x ≥ X` and also
   `p ≥ (1−δ)(n+2)/3 ≥ n/6 ≥ 3`, so `p` is an odd prime.
   From `p ≤ (n+2)/3` we get `3p ≤ n+2`, i.e. `3p − 2 ≤ n`.
   By s3, `p − 1 ≤ g(3p−2)`; by s5 (monotonicity), `g(3p−2) ≤ g n`. Therefore
   ```
        g n ≥ p − 1 ≥ (1−δ)(n+2)/3 − 1 ≥ (1−δ)n/3 − 1 = n/3 − (δ/3)n − 1 = n/3 − (ε/2)n − 1.
   ```
   For `n ≥ 2/ε` we have `1 ≤ (ε/2)n`, so `g n ≥ n/3 − ε·n = (1/3 − ε)·n`. ∎

   **(c) The `o`-functions.** Define
   ```
        o  : ℕ → ℝ ,  o  n := min 0 ((g n : ℝ)/n − 1/3),
        o' : ℕ → ℝ ,  o' n := max 0 ((g n : ℝ)/n − 2/3).
   ```
   *Membership in the `Icc`, for every `n`.*
   If `n ≥ 1` then, multiplying through by `n > 0` and using `n·min 0 t = min 0 (n t)`,
   ```
        (1/3 + o n)·n = n/3 + min 0 (g n − n/3) = min (n/3) (g n) ≤ g n,
        (2/3 + o' n)·n = 2n/3 + max 0 (g n − 2n/3) = max (2n/3) (g n) ≥ g n.
   ```
   If `n = 0`, then in Lean `(g 0 : ℝ)/0 = 0`, so `o 0 = min 0 (−1/3) = −1/3`,
   `o' 0 = max 0 (−2/3) = 0`, and both endpoints are `(1/3 − 1/3)·0 = 0` and `(2/3+0)·0 = 0`,
   while `g 0 = 0` (indeed `Set.Icc 1 0 = ∅` in `ℕ` forces `k = 0`); so `0 ∈ Icc 0 0`. ✓
   Hence the `∀ᶠ` holds — in fact for **all** `n`.
   *`o =o[atTop] 1`.* By `Asymptotics.isLittleO_one_iff` this is `Tendsto o atTop (𝓝 0)`.
   We have `−1/3 ≤ o n ≤ 0` always, and `|o n| = max 0 (1/3 − (g n)/n)`. Given `ε > 0`,
   by (b) eventually `g n ≥ (1/3 − ε)n` with `n ≥ 1`, hence `(g n)/n ≥ 1/3 − ε` and
   `|o n| ≤ ε`. So `o → 0`.
   *`o' =o[atTop] 1`.* Symmetrically: `o' n ≥ 0` and `|o' n| = max 0 ((g n)/n − 2/3) ≤ ε`
   eventually by (a). So `o' → 0`.

   Supplying `o`, `o'` to the goal's existential and discharging the three conjuncts with
   the above finishes the theorem. ∎

## 4. Supporting Evidence & Positive Test Cases

All computations were run with `scratch/verify.py` and `scratch/verify2.py`.

### 4.1 Exact values of `g(n)` by exhaustive search

Exhaustive DFS over all gap sequences `d ∈ [1,n]^k` keeping all block sums distinct:

| `n` | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|---|---|---|---|---|
| `g(n)` | 0 | 1 | 2 | 3 | 3 | 4 | 5 | 6 | 6 | 7 |
| `g(n)/n` | — | 1.000 | 1.000 | 1.000 | .750 | .800 | .833 | .857 | .750 | .778 |

(Matches OEIS-style expectations for the "all consecutive sums distinct, values ≤ n,
repeats allowed" quantity. Note `g(0) = 0`, confirming the degenerate case: `Set.Icc 1 0 = ∅`
in `ℕ`, so the only admissible `k` is `0`, and `sSup {0} = 0`.)

### 4.2 The full inequality chain of s2, verified exhaustively

For **every** valid configuration with `n ≤ 7` (1102 of them) and every `r` with
`1 ≤ r ≤ min(8, k)`, the script asserted each of:

* the gaps `d_m` are pairwise distinct;
* `2S ≤ 2kn − k(k−1)`  (inequality (A));
* `|P_r| = M = rk − r(r−1)/2`, and the `M` differences are pairwise distinct;
* `2Σ ≥ M(M+1)`  (inequality (C));
* `2Σ ≤ r(r+1)S`  (inequality (D));
* `2M² ≤ r(r+1)·k·(2n − k + 1)` (the combination in step (6));
* `(3r+1)k ≤ 2(r+1)n + 2r² − r + 1` (the sharp final form);
* `(3r+1)k ≤ 2(r+1)n + 4r²` (the stated form).

**All 1102 configurations passed all assertions** (script output:
`checked 1102 configurations, all inequalities hold`).
Additionally the degenerate branch `r > k` was checked for all `1 ≤ n < 60`, `0 ≤ k ≤ n`,
`1 ≤ r < 200`: **0 violations**.

### 4.3 The bound `2(r+1)/(3r+1) → 2/3`

Value of `((2(r+1)n + 4r²)/(3r+1))/n`, i.e. the bound on `g(n)/n`:

| `n \ r` | 1 | 2 | 3 | 5 | 10 | 50 | 200 |
|---|---|---|---|---|---|---|---|
| 5 | 1.2000 | 1.3143 | 1.5200 | 2.0000 | 3.2903 | 13.92 | 53.91 |
| 20 | 1.0500 | 0.9714 | 0.9800 | 1.0625 | 1.3548 | 3.99 | 13.98 |
| 100 | 1.0100 | 0.8800 | 0.8360 | 0.8125 | 0.8387 | 1.3377 | 3.3311 |
| 1000 | 1.0010 | 0.8594 | 0.8036 | 0.7562 | 0.7226 | 0.7417 | 0.9351 |
| 10⁶ | 1.0000 | 0.8571 | 0.8000 | 0.7500 | 0.7097 | 0.6756 | 0.6692 |

The limiting envelope is `2(r+1)/(3r+1)`: `1, 6/7 ≈ .857, .8, .75, .710, .676, .669 → 2/3`,
exactly as the algebra predicts. For a fixed `ε`, choosing `r ≈ 8/(9ε)` and then `n ≥ 8r²/ε`
realises `g(n) ≤ (2/3 + ε)n`.

### 4.4 The Erdős–Turán construction, verified

`S_j = (2p−1)j + (j² mod p)`, `j = 0..p−1`:

| `p` | points | Sidon? | min gap | max gap | `3p−2` | `k = p−1` | `n = 3p−2` | `k/n` |
|---|---|---|---|---|---|---|---|---|
| 3 | 3 | ✔ | 5 | 6 | 7 | 2 | 7 | .2857 |
| 5 | 5 | ✔ | 6 | 12 | 13 | 4 | 13 | .3077 |
| 7 | 7 | ✔ | 10 | 16 | 19 | 6 | 19 | .3158 |
| 11 | 11 | ✔ | 16 | 26 | 31 | 10 | 31 | .3226 |
| 13 | 13 | ✔ | 16 | 34 | 37 | 12 | 37 | .3243 |
| 17 | 17 | ✔ | 20 | 46 | 49 | 16 | 49 | .3265 |
| 19 | 19 | ✔ | 26 | 48 | 55 | 18 | 55 | .3273 |
| 23 | 23 | ✔ | 30 | 60 | 67 | 22 | 67 | .3284 |
| 31 | 31 | ✔ | 40 | 82 | 91 | 30 | 91 | .3297 |
| 101 | 101 | ✔ | 110 | 292 | 301 | 100 | 301 | .3322 |
| 211 | 211 | ✔ | 236 | 606 | 631 | 210 | 631 | .3328 |

In every case `min gap ≥ p` and `max gap ≤ 3p−2`, and the set is Sidon.
`k/n = (p−1)/(3p−2) ↗ 1/3`.

Worked instance `p = 5` (fully explicit, as in step s3):
`r = (0,1,4,4,1)`, `C = 9`, `S = (0,10,22,31,37)`, gaps `a = (10,12,9,6) ⊆ [5,13]`,
differences `{10,22,31,37,12,21,27,9,15,6}` — 10 distinct values, so
`HasDistinctSums` holds and `g(13) ≥ 4`. (Brute force also confirms `g(13) ≥ 4`.)

### 4.5 Consistency of s2 with s3

The two bounds must not contradict. For `p = 211`: `n = 631`, `k = 210`. s2 with `r = 10`:
`(3·10+1)·210 = 6510 ≤ 2·11·631 + 400 = 13882 + 400 = 14282` ✔. The upper bound is far
above the construction, as it must be — the truth for this problem is somewhere in
`[1/3, 2/3]` and pinning it down is open.

### 4.6 Indexing / type translation table (Lean `ℕ` vs. informal 1-indexing)

| informal | Lean | note |
|---|---|---|
| `a_1,…,a_k` (1-indexed) | `a : Fin k → ℕ`, entries `a 0,…,a (k−1)` | shift by one |
| run sum `Σ_{u ≤ i ≤ v} a_i` | `∑ x ∈ Finset.Icc u v, a x`, `u v : Fin k` | `Finset.Icc` is inclusive |
| `s_i = a_1+⋯+a_i` | `S i = ∑_{m ∈ range i} d m`, `S 0 = 0` | `S : ℕ → ℕ`, `0 ≤ i ≤ k` |
| run sum `= s_v − s_{u−1}` | `∑_{Icc u v} a = S (v+1) − S u` | `(u, v+1)`, `0 ≤ u < v+1 ≤ k` |
| `1 ≤ a_i ≤ n` | `Set.range a ⊆ Set.Icc 1 n` | in `ℕ`; forces `Icc 1 0 = ∅` at `n=0` |
| E–T index `j = 0..p−1` | `S_j`, `p` points, `p−1` gaps, `a : Fin (p−1) → ℕ` | `p−1` is ℕ-subtraction, safe since `p ≥ 3` |

Checked numerically at `n = 0, 1, 2` and `p = 3, 5` (Sections 4.1, 4.4): no off-by-one.

## 5. Adversarial Refutation & Falsification Attempts

### 5.1 "`g(n)/n` exceeds `2/3` for small `n` — is the statement false?"
Yes, `g(7)/7 = 6/7 = 0.857 > 2/3`, and `g(1)/1 = g(2)/2 = g(3)/3 = 1`. This does **not**
refute the target: the claim is `∀ᶠ n in atTop` and `o'` is allowed to be positive.
With our definition `o'(7) = 6/7 − 2/3 = 0.190`, and the `Icc` membership still holds at
`n = 7`. Only `o' → 0` is required, which is an asymptotic statement. ✔ Survived.
It does, however, show that any plan asserting the bound *for all `n`* would be **false** —
our step s6(c) deliberately produces an `o'` that absorbs the small-`n` excess exactly.

### 5.2 "`n = 0`: `sSup` of an empty or unbounded set"
`Set.Icc 1 0 = ∅` in `ℕ`, so `Set.range a ⊆ ∅` forces `k = 0`; the set is `{0}`, nonempty and
bounded, `g 0 = 0`. Both endpoints of the `Icc` evaluate to `0` and `0 ∈ Icc 0 0`. ✔
Also checked: the set is *always* nonempty (`k = 0` works: `Fin 0 → ℕ` has empty range and
the only order-connected `Finset (Fin 0)` is `∅`) and *always* bounded by `n`
(s1's singleton argument). So Mathlib's `sSup = 0` fallback for unbounded sets never fires.

### 5.3 "Can the existential over `o, o'` be satisfied cheaply, dodging the hard bounds?"
No. Suppose `o → 0` and eventually `(1/3 + o n)n ≤ g n`. Fix `ε > 0`; eventually
`o n > −ε`, hence eventually `g n > (1/3 − ε)n`. So the target *implies* (LB), and dually
(UB). Conversely (LB)+(UB) imply the target (step s6(c)). The target is therefore
**exactly** equivalent to (LB)∧(UB); there is no cheap witness. This is the reason the
plan cannot be shortened, and the reason s4 (prime density) is genuinely needed.

### 5.4 "Is the `2/3` derivation too strong (would it contradict the construction)?"
Tested: the s2 bound evaluated on the actual Erdős–Turán configurations (Section 4.5) is
comfortably satisfied; and on all 1102 exhaustively enumerated configurations with `n ≤ 7`
(Section 4.2). Also the derivation's weakest link — the step
`(2k−r+1)² ≥ 4k(k−r+1)` — is an identity plus `(r−1)² ≥ 0`, hence never lossy in the wrong
direction. No counterexample found. ✔

### 5.5 "Does the Erdős–Turán Sidon proof need `p` odd, and does it break at `p = 2`?"
Step (iv) divides by `2` modulo `p`; this is invalid for `p = 2`. We therefore require
`p ≥ 3` in s3, and s6(b) only ever applies s3 to primes `p ≥ n/6 ≥ 3`. Also checked that
`p − 1` (ℕ-subtraction) is harmless because `p ≥ 3`. ✔

### 5.6 "Is there an elementary substitute for the prime-density input s4?"
Falsification attempt, and the one that **partially succeeded** (it shows the plan's real
risk, not that the plan is wrong):
* Mathlib probe (`scratch/probe.lean`, `scratch/probe2.lean`, plus two
  `lean_search_tool_bin` queries) returned: `Nat.exists_prime_lt_and_le_two_mul` (Bertrand),
  `Chebyshev.theta`, `Chebyshev.psi`, `Chebyshev.theta_le_log4_mul_x`,
  `Chebyshev.eventually_primeCounting_le`, `Chebyshev.primeCounting_sub_theta_div_log_isBigO`
  — **no `θ(x) ∼ x`, no `π(x) ∼ x/log x`.** PNT is not in Mathlib.
* With only Chebyshev constants `log 2 ≤ θ(x)/x ≤ log 4` the argument gives a prime in
  `(x, 2x]`, hence only `liminf g(n)/n ≥ 1/6`, not `1/3`.
* I attempted three ways to remove the prime-density requirement; **all three were refuted**:
  1. *Use a prime `p ≤ n/3` far from `n/3` and enlarge `C`.* Refuted: enlarging `C` never
     increases the number of points; the count is `p` regardless of `C`.
  2. *Build a "graph-Sidon" function `σ : [0,m) → [0,R)` (all difference vectors
     `(j−j′, σ(j)−σ(j′))` distinct, `R ≈ m`) for composite `m` via a twisted product
     `σ(pa+b) = ((b+λa)² mod p) + p·τ(a)`.* Refuted by explicit counterexample:
     with `p = 5, t = 2, λ = 1, τ = (0,1)`, take `j₁ = 2, j₂ = 5, j₃ = 6, j₄ = 1`:
     `j₁+j₂ = 7 = j₃+j₄` and `σ(2)+σ(5) = 4+6 = 10 = 9+1 = σ(6)+σ(1)` while
     `{2,5} ≠ {6,1}`. The "rectangle" obstruction of product constructions survives the twist.
  3. *Interleave / insert extra points into an Erdős–Turán set.* Refuted on cardinality
     grounds for the natural parameter range, and greedy insertion only yields `O(n^{1/3})`
     extra points (the forbidden set for a new point has size `Θ(k³)`, which must fit in a
     window of length `n`).
  Conclusion: the ratio-`1/3` lower bound really does need
  `max{p prime : p ≤ x} = (1−o(1))x`, i.e. `p_{m+1}/p_m → 1`. This is recorded as the
  principal risk in Section 7 and in `findings.md`.

### 5.7 "Is `HasDistinctSums` really the Sidon condition — did I mis-read `OrdConnected`?"
`Set.ordConnected_iff : s.OrdConnected ↔ ∀ x ∈ s, ∀ y ∈ s, x ≤ y → Set.Icc x y ⊆ s` (probed).
For a *finset* of a linear order this forces `J = ∅` or `J = Finset.Icc (min' J) (max' J)`.
So `HasDistinctSums` quantifies over `∅` and the closed intervals only, and — because all
`a i ≥ 1` makes the empty sum `0` distinct from every interval sum — it is precisely
"all run sums distinct". Cross-checked against the docstring in `problem.lean`
("all sums of the shape `Σ_{u ≤ i ≤ v} a_i` are distinct"). ✔
Adversarial sub-case: could a *degenerate* interval matter? `Finset.Icc u u = {u}`, whose
sum is `a u`; this is exactly the fact used in s1 to prove `k ≤ n`. ✔

### 5.8 "Does the assembly `o`/`o'` formula break anywhere?"
Tested at `n = 0` (Section 5.2), at `n = 7` where `g n > (2/3)n` (Section 5.1), and at
`n = 4, 8` where `g n < (1/3)n` is false but `g n/n = .75, .75 > 1/3` so `o n = 0`. The
formulas `min (n/3) (g n) ≤ g n` and `max (2n/3) (g n) ≥ g n` are unconditional for `n ≥ 1`.
No boundary failure. ✔

## 6. Freshness & Anti-Recycling Audit

* This is the **root** node with `Proof Attempts: 0` and `Decomposition Attempts: 0`
  (`context.md` §5). There is no prior decomposition history, no retired subgoal set, and
  no `findings.md` with prior content, so **no subgoal here can be a recycled failure**.
* `§9 Subtree Ledger`: *No live decomposition.* `§10 Reusable Proved Lemmas`: *nothing in scope.*
* `get_accessible_nodes` for this node returned **`(None available)`** (run 2026-09-27),
  so there are no siblings, cousins, or unproved peers; no step cites any node.
* All four `[LEMMA]` steps (s1, s2, s3, s4) are freshly stated here from first principles and
  mention only `Erdos357.g`, `Erdos357.HasDistinctSums`, and `Nat.Prime`.
* No step cites a Mathlib name that was not confirmed to exist by a `#check` probe
  (`scratch/probe.lean`, `scratch/probe2.lean`).

## 7. Open Risks

1. **s4 (`[CRUX]`) is the Prime Number Theorem and Mathlib does not have it.**
   This is the dominant risk of the whole plan. Probes confirmed `Mathlib.NumberTheory.Chebyshev`
   stops at `θ(x) ≤ x·log 4` / `π(x) ≤ (log 4 + ε)x/log x`. The child will have to develop
   `θ(x) ∼ x` (Newman/Wiener–Ikehara, or the Erdős–Selberg elementary proof). Falsifier:
   if a future planner finds a genuinely elementary lower-bound construction of density
   `1/3` that avoids prime density, s4 becomes unnecessary — but Section 5.6 records three
   refuted attempts at exactly that, so I do not expect one.
   *Fallback that is NOT acceptable:* replacing `1/3` by `1/6` (which Bertrand gives) does
   **not** prove the target, since the target is equivalent to `liminf ≥ 1/3` (Section 5.3).
2. **s2's double counting in Lean.** The coefficient bound `c_{u,m} ≤ u` in step (5) is an
   intersection-of-intervals cardinality count; if the formaliser finds re-indexing
   `Σ_{u} Σ_{i} Σ_{m}` painful, the alternative is to prove
   `Σ_{i=0}^{k−u}(S(i+u) − S(i)) = Σ_{i=0}^{k−u} Σ_{m∈Ico i (i+u)} d m ≤ u · S` by
   `Finset.sum_le_sum` after `Finset.sum_comm`. Falsifier: none mathematically; this is a
   formalisation-effort risk only, and it was verified numerically (Section 4.2, inequality (D)).
3. **s2 step (7) divides by `2k`.** Valid only for `k ≥ 1`; the `k = 0` case is handled
   separately in step (0). Likewise (★) needs `r ≤ k`, also handled in step (0).
   Both branches were machine-checked (Section 4.2).
4. **s3's `Finset.Icc` sums over `Fin (p−1)`.** ℕ-subtraction `p − 1` and the reindexing
   `Fin (p−1) ↪ ℕ` are the fiddly parts. Mitigation: `p ≥ 3` is a hypothesis, and the
   blueprint fixes the dictionary in Section 4.6. Falsifier: an off-by-one would show up as
   a wrong gap count; verified numerically for `p = 3, 5, 7, …, 211` (Section 4.4).
5. **s6(c) at `n = 0`.** Relies on Lean's `x / 0 = 0` convention making `o 0 = −1/3`; the
   `Icc` membership still holds because both endpoints are `0`. If a formaliser prefers, it
   can restrict the `∀ᶠ` to `n ≥ 1`, which is all that is required. Low risk.
6. **The true constant is unknown.** `limsup g(n)/n` is not known (it lies in `[1/3, 2/3]`).
   Nothing in the plan pretends otherwise; both bounds are proved separately and neither is
   claimed to be tight.
