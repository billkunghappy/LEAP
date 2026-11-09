# Blueprint: erdos_1095.variants.upper_conjecture
Revision: 1

## 1. Statement

**Formal target (verbatim from `problem.lean`):**

```lean
noncomputable def g (k : ℕ) : ℕ := sInf {m | k + 1 < m ∧ k < (m.choose k).minFac}

theorem erdos_1095.variants.upper_conjecture :
    ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧ ∀ᶠ k in atTop, g k ≤ exp (k * (1 + f k))
```

**Plain mathematics.** `g k` is the *Erdős–Selfridge function*: the least integer `n > k+1`
such that every prime factor of `C(n,k)` exceeds `k` (OEIS **A003458**; introduced in
[EES74] Ecklund–Erdős–Selfridge, *A new function associated with the prime factors of
$\binom nk$*, Math. Comp. 28 (1974), 647–649). The target asserts

$$\limsup_{k\to\infty}\frac{\log g(k)}{k}\le 1,$$

i.e. $g(k)\le e^{k(1+o(1))}$. (§3 step **s1** turns the $\limsup$ form into the exact
`∃ f → 0` form, with `f` written down explicitly, so the two really are the same claim
here — no strengthening, no weakening.)

*Definitional check performed:* I verified by brute force (`scratch/validate.py`) that the
Lean `sInf` definition reproduces A003458 exactly for $k=1,\dots,13$:
$3,6,7,7,23,62,143,44,159,46,47,174,2239$. So there is no indexing or off-by-one mismatch,
and in particular the defining set is **not** empty (the `sInf ∅ = 0` loophole does not
arise and is not used anywhere in this plan).

**Calibration.** This is harder than a textbook exercise and harder than a typical Putnam
problem. It is a *research-level* statement whose honest proof has two clearly separated
halves:

* an elementary **construction + sieve** half (Kummer/Lucas digit criterion, CRT, a union
  bound) — comparable in difficulty to a hard olympiad/graduate-exercise chain, and
  *fully written out below to bedrock*; and
* one **analytic input**: $\theta(x)\le(1+o(1))x$, i.e. the upper half of the **Prime
  Number Theorem**. I probed Mathlib and this is **not present** (Mathlib currently has only
  the Chebyshev bound `Chebyshev.psi_le : ψ x ≤ log 4 · x + 2√x log x`, and
  `Chebyshev.eventually_primeCounting_le` with constant `log 4 + ε`). §5 shows the
  $\log 4$ constant is *provably insufficient* for this target, so PNT is a genuine,
  unavoidable dependency of this route, not laziness.

Expected number of genuinely separable claims: **six** (one analytic crux + five
independent elementary lemmas). That is the shape below.

## 2. Strategy

**The single idea: Kummer's/Lucas' digit criterion turns "all prime factors of $\binom nk$
exceed $k$" into a purely *digit-wise domination* condition, which is a system of
congruences; satisfy the expensive ones by CRT and the cheap ones by a union-bound sieve.**

By Lucas' theorem, for a prime $p$,
$$p\nmid\binom nk \iff \forall i,\ \big\lfloor k/p^i\big\rfloor \bmod p \ \le\ \big\lfloor n/p^i\big\rfloor \bmod p ,$$
i.e. every base-$p$ digit of $k$ is at most the corresponding digit of $n$. So we must
produce **one** $n>k+1$ whose base-$p$ digits dominate those of $k$ **simultaneously for
every prime $p\le k$**, with $\log n\le(1+o(1))k$.

Fix a small $\varepsilon>0$ and split the primes at $\varepsilon k$.

* **Small primes $p\le\varepsilon k$** (there are few, and $\sum_{p\le\varepsilon k}\log(\text{least }p\text{-power}>k)=O(\varepsilon k)$):
  force *all* relevant digits of $n$ to be $p-1$, the maximum, by putting the full prime
  power $p^{a_p}>k$ into a modulus $R$ and taking $n\equiv-1 \pmod{p^{a_p}}$.
* **Large primes $\varepsilon k<p\le k$** (these carry the whole cost $\theta(k)\sim k$, and
  we cannot avoid them — see §5): put only the *first* power $p$ into $R$. That makes
  digit $0$ of $n$ equal to $p-1$ for free. Since $p^2>k$, the **only** remaining condition
  is on digit $1$, and it forbids just $\lfloor k/p\rfloor\le 1/\varepsilon$ residues out of $p$.

So take $n=sR-1$ and sieve on the single small integer $s$: the digit-1 conditions forbid
$\lfloor k/p\rfloor$ residues of $s$ modulo each large $p$, and a union bound shows a good
$s\le T=\lceil 8k/(\varepsilon\log k)\rceil$ exists, because
$\sum_{p>\varepsilon k}\lfloor k/p\rfloor/p = O(\varepsilon^{-2}/\log k)\to 0$.
Then $\log n\le\log T+\log R\le o(k)+O(\varepsilon k)+\theta(k)=(1+O(\varepsilon))k$.

The **reduction** achieved by the split is: everything except $\theta(k)\le(1+\varepsilon)k$
is elementary finite combinatorics/arithmetic, and the difficulty is concentrated in one
standalone classical analytic theorem (step **s6**, tagged `[CRUX]`).

*Attribution.* The construction is the standard one behind [EES74] and behind the
Kummer-criterion sieve used computationally by Sorenson–Sorenson–Webster, *An algorithm and
estimates for the Erdős–Selfridge function* (2020), who search residues mod
$M_k=\prod_{p\le k}p^{a_p}$ satisfying Kummer's criteria. I did **not** copy a proof: every
constant below was re-derived here and re-checked numerically in §4 against the Lean
definition.

## 3. Proof

Throughout, $p$ ranges over primes. For $p\ge2$ and $k\ge1$ put

$$a_p(k):=\texttt{Nat.log}\,p\,k+1,\qquad q_p(k):=p^{a_p(k)},$$

so that $q_p(k)$ is **the least power of $p$ exceeding $k$**
(`Nat.pow_log_le_self : p ^ Nat.log p k ≤ k` and
`Nat.lt_pow_succ_log_self : k < p ^ (Nat.log p k).succ`, both verified to exist).

Write $\mathrm{dig}_i^p(m):=\lfloor m/p^i\rfloor\bmod p = (m / p^i) \% p$ for the $i$-th base-$p$ digit.

---

1. **[s1] [LEMMA] `exists_tendsto_zero_of_forall_eps_le_exp`** : for `u : ℕ → ℕ`, if for every
   real `ε > 0` we have `∀ᶠ k in atTop, (u k : ℝ) ≤ Real.exp ((1+ε) * k)`, then there exists
   `f : ℕ → ℝ` with `Tendsto f atTop (𝓝 0)` and `∀ᶠ k in atTop, (u k : ℝ) ≤ Real.exp (k * (1 + f k))`.

   *This is the whole "$\limsup\le1\Rightarrow\exists f\to0$" bookkeeping, isolated from all
   number theory.* **Full proof.** Define
   $$f(k):=\max\Big(0,\ \frac{\log (u(k))}{k}-1\Big)\quad(k\ge1),\qquad f(0):=0 .$$
   (Lean's `Real.log 0 = 0`, `(0:ℕ) : ℝ = 0`; both branches are handled below.)

   *Inequality, for every $k\ge1$.*
   - If $u(k)=0$: then $f(k)=\max(0,-1)=0$ and $0\le e^{k}$. ✔
   - If $u(k)\ge1$ and $\log u(k)/k-1\le0$: then $f(k)=0$, $k(1+f(k))=k$, and
     $\log u(k)\le k$, so $u(k)=e^{\log u(k)}\le e^{k}$ by `Real.exp_log`/`Real.exp_le_exp`. ✔
   - If $u(k)\ge1$ and $\log u(k)/k-1>0$: then $f(k)=\log u(k)/k-1$, so
     $k(1+f(k))=k\cdot\frac{\log u(k)}{k}=\log u(k)$ (using $k\ne0$), hence
     $e^{k(1+f(k))}=e^{\log u(k)}=u(k)$. ✔

   *Convergence.* $f\ge0$ always. Let $\varepsilon>0$. By hypothesis there is $K$ with
   $u(k)\le e^{(1+\varepsilon)k}$ for $k\ge K$. For $k\ge\max(K,1)$: if $u(k)=0$ then
   $f(k)=0\le\varepsilon$; if $u(k)\ge1$ then `Real.log_le_iff_le_exp` gives
   $\log u(k)\le(1+\varepsilon)k$, so $\log u(k)/k-1\le\varepsilon$ and $f(k)\le\varepsilon$.
   Hence $0\le f(k)\le\varepsilon$ eventually, i.e. $f\to0$ (`Metric.tendsto_atTop`). ∎

   *Why massively easier:* no primes, no binomial coefficients, no construction — it is
   one explicit formula plus three case checks in `Real`.

2. **[s2] [LEMMA] `minFac_choose_gt_of_digits_le`** : for `n k : ℕ` with `1 ≤ k` and `k + 2 ≤ n`,
   if for every prime `p ≤ k` and every `i : ℕ` we have `(k / p^i) % p ≤ (n / p^i) % p`,
   then `k < (n.choose k).minFac`.

   *This is exactly the Lucas/Kummer criterion, isolated.* **Full proof.**
   First $\binom nk>1$: since $n\ge k+2$, `Nat.choose_le_choose` gives
   $\binom nk\ge\binom{k+2}{k}=\frac{(k+2)(k+1)}2\ge3>1$ for $k\ge1$. Hence
   `Nat.minFac_prime` applies: $q:=\mathrm{minFac}\binom nk$ is prime and $q\mid\binom nk$.

   Suppose for contradiction $q\le k$. Choose $a$ with $n<q^{a}$ (e.g. $a=n$, since
   $q\ge2\Rightarrow n<2^n\le q^n$); also $k<n<q^a$. Lucas' theorem
   (`Choose.choose_modEq_prod_range_choose_nat`, verified present, signature
   `n < p^a → k < p^a → n.choose k ≡ ∏ i ∈ Finset.range a, (n / p^i % p).choose (k / p^i % p) [MOD p]`)
   gives
   $$\binom nk\ \equiv\ \prod_{i<a}\binom{\,\mathrm{dig}_i^q(n)\,}{\,\mathrm{dig}_i^q(k)\,}\pmod q .$$
   By hypothesis $\mathrm{dig}_i^q(k)\le \mathrm{dig}_i^q(n)$ for each $i$, and both are $<q$.
   For $0\le b\le a'<q$ we have $q\nmid\binom{a'}{b}$: indeed $\binom{a'}{b}\cdot b!\,(a'-b)!=a'!$,
   so $\binom{a'}b\mid a'!$, while $q\nmid a'!$ because $a'!$ is a product of integers
   $1,\dots,a'$ all $<q$ and $q$ is prime. Hence every factor of the product is $\not\equiv0$,
   and since $q$ is prime the product is $\not\equiv0\pmod q$. Therefore $q\nmid\binom nk$ —
   contradicting $q\mid\binom nk$. So $q>k$. ∎

   *Why massively easier:* one Mathlib theorem plus a two-line divisibility argument;
   no asymptotics, no construction, no choice of $n$.

3. **[s3] [LEMMA] `digits_of_dvd_sub_one`** : for `p a M : ℕ` with `2 ≤ p`, `1 ≤ M` and `p^a ∣ M`:
   (i) `∀ i < a, ((M - 1) / p^i) % p = p - 1`, and (ii) `(M - 1) / p^a = M / p^a - 1`.

   *The digit computation for numbers of the form (multiple of a prime power) $-1$.*
   **Full proof.** Write $M=c\,p^{a}$ with $c\ge1$. Then
   $$M-1=(c-1)p^{a}+(p^{a}-1).$$
   (ii) Since $0\le p^a-1<p^a$, Euclidean division gives $(M-1)/p^{a}=c-1=M/p^a-1$. ✔
   (i) Let $i<a$. From $p^{a}-1=p^{i}\,(p^{a-i}-1)+(p^{i}-1)$ with $0\le p^i-1<p^i$ we get
   $(p^a-1)/p^i=p^{a-i}-1$, hence
   $$\frac{M-1}{p^{i}}=(c-1)p^{a-i}+\big(p^{a-i}-1\big).$$
   Because $a-i\ge1$, $p\mid (c-1)p^{a-i}$ and $p\mid p^{a-i}$, so modulo $p$ this is
   $\equiv -1\equiv p-1$; as the value $p-1$ lies in $[0,p)$, the residue **is** $p-1$. ✔ ∎

4. **[s4] [LEMMA] `exists_residue_avoiding`** : let `P : Finset ℕ` with `0 < p` for all `p ∈ P`,
   let `B : ℕ → Finset ℕ`, let `T : ℕ`. If
   `∑ p ∈ P, (B p).card * (T / p + 1) < T`, then there exists `s` with `1 ≤ s ≤ T` and
   `∀ p ∈ P, s % p ∉ B p`.

   *A pure union bound — the "small sieve" step.* **Full proof.** Work inside the finite set
   $I=\{1,2,\dots,T\}$, $|I|=T$. For fixed $p\in P$ and fixed $b$, the set
   $\{s\in I: s\equiv b\ (\mathrm{mod}\ p)\}$ has cardinality at most $\lfloor T/p\rfloor+1$
   (the elements are $b_0,b_0+p,b_0+2p,\dots$ inside an interval of length $T$; injecting
   $s\mapsto (s-b_0)/p$ into $\{0,1,\dots,\lfloor T/p\rfloor\}$ gives the bound, via
   `Finset.card_le_card_of_injOn`). Hence
   $$\Big|\{s\in I:\exists p\in P,\ s\bmod p\in B_p\}\Big|\ \le\ \sum_{p\in P}\sum_{b\in B_p}\big(\lfloor T/p\rfloor+1\big)=\sum_{p\in P}|B_p|\Big(\Big\lfloor\frac Tp\Big\rfloor+1\Big)\ <\ T=|I| .$$
   So the bad set is a proper subset of $I$ and some $s\in I$ is good. ∎

   *Why massively easier:* finite counting; no primality, no analysis, no binomials.

5. **[s5] [LEMMA] `small_prime_power_sum_le`** : for every real `ε` with `0 < ε < 1`,
   `∀ᶠ k : ℕ in atTop`,
   `∑ p ∈ (Finset.range (⌊ε*k⌋₊ + 1)).filter Nat.Prime, ((Nat.log p k + 1 : ℝ) * Real.log p) ≤ 6 * ε * k`.

   *The cheap half of $\log R$.* **Proof sketch (complete).** Put $y=\lfloor\varepsilon k\rfloor$.
   For each prime $p\le y$,
   $$\log q_p(k)=(\texttt{Nat.log}\,p\,k+1)\log p\le \log k+\log p,$$
   because $p^{\texttt{Nat.log}\,p\,k}\le k$ (`Nat.pow_log_le_self`). Summing,
   $$\sum_{p\le y}\log q_p(k)\ \le\ \pi(y)\log k+\theta(y).$$
   Now use only **Chebyshev-strength** Mathlib facts:
   `Chebyshev.eventually_primeCounting_le` with $\delta=0.6$ gives $\pi(y)\le 2y/\log y$ for
   $y$ large, and $\theta(y)\le\psi(y)\le \log4\cdot y+2\sqrt y\log y\le 1.5\,y$ for $y$ large
   (`Chebyshev.psi_le`, `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`). Also
   $\log k/\log y=\log k/\log(\varepsilon k)\to1$, so $\log k\le 2\log y$ for $k$ large
   (given $\varepsilon$). Hence eventually
   $$\sum_{p\le y}\log q_p(k)\ \le\ \frac{2y}{\log y}\cdot 2\log y+1.5\,y\ =\ 5.5\,y\ \le\ 6\varepsilon k .$$
   ∎ *Why massively easier:* it uses only bounds Mathlib already has, and the constant 6 is
   deliberately loose so no sharpness is needed anywhere.

6. **[s6] [LEMMA] [CRUX] `theta_le_one_add_eps`** : for every real `ε > 0`,
   `∀ᶠ x : ℝ in atTop, Chebyshev.theta x ≤ (1 + ε) * x`.
   (Equivalently, by `Chebyshev.theta_eq_log_primorial`, `Real.log (primorial n) ≤ (1+ε) * n`
   eventually, i.e. $\prod_{p\le n}p\le e^{(1+\varepsilon)n}$.)

   *This is the upper half of the **Prime Number Theorem**, and §5 proves it is genuinely
   necessary for the target: the best constant Mathlib currently provides is $\log4=1.386\ldots$,
   and the construction in **s7** produces $n$ divisible by $\prod_{\varepsilon k<p\le k}p$,
   so no route of this shape can output an exponent below $\limsup\theta(k)/k$.*

   **Proof route (known, and previously formalized).** $\theta(x)\sim x$ is classical.
   Standard route with the pieces Mathlib already has:
   1. `riemannZeta` and the non-vanishing `riemannZeta_ne_zero_of_one_le_re : 1 ≤ s.re → riemannZeta s ≠ 0`
      are **already in Mathlib** (probe-verified). This is the hard arithmetic input.
   2. The Dirichlet series $-\zeta'/\zeta(s)=\sum\Lambda(n)n^{-s}$ (`ArithmeticFunction.vonMangoldt`,
      `LSeries` are in Mathlib) is analytic on $\Re s\ge1$ except the simple pole at $s=1$
      with residue $1$.
   3. A Tauberian step — Newman's contour-integral theorem (D. J. Newman, *Simple analytic
      proof of the prime number theorem*, Amer. Math. Monthly 87 (1980) 693–696) or
      Wiener–Ikehara — yields $\psi(x)\sim x$. **Mathlib does not have a Tauberian theorem**
      (searched; nothing found), so this must be built; it is the bulk of the work.
   4. Transfer $\psi\to\theta$ by `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`
      (`1 ≤ x → |ψ x − θ x| ≤ 2√x log x`) together with
      `Chebyshev.theta_le_psi : ∀ x, θ x ≤ ψ x`; both are probe-verified in Mathlib.

   A complete Lean 4 proof of exactly this statement exists in the public
   **`PrimeNumberTheoremAnd`** project (Tao et al., https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
   so this is a porting/rebuilding task, not an unknown one. Only the **upper** bound
   $\limsup\theta(x)/x\le1$ is needed, which is all that step 3 has to deliver.

   *Why this is strictly smaller than the parent:* it mentions only primes and $\theta$; it
   contains no binomial coefficients, no `minFac`, no `g`, and no construction. The parent
   is this lemma **plus** the five other lemmas **plus** the assembly.

7. **[s7] [ELEM] The construction and the assembly: for every `ε ∈ (0, 1/2)`, eventually `g k ≤ exp((1+8ε)k)`.**

   This step is written out in full; it uses s2–s6 and nothing else.

   **Setup.** Fix $\varepsilon\in(0,\tfrac12)$. Let $k$ be large enough that all of the
   following hold (each is an "eventually in $k$" condition for this fixed $\varepsilon$):

   * (H1) $k\ge \varepsilon^{-2}$  and $k\ge10$  and $\varepsilon k\ge2$;
   * (H2) $\log k\ge 8/\varepsilon^{2}$;
   * (H3) $\pi(k)\le 2k/\log k$  [from `Chebyshev.eventually_primeCounting_le` with $\delta=0.6$, since $\log4+0.6<2$];
   * (H4) $\sum_{p\le\varepsilon k}\log q_p(k)\le 6\varepsilon k$  [**s5**];
   * (H5) $\theta(k)\le(1+\varepsilon)k$  [**s6**];
   * (H6) $\log\big(\lceil 8k/(\varepsilon\log k)\rceil\big)\le\varepsilon k$.

   Define
   $$S:=\{p\ \text{prime}: p\le \varepsilon k\},\qquad L:=\{p\ \text{prime}: \varepsilon k<p\le k\},$$
   $$\boxed{\;R:=\prod_{p\in S}q_p(k)\ \cdot\prod_{p\in L}p\;}\qquad
     \boxed{\;T:=\Big\lceil \frac{8k}{\varepsilon\log k}\Big\rceil\;}$$
   and for $p\in L$
   $$d_p:=\Big\lfloor \frac kp\Big\rfloor,\qquad u_p:=\Big(\frac Rp\Big)\bmod p,\qquad
     B_p:=\Big\{b\in[0,p): (b\,u_p)\bmod p\in\{1,2,\dots,d_p\}\Big\}.$$

   **(a) Basic size facts.** For $p\in L$: $p>\varepsilon k\ge\varepsilon\cdot\varepsilon^{-2}=1/\varepsilon$
   by (H1), and $p^2>\varepsilon^2k^2\ge \varepsilon^2k\cdot\varepsilon^{-2}=k$, so
   $$p^2>k,\qquad d_p\le k/p<k/(\varepsilon k)=1/\varepsilon<p,\qquad 1\le d_p .$$
   Also $p\nmid R/p$: the factors of $R/p$ are $q_{p'}(k)$ for $p'\in S$ (powers of primes
   $p'\ne p$, since $p\notin S$) and $p'$ for $p'\in L\setminus\{p\}$; all are coprime to $p$.
   Hence $u_p\ne0$ and $b\mapsto (b\,u_p)\bmod p$ is a bijection of $[0,p)$, so
   $$|B_p|=\big|\{1,\dots,d_p\}\big|=d_p\qquad(\text{using } d_p<p).$$

   **(b) The sieve applies.** Put $A:=\sum_{p\in L}d_p/p$ and $B:=\sum_{p\in L}d_p$. Using
   $d_p<1/\varepsilon$, $p>\varepsilon k$, $|L|\le\pi(k)\le 2k/\log k$ (H3):
   $$A\ \le\ \frac1\varepsilon\sum_{p\in L}\frac1p\ \le\ \frac1\varepsilon\cdot\frac{|L|}{\varepsilon k}\ \le\ \frac{1}{\varepsilon^{2}}\cdot\frac{2k/\log k}{k}=\frac{2}{\varepsilon^{2}\log k}\ \overset{\text{(H2)}}{\le}\ \frac14,$$
   $$B\ \le\ \frac{|L|}{\varepsilon}\ \le\ \frac{2k}{\varepsilon\log k}\ =\ \frac14\cdot\frac{8k}{\varepsilon\log k}\ \le\ \frac T4 .$$
   Therefore
   $$\sum_{p\in L}|B_p|\Big(\Big\lfloor\frac Tp\Big\rfloor+1\Big)\ \le\ \sum_{p\in L}d_p\Big(\frac Tp+1\Big)=T\!\cdot\!A+B\ \le\ \frac T4+\frac T4=\frac T2\ <\ T .$$
   By **s4** there exists $s$ with $1\le s\le T$ and $s\bmod p\notin B_p$ for every $p\in L$.

   **(c) The witness.** Set
   $$\boxed{\,n:=sR-1\,}.$$
   Since $2\in S$ (by $\varepsilon k\ge2$) and $3\in S$ (as $\varepsilon k\ge2$ may not give $3\le\varepsilon k$; if not, $3\in L$ and $3\mid R$ anyway), we have $R\ge q_2(k)>k$, and in fact $R>k^{2}>k+2$ for $k\ge10$ because $R$ contains $q_2(k)>k$ and at least one further prime factor $\ge3$. Hence
   $$n=sR-1\ \ge\ R-1\ >\ k+1 .$$

   **(d) Digit domination for every prime $p\le k$.** Let $M:=sR\ge1$.

   *Case $p\in S$.* Let $a:=a_p(k)$, so $q_p(k)=p^{a}>k$ and $p^{a}\mid R\mid M$.
   By **s3**(i), $\mathrm{dig}_i^p(n)=p-1$ for all $i<a$, which dominates any digit of $k$.
   For $i\ge a$: $p^{i}\ge p^{a}>k$, so $\lfloor k/p^{i}\rfloor=0$ and $\mathrm{dig}_i^p(k)=0\le\mathrm{dig}_i^p(n)$. ✔

   *Case $p\in L$.* Here $p\mid R\mid M$.
   - $i=0$: by **s3**(i) with $a=1$, $\mathrm{dig}_0^p(n)=p-1\ge\mathrm{dig}_0^p(k)$. ✔
   - $i=1$: by **s3**(ii) with $a=1$, $n/p=(M-1)/p=M/p-1=s\,(R/p)-1$. Hence
     $$\mathrm{dig}_1^p(n)=\big(s\,(R/p)-1\big)\bmod p .$$
     Write $x:=\big(s\,(R/p)\big)\bmod p=\big((s\bmod p)\,u_p\big)\bmod p$. Then
     $\big(s(R/p)-1\big)\bmod p=(x+p-1)\bmod p$, which equals $p-1$ if $x=0$ and $x-1$ if $1\le x\le p-1$.
     Since $s\bmod p\notin B_p$ we have $x\notin\{1,\dots,d_p\}$, so either $x=0$ (giving digit $p-1\ge d_p$,
     as $d_p<p$) or $x>d_p$ (giving digit $x-1\ge d_p$). Either way
     $\mathrm{dig}_1^p(n)\ge d_p=\lfloor k/p\rfloor=\mathrm{dig}_1^p(k)$ — the last equality because
     $\lfloor k/p\rfloor=d_p<p$ so reducing mod $p$ changes nothing. ✔
   - $i\ge2$: $p^{i}\ge p^{2}>k$ by (a), so $\mathrm{dig}_i^p(k)=0$. ✔

   **(e) Conclusion of the construction.** $k\ge1$, $n\ge k+2$, and every prime $p\le k$ has
   all its base-$p$ digits of $k$ dominated by those of $n$. By **s2**,
   $k<\mathrm{minFac}\big(\binom nk\big)$. Together with $n>k+1$ this places $n$ in the set
   $\{m: k+1<m\wedge k<(\binom mk).\mathrm{minFac}\}$, so by `Nat.sInf_le`,
   $$g(k)\ \le\ n\ =\ sR-1\ \le\ sR\ \le\ TR .$$

   **(f) Size estimate.**
   $$\log R=\sum_{p\in S}\log q_p(k)+\sum_{p\in L}\log p\ \le\ \underbrace{6\varepsilon k}_{\text{(H4)}}+\ \theta(k)\ \overset{\text{(H5)}}{\le}\ 6\varepsilon k+(1+\varepsilon)k .$$
   Hence, using (H6),
   $$\log g(k)\ \le\ \log T+\log R\ \le\ \varepsilon k+6\varepsilon k+(1+\varepsilon)k\ =\ (1+8\varepsilon)k,$$
   i.e. $g(k)\le\exp\big((1+8\varepsilon)k\big)$ for all large $k$. ∎

8. **[s8] [ELEM] Finish.** Let $\delta>0$. Apply **s7** with $\varepsilon:=\min(\delta/8,\ 1/4)$:
   eventually $g(k)\le\exp((1+8\varepsilon)k)\le\exp((1+\delta)k)$. So the hypothesis of **s1**
   holds for $u:=g$, and **s1** delivers `f : ℕ → ℝ` with `Tendsto f atTop (𝓝 0)` and
   `∀ᶠ k in atTop, (g k : ℝ) ≤ exp (k * (1 + f k))`, which is the target. ∎

---

### Mathlib facts used, all probe-verified present (`scratch/probe*.lean`)

| name | signature (as returned by `#check`) |
|---|---|
| `Choose.choose_modEq_prod_range_choose_nat` | `n < p^a → k < p^a → n.choose k ≡ ∏ i ∈ range a, (n/p^i % p).choose (k/p^i % p) [MOD p]` |
| `Nat.minFac_prime` | `n ≠ 1 → Nat.Prime n.minFac` |
| `Nat.minFac_dvd` | `n.minFac ∣ n` |
| `Nat.choose_le_choose` | `a ≤ b → a.choose c ≤ b.choose c` |
| `Nat.pow_log_le_self` | `x ≠ 0 → b ^ Nat.log b x ≤ x` |
| `Nat.lt_pow_succ_log_self` | `1 < b → x < b ^ (Nat.log b x).succ` |
| `Chebyshev.theta` / `Chebyshev.theta_eq_log_primorial` | `theta x = Real.log (primorial ⌊x⌋₊)` |
| `Chebyshev.psi_le` | `1 ≤ x → ψ x ≤ log 4 * x + 2√x log x` |
| `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log` | `1 ≤ x → |ψ x − θ x| ≤ 2√x log x` |
| `Chebyshev.eventually_primeCounting_le` | `0 < ε → ∀ᶠ x in atTop, π ⌊x⌋₊ ≤ (log 4 + ε) * x / log x` |
| `Real.log_le_iff_le_exp`, `Real.exp_log`, `Real.log_le_log` | as printed |
| `Finset.card_le_card_of_injOn` | `MapsTo f s t → InjOn f s → s.card ≤ t.card` |
| `riemannZeta_ne_zero_of_one_le_re` | `1 ≤ s.re → riemannZeta s ≠ 0`  (available for **s6**) |

**Verified absent** (so they must not be cited): `PrimeNumberTheorem`, `WienerIkehara`,
`Chebyshev.theta_isEquivalent_id`, `Chebyshev.psi_isEquivalent_id`,
`Nat.primeCounting_isEquivalent`, `Nat.primeCounting_asymptotic`, any Tauberian theorem.

## 4. Supporting Evidence & Positive Test Cases

All computations in `scratch/validate.py` and `scratch/asymptotics.py`.

### 4.1 The Lean definition of `g` is the Erdős–Selfridge function (A003458)

Brute force over the *Lean* definition `sInf {m | k+1 < m ∧ k < minFac (C(m,k))}`:

| $k$ | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| computed $g(k)$ | 3 | 6 | 7 | 7 | 23 | 62 | 143 | 44 | 159 | 46 | 47 | 174 | 2239 |
| A003458 | 3 | 6 | 7 | 7 | 23 | 62 | 143 | 44 | 159 | 46 | 47 | 174 | 2239 |

Exact match — no indexing/convention mismatch, and the defining set is non-empty.
(Spot check by hand: $k=3$, $\binom73=35=5\cdot7$, both factors $>3$, and $\binom53=10$,
$\binom63=20$ are even, so $g(3)=7$. ✔)

### 4.2 The construction of **s7** works and is verified end-to-end

For each $(k,\varepsilon)$ the script builds $R$ exactly as in **s7**, finds the least
$s\ge1$ such that $n=sR-1$ satisfies the digit condition for the **large** primes, and then
*independently re-verifies the digit condition for **all** primes $\le k$* (column `ok`).

| $k$ | $\varepsilon$ | $s$ | $\log R/k$ | $\log n/k$ | all primes $\le k$ verified |
|---|---|---|---|---|---|
| 20 | 0.5 | 1 | 1.2306 | 1.2306 | **True** |
| 20 | 0.1 | 40 | 0.9430 | 1.1275 | **True** |
| 50 | 0.25 | 1 | 1.1446 | 1.1446 | **True** |
| 50 | 0.1 | 3 | 1.0188 | 1.0408 | **True** |
| 120 | 0.1 | 29 | 1.0428 | 1.0708 | **True** |
| 400 | 0.1 | 9 | 1.0687 | 1.0742 | **True** |
| 1000 | 0.1 | 3 | — | 1.0815 | **True** |
| 3000 | 0.1 | 1 | 1.0927 | 1.0927 | **True** |

So the Kummer/Lucas reasoning of **s2**+**s3** and the shape $n=sR-1$ are correct: in every
instance the constructed $n$ really does make all prime factors of $\binom nk$ exceed $k$.

### 4.3 $\log n/k\to1$ as $\varepsilon\to0$, $k\to\infty$ — exactly as **s7**(f) predicts

Here $\theta(k)/k$ is listed to show that the bound is $\theta(k)/k+O(\varepsilon)$, i.e. the
PNT term is the dominant one and *everything else is $O(\varepsilon)$*:

| $k$ | $\varepsilon$ | $\theta(k)/k$ | small-prime part $/k$ | $s$ | $\log n/k$ | verified |
|---|---|---|---|---|---|---|
| 1000 | 0.10 | 0.95625 | 0.20789 | 3 | 1.08151 | True |
| 1000 | 0.05 | 0.95625 | 0.12236 | 23 | 1.04078 | True |
| 1000 | 0.04 | 0.95625 | 0.09971 | 890 | 1.03311 | True |
| 10000 | 0.10 | 0.98960 | 0.20299 | 3 | 1.09707 | True |
| 10000 | 0.03 | 0.98960 | 0.06715 | 107 | 1.02951 | True |
| 100000 | 0.10 | 0.99685 | 0.20158 | 3 | 1.09949 | True |
| 100000 | 0.03 | 0.99685 | 0.06231 | 24 | 1.02987 | True |
| 100000 | 0.01 | 0.99685 | 0.02279 | 83101 | 1.01019 | True |

Consistency check of the arithmetic of **s7**(f) on the row $k=10^5,\varepsilon=0.03$:
$\theta(k)/k=0.99685$, $\theta(\varepsilon k)/k=\theta(3000)/10^5\approx0.0288$, small part
$0.06231$; predicted $\log R/k\approx 0.99685-0.0288+0.06231=1.0304$, and the measured
$\log n/k=1.02987$ (the difference is $\log s/k\approx3\cdot10^{-5}$, negligible). ✔
The small-prime part is empirically $\approx 2\varepsilon$, comfortably inside the bound
$6\varepsilon$ claimed in **s5**.

### 4.4 The sieve bound of **s7**(b) is conservative (never optimistic)

With $T=\lceil 8k/(\varepsilon\log k)\rceil$:

| $k$ | $\varepsilon$ | $T$ | actual #bad $s$ in $[1,T]$ | proven bound $TA+B$ | $A$ | $B$ |
|---|---|---|---|---|---|---|
| 1000 | 0.1 | 11582 | 9081 | 17742.7 | 1.503 | 335 |
| 1000 | 0.05 | 23163 | 22631 | 81159.1 | 3.483 | 471 |

At these tiny $k$, hypothesis (H2) ($\log k\ge8/\varepsilon^2$, i.e. $k\ge e^{800}$) is
violated by an astronomical margin, so $A>1/4$ and the *proven* bound is vacuous — yet the
actual bad count is still $<T$ and a good $s$ exists. This confirms (i) the bound is an
upper bound (actual $\le$ bound in both rows), and (ii) the construction is far more robust
than the proof needs. No contradiction with **s7**, whose hypotheses are "eventually in $k$
for fixed $\varepsilon$".

### 4.5 Hand-check of the digit algebra of **s7**(d) at $k=20$, $\varepsilon=0.5$, $p=17$

$S=\{2,3,5,7\}$ (primes $\le10$), $L=\{11,13,17,19\}$. $q_2=32,q_3=27,q_5=25,q_7=49$;
$R=32\cdot27\cdot25\cdot49\cdot11\cdot13\cdot17\cdot19=1058400\cdot46189\cdot\ldots$; $s=1$,
$n=R-1$. For $p=17$: $k=20=1\cdot17+3$, so $d_{17}=1$, $\mathrm{dig}_0^{17}(20)=3$,
$\mathrm{dig}_1^{17}(20)=1$. And $17\mid R$, so $\mathrm{dig}_0^{17}(n)=16\ge3$ ✔, and
$n/17=R/17-1$, whose residue mod 17 must be $\ge1$ — the script confirms the whole digit
condition holds for $p=17$ and for every other prime $\le20$. ✔

## 5. Adversarial Refutation & Falsification Attempts

**F1. Is the defining set ever empty, making `g k = 0` (Lean's `sInf ∅`) and the statement
vacuous?** Checked: no, and the plan never relies on it. §4.1 shows non-emptiness for
$k\le13$, and **s7** constructs an explicit member for every large $k$. (Had the set been
empty the target would be *trivially* true; it is not, so the work is real.)

**F2. Does the target maybe fail because $g$ is much bigger than $e^{k}$?** No — §4.2/4.3
exhibit explicit $n$ with $\log n/k\to1^{+}$ and full verification, so
$\limsup\log g(k)/k\le1$ is *witnessed numerically*. Independently, the heuristic count of
valid residues gives $\log g(k)=\Theta(k/\log k)$ (Sorenson–Sorenson–Webster's $\hat g$),
far below $e^k$; so the target has a wide safety margin.

**F3. Boundary $k=0,1,2$.** The goal is `∀ᶠ k in atTop`, so small $k$ are irrelevant; and
**s1**'s constructed `f` makes the inequality true for *every* $k\ge1$ anyway. $k=0$:
`g 0 = 2` (the set is all $m\ge2$ since `minFac (m.choose 0) = minFac 1 = 1 > 0`), and
`f 0 := 0` with `exp 0 = 1 < 2` would fail — **this is why `f 0` is irrelevant and the
conclusion is stated `∀ᶠ`, and why s1's inequality is claimed only for $k\ge1$.** Recorded
as a live constraint on s1: *do not claim the inequality at $k=0$.*

**F4. Degenerate $\varepsilon$: what if $\varepsilon k<2$, so $S=\emptyset$?** Then $R$ has no
small-prime part and $q_2$ is missing, breaking the $R>k+2$ argument. Excluded by (H1)
($\varepsilon k\ge2$), which holds eventually for fixed $\varepsilon$.

**F5. What if $\varepsilon k<\sqrt k$, so some $p\in L$ has $p^2\le k$ and needs a third
digit?** Then the sieve of **s7**(b) is *wrong*, because digit 2 would also be constrained.
**I tested this experimentally and it really does break**: at $k=1000,\varepsilon=0.01$
($\varepsilon k=10<\sqrt{1000}\approx31.6$) and at $k=10^4,\varepsilon=0.012$ and
$k=10^5,\varepsilon=0.004$, **no** admissible $s\le5\cdot10^5$ exists. This is a genuine
falsification of the *unguarded* argument and is exactly why (H1) carries the hypothesis
$k\ge\varepsilon^{-2}$. Guarded, the argument is fine (rows with $k\ge\varepsilon^{-2}$ all
succeed). **This hypothesis must appear in the formalization; dropping it makes s7 false.**

**F6. Can $p\mid s$ break digit 1?** If $p\mid s$ then $x=0$ and $\mathrm{dig}_1^p(n)=p-1$,
which is the *best* possible; and $0\notin B_p$ since $0\cdot u_p=0\notin\{1,\dots,d_p\}$.
Consistent, no gap.

**F7. Can $u_p=0$ (i.e. $p\mid R/p$), destroying $|B_p|=d_p$?** Only if $p^2\mid R$. By
construction $R$ contains $p$ to the first power only for $p\in L$ and $S\cap L=\emptyset$;
also $q_{p'}$ for $p'\in S$ is a power of $p'\ne p$. So $p\,\|\,R$ and $u_p\ne0$. ✔

**F8. Is $d_p<p$ really guaranteed (needed for $|B_p|=d_p$ and for
$\mathrm{dig}_1^p(k)=d_p$)?** $d_p\le k/p<1/\varepsilon$ and $p>\varepsilon k\ge1/\varepsilon$
under (H1). If (H1) failed, $d_p$ could exceed $p$ and $\mathrm{dig}_1^p(k)=d_p\bmod p\ne d_p$.
Guarded. ✔

**F9. Could the whole route be replaced by one avoiding PNT (so that s6 is unnecessary)?**
I tried three escapes and all fail:
  * *(a) Sieve the large primes' digit-0 condition too, instead of putting them in $R$.*
    The forbidden fraction is $(k\bmod p)/p$, which averages $\approx\frac12$; summing over
    $\sim k/\log k$ primes gives $\sim k/(2\log k)\gg1$, so the union bound of **s4** is
    hopeless. Only the very top of the range can be sieved: keeping the primes with
    $(k\bmod p)/p\le\delta$ out of $R$ costs $\sum\le\delta\cdot(\delta k/\log k)$, which is
    $<\frac12$ only for $\delta\lesssim\sqrt{\log k/k}$, saving
    $O(\delta k)=O(\sqrt{k\log k})=o(k)$ from $\log R$. Useless.
  * *(b) Use only Chebyshev, $\theta(k)\le\log4\cdot k$.* Then the same argument outputs
    $g(k)\le e^{(1.386+O(\varepsilon))k}$, which does **not** imply the target (it gives
    $f\to0.386$, not $f\to0$). So $\log4$ is provably insufficient.
  * *(c) Pick residues other than $-1$ so the CRT representative is small.* The valid
    residue classes mod $R$ number $\approx R\,e^{-\Theta(k/\log k)}$, so a *small*
    representative exists heuristically, but exhibiting one requires equidistribution of the
    valid set at scale $\ll R$ — that is precisely the open part of Erdős problem 1095
    (getting $g(k)=e^{o(k)}$). Not available.
  Conclusion: **s6 (PNT upper half) is a necessary dependency of this route**, recorded
  honestly rather than hidden.

**F10. Does s1's `f` really tend to 0 and not merely stay bounded?** Re-checked: for each
$\varepsilon>0$ the hypothesis pins $0\le f(k)\le\varepsilon$ eventually. Since $f\ge0$ by
construction, $f\to0$. A sign error (taking `min` instead of `max`) would break the
inequality branch; noted in §7.

**F11. Does `s2` need `n ≥ k+2` or would `n ≥ k+1` do?** With $n=k+1$, $\binom{n}{k}=k+1$,
whose `minFac` can be $\le k$; more importantly $\binom nk=1$ when $n=k$, and then
`minFac 1 = 1`, so `k < 1` is false — the `≠ 1` hypothesis of `Nat.minFac_prime` genuinely
needs $n\ge k+2$ **and** $k\ge1$. Both are in the statement of s2.

## 6. Freshness & Anti-Recycling Audit

* §5 of `context.md` reports **0 proof attempts and 0 decomposition attempts**; §6 lists no
  retired subgoals; §9 reports *no live decomposition*; §10 reports *nothing proved
  elsewhere in scope*. There are no `findings.md` files anywhere in `nodes/` other than the
  (empty) one for this node, and no sibling or cousin nodes exist — this node is the root and
  the graph contains only it.
* Therefore **nothing is recycled**: s1–s6 are all freshly derived here, and no step cites
  any unproved node. Every Mathlib name cited in a `[CITE]`-style position was
  probe-verified in `scratch/probe.lean`, `probe2.lean`, `probe3.lean`.
* No step depends on an unproved sibling (there are none).

## 7. Open Risks

1. **s6 (PNT) is a very large formalization.** Mathlib has the hard arithmetic input
   (`riemannZeta_ne_zero_of_one_le_re`) but **no Tauberian theorem**, so the Newman/
   Wiener–Ikehara step must be built. This is the single biggest risk in the plan. It is
   *not* a miracle lemma: the proof is classical and a complete Lean 4 formalization exists
   publicly (`PrimeNumberTheoremAnd`). What would falsify my framing of s6 is a discovery
   that Mathlib *does* already have $\theta(x)\sim x$ under a name I did not probe — in that
   case s6 becomes a one-line `[CITE]`. I probed 10+ plausible names and a semantic search;
   all negative.
2. **s7 hypothesis (H2) is $\log k\ge8/\varepsilon^2$**, i.e. $k\ge e^{8/\varepsilon^2}$.
   This is harmless for an `atTop` statement but means no finite numerical check can ever
   exercise the proven regime (§4.4 documents this honestly). Risk: a formalizer might try
   to verify (H2) numerically and conclude the lemma is false. It is not; the quantifier
   order is $\forall\varepsilon\ \exists K\ \forall k\ge K$.
3. **s7(c), $R>k+2$**, is stated slightly loosely (I argue $R\ge q_2(k)>k$ times another
   factor). If $\varepsilon k<3$ the "another factor" claim needs care. Safe fix, already
   implied by (H1): take $k\ge10$ and $\varepsilon k\ge2$, then $2\in S$, $q_2(k)>k$, and
   $R\ge q_2(k)\cdot\prod_{p\in L}p\ge q_2(k)\cdot p_0$ for some prime $p_0>\varepsilon k\ge2$
   (such $p_0$ exists by Bertrand, `Nat.exists_prime_lt_and_le_two_mul`). Falsifier: if $L$
   were empty the bound degrades — but $L\ne\emptyset$ for $k\ge5$ by Bertrand.
4. **s5's constant 6** is loose but depends on $\log k/\log(\varepsilon k)\le2$, which holds
   only for $k$ large given $\varepsilon$. If a formalizer fixes $\varepsilon$ and $k$
   independently this fails. The statement is `∀ ε, ∀ᶠ k`, which is the right order.
5. **s1's sign convention.** `f k := max 0 (log (u k) / k - 1)`; using `min`, or forgetting
   the $u(k)=0$ branch (`Real.log 0 = 0`), breaks it. The three branches are written out in
   s1 precisely to prevent this.
6. **`Nat` subtraction** appears in `M - 1`, `p - 1`, `M/p^a - 1` (s3). All are guarded by
   $M\ge1$, $p\ge2$, $M/p^a=c\ge1$, so no truncation surprises — but this is the most likely
   place for a formalization to stall.
