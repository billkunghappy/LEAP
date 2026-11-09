# Blueprint: erdos_789.variants.cube_root_linearithmic
Revision: 3  (REFUTATION PLAN — the target is FALSE; KERNEL-REFUTED TWICE)

> Revision 3 note (informal dispatch #5, 2026-09-28T09:50Z): a second disprove run was also accepted
> (logs/verification/1790588905_214293_disproof.json, is_valid=true, 0 sorry, axioms = standard + target).
> Independently re-derived before reading prior files: h(n) ≥ sqrt((n−1)/(66 log(n−1))) for large n
> (details in findings.md, DISPATCH #5). The only consistent action remains `refute`.

> Revision 2 note (informal dispatch #3, 2026-09-28T09:40Z): the refutation below was formalized in the
> disprove phase and ACCEPTED by the verifier: logs/verification/1790588298_440996_disproof.json has
> is_valid=true, 0 sorry, axioms = {propext, Classical.choice, Quot.sound, the target}. Certificate:
> disproof_scaffold.lean / logs/1790588298_443988_disproof.log (810 lines), proving
> (n−1)^2 ≤ 921600·(h(n)+1)^5, i.e. h(n) ≫ n^{2/5}, which contradicts the IsBigO half of the target.
> No proof plan for the target can exist; the only consistent action is `refute` with this witness.

## 1. Statement

Target (Lean): `(fun n ↦ (subsetSumThreshold n : ℝ)) =Θ[atTop] fun n ↦ (n * Real.log n) ^ ((1:ℝ)/3)`,
where `subsetSumThreshold n = sSup {m | IsSubsetSumSeparatingCard n m}` and
`IsSubsetSumSeparatingCard n m` says: every `A : Finset ℤ` with `#A = n` has `B ⊆ A`, `m ≤ #B`, such that
for all nonempty `T, S ⊆ B`, `∑T = ∑S → #T = #S`.

Write h(n) := subsetSumThreshold n. The Θ claim contains the upper half h(n) = O((n log n)^{1/3}).
**This upper half is false**: h(n) ≥ c·n^{2/5} for all large n (in fact h(n) ≫ sqrt(n/log n)).

Calibration. The formal-conjectures file (FormalConjectures/ErdosProblems/789.lean) states this Θ as a
*candidate* answer (the best lower bound known classically, Choi 1974). The candidate is refuted by a
2026 proof claim of S. Korsky (erdosproblems.com/forum/thread/789/proof-claims, "A Near-Square-Root Bound
for an Additive Problem of Erdős and Straus", Sept 12 2026) giving h(n) ≫ sqrt(n loglog n / log n).
I re-derived (independently, below) a slightly weaker, simpler version h(n) ≫ sqrt(n / log n), and a
still cruder version h(n) ≥ ((n−1)/4)^{2/5} − 1 which suffices. Difficulty: a genuine research-level
but entirely elementary argument (linear algebra + Cramer's rule + a Chebyshev-type prime count); roughly
five to seven separable lemmas.

## 2. Strategy

Let P = A \ {0}. Call B "good" if every signed relation Σ ε_b b = 0 (ε ∈ {−1,0,1}^B) has Σ ε_b = 0;
good ⇒ the Lean property. Let D be a maximum-cardinality good subset of P, d = |D|, k = d+1.
(i) Every a ∈ P is a {−1,0,1}-combination η_a·𝐝 of D (maximality). (ii) Cramer's rule gives a small
integer vector x orthogonal to every relation-vector w = Σ ε_a η_a coming from relations of support ≤ k,
with b_a := η_a·x ≠ 0 for ≥ half of P, |b_a| ≤ k^{3k}; relations of support ≤ k among a's pass to the b_a.
(iii) For a prime p > k, k elements whose images are ≡ the same nonzero residue mod p would form a good
set of size k > d; so each nonzero residue class holds ≤ d elements. (iv) Each b_a has ≤ 3k prime
factors > k; double counting over ≥ 6k primes in (k, K] gives |A'| ≤ 2Kd, hence n − 1 ≤ 4Kd with
K ≤ k^{3/2}, i.e. d ≳ n^{2/5}, contradicting d ≤ h(n) = O((n log n)^{1/3}).
Source: adapted from S. Korsky (2026), Lemma 2 and §3 (the log p/p weighting there is replaced by a plain
count, losing only a loglog factor that is irrelevant here).

## 3. Proof (of ¬target)

Notation: for a finset B ⊆ ℤ, good(B) :⇔ ∀ ε : B → {−1,0,1}, Σ ε_b b = 0 → Σ ε_b = 0.

1. [s1] [ELEM] good_imp_lean : good(B) ⇒ ∀ T S ⊆ B nonempty, ∑T = ∑S → #T = #S.
   Put ε = 1_T − 1_S ∈ {−1,0,1}^B. Then Σ ε_b b = ∑T − ∑S = 0, so 0 = Σ ε_b = #T − #S.
   (The converse fails only when ∑B = 0, e.g. B = {−996,425,571}; the converse is NOT used.)

2. [s2] [ELEM] h_ge : IsSubsetSumSeparatingCard n m → m ≤ subsetSumThreshold n.
   The set {m | …} is bounded above by n: apply the property to A = image of range n under Nat.cast
   (card n) to get m ≤ #B ≤ #A = n. Then `le_csSup`.

3. [s3] [LEMMA] representation : Let P ⊆ ℤ finite, 0 ∉ P, D ⊆ P good of maximum cardinality among good
   subsets of P, D = {d_1,…,d_d}. Then ∀ a ∈ P ∃ η ∈ {−1,0,1}^d with a = Σ_i η_i d_i.
   Proof: a = d_i: unit vector. a ∉ D: D ∪ {a} is not good (it is larger than D), so some ε on D∪{a} has
   Σ ε x = 0, Σ ε ≠ 0. If ε_a = 0 the restriction to D contradicts good(D). So ε_a = ±1 and
   a = −ε_a Σ_{b∈D} ε_b b; take η = −ε_a·ε|_D.

4. [s4] [LEMMA] [CRUX] small_images : Same hypotheses, k = d+1, P ≠ ∅. There exist A' ⊆ P with 2|A'| ≥ |P|
   and b : ℤ → ℤ with, for a ∈ A': b_a ≠ 0, |b_a| ≤ k^{3k}; and for every ε : A' → {−1,0,1} with
   #supp ε ≤ k and Σ ε_a a = 0 we have Σ ε_a b_a = 0.
   Proof. Fix η_a from s3 (so η_a·𝐝 = a, 𝐝 = (d_1..d_d)). Let W = { Σ_{a∈P} ε_a η_a : ε ∈ {−1,0,1}^P,
   #supp ε ≤ k, Σ ε_a a = 0 } ⊆ ℤ^d. Each w ∈ W has |w_i| ≤ k and w·𝐝 = 0. Let C be the matrix with rows W,
   r = rank C over ℚ; 𝐝 ≠ 0 lies in ker C, so r ≤ d−1. If r = 0 set z_j = e_j (j=1..d). Else choose r
   independent rows I and columns J with Δ = det C_{I,J} ≠ 0 (|Δ| ≤ r!k^r by Matrix.det_le), and for each
   j ∉ J define z_j by z_j[j] = Δ, z_j[j'] = 0 (j' ∉ J, j' ≠ j), z_j[J] = −cramer(C_{I,J}, C_{I,j}).
   Then C_{I} z_j = −Δ C_{I,j} + Δ C_{I,j} = 0 (Matrix.mulVec_cramer), the rows I span the row space so
   C z_j = 0; the q = d−r vectors z_j are independent (Δ-pattern on free coordinates), hence a ℚ-basis of
   ker C; entries |z_j[i]| ≤ r!k^r (cramer_apply = det of updateCol, Matrix.det_le).
   For a ∈ P some j has η_a·z_j ≠ 0: otherwise η_a ⟂ ker C ∋ 𝐝, giving a = η_a·𝐝 = 0.
   For ξ ∈ {0,1}^q let x(ξ) = Σ ξ_j z_j. Flipping ξ_j changes η_a·x by ±η_a·z_j ≠ 0, so η_a·x(ξ) = 0 for
   at most 2^{q−1} of the 2^q vectors ξ. Summing over a, some ξ has #{a : η_a·x(ξ) ≠ 0} ≥ |P|/2.
   Set A' = that set, b_a = η_a·x. Bound: ‖x‖∞ ≤ d·d!·k^d, |b_a| ≤ d‖x‖∞ ≤ d²d!k^d ≤ k^{2k+2} ≤ k^{3k}
   (k ≥ 2). Preservation: a relation ε on A' with support ≤ k extends by 0 to P, gives
   w = Σ ε_a η_a ∈ W, and x ∈ ker C, so Σ ε_a b_a = w·x = 0.
   (Simplification: this is a finite linear-algebra statement with no primes and no asymptotics.)

5. [s5] [LEMMA] residue_class_bound : In the setting of s4 (D maximum good in P, d = |D|, k = d+1, A', b as
   in s4), for every prime p > k and u with p ∤ u: #{a ∈ A' : b_a ≡ u (mod p)} ≤ d.
   Proof: otherwise pick E ⊆ that class, |E| = k. For ε on E with Σ ε a = 0: support ≤ k so
   Σ ε_a b_a = 0, hence u Σ ε_a ≡ 0 (mod p), p | Σ ε_a, |Σ ε_a| ≤ k < p, so Σ ε_a = 0. So E ⊆ P is good
   with |E| = d+1 > d: contradiction with maximality.
   Consequence: #{a ∈ A' : p ∤ b_a} ≤ (p−1)d.

6. [s6] [LEMMA] few_large_prime_factors : k ≥ 2, b ∈ ℤ, b ≠ 0, |b| ≤ k^{3k} ⇒
   #{p prime : k < p, p | b} ≤ 3k.  Proof: the product of t such primes divides b, so
   k^t < ∏ p ≤ |b| ≤ k^{3k}, t < 3k.

7. [s7] [LEMMA] many_primes : ∃ k0, ∀ k ≥ k0, #{p prime : k < p ≤ ⌊k^{3/2}⌋} ≥ 6k.
   Proof: π(k) ≤ k, so it suffices that π(K) ≥ 7k for K = ⌊k^{3/2}⌋. Chebyshev lower bound via the
   central binomial coefficient: 4^m ≤ (2m+1)·C(2m,m) (Nat.four_pow_le_two_mul_add_one_mul_central_binom)
   and C(2m,m) = ∏_{p ≤ 2m} p^{v_p} with p^{v_p} ≤ 2m (Nat.pow_factorization_choose_le), so
   C(2m,m) ≤ (2m)^{π(2m)} and π(2m) ≥ (m log 4 − log(2m+1))/log(2m). With 2m ≈ K this is
   ≥ 0.69 k^{3/2}/(1.5 log k) − 1 ≥ 7k once k^{1/2} ≥ 16 log k (e.g. all k ≥ 10^5).

8. [s8] [ELEM] counting : with P_K = primes in (k, K], N = |P_K| ≥ 6k:
   N·|A'| = Σ_{p∈P_K} (#{a: p | b_a} + #{a: p ∤ b_a}) ≤ Σ_{a∈A'} #{p ∈ P_K : p | b_a} + N(K−1)d
   ≤ 3k|A'| + NKd (s5, s6). Since N − 3k ≥ N/2: |A'| ≤ 2Kd. With 2|A'| ≥ |P| ≥ n − 1: n − 1 ≤ 4Kd.

9. [s9] [ELEM] lower_bound : for every A : Finset ℤ, #A = n, with d = d(A) the max good-subset size of
   P = A \ {0}: either d+1 < k0 (then n − 1 ≤ 4 d K*(d+1) ≤ const, where K*(k) = least K with ≥ 6k primes in
   (k,K], finite by Nat.exists_infinite_primes) or n − 1 ≤ 4 d (d+1)^{3/2} ≤ 4(d+1)^{5/2}.
   Hence for n ≥ N1: d ≥ ((n−1)/4)^{2/5} − 1, and by s1, s2: h(n) ≥ ((n−1)/4)^{2/5} − 1.

10. [s10] [ELEM] contradiction : the target's IsBigO half gives C, N0 with h(n) ≤ C (n log n)^{1/3} for
   n ≥ N0; but ((n−1)/4)^{2/5} − 1 > C (n log n)^{1/3} for large n since n^{2/5−1/3} = n^{1/15}
   dominates (log n)^{1/3}. False.

## 4. Supporting Evidence & Positive Test Cases

* scratch/evidence.py (300 random sets A ⊆ [−M,M], |A| ≤ 8, M ∈ {10,30,100,1000}):
  - good ⇒ Lean property: 25,367 subset checks, no failure. Lean-true/good-false occurs (191 cases) and
    ONLY when the whole subset sums to 0, e.g. (−996,425,571), (−10,10): hence s1 is stated one way only.
  - s3 representation: 1,660 checks, every a ∈ P is a {−1,0,1}-combination of a maximum good D.
  - s5 class lemma with the trivial images b_a = a (which preserve all relations): 65,428 (p,u) classes,
    every nonzero residue class mod a prime p > k has ≤ d elements.
* Exact small values, A = [1..n], max good subset size: n=1..12 → 1,2,2,3,3,4,4,4,5,5,5,6
  (e.g. {7,…,12} for n=12, the interval-window example, consistent with (2+o(1))√n on intervals).
* scratch/primes.py: Chebyshev bound π(2m) ≥ (m ln4 − ln(2m+1))/ln(2m) holds for m=5..10^6
  (e.g. m=10^4: π=2262 ≥ 1398.8). Minimal K with ≥ 6k primes in (k,K]: k=10^4 → 763,369 ≤ k^{1.5}=10^6;
  k=2·10^4 → 1,616,033 ≤ 2,828,427 (s7 holds from about k ≈ 10^4 on).

## 5. Adversarial Refutation & Falsification Attempts

* Zero element: 0 ∈ B kills goodness ({0} ∪ {b}: ε_0 = 1 gives Σε=1). Handled by P = A \ {0}; costs 1.
* Whole-set zero sum: good is strictly stronger than the Lean property; we only use good ⇒ Lean and take
  maxima over good sets, so the discrepancy is harmless.
* Negative elements: no positivity is used anywhere (only a ≠ 0 in s4's "some z_j" step).
* Duplicated images b_a = b_{a'} for a ≠ a': allowed; s5 counts elements a, and E ⊆ A' ⊆ P are distinct
  elements of A.
* r = 0 (no nontrivial short relations): z_j = e_j works, x ∈ {0,1}^d.
* k small (d+1 < k0): absorbed into the constant N1 in s9.
* Support restriction ≤ k in W is essential: using all relations gives |w_i| up to 3^d and
  log|b_a| ~ d², too many prime factors. s5 only needs relations on k-element sets, so ≤ k suffices.
* Could Korsky's claim be wrong? Irrelevant: the argument above was re-derived and checked line by line
  here; only the crude version (exponent 2/5) is needed.

## 6. Freshness & Anti-Recycling Audit
Root node, no prior attempts, no retired decompositions, no siblings. Nothing recycled; no citations of
unproved nodes.

## 7. Open Risks
* s4 formalization (choosing a nonsingular maximal minor / ℚ-basis of ker C with small integer entries) is
  the heaviest part. Alternative: Siegel's lemma does NOT suffice (need a spanning family, not one vector).
* s7 needs a Chebyshev lower bound not present in Mathlib (only upper bounds in Mathlib.NumberTheory.Chebyshev);
  it must be built from the central-binomial lemmas named above.
