# Blueprint: erdos_416.parts.i
Revision: 1

## 0. Read-me-first for every agent below this node

* A **complete, kernel-checked Lean proof of exactly this target already exists** (conjectures.io result
  `51923647-3c0d-418e-b330-aa595f5cad42`, certified 16 Sept 2026; axioms propext/Quot.sound/Classical.choice;
  statement hash matched the Formal-Conjectures statement, which is character-for-character our `problem.lean`).
  The full 64,775-line source is saved at
  `nodes/erdos_416.parts.i/scratch/Main.lean`.
  **Every step of this plan is a slice of that file; line numbers below refer to it.** Component index (line → component):
  `scratch/components.txt`. Heuristic dependency closures per child (over-approximate line ranges): `scratch/child_ranges.txt`.
* That file targets a **newer Mathlib** than ours ("Ported to Lean 4.33.1"). A `#check` sweep of all 1220 Mathlib
  names it uses (`scratch/probe_names.lean` → `scratch/probe_names_out.json`) found these genuinely missing here:
  `Nat.primesLE` + API (`mem_primesLE`, `primesLE_card_eq_primeCounting`, `prime_of_mem_primesLE`, `le_of_mem_primesLE`,
  `one_lt_of_mem_primesLE`, `primesLE_mono`), `Set.ofPred`/`Set.mem_ofPred_eq`/`Set.ofPred_and`/`Set.ofPred_forall`,
  `Function.HasFiniteSupport`, `Real.prod_one_add_le_exp_sum`, `MeasureTheory.integral_deriv_smul_comp_Ioi`,
  `MeasureTheory.integrableOn_indicator_iff`, `Finset.prod_eq_mul_prod_sdiff_singleton_of_mem`,
  `Finset.prod_le_prod_of_subset_of_one_le`, `Set.sdiff_subset` (ours: `Set.diff_subset`). Recommended shim:
  `def Nat.primesLE (n : ℕ) : Finset ℕ := (Finset.Iic n).filter Nat.Prime` with its 6 one-line lemmas.
  Everything else probed exists. Expect additional tactic-level drift (simp sets, `omega`, `positivity`).
* The file's own `Erdos416Proof.V` is `def V (x : ℝ) : ℝ := (totientsUpTo x).card`; it is `rfl`-equal to our
  `Erdos416.V` (file line 93, `V_eq_standard_count`, proved by `rfl`).
* Our Mathlib has **no PNT and no Mertens theorems** (only Chebyshev upper bounds, `Mathlib.NumberTheory.Chebyshev`).

## 1. Statement

Let `V(x) = #{ n ∈ [1, ⌊x⌋] : n = φ(m) for some m ∈ ℕ }` (as a real number). Prove `V(2x)/V(x) → 2` as real `x → ∞`.
The Lean statement is exactly this (`Finset.Icc 1 ⌊x⌋₊` filtered by `∃ m, m.totient = n`, cast to ℝ, `Filter.atTop` on ℝ).
No difference between the informal and formal statement.

Calibration: this is Erdős Problem #416(i), listed as open until 2026; Ford (1998) determined `V(x)` only up to
constant factors, which does not give the limit. It is a research-level theorem, far harder than any contest problem;
its known proof (the certified file) is ~65k Lean lines, containing a PNT port (~12k lines), a Mertens port (~2.3k),
a Selberg-sieve port (~2k), Ford's lower/upper-bound machinery for `V` (~30k), and a collision/rigidity theory (~13k).
It genuinely separates into **nine** claims: three classical analytic inputs (PNT, two Mertens theorems), an
elementary abstract endpoint, an elementary power-cutoff lemma, an elementary "values are totients" lemma, a
PNT-based imbalance lemma, a sieve-based collision bound and Ford's coverage theorem. The last two are hard; the
coverage theorem is the crux and will need further decomposition by its own planner.

## 2. Strategy

Build, for each accuracy ε, an explicit finite family `Q(y)` of pairs `(b,p)` (b a "numerical core" of a Ford-type
record, p a prime) with value map `(b,p) ↦ (p−1)b`, all values being totients in `(y^{0.99}, y]`. Then
`V(y) ≈ #Q(y)` (up to missing values ≤ εV + V(y^{0.99}) = εV + o(V), and repeated values = collision points = o(V)),
and, by the prime number theorem applied uniformly over the cores (all cores are `y^{o(1)}`), exactly half of the
pairs (asymptotically) have value ≤ y/2, so `V(y/2) ≈ #Q(y)/2`. An elementary finite counting inequality turns these
three error terms into `|V(2x) − 2V(x)| ≤ δ V(2x)`, hence the limit. The single idea: **replace the counting
function by a counted family of structured representations `φ(p·a) = (p−1)φ(a)`, where the large prime p carries
the whole x-dependence and PNT makes the family scale linearly.** Source: the certified conjectures.io proof
(URL `https://conjectures.io/results/51923647-3c0d-418e-b330-aa595f5cad42/solution`), built on K. Ford,
"The distribution of totients" (Ramanujan J. 2 (1998); arXiv:1104.3264).

## 3. Shared definitions (put these in the root scaffold; copied from Main.lean with the file's names)

```lean
open Filter Asymptotics
open scoped Topology BigOperators

-- (inside `namespace Erdos416`, after `V`)
noncomputable def totientsUpTo (x : ℝ) : Finset ℕ :=
  open scoped Classical in
  (Finset.Icc 1 ⌊x⌋₊).filter (fun n => ∃ m : ℕ, m.totient = n)
-- fact, by rfl:  V x = ((totientsUpTo x).card : ℝ)

open scoped Classical in
noncomputable def collisionPoints {α β : Type*} (s : Finset α) (f : α → β) : Finset α :=
  s.filter fun a => ∃ b ∈ s, b ≠ a ∧ f b = f a                       -- file l.335

def largestPrimeFactor (n : ℕ) : ℕ := max 1 (n.primeFactors.sup id)  -- file l.102
noncomputable def logLog (x : ℝ) : ℝ := Real.log (Real.log x)       -- file l.836
def corePairValue (bp : ℕ × ℕ) : ℕ := (bp.2 - 1) * bp.1              -- file l.730

open scoped Classical in
noncomputable def corePairs (cores : Finset ℕ) (lo hi : ℝ) : Finset (ℕ × ℕ) :=   -- file l.733
  (cores.product (Finset.range (⌊hi⌋₊ + 2))).filter fun bp =>
    bp.2.Prime ∧ lo < (corePairValue bp : ℝ) ∧ (corePairValue bp : ℝ) ≤ hi

noncomputable def fordWeight (idx : ℕ) : ℝ :=                        -- file l.2443
  ((idx : ℝ) + 1) * Real.log ((idx : ℝ) + 1) - idx * Real.log idx - 1

def weightedForm {L : ℕ} (a : Fin L → ℝ) : (Fin L → ℝ) →ₗ[ℝ] ℝ where  -- file l.522
  toFun x := ∑ idx, a idx * x idx
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' t x := by simp [Finset.mul_sum, mul_left_comm]

noncomputable def FordGeometry.outerForm (L : ℕ) : (Fin L → ℝ) →ₗ[ℝ] ℝ :=   -- file l.36009
  weightedForm (fun idx => fordWeight (idx.val + 1))

noncomputable def CollisionBox.cutoff (Y ν : ℝ) : ℝ := Real.exp ((Real.log Y) ^ ν)       -- l.33236
noncomputable def CollisionBox.primeCoordinate (T : ℝ) (p : ℕ) : ℝ := logLog p / T        -- l.33280

structure CoreRecords.LowerCoreRecord (Y : ℝ) (L R : ℕ) (P : ℝ) where                     -- l.62597
  length_pos : 0 < L
  tail : ℕ
  tail_pos : 0 < tail
  tail_le : tail ≤ R
  lower : Fin L → ℕ
  prime : ∀ idx, (lower idx).Prime
  order : StrictAnti lower
  last_lower : max 17 (largestPrimeFactor tail) < lower ⟨L-1, by omega⟩
  last_upper : (lower ⟨L-1, by omega⟩ : ℝ) ≤ P
  gaps : ∀ idx j : Fin L, j.val = idx.val+1 → (6/5 : ℝ)*logLog (lower j) ≤ logLog (lower idx)
  upper : ∀ idx, (lower idx : ℝ) ≤ CollisionBox.cutoff Y (4/5)
  facet : FordGeometry.outerForm L (fun idx => CollisionBox.primeCoordinate (logLog Y) (lower idx)) ≤
    1-(logLog Y)^(-1/8 : ℝ)

-- namespace CoreRecords.LowerCoreRecord, variable (Q : LowerCoreRecord Y L R P):   l.62618–62813
noncomputable def integer : ℕ := Q.tail * ∏ idx, Q.lower idx
noncomputable def numericalCore : ℕ := Q.tail.totient * ∏ idx, (Q.lower idx - 1)
theorem ext {Q₁ Q₂ : LowerCoreRecord Y L R P} (hr : Q₁.tail = Q₂.tail) (hq : Q₁.lower = Q₂.lower) : Q₁ = Q₂
noncomputable def boundedEncoding : Fin (R+1) × (Fin L → Fin (⌊CollisionBox.cutoff Y (4/5)⌋₊+1)) := …  -- l.62797
theorem boundedEncoding_injective : Function.Injective (boundedEncoding : LowerCoreRecord Y L R P → _)
noncomputable instance instFintype : Fintype (LowerCoreRecord Y L R P) :=
  Fintype.ofInjective boundedEncoding boundedEncoding_injective
-- (the file uses `letI := @instFintype` in every statement instead of an instance; either works)

structure CoreRecords.CoreSelection (Y : ℝ) (L R : ℕ) (P : ℝ) where                      -- l.62997
  cores : Finset ℕ
  record : ∀ _b : cores, LowerCoreRecord Y L R P
  core_eq : ∀ b : cores, (record b).numericalCore = b.val

noncomputable def CoreSelection.ofRecords (F : Finset (LowerCoreRecord Y L R P)) : CoreSelection Y L R P :=
  { cores := F.image LowerCoreRecord.numericalCore
    record := fun b => Classical.choose (Finset.mem_image.mp b.property)
    core_eq := fun b => (Classical.choose_spec (Finset.mem_image.mp b.property)).2 }     -- l.63009
noncomputable def CoreSelection.fullSelection (Y : ℝ) (L R : ℕ) (P : ℝ) : CoreSelection Y L R P :=
  CoreSelection.ofRecords Finset.univ                                                    -- l.63032
noncomputable def CoreRecords.powerRawPairs {Y P : ℝ} {L R : ℕ} (S : CoreSelection Y L R P) :
    Finset (ℕ × ℕ) := corePairs S.cores (Y ^ (99/100 : ℝ)) Y                             -- l.63377
```

Notation used below: `PNT := Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x)) atTop (𝓝 1)`;
`MERT := ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → |(∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p) - Real.log (Real.log x)| ≤ C`;
`EULER := IsEquivalent atTop (fun x : ℝ => ∏ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, (1 - (1 : ℝ) / p)) (fun x => Real.exp (-Real.eulerMascheroniConstant) / Real.log x)`.
**In every Lean statement below, write these three propositions out in full** (they are abbreviations here only).

## 4. Proof

1. [s1] [LEMMA] prime_counting_ratio : `Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x)) atTop (𝓝 1)`.

   The prime number theorem. Not in our Mathlib (probe: `Chebyshev.*` has only upper bounds and
   `primeCounting_sub_theta_div_log_isBigO`; no `psi ~ x`). Proof route: port Main.lean lines 2901–15206
   (sections `PNTSource_0…7`, adapted from the PNT+ project `AlexKontorovich/PrimeNumberTheoremAnd`, revision
   a5154676…, Apache-2.0; Wiener–Ikehara/Fourier route via `CS`, `trunc`, `W1`, `W21`, `nabla`), ending in
   `pi_alt'` (l.15139) and `prime_counting_asymptotic`/`prime_counting_ratio` (l.15195–15206). Independent of all
   totient content, so it is a separable classical claim. Evidence it is easier than the goal: it is one named
   classical theorem whose complete formal proof is in hand; no totient/Ford input. Alternative if the port fights
   the Mathlib version: `Chebyshev.primeCounting_sub_theta_div_log_isBigO` reduces it to `θ(x) ~ x`.

2. [s2] [LEMMA] prime_reciprocal_mertens : `∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → |(∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p) - Real.log (Real.log x)| ≤ C`.

   Mertens' second theorem (bounded error). Port Main.lean 15709–18020 (`MertensDependencyPort`, from PNT+:
   Euler–Maclaurin, `Mertens.sum_prime_div_eq_log_log`) and replace `Nat.primesLE n` by `(Finset.Iic n).filter Nat.Prime`
   (file l.18010 shows the bridge `primesLE_eq_Ioc_filter`). Classical route if porting fails: Chebyshev
   `∑_{p≤x} log p / p = log x + O(1)` (from `log n! = ∑_{p^k ≤ n} ⌊n/p^k⌋ log p` and `θ(x) ≤ log 4 · x`, both available)
   plus Abel summation. Needed only as a hypothesis of s8, s9 (used at file l.23410–31498, 50527, 52044).

3. [s3] [LEMMA] prime_euler_product_asymptotic : `IsEquivalent atTop (fun x : ℝ => ∏ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, (1 - (1 : ℝ) / p)) (fun x => Real.exp (-Real.eulerMascheroniConstant) / Real.log x)`.

   Mertens' third theorem. Port Main.lean 15709–18028 (`Mertens.E₃.bound''`, l.18024–18028). Needed only as a
   hypothesis of s8, s9 (used at l.18360, 28439). Separable classical claim.

4. [s4] [LEMMA] doubling_of_raw_counting_contracts :
   `(∀ ε : ℝ, 0 < ε → ε < 1/2 → ∃ (Q : ℝ → Finset (ℕ × ℕ)) (f : ℝ → ℕ × ℕ → ℕ) (r : ℝ → ℝ), (∀ᶠ y : ℝ in atTop, (∀ a ∈ Q y, f y a ∈ totientsUpTo y) ∧ V y - (((Q y).image (f y)).card : ℝ) ≤ ε * V y + r y) ∧ r =o[atTop] V ∧ (fun y => ((collisionPoints (Q y) (f y)).card : ℝ)) =o[atTop] V ∧ (fun y => ((Q y).card : ℝ) - 2 * (((Q y).filter (fun a => f y a ∈ totientsUpTo (y/2))).card : ℝ)) =o[atTop] (fun y => ((Q y).card : ℝ))) → Tendsto (fun x => V (2 * x) / V x) atTop (𝓝 2)`.

   Elementary (finite combinatorics + little-o bookkeeping); file l.45343–45424, 52168–52289, 64387–64479
   (there stated for a general type α; here α = ℕ × ℕ). Complete argument:
   (a) *Excess ≤ collisions*: `f` is injective on `P \ collisionPoints P f`, so `|P| ≤ |f(P)| + |collisionPoints P f|`.
   (b) *Finite counting error*: for finite `P`, `T₀ ⊆ T`, `f(P) ⊆ T`, with `I = f(P)`, `P₀ = {a ∈ P : f a ∈ T₀}`,
   `I₀ = f(P₀) = I ∩ T₀`: the identity
   `|T| − 2|T₀| = (|P| − 2|P₀|) + [(|T|−|I|) − 2(|T₀|−|I₀|)] − [(|P|−|I|) − 2(|P₀|−|I₀|)]`
   holds (expand), and `0 ≤ |T₀|−|I₀| ≤ |T|−|I|` (since `T₀ \ I₀ ⊆ T \ I`), `0 ≤ |P₀|−|I₀| ≤ |P|−|I|`
   (excess is monotone: `f(P) \ f(P₀) ⊆ f(P \ P₀)`). Since `0 ≤ b ≤ a ⇒ |a − 2b| ≤ a`, we get
   `||T| − 2|T₀|| ≤ ||P| − 2|P₀|| + (|T| − |I|) + (|P| − |I|)`.
   (c) Apply with `T = totientsUpTo (2x)`, `T₀ = totientsUpTo x`, `P = Q(2x)`, `f = f(2x)` (compose all eventual
   hypotheses with `x ↦ 2x`, which tends to `atTop`; note `2x/2 = x`): given δ>0 choose `ε = min(δ/4, 1/4)`,
   `η = min(δ/8, 1)`; eventually `missing ≤ εV(2x) + r(2x) ≤ (δ/4 + δ/8)V(2x)`, `excess ≤ ηV(2x)`,
   `|P| ≤ |I| + excess ≤ 2V(2x)`, `imbalance ≤ (δ/4)|P| ≤ (δ/2)V(2x)`; total `|V(2x) − 2V(x)| ≤ δ V(2x)`.
   (d) *Quotient lemma*: `v > 0, 0 ≤ δ ≤ 1/2, |w − 2v| ≤ δw ⇒ w ≤ 4v ⇒ |w/v − 2| = |w−2v|/v ≤ 4δ`.
   With `V x > 0` for `x ≥ 1` (`1 = φ(1) ∈ totientsUpTo x`) this gives the limit.

5. [s5] [LEMMA] V_lower_bound_and_power_cutoff : `PNT → (∀ᶠ x : ℝ in atTop, x / (2 * Real.log x) ≤ V x) ∧ (fun x : ℝ => V (x ^ (99/100 : ℝ))) =o[atTop] V`.

   Elementary given PNT; file l.15642–15672 and 53987–54028. (a) `π(⌊x⌋) ≤ V(x)` for `x ≥ 0`: `p ↦ p − 1`
   injects the primes ≤ ⌊x⌋ into `totientsUpTo x` (`p − 1 = φ(p) ≥ 1`, `p − 1 ≤ x`). (b) PNT gives eventually
   `π(⌊x⌋)/(x/log x) > 1/2`. (c) `V(z) ≤ z` for `z ≥ 0` (`totientsUpTo z ⊆ Icc 1 ⌊z⌋`), so `V(x^{0.99}) ≤ x^{0.99}`,
   and `x^{0.99} ≤ (ε/2)·x/log x` eventually because `log x = o(x^{0.01})` (`isLittleO_log_rpow_atTop`, verified),
   hence `≤ ε V(x)` by (a,b).

6. [s6] [LEMMA] record_cores_and_actual_values : `∀ (R : ℕ) (A : ℝ), ∀ᶠ Y : ℝ in atTop, ∀ (L : ℕ) (P : ℝ) (S : CoreRecords.CoreSelection Y L R P), (L : ℝ) ≤ A * Real.log (logLog Y) → (∀ b ∈ S.cores, 0 < b ∧ Real.log b ≤ Real.log R + A * Real.log (logLog Y) * (Real.log Y) ^ (4/5 : ℝ)) ∧ (∀ bp ∈ CoreRecords.powerRawPairs S, corePairValue bp ∈ totientsUpTo Y)`.

   Elementary; file l.62618–62790, 62917–62962, 63387–63473, 15410–15436. For `b ∈ S.cores` let `Q = S.record b`,
   so `b = Q.numericalCore`. (i) `Q.integer = tail·∏ lower ≤ R·cutoff(Y,4/5)^L`, so
   `log Q.integer ≤ log R + L (log Y)^{4/5} ≤ log R + A log(logLog Y)(log Y)^{4/5} =: G(Y)` (Y>1).
   (ii) The lower primes are distinct and all exceed `P⁺(tail)` (`order`, `last_lower`), so
   `φ(Q.integer) = φ(tail)∏(q_i − 1) = b` (`Nat.totient_mul`, coprimality), hence `1 ≤ b ≤ Q.integer` and
   `log b ≤ G(Y)`. (iii) `G(Y)/log Y → 0`, so eventually `G(Y) ≤ (9/100) log Y`, i.e. `Q.integer ≤ Y^{9/100}`,
   and `(log Y)^{4/5} < (9/10) log Y`, i.e. `cutoff(Y,4/5) < Y^{9/10}` (both uniform in L, P, S).
   (iv) For `(b,p) ∈ powerRawPairs S`: p prime, `Y^{0.99} < (p−1)b ≤ Y`. If `p ≤ Y^{9/10}` then
   `(p−1)b ≤ p·Q.integer ≤ Y^{9/10}·Y^{9/100} = Y^{99/100}`, contradiction; so `p > Y^{9/10} > cutoff ≥ lower_0 = P⁺(Q.integer)`.
   Hence `p ∤ Q.integer`, `φ(p·Q.integer) = (p−1)b = corePairValue (b,p)`, which is ≥ 1 and ≤ Y, so it lies in
   `totientsUpTo Y`.

7. [s7] [LEMMA] power_corePairs_imbalance : `PNT → ∀ (C : ℝ → Finset ℕ) (R A : ℝ), (∀ᶠ y : ℝ in atTop, ∀ b ∈ C y, 0 < b ∧ Real.log b ≤ Real.log R + A * Real.log (logLog y) * (Real.log y) ^ (4/5 : ℝ)) → (∀ᶠ y : ℝ in atTop, (C y).Nonempty) → (fun y => ((corePairs (C y) (y ^ (99/100 : ℝ)) y).card : ℝ) - 2 * ((corePairs (C y) (y ^ (99/100 : ℝ)) (y / 2)).card : ℝ)) =o[atTop] (fun y => ((corePairs (C y) (y ^ (99/100 : ℝ)) y).card : ℝ))`.

   PNT uniformly over small moduli; file l.15216–15616 and 63481–63560. For each `b`, the pairs with first
   coordinate b and value in `(lo, hi]` are exactly the primes `p` with `1 + lo/b < p ≤ 1 + hi/b`, so their number is
   `π(1 + hi/b) − π(1 + lo/b)` (floors inside; file `corePairs_card_prime_count`). Put `G(y) = log R + A log(logLog y)(log y)^{4/5}`;
   `G(y)/log y → 0` (file `logCoreBound_small`, l.15414). For `b ∈ C(y)` we have `b ≤ e^{G(y)} = y^{o(1)}`, so
   `t·y/b → ∞` and `log(t y/b)/log y → 1` uniformly in b; by PNT, `π(1 + t y/b) = (t + o(1))·y/(b log y)`
   uniformly, while `π(1 + y^{0.99}/b) ≤ 1 + y^{0.99}/b = o(y/(b log y))` uniformly. The uniformity is handled
   in the file by a filter on pairs `(y,b)` (`coreScaleFilter`, `prime_counting_core_interval_uniform`).
   Summing with weights `w_b = y/(b log y)` (weighted-average lemma `finite_weighted_ratio_bound`, l.15526):
   `#corePairs(C(y), y^{0.99}, t y) / ∑_b w_b → t` for t = 1 and t = 1/2 (nonemptiness makes ∑ w_b > 0), hence the
   ratio `#(…, y/2)/#(…, y) → 1/2` and the displayed difference is `o(#(…, y))`.

8. [s8] [LEMMA] powerRawPairs_collisions_bound : `PNT → MERT → EULER → ∀ (R : ℕ) (P A : ℝ), 0 < A → ∀ᶠ Y : ℝ in atTop, ∀ (L : ℕ) (S : CoreRecords.CoreSelection Y L R P), (L : ℝ) ≤ A * Real.log (logLog Y) → ((collisionPoints (CoreRecords.powerRawPairs S) corePairValue).card : ℝ) ≤ 4 * R * (Y / (Real.log Y * (logLog Y) ^ 2))`.

   Hard (sieve). Known proof = file l.18037–35980 (collision theory, `Rigidity`) + Selberg sieve port l.20077–22115
   + l.63629–63916 (bridge). Mechanism: (i) two distinct pairs with the same value have distinct primes
   (`corePair_eq_of_same_prime`, l.763). (ii) For a pair `(b,p)` let r = tail ∈ [1,R] and `n = p·∏ q_i` of its record;
   the record + `p > Y^{9/10}` give a `Rigidity.Tuple` (l.35528; `toTuple`, l.62714) and `φ(r)φ(n) = value`; a colliding
   partner supplies a preimage of the value with a *different* largest prime. The map pair ↦ (r, p·∏q_i) is
   injective (`actualInteger_injective`, l.63108), so `#collisions ≤ ∑_{r ≤ R} #(fixed-tail witnessed family)`
   (`collision_points_card_le_sum_tailProducts`, l.63840). (iii) Fixed-tail rigidity (`witnessed_family_count_eventually`,
   l.35907): each fixed-tail family has ≤ `4Y/(log Y (loglog Y)²)` members: delete non-normal squarefree integers,
   integers with a large prime square, and non-normal totients (each `≤ Y/(log Y (loglog Y)²)`, using a crude
   counting-envelope bound `A(x) ≤ exp(B (log₃ x)²)` for totient multiplicities, l.26245–27067); for the retained
   ones, equality of totients with different top primes `p ≠ p'` forces `a(p−1) = c(p'−1)` with small cofactors,
   and the three-form Selberg sieve for `q, aq+1, cq+1` (l.27070–28100) summed over normal cofactor structures
   (l.28101–33852) gives the extra `(loglog Y)^{-2}`. Uses MERT/EULER (l.23410–31498, 18360, 28439); PNT only via
   Chebyshev-type bounds. Evidence it is much easier than the goal: it is a pure upper bound on a sieve count with no
   reference to `V`, no coverage, no PNT asymptotics; ~13k of the 65k lines.

9. [s9] [LEMMA] [CRUX] exists_powerRawPairs_fullSelection_coverage : `PNT → MERT → EULER → ∀ ε : ℝ, 0 < ε → ∃ (L : ℝ → ℕ) (R : ℕ) (P : ℝ), (∀ᶠ y : ℝ in atTop, (L y : ℝ) ≤ 4 * Real.log (logLog y)) ∧ ∀ᶠ y : ℝ in atTop, V y - (((CoreRecords.powerRawPairs (CoreRecords.CoreSelection.fullSelection y (L y) R P)).image corePairValue).card : ℝ) ≤ ε * V y + V (y ^ (99/100 : ℝ))`.

   Ford's structure theorem for totients; this is where the difficulty lives. Known proof = file l.35992–62580
   plus 62583–63365, 63965–64370 (`exists_powerRawPairs_fullSelection_coverage`, l.64294, stated there with
   `L y = coreDimension M (logLog y)`; our ∃L form follows with `coreDimension_le_four_log`, l.41231).
   Mechanism: with `m ∈ totientsUpTo y`, `m > y^{0.99}`, choose any preimage N and list its prime factors
   `q₀ ≥ q₁ ≥ …` (`ordinaryPrimeAt N i`, l.54232). Define six exceptional value sets (l.63977):
   (E1) `firstFailedExceptionalValues`: m ≤ √y, "bad facet" values, values with a preimage having too many prime
   factors (`fiveLogOmegaTotients`), values with a large prime square in a preimage, bad outer facet at Ford's
   optimal dimension — all `o(V)` (l.59614);
   (E2) `polytopeFailureValues`: the normalized coordinates `x_i = loglog q_i / loglog y` of some preimage leave
   Ford's expanded polytope `S_L(ξ)` at dimension `coreDimension H` — `≤ εV` for H large (first-failed-row, l.59657);
   (E3) large terminal prime `q_L ≥ P_D` — `≤ εV` (l.60353); (E4) concentration region — `≤ (C log z/A)V` (l.62519);
   (E5) outer shell — `o(V)` (l.62551); (E6) large smooth residual `≥ R` — `≤ εV` (l.60517).
   Combined: `#E ≤ εV(y)` (`actual_core_coverage_exception_bound`, l.64079). Outside E, the preimage's
   ordered primes satisfy `OrdinaryLowerCoreConditions` (l.62819; eventually, l.63302), giving a
   `LowerCoreRecord` with `tail = ordinarySuffix N (L+1)`, `lower i = q_{i+1}`, and `m = corePairValue(core, q₀)`
   with `q₀ > y^{9/10}` prime and `q₁ < q₀` (l.64183–64345); so m is in the image. Values ≤ y^{0.99} cost exactly
   `V(y^{0.99})` (`powerRangeTotients_count_defect`, l.54053). Counting each exceptional class *relative to V*
   needs Ford's lower bound for V (namespace `FordLower`, l.43986–49700) and polytope/simplex volume
   asymptotics (`FordGeometry`, `SimplexVolume`, `FordAnalysis` with ρ the root of `F(ρ)=1`, `C = 1/(2|log ρ|)`,
   l.36578–43345). Suggested split for this node's planner: (a) Ford lower bound for V, (b) volume asymptotics of
   Ford polytopes, (c) the six exception counts, (d) the structural "outside E ⇒ in image" lemma.
   Evidence it is strictly smaller than the goal: PNT, both Mertens theorems, the doubling endpoint, collisions,
   imbalance and the totient-value check are all removed; what remains is a single one-sided counting estimate.

10. [s10] [ELEM] Assemble the target from s1–s9.

   Apply s4. Fix `ε ∈ (0,1/2)`. From s9 (fed with s1, s2, s3) get `L, R, P` with `hL : ∀ᶠ y, (L y:ℝ) ≤ 4 log(logLog y)`
   and the coverage bound. Put `S y := fullSelection y (L y) R P`, `Q y := powerRawPairs (S y)`,
   `f := fun _ => corePairValue`, `r y := V (y^{99/100})`. Obtain from s6 with `(R, A := 4)` the eventual facts
   `hcore : ∀ b ∈ (S y).cores, 0 < b ∧ log b ≤ log R + 4 log(logLog y)(log y)^{4/5}` and
   `hact : ∀ bp ∈ Q y, corePairValue bp ∈ totientsUpTo y` (combine with `hL` by `filter_upwards`).
   * Map + coverage: `hact` and s9's bound, eventually. `r = o(V)`: s5 (with s1), second conjunct.
   * Collisions: s8 (with s1–s3) at `(R, P, A := 4)` gives eventually `#coll ≤ 4R·y/(log y·T²)`, `T = logLog y`.
     Given ε'>0, eventually also `y/(2 log y) ≤ V y` (s5) and `T ≥ max(1, 8R/ε')`; then
     `4R/T² ≤ 4R/T ≤ ε'/2` and `#coll ≤ (4R/T²)(y/log y) ≤ (ε'/2)(2V y) = ε' V y`. (File l.63928–63957.)
   * Nonemptiness: eventually `V y − |image| ≤ εV y + r y`, `|r y| ≤ V y/4`, `V y > 0`. If `Q y = ∅` then
     `V y ≤ εV y + V y/4 < (3/4)V y`, contradiction. So `Q y ≠ ∅`, and any `(b,p) ∈ Q y` has `b ∈ (S y).cores`
     (membership in `corePairs`), so `(S y).cores` is eventually nonempty. (File l.64428–64446, 64551–64554.)
   * Imbalance: s7 (with s1) applied to `C y := (S y).cores`, `R := (R:ℝ)`, `A := 4`, using `hcore` and nonemptiness,
     gives the o-statement for `corePairs (C y) (y^{0.99}) y` = `Q y` (by definition) and `corePairs (C y) (y^{0.99}) (y/2)`.
     Convert: eventually `(Q y).filter (fun bp => corePairValue bp ∈ totientsUpTo (y/2)) = corePairs (C y) (y^{0.99}) (y/2)`
     — `⊆`: a member lies in `corePairs … y` and its value is ≤ y/2; `⊇`: a member of `corePairs … (y/2)` lies in
     `corePairs … y` (since y/2 ≤ y) and by `hact` its value is a positive totient ≤ y/2. Membership in `corePairs`
     needs `0 ≤ hi` and positive cores, where the range bound `p ≤ ⌊hi⌋+1` follows from `(p−1)b ≤ hi, b ≥ 1`
     (file `mem_corePairs` l.738, `corePairs_filter_totients` l.63563). Then `IsLittleO.congr'`.
   All four contracts hold, so s4 yields `Tendsto (fun x => V (2*x)/V x) atTop (𝓝 2)`. (File l.64526–64557.)

## 5. Supporting Evidence & Positive Test Cases (scratch/evidence.py; sieve of φ up to 1.6·10⁷, max n/φ(n)=5.85 so all preimages of m ≤ 2·10⁶ are seen)

| x | V(x) | V(2x) | V(2x)/V(x) |
|---|---|---|---|
| 10 | 6 | 10 | 1.6667 |
| 100 | 38 | 72 | 1.8947 |
| 10³ | 291 | 543 | 1.8660 |
| 10⁴ | 2374 | 4486 | 1.8896 |
| 10⁵ | 20254 | 38992 | 1.9252 |
| 5·10⁵ | 93080 | 180184 | 1.9358 |
| 10⁶ | 180184 | 349297 | 1.9386 |

(V(10⁶) = 180184 agrees with OEIS A264810.) The ratio creeps toward 2, consistent with the target (the convergence
is logarithmically slow, as expected from a PNT-driven mechanism).

* s5(a) `π(x) ≤ V(x)`: no violation at any sampled x ≤ 2·10⁶ (step 997); e.g. π(10⁶)=78498 ≤ 180184, and
  `x/(2 log x)` = 36191 ≤ V(10⁶).
* s4(b) finite counting inequality: 20,000 random instances (|T| ≤ 40, |P| ≤ 50, random f, random T₀ ⊆ T): 0 violations.
  Hand check: T={1,2,3,4}, T₀={1,2}, P={a,b,c}, f=(1,1,3): I={1,3}, P₀={a,b}, I₀={1}; LHS=|4−4|=0;
  RHS=|3−4|+(4−2)+(3−2)=4 ✓.
* s4(d) quotient lemma: v=10, w=21, δ=1/21: |w/v−2| = 0.1 ≤ 4/21 ≈ 0.19 ✓.
* s6(ii),(iv) arithmetic identity on a concrete record-like datum: tail 3 (φ=2), lower primes 101 > 29 > 19
  (all > max(17, P⁺(3))); integer = 3·101·29·19 = 166953, numericalCore = 2·100·28·18 = 100800 = φ(166953);
  with p = 1009 > 101: φ(1009·166953) = 1008·100800 = 101606400 = corePairValue(100800, 1009) ✓.
* s7 imbalance, cores {1,2,4,6,10,12}, y = 2·10⁶: with lower cutoff y^{0.8}: (|Q| − 2|Q(y/2)|)/|Q| = 0.014;
  y^{0.6}: −0.053; y^{0.5}: −0.057 (π(x/2)/π(x) ≈ 0.53 at this scale, → 1/2). With the true cutoff y^{0.99}
  the half-range is empty at this y because `y^{0.99} < y/2` needs `y > 2^{100}` — the lemma is purely asymptotic.
* s1 sanity: π(10⁶)/(10⁶/log 10⁶) = 1.084 → 1.
* Mathlib probes: `Chebyshev.eventually_primeCounting_le`, `Chebyshev.primeCounting_sub_theta_div_log_isBigO`,
  `isLittleO_log_rpow_atTop`, `Asymptotics.isEquivalent_iff_tendsto_one`, `Finset.card_le_card_of_surjOn`,
  `Finset.eventually_all`, `Nat.totient_mul`, `Nat.totient_prime_pow_succ`, `Fintype.ofInjective`,
  `EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum`, `Finset.exists_cycleOn`,
  `MeasureTheory.Measure.addHaar_smul_of_nonneg`, `Real.eulerMascheroniConstant` all exist with the shapes used.
  Absent: PNT, Mertens, `Nat.primesLE` (hence s1–s3 are LEMMAs and the Finset.Iic form is used).

Why each LEMMA is massively easier than the root (1B):
* s1/s2/s3: single classical theorems about primes, no totients; complete formal proofs in hand (ports).
* s4: finite combinatorics + ε-bookkeeping, ~250 lines; no number theory at all.
* s5: two injections and one little-o fact, given PNT; ~80 lines.
* s6: elementary inequalities on one record + one application of multiplicativity; ~300 lines.
* s7: a uniform-PNT counting statement about primes in intervals `(y^{0.99}/b, y/b]`; no totients; ~400 lines.
* s8: a one-sided sieve bound for a structured family, no V, no asymptotic equality; ~13k lines but self-contained.
* s9: one one-sided coverage estimate with all prime-distribution inputs given as hypotheses.

## 6. Adversarial Refutation & Falsification Attempts

* **Is the target false?** The certified proof is kernel-checked with standard axioms against the identical
  statement; numerics trend toward 2. No refutation attempted beyond that; `refute` is out of the question.
* **Degenerate x** (x < 1): V = 0 and Lean's `0/0 = 0`; irrelevant for `atTop`. All children are `∀ᶠ`/little-o.
* **Floors**: V(2x) uses ⌊2x⌋₊ ≠ 2⌊x⌋₊ in general; s4 works with real endpoints and never relates floors. ✓
* **Small-y degeneracy**: `y^{0.99} ≥ y/2` for `y ≤ 2^{100}` makes `corePairs(…, y/2)` empty there; every
  statement is eventual, and s7's proof uses `y^{0.99}/b = o(y/(b log y))`. ✓
* **p = 2 / tiny primes in pairs**: value `(p−1)b ≤ p·integer ≤ Y^{99/100}` for `p ≤ Y^{9/10}`, so such pairs are
  never in `powerRawPairs` eventually (s6(iv)). ✓
* **R = 0, P < 17, L = 0**: no `LowerCoreRecord` exists (tail_pos/tail_le; last_lower/last_upper; length_pos), so
  cores = ∅, `powerRawPairs = ∅`, collisions = 0 ≤ 0 (s8 with R = 0 ✓), s6/s7 vacuous. s9 must choose R ≥ 1 itself.
* **A ≤ 0** in s6: records need L ≥ 1 but `L ≤ A·log(logLog Y) ≤ 0` once `logLog Y > 1`; vacuous ✓. s8 assumes A > 0.
* **Negative/zero real R in s7**: `Real.log R` is a constant (log|R|, or 0); `G(y)/log y → 0` still. ✓
* **Collisions of distinct pairs with the same prime**: impossible, `(p−1)b = (p−1)b' ⇒ b = b'` (p ≥ 2). ✓
* **Coverage with ε < 1/2 but family empty**: excluded by the nonemptiness argument in s10 (needs V > 0 and
  `r ≤ V/4`), which is exactly why s4 restricts to `ε < 1/2`. ✓
* **Weaker-than-file statements**: s9 is existential in L (implied by the file's version via
  `coreDimension_le_four_log`, valid once `logLog y ≥ e`); s6 bundles two file facts; s7 uses the explicit
  G = logCoreBound; s8/s9 carry extra true hypotheses. None is stronger than what the file proves. ✓
* **Hypothesis types must match**: the PNT/MERT/EULER hypotheses of s5, s7, s8, s9 must be literally the
  conclusions of s1, s2, s3 so s10 can pass them. ✓ (written out in full in the scaffold.)
* **Instance diamonds**: `totientsUpTo`, `corePairs`, `collisionPoints` use `Classical` decidability exactly as
  `Erdos416.V` does (`open scoped Classical in`), so `V x = (totientsUpTo x).card` is `rfl` (file l.93). ✓

## 7. Freshness & Anti-Recycling Audit

First decomposition of this node (0 prior attempts, no §6 history, no §9 ledger, `get_accessible_nodes` empty).
No sibling nodes exist; nothing is cited that is unproved elsewhere. All nine LEMMAs are fresh. The plan re-uses an
external, kernel-verified proof (attributed in §0/§2 and in findings.md), which the skill explicitly permits.

## 8. Open Risks

* **Mathlib version drift** (highest practical risk): the file compiles on a newer Mathlib; missing names are
  listed in §0. s1 (≈12k lines) and s8/s9 (≈13k/≈40k lines) may hit many small breakages. If the PNT port for s1
  proves intractable, the fallback route is `Chebyshev.primeCounting_sub_theta_div_log_isBigO` + a separate
  proof of `θ(x) ~ x`.
* **s9 size**: it carries ~60% of the verified proof and will need a multi-level decomposition (suggested split in
  its sketch). If a child finds a gap in the file's argument that is invisible from the statement level, the most
  likely place is the relative-to-V exception counts, which depend on Ford's lower bound (`FordLower`).
* **s8** uses a counting-envelope bound for totient multiplicity and the Selberg sieve port; the constant 4R in its
  statement is exactly the file's; do not change it without re-checking s10's arithmetic (any `c·R` works there).
* **Shared definitions**: `LowerCoreRecord`'s `facet` field uses `FordGeometry.outerForm` (a linear map). Keep it
  a linear map, not a plain function, so copied code (`map_add`, `outerForm_eq_extended_sum`) keeps working.
* The certified proof has not been human-reviewed (erdosproblems.com lists it as an unverified claim), but it is a
  kernel-checked artifact with standard axioms and matching statement hash; our children re-check every slice.
