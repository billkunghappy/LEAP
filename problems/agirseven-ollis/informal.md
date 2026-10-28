# Blueprint: agirseven_ollis_linear_realization_conjecture
Revision: 2

> **Revision 2 change log (reviewer SHAPE, minimal change).** Children s1–s5, s7, s8, s9 are
> resubmitted WORD FOR WORD (s1–s5 are already FORMAL_PROVED; s7–s9 keep their existing nodes).
> Only s6 changes: the old `base_A` is replaced by `base_A_par`, identical except for the extra
> hypothesis `¬ (y % 2 = 1 ∧ k % 2 = 0)` (i.e. excluding y odd / k even, the class where m = y−k is
> odd together with y). It needs a new name because the node `base_A` holds the old statement.
> The excluded class is routed in the assembly s10 through `base_B` + two applications of the
> proved `grow_top_end_iter` (with ℓ = y, then ℓ = m) — new sub-case (A-oe) in s10, full proof
> below. Idea due to base_A findings, ANCESTOR NOTE 5; checked by hand by the reviewer and
> numerically here (§4 E4).

## 1. Statement

Fix naturals `y k a b c` with `1 ≤ k`, `2k < y`, `y ≤ a`. Put `m := y - k` and `v := a + b + c + 1`.
Goal: there is a list `p` that is a permutation of `[0, v)` (`List.Perm p (List.range v)`) whose multiset of
adjacent absolute differences `edgeLengths p` equals `prescribedLengths y k a b c =
replicate a 1 + replicate b (y-k) + replicate c y`. This is exactly the formal signature
(`HasLinearRealization (a+b+c+1) (prescribedLengths y k a b c)`); nothing is changed.

Elementary consequences of the hypotheses used everywhere: `k < m < y`, `m ≥ 2`, `y ≥ 3`
(`m = y-k > k ≥ 1`). In particular `1 ∉ {m, y}` and `m ≠ y`, so the three lengths are distinct.

Calibration. This is Conjecture 1.11 of Ağırseven–Ollis, arXiv:2502.00164 (2025); that paper proves
it only for `k ≤ 2` (Theorem 1.9) and says the method of its Theorem 3.5 "breaks down at k = 5".
The file header cites an unpublished resolution (`Linreal_Proof.pdf`) that I could not find online.
So this is a research-level theorem, much harder than any Mathlib lemma or olympiad problem; the
closest published analogue (the k = 1 case, their ref. [1]) is a full paper of explicit constructions.
I expect it to split into (i) generic, provable-now machinery: padding by 1-edges and four
"growth" surgeries that make the problem periodic in `b` (period `m`) and in `c` (period `y`), and
(ii) four bounded "base window" families, where all remaining difficulty lives.
Nine children in total: five that are routine list surgery, four base windows.

## 2. Strategy

**Periodicity by row-insertion ("growth"), then a bounded base.**
If the top `ℓ` vertices `[v-ℓ, v-1]` of a realization are linked in consecutive pairs by 1-edges
(plus, depending on parity, an endpoint at `v-1`), then inserting a new row of `ℓ` vertices above
them and replacing each pair-edge `x—x'` by `x—(x+ℓ)—(x'+ℓ)—x'` adds exactly `ℓ` edges of length `ℓ`
and reproduces the same pattern one row higher (Ağırseven–Ollis, arXiv:2502.00164, Lemma 2.5 "type
C_y"; there it is used only at the top). The mirror-image surgery at the bottom (shift everything by
`ℓ`, insert a row below) adds `ℓ` edges of length `ℓ`. Using `ℓ = y` on top and `ℓ = m` at the
bottom, and noting that each surgery leaves every edge away from its own window untouched, any
`(b, c)` reduces to a base with `b₀ ∈ [0, 2m)`, `c₀ ∈ [0, 2y)` (`b ≡ b₀ mod m`, `c ≡ c₀ mod y`), using
**at most `y` ones**; since `a ≥ y`, the remaining `a - a₀` ones are appended as a run
`v, v+1, …` at an endpoint equal to `0` or `v-1` (paper Lemma 2.2).
What got easier: an infinite family in `(b, c)` for each `(y, k)` becomes a finite (bounded-window)
family; all unbounded growth is handled by four uniform, completely explicit surgeries.
Difficulty is concentrated in the four base windows s6–s9; s6 (the generic window) is tagged crux,
but s7–s9 are of the same nature (boundary strips), so the difficulty is really distributed over them.

## 3. Proof

### Shared definitions (to be placed in the scaffold's definitions block, verbatim)

```lean
/-- `u` and `w` are consecutive (in either order) in `p`. -/
def Adj (p : List ℕ) (u w : ℕ) : Prop :=
  ∃ l₁ l₂ : List ℕ, p = l₁ ++ u :: w :: l₂ ∨ p = l₁ ++ w :: u :: l₂

/-- `x` is an endpoint of `p`. -/
def IsEnd (p : List ℕ) (x : ℕ) : Prop :=
  p.head? = some x ∨ p.getLast? = some x

/-- Bottom window `[0, ℓ-1]`, "end" form: 0 is an endpoint, `2j-1 — 2j` are path edges for
`1 ≤ j`, `2j ≤ ℓ-1`, and if `ℓ` is even `ℓ-1` is (the other) endpoint. -/
def BotEndInv (ℓ : ℕ) (p : List ℕ) : Prop :=
  IsEnd p 0 ∧ (∀ j : ℕ, 1 ≤ j → 2 * j + 1 ≤ ℓ → Adj p (2 * j - 1) (2 * j)) ∧
    (Even ℓ → IsEnd p (ℓ - 1))

/-- Bottom window, "pair" form (ℓ even): `2j — 2j+1` are path edges for `2j+1 ≤ ℓ-1`. -/
def BotPairInv (ℓ : ℕ) (p : List ℕ) : Prop :=
  Even ℓ ∧ ∀ j : ℕ, 2 * j + 2 ≤ ℓ → Adj p (2 * j) (2 * j + 1)

/-- Top window `[v-ℓ, v-1]`, mirror image of `BotEndInv` under `x ↦ v-1-x`. -/
def TopEndInv (ℓ v : ℕ) (p : List ℕ) : Prop :=
  IsEnd p (v - 1) ∧ (∀ j : ℕ, 1 ≤ j → 2 * j + 1 ≤ ℓ → Adj p (v - 2 * j) (v - 1 - 2 * j)) ∧
    (Even ℓ → IsEnd p (v - ℓ))

/-- Top window, mirror image of `BotPairInv`. -/
def TopPairInv (ℓ v : ℕ) (p : List ℕ) : Prop :=
  Even ℓ ∧ ∀ j : ℕ, 2 * j + 2 ≤ ℓ → Adj p (v - 1 - 2 * j) (v - 2 - 2 * j)
```

Explicit windows, e.g. `ℓ = 5`: BotEndInv = {0 is an end, 1—2, 3—4}; `ℓ = 4`: BotEndInv = {0 and 3
are the ends, 1—2}, BotPairInv = {0—1, 2—3}. Top versions: replace `x` by `v-1-x`.

Two helper facts every child below may need (each is a two-line proof; a child may prove it
inline): (H1) `edgeLengths p.reverse = edgeLengths p` (as multisets: the zipWith of the reversed
list is the reverse of the zipWith with arguments swapped, `natAbs (a-b) = natAbs (b-a)`,
`Multiset.coe_reverse`), and `Adj`, `IsEnd`, `IsVertexPerm` are invariant under `List.reverse`
(`List.reverse_perm`, `List.head?_reverse`, `List.getLast?_reverse`). (H2) for lists `l₁ ++ l₂`
with both nonempty: `edgeLengths (l₁ ++ l₂) = edgeLengths l₁ + {natAbs (head l₂ - last l₁)} +
edgeLengths l₂` (from `List.zipWith_append`, `List.tail_append_of_ne_nil`).

### Steps

1. [s1] [LEMMA] pad_ones : ∀ (v s : ℕ) (L : Multiset ℕ) (p : List ℕ), 1 ≤ v → IsLinearRealization v L p → (IsEnd p 0 ∨ IsEnd p (v - 1)) → HasLinearRealization (v + s) (L + Multiset.replicate s 1).

   Proof. `s = 0`: take `p`. Otherwise two cases.
   (a) `IsEnd p (v-1)`: let `q := p` if `p.getLast? = some (v-1)`, else `q := p.reverse` (then
   `q.getLast? = some (v-1)` by `List.getLast?_reverse`). Put `p' := q ++ (List.range s).map (v + ·)`.
   Perm: `q ~ range v` (reverse_perm) and `List.range_add : range (v + s) = range v ++ map (v + ·) (range s)`,
   so `p' ~ range (v+s)` by `List.Perm.append_right`. Lengths by (H2): `edgeLengths q = L` (H1),
   the junction edge `|v - (v-1)| = 1`, and the run `v, v+1, …, v+s-1` has `s-1` ones; total
   `L + replicate s 1`.
   (b) `IsEnd p 0`: orient `q` with `q.head? = some 0`; `p' := (List.range s) ++ q.map (s + ·)`.
   Perm: `range (s + v) = range s ++ map (s + ·) (range v)` and `v + s = s + v`. Translation
   preserves differences, junction `|s - (s-1)| = 1`. ∎ (Paper Lemma 2.2.)

2. [s2] [LEMMA] grow_top_end_iter : ∀ (ℓ v t : ℕ) (L : Multiset ℕ) (p : List ℕ), 2 ≤ ℓ → ℓ ≤ v → IsLinearRealization v L p → TopEndInv ℓ v p → ∃ p' : List ℕ, IsLinearRealization (v + t * ℓ) (L + Multiset.replicate (t * ℓ) ℓ) p' ∧ TopEndInv ℓ (v + t * ℓ) p' ∧ (∀ u w : ℕ, u + ℓ < v → w + ℓ < v → Adj p u w → Adj p' u w) ∧ (∀ x : ℕ, x + ℓ < v → IsEnd p x → IsEnd p' x).

   Proof: induction on `t` (for `t+1` apply the one-step surgery to the `t`-result, whose vertex
   count is `v_t = v + tℓ ≥ v`, so the "far" region `u + ℓ < v` is inside `u + ℓ < v_t`; replicate
   counts add by `Multiset.replicate_add`, `(t+1)ℓ = tℓ + ℓ`).
   **One step** (`v ↦ v+ℓ`). Orient `p` so that `p.getLast? = some (v-1)` (H1). Let
   `J := {j : 1 ≤ j, 2j+1 ≤ ℓ}` and for `j ∈ J` the pair `{x_j, x_j'} = {v-2j, v-1-2j}`, consecutive in
   `p` by TopEndInv. For every `j ∈ J` replace the consecutive block `x, x'` (in whichever order it
   occurs) by `x, x+ℓ, x'+ℓ, x'`; append `v-1+ℓ` after the final `v-1`; if `ℓ` is even, `p` starts
   at `v-ℓ` (it is an end and `≠ v-1`), prepend `v`.
   Length bookkeeping: each block swap removes one `1` and adds `ℓ, 1, ℓ` (net `+{ℓ,ℓ}`); the append
   adds `ℓ`; the prepend adds `|v-(v-ℓ)| = ℓ`. `|J| = ⌊(ℓ-1)/2⌋`, so added `ℓ`-edges:
   ℓ odd `2·(ℓ-1)/2 + 1 = ℓ`; ℓ even `2·(ℓ/2-1) + 1 + 1 = ℓ`.
   New vertices: `{v-2j+ℓ, v-1-2j+ℓ : j ∈ J} ∪ {v+ℓ-1} (∪ {v} if ℓ even) = [v, v+ℓ-1]` exactly once
   each (ℓ odd: pairs `{v,v+1},…,{v+ℓ-3,v+ℓ-2}` plus `v+ℓ-1`; ℓ even: pairs `{v+1,v+2},…,{v+ℓ-3,v+ℓ-2}`
   plus `v`, `v+ℓ-1`), so `p' ~ range (v+ℓ)` via `List.range_add`.
   New invariant (with `v' = v+ℓ`): `v'-1` is last; pairs `{v'-2j, v'-1-2j} = {x+ℓ, x'+ℓ}` are
   consecutive; if ℓ even, `v'-ℓ = v` is first. Far part: the only removed edges are the pair edges,
   whose endpoints are `≥ v-ℓ`; ends `< v-ℓ` can only be the first element when ℓ is odd, which is
   unchanged. ∎  (Concrete run: see §4, Example G.)

3. [s3] [LEMMA] grow_top_pair_iter : ∀ (ℓ v t : ℕ) (L : Multiset ℕ) (p : List ℕ), 2 ≤ ℓ → ℓ ≤ v → IsLinearRealization v L p → TopPairInv ℓ v p → ∃ p' : List ℕ, IsLinearRealization (v + t * ℓ) (L + Multiset.replicate (t * ℓ) ℓ) p' ∧ TopPairInv ℓ (v + t * ℓ) p' ∧ (∀ u w : ℕ, u + ℓ < v → w + ℓ < v → Adj p u w → Adj p' u w) ∧ (∀ x : ℕ, x + ℓ < v → IsEnd p x → IsEnd p' x).

   Proof: induction on `t` as in s2. One step (ℓ even): pairs `{v-1-2j, v-2-2j}`, `0 ≤ j ≤ ℓ/2-1`
   (covering `[v-ℓ, v-1]`); replace each consecutive block `x, x'` by `x, x+ℓ, x'+ℓ, x'`. Added:
   `2·(ℓ/2) = ℓ` edges of length ℓ, one `1` removed and one re-added per pair. New vertices
   `[v, v+ℓ-1]` once each; new pairs `{v'-1-2j, v'-2-2j}` consecutive. No endpoint changes (a block
   at an end keeps that end), all non-pair edges preserved. ∎

4. [s4] [LEMMA] grow_bot_end_iter : ∀ (ℓ v t : ℕ) (L : Multiset ℕ) (p : List ℕ), 2 ≤ ℓ → ℓ ≤ v → IsLinearRealization v L p → BotEndInv ℓ p → ∃ p' : List ℕ, IsLinearRealization (v + t * ℓ) (L + Multiset.replicate (t * ℓ) ℓ) p' ∧ BotEndInv ℓ p' ∧ (∀ u w : ℕ, ℓ ≤ u → ℓ ≤ w → Adj p u w → Adj p' (u + t * ℓ) (w + t * ℓ)) ∧ (∀ x : ℕ, ℓ ≤ x → IsEnd p x → IsEnd p' (x + t * ℓ)).

   Proof: induction on `t` (vertices `≥ ℓ` stay `≥ ℓ` after `+ℓ`, so the far clauses compose:
   `u + tℓ + ℓ = u + (t+1)ℓ`). **One step**: orient `p` with `p.head? = some 0` (H1). Let
   `q := p.map (· + ℓ)` (a realization of `L` on `[ℓ, v+ℓ)`, same differences). For each `j` with
   `1 ≤ j`, `2j+1 ≤ ℓ`, the vertices `2j-1+ℓ, 2j+ℓ` are consecutive in `q`; replace that block
   `x+ℓ, x'+ℓ` by `x+ℓ, x, x', x'+ℓ`. Prepend `0` (edge `0—ℓ`). If `ℓ` even, `p` ends at `ℓ-1`, so `q`
   ends at `2ℓ-1`; append `ℓ-1`. Added ℓ-edges: ℓ odd `1 + (ℓ-1) = ℓ`; ℓ even `1 + (ℓ-2) + 1 = ℓ`.
   Vertex set `[0, ℓ) ∪ ([0,v)+ℓ) = [0, v+ℓ)` via `List.range_add` (`range (ℓ + v) = range ℓ ++
   map (ℓ + ·) (range v)`, `List.Perm.map`). New BotEndInv: `0` first, new pairs `2j-1, 2j` inserted
   adjacent, `ℓ-1` last if ℓ even. Far: non-pair edges `u—w` with `u, w ≥ ℓ` become `(u+ℓ)—(w+ℓ)`;
   an end `x ≥ ℓ` is the last element (ℓ odd; for ℓ even both ends are `< ℓ`), which becomes `x+ℓ`. ∎

5. [s5] [LEMMA] grow_bot_pair_iter : ∀ (ℓ v t : ℕ) (L : Multiset ℕ) (p : List ℕ), 2 ≤ ℓ → ℓ ≤ v → IsLinearRealization v L p → BotPairInv ℓ p → ∃ p' : List ℕ, IsLinearRealization (v + t * ℓ) (L + Multiset.replicate (t * ℓ) ℓ) p' ∧ BotPairInv ℓ p' ∧ (∀ u w : ℕ, ℓ ≤ u → ℓ ≤ w → Adj p u w → Adj p' (u + t * ℓ) (w + t * ℓ)) ∧ (∀ x : ℕ, ℓ ≤ x → IsEnd p x → IsEnd p' (x + t * ℓ)).

   Proof: induction on `t`. One step (ℓ even): `q := p.map (· + ℓ)`; for `0 ≤ j ≤ ℓ/2 - 1` replace
   the consecutive block `2j+ℓ, 2j+1+ℓ` (either order) by `2j+ℓ, 2j, 2j+1, 2j+1+ℓ`. Added `2·(ℓ/2) = ℓ`
   ℓ-edges. Vertex set `[0, v+ℓ)`. New pairs `2j—2j+1` adjacent. Ends: every end `x` of `p` becomes
   end `x+ℓ` of `p'` (blocks at an end keep that end), in particular those with `x ≥ ℓ`. ∎

6. [s6] [LEMMA] [CRUX] base_A_par : ∀ (y k b c : ℕ), 1 ≤ k → 2 * k < y → ¬ (y % 2 = 1 ∧ k % 2 = 0) → y - k ≤ b → b < 2 * (y - k) → y ≤ c → c < 2 * y → ∃ a₀ : ℕ, a₀ ≤ y ∧ ∃ p : List ℕ, IsLinearRealization (a₀ + b + c + 1) (prescribedLengths y k a₀ b c) p ∧ (BotEndInv (y - k) p ∨ BotPairInv (y - k) p) ∧ (TopEndInv y (a₀ + b + c + 1) p ∨ TopPairInv y (a₀ + b + c + 1) p) ∧ (BotEndInv (y - k) p ∨ TopEndInv y (a₀ + b + c + 1) p).

   Lean form for the scaffold (copy exactly):
   ```lean
   lemma base_A_par : ∀ (y k b c : ℕ), 1 ≤ k → 2 * k < y → ¬ (y % 2 = 1 ∧ k % 2 = 0) →
       y - k ≤ b → b < 2 * (y - k) → y ≤ c → c < 2 * y → ∃ a₀ : ℕ, a₀ ≤ y ∧ ∃ p : List ℕ,
         IsLinearRealization (a₀ + b + c + 1) (prescribedLengths y k a₀ b c) p ∧
         (BotEndInv (y - k) p ∨ BotPairInv (y - k) p) ∧
         (TopEndInv y (a₀ + b + c + 1) p ∨ TopPairInv y (a₀ + b + c + 1) p) ∧
         (BotEndInv (y - k) p ∨ TopEndInv y (a₀ + b + c + 1) p) := sorry
   ```
   It is the revision-1 `base_A` with one extra hypothesis. The three remaining parity classes
   `(y mod 2, m mod 2)` are (even, even) [y even, k even], (even, odd) [y even, k odd] and
   (odd, even) [y odd, k odd]; the excluded class is (odd, odd) [y odd, k even].
   Status: TRUE on all tested instances — base_A (strictly stronger) was verified by exact SAT on
   every region-A cell for all `(y,k)` with `y ≤ 11`, always with `a₀ = y−1` (base_A findings,
   rev 3 item 2; this corrects rev-1's DFS-timeout claim that `a₀ = y` was needed).
   Why this is progress over rev-1 `base_A`: the excluded (odd, odd) class is exactly the one with
   no pair window, where both End windows must be exact (a perfect path 0 → n−1 with cups and caps),
   and where every move calculus tried in 7 base_A revisions failed (base_A findings rev 4–7). In
   each remaining class at least one of y, m is even, so at least one window admits the Pair form,
   and pair-form partial growth (base_A findings rev 3 item 3: TopPair(y) survives growth of the
   lowest s/2 top pairs, mirror for BotPair(m)) reduces the window in that coordinate to 2 values
   (c ∈ {y, y+1}, resp. b ∈ {m, m+1}) — a one-dimensional family; the base_D op-catalogue BFS
   covers (odd, even) and (even, odd) fully for y ≤ 9 (base_A findings rev 7 item 1).
   Why it is massively easier than the root: for each fixed `(y,k)` it is a *finite* statement
   (`m·y` pairs `(b,c)`, `v ≤ 3y + 2m`, i.e. at most five rows of width `y`), whereas the root is
   infinite in `(a,b,c)`; all unbounded behaviour has been moved into s1–s5, and one of the four
   parity classes has been moved to s7 (base_B) by the glue branch (A-oe) of s10.
   Honest note: a uniform closed-form construction is **not yet known**; this is where the
   remaining difficulty lives (the literature proves the conjecture only for k ≤ 2).
   Suggested route for the child planner (mechanism, with evidence of where it works and fails):
   *monotone strand model*. With `m = y-k` and a threshold `T`, set `σ(x) = x + m` for `x < T` and
   `σ(x) = x + y` for `x ≥ T` (keep only `σ(x) ≤ v-1`). `σ` is injective (a collision `x+m = x'+y`
   with `x < T ≤ x'` forces `x' = x-k < x`). Its chains ("strands") start at `[0, m-1]` and at the
   `k` consecutive vertices `[T+m, T+y-1]`, and end at the top window `[v-y, v-1]`; strands from
   `[0,m-1]` are `m`-columns that turn into `y`-columns; linking all `y` strands with `y-1` ones
   gives a realization of `{1^{y-1}, m^T, y^{v-y-T}}`. Indexing strands by their entry offset
   `u ∈ [0,y)` into `[T, T+y)`, the top end is `(u - c) mod y` and the bottom end is `(u + b) mod m`
   (for `u < m`) or `T+u` (for `u ≥ m`); so linkability depends only on `(b mod m, c mod y)`.
   The alternating ("battlement") linking realises s6's invariants only on a sparse set of residue
   classes (§4 table), so the child must add further gadgets: per-residue-class thresholds
   `T_r` (`σ(x) = x+m` iff `x < T_{x mod k}`; still injective because `y ≡ m (mod k)`), the spare
   `y`-th one (tail curl, paper Lemma 2.4), and the paper's `Γ_{k,y}` zig-zag strands. Splitting by
   the parities of `y` and `m` (four classes) is natural, because the admissible invariant forms
   (End/Pair) are parity-dependent.

7. [s7] [LEMMA] base_B : ∀ (y k b c : ℕ), 1 ≤ k → 2 * k < y → b < y - k → y ≤ c → c < 2 * y → ∃ a₀ : ℕ, a₀ ≤ y ∧ ∃ p : List ℕ, IsLinearRealization (a₀ + b + c + 1) (prescribedLengths y k a₀ b c) p ∧ (TopEndInv y (a₀ + b + c + 1) p ∨ TopPairInv y (a₀ + b + c + 1) p) ∧ (IsEnd p 0 ∨ TopEndInv y (a₀ + b + c + 1) p).

   Status: TRUE on all tested instances (`y ≤ 9`, §4); here `a₀ = y` is genuinely needed in some
   cases (e.g. `y = 5,7,9`). Finite for fixed `(y,k)`. Evidence of mechanism: for `b = 0, c = y`
   the ladder `0, y, y+1, 1, 2, y+2, y+3, 3, …` (y rungs, `y-1` ones) works (y=7: `[0,7,8,1,2,9,10,3,4,
   11,12,5,6,13]`, ends at `v-1 = 13`, pairs `{11,12},{9,10},{7,8}`); in general `b < m` short
   `m`-edges must be woven into the bottom rows of such a ladder / ω-construction (paper Lemma 2.3).
   Uniform recipe not yet known.

8. [s8] [LEMMA] base_C : ∀ (y k b c : ℕ), 1 ≤ k → 2 * k < y → y - k ≤ b → b < 2 * (y - k) → c < y → ∃ a₀ : ℕ, a₀ ≤ y ∧ ∃ p : List ℕ, IsLinearRealization (a₀ + b + c + 1) (prescribedLengths y k a₀ b c) p ∧ (BotEndInv (y - k) p ∨ BotPairInv (y - k) p) ∧ (IsEnd p (a₀ + b + c) ∨ BotEndInv (y - k) p).

   Status: TRUE on all tested instances (`y ≤ 9`, §4), `a₀ ≤ y-1` observed except `(8,1)` (needs `y`). Finite for fixed
   `(y,k)`. Example (y,k,b,c) = (7,2,5,0): `[0,5,10,11,6,1,2,3,4,9,8,7]` (0 is an end, pairs
   `{1,2},{3,4}`). Mechanism: `m`-columns over `[0, v)` (ω-construction w.r.t. `m`) with `c < y`
   long edges inserted near the top. Uniform recipe not yet known.

9. [s9] [LEMMA] base_D : ∀ (y k b c : ℕ), 1 ≤ k → 2 * k < y → b < y - k → c < y → ∃ a₀ : ℕ, a₀ ≤ y ∧ ∃ p : List ℕ, IsLinearRealization (a₀ + b + c + 1) (prescribedLengths y k a₀ b c) p ∧ (IsEnd p 0 ∨ IsEnd p (a₀ + b + c)).

   Status: TRUE on all tested instances (`y ≤ 9`; and plain standard realizations with `a₀ = y-1`
   exist for all `b ≤ m+2, c ≤ y+2`, `y ≤ 8`). Smallest of the four: `v ≤ 2y + m`, at most three rows.
   Example (7,2,2,3): `[0,7,2,3,4,11,10,9,8,1,6,5]`. Related published result: for `k = 1`,
   paper Lemma 4.6 / ref. [1] (`b + c < y`). Uniform recipe not yet known.

10. [s10] [ELEM] Assembly of the root theorem from s1–s9.

   Let `m := y - k`; from `hk, hyk` get `2 ≤ m`, `m ≤ y`, `3 ≤ y` (omega).
   Define `b₀, t_b` by: if `b < m` then `b₀ = b, t_b = 0`, else `b₀ = m + (b-m) % m`, `t_b = (b-m)/m`;
   similarly `c₀, t_c` with modulus `y`. Then `b = b₀ + t_b·m`, `c = c₀ + t_c·y` (`Nat.div_add_mod`),
   `b₀ < 2m`, `c₀ < 2y`, and `b₀ ≥ m ⇔ b ≥ m`, `c₀ ≥ y ⇔ c ≥ y`. Four cases.

   (A) `m ≤ b`, `y ≤ c` (so `m ≤ b₀ < 2m`, `y ≤ c₀ < 2y`). **Split on `hpar : y % 2 = 1 ∧ k % 2 = 0`.**

   (A-main) `¬ hpar`. s6 (`base_A_par`, its parity hypothesis is exactly `¬ hpar`) at `(b₀,c₀)`
   gives `a₀ ≤ y`, `p` on `v₀ = a₀+b₀+c₀+1 ≥ m+y+1`.
   Apply s2 or s3 (according to the TopInv disjunct) with `ℓ = y`, `t = t_c` (`y ≤ v₀`):
   `p₁` on `v₁ = v₀ + t_c·y`. Every bottom-window fact of `p` (pairs among vertices `≤ m-1`, `IsEnd 0`,
   `IsEnd (m-1)`) involves only vertices `u` with `u + y < v₀` (as `m - 1 + y < v₀`), so it transfers
   to `p₁`: BotInv of the same form holds for `p₁`. Then apply s4 or s5 with `ℓ = m`, `t = t_b`
   (`m ≤ v₁`): `p₂` on `v₂ = v₁ + t_b·m`. Every top-window fact of `p₁` involves only vertices
   `≥ v₁ - y ≥ m`, so it transfers with shift `t_b·m`: `v₁-1 ↦ v₂-1`, `v₁-y ↦ v₂-y`, pairs
   `v₁-2j ↦ v₂-2j`, etc.; TopInv of the same form holds for `p₂`. From the third disjunct of s6:
   BotEndInv ⇒ `IsEnd p₂ 0`; TopEndInv ⇒ `IsEnd p₂ (v₂-1)`. Apply s1 with `s = a - a₀` (`a₀ ≤ y ≤ a`).
   This is verbatim the revision-1 case (A) code of the scaffold, with `base_A y k b₀ c₀ hk hyk hb1
   hb2 hc1 hc2` replaced by `base_A_par y k b₀ c₀ hk hyk hpar hb1 hb2 hc1 hc2`.

   (A-oe) `hpar` holds: y odd, k even. Then `m = y - k` is odd: `(y-k) % 2 = 1` by omega from
   `y % 2 = 1`, `k % 2 = 0`, `k < y`. The bottom window is never used; everything is done on top.
   * (oe1) **Key implication** (pure definition unfolding): for `ℓ' ≤ ℓ` with `ℓ'` odd,
     `TopEndInv ℓ v q → TopEndInv ℓ' v q`. Proof: TopEndInv ℓ' v q = `IsEnd q (v-1)` ∧
     `(∀ j, 1 ≤ j → 2j+1 ≤ ℓ' → Adj q (v-2j) (v-1-2j))` ∧ `(Even ℓ' → IsEnd q (v-ℓ'))`. First conjunct
     is the same as for ℓ. Second: given `j` with `2j+1 ≤ ℓ'`, we have `2j+1 ≤ ℓ` (since `ℓ' ≤ ℓ`), so the
     ℓ-clause gives it. Third: `Even ℓ'` is false (`Even ℓ' ↔ ℓ' % 2 = 0` by `Nat.even_iff`,
     contradiction with `ℓ' % 2 = 1`; or `obtain ⟨r, hr⟩` then omega), so the implication is vacuous.
     Used with `ℓ = y`, `ℓ' = m = y - k` (`m ≤ y`, m odd).
   * (oe2) Apply s7 `base_B y k (b₀ - m) c₀ hk hyk (_ : b₀ - m < y - k) hc1 hc2` (since
     `b₀ < 2m`, omega). Get `a₀ ≤ y`, `p` with `IsLinearRealization v₀ (prescribedLengths y k a₀ (b₀-m) c₀) p`,
     `v₀ = a₀ + (b₀-m) + c₀ + 1`, and `TopEndInv y v₀ p ∨ TopPairInv y v₀ p`. The right disjunct is
     impossible: `TopPairInv y v₀ p` has first conjunct `Even y`, i.e. `y = r + r`, contradicting
     `y % 2 = 1` (omega). So `hTE : TopEndInv y v₀ p`. (The third conjunct of base_B is not needed.)
   * (oe3) Apply s2 `grow_top_end_iter y v₀ t_c _ p (2 ≤ y) (y ≤ v₀) hp hTE` (`v₀ ≥ c₀ + 1 ≥ y + 1`).
     Get `p₁` with `IsLinearRealization v₁ (prescribedLengths y k a₀ (b₀-m) c₀ + replicate (t_c·y) y) p₁`,
     `v₁ = v₀ + t_c·y`, and `TopEndInv y v₁ p₁`. Rewrite the multiset with `eqC`:
     `= prescribedLengths y k a₀ (b₀-m) (c₀ + t_c·y)`.
   * (oe4) By (oe1): `TopEndInv m v₁ p₁`.
   * (oe5) Apply s2 again, `grow_top_end_iter m v₁ (t_b + 1) _ p₁ (2 ≤ m) (m ≤ v₁) hp₁ hTm`
     (`2 ≤ m` since `m > k ≥ 1`; `m ≤ y < v₀ ≤ v₁`). Get `p₂` with
     `IsLinearRealization v₂ (prescribedLengths y k a₀ (b₀-m) (c₀+t_c·y) + replicate ((t_b+1)·m) m) p₂`,
     `v₂ = v₁ + (t_b+1)·m`, and `TopEndInv m v₂ p₂`, whose first conjunct is `IsEnd p₂ (v₂ - 1)`.
   * (oe6) Bookkeeping. Multiset: `eqB a₀ (b₀-m) (c₀+t_c y) (t_b+1)` gives
     `prescribedLengths y k a₀ ((b₀-m) + (t_b+1)·(y-k)) (c₀+t_c·y)`; and
     `(b₀-m) + (t_b+1)·m = b₀ + t_b·m` because `(t_b+1)·m = t_b·m + m` (`add_one_mul` / `Nat.succ_mul`)
     and `b₀ ≥ m` (omega with `t_b·(y-k)` as an atom). Vertex count:
     `a₀ + (b₀-m) + c₀ + 1 + t_c·y + (t_b+1)·m = a₀ + (b₀ + t_b·m) + (c₀ + t_c·y) + 1` (same rewrite,
     then omega). So `v₂ - 1 = a₀ + (b₀+t_b m) + (c₀+t_c y)`.
   * (oe7) `finish a₀ p₂ (a₀ ≤ a, from a₀ ≤ y ≤ a) hp₂ (Or.inr hend)`.
   Lean sketch (inside the case-(A) bullet of the scaffold, after `rcases`):
   ```lean
   by_cases hpar : y % 2 = 1 ∧ k % 2 = 0
   · obtain ⟨a₀, ha₀, p, hp, hTop, -⟩ := base_B y k (b₀ - (y - k)) c₀ hk hyk (by omega) hc1 hc2
     have hTE : TopEndInv y (a₀ + (b₀ - (y - k)) + c₀ + 1) p := by
       rcases hTop with h | ⟨⟨r, hr⟩, -⟩
       · exact h
       · omega
     obtain ⟨p₁, hp₁, hTE₁, -, -⟩ :=
       grow_top_end_iter y _ tc _ p (by omega) (by omega) hp hTE
     have hTm : TopEndInv (y - k) (a₀ + (b₀ - (y - k)) + c₀ + 1 + tc * y) p₁ :=
       ⟨hTE₁.1, fun j hj1 hj2 => hTE₁.2.1 j hj1 (by omega),
        fun ⟨r, hr⟩ => absurd hr (by omega)⟩
     obtain ⟨p₂, hp₂, hTE₂, -, -⟩ :=
       grow_top_end_iter (y - k) _ (tb + 1) _ p₁ (by omega) (by omega) hp₁ hTm
     have hm : (tb + 1) * (y - k) = tb * (y - k) + (y - k) := add_one_mul _ _
     -- rewrite vertex count and multiset (eqC, eqB, hm, omega), then:
     -- exact finish a₀ p₂ (by omega) hp₂' (Or.inr hend)
     sorry
   · -- (A-main): revision-1 code with base_A_par ... hpar ...
   ```
   (The `sorry` marks where the prover writes the `rw [...]`/`omega` bookkeeping of (oe6); it is
   the same pattern as the `ev`/`eqB`/`eqC` rewrites already in the scaffold.)
   (B) `b < m`, `y ≤ c`: s7, then s2/s3 with `t = t_c`; `IsEnd p 0` transfers (`0 + y < v₀` since
   `v₀ ≥ c₀+1 ≥ y+1`), TopEndInv transfers as itself; then s1.
   (C) `m ≤ b`, `c < y`: s8, then s4/s5 with `t = t_b`; `IsEnd p (v₀-1)` transfers to
   `IsEnd (v₀-1+t_b m)` because `v₀ - 1 ≥ b₀ ≥ m`; BotEndInv gives `IsEnd 0`; then s1.
   (D) `b < m`, `c < y`: s9, then s1 directly.
   Final bookkeeping in every case: vertex count `a₀ + b₀ + c₀ + 1 + t_c y + t_b m + (a - a₀) =
   a + b + c + 1`, and `replicate a₀ 1 + replicate b₀ m + replicate c₀ y + replicate (t_c y) y +
   replicate (t_b m) m + replicate (a-a₀) 1 = prescribedLengths y k a b c` by `Multiset.replicate_add`
   and commutativity/associativity of `+` on `Multiset` (note `prescribedLengths` uses `y - k = m`
   literally). Rewrite the vertex count with `congrArg`/`Nat` arithmetic before concluding.

## 4. Supporting Evidence & Positive Test Cases

All scripts are in `scratch/` (Python 3).

**E1. End-to-end verification of the whole reduction** (`scratch/pipeline.py`). For every
`(y,k)` with `3 ≤ y ≤ 7`, `1 ≤ k`, `2k < y`, every `b ∈ [0, 4m]`, `c ∈ [0, 4y]`, `a ∈ {y, y+1, y+3}`:
take a base witness for `(b₀, c₀)` found by exhaustive DFS satisfying exactly the s6–s9
conclusions, apply the s2/s3 surgery `t_c` times and the s4/s5 surgery `t_b` times exactly as
written in s2–s5, then s1; at each step the script asserts: permutation of `range v`, exact length
multiset, the invariant of the same form, far-edge preservation and far-endpoint preservation as
stated in s2–s5, and at the end `v = a+b+c+1`. **11,235 realizations built and verified, 0 failures.**
This covers all four parity classes: `(y,m) = (7,5)` odd/odd, `(5,4)` odd/even, `(6,5)` even/odd,
`(6,4)` even/even, and the minimum `m = 2` (`y=3,k=1`).

**E2. Base windows exist** (`scratch/base_search.py`, `rerun_to.py`): exhaustive DFS with the exact
s6–s9 requirements.

| region | window | (y,k) verified | failures | max a₀ used |
|---|---|---|---|---|
| A (s6) | `b∈[m,2m), c∈[y,2y)` | all with y ≤ 9 | 0 | y−1, except y for (8,1),(9,1) |
| B (s7) | `b<m, c∈[y,2y)` | all with y ≤ 9 | 0 | y (needed for y=5,7,9) |
| C (s8) | `b∈[m,2m), c<y` | all with y ≤ 9 | 0 | y−1, except y for (8,1) |
| D (s9) | `b<m, c<y` | all with y ≤ 9 | 0 | y−1 |

Three y ∈ {8,9} region-A cases hit the 2·10⁶-step DFS cap and were re-run with a 4·10⁷ cap: all found
(`(8,1,13,13)`: a₀=7, `(9,1,15,15)`: a₀=8, `(9,2,13,16)`: a₀=8).

**Example G (s2, s4, s1 on real data).** `(y,k)=(7,2)`, `m=5`, base A at `(b,c)=(5,7)`, `a₀=6`, `v=19`:
`p = [0,7,14,15,8,13,12,5,10,17,16,9,4,3,2,1,6,11,18]` — 0 and 18 are the ends (so perfect);
BotEndInv(5): pairs `{1,2}` (…2,1…), `{3,4}` (…4,3…) ✓; TopEndInv(7,19): end 18, pairs `{16,17}`,
`{14,15}`, `{12,13}` ✓. Lengths: `1^6, 5^5, 7^7` ✓.
After s2 (one step, `v=26`): `[25,18,11,6,1,2,3,4,9,16,23,24,17,10,5,12,19,20,13,8,15,22,21,14,7,0]`
(= reverse orientation; new top pairs `{23,24},{21,22},{19,20}`, end 25).
After s4 (one step, `v=31`): `[0,5,12,19,26,27,20,13,18,25,24,17,10,15,22,29,28,21,14,9,4,3,8,7,2,1,6,11,16,23,30]`.
After s1 (`s=2`): append `31,32`. Result: permutation of `range 33`, lengths `1^8, 5^10, 7^14` ✓ =
`prescribedLengths 7 2 8 10 14`, `v = 8+10+14+1 = 33` ✓.

**E3. Strand model success table** (`scratch/table.py`): single threshold, alternating linking,
s6 invariants required; `#` = works. `(y,k) = (7,2)`, rows `b mod 5`, cols `c mod 7`:
```
0 #.#....
1 ....#.#
2 #......
3 ..#.#..
4 ......#
```
`(10,3)` has three whole rows empty (`b ≡ 3,4,5 mod 7`). So the single-threshold model alone
cannot prove s6 — recorded so the child does not rely on it. Without invariants and with arbitrary
link orders (`scratch/thresh.py`), it still fails on ~31% of `(b,c)` for `y ≤ 9`; with per-class
thresholds (`scratch/multi.py`) failures drop sharply for `k ≥ 2` but remain for `k = 1`
(only one residue class). Using `y-1` vs `y` ones: plain standard realizations with `a = y-1`
exist for all `b ≤ m+2, c ≤ y+2, y ≤ 8` (`scratch/brute.py`), while `a = y-2` fails (e.g. `b = 0`,
`c ≥ 1` for every `(y,k)` tested) — consistent with the bound `a ≥ y` being near-sharp.

**E4. (Revision 2) The new glue branch (A-oe), end to end** (`scratch/glue_oddeven.py`). For every
`(y,k)` with y odd, k even, `2k < y`, `y ≤ 9` — i.e. `(5,2), (7,2), (9,2), (9,4)` — every region-A
base cell `b₀ ∈ [m,2m)`, `c₀ ∈ [y,2y)`, every `t_b, t_c ∈ {0,1,2}`, `a ∈ {y, y+2}`: take a base_B
witness at `(b₀-m, c₀)` (exhaustive DFS with exact base_B conclusions), assert it is NOT TopPairInv
and IS TopEndInv y; grow on top with ℓ = y `t_c` times (assert TopEndInv y each time); assert
TopEndInv m (the implication oe1); grow on top with ℓ = m `t_b + 1` times (assert TopEndInv m, far
preservation, permutation, exact lengths each time); assert `v = a₀ + b + c + 1` with
`b = b₀ + t_b m`, `c = c₀ + t_c y`, `v-1` an end; pad with `a - a₀` ones and assert the final
multiset is `{1^a, m^b, y^c}` on `a+b+c+1` vertices. **2,844 realizations built and verified,
0 failures.** (Independent confirmation of base_A findings' `reframe_check.py`, 148/148.)
Worked instance: `(y,k) = (5,2)`, `m = 3`, `(b₀,c₀) = (3,5)`, `t_b = t_c = 0`: base_B at `(0,5)`
gives a realization of `{1^{a₀}, 5^5}`; one m-growth adds `3^3`, total `{1^{a₀}, 3^3, 5^5}` =
`prescribedLengths 5 2 a₀ 3 5`, consistent with `(b₀-m) + (t_b+1)m = 0 + 3 = 3 = b₀`.

**Mathlib names confirmed by `#check`** (rev 2 additions): `add_one_mul : (a + 1) * b = a * b + b`,
`Nat.succ_mul`, `Nat.even_iff : Even n ↔ n % 2 = 0`, `Nat.odd_iff`, `Multiset.replicate_add`.

**Mathlib names confirmed by `#check`** (`scratch/probe.lean`): `List.range_add`
(`range (n+m) = range n ++ map (n + ·) (range m)`), `Multiset.replicate_add`, `List.zipWith_append`,
`List.Perm.map`, `List.reverse_perm`, `List.perm_ext_iff_of_nodup`, `List.nodup_range`,
`Multiset.coe_reverse`, `List.getLast?_reverse`, `List.head?_reverse`, `Nat.div_add_mod`,
`List.tail_append_of_ne_nil`, `List.zipWith_comm`.

## 5. Adversarial Refutation & Falsification Attempts

- **Is the root false?** Exhaustive search (E2 + `brute.py`) found realizations in every tested
  instance; with `a = y-2` there are failures, so the hypothesis `a ≥ y` is doing real work, but
  `a ≥ y` itself never failed. No refutation.
- **Growth at the smallest length `ℓ = 2`** (`m = 2`, `y=3,k=1`): BotEndInv(2) = {0, 1 are the two
  ends}; one step: `0, (p+2), 1` adds two 2-edges ✓ (E1 covers it). BotPairInv(2) = {0—1}: block
  `2,3 → 2,0,1,3` ✓.
- **`ℓ` even with End form**: the invariant forces both ends into the window (0 and ℓ−1); then the
  "far end" clause of s4 is vacuous (no end `≥ ℓ`), and the End form of the *other* window cannot
  simultaneously hold on the same side — s6's third disjunct only asks for one of them. The
  combination (`m` even End form, `y` odd) is impossible (three ends); s6 does not require it, and the
  search confirms s6 is satisfiable anyway (it picks BotPair + TopEnd there).
- **Window overlap**: s2's far clause is used for bottom vertices `u ≤ m-1` and needs
  `u + y < v₀`; region A has `v₀ ≥ m + y + 1` ✓. s4's far clause for top vertices needs
  `v₁ - y ≥ m` ✓ by the same bound. Region B only transfers `IsEnd 0` (`y < v₀` ✓); region C only
  transfers `IsEnd (v₀-1)` (`v₀-1 ≥ m` ✓).
- **Both disjuncts true** (a path satisfying both BotEndInv and BotPairInv): the lemmas are split
  per form, so the assembly picks one; no ambiguity.
- **Degenerate strands / small v**: s2–s5 need `ℓ ≤ v` so the window exists; in all uses `v₀ ≥ y+1`
  (top) or `v₀ ≥ m+1` (bottom).
- **Off-by-one in `a₀ + b + c` vs `v - 1`**: s8/s9 state the top end as `a₀ + b + c`, which is
  `v - 1` for `v = a₀+b+c+1` (checked in the scripts, which use `n-1`).
- **Parity of the pair ranges**: `2j+1 ≤ ℓ` with `j ≥ 1` gives pairs `(1,2),…` up to `(ℓ-2,ℓ-1)`
  (ℓ odd) or `(ℓ-3,ℓ-2)` (ℓ even); `2j+2 ≤ ℓ` gives `(0,1),…,(ℓ-2,ℓ-1)`. Matches the Python checker
  `bot_req` exactly (E1 asserts invariants with that checker).
- **(Rev 2) Glue branch (A-oe) edge cases.**
  * Smallest instance of the class: `y = 5, k = 2, m = 3` (y odd, k even needs `y ≥ 5`). `b₀ = m`
    gives base_B at `b = 0` (allowed: `0 < m`), `t_b = 0` still performs one m-growth (`t = 1`) —
    covered in E4.
  * `2 ≤ m ≤ v₁` for the m-growth: `m ≥ k+1 ≥ 3` here (k even ⇒ k ≥ 2), `v₁ ≥ v₀ ≥ c₀+1 ≥ y+1 > m` ✓.
  * Implication oe1 fails if m were even (the `Even m → IsEnd (v-m)` clause is not supplied by
    TopEndInv y); that is exactly why the branch is restricted to m odd, which `hpar` guarantees.
    It would also fail if `m > y`; here `m < y` ✓.
  * base_B's TopPair disjunct: impossible for y odd (first conjunct `Even y`) ✓; so no Pair-form
    sub-branch is needed.
  * Natural subtraction `b₀ - m`: `b₀ ≥ m` in case A, so `(b₀ - m) + (t_b+1)m = b₀ + t_b m` is exact ✓.
  * Does `¬hpar` in base_A_par exclude anything the assembly needs? No: the assembly calls
    base_A_par only under `¬hpar`.
- **(Rev 2) Is base_A_par true?** It is implied by rev-1 base_A, which exact SAT verified on every
  region-A cell for all `(y,k)`, `y ≤ 11` (base_A findings rev 3). No counterexample.

## 6. Freshness & Anti-Recycling Audit

Revision 2 is the reviewer-requested minimal change of attempt 1 (context §5 SHAPE reason, which
explicitly asks to resubmit pad_ones, the four grow_*_iter (FORMAL_PROVED, §10) and base_B, base_C,
base_D word for word, and to change only base_A). The subgoal set differs from attempt 1 because
`base_A` is replaced by `base_A_par` (strictly weaker statement, new name — the name `base_A` is
held by the old statement). No subgoal was itself recorded `failed`. base_B/base_C/base_D are
existing unproved nodes taken as `[LEMMA]` dependencies (DAG edges), not cited. s1–s5 are
FORMAL_PROVED and reused verbatim. `top_pairs` (proved, §10) is not needed.

## 7. Open Risks

- s6 (base_A_par) and s7–s9: no uniform construction is known. They are verified for `y ≤ 9`
  (base_A: `y ≤ 11` by SAT) only; a counterexample for larger `y` would kill the corresponding base
  lemma (but not s1–s5). The strand model alone is insufficient (E3). If a base lemma turns out false
  for some residue class, the fix is to enlarge that window, which s1–s5 support unchanged.
- s7 (base_B) now carries more weight: the (A-oe) branch relies on it for the y odd / k even class.
  Its required conclusion there is only TopEndInv y (forced by y odd), which base_A findings
  (`reframe_miss.py`) found realizable on all 158 base_B cells with y ∈ {5,7,9}, k even.
- Do NOT strengthen any base to `a₀ ≤ y-1` (region B needs `a₀ = y` for y = 5,7,9 by DFS; the
  region-A claim to the same effect was a DFS artifact, corrected by SAT).
- s2–s5 are proved; the remaining formal work at the root is the (A-oe) bookkeeping (oe6), which
  follows the existing `ev`/`eqB`/`eqC` pattern.
