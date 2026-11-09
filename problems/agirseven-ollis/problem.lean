import Mathlib
set_option maxHeartbeats 4000000

/-!
# The Ağırseven–Ollis Linear-Realization Conjecture

*References:*
- O. Ağırseven and M. A. Ollis, *Construction Techniques for Linear Realizations of Multisets
  with Small Support*, arXiv:2502.00164 (2025), Conjecture 1.11.
- *A Resolution of the Ağırseven–Ollis Linear-Realization Conjecture* (`Linreal_Proof.pdf`),
  Definitions 1.1, 1.4, 2.1 and Theorem 1.5.

## Mathematical Statement

Let $v \ge 2$ be an integer, and label the vertices of the complete graph $K_v$ by
$V_v = \{0, 1, \dots, v - 1\}$. For a sequence $P = (p_0, \dots, p_{v-1})$, let
$$\Delta(P) = L(P) := \{\!\{ |p_{i+1} - p_i| \mid 0 \le i < v - 1 \}\!\}$$
denote its multiset of adjacent absolute differences, counted with multiplicity.
A **linear realization** of a multiset $L$ of $v - 1$ positive integers is a permutation
$P = (p_0, \dots, p_{v-1})$ of $V_v = \{0, \dots, v - 1\}$ such that $L(P) = L$.
It is *standard* if $p_0 = 0$, and *perfect* if $p_0 = 0$ and $p_{v-1} = v - 1$.

An **admissible tuple** (Definition 1.4) is a tuple of integers $(y, k, a, b, c)$ satisfying
$$1 \le k < \frac{y}{2}, \qquad a \ge y, \qquad b, c \ge 0.$$
For such a tuple, put $v = a + b + c + 1$ and define the prescribed edge-length multiset
$$L(y, k; a, b, c) := \{1^a, (y - k)^b, y^c\},$$
where exponents denote multiplicities (a length with exponent zero is absent from the multiset).

**The Ağırseven–Ollis Linear-Realization Conjecture** (Conjecture 1.11 of [AO25]; Theorem 1.5 of
`Linreal_Proof.pdf`) asserts that for every admissible tuple $(y, k, a, b, c)$, the multiset
$L(y, k; a, b, c)$ has a linear realization on $\{0, \dots, v - 1\}$ (with unrestricted endpoints).
-/

namespace LinearRealization

/-- The multiset $\Delta(P) = L(P) = \{\!\{ |p_{i+1} - p_i| : 0 \le i < v - 1 \}\!\}$ of adjacent
absolute differences of a vertex sequence `p` (Definitions 1.1 and 2.1). -/
def edgeLengths (p : List ℕ) : Multiset ℕ :=
  (List.zipWith (fun a b => Int.natAbs ((b : ℤ) - (a : ℤ))) p p.tail : List ℕ)

/-- A sequence `p` is a permutation of $V_v = \{0, 1, \dots, v - 1\}$. -/
def IsVertexPerm (v : ℕ) (p : List ℕ) : Prop :=
  p.Perm (List.range v)

/-- `p` is an (ordinary) **linear realization** of a multiset `L` on $\{0, \dots, v - 1\}$
(Definitions 1.1 and 2.1). -/
def IsLinearRealization (v : ℕ) (L : Multiset ℕ) (p : List ℕ) : Prop :=
  IsVertexPerm v p ∧ edgeLengths p = L

/-- `p` is a **standard linear realization** of `L` on $\{0, \dots, v - 1\}$, i.e. a linear
realization starting at `0` (Definitions 1.1 and 2.1). -/
def IsStandardLinearRealization (v : ℕ) (L : Multiset ℕ) (p : List ℕ) : Prop :=
  IsLinearRealization v L p ∧ p.head? = some 0

/-- `p` is a **perfect linear realization** of `L` on $\{0, \dots, v - 1\}$, i.e. a standard
linear realization ending at `v - 1` (Definitions 1.1 and 2.1). -/
def IsPerfectLinearRealization (v : ℕ) (L : Multiset ℕ) (p : List ℕ) : Prop :=
  IsStandardLinearRealization v L p ∧ p.getLast? = some (v - 1)

/-- A multiset `L` has a linear realization on $\{0, \dots, v - 1\}$ (with unrestricted
endpoints). -/
def HasLinearRealization (v : ℕ) (L : Multiset ℕ) : Prop :=
  ∃ p : List ℕ, IsLinearRealization v L p

/-- The prescribed three-length multiset $L(y, k; a, b, c) = \{1^a, (y - k)^b, y^c\}$ with
multiplicities $a, b, c$ (Definition 1.4 and Notation 2.2). Here `+` on `Multiset ℕ` is multiset
sum ($\uplus$), which adds multiplicities. -/
def prescribedLengths (y k a b c : ℕ) : Multiset ℕ :=
  Multiset.replicate a 1 + Multiset.replicate b (y - k) + Multiset.replicate c y

/-- An **admissible tuple** $(y, k, a, b, c)$ of nonnegative integers satisfying
$1 \le k < y / 2$ (i.e. $2k < y$) and $a \ge y$ (Definition 1.4). -/
def IsAdmissibleTuple (y k a _b _c : ℕ) : Prop :=
  1 ≤ k ∧ 2 * k < y ∧ y ≤ a

/-- **The Ağırseven–Ollis Linear-Realization Conjecture** (Conjecture 1.11 of [AO25]; resolved in
Theorem 1.5 of `Linreal_Proof.pdf`):
Let $y, k, a, b, c \in \mathbb{N}$ satisfy $1 \le k < y / 2$ (i.e. $2k < y$) and $a \ge y$, and
put $v = a + b + c + 1$. Then there exists a permutation $(x_0, \dots, x_{v-1})$ of
$\{0, \dots, v - 1\}$ whose multiset of adjacent absolute differences is
$\{1^a, (y - k)^b, y^c\}$. -/
theorem agirseven_ollis_linear_realization_conjecture
    (y k a b c : ℕ) (hk : 1 ≤ k) (hyk : 2 * k < y) (ha : y ≤ a) :
    HasLinearRealization (a + b + c + 1) (prescribedLengths y k a b c) := by
  sorry

end LinearRealization
