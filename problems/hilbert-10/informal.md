# Hilbert’s Tenth Problem via Additive Combinatorics

**Peter Koymans**¹ and **Carlo Pagano**²  
¹ *Mathematisch Instituut, Universiteit Utrecht, Postbus 80.010, 3508 TA Utrecht, The Netherlands, `p.h.koymans@uu.nl`*  
² *Department of Mathematics and Statistics, Montreal, Quebec H3G 1M8, Canada, `carlein90@gmail.com`*  
*April 26, 2026*

---

### Abstract
For all infinite rings $R$ that are finitely generated over $\mathbb{Z}$, we show that Hilbert’s tenth problem has a negative answer. This is accomplished by constructing elliptic curves $E$ without rank growth in certain quadratic extensions $L/K$. To achieve such a result unconditionally, our key innovation is to combine techniques from additive combinatorics with $2$-descent.

> *Wir müssen wissen*  
> *Wir werden wissen*  
> — **David Hilbert**

---

## Navigation: Table of Contents & Key Results

- [1 Introduction](#1-introduction)
  - [1.1 History of the problem](#11-history-of-the-problem)
  - [1.2 Our results](#12-our-results)
    - [Theorem 1.1 (Negative Answer for Finitely Generated Rings)](#theorem-11)
    - [Theorem 1.2 (Conjecture of Denef & Lipshitz: $\mathbb{Z}$ is Diophantine over $\mathcal{O}_K$)](#theorem-12)
  - [1.3 Additive combinatorics](#13-additive-combinatorics) — [Key Equation (1.1)](#equation-11)
  - [1.4 Layout of the paper](#14-layout-of-the-paper)
- [Acknowledgements](#acknowledgements)
- [2 Initial reductions](#2-initial-reductions)
  - [Lemma 2.1 (Diophantine Properties of Subfields)](#lemma-21)
  - [Lemma 2.2 (Denef: Totally Real Fields)](#lemma-22)
  - [Lemma 2.3 (Shlapentokh: Rank Retention)](#lemma-23)
  - [Theorem 2.4 (Core Rank Growth Theorem: $\geq 32$ Real Places)](#theorem-24)
  - [Corollary 2.5 (Galois Extensions Containing $K_0$)](#corollary-25)
  - [Theorem 2.6 (Main Equivalence: $\mathbb{Z}$ is Diophantine over $\mathcal{O}_F$)](#theorem-26)
- [3 Background theory](#3-background-theory)
  - [3.1 Elliptic curves](#31-elliptic-curves) — [Lemma 3.1](#lemma-31), [Lemma 3.2](#lemma-32), [Lemma 3.3](#lemma-33)
  - [3.2 Root numbers](#32-root-numbers) — [Theorem 3.4](#theorem-34), [Theorem 3.5 (2-parity)](#theorem-35), [Corollary 3.6](#corollary-36), [Lemma 3.7 (Starting Curve)](#lemma-37)
  - [3.3 Upper bounds for generator counts](#33-upper-bounds-for-generator-counts) — [Lemma 3.8](#lemma-38)
- [4 Selmer ranks as transition processes](#4-selmer-ranks-as-transition-processes)
  - [Proposition 4.1 (Poonen–Rains Quadratic Forms)](#proposition-41), [Lemma 4.2](#lemma-42), [Lemma 4.3](#lemma-43), [Proposition 4.4](#proposition-44), [Theorem 4.5 (Poitou–Tate Duality)](#theorem-45), [Proposition 4.6](#proposition-46), [Lemma 4.7 (Transition Steps $n_i \in \{2, -2, 0\}$)](#lemma-47), [Remark 4.8](#remark-48), [Lemma 4.9](#lemma-49)
- [5 Proof of Theorem 2.4](#5-proof-of-theorem-24)
  - [5.1 First steps](#51-first-steps) — [Definition 5.1 (Suitable Twist $t$)](#definition-51), [Theorem 5.2](#theorem-52)
  - [5.2 Application of additive combinatorics](#52-application-of-additive-combinatorics) — [Definition 5.3 (Auxiliary Twist $\kappa$)](#definition-53), [Theorem 5.4](#theorem-54), [Lemma 5.5](#lemma-55), [Lemma 5.6](#lemma-56), [Lemma 5.7](#lemma-57), [Lemma 5.8](#lemma-58)
  - [5.3 Construction of an auxiliary twist](#53-construction-of-an-auxiliary-twist)
    - [Lemma 5.9](#lemma-59), [Lemma 5.10](#lemma-510)
    - [5.3.1 Reducing ranks](#531-reducing-ranks) — [Lemma 5.11](#lemma-511), [Lemma 5.12](#lemma-512), [Lemma 5.13](#lemma-513)
    - [5.3.2 Vanishing of auxiliary spaces](#532-vanishing-of-auxiliary-spaces) — [Lemma 5.14](#lemma-514)
    - [5.3.3 Auxiliary primes](#533-auxiliary-primes) — [Definition 5.15](#definition-515), [Lemma 5.16](#lemma-516), [Lemma 5.17](#lemma-517), [Lemma 5.18](#lemma-518), [Lemma 5.19](#lemma-519)
    - [5.3.4 The final step](#534-the-final-step) — [Theorem 5.20 (Existence of $\kappa$)](#theorem-520), [Lemma 5.21](#lemma-521), [Figure 1 (Legendre Symbol Graph)](#figure-1), [Lemma 5.22](#lemma-522), [Lemma 5.23](#lemma-523)
- [References](#references)
- [Appendix A: Additive combinatorics](#appendix-a-additive-combinatorics)
  - [Definition A.1](#definition-a1), [Definition A.2](#definition-a2), [Definition A.3](#definition-a3), [Proposition A.4](#proposition-a4), [Definition A.5](#definition-a5), [Theorem A.6](#theorem-a6), [Theorem A.7](#theorem-a7)
  - [Appendix References](#appendix-references)

---

## 1 Introduction <a id="1-introduction"></a>

### 1.1 History of the problem <a id="11-history-of-the-problem"></a>

At the 1900 mathematical congress in Paris, Hilbert introduced his famous list of 23 problems.
The tenth problem of his list is nowadays interpreted as asking for an algorithm to decide the
solvability of Diophantine equations. Gödel dealt a major blow to this program in 1931 with
his incompleteness theorems, although his results certainly did not rule out the existence of
such an algorithm.
    In 1950, Julia Robinson proved that exponentiation is Diophantine conditional under a
hypothesis that later became known as “J.R.”. One major ingredient in this step is the basic
theory of Pell’s equation. Not much later, Davis, Putnam and Robinson [5] showed that the
hypothesis J.R. implies that every recursively enumerable set is Diophantine, hence Hilbert’s
tenth problem is unsolvable over the integers. Finally, Matiyasevich [25] proved J.R. using
properties of Fibonacci numbers, thus settling Hilbert’s tenth problem in full. Because of the
combined efforts of these four authors, this result became known as the MRDP theorem.
    Nevertheless, the field remained an active research area as the MRDP theorem only settles
the case of integer polynomials and integer solutions, while it is natural to wonder what happens for other number-theoretic rings. One of the main difficulties was to find an appropriate
   ∗
     Mathematisch Instituut, Universiteit Utrecht, Postbus 80.010, 3508 TA Utrecht, The Netherlands,
p.h.koymans@uu.nl
   †
     Department of Mathematics and Statistics, Montreal, Quebec H3G 1M8, Canada, carlein90@gmail.com

<!-- [Original PDF Page 2] -->

substitute for Pell’s equation to show that exponentiation is Diophantine. Fairly early on
researchers realized that algebraic groups of rank 1 could fulfill such a role, but rigorously
establishing their existence has been a difficult problem. As it stands, results from the 1980s
give a negative answer to Hilbert’s tenth problem for the ring of integers of the following
number fields K:

   • K is totally real or a quadratic extension of a totally real field [7, 6],

   • [K : $\mathbb{Q}$] = 4 and K is not totally real [7],

   • K has exactly one complex place [35, 42, 47],

   • K is contained in a number field L such that $\mathbb{Z}$ is Diophantine over $\mathcal{O}_L$ [41].

We also mention the recent works of Garcia-Fritz–Pasten [11], Kundu–Lei–Sprung [24] and
Shnidman–Weiss [44], who give a negative answer for a large number of sextic fields. There
are also related results on Diophantine stability in [28] and [39].

### 1.2 Our results <a id="12-our-results"></a>

After the completion of the MRDP theorem, elliptic curves became a particularly natural
candidate to replace the role of Pell’s equation. This was briefly suggested by Denef in [6]. A
rigorous connection was first established by Poonen [36] and independently by Cornelissen–
Pheidas–Zahidi [3]. These results were further strengthened by Shlapentokh [43] and Mazur–
Rubin–Shlapentokh [29].
    However, these results came with one major downside: unlike Pell’s equation, it is not easy
to show that there exists an elliptic curve of rank 1 over a given number field. In fact, only
after the release of our initial preprint, this was shown to be true independently by Zywina
[49] and the authors [23].
    However, assuming finiteness of the Tate–Shafarevich group, Mazur–Rubin [27] were able
to use the aforementioned results to show that Hilbert’s tenth problem is undecidable for any
infinite ring $R$ that is finitely generated over $\mathbb{Z}$. Further conditional results were obtained by
Murty–Pasten [32] and by Pasten [34]. We establish the same result unconditionally.

<a id="theorem-11"></a>
> **Theorem 1.1.** Let $R$ be a finitely generated ring over $\mathbb{Z}$ with |$R$| = ∞. Then Hilbert’s tenth
problem has a negative answer for $R$.

   We prove Theorem 1.1 by proving the following conjecture of Denef and Lipshitz [7].

<a id="theorem-12"></a>
> **Theorem 1.2.** Let K be a number field. Then $\mathbb{Z}$ is Diophantine over $\mathcal{O}_K$ .

    Eisenträger [10], building on earlier work of Shlapentokh, proved in her PhD thesis that
Theorem 1.2 implies Theorem 1.1, so it remains to establish Theorem 1.2.
    Approximately two months after the release of our initial preprint, Alpöge–Bhargava–Ho–
Shnidman [1] proved a rank growth result of similar strength as our Theorem 2.4. Their main
result recovers our Theorem 1.1 and Theorem 1.2.

<!-- [Original PDF Page 3] -->

### 1.3 Additive combinatorics <a id="13-additive-combinatorics"></a>

Our main new insight is to bring additive combinatorics into this field. For now, let L/K be
a quadratic extension. Our goal will be to construct an elliptic curve E over K with

<a id="equation-11"></a>
$$
rk E(L) = rk E(K) > 0. \tag{1.1}
$$

In fact, we may and will later assume quite a bit more about L/K to aid with some of the
technical arguments, see Theorem 2.4 for a precise statement.
     Mazur–Rubin [27] conditionally construct elliptic curves satisfying (1.1) by taking an elliptic curve E and quadratic twisting it to control the $2$-Selmer rank. In their work they take
an elliptic curve with Gal(K(E[2])/K) $\cong$ S3 as large as possible. Then they rely on finiteness
of Sha to go back to ranks.
     We instead perform $2$-descent on elliptic curves with full rational $2$-torsion. Let E be the
elliptic curve
                               y 2 = (x − a1 )(x − a2 )(x − a3 ).
Our first idea is to consider the twist by t := d(c − a1 d)(c − a2 d)(c − a3 d), so E t has the
equation
                               ty 2 = (x − a1 )(x − a2 )(x − a3 ),
which tautologically has the rational point (x, y) = (c/d, 1/d2 ). This point is readily seen to
be non-torsion for all but finitely many twists t and hence the rank of E t is positive. Thus, if
we were able to show that the $2$-Selmer rank of E t over L equals 2 + rk E(K), then we would
have unconditionally established equation (1.1). However, as the Selmer growth results in
Morgan–Paterson [31] suggest, this is typically not possible so we have opted to prove instead
                                                                   √
that the $2$-Selmer rank of E αt is 2, where α is such that L = K( α).
    Our second idea is to take advantage of additive combinatorics. Indeed, in general it is
exceptionally difficult to control Selmer ranks of polynomial twists; there are no distributional
results known outside linear polynomials. However, the change of Selmer ranks is well understood for prime elements. Hence we consider the situation that d, c − a1 d, c − a2 d and c − a3 d
are all prime elements. This is possible by recent work of Kai [19], which is a Green–Tao
type result for number fields based on the earlier works [13, 14, 15, 16]. In fact, we only
need an inverse theorem for the Gowers U 3 norm, which is technically simpler and established
previously in [12].

### 1.4 Layout of the paper <a id="14-layout-of-the-paper"></a>

In Section 2 we perform a standard reduction step to reduce the problem to establishing
equation (1.1) for certain quadratic extensions L/K. This reduction step allows one to assume
that K contains any given totally real field. We will use this flexibility merely to ensure that
K itself has at least 32 real places, which we will take advantage of in Section 5. Moreover,
unlike Mazur–Rubin [27] we reduce to the case where L/K is quadratic instead of cyclic. That
this suffices was first noticed by Shlapentokh, see [29, Theorem 4.8].
    The main result of Section 2 is that Theorem 2.4 implies Theorem 1.2. The remainder of
the paper is dedicated to establishing Theorem 2.4.
    In Section 3 we develop some background theory. We perform $2$-descent over general
number fields, and give several results to compute the parity of $2$-Selmer. Moreover, we

<!-- [Original PDF Page 4] -->

construct suitable “starting” elliptic curves that we shall twist in the later sections. We end
this section by giving a reasonable parametrization of H 1 (GK , $\mathbb{F}_2$ ).
    In Section 4 we define a transition process that computes the change in $2$-Selmer rank
of E κ to E κπ . Since this transition is rather delicate, we spend a great amount of time to
carefully control the $2$-Selmer rank of E κ in Section 5.
    After having suitably prepared our Selmer groups for our additive combinatorics arguments, we finish the argument in Section 5. At this stage a final obstacle arises as one can
not independently prescribe c − a1 d, c − a2 d, c − a3 d modulo d. To work around this issue, we
make use of infinite places to carefully control some terms arising from quadratic reciprocity.

## Acknowledgements <a id="acknowledgements"></a>

This project was initiated when the second author visited the first author at the Institute for
Theoretical Studies (ETH Zürich), and both authors wish to thank the institute for its financial
support and excellent working conditions. The first author gratefully acknowledges the support
of Dr. Max Rössler, the Walter Haefner Foundation and the ETH Zürich Foundation. The
first author also acknowledges the support of the Dutch Research Council (NWO) through
the Veni grant “New methods in arithmetic statistics”.
     The manuscript was completed while the authors were at the workshop Nilpotent counting
problems in arithmetic statistics at AIM. We are very grateful to AIM and the organizers
Brandon Alberts, Yuan Liu and Melanie Wood.
     The authors are deeply indebted to Efthymios Sofos, who answered many questions about
additive combinatorics during the project. Without his constant support, the project would
most likely not have come to be. We would also like to thank Gunther Cornelissen, Christopher
Frei, Ofer Gabber, Andrew Granville, Ben Green, Wataru Kai, Emmanuel Kowalski, Vivian
Kuperberg, Jeff Lagarias and Alexander Smith for helpful conversations. We are also indebted
to Hector Pasten for explaining us how to reduce Hilbert’s tenth problem to rank growth in
quadratic extensions instead of general cyclic extensions.
     We would like to thank Adam Morgan for valuable feedback on Section 3. Moreover, we
are most grateful to him for the shared time at the Max Planck Institute in Bonn, where he
explained to us how to control the $2$-Selmer group with the transition process from Section 4.
In particular, his excellent notes formed the basis of our Section 4.
     Finally, we would like to express our admiration for the dedication of the anonymous
referees. Their careful reading and their numerous suggestions have greatly improved this
manuscript. In particular, their suggestions have led to several simplifications of the original
arguments.

## 2 Initial reductions <a id="2-initial-reductions"></a>

In this section we reduce our main theorem to establishing a certain rank growth condition
of elliptic curves. This reduction is standard in the literature, see for example [27, Section 8].
We redo the arguments here as we are going to impose some extra conditions on the relevant
extensions of number fields that will ease some future arguments. We start by recalling three
well-known results.

<a id="lemma-21"></a>
> **Lemma 2.1.** Suppose K ⊆ L are number fields. Then:
    (i) If D1 , D2 ⊆ $\mathcal{O}_L$ are Diophantine over $\mathcal{O}_L$ , then so is D1 ∩ D2 .

<!-- [Original PDF Page 5] -->

 (ii) If D ⊆ $\mathcal{O}_K$ is Diophantine over $\mathcal{O}_K$ , and $\mathcal{O}_K$ is Diophantine over $\mathcal{O}_L$ , then D is Diophantine over $\mathcal{O}_L$ .

 (iii) If $\mathbb{Z}$ is Diophantine over $\mathcal{O}_L$ , then $\mathbb{Z}$ is Diophantine over $\mathcal{O}_K$ .

*Proof.* See [27, Lemma 8.3].

<a id="lemma-22"></a>
> **Lemma 2.2.** If M is a totally real number field, then $\mathbb{Z}$ is Diophantine over $\mathcal{O}_M$ .

*Proof.* This is the statement of [6, Theorem].

<a id="lemma-23"></a>
> **Lemma 2.3.** If L/K is an extension of number fields and if there exists an elliptic curve
E/K such that rk E(K) = rk E(L) > 0, then $\mathcal{O}_K$ is Diophantine over $\mathcal{O}_L$ .

*Proof.* See [43, Theorem 1.9].

   Having stated these results, we will now perform our reduction step. Let us first state the
theorem that we shall prove in the remaining sections of the paper.

<a id="theorem-24"></a>
> **Theorem 2.4.** Let K be a number field and set L := K(i). Assume that K has at least 32
real places. Then there exists an elliptic curve E over K such that rk E(K) = rk E(L) > 0.
   We shall prove Theorem 2.4 in Section 5. In order to prove that Theorem 2.4 implies
Theorem 1.2, we shall pass through the following intermediate result.

<a id="corollary-25"></a>
> **Corollary 2.5.** Let K be a number field and set L := K(i). Assume that
  (i) L is Galois over $\mathbb{Q}$,

 (ii) K has a real place,
                          √ √ √ √ √
 (iii) K contains K0 := $\mathbb{Q}$( 5, 7, 11, 13, 17).
Then there exists an elliptic curve E over K such that rk E(K) = rk E(L) > 0.

*Proof that Theorem 2.* 4 implies Corollary 2.5. Let K be a number field, set L := K(i) and
assume that conditions (i), (ii), (iii) hold.
   Write CG (S) for the centralizer of a subset S inside a group G. Fix an embedding σ :
K → $\mathbb{R}$ and extend it to σ1 : L → $\mathbb{C}$. We will start by proving that

<a id="equation-21"></a>
$$
{τ ∈ Gal(L/$\mathbb{Q}$) : σ1 (τ (K)) ⊆ $\mathbb{R}$} = CGal(L/$\mathbb{Q}$) (Gal(L/K)). \tag{2.1}
$$

Write ⟨ρ⟩ = Gal(L/K). Denoting complex conjugation by z 7→ z̄, we observe that σ1 ◦ ρ = σ1 .
Hence if τ ∈ CGal(L/$\mathbb{Q}$) (⟨ρ⟩), we have

                      σ1 (τ (α)) = σ1 (ρ(τ (α))) = σ1 (τ (ρ(α))) = σ1 (τ (α))

for all α ∈ K, so σ1 (τ (K)) ⊆ $\mathbb{R}$. Conversely, if σ1 (τ (K)) ⊆ $\mathbb{R}$, then

                      σ1 (ρ(τ (α))) = σ1 (τ (α)) = σ1 (τ (α)) = σ1 (τ (ρ(α)))

for all α ∈ K, hence [ρ, τ ] must fix K. This implies [ρ, τ ] ∈ Gal(L/K), therefore [ρ, τ ] is the
identity (as the alternative [ρ, τ ] = ρ forces ρ to be the identity, contradiction). This proves
equation (2.1).

<!-- [Original PDF Page 6] -->

   In order to apply Theorem 2.4, we need to show that K has at least 32 real places. Note
that there is a 2-to-1 surjective map from {τ ∈ Gal(L/$\mathbb{Q}$) : σ1 (τ (K)) ⊆ $\mathbb{R}$} to the set of real
embeddings of K. Therefore, by equation (2.1), the number of real embeddings of K is exactly
|CGal(L/$\mathbb{Q}$) (⟨ρ⟩)|/2. Let $C$ be the conjugacy class of ρ in Gal(L/$\mathbb{Q}$). Then every element of $C$
must map to the same element of Gal(K0 (i)/$\mathbb{Q}$), so |$C$| ≤ [L : $\mathbb{Q}$]/64. By the orbit–stabilizer
formula, |CGal(L/$\mathbb{Q}$) (⟨ρ⟩)| = |Gal(L/$\mathbb{Q}$)|/|$C$| ≥ 64.

    We shall now prove that Corollary 2.5 implies Theorem 1.2 (stated here again as Theorem
2.6). The remainder of this paper is dedicated to establishing Theorem 2.4.

<a id="theorem-26"></a>
> **Theorem 2.6.** Let F be a number field. Then $\mathbb{Z}$ is Diophantine over $\mathcal{O}_F$ .

*Proof that Corollary 2.* 5 implies Theorem 2.6. Let F be any number field. Define L to be the
compositum of the normal closure of F together with K0 (i). Let K be any field such that
L = K(i) and such that K has at least one real place. Then K must contain all totally real
subfields of L, hence contains K0 . We conclude that $\mathcal{O}_K$ is Diophantine over $\mathcal{O}_L$ by Lemma
2.3 and Corollary 2.5 applied to L/K.
    Take M to be the intersection of all K that satisfy L = K(i) and have at least one real
place. As we have just proven that $\mathcal{O}_K$ is Diophantine over $\mathcal{O}_L$ for all such K, then so is $\mathcal{O}_M$
by Lemma 2.1(i). Note that M is Galois over $\mathbb{Q}$, and since there exists a field K containing M
with at least one real place, M must be totally real. So $\mathbb{Z}$ is Diophantine over $\mathcal{O}_M$ by Lemma
2.2, and thus $\mathbb{Z}$ is Diophantine over $\mathcal{O}_L$ by Lemma 2.1(ii). This implies that $\mathbb{Z}$ is Diophantine
over $\mathcal{O}_F$ by Lemma 2.1(iii).

## 3 Background theory <a id="3-background-theory"></a>

### 3.1 Elliptic curves <a id="31-elliptic-curves"></a>

Given a field K and a1 , a2 , a3 ∈ K, we define

<a id="equation-31"></a>
$$
α := a1 − a2 ,     β := a1 − a3 ,      γ := a2 − a3 . \tag{3.1}
$$

Write (−, −)Weil : E[2] × E[2] → $\mu_2$ for the Weil pairing.

<a id="lemma-31"></a>
> **Lemma 3.1.** Let K be a field of characteristic 0. Let a1 , a2 , a3 ∈ K be distinct and let E be
the elliptic curve defined by

                               E : y 2 = (x − a1 )(x − a2 )(x − a3 ).

Let P1 = (a1 , 0) and P2 = (a2 , 0). Let λi be the homomorphism E[2] → $\mu_2$ given by P 7→
(P, Pi )Weil . Under the isomorphism (λ1 , λ2 ) : H 1 (GK , E[2]) ∼
                                                                  = (K ∗ /K ∗2 )2 , the Kummer map
δ : E(K)/2E(K) ,−   → H 1 (GK , E[2]) ∼
                                      = (K ∗ /K ∗2 )2 is given explicitly by

                                        (x − a1 , x − a2 ) if P ̸= P1 , P2
                                        
                                        
                         P = (x, y) 7→ (αβ, α)                if P = P1
                                                              if P = P2 .
                                        
                                         (−α, −αγ)
                                        

*Proof.* See [45, Proposition 1.4, Chapter 10].

<!-- [Original PDF Page 7] -->

     Throughout the paper we shall often implicitly identify H 1 (GK , E[2]) with (K ∗ /K ∗2 )2 ∼
                                                                                                =
H 1 (GK , $\mathbb{F}_2$ )2 . Whenever we do so, the implicit identification used is (λ1 , λ2 ).
     In order to show that the rational point that we will construct later is not torsion, the
following fact will be useful.

<a id="lemma-32"></a>
> **Lemma 3.2.** Let K be a number field and let E be an elliptic curve defined over K. For all
but finitely many d ∈ K ∗ /K ∗2 , we have

                                     E d (K)tors = E d (K)[2].

*Proof.* Recall that for each d ∈ K ∗ the map
                                                         √
                                       (x, y) 7→ (x,         d · y)

induces an injective group homomorphism ϕd : E d (K) → E(K). The image of ϕd consists√of
the zero element together with those points (x, y) ∈ E(K) satisfying x ∈ K and y ∈ K d.
Therefore, if we take d1 , d2 ∈ K ∗ with different classes in K ∗ /K ∗2 , we have that

                                 im(ϕd1 ) ∩ im(ϕd2 ) = E(K)[2].

Hence it suffices to show that

                                       [
                                                  im(ϕd )tors < ∞.
                                    d∈K ∗ /K ∗2

However, d∈K ∗ /K ∗2 im(ϕd )tors ⊆ E(K)tors is a subset of bounded height and degree, thus we
         S
conclude with Northcott’s theorem.
                                                                                         √

<a id="lemma-33"></a>
> **Lemma 3.3.** Let K be a number field, let d ∈ K ∗ /K ∗2 be non-trivial and set L := K( d).
Let E be an elliptic curve defined over K. Then

                                 rk E(L) = rk E(K) + rk E d (K).

*Proof.* This is a standard result, which follows from decomposing E(L) ⊗$\mathbb{Z}$ $\mathbb{Q}$ into its plus and
minus part under the action of Gal(L/K).

### 3.2 Root numbers <a id="32-root-numbers"></a>

The global root number w(E/K) is defined by
                                          Y
                              w(E/K) =      w(E/Kv ),
                                                     v

where w(E/Kv ) is the local root number. We shall not need the precise definition of this local
root number as our next theorem provides a convenient way to calculate it.

<a id="theorem-34"></a>
> **Theorem 3.4 (Root number facts).** Let E be an elliptic curve defined over a local field K of
characteristic 0. Let k be the residue field of K and let v be the associated normalized valuation
of K. Then we have:

  (i) If E/K has good reduction, then w(E/K) = +1.

<!-- [Original PDF Page 8] -->

 (ii) If E/K has additive, potentially good reduction and char(k) ≥ 5, then
                                                          v(∆)|k|
                                       w(E/K) = (−1)⌊       12
                                                                  ⌋
                                                                      .

 (iii) If K is archimedean, then w(E/K) = −1.

*Proof.* See [4, Theorem 2.3] or [8, Theorem 3.1]. These statements were originally proven in
Kobayashi [22] and Rohrlich [40].

    The relevance of these root number computations is that we can relate them to the parity
                                                              ∞                    n
of the $2$-Selmer rank by our next theorem. Recall that Sel2 (E/K) := limn Sel2 (E/K).
                                                                           −→
Define rk2 (E/K) to be the $\mathbb{Z}_2$ -corank of the 2∞ -Selmer group.

<a id="theorem-35"></a>
> **Theorem 3.5 (2-parity).** Let K be a number field and let E/K be an elliptic curve with
E(K)[2] ∼
        = $\mathbb{F}_2^2$ . We have
                             (−1)rk2 (E/K) = w(E/K).

*Proof.* This was originally proven in [9, Theorem 1.8] and generalized in [2, Theorem 1.4].

<a id="corollary-36"></a>
> **Corollary 3.6.** Let K be a number field and let E/K be an elliptic curve. Suppose that
E(K)[2] ∼
        = $\mathbb{F}_2^2$ . Then
                                        2
                           (−1)dimF2 Sel (E/K) = w(E/K).

*Proof.* In virtue of Theorem 3.5, it suffices to prove that dimF2 Sel2 (E/K) and rk2 (E/K) are
congruent modulo 2, which we do below. We start with the exact sequences

                     0 → E(K)/2E(K) → Sel2 (E/K) → X(E/K)[2] → 0
                               $\mathbb{Q}_2$       ∞
                   0 → E(K) ⊗$\mathbb{Z}$    → Sel2 (E/K) → X(E/K)[2∞ ] → 0.
                               $\mathbb{Z}_2$
Write X(E/K)div for the largest divisible subgroup of X(E/K). The second exact sequence
implies that rk2 (E/K) = rk E(K) + dimF2 X(E/K)div [2]. Recalling that E(K)[2] ∼
                                                                               = $\mathbb{F}_2^2$ by
assumption and taking dimensions in the first exact sequence above gives

      dimF2 Sel2 (E/K) = dimF2 E(K)[2] + rk E(K) + dimF2 X(E/K)[2]
                                                                   X(E/K)
                       = 2 + rk E(K) + dimF2 X(E/K)div [2] + dimF2           [2]
                                                                   X(E/K)div
                                               X(E/K)
                       = 2 + rk2 (E/K) + dimF2            [2].
                                               X(E/K)div

By [38, Corollary 12], the Poonen–Stoll class pairs trivially with itself. Then [38, Theorem 8,
1 implies 3] shows that dimF2 X(E/K)
                               X(E/K)
                                    div
                                        [2] is even, which immediately gives the corollary.

    Finally, we are ready to construct a starting curve that we will twist later. Since our
methods are fairly flexible, we shall not need to demand too much on our starting curve. Given
three distinct real numbers x1 , x2 , x3 , we define p(x1 , x2 , x3 ) to be the unique permutation
σ ∈ S3 such that
                                       xσ(1) < xσ(2) < xσ(3) .
Given a1 , a2 , a3 , we recall the notation α = a1 − a2 , β = a1 − a3 and γ = a2 − a3 .

<!-- [Original PDF Page 9] -->

<a id="lemma-37"></a>
> **Lemma 3.7.** Let K be a number field with at least 25 real embeddings. Then there exist
elements a1 , a2 , a3 ∈ $\mathcal{O}_K$ such that

  (a) −1, α, β, γ ∈ K ∗ are linearly independent in K ∗ /K ∗2 ;

  (b) there exist real embeddings σ1 , . . . , σ24 such that for every f ∈ S3 there are precisely four
      indices i satisfying
                                      p(σi (a1 ), σi (a2 ), σi (a3 )) = f ;

  (c) the elliptic curve
                                      E : y 2 = (x − a1 )(x − a2 )(x − a3 )
      satisfies w(E/K) = +1.

*Proof.* Fix some real embeddings σ1 , . . . , σ25 . There exist a′1 , a′2 , a′3 ∈ $\mathcal{O}_K$ satisfying (b) as $\mathcal{O}_K$
is naturally a lattice of full rank inside K ⊗$\mathbb{Z}$ $\mathbb{R}$ and thus meets every orthant.
    Let E
        e be the elliptic curve given by

                                  e : y 2 = (x − a′ )(x − a′ )(x − a′ ).
                                  E               1        2        3

Write N for the product of finite bad places of E.       e By the Mitsui prime ideal theorem (see
[30, Theorem, p. 35] or [18, Theorem 1.2.1] for a more modern version), there exists an odd
principal prime element π of good reduction that has the same sign as w(E/K)                e      at σ25 , is
positive at all other real places and satisfies π ≡ 1 mod 24N . Applying Hilbert reciprocity to
the symbol (π, −1), we see that |$\mathcal{O}_K$ /π| ≡ 1 mod 4 if w(E/K)      e      = +1 and |$\mathcal{O}_K$ /π| ≡ 3 mod 4
if w(E/K) = −1. We now take E := E , a1 := πa1 , a2 := πa′2 and a3 := πa′3 .
       e                                      e π         ′

     Because E  e has good reduction at the prime (π), the π-adic valuation of ∆ e equals zero by
                                                                                           E
[45, Proposition 5.1, Chapter 7]. Then a direct inspection of the formula for $\Delta_E$ shows that
the π-adic valuation of $\Delta_E$ equals 6. In particular, Theorem 3.4 gives that w(E/K(π) ) = −1.
Since E  e and E are isomorphic at all finite places of bad reduction for E  e and are also isomorphic
at all 2-adic and 3-adic places, it follows from Theorem 3.4 that w(E/K) = +1.
     Since a′1 , a′2 , a′3 satisfy (b) and since π is totally positive at σ1 , . . . , σ24 , it follows that
a1 , a2 , a3 also satisfy (b). Finally, (a) is in fact a consequence of (b).

### 3.3 Upper bounds for generator counts <a id="33-upper-bounds-for-generator-counts"></a>

We need the following analytic counting result.

<a id="lemma-38"></a>
> **Lemma 3.8.** Let K be a number field of degree n and let ω1 , . . . , ωn be an integral basis of
$\mathcal{O}_K$ . Then there is $C > 0$ such that for all integral ideals I ⊆ $\mathcal{O}_K$ and all B ≥ 10

      |{(a1 , . . . , an ) ∈ [−B, B]n ∩ Zn : a1 ω1 + · · · + an ωn generates I}| ≤ $C(\log B)$n−1 .
                                                       Pn

*Proof.* Each non-zero number α of the form                  i=1 ai ωi with ai ∈ [−B, B] ∩ $\mathbb{Z}$ has every
archimedean absolute value ≤ B         O(1) , and, by the product formula, ≥ B −O(1) . Now suppose
that α and β generate I. Let T be the torsion subgroup of $\mathcal{O}_K$             ∗ . Then the usual logarithmic

embedding $\mathcal{O}_K$ /T ,−
                 ∗        → $\mathbb{R}$ 1 2 sends the ratio β/α into a point with coordinates that are
                               r +r

O(log B), in a fixed lattice of rank r1 + r2 − 1 ≤ n − 1, so there are at most O((log B)n−1 )
such images, and the torsion subgroup T is of constant size.

<!-- [Original PDF Page 10] -->

## 4 Selmer ranks as transition processes <a id="4-selmer-ranks-as-transition-processes"></a>

Let K be a number field and let E/K be an elliptic curve with E(K)[2] ∼       = $\mathbb{F}_2^2$ . The central
result of this section is a description of $2$-Selmer ranks of quadratic twists of E in terms of a
transition process. We denote by $\Omega_K$ the set of places of K. Take T to be any finite subset
of $\Omega_K$ containing all 2-adic places of K, all infinite places of K, all places of bad reduction of
E and all places where α, β or γ has non-zero valuation; for the definition of α, β and γ, see
equation (3.1).
    To describe the Selmer rank as a transition process, we will introduce a sequence of Selmer
structures. Let A be a finite GK -module. For each v ∈ $\Omega_K$ , we fix an embedding GKv ,→ GK
and we write Iv for the inertia subgroup of GKv . The embedding GKv ,→ GK gives rise to a
natural restriction map resv : H 1 (GK , A) → H 1 (GKv , A). Define
                           1
                             (GKv , A) := ker H 1 (GKv , A) → H 1 (Iv , A) .
                                                                          
                         Hnr

A Selmer structure L = (Lv )v∈$\Omega_K$ (in the language of [33, Definition 8.7.8], this is called
a collection of local conditions) is a collection of subgroups Lv ⊆ H 1 (GKv , A) such that
             Kv , A) for all but finitely many v. To a Selmer structure L, we associate its
Lv = Hnr 1 (G

Selmer group via the formula
                                                                          
                                                    $\mathbb{Q}$           1
                                                               H (GKv , A) 
                                                      v resv
                                                             Y
                SelL (GK , A) := ker H 1 (GK , A) −−− −−→                   .
                                                                  Lv
                                                              v∈$\Omega_K$

Let n ∈ $\mathbb{Z}$≥0 and let v1 , . . . , vn be distinct places outside of T . For each 1 ≤ j ≤ n, let πj be
an element of Kv∗j /Kv∗2j with odd valuation (note that there are exactly two such choices) and
write π = (πj )1≤j≤n for the resulting vector. For each integer 0 ≤ i ≤ n, we define a Selmer
structure Li,π = (Li,π,v )v∈$\Omega_K$ by

                                                       if v ∈ T
                     
                     δ(E(Kv ))
                     

<a id="equation-41"></a>
$$
Li,π,v = ⟨(αβ, πj α), (−πj α, −αγ)⟩ if v = vj for some j ∈ {1, . . . , i} \tag{4.1}
$$

                                                       otherwise.
                     
                      1
                         Hnr (GKv , E[2])

We shall see in Lemma 4.2 that ⟨(αβ, πj α), (−πj α, −αγ)⟩ = δ(E πj (Kv )), which is the main
motivation for defining the second line of equation (4.1) as above.
   For 0 ≤ i ≤ n − 1, define

                  ni := dimF2 SelLi+1,π (GK , E[2]) − dimF2 SelLi,π (GK , E[2]).

In order to study ni , we introduce a second Selmer structure L′i,π = (L′i,π,v )v∈$\Omega_K$ through
                      
                      
                      
                      δ(E(Kv ))                 if v ∈ T
                      ⟨(αβ, π α), (−π α, −αγ)⟩ if v = v for some j ∈ {1, . . . , i}
                      
                               j         j                j
            L′i,π,v =
                      
                      
                      H 1 (G
                             Kv  , E[2])         if v = v i+1
                      H 1 (G , E[2])            otherwise
                      
                         nr   Kv

and

<a id="equation-42"></a>
$$
Avi+1 := resvi+1 SelL′i,π (GK , E[2]). \tag{4.2}
$$

<!-- [Original PDF Page 11] -->

As we shall now summarize, an important insight of Poonen–Rains [37] is that the local Tate
pairing naturally comes from a certain quadratic form qE,v : H 1 (GKv , E[2]) → Br(Kv )[2],
which was first constructed by Zarhin [48]. We will then use this theory to show that Avi+1 is
a maximal isotropic subspace (see Proposition 4.6).
    We start by recalling some basic properties of this construction. Let v ∈ $\Omega_K$ . Identifying
E[2] with its dual GKv -module through the Weil pairing, we see that local Tate duality induces
an alternating non-degenerate bilinear pairing

                     bE,v : H 1 (GKv , E[2]) × H 1 (GKv , E[2]) → Br(Kv )[2].

<a id="proposition-41"></a>
> **Proposition 4.1.** (a) For each place v of K, there exists a quadratic form

                               qE,v : H 1 (GKv , E[2]) → Br(Kv )[2]

inducing the pairing bE,v . Furthermore, δ(E(Kv )/2E(Kv )) is a maximal isotropic subspace of
the quadratic space (H 1 (GKv , E[2]), qE,v ).
    (b) There exists a quadratic form qE,K : H 1 (GK , E[2]) → Br(K)[2] satisfying

                                    resv ◦ qE,K = qE,v ◦ resv .

*Proof.* (a) The construction of the quadratic forms qE,v and qE,K can be found in [37, Section
4.1]. The fact that it induces bE,v is given in [37, Corollary 4.7], while the last part is [37,
Proposition 4.11].
    (b) The forms qE,K and qE,v in [37, Section 4.1] are constructed as connecting homomorphisms. Hence the desired claim follows from the fact that connecting homomorphisms
commute with restriction to subgroups.

   We will now use Proposition 4.1 to prove several important equalities between the local
conditions appearing in the definitions of Li,π and L′i,π .

<a id="lemma-42"></a>
> **Lemma 4.2.** Let v ∈ $\Omega_K$ .
  (a) If v is odd, then

              dimF2 H 1 (GKv , E[2]) = dimF2 H 1 (GKv , $\mathbb{F}_2^2$ ) = 2 dimF2 H 1 (GKv , $\mathbb{F}_2$ ) = 4.

      Moreover, the subgroup of Kv∗ /Kv∗2 corresponding to Hnr
                                                            1 (G
                                                                Kv , $\mathbb{F}_2$ ) via Kummer theory
          ∗    ∗2
      is OKv /OKv , and
                                 1
                          dimF2 Hnr                         1

<a id="equation-43"></a>
$$
(GKv , E[2]) = 2 dimF2 Hnr (GKv , $\mathbb{F}_2$ ) = 2. \tag{4.3}
$$

  (b) If v is odd and of good reduction for E, then
                                                     1
                                δ(E(Kv )/2E(Kv )) = Hnr (GKv , E[2]).

  (c) If v ̸∈ T and if π is a uniformizer for Kv , then

                           δ(E π (Kv )/2E π (Kv )) = ⟨(αβ, πα), (−πα, −αγ)⟩.

  (d) If v ̸∈ T and if π is a uniformizer for Kv , then
                                                      1
                            ⟨(αβ, πα), (−πα, −αγ)⟩ ∩ Hnr (GKv , E[2]) = 0.

<!-- [Original PDF Page 12] -->

  (e) If v is a real archimedean place, then dimF2 δ(E(Kv )/2E(Kv )) = 1 and moreover

                               δ(E(Kv )/2E(Kv )) = ⟨(αβ, α), (−α, −αγ)⟩.

*Proof.* The first half of part (a) is a consequence of the isomorphism E[2] ∼       = $\mathbb{F}_2^2$ and the
explicit description of Kv /Kv for local fields Kv . For the second half of part (a), we obtain
                          ∗   ∗2
  1 (G
Hnr              ∼ ∗
       Kv , $\mathbb{F}_2$ ) = OKv /OKv using Hensel’s lemma and that v is odd by assumption. Using
                          ∗2

again that v is odd, we conclude that dimF2 Hnr   1 (G
                                                      Kv , $\mathbb{F}_2$ ) = 1. Then equation (4.3) follows
from exploiting the isomorphism E[2] $\cong$ 2F 2 once more.  Part (b) follows from [37, Remark 4.12
and Proposition 4.13].
    As for part (c), we start by observing that δ(E π (Kv )/2E π (Kv )) is a maximal isotropic
subspace of qE π ,v by Proposition 4.1(a). Therefore it follows from part (a) that

                                 dimF2 δ(E π (Kv )/2E π (Kv )) = 2.

Inspecting valuations and using that v ̸∈ T , we see that dimF2 ⟨(αβ, πα), (−πα, −αγ)⟩ =
2. Since (αβ, πα) and (−πα, −αγ) are inside δ(E π (Kv )/2E π (Kv )) by Lemma 3.1, part (c)
follows. Part (d) is a direct consequence of inspecting valuations. Part (e) follows from Lemma
3.1 and the fact that E($\mathbb{R}$) ∼  = $\mathbb{R}$/$\mathbb{Z}$ ⊕ $\mathbb{Z}$/2Z for elliptic curves with full rational $2$-torsion.

   We now describe the initial state of the transition process, which is another important
motivation for the definition of Li,π .

<a id="lemma-43"></a>
> **Lemma 4.3.** We have
                                 SelL0,π (GK , E[2]) = Sel2 (E/K).

*Proof.* Unwind the definitions and then use Lemma 4.2(b) for v ̸∈ T .
                           ∗
   For v ∈ $\Omega_K$ and x ∈ KK∗2 v
                             , we have a natural isomorphism E x [2] → E[2] as GKv -modules.
                          v
Thus, after applying this natural identification, the quadratic forms qE x ,v and qE,v have the
same cohomology group as source. The following establishes that these forms actually coincide.
                                                                 ∗

<a id="proposition-44"></a>
> **Proposition 4.4 ([20, Lemma 5.2]).** Let v ∈ $\Omega_K$ and x ∈ KK∗2
                                                        v
                                                           . Then qE,v = qE x ,v .
                                                                v

                                                                                              ∗
    We will also use the following version of Poitou–Tate duality. We write M ∨ = Hom(M, K )
for the dual module, and we write L∨ for the dual Selmer structure.

<a id="theorem-45"></a>
> **Theorem 4.5 ([26, Theorem 2.3.4]).** Let L and F be Selmer structures such that Lv ⊆ Fv
for all v ∈ $\Omega_K$ . Let S be a finite set of places such that Lv = Fv for all v ̸∈ S. Then the
images of SelF (GK , M ) and SelL∨ (GK , M ∨ ) are orthogonal complements under the pairing
                              M              M
                                   Fv /Lv ×      L∨    ∨
                                                   v /Fv → $\mathbb{Q}$/$\mathbb{Z}$
                                 v∈S          v∈S

given by the sum of the local Tate pairings over S.

<a id="proposition-46"></a>
> **Proposition 4.6.** Let 0 ≤ i ≤ n − 1. Then Avi+1 is a maximal isotropic subspace of the
quadratic space (H 1 (GKvi+1 , E[2]), qE,vi+1 ).

<!-- [Original PDF Page 13] -->

*Proof.* We apply Theorem 4.5 with F := L′i,π and L := (Lv )v∈$\Omega_K$ given by
                                    (
                                     L′i,π,v if v ̸= vi+1 ,
                              Lv :=
                                     0        if v = vi+1 .

Note that L∨ = F: this follows from Proposition 4.1(a) for all v different from vi+1 and holds
by construction at v = vi+1 . Then Theorem 4.5 gives that Avi+1 equals its own orthogonal
complement under bE,vi+1 .
   It now suffices to show that qE,vi+1 vanishes on Avi+1 . We claim that

<a id="equation-44"></a>
$$
qE,v (L′i,π,v ) = 0 \tag{4.4}
$$

for all v ∈ $\Omega_K$ − {vi+1 }. If v ∈ T , this follows from the definition of L′i,π,v and Proposition
4.1(a). If v ̸∈ T ∪ {v1 , . . . , vi+1 }, then the claim follows once more by the definition of L′i,π,v ,
Lemma 4.2(b) and Proposition 4.1(a). For v ∈ {v1 , . . . , vi }, Lemma 4.2(c) gives
                                                       πi         
                                            ′           E (Kv )
                                           Li,π,v = δ                .
                                                       2E πi (Kv )
Therefore the desired conclusion follows immediately from Proposition 4.1(a) (applied to the
quadratic twist E πi ) and Proposition 4.4. We have now proven the claim (4.4).
   Let c ∈ SelL′i,π (GK , E[2]). Invoking Proposition 4.1(b) and equation (4.4), we conclude
that qE,K (c) is an element of Br(K)[2] that restricts trivially at all v different from vi+1 .
Therefore Hilbert reciprocity shows that qE,K (c) restricts trivially also at vi+1 . Applying once
more Proposition 4.1(b), we conclude that qE,vi+1 (resvi+1 (c)) = 0, as desired.

    We deduce from Lemma 4.2(a) and Proposition 4.6 that

<a id="equation-45"></a>
$$
dimF2 Avi+1 = 2. \tag{4.5}
$$

The additional quadratic structure was heavily used in the work of Klagsbrun–Mazur–Rubin
[20, 21]. The following key fact follows also from [21, Proposition 7.2(iii)], but we opt for a
self-contained proof for the reader’s convenience.

<a id="lemma-47"></a>
> **Lemma 4.7.** Let 0 ≤ i ≤ n − 1. Then we have

                  if dimF2 resvi+1 (SelLi,π (GK , E[2])) = 0 and Avi+1 = Li+1,π,vi+1
           
           2
           
      ni = −2 if dimF2 resvi+1 (SelLi,π (GK , E[2])) = 2
                  otherwise.
           
            0
           

*Proof.* Write resvi+1 for the composition of resvi+1 with the natural quotient map going from
H 1 (GKvi+1 , E[2]) to H 1 (GKvi+1 , E[2])/Li+1,π,vi+1 . Let us start by recording the observation
                                                                        1
                                                                                        !
                                                              resvi+1 H (GKvi+1 , E[2])

<a id="equation-46"></a>
$$
SelLi+1,π (GK , E[2]) = ker SelL′i,π (GK , E[2]) −−−−→ \tag{4.6}
$$

                                                                          Li+1,π,vi+1

that we will use repeatedly.
   Recalling that Avi+1 = resvi+1 SelL′i,π (GK , E[2]) by definition (see (4.2)), we also record the
observations

                    resvi+1 (SelLi,π (GK , E[2]))              1

<a id="equation-47"></a>
$$
= Avi+1 ∩ Hnr (GKvi+1 , E[2]) \tag{4.7}
$$

<!-- [Original PDF Page 14] -->

<a id="equation-48"></a>
$$
resvi+1 (SelLi+1,π (GK , E[2])) = Avi+1 ∩ Li+1,π,vi+1 , \tag{4.8}
$$

which follow directly from unwinding the definitions of the various Selmer structures.
   By first using equation (4.7) and then equation (4.5), we obtain

                      dimF2 resvi+1 (SelLi,π (GK , E[2])) ≤ dimF2 Avi+1 = 2.

We now examine the three possible cases for the value of this dimension. Suppose first that

<a id="equation-49"></a>
$$
dimF2 resvi+1 (SelLi,π (GK , E[2])) = 2. \tag{4.9}
$$

Since dimF2 Hnr1 (G
                   Kvi+1 , E[2]) = 2 = dimF2 Avi+1 by the second part of Lemma 4.2(a) and
equation (4.5), equation (4.9) and equation (4.7) imply the equalities

                    resvi+1 (SelLi,π (GK , E[2])) = Avi+1 = Hnr
                                                             1

<a id="equation-410"></a>
$$
(GKvi+1 , E[2]). \tag{4.10}
$$

In particular, the first equality in (4.10) combined with the definition (4.2) implies the equality
SelLi,π (GK , E[2]) = SelL′i,π (GK , E[2]). Therefore equation (4.6) yields

                                                                   H 1 (GKvi+1 , E[2])
                                                                                         !
                                                         resvi+1

<a id="equation-411"></a>
$$
SelLi+1,π (GK , E[2]) = ker SelLi,π (GK , E[2]) −−−−→                                 . \tag{4.11}
$$

                                                                      Li+1,π,vi+1

Moreover, by equation (4.10), the image of SelLi,π (GK , E[2]) under resvi+1 is

                                         Li+1,π,vi+1 Avi+1
                                                           .
                                           Li+1,π,vi+1

Since Li+1,π,vi+1 intersects Hnr
                               1 (G
                                   Kvi+1 , E[2]) trivially by Lemma 4.2(d) and since we have
Avi+1 = Hnr (GKvi+1 , E[2]) by equation (4.10), it follows from equation (4.5) that ni = −2.
          1

   Suppose now that

<a id="equation-412"></a>
$$
dimF2 resvi+1 (SelLi,π (GK , E[2])) = 0. \tag{4.12}
$$

We will distinguish two further cases, namely Avi+1 = Li+1,π,vi+1 or Avi+1 ̸= Li+1,π,vi+1 .
   Suppose that Avi+1 = Li+1,π,vi+1 . Then equation (4.6) shows that

<a id="equation-413"></a>
$$
SelLi+1,π (GK , E[2]) = SelL′i,π (GK , E[2]). \tag{4.13}
$$

Since Avi+1 = Li+1,π,vi+1 intersects Hnr 1 (G
                                             Kvi+1 , E[2]) trivially by Lemma 4.2(d), we deduce
from equation (4.7) that SelLi,π (GK , E[2]) equals the subspace of SelL′i,π (GK , E[2]) that restricts trivially at vi+1 . Hence we have ni = 2 by equations (4.5) and (4.13).
    Now suppose that Avi+1 ̸= Li+1,π,vi+1 . We have
                                         1

<a id="equation-414"></a>
$$
Avi+1 ∩ Hnr (GKvi+1 , E[2]) = {0} \tag{4.14}
$$

by equations (4.7) and (4.12). Observe that Li+1,π,vi+1 intersects Hnr1 (G
                                                                          Kvi+1 , E[2]) trivially
by Lemma 4.2(d), and observe moreover that Avi+1 , Li+1,π,vi+1 and Hnr (GKvi+1 , E[2]) are all
                                                                        1

maximal isotropic subspaces of H 1 (GKvi+1 , E[2]) (for Avi+1 , see Proposition 4.6, while the
other two spaces are of the shape δ(E x (Kv )/2E x (Kv )) for some quadratic twist E x of E

<!-- [Original PDF Page 15] -->

by Lemma 4.2 and are thus maximal isotropic by Proposition 4.1(a) and Proposition 4.4).
Combining this with equation (4.14), we see that [20, Proposition 2.4] yields

                              dimF2 Avi+1 ∩ Li+1,π,vi+1 ≡ 0 mod 2.

However, the left hand side is strictly smaller than 2 since Avi+1 ̸= Li+1,π,vi+1 by assumption
(and both spaces are 2-dimensional). Therefore the left hand side has to be equal to 0, i.e.

<a id="equation-415"></a>
$$
Avi+1 ∩ Li+1,π,vi+1 = {0}. \tag{4.15}
$$

We conclude that
                                               resvi+1                  
 SelLi,π (GK , E[2]) = ker SelL′i,π (GK , E[2]) −−−−→ H 1 (GKvi+1 , E[2]) = SelLi+1,π (GK , E[2]),

where the first equality follows from equations (4.14) and (4.7) and the second equality follows
from equations (4.15) and (4.8). In particular, we have ni = 0 as desired.
   It remains to consider the case

                              dimF2 resvi+1 (SelLi,π (GK , E[2])) = 1.

By equation (4.7), this may be rephrased as
                                             1

<a id="equation-416"></a>
$$
dimF2 Avi+1 ∩ Hnr (GKvi+1 , E[2]) = 1. \tag{4.16}
$$

Recall that Li+1,π,vi+1 intersects Hnr
                                    1 (G
                                        Kvi+1 , E[2]) trivially by Lemma 4.2(d). Combining this
with equation (4.16), we obtain from [20, Proposition 2.4] the congruence

                              dimF2 Avi+1 ∩ Li+1,π,vi+1 ≡ 1 mod 2.

Therefore the above dimension must be exactly equal to 1. Thus, SelLi+1,π (GK , E[2]) equals
the inverse image of the 1-dimensional space Avi+1 ∩ Li+1,π,vi+1 under the map

                               resvi+1 : SelL′i,π (GK , E[2]) ↠ Avi+1 .

At the same time SelLi,π (GK , E[2]) equals the inverse image of Avi+1 ∩ Hnr   1 (G
                                                                                    Kvi+1 , E[2]) under the same map, which is also 1-dimensional by equation (4.16). Hence the two spaces
SelLi,π (GK , E[2]) and SelLi+1,π (GK , E[2]) are both subspaces in SelL′i,π (GK , E[2]) of codimension 1 and hence they must have the same dimension. We conclude that ni = 0, as desired.

<a id="remark-48"></a>
> **Remark 4.8.** In some of our applications, it will be important to strengthen the conclusion
of Lemma 4.7 as follows:

  (a) the condition Avi+1 = Li+1,π,vi+1 implies dimF2 resvi+1 (SelLi,π (GK , E[2])) = 0. Indeed,
      this follows from the fact that resvi+1 (SelLi,π (GK , E[2])) is exactly
                          1                                   1
                 Avi+1 ∩ Hnr (GKvi+1 , E[2]) = Li+1,π,vi+1 ∩ Hnr (GKvi+1 , E[2]) = {0}

      by Lemma 4.2(d);

  (b) ni = −2 implies that SelLi+1,π (GK , E[2]) ⊆ SelLi,π (GK , E[2]) is a subspace of codimension 2 (indeed, combine ni = −2 with equation (4.11));

<!-- [Original PDF Page 16] -->

    (c) since resvi+1 (SelLi,π (GK , E[2])) ⊆ Hnr
                                               1 (G
                                                   Kvi+1 , E[2]) by definition and since moreover
                 1
        dimF2 Hnr (GKvi+1 , E[2]) = 2 by the second part of Lemma 4.2(a), the condition

                                   dimF2 resvi+1 (SelLi,π (GK , E[2])) = 2

        is equivalent to the existence of two linearly independent elements inside the restriction
        resvi+1 (SelLi,π (GK , E[2])).
   The final step in the transition process is completely predictable because of the $2$-torsion
elements of E.

<a id="lemma-49"></a>
> **Lemma 4.9.** Let d ∈ K ∗ /K ∗2 . Assume that

                                       d ∈ Kv∗2     for all v ∈ T.                               (4.17)

Let v1 , . . . , vr be the set of places v ∈ $\Omega_K$ such that v(d) is odd; note that v1 , . . . , vr ̸∈ T by
(4.17). We assume that r ≥ 1. Then we have

                     dimF2 Sel2 (E d /K) = 2 + dimF2 SelLr−1,(d,...,d) (GK , E[2]).

*Proof.* We define the Selmer structure Ld = (Ld,v )v∈$\Omega_K$ by

                                          Ld,v := δ(E d (Kv )).

Recall that Sel2 (E d /K) = SelLd (GK , E[2]) by definition. We remark that

                                                           if v ∈ T
                              
                              δ(E(Kv ))
                              
                     d

<a id="equation-418"></a>
$$
Ld,v = δ(E (Kv )) = ⟨(αβ, dα), (−dα, −αγ)⟩ if v ∈ {v1 , . . . , vr } \tag{4.18}
$$

                                                           if v ̸∈ T ∪ {v1 , . . . , vr }.
                              
                               1
                                Hnr (GKv , E[2])

The first row follows from the isomorphism E ∼  = E d locally at Kv , which is a consequence of
our assumption (4.17). The second and third row follow from respectively Lemma 4.2(c) and

<a id="lemma-42(b)"></a>
> **Lemma 4.2(b).** 
    Set π := (d, . . . , d). By comparing equation (4.1) with equation (4.18), it follows that
Ld,v = Lr,π,v for all v ∈ $\Omega_K$ . Therefore we certainly have

                                  Sel2 (E d /K) = SelLr,π (GK , E[2]),

so it suffices to show that nr−1 = 2.
    We know that Avr has dimension 2 by equation (4.5). However, it also contains (the
restrictions of) (αβ, dα) and (−dα, −αγ) as these are in Sel2 (E d /K) by Lemma 3.1 and hence
in SelLr,π (GK , E[2]). Since r ≥ 1, it follows that resvr (αβ, dα) and resvr (−dα, −αγ) are
linearly independent by inspecting valuations at vr (recall that vr ̸∈ T by (4.17)). Therefore
Avr is equal to the span of (αβ, dα) and (−dα, −αγ), which is Lr,π,vr . Thus we obtain the
equality nr−1 = 2 from Remark 4.8(a) and Lemma 4.7, as desired.

## 5 Proof of Theorem 2.4 <a id="5-proof-of-theorem-2.4"></a>

In this section we combine the material from Section 3 and 4 to prove Theorem 2.4. For the
remainder of the paper, we fix a number field K satisfying the conditions of Theorem 2.4, so
K has at least 32 real places and we set L := K(i).

<!-- [Original PDF Page 17] -->

### 5.1 First steps <a id="51-first-steps"></a>

Let a1 , a2 , a3 , E, σ1 , . . . , σ24 be as in Lemma 3.7. Let α, β, γ be as in equation (3.1). We
will twist E. Define

                T := {v ∈ $\Omega_K$ : v | 6$\Delta_E$ ∞ or v(α) ̸= 0 or v(β) ̸= 0 or v(γ) ̸= 0}.

In the next two subsections, we will find t ∈ K ∗ /K ∗2 satisfying

<a id="equation-51"></a>
$$
dimF2 Sel2 (E t /K) = 2,               rk E −t (K) > 0. \tag{5.1}
$$

Because E t has full rational $2$-torsion, we have the inequality

                                  rk E t (K) + 2 ≤ dimF2 Sel2 (E t /K).

Hence it follows from the first part of equation (5.1) that rk E t (K) = 0. Combining this with
the second part of equation (5.1) and Lemma 3.3 (applied to E −t and d = −1) we deduce
that rk E −t (K) = rk E −t (L) > 0. Hence Theorem 2.4 holds with E −t being our witness.
   We will establish (5.1) with two reduction steps. The first reduction step gives sufficient
conditions on t (see Definition 5.1) to ensure that

                                            dimF2 Sel2 (E t /K) = 2.

The second reduction step finds sufficient conditions on κ (see Definition 5.3 for a precise
statement) that will allow us to construct t through additive combinatorics. Specifically, t will
take the shape
                                        t = κq1 q2 q3 q3 q4 ,
where κ is an auxiliary twist to arrange the Selmer group favorably, and q1 , q2 , q3 , q4 are
constructed through additive combinatorics to ensure that equation (5.1) holds. Finally, we
finish the proof by showing that an auxiliary twist κ exists.

<a id="definition-51"></a>
> **Definition 5.1.** We say that an element t ∈ K ∗ /K ∗2 is a suitable twist if there exists κ ∈
K ∗ /K ∗2 and prime elements q1 , q2 , q3 , q4 such that, denoting by p1 , . . . , ps the primes where
κ has odd valuation and putting T ′ := T ∪ {p1 , . . . , ps }, then

(P 1) t ∈ Kv∗2 for all places v ∈ T ;

(P 2) we have t = κq1 q2 q3 q4 and the elements q1 , q2 , q3 , q4 are pairwise coprime and also
      coprime to T ′ ;

(P 3) there exists a basis

                            (z1 , z2 ), (z3 , z4 ), (z5 , z6 ), (z7 , z8 ), (z9 , z10 ), (z11 , z12 )

      of SelLs,(t,...,t) (GK , E[2]) such that
                              Y                       Y
                                      (z1 , q1 )v =           (z4 , q1 )v = −1
                              v∈T ′                   v∈T ′
                              Y                       Y
                                      (z5 , q2 )v =           (z8 , q2 )v = −1
                              v∈T ′                   v∈T ′

<!-- [Original PDF Page 18] -->

                                  Y                      Y
                                         (z9 , q3 )v =           (z12 , q3 )v = −1
                                 v∈T ′                   v∈T ′
                                  Y
                                         (zi , q1 )v = 1         for i ∈ {1, . . . , 12} − {1, 4}
                                 v∈T ′
                                  Y
                                         (zi , q2 )v = 1         for i ∈ {5, . . . , 12} − {5, 8}
                                 v∈T ′
                                  Y
                                         (zi , q3 )v = 1         for i ∈ {9, . . . , 12} − {9, 12};
                                 v∈T ′

(P 4) we have rk E −t (K) > 0.

    Property (P 3) serves two distinct roles. Firstly, we will use this property to understand
how q1 , q2 , q3 behave in the transition process from Lemma 4.7. In fact, we will show that the
dimension drops by 2 in each case. Secondly, (P 3) imposes merely congruences on q1 , q2 , q3
modulo T ′ . This is very convenient, as Theorem A.7 does allow us to prescribe such congruence
conditions, but does not allow for control on mutual Legendre symbols (qi /qj ). Condition
(P 3) carefully sets up a situation where we can understand the change of Selmer rank without
having knowledge of these Legendre symbols.

<a id="theorem-52"></a>
> **Theorem 5.2.** Let t ∈ K ∗ /K ∗2 be suitable. Then t satisfies equation (5.1).

*Proof.* Because t is suitable, (P 4) holds. This is exactly the second part of equation (5.1),
and thus we need to show that

<a id="equation-52"></a>
$$
dimF2 Sel2 (E t /K) = 2. \tag{5.2}
$$

By (P 1) and (P 2), we have that

              {v ∈ $\Omega_K$ : v finite, v(t) ≡ 1 mod 2} = {p1 , . . . , ps , (q1 ), (q2 ), (q3 ), (q4 )}.

We claim that

<a id="equation-53"></a>
$$
SelLs+1,(t,...,t) (GK , E[2]) = ⟨(z5 , z6 ), (z7 , z8 ), (z9 , z10 ), (z11 , z12 )⟩. \tag{5.3}
$$

To this end, we apply Hilbert reciprocity to obtain the relations
                                       Y
                                           (zi , q1 )v = 1
                                                   v∈$\Omega_K$

for all i ∈ {1, . . . , 12}. Using that v(zi ) is even for all v ̸∈ T ′ , we deduce that (zi , q1 )v = 1 for
all v ̸∈ T ′ ∪ {(q1 )}. Therefore (P 3) reveals the identity
                                                      (
                                                       −1 if i ∈ {1, 4}

<a id="equation-54"></a>
$$
(zi , q1 )(q1 ) = \tag{5.4}
$$

                                                       1   otherwise.

Now note that (zi , q1 )(q1 ) detects precisely whether res(q1 ) (zi ) is the trivial class or the unique
non-trivial unramified class ϵ. Combining this with equation (5.4) we conclude that

<a id="equation-55"></a>
$$
res(q1 ) ((z1 , z2 )) = (ϵ, 1),   res(q1 ) ((z3 , z4 )) = (1, ϵ),         res(q1 ) ((z2i+1 , z2i+2 )) = (1, 1) \tag{5.5}
$$

<!-- [Original PDF Page 19] -->

for all i ∈ {2, 3, 4, 5}. Hence Lemma 4.7 implies that ns = −2. Moreover, from equation (5.5),
we visibly have that (z5 , z6 ), (z7 , z8 ), (z9 , z10 ) and (z11 , z12 ) are in SelLs+1,(t,...,t) (GK , E[2]).
Since these elements are linearly independent, we deduce equation (5.3).
    Proceeding in this way, one successively shows that

                            SelLs+2,(t,...,t) (GK , E[2]) = ⟨(z9 , z10 ), (z11 , z12 )⟩

and that

<a id="equation-56"></a>
$$
dimF2 SelLs+3,(t,...,t) (GK , E[2]) = 0 \tag{5.6}
$$

for all suitable t.
    Note that equation (4.17) holds thanks to our assumption (P 1). Therefore the hypotheses
of Lemma 4.9 are satisfied (note that the condition r ≥ 1 is clearly satisfied in our case). Then
equation (5.2) is an immediate consequence of equation (5.6) and Lemma 4.9.

    Thanks to Theorem 5.2, it remains to establish the existence of a suitable t.

### 5.2 Application of additive combinatorics <a id="52-application-of-additive-combinatorics"></a>

We will now construct a suitable t in two steps. First, we shall assume that a certain auxiliary
twist κ has certain good properties. Under this assumption, we will apply Kai’s work [19] to
find such t. The construction of κ is delicate and relies on the material in Section 4 in an
essential way. This construction will occupy the entirety of Subsection 5.3.
    By the second part of Lemma 3.7, we fix six infinite places τ1 , . . . , τ6 of K among σ1 , . . . , σ24
with

<a id="equation-57"></a>
$$
τ1 (a2 ) < τ1 (a1 ) < τ1 (a3 ),          τ2 (a1 ) < τ2 (a2 ) < τ2 (a3 ) \tag{5.7}
$$

<a id="equation-58"></a>
$$
τ3 (a2 ) < τ3 (a3 ) < τ3 (a1 ),          τ4 (a1 ) < τ4 (a3 ) < τ4 (a2 ) \tag{5.8}
$$

<a id="equation-59"></a>
$$
τ5 (a2 ) < τ5 (a1 ) < τ5 (a3 ),          τ6 (a1 ) < τ6 (a2 ) < τ6 (a3 ). \tag{5.9}
$$

For the reader’s convenience, we have added the image δ(E(Kτj )) of the local Kummer map,
computed via Lemma 4.2(e), at each real place τj in the second row of the table (5.10); more
precisely, we have recorded the signs of the unique non-trivial element.

<a id="definition-53"></a>
> **Definition 5.3.** We say that κ ∈ K ∗ /K ∗2 is an auxiliary twist if

(K1) κ has even valuation at all finite places in T , is negative at τ4 , τ5 , τ6 , and is positive at
     τ1 , τ2 , τ3 ;

(K2) writing p1 , . . . , ps for the primes where κ has odd valuation, there exists π = (πi )1≤i≤s ,
     with each πi a uniformizer for Kpi , such that SelLs,π (GK , E[2]) has a basis

                             (z1 , z2 ), (z3 , z4 ), (z5 , z6 ), (z7 , z8 ), (z9 , z10 ), (z11 , z12 )

<!-- [Original PDF Page 20] -->

      such that the signs of zi at τ1 , . . . , τ6 are given by the table
| | $\tau_1$ | $\tau_2$ | $\tau_3$ | $\tau_4$ | $\tau_5$ | $\tau_6$ |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| **$\mathrm{im}(\delta)$** | $(-, +)$ | $(+, -)$ | $(-, +)$ | $(+, -)$ | $(-, +)$ | $(+, -)$ |
| $z_1$ | $-$ | $+$ | $+$ | $+$ | $+$ | $+$ |
| $z_2$ | $+$ | $+$ | $+$ | $+$ | $+$ | $+$ |
| $z_3$ | $+$ | $+$ | $+$ | $+$ | $+$ | $+$ |
| $z_4$ | $+$ | $-$ | $+$ | $+$ | $+$ | $+$ |
| $z_5$ | $+$ | $+$ | $-$ | $+$ | $+$ | $+$ |
| $z_6$ | $+$ | $+$ | $+$ | $+$ | $+$ | $+$ |
| $z_7$ | $+$ | $+$ | $+$ | $+$ | $+$ | $+$ |
| $z_8$ | $+$ | $+$ | $+$ | $-$ | $+$ | $+$ |
| $z_9$ | $+$ | $+$ | $+$ | $+$ | $-$ | $+$ |
| $z_{10}$ | $+$ | $+$ | $+$ | $+$ | $+$ | $+$ |
| $z_{11}$ | $+$ | $+$ | $+$ | $+$ | $+$ | $+$ |
| $z_{12}$ | $+$ | $+$ | $+$ | $+$ | $+$ | $-$ |

*(5.10)*
One may check that the pair (z2i+1 , z2i+2 ) satisfies the Selmer conditions at each τj .
    We will now give some motivation for (K2). Write N for the product of all odd prime
ideals in T . In order to construct suitable t, we shall soon choose the primes q1 , q2 , q3 in such
a way that
                                q1 ≡ q2 ≡ q3 ≡ 1 mod 8N p1 · · · ps
and that q1 , q2 , q3 are positive at all real places except {τ1 , . . . , τ6 }. Then the sum over v ∈ T ′
in (P 3) will simplify to a sum over just v ∈ {τ1 , . . . , τ6 }. With the further sign choices we
shall make for q1 , q2 , q3 at τ1 , . . . , τ6 in (5.13), we will see that the table (5.10) is constructed
exactly to give back (P 3).
    We are now ready to phrase our last reduction step, after which it remains to construct
an auxiliary twist κ in Subsection 5.3.

<a id="theorem-54"></a>
> **Theorem 5.4.** Assume that there exists an auxiliary twist κ. Then there exists a suitable
t ∈ K ∗ /K ∗2 .

*Proof.* We will proceed in four steps, aiming to eventually apply Theorem A.7. In our first step,
we construct four affine linear polynomials L1 , L2 , L3 , L4 . In the second step, we construct a
convex region Ω ⊆ R2n . In the third step we estimate the volume of Ω ∩ [−H, H]2n . Finally,
we apply Theorem A.7 and verify the properties (P 1), (P 2), (P 3) and (P 4) in the fourth step.

#### Construction of affine linear polynomials

Fix an auxiliary twist κ. Then, by (K1) and strong approximation, there exists an integral
representative of κ coprime to 8N . We also fix such an integral representative, which by abuse
of notation we also denote by κ.
    Writing h for the class number of K, we let m be a generator of the ideal 8N h . Write
λ ∈ $\mathcal{O}_K$ for an element coprime to κ and the finite places in T such that λ reduces to the
inverse of κ modulo 8N and satisfies respi (λκ) = πi for all 1 ≤ i ≤ s. We define affine linear
polynomials L1 , L2 , L3 , L4 ∈ $\mathcal{O}_K$ [X, Y ] by

                           L1 (X, Y ) := m2 κX + a1 m2 κ(m2 κY + λ) + 1

<!-- [Original PDF Page 21] -->

                             L2 (X, Y ) := m2 κX + a2 m2 κ(m2 κY + λ) + 1
                             L3 (X, Y ) := m2 κX + a3 m2 κ(m2 κY + λ) + 1
                             L4 (X, Y ) := m2 κY + λ.

Since the ai are distinct, it follows immediately that the Li (X, Y ) are pairwise K-linearly
independent.
    We identify $\mathcal{O}_K$ with the group Zn to reinterpret the Li as linear polynomials Z2n → $\mathcal{O}_K$ .
In order to show that the main term in Theorem A.7 dominates, we need to check that the
p-adic densities βpOK (L1 , L2 , L3 , L4 ) there do not vanish. We will do this now.

<a id="lemma-55"></a>
> **Lemma 5.5.** For every prime p of $\mathcal{O}_K$ , there exist u, v ∈ $\mathcal{O}_K$ such that

                              L1 (u, v)L2 (u, v)L3 (u, v)L4 (u, v) ̸≡ 0 mod p.

*Proof.* For primes p dividing mκ, we may pick u = v = 0. It remains to verify the lemma for
primes p ∤ mκ. In particular, p ∤ 6, so the residue field $\mathcal{O}_K$ /p is $\mathbb{F}_q$ for some q ≥ 5. Since m2 κ
is a unit in $\mathbb{F}_q$ , each Li cuts out a line in $\mathbb{F}_q$ × $\mathbb{F}_q$ , leaving at least q 2 − 4q > 0 possibilities for
(u, v) mod p.

#### Construction of a convex region

We will now construct a convex set Ω to which we apply Theorem A.7. We define Ω ⊆ R2n
through the simultaneous conditions:

  (I) for all real embeddings τ of K not equal to τ1 , . . . , τ6 and all k ∈ {1, 2, 3}

<a id="equation-511"></a>
$$
τ (Lk (X, Y )) > 0. \tag{5.11}
$$

       Here we note that τ ◦ Lk is an affine $\mathbb{Z}$-linear map Z2n → $\mathbb{R}$, which extends uniquely to
       an affine $\mathbb{R}$-linear map R2n → $\mathbb{R}$. From now on we shall frequently extend linear maps
       Z2n → $\mathbb{R}$ uniquely to R2n → $\mathbb{R}$ without further mention;

 (II) for all real embeddings τ of K not equal to τ1 , . . . , τ6

<a id="equation-512"></a>
$$
τ (L4 (X, Y )) τ (κ) > 0; \tag{5.12}
$$

(III) for j ∈ {1, . . . , 6} and k ∈ {1, 2, 3}, the sign of τj (Lk (X, Y )) is precisely the entry (k, j)
      in the table
| | $\tau_1$ | $\tau_2$ | $\tau_3$ | $\tau_4$ | $\tau_5$ | $\tau_6$ |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| $L_1(X, Y)$ | $-$ | $-$ | $+$ | $+$ | $+$ | $+$ |
| $L_2(X, Y)$ | $-$ | $-$ | $-$ | $-$ | $+$ | $+$ |
| $L_3(X, Y)$ | $+$ | $+$ | $-$ | $+$ | $-$ | $-$ |

*(5.13)*
(IV ) for all j ∈ {1, . . . , 6}
                                               τj (L4 (X, Y )) > 0.

<!-- [Original PDF Page 22] -->

#### Volume computation

In order to show that the main term in Theorem A.7 dominates, we also need to asymptotically
estimate the volume of Ω ∩ [−H, H]2n . We start with a general lemma on volumes. Write µ
for the Lebesgue measure.

<a id="lemma-56"></a>
> **Lemma 5.6.** Let ℓ ≥ k ≥ 1 be integers, let A : Rℓ ↠ Rk be a surjective linear operator, and
let (c1 , . . . , ck ) ∈ Rk . Then there exists a positive real number $C$ such that
                                            k
                                                      !              !
                                           Y
                                      −1
                                 µ A          (ci , ∞) ∩ [−H, H] ∼ CH ℓ
                                                                   ℓ

                                    i=1

as H → ∞.

*Proof.* It will be convenient to fix a linear operator B : Rℓ ↠ Rℓ−k such that the linear
operator T := (A, B) : Rℓ → Rℓ is an isomorphism. Defining
                                        k
                                                           !
                                      Y
                                  −1                   ℓ−k
                       D(H) := T          (ci , ∞) × $\mathbb{R}$       ∩ [−H, H]ℓ ,
                                          i=1

our task is then to give an asymptotic formula for µ(D(H)). Changing c1 to 0 changes the
volume by only O(H ℓ−1 ), since the difference is contained in a parallelepiped of side lengths
bounded by O(1), O(H), . . . , O(H). Similarly, we may assume that all the ci are 0. Let $\mathbb{R}$(H)
denote the region thus obtained, i.e.
                                         k
                                                         !
                                       Y
                       $\mathbb{R}$(H) := T −1        (0, ∞) × Rℓ−k ∩ [−H, H]ℓ .
                                          i=1

Then $\mathbb{R}$(H) = HR(1), so its volume is H ℓ times the volume of $\mathbb{R}$(1), which is positive since
a linear change of coordinates transforms $\mathbb{R}$(1) into the intersection of (0, ∞)k × Rℓ−k with a
neighborhood of 0.

    We use Lemma 5.6 with ℓ = 2n and k equal to twice the number of real places of K.
It is however not obvious that the region Ω can be given by k linear inequalities, as it is
a priori only defined through 2k linear inequalities. We will start by establishing a general
lemma granting linear independence of the resulting set of linear forms. We write Lhomi   for
the homogeneous part of the affine linear polynomial Li .

<a id="lemma-57"></a>
> **Lemma 5.7.** For each real place τ ∈ $\Omega_K$ , fix a 2-element subset Iτ ⊆ {1, 2, 3, 4}. Then
{τ ◦ Lhom
      i   : τ real, i ∈ Iτ } ⊆ HomQ-linear (K, $\mathbb{R}$) is an $\mathbb{R}$-linearly independent set.

*Proof.* The four forms Lhom
                         i    are pairwise K-linearly independent, so the Lhom
                                                                           i    for i ∈ Iτ define
an isomorphism K →QK . Applying
                   2        2             ⊗K K τ  and taking the product  over all real places τ
gives an isomorphism τ Kτ2 → τ Kτ2 . Composing with the projections onto the various
                                    $\mathbb{Q}$
Kτ ∼= $\mathbb{R}$ on the right gives $\mathbb{R}$-linearly independent     maps. Pre-composing with the product of
two copies of the surjection KR := K ⊗ $\mathbb{R}$ ↠ τ Kτ gives the $\mathbb{R}$-linear extensions KR2 → $\mathbb{R}$ of
                                               $\mathbb{Q}$
the maps τ ◦ Lhom
               i    so the latter are $\mathbb{R}$-linearly independent too.

<!-- [Original PDF Page 23] -->

   Let
                           c := m2 κX + 1,         d := m2 κ(m2 κY + λ).
Then observe that Li (X, Y ) = c + ai d for i ∈ {1, 2, 3} and d = m2 κL4 (X, Y ). We shall now
use (K1) to rewrite the defining inequalities of Ω as k linear inequalities, namely 2 for each
real place τ of K, given by two linear forms Mτ,1 and Mτ,2 . In order to construct Mτ,1 and
Mτ,2 , we will now distinguish two cases.
    Firstly, suppose that the real place is τℓ for ℓ ∈ {1, . . . , 6}. Then we will construct Mτℓ ,1
and Mτℓ ,2 via the following lemma.

<a id="lemma-58"></a>
> **Lemma 5.8.** Let ℓ ∈ {1, . . . , 6}. Let Iℓ be {1, 3} if ℓ ∈ {1, 3, 5} and {2, 3} if ℓ ∈ {2, 4, 6} and
define i0 to be the unique element of {1, 2, 3} − Iℓ . Assume that the sign of τℓ (Li (X, Y )) is
precisely the (i, ℓ) entry in the table (5.13) for all i ∈ Iℓ . Then the sign of τℓ (Li0 (X, Y )) is
also the (i0 , ℓ) entry in the table (5.13), and moreover τℓ (L4 (X, Y )) > 0.

*Proof.* Appealing to (K1) and d = m2 κL4 (X, Y ), we see that (IV ) is equivalent to τℓ (d) > 0
for ℓ ∈ {1, 2, 3} and τℓ (d) < 0 for ℓ ∈ {4, 5, 6}. If {i, j, k} = {1, 2, 3}, the condition τℓ (ai ) <
τℓ (aj ) < τℓ (ak ) implies

<a id="equation-514"></a>
$$
τℓ (c + ai d) < τℓ (c + aj d) < τℓ (c + ak d) \tag{5.14}
$$

for ℓ ∈ {1, 2, 3}, and

<a id="equation-515"></a>
$$
τℓ (c + ak d) < τℓ (c + aj d) < τℓ (c + ai d) \tag{5.15}
$$

for ℓ ∈ {4, 5, 6}.
    Keeping the inequalities (5.14) and (5.15) in mind and the orderings (5.7), (5.8), (5.9), the
lemma is now a direct verification.

     If Iℓ = {1, 3}, we choose Mτℓ ,1 := τℓ ◦ Lhom 1    and Mτℓ ,2 := τℓ ◦ Lhom
                                                                              3   . If Iℓ = {2, 3}, we
choose Mτℓ ,1 := τℓ ◦ L2 and Mτℓ ,2 := τℓ ◦ L3 .
                          hom                      hom

     Secondly, suppose that the real place is τ with τ ̸= τℓ for all ℓ ∈ {1, . . . , 6}. In this
case, we can also rewrite, for each given infinite place, the combined four inequalities from
(5.11) and (5.12) as two inequalities. Indeed, pick i ∈ {1, 2, 3} with τ (ai ) minimal. Note that
τ (c + ai d) > 0 then forces τ (c + aj d) > 0 for all j ∈ {1, 2, 3} because τ (d) > 0 by (5.12). Then
we take Mτ,1 = τ ◦ Lhom i     and Mτ,2 = τ ◦ Lhom
                                                4   .
     The linear forms {Mτ,1 : τ ∈ $\Omega_K$ }∪{Mτ,2 : τ ∈ Ωreal
                                       real
                                                            K } are linearly independent by Lemma
5.7, so the resulting linear operator A is surjective. By Lemma 5.6, we conclude that there is
some $C > 0$

<a id="equation-516"></a>
$$
µ Ω ∩ [−H, H]2n ∼ CH 2n             as H → ∞. \tag{5.16}
$$

                                                

#### Application of Kai’s theorem

We now apply Theorem A.7 to Ω and the linear polynomials L1 , L2 , L3 , L4 . Recall that the
linear forms Lhom
              j   are pairwise linearly independent. Therefore the cokernel condition from
Theorem A.7 holds. Moreover, the volume assumption in Theorem A.7 is satisfied thanks to
equation (5.16). Observe that the leading constant in Theorem A.7 is positive by Lemma 5.5.

<!-- [Original PDF Page 24] -->

    We now claim that the asymptotic from Theorem A.7 remains valid upon replacing the
function ΛOK (Li (x, y)) by ΛOK (Li (x, y))1Li (x,y) prime element . Indeed, the difference is bounded
in absolute value by
               4
               X           X                                                     4
                                                                                 Y

<a id="equation-517"></a>
$$
1(Lj (x,y))=pm for some p∈$\Omega_K$ ,m≥2             ΛOK (Li (x, y)). \tag{5.17}
$$

                j=1       x,y∈Zn                                                 i=1
                      (x,y)∈[−N,N ]2n

Note that we have already fixed K, an integral basis for K and the linear forms L1 , . . . , L4 .
Observe that if (x, y) ∈ [−N, N ]2n , then the norm of Lj (x, y) is at most B1 N n (with B1
depending only on K, the fixed integral basis and L1 , . . . , L4 ). Then for every ϵ > 0, there
exists B2 (ϵ) > 0 (which is allowed to depend on ϵ, K, the fixed integral basis of K and
L1 , . . . , L4 ) such that all (x, y) ∈ [−N, N ]2n satisfy ΛOK (Li (x, y)) ≤ B2 (ϵ)N ϵ . Therefore the
expression in equation (5.17) is at most
                                       4
                                       X           X
                      B2 (ϵ) N4   4ϵ

<a id="equation-518"></a>
$$
1(Lj (x,y))=pm for some p∈$\Omega_K$ ,m≥2 . \tag{5.18}
$$

                                       j=1        x,y∈Zn
                                             (x,y)∈[−N,N ]2n

Using once more that the norm of Lj (x, y) is at most B1 N n and using that m ≥ 2, we see
that there are at most B3 N n/2 choices for pm . Hence there exists a real number B4 (ϵ) > 0
such that (5.18) is at most
                          n
              B4 (ϵ)4 N 2 +4ϵ                sup        |{(x, y) ∈ [−N, N ]2n : I = (Lj (x, y))}|.
                                  I⊆$\mathcal{O}_K$ , j∈{1,...,4}

Using that y 7→ Lj (x, y) is injective for every x (by an explicit inspection of the defining
equation), we apply Lemma 3.8 for each I, j, x to bound the number of y ∈ [−N, N ]n such
                                                                                 3n
that I = (Lj (x, y)). We conclude that equation (5.17) is at most B5 (ϵ)N 2 +5ϵ for some
B5 (ϵ) > 0. This proves the claim, since the leading term in Theorem A.7 has magnitude N 2n .
    Furthermore, for any fixed finite set S ⊆ $\Omega_K$ , we claim that the asymptotic in Theorem A.7
remains valid upon imposing the following additional summation conditions on (x, y) ∈ Z2n :
   • each prime element Li (x, y) is not in S,

   • the prime elements Li (x, y) and Lj (x, y) are pairwise coprime for all i ̸= j.
Indeed, for the first bullet point we apply Lemma 3.8 and argue similarly as above. For
the second bullet point, we note that, since Li (x, y) and Lj (x, y) are prime elements, we
must have (Li (x, y)) = (Lj (x, y)) in case they are not coprime. We then use that the map
(x, y) 7→ (Li (x, y), Lj (x, y)) is injective to deduce that the number of (x, y) ∈ [−N, N ]2n ∩ Z2n
such that (Li (x, y)) = (Lj (x, y)) is at most the number of triples (α, β, I) with α and β
generators of I (with coordinates bounded by N in our fixed integral basis) and I of norm at
most B6 N n for some B6 > 0. Hence the desired bound follows from Lemma 3.8.
    We apply this modified version of Theorem A.7 first with S := T ′ , and then we repeatedly
apply this with S equal to T ′ together with the prime elements obtained thus far. Proceeding in
this way, we obtain an infinite sequence (xj , yj ) ∈ Z2n such that, upon setting qi,j := Li (xj , yj ),
we have that
   • each qi,j is a prime element such that (qi,j ) ̸∈ T ′ ,

<!-- [Original PDF Page 25] -->

      • for every (i1 , j1 ) ̸= (i2 , j2 ) we have that (qi1 ,j1 ) ̸= (qi2 ,j2 ).
Set
                                   cj := m2 κxj + 1,        dj := m2 κ(m2 κyj + λ)
and
                    tj := κq1,j q2,j q3,j q4,j = m−2 dj (cj + a1 dj )(cj + a2 dj )(cj + a3 dj ).
We claim that tj satisfies (P 1), (P 2), (P 3). Moreover, we claim that tj satisfies (P 4) for all
but finitely many quadruples. Once we establish the claim, we find in particular at least one
suitable tj , proving Theorem 5.4. Thus it remains to prove the claim. In order to lighten up
the notation, we fix j for now and write t, c, d, q1 , q2 , q3 , q4 for tj , cj , dj , q1,j , q2,j , q3,j , q4,j .
    Let us first check (P 1). By construction of the Li , we see that

                                           q1 ≡ q2 ≡ q3 ≡ 1 mod 8N κ.

Moreover, by the definition of λ and L4 , we have q4 κ ≡ λκ ≡ 1 mod 8N , hence t ≡ 1 mod 8N ,
so by Hensel’s lemma, t ∈ Kv∗2 for all finite v ∈ T . We now check that t is totally positive.
If τ is a real place other than τ1 , . . . , τ6 , then τ (κq4 ) > 0 by (II), and τ (q1 ), τ (q2 ), τ (q3 ) > 0
by (I); hence τ (t) > 0. If instead τ = τℓ for some ℓ ∈ {1, . . . , 6}, then τ (κq4 ) is positive for
ℓ ∈ {1, 2, 3} and negative for ℓ ∈ {4, 5, 6} by (IV ) and (K1); by inspecting the table (5.13),
this matches exactly the sign of τ (q1 q2 q3 ), so τ (t) > 0. Hence t is totally positive. This
establishes (P 1). Finally, the identity t = κq1 q2 q3 q4 gives (P 2).
    We now check (P 3). We have shown just above that

                                           q1 ≡ q2 ≡ q3 ≡ 1 mod 8N κ

and that q1 , q2 , q3 are positive at all real embeddings outside τ1 , . . . , τ6 , so q1 , q2 , q3 ∈ Kv∗2 for
all v ∈ T ′ − {τ1 , . . . , τ6 }. Now fix π and zi as in (K2). Then we have
                            Y                  Y               Y
                                 (zi , qj )v =   (zi , qj )v =           (zi , qj )v
                           v∈T ′             v|∞                v∈{τ1 ,τ2 ,τ3 ,τ4 ,τ5 ,τ6 }

for i ∈ {1, . . . , 12} and j ∈ {1, 2, 3}. By (K2), the signs of zi at τ1 , . . . , τ6 are given by the
table (5.10). Then (P 3) follows from a direct computation using the tables (5.10) and (5.13).
    It remains to check (P 4). Because t is of the shape m−2 d(c + a1 d)(c + a2 d)(c + a3 d), one
directly checks that

                 E −t : m−2 d(c + a1 d)(c + a2 d)(c + a3 d)y 2 = (x + a1 )(x + a2 )(x + a3 )

has the rational point (x, y) = (c/d, m/d2 ), which is also readily seen to be non-torsion for all
but finitely many quadruples (q1,j , q2,j , q3,j , q4,j ) by Lemma 3.2.

### 5.3 Construction of an auxiliary twist <a id="53-construction-of-an-auxiliary-twist"></a>

It remains to prove that an auxiliary twist κ exists, i.e. some κ satisfying (K1) and (K2). It
is possible to give a probabilistic proof of this statement, in the spirit of [46]. However, for
the sake of brevity, we have opted for a direct construction.

<a id="lemma-59"></a>
> **Lemma 5.9.** Let k be a field. If W is a subspace of M2 (k) mapped by the determinant to
zero, then there exists a non-zero row vector r such that rW = 0 or a non-zero column vector
c such that W c = 0.

<!-- [Original PDF Page 26] -->

*Proof.* This follows from the description of lines on a smooth quadric [17, p. 26]. Note that Harris [17] assumes that the ground field is algebraically closed, but the vanishing of a quadratic
form is unchanged by field extension.

   Our next lemma classifies precisely in which situation one is unable to reduce the dimension
by 2 in the context of Lemma 4.7.

<a id="lemma-510"></a>
> **Lemma 5.10.** Let V ⊆ H 1 (GK , $\mathbb{F}_2^2$ ) be a subspace with dimF2 V ≥ 2. Assume that for all
g ∈ GK and for all (χ1 , χ2 ), (χ′1 , χ′2 ) ∈ V
                                                             
                                               χ1 (g) χ2 (g)
                                       det                      = 0.
                                               χ′1 (g) χ′2 (g)

Then, writing T1 , T2 : H 1 (GK , $\mathbb{F}_2^2$ ) → H 1 (GK , $\mathbb{F}_2$ ) for the natural projection maps, we have
T1 (V ) = 0, T2 (V ) = 0 or (T1 + T2 )(V ) = 0.

*Proof.* Since ker(T1 ), ker(T2 ) and ker(T1 + T2 ) have pairwise trivial intersection, we reduce to
the case that dimF2 V = 2, so (χ1 , χ2 ) and (χ′1 , χ′2 ) form a basis of V . Our assumption implies
that the homomorphism φ : GK → M2 ($\mathbb{F}_2$ ) given by
                                                             
                                             χ1 (g) χ2 (g)
                                      g 7→
                                             χ′1 (g) χ′2 (g)

satisfies det ◦φ = 0. Write W := φ(GK ). By Lemma 5.9, it follows that W is included in one
of the following six subspaces of M2 ($\mathbb{F}_2$ )
                                                          
                      ∗ ∗      0 0      ∗ 0     0 ∗     a a      a b
                            ,         ,      ,       ,         ,         .
                      0 0      ∗ ∗      ∗ 0     0 ∗     b b      a b

Since (χ1 , χ2 ) and (χ′1 , χ′2 ) are linearly independent, it is easy to eliminate the first, second
and sixth possibility. The remaining three options correspond exactly to the final conclusion
of the lemma.

    We will prove the existence of an auxiliary twist in four parts. In the first part, we construct
distinct prime ideals p1 , . . . , ps1 ̸∈ T and corresponding local uniformizers π1 , . . . , πs1 for some
integer s1 ≥ 0 such that
                                       SelLs1 ,(π1 ,...,πs ) (GK , E[2]) = 1.
                                                  1

In the second part, we enlarge this list of prime ideals to p1 , . . . , ps2 ̸∈ T and corresponding
local uniformizers π1 , . . . , πs2 for some integer s2 ≥ s1 such that certain auxiliary spaces vanish
while maintaining the property SelLs2 ,(π1 ,...,πs ) (GK , E[2]) = 1.
                                                    2
    In the third and fourth part, we introduce 16 more prime ideals (in particular s := s2 +16).
We will first construct six convenient prime elements ps2 +1 , . . . , ps2 +6 with prescribed local
behavior and local uniformizers. As we are introducing these prime elements, our Selmer
groups may grow and we use six additional prime ideals ps2 +7 , . . . , ps2 +12 to remove any
additional classes introduced in this process. It is at this stage that we heavily rely on the
auxiliary vanishing from the second part.
    Finally, we introduce three more prime elements ps2 +13 , ps2 +14 and ps2 +15 , which combined
appropriately with ps2 +1 , . . . , ps2 +6 , introduce Selmer classes satisfying the sign conditions
from the table (5.10). The task of ps2 +16 is to ensure the sign conditions and ramification
conditions of (K1) and to principalize the product of all the prime ideals.

<!-- [Original PDF Page 27] -->

#### 5.3.1 Reducing ranks <a id="531-reducing-ranks"></a>

Throughout this section, π denotes a vector of uniformizers (the precise entries of this vector
will be clear from context).

<a id="lemma-511"></a>
> **Lemma 5.11.** We have for all i ≥ 0, for all distinct prime ideals p1 , . . . , pi ̸∈ T and all local
uniformizers π1 , . . . , πi ,
                               dimF2 SelLi,π (GK , E[2]) ≡ 0 mod 2.

*Proof.* For i = 0, we observe that SelL0,π (GK , E[2]) = Sel2 (E/K) by Lemma 4.3. Hence
the case i = 0 follows from Corollary 3.6 and Lemma 3.7(c). The general case is then a
consequence of Lemma 4.7 and the case i = 0.

<a id="lemma-512"></a>
> **Lemma 5.12.** For every two non-trivial elements y1 , y2 ∈ K ∗ /K ∗2 , there exist infinitely many
prime ideals q such that y1 and y2 are non-trivial in Kq∗ /Kq∗2 .

*Proof.* This follows from the Chebotarev density theorem if y1 and y2 are linearly independent.
If y1 and y2 are not linearly independent, then we must have y1 = y2 and moreover y1 is nontrivial. In this case the lemma follows once more from the Chebotarev density theorem.

   Our next lemma corresponds precisely to the first part of the argument outlined above.

<a id="lemma-513"></a>
> **Lemma 5.13.** There exists an integer s1 ≥ 0, distinct prime ideals p1 , . . . , ps1 ̸∈ T and local
uniformizers π1 , . . . , πs1 with
                                   SelLs1 ,π (GK , E[2]) = 1.

*Proof.* We claim that for all distinct primes p1 , . . . , pi ̸∈ T and for all local uniformizers
π1 , . . . , πi at least one of the following three statements holds:

(S1) we have SelLi,π (GK , E[2]) = 1,

(S2) there exist a prime ideal pi+1 and a local uniformizer πi+1 such that

                     dimF2 SelLi+1,π (GK , E[2]) = −2 + dimF2 SelLi,π (GK , E[2]),

(S3) there exist prime ideals pi+1 , pi+2 and local uniformizers πi+1 , πi+2 such that

                     dimF2 SelLi+2,π (GK , E[2]) = −2 + dimF2 SelLi,π (GK , E[2]).

The claim visibly implies Lemma 5.13, so it remains to prove the claim.
   Suppose that (S1) fails. Thus we have dimF2 SelLi,π (GK , E[2]) ≥ 2 by Lemma 5.11. If the
space V := SelLi,π (GK , E[2]) does not satisfy the hypothesis of Lemma 5.10, then we can find
g ∈ GK and two elements (χ1 , χ2 ) ∈ V and (χ′1 , χ′2 ) ∈ V such that
                                                       
                                         χ1 (g) χ2 (g)
                                   det                    = 1.
                                         χ′1 (g) χ′2 (g)

By the Chebotarev density theorem, there exists a prime ideal pi+1 ̸∈ T ∪ {p1 , . . . , pi } with
                                                             
                               χ1 (Frobpi+1 ) χ2 (Frobpi+1 )

<a id="equation-519"></a>
$$
det                                    = 1. \tag{5.19}
$$

                               χ′1 (Frobpi+1 ) χ′2 (Frobpi+1 )

<!-- [Original PDF Page 28] -->

Fix an arbitrary choice for the local uniformizer πi+1 . By equation (5.19), the restrictions
respi+1 (χ1 , χ2 ) and respi+1 (χ′1 , χ′2 ) are linearly independent, hence Remark 4.8(c) shows that
we must be in the second case of Lemma 4.7. Thus (S2) holds in this case.
    We henceforth assume that V := SelLi,π (GK , E[2]) does satisfy the hypothesis of Lemma
5.10. Therefore, recalling that T1 , T2 are the projection maps from Lemma 5.10, it follows
from Lemma 5.10 that

T1 (SelLi,π (GK , E[2])) = 0 or T2 (SelLi,π (GK , E[2])) = 0 or (T1 +T2 )(SelLi,π (GK , E[2])) = 0.

Our goal is now to show that (S3) is true. We proceed with the case T1 (SelLi,π (GK , E[2])) = 0;
the other cases are similar.
    Recalling that dimF2 SelLi,π (GK , E[2]) ≥ 2, we may therefore fix some non-trivial element
(1, x) ∈ SelLi,π (GK , E[2]). We apply Lemma 5.12 with y1 = x and y2 = αβ; note that x is
not a square by assumption and that αβ is not a square by Lemma 3.7(a). Therefore there
exists a prime ideal pi+1 ̸∈ T ∪ {p1 , . . . , pi } such that x and αβ are both non-trivial elements
in Kp∗i+1 /Kp∗2i+1 . Now we claim that

<a id="equation-520"></a>
$$
dimF2 respi+1 SelLi,π (GK , E[2]) = 1. \tag{5.20}
$$

Indeed, the above dimension is at least 1, as the element respi+1 (1, x) is non-trivial by the
choice of pi+1 . Moreover, respi+1 SelLi,π (GK , E[2]) is contained in {0} × Hnr
                                                                              1 (G
                                                                                  Kpi+1 $\mathbb{F}_2$ ). But
{0} × Hnr (GKpi+1 $\mathbb{F}_2$ ) is 1-dimensional by Lemma 4.2(a), thus proving the claim (5.20).
          1

    We now pick any local uniformizer πi+1 . It follows from equation (5.20) that, for all choices
of πi+1 , we are in the third case of Lemma 4.7, and hence

<a id="equation-521"></a>
$$
dimF2 SelLi+1,π (GK , E[2]) = dimF2 SelLi,π (GK , E[2]). \tag{5.21}
$$

We claim that there exists (x1 , x2 ) ∈ SelLi+1,π (GK , E[2]) − ker(T1 ). Recall that we picked x to
have non-trivial image in Kp∗i+1 /Kp∗2i+1 and that (1, x) ∈ SelLi,π (GK , E[2]). Hence respi+1 (1, x)
is a non-trivial element of Hnr1 (G
                                     Kpi+1 , E[2]). We deduce that respi+1 (1, x) ̸∈ Li+1,π,pi+1 by
Lemma 4.2(d) and therefore

<a id="equation-522"></a>
$$
(1, x) ̸∈ SelLi+1,π (GK , E[2]). \tag{5.22}
$$

By equations (5.21), (5.22) and the fact that (1, x) ∈ SelLi,π (GK , E[2]), we conclude that
SelLi+1,π (GK , E[2]) − SelLi,π (GK , E[2]) is non-empty. Now we fix any element (x1 , x2 ) ∈
SelLi+1,π (GK , E[2]) − SelLi,π (GK , E[2]), and we will show that x1 is not locally trivial at pi+1 ;
this implies that x1 is also not globally trivial and thus (x1 , x2 ) ̸∈ ker(T1 ) as claimed.
    Observe that (x1 , x2 ) must certainly be non-trivial locally at pi+1 , as otherwise (x1 , x2 ) is
in SelLi,π (GK , E[2]) contrary to our assumption. Inspecting the three non-trivial elements of
Li+1,π,pi+1 in equation (4.1), we see that respi+1 (x1 ) has odd valuation in two cases (and is
hence non-trivial) and that respi+1 (x1 ) = respi+1 (αβ) in the third case (which is non-trivial by
our choice of pi+1 ). This proves the claimed existence of (x1 , x2 ), and we fix any such choice.
    We also clearly have
                                     respi+1                  
            ker SelLi,π (GK , E[2]) −−−−→ H 1 (GKpi+1 , E[2]) ⊆ SelLi+1,π (GK , E[2]).

By the inequality dimF2 SelLi,π (GK , E[2]) ≥ 2 and by equation (5.20), there exists a nontrivial element in the above kernel. By the assumption T1 (SelLi,π (GK , E[2])) = 0, we see that
this element must be of the shape (1, x′ ).

<!-- [Original PDF Page 29] -->

    By Lemma 5.12, there exists a prime ideal pi+2 ̸∈ T ∪ {p1 , . . . , pi+1 } such that x1 and x′
are not locally trivial at pi+2 . Hence the restrictions of (1, x′ ), (x1 , x2 ) ∈ SelLi+1,π (GK , E[2])
at pi+2 must be linearly independent. By Remark 4.8(c) we conclude that we are necessarily
in the second case of Lemma 4.7 for any choice of πi+2 . Combining this with equation (5.21),
we have thus shown that (S3) holds.

#### 5.3.2 Vanishing of auxiliary spaces <a id="532-vanishing-of-auxiliary-spaces"></a>

We have now completed the first part of the construction of the auxiliary twist. The second
part also imposes vanishing of some auxiliary spaces. Given any sequence of distinct primes
p1 , . . . , pr ̸∈ T and local uniformizers π1 , . . . , πr , we define

                                             respj (x, x) ∈ Lr,π,pj for all 1 ≤ j ≤ r,
                                                                                            
                                 ∗   ∗2
                  Dr,1 := x ∈ K /K :
                                          v(x) ≡ 0 mod 2 for all v ̸∈ T ∪ {p1 , . . . , pr }

and
                                                respj (x, 1) ∈ Lr,π,pj for all 1 ≤ j ≤ r,
                                                                                                  
             Dr,2 := x ∈ K ∗ /K ∗2 :
                                             v(x) ≡ 0 mod 2 for all v ̸∈ T ∪ {p1 , . . . , pr }
and
                                                respj (1, x) ∈ Lr,π,pj for all 1 ≤ j ≤ r,
                                                                                                  
             Dr,3 :=       x ∈ K ∗ /K ∗2 :                                                             .
                                             v(x) ≡ 0 mod 2 for all v ̸∈ T ∪ {p1 , . . . , pr }

<a id="lemma-514"></a>
> **Lemma 5.14.** There exists an integer s2 ≥ 0, distinct prime ideals p1 , . . . , ps2 ̸∈ T and local
uniformizers π1 , . . . , πs2 with

                    SelLs2 ,π (GK , E[2]) = 1,          Ds2 ,i = 1        for all i ∈ {1, 2, 3}.           (5.23)

*Proof.* Fix an integer s1 ≥ 0, distinct prime ideals p1 , . . . , ps1 ̸∈ T and local uniformizers
π1 , . . . , πs1 as guaranteed by Lemma 5.13. We will now find an integer s2 ≥ s1 and enlargements p1 , . . . , ps2 and π1 , . . . , πs2 of our previous list of prime ideals and local uniformizers
such that equation (5.23) holds.
     As a first step, we use the Chebotarev density theorem to add four distinct prime ideals
ps1 +1 , . . . , ps1 +4 ̸∈ T ∪ {p1 , . . . , ps } such that the Frobenius elements Frobps1 +1 , . . . , Frobps1 +4
                     √     √ √ √
span Gal(K( −1, α, β, γ)/K). This implies that every non-trivial x ∈ ⟨−1, α, β, γ⟩
reduces to a non-square unit modulo at least one ps1 +j . By our choice of T , the elements
−1, α, β, γ have even valuation at all places v ̸∈ T . Hence resps1 +j (x, x) ∈ Hnr       1 (G
                                                                                                  Kv , E[2]) for
all x ∈ ⟨−1, α, β, γ⟩ and for all j ∈ {1, 2, 3, 4}. Therefore

<a id="equation-524"></a>
$$
⟨−1, α, β, γ⟩ ∩ Ds1 +4,i = 1, \tag{5.24}
$$

as an element in the intersection lies in Kp∗2s +j for all j ∈ {1, 2, 3, 4} by Lemma 4.2(d) and
                                                      1
must therefore be trivial by our choice of ps1 +1 , . . . , ps1 +4 .
    If we let πs′ 1 +j and πs′′1 +j denote the two different local uniformizers in Kp∗s +j /Kp∗2s +j and
                                                                                         1       1
if we denote by π ′ and π ′′ the resulting vectors, then an inspection of equation (4.1) yields
Ls1 +j,π′ ,ps1 +j ̸= Ls1 +j,π′′ ,ps1 +j . Recalling the definition of Aps1 +j in equation (4.2), we may
thus choose the local uniformizer πs1 +j each time in such a way that

<a id="equation-525"></a>
$$
Ls1 +j,π,ps1 +j ̸= Aps1 +j \tag{5.25}
$$

<!-- [Original PDF Page 30] -->

for j ∈ {1, . . . , 4}. Since the restriction of SelLs1 ,π (GK , E[2]) = 1 at ps1 +1 is trivial, we
are not in the second case of Lemma 4.7, and the first case of Lemma 4.7 is ruled out by
equation (5.25) for j = 1. Therefore we must be in the third case of Lemma 4.7. Hence
SelLs1 +1,π (GK , E[2]) = 1 by Lemma 4.7. Repeating this argument three more times, we
deduce that

<a id="equation-526"></a>
$$
SelLs1 +4,π (GK , E[2]) = 1. \tag{5.26}
$$

We claim that for all j ≥ 0 and for all distinct prime ideals ps1 +5 , . . . , ps1 +4+j ̸∈ T ∪
{p1 , . . . , ps1 +4 } and for all local uniformizers πs1 +5 , . . . , πs1 +4+j satisfying
                                                               3
                                                               X
                  SelLs1 +4+j,π (GK , E[2]) = 1      and             dimF2 Ds1 +4+j,i > 0,
                                                               i=1
                             Ds1 +4+j,i ⊆ Ds1 +4,i        for all i ∈ {1, 2, 3},                          (5.27)

there exists a prime ideal ps1 +5+j and a local uniformizer πs1 +5+j such that
                                                    3
                                                    X                          3
                                                                               X
        SelLs1 +5+j,π (GK , E[2]) = 1      and            dimF2 Ds1 +5+j,i <         dimF2 Ds1 +4+j,i ,
                                                    i=1                        i=1
                             Ds1 +5+j,i ⊆ Ds1 +4,i        for all i ∈ {1, 2, 3}.                          (5.28)

Note that this claim suffices to prove the lemma; if equation (5.27) fails for j = 0, then we
must have
                                   X3
                                       dimF2 Ds1 +4+j,i = 0
                                         i=1
by equation (5.26) and hence we may pick s2 := s1 + 4, while if equation (5.27) holds for
j = 0, we may iteratively apply this claim to obtain the lemma.
    We will now prove the claim. Let j ≥ 0, let ps1 +5 , . . . , ps1 +4+j ̸∈ T ∪ {p1 , . . . , ps1 +4 } be
distinct and let πs1 +5 , . . . , πs1 +4+j be local uniformizers satisfying equation (5.27). Fix some
i and some non-trivial x ∈ Ds1 +4+j,i . Since x ̸∈ ⟨−1, α, β, γ⟩ by (5.27) and (5.24), it follows
from Lemma 3.7(a) that ⟨−1, α, β, γ, x⟩ spans a 5-dimensional subspace of K ∗ /K ∗2 . Therefore
there exists a prime ideal v := ps1 +5+j ̸∈ T ∪ {p1 , . . . , ps1 +4+j } such that

<a id="equation-529"></a>
$$
resv (x) ̸= 1,   resv (αβ) ̸= 1,     resv (−αγ) ̸= 1,      resv (βγ) ̸= 1. \tag{5.29}
$$

We recall the definition of Av in equation (4.2), and we choose the local uniformizer πs1 +5+j
in such a way that
                                      Ls1 +5+j,π,v ̸= Av .
Since SelLs1 +4+j,π (GK , E[2]) = 1 by equation (5.27), we may use the argument after equation
(5.25) to show that we are in the third case of Lemma 4.7. This guarantees that

<a id="equation-530"></a>
$$
SelLs1 +5+j,π (GK , E[2]) = 1. \tag{5.30}
$$

Observe that

<a id="equation-531"></a>
$$
x ∈ Ds1 +4+j,i − Ds1 +5+j,i ; \tag{5.31}
$$

indeed, x has even valuation at v and is non-trivial by equation (5.29), so our observation
follows from Lemma 4.2(d).

<!-- [Original PDF Page 31] -->

   We will now show that Ds1 +5+j,i′ ⊆ Ds1 +4+j,i′ for each i′ . To this end, we claim that by
our choice of v = ps1 +5+j

<a id="equation-532"></a>
$$
Ls1 +5+j,π,v ∩ {(y, y) : y ∈ Kv∗ /Kv∗2 } = 1, \tag{5.32}
$$

<a id="equation-533"></a>
$$
Ls1 +5+j,π,v ∩ {(y, 1) : y ∈ Kv∗ /Kv∗2 } = 1, \tag{5.33}
$$

<a id="equation-534"></a>
$$
Ls1 +5+j,π,v ∩ {(1, y) : y ∈ Kv∗ /Kv∗2 } = 1. \tag{5.34}
$$

Indeed, equation (5.32) follows from directly comparing the three non-trivial elements in
{(y, y) : y ∈ Kv∗ /Kv∗2 } with the definition of Ls1 +5+j,π,v in (4.1) and using that resv (βγ) ̸= 1
from equation (5.29). The other claims (5.33) and (5.34) are proven similarly.
    By equations (5.32), (5.33) and (5.34), every element in Ds1 +5+j,i′ must be trivial at v.
This gives the inclusion Ds1 +5+j,i′ ⊆ Ds1 +4+j,i′ for all i′ . Combining this with equations (5.27),
(5.30) and (5.31), we have now shown (5.28).

#### 5.3.3 Auxiliary primes <a id="533-auxiliary-primes"></a>

So far we have executed the first and second part of our construction of κ. We will now embark
on the third part of our construction, where we add certain auxiliary primes. Pick a second
subset {τ7 , . . . , τ12 } of {σ1 , . . . , σ24 } of cardinality 6, disjoint from {τ1 , . . . , τ6 }, such that

<a id="equation-535"></a>
$$
τi (x) · τ6+i (x) > 0 \tag{5.35}
$$

for all x ∈ {−1, α, β, γ} and for all i ∈ {1, . . . , 6}. This is indeed possible; for x = −1 equation
(5.35) always holds, while for x ∈ {α, β, γ}, we use that E satisfies Lemma 3.7(b).
    Finally, we define for α ∈ $\mathcal{O}_K$ and odd β ∈ $\mathcal{O}_K$ the “generalized Legendre symbol”
                                                    
                                    α             α
                                         :=               ∈ {−1, 0, 1},
                                    β          βOK
where the latter symbol is the usual 2-power residue symbol for $\mathcal{O}_K$ .

<a id="definition-515"></a>
> **Definition 5.15.** Let r ≥ 0 and let p1 , . . . , pr ̸∈ T . We say that pr+1 , . . . , pr+6 ∈ $\mathcal{O}_K$ are
auxiliary primes if
(C1) the ideals pr+1 := (pr+1 ), . . . , pr+6 := (pr+6 ) are distinct prime ideals coprime to T and
     p1 , . . . , pr ;

(C2) for all real places τ and for every i ∈ {1, . . . , 6}, we have

                                         τ (pr+i ) < 0 ⇐⇒ τ ∈ {τi , τ6+i }

(C3) we have pr+1 , . . . , pr+6 ∈ Kv∗2 for all v ∈ {p1 , . . . , pr } and for all finite places v ∈ T ;

(C4) for each 1 ≤ i < j ≤ 6 we have
                               
                           pr+j
                                  = −1 ⇐⇒ (i, j) ∈ {(1, 2), (3, 4), (5, 6)}.
                           pr+i

Given r ≥ 0 and distinct prime ideals p1 , . . . , pr ̸∈ T , Mitsui’s prime ideal theorem [18,

<a id="theorem-12"></a>
> **Theorem 1.2.** 1] shows that there always exist auxiliary primes pr+1 , . . . , pr+6 by constructing
the pr+1 , . . . , pr+6 one at a time (starting with pr+1 , then pr+2 , etc.). We pick

<!-- [Original PDF Page 32] -->

(U 1) local uniformizers πr+1 , . . . , πr+6 such that for all i ∈ {1, . . . , 6}

                                                          πr+i = ϵr+i pr+i ,

      where ϵr+i is a non-square unit in Kp∗r+i .

We now collect some standard properties of the Hilbert symbol.

<a id="lemma-516"></a>
> **Lemma 5.16.** Let v ∈ $\Omega_K$ be an odd place. Then:

  (a) (λ1 , λ2 )v = 1 for all λ1 , λ2 ∈ Kv∗ with even valuation;

  (b) for all λ ∈ Kv∗ with even valuation and all uniformizers π ∈ Kv∗ , we have (λ, π)v = 1 if
      and only if λ ∈ Kv∗2 .

Moreover, we have for all real places w of K and for all x, y ∈ Kw∗

                             (x, y)w = -1 ⇐⇒ x and y are both negative.

<a id="lemma-517"></a>
> **Lemma 5.17.** Let pr+1 , . . . , pr+6 be auxiliary primes.

  (i) For all i ∈ {1, . . . , 6}, the elements −1, α, β and γ are in Kp∗2r+i .

 (ii) We have                                      
                            pr+i               pr+j
                                       =                       for all distinct i, j ∈ {1, . . . , 6}.
                            pr+j               pr+i

 (iii) We have for all i ∈ {1, . . . , 6}

<a id="equation-536"></a>
$$
Lr+i,π,pr+i = ⟨(1, ϵr+i pr+i ), (ϵr+i pr+i , 1)⟩. \tag{5.36}
$$

*Proof.* For (i), we apply Hilbert reciprocity to the symbol (pr+i , x) for each i ∈ {1, . . . , 6} and
x ∈ {−1, α, β, γ}. Note that −1, α, β, γ are units at all places outside of T . Hence by (C3) and
Lemma 5.16(a), the symbol (pr+i , x)v certainly vanishes at all finite places v different from
pr+i . Moreover, the total contribution from the infinite places is trivial because of equation
(5.35) and (C2). Hence Hilbert reciprocity gives the vanishing of the local Hilbert symbol
(pr+i , x)(pr+i ) . Since x has pr+i -adic valuation zero, this gives part (i) thanks to Lemma
5.16(b).
    For (ii), note that

    • (pr+i , pr+j )v = 1 for all odd places v ∈ $\Omega_K$ − {pr+i , pr+j } by Lemma 5.17(a);

    • (pr+i , pr+j )v = 1 for all 2-adic places v by (C3);

    • (pr+i , pr+j )v = 1 for all infinite places v, as pr+i and pr+j are not simultaneously negative
      at v by (C2) (hence the result follows from the last part of Lemma 5.16).

Thus, part (ii) follows from Hilbert reciprocity applied to the symbol (pr+i , pr+j ) and Lemma
5.16(b). Part (iii) is a consequence of (i), condition (U 1) and equation (4.1).

<!-- [Original PDF Page 33] -->

    Given auxiliary primes pr+1 , . . . , pr+6 , we now write

                                        V := SelLr+6,π (GK , E[2]).

If we take two elements w1 , w2 ∈ V , then by Lemma 4.2(a) there are unique a, b, c, d ∈ K ∗ /K ∗2
having even valuation at all places v ̸∈ T ∪ {p1 , . . . , pr } and unique ei,1 , fi,1 , ei,2 , fi,2 ∈ {0, 1}
such that
                         6            6                           6          6
                                              !                                       !
                              ei,1       fi,1                        ei,2        fi,2
                        Y             Y                          Y           Y

<a id="equation-537"></a>
$$
w1 = a       pr+i , b   pr+i ,      w2 = c          pr+i , d   pr+i . \tag{5.37}
$$

                            i=1         i=1                            i=1         i=1

<a id="lemma-518"></a>
> **Lemma 5.18.** Let r ≥ 0, let p1 , . . . , pr ̸∈ T be distinct prime ideals and let π1 , . . . , πr be local
uniformizers. Assume that
                             Dr,i = 1 for all i ∈ {1, 2, 3}.                                      (5.38)
Let pr+1 , . . . , pr+6 be auxiliary primes. Let w1 ∈ V be non-trivial and expand it uniquely as in
equation (5.37).

  (i) The pair (a, b) is not in the kernel of the maps T1 , T2 or T1 + T2 from Lemma 5.10.

 (ii) Moreover, if w2 ∈ V does not equal w1 , then (a, b) and (c, d) are distinct (with (c, d) as
      in equation (5.37)).

*Proof.* We start by showing that for all e1 , . . . , e6 , f1 , . . . , f6 ∈ $\mathbb{F}_2$
                            6         6
                                              !
                                         f
                          Y           Y
                              per+i
                                 i
                                    ,      i

<a id="equation-539"></a>
$$
pr+i       ∈ V =⇒ ei = fi = 0. \tag{5.39}
$$

                                  i=1      i=1

Using the local conditions at τ1 , . . . , τ6 (see the top row of the table (5.10)) and the sign
assignments in (C2), we deduce that f1 = f3 = f5 = 0 and e2 = e4 = e6 = 0. The condition
(C4) reveals that pr+4 and pr+6 are in Kp∗2r+2 . Combining this with f1 = f3 = f5 = 0 yields

                                           6
                       respr+2 (pfr+2            respr+2 (pfr+i
                                           Y
                                   2
                                      )=                     i
                                                                ) ∈ ⟨ϵr+2 respr+2 (pr+2 )⟩
                                           i=1

by Lemma 5.17(iii), and ϵr+2 is a non-square unit, so f2 = 0. Using Lemma 5.17(ii) as needed,
we may similarly prove that f4 = f6 = 0 and e1 = e3 = e5 = 0, thus proving the implication
(5.39).
    For (i), let w1 ∈ V be non-trivial and write it as in equation (5.37). Note that the auxiliary
primes pr+i are squares at p1 , . . . , pr by (C3). Hence (a, b) lies in Lr,π,pj for all j = 1, . . . , r.
If (a, b) ∈ ker T1 , then (a, b) ∈ Dr,3 , so (5.38) implies (a, b) = (1, 1), and then (5.39) implies
w1 = (1, 1), contradicting our assumption. Likewise, (a, b) ∈ ker T2 or (a, b) ∈ ker(T1 + T2 )
lead to a contradiction.
    For (ii), apply (5.39) to w1 /w2 .

   In our next result we shall insist on adding exactly six primes; this is not strictly necessary
but is convenient for numbering our primes in the last part of the argument.

<!-- [Original PDF Page 34] -->

<a id="lemma-519"></a>
> **Lemma 5.19.** Let r ≥ 0, let p1 , . . . , pr ̸∈ T be distinct prime ideals and let π1 , . . . , πr be local
uniformizers. Assume that

                    SelLr,π (GK , E[2]) = 1,                  Dr,i = 1     for all i ∈ {1, 2, 3}.     (5.40)

Let pr+1 , . . . , pr+6 be auxiliary primes. Then there exist distinct prime ideals pr+7 , . . . , pr+12 ̸∈
T ∪ {p1 , . . . , pr , (pr+1 ), . . . , (pr+6 )} and local uniformizers πr+7 , . . . , πr+12 such that

<a id="equation-541"></a>
$$
SelLr+12,π (GK , E[2]) = 1,       and \tag{5.41}
$$

                             
                       pr+i
                                  =1            for all i ∈ {1, . . . , 6} and j ∈ {7, . . . , 12}.   (5.42)
                       pr+j

*Proof.* Define V := SelLr+6,π (GK , E[2]). We first show that for each 2-dimensional subspace
W of V , there exists a prime ideal P ̸∈ T ∪ {p1 , . . . , pr , (pr+1 ), . . . , (pr+6 )} such that the
auxiliary primes pr+i are squares modulo P and such that the restriction map resP |W : W →
H 1 (GKP , E[2]) is injective.
     To this end, take such a 2-dimensional subspace W of V spanned by w1 and w2 . Write (a, b)
and (c, d) for the elements corresponding to w1 and w2 as in equation (5.37). Let K1 /K be the
maximal abelian extension of K of exponent 2 that is unramified outside of T ∪ {p1 , . . . , pr },
and write
                                       √
                             K2 := K({ pi : i ∈ {r + 1, . . . , r + 6}}).
Then the extensions K1 /K and K2 /K are linearly disjoint by ramification considerations, and
moreover                          √ √ √ √
                               K( a, b, c, d) ⊆ K1 .
The assumption (5.38) of Lemma 5.18 is satisfied thanks to equation (5.40). By Lemma 5.18(i),
⟨(a, b), (c, d)⟩ is not contained in the kernel of T1 , T2 or T1 + T2 . Moreover, by the second part
of Lemma 5.18(ii), the dimension of ⟨(a, b), (c, d)⟩ equals 2. Then, by the contrapositive of
Lemma 5.10 applied to the quadratic characters (χ1 , χ2 ) and (χ′1 , χ′2 ) associated to respectively
(a, b) and (c, d), we deduce the existence of g ∈ GK such that
                                                          
                                            χ1 (g) χ2 (g)
                                      det                    = 1.
                                            χ′1 (g) χ′2 (g)

Recalling that the extensions K1 /K and K2 /K are linearly disjoint, the existence of P follows
from applying the Chebotarev density theorem to K1 K2 /K.
     We will now prove the lemma. If dimF2 V ≥ 2, then we fix a 2-dimensional subspace
W ⊆ V , and take pr+7 to be a prime P as above. Since the restriction map resP |W : W →
H 1 (GKP , E[2]) is injective and since W has dimension 2, we have nr+6 = −2 by Remark
4.8(c) and Lemma 4.7. Moreover, given that nr+6 = −2, it follows from Remark 4.8(b) that

                          SelLr+7,π (GK , E[2]) ⊆ SelLr+6,π (GK , E[2]) = V.

Note that dimF2 V is even by Lemma 5.11. Hence iterating this procedure, we find a sequence
of prime ideals pr+7 , . . . , pr+6+ 1 dimF V such that
                                           2     2

                                                                                        
                                                                                  pr+i
                         SelLr+6+ 1 dim                 (GK , E[2]) = 1,                     =1
                                       2       $\mathbb{F}_2$ V,π                             pr+j

<!-- [Original PDF Page 35] -->

for all i ∈ {1, . . . , 6} and all j ∈ {7, . . . , 6 + 12 dimF2 V }.
    Note that we have the bound dimF2 V ≤ 12 as a consequence of (5.40) and Lemma 4.7.
Set k := s2 + 6 + 12 dimF2 V ≤ s2 + 12. If k < s2 + 12, we pick pk+1 such that all pr+i (with
i ∈ {1, . . . , 6}) are squares modulo pk+1 . After choosing the local uniformizer πk+1 so that
Lk+1,π,pk+1 ̸= Apk+1 , we are not in the first case of Lemma 4.7. Hence if SelLk,π (GK , E[2]) = 1,
we must be in the third case and thus also SelLk+1,π (GK , E[2]) = 1. Iterating this procedure
exactly 6 − 21 dimF2 V times gives the lemma.

#### 5.3.4 The final step <a id="534-the-final-step"></a>

We are now ready to finish the construction of κ.

<a id="theorem-520"></a>
> **Theorem 5.20.** There exists an auxiliary twist κ.

*Proof.* Fix an integer s2 ≥ 0, distinct prime ideals p1 , . . . , ps2 ̸∈ T and local uniformizers
π1 , . . . , πs2 as in Lemma 5.14. We will take s := s2 + 16. Let ps2 +1 , . . . , ps2 +6 be auxiliary
primes and let πs2 +1 , . . . , πs2 +6 be local uniformizers as in (U 1). Let ps2 +7 , . . . , ps2 +12 and
πs2 +7 , . . . , πs2 +12 be respectively the primes and local uniformizers guaranteed by Lemma
5.19. Applying Mitsui’s prime ideal theorem [18, Theorem 1.2.1] three times yields prime
elements ps2 +13 , ps2 +14 , ps2 +15 such that

(C6) the ideals ps2 +13 := (ps2 +13 ), ps2 +14 := (ps2 +14 ) and ps2 +15 := (ps2 +15 ) are distinct
     prime ideals coprime to T and p1 , . . . , ps2 +12 ;

(C7) we have ps2 +13 , ps2 +14 , ps2 +15 ∈ Kv∗2 for all v ∈ T ∪ {p1 , . . . , ps2 } ∪ {ps2 +7 , . . . , ps2 +12 };

(C8) for each i ∈ {1, . . . , 6} and each j ∈ {13, 14, 15}
                    
              ps2 +j
                       = −1 ⇐⇒ (i, j) ∈ {(1, 13), (2, 13), (3, 14), (4, 14), (5, 15), (6, 15)} ;
              ps2 +i

(C9) for all 13 ≤ i < j ≤ 15                                    
                                                        ps2 +j
                                                                     = 1.
                                                        ps2 +i

We next pick

(U 2) local uniformizers πs2 +13 , πs2 +14 , πs2 +15 such that for all i ∈ {13, 14, 15}

                                                 πs2 +i = ϵs2 +i ps2 +i ,

        where ϵs2 +i is a non-square unit.

<a id="lemma-521"></a>
> **Lemma 5.21.** The following properties hold.

  (i) For all i ∈ {1, . . . , 6} ∪ {13, 14, 15} and all j ∈ {13, 14, 15} with i ̸= j
                                                               
                                               ps2 +i      ps2 +j
                                                       =            .
                                               ps2 +j      ps2 +i

 (ii) The elements −1, α, β and γ lie in Kp∗2s +13 , Kp∗2s +14 and Kp∗2s +15 .
                                                         2             2           2

<!-- [Original PDF Page 36] -->

 (iii) For all i ∈ {s2 + 13, s2 + 14, s2 + 15}

                                           Ls2 +15,π,pi = ⟨(1, ϵi pi ), (ϵi pi , 1)⟩.

*Proof.* Our arguments will be rather similar to those in the proof of Lemma 5.17. For (i),
we apply Hilbert reciprocity to the symbol (ps2 +i , ps2 +j ). The contribution from odd places
v ∈ $\Omega_K$ − {(ps2 +i ), (ps2 +j )} vanishes by Lemma 5.16(a). Next, at the 2-adic and infinite
places, we also get vanishing of the local Hilbert symbol by (C7). Hence (i) follows from an
examination of the local Hilbert symbol at v ∈ {(ps2 +i ), (ps2 +j )} and an application of Lemma
5.16(b).
    For (ii), we apply Hilbert reciprocity to the symbol (ps2 +j , x) for each j ∈ {13, 14, 15}
and x ∈ {−1, α, β, γ}. This symbol vanishes by (C7) and Lemma 5.16(a) at all places v ∈
$\Omega_K$ −{(ps2 +j )}. Then the result follows from Lemma 5.16(b) applied to the place v := (ps2 +j ).
For (iii), it follows from (U 2), (ii) and the defining equation (4.1) of Ls2 +15,π,pi that

                                        Ls2 +15,π,pi = ⟨(1, ϵi pi ), (ϵi pi , 1)⟩

for all i ∈ {s2 + 13, s2 + 14, s2 + 15}.

     To help the reader visualize the mutual Legendre symbols between the prime elements
ps2 +1 , . . . , ps2 +6 and ps2 +13 , ps2 +14 , ps2 +15 imposed by (C4), (C8) and (C9), we represent them
in the graph below, where two distinct vertices are connected by an edge if and only if their
mutual Legendre symbol is −1. Observe that this is a symmetric relation in view of Lemma
5.17 and Lemma 5.21, which explains why our graph is undirected.
```
            p_{s_2+13}                  p_{s_2+14}                  p_{s_2+15}
             /      \                   /      \                   /      \
            /        \                 /        \                 /        \
       p_{s_2+1} -- p_{s_2+2}     p_{s_2+3} -- p_{s_2+4}     p_{s_2+5} -- p_{s_2+6}
```
*Figure 1: Mutual Legendre symbols between $p_{s_2+1}, \dots, p_{s_2+6}, p_{s_2+13}, \dots, p_{s_2+15}$*
Define the six elements

                  (z1 , z2 ) := (ps2 +1 ps2 +13 , 1),            (z3 , z4 )   := (1, ps2 +2 ps2 +13 ),
                  (z5 , z6 ) := (ps2 +3 ps2 +14 , 1),            (z7 , z8 )   := (1, ps2 +4 ps2 +14 ),

<a id="equation-543"></a>
$$
(z9 , z10 ) := (ps2 +5 ps2 +15 , 1),           (z11 , z12 ) := (1, ps2 +6 ps2 +15 ). \tag{5.43}
$$

<a id="lemma-522"></a>
> **Lemma 5.22.** The elements of (5.43) form a basis of SelLs2 +15,π (GK , E[2]) and satisfy the
sign conditions in the table (5.10).

*Proof.* For i = 1, . . . , 6, the prime ps2 +i appears only in the ith element, so the above six
elements are linearly independent. We also have the inequality

                                        dimF2 SelLs2 +15,π (GK , E[2]) ≤ 6

by Lemma 4.7 and by equation (5.41) (applied with r = s2 ). So to establish the claim, it
suffices to check that the above six elements restrict to Ls2 +15,π,v for all v ∈ $\Omega_K$ and satisfy
the sign conditions in the table (5.10).

<!-- [Original PDF Page 37] -->

     For the sign conditions, these are a direct consequence of conditions (C2) and (C7).
In particular, the above six elements restrict to Ls2 +15,π,τ for τ ∈ {τ1 , . . . , τ6 }. Moreover,
(z1 , z2 ), . . . , (z11 , z12 ) are then also in Ls2 +15,π,τ for τ ∈ {τ7 , . . . , τ12 } by equation (4.1), Lemma
4.2(e), equation (5.35) and conditions (C2) and (C7). Finally, for all j ∈ {0, . . . , 5} and all
archimedean places τ ̸∈ {τ1 , . . . , τ12 }, we have resτ (z2j+1 , z2j+2 ) = (1, 1) ∈ Ls2 +15,π,τ by (C2)
and (C7).
     The elements z1 , . . . , z12 have even valuation at all places v outside T ∪ {p1 , . . . , ps2 +15 },
and therefore the pairs (z1 , z2 ), . . . , (z11 , z12 ) are in Ls2 +15,π,v for all such v by equation (4.1)
and Lemma 4.2(a). At the finite places v ∈ T ∪ {p1 , . . . , ps2 } we have resv (z2j+1 , z2j+2 ) =
(1, 1) ∈ Ls2 +15,π,v for all j ∈ {0, . . . , 5} due to (C3) and (C7). So it remains to check that
(z1 , z2 ), . . . , (z11 , z12 ) are in Ls2 +15,π,p for all p ∈ {ps2 +1 , . . . , ps2 +15 }. For the prime ideals
ps2 +7 , . . . , ps2 +12 , this is a consequence of equation (5.42) and condition (C7).
     We now treat the remaining places ps2 +1 , . . . , ps2 +6 , ps2 +13 , ps2 +14 , ps2 +15 . By Lemma
5.17(iii) and Lemma 5.21(iii)

                                          Ls2 +15,π,pi = ⟨(1, ϵi pi ), (ϵi pi , 1)⟩

for all i ∈ {s2 + 1, . . . , s2 + 6, s2 + 13, s2 + 14, s2 + 15}.
    Take i ∈ {s2 + 1, . . . , s2 + 6, s2 + 13, s2 + 14, s2 + 15} and j ∈ {0, . . . , 5}. We thus need
to show that respi (z2j+1 , z2j+2 ) ∈ ⟨(1, ϵi pi ), (ϵi pi , 1)⟩ (Figure 1 may be useful here to keep
track of the relevant indices). Suppose first that i ∈ {s2 + 1, . . . , s2 + 6}. We begin with
the case i = s2 + j + 1, in which case the desired conclusion follows directly from (C8). For
i = s2 + j + 2, for j even, and i = s2 + j for j odd, we combine (C8) and (C4) and, if
needed, Lemma 5.17(ii): for j even we obtain respi (z2j+1 , z2j+2 ) = (ϵi · ϵi , 1) = (1, 1) and
for j odd we obtain respi (z2j+1 , z2j+2 ) = (1, ϵi · ϵi ) = (1, 1). For all remaining values of
i ∈ {s2 + 1, . . . , s2 + 6, s2 + 13, s2 + 14, s2 + 15} we have that (C8) and (C4) and, Lemma
5.17(ii) if needed, imply that respi (z2j+1 , z2j+2 ) = (1, 1).
    We next focus on i ∈ {s2 +13, s2 +14, s2 +15}. We consider first the case i = s2 +13+⌊ 2j ⌋, we
invoke (C8) along with Lemma 5.21(i) to deduce: respi (z2j+1 , z2j+2 ) = (ϵi pi , 1) for even j and
respi (z2j+1 , z2j+2 ) = (1, ϵi pi ) for odd j. We now consider the two remaining cases, and invoke
(C8) and (C9), combined with Lemma 5.21(i), to obtain that respi (z2j+1 , z2j+2 ) = (1, 1).

    Denote by t the product of odd prime ideals in T .

<a id="lemma-523"></a>
> **Lemma 5.23.** There exist a prime ideal q and an element κ ∈ K ∗ such that

  (i) q ̸∈ T ∪ {p1 , . . . , ps2 +15 };

 (ii) ps2 +1 , . . . , ps2 +6 , ps2 +13 , . . . , ps2 +15 ∈ Kq∗2 ;

 (iii) p1 · · · ps2 +15 q = (κ);

 (iv) κ ≡ 1 mod 8t;

  (v) κ is negative at τ4 , τ5 , τ6 and positive at all other real places.

*Proof.* Let m be the modulus 8∞t, where ∞ denotes the product of all archimedean places of
K. Denote by K(m)/K the corresponding ray class field and denote by
                       √
               L := K({ pi : i ∈ {s2 + 1, . . . , s2 + 6} ∪ {s2 + 13, s2 + 14, s2 + 15}}).

<!-- [Original PDF Page 38] -->

Let Im be the group of fractional ideals generated by the finite primes not dividing m. Let
Pm = {(x) : x ≡× 1 mod m}. Then Gal(K(m)/K) is isomorphic to the ray class group Im /Pm .
     By weak approximation, there exists x ∈ $\mathcal{O}_K$ such that x ≡ 1 mod 8t and x is negative at τ4 , τ5 , τ6 and positive at all other real places. Since L and K(m) are linearly disjoint over K, the Chebotarev density theorem provides a prime q that splits completely in
L/K and has the same class as (x)(p1 · · · ps2 +15 )−1 in Gal(K(m)/K). The former says that
ps2 +1 , . . . , ps2 +6 , ps2 +13 , . . . , ps2 +15 ∈ Kq∗2 . The latter says that (x)−1 p1 · · · ps2 +15 q = (y) for
some y ≡× 1 mod m. Now take κ := xy.

    Let q and κ as in Lemma 5.23 and set ps2 +16 := q. By (5.43) and Lemma 5.23(ii), we have
resq (z2j+1 , z2j+2 ) = (1, 1) ∈ Ls2 +16,π,q for all 0 ≤ j ≤ 5. This implies the inclusion

<a id="equation-544"></a>
$$
SelLs2 +15,π (GK , E[2]) ⊆ SelLs2 +16,π (GK , E[2]). \tag{5.44}
$$

Hence we are either in the first or third case of Lemma 4.7. Choosing the local uniformizer
πs2 +16 such that Ls2 +16,π,ps2 +16 ̸= Aps2 +16 , we must be in the third case of Lemma 4.7 and
therefore ns2 +15 = 0. Thus we deduce from equation (5.44) that

                             SelLs2 +16,π (GK , E[2]) = SelLs2 +15,π (GK , E[2]).

Therefore by Lemma 5.22, the elements in (5.43) form a basis of SelLs2 +16,π (GK , E[2]) as well.
Then by Lemma 5.22 and Lemma 5.23, κ satisfies (K1) and (K2), ending the proof.

## References <a id="references"></a>

 [1] L. Alpöge, M. Bhargava, W. Ho and A. Shnidman. Rank stability in quadratic extensions and Hilbert’s tenth problem for the ring of integers of a number field. arXiv
     preprint:2501.18774v1.

 [2] K. Česnavičius. The p-parity conjecture for elliptic curves with a p-isogeny. Journal für
     die reine und angewandte Mathematik 2016 (2016), no. 719, 45–73.

 [3] G. Cornelissen, T. Pheidas and K. Zahidi. Division-ample sets and the Diophantine problem for rings of integers. J. Théor. Nombres Bordeaux 17 (2005), no. 3, 727–735.

 [4] L. Cowland Kellock and V. Dokchitser. Root numbers and parity phenomena. arXiv
     preprint:2303.07883v1.

 [5] M. Davis, H. Putnam, J. Robinson. The decision problem for exponential diophantine
     equations. Ann. of Math. (2) 74 (1961), 425–436.

 [6] J. Denef. Diophantine sets over algebraic integer rings. II. Trans. Amer. Math. Soc. 257
     (1980), no. 1, 227–236.

 [7] J. Denef and L. Lipshitz. Diophantine sets over some rings of algebraic integers. J. London
     Math. Soc. (2) 18 (1978), no. 3, 385–391.

 [8] T. Dokchitser and V. Dokchitser. On the Birch–Swinnerton-Dyer quotients modulo
     squares. Ann. of Math. (2) 172 (2010), no. 1, 567–596.

<!-- [Original PDF Page 39] -->

 [9] T. Dokchitser and V. Dokchitser. Root numbers and parity of ranks of elliptic curves.
     Journal für die reine und angewandte Mathematik 2011 (2011), no. 658, 39–64.

[10] K. Eisenträger. Hilbert’s tenth problem and arithmetic geometry. Ph.D. Thesis, UC
     Berkeley (2003).

[11] N. Garcia-Fritz and H. Pasten. Towards Hilbert’s tenth problem for rings of integers
     through Iwasawa theory and Heegner points. Math. Ann. 377 (2020), no. 3-4, 989–1013.

[12] B. Green and T. Tao. An inverse theorem for the Gowers U 3 (G) norm. Proc. Edinb. Math.
     Soc. (2) 51 (2008), no. 1, 73–153.

[13] B. Green and T. Tao. Linear equations in primes. Ann. of Math. (2) 171 (2010), no. 3,
     1753–1850.

[14] B. Green and T. Tao. The quantitative behaviour of polynomial orbits on nilmanifolds.
     Ann. of Math. (2) 175 (2012), no. 2, 465–540.

[15] B. Green and T. Tao. The Möbius function is strongly orthogonal to nilsequences. Ann.
     of Math. (2) 175 (2012), no. 2, 541–566.

[16] B. Green, T. Tao and T. Ziegler. An inverse theorem for the Gowers U s+1 [N ]-norm. Ann.
     of Math. (2) 176 (2012), no. 2, 1231–1372.

[17] J. Harris. Algebraic geometry. Grad. Texts in Math., 133. Springer-Verlag, New York,
     1992, xx+328 pp.

[18] W. Kai. Notes on Mitsui’s Prime Number Theorem with Siegel zeros.                  arXiv
     preprint:2209.11816v2.

[19] W. Kai. Linear patterns of prime elements in number fields. arXiv preprint:2306.16983v4.

[20] $\mathbb{Z}$. Klagsbrun, B. Mazur and K. Rubin. Disparity in Selmer ranks of quadratic twists of
     elliptic curves. Ann. of Math. (2) 178 (2013), no. 1, 287–320.

[21] $\mathbb{Z}$. Klagsbrun, B. Mazur and K. Rubin. A Markov model for Selmer ranks in families of
     twists. Compos. Math. 150 (2014), no. 7, 1077–1106.

[22] S. Kobayashi. The local root number of elliptic curves with wild ramification. Math. Ann.
     323 (2002), no. 3, 609–623.

[23] P. Koymans and C. Pagano. Elliptic curves of rank one over number fields. arXiv
     preprint:2505.16910v1.

[24] D. Kundu, A. Lei and F. Sprung. Studying Hilbert’s 10th problem via explicit elliptic
     curves. Math. Ann. 390 (2024), no. 4, 5153–5183.

[25] Y. Matiyasevich. The Diophantineness of enumerable sets. Dokl. Akad. Nauk SSSR 191
     (1970), 279–282.

[26] B. Mazur and K. Rubin. Kolyvagin systems. Mem. Amer. Math. Soc. 168 (2004), no.
     799, viii+96.

<!-- [Original PDF Page 40] -->

[27] B. Mazur and K. Rubin. Ranks of twists of elliptic curves and Hilbert’s Tenth Problem.
     Invent. math. 181 (2010), no. 3, 541–575.

[28] B. Mazur and K. Rubin. Diophantine stability. With an appendix by Michael Larsen.
     Amer. J. Math. 140 (2018), no. 3, 571–616.

[29] B. Mazur, K. Rubin and A. Shlapentokh. Existential definability and diophantine stability. J. Number Theory 254 (2024), 1–64.

[30] T. Mitsui. Generalized prime number theorem. Jpn. J. Math. 26 (1956), 1–42.

[31] A. Morgan and $\mathbb{R}$. Paterson. On $2$-Selmer groups of twists after quadratic extension. J.
     London Math. Soc. 105 (2022), no. 2, 1110–1166.

[32] M.$\mathbb{R}$. Murty and H. Pasten. Elliptic curves, L-functions, and Hilbert’s tenth problem. J.
     Number Theory 182 (2018), 1–18.

[33] J. Neukirch, A. Schmidt and K. Wingberg. Cohomology of Number Fields. Second. Vol.
     323. Grundlehren der Mathematischen Wissenschaften. Springer-Verlag, Berlin, 2008.

[34] H. Pasten. Superficies elípticas y el décimo problema de Hilbert. Rev. Mat. Teor. Apl. 30
     (2023), no. 1, 113–120.

[35] T. Pheidas. Hilbert’s tenth problem for a class of rings of algebraic integers. Proc. Amer.
     Math. Soc. 104 (1988), no. 2, 611–620.

[36] B. Poonen. Using elliptic curves of rank one towards the undecidability of Hilbert’s tenth
     problem over rings of algebraic integers. In: Algorithmic Number Theory (Sydney, 2002),
     Lecture Notes in Comput. Sci. 2369, Berlin: Springer-Verlag (2002) 33–42.

[37] B. Poonen and E. Rains. Random maximal isotropic subspaces and Selmer groups. J.
     Amer. Math. Soc. 25 (2012), no. 1, 245–269.

[38] B. Poonen and M. Stoll. The Cassels–Tate pairing on polarized abelian varieties. Ann. of
     Math. (2) 150 (1999), no. 3, 1109–1149.

[39] A. Ray and T. Weston. Diophantine stability for elliptic curves on average. arXiv
     preprint:2304.09742v2.

[40] D. Rohrlich. Variation of the root number in families of elliptic curves. Compos. Math.
     87 (1993), no. 2, 119–151.

[41] H. Shapiro and A. Shlapentokh. Diophantine relationships between algebraic number
     fields. Comm. Pure Appl. Math. 42 (1989), no. 8, 1113–1122.

[42] A. Shlapentokh. Extension of Hilbert’s tenth problem to some algebraic number fields.
     Comm. Pure Appl. Math. 42 (1989), no. 7, 939–962.

[43] A. Shlapentokh. Elliptic curves retaining their rank in finite extensions and Hilbert’s
     tenth problem for rings of algebraic numbers. Trans. Amer. Math. Soc. 360 (2008), no.
     7, 3541–3555.

<!-- [Original PDF Page 41] -->

[44] A. Shnidman and A. Weiss. Rank growth of elliptic curves over N -th root extensions.
     Trans. Amer. Math. Soc. Ser. B 10 (2023), 482–506.

[45] J.H. Silverman. The arithmetic of elliptic curves. Second edition. Grad. Texts in Math.,
     106. Springer, Dordrecht, 2009. xx+513 pp.

[46] P. Swinnerton-Dyer. The effect of twisting on the $2$-Selmer group. Math. Proc. Cambridge
     Philos. Soc. 145 (2008), no. 3, 513–526.

[47] C. Videla. Sobre el décimo problema de Hilbert. Atas da Xa Escola de Algebra, Vitoria,
     ES, Brasil. Colecao Atas 16 Sociedade Brasileira de Matematica (1989), 95–108.

[48] J.G. Zarhin. Noncommutative cohomology and Mumford groups. Mat. Zametki 15 (1974),
     415–419.

[49] D. Zywina. Rank one elliptic curves and rank stability. arXiv preprint:2505.16960v1.

<!-- [Original PDF Page 42] -->

# Appendix A: Additive combinatorics <a id="appendix-a-additive-combinatorics"></a>

In this appendix, we shall first introduce the necessary notation to formally state Kai’s result [5, Theorem 12.1] in the special case of four linear forms. The additive combinatorics
machinery of Kai builds on the earlier works [1, 2, 3, 4]. After stating Kai’s result, we shall
then derive the additive combinatorics result that we shall use in this paper. We start by
introducing two classes of norms that will be important to us.

<a id="definition-A1"></a>
> **Definition A.1.** Let K be a number field. We define the canonical norm on K to be

                                     ||x||can := max |σ(x)|
                                                     →$\mathbb{C}$
                                                σ:K ,−

for x ∈ K. Here the maximum ranges over all embeddings K ,−
                                                          → $\mathbb{C}$.

<a id="definition-A2"></a>
> **Definition A.2.** Let K be a number field and let a be a non-zero fractional ideal of K. Fix
an ordered $\mathbb{Z}$-basis ω := (ω1 , . . . , ωn ) of a. This gives rise to a norm on a by defining the norm
of α = x1 ω1 + · · · + xn ωn ∈ a (with x1 , . . . , xn ∈ $\mathbb{Z}$) to be

                                 ||α||ω,∞ = max(|x1 |, . . . , |xn |).

    Since Kai is interested in uniformity over the fractional ideals a, the notion of norm-length
compatible basis is introduced. The point of this notion is that one wants to uniformly pick
bases of a that are close to the canonical norm. For us, this uniformity is not relevant as we
will ultimately take a = $\mathcal{O}_K$ . Nevertheless, we shall need to introduce this notion to formally
state his result.

<a id="definition-A3"></a>
> **Definition A.3.** Let $C > 1$. Then an ordered $\mathbb{Z}$-basis ω := (ω1 , . . . , ωn ) of a is said to be
$C$-norm-length compatible if

                   $C^{-1}$ NK/$\mathbb{Q}$ (a)1/n ||x||ω,∞ ≤ ||x||can ≤ CNK/$\mathbb{Q}$ (a)1/n ||x||ω,∞

for all x ∈ a.
    Kai shows that norm-length compatible bases always exist.

<a id="proposition-A4"></a>
> **Proposition A.4 ([5, Proposition 3.1]).** Let K be a number field. Then there is a constant
CK > 1 such that for all non-zero fractional ideals a of K, there is a CK -norm-length compatible basis of a.
    Kai then proceeds to fix such a choice of CK throughout his paper, and always takes normlength compatible bases of a. The advantage of doing this is that Kai’s result holds uniformly
over the choice of a, a flexibility that will not be of relevance for us. We now introduce two
direct number field analogues of respectively the von Mangoldt and Euler phi function.

<a id="definition-A5"></a>
> **Definition A.5.** For a number field K and a non-zero integral ideal I of $\mathcal{O}_K$ , we define

                                       φ(I) := |($\mathcal{O}_K$ /I)∗ |.

We also define the von Mangoldt function on all integral ideals I of $\mathcal{O}_K$ through
                    (
                     log NK/$\mathbb{Q}$ (p) if I = pm for some prime p and some m ≥ 1
            Λ(I) =
                     0            otherwise.

<!-- [Original PDF Page 43] -->

Given a fractional ideal a, we define

                                                    Λa (x) = Λ(xa−1 )

for x ∈ a.
    An affine linear form ψ : Zd → Zn can always be written as
                                                                           d
                                                                           X
                                             ψ(x1 , . . . , xd ) = c0 +          ci xi
                                                                           i=1

for some c0 , . . . , cd ∈ Zn . We then define
                                                                           d
                                                                           X
                                             ψ hom (x1 , . . . , xd ) :=         ci xi
                                                                           i=1

to be the corresponding homogeneous linear form and we define for each integer N ≥ 1 another
norm
                         ||ψ||N = max(||c0 ||∞ /N, ||c1 ||∞ , . . . , ||cd ||∞ ),
where || · ||∞ denotes the usual infinity norm. We define

                    p4n |{x ∈ ($\mathbb{Z}$/pZ)d : ψi (x) ̸= 0 in a/pa for all i ∈ {1, . . . , 4} and p | p}|
 βpa (ψ1 , . . . , ψ4 ) :=                                                                         .
                  φ(p)4                                       pd
Kai [5, Remark 12.5] proves that p βpa (ψ1 , . . . , ψ4 ) converges absolutely.
                                $\mathbb{Q}$

<a id="theorem-A6"></a>
> **Theorem A.6 ([5, Theorem 12.1]).** For all n ∈ $\mathbb{Z}$≥1 , there is a positive real number cn > 0
such that for all d ∈ $\mathbb{Z}$≥1 , there is a positive real number cn,d > 0 such that for all number
fields K of degree n, there exists $C > 0$ such that the following holds.
     Let a be a non-zero fractional ideal equipped with a CK -norm-length compatible basis. Let
$N > C$. Let ψ1 , . . . , ψ4 : Zd → a ∼
                                    = Zn be affine linear forms, where the isomorphism a ∼= Zn
comes from the norm-length compatible basis. We assume that:
    • the restriction of ψihom to the kernel of ψjhom has finite cokernel for all i ̸= j, and
                                     1
    • ||ψi ||N ≤ (log log N ) 103 d2 cn .
Let Ω ⊆ [−N, N ]d be a convex set. Then we have

                       4
                                         !
             X         Y                            Vol(Ω)       Y                                 CN d
                             Λa (ψi (x))     −                 ·   β a
                                                                       (ψ 1 , . . . , ψ 4 ) ≤                  .
                                                 ress=1 ζK (s)4 p    p
                                                                                              (log log N )cn,d
          x∈Ω∩Zd       i=1

    Since our affine linear forms will be fixed and since we will take a = $\mathcal{O}_K$ , let us state a
version of this result without any uniformity.

<a id="theorem-A7"></a>
> **Theorem A.7.** Let K be a number field and let d ≥ 1. Let ψ1 , . . . , ψ4 : Zd → $\mathcal{O}_K$ be affine
linear forms. We assume that the restriction of ψihom to the kernel of ψjhom has finite cokernel
for all i ̸= j. Let Ω ⊆ Rd be a convex set, whose volume grows as

                                         Vol(Ω ∩ [−N, N ]d ) = cN d + o(N d )

<!-- [Original PDF Page 44] -->

for some fixed c > 0 as N → ∞. Then we have
                        4
                                      !
            X          Y                     cN d         Y
                          ΛOK (ψi (x)) =                ·   βpOK (ψ1 , . . . , ψ4 ) + o(N d ).
                                         ress=1 ζK (s)4
                                                          p
                 d
      x∈Ω∩[−N,N ] ∩Zd    i=1

*Proof.* This follows from Theorem A.6 and the fact that $\mathcal{O}_K$ has a CK -norm-length compatible
basis by Proposition A.4.

## References <a id="references"></a>

[1] B. Green and T. Tao. An inverse theorem for the Gowers U 3 (G) norm. Proc. Edinb. Math.
    Soc. (2) 51 (2008), no. 1, 73–153.

[2] B. Green and T. Tao. Linear equations in primes. Ann. of Math. (2) 171 (2010), no. 3,
    1753–1850.

[3] B. Green and T. Tao. The quantitative behaviour of polynomial orbits on nilmanifolds.
    Ann. of Math. (2) 175 (2012), no. 2, 465–540.

[4] B. Green and T. Tao. The Möbius function is strongly orthogonal to nilsequences. Ann.
    of Math. (2) 175 (2012), no. 2, 541–566.

[5] W. Kai. Linear patterns of prime elements in number fields. arXiv preprint:2306.16983v4.