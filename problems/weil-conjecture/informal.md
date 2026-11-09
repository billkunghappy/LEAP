<!-- p. 1 -->

# THE WEIL CONJECTURE. I

By Pierre Deligne[^star]

## Contents

- **1 Grothendieck's theory: cohomological interpretation of $L$-functions** — **1**
- **2 Grothendieck's theory: Poincare duality** — **7**
- **3 The main lemma (La majoration fondamentale)** — **10**
- **4 Lefschetz theory: local theory** — **14**
- **5 Lefschetz theory: global theory** — **16**
- **6 The rationality theorem** — **20**
- **7 Completion of the proof of (1.7)** — **24**
- **8 First applications** — **26**

In this article, I prove the Weil conjecture on the eigenvalues of Frobenius endomorphisms. The precise statement is given in (1.6). I have tried to present the proof in a form as geometric and elementary as possible and have included many reviews: only the results of §§3, 6, 7, and 8 are original.

In a sequel to this article,[^1] I will give various refinements of the intermediate results and of the applications, including the “hard” Lefschetz theorem (on the iterated cup-products by the cohomology class of a hyperplane section).

The text faithfully follows that of six lectures given at Cambridge in July 1973. I thank N.Katz for allowing me to use his notes.

## 1 Grothendieck’s theory: cohomological interpretation of $L$-functions

**(1.1)** Let $X$ be a scheme of finite type over $\mathbb{Z}$ and $|X|$ the set of closed points of $X$. For $x \in |X|$, let $N(x)$ denote the number of elements in the residue field $k(x)$ of $X$ at $x$. The

[^star]: This is a translation of Deligne, Pierre, La conjecture de Weil. I. Inst. Hautes Études Sci. Publ. Math. No. 43 (1974), 273–307, based on arXiv:10807.10810 (Evgeny Goncharov). It is available at www.jmilne.org/math under Documents. Last revised October 24, 2021.
[^1]: La conjecture de Weil. II. Inst. Hautes Études Sci. Publ. Math. No. 52 (1980), 137–252.

<!-- p. 2 -->

Hasse-Weil zeta function of $X$ is
$$
\zeta_X(s) = \prod_{x \in |X|} (1 - N(x)^{-s})^{-1} \tag{1.1.1}
$$
(this product converges absolutely for $\Re(s)$ sufficiently large). For $X = \operatorname{Spec}(\mathbb{Z})$, $\zeta_X(s)$ is the Riemann zeta function.

We will consider exclusively the case where $X$ is a scheme over a finite field $\mathbb{F}_q$.

For $x \in |X|$, we write $q_x$ for $N(x)$. Putting $\deg(x) = [k(x)\colon\mathbb{F}_q]$, we have $q_x = q^{\deg(x)}$. It is useful to introduce a new variable $t = q^{-s}$. Let
$$
Z(X; t) = \prod_{x \in |X|} (1 - t^{\deg(x)})^{-1}; \tag{1.1.2}
$$
this product converges for $|t|$ sufficiently small, and we have
$$
\zeta_X(s) = Z(X; q^{-s}). \tag{1.1.3}
$$

**(1.2)** Dwork (On the rationality of the zeta function of an algebraic variety, *Amer. J. Math.*, 82, 1960, p. 631–648) and Grothendieck ([1] and SGA 5) have proved that $Z(X; t)$ is a rational function of $t$.

For Grothendieck, this is a corollary of general results in $l$-adic cohomology (where $l$ is a prime number not equal to the characteristic $p$ of $\mathbb{F}_q$). These provide a cohomological interpretation of the zeros and poles of $Z(X; t)$, and a functional equation when $X$ is proper and smooth. The methods of Dwork are $p$-adic. For $X$ a non-singular hypersurface in a projective space they also provided him with a cohomological interpretation of the zeros and poles, and the functional equation. They inspired the crystalline theory of Grothendieck and Berthelot, which for $X$ proper and smooth provides a $p$-adic cohomological interpretation of the zeros and poles, and the functional equation. Based on the ideas of Washnitzer, Lubkin created a variant of this theory, valid only for $X$ proper, smooth, and liftable to characteristic $0$ (A $p$-adic proof of Weil’s conjectures, *Ann of Math*, 87, 1968, pp. 125-255).

We will make essential use of Grothendieck’s results, and recall them below.

**(1.3)** Let $X$ be an algebraic variety over an algebraically closed field $k$ of characteristic $p$, i.e., a separated scheme of finite type over $k$. We do not exclude the case $p = 0$. For any prime number $l \neq p$, Grothendieck defined $l$-adic cohomology groups $H^i(X, \mathbb{Q}_l)$. He also defined cohomology groups with compact support $H_c^i(X, \mathbb{Q}_l)$. For $X$ proper, the two coincide. The $H_c^i(X, \mathbb{Q}_l)$ are vector spaces of finite dimension over $\mathbb{Q}_l$, zero for $i > 2\dim(X)$.

**(1.4)** Let $X_0$ be an algebraic variety over $\mathbb{F}_q$, $\overline{\mathbb{F}}_q$ the algebraic closure of $\mathbb{F}_q$, and $X$ the algebraic variety over $\overline{\mathbb{F}}_q$ obtained from $X_0$ by extension of scalars from $\mathbb{F}_q$ to $\overline{\mathbb{F}}_q$. In the language of Weil and Shimura, we would express this situation by: “Let $X$ be an algebraic variety defined over $\mathbb{F}_q$”. Let $F\colon X \to X$ be the Frobenius morphism; it sends a point with coordinates $x$ to the point with coordinates $x^q$; in other words, for $U_0$ a Zariski open subset of $X_0$, defining an open subset $U$ of $X$, we have $F^{-1}(U) = U$; for $x \in H^0(U_0, \mathcal{O})$, we have $F^*x = x^q$. Let us identify the set $|X|$ of closed points of $X$ with $X_0(\overline{\mathbb{F}}_q)$ (the set $\operatorname{Hom}_{\mathbb{F}_q}(\operatorname{Spec}(\overline{\mathbb{F}}_q), X_0)$ of points of $X_0$ with coefficients in $\overline{\mathbb{F}}_q$) and let $\varphi \in \operatorname{Gal}(\overline{\mathbb{F}}_q/\mathbb{F}_q)$ be

<!-- p. 3 -->

the Frobenius map: $\varphi(x) = x^q$. The action of $F$ on $|X|$ can be identified with the action of $\varphi$ on $X_0(\overline{\mathbb{F}}_q)$. So:

a) The set $X^F$ of closed points of $X$ fixed under $F$ can be identified with the set $X_0(\mathbb{F}_q) \subset X_0(\overline{\mathbb{F}}_q)$ of points of $X$ defined over $\mathbb{F}_q$. This simply expresses the fact that for, $x \in \overline{\mathbb{F}}_q$, we have $x \in \mathbb{F}_q \Leftrightarrow x^q = x$.

b) Similarly, the set $X^{F^n}$ of closed points of $X$ fixed under the $n$th iterate of $F$ can be identified with $X_0(\mathbb{F}_{q^n})$.

c) The set $|X|$ of closed points of $X$ can be identified with the set $|X|_F$ of orbits of $F$ (or $\varphi$) on $|X|$. The degree $\deg(x)$ of $x \in |X_0|$ is the number of elements in the corresponding orbit.

d) From b) and c) we see that
$$
\#X^{F^n} = \#X_0(\mathbb{F}_{q^n}) = \sum_{\deg(x)\mid n} \deg(x). \tag{1.4.1}
$$
(If $x \in |X_0|$ and $\deg(x)\mid n$, then $x$ defines $\deg(x)$ points with coordinates in $\mathbb{F}_{q^n}$, all conjugate over $\mathbb{F}_q$).

**(1.5)** The morphism $F$ is finite, in particular, proper. Therefore, it induces morphisms
$$
F^*\colon H_c^i(X, \mathbb{Q}_l) \to H_c^i(X, \mathbb{Q}_l).
$$
Grothendieck proved the Lefschetz formula
$$
\#X^F = \sum_i (-1)^i \operatorname{Tr}(F^*, H_c^i(X, \mathbb{Q}_l));
$$
the term on the right, *a priori* an $l$-adic number, is an integer, equal to the term on the left. We note that such a formula is only reasonable because $dF = 0$, even at infinity ($X$ is not assumed to be proper); the relation $dF = 0$ implies that fixed points of $F$ have multiplicity one.

An analogous formula is valid for the iterates of $F$:
$$
\#X^{F^n} = X_0(\mathbb{F}_{q^n}) = \sum_i (-1)^i \operatorname{Tr}(F^{*n}, H_c^i(X, \mathbb{Q}_l)) \tag{1.5.1}
$$

We take the logarithmic derivative of (1.1.2):
$$
\begin{aligned}
t\frac{d}{dt}\log Z(X_0, t) &= \frac{t\frac{d}{dt}Z(X_0, t)}{Z(X_0, t)} \\
&= \sum_{x \in |X_0|} -\frac{-\deg(x)t^{\deg(x)}}{1 - t^{\deg(x)}} \\
&= \sum_{x \in |X_0|} \sum_{n > 0} \deg(x)t^{n\deg(x)} \overset{(1.4.1)}{=} \sum_n X_0(\mathbb{F}_{q^n})t^n
\end{aligned} \tag{1.5.2}
$$

For $F$ an endomorphism of a vector space $V$, we have an identity of formal series
$$
t\frac{d}{dt}\log(\det(1 - Ft, V)^{-1}) = \sum_{n > 0} \operatorname{Tr}(F^n, V)t^n \tag{1.5.3}
$$

<!-- p. 4 -->

(check it for $\dim V = 1$ and observe that both sides are additive in V when we take short exact sequences). On substituting (1.5.1) into (1.5.2) and applying (1.5.3), we find that
$$
t\frac{d}{dt}\log Z(X_0, t) = \sum_i (-1)^i t\frac{d}{dt}\log\det(1 - F^*t, H_c^i(X, \mathbb{Q}_l))^{-1},
$$
or
$$
Z(X, t) = \prod_i \det(1 - F^*t, H_c^i(X, \mathbb{Q}_l))^{(-1)^{i+1}} \tag{1.5.4}
$$

The term on the right is in $\mathbb{Q}_l(t)$. The formula affirms that its Taylor expansion at $t = 0$, *a priori* a formal series in $\mathbb{Q}_l[[t]]$ with constant coefficient one, is in $\mathbb{Z}[[t]]$ and is equal to the term on the left, also considered as a formal series in $t$. This formula is the Grothendiek’s cohomological interpretation of the $Z$-function.

Our main result is the following:

**Theorem (1.6).** *Let $X_0$ be a projective nonsingular ($=$ smooth) variety over $\mathbb{F}_q$. For each $i$, the characteristic polynomial $\det(1 - F^*t, H^i(X, \mathbb{Q}_l))$ has integer coefficients independent of $l$ ($l \neq p$). The complex roots $\alpha$ of this polynomial (complex conjugates of the eigenvalues of $F^*$) have absolute value $|\alpha| = q^{\frac{i}{2}}$.*

We show that (1.6) is a consequence of the following apparently weaker statement:

**Lemma (1.7).** *For each $i$ and each $l \neq p$, the eigenvalues of the Frobenius endomorphism $F^*$ on $H^i(X, \mathbb{Q}_l)$ are algebraic numbers all of whose complex conjugates are of absolute value $|\alpha| = q^{\frac{i}{2}}$.*

*Proof of (1.7) $\Rightarrow$(1.6):* Regard $Z(X_0, t)$ as a formal series with constant term $1$ in $\mathbb{Z}[[t]]\colon Z(X_0, t) = \sum_n a_n t^n$. From (1.5.3), the image of $Z(X_0, t)$ in $\mathbb{Q}_l[[t]]$ is the Taylor expansion of a rational function. This means that for $N$ and $M$ sufficiently large ($\geq$ the degrees of numerators and denominators) the Hankel determinants
$$
H_k = \det((a_{i+j+k})_{0 \leq i, j \leq M}) \qquad (k > N)
$$
are zero. The vanishing is true in $\mathbb{Q}_l$ if and only if it is true in $\mathbb{Q}$; $Z(X_0, t)$ is therefore the Taylor expansion of an element of $\mathbb{Q}(t)$. In other words,
$$
Z(X_0, t) \in \mathbb{Z}[[t]] \cap \mathbb{Q}_l(t) \subset \mathbb{Q}(t).
$$

Let $Z(X_0, t) = P/Q$ with $P, Q$ coprime elements of $\mathbb{Z}[t]$ having positive constant terms. According to a lemma of Fatou, since $Z(X_0, t)$ lies in $\mathbb{Z}[[t]]$ and has constant term $1$, the constant terms of $P$ and $Q$ are $1$. Let
$$
P_i(t) = \det(1 - F^*t, H^i(X, \mathbb{Q}_l)).
$$
(1.7) implies that $P_i$ are coprime. The term on the right of (1.5.4) is therefore an irreducible fraction and
$$
\begin{aligned}
P(t) &= \prod_{i\text{ odd}} P_i(t) \\
Q(t) &= \prod_{i\text{ even}} P_i(t).
\end{aligned}
$$

<!-- p. 5 -->

Let $K$ be the subfield of the algebraic closure $\overline{\mathbb{Q}}_l$ of $\mathbb{Q}_l$ generated over $\mathbb{Q}$ by the roots of $R(t) = P(t)Q(t)$. The roots of $P_i(t)$ are those roots of $R(t)$ with the property that all their complex conjugates have absolute value $q^{-\frac{i}{2}}$. This set is stable under $\operatorname{Gal}(K/\mathbb{Q})$. Therefore, $P_i(t)$ has rational coefficients. According to a lemma of Gauss (or because roots of $P_i$, being roots of $R$, are the inverses of algebraic integers), it even has integer coefficients. The description above of the roots of $P_i(t)$ is independent of $l$; therefore, the polynomial $P_i(t)$ is also independent of $l$.

The rest of the article is devoted to the proof of (1.7).

**(1.8)** Grothendieck’s theory provides a cohomological interpretation, not only of zeta functions, but also of $L$-functions. The results are as follows.

**(1.9)** Let $X$ be an algebraic variety over a field $k$. For the definition of a constructible $\mathbb{Q}_l$-sheaf on $X$, I refer to SGA 5 VI. It suffices to say that:

a) If $\mathcal{F}$ is a constructible $\mathbb{Q}_l$-sheaf on $X$, then there exists a finite partition of $X$ into locally closed subschemes such that $\mathcal{F}|X_i$ is locally constant.

b) Suppose that $X$ is connected, and let $\bar{x}$ be a geometric point of $X$. For $\mathcal{F}$ locally constant, $\pi_1(X, \bar{x})$ acts on the stalks $\mathcal{F}_{\bar{x}}$; the functor sending a sheaf to its stalk at $\bar{x}$ is an equivalence from the category of locally constant $\mathbb{Q}_l$-sheaves on $X$ to the category of continuous representations of $\pi_1(X, \bar{x})$ on $\mathbb{Q}_l$-vector spaces of finite dimension. Such a representation in general does not factor through a finite quotient.

c) When $k = \mathbb{C}$, the constructible $\mathbb{Q}_l$-sheaves over $X$ can be identified with the sheaves of $\mathbb{Q}_l$-vector spaces $\mathcal{F}$ on $X^{\text{an}}$ with the property that there exists a finite partition of $X$ into Zariski-locally closed subsets $X_i$ such that, for each $i$, there is a local system of free $\mathbb{Z}_l$-modules $\mathcal{F}_i$ of finite type on $X_i$ with
$$
\mathcal{F}|X_i = \mathcal{F}_i \otimes_{\mathbb{Z}_l} \mathbb{Q}_l.
$$

We will consider only constructible $\mathbb{Q}_l$-sheaves, and will simply call them $\mathbb{Q}_l$-sheaves.

**(1.10)** Suppose that $k$ is algebraically closed, and let $\mathcal{F}$ be a $\mathbb{Q}_l$-sheaf on $X$. Grothendieck has defined $l$-adic cohomology groups $H^i(X, \mathcal{F})$ and $H_c^i(X, \mathcal{F})$. The $H_c^i(X, \mathcal{F})$ are vector spaces of finite dimension over $\mathbb{Q}_l$, zero for $i > 2\dim(X)$. For $k = \mathbb{C}$, the $H^i(X, \mathcal{F})$ and $H_c^i(X, \mathcal{F})$ are the usual cohomology groups (resp. with compact support) of $X^{\text{an}}$ with coefficients in $\mathcal{F}$.

**(1.11)** Let $X_0$ be an algebraic variety over $\mathbb{F}_q$, $X$ the corresponding variety over $\overline{\mathbb{F}}_q$, and $\mathcal{F}_0$ a sheaf of sets on $X_0$ (for the etale topology). We denote by $\mathcal{F}$ its inverse image on $X$. In addition to the Frobenius isomorphism $F\colon X \to X$, we have a canonical isomorphism $F^*\colon F^*\mathcal{F} \xrightarrow{\sim} \mathcal{F}$. Here is a description. We regard $\mathcal{F}_0$ as an étale space over $X_0$, i.e., we identify $\mathcal{F}_0$ with an algebraic space $[\mathcal{F}_0]$ equipped with an etale morphism $f\colon [\mathcal{F}_0] \to X_0$ such that $\mathcal{F}_0$ is the sheaf of local sections of $[\mathcal{F}_0]$. The similar etale space $[\mathcal{F}]$ over $X$ is obtained from $[\mathcal{F}_0]$ by extension of scalars. Therefore, we have a commutative diagram
$$
\begin{array}{ccc}
[\mathcal{F}] & \xrightarrow{F} & [\mathcal{F}] \\
f \downarrow & & \downarrow f \\
X & \xrightarrow{F} & X,
\end{array}
$$

<!-- p. 6 -->

and hence a morphism $[\mathcal{F}] \to X \times_{(F, X, f)} [\mathcal{F}] = [F^*\mathcal{F}]$, which is an isomorphism because $f$ is étale. The inverse of this isomorphism defines the isomorphism $F^*\mathcal{F} \xrightarrow{\sim} \mathcal{F}$ sought.

This construction can be generalized to $\mathbb{Q}_l$-sheaves.

**(1.12)** Let $X_0$ be an algebraic variety over $\mathbb{F}_q$, $\mathcal{F}_0$ a $\mathbb{Q}_l$-sheaf on $X_0$, $(X, \mathcal{F})$ the pair obtained by extension of scalars from $\mathbb{F}_q$ to $\overline{\mathbb{F}}_q$, $F\colon X \to X$, and $F^*\colon F^*\mathcal{F} \to \mathcal{F}$.

The finite morphism $F$ and $F^*$ define an endomorphism
$$
F^*\colon H_c^i(X, \mathcal{F}) \to H_c^i(X, F^*\mathcal{F}) \to H_c^i(X, \mathcal{F}).
$$
For $x \in |X|$, $F^*$ defines a morphism $F_x^*\colon \mathcal{F}_{F(x)} \to \mathcal{F}_x$. When $x \in X^F$ this is an endomorphism of $\mathcal{F}_x$. Grothendieck proved the Lefschetz formula
$$
\sum_{x \in X^F} \operatorname{Tr}(F_x^*, \mathcal{F}_x) = \sum_i (-1)^i \operatorname{Tr}(F^*, H_c^i(X, \mathcal{F})).
$$
A similar formula holds for the iterates of $F$: the $n$ iterate of $F^*$ defines morphisms $F_x^{*n}\colon \mathcal{F}_{F^n(x)} \to \mathcal{F}_x$; for $x$ fixed by $F^n$, $F_x^{*n}$ is an endomorphism and
$$
\sum_{x \in X^{F^n}} \operatorname{Tr}(F_x^{*n}, \mathcal{F}_x) = \sum_i (-1)^i \operatorname{Tr}(F^{*n}, H_c^i(X, \mathcal{F})) \tag{1.12.1}
$$

**(1.13)** Let $x_0 \in |X|$, $Z$ the orbit corresponding to $F$ in $|X|$, and $x \in Z$. The orbit $Z$ has $\deg(x_0)$ elements (1.4). We denote by $F_{x_0}^*$ the endomorphism $F_x^{*\deg(x_0)}$ of $\mathcal{F}_x$, and we put
$$
\det(1 - F_{x_0}^*t, \mathcal{F}_0) = \det(1 - F_{x_0}^*t, \mathcal{F}_x).
$$
Up to isomorphism, $(\mathcal{F}_x, F_{x_0}^*)$ does not depend on the choice of $x$. This justifies omitting $x$ in the notation. We will use a similar notation for other functions of $(\mathcal{F}_x, F_{x_0}^*)$.

**(1.14)** Define $Z(X_0, \mathcal{F}_0, t) \in \mathbb{Q}_l[[t]]$ by the product
$$
Z(X_0, \mathcal{F}_0, t) = \prod_{x \in |X_0|} \det(1 - F_x^*t^{\deg(x)}, \mathcal{F}_0)^{-1}. \tag{1.14.1}
$$
For $\mathcal{F}$ the constant sheaf $\mathbb{Q}_l$, we recover (1.1.2). According to (1.5.3), the logarithmic derivative of $Z$ is
$$
t\frac{d}{dt}\log Z(X_0, \mathcal{F}_0, t) \overset{\text{def}}{=} \frac{t\frac{d}{dt}Z(X_0, \mathcal{F}_0, t)}{Z(X_0, \mathcal{F}_0, t)} = \sum_n \sum_{x \in X^{F^n} = X_0(\mathbb{F}_{q^n})} \operatorname{Tr}(F_x^{*n}, \mathcal{F}_0)t^n \tag{1.14.2}
$$
Substituting (1.12.1) into (1.14.2), we find, by the same calculation as in (1.5), the following generalization of (1.5.4)
$$
Z(X_0, \mathcal{F}_0, t) = \prod_i \det(1 - F^*t, H_c^i(X, \mathcal{F}))^{(-1)^{i+1}} \tag{1.14.3}
$$
This formula is an identity in $\mathbb{Q}_l[[t]]$.

**(1.15)** It is sometimes convenient to use a galoisian language rather than a geometric one. Here is the dictionary.

<!-- p. 7 -->

If $\overline{\mathbb{F}}_q^1$ and $\overline{\mathbb{F}}_q^2$ are two algebraic closures of $\mathbb{F}_q$, then $(X_0, \mathcal{F}_0)$ over $\mathbb{F}_q$ defines by extension of scalars $(X_1, \mathcal{F}_1)$ over $\overline{\mathbb{F}}_q^1$ and $(X_2, \mathcal{F}_2)$ over $\overline{\mathbb{F}}_q^2$. Every $\mathbb{F}_q$-isomorphism $\sigma\colon \overline{\mathbb{F}}_q^1 \xrightarrow{\sim} \overline{\mathbb{F}}_q^2$ defines an isomorphism
$$
H_c^*(X_1, \mathcal{F}_1) \xrightarrow{\sim} H_c^*(X_2, \mathcal{F}_2).
$$
In particular, for $\overline{\mathbb{F}}_q^1 = \overline{\mathbb{F}}_q^2$ (denoted by $\overline{\mathbb{F}}_q$), we find that $\operatorname{Gal}(\overline{\mathbb{F}}_q/\mathbb{F}_q)$ acts on $H_c^*(X, \mathcal{F})$ (action by transport of structure ). Let $\varphi \in \operatorname{Gal}(\overline{\mathbb{F}}_q/\mathbb{F}_q)$ be the Frobenius map. One can check that
$$
F^* = \varphi^{-1} \qquad (\text{in }\operatorname{End}(H_c^*(X, \mathcal{F}))).
$$
This suggests defining the *geometric Frobenius* $F \in \operatorname{Gal}(\overline{\mathbb{F}}_q/\mathbb{F}_q)$ to be $\varphi^{-1}$. We have
$$
F^* = F. \tag{1.15.1}
$$

Let $x$ be a geometric point of $X_0$, localized to $x_0 \in |X_0|$. By transport of structure, the group $\operatorname{Gal}(k(x)/k(x_0))$ acts on the stalk $(\mathcal{F}_0)_x$ of $\mathcal{F}_0$ at $x$; in particular, the geometric Frobenius relative to $k(x_0)$, $F_{x_0} \in \operatorname{Gal}(k(x)/k(x_0))$, acts. For $x$ defined by a closed point, again denoted by $x$, in $X$, we have $\mathcal{F}_x = (\mathcal{F}_0)_x$ and
$$
F_{x_0}^* \overset{\text{def}}{=} F_x^{*\deg(x_0)} = F_{x_0} \qquad (\text{in }\operatorname{End}(\mathcal{F}_x)) \tag{1.15.2}
$$
.

In the galoisian notation, (1.14.3) becomes
$$
\prod_{x \in |X_0|} \det(1 - F_x t^{\deg(x)}, \mathcal{F}_0)^{-1} = \prod_i \det(1 - Ft, H_c^i(X, \mathcal{F}))^{(-1)^{i+1}}.
$$

## 2 Grothendieck’s theory: Poincare duality

**(2.1)** To explain the relation between roots of unity and orientations, I will first restate two classical cases in an unusual language .

a) *Differentiable manifolds.* - Let $X$ be a differentiable manifold purely of dimension $n$. The orientation sheaf $\mathbb{Z}'$ on $X$ is the sheaf locally isomorphic to the constant sheaf $\mathbb{Z}$, whose invertible sections on an open $U$ in $X$ correspond to the orientations of $U$. An *orientation* of $X$ is an isomorphism of $\mathbb{Z}'$ with the constant sheaf $\mathbb{Z}$. The *fundamental class* of $X$ is a morphism $\operatorname{Tr}\colon H_c^n(X, \mathbb{Z}') \to \mathbb{Z}$; if $X$ is orientable, it can be identified with a morphism $\operatorname{Tr}\colon H_c^n(X, \mathbb{Z}) \to \mathbb{Z}$. Poincaré duality can be expressed using this fundamental class.

b) *Complex varieties.* - Let $\mathbb{C}$ be an algebraic closure of $\mathbb{R}$. A smooth complex algebraic variety, or rather the underlying differentiable variety, is always orientable. To justify this it suffices to orient $\mathbb{C}$ itself. This amounts to a choice:

*a)* choosing one of the two roots of the equation $X^2 = -1$; we call it $+i$;

*b)* choosing an isomorphism from $\mathbb{R}/\mathbb{Z}$ to $U^1 = \{z \in \mathbb{C} \mid |z| = 1\}$; $+i$ is the image of $1/4$;

*c)* choosing one of the two isomorphisms $x \mapsto \exp(\pm 2\pi ix)$ from $\mathbb{Q}/\mathbb{Z}$ to the group of the roots of unity of $\mathbb{C}$, which extends continuously to an isomorphism from $\mathbb{R}/\mathbb{Z}$ to $U^1$.

We denote by $\mathbb{Z}(1)$ a free $\mathbb{Z}$-module of rank one whose set of generators has two elements canonically corresponding to one of the two-element sets *a)*, *b)*, *c)*. The simplest is to take $\mathbb{Z}(1) = \operatorname{Ker}(\exp\colon \mathbb{C} \to \mathbb{C}^*)$. The generator $y = \pm 2\pi i$ corresponds to the isomorphism *c)*: $x \mapsto \exp(xy)$.

<!-- p. 8 -->

Let $\mathbb{Z}(r)$ be the $r$-th tensor power of $\mathbb{Z}(1)$. If $X$ is a smooth complex algebraic variety purely of complex dimension $r$, the orientation sheaf on $X$ is the constant sheaf of value $\mathbb{Z}(r)$.

**(2.2)** To “orient” an algebraic variety over an algebraically closed $k$ of characteristic zero, we must choose an isomorphism from $\mathbb{Q}/\mathbb{Z}$ to the group of the roots of unity of $k$. The set of such isomorphisms is a principal homogeneous space under $\widehat{\mathbb{Z}}^*$ (no longer under $\mathbb{Z}^*$). When one is only interested in $l$-adic cohomology, it suffices to consider the roots of unity of order a power of $l$, and to suppose that the characteristic $p$ of $k$ differs from $l$. We denote by $\mathbb{Z}/l^n(1)$ the group of roots of unity of $k$ of order dividing $l^n$. For variable $n$, the $\mathbb{Z}/l^n(1)$ form a projective system with transition maps
$$
\sigma_{m,n}\colon \mathbb{Z}/l^m(1) \to \mathbb{Z}/l^n(1), \quad x \mapsto x^{l^{m-n}}.
$$
We put $\mathbb{Z}_l(1) = \operatorname{lim\,proj} \mathbb{Z}/l^n(1)$ and $\mathbb{Q}_l(1) = \mathbb{Z}_l(1) \otimes_{\mathbb{Z}_l} \mathbb{Q}_l$. Denote by $\mathbb{Q}_l(r)$ the $r$-th tensor power of $\mathbb{Q}_l(1)$; for $r \in \mathbb{Z}$ negative we put $\mathbb{Q}_l(r) = \mathbb{Q}_l(-r)^\vee$.

As a vector space over $\mathbb{Q}_l$, $\mathbb{Q}_l(1)$ is isomorphic to $\mathbb{Q}_l$. However, the automorphism group of $k$ acts non-trivially on $\mathbb{Q}_l(1)$: it acts via the character with values in $\mathbb{Z}_l^*$ giving its action on the roots of unity. In particular, for $k = \overline{\mathbb{F}}_q$, the Frobenius map $\varphi\colon x \to x^q$ acts by multiplication by $q$.

Let $X$ be an algebraic variety purely of dimension $n$ over $k$. The *orientation sheaf* of $X$ for the $l$-adic cohomology is the constant $\mathbb{Q}_l$-sheaf $\mathbb{Q}_l(n)$. The *fundamental class* is a morphism
$$
\operatorname{Tr}\colon H_c^{2n}(X, \mathbb{Q}_l(n)) \to \mathbb{Q}_l,
$$
or again
$$
\operatorname{Tr}\colon H_c^{2n}(X, \mathbb{Q}_l) \to \mathbb{Q}_l(-n).
$$

**Theorem (2.3) (Poincare duality).** *For $X$ proper and smooth, purely of dimension $n$, the bilinear form*
$$
\operatorname{Tr}(x \cup y)\colon H^i(X, \mathbb{Q}_l) \otimes H^{2n-i}(X, \mathbb{Q}_l) \to \mathbb{Q}_l(-n)
$$
*is a perfect pairing (it identifies $H^i(X, \mathbb{Q}_l)$ with the dual of $H^{2n-i}(X, \mathbb{Q}_l(n))$).*

**(2.4)** Let $X_0$ be a smooth proper algebraic variety over $\mathbb{F}_q$, purely of dimension $n$, and $X$ over $\overline{\mathbb{F}}_q$ the variety deduced from $X_0$ by extension of scalars. The morphism (2.3) is compatible with the action of $\operatorname{Gal}(\overline{\mathbb{F}}_q/\mathbb{F}_q)$. If the $(\alpha_j)$ are the eigenvalues of the geometric Frobenius acting on $H^i(X, \mathbb{Q}_l)$, the eigenvalues of $F$ acting on $H^{2n-i}(X, \mathbb{Q})$ are $(q^n\alpha_j^{-1})$.

**(2.5)** Suppose, for simplicity, that $X$ is connected. The proof of (2.4) is as follows once we transpose to the geometric language instead of the Galois one (see (1.15)).

a) Cup-product puts $H^i(X, \mathbb{Q}_l)$ and $H^{2n-i}(X, \mathbb{Q}_l)$ in perfect duality with values in $H^{2n}(X, \mathbb{Q}_l)$, which has dimension one.

b) Cup-product commutes with forming the inverse image $F^*$ by the Frobenius morphism $F\colon X \to X$.

c) The morphism $F$ is finite of degree $q^n$: on $H^{2n}(X, \mathbb{Q}_l)$, $F^*$ is multiplication by $q^n$.

d) The eigenvalues of $F^*$ therefore have the property (2.4).

<!-- p. 9 -->

**(2.6)** We let $\chi(X) = \sum_i (-1)^i \dim H^i(X, \mathbb{Q}_l)$. When $n$ is odd, the form $\operatorname{Tr}(x \cup y)$ on $H^n(X, \mathbb{Q}_l)$ is alternating; the integer $n\chi(X)$ is therefore always even. It is easy to deduce from $(1.5.4)$ and (2.3), (2.4) that
$$
Z(X_0, t) = \varepsilon q^{\frac{-n\chi(X)}{2}} t^{-\chi(X)} Z(X_0, q^{-n}t^{-n}),
$$
where $\varepsilon = \pm 1$. When $n$ is even, we let $N$ denote the multiplicity of the eigenvalue $q^{n/2}$ of $F^*$ acting on $H^n(X, \mathbb{Q}_l)$ (i.e., the dimension of the corresponding invariant subspace). We have
$$
\varepsilon = \begin{cases}
1, & \text{if } n \text{ is odd} \\
(-1)^N, & \text{if } n \text{ is even.}
\end{cases}
$$
This is the Grothendieck’s formulation of the functional equation for $Z$-functions.

**(2.7)** We will need other forms of the duality theorem. The case of curves will be enough for our purposes. If $\mathcal{F}$ is a $\mathbb{Q}_l$-sheaf on an algebraic variety $X$ over an algebraically closed $k$, we denote by $\mathcal{F}(r)$ the sheaf $\mathcal{F} \otimes \mathbb{Q}_l(r)$. This sheaf is (noncanonically) isomorphic to $\mathcal{F}$.

**Theorem (2.8).** *Let $X$ be smooth purely of dimension $n$ and $\mathcal{F}$ locally constant. We denote by $\mathcal{F}^\vee$ the dual of $\mathcal{F}$. The bilinear form*
$$
\operatorname{Tr}(x \cup y)\colon H^i(X, \mathcal{F}) \otimes H_c^{2n-i}(X, \mathcal{F}^\vee(n)) \to H_c^{2n}(X, \mathcal{F} \otimes \mathcal{F}^\vee(n)) \to H_c^{2n}(X, \mathbb{Q}_l(n)) \to \mathbb{Q}_l
$$
*is a perfect pairing.*

**(2.9)** Suppose that $X$ is connected and that $x$ is a closed point of $X$. The functor $\mathcal{F} \mapsto \mathcal{F}_x$ is an equivalence of the category of locally constant $\mathbb{Q}_l$-sheaves with that of $l$-adic representations of $\pi_1(X, x)$. Via this equivalence, $H^0(X, \mathcal{F})$ can be identified with the invariants of $\pi_1(X, x)$ acting on $\mathcal{F}_x$:
$$
H^0(X, \mathcal{F}) \xrightarrow{\sim} \mathcal{F}_x^{\pi_1(X, x)}. \tag{2.9.1}
$$
According to (2.8), for $X$ smooth and connected of dimension $n$, we have
$$
H_c^{2n}(X, \mathcal{F}) = H^0(X, \mathcal{F}^\vee(n))^\vee = ((\mathcal{F}_x^\vee(n))^{\pi_1(X, x)})^\vee.
$$
The duality exchanges invariants (the largest invariant subspace) with coinvariants (the largest invariant quotient). The formula can be rewritten as
$$
H_c^{2n}(X, \mathcal{F}) = (\mathcal{F}_x)_{\pi_1(X, x)}(-n).
$$
We will use it only for $n = 1$.

**Statement (2.10).** *Let $X$ be a connected smooth curve over an algebraically closed field $k$, $x$ a closed point of $X$, and $\mathcal{F}$ a locally constant $\mathbb{Q}_l$-sheaf. We have*

*(i) $H_c^0(X, \mathcal{F}) = 0$ if $X$ is affine.*

*(ii) $H_c^2(X, \mathcal{F}) = (\mathcal{F}_x)_{\pi_1(X, x)}(-1)$.*

<!-- p. 10 -->

Assertion (i) simply states that $\mathcal{F}$ does not have sections with finite support.

**(2.11)** Let $X$ be a connected smooth projective curve over an algebraically closed field $k$, $U$ an open set in $X$, the complement of the finite set $S$ of closed points of $X$, $j$ the inclusion $U \hookrightarrow X$, and $\mathcal{F}$ a locally constant $\mathbb{Q}_l$-sheaf on $U$. Let $j_*\mathcal{F}$ be the constructible $\mathbb{Q}_l$-sheaf – the direct image of $\mathcal{F}$. Its stalk at $x \in S$ has rank at most the rank of the stalk at a general point; it is the space of invariants of the local monodromy group.

**Theorem (2.12).** *The bilinear form*
$$
\begin{aligned}
\operatorname{Tr}(x \cup y)\colon H^i(X, j_*\mathcal{F}) \otimes H^{2-i}(X, j_*\mathcal{F}^\vee(1)) &\to H^2(X, j_*\mathcal{F} \otimes j_*\mathcal{F}^\vee(1)) \\
&\to H^2(X, j_*(\mathcal{F} \otimes \mathcal{F}^\vee)(1)) \to H_c^2(X, \mathbb{Q}_l(1)) \to \mathbb{Q}_l
\end{aligned}
$$
*is a perfect pairing.*

**(2.13)** It will be convenient to have $\mathbb{Q}_l$-sheaves $\mathbb{Q}_l(r)$ on any scheme $X$ on which $l$ is invertible. The main point is to define $\mathbb{Z}/l^n(1)$. By definition, $\mathbb{Z}/l^n(1)$ is the étale sheaf of $l^n$-th roots of unity.

**(2.14)** *Bibliographical notes for paragraphs 1 and 2.*

A) All the important results in étale cohomology are first proved for torsion sheaves. The extension to $\mathbb{Q}_l$-sheaves is done by passing to formal limits. In what follows, for each theorem mentioned, I will not refer to the reference where it is proved, but to the reference where a similar statement for torsion sheaves is proved.

B) With the exception of the Lefschetz formula and (2.12), all the results in étale cohomology used in this article are all proved in SGA 4. For those already stated, the references are: definition of $H^i$: VII; definition of $H_c^i$: XVII 5.1; finiteness theorem: XIV 1, completed in XVII 5.3; cohomological dimension: X; Poincare duality: XVIII.

C) The relation between the various Frobenius elements ((1.4), (1.11), (1.15)) is explained in detail in SGA 5, XV, §§1, 2.

D) The cohomological interpretation of the $Z$-functions is clearly explained in [1]; however, the Lefschetz formula (1.12) for $X$ a smooth projective curve is used, but not proved. For the proof, one has to consult SGA 5.

E) The form $(2.12)$ of Poincare duality follows from the general result SGA 4, XVIII (3.2.5) (for $S = \operatorname{Spec}(k)$, $X = X$, $K = j_*\mathcal{F}$, $L = \mathbb{Q}_l$) by a local calculation that is not difficult. The statement will be explicitly included in the final version of SGA 5. For the case where we use it (tame ramification of $\mathcal{F}$), we could obtain it by transcendental methods by lifting $X$ and $\mathcal{F}$ to characteristic $0$.

## 3 The main lemma (La majoration fondamentale)

The result of this paragraph was catalyzed by reading Rankin [3].

**(3.1)** Let $U_0$ be a curve over $\mathbb{F}_q$, complement in $\mathbb{P}^1$ of a finite set of closed points, $U$ the curve over $\overline{\mathbb{F}}_q$ deduced from it, $u$ a closed point of $U$, $\mathcal{F}_0$ a locally constant sheaf on $U_0$, and $\mathcal{F}$ its inverse image on $U$.

Let $\beta \in \mathbb{Q}$. We say that $\mathcal{F}_0$ is of *weight* $\beta$ if, for all $x \in |U_0|$, the eigenvalues of $F_x$ acting on $\mathcal{F}_0$ (1.13) are algebraic numbers all of whose complex conjugates are of absolute value $q_x^{\beta/2}$. For example, $\mathbb{Q}_l(r)$ is of weight $-2r$.

<!-- p. 11 -->

**Theorem (3.2).** *We make the following hypotheses:*

*(i) $\mathcal{F}_0$ is equipped with a nondegenerate alternating bilinear form*
$$
\psi\colon \mathcal{F}_0 \otimes \mathcal{F}_0 \to \mathbb{Q}_l(-\beta) \qquad (\beta \in \mathbb{Z}).
$$

*(ii) The image of $\pi_1(U, u)$ in $\operatorname{GL}(\mathcal{F}_u)$ is an open subgroup of the symplectic group $\operatorname{Sp}(\mathcal{F}_u, \psi_u)$.*

*(iii) For all $x \in |U_0|$, the polynomial $\det(1 - F_x t, \mathcal{F}_0)$ has rational coefficients.*

*Then $\mathcal{F}$ is of weight $\beta$.*

We may suppose, and we do suppose, that $U$ is affine and that $\mathcal{F} \neq 0$.

**Lemma (3.3).** *Let $2k$ be an even integer and denote by $\overset{2k}{\otimes}\mathcal{F}_0$ the $2k$-th tensor power of $\mathcal{F}_0$. For $x \in |U_0|$, the logarithmic derivative*
$$
t\frac{d}{dt}\log(\det(1 - F_x t^{\deg(x)}, \overset{2k}{\otimes}\mathcal{F}_0)^{-1})
$$
*is a formal series with positive rational coefficients.*

The hypothesis (iii) ensures that, for all $n$, $\operatorname{Tr}(F_x^n, \mathcal{F}_0) \in \mathbb{Q}$. The number
$$
\operatorname{Tr}(F_x^n, \overset{2k}{\otimes}\mathcal{F}_0) = Tr(F_x^n, \mathcal{F}_0)^{2k}
$$
is a positive rational, and we apply (1.5.3).

**Lemma (3.4).** *The local factors $\det(1 - F_x t^{\deg(x)}, \overset{2k}{\otimes}\mathcal{F}_0)^{-1}$ are formal series with positive rational coefficients.*

The formal series $\log(\det(1 - F_x t^{\deg(x)}, \overset{2k}{\otimes}\mathcal{F}_0)^{-1})$ has constant term zero; from (3.3) all the coefficients are $\geq 0$; the coefficients of its exponential are therefore also positive.

**Lemma (3.5).** *Let $f_i = \sum_n a_{i,n} t^n$ be a sequence of formal series with constant term $1$ and positive real coefficients. We assume that the order of $f_i - 1$ tends to infinity with $i$; and we put $f = \prod_i f_i$. Then the radius of convergence of $f_i$ is at least equal to that of $f$.*

If $f = \sum_n a_n t^n$, we have $a_{i,n} \leq a_n$.

**Lemma (3.6).** *Under the hypotheses of (3.5), if $f$ and the $f_i$ are Taylor expansions of meromorphic functions, then*
$$
\inf\{|z| \mid f(z) = \infty\} \leq \inf\{|z| \mid f_i(z) = \infty\}.
$$

Indeed, these numbers are the radii of absolute convergence.

**(3.7)** For each partition $P$ of $[1, 2k]$ into two element sets $\{i_\alpha, j_\alpha\}$ ($i_\alpha \leq j_\alpha$), we define
$$
\psi_P\colon \overset{2k}{\otimes}\mathcal{F}_0 \to \mathbb{Q}_l(-k\beta)\colon x_1 \otimes \cdots \otimes x_{2k} \to \prod_\alpha \psi(x_{i_\alpha}, x_{j_\alpha}).
$$
Let $x$ be a closed point of $X$. Hypothesis (ii) ensures that the coinvariants of $\pi_1(U, u)$ on $\overset{2k}{\otimes}\mathcal{F}_u$ are the coinvariants on $\overset{2k}{\otimes}\mathcal{F}_u$ of the entire symplectic group ($\pi_1$ is Zariski-dense

<!-- p. 12 -->

in $\operatorname{Sp}$). Let $\mathcal{P}$ be the set of partitions $P$. From H.Weil (*The classical groups*, Princeton University Press, chap. VI, §1), for a suitable $\mathcal{P}' \subset \mathcal{P}$, depending on $\dim(\mathcal{F}_u)$, the $\psi_P$ (for $P \in \mathcal{P}'$) define isomorphisms
$$
(\overset{2k}{\otimes}\mathcal{F}_u)_{\pi_1} = (\overset{2k}{\otimes}\mathcal{F}_u)_{\operatorname{Sp}} \xrightarrow{\sim} \mathbb{Q}_l(-k\beta)^{\mathcal{P}'}.
$$
Let $N$ be the number of elements in $\mathcal{P}'$. According to (2.10) the formula above gives
$$
H_c^2(U, \overset{2k}{\otimes}\mathcal{F}) \simeq \mathbb{Q}_l(-k\beta - 1)^N.
$$
Since $H_c^0(U, \overset{2k}{\otimes}\mathcal{F}) = 0$ , the formula (1.14.3) reduces to
$$
Z(U_0, \overset{2k}{\otimes}\mathcal{F}_0, t) = \frac{\det(1 - F^*t, H^1(U, \overset{2k}{\otimes}\mathcal{F}))}{(1 - q^{k\beta+1}t)^N}.
$$
This $Z$-function is therefore the Taylor series expansion of a rational function having only one pole at $t = 1/q^{k\beta+1}$. We will only use the fact that the poles are of absolute value $t = 1/q^{k\beta+1}$ in $\mathbb{C}$. This could be concluded from general arguments on reductive groups.

If $\alpha$ is an eigenvalue of $F_x$ on $\mathcal{F}_0$, then $\alpha^{2k}$ is an eigenvalue of $F_x$ on $\overset{2k}{\otimes}\mathcal{F}_0$. We now let $\alpha$ be any complex conjugate of $\alpha$. The inverse power $1/\alpha^{2k/\deg(x)}$ is a pole of $\det(1 - F_x t^{\deg(x)}, \overset{2k}{\otimes}\mathcal{F})^{-1}$. After (3.4) and (3.6) we therefore have
$$
|1/q^{k\beta+1}| \leq |1/\alpha^{2k/\deg(x)}|,
$$
or
$$
|\alpha| \leq q_x^{\frac{\beta}{2} + \frac{1}{2k}}.
$$
Letting $k$ tend to infinity, we find that
$$
|\alpha| \leq q_x^{\frac{\beta}{2}}.
$$
On the other hand, the existence of $\psi$ ensures that $q_x^\beta \alpha^{-1}$ is also an eigenvalue, so we have the inequality
$$
|q_x^\beta \alpha^{-1}| \leq q_x^{\beta/2},
$$
or
$$
q_x^{\beta/2} \leq |\alpha|.
$$
This completes the proof.

**Corollary (3.8).** *Let $\alpha$ be an eigenvalue of $F^*$ acting on $H_c^1(U, \mathcal{F})$. Then $\alpha$ is an algebraic number all of whose complex conjugates satisfy*
$$
|\alpha| \leq q^{\frac{\beta+1}{2} + \frac{1}{2}}.
$$

The formula (1.14.3) for $\mathcal{F}_0$ reduces to
$$
Z(U_0, \mathcal{F}, t) = \det(1 - F^*t, H_c^1(U, \mathcal{F})).
$$

<!-- p. 13 -->

The term on the left is a formal series with rational coefficients, in view of its representation as a product and hypothesis (iii). The term on the right is therefore a polynomial with rational coefficients; $1/\alpha$ is a root. This already implies that $\alpha$ is algebraic. To complete the proof, it suffices to show that the infinite product defining $Z(U_0, \mathcal{F}_0, t)$ converges absolutely (and thus is nonzero) for $|t| < q^{\frac{-\beta}{2} - 1}$.

Let $N$ be the rank of $\mathcal{F}$, and put
$$
\det(1 - F_x t, \mathcal{F}) = \prod_{i=1}^N (1 - \alpha_{i,x} t).
$$
According to (3.2), $|\alpha_{i,x}| = q_x^{\beta/2}$. The convergence of the infinite product for Z follows from that of the series
$$
\sum_{i,x} |\alpha_{i,x} t^{\deg(x)}|.
$$
For $|t| = q^{\frac{-\beta}{2} - 1 - \varepsilon}$ ($\varepsilon > 0$), we have
$$
\sum_{i,x} |\alpha_{i,x} t^{\deg(x)}| = N \sum_x q_x^{-1-\varepsilon}.
$$
On the affine line, there are $q^n$ points with coordinate in $\mathbb{F}_{q^n}$, so there are at most $q^n$ closed points of degree $n$. We have therefore
$$
\sum_x q_x^{-1-\varepsilon} \leq \sum_n q^n q^{n(-1-\varepsilon)} = \sum_n q^{-n\varepsilon} < \infty,
$$
which completes the proof.

**Corollary (3.9).** *Let $j_0$ be the inclusion of $U_0$ in $\mathbb{P}_{\mathbb{F}_q}^1$, $j$ that of $U$ into $\mathbb{P}^1$, and $\alpha$ an eigenvalue of $F^*$ acting on $H^1(\mathbb{P}^1, j_*\mathcal{F})$. Then $\alpha$ is an algebraic number all of whose complex conjugates satisfy*
$$
q^{\frac{\beta+1}{2} - \frac{1}{2}} \leq |\alpha| \leq q^{\frac{\beta+1}{2} + \frac{1}{2}}.
$$

A segment of the long exact sequence in cohomology defined by the short exact sequence
$$
0 \to j_!\mathcal{F} \to j_*\mathcal{F} \to j_*\mathcal{F}/j_!\mathcal{F} \to 0
$$
($j_!$ is extension by $0$) can be written
$$
H_c^1(U, \mathcal{F}) \to H^1(\mathbb{P}, j_*\mathcal{F}) \to 0.
$$
Therefore, the eigenvalue $\alpha$ already appears in $H_c^1(U, \mathcal{F})$, and so by (3.8) we have:
$$
|\alpha| \leq q^{\frac{\beta+1}{2} + \frac{1}{2}}.
$$
Poincare duality (2.12) implies that $q^{\beta+1}\alpha^{-1}$ is an eigenvalue, so we have the inequality
$$
|q^{\beta+1}\alpha^{-1}| \leq q^{\frac{\beta+1}{2} + \frac{1}{2}}
$$
and the corollary is proved.

<!-- p. 14 -->

## 4 Lefschetz theory: local theory

**(4.1)** Over $\mathbb{C}$, the local Lefshietz results are the following.

Let $D = \{z \mid |z| < 1\}$ be the unit disk, $D^* = D - \{0\}$, and $f\colon X \to D$ a morphism of analytic spaces. We suppose that

a) $X$ is nonsingular and purely of dimension $n + 1$;

b) $f$ is proper;

c) $f$ is smooth outside the point $x$ of the special fiber $X_0 = f^{-1}(0)$;

d) at $x$, $f$ has a nondegenerate double point.

Let $t \neq 0$ be a point of $D$ and $X_t = f^{-1}(t)$ “the” general fiber. With the previous data we associate:

$\alpha)$ a specialization morphisms $sp\colon H^i(X_0, \mathbb{Z}) \to H^i(X_t, \mathbb{Z})$: $X_0$ is a deformation retract of $X$ and $sp$ is the composite arrow
$$
H^i(X_0, \mathbb{Z}) \xleftarrow{\sim} H^i(X, \mathbb{Z}) \to H^i(X_t, \mathbb{Z})
$$

$\beta)$ the monodromy transformations $T\colon H^i(X_t, \mathbb{Z}) \to H^i(X_t, \mathbb{Z})$, which describe the effect on the singular cycles of $X_t$ of “rotating $t$ around $0$”. This is even an action on $H^i(X_t, \mathbb{Z})$, the stalk at $t$ of the local system $R^i f_*\mathbb{Z}|D^*$, of the positive generator of $\pi_1(D^*, t)$.

Lefschetz theory describes $\alpha)$ and $\beta)$ in terms of the *vanishing cycle* $\delta \in H^n(X_t, \mathbb{Z})$. This cycle is well-defined up to sign. For $i \neq n, n + 1$ we have
$$
H^i(X_0, \mathbb{Z}) \xrightarrow{\sim} H^i(X_t, \mathbb{Z}) \qquad (i \neq n, n + 1).
$$
For $i = n, n + 1$, we have an exact sequence
$$
0 \to H^n(X_0, \mathbb{Z}) \to H^n(X_t, \mathbb{Z}) \xrightarrow{x \mapsto (x, \delta)} \mathbb{Z} \to H^{n+1}(X_0, \mathbb{Z}) \to H^{n+1}(X_t, \mathbb{Z}) \to 0.
$$
For $i \neq n$, the monodromy $T$ is the identity. For $i = n$, we have
$$
Tx = x \pm (x, \delta)\delta.
$$
The values of $\pm$, $T\delta$ and $(\delta, \delta)$ are as follows:
$$
\begin{array}{lcccc}
n \bmod 4 & 0 & 1 & 2 & 3 \\
Tx = x \pm (x, \delta)\delta & - & - & + & + \\
(\delta, \delta) & 2 & 0 & -2 & 0 \\
T\delta & -\delta & \delta & -\delta & \delta
\end{array}
$$
The monodromy transformation preserves the intersection form $\operatorname{Tr}(x \cup y)$ on $H^n(X_t, \mathbb{Z})$. For $n$ odd, it is the symplectic transvection. For $n$ even, it is an orthogonal symmetry.

**(4.2)** Here is the analog of (4.1) in abstract algebraic geometry. The disk $D$ is replaced by the spectrum of a henselian discrete valuation ring $A$ with algebraically closed residue field. Let $S$ be its spectrum, $\eta$ its generic point (spectrum of the field of fractions of $A$), $s$ the closed point (spectrum of the residue field). The role of $t$ is played by the geometric generic point $\bar{\eta}$ (spectrum of the algebraic closure of the field of fractions of $A$).

Let $f\colon X \to S$ be a proper morphism, with $X$ regular purely of dimension $n + 1$. We suppose that $f$ is smooth except for an ordinary double point $x$ in the special fiber $X_s$. Let

<!-- p. 15 -->

$l$ be a prime number different from the residue characteristic $p$ of $S$. Denoting by $X_{\bar{\eta}}$ the geometric generic fiber, we have a specialization morphism
$$
sp\colon H^i(X_s, \mathbb{Q}_l) \xleftarrow{\sim} H^i(X, \mathbb{Q}_l) \to H^i(X_{\bar{\eta}}, \mathbb{Q}_l) \tag{4.2.1}
$$
The role of $T$ is played by the action of the inertia group $I = \operatorname{Gal}(\bar{\eta}/\eta)$ on $H^i(X_{\bar{\eta}}, \mathbb{Q}_l)$ by transport of structure (see (1.15)):
$$
I = \operatorname{Gal}(\bar{\eta}/\eta) \to \operatorname{GL}(H^i(X_{\bar{\eta}}, \mathbb{Q}_l)) \tag{4.2.2}
$$
The data (4.2.1), (4.2.2) fully determine the sheaf $R^i f_*\mathbb{Q}_l$ on $S$.

**(4.3)** Put $n = 2m$ for $n$ even and $n = 2m + 1$ for $n$ odd. (4.2.1) and (4.2.2) can still be described in terms of the vanishing cycle
$$
\delta \in H^n(X_{\bar{\eta}}, \mathbb{Q}_l)(m). \tag{4.3.1}
$$
This cycle is well-defined up to sign.

For $i \neq n, n + 1$, we have
$$
H^i(X_s, \mathbb{Q}_l) \xrightarrow{\sim} H^i(X_{\bar{\eta}}, \mathbb{Q}_l) \quad (i \neq n, n + 1). \tag{4.3.2}
$$
For $i = n, n + 1$, we have an exact sequence
$$
0 \to H^n(X_s, \mathbb{Q}_l) \to H^n(X_{\bar{\eta}}, \mathbb{Q}_l) \xrightarrow{x \mapsto \operatorname{Tr}(x \cup \delta)} \mathbb{Q}_l(m - n) \to H^{n+1}(X_s, \mathbb{Q}_l) \to H^{n+1}(X_{\bar{\eta}}, \mathbb{Q}_l) \to 0 \tag{4.3.3}
$$

The action (4.2.2) of $I$ (local monodromy) is trivial for $i \neq n$. For $i = n$, it is described as follows.

A) *n odd.* - We have a canonical homomorphism
$$
t_l\colon I \to \mathbb{Z}_l(1),
$$
and the action of $\sigma \in I$ is
$$
x \to x \pm t_l(\sigma)(x, \delta)\delta.
$$

B) *n even.* - We will not need this case. We just say that, if $p \neq 2$, there exists a unique character of order two
$$
\varepsilon\colon I \to \{\pm 1\},
$$
and that we have
$$
\begin{aligned}
\sigma x &= x && \text{if}\quad \varepsilon(\sigma) = 1 \\
\sigma x &= x \pm (x, \delta)\delta && \text{if}\quad \varepsilon(\sigma) = -1.
\end{aligned}
$$
The signs $\pm$ in A) and B) are the same as in (4.1).

**(4.4)** These results furnish the following information about $R^i f_*\mathbb{Q}_l$.

a) If $\delta \neq 0$:

1) For $i \neq n$, the sheaf $R^i f_*\mathbb{Q}_l$ is constant.

2) Let $j$ be the inclusion of $\eta$ into $S$. We have
$$
R^i f_*\mathbb{Q}_l = j_*j^*R^i f_*\mathbb{Q}_l.
$$

<!-- p. 16 -->

b) If $\delta = 0$: (This is the exceptional case. Since $(\delta, \delta) = \pm 2$ for $n$ even, it can happen only for $n$ odd.)

1) For $i \neq n + 1$, the sheaf $R^i f_*\mathbb{Q}_l$ is constant.

2) Let $\mathbb{Q}_l(m - n)_s$ be the sheaf $\mathbb{Q}_l(m - n)$ on $\{s\}$, extended by zero on $S$. Then we have an exact sequence
$$
0 \to \mathbb{Q}_l(m - n)_s \to R^{n+1} f_*\mathbb{Q}_l \to j_*j^*R^{n+1} f_*\mathbb{Q}_l \to 0,
$$
where $j_*j^*R^{n+1} f_*\mathbb{Q}_l$ is a constant sheaf.

## 5 Lefschetz theory: global theory

**(5.1)** Over $\mathbb{C}$, the results of Lefschetz are the followsing. Let $\mathbb{P}$ be a projective space of dimension $\geq 1$ and $\breve{\mathbb{P}}$ the dual projective space; its points parametrize the hyperplanes of $\mathbb{P}$ and we denote by $H_t$ the hyperplane defined by $t \in \breve{\mathbb{P}}$. If $A$ is a linear subspace of codimension $2$ in $\mathbb{P}$, the hyperplanes containing $A$ are parameterized by points of a line $D \subset \breve{\mathbb{P}}$, the *dual* of $A$. These hyperplanes $(H_t)_{t \in D}$ form the *pencil with axis $A$*.

Let $X \subset \mathbb{P}$ be a connected nonsingular projective variety of dimension $n + 1$. Let $\widetilde{X} \subset X \times D$ be the set of pairs $(x, t)$ such that $x \in H_t$. The projections to the first and second coordinates form a diagram
$$
\begin{array}{ccc}
X & \xleftarrow{\pi} & \widetilde{X} \\
& & \downarrow f \\
& & D
\end{array} \tag{5.1.1}
$$
The fiber of $f$ at $t \in D$ is the hyperplane section $X_t = X \cap H_t$ of $X$.

Fix $X$, and take $A$ sufficiently general. Then:

A) $A$ is transverse to $X$ and $\widetilde{X}$ is the blowing up of $X$ along $A \cap X$. In particular, $\widetilde{X}$ is nonsingular.

B) There exists a finite subset $S$ of $D$ and, for each $s \in S$, a point $x_s \in X_s$ such that $f$ is smooth outside $x_s$.

C) The $x_s$ are nondegenerate critical points of $f$.

Therefore, for each $s \in S$, local Lefschetz theory (4.1) applies to a small disk $D_s$ around $s$ and to $f^{-1}(D_s)$.

**(5.2)** Let $U = D - S$. Let $u \in U$, and choose disjoint loops $(\gamma_s)_{s \in S}$ starting from $u$, with $\gamma_s$ turning once around $s$:
These loops generate the fundamental group $\pi_1(U, u)$. This group acts on $H^i(X_u, \mathbb{Z})$, the stalk at $u$ of the local system $R^i f_*\mathbb{Z}|U$. According to the local theory (4.1), to each $s \in S$ corresponds a vanishing cycle $\delta_s \in H^n(X_u, \mathbb{Z})$; these cycles depend on the choice of the $\gamma_s$. For $i \neq n$, the action of $\pi_1(U, u)$ on $H^i(X_u, \mathbb{Z})$ is trivial. For $i = n$, we have
$$
\gamma_s x = x \pm (x, \delta_s)\delta_s \tag{5.2.1}
$$

Let $E$ be the subspace of $H^n(X_u, \mathbb{Q})$ generated by the $\delta_s$ (vanishing part of the cohomology).

**Proposition (5.3).** *$E$ is stable under the action of the monodromy group $\pi_1(U, u)$. The orthogonal complement $E^\perp$ of $E$ (for the intersection form $\operatorname{Tr}(x \cup y)$) is the subspace of invariants of the monodromy in $H^n(X_u, \mathbb{Q})$.*

<!-- p. 17 -->

[Figure: base point $u$ with three disjoint loops starting at $u$ and turning once counterclockwise around three points marked $\times$, one of which is labeled $x_s$ with loop $\gamma_s$.]

The $\gamma_s$ generate the monodromy group, so this is clear from (5.2.1).

**Theorem (5.4).** *The vanishing cycles $\pm\delta_s$ (taken up to sign) are conjugate under the action of $\pi_1(U, u)$.*

Let $\breve{X} \subset \breve{\mathbb{P}}$ be the dual variety of $X$; it is the set of $t \in \breve{\mathbb{P}}$ such that $H_t$ is tangent to $X$, i.e., such that $X_t$ is singular or $X \subset H_t$. The variety $\breve{X}$ is irreducible. Let $Y \subset X \times \breve{\mathbb{P}}$ be the space of pairs $(x, t)$ such that $x \in H_t$. We have a diagram
$$
\begin{array}{ccc}
X & \longleftarrow & Y \\
& & \downarrow g \\
& & \breve{\mathbb{P}}
\end{array}
$$
The fiber of $g$ at $t \in \breve{\mathbb{P}}$ is the hyperplane section $X_t = X \cap H_t$ of $X$, and $g$ is smooth on the complement of the inverse image of $\breve{X}$.

We recover the situation of (5.1) by replacing $\breve{\mathbb{P}}$ with the line $D \subset \breve{\mathbb{P}}$ and $Y$ with $g^{-1}(D)$. We have $S = D \cap \breve{X}$. According to a theorem of Lefschetz, for $D$ sufficiently general, the map
$$
\pi_1(D - S, u) \to \pi_1(\breve{\mathbb{P}} - \breve{X}, u)
$$
is surjective. It suffices to show that the $\pm\delta_s$ are conjugate under $\pi_1(\breve{\mathbb{P}} - \breve{X})$.

For $x$ in the smooth locus of codimension $1$ of $\breve{X}$, let $ch$ be the path from $t$ to $x$ in $\breve{\mathbb{P}} - \breve{X}$ and $\gamma_x$ the loop that follows $ch$ until the neighborhood of $\breve{X}$, turns once around $\breve{X}$, and then returns to $t$ by $ch$. The loops $\gamma_x$ (for various $ch$) are mutually conjugate. Since $\breve{X}$ is irreducible, two points in the smooth locus of $\breve{X}$ can always be joined, in $\breve{X}$, by a path that does not leave the smooth locus. It follows that the conjugacy class of $\gamma_x$ does not depend on $x$. In particular, the $\gamma_s$ are mutually conjugate. We see from (5.2.1) that this implies the conjugacy of $\pm\delta_s$.

**Corollary (5.5).** *The action of $\pi_1(U, u)$ on $E/(E \cap E^\perp)$ is absolutely irreducible.*

Let $F \subset E \otimes \mathbb{C}$ be a subspace stable under the monodromy. If $F \not\subset (E \cap E^\perp) \otimes \mathbb{C}$, there exists an $x \in F$ and an $s \in S$ such that $(x, \delta_s) \neq 0$. We then have
$$
\gamma_s x - x = \pm(x, \delta_s)\delta_s \in F,
$$
and $\delta_s \in F$. According to (5.4), all the $\delta_s$ are then in $F$ and $F = E$. This proves (5.5).

**(5.6)** These results transpose as follows into abstract algebraic geometry. Let $\mathbb{P}$ be a projective space of dimension $> 1$ over an algebraically closed field $k$ of characteristic $p$

<!-- p. 18 -->

and $X \subset \mathbb{P}$ a connected projective nonsingular variety of dimension $n + 1$. For $A$ a linear subspace of codimension $2$ we define $D$, the pencil $(H_t)_{t \in D}$, $\widetilde{X}$, and the diagram (5.1.1) as in (5.1). We say that the $(H_t)_{t \in D}$ form a *Lefschetz pencil* of hyperplane sections if the following conditions are satisfied:

A) The axis $A$ is transverse to $X$. The variety $\widetilde{X}$ is then obtained from $X$ by blowing up along $A \cap X$, and it is smooth.

B) There is a finite subset $S$ of $D$ and, for each $s \in S$, a point $x_s \in X_s$ such that $f$ is smooth outside $x_s$.

C) $x_s$ is an ordinary quadratic singular point of $X_s$.

For each $s \in S$, the local Lefschetz theory of §4 applies to the spectrum $D_s$ of the henselization of the local ring of $D$ at $s$ and to $\widetilde{X}_{D_s} = \widetilde{X} \times_D D_s$.

**(5.7)** Let $N$ be the dimension of $\mathbb{P}$, $r$ an integer $\geq 1$, and $\iota_{(r)}$ the embedding of $\mathbb{P}$ into the projective space of dimension $\binom{N+r}{N} - 1$, the homogeneous coordinates of which are the monomials of degree $r$ in the homogeneous coordinates of $\mathbb{P}$. The hyperplane sections of $\iota_{(r)}(\mathbb{P})$ are the hypersurfaces of degree $r$ of $\mathbb{P}$.

For $p \neq 0$ it might happen that there is no such pencil of hyperplane sections of $X$ that is Lefschetz. However, if $r \geq 2$ and we replace the projective embedding $\iota_1\colon X \hookrightarrow \mathbb{P}$ by $\iota_r = \iota_{(r)} \circ \iota_1$, then, in this new embedding, any general enough pencil of hypersurface sections of degree $r$ on $X$ is always Lefschetz.

**(5.8)** For the rest of this discussion, we will study the Lefschetz pencil of hyperplane sections of $X$, *excluding the case $p = 2$, $n$ even*. The case where $n$ is odd will suffice for our purposes. We put $U = D - S$. Take $u \in U$ and $l$ a prime number $\neq p$. The local results of §4 show that $R^n f_*\mathbb{Q}_l$ is *tamely ramified* at each $s \in S$. The tame fundamental group of $U$ is a quotient of the profinite completion of the corresponding transcendental fundamental group (lifting to characteristic $0$ of the tame coverings and the Riemann existence theorem). The algebraic situation is therefore very similar to the transcendental situation, and the transfer of Lefschetz’s results can be done by standard arguments. In the proof of (5.4), the theorem of Lefschetz for $\pi_1$ is replaced by the theorem of Bertini, and we have to invoke Abhyankar’s lemma to control the ramification of $R^*g_*\mathbb{Q}_l$ along the smooth locus of codimension one in $\breve{X}$.

The results are as follows:

a) *If the vanishing cycles are nonzero:*

1) For $i \neq n$, the sheaf $R^i f_*\mathbb{Q}_l$ is constant.

2) Let $j$ be the inclusion of $U$ in $D$. We have
$$
R^n f_*\mathbb{Q}_l = j_*j^*R^n f_*\mathbb{Q}_l.
$$

3) Let $E \subset H^n(X_u, \mathbb{Q}_l)$ be the subspace of the cohomology generated by the vanishing cycles. This subspace is stable under $\pi_1(U, u)$ and
$$
E^\perp = H^n(X_u, \mathbb{Q}_l)^{\pi(U, u)}.
$$
The representation of $\pi_1(U, u)$ on $E/(E \cap E^\perp)$ is absolutely irreducible and the image of $\pi_1$ in $\operatorname{GL}(E/(E \cap E^\perp))$ is generated (topologically) by the maps $x \mapsto x \pm (x, \delta_s)\delta_s$ ($s \in S$) (the $\pm$ sign is determined as in (4.1)).

b) *If the vanishing cycles are zero:* (This is an exceptional case. Since $(\delta, \delta) = \pm 2$ for $n$ even, it can only happen for $n$ odd: $n = 2m + 1$. Note that if one vanishing cycle is zero, they all are, because of conjugacy.)

<!-- p. 19 -->

1) For $i \neq n + 1$, the sheaf $R^i f_*\mathbb{Q}_l$ is constant.

2) We have an exact sequence
$$
0 \to \underset{s \in S}{\oplus} \mathbb{Q}_l(m - n)_s \to R^{n+1} f_*\mathbb{Q}_l \to \mathcal{F} \to 0
$$
with $\mathcal{F}$ constant.

3) $E = 0$.

**(5.9)** The subspace $E \cap E^\perp$ of $E$ is the kernel of the restriction to $E$ of the intersection form $\operatorname{Tr}(x \cup y)$. Therefore, this form induces a bilinear nondegenerate form
$$
\psi\colon E/(E \cap E^\perp) \otimes E/(E \cap E^\perp) \to \mathbb{Q}_l(-n),
$$
skew-symmetric for $n$ odd and symmetric for $n$ even. This form is preserved by the monodromy; for $n$ odd, therefore, the monodromy representation induces
$$
\rho\colon \pi_1(U, u) \to \operatorname{Sp}(E/(E \cap E^\perp), \psi).
$$

**Theorem (5.10) (Kajdan-Margulis).** *The image of $\rho$ is open.*

The image of $\rho$ is a compact, hence analytic $l$-adic, subgroup of $\operatorname{Sp}(E/(E \cap E^\perp), \psi)$. It suffices to show that its Lie algebra $\mathfrak{L}$ equals $\mathfrak{sp}(E/(E \cap E^\perp), \psi)$. The transcendental analog of this Lie algebra is the Lie algebra of the Zariski closure of the monodromy group.

We deduce from (5.8) that $\mathfrak{L}$ is generated by transformations with square zero
$$
N_s\colon x \mapsto (x, \delta_s)\delta_s \quad (s \in S)
$$
and that $E/(E \cap E^\perp)$ is an absolutely irreducible representation of $\mathfrak{L}$. The theorem follows from the next lemma.

**Lemma (5.11).** *Let $V$ be a finite dimensional vector space over a field $k$ of characteristic zero, and $\psi$ a nondegenerate skew-symmetric form on a Lie subalgebra $\mathfrak{L}$ of the Lie algebra $\mathfrak{sp}(V, \eta)$. We suppose that:*

*(i) $V$ is a simple representation of $\mathfrak{L}$.*

*(ii) $\mathfrak{L}$ is generated by the family of endomorphisms of $V$ of the form $x \mapsto \psi(x, \delta)\delta$.*

*Then $\mathfrak{L} = \mathfrak{sp}(V, \psi)$.*

We may, and do, assume that $V$, therefore $\mathfrak{L}$, is nonzero. Let $W \subset V$ be the set of $\delta \in V$ such that $N(\delta)\colon x \mapsto \psi(x, \delta)\delta$ is in $\mathfrak{L}$.

a) $W$ is stable under homotheties (because $\mathfrak{L}$ is a vector subspace of $\mathfrak{gl}(V)$).

b) If $\delta \in W$, $\exp(\lambda N(\delta))$ is an automorphism of $(V, \psi, \mathfrak{L})$, and therefore transforms $W$ to itself. If $\delta', \delta'' \in W$, we therefore have
$$
\exp(\lambda N(\delta'))\delta'' = \delta'' + \lambda\psi(\delta'', \delta')\delta' \in W;
$$
if $\psi(\delta', \delta'') \neq 0$, then the vector subspace spanned by $\delta'$ and $\delta''$ lies in $W$.

c) It follows that $W$ is the union of its maximal linear subspaces $W_\alpha$, and that they are pairwise orthogonal. Each $W_\alpha$ is therefore stable under the $N(\delta)$ ($\delta \in W$), so it is stable under $\mathfrak{L}$. By hypothesis (i), $W_\alpha = V$ and $\mathfrak{L}$ contains all $N(\delta)$ for $\delta \in V$. We conclude by noting that Lie algebra $\mathfrak{sp}(V, \psi)$ is generated by the $N(\delta)$, ($\delta \in V$).

<!-- p. 20 -->

*Remark* **(5.12)** (not necessary for what follows). — It is now easy to prove (1.6) for a hypersurface of odd dimension $n$ in $\mathbb{P}_{\mathbb{F}_q}^{n+1}$.

Let $X_0$ be such a hypersurface and $\overline{X}_0$ the hypersurface over $\overline{\mathbb{F}}_q$ deduced from $X_0$ by extension of scalars. We have
$$
H^i(\overline{X}_0, \mathbb{Q}_l) = \mathbb{Q}_l(-i) \qquad (0 \leq i \leq n);
$$
$H^i(\overline{X}_0, \mathbb{Q}_l(i))$ is generated by the $i$-th cup power of $\eta$, the cohomology class $c_1(\mathcal{O}(1))$ of a hyperplane section. Therefore, we have
$$
Z(X_0, t) = \frac{\det(1 - F^*t, H^n(\overline{X}_0, \mathbb{Q}_l)}{\prod_{i=0}^n (1 - q^i t)}
$$
and $\det(1 - F^*t, H^n(\overline{X}_0, \mathbb{Q}_l)$ is a polynomial with integer coefficients independent of $l$.

We let $X_0$ vary in a Lefschetz pencil of hypersurfaces defined over $\mathbb{F}_q$ (see (5.7) for $X = \mathbb{P}^{n+1}$; the existence of such a pencil is not clear; if we wanted to complete the argument sketched here, we would have to use the arguments that will be given in (7.1). One checks that $E$ coincides here with the whole $H^n$, and (3.2) proves the Weil conjecture for all the hypersurfaces of the pencil, in particular for $X_0$.

**(5.13)** *Bibliographical notes for §§4 and 5.*

A) The results of Lefschetz (4.1) and (5.1) to (5.5) are contained in his book [2]. For the local theory (4.1), it may be more convenient to consult SGA 7, XIV (3.2).

B) The results of §4 are proved in Exposés XIII, XIV, and XV of SGA 7.

C) (5.7) is proved in SGA 7, XVII.

D) (5.8) is proved in SGA 7, XVIII. The irreducibility theorem is proved there for $E$, but only under the hypothesis that $E \cap E^\perp = \{0\}$. The proof of the general case (for $E/(E \cap E^\perp)$) is similar.

## 6 The rationality theorem

**(6.1)** Let $\mathbb{P}_0$ be a projective space of dimension $\geq 1$ over $\mathbb{F}_q$, $X_0 \subset \mathbb{P}_0$ a projective nonsingular variety, $A_0 \subset \mathbb{P}_0$ a linear subspace of codimension two, $D_0 \subset \breve{\mathbb{P}}_0$ the dual line, $\overline{\mathbb{F}}_q$ the algebraic closure of $\mathbb{F}_q$, and $\mathbb{P}, X, A, D$ the varieties over $\overline{\mathbb{F}}_q$ obtained from $\mathbb{P}_0, X_0, A_0, D_0$ by extension of scalars. The diagram (5.1.1) from (5.6) comes from a similar diagram over $\mathbb{F}_q$:
$$
\begin{array}{ccc}
X_0 & \xleftarrow{\pi_0} & \widetilde{X}_0 \\
& & \downarrow f_0 \\
& & D_0
\end{array} \tag{6.1.1}
$$

We suppose that $X$ is connected of *even* dimension $n + 1 = 2m + 2$ and that the pencil of hyperplane sections of $X$ defined by $D$ is a *Lefschetz pencil*. The set $S$ of $t \in D$ such that $X_t$ is singular and defined over $\mathbb{F}_q$ comes from $S_0 \subset D_0$. We put $U_0 = D_0 - S_0$ and $U = D - S$.

Let $u \in U$. The vanishing part of the cohomology $E \subset H^n(X_u, \mathbb{Q}_l)$ is stable under $\pi_1(U, u)$, so it is defined over $U$ by a local subsystem $\mathcal{E}$ of $R^n f_*\mathbb{Q}_l$. The latter is defined

<!-- p. 21 -->

over $\mathbb{F}_q$: $R^i f_*\mathbb{Q}_l$ is the inverse image of the $\mathbb{Q}_l$-sheaf $R^i f_{0*}\mathbb{Q}_l$ on $D_0$ and, on $U$, $\mathcal{E}$ is the inverse image of a local subsystem
$$
\mathcal{E}_0 \subset R^n f_{0*}\mathbb{Q}_l.
$$

Cup product is a skew-symmetric form
$$
\psi\colon R^n f_{0*}\mathbb{Q}_l \otimes R^n f_{0*}\mathbb{Q}_l \to \mathbb{Q}_l(-n).
$$
Denoting by $\mathcal{E}_0^\perp$ the orthogonal complement of $\mathcal{E}_0$ relative to $\psi$ on $R^n f_{0*}\mathbb{Q}_l|U_0$, we see that $\psi$ induces a a perfect pairing
$$
\psi\colon \mathcal{E}_0/(\mathcal{E}_0 \cap \mathcal{E}_0^\perp) \otimes \mathcal{E}_0/(\mathcal{E}_0 \cap \mathcal{E}_0^\perp) \to \mathbb{Q}_l(-n).
$$

**Theorem (6.2).** *For all $x \in |U_0|$, the polynomial $\det(1 - F_x^*t, \mathcal{E}_0/(\mathcal{E}_0 \cap \mathcal{E}_0^\perp))$ has rational coefficients.*

**Corollary (6.3).** *Let $j_0$ be the inclusion of $U_0$ in $D_0$ and $j$ that of $U$ in $D$. The eigenvalues of $F^*$ acting on $H^1(D, j_*\mathcal{E}_0/(\mathcal{E}_0 \cap \mathcal{E}_0^\perp))$ are algebraic numbers all of whose complex conjugates $\alpha$ satisfy*
$$
q^{\frac{n+1}{2} - \frac{1}{2}} \leq |\alpha| \leq q^{\frac{n+1}{2} + \frac{1}{2}}.
$$

After (5.10) and (6.2), the hypotheses of (3.2) are indeed satisfied for
$$
(U_0, \mathcal{E}_0/(\mathcal{E}_0 \cap \mathcal{E}_0^\perp), \psi)
$$
for $\beta = n$, and we can apply (3.9).

**Lemma (6.4).** *Let $\mathcal{G}_0$ be a locally constant $\mathbb{Q}_l$-sheaf on $U_0$ such that its inverse image $\mathcal{G}$ on $U$ is a constant sheaf. Then there exist units $\alpha_i$ in $\overline{\mathbb{Q}}_l$ such that for each $x \in |U_0|$ we have*
$$
\det(1 - F_x^*t, \mathcal{G}_0) = \prod_i (1 - \alpha_i^{\deg(x)}t).
$$

The lemma expresses the fact that $\mathcal{G}_0$ is the inverse image of a sheaf on $\operatorname{Spec}(\mathbb{F}_q)$, namely, its direct image on $\operatorname{Spec}(\mathbb{F}_q)$ . The latter can be identified with an $l$-adic representation $G_0$ of $\operatorname{Gal}(\overline{\mathbb{F}}_q/\mathbb{F}_q)$, and we have
$$
\det(1 - Ft, G_0) = \prod_i (1 - \alpha_i t).
$$

Lemma (6.4) applies to $R^i f_{0*}\mathbb{Q}_l$, ($i \neq n$), to $R^n f_{0*}\mathbb{Q}_l/\mathcal{E}_0$, and to $\mathcal{E}_0 \cap \mathcal{E}_0^\perp$ .

For $x \in |U_0|$, the fiber $X_x = f_0^{-1}(x)$ is a variety over the finite field $k(x)$. If $\bar{x}$ is a point of $U$ above $x$, $X_{\bar{x}}$ is obtained from $X_x$ by extension of scalars from $k(x)$ to the algebraic closure $k(\bar{x}) = \overline{\mathbb{F}}_q$ and $H^i(X_{\bar{x}}, \mathbb{Q}_l)$ is the stalk of $R^i f_*\mathbb{Q}_l$ at $\bar{x}$. The formula (1.5.4) for the variety $X_x$ over $k(x)$ can therefore be written
$$
Z(X_x, t) = \prod_i \det(1 - F_x^*t, R^i f_{0*}\mathbb{Q}_l)^{(-1)^{i+1}}
$$
and $Z(X_x, t)$ is the product of
$$
Z^f = \det(1 - F_x^*t, R^n f_{0*}\mathbb{Q}_l/\mathcal{E}_0) \cdot \det(1 - F_x^*t, \mathcal{E}_0 \cap \mathcal{E}_0^\perp) \cdot \prod_{i \neq n} \det(1 - F_x^*t, R^i f_{0*}\mathbb{Q}_l)^{(-1)^{i+1}}
$$

<!-- p. 22 -->

with
$$
Z^m = \det(1 - F_x^*t, \mathcal{E}_0/(\mathcal{E}_0 \cap \mathcal{E}_0^\perp)).
$$
Put $\mathcal{F}_0 = \mathcal{E}_0/(\mathcal{E}_0 \cap \mathcal{E}_0^\perp)$ and $\mathcal{F} = \mathcal{E}/(\mathcal{E} \cap \mathcal{E}^\perp)$, and apply (6.4) to the factors of $Z^f$. We find that there exist $l$-adic units $\alpha_i$ ($1 \leq i \leq N$) and $\beta_j$ ($1 \leq j \leq M$) in $\overline{\mathbb{Q}}_l$ such that for all $x \in |U_0|$,
$$
Z(X_x, t) = \frac{\prod_i (1 - \alpha_i^{\deg(x)}t)}{\prod_j (1 - \beta_j^{\deg(x)}t)} \cdot \det(1 - F_x^*t, \mathcal{F}_0),
$$
and in particular the term on the right is in $\mathbb{Q}(t)$. If some $\alpha_i$ coincides with a $\beta_j$, we can simultaneously delete $\alpha_i$ from the family of $\alpha$ and $\beta_j$ from the family of $\beta$. Therefore, we may and do suppose that $\alpha_i \neq \beta_j$ for all $i$ and all $j$.

**(6.5)** It suffices to prove that the polynomials $\prod_i (1 - \alpha_i t)$ and $\prod_j (1 - \beta_j t)$ have rational coefficients, i.e., that the family of $\alpha_i$ (resp. the family of $\beta_j$) is defined over $\mathbb{Q}$. We will deduce this from the following propositions.

**Proposition (6.6).** *Let $(\gamma_i)_{1 \leq i \leq P}$ and $(\delta_j)_{1 \leq j \leq Q}$ be two families of $l$-adic units in $\overline{\mathbb{Q}}_l$. Suppose that $\gamma_i \neq \delta_j$. If $K$ is a sufficiently large finite set of integers $\neq 1$, and $L$ is a sufficiently large nowhere dense subset of $|U_0|$, then, if $x \in |U_0|$ satisfies $k \nmid \deg(x)$ (for all $k \in K$) and $x \notin L$, the denominator of the fraction,*
$$
\frac{\det(1 - F_x^*t, \mathcal{F}_0) \cdot \prod_i (1 - \gamma_i^{\deg(x)}t)}{\prod_j (1 - \delta_j^{\deg(x)}t)}, \tag{6.6.1}
$$
*written in irreducible form, is $\prod_j (1 - \delta_j^{\deg(x)}t)$.*

The proof will be given in (6.10-13). According to (6.7) below, (6.6) provides an intrinsic description of the family of $\delta_j$ in terms of the family of rational fractions (6.6.1) for $x \in |U_0|$.

**Lemma (6.7).** *Let $K$ be a finite set of integers $\neq 1$ and $(\delta_j)_{1 \leq j \leq Q}$ and $(\varepsilon_j)_{1 \leq j \leq Q}$ two families of elements of a field. If, for all sufficiently large $n$ not divisible by any of the $k \in K$, the family $(\delta_j^n)$ coincides with the family $(\varepsilon_j^n)$ (up to order), then the family $(\delta_j)$ coincides with the family $(\varepsilon_j)$ (up to order).*

We proceed by induction on $Q$. The set of integers $n$ such that $\delta_Q^n = \varepsilon_j^n$ is an ideal $(n_j)$. We prove that there exists a $j_0$ such that $\delta_Q = \varepsilon_{j_0}$. Otherwise the $n_j$ would be distinct from $1$ and there would be arbitrarily large integers $n$, not divisible by any of the $n_j$ nor by any of the $k \in K$. We would have $\delta_Q^n \neq \varepsilon_j^n$ and this contradicts the hypothesis. So there exists a $j_0$ such that $\delta_Q = \varepsilon_{j_0}$.We conclude by applying the induction hypothesis to the families $(\delta_j)_{j \neq Q}$ and $(\varepsilon_j)_{j \neq j_0}$.

**Proposition (6.8).** *Let $(\gamma_i)_{1 \leq i \leq P}$ and $(\delta_j)_{1 \leq j \leq Q}$ be two families of $p$-adic units in $\overline{\mathbb{Q}}_l$, $R(t) = \prod_i (1 - \gamma_i t)$, and $S(t) = \prod_j (1 - \delta_j t)$. Suppose that for all $x \in |U_0|$, the product $\prod_j (1 - \delta_j^{\deg(x)}t)$ divides*
$$
\prod_i (1 - \gamma_i^{\deg(x)}t) \cdot \det(1 - F_x^*t, \mathcal{F}_0).
$$
*Then $S(t)$ divides $R(t)$.*

<!-- p. 23 -->

Remove from the families $(\gamma_i)$ and $(\delta_j)$ pairs of common elements until they satisfy the hypothesis of (6.6). Apply (6.6). By hypothesis, the rational fractions (6.6.1) are polynomials. Therefore, no $\delta$ survives, which means that $S(t)$ divides $R(t)$.

**(6.9)** We prove (6.5) and (6.2) (modulo (6.6)). Put $(\gamma_i) = (\alpha_i)$ and $(\delta_i) = (\beta_i)$ in (6.6). We get an intrinsic characterization of the family of $\beta_j$ in terms of the family of rational functions $Z(X_x, t)$ ($x \in |U_0|$). These being in $\mathbb{Q}(t)$, the family of $\beta_j$ is defined over $\mathbb{Q}$.

The polynomials $\prod_i (1 - \alpha_j^{\deg(x)}t) \cdot \det(1 - F_x^*t, \mathcal{F}_0)$ are therefore in $\mathbb{Q}[t]$. Proposition (6.8) provides an intrinsic description of the family of $\alpha_i$ in terms of this family of polynomials. The family of $\alpha_i$ is thus defined over $\mathbb{Q}$.

**(6.10)** *Preliminaries.*— Let $u \in U$, and let $\mathcal{F}_u$ be the stalk of $\mathcal{F}$ at $u$. The arithmetic fundamental group $\pi_1(U_0, u)$, the extension of $\widehat{\mathbb{Z}} = \operatorname{Gal}(\overline{\mathbb{F}}/\mathbb{F})$ (generator: $\varphi$) by the geometric fundamental group $\pi_1(U, u)$, acts on $\mathcal{F}_u$ by symplectic similitudes
$$
\rho\colon \pi_1(U_0, u) \to \operatorname{CSp}(\mathcal{F}_u, \psi).
$$
We denote by $\mu(g)$ the multiplier of the symplectic similitude $g$. Let
$$
H \subset \widehat{\mathbb{Z}} \times C\operatorname{Sp}(\mathcal{F}_u, \psi)
$$
be the subgroup defined by the equation
$$
q^{-n} = \mu(g)
$$
($q$ being an $l$-adic unit, $q^n \in \mathbb{Q}_l^*$ is defined for all $n \in \widehat{\mathbb{Z}}$). The fact that $\psi$ has values in $\mathbb{Q}_l(-n)$ can be expressed by saying that the map from $\pi_1$ to $\widehat{\mathbb{Z}} \times \operatorname{CSp}$, with coordinates the canonical projection to $\widehat{\mathbb{Z}}$ and $\rho$, factors through
$$
\rho_1\colon \pi_1(U_0, u) \to H.
$$

**Lemma (6.11).** *The image $H_1$ of $\rho_1$ is open in $H$.*

Indeed, $\pi_1(U_0, u)$ projects *onto* $\widehat{\mathbb{Z}}$, and the image of $\pi_1(U, u) = \operatorname{Ker}(\pi_1(U_0, u) \to \widehat{\mathbb{Z}})$ in $\operatorname{Sp}(\mathcal{F}_u, \psi) = \operatorname{Ker}(H \to \widehat{\mathbb{Z}})$ is open (5.10).

**Lemma (6.12).** *For $\delta \in \overline{\mathbb{Q}}_l$ an $l$-adic unit, the set $Z$ of $(n, g) \in H_1$ such that $\delta^n$ is an eigenvalue of $g$ is closed of measure $0..$*

It is clear that $Z$ is closed. For each $n \in \widehat{\mathbb{Z}}$, let $\operatorname{CSp}_n$ be the set of $g \in \operatorname{CSp}(\mathcal{F}_u, \psi)$ such that $\mu(g) = q^{-n}$ and let $Z_n$ be the set of $g \in \operatorname{CSp}_n$ such that $\delta^n$ is an eigenvalue of $g$. Then $\operatorname{CSp}_n$ is a homogeneous space for $\operatorname{Sp}$ and one can check that $Z_n$ is a proper algebraic subspace, thus, of measure $0$. After (6.11), $H_1 \cap (\{n\} \times Z_n)$ is therefore of measure $0$ in the inverse image in $H_1$ of $n$ and we can apply Fubini to the projection $H_1 \to \widehat{\mathbb{Z}}$.

**(6.13)** Let us prove (6.6). For each $i$ and $j$, the set of integers $n$ such that $\gamma_i^n = \delta_j^n$ is the set of multiples of a fixed integer $n_{ij}$ (we do not exclude $n_{ij} = 0$). By hypothesis, $n_{ij} \neq 1$.

After (6.12) and the Chebotarev density theorem, the set of $x \in |U_0|$ such that $\beta_j^{\deg(x)}$ is an eigenvalue of $F_x^*$ acting on $\mathcal{F}_0$ is nowhere dense. We take for $K$ the set of $n_{ij}$ and for $L$ the set of $x$ as above.

<!-- p. 24 -->

## 7 Completion of the proof of (1.7)

**Lemma (7.1).** *Let $X_0$ be an absolutely irreducible nonsingular projective variety of even dimension $d$ over $\mathbb{F}_q$. Let $X$ over $\overline{\mathbb{F}}_q$ be obtained from $X_0$ by extension of scalars, and let $\alpha$ an eigenvalue of $F^*$ acting on $H^d(X, \mathbb{Q}_l)$. Then $\alpha$ is an algebraic number, all of whose complex conjugates, again denoted by $\alpha$, satisfy*
$$
q^{\frac{d}{2} - \frac{1}{2}} \leq |\alpha| \leq q^{\frac{d}{2} + \frac{1}{2}} \tag{7.1.1}
$$

We proceed by induction on $d$ (always assumed even). The case $d = 0$ is trivial even without assuming that $X_0$ is absolutely irreducible; we assume from now on $d \geq 2$. We put $d = n + 1 = 2m + 2$.

If $\mathbb{F}_{q^r}$ is an extension of degree $r$ of $\mathbb{F}_q$ and $X_0'/\mathbb{F}_{q^r}$ is obtained from $X_0/\mathbb{F}_q$ by extension of scalars, the statement (7.1) for $X_0/\mathbb{F}_q$ is equivalent to (7.1) for $X_0'/\mathbb{F}_{q^r}$; in the same way as $q$ is replaced by $q^r$, the eigenvalues of $F^*$ are replaced by their $r$-th powers.

According to (5.7), in a suitable projective embedding $i\colon X \to \mathbb{P}$, $X$ admits a Lefschetz pencil of hyperplane sections. The preceding remark allows us to assume that the pencil is defined over $\mathbb{F}_q$ (once we replace $\mathbb{F}_q$ by a finite extension).

Suppose therefore that there exists a projective embedding $X_0 \to \mathbb{P}_0$ and a subspace $A_0 \subset \mathbb{P}_0$ of codimension two defining the Lefschetz pencil. We recall the notation of (6.1) and (6.3). A new extension of scalars allows us to assume that:

a) The points of $S$ are defined over $\mathbb{F}_q$.

b) The vanishing cycles for $x_s$ ($s \in S$) are defined over $\mathbb{F}_q$ (since only $\pm\delta$ is intrinsic, they can only be defined over quadratic extensions).

c) There exists a rational point $u_0 \in U_0$. We take the corresponding point $u$ of $U$ as the base point.

d) $X_{u_0} = f_0^{-1}(u_0)$ admits a smooth hyperplane section $Y_0$ defined over $\mathbb{F}_q$. We let $Y = Y_0 \otimes_{\mathbb{F}_q} \overline{\mathbb{F}}_q$.

Since $\widetilde{X}$ is obtained from $X$ by blowing up along a smooth subvariety $A \cap X$ of dimension two, we have
$$
H^i(X, \mathbb{Q}_l) \hookrightarrow H^i(\widetilde{X}, \mathbb{Q}_l)
$$
(in fact, $H^i(\widetilde{X}, \mathbb{Q}_l) = H^i(X, \mathbb{Q}_l) \oplus H^{i-2}(A \cap X, \mathbb{Q}_l)(-1)$). It suffices to prove (7.1.1) for the eigenvalues $\alpha$ of $F^*$ acting on $H^d(\widetilde{X}, \mathbb{Q}_l)$.

The Leray spectral sequence for $f$ is
$$
E_2^{pq} = H^p(D, R^q f_*\mathbb{Q}_l) \Rightarrow H^{p+q}(\widetilde{X}, \mathbb{Q}_l).
$$
It suffices to prove (7.1.1) for the eigenvalues of $F^*$ acting on $E_2^{pq}$ for $p + q = d = n + 1$. They are:

A) $E_2^{2,n-1}$. According to (5.8), $R^{n-1} f_*\mathbb{Q}_l$ is constant. From (2.10) we have
$$
E_2^{2,n-1} = H^{n-1}(X_u, \mathbb{Q}_l)(-1).
$$
Applying the weak Lefschetz theorem (corollary of SGA 4, XIV (3.2)) and Poincare duality (SGA 4, XVIII), we have
$$
H^{n-1}(X_u, \mathbb{Q}_l)(-1) \hookrightarrow H^{n-1}(Y, \mathbb{Q}_l)(-1)
$$
and we apply the induction hypothesis to $Y_0$.

<!-- p. 25 -->

B) $E_2^{0,n+1}$. If the vanishing cycles are nonzero, $R^{n+1} f_*\mathbb{Q}_l$ is constant and
$$
E_2^{0,n+1} = H^{n+1}(X_u, \mathbb{Q}_l).
$$
The Gysin map
$$
H^{n-1}(Y, \mathbb{Q}_l)(-1) \to H^{n+1}(X_u, \mathbb{Q}_l)
$$
is surjective (by an argument dual to that of A)) and we apply the induction hypothesis to $Y_0$.

If the vanishing cycles are zero, the exact sequence of (5.8) b) gives the following exact sequence
$$
\bigoplus_{s \in S} \mathbb{Q}_l(m - n) \to E_2^{0,n+1} \to H^{n+1}(X_u, \mathbb{Q}_l).
$$
The eigenvalues of $F$ acting on $\mathbb{Q}_l(m - n)$ are $q^{d/2}$, and for $H^{n+1}$ everything is as above.

C) $E_2^{1,n}$. If we had the “hard” Lefschetz theorem, we would know that $\mathcal{E} \cap \mathcal{E}^\perp$ is zero and that $R^n f_*\mathbb{Q}_l$ is the direct sum of $j_*\mathcal{E}$ and a constant sheaf. The $H^1$ of a constant sheaf on $\mathbb{P}^1$ is zero and it would suffice to apply (6.3).

Since we have not proved the “hard” Lefshetz theorem yet, we will have to figure a way out (literally: unscrew). If the vanishing cycles are zero, $R^n f_*\mathbb{Q}_l$ is constant ((5.8) b)) and $E_2^{1,n} = 0$. Therefore we may and do assume that the vanishing cycles are nonzero. Filter $R^n f_*\mathbb{Q}_l = j_*j^*R^n f_*\mathbb{Q}_l$ (5.8) by the subsheafs $j_*\mathcal{E}$ and $j_*(\mathcal{E} \cap \mathcal{E}^\perp)$. If the vanishing cycles $\delta$ are not in $\mathcal{E} \cap \mathcal{E}^\perp$, then we have exact sequences:
$$
0 \to j_*\mathcal{E} \to R^n f_*\mathbb{Q}_l \to \text{constant sheaf} \to 0, \tag{7.1.2}
$$
$$
0 \to \text{constant sheaf } j_*(\mathcal{E} \cap \mathcal{E}^\perp) \to j_*\mathcal{E} \to j_*(\mathcal{E}/(\mathcal{E} \cap \mathcal{E}^\perp)) \to 0. \tag{7.1.3}
$$
If, God forbid, the $\delta$ are in $\mathcal{E} \cap \mathcal{E}^\perp$, then $\mathcal{E} \subset \mathcal{E}^\perp$ and we have exact sequences:
$$
0 \to \text{the constant sheaf } j_*\mathcal{E}^\perp \to R^n f_*\mathbb{Q}_l \to \text{a sheaf } \mathcal{F} \to 0 \tag{7.1.4}
$$
$$
0 \to \mathcal{F} \to \text{the constant sheaf } j_*j^*\mathcal{F} \to \underset{s \in S}{\oplus} \mathbb{Q}_l(n - m)_s \to 0 \tag{7.1.5}
$$

In the first case the long exact sequences in cohomology give
$$
H^1(D, j_*\mathcal{E}) \to H^1(D, R^n f_*\mathbb{Q}_l) \to 0 \tag{7.1.2$'$}
$$
$$
0 \to H^1(D, j_*\mathcal{E}) \to H^1(D, j_*(\mathcal{E}/(\mathcal{E} \cap \mathcal{E}^\perp))) \tag{7.1.3$'$}
$$
and we apply (6.3).

In the second case, they give
$$
0 \to H^1(D, R^n f_*\mathbb{Q}_l) \to H^1(D, \mathcal{F}) \tag{7.1.4$'$}
$$
$$
\bigoplus_{s \in S} \mathbb{Q}_l(n - m) \to H^1(D, \mathcal{F}) \to 0 \tag{7.1.5$'$}
$$
and we remark that $F$ acts on $\mathbb{Q}_l(n - m)$ by multiplication by $q^{d/2}$.

**Lemma (7.2).** *Let $X_0$ be an absolutely irreducible nonsingular projective variety of dimension $d$ over $\mathbb{F}_q$. Let $X$ over $\overline{\mathbb{F}}_q$ be obtained from $X_0$ by extension of scalars and let $\alpha$ be an eigenvalue of $F^*$ acting on $H^d(X, \mathbb{Q}_l)$. Then $\alpha$ is an algebraic number all of whose complex conjugates, still denoted $\alpha$, satisfy*
$$
|\alpha| = q^{\frac{d}{2}}.
$$

<!-- p. 26 -->

We first prove that $(7.2) \Rightarrow (1.7)$. For $X_0$ projective nonsingular over $\overline{\mathbb{F}}_q$ we have to prove the following statements:

*$W(X_0, i)$. Let $X$ be obtained from $X_0$ by extension of scalars from $\mathbb{F}_q$ to $\overline{\mathbb{F}}_q$. If $\alpha$ is an eigenvalue of $F^*$ acting on $H^i(X, \mathbb{Q}_l)$, then $\alpha$ is an algebraic number all of which complex conjugates, again denoted $\alpha$, satisfy $|\alpha| = q^{i/2}$.*

a) If $\mathbb{F}_{q^n}$ is an an extension of degree $n$ of $\mathbb{F}_q$ and $X_0'/\mathbb{F}_{q^n}$ is obtained from $X_0/\mathbb{F}_q$ by extension of scalars, then $W(X_0, i)$ is equivalent to $W(X_0', i)$: the extension of scalars replaces $\alpha$ by $\alpha^n$ and $q$ by $q^n$.

b) If $X_0$ is purely of dimension $n$, $W(X_0, i)$ is equivalent to $W(X_0, 2n - i)$; this follows from Poincare duality.

c) If $X_0$ is a sum of the varieties $X_0^\alpha$, then $W(X_0, i)$ is equivalent to the conjunction of the $W(X_0^\alpha, i)$.

d) If $X_0$ is purely of dimension $n$, $Y_0$ is a smooth hyperplane section of $X_0$, and $i < n$, then $W(Y_0, i) \Rightarrow W(X_0, i)$: this follows from the weak Lefschetz theorem.

To prove the statements $W(X_0, i)$ we move in succession:
— by c), we may suppose that $X_0$ is purely of dimension $n$;
— by b), we may also suppose that $0 \leq i \leq n$;
— by a) and d), we may also suppose that $i = n$;
— by a) and c), we may also suppose that $X_0$ is absolutely irreducible.
This case satisfies the hypotheses of (7.2).

**(7.3)** We prove (7.2). For every integer $k$, $\alpha^k$ is an eigenvalue of $F^*$ acting on $H^{kd}(X^k, \mathbb{Q}_l)$ (Künneth formula). For $k$ even, $X^k$ satisfies the conditions of (7.1), so we have
$$
q^{\frac{kd}{2} - \frac{1}{2}} \leq |\alpha^k| \leq q^{\frac{kd}{2} + \frac{1}{2}}
$$
and
$$
q^{\frac{d}{2} - \frac{1}{2k}} \leq |\alpha| \leq q^{\frac{d}{2} + \frac{1}{2k}}.
$$
Letting $k$ go to infinity, we establish (7.2).

## 8 First applications

**Theorem (8.1).** *Let $X_0 \subset \mathbb{P}_0^{n+r}$ be a nonsingular complete intersection over $\mathbb{F}_q$ of dimension $n$ and multidegree $(d_1, \cdots d_r)$. Let $b'$ be the $n$-th Betti number of a complex nonsingular complete intersection with the same dimension and multidegree. Put $b = b'$ for $n$ odd and $b = b' - 1$ for $n$ even. Then*
$$
|\#X_0(\mathbb{F}_q) - \#\mathbb{P}^n(\mathbb{F}_q)| \leq b q^{n/2}.
$$

Let $X/\overline{\mathbb{F}}_q$ be obtained from $X_0$, and let $\mathbb{Q}_l \cdot \eta^i$ be the line in $H^{2n}(X, \mathbb{Q}_l)$ generated by the $i$-th cup power of the cohomology class of the hyperplane section. On this line $F^*$ acts by multiplication by $q^i$. The cohomology of $X$ is the direct sum of the $\mathbb{Q}_l \eta^i$ ($0 \leq i \leq n$) and the primitive part of $H^n(X, \mathbb{Q}_l)$ of dimension $b$. According to (1.5), therefore, there exist $b$ algebraic numbers $\alpha_j$, the eigenvalues of $F^*$ acting on this primitive cohomology, such that
$$
\#X_0(\mathbb{F}_q) = \sum_{i=0}^n q^i + (-1)^n \sum_j \alpha_j.
$$

<!-- p. 27 -->

According to (1.7), $|\alpha_j| = q^{n/2}$ and
$$
|\#X_0(\mathbb{F}_q) - \#\mathbb{P}^n(\mathbb{F}_q)| = |\#X_0(\mathbb{F}_q) - \sum_{i=0}^n q^i| = |\sum_j \alpha_j| \leq \sum_j |\alpha_j| = b q^{n/2}.
$$

**Theorem (8.2).** *Let $N$ be an integer $\geq 1$, $\varepsilon\colon (\mathbb{Z}/N)^* \to \mathbb{C}^*$ a character, $k$ an integer $\geq 2$, and $f$ a holomorphic modular form on $\Gamma_0(N)$ of weight $k$ and with character $\varepsilon$: $f$ is a holomorphic function on the Poincare half-plane $X$ such that for $\left(\begin{smallmatrix} a & b \\ c & d \end{smallmatrix}\right) \in SL(2, \mathbb{Z})$, with $c \equiv 0\ (N)$ we have*
$$
f\left(\frac{az + b}{cz + d}\right) = \varepsilon(a)^{-1}(cz + d)^k f(z).
$$
*We suppose that $f$ is cuspidal and primitive (”new” in the sense of Atkin-Lehner and Miyake), in particular an eigenvector of the Hecke operators $T_p$ ($p \nmid N$). Let $f = \sum_{n=1}^\infty a_n q^n$ with $q = e^{2\pi iz}$ (and $a_1 = 1$). Then for $p$ prime not dividing $N$*
$$
|a_p| \leq 2p^{\frac{k-1}{2}}.
$$
*In other words, the roots of the equation*
$$
T^2 - a_p T + \varepsilon(p)p^{k-1}
$$
*are of absolute value $p^{\frac{k-1}{2}}$.*

These roots are indeed the eigenvalues of the Frobenius map acting on the $H^{k-1}$ of a nonsingular projective variety of dimension $k - 1$ defined over $\mathbb{F}_p$.

Under restrictive assumptions, this fact is proved in my Bourbaki exposé (Formes modulaires et représentations $l$-adiques, exposé 355, February 1969, in: *Lecture Notes in Mathematics, 179*). The general case is not much more difficult.

*Remark* **(8.3)** J. P. Serre and I have recently proved that (8.2) remains true for $k = 1$.

The proof is quite different.

The following application was suggested to me by E. Bombieri.

**Theorem (8.4).** *Let $Q$ be a polynomial in $n$ variables and of degree $d$ over $\mathbb{F}_q$, $Q_d$ the homogeneous part of degree $d$ of $Q$, and $\psi\colon \mathbb{F}_q \to \mathbb{C}^*$ an additive nontrivial character on $\mathbb{F}_q$. We assume that:*

*(i) $d$ is prime to $p$*

*(ii) the hypersurface $H_0$ in $\mathbb{P}_{\mathbb{F}_q}^{n-1}$ defined by $Q_d$ is smooth.*

*Then*
$$
| \sum_{x_1, \cdots, x_n \in \mathbb{F}_q} \psi(Q(x_1, \cdots, x_n))| \leq (d - 1)^n q^{n/2}.
$$

After replacing $Q$ by a scalar multiple, we may (and do) suppose that
$$
\psi(x) = \exp(2\pi i \operatorname{Tr}_{\mathbb{F}_q/\mathbb{F}_p}(x)/p). \tag{8.4.1}
$$
Let $X_0$ be the étale covering of the affine space $\mathbb{A}_0$ of dimension $n$ over $\mathbb{F}_q$ with equation $T^p - T = Q$, and let $\sigma$ be the projection of $X_0$ to $\mathbb{A}_0$:
$$
\sigma\colon X_0 \to \mathbb{A}_0, \qquad X_0 = \operatorname{Spec}(\mathbb{F}_q[x_1, \cdots, x_n, T]/(T^p - T - Q)).
$$

<!-- p. 28 -->

The covering $X_0$ is Galois with Galois group $\mathbb{Z}/p$; $i \in \mathbb{Z}/p = \mathbb{F}_p$ acts by $T \to T + i$.

For $x \in \mathbb{A}_0(\mathbb{F}_q)$, we compute the Frobenius endomorphism on the fiber of $X_0/\mathbb{A}_0$ at $x$. Let $q = p^f$, and let $\overline{\mathbb{F}}_q$ be the algebraic closure of $\mathbb{F}_q$. For $(x, T) \in X_0(\overline{\mathbb{F}})$ above $x$ we have $F((x, T)) = (x, T^q)$ and
$$
T^q = T + \sum_{i=1}^f (T^{p^i} - T^{p^{i-1}}) = T + \sum Q(x)^{p^{i-1}} = T + \operatorname{Tr}_{\mathbb{F}_q/\mathbb{F}_p}(Q(x)).
$$
This is the action of the element $\operatorname{Tr}_{\mathbb{F}_q/\mathbb{F}_p}(Q(x))$ of the Galois group.

Let $E$ be the field of the $p$-th roots of unity and $\lambda$ a finite place of $E$ prime to $p$. We will work in $\lambda$-adic cohomology. For $j \in \mathbb{Z}/p$, let $\mathcal{F}_{j,0}$ be a $E_\lambda$-local system of rank one on $\mathbb{A}_0$ defined by $X_0$ and $\psi(-jx)\colon \mathbb{Z}/p \to E^* \to E_\lambda^*$: we have $\iota\colon X_0 \to \mathcal{F}_{j,0}$ and $\iota(i * x) = \psi(-ij)\iota(x)$. Denote without $_0$ objects obtained from $\mathbb{A}_0$, $X_0$, $\mathcal{F}_{j,0}$ by extension of scalars to $\overline{\mathbb{F}}_q$. The trace formula (1.12.1) for $\mathcal{F}_{j,0}$ gives:
$$
\sum_{x_1, \cdots, x_n \in \mathbb{F}_q} \psi(Q(x_1, \cdots, x_n)) = \sum_i \operatorname{Tr}(F^*, H_c^i(\mathbb{A}, \mathcal{F}_1)) \tag{8.4.2}
$$
We have $\sigma_* E_\lambda = \underset{j}{\oplus} \mathcal{F}_j$ and so
$$
H_c^*(X, \mathbb{Q}_l) \otimes_{\mathbb{Q}_l} E_\lambda = \underset{j}{\oplus} H_c^*(\mathbb{A}, \mathcal{F}_j). \tag{8.4.3}
$$
For $j = 0$, $\mathcal{F}_j$ is the constant sheaf $E_\lambda$; this factor corresponds to inclusion, by taking the inverse image, of the cohomology of $\mathbb{A}$ in that of $X$.

**Lemma (8.5).** *(i) For $j \neq 0$, $H_c^i(\mathbb{A}, \mathcal{F}_j)$ is zero for $i \neq n$; for $i = n$, this cohomology space has dimension $(d - 1)^n$.*

*(ii) For $j \neq 0$, the cup-product*
$$
H_c^n(\mathbb{A}, \mathcal{F}_j) \otimes H_c^n(\mathbb{A}, \mathcal{F}_{-j}) \to H^{2n}(\mathbb{A}, E_\lambda) \xrightarrow{\operatorname{Tr}} E_\lambda(-n)
$$
*is a perfect pairing.*

*(iii) $X_0$ is open in a nonsinqular projective variety $Z_0$.*

Let’s deduce (8.4) from (8.5). Let $j_0\colon X_0 \hookrightarrow Z_0$ and $j\colon X \hookrightarrow Z$ be obtained by extension of scalars to $\overline{\mathbb{F}}_q$. According to (8.4.2), (i), and (1.7) for $Z_0$, it suffices to prove the injectivity of
$$
H_c^n(\mathbb{A}, \mathcal{F}_1) \xrightarrow{\sigma^*} H_c^n(X, \mathcal{F}_1) = H_c^n(X, E_\lambda) \xrightarrow{j_!} H^n(Z, E_\lambda).
$$
We have $\operatorname{Tr}(a \cup b) = \frac{1}{p}\operatorname{Tr}(j_!\sigma^*a \cap j_!\sigma^*b)$, so this injectivity follows from (ii).

**(8.6)** We prove (8.5) (iii). Let $\mathbb{P}_0$ be the projective space over $\mathbb{F}_q$ obtained from $\mathbb{A}_0$ by adding a hyperplane at infinity $\mathbb{P}_0^\infty$, $H_0 \subset \mathbb{P}_0^\infty$ with equation $Q_d = 0$, and $Y_0$ the covering of $\mathbb{P}_0$ normalizing $\mathbb{P}_0$ along $X_0$.
$$
\begin{array}{ccccccc}
X_0 & \hookrightarrow & Y_0 & & & & \\
\downarrow \sigma & & \downarrow & & & & \\
\mathbb{A}_0 & \hookrightarrow & \mathbb{P}_0 & \longleftarrow & \mathbb{P}_0^\infty & \xhookleftarrow{\quad} & H_0
\end{array} \tag{8.6.1}
$$
We study $Y_0/\mathbb{P}_0$ near the infinity, locally for the étale topology.

<!-- p. 29 -->

**Lemma (8.7).** *$Y_0$ is smooth outside the inverse image of $H_0$.*

The divisor of a rational function $Q$ on $\mathbb{P}_0$ is the sum of the finite part $div(Q)_f$ and of $(-d)$ times the hyperplane at infinity. We have:
$$
\begin{aligned}
\operatorname{div}(Q) &= \operatorname{div}(Q)_f - d\mathbb{P}_0^\infty \\
\operatorname{div}(Q)_f \cap \mathbb{P}_0^\infty &= H_0
\end{aligned} \tag{8.7.1}
$$
At finite distance, $Y_0 = X_0$ is étale over $\mathbb{A}_0$, so smooth. At the infinity, but outside the inverse image of $H_0$, there exist local coordinates $(z_1, \cdots, z_n)$ such that $Q = z_1^{-d}$ (here we use $(d, p) = 1$). In these coordinates, $Y_0$ appears as a product of a curve and a smooth space (corresponding to coordinates $z_2, \cdots, z_n$). By normality it is smooth.

**Lemma (8.8).** *In an étale neighborhood of a point above $H_0$, $Y_0$ is smooth on a normal singular surface, always the same.*

This time we can find local coordinates such that $Q = z_1^{-d}z_2$. Indeed, since $H_0$ is smooth, $\operatorname{div}(Q)_f$ is smooth in the neighborhood of infinity and crosses $\mathbb{P}_0^\infty$ transversely. This form is independent of the chosen point, and uses only two coordinates, hence the assertion.

**(8.9)** The following method (due to Zariski) allows one to resolve singularities on surfaces: alternately, we normalize and we blow up the (reduced) singular locus. The operators in play commute with étale localization and taking a product with a smooth space. The method of Zariski, therefore, allows one to resolve the singularities of a space that (like $Y_0$) is, locally for the étale topology, smooth over a surface. The resolution obtained from $Y_0$ is the $Z_0$ sought.

If $T$ is a curve on a surface $S$, containing the singular locus, and $T'$ is the inverse image of $T$ in the Zariski resolution $S'$ of $S$, we know that if we repeatedly blow up the (reduced) singular locus of $(T')_{\text{red}}$ in $S'$, we obtain a surface $S''$ such that the reduced inverse image $(T'')_{\text{red}}$ of $T$ in $S''$ is a divisor with normal crossings. Again, the operators in play commute with étale localization and taking products with a smooth space. Arguing as above and observing that $(Y_0, \text{infinity})$ is locally smooth in $(S, T)$, we can find $Z_0$ such that $Z_0 - X_0$ is a divisor with normal crossings.

**(8.10)** We prove (8.5) (i), (ii). These assertions are geometric; this allows us to work from now on over $\overline{\mathbb{F}}_q$. Let $S'$ be the affine space over $\overline{\mathbb{F}}_q$ that parametrizes polynomials in $n$ variables of degree $\leq d$, and let $S$ be the open subscheme in $S'$ corresponding to the polynomials whose homogeneous part of degree $d$ has nonzero discriminant. We denote by $Q_S \in H^0(S, \mathcal{O}[x_1, \cdots, x_n])$ the universal polynomial of $S$ and by $X_S$ the Galois étale covering of $\mathbb{A}_S = \mathbb{A}^n \times S$ with equation $T^p - T = Q_S$ and Galois group $\mathbb{Z}/p$. Let $\mathbb{P}_S = \mathbb{P}^n \times S$ be the projective completion of $\mathbb{A}_S$ and $Y_S$ the normalization of $\mathbb{P}_S$ along $X_s$. We have, for $S$, a diagram similar to (8.6.1).

The expressions of $Q$ in local coordinates given in (8.7) and (8.8) remain valid in the present situation, with parameters, so that, locally for the étale topology on $Y_S$, $Y_S/S$ is isomorphic to the product of $S$ (which is smooth) with a fiber. The method of canonical resolution used in (8.9) gives us a relative compactification $Z_S/S$ of $X_S/S$ with $Z_S - X_S$

<!-- p. 30 -->

a divisor with normal crossings relative to $S$
$$
\begin{array}{ccc}
X_S & \xhookrightarrow{u} & Z_S \\
\downarrow \sigma & & \downarrow f \\
\mathbb{A}_S & \xhookrightarrow{a} & S
\end{array}
$$
($f$ proper and smooth, $u$ an open immersion, $Z_s - X_s$ a divisor with relative normal crossings).

Let $\mathcal{F}_{j,S}$ be an $E_\lambda$-sheaf on $\mathbb{A}_S$ obtained as in (8.4) from $X_S/\mathbb{A}_S$. We have $\sigma^* E_\lambda = \oplus \mathcal{F}_{j,S}$, so
$$
R^*(fu)_!(E_\lambda) = \underset{j}{\oplus} R^*a_!\mathcal{F}_{j,S}.
$$
The properties of $Z_S$ ensure that $R^i(fu)_! E_\lambda = R^i f_*(u_! E_\lambda)$ is a locally constant sheaf on $S$. Therefore, $R^i a_!\mathcal{F}_{j,S}$ is also locally constant. Since $S$ is connected, it suffices to prove (8.5) (i), (ii) for a particular polynomial $Q$. We will take $Q = \sum_i x_i^d$. This polynomial satisfies the nonsingularity condition because $(d, p) = 1$. For this polynomial, the variables separate in the exponential sum (8.4). This corresponds to the fact that $\mathcal{F}_j$ is the tensor product of the inverse images of similar sheaves $\mathcal{F}_j^1$ on the factors of dimension one $\mathbb{A}^1$ of $\mathbb{A} = \mathbb{A}^n$. By the Künneth formula
$$
H^*(\mathbb{A}, \mathcal{F}_j) = \bigotimes H^*(\mathbb{A}^1, \mathcal{F}_j^1).
$$
This reduces the proof of (8.5) (i), (ii) to the case where $n = 1$ and $Q$ is $x^d$.

**(8.11)** We treat this particular case. The covering $X$ of $\mathbb{A}$ is irreducible, so for $i = 0, 2$
$$
H_c^i(\mathbb{A}, E_\lambda) \xrightarrow{\sim} H_c^i(X, E_\lambda).
$$
So for $i \neq 1$ and $j \neq 0$ we have
$$
H_c^i(X, \mathcal{F}_j) = 0.
$$
Assertion (ii) follows from (2.8) or (2.12) and the fact that $u_!\mathcal{F}_j = u_*\mathcal{F}_j$. To prove (i) it remains to show that
$$
\chi_c(\mathbb{A}, \mathcal{F}_j) = 1 - d.
$$
According to the Euler-Poincare formula (see Bourbaki Exposé 286, February 1965, by M.Raynaud), this is equivalent to the following lemma.

**Lemma (8.12).** *Swan’s conductor of $\mathcal{F}_j$ at infinity equals $d$.*

This statement is equivalent to the following.

**Lemma (8.13).** *Let $k$ be a finite field of characteristic $p$, $y \in k[[x]]$ an element of valuation $d$ prime to $p$, $L$ the extension of $K = k((x))$ generated by the roots of $T^p - T = y^{-1}$, and $\chi$ the following character on $\operatorname{Gal}(L/K)$ with values in $\mathbb{Z}/p$:*
$$
\chi(\sigma) = \sigma T - T.
$$
*Then $\chi$ has conductor $d + 1$.*

By extension of the residue field, we may suppose that $k$ is algebraically closed rather than finite and apply: J.P.Serre, Sur les corps locaux a corps residuel algebriquement clos, *Bull. Soc. Math. France*, 89 (1961), p. 105-154, $\text{n}^{\text{o}}$ 4.4.

<!-- p. 31 -->

## References

[1] A. Grothendieck, *Formule de Lefschetz et rationalite des fonctions $L$*, Séminare Bourbaki, 279, December 1964 (Benjamin).

[2] S. Lefschetz, *L’analysis situs et la géometrie algébrique* (Gauthier-Villars), 1924. Reproduced in: *Selected papers* (Chelsea Publ. Co.).

[3] R. A. Rankin *Contributions to the theory of Ramanujan’s function $\tau(n)$ and similar arithmetical functions..* II, Proc. Camb. Phil. Soc., **35** (1939), 351-372.

[4] A.Weil *Numbers of solutions of equations in finite fields*, Bull. Math. Soc., **55** (1949), p. 497-508.

SGA, *Séminaire de Géométrie Algébrique du Bois-Marie* (IHES):

SGA 4, *Théorie des topos et cohomologie étale des schemas* (dirigé par M. Artin, A. Grothendieck et J.-L. Verdier), *Lecture notes in Math.*, 269, 270, 305.

SGA 5, *Cohomologie $l$-adique et fonctions $L$*, distributed by l’IHES.

SGA 7, Groupes de monodromie en géometrie algebrique.
- 1st part: dirigé par A. Grothendieck, *Lecture Notes in Math.*, 288.
- 2nd part: par P. Deligne et N. Katz, *Lecture Notes in Math.*, 340.

*Manuscript received on 20 September 1973.*
