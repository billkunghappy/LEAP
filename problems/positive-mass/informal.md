<!-- page 1 -->

arXiv:1911.06754v1 [math.DG] 15 Nov 2019

# HARMONIC FUNCTIONS AND THE MASS OF 3-DIMENSIONAL ASYMPTOTICALLY FLAT RIEMANNIAN MANIFOLDS

HUBERT L. BRAY, DEMETRE P. KAZARAS, MARCUS A. KHURI, AND DANIEL L. STERN

**Abstract.** An explicit lower bound for the mass of an asymptotically flat Riemannian 3-manifold is given in terms of linear growth harmonic functions and scalar curvature. As a consequence, a new proof of the positive mass theorem is achieved in dimension three. The proof has parallels with both the Schoen-Yau minimal hypersurface technique and Witten's spinorial approach. In particular, the role of harmonic spinors and the Lichnerowicz formula in Witten's argument is replaced by that of harmonic functions and a formula introduced by the fourth named author in recent work, while the level sets of harmonic functions take on a role similar to that of the Schoen-Yau minimal hypersurfaces.

## 1. Introduction

Let $(M,g)$ be a smooth connected 3-dimensional asymptotically flat Riemannian manifold with nonnegative scalar curvature $R_g \geq 0$. The notion of asymptotic flatness means that there is a compact set $\mathcal{K} \subset M$ such that $M \setminus \mathcal{K} = \cup_{k=1}^{k_0} M_{end}^k$ where the ends $M_{end}^k$ are pairwise disjoint and diffeomorphic to the complement of a ball $\mathbb{R}^3 \setminus B_1$, and there exists in each end a coordinate system satisfying

$$
|\partial^l (g_{ij} - \delta_{ij})(x)| = O(|x|^{-q-l}), \tag{1.1}
$$

for some $q > \frac{1}{2}$ and with $l = 0, 1, 2$. The scalar curvature is assumed to be integrable $R_g \in L^1(M)$ so that the ADM mass of each end is well-defined [1] and given by

$$
m = \lim_{r \to \infty} \frac{1}{16\pi} \int_{S_r} \sum_i (g_{ij,i} - g_{ii,j}) \upsilon^j dA, \tag{1.2}
$$

where $\upsilon$ is the unit outer normal to the coordinate sphere $S_r$ of radius $r = |x|$ and $dA$ denotes its area element. The positive mass theorem asserts that this parameter has a sign, and it characterizes Euclidean space as the unique manifold in this class with vanishing mass.

**Theorem 1.1.** *If* $(M,g)$ *is complete and asymptotically flat with nonnegative scalar curvature then* $m \geq 0$*, and* $m = 0$ *if and only if* $(M,g) \cong (\mathbb{R}^3, \delta)$.

This theorem was first established in the late 1970's by Schoen and Yau [13, 14] via a contradiction argument, and is based on the existence of stable minimal hypersurfaces along with manipulations of the stability inequality. Shortly after this Witten [12, 16] found an alternate proof in which the mass is expressed as a sum of squares. This proof relies on the existence of harmonic spinors and the Lichnerowicz formula. More recently two other proofs have been given in the general case. One by Huisken and Ilmanen [7], which arose out of their study of the Penrose inequality, follows from the existence of a weak version of inverse mean curvature flow and monotonicity of Hawking mass. The other is a Ricci flow proof and is due to Li [8]. Further proofs have been given in special cases, such as

D. Kazaras acknowledges the support of NSF Grant DMS-1547145. M. Khuri acknowledges the support of NSF Grant DMS-1708798.

<!-- page 2 -->

that of Brill [4] in the axisymmetric setting. It should also be noted that Lohkamp [17] showed how the positive mass theorem can be reduced to the nonexistence of positive scalar curvature metrics on the connected sum $N \# T$ of a compact manifold $N$ with a torus $T$. See [6] for a survey of these topics. Furthermore, we point out the articles of Schoen and Yau [15] and Lohkamp [18] which address the higher dimensional case.

The purpose of the current article is to give an explicit lower bound for the mass in terms of linear growth harmonic functions and scalar curvature. This approach is based on an integral inequality due to Stern [19], and leads to a new and relatively simple proof of Theorem 1.1. Associated with each asymptotic end $M_{end}$ there is a corresponding *exterior region* $M_{ext} \supset M_{end}$, which is diffeomorphic to the complement of a finite number of balls (with disjoint closure) in $\mathbb{R}^3$ and has minimal boundary [7, Lemma 4.1].

**Theorem 1.2.** *Let* $(M_{ext}, g)$ *be an exterior region of a complete asymptotically flat Riemannian 3-manifold* $(M,g)$ *with mass* $m$*. Let* $u$ *be a harmonic function on* $(M_{ext}, g)$ *satisfying Neumann boundary conditions at* $\partial M_{ext}$*, and which is asymptotic to one of the asymptotically flat coordinate functions of the associated end. Then*

$$
m \geq \frac{1}{16\pi} \int_{M_{ext}} \left( \frac{|\nabla^2 u|^2}{|\nabla u|} + R_g |\nabla u| \right) dV. \tag{1.3}
$$

*In particular, if the scalar curvature is nonnegative then* $m \geq 0$*. Furthermore, if* $m = 0$ *then* $(M,g) \cong (\mathbb{R}^3, \delta)$.

Two approaches to the positive mass theorem will be presented within the context of the harmonic level set technique. They differ in their handling of the exterior region boundary, and in their use of the asymptotically flat geometry. In the first method Neumann boundary conditions are imposed on $\partial M_{ext}$ in order to deal with boundary terms appearing in Stern's integration formula [19], while in the second method the Mantoulidis neck construction [10] is used to cap-off the boundary spheres so that the resulting manifold is diffeomorphic to $\mathbb{R}^3$ and still possesses nonnegative scalar curvature. Within the asymptotic end harmonic coordinates are employed along with cylindrical domains in the first approach to extract the mass and compute total geodesic curvatures. On the other hand, the second approach utilizes a density theorem to reduce the asymptotic geometry to that of Schwarzschild where the analysis is then performed on coordinate spheres.

## 2. Preparing the Data

Within the context of the 3-dimensional positive mass theorem, simplifications of the asymptotics and topology may be assumed without loss of generality. More precisely Schoen and Yau [14] showed that metrics with harmonic asymptotics are dense in the relevant class of metrics, and Bray [2] (see also [5, Proposition 3.3]) extended this to show that in fact harmonic asymptotics may be replaced with Schwarzschild asymptotics. As for the topology of $M$, one may consider the portion of $M$ outside the outermost minimal surface, and fill in the resulting spherical holes using work of Mantoulidis [10] and the Miao smoothing [11]. This procedure allows one to reduce the topology of $M$ to $\mathbb{R}^3$. It should be noted that this reduction is specific to dimension 3.

**Proposition 2.1.** *Let* $(M,g)$ *be a smooth 3-dimensional complete asymptotically flat Riemannian manifold having nonnegative scalar curvature* $R_g \geq 0$*, and with mass* $m$ *of a designated end* $M_{end}^+$*. Given* $\varepsilon > 0$*, there exists a smooth* 3*-dimensional complete asymptotically flat Riemannian manifold* $(\overline{M}, \overline{g})$ *with nonnegative scalar curvature* $R_{\overline{g}} \geq 0$ *and satisfying the following properties.*

(1) *The underlying manifold* $\overline{M}$ *is diffeomorphic to* $\mathbb{R}^3$.

<!-- page 3 -->

(2) *The mass* $\overline{m}$ *of the single end* $\overline{M}_{end}$ *satisfies* $|m - \overline{m}| < \varepsilon$.

(3) *In the asymptotic coordinates of* $\overline{M}_{end}$, $\overline{g} = \left(1 + \frac{\overline{m}}{2r}\right)^4 \delta$.

*Proof.* By passing to the orientable double cover if necessary we may assume that $M$ is orientable. Moreover by applying an appropriate conformal deformation with conformal factor approximating 1, such that the deformed mass differs from the original by an arbitrarily small amount, we may assume that $(M,g)$ has positive scalar curvature $R_g > 0$ everywhere. Let $\mathcal{S} \subset M$ denote the *trapped region* in the sense of [7]. If $\mathcal{S} = \emptyset$ then $M$ is diffeomorphic to $\mathbb{R}^3$ [7, Lemma 4.1], and we set $\overline{M} = M$. The desired metric $\overline{g}$ then arises from Bray's density result [5, Proposition 3.3]. If $\mathcal{S} \neq \emptyset$, then consider $\overline{M}^+$, the metric closure of the component of $M \setminus \mathcal{S}$ containing $M_{end}^+$. According to [7, Lemma 4.1] this exterior region is diffeomorphic to the complement of a finite union of balls, so that

$$
\overline{M}^+ = \mathbb{R}^3 \setminus \cup_{i=1}^k B_i, \tag{2.1}
$$

where the spheres $\cup_i S_i^2 = \cup_i \partial B_i$ are homologically area outer-minimizing. Since each submanifold $(S_i^2, \gamma_i = g|_{S_i^2})$ is a 2-sided stable minimal surface in an ambient space of positive scalar curvature, the principal eigenvalue of $-\Delta_{\gamma_i} + K_{\gamma_i}$ is positive, where $K_{\gamma_i}$ denotes Gaussian curvature. The hypotheses of [10, Corollary 2.2.13] are then satisfied, so that for each $i = 1, \ldots, k$ there is a Riemannian 3-ball $(D_i, g_i)$ with positive scalar curvature, minimal boundary, and satisfying $\partial(D_i, g_i) \cong (S_i^2, \gamma_i)$. Glue in these 3-balls to form

$$
\overline{M} = \overline{M}^+ \bigcup_{\mathcal{S}} \left( \cup_{i=1}^k D_i \right), \tag{2.2}
$$

and equip $\overline{M}$ with a $C^{0,1}$-Riemannian metric that agrees with $g$ on $\overline{M}^+$ and $g_i$ on each $D_i$, see Figure 1. Next, smooth a tubular neighborhood of $\mathcal{S}$ followed by a conformal deformation as in [11, Sections 3 & 4], to obtain an asymptotically flat metric $\tilde{g}$ on $\overline{M}$ with nonnegative scalar curvature and mass satisfying $|m - \tilde{m}| < \varepsilon/2$. Now apply Bray's density result [5, Proposition 3.3] to $\tilde{g}$ to produce the desired metric $\overline{g}$ with mass $\overline{m}$ satisfying $|\tilde{m} - \overline{m}| < \varepsilon/2$. $\square$

**Remark 2.2.** In Proposition 2.1, the conclusion that $\overline{M}$ is diffeomorphic to $\mathbb{R}^3$ relies on deep results outlined in [7]. In light of this, it is worth pointing out that ultimately we do not require the full strength of this topological simplification. Indeed, the only time this portion of Proposition 2.1 is utilized, is in the proof of Lemma 3.1 where only the triviality of $H_2(\overline{M}; \mathbb{Z})$ is needed. This weaker simplification may be achieved via more elementary means. By following the arguments of [6, page 140], there exists $\widetilde{M}^+$ containing $M_{end}^+$ whose boundary consists of minimal spheres and satisfies $H_2(\widetilde{M}^+, \partial \widetilde{M}^+; \mathbb{Z}) = 0$. Then filling in with discs as above yields the desired conclusion.

A 3-dimensional Riemannian manifold satisfying points (1) and (3) of Proposition 2.1 will be referred to as *Schwarzschildian*. This proposition allows the proof of Theorem 1.1 to be reduced to the following Schwarzschildian case, which will be established in Section 5.

**Theorem 2.3.** *If* $(M,g)$ *is complete and Schwarzschildian with nonnegative scalar curvature then* $m \geq 0$*, and* $m = 0$ *if and only if* $(M,g) \cong (\mathbb{R}^3, \delta)$.

## 3. Linear Growth Harmonic Functions

### 3.1. Harmonic functions on Schwarzschildian ends.

Suppose that $(M,g)$ is Schwarzschildian, and in $M_{end}$ write $g = w^4 \delta$ where $w = 1 + \frac{m}{2r}$. Let

$$
L_g = \Delta_g - \frac{1}{8} R_g \tag{3.1}
$$

<!-- page 4 -->

*[Figure: Figure 1. A schematic description of the construction in Proposition 2.1.]*

be the conformal Laplacian. According to the conformal invariance of this operator,

$$
L_g v = w^{-5} L_\delta (wv)
\tag{3.2}
$$

for any function $v$. Let $\ell(x) = a_i x^i$ be a linear function in the asymptotically flat coordinates $\{x^i\}_{i=1}^3$ on $M_{end}$. Since $R_g \equiv 0$ in $M_{end}$ it follows that

$$
\Delta_g (\ell w^{-1}) = L_g (\ell w^{-1}) = w^{-5} L_\delta \ell = w^{-5} \Delta_\delta \ell = 0.
\tag{3.3}
$$

We can now find harmonic functions on $M$ with the following prescribed linear asymptotics. Given $a_i$ there exists a constant $a$ such that

$$
\begin{cases}
\Delta_g u = 0 & \text{on } M, \\
u(x) = \frac{a_i x^i}{1+\frac{m}{2r}} + \frac{a}{r} + O_2(r^{-2}) & \text{in } M_{end},
\end{cases}
\tag{3.4}
$$

where the notation $v = O_l(r^{-k})$ asserts that $|\partial^j v| \leq C r^{-k-j}$ for $j \leq l$. To see this, let $u_0 \in C^\infty(M)$ be any smooth function satisfying $u_0 \equiv \ell w^{-1}$ in $M_{end}$, and set $f = -\Delta_g u_0$. Notice that (3.3) implies $f \equiv 0$ in $M_{end}$. By a standard argument [13, Lemma 3.2], there exists a function $u_1 \in C^\infty(M)$ solving

$$
\begin{cases}
\Delta_g u_1 = f & \text{on } M, \\
u_1(x) = \frac{a}{r} + O_2(r^{-2}) & \text{in } M_{end},
\end{cases}
\tag{3.5}
$$

for some constant $a$. The desired unique solution of (3.4) is $u = u_0 + u_1$.

**Lemma 3.1.** *Let* $(M, g)$ *be complete and Schwarzschildian. For any linear function* $\ell$ *in the coordinates of* $M_{end}$*, there exists a unique solution* $u_\ell$ *of* (3.4)*. Moreover, all regular level sets of* $u_\ell$ *are connected and noncompact with a single end modeled on* $\mathbb{R}^2 \setminus B_1$*.*

*Proof.* The discussion preceding the lemma establishes the existence of the solutions $u_\ell$, and uniqueness follows from the maximum principle. For such an asymptotically linear harmonic function $u_\ell$, let $t$ be a regular value of $u_\ell$ and consider the level set $\Sigma_t = u^{-1}(t)$. Suppose that there is a compact connected component $\Sigma_t' \subset \Sigma_t$. Notice that $\Sigma_t'$ is a properly embedded submanifold and is 2-sided (has trivial normal bundle). Since $M = \mathbb{R}^3$ has trivial homology, $\Sigma_t'$ must bound a compact region of $M$. By uniqueness of solutions to the Dirichlet problem for harmonic functions, $u_\ell \equiv t$ on this

<!-- page 5 -->

*[Figure: Figure 2. Possible level sets of a harmonic function from Lemma 3.1.]*

region. However this contradicts the assumption that $t$ is a regular value. It follows that all components of $\Sigma_t$ are noncompact. Furthermore, since it is properly embedded $\Sigma_t$ is a closed subset of $M$. Thus if any component of $\Sigma_t$ stays within $M_r$, the compact region bounded by the coordinate sphere $S_r \subset M_{end}$, it must be compact which is a contradiction. We conclude that each component must extend outside $S_r$ for all $r$.

The asymptotics of $u_\ell$ imply that there exists a constant $C$, such that for all sufficiently large $r$ the level set $\Sigma_t$ lies within the slab $\{x \in M \setminus M_r \mid t - C < \ell(x) < t + C\}$. More precisely, the implicit function theorem shows that $\Sigma_t$ is represented uniquely in this region as a graph over the plane $t = \ell(x)$. It follows that $\Sigma_t$ is connected and has a single end modeled on $\mathbb{R}^2 \setminus B_1$. $\square$

### 3.2. Harmonic coordinates.

In the general case of an asymptotically flat 3-manifold $(M, g)$, not necessarily Schwarzschildian, consider the exterior region $M_{ext}$ associated with a given end $M_{end}$. Let $y^i$, $i = 1, 2, 3$ denote the given asymptotically flat coordinate system in $M_{end}$. The analysis of [1, Theorem 3.1] may be appropriately modified in order to produce harmonic coordinates satisfying Neumann boundary conditions. That is, there exist functions $x^i \in C^\infty(M_{ext})$ satisfying

$$
\Delta_g x^i = 0 \quad \text{ on } \quad M_{ext}, \quad \partial_\upsilon x^i = 0 \quad \text{ on } \quad \partial M_{ext}, \quad |x^i - y^i| = o(|y|^{1-q}) \quad \text{ as } \quad |y| \to \infty,
\tag{3.6}
$$

where $q$ is the order of asymptotically flat decay in (1.1). This decay is still valid for the harmonic coordinates, that is

$$
|\partial^l (g_{ij} - \delta_{ij})(x)| = O(|x|^{-q-l}), \qquad l = 0, 1, 2.
\tag{3.7}
$$

Harmonic coordinates are particularly well suited for studying the mass [1], and will play an important role in the computation of asymptotic boundary terms appearing in the integral inequalities of Section 4 below.

## 4. Relating Scalar Curvature to Level Set Geometry

The purpose of this section is to obtain integral inequalities for the scalar curvature of a compact Riemannian manifold equipped with a harmonic function, building on the techniques introduced by the fourth named author in [19]. Note that our setting is slightly different from that of [19], which studies closed 3-manifolds with harmonic maps to $S^1$, while we work with harmonic functions on compact manifolds with boundary where additional boundary conditions are needed. As in [19], the first step in obtaining the relevant identities is to apply the Gauss equations to extract scalar curvature on a regular level set of a harmonic function. Note that in the next result, the dimension is not restricted to three.

<!-- page 6 -->

**Lemma 4.1.** *Suppose that* $(M, g)$ *is a Riemannian manifold and* $u : M \to \mathbb{R}$ *is harmonic with regular level set* $\Sigma$*. Then, on* $\Sigma$*, the following identity holds*

$$
\mathrm{Ric}(\nabla u, \nabla u) = \frac{1}{2} |\nabla u|^2 \left( R_g - R_\Sigma \right) + |\nabla |\nabla u||^2 - \frac{1}{2} |\nabla^2 u|^2,
\tag{4.1}
$$

*where* $R_g$ *and* $R_\Sigma$ *denote the respective scalar curvatures.*

*Proof.* Since $\Sigma$ is a regular level set, its unit normal is given by $\nu = \frac{\nabla u}{|\nabla u|}$. Taking two traces of the Gauss equations then yields

$$
R_g - 2\mathrm{Ric}\left( \frac{\nabla u}{|\nabla u|}, \frac{\nabla u}{|\nabla u|} \right) = R_\Sigma + |II|^2 - H^2,
\tag{4.2}
$$

where $H$ and $II$ are the mean curvature and second fundamental form of $\Sigma$. The second fundamental form is given by $II = \frac{\nabla^2_\Sigma u}{|\nabla u|}$, where $\nabla^2_\Sigma u$ denotes the Hessian of $u$ restricted to $T\Sigma \otimes T\Sigma$. It follows that

$$
|II|^2 = |\nabla u|^{-2} \left( |\nabla^2 u|^2 - 2 |\nabla |\nabla u||^2 + [\nabla^2 u(\nu, \nu)]^2 \right),
\tag{4.3}
$$

and because $u$ is harmonic

$$
H = \mathrm{Tr}_\Sigma II = |\nabla u|^{-1} \left( \mathrm{Tr}_g \nabla^2 u - \nabla^2 u(\nu, \nu) \right) = -|\nabla u|^{-1} \nabla^2 u(\nu, \nu).
\tag{4.4}
$$

Combining equations (4.3) and (4.4) produces

$$
|II|^2 - H^2 = |\nabla u|^{-2} \left( |\nabla^2 u|^2 - 2 |\nabla |\nabla u||^2 \right).
\tag{4.5}
$$

Inserting this into (4.2) gives the desired result. $\square$

The formula of Lemma 4.1 will be combined with Bochner's identity and integrated by parts over a compact manifold with boundary, while applying the coarea formula with harmonic level sets. For a function $u : \Omega \to \mathbb{R}$ on a compact manifold $\Omega$, let $\overline{u}$ and $\underline{u}$ be the maximum and minimum values of $u$, respectively. The following computation plays a key role in both of our approaches for obtaining lower bounds on the ADM mass. We remark that related computations for $S^1$-valued harmonic maps with homogeneous Neumann condition can be found in the paper [3], where several applications to the geometry of compact 3-manifolds are obtained.

**Proposition 4.2.** *Let* $(\Omega^3, g)$ *be an 3-dimensional oriented compact Riemannian manifold with boundary decomposed into* $\partial \Omega = P_1 \sqcup P_2$*. Let* $u : \Omega \to \mathbb{R}$ *be a harmonic function satisfying the Neumann condition* $\partial_\upsilon u \equiv 0$ *on* $P_1$ *and the nondegeneracy condition* $|\nabla u|_{P_2}| > 0$ *on* $P_2$*. Then*

$$
\begin{aligned}
&\int_{\underline{u}}^{\overline{u}} \left( \int_{\Sigma_t} \frac{1}{2} \left( \frac{|\nabla^2 u|^2}{|\nabla u|^2} + R_g \right) dA + \int_{\partial \Sigma_t \cap P_1} H_{P_1} \right) dt \\
&\qquad\qquad \leq \int_{\underline{u}}^{\overline{u}} \left( 2\pi \chi(\Sigma_t) - \int_{\partial \Sigma_t \cap P_2} \kappa_{\partial \Sigma_t} \right) dt + \int_{P_2} \partial_\upsilon |\nabla u| dA,
\end{aligned}
\tag{4.6}
$$

*where* $\kappa_{\partial \Sigma_t}$ *denotes the geodesic curvature of* $\partial \Sigma_t \subset \Sigma_t$*,* $H_{P_1}$ *denotes the mean curvature of* $P_1$*, and* $\upsilon$ *is the unit outer normal to* $\partial \Omega$*. In the case* $P_1 = \varnothing$*, we record also the equivalent formulation*

$$
\int_{\underline{u}}^{\overline{u}} \int_{\Sigma_t} \frac{1}{2} \left( \frac{|\nabla^2 u|^2}{|\nabla u|^2} + R_g - R_{\Sigma_t} \right) dA dt \leq \int_{\partial \Omega} \partial_\upsilon |\nabla u|.
\tag{4.7}
$$

<!-- page 7 -->

*Proof.* Let $\varepsilon > 0$ and consider $\phi = \sqrt{|\nabla u|^2 + \varepsilon}$. By Bochner's identity

$$
\begin{aligned}
\Delta_g \phi =& \frac{\Delta_g |\nabla u|^2}{2\phi} - \frac{|\nabla |\nabla u|^2|^2}{4\phi^3} \\
=& \phi^{-1} \left( |\nabla^2 u|^2 + \mathrm{Ric}(\nabla u, \nabla u) - \phi^{-2} |\nabla u|^2 |\nabla |\nabla u||^2 \right).
\end{aligned}
\tag{4.8}
$$

It follows that on a regular level set $\Sigma$, Lemma 4.1 may be applied to find

$$
\Delta_g \phi \geq \frac{1}{2} \phi^{-1} \left( |\nabla^2 u|^2 + |\nabla u|^2 (R_g - R_\Sigma) \right).
\tag{4.9}
$$

Let $\mathcal{A} \subset [\underline{u}, \overline{u}]$ be an open set containing the critical values of $u$, and denote the complementary closed set by $\mathcal{B} \subset [\underline{u}, \overline{u}]$. Note that, by virtue of the boundary conditions for $u$, $\mathcal{A}$ also contains all critical values for the restriction $u|_{\partial\Omega}$ of $u$ to the boundary.

Now, integration by parts yields

$$
\int_{\partial\Omega} \partial_\upsilon \phi dA = \int_\Omega \Delta_g \phi dV = \int_{u^{-1}(\mathcal{A})} \Delta_g \phi dV + \int_{u^{-1}(\mathcal{B})} \Delta_g \phi dV.
\tag{4.10}
$$

In order to control the integral over $u^{-1}(\mathcal{A})$, observe that (4.8) and Cauchy-Schwarz give the estimate

$$
\Delta_g \phi \geq \phi^{-1} \mathrm{Ric}(\nabla u, \nabla u) \geq - \parallel \mathrm{Ric} \parallel |\nabla u|.
\tag{4.11}
$$

Applying the coarea formula to $u : u^{-1}(\mathcal{A}) \to \mathcal{A}$ then produces

$$
- \int_{u^{-1}(\mathcal{A})} \Delta_g \phi dV \leq \int_{u^{-1}(\mathcal{A})} \parallel \mathrm{Ric} \parallel |\nabla u| dV \leq C \int_{t \in \mathcal{A}} \mathcal{H}^2(\Sigma_t) dt,
\tag{4.12}
$$

for some constant $C$ independent of $\varepsilon$ and the choice of $\mathcal{A}$. In addition, applying the coarea formula to $u : u^{-1}(\mathcal{B}) \to \mathcal{B}$ in conjunction with (4.9) gives

$$
\int_{u^{-1}(\mathcal{B})} \Delta_g \phi dV \geq \frac{1}{2} \int_{t \in \mathcal{B}} \int_{\Sigma_t} \phi^{-1} \left[ \frac{|\nabla^2 u|^2}{|\nabla u|^2} + (R_g - R_{\Sigma_t}) \right] dA dt.
\tag{4.13}
$$

Putting this all together yields

$$
\frac{1}{2} \int_{t \in \mathcal{B}} \int_{\Sigma_t} \phi^{-1} |\nabla u| \left[ \frac{|\nabla^2 u|^2}{|\nabla u|^2} + (R_g - R_{\Sigma_t}) \right] dA dt \leq \int_{\partial\Omega} \partial_\upsilon \phi dA + C \int_{t \in \mathcal{A}} \mathcal{H}^2(\Sigma_t) dt.
\tag{4.14}
$$

Next, we employ the homogeneous Neumann condition $\partial_\upsilon u \equiv 0$ to rewrite the boundary integral $\int_{P_1} \partial_\upsilon \phi$. Indeed, note that, away from critical points of $u$ along $P_1$, we have

$$
\partial_\upsilon \phi = \phi^{-1} \langle \nabla_{\nabla u} \nabla u, \upsilon \rangle = -\phi^{-1} \langle \nabla u, \nabla_{\nabla u} \upsilon \rangle,
\tag{4.15}
$$

where in the last line the Neumann condition was used. Writing $\nu = \frac{\nabla u}{|\nabla u|}$ and continuing to use the homogeneous Neumann condition, a brief calculation shows that

$$
\langle \nu, \nabla_\nu \upsilon \rangle = II_{\partial\Omega}(\nu, \nu) = H_{P_1} - \kappa_{\partial\Sigma_t},
\tag{4.16}
$$

so we can rewrite (4.15) as

$$
\partial_\upsilon \phi = -\phi^{-1} |\nabla u|^2 (H_{P_1} - \kappa_{\partial\Sigma_t}).
\tag{4.17}
$$

In particular, applying the coarea formula for the restriction $u|_{P_1}$–and using the homogeneous Neumann condition to see that $|\nabla u|_{P_1}| = |\nabla u|$ along $P_1$–we find that

$$
\int_{P_1} \partial_\upsilon \phi dA = - \int_{t \in \mathcal{B}} \int_{\partial\Sigma_t \cap P_1} \phi^{-1} |\nabla u| (H_{P_1} - \kappa_{\partial\Sigma_t}) + \int_{t \in \mathcal{A}} \int_{\partial\Sigma_t \cap P_1} |\nabla u|^{-1} \phi^{-1} \langle \nabla_{\nabla u} \nabla u, \upsilon \rangle.
\tag{4.18}
$$

<!-- page 8 -->

Since

$$
|\nabla u|^{-1} \phi^{-1} |\langle \nabla_{\nabla u} \nabla u, \upsilon \rangle| \leq |II_{P_1}| \leq C,
\tag{4.19}
$$

it follows that

$$
\int_{P_1} \partial_\upsilon \phi dA \leq - \int_{t \in \mathcal{B}} \int_{\partial\Sigma_t \cap P_1} \phi^{-1} |\nabla u| (H_{P_1} - \kappa_{\partial\Sigma_t}) + C \int_{t \in \mathcal{A}} \mathcal{H}^1(\partial\Sigma_t \cap P_1).
\tag{4.20}
$$

Apply (4.20) in (4.14) to obtain

$$
\begin{aligned}
\frac{1}{2} \int_{t \in \mathcal{B}} \int_{\Sigma_t} \frac{|\nabla u|}{\phi} \left( \frac{|\nabla^2 u|^2}{|\nabla u|^2} + R_g \right) dA dt \leq & \int_{t \in \mathcal{B}} \left( \frac{1}{2} \int_{\Sigma_t} \frac{|\nabla u|}{\phi} R_{\Sigma_t} dA + \int_{\partial\Sigma_t \cap P_1} \frac{|\nabla u|}{\phi} (\kappa_{\partial\Sigma_t} - H_{P_1}) \right) dt \\
& + \int_{P_2} \partial_\upsilon \phi dA + C \int_{t \in A} \left( \mathcal{H}^2(\Sigma_t) + \mathcal{H}^1(\partial\Sigma_t \cap P_1) \right).
\end{aligned}
\tag{4.21}
$$

Observe that $|\nabla u|$ is uniformly bounded from below on $u^{-1}(\mathcal{B})$, since $\mathcal{B}$ is a closed subset of the regular values of $u$. Recalling that $\phi = (|\nabla u|^2 + \varepsilon)^{1/2}$, we may take $\varepsilon \to 0$ in the preceding inequality to conclude that

$$
\begin{aligned}
\frac{1}{2} \int_{t \in \mathcal{B}} \int_{\Sigma_t} \left( \frac{|\nabla^2 u|^2}{|\nabla u|^2} + R_g \right) dA dt \leq & \int_{t \in \mathcal{B}} \left( \frac{1}{2} \int_{\Sigma_t} R_{\Sigma_t} dA + \int_{\partial\Sigma_t \cap P_1} (\kappa_{\partial\Sigma_t} - H_{P_1}) \right) dt \\
& + \int_{P_2} \partial_\upsilon |\nabla u| dA + C \int_{t \in A} \left( \mathcal{H}^2(\Sigma_t) + \mathcal{H}^1(\partial\Sigma_t \cap P_1) \right) \\
= & \int_{t \in \mathcal{B}} \left( 2\pi\chi(\Sigma_t) - \int_{\partial\Sigma_t \cap P_2} \kappa_{\partial\Sigma_t} - \int_{\partial\Sigma_t \cap P_1} H_{P_1} \right) dt \\
& + \int_{P_2} \partial_\upsilon |\nabla u| dA + C \int_{t \in A} \left( \mathcal{H}^2(\Sigma_t) + \mathcal{H}^1(\partial\Sigma_t \cap P_1) \right),
\end{aligned}
\tag{4.22}
$$

where in the second step we have applied the Gauss-Bonnet theorem to $\Sigma_t$.

Finally, by Sard's theorem, we may take the measure $|\mathcal{A}|$ of $\mathcal{A}$ to be arbitrarily small. Since

$$
t \mapsto \mathcal{H}^2(\Sigma_t) + \mathcal{H}^1(\Sigma_t \cap P_1)
\tag{4.23}
$$

is integrable over $[\underline{u}, \overline{u}]$ by the coarea formula, taking $|\mathcal{A}| \to 0$ in the preceding inequality yields the desired conclusion. $\square$

**Remark 4.3.** Note that for our applications in Section 6, the boundary component $P_2$ in Proposition 4.2 will be a piecewise smooth surface, diffeomorphic to the boundary $\partial(D^2 \times [0,1])$ of the solid cylinder $D^2 \times [0,1]$. However, our harmonic function $u$ in this case will be constant on the disks $D^2 \times \{0\}$ and $D^2 \times \{1\}$, with nonvanishing gradient along the cylindrical portion $S^1 \times [0,1]$, and it is easy to check that the preceding argument carries over to this case without difficulty.

## 5. The Schwarzschildian Approach

In this section we prove Theorem 1.1 by establishing Theorem 2.3 and applying the Schwarzschildian reduction of Proposition 2.1. Unless stated otherwise, in this section $(M, g)$ will denote a 3-dimensional Schwarzschildian manifold.

<!-- page 9 -->

### 5.1. Connectivity of level sets.

Consider a coordinate sphere $S_r \subset M_{end}$ and let $M_r$ be the compact component of $M \setminus S_r$. In order to apply the identity (4.7) to $\Omega = M_r$, a computation of the Gauss curvature piece is required, which is given in Proposition 5.2 below. Before proceeding to this calculation, properties concerning the topology of regular level sets in $M_r$ will be recorded. Let $u$ be an asymptotically linear harmonic function as in Lemma 3.1, and for $t \in \mathbb{R}$, $r > 0$ set $\Sigma_t^r = \Sigma_t \cap M_r$.

**Lemma 5.1.** *Let* $(M, g)$ *and* $u$ *be as above. There are constants* $r_0 > 0$ *and* $c_0 > 0$ *such that for all* $r \geq r_0$ *and* $t \in [-r + c_0, r - c_0]$ *with* $t$ *a regular value,* $\Sigma_t^r$ *is connected with boundary* $\partial\Sigma_t^r = S^1$*.*

*Proof.* Let $\ell = a_i x^i$ be the nontrivial linear function on $M_{end}$ to which $u$ converges. By performing an orthogonal transformation if necessary, noting that this does not disturb the Schwarzschild asymptotics of $g$, it may be assumed that $\ell = a_1 x^1$ for some $a_1 \neq 0$. Since $a_1^{-1} u$ is harmonic and has the same level sets as $u$, we may assume without loss of generality that $\ell = x^1$. In what follows $x^1$ will be denoted by $x$ for convenience.

The first step is to show that $\Sigma_t$ transversely intersects $S_r \subset M_{end}$, away from the north and south pole on the $x$-axis. More precisely, we claim that there exist $r_0 > 0$ and $c_0 > 0$ such that for $r \geq r_0$ and $|t| \leq r - c_0$, $\Sigma_t$ transversely intersects $S_r$. To see this observe that using (5.25), (5.26), and (5.27) yields

$$
\delta(\nabla u, \partial_r) = \frac{x}{r} \left( 1 + \frac{m}{2r} \right)^{-1} + \frac{mx}{2r^2} \left( 1 + \frac{m}{2r} \right)^{-2} + O(r^{-2}) = \frac{x}{r} + O(r^{-2}),
\tag{5.1}
$$

and

$$
|\nabla u|_\delta = 1 - \frac{m}{2r} + \frac{mx^2}{2r^3} + O(r^{-2}), \qquad |\partial_r|_\delta = 1.
\tag{5.2}
$$

Therefore

$$
\frac{\delta(\nabla u, \partial_r)}{|\nabla u|_\delta |\partial_r|_\delta} = \frac{x}{r} \left( 1 + \frac{m}{2r} - \frac{mx^2}{2r^3} \right) + O(r^{-2}),
\tag{5.3}
$$

so that for $|x| \leq r - c_*$ with appropriately chosen $c_* > 0$ we have

$$
|\cos\theta| = \frac{|\delta(\nabla u, \partial_r)|}{|\nabla u|_\delta |\partial_r|_\delta} \leq 1 - \frac{1}{r} + O(r^{-2}).
\tag{5.4}
$$

Here $\theta$ represents the angle between $\nabla u$ and $\partial_r$, which stays away from zero for large $r$. The desired claim now follows since $t = x + O(1)$ on $\Sigma_t \cap M_{end}$.

Now let $r \geq r_0$ and $|t| \leq r - c_0$ so that $\Sigma_t$ intersects $S_r$ transversely. Additionally, suppose that $t$ is a regular value of $u$. Since $\Sigma_t \cap S_r$ is transverse and nonempty, it consists of a finite number of disjoint embedded circles $\gamma_1, \ldots, \gamma_p$. Since, by Lemma 3.1, $\Sigma_t$ is connected and noncompact with only one end, removing the circles yields the decomposition

$$
\Sigma_t \setminus \cup_{i=1}^p \gamma_i = U \sqcup \mathcal{C},
\tag{5.5}
$$

where $U$ is unbounded and connected, and $\overline{\mathcal{C}}$ is bounded and compact. Evidently $\Sigma_t^r \subset \overline{\mathcal{C}}$. If $\overline{\mathcal{C}} \neq \Sigma_t^r$, then there is a path component $\mathcal{C}' \subset \overline{\mathcal{C}}$ which lies outside of $M_r$. Since $\mathcal{C}'$ is compact, there is a largest $r' > r$ so that $S_{r'} \cap \mathcal{C}' \neq \emptyset$, see Figure 3. In this intersection, $S_{r'}$ is tangential to $\Sigma_t$. This, however, contradicts the transversality established above. We conclude that $\Sigma_t^r = \mathcal{C}$.

Now assume that $\partial\Sigma_t^r$ is disconnected, so that there are at least two distinct circles $\gamma_1$ and $\gamma_2$. Since $U$ is connected, there is a path in $\overline{U}$ from $\gamma_1$ to $\gamma_2$. Let $r' > r$ be the smallest radius so that there is such a path $\sigma$ from $\gamma_1$ to $\gamma_2$ which lies entirely within $\Sigma_t^{r'}$, see Figure 4. Since $r'$ is the smallest such radius, $\sigma$ must intersect $S_{r'}$. At the intersection $\Sigma_t$ will be tangential to $S_{r'}$ since all perturbations of $\sigma$, within $\Sigma_t$ and supported on this intersection, either push $\sigma$ outside of $\Sigma_t^{r'}$

<!-- page 10 -->

*[Figure: Figure 3. The case where $\overline{\mathcal{C}} \neq \Sigma_t^r$ in the proof of Lemma 5.1.]*

or possess a point of tangency. This again contradicts transversality and we conclude that $\partial \Sigma_t^r$ is connected. Since $\Sigma_t^r$ has no closed components, all points in $\Sigma_t^r$ can be connected to its boundary and we conclude that $\Sigma_t^r$ itself is connected. $\square$

*[Figure: Figure 4. The argument showing $\partial \Sigma_t^r$ is connected in Lemma 5.1.]*

### 5.2. The Gaussian curvature.

The Gaussian curvature integral appearing in formula (4.7) in Proposition 4.2 will now be computed.

**Proposition 5.2.** *Suppose that* $(M, g)$ *is complete and Schwarzschildian. Let* $u$ *be a harmonic function of Lemma 3.1 which is asymptotic to a linear function* $\ell$*, and let* $\overline{u}$ *and* $\underline{u}$ *denote the maximum and minimum values of* $u$ *within* $M_r$*, respectively. Then*

$$
\int_{\underline{u}}^{\overline{u}} \int_{\Sigma_t^r} K dA dt \leq m\omega + O(r^{-1})
\tag{5.6}
$$

*for some constant* $\omega \in (0, \infty)$ *independent of* $r$*, where* $K$ *is the Gaussian curvature of* $\Sigma_t^r$*.*

*Proof.* As in the proof of Lemma 5.1 we may assume without loss of generality that $\ell = x$, where the asymptotic coordinates on $M_{end}$ will be denoted by $(x, y, z)$. Observe that on a $t$-level set

$$
t = u = \frac{x}{1 + \frac{m}{2r}} + \frac{a}{r} + O_2(r^{-2}),
\tag{5.7}
$$

<!-- page 11 -->

which implies that

$$
x = t + \frac{c(t)}{r} + O_2(r^{-2}), \qquad\qquad c(t) = \frac{tm}{2} - a.
\tag{5.8}
$$

In the expressions to follow, the subindex $l$ of $O_l$ will be ignored for convenience. By the implicit function theorem we may solve for $x = x(y, z)$ when $r$ is large. Let

$$
r^2 = x^2 + y^2 + z^2 = x^2 + \rho^2, \qquad\qquad \tilde{r}^2 = t^2 + \rho^2,
\tag{5.9}
$$

then a calculation shows that

$$
x(y, z) = t + \frac{c(t)}{\tilde{r}} + O(\tilde{r}^{-1}).
\tag{5.10}
$$

Furthermore, in the asymptotic end

$$
g = \left(1 + \frac{m}{2r}\right)^4 \left(dx^2 + dy^2 + dz^2\right),
\tag{5.11}
$$

so that the induced metric on $\Sigma_t^r \cap M_{end}$ is given by

$$
\gamma = \left(1 + \frac{m}{2r}\right)^4 \left((1 + x_y^2) dy^2 + 2 x_y x_z dy dz + (1 + x_z^2) dz^2\right).
\tag{5.12}
$$

From (5.8) the partial derivatives may be computed

$$
x_y = -\frac{c}{r^3}(x x_y + y) + O\left(\frac{|x x_y| + |y|}{r^4} + \frac{1}{r^3}\right) \qquad \Rightarrow \qquad x_y = -\frac{c(t) y}{r^3} + O(r^{-2}),
\tag{5.13}
$$

and similarly

$$
x_z = -\frac{c(t) z}{r^3} + O(r^{-2}).
\tag{5.14}
$$

Hence

$$
\gamma = \left(1 + \frac{m}{2r}\right)^4 \left[\left(1 + \frac{c^2 y^2}{r^6}\right) dy^2 + \frac{2 c^2 y z}{r^6} dy dz + \left(1 + \frac{c^2 z^2}{r^6}\right) dz^2 + O(r^{-3}) dx^i dx^j\right].
\tag{5.15}
$$

Since the Gauss curvature consists of second derivatives and quadratic first derivatives, it follows that

$$
K = O(r^{-3}).
\tag{5.16}
$$

Let $r_0 > 0$ and $c_0 > 0$ be the constants given by Lemma 5.1. From now on, we will only consider $r \geq r_0$. Let $\overline{u}$ and $\underline{u}$ be the max and min levels for $u$ within $M_r$. Then $\overline{u} = r - \frac{m}{2} + O(r^{-1})$ and $\underline{u} = -r - \frac{m}{2} + O(r^{-1})$. At this point, we will break the interval $[\underline{u}, \overline{u}]$ into three pieces: $[\underline{u}, -r + c_0]$, $[-r + c_0, r - c_0]$, and $[r - c_0, \overline{u}]$, see Figure 5. Consider $t \in [r - c_0, \overline{u}]$, then $0 \leq \rho \leq c_1 \sqrt{r}$ for some constant $c_1$. On this region all $t$-levels are regular and

$$
\int_{\Sigma_t^r} K dA = O\left(\frac{\rho^2}{r^3}\right) = O(r^{-2}),
\tag{5.17}
$$

so that

$$
\int_{r - c_0}^{\overline{u}} \left(\int_{\Sigma_t^r} K dA\right) dt = O(r^{-1}),
\tag{5.18}
$$

and similarly

$$
\int_{\underline{u}}^{-r + c_0} \left(\int_{\Sigma_t^r} K dA\right) dt = O(r^{-1}).
\tag{5.19}
$$

<!-- page 12 -->

*[Figure: Figure 5. The decomposition of $M_r$ used to estimate the integral in Proposition 5.2.]*

Now let us restrict attention to the range $|t| \leq r - c_0$, so that $c_2 \sqrt{r} \leq \rho \leq r$ for some constant $c_2 > 0$. According to Lemma 5.1, for regular values $t$ in this range, $\Sigma_t^r$ is a connected smooth submanifold with boundary $\partial \Sigma_t^r = S^1 \subset S_r$. Let $\alpha : [0, \theta_0] \to \partial \Sigma_t^r$ be a parameterization and let $\tilde{\nu}$ be an inward pointing normal vector to $\partial \Sigma_t^r$ tangent to $\Sigma_t^r$, both to be chosen later. The geodesic curvature of the circle $\partial \Sigma_t^r$ is given by

$$
\kappa = \left\langle \nu, \nabla_{\frac{\alpha'}{|\alpha'|}} \frac{\alpha'}{|\alpha'|} \right\rangle = \frac{\langle \tilde{\nu}, \nabla_{\alpha'} \alpha' \rangle}{|\tilde{\nu}| |\alpha'|^2},
\tag{5.20}
$$

where $\nabla$ is the Levi-Civita connection for $g = \langle \cdot, \cdot \rangle$, $\nu = \frac{\tilde{\nu}}{|\tilde{\nu}|}$ is the unit normal of $\partial \Sigma_t^r$ tangent to $\Sigma_t^r$, and $\alpha' = \partial_\theta \alpha$ is the velocity vector associated with $\alpha$. Write this curve as

$$
\alpha(\theta) = (x(\theta), y(\theta), z(\theta))
\tag{5.21}
$$

where these functions are defined by the equations

$$
x(\theta)^2 + y(\theta)^2 + z(\theta)^2 = r^2, \qquad\qquad u(\alpha(\theta)) = t.
\tag{5.22}
$$

In order to compute $\alpha'$, observe that the equations defining $\alpha'$ (up to scaling) are

$$
\alpha \cdot \alpha' = 0, \qquad\qquad \nabla u \cdot \alpha' = 0,
\tag{5.23}
$$

where $\cdot$ represents the Euclidean inner product. It follows that $\alpha$ and $\theta_0$ can be chosen so that

$$
\alpha' = (z u_y - y u_z) \partial_x + (x u_z - z u_x) \partial_y + (y u_x - x u_y) \partial_z.
\tag{5.24}
$$

The partial derivatives have the expansions

$$
u_x = \left(1 + \frac{m}{2r}\right)^{-1} - x \left(1 + \frac{m}{2r}\right)^{-2} \left(\frac{-mx}{2r^3}\right) - \frac{ax}{r^3} + O(r^{-2}) = 1 - \frac{m}{2r} + \frac{mx^2}{2r^3} + O(r^{-2}),
\tag{5.25}
$$

$$
u_y = -x \left(1 + \frac{m}{2r}\right)^{-2} \left(\frac{-my}{2r^3}\right) - \frac{ay}{r^3} + O(r^{-2}) = \frac{mxy}{2r^3} + O\left(\frac{\rho}{r^3} + \frac{1}{r^2}\right),
\tag{5.26}
$$

<!-- page 13 -->

$$
u_z = -x\left(1+\frac{m}{2r}\right)^{-2}\left(\frac{-mz}{2r^3}\right) - \frac{az}{r^3} + O(r^{-2}) = \frac{mxz}{2r^3} + O\left(\frac{\rho}{r^3}+\frac{1}{r^2}\right). \tag{5.27}
$$

Therefore

$$
\alpha' = \alpha'_x\partial_x + \alpha'_y\partial_y + \alpha'_z\partial_z = O\left(\frac{\rho}{r^2}\right)\partial_x + \left(-z+\frac{mz}{2r}+O\left(\frac{\rho}{r^2}\right)\right)\partial_y + \left(y-\frac{my}{2r}+O\left(\frac{\rho}{r^2}\right)\right)\partial_z, \tag{5.28}
$$

and

$$
|\alpha'|^2 = \left(1+\frac{m}{2r}\right)^4\left[O\left(\frac{\rho^2}{r^2}\right)+\rho^2\left(1-\frac{m}{r}+\frac{m^2}{4r^2}\right)\right] = \rho^2\left(1+\frac{m}{r}+O(r^{-2})\right). \tag{5.29}
$$

At this point, it is convenient to estimate the value $\theta_0$ of the parameterizing interval. On one hand, the length of $\partial\Sigma_t^r$ may be computed from (5.29),

$$
\mathrm{Length}(\partial\Sigma_t^r) = \int_0^{\theta_0}|\alpha'|d\theta = \int_0^{\theta_0}\rho\left(1+\frac{m}{2r}+O(r^{-2})\right)d\theta. \tag{5.30}
$$

On the other hand, we can parameterize the $yz$-projection of $\partial\Sigma_t^r$ by $\vartheta\mapsto(\rho(\vartheta)\cos\vartheta,\rho(\vartheta)\sin\vartheta)$ for $\vartheta\in[0,2\pi]$, and use (5.15) to find

$$
\mathrm{Length}(\partial\Sigma_t^r) = \int_0^{2\pi}\sqrt{\det\gamma|_{\partial\Sigma_t^r}}\,d\vartheta = \int_0^{2\pi}\rho\left(1+\frac{m}{r}+O(r^{-2})\right)d\vartheta. \tag{5.31}
$$

Using (5.8), it follows that $\rho=\sqrt{r^2-x^2}$ is a constant (depending on $r$ and $t$) along $\partial\Sigma_t^r$ up to $O(r^{-2})$. Thus we may subtract (5.30) and (5.31) to obtain

$$
\theta_0 = 2\pi\left(1+\frac{m}{2r}+O(r^{-2})\right). \tag{5.32}
$$

Let us return to our calculation of (5.20). The normal vector $\tilde{\nu}$ must satisfy

$$
\alpha'\cdot\tilde{\nu}=0, \qquad \nabla u\cdot\tilde{\nu}=0, \tag{5.33}
$$

and so we may choose

$$
\tilde{\nu} = (\alpha'_z u_y - \alpha'_y u_z)\partial_x + (\alpha'_x u_z - \alpha'_z u_x)\partial_y + (\alpha'_y u_x - \alpha'_x u_y)\partial_z. \tag{5.34}
$$

It follows that the components have the expansions

$$
\tilde{\nu}_x = \alpha'_z u_y - \alpha'_y u_z = \frac{mx\rho^2}{2r^3} + O\left(\frac{\rho}{r^2}\right), \tag{5.35}
$$

$$
\tilde{\nu}_y = \alpha'_x u_z - \alpha'_z u_x = -y + \frac{my}{r} - \frac{mx^2y}{2r^3} + O\left(\frac{\rho}{r^2}\right), \tag{5.36}
$$

$$
\tilde{\nu}_z = \alpha'_y u_x - \alpha'_x u_y = -z + \frac{mz}{r} - \frac{mx^2z}{2r^3} + O\left(\frac{\rho}{r^2}\right), \tag{5.37}
$$

and

$$
|\tilde{\nu}|^2 = \rho^2\left(1+\frac{m}{2r}\right)^4\left(1-\frac{2m}{r}+\frac{mx^2}{r^3}+O(r^{-2})\right) = \rho^2\left(1+\frac{mx^2}{r^3}+O(r^{-2})\right). \tag{5.38}
$$

We now compute the covariant derivative portion of (5.20). Observe that

$$
\nabla_{\alpha'}\alpha' = \alpha'^{i}\nabla_i\left(\alpha'^{j}\partial_j\right) = \left(\alpha'^{i}\partial_i\alpha'^{j}\right)\partial_j + \alpha'^{i}\alpha'^{j}\Gamma_{ij}^{l}\partial_l, \tag{5.39}
$$

where $\Gamma_{ij}^l$ are Christoffel symbols. Furthermore

$$
\alpha'^{i}\partial_i\alpha'_x = O\left(\frac{\rho}{r^2}\right), \tag{5.40}
$$

<!-- page 14 -->

$$
\begin{aligned}
\alpha'^{i}\partial_i\alpha'_y =& O\left(\frac{\rho}{r^2}\right)O\left(\frac{\rho}{r^2}\right) + \left(-z+\frac{mz}{2r}+O\left(\frac{\rho}{r^2}\right)\right)\left(-\frac{myz}{2r^3}+O\left(\frac{1}{r^2}+\frac{\rho^2}{r^4}\right)\right)\\
&+\left(y-\frac{my}{2r}+O\left(\frac{\rho}{r^2}\right)\right)\left(-1+\frac{m}{2r}-\frac{mz^2}{2r^3}+O\left(\frac{1}{r^2}+\frac{\rho^2}{r^4}\right)\right)\\
=&-y+\frac{my}{r}+O\left(\frac{\rho}{r^2}+\frac{\rho^3}{r^4}\right),
\end{aligned} \tag{5.41}
$$

$$
\begin{aligned}
\alpha'^{i}\partial_i\alpha'_z =& O\left(\frac{\rho}{r^2}\right)O\left(\frac{\rho}{r^2}\right) + \left(-z+\frac{mz}{2r}+O\left(\frac{\rho}{r^2}\right)\right)\left(1-\frac{m}{2r}+\frac{my^2}{2r^3}+O\left(\frac{1}{r^2}+\frac{\rho^2}{r^4}\right)\right)\\
&+\left(y-\frac{my}{2r}+O\left(\frac{\rho}{r^2}\right)\right)\left(\frac{myz}{2r^3}+O\left(\frac{1}{r^2}+\frac{\rho^2}{r^4}\right)\right)\\
=&-z+\frac{mz}{r}+O\left(\frac{\rho}{r^2}+\frac{\rho^3}{r^4}\right).
\end{aligned} \tag{5.42}
$$

Hence

$$
\nabla_{\alpha'}\alpha' = \left(-y+\frac{my}{r}\right)\partial_y + \left(-z+\frac{mz}{r}\right)\partial_z + O\left(\frac{\rho}{r^2}\right)\partial_l + \alpha'^{i}\alpha'^{j}\Gamma_{ij}^{l}\partial_l. \tag{5.43}
$$

To compute the Christoffel symbols write let $w=1+\frac{m}{2r}$ and use (5.11) to find

$$
\begin{aligned}
\Gamma_{ij}^{l} =& \frac{1}{2}g^{lk}\left(\partial_i g_{kj}+\partial_j g_{ki}-\partial_k g_{ij}\right)\\
=& \frac{1}{2}w^{-4}\delta^{lk}\left(\delta_{kj}\partial_i w^4+\delta_{ki}\partial_j w^4-\delta_{ij}\partial_k w^4\right)\\
=& 2\left(\delta_j^l\partial_i\log w+\delta_i^l\partial_j\log w-\delta_{ij}\partial^l\log w\right).
\end{aligned} \tag{5.44}
$$

Therefore using the orthogonality of $\tilde{\nu}$ and $\alpha'$ yields

$$
\langle\tilde{\nu},\alpha'^{i}\alpha'^{j}\Gamma_{ij}^{l}\partial_l\rangle = w^4\delta_{kl}\tilde{\nu}^k\alpha'^{i}\alpha'^{j}\Gamma_{ij}^{l} = -2|\alpha'|^2\tilde{\nu}^l\partial_l\log w. \tag{5.45}
$$

Since

$$
\tilde{\nu}^l\partial_l\log w = \tilde{\nu}^l\left(1+\frac{m}{2r}\right)^{-1}\left(-\frac{mx^l}{2r^3}\right) = \frac{m\rho^2}{2r^3}+O(r^{-2}), \tag{5.46}
$$

we then have

$$
\langle\tilde{\nu},\alpha'^{i}\alpha'^{j}\Gamma_{ij}^{l}\partial_l\rangle = -\frac{m\rho^4}{r^3}+O\left(\frac{\rho^2}{r^2}\right). \tag{5.47}
$$

Putting this altogether produces

$$
\begin{aligned}
\langle\tilde{\nu},\nabla_{\alpha'}\alpha'\rangle =& \left(1+\frac{m}{2r}\right)^4\Bigg[O\left(\frac{\rho}{r^2}\right)O\left(\frac{|x|\rho}{r^2}+\frac{\rho}{r^2}\right)-\frac{m\rho^4}{r^3}+O\left(\frac{\rho^2}{r^2}\right)\\
&+\left(-y+\frac{my}{r}-\frac{mx^2y}{2r^3}+O\left(\frac{\rho}{r^2}\right)\right)\left(-y+\frac{my}{r}+O\left(\frac{\rho}{r^2}\right)\right)\\
&+\left(-z+\frac{mz}{r}-\frac{mx^2z}{2r^3}+O\left(\frac{\rho}{r^2}\right)\right)\left(-z+\frac{mz}{r}+O\left(\frac{\rho}{r^2}\right)\right)\Bigg]\\
=&\rho^2\left(1+\frac{mx^2}{2r^3}-\frac{m\rho^2}{r^3}+O(r^{-2})\right).
\end{aligned} \tag{5.48}
$$

<!-- page 15 -->

We also have

$$
|\tilde{\nu}||\alpha'| = \rho^2\left(1+\frac{m}{2r}+\frac{mx^2}{2r^3}+O(r^{-2})\right), \tag{5.49}
$$

and therefore

$$
\frac{\langle\tilde{\nu},\nabla_{\alpha'}\alpha'\rangle}{|\tilde{\nu}||\alpha'|} = 1-\frac{m}{2r}-\frac{m\rho^2}{r^3}+O(r^{-2}). \tag{5.50}
$$

Combining this with (5.32) we find that

$$
\int_{\partial\Sigma_t^r}\kappa ds = \int_0^{\theta_0}\frac{\langle\tilde{\nu},\nabla_{\alpha'}\alpha'\rangle}{|\tilde{\nu}||\alpha'|}d\theta = 2\pi\left(1-\frac{m}{r}+\frac{mt^2}{r^3}\right)+O(r^{-2}). \tag{5.51}
$$

By Sard's theorem we may restrict attention to regular level sets when computing (5.6). Moreover since for regular levels in the range $|t|\leq r-c_0$ with $r\geq r_0$, the compact surface $\Sigma_t^r$ is connected with nonempty boundary (Lemma 5.1), its Euler characteristic satisfies $\chi(\Sigma_t^r)\leq 1$. Thus using (5.18), (5.19), and the Gauss-Bonnet theorem we find that

$$
\begin{aligned}
\int_{\underline{u}}^{\overline{u}}\int_{\Sigma_t^r}Kd\mathcal{H}dt =& \int_{-r+c_0}^{r-c_0}\left(2\pi\chi(\Sigma_t^r)-\int_{\Sigma_t^r}\kappa ds\right)dt\\
&+\int_{\underline{u}}^{-r+c_0}\left(\int_{\Sigma_t^r}KdA\right)dt+\int_{r-c_0}^{\overline{u}}\left(\int_{\Sigma_t^r}KdA\right)dt\\
\leq&\frac{8\pi}{3}m+O(r^{-1}).
\end{aligned} \tag{5.52}
$$

$\square$

### 5.3. Proof of the positive mass theorem.

*Proof of Theorem 2.3.* Let $(M,g)$ be complete with nonnegative scalar curvature and Schwarzschildian. Consider the harmonic function $u$ of Lemma 3.1 asymptotic to the linear function $\ell(x,y,z)=x$. Apply identity (4.7) of Proposition 4.2 to $\Omega=M_r$ to obtain

$$
\int_{S_r}\partial_\upsilon|\nabla u|dA \geq \frac{1}{2}\int_{\underline{u}}^{\overline{u}}\int_{\Sigma_t^r}\left(\frac{|\nabla^2u|^2}{|\nabla u|^2}+R_g-2K\right)dAdt, \tag{5.53}
$$

where $\overline{u}$ and $\underline{u}$ denote the maximum and minimum values of $u$ on $M_r$, and $K$ is the Gaussian curvature of $\Sigma_t^r$.

In order to compute the boundary integral in (5.53), use (5.25), (5.26), and (5.27) to find

$$
|\nabla u| = \left(1+\frac{m}{2r}\right)^{-2}\left(u_x^2+u_y^2+u_z^2\right)^{\frac{1}{2}} = 1-\frac{3m}{2r}+\frac{mx^2}{2r^3}+O_1(r^{-2}). \tag{5.54}
$$

It follows that

$$
\partial_\upsilon|\nabla u| = \left(1+\frac{m}{2r}\right)^{-2}\partial_r|\nabla u| = \frac{3m}{2r^2}-\frac{mx^2}{2r^4}+O(r^{-3}), \tag{5.55}
$$

and therefore

$$
\int_{S_r}\partial_\upsilon|\nabla u|dA = 4\pi\left(\frac{3m}{2}-\frac{m}{6}\right)+O(r^{-1}) = \frac{16\pi}{3}m+O(r^{-1}), \tag{5.56}
$$

where we have used

$$
\int_{S_r}x^2dA_\delta = \frac{1}{3}\int_{S_r}(x^2+y^2+z^2)dA_\delta = \frac{1}{3}\int_{S_r}r^2dA_\delta = \frac{4\pi}{3}r^4. \tag{5.57}
$$

<!-- page 16 -->

This combined with Proposition 5.2 and letting $r \to \infty$ yields

$$
16\pi m \geq \int_{-\infty}^{\infty} \int_{\Sigma_t} \left( \frac{|\nabla^2 u|^2}{|\nabla u|^2} + R_g \right) dA dt, \tag{5.58}
$$

from which we find that $m \geq 0$.

Consider now the case of equality $m = 0$. Inequality (5.58) implies that $R_g \equiv 0$ and $|\nabla^2 u| \equiv 0$. In particular, $\nabla u$ is a parallel vector field. The same procedure above may be applied to second and third harmonic functions $v$ and $w$ of Lemma 3.1 asymptotic to the linear functions $\ell = y$ and $\ell = z$, respectively, so that $\nabla v$ and $\nabla w$ are also parallel. Since these three vector fields are linearly independent, $(M, g)$ is flat. Since $(M, g)$ is also complete it must be isometric to Euclidean 3-space. $\square$

*Proof of Theorem 1.1.* Let $(M, g)$ be complete of nonnegative scalar curvature, and asymptotically flat with $m$ the mass of a designated end $M_{end}^{+}$. Let $(\overline{M}, \overline{g})$ be the Schwarzschildian manifold of Proposition 2.1 with mass $\overline{m}$ satisfying $|m - \overline{m}| < \varepsilon$. According to Theorem 2.3, $\overline{m} \geq 0$. Since $\varepsilon > 0$ is arbitrarily small, we conclude that $m \geq 0$.

The conclusion in the case of equality, $m = 0$, follows from the positive mass inequality as in [13]. Namely, one shows through conformal deformation that $(M, g)$ is scalar flat, and then that it is Ricci flat via an infinitesimal Ricci flow. $\square$

## 6. The Harmonic Coordinate Method

In this section, we give another way to derive the total mass of an asymptotically flat manifold. Instead of using the trick of approximating by Schwarzschild metrics as in the previous section, we show how the mass term falls out naturally from our boundary term at infinity. Let $(M, g)$ be a complete asymptotically flat Riemannian 3-manifold, and let $M_{ext}$ be the exterior region associated with a specified end $M_{end}$. According to [7, Lemma 4.1] the exterior region is diffeomorphic to $\mathbb{R}^3$ minus a finite number of disjoint balls, and has minimal boundary. Let $\{x^1, x^2, x^3\}$ be harmonic coordinates on $M_{ext}$ as in Section 3.2, with homogeneous Neumann condition on $\partial M_{ext}$, and let $\vec{x} = (x^1, x^2, x^3)$. For a unit vector $a \in S^2 \subset \mathbb{R}^3$, it obviously follows that $u = \vec{x} \cdot a$ is harmonic on $M_{ext}$ with homogeneous Neumann condition. For $L > 0$ sufficiently large, consider the coordinate cylinders $C_L := D_L^{\pm} \cup T_L$ where

$$
D_L^{\pm} := \{\vec{x} \mid \vec{x} \cdot a = \pm L,\ |\vec{x}|^2 - (\vec{x} \cdot a)^2 \leq L^2\}, \quad T_L := \{\vec{x} \mid |\vec{x} \cdot a| \leq L,\ |\vec{x}|^2 - (\vec{x} \cdot a)^2 = L^2\}. \tag{6.1}
$$

Set $\Omega_L \subset M_{ext}$ to be the closure of the bounded component of $M_{ext} \setminus C_L$. Following the arguments of [1, Section 4], if the scalar curvature $R_g$ is integrable then the mass of $M_{ext}$ is given by

$$
m = \lim_{L \to \infty} \frac{1}{16\pi} \int_{C_L} \sum_i (g_{ij,i} - g_{ii,j}) \upsilon^j dA. \tag{6.2}
$$

where $\upsilon$ is the outward unit normal to $C_L$.

### 6.1. Computation of the mass.

To prove inequality (1.3), begin by applying Proposition 4.2 to $u$ on the cylindrical domains $\Omega_L$ (so that $P_2 = C_L$ and $P_1 = \partial M_{ext}$) to find that

$$
\frac{1}{2} \int_{\Omega_L} \left( \frac{|\nabla^2 u|^2}{|\nabla u|} + R_g |\nabla u| \right) dV \leq \int_{-L}^{L} \left( 2\pi \chi(\Sigma_t^L) - \int_{\Sigma_t^L \cap T_L} \kappa_{t,L} \right) dt + \int_{C_L} \partial_\upsilon |\nabla u| dA, \tag{6.3}
$$

where $\Sigma_t^L := \{u = t\} \cap \Omega_L$, and $\kappa_{t,L}$ is the geodesic curvature of the curve $\Sigma_t^L \cap T_L$ viewed as the boundary of $\Sigma_t$. Note that the asymptotics guarantee that, for $L$ sufficiently large, the level sets $\Sigma_t^L$

<!-- page 17 -->

indeed meet $T_L$ transversely. We claim next that for every regular value $t \in (-L, L)$, $\Sigma_t^L$ consists of a single connected component, intersecting $T_L$ along the circle $\Sigma_t^L \cap T_L$. Indeed, if this is not the case, then there is a regular value $t \in (-L, L)$ and a component $\Sigma' \subset \Sigma_t^L$ disjoint from $T_L$. Since $M_{ext}$ is diffeomorphic to the compliment of finitely many balls in $\mathbb{R}^3$, there is a domain $E \subset \Omega_L$ such that $\partial E \setminus \partial M_{ext} = \Sigma'$ and $E \cap T_L = \varnothing$. But since $u$ is harmonic with Neumann boundary conditions on $\partial M_{ext}$ and identically $t$ on $\Sigma'$, the maximum principle would then imply that $u \equiv t$ in $E$, contradicting the fact that $t$ is a regular value. Thus, $\Sigma_t^L$ has only one component, with boundary given by $\Sigma_t^L \cap T_L$, and as a consequence $\chi(\Sigma_t^L) \leq 1$. In particular, applying this in the preceding computation gives

$$
\frac{1}{2} \int_{\Omega_L} \left( \frac{|\nabla^2 u|^2}{|\nabla u|} + R_g |\nabla u| \right) dV \leq 4\pi L - \int_{-L}^{L} \left( \int_{\Sigma_t^L \cap T_L} \kappa_{t,L} \right) dt + \int_{C_L} \partial_\upsilon |\nabla u| dA. \tag{6.4}
$$

The remainder of the proof of Theorem 1.2 rests on a computation of the boundary terms in inequality (6.4). To carry out these computations, it will be useful to take $a = \partial_{x^1}$, so that $u = x^1$ is the distinguished coordinate. In what follows the notation $\int_{D_L^{\pm}} \pm f$ represents $\int_{D_L^{+}} f - \int_{D_L^{-}} f$.

**Lemma 6.1.** *In the notation fixed above, we have*

$$
\begin{aligned}
\int_{C_L} \partial_\upsilon |\nabla u| dA = & \frac{1}{2} \int_{D_L^{\pm}} \pm \sum_j (g_{1j,j} - g_{jj,1}) dA \\
& + \frac{1}{2L} \int_{T_L} \left[ x^2 (g_{21,1} - g_{11,2}) + x^3 (g_{31,1} - g_{11,3}) \right] dA + O(L^{1-2q}).
\end{aligned} \tag{6.5}
$$

*Proof.* To begin, note that

$$
\nabla |\nabla u| = \nabla (g^{11})^{1/2} = -\frac{1}{2} \nabla g_{11} + O(|x|^{-1-2q}), \tag{6.6}
$$

where in the second line we have used the decay rates (3.7). Next since the outer normal $\upsilon$ to $C_L$ is given by

$$
\upsilon = \pm \partial_1 + O(|x|^{-q}) \quad \text{ on } \quad D_L^{\pm}, \quad \text{ and } \quad \upsilon = \frac{x^2 \partial_2 + x^3 \partial_3}{L} + O(|x|^{-q}) \quad \text{ on } T_L, \tag{6.7}
$$

it follows that

$$
\int_{C_L} \partial_\upsilon |\nabla u| dA = -\frac{1}{2} \int_{D_L^{\pm}} \pm g_{11,1} dA - \frac{1}{2L} \int_{T_L} (x^2 g_{11,2} + x^3 g_{11,3}) dA + O(L^{1-2q}). \tag{6.8}
$$

Now, because $x^1$ is harmonic we see that

$$
\begin{aligned}
g_{11,1} = & -2g(\nabla_{\partial_1} \partial_1, \partial_1) + O(|x|^{-1-2q}) \\
= & 2g(\nabla_{\partial_2} \partial_1, \partial_2) + 2g(\nabla_{\partial_3} \partial_1, \partial_3) + O(|x|^{-1-2q}) \\
= & -2g_{21,2} - 2g_{31,3} + g_{22,1} + g_{33,1} + O(|x|^{-1-2q}),
\end{aligned} \tag{6.9}
$$

<!-- page 18 -->

and therefore

$$
\begin{aligned}
\int_{C_L} \partial_\upsilon |\nabla u| dA = & \int_{D_L^{\pm}} \pm (g_{12,2} + g_{13,3} - \frac{1}{2} g_{22,1} - \frac{1}{2} g_{33,1}) dA \\
& - \frac{1}{2L} \int_{T_L} (x^2 g_{11,2} + x^3 g_{11,3}) dA + O(L^{1-2q}) \\
= & \frac{1}{2} \int_{D_L^{\pm}} \pm (g_{12,2} - g_{22,1} + g_{13,3} - g_{33,1}) dA \\
& + \int_{D_L^{+}} \frac{1}{2} (g_{12,2} + g_{13,3}) dA - \int_{D_L^{-}} \frac{1}{2} (g_{12,2} + g_{13,3}) dA \\
& - \frac{1}{2L} \int_{T_L} (x^2 g_{11,2} + x^3 g_{11,3}) dA + O(L^{1-2q}).
\end{aligned} \tag{6.10}
$$

Applying the divergence theorem to the penultimate line above, and subsequently employing the fundamental theorem of calculus on $T_L$ yields

$$
\begin{aligned}
\int_{C_L} \partial_\upsilon |\nabla u| dA = & \frac{1}{2} \int_{D_L^{\pm}} \pm (g_{12,2} - g_{22,1} + g_{13,3} - g_{33,1}) dA \\
& + \int_{\partial D_L^{+}} \frac{1}{2L} (x^2 g_{12} + x^3 g_{13}) dA - \int_{\partial D_L^{-}} \frac{1}{2L} (x^2 g_{12} + x^3 g_{13}) dA \\
& - \frac{1}{2L} \int_{T_L} (x^2 g_{11,2} + x^3 g_{11,3}) dA + O(L^{1-2q}) \\
= & \frac{1}{2} \int_{D_L^{\pm}} \pm (g_{12,2} - g_{22,1} + g_{13,3} - g_{33,1}) dA + \int_{T_L} \partial_1 \left( \frac{x^2}{2L} g_{12} + \frac{x^3}{2L} g_{13} \right) dA \\
& - \frac{1}{2L} \int_{T_L} (x^2 g_{11,2} + x^3 g_{11,3}) dA + O(L^{1-2q}) \\
= & \frac{1}{2} \int_{D_L^{\pm}} \pm (g_{12,2} - g_{22,1} + g_{13,3} - g_{33,1}) dA \\
& + \frac{1}{2L} \int_{T_L} [x^2 (g_{21,1} - g_{11,2}) + x^3 (g_{31,1} - g_{11,3})] dA + O(L^{1-2q}).
\end{aligned} \tag{6.11}
$$

$\square$

**Lemma 6.2.** *In the notation established above, we have*

$$
\begin{aligned}
\int_{-L}^{L} \left( \int_{\Sigma_t^L \cap T_L} \kappa_{t,L} \right) dt = & 4\pi L + \frac{1}{2L} \int_{T_L} \left[ x^2 (g_{33,2} - g_{23,3}) + x^3 (g_{22,3} - g_{32,2}) \right] dA \\
& + O(L^{1-2q} + L^{-q}).
\end{aligned} \tag{6.12}
$$

*Proof.* To begin, recall that the geodesic curvature $\kappa_{t,L}$ is given by

$$
\kappa_{t,L} = \langle \nabla_\tau \beta, \tau \rangle = -\langle \beta, \nabla_\tau \tau \rangle, \tag{6.13}
$$

where $\tau$ is a unit tangent vector to $\Sigma_t^L \cap T_L$ and $\beta$ is the outward pointing unit normal to $\Sigma_t^L \cap T_L$ along $\Sigma_t^L$. Let

$$
X := x^2 \partial_2 + x^3 \partial_3 \quad \text{ and } \quad Y := x^3 \partial_2 - x^2 \partial_3. \tag{6.14}
$$

<!-- page 19 -->

Then by setting $\tilde{X} := X - \langle X, \tau \rangle \tau$ we may take

$$
\tau = \frac{Y}{|Y|} \quad \text{ and } \quad \beta = \frac{\tilde{X}}{|\tilde{X}|}. \tag{6.15}
$$

Consequently

$$
\kappa_{t,L} = -\left\langle \frac{\tilde{X}}{|\tilde{X}|}, \nabla_{\tau} \tau \right\rangle = \frac{-1}{|\tilde{X}||Y|^3} \left( |Y| \langle X, \nabla_Y Y \rangle - \langle X, Y \rangle \langle \nabla |Y|, Y \rangle \right). \tag{6.16}
$$

The decay conditions (3.7) imply that

$$
|\nabla |Y|| = O(|x|^{-q}) \quad \text{ and } \quad \langle X, Y \rangle = O(|x|^{2-q}). \tag{6.17}
$$

It follows that

$$
\frac{\langle X, Y \rangle \langle \nabla |Y|, Y \rangle}{|\tilde{X}||Y|^3} = O\left( \frac{|x|^{2-q} |x|^{-q} |x|}{|x|^4} \right) = O(|x|^{-1-2q}), \tag{6.18}
$$

and hence

$$
\kappa_{t,L} = \frac{-\langle X, \nabla_Y Y \rangle}{|\tilde{X}||Y|^2} + O(|x|^{-1-2q}). \tag{6.19}
$$

A direct computation gives

$$
\nabla_Y Y = -X + (x^3)^2 \nabla_{\partial_2} \partial_2 + (x^2)^2 \nabla_{\partial_3} \partial_3 - 2 x^2 x^3 \nabla_{\partial_2} \partial_3. \tag{6.20}
$$

Upon expanding $\langle X, \nabla_Y Y \rangle = \langle x^2 \partial_2 + x^3 \partial_3, \nabla_Y Y \rangle$ in terms of the metric derivatives, we see that (6.16) becomes

$$
\begin{aligned}
\kappa_{t,L} =& \frac{|X|^2}{|\tilde{X}||Y|^2} + O(L^{-1-2q}) - \frac{\langle X, (x^3)^2 \nabla_{\partial_2} \partial_2 + (x^2)^2 \nabla_{\partial_3} \partial_3 - 2 x^2 x^3 \nabla_{\partial_2} \partial_3 \rangle}{L^3} \\
=& \frac{|X|}{|Y|^2} + O(L^{-2-q} + L^{-1-2q}) - \frac{1}{2L^3} (x^2 (x^3)^2 g_{22,2} + (x^2)^2 x^3 g_{33,3}) \\
& + [(x^2)^2 x^3 + \frac{1}{2} (x^3)^3] \frac{g_{22,3}}{L^3} + [(x^3)^2 x^2 + \frac{1}{2} (x^2)^3] \frac{g_{33,2}}{L^3} - (x^2)^3 \frac{g_{23,3}}{L^3} - (x^3)^3 \frac{g_{32,2}}{L^3},
\end{aligned} \tag{6.21}
$$

where the decay properties (3.7) have been used repeatedly. At this point it will be useful to parameterize $\Sigma_t^L \cap T_L$ by

$$
[0, 2\pi] \ni s \mapsto \gamma(s) := (t, L \cos(s), L \sin(s)).
$$

Notice that $\gamma'(s) = -Y$. We then have

$$
\begin{aligned}
\int_{\Sigma_t^L \cap T_L} \frac{|X|}{|Y|^2} =& \int_0^{2\pi} \left( |Y| \frac{|X|}{|Y|^2} \right) (\gamma(s)) ds \\
=& \int_0^{2\pi} \left( 1 + \frac{|X| - |Y|}{|Y|} \right) (\gamma(s)) ds \\
=& 2\pi + \int_0^{2\pi} \left( \frac{|X|^2 - |Y|^2}{|Y|(|X| + |Y|)} \right) (\gamma(s)) ds \\
=& 2\pi + \frac{1}{2L^2} \int_0^{2\pi} (|X|^2 - |Y|^2)(\gamma(s)) ds + O(L^{-2q}).
\end{aligned} \tag{6.22}
$$

<!-- page 20 -->

Next compute

$$
\begin{aligned}
& \frac{1}{L^2} \int_0^{2\pi} (|X|^2 - |Y|^2)(\gamma(s)) ds \\
=& \int_0^{2\pi} (\cos^2(s) - \sin^2(s)) g_{22}(\gamma(s)) ds + \int_0^{2\pi} (\sin^2(s) - \cos^2(s)) g_{33}(\gamma(s)) ds \\
& + \int_0^{2\pi} 4 \sin(s) \cos(s) g_{23}(\gamma(s)) ds \\
=& \int_0^{2\pi} \frac{1}{2} \frac{d}{ds} [\sin(2s)] g_{22}(\gamma(s)) ds - \int_0^{2\pi} \frac{1}{2} \frac{d}{ds} [\sin(2s)] g_{33}(\gamma(s)) ds \\
& - \int_0^{2\pi} \frac{d}{ds} [\cos(2s)] g_{23}(\gamma(s)) ds \\
=& \frac{1}{L^2} \int_0^{2\pi} [x^2 x^3 (x^3 g_{22,2} - x^2 g_{22,3})] \circ \gamma ds + \frac{1}{L^2} \int_0^{2\pi} [x^2 x^3 (x^2 g_{33,3} - x^3 g_{33,2})] \circ \gamma ds \\
& + \frac{1}{L^2} \int_0^{2\pi} [((x^2)^2 - (x^3)^2)(x^2 g_{23,3} - x^3 g_{23,2})] \circ \gamma ds,
\end{aligned} \tag{6.23}
$$

where in the final line we have integrated by parts and used the double angle formulas to write $\sin(2s)$ and $\cos(2s)$ in terms of $x^2$ and $x^3$. Combining this with (6.22) produces

$$
\begin{aligned}
\int_{\Sigma_t^L \cap T_L} \frac{|X|}{|Y|^2} =& 2\pi + \frac{1}{2L^3} \int_{\Sigma_t^L \cap T_L} x^2 x^3 [x^3 g_{22,2} + x^2 g_{33,3}] + O(L^{-2q}) \\
& - \frac{1}{2L^3} \int_{\Sigma_t^L \cap T_L} x^2 x^3 [x^2 g_{22,3} + x^3 g_{33,2}] \\
& + \frac{1}{2L^3} \int_{\Sigma_t^L \cap T_L} [(x^2)^2 - (x^3)^2](x^2 g_{23,3} - x^3 g_{32,2}).
\end{aligned} \tag{6.24}
$$

We then have that (6.21) and (6.24) yield

$$
\begin{aligned}
\int_{\Sigma_t^L \cap T_L} \kappa_{t,L} =& 2\pi + \frac{1}{2L^3} \int_{\Sigma_t^L \cap T_L} x^2 x^3 [x^3 g_{22,2} + x^2 g_{33,3}] \\
& - \frac{1}{2L^3} \int_{\Sigma_t^L \cap T_L} x^2 x^3 [x^2 g_{22,3} + x^3 g_{33,2}] \\
& + \frac{1}{2L^3} \int_{\Sigma_t^L \cap T_L} [(x^2)^2 - (x^3)^2](x^2 g_{23,3} - x^3 g_{32,2}) \\
& - \int_{\Sigma_t^L \cap T_L} \frac{1}{2L^3} (x^2 (x^3)^2 g_{22,2} + (x^2)^2 x^3 g_{33,3}) \\
& + \int_{\Sigma_t^L \cap T_L} \left( \left[ (x^2)^2 x^3 + \frac{1}{2} (x^3)^3 \right] \frac{g_{22,3}}{L^3} + \left[ (x^3)^2 x^2 + \frac{1}{2} (x^2)^3 \right] \frac{g_{33,2}}{L^3} \right) \\
& - \int_{\Sigma_t^L \cap T_L} \left( (x^2)^3 \frac{g_{23,3}}{L^3} + (x^3)^3 \frac{g_{32,2}}{L^3} \right) + O(L^{-1-q} + L^{-2q}) \\
=& 2\pi + \frac{1}{2L} \int_{\Sigma_t^L \cap T_L} (x^3 g_{22,3} - x^3 g_{32,2} + x^2 g_{33,2} - x^2 g_{23,3}) + O(L^{-1-q} + L^{-2q}).
\end{aligned} \tag{6.25}
$$

Finally, integrating over $[-L, L]$ gives the desired identity. $\square$

<!-- page 21 -->

### 6.2. Proof of Theorem 1.2.

Recall that from (6.4) we have

$$
\frac{1}{2}\int_{\Omega_L}\left(\frac{|\nabla^2 u|^2}{|\nabla u|}+R_g|\nabla u|\right)dV\leq 4\pi L-\int_{-L}^{L}\left(\int_{\Sigma_t^L\cap T_L}\kappa_{t,L}\right)dt+\int_{C_L}\partial_\upsilon|\nabla u|dA. \tag{6.26}
$$

On the other hand, it follows from Lemmas 6.1 and 6.2 that

$$
\begin{aligned}
\int_{C_L}\partial_\upsilon|\nabla u|dA-\int_{-L}^{L}\left(\int_{\Sigma_t^L\cap T_L}\kappa_{t,L}\right)dt =&\frac{1}{2}\int_{D_L^{\pm}}\pm\sum_j(g_{1j,j}-g_{jj,1})dA\\
&+\frac{1}{2}\int_{T_L}\left[\frac{x^2}{L}(g_{21,1}-g_{11,2})+\frac{x^3}{L}(g_{31,1}-g_{11,3})\right]dA\\
&+\frac{1}{2}\int_{T_L}\left[\frac{x^2}{L}(g_{23,3}-g_{33,2})+\frac{x^3}{L}(g_{32,2}-g_{22,3})\right]dA\\
&-4\pi L+o(1)\\
=&-4\pi L+\frac{1}{2}\int_{C_L}\sum_j(g_{ij,j}-g_{jj,i})\upsilon^i dA+o(1),
\end{aligned} \tag{6.27}
$$

Therefore

$$
\frac{1}{2}\int_{\Omega_L}\left(\frac{|\nabla^2 u|^2}{|\nabla u|}+R_g|\nabla u|\right)dV\leq\frac{1}{2}\int_{C_L}\sum_j(g_{ij,j}-g_{jj,i})\upsilon^i dA+o(1), \tag{6.28}
$$

and taking the limit as $L\to\infty$ gives the desired inequality (1.3).

Consider now the case of equality when $m=0$. From the arguments above, this implies that the harmonic coordinate function is linear $|\nabla^2 u|\equiv 0$ and that the Euler characteristic of the level sets is constant $\chi(\Sigma_t)=1$. In particular the boundary of the exterior region is empty $\partial N=\emptyset$, and thus $M\cong\mathbb{R}^3$. Since there are three linearly independent harmonic coordinate functions with $\nabla^2 u\equiv 0$, the manifold is flat, yielding the isometry $(M,g)\cong(\mathbb{R}^3,\delta)$.

**Acknowledgements.** The authors would like to thank Dan Lee for several helpful comments on an earlier version of this manuscript, in particular for pointing out the simplification in Remark 2.2.

## References

[1] R. Bartnik, *The mass of an asymptotically flat manifold*, Comm. Pure Appl. Math., **39** (1986), no. 5, 661-693.

[2] H. Bray, *The Penrose inequality in general relativity and volume comparison theorems involving scalar curvature*, Dissertation, Stanford University, 1997.

[3] H. Bray and D. Stern *Scalar curvature and harmonic one-forms on 3-manifolds with boundary*, in preparation.

[4] D. Brill, *On the positive definite mass of the Bondi-Weber-Wheeler time-symmetric gravitational waves*, Ann. Phys., **7** (1959), 466-483.

[5] J. Corvino, and D. Pollack, *Scalar curvature and the Einstein constraint equations*, Surveys in Geometric Analysis and Relativity, 145–188, Adv. Lect. Math. (ALM), **20**, Int. Press, Somerville, MA, 2011.

[6] D. Lee, *Geometric Relativity*, Graduate Studies in Mathematics, Volume **201**, 2019.

[7] G. Huisken, and T. Ilmanen, *The inverse mean curvature flow and the Riemannian Penrose inequality*, J. Differential Geom., **59** (2001), 353-437.

[8] Y. Li, *Ricci flow on asymptotically Euclidean manifolds*, Geom. Topol., **22** (2018), 1837-1891.

[9] C. Mantoulidis, and R. Schoen, *On the Bartnik mass of apparent horizons*, Class. Quant. Grav., **32** (2015), no. 20, 205002, 16 pp.

[10] C. Mantoulidis, *Geometric variational problems in mathematical physics*, Ph.D. thesis, Stanford University, (2017)

[11] P. Miao, *Positive mass theorem on manifolds admitting corners along a hypersurface*, Adv. Theor. Math. Phys., **6** (2002), no. 6, 1163-1182.

<!-- page 22 -->

[12] T. Parker, and C. Taubes, *On Witten’s proof of the positive energy theorem*, Comm. Math. Phys., **84** (1982), no. 2, 223–238.

[13] R. Schoen, and S.-T. Yau, *On the proof of the positive mass conjecture in general relativity*, Comm. Math. Phys., **65** (1979), no. 1, 45-76.

[14] R. Schoen, and S.-T. Yau, *The energy and the linear momentum in of space-times in general relativity*, Comm. Math. Phys., **79** (1981), no. 1, 47-51.

[15] R. Schoen, and S.-T. Yau, *Positive scalar curvature and minimal hypersurface singularities*, preprint, 2017. arXiv:1704.05490

[16] E. Witten, *A simple proof of the positive energy theorem*, Comm. Math. Phys. **80** (1981), no. 3, 381-402.

[17] J. Lohkamp, *Scalar curvature and hammocks*, Math. Ann., **313** (1999), no. 3, 385-407.

[18] J. Lohkamp, *The higher dimensional positive mass theorem I*, preprint, 2016. arXiv:math/0608795

[19] D. Stern, *Scalar curvature and harmonic maps to $S^1$*, preprint, 2019. arXiv:1908.09754

Department of Mathematics, Duke University, Durham, NC, 27708, USA
*E-mail address*: `bray@math.duke.edu`

Department of Mathematics, Stony Brook University, Stony Brook, NY, 11794-3660, USA
*E-mail address*: `demetre.kazaras@stonybrook.edu, khuri@math.sunysb.edu`

Department of Mathematics, University of Toronto, Toronto, ON, M5S 2E4, Canada
*E-mail address*: `dl.stern@utoronto.ca`

