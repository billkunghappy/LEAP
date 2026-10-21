# KdV is well-posed in $H^{-1}$

**Rowan Killip and Monica Vişan**

*Department of Mathematics, University of California, Los Angeles, CA 90095, USA*
killip@math.ucla.edu, visan@math.ucla.edu

*Source:* arXiv:1802.04851v2 [math.AP], 26 Apr 2019; published in *Annals of Mathematics* **190** (2019), no. 1, 249–305. Converted from the authors' arXiv LaTeX source to Markdown with LaTeX math. Equation, theorem and section numbers, and bibliography numbers, match the arXiv version.

---

**Abstract.**
We prove global well-posedness of the Korteweg–de Vries equation for initial data in the space $H^{-1}(\mathbb{R})$.  This is sharp in the class of $H^{s}(\mathbb{R})$ spaces.  Even local well-posedness was previously unknown for $s<-3/4$.  The proof is based on the introduction of a new method of general applicability for the study of low-regularity well-posedness for integrable PDE, informed by the existence of commuting flows.   In particular, as we will show, completely parallel arguments give a new proof of global well-posedness for KdV with periodic $H^{-1}$ data, shown previously by Kappeler and Topalov, as well as global well-posedness for the 5th order KdV equation in $L^2(\mathbb{R})$.

Additionally, we give a new proof of the a priori local smoothing bound of Buckmaster and Koch for KdV on the line.  Moreover, we upgrade this estimate to show that convergence of initial data in $H^{-1}(\mathbb{R})$ guarantees convergence of the resulting solutions in $L^2_\text{loc}(\mathbb{R}\times\mathbb{R})$.  Thus, solutions with $H^{-1}(\mathbb{R})$ initial data are distributional solutions.

## 1. Introduction

The Korteweg–de Vries equation

$$
\frac{d\ }{dt} q = - q''' + 6qq' \tag{KdV}
$$

was derived in [44] to explain the observation of solitary waves in a shallow channel of water.  Specifically, they sought to definitively settle (to use their words) the debate over whether such solitary waves are consistent with the mathematical theory of a frictionless fluid, or whether wave fronts must necessarily steepen.  The equation itself, however, appears earlier; see [7, p. 77].  The term *solitary wave* has now been supplanted by *soliton*, a name coined in [69] and inspired by the particle-like interactions they observed between solitary waves in their numerical simulations of (KdV).

In a series of papers, researchers at Princeton's Plasma Physics Laboratory demonstrated that equation (KdV) exhibits a wealth of novel features, including the existence of infinitely many conservation laws [54] and the connection to the scattering problem for one-dimensional Schrödinger equations [19].  Nowadays, we say that (KdV) is a completely integrable system (cf. [70]).

Although we shall focus on mathematical matters here, (KdV) continues to be an important effective model for a diverse range of physical phenomena; see, for example, the review [15] occasioned by the centenary of [44].

One of the most basic mathematical questions one may ask of (KdV) is whether it is well-posed.  This is the question of the existence and uniqueness of solutions, together with the requirement that the solution depends continuously on time and the initial data.  As we shall discuss, this topic has attracted several generations of researchers who have successively enlarged the class of initial data for which well-posedness can be shown.  Our principal contribution is the following:

**Theorem 1.1 (Global well-posedness).**
The equation (KdV) is globally well-posed for initial data in $H^{-1}(\mathbb{R})$ or $H^{-1}(\mathbb{R}/\mathbb{Z})$ in the following sense:  In each geometry, the solution map extends uniquely from Schwartz space to a jointly continuous map $\Phi:\mathbb{R}\times H^{-1}\to H^{-1}$.  Moreover, for each initial data $q\in H^{-1}$, the orbit $\{\Phi(t,q) : t\in\mathbb{R}\}$ is uniformly bounded and equicontinuous in $H^{-1}$.

On the circle $\mathbb{R}/\mathbb{Z}$, Schwartz space is coincident with $C^\infty(\mathbb{R}/\mathbb{Z})$; on the line, it is comprised of those $C^\infty(\mathbb{R})$ functions that decay (along with their derivatives) faster than any polynomial as $|x|\to\infty$.  For the definition of $H^{-1}(\mathbb{R})$ and $H^{-1}(\mathbb{R}/\mathbb{Z})$, see subsection 1.2; informally, they are comprised of those tempered distributions that are derivatives of $L^2$ functions.  For the precise definition of equicontinuity in the $H^s$ setting, see (4.1).

The fact that Schwartz-space initial data leads to unique global solutions to (KdV) that remain in Schwartz class has been known for some time; see, for example, [5, 34, 63, 64, 65].  Indeed, in this class, the solution map is known not only to be continuous, but infinitely differentiable in both variables.  We shall rely on this result in what follows.

In the case of (KdV) posed on the torus (or equivalently for periodic initial data), Theorem 1.1 reproduces the principal results of [30].  Note that because the circle is compact, uniform boundedness and equicontinuity of the orbit is equivalent to it being pre-compact.  In the line case, one does not expect orbits to be pre-compact; both solitons and radiation preclude tightness from holding globally in time.

The papers [55, 56] show that well-posedness cannot persist (in either geometry) in $H^{s}$ for any $s<-1$.  In this sense, Theorem 1.1 is sharp.  On the other hand, one may consider well-posedness at higher regularity $s>-1$.  Existence and uniqueness are immediate from the case $s=-1$; the key is to demonstrate that continuous dependence remains valid in this stronger topology.  In this paper, we will settle the cases left open by prior work, namely, the wellposedness of (KdV) in $H^{s}(\mathbb{R})$ with $-1\leq s< -\frac34$.  (On the circle, all $s\geq -1$ were treated already in [30].) In fact, the proof of Corollary 5.3 provides a simple uniform treatment of all $-1\leq s<0$ and adapts trivially to the case of the circle also.

The notion of solution used here (unique limits of Schwartz solutions) coincides with that in [30] and is informed by several important considerations.  Firstly, as the notion of a solution in the case of Schwartz initial data is firmly settled, any notion of a solution to (KdV) leading to well-posedness in $H^{-1}$ must produce solutions identical to those given by Theorem 1.1.

Secondly, for functions that are merely $C_t H^{-1}_x$ it is not possible to make sense of the nonlinearity in (KdV) as a space-time distribution in either geometry.  While the local smoothing effect (see subsection 1.1) provides a potential resolution of this problem in the line setting, there is no natural alternative notion of a weak solution in the circle geometry.  Any methodology that purports to apply in wide generality must adopt a notion of solution that applies in wide generality.

A wider notion of solution was considered in [9], namely, limits of smooth solutions in the presence of smooth asymptotically vanishing forcing.  That paper shows (see [9, §2.7]) that with this wider notion of solution, uniqueness cannot be guaranteed for $C_t H^{s}(\mathbb{R}/\mathbb{Z})$ solutions to (KdV) already for $s<0$.

From Theorem 1.1, we see that the map $\Phi$ is continuous, as was also shown in [30] for the circle case.  It is natural to ask if this continuity may be expressed more quantitatively.  In some sense, the answer is no: it is shown in [10] that the data to solution map cannot be uniformly continuous on bounded sets when $s<-\frac34$ in the line case or when $s<-\frac12$ in the circle case.  Nevertheless, the arguments presented here are sufficiently transparent that one may readily obtain information on the modulus of continuity of $q\mapsto\Phi(t,q)$.  Specifically, we find that the key determiners of the modulus of continuity at an initial datum $q\in H^{-1}(\mathbb{R})$ are the time $t$ in question and the rate at which

$$
\int \frac{|\hat q(\xi)|^2\,d\xi}{\xi^2+4\kappa^2} \to 0\quad\text{as}\quad  \kappa\to\infty.
$$

Evidently, this integral does not converge to zero uniformly on any open set of initial data.

Let us now turn our attention to a discussion of prior work proving well-posedness for (KdV). Discussion of weak solutions (without uniqueness) is postponed until subsection 1.1.  Our discussion will not be exhaustive; the body of literature on (KdV) is simply immense.  Nor will we insist on a strict chronology.

Early work on the local and global well-posedness of (KdV) treated it as a quasi-linear hyperbolic problem.  The appearance of the derivative in the nonlinearity prohibits simple contraction mapping arguments from closing.  The principal methods employed were (i) compactness and uniqueness arguments (e.g. [61, 65]) combined with parabolic regularization, (ii) convergence of Picard iterates with (e.g. [66]) or without (e.g. [33]) parabolic regularization, and (iii) approximation by the Benjamin–Bona–Mahoney (BBM) equation [4, 5].

The BBM equation was introduced in [3]; this equation has a much more regular nonlinearity and global well-posedness was shown there by simple contraction mapping arguments.  The BBM equation has the same Hamiltonian as (KdV), namely,

$$
H_\text{KdV} (q) := \int \tfrac12 q'(x)^2 + q(x)^3\,dx; \tag{1.1}
$$

however the underlying symplectic structure is different.  Of all the prior approaches we know of, the one we follow here is closest in spirit to that of Bona–Smith [5], since both we and they employ the idea of approximating the full flow by another Hamiltonian evolution that is more readily controlled.

Incidentally, the problem of local  well-posedness of (KdV) in Schwartz space, which we shall take for granted here, is rather easier than the works just cited, because one may safely lose regularity in proving continuous dependence of the solution on the initial data.

While multiple authors sought to obtain well-posedness in $H^{s}$ for $s$ as small as possible, these early attempts did not succeed in proving local well-posedness beyond the regime $s>3/2$.  Most significantly, this does not reach the level $s=1$ at which one may upgrade local to  global well-posedness by exploiting conservation of the Hamiltonian.  Nevertheless, global well-posedness was obtained at this time for $s\geq 2$ by using the conserved quantities at such higher regularity discovered in [54].

To progress further in this vein, the key has been to exploit the dispersive property of (KdV).  Global well-posedness for finite energy initial data on the line was first proved in [36], by utilizing local smoothing and maximal function estimates.  The paper actually proves local well-posedness in $H^s(\mathbb{R})$ for $s>3/4$; the global $H^1(\mathbb{R})$ result follows trivially from this and conservation of the Hamiltonian.

The next conspicuous benchmark for the well-posedness theory was the treatment of initial data with finite momentum

$$
P(q) := \int \tfrac12 q(x)^2 \,dx, \tag{1.2}
$$

that is, data in $L^2$.  *Momentum* is the appropriate term here; this quantity is the generator of translations with respect to the standard symplectic structure.  Moreover, this quantity is conserved under the KdV flow.  The *mass* of a wave is given by $\int q(x)\,dx$, which is also conserved, and represents the total deficit (or surplus) of water relative to $q\equiv 0$.

Well-posedness of (KdV) in $L^2$ was proved both on the line and on the circle by Bourgain in [6].  At the heart of this work is the use of $X^{s,b}$ spaces, which efficiently capture the dispersive nature of the equation and effectively control the deviation of the KdV dynamics from solutions to the linear equation $\partial_t q = - q'''$.  After developing suitable estimates in these spaces, the proof proceeds by contraction mapping arguments; thus the solutions constructed depend analytically on the initial data.

Further development and refinement of the methods employed in [6] ultimately led to a proof of local well-posedness for (KdV) in $H^{s}(\mathbb{R})$ for $s\geq -3/4$ and in $H^s(\mathbb{R}/\mathbb{Z})$ for $s\geq -1/2$.  Excepting the endpoints, this was proved by Kenig–Ponce–Vega in [37].  For a discussion of the endpoints, see [10] and [12, 13, 14].  These ranges of $s$ are sharp if one requires the data to solution map to be uniformly continuous on bounded sets; see [10].

These local well-posedness results were made global in time in [12], excepting the endpoint case $H^{-3/4}(\mathbb{R})$, which was proved later in [22, 38].    At that time, no exact conservation laws were known that were adapted to negative regularity.  To obtain such global results, these authors constructed almost conserved quantities, whose growth in time they were able to control.

While it is true that the conspicuous manifestations of complete integrability of KdV played no particular role in the series of works we have just described, it is difficult to completely decouple these successes from the exact structure of the KdV equation.  In the first place, many of these arguments rely on the absence of unfavorable resonances.  This appears in the multilinear $X^{s,b}$ estimates and (rather more explicitly) in the construction of almost conserved quantities in [12].  This is akin to the construction of Birkoff normal form, which may fail due to resonances, but which does succeed in completely integrable systems (cf. [68, 71]).  As we will discuss below, we now know that KdV admits exact conservation laws adapted to every regularity $s\geq -1$; this offers a rather transparent explanation for the otherwise startling success of [12] in constructing almost conserved quantities.

The Miura map [53], implements a first iteration toward the construction of Birkoff normal form by converting the KdV equation to the mKdV equation, which has a nonlinearity that is one degree higher.  This transformation was one of the first indications that there was something peculiar about (KdV).  Moreover, a one-parameter generalization of this transformation, due to Gardner, led to the first proof of the existence of infinitely many polynomial conservation laws; see [54].  The Miura map has been very popular in the study of KdV at low regularity.  Most particularly, it allows one to work at positive regularity, where many nonlinear transformations (e.g., pointwise products) are much better behaved.

The breakdown of traditional PDE techniques ultimately stems from a high-high-low frequency interaction that makes it impossible to approximate the KdV flow by a linear evolution even locally in time.  This particular frequency interaction appears in many fluid models, due to the ubiquity of the advection nonlinearity $(u\cdot\nabla) u$, and is exploited crucially in the construction of solutions exhibiting energy growth.

It is worth noting that among the family of monomial gKdV equations, namely, those of the form $\partial_t q = -\partial_x^3 q \pm \partial_x (q^k)$, only for the completely integrable models (i.e., $k=2,3$) does the local well-posedness threshold deviate from scaling.  Indeed, the completely integrable models are *less* well-posed relative to scaling than those with $k\geq 4$.  Ultimately, we see that complete integrability does not completely ameliorate the severity of this nonlinearity when acting on solutions of low regularity.

In this vein, we contend that the complete integrability of a system is not divorced from the class of initial data on which it is studied.  The PDE $\partial_t q = \partial_x q$ posed on the line might immediately be classed as completely integrable; it even belongs to the KdV hierarchy.  However, when the initial data is white-noise, we see that the dynamics is mixing!  On the basis of the results of this paper, we may say that the term *completely integrable* continues to apply to (KdV) in the class $H^s(\mathbb{R})$ when $s\geq -1$.

We have not yet explained in what sense (KdV) can be regarded as completely integrable.  The most common definition applied in finite-dimensional mechanics is that the system has sufficiently many Poisson commuting, functionally independent, conserved quantities.  Here, sufficiently many means half the dimension of the ambient symplectic manifold.  As noted earlier, the fact that (KdV) admits infinitely many independent conserved quantities was first proved in [54].  We have already seen three: the mass, momentum, and energy.  In the original paper, the conservation laws were presented in a microscopic form, that is, as

$$
\partial_t \rho(t,x) + \partial_x j(t,x) = 0, \tag{1.3}
$$

where the densities $\rho$ and the currents $j$ are given by particular polynomials in $q$ and its derivatives.  The (macroscopic) conserved quantities are then obtained integrating $\rho$ over the whole line or circle, as appropriate.

The polynomial nature of these conserved quantities is such that, except in the case of $H^\infty$ data (i.e. all derivatives square integrable), all but finitely many of them are infinite.  Moreover, it is also not immediately clear whether these constitute a sufficient number of conserved quantities to call the system completely integrable, even in Schwartz space.  These concerns turn out to be unwarranted.  To explain, we begin with an innovation of Lax [45], namely, the introduction of the Lax pair:  Defining

$$
\begin{aligned}
L(t) &:= -\partial_x^2 + q(t,x) \quad\text{and}\quad  P(t) := - 4 \partial_x^3 + 3\bigl(\partial_x q(t,x) + q(t,x) \partial_x \bigr)
\end{aligned}
$$

it is easy to verify that

$$
\text{$q(t)$ solves (KdV)} \iff \frac{d\ }{dt} L(t) = [P(t),\, L(t)].
$$

As $P(t)$ is always anti-self-adjoint, this shows that at each time slice, the Schrödinger operator with potential $q(t,x)$ is unitarily equivalent to that built from the initial data $q(0,x)$.  Speaking loosely, we may say that all spectral properties of $L(t)$ are conserved under the KdV flow.

One of the beauties of the Lax pair is that it works equally well in both geometries.  However, once we try to speak more precisely about which spectral properties are conserved, this unity quickly dissolves.  We will first discuss the periodic case where related ideas have been most successful in tackling the well-posedness problem.

The Schrödinger operator on the circle with (periodic) potential $q$ has purely discrete spectrum.  This remains true for potentials that are merely $H^{-1}$ because such perturbations of $-\partial_x^2$ are relatively compact. The Lax pair shows that these (periodic) eigenvalues are then conserved under the flow and so we obtain an infinite sequence of conserved quantities that extend to the case of very low regularity.  There is a direct connection between these eigenvalues and the polynomial conservation laws mentioned earlier; see, for example, [51, §3].

As it turns out, these eigenvalues are not the most convenient objects for further development.  Rather, one should consider the spectrum of the Schrödinger operator associated to the $1$-periodic potential, acting on the whole line.  This set is wholly determined by the periodic eigenvalues; see [20].  Nevertheless, this new perspective suggests an alternate set of conserved quantities, namely, the lengths of the gaps in the spectrum.  The virtue of these new quantities can be seen already in the fact that these numbers effectively capture the $H^s$ norms of the potential, at least if $s\geq0$; see [49].  While such a priori bounds are useful for well-posedness questions (particularly, to extend solutions globally in time), they do not suffice.

For the purposes of well-posedness, there is no better expression of complete integrability than the existence of action-angle coordinates.  Such coordinates are now known to exist for (KdV) with data in $H^{-1}(\mathbb{R}/\mathbb{Z})$ and this result was decisive in the proof of global well-posedness in [30].  A key step down this path was the discovery that one should adopt the Dirichlet spectrum (together with the gap lengths) to form a complete set of coordinates and secondly, that these points (which lie in the gaps) should properly be interpreted as lying on the Riemann surface obtained by gluing together two copies of the complex plane cut along the spectrum.  These considerations lead to the definition of angle variables (cf. [17, 50]) and thence to associated actions [18].  A very pedagogical account of these constructions can be found in [29]; moreover, this monograph culminates in a proof that these variables define *global* action-angle coordinates on each symplectic leaf in the phase-space $L^2(\mathbb{R}/\mathbb{Z})$.

The proof in [30] of global well-posedness in $H^{-1}(\mathbb{R}/\mathbb{Z})$ required two more steps.  The first, carried out in [26], was the extension of these coordinates (as a global analytic symplectic diffeomorphism) to $H^{-1}(\mathbb{R}/\mathbb{Z})$.  The second was to gain adequate control of the frequencies (i.e., the time derivatives of the angles).  Usually, these frequencies are computed as the derivatives of the Hamiltonian with respect to the corresponding actions.  However, the Hamiltonian $H_\text{KdV}$ does not make sense as a function on $H^{-1}(\mathbb{R}/\mathbb{Z})$!

Let us now turn our attention to the case of (KdV) posed on the line.  We begin by describing a system of coordinates discovered already in [19] that linearize the flow (at least for a suitable class of data).  While not action-angle variables themselves, such variables can be readily expressed in terms of them; see [70].

To the best of our knowledge, the broadest class in which the construction that follows has been successfully completed is $\mathcal L^1_1:= \{q\in L^1(\mathbb{R}): x q(x) \in L^1(\mathbb{R})\}$; see [48, 52].  As we will discuss later, there are compelling reasons to doubt that this construction can be taken much further without substantial new ideas.

Given $q\in \mathcal L^1_1$ and $k\in\mathbb{C}$ with $\operatorname{Im} k\geq 0$, there are unique solutions $f_\pm(x;k)$ to

$$
-f''(x) + q(x)f(x) = k^2 f(x) \quad\text{satisfying}\quad  f_\pm(x) = e^{\pm ik x} +o(1) \quad\text{as $x\to\pm\infty$.}
$$

These are known as Jost solutions and depend analytically on $k$.  For $k\in\mathbb{R}\setminus\{0\}$, $f_+(x;\pm k)$ are linearly independent solutions to our ODE.  Thus we may define connection coefficients, say $a(k)$ and $b(k)$, so that

$$
f_-(x;k) = a(k) f_+(x;-k) + b(k) f_+(x;k). \tag{1.4}
$$

Note that $a(k)$ extends analytically to the upper half-plane, since it can be expressed through the Wronskian of $f_+$ and $f_-$.  There is no such extension of $b(k)$.  The relation to the Wronskian also shows that $a(k)$ has zeros in the upper half-plane precisely at those points $i\kappa_n$ for which $-\kappa_n^2$ is an eigenvalue of the Schrödinger operator.

The objects introduced so far do not uniquely characterize the potential $q$.  To do so, one must also consider *norming constants*, $c_n>0$, associated to each eigenvalue $-\kappa_n^2$.  These describe the large-$x$ asymptotics of the $L^2$-normalized eigenfunction $\psi_n(x)$; specifically, $e^{\kappa_n x} |\psi(x)| \to c_n$ as $x\to+\infty$.

As shown already in [19], the objects just described evolve very simply under (KdV): $a(k)$, $|b(k)|$, and the eigenvalues remain constant, while $\arg( b(k))$ and $\log(c_n)$ evolve linearly.  As the forward and inverse scattering problems have been shown to be well-posed in the class $\mathcal L^1_1$, this yields a proof of well-posedness of (KdV) in this class.  This is the natural analogue of the argument that has proven so successful in the circle geometry.

Unfortunately, well-posedness of the forward/inverse scattering problems (as they are currently understood) begins to break down under very mild relaxations of the condition $q\in \mathcal L^1_1$.  For example, the scattering data fails to determine $q$ already for potentials that are bounded and $O(x^{-2})$ at infinity, due to the presence of zero-energy eigenvalues; see [16].  Relaxing our decay restrictions on $q$ to merely $O(|x|^{-1})$ at infinity, gives rise to further problems: positive energy (embedded) eigenvalues may occur (cf. [59, § XIII.13]); moreover, Jost solutions may fail to exist (without WKB correction) at every positive energy.

In [42], it is shown that embedded singular continuous spectrum can occur as soon as one passes beyond $O(|x|^{-1})$ decay, even in the slightest.  Moreover, potentials $q\in L^2(\mathbb{R})$ can yield essentially arbitrary embedded singular spectrum; see [40].  The appearance of such exotic spectra leads us to believe that seeking a solution to the well-posedness problem for (KdV) in $H^{-1}(\mathbb{R})$ through the inverse scattering methodology has little chance of success at this time.  In particular, we are not aware of any proposal for action-angle variables in such a scenario.  This raises the following question: What other manifestation of complete integrability may hold the key to further progress on the well-posedness problem?

Our answer, in this paper, is the existence of a wealth of commuting flows.  As we will see, the method we propose does not completely supplant PDE techniques, but rather, like the Miura map, provides a new avenue for their application to the KdV problem.  As the existence of an abundance of commuting flows is a necessary (but not sufficient) condition for a system to be considered completely integrable, the method has a good chance of being applicable to any PDE that is considered completely integrable.

The commuting flows associated to the traditional sequence of conserved quantities (based on polynomials in $q$ and its derivatives) are not what we have in mind.  Their well-posedness is at least as difficult as for (KdV) itself.  Moreover, there is no sense in which they approximate the KdV flow; they are better considered as flowing in orthogonal directions.  Rather, we begin our discussion with

$$
\alpha(\kappa;q) := - \log[a(i\kappa;q)] + \tfrac{1}{2\kappa}\int q(x)\,dx, \tag{1.5}
$$

where $a(k;q)$ denotes the coefficient $a(k)$ from (1.4) associated to the potential $q$.  As noted previously, both $a(k;q)$ and $\int q$ are conserved under the KdV flow; thus one should expect $\alpha(\kappa)$ to also be conserved whenever it is defined.

Unaware that the same idea had already been implemented by Rybkin in [60], the authors together with X. Zhang showed in [41] that $\alpha(\kappa;q)$ is a real-analytic function of $q\in H^{-1}(\mathbb{R})$, provided $\kappa\geq 1 + 45\|q\|_{H^{-1}}^2$.  We also gave a direct proof that it is conserved for Schwartz initial data.   In these arguments, both we and Rybkin use the fact that $a(k;q)$ can also be written as a Fredholm determinant; see (2.21) below.  That such a determinant representation of this scattering coefficient is possible was first noticed in the setting of three-dimensional central potentials in [25].  (See [62, Proposition 5.4] or [39, Lemma 2.8] for simple proofs in one dimension.)

The renormalization of $\log|a(k)|$ appearing in (1.5) is essential for considering $q\in H^{-1}(\mathbb{R})$; without it, one would need to restrict to potentials that are at least conditionally integrable.  Incidentally, this renormalizing term can also be predicted as the leading behaviour of the phase shift via WKB theory.

The goal of the paper [41] was the construction of a variety of low-regularity conservation laws for KdV both on the line and on the circle. (NLS and complex mKdV were also treated there by the same method.) In the case of $H^{-1}(\mathbb{R})$ bounds for KdV, our argument is essentially that of Rybkin [60], who obtained the same result.  Another proof (also independent of Rybkin) can be found in [8].  In the line setting, general $H^s(\mathbb{R})$ bounds for KdV, NLS, and mKdV were obtained, independently, by Koch and Tataru [43].  For an earlier partial result, see also [46].  In the circle setting, bounds of this type were obtained considerably earlier; see [26].

In this paper, we will not rely on the results of [8, 26, 41, 43, 60]. In fact, the proof of Theorem 1.2 below relies on our development of an alternate argument, which also yields the global $H^{-1}$ bound.  Specifically, we will develop a microscopic version (cf. (1.3)) of the macroscopic conservation law from [41, 60].

A priori bounds of the type just described do not in themselves yield well-posedness.  Indeed, conservation of momentum was known already to Korteweg and de Vries, yet the corresponding well-posedness result did not appear until [6].  The key obstacle is always to control differences of solutions.  While individual solutions admit infinitely many conservation laws, the difference of two solutions need not have any.

As discussed previously, the map $q\mapsto \alpha(\kappa;q)$ is analytic; therefore, its derivative (with respect to $q$) is represented (in the sense (1.7)) by an analytic $H^1$-valued function of $q\in H^{-1}$.  Thus, when we consider the Hamiltonian evolution induced by this functional, namely,

$$
\frac{d\ }{dt} q(t) = \partial_x \frac{\delta \alpha}{\delta q},
$$

we see that the right-hand side is a Lipschitz function on $H^{-1}$ and so well-posedness of this equation follows by the standard ODE argument.  Our ambition (and this appears to be a new idea) is to approximate (KdV) by this flow.  It turns out that this is possible after one further renormalization, as we will now explain.

It was observed already in [70] that $\log[a(i\kappa)]$ acts as a generating function for the polynomial conserved quantities; in particular, this yields the asymptotic expansion

$$
\alpha(\kappa;q) = \tfrac{1}{4\kappa^3} P(q) - \tfrac{1}{16\kappa^5} H_\text{KdV}(q) + O(\kappa^{-7}),
$$

using the notations (1.1) and (1.2).  Inspired by this, one may then postulate that the Hamiltonian

$$
H_\kappa := - 16 \kappa^5 \alpha(\kappa;q) + 4 \kappa^2 P(q)
$$

provides a good approximation to the KdV Hamiltonian for $\kappa$ large.  More ambitiously, one may hope that the KdV flow is well approximated by the flow under $H_\kappa$.  Verifying this and so deducing Theorem 1.1 occupies the central portion of the paper, namely, Sections 3–5.

Several observations are in order.  Firstly, while $\alpha(\kappa,q)$ is a analytic function on $H^{-1}$, the approximate Hamiltonian $H_\kappa$ is not, because momentum is not.  Nevertheless, well-posedness of the resulting flow is still elementary; see Proposition 3.2.

The problem of estimating the discrepancy between the $H_\kappa$ flow and the full KdV flow is much simplified by the fact that the two flows commute.  Indeed, it reduces the question of such an approximation to showing that the flow induced by the difference $H_\text{KdV} - H_\kappa$ is close to the identity for $\kappa$ large and bounded time intervals.

Naturally, one needs to show that this flow is close to the identity in the $H^{-1}$ metric; however, this follows from proximity in much weaker norms, say $H^{-3}$.  The central point here is equicontinuity, or what is equivalent, tightness on the Fourier side; see Lemma 4.2.  The equicontinuity of orbits under the flows of interest to us follows from the fact that all conserve $\alpha(\kappa;q)$; see Lemma 4.3.  Indeed, from (2.20), we see that this functional effectively captures how much of the $H^{-1}$ norm of $q$ lives at frequencies $\xi$ with $|\xi|\gtrsim \kappa$.

One further innovation informs our implementation of the program laid out above, namely, the adoption of the `good unknown' $x\mapsto\kappa - \tfrac{1}{2g(x)}$.   Here $g(x):=g(x;\kappa,q)$ denotes the diagonal of the Green's function associated to the potential $q$ at energy $-\kappa^2$.  For a discussion of this object, see Section 2.  In particular, it is shown there that the map from $q(x)$ to $\kappa - \tfrac{1}{2g(x)}$ is a real-analytic diffeomorphism, thus, justifying the notion that $g(x)$ may effectively replace the traditional unknown $q(x)$.

Both the diagonal Green's function and its reciprocal appear naturally in several places in our argument, including in the conserved density $\rho$ introduced in (2.18) and in the dynamics associated to the Hamiltonian $H_\kappa$; see (3.11).   Although our embracement of $g(x)$ is certainly responsible for the simplicity of many of our estimates and concomitantly, for the brevity of the paper, we caution the reader that it is not in itself the key to overcoming the fundamental obstacle confounding previous investigators, namely, the problem of estimating differences between two solutions.

We are not aware of any obstruction to extending the method employed here to a wide range of integrable systems, including those in the AKNS family.  As evidence in favour of this assertion, we demonstrate in Section 6 how our method applies in the setting of KdV on the circle.  In Appendix A we apply it to the next equation in the KdV hierarchy, following up on an enquiry of a referee. Regarding models in the AKNS family, we note that the functional $\alpha(\kappa,q)$ discussed in [41] is easily seen to have several of the favorable properties needed for our arguments, such as providing global norm control, yielding equicontinuity, and inducing a well-posed Hamiltonian flow.

We do not consider what our results may imply for (real) mKdV via the Miura map.  Rather, it is our hope that our method may soon be adapted
to give an *intrinsic* treatment of the more general *complex* mKdV, which fits within the AKNS family of integrable systems.

Finally, while the ideas presented here are rooted in the complete integrability of KdV, we believe they may prove fruitful beyond this realm.  Specifically, we envision the $H_\kappa$ flow being used as a leading approximation for KdV-like equations in much the same way as the Airy equation, $\partial_t q = -q'''$, has been used as an approximation of KdV itself.

### 1.1. Local smoothing

The local smoothing effect is observed for a wide range of dispersive equations in Euclidean space, both linear and nonlinear.  The underlying physical principle is that when high-frequency components of a wave travel very quickly, they must spend little time in any fixed finite region of space.  Thus, one should expect a gain in regularity locally in space on average in time.  This phenomenon seems to have been first appreciated by Kato, both for linear [31, 32] and nonlinear [34] problems.   In [34], it is shown that for Schwartz solutions to (KdV) one has

$$
\int_{-1}^1 \int_{-1}^1 |q'(t,x)|^2 \,dx\,dt \lesssim \| q(0) \|_{L^2}^2 +  \| q(0) \|_{L^2}^6.
$$

This is then used to prove the existence of global weak solutions to (KdV) for initial data in $L^2(\mathbb{R})$.  Prior to this, existence of global weak solutions (in either geometry) was known only for data in $H^1$; see [65].

In [8], Buckmaster and Koch proved the existence of an analogous a priori local-smoothing estimate one degree lower in regularity (on both sides).  This is achieved by using a Miura-type map and adapting Kato's local smoothing estimate for mKdV to the presence of a kink.  This technology is then used to prove the existence of global weak/distributional solutions to (KdV) with initial data in $H^{-1}(\mathbb{R})$.  (The nonlinearity may now be interpreted distributionally, because local smoothing guarantees that $q(t,x)$ is locally square integrable in space-time.)  As is usual with the construction of weak solutions, the arguments do not yield uniqueness and continuity in time is only shown with respect to the weak topology.  (Continuous dependence on the initial data is hopeless without first knowing uniqueness.)  For a restricted class of $H^{-1}$ initial data (namely, that in the range of the traditional Miura map), the existence of weak solutions was shown earlier in [28]; see also [67].

In Section 7 we will give a new derivation of the a priori local smoothing bound of [8].  Our argument is based on the discovery of a new microscopic conservation law (3.7) adapted to regularity $H^{-1}(\mathbb{R})$, which is then integrated against a suitably chosen weight function.  It is not difficult to extend the a priori bound to the full class of solutions constructed in Theorem 1.1.  However, we are able to take the argument one step further and show the following (cf. Proposition 7.2):

**Theorem 1.2.**  Let $q$ and $\{q_n:n\in\mathbb{N}\}$ be solutions to (KdV) on the line in the sense of Theorem 1.1.  If the initial data obey $q_n(0)\to q(0)$ in $H^{-1}(\mathbb{R})$, then

$$
\iint_K \bigl| q(t,x) - q_n(t,x)\bigr|^2\,dx\,dt \to 0\quad\text{as}\quad  n\to\infty \tag{1.6}
$$

for every compact set $K\subset \mathbb{R}\times\mathbb{R}$.

It follows immediately from this result that the solutions we construct are indeed distributional solutions in the line case.

### Acknowledgements.

 R. K. was supported, in part, by NSF grant DMS-1600942 and M. V. by grant DMS-1500707.  We would also like to thank the referee, whose comments and questions led to the inclusion of Appendix A.

### 1.2. Notation and Preliminaries

Many of the functions considered in this paper have numerous arguments.  For example, the diagonal Green's function ultimately depends on the location in space $x$, an energy parameter $\kappa$, and the wave profile $q$, which itself depends on time.  We find it advantageous to readability to suppress some of these dependencies from time to time.

We use prime solely to indicate derivatives in $x$; thus $f' =\partial_x f$.

Our conventions for the Fourier transform are as follows:

$$
\hat f(\xi) = \tfrac{1}{\sqrt{2\pi}} \int_\mathbb{R} e^{-i\xi x} f(x)\,dx  \quad\text{so}\quad  f(x) = \tfrac{1}{\sqrt{2\pi}} \int_\mathbb{R} e^{i\xi x} \hat f(\xi)\,d\xi
$$

for functions on the line and

$$
\hat f(\xi) = \int_0^1 e^{- i\xi x} f(x)\,dx \quad\text{so}\quad  f(x) = \sum_{\xi\in 2\pi\mathbb{Z}} \hat f(\xi) e^{i\xi x}
$$

for functions on the circle $\mathbb{R}/\mathbb{Z}$.  Concomitant with this, we define

$$
\| f\|_{H^{s}(\mathbb{R})}^2 = \int_\mathbb{R} |\hat f(\xi)|^2 (4+|\xi|^2)^s \,d\xi
\quad\text{and}\quad
\| f\|_{H^{s}(\mathbb{R}/\mathbb{Z})}^2 = \sum_{\xi\in 2\pi\mathbb{Z}} (4+\xi^2)^s |\hat f(\xi)|^2 .
$$

The use of the number $4$ here rather than the more traditional $1$ has no meaningful effect on these Hilbert spaces (the norms are equivalent); however, this definition simplifies our exposition by making certain key relations exact identities.  More generally, we define

$$
\| f\|_{H^{s}_\kappa(\mathbb{R})}^2 = \int_\mathbb{R} |\hat f(\xi)|^2 (4\kappa^2+|\xi|^2)^s \,d\xi
\quad\text{and}\quad
\| f\|_{H^{s}_\kappa(\mathbb{R}/\mathbb{Z})}^2 = \sum_{\xi\in 2\pi\mathbb{Z}} (4\kappa^2+\xi^2)^s |\hat f(\xi)|^2 .
$$

Note that $H^{1}_\kappa$ is an algebra in either geometry.  Indeed, one readily sees that

$$
\| f g \|_{H^{1}_\kappa} \lesssim \| f \|_{H^{1}} \| g \|_{H^{1}_\kappa} \leq \| f \|_{H^{1}_\kappa} \| g \|_{H^{1}_\kappa}  \quad\text{uniformly for $\kappa\geq 1$.}
$$

By duality, this implies that

$$
\| f h \|_{H^{-1}_\kappa} \lesssim \| f \|_{H^{\vphantom{+}1}_{\vphantom{\kappa}}} \| h \|_{H^{-1}_\kappa}  \quad\text{uniformly for $\kappa\geq 1$.}
$$

Throughout the paper, we will employ the $L^2$ pairing.  This informs our identification of $H^{-1}$ and $H^1$ as dual spaces and our notation for functional derivatives:

$$
\frac{d\ }{ds}\biggr|_{s=0} F(q+sf) = dF\bigl|_q (f) = \int \frac{\delta F}{\delta q}(x) f(x)\,dx . \tag{1.7}
$$

We write $\mathfrak{I}_p$ for the Schatten class of compact operators whose singular values are $\ell^p$ summable.  In truth, we shall use the Hilbert–Schmidt class $\mathfrak{I}_2$ almost exclusively. When we do use $\mathfrak{I}_1$, it will only be as a notation for products of Hilbert–Schmidt operators; see (6.5).  Let us quickly recall several facts about the class $\mathfrak{I}_2$ that we will use repeatedly:  An operator $A$ on $L^2(\mathbb{R})$ is Hilbert–Schmidt  if and only if it admits an integral kernel $a(x,y)\in L^2(\mathbb{R}\times\mathbb{R})$; moreover,

$$
\| A \|_{L^2\to L^2} \leq \| A \|_{\mathfrak{I}_2} = \iint |a(x,y)|^2\,dx\,dy.
$$

The product of two Hilbert–Schmidt operators is trace class; moreover,

$$
\operatorname{tr}(AB) := \iint a(x,y)b(y,x)\,dy\,dx = \operatorname{tr}(BA) \quad\text{and}\quad    |\operatorname{tr}(AB)| \leq \| A \|_{\mathfrak{I}_2} \| B \|_{\mathfrak{I}_2}.
$$

Lastly, Hilbert–Schmidt operators form a two-sided ideal in the algebra of bounded operators; indeed,

$$
\| B A C \| \leq \| B \|_{L^2\to L^2} \| A \|_{\mathfrak{I}_2}\| C \|_{L^2\to L^2}.
$$

All of this (and much more) is explained very clearly in [62].

For the arguments presented here, the problem (KdV) posed on circle is more favorably interpreted as a problem on the whole line with periodic initial data.  Correspondingly, even in this case, we will be dealing primarily with operators on the whole line, albeit with periodic coefficients.  When we do need to discuss operators acting on the circle $\mathbb{R}/\mathbb{Z}$ in connection with prior work, these will be distinguished by the use of calligraphic font.

## 2. Diagonal Green's function

The goal of this section is to discuss the Green's function $G(x,y)$ associated to the whole-line Schrödinger operator

$$
L := -\partial_x^2 + q
$$

for potentials

$$
q \in B_\delta := \{ q \in H^{-1}(\mathbb{R}) : \| q \|_{H^{-1}(\mathbb{R})} \leq \delta\} \tag{2.1}
$$

and $\delta$ small.  Particular attention will be paid to the diagonal $g(x):=G(x,x)$ and its reciprocal $1/g(x)$; the latter appears in the energy density associated to the key microscopic conservation law for KdV.

Let us briefly recall one key fact associated to the Schrödinger operator with $q\equiv 0$: The resolvent

$$
R_0(\kappa) = (-\partial^2_x + \kappa^2)^{-1} \quad\text{has integral kernel}\quad  G_0(x,y;\kappa) = \tfrac{1}{2\kappa} e^{-\kappa|x-y|} \tag{2.2}
$$

for all $\kappa>0$.

**Proposition 2.1.**
Given $q\in H^{-1}(\mathbb{R})$, there is a unique self-adjoint operator $L$ associated to the quadratic form

$$
\psi \mapsto \int |\psi'(x)|^2 + q(x) |\psi(x)|^2\,dx \quad\text{with domain}\quad  H^1(\mathbb{R}).
$$

It is semi-bounded.  Moreover, for $\delta\leq \frac12$ and $q\in B_\delta$, the resolvent is given by the norm-convergent series

$$
R := (L+\kappa^2)^{-1} = \sum_{\ell=0}^\infty (-1)^\ell \sqrt{R_0} \Bigl( \sqrt{R_0}\,q\,\sqrt{R_0}\Bigr)^\ell \sqrt{R_0} \tag{2.3}
$$

for all $\kappa\geq 1$.

*Proof.*
The key estimate on which all rests is the following:

$$
\begin{aligned}
\Bigl\| \sqrt{R_0}\, q\, \sqrt{R_0} \Bigr\|^2_{\text{op}} \leq \Bigl\| \sqrt{R_0}\, q\, \sqrt{R_0} \Bigr\|^2_{\mathfrak I_2(\mathbb{R})} &= \frac1\kappa \int \frac{|\hat q(\xi)|^2}{\xi^2+4\kappa^2}\,d\xi .
\end{aligned} \tag{2.4}
$$

For $q\in \mathcal S(\mathbb{R})$ the Hilbert–Schmidt norm can be evaluated directly using (2.2):

$$
\begin{aligned}
\Bigl\| \sqrt{R_0}\, q\, \sqrt{R_0} \Bigr\|^2_{\mathfrak I_2(\mathbb{R})} &= \frac1{4\kappa^2} \iint q(x) e^{-2\kappa|x-y|}q(y)\,dx\,dy = \text{RHS(2.4)}.
\end{aligned}
$$

This then extends to all $q\in H^{-1}(\mathbb{R})$ by approximation.

From (2.4), we see that

$$
\int q(x)|\psi(x)|^2 \,dx \leq \kappa^{-1/2} \|q\|_{H^{-1}} \int |\psi'(x)|^2 + \kappa^2 |\psi(x)|^2\,dx \quad\text{for all}\quad  \psi \in H^1(\mathbb{R}),
$$

at least for all $\kappa\geq 1$.   (Note that the LHS here should be interpreted via the natural pairing between $H^{-1}$, which contains $q$, and $H^1$, which contains $|\psi|^2$.)  This estimate shows that
$q$ is an infinitesimally form-bounded perturbation of the case $q\equiv 0$ and so the existence and uniqueness of $L$ follows from [58, Theorem X.17].

In view of (2.4), the series (2.3) converges provided we just choose $\delta <1$.
 $\square$

**Proposition 2.2 (Diffeomorphism property).**  There exists $\delta>0$ so that the following are true for all $\kappa\geq 1${:}

(i) For each $q\in B_\delta$, the resolvent $R$ admits a continuous integral kernel $G(x,y;\kappa,q)${;} thus, we may unambiguously define

$$
g(x;\kappa,q):=G(x,x;\kappa,q). \tag{2.5}
$$

(ii) The mappings

$$
q\mapsto g-\tfrac1{2\kappa} \quad\text{and}\quad  q\mapsto \kappa-\tfrac1{2g} \tag{2.6}
$$

are (real analytic) diffeomorphisms of $B_\delta$ into $H^1(\mathbb{R})$.

(iii) If $q(x)$ is Schwartz, then so are $g(x)- \tfrac1{2\kappa}$ and $\kappa-\tfrac1{2g(x)}$.  Indeed,

$$
\|g'(x)\|_{H^{s}}  \lesssim_s \| q \|_{H^{s-1}} \quad\text{and}\quad  \| \langle x\rangle ^s g'(x) \|_{L^2}  \lesssim_s \| \langle x\rangle ^s q \|_{H^{-1}} \tag{2.7}
$$

for every integer $s\geq 0$.

*Remark.*
The diffeomorphism property is necessarily restricted to a neighborhood of the origin because for $q$ large, the spectrum of $L$ may intersect $-\kappa^2$.

*Proof.*
Initially, we ask that $\delta\leq \frac12$; later, we will add further restrictions.

From (2.3) and (2.4), we see that

$$
\Bigl\| \sqrt{\kappa^2-\partial_x^2} \bigl(R - R_0\bigr) \sqrt{\kappa^2-\partial_x^2} \Bigr\|_{\mathfrak{I}_2} < \infty \quad\text{for all}\quad  q\in B_\delta \quad\text{and all}\quad  \kappa\geq 1.
$$

Consequently, $G-G_0$ exists as an element of $H^1(\mathbb{R})\otimes H^1(\mathbb{R})$.  Here we mean tensor product in the Hilbert-space sense (cf. [57]); note that $H^1(\mathbb{R})\otimes H^1(\mathbb{R})$ is comprised of those $f\in H^1(\mathbb{R}^2)$ for which $\partial_x\partial_yf \in L^2(\mathbb{R}^2)$.  It follows that $G(x,y;\kappa,q)$ is a continuous function of $x$ and $y$ and we may define

$$
g(x) = g(x;\kappa,q) = \tfrac1{2\kappa} + \sum_{\ell=1}^\infty (-1)^\ell \Bigl\langle\sqrt{R_0}\delta_x,\ \Bigl( \sqrt{R_0}\,q\,\sqrt{R_0}\Bigr)^\ell \sqrt{R_0} \delta_x\Bigr\rangle, \tag{2.8}
$$

where inner products are taken in $L^2(\mathbb{R})$.  This settles (i).

Next we observe that by (2.3) and (2.4),

$$
\begin{aligned}
\Bigl| \int f(x) \bigl[g(x) -\tfrac1{2\kappa}\bigr]\,dx \Bigr| &\leq \sum_{\ell=1}^\infty  \Bigl\| \sqrt{R_0}\, f\, \sqrt{R_0} \Bigr\|_{\mathfrak I_2(\mathbb{R})}\Bigl\| \sqrt{R_0}\, q\, \sqrt{R_0} \Bigr\|_{\mathfrak I_2(\mathbb{R})}^\ell \\
&\leq 2\delta\kappa^{-1} \|f\|_{H^{-1}(\mathbb{R})}
\end{aligned}
$$

for any Schwartz function $f$.  Thus $g-\frac1{2\kappa}\in H^1(\mathbb{R})$; indeed,

$$
\bigl\| g - \tfrac1{2\kappa} \bigr\|_{H^1(\mathbb{R})} \leq 2\delta\kappa^{-1}. \tag{2.9}
$$

Moreover, this argument precisely shows the convergence of the series (2.8) and so that the mapping from $q\in B_\delta$ to $g-\frac1{2\kappa}\in H^{1}(\mathbb{R})$ is real analytic.

Given $f\in H^{-1}(\mathbb{R})$, the resolvent identity implies

$$
\frac{d\ }{ds}\biggr|_{s=0} g(x;q+sf) = - \int G(x,y)f(y)G(y,x)\,dy . \tag{2.10}
$$

In particular, by (2.2),

$$
dg\bigr|_{q\equiv 0} = - \kappa^{-1} R_0(2\kappa),
$$

which is an isomorphism of $H^{-1}_\kappa$ onto $H^1_\kappa$, with condition number equal to $1$. Moreover, by (2.4), (2.3), and duality,

$$
\bigl\| dg\bigr|_{q\equiv 0} - dg\bigr|_q \bigr\|_{H^{-1}_\kappa \to H^{1\vphantom{+}}_\kappa} \lesssim \kappa^{-1} \|q\|_{H^{-1}_\kappa}
    \lesssim  \delta \Bigl\| \bigl(dg\bigr|_{q\equiv 0} \bigr)^{-1} \Bigr\|_{H^{1\vphantom{+}}_\kappa \to H^{-1}_\kappa}^{-1} . \tag{2.11}
$$

Thus choosing $\delta$ sufficiently small, the inverse function theorem guarantees that

$$
q \mapsto g - \tfrac{1}{2\kappa} \quad\text{is a diffeomorphism of $\{ q : \|q\|_{H^{-1}_\kappa} \leq \delta\}$ into $H^{1}_\kappa$}. \tag{2.12}
$$

Note that (2.11) combined with the standard contraction-mapping proof of the implicit function theorem guarantees that $\delta$ can be chosen independently of $\kappa$.  The claimed $H^{-1}\to H^1$ diffeomorphism property of this map then follows since

$$
\|q\|_{H^{-1}_\kappa} \leq \|q\|_{H^{-1}} \quad\text{and}\quad  \| f\|_{H^1_\kappa} \lesssim_\kappa \|f\|_{H^1}.
$$

Choosing $\delta$ even smaller if necessary, (2.9) together with the embedding $H^1\hookrightarrow L^\infty$ guarantees that

$$
\tfrac1{4\kappa} \leq g(x) \leq \tfrac{3}{4\kappa} \quad\text{for all $q\in B_\delta$.}
$$

Consequently, the second mapping in (2.6) is also real-analytic.  To prove that it is a diffeomorphism (for some $\kappa$-independent choice of $\delta$), we simply note that

$$
f \mapsto \frac{f}{1+f}
$$

is a diffeomorphism from a neighbourhood of zero in $H^1(\mathbb{R})$ into $H^1(\mathbb{R})$, write

$$
\kappa-\tfrac1{2g} = \kappa \frac{2\kappa(g-\frac1{2\kappa} )}{1+2\kappa(g-\frac1{2\kappa} )},
$$

and use (2.9) together with (2.12).

We now turn our attention to part (iii).  The Green's function associated to a translated potential is simply the translation of the original Green's function.  Correspondingly,

$$
g(x+h;q) = g\bigl(x; q(\cdot+h)\bigr)  \qquad\text{for all $h\in\mathbb{R}$.} \tag{2.13}
$$

Differentiating with respect to $h$ at $h=0$ and invoking (2.8) yields

$$
\begin{aligned}
\int \bigl[\partial_x^s g(x)\bigr] f(x)\,dx &\leq \sum_{\ell=1}^\infty \sum_{\sigma} \binom{s}{\sigma}  \Bigl\| \sqrt{R_0}\, f\, \sqrt{R_0} \Bigr\|_{\mathfrak I_2(\mathbb{R})}
    \prod_{k=1}^\ell \Bigl\| \sqrt{R_0}\, q^{(\sigma_k)}\, \sqrt{R_0} \Bigr\|_{\mathfrak I_2(\mathbb{R})}.
\end{aligned}
$$

Here, the inner sum extends over multi-indices $\sigma=(\sigma_1,\ldots,\sigma_\ell)$ with $|\sigma|=s$.  Maximizing over unit vectors $f\in H^{-1}$, exploiting (2.4), and using

$$
\prod_{k=1}^\ell \bigl\| q^{(\sigma_k)} \bigr\|_{H^{-1}} \leq  \bigl\| q^{(s)} \bigr\|_{H^{-1}} \bigl\| q \bigr\|_{H^{-1}}^{\ell-1},
$$

which is merely an application of Holder's inequality in Fourier variables, this yields

$$
\begin{aligned}
\bigl\|\partial_x^s g(x)\bigr\|_{H^{1}}  &\leq  \sum_{\ell=1}^\infty \ell^s \bigl\| q^{(s)} \bigr\|_{H^{-1}} \delta^{\ell-1} \lesssim_s \bigl\| q\bigr\|_{H^{s-1}}.
\end{aligned}
$$

Thus we have verified the first claim in (2.7).

To address the second assertion in (2.7), we first make the following claim: For every integer $s\geq 0$,

$$
\langle x\rangle^s R_0 = \sum_{r=0}^s \sqrt{R_0}\, A_{r,s} \sqrt{R_0}\, \langle x\rangle^r
\quad\text{with operators}\quad  \| A_{r,s} \|_{L^2\to L^2}\lesssim_s 1. \tag{2.14}
$$

This is easily verified recursively, by repeatedly using the following commutators:

$$
\begin{aligned}
\bigl[ \langle x\rangle,\  R_0\bigr] = R_0 \bigl[ -\partial_x^2 +\kappa^2 ,\ \langle x\rangle \bigr] R_0 &= -R_0 \bigl(\tfrac{x}{\langle x\rangle} \partial_x + \partial_x\tfrac{x}{\langle x\rangle}\bigr) R_0 \\
\bigl[ \tfrac{x}{\langle x\rangle} \partial_x + \partial_x\tfrac{x}{\langle x\rangle},\ \langle x\rangle\bigr]  &= 2\tfrac{x^2}{\langle x\rangle^2}.
\end{aligned} \tag{2.15}
$$

In connection with (2.14), let us also pause to note that

$$
\bigl\| \langle x\rangle^r q \bigr\|_{H^{-1}} \lesssim_{s} \bigl\| \langle x\rangle^s q \bigr\|_{H^{-1}} \quad\text{for any pair of integers $0\leq r\leq s$}, \tag{2.16}
$$

since $\langle x\rangle^{-1}\in H^1(\mathbb{R})$, which is an algebra.

By applying (2.8), (2.4), (2.14), and (2.16), we deduce that

$$
\begin{aligned}
\int  f(x) & \langle x\rangle^s \bigl[g(x) -\tfrac{1}{2\kappa} \bigr]\,dx \\
&\lesssim_s \sum_{\ell=1}^\infty \sum_{r=0}^s \Bigl\| \sqrt{R_0}\, f\, \sqrt{R_0} \Bigr\|_{\mathfrak I_2(\mathbb{R})}  \Bigl\| \sqrt{R_0}\, \langle x\rangle^r q\, \sqrt{R_0} \Bigr\|_{\mathfrak I_2(\mathbb{R})} \delta^{\ell-1} \\
&\lesssim_s \bigl\| f \bigr\|_{H^{-1}} \bigl\| \langle x\rangle^s q \bigr\|_{H^{-1}}.
\end{aligned}
$$

Optimizing over $f\in H^{-1}(\mathbb{R})$, it then follows that

$$
\| \langle x\rangle^s g'(x) \|_{L^2(\mathbb{R})} \lesssim_s \bigl\| \langle x\rangle^s \bigl[g(x) -\tfrac{1}{2\kappa} \bigr] \bigr\|_{H^1(\mathbb{R})} \lesssim_s \| \langle x\rangle ^s q \|_{H^{-1}},
$$

thereby completing the proof of (2.7) and so the proof of the proposition.
 $\square$

**Proposition 2.3 (Elliptic PDE).**
The diagonal Green's function obeys

$$
\begin{aligned}
g'''(x) &= 2 \bigl[q(x) g(x) \bigr]' + 2 q(x) g'(x) + 4\kappa^2 g'(x) .
\end{aligned} \tag{2.17}
$$

*Proof.*
By virtue of being the Green's function,

$$
\bigl( -\partial_x^2 + q(x) \bigr) G(x,y) = -\kappa^2 G(x,y) + \delta(x-y) = \bigl( -\partial_y^2 + q(y) \bigr) G(x,y)
$$

and consequently,

$$
\begin{aligned}
\bigl( \partial_x + \partial_y\bigr)^3 G(x,y) &= \bigl(q'(x)+q'(y)\bigr)G(x,y) + 2\bigl(q(x)+q(y)\bigr) \bigl( \partial_x + \partial_y\bigr) G(x,y) \\
&\qquad - \bigl(q(x)-q(y)\bigr) \bigl( \partial_x - \partial_y\bigr) G(x,y) +4\kappa^2\bigl(\partial_x + \partial_y\bigr) G(x,y).
\end{aligned}
$$

Thus specializing to $y=x$, we deduce that

$$
g'''(x) = 2 q'(x) g(x) + 4 q(x) g'(x) + 4 \kappa^2 g'(x),
$$

which agrees with (2.17) after regrouping terms.
 $\square$

*Remark.*
As will be discussed in the proof of Lemma 2.5, the Green's function can be expressed in terms of two solutions $\psi_\pm(x)$ to the Sturm–Liouville equation (the Weyl solutions); see (2.26).
In this sense, $g(x)=\psi_+(x)\psi_-(x)$ was seen to obey (2.17) already in [1].

**Proposition 2.4 (Introducing $\rho$).**
There exists $\delta>0$ so that

$$
\rho(x;\kappa,q) := \kappa - \tfrac{1}{2g(x)} + \tfrac12\int e^{-2\kappa|x-y|} q(y)\,dy \tag{2.18}
$$

belongs to $L^1(\mathbb{R}) \cap H^1(\mathbb{R})$ for all $q\in B_\delta$ and $\kappa\geq 1$.  Moreover, fixing $x\in\mathbb{R}$, the map $q\mapsto \rho(x)$ is non-negative and convex.  Additionally,

$$
\alpha(\kappa;q) := \int_\mathbb{R} \rho(x)\,dx \tag{2.19}
$$

defines a non-negative, real-analytic, strictly convex function of $q\in B_\delta$, and satisfies

$$
\alpha(\kappa;q) \approx \frac{1}{\kappa} \int_\mathbb{R} \frac{|\hat q(\xi)|^2\,d\xi}{\xi^2+4\kappa^2}, \tag{2.20}
$$

uniformly for $q\in B_\delta$ and $\kappa\geq 1$.  Lastly,

$$
\alpha(\kappa;q) = - \log\det_2\left( 1+ \sqrt{R_0}\, q \, \sqrt{R_0} \right). \tag{2.21}
$$

*Remarks.*
1. Although we shall have no use for the strict convexity of $q\mapsto\alpha(\kappa;q)$ in this paper, it does have important consequences.  Most notably, by the Radon–Riesz argument, it shows that weakly continuous solutions conserving $\alpha(\kappa)$ are automatically norm-continuous.

2. As noted in the Introduction (see (1.5) and subsequent discussion), the quantity $\alpha(\kappa;q)$ is essentially the logarithm of the transmission coefficient and so well-studied.  Nevertheless, none of the literature we have studied contains the representation (2.19) in terms of the reciprocal of the Green's function.  Rather, prior works employ an integral representation based on the logarithmic derivative of one of the Jost solutions; see (2.28).  To the best of our knowledge, this approach originates in [70, §3], where it was shown to be an effective tool for deriving polynomial conservation laws and for demonstrating that these polynomial conservation laws appear as coefficients in the asymptotic expansion of the logarithm of the transmission coefficient as $\kappa\to\infty$.

Before turning to the proof of Proposition 2.4, we first explain the meaning of RHS(2.21) and then present two lemmas that we shall need.

The symbol $\det_2$ denotes the renormalized Fredholm determinant introduced by Hilbert in [24]; see [62] for a more up-to-date exposition.  In the context of Proposition 2.4, our choice of $\delta$ guarantees that the operator

$$
A = \sqrt{R_0}\, q \, \sqrt{R_0} \quad\text{obeys}\quad  \| A \|_{\mathfrak{I}_2} < 1.
$$

Consequently, it suffices for what follows to exploit only the notion of the trace of an operator (rather than determinant) thanks to the identity

$$
-\log \det_2 \bigl(1 + A \bigr) = \operatorname{tr}\big( A - \log(1+A) \bigr) =  \sum_{\ell=2}^\infty \frac{(-1)^\ell}{\ell} \operatorname{tr}\bigl( A^\ell \bigr). \tag{2.22}
$$

We shall not delve deeply into such matters here, since (2.21) has no bearing on the proof of well-posedness for KdV; indeed, our only reason for verifying this identity is to make the link to the prior works [41, 60], which might otherwise seem unrelated.

**Lemma 2.5.**
There exists $\delta>0$ so that

$$
\int \frac{G(x,y;\kappa,q)G(y,x;\kappa,q)}{2g(y;\kappa,q)^2}\,dy = g(x;\kappa,q) \tag{2.23}
$$

for all $q\in B_\delta$ and all $\kappa\geq 1$.

*Remark.*
Augmenting the proof below with the results of [11, §8.3] shows that (2.23) holds also in the case of $q\in H^{-1}(\mathbb{R}/\mathbb{Z})$ and $\kappa\geq 1$ that obey (6.1).  As below, one first uses analyticity to reduce to a case where one may apply ODE techniques, more specifically, to the case of small smooth periodic potentials.

*Proof.*
We choose $\delta>0$ as needed for Proposition 2.2.  In this case, both sides of (2.23) are analytic functions of $q$.  Consequently, it suffices to prove the result under the additional hypotheses that $q$ is Schwartz and $\|q\|_{L^\infty}<1$.

Techniques in Sturm–Liouville theory (cf. [11, §3.8]) show that there are solutions $\psi_\pm(x)$ to

$$
-\psi'' + q \psi = -\kappa^2 \psi \tag{2.24}
$$

that decay (along with derivatives) exponentially as $x\to\pm\infty$ and grow exponentially as $x\to\mp\infty$.  Constancy of the Wronskian guarantees that these Weyl solutions (as they are known) are unique up to scalar multiples; we (partially) normalize them by requiring the Wronskian relation

$$
\psi_+(x) \psi_-'(x) - \psi_+'(x)\psi_-(x) = 1 \tag{2.25}
$$

and that $\psi_\pm(x) >0$.  Note that the Sturm oscillation theorem guarantees that neither solution may change sign.

Using the Weyl solutions, we may write the Green's function as

$$
G(x,y) = \psi_+(x\vee y) \psi_-(x\wedge y). \tag{2.26}
$$

In this way, the proof of the lemma reduces to showing that

$$
\tfrac12 \int_{-\infty}^x \Bigl[\tfrac{\psi_+(x)}{\psi_+(y)}\Bigr]^2 \,dy + \tfrac12 \int_x^\infty \Bigl[\tfrac{\psi_-(x)}{\psi_-(y)}\Bigr]^2 \,dy = \psi_+(x)\psi_-(x). \tag{2.27}
$$

However, by (2.25), we have

$$
\tfrac{d\ }{dy} \tfrac{\psi_-(y)}{\psi_+(y)} = \tfrac{1}{\psi_+(y)^2} \quad\text{and}\quad  \tfrac{d\ }{dy} \tfrac{\psi_+(y)}{\psi_-(y)} = - \tfrac{1}{\psi_-(y)^2}.
$$

Thus (2.27) follows by the fundamental theorem of calculus and the exponential behavior of $\psi_\pm(y)$, as $|y|\to \infty$.
 $\square$

*Remark.*
As mentioned above, there is an alternate integral representation of $\alpha(\kappa;q)$ introduced much earlier.  The proof of Lemma 2.5 provides the requisite vocabulary to explain what that is:

$$
\log[a(i\kappa)] = - \int \tfrac{\psi_+'(y)}{\psi_+(y)} + \kappa \,dy = \int \tfrac{\psi_-'(y)}{\psi_-(y)} - \kappa \,dy. \tag{2.28}
$$

Here $\psi_\pm$ represent the Weyl solutions; however, the formula applies equally well using the Jost solutions, since they differ only in normalization.  It is in this equivalent form that the first identity appears in [70, §3].
Averaging these two representations and invoking (2.25) and then (2.26) yields

$$
\log[a(i\kappa)] = \int \tfrac{1}{2\psi_-(y)\psi_+(y)} - \kappa \,dy = \int \tfrac{1}{2g(y)} - \kappa\,dy, \tag{2.29}
$$

which is readily seen to be equivalent to (2.19).  One easy way to distinguish these three representations is the fact that $\psi_+(y)$ depends only on the values of $q$ on the interval $[y,\infty)$, while $\psi_-(y)$ is determined by $q$ on the interval $(-\infty,y]$; on the other hand, $g(y)$ depends on the values of $q$ throughout the real line.

The following identity will be used not only in the proof of Proposition 2.4, but also in Section 3.

**Lemma 2.6.**   Given Schwartz functions $f$ and $q$,

$$
\begin{aligned}
& \int G(x,y;\kappa,q) \bigl[ - f'''(y) + 2q(y)f'(y) + 2\bigl(q(y)f(y)\bigr)'+4\kappa^2 f'(y)\bigr]G(y,x;\kappa,q)\,dy \\
&= 2 f'(x)g(x;\kappa,q) - 2f(x)g'(x;\kappa,q).
\end{aligned}
$$

This identity also holds if merely $f(x)-c$ is Schwartz for some constant $c$.

*Proof.*
The argument that follows applies equally well irrespective of the presence/absence of the constant $c$.  Alternately, as both sides of the identity are linear in $f$, the cases $f$ Schwartz and $f$ constant can be treated separately. However, when $f$ is constant the identity can be obtained more swiftly by other means; see (3.9).

The most elementary proof proceeds from the defining property of $G$, namely,

$$
\bigl(-\partial_y^2 + q(y) + \kappa^2\bigr)G(y,x) = \bigl(-\partial_y^2 + q(y) + \kappa^2\bigr)G(x,y) = \delta(x-y)
$$

and integration by parts.  However, we find the argument more palatable when presented in terms of operator identities.  Specifically, from the operator identity

$$
\begin{aligned}
- f''' &= (-\partial^2+\kappa^2)f' + f' (-\partial^2+\kappa^2) - 2(-\partial^2+\kappa^2)f\partial +  2\partial f(-\partial^2+\kappa^2) - 4\kappa^2f',
\end{aligned}
$$

it follows that

$$
- R f''' R = f'R - 2 R qf' R + Rf' - 2f\partial R - 2R[\partial,qf]R  + 2 R\partial f - 4\kappa^2 Rf'R.
$$

Noting, for example, that

$$
g'(x) = \langle\delta_x, [\partial,R]\delta_x\rangle,
$$

the lemma then follows by considering the diagonal of the associated integral kernel.
 $\square$

*Proof of Proposition 2.4.*
By (2.2),

$$
\tfrac12\int e^{-2\kappa|x-y|} q(y)\,dy = 2\kappa [R_0(2\kappa) q](x).
$$

Combined with Proposition 2.2, this shows $\rho\in H^1(\mathbb{R})$.  Next we write

$$
\rho(x) = 2\kappa^2 \bigl[g - \tfrac1{2\kappa} + \tfrac1{\kappa} R_0(2\kappa) q\bigr](x) - \tfrac{2\kappa^2}{g(x)}[g(x)-\tfrac1{2\kappa}]^2 .
$$

The second summand belongs to $L^1(\mathbb{R})$ by Proposition 2.2; thus it remains to consider the first summand.  To this end, we use (2.8) and (2.4) to obtain

$$
\begin{aligned}
\int \bigl[g - \tfrac1{2\kappa} + \tfrac1{\kappa} R_0(2\kappa) q\bigr](x) f(x)\,dx &= \sum_{\ell=2}^\infty (-1)^\ell \operatorname{tr}\Bigl\{\sqrt{R_0} f \sqrt{R_0} \Bigl( \sqrt{R_0}\,q\,\sqrt{R_0}\Bigr)^\ell \Bigr\} \\
&\leq \| f \|_{L^\infty}  \Bigl\|\sqrt{R_0}\Big\|_{op}^2 \Bigl\| \sqrt{R_0}\,q\,\sqrt{R_0}\Bigr\|^2_{\mathfrak{I}_2} \sum_{\ell=2}^\infty \delta^{\ell-2},
\end{aligned} \tag{2.30}
$$

from which we may conclude that $\rho\in L^1(\mathbb{R})$.  Note that the arguments just presented actually show that $q\mapsto\rho$ is real analytic as a mapping of $B_\delta$ into $L^1\cap H^1$.

To show convexity at fixed $x$, we compute derivatives.  As in (2.10), the resolvent identity guarantees that

$$
d[\rho(x)]\bigr|_q (f) =  \tfrac{-1}{2g(x)^2} \int G(x,y) f(y) G(y,x) \,dy + \tfrac12 [e^{-2\kappa|\cdot|} * f ](x) \tag{2.31}
$$

and thence

$$
\begin{aligned}
d^2[\rho(x)]\bigr|_q (f,h) = {}&{}\tfrac{-1}{g(x)^3} \iint G(x,y) f(y) G(y,x) G(x,z) h(z) G(z,x) \,dy\,dz \\
& + \tfrac{1}{g(x)^2} \iint G(x,y) f(y) G(y,z) h(z) G(z,x) \,dy\,dz.
\end{aligned} \tag{2.32}
$$

Multiplying through by $g(x)^3>0$ we then see that the convexity of $\rho(x)$ is reduced to the assertion that

$$
\bigl\langle \sqrt{R} \delta_x,\sqrt{R} \delta_x\bigr\rangle \bigl\langle \sqrt{R} \delta_x,\sqrt{R}fRf\sqrt{R}\,\sqrt{R} \delta_x\bigr\rangle
    - \bigl\langle \sqrt{R} \delta_x,\sqrt{R}f\sqrt{R}\, \sqrt{R} \delta_x\bigr\rangle^2 \geq 0
$$

for all $f\in H^{-1}(\mathbb{R})$.  (Here inner-products are taken in $L^2(\mathbb{R})$ which contains $\sqrt{R} \delta_x$.)  The veracity of this assertion now follows immediately from the Cauchy–Schwarz inequality.

Specializing (2.31) to $q\equiv 0$ and substituting (2.2) shows

$$
\frac{\delta\rho(x)}{\delta q}\biggr|_{q\equiv0} = 0. \tag{2.33}
$$

Note also that $\rho(x)\equiv0$ when $q\equiv 0$.  In this way the convexity of $q\mapsto \rho(x)$ guarantees its positivity.

Let us now turn our attention to $\alpha(\kappa;q)$.  In view of the preceding, we already know that this is a non-negative, convex, and real-analytic function of $q\in B_\delta$.  It remains to show strict convexity, (2.20), and (2.21).

As we have already noted, $\rho(x)\equiv 0$ when $q\equiv 0$.  Thus (2.21) holds trivially in this case.  In general (2.21) follows easily from

$$
\frac{\delta \alpha}{\delta q} = \tfrac{1}{2\kappa} - g(x)  = \frac{\delta\ }{\delta q} - \log\det_2\left( 1+ \sqrt{R_0}\, q \, \sqrt{R_0} \right), \tag{2.34}
$$

which we will now verify.

From (2.31) and Lemma 2.5,

$$
\begin{aligned}
\frac{d\ }{ds}\biggr|_{s=0} \alpha(\kappa; q+sf) &= - \iint \frac{G(y,x)G(x,y)}{2g(x)^2} f(y)\,dx  \,dy+ \tfrac1{2\kappa}\int f(y)\,dy \\
&= \int \Bigl[\tfrac{1}{2\kappa} - g(x)\Bigr] f(x)\,dx,
\end{aligned}
$$

at least for Schwartz functions $f$.  This proves the first equality in (2.34).

From (2.22) and (2.8), we have

$$
\begin{aligned}
\frac{d\ }{ds}\biggr|_{s=0} - \log&\det_2\left( 1+ \sqrt{R_0}\, (q+sf) \, \sqrt{R_0} \right) \\
&= \sum_{\ell=2}^\infty (-1)^\ell\operatorname{tr}\Bigl\{ \Bigl(\sqrt{R_0}\, q \, \sqrt{R_0} \Bigr)^{\ell-1} \sqrt{R_0}\, f \, \sqrt{R_0} \Bigr\} \\
&= \int \Bigl[\tfrac{1}{2\kappa} - g(x)\Bigr] f(x)\,dx.
\end{aligned}
$$

This verifies the second equality in (2.34) and so finishes the proof of (2.21).

Toward verifying strict convexity and (2.20), let us first compute the Hessian of $\alpha(\kappa)$ at $q\equiv 0$.  From (2.32) and (2.2), we have

$$
\begin{aligned}
d^2\alpha\bigr|_{q\equiv 0} (f,f) &= -\tfrac{1}{2\kappa} \iiint e^{-2\kappa|x-y| - 2\kappa|x-z|}  f(y)f(z) \,dx\,dy\,dz \\
&\quad  + \tfrac{1}{2\kappa} \iiint e^{-\kappa|x-y| - \kappa|y-z| - \kappa|z-x|} f(y) f(z) \,dx\,dy\,dz \\
&= \tfrac{1}{4\kappa^2} \iint e^{-2\kappa|y-z|} f(y) f(z) \,dy\,dz = \tfrac{1}{\kappa} \int \frac{|\hat f(\xi)|^2}{\xi^2+4\kappa^2}\,d\xi.
\end{aligned} \tag{2.35}
$$

As $\alpha(\kappa)$ is real analytic, this immediately shows strict convexity and (2.20) in some neighbourhood of $q\equiv 0$; however, to verify that the size $\delta$ of this neighbourhood may
be taken independent of $\kappa$, we must adequately control the modulus of continuity of the Hessian.  From (2.11) and the first identity in (2.34), we have

$$
\Bigl|\Bigl( d^2\alpha\bigr|_{q\equiv 0} - d^2\alpha\bigr|_{q}\Bigr)(f,f)\Bigr| \lesssim \delta\kappa^{-1} \int \frac{|\hat f(\xi)|^2}{\xi^2+4\kappa^2}\,d\xi,
$$

thereby settling the matter.
 $\square$

## 3. Dynamics

The natural Poisson structure on $\mathcal S(\mathbb{R})$ or $C^\infty(\mathbb{R}/\mathbb{Z})$ associated to the KdV equation is

$$
\{ F, G \} = \int  \frac{\delta F}{\delta q}(x) \biggl(\frac{\delta G}{\delta q}\biggr) '(x) \,dx . \tag{3.1}
$$

This structure is degenerate: $q\mapsto \int q$ is a Casimir (i.e. Poisson commutes with everything).  It is common practice to say that this is the
Poisson bracket associated to the (degenerate) almost complex structure $J=\partial_x$ and the $L^2$ inner product.  We shall not need such notions; however, they do suggest a very convenient notation for the time-$t$ flow under the Hamiltonian $H$:

$$
q(t) = e^{t J\nabla\! H} q(0).
$$

Note that under our sign conventions,

$$
\frac{d\ }{dt}\ F\circ e^{t J\nabla\! H} = \{ F, H \} \circ e^{t J\nabla\! H}.
$$

As two simple examples, we note that for

$$
P:=\int \tfrac12 |q(x)|^2\,dx \quad\text{and}\quad  H_\text{KdV} := \int \tfrac12 |q'(x)|^2 + q(x)^3 \,dx,
$$

we have

$$
\frac{\delta P}{\delta q}(x) = q(x)  \quad\text{and}\quad  \frac{\delta H_\text{KdV}}{\delta q}(x) = -q''(x) + 3q(x)^2. \tag{3.2}
$$

Thus, the flow associated to $P$ is precisely $\partial_t q = \partial_x q$, which is to say, $P$ represents momentum (= generator of translations); the flow associated to $H_\text{KdV}$ is precisely the KdV equation.
Note that $H_\text{KdV}$ and $P$ Poisson commute:

$$
\{H_\text{KdV},P\}=\int \bigl(-q''(x)+3q(x)^2\bigr) q'(x)\,dx = \int \bigl(-\tfrac12 q'(x)^2 + q(x)^3\bigr)' \,dx =0.
$$

This simultaneously expresses that the KdV flow conserves $P$ and that $H_\text{KdV}$ is conserved under translations.  Moreover, the two flows commute:

$$
e^{s J\nabla\! P} \circ e^{t J\nabla\! H_\text{KdV}} = e^{t J\nabla\! H_\text{KdV}} \circ e^{s J\nabla\! P} \quad\text{for all}\quad  s,t\in\mathbb{R},
$$

at least as mappings of Schwartz space.  The claim that the KdV flow commutes with translations is without controversy; nonetheless, it is important for what follows to see that it stems precisely from the vanishing of the Poisson bracket.  Fortunately, by restricting our attention to Schwartz-space solutions, we may simply apply the standard arguments from differential geometry; see, for example, [2, §39].

We will also consider one more Hamiltonian, namely,

$$
H_\kappa := - 16 \kappa^5 \alpha(\kappa) + 2 \kappa^2 \int q(x)^2\,dx \tag{3.3}
$$

which, formally at least, converges to

$$
H_\text{KdV} := \int \tfrac12 |q'(x)|^2 + q(x)^3 \,dx
$$

as $\kappa\to\infty$.  In due course, we will see that $H_\kappa$ leads to a well-posed flow on $H^{-1}$ and that it Poisson commutes with both $P$ and $H_\text{KdV}$, at least as a functional on Schwartz space.  For the moment, however, let us describe the evolution of the diagonal Green's function under the KdV flow.

**Proposition 3.1.**
Given $\delta>0$, there is a $\delta_0>0$ so that for every Schwartz solution $q(t)$ to KdV with initial data
$q(0)\in B_{\delta_0}$, we have

$$
\sup_{t\in\mathbb{R}}\| q(t)\|_{H^{-1}(\mathbb{R})} \leq \delta. \tag{3.4}
$$

Moreover, for each $\kappa\geq 1$, the quantities $g(t,x)=g(x;\kappa,q(t))$, $\rho(t,x)=\rho(x;\kappa,q(t))$, and $\alpha(\kappa;q(t))$ obey

$$
\begin{gathered}
\tfrac{d\ }{dt}\, g(t,x)  = -2 q'(t,x) g(t,x) + 2 q(t,x) g'\!(t,x) - 4\kappa^2 g'\!(t,x) \qquad\text{(3.5)} \\
\tfrac{d\ }{dt}  \, \tfrac{1}{2g(t,x)} = \Bigl( \tfrac{q(t,x)}{g(t,x)} - \tfrac{2\kappa^2}{g(t,x)} + 4\kappa^3\Bigr)' \qquad\text{(3.6)} \\
\tfrac{d\ }{dt}  \rho(t,x) = \Bigl(\tfrac32 \bigl[e^{-2\kappa|\cdot|}* q^2\bigr](t,x)  + 2q(t,x)\bigl[ \kappa - \tfrac{1}{2g(t,x)}\bigr] - 4\kappa^2\rho(t,x) \Bigr)' \qquad\text{(3.7)} \\
\tfrac{d\ }{dt} \alpha(\kappa;q(t)) = 0. \qquad\text{(3.8)}
\end{gathered}
$$

*Proof.*
Without loss of generality, we may require that $\delta$ is a small as we wish.  We shall require that $\delta$ meets the requirements of Propositions 2.2, 2.3, and 2.4.  As an initial choice, we then set $\delta_0=\tfrac12\delta$.  This guarantees that these propositions are all applicable to $q(t)$ for some open interval of times containing $t=0$.  (Schwartz solutions are necessarily continuous in $H^{-1}(\mathbb{R})$.)  We will show below that equations (3.5)–(3.8) are valid on this time interval. But then, choosing $\kappa=1$ in (2.20) and (3.8), we obtain

$$
\| q(t) \|_{H^{-1}} \lesssim \| q(0) \|_{H^{-1}}
$$

on this interval.  Thus we see that (3.4) holds globally in time, after updating our choice of $\delta_0$, if necessary.

It remains to show that the stated differential equations apply to Schwartz solutions whose $H^{-1}$ norm is small enough that the results of Section 2 apply.  We begin the proof in earnest after one minor preliminary: by taking an $h$ derivative in (2.13) and using the resolvent identity, we have

$$
g'(x; q) =  - \int G(x,y) q'(y) G(y,x)\,dy. \tag{3.9}
$$

By the resolvent identity, then Lemma 2.6, and then (3.9),

$$
\begin{aligned}
\frac{d\ }{dt} g(&x; q(t)) =  - \int G(x,y) \bigl[ -q'''(t,y) + 6q(t,y)q'(t,y) \bigr]  G(y,x)\,dy \\
&= - 2 q'(t,x)g(x; q(t)) + 2 q(t,x) g'(x; q(t)) + 4\kappa^2 \int G(x,y) q'(t,y)  G(y,x)\,dy \\
&= - 2 q'(t,x)g(x; q(t)) + 2 q(t,x) g'(x; q(t)) - 4\kappa^2 g'(x;q(t)).
\end{aligned}
$$

This proves (3.5).  Alternately, (3.5) can be derived from the Lax pair formulation of KdV; specifically,

$$
\frac{d\ }{dt} \bigl(L(t)+\kappa^2\bigr)^{-1} = \bigl[ P(t), \bigl(L(t)+\kappa^2\bigr)^{-1} \bigr] .
$$

We leave the details to the interested reader.

Equation (3.6) follows immediately from (3.5) and the chain rule, while (3.7) is simply a combination of (3.6) and (KdV).  Lastly, (3.8) follows from integrating (3.7) in $x$ over the whole line.
 $\square$

*Remark.*  Combining (2.17) and (3.5) yields

$$
\begin{aligned}
\tfrac{d\ }{dt}\, g(x) &= \Bigl( 2g''(x) -6q(x)g(x) - 12\kappa^2g(x) + 6\kappa \Bigr)' ,
\end{aligned} \tag{3.10}
$$

from which we see that there is also a microscopic conservation law for the KdV flow associated to $g(x)$. Ultimately, however, this turns out to be a consequence of the conservation of $\alpha(\kappa)$; specifically, we have

$$
\frac{d\ }{d\kappa} \alpha(\kappa) = - 2\kappa  \int g(x) - \tfrac{1}{2\kappa} + \tfrac{1}{4\kappa^3} q(x) \,dx.
$$

**Proposition 3.2.**
Fix $\kappa\geq 1$. The Hamiltonian evolution induced by $H_\kappa$ is

$$
\tfrac{d\ }{dt} q(x) = 16\kappa^5 g'(x;\kappa) + 4\kappa^2 q'(x). \tag{3.11}
$$

This flow is globally well-posed for initial data in $B_\delta$, for $\delta>0$ small enough (independent of $\kappa$), and conserves $\alpha(\varkappa)$ for any $\varkappa\geq 1$.  Moreover, in the case of Schwartz-class initial data, the solution is Schwartz-class for all time, the associated diagonal Green's function evolves according to

$$
\begin{aligned}
\tfrac{d\ }{dt}  \, \tfrac{1}{2g(x;\varkappa)} &= - \tfrac{4\kappa^5}{\kappa^2-\varkappa^2} \Bigl( \tfrac{g(x;\kappa)}{g(x;\varkappa)} -\tfrac{\varkappa}{\kappa} \Bigr)' + 4\kappa^2 \Bigl( \tfrac{1}{2g(x;\varkappa)} - \varkappa \Bigr)'
    \quad\text{if $\varkappa\neq \kappa$},
\end{aligned} \tag{3.12}
$$

and the flow commutes with that of $H_\text{KdV}$.

*Proof.*
From (2.34) and (3.2) we see that

$$
\frac{\delta H_\kappa}{\delta q} = - 16 \kappa^5\bigl[\tfrac{1}{2\kappa} - g(x;\kappa,q)\bigr]  + 4 \kappa^2 q(x) ,
$$

from which (3.11) immediately follows.

Rewriting (3.11) as the integral equation

$$
q(t,x) = q(0,x+4\kappa^2 t) + \int_0^t 16\kappa^5 g'\bigl(x+4\kappa^2(t-s);\kappa,q(s)\bigr) \,ds ,
$$

we see that local well-posedness follows by Picard iteration and the estimate

$$
\bigl\| g'(x,q) - g'(x,\tilde q) \bigr\|_{H^{-1}} \lesssim \bigl\| g(x,q) - g(x,\tilde q) \bigr\|_{H^{1}} \lesssim \| q -\tilde q \|_{H^{-1}},
$$

which in turn follows from the diffeomorphism property.

Global well-posedness follows from local well-posedness, once we prove that $\alpha(\varkappa)$ is conserved, since we may then use (2.20) to guarantee that the solution remains small in $H^{-1}$.  (This argument appeared already in Proposition 3.1.)  Moreover, because the problem is $H^{-1}$-locally well-posed, it suffices to verify conservation of $\alpha(\varkappa)$ just in the case of Schwartz initial data.  Note that (2.7) shows that solutions with Schwartz initial data remain in Schwartz class.  So let us consider a Schwartz solution $q(t)$ to (3.11) and endeavor to prove conservation of $\alpha(\varkappa)$.  Actually, it suffices to prove (3.12), because conservation of $\alpha(\varkappa)$ follows from this and (3.11).

By the resolvent identity and (3.11),

$$
\begin{aligned}
\tfrac{d\ }{dt} \tfrac{1}{2 g(t,x;\varkappa)}  ={} & \tfrac{8\kappa^5}{g(t,x;\varkappa)^2} \int G(x,y;\varkappa,q(t)) g'(t,y;\kappa) G(y,x;\varkappa,q(t))\,dy \\
& + \tfrac{2\kappa^2}{g(t,x;\varkappa)^2} \int G(x,y;\varkappa,q(t)) q'(t,y) G(y,x;\varkappa,q(t))\,dy.
\end{aligned}
$$

From here we substitute the following rewriting of (2.17)

$$
4(\kappa^2-\varkappa^2) g'(y;\kappa) = -\bigl[ - g'''(y;\kappa) + 2\bigl(q(y)g(y;\kappa)\bigr)' + 2 q(y)g'(y;\kappa) + 4\varkappa^2g'(y;\kappa)\bigr]
$$

into the first term and use Lemma 2.6, while for the second term we employ (3.9).  In this way, we deduce that

$$
\begin{aligned}
\tfrac{d\ }{dt} \tfrac{1}{2 g(t,x;\varkappa)}  &= - \tfrac{4\kappa^5}{(\kappa^2-\varkappa^2) g(t,x;\varkappa)^2} \bigl[ g'(t,x;\kappa)g(t,x;\varkappa)  - g(t,x;\kappa)g'(t,x;\varkappa) \bigr] \\
&\qquad - \tfrac{2\kappa^2}{g(t,x;\varkappa)^2} g'(t,x;\varkappa),
\end{aligned}
$$

which agrees with (3.12).

Lastly, by (3.3) and Proposition 3.1,

$$
\{ H_\kappa, H_\text{KdV} \} = - 16 \kappa^5 \{ \alpha(\kappa), H_\text{KdV} \} + 4 \kappa^2 \{ P, H_\text{KdV} \} = 0,
$$

which shows that the $H_\kappa$ and $H_\text{KdV}$ flows commute, at least as mappings on Schwartz space.
 $\square$

## 4. Equicontinuity

Let us first recall the meaning of equicontinuity:

**Definition 4.1.**
A subset $Q$ of $H^s$ is said to be *equicontinuous* if

$$
q(x+h) \to q(x) \quad\text{in $H^s$ as $h\to 0$, uniformly for $q\in Q$.} \tag{4.1}
$$

This definition works in great generality.  For $H^s$ spaces, it is also common to define equicontinuity as tightness of the Fourier transform.  The two approaches are easily reconciled, as our next lemma shows.

**Lemma 4.2.**
Fix $-\infty < \sigma < s <\infty$. Then:

(i) A bounded subset $Q$ of $H^s(\mathbb{R})$ is equicontinuous in $H^s(\mathbb{R})$ if and only if

$$
\int_{|\xi|\geq \kappa} |\hat q(\xi)|^2 (\xi^2+4)^s \,d\xi \to 0  \quad\text{as $\kappa\to \infty$, uniformly for $q\in Q$.}\quad \tag{4.2}
$$

(ii) A sequence $q_n$ is convergent in $H^s(\mathbb{R})$ if and only if it is convergent in $H^\sigma(\mathbb{R})$ and equicontinuous in $H^s(\mathbb{R})$.

*Proof.*
As $Q$ is bounded and

$$
\begin{aligned}
\int |e^{i\xi h}-1|^2 |\hat q(\xi)|^2 (\xi^2+4)^s \,d\xi &\lesssim \kappa^2 h^2 \int |\hat q(\xi)|^2 (\xi^2+4)^s \,d\xi \\
&\qquad  + \int_{|\xi|>\kappa} |\hat q(\xi)|^2 (\xi^2+4)^s \,d\xi,
\end{aligned}
$$

we see that (4.2) implies (4.1).  To prove the converse, we note that

$$
\begin{aligned}
\int |e^{i\xi h}-1|^2\, \kappa e^{-2\kappa|h|}\,dh &= \tfrac{2\xi^2}{\xi^2+4\kappa^2} \gtrsim 1 - \chi_{[-\kappa,\kappa]}(\xi)
\end{aligned}
$$

and hence

$$
\int\, \| q(x+h) - q(x) \|_{H^s(\mathbb{R})}^2 \kappa e^{-2\kappa|h|}\,dh \gtrsim \int_{|\xi|>\kappa} |\hat q(\xi)|^2 (\xi^2+4)^s \,d\xi.
$$

Let us now turn attention to (ii).  As the forward implication is trivial, we need only consider sequences $q_n$ that are convergent in $H^\sigma(\mathbb{R})$ and equicontinuous in $H^s(\mathbb{R})$.  But then writing

$$
\begin{aligned}
\int |\hat q_n(\xi) - \hat q_m(\xi)|^2 (\xi^2+4)^s \,d\xi &\leq (\kappa^2+4)^{s-\sigma} \int |\hat q_n(\xi) - \hat q_m(\xi)|^2 (\xi^2+4)^\sigma \,d\xi \\
&\qquad + \int_{|\xi|>\kappa} |\hat q_n(\xi) - \hat q_m(\xi)|^2 (\xi^2+4)^s \,d\xi
\end{aligned}
$$

and employing (4.2), we see that the sequence is Cauchy in $H^{s}(\mathbb{R})$ and so convergent there also.
 $\square$

It is now easy to see that equicontinuity in $H^{-1}(\mathbb{R})$ is readily accessible through the conserved quantity $\alpha(\kappa;q)$:

**Lemma 4.3.**
A subset $Q$ of $B_\delta$ is equicontinuous in $H^{-1}(\mathbb{R})$ if and only if

$$
\kappa \alpha(\kappa;q) \to 0  \quad\text{as $\kappa\to \infty$, uniformly for $q\in Q$.} \tag{4.3}
$$

*Proof.*
By virtue of (2.20), it suffices to show that $Q$ is equicontinuous in $H^{-1}(\mathbb{R})$ if and only if

$$
\lim_{\kappa\to\infty} \ \sup_{q\in Q}\ \int_{\mathbb{R}} \frac{|\hat q(\xi)|^2}{\xi^2+4\kappa^2} \,d\xi = 0. \tag{4.4}
$$

That (4.4) implies (4.2) and hence equicontinuity follows immediately from

$$
\int_{|\xi|\geq \kappa} \frac{|\hat q(\xi)|^2}{\xi^2+4} \,d\xi \lesssim \int_{\mathbb{R}} \frac{|\hat q(\xi)|^2}{\xi^2+4\kappa^2} \,d\xi .
$$

On the other hand, (4.2) implies (4.4) by virtue of the boundedness of $Q$ and

$$
\begin{aligned}
\int \frac{|\hat q(\xi)|^2}{\xi^2+4\kappa^2} \,d\xi &\lesssim \tfrac{\varkappa^2}{\kappa^2} \int \frac{|\hat q(\xi)|^2}{\xi^2+4} \,d\xi + \int_{|\xi|>\varkappa} \frac{|\hat q(\xi)|^2 \,d\xi}{\xi^2+4}.
\end{aligned}
$$

 $\square$

From the preceding lemma and the conservation of $\alpha(\kappa)$ we readily deduce the following:

**Proposition 4.4.**
Let $Q\subset B_\delta$ be a set of Schwartz functions that is equicontinuous in $H^{-1}(\mathbb{R})$.  Then

$$
Q^* = \bigl\{ e^{J\nabla(t H_\text{KdV} + s H_\kappa)} q : q\in Q,\ t,s\in \mathbb{R},\text{ and } \kappa\geq 1 \bigr\} \tag{4.5}
$$

is equicontinuous in $H^{-1}(\mathbb{R})$.  By virtue of this,

$$
4\kappa^3\bigl[ \tfrac1{2\kappa} - g(x;\kappa,q) \bigr] \to q \quad\text{in $H^{-1}(\mathbb{R})$ as $\kappa\to\infty$}, \tag{4.6}
$$

uniformly for $q\in Q^*$.

*Proof.*
By Lemma 4.3 and (2.20), the boundedness and equicontinuity of $Q$ guarantees that $\alpha(\kappa;q)$ is uniformly bounded on $Q$ and that

$$
\lim_{\kappa\to\infty} \kappa \alpha(\kappa;q) = 0 \quad\text{uniformly for $q\in Q$.}
$$

But then since $\alpha(\kappa;q)$ is conserved under these flows, we may reverse this reasoning to deduce that $Q^*$ is equicontinuous as well.

Looking back to (2.30), (2.4), and (2.20), we have

$$
\kappa^3 \bigl\| \tfrac1{2\kappa}  - g(\,\cdot\;;\kappa,q) - \tfrac1{\kappa} R_0(2\kappa) q\bigr\|_{L^1} \lesssim \kappa \alpha(\kappa;q),
$$

which converges to zero as $\kappa\to\infty$ uniformly for $q\in Q^*$ by (4.3).  In this way, the proof of (4.6) is reduced to the simple calculation

$$
\| 4\kappa^2 R_0(2\kappa)q - q \|_{H^{-1}}^2 = \int \frac{\xi^4 |\hat q(\xi)|^2}{(\xi^2+4\kappa^2)^2}\,\frac{d\xi}{\xi^2+4} \leq \int \frac{|\hat q(\xi)|^2}{\xi^2+4\kappa^2}\,d\xi
$$

and (4.4).
 $\square$

## 5. Well-posedness

**Theorem 5.1.**
Let $q_n(t)$ be a sequence of Schwartz solutions to (KdV) on the line and fix $T>0$.  If $q_n(0)$ converges in $H^{-1}(\mathbb{R})$ then so does $q_n(t)$, uniformly for $t\in[-T,T]$.

*Proof.*
Let us first reduce to the case $q_n(0)\in B_\delta$ for any fixed $\delta>0$, which is required in order to apply many of the results of the previous sections.  This is easily handled by a simple scaling argument:
if $q(t,x)$ is a Schwartz solution to (KdV), then so is

$$
q_\lambda(t,x) = \lambda^2 q(\lambda^3 t, \lambda x) \tag{5.1}
$$

for any $\lambda>0$; moreover,

$$
\| q_\lambda(0) \|_{H^{-1}(\mathbb{R})}^2 = \lambda \int \frac{|\hat q(0,\xi)|^2\,d\xi}{\xi^2+4\lambda^{-2}}, \tag{5.2}
$$

which converges to zero as $\lambda\to 0$.  Although it is incidental to the current proof, let us note here that

$$
\begin{gathered}
G(x,y;\kappa,q_\lambda)  = \lambda^{-1} G(\lambda x,\lambda y;\lambda^{-1}\kappa,q),\\
\rho(x;\kappa,q_\lambda) =\lambda\rho(\lambda x;\lambda^{-1}\kappa,q),\quad\text{and}\quad  \alpha(\kappa;q_\lambda) = \alpha(\lambda^{-1}\kappa;q).
\end{gathered} \tag{5.3}
$$

By commutativity of the flows, we have

$$
q_n(t) = e^{t J\nabla(H_\text{KdV} - H_\kappa)} \circ e^{t J\nabla H_\kappa} q_n(0).
$$

Thus, setting $Q=\{q_n(0)\}$ and defining $Q^*$ as in (4.5), we have

$$
\begin{aligned}
\sup_{|t|\leq T} \| q_n(t) - q_m(t) \|_{H^{-1}}  &\leq \sup_{|t|\leq T} \| e^{t J\nabla H_\kappa} q_n(0) - e^{t J\nabla H_\kappa} q_m(0) \|_{H^{-1}} \\
&\qquad + 2 \sup_{q\in Q^*} \sup_{|t|\leq T} \| e^{tJ\nabla (H_\text{KdV} - H_\kappa)} q - q \|_{H^{-1}}.
\end{aligned} \tag{5.4}
$$

Note that $Q^*$ is equicontinuous in $H^{-1}(\mathbb{R})$; this follows from Proposition 4.4.

For fixed $\kappa$, the first term in RHS(5.4) converges to zero as $n,m\to\infty$ due to the well-posedness of the $H_\kappa$ flow; see Proposition 3.2.  Thus, it remains to prove that

$$
\lim_{\kappa\to\infty} \sup_{q\in Q^*} \ \sup_{|t|\leq T}\ \| e^{tJ\nabla (H_\text{KdV} - H_\kappa)} q - q \|_{H^{-1}} =0. \tag{5.5}
$$

We prove (5.5) by considering the reciprocal of the diagonal Green's function at some fixed energy.  To this end, we fix $\varkappa\geq 1$ and adopt the following notations: given $q\in Q^*$ and $\kappa\geq \varkappa +1$,

$$
q(t) := e^{tJ\nabla (H_\text{KdV} - H_\kappa)} q \quad\text{and}\quad  g(t,x;\varkappa) := g(x;\varkappa,q(t)).
$$

Note that $q(t)\in (Q^*)^*=Q^*$ for any $t\in\mathbb{R}$.

Combining (3.6) and (3.12), we obtain

$$
\begin{aligned}
\tfrac{d\ }{dt}  \tfrac{1}{2g(t,x;\varkappa)} &= \Bigl\{ \tfrac{1}{g(t,x;\varkappa)} \Bigl( q(t,x) + \tfrac{4\kappa^5}{\kappa^2-\varkappa^2}\bigl[g(t,x;\kappa)-\tfrac{1}{2\kappa}\bigr]  -   \tfrac{4\varkappa^5}{\kappa^2-\varkappa^2} \bigl[ g(t,x;\varkappa) -\tfrac{1}{2\varkappa}\bigr]\Bigr)\Bigr\}'
\end{aligned}
$$

and thence

$$
\begin{aligned}
\bigl\| \tfrac{d\ }{dt} \bigl(\varkappa - \tfrac{1}{2g(t;\varkappa)}\bigr) \bigr\|_{H^{-2}}
&\lesssim \bigl\| q(t,x) + 4\kappa^3\bigl[g(t,x;\kappa)-\tfrac{1}{2\kappa}\bigr]\bigr\|_{H^{-1}} \\
&\quad \ {} + \kappa \bigl\| g(t,x;\kappa)-\tfrac{1}{2\kappa}\bigr\|_{H^{-1}}  + \kappa^{-2} \bigl\| g(t,x;\varkappa)-\tfrac{1}{2\varkappa}\bigr\|_{H^{-1}}
\end{aligned}
$$

uniformly for $q\in Q^*$ and $\kappa\geq \varkappa+1$.  (The implicit constants here depend on $\varkappa$.)  But then, by the fundamental theorem of calculus and Proposition 4.4,

$$
\lim_{\kappa\to\infty}\; \sup_{q\in Q^*}\ \sup_{|t|\leq T}\ \bigl\| \tfrac{1}{2g(t;\varkappa)} - \tfrac{1}{2g(0;\varkappa)} \bigr\|_{H^{-2}} =0. \tag{5.6}
$$

In view of Lemma 4.2(ii), we may upgrade this convergence to

$$
\lim_{\kappa\to\infty} \; \sup_{q\in Q^*} \ \sup_{|t|\leq T}\ \bigl\| \tfrac{1}{2g(t;\varkappa)} - \tfrac{1}{2g(0;\varkappa)} \bigr\|_{H^{1}} =0, \tag{5.7}
$$

due to the equicontinuity of the set

$$
E:= \Bigl\{ \varkappa - \tfrac{1}{2g(x;\varkappa,q(t))} \in H^1(\mathbb{R}) : q\in Q^* \text{ and } t\in\mathbb{R}\Bigr\}
$$

in $H^1(\mathbb{R})$.  This property of $E$ holds because, by the diffeomorphism property and the relation (2.13), it is equivalent to equicontinuity of $Q^*$.

Lastly, the diffeomorphism property shows that (5.7) implies (5.5) and so completes the proof of Theorem 5.1.
 $\square$

The line case of Theorem 1.1 follows from the next corollary.  We then extend this to higher values of $s$.

**Corollary 5.2.**
The KdV equation is globally well-posed in $H^{-1}(\mathbb{R})$ in the following sense:  The solution map extends (uniquely) from Schwartz space to a jointly continuous map

$$
\Phi:\mathbb{R}\times H^{-1}(\mathbb{R})\to H^{-1}(\mathbb{R}).
$$

In particular, $\Phi$ has the group property: $\Phi(t+s)=\Phi(t)\circ \Phi(s)$.  Moreover, each orbit $\{\Phi(t,q) : t\in\mathbb{R}\}$ is bounded and equicontinuous in $H^{-1}(\mathbb{R})$.  Concretely,

$$
\sup_t \| q(t) \|_{H^{-1}(\mathbb{R})} \lesssim \| q(0) \|_{H^{-1}(\mathbb{R})}  + \| q(0) \|_{H^{-1}(\mathbb{R})}^3 . \tag{5.8}
$$

*Proof.*
Given $q\in H^{-1}(\mathbb{R})$, we may define $\Phi(t,q)$ by choosing some sequence of Schwartz solutions $q_n(t)$ with $q_n(0)\to q$ in $H^{-1}(\mathbb{R})$ and then set

$$
\Phi(t,q)= \lim_{n\to\infty} q_n(t).
$$

By virtue of Theorem 5.1, this limit exists in $H^{-1}(\mathbb{R})$,  it is independent of the sequence $q_n$, and the convergence is uniform on compact intervals of time.

Now consider a sequence $q_n\to q \in H^{-1}(\mathbb{R})$ and fix $T>0$.  Theorem 5.1 guarantees that there is a sequence of Schwartz solutions $\tilde q_n$ so that

$$
\sup_{|t|\leq T} \| \tilde q_n(t) - \Phi(t,q_n) \|_{H^{-1}} \to 0 \quad\text{as $n\to\infty$.}\quad
$$

But then $\tilde q_n(0) \to q$ in $H^{-1}$ and so Theorem 5.1 implies

$$
\sup_{|t|\leq T} \| \tilde q_n(t) - \Phi(t,q) \|_{H^{-1}} \to 0 \quad\text{as $n\to\infty$.}\quad
$$

As each $\tilde q_n(t)$ is itself $H^{-1}(\mathbb{R})$-continuous in time, this proves joint continuity of $\Phi$.

As $\Phi$ is continuous, the group property on $H^{-1}(\mathbb{R})$ is inherited from that on Schwartz space.

For small initial data, boundedness and equicontinuity of orbits follows from conservation of $\alpha(\kappa)$, (2.20), and Lemma 4.3.  In fact, this argument shows that

$$
\sup_t \| q(t) \|_{H^{-1}(\mathbb{R})} \lesssim \| q(0) \|_{H^{-1}(\mathbb{R})} \quad\text{for}\quad  q(0)\in B_\delta
$$

and $\delta>0$ sufficiently small.  Equicontinuity and (5.8) for large data then follow from the scaling transformation (5.1).
 $\square$

**Corollary 5.3.**
The KdV equation is globally well-posed in $H^{s}(\mathbb{R})$ for all $s\geq -1$.

*Proof.*
In view of the preceding, it suffices to prove an analogue of Theorem 5.1 in $H^s(\mathbb{R})$.  We shall content ourselves with the treatment of $s\in(-1,0)$ here, since we may do so in a simple and uniform manner; moreover, together with Corollary 5.2, this covers all cases not previously known, namely, $s\in[-1,-\tfrac34)$.

Given Schwartz solutions $q_n(t)$ to (KdV) with $q_n(0)$ convergent in $H^{s}(\mathbb{R})$ and $T>0$, we may apply Theorem 5.1 to obtain convergence of $q_n(t)$ in $H^{-1}(\mathbb{R})$, uniformly for $t\in[-T,T]$.  The goal is to upgrade this to uniform convergence in $H^s(\mathbb{R})$.  In view of Lemma 4.2, this amounts to demonstrating $H^s(\mathbb{R})$-equicontinuity of the set $\{q_n(t):n\in\mathbb{N}\text{ and } t\in[-T,T]\}$.

To prove equicontinuity, we employ the following trick we used in [41]:  Integrating both sides of (2.20) against the measure $\kappa^{2+2s} \,d\kappa$ over the interval $[\kappa_0,\infty)$, we obtain

$$
\int_{\kappa_0}^\infty \alpha(\kappa;q) \kappa^{2+2s} \,d\kappa \approx \int |\hat q(\xi)|^2 (\xi^2+4\kappa_0^2)^s \,d\xi, \tag{5.9}
$$

where the implicit constants depend only on $s$.  Notice that LHS(5.9) is conserved by the flow and so, it follows that

$$
\int |\hat q_n(t,\xi)|^2 (\xi^2+4\kappa_0^2)^s \,d\xi \approx \int |\hat q_n(0,\xi)|^2 (\xi^2+4\kappa_0^2)^s \,d\xi \tag{5.10}
$$

uniformly for $n\in\mathbb{N}$ and $t\in\mathbb{R}$.  As the initial data $q_n(0)$ are $H^s(\mathbb{R})$-convergent, they are $H^s(\mathbb{R})$-equicontinuous and so RHS(5.10) converges to zero as $\kappa_0\to\infty$ uniformly in $n$.  But then LHS(5.10) converges to zero as $\kappa_0\to\infty$ uniformly in $n$, thus proving equicontinuity of $\{q_n(t) : n\in\mathbb{N}\text{ and } t\in\mathbb{R}\}$.
 $\square$

## 6. The periodic case

With the exception of Section 2, very little of substance changes in carrying over the arguments presented so far to the case of KdV with initial data in $H^{-1}(\mathbb{R}/\mathbb{Z})$.  Nevertheless, there are several reasons why we chose not to present both geometries simultaneously (as in our prior work [41]).  First and foremost, we avoid the necessity of continually interrupting the principal line of reasoning to discuss minor changes (often notational) associated to the two geometries.

Secondly, in the non-periodic setting, the scaling transformation (5.1) allows us effortlessly to focus attention on small solutions, which manifests in the appearance of $\delta$ throughout our arguments thus far.  To overcome the lack of scaling-invariance in the periodic case, we follow the approach we used in [41].  Although we still maintain that this is the best solution, we can attest that it burdens the exposition considerably.  Looking to (5.2) and (5.3), we see that rescaling $q$ transforms the parameter $\kappa$. Correspondingly, the smallness condition for $q$ can be replaced by a relation involving $\kappa$ and $q$.  On the other hand, many formulas become tremendously ugly if we do not employ the simplifications made possible by requiring $\kappa\geq 1$.  This reasoning leads to the following *coupled* conditions on $q$ and $\kappa$ that we shall impose:

$$
\kappa\geq 1 \quad\text{and}\quad  \kappa^{-1/2} \| q \|_{H^{-1}(\mathbb{R}/\mathbb{Z})} \leq \delta. \tag{6.1}
$$

Here $\delta>0$ remains our over-arching smallness parameter, whose value will be allowed to shrink as the argument progresses.  Concomitant with this, for fixed $\kappa\geq 1$, we define

$$
B_{\delta,\kappa} := \{ q\in H^{-1}(\mathbb{R}/\mathbb{Z}) : \kappa^{-1/2} \| q \|_{H^{-1}(\mathbb{R}/\mathbb{Z})} \leq \delta\bigr\}. \tag{6.2}
$$

To make the arguments as parallel as possible, we shall insist on working with a Lax operator

$$
L = -\partial_x^2 + q(x)
$$

(and its resolvent) acting on $L^2(\mathbb{R})$ with periodic coefficients and *not* as an operator on $L^2(\mathbb{R}/\mathbb{Z})$.  This deviates from our treatment in [41].

In light of our convention, $L$ is no longer a relatively Hilbert–Schmidt (or even relatively compact) perturbation of the case $q\equiv 0$.  As many arguments in Section 2 were founded on (2.4), which is the quantitative expression of this, those arguments do not automatically carry over to the periodic case.  In Lemma 6.1 we obtain the key substitute for (2.4).  We will then show how to use this to obtain the analogues of the results from Section 2 in the periodic setting.

By comparison, Section 3 is almost devoid of estimates (and those that do appear are easily adapted).  Rather, it is preoccupied with identities that hold pointwise in space and so are immune to the ambient geometry.

Once we have proved (6.10) below, everything in Section 4 carries over by simply replacing every instance of integration with respect to $\xi$ by summation over $\xi\in2\pi\mathbb{Z}$.

The principal difficulty in transferring the proof of Theorem 5.1 to the circle case is the absence of the scaling symmetry (5.1); we have already explained how this can be avoided.  The only change needed for the treatment of the remaining results in Section 5, namely, Corollaries 5.2 and 5.3, is to employ (6.10) whenever the original argument calls on (2.20).

Let us turn now to the central matter at hand, namely, obtaining analogues of the principal results of Section 2 in the periodic setting.

**Lemma 6.1.**
Fix $\psi\in C^\infty_c(\mathbb{R})$.  If $q,f\in H^{-1}(\mathbb{R}/\mathbb{Z})$, then

$$
\begin{aligned}
\bigl\| \sqrt{R_0}\,q \sqrt{R_0} \bigr\|_{L^2(\mathbb{R})\to L^2(\mathbb{R})}^2 &\lesssim \kappa^{-1} \sum_{\xi\in2\pi\mathbb{Z}} \frac{|\hat q(\xi)|^2}{\xi^2+4\kappa^2}, \qquad\text{(6.3)} \\
\bigl\| \sqrt{R_0}\, f\psi R_0 q \sqrt{R_0} \bigr\|_{\mathfrak{I}_1(L^2(\mathbb{R}))} &\lesssim \kappa^{-1} \| f \|_{H^{-1}_\kappa(\mathbb{R}/\mathbb{Z})} \| q \|_{H^{-1}_\kappa(\mathbb{R}/\mathbb{Z})}, \qquad\text{(6.4)}
\end{aligned}
$$

both uniformly for $\kappa\geq 1$.

Note that $\mathfrak{I}_1(L^2(\mathbb{R}))$ denotes the ideal of trace-class operators acting on the Hilbert space $L^2(\mathbb{R})$.  Here and below, we simply use trace-class as a notational convenience for denoting operators representable as a product of Hilbert–Schmidt operators:

$$
\| B \|_{\mathfrak{I}_1} = \inf \bigl\{ \|B_1\|_{\mathfrak{I}_2}\|B_1\|_{\mathfrak{I}_2} : B = B_1 B_2 \bigr\} . \tag{6.5}
$$

For a proper discussion of trace-class, including the veracity of (6.5), see [62].

Before beginning the proof of Lemma 6.1, we describe one more preliminary: Given $f\in L^2(\mathbb{R})$ and $\theta\in[0,2\pi]$, we define

$$
f_\theta(x) = \sum_{\xi\in2\pi\mathbb{Z}} \hat f(\xi+\theta) e^{ix(\xi+\theta)},
$$

which may be regarded as a jointly square-integrable function of $x\in[0,1]$ and $\theta\in[0,2\pi]$.  Indeed,

$$
\int_{\mathbb{R}} |f(x)|^2\,dx = \int_0^{2\pi} \| f_\theta\|_{L^2([0,1])}^2\,d\theta.
$$

Moreover, any (pseudo)differential operator $L$ with $1$-periodic coefficients acts fibre-wise, which is to say it commutes with multiplication by any function of $\theta$.  Note that what we describe here is simply the standard direct integral representation of a periodic operator (cf. [59, § XIII.16]).

*Proof of Lemma 6.1.*
As the operator appearing in (6.3) is self-adjoint, it suffices to take $f\in L^2(\mathbb{R})$ and consider

$$
\langle f, \sqrt{R_0} q \sqrt{R_0} \,f\rangle_{L^2} = \int_0^{2\pi} \langle f_\theta, \mathcal{M}_\theta q \mathcal{M}_\theta f_\theta \rangle\,d\theta,
$$

where $\mathcal{M}_\theta :L^2([0,1])\to L^2([0,1])$ is defined via

$$
\mathcal{M}_\theta  : \sum_{\xi\in2\pi\mathbb{Z}} c_\xi e^{ix(\xi+\theta)} \mapsto \sum_{\xi\in2\pi\mathbb{Z}} \frac{c_\xi e^{ix(\xi+\theta)}}{\sqrt{(\xi+\theta)^2+\kappa^2}}.
$$

In this way, we see that

$$
\| \sqrt{R_0} q \sqrt{R_0} \|_{L^2(\mathbb{R})\to L^2(\mathbb{R})}  = \bigl\| \| \mathcal{M}_\theta q \mathcal{M}_\theta \|_{L^2([0,1])\to L^2([0,1])} \bigr\|_{L^\infty_\theta}.
$$

The estimate (6.3) now follows by bounding operator norms by Hilbert–Schmidt norms and the equivalence

$$
\| \mathcal{M}_\theta q \mathcal{M}_\theta \|_{\mathfrak{I}_2(L^2([0,1]))}^2  \approx \kappa^{-1} \sum_{\xi\in2\pi\mathbb{Z}} \frac{|\hat q(\xi)|^2}{\xi^2+4\kappa^2}, \tag{6.6}
$$

which is valid uniformly for $\theta\in[0,2\pi)$.

We turn now to (6.4). From (2.15), we find

$$
\begin{aligned}
\sqrt{R_0}\, f\psi R_0 q \sqrt{R_0}\, &= \sqrt{R_0}\, f\psi\langle x\rangle R_0 \langle x\rangle^{-1} q \sqrt{R_0}
	+ \sqrt{R_0}\, f\psi \sqrt{R_0}\, A \sqrt{R_0}\, \langle x\rangle^{-1} q \sqrt{R_0} \\
\text{with}\quad A &= \sqrt{R_0}\, \bigl(\tfrac{x}{\langle x\rangle} \partial_x + \partial_x\tfrac{x}{\langle x\rangle}\bigr) \sqrt{R_0}\,.
\end{aligned}
$$

Evidently, $A$ is an $L^2(\mathbb{R})$-bounded operator.  From (2.4) we obtain

$$
\begin{aligned}
\bigl\| \sqrt{R_0}\, \langle x\rangle^{-1} q \sqrt{R_0} \bigr\|_{\mathfrak{I}_2(L^2(\mathbb{R}))}
	&\lesssim \kappa^{-1/2} \bigl\| \langle x\rangle^{-1} q \bigr\|_{H^{-1}_\kappa(\mathbb{R})} \lesssim \kappa^{-1/2} \bigl\| q \bigr\|_{H^{-1}_\kappa(\mathbb{R}/\mathbb{Z})}
\end{aligned}
$$

and similarly,

$$
\bigl\| \sqrt{R_0}\, f\psi \sqrt{R_0} \bigr\|_{\mathfrak{I}_2(L^2(\mathbb{R}))} + \bigl\| \sqrt{R_0}\, f\psi\langle x\rangle\sqrt{R_0} \bigr\|_{\mathfrak{I}_2(L^2(\mathbb{R}))}
\lesssim \kappa^{-1/2} \bigl\| f \bigr\|_{H^{-1}_\kappa(\mathbb{R}/\mathbb{Z})}.
$$

Combining the preceding immediately yields (6.4).
 $\square$

**Proposition 6.2.**
Let $q\in H^{-1}(\mathbb{R}/\mathbb{Z})$.  There is a unique self-adjoint operator $L$ acting on $L^2(\mathbb{R})$ associated to the semi-bounded quadratic form

$$
\psi \mapsto \int_{\mathbb{R}} |\psi'(x)|^2 + q(x) |\psi(x)|^2\,dx .
$$

Furthermore, there exists $\delta>0$, so that if $q$ and $\kappa$ obey (6.1), then the resolvent $R:=(L+\kappa^2)^{-1}$ admits a continuous integral kernel $G(x,y;\kappa,q)$ given by the uniformly convergent series

$$
G(x,y;\kappa, q) = \tfrac{1}{2\kappa} e^{-\kappa|x-y|} + \sum_{\ell=1}^\infty (-1)^\ell \Bigl\langle \sqrt{R_0}\, \delta_x, \Bigl(\!\sqrt{R_0}\,q \sqrt{R_0}\Bigr)^\ell \sqrt{R_0}\,\delta_y\Bigr\rangle. \tag{6.7}
$$

*Proof.*
Regarding the existence and uniqueness of $L$, we note that (6.3) guarantees that $q$ is an infinitesimally form bounded perturbation and then apply [58, Theorem X.17].  This is the same argument used in the proof of Proposition 2.1.

Using Plancherel, it is easy to check that $x\mapsto \sqrt{R_0}\delta_x$ is Hölder-continuous as a map from $\mathbb{R}$ to $L^2(\mathbb{R})$.  Thus, convergence of the series (6.7) and continuity of the result follows whenever
$\sqrt{R_0}\,q \sqrt{R_0}$ is a contraction; this in turn follows from (6.1) and (6.3) when $\delta$ is small enough.
 $\square$

We define $g(x;\kappa,q)$ and $\rho(x;\kappa,q)$ exactly as in Section 2; see (2.5) and (2.18).  Let us now demonstrate their basic properties:

**Proposition 6.3.**
There exists $\delta>0$, so that the following are true for all $\kappa\geq 1:$

(i) The mappings

$$
q\mapsto g-\tfrac1{2\kappa} \quad\text{and}\quad  q\mapsto \kappa-\tfrac1{2g} \tag{6.8}
$$

are (real analytic) diffeomorphisms of $B_{\delta,\kappa}$ into $H^1(\mathbb{R}/\mathbb{Z})$.

(ii) For every $q\in B_{\delta,\kappa}$ and every integer $s\geq 0$,

$$
\|g'(x)\|_{H^{s}(\mathbb{R}/\mathbb{Z})}  \lesssim_s \| q \|_{H^{s-1}(\mathbb{R}/\mathbb{Z})} . \tag{6.9}
$$

(iii) For every $q\in B_{\delta,\kappa}$, $\rho(x;q)$ is non-negative and in $H^1(\mathbb{R}/\mathbb{Z})$. Moreover,

$$
\alpha(\kappa,q):=\int_0^1 \rho(x)\,dx \approx \kappa^{-1} \sum_{\xi\in 2\pi\mathbb{Z}} \frac{|\hat q(\xi)|^2}{\xi^2+4\kappa^2}, \tag{6.10}
$$

uniformly for $\kappa\geq 1$ and $q\in B_{\delta,\kappa}$.

*Proof.*
First we show that $g\in H^{1}(\mathbb{R}/\mathbb{Z})$.  That it is periodic is self-evident from (6.7). To estimate its norm, we pick $\psi\in C^\infty_c(\mathbb{R})$ so that

$$
\sum_{k\in\mathbb{Z}} \psi(x-k) \equiv 1.
$$

The utility of this partition of unity for us stems from the duality relation

$$
\| h \|_{H^{1}_\kappa(\mathbb{R}/\mathbb{Z})} = \sup \biggl\{ \int_\mathbb{R} h(x) \psi(x) f(x)\,dx : f\in C^\infty(\mathbb{R}/\mathbb{Z}) \text{ and }\|f\|_{H^{-1}_\kappa(\mathbb{R}/\mathbb{Z})}\leq 1\biggr\}.
$$

Now given $f\in C^\infty(\mathbb{R}/\mathbb{Z})$, from (6.7) we obtain that

$$
\int \bigl[g(x) -\tfrac1{2\kappa}\bigr] \psi(x) f(x) \,dx = \sum_{\ell=1}^\infty (-1)^\ell \operatorname{tr}\Bigl\{ \!\sqrt{R_0}\,f\psi \sqrt{R_0} \Bigl(\!\sqrt{R_0}\,q \sqrt{R_0}\Bigr)^\ell \Bigr\} \tag{6.11}
$$

and thence, using (6.4), (6.3), and (6.2),

$$
\bigl\|g(x) -\tfrac1{2\kappa}\bigr\|_{H^1(\mathbb{R}/\mathbb{Z})} \lesssim \kappa^{-1} \|q\|_{H^{-1}(\mathbb{R}/\mathbb{Z})}, \tag{6.12}
$$

provided $\delta$ is chosen sufficiently small.  Moreover, this argument shows that the first mapping in (6.8) is real-analytic by directly proving convergence of the power series.

When combined with (2.13), the estimates just presented also lead to a proof of (6.9); for further details see the proof of Proposition 2.2.

We consider now the inverse mapping.  As in Section 2,

$$
\kappa \cdot dg\bigr|_{q\equiv 0} = - R_0(2\kappa)
$$

is a unitary map of $H^{-1}_\kappa(\mathbb{R}/\mathbb{Z})$ onto $H^1_\kappa(\mathbb{R}/\mathbb{Z})$.  Thus, by the inverse function theorem, $q\mapsto g-\tfrac1{2\kappa}$ is a diffeomorphism in some neighbourhood of zero.  We must verify that the inverse mapping extends to the whole of $B_{\delta,\kappa}$.  Differentiating (6.11) with respect to $q$ and applying (6.3) and (6.4) yields

$$
\Bigl\| dg -dg\bigr|_{q\equiv0} \Bigr\|_{H^{-1}_\kappa\to H^{\vphantom{+}1}_\kappa}  \lesssim \kappa^{-3/2} \|q\|_{H^{-1}(\mathbb{R}/\mathbb{Z})}, \tag{6.13}
$$

which suffices for this task.

The diffeomorphism property extends from the first map in (6.8) to the second by exactly the same argument presented in the proof of Proposition 2.2.

We turn now to part (iii), focussing on (6.10).  As previously, we proceed by computing derivatives, beginning with

$$
\frac{d\ }{ds}\biggr|_{s=0} \int_0^1 \frac{dy}{2g(y;q+sf)} = \int_0^1 g(x) f(x)\,dx. \tag{6.14}
$$

This may be proved as follows: By the resolvent identity, periodicity, and Lemma 2.5,

$$
\begin{aligned}
\text{LHS(6.14)} &= \int_0^1 \int_\mathbb{R} \frac{G(y,x)f(x)G(x,y)}{2g(y)^2}\,dx\,dy \\
&= \sum_{k\in\mathbb{Z}} \int_0^1 \int_0^1 \frac{G(y,x+k)f(x+k)G(x+k,y)}{2g(y)^2}\,dx\,dy \\
&= \sum_{k\in\mathbb{Z}} \int_0^1 \int_0^1 \frac{G(y-k,x)f(x)G(x,y-k)}{2g(y-k)^2}\,dx\,dy \\
&= \int_0^1 \int_\mathbb{R} \frac{G(y,x)G(x,y)}{2g(y)^2}\,dy\,f(x)\,dx = \text{RHS(6.14)}.
\end{aligned}
$$

Beginning with (6.14) and using (2.10) shows

$$
\begin{aligned}
d^2\alpha\bigr|_{q\equiv 0} (f,f) &= \tfrac{1}{4\kappa^2} \int_0^1 \!\! \int_\mathbb{R} e^{-2\kappa|y-z|} f(y) f(z) \,dy\,dz
	= \tfrac{1}{\kappa} \sum_{\xi\in 2\pi\mathbb{Z}} \frac{|\hat f(\xi)|^2}{\xi^2+4\kappa^2}.
\end{aligned}
$$

Relying also on (6.13) yields

$$
\begin{aligned}
\Bigl| d^2\alpha(f,f) - d^2\alpha\bigr|_{q\equiv 0} (f,f)\Bigr| & \lesssim \kappa^{-3/2} \|q\|_{H^{-1}(\mathbb{R}/\mathbb{Z})} \|f\|_{H^{-1}_\kappa(\mathbb{R}/\mathbb{Z})}^2.
\end{aligned}
$$

In this way, we see that the power series expansion of $\alpha$ as a function of $q$ is dominated by its quadratic term throughout (6.2), thus proving (6.10).
 $\square$

Proposition 6.3 contains no analogue of (2.21).  Unlike in the decaying case, the quantity defined in (6.10) does not coincide precisely with the renormalized perturbation determinant considered in [41].  To describe the connection, we must introduce several new objects.  Henceforth, we consider only $q\in C^\infty(\mathbb{R}/\mathbb{Z})$.  Once we have established suitable identities in this setting, they may be extended via analyticity to $q$ that are merely $H^{-1}(\mathbb{R}/\mathbb{Z})$.

Let $\mathcal{R}_0$ denote the resolvent associated to the Laplacian on $[0,1]$ with periodic boundary conditions; concretely,

$$
\mathcal{R}_0 : \sum_{\xi\in2\pi\mathbb{Z}} c_\xi e^{i\xi x} \mapsto \sum_{\xi\in2\pi\mathbb{Z}} \frac{c_\xi e^{i\xi x}}{\xi^2 + \kappa^2}.
$$

Note that this coincides with $\mathcal{M}_0^2$ where $\mathcal{M}_0$ is as in the proof of (6.3).  Using (6.6), we see that the resolvent of the operator $\mathcal{L}=-\partial_x^2+q$, acting on $L^2([0,1])$ with periodic boundary conditions, can be expanded in a convergent series

$$
\mathcal{R} = \mathcal{R}_0 + \sum_{\ell=1}^\infty (-1)^\ell \sqrt{\mathcal{R}_0} \left(\sqrt{\mathcal{R}_0}\, q \, \sqrt{\mathcal{R}_0}\right)^\ell \sqrt{\mathcal{R}_0}
$$

whenever $\kappa$ and $q$ satisfy (6.1) for suitable $\delta>0$.  Moreover, the kernels of these operators can be found by the method of images:

$$
\langle \delta_x, \mathcal{R}_0\delta_y\rangle = \sum_{k\in\mathbb{Z}} \langle \delta_x, R_0\delta_{y+k}\rangle =  \tfrac{1}{2\kappa(1-e^{-\kappa})} \bigl[ e^{-\kappa\|x-y\|} + e^{-\kappa(1-\|x-y\|)} \bigr], \tag{6.15}
$$

where $\|x-y\|=\operatorname{dist}(x-y,\mathbb{Z})$, and similarly,

$$
\mathcal G(x,y) := \langle \delta_x, \mathcal{R} \delta_y\rangle = \sum_{k\in\mathbb{Z}} G(x,y+k). \tag{6.16}
$$

The last object we need to define is the Lyapunov exponent.  Let $\psi_\pm(x;\kappa)$ be the Weyl solutions introduced earlier in this section.  Due to the periodicity of $q$, we see that $x\mapsto\psi_+(x+1)$ and $x\mapsto\psi_-(x+1)$ constitute equally good Weyl solutions and so must differ from the originals by numerical constants.  Noting the constancy of the Wronskian as well as the square-integrability constraint, we see
that there is a $\gamma=\gamma(\kappa)>0$ so that

$$
\psi_+(x+1;\kappa) = e^{-\gamma(\kappa)} \psi_+(x;\kappa) \quad\text{and}\quad  \psi_-(x+1;\kappa) = e^{+\gamma(\kappa)} \psi_-(x;\kappa).
$$

This quantity $\gamma$ is known as the Lyapunov exponent.  Employing these relations to sum in (6.16), we deduce that

$$
\mathcal G(x,x) = \frac{1+e^{-\gamma}}{1-e^{-\gamma}} G(x,x). \tag{6.17}
$$

**Proposition 6.4.**   For $q\in C^\infty(\mathbb{R}/\mathbb{Z})$ and $\kappa$ satisfying (6.1), we have

$$
\gamma(\kappa) = \int_0^1 \frac{dx}{2g(x)}, \tag{6.18}
$$

$$
\operatorname{tr}\left(\sqrt{\mathcal{R}_0}\, q \, \sqrt{\mathcal{R}_0} \right) = \tfrac{1+e^{-\kappa}}{1-e^{-\kappa}}  \int_0^1  \bigl[\tfrac{1}{2} e^{-2\kappa|\cdot|}*q\bigr](x) \,dx
    = \tfrac1{2\kappa}\,\tfrac{1+e^{-\kappa}}{1-e^{-\kappa}} \int_0^1  q(x) \,dx, \tag{6.19}
$$

which is a Casimir, and

$$
\log\det\left( 1 + \sqrt{\mathcal{R}_0}\, q \, \sqrt{\mathcal{R}_0} \right) = \log\bigl(e^{\gamma} - 2 + e^{-\gamma} \bigr) - \log\bigl(e^{\kappa} - 2 + e^{-\kappa} \bigr). \tag{6.20}
$$

Here the trace and determinant are with respect to the Hilbert space $L^2(\mathbb{R}/\mathbb{Z})$.

*Proof.*
The proof of (6.18) is very simple: combining $g(x)=\psi_+(x)\psi_-(x)$ with the Wronskian relation (2.25), we have

$$
\int_0^1 \frac{dx}{2g(x)} = \tfrac12 \int_0^1 \frac{d }{dx} \log\Bigl[\tfrac{\psi_-(x)}{\psi_+(x)}\Bigr]\,dx = \tfrac12 \log\Bigl[\tfrac{\psi_-(x+1)\psi_+(x)}{\psi_-(x)\psi_+(x+1)}\Bigr] = \gamma.
$$

By (6.15), we have

$$
\operatorname{tr}\Bigl\{ \sqrt{\mathcal{R}_0}\, q \, \sqrt{\mathcal{R}_0} \Bigr\} = \frac{(1+e^{-\kappa})}{2\kappa(1-e^{-\kappa})} \int_0^1 q(x)\,dx,
$$

while

$$
\begin{aligned}
\int_0^1\int_\mathbb{R} \tfrac{1}{2} e^{-2\kappa|x-y|} q(y)\,dy\,dx &= \sum_{k\in\mathbb{Z}} \int_0^1\int_0^1 \tfrac{1}{2} e^{-2\kappa|x-k-y|} q(y)\,dy\,dx \\
&= \int_0^1\int_\mathbb{R} \tfrac{1}{2} e^{-2\kappa|x-y|} q(y) \,dx\,dy = \tfrac{1}{2\kappa} \int_0^1 q(y)\,dy.
\end{aligned}
$$

This proves (6.19).

The identity (6.20) can be readily deduced from [47, Theorem 2.9], which is a recapitulation of venerable results of Hill and of Wittaker and Watson.  For completeness, we given an alternate proof paralleling our arguments from the rapidly decreasing case.

By (6.18), we see that (6.20) holds in the case $q\equiv 0$.  Moreover, arguing as in the decaying case, we find that for any $f\in C^\infty(\mathbb{R}/\mathbb{Z})$,

$$
\frac{d\ }{ds}\biggr|_{s=0} \log\det\left( 1 + \sqrt{\mathcal{R}_0}\, (q+sf) \, \sqrt{\mathcal{R}_0} \right) (x) = \int_0^1 \mathcal G(x,x) f(x)\,dx.
$$

On the other hand, by (6.18) and (6.14),

$$
\frac{d\ }{ds}\biggr|_{s=0} \log\bigl(e^{\gamma(\kappa;q+sf)} - 2 + e^{-\gamma(\kappa;q+sf)} \bigr) = \frac{e^\gamma-e^{-\gamma}}{(e^{\gamma} - 2 + e^{-\gamma})}\int_0^1 g(x) f(x)\,dx.
$$

In view of (6.17), these two derivatives agree.  Thus equality in (6.20) extends to all $q\in B_{\delta,\kappa}$.
 $\square$

**Corollary 6.5.**   For smooth initial data, the conservation of

$$
\int_0^1 \rho(x)\,dx
$$

under the KdV flow, which follows from (3.7), is equivalent to conservation of

$$
-\log\det_2\left( 1 + \sqrt{\mathcal{R}_0}\, q \, \sqrt{\mathcal{R}_0} \right),
$$

which was proved in [41].

## 7. Local smoothing

Our first goal in this section is to derive a local smoothing result for $H^{-1}$-solutions to (KdV) on the line.  A similar a priori estimate was obtained by Buckmaster and Koch in [8] via the Miura map.

**Lemma 7.1 (Local smoothing).**
There exists $\delta>0$ so that for every $H^{-1}(\mathbb{R})$-solution $q(t)$ to (KdV), in the sense of Corollary 5.2, with initial data $q(0)\in B_\delta$,

$$
\sup_{t_0,x_0\in\mathbb{R}} \ \int_{0}^{1} \!\! \int_{0}^{1} |q(t-t_0,x-x_0)|^2 \,dx\,dt \lesssim \delta^2. \tag{7.1}
$$

*Proof.*
As noted already in Proposition 3.1, conservation of $\alpha(\kappa=1)$ guarantees that

$$
\| q \|_{L^\infty_x H^{-1}_x} ^2 \lesssim \delta^2.
$$

This allows us to choose $\delta$ sufficiently small that all results from Section 3 can be applied at all times $t\in\mathbb{R}$.
It also means that it suffices to prove (7.1) with $t_0=x_0=0$.

Let us now fix a smooth function $\phi$ whose derivative $\phi'$ is positive and Schwartz and define

$$
\psi(x) = \tfrac32 \int_\mathbb{R} e^{-2|x-y|} \phi'(y) \,dy,
$$

which is positive everywhere.

Suppose first that $q(t)$ is a Schwartz solution to (KdV).  Setting $\kappa=1$ in (3.7), we obtain

$$
\begin{aligned}
\tfrac{d\ }{dt}  \rho(t,x) &= \Bigl( \tfrac32 \bigl[e^{-2|\cdot|}* q(t)^2\bigr](x)  + 2q(t,x)\bigl[ 1 - \tfrac{1}{2g(t,x)}\bigr] - 4\rho(t,x) \Bigr)'.
\end{aligned}
$$

Integrating this against $\phi(x)$ and integrating by parts, yields

$$
\begin{aligned}
\int_0^1 \! \int_\mathbb{R} |q(t,x)|^2 \psi(x) \,dx\,dt &= \int_\mathbb{R} [\rho(0,x)-\rho(1,x)] \phi(x) \,dx \\
&\quad - 2 \int_0^1 \! \int_\mathbb{R} q(t,x)\bigl[ 1 - \tfrac{1}{2g(t,x)}\bigr] \phi'(x) \,dx\,dt \\
&\quad + 4 \int_0^1 \! \int_\mathbb{R} \rho(t,x) \phi'(x) \,dx\,dt .
\end{aligned} \tag{7.2}
$$

But by the results of Section 3, the right-hand side is bounded uniformly;  thus (7.1) follows for Schwartz solutions.

Next we allow $q(t)$ to be a general (not Schwartz) solution to (KdV) and suppose $q_n(t)$ is a sequence of Schwartz solutions with $q_n(0)\to q(0)$ in $H^{-1}(\mathbb{R})$.  By weak lower-semicontinuity of the $L^2$-norm and the fact that weak convergence is guaranteed by Theorem 5.1,

$$
\int_{0}^{1} \int_{0}^{1} |q(t,x)|^2 \,dx\,dt \leq \liminf_{n\to\infty} \int_{0}^{1} \int_0^1 |q_n(t,x)|^2 \,dx\,dt.
$$

Thus, (7.1) for such general solutions $q(t)$ follows from the Schwartz-class case already proven.
 $\square$

Using this a priori bound as a stepping stone, we will now show that solutions whose initial data converge in $H^{-1}(\mathbb{R})$ actually converge in the local smoothing norm as claimed in Theorem 1.2.  In fact, the following proposition is strictly stronger than this theorem because of the additional uniformity in $x_0$.

**Proposition 7.2.**
Let $q(t)$ and $q_n(t)$ be $H^{-1}(\mathbb{R})$-solutions to (KdV), in the sense of Corollary 5.2, with initial data $q_n(0)\to q(0)$ in $H^{-1}(\mathbb{R})$.  Then for every $T>0$,

$$
\lim_{n\to\infty} \ \sup_{x_0\in\mathbb{R}} \ \int_{-T}^T \int_0^1 |q(t,x-x_0)-q_n(t,x-x_0)|^2 \,dx\,dt  = 0. \tag{7.3}
$$

In particular, solutions in the sense of Corollary 5.2 are distributional solutions.

A major part of the argument leading to Proposition 7.2 is a refinement of the proof of Lemma 7.1. The key improvement stems from analyzing the behavior of the various terms in (7.2) as $\kappa\to\infty$, rather than simply setting $\kappa=1$.  We begin with the following preliminary estimates:

**Lemma 7.3.**
Fix $\psi\in C^\infty_c(\mathbb{R})$ with $\operatorname{supp}(\psi)\subset (0,1)$.  There exists $\delta>0$ so that

$$
\begin{gathered}
\bigl\| \psi(x)\bigl[g(x)-\tfrac1{2\kappa}\bigr] + \kappa^{-1}[R_0(2\kappa)(q\psi)](x) \bigr\|_{L^2(\mathbb{R})}^2
	\lesssim \kappa^{-7} \biggl[ 1+ \int_0^1 |q(x)|^2\,dx \biggr] \qquad\text{(7.4)} \\
\bigl\| \psi(x)\bigl[\kappa -\tfrac1{2g(x)}\bigr] + 2\kappa [R_0(2\kappa)(q\psi)](x) \bigr\|_{L^2(\mathbb{R})}^2
	\lesssim \kappa^{-3} \biggl[ 1+ \int_0^1 |q(x)|^2\,dx \biggr] \qquad\text{(7.5)} \\
\ \ \biggl| \int \rho(x) \psi(x)^2 \,dx - \tfrac{1}{2\kappa} \int \frac{|\widehat{q\psi} (\xi)|^2\,d\xi}{\xi^2+4\kappa^2} \biggr|
	\lesssim \kappa^{-7/2} \biggl[ 1+ \int_0^1 |q(x)|^2\,dx \biggr] \qquad\text{(7.6)} \\
\biggl| \iint q(x)^2 \kappa e^{-2\kappa|x-y|} \psi(y)^2 \,dx\,dy - \int q(x)^2 \psi(x)^2 \,dx \biggr|
	\lesssim \int_\mathbb{R} \frac{|q(x)|^2\,dx}{\kappa(1+x^2)} \qquad\text{(7.7)}
\end{gathered}
$$

for every $q\in B_\delta$ and $\kappa\geq 1$.  (Note that the implicit constants depend on $\psi$.)

*Proof.*
We begin with a commutator calculation:

$$
\begin{aligned}
[\psi(x),R_0] &= R_0 \bigl(-2\partial_x \psi'(x) + \psi''(x)\bigr) R_0 \\
&= R_0 \bigl(-2\partial_x\bigr) [\psi'(x),R_0] + R_0 \bigl(-2\partial_x\bigr)R_0\psi'(x) + R_0\psi''(x) R_0.
\end{aligned}
$$

This shows that for $\kappa\geq 1$, we can write

$$
\begin{gathered}\relax
[\psi(x),R_0] = \sqrt{R_0} A \sqrt{R_0} = \sqrt{R_0} B \sqrt{R_0} + \sqrt{R_0} C \sqrt{R_0} \psi'(x) \\
\text{with} \quad  \|A\|_{L^2\to L^2} + \|C\|_{L^2\to L^2} \lesssim \kappa^{-1} \quad\text{and}\quad  \|B\|_{L^2\to L^2} \lesssim \kappa^{-2}.
\end{gathered} \tag{7.8}
$$

From the series (2.8), we have

$$
\begin{aligned}
&\int_\mathbb{R}\{ \psi(x)\bigl[g(x)-\tfrac1{2\kappa}\bigr] + \kappa^{-1}[R_0(2\kappa)(q\psi)](x) \bigr\} f(x)\,dx \\
={}&  \sum_{\ell\geq 2} (-1)^\ell \operatorname{tr}\Bigl\{ \sqrt{R_0}\,f\,\sqrt{R_0} \sqrt{R_0}\,\psi q\,\sqrt{R_0} \Bigl( \sqrt{R_0}\,q\,\sqrt{R_0}\Bigr)^{\ell-1}  \Bigr\} \\
&\ +\sum_{\ell\geq 1} (-1)^\ell  \operatorname{tr}\Bigl\{ \sqrt{R_0}\,f\,\sqrt{R_0} B \Bigl( \sqrt{R_0}\,q\,\sqrt{R_0}\Bigr)^\ell  \Bigr\} \\
&\ +\sum_{\ell\geq 1} (-1)^\ell \operatorname{tr}\Bigl\{ \sqrt{R_0}\,f\,\sqrt{R_0} C \sqrt{R_0}\,\psi' q\,\sqrt{R_0} \Bigl( \sqrt{R_0}\,q\,\sqrt{R_0}\Bigr)^{\ell-1}  \Bigr\}.
\end{aligned} \tag{7.9}
$$

Using

$$
\Bigl\| \sqrt{R_0}\,h\,\sqrt{R_0} \Bigr\|_{\mathfrak{I}_2} \lesssim \kappa^{-3/2} \| h \|_{L^2}
\quad\text{and}\quad  \Bigl\| \sqrt{R_0}\,q\,\sqrt{R_0} \Bigr\|_{\mathfrak{I}_2} \lesssim \kappa^{-1/2} \| q \|_{H^{-1}}, \tag{7.10}
$$

which follow from (2.4), we then deduce that

$$
\text{LHS(7.9)} \leq \kappa^{-7/2} \|f\|_{L^2} \Bigl\{ \|\psi q\|_{L^2} + 1 + \|\psi' q\|_{L^2}\Bigr\},
$$

provided, say, $\delta\leq\frac12$.  This proves (7.4).  For future use, we also note that with the aid of (7.4), one may readily show

$$
\int \bigl(g(x) - \tfrac1{2\kappa}\bigr)^2\psi(x)^2\,dx + \bigl\| \kappa^{-1} R_0(2\kappa)(q\psi) \bigr\|_{L^2(\mathbb{R})}^2
	\lesssim \kappa^{-6} \biggl[ 1+ \int_0^1 |q(x)|^2\,dx \biggr] . \tag{7.11}
$$

Next we prove (7.5).  This almost follows from (7.4); indeed, writing

$$
\kappa -\tfrac1{2g(x)} = 2\kappa^2\bigl( g(x) - \tfrac1{2\kappa}\bigr) - \tfrac{2\kappa^2}{g(x)} \bigl( g(x) - \tfrac1{2\kappa}\bigr)^2 \tag{7.12}
$$

and invoking (7.4), we are left only to prove

$$
\int \tfrac{2\kappa^2}{g(x)} \bigl( g(x) - \tfrac1{2\kappa}\bigr)^2 \psi(x)^2\,dx \lesssim \kappa^{-3} \biggl[ 1+ \int_0^1 |q(x)|^2\,dx \biggr]. \tag{7.13}
$$

This then follows from (7.11).

We begin the proof of (7.6) by expanding one step further than (7.12) to write

$$
\begin{gathered}
\rho(x) =\sum_{i=1}^3 \rho_i(x) \quad\text{with}\quad  \rho_1(x):= 2\kappa^2\bigl\{g(x) - \tfrac1{2\kappa} + \tfrac1\kappa [R_0(2\kappa)q](x)\bigr\},\\
\rho_2(x):=  - 4\kappa^3\bigl(g(x) - \tfrac1{2\kappa}\bigr)^2 \quad\text{and}\quad  \rho_3(x):= 4\kappa^3\bigl(g(x) - \tfrac1{2\kappa}\bigr)^3 / g(x).
\end{gathered}
$$

Let us begin our analysis with the contribution of $\rho_1$.  From (2.8), we have

$$
\int \rho_1(x)\psi(x)^2\,dx = 2\kappa^2 \sum_{\ell\geq 2} (-1)^\ell \operatorname{tr}\Bigl\{ \psi(x)^2 \sqrt{R_0}\Bigl(\sqrt{R_0}\,q\,\sqrt{R_0}\Bigr)^\ell \sqrt{R_0}\Bigr\}.
$$

Now for any $\ell\geq2$, we have from (7.10), (7.8) and its adjoint that

$$
\begin{aligned}
&\operatorname{tr} \Bigl\{ \psi(x)^2 \sqrt{R_0} \Bigl(\sqrt{R_0}\,q\,\sqrt{R_0}\Bigr)^\ell \sqrt{R_0} \Bigr\} \\
&\ \ = \operatorname{tr} \Bigl\{  \sqrt{R_0}\,\psi q R_0^2 \psi q\,\sqrt{R_0} \Bigl(\sqrt{R_0}\,q\,\sqrt{R_0}\Bigr)^{\ell-2} \Bigr\}
	+ O\biggl( \kappa^{-6} \delta^{\ell-2} \biggl[ 1+ \int_0^1 |q(x)|^2\,dx \biggr] \biggr) .
\end{aligned}
$$

The error term here sums acceptably over $\ell\geq 2$.  The contribution of the first term is also acceptable provided we restrict to $\ell\geq 3$; indeed,

$$
\Bigl| \operatorname{tr} \Bigl\{ \sqrt{R_0}\,\psi q R_0^2 \psi q\,\sqrt{R_0} \Bigl(\sqrt{R_0}\,q\,\sqrt{R_0}\Bigr)^{\ell-2} \Bigr\} \Bigr|
	\lesssim \kappa^{-5-\frac{\ell-2}2} \delta^{\ell-2} \int_0^1 |q(x)|^2\,dx.
$$

Combining all of this, we deduce that

$$
\int \rho_1(x)\psi(x)^2\,dx = 2\kappa^2 \operatorname{tr} \Bigl\{ R_0\psi q R_0 \psi q R_0 \Bigr\}
	+ O\biggl( \kappa^{-7/2} \biggl[ 1+ \int_0^1 |q(x)|^2\,dx \biggr] \biggr) .
$$

We turn now to $\rho_2$.  Combining (7.11) and (7.4) gives

$$
\biggl| \int \bigl(g(x) - \tfrac1{2\kappa}\bigr)^2\psi(x)^2\,dx - \kappa^{-2} \bigl\| R_0(2\kappa)(q\psi) \bigr\|_{L^2(\mathbb{R})}^2 \biggr|
	\lesssim \kappa^{-13/2} \biggl[ 1+ \int_0^1 |q(x)|^2\,dx \biggr].
$$

Therefore,

$$
\int \rho_2(x)\psi(x)^2\,dx = - 4 \kappa \bigl\| R_0(2\kappa)(q\psi) \bigr\|_{L^2(\mathbb{R})}^2
	+ O\biggl( \kappa^{-7/2} \biggl[ 1+ \int_0^1 |q(x)|^2\,dx \biggr] \biggr) .
$$

We now consider $\rho_3$.  From (2.4) we have

$$
\Bigl\| \sqrt{R_0}\,h\,\sqrt{R_0} \Bigr\|_{\mathfrak{I}_2}^2 \lesssim \kappa^{-1} \| h \|_{L^1}^2 \int\frac{d\xi}{\xi^2+4\kappa^2} \lesssim \kappa^{-2} \| h \|_{L^1}^2 .
$$

Employing this to estimate the series (2.8) via duality, we obtain

$$
\bigl\| g - \tfrac1{2\kappa} \bigr\|_{L^\infty} \lesssim \kappa^{-3/2} \delta .
$$

Combining this with (7.11) yields

$$
\int \rho_3(x)\psi(x)^2\,dx \lesssim \kappa^{-7/2} \biggl[ 1+ \int_0^1 |q(x)|^2\,dx \biggr] .
$$

To derive the claim (7.6) by combining our results on each part of $\rho$, we need one additional identity, namely,

$$
2\kappa^2 \operatorname{tr} \Bigl\{ R_0\psi q R_0 \psi q R_0 \Bigr\} - 4 \kappa \bigl\| R_0(2\kappa)(q\psi) \bigr\|_{L^2(\mathbb{R})}^2
	= \tfrac{1}{2\kappa} \int \frac{|\widehat{q\psi} (\xi)|^2\,d\xi}{\xi^2+4\kappa^2} .
$$

That this equality holds follows from the same calculation we carried out in (2.35).

The last estimate (7.7) is relatively trivial.  As $\int \kappa e^{-2\kappa|x-y|}\,dy =1$,

$$
\biggl| \psi(x)^2 - \int \kappa e^{-2\kappa|x-y|} \psi(y)^2 \,dy \biggr| \lesssim \int \kappa e^{-2\kappa|y-x|} |x-y| \,dy \lesssim \kappa^{-1},
$$

which settles the case $|x|\leq 10$.  For $|x|\geq 10$, we have

$$
\biggl| \psi(x)^2 - \int \kappa e^{-2\kappa|x-y|} \psi(y)^2 \,dy \biggr| = \int_0^1 \kappa e^{-2\kappa|y-x|} \psi(y)^2 \,dy	\lesssim \kappa e^{-\kappa|x|} ,
$$

which offers more than enough decay in both $x$ and $\kappa$.
 $\square$

**Lemma 7.4.**
There is a $\delta>0$ so that the following is true: Let $Q$ be a family of Schwartz solutions to (KdV) on the line such that $\{q(0):q\in Q\}$ is an equicontinuous subset of $B_\delta$.  Then, for any $\psi\in C^\infty_c(\mathbb{R})$ and any $T>0$, we have

$$
\lim_{\kappa\to\infty} \ \sup_{q\in Q} \ \int_{-T}^T \int \frac{\xi^2 |\widehat{q\psi} (t,\xi)|^2\,d\xi}{\xi^2+4\kappa^2} \,d\xi\,dt  = 0. \tag{7.14}
$$

*Proof.*
Without loss of generality, we may assume that $\operatorname{supp}(\psi)\subset (0,1)$.  Throughout the proof, we regard $\psi$ and $T$ as fixed and implicit constants may depend on them.   Multiplying (3.7) by $\kappa$ and integrating against

$$
\phi(x) = \int_{-\infty}^x \psi(y)^2\,dy,
$$

we obtain

$$
\begin{aligned}
\int \kappa [\rho(T,x)-\rho(-T,x)] & \phi(x) \,dx \qquad\text{(7.15)} \\
&= -\tfrac32 \int_{-T}^T \! \iint |q(t,x)|^2 \kappa e^{-2\kappa|x-y|}\psi(y)^2 \,dx\,dy\,dt \qquad\text{(7.16)} \\
&\quad - 2\kappa \int_{-T}^T \! \int q(t,x)\bigl[ \kappa - \tfrac{1}{2g(t,x)}\bigr] \psi(x)^2 \,dx\,dt \qquad\text{(7.17)} \\
&\quad + 4\kappa^3 \int_{-T}^T \! \int \rho(t,x) \psi(x)^2 \,dx\,dt. \qquad\text{(7.18)}
\end{aligned}
$$

We will discuss these terms one at a time.

From Proposition 2.4, we have

$$
\bigl| \text{(7.15)} \bigr| \lesssim \kappa \alpha(\kappa;q),
$$

which converges to zero as $\kappa\to\infty$ uniformly for $q\in Q$; see Lemma 4.3.

Combining (7.7) and Lemma 7.1 yields

$$
\biggl| (7.16) + \tfrac32 \int_{-T}^T \! \int |q(t,x)|^2 \psi(x)^2 \,dx\,dt \biggr| \lesssim \kappa^{-1},
$$

or equivalently, by Plancherel,

$$
\biggl| (7.16) + \tfrac32 \int_{-T}^T \! \int |\widehat{\psi q}(t,\xi)|^2 \,d\xi\,dt \biggr| \lesssim \kappa^{-1}.
$$

From (7.5) and Lemma 7.1, we have

$$
\biggl| (7.17) - \int_{-T}^T \! \iint \psi(x)q(t,x) \kappa e^{-2\kappa|x-y|} q(t,y)\psi(y) \,dx\,dy\,dt \biggr| \lesssim \kappa^{-1/2},
$$

or equivalently (see (2.2)),

$$
\biggl| (7.17) - \int_{-T}^T \! \int \frac{4\kappa^2|\widehat{\psi q}(t,\xi)|^2}{\xi^2+4\kappa^2} \,d\xi\,dt \biggr| \lesssim \kappa^{-1/2}.
$$

From (7.6) and Lemma 7.1,

$$
\biggl| (7.18) - \tfrac{1}{2} \int_{-T}^T \! \int \frac{4\kappa^2|\widehat{\psi q}(t,\xi)|^2}{\xi^2+4\kappa^2} \,d\xi\,dt \biggr|
	\lesssim \kappa^{-1/2}.
$$

The claim (7.14) now follows from recombining (7.15)–(7.18).
 $\square$

*Proof of Proposition 7.2.*
By the same scaling argument as in Theorem 5.1, it suffices to prove (7.3) for solutions that are small in $L^\infty_t H^{-1}_x$.  Moreover, we may assume that $q_n$ are Schwartz solutions, since Proposition 7.2 in this reduced generality provides precisely the tool necessary to obtain the full version by approximation.

Let us fix $\psi\in C^\infty_c(\mathbb{R})$, not identically zero, with $\operatorname{supp}(\psi)\subseteq(0,1)$.  By a simple covering argument, it suffices to show that

$$
\lim_{n\to\infty} \ \sup_{x_0\in\mathbb{R}} \ \int_{-T}^T \Bigl\|\bigl[q_n(t,x)-q(t,x)\bigr] \psi(x+x_0) \Bigr\|_{L^2(\mathbb{R})}^2 \,dt  = 0. \tag{7.19}
$$

We will do this by breaking into high- and low-frequency components, using a refined local smoothing argument to handle the former, and applying Theorem 5.1 to handle the latter. The frequency decomposition is based on the multipliers

$$
m_\text{hi}(\xi) = \frac{|\xi|}{\sqrt{\xi^2+4\kappa^2}} \quad\text{and}\quad   m_\text{lo}(\xi) = \sqrt{1 - m_\text{hi}(\xi)^2} = \frac{2\kappa}{\sqrt{\xi^2+4\kappa^2}}.
$$

We begin with the low frequencies.  For $\kappa$ fixed, Theorem 5.1 implies

$$
\begin{aligned}
\lim_{n\to\infty} &\ \sup_{x_0\in\mathbb{R}}\ \int_{-T}^T  \; \Bigl\|m_\text{lo}(-i\partial_x) \Bigl(\bigl[q_n(t)-q(t)\bigr] \psi(\cdot + x_0) \Bigr)\Bigr\|_{L^2(\mathbb{R})}^2 \,dt \\
&\lesssim \kappa T  \lim_{n\to\infty}\ \sup_{x_0\in\mathbb{R}}\  \Bigl\| \bigl[q_n(t,x)-q(t,x)\bigr] \psi(x+x_0) \Bigr\|_{L^\infty_t H^{-1}_x ([-T,T]\times\mathbb{R})} \\
&\lesssim \kappa T \|\psi\|_{H^1(\mathbb{R})}  \lim_{n\to\infty} \bigl\| q_n(t,x)-q(t,x) \bigr\|_{L^\infty_t H^{-1}_x ([-T,T]\times\mathbb{R})} =0.
\end{aligned} \tag{7.20}
$$

We turn now to the high-frequency part.  As the sequence $q_n(0)$ is convergent in $H^{-1}(\mathbb{R})$, it is equicontinuous there.  Proposition 4.4 then guarantees that $\{q_n(t) : t\in\mathbb{R}\text{ and } n\in\mathbb{N}\}$ is also $H^{-1}(\mathbb{R})$-equicontinuous.  Thus Lemma 7.4 implies

$$
\lim_{\kappa\to\infty} \ \sup_{n} \int_{-T}^T \; \Bigl\|m_\text{hi}(-i\partial_x) [q_n(t)\psi(\cdot+x_0)] \Bigr\|_{L^2(\mathbb{R})}^2 \,dt = 0. \tag{7.21}
$$

Note that by Theorem 5.1 and weak lower-semicontinuity, it then follows that

$$
\lim_{\kappa\to\infty} \int_{-T}^T  \; \Bigl\|m_\text{hi}(-i\partial_x) [q(t)\psi(\cdot+x_0)] \Bigr\|_{L^2(\mathbb{R})}^2 \,dt = 0. \tag{7.22}
$$

We are now ready to put the pieces together.  From (7.21) and (7.22), we see that we can make the high-frequency contribution to LHS(7.19) small, uniformly in $n$, by choosing $\kappa$ sufficiently large.  But then by (7.20), we may make the low-frequency contribution as small as we wish by choosing $n$ sufficiently large.  This proves (7.19) and so (7.3).

Lastly, integration by parts shows that Schwartz solutions are distributional solutions of the initial-value problem, which is to say

$$
\begin{aligned}
\int h(0,x)q(0,x)\,dx + \int_0^\infty \!&\! \int [\partial_t h](t,x) q(t,x) \,dx\,dt \\
& =  \int_0^\infty \!\! \int - [\partial_x^3 h](t,x) q(t,x) + 3[\partial_x h](t,x) q(t,x)^2 \,dx\,dt
\end{aligned}
$$

for every $h\in C^\infty_c(\mathbb{R}\times\mathbb{R})$ (as well as the analogous statement backwards in time).  This now extends to $H^{-1}$ solutions via Corollary 5.2 and Proposition 7.2.
 $\square$

## Appendix A. 5th order KdV

The first polynomial conservation law for (KdV) beyond those discussed in the body of the paper is

$$
H_\text{5th}(q) := \int \tfrac12 q''(x)^2 + 5 q(x)q'(x)^2 + \tfrac52 q(x)^4\,dx,
$$

which generates the dynamics

$$
\frac{d\ }{dt} q = q^{(5)} -20 q'q'' - 10 qq''' +30 q^2q' = \bigl(q^{(4)} - 10qq'' - 5 [q']^2+10q^3\bigr)' \tag{A.1}
$$

under the Poisson structure (3.1).

Local well-posedness of (A.1) in $H^s(\mathbb{R})$ for $s\geq \tfrac54$ was shown in [23, 35], which immediately implies global well-posedness in the energy space $H^2(\mathbb{R})$; see also [21] for a thorough discussion of results in Fourier–Lebesgue spaces.  As reviewed therein, these papers represent the culmination of a considerable body of prior work.  In particular, we do not know of any further progress on the low regularity problem on the line.  On the torus, however, an optimal well-posedness result was obtained in  [27].  Specifically, they prove that (A.1) is well-posed in $L^2(\mathbb{R}/\mathbb{Z})$ and moreover, that the solution map does not admit a continuous extension to $H^s(\mathbb{R}/\mathbb{Z})$ for any $s<0$.  Our goal in this appendix is to show that a direct adaptation of the methods introduced in this paper yields an analogous well-posedness result on the line:

**Theorem A.1.**
Equation (A.1) is globally well-posed in $L^2(\mathbb{R})$.

As the proof of this theorem follows closely the treatment of (KdV) in the main body of the paper, we shall focus on recording the central estimates and identities, rather than recapitulating the arguments.

By the rescaling argument presented earlier and the fact that (A.1) preserves the $L^2$ norm, it suffices to show well-posedness of this equation in

$$
B_\delta:=\{ q\in L^2(\mathbb{R}) : \| q\|_{L^2} \leq \delta\} \qquad\text{(endowed with the $L^2$ topology)}
$$

for some $\delta>0$.  As this is a subset of the ball (2.1), all results of Section 2 and 3 still apply. Nevertheless some updating is required by the shift in regularity considered here:

**Proposition A.2.**
There exists $\delta>0$ so that the following are true:

*(a)* For all $\kappa\geq 1$, the two mappings in (2.6) are diffeomorphisms from $B_\delta$ onto a neighbourhood of the origin in $H^{+2}(\mathbb{R})$.

*(b)* For all $q\in B_\delta$,

$$
16\kappa^5\bigl(g-\tfrac1{2\kappa}\bigr) + 4\kappa^2 q \longrightarrow -q'' + 3q^2 \qquad\text{in $H^{-2}(\mathbb{R})$ as $\kappa\to\infty$.} \tag{A.2}
$$

Moreover, convergence is uniform on $L^2$-bounded and equicontinuous sets.

*Proof.*
As in the main body of the paper, the statements follow readily from certain basic estimates on the terms in the series (2.8).  As we must delve more deeply into the series than previously, we adopt the following notation

$$
h_\ell(x;\kappa) := (-1)^\ell  \langle \delta_x, R_0 (qR_0)^\ell \delta_x\rangle \quad\text{so that}\quad  g(x;\kappa)-\tfrac1{2\kappa} = \sum_{\ell=1}^\infty h_\ell(x;\kappa). \tag{A.3}
$$

The same computations that yielded (2.4) also show that

$$
\hat{h}_1(\xi) =  - \frac{\hat q(\xi)}{\kappa(\xi^2+4\kappa^2)}.
$$

Easy consequences of this include

$$
\| h_1 \|_{H^2_\kappa} = \kappa^{-1} \|q\|_{L^2} \tag{A.4}
$$

and

$$
16\kappa^5h_1 + 4\kappa^2 q + q'' \longrightarrow 0 \quad\text{in $H^{-2}$ as $\kappa\to\infty$;} \tag{A.5}
$$

moreover, this convergence is uniform on $L^2$-bounded and equicontinuous sets.

Elementary, though rather tiresome, calculations show that

$$
\hat{h}_2(\xi) = \frac{1}{2\kappa\sqrt{2\pi}} \int \frac{(\xi-\eta)^2 + \eta^2 + \xi^2+24\kappa^2}{[\xi^2+4\kappa^2][\eta^2+4\kappa^2][(\xi-\eta)^2+4\kappa^2]} \hat q(\xi-\eta)\hat q(\eta)\,d\eta,
$$

which should be compared with

$$
\widehat{\,q^2\,}\!(\xi) = \frac{1}{\sqrt{2\pi}} \int \hat q(\xi-\eta)\hat q(\eta)\,d\eta.
$$

Indeed, expanding out the difference in partial fractions reveals that as $\kappa\to\infty$,

$$
16\kappa^5 h_2 - 3q^2 \longrightarrow 0 \quad\text{in $L^1(\mathbb{R})$, and so also in $H^{-2}(\mathbb{R})$.} \tag{A.6}
$$

Moreover, convergence (even in $L^1$) is uniform for $q$ belonging to $L^2$-bounded and equicontinuous sets.

For any $\ell\geq 2$ and any Schwartz $f$,

$$
\biggl| \int f(x) h_\ell(x)\,dx \biggr| = \bigl| \operatorname{tr} \bigl( R_0 f R_0 q (R_0q)^{\ell-1} \bigr)\bigr| \leq \| R_0 f R_0\|_{\textit{op}} \| q R_0 q \|_{\mathfrak{I}_1} \| R_0 q\|_{\textit{op}}^{\ell-2},
$$

which we shall now use to estimate $h_\ell$ via duality. First, we apply the following elementary estimates

$$
\| R_0 f R_0\|_{\textit{op}} \lesssim \|f\|_{H^{-2}_\kappa},\quad
 \| q R_0 q \|_{\mathfrak{I}_1} = \tfrac1{2\kappa} \|q\|_{L^2}^2, \quad\text{and}\quad  \| R_0 q\|_{\textit{op}} \lesssim \kappa^{-3/2}\|q\|_{L^2},
$$

to deduce that the series (A.3) converges uniformly in $H^2_\kappa$ on $B_\delta$, for $\delta>0$ sufficiently small.  Indeed, this analysis readily yields also that

$$
\bigl\| g-\tfrac1{2\kappa} - h_1 \bigr\|_{H^{2}_\kappa} \lesssim \kappa^{-1} \|q\|_{L^2}^2 \quad\text{and}\quad
    \bigl\| dg - dh_1 \bigr\|_{L^2\to H^{2}_\kappa} \lesssim \kappa^{-1} \delta .
$$

Combined with (A.4), these two estimates allow one to readily complete the proof of part (a) by mimicking the arguments used to prove Proposition 2.2; compare, in particular, (2.9) and (2.11).

It remains to justify (A.2).  In view of (A.5) and (A.6), this follows from

$$
\bigl\| g-\tfrac1{2\kappa} - h_1 - h_2 \bigr\|_{H^{-2}} \lesssim \kappa^{-13/2} \|q\|_{L^2}^3,
$$

which follows in turn by incorporating the elementary bound

$$
\| R_0 f R_0\|_{\textit{op}} \lesssim \kappa^{-4} \|f\|_{L^\infty} \lesssim \kappa^{-4} \|f\|_{H^{2}}
$$

into the preceding duality analysis.
 $\square$

Our next task is to decide on a proper replacement for $H_\kappa$.  Proceeding formally, one is lead to the asymptotic expansion

$$
\alpha(\kappa;q) = \tfrac{1}{4\kappa^3} P(q)  - \tfrac{1}{16\kappa^5} H_\text{KdV}(q) + \tfrac{1}{64\kappa^7} H_\text{5th}(q) + O(\kappa^{-9})
$$

and thus to a natural proposal for renormalized Hamiltonians, namely,

$$
H^\text{5th}_\kappa (q) := 64\kappa^7 \alpha(\kappa;q) - 16 \kappa^4 P(q) + 4\kappa^2 H_\text{KdV}(q) = 4\kappa^2\bigl[ H_\text{KdV}(q) - H_\kappa(q) \bigr].
$$

We will now discuss analogues of Propositions 3.1, 3.2, and 4.4:

**Proposition A.3.**  There exists $\delta>0$ so that the following hold:

*(a)* The flow generated by $H^\text{\rm 5th}_\kappa$ is

$$
\tfrac{d\ }{dt}  \, q(x) =  -64\kappa^7 g'(x;\kappa,q) - 16 \kappa^4 q'(x) + 4\kappa^2 \bigl[ -q'''(x) + 6 q(x)q'(x) \bigr], \tag{A.7}
$$

which is globally well-posed on $B_\delta$ for any $\kappa\geq1;$ moreover, under this flow,

$$
\begin{aligned}
\tfrac{d\ }{dt}  \, \tfrac{1}{2g(x;\varkappa)} &= \tfrac{16\kappa^7}{\kappa^2-\varkappa^2} \Bigl( \tfrac{g(x;\kappa)}{g(x;\varkappa)} \Bigr)' - 16 \kappa^4 \Bigl( \tfrac{1}{2g(x;\varkappa)} \Bigr)'
    + 4\kappa^2 \Bigl( \tfrac{q(x)-2\varkappa^2}{g(x;\varkappa)}  \Bigr)'
\end{aligned} \tag{A.8}
$$

for any $1\leq \varkappa < \kappa$ and $\alpha(q;\varkappa)$ is conserved.

*(b)* Consider now the $H_\text{\rm 5th}$ flow (A.1), which is globally well-posed on $H^2(\mathbb{R})$.  For initial data in $B_\delta\cap H^2$ and any $\varkappa\geq 1$,

$$
\begin{aligned}
\tfrac{d\ }{dt}  \, \tfrac{1}{2g(x;\varkappa,q(t))} &= \Bigl(\tfrac{-q''(t,x)+3q(t,x)^2-4\varkappa^2q(t,x)+8\varkappa^4}{g(x;\varkappa,q(t))} \Bigr)';
\end{aligned} \tag{A.9}
$$

moreover, $H^\text{\rm 5th}_\varkappa$ is conserved.

*(c)* Let $Q\subseteq B_\delta\cap H^2$ be $L^2$-equicontinuous and let

$$
Q^* = \bigl\{ e^{J\nabla(t H_\text{\rm 5th} + s H^\text{\rm 5th}_\kappa)} q : q\in Q,\ t,s\in \mathbb{R},\text{ and } \kappa\geq 1 \bigr\}. \tag{A.10}
$$

Then $Q^*$ is $L^2$-equicontinuous and so convergence in (A.2) is uniform on $Q^*$.

*Proof.*
As $H^\text{5th}_\kappa = 4\kappa^2[ H_\text{KdV} - H_\kappa ]$, equation (A.7) follows from (3.11), while (A.8) follows directly from Propositions 3.1 and 3.2.  Well-posedness and commutativity of these constituent flows (together with conservation of $P$) immediately guarantees the well-posedness of this flow in the $H^{-1}$ topology on $B_\delta$.  Continuity in the $L^2$-topology will follow when we prove part (c) below.

The conservation of $\alpha(q;\varkappa)$ under the $H^\text{5th}_\kappa$ follows from its conservation under the $H_\text{KdV}$ and $H_\kappa$ flows.  It may also be deduced directly from (A.7) and (A.8).

As noted earlier, the well-posedness of (A.1) on $H^2(\mathbb{R})$ is a result of [23, 35].  To verify (A.9), we first observe that (A.1) can be rewritten as

$$
\frac{d\ }{dt} q = (-\partial_x^3 + 2 q\partial_x  + 2\partial_x q + 4\varkappa^2\partial_x) (-q''+3q^2-4\varkappa^2q) + 16\varkappa^4 q' ,
$$

which is little more that the biHamiltonian relation for the KdV hierarchy.  Applying Lemma 2.6  just as in the proof of Proposition 3.1, we deduce that

$$
\begin{aligned}
\tfrac{d\ }{dt}  \, g &= -2(-q''+3q^2-4\varkappa^2q)'g + 2(-q''+3q^2-4\varkappa^2q)g' + 16\varkappa^4 g'
\end{aligned}
$$

where we abbreviate  $g=g(x;\varkappa,q)$.  This then leads to (A.9) via the chain rule.

To verify that the $H_\text{\rm 5th}$ flow conserves $H^\text{5th}_\varkappa$, it suffices to verify that it conserves $P(q)$, $H_\text{KdV}(q)$, and $\alpha(q;\varkappa)$.  The first two follow from elementary calculations, while the conservation of $\alpha$ follows from (A.1) and (A.9).

The conservation of $\alpha$ holds the key to proving part (c); we simply need to modify Lemma 4.3 in the following way (cf. [41, Proposition 3.6]):  In view of (2.4),

$$
\begin{aligned}
\biggl| 4\varkappa^3\alpha(q;\varkappa) - \tfrac12\int \frac{4\varkappa^2 |\hat q(\xi)|^2\,d\xi}{\xi^2+4\varkappa^2} \biggr|
    &\leq 4\varkappa^3 \sum_{\ell=3}^\infty \bigl\| \sqrt{R_0} q \sqrt{R_0} \bigr\|^{\ell}_{\textit{op}}
        \lesssim  \varkappa^{-3/2}
\end{aligned}
$$

uniformly for $q\in B_\delta$ and $\varkappa\geq 1$, provided $\delta$ is sufficiently small.  Thus

$$
\text{$Q^*$ is $L^2$-equicontinuous} \iff [P(q)-4\varkappa^3\alpha(q;\varkappa)] \to 0\ \text{uniformly on $Q^*$ as $\varkappa\to\infty$}
$$

and (by conservation of $\alpha$) this holds if and only if $Q$ is $L^2$-equicontinuous.
 $\square$

*Proof of Theorem A.1.*
Reviewing what has gone before, we see that it suffices to show that for any $L^2$-equicontinuous set $Q\subseteq B_\delta\cap H^2$,

$$
\lim_{\kappa\to\infty} \sup_{q\in Q^*} \ \sup_{|t|\leq T}\ \| e^{tJ\nabla (H_\text{\rm 5th} - H_\kappa^\text{\rm 5th})} q - q \|_{L^2} =0. \tag{A.11}
$$

With a view to further reduction, let us define

$$
g(t,x) = g(x;\varkappa,q(t)) \quad\text{where}\quad  q(t) = e^{tJ\nabla(H_\text{\rm 5th} - H^\text{\rm 5th}_\kappa)} q \quad\text{and}\quad  q\in Q^*.
$$

In view of Proposition A.2(a), (2.13), and the equicontinuity of $Q^*$, we see that

$$
E:=\Bigl\{ \tfrac{1}{2 g(t,x)} - \varkappa : q\in Q^* \textrm{ and }t\in\mathbb{R}\Bigr\} \quad\text{is $H^2(\mathbb{R})$-equicontinuous.}
$$

Thus, by Lemma 4.2(ii) and Proposition A.2(a), we may verify (A.11) by showing that

$$
\bigl\| \tfrac{d\ }{dt} \bigl(\varkappa - \tfrac{1}{2g(t;\varkappa)}\bigr) \bigr\|_{H^{-3}} \to 0 \tag{A.12}
$$

as $\kappa\to\infty$ uniformly for $q\in Q^*$ and $t\in\mathbb{R}$.

We now verify (A.12).  Combining (A.8) and (A.9), we deduce (after considerable rearrangement) that

$$
\begin{aligned}
\tfrac{d\ }{dt}  \, \tfrac{1}{2g(x;\varkappa)} &= \Bigl( \tfrac{-q''(t,x)+3q(t,x)^2 - 16\kappa^5(g(x;\kappa)-\frac{1}{2\kappa})-4\kappa^2q}{g(x;\varkappa)} \Bigr)' \\
&\qquad  + \varkappa^2 \Bigl( \tfrac{-4q(t,x) - 16\kappa^3(g(x;\kappa)-\frac{1}{2\kappa})}{g(x;\varkappa)} \Bigr)' \\
&\qquad  - \tfrac{\varkappa^4\kappa^2}{\kappa^2-\varkappa^2}\Bigl( \tfrac{16\kappa(g(x;\kappa)-\frac{1}{2\kappa})}{g(x;\varkappa)} \Bigr)' - \tfrac{\varkappa^6}{\kappa^2-\varkappa^2}\Bigl( \tfrac{8}{g(x;\varkappa)} \Bigr)' .
\end{aligned}
$$

That this converges to zero in the desired sense then follows trivially from (A.2).
 $\square$

## References

[1] M. Appell, Sur la transformation des équations différentielles linéaires. Comptes Rendus **91** (1880), no. 4, 211–214.

[2] V. I. Arnol'd, *Mathematical methods of classical mechanics. Second edition.* Translated from the Russian by K. Vogtmann and A. Weinstein. Graduate Texts in Mathematics, **60**. Springer-Verlag, New York, 1989.

[3] T. B. Benjamin, J. L. Bona, and J. J. Mahony, Model equations for long waves in nonlinear dispersive systems. Philos. Trans. Roy. Soc. London Ser. A **272** (1972), no. 1220, 47–78.

[4] J. Bona and R. Scott, Solutions of the Korteweg-de Vries equation in fractional order Sobolev spaces. Duke Math. J. **43** (1976), no. 1, 87–99.

[5] J. L. Bona and R. Smith, The initial-value problem for the Korteweg-de Vries equation. Philos. Trans. Roy. Soc. London Ser. A **278** (1975), no. 1287, 555–601.

[6] J. Bourgain, Fourier transform restriction phenomena for certain lattice subsets and applications to nonlinear evolution equations. II. The KdV-equation. Geom. Funct. Anal. **3** (1993), no. 3, 209–262.

[7] J. Boussinesq, Théorie des ondes et des remous qui se propagent le long d'un canal rectangulaire horizontal, en communiquant au liquide contenu dans ce canal des vitesses sensiblement pareilles de la surface au fond. J. Math. Pures et Appl. (2) **17** (1872), 55–108.

[8] T. Buckmaster and H. Koch, The Korteweg–de Vries equation at $H^{-1}$ regularity. Ann. Inst. H. Poincaré Anal. Non Linéaire **32** (2015), no. 5, 1071–1098.

[9] M. Christ, Nonuniqueness of weak solutions of the nonlinear Schrödinger equation. Preprint `arXiv:math/0503366`.

[10] M. Christ, J. Colliander, and T. Tao, Asymptotics, frequency modulation, and low regularity ill-posedness for canonical defocusing equations. Amer. J. Math. **125** (2003), no. 6, 1235–1293.

[11] E. A. Coddington and N. Levinson, *Theory of ordinary differential equations.* McGraw-Hill Book Company, Inc., New York-Toronto-London, 1955.

[12] J. Colliander, M. Keel, G. Staffilani, H. Takaoka, and T. Tao, Sharp global well-posedness for KdV and modified KdV on $\mathbb{R}$ and $\mathbb{T}$. J. Amer. Math. Soc. **16** (2003), no. 3, 705–749.

[13] J. Colliander, M. Keel, G. Staffilani, H. Takaoka, and T. Tao, Multilinear estimates for periodic KdV equations, and applications. J. Funct. Anal. **211** (2004), no. 1, 173–218.

[14] J. Colliander, M. Keel, G. Staffilani, H. Takaoka, and T. Tao, Symplectic nonsqueezing of the Korteweg-de Vries flow. Acta Math. **195** (2005), 197–252.

[15] D. G. Crighton, Applications of KdV. In “KdV '95 (Amsterdam, 1995)”. Acta Appl. Math. **39** (1995), no. 1–3, 39–67.

[16] A. Degasperis and P. C. Sabatier, Extension of the one-dimensional scattering theory, and ambiguities. Inverse Problems **3** (1987), no. 1, 73–109.

[17] B. A. Dubrovin, V. B. Matveev, and S. P. Novikov, Nonlinear equations of Korteweg-de Vries type, finite-band linear operators and Abelian varieties. Uspehi Mat. Nauk **31** (1976), no. 1, 55–136.

[18] H. Flaschka and D. W. McLaughlin, Canonically conjugate variables for the Korteweg-de Vries equation and the Toda lattice with periodic boundary conditions. Progr. Theoret. Phys. **55** (1976), no. 2, 438–456.

[19] C. S. Gardner, J. M. Greene, M. D. Kruskal, and R. M. Miura, Method for solving the Korteweg-de Vries equation. Phys. Rev. Lett. **19** (1967), no. 19, 1095–1097.

[20] J. Garnett and E. Trubowitz, Gaps and bands of one-dimensional periodic Schrödinger operators. Comment. Math. Helv. **59** (1984), no. 2, 258–312.

[21] A. Grünrock, On the hierarchies of higher order mKdV and KdV equations. Cent. Eur. J. Math. **8** (2010), no. 3, 500–536.

[22] Z. Guo, Global well-posedness of Korteweg-de Vries equation in $H^{-3/4}(\mathbb{R})$. J. Math. Pures Appl. (9) **91** (2009), no. 6, 583–597.

[23] Z. Guo, C. Kwak, and S. Kwon, Rough solutions of the fifth-order KdV equations. J. Funct. Anal. **265** (2013), no. 11, 2791–2829.

[24] D. Hilbert, Grundzüge einer allgemeinen Theorie der linearen Integralgleichungen (Erste Mitteilung). Nachr. Ges. Wiss. Göttingen (1904), 49–91.

[25] R. Jost and A. Pais, On the scattering of a particle by a static potential. Physical Rev. (2) **82**, (1951), no. 6, 840–851.

[26] T. Kappeler, C. Möhr, and P. Topalov, Birkhoff coordinates for KdV on phase spaces of distributions. Selecta Math. (N.S.) **11** (2005), no. 1, 37–98.

[27] T. Kappeler and J.-C. Molnar, On the wellposedness of the KdV/KdV2 equations and their frequency maps. Ann. Inst. H. Poincaré Anal. Non Linéaire **35** (2018), no. 1, 101–160.

[28] T. Kappeler, P. Perry, M. Shubin, and P. Topalov, The Miura map on the line. Int. Math. Res. Not. 2005, no. 50, 3091–3133.

[29] T. Kappeler and J. Pöschel, *KdV & KAM.* Ergebnisse der Mathematik und ihrer Grenzgebiete, **45**. Springer-Verlag, Berlin, 2003.

[30] T. Kappeler and P. Topalov, Global wellposedness of KdV in $H^{-1}(\mathbb{T},\mathbb{R})$. Duke Math. J. **135** (2006), no. 2, 327–360.

[31] T. Kato, Wave operators and similarity for some non-selfadjoint operators. Math. Ann. **162** (1965/1966), 258–279.

[32] T. Kato, Smooth operators and commutators. Studia Math. **31** (1968), 535–546.

[33] T. Kato, Quasi-linear equations of evolution, with applications to partial differential equations. In “Spectral theory and differential equations” (Proc. Sympos., Dundee, 1974; dedicated to Konrad Jörgens), pp. 25–70. Lecture Notes in Math., Vol. 448, Springer, Berlin, 1975.

[34] T. Kato, On the Cauchy problem for the (generalized) Korteweg-de Vries equation. Studies in applied mathematics, 93–128, Adv. Math. Suppl. Stud., 8, Academic Press, New York, 1983.

[35] C. Kenig and D. Pilod, Well-posedness for the fifth-order KdV equation in the energy space. Trans. Amer. Math. Soc. **367** (2015), no. 4, 2551–2612.

[36] C. E. Kenig, G. Ponce, and L. Vega, Well-posedness of the initial value problem for the Korteweg-de Vries equation. J. Amer. Math. Soc. **4** (1991), no. 2, 323–347.

[37] C. E. Kenig, G. Ponce, and L. Vega, A bilinear estimate with applications to the KdV equation. J. Amer. Math. Soc. **9** (1996), no. 2, 573–603.

[38] N. Kishimoto, Well-posedness of the Cauchy problem for the Korteweg-de Vries equation at the critical regularity. Differential Integral Equations **22** (2009), no. 5–6, 447–464.

[39] R. Killip, Spectral theory via sum rules. In *Spectral theory and mathematical physics: a Festschrift in honor of Barry Simon's 60th birthday*, 907–930, Proc. Sympos. Pure Math., **76**, Part 2, Amer. Math. Soc., Providence, RI, 2007.

[40] R. Killip and B. Simon, Sum rules and spectral measures of Schrödinger operators with $L^2$ potentials. Ann. of Math. (2) **170** (2009), no. 2, 739–782.

[41] R. Killip, M. Visan, and X. Zhang, Low regularity conservation laws for integrable PDE. Preprint `arXiv:1708.05362`.

[42] A. Kiselev, Imbedded singular continuous spectrum for Schrödinger operators. J. Amer. Math. Soc. **18** (2005), no. 3, 571–603.

[43] H. Koch and D. Tataru, Conserved energies for the cubic NLS in 1-d. Preprint `arXiv:1607.02534`.

[44] D. J. Korteweg and G. de Vries, On the change of form of long waves advancing in a rectangular canal, and on a new type of long stationary waves. Philosophical Magazine, **39** (1895), no. 240, 422–443.

[45] P. D. Lax, Integrals of nonlinear equations of evolution and solitary waves. Comm. Pure Appl. Math. **21** (1968), 467–490.

[46] B. Liu, A priori bounds for KdV equation below $H^{-3/4}$. J. Funct. Anal. **268** (2015), no. 3, 501–554.

[47] W. Magnus and S. Winkler, *Hill's equation.* Corrected reprint of the 1966 edition. Dover Publications, Inc., New York, 1979.

[48] V. A. Marchenko, *Sturm-Liouville operators and applications.* Translated from the Russian by A. Iacob. Operator Theory: Advances and Applications, **22**. Birkhäuser Verlag, Basel, 1986.

[49] V. A. Marčenko and I. V. Ostrovskiĭ, A characterization of the spectrum of the Hill operator. Math. USSR-Sb. **26** (1975), no. 4, 493–554.

[50] H. P. McKean and E. Trubowitz, Hill's operator and hyperelliptic function theory in the presence of infinitely many branch points. Comm. Pure Appl. Math. **29** (1976), no. 2, 143–226.

[51] H. P. McKean and P. van Moerbeke, The spectrum of Hill's equation. Invent. Math. **30** (1975), no. 3, 217–274.

[52] A. Melin, Operator methods for inverse scattering on the real line. Comm. Partial Differential Equations **10** (1985), no. 7, 677–766.

[53] R. Miura, Korteweg-de Vries equation and generalizations. I. A remarkable explicit nonlinear transformation. J. Mathematical Phys. **9** (1968), no. 8, 1202–1204.

[54] R. M. Miura, C. S. Gardner, and M. D. Kruskal, Korteweg-de Vries equation and generalizations. II. Existence of conservation laws and constants of motion. J. Mathematical Phys. **9** (1968), no. 8, 1204–1209.

[55] L. Molinet, A note on ill posedness for the KdV equation. Differential Integral Equations **24** (2011), no. 7-8, 759–765.

[56] L. Molinet, Sharp ill-posedness results for the KdV and mKdV equations on the torus. Adv. Math. **230** (2012), no. 4–6, 1895–1930.

[57] M. Reed and B. Simon, *Methods of modern mathematical physics. I. Functional analysis.* Academic Press, New York-London, 1972.

[58] M. Reed and B. Simon, *Methods of modern mathematical physics. II. Fourier analysis, self-adjointness.* Academic Press, New York-London, 1975.

[59] M. Reed and B. Simon, *Methods of modern mathematical physics. IV. Analysis of operators.* Academic Press, New York-London, 1978.

[60] A. Rybkin, *Regularized perturbation determinants and KdV conservation laws for irregular initial profiles.* Topics in operator theory. Volume 2. Systems and mathematical physics, 427–444, Oper. Theory Adv. Appl., **203**, Birkhäuser Verlag, Basel, 2010.

[61] J. C. Saut and R. Temam, Remarks on the Korteweg-de Vries equation. Israel J. Math. **24** (1976), no. 1, 78–87.

[62] B. Simon, *Trace ideals and their applications.* Second edition. Mathematical Surveys and Monographs, 120. American Mathematical Society, Providence, RI, 2005.

[63] A. Sjöberg, On the Korteweg-de Vries equation. Report Dept of Computer Science Upsala University, 1967.

[64] A. Sjöberg, On the Korteweg-de Vries equation: existence and uniqueness. J. Math. Anal. Appl. **29** (1970), 569–579.

[65] R. Temam, Sur un problème non linéaire. J. Math. Pures Appl. (9) **48** (1969), 159–172.

[66] M. Tsutsumi and T. Mukasa, Parabolic regularizations for the generalized Korteweg-de Vries equation. Funkcial. Ekvac. **14** (1971), 89–110.

[67] Y. Tsutsumi, The Cauchy problem for the Korteweg-de Vries equation with measures as initial data. SIAM J. Math. Anal. **20** (1989), no. 3, 582–588.

[68] J. Vey, Sur certains systèmes dynamiques séparables. Amer. J. Math. **100** (1978), no. 3, 591–614.

[69] N. J. Zabusky and M. D. Kruskal, Interaction of “solitons” in a collisionless plasma and the recurrence of initial states. Phys. Rev. Lett. **15**, no. 15, (1965) 240–243.

[70] V. E. Zaharov and L. D. Faddeev, The Korteweg-de Vries equation is a completely integrable Hamiltonian system. Funkcional. Anal. i Priložen. **5** (1971), no. 4, 18–27.

[71] N. T. Zung, Convergence versus integrability in Birkhoff normal form. Ann. of Math. (2) **161** (2005), no. 1, 141–156.
