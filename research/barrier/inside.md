# Inside the CMQR framework: the true value of the index-2 constant, a certified 0.76077, and what the barrier rests on

Files (all in this directory; outputs in the matching `.out`):

| file | role | status |
|---|---|---|
| `inside_repro.py` | reproduces CMQR's 0.7615 (primal) and 0.7596 (dual) | floating point (mpmath, 30 digits) |
| `inside_primal_socp.py`, `inside_primal_scan.py` | primal convex programme on the Hardy/Laguerre family | floating point (cvxpy + Clarabel) |
| `inside_dual_socp.py` | dual convex programme | floating point |
| `inside_make_testfn.py` → `inside_testfn.json` | the explicit test function (33 rational coefficients, 8 decimals) | data |
| **`inside_certificate.py`** | **rigorous** lower bound J(φ) ≥ 1.146504 for that function | exact rationals + Sturm + `mpmath.iv` interval arithmetic; stdlib + mpmath only; 25 s |
| `inside_check.py` | independent quadrature check of the closed forms used by the certificate | floating point |
| `inside_dual_certificate.py`, `inside_dual_s.json` | upper bound C(1) < 1.14654 for an explicit dual function | float64 branch-and-bound with Lipschitz constant and explicit rounding allowance (not interval arithmetic) |

The SOCP scripts need `cvxpy`/`clarabel` (a scratch venv was used); the two certificates and the checks run with the
system `python3` (mpmath, numpy).

## 0. Results

1. **Framework** (§1). For index h = 2 the CMQR method proves, under GRH, limsup n_χ/log²q ≤ C(1)⁻², where
   C(1) = sup_φ J(φ), J = N/I,

       N(φ) = ∫_{v<0} φ(v) e^{v/2} dv − ∫_{v>0} |φ(v)| e^{v/2} dv,     I(φ) = (1/2π) ∫ |K(t)| dt,   K(t) = ∫ φ(v) e^{itv} dv,

   over real φ with K ∈ L¹. This is BRIEF.md's reduced functional without the restriction φ ≥ 0.
2. **Reproduction** (§2). CMQR Table 2 function: J = 1.146007, J⁻² = 0.761422 (their "0.7615").
   CMQR Table 1 dual function: sup|ĝ| = 1.1473077, i.e. 0.759697 (their "0.7596").
3. **Neither number is the truth.** Solving both problems as convex programmes:
   primal optimum ≈ 1.146512 (J⁻² = 0.760752), dual optimum ≈ 1.146513 (0.760750). So numerically
   **C(1) = 1.14651, C(1)⁻² = 0.76075**, and there is no duality gap to 5–6 digits.
   The window 0.7596–0.7615 collapses to a point: 0.7615 can be lowered by 0.0007, not by 0.0019.
4. **Certified** (§3): an explicit φ with **J(φ) ≥ 1.14650421**, hence (CMQR Theorem 3, ℓ = 2)

       limsup_{q→∞} n_χ / log² q  ≤  C(1)⁻²  <  0.76077       (GRH).

   Conversely (§4, float-verified) C(1) < 1.14654, i.e. the framework cannot give less than 0.76071.
   So **0.76071 < C(1)⁻² < 0.76077**.
5. **Barrier** (§5). It rests on two worst-case steps: (D1) χ(p) for p ≥ X is an arbitrary number in the unit disc
   with PNT density; (D2) the triangle inequality over zeros |Σ_γ K(γ)X^{iγ}| ≤ Σ_γ|K(γ)| ≤ (1+o(1))(log q/2π)∫|K|.
   Exact zero-sum identities for rational |K(it)| and the hypothesis gain inside zero sums change only the
   O(1) term next to log q; they are instances of (EP1) and are subject to the same bound C(1)⁻² ≈ 0.76075.
   Getting below needs input that is not linear-explicit-formula + positivity: a constraint on clumping of zeros
   (S(t,χ) bounds with a small constant), or structure of χ beyond X.

## 1. The extremal problem

### 1.1 CMQR's statement (arXiv:2404.08380v2, §1.3, §2.1)

Fourier transform F̂(t) = ∫F(x)e^{−2πixt}dx. Class 𝒜 = {F ∈ L¹(ℝ) complex-valued, F̂ real-valued}.

    (EP1)   C(A) = sup_{0≠F∈𝒜} (2π/‖F‖₁) ( ∫_{−∞}^0 F̂(t)e^{πt}dt − ∫_0^∞ F̂₋(t)e^{πt}dt − A∫_0^∞ F̂₊(t)e^{πt}dt ).
    (EP2)   C*(A) = inf_ψ 2π ‖ (1_{ℝ₋}e^{π·})^ − (1_{ℝ₊}ψ)^ ‖_∞ ,   ψ ∈ L¹(ℝ₊), −e^{πt} ≤ ψ(t) ≤ A e^{πt}.

* Theorem 3: GRH, χ non-principal of order ℓ ⟹ limsup n_χ/log²q ≤ C(1/(ℓ−1))⁻². Index 2 is A = 1.
* Proposition 6 (weak duality): C(A) ≤ C*(A). Proof: for ψ in the class,
  numerator ≤ ∫F̂·(1_{ℝ₋}e^{π·} − 1_{ℝ₊}ψ) = ∫F·(…)^ ≤ ‖F‖₁‖(…)^‖_∞.
* Theorem 2: 1.14600 < C(1) < 1.14731, i.e. 0.75969 < C(1)⁻² < 0.76143.
  * Lower bound 1.14600 (→ "0.7615"): F̂(t) = g((πt−c)/a), g(y) = Σ_{n≤12} b_n y^{2n−1}e^{y}1_{y<0}/(2n−1)!
    (sign as in their ancillary `lb.py`), a = 0.246, c = 0.626, b from Table 2; 14 parameters optimised by Brent's
    derivative-free principal-axis method; value by mpmath quadrature (not interval arithmetic).
  * Upper bound 1.14731 (→ "0.7596"): ψ(t) = e^{πt}·(+1, −1, +1, …) on (T_n, T_{n+1}), n = 0..6, ψ = 0 beyond T₇ = 0.282;
    T_i found by random-restart local search; sup of |g₁| read off numerically (three nearly equal local maxima).
  * They stop there: "we do not attempt further numerical experimentation, leaving the problem of numerically
    identifying the third decimal digit, and beyond, to the interested reader."
* Where the zero side enters (their Lemma 5 and eq. after (4.10)): with ĥ(t) = ½(F̂(t−Δ)+F̂(−t−Δ)), Δ = log n_χ/2π,
  |Σ_γ h(γ)| ≤ Σ_γ |F(γ)| ≤ (log q/2π)‖F‖₁ + O_F(log q/log log q)   (Selberg's bound for S(t,χ)).

### 1.2 Normalisation used here

v = 2πt (so v = log(n/n_χ)), φ(v) = F̂(v/2π), K(x) = ∫φ(v)e^{ixv}dv = 2πF(x). Then

    C(1) = sup_φ J(φ),   J = N(φ)/I(φ),   N, I as in §0.1,          c∞(φ) := J(φ)⁻².

Dual: for s: (0,∞) → [−1,1] put g_s(v) = e^{v/2}1_{v<0} − s(v)e^{v/2}1_{v>0}, ĝ_s(t) = ∫g_s e^{itv}dv
= 1/(½+it) − ∫_0^∞ s(v)e^{(½+it)v}dv. Then

    N(φ) ≤ ∫φ g_s = (1/2π)∫K(t)·conj ĝ_s(t) dt ≤ I(φ)·sup_t|ĝ_s(t)|,   so  C(1) ≤ C*(1) = inf_s ‖ĝ_s‖_∞.      (1.1)

Relation to LLS/BRIEF: BRIEF's c = λ(h−1)²I²/(h∫_{v≤log λ}φe^{v/2} − ∫φe^{v/2})² with φ ≥ 0 is J⁻² after the shift
v ↦ v − log λ; CMQR's only change is to drop φ ≥ 0 and pay −|φ| beyond X. designB's kernel 6/(s+1)⁴ is
φ(v) = −(v−log 3)³e^{v−log 3}1_{v<log 3}: J⁻² = 0.77713 (checked with `inside_primal_socp.evaluate`).

### 1.3 The Hardy/Laguerre family (all one-sided rational kernels with a single pole)

Fix β > 0, c ∈ ℝ, and q(z) = Σ_{n=0}^D q_n zⁿ with real coefficients. Put

    Φ_n(y) = ((−1)ⁿ/(n+1))·(−y)e^{y}L_n^{(1)}(−2y)  (y < 0),   Φ = Σ q_nΦ_n,   φ(v) = Φ(β(v−c))·1_{v<c}.

**Lemma 1.** With u = 1/(1+iw), z = 2u−1 = (1−iw)/(1+iw):
(i) ∫_{−∞}^0 Φ_n(y)e^{iwy}dy = u²zⁿ for every complex w with Re(1+iw) > 0. Hence
K(t) = (e^{itc}/β)·u²q(z) at w = t/β, and, substituting w = tan(θ/2) (z = e^{−iθ}, |u|²dw = dθ/2),

    I(φ) = (1/2π)∫|u|²|q(z)|dw = (1/4π)∫_{−π}^{π}|q(e^{iθ})|dθ = ½‖q‖_{H¹}.

(ii) ∫φ(v)e^{v/2}dv = (e^{c/2}/β)·u₀²q(z₀), u₀ = 2β/(2β+1), z₀ = (2β−1)/(2β+1) (take iw = 1/(2β)).
(iii) N(φ) = ∫φe^{v/2} − 2∫_0^cφ₊e^{v/2}dv, and ∫_0^cφ₊e^{v/2}dv = (e^{c/2}/β)∫_{−βc}^0[Φ(y)]₊e^{y/(2β)}dy.

*Proof.* (i) is the Laplace transform ∫_0^∞e^{−sτ}τL_n^{(1)}(τ)dτ = (n+1)(s−1)ⁿ/s^{n+2} at s = (1+iw)/2 after
τ ↦ 2τ. (ii) is (i) at a non-real w. (iii): for A = 1, ∫_{v<0}φ − ∫_{v>0}|φ| = ∫φ − 2∫_{v>0}φ₊. ∎
(`inside_check.py` confirms (i)–(iii) by direct quadrature to ≥ 10 digits.)

So on this family (EP1) is: maximise the concave function N over the H¹-ball of polynomials — a second-order cone
programme for fixed (β, c). The family is dense in {φ supported in (−∞, c]} as D → ∞ (Laguerre functions), and
c may be taken large. CMQR's Table 2 function is the member β = 1/(2a) = 2.0325, c = 1.252, D = 22
(restricted to odd powers of y).

## 2. Numerics (floating point)

`inside_repro.out`:

```
primal (CMQR Table 2, A=1):  N = 1.14600151272  I = 0.999995488249  J = 1.146006683   c = J^-2 = 0.7614224882
dual (CMQR Table 1, A=1): largest local maxima of |ghat| on [0,60):  [('1.14730774', '0.0'), ('1.1473066', '3.27'), ('1.14730334', '0.91'), ...]
   C*(1) <= 1.14730774   =>  barrier  c >= C*^-2 = 0.759696554
```

`inside_socp.out` (primal SOCP: 4000 nodes on the half circle for ‖q‖_{H¹}, 60×8 Gauss nodes on (0,c); values
re-evaluated with 2·10⁵ / 3.2·10⁴ nodes; dual SOCP: s piecewise constant on m cells of [0,V], sup over a t-grid,
re-evaluated on a 4·10⁵ grid):

```
beta=2.0325 c=1.252 D=22: re-evaluated J = 1.1463286   c_inf = 0.760995     <- CMQR's own (a, c, degree), convex optimum
beta=2 c=2 D=32:          re-evaluated J = 1.1465042   c_inf = 0.760762     <- used for the certificate
beta=3 c=2 D=40:          re-evaluated J = 1.1465106   c_inf = 0.760753
beta=4 c=3.2 D=60:        re-evaluated J = 1.1465113   c_inf = 0.760752
D=100, beta in {3,5,7}, c in [1.8,3.2]:  J = 1.146510 .. 1.146512                     (inside_primal_scan.py)
dual V=3 m=600 : 1.1466131  (0.760617)                                  (first run, not in the .out file)
dual V=5 m=1000: 1.1465202  (0.760741)
dual V=8 m=1600: 1.1465129  (0.760750)
```

Reading.
* Already with CMQR's own scale, shift and degree the convex optimum is 0.76100, not 0.76142: Brent's method on
  a non-smooth 14-parameter functional did not converge. Their dual function (7 switches, compact support
  [0, 1.77]) is further from optimal: 0.75970 vs 0.76075.
* Primal saturates at J = 1.146512 (stable in β ∈ [2,7], c ∈ [2,3.2], D ∈ [60,100]); dual decreases to 1.146513.
  **C(1) = 1.14651(2), C(1)⁻² = 0.76075.** The duality gap is < 2·10⁻⁶: (EP1) and (EP2) have the same value
  to this accuracy.
* Shape of the extremiser: φ > 0 on (−∞, 0.965), then sign changes at v ≈ 0.965, 1.396, 1.737, with φ tiny
  beyond v ≈ 1 (φ(0) = 0.287, φ(0.5) = 0.062, φ(1.2) = −9·10⁻⁴, φ(1.6) = 6·10⁻⁵). The dual optimum has s = +1, −1, +1,
  −1 switching at v ≈ 0.96, 1.39, 1.72 (complementary slackness: s = sign φ), then non-extreme values.
  Economically: beyond X the kernel uses a factor e^{0.965} ≈ 2.6 of positive weight, the rest is a small correction.
* Other bases suggested in the task (B-splines, Gaussian×polynomial): not needed — the Laguerre/H¹ family is
  dense for one-sided φ, turns ‖K‖₁ into a polynomial H¹ norm, and already meets the dual bound.

## 3. Rigorous certificate: C(1) > 1.14650421, c∞ < 0.76077

**Test function** (`inside_testfn.json`): β = 2, c = 2, D = 32, q₀..q₃₂ =

    0.06052663 0.43299452 1.25513415 1.89067032 1.65626707 1.10778195 0.88829330 0.67452346 0.40658906
    0.30608696 0.21279811 0.12002922 0.09541892 0.05780989 0.03295835 0.02853556 0.01318068 0.00971956
    0.00789687 0.00217006 0.00371031 0.00129630 0.00057592 0.00136160 −0.00036032 0.00070669 −0.00015795
    −0.00002135 0.00001438 −0.00067018 0.00000943 −0.00166760 −0.00153447

(exact decimals). φ(v) = Φ(2(v−2))1_{v<2}, Φ(y) = (−y)e^{y}R(y), R = Σ q_n((−1)ⁿ/(n+1))Σ_{k≤n}C(n+1,n−k)(2y)^k/k! ∈ ℚ[y],
deg R = 32. K(t) = (e^{2it}/2)·q(z)/(1+it/2)², z = (2−it)/(2+it): rational with one pole, of order 34, at t = 2i
(Mellin variable s = −2), K = O(t⁻²), φ continuous, real: F = K/2π ∈ 𝒜.

**Theorem C.** J(φ) ≥ 1.14650421. Hence C(1) > 1.1465042 and, under GRH, for non-principal χ mod q of any
order ℓ ≥ 2 (C(A) is non-increasing in A, and ℓ = 2 is A = 1): limsup n_χ/log²q ≤ C(1)⁻² ≤ 0.7607618 < 0.76077.

*Proof = `inside_certificate.py`* (output below). By Lemma 1 with u₀ = 4/5, z₀ = 3/5, κ = 1+1/(2β) = 5/4:

    N(φ) = (e/2)·( T₁ − 2T₂ ),   T₁ = (16/25)q(3/5) ∈ ℚ,   T₂ = ∫_{−4}^0 [−yR(y)]₊ e^{5y/4} dy,   I(φ) = (1/2π)∫_0^π|q(e^{iθ})|dθ.

* **A (signs).** R is built exactly in ℚ[y]. Its Sturm chain (exact rational arithmetic) gives exactly 3 distinct
  roots in (−4, 0) (R(−4), R(0) ≠ 0; R is squarefree). Three intervals of width 2·10⁻⁴⁵ with an exact sign change
  of R at their rational endpoints isolate them (y = −2.0700561, −1.2079055, −0.5254281, i.e. v = 0.964972,
  1.396047, 1.737286). So the sign of R on the four complementary intervals is constant: +, −, +, −.
* **B (T₂).** W(y) = e^{κy}Σ_j(−1)^jG^{(j)}(y)/κ^{j+1}, G = −yR, is an exact antiderivative of Ge^{κy} (the script
  verifies W_p' + κW_p = G in ℚ[y]). T₂ ≤ Σ_{R>0 intervals}(W(b)−W(a)) + 3·2·10⁻⁴⁵·Σ|G_k|4^k, with W evaluated at
  rational points (polynomial part exact, exponential in 260-bit interval arithmetic):
  T₂ ∈ [0.07538985742641, 0.07538985742642]; T₁ = 0.994330371618759…; N(φ) ≥ 1.14650421083575.
* **C (I).** |q(e^{iθ})|² = r₀ + Σ_{k≥1}r_k cos kθ with r_k ∈ ℚ exact. On each of M = 40000 cells of [0,π],
  Cauchy–Schwarz: ∫_cell|q| ≤ (h·∫_cell|q|²)^{1/2}, and ∫_cell|q|² = A(θ_{i+1}) − A(θ_i),
  A(θ) = r₀θ + Σ r_k sin(kθ)/k, in 120-bit interval arithmetic (enclosure widths ≤ 1.4·10⁻²⁷).
  Result I(φ) ≤ 1.00000000019478 (the true value is 0.9999999995…; the loss of the bound is 7·10⁻¹⁰).
* J ≥ 1.14650421083575/1.00000000019478 ≥ 1.14650421061. ∎

```
A. deg R = 32, R squarefree: True, Sturm: number of distinct roots of R in (-beta c, 0) = 3   [1.0s]
   isolated 3 roots (each in an interval of width 2e-45, exact sign change verified):
   y_i = [-2.070056099364819, -1.2079055137218562, -0.5254281474273185]  i.e. v_i = c + y_i/beta = [0.964972, 1.396047, 1.737286]
   sign of phi on (0,c) between consecutive roots (from v = 0 upwards): [1, -1, 1, -1]
B. T2 = int [(-y)R]_+ e^{kappa y} dy  in  [0.0753898574264166, 0.0753898574264166]
   T1 = u0^2 q(z0) = 0.994330371618759 (exact rational);   N(phi) in [1.14650421083575, 1.14650421083575]
C. I(phi) <= 1.00000000019478   (M = 40000 cells, widest enclosure of a cell integral 1.4e-27)   [19.0s]
RESULT:  J(phi) >= 1.14650421061   =>   C(1) >= 1.14650421   and   limsup n_chi/log^2 q <= 0.760761791
CERTIFIED:  C(1) > 1.1465,   c_inf <= C(1)^-2 < 0.76077 < 0.7615
```

Independent check (`inside_check.out`, plain quadrature of φ and K, no closed forms):
N = 1.14650421084, I = 0.999999999516, J = 1.146504211, J⁻² = 0.760761789.

**What exactly is certified, and what is assumed.**
* Certified by computation: the inequality J(φ) ≥ 1.14650421 for the explicit φ. Inputs that are *not* machine
  checked: Lemma 1 (a textbook Laplace transform; cross-checked numerically), correctness of `mpmath.iv` and of
  Python's `Fraction`. No floating-point optimisation output is trusted; float root guesses are verified exactly.
* Taken from the literature: CMQR Theorem 3 (asymptotic, non-explicit: it uses Selberg's S(t,χ) = O(log q/log log q)
  and their Theorem 1(i), the reduction to F̂ ∈ C_c^∞). Our F is in 𝒜 (F ∈ L¹, F̂ real), so J(F) ≤ C(1) by
  definition and Theorem 3 applies verbatim.
* Not done: an *explicit* (N₀) version in the style of designB. That needs an explicit bound for Σ_γ|K(γ)| with
  |K(t)| = |q(z)|/(2|1+it/2|²) non-rational: a rational majorant G ≥ |K| with ∫G/∫|K| − 1 ≪ 2% (designB §1.4 found
  0.3–0.4% loss in I for similar kernels with low-order majorants; a loss of that size would eat a third of the gain). The asymptotic
  gain over designB's 0.7771 is 2.1% in c (1.05% in √c). q has near-zeros on |z| = 1 only near θ ≈ π (|t| ≳ 25),
  where |K| is negligible, so such a majorant is plausible; it was not constructed here.

Margin left by this certificate: best float value in the family 0.760752 vs certified 0.760762 (D = 32 instead of
60–100); not worth pursuing, since the dual bound (§4) is 0.76071.

## 4. The barrier, recomputed: C(1) < 1.14654

`inside_dual_s.json`: s piecewise constant on 1000 cells of [0,5] (6 decimals, |s| ≤ 1), s = 0 beyond; ψ = s·e^{v/2}
is in CMQR's class 𝓑₁. `inside_dual_certificate.py` proves sup_t|ĝ_s(t)| < 1.14654 by branch-and-bound in t with
|ĝ_s'| ≤ ∫|v||g_s| ≤ L = 81.09 and the tail bound |ĝ_s(t)| ≤ 106.51/|t| (Abel summation):

```
m = 1000 cells, V = 5, Lipschitz L = 81.09, tail constant B = 106.51 -> scan t in [0, 106.5]
verified: |ghat(t)| < 1.146540 for all real t   (20681662 evaluations, depth 15, largest value seen 1.14652036)
=> C(1) <= C*(1) < 1.146540,  so no test function in (EP1) gives c below  0.760714
```

Status: float64 with an explicit allowance 10⁻⁸ per evaluation (a priori rounding error < 10⁻¹⁰; the margin is
2·10⁻⁵). Not interval arithmetic; I regard it as reliable but it is one notch below §3. The unrounded V = 8
solution gives 1.146513 on a fine grid (not branch-and-bound verified).

**Conclusion for goal (2).** The gap 0.7615 → 0.7596 cannot be closed. The framework's constant is
C(1)⁻² ∈ (0.76071, 0.76077), numerically 0.76075. CMQR's primal value loses 6.7·10⁻⁴ and their barrier is
1.05·10⁻³ too optimistic.

## 5. What the barrier rests on, and which variants it covers

### 5.1 The two inequalities

Chain (1.1) has exactly two inequalities, and they are the two "worst-case" steps of the number-theoretic proof:

* **(D1) prime side beyond X.** −|φ(v)| ≤ −s(v)φ(v) for v > 0, |s| ≤ 1. In the proof: for n ≥ X the value
  Re χ(n) ∈ [−1,1] is unknown and the primes have density 1 (PNT/RH for ζ). A dual function s *is* a hypothetical
  profile of −Re χ(p) at p = Xe^{v}.
* **(D2) zero side.** (1/2π)∫K·conj ĝ ≤ (1/2π)∫|K|·‖ĝ‖_∞. In the proof:
  |Σ_γ K(γ)X^{iγ}| ≤ Σ_γ|K(γ)| ≤ (1+o(1))(log q/2π)∫|K|: triangle inequality over the zeros, then local zero density.

Everything else (explicit formula, removal of imprimitivity, Γ-terms, RH for ζ on n < X) is an identity up to o(log q).

Model reading. Set √X = log q/‖ĝ_s‖_∞. The explicit formula says that the zero-counting measure is
dN(t) = (log q/2π)dt − (1/π)Re Σ_nΛ(n)χ(n)n^{−½−it}dt + O(1)dt. With χ = 1 below X and −s beyond,
Σ_nΛ(n)χ(n)n^{−½−it} ≈ √X·X^{−it}·conj ĝ_s(t) − 1/(½−it), so the model's zero "density" has first harmonic (in the
fast phase θ = t log X + arg ĝ_s(t)) of relative amplitude 2√X|ĝ_s(t)|/log q ≤ 2. A positive measure with mean 1 can have
first-harmonic amplitude up to 2 (a comb δ(θ − θ₀)), and the higher harmonics it needs sit at frequencies ≈ k log X,
k ≥ 2, i.e. at primes ≈ X^k where Λ(n)n^{−½} ≍ X^{k/2} ≫ log q leaves unlimited room for |χ(p)| ≤ 1. So for
X = (log q/C*(1))² there is a fictitious configuration — χ(p) = 1 below X, bias −s(v) beyond X, zeros on the line in
clumps of ≈ log q/log X at spacing 2π/log X wherever |ĝ_s| is extremal — that satisfies every explicit formula to
leading order, has a positive zero measure of the right density, and violates nothing. (This paragraph is a
heuristic model, not a theorem; the rigorous statement is (1.1). In particular the harmonic bookkeeping at
frequencies k log X is only sketched.)

Hence the precise answer: **the barrier rests on (D2) — the triangle inequality over zeros, which is sharp exactly
for clumped (comb-like) zero configurations — together with (D1), full freedom of χ at primes ≥ X.**
It is not an artefact of a lossy estimate inside the framework.

### 5.2 Variants

1. **Exact zero-sum identity for rational |K(it)|** (designB Lemma 4). It replaces the *second* inequality of (D2)
   by an identity: Σ_γ|K(γ)| = (log q/2π)∫|K| + (explicit O(1)). The leading coefficient is the same number
   (1/2π)∫|K| = I(φ); only the O(1) changes. The first inequality of (D2) (triangle inequality with the phases
   X^{iγ}) is still used. So such a proof has c∞ = J(φ)⁻² ≥ C(1)⁻² > 0.76071 whatever the kernel, and designB's
   0.7771 is simply J⁻² of a non-optimal φ. **Covered.**
2. **Hypothesis gain inside the zero sum** (designB's −κ). The even test function |K| has a fixed Fourier transform
   ĥ; the prime side of its explicit formula is Σ_nΛ(n)Re χ(n)n^{−½}ĥ(log n), bounded by Σ_nΛ(n)n^{−½}|ĥ(log n)| = O(1)
   independently of q and X. Using χ(n) = 1 for n < X fixes its sign (−κ instead of +κ) — a shift of log q by a
   constant, decisive for N₀, invisible in c∞. **Covered** (c∞ unchanged).
3. **General positivity: any h ≥ 0 on ℝ in Σ_γh(γ) ≥ 0, with the hypothesis used on its whole prime side.**
   To gain at leading order ĥ must carry mass ≍ 1 at v = log X + O(1) (weight √X there). Write
   h = H + Re(e^{it log X}F(t)) with H the part of ĥ near 0. Mass of ĥ on 1 ≪ v ≪ log X contributes o(√X); mass at
   v ≈ k log X, k ≥ 2, is penalised by X^{k/2} (it sits beyond X with unknown χ); and h ≥ 0 forces H ≥ |F|
   asymptotically (average over the fast phase). The inequality obtained is N(F̂) ≤ (log q/√X)·(1/2π)∫H with
   ∫H ≥ ∫|F|: again (EP1). The model of §5.1 satisfies all such inequalities simultaneously. **Covered**
   (heuristic reduction; I have not written a full proof).
4. **Several characters / the index-h trick.** Already in the framework through A = 1/(h−1); for h = 2 nothing is left.
5. **φ ≥ 0 (LLS), two-sided kernels, majorants.** Sub-cases of (EP1).

### 5.3 What is *not* covered (where an improvement would have to come from)

* **Constraints on zero clumping.** The extremal configuration needs ≈ log q/log X ≈ log q/(2 log log q) zeros in
  windows much shorter than 1/log X, i.e. S(t,χ) of size ≍ log q/log log q. CMQR Appendix A (their last theorem, label `arg_bound`) makes this
  quantitative: if |S(t,χ)| ≤ (1+o(1))𝓜(q) then limsup n_χ/(𝓜(q)log n_χ)² ≤ (2π/C(1))²; the known GRH bound
  𝓜 = ¼log q/log log q (Carneiro–Chandee–Milinovich) gives a result worse by π², and any constant below 1/(4π)
  would beat C(1)⁻². This is the genuine exit, and it is a different (non-linear in the zeros) input.
* **Structure of χ beyond X.** At primes there is none (χ(p), p ≥ X, are free), so inside sums over Λ(n) nothing
  can be gained; arguments on integers (χ(mn) = χ(m)χ(n), positivity of 1∗χ, Vinogradov-type sieving of smooth
  numbers) are outside the framework.
* **Lower-order terms.** All of the above concerns c∞ only. For explicit (c, N₀) pairs the O(1) terms of variants
  1–2 matter a great deal (designB), and the barrier says nothing about them.

## 6. Caveats / things I am not sure about

* §3 is rigorous modulo Lemma 1 and the interval library; §4 is float64 + Lipschitz (not interval arithmetic).
* "C(1) = C*(1)" is observed to 2·10⁻⁶, not proved; nothing here depends on it (only the two-sided enclosure).
* §5.1 (model) and §5.2 item 3 are heuristic reductions. The rigorous content of "barrier" is (1.1) = CMQR Prop. 6,
  which covers every argument of the shape "explicit formula for h = Re(e^{it log X}F) + |Σ_γh(γ)| ≤ Σ_γ|F(γ)| ≤
  (1+o(1))(log q/2π)‖F‖₁", including items 1, 2, 4, 5.
* The certified 0.76077 is an asymptotic constant (limsup). No N₀ is attached to it.
