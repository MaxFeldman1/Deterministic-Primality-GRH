# Beyond the LLS/CMQR barrier: which extra information could help, and which cannot

Scripts (numpy/scipy floating point: evidence, not proof): `beyond_dual.py`, `beyond_positive.py`,
`beyond_smooth.py`, `beyond_miller.py`; outputs in the matching `.out` files and in §9.
Sources read: `below-one/BRIEF.md`, `designB.md`, `skeptic.md`; LLS v3 TeX (§5 L(1,χ), §6); CMQR v2 TeX
(EP1/EP2, Prop. 6, Thm 2, §5 numerics, the appendix on S(t,χ)).
Statements about Goldston–Gonek, Carneiro–Chandee–Milinovich, Chandee–Soundararajan, Granville–Soundararajan and
Kaczorowski–Perelli are from memory and were not re-read: marked "(recalled)".

## 0. Verdict

1. **Quadratic χ, GRH only: no idea (a)–(e) gives a constant below the barrier, and I found a structural reason.**
   The CMQR dual certificate is not just a bound on "the method". It is a complete *scenario*: a prime profile
   (χ = +1 below X, −1 on (X, 2.58X), +1 on (2.58X, 3.72X), …) together with a **positive** zero measure that
   satisfies the explicit formula for every test function at every scale (Proposition R, §3; checked numerically).
   Every inequality that follows from {zeros real, zero measure ≥ 0, conductor density, the explicit formula with
   any kernels, |χ(p)| ≤ 1, χ = 1 below X, complete multiplicativity} holds for this scenario. So no argument
   built from those inputs — linear, quadratic, SDP, multi-scale, Dedekind zeta, smooth numbers — can prove
   c < C*(1)⁻² ∈ [0.7597, 0.7615]. The principle is a heuristic theorem, not a formal one (§3.3 lists the gaps).
2. **No constant below 0.7596 survives for the quadratic problem.** The most tempting number, e/4 = 0.6796 from
   smooth numbers plus the LLS bound for L(1,χ), needs χ to have mean ≥ 0 just above X, which is exactly what the
   extremal scenario denies (§5e).
3. **For the application (Miller–Rabin) the index-2 worst case does not occur.** For every odd composite n ≠ 9
   the strong liars lie in a subgroup of index ≥ 4 with cyclic or Klein quotient (§7: short proof, brute force
   for n < 6000). The same framework then gives C(1/3)⁻² ≤ 0.6131 (limit of the method 0.6029) for the least
   Miller–Rabin witness. This is the only sub-0.7596 constant in this report that survives scrutiny, and it is
   for "least witness", not for "least quadratic non-residue".

## 1. Normalisation

χ primitive real mod q, hypothesis χ(n) = 1 for n < X, X = c·log²q, L := log X = 2 loglog q + log c.
v = log(n/X); a(v) ∈ [−1, 1] is the local mean of χ(p) over primes p ≈ X·e^v; a ≡ 1 on v < 0.
For a kernel φ(v) with φ̂(t) = ∫φ(v)e^{itv}dv, the explicit formula (GRH; errors o(log q)) reads

    Σ_n Λ(n)χ(n) n^{−1/2} φ(log(n/X)) = −Σ_γ φ̂(γ) X^{iγ},      LHS = √X ∫ a(v) e^{v/2} φ(v) dv + o(log q).

With B(v) := a(v)e^{v/2} and G(t) := ∫B(v)e^{itv}dv, Parseval gives ∫Bφ = (1/2π)∫φ̂·conj(G). The framework bounds
the zero side by (log q/2π)∫|φ̂|, so it proves exactly

    √c · |∫ B φ dv| ≤ (1/2π) ∫|φ̂| for all φ   ⟺   ‖G‖_∞ ≤ c^{−1/2}.

Hence c_LP = (inf over admissible a of ‖G‖_∞)⁻². This is CMQR's (EP2) with A = 1 (their t is v/2π, their ψ is
−a·e^{πt} on t > 0), and (EP1) is the primal. CMQR Theorem 2: 1.14600 < C(1) ≤ C*(1) < 1.14731, so
c_LP ∈ [0.75970, 0.76143]. `beyond_dual.py` reproduces ‖G‖_∞ = 1.1473077 for their 7-breakpoint profile, with
near-equal maxima at t = 0, 0.912, 3.27 (equioscillation).

## 2. The extremal scenario ("fake character")

From CMQR's Table (A = 1), in units n/X:

| window | (0,1) | (1, 2.581) | (2.581, 3.719) | (3.719, 4.293) | (4.293, 4.544) | (4.544, 5.217) | (5.217, 5.770) | (5.770, 5.882) | > 5.882 |
|---|---|---|---|---|---|---|---|---|---|
| a = mean of χ(p) | +1 | −1 | +1 | −1 | +1 | −1 | +1 | −1 | 0 |

Zero side: ρ(t) := −conj(G(t))/M with M = ‖G‖_∞, w(t) := ρ(t)e^{−itL}, D := log q/2π, and

    ν(t) := D · (1 − |w|²)/|1 − w|² = D · (1 + 2 Re Σ_{k≥1} w^k)  ≥ 0      (Poisson kernel in the fast phase tL).

Where |G| = M (t = 0 and the other equioscillation points) this is a Dirac comb: clusters of log q/L zeros at
t = ±π/L, ±3π/L, … (G(0) > 0 gives ρ(0) = −1, so the central point is a gap). To leading order the scenario sits
exactly on every known GRH ceiling for an individual L-function (all recalled):

| quantity | scenario | known GRH ceiling |
|---|---|---|
| zero multiplicity / cluster | log q/L = ½·log q/loglog q | Goldston–Gonek ½ |
| S(t,χ) sawtooth | ¼·log q/loglog q | Carneiro–Chandee–Milinovich ¼ (quoted in CMQR's appendix) |
| gap between zeros | 2π/L = π/loglog q | π/loglog q |
| log\|L(½+it)\| between clusters | (log 2/2)·log q/loglog q | Chandee–Soundararajan log 2/2 |
| L(1,χ) | e^γ(log log²q + log c + I₁), log c + I₁ = −1.001 | LLS Thm 1.5: ≤ 1 − 2 log 2 = −0.386 (slack) |

These coincidences are leading-order only (they depend on L ≈ 2 loglog q, not on c), but they show the scenario
is not excluded by any of those theorems. All of them are proved with the same explicit formula.

## 3. Proposition R and the no-go principle

### 3.1 Statement
**Proposition R (realisability; proof sketched, numerics in §9).** Let a(v) be admissible with ‖G‖_∞ = M and let
c < M⁻². For q large there is an even positive measure ν on ℝ with mean density log q/2π such that the pair
(ν, a) satisfies the explicit formula of §1 for every test function, with a ≡ 1 below X = c·log²q, |a| ≤ 1
everywhere, and a changed by O(loglog q/log q) elsewhere.

*Sketch.* Take ν as in §2 with M replaced by c^{−1/2} > M, so |w| ≤ M√c < 1 and ν/D is bounded above and below.
* k = 0: ∫φ̂(t)e^{itL}·D dt = log q·φ(−L). This is the genuine conductor term (n = 1).
* k = 1: −D∫φ̂·ρ dt = √c·log q·(1/2π)∫φ̂·conj(G) = √X∫Bφ. This is the prime side, for every φ.
* k ≥ 2: w^k has frequency kL + v, i.e. it is prime data at n = X^k e^v. The required density is D·|ρ^k|^ (v)
  ≲ D·c^{k/2}e^{v/2}|v|^{k−1}/(k−1)!, against available prime mass X^{k/2}e^{v/2}. The ratio is
  ≤ (e·k·L/((k−1)log q))^{k−1}, summable, total O(L/log q). So the harmonics ask for a bias O(loglog q/log q)
  in χ(p) for p ≈ X^k, which |χ| ≤ 1 allows.
* The leak of the k ≥ 2 tails into n < X (where a must be exactly 1) has relative size O(L/log q). Cancel it by
  a signed correction η with ‖η‖_∞ = O(D·L/log q); ν + η ≥ 0 because ν ≥ D(1−M√c)/(1+M√c) > 0.

Numerical check (`beyond_positive.py`, c^{−1/2} = 1.02·M, L = 20, 40, 80, four Gaussian kernels): ν/D ≥ 0.0099 > 0,
and the zero side computed from the positive ν agrees with the prime side to 10⁻⁴–10⁻³ (grid error; §9).

### 3.2 The principle
Any proof of n_χ ≤ c·log²q whose inputs all hold for the pair (ν, a) of Proposition R cannot have c < M⁻² = 0.7597.
Inputs that hold for (ν, a):
* GRH (ν lives on the real line), evenness (χ real), positivity of ν, mean density and conductor term;
* the explicit formula for any kernel, at any scale x, any finite family of kernels simultaneously;
* every consequence of ν ≥ 0: Bochner positive-definiteness of the matrix [ν̂(u_i − u_j)], any SDP relaxation;
* |χ(p)| ≤ 1, χ(p) = 1 for p < X, χ(p^k) = χ(p)^k (prime powers move ν by O(loglog q), negligible against D);
* complete multiplicativity: any ±1 assignment on primes with local mean a(v) extends to a completely
  multiplicative f with f = 1 on X-smooth integers, 1∗f ≥ 0, |f| ≤ 1;
* every bound for L(s,χ), S(t,χ), N(t,χ), zero gaps or multiplicities that is derived from the explicit formula.

So the framework's loss |Σ_γ K(iγ)x^{iγ}| ≤ Σ_γ|K(iγ)| is **not** recoverable from positivity: a positive measure
whose smooth density is log q/2π may put all its mass where the phase is aligned, because the phase x^{iγ}
oscillates at scale 1/loglog q, exactly the scale at which GRH does not control the local zero density
(a majorant of bandwidth < log X − ω(1) cannot see it; a wider one meets primes ≥ X of mass ≍ log q).

### 3.3 Where the principle is not a theorem
* Proposition R is a sketch. The correction step and the Γ-factor terms were not written out.
* (ν, a) is an asymptotic object. I do not construct an L-function. If (ν, a) existed exactly with integer atoms
  and ±1 primes, it would be a degree-1 Selberg-class function, i.e. a real Dirichlet character
  (Kaczorowski–Perelli, recalled). So the scenario can only be excluded by exact arithmetic
  (discreteness of primes, true periodicity), not by any o(log q)-robust inequality.
* Strong duality C(1) = C*(1) is not proved by CMQR; the gap is [0.75970, 0.76143]. The principle uses C*.

## 4. Ideas (b), (c), (d): zero-side information

**(b) Several scales/kernels with a quadratic form or SDP.** Precise form: for scales x_1..x_m and kernels K_j,
bound the vector (Σ_γ K_j(iγ)x_j^{iγ})_j using ν ≥ 0, e.g. via the PSD matrix [ν̂(log x_i/x_j)].
Estimate: no gain; limit stays C*(1)⁻². Flaw: §3.2 — the single pair (ν, a) satisfies all scales at once, and
ν ≥ 0 holds, so every such PSD constraint is satisfied. The off-diagonal entries ν̂(u) for |u| = O(1) are
≈ 0 (no primes of weight ≍ log q below log^{2−ε}q), so the matrix is ≈ D·Id for separated scales anyway.

**(c) Lower bounds from positive definiteness (K with non-negative transform on both sides).** Even
positive-definite φ give c ≈ 1.09–3.98 (BRIEF); one-sidedness is needed because the main term lives on v < 0
only. Mixed versions are covered by (b). Not viable.

**(d) Low-lying zeros of an individual L(s,χ) under GRH.** The available individual results (multiplicity,
S(t), gaps, lowest zero, size of L on the line, L(1,χ)) are all explicit-formula theorems, and the scenario
saturates them to leading order (§2). Family results (one-level density of quadratic characters) need an
average over q; for one χ there is no family: {χ^j} is trivial, and twists χψ by small-conductor ψ have prime
data ψ(p) below X (no main term) and ≈ 0 above, so their zeros are unconstrained and constrain nothing.
A hypothesis beyond GRH does help (CMQR appendix theorem on S(t,χ): S(t,χ) ≤ M(q) gives n_χ ≲ (2π/C(1))²(M(q) log n_χ)²), but
only if the S-constant drops below 1/(4π) ≈ 0.080 against the proven 1/4; that is not GRH alone. Not viable.

## 5. Ideas (a), (e): integers instead of prime powers

**(a) Dedekind zeta ζ_K = ζ·L(·,χ).** r = 1∗χ ≥ 0, and r(n) = d(n) on X-smooth n.
* Explicit formula for ζ_K'/ζ_K: the sum of the two explicit formulas. Linear, nothing new (this *is* the
  index-2 framework: 1 + χ ≥ 0).
* Σ_n r(n)w(n/y) = y·W(1)·L(1,χ) + (1/2πi)∫_{(σ)} ζ(s)L(s,χ)W(s)y^s ds ≥ Σ_{smooth} d(n)w(n/y). The pole term
  already exceeds the smooth-number sum (L(1,χ) = e^γ log X·e^T with T = Σ_{p≥X}χ(p)/p), so the inequality is
  empty unless T is controlled; controlling T is the L(1,χ) comparison below, which is linear.
* A pole-free product ζ^b L^a with non-negative coefficients does not exist (needs b ≥ |a| and b ≤ 0; this is
  Landau's theorem). At σ > 1 the inequality ζ(σ)L(σ,χ) ≥ ζ_X(σ)² reduces to the trivial
  Π_{p≥X}(1−χ(p)p^{−σ})⁻¹ ≥ Π_{p≥X}(1+p^{−σ})⁻¹.
* Class number: h(−q) ≥ #{reduced forms with X-smooth leading coefficient ≤ √q/2} ≈ Ψ(√q, log²q) = q^{1/4+o(1)}
  against h ≍ √q·loglog q. No contradiction.
Not viable.

**(e) Vinogradov's trick: χ = 1 on X-smooth integers.**
Precise form: S(y) = Σ_n χ(n)w(n/y) = (1/2πi)∫_{(σ)} L(s,χ)W(s)y^s ds, y = X^u; compare a lower bound from
smooth numbers with a GRH upper bound.
1. *Upper bound.* GRH gives log|L(σ+it,χ)| ≤ Σ_{p≤z}p^{−σ}(1+o(1)), z = z_eff ≍ log²q. Optimising
   σ = 1 − w/log z gives exponent min_w[−uw + E(w)], E(w) = ∫_0^w (e^s−1)/s ds: the de Bruijn saddle point for
   Dickman's ρ(u) (`beyond_smooth.py`, table 1: ratio to ρ(u) is 1.6–4.7 for u = 2..12). So GRH yields
   |S(y)| ≲ Ψ(y, z_eff)·slop, never o(Ψ). This matches Granville–Soundararajan (recalled): under GRH character
   sums are ≪ Ψ(x, log²q·(loglog q)^{O(1)}), and sums of length log^A q can be ≫ Ψ(x, log q). Vinogradov's trick
   needs S(y) = o(y) at y = X^u, u < √e, i.e. y = log^{3.3}q. That is false in general under GRH.
2. *Threshold.* Ψ(y, log²q) = y^{1/2+o(1)} for y = q^ε, the same size as the √y·|L(½+it)| error, where
   |L(½+it)| may be exp(c·log q/loglog q). X ≍ log²q is exactly the scale at which smooth numbers stop winning.
3. *Constant.* The dependence on c is Ψ(y, cz)/Ψ(y, z) ≈ exp(u·ξ(u)·log c/log z): 1 + O(1/loglog q) for bounded
   u (table 2), so u ≫ loglog q is needed, and then the comparison must be sharp to within e^{o(uξ(u))}.
4. *Best case and the flaw.* At σ → 1 the sharp GRH ceiling is LLS Thm 1.5, L(1,χ) ≤ e^γ·log((e/4)log²q), i.e.
   z_eff = (e/4)log²q. If χ had mean ≥ 0 on primes just above X, then L(1,χ) ≥ e^γ log X(1−o(1/log X)) and
   **c ≤ e/4 = 0.6796**. But the true statement is L(1,χ) = e^γ(log X + I₁ + o(1)), I₁ = ∫_{v>0} a(v)dv, so the
   constraint is log c + I₁ ≤ 1 − 2 log 2: linear in the prime data, a member of the LP family (LLS prove
   Thm 1.5 from the explicit formula, lines 1137–1175). The scenario has I₁ = −0.7265, X_eff = X·e^{I₁} =
   0.367·log²q < 0.6796·log²q: no contradiction (table 3). The same happens at every σ: the lower bound for the
   integer sum is Ψ(y, X_eff), not Ψ(y, X), because non-residues in (X, 2.58X) are not excluded, and there is
   no positivity to rescue it (see (a)).
5. *Why multiplicativity cannot bite at all.* χ(pp') and χ(mp) for p, p' ≥ X are values at composite integers of
   size > X. No GRH statement constrains sums over those integers except through L(s,χ) = exp(Σ Λχ/(n^s log n)),
   which is determined by the prime data. The scenario's f is a genuine completely multiplicative function, so
   every identity between integer sums and prime sums holds for it automatically.
Not viable under GRH alone. Estimated constant: none (the 0.6796 is illusory).

## 6. What is outside the principle (where a real improvement would have to come from)

Ranked by my estimate of viability; none is close to a proof.
1. **Change the problem: use index ≥ 4 for Miller–Rabin** (§7). Viable, elementary, constant 0.6131.
2. **Exact arithmetic of a real character**, i.e. properties false for "Beurling-type" generalised characters:
   true periodicity mod q beyond the functional equation, additive structure (χ on n and n+1, reciprocity
   classes of q modulo all p < X). The sieve heuristic gives n_χ ≲ log q·loglog q/log 2, but I know no GRH
   argument that uses it at polylog scale. Viability: very low.
3. **Hypotheses beyond GRH on local zero statistics** at scale 1/loglog q (S(t,χ) = o(log q/loglog q) near
   t = 0, or no clusters of ≫ log q/(loglog q)^{1+δ} zeros). These exclude the comb directly and give
   n_χ = o(log²q) (CMQR appendix theorem on S(t,χ)). Not GRH alone.
4. **Second-order terms**: the ceilings in §2 agree only to leading order. A proof that one of them fails at
   relative order 1/loglog q for the specific phase pattern of §2 would exclude the scenario; but each such
   ceiling is again an LP statement, so I expect nothing. Viability: very low.
5. **Inside the framework**: the true LP value lies in [0.7597, 0.7615]; at most 0.0018 to gain (the other
   agent's `inside.md`).

## 7. Miller–Rabin: the worst case is index 4, not index 2

**Lemma M.** Let n be odd, composite, n ≠ 9. The strong liars mod n lie in a subgroup H ≤ (ℤ/n)^* with
(ℤ/n)^*/H cyclic of order ≥ 4 or ≅ (ℤ/2)².

*Proof.* A strong liar a satisfies (i) a^{n−1} ≡ 1 (mod n); (ii) for primes p₁, p₂ | n the 2-parts of
ord_{p₁}(a) and ord_{p₂}(a) are equal (either a^d ≡ 1, or a^{2^j d} ≡ −1 modulo both). Let k_i = v₂(p_i − 1),
ψ_i a character mod p_i of order 2^{k_i}, χ_i = ψ_i^{2^{k_i−1}} the quadratic character; the 2-part of
ord_{p_i}(a) is the order of ψ_i(a).
* *n = p^e, e ≥ 2.* ord(a) divides gcd(p^e − 1, p^{e−1}(p−1)) = p − 1, so the liars lie in the subgroup of
  index p^{e−1} with cyclic quotient; p^{e−1} ≥ 5 unless n = 9.
* *Two primes with k₁ > k₂.* Ψ := ψ₁^{2^{k₂−1}}·χ₂ has order 2^{k₁−k₂+1} ≥ 4. For a liar, ψ₁(a) and ψ₂(a) have
  the same order 2^i ≤ 2^{k₂}: if i = k₂ both factors are −1, if i < k₂ both are 1. So Ψ(a) = 1.
* *All k_i equal, at least three primes.* χ₁χ₂ and χ₁χ₃ are trivial on liars: Klein quotient.
* *Exactly two primes, k₁ = k₂, n = p₁p₂.* n − 1 ≡ p₂ − 1 (mod p₁ − 1), so (i) forces a to be an m₁-th power
  residue mod p₁, m₁ = (p₁−1)/gcd(p₁−1, p₂−1), odd; m₁, m₂ are not both 1. With an order-m character ω (m ≥ 3
  odd), ω·χ₁χ₂ has order 2m ≥ 6.
* *Exactly two primes, k₁ = k₂, p_i² | n.* (i) makes a a p_i-th power residue mod p_i²: order-p_i character
  times χ₁χ₂, order 2p_i ≥ 6. ∎

Brute force (`beyond_miller.py`): for all odd composite n < 6000 and ten Carmichael numbers the subgroup
generated by the strong liars has index ≥ 4 except n = 9 (index 3); index exactly 4 at 15, 91, 703, 1891.

**Consequence.** "Every a < X is a non-witness" implies "every a < X lies in H" with h = [G:H] ≥ 4. Summing the
explicit formula over the h − 1 non-trivial characters of G/H (values h − 1 on H, −1 off H; conductors ≤ n)
is the LLS/CMQR index-h argument with A = 1/(h−1) ≤ 1/3. CMQR Theorem 2: C(1/3) > 1.27722, so the least
Miller–Rabin witness is ≤ (0.6131 + o(1))·log²n (method limit 0.6029). With the LLS Γ-kernel the skeptic's
table gives 0.6566 at h = 4. Caveats: (1) CMQR Theorem 3 is stated for one character of order ℓ; the Klein case
needs the subgroup version (same proof; LLS state their theorem for subgroups). (2) asymptotic only: explicit
N₀ would need the designB machinery redone with h = 4 (the positivity gain is per character, the zero sum has
three characters). (3) I have not checked whether this is in the literature; it is close to the Rabin–Monier
φ(n)/4 bound but is a statement about the generated subgroup.

## 8. What a human expert should check

1. Proposition R: write out the correction step and the Γ-terms, or find an obstruction I missed to a positive
   ν with first harmonic −conj(G)/M. This is the load-bearing claim for "(b), (c), (d) are dead".
2. Whether any GRH-only theorem about an individual L(s,χ) is *not* an explicit-formula statement and fails for
   the comb of §2 (I know of none).
3. §5e step 4: that the lower bound for integer sums under the hypothesis is governed by X·e^{I₁}, so that
   e/4 is unreachable. A counter-argument would have to produce positivity above X.
4. Lemma M and the Klein-quotient version of the index-h argument; then whether the project wants a
   Miller–Rabin constant ≈ 0.61–0.66 instead of 0.777.

## 9. Script outputs

```
$ python beyond_dual.py
sup|G| = 1.1473077 at t = 0.0000   (CMQR: 1.1473077 at 0)
   max on [0.2,0.4]: 1.14726 at t=0.2000
   max on [0.9,1.2]: 1.14730 at t=0.9118
   max on [1.5,200.0]: 1.14731 at t=3.2707
barrier c = 1/sup^2 = 0.75970
L(1,chi): I1 = -0.7265, log c + I1 = -1.0013 vs LLS ceiling 1 - 2 log 2 = -0.3863 -> satisfied

$ python beyond_positive.py        (c^{-1/2} = 1.02 M; columns: prime side | zero side from the positive nu)
L = 20:  min nu/D = 9.901e-03, max nu/D = 100.8
   gauss(mu=0.0,s=0.5)   -0.123073 | -0.123789      gauss(mu=0.8,s=0.3)   -0.350322 | -0.351055
   gauss(mu=-1.0,s=1.0)  +0.714992 | +0.713945      gauss(mu=1.5,s=0.4)   +0.014698 | +0.013470
L = 40:  -0.123073 | -0.123000    -0.350322 | -0.350390    +0.714992 | +0.715032    +0.014698 | +0.014686
L = 80:  -0.123073 | -0.122945    -0.350322 | -0.350340    +0.714992 | +0.715063    +0.014698 | +0.014741
(residuals 1e-4..1e-3: quadrature of the fast phase on a grid of step 2e-4 and, at L = 20, the k >= 2 harmonics;
 not a precision test.)

$ python beyond_smooth.py
(1) u=2: rho 3.07e-01, saddle 4.87e-01 | u=5: 3.55e-04, 9.46e-04 | u=12: 1.30e-14, 6.08e-14
(2) gain from c = 0.76 at log q = 1e6: u=2: 1.025, u=5: 1.141, u=20: 2.45, u=100: 621
(3) X_eff = X e^{I1} = 0.3674 log^2 q  vs  z_eff = (e/4) log^2 q = 0.6796 log^2 q -> no contradiction

$ python beyond_miller.py 6000
indices < 4: [(9, 3)]
histogram of small indices: {3: 1, 4: 7, 5: 1, 6: 8, 7: 1, 8: 8, 9: 1, 10: 5, 11: 1, 12: 15}
examples with index exactly 4: [15, 91, 703, 1891]
```
