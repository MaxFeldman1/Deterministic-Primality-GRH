# Research brief: an explicit Miller–Rabin / least-character-non-residue constant c < 1 under GRH

## Target theorem (new: no explicit version is published)
Assume GRH for all Dirichlet L-functions (incl. ζ). There are explicit c < 1 and N₀ such that for every
n ≥ N₀ and every Dirichlet character χ ≠ 1 mod n there is an integer 1 ≤ a < c·(log n)² with χ(a) ≠ 1
(non-units count: χ(a) = 0 ≠ 1). Ideally c(n) → 0.794 (LLS Thm 1.2 constant for index 2) or toward
0.7615 (Carneiro–Milinovich–Quesada-Herrera–Ramos, arXiv:2404.08380), with an explicit rate, e.g.
c(n) ≤ c∞ + A/log log n or c∞ + A/log n; at minimum one explicit pair (c, N₀) with c ≤ 0.9.
Report N₀ for c ∈ {0.95, 0.9, 0.85, 0.8} (and the limit c∞ of your construction).

## Setting / reductions you may assume (all already proved in Lean)
* Contradiction hypothesis: χ(a) = 1 for all 1 ≤ a < X. Then every a < X is coprime to n (so every prime
  factor of n is ≥ X), and χ is induced by a primitive χ̃ mod q̃ | n with χ̃(a) = 1 for a < X.
* Let h = order of χ, H̃ = ⟨χ⟩ (h characters χ^j, j = 0..h−1). For every n, Σ_j χ^j(n) = h·1[(n,q)=1, χ(n)=1] ≥ 0.
  h = 2 is the worst case (constants improve with h). Each χ^j (j ≠ 0) is non-principal with conductor ≤ q.
* GRH: zeros of L(s, χ̃) in 0 < Re s < 1 have Re = 1/2; also RH for ζ.

## Source
LLS, arXiv 1309.3595 v3; TeX at
/private/tmp/claude-501/-Users-maxfeldman-Desktop/adeaa94f-ea9f-4c13-80e6-10ff2e96c919/scratchpad/lls_src/lls.tex
§6 (lines 1347–1540): Lemma 6.1, Proposition 6.2, kernels. Reduced functional (lead's numerics): with
φ(v) = K̃(e^v), for index h:  c = λ (h−1)² ((1/2π)∫|K(it)|dt)² / (h∫_{v≤log λ} φ(v)e^{v/2}dv − ∫ φ(v)e^{v/2}dv)².
The Γ(s+1/2) kernel (φ(v) = e^{v/2 − e^v}) gives 0.7935 at λ = 2.452 (h = 2). Even, positive-definite φ
(K(it) ≥ 0, e.g. Fejér, Gaussian, e^{−a|v|}) give only ≈ 1.09, 1.11, 3.98 — one-sided kernels are needed, so
K(it) is complex and the zero side needs an EXPLICIT bound for Σ_γ |K(iγ)| (LLS: "(1+o(1)) log q /2π ∫|K|",
via Iwaniec–Kowalski Thm 5.12, not explicit). Making this explicit is the heart of the problem.

## Formalizability (important: the result will be formalized in Lean 4 / Mathlib afterwards)
Existing Lean infrastructure (repo ~/Desktop/maths/Deterministic-Primality-GRH/lean/DetPrimality/Bach):
Perron/Mellin integrals on Re s = 2 for kernels 1/(s(s+1)), 1/s² (and double-pole variants) with residue
lemmas and termwise integration over zeros; genus-1 Hadamard partial fractions ξ'/ξ(s) = B + Σ_ρ(1/(s−ρ)+1/ρ)
for primitive χ ≠ 1 AND for ζ (valid at every non-zero s); Re B(χ) = −Σ Re 1/ρ; exact Γ-factor (digamma)
pieces; sharp numerics for Σ Λ(n)n^{−σ} (σ = 3/2, 2, 5/4) and digamma values via `decide +kernel`;
RH-explicit lower bound Σ_{n≤x} Λ(n) log(x/n) ≥ x − 0.05(√x+1) − log(2π) log x − 1.
Prefer constructions whose analytic inputs are: rational (or finite exponential-polynomial) kernels K(s)
with residue computations; partial-fraction identities at real points σ (σ > 1 preferred, since Dirichlet
series converge); explicit Dirichlet-series numerics. Avoid, if you can, anything needing deep special-function
theory in Lean (Γ on vertical lines, Stirling with explicit constants, Beurling–Selberg extremal functions
whose properties need heavy proofs) — or isolate such facts as small, clearly stated numeric lemmas.

## Deliverables (write into this directory)
1. `<your-name>.md`: a complete, rigorous pen-and-paper proof with every constant explicit (no O(·), no o(1)
   without an explicit bound), structured as numbered lemmas suitable for formalization, stating exactly which
   analytic facts are used.
2. Python scripts (mpmath; interval-style safety margins) computing every numeric constant and N₀; run them,
   include the output.
3. A summary (≤ 400 words) as your final message: construction, c∞, the (c, N₀) table, the riskiest step.
Be skeptical of your own steps; flag anything you are not sure is correct. Do not edit Lean files.
