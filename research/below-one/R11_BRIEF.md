# Round 11 brief — formalize designB (explicit c < 1 under GRH) in Lean 4

Math source: `research/below-one/designB.md` (proof), `refereeB.md` (independent referee: all lemmas correct;
its to-do list: certified F₀, F₁ lower bounds; Chebyshev input; write out the order-4 Perron/termwise
Hadamard argument; Z₃ via Cauchy–Schwarz). Hand-off statements (fixed, do not edit):
`lean/DetPrimality/Bach/R11Defs.lean` — `R11ZetaZ`, `R11ZetaExplicit`, `R11ChiExplicit`, `R11ZeroSumGain`,
`R11Tail c₀`, `R11Bound c n`. Their constants are loosened from designB; the lead verified the assembly
closes with them (c₀ = 2: (c, N₀) = (0.95, 10¹²), (0.90, 10¹⁴), (0.85, 10¹⁶), (0.80, 10¹⁹), (0.79, 10²¹);
c₀ = 1.39: 10⁹·⁶, 10¹⁰·⁵, 10¹¹·⁸, 10¹³·⁹; c∞ ≤ 0.77715).

Repo: `~/Desktop/maths/Deterministic-Primality-GRH/lean` (Lean v4.33.1, Mathlib pinned; NEVER build Mathlib from source).
Build/check ONLY via `~/Desktop/maths/Deterministic-Primality-GRH/bin/check.sh DetPrimality/<Path>.lean`
(rsyncs to the AWS box; do not run lake locally). Other agents build concurrently — fine.

Reusable proved infrastructure (read; grep exact names):
* Hadamard: `Bach/HadamardGeneral.lean` (`logDeriv_eq_tsum`, valid at every non-zero point; summability),
  `Bach/HadamardL.lean` (primitive χ ≠ 1: `zeroOrd`, functional equation `logDeriv_completed_reflect`,
  `re_logDeriv_eq_tsum_proof`), `Bach/LLSZeta.lean`, `Bach/LLSZetaConst.lean` (ζ: ξ = s(s−1)Λ₀+1, zeros
  `zeroOrd (1 : DirichletCharacter ℂ 1)`, `llsZeta_hadamard`, `llsZeta_B`, decomposition of −ζ'/ζ).
* Perron: `Bach/ExplicitFormula.lean` (`perronI`, kernel 1/(s(s+1))), `Bach/ExplicitPerronLog.lean` (double poles,
  `hasMellin_log_ind1`), `Bach/LLSPerron*.lean` (kernel x^s/s²: `llsPer_perronL`, residues, termwise zero sums
  `llsPer_perronL_zeroSum`, Γ-part, `llsPer_explicit`), `Bach/LLSZetaLower.lean` (ζ version, weight summability
  `llsZL_summable_weight`), `Bach/LLSGain*.lean` (shifted kernels `s ↦ f(s+1)`, re-centring at 3).
* Numerics: `Bach/SharpZeroSum.lean` (certified Σ Λ(n) n^{-σ} at σ = 3/2, 2 via Λ*1 = log and `decide +kernel`
  certificates; digamma values), `Bach/ExplicitDigamma.lean`, `Bach/ZeroSumGain.lean`, `Bach/ChebyshevThirty.lean`
  (Chebyshev ψ bounds), `Bach/LLSZetaConst.lean` (`llsZeta_gamma_lt`).
* Elementary/assembly templates: `Bach/LLSElem.lean` (`llsElem_no_witness_facts`: reduction to the primitive χ̃,
  coprimality of all a < X), `Bach/LLSAssembly.lean`, `Bach/LLSPrime.lean`, `Miller/LLSMiller.lean`.

Rules: new files only, under `lean/DetPrimality/Bach/R11<Topic>*.lean`, with your assigned declaration prefix; never
edit existing files. No `sorry`/`admit`/`axiom`/`native_decide`/`implemented_by`/`@[extern]` (`decide +kernel` OK).
Finish with `#print axioms` on your main theorems — only [propext, Classical.choice, Quot.sound]. No git commits.
If a Prop is false as stated or out of reach, prove the closest correct variant and report exactly what changed
(the lead re-runs the numeric assembly). Final message ≤ 400 words: exact statements, files, build status, axioms.
