# Lean-verified deterministic primality (GRH) — research notes

Started 2026-11-21.

## Status of formalization (checked 2026-11-21)

- **AKS (unconditional, deterministic poly-time):** NOT in Mathlib.
  - mathlib4 PR #34507 "feat(NumberTheory/AKSPrimality)" — open, last update 2026-05-15.
  - mathlib4 PR #39404 "AKSPrimality: Introspective definition" — open, last update 2026-09-02.
  - Supporting PRs #43343 (AdjoinRoot charP/isReduced), #37299 (Chebyshev primorial bound) — open.
  - Zulip (Jan 2026): author self-reports ~60% through the *correctness* proof; no runtime/complexity proof mentioned.
  - Prior art in other systems: HOL4 (Chan & Norrish, ANU thesis — correctness, plus some complexity work), Coq, ACL2.
- **Miller–Rabin (probabilistic):** formalized in hanwenzhu/miller-rabin (Reservoir), error <= 1/4, no GRH / deterministic version.
- **Deterministic Miller under GRH (Bach bound: witness a <= 2(ln n)^2):** no Lean formalization found.
- Mathlib has: Lucas primality (LucasPrimality.lean), Lucas–Lehmer, Fermat pseudoprimes — no deterministic general poly-time test.

## GRH status
- 2026-11-20: Alpöge + Claude claim a Lean proof of GRH (~17M lines); Masullo independent claim. Verification ongoing (see Tao blog, Lean Zulip).

## Key math
- Miller (1976): under GRH, n composite => some witness a < O((log n)^2).
- Bach (1990): explicit bound 2(ln n)^2.
- Needs: GRH for Dirichlet L-functions of characters mod n (not full GRH for all L-functions).

## Archive recon (2026-11-21) — rh-archive/ (shallow clone of CocoSgt/riemann-hypothesis-lean)
- Toolchain leanprover/lean4:v4.33.1, Mathlib pinned 0df444a360eaa60ab8c11dca51a86af692955474. 175,187 .lean files.
- src/Statements.lean: `DirichletLZerosOnLine` covers ALL chars mod N (not just primitive), zeros with 0<Re<1 -> Re=1/2. Good fit for Bach (needs chars mod n).
- No Bach / Ankeny / least-nonresidue results anywhere (0 hits).
- Reusable analytic lemmas exist, but ALL with existential constants (`∃ C`):
  - GlobalTheory.ExplicitFormula.truncated_explicit_formula (Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedExplicitFormula.lean):
    primitive χ mod N, |psi0 χ u + Σ_{|Im ρ|<T} u^ρ/ρ| ≤ C(u log²(NuT)/T + log(Nu) + Σ_{|Im ρ|<1} 1/|ρ|). C = C₁+C₂+C₃ from other ∃-lemmas.
  - GlobalTheory.Mem.An.ZeroCount: #zeros with |Im ρ - t| ≤ 1 is ≤ C log(q(|t|+2)), primitive χ. Proved in ZeroCountHolds.lean.
  - explicit_formula_right: error term has √u·q³ — useless for Bach (need u ~ log² q).
- Consequence: archive + GRH gives Ankeny-type "least witness ≤ C (log n)²" with an UNSPECIFIED C. Not runnable as-is.
  Options: (a) chase the ∃ witnesses to a numeral (likely huge but still poly-time); (b) prove Bach's smoothed explicit formula with explicit constants ourselves.
