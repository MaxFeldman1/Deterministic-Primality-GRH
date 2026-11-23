# Deterministic primality testing and modular square roots, verified in Lean 4

This repository contains a Lean 4 / Mathlib formalization of two deterministic algorithms whose
correctness depends on the Generalized Riemann Hypothesis (GRH) for Dirichlet L-functions:

* **Deterministic Miller–Rabin.** `millerDet 1 n` tests `n` against every base
  `2 ≤ a < ⌈0.480454 · (log₂ n + 1)²⌉`, which is about `(ln n)²` bases. It returns `true` exactly
  when `n` is prime.
* **Deterministic Tonelli–Shanks.** `sqrtModDet 1 p n` searches for a quadratic non-residue below
  about `(ln p)²`, then computes a square root of `n` modulo the odd prime `p`. It returns a root
  exactly when one exists.

The constant `c = 1` in both bounds is the best published explicit constant. It comes from
Lamzouri, Li and Soundararajan (2015), and it improves on Bach's `c = 2` (1990).

## Main theorems

### Conditional on GRH (this project alone)

In `lean/DetPrimality/EndToEnd.lean`. `DirichletLZerosOnLine` is GRH for all Dirichlet L-functions,
including ζ, as defined in `lean/Statements.lean`.

```lean
theorem DetPrimality.millerDet_correct_of_GRH (hGRH : DirichletLZerosOnLine) (n : ℕ) :
    Miller.millerDet 1 n = true ↔ n.Prime

theorem DetPrimality.sqrtModDet_correct_of_GRH (hGRH : DirichletLZerosOnLine) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (n : ℕ) :
    IsSquare (n : ZMod p) → ∃ r, TonelliShanks.sqrtModDet 1 p n = some r ∧ (r : ZMod p) ^ 2 = n
```

### Constants below 1 (new results, Rounds 11–12)

Produced by AI agents (see `research/below-one/`, `research/barrier/`); all are proved in Lean under GRH
(`EndToEnd.lean`) and unconditionally via the bridge (`grh-bridge/GRHBridge.lean`):

* **Single character** (`charBound_table_of_GRH`, `charBound_eventually_of_GRH`): every Dirichlet character
  χ ≠ 1 mod n has χ(a) ≠ 1 for some `1 ≤ a < c (ln n)²`, with c = 0.95, 0.9, 0.85, 0.8, 0.78 for
  n ≥ 10⁹, 10¹⁰, 10¹¹, 10¹³, 10¹⁴, and every c > 0.7772 for all large n. The best published explicit
  constant valid for all large n was 1 (Lamzouri–Li–Soundararajan 2015).
  Kernel `6/(s+1)⁴`, whose sum over zeros is an exact identity (`research/below-one/designB.md`).
* **Miller–Rabin** (`millerDet_correct_of_GRH_70`, `millerDetBest_correct_of_GRH`, `subgroupBound_*`): strong
  liars lie in a subgroup of index ≥ 4 (`Miller.liar4_exists_subgroup`, n ≠ 9). Averaging over the four
  characters gives `millerDet (7/10)` correct for n ≥ 10¹¹ (0.66 for n ≥ 10¹², 0.65 for n ≥ 10¹³), and every
  c > 0.6417 for all large n. Bach (1990) gives 2.

### Running time (unconditional)

In `lean/DetPrimality/Complexity/`. The base loop is bounded by construction, so these theorems do
not use GRH.

* `cx_millerDet_modmul_count`: the test performs at most `(log₂ n + 1)³` multiplications mod `n`.
* `cx_millerDet_bit_cost`: a bit-level implementation, using schoolbook multiply and
  shift-subtract remainder with every constant-size bit step charged, computes `millerDet 1 n` in
  at most `31 · (log₂ n + 1)⁵` bit operations.
* `cx_millerDet_bit_cost_generic`: the same bound for any multiplication algorithm with cost `M`:
  `(log₂ n + 1)³ · M(log₂ n + 1) + 4 (log₂ n + 1)⁴`.

### Unconditional, via the GRH archive

In `grh-bridge/GRHBridge.lean`. This file imports Levent Alpöge's Lean proof of GRH (mirror:
[CocoSgt/riemann-hypothesis-lean](https://github.com/CocoSgt/riemann-hypothesis-lean)) and
instantiates the hypothesis with its `LFunction_eq_zero_re : DirichletLZerosOnLine`:

```lean
theorem millerDet_correct (n : ℕ) : DetPrimality.Miller.millerDet 1 n = true ↔ n.Prime
theorem millerDetBits_correct (n : ℕ) :
    ((cx_millerDetBits n).1 = true ↔ n.Prime) ∧ (cx_millerDetBits n).2 ≤ 31 * (Nat.log2 n + 1) ^ 5
theorem sqrtModDet_correct ...
theorem sqrtModDet_isSome_iff ...
```

`#print axioms` reports only `[propext, Classical.choice, Quot.sound]` for every theorem above.

**Trust.** The archive is a *claimed* proof of RH and GRH, announced 2026-11-20, and no independent
review had been published as of 2026-11-23. We checked the following:

* It builds: 175,187 modules, 0 errors.
* Its main theorems use only the standard axioms.
* Its source contains no `axiom`, `sorry`, `native_decide`, `unsafe`, `implemented_by`/`extern`
  or kernel options.
* A `leanchecker` replay of every module of the archive and of this project is in progress; see
  `STATUS.md`.

The unconditional theorems are as trustworthy as that archive, the Lean kernel, and Mathlib's
definitions of `riemannZeta` and `DirichletCharacter.LFunction`.

## How the proof works

1. **Characters.** If `n` is composite, the strong liars lie in a proper subgroup of `(ℤ/n)ˣ`.
   So it suffices to show that every non-trivial Dirichlet character `χ` mod `n` has
   `χ(a) ≠ 1` for some small `a` (`Miller/`, `Characters/`).
2. **Explicit formulas under GRH.** Suppose `χ(a) = 1` for all `a < X = (log n)²`. Compare upper
   and lower bounds for `Re Σ_{m≤X} Λ(m) χ(m) log(X/m)`. Lamzouri–Li–Soundararajan,
   Theorem 1.1(2), gives these bounds:
   * Lemma 1: RH lower bound for `Σ Λ(m) log(X/m)`, via the Hadamard product of `ξ(s)`
     (`Bach/LLSZeta*.lean`).
   * Lemma 2: upper bound for a primitive `χ` via a Perron integral with kernel `x^s/s²`
     (`Bach/LLSPerron*.lean`).
   * Lemma 3: zero-sum bound with the "χ = 1 below X" gain (`Bach/LLSGain*.lean`).
   * Lemma 4: unconditional weighted bound for `Λ(m)/m` (`Bach/LLSElem.lean`).

   The bounds contradict each other for `n ≥ 3000` (`Bach/LLSAssembly.lean`,
   `Bach/LLSPrime.lean`).
3. **Small inputs.** For `n < 3000`, kernel-checked `decide +kernel` tables
   (`Miller/LLSSmall.lean`, `TonelliShanks/LLSSqrt.lean`).

Earlier rounds proved weaker constants by Bach's method: 1024, 64, 46, 22, 8, and 73/50 for
composite moduli. Those proofs are kept in `Bach/` with suffixed theorem names in `EndToEnd.lean`.
`STATUS.md` has the round-by-round history.

## Layout

| Path | Contents |
|---|---|
| `lean/Statements.lean` | The four GRH/RH statements; a byte-identical copy of the archive's `src/Statements.lean` |
| `lean/DetPrimality/GRHStatements.lean`, `Interfaces.lean`, `CompositeInterface.lean` | Statement layer |
| `lean/DetPrimality/Miller/` | `sprp`, `millerDet`, strong-liar subgroup, correctness from a witness bound |
| `lean/DetPrimality/TonelliShanks/` | `sqrtModDet` and its correctness |
| `lean/DetPrimality/Bach/` | Analytic number theory: Hadamard factorization, explicit formulas, zero sums, constants |
| `lean/DetPrimality/Complexity/` | Running-time bounds |
| `lean/DetPrimality/EndToEnd.lean` | The composed theorems |
| `lean/DetPrimality/Audit.lean` | `#print axioms` for all main results |
| `grh-bridge/` | Unconditional corollaries using the GRH archive |
| `blueprint/BACH_BLUEPRINT.md`, `NOTES.md`, `STATUS.md` | Blueprint, research notes, status log |

## Building

Requirements: Lean `v4.33.1` and Mathlib at commit `0df444a3` (pinned in `lean/lakefile.toml`).
Use the Mathlib cache; do not build Mathlib from source.

```bash
cd lean
lake exe cache get      # download prebuilt Mathlib
lake build              # builds DetPrimality (~8,800 jobs, almost all from the cache)
lake env lean DetPrimality/Audit.lean   # axiom report
```

`bin/check.sh` and `bin/check_bridge.sh` are the scripts used during development. They sync to a
remote build machine and compile there, so adapt the host name before using them.

The bridge needs a built copy of the GRH archive (about 1.1 TB of build output, roughly a day on
192 cores). `bin/check_bridge.sh` then compiles `grh-bridge/GRHBridge.lean` against both sets of
`.olean` files.

## References

* G. L. Miller, *Riemann's hypothesis and tests for primality*, J. Comput. System Sci. 13 (1976).
* M. O. Rabin, *Probabilistic algorithm for testing primality*, J. Number Theory 12 (1980).
* E. Bach, *Explicit bounds for primality testing and related problems*, Math. Comp. 55 (1990).
* Y. Lamzouri, X. Li, K. Soundararajan, *Conditional bounds for the least quadratic non-residue
  and related problems*, Math. Comp. 84 (2015); arXiv:1309.3595.
* K. Conrad, *The Miller–Rabin test* (expository notes).
