# Deterministic primality testing and least non-residues under GRH, verified in Lean 4

A Lean 4 / Mathlib formalization of deterministic Miller–Rabin and deterministic Tonelli–Shanks,
proved correct under the Generalized Riemann Hypothesis (GRH) for Dirichlet L-functions, plus several
new explicit and asymptotic bounds for the least character non-residue and the least Miller–Rabin
witness. Every theorem below is proved in Lean:

* **conditionally**, assuming `DirichletLZerosOnLine` (GRH for all Dirichlet L-functions including ζ,
  `lean/Statements.lean`), in `lean/DetPrimality/EndToEnd.lean` and `lean/DetPrimality/Barrier/`;
* **unconditionally**, by plugging in the GRH proof of the Alpöge archive [Alp26], in
  `grh-bridge/GRHBridge.lean`.

`#print axioms` reports only `[propext, Classical.choice, Quot.sound]` for every theorem listed.

The new mathematics (results 5–11) was produced by AI agents with little human mathematical guidance;
the designs, referee reports and literature checks are in `research/`.

## Results

### Known mathematics, now machine-checked

1. **Deterministic Miller–Rabin with constant 1.** `millerDet 1 n` tests every base
   `2 ≤ a < ⌈0.480454·(log₂ n + 1)²⌉` (about `(ln n)²` bases) and returns `true` exactly when `n` is
   prime, for every `n`. This is the constant of [LLS15, Thm 1.1]; Bach [Bac90] has 2, Miller's original
   test [Mil76] an unspecified O(log² n).
   `millerDet_correct_of_GRH` (bridge: `millerDet_correct`).
2. **Deterministic Tonelli–Shanks with constant 1.** `sqrtModDet 1 p n` searches for a quadratic
   non-residue below about `(ln p)²` and returns a square root of `n` mod the odd prime `p` exactly when
   one exists ([LLS15, Cor 1.1]; Tonelli–Shanks [Sha73]). `sqrtModDet_correct_of_GRH`, `sqrtModDet_isSome_iff_of_GRH`.
3. **[LLS15, Theorem 1.1(2)].** For every `n ≥ 3000`, every character `χ ≠ 1` mod `n` has `χ(a) ≠ 1`
   for some `1 ≤ a ≤ (ln n)²`. `bachBoundComposite_one_ge_3000_of_GRH`, `Bach.llsPrime_bachBound_one_all_of_GRH`.
4. **Strong liars lie in a subgroup of index ≥ 4** for every odd composite `n ≠ 9` (the structure
   behind the ¼ bound of Monier [Mon80] and Rabin [Rab80]). `Miller.liar4_exists_subgroup` (unconditional).

### New results

Least Miller–Rabin witness:

5. **Explicit constant below 1.** `millerDet (7/10) n` is correct for every `n ≥ 10¹¹`, with further
   rows 0.75 and 0.72 (`n ≥ 10¹⁰`), 0.68 (`n ≥ 10¹¹`), 0.66 (`n ≥ 10¹²`), 0.65 (`n ≥ 10¹³`)
   (`research/barrier/miller4.md`).
   `millerDetBest` (constant 1 below `10¹¹`, `7/10` above) is correct for all `n`. Nothing published
   gives a Miller–Rabin constant below 1 for all large `n`.
   `millerDet_correct_of_GRH_70`, `_66`, `_65`, `millerDetBest_correct_of_GRH`, `subgroupBound_table_of_GRH`
   (bridge: `millerDet_70_correct`, `millerDetBest_correct`).
6. **Asymptotic.** Every `c > 0.6417` works for all large `n` (index ≥ 4, averaging over the four
   characters; [Bac90] states `1 + o(1)`, and the index-≥ 4 constant 0.66 of [LLS15, Thm 1.2] was never
   applied to Miller).
   `subgroupBound_eventually_of_GRH` (bridge: `subgroupBound_eventually`).

Least `n` with `χ(n) ≠ 1` for a single non-principal character (worst case: least quadratic non-residue):

7. **Explicit uniform constant below 1.** `c = 0.95, 0.9, 0.85, 0.8, 0.78` for all `n ≥ 10⁹, 10¹⁰,
   10¹¹, 10¹³, 10¹⁴`. The best published explicit constant valid for all large `n` was 1 [LLS15, Thm 1.1];
   the tables of [Bac90, Table 1] dip below 1 only on finite ranges (`research/barrier/bach_check.md`). `charBound_table_of_GRH` (bridge: `charBound_table`).
8. **Every `c > 0.7772` eventually**, from the kernel `6/(s+1)⁴`, whose sum over zeros is an exact
   identity (`research/below-one/designB.md`). `charBound_eventually_of_GRH`.
9. **Asymptotic record.** Every `c > 0.760753` works for all large `n`, improving 0.7615 of
   [CMQR24, Thm 1]; the asymptotic constant of [LLS15, Thm 1.2] is 0.794. Exact-modulus kernels
   `K = Q((s−1)²)·H₀(s)²` with three exact sign changes (`research/barrier/formal0760.md`).
   `charBound_record_tight_of_GRH` (bridge: `charBound_record_tight`); earlier steps `charBound_record_of_GRH`
   (0.7612), `charBound_record076_of_GRH` (0.76076).

Limits of the method:

10. **Framework limit.** The extremal problem (EP1) of [CMQR24] satisfies `C(1) ≤ 1.146514`, so their framework cannot
    prove any constant below **0.760748** (their stated barrier [CMQR24, Thm 2]: 0.7596). Together with result 9, the
    method's true limit lies in `[0.760748, 0.760753]`. `Barrier.dual2_EP1_le`, `Barrier.dual2_barrier`
    (no GRH needed: a statement about the extremal problem).
11. **Nehari barrier** (after Nehari's theorem on Hankel forms [Neh57]). One-sided kernels whose support lies entirely in the counted range satisfy
    `K(½) ≤ (1/2π)∫|K(it)| dt`, so they can never give `c < 1`. `neh_nehari_line`, `neh_barrier`.

### Informal only (not formalized)

* A "no-go" scenario suggesting that no GRH-only explicit-formula argument beats ≈ 0.7607 for quadratic
  characters (`research/barrier/beyond.md`). It is a claim about proof methods, not a theorem; the true
  least non-residue is believed to be about `log q · log log q` [Mon71].
* Literature checks (`research/`): GRH-Miller is the best proven deterministic primality route; GRH
  non-residue search + Tonelli–Shanks is the best known deterministic square-root route; Bach (1990) has no
  index-based or uniform below-1 bound; the best unconditional deterministic test is
  `(log n)^{6+o(1)}` [LP19]. These searches were not exhaustive; an expert should confirm novelty.

## Running time (separate from the results above)

In `lean/DetPrimality/Complexity/`, unconditional (the number of bases is bounded by the code), for
`millerDet 1`, with `L = log₂ n + 1` and a bit-level cost model in which every constant-size bit step
on little-endian bit lists costs 1:

* `cx_millerDetFast_eq`: an efficient variant (one `a^d`, then squarings) returns exactly `millerDet 1 n`.
* `cx_millerDet_modmul_count`: at most `L³` modular multiplications.
* `cx_millerDet_bit_cost`: schoolbook multiply and remainder, at most `31·L⁵` bit operations.
* `cx_millerDet_bit_cost_generic`: with any multiplier of cost `M`, at most `L³·M(L) + 4L⁴`.
* `kx_millerDet_bit_cost_karatsuba_real`: Karatsuba [KO62] with Barrett reduction [Bar86], at most
  `687·L^4.585`.

These do not reach the best known bit complexity `(log n)^{4+o(1)}`, which needs near-linear
multiplication [HvdH21] (not formalized). Not charged: computing the base budget (a function of the bit length)
and converting `n` to bits. No running time is proved for Tonelli–Shanks or for `millerDetBest`.

## Trust

The unconditional theorems depend on the Alpöge archive (mirror:
[CocoSgt/riemann-hypothesis-lean](https://github.com/CocoSgt/riemann-hypothesis-lean)), a claimed
Lean proof of RH and GRH announced 2026-11-20 [Alp26]. We checked:

* It builds with the same Lean (v4.33.1) and Mathlib (`0df444a3`) as this project: 175,187 modules,
  0 errors.
* Its main theorems, including `LFunction_eq_zero_re : DirichletLZerosOnLine`, use only the standard axioms.
* Its source contains no `axiom`, `sorry`, `native_decide`, `unsafe`, `implemented_by`/`extern` or
  kernel options; the only environment-modifying commands are five `run_cmd` lines that edit a
  library-suggestion deny list.
* `lean/Statements.lean` is a byte-identical copy of the archive's `src/Statements.lean` (sha256
  `79ef7ca7…`), so `DirichletLZerosOnLine` is literally the same constant in both projects.

A full independent kernel replay of the archive (`leanchecker --fresh`) was started and stopped by
decision; this project's own modules were replayed with `leanchecker` (all pass). The unconditional
theorems are as trustworthy as the archive, the Lean kernel, and Mathlib's definitions of `riemannZeta`
and `DirichletCharacter.LFunction`.

## How the proofs work

1. **Characters.** If `n` is composite, the strong liars lie in a proper subgroup of `(ℤ/n)ˣ` (of index
   ≥ 4 for `n ≠ 9`), so it suffices that every non-trivial character trivial on it has `χ(a) ≠ 1` for some
   small `a` (`Miller/`, `Characters/`).
2. **Explicit formulas under GRH.** Assume `χ(a) = 1` for all `a < X`, weight prime powers below
   `x = λ⁻¹X` by a kernel, and compare a lower bound (prime side, RH for ζ) with an upper bound (zero
   side, GRH for `χ`):
   * c = 1: the log-kernel argument of [LLS15, §3] (`Bach/LLS*.lean`).
   * Explicit c < 1: kernel `6/(s+1)⁴` with an exact zero-sum identity at `s = 3/2` and the hypothesis
     reused inside the zero sum (`Bach/R11*.lean`); index ≥ 4 by averaging over the characters trivial on
     the subgroup (`Bach/R12*.lean`).
   * Records: exact-modulus kernels `Q((s−1)²)·H₀²` with a polynomial certificate (`Bach/R13*.lean`,
     `Bach/R14*.lean`).
3. **Small inputs** by kernel-checked tables (`Miller/LLSSmall.lean`, `TonelliShanks/LLSSqrt.lean`).
4. **Barriers** by Fourier analysis: weak duality with a kernel-checked dual function (`Barrier/dual2_*`)
   and the Nehari inequality (`Barrier/Nehari.lean`).

Earlier rounds proved weaker constants by Bach's method [Bac90] (1024, 64, 46, 22, 8, 73/50); they are kept with
suffixed names in `EndToEnd.lean`. `STATUS.md` has the round-by-round history.

## Layout

| Path | Contents |
|---|---|
| `lean/Statements.lean` | The four GRH/RH statements (byte-identical copy of the archive's) |
| `lean/DetPrimality/Miller/`, `TonelliShanks/`, `Characters/` | Algorithms, liar subgroups, small-n tables |
| `lean/DetPrimality/Bach/` | Analytic number theory: Hadamard, explicit formulas, zero sums, certificates |
| `lean/DetPrimality/Barrier/` | Framework limit (dual certificate) and the Nehari barrier |
| `lean/DetPrimality/Complexity/` | Running-time bounds |
| `lean/DetPrimality/EndToEnd.lean`, `Audit.lean` | Composed theorems; `#print axioms` for all of them |
| `grh-bridge/` | Unconditional corollaries via the GRH archive |
| `research/` | Designs, referee reports, literature checks, certificate generators |
| `blueprint/`, `NOTES.md`, `STATUS.md` | Early blueprint, research notes, status log |

## Building

Requirements: Lean `v4.33.1` and Mathlib at commit `0df444a3` (pinned in `lean/lakefile.toml`).
Use the Mathlib cache; do not build Mathlib from source.

```bash
cd lean
lake exe cache get      # download prebuilt Mathlib
lake build              # builds DetPrimality (~8,900 jobs, almost all from the cache)
lake env lean DetPrimality/Audit.lean   # axiom report
```

`bin/check.sh` and `bin/check_bridge.sh` are the development scripts; they sync to a remote build machine,
so adapt the host name. The bridge needs a built copy of the GRH archive (about 1.1 TB of build output,
roughly a day on 192 cores).

## References

* [Alp26] L. Alpöge, announcement of a Lean proof of RH and GRH (2026-11-20), https://alpo.ge/remark.pdf;
  code mirror https://github.com/CocoSgt/riemann-hypothesis-lean.
* [Bac90] E. Bach, *Explicit bounds for primality testing and related problems*, Math. Comp. 55 (1990), 355–380.
* [Bar86] P. Barrett, *Implementing the Rivest Shamir and Adleman public key encryption algorithm on a standard
  digital signal processor*, CRYPTO '86, LNCS 263 (1987).
* [CMQR24] E. Carneiro, M. B. Milinovich, E. Quesada-Herrera, A. P. Ramos, *Fourier optimization, the least
  quadratic non-residue, and the least prime in an arithmetic progression*, arXiv:2404.08380 (2024).
* [HvdH21] D. Harvey, J. van der Hoeven, *Integer multiplication in time O(n log n)*, Ann. of Math. 193 (2021).
* [KO62] A. Karatsuba, Yu. Ofman, *Multiplication of many-digital numbers by automatic computers*, Dokl. Akad.
  Nauk SSSR 145 (1962).
* [LLS15] Y. Lamzouri, X. Li, K. Soundararajan, *Conditional bounds for the least quadratic non-residue and
  related problems*, Math. Comp. 84 (2015), 2391–2412; corrigendum Math. Comp. 86 (2017); arXiv:1309.3595.
* [LP19] H. W. Lenstra Jr., C. Pomerance, *Primality testing with Gaussian periods*, J. Eur. Math. Soc. 21 (2019).
* [Mil76] G. L. Miller, *Riemann's hypothesis and tests for primality*, J. Comput. System Sci. 13 (1976), 300–317.
* [Mon71] H. L. Montgomery, *Topics in Multiplicative Number Theory*, Lecture Notes in Math. 227, Springer (1971).
* [Mon80] L. Monier, *Evaluation and comparison of two efficient probabilistic primality testing algorithms*,
  Theoret. Comput. Sci. 12 (1980), 97–108.
* [Neh57] Z. Nehari, *On bounded bilinear forms*, Ann. of Math. 65 (1957), 153–162.
* [Rab80] M. O. Rabin, *Probabilistic algorithm for testing primality*, J. Number Theory 12 (1980), 128–138.
* [Sha73] D. Shanks, *Five number-theoretic algorithms*, Proc. Second Manitoba Conf. Numer. Math. (1973).
* K. Conrad, *The Miller–Rabin test* (expository notes) — a readable introduction.
