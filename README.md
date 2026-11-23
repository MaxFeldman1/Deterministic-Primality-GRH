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

Lean statements are given without proofs. The GRH form lives in namespace `DetPrimality` (file
`lean/DetPrimality/EndToEnd.lean` unless noted) and takes `hGRH : DirichletLZerosOnLine`; the unconditional
form in `grh-bridge/GRHBridge.lean` is the same statement with no hypothesis. Shorthand used below:

```lean
-- every non-principal character mod n is ≠ 1 somewhere below c (ln n)²
def Bach.R11Bound (c : ℝ) (n : ℕ) : Prop :=
  ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 →
    ∃ a : ℕ, 1 ≤ a ∧ (a : ℝ) < c * Real.log n ^ 2 ∧ χ (a : ZMod n) ≠ 1
```

### Known mathematics, now machine-checked

| # | Result | Lean statement | Unconditional |
|---|---|---|---|
| 1 | Deterministic Miller–Rabin with about `(ln n)²` bases (constant 1 [LLS15, Thm 1.1]; Bach [Bac90] has 2, Miller [Mil76] an unspecified O(log² n)) | `theorem millerDet_correct_of_GRH (hGRH : DirichletLZerosOnLine) (n : ℕ) : Miller.millerDet 1 n = true ↔ n.Prime` | `millerDet_correct` |
| 2 | Deterministic Tonelli–Shanks [Sha73] with a non-residue search below about `(ln p)²` [LLS15, Cor 1.1] | `theorem sqrtModDet_correct_of_GRH (hGRH : DirichletLZerosOnLine) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (n : ℕ) : IsSquare (n : ZMod p) → ∃ r, TonelliShanks.sqrtModDet 1 p n = some r ∧ (r : ZMod p) ^ 2 = n` | `sqrtModDet_correct` |
| 3 | [LLS15, Thm 1.1(2)]: for `n ≥ 3000` every χ ≠ 1 mod n is ≠ 1 at some `a ≤ (ln n)²` (`Bach/LLSPrime.lean`) | `theorem Bach.llsPrime_bachBound_one_all_of_GRH (hGRH : DirichletLZerosOnLine) : ∀ n : ℕ, 3000 ≤ n → ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 → ∃ a : ℕ, 1 ≤ a ∧ (a : ℝ) < Real.log n ^ 2 ∧ χ (a : ZMod n) ≠ 1` | — |
| 4 | Strong liars lie in a subgroup of index ≥ 4 for odd composite `n ≠ 9` (structure behind the ¼ bound [Mon80, Rab80]; `Miller/LiarIndex.lean`, no GRH) | `theorem Miller.liar4_exists_subgroup {n : ℕ} (hn : 2 < n) (hodd : n % 2 = 1) (hnp : ¬ n.Prime) (h9 : n ≠ 9) : ∃ H : Subgroup (ZMod n)ˣ, 4 ≤ H.index ∧ ∀ x, IsStrongLiar n x → x ∈ H` | (no GRH needed) |

### New results

| # | Result | Lean statement | Unconditional |
|---|---|---|---|
| 5 | **Miller–Rabin, explicit constant below 1**: constant 0.7 for `n ≥ 10¹¹` (also 0.66 for `n ≥ 10¹²`, 0.65 for `n ≥ 10¹³`; subgroup table `subgroupBound_table_of_GRH`). Bach [Bac90] gives 2; nothing published gives below 1 for all large `n` (`research/barrier/miller4.md`) | `theorem millerDet_correct_of_GRH_70 (hGRH : DirichletLZerosOnLine) (n : ℕ) (hn : (10 : ℝ) ^ 11 ≤ n) : Miller.millerDet (7 / 10) n = true ↔ n.Prime` | `millerDet_70_correct` |
| 5′ | Combined test (constant 1 below `10¹¹`, `7/10` above), correct for all `n` | `theorem millerDetBest_correct_of_GRH (hGRH : DirichletLZerosOnLine) (n : ℕ) : millerDetBest n = true ↔ n.Prime` | `millerDetBest_correct` |
| 6 | **Miller–Rabin, asymptotic**: every `c > 0.6417` for all large `n`, for any subgroup of index ≥ 4 ([Bac90] states `1 + o(1)`; [LLS15, Thm 1.2]'s index-≥ 4 constant 0.66 was never applied to Miller) | `theorem subgroupBound_eventually_of_GRH (hGRH : DirichletLZerosOnLine) : ∀ c : ℝ, 0.6417 < c → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ H : Subgroup (ZMod n)ˣ, 4 ≤ H.index → ∃ a : ℕ, 1 ≤ a ∧ (a : ℝ) < c * Real.log n ^ 2 ∧ (¬ IsUnit (a : ZMod n) ∨ ∃ u : (ZMod n)ˣ, (u : ZMod n) = a ∧ u ∉ H)` | `subgroupBound_eventually` |
| 7 | **Single character, explicit uniform constant below 1**: c = 0.95, 0.9, 0.85, 0.8, 0.78 for n ≥ 10⁹, 10¹⁰, 10¹¹, 10¹³, 10¹⁴ (previous best for all large n: 1 [LLS15, Thm 1.1]; [Bac90, Table 1] dips below 1 only on finite ranges) | `theorem charBound_table_of_GRH (hGRH : DirichletLZerosOnLine) : (∀ n : ℕ, (10 : ℝ) ^ 9 ≤ n → Bach.R11Bound 0.95 n) ∧ (∀ n : ℕ, (10 : ℝ) ^ 10 ≤ n → Bach.R11Bound 0.9 n) ∧ (∀ n : ℕ, (10 : ℝ) ^ 11 ≤ n → Bach.R11Bound 0.85 n) ∧ (∀ n : ℕ, (10 : ℝ) ^ 13 ≤ n → Bach.R11Bound 0.8 n) ∧ (∀ n : ℕ, (10 : ℝ) ^ 14 ≤ n → Bach.R11Bound 0.78 n)` | `charBound_table` |
| 8 | Single character: every `c > 0.7772` eventually, kernel `6/(s+1)⁴` with an exact zero-sum identity (`research/below-one/designB.md`) | `theorem charBound_eventually_of_GRH (hGRH : DirichletLZerosOnLine) : ∀ c : ℝ, 0.7772 < c → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Bach.R11Bound c n` | `charBound_eventually` |
| 9 | **Single character, asymptotic record**: every `c > 0.760753` eventually, improving 0.7615 [CMQR24, Thm 1] (LLS's own constant: 0.794 [LLS15, Thm 1.2]); exact-modulus kernels with three sign changes (`research/barrier/formal0760.md`) | `theorem charBound_record_tight_of_GRH (hGRH : DirichletLZerosOnLine) : ∀ c : ℝ, 0.760753 < c → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Bach.R11Bound c n` | `charBound_record_tight` |
| 10 | **Framework limit**: the extremal problem (EP1) of [CMQR24] has `C(1) ≤ 1.146514`, so the method cannot prove any constant below 0.760748 (their stated barrier [CMQR24, Thm 2]: 0.7596). With 9: the limit is in `[0.760748, 0.760753]` (`Barrier/dual2_Main.lean`, no GRH) | `theorem Barrier.dual2_EP1_le {F : ℝ → ℂ} (hF : Integrable F) (hreal : ∀ t, (𝓕 F t).im = 0) (hint : IntegrableOn (fun t => (𝓕 F t).re * Real.exp (π * t)) (Ioi 0)) : 2 * π * ((∫ t in Iic 0, (𝓕 F t).re * Real.exp (π * t)) - ∫ t in Ioi 0, \|(𝓕 F t).re\| * Real.exp (π * t)) ≤ 1.146514 * ∫ x, ‖F x‖`  and  `theorem Barrier.dual2_barrier : (0.760748 : ℝ) ≤ ((1.146514 : ℝ) ^ 2)⁻¹` | (no GRH needed) |
| 11 | **Nehari barrier** (after [Neh57]): kernels with all support in the counted range give `c ≥ 1` (`Barrier/Nehari.lean`, no GRH) | `theorem neh_barrier {φ : ℝ → ℂ} (hc : Continuous φ) (hφ : Integrable φ) (hs : ∀ v, 0 < v → φ v = 0) (hL : Integrable fun t : ℝ => neh_K φ (t * I)) (hK : neh_K φ (1 / 2) ≠ 0) : 1 ≤ ((1 / (2 * π) * ∫ t : ℝ, ‖neh_K φ (t * I)‖) / ‖neh_K φ (1 / 2)‖) ^ 2` | (no GRH needed) |

Here `neh_K φ s = ∫ v, φ v * exp (s * v)` and `𝓕` is Mathlib's Fourier transform.

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
