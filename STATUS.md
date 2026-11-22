# STATUS — Lean-verified deterministic primality / sqrt mod p under GRH

Integration review on 2026-11-21. Toolchain: Lean v4.33.1, Mathlib `0df444a3`.

## Build

- `bin/check.sh --build` **succeeds**: 8716 jobs, `Build completed successfully`.
- **Mathlib was not rebuilt.** Before building, `lake build --no-build Mathlib` on the box reported `All targets up-to-date (8705 jobs)`. Mathlib therefore comes from the existing cache, and only the `DetPrimality` modules were compiled, each in about 4–10 s.
- **The only warnings** are the 4 `declaration uses 'sorry'` in `Bach/Blueprint.lean`, at lines 48, 58, 70 and 83.
- **No agent code needed fixing.** The earlier "Interfaces.olean does not exist" failures came only from the library never having been built.
- **Every file now compiles as written,** without the inlined copies the agents used.
- **`lean/DetPrimality.lean` imports every module:** GRHStatements, Interfaces, Characters.Bridge, Bach.Blueprint, Miller.Basic, Miller.Examples, TonelliShanks.Basic, TonelliShanks.Examples, EndToEnd.
- **New files (integration):**
  - `lean/DetPrimality/EndToEnd.lean`: the composed GRH ⟹ algorithm theorems. It is in the library.
  - `lean/DetPrimality/Audit.lean`: the `#print axioms` checks. It is not imported by the library; run it with `bin/check.sh DetPrimality/Audit.lean`.
- **GRH archive cache:** `rh-archive` (CocoSgt/riemann-hypothesis-lean) has no `.lake`/olean cache and no published build. Importing it would mean building that dependency cone from source, on top of the cached Mathlib at the same pin. It is **not** a dependency now; nothing in the build uses it.

## Per-layer status

| Layer | Content | File | Status |
|---|---|---|---|
| 0 | Statements: `DirichletLZerosOnLine` etc., `BachBound`, `BachBoundChar`, `GRHImpliesBach` | `GRHStatements.lean`, `Interfaces.lean` | Done (unchanged) |
| 1 | Character ↔ subgroup bridge; `BachBound c ↔ BachBoundChar c`; nonresidue corollaries | `Characters/Bridge.lean` | **Done, 0 sorry** |
| 2 | GRH ⟹ Bach with c = 1024 | `Bach/Blueprint.lean` | **Assembled, 4 sorries** (listed below) |
| 3 | Strong liars lie in a proper subgroup for odd composite n | `Miller/Basic.lean` | **Done, 0 sorry** |
| 4a | Deterministic Miller test `millerDet`, correct given `BachBound c` | `Miller/Basic.lean` | **Done, 0 sorry** |
| 4b | Deterministic Tonelli–Shanks `sqrtModDet`, correct given `BachBound c` | `TonelliShanks/Basic.lean` | **Done, 0 sorry** |
| — | End-to-end composition | `EndToEnd.lean` | **Done** (inherits the Layer 2 sorries) |
| — | Running-time (poly-time) proofs | — | **Missing** (not started) |

### Remaining sorries, all in `Bach/Blueprint.lean`, namespace `DetPrimality.Bach`

The first three are unconditional (no GRH) and assume `χ` is primitive with `χ ≠ 1`.

1. **DEEP — `summable_zeroOrd_div_normSq` (l.48):** `Summable fun ρ : ℂ => (zeroOrd χ ρ : ℝ) / ‖ρ‖ ^ 2`.
   - Needs Jensen zero counting, or order-1 Hadamard theory, for `completedLFunction χ`.
   - The archive's `ZeroCount` would discharge it.
2. **DEEP — `re_logDeriv_eq_tsum` (l.58):** for `1 < s.re`,
   `(L'/L + gammaFactor'/gammaFactor)(s).re = -(log q)/2 + ∑' ρ, zeroOrd χ ρ * Re(1/(s-ρ))`.
   - Needs Hadamard factorisation of `completedLFunction χ` and `Re B(χ)` via the functional equation.
   - I checked the normalisation against Davenport ch. 12: Mathlib's `gammaFactor` is `Gammaℝ(s)` or `Gammaℝ(s+1)`, with no `q^{s/2}`, so the `-(log q)/2` is correct.
3. **DEEP — `explicit_formula_bound` (l.70):** for `x ≥ 1`, Bach's smoothed explicit formula (kernel `1/(s(s+1))`, re-centred at s = 2) holds with Γ-term error `≤ log x + 4`.
   - Needs a Perron/Mellin inversion, the Hadamard partial fraction, the digamma series and termwise integration.
   - Review check: at x = 1 the left side is exactly 0, because `1/(ρ(ρ+1)) − 2/(ρ(2−ρ)) + 3/((ρ+1)(2−ρ)) = 0`. That is consistent.
   - I did **not** independently re-derive the general-x Γ-term bound. It comes from blueprint §3.
4. **NUM — `tsum_vonMangoldt_term_two_le` (l.83):** `∑' n, ‖LSeries.term Λ 2 n‖ ≤ 1`.
   - The true value is −ζ'/ζ(2) ≈ 0.5699, so the statement is true but the suggested proof is tight (0.995).
   - If only ≤ 3/2 is proved, some constants in `zeroSum_le` need retuning (blueprint §4.1a).

Each sorry has a docstring explaining what is missing. There is no `axiom`, `native_decide` or `admit` anywhere.

## End-to-end theorem chain (exact Lean)

```lean
-- Layer 0 (Interfaces.lean / GRHStatements.lean)
def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
def BachBound (c : ℝ) : Prop :=
  ∀ n : ℕ, 2 < n → ∀ H : Subgroup (ZMod n)ˣ, H ≠ ⊤ →
    ∃ a : (ZMod n)ˣ, a ∉ H ∧ (((a : ZMod n).val : ℕ) : ℝ) < c * (Real.log n) ^ 2
def GRHImpliesBach (c : ℝ) : Prop := DirichletLZerosOnLine → BachBound c

-- Layer 2 (Bach/Blueprint.lean)  [4 sorries]
theorem DetPrimality.Bach.bachBoundChar_of_GRH (hGRH : DirichletLZerosOnLine) : BachBoundChar 1024
theorem DetPrimality.Bach.bachBound_of_bachBoundChar {c : ℝ} (h : BachBoundChar c) : BachBound c
theorem DetPrimality.Bach.grh_implies_bach : GRHImpliesBach 1024

-- Layer 1 (Characters/Bridge.lean)  [sorry-free]
theorem DetPrimality.bachBound_iff_bachBoundChar (c : ℝ) : BachBound c ↔ BachBoundChar c

-- Layers 3-4 (Miller/Basic.lean)  [sorry-free]
def millerBound (c : ℚ) (n : ℕ) : ℕ := ⌈c⌉₊ * (Nat.log2 n + 1) ^ 2
def millerDet (c : ℚ) (n : ℕ) : Bool :=
  if n < 2 then false else if n = 2 then true else if n % 2 = 0 then false
  else (List.range' 2 (min (millerBound c n) n - 2)).all (fun a => sprp n a)
theorem DetPrimality.Miller.exists_proper_subgroup_strongLiars {n : ℕ} (hn : 2 < n)
    (hodd : n % 2 = 1) (hnp : ¬ n.Prime) :
    ∃ H : Subgroup (ZMod n)ˣ, H ≠ ⊤ ∧ ∀ x, IsStrongLiar n x → x ∈ H
theorem DetPrimality.Miller.millerDet_correct (c : ℚ) (hc : 0 < c) (hB : BachBound (c : ℝ)) (n : ℕ) :
    millerDet c n = true ↔ n.Prime

-- Layer 4 (TonelliShanks/Basic.lean)  [sorry-free]
theorem DetPrimality.TonelliShanks.sqrtModDet_correct {c : ℚ} (hB : BachBound (c : ℝ)) (hc : 0 < c)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (n : ℕ) :
    IsSquare (n : ZMod p) → ∃ r, sqrtModDet c p n = some r ∧ ((r : ZMod p)) ^ 2 = n
theorem DetPrimality.TonelliShanks.sqrtModDet_sound {c : ℚ} {p n r : ℕ}
    (h : sqrtModDet c p n = some r) : (r : ZMod p) ^ 2 = n            -- unconditional

-- End-to-end (EndToEnd.lean)  [inherits the Layer 2 sorries]
theorem DetPrimality.bachBound_1024_of_GRH (hGRH : DirichletLZerosOnLine) : BachBound ((1024 : ℚ) : ℝ)
theorem DetPrimality.millerDet_correct_of_GRH (hGRH : DirichletLZerosOnLine) (n : ℕ) :
    Miller.millerDet 1024 n = true ↔ n.Prime
theorem DetPrimality.sqrtModDet_correct_of_GRH (hGRH : DirichletLZerosOnLine) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (n : ℕ) :
    IsSquare (n : ZMod p) → ∃ r, TonelliShanks.sqrtModDet 1024 p n = some r ∧ (r : ZMod p) ^ 2 = n
theorem DetPrimality.sqrtModDet_isSome_iff_of_GRH (hGRH : DirichletLZerosOnLine) (p : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (n : ℕ) :
    (TonelliShanks.sqrtModDet 1024 p n).isSome ↔ IsSquare (n : ZMod p)
```

## Axioms (`bin/check.sh DetPrimality/Audit.lean`, verbatim)

```
'DetPrimality.millerDet_correct_of_GRH' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'DetPrimality.sqrtModDet_correct_of_GRH' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'DetPrimality.sqrtModDet_isSome_iff_of_GRH' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'DetPrimality.Bach.grh_implies_bach' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'DetPrimality.Bach.bachBoundChar_of_GRH' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'DetPrimality.Bach.bachBound_of_bachBoundChar' depends on axioms: [propext, Classical.choice, Quot.sound]
'DetPrimality.Bach.zeroSum_le' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'DetPrimality.Bach.norm_smoothPsi_le' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'DetPrimality.Bach.re_smoothPsi_primitive_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'DetPrimality.bachBound_iff_bachBoundChar' depends on axioms: [propext, Classical.choice, Quot.sound]
'DetPrimality.exists_dirichletCharacter_trivial_on' depends on axioms: [propext, Classical.choice, Quot.sound]
'DetPrimality.exists_nonresidue_lt_of_bachBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'DetPrimality.Miller.millerDet_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'DetPrimality.Miller.exists_proper_subgroup_strongLiars' depends on axioms: [propext, Classical.choice, Quot.sound]
'DetPrimality.Miller.millerDet_of_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'DetPrimality.Miller.millerBound_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'DetPrimality.TonelliShanks.sqrtModDet_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'DetPrimality.TonelliShanks.sqrtModDet_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'DetPrimality.TonelliShanks.sqrtModDet_isSome_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'DetPrimality.TonelliShanks.tonelliShanks_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`sorryAx` appears only in the theorems that go through Layer 2's four sorries. Everything conditional on `BachBound c` (Layers 1, 3, 4) uses only the standard three axioms.

## Honesty review

- **Interface names match.** All layers use `BachBound`, `BachBoundChar`, `GRHImpliesBach` and `DirichletLZerosOnLine` from `Interfaces.lean`/`GRHStatements.lean`, with no local redefinitions.
  - `bachBound_of_bachBoundChar` is proved twice, as `DetPrimality.bachBound_of_bachBoundChar` (Bridge) and `DetPrimality.Bach.bachBound_of_bachBoundChar` (Blueprint).
  - The names do not clash because the namespaces differ. One copy could be removed later.
- **No trivialising hypotheses.**
  - **`BachBound c` can be false for small c**, which would make the conditional theorems vacuous. For example, n = 3 needs c ≥ 2/log²3 ≈ 1.66, so `BachBound 1` is false.
  - The end-to-end theorems use c = 1024, obtained from `grh_implies_bach`. The Layer 3–4 theorems are therefore only as meaningful as Layer 2, which is the expected dependency.
  - `0 < c` is the only other hypothesis, and it is harmless.
  - `DirichletLZerosOnLine` quantifies over all χ mod N, imprimitive ones included. Their extra zeros lie on Re s = 0, outside the strip, so the statement is not trivially false. Bridge/Notes.md argues it is equivalent to the primitive version.
- **Loop bounds are at least c·log² n.**
  - **Miller:** the bases are `[2, min(millerBound c n, n))`, with `millerBound c n = ⌈c⌉·(log2 n + 1)² ≥ c·(ln n)²` (`millerBound_ge`, proved).
    - The Bach witness `a` satisfies `a.val ∉ {0, 1}`, `a.val < n` and `a.val < c ln² n`, so it is inside the loop.
    - No a priori "n is prime" check is needed; the composite case goes through `exists_proper_subgroup_strongLiars`.
  - **Tonelli–Shanks:** `findNonResidue` searches `[2, nonResidueBound c p + 2)`, with `nonResidueBound c p = ⌈c⌉·(size p)² ≥ c·(ln p)²` (`le_nonResidueBound`, proved).
- **The Layer 2 sorry statements look true as written.** The numeric constant is true (0.57 ≤ 1). The normalisation of sorry 2 matches the classical formula. Sorry 3 is consistent at x = 1, but its general Γ-term constant rests on blueprint §3 and was not re-derived.
- **Executable sanity checks** (`#eval`, c = 2) were rerun inside the library build. Miller rejects 561, 1105, 41041, 2047, 3215031751 and 2^61+1, and accepts 1000003, 10^9+7 and 2^61−1. Filtering 0–99 returns exactly the 25 primes. All Tonelli–Shanks outputs satisfy r² ≡ n.

## For the lead

- **Stale scratch files on the box** under `~/maths/detprimality/` (rsync has no `--delete`): `DetPrimality/Bach/BlueprintCheck.lean` and `DetPrimality/Miller/CheckTmp.lean`. They are not imported and are harmless; delete them when convenient.
- **Runtime cost of c = 1024:** with c = 1024 the Miller loop runs over about 1024·(log₂ n + 1)² bases, 512× more than Bach's c = 2. That is still polynomial, but roughly 4·10⁶ bases for n ≈ 2^61. The examples use c = 2, which is correct only under Bach's sharper (unformalised) constant.
- Nothing has been committed. Files edited in this pass: `lean/DetPrimality.lean`, plus the new `lean/DetPrimality/EndToEnd.lean` and `lean/DetPrimality/Audit.lean`.

## Next steps (ranked)

1. **NUM sorry 4 (`tsum_vonMangoldt_term_two_le`)** is cheap and self-contained, about 100–200 lines. Use `Λ(n) ≤ log n` and an integral comparison, or a bound on ∑_p log p/(p²−1).
2. **DEEP sorry 1 (zero summability).** Either prove Jensen zero counting for `completedLFunction χ` or import the archive's `ZeroCount`.
   - The archive has no build cache. Importing means building its cone from source against the cached Mathlib, which is expensive but acceptable per the user.
   - First measure the size of the transitive cone of `ZeroCountHolds.lean`.
3. **DEEP sorry 2 (Hadamard partial fractions for `completedLFunction χ`).** This is the core missing Mathlib infrastructure: order-1 entire functions and Hadamard factorisation, plus Re B(χ) from `IsPrimitive.completedLFunction_one_sub`. The archive's `dirichlet_logDeriv_reflection_formula` helps with the Γ part. This is the largest item, an estimated several thousand lines.
4. **DEEP sorry 3 (smoothed explicit formula).** Perron for the kernel 1/(s(s+1)) via `mellinInv_mellin_eq`, the digamma series and termwise integration. It reuses item 3.
5. **Sharpen c from 1024 toward about 70 (or Bach's 2).** Only the elementary §6–§7 lemmas change (blueprint §8); this improves runtime, not correctness.
6. **Complexity:** prove polynomial running-time bounds for `millerDet`/`sqrtModDet`, which are not started. Optionally switch the examples to c = 1024, or add a `c = 2` corollary once Bach's constant is formalised.
7. **Housekeeping:** remove the duplicate `Bach.bachBound_of_bachBoundChar` in favour of Bridge's, and clean the stale box files.

---

# Round 2 (2026-11-21): Layer 2 closed. The end-to-end chain is sorry-free.

## Headline

`DetPrimality.millerDet_correct_of_GRH`, `sqrtModDet_correct_of_GRH` and `sqrtModDet_isSome_iff_of_GRH` now depend only on `[propext, Classical.choice, Quot.sound]`. There is **no `sorryAx`**. GRH for Dirichlet L-functions (`DirichletLZerosOnLine`) implies, in Lean, that `millerDet 1024` decides primality.

```lean
theorem DetPrimality.Bach.grh_implies_bach_v2 : GRHImpliesBach 1024              -- Bach/Assembly.lean
theorem DetPrimality.Bach.bachBoundChar_of_GRH_v2 (hGRH : DirichletLZerosOnLine) : BachBoundChar 1024
theorem DetPrimality.millerDet_correct_of_GRH (hGRH : DirichletLZerosOnLine) (n : ℕ) :
    Miller.millerDet 1024 n = true ↔ n.Prime                                       -- EndToEnd.lean, via _v2
```

## Build and audit

- **Full build:** `bin/check.sh --build` gives `Build completed successfully (8732 jobs)`.
  - Warnings: the 4 `declaration uses 'sorry'` in `Bach/Blueprint.lean` (the round-1 chain, now outside the end-to-end cone), plus 2 unused-variable `hχ` lints (`ZeroCount.lean:252`, `ExplicitMain.lean:18`).
- **Axiom audit:** `bin/check.sh DetPrimality/Audit.lean` (excerpt, verbatim):
  ```
  'DetPrimality.millerDet_correct_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
  'DetPrimality.sqrtModDet_correct_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
  'DetPrimality.sqrtModDet_isSome_iff_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
  'DetPrimality.Bach.grh_implies_bach_v2' depends on axioms: [propext, Classical.choice, Quot.sound]
  'DetPrimality.Bach.bachBoundChar_of_GRH_v2' depends on axioms: [propext, Classical.choice, Quot.sound]
  'DetPrimality.Bach.bachInputs' depends on axioms: [propext, Classical.choice, Quot.sound]
  'DetPrimality.Bach.grh_implies_bach_of_inputs' depends on axioms: [propext, Classical.choice, Quot.sound]
  'DetPrimality.Bach.growth_completedLFunction' depends on axioms: [propext, Classical.choice, Quot.sound]
  'DetPrimality.Bach.hadamardLogDeriv_of_growth' depends on axioms: [propext, Classical.choice, Quot.sound]
  'DetPrimality.Bach.summable_zeroOrd_div_normSq_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
  'DetPrimality.Bach.summable_zeroOrd_div_normSq_of_growth' depends on axioms: [propext, Classical.choice, Quot.sound]
  'DetPrimality.Bach.re_logDeriv_eq_tsum_of_growth' depends on axioms: [propext, Classical.choice, Quot.sound]
  'DetPrimality.Bach.explicit_formula_bound_of_hadamard' depends on axioms: [propext, Classical.choice, Quot.sound]
  'DetPrimality.Bach.Numerics.tsum_vonMangoldt_term_two_le_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
  'DetPrimality.Bach.Numerics.tsum_vonMangoldt_term_two_le_three_quarters' depends on axioms: [propext, Classical.choice, Quot.sound]
  'DetPrimality.bachBound_1024_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
  'DetPrimality.Bach.blueprintInputs' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
  'DetPrimality.Bach.grh_implies_bach' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]   -- round-1 chain, kept
  ```
  The Layers 1, 3 and 4 lines are unchanged from round 1; all use only the standard three axioms.
- **Text grep:** there is no `sorry`, `axiom`, `native_decide` or `admit` anywhere under `lean/DetPrimality/` except the 4 sorries in `Bach/Blueprint.lean`.

## Remaining sorries in the dependency cone of `millerDet_correct_of_GRH`

**None.** The `#print axioms` output above confirms it.

The library still contains the 4 round-1 sorries in `Bach/Blueprint.lean` (l.48, 58, 70, 83: `summable_zeroOrd_div_normSq`, `re_logDeriv_eq_tsum`, `explicit_formula_bound`, `tsum_vonMangoldt_term_two_le`).
- They are now **outside** the end-to-end cone. Only the round-1 theorems `grh_implies_bach`, `bachBoundChar_of_GRH`, `zeroSum_le`, `norm_smoothPsi_le` and `blueprintInputs` use them.
- **They cannot be filled in place**, because `Handoffs.lean`, and with it every round-2 file, imports `Blueprint.lean`, which would create an import cycle.
- **All four have now been proved** elsewhere, with the identical statement (or, for §3, from extra hypotheses that are themselves discharged), so they are known to be true.
- **Optional cleanup:** move the §1 definitions of Blueprint into a `Bach/Defs.lean` that Handoffs imports. Then Blueprint can import the round-2 files and its sorries can be replaced by the proofs. This needs an edit to `Handoffs.lean`, which only the lead may make.

## What was integrated (round-2 files, all in `lean/DetPrimality/Bach/`, all sorry-free)

| Input (Blueprint §) | Round-2 theorem | File(s) | Hypotheses needed beyond `χ ≠ 1` |
|---|---|---|---|
| Growth hand-off | `growth_completedLFunction : GrowthLtTwo (completedLFunction χ)` | `Growth.lean` | none (primitivity not needed) |
| §2.1 `∑ m_ρ/|ρ|² < ∞` | `summable_zeroOrd_div_normSq_proof` (Hadamard agent); also `summable_zeroOrd_div_normSq_of_growth` (zerocount agent, independent proof) | `HadamardGeneral.lean`, `HadamardL.lean`; `ZeroCount.lean` | primitive (in the `HadamardL` version), `GrowthLtTwo` |
| Hadamard hand-off | `hadamardLogDeriv_of_growth : HadamardLogDeriv χ` | `HadamardGeneral.lean`, `HadamardL.lean` | primitive, `GrowthLtTwo` |
| §2.2 `Re Λ'/Λ` formula | `re_logDeriv_eq_tsum_of_growth` | `HadamardL.lean` | primitive, `GrowthLtTwo` |
| §3 explicit formula | `explicit_formula_bound_of_hadamard` | `ExplicitDigamma`, `ExplicitPerron`, `ExplicitPerronLog`, `ExplicitFormula`, `ExplicitGamma`, `ExplicitKernel`, `ExplicitWeight`, `ExplicitZeros`, `ExplicitMain` | `HadamardLogDeriv χ`, `hS` (primitivity unused) |
| §4.1a `∑ Λ(n)/n² ≤ 1` | `Numerics.tsum_vonMangoldt_term_two_le_proof` (also `≤ 3/4`) | `Numerics.lean` | none |

**New integration file: `Bach/Assembly.lean`.**
- **`structure BachInputs : Prop`** has four fields, `summable`, `reLogDeriv`, `explicit` and `vonMangoldt`. They are the four Blueprint sorry statements verbatim, quantified over `q`, `χ` and the primitive, nonprincipal hypotheses.
- **`blueprintInputs : BachInputs`** is built from the round-1 sorries. It shows that the old chain fits the same interface.
- **`bachInputs : BachInputs`** is built from the round-2 proofs and is sorry-free.
- **The downstream assembly (§4.1, §5.1, §5.2, §7.3) is restated with `(hI : BachInputs)`**: `norm_logDeriv_LFunction_two_le_of_inputs`, `summable_zeroSum_of_inputs`, `zeroSum_le_of_inputs`, `norm_smoothPsi_le_of_inputs`, `bachBoundChar_of_GRH_of_inputs` and `grh_implies_bach_of_inputs`.
  - The proofs are copied verbatim from Blueprint, with each sorried lemma replaced by an `hI` field.
  - All the sorry-free Blueprint lemmas are reused as they are: `zero_facts`, `re_logDeriv_gammaFactor_two_nonpos`, `psiOne_lower`, `noncoprimeSum_le`, `re_smoothPsi_primitive_lower`, `nine_le_log_of_no_small_witness`, `final_numeric` and `bachBound_of_bachBoundChar`.
- **`grh_implies_bach_v2 := grh_implies_bach_of_inputs bachInputs`.**

**Other integration edits:**
- **`EndToEnd.lean`** now imports `Bach.Assembly`, and `bachBound_1024_of_GRH` uses `grh_implies_bach_v2`. The theorem statements are unchanged.
- **`DetPrimality.lean`** imports all 16 new `Bach/*` library modules. The `*Audit.lean` files are not imported.
- **`Audit.lean`** has new `#print axioms` lines for the round-2 theorems.
- **One name clash was fixed.** `ExplicitFormula.lean`'s `completed_eq_mul` (`Λ = L·γ`) collided with `HadamardL.lean`'s `completed_eq_mul` (`Λ = γ·L`, with `χ ≠ 1`). The ExplicitFormula one was renamed `completed_eq_L_mul_gammaFactor`; there are 3 uses, all in that file.
- **Protected files were not touched:** `GRHStatements.lean`, `Interfaces.lean`, `Bach/Handoffs.lean`, and `Bach/Blueprint.lean` are unchanged.

## Statement findings from round 2

All findings are benign, and no statement turned out to be false.
1. **Primitivity is not needed** for growth, zero counting (the ZeroCount version) or the explicit formula given `HadamardLogDeriv`. It is used for Hadamard and §2.2, through `completedLFunction χ 0 ≠ 0` and the functional equation.
2. **`HadamardLogDeriv` alone does not give convergence**, so §2.2 also needs `hS`. `re_logDeriv_eq_tsum_of_growth` packages both.
3. **The explicit-formula swap of ∑_ρ and ∫** needs `∑ m_ρ (1+|γ|)^{-7/4} < ∞`, which is stronger than `hS`. It was derived from `HadamardLogDeriv` + `hS`, so no extra hypothesis is required.
4. **The Hadamard constant is identified** as `B = Λ'(0)/Λ(0)`.
5. **The explicit-formula Γ-term constant 4 is correct and generous.** Exact Γ-term values: `|I_Γ| ≤ log x + 1` (even) and `≤ ~1.31` (odd). The Lean proof gets `log x + 3`.
6. **`∑ Λ(n)/n² ≤ 3/4` is also proved**, against a true value of 0.5699.

## Honesty review, round 2

- **The end-to-end hypotheses are unchanged.** The only hypothesis is `DirichletLZerosOnLine` (Layer 0, unchanged). The round-1 discussion of why it is not trivially false still applies.
- **`GrowthLtTwo` and `HadamardLogDeriv` are not hypotheses of any end-to-end theorem.** Both are proved, for every primitive `χ ≠ 1`, inside `bachInputs`.
- **`BachInputs` is only an internal packaging device.** It holds the exact Blueprint statements, and `bachInputs` proves it outright.
- **Duplicate work:** §2.1 has two independent proofs (`HadamardL` via `HadamardGeneral`, and `ZeroCount`). The chain uses the Hadamard one; `ZeroCount.lean` is redundant but harmless. It could be dropped from `DetPrimality.lean` to save build time.

## Still missing

- **Running-time / polynomial-time proofs** for `millerDet` and `sqrtModDet` have not been started.
- **The constant is still c = 1024.** That is 512× Bach's c = 2 in loop length. See the plan below.
- **Optional cleanup:** retire the round-1 sorries via the `Bach/Defs.lean` split described above, and delete the agents' `*Audit.lean` scratch files (`ExplicitAudit`, `GrowthAudit`, `HadamardAudit`) or merge them into `Audit.lean`.

## Plan for lowering c = 1024 (from the numerics agent; elementary, §6 / §7 of the assembly only)

**Numerical model.** The final inequality is `(√c·L + 5)(L + 2) + log x + 5 < main(x) − 2·(L + E(x))`. Here `x = cL²`, and `E` bounds `ψ − θ`. It is checked for all `L ≥ L₀(c)`, where `e^{L₀} = c·L₀²` is the exact form of the §7.1 bootstrap.

Smallest workable c:

| Main term (§6.1) | `E(x)` (§6.2) | zero-sum +2 (current) | zero-sum +0.04 |
|---|---|---|---|
| `ψ(x/2)/2` (current) | `16.16√x` (current) | 564 | 522 |
| `ψ(x/2)/2` | Mathlib `Chebyshev.psi_le` at √x, x^{1/3}, x^{1/5} | 129 | 107 |
| `ψ(x/2)/2` | `1.43√x` (not in Mathlib) | 93 | 72 |
| integral form `(x−3)·log 2/2 − log(x+2)` | `16.16√x` | 177 | 165 |
| **integral form** | **Mathlib `psi_le`** | **46** | 38 |
| integral form | `1.43√x` | 31 | 24 |

`L₀` is about 7.99 for c = 46, 8.54 for c = 70, and 11.16 for c = 564.

Steps:
0. **Free win (about c = 600).** Retune only `final_numeric` and `nine_le_log_of_no_small_witness` (L ≥ 11), using the exact bootstrap.
1. **§6.2 `noncoprimeSum_le`** (easy, about 30 lines).
   - Keep `Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi`.
   - Replace `psi_le_const_mul_self` with `Chebyshev.psi_le` (ψ(y) ≤ log 4·y + 2√y·log y, for y ≥ 1), and use `psi_eq_zero_of_lt_two` below 2.
   - This gives about 1.39√x + O(x^{1/4}log x + x^{1/3}). The bound is no longer linear in √x, so `final_numeric` needs extra rpow/log handling.
2. **§6.1 `psiOne_lower`** (moderate, about 80–120 lines).
   - x·ψ₁(x) ≥ Σ_{k<N} ψ(k), with N = ⌊x⌋, by swapping a double Finset sum.
   - Apply `Chebyshev.psi_ge` (n·log 2 − log(n+1) ≤ ψ n), then `log N! ≤ N log N`.
   - Result: ψ₁(x) ≥ (x−3)·log 2/2 − log x. This doubles α from log 2/4 to log 2/2.
   - Intermediate option: ψ₁ ≥ (1/J)Σ_{j<J} ψ(jx/J), which gives α = 3·log 2/8 at J = 4.
3. **§7.1–7.2** (easy).
   - Redo `final_numeric` for c = 64 or 70, valid for L ≥ 8.5.
   - Bootstrap: n > 70·64 ⟹ L > 8.4 ⟹ … .
   - With steps 1 + 2 + 3 the model gives c ≈ 46, so c = 64 leaves room.
   - In `Assembly.lean` this is a new `bachBoundChar_of_GRH_of_inputs` at the new c. The `BachInputs` and analytic files are unchanged. `EndToEnd` then takes c = 64.
4. **Optional, small:**
   - Use `tsum_vonMangoldt_term_two_le_three_quarters` (already proved) to get T ≤ log q + 1.5. That saves about 2–4 in c.
   - +0.04 in the zero sum would need more digits of −ζ'/ζ(2) and a sharper Γ-term.
5. **Below about 40, the routes are not elementary:**
   - ψ − θ ≤ 1.43√x (Rosser–Schoenfeld, a computation).
   - τ = 2/3 via Bach's evaluation point.
   - RH for ζ in the main term (α = 1/2).
   - These are needed for c ≈ 4–10.

## Round 3: lowering c

**Result: c = 64 (was 1024), sorry-free.** The analytic part (`BachInputs` / `bachInputs`) is unchanged. Only the elementary §6–§7 inputs were sharpened, in three new files:

- `Bach/ConstPsiOne.lean`: `psiOne_lower_integral : 1 ≤ x → (x - 3) * log 2 / 2 - log x ≤ psiOne x`. The slope is log 2 / 2; the old bound had log 2 / 4.
- `Bach/ConstNoncoprime.lean`: `noncoprimeSum_le_of_ge_4096 : 4096 ≤ x → noncoprimeSum n x ≤ log n + 3.36 * √x`. The old constant was 16.16. The file also gives 2.6 for x ≥ 2^16 and 2 for x ≥ 2^22.
- `Bach/Constant.lean`:
  - `eight_le_log_of_no_small_witness`: the bootstrap n > 64 (log n)² ⟹ log n ≥ 8.
  - `final_numeric_64`: with L ≥ 8 and √x = 8L, the inequality reduces to 14.18 L² − 108.76 L − 12.04 > 0. Its value at L = 8 is about 25.
  - `bachBoundChar_of_GRH_c : DirichletLZerosOnLine → BachBoundChar 64`.
  - `grh_implies_bach_c : GRHImpliesBach 64`.
- `EndToEnd.lean`: `millerDet_correct_of_GRH`, `sqrtModDet_correct_of_GRH` and `sqrtModDet_isSome_iff_of_GRH` now use constant 64. The 1024 versions are kept with a `_1024` suffix. The `Examples.lean` `#eval`s use 64.
- Axioms: every end-to-end theorem depends only on `[propext, Classical.choice, Quot.sound]`. See `Audit.lean`.

**Remaining slack.** These lemmas leave numerical room for c ≈ 46. Python check, with a = sharpE(x₀)/√x₀ at the bootstrap point x₀ = c·L₀², where e^{L₀} = c L₀²: c = 48 passes with margin of about 44, and c = 44 fails. Getting c = 48 would need:
- a `sharpE` point bound at x₀ ≈ 3100, below 4096;
- a bootstrap to log n ≥ 8.04;
- handling of √48·L.

The routes below c ≈ 40 are listed in the ConstNoncoprime report:
- a Stirling-type log N! bound in `sum_psi_ge`;
- bounding ψ − θ exactly as Σ θ(x^{1/k});
- the 3/4 bound on Σ Λ(n)/n² in `zeroSum_le`.

## Round 4: c = 46

**Result: c = 46 (was 64), sorry-free.** The analytic part (`BachInputs` / `bachInputs`) is unchanged, and no existing Bach file was modified.

- `Bach/ConstPsiTheta.lean` (new, generated tables): `psi_sub_theta_le_small : ψ x − θ x ≤ 1.84 √x` for all real x, and `noncoprimeSum_le_small : noncoprimeSum n x ≤ log n + 1.84 √x`. It also has sharper range bounds (1.43 on [0, 2^16), 1.35 on [420, 2^16), 1.34 on [2000, 2^16), 1.30 on [2500, 2^16)). One binder-type fix was needed on the first compile (`∀ k : ℕ, k ∈ Finset.Icc 2 15 → …`).
- `Bach/ConstPsiOneSharp.lean` (new): `psiOne_lower_2048` / `psiOne_lower_1024`, which add 946453·log 2/x and 239571·log 2/x to the §6.1 bound. These are proved by kernel-checked lcm-product certificates. The c = 46 proof does not need them.
- `Bach/Constant46.lean` (new):
  - `log_ge_of_no_small_witness_46`: the bootstrap n > 46 (log n)² ⟹ log n ≥ 11 log 2 > 7.62. It goes through 2^5, 2^9, 2^10 and 2^11, so no exp bound is needed.
  - `final_numeric_46`: in s = √x with s² = 46 L², using s ≤ 6.7824 L and log x ≤ 12 log 2 + x/4096 − 1.
  - `bachBoundChar_of_GRH_c46 : DirichletLZerosOnLine → BachBoundChar 46`.
  - `grh_implies_bach_c46 : GRHImpliesBach 46`.
- `EndToEnd.lean`: `millerDet_correct_of_GRH`, `sqrtModDet_correct_of_GRH` and `sqrtModDet_isSome_iff_of_GRH` now use 46, through `bachBound_46_of_GRH`. The c = 64 versions are kept with a `_64` suffix, and the `_1024` versions are kept. The `Examples.lean` `#eval`s use 46.
- Build: `bin/check.sh --build` succeeds (8738 jobs). Axioms: every end-to-end theorem depends only on `[propext, Classical.choice, Quot.sound]` (see `Audit.lean`).

**Slack.** The Lean-form inequality is 9.14 L² − 45.5 L − 30.7 > 0 for L ≥ 7.62. It has margin of about 153 at L = 7.62 and grows like L². In the exact model (true bootstrap L₀ = 7.983, uniform 1.84, no ψ₁ gain), the margin at c = 46 is about 188.

**Going lower** (Python model, exact bootstrap e^{L₀} = c L₀²):
- Uniform 1.84 with the round-3 ψ₁ bound reaches c ≈ 34 (margin +6.5).
- Adding the piecewise ψ − θ constants (1.35, 1.34, 1.30 below 2^16) reaches c ≈ 32.
- Adding the ψ₁ gains as well (K = 1024 on (1024, 2048], K = 2048 above) reaches **c ≈ 22**. The margin is +38 at c = 22, +56 at c = 24 and +83 at c = 28; c = 20 fails, because there x₀ = 936 < 1024.

All of these lemmas are already proved. What remains is assembly work: case splits of the final inequality on the x-ranges, and a tighter bootstrap (to L₀ ≈ 7.0 for c = 22, which needs an exp bound or finer powers of 2).

## Round 5: c = 22

**Result: c = 22 (was 46), sorry-free.** No existing Bach file was modified. There are two new files from independent attempts.

- `Bach/Constant22.lean`:
  - **Bootstrap.** `log_ge_of_no_small_witness_22`: n > 22 L² ⟹ n ≥ 2^10, so L ≥ 6.9314 and x = 22L² > 1024. The steps are 2^4, 2^7, 2^9, then fractional powers via n² ≥ 2^19, n⁴ ≥ 2^39, n⁸ ≥ 2^79. No exp bound is needed.
  - **Final inequality,** split into four x-ranges. Each range reduces through `final_of_quad` to a quadratic in L. The ψ₁ gain stays linear because of the tangent line of 1/x (`gain_tangent`). Minimum Lean-form margins:

    | x range | ψ−θ constant | ψ₁ bound | margin |
    |---|---|---|---|
    | (1024, 1450] | 1.35 | `psiOne_lower_1024` | 37.7 |
    | (1450, 2048] | 1.35 | `psiOne_lower_1024` | 38.1 |
    | (2048, 4096] | 1.34 | `psiOne_lower_2048_of_le` | 122 |
    | > 4096 | 1.84 | `psiOne_lower_integral` | 54, growing like L² |

  - `bachBoundChar_of_GRH_c22`, `grh_implies_bach_c22 : GRHImpliesBach 22`.
- `Bach/Constant28.lean`: an independent and simpler proof of c = 28. It uses the uniform 1.84 constant and the 1024 gain, with a two-way split at L = 10. It is kept as a cross-check and is not on the main path.
- `EndToEnd.lean`: `millerDet_correct_of_GRH`, `sqrtModDet_correct_of_GRH` and `sqrtModDet_isSome_iff_of_GRH` now use 22, through `bachBound_22_of_GRH`. The c = 46 versions are kept with a `_46` suffix, alongside the `_64` and `_1024` ones. The `Examples.lean` `#eval`s now use 22.
- **Verification:** the full build succeeds (8740 jobs). Every end-to-end theorem in `Audit.lean` depends only on `[propext, Classical.choice, Quot.sound]`. `leanchecker` returns rc=0 on Constant22, Constant28 and EndToEnd.

**Below 22.** c = 21 fails with the current lemmas. Its true bootstrap gives x₀ ≈ 1003 < 1024, and on [1003, 1024] there is no ψ₁ gain (model margin ≈ −98). The route down is new `lcmProd` certificates through `psiOne_lower_of_cert` with K ≈ 900, plus a finer bootstrap. The model margin is then about +64 for c = 21 and +58 for c = 20. Bach's own constant is 2, and reaching it needs his sharper analytic inputs (a different explicit formula), not just tighter numerics.

## Round 6: c = 8

**Result: c = 8 (was 22), sorry-free.** It was produced by a Fable workflow: four lemma files written in parallel, then two assembly attempts. No existing Bach file was modified.

Changes to the analytic side (all under GRH and sorry-free):
- `Bach/SharpZeroSum.lean`:
  - `zeroSum_le_sharp32 : zeroSum χ ≤ 2/3·log q + 1.097`, using reLogDeriv at s = 3/2. On the critical line, 1/(|ρ||ρ+1|) ≤ (4/3)·Re 1/(3/2−ρ).
  - `zeroSum_le_sharp2 : ≤ log q + 0.036`, at s = 2 with sharp digamma bounds.
  - Supporting bounds: ∑Λ(n)/n² ≤ 0.5708 and ∑Λ(n)n^{-3/2} ≤ 1.5075, both through Λ∗1 = log and rational certificates, plus digamma and gammaFactor bounds.
- `Bach/SharpExplicit.lean`:
  - The prefactor becomes (√x + 2 + 3/x), down from (√x + 5), using |2−ρ| = |ρ+1| under GRH.
  - A one-sided version `re_smoothPsi_le_of_zeroSum_le_of_logDeriv`: the explicit-formula residual is essentially negative, so in the upper bound for Re smoothPsi the term log x + 4 becomes −1 + (log x + 13/6)/x.

Changes to the elementary side:
- `Bach/ConstNoncoprimeOmega.lean`: noncoprimeSum n x ≤ log n + ∑_{p | n, p ≤ x} (log x − log p), with corollaries for n below the primorials 6, 30, 210, 2310 and 30030.
- `Bach/ConstPsiOneGrid.lean` (generated): near-exact ψ₁ lower bounds on (256, 1536], from lcm-product certificates on a grid.

Assembly:
- `Bach/ConstantLow.lean`: `grh_implies_bach_c8` and `grh_implies_bach_c9`.
  - Exact bootstraps: n ≥ 241 (c = 8) and n ≥ 289 (c = 9).
  - For c = 8, additional cases on ω(n). `clow8_omega4`: if n ≥ 241 has 4 prime factors, then n ≥ 420, or n ≡ 2 (mod 4) and n ≥ 330.
  - Also for c = 8: when n ≡ 2 (mod 4), the conductor is ≤ n/2 (`clow8_conductor_le`).
  - The smallest Lean-form margin is about 1.26, against margins of roughly 4–100 for c ≥ 9.
- `Bach/ConstantMid.lean`: an independent and simpler proof of c = 13.

`EndToEnd.lean`: the main theorems use c = 8, through `bachBound_8_of_GRH`. The `_22`, `_46`, `_64` and `_1024` versions are kept.

Verification:
- `bin/check.sh --build` succeeds (8747 jobs).
- `Audit.lean`: every end-to-end theorem and every round-6 theorem depends only on `[propext, Classical.choice, Quot.sound]`.
- `leanchecker` returns rc=0 on all six new modules and on EndToEnd.

**Below 8.** c = 7 fails with these inputs. At n = 210 (x ≈ 200), even the exact noncoprime sum leaves the model at −5. Further progress would need sharper analytic inputs (σ ≈ 1.37 in the zero sum, or a better explicit-formula residual), or a different lower bound that sums over m coprime to q.

## Round 7 (2026-11-22): Bach's Theorem 2 form, c = 1.46 for Miller

- New interface `CompositeInterface.lean`: `BachBoundCharComposite c` (Bach 1990 Theorem 2 form,
  composite moduli; a base sharing a factor with `n` counts as a witness). Miller only needs this.
- `Miller/Composite.lean`: `millerDet_correct_of_composite` (non-unit bases fail `sprp`).
- `Bach/CompositeReduction.lean`: no witness below `x` ⟹ noncoprime sum = 0, `χ* = 1` below `x`,
  and `n ≥ x²` (least prime factor ≥ x), bootstrapping `log n ≥ 9.94` at `c = 1.46`.
- `Bach/ZeroSumGain.lean`: two-point majorant at `s = 5/4, 2` (weights 8/9, 2/9, exact polynomial
  certificate) ⟹ `zeroSum ≤ (5/9) log q + …`, plus Bach's hypothesis gain
  `Re L'/L(σ) ≤ Z(σ) − 2 Σ_{m<K} Λ(m) m^{−σ}` ⟹ `zeroSum ≤ (5/9) log q − 2.20` for `x ≥ 240`.
- `Bach/ChebyshevThirty.lean`: Chebyshev's 30-identity, `ψ₁(x) ≥ 0.460645 x − 1.5 log x + …`.
- `Bach/ConstPsiOneGrid2.lean`: `ψ₁(x) ≥ x/2 − 2.9` on (1536, 6000] (not needed by the final proof).
- `Bach/ConstantComposite.lean` (c = 4, old ingredients), `ConstantThree.lean` (c = 3),
  `ConstantTwo.lean` (c = 73/50, hence 3/2 and 2). Limit of these inputs: c > (5/9 / 0.460645)² ≈ 1.4546.
- `EndToEnd.millerDet_correct_of_GRH : millerDet (73/50) n = true ↔ n.Prime` (`_2`, `_8` kept).
  Tonelli–Shanks still uses the unit form at c = 8 (prime moduli are excluded from the composite form).
- Verified: full build (8756 jobs), axioms only [propext, Classical.choice, Quot.sound],
  leanchecker rc=0 on all new modules + EndToEnd, no odd composite ≤ 3·10⁵ passes `millerDet (73/50)`.

## Round 8 (2026-11-22): c = 1 — Lamzouri–Li–Soundararajan Theorem 1.1(2)

`DetPrimality.millerDet_correct_of_GRH : DirichletLZerosOnLine → (Miller.millerDet 1 n = true ↔ n.Prime)`,
i.e. bases below about `(ln n)²`. This is the best published explicit constant (LLS, Math. Comp. 84 (2015),
Thm 1.1(2); below 1 is known only asymptotically). The Round-7 `c = 73/50` version is kept as `_146`.

| Input | Statement | File |
|---|---|---|
| Hand-off | `LLSZetaLower κ`, `LLSChiUpper`, `LLSZeroSumGain`, `LLSWeightedLower` | `Bach/LLSDefs.lean` |
| LLS Lemma 1 (RH, ζ) | `llsZL_main : LLSZetaLower (1/20)` | `Bach/LLSZetaLower.lean` |
| ζ Hadamard, `2|B| ≤ 0.0475` | `llsZeta_hadamard`, `llsZeta_zeroSumSq_le` | `Bach/LLSZeta.lean`, `LLSZetaConst.lean` |
| LLS Lemma 2 (x^s/s² Perron) | `llsPer_chiUpper : LLSChiUpper` | `Bach/LLSPerron*.lean` |
| LLS Lemma 3 (zero sum, hypothesis gain) | `llsGain_main : LLSZeroSumGain` | `Bach/LLSGain*.lean` |
| Lemma 4 (unconditional) | `llsElem_weightedLower` | `Bach/LLSElem.lean` |
| Assembly (n ≥ 3000) | `llsAsm_bachBound_one` | `Bach/LLSAssembly.lean` |
| n < 3000 | `llsElem_millerDet_one_small` (`decide +kernel`) | `Miller/LLSSmall.lean` |
| Miller | `llsAsm_millerDet_one_correct'` | `Miller/LLSMiller.lean` |

Verification: full build 8770 jobs OK; every Round-8 theorem depends only on
`[propext, Classical.choice, Quot.sound]`; `leanchecker` rc=0 on all 14 new modules and `EndToEnd`;
protected files unchanged. Tonelli–Shanks still uses `c = 8` (unit form at prime moduli).

### Round 8b: Tonelli–Shanks at c = 1
`sqrtModDet_correct_of_GRH` / `sqrtModDet_isSome_iff_of_GRH` now use `sqrtModDet 1` (non-residue search
below about `(ln p)²`, LLS Cor 1.1), via `TonelliShanks/LLSSqrt.lean` and `Bach/LLSPrime.lean`
(`llsPrime_bachBound_one_all_of_GRH`: the c = 1 bound for *all* n ≥ 3000, non-units counting; odd primes
< 3000 by a `decide +kernel` table). The c = 8 versions are kept with suffix `_8`. Build 8772 jobs OK;
axioms standard; leanchecker rc=0 on LLSPrime, LLSSqrt, EndToEnd.

## Round 9: running time of the deterministic Miller test (`Complexity/cx_*.lean`), unconditional
* `cx_millerDetFast_eq : cx_millerDetFast n = millerDet 1 n` (textbook sprp: one powMod, then squarings).
* `cx_millerDet_modmul_count`: at most `(log₂ n + 1)³` modular multiplications.
* Bit level (little-endian `List Bool`, schoolbook shift-add multiply + shift-subtract remainder, every
  constant-size bit step charged 1): `cx_millerDet_bit_cost : (cx_millerDetBits n).1 = millerDet 1 n ∧
  (cx_millerDetBits n).2 ≤ 31 (log₂ n + 1)⁵`; generic in any modmul cost `M`:
  `≤ (log₂ n + 1)³ M(log₂ n + 1) + 4 (log₂ n + 1)⁴` (`cx_millerDet_bit_cost_generic`).
* `cx_millerDetBits_correct_of_GRH`: correct under GRH and within that bit budget.
* Not charged: computing the base budget `millerBound 1 n − 2` (depends only on the bit length) and the
  ℕ → bits input conversion; loop counters are unary. Õ(log⁴) needs a fast multiplier plugged into `M`.
