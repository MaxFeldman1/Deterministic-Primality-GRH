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
