# Characters/ — notes for the analytic layer

## What is proved here (Bridge.lean, compiles, no sorry)

- `bachBound_of_bachBoundChar (c) : BachBoundChar c → BachBound c`
- `bachBoundChar_of_bachBound (c) : BachBound c → BachBoundChar c`, hence `bachBound_iff_bachBoundChar`
- `exists_dirichletCharacter_trivial_on`: a proper `H < (ZMod n)ˣ` lies in the kernel of a
  nontrivial `χ : DirichletCharacter ℂ n` (via `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`
  on `(ZMod n)ˣ ⧸ H`, then `MulChar.ofUnitHom`).
- `squares_ne_top`, `exists_nonresidue_lt_of_bachBound`, `exists_nonresidue_lt_of_bachBoundChar`:
  for an odd prime `p`, some `a < c (log p)^2` has `legendreSym p a = -1` (Tonelli–Shanks input).

So the analytic proof only has to deliver **`BachBoundChar c`**, i.e. for every `n > 2` and every
nontrivial `χ : DirichletCharacter ℂ n` (primitive OR imprimitive), some natural `a < c (log n)^2`
with `IsUnit (a : ZMod n)` and `χ a ≠ 1`. Note `IsUnit` is required: a non-unit `a` would give
`χ a = 0 ≠ 1` trivially, so it is excluded.

## Mathlib's `DirichletCharacter.LFunction` for imprimitive χ

Checked in `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean` (pinned Mathlib):

- `LFunction χ s := ZMod.LFunction χ s` is the analytic continuation of `∑ χ(n) n^{-s}` with
  `χ` viewed **at its own level `N`** (so `χ(m) = 0` whenever `gcd(m, N) > 1`). It does NOT
  silently replace χ by its primitive character.
- `LFunction_changeLevel (hMN : M ∣ N) χ (h : χ ≠ 1 ∨ s ≠ 1)`:
  `LFunction (changeLevel hMN χ) s = LFunction χ s * ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s))`.
  Combined with `changeLevel_primitiveCharacter` (Basic.lean:310) and
  `primitiveCharacter_isPrimitive`, for imprimitive χ mod N with primitive χ* mod f = conductor:
  `L(χ, s) = L(χ*, s) · ∏_{p | N} (1 − χ*(p) p^{−s})`.
  So the removed Euler factors ARE included (multiplied in); factors with `p | f` are `1` since
  `χ*(p) = 0`.

### Consequence for zeros
- Each factor `1 − χ*(p) p^{−s}` with `p | N, p ∤ f` vanishes iff `p^{−s} = χ*(p)^{−1}`, which
  forces `|p^{−s}| = p^{−Re s} = 1`, i.e. **Re s = 0**. These are infinitely many extra zeros on
  the imaginary axis (`s = (log χ*(p) + 2πik)/log p`, purely imaginary).
- They lie OUTSIDE `0 < Re s < 1`, so `DirichletLZerosOnLine` (all χ mod N, zeros in the open
  strip) is NOT vacuous/false for imprimitive χ, and it is equivalent to
  `PrimitiveDirichletLZerosOnLine` (both directions are easy given the factorisation above, since
  in `0 < Re s` each extra factor has `|χ*(p) p^{−s}| < 1`, hence is nonzero). The implication
  `DirichletLZerosOnLine → PrimitiveDirichletLZerosOnLine` is trivial (specialise).
- Also `LFunction (1 : DirichletCharacter ℂ N) 1` is a junk value (pole); BachBoundChar only
  concerns `χ ≠ 1`, so `differentiable_LFunction hχ` (entire) applies.

## Recommendation for the analytic proof
Work with the **primitive** character χ* (conductor f ∣ n, f ≥ 3 possible but f could be much
smaller than n) and use only `PrimitiveDirichletLZerosOnLine` + the functional equation
`IsPrimitive.completedLFunction_one_sub` (which Mathlib has only for primitive χ). The explicit
formula for χ* then has no zeros on Re s = 0 other than possibly s = 0 (trivial zero for even χ*),
and the Gamma factor is `gammaFactor` (Gammaℝ s or Gammaℝ (s+1)).

Then transfer to χ mod n: for `a` coprime to `n`, `χ(a) = χ*(a)`. The hypothesis to contradict is
"`χ(a) = 1` for all units `a < x`"; in the weighted prime sum `∑ Λ(m) χ*(m) w(m/x)` the terms with
`gcd(m, n) > 1, f ∤ ...` differ from the principal sum only on prime powers `p^k` with `p | n`,
contributing `≤ ∑_{p | n} log p · #{k : p^k ≤ x} ≤ log n · (log x / log 2)`-ish — this is the
standard `O(log n · log x)` error that Bach absorbs (it is why the bound is in terms of `log n`,
the modulus, and not `log f`). The analytic team must account for this term explicitly when
chasing the constant `c`.

Note the log in the bound is `log n` (the level), and the conductor satisfies `f ≤ n`, so
bounds of the form `c (log f)^2 + (prime-power-of-n correction)` must be converted to
`c (log n)^2`.
