import DetPrimality.TonelliShanks.Basic

/-!
# Examples for deterministic square roots mod `p`

All computations use `c = 22` (the constant proved in `Bach/Constant22.lean`). `check p n` returns the root found together
with `r * r % p == n % p`.
-/

namespace DetPrimality.TonelliShanks.Examples

open DetPrimality.TonelliShanks

def check (p n : ℕ) : Option (ℕ × Bool) :=
  (sqrtModDet 22 p n).map fun r => (r, r * r % p == n % p)

-- search bound and least non-residues
#eval nonResidueBound 22 1000000007         -- ⌈22 · 0.480454 · 30²⌉ = 9513 (was 22 · 30² = 19800)
#eval findNonResidue 22 41                   -- 3
#eval findNonResidue 22 1000000007           -- 5
#eval findNonResidue 22 998244353            -- 3
#eval findNonResidue 22 (2 ^ 61 - 1)        -- 3

-- small primes
#eval check 41 2                            -- some (17, true); 41 ≡ 1 mod 8
#eval check 41 3                            -- none: 3 is a non-residue mod 41
#eval check 17 0                            -- some (0, true)
#eval (List.range 13).map (check 13)

-- p ≡ 3 mod 4, p ≡ 1 mod 4 with large 2-adic valuation (998244353 = 119 * 2^23 + 1)
#eval check 1000000007 2                    -- some (940286407, true)
#eval check 1000000007 5                    -- none
#eval check 998244353 5                     -- none (998244353 ≡ 3 mod 5)
#eval check 998244353 123456789             -- some (844148532, true)
#eval check (2 ^ 61 - 1) (1234567891011 ^ 2 % (2 ^ 61 - 1))
#eval check (2 ^ 127 - 1) (3 ^ 70)          -- an explicit square

-- Tonelli–Shanks directly, with a known non-residue
#eval tonelliShanks 998244353 123456789 3   -- some 844148532 (or its negative)
#eval tonelliShanks 998244353 10 3          -- none: 10 is a non-residue (precondition fails)

end DetPrimality.TonelliShanks.Examples
