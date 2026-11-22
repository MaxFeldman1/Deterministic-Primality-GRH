import DetPrimality.Miller.Basic

/-! Sanity checks for the deterministic Miller test (`c = 73/50`, the constant proved under GRH in `Bach/ConstantTwo.lean`). -/

namespace DetPrimality.Miller

-- Carmichael numbers are rejected
#eval millerDet (73/50) 561      -- false
#eval millerDet (73/50) 1105     -- false
#eval millerDet (73/50) 41041    -- false
-- 2047 = 23 * 89 is a strong pseudoprime to base 2 but is rejected by later bases
#eval (sprp 2047 2, millerDet (73/50) 2047)   -- (true, false)
-- 3215031751 is a strong pseudoprime to bases 2, 3, 5, 7
#eval millerDet (73/50) 3215031751  -- false
-- primes pass
#eval millerDet (73/50) 1000003     -- true
#eval millerDet (73/50) 1000000007  -- true
#eval millerDet (73/50) (2 ^ 61 - 1)  -- true (Mersenne prime)
#eval millerDet (73/50) (2 ^ 61 + 1)  -- false
#eval (List.range 100).filter (fun n => millerDet (73/50) n)  -- primes below 100

end DetPrimality.Miller
