"""Weights w(u) = sum_k c_k (1-u)^k (exact rationals) and truncation parameter lam (X = lam*x).
riesz*: pure Riesz kernels (1-u)^b.  opt*: numerically optimised polynomials (designA_explore.py),
coefficients rounded to 6 decimals and then treated as EXACT rationals."""
from fractions import Fraction as Fr
def _d(x): return Fr(x)
WEIGHT_DATA = {
 "riesz4":  ({4: Fr(1)}, Fr(87, 200)),
 "riesz6":  ({6: Fr(1)}, Fr(323, 1000)),
 "riesz10": ({10: Fr(1)}, Fr(213, 1000)),
 "opt4": ({2: _d("0.236295"), 3: _d("-0.549544"), 4: _d("1.313249")}, Fr(454, 1000)),
 "opt6": ({2: _d("0.286157"), 3: _d("-1.603245"), 4: _d("5.712813"), 5: _d("-7.500122"), 6: _d("4.104397")}, Fr(436, 1000)),
 "opt8": ({2: _d("0.296745"), 3: _d("-3.334339"), 4: _d("21.785286"), 5: _d("-69.659964"), 6: _d("120.898712"),
           7: _d("-105.702417"), 8: _d("36.715977")}, Fr(433, 1000)),
}
