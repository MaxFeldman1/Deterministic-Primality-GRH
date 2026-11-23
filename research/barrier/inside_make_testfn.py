"""Produce the explicit test function used in the certificate: solve the SOCP at (beta, c, D), round the
coefficients q_n to 8 decimals, store them as exact decimal strings in inside_testfn.json."""
import sys, json, numpy as np
from inside_primal_socp import solve, evaluate
beta, c, D = float(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3])
val, qv = solve(beta, c, D, M=8000, panels=120)
qv = qv/ (np.mean(np.abs(np.polynomial.polynomial.polyval(np.exp(-1j*(np.arange(200000)+0.5)*np.pi/200000), qv)))/2)
qs = ["%.8f" % x for x in qv]
J, N, I = evaluate(beta, c, np.array([float(s) for s in qs]))
print("SOCP value %.8f; rounded coefficients: J = %.8f (N = %.8f, I = %.8f), c_inf = %.7f" % (val, J, N, I, J**-2))
json.dump({"beta": sys.argv[1], "c": sys.argv[2], "D": D, "q": qs, "float_J": J}, open("inside_testfn.json", "w"), indent=1)
