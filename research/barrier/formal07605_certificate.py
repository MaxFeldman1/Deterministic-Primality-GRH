"""formal07605: exact certificate (stdlib only, rational arithmetic) for the designs of formal07605_design.py.
   This is formal0760_certificate.main (generic in beta and in the number p of exact sign changes) applied to
   formal07605_testfn_<name>.json; it writes formal07605_certificate_<name>.json and prints the certified c*
   exactly and with 12-digit exponential enclosures (as used by the Lean generator formal07605_emit.py).
   usage: formal07605_certificate.py formal07605_testfn_<name>.json [...]"""
import sys, os
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from formal0760_certificate import main
if __name__=="__main__":
    for fn in sys.argv[1:]:
        assert "formal07605_testfn_" in fn
        main(fn); main(fn,expdigits=12)
