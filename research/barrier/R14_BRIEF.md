# Round 14 brief — formalize the asymptotic record c* < 0.7612 (research/barrier/formal0760.md (§1.2 scaling, §3 certificates, §4 Lean plan) — Round 14 generalises Round 13 to weights √n·(n/x)^a·W(β log(x/n)), a = β − 1, β = 3)

Math + plan: `research/barrier/formal0760.md (§1.2 scaling, §3 certificates, §4 Lean plan) — Round 14 generalises Round 13 to weights √n·(n/x)^a·W(β log(x/n)), a = β − 1, β = 3` (§1 Lemma E and the asymptotic argument, §3 certificate,
§4 Lean plan); certificate data `formal076_certificate_{A,B}.json`, `formal076_testfn_{A,B}.json`, script
`formal076_certificate.py`. Fixed hand-off (do not edit): `lean/DetPrimality/Bach/R14Defs.lean (and R13Defs.lean)` — `r13Phi`, `r13W`,
`r13K`, `r13R`, `r13A`, `r13G`, `R13Cert`, Props `R13ZetaSmooth` (P1), `R13ChiExplicit` (P2), `R13ZeroPow` (P3).
All other rules, the build command (`bin/check.sh DetPrimality/<Path>.lean`, CPUs 160–191), and the reusable
infrastructure are as in `research/below-one/R11_BRIEF.md` — read it. Additionally reuse Round 11's proved files:
`R11ChiPerron` (Perron for any order j: `r11Chi_perron_LSeries`, `r11Chi_perron_inv_sub`, `r11Chi_perron_hasSum_poles`),
`R11ChiFormula` (`r11Chi_decomp`), `R11ChiDeriv` (`r11Chi_pole_hasDerivAt`, `r11Chi_zeroPow_eq` for k ≤ 3, summability
lemmas stated for general k), `R11ZeroSum*` (identities at 3/2, `r11Zs_hasDerivAt_tsum`), `R11ZetaX*`
(`r11Zx_main_of_zetaZ`, `r11Zx_formula`), `R11Asm*` (`r11Asm_A0_ge`, `r11Asm_core`, `r11Asm_sum_ge`), `LLSElem`
(`llsElem_no_witness_facts`), research/below-one/r11Asm_gen and research/barrier/r12M4_gen (generators).
New files only: `lean/DetPrimality/Bach/R14<Topic>*.lean`, your assigned prefix. No sorry/admit/axiom/native_decide/
implemented_by/extern (`decide +kernel` OK); `#print axioms` on main theorems: only [propext, Classical.choice,
Quot.sound]. No git commits. Final message ≤ 400 words: exact statements, files, build status, axioms, deviations.

Round 14 specifics: the Round-13 proofs (`R13Zeta.lean` = P1, `R13Chi.lean` = P2, `R13ZeroPow.lean` = P3, `R13Asm*.lean`,
`R13CertGen.lean`, `R13CertB.lean`, generator `research/barrier/r13Cert_gen`) are the templates — Round 14 is the same
argument with the shift a (formal0760 §4 tables give the per-piece route). Certificate data: formal0760_certificate_*.json,
formal0760_testfn_*.json (instances b3m19 = "∀ c > 0.76078", b3m24 = "∀ c > 0.76076"; b1 instances use the existing
β = 1 inputs).
