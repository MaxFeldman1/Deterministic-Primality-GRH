# Round 13 brief — formalize the asymptotic record c* < 0.7612 (research/barrier/formal076.md)

Math + plan: `research/barrier/formal076.md` (§1 Lemma E and the asymptotic argument, §3 certificate,
§4 Lean plan); certificate data `formal076_certificate_{A,B}.json`, `formal076_testfn_{A,B}.json`, script
`formal076_certificate.py`. Fixed hand-off (do not edit): `lean/DetPrimality/Bach/R13Defs.lean` — `r13Phi`, `r13W`,
`r13K`, `r13R`, `r13A`, `r13G`, `R13Cert`, Props `R13ZetaSmooth` (P1), `R13ChiExplicit` (P2), `R13ZeroPow` (P3).
All other rules, the build command (`bin/check.sh DetPrimality/<Path>.lean`, CPUs 160–191), and the reusable
infrastructure are as in `research/below-one/R11_BRIEF.md` — read it. Additionally reuse Round 11's proved files:
`R11ChiPerron` (Perron for any order j: `r11Chi_perron_LSeries`, `r11Chi_perron_inv_sub`, `r11Chi_perron_hasSum_poles`),
`R11ChiFormula` (`r11Chi_decomp`), `R11ChiDeriv` (`r11Chi_pole_hasDerivAt`, `r11Chi_zeroPow_eq` for k ≤ 3, summability
lemmas stated for general k), `R11ZeroSum*` (identities at 3/2, `r11Zs_hasDerivAt_tsum`), `R11ZetaX*`
(`r11Zx_main_of_zetaZ`, `r11Zx_formula`), `R11Asm*` (`r11Asm_A0_ge`, `r11Asm_core`, `r11Asm_sum_ge`), `LLSElem`
(`llsElem_no_witness_facts`), research/below-one/r11Asm_gen and research/barrier/r12M4_gen (generators).
New files only: `lean/DetPrimality/Bach/R13<Topic>*.lean`, your assigned prefix. No sorry/admit/axiom/native_decide/
implemented_by/extern (`decide +kernel` OK); `#print axioms` on main theorems: only [propext, Classical.choice,
Quot.sound]. No git commits. Final message ≤ 400 words: exact statements, files, build status, axioms, deviations.
