import DetPrimality

/-! Axiom audit (not imported by the library). Compile with `bin/check.sh DetPrimality/Audit.lean`. -/

open DetPrimality

-- End-to-end
#print axioms DetPrimality.millerDet_correct_of_GRH
#print axioms DetPrimality.sqrtModDet_correct_of_GRH
#print axioms DetPrimality.sqrtModDet_isSome_iff_of_GRH
-- Layer 2, round 2 (sorry-free chain, Bach/Assembly.lean)
#print axioms DetPrimality.Bach.grh_implies_bach_v2
#print axioms DetPrimality.Bach.bachBoundChar_of_GRH_v2
#print axioms DetPrimality.Bach.bachInputs
#print axioms DetPrimality.Bach.grh_implies_bach_of_inputs
#print axioms DetPrimality.Bach.growth_completedLFunction
#print axioms DetPrimality.Bach.hadamardLogDeriv_of_growth
#print axioms DetPrimality.Bach.summable_zeroOrd_div_normSq_proof
#print axioms DetPrimality.Bach.summable_zeroOrd_div_normSq_of_growth
#print axioms DetPrimality.Bach.re_logDeriv_eq_tsum_of_growth
#print axioms DetPrimality.Bach.explicit_formula_bound_of_hadamard
#print axioms DetPrimality.Bach.Numerics.tsum_vonMangoldt_term_two_le_proof
#print axioms DetPrimality.Bach.Numerics.tsum_vonMangoldt_term_two_le_three_quarters
-- Layer 2, round 1 (Blueprint chain, kept for reference; uses the 4 Blueprint sorries)
#print axioms DetPrimality.Bach.blueprintInputs
#print axioms DetPrimality.bachBound_1024_of_GRH
#print axioms DetPrimality.Bach.grh_implies_bach
#print axioms DetPrimality.Bach.bachBoundChar_of_GRH
#print axioms DetPrimality.Bach.bachBound_of_bachBoundChar
#print axioms DetPrimality.Bach.zeroSum_le
#print axioms DetPrimality.Bach.norm_smoothPsi_le
#print axioms DetPrimality.Bach.re_smoothPsi_primitive_lower
-- Characters bridge
#print axioms DetPrimality.bachBound_iff_bachBoundChar
#print axioms DetPrimality.exists_dirichletCharacter_trivial_on
#print axioms DetPrimality.exists_nonresidue_lt_of_bachBound
-- Layers 3-4: Miller
#print axioms DetPrimality.Miller.millerDet_correct
#print axioms DetPrimality.Miller.exists_proper_subgroup_strongLiars
#print axioms DetPrimality.Miller.millerDet_of_prime
#print axioms DetPrimality.Miller.millerBound_ge
-- Layer 4: Tonelli-Shanks
#print axioms DetPrimality.TonelliShanks.sqrtModDet_correct
#print axioms DetPrimality.TonelliShanks.sqrtModDet_sound
#print axioms DetPrimality.TonelliShanks.sqrtModDet_isSome_iff
#print axioms DetPrimality.TonelliShanks.tonelliShanks_correct
-- Round 3: c = 64 (Bach/Constant.lean, ConstPsiOne.lean, ConstNoncoprime.lean)
#print axioms DetPrimality.Bach.grh_implies_bach_c
#print axioms DetPrimality.Bach.bachBoundChar_of_GRH_c
#print axioms DetPrimality.Bach.psiOne_lower_integral
#print axioms DetPrimality.Bach.noncoprimeSum_le_of_ge_4096
#print axioms DetPrimality.bachBound_64_of_GRH
#print axioms DetPrimality.millerDet_correct_of_GRH_1024
#print axioms DetPrimality.sqrtModDet_correct_of_GRH_1024
#print axioms DetPrimality.sqrtModDet_isSome_iff_of_GRH_1024
-- Round 4: c = 46 (Bach/Constant46.lean, ConstPsiTheta.lean; ConstPsiOneSharp.lean is proved but not needed)
#print axioms DetPrimality.Bach.grh_implies_bach_c46
#print axioms DetPrimality.Bach.bachBoundChar_of_GRH_c46
#print axioms DetPrimality.Bach.final_numeric_46
#print axioms DetPrimality.Bach.log_ge_of_no_small_witness_46
#print axioms DetPrimality.Bach.noncoprimeSum_le_small
#print axioms DetPrimality.Bach.psi_sub_theta_le_small
#print axioms DetPrimality.Bach.noncoprimeSum_le_of_ge_2500_of_lt_65536
#print axioms DetPrimality.Bach.psiOne_lower_2048
#print axioms DetPrimality.bachBound_46_of_GRH
#print axioms DetPrimality.millerDet_correct_of_GRH_64
#print axioms DetPrimality.sqrtModDet_correct_of_GRH_64
#print axioms DetPrimality.sqrtModDet_isSome_iff_of_GRH_64
