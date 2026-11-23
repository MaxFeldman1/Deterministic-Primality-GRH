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
-- Round 5: c = 22 (Bach/Constant22.lean; Constant28.lean is an independent c = 28 proof)
#print axioms DetPrimality.Bach.grh_implies_bach_c22
#print axioms DetPrimality.Bach.bachBoundChar_of_GRH_c22
#print axioms DetPrimality.Bach.grh_implies_bach_c28
#print axioms DetPrimality.bachBound_22_of_GRH
#print axioms DetPrimality.millerDet_correct_of_GRH
#print axioms DetPrimality.sqrtModDet_correct_of_GRH
#print axioms DetPrimality.sqrtModDet_isSome_iff_of_GRH
#print axioms DetPrimality.millerDet_correct_of_GRH_46
#print axioms DetPrimality.sqrtModDet_correct_of_GRH_46
#print axioms DetPrimality.sqrtModDet_isSome_iff_of_GRH_46
-- Round 6: c = 8 (Bach/ConstantLow.lean; also c = 9 there and c = 13 in ConstantMid.lean)
#print axioms DetPrimality.Bach.grh_implies_bach_c8
#print axioms DetPrimality.Bach.bachBoundChar_of_GRH_c8
#print axioms DetPrimality.Bach.grh_implies_bach_c9
#print axioms DetPrimality.Bach.grh_implies_bach_c13
#print axioms DetPrimality.Bach.zeroSum_le_sharp32
#print axioms DetPrimality.Bach.zeroSum_le_sharp2
#print axioms DetPrimality.Bach.psiOne_lower_grid
#print axioms DetPrimality.bachBound_8_of_GRH
#print axioms DetPrimality.millerDet_correct_of_GRH
#print axioms DetPrimality.sqrtModDet_correct_of_GRH
#print axioms DetPrimality.sqrtModDet_isSome_iff_of_GRH
#print axioms DetPrimality.millerDet_correct_of_GRH_22

-- Round 7: Bach's Theorem 2 form for composite moduli, c = 73/50 (ConstantTwo), c = 3, c = 4
#print axioms DetPrimality.Bach.grh_implies_bach_composite_c146
#print axioms DetPrimality.Bach.grh_implies_bach_composite_c2
#print axioms DetPrimality.Bach.grh_implies_bach_composite_c3
#print axioms DetPrimality.Bach.grh_implies_bach_composite_c4
#print axioms DetPrimality.Bach.zeroSum_le_twoPoint
#print axioms DetPrimality.Bach.zeroSum_le_gain_240
#print axioms DetPrimality.Bach.psiOne_lower_cheb30_sharp
#print axioms DetPrimality.Bach.psiOne_lower_grid2
#print axioms DetPrimality.Bach.composite_no_witness_facts
#print axioms DetPrimality.Miller.millerDet_correct_of_composite
#print axioms DetPrimality.bachBoundComposite_146_of_GRH
#print axioms DetPrimality.millerDet_correct_of_GRH
#print axioms DetPrimality.millerDet_correct_of_GRH_2
#print axioms DetPrimality.millerDet_correct_of_GRH_8
#print axioms DetPrimality.sqrtModDet_correct_of_GRH

-- Round 8: Lamzouri–Li–Soundararajan Theorem 1.1(2), c = 1 (Bach/LLS*.lean, Miller/LLS*.lean)
#print axioms DetPrimality.Bach.llsZL_main
#print axioms DetPrimality.Bach.llsPer_chiUpper
#print axioms DetPrimality.Bach.llsGain_main
#print axioms DetPrimality.Bach.llsElem_weightedLower
#print axioms DetPrimality.Bach.llsZeta_zeroSumSq_le
#print axioms DetPrimality.Bach.llsAsm_bachBound_one
#print axioms DetPrimality.Miller.llsElem_millerDet_one_small
#print axioms DetPrimality.Miller.llsAsm_millerDet_one_correct'
#print axioms DetPrimality.bachBoundComposite_one_ge_3000_of_GRH
#print axioms DetPrimality.millerDet_correct_of_GRH
#print axioms DetPrimality.millerDet_correct_of_GRH_146
#print axioms DetPrimality.Bach.llsPrime_bachBound_one_all_of_GRH
#print axioms DetPrimality.TonelliShanks.llsPrime_sqrtModDet_correct
#print axioms DetPrimality.sqrtModDet_correct_of_GRH
#print axioms DetPrimality.sqrtModDet_isSome_iff_of_GRH
#print axioms DetPrimality.sqrtModDet_correct_of_GRH_8

-- Rounds 11–12: explicit constants below 1 (designB; index ≥ 4 for Miller)
#print axioms DetPrimality.r11_inputs
#print axioms DetPrimality.charBound_table_of_GRH
#print axioms DetPrimality.charBound_eventually_of_GRH
#print axioms DetPrimality.subgroupBound_table_of_GRH
#print axioms DetPrimality.subgroupBound_eventually_of_GRH
#print axioms DetPrimality.millerDet_correct_of_GRH_70
#print axioms DetPrimality.millerDet_correct_of_GRH_65
#print axioms DetPrimality.millerDetBest_correct_of_GRH
#print axioms DetPrimality.Miller.liar4_exists_subgroup
