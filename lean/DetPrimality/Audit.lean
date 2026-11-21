import DetPrimality

/-! Axiom audit (not imported by the library). Compile with `bin/check.sh DetPrimality/Audit.lean`. -/

open DetPrimality

-- End-to-end
#print axioms DetPrimality.millerDet_correct_of_GRH
#print axioms DetPrimality.sqrtModDet_correct_of_GRH
#print axioms DetPrimality.sqrtModDet_isSome_iff_of_GRH
-- Layer 2 (GRH ⟹ Bach)
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
