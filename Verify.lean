import Mathlib
import GRR.ToddSeries
import GRR.GradedExp
import GRR.GradedHom
import GRR.ToddClass
import GRR.Pullback
import GRR.PushforwardK
import GRR.Statement
import GRR.Projection
import GRR.ClosedImmersion
import GRR.Main
import GRR.HRR
import GRR.ProjectionK
import GRR.ProjectionGen
import GRR.ProjectionTau
import GRR.Koszul
import GRR.Final
import GRR.PerfectCh
import GRR.DeformationGeom
import GRR.Specialization
import GRR.ClosedFormulaCore
import GRR.ZeroSectionRR
import GRR.ClosedImmersionReduce
import GRR.Theorem
#print axioms GRR.grothendieck_riemann_roch
#check @GRR.grothendieck_riemann_roch
#print axioms GRR.toddSeries_mul_one_sub_expNeg
#check @GRR.toddSeries_mul_one_sub_expNeg
#print axioms GRR.coeff_exp_pow_mul_toddSeries_pow
#check @GRR.coeff_exp_pow_mul_toddSeries_pow
#print axioms GRR.coeff_expNeg_pow_mul_toddSeries_pow
#check @GRR.coeff_expNeg_pow_mul_toddSeries_pow
#print axioms GRR.coeff_toddSeries_eq_coeff_sum_logTodd_pow
#check @GRR.coeff_toddSeries_eq_coeff_sum_logTodd_pow
#print axioms GRR.GradedComplete.gexp_add
#check @GRR.GradedComplete.gexp_add
#print axioms GRR.GradedComplete.gexp_zero
#check @GRR.GradedComplete.gexp_zero
#print axioms GRR.GradedComplete.isUnit_gexp
#check @GRR.GradedComplete.isUnit_gexp
#print axioms GRR.GradedComplete.ev_mul
#check @GRR.GradedComplete.ev_mul
#print axioms GRR.GradedComplete.ev_add
#check @GRR.GradedComplete.ev_add
#print axioms GRR.GradedComplete.ev_smul
#check @GRR.GradedComplete.ev_smul
#print axioms GRR.GradedComplete.ev_one
#check @GRR.GradedComplete.ev_one
#print axioms GRR.GradedComplete.ev_X
#check @GRR.GradedComplete.ev_X
#print axioms GRR.GradedComplete.commute_weight_of_commute_scaling
#check @GRR.GradedComplete.commute_weight_of_commute_scaling
#print axioms GRR.GradedComplete.gexp_ev
#check @GRR.GradedComplete.gexp_ev
#print axioms GRR.GradedComplete.toddOf_add
#check @GRR.GradedComplete.toddOf_add
#print axioms GRR.GradedComplete.toddOf_zero
#check @GRR.GradedComplete.toddOf_zero
#print axioms GRR.GradedComplete.toddOf_mul_toddOf_neg
#check @GRR.GradedComplete.toddOf_mul_toddOf_neg
#print axioms GRR.GradedComplete.isUnit_toddOf
#check @GRR.GradedComplete.isUnit_toddOf
#print axioms GRR.GradedComplete.toddOf_ev_exp
#check @GRR.GradedComplete.toddOf_ev_exp
#print axioms GRR.GradedComplete.ev_toddSeries_mul_one_sub_ev_expNeg
#check @GRR.GradedComplete.ev_toddSeries_mul_one_sub_ev_expNeg
#print axioms GRR.isSmoothFT_of_isSmoothVariety
#check @GRR.isSmoothFT_of_isSmoothVariety
#print axioms GRR.vectorBundleEquiv_classOf
#check @GRR.vectorBundleEquiv_classOf
#print axioms GRR.commute_weight_ch
#check @GRR.commute_weight_ch
#print axioms GRR.toddClass_add
#check @GRR.toddClass_add
#print axioms GRR.toddClass_zero
#check @GRR.toddClass_zero
#print axioms GRR.toddClass_classOf_of_shortExact
#check @GRR.toddClass_classOf_of_shortExact
#print axioms GRR.toddClass_mul_toddClass_neg
#check @GRR.toddClass_mul_toddClass_neg
#print axioms GRR.isUnit_toddClass
#check @GRR.isUnit_toddClass
#print axioms GRR.commute_toddClass_ch
#check @GRR.commute_toddClass_ch
#print axioms GRR.commute_toddClass_toddClass
#check @GRR.commute_toddClass_toddClass
#print axioms GRR.isHom_firstChernQ
#check @GRR.isHom_firstChernQ
#print axioms GRR.ch_classOf_invertible
#check @GRR.ch_classOf_invertible
#print axioms GRR.toddClass_classOf_invertible
#check @GRR.toddClass_classOf_invertible
#print axioms GRR.GradedComplete.IsGradedHom.map_gexp
#check @GRR.GradedComplete.IsGradedHom.map_gexp
#print axioms GRR.GradedComplete.IsGradedHom.map_weight
#check @GRR.GradedComplete.IsGradedHom.map_weight
#print axioms GRR.GradedComplete.IsGradedHom.map_ev
#check @GRR.GradedComplete.IsGradedHom.map_ev
#print axioms GRR.GradedComplete.IsGradedHom.map_toddOf
#check @GRR.GradedComplete.IsGradedHom.map_toddOf
#print axioms GRR.pullbackAQ_apply
#check @GRR.pullbackAQ_apply
#print axioms GRR.isGradedHom_pullbackAQ
#check @GRR.isGradedHom_pullbackAQ
#print axioms GRR.pullbackAQ_ch
#check @GRR.pullbackAQ_ch
#print axioms GRR.pullbackAQ_toddClass
#check @GRR.pullbackAQ_toddClass
#print axioms GRR.rationalProperChowPushforward_totalRationalChowCap_pullbackAQ
#check @GRR.rationalProperChowPushforward_totalRationalChowCap_pullbackAQ
#print axioms GRR.pushforwardK_mk
#check @GRR.pushforwardK_mk
#print axioms GRR.pushforwardK_mk_of_isZero
#check @GRR.pushforwardK_mk_of_isZero
#print axioms GRR.sum_range_higherDirectImageCoh_add
#check @GRR.sum_range_higherDirectImageCoh_add
#print axioms GRR.pushforwardK_mk_of_isClosedImmersion
#check @GRR.pushforwardK_mk_of_isClosedImmersion
#print axioms GRR.pushforwardK_comp_of_isClosedImmersion
#check @GRR.pushforwardK_comp_of_isClosedImmersion
#print axioms GRR.rationalProperChowPushforward_comp
#check @GRR.rationalProperChowPushforward_comp
#print axioms GRR.riemannRochFor_comp
#check @GRR.riemannRochFor_comp
#print axioms GRR.isSmoothFT_projectiveSpaceOver
#check @GRR.isSmoothFT_projectiveSpaceOver
#print axioms GRR.isProper_projectiveSpaceOver_hom
#check @GRR.isProper_projectiveSpaceOver_hom
#print axioms GRR.riemannRochFor_of_isProjectiveMorphism
#check @GRR.riemannRochFor_of_isProjectiveMorphism
#print axioms GRR.riemannRochFor_projection_of
#check @GRR.riemannRochFor_projection_of
#print axioms GRR.isFiniteLocallyFree_conormalSheaf
#check @GRR.isFiniteLocallyFree_conormalSheaf
#print axioms GRR.ch_classOf_dualSheaf
#check @GRR.ch_classOf_dualSheaf
#print axioms GRR.toddTangent_eq
#check @GRR.toddTangent_eq
#print axioms GRR.cap_mul
#check @GRR.cap_mul
#print axioms GRR.riemannRochFor_of_closedImmersionFormula
#check @GRR.riemannRochFor_of_closedImmersionFormula
#print axioms GRR.closedImmersionFormula
#check @GRR.closedImmersionFormula
#print axioms GRR.riemannRochFor_closedImmersion
#check @GRR.riemannRochFor_closedImmersion
#print axioms GRR.projectionPushforwardFormula
#check @GRR.projectionPushforwardFormula
#print axioms GRR.projectionGeneration
#check @GRR.projectionGeneration
#print axioms GRR.projectionTauFormula
#check @GRR.projectionTauFormula
#print axioms GRR.riemannRochFor_projectiveSpaceOver
#check @GRR.riemannRochFor_projectiveSpaceOver
#print axioms GRR.grothendieck_riemann_roch_of
#check @GRR.grothendieck_riemann_roch_of
#print axioms GRR.eulerK_mk
#check @GRR.eulerK_mk
#print axioms GRR.eulerK_pushforwardK
#check @GRR.eulerK_pushforwardK
#print axioms GRR.isSmoothFT_id
#check @GRR.isSmoothFT_id
#print axioms GRR.tau_point
#check @GRR.tau_point
#print axioms GRR.hirzebruch_riemann_roch_of
#check @GRR.hirzebruch_riemann_roch_of
#print axioms GRR.hirzebruch_riemann_roch
#check @GRR.hirzebruch_riemann_roch
#print axioms GRR.higherDirectImageTensorIso
#check @GRR.higherDirectImageTensorIso
#print axioms GRR.ProjectionGen.exists_X_pow_eq_sum_expNeg_pow
#check @GRR.ProjectionGen.exists_X_pow_eq_sum_expNeg_pow
#print axioms GRR.ProjectionGen.ch_twistClass_neg
#check @GRR.ProjectionGen.ch_twistClass_neg
#print axioms GRR.ProjectionGen.exists_eq_sum_cap_pow_smoothGysinRational
#check @GRR.ProjectionGen.exists_eq_sum_cap_pow_smoothGysinRational
#print axioms GRR.ProjectionGen.cap_firstChernQ_pow_succ_eq_zero
#check @GRR.ProjectionGen.cap_firstChernQ_pow_succ_eq_zero
#print axioms GRR.toddTangent_projectiveSpaceOver
#check @GRR.toddTangent_projectiveSpaceOver
#print axioms GRR.pushforward_cap_pullbackAQ_mul_ev
#check @GRR.pushforward_cap_pullbackAQ_mul_ev
#print axioms GRR.ch_koszul
#check @GRR.ch_koszul
#print axioms GRR.grothendieck_riemann_roch_of_closedImmersionFormula
#check @GRR.grothendieck_riemann_roch_of_closedImmersionFormula
#print axioms GRR.hirzebruch_riemann_roch_projectiveSpace
#check @GRR.hirzebruch_riemann_roch_projectiveSpace
#print axioms GRR.hirzebruch_riemann_roch_of_closedImmersionFormula
#check @GRR.hirzebruch_riemann_roch_of_closedImmersionFormula
#print axioms GRR.isFiniteLocallyFree_tangentSheaf
#check @GRR.isFiniteLocallyFree_tangentSheaf
#print axioms GRR.perfectCh_congr
#check @GRR.perfectCh_congr
#print axioms GRR.perfectCh_eq_zero
#check @GRR.perfectCh_eq_zero
#print axioms GRR.pullbackAQ_perfectCh
#check @GRR.pullbackAQ_perfectCh
#print axioms GRR.perfectCh_single
#check @GRR.perfectCh_single
#print axioms GRR.perfectCh_derivedTensor
#check @GRR.perfectCh_derivedTensor
#print axioms GRR.hasDefinedChernClasses_single_coherent
#check @GRR.hasDefinedChernClasses_single_coherent
#print axioms GRR.chK_mk_eq_perfectCh
#check @GRR.chK_mk_eq_perfectCh
#print axioms GRR.chK_pushforwardK_classOf_eq_perfectCh
#check @GRR.chK_pushforwardK_classOf_eq_perfectCh
#print axioms GRR.closedImmersionFormula_of_bundles
#check @GRR.closedImmersionFormula_of_bundles
#print axioms GRR.isSmoothFT_blowupAtInfinity
#check @GRR.isSmoothFT_blowupAtInfinity
#print axioms GRR.DeformationGeom.isRegularImmersion_of_isSmoothFT
#check @GRR.DeformationGeom.isRegularImmersion_of_isSmoothFT
#print axioms GRR.derivedPullbackSinglePushforwardIsoOfTorIndependent
#check @GRR.derivedPullbackSinglePushforwardIsoOfTorIndependent
#print axioms GRR.deformationZeroFibreIso
#check @GRR.deformationZeroFibreIso
#print axioms GRR.deformationExceptionalFibreIso
#check @GRR.deformationExceptionalFibreIso
#print axioms GRR.isZero_deformationStrictTransform
#check @GRR.isZero_deformationStrictTransform
#print axioms GRR.exists_specialization_fundamentalClass
#check @GRR.exists_specialization_fundamentalClass
#print axioms GRR.isSmoothFT_projectiveCompletion
#check @GRR.isSmoothFT_projectiveCompletion
#print axioms GRR.ZeroSectionRR.isIso_bundleProj_unitModule
#check @GRR.ZeroSectionRR.isIso_bundleProj_unitModule
#print axioms GRR.perfectCh_pushforward_zeroSection
#check @GRR.perfectCh_pushforward_zeroSection
#print axioms GRR.perfectCh_pushforward_zeroSection_unit
#check @GRR.perfectCh_pushforward_zeroSection_unit
#print axioms GRR.cap_topClass_fundamentalClass
#check @GRR.cap_topClass_fundamentalClass
#print axioms GRR.pullback_zeroSection_classOf_dual_koszulModule
#check @GRR.pullback_zeroSection_classOf_dual_koszulModule
#print axioms GRR.zeroSection_formula
#check @GRR.zeroSection_formula
#print axioms GRR.conormalSheafIsoConormalModule
#check @GRR.conormalSheafIsoConormalModule
#print axioms GRR.normalClass_eq_classOf_dualSheaf_bundle
#check @GRR.normalClass_eq_classOf_dualSheaf_bundle
#print axioms GRR.closedImmersionFormula_core_of
#check @GRR.closedImmersionFormula_core_of
#print axioms GRR.closedImmersionFormula_core
#check @GRR.closedImmersionFormula_core
#print axioms GRR.closedImmersionFormula_comp
#check @GRR.closedImmersionFormula_comp
#print axioms GRR.closedImmersionFormula_of_comp
#check @GRR.closedImmersionFormula_of_comp
#print axioms GRR.closedImmersionFormula_ι
#check @GRR.closedImmersionFormula_ι
#print axioms GRR.closedImmersionFormula_of_isClopenDecomposition
#check @GRR.closedImmersionFormula_of_isClopenDecomposition
#print axioms GRR.closedImmersionFormula_of_restrict
#check @GRR.closedImmersionFormula_of_restrict
#print axioms GRR.closedImmersionFormula_of_codim_zero
#check @GRR.closedImmersionFormula_of_codim_zero
#print axioms GRR.closedImmersionFormula_of_core
#check @GRR.closedImmersionFormula_of_core
