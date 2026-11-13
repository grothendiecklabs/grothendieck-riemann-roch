import GRR.PerfectCh
import GRR.Koszul
import GRR.ProjectionK
import GRR.ProjectionTau
import StacksFrontier.AlgebraicGeometry.Chow.ZeroSectionKoszul.ChernClassZeroSection
import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.RegularImmersionDeformationChernZeroSection
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyFreeSmooth
import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SubbundleTwist
import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.Inputs
import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Formula
import StacksFrontier.AlgebraicGeometry.Morphism.KerChart
import StacksFrontier.AlgebraicGeometry.ReflexiveHull.UnitDual
import StacksFrontier.AlgebraicGeometry.Reflexive.DualMap

/-!
# Riemann–Roch for the zero section of `P̄ = 𝐏(𝒞 ⊕ 𝒪_X)`

`X` smooth over a field, `𝒞` finite locally free of rank `r`, `π : P̄ ⟶ X`, zero section
`s : 𝐏(𝒪_X) ⟶ P̄`, `ρ = π ∘ s` (an isomorphism), Koszul module `ℰ = π^*𝒞 ⊗ 𝒪(-1)`. Items B0–B5
of `notes/E_plan.md`: `P̄` is smooth (`GRR.isSmoothFT_projectiveCompletion`); `ch(s_*𝒪) =
ch(λ_{-1}ℰ)` (`GRR.perfectCh_pushforward_zeroSection_unit`); `ch(λ_{-1}ℰ) td([ℰ^∨]) ∩ [P̄] =
s_*[𝐏(𝒪_X)]`, i.e. `c_r(ℰ) ∩ [P̄] = (-1)^r s_*[𝐏(𝒪_X)]`, by uniqueness in the projective bundle
formula (`GRR.cap_topClass_fundamentalClass`);
`s^*[ℰ^∨] = ρ^*[𝒞^∨]` (`GRR.pullback_zeroSection_classOf_dual_koszulModule`); and
`π_*(ch(s_*ρ^*E) ∩ [P̄]) = (ch(E) · td(-[𝒞^∨])) ∩ [X]` (`GRR.zeroSection_formula`).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open Stacks.ProjectiveCompletion (projectiveCompletion projectiveCompletionProj zeroSection
  koszulModule completionModule
  vectorBundleZeroSection_comp_toCompletion_comp_projectiveCompletionProj)
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf)
open scoped TensorProduct

universe u

namespace GRR

attribute [local instance 10000] HasDerivedCategory.standard

section Geometry

variable {X : Scheme.{u}} (𝒞 : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞]
  (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r]

include r in
theorem ZeroSectionRR.smooth_projectiveCompletionProj : Smooth (projectiveCompletionProj 𝒞) :=
  Stacks.Chow.smooth_bundleProj (completionModule 𝒞) r

theorem ZeroSectionRR.smooth_bundleProj_unitModule (X : Scheme.{u}) :
    Smooth (bundleProj (Stacks.Ample.unitModule X)) :=
  haveI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.Ample.unitModule X) (0 + 1) :=
    AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_unit X
  Stacks.Chow.smooth_bundleProj (Stacks.Ample.unitModule X) 0

include r in
/-- **B0**: the projective completion of a vector bundle on a smooth `X` is smooth. -/
theorem isSmoothFT_projectiveCompletion (k : Type u) [Field k] (sX : X ⟶ Spec (.of k))
    [IsSmoothFT k sX] : IsSmoothFT k (projectiveCompletionProj 𝒞 ≫ sX) :=
  haveI := ZeroSectionRR.smooth_projectiveCompletionProj 𝒞 r
  { smooth := inferInstance
    isSeparated := inferInstance
    quasiCompact := inferInstance }

/-- `𝐏(𝒪_X)` is smooth when `X` is. -/
theorem ZeroSectionRR.isSmoothFT_bundleProj_unitModule (k : Type u) [Field k]
    (sX : X ⟶ Spec (.of k)) [IsSmoothFT k sX] :
    IsSmoothFT k (bundleProj (Stacks.Ample.unitModule X) ≫ sX) :=
  haveI := ZeroSectionRR.smooth_bundleProj_unitModule X
  { smooth := inferInstance
    isSeparated := inferInstance
    quasiCompact := inferInstance }

include 𝒞 r in
/-- `ρ : 𝐏(𝒪_X) ⟶ X` is an isomorphism. -/
theorem ZeroSectionRR.isIso_bundleProj_unitModule [IsLocallyNoetherian X] :
    IsIso (bundleProj (Stacks.Ample.unitModule X)) := by
  have hker := Stacks.ProjectiveCompletion.ker_vectorBundleZeroSection_comp_toCompletion (E := 𝒞) r
  obtain ⟨θ, hθ⟩ : ∃ θ : bundle (Stacks.Ample.unitModule X) ≅ X,
      θ.hom ≫ (Scheme.Modules.vectorBundleLiftZero 𝒞 ≫ Stacks.ProjectiveCompletion.toCompletion 𝒞) =
        zeroSection 𝒞 :=
    ⟨_, Stacks.AlgebraicGeometry.KerChart.isoOfKerEq_hom_comp _ _ hker⟩
  have h : bundleProj (Stacks.Ample.unitModule X) = θ.hom := by
    rw [← Stacks.ProjectiveCompletion.zeroSection_comp_projectiveCompletionProj 𝒞, ← hθ]
    simp only [Category.assoc,
      vectorBundleZeroSection_comp_toCompletion_comp_projectiveCompletionProj,
      Category.comp_id]
  rw [h]
  infer_instance

/-- `s^*𝒪_{P̄}(1) ≅ 𝒪`. -/
noncomputable def ZeroSectionRR.pullbackTwistIso :
    (Scheme.Modules.pullback (zeroSection 𝒞)).obj (bundleTwist (completionModule 𝒞)) ≅
      SheafOfModules.unit (bundle (Stacks.Ample.unitModule X)).ringCatSheaf :=
  haveI := AlgebraicGeometry.SheafOfModules.isInvertible_unit X.presheaf X.ringCatSheaf.2
  GenuineChern.bundleEmbeddingTwistIso (Stacks.ProjectiveCompletion.completionSnd 𝒞) ≪≫
    (GenuineChern.bundleTwistIsoOfRankOne (Stacks.Ample.unitModule X)).symm ≪≫
    Scheme.Modules.pullbackUnitIso _

/-- `s^*π^*𝒞 ≅ ρ^*𝒞`. -/
noncomputable def ZeroSectionRR.pullbackPullbackIso (M : X.Modules) :
    (Scheme.Modules.pullback (zeroSection 𝒞)).obj
        ((Scheme.Modules.pullback (projectiveCompletionProj 𝒞)).obj M) ≅
      (Scheme.Modules.pullback (bundleProj (Stacks.Ample.unitModule X))).obj M :=
  (Scheme.Modules.pullbackComp (zeroSection 𝒞) (projectiveCompletionProj 𝒞)).app M ≪≫
    (Scheme.Modules.pullbackCongr
      (Stacks.ProjectiveCompletion.zeroSection_comp_projectiveCompletionProj 𝒞)).app M

/-- `s^*ℰ ≅ ρ^*𝒞` for the Koszul module `ℰ = π^*𝒞 ⊗ 𝒪(1)^∨`. -/
noncomputable def ZeroSectionRR.pullbackKoszulModuleIso :
    (Scheme.Modules.pullback (zeroSection 𝒞)).obj (koszulModule 𝒞) ≅
      (Scheme.Modules.pullback (bundleProj (Stacks.Ample.unitModule X))).obj 𝒞 :=
  haveI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (bundleTwist (completionModule 𝒞)) 1 :=
    isFiniteLocallyFreeOfRank_one_of_isInvertible _
  haveI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (bundleTwist (completionModule 𝒞)) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1
  Stacks.Chow.pullbackTensorObjIso (zeroSection 𝒞) _ _ ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso
      (ZeroSectionRR.pullbackPullbackIso 𝒞 𝒞)).app _ ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso
      (VectorBundleKZero.pullbackDualSheafIso (zeroSection 𝒞) _
          (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree _) ≪≫
        Stacks.AlgebraicGeometry.ReflexiveModules.dualSheafIsoOfIso
          (ZeroSectionRR.pullbackTwistIso 𝒞).symm ≪≫
        Stacks.AlgebraicGeometry.ReflexiveModules.unitDualIso _) ≪≫
    Stacks.Chow.tensorObjUnitIso _ _

include r in
/-- **B4**: `s^*[ℰ^∨] = ρ^*[𝒞^∨]` in `K₀(Vect 𝐏(𝒪_X))`. -/
theorem pullback_zeroSection_classOf_dual_koszulModule :
    VectorBundleKZero.pullback (zeroSection 𝒞)
        (VectorBundleKZero.classOf _ (dualSheaf (koszulModule 𝒞))) =
      VectorBundleKZero.pullback (bundleProj (Stacks.Ample.unitModule X))
        (VectorBundleKZero.classOf X (dualSheaf 𝒞)) := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (koszulModule 𝒞) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ r
  rw [pullback_classOf_dualSheaf, pullback_classOf_dualSheaf]
  have := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank (koszulModule 𝒞) r (zeroSection 𝒞)
  have hd := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf
    ((Scheme.Modules.pullback (zeroSection 𝒞)).obj (koszulModule 𝒞)) r inferInstance
  exact VectorBundleKZero.classOf_eq_of_iso
    (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheafIsoOfIso
      (ZeroSectionRR.pullbackKoszulModuleIso 𝒞).symm)
    (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ r)

end Geometry

/-! ### B1: the Koszul resolution of the zero section -/

section Koszul

namespace ZeroSectionRR

variable {Y : Scheme.{u}} {F : DerivedCategory Y.Modules} {ℰ : Y.Modules} (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} ℰ r]
  (R : ExteriorPowerResolution F ℰ)

theorem isStrictlyGE_complex : R.complex.IsStrictlyGE (-(r : ℤ)) :=
  (CochainComplex.isStrictlyGE_iff _ _).2 fun m hm ↦ R.isZero_X_of_lt r m hm

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} ℰ r] in
theorem isStrictlyLE_complex : R.complex.IsStrictlyLE 0 :=
  (CochainComplex.isStrictlyLE_iff _ _).2 fun m hm ↦ R.isZero_of_pos m hm

include r in
/-- An exterior-power resolution is a bounded complex of finite locally free modules. -/
theorem boundedFiniteLocallyFreeComplex_complex :
    Stacks.Perfect.BoundedLocallyFreeComplexes.boundedFiniteLocallyFreeComplex Y R.complex :=
  ⟨⟨(CochainComplex.plus_iff _ _).2 ⟨_, isStrictlyGE_complex r R⟩,
      (CochainComplex.minus_iff _).2 ⟨_, isStrictlyLE_complex R⟩⟩, fun i ↦ by
    have := R.isFiniteLocallyFreeOfRank_X r i
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R.complex.X i) :=
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _
        (exteriorPowerRanks r i)
    exact Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree _⟩

/-- Reindexing `∑_{-r ≤ i ≤ 0} f(i)` as `∑_{p ≤ r} f(-p)`. -/
theorem sum_Icc_neg_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℤ → M) :
    ∑ i ∈ Finset.Icc (-(r : ℤ)) 0, f i = ∑ p ∈ Finset.range (r + 1), f (-(p : ℤ)) := by
  symm
  refine Finset.sum_nbij' (fun p : ℕ ↦ -(p : ℤ)) (fun i ↦ (-i).toNat) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_range] at hp
    rw [Finset.mem_Icc]
    omega
  · intro i hi
    rw [Finset.mem_Icc] at hi
    rw [Finset.mem_range]
    omega
  · intro p _
    simp only [neg_neg, Int.toNat_natCast]
  · intro i hi
    rw [Finset.mem_Icc] at hi
    rw [Int.toNat_of_nonneg (by omega), neg_neg]
  · intro p _
    rfl

/-- **The Euler characteristic of an exterior-power resolution** is `λ_{-1}(ℰ)`. -/
theorem eulerCharComplex_complex :
    Stacks.Perfect.BoundedLocallyFreeComplexes.eulerCharComplex Y R.complex = lambdaNegOne ℰ r := by
  rw [Stacks.Perfect.BoundedLocallyFreeComplexes.eulerCharComplex_eq_sum Y R.complex _ _
    (isStrictlyGE_complex r R) (isStrictlyLE_complex R), sum_Icc_neg_eq_sum_range, lambdaNegOne]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have := R.isFiniteLocallyFreeOfRank_X r (-(p : ℤ))
  rw [Int.negOnePow_neg, Int.coe_negOnePow_natCast,
    VectorBundleKZero.classOf_eq_of_iso (R.termIso p)
      (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _
        (exteriorPowerRanks r (-(p : ℤ))))]

end ZeroSectionRR

variable {X : Scheme.{u}} (𝒞 : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞]
  (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r]
  (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **B1**: the Chern character of `s_*𝒪` is that of the Koszul complex,
`ch(s_*𝒪) = ch(λ_{-1}(ℰ))`, `ℰ = π^*𝒞 ⊗ 𝒪(-1)`. -/
theorem perfectCh_pushforward_zeroSection_unit
    (hK : HasDefinedChernClasses
      ((DerivedCategory.singleFunctor (projectiveCompletion 𝒞).Modules 0).obj
      ((Scheme.Modules.pushforward (zeroSection 𝒞)).obj
        (SheafOfModules.unit (bundle (Stacks.Ample.unitModule X)).ringCatSheaf)))) :
    perfectCh C (projectiveCompletionProj 𝒞 ≫ sX) hK =
      ch C (projectiveCompletionProj 𝒞 ≫ sX) (lambdaNegOne (koszulModule 𝒞) r) := by
  have R := Stacks.ProjectiveCompletion.koszulResolutionZeroSection 𝒞 r
  rw [perfectCh_eq_ch_eulerCharComplex C _ hK
      (ZeroSectionRR.boundedFiniteLocallyFreeComplex_complex r R) R.iso.some.symm,
    ZeroSectionRR.eulerCharComplex_complex r R]

end Koszul

/-! ### B1 twisted by a vector bundle -/

section KoszulTensor

variable {X : Scheme.{u}} (𝒞 : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞]
  (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r]
  (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

namespace ZeroSectionRR

/-- The Koszul complex tensored with `π^*E`. -/
noncomputable def koszulTensorComplex {F : DerivedCategory (projectiveCompletion 𝒞).Modules}
    (R : ExteriorPowerResolution F (koszulModule 𝒞)) :
    CochainComplex (projectiveCompletion 𝒞).Modules ℤ :=
  ((tensorRightMod (projectiveCompletion 𝒞)
    ((Scheme.Modules.pullback (projectiveCompletionProj 𝒞)).obj E)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj R.complex

variable {F : DerivedCategory (projectiveCompletion 𝒞).Modules}
  (R : ExteriorPowerResolution F (koszulModule 𝒞))

theorem isStrictlyGE_koszulTensorComplex :
    (koszulTensorComplex 𝒞 E R).IsStrictlyGE (-(r : ℤ)) := by
  have := isStrictlyGE_complex r R
  unfold koszulTensorComplex
  infer_instance

theorem isStrictlyLE_koszulTensorComplex : (koszulTensorComplex 𝒞 E R).IsStrictlyLE 0 := by
  have := isStrictlyLE_complex R
  unfold koszulTensorComplex
  infer_instance

include r in
theorem boundedFiniteLocallyFreeComplex_koszulTensorComplex :
    Stacks.Perfect.BoundedLocallyFreeComplexes.boundedFiniteLocallyFreeComplex _
      (koszulTensorComplex 𝒞 E R) :=
  ⟨⟨(CochainComplex.plus_iff _ _).2 ⟨_, isStrictlyGE_koszulTensorComplex 𝒞 r E R⟩,
      (CochainComplex.minus_iff _).2 ⟨_, isStrictlyLE_koszulTensorComplex 𝒞 E R⟩⟩, fun i ↦ by
    have := R.isFiniteLocallyFreeOfRank_X r i
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R.complex.X i) :=
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _
        (exteriorPowerRanks r i)
    exact AlgebraicGeometry.isFiniteLocallyFree_tensorObj (R.complex.X i)
      ((Scheme.Modules.pullback (projectiveCompletionProj 𝒞)).obj E)⟩

include r in
/-- The Euler characteristic of the twisted Koszul complex is `λ_{-1}(ℰ) · [π^*E]`. -/
theorem eulerCharComplex_koszulTensorComplex :
    Stacks.Perfect.BoundedLocallyFreeComplexes.eulerCharComplex _ (koszulTensorComplex 𝒞 E R) =
      lambdaNegOne (koszulModule 𝒞) r *
        VectorBundleKZero.classOf _
          ((Scheme.Modules.pullback (projectiveCompletionProj 𝒞)).obj E) := by
  rw [Stacks.Perfect.BoundedLocallyFreeComplexes.eulerCharComplex_eq_sum _ _ _ _
      (isStrictlyGE_koszulTensorComplex 𝒞 r E R) (isStrictlyLE_koszulTensorComplex 𝒞 E R),
    ← eulerCharComplex_complex r R,
    Stacks.Perfect.BoundedLocallyFreeComplexes.eulerCharComplex_eq_sum _ R.complex _ _
      (isStrictlyGE_complex r R) (isStrictlyLE_complex R), Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have := R.isFiniteLocallyFreeOfRank_X r i
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R.complex.X i) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _
      (exteriorPowerRanks r i)
  rw [smul_mul_assoc, VectorBundleKZero.classOf_mul _ _
    (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree _)
    (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree _)]
  rfl

/-- `(s_*𝒪) ⊗ π^*E ≅ s_*(ρ^*E)`: the projection formula for `s`. -/
noncomputable def pushforwardUnitTensorIso :
    (tensorRightMod (projectiveCompletion 𝒞)
        ((Scheme.Modules.pullback (projectiveCompletionProj 𝒞)).obj E)).obj
        ((Scheme.Modules.pushforward (zeroSection 𝒞)).obj
          (SheafOfModules.unit (bundle (Stacks.Ample.unitModule X)).ringCatSheaf)) ≅
      (Scheme.Modules.pushforward (zeroSection 𝒞)).obj
        ((Scheme.Modules.pullback (bundleProj (Stacks.Ample.unitModule X))).obj E) :=
  ((pushforwardTensorIso (zeroSection 𝒞)
      ((Scheme.Modules.pullback (projectiveCompletionProj 𝒞)).obj E)).app _).symm ≪≫
    (Scheme.Modules.pushforward (zeroSection 𝒞)).mapIso
      (unitTensorIso _ ≪≫ pullbackPullbackIso 𝒞 E)

/-- The twisted Koszul complex represents `s_*(ρ^*E)`: tensoring with `π^*E` is exact. -/
noncomputable def koszulTensorIso
    (R : ExteriorPowerResolution ((DerivedCategory.singleFunctor _ 0).obj
      ((Scheme.Modules.pushforward (zeroSection 𝒞)).obj
        (SheafOfModules.unit (bundle (Stacks.Ample.unitModule X)).ringCatSheaf)))
      (koszulModule 𝒞)) :
    DerivedCategory.Q.obj (koszulTensorComplex 𝒞 E R) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((Scheme.Modules.pushforward (zeroSection 𝒞)).obj
        ((Scheme.Modules.pullback (bundleProj (Stacks.Ample.unitModule X))).obj E)) :=
  ((tensorRightMod (projectiveCompletion 𝒞)
      ((Scheme.Modules.pullback (projectiveCompletionProj 𝒞)).obj E)).mapDerivedCategoryFactors.app
        R.complex).symm ≪≫
    (tensorRightMod (projectiveCompletion 𝒞)
      ((Scheme.Modules.pullback (projectiveCompletionProj 𝒞)).obj E)).mapDerivedCategory.mapIso
        R.iso.some ≪≫
    ((tensorRightMod (projectiveCompletion 𝒞)
      ((Scheme.Modules.pullback (projectiveCompletionProj 𝒞)).obj
        E)).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (pushforwardUnitTensorIso 𝒞 E)

end ZeroSectionRR

variable (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **B1 twisted by `E`**: `ch(s_*ρ^*E) = ch(λ_{-1}(ℰ)) · ch(π^*E)`. -/
theorem perfectCh_pushforward_zeroSection {K : DerivedCategory (projectiveCompletion 𝒞).Modules}
    (hK : HasDefinedChernClasses K)
    (e : K ≅ (DerivedCategory.singleFunctor _ 0).obj
      ((Scheme.Modules.pushforward (zeroSection 𝒞)).obj
        ((Scheme.Modules.pullback (bundleProj (Stacks.Ample.unitModule X))).obj E))) :
    perfectCh C (projectiveCompletionProj 𝒞 ≫ sX) hK =
      ch C (projectiveCompletionProj 𝒞 ≫ sX) (lambdaNegOne (koszulModule 𝒞) r) *
        ch C (projectiveCompletionProj 𝒞 ≫ sX) (VectorBundleKZero.classOf _
          ((Scheme.Modules.pullback (projectiveCompletionProj 𝒞)).obj E)) := by
  have R := Stacks.ProjectiveCompletion.koszulResolutionZeroSection 𝒞 r
  rw [perfectCh_eq_ch_eulerCharComplex C _ hK
      (ZeroSectionRR.boundedFiniteLocallyFreeComplex_koszulTensorComplex 𝒞 r E R)
      (e ≪≫ (ZeroSectionRR.koszulTensorIso 𝒞 E R).symm),
    ZeroSectionRR.eulerCharComplex_koszulTensorComplex 𝒞 r E R, map_mul]

end KoszulTensor

/-! ### B5, from B3 -/

section Formula

namespace ZeroSectionRR

/-- Pushforward along equal morphisms. -/
theorem rationalProperChowPushforward_congr_hom {C : ChowSituation.{u}} {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    {f g : A ⟶ B} [IsProper f] [IsProper g] (h : f = g) (hf : f ≫ sB = sA) (hg : g ≫ sB = sA)
    (γ : DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sA j) :
    rationalProperChowPushforward C sA sB hf γ = rationalProperChowPushforward C sA sB hg γ := by
  subst h
  rfl

/-- **`u_*[A] = [B]` for an isomorphism `u : A ⟶ B`.** -/
theorem rationalProperChowPushforward_fundamentalClass_of_isIso (k : Type u) [Field k]
    {A B : Scheme.{u}} (sA : A ⟶ Spec (.of k)) (sB : B ⟶ Spec (.of k)) [IsSmoothFT k sA]
    [IsSmoothFT k sB] (f : A ⟶ B) [IsIso f] (hf : f ≫ sB = sA) :
    rationalProperChowPushforward (fieldChowSituation k) sA sB hf (fundamentalClass k sA) =
      fundamentalClass k sB := by
  have := isNoetherian k sA
  have := isNoetherian k sB
  set C := fieldChowSituation k
  have hpush : ∀ d (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sB f hf d),
      properChowPushforward C sA sB f hf d hfac (fundamentalChowClass C sA d) =
        fundamentalChowClass C sB d :=
    fun d hfac ↦ properChowPushforward_fundamentalChowClass_of_isIso C sA sB f hf d hfac
  set g : ℤ → CHQ k sB := fun d =>
    DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sB j) d
      ((1 : ℚ) ⊗ₜ fundamentalChowClass C sB d) with hg
  rw [fundamentalClass, fundamentalClass, rationalFundamentalClass_eq,
    rationalFundamentalClass_eq, map_sum]
  have hterm : ∀ d ∈ (fundamentalClassDegrees_finite C sA).toFinset,
      rationalProperChowPushforward C sA sB hf
          (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sA j) d
            ((1 : ℚ) ⊗ₜ fundamentalChowClass C sA d)) = g d := by
    intro d _
    rw [rationalProperChowPushforward_of_tmul, hpush]
  have hvanA : ∀ d ∈ (fundamentalClassDegrees_finite C sA).toFinset ∪
      (fundamentalClassDegrees_finite C sB).toFinset,
      d ∉ (fundamentalClassDegrees_finite C sA).toFinset → g d = 0 := by
    intro d _ hd
    rw [Set.Finite.mem_toFinset] at hd
    have h0 : fundamentalChowClass C sA d = 0 := by
      rw [fundamentalChowClass, fundamentalCycle_eq_zero_of_notMem_fundamentalClassDegrees C sA hd,
        map_zero]
    rw [hg]
    dsimp only
    rw [← hpush d (properPushforwardDescends C _ _ _ _ _), h0, map_zero, TensorProduct.tmul_zero,
      map_zero]
  have hvanB : ∀ d ∈ (fundamentalClassDegrees_finite C sA).toFinset ∪
      (fundamentalClassDegrees_finite C sB).toFinset,
      d ∉ (fundamentalClassDegrees_finite C sB).toFinset → g d = 0 := by
    intro d _ hd
    rw [Set.Finite.mem_toFinset] at hd
    rw [hg]
    dsimp only
    rw [fundamentalChowClass, fundamentalCycle_eq_zero_of_notMem_fundamentalClassDegrees C sB hd,
      map_zero, TensorProduct.tmul_zero, map_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_subset Finset.subset_union_left hvanA,
    ← Finset.sum_subset Finset.subset_union_right hvanB]

end ZeroSectionRR

variable (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsSmoothFT k sX]
  (𝒞 : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞]
  (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r]
  (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

namespace ZeroSectionRR

/-- `ch(s_*ρ^*E) = (td(-[ℰ^∨]) · ch(π^*E)) · (ch(λ_{-1}ℰ) · td([ℰ^∨]))`. -/
theorem perfectCh_eq_mul {K : DerivedCategory (projectiveCompletion 𝒞).Modules}
    (hK : HasDefinedChernClasses K)
    (e : K ≅ (DerivedCategory.singleFunctor _ 0).obj
      ((Scheme.Modules.pushforward (zeroSection 𝒞)).obj
        ((Scheme.Modules.pullback (bundleProj (Stacks.Ample.unitModule X))).obj E))) :
    perfectCh (fieldChowSituation k) (projectiveCompletionProj 𝒞 ≫ sX) hK =
      (toddClass (fieldChowSituation k) (projectiveCompletionProj 𝒞 ≫ sX)
          (-VectorBundleKZero.classOf _ (dualSheaf (koszulModule 𝒞))) *
        ch (fieldChowSituation k) (projectiveCompletionProj 𝒞 ≫ sX) (VectorBundleKZero.classOf _
          ((Scheme.Modules.pullback (projectiveCompletionProj 𝒞)).obj E))) *
      (ch (fieldChowSituation k) (projectiveCompletionProj 𝒞 ≫ sX)
          (lambdaNegOne (koszulModule 𝒞) r) *
        toddClass (fieldChowSituation k) (projectiveCompletionProj 𝒞 ≫ sX)
          (VectorBundleKZero.classOf _ (dualSheaf (koszulModule 𝒞)))) := by
  rw [perfectCh_pushforward_zeroSection 𝒞 r E (fieldChowSituation k) sX hK e]
  set x := ch (fieldChowSituation k) (projectiveCompletionProj 𝒞 ≫ sX)
    (lambdaNegOne (koszulModule 𝒞) r)
  set y := ch (fieldChowSituation k) (projectiveCompletionProj 𝒞 ≫ sX) (VectorBundleKZero.classOf _
    ((Scheme.Modules.pullback (projectiveCompletionProj 𝒞)).obj E))
  set t := toddClass (fieldChowSituation k) (projectiveCompletionProj 𝒞 ≫ sX)
    (VectorBundleKZero.classOf _ (dualSheaf (koszulModule 𝒞)))
  set t' := toddClass (fieldChowSituation k) (projectiveCompletionProj 𝒞 ≫ sX)
    (-VectorBundleKZero.classOf _ (dualSheaf (koszulModule 𝒞)))
  have hc1 : Commute y x := (Commute.all _ _).map _
  have hc2 : Commute t' (x * y) :=
    (commute_toddClass_ch _ _ _ _).mul_right (commute_toddClass_ch _ _ _ _)
  have h1 : t' * t = 1 := toddClass_neg_mul_toddClass _ _ _
  calc x * y = x * y * (t' * t) := by rw [h1, mul_one]
    _ = t' * (x * y) * t := by rw [← mul_assoc, ← hc2.eq]
    _ = t' * y * (x * t) := by
        rw [← hc1.eq]
        simp only [mul_assoc]

/-- The projection formula along `ρ`, in `cap` form. -/
theorem rationalProperChowPushforward_cap_pullbackAQ_bundleProj
    (b : AQ k sX) (γ : CHQ k (bundleProj (Stacks.Ample.unitModule X) ≫ sX)) :
    rationalProperChowPushforward (fieldChowSituation k)
        (bundleProj (Stacks.Ample.unitModule X) ≫ sX) sX rfl
        (cap k (bundleProj (Stacks.Ample.unitModule X) ≫ sX)
          (pullbackAQ (fieldChowSituation k) (bundleProj (Stacks.Ample.unitModule X) ≫ sX) sX
            (bundleProj (Stacks.Ample.unitModule X)) rfl b) γ) =
      cap k sX b (rationalProperChowPushforward (fieldChowSituation k)
        (bundleProj (Stacks.Ample.unitModule X) ≫ sX) sX rfl γ) :=
  rationalProperChowPushforward_totalRationalChowCap_pullbackAQ (fieldChowSituation k) _ sX _ rfl
    (bddBelow_relativeDimension_field k _) (bddBelow_relativeDimension_field k sX) b γ

include r in
/-- `π_* s_* = ρ_*`. -/
theorem pushforward_pushforward_zeroSection
    (y : CHQ k (bundleProj (Stacks.Ample.unitModule X) ≫ sX)) :
    haveI := isSmoothFT_projectiveCompletion 𝒞 r k sX
    haveI := ZeroSectionRR.isSmoothFT_bundleProj_unitModule k sX
    rationalProperChowPushforward (fieldChowSituation k) (projectiveCompletionProj 𝒞 ≫ sX) sX rfl
        (rationalProperChowPushforward (fieldChowSituation k)
          (bundleProj (Stacks.Ample.unitModule X) ≫ sX) (projectiveCompletionProj 𝒞 ≫ sX)
          (Stacks.ProjectiveCompletion.zeroSection_comp_projectiveCompletionProj_assoc 𝒞 sX) y) =
      rationalProperChowPushforward (fieldChowSituation k)
        (bundleProj (Stacks.Ample.unitModule X) ≫ sX) sX rfl y := by
  have := isSmoothFT_projectiveCompletion 𝒞 r k sX
  have := ZeroSectionRR.isSmoothFT_bundleProj_unitModule k sX
  rw [← rationalProperChowPushforward_comp k (bundleProj (Stacks.Ample.unitModule X) ≫ sX)
      (projectiveCompletionProj 𝒞 ≫ sX) sX (zeroSection 𝒞) (projectiveCompletionProj 𝒞)
      (Stacks.ProjectiveCompletion.zeroSection_comp_projectiveCompletionProj_assoc 𝒞 sX) rfl
      (by rw [Category.assoc,
        Stacks.ProjectiveCompletion.zeroSection_comp_projectiveCompletionProj_assoc])]
  exact ZeroSectionRR.rationalProperChowPushforward_congr_hom _ _
    (Stacks.ProjectiveCompletion.zeroSection_comp_projectiveCompletionProj 𝒞) _ rfl y

include 𝒞 r in
/-- `ρ_*(ρ^* b ∩ [𝐏(𝒪_X)]) = b ∩ [X]`. -/
theorem pushforward_cap_pullbackAQ_fundamentalClass_bundleProj (b : AQ k sX) :
    haveI := ZeroSectionRR.isSmoothFT_bundleProj_unitModule k sX
    rationalProperChowPushforward (fieldChowSituation k)
        (bundleProj (Stacks.Ample.unitModule X) ≫ sX) sX rfl
        (cap k (bundleProj (Stacks.Ample.unitModule X) ≫ sX)
          (pullbackAQ (fieldChowSituation k) (bundleProj (Stacks.Ample.unitModule X) ≫ sX) sX
            (bundleProj (Stacks.Ample.unitModule X)) rfl b)
          (fundamentalClass k (bundleProj (Stacks.Ample.unitModule X) ≫ sX))) =
      cap k sX b (fundamentalClass k sX) := by
  have := ZeroSectionRR.isSmoothFT_bundleProj_unitModule k sX
  have : IsLocallyNoetherian X := (isNoetherian k sX).toIsLocallyNoetherian
  have := ZeroSectionRR.isIso_bundleProj_unitModule 𝒞 r
  rw [ZeroSectionRR.rationalProperChowPushforward_cap_pullbackAQ_bundleProj,
    ZeroSectionRR.rationalProperChowPushforward_fundamentalClass_of_isIso k _ sX _ rfl]

end ZeroSectionRR

/-- **B5 from B3**: the zero-section formula
`π_*(ch(s_*ρ^*E) ∩ [P̄]) = (ch(E) · td(-[𝒞^∨])) ∩ [X]`, given
`(ch(λ_{-1}ℰ) · td([ℰ^∨])) ∩ [P̄] = s_*[𝐏(𝒪_X)]` (B3). -/
theorem zeroSection_formula_of
    (hB3 : haveI := isSmoothFT_projectiveCompletion 𝒞 r k sX
      haveI := ZeroSectionRR.isSmoothFT_bundleProj_unitModule k sX
      cap k (projectiveCompletionProj 𝒞 ≫ sX)
          (ch (fieldChowSituation k) (projectiveCompletionProj 𝒞 ≫ sX)
              (lambdaNegOne (koszulModule 𝒞) r) *
            toddClass (fieldChowSituation k) (projectiveCompletionProj 𝒞 ≫ sX)
              (VectorBundleKZero.classOf _ (dualSheaf (koszulModule 𝒞))))
          (fundamentalClass k (projectiveCompletionProj 𝒞 ≫ sX)) =
        rationalProperChowPushforward (fieldChowSituation k)
          (bundleProj (Stacks.Ample.unitModule X) ≫ sX) (projectiveCompletionProj 𝒞 ≫ sX)
          (Stacks.ProjectiveCompletion.zeroSection_comp_projectiveCompletionProj_assoc 𝒞 sX)
          (fundamentalClass k (bundleProj (Stacks.Ample.unitModule X) ≫ sX)))
    {K : DerivedCategory (projectiveCompletion 𝒞).Modules} (hK : HasDefinedChernClasses K)
    (e : K ≅ (DerivedCategory.singleFunctor _ 0).obj
      ((Scheme.Modules.pushforward (zeroSection 𝒞)).obj
        ((Scheme.Modules.pullback (bundleProj (Stacks.Ample.unitModule X))).obj E))) :
    haveI := isSmoothFT_projectiveCompletion 𝒞 r k sX
    rationalProperChowPushforward (fieldChowSituation k) (projectiveCompletionProj 𝒞 ≫ sX) sX rfl
        (cap k (projectiveCompletionProj 𝒞 ≫ sX) (perfectCh (fieldChowSituation k) _ hK)
          (fundamentalClass k (projectiveCompletionProj 𝒞 ≫ sX))) =
      cap k sX (ch (fieldChowSituation k) sX (VectorBundleKZero.classOf X E) *
          toddClass (fieldChowSituation k) sX (-VectorBundleKZero.classOf X (dualSheaf 𝒞)))
        (fundamentalClass k sX) := by
  have := isSmoothFT_projectiveCompletion 𝒞 r k sX
  have := ZeroSectionRR.isSmoothFT_bundleProj_unitModule k sX
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (koszulModule 𝒞) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ r
  rw [ZeroSectionRR.perfectCh_eq_mul k sX 𝒞 r E hK e, cap_mul, Module.End.mul_apply, hB3,
    ← rationalProperChowPushforward_cap_pullbackAQ k (bundleProj (Stacks.Ample.unitModule X) ≫ sX)
      (projectiveCompletionProj 𝒞 ≫ sX) (zeroSection 𝒞)
      (Stacks.ProjectiveCompletion.zeroSection_comp_projectiveCompletionProj_assoc 𝒞 sX)]
  have hG : VectorBundleKZero.pullback (zeroSection 𝒞) (VectorBundleKZero.classOf _
        ((Scheme.Modules.pullback (projectiveCompletionProj 𝒞)).obj E)) =
      VectorBundleKZero.pullback (bundleProj (Stacks.Ample.unitModule X))
        (VectorBundleKZero.classOf X E) := by
    rw [VectorBundleKZero.pullback_classOf, VectorBundleKZero.pullback_classOf]
    exact VectorBundleKZero.classOf_eq_of_iso (ZeroSectionRR.pullbackPullbackIso 𝒞 E)
      (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree _)
  rw [map_mul, pullbackAQ_toddClass, pullbackAQ_ch, map_neg,
    pullback_zeroSection_classOf_dual_koszulModule 𝒞 r, hG, ← map_neg,
    ← pullbackAQ_toddClass (fieldChowSituation k) (bundleProj (Stacks.Ample.unitModule X) ≫ sX) sX
      (bundleProj (Stacks.Ample.unitModule X)) rfl,
    ← pullbackAQ_ch (fieldChowSituation k) (bundleProj (Stacks.Ample.unitModule X) ≫ sX) sX
      (bundleProj (Stacks.Ample.unitModule X)) rfl, ← map_mul,
    ZeroSectionRR.pushforward_pushforward_zeroSection k sX 𝒞 r,
    ZeroSectionRR.pushforward_cap_pullbackAQ_fundamentalClass_bundleProj k sX 𝒞 r,
    (commute_toddClass_ch (fieldChowSituation k) sX _ _).eq]

end Formula

namespace ZeroSectionRR

/-! ### Degree casts -/

theorem chowGroupCast_chowGroupCast (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] {a b c : ℤ} (h₁ : a = b) (h₂ : b = c) (x : chowGroup C sY a) :
    chowGroupCast C sY h₂ (chowGroupCast C sY h₁ x) = chowGroupCast C sY (h₁.trans h₂) x := by
  subst h₁ h₂
  rfl

theorem properChowPushforward_chowGroupCast (C : ChowSituation.{u}) {Y Z : Scheme.{u}}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
    (f : Y ⟶ Z) [IsProper f] (hf : f ≫ sZ = sY) {a b : ℤ} (h : a = b)
    (ha : ProperPushforwardFactorsThroughRationalEquivalence C sY sZ f hf a)
    (hb : ProperPushforwardFactorsThroughRationalEquivalence C sY sZ f hf b)
    (x : chowGroup C sY a) :
    properChowPushforward C sY sZ f hf b hb (chowGroupCast C sY h x) =
      chowGroupCast C sZ h (properChowPushforward C sY sZ f hf a ha x) := by
  subst h
  rfl

theorem properChowPushforward_congr_hom (C : ChowSituation.{u}) {Y Z : Scheme.{u}}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
    {f g : Y ⟶ Z} [IsProper f] [IsProper g] (e : f = g) (hf : f ≫ sZ = sY) (hg : g ≫ sZ = sY)
    (a : ℤ) (ha : ProperPushforwardFactorsThroughRationalEquivalence C sY sZ f hf a)
    (hb : ProperPushforwardFactorsThroughRationalEquivalence C sY sZ g hg a)
    (x : chowGroup C sY a) :
    properChowPushforward C sY sZ f hf a ha x = properChowPushforward C sY sZ g hg a hb x := by
  subst e
  rfl

/-! ### Uniqueness in the projective space bundle formula -/

section Uniqueness

-- `LocallyOfFiniteType π` is the instance argument `bundlePullback` is stated with.
set_option linter.overlappingInstances false

variable (C : ChowSituation.{u}) {P U : Scheme.{u}} (sU : U ⟶ C.S) [LocallyOfFiniteType sU]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ U) [LocallyOfFiniteType π] [Flat π]
  [IsProper π] (hsP : π ≫ sU = sP) (n : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π n)
  (ξ : ChernCapOperator C sP)

/-- A class `y = ∑_i ξ^i ∩ π^*β_i` with `π_*(ξ^{n-i} ∩ y) = 0` for all `i ≤ n` is zero (the
downward induction of Stacks 02TX). -/
theorem eq_zero_of_pushforward_capPow_bundleMap
    (htop : ∀ (k : ℤ) (α : chowGroup C sU k),
      bundleProjection C sU sP π hsP n hπ ξ n k k (by ring) α = α) (k : ℤ)
    (β : ∀ i : Fin (n + 1), chowGroup C sU (k + (i : ℕ)))
    (hkey : ∀ (i : ℕ) (hi : i ≤ n),
      properChowPushforward C sP sU π hsP (k + i)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sU π hsP _)
          (capPow C sP ξ (n - i) (k + n) (k + i) (by push_cast [hi]; ring)
            (bundleMap C sU sP π hsP n hπ ξ k β)) = 0) :
    β = 0 := by
  have hterm : ∀ (i : Fin (n + 1)) (m : ℕ) (hm : m ≤ n),
      properChowPushforward C sP sU π hsP (k + m)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sU π hsP _)
          (capPow C sP ξ (n - m) (k + n) (k + m) (by push_cast [hm]; ring)
            (bundleTerm C sU sP π hsP n hπ ξ k i (β i))) =
        bundleProjection C sU sP π hsP n hπ ξ ((i : ℕ) + (n - m)) (k + (i : ℕ)) (k + m)
          (by push_cast [hm]; ring) (β i) := by
    intro i m hm
    simp only [bundleTerm, bundleProjection, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [capPow_capPow]
  have hexp : ∀ {s s' : ℕ} (e : s = s') (a b : ℤ) (h : a + n = b + s) (x : chowGroup C sU a),
      bundleProjection C sU sP π hsP n hπ ξ s a b h x =
        bundleProjection C sU sP π hsP n hπ ξ s' a b (e ▸ h) x := by
    intro s s' e a b h x; subst e; rfl
  have step : ∀ i : Fin (n + 1), (∀ i' : Fin (n + 1), (i : ℕ) < i' → β i' = 0) → β i = 0 := by
    intro i hi
    have hle : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
    have h0 := hkey i hle
    rw [bundleMap_apply, map_sum, map_sum] at h0
    rw [Finset.sum_congr rfl fun j _ ↦ hterm j i hle] at h0
    rw [Finset.sum_eq_single i (fun j _ hj ↦ ?_) (by simp)] at h0
    · rw [hexp (show (i : ℕ) + (n - i) = n by omega)] at h0
      rw [← htop (k + (i : ℕ)) (β i)]
      exact h0
    · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hj) with hlt | hgt
      · exact bundleProjection_eq_zero_of_lt C sU sP π hsP n hπ ξ _ (by omega) _ _ _ _
      · rw [hi j hgt, map_zero]
  have all : ∀ d : ℕ, ∀ i : Fin (n + 1), n - d ≤ (i : ℕ) → β i = 0 := by
    intro d
    induction d with
    | zero =>
      intro i hi
      exact step i fun i' hi' ↦ absurd i'.isLt (by omega)
    | succ d ih =>
      intro i hi
      by_cases h : n - d ≤ (i : ℕ)
      · exact ih i h
      · exact step i fun i' hi' ↦ ih i' (by omega)
  funext i
  exact all n i (by omega)

/-- **Uniqueness for classes killed by `ξ`**: on a projective bundle (02TW, 02TX), a class `y`
with `ξ ∩ y = 0` and `π_* y = 0` is zero. -/
theorem eq_zero_of_capOnChow_eq_zero_of_pushforward_eq_zero
    (htop : ∀ (k : ℤ) (α : chowGroup C sU k),
      bundleProjection C sU sP π hsP n hπ ξ n k k (by ring) α = α)
    (hsurj : ∀ k : ℤ, Function.Surjective (bundleMap C sU sP π hsP n hπ ξ k))
    (a : ℤ) (y : chowGroup C sP a)
    (hξ : ∀ (d : ℤ) (hd : a = d + 1), ξ.capOnChow C sP d (chowGroupCast C sP hd y) = 0)
    (hpush : properChowPushforward C sP sU π hsP a
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sU π hsP a) y = 0) :
    y = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, a = k + n := ⟨a - n, by ring⟩
  obtain ⟨β, rfl⟩ := hsurj k y
  suffices hβ : β = 0 by rw [hβ, map_zero]
  refine eq_zero_of_pushforward_capPow_bundleMap C sU sP π hsP n hπ ξ htop k β fun i hi ↦ ?_
  rcases Nat.eq_or_lt_of_le hi with rfl | hlt
  · rw [capPow_congr C sP ξ (Nat.sub_self i), capPow_zero_apply,
      properChowPushforward_chowGroupCast C sP sU π hsP _
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sU π hsP _), hpush,
      map_zero]
  · obtain ⟨j, hj⟩ : ∃ j, n - i = j + 1 := ⟨n - i - 1, by omega⟩
    rw [capPow_congr C sP ξ hj, capPow_succ_apply, hξ (k + n - 1) (by ring), map_zero, map_zero]

end Uniqueness

/-! ### The top Chern class of `ℰ` capped with `[P̄]` -/

section TopClass

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (𝒞 : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞]
  (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r]

/-- `ξ ∩ s_* z = 0`: `𝒪(1)` is trivial along the zero section. -/
theorem capOnChow_pushforward_zeroSection (d : ℤ)
    (z : chowGroup C (bundleProj (Stacks.Ample.unitModule X) ≫ sX) (d + 1)) :
    (completionTwistCap C sX 𝒞).capOnChow C _ d
      (properChowPushforward C (bundleProj (Stacks.Ample.unitModule X) ≫ sX)
        (projectiveCompletionProj 𝒞 ≫ sX) (zeroSection 𝒞)
        (Stacks.ProjectiveCompletion.zeroSection_comp_projectiveCompletionProj_assoc 𝒞 sX) (d + 1)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ _ _) z) = 0 := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible _ _
      ((Scheme.Modules.pullback (zeroSection 𝒞)).obj (bundleTwist (completionModule 𝒞))) :=
    isInvertible_presheaf_modulePullback _ _
  rw [← properChowPushforward_invCap C _ _ (zeroSection 𝒞) _ (bundleTwist (completionModule 𝒞)) d z,
    GRR.invCap_capOnChow_eq_zero_of_iso C _ _ (pullbackTwistIso 𝒞) d z, map_zero]

include r in
/-- `π_* s_* [𝐏(𝒪_X)]_m = [X]_m`. -/
theorem pushforward_pushforward_fundamentalChowClass [IsLocallyNoetherian X] (m : ℤ)
    (h₁ : ProperPushforwardFactorsThroughRationalEquivalence C (projectiveCompletionProj 𝒞 ≫ sX) sX
      (projectiveCompletionProj 𝒞) rfl m)
    (h₂ : ProperPushforwardFactorsThroughRationalEquivalence C
      (bundleProj (Stacks.Ample.unitModule X) ≫ sX) (projectiveCompletionProj 𝒞 ≫ sX)
      (zeroSection 𝒞)
      (Stacks.ProjectiveCompletion.zeroSection_comp_projectiveCompletionProj_assoc 𝒞 sX) m) :
    properChowPushforward C (projectiveCompletionProj 𝒞 ≫ sX) sX (projectiveCompletionProj 𝒞) rfl m
        h₁ (properChowPushforward C (bundleProj (Stacks.Ample.unitModule X) ≫ sX)
          (projectiveCompletionProj 𝒞 ≫ sX) (zeroSection 𝒞)
          (Stacks.ProjectiveCompletion.zeroSection_comp_projectiveCompletionProj_assoc 𝒞 sX) m h₂
          (fundamentalChowClass C (bundleProj (Stacks.Ample.unitModule X) ≫ sX) m)) =
      fundamentalChowClass C sX m := by
  have := isIso_bundleProj_unitModule 𝒞 r
  have h := DFunLike.congr_fun (properChowPushforward_comp C
    (bundleProj (Stacks.Ample.unitModule X) ≫ sX) (projectiveCompletionProj 𝒞 ≫ sX) sX
    (zeroSection 𝒞) (projectiveCompletionProj 𝒞)
    (Stacks.ProjectiveCompletion.zeroSection_comp_projectiveCompletionProj_assoc 𝒞 sX) rfl m h₂ h₁)
    (fundamentalChowClass C (bundleProj (Stacks.Ample.unitModule X) ≫ sX) m)
  rw [AddMonoidHom.comp_apply] at h
  rw [h, properChowPushforward_congr_hom C _ sX
      (Stacks.ProjectiveCompletion.zeroSection_comp_projectiveCompletionProj 𝒞) _ rfl m _
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ _ _),
    properChowPushforward_fundamentalChowClass_of_isIso]

include r in
/-- **The top Chern class of `ℰ` on `[P̄]`, degreewise**: `c_r(ℰ) ∩ π^*[X]_m = (-1)^r s_*[X']_m`. -/
theorem chernCap_koszulModule_completionPullback_fundamentalChowClass [IsLocallyNoetherian X]
    [Flat (projectiveCompletionProj 𝒞)] [LocallyOfFiniteType (projectiveCompletionProj 𝒞)]
    (m : ℤ) :
    GenuineChern.chernCap C r (projectiveCompletionProj 𝒞 ≫ sX) (koszulModule 𝒞) (m + r)
        (Fin.last r) (completionPullback C sX 𝒞 r m (fundamentalChowClass C sX m)) =
      ((-1 : ℤ) ^ r) • chowGroupCast C (projectiveCompletionProj 𝒞 ≫ sX)
        (show m = m + r - r by ring)
        (properChowPushforward C (bundleProj (Stacks.Ample.unitModule X) ≫ sX)
          (projectiveCompletionProj 𝒞 ≫ sX) (zeroSection 𝒞)
          (Stacks.ProjectiveCompletion.zeroSection_comp_projectiveCompletionProj_assoc 𝒞 sX) m
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ _ _)
          (fundamentalChowClass C (bundleProj (Stacks.Ample.unitModule X) ≫ sX) m)) := by
  rw [← sub_eq_zero]
  refine eq_zero_of_capOnChow_eq_zero_of_pushforward_eq_zero C sX
    (projectiveCompletionProj 𝒞 ≫ sX) (projectiveCompletionProj 𝒞) rfl r
    (relativeDimension_projectiveCompletionProj' 𝒞 r) (completionTwistCap C sX 𝒞)
    (fun k α ↦ projectiveBundle_projection_self (completionModule 𝒞) r C sX k α)
    (fun k ↦ (projectiveBundle_formula (completionModule 𝒞) r C sX k).2) (m + r - r) _ ?_ ?_
  · intro d hd
    rw [map_sub, map_sub, capOnChow_chernCap_koszulModule_bundlePullback C sX 𝒞 r m d hd,
      map_zsmul, map_zsmul, chowGroupCast_chowGroupCast,
      ← properChowPushforward_chowGroupCast C _ _ (zeroSection 𝒞) _ _ _
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ _ _),
      capOnChow_pushforward_zeroSection, smul_zero, sub_zero]
  · rw [map_sub, pushforward_chernCap_tensorDual_bundlePullback C sX _ _ rfl r
        (relativeDimension_projectiveCompletionProj' 𝒞 r) _ 𝒞 _
        (isLocallyProjectiveTower_bundle (completionModule 𝒞) r) (Iso.refl _) m,
      map_zsmul, properChowPushforward_chowGroupCast C _ _ _ _ _
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ _ _),
      pushforward_pushforward_fundamentalChowClass C sX 𝒞 r m, sub_self]

end TopClass

/-! ### Rational classes -/

section Rational

/-- Changing the structure morphism of a Chern class cap along an equality. -/
theorem chernCap_heq_of_eq (C : ChowSituation.{u}) (r : ℕ) {T : Scheme.{u}} {q q' : T ⟶ C.S}
    [LocallyOfFiniteType q] [LocallyOfFiniteType q'] (h : q = q') (F : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (a : ℤ)
    (j : Fin (r + 1)) {x : chowGroup C q a} {x' : chowGroup C q' a} (hx : x ≍ x') :
    GenuineChern.chernCap C r q F a j x ≍ GenuineChern.chernCap C r q' F a j x' := by
  subst h
  cases hx
  rfl

/-- **Capping with `c_r(F) ∈ A^r(T)` is the top Chern class operation `c_r(F) ∩ -`.** -/
theorem chowCohomologyCap_totalChern_heq (C : ChowSituation.{u}) {T : Scheme.{u}}
    (sT : T ⟶ C.S) [LocallyOfFiniteType sT] (F : T.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (a : ℤ)
    (x : chowGroup C sT a) :
    chowCohomologyCap C (gysinSystemOfInvertible C) sT (r : ℤ) (totalChern C sT F r r) a x ≍
      GenuineChern.chernCap C r sT F a (Fin.last r) x := by
  have := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r (𝟙 T)
  refine (chowCohomologyCap_heq_idRule_ofGysinSystem C _ sT _ _ a x).trans ?_
  rw [← TotalChowClass.op_apply]
  refine (heq_of_eq (op_totalChern_apply C sT F r (𝟙 T) a (Fin.last r) _)).trans ?_
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((𝟭 T.Modules).obj F) r :=
    inferInstanceAs (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r)
  rw [GenuineChern.chernCap_congr C _ r ((Scheme.Modules.pullbackId T).app F)]
  exact chernCap_heq_of_eq C r (Category.id_comp sT) F a (Fin.last r)
    (chowGroupCongr_heq C _ a x)

/-- `c_r(F) ∩ -` on a generator, through the total cap action. -/
theorem cap_topChern_of_tmul (k : Type u) [Field k] {T : Scheme.{u}} (sT : T ⟶ Spec (.of k))
    [LocallyOfFiniteType sT] (F : T.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (a : ℤ) (q : ℚ)
    (x : chowGroup (fieldChowSituation k) sT a) :
    cap k sT (RationalTotalChowClass.ofTotalChowClass
        (TotalChowClass.homComponent r (totalChern (fieldChowSituation k) sT F r)))
        (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sT j) a (q ⊗ₜ x)) =
      DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sT j) (a - r)
        (q ⊗ₜ GenuineChern.chernCap (fieldChowSituation k) r sT F a (Fin.last r) x) := by
  rw [← DirectSum.lof_eq_of ℚ]
  unfold cap
  rw [totalRationalChowCap_lof_eq_sum_range (fieldChowSituation k) _ sT 0
      (relativeDimension_fieldChowSituation_nonneg k sT) _ a _ (a.toNat + r) (by omega),
    Finset.sum_eq_single r]
  · rw [DirectSum.lof_eq_of, RationalTotalChowClass.ofFamily_symm_apply,
      RationalTotalChowClass.ofTotalChowClass_apply, rationalChowCap_of_tmul, one_mul]
    refine of_tmul_eq_of_tmul_of_heq (fieldChowSituation k) sT rfl q ?_
    rw [TotalChowClass.homComponent_apply, ite_eq_left rfl]
    exact chowCohomologyCap_totalChern_heq (fieldChowSituation k) sT F r a x
  · intro p _ hp
    rw [RationalTotalChowClass.ofFamily_symm_apply, RationalTotalChowClass.ofTotalChowClass_apply,
      TotalChowClass.homComponent_apply, ite_eq_right hp, TensorProduct.tmul_zero, map_zero,
      LinearMap.zero_apply]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- `cap` is additive in the class. -/
theorem cap_zsmul_apply (k : Type u) [Field k] {T : Scheme.{u}} (sT : T ⟶ Spec (.of k))
    [LocallyOfFiniteType sT] (n : ℤ) (c : AQ k sT) (x : CHQ k sT) :
    cap k sT (n • c) x = n • cap k sT c x := by
  unfold cap
  rw [map_zsmul, map_zsmul]
  rfl

-- `LocallyOfFiniteType p` is the instance argument `bundlePullback` is stated with.
set_option linter.overlappingInstances false in
/-- **`p^*[Y] = [P]`** for the rational fundamental classes of a flat `p : P ⟶ Y` of relative
dimension `n` between smooth schemes. -/
theorem rationalChowMap_bundlePullback_fundamentalClass' (k : Type u) [Field k]
    {Y P : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsSmoothFT k sY] (sP : P ⟶ Spec (.of k))
    [IsSmoothFT k sP] (p : P ⟶ Y) [LocallyOfFiniteType p] [Flat p] (hsP : p ≫ sY = sP) (n : ℕ)
    (hπ : AlgebraicGeometry.RelativeDimension p n) :
    rationalChowMap (fieldChowSituation k) sP sY (fun e => e + n)
        (fun e => bundlePullback (fieldChowSituation k) sY sP p hsP n hπ e)
        (fundamentalClass k sY) =
      fundamentalClass k sP := by
  set C := fieldChowSituation k
  have := isNoetherian k sY
  have := isNoetherian k sP
  have hfund : ∀ e : ℤ, bundlePullback C sY sP p hsP n hπ e (fundamentalChowClass C sY e) =
      fundamentalChowClass C sP (e + n) :=
    fun e => flatPullbackChow_fundamentalChowClass_smooth sY sP p hsP n hπ e
  set g : ℤ → CHQ k sP := fun d =>
    DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sP j) d
      ((1 : ℚ) ⊗ₜ fundamentalChowClass C sP d) with hg
  have hvanP : ∀ d ∈ (fundamentalClassDegrees_finite C sP).toFinset ∪
      (fundamentalClassDegrees_finite C sY).toFinset.image (· + (n : ℤ)),
      d ∉ (fundamentalClassDegrees_finite C sP).toFinset → g d = 0 := by
    intro d _ hd
    rw [Set.Finite.mem_toFinset] at hd
    rw [hg]
    dsimp only
    rw [fundamentalChowClass, fundamentalCycle_eq_zero_of_notMem_fundamentalClassDegrees C sP hd,
      map_zero, TensorProduct.tmul_zero, map_zero]
  have hcast : ∀ a b : ℤ, a = b → fundamentalChowClass C sP a = 0 →
      fundamentalChowClass C sP b = 0 := by
    rintro a b rfl h
    exact h
  have hvanY : ∀ d ∈ (fundamentalClassDegrees_finite C sP).toFinset ∪
      (fundamentalClassDegrees_finite C sY).toFinset.image (· + (n : ℤ)),
      d ∉ (fundamentalClassDegrees_finite C sY).toFinset.image (· + (n : ℤ)) → g d = 0 := by
    intro d _ hd
    have he : d - n ∉ fundamentalClassDegrees C sY := fun h =>
      hd (Finset.mem_image.mpr ⟨d - n, (Set.Finite.mem_toFinset _).mpr h, by ring⟩)
    have h0 : fundamentalChowClass C sY (d - n) = 0 := by
      rw [fundamentalChowClass, fundamentalCycle_eq_zero_of_notMem_fundamentalClassDegrees C sY he,
        map_zero]
    have h1 : fundamentalChowClass C sP (d - n + n) = 0 := by
      rw [← hfund, h0, map_zero]
    rw [hg]
    dsimp only
    rw [hcast _ _ (by ring) h1, TensorProduct.tmul_zero, map_zero]
  rw [fundamentalClass, fundamentalClass, rationalFundamentalClass_eq,
    rationalFundamentalClass_eq, map_sum]
  have hterm : ∀ e ∈ (fundamentalClassDegrees_finite C sY).toFinset,
      rationalChowMap C sP sY (fun e => e + n)
          (fun e => bundlePullback C sY sP p hsP n hπ e)
          (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sY j) e
            ((1 : ℚ) ⊗ₜ fundamentalChowClass C sY e)) = g (e + n) := by
    intro e _
    rw [rationalChowMap_of_tmul, hfund]
  rw [Finset.sum_congr rfl hterm,
    ← Finset.sum_image (f := g) (fun a _ b _ h => by simpa using h),
    Finset.sum_subset Finset.subset_union_right hvanY,
    ← Finset.sum_subset Finset.subset_union_left hvanP]

end Rational

end ZeroSectionRR

/-! ### B3 -/

section B3

variable {X : Scheme.{u}} (𝒞 : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞]
  (r : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r]
  (k : Type u) [Field k] (sX : X ⟶ Spec (.of k)) [IsSmoothFT k sX]

/-- **B3, top Chern class form**: `c_r(ℰ) ∩ [P̄] = (-1)^r s_*[𝐏(𝒪_X)]` for the Koszul module
`ℰ = π^*𝒞 ⊗ 𝒪(-1)`. -/
theorem ZeroSectionRR.cap_topChern_koszulModule_fundamentalClass :
    haveI := isSmoothFT_projectiveCompletion 𝒞 r k sX
    haveI := ZeroSectionRR.isSmoothFT_bundleProj_unitModule k sX
    cap k (projectiveCompletionProj 𝒞 ≫ sX)
        (RationalTotalChowClass.ofTotalChowClass (TotalChowClass.homComponent r
          (totalChern (fieldChowSituation k) (projectiveCompletionProj 𝒞 ≫ sX) (koszulModule 𝒞) r)))
        (fundamentalClass k (projectiveCompletionProj 𝒞 ≫ sX)) =
      ((-1 : ℤ) ^ r) • rationalProperChowPushforward (fieldChowSituation k)
        (bundleProj (Stacks.Ample.unitModule X) ≫ sX) (projectiveCompletionProj 𝒞 ≫ sX)
        (Stacks.ProjectiveCompletion.zeroSection_comp_projectiveCompletionProj_assoc 𝒞 sX)
        (fundamentalClass k (bundleProj (Stacks.Ample.unitModule X) ≫ sX)) := by
  have := isSmoothFT_projectiveCompletion 𝒞 r k sX
  have := ZeroSectionRR.isSmoothFT_bundleProj_unitModule k sX
  have : IsLocallyNoetherian X := (isNoetherian k sX).toIsLocallyNoetherian
  have := Stacks.ProjectiveCompletion.flat_projectiveCompletionProj 𝒞 r
  have := Stacks.ProjectiveCompletion.locallyOfFiniteType_projectiveCompletionProj 𝒞 r
  have := isNoetherian k sX
  have := isNoetherian k (bundleProj (Stacks.Ample.unitModule X) ≫ sX)
  set g : ℤ → CHQ k (projectiveCompletionProj 𝒞 ≫ sX) := fun m =>
    DirectSum.of (fun j : ℤ =>
        ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) (projectiveCompletionProj 𝒞 ≫ sX) j) m
      ((1 : ℚ) ⊗ₜ properChowPushforward (fieldChowSituation k)
        (bundleProj (Stacks.Ample.unitModule X) ≫ sX) (projectiveCompletionProj 𝒞 ≫ sX)
        (zeroSection 𝒞)
        (Stacks.ProjectiveCompletion.zeroSection_comp_projectiveCompletionProj_assoc 𝒞 sX) m
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _)
        (fundamentalChowClass (fieldChowSituation k)
          (bundleProj (Stacks.Ample.unitModule X) ≫ sX) m)) with hg
  -- the terms of `c_r(ℰ) ∩ π^*[X]`
  have hterm : ∀ m : ℤ,
      cap k (projectiveCompletionProj 𝒞 ≫ sX)
        (RationalTotalChowClass.ofTotalChowClass (TotalChowClass.homComponent r
          (totalChern (fieldChowSituation k) (projectiveCompletionProj 𝒞 ≫ sX) (koszulModule 𝒞) r)))
        (rationalChowMap (fieldChowSituation k) (projectiveCompletionProj 𝒞 ≫ sX) sX
          (fun e => e + r)
          (fun e => bundlePullback (fieldChowSituation k) sX (projectiveCompletionProj 𝒞 ≫ sX)
            (projectiveCompletionProj 𝒞) rfl r (relativeDimension_projectiveCompletionProj' 𝒞 r) e)
          (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sX j) m
            ((1 : ℚ) ⊗ₜ fundamentalChowClass (fieldChowSituation k) sX m))) =
        ((-1 : ℤ) ^ r) • g m := by
    intro m
    rw [rationalChowMap_of_tmul, ZeroSectionRR.cap_topChern_of_tmul,
      ZeroSectionRR.chernCap_koszulModule_completionPullback_fundamentalChowClass
        (fieldChowSituation k) sX 𝒞 r m, TensorProduct.tmul_smul, map_zsmul, hg]
    congr 1
    exact of_tmul_eq_of_tmul_of_heq _ _ (by ring) 1 (chowGroupCast_heq _ _ _ _)
  have hinv : ∀ {A : Type u} [AddCommGroup A] (y : A),
      ((-1 : ℤ) ^ r) • ((-1 : ℤ) ^ r) • y = y := by
    intro A _ y
    rw [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
  -- outside the degrees of `[X]`, the terms vanish
  have hzeroD : ∀ m ∈ (fundamentalClassDegrees_finite (fieldChowSituation k) sX).toFinset ∪
      (fundamentalClassDegrees_finite (fieldChowSituation k)
        (bundleProj (Stacks.Ample.unitModule X) ≫ sX)).toFinset,
      m ∉ (fundamentalClassDegrees_finite (fieldChowSituation k) sX).toFinset →
        ((-1 : ℤ) ^ r) • g m = 0 := by
    intro m _ hm
    rw [Set.Finite.mem_toFinset] at hm
    have h0 : fundamentalChowClass (fieldChowSituation k) sX m = 0 := by
      rw [fundamentalChowClass, fundamentalCycle_eq_zero_of_notMem_fundamentalClassDegrees
        (fieldChowSituation k) sX hm, map_zero]
    have h := ZeroSectionRR.chernCap_koszulModule_completionPullback_fundamentalChowClass
      (fieldChowSituation k) sX 𝒞 r m
    rw [h0, map_zero, map_zero] at h
    have h' := congrArg (fun y ↦ ((-1 : ℤ) ^ r) • y) h
    simp only [smul_zero] at h'
    rw [hinv, eq_comm, AddEquiv.map_eq_zero_iff] at h'
    rw [hg]
    dsimp only
    rw [h', TensorProduct.tmul_zero, map_zero, smul_zero]
  -- outside the degrees of `[𝐏(𝒪_X)]`, the terms vanish
  have hzeroD' : ∀ m ∈ (fundamentalClassDegrees_finite (fieldChowSituation k) sX).toFinset ∪
      (fundamentalClassDegrees_finite (fieldChowSituation k)
        (bundleProj (Stacks.Ample.unitModule X) ≫ sX)).toFinset,
      m ∉ (fundamentalClassDegrees_finite (fieldChowSituation k)
        (bundleProj (Stacks.Ample.unitModule X) ≫ sX)).toFinset →
        ((-1 : ℤ) ^ r) • g m = 0 := by
    intro m _ hm
    rw [Set.Finite.mem_toFinset] at hm
    rw [hg]
    dsimp only
    rw [fundamentalChowClass, fundamentalCycle_eq_zero_of_notMem_fundamentalClassDegrees
      (fieldChowSituation k) (bundleProj (Stacks.Ample.unitModule X) ≫ sX) hm,
      map_zero, map_zero, TensorProduct.tmul_zero, map_zero, smul_zero]
  rw [← ZeroSectionRR.rationalChowMap_bundlePullback_fundamentalClass' k sX
      (projectiveCompletionProj 𝒞 ≫ sX) (projectiveCompletionProj 𝒞) rfl r
      (relativeDimension_projectiveCompletionProj' 𝒞 r)]
  unfold fundamentalClass
  rw [rationalFundamentalClass_eq, rationalFundamentalClass_eq, map_sum, map_sum, map_sum,
    Finset.smul_sum, Finset.sum_congr rfl fun m _ ↦ hterm m]
  have hterm' : ∀ m ∈ (fundamentalClassDegrees_finite (fieldChowSituation k)
      (bundleProj (Stacks.Ample.unitModule X) ≫ sX)).toFinset,
      ((-1 : ℤ) ^ r) • rationalProperChowPushforward (fieldChowSituation k)
        (bundleProj (Stacks.Ample.unitModule X) ≫ sX) (projectiveCompletionProj 𝒞 ≫ sX)
        (Stacks.ProjectiveCompletion.zeroSection_comp_projectiveCompletionProj_assoc 𝒞 sX)
        (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k)
          (bundleProj (Stacks.Ample.unitModule X) ≫ sX) j) m
          ((1 : ℚ) ⊗ₜ fundamentalChowClass (fieldChowSituation k)
            (bundleProj (Stacks.Ample.unitModule X) ≫ sX) m)) = ((-1 : ℤ) ^ r) • g m := by
    intro m _
    rw [rationalProperChowPushforward_of_tmul]
  rw [Finset.sum_congr rfl hterm', Finset.sum_subset Finset.subset_union_left hzeroD,
    ← Finset.sum_subset Finset.subset_union_right hzeroD']

/-- **B3**: `(ch(λ_{-1}ℰ) · td([ℰ^∨])) ∩ [P̄] = s_*[𝐏(𝒪_X)]` in `CH_*(P̄) ⊗ ℚ`, the class
`ch(λ_{-1}ℰ) · td([ℰ^∨])` being `(-1)^r c_r(ℰ)` (`GRR.ch_lambdaNegOne_mul_toddClass`). -/
theorem cap_topClass_fundamentalClass :
    haveI := isSmoothFT_projectiveCompletion 𝒞 r k sX
    haveI := ZeroSectionRR.isSmoothFT_bundleProj_unitModule k sX
    cap k (projectiveCompletionProj 𝒞 ≫ sX)
        (ch (fieldChowSituation k) (projectiveCompletionProj 𝒞 ≫ sX)
            (lambdaNegOne (koszulModule 𝒞) r) *
          toddClass (fieldChowSituation k) (projectiveCompletionProj 𝒞 ≫ sX)
            (VectorBundleKZero.classOf _ (dualSheaf (koszulModule 𝒞))))
        (fundamentalClass k (projectiveCompletionProj 𝒞 ≫ sX)) =
      rationalProperChowPushforward (fieldChowSituation k)
        (bundleProj (Stacks.Ample.unitModule X) ≫ sX) (projectiveCompletionProj 𝒞 ≫ sX)
        (Stacks.ProjectiveCompletion.zeroSection_comp_projectiveCompletionProj_assoc 𝒞 sX)
        (fundamentalClass k (bundleProj (Stacks.Ample.unitModule X) ≫ sX)) := by
  have := isSmoothFT_projectiveCompletion 𝒞 r k sX
  have := ZeroSectionRR.isSmoothFT_bundleProj_unitModule k sX
  rw [ch_lambdaNegOne_mul_toddClass (fieldChowSituation k) _ (koszulModule 𝒞) r,
    ZeroSectionRR.cap_zsmul_apply,
    ZeroSectionRR.cap_topChern_koszulModule_fundamentalClass 𝒞 r k sX,
    smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

/-- **Riemann–Roch for the zero section of `P̄ = 𝐏(𝒞 ⊕ 𝒪_X)`** (item B5 of `notes/E_plan.md`).
Let `X` be smooth, separated and of finite type over a field `k`, `𝒞` finite locally free of
constant rank `r`, `π : P̄ ⟶ X` the projective completion, `s : 𝐏(𝒪_X) ⟶ P̄` the zero section and
`ρ = π ∘ s : 𝐏(𝒪_X) ⟶ X`. For `E` finite locally free on `X` and any `K ≅ (s_*ρ^*E)[0]` whose
Chern classes are defined,

  `π_*(ch(K) ∩ [P̄]) = (ch(E) · td(-[𝒞^∨])) ∩ [X]`   in `CH_*(X) ⊗ ℚ`,

where `ch(K)` is the Chern character of the perfect complex `K` (`GRR.perfectCh`). -/
theorem zeroSection_formula (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    {K : DerivedCategory (projectiveCompletion 𝒞).Modules} (hK : HasDefinedChernClasses K)
    (e : K ≅ (DerivedCategory.singleFunctor _ 0).obj
      ((Scheme.Modules.pushforward (zeroSection 𝒞)).obj
        ((Scheme.Modules.pullback (bundleProj (Stacks.Ample.unitModule X))).obj E))) :
    haveI := isSmoothFT_projectiveCompletion 𝒞 r k sX
    rationalProperChowPushforward (fieldChowSituation k) (projectiveCompletionProj 𝒞 ≫ sX) sX rfl
        (cap k (projectiveCompletionProj 𝒞 ≫ sX) (perfectCh (fieldChowSituation k) _ hK)
          (fundamentalClass k (projectiveCompletionProj 𝒞 ≫ sX))) =
      cap k sX (ch (fieldChowSituation k) sX (VectorBundleKZero.classOf X E) *
          toddClass (fieldChowSituation k) sX (-VectorBundleKZero.classOf X (dualSheaf 𝒞)))
        (fundamentalClass k sX) :=
  zeroSection_formula_of k sX 𝒞 r E (cap_topClass_fundamentalClass 𝒞 r k sX) hK e

end B3

end GRR
