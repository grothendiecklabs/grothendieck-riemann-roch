import GRR.Projection
import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.MiddleVanishing
import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.TwistAcyclicRange
import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.TopDegreeVanishing
import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.StructureSheafPushforward
import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.Vanishing
import StacksFrontier.AlgebraicGeometry.HigherDirectImage.Basic
import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Pullback
import StacksFrontier.AlgebraicGeometry.ProjectionFormula.HigherDirectImage
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSheafTensorMonoidal
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictSheafTensorAgree
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDualLocalDualBasis
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.OnSpace
import StacksFrontier.CategoryTheory.Monoidal.RigidProjectionFormula
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# The pushforward of the twisted classes along `ℙⁿ_Y → Y`

For `π : ℙⁿ_Y → Y`, `0 ≤ j ≤ n` and a finite locally free `G` on `Y`,
`π_! [𝒪(-j) ⊗ π^*G] = [G]` if `j = 0` and `0` otherwise (`GRR.projectionPushforwardFormula`).
The input is the projection formula `R^q π_*(F ⊗ π^*G) ≅ R^q π_*F ⊗ G` for a finite locally
free `G` (`GRR.higherDirectImageTensorIso`), together with the vanishing of `R^q π_* 𝒪(-j)`
for `1 ≤ j ≤ n` and of `R^q π_* 𝒪` for `q ≥ 1`, and `π_* 𝒪 ≅ 𝒪_Y`.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)
open Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

universe u

namespace GRR

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Higher direct images of the twists -/

/-- The twisting sheaf `𝒪(d)` on `ℙⁿ_S` is finite locally free, being invertible. -/
theorem isFiniteLocallyFree_twistOver_projectiveSpace (n : ℕ) (S : Scheme.{u}) (d : ℤ) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u}
      (R := (projectiveSpaceOver n S).ringCatSheaf) (twistOver n S d) :=
  haveI := Stacks.InvertibleRankOneScheme.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule _
    (twistOver n S d)
  SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1

variable {Y : Scheme.{u}}

/-- `R^i π_* 𝒪(-j) = 0` for every `i` when `1 ≤ j ≤ n`. -/
theorem isZero_higherDirectImage_twistOver_neg (n j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) (i : ℕ) :
    IsZero (higherDirectImage (projectiveSpaceOver n Y ↘ Y) (twistOver n Y (-(j : ℤ))) i) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact isZero_rightDerivedPlus_pushforward_twistOver_of_acyclic m Y (by push_cast; omega)
    (by omega) (i : ℤ)

/-- `R^i π_* 𝒪 = 0` for `i ≥ 1`. -/
theorem isZero_higherDirectImage_twistOver_zero (n i : ℕ) (hi : 1 ≤ i) :
    IsZero (higherDirectImage (projectiveSpaceOver n Y ↘ Y) (twistOver n Y 0) i) := by
  by_cases hin : i = n
  · subst hin
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    exact isZero_rightDerivedPlus_pushforward_twistOver_top_of_lt m Y (by omega)
  · exact MiddleVanishing.isZero_rightDerivedPlus_pushforward_twistOver_of_ne n Y 0 (i : ℤ)
      (by omega) (by omega)

/-- `R⁰ π_* 𝒪 ≅ 𝒪_Y`. -/
noncomputable def higherDirectImageTwistOverZeroIso (n : ℕ) :
    higherDirectImage (projectiveSpaceOver n Y ↘ Y) (twistOver n Y 0) 0 ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  Stacks.AlgebraicGeometry.HigherDirectImage.higherDirectImageZeroIso _ _ ≪≫
    (Scheme.Modules.pushforward (projectiveSpaceOver n Y ↘ Y)).mapIso
      (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistZeroIsoUnit n Y) ≪≫
    pushforwardUnitIso n Y

/-! ### Duals of finite locally free modules

The monoidal structure used below is `Stacks.PullbackSheafTensor.monoidalSheafTensor`, whose
tensor product is `sheafTensor` on the nose, so that its objects are the tensor products
`Scheme.Modules.tensorObjRingedSpace` of `K₀(Vect)`, and for which the pullback is monoidal
(`Stacks.PullbackSheafTensor.monoidal`). Monoidal structures are passed by `@`-application. -/

/-- The dual `𝓗om(G, 𝒪_Y)` of a module on a scheme. -/
noncomputable abbrev dualModule (G : Y.Modules) : Y.Modules :=
  Stacks.SheafOfModules.dualSheaf Y.toRingedSpace.sheaf.obj
    (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf Y.toRingedSpace.sheaf) G

/-- A finite locally free module and its dual form an exact pairing (Stacks 0FNV), in the strict
monoidal structure. -/
@[instance_reducible] noncomputable def exactPairingDualStrict (G : Y.Modules)
    [hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G] :
    @ExactPairing (Stacks.SheafOfModules.Strict.Mod Y.toRingedSpace.sheaf) _
      (Stacks.SheafOfModules.Strict.monoidalCategory Y.toRingedSpace.sheaf.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf Y.toRingedSpace.sheaf))
      G (dualModule G) := by
  have h := @Stacks.SheafOfModules.OnSpace.isLocallyFiniteFreeSummand_of_isFiniteLocallyFree
    Y.toRingedSpace G hG
  choose U hU n r using h
  have hX : (Opens.grothendieckTopology Y.carrier).CoversTop U :=
    (Opens.coversTop_iff Y.carrier U).mpr (eq_top_iff.mpr fun x _ =>
      TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hU x⟩)
  exact Stacks.SheafOfModules.exactPairingDualSheafOfRetract _ _ G hX
    (I := fun x => ULift.{u} (Fin (n x))) fun x => (r x).some

/-- The pairing `exactPairingDualStrict`, moved to the monoidal structure of `sheafTensor`. -/
@[instance_reducible] noncomputable def exactPairingDual (G : Y.Modules)
    [hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G] :
    @ExactPairing (SheafOfModules (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace)) _
      (Stacks.PullbackSheafTensor.monoidalSheafTensor Y.toRingedSpace) G (dualModule G) :=
  @ExactPairing.map _ _ _ _
    (Stacks.SheafOfModules.Strict.monoidalCategory Y.toRingedSpace.sheaf.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf Y.toRingedSpace.sheaf))
    (SheafOfModules.monoidalCategorySheafTensor Y.toRingedSpace.sheaf) (𝟭 _)
    (SheafOfModules.idMonoidalStrictToSheafTensor Y.toRingedSpace.sheaf) G (dualModule G)
    (exactPairingDualStrict G)

/-- The symmetry of `sheafTensor`, as a braiding of `monoidalSheafTensor`. -/
@[instance_reducible] noncomputable def braidedSheafTensor (Z : RingedSpace.{u, u}) :
    @BraidedCategory (SheafOfModules (Stacks.RingedSpace.structureRingSheaf Z)) _
      (Stacks.PullbackSheafTensor.monoidalSheafTensor Z) :=
  (SheafOfModules.symmetricCategorySheafTensor Z.sheaf).toBraidedCategory

/-- The dual of a finite locally free module is also a left dual. -/
@[instance_reducible] noncomputable def exactPairingDualSwap (G : Y.Modules)
    [hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G] :
    @ExactPairing (SheafOfModules (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace)) _
      (Stacks.PullbackSheafTensor.monoidalSheafTensor Y.toRingedSpace) (dualModule G) G :=
  @BraidedCategory.exactPairing_swap _ _
    (Stacks.PullbackSheafTensor.monoidalSheafTensor Y.toRingedSpace)
    (braidedSheafTensor Y.toRingedSpace) G (dualModule G) (exactPairingDual G)

/-! ### Tensoring by a finite locally free module -/

/-- Tensoring on the right by `H`, `A ↦ A ⊗ H`. -/
noncomputable def tensorRightMod (Z : Scheme.{u}) (H : Z.Modules) : Z.Modules ⥤ Z.Modules :=
  @MonoidalCategory.tensorRight
    (SheafOfModules (Stacks.RingedSpace.structureRingSheaf Z.toRingedSpace)) _
    (Stacks.PullbackSheafTensor.monoidalSheafTensor Z.toRingedSpace) H

theorem tensorRightMod_obj (Z : Scheme.{u}) (H A : Z.Modules) :
    (tensorRightMod Z H).obj A = Scheme.Modules.tensorObjRingedSpace Z A H := rfl

section Exact

variable (Z : Scheme.{u}) (H : Z.Modules)
  [hH : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} H]

/-- `- ⊗ H ⊣ - ⊗ H^∨`. -/
noncomputable def tensorRightModAdj : tensorRightMod Z H ⊣ tensorRightMod Z (dualModule H) :=
  @tensorRightAdjunction _ _ (Stacks.PullbackSheafTensor.monoidalSheafTensor Z.toRingedSpace)
    H (dualModule H) (exactPairingDual H)

/-- `- ⊗ H^∨ ⊣ - ⊗ H`. -/
noncomputable def tensorRightModAdj' : tensorRightMod Z (dualModule H) ⊣ tensorRightMod Z H :=
  @tensorRightAdjunction _ _ (Stacks.PullbackSheafTensor.monoidalSheafTensor Z.toRingedSpace)
    (dualModule H) H (exactPairingDualSwap H)

instance isLeftAdjoint_tensorRightMod : (tensorRightMod Z H).IsLeftAdjoint :=
  (tensorRightModAdj Z H).isLeftAdjoint

instance isRightAdjoint_tensorRightMod : (tensorRightMod Z H).IsRightAdjoint :=
  (tensorRightModAdj' Z H).isRightAdjoint

instance preservesFiniteLimits_tensorRightMod : PreservesFiniteLimits (tensorRightMod Z H) :=
  inferInstance

instance preservesFiniteColimits_tensorRightMod : PreservesFiniteColimits (tensorRightMod Z H) :=
  inferInstance

instance additive_tensorRightMod : (tensorRightMod Z H).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Tensoring by a finite locally free module preserves injective objects (Stacks 01E7). -/
theorem preservesInjectiveObjects_tensorRightMod :
    (tensorRightMod Z H).PreservesInjectiveObjects :=
  @preservesInjectiveObjects_tensorRight_of_exactPairing _ _
    (Stacks.PullbackSheafTensor.monoidalSheafTensor Z.toRingedSpace) H (dualModule H)
    (exactPairingDual H) (exactPairingDualSwap H)

end Exact

/-! ### The projection formula for a finite locally free module (Stacks 01E8) -/

section ProjectionFormula

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X : Scheme.{u}} (f : X ⟶ Y)

instance isFiniteLocallyFree_pullback_scheme (G : Y.Modules)
    [hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback f).obj G) :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme f G hG

variable (G : Y.Modules) [hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G]

/-- **The projection formula in degree zero**, `(- ⊗ f^*G) ⋙ f_* ≅ f_* ⋙ (- ⊗ G)`: both are
right adjoints, of isomorphic functors, `G` being dualizable and `f^*` monoidal. -/
noncomputable def pushforwardTensorIso :
    tensorRightMod X ((Scheme.Modules.pullback f).obj G) ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward f ⋙ tensorRightMod Y G :=
  @Adjunction.tensorRightProjectionIso _ _ _ _
    (Stacks.PullbackSheafTensor.monoidalSheafTensor Y.toRingedSpace)
    (Stacks.PullbackSheafTensor.monoidalSheafTensor X.toRingedSpace) _ _
    (Stacks.RingedSpace.pullbackAdjunction f.toLRSHom.toShHom)
    (Stacks.PullbackSheafTensor.monoidal f.toLRSHom.toShHom) G (dualModule G)
    (exactPairingDualSwap G)

include hG in
/-- An injective module tensored by `f^*G` is right acyclic for `f_*`. -/
theorem rightAcyclic_pushforward_tensorRightMod (I : X.Modules) (hI : Injective I) :
    (Scheme.Modules.pushforward f).rightAcyclic
      ((tensorRightMod X ((Scheme.Modules.pullback f).obj G)).obj I) :=
  haveI := preservesInjectiveObjects_tensorRightMod X ((Scheme.Modules.pullback f).obj G)
  Functor.rightAcyclic_obj_of_preservesInjectiveObjects
    (tensorRightMod X ((Scheme.Modules.pullback f).obj G))
    (Scheme.Modules.pushforward f) I hI

/-- The projection formula in `D⁺`, `D(- ⊗ f^*G) ⋙ Rf_* ≅ Rf_* ⋙ D(- ⊗ G)`. -/
noncomputable def derivedPushforwardTensorIso :
    (tensorRightMod X ((Scheme.Modules.pullback f).obj G)).mapDerivedCategoryPlus ⋙
        (Scheme.Modules.pushforward f).rightDerivedFunctorPlus ≅
      (Scheme.Modules.pushforward f).rightDerivedFunctorPlus ⋙
        (tensorRightMod Y G).mapDerivedCategoryPlus :=
  Stacks.Cohomology.BoundedBelowComplexes.derivedBaseChangePlusIso
    (tensorRightMod X ((Scheme.Modules.pullback f).obj G)) (tensorRightMod Y G)
    (Scheme.Modules.pushforward f) (Scheme.Modules.pushforward f)
    (pushforwardTensorIso f G) (rightAcyclic_pushforward_tensorRightMod f G)

/-- **The projection formula for higher direct images along a finite locally free module**
(Stacks 01E8): `(- ⊗ f^*G) ⋙ R^n f_* ≅ R^n f_* ⋙ (- ⊗ G)`, read off the `D⁺` statement through
`R^n f_* = H^n ∘ Rf_* ∘ (·)[0]` and the exactness of `- ⊗ G`. -/
noncomputable def higherDirectImageTensorIso (n : ℤ) :
    tensorRightMod X ((Scheme.Modules.pullback f).obj G) ⋙
        (Scheme.Modules.pushforward f).rightDerivedPlus n ≅
      (Scheme.Modules.pushforward f).rightDerivedPlus n ⋙ tensorRightMod Y G :=
  Functor.isoWhiskerRight
      (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
        (tensorRightMod X ((Scheme.Modules.pullback f).obj G)) 0).symm
      ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor Y.Modules n) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor X.Modules 0)
      (Functor.isoWhiskerRight (derivedPushforwardTensorIso f G)
        (DerivedCategory.Plus.homologyFunctor Y.Modules n)) ≪≫
    Functor.isoWhiskerLeft
      (DerivedCategory.Plus.singleFunctor X.Modules 0 ⋙
        (Scheme.Modules.pushforward f).rightDerivedFunctorPlus)
      (Functor.isoWhiskerRight
          (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso (tensorRightMod Y G))
          (DerivedCategory.Plus.homologyFunctor Y.Modules n) ≪≫
        Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso (tensorRightMod Y G) n)

end ProjectionFormula

/-! ### The pushforward of the twisted classes -/

section K

variable (k : Type u) [Field k] (sY : Y ⟶ Spec (.of k)) [IsSmoothFT k sY]

theorem pushforwardK_twist_aux [CompactSpace Y] [IsLocallyNoetherian Y] (n j : ℕ) (hj : j ≤ n) :
    pushforwardK (projectiveSpaceOver n Y ↘ Y)
        (vectorBundleEquiv k ((projectiveSpaceOver n Y ↘ Y) ≫ sY) (twistClass Y n (-(j : ℤ)))) =
      if j = 0 then vectorBundleEquiv k sY 1 else 0 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · rw [ite_eq_left rfl]
    simp only [Nat.cast_zero, neg_zero]
    obtain ⟨hcoh, h⟩ := vectorBundleEquiv_classOf k ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
      (twistOver n Y 0) (isFiniteLocallyFree_twistOver_projectiveSpace n Y 0)
    obtain ⟨hcoh1, h1⟩ := vectorBundleEquiv_classOf k sY (SheafOfModules.unit Y.ringCatSheaf)
      inferInstance
    rw [twistClass, h, ← VectorBundleKZero.classOf_unit Y, h1,
      pushforwardK_mk_eq_sum_of_iso _ _ 1
        (fun i hi => isZero_higherDirectImage_twistOver_zero n i hi)
        (fun _ => ⟨SheafOfModules.unit Y.ringCatSheaf, hcoh1⟩)
        (fun i hi => by
          obtain rfl : i = 0 := by omega
          exact ⟨higherDirectImageTwistOverZeroIso n⟩)]
    simp
  · rw [ite_eq_right (by omega)]
    obtain ⟨hcoh, h⟩ := vectorBundleEquiv_classOf k ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
      (twistOver n Y (-(j : ℤ))) (isFiniteLocallyFree_twistOver_projectiveSpace n Y _)
    rw [twistClass, h, pushforwardK_mk_of_isZero _ _ 0
      (fun i _ => isZero_higherDirectImage_twistOver_neg n j hj1 hj i)]
    simp

/-- **The pushforward of the twisting classes along `π : ℙⁿ_Y → Y`**: for `0 ≤ j ≤ n`,
`π_! [𝒪(-j)] = [𝒪_Y]` if `j = 0` and `0` otherwise. -/
theorem pushforwardK_twist (n j : ℕ) (hj : j ≤ n) :
    haveI := compactSpace k sY
    haveI : IsLocallyNoetherian Y := (isNoetherian k sY).toIsLocallyNoetherian
    pushforwardK (projectiveSpaceOver n Y ↘ Y)
        (vectorBundleEquiv k ((projectiveSpaceOver n Y ↘ Y) ≫ sY) (twistClass Y n (-(j : ℤ)))) =
      if j = 0 then vectorBundleEquiv k sY 1 else 0 :=
  haveI := compactSpace k sY
  haveI : IsLocallyNoetherian Y := (isNoetherian k sY).toIsLocallyNoetherian
  pushforwardK_twist_aux k sY n j hj

/-- `R^i π_*(𝒪(d) ⊗ π^*G) ≅ R^i π_*(𝒪(d)) ⊗ G`. -/
noncomputable def higherDirectImageTwistTensorIso (n : ℕ) (d : ℤ) (G : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G] (i : ℕ) :
    higherDirectImage (projectiveSpaceOver n Y ↘ Y)
        (Scheme.Modules.tensorObjRingedSpace _ (twistOver n Y d)
          ((Scheme.Modules.pullback (projectiveSpaceOver n Y ↘ Y)).obj G)) i ≅
      (tensorRightMod Y G).obj
        (higherDirectImage (projectiveSpaceOver n Y ↘ Y) (twistOver n Y d) i) :=
  (higherDirectImageTensorIso (projectiveSpaceOver n Y ↘ Y) G (i : ℤ)).app (twistOver n Y d)

/-- `𝒪_Y ⊗ G ≅ G`. -/
noncomputable def unitTensorIso (G : Y.Modules) :
    (tensorRightMod Y G).obj (SheafOfModules.unit Y.ringCatSheaf) ≅ G :=
  @MonoidalCategoryStruct.leftUnitor
    (SheafOfModules (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace)) _
    (Stacks.PullbackSheafTensor.monoidalSheafTensor Y.toRingedSpace).toMonoidalCategoryStruct G

theorem pushforwardK_twistedPullback_classOf [CompactSpace Y] [IsLocallyNoetherian Y]
    (n j : ℕ) (hj : j ≤ n) (G : Y.Modules)
    (hG : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) G) :
    pushforwardK (projectiveSpaceOver n Y ↘ Y)
        (twistedPullback k sY n j (VectorBundleKZero.classOf Y G)) =
      if j = 0 then vectorBundleEquiv k sY (VectorBundleKZero.classOf Y G) else 0 := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G := hG
  have hpb : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u}
      (R := (projectiveSpaceOver n Y).ringCatSheaf)
      ((Scheme.Modules.pullback (projectiveSpaceOver n Y ↘ Y)).obj G) :=
    isFiniteLocallyFree_pullback_scheme _ G
  unfold twistedPullback
  rw [VectorBundleKZero.pullback_classOf]
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · rw [ite_eq_left rfl]
    simp only [Nat.cast_zero, neg_zero]
    have htw := isFiniteLocallyFree_twistOver_projectiveSpace n Y 0
    rw [twistClass, VectorBundleKZero.classOf_mul _ _ htw hpb]
    obtain ⟨hcoh, h⟩ := vectorBundleEquiv_classOf k ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
      (Scheme.Modules.tensorObjRingedSpace _ (twistOver n Y 0)
        ((Scheme.Modules.pullback (projectiveSpaceOver n Y ↘ Y)).obj G))
      (@AlgebraicGeometry.isFiniteLocallyFree_tensorObj _ _ _ htw hpb)
    obtain ⟨hcohG, hG'⟩ := vectorBundleEquiv_classOf k sY G hG
    have hz : ∀ i, 1 ≤ i → IsZero (higherDirectImage (projectiveSpaceOver n Y ↘ Y)
        (Scheme.Modules.tensorObjRingedSpace _ (twistOver n Y 0)
          ((Scheme.Modules.pullback (projectiveSpaceOver n Y ↘ Y)).obj G)) i) := fun i hi =>
      (Functor.map_isZero (tensorRightMod Y G)
        (isZero_higherDirectImage_twistOver_zero n i hi)).of_iso
        (higherDirectImageTwistTensorIso n 0 G i)
    have e0 : higherDirectImage (projectiveSpaceOver n Y ↘ Y)
        (Scheme.Modules.tensorObjRingedSpace _ (twistOver n Y 0)
          ((Scheme.Modules.pullback (projectiveSpaceOver n Y ↘ Y)).obj G)) 0 ≅ G :=
      higherDirectImageTwistTensorIso n 0 G 0 ≪≫
        (tensorRightMod Y G).mapIso (higherDirectImageTwistOverZeroIso n) ≪≫ unitTensorIso G
    rw [h, hG', pushforwardK_mk_eq_sum_of_iso _ ⟨_, hcoh⟩ 1 hz (fun _ => ⟨G, hcohG⟩)
      (fun i hi => by
        obtain rfl : i = 0 := by omega
        exact ⟨e0⟩)]
    simp
  · rw [ite_eq_right (by omega)]
    have htw := isFiniteLocallyFree_twistOver_projectiveSpace n Y (-(j : ℤ))
    rw [twistClass, VectorBundleKZero.classOf_mul _ _ htw hpb]
    obtain ⟨hcoh, h⟩ := vectorBundleEquiv_classOf k ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
      (Scheme.Modules.tensorObjRingedSpace _ (twistOver n Y (-(j : ℤ)))
        ((Scheme.Modules.pullback (projectiveSpaceOver n Y ↘ Y)).obj G))
      (@AlgebraicGeometry.isFiniteLocallyFree_tensorObj _ _ _ htw hpb)
    have hz : ∀ i, IsZero (higherDirectImage (projectiveSpaceOver n Y ↘ Y)
        (Scheme.Modules.tensorObjRingedSpace _ (twistOver n Y (-(j : ℤ)))
          ((Scheme.Modules.pullback (projectiveSpaceOver n Y ↘ Y)).obj G)) i) := fun i =>
      (Functor.map_isZero (tensorRightMod Y G)
        (isZero_higherDirectImage_twistOver_neg n j hj1 hj i)).of_iso
        (higherDirectImageTwistTensorIso n (-(j : ℤ)) G i)
    rw [h, pushforwardK_mk_of_isZero _ ⟨_, hcoh⟩ 0 (fun i _ => hz i)]
    simp

/-- The map `β ↦ [𝒪(-j)] · π^* β`, read in `K'₀(ℙⁿ_Y)`, as an additive map. -/
noncomputable def twistedPullbackHom (n j : ℕ) :
    VectorBundleKZero Y →+ CoherentKZero (projectiveSpaceOver n Y) :=
  (vectorBundleEquiv k ((projectiveSpaceOver n Y ↘ Y) ≫ sY)).toAddMonoidHom.comp
    ((AddMonoidHom.mulLeft (twistClass Y n (-(j : ℤ)))).comp
      (VectorBundleKZero.pullback (projectiveSpaceOver n Y ↘ Y)))

theorem twistedPullbackHom_apply (n j : ℕ) (β : VectorBundleKZero Y) :
    twistedPullbackHom k sY n j β = twistedPullback k sY n j β := rfl

end K

/-- **The pushforward formula for `π : ℙⁿ_Y → Y`**: `π_!([𝒪(-j)] · π^* β) = β` for `j = 0` and
`0` for `1 ≤ j ≤ n`. Both sides are additive in `β`, and on the class of a finite locally free
`G` this is `pushforwardK_twistedPullback_classOf`. -/
theorem projectionPushforwardFormula (k : Type u) [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsSmoothFT k sY] (n : ℕ) :
    ProjectionPushforwardFormula k sY n := by
  have := compactSpace k sY
  have : IsLocallyNoetherian Y := (isNoetherian k sY).toIsLocallyNoetherian
  intro j hj β
  have key : (pushforwardK (projectiveSpaceOver n Y ↘ Y)).comp (twistedPullbackHom k sY n j) =
      if j = 0 then (vectorBundleEquiv k sY).toAddMonoidHom else 0 := by
    refine VectorBundleKZero.addHom_ext fun G hG => ?_
    rw [AddMonoidHom.comp_apply, twistedPullbackHom_apply,
      pushforwardK_twistedPullback_classOf k sY n j hj G hG]
    split_ifs <;> rfl
  have h := DFunLike.congr_fun key β
  rw [AddMonoidHom.comp_apply, twistedPullbackHom_apply] at h
  rw [h]
  split_ifs <;> rfl

end GRR
