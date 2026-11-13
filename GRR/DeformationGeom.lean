import GRR.Statement
import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.RegularImmersionDeformationChernQ
import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedModificationComparison
import StacksFrontier.AlgebraicGeometry.Blowup.SmoothCentre
import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.ProductRegular
import StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatSingleDerivedPullback
import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation
import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Pullback
import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.ClosedImmersionStalkVanishing
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.SyntomicIntoSmooth
import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.AlongAnIsomorphism
import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent

/-!
# Deformation to the normal cone: the geometric half

For a closed immersion `i : X ⟶ P` and a module `E` on `X`, let `W` be the blowup of `𝐏¹_P` in
`∞(X)` (`Stacks.Chow.blowupAtInfinity`), `q : W ⟶ P` (`GRR.DeformationGeom.proj`), `i₀ : P ⟶ W`
the section at zero (`sectionAtZero`), `e : E ⟶ W` and `a : X' ⟶ W` the exceptional divisor and
the strict transform (`exceptionalInclusion`, `strictTransformInclusion`), `i' : 𝐏¹_X ⟶ W` the
closed immersion of Stacks 0FE9, `pr : 𝐏¹_X ⟶ X` (`lineProj`) and `Q = (i'_*(pr^*E))[0]` (`Q`).
This file proves items C0, C2–C5 of `notes/E_plan.md`: `GRR.isSmoothFT_blowupAtInfinity`,
`GRR.derivedPullbackSinglePushforwardIsoOfTorIndependent`, `GRR.deformationZeroFibreIso`,
`GRR.deformationExceptionalFibreIso`, `GRR.isZero_deformationStrictTransform`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

attribute [local instance 10000] HasDerivedCategory.standard

noncomputable section

namespace GRR

namespace DeformationGeom

/-- The two spellings of the pullback of modules along a morphism of schemes agree: both are left
adjoint to the pushforward. -/
noncomputable def modulePullbackIsoPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom ≅ Scheme.Modules.pullback f :=
  Adjunction.leftAdjointUniq
    (RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction f.toLRSHom.toShHom)
    (Scheme.Modules.pullbackPushforwardAdjunction f)

/-- Pulling back along `g` a module pulled back along `p`, when `g ≫ p = 𝟙`, gives the module
back. -/
noncomputable def pullbackPullbackIsoOfCompEqId {X Y : Scheme.{u}} {g : X ⟶ Y} {p : Y ⟶ X}
    (h : g ≫ p = 𝟙 X) (E : X.Modules) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback p).obj E) ≅ E :=
  (Scheme.Modules.pullbackComp g p).app E ≪≫ (Scheme.Modules.pullbackCongr h).app E ≪≫
    (Scheme.Modules.pullbackId X).app E

/-- **`j_*G` restricts to zero off its support**: for a closed immersion `j : P ⟶ W`, a module
`G` on `P` and `k : V ⟶ W` whose image misses that of `j`, `Lk^*((j_*G)[0]) = 0`. -/
theorem isZero_derivedPullback_singlePushforward_of_disjoint {W P V : Scheme.{u}} (j : P ⟶ W)
    [IsClosedImmersion j] (k : V ⟶ W) (G : P.Modules)
    (hk : Disjoint (Set.range k.base) (Set.range j.base)) :
    IsZero ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      k.toLRSHom.toShHom).obj ((DerivedCategory.singleFunctor W.Modules 0).obj
        ((Scheme.Modules.pushforward j).obj G))) := by
  let U : W.Opens := ⟨(Set.range j.base)ᶜ, j.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hU : IsZero ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      U.ι.toLRSHom.toShHom).obj ((DerivedCategory.singleFunctor W.Modules 0).obj
        ((Scheme.Modules.pushforward j).obj G))) := by
    refine isZero_derivedPullback_ofRestrict_compl _ _ j.isClosedEmbedding.isClosed_range ?_ _
      (Iso.refl _)
    intro x hx
    by_contra hrange
    have := subsingleton_stalk_pushforward_of_notMemRange' j G x hrange
    obtain ⟨a, ha⟩ := hx
    exact ha (Subsingleton.elim _ _)
  exact isZero_derivedPullback_of_factors (IsOpenImmersion.lift_fac U.ι k (by
    rw [Scheme.Opens.range_ι]
    exact fun _ hx => Set.disjoint_left.1 hk hx)) hU

end DeformationGeom

/-! ### C2: Tor-independent base change of a flat module -/

/-- **Tor-independent base change of a pushed-forward flat module** (Stacks 0E23). For a
cartesian square
```
Z' --i'--> X'
|g          |f
Z  --j---> X
```
with `j` a closed immersion, `Z` and `X'` Tor independent over `X`, and `G` a flat module on
`Z`, `Lf^*((j_*G)[0]) ≅ (i'_*(g^*G))[0]`. -/
noncomputable def derivedPullbackSinglePushforwardIsoOfTorIndependent {Z' X' Z X : Scheme.{u}}
    {i' : Z' ⟶ X'} {g : Z' ⟶ Z} {f : X' ⟶ X} {j : Z ⟶ X} (sq : IsPullback i' g f j)
    [IsClosedImmersion j] (h : TorIndependent j f) (G : Z.Modules)
    (hG : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Z.sheaf) G) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj ((Scheme.Modules.pushforward j).obj G)) ≅
      (DerivedCategory.singleFunctor X'.Modules 0).obj
        ((Scheme.Modules.pushforward i').obj ((Scheme.Modules.pullback g).obj G)) := by
  haveI : IsClosedImmersion i' := MorphismProperty.of_isPullback sq.flip inferInstance
  have hiso := derivedBaseChangeIsoOfTorIndependent sq inferInstance h
    ((DerivedCategory.singleFunctor Z.Modules 0).obj G)
  exact (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        f.toLRSHom.toShHom).mapIso
      (Stacks.Thickenings.derivedPushforwardSingleIso j.toLRSHom.toShHom
        j.isClosedEmbedding _).symm ≪≫
    @asIso _ _ _ _ _ hiso ≪≫
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
        i'.toLRSHom.toShHom).mapIso
      (Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso g.toLRSHom.toShHom
          G hG ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso
          ((DeformationGeom.modulePullbackIsoPullback g).app G)) ≪≫
    Stacks.Thickenings.derivedPushforwardSingleIso i'.toLRSHom.toShHom i'.isClosedEmbedding _

namespace DeformationGeom

variable {k : Type u} [Field k] {X P : Scheme.{u}} (sP : P ⟶ Spec (.of k)) (i : X ⟶ P)

/-- The structure morphism `q : W ⟶ P` of the blowup at infinity `W = Bl_{∞(X)} 𝐏¹_P`. -/
abbrev proj : blowupAtInfinity i.ker ⟶ P :=
  modificationProjection sP (blowupAtInfinityToProjectiveLineProduct i.ker sP)

/-- The section at zero `i₀ : P ⟶ W`, the inclusion of the fibre `W_0 ≅ P` over `0 ∈ 𝐏¹`. -/
abbrev sectionAtZero : P ⟶ blowupAtInfinity i.ker :=
  modificationSectionAtZero sP (blowupAtInfinityToProjectiveLineProduct i.ker sP)
    (isIso_modificationFibreAtZeroProjection sP _
      (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct i.ker sP))

/-- `i₀` is a section of `q`. -/
theorem sectionAtZero_comp_proj : sectionAtZero sP i ≫ proj sP i = 𝟙 P :=
  modificationSectionAtZero_comp_projection sP _
    (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct i.ker sP)

/-- `i₀` is a section of `q`, composed with a further morphism. -/
theorem sectionAtZero_comp_proj_assoc {Z : Scheme.{u}} (h : P ⟶ Z) :
    sectionAtZero sP i ≫ proj sP i ≫ h = h := by
  rw [← Category.assoc, sectionAtZero_comp_proj, Category.id_comp]

/-- `i₀` is a section of `W ⟶ P`, in the simp-normal form `q = blowupAtInfinityToBase`. -/
@[simp]
theorem sectionAtZero_comp_blowupAtInfinityToBase :
    sectionAtZero sP i ≫ blowupAtInfinityToBase i.ker = 𝟙 P := by
  rw [← modificationProjection_blowupAtInfinityToProjectiveLineProduct i.ker sP]
  exact sectionAtZero_comp_proj sP i

/-- `i₀` is a section of `W ⟶ P`, composed with a further morphism. -/
@[simp]
theorem sectionAtZero_comp_blowupAtInfinityToBase_assoc {Z : Scheme.{u}} (h : P ⟶ Z) :
    sectionAtZero sP i ≫ blowupAtInfinityToBase i.ker ≫ h = h := by
  rw [← Category.assoc, sectionAtZero_comp_blowupAtInfinityToBase, Category.id_comp]

/-- The section at zero is a closed immersion: it is the base change of the zero section of
`𝐏¹_P`. -/
instance isClosedImmersion_sectionAtZero : IsClosedImmersion (sectionAtZero sP i) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_modificationSectionAtZero sP _
      (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct i.ker sP)).flip inferInstance

/-- The inclusion `e : E ⟶ W` of the exceptional divisor, read as `E = W_∞ ×_P X`. -/
abbrev exceptionalInclusion :
    pullback (modificationProjectionAtInfinity sP
      (blowupAtInfinityToProjectiveLineProduct i.ker sP)) i ⟶ blowupAtInfinity i.ker :=
  pullback.fst (modificationProjectionAtInfinity sP
      (blowupAtInfinityToProjectiveLineProduct i.ker sP)) i ≫
    modificationInclusionAtInfinity sP (blowupAtInfinityToProjectiveLineProduct i.ker sP)

/-- The exceptional divisor lies over `X`: `e ≫ q = (E ⟶ X) ≫ i`. -/
theorem exceptionalInclusion_comp_proj :
    exceptionalInclusion sP i ≫ proj sP i =
      pullback.snd (modificationProjectionAtInfinity sP
        (blowupAtInfinityToProjectiveLineProduct i.ker sP)) i ≫ i := by
  rw [exceptionalInclusion, Category.assoc, ← pullback.condition]

/-- The exceptional divisor lies over `X`, composed with a further morphism. -/
theorem exceptionalInclusion_comp_proj_assoc {Z : Scheme.{u}} (h : P ⟶ Z) :
    exceptionalInclusion sP i ≫ proj sP i ≫ h =
      pullback.snd (modificationProjectionAtInfinity sP
        (blowupAtInfinityToProjectiveLineProduct i.ker sP)) i ≫ i ≫ h := by
  rw [← Category.assoc, exceptionalInclusion_comp_proj, Category.assoc]

/-- The inclusion `a : X' ⟶ W` of the strict transform `X'` of `P` (inside `W_∞`). -/
abbrev strictTransformInclusion :
    (strictTransformIdealAtInfinity i.ker).subscheme ⟶ blowupAtInfinity i.ker :=
  strictTransformToFibreAtInfinity sP i ≫
    modificationInclusionAtInfinity sP (blowupAtInfinityToProjectiveLineProduct i.ker sP)

variable [IsClosedImmersion i]

/-- The projection `pr : 𝐏¹_X ⟶ X`, with `X` read as the closed subscheme `V(ker i)`. -/
abbrev lineProj : relativeProjectiveLine i.ker.subscheme ⟶ X :=
  (relativeProjectiveLine i.ker.subscheme ↘ i.ker.subscheme) ≫ inv i.toImage

/-- `G = pr^*E` on `𝐏¹_X`. -/
abbrev G (E : X.Modules) : (relativeProjectiveLine i.ker.subscheme).Modules :=
  (Scheme.Modules.pullback (lineProj i)).obj E

/-- **The object `Q = (i'_*(pr^*E))[0]` of `D(𝒪_W)`**, the deformation of `i_*E` to the normal
cone: `i' : 𝐏¹_X ⟶ W` is the closed immersion of Stacks 0FE9 and `pr : 𝐏¹_X ⟶ X`. -/
abbrev Q (E : X.Modules) : DerivedCategory (blowupAtInfinity i.ker).Modules :=
  (DerivedCategory.singleFunctor (blowupAtInfinity i.ker).Modules 0).obj
    ((Scheme.Modules.pushforward (lineToBlowupAtInfinity i.ker)).obj (G i E))

/-- `pr` restricted to the infinity section `X ⟶ 𝐏¹_X` is the identity. -/
theorem lineInfinitySection_comp_lineProj :
    (i.toImage ≫ lineInfinitySection i.ker.subscheme) ≫ lineProj i = 𝟙 X := by
  rw [lineProj, Category.assoc, ← Category.assoc (lineInfinitySection _), lineInfinitySection_comp,
    Category.id_comp, IsIso.hom_inv_id]

/-- The module `i'_*(pr^*E)` underlying `Q` is coherent when `E` is finite locally free and `P`
is locally Noetherian: `Q` is a coherent module placed in degree `0`. -/
theorem coherentModules_pushforward_G [IsLocallyNoetherian P] (E : X.Modules)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    Stacks.SheafOfModules.coherentModules (blowupAtInfinity i.ker).ringCatSheaf
      ((Scheme.Modules.pushforward (lineToBlowupAtInfinity i.ker)).obj (G i E)) := by
  have : IsLocallyNoetherian (blowupAtInfinity i.ker) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowupAtInfinityToBase i.ker)
  have : IsLocallyNoetherian (relativeProjectiveLine i.ker.subscheme) :=
    isLocallyNoetherian_of_isClosedImmersion (lineToBlowupAtInfinity i.ker)
  have h1 := isCoherent_of_isFiniteLocallyFree_of_isLocallyNoetherian (G i E)
    (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme _ _ hE)
  have h2 := (Stacks.AlgebraicGeometry.GrothendieckGroupAffine.isCoherent_iff_isCoherent' _).1 h1
  exact (Stacks.AlgebraicGeometry.GrothendieckGroupAffine.isCoherent_iff_isCoherent' _).2
    (isCoherent_pushforward_of_isClosedImmersion (lineToBlowupAtInfinity i.ker) (G i E))

/-- The open immersion `c : b⁻¹(𝐀¹_P) ⟶ W` of the part of `W` over the affine chart of `𝐏¹_P`. -/
abbrev chartι :
    pullback (blowupAtInfinityToProjectiveLineProduct i.ker sP) (projectiveLineAffineChart sP) ⟶
      blowupAtInfinity i.ker :=
  pullback.fst (blowupAtInfinityToProjectiveLineProduct i.ker sP) (projectiveLineAffineChart sP)

/-- **`Q` on the chart `b⁻¹(𝐀¹_P)`**: the restriction of `Q` to the open `b⁻¹(𝐀¹_P) ⊆ W` is the
derived pullback of `(i_*E)[0]` along the flat morphism `b⁻¹(𝐀¹_P) ⟶ P`. Both are the pushforward
of the pullback of `E` to `𝐏¹_X ∩ b⁻¹(𝐀¹_P) = X ×_P b⁻¹(𝐀¹_P)` (flat base change). -/
def chartIso (E : X.Modules) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (chartι sP i).toLRSHom.toShHom).obj (Q i E) ≅
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (chartι sP i ≫ proj sP i).toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor P.Modules 0).obj ((Scheme.Modules.pushforward i).obj E)) := by
  have sq := isPullback_lineToBlowupAtInfinity_affineChart sP i
  have sqc := (IsPullback.of_hasPullback (lineToBlowupAtInfinity i.ker) (chartι sP i)).flip
  have : Flat (chartι sP i ≫ proj sP i) := flat_affineChartRestriction_blowupAtInfinity sP i
  letI : PreservesFiniteLimits (RingedSpaceModuleAdjunction.modulePullback
      (chartι sP i ≫ proj sP i).toLRSHom.toShHom) :=
    preservesFiniteLimits_pullback_of_flat (chartι sP i ≫ proj sP i)
  letI : PreservesFiniteColimits (RingedSpaceModuleAdjunction.modulePullback
      (chartι sP i ≫ proj sP i).toLRSHom.toShHom) :=
    RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback _
  letI : (RingedSpaceModuleAdjunction.modulePullback
      (chartι sP i ≫ proj sP i).toLRSHom.toShHom).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  letI : PreservesFiniteLimits (RingedSpaceModuleAdjunction.modulePullback
      (chartι sP i).toLRSHom.toShHom) :=
    preservesFiniteLimits_pullback_of_flat (chartι sP i)
  letI : PreservesFiniteColimits (RingedSpaceModuleAdjunction.modulePullback
      (chartι sP i).toLRSHom.toShHom) :=
    RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback _
  letI : (RingedSpaceModuleAdjunction.modulePullback
      (chartι sP i).toLRSHom.toShHom).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  refine derivedPullbackSingleIsoOfPreservesHomology (chartι sP i).toLRSHom.toShHom
      ((Scheme.Modules.pushforward (lineToBlowupAtInfinity i.ker)).obj (G i E)) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso ((modulePullbackIsoPullback (chartι sP i)).app
      ((Scheme.Modules.pushforward (lineToBlowupAtInfinity i.ker)).obj (G i E))) ≪≫ ?_
  refine ?_ ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso
      ((modulePullbackIsoPullback (chartι sP i ≫ proj sP i)).app
        ((Scheme.Modules.pushforward i).obj E)).symm ≪≫
    (derivedPullbackSingleIsoOfPreservesHomology (chartι sP i ≫ proj sP i).toLRSHom.toShHom
      ((Scheme.Modules.pushforward i).obj E)).symm
  refine (DerivedCategory.singleFunctor _ 0).mapIso ?_
  refine (baseChangeIsoOfKernelAnnihilates sqc.w
      (kernelAnnihilatesPullbackPushforward_of_isPullback sqc)).app (G i E) ≪≫ ?_
  refine ?_ ≪≫ ((baseChangeIsoOfKernelAnnihilates sq.w.symm
      (kernelAnnihilatesPullbackPushforward_of_isPullback sq.flip)).app E).symm
  exact (Scheme.Modules.pushforward (pullback.snd (lineToBlowupAtInfinity i.ker)
      (chartι sP i))).mapIso ((Scheme.Modules.pullbackComp
        (pullback.fst (lineToBlowupAtInfinity i.ker) (chartι sP i)) (lineProj i)).app E)

end DeformationGeom

open DeformationGeom

/-! ### C0: the deformation space is smooth -/

/-- **`W` is smooth, separated and of finite type over `k`** (item C0): for a closed immersion
`i : X ⟶ P` of schemes smooth, separated and of finite type over `k`, the blowup
`W = Bl_{∞(X)} 𝐏¹_P` with its morphism `q ≫ sP : W ⟶ P ⟶ Spec k` is again one. `W` is the blowup
of `𝐏¹_P` (smooth over `k`) in the closed subscheme `∞(X) ≅ X` (smooth over `k`), hence smooth by
Stacks 0FUT; `q` is proper. -/
theorem isSmoothFT_blowupAtInfinity (k : Type u) [Field k] {X P : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sP : P ⟶ Spec (.of k)) [IsSmoothFT k sX] [IsSmoothFT k sP]
    (i : X ⟶ P) [IsClosedImmersion i] (hi : i ≫ sP = sX) :
    IsSmoothFT k (proj sP i ≫ sP) := by
  have : IsNoetherian P := isNoetherian k sP
  refine ⟨?_, inferInstance, inferInstance⟩
  have : Smooth ((i ≫ lineInfinitySection P) ≫ (relativeProjectiveLine P ↘ P) ≫ sP) := by
    rw [Category.assoc, ← Category.assoc (lineInfinitySection P), lineInfinitySection_comp,
      Category.id_comp, hi]
    infer_instance
  have h := Stacks.AlgebraicGeometry.smooth_blowUpToBase_comp
    ((relativeProjectiveLine P ↘ P) ≫ sP) (i ≫ lineInfinitySection P)
  have hker : (i ≫ lineInfinitySection P).ker = infinityCentreIdeal i.ker :=
    Scheme.Hom.ker_comp _ _
  rw [hker] at h
  rw [proj, modificationProjection_blowupAtInfinityToProjectiveLineProduct, blowupAtInfinityToBase,
    Category.assoc]
  exact h

/-- A closed immersion of schemes smooth over `k` is a regular immersion (the hypothesis `hreg`
of `GRR.deformationExceptionalFibreIso`). -/
theorem DeformationGeom.isRegularImmersion_of_isSmoothFT (k : Type u) [Field k]
    {X P : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sP : P ⟶ Spec (.of k)) [IsSmoothFT k sX]
    [IsSmoothFT k sP] (i : X ⟶ P) [IsClosedImmersion i] (hi : i ≫ sP = sX) :
    Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion i := by
  have : Smooth (i ≫ sP) := by
    rw [hi]
    infer_instance
  exact Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_of_smooth i sP

/-! ### C3: the zero fibre -/

/-- **`Q` restricted to the zero fibre is `i_*E`** (item C3): `L i₀^* Q ≅ (i_*E)[0]` for the
section at zero `i₀ : P ⟶ W`. The section factors as `σ : P ⟶ b⁻¹(𝐀¹_P)` followed by the open
immersion of the chart, `σ` is a section of the flat `b⁻¹(𝐀¹_P) ⟶ P`, and on the chart `Q` is the
pullback of `(i_*E)[0]` (`GRR.DeformationGeom.chartIso`). No hypothesis on `E` is needed. -/
def deformationZeroFibreIso {k : Type u} [Field k] {X P : Scheme.{u}} (sP : P ⟶ Spec (.of k))
    (i : X ⟶ P) [IsClosedImmersion i] (E : X.Modules) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (sectionAtZero sP i).toLRSHom.toShHom).obj (Q i E) ≅
      (DerivedCategory.singleFunctor P.Modules 0).obj ((Scheme.Modules.pushforward i).obj E) := by
  let σ : P ⟶ pullback (blowupAtInfinityToProjectiveLineProduct i.ker sP)
      (projectiveLineAffineChart sP) :=
    modificationSectionAtZeroToChart (C := fieldChowSituation k) (f := sP)
      (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct i.ker sP)
  have hσ : σ ≫ chartι sP i = sectionAtZero sP i := modificationSectionAtZeroToChart_fst _
  have h1 : (sectionAtZero sP i).toLRSHom.toShHom =
      σ.toLRSHom.toShHom ≫ (chartι sP i).toLRSHom.toShHom := by
    rw [← hσ]
    rfl
  have h2 : σ.toLRSHom.toShHom ≫ (chartι sP i ≫ proj sP i).toLRSHom.toShHom = 𝟙 _ := by
    have h : σ ≫ chartι sP i ≫ proj sP i = 𝟙 P := by
      rw [← Category.assoc, hσ, sectionAtZero_comp_proj]
    exact congrArg (fun f : P ⟶ P => f.toLRSHom.toShHom) h
  exact (eqToIso (Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullback_eq_of_eq h1)).app
      (Q i E) ≪≫
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical σ.toLRSHom.toShHom
      (chartι sP i).toLRSHom.toShHom).app (Q i E)).symm ≪≫
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      σ.toLRSHom.toShHom).mapIso (chartIso sP i E) ≪≫
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical σ.toLRSHom.toShHom
      (chartι sP i ≫ proj sP i).toLRSHom.toShHom).app
        ((DerivedCategory.singleFunctor P.Modules 0).obj ((Scheme.Modules.pushforward i).obj E)) ≪≫
    (eqToIso (Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullback_eq_of_eq h2)).app
      ((DerivedCategory.singleFunctor P.Modules 0).obj ((Scheme.Modules.pushforward i).obj E)) ≪≫
    (Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIso _).app
      ((DerivedCategory.singleFunctor P.Modules 0).obj ((Scheme.Modules.pushforward i).obj E))

/-! ### C4: the exceptional divisor -/

/-- **`Q` restricted to the exceptional divisor is the zero section sheaf** (item C4): for
`e : E = W_∞ ×_P X ⟶ W`, `φ : E ≅ P̄ = 𝐏(𝒞 ⊕ 𝒪_X)` (`𝒞` the conormal sheaf), the zero section
`s : 𝐏(𝒪_X) ⟶ P̄` and `ρ : 𝐏(𝒪_X) ⟶ X`, `L e^* Q ≅ Lφ^*((s_*ρ^*E)[0])`. Both sides are the
pushforward of `E` along the vertex `X ⟶ E` of the normal cone: the left by Tor-independent base
change along `e` (Stacks 0FE9), the right by flat base change along `φ`, the vertex being the zero
section under `φ`. The conormal module is assumed of constant rank `r`. -/
def deformationExceptionalFibreIso {k : Type u} [Field k] {X P : Scheme.{u}}
    (sP : P ⟶ Spec (.of k)) (i : X ⟶ P) [IsClosedImmersion i] [IsLocallyNoetherian X]
    (hreg : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion i) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule i) r]
    (E : X.Modules) [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (exceptionalInclusion sP i).toLRSHom.toShHom).obj (Q i E) ≅
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (exceptionalFibreIsoProjectiveCompletion sP i hreg).hom.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor (Stacks.ProjectiveCompletion.projectiveCompletion
            (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
              (VirtualNormalBundle.ofIsRegularImmersion i hreg).bundle)).Modules 0).obj
          ((Scheme.Modules.pushforward (Stacks.ProjectiveCompletion.zeroSection
              (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
                (VirtualNormalBundle.ofIsRegularImmersion i hreg).bundle))).obj
            ((Scheme.Modules.pullback (bundleProj (Stacks.Ample.unitModule X))).obj E))) := by
  have hker := ker_vertex_comp_exceptionalDivisorIsoProjectiveCompletion_hom i hreg r
  let θ := Stacks.AlgebraicGeometry.KerChart.isoOfKerEq _ _ hker
  have hθ : θ.hom ≫ ((normalConeZeroSection i ≫ normalConeToExceptionalDivisor i) ≫
      (exceptionalDivisorIsoProjectiveCompletion i hreg).hom) =
      Stacks.ProjectiveCompletion.zeroSection (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
        (VirtualNormalBundle.ofIsRegularImmersion i hreg).bundle) :=
    Stacks.AlgebraicGeometry.KerChart.isoOfKerEq_hom_comp _ _ hker
  have sq : IsPullback ((normalConeZeroSection i ≫ normalConeToExceptionalDivisor i) ≫
        (isPullback_exceptionalDivisorToFibreAtInfinity sP i).isoPullback.hom) θ.inv
      (exceptionalFibreIsoProjectiveCompletion sP i hreg).hom
      (Stacks.ProjectiveCompletion.zeroSection (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
        (VirtualNormalBundle.ofIsRegularImmersion i hreg).bundle)) := by
    refine IsPullback.of_vert_isIso ⟨?_⟩
    rw [← hθ, Iso.inv_hom_id_assoc]
    simp only [exceptionalFibreIsoProjectiveCompletion, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Iso.hom_inv_id_assoc]
  have hρ : θ.inv ≫ bundleProj (Stacks.Ample.unitModule X) = 𝟙 X := by
    rw [← Stacks.ProjectiveCompletion.zeroSection_comp_projectiveCompletionProj
      (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
        (VirtualNormalBundle.ofIsRegularImmersion i hreg).bundle), ← hθ]
    simp only [Category.assoc, Iso.inv_hom_id_assoc,
      exceptionalDivisorIsoProjectiveCompletion_hom_projection]
    simpa only [Category.assoc] using vertex_comp_exceptionalDivisorToCentre i
  have hG : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (G i E) :=
    AlgebraicGeometry.SheafOfModules.isFlat_of_isFiniteLocallyFree _
      (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme _ _ hE)
  have hρE : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      ((Scheme.Modules.pullback (bundleProj (Stacks.Ample.unitModule X))).obj E) :=
    AlgebraicGeometry.SheafOfModules.isFlat_of_isFiniteLocallyFree _
      (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme _ _ hE)
  exact derivedPullbackSinglePushforwardIsoOfTorIndependent
      (isPullback_vertex_lineToBlowupAtInfinity sP i)
      (torIndependent_lineToBlowupAtInfinity_exceptionalFibre sP i) _ hG ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso ((Scheme.Modules.pushforward _).mapIso
      (pullbackPullbackIsoOfCompEqId (lineInfinitySection_comp_lineProj i) E ≪≫
        (pullbackPullbackIsoOfCompEqId hρ E).symm)) ≪≫
    (derivedPullbackSinglePushforwardIsoOfTorIndependent sq (torIndependent_of_flat_right _ _) _
      hρE).symm

/-! ### C5: the strict transform -/

/-- **`Q` restricted to the strict transform vanishes** (item C5): `L a^* Q = 0` for the inclusion
`a : X' ⟶ W_∞ ⟶ W` of the strict transform of `P`, because `𝐏¹_X` misses `X'` (Stacks 0FE9). -/
theorem isZero_deformationStrictTransform {k : Type u} [Field k] {X P : Scheme.{u}}
    (sP : P ⟶ Spec (.of k)) (i : X ⟶ P) [IsClosedImmersion i] (E : X.Modules) :
    IsZero ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (strictTransformInclusion sP i).toLRSHom.toShHom).obj (Q i E)) := by
  refine isZero_derivedPullback_singlePushforward_of_disjoint _ _ _ ?_
  rw [strictTransformInclusion, strictTransformToFibreAtInfinity_inclusion,
    Scheme.IdealSheafData.range_subschemeι, Set.disjoint_iff]
  rintro _ ⟨hx, y, rfl⟩
  have hy : y ∈ ((strictTransformIdealAtInfinity i.ker).comap
      (lineToBlowupAtInfinity i.ker)).support := by
    rwa [Scheme.IdealSheafData.support_comap]
  rwa [congrArg Scheme.IdealSheafData.support
    (comap_strictTransformIdealAtInfinity_lineToBlowupAtInfinity i.ker)] at hy

end GRR

end
