import Mathlib
import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.SmoothGysinRing
import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.GysinChernCharacter
import StacksFrontier.AlgebraicGeometry.Perfect.RegularVectorBundleKGroup
import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective
import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Relative
import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DifferentialsLocallyFree
import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChern.RankOne
import GRR.ToddClass
import GRR.PushforwardK

/-!
# The statement of Grothendieck–Riemann–Roch

Let `k` be a field. For a smooth separated scheme `X` of finite type over `k` (`GRR.IsSmoothFT`;
every smooth quasi-projective variety is one) this file assembles, from Stacks,

* `GRR.CHQ k sX = CH_*(X) ⊗ ℚ`, the rational Chow group, on which `∏_p A^p(X) ⊗ ℚ` acts by cap
  product (`GRR.cap`), with the fundamental class `GRR.fundamentalClass k sX = [X]`;
* `GRR.chK k sX : K'₀(X) → ∏_p A^p(X) ⊗ ℚ`, the Chern character of a coherent class, through the
  identification `K₀(Vect X) ≅ K'₀(X)` of a regular scheme;
* `GRR.tangentClass k sX = [T_X] ∈ K₀(Vect X)`, the class of the dual of `Ω_{X/k}`;
* `GRR.tau k sX : K'₀(X) → CH_*(X) ⊗ ℚ`, `τ_X(α) = (ch(α) · td(T_X)) ∩ [X]`.

`GRR.RiemannRochFor k sX sY f hf` says `f_* (τ_X α) = τ_Y (f_! α)` for all `α ∈ K'₀(X)`: this is
the Grothendieck–Riemann–Roch formula `ch(f_! α) · td(T_Y) = f_*(ch(α) · td(T_X))` read in
`CH_*(Y) ⊗ ℚ = A^*(Y) ⊗ ℚ` by capping with `[Y]`.

The reduction: `RiemannRochFor` is stable under composing a closed immersion with a proper
morphism (`riemannRochFor_comp`), so it holds for every projective morphism as soon as it holds
for closed immersions and for the projections `ℙⁿ_Y → Y` (`riemannRochFor_of_isProjectiveMorphism`).
-/

open AlgebraicGeometry CategoryTheory Stacks.Chow
open scoped TensorProduct

universe u

namespace GRR

variable (k : Type u) [Field k]

/-- `X` is a smooth scheme, separated and of finite type over the field `k`. Every smooth
quasi-projective variety over `k` is one; integrality and quasi-projectivity are not needed. -/
class IsSmoothFT {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) : Prop where
  smooth : Smooth sX
  isSeparated : IsSeparated sX
  quasiCompact : QuasiCompact sX

attribute [instance] IsSmoothFT.smooth IsSmoothFT.isSeparated IsSmoothFT.quasiCompact

/-- A smooth variety over `k` (integral, separated, of finite type, smooth) is smooth, separated
and of finite type. -/
instance isSmoothFT_of_isSmoothVariety {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsSmoothVariety k sX] : IsSmoothFT k sX where
  smooth := inferInstance
  isSeparated := inferInstance
  quasiCompact := inferInstance

section Objects

variable {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- The rational Chow group `CH_*(X) ⊗ ℚ = ⨁_j CH_j(X) ⊗ ℚ` of a scheme locally of finite type
over `k`, graded by dimension. -/
abbrev CHQ [LocallyOfFiniteType sX] : Type u :=
  DirectSum ℤ fun j : ℤ ↦ ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sX j

/-- The rational Chow cohomology ring `A^*(X) ⊗ ℚ = ∏_p A^p(X) ⊗ ℚ` of Stacks. -/
abbrev AQ [LocallyOfFiniteType sX] : Type (u + 1) :=
  RationalTotalChowClass (fieldChowSituation k) sX

/-- The cap product: the action of `c ∈ ∏_p A^p(X) ⊗ ℚ` on `CH_*(X) ⊗ ℚ`, `α ↦ ∑_p c_p ∩ α`. -/
noncomputable def cap [LocallyOfFiniteType sX] (c : AQ k sX) : Module.End ℚ (CHQ k sX) :=
  totalRationalChowCap (fieldChowSituation k) (gysinSystemOfInvertible (fieldChowSituation k)) sX
    (RationalTotalChowClass.ofFamily.symm c)

variable [IsSmoothFT k sX]

include k sX in
theorem isNoetherian : IsNoetherian X := isNoetherian_of_quasiCompact_fieldChowSituation (sX := sX)

include k sX in
theorem compactSpace : CompactSpace X := (quasiCompact_iff_compactSpace sX).mp inferInstance

include k sX in
theorem isAffineHom_diagonal :
    IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X)) :=
  isAffineHom_diagonal_of_isSeparated_fieldChowSituation (sX := sX)

include k sX in
theorem isRegular : IsRegular X := isRegular_of_smooth_over_field sX

/-- The fundamental class `[X] ∈ CH_*(X) ⊗ ℚ`. -/
noncomputable def fundamentalClass : CHQ k sX :=
  haveI := isNoetherian k sX
  rationalFundamentalClass (fieldChowSituation k) sX

/-- The identification `K₀(Vect X) ≅ K'₀(X)` of a smooth scheme over a field (Stacks 0FDJ, 0FDI):
it sends the class of a finite locally free module to its class as a coherent sheaf. -/
noncomputable def vectorBundleEquiv : VectorBundleKZero X ≃+ CoherentKZero X :=
  haveI := compactSpace k sX
  haveI := isAffineHom_diagonal k sX
  regularVectorBundleKZeroAddEquiv X (isRegular k sX)

/-- The identification `K₀(Vect X) ≅ K'₀(X)` sends the class of a finite locally free module to
its class as a coherent sheaf. -/
theorem vectorBundleEquiv_classOf (E : X.Modules)
    (hE : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) :
    ∃ hcoh : Stacks.SheafOfModules.IsCoherent E,
      vectorBundleEquiv k sX (VectorBundleKZero.classOf X E) = KZero.mk _ ⟨E, hcoh⟩ :=
  haveI := compactSpace k sX
  haveI := isAffineHom_diagonal k sX
  ⟨_, regularVectorBundleKZeroAddEquiv_classOf' X (isRegular k sX) E hE⟩

/-- **The Chern character of a coherent class**, `ch : K'₀(X) → ∏_p A^p(X) ⊗ ℚ`: the Chern
character of Stacks 0FEM through the identification `K₀(Vect X) ≅ K'₀(X)`. -/
noncomputable def chK : CoherentKZero X →+ AQ k sX :=
  (ch (fieldChowSituation k) sX : VectorBundleKZero X →+ AQ k sX).comp
    (vectorBundleEquiv k sX).symm.toAddMonoidHom

/-- The tangent sheaf `T_X`, the dual of the sheaf of differentials `Ω_{X/k}`. -/
noncomputable def tangentSheaf : X.Modules :=
  Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf (Scheme.Hom.relativeDifferentials sX)

/-- The class `[T_X] ∈ K₀(Vect X)` of the tangent sheaf. -/
noncomputable def tangentClass : VectorBundleKZero X :=
  VectorBundleKZero.classOf X (tangentSheaf k sX)

/-- The Todd class `td(T_X) ∈ ∏_p A^p(X) ⊗ ℚ` of the tangent sheaf. -/
noncomputable def toddTangent : AQ k sX :=
  toddClass (fieldChowSituation k) sX (tangentClass k sX)

/-- **The Riemann–Roch map** `τ_X : K'₀(X) → CH_*(X) ⊗ ℚ`, `τ_X(α) = (ch(α) · td(T_X)) ∩ [X]`. -/
noncomputable def tau : CoherentKZero X →+ CHQ k sX where
  toFun α := cap k sX (chK k sX α * toddTangent k sX) (fundamentalClass k sX)
  map_zero' := by
    rw [map_zero, zero_mul]
    unfold cap
    rw [map_zero, map_zero]
    rfl
  map_add' a b := by
    rw [map_add, add_mul]
    unfold cap
    rw [map_add, map_add]
    rfl

theorem tau_apply (α : CoherentKZero X) :
    tau k sX α = cap k sX (chK k sX α * toddTangent k sX) (fundamentalClass k sX) := rfl

end Objects

section Statement

variable {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
  [IsSmoothFT k sX] [IsSmoothFT k sY]

/-- **The Grothendieck–Riemann–Roch formula for `f : X ⟶ Y`** (a proper morphism of smooth
separated schemes of finite type over `k`): for every `α ∈ K'₀(X)`,

  `f_* ((ch(α) · td(T_X)) ∩ [X]) = (ch(f_! α) · td(T_Y)) ∩ [Y]`  in `CH_*(Y) ⊗ ℚ`,

where `f_*` is proper pushforward of cycles and `f_! [F] = ∑_i (-1)^i [R^i f_* F]`. -/
def RiemannRochFor (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) : Prop :=
  haveI := compactSpace k sY
  haveI : IsLocallyNoetherian Y := (isNoetherian k sY).toIsLocallyNoetherian
  ∀ α : CoherentKZero X,
    rationalProperChowPushforward (fieldChowSituation k) sX sY hf (tau k sX α) =
      tau k sY (pushforwardK f α)

end Statement

section Reduction

variable {X P Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sP : P ⟶ Spec (.of k))
  (sY : Y ⟶ Spec (.of k)) [IsSmoothFT k sX] [IsSmoothFT k sP] [IsSmoothFT k sY]

/-- Proper pushforward on rational Chow groups is functorial. -/
theorem rationalProperChowPushforward_comp (i : X ⟶ P) [IsProper i] (p : P ⟶ Y) [IsProper p]
    (hi : i ≫ sP = sX) (hp : p ≫ sY = sP) (hip : (i ≫ p) ≫ sY = sX) (γ : CHQ k sX) :
    rationalProperChowPushforward (fieldChowSituation k) sX sY hip γ =
      rationalProperChowPushforward (fieldChowSituation k) sP sY hp
        (rationalProperChowPushforward (fieldChowSituation k) sX sP hi γ) := by
  have h : rationalProperChowPushforward (fieldChowSituation k) sX sY hip =
      (rationalProperChowPushforward (fieldChowSituation k) sP sY hp).comp
        (rationalProperChowPushforward (fieldChowSituation k) sX sP hi) := by
    refine rationalChowHomology_linearMap_ext (fieldChowSituation k) sX fun j q α ↦ ?_
    rw [LinearMap.comp_apply, rationalProperChowPushforward_of_tmul,
      rationalProperChowPushforward_of_tmul, rationalProperChowPushforward_of_tmul]
    congr 2
    exact (DFunLike.congr_fun (properChowPushforward_comp (fieldChowSituation k) sX sP sY i p hi
      hp j (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _)) α).symm
  exact DFunLike.congr_fun h γ

/-- **Riemann–Roch composes**: if the formula holds for a closed immersion `i : X ⟶ P` and for a
proper morphism `p : P ⟶ Y`, it holds for `i ≫ p`. -/
theorem riemannRochFor_comp (i : X ⟶ P) [IsClosedImmersion i] (p : P ⟶ Y) [IsProper p]
    (hi : i ≫ sP = sX) (hp : p ≫ sY = sP) (hip : (i ≫ p) ≫ sY = sX)
    (hI : RiemannRochFor k sX sP i hi) (hP : RiemannRochFor k sP sY p hp) :
    RiemannRochFor k sX sY (i ≫ p) hip := by
  have := compactSpace k sP
  have : IsLocallyNoetherian P := (isNoetherian k sP).toIsLocallyNoetherian
  have := compactSpace k sY
  have : IsLocallyNoetherian Y := (isNoetherian k sY).toIsLocallyNoetherian
  intro α
  have h1 := hI α
  have h2 := hP (pushforwardK i α)
  rw [rationalProperChowPushforward_comp k sX sP sY i p hi hp hip, h1, h2,
    pushforwardK_comp_of_isClosedImmersion i p]
  rfl

end Reduction

section Projective

variable {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsSmoothFT k sY]

/-- Projective space over a smooth separated scheme of finite type over `k` is again one. -/
instance isSmoothFT_projectiveSpaceOver (n : ℕ) :
    IsSmoothFT k ((projectiveSpaceOver n Y ↘ Y) ≫ sY) :=
  haveI : IsProper (projectiveSpaceOver n Y ↘ Y) := isProper_projectiveSpaceOver n Y
  { smooth := inferInstance
    isSeparated := inferInstance
    quasiCompact := inferInstance }

/-- The projection `ℙⁿ_Y ⟶ Y` is proper. -/
instance isProper_projectiveSpaceOver_hom (n : ℕ) : IsProper (projectiveSpaceOver n Y ↘ Y) :=
  isProper_projectiveSpaceOver n Y

/-- **Reduction of Grothendieck–Riemann–Roch to closed immersions and projections.** Suppose the
Riemann–Roch formula holds for every closed immersion of smooth separated schemes of finite type
over `k` into `ℙⁿ_Y`, and for every projection `ℙⁿ_Y ⟶ Y`. Then it holds for every projective
morphism `f : X ⟶ Y`, i.e. every `f` factoring as a closed immersion `X ⟶ ℙⁿ_Y` followed by the
projection. -/
theorem riemannRochFor_of_isProjectiveMorphism
    (hE : ∀ {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsSmoothFT k sX] (n : ℕ)
      (i : X ⟶ projectiveSpaceOver n Y) [IsClosedImmersion i]
      (hi : i ≫ (projectiveSpaceOver n Y ↘ Y) ≫ sY = sX),
      RiemannRochFor k sX ((projectiveSpaceOver n Y ↘ Y) ≫ sY) i hi)
    (hP : ∀ n : ℕ, RiemannRochFor k ((projectiveSpaceOver n Y ↘ Y) ≫ sY) sY
      (projectiveSpaceOver n Y ↘ Y) rfl)
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsSmoothFT k sX] (f : X ⟶ Y) [IsProper f]
    (hf : f ≫ sY = sX) (hproj : IsProjectiveMorphism f) :
    RiemannRochFor k sX sY f hf := by
  obtain ⟨n, i, hi, hfac⟩ := hproj
  subst hfac
  have := hi
  exact riemannRochFor_comp k sX ((projectiveSpaceOver n Y ↘ Y) ≫ sY) sY i
    (projectiveSpaceOver n Y ↘ Y) ((Category.assoc _ _ _).symm.trans hf) rfl hf
    (hE sX n i ((Category.assoc _ _ _).symm.trans hf)) (hP n)

end Projective

end GRR
