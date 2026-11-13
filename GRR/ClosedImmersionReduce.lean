import GRR.PerfectCh
import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DimensionPart
import StacksFrontier.AlgebraicGeometry.Conormal.SmoothRank
import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.RegularImmersionGysinComposition
import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.ClosedSubschemeCycle
import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Local
import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleBaseChangeIso
import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.OpenImmersion
import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveLine
import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.DisjointSections
import StacksFrontier.AlgebraicGeometry.Reflexive.DualMap
import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.FiniteLocallyFreeReflexive
import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree
import StacksFrontier.AlgebraicGeometry.Chow.VectorBundleKZeroPullbackComp
import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.SecondAdamsChernCharacter
import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.ShortExact
import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceComparison

/-!
# Reduction of the closed immersion formula to its core case

`GRR.closedImmersionFormula_of_core` deduces `GRR.ClosedImmersionFormula` for every closed
immersion of smooth schemes over a field from `GRR.CoreClosedImmersionFormula`, the case of pure
dimensions and conormal sheaf of constant rank `r ≥ 1` (item F of `notes/E_plan.md`). Source and
target are cut into their open and closed parts of constant dimension (R1, R2); the codimension
zero case goes through the zero section of `𝐏¹_P` (R3). The normal class is identified with the
one of Part C by `GRR.normalClass_eq_classOf_dualSheaf_bundle` (R5).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf dualSheafIsoOfIso toDoubleDual)
open scoped TensorProduct

universe u

noncomputable section

namespace GRR

section Core

variable (k : Type u) [Field k]

/-- **The core case of `GRR.ClosedImmersionFormula`** (item C7 of `notes/E_plan.md`). For every
closed immersion `i : X ⟶ P` of smooth separated schemes of finite type over `k` with `X`
nonempty, `P` smooth of pure relative dimension `n`, `X` smooth of pure relative dimension `m`,
and the conormal sheaf `Stacks.Chow.conormalModule i` finite locally free of constant rank
`r ≥ 1` with `n = m + r`, and for every finite locally free `E` on `X`,

  `ch(i_! θ[E]) ∩ [P] = i_*((ch(E) · td(N_{X/P})⁻¹) ∩ [X])`.

Stacks' `RelativeDimension` follows from `SmoothOfRelativeDimension` by
`GRR.ClosedImmersionReduce.relativeDimension_of_smoothOfRelativeDimension`; the rank of
`GRR.conormalSheaf` is `GRR.isFiniteLocallyFreeOfRank_conormalSheaf_iff`, and the normal class
of Part C is `GRR.normalClass_eq_classOf_dualSheaf_bundle`. -/
def CoreClosedImmersionFormula : Prop :=
  ∀ {X P : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sP : P ⟶ Spec (.of k)) [IsSmoothFT k sX]
    [IsSmoothFT k sP] (i : X ⟶ P) [IsClosedImmersion i] (hi : i ≫ sP = sX) (n m r : ℕ)
    [SmoothOfRelativeDimension n sP] [SmoothOfRelativeDimension m sX] [Nonempty X]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.Chow.conormalModule i) r],
    1 ≤ r → n = m + r →
    ∀ (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E],
      haveI := compactSpace k sP
      haveI : IsLocallyNoetherian P := (isNoetherian k sP).toIsLocallyNoetherian
      cap k sP (chK k sP (pushforwardK i (vectorBundleEquiv k sX (VectorBundleKZero.classOf X E))))
          (fundamentalClass k sP) =
        rationalProperChowPushforward (fieldChowSituation k) sX sP hi
          (cap k sX (ch (fieldChowSituation k) sX (VectorBundleKZero.classOf X E) *
              toddClass (fieldChowSituation k) sX (-normalClass k sP i))
            (fundamentalClass k sX))

end Core

namespace ClosedImmersionReduce

/-! ### The two sides of the formula -/

section Sides

variable (k : Type u) [Field k] {X P : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sP : P ⟶ Spec (.of k)) [IsSmoothFT k sX] [IsSmoothFT k sP] (i : X ⟶ P) [IsClosedImmersion i]

/-- The left side `α ↦ ch(i_! α) ∩ [P]` of `GRR.ClosedImmersionFormula`. -/
def lhs : CoherentKZero X →+ CHQ k sP :=
  haveI := compactSpace k sP
  haveI : IsLocallyNoetherian P := (isNoetherian k sP).toIsLocallyNoetherian
  (PerfectCh.capFundamental k sP).comp ((chK k sP).comp (pushforwardK i))

variable (hi : i ≫ sP = sX)

/-- The right side `α ↦ i_*((ch(α) · td(N)⁻¹) ∩ [X])` of `GRR.ClosedImmersionFormula`. -/
def rhs : CoherentKZero X →+ CHQ k sP :=
  (rationalProperChowPushforward (fieldChowSituation k) sX sP hi).toAddMonoidHom.comp
    ((PerfectCh.capFundamental k sX).comp
      ((AddMonoidHom.mulRight (toddClass (fieldChowSituation k) sX (-normalClass k sP i))).comp
        (chK k sX)))

theorem lhs_apply [IsLocallyNoetherian P] [CompactSpace P] (α : CoherentKZero X) :
    lhs k sP i α = cap k sP (chK k sP (pushforwardK i α)) (fundamentalClass k sP) :=
  rfl

theorem rhs_apply (α : CoherentKZero X) :
    rhs k sX sP i hi α = rationalProperChowPushforward (fieldChowSituation k) sX sP hi
      (cap k sX (chK k sX α * toddClass (fieldChowSituation k) sX (-normalClass k sP i))
        (fundamentalClass k sX)) :=
  rfl

theorem closedImmersionFormula_iff :
    ClosedImmersionFormula k sX sP i hi ↔ lhs k sP i = rhs k sX sP i hi :=
  ⟨fun h ↦ AddMonoidHom.ext h, fun h α ↦ DFunLike.congr_fun h α⟩

theorem lhs_eq_rhs (h : ClosedImmersionFormula k sX sP i hi) (α : CoherentKZero X) :
    lhs k sP i α = rhs k sX sP i hi α :=
  DFunLike.congr_fun ((closedImmersionFormula_iff k sX sP i hi).1 h) α

theorem closedImmersionFormula_of_lhs_eq_rhs (h : ∀ α, lhs k sP i α = rhs k sX sP i hi α) :
    ClosedImmersionFormula k sX sP i hi :=
  (closedImmersionFormula_iff k sX sP i hi).2 (AddMonoidHom.ext h)

/-- It suffices to compare the two sides on the classes `θ[E]` of finite locally free modules. -/
theorem closedImmersionFormula_of_lhs_eq_rhs_bundles
    (h : ∀ (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E],
      lhs k sP i (vectorBundleEquiv k sX (VectorBundleKZero.classOf X E)) =
        rhs k sX sP i hi (vectorBundleEquiv k sX (VectorBundleKZero.classOf X E))) :
    ClosedImmersionFormula k sX sP i hi := by
  refine closedImmersionFormula_of_lhs_eq_rhs k sX sP i hi fun α ↦ ?_
  have hφψ : (lhs k sP i).comp (vectorBundleEquiv k sX).toAddMonoidHom =
      (rhs k sX sP i hi).comp (vectorBundleEquiv k sX).toAddMonoidHom :=
    VectorBundleKZero.addHom_ext fun M hM ↦ by
      have := Stacks.StalkFreeBridge.isFiniteLocallyFree_of_finiteLocallyFree M (hM := hM)
      simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
      exact h M
  have := DFunLike.congr_fun hφψ ((vectorBundleEquiv k sX).symm α)
  simpa only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.apply_symm_apply] using this

/-- The formula only depends on the morphism, not on how it is written. -/
theorem closedImmersionFormula_congr {f : X ⟶ P} [IsClosedImmersion f] (hfi : f = i)
    (hf : f ≫ sP = sX) (h : ClosedImmersionFormula k sX sP f hf) :
    ClosedImmersionFormula k sX sP i hi := by
  subst hfi
  exact h

end Sides

theorem cap_zero (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] : cap k sX 0 = 0 := by
  simp only [cap, map_zero]

theorem cap_one (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] : cap k sX 1 = 1 :=
  totalRationalChowCap_one (fieldChowSituation k) sX

/-! ### Composites -/

section Composition

variable (k : Type u) [Field k] {X P Q : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sP : P ⟶ Spec (.of k)) (sQ : Q ⟶ Spec (.of k)) [IsSmoothFT k sX] [IsSmoothFT k sP]
  [IsSmoothFT k sQ] (i : X ⟶ P) [IsClosedImmersion i] (j : P ⟶ Q) [IsClosedImmersion j]
  (hi : i ≫ sP = sX) (hj : j ≫ sQ = sP)

include hj in
/-- **Normal classes of a composite**: `td(N_{X/Q})⁻¹ = i^* td(N_{P/Q})⁻¹ · td(N_{X/P})⁻¹`, from
`td(T_X) = i^* td(T_P) · td(N_{X/P})⁻¹` for `i`, `j` and `i ≫ j`. -/
theorem toddClass_neg_normalClass_comp :
    toddClass (fieldChowSituation k) sX (-normalClass k sQ (i ≫ j)) =
      pullbackAQ (fieldChowSituation k) sX sP i hi
          (toddClass (fieldChowSituation k) sP (-normalClass k sQ j)) *
        toddClass (fieldChowSituation k) sX (-normalClass k sP i) := by
  have hij : (i ≫ j) ≫ sQ = sX := by rw [Category.assoc, hj, hi]
  have hA : pullbackAQ (fieldChowSituation k) sX sQ (i ≫ j) hij (toddTangent k sQ) =
      pullbackAQ (fieldChowSituation k) sX sP i hi
        (pullbackAQ (fieldChowSituation k) sP sQ j hj (toddTangent k sQ)) := by
    rw [toddTangent, pullbackAQ_toddClass, pullbackAQ_toddClass, pullbackAQ_toddClass,
      VectorBundleKZero.pullback_eq_pullbackRingHom, VectorBundleKZero.pullback_eq_pullbackRingHom,
      VectorBundleKZero.pullback_eq_pullbackRingHom, VectorBundleKZero.pullbackRingHom_comp_apply]
  have hu : IsUnit (pullbackAQ (fieldChowSituation k) sX sQ (i ≫ j) hij (toddTangent k sQ)) := by
    rw [toddTangent, pullbackAQ_toddClass]
    exact isUnit_toddClass _ _ _
  refine hu.mul_left_cancel ?_
  rw [← toddTangent_eq k sX sQ (i ≫ j) hij, toddTangent_eq k sX sP i hi,
    toddTangent_eq k sP sQ j hj, map_mul, hA, mul_assoc]

/-- `(i ≫ j)_*((ch α · td(N_{X/Q})⁻¹) ∩ [X])
  = j_*(td(N_{P/Q})⁻¹ ∩ i_*((ch α · td(N_{X/P})⁻¹) ∩ [X]))`. -/
theorem rhs_comp (hij : (i ≫ j) ≫ sQ = sX) (α : CoherentKZero X) :
    rhs k sX sQ (i ≫ j) hij α =
      rationalProperChowPushforward (fieldChowSituation k) sP sQ hj
        (cap k sP (toddClass (fieldChowSituation k) sP (-normalClass k sQ j))
          (rhs k sX sP i hi α)) := by
  have hcomm : Commute (chK k sX α) (pullbackAQ (fieldChowSituation k) sX sP i hi
      (toddClass (fieldChowSituation k) sP (-normalClass k sQ j))) := by
    rw [chK_eq_ch, pullbackAQ_toddClass]
    exact (commute_toddClass_ch _ _ _ _).symm
  rw [rhs_apply, rhs_apply, rationalProperChowPushforward_comp k sX sP sQ i j hi hj hij,
    toddClass_neg_normalClass_comp k sX sP sQ i j hi hj, ← mul_assoc, hcomm.eq, mul_assoc,
    cap_mul k sX (pullbackAQ (fieldChowSituation k) sX sP i hi
      (toddClass (fieldChowSituation k) sP (-normalClass k sQ j))), Module.End.mul_apply,
    rationalProperChowPushforward_cap_pullbackAQ k sX sP i hi]

/-- `j_*((ch(i_! α) · td(N_{P/Q})⁻¹) ∩ [P]) = j_*(td(N_{P/Q})⁻¹ ∩ (ch(i_! α) ∩ [P]))`. -/
theorem rhs_pushforwardK [IsLocallyNoetherian P] [CompactSpace P] (α : CoherentKZero X) :
    rhs k sP sQ j hj (pushforwardK i α) =
      rationalProperChowPushforward (fieldChowSituation k) sP sQ hj
        (cap k sP (toddClass (fieldChowSituation k) sP (-normalClass k sQ j))
          (lhs k sP i α)) := by
  have hcomm : Commute (chK k sP (pushforwardK i α))
      (toddClass (fieldChowSituation k) sP (-normalClass k sQ j)) := by
    rw [chK_eq_ch]
    exact (commute_toddClass_ch _ _ _ _).symm
  rw [rhs_apply, lhs_apply, hcomm.eq, cap_mul, Module.End.mul_apply]

theorem lhs_comp [IsLocallyNoetherian P] [CompactSpace P] (α : CoherentKZero X) :
    lhs k sQ (i ≫ j) α = lhs k sQ j (pushforwardK i α) := by
  have := compactSpace k sQ
  have : IsLocallyNoetherian Q := (isNoetherian k sQ).toIsLocallyNoetherian
  rw [lhs_apply, lhs_apply, pushforwardK_comp_of_isClosedImmersion i j, AddMonoidHom.comp_apply]

/-- With the formula for `i`, the right side of `j` at `i_! α` is the right side of `i ≫ j`. -/
theorem rhs_pushforwardK_eq [IsLocallyNoetherian P] [CompactSpace P]
    (hij : (i ≫ j) ≫ sQ = sX) (hI : ClosedImmersionFormula k sX sP i hi) (α : CoherentKZero X) :
    rhs k sP sQ j hj (pushforwardK i α) = rhs k sX sQ (i ≫ j) hij α := by
  rw [rhs_pushforwardK, lhs_eq_rhs k sX sP i hi hI α, rhs_comp k sX sP sQ i j hi hj hij]

end Composition

end ClosedImmersionReduce

section Composition

open ClosedImmersionReduce

variable (k : Type u) [Field k] {X P Q : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sP : P ⟶ Spec (.of k)) (sQ : Q ⟶ Spec (.of k)) [IsSmoothFT k sX] [IsSmoothFT k sP]
  [IsSmoothFT k sQ] (i : X ⟶ P) [IsClosedImmersion i] (j : P ⟶ Q) [IsClosedImmersion j]
  (hi : i ≫ sP = sX) (hj : j ≫ sQ = sP)

/-- **The formula is stable under composition** of closed immersions of smooth schemes. -/
theorem closedImmersionFormula_comp (hij : (i ≫ j) ≫ sQ = sX)
    (hI : ClosedImmersionFormula k sX sP i hi) (hJ : ClosedImmersionFormula k sP sQ j hj) :
    ClosedImmersionFormula k sX sQ (i ≫ j) hij := by
  have := compactSpace k sP
  have : IsLocallyNoetherian P := (isNoetherian k sP).toIsLocallyNoetherian
  refine closedImmersionFormula_of_lhs_eq_rhs k sX sQ (i ≫ j) hij fun α ↦ ?_
  rw [lhs_comp, lhs_eq_rhs k sP sQ j hj hJ, rhs_pushforwardK_eq k sX sP sQ i j hi hj hij hI]

/-- **Cancellation**: the formula for `i ≫ j` and for `j` gives the one for `i`, when
`j_* : CH_*(P) ⊗ ℚ → CH_*(Q) ⊗ ℚ` is injective. -/
theorem closedImmersionFormula_of_comp (hij : (i ≫ j) ≫ sQ = sX)
    (hIJ : ClosedImmersionFormula k sX sQ (i ≫ j) hij) (hJ : ClosedImmersionFormula k sP sQ j hj)
    (hinj : Function.Injective (rationalProperChowPushforward (fieldChowSituation k) sP sQ hj)) :
    ClosedImmersionFormula k sX sP i hi := by
  have := compactSpace k sP
  have : IsLocallyNoetherian P := (isNoetherian k sP).toIsLocallyNoetherian
  refine closedImmersionFormula_of_lhs_eq_rhs k sX sP i hi fun α ↦ ?_
  have h1 := lhs_eq_rhs k sX sQ (i ≫ j) hij hIJ α
  rw [lhs_comp, lhs_eq_rhs k sP sQ j hj hJ, rhs_pushforwardK,
    rhs_comp k sX sP sQ i j hi hj hij] at h1
  have h3 := congrArg (cap k sP (toddClass (fieldChowSituation k) sP (normalClass k sQ j)))
    (hinj h1)
  have h4 : ∀ x, cap k sP (toddClass (fieldChowSituation k) sP (normalClass k sQ j))
      (cap k sP (toddClass (fieldChowSituation k) sP (-normalClass k sQ j)) x) = x := fun x ↦ by
    rw [← Module.End.mul_apply, ← cap_mul, toddClass_mul_toddClass_neg, cap_one,
      Module.End.one_apply]
  rwa [h4, h4] at h3

end Composition

namespace ClosedImmersionReduce

/-! ### Empty source -/

/-- Sections of a module over an open containing no point are trivial. -/
theorem subsingleton_sections {X : Scheme.{u}} (M : X.Modules) (O : X.Opens)
    (hO : ∀ x : X, x ∉ O) : Subsingleton Γ(M, O) :=
  ⟨fun _ _ ↦ (Scheme.Modules.isSheaf M).section_ext (U := Opposite.op O)
    fun x hx ↦ absurd hx (hO x)⟩

theorem isZero_of_isEmpty {X : Scheme.{u}} [IsEmpty X] (M : X.Modules) : IsZero M := by
  refine (IsZero.iff_id_eq_zero _).2 (Scheme.Modules.hom_ext _ _ fun T ↦ ?_)
  have hs : Subsingleton Γ(M, T) := subsingleton_sections M T fun x ↦ isEmptyElim x
  ext s
  exact @Subsingleton.elim _ hs _ _

/-- The formula holds trivially for an empty source. -/
theorem closedImmersionFormula_of_isEmpty (k : Type u) [Field k] {X P : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sP : P ⟶ Spec (.of k)) [IsSmoothFT k sX] [IsSmoothFT k sP]
    (i : X ⟶ P) [IsClosedImmersion i] (hi : i ≫ sP = sX) [IsEmpty X] :
    ClosedImmersionFormula k sX sP i hi := by
  refine (closedImmersionFormula_iff k sX sP i hi).2 (KZero.hom_ext fun F ↦ ?_)
  have hF : IsZero F :=
    IsZero.of_full_of_faithful_of_isZero (coherentInclusion X) F (isZero_of_isEmpty F.obj)
  rw [KZero.mk_eq_zero_of_isZero hF, map_zero, map_zero]

/-! ### Open and closed pieces -/

section Clopen

variable (k : Type u) [Field k]

/-- An open and closed subscheme of a smooth scheme is smooth. -/
theorem isSmoothFT_ι {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsSmoothFT k sY] (V : Y.Opens)
    [IsClosedImmersion V.ι] : IsSmoothFT k (V.ι ≫ sY) where
  smooth := inferInstance
  isSeparated := inferInstance
  quasiCompact := by
    have := compactSpace k sY
    have hV : IsClosed (V : Set Y) := by
      have := V.ι.isClosedEmbedding.isClosed_range
      rwa [Scheme.Opens.range_ι] at this
    have : CompactSpace V := isCompact_iff_compactSpace.mp hV.isCompact
    exact (quasiCompact_iff_compactSpace (V.ι ≫ sY)).mpr this

/-- The normal class of an open and closed immersion vanishes: `td(N)⁻¹ = 1`. -/
theorem toddClass_neg_normalClass_of_isOpenImmersion {Z Y : Scheme.{u}} (sZ : Z ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k)) [IsSmoothFT k sZ] [IsSmoothFT k sY] (f : Z ⟶ Y) [IsOpenImmersion f]
    [IsClosedImmersion f] (hf : f ≫ sY = sZ) :
    toddClass (fieldChowSituation k) sZ (-normalClass k sY f) = 1 := by
  have hsm : Smooth (f ≫ sY) := by rw [hf]; infer_instance
  have hS := Stacks.ConormalSequenceRight.conormalShortComplex_shortExact f sY hsm
  have hg : IsIso (Stacks.ConormalSequenceRight.conormalShortComplex f sY).g :=
    Scheme.Hom.isIso_relativeDifferentialsMap_of_isOpenImmersion f sY (f ≫ sY) (𝟙 _) (by simp)
  have hz : IsZero (conormalSheaf k sY f) := hS.isIso_g_iff.mp hg
  have hC := isFiniteLocallyFree_conormalSheaf k sZ sY f hf
  have hcl : VectorBundleKZero.classOf Z (conormalSheaf k sY f) = 0 := by
    rw [VectorBundleKZero.classOf_eq_of_iso hz.isoZero
      (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree _),
      VectorBundleKZero.classOf_zero]
  have hch : ch (fieldChowSituation k) sZ (normalClass k sY f) = 0 := by
    rw [normalClass, normalSheaf, ch_classOf_dualSheaf, hcl, map_zero]
    refine RationalTotalChowClass.ext fun n ↦ ?_
    rw [chowGraded_weight_apply, RationalTotalChowClass.zero_apply, smul_zero]
  rw [toddClass, map_neg, hch, neg_zero, GradedComplete.toddOf_zero]

/-- On a Noetherian scheme `[T] = ∑_{n ∈ S} 1 ⊗ [T]_n` for any finite set `S` of degrees
containing those of the irreducible components. -/
theorem rationalFundamentalClass_eq_sum_of_subset (C : ChowSituation.{u}) {T : Scheme.{u}}
    (sT : T ⟶ C.S) [LocallyOfFiniteType sT] [IsNoetherian T] (S : Finset ℤ)
    (hS : (fundamentalClassDegrees_finite C sT).toFinset ⊆ S) :
    rationalFundamentalClass C sT = ∑ n ∈ S, DirectSum.of (fun j : ℤ ↦ ℚ ⊗[ℤ] chowGroup C sT j) n
      ((1 : ℚ) ⊗ₜ fundamentalChowClass C sT n) := by
  rw [rationalFundamentalClass_eq]
  refine Finset.sum_subset hS fun n _ hn ↦ ?_
  rw [fundamentalChowClass, fundamentalCycle_eq_zero_of_notMem_fundamentalClassDegrees C sT
    fun h ↦ hn ((fundamentalClassDegrees_finite C sT).mem_toFinset.2 h), map_zero,
    TensorProduct.tmul_zero, map_zero]

/-- **The fundamental cycle of a disjoint union**: `[Y]_n = V_*[V]_n + W_*[W]_n` in `A_n(Y)` for a
decomposition `Y = V ⊔ W` into open and closed subschemes. -/
theorem fundamentalChowClass_eq_add (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (V W : Y.Opens) (hVW : Disjoint (V : Set Y) W)
    (hcov : (V : Set Y) ∪ W = Set.univ) [IsClosedImmersion V.ι] [IsClosedImmersion W.ι] (n : ℤ) :
    fundamentalChowClass C sY n =
      properChowPushforward C (V.ι ≫ sY) sY V.ι rfl n (properPushforwardDescends C _ _ _ _ _)
          (fundamentalChowClass C (V.ι ≫ sY) n) +
        properChowPushforward C (W.ι ≫ sY) sY W.ι rfl n (properPushforwardDescends C _ _ _ _ _)
          (fundamentalChowClass C (W.ι ≫ sY) n) := by
  rw [fundamentalChowClass, fundamentalChowClass, fundamentalChowClass, properChowPushforward_mk,
    properChowPushforward_mk, ← map_add, properPushforward_fundamentalCycle_of_isClosedImmersion,
    properPushforward_fundamentalCycle_of_isClosedImmersion]
  congr 1
  exact cycleAssociatedToClosedSubscheme_eq_add_of_isOpenImmersion_pieces C sY (𝟙 Y) V.ι W.ι V.ι
    W.ι (Category.comp_id _) (Category.comp_id _)
    (by rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]; exact hVW)
    (by rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]; exact hcov) n

/-- **The fundamental class of a disjoint union**: `[Y] = V_*[V] + W_*[W]` in `CH_*(Y) ⊗ ℚ`. -/
theorem fundamentalClass_eq_add {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsSmoothFT k sY]
    (V W : Y.Opens) (hVW : Disjoint (V : Set Y) W) (hcov : (V : Set Y) ∪ W = Set.univ)
    [IsClosedImmersion V.ι] [IsClosedImmersion W.ι] :
    haveI := isSmoothFT_ι k sY V
    haveI := isSmoothFT_ι k sY W
    fundamentalClass k sY =
      rationalProperChowPushforward (fieldChowSituation k) (V.ι ≫ sY) sY rfl
          (fundamentalClass k (V.ι ≫ sY)) +
        rationalProperChowPushforward (fieldChowSituation k) (W.ι ≫ sY) sY rfl
          (fundamentalClass k (W.ι ≫ sY)) := by
  have := isSmoothFT_ι k sY V
  have := isSmoothFT_ι k sY W
  have := isNoetherian k sY
  have := isNoetherian k (V.ι ≫ sY)
  have := isNoetherian k (W.ι ≫ sY)
  obtain ⟨S, h1, h2, h3⟩ : ∃ S : Finset ℤ,
      (fundamentalClassDegrees_finite (fieldChowSituation k) sY).toFinset ⊆ S ∧
      (fundamentalClassDegrees_finite (fieldChowSituation k) (V.ι ≫ sY)).toFinset ⊆ S ∧
      (fundamentalClassDegrees_finite (fieldChowSituation k) (W.ι ≫ sY)).toFinset ⊆ S :=
    ⟨_ ∪ _ ∪ _, Finset.subset_union_left.trans Finset.subset_union_left,
      Finset.subset_union_right.trans Finset.subset_union_left, Finset.subset_union_right⟩
  simp only [fundamentalClass]
  rw [rationalFundamentalClass_eq_sum_of_subset (fieldChowSituation k) sY S h1,
    rationalFundamentalClass_eq_sum_of_subset (fieldChowSituation k) (V.ι ≫ sY) S h2,
    rationalFundamentalClass_eq_sum_of_subset (fieldChowSituation k) (W.ι ≫ sY) S h3, map_sum,
    map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [rationalProperChowPushforward_of_tmul (fieldChowSituation k) (V.ι ≫ sY) sY rfl,
    rationalProperChowPushforward_of_tmul (fieldChowSituation k) (W.ι ≫ sY) sY rfl,
    fundamentalChowClass_eq_add (fieldChowSituation k) sY V W hVW hcov n, TensorProduct.tmul_add,
    map_add]

/-- The restriction of `V_* M` to `V` is `M`. -/
def restrictPushforwardIso {Y : Scheme.{u}} (V : Y.Opens) (M : (V : Scheme.{u}).Modules) :
    (Scheme.Modules.restrictFunctor V.ι).obj ((Scheme.Modules.pushforward V.ι).obj M) ≅ M :=
  (Scheme.Modules.restrictFunctorAdjCounitIso V.ι).app M

/-- **`V_* M` vanishes on a disjoint open `W`.** -/
theorem isZero_restrict_pushforward {Y : Scheme.{u}} {V W : Y.Opens} (h : Disjoint V W)
    (M : (V : Scheme.{u}).Modules) :
    IsZero ((Scheme.Modules.restrictFunctor W.ι).obj ((Scheme.Modules.pushforward V.ι).obj M)) := by
  refine (IsZero.iff_id_eq_zero _).2 (Scheme.Modules.hom_ext _ _ fun T ↦ ?_)
  have hs : Subsingleton Γ(M, V.ι ⁻¹ᵁ (W.ι ''ᵁ T)) := subsingleton_sections M _ fun x hx ↦ by
    obtain ⟨t, -, ht⟩ := hx
    have h1 : V.ι x ∈ (W : Set Y) := by rw [← ht, ← Scheme.Opens.range_ι]; exact ⟨t, rfl⟩
    have h2 : V.ι x ∈ (V : Set Y) := by rw [← Scheme.Opens.range_ι]; exact ⟨x, rfl⟩
    exact h.le_bot (show V.ι x ∈ V ⊓ W from ⟨h2, h1⟩)
  ext s
  exact @Subsingleton.elim _ hs _ _

/-- **`V_* F` is finite locally free** for `F` finite locally free and `V` open and closed. -/
theorem isFiniteLocallyFree_pushforward_ι {Y : Scheme.{u}} (V : Y.Opens)
    (hV : IsClosed (V : Set Y)) (F : (V : Scheme.{u}).Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pushforward V.ι).obj F) := by
  let W : Y.Opens := ⟨(V : Set Y)ᶜ, hV.isOpen_compl⟩
  have hVW : Disjoint V W := by
    rw [disjoint_iff]
    ext x
    simp [W]
  refine Stacks.Modules.isFiniteLocallyFree_localGenerators_of_iSup_eq_top _
    (fun b : Bool ↦ Bool.rec W V b) ?_ fun b ↦ ?_
  · rw [iSup_bool_eq]
    ext x
    simp [W]
  · cases b
    · have := isFiniteLocallyFreeOfRank_zero_of_isZero (isZero_restrict_pushforward hVW F)
      exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 0
    · exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso
        (restrictPushforwardIso V F).symm

end Clopen

end ClosedImmersionReduce

section OpenClosed

open ClosedImmersionReduce

variable (k : Type u) [Field k]

/-- **R1: the formula for an open and closed immersion** `V ⟶ Y` of a smooth scheme. -/
theorem closedImmersionFormula_ι {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsSmoothFT k sY]
    (V : Y.Opens) [IsClosedImmersion V.ι] :
    haveI := isSmoothFT_ι k sY V
    ClosedImmersionFormula k (V.ι ≫ sY) sY V.ι rfl := by
  have := isSmoothFT_ι k sY V
  have hV : IsClosed (V : Set Y) := by
    have := V.ι.isClosedEmbedding.isClosed_range
    rwa [Scheme.Opens.range_ι] at this
  let W : Y.Opens := ⟨(V : Set Y)ᶜ, hV.isOpen_compl⟩
  have : IsClosedImmersion W.ι := IsClosedImmersion.of_isPreimmersion W.ι
    (by rw [Scheme.Opens.range_ι]; exact V.isOpen.isClosed_compl)
  have := isSmoothFT_ι k sY W
  have := compactSpace k sY
  have : IsLocallyNoetherian Y := (isNoetherian k sY).toIsLocallyNoetherian
  have hVW : Disjoint V W := by
    rw [disjoint_iff]
    ext x
    simp [W]
  refine closedImmersionFormula_of_bundles k (V.ι ≫ sY) sY V.ι rfl fun F hF ↦ ?_
  have := isFiniteLocallyFree_pushforward_ι V hV F
  have hθ : vectorBundleEquiv k sY
      (VectorBundleKZero.classOf Y ((Scheme.Modules.pushforward V.ι).obj F)) =
      pushforwardK V.ι (vectorBundleEquiv k (V.ι ≫ sY) (VectorBundleKZero.classOf V F)) := by
    obtain ⟨cF, hF'⟩ := vectorBundleEquiv_classOf k (V.ι ≫ sY) F
      (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree F)
    obtain ⟨cG, hG'⟩ := vectorBundleEquiv_classOf k sY ((Scheme.Modules.pushforward V.ι).obj F)
      (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree _)
    rw [hF', hG', pushforwardK_mk_of_isClosedImmersion]
    rfl
  have hzW : IsZero ((Scheme.Modules.pullback W.ι).obj ((Scheme.Modules.pushforward V.ι).obj F)) :=
    (isZero_restrict_pushforward hVW F).of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app _).symm
  have hV' : VectorBundleKZero.classOf V
      ((Scheme.Modules.pullback V.ι).obj ((Scheme.Modules.pushforward V.ι).obj F)) =
      VectorBundleKZero.classOf V F :=
    VectorBundleKZero.classOf_eq_of_iso
      (((Scheme.Modules.restrictFunctorIsoPullback V.ι).app _).symm ≪≫ restrictPushforwardIso V F)
      (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree _)
  have hW' : VectorBundleKZero.classOf W
      ((Scheme.Modules.pullback W.ι).obj ((Scheme.Modules.pushforward V.ι).obj F)) = 0 := by
    rw [VectorBundleKZero.classOf_eq_of_iso hzW.isoZero
      (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree _),
      VectorBundleKZero.classOf_zero]
  rw [← hθ, chK_vectorBundleEquiv,
    toddClass_neg_normalClass_of_isOpenImmersion k (V.ι ≫ sY) sY V.ι rfl, mul_one,
    fundamentalClass_eq_add k sY V W disjoint_compl_right (Set.union_compl_self _), map_add,
    ← rationalProperChowPushforward_cap_pullbackAQ k (V.ι ≫ sY) sY V.ι rfl,
    ← rationalProperChowPushforward_cap_pullbackAQ k (W.ι ≫ sY) sY W.ι rfl,
    pullbackAQ_ch (fieldChowSituation k) (V.ι ≫ sY) sY V.ι rfl,
    pullbackAQ_ch (fieldChowSituation k) (W.ι ≫ sY) sY W.ι rfl,
    VectorBundleKZero.pullback_classOf V.ι, VectorBundleKZero.pullback_classOf W.ι, hV', hW',
    map_zero, cap_zero, LinearMap.zero_apply, map_zero, add_zero]

end OpenClosed

namespace ClosedImmersionReduce

/-! ### Finite decompositions of the source -/

section Decomposition

/-- In a biproduct whose other summands vanish, the projection to the remaining one is an
isomorphism. -/
theorem isIso_biproduct_π_of_isZero {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] {ι : Type}
    [Fintype ι] (f : ι → 𝒞) [HasBiproduct f] (b : ι) (h : ∀ a, a ≠ b → IsZero (f a)) :
    IsIso (biproduct.π f b) := by
  classical
  refine ⟨⟨biproduct.ι f b, ?_, biproduct.ι_π_self f b⟩⟩
  rw [← biproduct.total, Finset.sum_eq_single b
    (fun a _ hab ↦ by rw [(h a hab).eq_of_tgt (biproduct.π f a) 0, zero_comp])
    (fun hb ↦ absurd (Finset.mem_univ b) hb)]

/-- A biproduct over `Option α` splits off its summand at `none`. -/
def biproductOptionIso {𝒜 : Type*} [Category 𝒜] [Preadditive 𝒜] [HasFiniteBiproducts 𝒜]
    {α : Type} [Fintype α] (f : Option α → 𝒜) :
    (⨁ f) ≅ f none ⊞ (⨁ fun a : α ↦ f (some a)) where
  hom := biproduct.desc fun x ↦ match x with
    | none => biprod.inl
    | some a => biproduct.ι (fun a : α ↦ f (some a)) a ≫ biprod.inr
  inv := biprod.desc (biproduct.ι f none) (biproduct.desc fun a ↦ biproduct.ι f (some a))
  hom_inv_id := by
    refine biproduct.hom_ext' _ _ fun x ↦ ?_
    cases x <;> simp
  inv_hom_id := by
    refine biprod.hom_ext' _ _ (by simp) (biproduct.hom_ext' _ _ fun a ↦ by simp)

/-- **The class of a finite biproduct is the sum of the classes of its summands.** -/
theorem kZero_mk_biproduct {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasFiniteBiproducts 𝒜]
    (α : Type) [Fintype α] (f : α → 𝒜) : KZero.mk 𝒜 (⨁ f) = ∑ a, KZero.mk 𝒜 (f a) := by
  classical
  refine Fintype.induction_empty_option
    (P := fun α _ ↦ ∀ f : α → 𝒜, KZero.mk 𝒜 (⨁ f) = ∑ a, KZero.mk 𝒜 (f a)) ?_ ?_ ?_ α f
  · intro α β _ e h g
    let : Fintype α := Fintype.ofEquiv β e.symm
    calc KZero.mk 𝒜 (⨁ g) = KZero.mk 𝒜 (⨁ fun a ↦ g (e a)) :=
          (KZero.mk_eq_of_iso (biproduct.whiskerEquiv e fun a ↦ Iso.refl (g (e a)))).symm
      _ = ∑ a, KZero.mk 𝒜 (g (e a)) := h _
      _ = ∑ b, KZero.mk 𝒜 (g b) := Fintype.sum_equiv e _ _ fun _ ↦ rfl
  · intro f
    have hz : IsZero (⨁ f) := by
      rw [IsZero.iff_id_eq_zero]
      ext j
      exact j.elim
    rw [KZero.mk_eq_zero_of_isZero hz, Finset.univ_eq_empty, Finset.sum_empty]
  · intro α _ h f
    rw [KZero.mk_eq_of_iso (biproductOptionIso f),
      KZero.mk_of_splitting (ShortComplex.Splitting.ofHasBinaryBiproduct _ _), h,
      Fintype.sum_option]

variable {X : Scheme.{u}} {ι : Type} [Fintype ι] (U : ι → X.Opens) (hU : IsClopenDecomposition U)
include hU

/-- **A module is the sum of its parts on a finite clopen decomposition**:
`M ≅ ⨁_a (U a)_*(M|_{U a})`, by the units of restriction ⊣ pushforward. -/
theorem isIso_biproductLift_unit (M : X.Modules) :
    IsIso (biproduct.lift fun a ↦ (Scheme.Modules.restrictAdjunction (U a).ι).unit.app M) := by
  classical
  refine Scheme.Modules.isIso_of_isIso_restrictFunctor_map _ (fun a ↦ (U a).ι) (fun x ↦ ?_)
    fun b ↦ ?_
  · obtain ⟨a, ha⟩ := hU.exists_mem x
    exact ⟨a, ⟨x, ha⟩, rfl⟩
  · let R := Scheme.Modules.restrictFunctor (U b).ι
    let G : ι → X.Modules := fun a ↦
      (Scheme.Modules.pushforward (U a).ι).obj ((Scheme.Modules.restrictFunctor (U a).ι).obj M)
    let v : ∀ a, M ⟶ G a := fun a ↦ (Scheme.Modules.restrictAdjunction (U a).ι).unit.app M
    have hcomp : R.map (biproduct.lift v) ≫ (R.mapBiproduct G).hom =
        biproduct.lift fun a ↦ R.map (v a) := by
      ext a
      dsimp only [Function.comp_def]
      simp only [Functor.mapBiproduct_hom, Category.assoc, biproduct.lift_π, ← R.map_comp]
    have hb : IsIso (R.map (v b)) := by
      have : IsIso (R.map (v b) ≫
          (Scheme.Modules.restrictAdjunction (U b).ι).counit.app (R.obj M)) := by
        rw [(Scheme.Modules.restrictAdjunction (U b).ι).left_triangle_components M]
        infer_instance
      exact IsIso.of_isIso_comp_right _
        ((Scheme.Modules.restrictAdjunction (U b).ι).counit.app (R.obj M))
    have hπ : IsIso (biproduct.π (fun a ↦ R.obj (G a)) b) :=
      isIso_biproduct_π_of_isZero _ b fun a hab ↦
        isZero_restrict_pushforward (hU.disjoint a b hab) _
    have hl : IsIso (biproduct.lift fun a ↦ R.map (v a)) := by
      have : IsIso ((biproduct.lift fun a ↦ R.map (v a)) ≫
          biproduct.π (fun a ↦ R.obj (G a)) b) := by
        rw [biproduct.lift_π]
        exact hb
      exact IsIso.of_isIso_comp_right _ (biproduct.π (fun a ↦ R.obj (G a)) b)
    have heq : R.map (biproduct.lift v) =
        (biproduct.lift fun a ↦ R.map (v a)) ≫ (R.mapBiproduct G).inv := by
      rw [← hcomp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    change IsIso (R.map (biproduct.lift v))
    rw [heq]
    infer_instance

/-- **`θ[E] = ∑_a (U a)_! θ[E|_{U a}]`** in `K'₀(X)` for a finite clopen decomposition. -/
theorem vectorBundleEquiv_classOf_eq_sum (k : Type u) [Field k] (sX : X ⟶ Spec (.of k))
    [IsSmoothFT k sX] [∀ a, IsClosedImmersion (U a).ι] [∀ a, IsSmoothFT k ((U a).ι ≫ sX)]
    (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    haveI := compactSpace k sX
    haveI : IsLocallyNoetherian X := (isNoetherian k sX).toIsLocallyNoetherian
    vectorBundleEquiv k sX (VectorBundleKZero.classOf X E) =
      ∑ a, pushforwardK (U a).ι (vectorBundleEquiv k ((U a).ι ≫ sX)
        (VectorBundleKZero.classOf (U a) ((Scheme.Modules.restrictFunctor (U a).ι).obj E))) := by
  have hbC : HasFiniteBiproducts (Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) :=
    Abelian.hasFiniteBiproducts
  have := compactSpace k sX
  have : IsLocallyNoetherian X := (isNoetherian k sX).toIsLocallyNoetherian
  have hEa : ∀ a, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.restrictFunctor (U a).ι).obj E) := fun a ↦
    have := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme (U a).ι E
      inferInstance
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback (U a).ι).app E).symm
  obtain ⟨cE, hθE⟩ := vectorBundleEquiv_classOf k sX E
    (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree E)
  have hpiece : ∀ a, ∃ c : Stacks.SheafOfModules.IsCoherent
      ((Scheme.Modules.restrictFunctor (U a).ι).obj E),
      vectorBundleEquiv k ((U a).ι ≫ sX)
        (VectorBundleKZero.classOf (U a) ((Scheme.Modules.restrictFunctor (U a).ι).obj E)) =
      KZero.mk (Stacks.SheafOfModules.CoherentModules (U a).toScheme.ringCatSheaf)
        ⟨(Scheme.Modules.restrictFunctor (U a).ι).obj E, c⟩ := fun a ↦
    vectorBundleEquiv_classOf k ((U a).ι ≫ sX) _
      (@Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree _ _ (hEa a))
  choose c hc using hpiece
  let f : ι → Stacks.SheafOfModules.CoherentModules X.ringCatSheaf := fun a ↦
    (pushforwardCoherentModules (U a).ι).obj ⟨(Scheme.Modules.restrictFunctor (U a).ι).obj E, c a⟩
  have hf : ∀ a, pushforwardK (U a).ι (vectorBundleEquiv k ((U a).ι ≫ sX)
      (VectorBundleKZero.classOf (U a) ((Scheme.Modules.restrictFunctor (U a).ι).obj E))) =
      KZero.mk _ (f a) := fun a ↦ by
    rw [hc a, pushforwardK_mk_of_isClosedImmersion]
  rw [hθE, Finset.sum_congr rfl fun a _ ↦ hf a, ← kZero_mk_biproduct]
  refine KZero.mk_eq_of_iso ?_
  have hiso := isIso_biproductLift_unit U hU E
  let incl := ObjectProperty.ι (Stacks.SheafOfModules.coherentModules X.ringCatSheaf)
  exact incl.preimageIso (@asIso _ _ _ _ _ hiso ≪≫ (incl.mapBiproduct f).symm)

end Decomposition

/-- Only finitely many pieces of a clopen decomposition of a quasi-compact scheme are nonempty. -/
theorem exists_finset_eq_bot {X : Scheme.{u}} [CompactSpace X] {U : ℕ → X.Opens}
    (hU : IsClopenDecomposition U) : ∃ S : Finset ℕ, ∀ n ∉ S, U n = ⊥ := by
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun n ↦ (U n : Set X))
    (fun n ↦ (U n).isOpen) fun x _ ↦ by
      obtain ⟨n, hn⟩ := hU.exists_mem x
      exact Set.mem_iUnion.2 ⟨n, hn⟩
  refine ⟨S, fun n hn ↦ eq_bot_iff.2 fun x hx ↦ ?_⟩
  obtain ⟨m, hm, hxm⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ x))
  rw [hU.eq_of_mem hx hxm] at hn
  exact absurd hm hn

/-- The nonempty pieces of a clopen decomposition still decompose the scheme. -/
theorem isClopenDecomposition_subtype {X : Scheme.{u}} {U : ℕ → X.Opens}
    (hU : IsClopenDecomposition U) (S : Finset ℕ) (hS : ∀ n ∉ S, U n = ⊥) :
    IsClopenDecomposition fun a : S ↦ U a where
  disjoint a b hab := hU.disjoint a b fun h ↦ hab (Subtype.ext h)
  iSup_eq_top := by
    refine eq_top_iff.2 fun x _ ↦ ?_
    obtain ⟨n, hn⟩ := hU.exists_mem x
    have hnS : n ∈ S := by
      by_contra h
      rw [hS n h] at hn
      exact hn
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨n, hnS⟩, hn⟩

end ClosedImmersionReduce

section Decomposition

open ClosedImmersionReduce

variable (k : Type u) [Field k] {X P : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sP : P ⟶ Spec (.of k)) [IsSmoothFT k sX] [IsSmoothFT k sP] (i : X ⟶ P) [IsClosedImmersion i]
  (hi : i ≫ sP = sX)

/-- **R2 for the source, finite form**: the formula for `i` follows from the formulas for its
restrictions to the pieces of a finite decomposition of `X` into open and closed subschemes. -/
theorem closedImmersionFormula_of_isClopenDecomposition_fintype {ι : Type} [Fintype ι]
    (U : ι → X.Opens) (hU : IsClopenDecomposition U) [∀ a, IsClosedImmersion (U a).ι]
    [∀ a, IsSmoothFT k ((U a).ι ≫ sX)]
    (h : ∀ a, ClosedImmersionFormula k ((U a).ι ≫ sX) sP ((U a).ι ≫ i)
      (by rw [Category.assoc, hi])) :
    ClosedImmersionFormula k sX sP i hi := by
  have := compactSpace k sX
  have : IsLocallyNoetherian X := (isNoetherian k sX).toIsLocallyNoetherian
  refine closedImmersionFormula_of_lhs_eq_rhs_bundles k sX sP i hi fun E hE ↦ ?_
  rw [vectorBundleEquiv_classOf_eq_sum U hU k sX E, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [← lhs_comp, rhs_pushforwardK_eq k ((U a).ι ≫ sX) sX sP (U a).ι i rfl hi
    (by rw [Category.assoc, hi]) (closedImmersionFormula_ι k sX (U a))]
  exact lhs_eq_rhs k _ sP _ _ (h a) _

/-- **R2 for the source**: the formula for `i` follows from the formulas for its restrictions to
the pieces of a decomposition of `X` into open and closed subschemes indexed by `ℕ` (only finitely
many pieces are nonempty, `X` being quasi-compact). -/
theorem closedImmersionFormula_of_isClopenDecomposition (U : ℕ → X.Opens)
    (hU : IsClopenDecomposition U)
    (h : ∀ n, haveI := hU.isClosedImmersion_ι n
      haveI := isSmoothFT_ι k sX (U n)
      ClosedImmersionFormula k ((U n).ι ≫ sX) sP ((U n).ι ≫ i) (by rw [Category.assoc, hi])) :
    ClosedImmersionFormula k sX sP i hi := by
  have := compactSpace k sX
  obtain ⟨S, hS⟩ := exists_finset_eq_bot hU
  have : ∀ a : S, IsClosedImmersion (U a).ι := fun a ↦ hU.isClosedImmersion_ι a
  have : ∀ a : S, IsSmoothFT k ((U a).ι ≫ sX) := fun a ↦ isSmoothFT_ι k sX (U a)
  exact closedImmersionFormula_of_isClopenDecomposition_fintype k sX sP i hi (fun a : S ↦ U a)
    (isClopenDecomposition_subtype hU S hS) fun a ↦ h a

/-- **R2 for the target**: for an open and closed `W ⊆ P`, the formula for the restriction
`i⁻¹(W) ⟶ W` of `i` gives the one for `i⁻¹(W) ⟶ P`. -/
theorem closedImmersionFormula_of_restrict (W : P.Opens) [IsClosedImmersion W.ι]
    [IsClosedImmersion (i ⁻¹ᵁ W).ι]
    (h : haveI := isSmoothFT_ι k sX (i ⁻¹ᵁ W)
      haveI := isSmoothFT_ι k sP W
      ClosedImmersionFormula k ((i ⁻¹ᵁ W).ι ≫ sX) (W.ι ≫ sP) (i ∣_ W)
        (by rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hi])) :
    haveI := isSmoothFT_ι k sX (i ⁻¹ᵁ W)
    ClosedImmersionFormula k ((i ⁻¹ᵁ W).ι ≫ sX) sP ((i ⁻¹ᵁ W).ι ≫ i)
      (by rw [Category.assoc, hi]) := by
  have := isSmoothFT_ι k sX (i ⁻¹ᵁ W)
  have := isSmoothFT_ι k sP W
  exact closedImmersionFormula_congr k ((i ⁻¹ᵁ W).ι ≫ sX) sP ((i ⁻¹ᵁ W).ι ≫ i)
    (by rw [Category.assoc, hi]) (morphismRestrict_ι i W) _
    (closedImmersionFormula_comp k _ (W.ι ≫ sP) sP (i ∣_ W) W.ι
      (by rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hi]) rfl
      (by rw [Category.assoc, morphismRestrict_ι_assoc, hi]) h (closedImmersionFormula_ι k sP W))

end Decomposition

namespace ClosedImmersionReduce

/-! ### Pure dimension -/

/-- A smooth morphism of relative dimension `n` in the sense of Stacks 02NJ is smooth of relative
dimension `n` in the sense of Mathlib. -/
theorem smoothOfRelativeDimension_of_relativeDimension {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    [LocallyOfFiniteType f] (n : ℕ) (h : RelativeDimension f n) : SmoothOfRelativeDimension n f :=
  Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq f n
    ((relativeDimension_iff_forall_topologicalKrullDimAt f n).1 h)

/-- A morphism smooth of relative dimension `n` has relative dimension `n` (Stacks 02NJ). -/
theorem relativeDimension_of_smoothOfRelativeDimension {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
    [SmoothOfRelativeDimension n f] [LocallyOfFiniteType f] : RelativeDimension f n :=
  (relativeDimension_iff_forall_topologicalKrullDimAt f n).2
    (fiberDimensionAt_eq_of_smoothOfRelativeDimension f n)

/-- **The rank of the conormal sheaf is the codimension**: in the conormal sequence of a closed
immersion of smooth schemes of relative dimensions `m` and `n`, `n = r + m`. -/
theorem rank_add_conormal {X P S : Scheme.{u}} (i : X ⟶ P) [IsClosedImmersion i] (p : P ⟶ S)
    (n m r : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension m (i ≫ p)]
    [hr : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.Chow.conormalModule i) r] (x : X) : n = r + m := by
  have hS := Stacks.ConormalSequenceRight.conormalShortComplex_shortExact i p
    (SmoothOfRelativeDimension.smooth m (i ≫ p))
  have := Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials p n
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.ConormalSequenceRight.conormalShortComplex i p).X₁ r :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      (Stacks.ConormalSequenceUnramifiedPair.conormalSheafComparisonIso i).symm hr
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.ConormalSequenceRight.conormalShortComplex i p).X₂ n :=
    Stacks.Chow.GenuineChern.isFiniteLocallyFreeOfRank_pullback i _ n
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.ConormalSequenceRight.conormalShortComplex i p).X₃ m :=
    Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials (i ≫ p) m
  exact AlgebraicGeometry.SheafOfModules.rank_add_of_shortExact _ hS r n m x

/-- `ℙ¹_k ⟶ Spec k` is smooth of relative dimension one. -/
theorem smoothOfRelativeDimension_relativeProjectiveLine (k : Type u) [Field k] :
    SmoothOfRelativeDimension 1 (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) := by
  have := smooth_relativeProjectiveLine_over (Spec (.of k))
  exact smoothOfRelativeDimension_of_relativeDimension _ 1
    (Stacks.WeilCohomology.relativeDimension_relativeProjectiveLine_spec k)

/-- Proper pushforward along a morphism equal to the identity is the identity. -/
theorem rationalProperChowPushforward_of_eq_id (k : Type u) [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] {f : Y ⟶ Y} [IsProper f] (hf : f = 𝟙 Y)
    (hs : f ≫ sY = sY) (γ : CHQ k sY) :
    rationalProperChowPushforward (fieldChowSituation k) sY sY hs γ = γ := by
  subst hf
  have : rationalProperChowPushforward (fieldChowSituation k) sY sY hs = LinearMap.id := by
    refine rationalChowHomology_linearMap_ext (fieldChowSituation k) sY fun j q α ↦ ?_
    rw [rationalProperChowPushforward_of_tmul, properChowPushforward_id]
    rfl
  rw [this, LinearMap.id_apply]

end ClosedImmersionReduce

section CodimZero

open ClosedImmersionReduce

variable (k : Type u) [Field k]

/-- R3 with an abstract section: `π : Q ⟶ P` proper and smooth of relative dimension one with a
section `j` which is a closed immersion. -/
theorem closedImmersionFormula_of_section (hcore : CoreClosedImmersionFormula k)
    {X P Q : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sP : P ⟶ Spec (.of k)) [IsSmoothFT k sX]
    [IsSmoothFT k sP] (π : Q ⟶ P) [IsProper π] [SmoothOfRelativeDimension 1 π]
    [IsSmoothFT k (π ≫ sP)] (j : P ⟶ Q) [IsClosedImmersion j] (hjπ : j ≫ π = 𝟙 P)
    (i : X ⟶ P) [IsClosedImmersion i] (hi : i ≫ sP = sX) (n : ℕ)
    [SmoothOfRelativeDimension n sP] [SmoothOfRelativeDimension n sX] [Nonempty X] :
    ClosedImmersionFormula k sX sP i hi := by
  have hj : j ≫ π ≫ sP = sP := by rw [← Category.assoc, hjπ, Category.id_comp]
  have hij : (i ≫ j) ≫ π ≫ sP = sX := by rw [Category.assoc, hj, hi]
  have : Nonempty P := ⟨i (Classical.arbitrary X)⟩
  have : SmoothOfRelativeDimension n (j ≫ π ≫ sP) := by rw [hj]; infer_instance
  have : SmoothOfRelativeDimension n ((i ≫ j) ≫ π ≫ sP) := by rw [hij]; infer_instance
  have hrj : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.Chow.conormalModule j) 1 := by
    have := Stacks.Conormal.isFiniteLocallyFreeOfRank_conormalSheaf_of_smoothOfRelativeDimension j
      (π ≫ sP) (1 + n) n
    rwa [Nat.add_sub_cancel] at this
  have hrij : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.Chow.conormalModule (i ≫ j)) 1 := by
    have := Stacks.Conormal.isFiniteLocallyFreeOfRank_conormalSheaf_of_smoothOfRelativeDimension
      (i ≫ j) (π ≫ sP) (1 + n) n
    rwa [Nat.add_sub_cancel] at this
  have hJ : ClosedImmersionFormula k sP (π ≫ sP) j hj :=
    closedImmersionFormula_of_bundles k sP (π ≫ sP) j hj fun E _ ↦
      hcore sP (π ≫ sP) j hj (1 + n) n 1 le_rfl (Nat.add_comm 1 n) E
  have hIJ : ClosedImmersionFormula k sX (π ≫ sP) (i ≫ j) hij :=
    closedImmersionFormula_of_bundles k sX (π ≫ sP) (i ≫ j) hij fun E _ ↦
      hcore sX (π ≫ sP) (i ≫ j) hij (1 + n) n 1 le_rfl (Nat.add_comm 1 n) E
  refine closedImmersionFormula_of_comp k sX sP (π ≫ sP) i j hi hj hij hIJ hJ ?_
  have key : ∀ γ, rationalProperChowPushforward (fieldChowSituation k) (π ≫ sP) sP (f := π) rfl
      (rationalProperChowPushforward (fieldChowSituation k) sP (π ≫ sP) hj γ) = γ := fun γ ↦ by
    rw [← rationalProperChowPushforward_comp k sP (π ≫ sP) sP j π hj rfl
      (by rw [Category.assoc, hj])]
    exact rationalProperChowPushforward_of_eq_id k sP hjπ _ γ
  intro γ γ' h
  rw [← key γ, ← key γ', h]

/-- **R3: codimension zero.** For `X`, `P` smooth of the same pure relative dimension `n`, the
formula for `i` follows from the core case for the two closed immersions `X ⟶ 𝐏¹_P` and
`P ⟶ 𝐏¹_P` of codimension one through the zero section `j`, `j_*` being injective (`j` has the
proper retraction `𝐏¹_P ⟶ P`). -/
theorem closedImmersionFormula_of_codim_zero (hcore : CoreClosedImmersionFormula k)
    {X P : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sP : P ⟶ Spec (.of k)) [IsSmoothFT k sX]
    [IsSmoothFT k sP] (i : X ⟶ P) [IsClosedImmersion i] (hi : i ≫ sP = sX) (n : ℕ)
    [SmoothOfRelativeDimension n sP] [SmoothOfRelativeDimension n sX] [Nonempty X] :
    ClosedImmersionFormula k sX sP i hi := by
  have := smoothOfRelativeDimension_relativeProjectiveLine k
  have := isProper_relativeProjectiveLine_over (Spec (.of k))
  have : IsSmoothFT k (pullback.fst sP (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫
      sP) :=
    { smooth := inferInstance, isSeparated := inferInstance, quasiCompact := inferInstance }
  exact closedImmersionFormula_of_section k hcore sX sP
    (pullback.fst sP (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)))
    (Stacks.Chow.zeroSection sP) (pullback.lift_fst _ _ _) i hi n

/-- **The formula for closed immersions between pure-dimensional schemes**, from the core case
(codimension `≥ 1`) and R3 (codimension `0`). -/
theorem closedImmersionFormula_of_smoothOfRelativeDimension (hcore : CoreClosedImmersionFormula k)
    {X P : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sP : P ⟶ Spec (.of k)) [IsSmoothFT k sX]
    [IsSmoothFT k sP] (i : X ⟶ P) [IsClosedImmersion i] (hi : i ≫ sP = sX) (n m : ℕ)
    [SmoothOfRelativeDimension n sP] [SmoothOfRelativeDimension m sX] :
    ClosedImmersionFormula k sX sP i hi := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact closedImmersionFormula_of_isEmpty k sX sP i hi
  have : SmoothOfRelativeDimension m (i ≫ sP) := by rw [hi]; infer_instance
  have hr := Stacks.Conormal.isFiniteLocallyFreeOfRank_conormalSheaf_of_smoothOfRelativeDimension i
    sP n m
  have hadd := rank_add_conormal i sP n m (n - m) (Classical.arbitrary X)
  by_cases h1 : 1 ≤ n - m
  · exact closedImmersionFormula_of_bundles k sX sP i hi fun E _ ↦
      hcore sX sP i hi n m (n - m) h1 (by omega) E
  · have hnm : n = m := by omega
    subst hnm
    exact closedImmersionFormula_of_codim_zero k hcore sX sP i hi n

/-- The formula for a target of pure dimension: cut the source into its parts of constant
dimension. -/
theorem closedImmersionFormula_of_target (hcore : CoreClosedImmersionFormula k)
    {X P : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sP : P ⟶ Spec (.of k)) [IsSmoothFT k sX]
    [IsSmoothFT k sP] (i : X ⟶ P) [IsClosedImmersion i] (hi : i ≫ sP = sX) (n : ℕ)
    [SmoothOfRelativeDimension n sP] : ClosedImmersionFormula k sX sP i hi := by
  refine closedImmersionFormula_of_isClopenDecomposition k sX sP i hi
    (Stacks.WeilCohomology.dimPart sX) (Stacks.WeilCohomology.isClopenDecomposition_dimPart sX)
    fun m ↦ ?_
  have := (Stacks.WeilCohomology.isClopenDecomposition_dimPart sX).isClosedImmersion_ι m
  have := isSmoothFT_ι k sX (Stacks.WeilCohomology.dimPart sX m)
  have : SmoothOfRelativeDimension m ((Stacks.WeilCohomology.dimPart sX m).ι ≫ sX) :=
    smoothOfRelativeDimension_of_relativeDimension _ m
      (Stacks.WeilCohomology.relativeDimension_partBase sX m)
  exact closedImmersionFormula_of_smoothOfRelativeDimension k hcore _ sP _ _ n m

end CodimZero

/-! ### The normal class of Part C (R5) -/

section Normal

variable (k : Type u) [Field k] {X P : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sP : P ⟶ Spec (.of k)) [IsSmoothFT k sX] [IsSmoothFT k sP] (i : X ⟶ P) [IsClosedImmersion i]

/-- The conormal sheaf of the conormal sequence is the library's conormal module
`Stacks.Chow.conormalModule i = Stacks.Conormal.conormalSheaf i`. -/
def conormalSheafIsoConormalModule : conormalSheaf k sP i ≅ Stacks.Chow.conormalModule i :=
  Stacks.ConormalSequenceUnramifiedPair.conormalSheafComparisonIso i

omit [IsSmoothFT k sP] in
/-- The rank of `GRR.conormalSheaf` is the rank of `Stacks.Chow.conormalModule`. -/
theorem isFiniteLocallyFreeOfRank_conormalSheaf_iff (r : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalSheaf k sP i) r ↔
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (Stacks.Chow.conormalModule i) r :=
  ⟨AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      (conormalSheafIsoConormalModule k sP i),
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      (conormalSheafIsoConormalModule k sP i).symm⟩

variable (hi : i ≫ sP = sX)

include sX hi in
/-- `[N_{X/P}] = [conormalModule(i)^∨]`. -/
theorem normalClass_eq_classOf_dualSheaf_conormalModule :
    normalClass k sP i =
      VectorBundleKZero.classOf X (dualSheaf (Stacks.Chow.conormalModule i)) := by
  have hD := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf
    (conormalSheaf k sP i) (isFiniteLocallyFree_conormalSheaf k sX sP i hi)
  exact VectorBundleKZero.classOf_eq_of_iso
    (dualSheafIsoOfIso (conormalSheafIsoConormalModule k sP i)).symm
    (@Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree _ _ hD)

include sX hi in
/-- **R5**: `[N_{X/P}] = [𝒞^∨]` for `𝒞 = 𝒩^∨` the dual of the normal bundle
`𝒩 = (VirtualNormalBundle.ofIsRegularImmersion i hreg).bundle` of Part C. -/
theorem normalClass_eq_classOf_dualSheaf_bundle [IsLocallyNoetherian X]
    (hreg : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion i) :
    normalClass k sP i = VectorBundleKZero.classOf X
      (dualSheaf (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i hreg).bundle)) := by
  rw [normalClass_eq_classOf_dualSheaf_conormalModule k sX sP i hi]
  have hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (dualSheaf (Stacks.Chow.conormalModule i)) :=
    (VirtualNormalBundle.ofIsRegularImmersion i hreg).isFiniteLocallyFree
  have hI := isIso_toDoubleDual_of_isFiniteLocallyFree _ hN
  exact VectorBundleKZero.classOf_eq_of_iso (@asIso _ _ _ _ _ hI)
    (@Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree _ _ hN)

end Normal

/-! ### The reduction (F) -/

section Final

open ClosedImmersionReduce

variable (k : Type u) [Field k]

/-- **F: the closed immersion formula for every closed immersion of smooth schemes**, from its
core case: the target is cut into its open and closed parts `P_n` of constant dimension `n`
(`i⁻¹(P_n) ⟶ P_n` gives `i⁻¹(P_n) ⟶ P` by R1), then the source into its parts of constant
dimension (R2), and each pure piece is the core case or, in codimension zero, R3. -/
theorem closedImmersionFormula_of_core (hcore : CoreClosedImmersionFormula k) {X P : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sP : P ⟶ Spec (.of k)) [IsSmoothFT k sX] [IsSmoothFT k sP]
    (i : X ⟶ P) [IsClosedImmersion i] (hi : i ≫ sP = sX) :
    ClosedImmersionFormula k sX sP i hi := by
  have hW := Stacks.WeilCohomology.isClopenDecomposition_dimPart sP
  refine closedImmersionFormula_of_isClopenDecomposition k sX sP i hi
    (fun n ↦ i ⁻¹ᵁ Stacks.WeilCohomology.dimPart sP n) (hW.preimage i) fun n ↦ ?_
  have := hW.isClosedImmersion_ι n
  have := (hW.preimage i).isClosedImmersion_ι n
  have := isSmoothFT_ι k sP (Stacks.WeilCohomology.dimPart sP n)
  have := isSmoothFT_ι k sX (i ⁻¹ᵁ Stacks.WeilCohomology.dimPart sP n)
  have : SmoothOfRelativeDimension n ((Stacks.WeilCohomology.dimPart sP n).ι ≫ sP) :=
    smoothOfRelativeDimension_of_relativeDimension _ n
      (Stacks.WeilCohomology.relativeDimension_partBase sP n)
  exact closedImmersionFormula_of_restrict k sX sP i hi _
    (closedImmersionFormula_of_target k hcore _ _ _ _ n)

/-- **Grothendieck–Riemann–Roch for every closed immersion of smooth schemes**, from the core
case. -/
theorem riemannRochFor_of_core (hcore : CoreClosedImmersionFormula k) {X P : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sP : P ⟶ Spec (.of k)) [IsSmoothFT k sX] [IsSmoothFT k sP]
    (i : X ⟶ P) [IsClosedImmersion i] (hi : i ≫ sP = sX) : RiemannRochFor k sX sP i hi :=
  riemannRochFor_of_closedImmersionFormula k sX sP i hi
    (closedImmersionFormula_of_core k hcore sX sP i hi)

end Final

end GRR
