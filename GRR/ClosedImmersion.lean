import Mathlib
import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.SchemeShortExact
import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.DualComplexChern
import StacksFrontier.AlgebraicGeometry.Perfect.GenericFreeCohomology
import GRR.Statement
import GRR.Pullback

/-!
# Riemann–Roch for closed immersions: reduction to the formula without tangent bundles

Let `i : X ⟶ P` be a closed immersion of smooth separated schemes of finite type over a field
`k`, with conormal sheaf `C_{X/P}` and normal sheaf `N = C_{X/P}^∨`. The conormal sequence
`0 → C_{X/P} → i^* Ω_P → Ω_X → 0` gives `td(T_X) = i^* td(T_P) · td(N)⁻¹`
(`GRR.toddTangent_eq`). With the projection formula, the Grothendieck–Riemann–Roch formula for
`i` then follows from the formula without tangent bundles (`GRR.ClosedImmersionFormula`)

  `ch(i_! α) ∩ [P] = i_* ((ch(α) · td(N)⁻¹) ∩ [X])`,

which is `GRR.riemannRochFor_of_closedImmersionFormula`.

The input on duals is the sign rule `ch_p(E^∨) = (-1)^p ch_p(E)` for the Chern character of a
finite locally free module (`GRR.ch_classOf_dualSheaf`), from Stacks 0FA5 on rank loci.
-/

open AlgebraicGeometry CategoryTheory Stacks.Chow
open scoped TensorProduct

universe u

namespace GRR

section DualSign

open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf)

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- The power sums of the dual of a module of constant rank are the `(-1)^p`-scalings of those of
the module: `signScale` is a ring map carrying `c(E)` to `c(E^∨)` (Stacks 0FA5), hence Newton's
polynomials in the `c_j(E)` to those in the `c_j(E^∨)`. -/
theorem powerSumTotal_dualSheaf (E : Y.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (p : ℕ) :
    powerSumTotal C sY (dualSheaf E) r p =
      TotalChowClass.signScale (powerSumTotal C sY E r p) := by
  rcases eq_or_ne p 0 with rfl | hp
  · rw [powerSumTotal_zero, powerSumTotal_zero, ← TotalChowClass.signScaleRingHom_apply,
      map_natCast]
  · rw [powerSumTotal_of_ne_zero C sY _ _ hp, powerSumTotal_of_ne_zero C sY _ _ hp,
      ← TotalChowClass.signScaleRingHom_apply]
    symm
    refine AlgebraicGeometry.map_coe_powerSumEval_closure TotalChowClass.signScaleRingHom
      (chernSet_commute C sY) (chernSet_commute C sY) _
      (homPart_totalChern_mem_chernSet C sY E r) _
      (homPart_totalChern_mem_chernSet C sY (dualSheaf E) r) (fun j ↦ ?_) ?_ p
    · rw [TotalChowClass.signScaleRingHom_apply, ← TotalChowClass.homComponent_signScale,
        totalChern_dualSheaf]
    · rintro _ ⟨F, s, hF, j, rfl⟩
      rw [TotalChowClass.signScaleRingHom_apply, ← TotalChowClass.homComponent_signScale,
        ← totalChern_dualSheaf]
      exact Subring.subset_closure (homPart_totalChern_mem_chernSet C sY _ s j)

/-- The power sums of the dual of a finite locally free module are the `(-1)^p`-scalings of those
of the module, checked on the rank loci. -/
theorem powerSumOfFiniteLocallyFree_dualSheaf (E : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (p : ℕ) :
    powerSumOfFiniteLocallyFree C sY (dualSheaf E) p =
      TotalChowClass.signScale (powerSumOfFiniteLocallyFree C sY E p) := by
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_rankLociFamily E) fun r ↦ ?_
  let := isFiniteLocallyFreeOfRank_pullback_rankLociFamily E r
  let e : (Scheme.Modules.pullback (rankLociFamily E r).ι).obj (dualSheaf E) ≅
      dualSheaf ((Scheme.Modules.pullback (rankLociFamily E r).ι).obj E) :=
    VectorBundleKZero.pullbackDualSheafIso (rankLociFamily E r).ι E
      (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree E)
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (rankLociFamily E r).ι).obj (dualSheaf E)) r.down :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} e.symm
      inferInstance
  rw [TotalChowClass.res_signScale, res_powerSumOfFiniteLocallyFree_rankLocus C sY E r p,
    res_powerSumOfFiniteLocallyFree_of_rank C sY (dualSheaf E) _ rfl r.down p,
    powerSumTotal_congr C _ e rfl p]
  exact powerSumTotal_dualSheaf C _ _ r.down p

/-- **The sign rule for the Chern character of a dual**: `ch_p(E^∨) = (-1)^p ch_p(E)` for a
finite locally free module `E`. -/
theorem ch_classOf_dualSheaf (E : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    ch C sY (VectorBundleKZero.classOf Y (dualSheaf E)) =
      (chowGraded C sY).weight (fun n ↦ (-1 : ℚ) ^ n)
        (ch C sY (VectorBundleKZero.classOf Y E)) := by
  refine RationalTotalChowClass.ext fun n ↦ ?_
  rw [chowGraded_weight_apply, ch_apply, ch_apply, chernCharacterVectorBundle_classOf,
    chernCharacterVectorBundle_classOf, chernCharacterOfFiniteLocallyFree,
    chernCharacterOfFiniteLocallyFree, powerSumClassOfFiniteLocallyFree,
    powerSumClassOfFiniteLocallyFree, powerSumOfFiniteLocallyFree_dualSheaf,
    TotalChowClass.signScale_apply, TensorProduct.tmul_smul,
    show ((-1 : ℚ) ^ n) = ((((-1 : ℤ) ^ n : ℤ) : ℚ)) by push_cast; ring, Int.cast_smul_eq_zsmul]

end DualSign

section Cap

variable (k : Type u) [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))

/-- Over a field `δ` is bounded below, by `0`. -/
theorem bddBelow_relativeDimension_field :
    BddBelow (Set.range (relativeDimension (fieldChowSituation k).dimensionFunction sY)) :=
  ⟨0, by rintro _ ⟨y, rfl⟩; exact relativeDimension_fieldChowSituation_nonneg k sY y⟩

/-- **The cap action is multiplicative**: `(c d) ∩ - = c ∩ (d ∩ -)`. -/
theorem cap_mul [LocallyOfFiniteType sY] (c d : AQ k sY) :
    cap k sY (c * d) = cap k sY c * cap k sY d :=
  totalRationalChowCap_mul (fieldChowSituation k) sY 0
    (relativeDimension_fieldChowSituation_nonneg k sY) c d

/-- The Chern character of a coherent class is that of the corresponding class in
`K₀(Vect Y)`. -/
theorem chK_eq_ch [IsSmoothFT k sY] (β : CoherentKZero Y) :
    chK k sY β = ch (fieldChowSituation k) sY ((vectorBundleEquiv k sY).symm β) := by
  simp only [chK, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_ofClass,
    AddEquiv.coe_toAddMonoidHom]

end Cap

variable (k : Type u) [Field k] {X P : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sP : P ⟶ Spec (.of k)) [IsSmoothFT k sX] [IsSmoothFT k sP]
  (i : X ⟶ P) [IsClosedImmersion i]

/-- The conormal sheaf `C_{X/P}` of a closed immersion `i : X ⟶ P`: the first term of the
conormal sequence `0 → C_{X/P} → i^* Ω_{P/k} → Ω_{X/k} → 0` of Stacks 06AA. -/
noncomputable def conormalSheaf : X.Modules :=
  (Stacks.ConormalSequenceRight.conormalShortComplex i sP).X₁

/-- The normal sheaf `N_{X/P}`, the dual of the conormal sheaf. -/
noncomputable def normalSheaf : X.Modules :=
  Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf (conormalSheaf k sP i)

/-- The class `[N_{X/P}] ∈ K₀(Vect X)` of the normal sheaf. -/
noncomputable def normalClass : VectorBundleKZero X :=
  VectorBundleKZero.classOf X (normalSheaf k sP i)

variable (hi : i ≫ sP = sX)

include sX hi in
/-- The conormal sheaf of a closed immersion of smooth schemes is finite locally free. -/
theorem isFiniteLocallyFree_conormalSheaf :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (conormalSheaf k sP i) := by
  have hsm : Smooth (i ≫ sP) := by rw [hi]; infer_instance
  have := Scheme.Hom.isFiniteLocallyFree_relativeDifferentials sP
  exact isFiniteLocallyFree_X₁_of_shortExact
    (Stacks.ConormalSequenceRight.conormalShortComplex_shortExact i sP hsm)
    (isFiniteLocallyFree_pullbackObj _ i)
    (Scheme.Hom.isFiniteLocallyFree_relativeDifferentials (i ≫ sP))

/-- **`td(T_X) = i^* td(T_P) · td(N)⁻¹`** for a closed immersion `i : X ⟶ P` of smooth schemes
with normal sheaf `N` (from the conormal sequence and multiplicativity of the Todd class). -/
theorem toddTangent_eq :
    toddTangent k sX =
      pullbackAQ (fieldChowSituation k) sX sP i hi (toddTangent k sP) *
        toddClass (fieldChowSituation k) sX (-normalClass k sP i) := by
  have hC := isFiniteLocallyFree_conormalSheaf k sX sP i hi
  subst hi
  have hS := Stacks.ConormalSequenceRight.conormalShortComplex_shortExact i sP inferInstance
  have hΩP := Scheme.Hom.isFiniteLocallyFree_relativeDifferentials sP
  have hΩX := Scheme.Hom.isFiniteLocallyFree_relativeDifferentials (i ≫ sP)
  have h₂ := isFiniteLocallyFree_pullbackObj (Scheme.Hom.relativeDifferentials sP) i
  have := hS.mono_f
  have := hS.epi_g
  have hK := VectorBundleKZero.classOf_shortExact
    (Stacks.ConormalSequenceRight.conormalShortComplex i sP).f
    (Stacks.ConormalSequenceRight.conormalShortComplex i sP).g
    (Stacks.ConormalSequenceRight.conormalShortComplex i sP).zero hC h₂ hΩX hS.exact
  change VectorBundleKZero.classOf X
      ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials sP)) =
    VectorBundleKZero.classOf X (conormalSheaf k sP i) +
      VectorBundleKZero.classOf X (Scheme.Hom.relativeDifferentials (i ≫ sP)) at hK
  have hσ := (isGradedHom_pullbackAQ (fieldChowSituation k) (i ≫ sP) sP i rfl).map_weight
    (fun n ↦ (-1 : ℚ) ^ n)
  -- `ch(i^* [T_P]) = σ ch([i^* Ω_P])`, `σ` the sign rescaling
  have hpb : ch (fieldChowSituation k) (i ≫ sP)
      (VectorBundleKZero.pullback i (tangentClass k sP)) =
      (chowGraded (fieldChowSituation k) (i ≫ sP)).weight (fun n ↦ (-1 : ℚ) ^ n)
        (ch (fieldChowSituation k) (i ≫ sP) (VectorBundleKZero.classOf X
          ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials sP)))) := by
    rw [← pullbackAQ_ch (fieldChowSituation k) (i ≫ sP) sP i rfl, tangentClass, tangentSheaf,
      ch_classOf_dualSheaf, hσ, pullbackAQ_ch, VectorBundleKZero.pullback_classOf]
  -- `ch[T_X] = σ ch[Ω_X] = σ (ch[i^* Ω_P] - ch[C]) = ch(i^*[T_P]) - ch[N]`
  have key : ch (fieldChowSituation k) (i ≫ sP) (tangentClass k (i ≫ sP)) =
      ch (fieldChowSituation k) (i ≫ sP)
        (VectorBundleKZero.pullback i (tangentClass k sP) + -normalClass k sP i) := by
    rw [map_add, map_neg, hpb, normalClass, normalSheaf, ch_classOf_dualSheaf, tangentClass,
      tangentSheaf, ch_classOf_dualSheaf, ← GradedComplete.weight_neg,
      ← GradedComplete.weight_add, hK, map_add]
    congr 1
    abel
  calc toddTangent k (i ≫ sP)
      = toddClass (fieldChowSituation k) (i ≫ sP)
          (VectorBundleKZero.pullback i (tangentClass k sP) + -normalClass k sP i) :=
        congrArg (chowGraded (fieldChowSituation k) (i ≫ sP)).toddOf key
    _ = _ := by
        rw [toddClass_add, ← pullbackAQ_toddClass (fieldChowSituation k) (i ≫ sP) sP i rfl]
        rfl

/-- **The projection formula for `i`**: `i_* (i^* c ∩ γ) = c ∩ i_* γ`. -/
theorem rationalProperChowPushforward_cap_pullbackAQ (c : AQ k sP) (γ : CHQ k sX) :
    rationalProperChowPushforward (fieldChowSituation k) sX sP hi
        (cap k sX (pullbackAQ (fieldChowSituation k) sX sP i hi c) γ) =
      cap k sP c (rationalProperChowPushforward (fieldChowSituation k) sX sP hi γ) :=
  rationalProperChowPushforward_totalRationalChowCap_pullbackAQ (fieldChowSituation k) sX sP i hi
    (bddBelow_relativeDimension_field k sX) (bddBelow_relativeDimension_field k sP) c γ

/-- **Riemann–Roch for a closed immersion without tangent bundles**: for every `α ∈ K'₀(X)`,

  `ch(i_! α) ∩ [P] = i_* ((ch(α) · td(N_{X/P})⁻¹) ∩ [X])`  in `CH_*(P) ⊗ ℚ`. -/
def ClosedImmersionFormula : Prop :=
  haveI := compactSpace k sP
  haveI : IsLocallyNoetherian P := (isNoetherian k sP).toIsLocallyNoetherian
  ∀ α : CoherentKZero X,
    cap k sP (chK k sP (pushforwardK i α)) (fundamentalClass k sP) =
      rationalProperChowPushforward (fieldChowSituation k) sX sP hi
        (cap k sX (chK k sX α * toddClass (fieldChowSituation k) sX (-normalClass k sP i))
          (fundamentalClass k sX))

/-- **Grothendieck–Riemann–Roch for a closed immersion follows from the formula without tangent
bundles.** -/
theorem riemannRochFor_of_closedImmersionFormula
    (h : ClosedImmersionFormula k sX sP i hi) : RiemannRochFor k sX sP i hi := by
  have := compactSpace k sP
  have : IsLocallyNoetherian P := (isNoetherian k sP).toIsLocallyNoetherian
  intro α
  have hα := h α
  have hcX : Commute (pullbackAQ (fieldChowSituation k) sX sP i hi (toddTangent k sP))
      (chK k sX α) := by
    rw [toddTangent, pullbackAQ_toddClass, chK_eq_ch k sX]
    exact commute_toddClass_ch (fieldChowSituation k) sX _ _
  have hcP : Commute (toddTangent k sP) (chK k sP (pushforwardK i α)) := by
    rw [toddTangent, chK_eq_ch k sP]
    exact commute_toddClass_ch (fieldChowSituation k) sP _ _
  have hring : chK k sX α * (pullbackAQ (fieldChowSituation k) sX sP i hi (toddTangent k sP) *
        toddClass (fieldChowSituation k) sX (-normalClass k sP i)) =
      pullbackAQ (fieldChowSituation k) sX sP i hi (toddTangent k sP) *
        (chK k sX α * toddClass (fieldChowSituation k) sX (-normalClass k sP i)) := by
    rw [← mul_assoc, ← mul_assoc, hcX.eq]
  rw [tau_apply, tau_apply, toddTangent_eq k sX sP i hi, hring,
    cap_mul k sX (pullbackAQ (fieldChowSituation k) sX sP i hi (toddTangent k sP)),
    Module.End.mul_apply, rationalProperChowPushforward_cap_pullbackAQ k sX sP i hi, ← hα,
    ← hcP.eq, cap_mul k sP (toddTangent k sP), Module.End.mul_apply]

end GRR
