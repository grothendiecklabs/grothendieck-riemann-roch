import Mathlib
import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.GysinChernCharacter
import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TotalClassRestriction
import GRR.GradedHom
import GRR.ToddClass

/-!
# Pullback of rational Chow cohomology classes, and the projection formula

For a morphism `f : X ⟶ Y` of schemes locally of finite type over the base `(S, δ)`, restriction of
bivariant classes gives a graded ring map

  `f^* : ∏_p A^p(Y) ⊗ ℚ ⟶ ∏_p A^p(X) ⊗ ℚ`  (`GRR.pullbackAQ`).

It commutes with the Chern character and with the Todd class: `f^* ch(a) = ch(f^* a)`,
`f^* td(a) = td(f^* a)` for `a ∈ K₀(Vect Y)`. For proper `f` the cap action satisfies the
projection formula `f_* (f^* c ∩ γ) = c ∩ f_* γ` on `CH_* ⊗ ℚ`.
-/

open AlgebraicGeometry CategoryTheory Stacks.Chow
open scoped TensorProduct

universe u

namespace GRR

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

section Lifts

variable (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX)

/-- Restriction `ℚ ⊗ ∏_p A^p(Y) ⟶ ℚ ⊗ ∏_p A^p(X)`, the base change of the ring map
`TotalChowClass.res`. -/
noncomputable def resQ : ℚ ⊗[ℤ] TotalChowClass C sY →ₗ[ℚ] ℚ ⊗[ℤ] TotalChowClass C sX :=
  (TotalChowClass.res f hf).toAddMonoidHom.toIntLinearMap.baseChange ℚ

theorem resQ_tmul (r : ℚ) (c : TotalChowClass C sY) :
    resQ C sX sY f hf (r ⊗ₜ[ℤ] c) = r ⊗ₜ[ℤ] TotalChowClass.res f hf c :=
  rfl

theorem resQ_one : resQ C sX sY f hf 1 = 1 := by
  rw [Algebra.TensorProduct.one_def, resQ_tmul, map_one, ← Algebra.TensorProduct.one_def]

theorem resQ_mul (x y : ℚ ⊗[ℤ] TotalChowClass C sY) :
    resQ C sX sY f hf (x * y) = resQ C sX sY f hf x * resQ C sX sY f hf y := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]
  | tmul r c =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
    | tmul r' d =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, resQ_tmul, resQ_tmul, resQ_tmul, map_mul,
        Algebra.TensorProduct.tmul_mul_tmul]

/-- Components commute with restriction. -/
theorem rationalComponent_resQ (p : ℕ) (x : ℚ ⊗[ℤ] TotalChowClass C sY) :
    RationalTotalChowClass.rationalComponent p (resQ C sX sY f hf x) =
      ((chowCohomologyRestrictionOfEq C sX sY hf (gysinSystemOfInvertible C)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) p).toIntLinearMap.baseChange ℚ)
        (RationalTotalChowClass.rationalComponent p x) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  | tmul r c =>
    rw [resQ_tmul, RationalTotalChowClass.rationalComponent_tmul,
      RationalTotalChowClass.rationalComponent_tmul, LinearMap.baseChange_tmul,
      AddMonoidHom.coe_toIntLinearMap, TotalChowClass.res_apply_eq_chowCohomologyRestrictionOfEq]

/-- Componentwise restriction `∏_p A^p(Y) ⊗ ℚ ⟶ ∏_p A^p(X) ⊗ ℚ`, as a `ℚ`-linear map. -/
noncomputable def pullbackAQLinear :
    RationalTotalChowClass C sY →ₗ[ℚ] RationalTotalChowClass C sX where
  toFun c p := ((chowCohomologyRestrictionOfEq C sX sY hf (gysinSystemOfInvertible C)
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) p).toIntLinearMap.baseChange ℚ) (c p)
  map_add' a b := RationalTotalChowClass.ext fun p ↦ map_add _ (a p) (b p)
  map_smul' r a := RationalTotalChowClass.ext fun p ↦ map_smul _ r (a p)

theorem pullbackAQLinear_apply (c : RationalTotalChowClass C sY) (p : ℕ) :
    pullbackAQLinear C sX sY f hf c p =
      ((chowCohomologyRestrictionOfEq C sX sY hf (gysinSystemOfInvertible C)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) p).toIntLinearMap.baseChange ℚ)
        (c p) :=
  rfl

/-- Restriction of a lift below degree `m` is a lift below degree `m` of the restriction. -/
theorem rationalComponent_resQ_truncatedLift (m : ℕ) (a : RationalTotalChowClass C sY) {k : ℕ}
    (hk : k ≤ m) :
    RationalTotalChowClass.rationalComponent k
        (resQ C sX sY f hf (RationalTotalChowClass.truncatedLift m a)) =
      pullbackAQLinear C sX sY f hf a k := by
  rw [rationalComponent_resQ, RationalTotalChowClass.rationalComponent_truncatedLift m a hk,
    pullbackAQLinear_apply]

theorem pullbackAQLinear_one : pullbackAQLinear C sX sY f hf 1 = 1 :=
  RationalTotalChowClass.ext fun p ↦ by
    rw [pullbackAQLinear_apply, RationalTotalChowClass.one_apply, RationalTotalChowClass.one_apply,
      ← rationalComponent_resQ, resQ_one]

theorem pullbackAQLinear_mul (a b : RationalTotalChowClass C sY) :
    pullbackAQLinear C sX sY f hf (a * b) =
      pullbackAQLinear C sX sY f hf a * pullbackAQLinear C sX sY f hf b :=
  RationalTotalChowClass.ext fun m ↦ by
    rw [pullbackAQLinear_apply, RationalTotalChowClass.mul_apply a b m, ← rationalComponent_resQ,
      resQ_mul, RationalTotalChowClass.mul_apply_eq
        (fun k hk ↦ rationalComponent_resQ_truncatedLift C sX sY f hf m a hk)
        (fun k hk ↦ rationalComponent_resQ_truncatedLift C sX sY f hf m b hk)]

end Lifts

/-- **Pullback of rational Chow cohomology classes** along `f : X ⟶ Y`, as a ring map
`∏_p A^p(Y) ⊗ ℚ ⟶ ∏_p A^p(X) ⊗ ℚ`: in each degree it is the restriction of bivariant classes of
Stacks, tensored with `ℚ`. -/
noncomputable def pullbackAQ (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX) :
    RationalTotalChowClass C sY →+* RationalTotalChowClass C sX where
  toFun := pullbackAQLinear C sX sY f hf
  map_one' := pullbackAQLinear_one C sX sY f hf
  map_mul' := pullbackAQLinear_mul C sX sY f hf
  map_zero' := map_zero _
  map_add' := map_add _

variable (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX)

/-- The degree-`p` component of a pullback is the restriction of the degree-`p` component. -/
theorem pullbackAQ_apply (c : RationalTotalChowClass C sY) (p : ℕ) :
    pullbackAQ C sX sY f hf c p =
      ((chowCohomologyRestrictionOfEq C sX sY hf (gysinSystemOfInvertible C)
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) p).toIntLinearMap.baseChange ℚ)
        (c p) :=
  rfl

/-- Pullback is a graded ring map. -/
theorem isGradedHom_pullbackAQ :
    GradedComplete.IsGradedHom (chowGraded C sY) (chowGraded C sX) (pullbackAQ C sX sY f hf) :=
  ⟨fun n ↦ ⟨(chowCohomologyRestrictionOfEq C sX sY hf (gysinSystemOfInvertible C)
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) n).toIntLinearMap.baseChange ℚ,
    fun a ↦ pullbackAQ_apply C sX sY f hf a n⟩⟩

/-- Pullback of an integral total class is the integral restriction. -/
theorem pullbackAQ_ofTotalChowClass (c : TotalChowClass C sY) :
    pullbackAQ C sX sY f hf (RationalTotalChowClass.ofTotalChowClass c) =
      RationalTotalChowClass.ofTotalChowClass (TotalChowClass.res f hf c) :=
  RationalTotalChowClass.ext fun p ↦ by
    rw [pullbackAQ_apply, RationalTotalChowClass.ofTotalChowClass_apply,
      RationalTotalChowClass.ofTotalChowClass_apply, LinearMap.baseChange_tmul,
      AddMonoidHom.coe_toIntLinearMap, TotalChowClass.res_apply_eq_chowCohomologyRestrictionOfEq]

/-- **The Chern character commutes with pullback**: `f^* ch(a) = ch(f^* a)`. -/
theorem pullbackAQ_ch (a : VectorBundleKZero Y) :
    pullbackAQ C sX sY f hf (ch C sY a) = ch C sX (VectorBundleKZero.pullback f a) :=
  RationalTotalChowClass.ext fun p ↦ by
    rw [pullbackAQ_apply, ch_apply, ch_apply,
      rationalChowCohomologyRestriction_chernCharacterVectorBundle]

/-- **The Todd class commutes with pullback**: `f^* td(a) = td(f^* a)`. -/
theorem pullbackAQ_toddClass (a : VectorBundleKZero Y) :
    pullbackAQ C sX sY f hf (toddClass C sY a) =
      toddClass C sX (VectorBundleKZero.pullback f a) := by
  rw [toddClass, toddClass, (isGradedHom_pullbackAQ C sX sY f hf).map_toddOf, pullbackAQ_ch]

/-- **The projection formula for the cap action**: for proper `f` and `δ` bounded below on `X`
and on `Y`, `f_* (f^* c ∩ γ) = c ∩ f_* γ` for `c ∈ ∏_p A^p(Y) ⊗ ℚ` and `γ ∈ CH_*(X) ⊗ ℚ`. -/
theorem rationalProperChowPushforward_totalRationalChowCap_pullbackAQ [IsProper f]
    (hX : BddBelow (Set.range (relativeDimension C.dimensionFunction sX)))
    (hY : BddBelow (Set.range (relativeDimension C.dimensionFunction sY)))
    (c : RationalTotalChowClass C sY)
    (γ : DirectSum ℤ fun j : ℤ ↦ ℚ ⊗[ℤ] chowGroup C sX j) :
    rationalProperChowPushforward C sX sY hf
        (totalRationalChowCap C (gysinSystemOfInvertible C) sX
          (RationalTotalChowClass.ofFamily.symm (pullbackAQ C sX sY f hf c)) γ) =
      totalRationalChowCap C (gysinSystemOfInvertible C) sY
        (RationalTotalChowClass.ofFamily.symm c) (rationalProperChowPushforward C sX sY hf γ) := by
  obtain ⟨loX, hX'⟩ : ∃ lo : ℤ, ∀ x : X, lo ≤ relativeDimension C.dimensionFunction sX x :=
    hX.imp fun _ h x ↦ h ⟨x, rfl⟩
  obtain ⟨loY, hY'⟩ : ∃ lo : ℤ, ∀ y : Y, lo ≤ relativeDimension C.dimensionFunction sY y :=
    hY.imp fun _ h y ↦ h ⟨y, rfl⟩
  refine LinearMap.congr_fun (f := rationalProperChowPushforward C sX sY hf ∘ₗ
      totalRationalChowCap C (gysinSystemOfInvertible C) sX
        (RationalTotalChowClass.ofFamily.symm (pullbackAQ C sX sY f hf c)))
    (g := totalRationalChowCap C (gysinSystemOfInvertible C) sY
        (RationalTotalChowClass.ofFamily.symm c) ∘ₗ rationalProperChowPushforward C sX sY hf)
    (DirectSum.linearMap_ext ℚ fun k ↦ LinearMap.ext fun t ↦ ?_) γ
  simp only [LinearMap.comp_apply]
  rw [totalRationalChowCap_lof_eq_sum C _ sX loX hX' _ k t
      (Finset.range ((k - loX).toNat + (k - loY).toNat + 1))
      (fun p hp ↦ by rw [Finset.mem_range]; omega), map_sum,
    rationalProperChowPushforward_lof, totalRationalChowCap_lof_eq_sum C _ sY loY hY' _ k _
      (Finset.range ((k - loX).toNat + (k - loY).toNat + 1))
      (fun p hp ↦ by rw [Finset.mem_range]; omega)]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [RationalTotalChowClass.ofFamily_symm_apply, RationalTotalChowClass.ofFamily_symm_apply,
    pullbackAQ_apply, ← LinearMap.comp_apply, rationalProperChowPushforward_comp_rationalChowCap,
    LinearMap.comp_apply, rationalProperChowPushforward_lof]

end GRR
