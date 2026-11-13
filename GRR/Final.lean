import Mathlib
import GRR.Main
import GRR.HRR
import GRR.ProjectionK
import GRR.ProjectionGen
import GRR.ProjectionTau

/-!
# Grothendieck–Riemann–Roch: what is proved, and what remains

* `GRR.riemannRochFor_projectiveSpaceOver`: the Riemann–Roch formula for every projection
  `ℙⁿ_Y ⟶ Y`, `Y` smooth, separated and of finite type over a field — unconditional.
* `GRR.hirzebruch_riemann_roch_projectiveSpace`: Hirzebruch–Riemann–Roch on `ℙⁿ_k` — unconditional.
* `GRR.grothendieck_riemann_roch_of_closedImmersionFormula`: the Riemann–Roch formula for every
  projective morphism, assuming only the formula without tangent bundles
  (`GRR.ClosedImmersionFormula`) for closed immersions; this is a reduction, not the theorem.
* `GRR.hirzebruch_riemann_roch_of_closedImmersionFormula`: Hirzebruch–Riemann–Roch for a smooth
  projective `X`, under the same assumption.
* `GRR.isFiniteLocallyFree_tangentSheaf`: the tangent sheaf of a smooth scheme is finite locally
  free, so that `GRR.tangentClass` is its class.
-/

open AlgebraicGeometry CategoryTheory Stacks.Chow

universe u

namespace GRR

variable (k : Type u) [Field k]

/-- The tangent sheaf of a smooth scheme over `k` is finite locally free. -/
theorem isFiniteLocallyFree_tangentSheaf {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsSmoothFT k sX] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (tangentSheaf k sX) := by
  have := Scheme.Hom.isFiniteLocallyFree_relativeDifferentials sX
  unfold tangentSheaf
  infer_instance

/-- The Riemann–Roch formula only depends on the morphism. -/
theorem RiemannRochFor.congr {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k)) [IsSmoothFT k sX] [IsSmoothFT k sY] {f g : X ⟶ Y} [IsProper f]
    [IsProper g] (h : f = g) (hf : f ≫ sY = sX) (hg : g ≫ sY = sX)
    (H : RiemannRochFor k sX sY f hf) : RiemannRochFor k sX sY g hg := by
  subst h
  exact H

/-- **Grothendieck–Riemann–Roch for the projections `ℙⁿ_Y ⟶ Y`**: for `Y` smooth, separated and
of finite type over `k` and every `α ∈ K'₀(ℙⁿ_Y)`,
`π_* ((ch(α) · td(T_{ℙⁿ_Y})) ∩ [ℙⁿ_Y]) = (ch(π_! α) · td(T_Y)) ∩ [Y]`. -/
theorem riemannRochFor_projectiveSpaceOver {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    [IsSmoothFT k sY] (n : ℕ) :
    RiemannRochFor k ((projectiveSpaceOver n Y ↘ Y) ≫ sY) sY (projectiveSpaceOver n Y ↘ Y) rfl :=
  riemannRochFor_projection_of k sY n (projectionPushforwardFormula k sY n)
    (projectionGeneration k sY n) (projectionTauFormula k sY n)

/-- **Grothendieck–Riemann–Roch for projective morphisms, assuming the formula without tangent
bundles for closed immersions.** This is a reduction: its hypothesis `hE` is not proved. -/
theorem grothendieck_riemann_roch_of_closedImmersionFormula
    (hE : ∀ {X P : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sP : P ⟶ Spec (.of k)) [IsSmoothFT k sX]
      [IsSmoothFT k sP] (i : X ⟶ P) [IsClosedImmersion i] (hi : i ≫ sP = sX),
      ClosedImmersionFormula k sX sP i hi)
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [IsSmoothFT k sX]
    [IsSmoothFT k sY] (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX)
    (hproj : IsProjectiveMorphism f) :
    RiemannRochFor k sX sY f hf :=
  grothendieck_riemann_roch_of k hE (fun sY _ n ↦ projectionPushforwardFormula k sY n)
    (fun sY _ n ↦ projectionGeneration k sY n) (fun sY _ n ↦ projectionTauFormula k sY n)
    sX sY f hf hproj

/-- **Hirzebruch–Riemann–Roch on projective space** `ℙⁿ_k`: for every `α ∈ K'₀(ℙⁿ_k)`, the
pushforward to the point of `(ch(α) · td(T_{ℙⁿ_k})) ∩ [ℙⁿ_k]` is `χ(ℙⁿ_k, α) · [Spec k]`. -/
theorem hirzebruch_riemann_roch_projectiveSpace (n : ℕ)
    (α : CoherentKZero (projectiveSpaceOver n (Spec (.of k)))) :
    rationalProperChowPushforward (fieldChowSituation k)
        ((projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) ≫ 𝟙 (Spec (.of k)))
        (𝟙 (Spec (.of k))) (Category.comp_id _)
        (tau k ((projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) ≫ 𝟙 (Spec (.of k))) α) =
      ((eulerK k ((projectiveSpaceOver n (Spec (.of k)) ↘ Spec (.of k)) ≫ 𝟙 (Spec (.of k))) α :
        ℤ) : ℚ) • fundamentalClass k (𝟙 (Spec (.of k))) :=
  hirzebruch_riemann_roch_of k _
    (RiemannRochFor.congr k _ _ (Category.comp_id _).symm rfl (Category.comp_id _)
      (riemannRochFor_projectiveSpaceOver k (𝟙 (Spec (.of k))) n)) α

/-- **Hirzebruch–Riemann–Roch for a smooth projective scheme, assuming the formula without
tangent bundles for closed immersions.** This is a reduction: `hE` is not proved. -/
theorem hirzebruch_riemann_roch_of_closedImmersionFormula
    (hE : ∀ {X P : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sP : P ⟶ Spec (.of k)) [IsSmoothFT k sX]
      [IsSmoothFT k sP] (i : X ⟶ P) [IsClosedImmersion i] (hi : i ≫ sP = sX),
      ClosedImmersionFormula k sX sP i hi)
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsSmoothFT k sX] [IsProper sX]
    (hproj : IsProjectiveMorphism sX) (α : CoherentKZero X) :
    rationalProperChowPushforward (fieldChowSituation k) sX (𝟙 (Spec (.of k)))
        (Category.comp_id sX) (tau k sX α) =
      ((eulerK k sX α : ℤ) : ℚ) • fundamentalClass k (𝟙 (Spec (.of k))) :=
  hirzebruch_riemann_roch_of k sX
    (grothendieck_riemann_roch_of_closedImmersionFormula k hE sX (𝟙 (Spec (.of k))) sX
      (Category.comp_id sX) hproj) α

end GRR
