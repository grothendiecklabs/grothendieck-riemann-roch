import Mathlib
import GRR.ClosedImmersion
import GRR.Projection

/-!
# Grothendieck–Riemann–Roch for projective morphisms, from its four remaining inputs

This file assembles the reductions of the project. The Riemann–Roch formula
`f_* ((ch(α) · td(T_X)) ∩ [X]) = (ch(f_! α) · td(T_Y)) ∩ [Y]` for a projective morphism
`f : X ⟶ Y` of smooth separated schemes of finite type over a field (`GRR.RiemannRochFor`) is
deduced from four statements:

* `GRR.ClosedImmersionFormula` for closed immersions (Riemann–Roch without tangent bundles);
* `GRR.ProjectionPushforwardFormula`, `GRR.ProjectionGeneration` and `GRR.ProjectionTauFormula`
  for the projections `ℙⁿ_Y ⟶ Y`.

`GRR.grothendieck_riemann_roch_of` is that implication; it is a reduction, not the theorem.
-/

open AlgebraicGeometry CategoryTheory Stacks.Chow

universe u

namespace GRR

variable (k : Type u) [Field k]

/-- **Grothendieck–Riemann–Roch for projective morphisms, assuming the four remaining inputs**:
the formula without tangent bundles for closed immersions, and the three statements about the
twisted classes on projective spaces. -/
theorem grothendieck_riemann_roch_of
    (hE : ∀ {X P : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sP : P ⟶ Spec (.of k)) [IsSmoothFT k sX]
      [IsSmoothFT k sP] (i : X ⟶ P) [IsClosedImmersion i] (hi : i ≫ sP = sX),
      ClosedImmersionFormula k sX sP i hi)
    (h1 : ∀ {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsSmoothFT k sY] (n : ℕ),
      ProjectionPushforwardFormula k sY n)
    (h2 : ∀ {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsSmoothFT k sY] (n : ℕ),
      ProjectionGeneration k sY n)
    (h3 : ∀ {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsSmoothFT k sY] (n : ℕ),
      ProjectionTauFormula k sY n)
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [IsSmoothFT k sX]
    [IsSmoothFT k sY] (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX)
    (hproj : IsProjectiveMorphism f) :
    RiemannRochFor k sX sY f hf :=
  riemannRochFor_of_isProjectiveMorphism k sY
    (fun sX' _ _ i _ hi ↦ riemannRochFor_of_closedImmersionFormula k sX' _ i hi (hE sX' _ i hi))
    (fun n ↦ riemannRochFor_projection_of k sY n (h1 sY n) (h2 sY n) (h3 sY n)) sX f hf hproj

end GRR
