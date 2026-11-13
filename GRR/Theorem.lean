import Mathlib
import GRR.Final
import GRR.ClosedFormulaCore
import GRR.ZeroSectionRR
import GRR.ClosedImmersionReduce

/-!
# The Grothendieck–Riemann–Roch theorem

For schemes smooth, separated and of finite type over a field `k`:

* `GRR.closedImmersionFormula`: Riemann–Roch without tangent bundles,
  `ch(i_! α) ∩ [P] = i_*((ch(α) · td(N_{X/P})⁻¹) ∩ [X])`, for every closed immersion `i : X ⟶ P`.
* `GRR.riemannRochFor_closedImmersion`: the Riemann–Roch formula for closed immersions.
* `GRR.grothendieck_riemann_roch`: for a projective morphism `f : X ⟶ Y` and `α ∈ K'₀(X)`,
  `f_*((ch(α) · td(T_X)) ∩ [X]) = (ch(f_! α) · td(T_Y)) ∩ [Y]` in `CH_*(Y) ⊗ ℚ`.
* `GRR.hirzebruch_riemann_roch`: for `X` projective over `k`,
  `∫_X ch(α) · td(T_X) = χ(X, α)`.
-/

open AlgebraicGeometry CategoryTheory Stacks.Chow

universe u

namespace GRR

variable (k : Type u) [Field k]

/-- **The core case of the closed immersion formula**: pure dimensions and conormal sheaf of
constant rank. The deformation to the normal cone (`GRR.closedImmersionFormula_core_of`) reduces
it to the zero section of `𝐏(𝒞 ⊕ 𝒪_X)` (`GRR.zeroSection_formula`). -/
theorem closedImmersionFormula_core : CoreClosedImmersionFormula k := by
  intro X P sX sP _ _ i _ hi n m r _ _ _ _ _ _ E _
  have hP : RelativeDimension sP n :=
    ClosedImmersionReduce.relativeDimension_of_smoothOfRelativeDimension sP n
  have : IsLocallyNoetherian X := (isNoetherian k sX).toIsLocallyNoetherian
  have := ClosedFormulaCore.isFiniteLocallyFreeOfRank_conormalBundle k sX sP i hi r
  exact closedImmersionFormula_core_of k sX sP i hi hP r
    (fun E _ _ hK e ↦
      zeroSection_formula (ClosedFormulaCore.conormalBundle k sX sP i hi) r k sX E hK e)
    (normalClass_eq_classOf_dualSheaf_bundle k sX sP i hi
      (DeformationGeom.isRegularImmersion_of_isSmoothFT k sX sP i hi)) E

/-- **Riemann–Roch without tangent bundles**: for every closed immersion `i : X ⟶ P` of schemes
smooth, separated and of finite type over `k` and every `α ∈ K'₀(X)`,
`ch(i_! α) ∩ [P] = i_*((ch(α) · td(N_{X/P})⁻¹) ∩ [X])`. -/
theorem closedImmersionFormula {X P : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sP : P ⟶ Spec (.of k)) [IsSmoothFT k sX] [IsSmoothFT k sP] (i : X ⟶ P)
    [IsClosedImmersion i] (hi : i ≫ sP = sX) : ClosedImmersionFormula k sX sP i hi :=
  closedImmersionFormula_of_core k (closedImmersionFormula_core k) sX sP i hi

/-- **Grothendieck–Riemann–Roch for closed immersions** of schemes smooth, separated and of
finite type over `k`. -/
theorem riemannRochFor_closedImmersion {X P : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sP : P ⟶ Spec (.of k)) [IsSmoothFT k sX] [IsSmoothFT k sP] (i : X ⟶ P)
    [IsClosedImmersion i] (hi : i ≫ sP = sX) : RiemannRochFor k sX sP i hi :=
  riemannRochFor_of_closedImmersionFormula k sX sP i hi (closedImmersionFormula k sX sP i hi)

/-- **The Grothendieck–Riemann–Roch theorem.** Let `X` and `Y` be smooth, separated and of
finite type over a field `k` and `f : X ⟶ Y` a projective morphism over `k` (a closed immersion
into some `ℙⁿ_Y` followed by the projection). For every `α ∈ K'₀(X)`,

  `f_*((ch(α) · td(T_X)) ∩ [X]) = (ch(f_! α) · td(T_Y)) ∩ [Y]`   in `CH_*(Y) ⊗ ℚ`,

where `f_*` is proper pushforward of cycles, `f_! [F] = ∑_i (-1)^i [R^i f_* F]` on the
Grothendieck group of coherent sheaves, and `τ_X(α) = (ch(α) · td(T_X)) ∩ [X]` is `GRR.tau`. -/
theorem grothendieck_riemann_roch {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sY : Y ⟶ Spec (.of k)) [IsSmoothFT k sX] [IsSmoothFT k sY] (f : X ⟶ Y) (hf : f ≫ sY = sX)
    (hproj : IsProjectiveMorphism f) (α : CoherentKZero X) :
    haveI := isProper_of_isProjectiveMorphism f hproj
    haveI := compactSpace k sY
    haveI : IsLocallyNoetherian Y := (isNoetherian k sY).toIsLocallyNoetherian
    rationalProperChowPushforward (fieldChowSituation k) sX sY hf (tau k sX α) =
      tau k sY (pushforwardK f α) :=
  haveI := isProper_of_isProjectiveMorphism f hproj
  grothendieck_riemann_roch_of_closedImmersionFormula k
    (fun sX sP _ _ i _ hi ↦ closedImmersionFormula k sX sP i hi) sX sY f hf hproj α

/-- **The Hirzebruch–Riemann–Roch theorem.** Let `X` be smooth and projective over a field `k`.
For every `α ∈ K'₀(X)`, the pushforward to the point of `(ch(α) · td(T_X)) ∩ [X]` is
`χ(X, α) · [Spec k]`, where `χ([F]) = ∑_i (-1)^i dim_k H^i(X, F)`. -/
theorem hirzebruch_riemann_roch {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsSmoothFT k sX]
    (hproj : IsProjectiveMorphism sX) (α : CoherentKZero X) :
    haveI := isProper_of_isProjectiveMorphism sX hproj
    rationalProperChowPushforward (fieldChowSituation k) sX (𝟙 (Spec (.of k)))
        (Category.comp_id sX) (tau k sX α) =
      ((eulerK k sX α : ℤ) : ℚ) • fundamentalClass k (𝟙 (Spec (.of k))) :=
  haveI := isProper_of_isProjectiveMorphism sX hproj
  hirzebruch_riemann_roch_of_closedImmersionFormula k
    (fun sX sP _ _ i _ hi ↦ closedImmersionFormula k sX sP i hi) sX hproj α

end GRR
