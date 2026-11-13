import Mathlib
import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistTensorPow
import GRR.Statement

/-!
# Riemann–Roch for the projection `ℙⁿ_Y → Y`: reduction to three statements

Let `Y` be a smooth separated scheme of finite type over a field `k`, `π : ℙⁿ_Y → Y` the
projection and `𝒪(d)` the twisting sheaves. On the classes

  `g_j(β) = [𝒪(-j)] · π^* β ∈ K₀(Vect ℙⁿ_Y) ≅ K'₀(ℙⁿ_Y)`,  `0 ≤ j ≤ n`, `β ∈ K₀(Vect Y)`

(`GRR.twistedPullback`), both sides of the Riemann–Roch formula can be computed:

* `GRR.ProjectionPushforwardFormula`: `π_! g_j(β) = β` if `j = 0` and `0` otherwise
  (cohomology of the twists and the projection formula);
* `GRR.ProjectionTauFormula`: `π_* τ(g_j(β)) = τ_Y(β)` if `j = 0` and `0` otherwise
  (the Todd class of `ℙⁿ_Y`, the projective bundle formula and the coefficients of
  `e^{-jx} (x / (1 - e^{-x}))^{n+1}`);
* `GRR.ProjectionGeneration`: the `g_j(β)` generate `K'₀(ℙⁿ_Y)` rationally: a positive multiple
  of every class is a sum of them.

`GRR.riemannRochFor_projection_of` deduces the Riemann–Roch formula for `π` from the three.
-/

open AlgebraicGeometry CategoryTheory Stacks.Chow
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)
open scoped TensorProduct

universe u

namespace GRR

variable (k : Type u) [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsSmoothFT k sY]
  (n : ℕ)

/-- The class `[𝒪(d)] ∈ K₀(Vect ℙⁿ_Y)` of the twisting sheaf `𝒪(d)` on `ℙⁿ_Y`. -/
noncomputable def twistClass (Y : Scheme.{u}) (n : ℕ) (d : ℤ) :
    VectorBundleKZero (projectiveSpaceOver n Y) :=
  VectorBundleKZero.classOf (projectiveSpaceOver n Y) (twistOver n Y d)

/-- The class `g_j(β) = [𝒪(-j)] · π^* β` of `K₀(Vect ℙⁿ_Y)`, read in `K'₀(ℙⁿ_Y)`. -/
noncomputable def twistedPullback (j : ℕ) (β : VectorBundleKZero Y) :
    CoherentKZero (projectiveSpaceOver n Y) :=
  vectorBundleEquiv k ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
    (twistClass Y n (-(j : ℤ)) * VectorBundleKZero.pullback (projectiveSpaceOver n Y ↘ Y) β)

/-- **The pushforward of the twisted classes**: `π_! ([𝒪(-j)] · π^* β) = β` for `j = 0` and `0`
for `1 ≤ j ≤ n`. -/
def ProjectionPushforwardFormula : Prop :=
  haveI := compactSpace k sY
  haveI : IsLocallyNoetherian Y := (isNoetherian k sY).toIsLocallyNoetherian
  ∀ j : ℕ, j ≤ n → ∀ β : VectorBundleKZero Y,
    pushforwardK (projectiveSpaceOver n Y ↘ Y) (twistedPullback k sY n j β) =
      if j = 0 then vectorBundleEquiv k sY β else 0

/-- **The Riemann–Roch map on the twisted classes**: `π_* τ([𝒪(-j)] · π^* β) = τ_Y(β)` for
`j = 0` and `0` for `1 ≤ j ≤ n`. -/
def ProjectionTauFormula : Prop :=
  ∀ j : ℕ, j ≤ n → ∀ β : VectorBundleKZero Y,
    rationalProperChowPushforward (fieldChowSituation k)
        ((projectiveSpaceOver n Y ↘ Y) ≫ sY) sY rfl
        (tau k ((projectiveSpaceOver n Y ↘ Y) ≫ sY) (twistedPullback k sY n j β)) =
      if j = 0 then tau k sY (vectorBundleEquiv k sY β) else 0

/-- **The twisted classes generate `K'₀(ℙⁿ_Y)` rationally**: a positive multiple of every class
of `K'₀(ℙⁿ_Y)` is a sum of classes `[𝒪(-j)] · π^* β_j`, `0 ≤ j ≤ n`. -/
def ProjectionGeneration : Prop :=
  ∀ α : CoherentKZero (projectiveSpaceOver n Y),
    ∃ N : ℕ, 0 < N ∧ ∃ β : ℕ → VectorBundleKZero Y,
      N • α = ∑ j ∈ Finset.range (n + 1), twistedPullback k sY n j (β j)

/-- **Riemann–Roch for the projection `ℙⁿ_Y → Y`, from its three inputs.** -/
theorem riemannRochFor_projection_of (h1 : ProjectionPushforwardFormula k sY n)
    (h2 : ProjectionGeneration k sY n) (h3 : ProjectionTauFormula k sY n) :
    RiemannRochFor k ((projectiveSpaceOver n Y ↘ Y) ≫ sY) sY (projectiveSpaceOver n Y ↘ Y) rfl := by
  have := compactSpace k sY
  have : IsLocallyNoetherian Y := (isNoetherian k sY).toIsLocallyNoetherian
  intro α
  obtain ⟨N, hN, β, hβ⟩ := h2 α
  have hgen : ∀ j ∈ Finset.range (n + 1),
      rationalProperChowPushforward (fieldChowSituation k)
          ((projectiveSpaceOver n Y ↘ Y) ≫ sY) sY rfl
          (tau k ((projectiveSpaceOver n Y ↘ Y) ≫ sY) (twistedPullback k sY n j (β j))) =
        tau k sY (pushforwardK (projectiveSpaceOver n Y ↘ Y) (twistedPullback k sY n j (β j))) := by
    intro j hj
    have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [h3 j hj' (β j), h1 j hj' (β j)]
    split_ifs
    · rfl
    · rw [map_zero]
  have key : N • rationalProperChowPushforward (fieldChowSituation k)
        ((projectiveSpaceOver n Y ↘ Y) ≫ sY) sY rfl
        (tau k ((projectiveSpaceOver n Y ↘ Y) ≫ sY) α) =
      N • tau k sY (pushforwardK (projectiveSpaceOver n Y ↘ Y) α) := by
    rw [← map_nsmul, ← map_nsmul, ← map_nsmul, ← map_nsmul, hβ, map_sum, map_sum, map_sum,
      map_sum]
    exact Finset.sum_congr rfl hgen
  have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ] at key
  exact smul_right_injective _ hN' key

end GRR
