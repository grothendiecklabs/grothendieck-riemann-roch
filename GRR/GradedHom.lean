import Mathlib
import GRR.GradedExp

/-!
# Graded maps between graded-complete rings

A ring map `φ : R →+* R'` between graded-complete `ℚ`-algebras is *graded* (`GRR.IsGradedHom`) if
it acts component by component through `ℚ`-linear maps. Such a map commutes with the exponential
`gexp`, with degreewise rescaling `weight`, with evaluation of power series `ev`, and therefore
with the Todd operation `toddOf`. Pullback of Chow cohomology classes is of this kind.
-/

open PowerSeries Finset

universe u v u' v'

namespace GRR

namespace GradedComplete

variable {R : Type u} [Ring R] [Module ℚ R] (G : GRR.GradedComplete.{u, v} R)
  {R' : Type u'} [Ring R'] [Module ℚ R'] (G' : GRR.GradedComplete.{u', v'} R')

/-- A ring map between graded-complete rings is graded if it acts component by component through
`ℚ`-linear maps. -/
structure IsGradedHom (φ : R →+* R') : Prop where
  exists_comp : ∀ n, ∃ ψ : G.M n →ₗ[ℚ] G'.M n, ∀ a, G'.comp n (φ a) = ψ (G.comp n a)

variable {G G'} {φ : R →+* R'}

theorem IsGradedHom.map_smul (hφ : IsGradedHom G G' φ) (q : ℚ) (a : R) :
    φ (q • a) = q • φ a := by
  refine G'.ext _ _ fun n ↦ ?_
  obtain ⟨ψ, hψ⟩ := hφ.exists_comp n
  rw [hψ, _root_.map_smul, _root_.map_smul, _root_.map_smul, hψ]

theorem IsGradedHom.map_gexp (hφ : IsGradedHom G G' φ) (x : R) :
    φ (G.gexp x) = G'.gexp (φ x) := by
  refine G'.ext _ _ fun n ↦ ?_
  obtain ⟨ψ, hψ⟩ := hφ.exists_comp n
  rw [hψ, comp_gexp, comp_gexp, ← hψ, map_sum]
  simp only [hφ.map_smul, map_pow]

theorem IsGradedHom.map_weight (hφ : IsGradedHom G G' φ) (w : ℕ → ℚ) (a : R) :
    φ (G.weight w a) = G'.weight w (φ a) := by
  refine G'.ext _ _ fun n ↦ ?_
  obtain ⟨ψ, hψ⟩ := hφ.exists_comp n
  rw [hψ, comp_weight, comp_weight, hψ, _root_.map_smul]

theorem IsGradedHom.map_ev (hφ : IsGradedHom G G' φ) (h : R) (F : ℚ⟦X⟧) :
    φ (G.ev h F) = G'.ev (φ h) F := by
  refine G'.ext _ _ fun n ↦ ?_
  obtain ⟨ψ, hψ⟩ := hφ.exists_comp n
  rw [hψ, comp_ev, comp_ev, ← hψ, map_sum]
  simp only [hφ.map_smul, map_pow]

/-- A graded ring map commutes with the Todd operation. -/
theorem IsGradedHom.map_toddOf (hφ : IsGradedHom G G' φ) (c : R) :
    φ (G.toddOf c) = G'.toddOf (φ c) := by
  rw [toddOf, toddOf, hφ.map_gexp, hφ.map_weight]

theorem IsGradedHom.isHom (hφ : IsGradedHom G G' φ) {n : ℕ} {a : R} (ha : G.IsHom n a) :
    G'.IsHom n (φ a) := fun p hp ↦ by
  obtain ⟨ψ, hψ⟩ := hφ.exists_comp p
  rw [hψ, ha p hp, map_zero]

end GradedComplete

end GRR
