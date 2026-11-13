import Mathlib
import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.ChernCharacterMultiplicative
import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.SecondAdamsChernCharacter
import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TwistFormula
import GRR.GradedExp

/-!
# The Todd class in `∏_p A^p(X) ⊗ ℚ`

Let `(S, δ)` be a base situation of Chow homology and `X` locally of finite type over `S`. The ring
`Stacks.Chow.RationalTotalChowClass C sX = ∏_p A^p(X) ⊗ ℚ` is graded-complete
(`GRR.chowGraded`), so the Todd operation of `GRR.GradedComplete` applies to the Chern character
`ch : K₀(Vect X) → ∏_p A^p(X) ⊗ ℚ` of Stacks: `GRR.toddClass C sX a = td(a)` is the exponential of
`∑_p p! ℓ_p ch_p(a)`, where `log (x / (1 - e^{-x})) = ∑ ℓ_p x^p`.

Main results: `toddClass_add` (multiplicativity, hence on short exact sequences
`toddClass_classOf_of_shortExact`), `isUnit_toddClass`, and for an invertible module `L`,
`ch_classOf_invertible : ch(L) = e^{c₁(L)}` and
`toddClass_classOf_invertible : td(L) = c₁(L) / (1 - e^{-c₁(L)})`.
-/

open AlgebraicGeometry CategoryTheory Stacks.Chow
open scoped TensorProduct

universe u

namespace GRR

namespace GradedComplete

variable {R : Type*} [Ring R] [Module ℚ R] (G : GRR.GradedComplete R)

include G in
/-- A combination `∑_j c_j x^j` of powers of `x` commutes with whatever `x` commutes with. -/
theorem commute_sum_smul_pow {x y : R} (h : Commute x y) (c : ℕ → ℚ) (N : ℕ) :
    Commute (∑ j ∈ Finset.range N, c j • x ^ j) y := by
  refine Commute.sum_left _ _ _ fun j _ ↦ ?_
  change c j • x ^ j * y = y * (c j • x ^ j)
  rw [G.smul_mul, G.mul_smul, (h.pow_left j).eq]

/-- **`exp x` commutes with whatever `x` commutes with**, for `x` without constant term: up to
degree `n` it agrees with the polynomial `∑_{j ≤ n} x^j / j!`. -/
theorem commute_gexp_left {x y : R} (hx : G.comp 0 x = 0) (h : Commute x y) :
    Commute (G.gexp x) y := by
  change G.gexp x * y = y * G.gexp x
  refine G.ext _ _ fun n ↦ ?_
  rw [G.mul_congr n (G.gexp x) (∑ j ∈ Finset.range (n + 1), ((j.factorial : ℚ)⁻¹) • x ^ j) y y
      (fun p hp ↦ G.comp_gexp_of_le hx hp) (fun _ _ ↦ rfl),
    (G.commute_sum_smul_pow h (fun j ↦ ((j.factorial : ℚ)⁻¹)) (n + 1)).eq,
    G.mul_congr n y y _ (G.gexp x) (fun _ _ ↦ rfl) (fun p hp ↦ (G.comp_gexp_of_le hx hp).symm)]

theorem commute_gexp_right {x y : R} (hx : G.comp 0 x = 0) (h : Commute y x) :
    Commute y (G.gexp x) :=
  (G.commute_gexp_left hx h.symm).symm

end GradedComplete

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- A product of classes of degrees `i` and `j` in `ℚ ⊗ ∏_q A^q(X)` has no component of degree
other than `i + j`. -/
theorem rationalComponent_rationalSingle_mul_rationalSingle {i j p : ℕ} (hp : p ≠ i + j)
    (x : rationalChowCohomologyComponent C (gysinSystemOfInvertible C) sX i)
    (y : rationalChowCohomologyComponent C (gysinSystemOfInvertible C) sX j) :
    RationalTotalChowClass.rationalComponent p
      (RationalTotalChowClass.rationalSingle i x * RationalTotalChowClass.rationalSingle j y) =
        0 := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => rw [map_add, add_mul, map_add, hx, hx', add_zero]
  | tmul r c =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => rw [map_add, mul_add, map_add, hy, hy', add_zero]
    | tmul r' d =>
      rw [RationalTotalChowClass.rationalSingle_tmul, RationalTotalChowClass.rationalSingle_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, RationalTotalChowClass.rationalComponent_tmul,
        ((TotalChowClass.isHomogeneous_single i c).mul
          (TotalChowClass.isHomogeneous_single j d)) p hp, TensorProduct.tmul_zero]

/-- A family concentrated in degree `i` is lifted to `ℚ ⊗ ∏_q A^q(X)` by its degree-`i`
component, in every degree. -/
theorem rationalComponent_rationalSingle_of_isHom {i : ℕ} {a : RationalTotalChowClass C sX}
    (ha : ∀ p, p ≠ i → a p = 0) (k : ℕ) :
    RationalTotalChowClass.rationalComponent k (RationalTotalChowClass.rationalSingle i (a i)) =
      a k := by
  rcases eq_or_ne k i with rfl | hk
  · exact RationalTotalChowClass.rationalComponent_rationalSingle_self k (a k)
  · rw [RationalTotalChowClass.rationalComponent_rationalSingle_of_ne hk, ha k hk]

/-- **`∏_p A^p(X) ⊗ ℚ` is graded-complete**: its elements are the families of components
`a_p ∈ A^p(X) ⊗ ℚ`, multiplied by the Cauchy product. -/
noncomputable def chowGraded : GradedComplete.{u + 1, u + 1} (RationalTotalChowClass C sX) where
  M := fun n ↦ rationalChowCohomologyComponent C (gysinSystemOfInvertible C) sX (n : ℤ)
  comp := fun n ↦
    { toFun := fun a ↦ a n
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  ofComps := fun f ↦ f
  comp_ofComps := fun _ _ ↦ rfl
  ext := fun _ _ h ↦ RationalTotalChowClass.ext h
  smul_mul := fun q a b ↦ RationalTotalChowClass.ext fun m ↦ by
    rw [RationalTotalChowClass.smul_apply, RationalTotalChowClass.mul_apply,
      RationalTotalChowClass.mul_apply, map_smul, smul_mul_assoc, map_smul]
  mul_smul := fun q a b ↦ RationalTotalChowClass.ext fun m ↦ by
    rw [RationalTotalChowClass.smul_apply, RationalTotalChowClass.mul_apply,
      RationalTotalChowClass.mul_apply, map_smul, mul_smul_comm, map_smul]
  mul_congr := fun n a a' b b' ha hb ↦
    RationalTotalChowClass.mul_apply_eq
      (fun k hk ↦ (RationalTotalChowClass.rationalComponent_truncatedLift n a' hk).trans
        (ha k hk).symm)
      (fun k hk ↦ (RationalTotalChowClass.rationalComponent_truncatedLift n b' hk).trans
        (hb k hk).symm)
  mul_hom := fun i j a b ha hb p hp ↦ by
    change (a * b) p = 0
    rw [RationalTotalChowClass.mul_apply_eq
      (fun k _ ↦ rationalComponent_rationalSingle_of_isHom C sX (a := a) ha k)
      (fun k _ ↦ rationalComponent_rationalSingle_of_isHom C sX (a := b) hb k)]
    exact rationalComponent_rationalSingle_mul_rationalSingle C sX hp _ _
  comp_one := fun p hp ↦ by
    change (1 : RationalTotalChowClass C sX) p = 0
    rw [RationalTotalChowClass.one_apply, Algebra.TensorProduct.one_def,
      RationalTotalChowClass.rationalComponent_tmul, TotalChowClass.one_apply_of_ne hp,
      TensorProduct.tmul_zero]

@[simp]
theorem chowGraded_comp_apply (n : ℕ) (a : RationalTotalChowClass C sX) :
    (chowGraded C sX).comp n a = a n := rfl

/-- The degreewise rescaling, read on components. -/
theorem chowGraded_weight_apply (w : ℕ → ℚ) (c : RationalTotalChowClass C sX) (n : ℕ) :
    (chowGraded C sX).weight w c n = w n • c n :=
  (chowGraded C sX).comp_weight w c n

/-- The Chern character `ch : K₀(Vect X) → ∏_p A^p(X) ⊗ ℚ` of Stacks, as a ring map. -/
noncomputable abbrev ch : VectorBundleKZero X →+* RationalTotalChowClass C sX :=
  rationalTotalChernCharacterRingHom C sX

theorem ch_apply (a : VectorBundleKZero X) (n : ℕ) :
    ch C sX a n = chernCharacterVectorBundle C sX a n := rfl

/-- **The Todd class** `td(a) ∈ ∏_p A^p(X) ⊗ ℚ` of a class `a ∈ K₀(Vect X)`: the exponential of
`∑_p p! ℓ_p ch_p(a)`, where `log (x / (1 - e^{-x})) = ∑ ℓ_p x^p`. For `a = [E]` with Chern roots
`x_i` it is `∏_i x_i / (1 - e^{-x_i})`. -/
noncomputable def toddClass (a : VectorBundleKZero X) : RationalTotalChowClass C sX :=
  (chowGraded C sX).toddOf (ch C sX a)

/-- `ch((ψ²)^i a)` is `ch(a)` rescaled by `2^{i p}` in degree `p` (Stacks 0FEN, iterated). -/
theorem ch_secondAdams_iterate (i : ℕ) (a : VectorBundleKZero X) :
    ch C sX ((VectorBundleKZero.secondAdamsRingHom (VectorBundleKZero.squarePowersData X))^[i] a) =
      (chowGraded C sX).weight (fun n ↦ (2 : ℚ) ^ (i * n)) (ch C sX a) := by
  induction i with
  | zero =>
    refine RationalTotalChowClass.ext fun n ↦ ?_
    rw [chowGraded_weight_apply, Function.iterate_zero_apply, zero_mul, pow_zero, one_smul]
  | succ i ih =>
    refine RationalTotalChowClass.ext fun n ↦ ?_
    rw [Function.iterate_succ_apply', ch_apply, chernCharacterVectorBundle_secondAdams,
      ← ch_apply, ih, chowGraded_weight_apply, chowGraded_weight_apply, smul_smul, ← pow_add,
      add_mul, one_mul, add_comm]

/-- The degreewise rescalings of two Chern characters commute (the Chern character is a ring map
out of a commutative ring and `ch_p(ψ² a) = 2^p ch_p(a)`). -/
theorem commute_weight_ch (w w' : ℕ → ℚ) (a b : VectorBundleKZero X) :
    Commute ((chowGraded C sX).weight w (ch C sX a)) ((chowGraded C sX).weight w' (ch C sX b)) := by
  refine (chowGraded C sX).commute_weight_of_commute_scaling (fun i ↦ ?_) w w'
  rw [← ch_secondAdams_iterate]
  exact (Commute.all _ _).map (ch C sX)

theorem toddClass_zero : toddClass C sX 0 = 1 := by
  rw [toddClass, map_zero, GradedComplete.toddOf_zero]

/-- **The Todd class is multiplicative**: `td(a + b) = td(a) · td(b)`. -/
theorem toddClass_add (a b : VectorBundleKZero X) :
    toddClass C sX (a + b) = toddClass C sX a * toddClass C sX b := by
  simp only [toddClass, map_add]
  exact (chowGraded C sX).toddOf_add (commute_weight_ch C sX _ _ a b)

theorem toddClass_mul_toddClass_neg (a : VectorBundleKZero X) :
    toddClass C sX a * toddClass C sX (-a) = 1 := by
  simp only [toddClass, map_neg]
  exact (chowGraded C sX).toddOf_mul_toddOf_neg _

theorem toddClass_neg_mul_toddClass (a : VectorBundleKZero X) :
    toddClass C sX (-a) * toddClass C sX a = 1 := by
  simp only [toddClass, map_neg]
  exact (chowGraded C sX).toddOf_neg_mul_toddOf _

theorem isUnit_toddClass (a : VectorBundleKZero X) : IsUnit (toddClass C sX a) :=
  (chowGraded C sX).isUnit_toddOf _

theorem commute_toddClass_ch (a b : VectorBundleKZero X) :
    Commute (toddClass C sX a) (ch C sX b) := by
  have h := commute_weight_ch C sX GradedComplete.toddWeight (fun _ ↦ 1) a b
  rw [GradedComplete.weight_one] at h
  exact (chowGraded C sX).commute_gexp_left ((chowGraded C sX).comp_zero_weight_toddWeight _) h

theorem commute_toddClass_toddClass (a b : VectorBundleKZero X) :
    Commute (toddClass C sX a) (toddClass C sX b) := by
  have h0 := (chowGraded C sX).comp_zero_weight_toddWeight
  exact (chowGraded C sX).commute_gexp_left (h0 _)
    ((chowGraded C sX).commute_gexp_right (h0 _) (commute_weight_ch C sX _ _ a b))

/-- **Multiplicativity of the Todd class on short exact sequences** of finite locally free
modules: `td(E) = td(E') · td(E'')` for `0 → E' → E → E'' → 0`. -/
theorem toddClass_classOf_of_shortExact (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [h₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₁]
    [h₃ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₃] :
    toddClass C sX (VectorBundleKZero.classOf X S.X₂) =
      toddClass C sX (VectorBundleKZero.classOf X S.X₁) *
        toddClass C sX (VectorBundleKZero.classOf X S.X₃) := by
  have h₂ := GenuineChern.isFiniteLocallyFree_of_shortExact S hS h₁ h₃
  have := hS.mono_f
  have := hS.epi_g
  rw [VectorBundleKZero.classOf_shortExact S.f S.g S.zero h₁ h₂ h₃ hS.exact, toddClass_add]

section Invertible

variable (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- The first Chern class `c₁(L)` of an invertible module, in `∏_p A^p(X) ⊗ ℚ` (in degree one). -/
noncomputable def firstChernQ : RationalTotalChowClass C sX :=
  RationalTotalChowClass.ofTotalChowClass (TotalChowClass.firstChernTotal C sX L)

theorem isHom_firstChernQ : (chowGraded C sX).IsHom 1 (firstChernQ C sX L) := fun p hp ↦
  show (1 : ℚ) ⊗ₜ[ℤ] TotalChowClass.firstChernTotal C sX L p = 0 by
    rw [TotalChowClass.firstChernTotal_apply_of_ne C sX L hp, TensorProduct.tmul_zero]

/-- **`ch(L) = e^{c₁(L)}`** for an invertible module `L`. -/
theorem ch_classOf_invertible :
    ch C sX (VectorBundleKZero.classOf X L) =
      (chowGraded C sX).ev (firstChernQ C sX L) (PowerSeries.exp ℚ) := by
  have h1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 :=
    isFiniteLocallyFreeOfRank_one_of_isInvertible L
  have hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
  refine RationalTotalChowClass.ext fun n ↦ ?_
  have hev : (chowGraded C sX).ev (firstChernQ C sX L) (PowerSeries.exp ℚ) n =
      PowerSeries.coeff n (PowerSeries.exp ℚ) • ((firstChernQ C sX L ^ n) n :
        rationalChowCohomologyComponent C (gysinSystemOfInvertible C) sX n) :=
    (chowGraded C sX).comp_ev_of_isHom (isHom_firstChernQ C sX L) (PowerSeries.exp ℚ) n
  rw [hev, ch_apply, chernCharacterVectorBundle_apply, powerSumKHom_classOf,
    powerSumOfFiniteLocallyFree_eq_powerSumTotal C sX L 1, powerSumTotal_of_rank_one,
    ← TotalChowClass.firstChernTotal_eq_homComponent_totalChern, firstChernQ,
    ← map_pow RationalTotalChowClass.ofTotalChowClass,
    RationalTotalChowClass.ofTotalChowClass_apply, PowerSeries.coeff_exp, TensorProduct.smul_tmul',
    Algebra.algebraMap_self_apply, smul_eq_mul, mul_one, one_div]

/-- **`td(L) = c₁(L) / (1 - e^{-c₁(L)})`** for an invertible module `L`: the Todd class of a line
bundle is the Todd power series evaluated at its first Chern class. -/
theorem toddClass_classOf_invertible :
    toddClass C sX (VectorBundleKZero.classOf X L) =
      (chowGraded C sX).ev (firstChernQ C sX L) toddSeries := by
  rw [toddClass, ch_classOf_invertible,
    (chowGraded C sX).toddOf_ev_exp (isHom_firstChernQ C sX L)]

end Invertible

end GRR
