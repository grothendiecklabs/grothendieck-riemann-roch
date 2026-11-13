import GRR.Projection
import GRR.ClosedImmersion
import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.FreeTower.IntegralModel
import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Formula
import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.CapPowCommute
import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFlat
import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedHomogeneousComposite
import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.CanonicalDiagonalFlat
import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.SmoothCapFundamentalProduct
import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClassTensor
import StacksFrontier.AlgebraicGeometry.Chow.ChernCapDivisorInduction

/-!
# The twisted classes generate `K'₀(ℙⁿ_Y)` rationally

For `Y` smooth, separated and of finite type over a field `k`, `π : ℙⁿ_Y ⟶ Y` and
`h = c₁(𝒪(1))`, this file proves `GRR.ProjectionGeneration`: a positive multiple of every class
of `K'₀(ℙⁿ_Y)` is `∑_{j ≤ n} [𝒪(-j)] · π^* β_j` (`GRR.projectionGeneration`).

Through `α ↦ ch(α) ∩ [ℙⁿ_Y]` (Stacks 0FEY) this is a statement on `CH_*(ℙⁿ_Y) ⊗ ℚ`. There every
class is `∑_{i ≤ n} h^i ∩ π^! y_i` (Stacks 02TX along the projective tower `ℙⁿ_Y ⟶ Y`, and
Stacks 0FF4: the Gysin map of the flat `π` is flat pullback),
`π^!(ch(b) ∩ [Y]) = ch(π^* b) ∩ [ℙⁿ_Y]` (Stacks 0FF8), `h^{n+1} = 0`, `ch(𝒪(-j)) = e^{-jh}`, and
`x^i` is a combination of the `e^{-jx}`, `j ≤ n`, modulo `x^{n+1}`. Denominators are cleared at
the end.
-/

open AlgebraicGeometry CategoryTheory Stacks.Chow
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)
open scoped TensorProduct

universe u

namespace GRR

namespace ProjectionGen

/-! ### (a) Powers of `x` modulo `x^{n+1}` as combinations of the `e^{-jx}` -/

section PowerSeriesAlgebra

open PowerSeries

/-- `F` is a combination of the `e^{-jx}`, `j ≤ n`, modulo `x^{n+1}`. -/
def IsTwistCombination (n : ℕ) (F : ℚ⟦X⟧) : Prop :=
  ∃ (c : ℕ → ℚ) (G : ℚ⟦X⟧),
    F = ∑ j ∈ Finset.range (n + 1), c j • expNeg ^ j + PowerSeries.X ^ (n + 1) * G

theorem IsTwistCombination.add {n : ℕ} {F F' : ℚ⟦X⟧} (h : IsTwistCombination n F)
    (h' : IsTwistCombination n F') : IsTwistCombination n (F + F') := by
  obtain ⟨c, G, rfl⟩ := h
  obtain ⟨c', G', rfl⟩ := h'
  refine ⟨c + c', G + G', ?_⟩
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, mul_add]
  abel

theorem IsTwistCombination.smul {n : ℕ} {F : ℚ⟦X⟧} (q : ℚ) (h : IsTwistCombination n F) :
    IsTwistCombination n (q • F) := by
  obtain ⟨c, G, rfl⟩ := h
  refine ⟨q • c, q • G, ?_⟩
  simp only [Pi.smul_apply, smul_add, Finset.smul_sum, smul_smul, mul_smul_comm, smul_eq_mul]

theorem IsTwistCombination.sub {n : ℕ} {F F' : ℚ⟦X⟧} (h : IsTwistCombination n F)
    (h' : IsTwistCombination n F') : IsTwistCombination n (F - F') := by
  rw [sub_eq_add_neg, ← neg_one_smul ℚ F']
  exact h.add (h'.smul (-1))

theorem isTwistCombination_X_pow_mul (n : ℕ) (G : ℚ⟦X⟧) :
    IsTwistCombination n (PowerSeries.X ^ (n + 1) * G) :=
  ⟨0, G, by simp⟩

/-- `(1 - e^{-x})^m` is a combination of the `e^{-jx}`, `j ≤ m`. -/
theorem isTwistCombination_one_sub_expNeg_pow {n m : ℕ} (hm : m ≤ n) :
    IsTwistCombination n ((1 - expNeg) ^ m) := by
  refine ⟨fun j ↦ ((1 - Polynomial.X : Polynomial ℚ) ^ m).coeff j, 0, ?_⟩
  have hdeg : ((1 - Polynomial.X : Polynomial ℚ) ^ m).natDegree < n + 1 := by
    have h1 : (1 - Polynomial.X : Polynomial ℚ).natDegree ≤ 1 := by
      rw [sub_eq_add_neg, ← Polynomial.C_1]
      exact (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) (by simp))
    have := Polynomial.natDegree_pow_le_of_le m h1
    omega
  rw [mul_zero, add_zero, ← Polynomial.aeval_eq_sum_range' hdeg]
  simp

/-- `1 - e^{-x} = x · V` with `V(0) = 1`. -/
theorem exists_one_sub_expNeg_eq :
    ∃ V : ℚ⟦X⟧, 1 - expNeg = PowerSeries.X * V ∧ constantCoeff V = 1 := by
  obtain ⟨V, hV⟩ : PowerSeries.X ∣ (1 - expNeg : ℚ⟦X⟧) := by
    rw [X_dvd_iff, map_sub, map_one, ← coeff_zero_eq_constantCoeff_apply, coeff_expNeg]
    simp
  refine ⟨V, hV, ?_⟩
  have h := congrArg (coeff 1) hV
  rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply, map_sub, coeff_one, coeff_expNeg] at h
  rw [← h]
  simp

/-- `(1 - e^{-x})^m = x^m + x^{m+1} · U`. -/
theorem exists_one_sub_expNeg_pow_eq (m : ℕ) :
    ∃ U : ℚ⟦X⟧, (1 - expNeg) ^ m = PowerSeries.X ^ m + PowerSeries.X ^ (m + 1) * U := by
  obtain ⟨V, hV, hV0⟩ := exists_one_sub_expNeg_eq
  obtain ⟨U, hU⟩ : PowerSeries.X ∣ (V ^ m - 1 : ℚ⟦X⟧) := by
    rw [X_dvd_iff, map_sub, map_pow, hV0, one_pow, map_one, sub_self]
  refine ⟨U, ?_⟩
  rw [hV, mul_pow, show V ^ m = 1 + PowerSeries.X * U by rw [← hU]; ring]
  ring

/-- `x^m F` is a combination of the `e^{-jx}`, `j ≤ n`, modulo `x^{n+1}`, by descending
induction on `m`. -/
theorem isTwistCombination_X_pow_mul_of (n : ℕ) :
    ∀ d m : ℕ, n + 1 ≤ m + d → ∀ F : ℚ⟦X⟧,
      IsTwistCombination n (PowerSeries.X ^ m * F) := by
  intro d
  induction d with
  | zero =>
    intro m hm F
    obtain ⟨e, rfl⟩ : ∃ e, m = n + 1 + e := ⟨m - (n + 1), by omega⟩
    rw [pow_add, mul_assoc]
    exact isTwistCombination_X_pow_mul n _
  | succ d ih =>
    intro m hm F
    by_cases hmn : n + 1 ≤ m
    · exact ih m (by omega) F
    · obtain ⟨U, hU⟩ := exists_one_sub_expNeg_pow_eq m
      obtain ⟨F', hF'⟩ : PowerSeries.X ∣ (F - PowerSeries.C (constantCoeff F) : ℚ⟦X⟧) := by
        rw [X_dvd_iff, map_sub, constantCoeff_C, sub_self]
      have hXm : PowerSeries.X ^ m = (1 - expNeg) ^ m - PowerSeries.X ^ (m + 1) * U := by
        rw [hU]; ring
      have hF : PowerSeries.X ^ m * F =
          constantCoeff F • PowerSeries.X ^ m + PowerSeries.X ^ (m + 1) * F' := by
        rw [smul_eq_C_mul, pow_succ, mul_assoc, ← hF']
        ring
      rw [hF, hXm]
      exact ((isTwistCombination_one_sub_expNeg_pow (by omega)).sub
        (ih (m + 1) (by omega) U)).smul _ |>.add (ih (m + 1) (by omega) F')

/-- **(a) Powers of `x` modulo `x^{n+1}`**: there are rationals `c_j` with
`x^m ≡ ∑_{j ≤ n} c_j e^{-jx}` modulo `x^{n+1}`. -/
theorem exists_X_pow_eq_sum_expNeg_pow (n m : ℕ) :
    ∃ (c : ℕ → ℚ) (G : ℚ⟦X⟧), (PowerSeries.X : ℚ⟦X⟧) ^ m =
      ∑ j ∈ Finset.range (n + 1), c j • expNeg ^ j + PowerSeries.X ^ (n + 1) * G := by
  have h := isTwistCombination_X_pow_mul_of n (n + 1) m (by omega) 1
  rwa [mul_one] at h

end PowerSeriesAlgebra

/-! ### (b) Clearing denominators in `ℚ ⊗ M` -/

theorem natCast_smul_one_tmul {B : Type*} [AddCommGroup B] (E : ℕ) (b : B) :
    (E : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] b) = (1 : ℚ) ⊗ₜ[ℤ] (E • b) := by
  rw [Nat.cast_smul_eq_nsmul ℚ, TensorProduct.tmul_smul]

/-- Every element of `ℚ ⊗ B` is `1/D ⊗ b`. -/
theorem exists_nat_smul_eq_one_tmul {B : Type*} [AddCommGroup B] (w : ℚ ⊗[ℤ] B) :
    ∃ (D : ℕ) (b : B), 0 < D ∧ (D : ℚ) • w = (1 : ℚ) ⊗ₜ[ℤ] b := by
  induction w using TensorProduct.inductionOn with
  | tmul q b =>
    refine ⟨q.den, q.num • b, q.pos, ?_⟩
    rw [TensorProduct.smul_tmul', smul_eq_mul, Rat.den_mul_eq_num, ← TensorProduct.smul_tmul,
      Int.smul_one_eq_cast]
  | add w w' hw hw' =>
    obtain ⟨D, b, hD, hb⟩ := hw
    obtain ⟨D', b', hD', hb'⟩ := hw'
    refine ⟨D * D', D' • b + D • b', Nat.mul_pos hD hD', ?_⟩
    rw [smul_add, Nat.cast_mul, mul_comm (D : ℚ), mul_smul, hb, mul_comm, mul_smul, hb',
      natCast_smul_one_tmul, natCast_smul_one_tmul, TensorProduct.tmul_add]

/-- The kernel of `B → ℚ ⊗ B` is the torsion subgroup. -/
theorem exists_nsmul_eq_zero_of_one_tmul_eq_zero {B : Type*} [AddCommGroup B] {b : B}
    (h : (1 : ℚ) ⊗ₜ[ℤ] b = 0) : ∃ N : ℕ, 0 < N ∧ N • b = 0 := by
  have : IsLocalizedModule (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ B 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ _).mpr
      (TensorProduct.isBaseChange ℤ B ℚ)
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors ℤ)
    (f := TensorProduct.mk ℤ ℚ B 1) (x₁ := b) (x₂ := 0) (by simpa using h)
  rw [smul_zero] at hc
  have hc0 : (c : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero c
  refine ⟨(c : ℤ).natAbs, Int.natAbs_pos.mpr hc0, ?_⟩
  have hc' : (c : ℤ) • b = 0 := hc
  rcases Int.natAbs_eq (c : ℤ) with h' | h'
  · rw [← natCast_zsmul, ← h', hc']
  · rw [← natCast_zsmul, show ((c : ℤ).natAbs : ℤ) = -(c : ℤ) by omega, neg_smul, hc', neg_zero]

/-- **(b) Clearing denominators.** If `1 ⊗ a = ∑_j (φ_j)_ℚ (w_j)` in `ℚ ⊗ A`, then a positive
multiple of `a` is `∑_j φ_j(b_j)` in `A`. -/
theorem exists_nsmul_eq_sum_of_one_tmul_eq {ι : Type*} {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] (φ : ι → B →+ A) (s : Finset ι) (a : A) (w : ι → ℚ ⊗[ℤ] B)
    (h : (1 : ℚ) ⊗ₜ[ℤ] a = ∑ j ∈ s, ((φ j).toIntLinearMap.baseChange ℚ) (w j)) :
    ∃ N : ℕ, 0 < N ∧ ∃ b : ι → B, N • a = ∑ j ∈ s, φ j (b j) := by
  classical
  have hden : ∀ t : Finset ι, ∃ D : ℕ, 0 < D ∧ ∃ b : ι → B,
      ∀ j ∈ t, (D : ℚ) • w j = (1 : ℚ) ⊗ₜ[ℤ] b j := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨1, one_pos, 0, by simp⟩
    | insert i t hi ih =>
      obtain ⟨D, hD, b, hb⟩ := ih
      obtain ⟨d, b', hd, hb'⟩ := exists_nat_smul_eq_one_tmul (w i)
      refine ⟨D * d, Nat.mul_pos hD hd, fun j ↦ if j = i then D • b' else d • b j, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simp only [↓reduceIte]
        rw [Nat.cast_mul, mul_smul, hb', natCast_smul_one_tmul]
      · have hji : j ≠ i := fun e ↦ hi (e ▸ hj)
        simp only [hji, ↓reduceIte]
        rw [Nat.cast_mul, mul_comm, mul_smul, hb j hj, natCast_smul_one_tmul]
  obtain ⟨D, hD, b, hb⟩ := hden s
  have key : (1 : ℚ) ⊗ₜ[ℤ] (D • a - ∑ j ∈ s, φ j (b j)) = 0 := by
    rw [TensorProduct.tmul_sub, ← natCast_smul_one_tmul, h, Finset.smul_sum,
      TensorProduct.tmul_sum, sub_eq_zero]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [← map_smul, hb j hj, LinearMap.baseChange_tmul, AddMonoidHom.coe_toIntLinearMap]
  obtain ⟨N, hN, hNa⟩ := exists_nsmul_eq_zero_of_one_tmul_eq_zero key
  refine ⟨N * D, Nat.mul_pos hN hD, fun j ↦ N • b j, ?_⟩
  rw [smul_sub, sub_eq_zero, smul_smul, Finset.smul_sum] at hNa
  rw [hNa]
  exact Finset.sum_congr rfl fun j _ ↦ (map_nsmul _ _ _).symm

/-! ### Chow-theoretic preliminaries -/

section FlatGysin

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f] [Flat f]
  (hf : f ≫ sY = sX) (hlci : IsLocalCompleteIntersectionMorphism f) (h : GysinMapExists f)
  (m : ℕ) (hm : AlgebraicGeometry.RelativeDimension f m)

/-- The homogeneous parts of the Gysin map of a flat morphism of relative dimension `m`: the
flat pullback class in degree `-m`, zero in the other degrees.

Provenance: this lemma and `lciGysinRational_of_tmul_of_flat` below restate Stacks 0FF4 as it is
proved in Stacks' own module
`StacksFrontier/AlgebraicGeometry/WeilCohomology/Concrete/ProjectiveBundleRationalChow.lean`,
which is not compiled on this machine; they are reproduced here from that module so that they
compile against the compiled part of Stacks. They are Stacks' results, not this project's. -/
theorem lciGysinMapComponent_eq_single (q : ℤ) :
    lciGysinMapComponent C sX sY hf hlci h q =
      Pi.single (M := fun q : ℤ => BivariantClass C (gysinSystemOfInvertible C) sX sY f hf q)
        (-(m : ℤ)) (flatPullbackBivariantClassOfInvertible C sX sY f hf m hm) q := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  rw [lciGysinMapComponent, lciGysinMap_eq_completedFlatPullbackOfFlatLCI,
    completedFlatPullbackOfFlatLCI, completedFlatPullback_eq_toCompleted C sX sY f hf m hm,
    completedBivariantSequenceOfInvertible_toCompleted]

/-- **Stacks 0FF4 on `CH_*(-) ⊗ ℚ`**: the Gysin map of a flat morphism of relative dimension `m`
sends `r ⊗ β`, `β ∈ CH_k(Y)`, to `r ⊗ f^*β` in degree `k + m`. -/
theorem lciGysinRational_of_tmul_of_flat (k : ℤ) (r : ℚ) (β : chowGroup C sY k) :
    lciGysinRational C sX sY hf hlci h
        (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sY j) k (r ⊗ₜ β)) =
      DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j) (k + m)
        (r ⊗ₜ flatPullbackChow C sX sY f hf m hm k
          (flatPullbackFactorsThroughRationalEquivalence_general C sX sY f hf m hm k) β) := by
  classical
  have hsupp : lciGysinSupport C sX sY hf hlci h ⊆ (({-(m : ℤ)} : Finset ℤ) : Set ℤ) := by
    intro q hq
    by_contra hne
    refine hq ?_
    rw [lciGysinMapComponent_eq_single C sX sY hf hlci h m hm,
      Pi.single_eq_of_ne (by simpa using hne)]
  rw [lciGysinRational_eq_sum C sX sY hf hlci h _ hsupp, Finset.sum_singleton,
    lciGysinRationalComponent, rationalChowMap_of_tmul]
  refine of_tmul_eq_of_tmul_of_heq C sX (by ring) r ?_
  rw [lciGysinChow, BivariantClass.capTargetHom_apply,
    lciGysinMapComponent_eq_single C sX sY hf hlci h m hm, Pi.single_eq_same]
  exact flatPullbackBivariantClass_capTarget_heq C _ sX sY f hf m hm (flatPullbackDescends C) _
    (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C sX sY f hf m hm) k β

end FlatGysin

section FirstChern

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- Capping with `c₁(L) ∈ A^1(X)` is the first Chern class operation `c₁(L) ∩ -` of
Stacks 02SO. -/
theorem chowCohomologyCap_firstChernTotal_heq (k : ℤ) (x : chowGroup C sX k) :
    chowCohomologyCap C (gysinSystemOfInvertible C) sX ((1 : ℕ) : ℤ)
        (TotalChowClass.firstChernTotal C sX L 1) k x ≍
      (invCap C sX L).capOnChow C sX (k - 1) (chowGroupCast C sX (by omega) x) := by
  have := GenuineChern.isInvertible_pullback (𝟙 X) L
  refine (chowCohomologyCap_heq_idRule_ofGysinSystem C _ sX _ _ k x).trans ?_
  refine (heq_of_eq (TotalChowClass.op_apply (TotalChowClass.firstChernTotal C sX L) (𝟙 X) k 1
    _).symm).trans ?_
  refine (TotalChowClass.op_firstChernTotal_one_heq C sX L (𝟙 X) k _).trans ?_
  rw [invCap_capOnChow_congr C (𝟙 X ≫ sX) _ L ((Scheme.Modules.pullbackId X).app L)]
  have h4 := chowGroupCongr_invCap_capOnChow C L (Category.id_comp sX) (k - 1)
    (chowGroupCast C (𝟙 X ≫ sX) (by omega)
      (chowGroupCongr C (Category.id_comp sX).symm k x))
  refine (chowGroupCongr_heq C (Category.id_comp sX) _ _).symm.trans
    ((heq_of_eq h4).trans (heq_of_eq (congrArg _ ?_)))
  exact eq_of_heq ((chowGroupCongr_heq C _ _ _).trans ((chowGroupCast_heq C _ _ _).trans
    ((chowGroupCongr_heq C _ _ _).trans (chowGroupCast_heq C _ _ _).symm)))

/-- The first Chern class operation of a module isomorphic to `𝒪_X` vanishes. -/
theorem invCap_capOnChow_eq_zero_of_iso (e : L ≅ SheafOfModules.unit X.ringCatSheaf) (d : ℤ)
    (x : chowGroup C sX (d + 1)) : (invCap C sX L).capOnChow C sX d x = 0 := by
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
  rw [invCap_capOnChow_mk]
  exact (firstChernClassCapOfInvertible_congr C sX d L _ e c).trans
    (firstChernClassCapOfInvertible_unit C sX d c)

end FirstChern

section Tower

/-- Capping with a power of `ξ` is unchanged by moving between equal degrees. -/
theorem capPow_capOnChow_cast (C : ChowSituation.{u}) {P : Scheme.{u}} (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] (ξ : ChernCapOperator C sP) (s : ℕ) {a a' m b : ℤ} (ha : a = a')
    (h : a = m + s) (h' : a' = m + s) (e : b = a + 1) (e' : b = a' + 1) (x : chowGroup C sP b) :
    capPow C sP ξ s a m h (ξ.capOnChow C sP a (chowGroupCast C sP e x)) =
      capPow C sP ξ s a' m h' (ξ.capOnChow C sP a' (chowGroupCast C sP e' x)) := by
  subst ha; rfl

/-- Pushforward along a closed immersion `i` carries `c₁(i^*L)^s ∩ -` to `c₁(L)^s ∩ -`. -/
theorem properChowPushforward_invCap_capPow (C : ChowSituation.{u}) {D P : Scheme.{u}}
    (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (i : D ⟶ P) [IsClosedImmersion i]
    [LocallyOfFiniteType (i ≫ sP)] (L : P.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible D.sheaf.obj D.ringCatSheaf.property
      ((Scheme.Modules.pullback i).obj L)]
    (s : ℕ) (a m : ℤ) (h : a = m + s) (x : chowGroup C (i ≫ sP) a) :
    properChowPushforward C (i ≫ sP) sP i rfl m
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sP i rfl m)
        (capPow C (i ≫ sP) (invCap C (i ≫ sP) ((Scheme.Modules.pullback i).obj L)) s a m h x) =
      capPow C sP (invCap C sP L) s a m h
        (properChowPushforward C (i ≫ sP) sP i rfl a
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sP i rfl a) x) :=
  capPow_comm C sP (invCap C sP L) (i ≫ sP)
    (invCap C (i ≫ sP) ((Scheme.Modules.pullback i).obj L))
    (fun d ↦ properChowPushforward C (i ≫ sP) sP i rfl d
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sP i rfl d))
    (fun d x ↦ properChowPushforward_invCap C (i ≫ sP) sP i rfl L d x) s a m h x

/-- **`c₁(L)^{n+1} ∩ π^*β = 0` along a projective tower of fibre dimension `n`.** By induction
along the tower: at the bottom `L` is trivial; in fibre dimension `n + 1`,
`c₁(L) ∩ π^*β = i_*((π|_D)^*β)` (Stacks 02TR) and the remaining caps commute with `i_*`
(Stacks 02SU). -/
theorem capPow_bundlePullback_eq_zero (C : ChowSituation.{u}) {n : ℕ} {P U : Scheme.{u}}
    {π : P ⟶ U} {L : P.Modules} (h : IsProjectiveTower n π L) :
    ∀ (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
      (hsP : π ≫ sU = sP)
      [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
      [LocallyOfFiniteType π] [Flat π]
      (hπ : AlgebraicGeometry.RelativeDimension π n) (k : ℤ) (β : chowGroup C sU k),
      capPow C sP (invCap C sP L) (n + 1) (k + n) (k - 1) (by push_cast; ring)
        (bundlePullback C sU sP π hsP n hπ k β) = 0 := by
  induction h with
  | zero π L hiso hL =>
    intro sU _ sP _ hsP _ _ _ hπ k β
    obtain ⟨e⟩ := hL
    rw [capPow_succ_apply, invCap_capOnChow_eq_zero_of_iso C sP L e, map_zero]
  | succ n π L hπ' s hD hq htower haff ih =>
    intro sU _ sP _ hsP _ _ _ hπ k β
    have := hD.2
    set i := (Stacks.Divisors.zeroScheme _ L s).subschemeι with hi
    let : AlgebraicGeometry.SheafOfModules.IsInvertible _ _
        ((Scheme.Modules.pullback i).obj L) := isInvertible_presheaf_modulePullback L i
    have hstep := capOnChow_bundlePullback_eq C sU sP π hsP n hπ L s hD hq k β
    have hIH := ih sU (i ≫ sP) (by rw [Category.assoc, hsP]) hq k β
    rw [capPow_succ_apply, capPow_capOnChow_cast C sP (invCap C sP L) (n + 1) (a' := k + n)
      (by push_cast; ring) _ (by push_cast; ring) _ (by push_cast; ring), hstep,
      ← properChowPushforward_invCap_capPow C sP i L (n + 1) (k + n) (k - 1)
        (by push_cast; ring), hIH, map_zero]

end Tower

section CapFirstChern

variable (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- The cap action of `c₁(L)` on `r ⊗ z`, `z ∈ CH_a(X)`, is `r ⊗ (c₁(L) ∩ z)`. -/
theorem cap_firstChernQ_of (a : ℤ) (r : ℚ) (z : chowGroup (fieldChowSituation k) sX a) :
    cap k sX (firstChernQ (fieldChowSituation k) sX L)
        (DirectSum.of (fun j : ℤ ↦ ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sX j) a (r ⊗ₜ z)) =
      DirectSum.of (fun j : ℤ ↦ ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sX j) (a - 1)
        (r ⊗ₜ (invCap (fieldChowSituation k) sX L).capOnChow (fieldChowSituation k) sX (a - 1)
          (chowGroupCast (fieldChowSituation k) sX (by omega) z)) := by
  rw [cap, ← DirectSum.lof_eq_of ℚ,
    totalRationalChowCap_lof_eq_sum (fieldChowSituation k)
      (gysinSystemOfInvertible (fieldChowSituation k)) sX 0
      (relativeDimension_fieldChowSituation_nonneg k sX)
      _ a _ (Finset.range (a.toNat + 2)) (fun p hp ↦ by rw [Finset.mem_range]; omega),
    Finset.sum_eq_single 1]
  · rw [RationalTotalChowClass.ofFamily_symm_apply, firstChernQ,
      RationalTotalChowClass.ofTotalChowClass_apply, DirectSum.lof_eq_of, rationalChowCap_of_tmul,
      one_mul]
    exact of_tmul_eq_of_tmul_of_heq (fieldChowSituation k) sX (by simp) r
      (chowCohomologyCap_firstChernTotal_heq (fieldChowSituation k) sX L a z)
  · intro p _ hp
    rw [RationalTotalChowClass.ofFamily_symm_apply, firstChernQ,
      RationalTotalChowClass.ofTotalChowClass_apply,
      TotalChowClass.firstChernTotal_apply_of_ne (fieldChowSituation k) sX L hp,
      TensorProduct.tmul_zero, map_zero, LinearMap.zero_apply]
  · intro h1
    exact absurd (Finset.mem_range.mpr (by omega)) h1

/-- The cap action of `c₁(L)^i` on `r ⊗ z`, `z ∈ CH_a(X)`, is `r ⊗ (c₁(L)^i ∩ z)`. -/
theorem cap_firstChernQ_pow_of (i : ℕ) (a m : ℤ) (h : a = m + i) (r : ℚ)
    (z : chowGroup (fieldChowSituation k) sX a) :
    (cap k sX (firstChernQ (fieldChowSituation k) sX L) ^ i)
        (DirectSum.of (fun j : ℤ ↦ ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sX j) a (r ⊗ₜ z)) =
      DirectSum.of (fun j : ℤ ↦ ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sX j) m
        (r ⊗ₜ capPow (fieldChowSituation k) sX (invCap (fieldChowSituation k) sX L) i a m h z) := by
  induction i generalizing m with
  | zero =>
    rw [pow_zero, Module.End.one_apply, capPow_zero_apply]
    exact of_tmul_eq_of_tmul_of_heq (fieldChowSituation k) sX (by simpa using h) r
      (chowGroupCast_heq (fieldChowSituation k) sX _ _).symm
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply, ih (m + 1) (by push_cast at h; omega),
      cap_firstChernQ_of, capPow_succ_apply']
    exact of_tmul_eq_of_tmul_of_heq (fieldChowSituation k) sX (by ring) r
      (ChernCapOperator.capOnChow_heq (fieldChowSituation k) sX _ (by ring)
        (chowGroupCast_heq (fieldChowSituation k) sX _ _))

theorem cap_add (c d : AQ k sX) : cap k sX (c + d) = cap k sX c + cap k sX d := by
  simp only [cap, map_add]

theorem cap_smul (q : ℚ) (c : AQ k sX) : cap k sX (q • c) = q • cap k sX c := by
  simp only [cap, map_smul]

theorem cap_sum {ι : Type*} (s : Finset ι) (c : ι → AQ k sX) :
    cap k sX (∑ i ∈ s, c i) = ∑ i ∈ s, cap k sX (c i) := by
  simp only [cap, map_sum]

theorem cap_one : cap k sX 1 = 1 :=
  totalRationalChowCap_one (fieldChowSituation k) sX

theorem cap_pow (c : AQ k sX) (i : ℕ) : cap k sX (c ^ i) = cap k sX c ^ i := by
  induction i with
  | zero => rw [pow_zero, pow_zero, cap_one]
  | succ i ih => rw [pow_succ, pow_succ, cap_mul, ih]

/-- `ch(a) ∩ -` is the cap action of `ch(a)`. -/
theorem cap_ch (a : VectorBundleKZero X) :
    cap k sX (ch (fieldChowSituation k) sX a) = chernCharacterCap (fieldChowSituation k) sX a := by
  rw [cap, ch, rationalTotalChernCharacterRingHom_apply, LinearEquiv.symm_apply_apply]
  rfl

/-- `ch(t) ∩ (ch(z) ∩ [X]) = ch(t z) ∩ [X]`. -/
theorem chernCharacterCap_rationalChernCharacterCapFundamentalClass [IsNoetherian X]
    (t : VectorBundleKZero X) (z : ℚ ⊗[ℤ] VectorBundleKZero X) :
    chernCharacterCap (fieldChowSituation k) sX t
        (rationalChernCharacterCapFundamentalClass (fieldChowSituation k) sX z) =
      rationalChernCharacterCapFundamentalClass (fieldChowSituation k) sX
        ((1 : ℚ) ⊗ₜ[ℤ] t * z) := by
  rw [rationalChernCharacterCapFundamentalClass_apply,
    rationalChernCharacterCapFundamentalClass_apply,
    rationalChernCharacterCap_mul (fieldChowSituation k) sX 0
      (relativeDimension_fieldChowSituation_nonneg k sX),
    Module.End.mul_apply, rationalChernCharacterCap_tmul, one_smul]

end CapFirstChern

section Twist

variable {Y : Scheme.{u}} (n : ℕ)

theorem isFiniteLocallyFree_twistOver (d : ℤ) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u}
      (R := (projectiveSpaceOver n Y).ringCatSheaf) (twistOver n Y d) := by
  have := isFiniteLocallyFreeOfRank_one_of_isInvertible (twistOver n Y d)
  have := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (twistOver n Y d) 1
  exact Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree _

/-- `[𝒪(a)] · [𝒪(b)] = [𝒪(a + b)]`. -/
theorem twistClass_mul (a b : ℤ) :
    twistClass Y n a * twistClass Y n b = twistClass Y n (a + b) := by
  have := isFiniteLocallyFree_twistOver (Y := Y) n a
  have := isFiniteLocallyFree_twistOver (Y := Y) n b
  rw [twistClass, twistClass, twistClass, VectorBundleKZero.classOf_mul _ _
    (isFiniteLocallyFree_twistOver n a) (isFiniteLocallyFree_twistOver n b)]
  exact VectorBundleKZero.classOf_eq_of_iso
    (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOverMulIso n Y a b)
    (AlgebraicGeometry.isFiniteLocallyFree_tensorObj _ _)

/-- `[𝒪(0)] = 1`. -/
theorem twistClass_zero : twistClass Y n 0 = 1 := by
  rw [twistClass, ← VectorBundleKZero.classOf_unit]
  exact VectorBundleKZero.classOf_eq_of_iso
    (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistZeroIsoUnit n Y)
    (isFiniteLocallyFree_twistOver n 0)

/-- `[𝒪(-j)] = [𝒪(-1)]^j`. -/
theorem twistClass_neg_natCast (j : ℕ) :
    twistClass Y n (-(j : ℤ)) = twistClass Y n (-1) ^ j := by
  induction j with
  | zero => rw [Nat.cast_zero, neg_zero, pow_zero, twistClass_zero]
  | succ j ih =>
    rw [pow_succ, ← ih, twistClass_mul]
    congr 1
    push_cast
    ring

/-- `ℙⁿ_Y ⟶ Y` with `𝒪(1)` is a projective tower of fibre dimension `n`. -/
theorem isProjectiveTower_twistOver :
    IsProjectiveTower n (projectiveSpaceOver n Y ↘ Y) (twistOver n Y 1) :=
  FreeTower.isProjectiveTower_projectiveSpaceOver n Y

end Twist

/-! ### (c)–(f) on `ℙⁿ_Y` -/

section Projective

variable (k : Type u) [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsSmoothFT k sY]
  (n : ℕ)

/-- **(c) `ch(𝒪(-j)) = e^{-jh}`** on `ℙⁿ_Y`, `h = c₁(𝒪(1))`. -/
theorem ch_twistClass_neg (j : ℕ) :
    ch (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
        (twistClass Y n (-(j : ℤ))) =
      (chowGraded (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)).ev
        (firstChernQ (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
          (twistOver n Y 1)) (expNeg ^ j) := by
  have hh0 : (chowGraded (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)).comp 0
      (firstChernQ (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
        (twistOver n Y 1)) = 0 :=
    isHom_firstChernQ (fieldChowSituation k) _ (twistOver n Y 1) 0 zero_ne_one
  have h1 : ch (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY) (twistClass Y n 1) =
      (chowGraded (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)).ev
        (firstChernQ (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
          (twistOver n Y 1)) (PowerSeries.exp ℚ) :=
    ch_classOf_invertible (fieldChowSituation k) _ (twistOver n Y 1)
  have hprod : ch (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
      (twistClass Y n 1) *
      ch (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY) (twistClass Y n (-1)) =
        1 := by
    rw [← map_mul, twistClass_mul, add_neg_cancel, twistClass_zero, map_one]
  have hinv : (chowGraded (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)).ev
        (firstChernQ (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
          (twistOver n Y 1)) expNeg *
      (chowGraded (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)).ev
        (firstChernQ (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
          (twistOver n Y 1)) (PowerSeries.exp ℚ) = 1 := by
    rw [← GradedComplete.ev_mul _ hh0, expNeg_mul_exp, GradedComplete.ev_one _ hh0]
  have hm1 : ch (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
      (twistClass Y n (-1)) =
      (chowGraded (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)).ev
        (firstChernQ (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
          (twistOver n Y 1)) expNeg := by
    rw [← mul_one ((chowGraded (fieldChowSituation k) _).ev _ expNeg), ← hprod, h1, ← mul_assoc,
      hinv, one_mul]
  rw [twistClass_neg_natCast, map_pow, hm1, GradedComplete.ev_pow _ hh0]

/-- Stacks 0FF4 for the projection `π : ℙⁿ_Y ⟶ Y`: `π^!(r ⊗ β) = r ⊗ π^*β`. -/
theorem smoothGysinRational_of_tmul (d : ℤ) (r : ℚ) (β : chowGroup (fieldChowSituation k) sY d) :
    smoothGysinRational ((projectiveSpaceOver n Y ↘ Y) ≫ sY) sY rfl
        (DirectSum.of (fun j : ℤ ↦ ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sY j) d (r ⊗ₜ β)) =
      DirectSum.of (fun j : ℤ ↦
          ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY) j) (d + n)
        (r ⊗ₜ bundlePullback (fieldChowSituation k) sY ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
          (projectiveSpaceOver n Y ↘ Y) rfl n (relativeDimension_projectiveSpaceOver n Y) d β) :=
  lciGysinRational_of_tmul_of_flat (fieldChowSituation k) _ sY rfl _ _ n
    (relativeDimension_projectiveSpaceOver n Y) d r β

/-- **(d) The projective bundle formula on `CH_*(ℙⁿ_Y) ⊗ ℚ`** (Stacks 02TX): every class is
`∑_{i ≤ n} h^i ∩ π^! y_i`. -/
theorem exists_eq_sum_cap_pow_smoothGysinRational
    (x : CHQ k ((projectiveSpaceOver n Y ↘ Y) ≫ sY)) :
    ∃ y : Fin (n + 1) → CHQ k sY,
      x = ∑ i : Fin (n + 1), (cap k ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
          (firstChernQ (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
            (twistOver n Y 1)) ^ (i : ℕ))
        (smoothGysinRational ((projectiveSpaceOver n Y ↘ Y) ≫ sY) sY rfl (y i)) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add x x' hx hx' =>
    obtain ⟨y, hy⟩ := hx
    obtain ⟨y', hy'⟩ := hx'
    exact ⟨y + y', by rw [hy, hy']; simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]⟩
  | of j t =>
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' =>
      obtain ⟨y, hy⟩ := ht
      obtain ⟨y', hy'⟩ := ht'
      exact ⟨y + y', by
        rw [map_add, hy, hy']; simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]⟩
    | tmul r z =>
      have hj : j = (j - n) + n := by ring
      obtain ⟨β, hβ⟩ := (isProjectiveTower_twistOver n (Y := Y)).bundleMap_surjective
        (fieldChowSituation k) (affineBundleSurjectivity _) sY
        ((projectiveSpaceOver n Y ↘ Y) ≫ sY) rfl (relativeDimension_projectiveSpaceOver n Y)
        (j - n) (chowGroupCast (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY) hj z)
      refine ⟨fun i ↦ DirectSum.of (fun j : ℤ ↦ ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sY j)
        (j - n + (i : ℕ)) (r ⊗ₜ β i), ?_⟩
      have hterm : ∀ i : Fin (n + 1), (cap k ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
          (firstChernQ (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
            (twistOver n Y 1)) ^ (i : ℕ))
          (smoothGysinRational ((projectiveSpaceOver n Y ↘ Y) ≫ sY) sY rfl
            (DirectSum.of (fun j : ℤ ↦ ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sY j)
              (j - n + (i : ℕ)) (r ⊗ₜ β i))) =
          DirectSum.of (fun j : ℤ ↦ ℚ ⊗[ℤ] chowGroup (fieldChowSituation k)
              ((projectiveSpaceOver n Y ↘ Y) ≫ sY) j) (j - n + n)
            (r ⊗ₜ bundleTerm (fieldChowSituation k) sY ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
              (projectiveSpaceOver n Y ↘ Y) rfl n (relativeDimension_projectiveSpaceOver n Y)
              (invCap (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
                (twistOver n Y 1)) (j - n) i (β i)) := by
        intro i
        rw [smoothGysinRational_of_tmul, cap_firstChernQ_pow_of k _ (twistOver n Y 1) i _
          (j - n + n) (by ring)]
        rfl
      rw [Finset.sum_congr rfl fun i _ ↦ hterm i, ← map_sum, ← TensorProduct.tmul_sum,
        ← bundleMap_apply, hβ]
      exact of_tmul_eq_of_tmul_of_heq (fieldChowSituation k) _ hj r
        (chowGroupCast_heq (fieldChowSituation k) _ _ _).symm

omit [IsSmoothFT k sY] in
/-- **(e) The Gysin map on `ch(y) ∩ [Y]`**: `f^!(ch(y) ∩ [Y]) = ch(f^* y) ∩ [X]` for a morphism
`f` of smooth schemes over `k` (Stacks 0FF8); for `π` the Gysin map is flat pullback by
`smoothGysinRational_of_tmul`. -/
theorem smoothGysinRational_rationalChernCharacterCapFundamentalClass {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [Smooth sX]
    [Smooth sY] [IsNoetherian X] [IsNoetherian Y] {f : X ⟶ Y} [LocallyOfFiniteType f]
    (hf : f ≫ sY = sX) (y : ℚ ⊗[ℤ] VectorBundleKZero Y) :
    smoothGysinRational sX sY hf
        (rationalChernCharacterCapFundamentalClass (fieldChowSituation k) sY y) =
      rationalChernCharacterCapFundamentalClass (fieldChowSituation k) sX
        ((VectorBundleKZero.pullback f).toIntLinearMap.baseChange ℚ y) := by
  rw [rationalChernCharacterCapFundamentalClass_apply,
    rationalChernCharacterCapFundamentalClass_apply,
    smoothGysinRational_rationalChernCharacterCap, smoothGysinRational_rationalFundamentalClass]

/-- `h^{n+1} ∩ π^! y = 0`. -/
theorem cap_pow_succ_smoothGysinRational (y : CHQ k sY) :
    (cap k ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
        (firstChernQ (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
          (twistOver n Y 1)) ^ (n + 1))
      (smoothGysinRational ((projectiveSpaceOver n Y ↘ Y) ≫ sY) sY rfl y) = 0 := by
  induction y using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | add y y' hy hy' => rw [map_add, map_add, hy, hy', add_zero]
  | of d t =>
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' => rw [map_add, map_add, map_add, ht, ht', add_zero]
    | tmul r β =>
      rw [smoothGysinRational_of_tmul, cap_firstChernQ_pow_of k _ (twistOver n Y 1) (n + 1) _
          (d - 1) (by push_cast; ring),
        capPow_bundlePullback_eq_zero (fieldChowSituation k) (isProjectiveTower_twistOver n) sY
          _ rfl _ d β, TensorProduct.tmul_zero, map_zero]

/-- **(f) `h^{n+1} = 0`** as an operator on `CH_*(ℙⁿ_Y) ⊗ ℚ`. -/
theorem cap_firstChernQ_pow_succ_eq_zero :
    cap k ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
        (firstChernQ (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
          (twistOver n Y 1)) ^ (n + 1) = 0 := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨y, rfl⟩ := exists_eq_sum_cap_pow_smoothGysinRational k sY n x
  rw [map_sum, LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [← Module.End.mul_apply, (Commute.pow_pow_self _ (n + 1) (i : ℕ)).eq,
    Module.End.mul_apply, cap_pow_succ_smoothGysinRational, map_zero]

/-- `h^i ∩ -` is a combination of the operators `ch(𝒪(-j)) ∩ -`, `j ≤ n`: by (a), (c), (f). -/
theorem exists_cap_pow_eq_sum (i : ℕ) :
    ∃ c : ℕ → ℚ, cap k ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
        (firstChernQ (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
          (twistOver n Y 1)) ^ i =
      ∑ j ∈ Finset.range (n + 1), c j • chernCharacterCap (fieldChowSituation k)
        ((projectiveSpaceOver n Y ↘ Y) ≫ sY) (twistClass Y n (-(j : ℤ))) := by
  obtain ⟨c, G, hX⟩ := exists_X_pow_eq_sum_expNeg_pow n i
  refine ⟨c, ?_⟩
  have hh0 : (chowGraded (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)).comp 0
      (firstChernQ (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
        (twistOver n Y 1)) = 0 :=
    isHom_firstChernQ (fieldChowSituation k) _ (twistOver n Y 1) 0 zero_ne_one
  have key := congrArg (fun F ↦ cap k ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
    ((chowGraded (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)).ev
      (firstChernQ (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
        (twistOver n Y 1)) F)) hX
  simp only at key
  rw [GradedComplete.ev_pow _ hh0, GradedComplete.ev_X _ hh0, cap_pow, GradedComplete.ev_add,
    GradedComplete.ev_mul _ hh0, cap_add, cap_mul, GradedComplete.ev_pow _ hh0 PowerSeries.X,
    GradedComplete.ev_X _ hh0, cap_pow, cap_firstChernQ_pow_succ_eq_zero, zero_mul, add_zero,
    GradedComplete.ev_sum, cap_sum] at key
  rw [key]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [GradedComplete.ev_smul, cap_smul, ← ch_twistClass_neg, cap_ch]

/-- The base change of `b ↦ t · f(b)` is `w ↦ (1 ⊗ t) · f_ℚ(w)`. -/
theorem baseChange_mulLeft_comp {A B : Type*} [CommRing A] [AddCommGroup B] (t : A) (f : B →+ A)
    (w : ℚ ⊗[ℤ] B) :
    ((AddMonoidHom.mulLeft t).comp f).toIntLinearMap.baseChange ℚ w =
      (1 : ℚ) ⊗ₜ[ℤ] t * f.toIntLinearMap.baseChange ℚ w := by
  induction w using TensorProduct.inductionOn with
  | tmul q b =>
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul]
    rfl
  | add w w' hw hw' => rw [map_add, map_add, hw, hw', mul_add]

include k sY in
/-- **The twisted classes generate `K₀(Vect ℙⁿ_Y) ⊗ ℚ`**:
`1 ⊗ a = ∑_{j ≤ n} [𝒪(-j)] · π^* W_j`. -/
theorem exists_one_tmul_eq_sum (a : VectorBundleKZero (projectiveSpaceOver n Y)) :
    ∃ W : ℕ → ℚ ⊗[ℤ] VectorBundleKZero Y,
      (1 : ℚ) ⊗ₜ[ℤ] a = ∑ j ∈ Finset.range (n + 1),
        (((AddMonoidHom.mulLeft (twistClass Y n (-(j : ℤ)))).comp
          (VectorBundleKZero.pullback (projectiveSpaceOver n Y ↘ Y))).toIntLinearMap.baseChange ℚ)
          (W j) := by
  have := isNoetherian k sY
  have := isNoetherian k ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
  have := compactSpace k sY
  have := compactSpace k ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
  have := isAffineHom_diagonal k sY
  have := isAffineHom_diagonal k ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
  have hinj : Function.Injective (rationalChernCharacterCapFundamentalClass (fieldChowSituation k)
      ((projectiveSpaceOver n Y ↘ Y) ≫ sY)) :=
    (bijective_rationalChernCharacterCapFundamentalClass (fieldChowSituation k) _
      (isRegular k ((projectiveSpaceOver n Y ↘ Y) ≫ sY))
      (exists_bounds_relativeDimension_fieldChowSituation k _)).1
  have hsurj : Function.Surjective
      (rationalChernCharacterCapFundamentalClass (fieldChowSituation k) sY) :=
    (bijective_rationalChernCharacterCapFundamentalClass (fieldChowSituation k) sY
      (isRegular k sY) (exists_bounds_relativeDimension_fieldChowSituation k sY)).2
  obtain ⟨y, hy⟩ := exists_eq_sum_cap_pow_smoothGysinRational k sY n
    (rationalChernCharacterCapFundamentalClass (fieldChowSituation k)
      ((projectiveSpaceOver n Y ↘ Y) ≫ sY) ((1 : ℚ) ⊗ₜ[ℤ] a))
  choose w hw using fun i ↦ hsurj (y i)
  choose c hc using fun i : Fin (n + 1) ↦ exists_cap_pow_eq_sum k sY n (i : ℕ)
  refine ⟨fun j ↦ ∑ i : Fin (n + 1), c i j • w i, hinj ?_⟩
  rw [hy]
  simp only [← hw, smoothGysinRational_rationalChernCharacterCapFundamentalClass, hc,
    LinearMap.sum_apply, LinearMap.smul_apply,
    chernCharacterCap_rationalChernCharacterCapFundamentalClass, map_sum, baseChange_mulLeft_comp,
    map_smul]
  exact Finset.sum_comm

end Projective

end ProjectionGen

/-- **(g) The twisted classes generate `K'₀(ℙⁿ_Y)` rationally** (`GRR.ProjectionGeneration`): a
positive multiple of every class of `K'₀(ℙⁿ_Y)` is a sum of classes `[𝒪(-j)] · π^* β_j`,
`0 ≤ j ≤ n`. -/
theorem projectionGeneration (k : Type u) [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    [IsSmoothFT k sY] (n : ℕ) : ProjectionGeneration k sY n := by
  intro α
  obtain ⟨W, hW⟩ := ProjectionGen.exists_one_tmul_eq_sum k sY n
    ((vectorBundleEquiv k ((projectiveSpaceOver n Y ↘ Y) ≫ sY)).symm α)
  obtain ⟨N, hN, β, hβ⟩ := ProjectionGen.exists_nsmul_eq_sum_of_one_tmul_eq _ _ _ W hW
  refine ⟨N, hN, β, ?_⟩
  have h := congrArg (vectorBundleEquiv k ((projectiveSpaceOver n Y ↘ Y) ≫ sY)) hβ
  rw [map_nsmul, AddEquiv.apply_symm_apply, map_sum] at h
  rw [h]
  rfl

end GRR
