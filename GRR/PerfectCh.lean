import Mathlib
import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.ChernCharacterFundamentalClass
import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.DerivedTensor
import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PerfectPowerSumChernCharacter
import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PerfectChernProperties
import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.BabyCaseTensor
import GRR.ClosedImmersion

/-!
# The Chern character of perfect complexes

For `K ∈ D(𝒪_Y)` whose Chern classes are defined (Stacks 0F9E), `GRR.perfectCh C sY hK` is its
Chern character `ch(K) = (P_p(K)/p!)_p ∈ ∏_p A^p(Y) ⊗ ℚ`. It is invariant under isomorphism,
vanishes on zero objects, commutes with pullback (`res_g ch(K) = ch(Lg^*K)`), is `ch(M)` on a
finite locally free `M[0]`, and is multiplicative on derived tensor products (Stacks 0FAG).

**The bridge** `GRR.chK_mk_eq_perfectCh`: on a smooth `Y` over a field, `chK [F] = ch(F[0])` for
a coherent `F` (Remark 0FEU). `GRR.closedImmersionFormula_of_bundles` reduces
`GRR.ClosedImmersionFormula` to the classes of finite locally free modules.
-/

open AlgebraicGeometry CategoryTheory Stacks.Chow
open scoped TensorProduct

universe u

namespace GRR

attribute [local instance 10000] HasDerivedCategory.standard

section Perfect

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- **The Chern character of a perfect complex** `K ∈ D(𝒪_Y)` whose Chern classes are defined
(Stacks 0F9E (2)): `ch(K) = (P_p(K)/p!)_{p ≥ 0} ∈ ∏_p A^p(Y) ⊗ ℚ`. -/
noncomputable def perfectCh {K : DerivedCategory Y.Modules} (hK : HasDefinedChernClasses K) :
    RationalTotalChowClass C sY :=
  RationalTotalChowClass.ofFamily (perfectChernCharacter C sY hK)

/-- `ch_p(K) = P_p(K)/p!`. -/
theorem perfectCh_apply {K : DerivedCategory Y.Modules} (hK : HasDefinedChernClasses K) (p : ℕ) :
    perfectCh C sY hK p = ((p.factorial : ℚ)⁻¹) ⊗ₜ[ℤ] perfectPowerSum C sY hK p p :=
  rfl

/-- **`ch(K)` depends only on the isomorphism class of `K`**: `K ≅ K'` gives `ch(K) = ch(K')`. -/
theorem perfectCh_congr {K K' : DerivedCategory Y.Modules} (hK : HasDefinedChernClasses K)
    (hK' : HasDefinedChernClasses K') (e : K ≅ K') : perfectCh C sY hK = perfectCh C sY hK' :=
  RationalTotalChowClass.ext fun p ↦ by
    rw [perfectCh_apply, perfectCh_apply, perfectPowerSum_congr C sY hK hK' e p]

/-- **`ch(0) = 0`**: the Chern character of a zero object vanishes. -/
theorem perfectCh_eq_zero {K : DerivedCategory Y.Modules} (hK : HasDefinedChernClasses K)
    (h0 : Limits.IsZero K) : perfectCh C sY hK = 0 :=
  RationalTotalChowClass.ext fun p ↦ by
    rw [perfectCh_apply, perfectPowerSum_of_isZero C sY hK h0 p, TotalChowClass.zero_apply,
      TensorProduct.tmul_zero, RationalTotalChowClass.zero_apply]

/-- **The Chern character commutes with pullback**: for `g : Y' ⟶ Y` locally of finite type,
`g^* ch(K) = ch(Lg^* K)`. -/
theorem pullbackAQ_perfectCh {Y' : Scheme.{u}} (sY' : Y' ⟶ C.S) [LocallyOfFiniteType sY']
    (g : Y' ⟶ Y) [LocallyOfFiniteType g] (hs : g ≫ sY = sY') {K : DerivedCategory Y.Modules}
    (hK : HasDefinedChernClasses K) :
    pullbackAQ C sY' sY g hs (perfectCh C sY hK) = perfectCh C sY' (hK.derivedPullback g) :=
  RationalTotalChowClass.ext fun p ↦ by
    rw [perfectCh_apply C sY' (hK.derivedPullback g) p,
      ← res_perfectPowerSum_derivedPullback C sY hK g hs (hK.derivedPullback g) p,
      TotalChowClass.res_apply_eq_chowCohomologyRestrictionOfEq]
    rfl

/-- `g^* ch(K) = ch(K')` for any `K' ≅ Lg^* K` whose Chern classes are defined. -/
theorem pullbackAQ_perfectCh_of_iso {Y' : Scheme.{u}} (sY' : Y' ⟶ C.S) [LocallyOfFiniteType sY']
    (g : Y' ⟶ Y) [LocallyOfFiniteType g] (hs : g ≫ sY = sY') {K : DerivedCategory Y.Modules}
    (hK : HasDefinedChernClasses K) {K' : DerivedCategory Y'.Modules}
    (hK' : HasDefinedChernClasses K')
    (e : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      g.toLRSHom.toShHom).obj K ≅ K') :
    pullbackAQ C sY' sY g hs (perfectCh C sY hK) = perfectCh C sY' hK' :=
  (pullbackAQ_perfectCh C sY sY' g hs hK).trans (perfectCh_congr C sY' _ hK' e)

/-- **`ch(M[0]) = ch(M)`** for a finite locally free module `M` placed in degree zero: the
Chern character of a perfect complex `K ≅ M[0]` is the Chern character of `[M] ∈ K₀(Vect Y)`. -/
theorem perfectCh_single {K : DerivedCategory Y.Modules} (hK : HasDefinedChernClasses K)
    (M : Y.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M]
    (e : K ≅ (DerivedCategory.singleFunctor Y.Modules 0).obj M) :
    perfectCh C sY hK = ch C sY (VectorBundleKZero.classOf Y M) :=
  RationalTotalChowClass.ext fun p ↦ by
    rw [perfectCh_apply, ch_apply, chernCharacterVectorBundle_classOf,
      perfectPowerSum_eq_powerSumOfFiniteLocallyFree C sY hK M e p]
    rfl

/-- **Remark 0FEU**: if `K ≅ E` for a bounded complex `E` of finite locally free modules, then
`ch(K) = ch(∑_n (-1)^n [E^n])`, the Chern character of the Euler characteristic of `E` in
`K₀(Vect Y)`. -/
theorem perfectCh_eq_ch_eulerCharComplex {K : DerivedCategory Y.Modules}
    (hK : HasDefinedChernClasses K) {E : CochainComplex Y.Modules ℤ}
    (hE : Stacks.Perfect.BoundedLocallyFreeComplexes.boundedFiniteLocallyFreeComplex Y E)
    (e : K ≅ DerivedCategory.Q.obj E) :
    perfectCh C sY hK =
      ch C sY (Stacks.Perfect.BoundedLocallyFreeComplexes.eulerCharComplex Y E) :=
  RationalTotalChowClass.ext fun p ↦ by
    rw [ch_apply, chernCharacterVectorBundle_apply, perfectCh_apply,
      perfectPowerSum_eq_powerSumKHom_eulerCharComplex C sY hK hE e.symm p]

end Perfect

namespace PerfectCh

/-- The components of an integer multiple of a total class. -/
theorem totalChowClass_zsmul_apply {C : ChowSituation.{u}} {Y : Scheme.{u}} {sY : Y ⟶ C.S}
    [LocallyOfFiniteType sY] (n : ℤ) (c : TotalChowClass C sY) (p : ℕ) :
    (n • c) p = n • c p :=
  rfl

/-- The lift `∑_{p ≤ m} P_p(K)/p!` of `ch(K)` below degree `m` has the components of `ch(K)` in
degrees at most `m`. -/
theorem rationalComponent_sum_perfectPowerSum (C : ChowSituation.{u}) {Y : Scheme.{u}}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {K : DerivedCategory Y.Modules}
    (hK : HasDefinedChernClasses K) (m : ℕ) {j : ℕ} (hj : j ≤ m) :
    RationalTotalChowClass.rationalComponent j
        (∑ p ∈ Finset.range (m + 1),
          ((p.factorial : ℚ)⁻¹) ⊗ₜ[ℤ] perfectPowerSum C sY hK p) =
      perfectCh C sY hK j := by
  rw [map_sum, perfectCh_apply, Finset.sum_eq_single j]
  · rfl
  · intro p _ hp
    rw [RationalTotalChowClass.rationalComponent_tmul,
      isHomogeneous_perfectPowerSum C sY hK p j (Ne.symm hp), TensorProduct.tmul_zero]
  · intro hj'
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) hj'

/-- `C(a + b, a) / (a + b)! = 1 / (a! b!)`. -/
theorem choose_div_factorial (a b : ℕ) :
    (((a + b).choose a : ℤ) : ℚ) * ((a + b).factorial : ℚ)⁻¹ =
      (a.factorial : ℚ)⁻¹ * (b.factorial : ℚ)⁻¹ := by
  have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
  rw [Nat.add_sub_cancel_left] at h
  have hc : (((a + b).choose a : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_right a b)).ne'
  have ha : (a.factorial : ℚ) ≠ 0 := by exact_mod_cast a.factorial_ne_zero
  have hb : (b.factorial : ℚ) ≠ 0 := by exact_mod_cast b.factorial_ne_zero
  rw [Int.cast_natCast, ← h, Nat.cast_mul, Nat.cast_mul, mul_inv, mul_inv, mul_assoc,
    mul_inv_cancel_left₀ hc]

end PerfectCh

open PerfectCh in
/-- **The Chern character is multiplicative on derived tensor products** (Stacks 0FAG):
`ch(E ⊗^L F) = ch(E) · ch(F)` for `E`, `F ∈ D(𝒪_Y)` whose Chern classes are defined. -/
theorem perfectCh_derivedTensor (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] {E F : DerivedCategory Y.Modules} (hE : HasDefinedChernClasses E)
    (hF : HasDefinedChernClasses F)
    (hEF : HasDefinedChernClasses
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).obj E).obj F)) :
    perfectCh C sY hEF = perfectCh C sY hE * perfectCh C sY hF := by
  refine RationalTotalChowClass.ext fun m ↦ ?_
  -- `rw` cannot see through the type of `hEF`, so the left side is unfolded by hand
  refine ((perfectCh_apply C sY hEF m).trans
    (congrArg (fun x : TotalChowClass C sY ↦ ((m.factorial : ℚ)⁻¹) ⊗ₜ[ℤ] x m)
      (perfectPowerSum_derivedTensor C sY hE hF hEF m))).trans ?_
  rw [RationalTotalChowClass.mul_apply_eq
      (fun j hj ↦ rationalComponent_sum_perfectPowerSum C sY hE m hj)
      (fun j hj ↦ rationalComponent_sum_perfectPowerSum C sY hF m hj), Finset.sum_mul, map_sum,
    TotalChowClass.sum_apply, TensorProduct.tmul_sum,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  have ham : a ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  rw [Finset.mul_sum, map_sum, Finset.sum_eq_single (m - a)]
  · rw [Algebra.TensorProduct.tmul_mul_tmul, RationalTotalChowClass.rationalComponent_tmul,
      totalChowClass_zsmul_apply, ← TensorProduct.smul_tmul, zsmul_eq_mul]
    congr 1
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ham
    rw [Nat.add_sub_cancel_left]
    exact choose_div_factorial a b
  · intro b _ hb
    rw [Algebra.TensorProduct.tmul_mul_tmul, RationalTotalChowClass.rationalComponent_tmul,
      ((isHomogeneous_perfectPowerSum C sY hE a).mul (isHomogeneous_perfectPowerSum C sY hF b)) m
        (by omega), TensorProduct.tmul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- `ch(K) = ch(E) · ch(F)` for any `K ≅ E ⊗^L F` whose Chern classes are defined. -/
theorem perfectCh_derivedTensor_of_iso (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] {E F K : DerivedCategory Y.Modules} (hE : HasDefinedChernClasses E)
    (hF : HasDefinedChernClasses F) (hK : HasDefinedChernClasses K)
    (e : K ≅ ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).obj E).obj F) :
    perfectCh C sY hK = perfectCh C sY hE * perfectCh C sY hF :=
  (perfectCh_congr C sY hK (hasDefinedChernClasses_derivedTensor hE hF) e).trans
    (perfectCh_derivedTensor C sY hE hF _)

section Bridge

variable (k : Type u) [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsSmoothFT k sY]

include k sY in
/-- **The Chern classes of a coherent module placed in degree zero are defined**: on a smooth
`Y` over a field, `F[0]` is perfect (Stacks 0F8F) and `Y` is quasi-compact. -/
theorem hasDefinedChernClasses_single_coherent
    (F : Stacks.SheafOfModules.CoherentModules Y.ringCatSheaf) :
    HasDefinedChernClasses ((DerivedCategory.singleFunctor Y.Modules 0).obj F.obj) := by
  have := compactSpace k sY
  have := isAffineHom_diagonal k sY
  obtain ⟨K₀, -, ⟨eK⟩, -, -, -⟩ :=
    exists_regularVectorBundleKZeroAddEquiv_symm_mk Y (isRegular k sY) F
  exact hasDefinedChernClasses_of_iso
    (hasDefinedChernClasses_of_compactSpace (fieldChowSituation k) sY K₀.obj K₀.property) eK

include k sY in
/-- **Every coherent module is a perfect complex with defined Chern classes**: on a smooth `Y`
over a field, a coherent `F` gives `K ≅ F[0]` with the Chern classes of `K` defined. -/
theorem exists_perfect_of_coherent (F : Stacks.SheafOfModules.CoherentModules Y.ringCatSheaf) :
    ∃ (K : DerivedCategory Y.Modules) (_ : HasDefinedChernClasses K),
      Nonempty (K ≅ (DerivedCategory.singleFunctor Y.Modules 0).obj F.obj) :=
  ⟨_, hasDefinedChernClasses_single_coherent k sY F, ⟨Iso.refl _⟩⟩

/-- **The bridge between `chK` and the Chern character of perfect complexes** (Remark 0FEU):
on a smooth `Y` over a field, `ch([F]) = ch(F[0])` for a coherent `F`, where the left side is
`GRR.chK` of the class of `F` in `K'₀(Y)` and the right side is the Chern character of any
`K ≅ F[0]` whose Chern classes are defined. -/
theorem chK_mk_eq_perfectCh (F : Stacks.SheafOfModules.CoherentModules Y.ringCatSheaf)
    {K : DerivedCategory Y.Modules} (hK : HasDefinedChernClasses K)
    (e : K ≅ (DerivedCategory.singleFunctor Y.Modules 0).obj F.obj) :
    chK k sY (KZero.mk _ F) = perfectCh (fieldChowSituation k) sY hK := by
  have := compactSpace k sY
  have := isAffineHom_diagonal k sY
  obtain ⟨K₀, E, ⟨eK⟩, hE, ⟨eE⟩, hθ⟩ :=
    exists_regularVectorBundleKZeroAddEquiv_symm_mk Y (isRegular k sY) F
  have hθ' : (vectorBundleEquiv k sY).symm (KZero.mk _ F) =
      Stacks.Perfect.BoundedLocallyFreeComplexes.eulerCharComplex Y E := hθ
  rw [chK_eq_ch, hθ', perfectCh_eq_ch_eulerCharComplex (fieldChowSituation k) sY hK hE
    (e ≪≫ eK.symm ≪≫ eE.symm)]

/-- `ch(θ a) = ch(a)` for `a ∈ K₀(Vect Y)`, `θ : K₀(Vect Y) ≅ K'₀(Y)`. -/
theorem chK_vectorBundleEquiv (a : VectorBundleKZero Y) :
    chK k sY (vectorBundleEquiv k sY a) = ch (fieldChowSituation k) sY a := by
  rw [chK_eq_ch, AddEquiv.symm_apply_apply]

/-- **`ch(i_! θ[E]) = ch((i_*E)[0])`** for a closed immersion `i : X ⟶ P` of smooth schemes over
`k` and a finite locally free `E` on `X`: the left side of `GRR.ClosedImmersionFormula` at
`θ[E]` is the Chern character of any `K ≅ (i_*E)[0]` whose Chern classes are defined. -/
theorem chK_pushforwardK_classOf_eq_perfectCh {X P : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (sP : P ⟶ Spec (.of k)) [IsSmoothFT k sX] [IsSmoothFT k sP] (i : X ⟶ P)
    [IsClosedImmersion i] (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    {K : DerivedCategory P.Modules} (hK : HasDefinedChernClasses K)
    (e : K ≅ (DerivedCategory.singleFunctor P.Modules 0).obj
      ((Scheme.Modules.pushforward i).obj E)) :
    haveI := compactSpace k sP
    haveI : IsLocallyNoetherian P := (isNoetherian k sP).toIsLocallyNoetherian
    chK k sP (pushforwardK i (vectorBundleEquiv k sX (VectorBundleKZero.classOf X E))) =
      perfectCh (fieldChowSituation k) sP hK := by
  have := compactSpace k sP
  have : IsLocallyNoetherian P := (isNoetherian k sP).toIsLocallyNoetherian
  obtain ⟨hcoh, hθ⟩ := vectorBundleEquiv_classOf k sX E
    (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree E)
  rw [hθ, pushforwardK_mk_of_isClosedImmersion]
  exact chK_mk_eq_perfectCh k sP _ hK e

end Bridge

namespace PerfectCh

variable (k : Type u) [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))

/-- Capping the fundamental class, `c ↦ c ∩ [Y]`, as an additive map. -/
noncomputable def capFundamental [IsSmoothFT k sY] : AQ k sY →+ CHQ k sY where
  toFun c := cap k sY c (fundamentalClass k sY)
  map_zero' := by simp only [cap, map_zero, LinearMap.zero_apply]
  map_add' c d := by simp only [cap, map_add, LinearMap.add_apply]

theorem capFundamental_apply [IsSmoothFT k sY] (c : AQ k sY) :
    capFundamental k sY c = cap k sY c (fundamentalClass k sY) :=
  rfl

end PerfectCh

section Bundles

open PerfectCh

variable (k : Type u) [Field k] {X P : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sP : P ⟶ Spec (.of k)) [IsSmoothFT k sX] [IsSmoothFT k sP]
  (i : X ⟶ P) [IsClosedImmersion i] (hi : i ≫ sP = sX)

/-- **Reduction of `ClosedImmersionFormula` to vector bundles.** If for every finite locally free
`E` on `X`

  `ch(i_! θ[E]) ∩ [P] = i_* ((ch(E) · td(N_{X/P})⁻¹) ∩ [X])`,

`θ : K₀(Vect X) ≅ K'₀(X)`, then the formula holds for every `α ∈ K'₀(X)`: both sides are additive
in `α` and `θ` is onto. -/
theorem closedImmersionFormula_of_bundles
    (h : ∀ (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E],
      haveI := compactSpace k sP
      haveI : IsLocallyNoetherian P := (isNoetherian k sP).toIsLocallyNoetherian
      cap k sP (chK k sP (pushforwardK i (vectorBundleEquiv k sX (VectorBundleKZero.classOf X E))))
          (fundamentalClass k sP) =
        rationalProperChowPushforward (fieldChowSituation k) sX sP hi
          (cap k sX (ch (fieldChowSituation k) sX (VectorBundleKZero.classOf X E) *
              toddClass (fieldChowSituation k) sX (-normalClass k sP i))
            (fundamentalClass k sX))) :
    ClosedImmersionFormula k sX sP i hi := by
  have := compactSpace k sP
  have : IsLocallyNoetherian P := (isNoetherian k sP).toIsLocallyNoetherian
  let φ : VectorBundleKZero X →+ CHQ k sP :=
    (capFundamental k sP).comp ((chK k sP).comp ((pushforwardK i).comp
      (vectorBundleEquiv k sX).toAddMonoidHom))
  let ψ : VectorBundleKZero X →+ CHQ k sP :=
    (rationalProperChowPushforward (fieldChowSituation k) sX sP hi).toAddMonoidHom.comp
      ((capFundamental k sX).comp
        ((AddMonoidHom.mulRight (toddClass (fieldChowSituation k) sX (-normalClass k sP i))).comp
          (ch (fieldChowSituation k) sX).toAddMonoidHom))
  have hφψ : φ = ψ := VectorBundleKZero.addHom_ext fun M hM ↦ by
    have := Stacks.StalkFreeBridge.isFiniteLocallyFree_of_finiteLocallyFree M (hM := hM)
    exact h M
  intro α
  have hα := DFunLike.congr_fun hφψ ((vectorBundleEquiv k sX).symm α)
  simp only [φ, ψ, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.apply_symm_apply, capFundamental_apply, LinearMap.toAddMonoidHom_coe,
    AddMonoidHom.mulRight_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass] at hα
  rw [chK_eq_ch k sX]
  exact hα

end Bundles

end GRR
