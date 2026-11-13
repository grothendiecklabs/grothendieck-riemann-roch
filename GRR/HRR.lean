import Mathlib
import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.ProperPushforwardUnconditional
import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.AdditivityUnconditional
import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyComparison
import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic
import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field
import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge
import GRR.Statement

/-!
# Hirzebruch–Riemann–Roch as the case `Y = Spec k`

For a proper smooth scheme `X` over a field `k`, the Euler characteristic
`χ(X, F) = ∑_i (-1)^i dim_k H^i(X, F)` is additive, hence a homomorphism
`GRR.eulerK k sX : K'₀(X) → ℤ`. It is compatible with the pushforward to the point
(`eulerK_pushforwardK`), and on the point the Riemann–Roch map is `τ(γ) = χ(γ) · [Spec k]`
(`tau_point`). Hence the Grothendieck–Riemann–Roch formula for `X → Spec k` gives
Hirzebruch–Riemann–Roch:

  `(s_X)_* ((ch(α) · td(T_X)) ∩ [X]) = χ(X, α) · [Spec k]`  in `CH_*(Spec k) ⊗ ℚ`,

i.e. `∫_X ch(α) · td(T_X) = χ(X, α)` (`hirzebruch_riemann_roch_of`).
-/

open AlgebraicGeometry CategoryTheory Stacks.Chow
open scoped TensorProduct

universe u

namespace GRR

variable (k : Type u) [Field k]

/-- The point `Spec k` is smooth, separated and of finite type over `k`. -/
instance isSmoothFT_id : IsSmoothFT k (𝟙 (Spec (.of k))) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

section Euler

/-- The Euler characteristic is additive on short exact sequences of coherent modules: the
inclusion of coherent modules into all modules is exact. -/
theorem eulerCharacteristic_add_coherent {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsProper sX]
    {S : ShortComplex (Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)} (hS : S.ShortExact) :
    @eulerCharacteristic k _ X sX _ S.X₂.obj
        (CoherentAbelian.isCoherent_of_stacksIsCoherent S.X₂.property) =
      @eulerCharacteristic k _ X sX _ S.X₁.obj
          (CoherentAbelian.isCoherent_of_stacksIsCoherent S.X₁.property) +
        @eulerCharacteristic k _ X sX _ S.X₃.obj
          (CoherentAbelian.isCoherent_of_stacksIsCoherent S.X₃.property) := by
  have : Limits.PreservesFiniteLimits (coherentInclusion X) :=
    ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass _
  have : Limits.PreservesFiniteColimits (coherentInclusion X) :=
    ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass _
  have hS' : (S.map (coherentInclusion X)).ShortExact := hS.map_of_exact _
  have : (S.map (coherentInclusion X)).X₁.IsCoherent :=
    CoherentAbelian.isCoherent_of_stacksIsCoherent S.X₁.property
  have : (S.map (coherentInclusion X)).X₂.IsCoherent :=
    CoherentAbelian.isCoherent_of_stacksIsCoherent S.X₂.property
  have : (S.map (coherentInclusion X)).X₃.IsCoherent :=
    CoherentAbelian.isCoherent_of_stacksIsCoherent S.X₃.property
  exact eulerCharacteristic_add_of_shortExact k sX hS'

/-- **The Euler characteristic as a homomorphism** `χ : K'₀(X) → ℤ`,
`χ([F]) = ∑_i (-1)^i dim_k H^i(X, F)`, for `X` proper over `k`. -/
noncomputable def eulerK {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsProper sX] :
    CoherentKZero X →+ ℤ :=
  KZero.lift (fun F => @eulerCharacteristic k _ X sX _ F.obj
      (CoherentAbelian.isCoherent_of_stacksIsCoherent F.property))
    fun _ hS => eulerCharacteristic_add_coherent k sX hS

variable {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsProper sX]

/-- `χ([F])` is the Euler characteristic of the coherent module `F`. -/
theorem eulerK_mk (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) :
    eulerK k sX (KZero.mk _ F) =
      @eulerCharacteristic k _ X sX _ F.obj
        (CoherentAbelian.isCoherent_of_stacksIsCoherent F.property) := by
  exact KZero.lift_mk _ _ F

/-- Euler characteristics along equal structure morphisms agree. -/
theorem eulerCharacteristic_congr_hom {f g : X ⟶ Spec (.of k)} (h : f = g) [IsProper f]
    [IsProper g] (F : X.Modules) [F.IsCoherent] :
    eulerCharacteristic k f F = eulerCharacteristic k g F := by
  subst h
  rfl

/-- **`χ(Spec k, (s_X)_! α) = χ(X, α)`**: the Euler characteristic is compatible with the
pushforward to the point. -/
theorem eulerK_pushforwardK (α : CoherentKZero X) :
    eulerK k (𝟙 (Spec (.of k))) (pushforwardK sX α) = eulerK k sX α := by
  have h : (eulerK k (𝟙 (Spec (.of k)))).comp (pushforwardK sX) = eulerK k sX := by
    refine KZero.hom_ext fun F => ?_
    have : F.obj.IsCoherent := CoherentAbelian.isCoherent_of_stacksIsCoherent F.property
    have : F.obj.IsQuasicoherent := isQuasicoherent_obj F
    rw [AddMonoidHom.comp_apply, pushforwardK_mk, map_sum, eulerK_mk,
      ← eulerCharacteristic_congr_hom k (Category.comp_id sX) F.obj,
      eulerCharacteristic_eq_finsum_higherDirectImage k sX (𝟙 (Spec (.of k))) F.obj,
      finsum_eq_sum_of_support_subset _ (s := Finset.range (cohomologicalBound sX)) ?_]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, eulerK_mk, smul_eq_mul]
      rfl
    · intro i hi
      rw [Function.mem_support] at hi
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hle
      refine hi ?_
      have hz := isZero_higherDirectImage_of_cohomologicalBound_le sX F.obj i (not_lt.1 hle)
      have h0 := KZero.mk_eq_zero_of_isZero ((isZero_higherDirectImageCoh_iff sX F i).2 hz)
      have h1 := congrArg (eulerK k (𝟙 (Spec (.of k)))) h0
      rw [eulerK_mk, map_zero] at h1
      exact mul_eq_zero_of_right _ h1
  exact DFunLike.congr_fun h α

end Euler

/-! ### Chow groups and cap products on the point -/

section Point

/-- Every point of `Spec k` has relative dimension `0` over `Spec k`. -/
theorem relativeDimension_point (x : Spec (.of k)) :
    relativeDimension (fieldChowSituation k).dimensionFunction (𝟙 (Spec (.of k))) x = 0 :=
  (relativeDimension_id _ x).trans (fieldChowSituation_dimensionFunction k x)

/-- `CH_j(Spec k) = 0` for `j ≠ 0`. -/
theorem chowGroup_point_eq_zero {j : ℤ} (hj : j ≠ 0)
    (α : chowGroup (fieldChowSituation k) (𝟙 (Spec (.of k))) j) : α = 0 :=
  chowGroup_eq_zero _ _ (fun x => by rw [relativeDimension_point]; exact fun h => hj h.symm) α

/-- `CH_j(Spec k) ⊗ ℚ = 0` for `j ≠ 0`. -/
theorem rationalChow_point_eq_zero {j : ℤ} (hj : j ≠ 0)
    (t : ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) (𝟙 (Spec (.of k))) j) : t = 0 := by
  induction t using TensorProduct.inductionOn with
  | tmul q a => rw [chowGroup_point_eq_zero k hj a, TensorProduct.tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

/-- On `CH_*(Spec k) ⊗ ℚ` the cap product with `c ∈ ∏_p A^p(Spec k) ⊗ ℚ` only depends on the
degree-`0` component of `c`: the components of degree `p > 0` land in `CH_{-p}(Spec k) = 0`. -/
theorem cap_point_congr {c c' : AQ k (𝟙 (Spec (.of k)))} (h : c 0 = c' 0) :
    cap k (𝟙 (Spec (.of k))) c = cap k (𝟙 (Spec (.of k))) c' := by
  have hlo : ∀ x : Spec (.of k), (0 : ℤ) ≤
      relativeDimension (fieldChowSituation k).dimensionFunction (𝟙 (Spec (.of k))) x :=
    fun x => (relativeDimension_point k x).ge
  have hs : ∀ p : ℕ, (p : ℤ) ≤ 0 - 0 → p ∈ ({0} : Finset ℕ) := fun p hp => by
    rw [Finset.mem_singleton]
    omega
  have e : ∀ d : AQ k (𝟙 (Spec (.of k))), (RationalTotalChowClass.ofFamily.symm d) 0 = d 0 :=
    fun d => (RationalTotalChowClass.ofFamily_apply (RationalTotalChowClass.ofFamily.symm d)
      0).symm.trans (by rw [LinearEquiv.apply_symm_apply])
  unfold cap
  refine DirectSum.linearMap_ext ℚ fun j => LinearMap.ext fun t => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  rcases eq_or_ne j 0 with rfl | hj
  · rw [totalRationalChowCap_lof_eq_sum _ _ _ 0 hlo _ 0 t {0} hs,
      totalRationalChowCap_lof_eq_sum _ _ _ 0 hlo _ 0 t {0} hs,
      Finset.sum_singleton, Finset.sum_singleton, e, e, h]
  · rw [rationalChow_point_eq_zero k hj t]
    simp only [map_zero]

/-- The cap product with the integer `n` is multiplication by `n`. -/
theorem cap_natCast {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (n : ℕ)
    (x : CHQ k sX) : cap k sX (n : AQ k sX) x = n • x := by
  unfold cap
  rw [← nsmul_one, map_nsmul, map_nsmul, totalRationalChowCap_one, LinearMap.smul_apply,
    Module.End.one_apply]

end Point

/-! ### Degree-zero components of the Chern character and the Todd class -/

section DegreeZero

variable {C : ChowSituation.{u}} {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- The degree-`0` component of a Todd class is that of `1`. -/
theorem toddClass_apply_zero (a : VectorBundleKZero X) :
    toddClass C sX a 0 = (1 : RationalTotalChowClass C sX) 0 := by
  change (chowGraded C sX).comp 0 ((chowGraded C sX).gexp _) = (chowGraded C sX).comp 0 1
  rw [GradedComplete.comp_gexp, Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one,
    inv_one, one_smul]

/-- Multiplying by a Todd class does not change the degree-`0` component. -/
theorem mul_toddClass_apply_zero (c : RationalTotalChowClass C sX) (a : VectorBundleKZero X) :
    (c * toddClass C sX a) 0 = c 0 := by
  have h := (chowGraded C sX).mul_congr 0 c c (toddClass C sX a) 1 (fun _ _ => rfl)
    (fun p hp => by
      obtain rfl : p = 0 := Nat.le_zero.mp hp
      exact toddClass_apply_zero sX a)
  rw [mul_one] at h
  exact h

/-- The degree-`0` component of `ch(E)` is the rank of `E` (`P_0(E) = r`). -/
theorem ch_classOf_apply_zero (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    ch C sX (VectorBundleKZero.classOf X E) 0 = (r : RationalTotalChowClass C sX) 0 := by
  change rationalTotalChernCharacterRingHom C sX (VectorBundleKZero.classOf X E) 0 = _
  rw [rationalTotalChernCharacterRingHom_classOf, rationalTotalChernCharacter_apply,
    chernCharacterOfFiniteLocallyFree, powerSumClassOfFiniteLocallyFree,
    powerSumOfFiniteLocallyFree_eq_powerSumTotal C sX E r, powerSumTotal_zero,
    Nat.factorial_zero, Nat.cast_one, inv_one,
    ← map_natCast (RationalTotalChowClass.ofTotalChowClass (C := C) (sX := sX)) r,
    RationalTotalChowClass.ofTotalChowClass_apply]

end DegreeZero

/-! ### Coherent modules on the point -/

section Modules

/-- The global sections of a module on `Spec k`, with `k` acting through `Γ(Spec k, 𝒪)`, are its
global sections with `k` acting through the structure morphism `𝟙 (Spec k)`. -/
noncomputable def sectionsLinearEquiv (M : (Spec (.of k)).Modules) :
    (moduleSpecΓFunctor (R := .of k)).obj M ≃ₗ[k]
      (restrictScalarsOverBase k (𝟙 (Spec (.of k)))).obj
        ((SheafOfModules.evaluation (Spec (.of k)).ringCatSheaf (Opposite.op ⊤)).obj M) where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- On `Spec k` the Euler characteristic of a coherent module is the dimension of its `H⁰`: the
higher cohomology of a quasi-coherent module on an affine scheme vanishes. -/
theorem eulerCharacteristic_point (F : (Spec (.of k)).Modules) [F.IsCoherent] :
    eulerCharacteristic k (𝟙 (Spec (.of k))) F =
      Module.finrank k (cohomologyOverField k (𝟙 (Spec (.of k))) F 0) := by
  have : F.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1
  have hz : ∀ m, 1 ≤ m →
      Module.finrank k (cohomologyOverField k (𝟙 (Spec (.of k))) F m) = 0 := fun m hm =>
    have := ModuleCat.subsingleton_of_isZero
      ((isZero_cohomologyOverField_iff_isZero_hgroup k (𝟙 (Spec (.of k))) F m).mpr
        (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen _ F ⊤ (isAffineOpen_top _) m hm))
    Module.finrank_zero_of_subsingleton
  rw [eulerCharacteristic_eq_finsum, finsum_eq_sum_of_support_subset (s := Finset.range 1) _
    fun m hm => ?_]
  · rw [Finset.sum_range_one]
    ring
  · by_contra hn
    simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hn
    simp [hz m hn] at hm

/-- A coherent module on `Spec k` is finite locally free of rank `r = dim_k H⁰`, and its Euler
characteristic is `r`. -/
theorem exists_rank_point
    (F : Stacks.SheafOfModules.CoherentModules (Spec (.of k)).ringCatSheaf) :
    ∃ r : ℕ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F.obj r ∧
      eulerK k (𝟙 (Spec (.of k))) (KZero.mk _ F) = r := by
  have : F.obj.IsCoherent := CoherentAbelian.isCoherent_of_stacksIsCoherent F.property
  have hqc : F.obj.IsQuasicoherent := isQuasicoherent_obj F
  have : FiniteDimensional k (cohomologyOverField k (𝟙 (Spec (.of k))) F.obj 0) :=
    finiteDimensional_cohomologyOverField_of_isProper k _ F.obj 0
  let e : (moduleSpecΓFunctor (R := .of k)).obj F.obj ≃ₗ[k]
      cohomologyOverField k (𝟙 (Spec (.of k))) F.obj 0 :=
    (sectionsLinearEquiv k F.obj).trans
      (cohomologyOverFieldZeroLinearIso k _ F.obj).symm.toLinearEquiv
  refine ⟨Module.finrank k (cohomologyOverField k (𝟙 (Spec (.of k))) F.obj 0), ?_, ?_⟩
  · have hfin : Module.Finite k ((moduleSpecΓFunctor (R := .of k)).obj F.obj) :=
      Module.Finite.equiv e.symm
    have h := (Module.isFiniteLocallyFreeOfRank_iff_finrank_eq _ _).mpr ⟨hfin, e.finrank_eq⟩
    have : IsIso (Scheme.Modules.fromTildeΓ F.obj) :=
      (isQuasicoherent_iff_isIso_fromTildeΓ F.obj).mp hqc
    exact (Scheme.Modules.isFiniteLocallyFreeOfRank_iff F.obj _).mp <|
      Scheme.Modules.IsFiniteLocallyFreeOfRank.of_iso (asIso (Scheme.Modules.fromTildeΓ F.obj))
        ((tilde_isFiniteLocallyFreeOfRank_iff k ((moduleSpecΓFunctor (R := .of k)).obj F.obj)
          _).mpr h)
  · rw [eulerK_mk]
    exact eulerCharacteristic_point k F.obj

end Modules

/-- **Riemann–Roch on the point**: `τ(γ) = χ(γ) · [Spec k]` for `γ ∈ K'₀(Spec k)`. -/
theorem tau_point (γ : CoherentKZero (Spec (.of k))) :
    tau k (𝟙 (Spec (.of k))) γ =
      ((eulerK k (𝟙 (Spec (.of k))) γ : ℤ) : ℚ) • fundamentalClass k (𝟙 (Spec (.of k))) := by
  let R : CoherentKZero (Spec (.of k)) →+ CHQ k (𝟙 (Spec (.of k))) :=
    { toFun := fun γ => ((eulerK k (𝟙 (Spec (.of k))) γ : ℤ) : ℚ) •
        fundamentalClass k (𝟙 (Spec (.of k)))
      map_zero' := by rw [map_zero, Int.cast_zero, zero_smul]
      map_add' := fun a b => by rw [map_add, Int.cast_add, add_smul] }
  have h : tau k (𝟙 (Spec (.of k))) = R := by
    refine KZero.hom_ext fun F => ?_
    obtain ⟨r, hr, hχ⟩ := exists_rank_point k F
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F.obj :=
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F.obj r
    have hθ : (vectorBundleEquiv k (𝟙 (Spec (.of k)))).symm (KZero.mk _ F) =
        VectorBundleKZero.classOf _ F.obj := by
      rw [AddEquiv.symm_apply_eq]
      exact (regularVectorBundleKZeroAddEquiv_classOf _ _ F this).symm
    have hch : chK k (𝟙 (Spec (.of k))) (KZero.mk _ F) =
        ch (fieldChowSituation k) (𝟙 (Spec (.of k))) (VectorBundleKZero.classOf _ F.obj) :=
      congrArg (ch (fieldChowSituation k) (𝟙 (Spec (.of k)))) hθ
    change cap k _ (chK k _ (KZero.mk _ F) * toddTangent k _) (fundamentalClass k _) =
      ((eulerK k (𝟙 (Spec (.of k))) (KZero.mk _ F) : ℤ) : ℚ) •
        fundamentalClass k (𝟙 (Spec (.of k)))
    rw [cap_point_congr k (c' := (r : AQ k (𝟙 (Spec (.of k))))) ?_, cap_natCast, hχ,
      Int.cast_natCast, Nat.cast_smul_eq_nsmul]
    rw [toddTangent, mul_toddClass_apply_zero, hch]
    exact ch_classOf_apply_zero _ F.obj r
  exact DFunLike.congr_fun h γ

/-- **Hirzebruch–Riemann–Roch, from Grothendieck–Riemann–Roch for `X → Spec k`**: for `X` smooth
and proper over `k` and `α ∈ K'₀(X)`, the pushforward to the point of
`(ch(α) · td(T_X)) ∩ [X]` is `χ(X, α) · [Spec k]`. -/
theorem hirzebruch_riemann_roch_of {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsSmoothFT k sX]
    [IsProper sX]
    (hRR : RiemannRochFor k sX (𝟙 (Spec (.of k))) sX (Category.comp_id sX))
    (α : CoherentKZero X) :
    rationalProperChowPushforward (fieldChowSituation k) sX (𝟙 (Spec (.of k)))
        (Category.comp_id sX) (tau k sX α) =
      ((eulerK k sX α : ℤ) : ℚ) • fundamentalClass k (𝟙 (Spec (.of k))) := by
  rw [hRR α, tau_point, eulerK_pushforwardK]

end GRR
