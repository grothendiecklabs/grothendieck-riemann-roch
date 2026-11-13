import Mathlib
import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.TowerChow
import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Injective
import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.FreeTower.IntegralModel
import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.CapPowCommute
import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DimensionPart
import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionRegularImmersionProduct
import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.CanonicalDiagonalFlat
import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly.ZeroSchemePieces
import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullback
import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.Exactness
import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BaseChange
import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FormallySmooth
import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmoothTag
import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TensorTotalComplex
import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
import GRR.Projection
import GRR.ClosedImmersion

/-!
# The Riemann–Roch map on the twisted classes of `ℙⁿ_Y`

Let `π : P = ℙⁿ_Y ⟶ Y` be the projection, `h = c₁(𝒪(1))` and `ξ = h ∩ -`. This file proves

* `GRR.pushforward_cap_pullbackAQ_mul_ev`: `π_*((π^*c · F(h)) ∩ [P]) = F_n · (c ∩ [Y])` for every
  power series `F`, from `π_*(ξ^j ∩ π^*α) = [j = n] α` (Stacks 02TW; `ξ^{n+1} ∩ π^*α = 0` along
  the projective tower of `ℙⁿ_Y`) and `π^*[Y] = [P]`;
* `GRR.toddTangent_projectiveSpaceOver`: `td(T_P) = π^* td(T_Y) · (h / (1 - e^{-h}))^{n+1}`, from
  the relative cotangent sequence and the Euler sequence of `ℙⁿ_ℤ` pulled back to `P`;
* `GRR.projectionTauFormula`: `GRR.ProjectionTauFormula`, using `ch [𝒪(-j)] = e^{-j h}` and the
  coefficients of `e^{-j x} (x / (1 - e^{-x}))^{n+1}`.
-/

open AlgebraicGeometry CategoryTheory Stacks.Chow
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)
open scoped TensorProduct

universe u

namespace GRR

section Twists

variable {Y : Scheme.{u}} (n : ℕ)

instance isInvertible_twistOver (d : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (projectiveSpaceOver n Y).sheaf.obj
      (projectiveSpaceOver n Y).ringCatSheaf.property (twistOver n Y d) :=
  Stacks.AlgebraicGeometry.ProjTwistTensorPow.isInvertibleModule_twistOver n Y d

theorem isFiniteLocallyFree_twistOver (d : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (projectiveSpaceOver n Y).ringCatSheaf) (twistOver n Y d) :=
  haveI := isFiniteLocallyFreeOfRank_one_of_isInvertible (twistOver n Y d)
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1

/-- `[𝒪(a)] · [𝒪(b)] = [𝒪(a + b)]`. -/
theorem twistClass_add (a b : ℤ) :
    twistClass Y n a * twistClass Y n b = twistClass Y n (a + b) := by
  rw [twistClass, twistClass, twistClass,
    VectorBundleKZero.classOf_mul _ _ (isFiniteLocallyFree_twistOver n a)
      (isFiniteLocallyFree_twistOver n b)]
  have := isFiniteLocallyFree_twistOver (Y := Y) n a
  have := isFiniteLocallyFree_twistOver (Y := Y) n b
  exact VectorBundleKZero.classOf_eq_of_iso
    (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOverMulIso n Y a b)
    (AlgebraicGeometry.isFiniteLocallyFree_tensorObj _ _)

/-- `[𝒪(0)] = 1`. -/
theorem twistClass_zero : twistClass Y n 0 = 1 := by
  rw [twistClass, ← VectorBundleKZero.classOf_unit]
  exact VectorBundleKZero.classOf_eq_of_iso
    (Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistZeroIsoUnit n Y)
    (isFiniteLocallyFree_twistOver n 0)

end Twists

section ChernTwists

variable (k : Type u) [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsSmoothFT k sY]
  (n : ℕ)

/-- `ch [𝒪(-1)] = e^{-h}`, `h = c₁(𝒪(1))`: `[𝒪(-1)]` is inverse to `[𝒪(1)]`. -/
theorem ch_twistClass_neg_one :
    ch (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY) (twistClass Y n (-1)) =
      (chowGraded (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)).ev
        (firstChernQ (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
          (twistOver n Y 1)) expNeg := by
  set C := fieldChowSituation k
  set sP := (projectiveSpaceOver n Y ↘ Y) ≫ sY
  set G := chowGraded C sP
  set h := firstChernQ C sP (twistOver n Y 1)
  have hh : G.comp 0 h = 0 := isHom_firstChernQ C sP (twistOver n Y 1) 0 zero_ne_one
  have e1 : ch C sP (twistClass Y n 1) = G.ev h (PowerSeries.exp ℚ) :=
    ch_classOf_invertible C sP (twistOver n Y 1)
  have h1 : ch C sP (twistClass Y n (-1)) * G.ev h (PowerSeries.exp ℚ) = 1 := by
    rw [← e1, ← map_mul, twistClass_add, show (-1 : ℤ) + 1 = 0 by norm_num, twistClass_zero,
      map_one]
  have h2 : G.ev h (PowerSeries.exp ℚ) * G.ev h expNeg = 1 := by
    rw [← G.ev_mul hh, exp_mul_expNeg, G.ev_one hh]
  calc ch C sP (twistClass Y n (-1))
      = ch C sP (twistClass Y n (-1)) * (G.ev h (PowerSeries.exp ℚ) * G.ev h expNeg) := by
        rw [h2, mul_one]
    _ = G.ev h expNeg := by rw [← mul_assoc, h1, one_mul]

/-- `ch [𝒪(-j)] = e^{-j h}`, `h = c₁(𝒪(1))`. -/
theorem ch_twistClass_neg (j : ℕ) :
    ch (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY) (twistClass Y n (-(j : ℤ))) =
      (chowGraded (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)).ev
        (firstChernQ (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
          (twistOver n Y 1)) (expNeg ^ j) := by
  set C := fieldChowSituation k
  set sP := (projectiveSpaceOver n Y ↘ Y) ≫ sY
  set G := chowGraded C sP
  set h := firstChernQ C sP (twistOver n Y 1)
  have hh : G.comp 0 h = 0 := isHom_firstChernQ C sP (twistOver n Y 1) 0 zero_ne_one
  induction j with
  | zero => rw [Nat.cast_zero, neg_zero, twistClass_zero, map_one, pow_zero, G.ev_one hh]
  | succ j ih =>
    rw [show (-((j + 1 : ℕ) : ℤ)) = -(j : ℤ) + -1 by push_cast; ring, ← twistClass_add,
      map_mul, ih, ch_twistClass_neg_one, pow_succ, G.ev_mul hh]

end ChernTwists

section Tower

/-- Capping with a power is unchanged by moving between equal degrees. -/
theorem capPow_capOnChow_cast' (C : ChowSituation.{u}) {P : Scheme.{u}} (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] (ξ : ChernCapOperator C sP) (s : ℕ) {a a' m b : ℤ} (ha : a = a')
    (h : a = m + s) (h' : a' = m + s) (e : b = a + 1) (e' : b = a' + 1) (x : chowGroup C sP b) :
    capPow C sP ξ s a m h (ξ.capOnChow C sP a (chowGroupCast C sP e x)) =
      capPow C sP ξ s a' m h' (ξ.capOnChow C sP a' (chowGroupCast C sP e' x)) := by
  subst ha; rfl

/-- The first Chern class of a trivial invertible module caps to zero. -/
theorem invCap_capOnChow_eq_zero_of_iso (C : ChowSituation.{u}) {P : Scheme.{u}} (sP : P ⟶ C.S)
    [LocallyOfFiniteType sP] (L : P.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
    (e : L ≅ SheafOfModules.unit P.ringCatSheaf) (k : ℤ) (x : chowGroup C sP (k + 1)) :
    (invCap C sP L).capOnChow C sP k x = 0 := by
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
  rw [invCap_capOnChow_congr C sP L _ e]
  exact (invCap_capOnChow_mk C sP _ k α).trans (firstChernClassCapOfInvertible_unit C sP k α)

/-- Pushforward along a closed immersion `i` carries `c₁(i^*L)^s ∩ -` to `c₁(L)^s ∩ -`. -/
theorem properChowPushforward_invCap_capPow' (C : ChowSituation.{u}) {D P : Scheme.{u}}
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

/-- **`ξ^{n+1} ∩ π^*β = 0` along a projective tower of fibre dimension `n`**: by induction along
the tower, `ξ ∩ π^*β` is pushed forward from the divisor `D`, a tower of fibre dimension
`n - 1`, and at the bottom the twist is trivial. -/
theorem capPow_succ_bundlePullback_of_isProjectiveTower (C : ChowSituation.{u}) {n : ℕ}
    {P U : Scheme.{u}} {π : P ⟶ U} {L : P.Modules} (h : IsProjectiveTower n π L) :
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
    rw [capPow_succ_apply, capPow_zero_apply,
      invCap_capOnChow_eq_zero_of_iso C sP L hL.some, map_zero]
  | succ n π L hπ' s hD hq htower haff ih =>
    intro sU _ sP _ hsP _ _ _ hπ k β
    have := hD.2
    set i := (Stacks.Divisors.zeroScheme _ L s).subschemeι with hi
    let : AlgebraicGeometry.SheafOfModules.IsInvertible _ _
        ((Scheme.Modules.pullback i).obj L) := isInvertible_presheaf_modulePullback L i
    have hstep := capOnChow_bundlePullback_eq C sU sP π hsP n hπ L s hD hq k β
    have hIH := ih sU (i ≫ sP) (by rw [Category.assoc, hsP]) hq k β
    rw [capPow_succ_apply,
      capPow_capOnChow_cast' C sP (invCap C sP L) (n + 1) (a' := k + n) (by push_cast; ring) _
        (by push_cast; ring) _ (by push_cast; ring),
      hstep, ← properChowPushforward_invCap_capPow' C sP i L, hIH, map_zero]

end Tower

section RationalCap

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **Capping with `c₁(L) ∈ A^1(X)` is the first Chern class operation `c₁(L) ∩ -`.** -/
theorem chowCohomologyCap_firstChernTotal_heq (k : ℤ) (x : chowGroup C sX k) :
    chowCohomologyCap C (gysinSystemOfInvertible C) sX ((1 : ℕ) : ℤ)
        (TotalChowClass.firstChernTotal C sX L 1) k x ≍
      (invCap C sX L).capOnChow C sX (k - 1) (chowGroupCast C sX (by omega) x) := by
  have := GenuineChern.isInvertible_pullback (𝟙 X) L
  refine (chowCohomologyCap_heq_idRule_ofGysinSystem C _ sX _ _ k x).trans ?_
  rw [← TotalChowClass.op_apply]
  refine (TotalChowClass.op_firstChernTotal_one_heq C sX L (𝟙 X) k _).trans ?_
  rw [invCap_capOnChow_congr C (𝟙 X ≫ sX) ((Scheme.Modules.pullback (𝟙 X)).obj L) L
    ((Scheme.Modules.pullbackId X).app L)]
  refine (chowGroupCongr_heq C (Category.id_comp sX) _ _).symm.trans ?_
  rw [chowGroupCongr_invCap_capOnChow C L (Category.id_comp sX)]
  refine heq_of_eq (congrArg _ (eq_of_heq ?_))
  exact (chowGroupCongr_heq C _ _ _).trans ((chowGroupCast_heq C _ _ _).trans
    ((chowGroupCongr_heq C _ _ _).trans (chowGroupCast_heq C _ _ _).symm))

/-- `c₁(L) ∩ -` on a generator of `CH_*(X) ⊗ ℚ`. -/
theorem rationalChowCap_firstChernQ_one_of_tmul (a : ℤ) (q : ℚ) (x : chowGroup C sX a) :
    rationalChowCap C (gysinSystemOfInvertible C) sX ((1 : ℕ) : ℤ) (firstChernQ C sX L 1)
        (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j) a (q ⊗ₜ x)) =
      DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j) (a - 1)
        (q ⊗ₜ (invCap C sX L).capOnChow C sX (a - 1) (chowGroupCast C sX (by omega) x)) := by
  rw [firstChernQ, RationalTotalChowClass.ofTotalChowClass_apply, rationalChowCap_of_tmul,
    one_mul]
  exact of_tmul_eq_of_tmul_of_heq C sX (by simp) q
    (chowCohomologyCap_firstChernTotal_heq C sX L a x)

end RationalCap

section CapPowers

variable (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [LocallyOfFiniteType sX] (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- The cap action on `CH_a(X) ⊗ ℚ` only sees the components of degree at most `a`. -/
theorem cap_of_congr {c c' : AQ k sX} (a : ℤ) (N : ℕ) (haN : a ≤ N) (h : ∀ p ≤ N, c p = c' p)
    (t : ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sX a) :
    cap k sX c (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sX j) a t) =
      cap k sX c'
        (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sX j) a t) := by
  rw [← DirectSum.lof_eq_of ℚ]
  unfold cap
  rw [totalRationalChowCap_lof_eq_sum_range (fieldChowSituation k) _ sX 0
      (relativeDimension_fieldChowSituation_nonneg k sX) _ a t N (by omega),
    totalRationalChowCap_lof_eq_sum_range (fieldChowSituation k) _ sX 0
      (relativeDimension_fieldChowSituation_nonneg k sX) _ a t N (by omega)]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [RationalTotalChowClass.ofFamily_symm_apply, RationalTotalChowClass.ofFamily_symm_apply,
    h p (Nat.lt_succ_iff.mp (Finset.mem_range.mp hp))]

theorem cap_one : cap k sX 1 = 1 :=
  totalRationalChowCap_one (fieldChowSituation k) sX

theorem cap_pow (c : AQ k sX) (j : ℕ) : cap k sX (c ^ j) = cap k sX c ^ j := by
  induction j with
  | zero => rw [pow_zero, pow_zero, cap_one]
  | succ j ih => rw [pow_succ, pow_succ, cap_mul, ih]

theorem cap_sum_smul (c : ℕ → AQ k sX) (w : ℕ → ℚ) (s : Finset ℕ) :
    cap k sX (∑ j ∈ s, w j • c j) = ∑ j ∈ s, w j • cap k sX (c j) := by
  let Φ : AQ k sX →ₗ[ℚ] Module.End ℚ (CHQ k sX) :=
    (totalRationalChowCap (fieldChowSituation k) (gysinSystemOfInvertible _) sX).comp
      RationalTotalChowClass.ofFamily.symm.toLinearMap
  have hΦ : ∀ c, cap k sX c = Φ c := fun _ => rfl
  rw [hΦ, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul, hΦ]

/-- `c₁(L) ∩ -` on a generator, through the total cap action. -/
theorem cap_firstChernQ_of_tmul (a : ℤ) (q : ℚ) (x : chowGroup (fieldChowSituation k) sX a) :
    cap k sX (firstChernQ (fieldChowSituation k) sX L)
        (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sX j) a (q ⊗ₜ x)) =
      DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sX j) (a - 1)
        (q ⊗ₜ (invCap (fieldChowSituation k) sX L).capOnChow (fieldChowSituation k) sX (a - 1)
          (chowGroupCast (fieldChowSituation k) sX (by omega) x)) := by
  rw [← DirectSum.lof_eq_of ℚ]
  unfold cap
  rw [totalRationalChowCap_lof_eq_sum_range (fieldChowSituation k) _ sX 0
      (relativeDimension_fieldChowSituation_nonneg k sX) _ a _ (a.toNat + 1) (by omega),
    Finset.sum_eq_single 1]
  · rw [DirectSum.lof_eq_of]
    exact rationalChowCap_firstChernQ_one_of_tmul (fieldChowSituation k) sX L a q x
  · intro p _ hp
    have h0 : (RationalTotalChowClass.ofFamily.symm (firstChernQ (fieldChowSituation k) sX L)) p =
        (0 : rationalChowCohomologyComponent (fieldChowSituation k)
          (gysinSystemOfInvertible (fieldChowSituation k)) sX (p : ℤ)) :=
      isHom_firstChernQ (fieldChowSituation k) sX L p hp
    rw [h0, map_zero, LinearMap.zero_apply]
  · intro h1
    exact absurd (Finset.mem_range.mpr (by omega)) h1

/-- `c₁(L)^j ∩ -` on a generator is the `j`-th power of the first Chern class operation. -/
theorem cap_firstChernQ_pow_of_tmul (j : ℕ) (a : ℤ) (q : ℚ)
    (x : chowGroup (fieldChowSituation k) sX a) :
    ((cap k sX (firstChernQ (fieldChowSituation k) sX L)) ^ j)
        (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sX j) a (q ⊗ₜ x)) =
      DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sX j) (a - j)
        (q ⊗ₜ capPow (fieldChowSituation k) sX (invCap (fieldChowSituation k) sX L) j a (a - j)
          (by ring) x) := by
  induction j generalizing a with
  | zero =>
    rw [pow_zero, Module.End.one_apply]
    refine of_tmul_eq_of_tmul_of_heq (fieldChowSituation k) sX (by simp) q ?_
    rw [capPow_zero_apply]
    exact (chowGroupCast_heq (fieldChowSituation k) sX _ x).symm
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, cap_firstChernQ_of_tmul, ih, capPow_succ_apply]
    refine of_tmul_eq_of_tmul_of_heq (fieldChowSituation k) sX (by push_cast; ring) q ?_
    exact capPow_heq_of_heq (fieldChowSituation k) sX _ j _ _ rfl (by push_cast; ring) HEq.rfl

/-- **`F(c₁(L)) ∩ -` on a generator of `CH_a(X) ⊗ ℚ`**, for every `N ≥ a`. -/
theorem cap_ev_firstChernQ_of_tmul (F : PowerSeries ℚ) (a : ℤ) (N : ℕ) (haN : a ≤ N) (q : ℚ)
    (x : chowGroup (fieldChowSituation k) sX a) :
    cap k sX ((chowGraded (fieldChowSituation k) sX).ev (firstChernQ (fieldChowSituation k) sX L) F)
        (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sX j) a (q ⊗ₜ x)) =
      ∑ j ∈ Finset.range (N + 1), PowerSeries.coeff j F •
        DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sX j) (a - j)
          (q ⊗ₜ capPow (fieldChowSituation k) sX (invCap (fieldChowSituation k) sX L) j a (a - j)
            (by ring) x) := by
  have hh : (chowGraded (fieldChowSituation k) sX).comp 0 (firstChernQ (fieldChowSituation k) sX L)
      = 0 := isHom_firstChernQ (fieldChowSituation k) sX L 0 zero_ne_one
  rw [cap_of_congr k sX (c := (chowGraded (fieldChowSituation k) sX).ev
        (firstChernQ (fieldChowSituation k) sX L) F) a N haN
      (c' := ∑ j ∈ Finset.range (N + 1),
        PowerSeries.coeff j F • firstChernQ (fieldChowSituation k) sX L ^ j)
      (fun p hp => (chowGraded (fieldChowSituation k) sX).comp_ev_of_le hh F hp),
    cap_sum_smul, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.smul_apply, cap_pow, cap_firstChernQ_pow_of_tmul]

end CapPowers

section BundleProjection

variable (C : ChowSituation.{u}) {P U : Scheme.{u}} (sU : U ⟶ C.S) [LocallyOfFiniteType sU]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ U) [LocallyOfFiniteType π] [Flat π]
  [IsProper π] (hsP : π ≫ sU = sP) (n : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π n)
  (ξ : ChernCapOperator C sP)

-- `LocallyOfFiniteType π` is the instance argument `bundlePullback` is stated with.
set_option linter.overlappingInstances false in
theorem properChowPushforward_capPow_eq_bundleProjection (s : ℕ) (k m : ℤ)
    (h : k + n = m + s) (α : chowGroup C sU k) :
    properChowPushforward C sP sU π hsP m (properPushforwardDescends C _ _ _ _ _)
        (capPow C sP ξ s (k + n) m h (bundlePullback C sU sP π hsP n hπ k α)) =
      bundleProjection C sU sP π hsP n hπ ξ s k m h α :=
  rfl

-- `LocallyOfFiniteType π` is the instance argument `bundlePullback` is stated with.
set_option linter.overlappingInstances false in
theorem bundleProjection_heq (s : ℕ) (k : ℤ) {m m' : ℤ} (hm : m = m') (h : k + n = m + s)
    (h' : k + n = m' + s) (α : chowGroup C sU k) :
    bundleProjection C sU sP π hsP n hπ ξ s k m h α ≍
      bundleProjection C sU sP π hsP n hπ ξ s k m' h' α := by
  subst hm
  rfl

end BundleProjection

section FundamentalClassSmooth

/-! The flat pullback of the fundamental class of a smooth scheme, `f^*[X]_m = [Y]_{m+r}` in every
degree. This is `Stacks.WeilCohomology.flatPullbackChow_fundamentalChowClass_of_smooth`, whose
module is not among the built ones; its proof is reproduced from built modules. -/

open Stacks.WeilCohomology

/-- If `q = f ≫ g` with `f` flat of relative dimension `r` and `g` of relative dimension `s`,
then `q` has relative dimension `r + s`. -/
theorem relativeDimension_of_eq_comp_smooth {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {q : X ⟶ Z} [LocallyOfFiniteType q] [LocallyOfFiniteType f] [Flat f] [LocallyOfFiniteType g]
    {r s : ℕ} (hf : RelativeDimension f r) (hg : RelativeDimension g s) (e : q = f ≫ g) :
    RelativeDimension q (r + s) := by
  subst e
  exact RelativeDimension.comp_of_flat _ _ hf hg

/-- `f_d : Y_d ⟶ X_d` is locally of finite type, being a base change of `f`. -/
theorem locallyOfFiniteType_dimPartOverHom_smooth {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX] (f : Y ⟶ X) [LocallyOfFiniteType f] (d : ℕ) :
    LocallyOfFiniteType (dimPartOverHom sX f d) :=
  MorphismProperty.of_isPullback (isPullback_morphismRestrict f _).flip inferInstance

/-- `f_d : Y_d ⟶ X_d` is flat, being a base change of `f`. -/
theorem flat_dimPartOverHom_smooth {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX] (f : Y ⟶ X) [Flat f] (d : ℕ) :
    Flat (dimPartOverHom sX f d) :=
  MorphismProperty.of_isPullback (isPullback_morphismRestrict f _).flip inferInstance

/-- `f_d : Y_d ⟶ X_d` has the same relative dimension as `f`. -/
theorem relativeDimension_dimPartOverHom_smooth {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX] (f : Y ⟶ X) [LocallyOfFiniteType f]
    {r : ℕ} (hr : RelativeDimension f r) (d : ℕ) [LocallyOfFiniteType (dimPartOverHom sX f d)] :
    RelativeDimension (dimPartOverHom sX f d) r :=
  RelativeDimension.of_isPullback (isPullback_morphismRestrict f _).flip hr

section FundamentalClass

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX]
  (sY : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sY] (f : Y ⟶ X)
  [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sX = sY) (r : ℕ) (hr : RelativeDimension f r)

include hf in
/-- On the part `Y_d = f⁻¹(X_d)` over the part of `X` of dimension `d`, the restriction of `f^*α`
is the flat pullback of the restriction of `α` along `f_d : Y_d ⟶ X_d` (Stacks 02RD). -/
theorem chowGroupRestrict_flatPullbackChow_heq_smooth (d : ℕ) (m : ℤ)
    (α : chowGroup (fieldChowSituation k) sX m) :
    letI : LocallyOfFiniteType (dimPartOverHom sX f d) :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict f _).flip inferInstance
    letI : Flat (dimPartOverHom sX f d) :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict f _).flip inferInstance
    chowGroupRestrict (fieldChowSituation k) sY ((dimPartOver sX f d).ι ≫ sY)
        (dimPartOver sX f d).ι rfl (m + r)
        (flatPullbackChowOfRelativeDimension (fieldChowSituation k) sY sX f hf r hr m α) ≍
      flatPullbackChowOfRelativeDimension (fieldChowSituation k) ((dimPartOver sX f d).ι ≫ sY)
        (partBase sX d) (dimPartOverHom sX f d)
        (by rw [dimPartOverHom_comp_partBase, hf]) r
        (RelativeDimension.of_isPullback (isPullback_morphismRestrict f _).flip hr) m
        (chowGroupRestrict (fieldChowSituation k) sX (partBase sX d) (dimPart sX d).ι rfl m α) := by
  have := locallyOfFiniteType_dimPartOverHom_smooth sX f d
  have := flat_dimPartOverHom_smooth sX f d
  have hfd := relativeDimension_dimPartOverHom_smooth sX f hr d
  have h1 := heq_chowGroupRestrict_flatPullbackChow (fieldChowSituation k) sY
    ((dimPartOver sX f d).ι ≫ sY) (dimPartOver sX f d).ι rfl
    (relativeDimension_of_isOpenImmersion (dimPartOver sX f d).ι) (m + r)
    (flatPullbackDescends _ _ _ _ _ _ _ _)
    (flatPullbackChowOfRelativeDimension (fieldChowSituation k) sY sX f hf r hr m α)
  have h2 := flatPullbackChow_comp (fieldChowSituation k) ((dimPartOver sX f d).ι ≫ sY) sY sX
    (dimPartOver sX f d).ι f rfl hf 0 r
    (relativeDimension_of_isOpenImmersion (dimPartOver sX f d).ι) hr m
    (flatPullbackDescends _ _ _ _ _ _ _ _) (flatPullbackDescends _ _ _ _ _ _ _ _)
    (flatPullbackDescends _ _ _ _ _ _ _ _) α
  have hcomm : (dimPartOver sX f d).ι ≫ f = dimPartOverHom sX f d ≫ (dimPart sX d).ι :=
    (morphismRestrict_ι f _).symm
  have h3 : ∀ (g g' : (dimPartOver sX f d).toScheme ⟶ X) [LocallyOfFiniteType g] [Flat g]
      [LocallyOfFiniteType g'] [Flat g'] (e : g = g') (hg : g ≫ sX = (dimPartOver sX f d).ι ≫ sY)
      (hg' : g' ≫ sX = (dimPartOver sX f d).ι ≫ sY) {s s' : ℕ} (es : s = s')
      (hs : RelativeDimension g s) (hs' : RelativeDimension g' s'),
      flatPullbackChowOfRelativeDimension (fieldChowSituation k) ((dimPartOver sX f d).ι ≫ sY) sX
          g hg s hs m α ≍
        flatPullbackChowOfRelativeDimension (fieldChowSituation k) ((dimPartOver sX f d).ι ≫ sY)
          sX g' hg' s' hs' m α := by
    intro g g' _ _ _ _ e hg hg' s s' es hs hs'
    subst e es
    rfl
  have h4 := flatPullbackChow_comp (fieldChowSituation k) ((dimPartOver sX f d).ι ≫ sY)
    (partBase sX d) sX (dimPartOverHom sX f d) (dimPart sX d).ι
    (by rw [dimPartOverHom_comp_partBase, hf]) rfl r 0 hfd
    (relativeDimension_of_isOpenImmersion _) m (flatPullbackDescends _ _ _ _ _ _ _ _)
    (flatPullbackDescends _ _ _ _ _ _ _ _) (flatPullbackDescends _ _ _ _ _ _ _ _) α
  have h5 := heq_chowGroupRestrict_flatPullbackChow (fieldChowSituation k) sX (partBase sX d)
    (dimPart sX d).ι rfl (relativeDimension_of_isOpenImmersion _) m
    (flatPullbackDescends _ _ _ _ _ _ _ _) α
  refine h1.trans (h2.trans ((h3 _ _ hcomm _ _ (by omega) _ _).trans (h4.symm.trans ?_)))
  have h6 : ∀ {a a' : ℤ} (e : a = a') {x : chowGroup (fieldChowSituation k) (partBase sX d) a}
      {x' : chowGroup (fieldChowSituation k) (partBase sX d) a'}, x ≍ x' →
      flatPullbackChowOfRelativeDimension (fieldChowSituation k) ((dimPartOver sX f d).ι ≫ sY)
          (partBase sX d) (dimPartOverHom sX f d) (by rw [dimPartOverHom_comp_partBase, hf]) r
          hfd a x ≍
        flatPullbackChowOfRelativeDimension (fieldChowSituation k) ((dimPartOver sX f d).ι ≫ sY)
          (partBase sX d) (dimPartOverHom sX f d) (by rw [dimPartOverHom_comp_partBase, hf]) r
          hfd a' x' := by
    intro a a' e x x' hx
    subst e
    cases hx
    rfl
  exact h6 (by simp) h5.symm

include hf in
/-- **Flat pullback of the fundamental class of a smooth scheme over a field.** For `X` smooth
over `k` and `f : Y ⟶ X` flat of relative dimension `r`, `f^*[X]_m = [Y]_{m+r}` in every degree
`m`, with no bound on the dimension of `X`. On the part `Y_d = f⁻¹(X_d)` lying over the part of
`X` of dimension `d` this is Stacks 02RE for `X_d` when `d = m`, and both sides vanish otherwise,
`X_d` and `Y_d` being equidimensional of dimensions `d` and `d + r`. -/
theorem flatPullbackChow_fundamentalChowClass_smooth (m : ℤ) :
    flatPullbackChowOfRelativeDimension (fieldChowSituation k) sY sX f hf r hr m
        (fundamentalChowClass (fieldChowSituation k) sX m) =
      fundamentalChowClass (fieldChowSituation k) sY (m + r) := by
  have hdec : IsClopenDecomposition fun d : ULift.{u} ℕ ↦
      (dimPartOver sX f d.down).ι.opensRange := by
    have h := ((isClopenDecomposition_dimPart sX).preimage f).opensRange_ι_equiv Equiv.ulift
    simpa only [Scheme.Opens.opensRange_ι, Equiv.ulift_apply] using h
  apply (chowGroupClopenRestrictEquiv (fieldChowSituation k) sY
    (fun d : ULift.{u} ℕ ↦ (dimPartOver sX f d.down).ι ≫ sY)
    (fun d : ULift.{u} ℕ ↦ (dimPartOver sX f d.down).ι) (fun _ ↦ rfl) hdec (m + r)).injective
  funext ⟨d⟩
  simp only [chowGroupClopenRestrictEquiv_apply]
  rw [chowGroupRestrict_fundamentalChowClass_of_isOpenImmersion]
  have := locallyOfFiniteType_dimPartOverHom_smooth sX f d
  have := flat_dimPartOverHom_smooth sX f d
  have hfd := relativeDimension_dimPartOverHom_smooth sX f hr d
  have hres := chowGroupRestrict_flatPullbackChow_heq_smooth sX sY f hf r hr d m
    (fundamentalChowClass (fieldChowSituation k) sX m)
  rw [chowGroupRestrict_fundamentalChowClass_of_isOpenImmersion] at hres
  refine eq_of_heq (hres.trans ?_)
  by_cases hdm : (d : ℤ) = m
  · subst hdm
    exact heq_of_eq (flatPullbackChow_fundamentalChowClass (fieldChowSituation k) _ _ _ _ r hfd _ _
      (schemeDeltaDimension_le_of_relativeDimension (partBase sX d)
        (relativeDimension_partBase sX d)))
  · -- `X_d` is equidimensional of dimension `d ≠ m`, and `Y_d` of dimension `d + r ≠ m + r`
    have hX0 : fundamentalChowClass (fieldChowSituation k) (partBase sX d) m = 0 := by
      have : LocallyOfFiniteType (𝟙 (dimPart sX d).toScheme ≫ partBase sX d) := by
        rw [Category.id_comp]; infer_instance
      have hY : RelativeDimension (𝟙 (dimPart sX d).toScheme ≫ partBase sX d) d := by
        have h := relativeDimension_of_eq_comp_smooth
          (q := 𝟙 (dimPart sX d).toScheme ≫ partBase sX d)
          (relativeDimension_of_isIso (𝟙 (dimPart sX d).toScheme))
          (relativeDimension_partBase sX d) rfl
        rwa [zero_add] at h
      rw [fundamentalChowClass, fundamentalCycle,
        cycleAssociatedToClosedSubscheme_eq_zero_of_relativeDimension (k := k) (partBase sX d)
          (𝟙 _) hY (Ne.symm hdm), map_zero]
    have hY0 :
        fundamentalChowClass (fieldChowSituation k) ((dimPartOver sX f d).ι ≫ sY) (m + r) = 0 := by
      have : LocallyOfFiniteType
          (𝟙 (dimPartOver sX f d).toScheme ≫ (dimPartOver sX f d).ι ≫ sY) := by
        rw [Category.id_comp]; infer_instance
      have hYd : RelativeDimension
          (𝟙 (dimPartOver sX f d).toScheme ≫ (dimPartOver sX f d).ι ≫ sY) (r + d) :=
        relativeDimension_of_eq_comp_smooth hfd (relativeDimension_partBase sX d)
          (by rw [Category.id_comp, dimPartOverHom_comp_partBase, hf])
      rw [fundamentalChowClass, fundamentalCycle,
        cycleAssociatedToClosedSubscheme_eq_zero_of_relativeDimension (k := k)
          ((dimPartOver sX f d).ι ≫ sY) (𝟙 _) hYd (by push_cast; omega), map_zero]
    rw [hX0, map_zero, hY0]

end FundamentalClass

end FundamentalClassSmooth

section Projective

variable (k : Type u) [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsSmoothFT k sY]
  (n : ℕ)

theorem isProjectiveTower_twistOver :
    IsProjectiveTower n (projectiveSpaceOver n Y ↘ Y) (twistOver n Y 1) :=
  Stacks.Chow.FreeTower.isProjectiveTower_projectiveSpaceOver n Y

/-- **`π_*(F(h) ∩ π^*α) = F_n α`** on `ℙⁿ_Y`, on a generator `α ∈ CH_e(Y)`. -/
theorem pushforward_cap_ev_bundlePullback (F : PowerSeries ℚ) (e : ℤ) (q : ℚ)
    (α : chowGroup (fieldChowSituation k) sY e) :
    rationalProperChowPushforward (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY) sY
        rfl
        (cap k ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
          ((chowGraded (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)).ev
            (firstChernQ (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
              (twistOver n Y 1)) F)
          (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k)
              ((projectiveSpaceOver n Y ↘ Y) ≫ sY) j) (e + n)
            (q ⊗ₜ bundlePullback (fieldChowSituation k) sY ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
              (projectiveSpaceOver n Y ↘ Y) rfl n (relativeDimension_projectiveSpaceOver n Y) e
              α))) =
      PowerSeries.coeff n F •
        DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) sY j) e (q ⊗ₜ α) := by
  set C := fieldChowSituation k
  set p := projectiveSpaceOver n Y ↘ Y
  set sP := p ≫ sY
  set L := twistOver n Y 1
  have hπ := relativeDimension_projectiveSpaceOver n Y
  have htower : IsProjectiveTower n p L := isProjectiveTower_twistOver n
  rw [cap_ev_firstChernQ_of_tmul k sP L F (e + n) ((e + n).toNat + n) (by omega) q _, map_sum,
    Finset.sum_eq_single n]
  · rw [map_smul, rationalProperChowPushforward_of_tmul,
      properChowPushforward_capPow_eq_bundleProjection C sY sP p rfl n hπ]
    congr 1
    refine of_tmul_eq_of_tmul_of_heq C sY (by ring) q ?_
    exact (bundleProjection_heq C sY sP p rfl n hπ _ n e (by ring) _ (by ring) α).trans
      (heq_of_eq (htower.bundleProjection_self C sY sP rfl hπ e α))
  · intro j _ hj
    rw [map_smul, rationalProperChowPushforward_of_tmul]
    rcases lt_or_gt_of_ne hj with hlt | hgt
    · rw [properChowPushforward_capPow_eq_bundleProjection C sY sP p rfl n hπ,
        bundleProjection_eq_zero_of_lt C sY sP p rfl n hπ _ j hlt, TensorProduct.tmul_zero,
        map_zero, smul_zero]
    · have hsplit : capPow C sP (invCap C sP L) j (e + n) (e + n - j) (by ring)
            (bundlePullback C sY sP p rfl n hπ e α) =
          capPow C sP (invCap C sP L) (j - (n + 1)) (e - 1) (e + n - j) (by omega)
            (capPow C sP (invCap C sP L) (n + 1) (e + n) (e - 1) (by push_cast; ring)
              (bundlePullback C sY sP p rfl n hπ e α)) := by
        rw [capPow_capPow]
        exact capPow_congr C sP _ (by omega) _ _ _ _
      rw [hsplit, capPow_succ_bundlePullback_of_isProjectiveTower C htower sY sP rfl hπ e α,
        map_zero, map_zero,
        TensorProduct.tmul_zero, map_zero, smul_zero]
  · intro hn
    exact absurd (Finset.mem_range.mpr (by omega)) hn

/-- **`π^*[Y] = [P]`** for the rational fundamental classes of `ℙⁿ_Y ⟶ Y`. -/
theorem rationalChowMap_bundlePullback_fundamentalClass :
    rationalChowMap (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY) sY
        (fun e => e + n)
        (fun e => bundlePullback (fieldChowSituation k) sY ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
          (projectiveSpaceOver n Y ↘ Y) rfl n (relativeDimension_projectiveSpaceOver n Y) e)
        (fundamentalClass k sY) =
      fundamentalClass k ((projectiveSpaceOver n Y ↘ Y) ≫ sY) := by
  set C := fieldChowSituation k
  set p := projectiveSpaceOver n Y ↘ Y
  set sP := p ≫ sY
  have hπ := relativeDimension_projectiveSpaceOver n Y
  have := isNoetherian k sY
  have := isNoetherian k sP
  have hfund : ∀ e : ℤ, bundlePullback C sY sP p rfl n hπ e (fundamentalChowClass C sY e) =
      fundamentalChowClass C sP (e + n) :=
    fun e => flatPullbackChow_fundamentalChowClass_smooth sY sP p rfl n hπ e
  set g : ℤ → CHQ k sP := fun d =>
    DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sP j) d
      ((1 : ℚ) ⊗ₜ fundamentalChowClass C sP d) with hg
  have hvanP : ∀ d ∈ (fundamentalClassDegrees_finite C sP).toFinset ∪
      (fundamentalClassDegrees_finite C sY).toFinset.image (· + (n : ℤ)),
      d ∉ (fundamentalClassDegrees_finite C sP).toFinset → g d = 0 := by
    intro d _ hd
    rw [Set.Finite.mem_toFinset] at hd
    rw [hg]
    dsimp only
    rw [fundamentalChowClass, fundamentalCycle_eq_zero_of_notMem_fundamentalClassDegrees C sP hd,
      map_zero, TensorProduct.tmul_zero, map_zero]
  have hcast : ∀ a b : ℤ, a = b → fundamentalChowClass C sP a = 0 →
      fundamentalChowClass C sP b = 0 := by
    rintro a b rfl h
    exact h
  have hvanY : ∀ d ∈ (fundamentalClassDegrees_finite C sP).toFinset ∪
      (fundamentalClassDegrees_finite C sY).toFinset.image (· + (n : ℤ)),
      d ∉ (fundamentalClassDegrees_finite C sY).toFinset.image (· + (n : ℤ)) → g d = 0 := by
    intro d _ hd
    have he : d - n ∉ fundamentalClassDegrees C sY := fun h =>
      hd (Finset.mem_image.mpr ⟨d - n, (Set.Finite.mem_toFinset _).mpr h, by ring⟩)
    have h0 : fundamentalChowClass C sY (d - n) = 0 := by
      rw [fundamentalChowClass, fundamentalCycle_eq_zero_of_notMem_fundamentalClassDegrees C sY he,
        map_zero]
    have h1 : fundamentalChowClass C sP (d - n + n) = 0 := by
      rw [← hfund, h0, map_zero]
    rw [hg]
    dsimp only
    rw [hcast _ _ (by ring) h1, TensorProduct.tmul_zero, map_zero]
  rw [fundamentalClass, fundamentalClass, rationalFundamentalClass_eq,
    rationalFundamentalClass_eq, map_sum]
  have hterm : ∀ e ∈ (fundamentalClassDegrees_finite C sY).toFinset,
      rationalChowMap C sP sY (fun e => e + n)
          (fun e => bundlePullback C sY sP p rfl n hπ e)
          (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sY j) e
            ((1 : ℚ) ⊗ₜ fundamentalChowClass C sY e)) = g (e + n) := by
    intro e _
    rw [rationalChowMap_of_tmul, hfund]
  rw [Finset.sum_congr rfl hterm,
    ← Finset.sum_image (f := g) (fun a _ b _ h => by simpa using h),
    Finset.sum_subset Finset.subset_union_right hvanY,
    ← Finset.sum_subset Finset.subset_union_left hvanP]

/-- **`π_*(F(h) ∩ [ℙⁿ_Y]) = F_n [Y]`**. -/
theorem pushforward_cap_ev_fundamentalClass (F : PowerSeries ℚ) :
    rationalProperChowPushforward (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY) sY
        rfl
        (cap k ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
          ((chowGraded (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)).ev
            (firstChernQ (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
              (twistOver n Y 1)) F)
          (fundamentalClass k ((projectiveSpaceOver n Y ↘ Y) ≫ sY))) =
      PowerSeries.coeff n F • fundamentalClass k sY := by
  set C := fieldChowSituation k
  set p := projectiveSpaceOver n Y ↘ Y
  set sP := p ≫ sY
  have hπ := relativeDimension_projectiveSpaceOver n Y
  rw [← rationalChowMap_bundlePullback_fundamentalClass k sY n]
  have hlin := rationalChowHomology_linearMap_ext C sY
    (f := (rationalProperChowPushforward C sP sY rfl) ∘ₗ
      (cap k sP ((chowGraded C sP).ev (firstChernQ C sP (twistOver n Y 1)) F)) ∘ₗ
      (rationalChowMap C sP sY (fun e => e + n)
        (fun e => bundlePullback C sY sP p rfl n hπ e)))
    (g := PowerSeries.coeff n F • LinearMap.id)
    (fun e q α => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, rationalChowMap_of_tmul,
        LinearMap.smul_apply, LinearMap.id_apply]
      exact pushforward_cap_ev_bundlePullback k sY n F e q α)
  exact LinearMap.congr_fun hlin _

/-- **The integral over the fibres of `ℙⁿ_Y ⟶ Y`**: for a power series `F` and a class `c` on
`Y`, `π_*((π^*c · F(h)) ∩ [ℙⁿ_Y]) = F_n · (c ∩ [Y])`, `h = c₁(𝒪(1))`. -/
theorem pushforward_cap_pullbackAQ_mul_ev (F : PowerSeries ℚ) (c : AQ k sY) :
    rationalProperChowPushforward (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
        sY rfl
        (cap k ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
          (pullbackAQ (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY) sY
              (projectiveSpaceOver n Y ↘ Y) rfl c *
            (chowGraded (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)).ev
              (firstChernQ (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
                (twistOver n Y 1)) F)
          (fundamentalClass k ((projectiveSpaceOver n Y ↘ Y) ≫ sY))) =
      PowerSeries.coeff n F • cap k sY c (fundamentalClass k sY) := by
  set C := fieldChowSituation k
  set p := projectiveSpaceOver n Y ↘ Y
  set sP := p ≫ sY
  set γ := cap k sP ((chowGraded C sP).ev (firstChernQ C sP (twistOver n Y 1)) F)
    (fundamentalClass k sP)
  have hproj : rationalProperChowPushforward C sP sY rfl (cap k sP (pullbackAQ C sP sY p rfl c) γ) =
      cap k sY c (rationalProperChowPushforward C sP sY rfl γ) :=
    rationalProperChowPushforward_totalRationalChowCap_pullbackAQ C sP sY p rfl
      (bddBelow_relativeDimension_field k sP) (bddBelow_relativeDimension_field k sY) c γ
  rw [cap_mul, Module.End.mul_apply, hproj, pushforward_cap_ev_fundamentalClass, map_smul]

end Projective

section Final

variable (k : Type u) [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsSmoothFT k sY]
  (n : ℕ)

/-- **`π_* τ(g_j(β))`, from the Todd class of `ℙⁿ_Y` and the integral over the fibres.** -/
theorem projectionTauFormula_of
    (hT : toddTangent k ((projectiveSpaceOver n Y ↘ Y) ≫ sY) =
      pullbackAQ (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY) sY
          (projectiveSpaceOver n Y ↘ Y) rfl (toddTangent k sY) *
        (chowGraded (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)).ev
          (firstChernQ (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
            (twistOver n Y 1)) toddSeries ^ (n + 1))
    (hI : ∀ (F : PowerSeries ℚ) (c : AQ k sY),
      rationalProperChowPushforward (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
          sY rfl
          (cap k ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
            (pullbackAQ (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY) sY
                (projectiveSpaceOver n Y ↘ Y) rfl c *
              (chowGraded (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)).ev
                (firstChernQ (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
                  (twistOver n Y 1)) F)
            (fundamentalClass k ((projectiveSpaceOver n Y ↘ Y) ≫ sY))) =
        PowerSeries.coeff n F • cap k sY c (fundamentalClass k sY)) :
    ProjectionTauFormula k sY n := by
  intro j hj β
  set C := fieldChowSituation k
  set p := projectiveSpaceOver n Y ↘ Y
  set sP := p ≫ sY
  set G := chowGraded C sP
  set h := firstChernQ C sP (twistOver n Y 1)
  have hh : G.comp 0 h = 0 := isHom_firstChernQ C sP (twistOver n Y 1) 0 zero_ne_one
  set A := G.ev h (expNeg ^ j)
  set B := pullbackAQ C sP sY p rfl (ch C sY β)
  set T := pullbackAQ C sP sY p rfl (toddTangent k sY)
  set E := G.ev h toddSeries ^ (n + 1)
  have hA : A = ch C sP (twistClass Y n (-(j : ℤ))) := (ch_twistClass_neg k sY n j).symm
  have hB : B = ch C sP (VectorBundleKZero.pullback p β) := pullbackAQ_ch C sP sY p rfl β
  have hT' : T = toddClass C sP (VectorBundleKZero.pullback p (tangentClass k sY)) :=
    pullbackAQ_toddClass C sP sY p rfl (tangentClass k sY)
  have c1 : Commute A B := by
    rw [hA, hB]
    exact (Commute.all _ _).map (ch C sP)
  have c2 : Commute A T := by
    rw [hA, hT']
    exact (commute_toddClass_ch C sP _ _).symm
  have key : chK k sP (twistedPullback k sY n j β) * toddTangent k sP =
      pullbackAQ C sP sY p rfl (ch C sY β * toddTangent k sY) *
        G.ev h (expNeg ^ j * toddSeries ^ (n + 1)) := by
    rw [chK_eq_ch, twistedPullback, AddEquiv.symm_apply_apply, map_mul (ch C sP),
      ch_twistClass_neg, ← pullbackAQ_ch C sP sY p rfl, hT,
      map_mul (pullbackAQ C sP sY p rfl), G.ev_mul hh, G.ev_pow hh toddSeries (n + 1)]
    change A * B * (T * E) = B * T * (A * E)
    rw [c1.eq, mul_assoc, ← mul_assoc A T E, c2.eq, mul_assoc, ← mul_assoc B T]
  rw [tau_apply k sP, key, hI]
  split_ifs with hj0
  · subst hj0
    rw [pow_zero, show (1 : PowerSeries ℚ) = PowerSeries.exp ℚ ^ 0 from (pow_zero _).symm,
      coeff_exp_pow_mul_toddSeries_pow n 0, Nat.add_zero, Nat.choose_self, Nat.cast_one, one_smul,
      tau_apply, chK_eq_ch, AddEquiv.symm_apply_apply]
  · rw [coeff_expNeg_pow_mul_toddSeries_pow (Nat.one_le_iff_ne_zero.mpr hj0) hj, zero_smul]

/-- **`π_* τ(g_j(β))` from the Todd class of `ℙⁿ_Y`**: the formula of
`GRR.ProjectionTauFormula` holds as soon as `td(T_P) = π^* td(T_Y) · (h / (1 - e^{-h}))^{n+1}`. -/
theorem projectionTauFormula_of_toddTangent
    (hT : toddTangent k ((projectiveSpaceOver n Y ↘ Y) ≫ sY) =
      pullbackAQ (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY) sY
          (projectiveSpaceOver n Y ↘ Y) rfl (toddTangent k sY) *
        (chowGraded (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)).ev
          (firstChernQ (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
            (twistOver n Y 1)) toddSeries ^ (n + 1)) :
    ProjectionTauFormula k sY n :=
  projectionTauFormula_of k sY n hT (pushforward_cap_pullbackAQ_mul_ev k sY n)

end Final

section ProjectiveSpaceTangent

open CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjEulerSequence Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTrivialization
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf)

attribute [local instance] MvPolynomial.gradedAlgebra

section Biproduct

variable {T : Scheme.{u}}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the biproduct and cokernel in `T.Modules` is heavy
/-- The class of a finite direct sum of finite locally free modules is the sum of the classes. -/
theorem classOf_biproduct (n : ℕ) {ι : Type} [Fintype ι] (hn : Fintype.card ι = n)
    (f : ι → T.Modules)
    (hf : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (f i)) :
    VectorBundleKZero.classOf T (⨁ f) = ∑ i, VectorBundleKZero.classOf T (f i) := by
  classical
  induction n generalizing ι with
  | zero =>
    have : IsEmpty ι := Fintype.card_eq_zero_iff.1 hn
    rw [Finset.univ_eq_empty, Finset.sum_empty,
      VectorBundleKZero.classOf_eq_of_iso (isZero_biproduct_of_isEmpty f).isoZero
        (isFiniteLocallyFree_biproduct 0 hn f hf), VectorBundleKZero.classOf_zero]
  | succ n ih =>
    obtain ⟨i⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    have hS := shortExact_biproduct_ι f i
    have := hS.mono_f
    have := hS.epi_g
    have h₃ := isFiniteLocallyFree_biproduct n (ι := {j // j ≠ i})
      (by have := card_subtype_ne i; omega) (Subtype.restrict _ f) fun j ↦ hf j
    have h₃' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (cokernel (biproduct.ι f i)) :=
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso
        (cokernelBiproductιIso f i).symm (h := h₃)
    rw [VectorBundleKZero.classOf_shortExact _ _ (cokernel.condition _) (hf i)
        (isFiniteLocallyFree_biproduct (n + 1) hn f hf) h₃' hS.exact,
      VectorBundleKZero.classOf_eq_of_iso (cokernelBiproductιIso f i) h₃',
      ih (ι := {j // j ≠ i}) (by have := card_subtype_ne i; omega) (Subtype.restrict _ f)
        (fun j => hf j),
      Fintype.sum_eq_add_sum_subtype_ne _ i]
    rfl

end Biproduct

section IntegralModel

/-- The polynomial model `Proj ℤ[T₀, …, Tₙ]` of `ℙⁿ_ℤ`; it is `projectiveSpaceAtUniverse n`. -/
noncomputable abbrev projZ (n : ℕ) : Scheme.{u} :=
  AlgebraicGeometry.Proj (polyGrading (ULift.{u} ℤ) n)

/-- The twist `𝒪(d)` of the polynomial model, as a module on the scheme `projZ n`. -/
noncomputable def twistZ (n : ℕ) (d : ℤ) : (projZ.{u} n).Modules :=
  twistingSheaf (polyGrading (ULift.{u} ℤ) n) d

variable (n : ℕ)

theorem isFiniteLocallyFree_twistingSheaf (d : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (projZ.{u} n).ringCatSheaf) (twistingSheaf (polyGrading (ULift.{u} ℤ) n) d) := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible (projZ.{u} n).sheaf.obj
      (projZ.{u} n).ringCatSheaf.property (twistingSheaf (polyGrading (ULift.{u} ℤ) n) d) :=
    Stacks.ProjectiveSpace.isInvertibleModule_twistingSheaf_homogeneousSubmodule (ULift.{u} ℤ) n d
  have := isFiniteLocallyFreeOfRank_one_of_isInvertible (X := projZ.{u} n)
    (twistingSheaf (polyGrading (ULift.{u} ℤ) n) d)
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1

theorem isFiniteLocallyFree_twistMinusOneSum :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (projZ.{u} n).ringCatSheaf)
        (twistMinusOneSum (ULift.{u} ℤ) n : (projZ.{u} n).Modules) :=
  isFiniteLocallyFree_biproduct (T := projZ.{u} n) (n + 1) (Fintype.card_fin _)
    (twistMinusOneFamily (ULift.{u} ℤ) n) fun _ => isFiniteLocallyFree_twistingSheaf n (-1)

theorem isFiniteLocallyFree_projDifferentials :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (projZ.{u} n).ringCatSheaf)
        (projDifferentials (ULift.{u} ℤ) n : (projZ.{u} n).Modules) :=
  @isFiniteLocallyFree_X₁_of_shortExact (projZ.{u} n)
    (ShortComplex.mk (eulerFirstArrow (ULift.{u} ℤ) n) (eulerSurjection (ULift.{u} ℤ) n)
      (eulerFirstArrow_comp_eulerSurjection (ULift.{u} ℤ) n))
    (shortExact_eulerSequence (ULift.{u} ℤ) n) (isFiniteLocallyFree_twistMinusOneSum n)
    (AlgebraicGeometry.isFiniteLocallyFree_unit (projZ.{u} n))

/-- **The Euler sequence in `K₀(Vect ℙⁿ_ℤ)`**: `[Ω] = (n + 1) [𝒪(-1)] - 1`. -/
theorem classOf_projDifferentials :
    VectorBundleKZero.classOf (projZ.{u} n)
        (Scheme.Hom.relativeDifferentials (projToSpecCoeff (ULift.{u} ℤ) n)) =
      (n + 1) • VectorBundleKZero.classOf (projZ.{u} n) (twistZ n (-1)) - 1 := by
  have hS := shortExact_eulerSequence (ULift.{u} ℤ) n
  have h := @VectorBundleKZero.classOf_shortExact (projZ.{u} n) _ _ _
    (eulerFirstArrow (ULift.{u} ℤ) n) (eulerSurjection (ULift.{u} ℤ) n) hS.mono_f hS.epi_g
    (eulerFirstArrow_comp_eulerSurjection (ULift.{u} ℤ) n)
    (isFiniteLocallyFree_projDifferentials n) (isFiniteLocallyFree_twistMinusOneSum n)
    (AlgebraicGeometry.isFiniteLocallyFree_unit (projZ.{u} n)) hS.exact
  have hsum := classOf_biproduct (T := projZ.{u} n) (n + 1) (Fintype.card_fin _)
    (twistMinusOneFamily (ULift.{u} ℤ) n) fun _ => isFiniteLocallyFree_twistingSheaf n (-1)
  have hconst : ∑ i, VectorBundleKZero.classOf (projZ.{u} n)
        (twistMinusOneFamily (ULift.{u} ℤ) n i) =
      (n + 1) • VectorBundleKZero.classOf (projZ.{u} n)
        (twistingSheaf (polyGrading (ULift.{u} ℤ) n) (-1)) :=
    calc ∑ i, VectorBundleKZero.classOf (projZ.{u} n) (twistMinusOneFamily (ULift.{u} ℤ) n i)
        = ∑ _i : Fin (n + 1), VectorBundleKZero.classOf (projZ.{u} n)
            (twistingSheaf (polyGrading (ULift.{u} ℤ) n) (-1)) := rfl
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [hconst] at hsum
  change VectorBundleKZero.classOf (projZ.{u} n) (twistMinusOneSum (ULift.{u} ℤ) n) = _ at hsum
  exact eq_sub_of_add_eq (h.symm.trans hsum)

end IntegralModel

section BaseChange

/-- `f^* 1 = 1` in `K₀(Vect)`: `f^* 𝒪_Y ≅ 𝒪_X`. -/
theorem vectorBundleKZero_pullback_one {X Y : Scheme.{u}} (f : X ⟶ Y) :
    VectorBundleKZero.pullback f 1 = 1 :=
  (@VectorBundleKZero.pullback_classOf _ _ f (Scheme.unitModule Y)
    (AlgebraicGeometry.isFiniteLocallyFree_unit Y)).trans
    (VectorBundleKZero.classOf_eq_of_iso (Scheme.Modules.pullbackUnitIso f)
      (isFiniteLocallyFree_pullbackObj (hF := AlgebraicGeometry.isFiniteLocallyFree_unit Y)
        (Scheme.unitModule Y) f))

variable (n : ℕ) (Y : Scheme.{u})

/-- The projection `ℙⁿ_Y ⟶ ℙⁿ_ℤ`, to the polynomial model. -/
noncomputable abbrev toProjZ : projectiveSpaceOver n Y ⟶ projZ.{u} n :=
  projectiveSpaceOver.toIntegralAtUniverse n Y

/-- `ℙⁿ_Y` is the base change of `ℙⁿ_ℤ ⟶ Spec ℤ` along `Y ⟶ Spec ℤ`. -/
theorem isPullback_toProjZ :
    IsPullback (toProjZ n Y) (projectiveSpaceOver n Y ↘ Y) (projToSpecCoeff (ULift.{u} ℤ) n)
      (specULiftZIsTerminal.from Y) := by
  have h := (IsPullback.of_hasPullback (terminal.from Y)
    (terminal.from (projectiveSpaceAtUniverse.{u} n))).flip
  exact h.of_iso (Iso.refl _) (Iso.refl (projZ.{u} n)) (Iso.refl _)
    (terminalIsTerminal.uniqueUpToIso specULiftZIsTerminal)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    (specULiftZIsTerminal.hom_ext _ _) (specULiftZIsTerminal.hom_ext _ _)

/-- **`[Ω_{ℙⁿ_Y/Y}] = (n + 1) [𝒪(-1)] - 1`**, by base change from the Euler sequence on `ℙⁿ_ℤ`. -/
theorem classOf_relativeDifferentials_projectiveSpaceOver :
    VectorBundleKZero.classOf (projectiveSpaceOver n Y)
        (Scheme.Hom.relativeDifferentials (projectiveSpaceOver n Y ↘ Y)) =
      (n + 1) • twistClass Y n (-1) - 1 := by
  have hiso := Scheme.Hom.isIso_relativeDifferentialsMap_of_isPullback _ _ _ _
    (isPullback_toProjZ n Y)
  have := isFiniteLocallyFree_projDifferentials.{u} n
  have hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback (toProjZ n Y)).obj
        (Scheme.Hom.relativeDifferentials (projToSpecCoeff (ULift.{u} ℤ) n))) :=
    isFiniteLocallyFree_pullbackObj _ _
  rw [← VectorBundleKZero.classOf_eq_of_iso (asIso (Scheme.Hom.relativeDifferentialsMap
      (toProjZ n Y) (projToSpecCoeff (ULift.{u} ℤ) n) (projectiveSpaceOver n Y ↘ Y)
      (specULiftZIsTerminal.from Y) (isPullback_toProjZ n Y).w)) hF,
    ← VectorBundleKZero.pullback_classOf]
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (twistZ.{u} n (-1)) :=
    isFiniteLocallyFree_twistingSheaf.{u} n (-1)
  rw [classOf_projDifferentials, map_sub, map_nsmul, VectorBundleKZero.pullback_classOf,
    vectorBundleKZero_pullback_one]
  rfl

end BaseChange

section Cotangent

variable (k : Type u) [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsSmoothFT k sY]
  (n : ℕ)

/-- **The relative cotangent sequence of `ℙⁿ_Y ⟶ Y ⟶ Spec k` in `K₀(Vect)`**:
`[Ω_{P/k}] = π^*[Ω_{Y/k}] + [Ω_{P/Y}]`, the projection being smooth. -/
theorem classOf_relativeDifferentials_comp :
    VectorBundleKZero.classOf (projectiveSpaceOver n Y)
        (Scheme.Hom.relativeDifferentials ((projectiveSpaceOver n Y ↘ Y) ≫ sY)) =
      VectorBundleKZero.pullback (projectiveSpaceOver n Y ↘ Y)
          (VectorBundleKZero.classOf Y (Scheme.Hom.relativeDifferentials sY)) +
        VectorBundleKZero.classOf (projectiveSpaceOver n Y)
          (Scheme.Hom.relativeDifferentials (projectiveSpaceOver n Y ↘ Y)) := by
  have hfs : FormallySmooth (projectiveSpaceOver n Y ↘ Y) :=
    Stacks.Smooth.formallySmoothScheme_of_smooth _
  obtain ⟨hw, hS⟩ := Scheme.Hom.toRelativeDifferentials_shortExact _ sY hfs
  have := hS.mono_f
  have := hS.epi_g
  have hY := Scheme.Hom.isFiniteLocallyFree_relativeDifferentials sY
  rw [VectorBundleKZero.classOf_shortExact _ _ hw
      (isFiniteLocallyFree_pullbackObj (Scheme.Hom.relativeDifferentials sY) _)
      (Scheme.Hom.isFiniteLocallyFree_relativeDifferentials _)
      (Scheme.Hom.isFiniteLocallyFree_relativeDifferentials _) hS.exact,
    VectorBundleKZero.pullback_classOf]

end Cotangent

namespace GradedComplete

variable {R : Type*} [Ring R] [Module ℚ R] (G : GRR.GradedComplete R)

/-- A rescaling fixing degree zero fixes `1`. -/
theorem weight_one_of {w : ℕ → ℚ} (hw : w 0 = 1) : G.weight w 1 = 1 := by
  refine G.ext _ _ fun n => ?_
  rw [G.comp_weight]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [hw, one_smul]
  · rw [G.comp_one n hn, smul_zero]

/-- `td(1) = 1`: the Todd weights vanish in degree zero, where `1` lives. -/
theorem toddOf_one : G.toddOf 1 = 1 := by
  have h0 : G.weight toddWeight 1 = 0 := by
    refine G.ext _ _ fun n => ?_
    rw [map_zero]
    rcases eq_or_ne n 0 with rfl | hn
    · exact G.comp_zero_weight_toddWeight 1
    · rw [G.comp_weight, G.comp_one n hn, smul_zero]
  rw [toddOf, h0, gexp_zero]

/-- The sign rescaling carries `e^{-h}` to `e^h`, for `h` homogeneous of degree one. -/
theorem weight_sign_ev_expNeg {h : R} (hh : G.IsHom 1 h) :
    G.weight (fun n ↦ (-1 : ℚ) ^ n) (G.ev h expNeg) = G.ev h (PowerSeries.exp ℚ) := by
  refine G.ext _ _ fun n => ?_
  rw [G.comp_weight, G.comp_ev_of_isHom hh, G.comp_ev_of_isHom hh, smul_smul]
  congr 1
  rw [coeff_expNeg, PowerSeries.coeff_exp, Algebra.algebraMap_self, RingHom.id_apply,
    ← mul_div_assoc, ← mul_pow]
  norm_num

end GradedComplete

section Todd

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

theorem toddClass_one : toddClass C sX 1 = 1 := by
  rw [toddClass, map_one, GradedComplete.toddOf_one]

theorem toddClass_neg_one : toddClass C sX (-1) = 1 := by
  have h := toddClass_mul_toddClass_neg C sX 1
  rwa [toddClass_one, one_mul] at h

theorem toddClass_nsmul (a : VectorBundleKZero X) (m : ℕ) :
    toddClass C sX (m • a) = toddClass C sX a ^ m := by
  induction m with
  | zero => rw [zero_smul, toddClass_zero, pow_zero]
  | succ m ih => rw [succ_nsmul, toddClass_add, ih, pow_succ]

end Todd

section TangentProjective

variable (k : Type u) [Field k] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsSmoothFT k sY]
  (n : ℕ)

/-- **`ch [T_P] = ch (π^*[T_Y] + (n + 1) [𝒪(1)] - 1)`** for `P = ℙⁿ_Y`. -/
theorem ch_tangentClass_projectiveSpaceOver :
    ch (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
        (tangentClass k ((projectiveSpaceOver n Y ↘ Y) ≫ sY)) =
      ch (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
        (VectorBundleKZero.pullback (projectiveSpaceOver n Y ↘ Y) (tangentClass k sY) +
          ((n + 1) • twistClass Y n 1 - 1)) := by
  set C := fieldChowSituation k
  set p := projectiveSpaceOver n Y ↘ Y
  set sP := p ≫ sY
  set G := chowGraded C sP
  have hh : G.IsHom 1 (firstChernQ C sP (twistOver n Y 1)) :=
    isHom_firstChernQ C sP (twistOver n Y 1)
  have := Scheme.Hom.isFiniteLocallyFree_relativeDifferentials sP
  have := Scheme.Hom.isFiniteLocallyFree_relativeDifferentials sY
  let W : RationalTotalChowClass C sP →+ RationalTotalChowClass C sP :=
    { toFun := G.weight (fun n ↦ (-1 : ℚ) ^ n)
      map_zero' := G.weight_zero _
      map_add' := G.weight_add _ }
  have hW : ∀ a, G.weight (fun n ↦ (-1 : ℚ) ^ n) a = W a := fun _ => rfl
  have hY : W (ch C sP (VectorBundleKZero.pullback p
        (VectorBundleKZero.classOf Y (Scheme.Hom.relativeDifferentials sY)))) =
      ch C sP (VectorBundleKZero.pullback p (tangentClass k sY)) := by
    rw [← hW, ← pullbackAQ_ch C sP sY p rfl, ← (isGradedHom_pullbackAQ C sP sY p rfl).map_weight,
      ← ch_classOf_dualSheaf, pullbackAQ_ch]
    rfl
  have htw : W (ch C sP (twistClass Y n (-1))) = ch C sP (twistClass Y n 1) := by
    rw [← hW, ch_twistClass_neg_one, G.weight_sign_ev_expNeg hh]
    exact (ch_classOf_invertible C sP (twistOver n Y 1)).symm
  have hone : W 1 = 1 := G.weight_one_of (by norm_num)
  calc ch C sP (tangentClass k sP)
      = W (ch C sP (VectorBundleKZero.classOf _ (Scheme.Hom.relativeDifferentials sP))) :=
        ch_classOf_dualSheaf C sP _
    _ = W (ch C sP (VectorBundleKZero.pullback p
          (VectorBundleKZero.classOf Y (Scheme.Hom.relativeDifferentials sY)) +
            ((n + 1) • twistClass Y n (-1) - 1))) := by
        rw [classOf_relativeDifferentials_comp k sY n,
          classOf_relativeDifferentials_projectiveSpaceOver n Y]
    _ = ch C sP (VectorBundleKZero.pullback p (tangentClass k sY)) +
          ((n + 1) • ch C sP (twistClass Y n 1) - 1) := by
        rw [map_add (ch C sP), map_sub (ch C sP), map_nsmul (ch C sP), map_one (ch C sP),
          map_add W, map_sub W, map_nsmul W, hY, htw, hone]
    _ = _ := by
        rw [map_add (ch C sP), map_sub (ch C sP), map_nsmul (ch C sP), map_one (ch C sP)]

/-- **The Todd class of `ℙⁿ_Y`**: `td(T_P) = π^* td(T_Y) · (h / (1 - e^{-h}))^{n+1}`,
`h = c₁(𝒪(1))`, from the relative cotangent sequence and the Euler sequence. -/
theorem toddTangent_projectiveSpaceOver :
    toddTangent k ((projectiveSpaceOver n Y ↘ Y) ≫ sY) =
      pullbackAQ (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY) sY
          (projectiveSpaceOver n Y ↘ Y) rfl (toddTangent k sY) *
        (chowGraded (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)).ev
          (firstChernQ (fieldChowSituation k) ((projectiveSpaceOver n Y ↘ Y) ≫ sY)
            (twistOver n Y 1)) toddSeries ^ (n + 1) := by
  set C := fieldChowSituation k
  set p := projectiveSpaceOver n Y ↘ Y
  set sP := p ≫ sY
  have key : toddTangent k sP = toddClass C sP
      (VectorBundleKZero.pullback p (tangentClass k sY) + ((n + 1) • twistClass Y n 1 - 1)) :=
    congrArg (chowGraded C sP).toddOf (ch_tangentClass_projectiveSpaceOver k sY n)
  rw [key, sub_eq_add_neg, toddClass_add, toddClass_add, toddClass_nsmul, toddClass_neg_one,
    mul_one, ← pullbackAQ_toddClass C sP sY p rfl, twistClass,
    toddClass_classOf_invertible]
  rfl

/-- **Riemann–Roch on the twisted classes of `ℙⁿ_Y`**: `π_* τ([𝒪(-j)] · π^* β) = τ_Y(β)` for
`j = 0` and `0` for `1 ≤ j ≤ n`. -/
theorem projectionTauFormula : ProjectionTauFormula k sY n :=
  projectionTauFormula_of_toddTangent k sY n (toddTangent_projectiveSpaceOver k sY n)

end TangentProjective

end ProjectiveSpaceTangent

end GRR
