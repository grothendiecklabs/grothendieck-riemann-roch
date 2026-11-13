import Mathlib
import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.ExteriorPowerTotalChern
import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.ChernRootsTotal
import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.SplittingProjective
import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.DualTotalChern
import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.SecondAdamsChernScaling
import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.ChernRelations
import StacksFrontier.AlgebraicGeometry.WeilCohomology.LambdaOperations
import GRR.ClosedImmersion
import GRR.Pullback
import GRR.ToddClass

/-!
# The Koszul identity for Chern characters

For `Q` finite locally free of constant rank `r` on `X`, with `λ_{-1}(Q^∨) = ∑_p (-1)^p [⋀^p Q^∨]`,

  `ch(λ_{-1}(Q^∨)) = c_r(Q) · td(Q)⁻¹`   in `∏_p A^p(X) ⊗ ℚ`  (`GRR.ch_koszul`).

The proof is by the splitting principle: for `V` with a filtration by invertible modules,
`λ_{-1}(V) = ∏ (1 - [L_i])` in `K₀(Vect X)`, and the rank-one case is `td(e^h) (1 - e^{-h}) = h`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow Finset
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf)

universe u

namespace GRR

/-! ### Exterior powers along an invertible submodule, in `K₀(Vect X)` -/

section KTheory

variable {X : Scheme.{u}}

/-- `λ_{-1}(E) = ∑_{p ≤ r} (-1)^p [⋀^p E]` in `K₀(Vect X)`. -/
noncomputable def lambdaNegOne (E : X.Modules) (r : ℕ) : VectorBundleKZero X :=
  ∑ p ∈ range (r + 1), (-1 : ℤ) ^ p •
    VectorBundleKZero.classOf X (Scheme.Modules.exteriorPower E (p : ℤ))

/-- `[⋀^n E] = 0` for `n` above the rank of `E`. -/
theorem classOf_exteriorPower_eq_zero_of_lt (E : X.Modules) (r n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (h : r < n) :
    VectorBundleKZero.classOf X (Scheme.Modules.exteriorPower E (n : ℤ)) = 0 := by
  have h0 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.exteriorPower E (n : ℤ)) 0 := by
    have := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower E r n
    rwa [Nat.choose_eq_zero_of_lt h] at this
  have hz := Stacks.WeilCohomology.isZero_of_isFiniteLocallyFreeOfRank_zero _ h0
  rw [VectorBundleKZero.classOf_eq_of_iso hz.isoZero
    (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 0),
    VectorBundleKZero.classOf_zero]

/-- **Exterior powers of an extension by a module of rank one**: for `0 → N → V → Q → 0` with `N`
of rank one, `[⋀^{p+1} V] = [N] [⋀^p Q] + [⋀^{p+1} Q]`. -/
theorem classOf_exteriorPower_succ_of_rankOne {N V Q : X.Modules} (f : N ⟶ V) (g : V ⟶ Q)
    (w : f ≫ g = 0) (hS : (ShortComplex.mk f g w).ShortExact)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N 1] (m : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Q m] (p : ℕ) :
    VectorBundleKZero.classOf X (Scheme.Modules.exteriorPower V ((p + 1 : ℕ) : ℤ)) =
      VectorBundleKZero.classOf X N *
          VectorBundleKZero.classOf X (Scheme.Modules.exteriorPower Q (p : ℤ)) +
        VectorBundleKZero.classOf X (Scheme.Modules.exteriorPower Q ((p + 1 : ℕ) : ℤ)) := by
  have hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree N 1
  have hQ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} Q :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree Q m
  have hV : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} V :=
    GenuineChern.isFiniteLocallyFree_of_shortExact _ hS hN hQ
  have hΛ : ∀ (M : X.Modules) (n : ℕ),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M →
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
          (Scheme.Modules.exteriorPower M (n : ℤ)) :=
    fun M n hM ↦ Scheme.Modules.isFiniteLocallyFree_exteriorPower M n hM
  rcases p with _ | k
  · have : Mono f := hS.mono_f
    have : Epi g := hS.epi_g
    have eV : VectorBundleKZero.classOf X (Scheme.Modules.exteriorPower V ((0 + 1 : ℕ) : ℤ)) =
        VectorBundleKZero.classOf X V :=
      VectorBundleKZero.classOf_eq_of_iso
        (_root_.SheafOfModules.algebras _ V).exteriorPowerOneIso (hΛ V 1 hV)
    have eQ : VectorBundleKZero.classOf X (Scheme.Modules.exteriorPower Q ((0 + 1 : ℕ) : ℤ)) =
        VectorBundleKZero.classOf X Q :=
      VectorBundleKZero.classOf_eq_of_iso
        (_root_.SheafOfModules.algebras _ Q).exteriorPowerOneIso (hΛ Q 1 hQ)
    rw [eV, eQ, Nat.cast_zero, VectorBundleKZero.classOf_exteriorPower_zero, mul_one]
    exact VectorBundleKZero.classOf_shortExact f g w hN hV hQ hS.exact
  · obtain ⟨φ, w', hS'⟩ := Scheme.Modules.shortExact_exteriorPower_of_rankOne f g w hS m k
    have : Mono φ := hS'.mono_f
    have : Epi (Scheme.Modules.exteriorPowerMap g ((1 + (k + 1) : ℕ) : ℤ)) := hS'.epi_g
    have h1N : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (Scheme.Modules.exteriorPower N 1) := hΛ N 1 hN
    have hT := @AlgebraicGeometry.isFiniteLocallyFree_tensorObj _ _ _ h1N (hΛ Q (k + 1) hQ)
    have key := VectorBundleKZero.classOf_shortExact φ _ w' hT (hΛ V _ hV) (hΛ Q _ hQ) hS'.exact
    have e1N : VectorBundleKZero.classOf X (Scheme.Modules.exteriorPower N 1) =
        VectorBundleKZero.classOf X N :=
      VectorBundleKZero.classOf_eq_of_iso
        (_root_.SheafOfModules.algebras _ N).exteriorPowerOneIso h1N
    have e2 : VectorBundleKZero.classOf X (Scheme.Modules.tensorObj
          (Scheme.Modules.exteriorPower N 1) (Scheme.Modules.exteriorPower Q ((k + 1 : ℕ) : ℤ))) =
        VectorBundleKZero.classOf X (Scheme.Modules.exteriorPower N 1) *
          VectorBundleKZero.classOf X (Scheme.Modules.exteriorPower Q ((k + 1 : ℕ) : ℤ)) :=
      (VectorBundleKZero.classOf_mul _ _ h1N (hΛ Q (k + 1) hQ)).symm
    rw [e2, e1N, show 1 + (k + 1) = k + 1 + 1 by omega] at key
    exact key

/-- The alternating sum of a sequence `a` with `a_{p+1} = n b_p + b_{p+1}` and `a_0 = b_0`. -/
theorem sum_neg_one_pow_mul_eq {R : Type*} [CommRing R] (a b : ℕ → R) (n : R)
    (ha0 : a 0 = b 0) (ha : ∀ p, a (p + 1) = n * b p + b (p + 1)) (M : ℕ) :
    ∑ p ∈ range (M + 1), (-1 : R) ^ p * a p =
      (1 - n) * ∑ p ∈ range M, (-1 : R) ^ p * b p + (-1) ^ M * b M := by
  induction M with
  | zero => simp [ha0]
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, ha, Finset.sum_range_succ]
    ring

/-- **`λ_{-1}` of an extension by a module of rank one**: for `0 → N → V → Q → 0` with `N` of
rank one and `Q` of rank `m`, `λ_{-1}(V) = (1 - [N]) λ_{-1}(Q)`. -/
theorem lambdaNegOne_of_rankOne {N V Q : X.Modules} (f : N ⟶ V) (g : V ⟶ Q) (w : f ≫ g = 0)
    (hS : (ShortComplex.mk f g w).ShortExact)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N 1] (m : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Q m] :
    lambdaNegOne V (m + 1) = (1 - VectorBundleKZero.classOf X N) * lambdaNegOne Q m := by
  have h := sum_neg_one_pow_mul_eq
    (fun p ↦ VectorBundleKZero.classOf X (Scheme.Modules.exteriorPower V (p : ℤ)))
    (fun p ↦ VectorBundleKZero.classOf X (Scheme.Modules.exteriorPower Q (p : ℤ)))
    (VectorBundleKZero.classOf X N)
    (by simp only [Nat.cast_zero, VectorBundleKZero.classOf_exteriorPower_zero])
    (classOf_exteriorPower_succ_of_rankOne f g w hS m) (m + 1)
  rw [classOf_exteriorPower_eq_zero_of_lt Q m (m + 1) (Nat.lt_succ_self m), mul_zero,
    add_zero] at h
  simp only [lambdaNegOne, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  exact h

/-- **`λ_{-1}` of a filtered module**: if `V` has a filtration with successive quotients `L_i`
of rank one, `λ_{-1}(V) = ∏_i (1 - [L_i])`. -/
theorem lambdaNegOne_of_hasQuotients : ∀ (r : ℕ) (V : X.Modules) (L : Fin r → X.Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (L i) 1],
    HasQuotients X r V L →
      lambdaNegOne V r = ∏ i, (1 - VectorBundleKZero.classOf X (L i)) := by
  intro r
  induction r with
  | zero =>
    intro V L _ _
    rw [lambdaNegOne, Finset.sum_range_one, pow_zero, one_smul, Nat.cast_zero,
      VectorBundleKZero.classOf_exteriorPower_zero, Fin.prod_univ_zero]
  | succ r ih =>
    intro V L _ h
    obtain ⟨N, eN, Q, f, g, w, hS, hQ⟩ := exists_bottom_of_hasQuotients r V L h
    have := isFiniteLocallyFreeOfRank_of_hasQuotients r Q _ hQ
    have hN1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N 1 :=
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso eN.symm inferInstance
    have hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N :=
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree N 1
    rw [lambdaNegOne_of_rankOne f g w hS r, ih Q _ hQ, Fin.prod_univ_castSucc,
      VectorBundleKZero.classOf_eq_of_iso eN hN]
    exact mul_comm _ _

/-- Pullback of `λ_{-1}`: `f^* λ_{-1}(E) = λ_{-1}(f^* E)`. -/
theorem pullback_lambdaNegOne {Y : Scheme.{u}} (f : Y ⟶ X) (E : X.Modules)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (r : ℕ) :
    VectorBundleKZero.pullback f (lambdaNegOne E r) =
      lambdaNegOne ((Scheme.Modules.pullback f).obj E) r := by
  rw [lambdaNegOne, lambdaNegOne, map_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have hΛ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Scheme.Modules.exteriorPower E (p : ℤ)) :=
    Scheme.Modules.isFiniteLocallyFree_exteriorPower E p hE
  rw [map_zsmul, VectorBundleKZero.pullback_classOf,
    VectorBundleKZero.classOf_eq_of_iso (VectorBundleKZero.pullbackExteriorPowerIso f E p)
      (isFiniteLocallyFree_pullbackObj _ f)]

/-- Pullback of the class of a dual: `f^* [E^∨] = [(f^* E)^∨]`. -/
theorem pullback_classOf_dualSheaf {Y : Scheme.{u}} (f : Y ⟶ X) (E : X.Modules)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    VectorBundleKZero.pullback f (VectorBundleKZero.classOf X (dualSheaf E)) =
      VectorBundleKZero.classOf Y (dualSheaf ((Scheme.Modules.pullback f).obj E)) := by
  have hd : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback f).obj (dualSheaf E)) := isFiniteLocallyFree_pullbackObj _ f
  rw [VectorBundleKZero.pullback_classOf]
  exact VectorBundleKZero.classOf_eq_of_iso (VectorBundleKZero.pullbackDualSheafIso f E
    (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree E)) hd

end KTheory

/-! ### Graded helpers -/

namespace GradedComplete

variable {R : Type*} [Ring R] [Module ℚ R] (G : GRR.GradedComplete R)

/-- Degreewise rescalings compose by multiplying the weights. -/
theorem weight_weight (w w' : ℕ → ℚ) (a : R) :
    G.weight w (G.weight w' a) = G.weight (fun n ↦ w n * w' n) a :=
  G.ext _ _ fun n ↦ by rw [comp_weight, comp_weight, comp_weight, smul_smul]

/-- The sign rescaling `(-1)^n` is an involution. -/
theorem weight_sign_sign (a : R) :
    G.weight (fun n ↦ (-1 : ℚ) ^ n) (G.weight (fun n ↦ (-1 : ℚ) ^ n) a) = a := by
  rw [weight_weight]
  conv_rhs => rw [← G.weight_one a]
  congr 1
  funext n
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

/-- For `h` homogeneous of degree one, `e^{-x}` evaluated at `-h` is `e^x` evaluated at `h`. -/
theorem ev_neg_expNeg {h : R} (hh : G.IsHom 1 h) :
    G.ev (-h) expNeg = G.ev h (PowerSeries.exp ℚ) := by
  have hh' : G.IsHom 1 (-h) := fun p hp ↦ by rw [map_neg, hh p hp, neg_zero]
  refine G.ext _ _ fun n ↦ ?_
  rw [G.comp_ev_of_isHom hh', G.comp_ev_of_isHom hh, neg_pow, coeff_expNeg,
    PowerSeries.coeff_exp, Algebra.algebraMap_self_apply]
  rcases Nat.even_or_odd n with hn | hn
  · rw [hn.neg_one_pow, hn.neg_one_pow, one_mul]
  · rw [hn.neg_one_pow, hn.neg_one_pow, neg_one_mul, map_neg, smul_neg, neg_div, neg_smul,
      neg_neg]

end GradedComplete

/-! ### Chern characters and Todd classes of duals -/

section Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- The Todd class only depends on the Chern character. -/
theorem toddClass_eq_of_ch_eq {a b : VectorBundleKZero X} (h : ch C sX a = ch C sX b) :
    toddClass C sX a = toddClass C sX b := by
  simp only [toddClass, h]

/-- `ch(E^∨∨) = ch(E)`. -/
theorem ch_classOf_dualSheaf_dualSheaf (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    ch C sX (VectorBundleKZero.classOf X (dualSheaf (dualSheaf E))) =
      ch C sX (VectorBundleKZero.classOf X E) := by
  rw [ch_classOf_dualSheaf, ch_classOf_dualSheaf, GradedComplete.weight_sign_sign]

/-- `td(E^∨∨) = td(E)`. -/
theorem toddClass_classOf_dualSheaf_dualSheaf (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    toddClass C sX (VectorBundleKZero.classOf X (dualSheaf (dualSheaf E))) =
      toddClass C sX (VectorBundleKZero.classOf X E) :=
  toddClass_eq_of_ch_eq C sX (ch_classOf_dualSheaf_dualSheaf C sX E)

/-- **The Todd class of the dual is multiplicative on short exact sequences**:
`td(V^∨) = td(N^∨) td(Q^∨)` for `0 → N → V → Q → 0`. -/
theorem toddClass_classOf_dualSheaf_of_shortExact {N V Q : X.Modules} (f : N ⟶ V) (g : V ⟶ Q)
    (w : f ≫ g = 0) (hS : (ShortComplex.mk f g w).ShortExact)
    [hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
    [hQ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} Q] :
    toddClass C sX (VectorBundleKZero.classOf X (dualSheaf V)) =
      toddClass C sX (VectorBundleKZero.classOf X (dualSheaf N)) *
        toddClass C sX (VectorBundleKZero.classOf X (dualSheaf Q)) := by
  have hV : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} V :=
    GenuineChern.isFiniteLocallyFree_of_shortExact _ hS hN hQ
  have : Mono f := hS.mono_f
  have : Epi g := hS.epi_g
  rw [← toddClass_add]
  refine toddClass_eq_of_ch_eq C sX ?_
  rw [map_add, ch_classOf_dualSheaf, ch_classOf_dualSheaf, ch_classOf_dualSheaf,
    ← GradedComplete.weight_add, ← map_add,
    ← VectorBundleKZero.classOf_shortExact f g w hN hV hQ hS.exact]

/-- **The rank-one Koszul identity**: `ch(1 - [L]) · td(L^∨) = -c₁(L)` for an invertible `L`. -/
theorem ch_one_sub_mul_toddClass_dualSheaf (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    ch C sX (1 - VectorBundleKZero.classOf X L) *
        toddClass C sX (VectorBundleKZero.classOf X (dualSheaf L)) =
      -firstChernQ C sX L := by
  have hy := isHom_firstChernQ C sX L
  have hy0 : (chowGraded C sX).comp 0 (-firstChernQ C sX L) = 0 := by
    rw [map_neg, hy 0 zero_ne_one, neg_zero]
  have hdual : firstChernQ C sX (dualSheaf L) = -firstChernQ C sX L := by
    simp only [firstChernQ, TotalChowClass.firstChernTotal_dualSheaf, map_neg]
  rw [← (commute_toddClass_ch C sX _ _).eq, toddClass_classOf_invertible, hdual, map_sub, map_one,
    ch_classOf_invertible, ← GradedComplete.ev_neg_expNeg _ hy]
  exact (chowGraded C sX).ev_toddSeries_mul_one_sub_ev_expNeg hy0

/-- `c_0 = 1`. -/
theorem homComponent_zero_one :
    TotalChowClass.homComponent 0 (1 : TotalChowClass C sX) = 1 := by
  refine TotalChowClass.ext fun p ↦ ?_
  rw [TotalChowClass.homComponent_apply]
  split_ifs with hp
  · rw [hp]
  · rw [TotalChowClass.one_apply_of_ne hp]

/-- **The top Chern class of an extension by an invertible module**: for `0 → N → V → Q → 0`
with `N` invertible and `Q` of rank `r`, `c_{r+1}(V) = c₁(N) c_r(Q)`. -/
theorem homComponent_totalChern_of_shortExact {N V Q : X.Modules} (f : N ⟶ V) (g : V ⟶ Q)
    (w : f ≫ g = 0) (hS : (ShortComplex.mk f g w).ShortExact)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N] (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Q r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} V (r + 1)] :
    TotalChowClass.homComponent (r + 1) (totalChern C sX V (r + 1)) =
      TotalChowClass.firstChernTotal C sX N *
        TotalChowClass.homComponent r (totalChern C sX Q r) := by
  have := isFiniteLocallyFreeOfRank_one_of_isInvertible N
  have hV' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} V (1 + r) :=
    add_comm r 1 ▸ ‹_›
  have hW : totalChern C sX V (1 + r) = totalChern C sX N 1 * totalChern C sX Q r :=
    congrArg Subtype.val (chernTotal_shortExact C sX f g w hS 1 r)
  have hV : totalChern C sX V (r + 1) = totalChern C sX V (1 + r) :=
    totalChern_congr C sX (Iso.refl V) (by omega)
  have h0 : TotalChowClass.homComponent (r + 1) (totalChern C sX Q r) = 0 := by
    refine TotalChowClass.ext fun p ↦ ?_
    rw [TotalChowClass.homComponent_apply]
    split_ifs with hp
    · subst hp
      exact totalChern_apply_of_lt C sX Q r (by omega)
    · rfl
  rw [hV, hW, totalChern_eq_one_add_firstChernTotal, add_mul, one_mul, map_add,
    TotalChowClass.homComponent_succ_mul_of_isHomogeneous_one
      (TotalChowClass.isHomogeneous_firstChernTotal C sX N), h0, zero_add]

/-- **The Koszul identity, dual form, for a filtered module**: if `V` has a filtration with
successive quotients of rank one, `ch(λ_{-1} V) · td(V^∨) = (-1)^r c_r(V)`. -/
theorem ch_lambdaNegOne_mul_toddClass_of_hasQuotients : ∀ (r : ℕ) (V : X.Modules)
    (L : Fin r → X.Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (L i) 1]
    (h : HasQuotients X r V L),
    letI := isFiniteLocallyFreeOfRank_of_hasQuotients r V L h
    ch C sX (lambdaNegOne V r) * toddClass C sX (VectorBundleKZero.classOf X (dualSheaf V)) =
      (-1 : ℤ) ^ r • RationalTotalChowClass.ofTotalChowClass
        (TotalChowClass.homComponent r (totalChern C sX V r)) := by
  intro r
  induction r with
  | zero =>
    intro V L _ h
    have := isFiniteLocallyFreeOfRank_of_hasQuotients 0 V L h
    have hV : IsZero V := h
    have hVF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} V :=
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree V 0
    have hcl : VectorBundleKZero.classOf X V = 0 := by
      rw [VectorBundleKZero.classOf_eq_of_iso hV.isoZero hVF, VectorBundleKZero.classOf_zero]
    have htd : toddClass C sX (VectorBundleKZero.classOf X (dualSheaf V)) = 1 := by
      rw [← toddClass_zero C sX]
      refine toddClass_eq_of_ch_eq C sX ?_
      rw [ch_classOf_dualSheaf, hcl, map_zero, GradedComplete.weight_zero]
    have hl : lambdaNegOne V 0 = 1 := by
      rw [lambdaNegOne, Finset.sum_range_one, pow_zero, one_smul, Nat.cast_zero,
        VectorBundleKZero.classOf_exteriorPower_zero]
    rw [hl, map_one, one_mul, htd, totalChern_of_rank_zero, homComponent_zero_one, map_one,
      pow_zero, one_smul]
  | succ r ih =>
    intro V L _ h
    obtain ⟨N, eN, Q, f, g, w, hS, hQ⟩ := exists_bottom_of_hasQuotients r V L h
    have hQr := isFiniteLocallyFreeOfRank_of_hasQuotients r Q _ hQ
    have hN1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N 1 :=
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso eN.symm inferInstance
    have hNi : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
        X.ringCatSheaf.property N :=
      Stacks.ModuleDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one X N hN1
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N :=
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree N 1
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} Q :=
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree Q r
    have := isFiniteLocallyFreeOfRank_of_hasQuotients (r + 1) V L h
    have IH := ih Q (fun i ↦ L i.castSucc) hQ
    have hc : Commute (ch C sX (lambdaNegOne Q r))
        (toddClass C sX (VectorBundleKZero.classOf X (dualSheaf N))) :=
      (commute_toddClass_ch C sX _ _).symm
    rw [lambdaNegOne_of_rankOne f g w hS r, map_mul,
      toddClass_classOf_dualSheaf_of_shortExact C sX f g w hS,
      homComponent_totalChern_of_shortExact C sX f g w hS r]
    calc ch C sX (1 - VectorBundleKZero.classOf X N) * ch C sX (lambdaNegOne Q r) *
          (toddClass C sX (VectorBundleKZero.classOf X (dualSheaf N)) *
            toddClass C sX (VectorBundleKZero.classOf X (dualSheaf Q)))
        = (ch C sX (1 - VectorBundleKZero.classOf X N) *
            toddClass C sX (VectorBundleKZero.classOf X (dualSheaf N))) *
          (ch C sX (lambdaNegOne Q r) *
            toddClass C sX (VectorBundleKZero.classOf X (dualSheaf Q))) := by
          rw [mul_assoc, ← mul_assoc (ch C sX (lambdaNegOne Q r)), hc.eq, mul_assoc, mul_assoc]
      _ = -firstChernQ C sX N * ((-1 : ℤ) ^ r • RationalTotalChowClass.ofTotalChowClass
            (TotalChowClass.homComponent r (totalChern C sX Q r))) := by
          rw [ch_one_sub_mul_toddClass_dualSheaf, IH]
      _ = _ := by
          rw [map_mul, mul_smul_comm, neg_mul, pow_succ, mul_smul, neg_one_smul]
          rfl

/-! ### The splitting principle for rational classes -/

/-- **Pullback along a morphism with injective restriction of total classes is injective** on
`∏_p A^p ⊗ ℚ` (`ℚ` is flat over `ℤ`). -/
theorem pullbackAQ_injective {P : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
    (π : P ⟶ X) [LocallyOfFiniteType π] (hs : π ≫ sX = sP)
    (hres : Function.Injective (TotalChowClass.res π hs)) :
    Function.Injective (pullbackAQ C sP sX π hs) := by
  intro a b hab
  refine RationalTotalChowClass.ext fun p ↦ ?_
  have hp := congrArg (fun c : RationalTotalChowClass C sP ↦ c p) hab
  simp only [pullbackAQ_apply] at hp
  have hρ : Function.Injective (chowCohomologyRestrictionOfEq C sP sX hs
      (gysinSystemOfInvertible C) (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) p) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have h1 : TotalChowClass.res π hs (TotalChowClass.single p c) = 0 := by
      refine TotalChowClass.ext fun q ↦ ?_
      rw [TotalChowClass.res_apply_eq_chowCohomologyRestrictionOfEq, TotalChowClass.zero_apply]
      rcases eq_or_ne q p with rfl | hq
      · rw [TotalChowClass.single_apply_same, hc]
      · rw [TotalChowClass.single_apply_of_ne hq, map_zero]
    have h2 := congrArg (fun t : TotalChowClass C sX ↦ t p) (hres (h1.trans (map_zero _).symm))
    simp only [TotalChowClass.single_apply_same, TotalChowClass.zero_apply] at h2
    exact h2
  have hQ : Function.Injective ((chowCohomologyRestrictionOfEq C sP sX hs
      (gysinSystemOfInvertible C) (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        p).toIntLinearMap.baseChange ℚ) := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hρ
  exact hQ hp

/-- **The splitting principle for rational classes** (Stacks 02UL): two classes in
`∏_p A^p(X) ⊗ ℚ` agree if their pullbacks agree along every `π : P ⟶ X` along which the `E_i`
acquire filtrations with invertible successive quotients. -/
theorem eq_of_pullbackAQ_eq_of_hasInvertibleFiltration {I : Type} [Fintype I]
    (E : I → X.Modules) (r : I → ℕ)
    (hE : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (E i) (r i))
    {a b : RationalTotalChowClass C sX}
    (h : ∀ {P : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ X)
      [LocallyOfFiniteType π] (hs : π ≫ sX = sP),
      (∀ i, Stacks.WeilCohomology.HasInvertibleFiltration P
        ((Scheme.Modules.pullback π).obj (E i)) (r i)) →
        pullbackAQ C sP sX π hs a = pullbackAQ C sP sX π hs b) :
    a = b := by
  obtain ⟨T, -, -, -, huniv, hfilt, -⟩ := exists_splittingMorphism_isProjective C sX I E r hE
  exact pullbackAQ_injective C sX T.sP T.π T.hsP
    (TotalChowClass.res_injective_of_universallyChowInjective T.π T.hsP _ T.relDim huniv)
    (h T.sP T.π T.hsP hfilt)

/-- **The Koszul identity, dual form**: for `V` finite locally free of rank `r`,
`ch(λ_{-1} V) · td(V^∨) = (-1)^r c_r(V)`, by the splitting principle. -/
theorem ch_lambdaNegOne_mul_toddClass (V : X.Modules) (r : ℕ)
    [hV : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} V r] :
    ch C sX (lambdaNegOne V r) * toddClass C sX (VectorBundleKZero.classOf X (dualSheaf V)) =
      (-1 : ℤ) ^ r • RationalTotalChowClass.ofTotalChowClass
        (TotalChowClass.homComponent r (totalChern C sX V r)) := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} V :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree V r
  refine eq_of_pullbackAQ_eq_of_hasInvertibleFiltration C sX (I := Unit) (fun _ ↦ V)
    (fun _ ↦ r) (fun _ ↦ hV) fun {P} sP _ π _ hs hfilt ↦ ?_
  obtain ⟨L, hL, hQ⟩ := exists_hasQuotients_of_hasInvertibleFiltration (hfilt ())
  have : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (L i) 1 :=
    fun i ↦ @isFiniteLocallyFreeOfRank_one_of_isInvertible _ (L i) (hL i)
  rw [map_mul, pullbackAQ_ch, pullbackAQ_toddClass, pullback_lambdaNegOne,
    pullback_classOf_dualSheaf, map_zsmul, pullbackAQ_ofTotalChowClass,
    TotalChowClass.res_homComponent, TotalChowClass.res_totalChern]
  exact ch_lambdaNegOne_mul_toddClass_of_hasQuotients C sP r _ L hQ

/-- The sign rescaling of a class homogeneous of degree `r` is multiplication by `(-1)^r`. -/
theorem signScale_eq_of_isHomogeneous {c : TotalChowClass C sX} {r : ℕ}
    (hc : c.IsHomogeneous r) : TotalChowClass.signScale c = (-1 : ℤ) ^ r • c := by
  refine TotalChowClass.ext fun p ↦ ?_
  rw [TotalChowClass.signScale_apply, ← TotalChowClass.component_apply p ((-1 : ℤ) ^ r • c),
    map_zsmul, TotalChowClass.component_apply]
  rcases eq_or_ne p r with rfl | hp
  · rfl
  · rw [hc p hp, smul_zero, smul_zero]

/-- `ch(λ_{-1} E) = ∑_{p ≤ r} (-1)^p ch[⋀^p E]`. -/
theorem ch_lambdaNegOne (E : X.Modules) (r : ℕ) :
    ch C sX (lambdaNegOne E r) = ∑ p ∈ range (r + 1), (-1 : ℤ) ^ p •
      ch C sX (VectorBundleKZero.classOf X (Scheme.Modules.exteriorPower E (p : ℤ))) := by
  rw [lambdaNegOne, map_sum]
  simp only [map_zsmul]

/-- **The Koszul identity, multiplied out**: for `Q` finite locally free of rank `r`,
`ch(λ_{-1} Q^∨) · td(Q) = c_r(Q)`. -/
theorem ch_lambdaNegOne_dualSheaf_mul_toddClass (Q : X.Modules) (r : ℕ)
    [hQ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Q r] :
    ch C sX (lambdaNegOne (dualSheaf Q) r) * toddClass C sX (VectorBundleKZero.classOf X Q) =
      RationalTotalChowClass.ofTotalChowClass
        (TotalChowClass.homComponent r (totalChern C sX Q r)) := by
  have hQd := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf Q r hQ
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} Q :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree Q r
  have key := ch_lambdaNegOne_mul_toddClass C sX (dualSheaf Q) r
  rw [toddClass_classOf_dualSheaf_dualSheaf, totalChern_dualSheaf,
    TotalChowClass.homComponent_signScale,
    signScale_eq_of_isHomogeneous C sX (TotalChowClass.isHomogeneous_homComponent r _), map_zsmul,
    smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul] at key
  exact key

/-- **The Koszul identity for Chern characters**. Let `Q` be finite locally free of rank `r` on
`X`. Then

  `∑_{p=0}^{r} (-1)^p ch[⋀^p (Q^∨)] = c_r(Q) · td(-[Q])`   in `∏_p A^p(X) ⊗ ℚ`,

i.e. `ch(λ_{-1} Q^∨) = c_r(Q) td(Q)⁻¹`. Here `c_r(Q)` is the degree-`r` homogeneous component
`TotalChowClass.homComponent r (totalChern C sX Q r)` of the total Chern class of `Q` (the
bivariant `c_r` of Stacks 0B7H), viewed in `RationalTotalChowClass C sX` through
`RationalTotalChowClass.ofTotalChowClass`; `GRR.ch_koszul'` states it with
`totalChernOfFiniteLocallyFree C sX Q` instead. -/
theorem ch_koszul (Q : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Q r] :
    ∑ p ∈ range (r + 1), (-1 : ℤ) ^ p •
        ch C sX (VectorBundleKZero.classOf X (Scheme.Modules.exteriorPower (dualSheaf Q) (p : ℤ))) =
      RationalTotalChowClass.ofTotalChowClass
          (TotalChowClass.homComponent r (totalChern C sX Q r)) *
        toddClass C sX (-VectorBundleKZero.classOf X Q) := by
  rw [← ch_lambdaNegOne, ← ch_lambdaNegOne_dualSheaf_mul_toddClass, mul_assoc,
    toddClass_mul_toddClass_neg, mul_one]

/-- `GRR.ch_koszul` with the top Chern class read off the total Chern class
`totalChernOfFiniteLocallyFree` of Stacks 0ESW. -/
theorem ch_koszul' (Q : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Q r] :
    haveI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree Q r
    ∑ p ∈ range (r + 1), (-1 : ℤ) ^ p •
        ch C sX (VectorBundleKZero.classOf X (Scheme.Modules.exteriorPower (dualSheaf Q) (p : ℤ))) =
      RationalTotalChowClass.ofTotalChowClass
          (TotalChowClass.homComponent r (totalChernOfFiniteLocallyFree C sX Q)) *
        toddClass C sX (-VectorBundleKZero.classOf X Q) := by
  have := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree Q r
  rw [totalChernOfFiniteLocallyFree_eq_totalChern C sX Q r]
  exact ch_koszul C sX Q r

end Chow

end GRR
