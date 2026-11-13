import GRR.PerfectCh
import GRR.DeformationGeom
import GRR.Specialization
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyFreeSmooth
import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree
import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport

/-!
# The closed immersion formula in the core case (item C7)

For a closed immersion `i : X ⟶ P` of smooth schemes over `k`, `P` pure of dimension `n` and the
conormal module of constant rank `r`, `GRR.closedImmersionFormula_core_of` proves
`ch(i_! θ[E]) ∩ [P] = i_*((ch(E) · td(N)⁻¹) ∩ [X])` for every vector bundle `E`, from the
zero-section formula on `𝐏(𝒞 ⊕ 𝒪_X)` (item B5) and `[N] = [𝒞^∨]` (item R5), both hypotheses.
The proof deforms `(i_*E)[0]` to `Q = (i'_*pr^*E)[0]` on `W = Bl_{∞(X)} 𝐏¹_P` and specializes
`(i₀)_*[P] = e_*[E] + a_*β` (items C3–C6 of `notes/E_plan.md`).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open Stacks.ProjectiveCompletion (projectiveCompletion projectiveCompletionProj zeroSection
  completionModule)
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf)
open scoped TensorProduct

universe u

attribute [local instance 10000] HasDerivedCategory.standard

noncomputable section

namespace GRR

namespace ClosedFormulaCore

section Pushforward

variable (C : ChowSituation.{u})

/-- Proper pushforward along the identity is the identity. -/
theorem pushforward_id {A : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
    (x : DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sA j) :
    rationalProperChowPushforward C sA sA (f := 𝟙 A) (Category.id_comp sA) x = x := by
  have h : rationalProperChowPushforward C sA sA (f := 𝟙 A) (Category.id_comp sA) =
      LinearMap.id :=
    rationalChowHomology_linearMap_ext C sA fun j q α => by
      rw [rationalProperChowPushforward_of_tmul, properChowPushforward_id]
      rfl
  rw [h, LinearMap.id_apply]

/-- Proper pushforward along equal morphisms. -/
theorem pushforward_congr_hom {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
    (sB : B ⟶ C.S) [LocallyOfFiniteType sB] {f g : A ⟶ B} [IsProper f] [IsProper g] (h : f = g)
    (hf : f ≫ sB = sA) (hg : g ≫ sB = sA)
    (x : DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sA j) :
    rationalProperChowPushforward C sA sB hf x = rationalProperChowPushforward C sA sB hg x := by
  subst h
  rfl

/-- Proper pushforward on `CH_*(-) ⊗ ℚ` is functorial, for schemes locally of finite type. -/
theorem pushforward_comp {A B D : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
    (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sD : D ⟶ C.S) [LocallyOfFiniteType sD]
    {f : A ⟶ B} [IsProper f] {g : B ⟶ D} [IsProper g] (hf : f ≫ sB = sA) (hg : g ≫ sD = sB)
    (hfg : (f ≫ g) ≫ sD = sA) (x : DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sA j) :
    rationalProperChowPushforward C sA sD hfg x =
      rationalProperChowPushforward C sB sD hg (rationalProperChowPushforward C sA sB hf x) := by
  have h : rationalProperChowPushforward C sA sD hfg =
      (rationalProperChowPushforward C sB sD hg).comp
        (rationalProperChowPushforward C sA sB hf) := by
    refine rationalChowHomology_linearMap_ext C sA fun j q α ↦ ?_
    rw [LinearMap.comp_apply, rationalProperChowPushforward_of_tmul,
      rationalProperChowPushforward_of_tmul, rationalProperChowPushforward_of_tmul]
    congr 2
    exact (DFunLike.congr_fun (properChowPushforward_comp C sA sB sD f g hf hg j
      (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _)) α).symm
  exact DFunLike.congr_fun h x

/-- **`u_*[A] = [B]` for an isomorphism `u : A ⟶ B`** of Noetherian schemes. -/
theorem pushforward_rationalFundamentalClass_of_isIso {A B : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] [IsNoetherian A] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    [IsNoetherian B] (f : A ⟶ B) [IsIso f] (hf : f ≫ sB = sA) :
    rationalProperChowPushforward C sA sB hf (rationalFundamentalClass C sA) =
      rationalFundamentalClass C sB := by
  have hpush : ∀ d (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sB f hf d),
      properChowPushforward C sA sB f hf d hfac (fundamentalChowClass C sA d) =
        fundamentalChowClass C sB d :=
    fun d hfac ↦ properChowPushforward_fundamentalChowClass_of_isIso C sA sB f hf d hfac
  set g : ℤ → DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sB j := fun d =>
    DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sB j) d
      ((1 : ℚ) ⊗ₜ fundamentalChowClass C sB d) with hg
  rw [rationalFundamentalClass_eq, rationalFundamentalClass_eq, map_sum]
  have hterm : ∀ d ∈ (fundamentalClassDegrees_finite C sA).toFinset,
      rationalProperChowPushforward C sA sB hf
          (DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sA j) d
            ((1 : ℚ) ⊗ₜ fundamentalChowClass C sA d)) = g d := by
    intro d _
    rw [rationalProperChowPushforward_of_tmul, hpush]
  have hvanA : ∀ d ∈ (fundamentalClassDegrees_finite C sA).toFinset ∪
      (fundamentalClassDegrees_finite C sB).toFinset,
      d ∉ (fundamentalClassDegrees_finite C sA).toFinset → g d = 0 := by
    intro d _ hd
    rw [Set.Finite.mem_toFinset] at hd
    have h0 : fundamentalChowClass C sA d = 0 := by
      rw [fundamentalChowClass, fundamentalCycle_eq_zero_of_notMem_fundamentalClassDegrees C sA hd,
        map_zero]
    rw [hg]
    dsimp only
    rw [← hpush d (properPushforwardDescends C _ _ _ _ _), h0, map_zero, TensorProduct.tmul_zero,
      map_zero]
  have hvanB : ∀ d ∈ (fundamentalClassDegrees_finite C sA).toFinset ∪
      (fundamentalClassDegrees_finite C sB).toFinset,
      d ∉ (fundamentalClassDegrees_finite C sB).toFinset → g d = 0 := by
    intro d _ hd
    rw [Set.Finite.mem_toFinset] at hd
    rw [hg]
    dsimp only
    rw [fundamentalChowClass, fundamentalCycle_eq_zero_of_notMem_fundamentalClassDegrees C sB hd,
      map_zero, TensorProduct.tmul_zero, map_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_subset Finset.subset_union_left hvanA,
    ← Finset.sum_subset Finset.subset_union_right hvanB]

end Pushforward

section Cap

variable (k : Type u) [Field k] {A B : Scheme.{u}} (sA : A ⟶ Spec (.of k))
  (sB : B ⟶ Spec (.of k)) [LocallyOfFiniteType sA] [LocallyOfFiniteType sB]

/-- **The projection formula** `f_*(f^* c ∩ γ) = c ∩ f_* γ` for a proper `f`, with no smoothness
assumed on its source or target. -/
theorem pushforward_cap_pullbackAQ (f : A ⟶ B) [IsProper f] (hf : f ≫ sB = sA) (c : AQ k sB)
    (γ : CHQ k sA) :
    rationalProperChowPushforward (fieldChowSituation k) sA sB hf
        (cap k sA (pullbackAQ (fieldChowSituation k) sA sB f hf c) γ) =
      cap k sB c (rationalProperChowPushforward (fieldChowSituation k) sA sB hf γ) :=
  rationalProperChowPushforward_totalRationalChowCap_pullbackAQ (fieldChowSituation k) sA sB f hf
    (bddBelow_relativeDimension_field k sA) (bddBelow_relativeDimension_field k sB) c γ

/-- The zero class caps every class to zero. -/
theorem cap_zero_apply (γ : CHQ k sA) : cap k sA 0 γ = 0 := by
  simp only [cap, map_zero, LinearMap.zero_apply]

end Cap

section Completion

variable (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsSmoothFT k sX]

/-- The projective completion `𝐏(𝒞 ⊕ 𝒪_X)` of a vector bundle of constant rank on a smooth `X`
is smooth, separated and of finite type over `k`. -/
theorem isSmoothFT_completion (𝒞 : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞] (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r] :
    IsSmoothFT k (projectiveCompletionProj 𝒞 ≫ sX) :=
  haveI : Smooth (projectiveCompletionProj 𝒞) :=
    Stacks.Chow.smooth_bundleProj (completionModule 𝒞) r
  { smooth := inferInstance
    isSeparated := inferInstance
    quasiCompact := inferInstance }

end Completion

/-- `s_*(ρ^*E)` is coherent on `𝐏(𝒞 ⊕ 𝒪_X)` for a finite locally free `E` on `X`, `s` the zero
section and `ρ : 𝐏(𝒪_X) ⟶ X`. -/
theorem coherentModules_pushforward_zeroSection {X : Scheme.{u}} (𝒞 : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞]
    [IsLocallyNoetherian (projectiveCompletion 𝒞)] (E : X.Modules)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    Stacks.SheafOfModules.coherentModules (projectiveCompletion 𝒞).ringCatSheaf
      ((Scheme.Modules.pushforward (zeroSection 𝒞)).obj
        ((Scheme.Modules.pullback (bundleProj (Stacks.Ample.unitModule X))).obj E)) := by
  have : IsLocallyNoetherian (bundle (Stacks.Ample.unitModule X)) :=
    isLocallyNoetherian_of_isClosedImmersion (zeroSection 𝒞)
  have h1 := isCoherent_of_isFiniteLocallyFree_of_isLocallyNoetherian
    ((Scheme.Modules.pullback (bundleProj (Stacks.Ample.unitModule X))).obj E)
    (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme _ _ hE)
  have h2 := (Stacks.AlgebraicGeometry.GrothendieckGroupAffine.isCoherent_iff_isCoherent' _).1 h1
  exact (Stacks.AlgebraicGeometry.GrothendieckGroupAffine.isCoherent_iff_isCoherent' _).2
    (isCoherent_pushforward_of_isClosedImmersion (zeroSection 𝒞) _)

section Conormal

variable (k : Type u) [Field k] {X P : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sP : P ⟶ Spec (.of k)) [IsSmoothFT k sX] [IsSmoothFT k sP] (i : X ⟶ P) [IsClosedImmersion i]
  (hi : i ≫ sP = sX)

/-- The conormal bundle `𝒞 = 𝒩^∨` of `i`, where `𝒩 = (conormalModule i)^∨` is the normal bundle
of `i` as a regular immersion: the exceptional divisor of the deformation to the normal cone is
`𝐏(𝒞 ⊕ 𝒪_X)` (`Stacks.Chow.exceptionalFibreIsoProjectiveCompletion`). -/
abbrev conormalBundle : X.Modules :=
  haveI : IsLocallyNoetherian X := (isNoetherian k sX).toIsLocallyNoetherian
  dualSheaf (VirtualNormalBundle.ofIsRegularImmersion i
    (DeformationGeom.isRegularImmersion_of_isSmoothFT k sX sP i hi)).bundle

/-- `𝒞` has the rank of the conormal module. -/
theorem isFiniteLocallyFreeOfRank_conormalBundle (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule i) r] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (conormalBundle k sX sP i hi) r :=
  Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf _ r
    (Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFreeOfRank_dualSheaf
      (conormalModule i) r inferInstance)

/-- `𝐏(𝒞 ⊕ 𝒪_X)` is smooth, separated and of finite type over `k`. -/
theorem isSmoothFT_conormalCompletion (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule i) r] :
    IsSmoothFT k (projectiveCompletionProj (conormalBundle k sX sP i hi) ≫ sX) :=
  haveI := isFiniteLocallyFreeOfRank_conormalBundle k sX sP i hi r
  isSmoothFT_completion k sX _ r

end Conormal

end ClosedFormulaCore

open DeformationGeom

-- `q : W ⟶ P`, `i₀ : P ⟶ W`, `e : E ⟶ W`, `a : X' ⟶ W`, `𝒞`, `π : P̄ ⟶ X`, `φ : E ≅ P̄`
set_option hygiene false in
local notation "𝐂𝐇" => fieldChowSituation k
set_option hygiene false in
local notation "𝐪" => DeformationGeom.proj sP i
set_option hygiene false in
local notation "𝐢₀" => DeformationGeom.sectionAtZero sP i
set_option hygiene false in
local notation "𝐞" => DeformationGeom.exceptionalInclusion sP i
set_option hygiene false in
local notation "𝐚" => DeformationGeom.strictTransformInclusion sP i
set_option hygiene false in
local notation "𝐂" => ClosedFormulaCore.conormalBundle k sX sP i hi
set_option hygiene false in
local notation "𝛑" => projectiveCompletionProj (ClosedFormulaCore.conormalBundle k sX sP i hi)
set_option hygiene false in
local notation "𝛗" => exceptionalFibreIsoProjectiveCompletion sP i
  (DeformationGeom.isRegularImmersion_of_isSmoothFT k sX sP i hi)

variable (k : Type u) [Field k] {X P : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sP : P ⟶ Spec (.of k)) [IsSmoothFT k sX] [IsSmoothFT k sP] (i : X ⟶ P) [IsClosedImmersion i]
  (hi : i ≫ sP = sX)

/-- **The closed immersion formula in the core case** (item C7 of `notes/E_plan.md`). Let
`i : X ⟶ P` be a closed immersion of smooth separated schemes of finite type over `k`, with `P`
pure of dimension `n` and the conormal module of constant rank `r`. Let `𝒞` be the conormal
bundle (`GRR.ClosedFormulaCore.conormalBundle`), `π : P̄ = 𝐏(𝒞 ⊕ 𝒪_X) ⟶ X`, `s` its zero section
and `ρ : 𝐏(𝒪_X) ⟶ X`. Assume the zero-section formula (item B5)

  `π_*(ch(K) ∩ [P̄]) = (ch(E) · td(-[𝒞^∨])) ∩ [X]`  for `K ≅ (s_*ρ^*E)[0]`,

and `[N_{X/P}] = [𝒞^∨]` (item R5). Then for every finite locally free `E` on `X`

  `ch(i_! θ[E]) ∩ [P] = i_*((ch(E) · td(N_{X/P})⁻¹) ∩ [X])`. -/
theorem closedImmersionFormula_core_of {n : ℕ} (hP : RelativeDimension sP n) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule i) r]
    (hB5 : haveI := ClosedFormulaCore.isSmoothFT_conormalCompletion k sX sP i hi r
      ∀ (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
        {K : DerivedCategory (projectiveCompletion 𝐂).Modules} (hK : HasDefinedChernClasses K)
        (_ : K ≅ (DerivedCategory.singleFunctor _ 0).obj
          ((Scheme.Modules.pushforward (zeroSection 𝐂)).obj
            ((Scheme.Modules.pullback (bundleProj (Stacks.Ample.unitModule X))).obj E))),
        rationalProperChowPushforward (fieldChowSituation k) (𝛑 ≫ sX) sX rfl
            (cap k (𝛑 ≫ sX) (perfectCh (fieldChowSituation k) _ hK)
              (fundamentalClass k (𝛑 ≫ sX))) =
          cap k sX (ch (fieldChowSituation k) sX (VectorBundleKZero.classOf X E) *
              toddClass (fieldChowSituation k) sX (-VectorBundleKZero.classOf X (dualSheaf 𝐂)))
            (fundamentalClass k sX))
    (hR5 : normalClass k sP i = VectorBundleKZero.classOf X (dualSheaf 𝐂))
    (E : X.Modules) [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    haveI := compactSpace k sP
    haveI : IsLocallyNoetherian P := (isNoetherian k sP).toIsLocallyNoetherian
    cap k sP (chK k sP (pushforwardK i (vectorBundleEquiv k sX (VectorBundleKZero.classOf X E))))
        (fundamentalClass k sP) =
      rationalProperChowPushforward (fieldChowSituation k) sX sP hi
        (cap k sX (ch (fieldChowSituation k) sX (VectorBundleKZero.classOf X E) *
            toddClass (fieldChowSituation k) sX (-normalClass k sP i))
          (fundamentalClass k sX)) := by
  have : IsLocallyNoetherian X := (isNoetherian k sX).toIsLocallyNoetherian
  have : IsLocallyNoetherian P := (isNoetherian k sP).toIsLocallyNoetherian
  have := compactSpace k sP
  have hW : IsSmoothFT k (𝐪 ≫ sP) := isSmoothFT_blowupAtInfinity k sX sP i hi
  have := ClosedFormulaCore.isFiniteLocallyFreeOfRank_conormalBundle k sX sP i hi r
  have hPb : IsSmoothFT k (𝛑 ≫ sX) := ClosedFormulaCore.isSmoothFT_conormalCompletion k sX sP i hi r
  have : IsLocallyNoetherian (projectiveCompletion 𝐂) :=
    (isNoetherian k (𝛑 ≫ sX)).toIsLocallyNoetherian
  have := isNoetherian k (𝛑 ≫ sX)
  have := isNoetherian_of_quasiCompact_fieldChowSituation k (𝐞 ≫ 𝐪 ≫ sP)
  -- `Q = (i'_*pr^*E)[0]` on `W` and `(s_*ρ^*E)[0]` on `P̄` have defined Chern classes (C1)
  have hQ : HasDefinedChernClasses (Q i E) :=
    hasDefinedChernClasses_single_coherent k (𝐪 ≫ sP) ⟨_, coherentModules_pushforward_G i E⟩
  have hK : HasDefinedChernClasses ((DerivedCategory.singleFunctor
      (projectiveCompletion 𝐂).Modules 0).obj ((Scheme.Modules.pushforward (zeroSection 𝐂)).obj
        ((Scheme.Modules.pullback (bundleProj (Stacks.Ample.unitModule X))).obj E))) :=
    hasDefinedChernClasses_single_coherent k (𝛑 ≫ sX)
      ⟨_, ClosedFormulaCore.coherentModules_pushforward_zeroSection 𝐂 E⟩
  -- the zero fibre (C3, A2, A4): `ch(i_! θ[E]) = i₀^* ch(Q)`
  have h₀ : 𝐢₀ ≫ 𝐪 ≫ sP = sP := sectionAtZero_comp_proj_assoc sP i sP
  have hA1 : chK k sP (pushforwardK i (vectorBundleEquiv k sX (VectorBundleKZero.classOf X E))) =
      pullbackAQ 𝐂𝐇 sP (𝐪 ≫ sP) 𝐢₀ h₀ (perfectCh 𝐂𝐇 (𝐪 ≫ sP) hQ) := by
    rw [pullbackAQ_perfectCh]
    exact chK_pushforwardK_classOf_eq_perfectCh k sX sP i E _ (deformationZeroFibreIso sP i E)
  -- `γ = q_*(i₀)_*γ`, as `i₀ ≫ q = 𝟙`
  have hA2 : ∀ γ : CHQ k sP, γ =
      rationalProperChowPushforward 𝐂𝐇 (𝐪 ≫ sP) sP (f := 𝐪) rfl
        (rationalProperChowPushforward 𝐂𝐇 sP (𝐪 ≫ sP) (f := 𝐢₀) h₀ γ) := by
    intro γ
    rw [← ClosedFormulaCore.pushforward_comp 𝐂𝐇 sP (𝐪 ≫ sP) sP (f := 𝐢₀) (g := 𝐪) h₀ rfl
        (by rw [sectionAtZero_comp_proj, Category.id_comp]),
      ClosedFormulaCore.pushforward_congr_hom 𝐂𝐇 sP sP (sectionAtZero_comp_proj sP i) _
        (Category.id_comp sP),
      ClosedFormulaCore.pushforward_id]
  -- the specialization (C6): `(i₀)_*[P] = e_*[E] + a_*β`
  obtain ⟨β, hβ⟩ : ∃ β : CHQ k (𝐚 ≫ 𝐪 ≫ sP),
      rationalProperChowPushforward 𝐂𝐇 sP (𝐪 ≫ sP) (f := 𝐢₀) h₀ (fundamentalClass k sP) =
        rationalProperChowPushforward 𝐂𝐇 (𝐞 ≫ 𝐪 ≫ sP) (𝐪 ≫ sP) (f := 𝐞) rfl
            (rationalFundamentalClass 𝐂𝐇 (𝐞 ≫ 𝐪 ≫ sP)) +
          rationalProperChowPushforward 𝐂𝐇 (𝐚 ≫ 𝐪 ≫ sP) (𝐪 ≫ sP) (f := 𝐚) rfl β :=
    exists_specialization_fundamentalClass k sP i hP
  -- the strict transform term vanishes (C5, A1, A2)
  have hB : rationalProperChowPushforward 𝐂𝐇 (𝐪 ≫ sP) sP (f := 𝐪) rfl
      (cap k (𝐪 ≫ sP) (perfectCh 𝐂𝐇 (𝐪 ≫ sP) hQ)
        (rationalProperChowPushforward 𝐂𝐇 (𝐚 ≫ 𝐪 ≫ sP) (𝐪 ≫ sP) (f := 𝐚) rfl β)) = 0 := by
    rw [← ClosedFormulaCore.pushforward_cap_pullbackAQ k (𝐚 ≫ 𝐪 ≫ sP) (𝐪 ≫ sP) 𝐚 rfl
        (perfectCh 𝐂𝐇 (𝐪 ≫ sP) hQ) β, pullbackAQ_perfectCh,
      perfectCh_eq_zero 𝐂𝐇 _ _ (isZero_deformationStrictTransform sP i E),
      ClosedFormulaCore.cap_zero_apply, map_zero, map_zero]
  -- the exceptional divisor term: `e^* ch(Q) = φ^* ch(s_*ρ^*E)` (C4, A2)
  have hφ : (𝛗).hom ≫ 𝛑 ≫ sX = 𝐞 ≫ 𝐪 ≫ sP := by
    rw [exceptionalFibreIsoProjectiveCompletion_hom_projection_assoc,
      exceptionalInclusion_comp_proj_assoc, hi]
  have hpull : pullbackAQ 𝐂𝐇 (𝐞 ≫ 𝐪 ≫ sP) (𝐪 ≫ sP) 𝐞 rfl (perfectCh 𝐂𝐇 (𝐪 ≫ sP) hQ) =
      pullbackAQ 𝐂𝐇 (𝐞 ≫ 𝐪 ≫ sP) (𝛑 ≫ sX) (𝛗).hom hφ (perfectCh 𝐂𝐇 (𝛑 ≫ sX) hK) :=
    (pullbackAQ_perfectCh 𝐂𝐇 (𝐪 ≫ sP) (𝐞 ≫ 𝐪 ≫ sP) 𝐞 rfl hQ).trans
      (pullbackAQ_perfectCh_of_iso 𝐂𝐇 (𝛑 ≫ sX) (𝐞 ≫ 𝐪 ≫ sP) (𝛗).hom hφ hK
        (hQ.derivedPullback 𝐞)
        (deformationExceptionalFibreIso sP i
          (DeformationGeom.isRegularImmersion_of_isSmoothFT k sX sP i hi) r E).symm).symm
  -- transport along `e ≫ q = φ ≫ π ≫ i`, `φ_*[E] = [P̄]`, then B5 and R5
  have heq : 𝐞 ≫ 𝐪 = (𝛗).hom ≫ 𝛑 ≫ i := by
    rw [exceptionalInclusion_comp_proj,
      exceptionalFibreIsoProjectiveCompletion_hom_projection_assoc]
  have hπi : (𝛑 ≫ i) ≫ sP = 𝛑 ≫ sX := by rw [Category.assoc, hi]
  have hφi : ((𝛗).hom ≫ 𝛑 ≫ i) ≫ sP = 𝐞 ≫ 𝐪 ≫ sP := by
    rw [Category.assoc, Category.assoc, hi, hφ]
  have h1 := ClosedFormulaCore.pushforward_cap_pullbackAQ k (𝐞 ≫ 𝐪 ≫ sP) (𝐪 ≫ sP) 𝐞 rfl
    (perfectCh 𝐂𝐇 (𝐪 ≫ sP) hQ) (rationalFundamentalClass 𝐂𝐇 (𝐞 ≫ 𝐪 ≫ sP))
  have h2 := ClosedFormulaCore.pushforward_comp 𝐂𝐇 (𝐞 ≫ 𝐪 ≫ sP) (𝐪 ≫ sP) sP (f := 𝐞) (g := 𝐪)
    rfl rfl (Category.assoc _ _ _)
    (cap k (𝐞 ≫ 𝐪 ≫ sP) (pullbackAQ 𝐂𝐇 (𝐞 ≫ 𝐪 ≫ sP) (𝐪 ≫ sP) 𝐞 rfl
      (perfectCh 𝐂𝐇 (𝐪 ≫ sP) hQ)) (rationalFundamentalClass 𝐂𝐇 (𝐞 ≫ 𝐪 ≫ sP)))
  have h3 := ClosedFormulaCore.pushforward_congr_hom 𝐂𝐇 (𝐞 ≫ 𝐪 ≫ sP) sP heq
    (Category.assoc _ _ _) hφi
    (cap k (𝐞 ≫ 𝐪 ≫ sP) (pullbackAQ 𝐂𝐇 (𝐞 ≫ 𝐪 ≫ sP) (𝛑 ≫ sX) (𝛗).hom hφ
      (perfectCh 𝐂𝐇 (𝛑 ≫ sX) hK)) (rationalFundamentalClass 𝐂𝐇 (𝐞 ≫ 𝐪 ≫ sP)))
  have h4 := ClosedFormulaCore.pushforward_comp 𝐂𝐇 (𝐞 ≫ 𝐪 ≫ sP) (𝛑 ≫ sX) sP
    (f := (𝛗).hom) (g := 𝛑 ≫ i) hφ hπi hφi
    (cap k (𝐞 ≫ 𝐪 ≫ sP) (pullbackAQ 𝐂𝐇 (𝐞 ≫ 𝐪 ≫ sP) (𝛑 ≫ sX) (𝛗).hom hφ
      (perfectCh 𝐂𝐇 (𝛑 ≫ sX) hK)) (rationalFundamentalClass 𝐂𝐇 (𝐞 ≫ 𝐪 ≫ sP)))
  have h5 := ClosedFormulaCore.pushforward_comp 𝐂𝐇 (𝛑 ≫ sX) sX sP (f := 𝛑) (g := i) rfl hi hπi
  have h6 := ClosedFormulaCore.pushforward_cap_pullbackAQ k (𝐞 ≫ 𝐪 ≫ sP) (𝛑 ≫ sX) (𝛗).hom hφ
    (perfectCh 𝐂𝐇 (𝛑 ≫ sX) hK) (rationalFundamentalClass 𝐂𝐇 (𝐞 ≫ 𝐪 ≫ sP))
  have h7 : rationalProperChowPushforward 𝐂𝐇 (𝐞 ≫ 𝐪 ≫ sP) (𝛑 ≫ sX) hφ
      (rationalFundamentalClass 𝐂𝐇 (𝐞 ≫ 𝐪 ≫ sP)) = fundamentalClass k (𝛑 ≫ sX) :=
    ClosedFormulaCore.pushforward_rationalFundamentalClass_of_isIso 𝐂𝐇 _ _ (𝛗).hom hφ
  have hC : rationalProperChowPushforward 𝐂𝐇 (𝐪 ≫ sP) sP (f := 𝐪) rfl
      (cap k (𝐪 ≫ sP) (perfectCh 𝐂𝐇 (𝐪 ≫ sP) hQ)
        (rationalProperChowPushforward 𝐂𝐇 (𝐞 ≫ 𝐪 ≫ sP) (𝐪 ≫ sP) (f := 𝐞) rfl
          (rationalFundamentalClass 𝐂𝐇 (𝐞 ≫ 𝐪 ≫ sP)))) =
      rationalProperChowPushforward 𝐂𝐇 sX sP hi
        (cap k sX (ch 𝐂𝐇 sX (VectorBundleKZero.classOf X E) *
            toddClass 𝐂𝐇 sX (-normalClass k sP i)) (fundamentalClass k sX)) := by
    rw [← h1, ← h2, hpull, h3, h4, h5, h6, h7, hB5 E hK (Iso.refl _), hR5]
  -- assembly: `ch(i_!θ[E]) ∩ [P] = q_*(ch(Q) ∩ (e_*[E] + a_*β))`
  rw [hA1]
  refine (hA2 _).trans ?_
  rw [ClosedFormulaCore.pushforward_cap_pullbackAQ k sP (𝐪 ≫ sP) 𝐢₀ h₀, hβ, map_add, map_add, hC,
    hB, add_zero]

/-- **`GRR.ClosedImmersionFormula` in the core case**, from the zero-section formula (B5) and
`[N_{X/P}] = [𝒞^∨]` (R5): `GRR.closedImmersionFormula_core_of` for every vector bundle, extended
to `K'₀(X)` by `GRR.closedImmersionFormula_of_bundles`. -/
theorem closedImmersionFormula_of_zeroSectionFormula {n : ℕ} (hP : RelativeDimension sP n)
    (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule i) r]
    (hB5 : haveI := ClosedFormulaCore.isSmoothFT_conormalCompletion k sX sP i hi r
      ∀ (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
        {K : DerivedCategory (projectiveCompletion 𝐂).Modules} (hK : HasDefinedChernClasses K)
        (_ : K ≅ (DerivedCategory.singleFunctor _ 0).obj
          ((Scheme.Modules.pushforward (zeroSection 𝐂)).obj
            ((Scheme.Modules.pullback (bundleProj (Stacks.Ample.unitModule X))).obj E))),
        rationalProperChowPushforward (fieldChowSituation k) (𝛑 ≫ sX) sX rfl
            (cap k (𝛑 ≫ sX) (perfectCh (fieldChowSituation k) _ hK)
              (fundamentalClass k (𝛑 ≫ sX))) =
          cap k sX (ch (fieldChowSituation k) sX (VectorBundleKZero.classOf X E) *
              toddClass (fieldChowSituation k) sX (-VectorBundleKZero.classOf X (dualSheaf 𝐂)))
            (fundamentalClass k sX))
    (hR5 : normalClass k sP i = VectorBundleKZero.classOf X (dualSheaf 𝐂)) :
    ClosedImmersionFormula k sX sP i hi :=
  closedImmersionFormula_of_bundles k sX sP i hi fun E _ ↦
    closedImmersionFormula_core_of k sX sP i hi hP r hB5 hR5 E

end GRR

end
