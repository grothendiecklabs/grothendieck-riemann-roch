import Mathlib
import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersectionCycles
import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.RegularImmersionDeformationTop
import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.LocalizationSequenceOpenImmersion
import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.SmoothComparison
import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDimension
import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction
import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Codimension
import StacksFrontier.AlgebraicGeometry.NormalizationBaseChangeBirational.Basic
import StacksFrontier.Topology.Sober.Generization
import GRR.Statement

/-!
# Specialization of the fundamental class in the deformation to the normal cone (item C6)

For a closed immersion `i : X ⟶ P`, `W` the blowup of `𝐏¹_P` in `∞(X)`, `i₀ : P ⟶ W` the section
at zero, `e : E = W_∞ ×_P X ⟶ W` and `a : X' ⟶ W`: if `P` is pure of dimension `n`, then
`(i₀)_*[P] = e_*[E] + a_*β` in `CH_*(W) ⊗ ℚ` (`GRR.exists_specialization_fundamentalClass`).
Stacks 0F9J gives `(i₀)_*[P]_n = (i_∞)_*[W_∞]_n`; Stacks 02RX on `W_∞ ∖ X' = E ∖ X'` writes
`[W_∞]_n - [E]_n` as a class from `X'`; `E` is pure of dimension `n`, being a Cartier divisor of
`W` whose generic points lie over `𝐀¹_P`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open scoped TensorProduct

universe u

namespace GRR.Specialization

section Modification

/-- The section at zero `i₀ : X ⟶ W` of a modification of `X ×_S 𝐏¹_S` is a closed immersion. -/
instance isClosedImmersion_modificationSectionAtZero {X W S : Scheme.{u}} (f : X ⟶ S)
    (b : W ⟶ projectiveLineProduct f) (h : IsIso (modificationFibreAtZeroProjection f b)) :
    IsClosedImmersion (modificationSectionAtZero f b h) := by
  unfold modificationSectionAtZero
  infer_instance

variable (C : ChowSituation.{u}) {X W : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))

omit [LocallyOfFiniteType f] [IsProper b] in
/-- The section at zero `i₀ : X ⟶ W` lies over the base. -/
theorem sectionAtZero_comp_structure :
    modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA) ≫
      modificationProjection f b ≫ f = f := by
  rw [← Category.assoc, modificationSectionAtZero_comp_projection f b hA, Category.id_comp]

/-- **Stacks 0F9J on a fundamental class**: `(i_∞)_*[W_∞]_n = (i₀)_*[X]_n` in `A_n(W)`, when
`dim_δ X ≤ n` and the fibre at infinity is an effective Cartier divisor. -/
theorem inclusionAtInfinity_pushforward_fundamentalChowClass (n : ℤ)
    (hX : schemeDeltaDimension C f ≤ (n : EInt))
    (hcart : Stacks.Divisors.IsEffectiveCartierDivisor
      (modificationInfinityBaseChange f b (𝟙 X)).ker) :
    properChowPushforward C (modificationInclusionAtInfinity f b ≫ modificationProjection f b ≫ f)
        (modificationProjection f b ≫ f) (modificationInclusionAtInfinity f b) rfl n
        (properPushforwardDescends C _ _ _ _ _)
        (fundamentalChowClass C
          (modificationInclusionAtInfinity f b ≫ modificationProjection f b ≫ f) n) =
      properChowPushforward C f (modificationProjection f b ≫ f)
        (modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA))
        (sectionAtZero_comp_structure C f b hA) n (properPushforwardDescends C _ _ _ _ _)
        (fundamentalChowClass C f n) := by
  have hT : schemeDeltaDimension C (𝟙 X ≫ f) ≤ (n : EInt) :=
    (schemeDeltaDimension_congr C (Category.id_comp f)).trans_le hX
  have h1 := chowPushforward_gysinCapOfLift C f b (𝟙 X) hA n
    (fundamentalChowClass C (𝟙 X ≫ f) n)
  rw [gysinCapOfLift_fundamentalChowClass C f b hA (𝟙 X) n hT hcart] at h1
  unfold chowPushforwardOfIsClosedImmersion at h1
  -- transport along the isomorphism `W ×_X X ⟶ W`
  have h2 := congrArg (properChowPushforward C (modificationBaseChangeOver f b (𝟙 X))
    (modificationProjection f b ≫ f) (pullback.fst (modificationProjection f b) (𝟙 X)) rfl n
    (properPushforwardDescends C _ _ _ _ _)) h1
  have hw : (pullback.fst (modificationProjectionAtInfinity f b) (𝟙 X) ≫
      modificationInclusionAtInfinity f b) ≫ modificationProjection f b ≫ f =
      modificationInfinityBaseChangeOver f b (𝟙 X) := by
    simp only [modificationInfinityBaseChangeOver, modificationProjectionAtInfinity,
      Category.assoc]
  have hψ' : pullback.fst (modificationProjectionAtInfinity f b) (𝟙 X) ≫
      modificationInclusionAtInfinity f b ≫ modificationProjection f b ≫ f =
      modificationInfinityBaseChangeOver f b (𝟙 X) :=
    (Category.assoc _ _ _).symm.trans hw
  rw [← properChowPushforward_comp_apply C _ _ _ _ _
      (pullback.fst (modificationProjectionAtInfinity f b) (𝟙 X) ≫
        modificationInclusionAtInfinity f b)
      (modificationInfinityBaseChange_comp_fst f b (𝟙 X)) _ _ hw n _ _
      (properPushforwardDescends C _ _ _ _ _),
    properChowPushforward_comp_apply C _
      (modificationInclusionAtInfinity f b ≫ modificationProjection f b ≫ f) _
      (pullback.fst (modificationProjectionAtInfinity f b) (𝟙 X))
      (modificationInclusionAtInfinity f b) _ rfl hψ' rfl hw n
      (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
      (properPushforwardDescends C _ _ _ _ _),
    properChowPushforward_fundamentalChowClass_of_isIso] at h2
  rw [h2]
  -- `[X]` read over `𝟙 X ≫ f` is the pushforward of `[X]` along `𝟙 X`
  have hid : 𝟙 X ≫ 𝟙 X ≫ f = f := by rw [Category.id_comp, Category.id_comp]
  rw [← properChowPushforward_fundamentalChowClass_of_isIso C f (𝟙 X ≫ f) (𝟙 X) hid n
    (properPushforwardDescends C _ _ _ _ _)]
  rw [← properChowPushforward_comp_apply C _ _ _ (𝟙 X) _ _ rfl _ _ _ n _ _
      (properPushforwardDescends C _ _ _ _ _),
    ← properChowPushforward_comp_apply C _ _ _ _ _
      (modificationSectionAtZero f b (isIso_modificationFibreAtZeroProjection f b hA)) ?_ _ _
      (sectionAtZero_comp_structure C f b hA) n _ _ (properPushforwardDescends C _ _ _ _ _)]
  · rw [Category.id_comp, modificationSectionAtZeroBaseChange, pullback.lift_fst, Category.id_comp]
  · rw [Category.assoc, modificationSectionAtZeroBaseChange_over, Category.id_comp,
      Category.id_comp]

end Modification

section Localization

variable (C : ChowSituation.{u})

/-- **Stacks 02RX on a fundamental class.** Let `e : E ⟶ V`, `a : Z ⟶ V` be closed immersions and
`m : N ⟶ V` an open immersion onto the complement of `Z` factoring through `E` by an open
immersion. Then `[V]_n = e_*[E]_n + a_*β` for some `β ∈ A_n(Z)`. -/
theorem exists_fundamentalChowClass_eq_add {V E Z N : Scheme.{u}}
    (sV : V ⟶ C.S) [LocallyOfFiniteType sV]
    (e : E ⟶ V) [IsClosedImmersion e] (sE : E ⟶ C.S) [LocallyOfFiniteType sE] (he : e ≫ sV = sE)
    (a : Z ⟶ V) [IsClosedImmersion a] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (ha : a ≫ sV = sZ)
    (m : N ⟶ V) [IsOpenImmersion m] (u : N ⟶ E) [IsOpenImmersion u] (hum : u ≫ e = m)
    (hcompl : Set.range a = (Set.range m)ᶜ) (n : ℤ) :
    ∃ β : chowGroup C sZ n,
      fundamentalChowClass C sV n =
        chowPushforwardOfIsClosedImmersion C sE sV e he n (fundamentalChowClass C sE n) +
          chowPushforwardOfIsClosedImmersion C sZ sV a ha n β := by
  have hexact := exact_chowPushforward_chowGroupRestrict C sV (m ≫ sV) m rfl n sZ a ha hcompl
  have hu : u ≫ sE = m ≫ sV := by rw [← hum, Category.assoc, he]
  have hres : chowGroupRestrict C sV (m ≫ sV) m rfl n
      (fundamentalChowClass C sV n -
        chowPushforwardOfIsClosedImmersion C sE sV e he n (fundamentalChowClass C sE n)) = 0 := by
    rw [map_sub, chowGroupRestrict_fundamentalChowClass_of_isOpenImmersion,
      chowPushforwardOfIsClosedImmersion,
      chowGroupRestrict_properChowPushforward_of_comp_eq C sE sV (m ≫ sV) e he m rfl u hu hum n,
      chowGroupRestrict_fundamentalChowClass_of_isOpenImmersion, sub_self]
  obtain ⟨β, hβ⟩ := (hexact _).mp hres
  exact ⟨β, by rw [hβ]; abel⟩

end Localization

section Rational

/-- On a Noetherian scheme all of whose irreducible components have `δ`-dimension `n`, the
rational fundamental class is `1 ⊗ [T]_n`, placed in degree `n`. -/
theorem rationalFundamentalClass_eq_of_deltaDimension (C : ChowSituation.{u}) {T : Scheme.{u}}
    (sT : T ⟶ C.S) [LocallyOfFiniteType sT] [IsNoetherian T] {n : ℤ}
    (hT : ∀ V : irreducibleComponents T, deltaDimension C sT
      ⟨V, V.2.1, isClosed_of_mem_irreducibleComponents (V : Set T) V.2⟩ = n) :
    rationalFundamentalClass C sT =
      DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sT j) n
        ((1 : ℚ) ⊗ₜ fundamentalChowClass C sT n) := by
  rw [rationalFundamentalClass_eq]
  by_cases hn : n ∈ (fundamentalClassDegrees_finite C sT).toFinset
  · refine Finset.sum_eq_single_of_mem _ hn fun m _ hm => ?_
    rw [fundamentalChowClass_eq_zero_of_deltaDimension_eq C sT hT hm, TensorProduct.tmul_zero,
      map_zero]
  · have h0 : fundamentalChowClass C sT n = 0 := by
      rw [fundamentalChowClass, fundamentalCycle_eq_zero_of_notMem_fundamentalClassDegrees C sT
        fun h => hn ((fundamentalClassDegrees_finite C sT).mem_toFinset.2 h), map_zero]
    rw [h0, TensorProduct.tmul_zero, map_zero]
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [fundamentalChowClass_eq_zero_of_deltaDimension_eq C sT hT (fun e => hn (e ▸ hm)),
      TensorProduct.tmul_zero, map_zero]

/-- `x + 1 ≤ 1` forces `x = 0` in `ℕ∞`. -/
theorem enat_eq_zero_of_add_one_le_one {x : ℕ∞} (h : x + 1 ≤ 1) : x = 0 := by
  induction x using ENat.recTopCoe with
  | top => simp at h
  | coe m =>
    have h' : ((m + 1 : ℕ) : ℕ∞) ≤ ((1 : ℕ) : ℕ∞) := by exact_mod_cast h
    have h'' : m + 1 ≤ 1 := by exact_mod_cast h'
    have hm : m = 0 := by omega
    rw [hm]
    rfl

end Rational

section Range

variable {X P S : Scheme.{u}} (f : P ⟶ S) (i : X ⟶ P) [IsClosedImmersion i]

/-- The strict transform `X' ⊆ W_∞` is the complement of the image of the normal cone
`C_X P ⟶ W_∞` (Stacks 0FBH), which is `W_∞ ∖ X' = E ∖ X'`. -/
theorem range_strictTransformToFibreAtInfinity :
    Set.range (strictTransformToFibreAtInfinity f i) =
      (Set.range (normalConeToFibreAtInfinity i f))ᶜ := by
  ext w
  refine ⟨fun hw hm =>
    Set.disjoint_left.mp (disjoint_range_strictTransformToFibreAtInfinity f i) hw hm,
    fun hw => ?_⟩
  have h1 : w ∉ ((normalConeToFibreAtInfinity i f).opensRange : Set _) := by
    rwa [Scheme.Hom.coe_opensRange]
  rw [opensRange_normalConeToFibreAtInfinity] at h1
  have h2 : modificationInclusionAtInfinity f (blowupAtInfinityToProjectiveLineProduct i.ker f) w ∈
      ((strictTransformIdealAtInfinity i.ker).support : Set _) := by
    by_contra h
    exact h1 h
  rw [← Scheme.IdealSheafData.range_subschemeι] at h2
  obtain ⟨y, hy⟩ := h2
  refine ⟨y, (modificationInclusionAtInfinity f
    (blowupAtInfinityToProjectiveLineProduct i.ker f)).isClosedEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, strictTransformToFibreAtInfinity_inclusion, hy]

end Range

section Blowup

variable (C : ChowSituation.{u}) {X P : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
  (i : X ⟶ P) [IsClosedImmersion i]

-- `b : W ⟶ P ×_S 𝐏¹_S`, `q : W ⟶ P`, `i_∞ : W_∞ ⟶ W`, `i₀ : P ⟶ W`, `e : E ⟶ W`, `a : X' ⟶ W`
set_option hygiene false in
local notation "𝐛" => blowupAtInfinityToProjectiveLineProduct (Scheme.Hom.ker i) sP
set_option hygiene false in
local notation "𝐪" => modificationProjection sP 𝐛
set_option hygiene false in
local notation "𝐢∞" => modificationInclusionAtInfinity sP 𝐛
set_option hygiene false in
local notation "𝐡𝐀" =>
  isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct (Scheme.Hom.ker i) sP
set_option hygiene false in
local notation "𝐢₀" =>
  modificationSectionAtZero sP 𝐛 (isIso_modificationFibreAtZeroProjection sP 𝐛 𝐡𝐀)
set_option hygiene false in
local notation "𝐄" => (pullback (modificationProjectionAtInfinity sP 𝐛) i : Scheme.{u})
set_option hygiene false in
local notation "𝐞" => pullback.fst (modificationProjectionAtInfinity sP 𝐛) i ≫ 𝐢∞
set_option hygiene false in
local notation "𝐚" => strictTransformToFibreAtInfinity sP i ≫ 𝐢∞

omit [IsClosedImmersion i] in
/-- **Stacks 0F9J on `[P]_n`**: the class at infinity caps `[P]_n` to `[W_∞ ×_P P]_n`, for
`dim_δ P ≤ n`. -/
theorem gysinAtInfinity_cap_fundamentalChowClass (n : ℤ)
    (hP : schemeDeltaDimension C sP ≤ (n : EInt)) :
    gysinCapAtInfinity C sP 𝐛 𝐡𝐀 (𝟙 P) n (fundamentalChowClass C (𝟙 P ≫ sP) n) =
      fundamentalChowClass C (modificationInfinityBaseChangeOver sP 𝐛 (𝟙 P)) n :=
  gysinCapOfLift_fundamentalChowClass C sP 𝐛 𝐡𝐀 (𝟙 P) n
    ((schemeDeltaDimension_congr C (Category.id_comp sP)).trans_le hP)
    (isEffectiveCartierDivisor_ker_modificationInfinityBaseChange_blowupAtInfinity i.ker sP (𝟙 P))

omit [IsClosedImmersion i] in
/-- **`(i₀)_*[P]_n = (i_∞)_*[W_∞]_n`** in `A_n(W)` for the blowup at infinity, when
`dim_δ P ≤ n`. -/
theorem sectionAtZero_pushforward_fundamentalChowClass (n : ℤ)
    (hP : schemeDeltaDimension C sP ≤ (n : EInt)) :
    properChowPushforward C sP (𝐪 ≫ sP) 𝐢₀ (sectionAtZero_comp_structure C sP 𝐛 𝐡𝐀) n
        (properPushforwardDescends C _ _ _ _ _) (fundamentalChowClass C sP n) =
      properChowPushforward C (𝐢∞ ≫ 𝐪 ≫ sP) (𝐪 ≫ sP) 𝐢∞ rfl n
        (properPushforwardDescends C _ _ _ _ _) (fundamentalChowClass C (𝐢∞ ≫ 𝐪 ≫ sP) n) :=
  (inclusionAtInfinity_pushforward_fundamentalChowClass C sP 𝐛 𝐡𝐀 n hP
    (isEffectiveCartierDivisor_ker_modificationInfinityBaseChange_blowupAtInfinity
      i.ker sP (𝟙 P))).symm

/-- **Specialization of `[P]_n`, integrally**: `(i₀)_*[P]_n = e_*[E]_n + a_*β` in `A_n(W)` for
some `β ∈ A_n(X')`, when `dim_δ P ≤ n`. -/
theorem exists_sectionAtZero_pushforward_eq (n : ℤ)
    (hP : schemeDeltaDimension C sP ≤ (n : EInt)) :
    ∃ β : chowGroup C (𝐚 ≫ 𝐪 ≫ sP) n,
      properChowPushforward C sP (𝐪 ≫ sP) 𝐢₀ (sectionAtZero_comp_structure C sP 𝐛 𝐡𝐀) n
          (properPushforwardDescends C _ _ _ _ _) (fundamentalChowClass C sP n) =
        properChowPushforward C (𝐞 ≫ 𝐪 ≫ sP) (𝐪 ≫ sP) 𝐞 rfl n
            (properPushforwardDescends C _ _ _ _ _) (fundamentalChowClass C (𝐞 ≫ 𝐪 ≫ sP) n) +
          properChowPushforward C (𝐚 ≫ 𝐪 ≫ sP) (𝐪 ≫ sP) 𝐚 rfl n
            (properPushforwardDescends C _ _ _ _ _) β := by
  obtain ⟨β, hβ⟩ := exists_fundamentalChowClass_eq_add C (𝐢∞ ≫ 𝐪 ≫ sP)
    (pullback.fst (modificationProjectionAtInfinity sP 𝐛) i) (𝐞 ≫ 𝐪 ≫ sP)
    (Category.assoc _ _ _).symm (strictTransformToFibreAtInfinity sP i) (𝐚 ≫ 𝐪 ≫ sP)
    (Category.assoc _ _ _).symm (normalConeToFibreAtInfinity i sP)
    (normalConeToExceptionalFibre sP i) (normalConeToExceptionalFibre_fst sP i)
    (range_strictTransformToFibreAtInfinity sP i) n
  refine ⟨β, ?_⟩
  rw [sectionAtZero_pushforward_fundamentalChowClass C sP i n hP, hβ, map_add]
  unfold chowPushforwardOfIsClosedImmersion
  rw [← properChowPushforward_comp_apply C _ _ _ _ _ 𝐞 rfl _ _ rfl n _ _
      (properPushforwardDescends C _ _ _ _ _),
    ← properChowPushforward_comp_apply C _ _ _ _ _ 𝐚 rfl _ _ rfl n _ _
      (properPushforwardDescends C _ _ _ _ _)]

omit [IsClosedImmersion i] in
/-- **The generic points of `W` have `δ = n + 1`** when every irreducible component of `P` has
`δ = n`: they lie over `𝐀¹_P`, which is flat of relative dimension one over `P`. -/
theorem relativeDimension_genericPoint_blowupAtInfinity {n : ℤ}
    (hP : ∀ V : irreducibleComponents P, deltaDimension C sP
      ⟨V, V.2.1, isClosed_of_mem_irreducibleComponents (V : Set P) V.2⟩ = n)
    {ξ : blowupAtInfinity i.ker} (hξ : ξ ∈ genericPoints (blowupAtInfinity i.ker)) :
    relativeDimension C.dimensionFunction (𝐪 ≫ sP) ξ = n + 1 := by
  have hcart := isEffectiveCartierDivisor_ker_modificationInfinityBaseChange_blowupAtInfinity
    i.ker sP (𝟙 P)
  have := flat_modificationAffineChartProjection sP 𝐛 (𝟙 P) 𝐡𝐀
  have hξ' : (inv (pullback.fst 𝐪 (𝟙 P))) ξ ∈
      genericPoints (modificationBaseChange sP 𝐛 (𝟙 P)) :=
    mem_genericPoints_target_of_isOpenImmersion (inv (pullback.fst 𝐪 (𝟙 P))) hξ
  obtain ⟨c, hc⟩ := genericPoints_subset_range_modificationAffineChartι C sP 𝐛 (𝟙 P) hcart hξ'
  have hcgen : c ∈ genericPoints (modificationAffineChart sP 𝐛 (𝟙 P)) :=
    mem_genericPoints_of_isOpenImmersion_apply (modificationAffineChartι sP 𝐛 (𝟙 P))
      (by rw [hc]; exact hξ')
  obtain ⟨V, hV⟩ := exists_irreducibleComponent_map_genericPoint
    (modificationAffineChartProjection sP 𝐛 (𝟙 P)) ⟨closure {c}, hcgen⟩
  have hδ := deltaDimension_irreducibleComponent_eq_add C
    (modificationAffineChartProjection sP 𝐛 (𝟙 P)) sP 1
    (relativeDimension_modificationAffineChartProjection sP 𝐛 (𝟙 P) 𝐡𝐀) ⟨closure {c}, hcgen⟩ V hV
  rw [hP V, deltaDimension_eq_of_isGenericPoint C _ _ c isGenericPoint_closure] at hδ
  have hcomp : modificationAffineChartProjection sP 𝐛 (𝟙 P) ≫ sP =
      modificationAffineChartι sP 𝐛 (𝟙 P) ≫ pullback.fst 𝐪 (𝟙 P) ≫ 𝐪 ≫ sP := by
    have e : pullback.snd 𝐪 (𝟙 P) = pullback.fst 𝐪 (𝟙 P) ≫ 𝐪 := by
      rw [pullback.condition, Category.comp_id]
    dsimp only [modificationAffineChartProjection]
    rw [e]
    simp only [Category.assoc]
  rw [hcomp, relativeDimension_comp_isOpenImmersion, hc, relativeDimension_comp_isOpenImmersion,
    ← Scheme.Hom.comp_apply, IsIso.inv_hom_id] at hδ
  have h2 : relativeDimension C.dimensionFunction (𝐪 ≫ sP) ξ = n + ((1 : ℕ) : ℤ) := hδ
  rw [h2, Nat.cast_one]

omit [IsClosedImmersion i] in
/-- **A point of coheight one in `W` has `δ = n`** when every irreducible component of `P` has
`δ = n`: it is an immediate specialization of a generic point of `W`, which has `δ = n + 1`. -/
theorem relativeDimension_of_coheight_eq_one {n : ℤ}
    (hP : ∀ V : irreducibleComponents P, deltaDimension C sP
      ⟨V, V.2.1, isClosed_of_mem_irreducibleComponents (V : Set P) V.2⟩ = n)
    {y : blowupAtInfinity i.ker} (hy : Order.coheight y = 1) :
    relativeDimension C.dimensionFunction (𝐪 ≫ sP) y = n := by
  obtain ⟨ξ, hyξ⟩ := not_isMax_iff.mp (Order.coheight_ne_zero.mp (by rw [hy]; exact one_ne_zero))
  have hξ0 : Order.coheight ξ = 0 := by
    have h := Order.coheight_add_one_le hyξ
    rw [hy] at h
    exact enat_eq_zero_of_add_one_le_one h
  have hξmax : IsMax ξ := Order.coheight_eq_zero.mp hξ0
  have hgen : ξ ∈ genericPoints (blowupAtInfinity i.ker) :=
    TopologicalSpace.mem_genericPoints_of_forall_specializes_eq fun z hz =>
      (hz.antisymm (hξmax hz)).eq
  -- in the specialization order `y < ξ` means `ξ ⤳ y`, `ξ ≠ y`
  have himm : TopologicalSpace.IsImmediateSpecialization ξ y := by
    refine ⟨hyξ.1, fun h => hyξ.2 (h ▸ le_rfl), fun z hξz hzy => ?_⟩
    by_contra hne
    push Not at hne
    have h1 : y < z := lt_iff_le_not_ge.mpr ⟨hzy, fun h => hne.2 (hzy.antisymm h).eq⟩
    have h2 : z < ξ := lt_iff_le_not_ge.mpr ⟨hξz, fun h => hne.1 (hξz.antisymm h).eq.symm⟩
    have h3 := Order.coheight_add_one_le h1
    rw [hy] at h3
    have hz0 := enat_eq_zero_of_add_one_le_one h3
    exact (Order.coheight_ne_zero.mpr (not_isMax_iff.mpr ⟨ξ, h2⟩)) hz0
  have hstep := (deltaDimensionFunction C (𝐪 ≫ sP)).step_immediate himm
  rw [deltaDimensionFunction_apply, deltaDimensionFunction_apply,
    relativeDimension_genericPoint_blowupAtInfinity C sP i hP hgen] at hstep
  omega

/-- **The generic points of the components of `E = W_∞ ×_P X` have coheight one in `W`**: `E` is
the exceptional divisor, an effective Cartier divisor on `W`, so the local rings of `W` there have
dimension one. -/
theorem coheight_exceptional_eq_one {ζ : 𝐄} (hζ : ζ ∈ genericPoints 𝐄) :
    Order.coheight ((𝐞) ζ) = 1 := by
  have : IsLocallyNoetherian (blowupAtInfinity i.ker) :=
    LocallyOfFiniteType.isLocallyNoetherian (𝐪 ≫ sP)
  have hsq := isPullback_exceptionalDivisorToFibreAtInfinity sP i
  have hgen : hsq.isoPullback.inv ζ ∈ genericPoints (exceptionalIdealAtInfinity i.ker).subscheme :=
    mem_genericPoints_target_of_isOpenImmersion hsq.isoPullback.inv hζ
  have hK := ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor
    (exceptionalIdealAtInfinity i.ker) (isEffectiveCartierDivisor_exceptionalIdealAtInfinity i.ker)
    (hsq.isoPullback.inv ζ) ⟨⟨closure {hsq.isoPullback.inv ζ}, hgen⟩, isGenericPoint_closure⟩
  have h1 : hsq.isoPullback.inv ≫ (exceptionalIdealAtInfinity i.ker).subschemeι = 𝐞 := by
    rw [← exceptionalDivisorToFibreAtInfinity_inclusion sP i, ← Category.assoc,
      IsPullback.isoPullback_inv_fst]
  rw [← Scheme.Hom.comp_apply, h1, ringKrullDim_stalk_eq_coheight] at hK
  exact_mod_cast hK

/-- **`E` is pure of dimension `n`**: every irreducible component of `E = W_∞ ×_P X` has
`δ = n` when every irreducible component of `P` has `δ = n`. -/
theorem deltaDimension_exceptional {n : ℤ}
    (hP : ∀ V : irreducibleComponents P, deltaDimension C sP
      ⟨V, V.2.1, isClosed_of_mem_irreducibleComponents (V : Set P) V.2⟩ = n)
    (V : irreducibleComponents 𝐄) :
    deltaDimension C (𝐞 ≫ 𝐪 ≫ sP) ⟨V, V.2.1, isClosed_of_mem_irreducibleComponents _ V.2⟩ = n := by
  have hgp := V.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ V.2)
  rw [deltaDimension_eq_of_isGenericPoint C _ _ _ hgp, relativeDimension_comp_closedImmersion]
  refine relativeDimension_of_coheight_eq_one C sP i hP (coheight_exceptional_eq_one C sP i ?_)
  change closure {_} ∈ irreducibleComponents _
  rw [hgp.def]
  exact V.2

end Blowup

section Field

variable (k : Type u) [Field k] {X P : Scheme.{u}} (sP : P ⟶ Spec (.of k)) [IsSmoothFT k sP]
  (i : X ⟶ P) [IsClosedImmersion i]

set_option hygiene false in
local notation "𝐛" => blowupAtInfinityToProjectiveLineProduct (Scheme.Hom.ker i) sP
set_option hygiene false in
local notation "𝐪" => modificationProjection sP 𝐛
set_option hygiene false in
local notation "𝐞" =>
  pullback.fst (modificationProjectionAtInfinity sP 𝐛) i ≫ modificationInclusionAtInfinity sP 𝐛

/-- **`[E] = 1 ⊗ [E]_n` in `CH_*(E) ⊗ ℚ`** for `E = W_∞ ×_P X`, when `P` is pure of dimension
`n`. -/
theorem rationalFundamentalClass_exceptional {n : ℕ} (hP : RelativeDimension sP n) :
    haveI := isNoetherian_of_quasiCompact_fieldChowSituation k (𝐞 ≫ 𝐪 ≫ sP)
    rationalFundamentalClass (fieldChowSituation k) (𝐞 ≫ 𝐪 ≫ sP) =
      DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) (𝐞 ≫ 𝐪 ≫ sP) j) n
        ((1 : ℚ) ⊗ₜ fundamentalChowClass (fieldChowSituation k) (𝐞 ≫ 𝐪 ≫ sP) n) :=
  haveI := isNoetherian_of_quasiCompact_fieldChowSituation k (𝐞 ≫ 𝐪 ≫ sP)
  rationalFundamentalClass_eq_of_deltaDimension (fieldChowSituation k) (𝐞 ≫ 𝐪 ≫ sP)
    (deltaDimension_exceptional (fieldChowSituation k) sP i
      (Stacks.WeilCohomology.deltaDimension_irreducibleComponent_of_relativeDimension k sP n hP))

end Field

end GRR.Specialization

namespace GRR

variable (k : Type u) [Field k] {X P : Scheme.{u}} (sP : P ⟶ Spec (.of k)) [IsSmoothFT k sP]
  (i : X ⟶ P) [IsClosedImmersion i]

set_option hygiene false in
local notation "𝐛" => blowupAtInfinityToProjectiveLineProduct (Scheme.Hom.ker i) sP
set_option hygiene false in
local notation "𝐪" => modificationProjection sP 𝐛
set_option hygiene false in
local notation "𝐢∞" => modificationInclusionAtInfinity sP 𝐛
set_option hygiene false in
local notation "𝐡𝐀" =>
  isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct (Scheme.Hom.ker i) sP
set_option hygiene false in
local notation "𝐞" => pullback.fst (modificationProjectionAtInfinity sP 𝐛) i ≫ 𝐢∞
set_option hygiene false in
local notation "𝐚" => strictTransformToFibreAtInfinity sP i ≫ 𝐢∞

/-- **Specialization of the fundamental class in the deformation to the normal cone** (item C6
of `notes/E_plan.md`). Let `i : X ⟶ P` be a closed immersion with `P` smooth, separated and of
finite type over `k` and of pure dimension `n`. Let `W` be the blowup of `𝐏¹_P` in `∞(X)`, with
`q : W ⟶ P`, the section at zero `i₀ : P ⟶ W`, the exceptional divisor
`e : E = W_∞ ×_P X ⟶ W_∞ ⟶ W` and the strict transform `a : X' ⟶ W_∞ ⟶ W`. Then there is
`β ∈ CH_*(X') ⊗ ℚ` with

  `(i₀)_*[P] = e_*[E] + a_*β`   in `CH_*(W) ⊗ ℚ`.

In Lean: `W = blowupAtInfinity i.ker`, `q = modificationProjection sP b`,
`i₀ = modificationSectionAtZero sP b _`, `e = pullback.fst (modificationProjectionAtInfinity sP b)
i ≫ modificationInclusionAtInfinity sP b` and `a = strictTransformToFibreAtInfinity sP i ≫
modificationInclusionAtInfinity sP b`, for `b = blowupAtInfinityToProjectiveLineProduct i.ker sP`
(the `GRR.DeformationGeom` abbreviations `sectionAtZero`, `exceptionalInclusion`,
`strictTransformInclusion`, `proj`). -/
theorem exists_specialization_fundamentalClass {n : ℕ} (hP : RelativeDimension sP n) :
    haveI := isNoetherian_of_quasiCompact_fieldChowSituation k (𝐞 ≫ 𝐪 ≫ sP)
    ∃ β : CHQ k (𝐚 ≫ 𝐪 ≫ sP),
      rationalProperChowPushforward (fieldChowSituation k) sP (𝐪 ≫ sP)
          (Specialization.sectionAtZero_comp_structure (fieldChowSituation k) sP 𝐛 𝐡𝐀)
          (GRR.fundamentalClass k sP) =
        rationalProperChowPushforward (fieldChowSituation k) (𝐞 ≫ 𝐪 ≫ sP) (𝐪 ≫ sP) (f := 𝐞) rfl
            (rationalFundamentalClass (fieldChowSituation k) (𝐞 ≫ 𝐪 ≫ sP)) +
          rationalProperChowPushforward (fieldChowSituation k) (𝐚 ≫ 𝐪 ≫ sP) (𝐪 ≫ sP) (f := 𝐚) rfl
            β := by
  have := isNoetherian_of_quasiCompact_fieldChowSituation k (𝐞 ≫ 𝐪 ≫ sP)
  have := isNoetherian k sP
  have hPδ :=
    Stacks.WeilCohomology.deltaDimension_irreducibleComponent_of_relativeDimension k sP n hP
  have hPdim : schemeDeltaDimension (fieldChowSituation k) sP ≤ ((n : ℤ) : EInt) :=
    Stacks.WeilCohomology.schemeDeltaDimension_le_of_forall_irreducibleComponent
      (C := fieldChowSituation k) sP hPδ
  obtain ⟨β, hβ⟩ :=
    Specialization.exists_sectionAtZero_pushforward_eq (fieldChowSituation k) sP i n hPdim
  refine ⟨DirectSum.of (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) (𝐚 ≫ 𝐪 ≫ sP) j)
    (n : ℤ) ((1 : ℚ) ⊗ₜ β), ?_⟩
  rw [GRR.fundamentalClass,
    Specialization.rationalFundamentalClass_eq_of_deltaDimension (fieldChowSituation k) sP hPδ,
    Specialization.rationalFundamentalClass_exceptional k sP i hP,
    rationalProperChowPushforward_of_tmul, rationalProperChowPushforward_of_tmul,
    rationalProperChowPushforward_of_tmul, hβ, TensorProduct.tmul_add, map_add]

end GRR
