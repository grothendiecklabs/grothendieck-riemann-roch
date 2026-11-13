import Mathlib
import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroup
import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.UniformVanishing
import StacksFrontier.AlgebraicGeometry.HigherDirectImage.DimensionShifting
import StacksFrontier.AlgebraicGeometry.Modules.DerivedAffineSystemKZero
import StacksFrontier.AlgebraicGeometry.ClosedImmersionRelativeLeray.Basic
import StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.SupportedCoherentKGroup
import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic

/-!
# The pushforward `f_!` on Grothendieck groups of coherent sheaves

For a proper morphism `f : X ⟶ Y` to a quasi-compact locally Noetherian scheme, the higher direct
images `R^i f_* F` of a coherent module are coherent (Stacks 02O5) and vanish for `i` beyond a
bound independent of `F` (Stacks 01XJ). This file defines

  `f_! : K'₀(X) ⟶ K'₀(Y)`,  `f_! [F] = ∑_i (-1)^i [R^i f_* F]`,

as `GRR.pushforwardK f`, proves that it is well defined (additive on short exact sequences, by the
long exact sequence of higher direct images), that `i_! [F] = [i_* F]` for a closed immersion `i`,
and that `(i ≫ g)_! = g_! ∘ i_!` for a closed immersion `i` followed by a proper morphism `g`.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace GRR

attribute [local instance 10000] HasDerivedCategory.standard

variable {X Y : Scheme.{u}}

/-- The higher direct image `R^i f_* F` of a module (Stacks 01XJ): the value of the `i`-th right
derived functor of `f_*`. -/
noncomputable def higherDirectImage (f : X ⟶ Y) (F : X.Modules) (i : ℕ) : Y.Modules :=
  ((Scheme.Modules.pushforward f).rightDerivedPlus (i : ℤ)).obj F

/-! ### The Euler characteristic of a cohomological long exact sequence -/

section LongExactSequence

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]

/-- For an exact sequence `X₁ → X₂ → X₃`, `[X₂] = [im f] + [im g]` in `K₀(𝒜)`. -/
theorem kZero_mk_eq_mk_image_add_mk_image (S : ShortComplex 𝒜) (hS : S.Exact) :
    KZero.mk 𝒜 S.X₂ = KZero.mk 𝒜 (Abelian.image S.f) + KZero.mk 𝒜 (Abelian.image S.g) := by
  rw [KZero.mk_eq_kernel_add_image S.g, ← KZero.mk_image_eq_mk_kernel _ hS]

/-- **The Euler characteristic of a cohomological long exact sequence vanishes.** For an exact
sequence `0 → A₀ → B₀ → C₀ → A₁ → B₁ → C₁ → A₂ → ⋯` in an abelian category with `A_N = 0`,
`∑_{j < N} (-1)ʲ ([Aⱼ] - [Bⱼ] + [Cⱼ]) = 0` in `K₀(𝒜)`. -/
theorem kZero_sum_range_neg_one_pow_zsmul_eq_zero {A B C : ℕ → 𝒜} (a : ∀ j, A j ⟶ B j)
    (b : ∀ j, B j ⟶ C j) (d : ∀ j, C j ⟶ A (j + 1)) (hab : ∀ j, a j ≫ b j = 0)
    (hbd : ∀ j, b j ≫ d j = 0) (hda : ∀ j, d j ≫ a (j + 1) = 0)
    (h₂ : ∀ j, (ShortComplex.mk _ _ (hab j)).Exact)
    (h₃ : ∀ j, (ShortComplex.mk _ _ (hbd j)).Exact)
    (h₁ : ∀ j, (ShortComplex.mk _ _ (hda j)).Exact) [Mono (a 0)] (N : ℕ)
    (hN : Limits.IsZero (A N)) :
    ∑ j ∈ Finset.range N, (-1 : ℤ) ^ j •
      (KZero.mk 𝒜 (A j) - KZero.mk 𝒜 (B j) + KZero.mk 𝒜 (C j)) = 0 := by
  obtain _ | M := N
  · simp
  have hA : KZero.mk 𝒜 (A 0) = KZero.mk 𝒜 (Abelian.image (a 0)) := by
    rw [KZero.mk_eq_kernel_add_image (a 0),
      KZero.mk_eq_zero_of_isZero (Limits.isZero_kernel_of_mono _), zero_add]
  rw [KZero.sum_range_neg_one_pow_zsmul_telescope _ (fun j => KZero.mk 𝒜 (Abelian.image (d j)))
    (by
      rw [hA, kZero_mk_eq_mk_image_add_mk_image _ (h₂ 0),
        kZero_mk_eq_mk_image_add_mk_image _ (h₃ 0)]
      abel)
    (fun j => by
      rw [kZero_mk_eq_mk_image_add_mk_image _ (h₁ j),
        kZero_mk_eq_mk_image_add_mk_image _ (h₂ (j + 1)),
        kZero_mk_eq_mk_image_add_mk_image _ (h₃ (j + 1))]
      abel) M,
    KZero.mk_eq_zero_of_isZero (hN.of_mono (Abelian.image.ι (d M))), smul_zero]

end LongExactSequence

/-! ### Higher direct images as a δ-functor -/

/-- The higher direct images `R^n f_*`, in the indexing of `higherDirectImage`, as a cohomological
δ-functor: the δ-functor of Mathlib's right derived functors of `f_*`, transported along the
comparison of the two indexings. -/
noncomputable def higherDirectImageDelta (f : X ⟶ Y) : DeltaFunctor X.Modules Y.Modules :=
  Stacks.DerivedIndexing.deltaFunctorOfNatIso
    (Stacks.AlgebraicGeometry.HigherDirectImage.pushforwardDeltaFunctor f)
    (fun n => (Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ))
    (fun n => Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) n)

theorem higherDirectImageDelta_functor_obj (f : X ⟶ Y) (F : X.Modules) (n : ℕ) :
    ((higherDirectImageDelta f).functor n).obj F = higherDirectImage f F n :=
  rfl

/-! ### Coherent higher direct images -/

/-- The inclusion of coherent modules into all modules. -/
abbrev coherentInclusion (X : Scheme.{u}) :=
  (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι

/-- A coherent module is quasi-coherent. -/
theorem isQuasicoherent_obj {X : Scheme.{u}}
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) : F.obj.IsQuasicoherent :=
  haveI : F.obj.IsCoherent := CoherentAbelian.isCoherent_of_stacksIsCoherent F.property
  _root_.isQuasicoherent_of_isCoherent F.obj

attribute [local instance] isQuasicoherent_obj

/-- The higher direct image `R^i f_* F` of a coherent module along a proper morphism to a locally
Noetherian scheme, as a coherent module (Stacks 02O5). -/
noncomputable def higherDirectImageCoh (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y]
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) (i : ℕ) :
    Stacks.SheafOfModules.CoherentModules Y.ringCatSheaf :=
  ⟨higherDirectImage f F.obj i, CoherentAbelian.stacksIsCoherent_of_isCoherent
    (ProperCoherenceWitness.higherDirectImageIsCoherent X Y f inferInstance inferInstance F.obj
      (CoherentAbelian.isCoherent_of_stacksIsCoherent F.property) i)⟩

theorem higherDirectImageCoh_obj (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y]
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) (i : ℕ) :
    (higherDirectImageCoh f F i).obj = higherDirectImage f F.obj i := by
  rfl

/-- `R^i f_* F` vanishes as a coherent module exactly when it vanishes as a module. -/
theorem isZero_higherDirectImageCoh_iff (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y]
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) (i : ℕ) :
    Limits.IsZero (higherDirectImageCoh f F i) ↔ Limits.IsZero (higherDirectImage f F.obj i) :=
  ⟨fun h => (coherentInclusion Y).map_isZero h,
    fun h => Limits.IsZero.of_full_of_faithful_of_isZero (coherentInclusion Y) _ h⟩

/-- If `R^i f_* F ≅ G` for a coherent `G`, then `[R^i f_* F] = [G]` in `K'₀(Y)`. -/
theorem mk_higherDirectImageCoh_eq_of_iso (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y]
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) (i : ℕ)
    (G : Stacks.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (e : higherDirectImage f F.obj i ≅ G.obj) :
    KZero.mk _ (higherDirectImageCoh f F i) = KZero.mk _ G :=
  KZero.mk_eq_of_iso (ObjectProperty.isoMk (Stacks.SheafOfModules.coherentModules Y.ringCatSheaf) e)

/-- A bound beyond which all higher direct images of quasi-coherent modules along `f` vanish. -/
noncomputable def cohomologicalBound (f : X ⟶ Y) [IsProper f] [CompactSpace Y] : ℕ :=
  (Stacks.AlgebraicGeometry.HigherDirectImageQcoh.exists_isZero_rightDerivedNat_pushforward
    f).choose

theorem isZero_higherDirectImage_of_cohomologicalBound_le (f : X ⟶ Y) [IsProper f] [CompactSpace Y]
    (F : X.Modules) [F.IsQuasicoherent] (i : ℕ) (hi : cohomologicalBound f ≤ i) :
    Limits.IsZero (higherDirectImage f F i) := by
  exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff (Scheme.Modules.pushforward f) i F).1
    ((Stacks.AlgebraicGeometry.HigherDirectImageQcoh.exists_isZero_rightDerivedNat_pushforward
      f).choose_spec F inferInstance i hi)

/-! ### Additivity along short exact sequences -/

/-- **The long exact sequence of higher direct images in `K'₀(Y)`.** For a short exact sequence
`0 → F₁ → F₂ → F₃ → 0` of coherent modules and `N` with `R^N f_* F₁ = 0`,
`∑_{j < N} (-1)ʲ ([R^j f_* F₁] - [R^j f_* F₂] + [R^j f_* F₃]) = 0`. -/
theorem sum_range_higherDirectImageCoh_eq_zero (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y]
    {S : ShortComplex (Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)} (hS : S.ShortExact)
    (N : ℕ) (hN : Limits.IsZero (higherDirectImage f S.X₁.obj N)) :
    ∑ j ∈ Finset.range N, (-1 : ℤ) ^ j •
      (KZero.mk _ (higherDirectImageCoh f S.X₁ j) - KZero.mk _ (higherDirectImageCoh f S.X₂ j) +
        KZero.mk _ (higherDirectImageCoh f S.X₃ j)) = 0 := by
  have : Limits.PreservesFiniteLimits (coherentInclusion X) :=
    ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass _
  have : Limits.PreservesFiniteColimits (coherentInclusion X) :=
    ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass _
  have hS' : (S.map (coherentInclusion X)).ShortExact := hS.map_of_exact _
  let D := higherDirectImageDelta f
  let a : ∀ j, higherDirectImageCoh f S.X₁ j ⟶ higherDirectImageCoh f S.X₂ j :=
    fun j => ObjectProperty.homMk ((D.functor j).map (S.map (coherentInclusion X)).f)
  let b : ∀ j, higherDirectImageCoh f S.X₂ j ⟶ higherDirectImageCoh f S.X₃ j :=
    fun j => ObjectProperty.homMk ((D.functor j).map (S.map (coherentInclusion X)).g)
  let d : ∀ j, higherDirectImageCoh f S.X₃ j ⟶ higherDirectImageCoh f S.X₁ (j + 1) :=
    fun j => ObjectProperty.homMk (D.δ hS' j)
  have hab : ∀ j, a j ≫ b j = 0 := fun j => (coherentInclusion Y).map_injective (by
    rw [Functor.map_comp, Functor.map_zero]
    exact D.map_f_comp_map_g j)
  have hbd : ∀ j, b j ≫ d j = 0 := fun j => (coherentInclusion Y).map_injective (by
    rw [Functor.map_comp, Functor.map_zero]
    exact D.map_g_δ hS' j)
  have hda : ∀ j, d j ≫ a (j + 1) = 0 := fun j => (coherentInclusion Y).map_injective (by
    rw [Functor.map_comp, Functor.map_zero]
    exact D.δ_map_f hS' j)
  have : Mono (a 0) := (coherentInclusion Y).mono_of_mono_map (D.mono_map_f hS')
  exact kZero_sum_range_neg_one_pow_zsmul_eq_zero a b d hab hbd hda
    (fun j => (coherentInclusion Y).reflects_exact_of_faithful _ (D.exact_map hS' j))
    (fun j => (coherentInclusion Y).reflects_exact_of_faithful _ (D.exact_δ₁ hS' j))
    (fun j => (coherentInclusion Y).reflects_exact_of_faithful _ (D.exact_δ₂ hS' j)) N
    ((isZero_higherDirectImageCoh_iff f S.X₁ N).2 hN)

/-- The alternating sum `∑_{i < N} (-1)^i [R^i f_* F]` is additive along short exact sequences of
coherent modules. -/
theorem sum_range_higherDirectImageCoh_add (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y]
    [CompactSpace Y]
    {S : ShortComplex (Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)} (hS : S.ShortExact) :
    ∑ i ∈ Finset.range (cohomologicalBound f),
        ((-1 : ℤ) ^ i) • KZero.mk _ (higherDirectImageCoh f S.X₂ i) =
      ∑ i ∈ Finset.range (cohomologicalBound f),
          ((-1 : ℤ) ^ i) • KZero.mk _ (higherDirectImageCoh f S.X₁ i) +
        ∑ i ∈ Finset.range (cohomologicalBound f),
          ((-1 : ℤ) ^ i) • KZero.mk _ (higherDirectImageCoh f S.X₃ i) := by
  have key := sum_range_higherDirectImageCoh_eq_zero f hS (cohomologicalBound f)
    (isZero_higherDirectImage_of_cohomologicalBound_le f S.X₁.obj _ le_rfl)
  simp only [smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] at key
  rw [← sub_eq_zero, ← neg_eq_zero, ← key]
  abel

/-! ### The pushforward -/

/-- **The pushforward `f_! : K'₀(X) ⟶ K'₀(Y)`** of a proper morphism to a quasi-compact locally
Noetherian scheme: `f_! [F] = ∑_i (-1)^i [R^i f_* F]`. -/
noncomputable def pushforwardK (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y] [CompactSpace Y] :
    CoherentKZero X →+ CoherentKZero Y :=
  KZero.lift (fun F => ∑ i ∈ Finset.range (cohomologicalBound f),
      ((-1 : ℤ) ^ i) • KZero.mk _ (higherDirectImageCoh f F i))
    fun _ hS => sum_range_higherDirectImageCoh_add f hS

/-- `f_! [F] = ∑_{i < N} (-1)^i [R^i f_* F]`, for the uniform bound `N`. -/
theorem pushforwardK_mk (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y] [CompactSpace Y]
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) :
    pushforwardK f (KZero.mk _ F) =
      ∑ i ∈ Finset.range (cohomologicalBound f),
        ((-1 : ℤ) ^ i) • KZero.mk _ (higherDirectImageCoh f F i) := by
  exact KZero.lift_mk _ _ F

/-- Terms of the alternating sum beyond a vanishing bound contribute nothing. -/
theorem sum_range_higherDirectImageCoh_eq_of_le (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y]
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) {N M : ℕ} (hNM : N ≤ M)
    (hN : ∀ i, N ≤ i → Limits.IsZero (higherDirectImage f F.obj i)) :
    ∑ i ∈ Finset.range M, ((-1 : ℤ) ^ i) • KZero.mk _ (higherDirectImageCoh f F i) =
      ∑ i ∈ Finset.range N, ((-1 : ℤ) ^ i) • KZero.mk _ (higherDirectImageCoh f F i) := by
  refine (Finset.sum_subset (Finset.range_subset_range.2 hNM) fun i _ hi => ?_).symm
  rw [Finset.mem_range, not_lt] at hi
  rw [KZero.mk_eq_zero_of_isZero ((isZero_higherDirectImageCoh_iff f F i).2 (hN i hi)),
    smul_zero]

/-- `f_! [F] = ∑_{i < N} (-1)^i [R^i f_* F]` for any `N` beyond which the `R^i f_* F` vanish. -/
theorem pushforwardK_mk_of_isZero (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y] [CompactSpace Y]
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) (N : ℕ)
    (hN : ∀ i, N ≤ i → Limits.IsZero (higherDirectImage f F.obj i)) :
    pushforwardK f (KZero.mk _ F) =
      ∑ i ∈ Finset.range N, ((-1 : ℤ) ^ i) • KZero.mk _ (higherDirectImageCoh f F i) := by
  rw [pushforwardK_mk]
  exact (sum_range_higherDirectImageCoh_eq_of_le f F (le_max_right N (cohomologicalBound f))
    fun i hi => isZero_higherDirectImage_of_cohomologicalBound_le f F.obj i hi).symm.trans
    (sum_range_higherDirectImageCoh_eq_of_le f F (le_max_left N (cohomologicalBound f)) hN)

/-- `f_! [F] = ∑_{i < N} (-1)^i [G_i]` when `R^i f_* F ≅ G_i` for `i < N` and `R^i f_* F = 0`
for `i ≥ N`. -/
theorem pushforwardK_mk_eq_sum_of_iso (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y]
    [CompactSpace Y] (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) (N : ℕ)
    (hN : ∀ i, N ≤ i → Limits.IsZero (higherDirectImage f F.obj i))
    (G : ℕ → Stacks.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (e : ∀ i, i < N → Nonempty (higherDirectImage f F.obj i ≅ (G i).obj)) :
    pushforwardK f (KZero.mk _ F) = ∑ i ∈ Finset.range N, ((-1 : ℤ) ^ i) • KZero.mk _ (G i) := by
  rw [pushforwardK_mk_of_isZero f F N hN]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [mk_higherDirectImageCoh_eq_of_iso f F i (G i) (e i (Finset.mem_range.1 hi)).some]

/-! ### Closed immersions -/

/-- For a closed immersion `i`, `i_! [F] = [i_* F]`. -/
theorem pushforwardK_mk_of_isClosedImmersion {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [IsLocallyNoetherian X] [CompactSpace X]
    (F : Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf) :
    pushforwardK i (KZero.mk _ F) = KZero.mk _ ((pushforwardCoherentModules i).obj F) := by
  rw [pushforwardK_mk_of_isZero i F 1 fun n hn =>
    Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isZero_higherDirectImage_of_isFinite i
      F.obj (n : ℤ) (by omega)]
  rw [Finset.sum_range_one, pow_zero, one_smul]
  exact mk_higherDirectImageCoh_eq_of_iso i F 0 _
    (Stacks.AlgebraicGeometry.HigherDirectImage.higherDirectImageZeroIso i F.obj)

/-- `R^n (i ≫ g)_* F ≅ R^n g_* (i_* F)` for a closed immersion `i`. -/
noncomputable def higherDirectImageCompIso {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (g : X ⟶ Y) (F : Z.Modules) (n : ℕ) :
    higherDirectImage (i ≫ g) F n ≅
      higherDirectImage g ((Scheme.Modules.pushforward i).obj F) n :=
  ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward (i ≫ g)) n).app F).symm ≪≫
    (Stacks.AlgebraicGeometry.ClosedImmersionRelativeLeray.rightDerivedPushforwardCompIso
      i g n).app F ≪≫
    (Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward g) n).app
      ((Scheme.Modules.pushforward i).obj F)

/-- **`(i ≫ g)_! = g_! ∘ i_!`** for a closed immersion `i` followed by a proper morphism `g`. -/
theorem pushforwardK_comp_of_isClosedImmersion {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (g : X ⟶ Y) [IsProper g] [IsLocallyNoetherian X] [CompactSpace X] [IsLocallyNoetherian Y]
    [CompactSpace Y] :
    pushforwardK (i ≫ g) = (pushforwardK g).comp (pushforwardK i) := by
  refine KZero.hom_ext fun F => ?_
  rw [AddMonoidHom.comp_apply, pushforwardK_mk_of_isClosedImmersion i F,
    pushforwardK_mk g ((pushforwardCoherentModules i).obj F),
    pushforwardK_mk_of_isZero (i ≫ g) F (cohomologicalBound g) fun n hn =>
      (isZero_higherDirectImage_of_cohomologicalBound_le g
        ((pushforwardCoherentModules i).obj F).obj n hn).of_iso
        (higherDirectImageCompIso i g F.obj n)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mk_higherDirectImageCoh_eq_of_iso (i ≫ g) F n
    (higherDirectImageCoh g ((pushforwardCoherentModules i).obj F) n)
    (higherDirectImageCompIso i g F.obj n)]

end GRR
