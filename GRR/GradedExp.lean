import Mathlib
import GRR.ToddSeries

/-!
# Exponentials and power series in a graded-complete `ℚ`-algebra

`GRR.GradedComplete R` records that the elements of a ring `R` are the families `(a_n)_{n ≥ 0}` of
components `a_n ∈ M n`, multiplied by a Cauchy product (the degree-`n` component of a product
only sees the components of degree `≤ n` of the factors, and a product of homogeneous elements of
degrees `i`, `j` is homogeneous of degree `i + j`). The ring `∏_p A^p(X) ⊗ ℚ` is of this kind.

In such a ring this file defines the exponential `gexp x = ∑ x^j / j!` of an element without
constant term, the value `ev h F = ∑ F_j h^j` of a power series `F ∈ ℚ⟦X⟧` at such an element, and
the Todd operation `toddOf c = gexp (∑_n n! · ℓ_n · c_n)`, where `log (x / (1 - e^{-x})) = ∑ ℓ_n x^n`.
It proves `gexp (x + y) = gexp x * gexp y` for commuting `x`, `y`, that `ev h` is a ring map, and
`toddOf (e^h) = h / (1 - e^{-h})` for `h` homogeneous of degree one.
-/

open PowerSeries Finset

universe u v

namespace GRR

/-- A ring `R` whose elements are the families `(a_n)_{n ≥ 0}` with `a_n ∈ M n`, with a
`ℚ`-bilinear Cauchy product: the degree-`n` component of `a * b` only depends on the components
of degree `≤ n` of `a` and `b`, and a product of homogeneous elements of degrees `i` and `j` is
homogeneous of degree `i + j`. -/
structure GradedComplete (R : Type u) [Ring R] [Module ℚ R] where
  /-- The group of degree-`n` components. -/
  M : ℕ → Type v
  [addCommGroup : ∀ n, AddCommGroup (M n)]
  [module : ∀ n, Module ℚ (M n)]
  /-- The degree-`n` component of an element. -/
  comp : ∀ n, R →ₗ[ℚ] M n
  /-- The element with given components. -/
  ofComps : (∀ n, M n) → R
  comp_ofComps : ∀ (f : ∀ n, M n) (n : ℕ), comp n (ofComps f) = f n
  ext : ∀ a b : R, (∀ n, comp n a = comp n b) → a = b
  smul_mul : ∀ (q : ℚ) (a b : R), (q • a) * b = q • (a * b)
  mul_smul : ∀ (q : ℚ) (a b : R), a * (q • b) = q • (a * b)
  mul_congr : ∀ (n : ℕ) (a a' b b' : R), (∀ p ≤ n, comp p a = comp p a') →
    (∀ p ≤ n, comp p b = comp p b') → comp n (a * b) = comp n (a' * b')
  mul_hom : ∀ (i j : ℕ) (a b : R), (∀ p, p ≠ i → comp p a = 0) → (∀ p, p ≠ j → comp p b = 0) →
    ∀ p, p ≠ i + j → comp p (a * b) = 0
  comp_one : ∀ p, p ≠ 0 → comp p (1 : R) = 0

attribute [instance] GradedComplete.addCommGroup GradedComplete.module

namespace GradedComplete

variable {R : Type u} [Ring R] [Module ℚ R] (G : GRR.GradedComplete.{u, v} R)

/-- `a` has no component of degree `< n`. -/
def VanishBelow (n : ℕ) (a : R) : Prop := ∀ p, p < n → G.comp p a = 0

/-- `a` is homogeneous of degree `n`: its components of every other degree vanish. -/
def IsHom (n : ℕ) (a : R) : Prop := ∀ p, p ≠ n → G.comp p a = 0

/-! ### Homogeneous pieces and the Cauchy product formula -/

/-- The homogeneous element of degree `p` with degree-`p` component `m`. -/
noncomputable def single (p : ℕ) (m : G.M p) : R := G.ofComps (Pi.single p m)

theorem comp_single (p : ℕ) (m : G.M p) (n : ℕ) :
    G.comp n (G.single p m) = Pi.single (M := G.M) p m n :=
  G.comp_ofComps _ n

theorem comp_single_self (p : ℕ) (m : G.M p) : G.comp p (G.single p m) = m := by
  rw [comp_single, Pi.single_eq_same]

theorem comp_single_of_ne {p n : ℕ} (m : G.M p) (h : n ≠ p) : G.comp n (G.single p m) = 0 := by
  rw [comp_single, Pi.single_eq_of_ne h]

theorem isHom_single (p : ℕ) (m : G.M p) : G.IsHom p (G.single p m) :=
  fun _ hn ↦ G.comp_single_of_ne m hn

theorem single_zero (p : ℕ) : G.single p (0 : G.M p) = 0 :=
  G.ext _ _ fun n ↦ by rw [comp_single, Pi.single_zero, Pi.zero_apply, map_zero]

theorem single_smul (p : ℕ) (q : ℚ) (m : G.M p) : G.single p (q • m) = q • G.single p m :=
  G.ext _ _ fun n ↦ by rw [comp_single, map_smul, comp_single, Pi.single_smul, Pi.smul_apply]

/-- An element agrees up to degree `n` with the sum of its homogeneous pieces of degree `≤ n`. -/
theorem comp_sum_single (a : R) {n p : ℕ} (hp : p ≤ n) :
    G.comp p (∑ q ∈ range (n + 1), G.single q (G.comp q a)) = G.comp p a := by
  rw [map_sum]
  simp only [comp_single]
  rw [Finset.sum_pi_single, ite_eq_left (Finset.mem_range.mpr (by omega))]

/-- **The Cauchy product formula**: the degree-`n` component of `a * b` is the sum over `p ≤ n`
of the degree-`n` components of the products of the pieces of degrees `p` and `n - p`. -/
theorem comp_mul (n : ℕ) (a b : R) :
    G.comp n (a * b) = ∑ p ∈ range (n + 1),
      G.comp n (G.single p (G.comp p a) * G.single (n - p) (G.comp (n - p) b)) := by
  rw [G.mul_congr n a (∑ p ∈ range (n + 1), G.single p (G.comp p a)) b
      (∑ q ∈ range (n + 1), G.single q (G.comp q b))
      (fun p hp ↦ (G.comp_sum_single a hp).symm) (fun p hp ↦ (G.comp_sum_single b hp).symm),
    Finset.sum_mul_sum, map_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hp' : p < n + 1 := Finset.mem_range.mp hp
  rw [map_sum, Finset.sum_eq_single (n - p)]
  · intro q _ hq
    exact G.mul_hom p q _ _ (G.isHom_single p _) (G.isHom_single q _) n (by omega)
  · intro hq
    exact absurd (Finset.mem_range.mpr (by omega)) hq

/-- The Cauchy product formula, indexed by the degree of the second factor. -/
theorem comp_mul_rev (n : ℕ) (a b : R) :
    G.comp n (a * b) = ∑ p ∈ range (n + 1),
      G.comp n (G.single (n - p) (G.comp (n - p) a) * G.single p (G.comp p b)) := by
  rw [comp_mul, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hp' : p < n + 1 := Finset.mem_range.mp hp
  rw [show n + 1 - 1 - p = n - p by omega, Nat.sub_sub_self (by omega : p ≤ n)]

theorem vanishBelow_smul {n : ℕ} (q : ℚ) {a : R} (ha : G.VanishBelow n a) :
    G.VanishBelow n (q • a) :=
  fun p hp ↦ by rw [map_smul, ha p hp, smul_zero]

/-- Orders add under multiplication. -/
theorem vanishBelow_mul {i j : ℕ} {a b : R} (ha : G.VanishBelow i a) (hb : G.VanishBelow j b) :
    G.VanishBelow (i + j) (a * b) := by
  intro n hn
  rw [comp_mul]
  refine Finset.sum_eq_zero fun p hp ↦ ?_
  have hp' : p < n + 1 := Finset.mem_range.mp hp
  rcases lt_or_ge p i with hpi | hpi
  · rw [ha p hpi, single_zero, zero_mul, map_zero]
  · rw [hb (n - p) (by omega), single_zero, mul_zero, map_zero]

/-- A power of an element without constant term has no component of degree below the exponent. -/
theorem vanishBelow_pow {x : R} (hx : G.comp 0 x = 0) (j : ℕ) : G.VanishBelow j (x ^ j) := by
  induction j with
  | zero => exact fun p hp ↦ absurd hp (Nat.not_lt_zero p)
  | succ j ih =>
    rw [pow_succ]
    exact G.vanishBelow_mul ih fun p hp ↦ by rw [Nat.lt_one_iff.mp hp, hx]

/-- A power of a homogeneous element of degree one is homogeneous of degree the exponent. -/
theorem isHom_pow {h : R} (hh : G.IsHom 1 h) (j : ℕ) : G.IsHom j (h ^ j) := by
  induction j with
  | zero => rw [pow_zero]; exact G.comp_one
  | succ j ih => rw [pow_succ]; exact G.mul_hom j 1 _ _ ih hh

/-- In a sum `∑_{j ≤ N} f j` with `f j` of order `≥ j`, the degree-`n` component does not depend
on `N ≥ n`. -/
theorem comp_sum_range_of_le (f : ℕ → R) (hf : ∀ j, G.VanishBelow j (f j)) {n N : ℕ}
    (h : n ≤ N) :
    G.comp n (∑ j ∈ range (n + 1), f j) = G.comp n (∑ j ∈ range (N + 1), f j) := by
  rw [map_sum, map_sum]
  refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun j _ hj ↦ ?_
  exact hf j n (by simp only [Finset.mem_range, not_lt] at hj; omega)

/-- Truncated Cauchy products: if `u a * v b` has order `≥ a + b`, then in degree `n` the product
of the partial sums up to `n` is the partial sum of the Cauchy product. -/
theorem comp_sum_mul_sum (u v : ℕ → R) (huv : ∀ a b, G.VanishBelow (a + b) (u a * v b))
    (n : ℕ) :
    G.comp n ((∑ a ∈ range (n + 1), u a) * ∑ b ∈ range (n + 1), v b) =
      G.comp n (∑ j ∈ range (n + 1), ∑ a ∈ range (j + 1), u a * v (j - a)) := by
  rw [Finset.sum_mul_sum, Finset.sum_range_diag_flip (n + 1) (fun a b ↦ u a * v b)]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  have ha' : a < n + 1 := Finset.mem_range.mp ha
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun b _ hb ↦ ?_
  exact huv a b n (by simp only [Finset.mem_range, not_lt] at hb; omega)

/-! ### The exponential -/

/-- The exponential `∑_j x^j / j!`, meaningful when `x` has no constant term: in degree `n` it is
the degree-`n` component of `∑_{j ≤ n} x^j / j!`. -/
noncomputable def gexp (x : R) : R :=
  G.ofComps fun n ↦ G.comp n (∑ j ∈ range (n + 1), ((j.factorial : ℚ)⁻¹) • x ^ j)

theorem comp_gexp (x : R) (n : ℕ) :
    G.comp n (G.gexp x) = G.comp n (∑ j ∈ range (n + 1), ((j.factorial : ℚ)⁻¹) • x ^ j) :=
  G.comp_ofComps _ n

/-- For `x` without constant term the truncation may be taken at any order `N ≥ n`. -/
theorem comp_gexp_of_le {x : R} (hx : G.comp 0 x = 0) {n N : ℕ} (h : n ≤ N) :
    G.comp n (G.gexp x) = G.comp n (∑ j ∈ range (N + 1), ((j.factorial : ℚ)⁻¹) • x ^ j) := by
  rw [comp_gexp]
  exact G.comp_sum_range_of_le _ (fun j ↦ G.vanishBelow_smul _ (G.vanishBelow_pow hx j)) h

theorem gexp_zero : G.gexp 0 = 1 := by
  refine G.ext _ _ fun n ↦ ?_
  rw [comp_gexp, Finset.sum_range_succ']
  simp

include G in
/-- `(x + y)^j / j! = ∑_{a ≤ j} (x^a / a!) (y^{j-a} / (j-a)!)` for commuting `x`, `y`. -/
theorem smul_add_pow {x y : R} (hxy : Commute x y) (j : ℕ) :
    ((j.factorial : ℚ)⁻¹) • (x + y) ^ j = ∑ a ∈ range (j + 1),
      (((a.factorial : ℚ)⁻¹) • x ^ a) * (((j - a).factorial : ℚ)⁻¹ • y ^ (j - a)) := by
  rw [hxy.add_pow, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  have ha' : a ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  rw [G.smul_mul, G.mul_smul, smul_smul, ← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
    Nat.cast_choose ℚ ha']
  congr 1
  have h1 : (j.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have h2 : (a.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)
  have h3 : ((j - a).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

/-- **The exponential of a sum of commuting elements without constant term is the product of the
exponentials.** -/
theorem gexp_add {x y : R} (hx : G.comp 0 x = 0) (hy : G.comp 0 y = 0) (hxy : Commute x y) :
    G.gexp (x + y) = G.gexp x * G.gexp y := by
  have huv : ∀ a b, G.VanishBelow (a + b)
      ((((a.factorial : ℚ)⁻¹) • x ^ a) * (((b.factorial : ℚ)⁻¹) • y ^ b)) := fun a b ↦ by
    rw [G.smul_mul, G.mul_smul]
    exact G.vanishBelow_smul _ (G.vanishBelow_smul _
      (G.vanishBelow_mul (G.vanishBelow_pow hx a) (G.vanishBelow_pow hy b)))
  refine G.ext _ _ fun n ↦ ?_
  rw [G.mul_congr n _ (∑ a ∈ range (n + 1), ((a.factorial : ℚ)⁻¹) • x ^ a) _
      (∑ b ∈ range (n + 1), ((b.factorial : ℚ)⁻¹) • y ^ b)
      (fun p hp ↦ G.comp_gexp_of_le hx hp) (fun p hp ↦ G.comp_gexp_of_le hy hp),
    G.comp_sum_mul_sum _ _ huv n, comp_gexp]
  exact congrArg _ (Finset.sum_congr rfl fun j _ ↦ G.smul_add_pow hxy j)

theorem gexp_mul_gexp_neg {x : R} (hx : G.comp 0 x = 0) : G.gexp x * G.gexp (-x) = 1 := by
  rw [← G.gexp_add hx (by rw [map_neg, hx, neg_zero]) (Commute.neg_right (Commute.refl x)),
    add_neg_cancel, gexp_zero]

theorem gexp_neg_mul_gexp {x : R} (hx : G.comp 0 x = 0) : G.gexp (-x) * G.gexp x = 1 := by
  rw [← G.gexp_add (by rw [map_neg, hx, neg_zero]) hx (Commute.neg_left (Commute.refl x)),
    neg_add_cancel, gexp_zero]

theorem isUnit_gexp {x : R} (hx : G.comp 0 x = 0) : IsUnit (G.gexp x) :=
  ⟨⟨G.gexp x, G.gexp (-x), G.gexp_mul_gexp_neg hx, G.gexp_neg_mul_gexp hx⟩, rfl⟩

/-! ### Degreewise rescaling -/

/-- Multiply the degree-`n` component by `w n`. -/
noncomputable def weight (w : ℕ → ℚ) (a : R) : R := G.ofComps fun n ↦ w n • G.comp n a

theorem comp_weight (w : ℕ → ℚ) (a : R) (n : ℕ) : G.comp n (G.weight w a) = w n • G.comp n a :=
  G.comp_ofComps _ n

theorem weight_add (w : ℕ → ℚ) (a b : R) : G.weight w (a + b) = G.weight w a + G.weight w b :=
  G.ext _ _ fun n ↦ by simp only [comp_weight, map_add, smul_add]

theorem weight_zero (w : ℕ → ℚ) : G.weight w (0 : R) = 0 :=
  G.ext _ _ fun n ↦ by rw [comp_weight, map_zero, smul_zero]

theorem weight_neg (w : ℕ → ℚ) (a : R) : G.weight w (-a) = -G.weight w a :=
  G.ext _ _ fun n ↦ by rw [map_neg, comp_weight, comp_weight, map_neg, smul_neg]

theorem weight_one (a : R) : G.weight (fun _ ↦ 1) a = a :=
  G.ext _ _ fun n ↦ by rw [comp_weight, one_smul]

/-- The Cauchy product formula for rescaled factors. -/
theorem comp_weight_mul_weight (w w' : ℕ → ℚ) (a b : R) (n : ℕ) :
    G.comp n (G.weight w a * G.weight w' b) = ∑ p ∈ range (n + 1), (w p * w' (n - p)) •
      G.comp n (G.single p (G.comp p a) * G.single (n - p) (G.comp (n - p) b)) := by
  rw [comp_mul]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [comp_weight, comp_weight, single_smul, single_smul, G.smul_mul, G.mul_smul, smul_smul,
    map_smul]

/-- The Cauchy product formula for rescaled factors, indexed by the degree of the second one. -/
theorem comp_weight_mul_weight_rev (w w' : ℕ → ℚ) (a b : R) (n : ℕ) :
    G.comp n (G.weight w' b * G.weight w a) = ∑ p ∈ range (n + 1), (w' (n - p) * w p) •
      G.comp n (G.single (n - p) (G.comp (n - p) b) * G.single p (G.comp p a)) := by
  rw [comp_mul_rev]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [comp_weight, comp_weight, single_smul, single_smul, G.smul_mul, G.mul_smul, smul_smul,
    map_smul]

/-- A family of vectors killed by a square `ℚ`-matrix with nonzero determinant vanishes. -/
theorem eq_zero_of_sum_smul_eq_zero {k : ℕ} {N : Type*} [AddCommGroup N] [Module ℚ N]
    (A : Matrix (Fin k) (Fin k) ℚ) (hA : A.det ≠ 0) (v : Fin k → N)
    (h : ∀ i, ∑ p, A i p • v p = 0) (q : Fin k) : v q = 0 := by
  have hBA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA)
  calc v q = ∑ p, (A⁻¹ * A) q p • v p := by
          rw [hBA]; simp [Matrix.one_apply]
    _ = ∑ i, A⁻¹ q i • ∑ p, A i p • v p := by
          simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
          exact Finset.sum_comm
    _ = 0 := by simp [h]

/-- **Commutation from scalings.** If the rescalings `(2^{i n} c_n)_n` of `c` all commute with
`c'` (for every `i`), then every degreewise rescaling of `c` commutes with every degreewise
rescaling of `c'`: the homogeneous components of `c` and `c'` commute pairwise, by a Vandermonde
argument in each degree. -/
theorem commute_weight_of_commute_scaling {c c' : R}
    (h : ∀ i : ℕ, Commute (G.weight (fun n ↦ (2 : ℚ) ^ (i * n)) c) c') (w w' : ℕ → ℚ) :
    Commute (G.weight w c) (G.weight w' c') := by
  show G.weight w c * G.weight w' c' = G.weight w' c' * G.weight w c
  refine G.ext _ _ fun m ↦ ?_
  have key : ∀ i : ℕ, ∑ p ∈ range (m + 1), ((2 : ℚ) ^ (i * p)) •
      (G.comp m (G.single p (G.comp p c) * G.single (m - p) (G.comp (m - p) c')) -
        G.comp m (G.single (m - p) (G.comp (m - p) c') * G.single p (G.comp p c))) = 0 := by
    intro i
    have e := congrArg (G.comp m) (h i).eq
    rw [← G.weight_one c', G.comp_weight_mul_weight, G.comp_weight_mul_weight_rev] at e
    simp only [mul_one, one_mul] at e
    rw [Finset.sum_congr rfl fun p _ ↦ smul_sub _ _ _, Finset.sum_sub_distrib, e, sub_self]
  have hXY : ∀ p ≤ m,
      G.comp m (G.single p (G.comp p c) * G.single (m - p) (G.comp (m - p) c')) =
        G.comp m (G.single (m - p) (G.comp (m - p) c') * G.single p (G.comp p c)) := by
    intro p hp
    have hinj : Function.Injective fun q : Fin (m + 1) ↦ (2 : ℚ) ^ (q : ℕ) :=
      (pow_right_injective₀ (by norm_num) (by norm_num)).comp Fin.val_injective
    have hdet : (Matrix.transpose
        (Matrix.vandermonde fun q : Fin (m + 1) ↦ (2 : ℚ) ^ (q : ℕ))).det ≠ 0 := by
      rw [Matrix.det_transpose]
      exact Matrix.det_vandermonde_ne_zero_iff.mpr hinj
    refine sub_eq_zero.mp (eq_zero_of_sum_smul_eq_zero _ hdet
      (fun q : Fin (m + 1) ↦
        G.comp m (G.single q (G.comp q c) * G.single (m - q) (G.comp (m - q) c')) -
          G.comp m (G.single (m - q) (G.comp (m - q) c') * G.single q (G.comp q c)))
      (fun i ↦ ?_) ⟨p, by omega⟩)
    have e := key i
    rw [← Fin.sum_univ_eq_sum_range] at e
    simp only [Matrix.transpose_apply, Matrix.vandermonde_apply, ← pow_mul]
    simpa only [mul_comm] using e
  rw [G.comp_weight_mul_weight, G.comp_weight_mul_weight_rev]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [hXY p (Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)), mul_comm (w p)]

/-! ### Power series evaluated at an element without constant term -/

/-- The value `∑_j F_j h^j` of a power series at `h`, meaningful when `h` has no constant term:
in degree `n` it is the degree-`n` component of `∑_{j ≤ n} F_j h^j`. -/
noncomputable def ev (h : R) (F : ℚ⟦X⟧) : R :=
  G.ofComps fun n ↦ G.comp n (∑ j ∈ range (n + 1), (coeff j F) • h ^ j)

theorem comp_ev (h : R) (F : ℚ⟦X⟧) (n : ℕ) :
    G.comp n (G.ev h F) = G.comp n (∑ j ∈ range (n + 1), (coeff j F) • h ^ j) :=
  G.comp_ofComps _ n

/-- For `h` without constant term the truncation may be taken at any order `N ≥ n`. -/
theorem comp_ev_of_le {h : R} (hh : G.comp 0 h = 0) (F : ℚ⟦X⟧) {n N : ℕ} (hn : n ≤ N) :
    G.comp n (G.ev h F) = G.comp n (∑ j ∈ range (N + 1), (coeff j F) • h ^ j) := by
  rw [comp_ev]
  exact G.comp_sum_range_of_le _ (fun j ↦ G.vanishBelow_smul _ (G.vanishBelow_pow hh j)) hn

/-- For `h` homogeneous of degree one, the degree-`n` component of `F(h)` is `F_n h^n`. -/
theorem comp_ev_of_isHom {h : R} (hh : G.IsHom 1 h) (F : ℚ⟦X⟧) (n : ℕ) :
    G.comp n (G.ev h F) = (coeff n F) • G.comp n (h ^ n) := by
  rw [comp_ev, map_sum, Finset.sum_eq_single n]
  · exact map_smul _ _ _
  · intro j _ hj
    rw [map_smul, G.isHom_pow hh j n (Ne.symm hj), smul_zero]
  · intro hn
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) hn

/-- The degree-`n` component of `F(h)` only depends on the coefficients of `F` of degree `≤ n`. -/
theorem comp_ev_congr (h : R) {F F' : ℚ⟦X⟧} {n : ℕ} (hF : ∀ i ≤ n, coeff i F = coeff i F') :
    G.comp n (G.ev h F) = G.comp n (G.ev h F') := by
  rw [comp_ev, comp_ev]
  exact congrArg _ (Finset.sum_congr rfl fun i hi ↦ by
    rw [hF i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))])

theorem ev_add (h : R) (F F' : ℚ⟦X⟧) : G.ev h (F + F') = G.ev h F + G.ev h F' :=
  G.ext _ _ fun n ↦ by simp only [map_add, comp_ev, add_smul, Finset.sum_add_distrib]

theorem ev_smul (h : R) (q : ℚ) (F : ℚ⟦X⟧) : G.ev h (q • F) = q • G.ev h F :=
  G.ext _ _ fun n ↦ by
    rw [map_smul, comp_ev, comp_ev, ← map_smul, Finset.smul_sum]
    simp only [map_smul, smul_eq_mul, smul_smul]

theorem ev_zero (h : R) : G.ev h 0 = 0 :=
  G.ext _ _ fun n ↦ by simp only [comp_ev, map_zero, zero_smul, Finset.sum_const_zero]

theorem ev_neg (h : R) (F : ℚ⟦X⟧) : G.ev h (-F) = -G.ev h F := by
  rw [← neg_one_smul ℚ F, ev_smul, neg_one_smul]

theorem ev_sub (h : R) (F F' : ℚ⟦X⟧) : G.ev h (F - F') = G.ev h F - G.ev h F' := by
  rw [sub_eq_add_neg, ev_add, ev_neg, ← sub_eq_add_neg]

theorem ev_sum (h : R) {ι : Type*} (s : Finset ι) (F : ι → ℚ⟦X⟧) :
    G.ev h (∑ i ∈ s, F i) = ∑ i ∈ s, G.ev h (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, ev_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ev_add, ih]

theorem ev_one {h : R} (hh : G.comp 0 h = 0) : G.ev h 1 = 1 := by
  -- `hh` belongs to the shared signature; this proof does not need it.
  have _ := hh
  refine G.ext _ _ fun n ↦ ?_
  rw [comp_ev, Finset.sum_eq_single 0]
  · rw [coeff_one, ite_eq_left rfl, one_smul, pow_zero]
  · intro j _ hj
    rw [coeff_one, ite_eq_right hj, zero_smul]
  · intro h0
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h0

theorem ev_X {h : R} (hh : G.comp 0 h = 0) : G.ev h X = h :=
  G.ext _ _ fun n ↦ by
    rw [comp_ev]
    rcases n with _ | n
    · rw [Finset.sum_range_one, coeff_X, ite_eq_right zero_ne_one, zero_smul, map_zero, hh]
    · rw [Finset.sum_eq_single 1]
      · rw [coeff_X, ite_eq_left rfl, one_smul, pow_one]
      · intro j _ hj
        rw [coeff_X, ite_eq_right hj, zero_smul]
      · intro h1
        exact absurd (Finset.mem_range.mpr (by omega)) h1

/-- **Evaluation at an element without constant term is multiplicative.** -/
theorem ev_mul {h : R} (hh : G.comp 0 h = 0) (F F' : ℚ⟦X⟧) :
    G.ev h (F * F') = G.ev h F * G.ev h F' := by
  have huv : ∀ a b, G.VanishBelow (a + b) ((coeff a F • h ^ a) * (coeff b F' • h ^ b)) :=
    fun a b ↦ by
      rw [G.smul_mul, G.mul_smul, ← pow_add]
      exact G.vanishBelow_smul _ (G.vanishBelow_smul _ (G.vanishBelow_pow hh _))
  refine G.ext _ _ fun n ↦ ?_
  rw [G.mul_congr n _ (∑ j ∈ range (n + 1), (coeff j F) • h ^ j) _
      (∑ j ∈ range (n + 1), (coeff j F') • h ^ j)
      (fun p hp ↦ G.comp_ev_of_le hh F hp) (fun p hp ↦ G.comp_ev_of_le hh F' hp),
    G.comp_sum_mul_sum _ _ huv n, comp_ev]
  refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b ↦ coeff a F * coeff b F'),
    Finset.sum_smul]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  have ha' : a ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  rw [G.smul_mul, G.mul_smul, smul_smul, ← pow_add, Nat.add_sub_cancel' ha']

theorem ev_pow {h : R} (hh : G.comp 0 h = 0) (F : ℚ⟦X⟧) (n : ℕ) :
    G.ev h (F ^ n) = G.ev h F ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, G.ev_one hh]
  | succ n ih => rw [pow_succ, pow_succ, G.ev_mul hh, ih]

theorem comp_zero_ev {h : R} (hh : G.comp 0 h = 0) {F : ℚ⟦X⟧} (hF : constantCoeff F = 0) :
    G.comp 0 (G.ev h F) = 0 := by
  -- `hh` belongs to the shared signature; this proof does not need it.
  have _ := hh
  rw [comp_ev, Finset.sum_range_one, coeff_zero_eq_constantCoeff_apply, hF, zero_smul, map_zero]

/-- Powers of a power series without constant term have no terms of low degree. -/
theorem coeff_pow_of_lt {L : ℚ⟦X⟧} (hL : constantCoeff L = 0) {i j : ℕ} (h : i < j) :
    coeff i (L ^ j) = 0 := by
  obtain ⟨g, hg⟩ := X_dvd_iff.mpr hL
  rw [hg, mul_pow, coeff_X_pow_mul', ite_eq_right (by omega)]

/-- **`exp (L(h)) = T(h)`** whenever `T = exp L` coefficient by coefficient. -/
theorem gexp_ev {h : R} (hh : G.comp 0 h = 0) {L T : ℚ⟦X⟧} (hL : constantCoeff L = 0)
    (hT : ∀ n, coeff n T = coeff n (∑ j ∈ range (n + 1), ((j.factorial : ℚ)⁻¹) • L ^ j)) :
    G.gexp (G.ev h L) = G.ev h T := by
  refine G.ext _ _ fun n ↦ ?_
  rw [G.comp_ev_congr h (F := T) (F' := ∑ j ∈ range (n + 1), ((j.factorial : ℚ)⁻¹) • L ^ j)
      fun i hi ↦ ?_, comp_gexp, ev_sum]
  · simp only [ev_smul, G.ev_pow hh]
  · rw [hT i]
    simp only [map_sum, map_smul]
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun j _ hj ↦ ?_
    rw [coeff_pow_of_lt hL (by simp only [Finset.mem_range, not_lt] at hj; omega), smul_zero]

/-! ### The Todd operation -/

/-- The weights `n! · ℓ_n`, where `log (x / (1 - e^{-x})) = ∑ ℓ_n x^n`. -/
noncomputable def toddWeight (n : ℕ) : ℚ := (n.factorial : ℚ) * coeff n logTodd

/-- The Todd operation on a "Chern character" `c = (c_n)_n`: the exponential of
`∑_n n! · ℓ_n · c_n`. For `c = ch(E) = ∑_i e^{x_i}` this is `∏_i x_i / (1 - e^{-x_i})`. -/
noncomputable def toddOf (c : R) : R := G.gexp (G.weight toddWeight c)

theorem comp_zero_weight_toddWeight (c : R) : G.comp 0 (G.weight toddWeight c) = 0 := by
  rw [comp_weight, toddWeight, coeff_zero_eq_constantCoeff_apply, constantCoeff_logTodd,
    mul_zero, zero_smul]

theorem toddOf_zero : G.toddOf 0 = 1 := by
  rw [toddOf, weight_zero, gexp_zero]

/-- **The Todd operation turns sums into products**, for summands whose rescalings commute. -/
theorem toddOf_add {c c' : R} (h : Commute (G.weight toddWeight c) (G.weight toddWeight c')) :
    G.toddOf (c + c') = G.toddOf c * G.toddOf c' := by
  rw [toddOf, weight_add]
  exact G.gexp_add (G.comp_zero_weight_toddWeight c) (G.comp_zero_weight_toddWeight c') h

theorem toddOf_mul_toddOf_neg (c : R) : G.toddOf c * G.toddOf (-c) = 1 := by
  rw [toddOf, toddOf, weight_neg]
  exact G.gexp_mul_gexp_neg (G.comp_zero_weight_toddWeight c)

theorem toddOf_neg_mul_toddOf (c : R) : G.toddOf (-c) * G.toddOf c = 1 := by
  rw [toddOf, toddOf, weight_neg]
  exact G.gexp_neg_mul_gexp (G.comp_zero_weight_toddWeight c)

theorem isUnit_toddOf (c : R) : IsUnit (G.toddOf c) :=
  G.isUnit_gexp (G.comp_zero_weight_toddWeight c)

/-- **The Todd operation on `e^h`** for `h` homogeneous of degree one is the Todd series at `h`:
`td(e^h) = h / (1 - e^{-h})`. -/
theorem toddOf_ev_exp {h : R} (hh : G.IsHom 1 h) :
    G.toddOf (G.ev h (exp ℚ)) = G.ev h toddSeries := by
  have hh0 : G.comp 0 h = 0 := hh 0 zero_ne_one
  have hw : G.weight toddWeight (G.ev h (exp ℚ)) = G.ev h logTodd := by
    refine G.ext _ _ fun n ↦ ?_
    rw [comp_weight, G.comp_ev_of_isHom hh, G.comp_ev_of_isHom hh, smul_smul, coeff_exp]
    congr 1
    have hn : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    simp only [toddWeight, Algebra.algebraMap_self, RingHom.id_apply]
    field_simp
  rw [toddOf, hw]
  exact G.gexp_ev hh0 constantCoeff_logTodd coeff_toddSeries_eq_coeff_sum_logTodd_pow

/-- **The rank-one Koszul identity**: `td(e^h) · (1 - e^{-h}) = h`. -/
theorem ev_toddSeries_mul_one_sub_ev_expNeg {h : R} (hh : G.comp 0 h = 0) :
    G.ev h toddSeries * (1 - G.ev h expNeg) = h := by
  rw [← G.ev_one hh, ← ev_sub, ← G.ev_mul hh, toddSeries_mul_one_sub_expNeg, G.ev_X hh]

end GradedComplete

end GRR
