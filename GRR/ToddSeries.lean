import Mathlib

/-!
# The Todd power series

`GRR.toddSeries` is `x / (1 - e^{-x}) = ∑ B⁺_n x^n / n!` in `ℚ⟦X⟧`. This file proves the three
facts about it that Grothendieck–Riemann–Roch uses:

* `GRR.toddSeries_mul_one_sub_expNeg`: `Q · (1 - e^{-x}) = x` (the rank-one Koszul identity);
* `GRR.coeff_exp_pow_mul_toddSeries_pow`: `[x^n] (e^{d x} · Q^{n+1}) = C(n + d, n)`
  (Riemann–Roch on projective space);
* `GRR.coeff_toddSeries_eq_coeff_sum_logTodd_pow`: `Q = exp (log Q)`, coefficient by coefficient
  (the Todd class is the exponential of a linear function of the Chern character).
-/

open PowerSeries

namespace GRR

/-- The Todd power series `x / (1 - e^{-x}) = ∑ B⁺_n x^n / n!`, as the generating series of the
Bernoulli numbers `B⁺_n` (those with `B⁺_1 = 1/2`). -/
noncomputable def toddSeries : ℚ⟦X⟧ := bernoulli'PowerSeries ℚ

/-- The power series `e^{-x}`. -/
noncomputable def expNeg : ℚ⟦X⟧ := evalNegHom (exp ℚ)

theorem exp_mul_expNeg : exp ℚ * expNeg = 1 := exp_mul_exp_neg_eq_one

theorem expNeg_mul_exp : expNeg * exp ℚ = 1 := by rw [mul_comm, exp_mul_expNeg]

/-- The defining relation of the Todd series: `Q · (1 - e^{-x}) = x`. -/
theorem toddSeries_mul_one_sub_expNeg : toddSeries * (1 - expNeg) = X := by
  have h : toddSeries * (exp ℚ - 1) = X * exp ℚ := bernoulli'PowerSeries_mul_exp_sub_one ℚ
  have h1 : (exp ℚ - 1) * expNeg = 1 - expNeg := by rw [sub_mul, exp_mul_expNeg, one_mul]
  calc toddSeries * (1 - expNeg) = toddSeries * (exp ℚ - 1) * expNeg := by rw [mul_assoc, h1]
    _ = X * (exp ℚ * expNeg) := by rw [h, mul_assoc]
    _ = X := by rw [exp_mul_expNeg, mul_one]

/-- The Todd series has constant term `1`. -/
theorem constantCoeff_toddSeries : constantCoeff toddSeries = 1 := by
  simp [toddSeries, bernoulli'PowerSeries]

/-- The coefficients of `e^{-x}`. -/
theorem coeff_expNeg (n : ℕ) : coeff n expNeg = (-1) ^ n / (n.factorial : ℚ) := by
  simp [expNeg, evalNegHom, coeff_exp, div_eq_mul_inv, mul_comm]

/-- `(e^{-x})' = -e^{-x}`. -/
theorem derivative_expNeg : d⁄dX expNeg = -expNeg := by
  ext n
  rw [coeff_derivative, map_neg, coeff_expNeg, coeff_expNeg, Nat.factorial_succ]
  have h : ((n.factorial : ℚ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have h' : ((n : ℚ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- `x · Q' = Q - e^{-x} · Q²`. -/
theorem X_mul_derivative_toddSeries :
    X * d⁄dX toddSeries = toddSeries - expNeg * toddSeries ^ 2 := by
  have h : d⁄dX (toddSeries * (1 - expNeg)) = d⁄dX (X : ℚ⟦X⟧) := by
    rw [toddSeries_mul_one_sub_expNeg]
  rw [Derivation.leibniz, map_sub, derivative_expNeg, derivative_X] at h
  simp only [smul_eq_mul, Derivation.map_one_eq_zero, zero_sub, neg_neg] at h
  -- h : toddSeries * expNeg + (1 - expNeg) * d⁄dX toddSeries = 1
  have h2 : toddSeries * (toddSeries * expNeg + (1 - expNeg) * d⁄dX toddSeries) = toddSeries := by
    rw [h, mul_one]
  have h3 : toddSeries * ((1 - expNeg) * d⁄dX toddSeries) = X * d⁄dX toddSeries := by
    rw [← mul_assoc, toddSeries_mul_one_sub_expNeg]
  rw [mul_add, h3] at h2
  linear_combination h2

/-- `x · (Q^n)' = n · Q^n - n · e^{-x} · Q^{n+1}`. -/
theorem X_mul_derivative_toddSeries_pow (n : ℕ) :
    X * d⁄dX (toddSeries ^ n) =
      (n : ℚ⟦X⟧) * toddSeries ^ n - (n : ℚ⟦X⟧) * (expNeg * toddSeries ^ (n + 1)) := by
  rcases n with _ | n
  · simp
  · rw [derivative_pow]
    have h := X_mul_derivative_toddSeries
    have : X * (((n + 1 : ℕ) : ℚ⟦X⟧) * toddSeries ^ (n + 1 - 1) * d⁄dX toddSeries) =
        ((n + 1 : ℕ) : ℚ⟦X⟧) * toddSeries ^ n * (X * d⁄dX toddSeries) := by
      rw [Nat.add_sub_cancel]; ring
    rw [this, h]
    ring

/-- The coefficient of `x^n` in `e^{-x} · Q^{n+1}` vanishes for `n ≥ 1`. -/
theorem coeff_expNeg_mul_toddSeries_pow (n : ℕ) :
    coeff (n + 1) (expNeg * toddSeries ^ (n + 2)) = 0 := by
  have h := congrArg (coeff (n + 1)) (X_mul_derivative_toddSeries_pow (n + 1))
  rw [mul_comm X, coeff_succ_mul_X, coeff_derivative, map_sub] at h
  have e1 : ((n + 1 : ℕ) : ℚ⟦X⟧) = C ((n + 1 : ℕ) : ℚ) := by simp
  rw [e1, coeff_C_mul, coeff_C_mul] at h
  have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have h' : ((n + 1 : ℕ) : ℚ) * coeff (n + 1) (expNeg * toddSeries ^ (n + 1 + 1)) = 0 := by
    push_cast at h ⊢
    linear_combination h
  exact (mul_eq_zero.mp h').resolve_left hn

/-- `e^{(d+1)x} Q^{n+1} - e^{dx} Q^{n+1} = x · e^{(d+1)x} Q^n`. -/
theorem exp_pow_succ_mul_toddSeries_pow_succ (n d : ℕ) :
    exp ℚ ^ (d + 1) * toddSeries ^ (n + 1) =
      exp ℚ ^ d * toddSeries ^ (n + 1) + X * (exp ℚ ^ (d + 1) * toddSeries ^ n) := by
  have h := toddSeries_mul_one_sub_expNeg
  have h1 : exp ℚ ^ (d + 1) * expNeg = exp ℚ ^ d := by
    rw [pow_succ, mul_assoc, exp_mul_expNeg, mul_one]
  calc exp ℚ ^ (d + 1) * toddSeries ^ (n + 1)
      = exp ℚ ^ (d + 1) * expNeg * toddSeries ^ (n + 1) +
          exp ℚ ^ (d + 1) * toddSeries ^ n * (toddSeries * (1 - expNeg)) := by ring
    _ = exp ℚ ^ d * toddSeries ^ (n + 1) + X * (exp ℚ ^ (d + 1) * toddSeries ^ n) := by
        rw [h1, h]; ring

/-- `Q^{n+1} - e^{-x} Q^{n+1} = x · Q^n`. -/
theorem toddSeries_pow_succ (n : ℕ) :
    toddSeries ^ (n + 1) = expNeg * toddSeries ^ (n + 1) + X * toddSeries ^ n := by
  have h := toddSeries_mul_one_sub_expNeg
  calc toddSeries ^ (n + 1)
      = expNeg * toddSeries ^ (n + 1) + toddSeries ^ n * (toddSeries * (1 - expNeg)) := by ring
    _ = expNeg * toddSeries ^ (n + 1) + X * toddSeries ^ n := by rw [h]; ring

/-- **Riemann–Roch on projective space, as an identity of power series**: the coefficient of
`x^n` in `e^{d x} · (x / (1 - e^{-x}))^{n+1}` is the binomial coefficient `C(n + d, n)`, the
rank of the degree-`d` forms in `n + 1` variables. -/
theorem coeff_exp_pow_mul_toddSeries_pow (n d : ℕ) :
    coeff n (exp ℚ ^ d * toddSeries ^ (n + 1)) = ((n + d).choose n : ℚ) := by
  induction n generalizing d with
  | zero =>
    have : constantCoeff (exp ℚ ^ d * toddSeries ^ (0 + 1)) = 1 := by
      simp [constantCoeff_toddSeries]
    simpa using this
  | succ n ihn =>
    induction d with
    | zero =>
      have h := congrArg (coeff (n + 1)) (toddSeries_pow_succ (n + 1))
      rw [map_add, coeff_expNeg_mul_toddSeries_pow, zero_add, mul_comm X, coeff_succ_mul_X] at h
      have h0 := ihn 0
      simp only [pow_zero, one_mul, Nat.add_zero, Nat.choose_self, Nat.cast_one] at h0 ⊢
      rw [h, h0]
    | succ d ihd =>
      have h := congrArg (coeff (n + 1)) (exp_pow_succ_mul_toddSeries_pow_succ (n + 1) d)
      rw [map_add, mul_comm X, coeff_succ_mul_X, ihd, ihn (d + 1)] at h
      rw [h]
      have : (n + 1 + (d + 1)).choose (n + 1) = (n + 1 + d).choose (n + 1) + (n + (d + 1)).choose n := by
        rw [show n + 1 + (d + 1) = (n + 1 + d) + 1 by ring, Nat.choose_succ_succ,
          show n + (d + 1) = n + 1 + d by ring, add_comm]
      rw [this]
      push_cast
      ring

/-- `e^{-jx} Q^{n+1} - e^{-(j+1)x} Q^{n+1} = x · e^{-jx} Q^n`. -/
theorem expNeg_pow_mul_toddSeries_pow_succ (n j : ℕ) :
    expNeg ^ j * toddSeries ^ (n + 1) =
      expNeg ^ (j + 1) * toddSeries ^ (n + 1) + X * (expNeg ^ j * toddSeries ^ n) := by
  have h := toddSeries_mul_one_sub_expNeg
  calc expNeg ^ j * toddSeries ^ (n + 1)
      = expNeg ^ (j + 1) * toddSeries ^ (n + 1) +
          expNeg ^ j * toddSeries ^ n * (toddSeries * (1 - expNeg)) := by ring
    _ = expNeg ^ (j + 1) * toddSeries ^ (n + 1) + X * (expNeg ^ j * toddSeries ^ n) := by
        rw [h]; ring

/-- **Vanishing on projective space, as an identity of power series**: the coefficient of `x^n`
in `e^{-j x} · (x / (1 - e^{-x}))^{n+1}` vanishes for `1 ≤ j ≤ n` (the twists `𝒪(-j)`,
`1 ≤ j ≤ n`, of `ℙⁿ` have no cohomology). -/
theorem coeff_expNeg_pow_mul_toddSeries_pow {n j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) :
    coeff n (expNeg ^ j * toddSeries ^ (n + 1)) = 0 := by
  induction j generalizing n with
  | zero => omega
  | succ j ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simpa using coeff_expNeg_mul_toddSeries_pow m
    · have h := congrArg (coeff (m + 1)) (expNeg_pow_mul_toddSeries_pow_succ (m + 1) j)
      rw [map_add, mul_comm X, coeff_succ_mul_X, ih hjpos (by omega), ih hjpos (by omega)] at h
      simpa using h.symm

/-! ### The logarithm of the Todd series -/

/-- The logarithm of the Todd series, `log (x / (1 - e^{-x})) = x/2 - x²/24 + ⋯`. -/
noncomputable def logTodd : ℚ⟦X⟧ := logOf toddSeries

theorem constantCoeff_logTodd : constantCoeff logTodd = 0 :=
  constantCoeff_logOf constantCoeff_toddSeries

theorem hasSubst_toddSeries_sub_one : HasSubst (toddSeries - 1) := by
  apply HasSubst.of_constantCoeff_zero'
  simp [constantCoeff_toddSeries]

theorem hasSubst_logTodd : HasSubst logTodd :=
  HasSubst.of_constantCoeff_zero' constantCoeff_logTodd

/-- `exp (log Q) = Q`, as a substitution of power series. -/
theorem exp_subst_logTodd : (exp ℚ).subst logTodd = toddSeries := by
  have h1 : (exp ℚ).subst logTodd =
      PowerSeries.subst (toddSeries - 1) ((exp ℚ).subst (log ℚ) : ℚ⟦X⟧) := by
    rw [logTodd, logOf_eq]
    exact (subst_comp_subst_apply HasSubst.log hasSubst_toddSeries_sub_one (exp ℚ)).symm
  rw [h1, subst_exp_log, subst_add hasSubst_toddSeries_sub_one,
    subst_X hasSubst_toddSeries_sub_one,
    ← coe_substAlgHom hasSubst_toddSeries_sub_one, map_one]
  ring

/-- Powers of `log Q` have no terms of low degree. -/
theorem coeff_logTodd_pow_of_lt {n d : ℕ} (h : n < d) : coeff n (logTodd ^ d) = 0 := by
  obtain ⟨g, hg⟩ := X_dvd_iff.mpr constantCoeff_logTodd
  rw [hg, mul_pow, coeff_X_pow_mul', ite_eq_right_iff]
  intro h'
  exact absurd h' (by omega)

/-- **`Q = exp (log Q)`, coefficient by coefficient**: the coefficient of `x^n` in the Todd
series is that of the truncated exponential `∑_{j ≤ n} (log Q)^j / j!`. -/
theorem coeff_toddSeries_eq_coeff_sum_logTodd_pow (n : ℕ) :
    coeff n toddSeries =
      coeff n (∑ j ∈ Finset.range (n + 1), ((j.factorial : ℚ)⁻¹) • logTodd ^ j) := by
  conv_lhs => rw [← exp_subst_logTodd, coeff_subst' hasSubst_logTodd]
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
  · rw [map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [coeff_exp, coeff_smul]
    simp
  · intro d hd
    simp only [Function.mem_support, ne_eq] at hd
    by_contra hd'
    simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hd'
    exact hd (by rw [coeff_logTodd_pow_of_lt (by omega), smul_zero])

end GRR
