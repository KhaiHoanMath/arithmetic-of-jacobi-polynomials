/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.SymmetricBridge
public import ArithmeticOfJacobiPolynomials.Jacobi.Endpoints
public import ArithmeticOfJacobiPolynomials.MainResults
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.FieldTheory.PolynomialGaloisGroup

/-!
# The Chebyshev specialization `α = β = -1/2` (remark after Theorem 1.6)

The manuscript remarks after Theorem 1.6: "Some restriction on the parameters is necessary: the
specialization `α = β = -1/2` gives Chebyshev polynomials [DLMF, (18.7.3)], whose zeros lie in
cyclotomic fields and whose Galois groups are abelian", and after Corollary 5.14 that the
denominator hypotheses "exclude the Chebyshev specializations".

* `jacobiP_neg_half_neg_half_eq`: `P_n^{(-1/2,-1/2)} = binom(n - 1/2, n) T_n`, where `T_n` is
  Mathlib's Chebyshev polynomial of the first kind (proved from the Jacobi and Chebyshev
  differential equations, not cited);
* `splits_chebyshevT_of_isPrimitiveRoot`, `splits_jacobiP_neg_half_neg_half`: for `n ≥ 1`,
  `T_n` and `P_n^{(-1/2,-1/2)}` split over every cyclotomic field `L = ℚ(ζ_{4n})`, the zeros
  being `(ζ^{2k+1} + ζ^{-(2k+1)})/2`, `0 ≤ k < n`;
* `jacobiP_neg_half_neg_half_gal_mul_comm_of_isCyclotomicExtension`: the Galois group of
  `P_n^{(-1/2,-1/2)}` over `ℚ` is abelian (a quotient of `Gal(L/ℚ)`); the instance with
  Mathlib's `CyclotomicField` is in
  `ArithmeticOfJacobiPolynomials.Remarks.ChebyshevCyclotomicField`;
* `not_even_den_neg_half_add_neg_half`: the reduced denominator of `α + β = -1` is `1`, which is
  odd, so the first clause of the denominator condition of Theorem 1.6
  (`JacobiDenominatorCondition`) fails;
* `not_jacobiDenominatorCondition_of_half`: the same for all four parameter pairs
  `α, β ∈ {±1/2}` (the Chebyshev families of the first to fourth kind).

The zeros and Galois groups of the other three kinds are in
`ArithmeticOfJacobiPolynomials.Remarks.ChebyshevKinds`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset
open Polynomial.Chebyshev (T T_zero T_one T_add_two T_eval_one map_T natDegree_T
  one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T)

/-! ### `P_n^{(-1/2,-1/2)}` is a multiple of `T_n` -/

/-- `T_n(2t+1)` satisfies the shifted Jacobi equation with `α = β = -1/2`. -/
theorem chebyshevT_comp_shift_ode (n : ℕ) :
    X * (X + 1) * derivative (derivative ((T ℚ n).comp (2 * X + 1))) +
      (C ((-1 / 2 : ℚ) + 1) + C ((-1 / 2 : ℚ) + (-1 / 2) + 2) * X) *
        derivative ((T ℚ n).comp (2 * X + 1)) =
      C ((n : ℚ) * (n + (-1 / 2) + (-1 / 2) + 1)) * (T ℚ n).comp (2 * X + 1) := by
  set T0 := T ℚ (n : ℤ) with hT0
  have hT := one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T (R := ℚ) (n : ℤ)
  rw [← hT0, Function.iterate_succ_apply, Function.iterate_one] at hT
  simp only [Int.cast_natCast] at hT
  have hz1 : derivative (T0.comp (2 * X + 1)) = 2 * (derivative T0).comp (2 * X + 1) := by
    rw [derivative_comp]; simp
  have hz2 : derivative (derivative (T0.comp (2 * X + 1))) =
      4 * (derivative (derivative T0)).comp (2 * X + 1) := by
    rw [hz1]; simp [derivative_comp]; ring
  have hTc := congrArg (fun p => p.comp (2 * X + 1)) hT
  simp only [mul_comp, sub_comp, one_comp, pow_comp, X_comp, natCast_comp] at hTc
  rw [hz2, hz1, show ((-1 / 2 : ℚ) + 1) = 1 / 2 by norm_num,
    show ((-1 / 2 : ℚ) + (-1 / 2) + 2) = 1 by norm_num,
    show (n : ℚ) * (n + (-1 / 2) + (-1 / 2) + 1) = n ^ 2 by ring]
  have hc2 : C (1 / 2 : ℚ) * 2 = 1 := by
    rw [← map_ofNat C 2, ← C_mul]; norm_num
  have hc1 : C (1 : ℚ) = 1 := C_1
  have hcn : C ((n : ℚ) ^ 2) = (n : ℚ[X]) ^ 2 := by simp
  linear_combination (-1 : ℚ[X]) * hTc + ((derivative T0).comp (2 * X + 1)) * hc2 +
    (2 * X * (derivative T0).comp (2 * X + 1)) * hc1 - (T0.comp (2 * X + 1)) * hcn

/-- **Remark after Theorem 1.6** ([DLMF, (18.7.3)], proved here):
`P_n^{(-1/2,-1/2)} = binom(n - 1/2, n) T_n`, with `T_n` the Chebyshev polynomial of the first
kind. -/
theorem jacobiP_neg_half_neg_half_eq (n : ℕ) :
    jacobiP (-1 / 2) (-1 / 2) n = C (Ring.choose ((n : ℚ) + (-1 / 2)) n) * T ℚ n := by
  have hy := jacobiP_shift_ode (-1 / 2 : ℚ) (-1 / 2) n
  have hz := chebyshevT_comp_shift_ode n
  have huniq := C_mul_eq_C_mul_of_shift_ode (by norm_num : (-1 : ℚ) < -1 / 2) hy hz
  have hz0 : ((T ℚ n).comp (2 * X + 1)).coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero, eval_comp]
    simp [T_eval_one]
  have hy0 : ((jacobiP (-1 / 2) (-1 / 2) n).comp (2 * X + 1)).coeff 0 =
      Ring.choose ((n : ℚ) + (-1 / 2)) n := by
    rw [coeff_zero_eq_eval_zero, eval_comp]
    have h1 : (2 * X + 1 : ℚ[X]).eval 0 = 1 := by simp
    rw [h1]
    exact jacobiP_eval_one _ _ n
  rw [hz0, hy0, C_1, one_mul] at huniq
  have hinv : (2 * X + 1 : ℚ[X]).comp (C (1 / 2) * (X - 1)) = X := by
    apply Polynomial.funext
    intro x
    simp
  calc jacobiP (-1 / 2) (-1 / 2) n =
        ((jacobiP (-1 / 2) (-1 / 2) n).comp (2 * X + 1)).comp (C (1 / 2) * (X - 1)) := by
          rw [comp_assoc, hinv, comp_X]
    _ = (C (Ring.choose ((n : ℚ) + (-1 / 2)) n) * (T ℚ n).comp (2 * X + 1)).comp
          (C (1 / 2) * (X - 1)) := by rw [huniq]
    _ = C (Ring.choose ((n : ℚ) + (-1 / 2)) n) * T ℚ n := by
          rw [mul_comp, C_comp, comp_assoc, hinv, comp_X]

/-! ### The zeros lie in a cyclotomic field -/

/-- `T_m((z + z⁻¹)/2) = (z^m + z^{-m})/2`. -/
theorem chebyshevT_eval_half_add_inv {K : Type*} [Field K] [CharZero K] {z : K} (hz : z ≠ 0)
    (m : ℕ) : (T K m).eval ((z + z⁻¹) / 2) = (z ^ m + z⁻¹ ^ m) / 2 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | _ | m
    · norm_num [T_zero]
    · simp [T_one]
    · have h1 := ih (m + 1) (by omega)
      have h0 := ih m (by omega)
      have hT : T K ((m + 1 + 1 : ℕ) : ℤ) = 2 * X * T K ((m + 1 : ℕ) : ℤ) - T K (m : ℤ) := by
        have h := T_add_two (R := K) (m : ℤ)
        rw [show (m : ℤ) + 2 = ((m + 1 + 1 : ℕ) : ℤ) by push_cast; ring,
          show (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) by push_cast; ring] at h
        exact h
      rw [hT, eval_sub, eval_mul, eval_mul, eval_X, h1, h0, eval_ofNat]
      set w := z⁻¹ with hw
      have hzw : z * w = 1 := mul_inv_cancel₀ hz
      linear_combination ((w ^ m + z ^ m) / 2) * hzw

/-- For a primitive `4n`-th root of unity `ζ` and every `k`, `(ζ^{2k+1} + ζ^{-(2k+1)})/2` is a
root of `T_n`. -/
theorem isRoot_chebyshevT_of_isPrimitiveRoot {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (hn : 1 ≤ n) {ζ : K} (hζ : IsPrimitiveRoot ζ (4 * n)) (k : ℕ) :
    (T K n).IsRoot ((ζ ^ (2 * k + 1) + (ζ ^ (2 * k + 1))⁻¹) / 2) := by
  have hz : ζ ^ (2 * k + 1) ≠ 0 := pow_ne_zero _ (hζ.ne_zero (by omega))
  rw [IsRoot.def, chebyshevT_eval_half_add_inv hz, inv_pow]
  have hi : ζ ^ (2 * n) = -1 :=
    (hζ.pow (by omega) (show 4 * n = 2 * n * 2 by ring)).eq_neg_one_of_two_right
  set w := (ζ ^ (2 * k + 1)) ^ n with hw
  have hw2 : w ^ 2 = -1 := by
    have e : w ^ 2 = (ζ ^ (2 * n)) ^ (2 * k + 1) := by
      rw [hw]
      simp only [← pow_mul]
      congr 1
      ring
    rw [e, hi, Odd.neg_one_pow ⟨k, rfl⟩]
  have hinv : w⁻¹ = -w := by
    apply inv_eq_of_mul_eq_one_right
    rw [mul_neg, ← sq, hw2, neg_neg]
  rw [hinv, add_neg_cancel, zero_div]

/-- **Remark after Theorem 1.6.** If a field `L ⊇ ℚ` contains a primitive `4n`-th root of
unity `ζ` (`n ≥ 1`), then `T_n` splits over `L`, and its `n` distinct zeros are
`(ζ^{2k+1} + ζ^{-(2k+1)})/2`, `0 ≤ k < n`. -/
theorem splits_chebyshevT_of_isPrimitiveRoot {L : Type*} [Field L] [Algebra ℚ L] (n : ℕ)
    (hn : 1 ≤ n) {ζ : L} (hζ : IsPrimitiveRoot ζ (4 * n)) :
    ((T ℚ n).map (algebraMap ℚ L)).Splits ∧
      ∀ y : L, ((T ℚ n).map (algebraMap ℚ L)).IsRoot y →
        ∃ k < n, y = (ζ ^ (2 * k + 1) + (ζ ^ (2 * k + 1))⁻¹) / 2 := by
  classical
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  rw [map_T]
  have hdeg : (T L n).natDegree = n := by simp [natDegree_T]
  have hT0 : T L n ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  set x : ℕ → L := fun k => (ζ ^ (2 * k + 1) + (ζ ^ (2 * k + 1))⁻¹) / 2 with hx
  have hinj : Set.InjOn x (range n) := by
    intro k₁ hk₁' k₂ hk₂' h
    have hk₁ := mem_range.mp (mem_coe.mp hk₁')
    have hk₂ := mem_range.mp (mem_coe.mp hk₂')
    have ha0 : ζ ^ (2 * k₁ + 1) ≠ 0 := pow_ne_zero _ (hζ.ne_zero (by omega))
    have hb0 : ζ ^ (2 * k₂ + 1) ≠ 0 := pow_ne_zero _ (hζ.ne_zero (by omega))
    simp only [hx] at h
    set a := ζ ^ (2 * k₁ + 1) with ha
    set b := ζ ^ (2 * k₂ + 1) with hb
    have haa : a * a⁻¹ = 1 := mul_inv_cancel₀ ha0
    have hbb : b * b⁻¹ = 1 := mul_inv_cancel₀ hb0
    have key : (a - b) * (a * b - 1) = 0 := by
      linear_combination (2 * a * b) * h - b * haa + a * hbb
    rcases mul_eq_zero.mp key with h1 | h1
    · have hab : ζ ^ (2 * k₁ + 1) = ζ ^ (2 * k₂ + 1) := sub_eq_zero.mp h1
      have := hζ.pow_inj (by omega) (by omega) hab
      omega
    · have hab : ζ ^ (2 * k₁ + 1 + (2 * k₂ + 1)) = 1 := by
        rw [pow_add]; exact sub_eq_zero.mp h1
      have hd := hζ.dvd_of_pow_eq_one _ hab
      have := Nat.le_of_dvd (by omega) hd
      omega
  have hsub : (range n).image x ⊆ (T L n).roots.toFinset := by
    intro y hy
    obtain ⟨k, -, rfl⟩ := mem_image.mp hy
    rw [Multiset.mem_toFinset, mem_roots hT0]
    exact isRoot_chebyshevT_of_isPrimitiveRoot hn hζ k
  have hcard_img : ((range n).image x).card = n := by rw [card_image_of_injOn hinj, card_range]
  have hle : (T L n).roots.toFinset.card ≤ n :=
    (Multiset.toFinset_card_le _).trans ((card_roots' _).trans hdeg.le)
  have heq : (range n).image x = (T L n).roots.toFinset :=
    eq_of_subset_of_card_le hsub (by rw [hcard_img]; exact hle)
  have hcard : n ≤ Multiset.card (T L n).roots := by
    calc n = ((range n).image x).card := hcard_img.symm
      _ ≤ (T L n).roots.toFinset.card := card_le_card hsub
      _ ≤ Multiset.card (T L n).roots := Multiset.toFinset_card_le _
  refine ⟨?_, fun y hy => ?_⟩
  · rw [splits_iff_card_roots, hdeg]
    exact le_antisymm ((card_roots' _).trans hdeg.le) hcard
  · have hy' : y ∈ (T L n).roots.toFinset := by
      rw [Multiset.mem_toFinset, mem_roots hT0]; exact hy
    rw [← heq] at hy'
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hy'
    exact ⟨k, mem_range.mp hk, rfl⟩

/-- **Remark after Theorem 1.6.** For `n ≥ 1`, `P_n^{(-1/2,-1/2)}` splits over every
cyclotomic field `ℚ(ζ_{4n})`: its zeros lie in a cyclotomic field. -/
theorem splits_jacobiP_neg_half_neg_half (n : ℕ) (hn : 1 ≤ n) (L : Type*) [Field L]
    [Algebra ℚ L] [IsCyclotomicExtension {4 * n} ℚ L] :
    ((jacobiP (-1 / 2) (-1 / 2) n).map (algebraMap ℚ L)).Splits := by
  have : NeZero (4 * n) := ⟨by omega⟩
  rw [jacobiP_neg_half_neg_half_eq, Polynomial.map_mul, Polynomial.map_C]
  exact (splits_chebyshevT_of_isPrimitiveRoot n hn
    (IsCyclotomicExtension.zeta_spec (4 * n) ℚ L)).1.C_mul _

/-- **Remark after Theorem 1.6.** For `n ≥ 1`, the Galois group of `P_n^{(-1/2,-1/2)}` over `ℚ`
is abelian, as a quotient of the abelian group `Gal(L/ℚ)` of any cyclotomic field
`L = ℚ(ζ_{4n})` (see `jacobiP_neg_half_neg_half_gal_mul_comm` for the unconditional form). -/
theorem jacobiP_neg_half_neg_half_gal_mul_comm_of_isCyclotomicExtension (n : ℕ) (hn : 1 ≤ n)
    (L : Type*) [Field L] [Algebra ℚ L] [IsCyclotomicExtension {4 * n} ℚ L]
    (σ τ : (jacobiP (-1 / 2) (-1 / 2) n).Gal) : σ * τ = τ * σ := by
  have : Fact ((jacobiP (-1 / 2) (-1 / 2) n).map (algebraMap ℚ L)).Splits :=
    ⟨splits_jacobiP_neg_half_neg_half n hn L⟩
  have : IsGalois ℚ L := IsCyclotomicExtension.isGalois (S := {4 * n}) (K := ℚ) (L := L)
  have : IsMulCommutative (L ≃ₐ[ℚ] L) :=
    IsCyclotomicExtension.isMulCommutative (S := {4 * n}) (A := ℚ) (B := L)
  obtain ⟨a, rfl⟩ := Gal.restrict_surjective (p := jacobiP (-1 / 2) (-1 / 2) n) (E := L) σ
  obtain ⟨b, rfl⟩ := Gal.restrict_surjective (p := jacobiP (-1 / 2) (-1 / 2) n) (E := L) τ
  have hab : a * b = b * a := IsMulCommutative.is_comm.comm a b
  rw [← map_mul, hab, map_mul]

/-! ### The denominator condition fails -/

/-- For `α = β = -1/2`, the reduced denominator of `α + β = -1` is `1`. -/
theorem den_neg_half_add_neg_half : ((-1 / 2 : ℚ) + (-1 / 2)).den = 1 := by
  rw [show (-1 / 2 : ℚ) + (-1 / 2) = -1 by norm_num]
  simp

/-- **Remark after Corollary 5.14.** The denominator hypotheses of Theorem 1.6 exclude the
Chebyshev specialization: for `α = β = -1/2` the reduced denominator of `α + β` is odd. -/
theorem not_even_den_neg_half_add_neg_half : ¬ Even ((-1 / 2 : ℚ) + (-1 / 2)).den := by
  rw [den_neg_half_add_neg_half]
  exact Nat.not_even_one

/-- The denominator condition of Theorem 1.6 fails for the Chebyshev parameters
`α = β = -1/2`. -/
theorem not_jacobiDenominatorCondition_neg_half :
    ¬ JacobiDenominatorCondition (-1 / 2) (-1 / 2) := fun h =>
  not_even_den_neg_half_add_neg_half h.1

/-- **The denominator hypotheses exclude every specialization `α, β ∈ {±1/2}`.** These are the
parameters of the four Chebyshev families (`P_n^{(∓1/2, ∓1/2)}`, `P_n^{(∓1/2, ±1/2)}`: first to
fourth kind, [DLMF, §18.7(i)]): `α + β ∈ {-1, 0, 1}` is an integer, so its reduced denominator is
`1`, which is odd. -/
theorem not_jacobiDenominatorCondition_of_half (α β : ℚ) (hα : α = 1 / 2 ∨ α = -1 / 2)
    (hβ : β = 1 / 2 ∨ β = -1 / 2) : ¬ JacobiDenominatorCondition α β := by
  intro h
  have h1 := h.1
  rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl <;> norm_num at h1

end ArithmeticOfJacobiPolynomials
