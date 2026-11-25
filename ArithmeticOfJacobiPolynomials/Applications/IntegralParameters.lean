/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Jacobi.UnequalIrreducibility
public import ArithmeticOfJacobiPolynomials.Jacobi.Endpoints
public import ArithmeticOfJacobiPolynomials.MainResults

/-!
# Integral parameters (Corollary 6.1)

For integers `a, b` put `a_- = max{-a, 0}` and `b_- = max{-b, 0}` (in Lean `(-a).toNat`,
`(-b).toNat`). Negative integral parameters contribute endpoint factors:

* `ArithmeticOfJacobiPolynomials.jacobiP_neg_left`: for `A, b ≥ 0`, `n = A + p`, the binomial
formula gives
  `P_n^{(-A,b)} = (n-A)!(n+b)!/(n!(n-A+b)!) ((x-1)/2)^A P_{n-A}^{(A,b)}`;
* `ArithmeticOfJacobiPolynomials.jacobiP_neg_neg`: for `A, B ≥ 0`, `n = A + B + p`,
  `P_n^{(-A,-B)} = ((x-1)/2)^A ((x+1)/2)^B P_{n-A-B}^{(A,B)}`;
* `ArithmeticOfJacobiPolynomials.exists_jacobiP_int_eq`: in all four sign cases (with reflection
for a negative
  second parameter), for `n ≥ a_- + b_-`,
  `P_n^{(a,b)} = (x-1)^{a_-} (x+1)^{b_-} · c P_{n-a_--b_-}^{(|a|,|b|)}` with `c ≠ 0`;
* `ArithmeticOfJacobiPolynomials.exists_forall_integralParameters_irreducible`: the degree and
irreducibility
  assertions of **Corollary 6.1**, from Theorem 1.3;
* `ArithmeticOfJacobiPolynomials.integralParametersStatement_of_galois`: **Corollary 6.1** in full,
given the
  `S_n` assertion of Theorem 1.3 as an explicit hypothesis (an intermediate step;
  `integralParametersStatement` discharges it using that assertion).

The irreducibility input is `exists_forall_irreducible_jacobiP`, conditional on the cited
`HansonLcmBound`, `JacobiSimpleRealZeros`.
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

/-- `Ring.choose (n - A) k` at the natural number `n - A`, for `A ≤ n`. -/
private lemma ringChoose_natCast_add_neg {n A : ℕ} (h : A ≤ n) (k : ℕ) :
    Ring.choose ((n : ℚ) + -(A : ℚ)) k = ((n - A).choose k : ℚ) := by
  rw [show (n : ℚ) + -(A : ℚ) = ((n - A : ℕ) : ℚ) by push_cast [Nat.cast_sub h]; ring,
    Ring.choose_natCast]

private lemma ringChoose_natCast_add_natCast (n b k : ℕ) :
    Ring.choose ((n : ℚ) + (b : ℚ)) k = ((n + b).choose k : ℚ) := by
  rw [← Nat.cast_add, Ring.choose_natCast]

/-- The factorial identity behind `jacobiP_neg_left`. -/
private lemma neg_left_coeff (A b p i : ℕ) (hi : i ≤ p) :
    (1 / 2 : ℚ) ^ (A + p) * ((p.choose i : ℚ) * ((A + p + b).choose (A + i) : ℚ)) =
      ((p.factorial : ℚ) * ((A + p + b).factorial : ℚ) /
          (((A + p).factorial : ℚ) * ((p + b).factorial : ℚ)) * (1 / 2) ^ A) *
        ((1 / 2) ^ p * (((A + p).choose (A + i) : ℚ) * ((p + b).choose i : ℚ))) := by
  rw [Nat.cast_choose ℚ hi, Nat.cast_choose ℚ (show A + i ≤ A + p + b by omega),
    Nat.cast_choose ℚ (show A + i ≤ A + p by omega), Nat.cast_choose ℚ (show i ≤ p + b by omega),
    show A + p + b - (A + i) = p + b - i by omega, show A + p - (A + i) = p - i by omega,
    pow_add]
  field_simp

/-- **Binomial formula, negative first parameter.** For `A, b ≥ 0` and `n = A + p`,
`P_n^{(-A,b)} = (n-A)!(n+b)!/(n!(n-A+b)!) · ((x-1)/2)^A · P_{n-A}^{(A,b)}`. -/
theorem jacobiP_neg_left (A b p : ℕ) :
    jacobiP (-(A : ℚ)) b (A + p) =
      C ((p.factorial : ℚ) * ((A + p + b).factorial : ℚ) /
          (((A + p).factorial : ℚ) * ((p + b).factorial : ℚ)) * (1 / 2) ^ A) *
        (polyX - 1) ^ A * jacobiP A b p := by
  set K : ℚ := (p.factorial : ℚ) * ((A + p + b).factorial : ℚ) /
    (((A + p).factorial : ℚ) * ((p + b).factorial : ℚ)) * (1 / 2) ^ A with hK
  rw [jacobiP_eq, jacobiP_eq, show A + p + 1 = A + (p + 1) by ring, sum_range_add _ A (p + 1)]
  have hzero : ∑ j ∈ range A, C (Ring.choose (((A + p : ℕ) : ℚ) + -(A : ℚ)) (A + p - j) *
      Ring.choose (((A + p : ℕ) : ℚ) + (b : ℚ)) j) * (polyX - 1) ^ j * (polyX + 1) ^ (A + p - j)
        = 0 := by
    refine sum_eq_zero fun j hj => ?_
    have hj : j < A := mem_range.mp hj
    rw [ringChoose_natCast_add_neg (n := A + p) (A := A) (by omega),
      Nat.choose_eq_zero_of_lt (by omega)]
    simp
  rw [hzero, zero_add]
  simp only [mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hi : i ≤ p := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have hcoef := neg_left_coeff A b p i hi
  rw [← hK] at hcoef
  rw [ringChoose_natCast_add_neg (n := A + p) (A := A) (by omega)]
  simp only [ringChoose_natCast_add_natCast]
  rw [show A + p - A = p by omega, show A + p - (A + i) = p - i by omega, Nat.choose_symm hi,
    show p + A = A + p by ring,
    Nat.choose_symm_of_eq_add (show A + p = (p - i) + (A + i) by omega)]
  calc C ((1 / 2 : ℚ) ^ (A + p)) * (C ((p.choose i : ℚ) * ((A + p + b).choose (A + i) : ℚ)) *
          (polyX - 1) ^ (A + i) * (polyX + 1) ^ (p - i))
      = C ((1 / 2 : ℚ) ^ (A + p) * ((p.choose i : ℚ) * ((A + p + b).choose (A + i) : ℚ))) *
          ((polyX - 1) ^ (A + i) * (polyX + 1) ^ (p - i)) := by simp only [C_mul]; ring
    _ = C (K * ((1 / 2) ^ p * (((A + p).choose (A + i) : ℚ) * ((p + b).choose i : ℚ)))) *
          ((polyX - 1) ^ (A + i) * (polyX + 1) ^ (p - i)) := by rw [hcoef]
    _ = _ := by simp only [C_mul, pow_add]; ring

/-- **Binomial formula, both parameters negative.** For `A, B ≥ 0` and `n = A + B + p`,
`P_n^{(-A,-B)} = ((x-1)/2)^A ((x+1)/2)^B P_{n-A-B}^{(A,B)}`. -/
theorem jacobiP_neg_neg (A B p : ℕ) :
    jacobiP (-(A : ℚ)) (-(B : ℚ)) (A + B + p) =
      C ((1 / 2 : ℚ) ^ (A + B)) * (polyX - 1) ^ A * (polyX + 1) ^ B * jacobiP A B p := by
  rw [jacobiP_eq, jacobiP_eq, show A + B + p + 1 = A + ((p + 1) + B) by ring,
    sum_range_add _ A (p + 1 + B), sum_range_add _ (p + 1) B]
  have hzero1 : ∑ j ∈ range A, C (Ring.choose (((A + B + p : ℕ) : ℚ) + -(A : ℚ)) (A + B + p - j) *
      Ring.choose (((A + B + p : ℕ) : ℚ) + -(B : ℚ)) j) * (polyX - 1) ^ j *
        (polyX + 1) ^ (A + B + p - j) = 0 := by
    refine sum_eq_zero fun j hj => ?_
    have hj : j < A := mem_range.mp hj
    rw [ringChoose_natCast_add_neg (n := A + B + p) (A := A) (by omega),
      Nat.choose_eq_zero_of_lt (by omega)]
    simp
  have hzero2 : ∑ k ∈ range B, C (Ring.choose (((A + B + p : ℕ) : ℚ) + -(A : ℚ))
      (A + B + p - (A + (p + 1 + k))) *
      Ring.choose (((A + B + p : ℕ) : ℚ) + -(B : ℚ)) (A + (p + 1 + k))) *
        (polyX - 1) ^ (A + (p + 1 + k)) * (polyX + 1) ^ (A + B + p - (A + (p + 1 + k))) = 0 := by
    refine sum_eq_zero fun k _ => ?_
    rw [ringChoose_natCast_add_neg (n := A + B + p) (A := B) (by omega) (A + (p + 1 + k)),
      Nat.choose_eq_zero_of_lt (by omega)]
    simp
  rw [hzero1, hzero2, zero_add, add_zero]
  simp only [mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hi : i ≤ p := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [ringChoose_natCast_add_neg (n := A + B + p) (A := A) (by omega),
    ringChoose_natCast_add_neg (n := A + B + p) (A := B) (by omega)]
  simp only [ringChoose_natCast_add_natCast]
  rw [show A + B + p - (A + i) = B + (p - i) by omega,
    show A + B + p - A = B + p by omega, show A + B + p - B = A + p by omega,
    Nat.choose_symm_of_eq_add (show B + p = (B + (p - i)) + i by omega),
    Nat.choose_symm_of_eq_add (show A + p = (A + i) + (p - i) by omega),
    show p + A = A + p by ring, show p + B = B + p by ring]
  simp only [C_mul, pow_add]
  ring

/-- Reflection in the form `P_n^{(α,β)}(x) = (-1)^n P_n^{(β,α)}(-x)`. -/
theorem jacobiP_eq_C_mul_comp_neg_X (α β : ℚ) (n : ℕ) :
    jacobiP α β n = C ((-1) ^ n) * (jacobiP β α n).comp (-polyX) := by
  rw [jacobiP_comp_neg_X, ← mul_assoc, ← C_mul, ← mul_pow]
  norm_num

/-- The constant of `jacobiP_neg_left` is nonzero. -/
private lemma neg_left_const_ne_zero (A b p : ℕ) :
    (p.factorial : ℚ) * ((A + p + b).factorial : ℚ) /
      (((A + p).factorial : ℚ) * ((p + b).factorial : ℚ)) * (1 / 2) ^ A ≠ 0 := by
  positivity

/-- **Reduction for integral parameters.** For integers `a, b` and `n ≥ a_- + b_-`,
`P_n^{(a,b)} = (x-1)^{a_-} (x+1)^{b_-} · c P_{n-a_--b_-}^{(|a|,|b|)}` for some `c ≠ 0`. -/
theorem exists_jacobiP_int_eq (a b : ℤ) (n : ℕ) (hn : (-a).toNat + (-b).toNat ≤ n) :
    ∃ c : ℚ, c ≠ 0 ∧ jacobiP a b n = (polyX - 1) ^ (-a).toNat * (polyX + 1) ^ (-b).toNat *
      (C c * jacobiP a.natAbs b.natAbs (n - (-a).toNat - (-b).toNat)) := by
  obtain ⟨A, rfl | rfl⟩ := Int.eq_nat_or_neg a <;> obtain ⟨B, rfl | rfl⟩ := Int.eq_nat_or_neg b
  · refine ⟨1, one_ne_zero, ?_⟩
    simp
  · simp only [Int.toNat_neg_natCast, neg_neg, Int.toNat_natCast, Int.natAbs_natCast,
      Int.natAbs_neg, zero_add, pow_zero, one_mul, Nat.sub_zero, Int.cast_natCast,
      Int.cast_neg] at hn ⊢
    obtain ⟨p, rfl⟩ : ∃ p, n = B + p := ⟨n - B, by omega⟩
    refine ⟨(-1) ^ (B + p) * ((p.factorial : ℚ) * ((B + p + A).factorial : ℚ) /
      (((B + p).factorial : ℚ) * ((p + A).factorial : ℚ)) * (1 / 2) ^ B) * (-1) ^ B * (-1) ^ p,
      mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
        (neg_left_const_ne_zero B A p)) (pow_ne_zero _ (by norm_num)))
        (pow_ne_zero _ (by norm_num)), ?_⟩
    rw [jacobiP_eq_C_mul_comp_neg_X (A : ℚ) (-(B : ℚ)) (B + p), jacobiP_neg_left B A p,
      mul_comp, mul_comp, C_comp, pow_comp, sub_comp, X_comp, one_comp,
      jacobiP_comp_neg_X, show B + p - B = p by omega]
    have h1 : (-polyX - 1 : ℚ[X]) = C (-1) * (polyX + 1) := by simp; ring
    rw [h1, mul_pow, ← C_pow]
    simp only [C_mul]
    ring
  · simp only [Int.toNat_neg_natCast, neg_neg, Int.toNat_natCast, Int.natAbs_natCast,
      Int.natAbs_neg, add_zero, pow_zero, mul_one, Nat.sub_zero, Int.cast_natCast,
      Int.cast_neg] at hn ⊢
    obtain ⟨p, rfl⟩ : ∃ p, n = A + p := ⟨n - A, by omega⟩
    refine ⟨(p.factorial : ℚ) * ((A + p + B).factorial : ℚ) /
      (((A + p).factorial : ℚ) * ((p + B).factorial : ℚ)) * (1 / 2) ^ A,
      neg_left_const_ne_zero A B p, ?_⟩
    rw [jacobiP_neg_left, show A + p - A = p by omega]
    ring
  · simp only [neg_neg, Int.toNat_natCast, Int.natAbs_neg, Int.natAbs_natCast,
      Int.cast_natCast, Int.cast_neg] at hn ⊢
    obtain ⟨p, rfl⟩ : ∃ p, n = A + B + p := ⟨n - A - B, by omega⟩
    refine ⟨(1 / 2 : ℚ) ^ (A + B), by positivity, ?_⟩
    rw [jacobiP_neg_neg, show A + B + p - A - B = p by omega]
    ring

/-- The monic endpoint factor `(x-1)^{a_-} (x+1)^{b_-}`. -/
theorem monic_endpointFactor (a b : ℤ) :
    ((polyX - 1 : ℚ[X]) ^ (-a).toNat * (polyX + 1) ^ (-b).toNat).Monic := by
  have h1 : ((polyX - 1 : ℚ[X]) ^ (-a).toNat).Monic := by
    simpa using (monic_X_sub_C (1 : ℚ)).pow (-a).toNat
  have h2 : ((polyX + 1 : ℚ[X]) ^ (-b).toNat).Monic := by
    simpa using (monic_X_add_C (1 : ℚ)).pow (-b).toNat
  exact h1.mul h2

/-- **Reduction for integral parameters, quotient form.** For `n ≥ a_- + b_-`,
`P_n^{(a,b)} / ((x-1)^{a_-} (x+1)^{b_-}) = c P_{n-a_--b_-}^{(|a|,|b|)}` for some `c ≠ 0`. -/
theorem exists_jacobiP_int_divByMonic_eq (a b : ℤ) (n : ℕ)
    (hn : (-a).toNat + (-b).toNat ≤ n) :
    ∃ c : ℚ, c ≠ 0 ∧ jacobiP a b n /ₘ ((polyX - 1) ^ (-a).toNat * (polyX + 1) ^ (-b).toNat) =
      C c * jacobiP a.natAbs b.natAbs (n - (-a).toNat - (-b).toNat) := by
  obtain ⟨c, hc, h⟩ := exists_jacobiP_int_eq a b n hn
  exact ⟨c, hc, by rw [h, mul_divByMonic_cancel_left _ (monic_endpointFactor a b)]⟩

/-- **Corollary 6.1, degree and irreducibility.** For integers
`a, b` with `|a| ≠ |b|`, for all sufficiently large `n` the polynomial
`g = P_n^{(a,b)} / ((x-1)^{a_-}(x+1)^{b_-})` has degree `n - a_- - b_-` and is irreducible
over `ℚ`. Conditional on the literature inputs of Theorem 1.3. -/
theorem exists_forall_integralParameters_irreducible (hH : HansonLcmBound)
     (hZ : JacobiSimpleRealZeros) (a b : ℤ) (hab : |a| ≠ |b|) :
    ∃ N : ℕ, ∀ n ≥ N,
      let g := jacobiP a b n /ₘ ((polyX - 1) ^ (-a).toNat * (polyX + 1) ^ (-b).toNat)
      g.natDegree = n - (-a).toNat - (-b).toNat ∧ Irreducible g := by
  have hab' : a.natAbs ≠ b.natAbs := by
    intro h; apply hab; rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs, h]
  obtain ⟨N₀, hN₀⟩ := exists_forall_irreducible_jacobiP hH hZ hab'
  refine ⟨N₀ + (-a).toNat + (-b).toNat, fun n hn => ?_⟩
  obtain ⟨c, hc, h⟩ := exists_jacobiP_int_divByMonic_eq a b n (by omega)
  dsimp only
  rw [h, natDegree_C_mul hc, natDegree_jacobiP_nat]
  refine ⟨rfl, ?_⟩
  rw [irreducible_isUnit_mul (isUnit_C.mpr (Ne.isUnit hc))]
  exact hN₀ _ (by omega)

/-- `Gal = S_n` is invariant under multiplication by a nonzero constant. -/
theorem GaloisGroupIsSymmetric.C_mul {f : ℚ[X]} {c : ℚ} (hc : c ≠ 0)
    (hf : GaloisGroupIsSymmetric f) : GaloisGroupIsSymmetric (C c * f) := by
  have h := GaloisGroupIsSymmetric.affine f (0 : ℚ) hc one_ne_zero hf
  simpa using h

/-- **Corollary 6.1**, given the `S_n` assertion of Theorem 1.3 as
the explicit hypothesis `hGal` (`integralParametersStatement` discharges `hGal` using the Galois
assertion of Theorem 1.3). -/
theorem integralParametersStatement_of_galois (hH : HansonLcmBound)
     (hZ : JacobiSimpleRealZeros)
    (hGal : ∀ a b : ℕ, a ≠ b → ∃ N : ℕ, ∀ n ≥ N, GaloisGroupIsSymmetric (jacobiP a b n)) :
    IntegralParametersStatement := by
  unfold IntegralParametersStatement
  intro a b hab
  have hab' : a.natAbs ≠ b.natAbs := by
    intro h; apply hab; rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs, h]
  obtain ⟨N₁, hN₁⟩ := exists_forall_integralParameters_irreducible hH hZ a b hab
  obtain ⟨N₂, hN₂⟩ := hGal _ _ hab'
  refine ⟨N₁ + N₂ + (-a).toNat + (-b).toNat, fun n hn => ?_⟩
  have h₁ := hN₁ n (by omega)
  dsimp only at h₁ ⊢
  obtain ⟨hdeg, hirr⟩ := h₁
  obtain ⟨c, hc, h⟩ := exists_jacobiP_int_divByMonic_eq a b n (by omega)
  refine ⟨hdeg, hirr, ?_⟩
  rw [h]
  exact (hN₂ _ (by omega)).C_mul hc

end ArithmeticOfJacobiPolynomials
