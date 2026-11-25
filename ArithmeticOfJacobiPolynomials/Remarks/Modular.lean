/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.External
public import ArithmeticOfJacobiPolynomials.Galois.KanekoZagierGalois
public import ArithmeticOfJacobiPolynomials.Jacobi.IntegralNormalization
public import ArithmeticOfJacobiPolynomials.Jacobi.MonicEndpoint

/-!
# The modular normalization of §6.4 and (5.18)

Statements about the polynomials displayed in §5.4 and §6.4.
The modular-form assertions of §6.4 (the solutions `F_k`, their Fourier constant terms, and
the reduction to the supersingular polynomial [KZ, Theorem 1]) concern modular forms and are
not formalized; the statements below are the algebraic identities about the given
polynomials. Here `r = 2λ + 3μ`, `e = 6 + r` and `ℓ = 12n + e` ((6.4), §6.4), and
`F̃_{ℓ-1}(Y) = 1728^n P_n^{(λ/3,μ/2)}(1 - Y/864)` is `kanekoZagierModularPoly` ((6.5)).

* `kanekoZagierIndex_mem`: `e ∈ {1, 5, 7, 11}`;
* `kanekoZagierIndex_sub_one`: `k = ℓ - 1 = 12n + 4a + 6b` with `a = (λ+1)/2`, `b = (μ+1)/2`;
* `natDegree_kanekoZagierModularPoly`, `leadingCoeff_kanekoZagierModularPoly`: `F̃_{ℓ-1}` has
  degree `n` and leading coefficient `A_{n,r} = (-1)^n binom(2n + r/6, n)` ((6.6),
  §6.4);
* `kanekoZagier_two_mul_add_eq`: `2n + r/6 = ℓ/6 - 1`;
* `kanekoZagierLeading_sub_one_eq`: for prime `ℓ`, `A_{n,r} ≡ 1 (mod ℓ)`, in the form
  `A_{n,r} - 1 = ℓ a / b` with integers `a, b` and `ℓ ∤ b`;
* `kanekoZagierModularPoly_eq_integralJacobi`: `F̃_{ℓ-1}(Y) = (576^n/n!) K_n^{λ,μ}(-Y/3456)`
  ((5.18), §5.4), with `K_n^{λ,μ}` the integral normalization (5.17);
* `one_sub_pow_mul_legendreP_eval`: `(1-z)^m P_m((1+z)/(1-z)) = ∑_j binom(m,j)^2 z^j`
  (the Hasse-polynomial identity of §6.4; the supersingular interpretation [BM, §1] is cited
  literature and not formalized).
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

/-- **(6.4).** For `λ, μ ∈ {-1, 1}`, `e = 6 + 2λ + 3μ ∈ {1, 5, 7, 11}`. -/
theorem kanekoZagierIndex_mem {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) :
    6 + (2 * l + 3 * μ) ∈ ({1, 5, 7, 11} : Finset ℤ) := by
  rcases hl with rfl | rfl <;> rcases hμ with rfl | rfl <;> simp

/-- **§6.4.** With `a = (λ+1)/2` and `b = (μ+1)/2`, the weight `k = ℓ - 1` equals
`12n + 4a + 6b`. -/
theorem kanekoZagierIndex_sub_one {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (n : ℕ) : 12 * (n : ℤ) + (6 + (2 * l + 3 * μ)) - 1 =
      12 * n + 4 * ((l + 1) / 2) + 6 * ((μ + 1) / 2) := by
  rcases hl with rfl | rfl <;> rcases hμ with rfl | rfl <;> omega

/-- `binom(2n + λ/3 + μ/2, n) ≠ 0` for `μ ∈ {-1, 1}`. -/
theorem ring_choose_kanekoZagier_ne_zero {l μ : ℤ} (hμ : μ = 1 ∨ μ = -1) (n : ℕ) :
    Ring.choose (2 * (n : ℚ) + (l : ℚ) / 3 + (μ : ℚ) / 2) n ≠ 0 := by
  refine ring_choose_ne_zero_of_forall_ne_intCast (fun m hm => ?_) n
  have h6 : (6 * m : ℚ) = 12 * n + 2 * l + 3 * μ := by rw [← hm]; ring
  have h6' : 6 * m = 12 * (n : ℤ) + 2 * l + 3 * μ := by exact_mod_cast h6
  rcases hμ with rfl | rfl <;> omega

/-- The affine argument `1 - Y/864` of (6.5). -/
theorem natDegree_kanekoZagier_affine : (C (-1 / 864 : ℚ) * polyX + C 1).natDegree = 1 :=
  natDegree_linear (by norm_num)

/-- **(6.5)–(6.6).** `F̃_{ℓ-1}` has degree `n`. -/
theorem natDegree_kanekoZagierModularPoly {l μ : ℤ} (hμ : μ = 1 ∨ μ = -1) (n : ℕ) :
    (kanekoZagierModularPoly l μ n).natDegree = n := by
  rw [kanekoZagierModularPoly_eq, natDegree_C_mul (pow_ne_zero n (show (1728 : ℚ) ≠ 0 by norm_num)),
    natDegree_comp,
    natDegree_kanekoZagier_affine, mul_one, ← kanekoZagierJacobi_eq,
    natDegree_kanekoZagierJacobi hμ]

/-- **(6.6), §6.4.** The leading coefficient of `F̃_{ℓ-1}` is
`A_{n,r} = (-1)^n binom(2n + r/6, n)`, `r = 2λ + 3μ`. -/
theorem leadingCoeff_kanekoZagierModularPoly {l μ : ℤ} (hμ : μ = 1 ∨ μ = -1) (n : ℕ) :
    (kanekoZagierModularPoly l μ n).leadingCoeff =
      (-1) ^ n * Ring.choose (2 * (n : ℚ) + ((2 * l + 3 * μ : ℤ) : ℚ) / 6) n := by
  have hne := ring_choose_kanekoZagier_ne_zero (l := l) hμ n
  have hlq : (C (-1 / 864 : ℚ) * polyX + C 1).leadingCoeff = -1 / 864 :=
    leadingCoeff_linear (by norm_num)
  have hq0 : (C (-1 / 864 : ℚ) * polyX + C 1).natDegree ≠ 0 := by
    rw [natDegree_kanekoZagier_affine]; norm_num
  rw [kanekoZagierModularPoly_eq, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_comp hq0, hlq,
    leadingCoeff_jacobiP _ _ n hne, natDegree_jacobiP _ _ n hne]
  have e : 2 * (n : ℚ) + ((2 * l + 3 * μ : ℤ) : ℚ) / 6 = 2 * n + (l : ℚ) / 3 + (μ : ℚ) / 2 := by
    push_cast; ring
  rw [e]
  have h1 : (1728 : ℚ) ^ n * (1 / 2) ^ n * (-1 / 864) ^ n = (-1) ^ n := by
    rw [← mul_pow, ← mul_pow]; norm_num
  linear_combination Ring.choose (2 * (n : ℚ) + (l : ℚ) / 3 + (μ : ℚ) / 2) n * h1

/-- **§6.4.** `2n + r/6 = ℓ/6 - 1` for `ℓ = 12n + 6 + r`. -/
theorem kanekoZagier_two_mul_add_eq (n : ℕ) (r : ℤ) :
    2 * (n : ℚ) + (r : ℚ) / 6 = (12 * (n : ℚ) + 6 + r) / 6 - 1 := by
  ring

/-- **§6.4.** If the modular index `ℓ = 12n + 6 + 2λ + 3μ` is prime, then
`A_{n,r} = (-1)^n binom(2n + r/6, n) ≡ 1 (mod ℓ)`: `A_{n,r} - 1 = ℓ a / b` with `a, b ∈ ℤ`
and `ℓ ∤ b`. -/
theorem kanekoZagierLeading_sub_one_eq {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (n ℓ : ℕ) (hℓ : (ℓ : ℤ) = 12 * n + 6 + 2 * l + 3 * μ) (hp : ℓ.Prime) :
    ∃ a b : ℤ, ¬ (ℓ : ℤ) ∣ b ∧
      (-1 : ℚ) ^ n * Ring.choose (2 * (n : ℚ) + ((2 * l + 3 * μ : ℤ) : ℚ) / 6) n - 1 =
        ℓ * a / b := by
  set x : ℚ := 2 * (n : ℚ) + ((2 * l + 3 * μ : ℤ) : ℚ) / 6 with hx_def
  have hℓq : (ℓ : ℚ) = 12 * n + 6 + 2 * l + 3 * μ := by exact_mod_cast hℓ
  have hx : x = ((ℓ : ℚ) - 6) / 6 := by rw [hx_def, hℓq]; push_cast; ring
  have hf : ((n.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  -- `binom(x, n) n! = ∏_{j<n} (x - j)`
  have hc : Ring.choose x n * n.factorial = ∏ j ∈ range n, (x - j) := by
    rw [ring_choose_eq_ascPochhammer_div, div_mul_cancel₀ _ hf,
      ← descPochhammer_eval_eq_ascPochhammer, descPochhammer_eval_eq_prod_range]
  -- the integral polynomial `E(Y) = ∏_{j<n} (Y - 6(j+1))`
  set E : ℤ[X] := ∏ j ∈ range n, (polyX - C (6 * (j : ℤ) + 6)) with hE
  have hEl : ((E.eval (ℓ : ℤ) : ℤ) : ℚ) = 6 ^ n * ∏ j ∈ range n, (x - j) := by
    have h6 : (6 : ℚ) ^ n = ∏ _j ∈ range n, (6 : ℚ) := by rw [prod_const, card_range]
    rw [hE, eval_prod, Int.cast_prod, h6, ← prod_mul_distrib]
    refine prod_congr rfl fun j _ => ?_
    simp only [eval_sub, eval_X, eval_C]
    push_cast
    rw [hx]
    ring
  have hE0 : ((E.eval 0 : ℤ) : ℚ) = (-1) ^ n * 6 ^ n * n.factorial := by
    have hfac : ((n.factorial : ℕ) : ℚ) = ∏ j ∈ range n, ((j : ℚ) + 1) := by
      exact_mod_cast (prod_range_add_one_eq_factorial n).symm
    have h6 : ((-1 : ℚ) * 6) ^ n = ∏ _j ∈ range n, ((-1 : ℚ) * 6) := by
      rw [prod_const, card_range]
    rw [hE, eval_prod, Int.cast_prod, hfac, ← mul_pow, h6, ← prod_mul_distrib]
    refine prod_congr rfl fun j _ => ?_
    simp only [eval_sub, eval_X, eval_C]
    push_cast
    ring
  obtain ⟨a, ha⟩ := sub_dvd_eval_sub (ℓ : ℤ) 0 E
  have haq : ((E.eval (ℓ : ℤ) : ℤ) : ℚ) - ((E.eval 0 : ℤ) : ℚ) = ℓ * a := by
    rw [← Int.cast_sub, ha, sub_zero, Int.cast_mul, Int.cast_natCast]
  rw [hEl, hE0, ← hc] at haq
  refine ⟨(-1) ^ n * a, 6 ^ n * n.factorial, ?_, ?_⟩
  · -- `ℓ` divides neither `6^n` nor `n!`
    have h6 : ¬ ℓ ∣ 6 := by
      intro hd
      have hle := Nat.le_of_dvd (by norm_num) hd
      have hcases : ℓ = 1 ∨ ℓ = 5 := by
        rcases hl with rfl | rfl <;> rcases hμ with rfl | rfl <;> omega
      rcases hcases with rfl | rfl
      · exact Nat.not_prime_one hp
      · exact absurd hd (by norm_num)
    have hfl : ¬ ℓ ∣ n.factorial := by
      rw [hp.dvd_factorial]
      rcases hl with rfl | rfl <;> rcases hμ with rfl | rfl <;> omega
    have hnat : ¬ ℓ ∣ 6 ^ n * n.factorial := by
      intro hd
      rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
      · exact h6 (hp.dvd_of_dvd_pow h)
      · exact hfl h
    intro hd
    apply hnat
    have : ((ℓ : ℕ) : ℤ) ∣ ((6 ^ n * n.factorial : ℕ) : ℤ) := by push_cast; exact hd
    exact Int.natCast_dvd_natCast.mp this
  · have h6n : (6 : ℚ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    have hsq : ((-1 : ℚ) ^ n) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    push_cast
    rw [eq_div_iff (mul_ne_zero h6n hf)]
    linear_combination (-1 : ℚ) ^ n * haq + (6 ^ n * (n.factorial : ℚ)) * hsq

/-- **(5.18), §5.4.** `F̃_{ℓ-1}(Y) = (576^n/n!) K_n^{λ,μ}(-Y/3456)`, where
`K_n^{λ,μ}` is the integral normalization (5.8) with `(a, u, D, r) = (λ, 3, 6, 2λ + 3μ)`, so
that `K_n^{λ,μ}(X) = 3^n n! P_n^{(λ/3,μ/2)}(4X + 1)` ((5.17), §5.4). -/
theorem kanekoZagierModularPoly_eq_integralJacobi (l μ : ℤ) (n : ℕ) :
    kanekoZagierModularPoly l μ n = C ((576 : ℚ) ^ n / n.factorial) *
      ((integralJacobi l 3 6 (2 * l + 3 * μ) n).map (Int.castRingHom ℚ)).comp
        (C (-1 / 3456) * polyX) := by
  have h := integralJacobi_map l 3 6 (2 * l + 3 * μ) ((μ : ℚ) / 2) n (by norm_num)
    (by push_cast; ring)
  simp only [Int.cast_ofNat] at h
  rw [h, kanekoZagierModularPoly_eq, mul_comp, C_comp, comp_assoc, ← mul_assoc, ← C_mul]
  have hf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  congr 2
  · rw [eq_comm, div_mul_eq_mul_div, div_eq_iff hf, show (1728 : ℚ) = 576 * 3 by norm_num,
      mul_pow]
    ring
  · apply Polynomial.funext
    intro x
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_one, eval_comp]
    ring


/-- **§5.4, after (5.18): `F̃_{ℓ-1}` and `K_n^{λ,μ}` are irreducible together.** -/
theorem irreducible_kanekoZagierModularPoly_iff (l μ : ℤ) (n : ℕ) :
    Irreducible (kanekoZagierModularPoly l μ n) ↔
      Irreducible ((integralJacobi l 3 6 (2 * l + 3 * μ) n).map (Int.castRingHom ℚ)) := by
  rw [kanekoZagierModularPoly_eq_integralJacobi]
  have h : (C (-1 / 3456 : ℚ) * polyX : ℚ[X]) = C (-1 / 3456 : ℚ) * polyX + C 0 := by
    rw [C_0, add_zero]
  rw [h]
  exact irreducible_C_mul_comp_affine_iff _ (c := 0)
    (by positivity) (by norm_num)

/-- **§5.4, after (5.18): `F̃_{ℓ-1}` and `K_n^{λ,μ}` have isomorphic splitting fields over `ℚ`.**
Together with `irreducible_kanekoZagierModularPoly_iff` this is the sentence "these polynomials
therefore have the same irreducibility behavior and isomorphic splitting fields over `ℚ`". -/
noncomputable def kanekoZagierModularPolySplittingFieldEquiv (l μ : ℤ) (n : ℕ) :
    ((integralJacobi l 3 6 (2 * l + 3 * μ) n).map (Int.castRingHom ℚ)).SplittingField ≃ₐ[ℚ]
      (kanekoZagierModularPoly l μ n).SplittingField := by
  have h : kanekoZagierModularPoly l μ n = C ((576 : ℚ) ^ n / n.factorial) *
      ((integralJacobi l 3 6 (2 * l + 3 * μ) n).map (Int.castRingHom ℚ)).comp
        (C (-1 / 3456 : ℚ) * polyX + C 0) := by
    rw [C_0, add_zero]; exact kanekoZagierModularPoly_eq_integralJacobi l μ n
  rw [h]
  exact splittingFieldAffineEquiv _ 0 (by positivity) (by norm_num)

/-- **§6.4, the Hasse-polynomial identity.** For `z ≠ 1`,
`(1-z)^m P_m((1+z)/(1-z)) = ∑_{j=0}^m binom(m,j)^2 z^j`. -/
theorem one_sub_pow_mul_legendreP_eval (m : ℕ) {z : ℚ} (hz : z ≠ 1) :
    (1 - z) ^ m * (legendreP m).eval ((1 + z) / (1 - z)) =
      ∑ j ∈ range (m + 1), ((m.choose j : ℕ) : ℚ) ^ 2 * z ^ j := by
  have h1z : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hx1 : (1 + z) / (1 - z) - 1 = 2 * z / (1 - z) := by
    rw [eq_div_iff h1z, sub_mul, div_mul_cancel₀ _ h1z]; ring
  have hx2 : (1 + z) / (1 - z) + 1 = 2 / (1 - z) := by
    rw [eq_div_iff h1z, add_mul, div_mul_cancel₀ _ h1z]; ring
  rw [legendreP_eq, jacobiP_eq, eval_mul, eval_C, eval_finsetSum, mul_sum, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
  simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_add, eval_X, eval_one, add_zero]
  rw [hx1, hx2, Ring.choose_natCast, Ring.choose_natCast, Nat.choose_symm hjm]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hjm
  rw [show j + k - j = k by omega]
  have ea : (2 * z / (1 - z)) ^ j = 2 ^ j * z ^ j * ((1 - z)⁻¹) ^ j := by
    rw [div_eq_mul_inv, mul_pow, mul_pow]
  have eb : (2 / (1 - z)) ^ k = 2 ^ k * ((1 - z)⁻¹) ^ k := by
    rw [div_eq_mul_inv, mul_pow]
  have e1 : (1 - z) ^ j * ((1 - z)⁻¹) ^ j = 1 := by rw [← mul_pow, mul_inv_cancel₀ h1z, one_pow]
  have e2 : (1 - z) ^ k * ((1 - z)⁻¹) ^ k = 1 := by rw [← mul_pow, mul_inv_cancel₀ h1z, one_pow]
  have e3 : ((1 : ℚ) / 2) ^ j * 2 ^ j = 1 := by rw [← mul_pow]; norm_num
  have e4 : ((1 : ℚ) / 2) ^ k * 2 ^ k = 1 := by rw [← mul_pow]; norm_num
  rw [ea, eb]
  linear_combination ((((j + k).choose j : ℕ) : ℚ) ^ 2 * z ^ j) *
    (((1 - z) ^ k * ((1 - z)⁻¹) ^ k) * (((1 : ℚ) / 2) ^ j * 2 ^ j) *
      (((1 : ℚ) / 2) ^ k * 2 ^ k) * e1 +
    (((1 : ℚ) / 2) ^ j * 2 ^ j) * (((1 : ℚ) / 2) ^ k * 2 ^ k) * e2 +
    ((1 : ℚ) / 2) ^ k * 2 ^ k * e3 + e4)

end ArithmeticOfJacobiPolynomials
