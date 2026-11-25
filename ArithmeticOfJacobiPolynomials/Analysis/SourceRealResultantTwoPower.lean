/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Analysis.RealResultant

/-!
# The power of `2` in the proof of Lemma 2.6, as in the manuscript

The proof of Lemma 2.6 replaces `-log b_h` by `log κ - (c_F + c_G) log 2` as follows.

> Write `κ = 2^k/c`, with `c` positive and odd. Since `h ∈ ℤ[1/2][x]` and `H` is primitive, `c`
> divides the odd part of `b_h`. If `t_2` is the minimum binary coefficient valuation of
> `h(2X+1)`, Gauss multiplicativity gives `c_F + c_G = k + t_2`, whereas `t_2 ≤ v_2(b_h)`. Thus
> `log κ - (c_F + c_G) log 2 = -log c - t_2 log 2 ≥ -log b_h`.

This file follows that sequence.

* `exists_kappa_form`: `κ = 2^k / c` with `c` odd, from `h ∈ ℤ[1/2][x]` and primitivity of `H`;
* `odd_dvd_of_kappa`: `c ∣ b_h`;
* `shiftedTwoAdicOrder_mul`: Gauss multiplicativity, `c_{FG} = c_F + c_G`;
* `exists_shift_form`: `h(2X+1) = 2^{t_2} T₂` with `T₂ ∈ ℤ[X]` having an odd coefficient, which says
  that `t_2` is the minimum binary coefficient valuation of `h(2X+1)`;
* `shiftedTwoAdicOrder_add_eq`: `c_F + c_G = k + t_2`;
* `two_pow_mul_le_of_source`: `c · 2^{t_2} ≤ b_h` (so `t_2 ≤ v_2(b_h)` and `c ∣ b_h`), and the
  consequence `2^{c_F + c_G} ≤ κ b_h`, i.e. `log κ - (c_F + c_G) log 2 ≥ -log b_h`.
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

/-- `F(2X+1) = 2^{c_F} F̃` with `F̃ ∈ ℤ[X]` having an odd coefficient. -/
theorem exists_comp_eq_C_two_pow_mul {F : ℤ[X]} (hF : F ≠ 0) :
    ∃ F₂ : ℤ[X], F.comp (2 * polyX + 1) = C (2 ^ shiftedTwoAdicOrder F) * F₂ ∧
      ∃ j, ¬ (2 : ℤ) ∣ F₂.coeff j := by
  obtain ⟨F₂, hF₂⟩ := (C_dvd_iff_dvd_coeff _ _).mpr (two_pow_dvd_coeff_comp F)
  refine ⟨F₂, hF₂, ?_⟩
  have hL : (2 * polyX + 1 : ℤ[X]) = C 2 * polyX + C 1 := by simp
  have hLdeg : (2 * polyX + 1 : ℤ[X]).natDegree = 1 := by
    rw [hL]
    exact natDegree_linear two_ne_zero
  have hF1 : F.comp (2 * polyX + 1) ≠ 0 := by
    intro h0
    have := leadingCoeff_comp (p := F)
      (by rw [hLdeg]; exact one_ne_zero : (2 * polyX + 1 : ℤ[X]).natDegree ≠ 0)
    rw [h0, leadingCoeff_zero, hL, leadingCoeff_linear two_ne_zero] at this
    exact mul_ne_zero (leadingCoeff_ne_zero.mpr hF) (pow_ne_zero _ two_ne_zero) this.symm
  set S := (fun j => padicValInt 2 ((F.comp (2 * polyX + 1)).coeff j)) ''
    ((F.comp (2 * polyX + 1)).support : Set ℕ) with hS
  have hSne : S.Nonempty := by
    obtain ⟨j, hj⟩ := Polynomial.support_nonempty.mpr hF1
    exact ⟨_, j, hj, rfl⟩
  obtain ⟨j, hj, hjv⟩ := Nat.sInf_mem hSne
  refine ⟨j, fun h2 => ?_⟩
  have hc : padicValInt 2 ((F.comp (2 * polyX + 1)).coeff j) = shiftedTwoAdicOrder F :=
    hjv.trans (shiftedTwoAdicOrder_eq F).symm
  have hdvd : ((2 : ℕ) : ℤ) ^ (shiftedTwoAdicOrder F + 1) ∣ (F.comp (2 * polyX + 1)).coeff j := by
    rw [hF₂, coeff_C_mul, pow_succ]
    push_cast
    exact mul_dvd_mul_left _ h2
  rcases (padicValInt_dvd_iff _ _).mp hdvd with h0 | hle
  · exact (mem_support_iff.mp (Finset.mem_coe.mp hj)) h0
  · omega

/-- Comparing two powers of `2` times polynomials having an odd coefficient. -/
theorem two_pow_unique {a b : ℕ} {A B : ℤ[X]}
    (h : C ((2 : ℤ) ^ a) * A = C ((2 : ℤ) ^ b) * B)
    (hA : ∃ j, ¬ (2 : ℤ) ∣ A.coeff j) (hB : ∃ j, ¬ (2 : ℤ) ∣ B.coeff j) : a = b := by
  have key : ∀ {a b : ℕ} {A B : ℤ[X]}, C ((2 : ℤ) ^ a) * A = C ((2 : ℤ) ^ b) * B →
      (∃ j, ¬ (2 : ℤ) ∣ B.coeff j) → a ≤ b := by
    intro a b A B h ⟨j, hj⟩
    by_contra hab
    push Not at hab
    obtain ⟨r, rfl⟩ : ∃ r, a = b + r + 1 := ⟨a - b - 1, by omega⟩
    have := congrArg (fun p => p.coeff j) h
    simp only [coeff_C_mul] at this
    apply hj
    have h2 : (2 : ℤ) ^ b * B.coeff j = 2 ^ b * (2 ^ (r + 1) * A.coeff j) := by
      rw [← this]; ring
    have h3 := mul_left_cancel₀ (pow_ne_zero b (two_ne_zero)) h2
    rw [h3, pow_succ]
    exact ⟨2 ^ r * A.coeff j, by ring⟩
  exact le_antisymm (key h hB) (key h.symm hA)

/-- The product of two integral polynomials with odd coefficients has an odd coefficient
(Gauss's lemma modulo `2`). -/
theorem exists_odd_coeff_mul {A B : ℤ[X]} (hA : ∃ j, ¬ (2 : ℤ) ∣ A.coeff j)
    (hB : ∃ j, ¬ (2 : ℤ) ∣ B.coeff j) : ∃ j, ¬ (2 : ℤ) ∣ (A * B).coeff j := by
  have hne : ∀ {P : ℤ[X]}, (∃ j, ¬ (2 : ℤ) ∣ P.coeff j) → P.map (Int.castRingHom (ZMod 2)) ≠ 0 := by
    rintro P ⟨j, hj⟩ h0
    apply hj
    have := congrArg (fun p => p.coeff j) h0
    simp only [coeff_map, coeff_zero, eq_intCast] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp this
  have hprod : (A * B).map (Int.castRingHom (ZMod 2)) ≠ 0 := by
    rw [Polynomial.map_mul]
    exact mul_ne_zero (hne hA) (hne hB)
  by_contra hcon
  push Not at hcon
  apply hprod
  ext j
  simp only [coeff_map, coeff_zero, eq_intCast]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr (hcon j)

/-- `c_F` is the exponent in any factorization `F(2X+1) = 2^a F̃` with `F̃` having an odd
coefficient. -/
theorem shiftedTwoAdicOrder_eq_of_comp {F F₂ : ℤ[X]} {a : ℕ} (hF : F ≠ 0)
    (h : F.comp (2 * polyX + 1) = C ((2 : ℤ) ^ a) * F₂) (h₂ : ∃ j, ¬ (2 : ℤ) ∣ F₂.coeff j) :
    shiftedTwoAdicOrder F = a := by
  obtain ⟨F₁, hF₁, h₁⟩ := exists_comp_eq_C_two_pow_mul hF
  exact two_pow_unique (hF₁.symm.trans h) h₁ h₂

/-- **Gauss multiplicativity** for the binary valuation of `F(2X+1)`:
`c_{FG} = c_F + c_G`. -/
theorem shiftedTwoAdicOrder_mul {F G : ℤ[X]} (hF : F ≠ 0) (hG : G ≠ 0) :
    shiftedTwoAdicOrder (F * G) = shiftedTwoAdicOrder F + shiftedTwoAdicOrder G := by
  obtain ⟨F₂, hF₂, hjF⟩ := exists_comp_eq_C_two_pow_mul hF
  obtain ⟨G₂, hG₂, hjG⟩ := exists_comp_eq_C_two_pow_mul hG
  refine shiftedTwoAdicOrder_eq_of_comp (mul_ne_zero hF hG) ?_ (exists_odd_coeff_mul hjF hjG)
  rw [mul_comp, hF₂, hG₂, pow_add, C_mul]
  ring

/-- **`κ = 2^k / c` with `c` odd.** If `h ∈ ℤ[1/2][x]` and `H = κ h` is a primitive integral
polynomial, then `κ = 2^k / c` for an integer `k` and an odd natural number `c`. -/
theorem exists_kappa_form {h : ℚ[X]} {κ : ℚ} (hκ : 0 < κ) {m : ℕ} {P : ℤ[X]}
    (hP : P.map (Int.castRingHom ℚ) = C ((2 : ℚ) ^ m) * h) {H : ℤ[X]}
    (hH : H.map (Int.castRingHom ℚ) = C κ * h) (hHprim : H.IsPrimitive) :
    ∃ (k : ℤ) (c : ℕ), Odd c ∧ κ = (2 : ℚ) ^ k / c := by
  have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  set q : ℕ := κ.den with hq
  set a : ℕ := κ.num.natAbs with ha
  have hq0 : q ≠ 0 := κ.den_nz
  have hnum : (0 : ℤ) < κ.num := Rat.num_pos.mpr hκ
  have ha0 : a ≠ 0 := by omega
  have hcop : Nat.Coprime a q := κ.reduced
  have haq : ((a : ℤ) : ℚ) = κ.num := by rw [ha, Int.natAbs_of_nonneg hnum.le]
  have hκa : κ * q = a := by
    have := Rat.mul_den_eq_num κ
    have h2 : ((a : ℤ) : ℚ) = (a : ℚ) := by simp
    rw [← h2, haq, ← this]
  -- `q 2^m H = a P`
  have hEq : C ((q : ℤ) * 2 ^ m) * H = C (a : ℤ) * P := by
    apply Polynomial.map_injective _ hinj
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, hH, hP]
    simp only [eq_intCast, Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat]
    have e : (q : ℚ) * 2 ^ m * κ = a * 2 ^ m := by rw [← hκa]; ring
    rw [← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul, e]
  -- every prime factor of `a` is `2`
  have hpow' : a = 2 ^ a.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd (p := 2) ha0 fun {ℓ} hℓ hℓa => by
      by_contra hne
      have hℓq : ¬ ℓ ∣ q := fun hd => hℓ.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop hℓa hd)
      have hℓ2 : ¬ ℓ ∣ 2 ^ m := fun hd => hne ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp
        (hℓ.dvd_of_dvd_pow hd))
      have hprimeZ : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
      have hC : C (ℓ : ℤ) ∣ H := by
        refine (C_dvd_iff_dvd_coeff _ _).mpr fun i => ?_
        have hi := congrArg (fun p => p.coeff i) hEq
        simp only [coeff_C_mul] at hi
        have hd : (ℓ : ℤ) ∣ ((q : ℤ) * 2 ^ m) * H.coeff i := by
          rw [hi]
          exact (Int.natCast_dvd_natCast.mpr hℓa).mul_right _
        rcases hprimeZ.dvd_or_dvd hd with h1 | h1
        · exfalso
          rcases hprimeZ.dvd_or_dvd h1 with h2 | h2
          · exact hℓq (Int.natCast_dvd_natCast.mp h2)
          · exact hℓ2 (Int.natCast_dvd_natCast.mp (by exact_mod_cast h2))
        · exact h1
      exact hℓ.one_lt.ne' (by
        have := Int.isUnit_iff.mp (hHprim _ hC)
        omega)
  obtain ⟨v, hpow⟩ : ∃ v : ℕ, a = 2 ^ v := ⟨_, hpow'⟩
  obtain ⟨s, c, hc, hqc⟩ := Nat.exists_eq_two_pow_mul_odd hq0
  refine ⟨(v : ℤ) - s, c, hc, ?_⟩
  have hqne : (q : ℚ) ≠ 0 := by exact_mod_cast hq0
  have hκ' : κ = a / q := by field_simp; exact hκa
  rw [hκ', zpow_sub₀ two_ne_zero, zpow_natCast, zpow_natCast, hqc, hpow]
  push_cast
  have hc0 : (c : ℚ) ≠ 0 := by
    have : c ≠ 0 := by rintro rfl; simp at hc
    exact_mod_cast this
  field_simp

private theorem coprime_two_pow_of_odd {c : ℕ} (hc : Odd c) (n : ℕ) : Nat.Coprime c (2 ^ n) :=
  Nat.Coprime.pow_right n
    (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hc.not_two_dvd_nat))

/-- **`c` divides `b_h`.** (`c` is odd, `κ = 2^k / c`, and `κ b_h = H(1)` is an integer.) -/
theorem odd_dvd_of_kappa {h : ℚ[X]} {κ : ℚ} {k : ℤ} {c : ℕ} (hc : Odd c)
    (hκ : κ = (2 : ℚ) ^ k / c) {H : ℤ[X]} (hH : H.map (Int.castRingHom ℚ) = C κ * h) {b : ℕ}
    (hb1 : h.eval 1 = b) : c ∣ b := by
  have hc0 : (c : ℚ) ≠ 0 := by
    have : c ≠ 0 := by rintro rfl; simp at hc
    exact_mod_cast this
  have hz : ((H.eval 1 : ℤ) : ℚ) = κ * b := by
    have := congrArg (eval 1) hH
    rw [eval_one_map] at this
    simpa [eval_mul, eval_C, hb1] using this
  have hz2 : ((H.eval 1 : ℤ) : ℚ) * c = 2 ^ k * b := by
    rw [hz, hκ]; field_simp
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [zpow_natCast] at hz2
    have hz3 : (H.eval 1) * (c : ℤ) = 2 ^ n * (b : ℤ) := by exact_mod_cast hz2
    have : (c : ℤ) ∣ ((2 ^ n * b : ℕ) : ℤ) := ⟨H.eval 1, by push_cast; linarith⟩
    exact (coprime_two_pow_of_odd hc n).dvd_of_dvd_mul_left (Int.natCast_dvd_natCast.mp this)
  · rw [zpow_neg, zpow_natCast] at hz2
    have hz3 : (H.eval 1) * (c : ℤ) * 2 ^ n = (b : ℤ) := by
      have : ((H.eval 1 : ℤ) : ℚ) * c * 2 ^ n = b := by
        rw [hz2]; field_simp
      exact_mod_cast this
    exact Int.natCast_dvd_natCast.mp ⟨H.eval 1 * 2 ^ n, by rw [← hz3]; ring⟩

/-- `h(2X+1) = 2^{t_2} T₂` with `T₂ ∈ ℤ[X]` having an odd coefficient: `t_2` is the minimum
binary valuation of the coefficients of `h(2X+1)`. -/
theorem exists_shift_form {h : ℚ[X]} (hh : h ≠ 0) {m : ℕ} {P : ℤ[X]}
    (hP : P.map (Int.castRingHom ℚ) = C ((2 : ℚ) ^ m) * h) :
    ∃ (t : ℤ) (T₂ : ℤ[X]), h.comp (2 * polyX + 1) = C ((2 : ℚ) ^ t) * T₂.map (Int.castRingHom ℚ) ∧
      ∃ j, ¬ (2 : ℤ) ∣ T₂.coeff j := by
  have hP0 : P ≠ 0 := by
    rintro rfl
    rw [Polynomial.map_zero] at hP
    exact hh ((mul_eq_zero.mp hP.symm).resolve_left (by simp))
  obtain ⟨P₂, hP₂, hj⟩ := exists_comp_eq_C_two_pow_mul hP0
  refine ⟨(shiftedTwoAdicOrder P : ℤ) - m, P₂, ?_, hj⟩
  have h1 : C ((2 : ℚ) ^ m) * h.comp (2 * polyX + 1) =
      C ((2 : ℚ) ^ shiftedTwoAdicOrder P) * P₂.map (Int.castRingHom ℚ) := by
    have e1 := congrArg (fun p => p.comp (2 * polyX + 1)) hP
    simp only [mul_comp, C_comp] at e1
    have e3 : (P.comp (2 * polyX + 1)).map (Int.castRingHom ℚ) =
        (P.map (Int.castRingHom ℚ)).comp (2 * polyX + 1) := by
      rw [Polynomial.map_comp]; simp
    rw [← e1, ← e3, hP₂, Polynomial.map_mul, Polynomial.map_C]
    simp
  have hne : ((2 : ℚ) ^ m)⁻¹ * (2 : ℚ) ^ m = 1 := inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero)
  calc h.comp (2 * polyX + 1)
      = C (((2 : ℚ) ^ m)⁻¹) * (C ((2 : ℚ) ^ m) * h.comp (2 * polyX + 1)) := by
        rw [← mul_assoc, ← C_mul, hne, C_1, one_mul]
    _ = _ := by
        rw [h1, ← mul_assoc, ← C_mul]
        congr 2
        rw [zpow_sub₀ two_ne_zero, zpow_natCast, zpow_natCast]
        ring

private theorem not_two_dvd_mul_of_odd {c : ℕ} (hc : Odd c) {x : ℤ} (hx : ¬ (2 : ℤ) ∣ x) :
    ¬ (2 : ℤ) ∣ (c : ℤ) * x := by
  intro h2
  rcases Int.prime_two.dvd_or_dvd h2 with h | h
  · exact hc.not_two_dvd_nat (by exact_mod_cast h)
  · exact hx h

/-- Comparing exponents of `2` in `c 2^a x = 2^e y` for odd `c`. -/
private theorem two_pow_cmp {c : ℕ} (hc : Odd c) {cH : ℕ} {e : ℤ} {x y : ℤ}
    (h : (c : ℚ) * 2 ^ cH * x = (2 : ℚ) ^ e * y) :
    (¬ (2 : ℤ) ∣ y → (cH : ℤ) ≤ e) ∧ (¬ (2 : ℤ) ∣ x → e ≤ cH) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg e
  · rw [zpow_natCast] at h
    have hz : (c : ℤ) * 2 ^ cH * x = 2 ^ n * y := by exact_mod_cast h
    constructor
    · intro hy
      by_contra hlt
      have hlt' : n < cH := by omega
      obtain ⟨r, rfl⟩ : ∃ r, cH = n + r + 1 := ⟨cH - n - 1, by omega⟩
      have h1 : (2 : ℤ) ^ n * y = 2 ^ n * (2 * (c * 2 ^ r * x)) := by rw [← hz]; ring
      exact hy ⟨_, mul_left_cancel₀ (pow_ne_zero n two_ne_zero) h1⟩
    · intro hx
      by_contra hlt
      have hlt' : cH < n := by omega
      obtain ⟨r, rfl⟩ : ∃ r, n = cH + r + 1 := ⟨n - cH - 1, by omega⟩
      have h1 : (2 : ℤ) ^ cH * (c * x) = 2 ^ cH * (2 * (2 ^ r * y)) := by
        rw [show (2 : ℤ) ^ cH * (c * x) = c * 2 ^ cH * x by ring, hz]; ring
      exact not_two_dvd_mul_of_odd hc hx ⟨_, mul_left_cancel₀ (pow_ne_zero cH two_ne_zero) h1⟩
  · rw [zpow_neg, zpow_natCast] at h
    have hz : (c : ℤ) * 2 ^ cH * x * 2 ^ n = y := by
      have : (c : ℚ) * 2 ^ cH * x * 2 ^ n = y := by rw [h]; field_simp
      exact_mod_cast this
    constructor
    · intro hy
      by_contra hlt
      obtain ⟨r, hr⟩ : ∃ r, cH + n = r + 1 := ⟨cH + n - 1, by omega⟩
      have e2 : (2 : ℤ) ^ cH * 2 ^ n = 2 ^ (r + 1) := by rw [← pow_add, hr]
      have : y = 2 * (c * 2 ^ r * x) := by
        calc y = c * (2 ^ cH * 2 ^ n) * x := by rw [← hz]; ring
          _ = _ := by rw [e2]; ring
      exact hy ⟨_, this⟩
    · intro _
      have := Int.natCast_nonneg cH
      have := Int.natCast_nonneg n
      omega

/-- **`c_F + c_G = k + t_2`** (Gauss multiplicativity). -/
theorem shiftedTwoAdicOrder_add_eq {h : ℚ[X]} {κ : ℚ} {k : ℤ} {c : ℕ} (hc : Odd c)
    (hκ : κ = (2 : ℚ) ^ k / c) {H : ℤ[X]} (hH : H.map (Int.castRingHom ℚ) = C κ * h)
    {F G : ℤ[X]} (hHFG : H = F * G) (hF : F ≠ 0) (hG : G ≠ 0) {t : ℤ} {T₂ : ℤ[X]}
    (hT : h.comp (2 * polyX + 1) = C ((2 : ℚ) ^ t) * T₂.map (Int.castRingHom ℚ))
    (hT₂ : ∃ j, ¬ (2 : ℤ) ∣ T₂.coeff j) :
    (shiftedTwoAdicOrder F : ℤ) + shiftedTwoAdicOrder G = k + t := by
  have hc0 : (c : ℚ) ≠ 0 := by
    have : c ≠ 0 := by rintro rfl; simp at hc
    exact_mod_cast this
  have hcH : shiftedTwoAdicOrder H = shiftedTwoAdicOrder F + shiftedTwoAdicOrder G := by
    rw [hHFG]; exact shiftedTwoAdicOrder_mul hF hG
  have hH0 : H ≠ 0 := by rw [hHFG]; exact mul_ne_zero hF hG
  obtain ⟨H₂, hH₂, hjH⟩ := exists_comp_eq_C_two_pow_mul hH0
  have e3 : (H.comp (2 * polyX + 1)).map (Int.castRingHom ℚ) =
      (H.map (Int.castRingHom ℚ)).comp (2 * polyX + 1) := by
    rw [Polynomial.map_comp]; simp
  have e : C ((2 : ℚ) ^ shiftedTwoAdicOrder H) * H₂.map (Int.castRingHom ℚ) =
      C κ * (C ((2 : ℚ) ^ t) * T₂.map (Int.castRingHom ℚ)) := by
    calc C ((2 : ℚ) ^ shiftedTwoAdicOrder H) * H₂.map (Int.castRingHom ℚ)
        = (H.comp (2 * polyX + 1)).map (Int.castRingHom ℚ) := by
          rw [hH₂, Polynomial.map_mul, Polynomial.map_C]; simp
      _ = (H.map (Int.castRingHom ℚ)).comp (2 * polyX + 1) := e3
      _ = _ := by rw [hH, mul_comp, C_comp, hT]
  have hcoef : ∀ j, (c : ℚ) * 2 ^ shiftedTwoAdicOrder H * (H₂.coeff j : ℚ) =
      (2 : ℚ) ^ (k + t) * (T₂.coeff j : ℚ) := by
    intro j
    have := congrArg (fun p => p.coeff j) e
    simp only [coeff_C_mul, coeff_map, eq_intCast] at this
    rw [zpow_add₀ two_ne_zero, hκ] at *
    rw [mul_assoc, mul_assoc, this]
    field_simp
  obtain ⟨j₁, hj₁⟩ := hjH
  obtain ⟨j₂, hj₂⟩ := hT₂
  have h1 := (two_pow_cmp hc (hcoef j₁)).2 hj₁
  have h2 := (two_pow_cmp hc (hcoef j₂)).1 hj₂
  rw [hcH] at h1 h2
  push_cast at h1 h2
  omega

/-- **`c · 2^{t_2} ≤ b_h`**: `t_2 ≤ v_2(b_h)` and `c ∣ b_h`. -/
theorem odd_mul_two_zpow_le {h : ℚ[X]} {c : ℕ} (hc : Odd c) {b : ℕ} (hb : 0 < b)
    (hb1 : h.eval 1 = b) (hcb : c ∣ b) {t : ℤ} {T₂ : ℤ[X]}
    (hT : h.comp (2 * polyX + 1) = C ((2 : ℚ) ^ t) * T₂.map (Int.castRingHom ℚ)) :
    (c : ℚ) * 2 ^ t ≤ b := by
  have hb0 : (b : ℚ) = 2 ^ t * (T₂.coeff 0 : ℚ) := by
    have := congrArg (fun p => p.coeff 0) hT
    have h0 : (h.comp (2 * polyX + 1)).coeff 0 = h.eval 1 := by
      rw [coeff_zero_eq_eval_zero, eval_comp]; simp
    simp only [h0, coeff_C_mul, coeff_map, eq_intCast] at this
    rw [← hb1, this]
  have hcb' : c ≤ b := Nat.le_of_dvd hb hcb
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg t
  · rw [zpow_natCast] at hb0 ⊢
    have hbz : (b : ℤ) = 2 ^ n * T₂.coeff 0 := by exact_mod_cast hb0
    have hcy : (c : ℤ) ∣ T₂.coeff 0 := by
      have h1 : (c : ℤ) ∣ T₂.coeff 0 * 2 ^ n := by
        have : (c : ℤ) ∣ (b : ℤ) := Int.natCast_dvd_natCast.mpr hcb
        rw [hbz] at this
        simpa [mul_comm] using this
      have hcop : IsCoprime (c : ℤ) ((2 : ℤ) ^ n) := by
        have := Nat.isCoprime_iff_coprime.mpr (coprime_two_pow_of_odd hc n)
        simpa using this
      exact hcop.dvd_of_dvd_mul_right h1
    obtain ⟨u, hu⟩ := hcy
    have hdvd : ((c : ℤ) * 2 ^ n) ∣ (b : ℤ) := ⟨u, by rw [hbz, hu]; ring⟩
    have := Int.le_of_dvd (by exact_mod_cast hb) hdvd
    have h2 : ((c : ℤ) * 2 ^ n : ℚ) ≤ (b : ℚ) := by exact_mod_cast this
    simpa using h2
  · have h1 : (2 : ℚ) ^ (-(n : ℤ)) ≤ 1 := by
      rw [zpow_neg, zpow_natCast]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have h2 : (c : ℚ) ≤ b := by exact_mod_cast hcb'
    have hc0 : (0 : ℚ) ≤ c := Nat.cast_nonneg c
    nlinarith

/-- **The key inequality of the proof of Lemma 2.6**: `2^{c_F + c_G} ≤ κ b_h`, that is
`log κ - (c_F + c_G) log 2 ≥ -log b_h`, obtained as in the manuscript: `κ = 2^k/c` with `c` odd
dividing `b_h`, `c_F + c_G = k + t_2` by Gauss multiplicativity, and `t_2 ≤ v_2(b_h)`. -/
theorem two_pow_shiftedTwoAdicOrder_mul_le {h : ℚ[X]} {κ : ℚ} (hκ : 0 < κ) {m : ℕ} {P : ℤ[X]}
    (hP : P.map (Int.castRingHom ℚ) = C ((2 : ℚ) ^ m) * h) {H : ℤ[X]}
    (hH : H.map (Int.castRingHom ℚ) = C κ * h) (hHprim : H.IsPrimitive) {F G : ℤ[X]}
    (hHFG : H = F * G) (hF : F ≠ 0) (hG : G ≠ 0) {b : ℕ} (hb : 0 < b) (hb1 : h.eval 1 = b) :
    (2 : ℚ) ^ shiftedTwoAdicOrder F * 2 ^ shiftedTwoAdicOrder G ≤ κ * b := by
  have hh : h ≠ 0 := by
    rintro rfl
    simp only [eval_zero] at hb1
    exact hb.ne' (by exact_mod_cast hb1.symm)
  obtain ⟨k, c, hc, hκk⟩ := exists_kappa_form hκ hP hH hHprim
  have hcb := odd_dvd_of_kappa hc hκk hH hb1
  obtain ⟨t, T₂, hT, hT₂⟩ := exists_shift_form hh hP
  have heq := shiftedTwoAdicOrder_add_eq hc hκk hH hHFG hF hG hT hT₂
  have hct := odd_mul_two_zpow_le hc hb hb1 hcb hT
  have hc0 : (0 : ℚ) < c := by
    have : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp at hc)
    exact_mod_cast this
  have h2k : (0 : ℚ) < 2 ^ k := zpow_pos (by norm_num) k
  have hlhs : (2 : ℚ) ^ shiftedTwoAdicOrder F * 2 ^ shiftedTwoAdicOrder G = 2 ^ k * 2 ^ t := by
    rw [← pow_add, ← zpow_natCast, Nat.cast_add, heq, zpow_add₀ two_ne_zero]
  rw [hlhs, hκk, div_mul_eq_mul_div, le_div_iff₀ hc0]
  calc 2 ^ k * 2 ^ t * (c : ℚ) = 2 ^ k * (c * 2 ^ t) := by ring
    _ ≤ 2 ^ k * b := mul_le_mul_of_nonneg_left hct h2k.le

end ArithmeticOfJacobiPolynomials
