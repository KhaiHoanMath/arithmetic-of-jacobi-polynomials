/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Padic.ProjectiveDistance
public import ArithmeticOfJacobiPolynomials.Jacobi.Wronskian
public import ArithmeticOfJacobiPolynomials.Jacobi.KanekoZagierLocal
public import ArithmeticOfJacobiPolynomials.Padic.SourceNewtonRoots
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.NumberTheory.Padics.MahlerBasis

/-!
# The primes `2` and `3` (Proposition 4.6)

Roots are taken in `PadicAlgCl p` with the real valuation `v_p = padicVal p`.

The total root-valuation deficits at `2` and `3` follow the manuscript through the Newton polygon
theorem (`NewtonPolygonRootSlopes`, [Berger, Theorem 2.4], an explicit hypothesis `hNP`): the exact
coefficient valuations (`padicValRat_monicEndpointCoeff_two` at `2`, `digitPhi` at `3`), the hull
of their correction term, and `monicEndpoint_deficit_le_of_hull`; the resultant bounds
`padicValInt_two_resultant_le` and `padicValInt_three_resultant_le` use this route.

Local estimates, for an arbitrary prime `p`:
* `sum_logb_max_le_of_coeff`: if the monic polynomial `∏ (X - w)` has coefficients
  `‖c_j‖ c^j ≤ p^D c^n`, then `∑_w log_p max(1, ‖w‖/c) ≤ D` (through the Gauss norm of radius `c`
  in the proof of `monicEndpoint_deficit_le`);
* `factorial_radius_bound`: the inequality (4.14);
* `padicVal_sub_le_of_ode`: the Taylor argument (4.12)–(4.13) at a root of a polynomial
  satisfying `z(1-z)P'' + (b+1-(c+2)z)P' + n(n+c+1)P = 0`;
* `padicVal_sub_le_of_eq`: the paired prime separation (4.15).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial renaming X → polyX
open Polynomial Finset

section LocalNorms

variable {p : ℕ} [hp : Fact p.Prime]

local notation "K" => PadicAlgCl p

theorem norm_intCast_padicAlgCl (k : ℤ) : ‖(k : K)‖ = ‖(k : ℤ_[p])‖ := by
  have h := norm_algebraMap_padicInt (p := p) (k : ℤ_[p])
  rwa [map_intCast] at h

theorem norm_intCast_padicAlgCl_le_one (k : ℤ) : ‖(k : K)‖ ≤ 1 := by
  rw [norm_intCast_padicAlgCl]
  exact PadicInt.norm_le_one _

theorem norm_intCast_padicAlgCl_le_inv {k : ℤ} (h : (p : ℤ) ∣ k) : ‖(k : K)‖ ≤ (p : ℝ)⁻¹ := by
  rw [norm_intCast_padicAlgCl]
  have := (PadicInt.norm_int_le_pow_iff_dvd (p := p) (k := k) (n := 1)).mpr (by simpa using h)
  simpa using this

theorem norm_ratCast_padicAlgCl_of_ne {q : ℚ} (hq : q ≠ 0) :
    ‖(q : K)‖ = (p : ℝ) ^ (-padicValRat p q) := by
  rw [← map_ratCast (algebraMap ℚ_[p] K) q, norm_ratCast_padicAlgCl q hq]

theorem padicVal_ratCast_padicAlgCl {q : ℚ} (hq : q ≠ 0) :
    padicVal p (q : K) = padicValRat p q := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  rw [padicVal_def, norm_ratCast_padicAlgCl_of_ne hq, ← Real.rpow_intCast,
    Real.logb_rpow hp0 (ne_of_gt one_lt_prime_real)]
  push_cast
  ring

theorem norm_natCast_padicAlgCl {m : ℕ} (hm : m ≠ 0) :
    ‖(m : K)‖ = ((p : ℝ) ^ padicValNat p m)⁻¹ := by
  have e : ((m : ℚ) : K) = (m : K) := Rat.cast_natCast m
  rw [← e, norm_ratCast_padicAlgCl_of_ne (by exact_mod_cast hm), padicValRat.of_nat, zpow_neg,
    zpow_natCast]

theorem norm_one_sub_padicAlgCl {z : K} (hz : ‖z‖ < 1) : ‖1 - z‖ = 1 := by
  have hne : ‖(1 : K)‖ ≠ ‖-z‖ := by rw [norm_one, norm_neg]; exact hz.ne'
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one, norm_neg,
    max_eq_left hz.le]

theorem norm_sub_le_max_padicAlgCl (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max x (-y)

theorem norm_add_le_max_padicAlgCl (x y : K) : ‖x + y‖ ≤ max ‖x‖ ‖y‖ :=
  IsUltrametricDist.norm_add_le_max x y

end LocalNorms

/-! ### Root masses through the Gauss norm of radius `c` -/

section GaussRadius

variable {p : ℕ} [hp : Fact p.Prime]

local notation "K" => PadicAlgCl p

local notation "absK" => NormedField.toAbsoluteValue (PadicAlgCl p)

private lemma isNonarchimedean_absK_radius : IsNonarchimedean (absK) :=
  PadicAlgCl.isNonarchimedean p

private lemma gaussNorm_X_sub_C_radius {c : ℝ} (hc : 0 < c) (w : K) :
    (polyX - C w).gaussNorm absK c = max c ‖w‖ := by
  apply le_antisymm
  · rw [sub_eq_add_neg, ← C_neg]
    have hna := isNonarchimedean_gaussNorm (hna := isNonarchimedean_absK_radius (p := p))
      (hc := hc.le)
    refine (hna polyX (C (-w))).trans ?_
    have hX : (polyX : K[X]).gaussNorm absK c = c := by
      rw [← monomial_one_one_eq_X, gaussNorm_monomial]
      simp
    rw [hX, gaussNorm_C]
    simp
  · apply max_le
    · have := le_gaussNorm absK (p := (polyX - C w : K[X])) hc.le 1
      simpa [coeff_X, coeff_C] using this
    · have := le_gaussNorm absK (p := (polyX - C w : K[X])) hc.le 0
      simpa [coeff_X, coeff_C] using this

private lemma gaussNorm_prod_X_sub_C_radius {c : ℝ} (hc : 0 < c) (s : Multiset K) :
    (s.map fun w => polyX - C w).prod.gaussNorm absK c = (s.map fun w => max c ‖w‖).prod := by
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero]
    rw [← C_1, gaussNorm_C]
    simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [gaussNorm_mul isNonarchimedean_absK_radius hc, gaussNorm_X_sub_C_radius hc, ih]

/-- The Gauss norm of radius `c` of `∏ (X - w)` is `∏ max(c, ‖w‖)`; hence a coefficient bound
`‖c_j‖ c^j ≤ B` bounds this product. -/
theorem prod_max_norm_le_of_coeff {c B : ℝ} (hc : 0 < c) (s : Multiset K)
    (h : ∀ j, ‖((s.map fun w => polyX - C w).prod).coeff j‖ * c ^ j ≤ B) :
    (s.map fun w => max c ‖w‖).prod ≤ B := by
  rw [← gaussNorm_prod_X_sub_C_radius hc]
  obtain ⟨i, hi⟩ := exists_eq_gaussNorm absK c (s.map fun w => polyX - C w).prod
  rw [hi]
  exact h i

/-- **Root deficits from coefficient valuations.** If the coefficients of the monic polynomial
`∏_{w ∈ s} (X - w)` satisfy `‖c_j‖ c^j ≤ p^D c^{|s|}`, then
`∑_{w ∈ s} log_p max(1, ‖w‖/c) ≤ D`. For `c = p^{-ρ}` the summand is `(ρ - v_p(w))_+`. -/
theorem sum_logb_max_le_of_coeff {c D : ℝ} (hc : 0 < c) (s : Multiset K)
    (h : ∀ j, ‖((s.map fun w => polyX - C w).prod).coeff j‖ * c ^ j ≤
      (p : ℝ) ^ D * c ^ Multiset.card s) :
    (s.map fun w => Real.logb p (max 1 (‖w‖ / c))).sum ≤ D := by
  have h1 := prod_max_norm_le_of_coeff hc s h
  have hfun : (fun w : K => max c ‖w‖) = fun w => c * max 1 (‖w‖ / c) := by
    funext w
    rw [mul_max_of_nonneg _ _ hc.le, mul_one, mul_div_cancel₀ _ hc.ne']
  rw [hfun, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
    mul_comm ((p : ℝ) ^ D)] at h1
  have hc' : 0 < c ^ Multiset.card s := pow_pos hc _
  have h2 := le_of_mul_le_mul_left h1 hc'
  have hpos : ∀ w ∈ s, (max 1 (‖w‖ / c)) ≠ 0 := fun w _ =>
    (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'
  have hprod : 0 < (s.map fun w => max 1 (‖w‖ / c)).prod := by
    apply Multiset.prod_pos
    intro x hx
    obtain ⟨w, -, rfl⟩ := Multiset.mem_map.mp hx
    exact lt_of_lt_of_le one_pos (le_max_left _ _)
  have h3 := Real.logb_le_logb_of_le (one_lt_prime_real (p := p)) hprod h2
  rwa [logb_multiset_prod_map _ _ hpos,
    Real.logb_rpow (by exact_mod_cast hp.out.pos) (ne_of_gt one_lt_prime_real)] at h3

theorem logb_max_one_nonneg (x : ℝ) : 0 ≤ Real.logb p (max 1 x) :=
  Real.logb_nonneg one_lt_prime_real (le_max_left _ _)

/-- The summand of `sum_logb_max_le_of_coeff` for `c = p^{-ρ}` and `w ≠ 0`. -/
theorem logb_max_one_div_eq {w : K} (hw : w ≠ 0) (ρ : ℝ) :
    Real.logb p (max 1 (‖w‖ / (p : ℝ) ^ (-ρ))) = max (ρ - padicVal p w) 0 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (p : ℝ) ≠ 1 := ne_of_gt one_lt_prime_real
  have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hc : 0 < (p : ℝ) ^ (-ρ) := Real.rpow_pos_of_pos hp0 _
  have hlog : Real.logb p (‖w‖ / (p : ℝ) ^ (-ρ)) = ρ - padicVal p w := by
    rw [Real.logb_div hw'.ne' hc.ne', Real.logb_rpow hp0 hp1, padicVal_def]
    ring
  rcases le_total 1 (‖w‖ / (p : ℝ) ^ (-ρ)) with h | h
  · rw [max_eq_right h, hlog]
    have : 0 ≤ Real.logb p (‖w‖ / (p : ℝ) ^ (-ρ)) := Real.logb_nonneg one_lt_prime_real h
    rw [hlog] at this
    exact (max_eq_left this).symm
  · rw [max_eq_left h, Real.logb_one]
    have : Real.logb p (‖w‖ / (p : ℝ) ^ (-ρ)) ≤ 0 :=
      Real.logb_nonpos one_lt_prime_real (by positivity) h
    rw [hlog] at this
    exact (max_eq_right this).symm

/-- **All roots lie in the ball `‖w‖ ≤ 1/p`** when `‖c_j‖ ≤ p^{-(n-j)}`. -/
theorem norm_le_inv_of_coeff (s : Multiset K)
    (h : ∀ j, ‖((s.map fun w => polyX - C w).prod).coeff j‖ * (p : ℝ)⁻¹ ^ j ≤
      (p : ℝ)⁻¹ ^ Multiset.card s) :
    ∀ w ∈ s, ‖w‖ ≤ (p : ℝ)⁻¹ := by
  have hc : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.out.pos)
  have hsum := sum_logb_max_le_of_coeff (D := 0) hc s (by simpa using h)
  intro w hw
  have hle := Multiset.single_le_sum (s := s.map fun w => Real.logb p (max 1 (‖w‖ / (p : ℝ)⁻¹)))
    (fun x hx => by
      obtain ⟨u, -, rfl⟩ := Multiset.mem_map.mp hx
      exact logb_max_one_nonneg _) _ (Multiset.mem_map_of_mem _ hw)
  have h0 : Real.logb p (max 1 (‖w‖ / (p : ℝ)⁻¹)) ≤ 0 := hle.trans hsum
  have h1 : max 1 (‖w‖ / (p : ℝ)⁻¹) ≤ 1 :=
    (Real.logb_nonpos_iff one_lt_prime_real (lt_of_lt_of_le one_pos (le_max_left _ _))).mp h0
  have h2 : ‖w‖ / (p : ℝ)⁻¹ ≤ 1 := (le_max_right _ _).trans h1
  rwa [div_le_one hc] at h2

end GaussRadius

/-! ### The factorial bound (4.14) and the separation constants -/

section FactorialBound

variable {p : ℕ} [hp : Fact p.Prime]

theorem one_le_digits_sum {b : ℕ} (hb : 1 < b) : ∀ n, 0 < n → 1 ≤ (Nat.digits b n).sum := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rw [Nat.digits_def' hb hn, List.sum_cons]
    by_cases hr : n % b = 0
    · have hq : 0 < n / b := by
        rcases Nat.eq_zero_or_pos (n / b) with h | h
        · have := Nat.div_add_mod n b
          rw [h, hr] at this
          omega
        · exact h
      have := ih (n / b) (Nat.div_lt_self hn hb) hq
      omega
    · omega

theorem mod_le_digits_sum {b : ℕ} (hb : 1 < b) (n : ℕ) : n % b ≤ (Nat.digits b n).sum := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Nat.digits_def' hb hn, List.sum_cons]
    omega

/-- **The factorial bound (4.14).** For `j ≥ 2` and `0 ≤ h ≤ 1`,
`v_p(j!) - ⌊j/p⌋ h ≤ (j-1)(1/(p-1) - h/p)`. -/
theorem factorial_radius_bound {j : ℕ} (hj : 2 ≤ j) {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    (padicValNat p j.factorial : ℝ) - ((j / p : ℕ) : ℝ) * h ≤
      ((j : ℝ) - 1) * (1 / ((p : ℝ) - 1) - h / p) := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hL := sub_one_mul_padicValNat_factorial (p := p) j
  have hsle := Nat.digit_sum_le p j
  have hs1 := one_le_digits_sum (b := p) (by omega) j (by omega)
  have hsr := mod_le_digits_sum (b := p) (by omega) j
  have hdiv := Nat.div_add_mod j p
  have hmod := Nat.mod_lt j (show p > 0 by omega)
  set s := (Nat.digits p j).sum with hs
  set v := padicValNat p j.factorial with hv
  set q := j / p with hq
  set r := j % p with hr
  have hLr : ((p : ℝ) - 1) * v = j - s := by
    have : ((p - 1) * v : ℕ) = ((j - s : ℕ) : ℝ) := by exact_mod_cast hL
    rw [Nat.cast_sub hsle, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ p)] at this
    simpa using this
  have hjr : (j : ℝ) = p * q + r := by exact_mod_cast hdiv.symm
  have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hs1' : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hsr' : (r : ℝ) ≤ s := by exact_mod_cast hsr
  have hrp : (r : ℝ) + 1 ≤ p := by exact_mod_cast hmod
  have hP1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hP0 : (0 : ℝ) < p := by linarith
  have key : (p : ℝ) * (1 - s) + ((p : ℝ) - 1) * h * ((r : ℝ) - 1) ≤ 0 := by
    rcases Nat.eq_zero_or_pos r with h0r | h0r
    · have hr0 : (r : ℝ) = 0 := by exact_mod_cast h0r
      have t1 := mul_nonneg hP0.le (sub_nonneg.mpr hs1')
      have t2 := mul_nonneg hP1.le h0
      rw [hr0]
      nlinarith
    · have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast h0r
      have hA : 0 ≤ ((p : ℝ) - 1) * ((r : ℝ) - 1) := mul_nonneg hP1.le (by linarith)
      have t1 := mul_nonneg hA (sub_nonneg.mpr h1)
      have t2 := mul_nonneg hP0.le (sub_nonneg.mpr hsr')
      nlinarith
  have hP1' : (p : ℝ) - 1 ≠ 0 := hP1.ne'
  have hP0' : (p : ℝ) ≠ 0 := hP0.ne'
  have e : ((p : ℝ) * ((p : ℝ) - 1)) * (((j : ℝ) - 1) * (1 / ((p : ℝ) - 1) - h / p)) =
      p * ((j : ℝ) - 1) - ((p : ℝ) - 1) * ((j : ℝ) - 1) * h := by
    field_simp
  have hpos : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) := mul_pos hP0 hP1
  refine le_of_mul_le_mul_left ?_ hpos
  rw [e]
  have : (p : ℝ) * ((p : ℝ) - 1) * ((v : ℝ) - (q : ℝ) * h) =
      p * (j - s) - p * ((p : ℝ) - 1) * q * h := by
    rw [← hLr]; ring
  rw [this, hjr]
  nlinarith

/-- The comparison used for (4.15): `1/(p-1) - min(1, r-1)/p ≤ 1/p + (ρ_p - r)_+/p`, where
`ρ_p = p/(p-1)`. -/
theorem separation_constant_le (r : ℝ) :
    1 / ((p : ℝ) - 1) - min 1 (r - 1) / p ≤
      1 / p + max ((p : ℝ) / ((p : ℝ) - 1) - r) 0 / p := by
  have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
  have hP1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hP0 : (0 : ℝ) < p := by linarith
  have hP1' : (p : ℝ) - 1 ≠ 0 := hP1.ne'
  have hP0' : (p : ℝ) ≠ 0 := hP0.ne'
  have hρ : (p : ℝ) / ((p : ℝ) - 1) = 1 + 1 / ((p : ℝ) - 1) := by field_simp; ring
  have hinv : 1 / ((p : ℝ) - 1) ≤ 1 := by rw [div_le_one hP1]; linarith
  -- it suffices: `1/(p-1) ≤ 1 + min(1,r-1) + (ρ-r)_+ - ...`; reduce to `1/(p-1) ≤ m + M`
  have hsuff : 1 / ((p : ℝ) - 1) ≤ min 1 (r - 1) + max ((p : ℝ) / ((p : ℝ) - 1) - r) 0 := by
    rw [hρ]
    rcases le_total 1 (r - 1) with h1 | h1
    · rw [min_eq_left h1]
      linarith [le_max_right (1 + 1 / ((p : ℝ) - 1) - r) 0]
    · rw [min_eq_right h1]
      linarith [le_max_left (1 + 1 / ((p : ℝ) - 1) - r) 0]
  have e : 1 / ((p : ℝ) - 1) - 1 / p = 1 / ((p : ℝ) - 1) / p := by field_simp; ring
  have : 1 / ((p : ℝ) - 1) / p ≤ (min 1 (r - 1) + max ((p : ℝ) / ((p : ℝ) - 1) - r) 0) / p :=
    div_le_div_of_nonneg_right hsuff hP0.le
  rw [add_div] at this
  linarith

end FactorialBound

/-! ### The Taylor argument at a root (4.12)–(4.15) -/

section Taylor

/-- One differentiation of `σ Q'' + (a - b X) Q' + l Q = 0`, `σ = X(1-X)`. -/
theorem ode_derivative_step {F : Type*} [CommRing F] {a b l : F} {Q : F[X]}
    (h : polyX * (1 - polyX) * derivative (derivative Q) + (C a - C b * polyX) * derivative Q +
      C l * Q = 0) :
    polyX * (1 - polyX) * derivative (derivative (derivative Q)) +
        (C (a + 1) - C (b + 1 + 1) * polyX) * derivative (derivative Q) +
      C (l - b) * derivative Q = 0 := by
  have h' := congrArg derivative h
  simp only [derivative_add, derivative_mul, derivative_sub, derivative_X, derivative_one,
    derivative_C, derivative_zero] at h'
  rw [C_add, C_add, C_add, C_sub, C_1]
  linear_combination h'

/-- The differential equation differentiated `m` times:
`σ P^{(m+2)} + (B₁ + m - (c₂ + 2m) X) P^{(m+1)} + (Λ₀ - m c₂ - m(m-1)) P^{(m)} = 0`. -/
theorem iterate_derivative_ode {F : Type*} [CommRing F] {B1 c2 Λ0 : F} {P : F[X]}
    (hode : polyX * (1 - polyX) * derivative (derivative P) + (C B1 - C c2 * polyX) * derivative P +
      C Λ0 * P = 0) (m : ℕ) :
    polyX * (1 - polyX) * derivative (derivative (derivative^[m] P)) +
        (C (B1 + m) - C (c2 + 2 * m) * polyX) * derivative (derivative^[m] P) +
      C (Λ0 - m * c2 - m * (m - 1)) * derivative^[m] P = 0 := by
  induction m with
  | zero => simpa using hode
  | succ m ih =>
    have h := ode_derivative_step ih
    rw [Function.iterate_succ_apply']
    have e1 : B1 + ((m + 1 : ℕ) : F) = B1 + m + 1 := by push_cast; ring
    have e2 : c2 + 2 * ((m + 1 : ℕ) : F) = c2 + 2 * m + 1 + 1 := by push_cast; ring
    have e3 : Λ0 - ((m + 1 : ℕ) : F) * c2 - ((m + 1 : ℕ) : F) * (((m + 1 : ℕ) : F) - 1) =
        Λ0 - m * c2 - m * (m - 1) - (c2 + 2 * m) := by push_cast; ring
    rw [e1, e2, e3]
    exact h

variable {p : ℕ} [hp : Fact p.Prime]

local notation "K" => PadicAlgCl p

/-- Distinct valuations: `v_p(w - z) = min(v_p(w), v_p(z))`. -/
theorem padicVal_sub_eq_min {w z : K} (hw : w ≠ 0) (hz : z ≠ 0)
    (h : padicVal p w ≠ padicVal p z) :
    padicVal p (w - z) = min (padicVal p w) (padicVal p z) := by
  have hwz : ‖w‖ ≠ ‖-z‖ := by
    rw [norm_neg]
    intro he
    exact h (by rw [padicVal_def, padicVal_def, he])
  have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [sub_eq_add_neg, padicVal_def, padicVal_def, padicVal_def,
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hwz, norm_neg]
  rcases le_total ‖w‖ ‖z‖ with hle | hle
  · rw [max_eq_right hle]
    have := Real.logb_le_logb_of_le (one_lt_prime_real (p := p)) hw' hle
    rw [min_eq_right (show -Real.logb p ‖z‖ ≤ -Real.logb p ‖w‖ by linarith)]
  · rw [max_eq_left hle]
    have := Real.logb_le_logb_of_le (one_lt_prime_real (p := p)) hz' hle
    rw [min_eq_left (show -Real.logb p ‖w‖ ≤ -Real.logb p ‖z‖ by linarith)]

/-- **The Taylor argument (4.12)–(4.14).** Let `P ∈ K[X]`, `K = PadicAlgCl p`, be nonzero with
`X(1-X) P'' + (B₁ - c₂ X) P' + Λ₀ P = 0`, where `‖B₁ + m‖ ≤ 1` for all `m`, `‖B₁ + m‖ ≤ 1/p`
whenever `p ∣ m + 2 + c₀` (`c₀ + 2 ≤ p`), `‖c₂ + 2m‖ ≤ p` and `‖Λ₀ - m c₂ - m(m-1)‖ ≤ p`.
If `z ≠ w` are roots of `P` with `0 < ‖z‖ ≤ 1/p`, then
`v_p(w - z) ≤ v_p(z) + 1/(p-1) - min(1, v_p(z) - 1)/p`. -/
theorem padicVal_sub_le_of_ode {c0 : ℕ} (hc0 : c0 + 2 ≤ p) {B1 c2 Λ0 : K} {P : K[X]}
    (hP : P ≠ 0)
    (hode : polyX * (1 - polyX) * derivative (derivative P) + (C B1 - C c2 * polyX) * derivative P +
      C Λ0 * P = 0)
    (hB : ∀ m : ℕ, ‖B1 + m‖ ≤ 1)
    (hBgain : ∀ m : ℕ, p ∣ m + 2 + c0 → ‖B1 + m‖ ≤ (p : ℝ)⁻¹)
    (hc : ∀ m : ℕ, ‖c2 + 2 * m‖ ≤ p)
    (hΛ : ∀ m : ℕ, ‖Λ0 - m * c2 - m * (m - 1)‖ ≤ p)
    {z w : K} (hz : P.eval z = 0) (hw : P.eval w = 0) (hz0 : z ≠ 0) (hzp : ‖z‖ ≤ (p : ℝ)⁻¹)
    (hwz : w ≠ z) :
    padicVal p (w - z) ≤ padicVal p z + (1 / ((p : ℝ) - 1) - min 1 (padicVal p z - 1) / p) := by
  classical
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) < p := one_lt_prime_real
  have hp2 : 2 ≤ p := hp.out.two_le
  obtain ⟨d, hd⟩ : ∃ d : ℕ → K, d = fun j => (derivative^[j] P).eval z := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℕ → K, W = fun j => z ^ j * d j := ⟨_, rfl⟩
  -- the recurrence for `W_j = z^j P^{(j)}(z)`
  have hrec : ∀ m : ℕ, (1 - z) * W (m + 1 + 1) =
      -((B1 + m) - (c2 + 2 * m) * z) * W (m + 1) -
        ((Λ0 - m * c2 - m * (m - 1)) * z) * W m := by
    intro m
    have h := congrArg (eval z) (iterate_derivative_ode hode m)
    simp only [eval_add, eval_mul, eval_sub, eval_X, eval_one, eval_C, eval_zero] at h
    have e1 : derivative^[m + 1] P = derivative (derivative^[m] P) :=
      Function.iterate_succ_apply' _ _ _
    have e2 : derivative^[m + 1 + 1] P = derivative (derivative (derivative^[m] P)) := by
      rw [Function.iterate_succ_apply', e1]
    simp only [hW, hd, e1, e2]
    linear_combination (z ^ (m + 1)) * h
  -- norms
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hz1 : ‖z‖ < 1 := lt_of_le_of_lt hzp (inv_lt_one_of_one_lt₀ hp1)
  have h1z : ‖1 - z‖ = 1 := norm_one_sub_padicAlgCl hz1
  set θ : ℝ := max (p : ℝ)⁻¹ (p * ‖z‖) with hθ
  have hθ0 : 0 < θ := lt_of_lt_of_le (inv_pos.mpr hp0) (le_max_left _ _)
  have hpz1 : (p : ℝ) * ‖z‖ ≤ 1 := by
    calc (p : ℝ) * ‖z‖ ≤ p * (p : ℝ)⁻¹ := mul_le_mul_of_nonneg_left hzp hp0.le
      _ = 1 := mul_inv_cancel₀ hp0.ne'
  have hθ1 : θ ≤ 1 := max_le (inv_le_one_of_one_le₀ hp1.le) hpz1
  have hpz : (p : ℝ) * ‖z‖ ≤ θ := le_max_right _ _
  have hpinv : (p : ℝ)⁻¹ ≤ θ := le_max_left _ _
  -- the valuation bound `‖W_j‖ ≤ θ^{⌊(j+c₀)/p⌋} ‖W_1‖`
  have hclaim : ∀ m : ℕ, ‖W m‖ ≤ θ ^ ((m + c0) / p) * ‖W 1‖ ∧
      ‖W (m + 1)‖ ≤ θ ^ ((m + 1 + c0) / p) * ‖W 1‖ := by
    intro m
    induction m with
    | zero =>
      have hW0 : W 0 = 0 := by simp [hW, hd, hz]
      have hg1 : (0 + 1 + c0) / p = 0 := Nat.div_eq_of_lt (by omega)
      refine ⟨by rw [hW0, norm_zero]; exact mul_nonneg (pow_nonneg hθ0.le _) (norm_nonneg _),
        by rw [hg1, pow_zero, one_mul, zero_add]⟩
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      have hcz : ‖(c2 + 2 * m) * z‖ ≤ θ := by
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_right (hc m) (norm_nonneg z)).trans hpz
      have hL : ‖(Λ0 - m * c2 - m * (m - 1)) * z‖ ≤ θ := by
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_right (hΛ m) (norm_nonneg z)).trans hpz
      have hsd : (m + 1 + 1 + c0) / p = (m + 1 + c0) / p + if p ∣ m + 1 + c0 + 1 then 1 else 0 := by
        rw [show m + 1 + 1 + c0 = (m + 1 + c0) + 1 by ring]
        exact Nat.succ_div
      have hgm : (m + 1 + 1 + c0) / p ≤ (m + c0) / p + 1 := by
        calc (m + 1 + 1 + c0) / p ≤ (m + c0 + p) / p := Nat.div_le_div_right (by omega)
          _ = (m + c0) / p + 1 := Nat.add_div_right _ (by omega)
      have t1 : ‖(B1 + m) - (c2 + 2 * m) * z‖ * ‖W (m + 1)‖ ≤
          θ ^ ((m + 1 + 1 + c0) / p) * ‖W 1‖ := by
        rw [hsd]
        split_ifs with hdvd
        · have hA : ‖(B1 + m) - (c2 + 2 * m) * z‖ ≤ θ := by
            refine (norm_sub_le_max_padicAlgCl _ _).trans (max_le ?_ hcz)
            exact (hBgain m (by rw [show m + 2 + c0 = m + 1 + c0 + 1 by ring]; exact hdvd)).trans
              hpinv
          calc ‖(B1 + m) - (c2 + 2 * m) * z‖ * ‖W (m + 1)‖ ≤
                θ * (θ ^ ((m + 1 + c0) / p) * ‖W 1‖) :=
                mul_le_mul hA ih.2 (norm_nonneg _) hθ0.le
            _ = θ ^ ((m + 1 + c0) / p + 1) * ‖W 1‖ := by ring
        · have hA : ‖(B1 + m) - (c2 + 2 * m) * z‖ ≤ 1 :=
            (norm_sub_le_max_padicAlgCl _ _).trans (max_le (hB m) (hcz.trans hθ1))
          calc ‖(B1 + m) - (c2 + 2 * m) * z‖ * ‖W (m + 1)‖ ≤
                1 * (θ ^ ((m + 1 + c0) / p) * ‖W 1‖) :=
                mul_le_mul hA ih.2 (norm_nonneg _) zero_le_one
            _ = θ ^ ((m + 1 + c0) / p + 0) * ‖W 1‖ := by ring
      have t2 : ‖(Λ0 - m * c2 - m * (m - 1)) * z‖ * ‖W m‖ ≤
          θ ^ ((m + 1 + 1 + c0) / p) * ‖W 1‖ := by
        calc ‖(Λ0 - m * c2 - m * (m - 1)) * z‖ * ‖W m‖ ≤ θ * (θ ^ ((m + c0) / p) * ‖W 1‖) :=
              mul_le_mul hL ih.1 (norm_nonneg _) hθ0.le
          _ = θ ^ ((m + c0) / p + 1) * ‖W 1‖ := by ring
          _ ≤ θ ^ ((m + 1 + 1 + c0) / p) * ‖W 1‖ :=
              mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hθ0.le hθ1 hgm) (norm_nonneg _)
      have hnorm : ‖W (m + 1 + 1)‖ = ‖(1 - z) * W (m + 1 + 1)‖ := by
        rw [norm_mul (1 - z), h1z, one_mul]
      rw [hnorm, hrec m]
      refine (norm_sub_le_max_padicAlgCl _ _).trans (max_le ?_ ?_)
      · rw [norm_mul, norm_neg]; exact t1
      · rw [norm_mul]; exact t2
  -- Taylor expansion at `z`
  have hfact : ∀ j, (j.factorial : K) * (hasseDeriv j P).eval z = d j := by
    intro j
    have h := congrFun (factorial_smul_hasseDeriv (R := K) (k := j)) P
    rw [LinearMap.smul_apply] at h
    simp only [hd]
    rw [← h, eval_smul, nsmul_eq_mul]
  have htaylor : P.eval w =
      ∑ j ∈ range (P.natDegree + 1), (hasseDeriv j P).eval z * (w - z) ^ j := by
    have h := taylor_eval z P (w - z)
    rw [sub_add_cancel] at h
    rw [← h, eval_eq_sum_range, natDegree_taylor]
    simp only [taylor_coeff]
  -- `P'(z) ≠ 0`
  have hW1 : W 1 ≠ 0 := by
    intro h0
    have hall : ∀ j, d j = 0 := by
      intro j
      have h1 := (hclaim j).1
      rw [h0, norm_zero, mul_zero] at h1
      have h2 : W j = 0 := norm_le_zero_iff.mp h1
      simp only [hW] at h2
      exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero _ hz0)
    apply hP
    rw [← taylor_eq_zero (r := z)]
    ext j
    rw [taylor_coeff, coeff_zero]
    have h := hfact j
    rw [hall j] at h
    exact (mul_eq_zero.mp h).resolve_left (Nat.cast_ne_zero.mpr j.factorial_ne_zero)
  -- the valuation `h = min(1, v(z) - 1)` and `θ = p^{-h}`
  set vz := padicVal p z with hvz
  have hvz1 : 1 ≤ vz := by
    rw [hvz, padicVal_def]
    have := Real.logb_le_logb_of_le hp1 hzpos hzp
    rw [Real.logb_inv, Real.logb_self_eq_one hp1] at this
    linarith
  set hh := min 1 (vz - 1) with hhh
  have hh0 : 0 ≤ hh := le_min zero_le_one (by linarith)
  have hh1 : hh ≤ 1 := min_le_left _ _
  have hlogθ : Real.logb p θ = -hh := by
    have hb : Real.logb p ((p : ℝ) * ‖z‖) = 1 - vz := by
      rw [Real.logb_mul hp0.ne' hzpos.ne', Real.logb_self_eq_one hp1, hvz, padicVal_def]
      ring
    have ha : Real.logb p (p : ℝ)⁻¹ = -1 := by
      rw [Real.logb_inv, Real.logb_self_eq_one hp1]
    rcases le_total ((p : ℝ)⁻¹) ((p : ℝ) * ‖z‖) with hab | hab
    · rw [hθ, max_eq_right hab, hb]
      have := Real.logb_le_logb_of_le hp1 (inv_pos.mpr hp0) hab
      rw [ha, hb] at this
      rw [hhh, min_eq_right (show vz - 1 ≤ 1 by linarith)]
      ring
    · rw [hθ, max_eq_left hab, ha]
      have := Real.logb_le_logb_of_le hp1 (mul_pos hp0 hzpos) hab
      rw [ha, hb] at this
      rw [hhh, min_eq_left (show (1 : ℝ) ≤ vz - 1 by linarith)]
  -- contradiction with a too close root
  by_contra hcon
  have hcon' := not_le.mp hcon
  set κ := 1 / ((p : ℝ) - 1) - hh / p with hκ
  set ε := w - z with hε
  have hε0 : ε ≠ 0 := sub_ne_zero.mpr hwz
  have hεpos : 0 < ‖ε‖ := norm_pos_iff.mpr hε0
  set r := ‖ε‖ / ‖z‖ with hr
  have hrpos : 0 < r := div_pos hεpos hzpos
  have hlogr : Real.logb p r < -κ := by
    rw [hr, Real.logb_div hεpos.ne' hzpos.ne']
    have h1 : padicVal p ε = -Real.logb p ‖ε‖ := padicVal_def _ _
    have h2 : vz = -Real.logb p ‖z‖ := padicVal_def _ _
    linarith
  have hW1pos : 0 < ‖W 1‖ := norm_pos_iff.mpr hW1
  -- the terms of the expansion
  obtain ⟨f, hf⟩ : ∃ f : ℕ → K, f = fun j => (hasseDeriv j P).eval z * ε ^ j := ⟨_, rfl⟩
  have htaylor' : P.eval w = ∑ j ∈ range (P.natDegree + 1), f j := by
    rw [hf]; exact htaylor
  have hf0 : f 0 = 0 := by simp [hf, hz]
  have hf1 : ‖f 1‖ = ‖W 1‖ * r := by
    have hzne : ‖z‖ ≠ 0 := hzpos.ne'
    simp only [hf, hW, hd, hasseDeriv_one, pow_one, Function.iterate_one, norm_mul, hr]
    rw [mul_div_assoc', eq_div_iff hzne]
    ring
  have hfj : ∀ i : ℕ, ‖f (i + 2)‖ < ‖f 1‖ := by
    intro i
    have hjf : ((i + 2).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (i + 2).factorial_ne_zero
    have hnf : ‖((i + 2).factorial : K)‖ = ((p : ℝ) ^ padicValNat p (i + 2).factorial)⁻¹ :=
      norm_natCast_padicAlgCl (i + 2).factorial_ne_zero
    have hHj : (hasseDeriv (i + 2) P).eval z =
        W (i + 2) / (z ^ (i + 2) * ((i + 2).factorial : K)) := by
      rw [eq_div_iff (mul_ne_zero (pow_ne_zero _ hz0) hjf)]
      simp only [hW]
      rw [← hfact (i + 2)]
      ring
    have hzne : ‖z‖ ≠ 0 := hzpos.ne'
    have hpv : (0 : ℝ) < (p : ℝ) ^ padicValNat p (i + 2).factorial := pow_pos hp0 _
    have hpv' := hpv.ne'
    have hnorm : ‖f (i + 2)‖ =
        ‖W (i + 2)‖ * r ^ (i + 2) * (p : ℝ) ^ padicValNat p (i + 2).factorial := by
      simp only [hf]
      rw [hHj, norm_mul, norm_div, norm_mul (z ^ (i + 2)), norm_pow z, norm_pow ε, hnf, hr,
        div_pow]
      field_simp
    have hX0pos : 0 < θ ^ ((i + 2 + c0) / p) * r ^ (i + 1) *
        (p : ℝ) ^ padicValNat p (i + 2).factorial :=
      mul_pos (mul_pos (pow_pos hθ0 _) (pow_pos hrpos _)) hpv
    have hlogX : Real.logb p (θ ^ ((i + 2 + c0) / p) * r ^ (i + 1) *
        (p : ℝ) ^ padicValNat p (i + 2).factorial) =
        -(((i + 2 + c0) / p : ℕ) : ℝ) * hh + ((i : ℝ) + 1) * Real.logb p r +
          (padicValNat p (i + 2).factorial : ℝ) := by
      rw [Real.logb_mul (mul_pos (pow_pos hθ0 _) (pow_pos hrpos _)).ne' hpv.ne',
        Real.logb_mul (pow_pos hθ0 _).ne' (pow_pos hrpos _).ne', Real.logb_pow, Real.logb_pow,
        Real.logb_pow, hlogθ, Real.logb_self_eq_one hp1]
      push_cast
      ring
    have hfb := factorial_radius_bound (p := p) (j := i + 2) (by omega) hh0 hh1
    have hgj : (((i + 2) / p : ℕ) : ℝ) ≤ (((i + 2 + c0) / p : ℕ) : ℝ) := by
      exact_mod_cast Nat.div_le_div_right (by omega)
    have hjcast : ((i + 2 : ℕ) : ℝ) - 1 = (i : ℝ) + 1 := by push_cast; ring
    rw [hjcast] at hfb
    have hX1 : θ ^ ((i + 2 + c0) / p) * r ^ (i + 1) *
        (p : ℝ) ^ padicValNat p (i + 2).factorial < 1 := by
      rw [← Real.logb_neg_iff hp1 hX0pos, hlogX]
      have h1 : ((i : ℝ) + 1) * Real.logb p r < ((i : ℝ) + 1) * (-κ) :=
        mul_lt_mul_of_pos_left hlogr (by positivity)
      have h2 : -(((i + 2 + c0) / p : ℕ) : ℝ) * hh ≤ -(((i + 2) / p : ℕ) : ℝ) * hh := by
        nlinarith
      rw [hκ] at h1
      nlinarith
    have hc := (hclaim (i + 2)).1
    have hbound : ‖f (i + 2)‖ ≤ ‖W 1‖ * r * (θ ^ ((i + 2 + c0) / p) * r ^ (i + 1) *
        (p : ℝ) ^ padicValNat p (i + 2).factorial) := by
      rw [hnorm]
      have hrj : r ^ (i + 2) = r * r ^ (i + 1) := by ring
      rw [hrj]
      calc ‖W (i + 2)‖ * (r * r ^ (i + 1)) * (p : ℝ) ^ padicValNat p (i + 2).factorial ≤
            (θ ^ ((i + 2 + c0) / p) * ‖W 1‖) * (r * r ^ (i + 1)) *
              (p : ℝ) ^ padicValNat p (i + 2).factorial :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hc (mul_pos hrpos (pow_pos hrpos _)).le) hpv.le
        _ = ‖W 1‖ * r * (θ ^ ((i + 2 + c0) / p) * r ^ (i + 1) *
              (p : ℝ) ^ padicValNat p (i + 2).factorial) := by ring
    rw [hf1]
    calc ‖f (i + 2)‖ ≤ ‖W 1‖ * r * (θ ^ ((i + 2 + c0) / p) * r ^ (i + 1) *
          (p : ℝ) ^ padicValNat p (i + 2).factorial) := hbound
      _ < ‖W 1‖ * r * 1 := mul_lt_mul_of_pos_left hX1 (mul_pos hW1pos hrpos)
      _ = ‖W 1‖ * r := mul_one _
  -- the degree is positive
  obtain ⟨N, hN⟩ : ∃ N, P.natDegree = N + 1 := by
    rcases Nat.eq_zero_or_pos P.natDegree with h0 | h0
    · exfalso
      rw [eq_C_of_natDegree_eq_zero h0, eval_C] at hz
      apply hP
      rw [eq_C_of_natDegree_eq_zero h0, hz, C_0]
    · exact ⟨P.natDegree - 1, by omega⟩
  rw [htaylor', hN, sum_range_succ', sum_range_succ'] at hw
  have hw' : (∑ i ∈ range N, f (i + 1 + 1)) + f 1 = 0 := by
    simpa only [zero_add, hf0, add_zero] using hw
  set T := ∑ i ∈ range N, f (i + 1 + 1) with hT
  have hTlt : ‖T‖ < ‖f 1‖ := by
    obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le (range N)
      (fun i => f (i + 1 + 1))
    by_cases hne : (range N).Nonempty
    · exact lt_of_le_of_lt hle (hfj i)
    · rw [not_nonempty_iff_eq_empty] at hne
      rw [hT, hne, sum_empty, norm_zero, hf1]
      exact mul_pos hW1pos hrpos
  have hsum : ‖T + f 1‖ = ‖f 1‖ := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hTlt.ne, max_eq_right hTlt.le]
  rw [hw', norm_zero, hf1] at hsum
  have : 0 < ‖W 1‖ * r := mul_pos hW1pos hrpos
  linarith

/-- **Paired prime separation (4.15).** Under the hypotheses of `padicVal_sub_le_of_ode`, if
moreover `v_p(w) = v_p(z)`, then with `ρ_p = p/(p-1)`,
`v_p(w - z) - min(v_p(w), v_p(z)) ≤ 1/p + (ρ_p - v_p(z))_+/p`. -/
theorem padicVal_sub_le_of_eq {c0 : ℕ} (hc0 : c0 + 2 ≤ p) {B1 c2 Λ0 : K} {P : K[X]}
    (hP : P ≠ 0)
    (hode : polyX * (1 - polyX) * derivative (derivative P) + (C B1 - C c2 * polyX) * derivative P +
      C Λ0 * P = 0)
    (hB : ∀ m : ℕ, ‖B1 + m‖ ≤ 1)
    (hBgain : ∀ m : ℕ, p ∣ m + 2 + c0 → ‖B1 + m‖ ≤ (p : ℝ)⁻¹)
    (hc : ∀ m : ℕ, ‖c2 + 2 * m‖ ≤ p)
    (hΛ : ∀ m : ℕ, ‖Λ0 - m * c2 - m * (m - 1)‖ ≤ p)
    {z w : K} (hz : P.eval z = 0) (hw : P.eval w = 0) (hz0 : z ≠ 0) (hzp : ‖z‖ ≤ (p : ℝ)⁻¹)
    (hwz : w ≠ z) (hvw : padicVal p w = padicVal p z) :
    padicVal p (w - z) ≤ min (padicVal p w) (padicVal p z) + 1 / p +
      max ((p : ℝ) / ((p : ℝ) - 1) - padicVal p z) 0 / p := by
  have h := padicVal_sub_le_of_ode hc0 hP hode hB hBgain hc hΛ hz hw hz0 hzp hwz
  have hs := separation_constant_le (p := p) (padicVal p z)
  rw [hvw, min_self]
  linarith

end Taylor

/-! ### Integrality of the numerators and the coefficient valuations -/

section Coefficients

variable {p : ℕ} [hp : Fact p.Prime]

local notation "K" => PadicAlgCl p

theorem norm_ratCast_padicAlgCl_eq (q : ℚ) : ‖(q : K)‖ = ‖(q : ℚ_[p])‖ := by
  rw [← map_ratCast (algebraMap ℚ_[p] K) q, PadicAlgCl.norm_extends]

/-- **Coefficient valuations of the monic endpoint polynomial (4.11).** If `v_p(α) = -1`,
`v_p(β) ≥ 0` and `β > -1`, then the coefficient `b_j` of `n! P_n^{(α,β)}(2X-1)/(n+α+β+1)_n`
(`j ≤ n`) is nonzero and `v_p(b_j) ≥ (n - j) + v_p(n!) - v_p(j!)`. -/
theorem padicValRat_monicEndpointCoeff_ge {α β : ℚ} (hα : padicValRat p α = -1)
    (hβ : 0 ≤ padicValRat p β) (hβ1 : -1 < β) {n j : ℕ} (hj : j ≤ n) :
    monicEndpointCoeff α β n j ≠ 0 ∧
      ((n - j : ℕ) : ℤ) + padicValNat p n.factorial - padicValNat p j.factorial ≤
        padicValRat p (monicEndpointCoeff α β n j) := by
  have hden := padicValRat_ascPochhammer_of_neg (p := p) (e := 1) one_pos
    (by rw [hα]; rfl) hβ (n + j + 1) (n - j)
  have e1 : ((n + j + 1 : ℕ) : ℚ) + α + β = (n : ℚ) + α + β + j + 1 := by push_cast; ring
  rw [e1] at hden
  have hnumpos : 0 < (ascPochhammer ℚ (n - j)).eval (β + j + 1) :=
    ascPochhammer_pos _ _ (by have : (0 : ℚ) ≤ j := Nat.cast_nonneg j; linarith)
  have hb := padicValRat_monicEndpointCoeff (p := p) α β n j hj hnumpos.ne' hden.1
  refine ⟨hb.1, ?_⟩
  rw [hb.2, hden.2]
  -- the numerator is divisible by `(n-j)!`
  have hx : 0 ≤ padicValRat p (β + j + 1) := by
    have := padicValRat_add_natCast_nonneg (p := p) hβ (j + 1)
    rwa [show β + ((j + 1 : ℕ) : ℚ) = β + j + 1 by push_cast; ring] at this
  have hv := padicValNat_factorial_le_padicValRat_ascPochhammer hx (n - j) hnumpos.ne'
  have hch := padicValNat_choose_add_factorial (p := p) n j hj
  have hch' : (padicValNat p (n.choose j) : ℤ) + padicValNat p j.factorial +
      padicValNat p (n - j).factorial = padicValNat p n.factorial := by exact_mod_cast hch
  omega

/-- From a valuation bound to the coefficient hypothesis of `sum_logb_max_le_of_coeff`:
if `v_p(q) ≥ ρ(n - j) - D` (for `q ≠ 0`), then `‖q‖ (p^{-ρ})^j ≤ p^D (p^{-ρ})^n`. -/
theorem norm_mul_rpow_le_of_padicValRat {q : ℚ} {ρ D : ℝ} {n j : ℕ}
    (h : q ≠ 0 → ρ * ((n : ℝ) - j) - D ≤ padicValRat p q) :
    ‖(q : K)‖ * ((p : ℝ) ^ (-ρ)) ^ j ≤ (p : ℝ) ^ D * ((p : ℝ) ^ (-ρ)) ^ n := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  rcases eq_or_ne q 0 with rfl | h0
  · simp only [Rat.cast_zero, norm_zero, zero_mul]
    positivity
  · rw [norm_ratCast_padicAlgCl_of_ne h0, ← Real.rpow_intCast, ← Real.rpow_natCast,
      ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_mul hp0.le,
      ← Real.rpow_add hp0, ← Real.rpow_add hp0]
    apply Real.rpow_le_rpow_of_exponent_le hp1
    have := h h0
    push_cast
    nlinarith

end Coefficients

/-! ### Resultants and endpoint values through roots -/

section RootSums

variable {p : ℕ} [hp : Fact p.Prime]

local notation "K" => PadicAlgCl p

theorem norm_intCast_padicAlgCl_eq_one {k : ℤ} (hk : ¬ (p : ℤ) ∣ k) : ‖(k : K)‖ = 1 := by
  rw [norm_intCast_padicAlgCl]
  exact le_antisymm (PadicInt.norm_le_one _)
    (not_lt.mp fun h => hk ((PadicInt.norm_int_lt_one_iff_dvd k).mp h))

theorem padicVal_intCast_padicAlgCl {R : ℤ} (hR : R ≠ 0) :
    padicVal p (R : K) = padicValInt p R := by
  rw [← padicVal_intCast (p := p) hR, padicVal_def, padicVal_def, norm_intCast_padicAlgCl]

theorem norm_leadingCoeff_map_intCast {A : ℤ[X]} (hA : ¬ (p : ℤ) ∣ A.leadingCoeff) :
    ‖(A.map (Int.castRingHom K)).leadingCoeff‖ = 1 := by
  rw [leadingCoeff_map_of_injective (RingHom.injective_int (Int.castRingHom K)), eq_intCast]
  exact norm_intCast_padicAlgCl_eq_one hA

theorem norm_eval_map_intCast {A : ℤ[X]} (hA : ¬ (p : ℤ) ∣ A.leadingCoeff) (x : K) :
    ‖(A.map (Int.castRingHom K)).eval x‖ =
      ((A.map (Int.castRingHom K)).roots.map fun t => ‖x - t‖).prod := by
  rw [(IsAlgClosed.splits _).eval_eq_prod_roots, norm_mul, norm_leadingCoeff_map_intCast hA,
    one_mul, norm_multiset_prod_map]

/-- `v_p(A(a)) = ∑_{A(t) = 0} v_p(a - t)` for `A ∈ ℤ[X]` with `p ∤ lc A` and `A(a) ≠ 0`. -/
theorem padicValInt_eval_eq_sum {A : ℤ[X]} (hA : ¬ (p : ℤ) ∣ A.leadingCoeff) {a : ℤ}
    (ha : A.eval a ≠ 0) :
    (padicValInt p (A.eval a) : ℝ) =
      ((A.map (Int.castRingHom K)).roots.map fun t => padicVal p ((a : K) - t)).sum := by
  rw [← padicVal_intCast_padicAlgCl (p := p) ha]
  have he : ((A.eval a : ℤ) : K) = (A.map (Int.castRingHom K)).eval (a : K) := by
    rw [eval_intCast_map, eq_intCast, Int.cast_id]
  have hne : ((A.eval a : ℤ) : K) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hprod := norm_eval_map_intCast hA (a : K)
  rw [← he] at hprod
  have hfac : ∀ t ∈ (A.map (Int.castRingHom K)).roots, ‖(a : K) - t‖ ≠ 0 := by
    intro t ht h0
    have : ‖((A.eval a : ℤ) : K)‖ = 0 := by
      rw [hprod]
      exact Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨t, ht, h0⟩)
    exact hne (norm_eq_zero.mp this)
  rw [padicVal_def, hprod, logb_multiset_prod_map _ _ hfac, ← Multiset.sum_map_neg]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun t _ => (padicVal_def _ _).symm)

/-- **The resultant through roots.** For `A, B ∈ ℤ[X]` with leading coefficients prime to `p`
and `Res(A,B) ≠ 0`, the roots of `A` and `B` in `PadicAlgCl p` are distinct and
`v_p(Res(A,B)) = ∑_{A(t)=0} ∑_{B(s)=0} v_p(t - s)`. -/
theorem padicValInt_resultant_eq_sum {A B : ℤ[X]} (hA : ¬ (p : ℤ) ∣ A.leadingCoeff)
    (hB : ¬ (p : ℤ) ∣ B.leadingCoeff) (hR : resultant A B ≠ 0) :
    (∀ t ∈ (A.map (Int.castRingHom K)).roots, ∀ s ∈ (B.map (Int.castRingHom K)).roots,
        t ≠ s) ∧
      (padicValInt p (resultant A B) : ℝ) = ((A.map (Int.castRingHom K)).roots.map fun t =>
        ((B.map (Int.castRingHom K)).roots.map fun s => padicVal p (t - s)).sum).sum := by
  set φ := Int.castRingHom K with hφ
  set A' := A.map φ with hA'
  set B' := B.map φ with hB'
  have hinj : Function.Injective φ := RingHom.injective_int φ
  have hAdeg : A'.natDegree = A.natDegree := natDegree_map_eq_of_injective hinj A
  have hBdeg : B'.natDegree = B.natDegree := natDegree_map_eq_of_injective hinj B
  have hres : φ (resultant A B) = A'.leadingCoeff ^ B.natDegree *
      (A'.roots.map fun t => B'.leadingCoeff * (B'.roots.map fun s => t - s).prod).prod := by
    rw [← resultant_map_map, ← hAdeg,
      resultant_eq_prod_eval A' B' _ hBdeg.le (IsAlgClosed.splits _)]
    congr 2
    exact Multiset.map_congr rfl fun t _ => (IsAlgClosed.splits B').eval_eq_prod_roots t
  have hnorm : ‖((resultant A B : ℤ) : K)‖ =
      (A'.roots.map fun t => (B'.roots.map fun s => ‖t - s‖).prod).prod := by
    rw [← eq_intCast φ, hres, norm_mul, norm_pow, norm_leadingCoeff_map_intCast hA, one_pow,
      one_mul, norm_multiset_prod_map]
    congr 1
    refine Multiset.map_congr rfl fun t _ => ?_
    rw [norm_mul, norm_leadingCoeff_map_intCast hB, one_mul, norm_multiset_prod_map]
  have hne : ‖((resultant A B : ℤ) : K)‖ ≠ 0 := norm_ne_zero_iff.mpr (Int.cast_ne_zero.mpr hR)
  have hdist : ∀ t ∈ A'.roots, ∀ s ∈ B'.roots, ‖t - s‖ ≠ 0 := by
    intro t ht s hs h0
    apply hne
    rw [hnorm]
    refine Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨t, ht, ?_⟩)
    exact Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨s, hs, h0⟩)
  refine ⟨fun t ht s hs h => hdist t ht s hs (by rw [h, sub_self, norm_zero]), ?_⟩
  have hinner : ∀ t ∈ A'.roots, (B'.roots.map fun s => ‖t - s‖).prod ≠ 0 := by
    intro t ht h0
    obtain ⟨s, hs, hs0⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp h0)
    exact hdist t ht s hs hs0
  rw [← padicVal_intCast_padicAlgCl (p := p) hR, padicVal_def, hnorm,
    logb_multiset_prod_map _ _ hinner, ← Multiset.sum_map_neg]
  congr 1
  refine Multiset.map_congr rfl fun t ht => ?_
  rw [logb_multiset_prod_map _ _ (hdist t ht), ← Multiset.sum_map_neg]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun s _ => (padicVal_def _ _).symm)

/-- The bilinear double-sum estimate used to sum (4.15). -/
theorem double_sum_le_min {α : Type*} (SA SB : Multiset α) (F : α → α → ℝ) (x y M : α → ℝ)
    (c : ℝ) (h : ∀ t ∈ SA, ∀ s ∈ SB, F t s ≤ min (x t) (y s) + c + M s) :
    (SA.map fun t => (SB.map fun s => F t s).sum).sum ≤
      min ((Multiset.card SB : ℝ) * (SA.map x).sum) ((Multiset.card SA : ℝ) * (SB.map y).sum) +
        (Multiset.card SA : ℝ) * Multiset.card SB * c +
          (Multiset.card SA : ℝ) * (SB.map M).sum := by
  rw [add_assoc, ← min_add_add_right]
  apply le_min
  · calc (SA.map fun t => (SB.map fun s => F t s).sum).sum ≤
          (SA.map fun t => (SB.map fun s => x t + c + M s).sum).sum := by
          refine Multiset.sum_map_le_sum_map _ _ fun t ht => ?_
          exact Multiset.sum_map_le_sum_map _ _ fun s hs =>
            (h t ht s hs).trans (by linarith [min_le_left (x t) (y s)])
      _ = _ := by
          simp only [Multiset.sum_map_add, Multiset.map_const', Multiset.sum_replicate,
            nsmul_eq_mul, Multiset.sum_map_mul_left]
          ring
  · calc (SA.map fun t => (SB.map fun s => F t s).sum).sum ≤
          (SA.map fun t => (SB.map fun s => y s + c + M s).sum).sum := by
          refine Multiset.sum_map_le_sum_map _ _ fun t ht => ?_
          exact Multiset.sum_map_le_sum_map _ _ fun s hs =>
            (h t ht s hs).trans (by linarith [min_le_right (x t) (y s)])
      _ = _ := by
          simp only [Multiset.sum_map_add, Multiset.map_const', Multiset.sum_replicate,
            nsmul_eq_mul]
          ring

/-- **The local resultant bound, abstract form (proof of Proposition 4.6).** Let `A, B ∈ ℤ[X]`
have leading coefficients prime to `p`, let `z = ε(t - a)` (`‖ε‖ = 1`, `a ∈ ℤ`) be the endpoint
coordinate, and let `S` be the multiset of coordinates of the roots of `AB`. Suppose the roots
are nonzero in this coordinate, satisfy the paired separation (4.15) with the constant `ρ`, and
have total deficit `∑ (ρ - v_p(z))_+ ≤ D`. Then
`v_p(Res(A,B)) ≤ min(e v_p(A(a)), k v_p(B(a))) + ke/p + kD/p`, `k = deg A`, `e = deg B`. -/
theorem padicValInt_resultant_le_of_roots {A B : ℤ[X]} (hA : ¬ (p : ℤ) ∣ A.leadingCoeff)
    (hB : ¬ (p : ℤ) ∣ B.leadingCoeff) {a : ℤ} {ε : K} (hε : ‖ε‖ = 1) {ρ D : ℝ}
    {S : Multiset K}
    (hS : ((A * B).map (Int.castRingHom K)).roots.map (fun t => ε * (t - a)) = S)
    (hS0 : ∀ z ∈ S, z ≠ 0)
    (hsep : ∀ w ∈ S, ∀ z ∈ S, w ≠ z → padicVal p w = padicVal p z →
      padicVal p (w - z) ≤ padicVal p z + 1 / p + max (ρ - padicVal p z) 0 / p)
    (hdef : (S.map fun z => max (ρ - padicVal p z) 0).sum ≤ D) :
    (padicValInt p (resultant A B) : ℝ) ≤
      min ((B.natDegree : ℝ) * padicValInt p (A.eval a))
          ((A.natDegree : ℝ) * padicValInt p (B.eval a)) +
        (A.natDegree : ℝ) * B.natDegree / p + (A.natDegree : ℝ) * D / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hD : 0 ≤ D := le_trans (Multiset.sum_nonneg fun x hx => by
    obtain ⟨z, -, rfl⟩ := Multiset.mem_map.mp hx
    exact le_max_right _ _) hdef
  by_cases hR : resultant A B = 0
  · rw [hR, padicValInt.zero, Nat.cast_zero]
    have h1 : 0 ≤ min ((B.natDegree : ℝ) * padicValInt p (A.eval a))
        ((A.natDegree : ℝ) * padicValInt p (B.eval a)) := by positivity
    have h2 : 0 ≤ (A.natDegree : ℝ) * B.natDegree / p := by positivity
    have h3 : 0 ≤ (A.natDegree : ℝ) * D / p := by positivity
    linarith
  obtain ⟨hdisj, heq⟩ := padicValInt_resultant_eq_sum hA hB hR
  set φ := Int.castRingHom K with hφ
  set A' := A.map φ with hA'
  set B' := B.map φ with hB'
  set g : K → K := fun t => ε * (t - a) with hg
  have hA0 : A ≠ 0 := by rintro rfl; simp at hA
  have hB0 : B ≠ 0 := by rintro rfl; simp at hB
  have hinj : Function.Injective φ := RingHom.injective_int φ
  have hAB' : A' * B' ≠ 0 := mul_ne_zero ((Polynomial.map_ne_zero_iff hinj).mpr hA0)
    ((Polynomial.map_ne_zero_iff hinj).mpr hB0)
  have hroots : ((A * B).map φ).roots = A'.roots + B'.roots := by
    rw [Polynomial.map_mul, roots_mul hAB']
  rw [hroots, Multiset.map_add] at hS
  have hgA : ∀ t ∈ A'.roots, g t ∈ S := fun t ht => by
    rw [← hS]; exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_map_of_mem _ ht))
  have hgB : ∀ s ∈ B'.roots, g s ∈ S := fun s hs => by
    rw [← hS]; exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_map_of_mem _ hs))
  have hgnorm : ∀ x y : K, ‖g x - g y‖ = ‖x - y‖ := by
    intro x y
    simp only [hg]
    rw [← mul_sub, norm_mul, hε, one_mul]
    congr 1
    ring
  have hgval : ∀ x y : K, padicVal p (g x - g y) = padicVal p (x - y) := by
    intro x y; rw [padicVal_def, padicVal_def, hgnorm]
  have hgval' : ∀ x : K, padicVal p (g x) = padicVal p ((a : K) - x) := by
    intro x
    rw [padicVal_def, padicVal_def]
    simp only [hg]
    rw [norm_mul, hε, one_mul, norm_sub_rev]
  -- endpoint values
  have hevalA : A.eval a ≠ 0 := by
    intro h0
    have hr : (a : K) ∈ A'.roots := by
      rw [mem_roots ((Polynomial.map_ne_zero_iff hinj).mpr hA0), IsRoot, hφ,
        eval_intCast_map, Int.cast_id, h0, map_zero]
    exact hS0 _ (hgA _ hr) (by simp [hg])
  have hevalB : B.eval a ≠ 0 := by
    intro h0
    have hr : (a : K) ∈ B'.roots := by
      rw [mem_roots ((Polynomial.map_ne_zero_iff hinj).mpr hB0), IsRoot, hφ,
        eval_intCast_map, Int.cast_id, h0, map_zero]
    exact hS0 _ (hgB _ hr) (by simp [hg])
  have hDA := padicValInt_eval_eq_sum (p := p) hA hevalA
  have hDB := padicValInt_eval_eq_sum (p := p) hB hevalB
  -- termwise bound
  have hterm : ∀ t ∈ A'.roots, ∀ s ∈ B'.roots, padicVal p (t - s) ≤
      min (padicVal p ((a : K) - t)) (padicVal p ((a : K) - s)) + 1 / p +
        max (ρ - padicVal p (g s)) 0 / p := by
    intro t ht s hs
    have hts : g t ≠ g s := by
      intro h
      have := hgnorm t s
      rw [h, sub_self, norm_zero] at this
      exact hdisj t ht s hs (sub_eq_zero.mp (norm_eq_zero.mp this.symm))
    rw [← hgval, ← hgval' t, ← hgval' s]
    by_cases hv : padicVal p (g t) = padicVal p (g s)
    · have := hsep _ (hgA t ht) _ (hgB s hs) hts hv
      rw [hv, min_self]
      exact this
    · rw [padicVal_sub_eq_min (hS0 _ (hgA t ht)) (hS0 _ (hgB s hs)) hv]
      have : 0 ≤ max (ρ - padicVal p (g s)) 0 / p := div_nonneg (le_max_right _ _) hp0.le
      have : (0 : ℝ) ≤ 1 / p := by positivity
      linarith
  have hcardA : (Multiset.card A'.roots : ℝ) = A.natDegree := by
    rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_map_eq_of_injective hinj]
  have hcardB : (Multiset.card B'.roots : ℝ) = B.natDegree := by
    rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_map_eq_of_injective hinj]
  have hmain := double_sum_le_min A'.roots B'.roots (fun t s => padicVal p (t - s))
    (fun t => padicVal p ((a : K) - t)) (fun s => padicVal p ((a : K) - s))
    (fun s => max (ρ - padicVal p (g s)) 0 / p) (1 / p) hterm
  rw [hcardA, hcardB, ← hDA, ← hDB, ← heq] at hmain
  -- the deficit over the roots of `B`
  have hdefB : (B'.roots.map fun s => max (ρ - padicVal p (g s)) 0 / p).sum ≤ D / p := by
    rw [Multiset.sum_map_div]
    apply div_le_div_of_nonneg_right _ hp0.le
    rw [← hS, Multiset.map_add, Multiset.sum_add, Multiset.map_map, Multiset.map_map] at hdef
    have hnn : 0 ≤ ((A'.roots.map ((fun z => max (ρ - padicVal p z) 0) ∘ g))).sum :=
      Multiset.sum_nonneg fun x hx => by
        obtain ⟨z, -, rfl⟩ := Multiset.mem_map.mp hx
        exact le_max_right _ _
    have : (B'.roots.map ((fun z => max (ρ - padicVal p z) 0) ∘ g)).sum ≤ D := by linarith
    exact this
  have hk : (0 : ℝ) ≤ A.natDegree := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left hdefB hk
  have e : (A.natDegree : ℝ) * B.natDegree * (1 / p) = (A.natDegree : ℝ) * B.natDegree / p := by
    ring
  have e2 : (A.natDegree : ℝ) * (D / p) = (A.natDegree : ℝ) * D / p := by ring
  linarith

end RootSums

/-! ### The monic endpoint polynomial over `PadicAlgCl p` -/

section MonicEndpointRoots

/-- `y_n^{(b,b')}(t) = (-1)^n (n+b'+b+1)_n / n! · T_n^{(b',b)}(t)`, where `T_n` is the monic
endpoint polynomial (4.11). -/
theorem jacobiShifted_eq_C_mul_monicEndpoint (b b' : ℚ) (n : ℕ)
    (h : (ascPochhammer ℚ n).eval ((n : ℚ) + b' + b + 1) ≠ 0) :
    jacobiShifted b b' n = C ((-1) ^ n * (ascPochhammer ℚ n).eval ((n : ℚ) + b' + b + 1) /
      n.factorial) * monicEndpoint b' b n := by
  rw [jacobiShifted_eq, monicEndpoint_def, ← mul_assoc, ← C_mul]
  have hf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have e : (-1 : ℚ) ^ n * (ascPochhammer ℚ n).eval ((n : ℚ) + b' + b + 1) / n.factorial *
      ((n.factorial : ℚ) / (ascPochhammer ℚ n).eval ((n : ℚ) + b' + b + 1)) = (-1) ^ n := by
    rw [div_mul_div_comm, div_eq_iff (mul_ne_zero hf h)]
    ring
  rw [e]
  have h1 : (1 - 2 * polyX : ℚ[X]) = (-polyX).comp (2 * polyX - 1) := by
    rw [neg_comp, X_comp]
    ring
  rw [h1, ← comp_assoc, jacobiP_comp_neg_X b' b n, mul_comp, C_comp]

/-- In the coordinate `z = 1 - t`: `y_n(1 - z) = (n+α+β+1)_n / n! · T_n^{(α,β)}(z)`. -/
theorem jacobiShifted_comp_one_sub_eq (α β : ℚ) (n : ℕ)
    (h : (ascPochhammer ℚ n).eval ((n : ℚ) + α + β + 1) ≠ 0) :
    (jacobiShifted α β n).comp (C (-1) * polyX + C 1) =
      C ((ascPochhammer ℚ n).eval ((n : ℚ) + α + β + 1) / n.factorial) *
        monicEndpoint α β n := by
  rw [jacobiShifted_eq, comp_assoc, monicEndpoint_def, ← mul_assoc, ← C_mul]
  have hf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have e : (ascPochhammer ℚ n).eval ((n : ℚ) + α + β + 1) / n.factorial *
      ((n.factorial : ℚ) / (ascPochhammer ℚ n).eval ((n : ℚ) + α + β + 1)) = 1 := by
    rw [div_mul_div_comm, div_eq_iff (mul_ne_zero hf h)]
    ring
  rw [e, C_1, one_mul]
  congr 1
  rw [sub_comp, one_comp, mul_comp, X_comp, ofNat_comp]
  simp only [C_neg, C_1]
  ring

variable {p : ℕ} [hp : Fact p.Prime]

local notation "K" => PadicAlgCl p

/-- The differential equation (2.3) of `y_n^{(b,b')}` over `PadicAlgCl p`. -/
theorem jacobiShifted_map_ode (b b' : ℚ) (n : ℕ) :
    polyX * (1 - polyX) * derivative (derivative ((jacobiShifted b b' n).map (algebraMap ℚ K))) +
        (C (((b + 1 : ℚ)) : K) - C (((b + b' + 2 : ℚ)) : K) * polyX) *
          derivative ((jacobiShifted b b' n).map (algebraMap ℚ K)) +
      C ((((n : ℚ) * (n + b + b' + 1) : ℚ)) : K) *
        (jacobiShifted b b' n).map (algebraMap ℚ K) = 0 := by
  have h := congrArg (Polynomial.map (algebraMap ℚ K)) (jacobiShifted_ode b b' n)
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_one, Polynomial.map_C, Polynomial.map_zero, derivative_map,
    eq_ratCast] at h ⊢
  exact h

theorem monicEndpoint_ascPochhammer_ne_zero {α β : ℚ} (hα : padicValRat p α = -1)
    (hβ : 0 ≤ padicValRat p β) (n : ℕ) :
    (ascPochhammer ℚ n).eval ((n : ℚ) + α + β + 1) ≠ 0 := by
  have hden := padicValRat_ascPochhammer_of_neg (p := p) (e := 1) one_pos
    (by rw [hα]; rfl) hβ (n + 1) n
  have e1 : ((n + 1 : ℕ) : ℚ) + α + β = (n : ℚ) + α + β + 1 := by push_cast; ring
  rw [e1] at hden
  exact hden.1

theorem monicEndpoint_map_roots {α β : ℚ} {n : ℕ}
    (h : (ascPochhammer ℚ n).eval ((n : ℚ) + α + β + 1) ≠ 0) :
    (((monicEndpoint α β n).map (algebraMap ℚ K)).roots.map fun w => polyX - C w).prod =
        (monicEndpoint α β n).map (algebraMap ℚ K) ∧
      Multiset.card ((monicEndpoint α β n).map (algebraMap ℚ K)).roots = n := by
  obtain ⟨hmon, hdeg⟩ := monicEndpoint_monic α β n h
  refine ⟨((IsAlgClosed.splits _).eq_prod_roots_of_monic (hmon.map _)).symm, ?_⟩
  rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_map, hdeg]

theorem coeff_monicEndpoint_map {α β : ℚ} {n : ℕ}
    (h : (ascPochhammer ℚ n).eval ((n : ℚ) + α + β + 1) ≠ 0) (j : ℕ) :
    ((monicEndpoint α β n).map (algebraMap ℚ K)).coeff j =
      if j ≤ n then (monicEndpointCoeff α β n j : K) else 0 := by
  rw [coeff_map, monicEndpoint_coeff α β n h j]
  split_ifs <;> simp [eq_ratCast]

/-- **The endpoint ball.** If `v_p(α) = -1`, `v_p(β) ≥ 0` and `β > -1`, then every root `z` of
the monic endpoint polynomial `T_n^{(α,β)}` in `PadicAlgCl p` is nonzero with `v_p(z) ≥ 1`. -/
theorem monicEndpoint_roots_ball {α β : ℚ} (hα : padicValRat p α = -1)
    (hβ : 0 ≤ padicValRat p β) (hβ1 : -1 < β) (n : ℕ) :
    ∀ z ∈ ((monicEndpoint α β n).map (algebraMap ℚ K)).roots, z ≠ 0 ∧ ‖z‖ ≤ (p : ℝ)⁻¹ := by
  have h := monicEndpoint_ascPochhammer_ne_zero hα hβ n
  obtain ⟨hprod, hcard⟩ := monicEndpoint_map_roots (p := p) h
  have hball := norm_le_inv_of_coeff (p := p) ((monicEndpoint α β n).map (algebraMap ℚ K)).roots
    (fun j => by
      rw [hprod, hcard, coeff_monicEndpoint_map h]
      split_ifs with hj
      · have hval : monicEndpointCoeff α β n j ≠ 0 →
            1 * ((n : ℝ) - j) - 0 ≤ padicValRat p (monicEndpointCoeff α β n j) := by
          intro _
          obtain ⟨-, hv⟩ := padicValRat_monicEndpointCoeff_ge hα hβ hβ1 hj
          have hch := padicValNat_choose_add_factorial (p := p) n j hj
          have h1 : ((n - j : ℕ) : ℤ) ≤ padicValRat p (monicEndpointCoeff α β n j) := by omega
          have h2 : ((n - j : ℕ) : ℝ) ≤ (padicValRat p (monicEndpointCoeff α β n j) : ℝ) := by
            exact_mod_cast h1
          rw [Nat.cast_sub hj] at h2
          linarith
        have := norm_mul_rpow_le_of_padicValRat (p := p) hval
        rwa [Real.rpow_neg_one, Real.rpow_zero, one_mul] at this
      · rw [norm_zero, zero_mul]
        positivity)
  intro z hz
  refine ⟨?_, hball z hz⟩
  rintro rfl
  have h0 : ((monicEndpoint α β n).map (algebraMap ℚ K)).eval 0 = 0 := (mem_roots'.mp hz).2
  rw [← coeff_zero_eq_eval_zero, coeff_monicEndpoint_map h] at h0
  simp only [Nat.zero_le, ↓reduceIte] at h0
  exact (padicValRat_monicEndpointCoeff_ge hα hβ hβ1 (Nat.zero_le n)).1 (by exact_mod_cast h0)

/-- **Total endpoint deficit, by the Gauss norm.** If the coefficients of `T_n^{(α,β)}` satisfy
`v_p(b_j) ≥ ρ(n-j) - D`, then `∑_z (ρ - v_p(z))_+ ≤ D` over its roots. This gives the final
inequality of Proposition 4.6 by the Gauss norm. `monicEndpoint_deficit_le_of_hull` gives the
manuscript's Newton polygon proof. -/
theorem monicEndpoint_deficit_le {α β : ℚ} {n : ℕ}
    (h : (ascPochhammer ℚ n).eval ((n : ℚ) + α + β + 1) ≠ 0) {ρ D : ℝ}
    (hval : ∀ j ≤ n, monicEndpointCoeff α β n j ≠ 0 →
      ρ * ((n : ℝ) - j) - D ≤ padicValRat p (monicEndpointCoeff α β n j))
    (h0 : ∀ z ∈ ((monicEndpoint α β n).map (algebraMap ℚ K)).roots, z ≠ 0) :
    (((monicEndpoint α β n).map (algebraMap ℚ K)).roots.map
      fun z => max (ρ - padicVal p z) 0).sum ≤ D := by
  obtain ⟨hprod, hcard⟩ := monicEndpoint_map_roots (p := p) h
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hc : (0 : ℝ) < (p : ℝ) ^ (-ρ) := Real.rpow_pos_of_pos hp0 _
  have hsum := sum_logb_max_le_of_coeff (p := p) (D := D) hc
    ((monicEndpoint α β n).map (algebraMap ℚ K)).roots (fun j => by
      rw [hprod, hcard, coeff_monicEndpoint_map h]
      split_ifs with hj
      · exact norm_mul_rpow_le_of_padicValRat (hval j hj)
      · rw [norm_zero, zero_mul]
        positivity)
  have hmap : (((monicEndpoint α β n).map (algebraMap ℚ K)).roots.map
      fun w => Real.logb p (max 1 (‖w‖ / (p : ℝ) ^ (-ρ)))) =
      ((monicEndpoint α β n).map (algebraMap ℚ K)).roots.map
        fun z => max (ρ - padicVal p z) 0 :=
    Multiset.map_congr rfl fun z hz => logb_max_one_div_eq (h0 z hz) ρ
  rwa [hmap] at hsum

/-- **Total endpoint deficit through the Newton polygon** (the chain of Proposition 4.6). If the
coefficient valuations of `T_n^{(α,β)}` are `v_p(b_j) = ρ(n-j) + θ Φ(j)` with `θ > 0`, `Φ(n) = 0`
and `Φ ≥ -D`, then, by the cited Newton polygon theorem, the root deficits are the positive slopes
of the hull `W` of `(j, Φ(j))`, so `∑_z (ρ - v_p(z))_+ = θ (W(n) - min W) ≤ θ D`. -/
theorem monicEndpoint_deficit_le_of_hull (hNP : NewtonPolygonRootSlopes) {α β : ℚ} {n : ℕ}
    (h : (ascPochhammer ℚ n).eval ((n : ℚ) + α + β + 1) ≠ 0) {ρ θ : ℝ} (hθ : 0 < θ)
    (Φ : ℕ → ℤ)
    (hval : ∀ j ≤ n, monicEndpointCoeff α β n j ≠ 0 ∧
      (padicValRat p (monicEndpointCoeff α β n j) : ℝ) = ρ * ((n : ℝ) - j) + θ * Φ j)
    (hΦn : Φ n = 0) {D : ℝ} (hD : ∀ j ≤ n, -D ≤ Φ j) :
    (((monicEndpoint α β n).map (algebraMap ℚ K)).roots.map
      fun z => max (ρ - padicVal p z) 0).sum ≤ θ * D := by
  obtain ⟨hmon, hdeg⟩ := monicEndpoint_monic α β n h
  refine deficit_le_of_hull hNP (hmon.map (algebraMap ℚ K)) (by rw [natDegree_map, hdeg]) Φ hθ
    (fun j hj => ?_) hΦn hD
  rw [coeff_monicEndpoint_map h]
  simp only [hj, ↓reduceIte]
  obtain ⟨h1, h2⟩ := hval j hj
  refine ⟨by exact_mod_cast h1, ?_⟩
  rw [padicVal_ratCast_padicAlgCl h1]
  exact h2

theorem norm_intCast_div_natCast_le (N : ℤ) {D : ℕ} (hD : D ≠ 0) :
    ‖(N : K) / (D : K)‖ ≤ (p : ℝ) ^ padicValNat p D * ‖(N : K)‖ := by
  rw [norm_div, norm_natCast_padicAlgCl hD, div_inv_eq_mul, mul_comm]

/-- `‖c + 2 + 2m‖ ≤ p` for `c = λ/3 + μ/2` when `v_p(6) = 1`. -/
theorem norm_jacobi_c2_le (hp6 : padicValNat p 6 = 1) {l μ : ℤ} {b b' : ℚ}
    (hbb : b + b' = (l : ℚ) / 3 + (μ : ℚ) / 2) (m : ℕ) :
    ‖(((b + b' + 2 : ℚ)) : K) + 2 * m‖ ≤ p := by
  have hbbK : (b : K) + (b' : K) = (l : K) / 3 + (μ : K) / 2 := by
    have := congrArg (fun q : ℚ => (q : K)) hbb
    push_cast at this
    exact this
  have e : (((b + b' + 2 : ℚ)) : K) + 2 * m =
      ((2 * l + 3 * μ + 12 + 12 * m : ℤ) : K) / ((6 : ℕ) : K) := by
    push_cast
    linear_combination hbbK
  rw [e]
  refine (norm_intCast_div_natCast_le _ (by norm_num)).trans ?_
  rw [hp6, pow_one]
  exact mul_le_of_le_one_right (by positivity) (norm_intCast_padicAlgCl_le_one _)

/-- `‖(n - m)(n + m + c + 1)‖ ≤ p` for `c = λ/3 + μ/2` when `v_p(6) = 1`. -/
theorem norm_jacobi_Λ_le (hp6 : padicValNat p 6 = 1) {l μ : ℤ} {b b' : ℚ}
    (hbb : b + b' = (l : ℚ) / 3 + (μ : ℚ) / 2) (n m : ℕ) :
    ‖((((n : ℚ) * (n + b + b' + 1) : ℚ)) : K) - m * (((b + b' + 2 : ℚ)) : K) -
      m * (m - 1)‖ ≤ p := by
  have hbbK : (b : K) + (b' : K) = (l : K) / 3 + (μ : K) / 2 := by
    have := congrArg (fun q : ℚ => (q : K)) hbb
    push_cast at this
    exact this
  have e : ((((n : ℚ) * (n + b + b' + 1) : ℚ)) : K) - m * (((b + b' + 2 : ℚ)) : K) -
      m * (m - 1) =
      ((((n : ℤ) - m) * (6 * n + 6 * m + 6 + 2 * l + 3 * μ) : ℤ) : K) / ((6 : ℕ) : K) := by
    push_cast
    linear_combination ((n : K) - m) * hbbK
  rw [e]
  refine (norm_intCast_div_natCast_le _ (by norm_num)).trans ?_
  rw [hp6, pow_one]
  exact mul_le_of_le_one_right (by positivity) (norm_intCast_padicAlgCl_le_one _)

end MonicEndpointRoots

/-! ### Proposition 4.6 -/

section Proposition46

theorem padicValNat_two_six : padicValNat 2 6 = 1 := by
  have h := padicValNat.mul (p := 2) (a := 2) (b := 3) (by norm_num) (by norm_num)
  rw [show (2 * 3 : ℕ) = 6 from rfl, padicValNat_self,
    padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3)] at h
  omega

theorem padicValNat_three_six : padicValNat 3 6 = 1 := by
  have h := padicValNat.mul (p := 3) (a := 2) (b := 3) (by norm_num) (by norm_num)
  rw [show (2 * 3 : ℕ) = 6 from rfl, padicValNat_self,
    padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2)] at h
  omega

theorem padicValRat_two_int_div_two {μ : ℤ} (hμ : μ = 1 ∨ μ = -1) :
    padicValRat 2 ((μ : ℚ) / 2) = -1 := by
  have h2 : padicValRat 2 (2 : ℚ) = 1 := by
    have := padicValRat.self (p := 2) (by norm_num)
    simpa using this
  rcases hμ with rfl | rfl
  · rw [Int.cast_one, padicValRat.div one_ne_zero (by norm_num), padicValRat.one, h2]; rfl
  · rw [Int.cast_neg, Int.cast_one, neg_div, padicValRat.neg,
      padicValRat.div one_ne_zero (by norm_num), padicValRat.one, h2]; rfl

theorem padicValRat_two_int_div_three {l : ℤ} (hl : l = 1 ∨ l = -1) :
    padicValRat 2 ((l : ℚ) / 3) = 0 := by
  have h3 : padicValRat 2 (3 : ℚ) = 0 := by
    have := padicValRat.of_nat (p := 2) (n := 3)
    rw [padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3)] at this
    exact_mod_cast this
  rcases hl with rfl | rfl
  · rw [Int.cast_one, padicValRat.div one_ne_zero (by norm_num), padicValRat.one, h3]; rfl
  · rw [Int.cast_neg, Int.cast_one, neg_div, padicValRat.neg,
      padicValRat.div one_ne_zero (by norm_num), padicValRat.one, h3]; rfl

theorem norm_two_jacobi_B_le {l : ℤ} (hl : l = 1 ∨ l = -1) (m : ℕ) :
    ‖((((l : ℚ) / 3 + 1 : ℚ)) : PadicAlgCl 2) + m‖ ≤ 1 ∧
      (2 ∣ m + 2 + 0 →
        ‖((((l : ℚ) / 3 + 1 : ℚ)) : PadicAlgCl 2) + m‖ ≤ ((2 : ℕ) : ℝ)⁻¹) := by
  have e : ((((l : ℚ) / 3 + 1 : ℚ)) : PadicAlgCl 2) + m =
      ((l + 3 + 3 * m : ℤ) : PadicAlgCl 2) / ((3 : ℕ) : PadicAlgCl 2) := by
    push_cast
    ring
  have h3 : padicValNat 2 3 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [e]
  have hle := norm_intCast_div_natCast_le (p := 2) (l + 3 + 3 * m) (D := 3) (by norm_num)
  rw [h3, pow_zero, one_mul] at hle
  refine ⟨hle.trans (norm_intCast_padicAlgCl_le_one _),
    fun hm => hle.trans (norm_intCast_padicAlgCl_le_inv ?_)⟩
  push_cast
  omega

theorem norm_three_jacobi_B_le {μ : ℤ} {δ : ℕ} (hμ : μ = 2 * δ - 1) (m : ℕ) :
    ‖((((μ : ℚ) / 2 + 1 : ℚ)) : PadicAlgCl 3) + m‖ ≤ 1 ∧
      (3 ∣ m + 2 + δ →
        ‖((((μ : ℚ) / 2 + 1 : ℚ)) : PadicAlgCl 3) + m‖ ≤ ((3 : ℕ) : ℝ)⁻¹) := by
  have e : ((((μ : ℚ) / 2 + 1 : ℚ)) : PadicAlgCl 3) + m =
      ((μ + 2 + 2 * m : ℤ) : PadicAlgCl 3) / ((2 : ℕ) : PadicAlgCl 3) := by
    push_cast
    ring
  have h2 : padicValNat 3 2 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  rw [e]
  have hle := norm_intCast_div_natCast_le (p := 3) (μ + 2 + 2 * m) (D := 2) (by norm_num)
  rw [h2, pow_zero, one_mul] at hle
  refine ⟨hle.trans (norm_intCast_padicAlgCl_le_one _),
    fun hm => hle.trans (norm_intCast_padicAlgCl_le_inv ?_)⟩
  push_cast
  omega

theorem map_intCast_eq_map_map (H : ℤ[X]) (F : Type*) [Field F] [CharZero F] :
    H.map (Int.castRingHom F) = (H.map (Int.castRingHom ℚ)).map (algebraMap ℚ F) := by
  rw [Polynomial.map_map]
  congr 1
  exact RingHom.ext_int _ _

/-- The correction `Ψ(j) = s_2(j) - s_2(n) + v_2 binom(n+α, n-j)` of Proposition 4.6 at `p = 2`;
the generalized binomial is `binom(n+b, n-j) = (b+j+1)_{n-j}/(n-j)!`. -/
noncomputable def twoAdicPsi (b : ℚ) (n j : ℕ) : ℤ :=
  ((Nat.digits 2 j).sum : ℤ) - (Nat.digits 2 n).sum +
    (padicValRat 2 ((ascPochhammer ℚ (n - j)).eval (b + j + 1)) -
      padicValNat 2 (n - j).factorial)

/-- **Exact coefficient valuations at `2`** (Proposition 4.6): `v_2(c_j) = 2(n-j) + Ψ(j)`. -/
theorem padicValRat_monicEndpointCoeff_two {α β : ℚ} (hα : padicValRat 2 α = -1)
    (hβ : 0 ≤ padicValRat 2 β) (hβ1 : -1 < β) {n j : ℕ} (hj : j ≤ n) :
    monicEndpointCoeff α β n j ≠ 0 ∧
      padicValRat 2 (monicEndpointCoeff α β n j) = 2 * ((n : ℤ) - j) + twoAdicPsi β n j := by
  have hden := padicValRat_ascPochhammer_of_neg (p := 2) (e := 1) one_pos
    (by rw [hα]; rfl) hβ (n + j + 1) (n - j)
  have e1 : ((n + j + 1 : ℕ) : ℚ) + α + β = (n : ℚ) + α + β + j + 1 := by push_cast; ring
  rw [e1] at hden
  have hnumpos : 0 < (ascPochhammer ℚ (n - j)).eval (β + j + 1) :=
    ascPochhammer_pos _ _ (by have : (0 : ℚ) ≤ j := Nat.cast_nonneg j; linarith)
  have hb := padicValRat_monicEndpointCoeff (p := 2) α β n j hj hnumpos.ne' hden.1
  refine ⟨hb.1, ?_⟩
  rw [hb.2, hden.2, twoAdicPsi]
  have hch := padicValNat_choose_add_factorial (p := 2) n j hj
  have hch' : (padicValNat 2 (n.choose j) : ℤ) + padicValNat 2 j.factorial +
      padicValNat 2 (n - j).factorial = padicValNat 2 n.factorial := by exact_mod_cast hch
  have hLn := sub_one_mul_padicValNat_factorial (p := 2) n
  have hLj := sub_one_mul_padicValNat_factorial (p := 2) j
  have hLk := sub_one_mul_padicValNat_factorial (p := 2) (n - j)
  have hsn := Nat.digit_sum_le 2 n
  have hsj := Nat.digit_sum_le 2 j
  have hsk := Nat.digit_sum_le 2 (n - j)
  have hc : ((n - j : ℕ) : ℤ) = (n : ℤ) - j := Nat.cast_sub hj
  simp only [hc, Nat.cast_one, one_mul]
  omega

theorem twoAdicPsi_self (b : ℚ) (n : ℕ) : twoAdicPsi b n n = 0 := by
  simp [twoAdicPsi]

theorem twoAdicPsi_ge {b : ℚ} (hβ : 0 ≤ padicValRat 2 b) {n j : ℕ}
    (hnum : (ascPochhammer ℚ (n - j)).eval (b + j + 1) ≠ 0) :
    -((Nat.digits 2 n).sum : ℤ) ≤ twoAdicPsi b n j := by
  have hx : 0 ≤ padicValRat 2 (b + j + 1) := by
    have := padicValRat_add_natCast_nonneg (p := 2) hβ (j + 1)
    rwa [show b + ((j + 1 : ℕ) : ℚ) = b + j + 1 by push_cast; ring] at this
  have hv := padicValNat_factorial_le_padicValRat_ascPochhammer (p := 2) hx (n - j) hnum
  unfold twoAdicPsi
  have : (0 : ℤ) ≤ ((Nat.digits 2 j).sum : ℤ) := Nat.cast_nonneg _
  linarith

/-- **Proposition 4.6 at `p = 2`.** Let `H ∈ ℤ[X]` be a nonzero rational multiple of
`y_n = P_n^{(λ/3,μ/2)}(1-2t)` with odd leading coefficient, and `H = AB` with `A, B ∈ ℤ[X]`,
`k = deg A`, `e = deg B`. Then, with `D_{2,A} = v_2(A(0))` and `D_{2,B} = v_2(B(0))`,
`v_2(Res(A,B)) ≤ min(e D_{2,A}, k D_{2,B}) + ke/2 + (k/2) s_2(n)`. -/
theorem padicValInt_two_resultant_le (hNP : NewtonPolygonRootSlopes) {l μ : ℤ}
    (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    {n : ℕ} {H A B : ℤ[X]} {c : ℚ} (hc : c ≠ 0)
    (hH : H.map (Int.castRingHom ℚ) = C c * jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n)
    (hlc : ¬ (2 : ℤ) ∣ H.leadingCoeff) (hAB : H = A * B) :
    (padicValInt 2 (resultant A B) : ℝ) ≤
      min ((B.natDegree : ℝ) * padicValInt 2 (A.eval 0))
          ((A.natDegree : ℝ) * padicValInt 2 (B.eval 0)) +
        (A.natDegree : ℝ) * B.natDegree / 2 + (A.natDegree : ℝ) / 2 * (Nat.digits 2 n).sum := by
  have hv1 := padicValRat_two_int_div_two hμ
  have hv2 := padicValRat_two_int_div_three hl
  have hl1 : -1 < (l : ℚ) / 3 := by rcases hl with rfl | rfl <;> norm_num
  have hden := monicEndpoint_ascPochhammer_ne_zero (p := 2) hv1 hv2.ge n
  have hball := monicEndpoint_roots_ball (p := 2) hv1 hv2.ge hl1 n
  have hrel := jacobiShifted_eq_C_mul_monicEndpoint ((l : ℚ) / 3) ((μ : ℚ) / 2) n hden
  set κ : ℚ := (-1) ^ n * (ascPochhammer ℚ n).eval ((n : ℚ) + (μ : ℚ) / 2 + (l : ℚ) / 3 + 1) /
    n.factorial with hκ
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hden)
      (by exact_mod_cast n.factorial_ne_zero)
  set fK := (monicEndpoint ((μ : ℚ) / 2) ((l : ℚ) / 3) n).map (algebraMap ℚ (PadicAlgCl 2))
    with hfK
  have hHK : H.map (Int.castRingHom (PadicAlgCl 2)) = C (((c * κ : ℚ)) : PadicAlgCl 2) * fK := by
    rw [map_intCast_eq_map_map, hH, hrel, ← mul_assoc, ← C_mul, Polynomial.map_mul,
      Polynomial.map_C, eq_ratCast]
  have hcκ : (((c * κ : ℚ)) : PadicAlgCl 2) ≠ 0 := by exact_mod_cast mul_ne_zero hc hκ0
  have hS : ((A * B).map (Int.castRingHom (PadicAlgCl 2))).roots.map
      (fun t => (1 : PadicAlgCl 2) * (t - ((0 : ℤ) : PadicAlgCl 2))) = fK.roots := by
    rw [← hAB, hHK, roots_C_mul _ hcκ]
    simp
  have hlcA : ¬ ((2 : ℕ) : ℤ) ∣ A.leadingCoeff := by
    intro h
    apply hlc
    rw [hAB, leadingCoeff_mul]
    exact dvd_mul_of_dvd_left (by exact_mod_cast h) _
  have hlcB : ¬ ((2 : ℕ) : ℤ) ∣ B.leadingCoeff := by
    intro h
    apply hlc
    rw [hAB, leadingCoeff_mul]
    exact dvd_mul_of_dvd_right (by exact_mod_cast h) _
  have hS0 : ∀ z ∈ fK.roots, z ≠ 0 := fun z hz => (hball z hz).1
  -- the Taylor separation
  have hPK : (jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n).map (algebraMap ℚ (PadicAlgCl 2)) =
      C ((κ : ℚ) : PadicAlgCl 2) * fK := by
    rw [hrel, Polynomial.map_mul, Polynomial.map_C, eq_ratCast]
  have hfK0 : fK ≠ 0 := ((monicEndpoint_monic _ _ n hden).1.map _).ne_zero
  have hP0 :
      (jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n).map (algebraMap ℚ (PadicAlgCl 2)) ≠ 0 := by
    rw [hPK]
    exact mul_ne_zero (C_ne_zero.mpr (by exact_mod_cast hκ0)) hfK0
  have hroot : ∀ z ∈ fK.roots,
      ((jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n).map (algebraMap ℚ (PadicAlgCl 2))).eval z
        = 0 := by
    intro z hz
    rw [hPK, eval_mul, eval_C, (mem_roots'.mp hz).2, mul_zero]
  have hbb : (l : ℚ) / 3 + (μ : ℚ) / 2 = (l : ℚ) / 3 + (μ : ℚ) / 2 := rfl
  have hsep : ∀ w ∈ fK.roots, ∀ z ∈ fK.roots, w ≠ z → padicVal 2 w = padicVal 2 z →
      padicVal 2 (w - z) ≤ padicVal 2 z + 1 / ((2 : ℕ) : ℝ) +
        max (2 - padicVal 2 z) 0 / ((2 : ℕ) : ℝ) := by
    intro w hw z hz hwz hv
    have h := padicVal_sub_le_of_eq (p := 2) (c0 := 0) (by norm_num) hP0
      (jacobiShifted_map_ode _ _ n) (fun m => (norm_two_jacobi_B_le hl m).1)
      (fun m => (norm_two_jacobi_B_le hl m).2) (norm_jacobi_c2_le padicValNat_two_six hbb)
      (norm_jacobi_Λ_le padicValNat_two_six hbb n) (hroot z hz) (hroot w hw) (hball z hz).1
      (hball z hz).2 hwz hv
    have e2 : ((2 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) - 1) = 2 := by norm_num
    rwa [hv, min_self, e2] at h
  -- the total deficit
  have hdef := monicEndpoint_deficit_le_of_hull (p := 2) hNP hden (ρ := 2) (θ := 1) one_pos
    (twoAdicPsi ((l : ℚ) / 3) n) (fun j hj => by
      obtain ⟨h1, h2⟩ := padicValRat_monicEndpointCoeff_two hv1 hv2.ge hl1 hj
      refine ⟨h1, ?_⟩
      have := congrArg (Int.cast : ℤ → ℝ) h2
      push_cast at this ⊢
      linarith)
    (twoAdicPsi_self _ n) (D := ((Nat.digits 2 n).sum : ℝ)) (fun j hj => by
      have hnum : (ascPochhammer ℚ (n - j)).eval ((l : ℚ) / 3 + j + 1) ≠ 0 :=
        (ascPochhammer_pos _ _ (by
          have : (0 : ℚ) ≤ j := Nat.cast_nonneg j
          linarith)).ne'
      have := twoAdicPsi_ge hv2.ge hnum (n := n) (j := j)
      exact_mod_cast this)
  rw [one_mul] at hdef
  have key := padicValInt_resultant_le_of_roots (p := 2) hlcA hlcB (a := 0)
    (ε := (1 : PadicAlgCl 2)) norm_one hS hS0 hsep hdef
  simp only [Nat.cast_ofNat] at key
  linarith

/-- **Proposition 4.6 at `p = 3`.** Let `H ∈ ℤ[X]` be a nonzero rational multiple of
`y_n = P_n^{(λ/3,μ/2)}(1-2t)` with leading coefficient prime to `3`, `δ = (μ+1)/2`, and
`H = AB` with `A, B ∈ ℤ[X]`, `k = deg A`, `e = deg B`. Then, with `D_{3,A} = v_3(A(1))` and
`D_{3,B} = v_3(B(1))`,
`v_3(Res(A,B)) ≤ min(e D_{3,A}, k D_{3,B}) + ke/3 + (k/6) s_3(2n+δ)`. -/
theorem padicValInt_three_resultant_le (hNP : NewtonPolygonRootSlopes) {l μ : ℤ}
    (hl : l = 1 ∨ l = -1) {δ : ℕ} (hδ : δ ≤ 1)
    (hμ : μ = 2 * δ - 1) {n : ℕ} {H A B : ℤ[X]} {c : ℚ} (hc : c ≠ 0)
    (hH : H.map (Int.castRingHom ℚ) = C c * jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n)
    (hlc : ¬ (3 : ℤ) ∣ H.leadingCoeff) (hAB : H = A * B) :
    (padicValInt 3 (resultant A B) : ℝ) ≤
      min ((B.natDegree : ℝ) * padicValInt 3 (A.eval 1))
          ((A.natDegree : ℝ) * padicValInt 3 (B.eval 1)) +
        (A.natDegree : ℝ) * B.natDegree / 3 + (A.natDegree : ℝ) / 6 * digitSum3 (2 * n + δ) := by
  have hμ' : μ = 1 ∨ μ = -1 := by omega
  have hv1 := padicValRat_three_int_div_three hl
  have hv2 := padicValRat_three_int_div_two hμ'
  have hμ1 : -1 < (μ : ℚ) / 2 := by rcases hμ' with h | h <;> rw [h] <;> norm_num
  have hden := monicEndpoint_ascPochhammer_ne_zero (p := 3) hv1 hv2.ge n
  have hball := monicEndpoint_roots_ball (p := 3) hv1 hv2.ge hμ1 n
  set fK := (monicEndpoint ((l : ℚ) / 3) ((μ : ℚ) / 2) n).map (algebraMap ℚ (PadicAlgCl 3))
    with hfK
  -- the coordinate `z = 1 - t`
  have hcomp := jacobiShifted_comp_one_sub_eq ((l : ℚ) / 3) ((μ : ℚ) / 2) n hden
  set κ₁ : ℚ := (ascPochhammer ℚ n).eval ((n : ℚ) + (l : ℚ) / 3 + (μ : ℚ) / 2 + 1) /
    n.factorial with hκ₁
  have hκ₁0 : κ₁ ≠ 0 := by
    rw [hκ₁]
    exact div_ne_zero hden (by exact_mod_cast n.factorial_ne_zero)
  set YK := (jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n).map (algebraMap ℚ (PadicAlgCl 3))
    with hYK
  have hYcomp : YK.comp (C (-1) * polyX + C 1) = C ((κ₁ : ℚ) : PadicAlgCl 3) * fK := by
    have := congrArg (Polynomial.map (algebraMap ℚ (PadicAlgCl 3))) hcomp
    rw [Polynomial.map_comp] at this
    convert this using 1
    · simp [hYK]
    · rw [Polynomial.map_mul, Polynomial.map_C, eq_ratCast]
  have hroots3 : YK.roots.map (fun x => (-1 : PadicAlgCl 3) * (x - 1)) = fK.roots := by
    have h1 := roots_comp_C_mul_X_add_C YK (-1 : PadicAlgCl 3) 1 isUnit_one.neg
    rw [hYcomp, roots_C_mul _ (by exact_mod_cast hκ₁0)] at h1
    rw [h1]
    refine Multiset.map_congr rfl fun x _ => ?_
    rw [Ring.inverse_eq_inv', inv_neg_one]
  have hHK : H.map (Int.castRingHom (PadicAlgCl 3)) = C ((c : ℚ) : PadicAlgCl 3) * YK := by
    rw [map_intCast_eq_map_map, hH, Polynomial.map_mul, Polynomial.map_C, eq_ratCast]
  have hS : ((A * B).map (Int.castRingHom (PadicAlgCl 3))).roots.map
      (fun t => (-1 : PadicAlgCl 3) * (t - ((1 : ℤ) : PadicAlgCl 3))) = fK.roots := by
    rw [← hAB, hHK, roots_C_mul _ (by exact_mod_cast hc), ← hroots3, Int.cast_one]
  have hlcA : ¬ ((3 : ℕ) : ℤ) ∣ A.leadingCoeff := by
    intro h
    apply hlc
    rw [hAB, leadingCoeff_mul]
    exact dvd_mul_of_dvd_left (by exact_mod_cast h) _
  have hlcB : ¬ ((3 : ℕ) : ℤ) ∣ B.leadingCoeff := by
    intro h
    apply hlc
    rw [hAB, leadingCoeff_mul]
    exact dvd_mul_of_dvd_right (by exact_mod_cast h) _
  have hS0 : ∀ z ∈ fK.roots, z ≠ 0 := fun z hz => (hball z hz).1
  -- the Taylor separation, with `P = y_n^{(β,α)}`
  have hden' : (ascPochhammer ℚ n).eval ((n : ℚ) + (l : ℚ) / 3 + (μ : ℚ) / 2 + 1) ≠ 0 := hden
  have hrel := jacobiShifted_eq_C_mul_monicEndpoint ((μ : ℚ) / 2) ((l : ℚ) / 3) n hden'
  set κ : ℚ := (-1) ^ n * (ascPochhammer ℚ n).eval ((n : ℚ) + (l : ℚ) / 3 + (μ : ℚ) / 2 + 1) /
    n.factorial with hκ
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hden)
      (by exact_mod_cast n.factorial_ne_zero)
  have hPK : (jacobiShifted ((μ : ℚ) / 2) ((l : ℚ) / 3) n).map (algebraMap ℚ (PadicAlgCl 3)) =
      C ((κ : ℚ) : PadicAlgCl 3) * fK := by
    rw [hrel, Polynomial.map_mul, Polynomial.map_C, eq_ratCast]
  have hfK0 : fK ≠ 0 := ((monicEndpoint_monic _ _ n hden).1.map _).ne_zero
  have hP0 :
      (jacobiShifted ((μ : ℚ) / 2) ((l : ℚ) / 3) n).map (algebraMap ℚ (PadicAlgCl 3)) ≠ 0 := by
    rw [hPK]
    exact mul_ne_zero (C_ne_zero.mpr (by exact_mod_cast hκ0)) hfK0
  have hroot : ∀ z ∈ fK.roots,
      ((jacobiShifted ((μ : ℚ) / 2) ((l : ℚ) / 3) n).map (algebraMap ℚ (PadicAlgCl 3))).eval z
        = 0 := by
    intro z hz
    rw [hPK, eval_mul, eval_C, (mem_roots'.mp hz).2, mul_zero]
  have hbb : (μ : ℚ) / 2 + (l : ℚ) / 3 = (l : ℚ) / 3 + (μ : ℚ) / 2 := add_comm _ _
  have hsep : ∀ w ∈ fK.roots, ∀ z ∈ fK.roots, w ≠ z → padicVal 3 w = padicVal 3 z →
      padicVal 3 (w - z) ≤ padicVal 3 z + 1 / ((3 : ℕ) : ℝ) +
        max (3 / 2 - padicVal 3 z) 0 / ((3 : ℕ) : ℝ) := by
    intro w hw z hz hwz hv
    have h := padicVal_sub_le_of_eq (p := 3) (c0 := δ) (by omega) hP0
      (jacobiShifted_map_ode _ _ n) (fun m => (norm_three_jacobi_B_le hμ m).1)
      (fun m => (norm_three_jacobi_B_le hμ m).2) (norm_jacobi_c2_le padicValNat_three_six hbb)
      (norm_jacobi_Λ_le padicValNat_three_six hbb n) (hroot z hz) (hroot w hw) (hball z hz).1
      (hball z hz).2 hwz hv
    have e3 : ((3 : ℕ) : ℝ) / (((3 : ℕ) : ℝ) - 1) = 3 / 2 := by norm_num
    rwa [hv, min_self, e3] at h
  -- the total deficit
  have hdef := monicEndpoint_deficit_le_of_hull (p := 3) hNP hden (ρ := 3 / 2) (θ := 1 / 2)
    (by norm_num) (digitPhi n δ) (fun j hj => by
      obtain ⟨h1, h2⟩ := two_mul_padicValRat_kanekoZagierCoeff hl δ hδ hμ n j hj
      refine ⟨h1, ?_⟩
      have := congrArg (Int.cast : ℤ → ℝ) h2
      push_cast at this ⊢
      linarith)
    (digitPhi_self n δ) (D := (digitSum3 (2 * n + δ) : ℝ)) (fun j hj => by
      have hΦ : -(digitSum3 (2 * n + δ) : ℤ) ≤ digitPhi n δ j := by
        rw [digitPhi_eq]
        have := Nat.cast_nonneg (α := ℤ) (digitSum3 (2 * j + δ))
        have := Nat.cast_nonneg (α := ℤ) (digitSum3 (n - j))
        linarith
      have hr := (Int.cast_le (R := ℝ)).mpr hΦ
      simpa using hr)
  rw [show (1 / 2 : ℝ) * (digitSum3 (2 * n + δ) : ℝ) = (digitSum3 (2 * n + δ) : ℝ) / 2 by ring]
    at hdef
  have key := padicValInt_resultant_le_of_roots (p := 3) hlcA hlcB (a := 1)
    (ε := (-1 : PadicAlgCl 3)) (by rw [norm_neg, norm_one]) hS hS0 hsep hdef
  simp only [Nat.cast_ofNat] at key
  linarith

end Proposition46

end ArithmeticOfJacobiPolynomials
