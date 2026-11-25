/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.External
public import ArithmeticOfJacobiPolynomials.NumberTheory.LogIntegralBounds
public import ArithmeticOfJacobiPolynomials.PermGroup.PrimeCriterion
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Primes in progressions for fixed rational parameters (Section 5.4)

* `exists_bmor_parameter`, `eventually_abs_sub_le_of_large_modulus`: for every `Z > 0` the
  parameters of [BMOR, Proposition 6.19] can be chosen (`κ₁ = κ₂ = κ₃ = (13Z + 14)^4`), so that
  `|π(x; q, a) - Li(x)/φ(q)| ≤ x/(4 (log x)^{Z+1})` for all large `x`, uniformly in the reduced
  classes, when `q ≥ 10^5`.
* **Lemma 5.13**, `exists_prime_modEq_Ioc`: for fixed `q ≥ 2` and
  `A > 0`, every interval `(x, x + x/(log x)^A]` with `x` large contains a prime in each reduced
  class modulo `q`, with a threshold uniform in the class. As in the source, the modulus is
  raised to `Q = q^17 ≥ 10^5` and [BMOR, Proposition 6.19] is applied with `Z = A + 1`.
* `eventually_abs_primeCountingAP_sub_le`: the prime number theorem in progressions with a fixed
  modulus, `|π(x; q, a) - Li(x)/φ(q)| ≤ x/(log x)^2` for large `x` uniformly in the reduced
  classes ([BMOR, Corollary 1.7] for `q ≤ 10^5`, [BMOR, Proposition 6.19] for `q > 10^5`), and
  the resulting two-sided bounds for prime counts in intervals (`exists_card_primesIoc_bounds`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Real Filter

namespace FixedRationalParameters

/-! ### Parameters for [BMOR, Proposition 6.19] -/

/-- `log (s^4) ≤ 4 s` for `s > 0`. -/
theorem log_pow_four_le {s : ℝ} (hs : 0 < s) : Real.log (s ^ 4) ≤ 4 * s := by
  rw [Real.log_pow]
  have := Real.log_le_sub_one_of_pos hs
  push_cast
  linarith

/-- For every `Z > 0`, `κ = (13Z + 14)^4` is admissible for all three parameters of
[BMOR, Proposition 6.19], i.e. satisfies (6.23). -/
theorem exists_bmor_parameter {Z : ℝ} (hZ : 0 < Z) :
    ∃ κ : ℝ, 0.0132 ≤ κ ∧ 1 < κ ∧ Z ≤ 460.516 * κ / (Real.log κ + 13.087) ∧
      Z ≤ (Real.sqrt (κ / 9.645908801) - 0.85317) / Real.log κ - 1 / 2 ∧
      Z ≤ (κ - 6.44) / (2 * Real.log κ) := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = 13 * Z + 14 := ⟨_, rfl⟩
  have hs14 : 14 ≤ s := by linarith
  have hs0 : 0 < s := by linarith
  have hs2 : 14 * s ≤ s ^ 2 := by nlinarith
  have hs4 : s ^ 4 = s ^ 2 * s ^ 2 := by ring
  have h196 : 196 ≤ s ^ 2 := by nlinarith
  have hs4' : 196 * s ^ 2 ≤ s ^ 4 := by
    rw [hs4]; nlinarith [mul_le_mul_of_nonneg_left h196 (sq_nonneg s)]
  have hκ1 : 1 < s ^ 4 := by nlinarith
  have hlog := log_pow_four_le hs0
  have hlog0 : 0 < Real.log (s ^ 4) := Real.log_pos hκ1
  have hZs : 0 ≤ Z * s := mul_nonneg hZ.le hs0.le
  have hss : (13 * Z + 8) * s ≤ s * s := mul_le_mul_of_nonneg_right (by linarith) hs0.le
  refine ⟨s ^ 4, by linarith, hκ1, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by linarith)]
    have h1 : Z * (Real.log (s ^ 4) + 13.087) ≤ Z * (5 * s) :=
      mul_le_mul_of_nonneg_left (by linarith) hZ.le
    have h2 : Z * (5 * s) ≤ s * (5 * s) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith [sq_nonneg s]
  · have hsq : 0.3125 * s ^ 2 ≤ Real.sqrt (s ^ 4 / 9.645908801) := by
      have h1 : (0.3125 * s ^ 2) ^ 2 ≤ s ^ 4 / 9.645908801 := by
        rw [le_div_iff₀ (by norm_num)]
        nlinarith [sq_nonneg (s ^ 2)]
      calc 0.3125 * s ^ 2 = Real.sqrt ((0.3125 * s ^ 2) ^ 2) :=
            (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt (s ^ 4 / 9.645908801) := Real.sqrt_le_sqrt h1
    have hmain : (Z + 1 / 2) * Real.log (s ^ 4) ≤
        Real.sqrt (s ^ 4 / 9.645908801) - 0.85317 := by
      have h1 : (Z + 1 / 2) * Real.log (s ^ 4) ≤ (Z + 1 / 2) * (4 * s) :=
        mul_le_mul_of_nonneg_left hlog (by linarith)
      nlinarith
    have h3 : Z + 1 / 2 ≤ (Real.sqrt (s ^ 4 / 9.645908801) - 0.85317) / Real.log (s ^ 4) := by
      rw [le_div_iff₀ hlog0]; exact hmain
    linarith
  · rw [le_div_iff₀ (by linarith)]
    have h1 : Z * (2 * Real.log (s ^ 4)) ≤ Z * (8 * s) :=
      mul_le_mul_of_nonneg_left (by linarith) hZ.le
    nlinarith [sq_nonneg s]

/-- `c (log x)^r ≤ x` for all large `x`. -/
theorem eventually_mul_log_rpow_le (r c : ℝ) : ∀ᶠ x : ℝ in atTop, c * Real.log x ^ r ≤ x := by
  have h := (isLittleO_log_rpow_rpow_atTop r one_pos).bound
    (c := 1 / (|c| + 1)) (by positivity)
  filter_upwards [h, eventually_ge_atTop 1] with x hx hx1
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hpow : 0 ≤ Real.log x ^ r := Real.rpow_nonneg hlog r
  rw [Real.rpow_one, Real.norm_of_nonneg hpow, Real.norm_of_nonneg (by linarith)] at hx
  have hc : c * Real.log x ^ r ≤ |c| * Real.log x ^ r :=
    mul_le_mul_of_nonneg_right (le_abs_self c) hpow
  have h2 : |c| * Real.log x ^ r ≤ |c| * (1 / (|c| + 1) * x) :=
    mul_le_mul_of_nonneg_left hx (abs_nonneg c)
  have h3 : |c| * (1 / (|c| + 1) * x) ≤ x := by
    rw [← mul_assoc, mul_one_div]
    have hk : |c| / (|c| + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) (by linarith : (0 : ℝ) ≤ x)]
  linarith

/-- [BMOR, Proposition 6.19] with admissible parameters: for `q ≥ 10^5` and `Z > 0`,
`|π(x; q, a) - Li(x)/φ(q)| ≤ x/(4 (log x)^{Z+1})` for all large `x`, uniformly in the reduced
classes `a`. -/
theorem eventually_abs_sub_le_of_large_modulus (h619 : BMORLargeModulusPrimeCounting) {q : ℕ}
    (hq : 10 ^ 5 ≤ q) {Z : ℝ} (hZ : 0 < Z) :
    ∀ᶠ x : ℝ in atTop, ∀ a : ℤ, Int.gcd a q = 1 →
      |(primeCountingAP x q a : ℝ) - logIntegral x / q.totient| ≤
        x / (4 * Real.log x ^ (Z + 1)) := by
  obtain ⟨κ, h1, h2, h3, h4, h5⟩ := exists_bmor_parameter hZ
  filter_upwards [eventually_ge_atTop
      (Real.exp (max (max (κ * Real.sqrt q * Real.log q ^ 3) κ) (max κ (Z + 28)))),
    eventually_gt_atTop 1,
    eventually_mul_log_rpow_le (Z + 1)
      (2000 * Real.exp (max (max (κ * Real.sqrt q * Real.log q ^ 3) κ) (max κ (Z + 28))))]
    with x hx hx1 hx2 a ha
  have hpos : 0 < Real.log x ^ (Z + 1) := Real.rpow_pos_of_pos (Real.log_pos hx1) _
  exact h619 q a Z κ κ κ hq ha hZ h1 h2 h2 h3 h4 h5 x hx (by rw [le_div_iff₀ hpos]; exact hx2)

/-! ### Lemma 5.13 -/

/-- The numerical core of Lemma 5.13: with `x = u P ℓ`, `y = x + x/P`, `ℓ > 2φ`, `P ≥ 1`,
`ℓ_y ≤ 2ℓ`, the bounds `|π(x) - Li(x)/φ| ≤ x/(4Pℓ²)`, `|π(y) - Li(y)/φ| ≤ y/(4R_y)` with
`R_y ≥ Pℓ²`, and `Li(y) - Li(x) ≥ (y - x)/ℓ_y` force `π(x) < π(y)`. -/
theorem gap_numeric {x u y ℓ ℓy P φ Rx Ry Lx Ly πx πy : ℝ} (hu0 : 0 < u)
    (hxu : x = u * (P * ℓ)) (hφ : 0 < φ) (hℓ : 2 * φ < ℓ) (hP : 1 ≤ P) (hy : y = x + x / P)
    (hℓy0 : 0 < ℓy) (hℓy2 : ℓy ≤ 2 * ℓ) (hRx : Rx = P * ℓ * ℓ) (hRy : P * ℓ * ℓ ≤ Ry)
    (hLi : (y - x) / ℓy ≤ Ly - Lx) (h1 : |πx - Lx / φ| ≤ x / (4 * Rx))
    (h2 : |πy - Ly / φ| ≤ y / (4 * Ry)) : πx < πy := by
  subst hxu hy hRx
  have hℓ0 : 0 < ℓ := by linarith
  have hP0 : 0 < P := by linarith
  have hRy0 : 0 < Ry := lt_of_lt_of_le (by positivity) hRy
  have hxP : u * (P * ℓ) / P = u * ℓ := by field_simp
  have ha : u / 2 ≤ Ly - Lx := by
    refine le_trans ?_ hLi
    rw [add_sub_cancel_left, hxP, le_div_iff₀ hℓy0]
    nlinarith [mul_le_mul_of_nonneg_left hℓy2 hu0.le]
  have hb : u * (P * ℓ) / (4 * (P * ℓ * ℓ)) = u / (4 * ℓ) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  have hc : (u * (P * ℓ) + u * (P * ℓ) / P) / (4 * Ry) ≤ u / (2 * ℓ) := by
    rw [hxP, div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : u * (P * ℓ * ℓ) ≤ u * Ry := mul_le_mul_of_nonneg_left hRy hu0.le
    nlinarith [mul_nonneg (mul_nonneg hu0.le (sq_nonneg ℓ)) (sub_nonneg.mpr hP)]
  have hd : u / (2 * φ) ≤ (Ly - Lx) / φ := by
    rw [div_le_div_iff₀ (by positivity) hφ]
    nlinarith [mul_le_mul_of_nonneg_right ha (by linarith : (0 : ℝ) ≤ 2 * φ)]
  rw [hb] at h1
  have e1 := (abs_le.mp h1).2
  have e2 := (abs_le.mp h2).1
  have hfin : u / (4 * ℓ) + u / (2 * ℓ) < u / (2 * φ) := by
    rw [div_add_div _ _ (by positivity) (by positivity),
      div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos (mul_pos hu0 hℓ0) (by linarith : (0 : ℝ) < 2 * ℓ - 3 * φ)]
  have e3 : (Ly - Lx) / φ = Ly / φ - Lx / φ := sub_div _ _ _
  linarith

/-- **Lemma 5.13**. Fix an integer `q ≥ 2` and a real `A > 0`. For
every reduced class `a` modulo `q` and all sufficiently large `x`, the interval
`(x, x + x/(log x)^A]` contains a prime `≡ a (mod q)`; the threshold is uniform in `a`.

Conditional on [BMOR, Proposition 6.19], taken as the hypothesis `h619`. -/
theorem exists_prime_modEq_Ioc (h619 : BMORLargeModulusPrimeCounting) {q : ℕ} (hq : 2 ≤ q)
    {A : ℝ} (hA : 0 < A) :
    ∃ x₀ : ℝ, ∀ a : ℤ, Int.gcd a q = 1 → ∀ x : ℝ, x₀ ≤ x →
      ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + x / Real.log x ^ A ∧
        (p : ℤ) ≡ a [ZMOD q] := by
  have hQ : 10 ^ 5 ≤ q ^ 17 := le_trans (by norm_num) (Nat.pow_le_pow_left hq 17)
  have hev := eventually_abs_sub_le_of_large_modulus h619 hQ (Z := A + 1) (by linarith)
  have htend : Tendsto (fun x : ℝ => x + x / Real.log x ^ A) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ tendsto_id
    filter_upwards [eventually_ge_atTop 1] with x hx
    have : 0 ≤ x / Real.log x ^ A :=
      div_nonneg (by linarith) (Real.rpow_nonneg (Real.log_nonneg hx) A)
    simp only [id]
    linarith
  have hev2 : ∀ᶠ x : ℝ in atTop, ∀ a : ℤ, Int.gcd a ((q ^ 17 : ℕ) : ℤ) = 1 →
      |(primeCountingAP (x + x / Real.log x ^ A) (q ^ 17) a : ℝ) -
          logIntegral (x + x / Real.log x ^ A) / (q ^ 17).totient| ≤
        (x + x / Real.log x ^ A) /
          (4 * Real.log (x + x / Real.log x ^ A) ^ (A + 1 + 1)) :=
    htend.eventually hev
  have hφ : (0 : ℝ) < (q ^ 17).totient := by
    exact_mod_cast Nat.totient_pos.mpr (by positivity)
  have hlog := Real.tendsto_log_atTop.eventually_gt_atTop (2 * ((q ^ 17).totient : ℝ) + 1)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (hev.and (hev2.and (hlog.and (eventually_ge_atTop 3))))
  refine ⟨x₀, fun a ha x hx => ?_⟩
  obtain ⟨e1, e2, hℓ, hx3⟩ := hx₀ x hx
  have haQ : Int.gcd a ((q ^ 17 : ℕ) : ℤ) = 1 := by
    rw [← Int.isCoprime_iff_gcd_eq_one] at ha ⊢
    push_cast
    exact ha.pow_right
  have b1 := e1 a haQ
  have b2 := e2 a haQ
  have hx0 : 0 < x := by linarith
  have hℓ1 : 1 ≤ Real.log x := by linarith
  have hℓ0 : 0 < Real.log x := by linarith
  have hP : 1 ≤ Real.log x ^ A := Real.one_le_rpow hℓ1 hA.le
  have hP0 : 0 < Real.log x ^ A := by linarith
  have hH0 : 0 ≤ x / Real.log x ^ A := div_nonneg hx0.le hP0.le
  have hHx : x / Real.log x ^ A ≤ x := div_le_self hx0.le hP
  have hxy : x ≤ x + x / Real.log x ^ A := by linarith
  have hy2 : x + x / Real.log x ^ A ≤ 2 * x := by linarith
  have hℓy : Real.log x ≤ Real.log (x + x / Real.log x ^ A) := Real.log_le_log hx0 hxy
  have hℓy2 : Real.log (x + x / Real.log x ^ A) ≤ 2 * Real.log x := by
    have h1 := Real.log_le_log (by linarith) hy2
    rw [Real.log_mul (by norm_num) hx0.ne'] at h1
    have := Real.log_two_lt_d9
    linarith
  have hRx : Real.log x ^ (A + 1 + 1) = Real.log x ^ A * Real.log x * Real.log x := by
    rw [Real.rpow_add_one hℓ0.ne', Real.rpow_add_one hℓ0.ne']
  have hRy : Real.log x ^ A * Real.log x * Real.log x ≤
      Real.log (x + x / Real.log x ^ A) ^ (A + 1 + 1) := by
    rw [← hRx]
    exact Real.rpow_le_rpow hℓ0.le hℓy (by linarith)
  have hLi := logIntegral_sub_ge (a := x) (b := x + x / Real.log x ^ A) (by linarith) hxy
  have hlt := gap_numeric (u := x / (Real.log x ^ A * Real.log x)) (by positivity)
    (div_mul_cancel₀ x (by positivity)).symm hφ (by linarith) hP rfl (by linarith) hℓy2 hRx hRy
    hLi b1 b2
  have hlt' : primeCountingAP x (q ^ 17) a <
      primeCountingAP (x + x / Real.log x ^ A) (q ^ 17) a := by exact_mod_cast hlt
  rw [primeCountingAP_eq, primeCountingAP_eq] at hlt'
  obtain ⟨p, hp1, hp2⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt'
  rw [Finset.mem_filter, Finset.mem_range] at hp1 hp2
  obtain ⟨hpy, hpp, hpa⟩ := hp1
  have hpx : ⌊x⌋₊ + 1 ≤ p := by
    by_contra h
    exact hp2 ⟨by omega, hpp, hpa⟩
  refine ⟨p, hpp, ?_, ?_, ?_⟩
  · have h1 := Nat.lt_floor_add_one x
    have h' : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast hpx
    push_cast at h'
    linarith
  · have h' : p ≤ ⌊x + x / Real.log x ^ A⌋₊ := by omega
    have h'' : ((p : ℕ) : ℝ) ≤ ⌊x + x / Real.log x ^ A⌋₊ := by exact_mod_cast h'
    exact h''.trans (Nat.floor_le (by linarith))
  · exact Int.ModEq.of_dvd ⟨(q : ℤ) ^ 16, by push_cast; ring⟩ hpa

/-! ### The prime number theorem in progressions with a fixed modulus -/

/-- **Prime number theorem in progressions, fixed modulus.** For fixed `q ≥ 1`,
`|π(x; q, a) - Li(x)/φ(q)| ≤ x/(log x)^2` for all large `x`, uniformly in the reduced classes
`a`. From [BMOR, Corollary 1.7] when `q ≤ 10^5` and [BMOR, Proposition 6.19] (with `Z = 1`)
when `q > 10^5`. -/
theorem eventually_abs_primeCountingAP_sub_le (hBMOR : BMORPrimeCountingBound)
    (h619 : BMORLargeModulusPrimeCounting) {q : ℕ} (hq : 1 ≤ q) :
    ∀ᶠ x : ℝ in atTop, ∀ a : ℤ, Int.gcd a q = 1 →
      |(primeCountingAP x q a : ℝ) - logIntegral x / q.totient| ≤ x / Real.log x ^ 2 := by
  rcases le_or_gt q (10 ^ 5) with hq5 | hq5
  · filter_upwards [eventually_ge_atTop (10 ^ 6 : ℝ)] with x hx a ha
    have h := hBMOR q a hq hq5 ha x hx
    have hpos : 0 ≤ x / Real.log x ^ 2 := div_nonneg (by linarith) (sq_nonneg _)
    have h2 : 0.027 * x / Real.log x ^ 2 ≤ x / Real.log x ^ 2 := by
      rw [mul_div_assoc]; linarith
    linarith
  · filter_upwards [eventually_abs_sub_le_of_large_modulus h619 hq5.le (Z := 1) one_pos,
      eventually_gt_atTop 1] with x hx hx1 a ha
    have h := hx a ha
    rw [show (1 : ℝ) + 1 = 2 by norm_num, Real.rpow_two] at h
    have hL : 0 < Real.log x ^ 2 := by have := Real.log_pos hx1; positivity
    have h2 : x / (4 * Real.log x ^ 2) ≤ x / Real.log x ^ 2 :=
      div_le_div_of_nonneg_left (by linarith) hL (by linarith)
    linarith

/-- Two-sided bounds for the number of primes of a reduced class modulo a fixed `q` in
`(lo, hi]`, for `lo` large: the main term `(hi - lo)/(φ(q) log)` up to `2 hi/(log lo)^2`. -/
theorem exists_card_primesIoc_bounds (hBMOR : BMORPrimeCountingBound)
    (h619 : BMORLargeModulusPrimeCounting) {q : ℕ} (hq : 1 ≤ q) :
    ∃ N : ℕ, ∀ a : ℤ, Int.gcd a q = 1 → ∀ lo hi : ℕ, N ≤ lo → lo ≤ hi →
      ((hi : ℝ) - lo) / (q.totient * Real.log hi) - 2 * hi / Real.log lo ^ 2 ≤
          (primesIoc lo hi q a).card ∧
        ((primesIoc lo hi q a).card : ℝ) ≤
          ((hi : ℝ) - lo) / (q.totient * Real.log lo) + 2 * hi / Real.log lo ^ 2 := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    ((eventually_abs_primeCountingAP_sub_le hBMOR h619 hq).and (eventually_ge_atTop (2 : ℝ)))
  refine ⟨⌈x₀⌉₊ + 2, fun a ha lo hi hlo h => ?_⟩
  have hlo' : x₀ ≤ lo :=
    (Nat.le_ceil x₀).trans (by exact_mod_cast (by omega : ⌈x₀⌉₊ ≤ lo))
  have hhilo : (lo : ℝ) ≤ hi := by exact_mod_cast h
  have hhi' : x₀ ≤ hi := hlo'.trans hhilo
  obtain ⟨e1, hlo2⟩ := hx₀ lo hlo'
  obtain ⟨e2, -⟩ := hx₀ hi hhi'
  have b1 := e1 a ha
  have b2 := e2 a ha
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hLlo : 0 < Real.log lo := Real.log_pos (by linarith)
  have hLle : Real.log lo ≤ Real.log hi := Real.log_le_log (by linarith) hhilo
  have hLhi : 0 < Real.log hi := by linarith
  have hE1 : (lo : ℝ) / Real.log lo ^ 2 ≤ hi / Real.log lo ^ 2 :=
    div_le_div_of_nonneg_right hhilo (by positivity)
  have hE2 : (hi : ℝ) / Real.log hi ^ 2 ≤ hi / Real.log lo ^ 2 :=
    div_le_div_of_nonneg_left (by linarith) (by positivity) (pow_le_pow_left₀ hLlo.le hLle 2)
  have hLi1 := logIntegral_sub_ge (a := lo) (b := hi) hlo2 hhilo
  have hLi2 := logIntegral_sub_le (a := lo) (b := hi) hlo2 hhilo
  rw [card_primesIoc_eq_sub h]
  have e3 : ((hi : ℝ) - lo) / (q.totient * Real.log hi) =
      ((hi - lo) / Real.log hi) / q.totient := by
    field_simp
  have e4 : ((hi : ℝ) - lo) / (q.totient * Real.log lo) =
      ((hi - lo) / Real.log lo) / q.totient := by
    field_simp
  have f1 : ((hi : ℝ) - lo) / Real.log hi / q.totient ≤
      logIntegral hi / q.totient - logIntegral lo / q.totient := by
    rw [← sub_div]; exact div_le_div_of_nonneg_right hLi1 hφ.le
  have f2 : logIntegral hi / q.totient - logIntegral lo / q.totient ≤
      ((hi : ℝ) - lo) / Real.log lo / q.totient := by
    rw [← sub_div]; exact div_le_div_of_nonneg_right hLi2 hφ.le
  rw [abs_le] at b1 b2
  rw [e3, e4]
  have e5 : 2 * (hi : ℝ) / Real.log lo ^ 2 = hi / Real.log lo ^ 2 + hi / Real.log lo ^ 2 := by
    ring
  constructor <;> linarith [b1.1, b1.2, b2.1, b2.2]

/-! ### Eventual bounds for `log n` -/

/-- `log n ≤ c n` for all large `n`. -/
theorem eventually_log_natCast_le (c : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, Real.log n ≤ c * n := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    ((Real.isLittleO_log_id_atTop.bound hc).and (eventually_ge_atTop (1 : ℝ)))] with n hn
  obtain ⟨h1, h2⟩ := hn
  rw [Real.norm_of_nonneg (Real.log_nonneg h2), id_eq, Real.norm_of_nonneg (by linarith)] at h1
  exact h1

/-- `c ≤ log n` for all large `n`. -/
theorem eventually_le_log_natCast (c : ℝ) : ∀ᶠ n : ℕ in atTop, c ≤ Real.log n :=
  tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually_ge_atTop c)

/-! ### Cycle lengths `d_p = 2n + 1 - (p - r)/D` -/

/-- For `Dn + B < p`, `2(p + B) ≤ 3Dn`, `p ≡ r (mod D)` and `|r| + 4D + 10 < B`, the cycle length
`d_p = 2n + 1 - (p - r)/D` satisfies `n/2 < d_p ≤ n - 4` ((5.21), §5.5). -/
theorem cycleLength_bounds {D B n p : ℕ} {r : ℤ} (hD : 0 < D) (hB : |r| + 4 * D + 10 < B)
    (h1 : D * n + B < p) (h2 : 2 * (p + B) ≤ 3 * (D * n)) (h3 : (p : ℤ) ≡ r [ZMOD D]) :
    (n : ℤ) < 2 * (2 * n + 1 - ((p : ℤ) - r) / D) ∧ 2 * n + 1 - ((p : ℤ) - r) / D ≤ n - 4 := by
  obtain ⟨k, hk⟩ := Int.ModEq.dvd h3.symm
  have hD0 : (0 : ℤ) < D := by exact_mod_cast hD
  rw [hk, Int.mul_ediv_cancel_left _ hD0.ne']
  have h1' : (D : ℤ) * n + B < p := by exact_mod_cast h1
  have h2' : 2 * ((p : ℤ) + B) ≤ 3 * (D * n) := by exact_mod_cast h2
  have hr1 := le_abs_self r
  have hr2 := neg_abs_le r
  constructor
  · by_contra hc
    have hc' := not_lt.mp hc
    have h4 : 3 * (n : ℤ) + 2 ≤ 2 * k := by omega
    nlinarith [mul_le_mul_of_nonneg_left h4 hD0.le]
  · by_contra hc
    have hc' := not_le.mp hc
    have h4 : k ≤ (n : ℤ) + 4 := by omega
    nlinarith [mul_le_mul_of_nonneg_left h4 hD0.le]

/-- A block size `s` dividing `d_p` forces `p ≡ D(2n + 1) + r (mod Ds)` ((5.22),
§5.5). -/
theorem forced_class_of_dvd {D n s p : ℕ} {r : ℤ} (hD : 0 < D) (hpr : (p : ℤ) ≡ r [ZMOD D])
    (hs : (s : ℤ) ∣ 2 * n + 1 - ((p : ℤ) - r) / D) :
    (p : ℤ) ≡ D * (2 * n + 1) + r [ZMOD ((D * s : ℕ) : ℤ)] := by
  obtain ⟨k, hk⟩ := Int.ModEq.dvd hpr.symm
  have hD0 : (D : ℤ) ≠ 0 := by exact_mod_cast hD.ne'
  obtain ⟨t, ht⟩ := hs
  rw [hk, Int.mul_ediv_cancel_left _ hD0] at ht
  apply Int.modEq_iff_dvd.mpr
  exact ⟨t, by push_cast; linear_combination -hk + (D : ℤ) * ht⟩

/-- If `p ≡ r + D (mod 2D)` then `p ≡ r (mod D)` and `d_p` is even. -/
theorem modEq_and_even_of_modEq_add {D n p : ℕ} {r : ℤ} (hD : 0 < D)
    (h : (p : ℤ) ≡ r + D [ZMOD ((2 * D : ℕ) : ℤ)]) :
    (p : ℤ) ≡ r [ZMOD D] ∧ Even (2 * (n : ℤ) + 1 - ((p : ℤ) - r) / D) := by
  obtain ⟨j, hj⟩ := Int.ModEq.dvd h.symm
  push_cast at hj
  have hD0 : (D : ℤ) ≠ 0 := by exact_mod_cast hD.ne'
  have hpr : (p : ℤ) - r = D * (2 * j + 1) := by linarith
  refine ⟨Int.modEq_iff_dvd.mpr ⟨-(2 * j + 1), by linarith⟩, ?_⟩
  rw [hpr, Int.mul_ediv_cancel_left _ hD0]
  exact ⟨n - j, by ring⟩

/-- If `p ≡ r (mod 2D)` then `p ≡ r (mod D)` and `d_p` is odd. -/
theorem modEq_and_odd_of_modEq {D n p : ℕ} {r : ℤ} (hD : 0 < D)
    (h : (p : ℤ) ≡ r [ZMOD ((2 * D : ℕ) : ℤ)]) :
    (p : ℤ) ≡ r [ZMOD D] ∧ Odd (2 * (n : ℤ) + 1 - ((p : ℤ) - r) / D) := by
  obtain ⟨j, hj⟩ := Int.ModEq.dvd h.symm
  push_cast at hj
  have hD0 : (D : ℤ) ≠ 0 := by exact_mod_cast hD.ne'
  have hpr : (p : ℤ) - r = D * (2 * j) := by linarith
  refine ⟨Int.modEq_iff_dvd.mpr ⟨-(2 * j), by linarith⟩, ?_⟩
  rw [hpr, Int.mul_ediv_cancel_left _ hD0]
  exact ⟨n - j, by ring⟩

/-- For `7Dn < 5p` (the upper subinterval (5.24), §5.5) the cycle length
satisfies `100 d_p ≤ 61 n` once `n ≥ 100(|r| + 1)`. -/
theorem cycleLength_le_of_upper {D n p : ℕ} {r : ℤ} (hD : 0 < D) (h : 7 * (D * n) < 5 * p)
    (h3 : (p : ℤ) ≡ r [ZMOD D]) (hn : 100 * (|r| + 1) ≤ n) :
    100 * (2 * (n : ℤ) + 1 - ((p : ℤ) - r) / D) ≤ 61 * n := by
  obtain ⟨k, hk⟩ := Int.ModEq.dvd h3.symm
  have hD0 : (0 : ℤ) < D := by exact_mod_cast hD
  rw [hk, Int.mul_ediv_cancel_left _ hD0.ne']
  have h' : 7 * ((D : ℤ) * n) < 5 * p := by exact_mod_cast h
  have hr1 := le_abs_self r
  have hr0 := abs_nonneg r
  by_contra hc
  have hc' := not_le.mp hc
  have h4 : 100 * k ≤ 139 * (n : ℤ) + 99 := by omega
  have h5 := mul_le_mul_of_nonneg_left h4 hD0.le
  have h6 := mul_le_mul_of_nonneg_left hn hD0.le
  have h7 : |r| ≤ (D : ℤ) * |r| := le_mul_of_one_le_left hr0 (by omega)
  nlinarith

/-! ### Primitivity: no block size -/

/-- `φ(Ds) ≥ 2φ(D)` for even `D` and `s ≥ 2`. -/
theorem two_mul_totient_le_totient_mul {D s : ℕ} (hDe : Even D) (hs : 2 ≤ s) :
    2 * D.totient ≤ (D * s).totient := by
  rcases Nat.lt_or_ge s 3 with h | h
  · have hs2 : s = 2 := by omega
    subst hs2
    rw [mul_comm D 2, Nat.totient_mul_of_prime_of_dvd Nat.prime_two (even_iff_two_dvd.mp hDe)]
  · have h1 := Nat.mul_le_mul_left D.totient (two_le_totient h)
    have h2 := Nat.totient_super_multiplicative D s
    omega

/-- `φ(Ds) ≥ 4φ(D)` for `s ≥ 7`. -/
theorem four_mul_totient_le_totient_mul {D s : ℕ} (hs : 7 ≤ s) :
    4 * D.totient ≤ (D * s).totient := by
  have h1 := Nat.mul_le_mul_left D.totient (four_le_totient (m := s) (Or.inr hs))
  have h2 := Nat.totient_super_multiplicative D s
  omega

/-- Two reduced lifts (proof of Theorem 1.6, "Primitivity on the large orbit"): reduction of units
modulo `Ds` onto units modulo `D` is surjective with fibers of size `φ(Ds)/φ(D)`; if this
is `≥ 2` there is a unit `u` modulo `Ds` with `u ≡ 1 (mod D)` and `u ≢ 1 (mod Ds)`, so that
every reduced class `a` modulo `Ds` has the distinct reduced lift `a u` over the same class
modulo `D`. -/
theorem exists_nontrivial_unit_lift {D s : ℕ} (hD : 0 < D) (hs : 0 < s)
    (h : D.totient < (D * s).totient) :
    ∃ u : ℤ, Int.gcd u ((D * s : ℕ) : ℤ) = 1 ∧ u ≡ 1 [ZMOD D] ∧
      ¬ u ≡ 1 [ZMOD ((D * s : ℕ) : ℤ)] := by
  have : NeZero (D * s) := ⟨Nat.mul_ne_zero hD.ne' hs.ne'⟩
  have : NeZero D := ⟨hD.ne'⟩
  by_contra hcon
  push Not at hcon
  have hdvd : D ∣ D * s := Dvd.intro s rfl
  have hinj : Function.Injective (ZMod.unitsMap hdvd) := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have hv' : ZMod.castHom hdvd (ZMod D) (v : ZMod (D * s)) = 1 := by
      have := congrArg Units.val hv
      rwa [ZMod.unitsMap_def, Units.coe_map] at this
    have hcast : ((v : ZMod (D * s)).val : ZMod (D * s)) = v := ZMod.natCast_zmod_val _
    have hu : ((((v : ZMod (D * s)).val : ℕ) : ℤ)) ≡ 1 [ZMOD D] := by
      rw [← ZMod.intCast_eq_intCast_iff]
      have := hv'
      rw [← hcast] at this
      rw [map_natCast] at this
      simpa using this
    have hgcd : Int.gcd (((v : ZMod (D * s)).val : ℕ) : ℤ) ((D * s : ℕ) : ℤ) = 1 := by
      have h1 : IsUnit ((((v : ZMod (D * s)).val : ℕ) : ZMod (D * s))) := by
        rw [hcast]; exact v.isUnit
      rw [ZMod.isUnit_iff_coprime] at h1
      rw [Int.gcd_natCast_natCast]
      exact h1
    have hone := hcon _ hgcd hu
    apply Units.ext
    have := (ZMod.intCast_eq_intCast_iff _ _ _).mpr hone
    rw [← hcast]
    simpa using this
  have h1 := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    ZMod.card_units_eq_totient] at h1
  omega

/-- The error term `2 hi/(log lo)^2` is negligible: `φ L (2 hi/ℓ²) ≤ 0.03 X`. -/
theorem err_numeric {X L φ ℓlo hi : ℝ} (hX : 0 < X) (hφ1 : 1 ≤ φ) (hφL : 100 * φ ≤ L)
    (hℓlo : L ≤ ℓlo) (hhi : hi ≤ 1.5 * X) : φ * L * (2 * hi / ℓlo ^ 2) ≤ 0.03 * X := by
  have hL0 : 0 < L := by linarith
  have hφ0 : 0 < φ := by linarith
  have hsq : L * L ≤ ℓlo ^ 2 := by rw [sq]; exact mul_le_mul hℓlo hℓlo hL0.le (by linarith)
  rw [← mul_div_assoc, div_le_iff₀ (pow_pos (by linarith) 2)]
  have h1 : φ * L * (2 * hi) ≤ φ * L * (3 * X) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h2 : X * L * (100 * φ) ≤ X * L * L := mul_le_mul_of_nonneg_left hφL (by positivity)
  have h3 : X * (L * L) ≤ X * ℓlo ^ 2 := mul_le_mul_of_nonneg_left hsq hX.le
  nlinarith

/-- The count `T` of primes `≡ r (mod D)` in `(Dn + B, 3Dn/2 - B]` satisfies
`φ(D) T log n ≥ 0.45 Dn`, from its lower bound (5.23) (§5.5). -/
theorem main_lower_numeric {X L T φ y ℓhi ℓlo hi : ℝ} (hX : 0 < X) (hφ1 : 1 ≤ φ)
    (hφL : 100 * φ ≤ L) (hy : 0.49 * X ≤ y) (hℓhi0 : 0 < ℓhi) (hℓhi : ℓhi ≤ 1.01 * L)
    (hℓlo : L ≤ ℓlo) (hhi : hi ≤ 1.5 * X) (hT : y / (φ * ℓhi) - 2 * hi / ℓlo ^ 2 ≤ T) :
    0.45 * X ≤ φ * L * T := by
  have hL0 : 0 < L := by linarith
  have hφ0 : 0 < φ := by linarith
  have h1 : 0.485 * X ≤ φ * L * (y / (φ * ℓhi)) := by
    rw [← mul_div_assoc, mul_assoc, mul_div_mul_left _ _ hφ0.ne', le_div_iff₀ hℓhi0]
    nlinarith [mul_le_mul_of_nonneg_left hy hL0.le,
      mul_le_mul_of_nonneg_left hℓhi (by linarith : (0 : ℝ) ≤ 0.485 * X), mul_pos hX hL0]
  have h2 := err_numeric hX hφ1 hφL hℓlo hhi
  have h3 := mul_le_mul_of_nonneg_left hT (by positivity : (0 : ℝ) ≤ φ * L)
  rw [mul_sub] at h3
  linarith

/-- Upper bound for a single class modulo `Ds`, `7 ≤ s ≤ n^{1/4}`, by Brun–Titchmarsh and
`φ(Ds) ≥ 4φ(D)`. -/
theorem bt_upper_numeric {X L N φ φs y ℓ : ℝ} (hX : 0 < X) (hφ1 : 1 ≤ φ) (hL : 100 ≤ L)
    (hφs : 4 * φ ≤ φs) (hy : y ≤ X / 2) (hℓ : 0.75 * L - 1.3863 ≤ ℓ)
    (hN : N < 2 * y / (φs * ℓ)) : φ * L * N < 0.34 * X := by
  have hL0 : 0 < L := by linarith
  have hℓ' : 0.736 * L ≤ ℓ := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hφ0 : 0 < φ := by linarith
  have hφs0 : 0 < φs := by linarith
  have k1 : φ * L * (2 * y / (φs * ℓ)) ≤ 0.34 * X := by
    rw [← mul_div_assoc, div_le_iff₀ (mul_pos hφs0 hℓ0)]
    have h1 : 4 * φ * (0.736 * L) ≤ φs * ℓ := mul_le_mul hφs hℓ' (by positivity) hφs0.le
    have h2 : X * (4 * φ * (0.736 * L)) ≤ X * (φs * ℓ) := mul_le_mul_of_nonneg_left h1 hX.le
    have h3 : φ * L * (2 * y) ≤ φ * L * X :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith [mul_pos (mul_pos hX hφ0) hL0]
  have k2 : φ * L * N < φ * L * (2 * y / (φs * ℓ)) := mul_lt_mul_of_pos_left hN (by positivity)
  linarith

/-- Upper bound for a single class modulo `Ds` with `s > n^{1/4}`, by counting integers. -/
theorem large_upper_numeric {n D L N φ s ℓs : ℝ} (hn : 0 < n) (hD : 0 < D) (hφ0 : 0 ≤ φ)
    (hφD : φ ≤ D) (hL0 : 0 ≤ L) (hs : 0 < s) (hLs : L ≤ 4 * ℓs) (hℓs : 10 * ℓs ≤ s)
    (hL40 : 40 * L ≤ n) (hN : N ≤ n / (2 * s) + 2) : φ * L * N ≤ 0.25 * (D * n) := by
  have k1 : L * (n / (2 * s)) ≤ 0.2 * n := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right (by linarith : L ≤ 0.4 * s) hn.le]
  have k2 : φ * L * N ≤ φ * L * (n / (2 * s) + 2) :=
    mul_le_mul_of_nonneg_left hN (mul_nonneg hφ0 hL0)
  have k3 : φ * (L * (n / (2 * s))) ≤ φ * (0.2 * n) := mul_le_mul_of_nonneg_left k1 hφ0
  have k4 : φ * (0.2 * n) ≤ D * (0.2 * n) := mul_le_mul_of_nonneg_right hφD (by linarith)
  have k5 : φ * L ≤ D * L := mul_le_mul_of_nonneg_right hφD hL0
  have k6 : D * (40 * L) ≤ D * n := mul_le_mul_of_nonneg_left hL40 hD.le
  rw [mul_add] at k2
  nlinarith

/-- **Class avoidance for `2 ≤ s ≤ 6`** (proof of Theorem 1.6, "Primitivity on the large orbit"):
if the class `D(2n + 1) + r` forced by `s ∣ d_p` is reduced modulo `Ds`, then the reduced lift
`(D(2n + 1) + r) u` of `r` (with `u ≡ 1 (mod D)`, `u ≢ 1 (mod Ds)`, from the fiber of size
`φ(Ds)/φ(D) ≥ 2`) contains an eligible prime, which is not in the forced class. -/
theorem exists_prime_off_forced_class {D B n s lo hi : ℕ} {r : ℤ} (hD0 : 0 < D) (hDe : Even D)
    (hs2 : 2 ≤ s) (hs6 : s ≤ 6)
    (hgcd : Int.gcd (D * (2 * n + 1) + r) ((D * s : ℕ) : ℤ) = 1)
    (hmem : ∀ {q : ℕ} {a : ℤ} {p : ℕ}, p ∈ primesIoc lo hi q a ↔
      D * n + B < p ∧ 2 * (p + B) ≤ 3 * (D * n) ∧ p.Prime ∧ (p : ℤ) ≡ a [ZMOD q])
    (H : ∀ p : ℕ, p.Prime → D * n + B < p → 2 * (p + B) ≤ 3 * (D * n) →
      (p : ℤ) ≡ r [ZMOD D] → (s : ℤ) ∣ 2 * n + 1 - ((p : ℤ) - r) / D)
    (hpos : ∀ a : ℤ, Int.gcd a ((D * s : ℕ) : ℤ) = 1 → 0 < (primesIoc lo hi (D * s) a).card) :
    False := by
  have hφ1 : 1 ≤ D.totient := Nat.totient_pos.mpr hD0
  have hφ2 : 2 * D.totient ≤ (D * s).totient := two_mul_totient_le_totient_mul hDe hs2
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_nontrivial_unit_lift (D := D) (s := s) hD0 (by omega)
    (by omega)
  have hFu : Int.gcd ((D * (2 * n + 1) + r) * u) ((D * s : ℕ) : ℤ) = 1 := by
    rw [← Int.isCoprime_iff_gcd_eq_one] at hgcd hu1 ⊢
    exact hgcd.mul_left hu1
  have hFD : D * (2 * n + 1) + r ≡ r [ZMOD D] :=
    (Int.modEq_iff_dvd.mpr ⟨2 * (n : ℤ) + 1, by ring⟩).symm
  have haD : (D * (2 * n + 1) + r) * u ≡ r [ZMOD D] := by
    have := hu2.mul_left (D * (2 * n + 1) + r)
    rw [mul_one] at this
    exact this.trans hFD
  have hane : ¬ (D * (2 * n + 1) + r) * u ≡ D * (2 * n + 1) + r [ZMOD ((D * s : ℕ) : ℤ)] := by
    intro h
    apply hu3
    have hg' : IsCoprime ((D * s : ℕ) : ℤ) (D * (2 * n + 1) + r) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]; exact hgcd
    have h1 := Int.modEq_iff_dvd.mp h.symm
    have h2 : ((D * s : ℕ) : ℤ) ∣ (D * (2 * n + 1) + r) * (1 - u) := by
      have e : (D * (2 * n + 1) + r) * u - (D * (2 * n + 1) + r) =
          -((D * (2 * n + 1) + r) * (1 - u)) := by ring
      rw [e] at h1
      exact (dvd_neg).mp h1
    exact Int.modEq_iff_dvd.mpr (hg'.dvd_of_dvd_mul_left h2)
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (hpos _ hFu)
  obtain ⟨h1, h2, h3, h4⟩ := hmem.mp hp
  have hcast : ((D * s : ℕ) : ℤ) = (D : ℤ) * s := by push_cast; ring
  have h4' : (p : ℤ) ≡ r [ZMOD D] := by
    rw [hcast] at h4
    exact (h4.of_mul_right _).trans haD
  exact hane (h4.symm.trans (forced_class_of_dvd hD0 h4' (H p h3 h1 h2 h4')))

/-- **Primitivity, for one `n`** (proof of Theorem 1.6, "Primitivity on the large orbit"). Under
explicit largeness conditions on `n`, for every `2 ≤ s < n` some prime `p ≡ r (mod D)` with
`Dn + B < p`, `2(p + B) ≤ 3Dn` has `s ∤ d_p`. The hypotheses `hlow` and `hlows` are the
lower bound of the fixed-modulus prime number theorem for the moduli `D` and `Ds`, `s ≤ 6`. -/
theorem exists_prime_not_dvd_of_bounds (hBT : BrunTitchmarshInequality) {D B n s lo hi : ℕ}
    (hD2 : 2 ≤ D) (hDe : Even D) {r : ℤ} (hlo : lo = D * n + B) (hhi : hi = 3 * (D * n) / 2 - B)
    (hn : 100 * (2 * B + 2) ≤ n) (hn40 : 40 ^ 4 ≤ n)
    (hL : 600 * (D : ℝ) + 100 * Real.log (2 * D) + 100 ≤ Real.log n)
    (hL40 : 40 * Real.log n ≤ n)
    (hlow : ((hi : ℝ) - lo) / (D.totient * Real.log hi) - 2 * hi / Real.log lo ^ 2 ≤
      (primesIoc lo hi D r).card)
    (hlows : s ≤ 6 → ∀ a : ℤ, Int.gcd a ((D * s : ℕ) : ℤ) = 1 →
      ((hi : ℝ) - lo) / ((D * s).totient * Real.log hi) - 2 * hi / Real.log lo ^ 2 ≤
        (primesIoc lo hi (D * s) a).card)
    (hs2 : 2 ≤ s) (hsn : s < n) :
    ∃ p : ℕ, p.Prime ∧ D * n + B < p ∧ 2 * (p + B) ≤ 3 * (D * n) ∧ (p : ℤ) ≡ r [ZMOD D] ∧
      ¬ (s : ℤ) ∣ 2 * n + 1 - ((p : ℤ) - r) / D := by
  by_contra hcon
  have H : ∀ p : ℕ, p.Prime → D * n + B < p → 2 * (p + B) ≤ 3 * (D * n) →
      (p : ℤ) ≡ r [ZMOD D] → (s : ℤ) ∣ 2 * n + 1 - ((p : ℤ) - r) / D := by
    intro p hp h1 h2 h3
    by_contra hnd
    exact hcon ⟨p, hp, h1, h2, h3, hnd⟩
  have hD0 : 0 < D := by omega
  have h2n : 2 * n ≤ D * n := Nat.mul_le_mul_right n hD2
  have hlohi : lo ≤ hi := by omega
  have hmem : ∀ {q : ℕ} {a : ℤ} {p : ℕ}, p ∈ primesIoc lo hi q a ↔
      D * n + B < p ∧ 2 * (p + B) ≤ 3 * (D * n) ∧ p.Prime ∧ (p : ℤ) ≡ a [ZMOD q] := by
    intro q a p
    rw [mem_primesIoc]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨by omega, by omega, h3, h4⟩
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨by omega, by omega, h3, h4⟩
  have hforced : ∀ p ∈ primesIoc lo hi D r,
      (p : ℤ) ≡ D * (2 * n + 1) + r [ZMOD ((D * s : ℕ) : ℤ)] := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hmem.mp hp
    exact forced_class_of_dvd hD0 h4 (H p h3 h1 h2 h4)
  -- real-valued facts
  have hn40r : (40 : ℝ) ^ 4 ≤ n := by exact_mod_cast hn40
  have hn0 : (0 : ℝ) < n := by linarith
  have hDr : (2 : ℝ) ≤ D := by exact_mod_cast hD2
  have hDpos : (0 : ℝ) < D := by linarith
  have hX : (0 : ℝ) < D * n := by positivity
  have hDn2 : 2 * (n : ℝ) ≤ D * n := by exact_mod_cast h2n
  have hBn : (100 : ℝ) * (2 * B + 2) ≤ n := by exact_mod_cast hn
  have hlo_r : (lo : ℝ) = D * n + B := by rw [hlo]; push_cast; ring
  have hhi1 : 2 * hi ≤ 3 * (D * n) := by omega
  have hhi2 : 3 * (D * n) ≤ 2 * hi + 2 * B + 1 := by omega
  have hhi1r : 2 * (hi : ℝ) ≤ 3 * (D * n) := by exact_mod_cast hhi1
  have hhi2r : 3 * ((D : ℝ) * n) ≤ 2 * hi + 2 * B + 1 := by exact_mod_cast hhi2
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hy_le : (hi : ℝ) - lo ≤ D * n / 2 := by rw [hlo_r]; linarith
  have hy_ge : 0.49 * ((D : ℝ) * n) ≤ (hi : ℝ) - lo := by rw [hlo_r]; linarith
  have hlo_ge : (n : ℝ) ≤ lo := by rw [hlo_r]; linarith
  have hhi_ge : (lo : ℝ) ≤ hi := by exact_mod_cast hlohi
  have hhi_pos : (0 : ℝ) < hi := by linarith
  have hlog2D : 0 ≤ Real.log (2 * D) := Real.log_nonneg (by linarith)
  have hL100 : 100 ≤ Real.log n := by linarith
  have hℓlo : Real.log n ≤ Real.log lo := Real.log_le_log hn0 hlo_ge
  have hℓhi : Real.log hi ≤ 1.01 * Real.log n := by
    have h1 : (hi : ℝ) ≤ 2 * D * n := by linarith
    have h2 := Real.log_le_log hhi_pos h1
    rw [Real.log_mul (by positivity) hn0.ne'] at h2
    linarith
  have hℓhi0 : 0 < Real.log hi := Real.log_pos (by linarith)
  have hφ1' : 1 ≤ D.totient := Nat.totient_pos.mpr hD0
  have hφ1 : (1 : ℝ) ≤ D.totient := by exact_mod_cast hφ1'
  have hφD : (D.totient : ℝ) ≤ D := by exact_mod_cast Nat.totient_le D
  have hφL : 100 * (D.totient : ℝ) ≤ Real.log n := by linarith
  have hmain : 0.45 * ((D : ℝ) * n) ≤ D.totient * Real.log n * (primesIoc lo hi D r).card :=
    main_lower_numeric hX hφ1 hφL hy_ge hℓhi0 hℓhi hℓlo (by linarith) hlow
  have hSpos : 0 < (primesIoc lo hi D r).card := by
    by_contra h0
    have h0' : (primesIoc lo hi D r).card = 0 := by omega
    rw [h0', Nat.cast_zero, mul_zero] at hmain
    linarith
  obtain ⟨p₀, hp₀⟩ := Finset.card_pos.mp hSpos
  -- the forced class is reduced
  have hgcd : Int.gcd (D * (2 * n + 1) + r) ((D * s : ℕ) : ℤ) = 1 := by
    obtain ⟨h1, -, h3, -⟩ := hmem.mp hp₀
    have hf := hforced p₀ hp₀
    have hg1 : ((Int.gcd (D * (2 * n + 1) + r) ((D * s : ℕ) : ℤ) : ℕ) : ℤ) ∣
        D * (2 * n + 1) + r := Int.gcd_dvd_left _ _
    have hg2 : ((Int.gcd (D * (2 * n + 1) + r) ((D * s : ℕ) : ℤ) : ℕ) : ℤ) ∣
        ((D * s : ℕ) : ℤ) := Int.gcd_dvd_right _ _
    have hg3 : ((Int.gcd (D * (2 * n + 1) + r) ((D * s : ℕ) : ℤ) : ℕ) : ℤ) ∣ (p₀ : ℤ) := by
      have h5 := dvd_trans hg2 (Int.modEq_iff_dvd.mp hf)
      have h6 := dvd_sub hg1 h5
      rwa [sub_sub_cancel] at h6
    have hg4 := Int.natCast_dvd_natCast.mp hg3
    have hg5 := Int.natCast_dvd_natCast.mp hg2
    rcases h3.eq_one_or_self_of_dvd _ hg4 with h | h
    · exact h
    · exfalso
      have h7 := Nat.le_of_dvd (Nat.mul_pos hD0 (by omega)) hg5
      have h8 : D * s ≤ D * n := Nat.mul_le_mul_left D hsn.le
      omega
  have hsub : primesIoc lo hi D r ⊆ primesIoc lo hi (D * s) (D * (2 * n + 1) + r) := by
    intro p hp
    obtain ⟨h1, h2, h3, -⟩ := hmem.mp hp
    exact hmem.mpr ⟨h1, h2, h3, hforced p hp⟩
  have hle : ((primesIoc lo hi D r).card : ℝ) ≤
      (primesIoc lo hi (D * s) (D * (2 * n + 1) + r)).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hφLn : (0 : ℝ) ≤ D.totient * Real.log n := mul_nonneg (by linarith) (by linarith)
  have hle' := mul_le_mul_of_nonneg_left hle hφLn
  have hs2r : (2 : ℝ) ≤ s := by exact_mod_cast hs2
  have hs0 : (0 : ℝ) < s := by linarith only [hs2r]
  have hcount := card_le_of_forall_modEq (S := primesIoc lo hi D r) (q := D * s)
    (c := D * (2 * n + 1) + r) (Nat.mul_pos hD0 (by omega)) hlohi (fun p hp => by
      obtain ⟨h1, h2, -, -⟩ := hmem.mp hp
      exact ⟨by omega, by omega, hforced p hp⟩)
  clear hcon hsub hlow hhi1 hhi2
  rcases Nat.lt_or_ge s 7 with hs7 | hs7
  · -- `2 ≤ s ≤ 6`: a reduced lift of `r` other than the forced class contains a prime
    refine exists_prime_off_forced_class hD0 hDe hs2 (by omega) hgcd hmem H ?_
    intro a ha
    have hlows' := hlows (by omega) a ha
    have hφsL : 100 * ((D * s).totient : ℝ) ≤ Real.log n := by
      have h1 : (D * s).totient ≤ D * s := Nat.totient_le _
      have h2 : D * s ≤ 6 * D := by
        have := Nat.mul_le_mul_left D (show s ≤ 6 by omega)
        omega
      have h3 : ((D * s).totient : ℝ) ≤ 6 * D := by exact_mod_cast h1.trans h2
      linarith only [h3, hL, hlog2D]
    have hφs1 : (1 : ℝ) ≤ (D * s).totient := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos hD0 (by omega))
    have hmains := main_lower_numeric hX hφs1 hφsL hy_ge hℓhi0 hℓhi hℓlo
      (by linarith only [hhi1r]) hlows'
    by_contra h0
    have h0' : (primesIoc lo hi (D * s) a).card = 0 := by omega
    rw [h0', Nat.cast_zero, mul_zero] at hmains
    linarith only [hmains, hX]
  · have hφs : 4 * (D.totient : ℝ) ≤ (D * s).totient := by
      exact_mod_cast four_mul_totient_le_totient_mul hs7
    rcases le_or_gt (s ^ 4) n with hs4 | hs4
    · -- `7 ≤ s ≤ n^{1/4}`: Brun–Titchmarsh
      have h343 : 343 * s ≤ n := by
        have h1 : 7 ^ 3 ≤ s ^ 3 := Nat.pow_le_pow_left hs7 3
        calc 343 * s ≤ s ^ 3 * s := Nat.mul_le_mul_right s h1
          _ = s ^ 4 := by ring
          _ ≤ n := hs4
      have h343r : 343 * (s : ℝ) ≤ n := by exact_mod_cast h343
      have hqr : (((D * s : ℕ) : ℝ)) = D * s := by push_cast; ring
      have hyq : (((D * s : ℕ) : ℝ)) < (hi : ℝ) - lo := by
        rw [hqr]
        linarith only [mul_le_mul_of_nonneg_left h343r hDpos.le, hy_ge, hX]
      have hlo0 : (0 : ℝ) < lo := by linarith only [hlo_ge, hn0]
      have hB := hBT (D * s) (D * (2 * n + 1) + r) lo ((hi : ℝ) - lo) (Nat.mul_pos hD0 (by omega))
        hgcd hlo0 hyq
      rw [add_sub_cancel, ← card_primesIoc_eq_sub hlohi] at hB
      have hyq' : (n : ℝ) / (4 * s) ≤ ((hi : ℝ) - lo) / ((D * s : ℕ) : ℝ) := by
        rw [hqr, div_le_div_iff₀ (by positivity) (by positivity)]
        linarith only [mul_le_mul_of_nonneg_right hy_ge (by positivity : (0 : ℝ) ≤ 4 * s),
          mul_pos hX hs0]
      have hlogs : 4 * Real.log s ≤ Real.log n := by
        have e := Real.log_pow (s : ℝ) 4
        push_cast at e
        rw [← e]
        exact Real.log_le_log (by positivity) (by exact_mod_cast hs4)
      have hℓ : 0.75 * Real.log n - 1.3863 ≤
          Real.log (((hi : ℝ) - lo) / ((D * s : ℕ) : ℝ)) := by
        have h1 := Real.log_le_log (by positivity) hyq'
        rw [Real.log_div hn0.ne' (by positivity), Real.log_mul (by norm_num) hs0.ne'] at h1
        have h4 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
        have h5 := Real.log_two_lt_d9
        linarith only [h1, h4, h5, hlogs]
      have hbt := bt_upper_numeric hX hφ1 hL100 hφs hy_le hℓ (lt_of_le_of_lt hle hB)
      linarith only [hbt, hmain, hX]
    · -- `s > n^{1/4}`: counting integers in the forced class
      have hs40 : 40 ≤ s := by
        by_contra h
        have : s ^ 4 ≤ 39 ^ 4 := Nat.pow_le_pow_left (by omega) 4
        omega
      have hT : ((primesIoc lo hi D r).card : ℝ) ≤ (n : ℝ) / (2 * s) + 2 := by
        have hqr : (((D * s : ℕ) : ℝ)) = D * s := by push_cast; ring
        have h1 : ((hi : ℝ) - lo) / (((D * s : ℕ) : ℝ)) ≤ (n : ℝ) / (2 * s) := by
          rw [hqr, div_le_div_iff₀ (by positivity) (by positivity)]
          linarith only [mul_le_mul_of_nonneg_right hy_le (by positivity : (0 : ℝ) ≤ 2 * s)]
        linarith only [hcount, h1]
      have hLs : Real.log n ≤ 4 * Real.log s := by
        have e := Real.log_pow (s : ℝ) 4
        push_cast at e
        rw [← e]
        exact Real.log_le_log hn0 (by exact_mod_cast hs4.le)
      have hℓs : 10 * Real.log s ≤ s := by
        have h1 := Real.log_le_sub_one_of_pos (x := (s : ℝ) / 64) (by positivity)
        rw [Real.log_div hs0.ne' (by norm_num)] at h1
        have h64 : Real.log 64 = 6 * Real.log 2 := by
          rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; push_cast; ring
        have h5 := Real.log_two_lt_d9
        have hs40r : (40 : ℝ) ≤ s := by exact_mod_cast hs40
        linarith only [h1, h64, h5, hs40r]
      have hlarge := large_upper_numeric hn0 hDpos (by positivity) hφD (by linarith only [hL100])
        hs0 hLs hℓs hL40 hT
      linarith only [hlarge, hmain, hX]

/-- **Primitivity** (proof of Theorem 1.6). For fixed even `D ≥ 2`, `B` and `r` prime to `D`,
for all large `n` and every `2 ≤ s < n`, some prime `p ≡ r (mod D)` with `Dn + B < p` and
`2(p + B) ≤ 3Dn` ((5.20), §5.5) has `s ∤ d_p`.

Conditional on [BMOR, Corollary 1.7], [BMOR, Proposition 6.19] and Brun–Titchmarsh [MV,
Theorem 2], taken as the hypotheses `hBMOR`, `h619`, `hBT`. -/
theorem eventually_exists_prime_not_dvd (hBMOR : BMORPrimeCountingBound)
    (h619 : BMORLargeModulusPrimeCounting) (hBT : BrunTitchmarshInequality) {D B : ℕ}
    (hD2 : 2 ≤ D) (hDe : Even D) {r : ℤ} (hr : Int.gcd r D = 1) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℕ, 2 ≤ s → s < n → ∃ p : ℕ, p.Prime ∧ D * n + B < p ∧
      2 * (p + B) ≤ 3 * (D * n) ∧ (p : ℤ) ≡ r [ZMOD D] ∧
      ¬ (s : ℤ) ∣ 2 * n + 1 - ((p : ℤ) - r) / D := by
  obtain ⟨N₀, hN₀⟩ := exists_card_primesIoc_bounds hBMOR h619 (q := D) (by omega)
  have hsmall : ∀ s : ℕ, ∃ N : ℕ, 1 ≤ s → ∀ a : ℤ, Int.gcd a ((D * s : ℕ) : ℤ) = 1 →
      ∀ lo hi : ℕ, N ≤ lo → lo ≤ hi →
        ((hi : ℝ) - lo) / ((D * s).totient * Real.log hi) - 2 * hi / Real.log lo ^ 2 ≤
          (primesIoc lo hi (D * s) a).card := by
    intro s
    rcases Nat.eq_zero_or_pos s with hs | hs
    · exact ⟨0, fun h => absurd h (by omega)⟩
    · obtain ⟨N, hN⟩ := exists_card_primesIoc_bounds hBMOR h619 (q := D * s)
        (Nat.mul_pos (by omega) hs)
      exact ⟨N, fun _ a ha lo hi h1 h2 => (hN a ha lo hi h1 h2).1⟩
  choose Ns hNs using hsmall
  filter_upwards [eventually_ge_atTop
      (N₀ + Ns 2 + Ns 3 + Ns 4 + Ns 5 + Ns 6 + 100 * (2 * B + 2) + 40 ^ 4),
    eventually_le_log_natCast (600 * (D : ℝ) + 100 * Real.log (2 * D) + 100),
    eventually_log_natCast_le (1 / 40) (by norm_num)] with n hn hL hL40
  intro s hs2 hsn
  have h2n : 2 * n ≤ D * n := Nat.mul_le_mul_right n hD2
  have hlohi : D * n + B ≤ 3 * (D * n) / 2 - B := by omega
  refine exists_prime_not_dvd_of_bounds hBT hD2 hDe rfl rfl (by omega) (by omega) hL
    (by linarith) (hN₀ r hr _ _ (by omega) hlohi).1 ?_ hs2 hsn
  intro hs6 a ha
  exact hNs s (by omega) a ha _ _ (by interval_cases s <;> omega) hlohi

/-! ### Primes in the upper subinterval and near `Dn` -/

/-- The count of primes in the upper subinterval is positive: `φ L T ≥ 0.05 X` from the lower
bound `T ≥ y/(φ log hi) - 2 hi/(log lo)²` with `y ≥ 0.09 X`. -/
theorem upper_lower_numeric {X L T φ y ℓhi ℓlo hi : ℝ} (hX : 0 < X) (hφ1 : 1 ≤ φ)
    (hφL : 100 * φ ≤ L) (hy : 0.09 * X ≤ y) (hℓhi0 : 0 < ℓhi) (hℓhi : ℓhi ≤ 1.01 * L)
    (hℓlo : L ≤ ℓlo) (hhi : hi ≤ 1.5 * X) (hT : y / (φ * ℓhi) - 2 * hi / ℓlo ^ 2 ≤ T) :
    0.05 * X ≤ φ * L * T := by
  have hL0 : 0 < L := by linarith
  have hφ0 : 0 < φ := by linarith
  have h1 : 0.089 * X ≤ φ * L * (y / (φ * ℓhi)) := by
    rw [← mul_div_assoc, mul_assoc, mul_div_mul_left _ _ hφ0.ne', le_div_iff₀ hℓhi0]
    nlinarith [mul_le_mul_of_nonneg_left hy hL0.le,
      mul_le_mul_of_nonneg_left hℓhi (by linarith : (0 : ℝ) ≤ 0.089 * X), mul_pos hX hL0]
  have h2 := err_numeric hX hφ1 hφL hℓlo hhi
  have h3 := mul_le_mul_of_nonneg_left hT (by positivity : (0 : ℝ) ≤ φ * L)
  rw [mul_sub] at h3
  linarith

/-- For all large `n` there is a prime `p ≡ c (mod 2D)` with `7Dn/5 < p` and `2(p + B) ≤ 3Dn`
((5.24), §5.5): the prime number theorem in the fixed class modulo `2D` (lower bound for the
count of primes in `(7Dn/5, 3Dn/2 - B]`, of length `≈ Dn/10`). -/
theorem eventually_exists_prime_upper (hBMOR : BMORPrimeCountingBound)
    (h619 : BMORLargeModulusPrimeCounting) {D B : ℕ}
    (hD2 : 2 ≤ D) {c : ℤ} (hc : Int.gcd c ((2 * D : ℕ) : ℤ) = 1) :
    ∀ᶠ n : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ D * n + B < p ∧ 2 * (p + B) ≤ 3 * (D * n) ∧
      7 * (D * n) < 5 * p ∧ (p : ℤ) ≡ c [ZMOD ((2 * D : ℕ) : ℤ)] := by
  obtain ⟨N₀, hN₀⟩ := exists_card_primesIoc_bounds hBMOR h619 (q := 2 * D) (by omega)
  filter_upwards [eventually_ge_atTop (N₀ + 100 * (B + 1) + 100),
    eventually_le_log_natCast (200 * (D : ℝ) + 100 * Real.log (2 * D) + 100)] with n hn hL
  have h2n : 2 * n ≤ D * n := Nat.mul_le_mul_right n hD2
  obtain ⟨lo, hlo⟩ : ∃ lo, lo = 7 * (D * n) / 5 := ⟨_, rfl⟩
  obtain ⟨hi, hhi⟩ : ∃ hi, hi = 3 * (D * n) / 2 - B := ⟨_, rfl⟩
  have hlohi : lo ≤ hi := by omega
  have hlo_ge : N₀ ≤ lo := by omega
  have hcard := (hN₀ c hc lo hi hlo_ge hlohi).1
  have hDr : (2 : ℝ) ≤ D := by exact_mod_cast hD2
  have hn' : ((N₀ + 100 * (B + 1) + 100 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
  push_cast at hn'
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hN00 : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg N₀
  have hn0 : (0 : ℝ) < n := by linarith
  have hDn2 : 2 * (n : ℝ) ≤ D * n := by exact_mod_cast h2n
  have hX : (0 : ℝ) < D * n := by linarith
  have hlo1 : 5 * lo ≤ 7 * (D * n) := by omega
  have hlo2 : 7 * (D * n) < 5 * lo + 5 := by omega
  have hhi1 : 2 * (hi + B) ≤ 3 * (D * n) := by omega
  have hhi2 : 3 * (D * n) ≤ 2 * (hi + B) + 1 := by omega
  have hlo1r : 5 * (lo : ℝ) ≤ 7 * (D * n) := by exact_mod_cast hlo1
  have hlo2r : 7 * ((D : ℝ) * n) < 5 * lo + 5 := by exact_mod_cast hlo2
  have hhi1r : 2 * ((hi : ℝ) + B) ≤ 3 * (D * n) := by exact_mod_cast hhi1
  have hhi2r : 3 * ((D : ℝ) * n) ≤ 2 * (hi + B) + 1 := by exact_mod_cast hhi2
  have hlohir : (lo : ℝ) ≤ hi := by exact_mod_cast hlohi
  have hy : 0.09 * ((D : ℝ) * n) ≤ (hi : ℝ) - lo := by nlinarith
  have hlo_n : (n : ℝ) ≤ lo := by nlinarith
  have hhi_pos : (0 : ℝ) < hi := by linarith
  have hlog2D : 0 ≤ Real.log (2 * D) := Real.log_nonneg (by linarith)
  have hℓlo : Real.log n ≤ Real.log lo := Real.log_le_log hn0 hlo_n
  have hℓhi : Real.log hi ≤ 1.01 * Real.log n := by
    have h1 : (hi : ℝ) ≤ 2 * D * n := by linarith
    have h2 := Real.log_le_log hhi_pos h1
    rw [Real.log_mul (by positivity) hn0.ne'] at h2
    linarith
  have hℓhi0 : 0 < Real.log hi := Real.log_pos (by linarith)
  have hφ1 : (1 : ℝ) ≤ (2 * D).totient := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hφL : 100 * ((2 * D).totient : ℝ) ≤ Real.log n := by
    have h1 : ((2 * D).totient : ℝ) ≤ 2 * D := by exact_mod_cast Nat.totient_le _
    linarith
  have hmain := upper_lower_numeric hX hφ1 hφL hy hℓhi0 hℓhi hℓlo (by linarith) hcard
  have hpos : 0 < (primesIoc lo hi (2 * D) c).card := by
    by_contra h0
    have h0' : (primesIoc lo hi (2 * D) c).card = 0 := by omega
    rw [h0', Nat.cast_zero, mul_zero] at hmain
    linarith
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  obtain ⟨h1, h2, h3, h4⟩ := mem_primesIoc.mp hp
  refine ⟨p, h3, ?_, by omega, by omega, h4⟩
  have : B + 1 ≤ n := by omega
  have h5 : 100 * (B + 1) ≤ 100 * n := by omega
  omega

/-- For every `A > 0` there are `C` and `N` such that for `n ≥ N` some prime `p ≡ r (mod D)`
with `Dn + B < p`, `2(p + B) ≤ 3Dn` has `n - d_p ≤ C n/(log n)^A`, by Lemma 5.13 with
`x = Dn + B`. -/
theorem exists_prime_near (h619 : BMORLargeModulusPrimeCounting) {D B : ℕ} (hD2 : 2 ≤ D)
    {r : ℤ} (hr : Int.gcd r D = 1) (hB : |r| < B) {A : ℝ} (hA : 0 < A) :
    ∃ (C : ℝ) (N : ℕ), ∀ n ≥ N, ∃ p : ℕ, p.Prime ∧ D * n + B < p ∧
      2 * (p + B) ≤ 3 * (D * n) ∧ (p : ℤ) ≡ r [ZMOD D] ∧
      (n : ℝ) - ((2 * (n : ℤ) + 1 - ((p : ℤ) - r) / D : ℤ) : ℝ) ≤ C * n / Real.log n ^ A := by
  obtain ⟨x₀, hx₀⟩ := exists_prime_modEq_Ioc h619 hD2 hA
  have hpow : ∀ᶠ n : ℕ in atTop, 10 ≤ Real.log n ^ A :=
    tendsto_natCast_atTop_atTop.eventually
      (((tendsto_rpow_atTop hA).comp Real.tendsto_log_atTop).eventually_ge_atTop 10)
  have hpow2 : ∀ᶠ n : ℕ in atTop, 1 * Real.log n ^ A ≤ n :=
    tendsto_natCast_atTop_atTop.eventually (eventually_mul_log_rpow_le A 1)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hpow.and hpow2)
  refine ⟨3 * B + D, N₁ + ⌈x₀⌉₊ + 10 * B + 1, fun n hn => ?_⟩
  obtain ⟨hP10, hPn⟩ := hN₁ n (by omega)
  have hn' : ((N₁ + ⌈x₀⌉₊ + 10 * B + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
  push_cast at hn'
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hN0 : (0 : ℝ) ≤ N₁ := Nat.cast_nonneg N₁
  have hc0 : (0 : ℝ) ≤ ⌈x₀⌉₊ := Nat.cast_nonneg _
  have hn0 : (1 : ℝ) ≤ n := by linarith
  have hDr : (2 : ℝ) ≤ D := by exact_mod_cast hD2
  have hD0 : (0 : ℤ) < D := by exact_mod_cast (by omega : 0 < D)
  have hDn : 2 * (n : ℝ) ≤ D * n := by nlinarith
  have hxn : (n : ℝ) ≤ D * n + B := by linarith
  obtain ⟨p, hp, h1, h2, h3⟩ := hx₀ r hr (D * n + B) (by linarith [Nat.le_ceil x₀])
  have hlogx : Real.log n ≤ Real.log (D * n + B) := Real.log_le_log (by linarith) hxn
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn0
  have hP : Real.log n ^ A ≤ Real.log (D * n + B) ^ A := Real.rpow_le_rpow hlogn0 hlogx hA.le
  have hP0 : 0 < Real.log n ^ A := by linarith
  have hH : ((D : ℝ) * n + B) / Real.log (D * n + B) ^ A ≤ (D * n + B) / 10 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have hH2 : ((D : ℝ) * n + B) / Real.log (D * n + B) ^ A ≤ (D + B) * n / Real.log n ^ A := by
    rw [div_le_div_iff₀ (by linarith) hP0]
    have h4 : (D : ℝ) * n + B ≤ (D + B) * n := by
      nlinarith [mul_le_mul_of_nonneg_left hn0 hB0]
    exact mul_le_mul h4 hP hP0.le (by positivity)
  have hH0 : 0 ≤ ((D : ℝ) * n + B) / Real.log (D * n + B) ^ A := by
    apply div_nonneg (by positivity)
    exact Real.rpow_nonneg (le_trans hlogn0 hlogx) A
  have hrB : |(r : ℝ)| < B := by exact_mod_cast hB
  have hr1' : (r : ℝ) ≤ |(r : ℝ)| := le_abs_self _
  have hr2' : -|(r : ℝ)| ≤ r := neg_abs_le _
  refine ⟨p, hp, by exact_mod_cast h1, ?_, h3, ?_⟩
  · have : 2 * ((p : ℝ) + B) ≤ 3 * (D * n) := by nlinarith
    exact_mod_cast this
  · obtain ⟨k, hk⟩ := Int.ModEq.dvd h3.symm
    rw [hk, Int.mul_ediv_cancel_left _ hD0.ne']
    have hkr : (p : ℝ) - r = D * k := by exact_mod_cast hk
    push_cast
    have hk1 : (D : ℝ) * (k - n - 1) ≤ |(r : ℝ)| + B + (D * n + B) / Real.log (D * n + B) ^ A := by
      nlinarith
    have hk2 : (k : ℝ) - n - 1 ≤ |(r : ℝ)| + B + (D * n + B) / Real.log (D * n + B) ^ A := by
      by_cases hkn : (k : ℝ) - n - 1 ≤ 0
      · linarith [abs_nonneg (r : ℝ)]
      · have hkn' := not_le.mp hkn
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ D - 1) hkn'.le]
    have hone : (1 : ℝ) ≤ n / Real.log n ^ A := by rw [le_div_iff₀ hP0]; linarith
    have hfin : |(r : ℝ)| + B ≤ 2 * B * (n / Real.log n ^ A) := by
      nlinarith [mul_nonneg hB0 (sub_nonneg.mpr hone)]
    have e : (3 * (B : ℝ) + D) * n / Real.log n ^ A =
        2 * B * (n / Real.log n ^ A) + (D + B) * n / Real.log n ^ A := by
      ring
    linarith

end FixedRationalParameters

end ArithmeticOfJacobiPolynomials
