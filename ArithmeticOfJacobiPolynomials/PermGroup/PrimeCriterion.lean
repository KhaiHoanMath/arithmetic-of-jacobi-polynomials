/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.PermGroup.Blocks
public import ArithmeticOfJacobiPolynomials.NumberTheory.LogIntegralBounds
public import ArithmeticOfJacobiPolynomials.External

/-!
# An explicit prime-counting criterion for `S_n` (Proposition 5.7)

Main result: `eq_top_of_forall_prime_exists_isCycle`, conditional on the cited
`BMORPrimeCountingBound` [BMOR, Corollary 1.7], `BrunTitchmarshInequality` [MV, Theorem 2] and
`JonesCycleTheorem` [Jones, Corollary 1.3].

Proof outline (it follows the printed proof; all numerics are proved here; `L = log n ≥ 13.8`,
`c_D = D/(2φ(D))`, `T` = number of eligible primes `p ≡ r (mod D)` with `Dn + 10D < p < 3Dn/2`):

* `count_full`, `count_eligible`: by [BMOR] at the endpoints `Dn` and `3Dn/2` (the upper endpoint is
  composite, `not_prime_hi`), `Li(b) - Li(a) ≥ (b - a)/log b`, `log (3Dn/2) ≤ L + log 9`, and
  discarding at most `10D` integers: the count in a reduced class modulo `q` exceeds
  `Dn/(2φ(q)(L + log 9)) - 0.0675 Dn/L² - 10D`.
* `total_numeric`: hence `T > 0.84 c_D n/L` (the bracket is
  `≥ 69/80 - 9/460 - 691/1250000 > 21/25`).
* `small_lift_numeric`: a reduced class modulo `Db`, `b ∈ {2,3}`, contains `> 0.4 n/L` such
  primes (`69/160 - 27/920 - 2073/2500000 > 2/5`).
* A block of size `b` (`2 ≤ b < n`, `b ∣ n`) gives `b ∣ d_p` (Lemma 5.3, as `n/2 < d_p ≤ n - 9`,
  `cycle_length_bounds`), so every counted prime is `≡ D + r (mod Db)` (`forced_class`).
* `b ∈ {2,3}`: the class `r (mod Db)` contains an eligible prime (`exists_prime_lift`), which is not
  in the forced class.
* `4 ≤ b ≤ n^{1/4}`: Brun–Titchmarsh with `y = Dn/2`, `q = Db`, `φ(Db) ≥ 4φ(D)`
  (`four_mul_totient_le`): `T < Dn/(4φ(D)(3L/4 - log 2)) < (138/193) c_D n/L` (`bt_numeric`).
* `b > n^{1/4}`: at most `n/(2b) + 1` integers of the interval lie in the forced class
  (`card_le_of_forall_modEq_succ`), and `L (n/(2b) + 1) < (691/3160 + 691/50000000) n < n/4`
  (`large_numeric`).
* So `G` is primitive; Jones gives `A_n ≤ G`; a prime `p ≡ r + D (mod 2D)` gives an even
  `d_p`, hence an odd cycle in `G`, so `G = ⊤`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Real

/-! ### Totient bounds -/

theorem two_le_totient {m : ℕ} (hm : 3 ≤ m) : 2 ≤ m.totient := by
  have h0 : 0 < m.totient := Nat.totient_pos.mpr (by omega)
  have h1 : m.totient ≠ 1 := by rw [Ne, Nat.totient_eq_one_iff]; omega
  omega

theorem four_le_totient_of_odd {m : ℕ} (hodd : Odd m) (hm : 5 ≤ m) : 4 ≤ m.totient := by
  have hp : m.minFac.Prime := Nat.minFac_prime (by omega)
  have hpm : m.minFac ∣ m := Nat.minFac_dvd m
  have hp2 : m.minFac ≠ 2 := by
    intro h
    rw [h] at hpm
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpm)
  have hp3 : 3 ≤ m.minFac := by have := hp.two_le; omega
  by_cases h3 : m.minFac = 3
  · obtain ⟨k, hk⟩ := hpm
    rw [h3] at hk
    have hk3 : 3 ≤ k := by
      rcases hodd with ⟨j, hj⟩
      omega
    by_cases h3k : 3 ∣ k
    · rw [hk, Nat.totient_mul_of_prime_of_dvd Nat.prime_three h3k]
      have := two_le_totient hk3
      omega
    · rw [hk, Nat.totient_mul ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3k),
        Nat.totient_prime Nat.prime_three]
      have := two_le_totient hk3
      omega
  · have hp4 : m.minFac ≠ 4 := by
      intro h
      rw [h] at hp
      exact absurd hp (by decide)
    have hp5 : 5 ≤ m.minFac := by omega
    have hdvd := Nat.totient_dvd_of_dvd hpm
    rw [Nat.totient_prime hp] at hdvd
    have := Nat.le_of_dvd (Nat.totient_pos.mpr (by omega)) hdvd
    omega

theorem four_le_totient {m : ℕ} (hm : m = 5 ∨ 7 ≤ m) : 4 ≤ m.totient := by
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | hodd
  · have hm2 : m = 2 * k := by omega
    rcases Nat.even_or_odd k with hke | hko
    · rw [hm2, Nat.totient_mul_of_prime_of_dvd Nat.prime_two (even_iff_two_dvd.mp hke)]
      have := two_le_totient (m := k) (by omega)
      omega
    · rw [hm2, Nat.totient_two_mul_of_odd hko]
      apply four_le_totient_of_odd hko
      rcases hko with ⟨j, hj⟩
      omega
  · exact four_le_totient_of_odd hodd (by omega)

/-- `φ(Db) ≥ 4 φ(D)` for `D ∈ {2, 6}` and `b ≥ 4`. -/
theorem four_mul_totient_le {D b : ℕ} (hD : D = 2 ∨ D = 6) (hb : 4 ≤ b) :
    4 * D.totient ≤ (D * b).totient := by
  by_cases h46 : b = 4 ∨ b = 6
  · rcases hD with rfl | rfl <;> rcases h46 with rfl | rfl <;> decide
  · have h1 := Nat.totient_super_multiplicative D b
    have h4 := four_le_totient (m := b) (by omega)
    calc 4 * D.totient ≤ b.totient * D.totient := Nat.mul_le_mul_right _ h4
      _ = D.totient * b.totient := mul_comm _ _
      _ ≤ _ := h1

theorem totient_two_or_six {D : ℕ} (hD : D = 2 ∨ D = 6) :
    (1 : ℝ) ≤ D.totient ∧ (D.totient : ℝ) ≤ 2 ∧ 2 * (D.totient : ℝ) ≤ D := by
  rcases hD with rfl | rfl
  · have : Nat.totient 2 = 1 := by decide
    rw [this]; norm_num
  · have : Nat.totient 6 = 2 := by decide
    rw [this]; norm_num

/-- The reduced classes used for the small block sizes and for the parity argument. -/
theorem gcd_lift_classes {D : ℕ} (hD : D = 2 ∨ D = 6) {r : ℤ} (hr : |r| < D)
    (hrD : Int.gcd r D = 1) :
    Int.gcd r ((D * 2 : ℕ) : ℤ) = 1 ∧ Int.gcd r ((D * 3 : ℕ) : ℤ) = 1 ∧
      Int.gcd (r + D) ((D * 2 : ℕ) : ℤ) = 1 := by
  obtain ⟨h1, h2⟩ := abs_lt.mp hr
  rcases hD with rfl | rfl
  · push_cast at h1 h2 hrD ⊢
    interval_cases r <;> revert hrD <;> decide
  · push_cast at h1 h2 hrD ⊢
    interval_cases r <;> revert hrD <;> decide

/-! ### Prime counts in the interval `(Dn, 3Dn/2)` -/

/-- The upper endpoint `3Dn/2` is a natural number for `D ∈ {2, 6}`. -/
theorem two_mul_hi {D n : ℕ} (hD : D = 2 ∨ D = 6) : 2 * (3 * D * n / 2) = 3 * D * n := by
  rcases hD with rfl | rfl <;> omega

theorem lo_le_hi {D n : ℕ} (hD : D = 2 ∨ D = 6) : D * n ≤ 3 * D * n / 2 := by
  rcases hD with rfl | rfl <;> omega

/-- The upper endpoint `3Dn/2` of the interval is composite (it is a multiple of `3`). -/
theorem not_prime_hi {D n : ℕ} (hD : D = 2 ∨ D = 6) (hn : 10 ^ 6 ≤ n) :
    ¬ (3 * D * n / 2).Prime := by
  intro hp
  have h3 : 3 ∣ 3 * D * n / 2 := by rcases hD with rfl | rfl <;> omega
  rcases hp.eq_one_or_self_of_dvd 3 h3 with h | h <;> rcases hD with rfl | rfl <;> omega

/-- The primes of the interval `(lo, 3Dn/2]` are exactly those with `p < 3Dn/2`, because the upper
endpoint is composite. -/
theorem mem_primesIoc_hi {D n p q lo : ℕ} {a : ℤ} (hD : D = 2 ∨ D = 6) (hn : 10 ^ 6 ≤ n) :
    p ∈ primesIoc lo (3 * D * n / 2) q a ↔
      lo < p ∧ 2 * p < 3 * D * n ∧ p.Prime ∧ (p : ℤ) ≡ a [ZMOD q] := by
  rw [mem_primesIoc]
  have h2 := two_mul_hi (D := D) (n := n) hD
  constructor
  · rintro ⟨h1, h2', h3, h4⟩
    have hne : p ≠ 3 * D * n / 2 := fun h => not_prime_hi hD hn (h ▸ h3)
    exact ⟨h1, by omega, h3, h4⟩
  · rintro ⟨h1, h2', h3, h4⟩
    exact ⟨h1, by omega, h3, h4⟩

/-- The count of primes of a reduced class modulo `q` in the interval `(Dn, 3Dn/2)`: [BMOR] at
both endpoints, `Li(b) - Li(a) ≥ (b - a)/log b`, and `log (3Dn/2) ≤ log n + log 9`
(proof of Proposition 5.7, first display). -/
theorem count_full (hBMOR : BMORPrimeCountingBound) {D n q : ℕ} {a : ℤ} (hD : D = 2 ∨ D = 6)
    (hn : 10 ^ 6 ≤ n) (hq1 : 1 ≤ q) (hq : q ≤ 10 ^ 5) (ha : Int.gcd a q = 1) :
    (D : ℝ) * n / (2 * (q.totient * (Real.log n + Real.log 9))) -
        0.0675 * ((D : ℝ) * n) / Real.log n ^ 2 <
      (primesIoc (D * n) (3 * D * n / 2) q a).card := by
  have hD2 : 2 ≤ D := by rcases hD with rfl | rfl <;> norm_num
  have hD6 : D ≤ 6 := by rcases hD with rfl | rfl <;> norm_num
  have h2hi := two_mul_hi (D := D) (n := n) hD
  have hle := lo_le_hi (D := D) (n := n) hD
  have hlo : 10 ^ 6 ≤ D * n := by nlinarith
  have h := card_primesIoc_gt hBMOR hq1 hq ha hlo hle
  obtain ⟨hi, hhi⟩ : ∃ hi, hi = 3 * D * n / 2 := ⟨_, rfl⟩
  rw [← hhi] at h h2hi ⊢
  have hN : (10 : ℝ) ^ 6 ≤ (n : ℝ) := by exact_mod_cast hn
  have hDr2 : (2 : ℝ) ≤ D := by exact_mod_cast hD2
  have hDr6 : (D : ℝ) ≤ 6 := by exact_mod_cast hD6
  have hhir : (2 : ℝ) * hi = 3 * (D * n) := by
    have : ((2 * hi : ℕ) : ℝ) = ((3 * D * n : ℕ) : ℝ) := by rw [h2hi]
    push_cast at this
    linarith
  have hlor : ((D * n : ℕ) : ℝ) = D * n := by push_cast; rfl
  rw [hlor] at h
  have hNpos : (0 : ℝ) < n := by linarith
  have hL138 : 13.8 ≤ Real.log n := log_ge_of_million_le hN
  have hL0 : 0 < Real.log n := by linarith
  have hDN2 : 2 * (n : ℝ) ≤ D * n := mul_le_mul_of_nonneg_right hDr2 hNpos.le
  have hDN6 : (D : ℝ) * n ≤ 6 * n := mul_le_mul_of_nonneg_right hDr6 hNpos.le
  have hhiN : (n : ℝ) ≤ hi := by linarith
  have hhi9 : (hi : ℝ) ≤ 9 * n := by linarith
  have hloN : (n : ℝ) ≤ D * n := by linarith
  have hloghi : Real.log n ≤ Real.log hi := Real.log_le_log hNpos hhiN
  have hloglo : Real.log n ≤ Real.log ((D : ℝ) * n) := Real.log_le_log hNpos hloN
  have hloghi' : Real.log hi ≤ Real.log n + Real.log 9 := by
    calc Real.log hi ≤ Real.log (9 * n) := Real.log_le_log (by linarith) hhi9
      _ = Real.log n + Real.log 9 := by rw [Real.log_mul (by norm_num) hNpos.ne']; ring
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hDNpos : (0 : ℝ) ≤ D * n := by linarith
  have term1 : (D : ℝ) * n / (2 * (q.totient * (Real.log n + Real.log 9))) ≤
      ((hi : ℝ) - D * n) / (q.totient * Real.log hi) := by
    have e : ((hi : ℝ) - D * n) = D * n / 2 := by linarith
    rw [e, div_div]
    refine div_le_div_of_nonneg_left hDNpos (mul_pos two_pos (mul_pos hφ (by linarith))) ?_
    have := mul_le_mul_of_nonneg_left hloghi' hφ.le
    linarith
  have term2 : 0.027 * (((D : ℝ) * n) / Real.log ((D : ℝ) * n) ^ 2 + (hi : ℝ) / Real.log hi ^ 2) ≤
      0.0675 * ((D : ℝ) * n) / Real.log n ^ 2 := by
    have t1 : ((D : ℝ) * n) / Real.log ((D : ℝ) * n) ^ 2 ≤ ((D : ℝ) * n) / Real.log n ^ 2 :=
      div_le_div_of_nonneg_left hDNpos (pow_pos hL0 2) (pow_le_pow_left₀ hL0.le hloglo 2)
    have t2 : (hi : ℝ) / Real.log hi ^ 2 ≤ (hi : ℝ) / Real.log n ^ 2 :=
      div_le_div_of_nonneg_left (by linarith) (pow_pos hL0 2) (pow_le_pow_left₀ hL0.le hloghi 2)
    have t3 : ((D : ℝ) * n) / Real.log n ^ 2 + (hi : ℝ) / Real.log n ^ 2 =
        2.5 * ((D : ℝ) * n) / Real.log n ^ 2 := by
      rw [← add_div, show (D : ℝ) * n + hi = 2.5 * ((D : ℝ) * n) by linarith]
    have t4 : 0.027 * (2.5 * ((D : ℝ) * n) / Real.log n ^ 2) =
        0.0675 * ((D : ℝ) * n) / Real.log n ^ 2 := by ring
    linarith
  linarith

/-- Discarding the integers of `(Dn, Dn + 10D]` loses at most `10D` primes. -/
theorem card_primesIoc_le_add {lo hi m q : ℕ} {a : ℤ} :
    (primesIoc lo hi q a).card ≤ (primesIoc (lo + m) hi q a).card + m := by
  have hsub : primesIoc lo hi q a ⊆ primesIoc (lo + m) hi q a ∪ Finset.Ioc lo (lo + m) := by
    intro p hp
    rw [mem_primesIoc] at hp
    rw [Finset.mem_union, mem_primesIoc, Finset.mem_Ioc]
    by_cases h : lo + m < p
    · exact Or.inl ⟨h, hp.2⟩
    · exact Or.inr ⟨hp.1, by omega⟩
  calc (primesIoc lo hi q a).card
      ≤ (primesIoc (lo + m) hi q a ∪ Finset.Ioc lo (lo + m)).card := Finset.card_le_card hsub
    _ ≤ (primesIoc (lo + m) hi q a).card + (Finset.Ioc lo (lo + m)).card :=
        Finset.card_union_le _ _
    _ = _ := by rw [Nat.card_Ioc]; simp

/-- The count of the eligible primes `Dn + 10D < p < 3Dn/2` in a reduced class modulo `q`:
`|P| > Dn/(2φ(q)(L + log 9)) - 0.0675 Dn/L² - 10D` (proof of Proposition 5.7). -/
theorem count_eligible (hBMOR : BMORPrimeCountingBound) {D n q : ℕ} {a : ℤ}
    (hD : D = 2 ∨ D = 6) (hn : 10 ^ 6 ≤ n) (hq1 : 1 ≤ q) (hq : q ≤ 10 ^ 5)
    (ha : Int.gcd a q = 1) :
    (D : ℝ) * n / (2 * (q.totient * (Real.log n + Real.log 9))) -
        0.0675 * ((D : ℝ) * n) / Real.log n ^ 2 - 10 * D <
      (primesIoc (D * n + 10 * D) (3 * D * n / 2) q a).card := by
  have h := count_full hBMOR hD hn hq1 hq ha
  have h2 : ((primesIoc (D * n) (3 * D * n / 2) q a).card : ℝ) ≤
      (primesIoc (D * n + 10 * D) (3 * D * n / 2) q a).card + 10 * D := by
    exact_mod_cast card_primesIoc_le_add (lo := D * n) (hi := 3 * D * n / 2) (m := 10 * D)
      (q := q) (a := a)
  linarith

/-! ### Numerical inequalities (the printed estimates of the proof) -/

/-- The total count, `T > 0.84 c_D n / L` with `c_D = D/(2φ(D))`: the expression
`L/(L + log 9) - 0.27/L - 40L/n` is at least `69/80 - 9/460 - 691/1250000 > 21/25`, using
`L ≥ 69/5`, `log 9 < 11/5` and `L/n ≤ 13.82/10⁶`. -/
theorem total_numeric {D t n L ℓ T : ℝ} (hD2 : 2 ≤ D) (ht1 : 1 ≤ t) (ht2 : t ≤ 2)
    (hn : 10 ^ 6 ≤ n) (hL : 13.8 ≤ L) (hLn : L / n ≤ 13.82 / 10 ^ 6) (hℓ0 : 0 ≤ ℓ)
    (hℓ : ℓ ≤ 2.2) (hT : D * n / (2 * (t * (L + ℓ))) - 0.0675 * (D * n) / L ^ 2 - 10 * D < T) :
    0.84 * (D * n / (2 * t * L)) < T := by
  have hL0 : 0 < L := by linarith
  have hn0 : 0 < n := by linarith
  have ht0 : 0 < t := by linarith
  have hD0 : 0 < D := by linarith
  have hLl : 0 < L + ℓ := by linarith
  have hX : 0 < D * n / (2 * t) := by positivity
  have h1 : (69 : ℝ) / 80 ≤ L / (L + ℓ) := by
    rw [div_le_div_iff₀ (by norm_num) hLl]; linarith
  have h2 : 0.27 / L ≤ 9 / 460 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]; linarith
  have h3 : 40 * (L / n) ≤ 691 / 1250000 := by linarith
  have key : 0.84 ≤ L / (L + ℓ) - 0.27 / L - 40 * (L / n) := by linarith
  have e1 : D * n / (2 * (t * (L + ℓ))) = (D * n / (2 * t)) * (1 / (L + ℓ)) := by
    field_simp
  have e2 : 0.0675 * (D * n) / L ^ 2 = (D * n / (2 * t)) * (0.135 * t / L ^ 2) := by
    field_simp
    ring
  have e3 : 10 * D = (D * n / (2 * t)) * (20 * t / n) := by
    field_simp
    ring
  have e4 : 0.84 * (D * n / (2 * t * L)) = (D * n / (2 * t)) * (0.84 / L) := by
    field_simp
  have s1 : 0.135 * t / L ^ 2 ≤ 0.27 / L ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) (pow_pos hL0 2).le
  have s2 : 20 * t / n ≤ 40 / n := div_le_div_of_nonneg_right (by linarith) hn0.le
  have s3 : 0.84 / L ≤ 1 / (L + ℓ) - 0.27 / L ^ 2 - 40 / n := by
    have hq : 0 ≤ 1 / L := by positivity
    have := mul_le_mul_of_nonneg_left key hq
    have f1 : 1 / L * (L / (L + ℓ) - 0.27 / L - 40 * (L / n)) =
        1 / (L + ℓ) - 0.27 / L ^ 2 - 40 / n := by field_simp
    have f2 : 1 / L * 0.84 = 0.84 / L := by ring
    linarith
  have s4 := mul_le_mul_of_nonneg_left
    (show 0.84 / L ≤ 1 / (L + ℓ) - 0.135 * t / L ^ 2 - 20 * t / n by linarith) hX.le
  rw [mul_sub, mul_sub, ← e1, ← e2, ← e3, ← e4] at s4
  linarith

/-- The count in a lifted class, `> 0.4 n/L`: `D/(2φ(Db)) ≥ 1/2`, `D ≤ 6`, and
`L/(2(L + log 9)) - 0.405/L - 60 L/n ≥ 69/160 - 27/920 - 2073/2500000 > 2/5`. -/
theorem small_lift_numeric {D f n L ℓ T : ℝ} (hD6 : D ≤ 6) (hf1 : 1 ≤ f)
    (hfD : f ≤ D) (hn : 10 ^ 6 ≤ n) (hL : 13.8 ≤ L) (hLn : L / n ≤ 13.82 / 10 ^ 6)
    (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ 2.2)
    (hT : D * n / (2 * (f * (L + ℓ))) - 0.0675 * (D * n) / L ^ 2 - 10 * D < T) :
    0.4 * (n / L) < T := by
  have hL0 : 0 < L := by linarith
  have hn0 : 0 < n := by linarith
  have hf0 : 0 < f := by linarith
  have hLl : 0 < L + ℓ := by linarith
  have a1 : n / (2 * (L + ℓ)) ≤ D * n / (2 * (f * (L + ℓ))) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hfD (mul_pos hn0 hLl).le]
  have a2 : 0.0675 * (D * n) / L ^ 2 ≤ 0.405 * n / L ^ 2 :=
    div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_right hD6 hn0.le])
      (pow_pos hL0 2).le
  have h1 : (69 : ℝ) / 160 ≤ L / (2 * (L + ℓ)) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
  have h2 : 0.405 / L ≤ 27 / 920 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]; linarith
  have h3 : 60 * (L / n) ≤ 2073 / 2500000 := by linarith
  have key : 0.4 ≤ L / (2 * (L + ℓ)) - 0.405 / L - 60 * (L / n) := by linarith
  have e1 : n / (2 * (L + ℓ)) = n * (1 / (2 * (L + ℓ))) := by field_simp
  have e2 : 0.405 * n / L ^ 2 = n * (0.405 / L ^ 2) := by field_simp
  have e3 : (60 : ℝ) = n * (60 / n) := by field_simp
  have e4 : 0.4 * (n / L) = n * (0.4 / L) := by field_simp
  have s3 : 0.4 / L ≤ 1 / (2 * (L + ℓ)) - 0.405 / L ^ 2 - 60 / n := by
    have hq : 0 ≤ 1 / L := by positivity
    have := mul_le_mul_of_nonneg_left key hq
    have f1 : 1 / L * (L / (2 * (L + ℓ)) - 0.405 / L - 60 * (L / n)) =
        1 / (2 * (L + ℓ)) - 0.405 / L ^ 2 - 60 / n := by field_simp
    have f2 : 1 / L * 0.4 = 0.4 / L := by ring
    linarith
  have s4 := mul_le_mul_of_nonneg_left s3 hn0.le
  rw [mul_sub, mul_sub, ← e1, ← e2, ← e3, ← e4] at s4
  linarith

/-- The Brun–Titchmarsh range gives a contradiction: with `y = Dn/2`, `q = Db`,
`T < Dn/(φ(Db) log(n/(2b))) ≤ Dn/(4φ(D)(3L/4 - log 2)) ≤ (138/193) c_D n/L`, using
`L ≥ 69/5` and `log 2 < 7/10`; this contradicts `T > 0.84 c_D n/L`. -/
theorem bt_numeric {D t n L ℓ₂ ℓ f T : ℝ} (hD : 0 < D) (hn : 0 < n) (ht1 : 1 ≤ t)
    (hL : 13.8 ≤ L) (hℓ₂ : ℓ₂ ≤ 0.7) (hmain : 0.84 * (D * n / (2 * t * L)) < T)
    (hT0 : 0 ≤ T) (hf : 4 * t ≤ f) (hℓ : 3 / 4 * L - ℓ₂ ≤ ℓ)
    (hBT : T < D * n / (f * ℓ)) : False := by
  have hL0 : 0 < L := by linarith
  have ht0 : 0 < t := by linarith
  have hf0 : 0 < f := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have h1 : T * (f * ℓ) < D * n := (lt_div_iff₀ (mul_pos hf0 hℓ0)).mp hBT
  have h2 : 4 * t * (3 / 4 * L - ℓ₂) ≤ f * ℓ :=
    mul_le_mul hf hℓ (by linarith) hf0.le
  have h3 : 193 / 276 * L ≤ 3 / 4 * L - ℓ₂ := by linarith
  have h4 : 4 * t * (193 / 276 * L) ≤ 4 * t * (3 / 4 * L - ℓ₂) :=
    mul_le_mul_of_nonneg_left h3 (by linarith)
  have h5 : T * (193 / 69 * (t * L)) ≤ T * (f * ℓ) :=
    mul_le_mul_of_nonneg_left (by linarith) hT0
  have h6 : 0.84 * (D * n) < T * (2 * t * L) := by
    have e : 0.84 * (D * n / (2 * t * L)) = 0.84 * (D * n) / (2 * t * L) := by ring
    rw [e] at hmain
    exact (div_lt_iff₀ (by positivity)).mp hmain
  have hDn : 0 < D * n := mul_pos hD hn
  nlinarith

/-- The large-block range gives a contradiction: `T ≤ n/(2b) + 1`, `L < 4 log b`,
`log b ≤ (691/6320) b` (so `L T < (691/3160) n + L ≤ (691/3160 + 691/50000000) n < n/4`), against
`T > 0.84 c_D n/L ≥ 0.84 n/L`. -/
theorem large_numeric {D t n L ℓb b T : ℝ} (hD : 2 * t ≤ D) (ht1 : 1 ≤ t) (hn : 10 ^ 6 ≤ n)
    (hL : 13.8 ≤ L) (hLn : L / n ≤ 13.82 / 10 ^ 6) (hb : 31.6 ≤ b) (hLb : L < 4 * ℓb)
    (hℓb : ℓb ≤ 691 / 6320 * b) (hmain : 0.84 * (D * n / (2 * t * L)) < T)
    (hT : T ≤ n / (2 * b) + 1) : False := by
  have hL0 : 0 < L := by linarith
  have hn0 : 0 < n := by linarith
  have hb0 : 0 < b := by linarith
  have ht0 : 0 < t := by linarith
  have h1 : n / L ≤ D * n / (2 * t * L) := by
    rw [div_le_div_iff₀ hL0 (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hD (mul_pos hn0 hL0).le]
  have h2 : 0.84 * n < T * L := by
    have e : 0.84 * (n / L) = 0.84 * n / L := by ring
    have : 0.84 * (n / L) < T := by linarith
    rw [e] at this
    exact (div_lt_iff₀ hL0).mp this
  have hLb2 : L < 4 * (691 / 6320) * b := by linarith
  have h3 : L * (n / (2 * b)) ≤ 2 * (691 / 6320) * n := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hLb2.le hn0.le]
  have h4 : L ≤ 13.82 / 10 ^ 6 * n := (div_le_iff₀ hn0).mp hLn
  have h5 := mul_le_mul_of_nonneg_left hT hL0.le
  nlinarith

/-! ### Cycle lengths and the forced residue class -/

/-- For an eligible prime, the cycle length `d_p = 2n + 1 - (p - r)/D` satisfies
`n/2 < d_p ≤ n - 9`. -/
theorem cycle_length_bounds {D n p : ℕ} {r : ℤ} (hD0 : 0 < D) (hr : |r| < D)
    (hpr : (p : ℤ) ≡ r [ZMOD D]) (h1 : D * n + 10 * D < p) (h2 : 2 * p < 3 * D * n) :
    (n : ℤ) < 2 * (2 * n + 1 - ((p : ℤ) - r) / D) ∧ 2 * n + 1 - ((p : ℤ) - r) / D ≤ n - 9 := by
  obtain ⟨k, hk⟩ := Int.ModEq.dvd hpr.symm
  have hD0' : (0 : ℤ) < D := by exact_mod_cast hD0
  rw [hk, Int.mul_ediv_cancel_left _ hD0'.ne']
  obtain ⟨hr1, hr2⟩ := abs_lt.mp hr
  have h1' : (D : ℤ) * n + 10 * D < p := by exact_mod_cast h1
  have h2' : 2 * (p : ℤ) < 3 * D * n := by exact_mod_cast h2
  have hk1 : (D : ℤ) * (n + 9) < D * k := by linarith
  have hk2 : (D : ℤ) * (2 * k) < D * (3 * n + 2) := by linarith
  have hk1' := lt_of_mul_lt_mul_left hk1 hD0'.le
  have hk2' := lt_of_mul_lt_mul_left hk2 hD0'.le
  constructor <;> omega

/-- If the block size `b ∣ n` divides `d_p`, then `p ≡ D + r (mod Db)`. -/
theorem forced_class {D n b p : ℕ} {r : ℤ} (hD0 : 0 < D) (hpr : (p : ℤ) ≡ r [ZMOD D])
    (hbn : b ∣ n) (hbd : (b : ℤ) ∣ 2 * n + 1 - ((p : ℤ) - r) / D) :
    (p : ℤ) ≡ D + r [ZMOD ((D * b : ℕ) : ℤ)] := by
  obtain ⟨k, hk⟩ := Int.ModEq.dvd hpr.symm
  have hD0' : (0 : ℤ) < D := by exact_mod_cast hD0
  rw [hk, Int.mul_ediv_cancel_left _ hD0'.ne'] at hbd
  obtain ⟨m, hm⟩ := hbd
  obtain ⟨n', hn'⟩ := hbn
  have hn'' : (n : ℤ) = b * n' := by exact_mod_cast hn'
  rw [Int.modEq_iff_dvd]
  refine ⟨m - 2 * n', ?_⟩
  push_cast
  linear_combination -hk + (D : ℤ) * hm - 2 * (D : ℤ) * hn''

/-! ### The three ranges of block sizes -/

/-- A prime of the interval in a lifted class modulo `Db`, `b ∈ {2, 3}` (the printed lower bound
`> 0.4 n/L` is positive). -/
theorem exists_prime_lift (hBMOR : BMORPrimeCountingBound) {D n k : ℕ} {a : ℤ}
    (hD : D = 2 ∨ D = 6) (hn : 10 ^ 6 ≤ n) (hk2 : 2 ≤ k) (hk3 : k ≤ 3)
    (ha : Int.gcd a ((D * k : ℕ) : ℤ) = 1) :
    ∃ p : ℕ, D * n + 10 * D < p ∧ 2 * p < 3 * D * n ∧ p.Prime ∧
      (p : ℤ) ≡ a [ZMOD ((D * k : ℕ) : ℤ)] := by
  have hD2 : 2 ≤ D := by rcases hD with rfl | rfl <;> norm_num
  have hD6 : D ≤ 6 := by rcases hD with rfl | rfl <;> norm_num
  have hq1 : 1 ≤ D * k := Nat.mul_pos (by omega) (by omega)
  have hq18 : D * k ≤ 18 := by nlinarith
  have hc := count_eligible hBMOR hD hn (q := D * k) (a := a) hq1 (by omega) ha
  have hφ1 : (1 : ℝ) ≤ (D * k).totient := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hφD : ((D * k).totient : ℝ) ≤ D := by
    have : (D * k).totient ≤ D := by
      rcases hD with rfl | rfl <;> interval_cases k <;> decide
    exact_mod_cast this
  have hN : (10 : ℝ) ^ 6 ≤ n := by exact_mod_cast hn
  have hNpos : (0 : ℝ) < n := by linarith
  have hL := log_ge_of_million_le hN
  have hLn := log_div_le_of_million hN
  have hDr2 : (2 : ℝ) ≤ D := by exact_mod_cast hD2
  have hDr6 : (D : ℝ) ≤ 6 := by exact_mod_cast hD6
  have hpos := small_lift_numeric hDr6 hφ1 hφD hN hL hLn
    (Real.log_nonneg (by norm_num)) log_nine_lt.le hc
  have hL0 : 0 < Real.log n := by linarith
  have hcard : 0 < (primesIoc (D * n + 10 * D) (3 * D * n / 2) (D * k) a).card := by
    have : (0 : ℝ) < 0.4 * ((n : ℝ) / Real.log n) := by positivity
    exact_mod_cast this.trans hpos
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hcard
  exact ⟨p, (mem_primesIoc_hi hD hn).mp hp⟩

/-- **No nontrivial block size.** Under the hypotheses of Proposition 5.7, no `b` with
`2 ≤ b < n`, `b ∣ n`, can divide `d_p` for every eligible prime `p`. -/
theorem no_block_size (hBMOR : BMORPrimeCountingBound) (hBT : BrunTitchmarshInequality)
    {D : ℕ} (hD : D = 2 ∨ D = 6) {r : ℤ} (hr : |r| < D) (hrD : Int.gcd r D = 1) {n : ℕ}
    (hn : 10 ^ 6 ≤ n) {b : ℕ} (hb2 : 2 ≤ b) (hbn : b ∣ n) (hblt : b < n)
    (hdiv : ∀ p : ℕ, p.Prime → D * n + 10 * D < p → 2 * p < 3 * D * n →
      (p : ℤ) ≡ r [ZMOD D] → (b : ℤ) ∣ 2 * n + 1 - ((p : ℤ) - r) / D) : False := by
  have hD2 : 2 ≤ D := by rcases hD with rfl | rfl <;> norm_num
  have hD6 : D ≤ 6 := by rcases hD with rfl | rfl <;> norm_num
  have hD0 : 0 < D := by omega
  have hmem : ∀ {q : ℕ} {a : ℤ} {p : ℕ},
      p ∈ primesIoc (D * n + 10 * D) (3 * D * n / 2) q a ↔
        D * n + 10 * D < p ∧ 2 * p < 3 * D * n ∧ p.Prime ∧ (p : ℤ) ≡ a [ZMOD q] :=
    fun {q a p} => mem_primesIoc_hi hD hn
  have hforced : ∀ p ∈ primesIoc (D * n + 10 * D) (3 * D * n / 2) D r,
      (p : ℤ) ≡ D + r [ZMOD ((D * b : ℕ) : ℤ)] := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hmem.mp hp
    exact forced_class hD0 h4 hbn (hdiv p h3 h1 h2 h4)
  have hcastDb : ((D * b : ℕ) : ℤ) = (D : ℤ) * b := by push_cast; ring
  rcases (show b ≤ 3 ∨ 4 ≤ b by omega) with hb3 | hb4
  · -- `b ∈ {2, 3}`: a prime in the class `r` modulo `Db`
    have hgcd : Int.gcd r ((D * b : ℕ) : ℤ) = 1 := by
      obtain ⟨g2, g3, -⟩ := gcd_lift_classes hD hr hrD
      interval_cases b
      · exact g2
      · exact g3
    obtain ⟨p, h1, h2, h3, h4⟩ := exists_prime_lift hBMOR hD hn hb2 hb3 hgcd
    have h4' : (p : ℤ) ≡ r [ZMOD D] := by
      rw [hcastDb] at h4
      exact h4.of_mul_right _
    have hf := hforced p (hmem.mpr ⟨h1, h2, h3, h4'⟩)
    have hrr := Int.modEq_iff_dvd.mp (h4.symm.trans hf)
    rw [add_sub_cancel_right] at hrr
    have hnat : D * b ∣ D := by exact_mod_cast hrr
    have := Nat.le_of_dvd hD0 hnat
    nlinarith
  · -- the total count `T > 0.84 c_D n / L`
    have hN : (10 : ℝ) ^ 6 ≤ (n : ℝ) := by exact_mod_cast hn
    have hNpos : (0 : ℝ) < n := by linarith
    have hL : 13.8 ≤ Real.log n := log_ge_of_million_le hN
    have hLn := log_div_le_of_million hN
    have hL0 : 0 < Real.log n := by linarith
    have hl2 := log_two_lt
    have hDr2 : (2 : ℝ) ≤ D := by exact_mod_cast hD2
    have hX : 0 < (D : ℝ) * (n : ℝ) := mul_pos (by linarith) hNpos
    have hc := count_eligible hBMOR hD hn (q := D) (a := r) (by omega) (by omega) hrD
    obtain ⟨ht1, ht2, htD⟩ := totient_two_or_six hD
    have hmain := total_numeric hDr2 ht1 ht2 hN hL hLn (Real.log_nonneg (by norm_num))
      log_nine_lt.le hc
    set S := primesIoc (D * n + 10 * D) (3 * D * n / 2) D r with hS
    have hT0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
    have hSpos : 0 < S.card := by
      by_contra h
      have h0 : S.card = 0 := by omega
      rw [h0, Nat.cast_zero] at hmain
      have : (0 : ℝ) < 0.84 * ((D : ℝ) * n / (2 * D.totient * Real.log n)) := by positivity
      linarith
    obtain ⟨p₀, hp₀⟩ := Finset.card_pos.mp hSpos
    -- the forced class is reduced
    have hgcd : Int.gcd (D + r) ((D * b : ℕ) : ℤ) = 1 := by
      obtain ⟨h1, h2, h3, h4⟩ := hmem.mp hp₀
      have hf := hforced p₀ hp₀
      have hg1 : ((Int.gcd (D + r) ((D * b : ℕ) : ℤ) : ℕ) : ℤ) ∣ D + r := Int.gcd_dvd_left _ _
      have hg2 : ((Int.gcd (D + r) ((D * b : ℕ) : ℤ) : ℕ) : ℤ) ∣ ((D * b : ℕ) : ℤ) :=
        Int.gcd_dvd_right _ _
      have hg3 : ((Int.gcd (D + r) ((D * b : ℕ) : ℤ) : ℕ) : ℤ) ∣ (p₀ : ℤ) := by
        have h5 := dvd_trans hg2 (Int.modEq_iff_dvd.mp hf)
        have h6 := dvd_sub hg1 h5
        rwa [sub_sub_cancel] at h6
      have hg4 := Int.natCast_dvd_natCast.mp hg3
      have hg5 := Int.natCast_dvd_natCast.mp hg2
      rcases h3.eq_one_or_self_of_dvd _ hg4 with h | h
      · exact h
      · exfalso
        have h7 := Nat.le_of_dvd (by positivity) hg5
        have h8 : D * b ≤ D * n := Nat.mul_le_mul_left D hblt.le
        omega
    have h2hi := two_mul_hi (D := D) (n := n) hD
    have hle := lo_le_hi (D := D) (n := n) hD
    have hhir : (2 : ℝ) * ((3 * D * n / 2 : ℕ) : ℝ) = 3 * (D * n) := by
      have : ((2 * (3 * D * n / 2) : ℕ) : ℝ) = ((3 * D * n : ℕ) : ℝ) := by rw [h2hi]
      push_cast at this
      linarith
    have hq0 : 0 < D * b := by positivity
    have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    have hbr : (4 : ℝ) ≤ b := by exact_mod_cast hb4
    rcases (show b ^ 4 ≤ n ∨ n < b ^ 4 by omega) with hb4n | hb4n
    · -- `4 ≤ b ≤ n^{1/4}`: Brun–Titchmarsh with `y = Dn/2`
      have h64 : 4 * b < n := by
        have : 4 ^ 3 ≤ b ^ 3 := Nat.pow_le_pow_left hb4 3
        have e : b ^ 4 = b * b ^ 3 := by ring
        nlinarith
      have h64r : 4 * (b : ℝ) < (n : ℝ) := by exact_mod_cast h64
      have hqr : (((D * b : ℕ) : ℝ)) = D * b := by push_cast; ring
      have hyq : (((D * b : ℕ) : ℝ)) < (D : ℝ) * n / 2 := by
        rw [hqr]
        have : (D : ℝ) * (4 * b) < D * (n : ℝ) := mul_lt_mul_of_pos_left h64r (by linarith)
        linarith
      have hx0 : (0 : ℝ) < ((D * n : ℕ) : ℝ) := by push_cast; exact hX
      have hB := hBT (D * b) (D + r) ((D * n : ℕ) : ℝ) ((D : ℝ) * n / 2) (by omega)
        (by exact_mod_cast hgcd) hx0 hyq
      have hxy : ((D * n : ℕ) : ℝ) + (D : ℝ) * n / 2 = ((3 * D * n / 2 : ℕ) : ℝ) := by
        push_cast; linarith
      rw [hxy, ← card_primesIoc_eq_sub hle] at hB
      have e1 : 2 * ((D : ℝ) * n / 2) = D * n := by ring
      have e2 : (D : ℝ) * n / 2 / (((D * b : ℕ) : ℝ)) = n / (2 * b) := by
        rw [hqr]; field_simp
      rw [e1, e2] at hB
      have hsub : S ⊆ primesIoc (D * n) (3 * D * n / 2) (D * b) (D + r) := by
        intro p hp
        obtain ⟨h1, h2, h3, -⟩ := hmem.mp hp
        rw [mem_primesIoc_hi hD hn]
        exact ⟨by omega, h2, h3, hforced p hp⟩
      have hSle : (S.card : ℝ) ≤
          (primesIoc (D * n) (3 * D * n / 2) (D * b) (D + r)).card := by
        exact_mod_cast Finset.card_le_card hsub
      have hf : 4 * (D.totient : ℝ) ≤ (D * b).totient := by
        exact_mod_cast four_mul_totient_le hD hb4
      have hlogb : 4 * Real.log b ≤ Real.log n := by
        have e := Real.log_pow (b : ℝ) 4
        push_cast at e
        rw [← e]
        exact Real.log_le_log (by positivity) (by exact_mod_cast hb4n)
      have hℓ : 3 / 4 * Real.log n - Real.log 2 ≤ Real.log ((n : ℝ) / (2 * b)) := by
        rw [Real.log_div hNpos.ne' (by positivity), Real.log_mul (by norm_num) hb0.ne']
        linarith
      have hl2' : Real.log 2 ≤ 0.7 := by linarith
      exact bt_numeric (by linarith) hNpos ht1 hL hl2' hmain hT0 hf hℓ
        (lt_of_le_of_lt hSle hB)
    · -- `b > n^{1/4}`: counting integers in the class `D + r (mod Db)`
      have hb32 : 32 ≤ b := by
        by_contra h
        have : b ^ 4 ≤ 31 ^ 4 := Nat.pow_le_pow_left (by omega) 4
        omega
      have hb31 : (31.6 : ℝ) ≤ b := by
        have : (32 : ℝ) ≤ b := by exact_mod_cast hb32
        linarith
      have hcount := card_le_of_forall_modEq_succ (S := S) (lo := D * n)
        (hi := 3 * D * n / 2) (q := D * b) (c := D + r) hq0 hle (fun p hp => by
          obtain ⟨h1, h2, -, -⟩ := mem_primesIoc.mp hp
          exact ⟨by omega, h2, hforced p hp⟩)
      have hT : (S.card : ℝ) ≤ (n : ℝ) / (2 * b) + 1 := by
        have e : (((3 * D * n / 2 : ℕ) : ℝ) - ((D * n : ℕ) : ℝ)) / (((D * b : ℕ) : ℝ)) =
            (n : ℝ) / (2 * b) := by
          have : (((3 * D * n / 2 : ℕ) : ℝ) - ((D * n : ℕ) : ℝ)) = D * n / 2 := by
            push_cast; linarith
          rw [this]; push_cast; field_simp
        rw [e] at hcount
        exact hcount
      have hLb : Real.log n < 4 * Real.log b := by
        have e := Real.log_pow (b : ℝ) 4
        push_cast at e
        rw [← e]
        exact Real.log_lt_log hNpos (by exact_mod_cast hb4n)
      exact large_numeric htD ht1 hN hL hLn hb31 hLb (log_le_mul_of_ge hb31) hmain hT

/-! ### Proposition 5.7 -/

/-- **Proposition 5.7**. Let `D ∈ {2, 6}`, `r ∈ ℤ` with `|r| < D` and
`gcd(r, D) = 1`, and `n ≥ 10^6`. Let `G ≤ Sym(α)`, `|α| = n`, be transitive, and suppose that
for every prime `p` with `Dn + 10D < p < 3Dn/2` and `p ≡ r (mod D)` the group `G` contains a
single cycle of length `d_p = 2n + 1 - (p - r)/D`. Then `G = Sym(α)`.

Conditional on the cited results [BMOR, Corollary 1.7], [MV, Theorem 2] (Brun–Titchmarsh) and
[Jones, Corollary 1.3], taken as the hypotheses `hBMOR`, `hBT`, `hJones`. -/
theorem eq_top_of_forall_prime_exists_isCycle (hBMOR : BMORPrimeCountingBound)
    (hBT : BrunTitchmarshInequality) (hJones : JonesCycleTheorem)
    {D : ℕ} (hD : D = 2 ∨ D = 6) {r : ℤ} (hr : |r| < D) (hrD : Int.gcd r D = 1)
    {n : ℕ} (hn : 10 ^ 6 ≤ n) {α : Type} [Fintype α] [DecidableEq α]
    (hα : Fintype.card α = n) (G : Subgroup (Equiv.Perm α))
    (hG : MulAction.IsPretransitive G α)
    (hcyc : ∀ p : ℕ, p.Prime → D * n + 10 * D < p → 2 * p < 3 * D * n →
      (p : ℤ) ≡ r [ZMOD D] →
        ∃ σ ∈ G, σ.IsCycle ∧ (σ.support.card : ℤ) = 2 * n + 1 - ((p : ℤ) - r) / D) :
    G = ⊤ := by
  have hD2 : 2 ≤ D := by rcases hD with rfl | rfl <;> norm_num
  have hD6 : D ≤ 6 := by rcases hD with rfl | rfl <;> norm_num
  have hD0 : 0 < D := by omega
  -- primitivity
  have hprim : MulAction.IsPreprimitive G α := by
    have := hG
    refine ⟨fun {B} hB => ?_⟩
    by_contra hnt
    simp only [MulAction.IsTrivialBlock, not_or] at hnt
    obtain ⟨hns, hnu⟩ := hnt
    have hb1 : 1 < B.ncard :=
      Set.one_lt_ncard_iff_nontrivial.mpr (Set.not_subsingleton_iff.mp hns)
    have hbN : B.ncard < Fintype.card α := by
      have := Set.ncard_lt_card hnu
      rwa [Nat.card_eq_fintype_card] at this
    have hbn : B.ncard ∣ n := by
      have := hB.ncard_dvd_card (Set.nonempty_of_ncard_ne_zero (by omega))
      rwa [Nat.card_eq_fintype_card, hα] at this
    refine no_block_size hBMOR hBT hD hr hrD hn hb1 hbn (hα ▸ hbN) ?_
    intro p hp h1 h2 h3
    obtain ⟨σ, hσG, hσ, hcard⟩ := hcyc p hp h1 h2 h3
    have hb := cycle_length_bounds hD0 hr h3 h1 h2
    rw [← hcard] at hb
    have hd : Fintype.card α < 2 * σ.support.card := by
      rw [hα]
      exact_mod_cast hb.1
    have := IsBlock.ncard_dvd_card_support_of_isCycle hG hB hb1 hbN hσG hσ hd
    rw [← hcard]
    exact_mod_cast this
  -- an even cycle
  obtain ⟨-, -, hg⟩ := gcd_lift_classes hD hr hrD
  obtain ⟨p, h1, h2, hp, h4⟩ := exists_prime_lift hBMOR hD hn (k := 2) (by norm_num)
    (by norm_num) hg
  have h4' : (p : ℤ) ≡ r [ZMOD D] := by
    have e : ((D * 2 : ℕ) : ℤ) = (D : ℤ) * 2 := by push_cast; ring
    rw [e] at h4
    exact (h4.of_mul_right _).trans (Int.modEq_iff_dvd.mpr (by simp))
  obtain ⟨σ, hσG, hσ, hcard⟩ := hcyc p hp h1 h2 h4'
  have hb := cycle_length_bounds hD0 hr h4' h1 h2
  rw [← hcard] at hb
  have hA : alternatingGroup α ≤ G := hJones α G hprim σ hσG hσ (by rw [hα]; omega)
  have heven : Even σ.support.card := by
    obtain ⟨k, hk⟩ := Int.ModEq.dvd h4'.symm
    have hD0' : (0 : ℤ) < D := by exact_mod_cast hD0
    rw [hk, Int.mul_ediv_cancel_left _ hD0'.ne'] at hcard
    obtain ⟨j, hj⟩ := Int.modEq_iff_dvd.mp h4
    have e : ((D * 2 : ℕ) : ℤ) = (D : ℤ) * 2 := by push_cast; ring
    rw [e] at hj
    have hkj : (D : ℤ) * (1 - k) = D * (2 * j) := by linear_combination hj + hk
    have hkj' := mul_left_cancel₀ hD0'.ne' hkj
    rw [Nat.even_iff]
    omega
  have hsign : Equiv.Perm.sign σ = -1 := by
    rw [hσ.sign, heven.neg_one_pow]
  rw [eq_top_iff]
  intro τ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h
  · exact hA (Equiv.Perm.mem_alternatingGroup.mpr h)
  · have hτσ : τ * σ⁻¹ ∈ G := hA (Equiv.Perm.mem_alternatingGroup.mpr (by
      rw [map_mul, map_inv, h, hsign]; rfl))
    simpa using G.mul_mem hτσ hσG

end ArithmeticOfJacobiPolynomials
