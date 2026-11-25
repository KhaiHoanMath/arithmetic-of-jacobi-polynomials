/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Padic.MomentBound
public import ArithmeticOfJacobiPolynomials.Jacobi.IntegralWeights
public import Mathlib.RingTheory.Polynomial.Content

/-!
# Local row bounds for integral weights (Lemma 2.4)

Fix integers `a, b ≥ 0`, `n ≥ 1` and a prime `p`. Let `Q = P_n^{(a,b)}(2X+1) / binom(n+a, a)`
(`integralWeightQ a b n`), `S = 2n + a + b + 1` and `L_p = ⌊log_p S⌋`. Lemma 2.4 of the
manuscript (Lemma 2.4) bounds the projective row sums of the roots of `Q` in `PadicAlgCl p`:
for every root `α`,
`∑_{γ ≠ α} δ_p(α, γ) ≤ L_p + 2 d_p + v_p(𝒞_n) ≤ L_p + 2 v_p(B) + v_p(𝒞_n)
  = L_p + v_p((n+a)! (n+b)! / (n! (n+a+b)!))`,
where `B = binom(n+a, a)`, `d_p = -min_j v_p([X^j] Q)` and `𝒞_n` is the root constant of
Lemma 2.3. The valuation of the factorial ratio is kept with its sign; for `a = b = r` it is
`v_p((n+r)!² / (n! (n+2r)!))`, which gives `D_p` of (2.11).

Main results:
* `ArithmeticOfJacobiPolynomials.integer_row_bound`: the projective moment bound (Lemma 2.2) for an
integer
  polynomial with a coefficient prime to `p`, rational moments and a rational root constant;
* `ArithmeticOfJacobiPolynomials.integralWeight_row_bound`: Lemma 2.4, with the signed factorial
ratio;
* `ArithmeticOfJacobiPolynomials.integralWeight_row_bound_symmetric`: the case `a = b = r`, bound
`D_p`.

The proof writes `P_n^{(a,b)}(2X+1) = p^k u` with `u ∈ ℤ[X]` having a coefficient prime to
`p`; then `u` is primitive over `ℤ_[p]`, `Q = (p^k / B) u`, and the root constant of `u` is
`𝒞_n B² / p^{2k}`, whose valuation is at most `v_p(𝒞_n B²)` since `k ≥ 0` (this is the
inequality `d_p ≤ v_p(B)` of the manuscript).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

/-! ### Integer polynomials and `ℤ_[p]` -/

/-- A nonzero integer polynomial is `p^k u` with `u` having a coefficient prime to `p`. -/
theorem exists_eq_C_pow_mul_not_dvd {p : ℕ} (hp : p.Prime) {P : ℤ[X]} (hP : P ≠ 0) :
    ∃ (k : ℕ) (u : ℤ[X]), P = C ((p : ℤ) ^ k) * u ∧ ∃ j, ¬ (p : ℤ) ∣ u.coeff j := by
  have hc : P.content ≠ 0 := content_eq_zero_iff.not.mpr hP
  obtain ⟨e, c', hpc', hc'⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hc) p
    hp.ne_one
  have hdvd : (p : ℤ) ^ e ∣ P.content := by
    rw [← Int.natAbs_dvd_natAbs, Int.natAbs_pow, Int.natAbs_natCast, hc']
    exact dvd_mul_right _ _
  obtain ⟨c, hcc⟩ := hdvd
  have hpc : ¬ (p : ℤ) ∣ c := by
    intro h
    apply hpc'
    have h1 : (P.content).natAbs = p ^ e * c.natAbs := by
      rw [hcc, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    rw [hc'] at h1
    have h2 : c' = c.natAbs := Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos e) h1
    rw [h2]
    exact Int.natAbs_dvd_natAbs.mpr h
  have hpp : ∃ j, ¬ (p : ℤ) ∣ P.primPart.coeff j := by
    by_contra! h
    have hC : C (p : ℤ) ∣ P.primPart := (C_dvd_iff_dvd_coeff _ _).mpr h
    have hu := (isPrimitive_iff_isUnit_of_C_dvd.mp (isPrimitive_primPart P)) _ hC
    rw [Int.isUnit_iff] at hu
    rcases hu with hu | hu
    · exact hp.one_lt.ne' (by exact_mod_cast hu)
    · have : (0 : ℤ) ≤ p := Int.natCast_nonneg p
      omega
  obtain ⟨j, hj⟩ := hpp
  refine ⟨e, C c * P.primPart, ?_, j, ?_⟩
  · conv_lhs => rw [P.eq_C_content_mul_primPart, hcc]
    rw [C_mul, mul_assoc]
  · rw [coeff_C_mul]
    intro h
    rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h with h | h
    · exact hpc h
    · exact hj h

/-- An integer polynomial with a coefficient prime to `p` is primitive over `ℤ_[p]`. -/
theorem isPrimitive_map_padicInt_of_not_dvd {p : ℕ} [Fact p.Prime] {P : ℤ[X]} {j : ℕ}
    (hj : ¬ (p : ℤ) ∣ P.coeff j) : (P.map (Int.castRingHom ℤ_[p])).IsPrimitive := by
  intro r hr
  have h1 : r ∣ ((P.coeff j : ℤ) : ℤ_[p]) := by
    have := (C_dvd_iff_dvd_coeff r _).mp hr j
    simpa [coeff_map] using this
  have hu : IsUnit ((P.coeff j : ℤ) : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun hlt => hj ?_)
    exact (PadicInt.norm_int_lt_one_iff_dvd _).mp hlt
  exact isUnit_of_dvd_unit h1 hu

variable {p : ℕ} [hp : Fact p.Prime]

local notation "K" => PadicAlgCl p

/-- For a nonzero rational `q`, the real valuation of `q ∈ ℚ_[p]` is `padicValRat p q`. -/
theorem padicVal_ratCast {q : ℚ} (hq : q ≠ 0) : padicVal p (q : ℚ_[p]) = padicValRat p q := by
  have hq' : (q : ℚ_[p]) ≠ 0 := Rat.cast_ne_zero.mpr hq
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (p : ℝ) ≠ 1 := ne_of_gt one_lt_prime_real
  rw [padicVal_def, Padic.norm_eq_zpow_neg_valuation hq', Padic.valuation_ratCast,
    ← Real.rpow_intCast, Real.logb_rpow hp0 hp1]
  push_cast
  ring

/-- If the rational moments `ν_j`, `j < 2n`, have valuation at least `-L` (or vanish), then
`η_p ≥ -L`. -/
theorem neg_le_minMomentVal {ν : ℕ → ℚ} {n L : ℕ}
    (hν : ∀ j < 2 * n, ν j = 0 ∨ -(L : ℤ) ≤ padicValRat p (ν j)) :
    -(L : ℝ) ≤ minMomentVal p (fun j => (ν j : ℚ_[p])) n := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hnorm : ∀ j < 2 * n, ‖((ν j : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ L := by
    intro j hj
    by_cases hj0 : ν j = 0
    · rw [hj0, Rat.cast_zero, norm_zero]; positivity
    · have hv := (hν j hj).resolve_left hj0
      rw [Padic.norm_eq_zpow_neg_valuation (Rat.cast_ne_zero.mpr hj0), Padic.valuation_ratCast,
        ← zpow_natCast]
      exact zpow_le_zpow_right₀ one_lt_prime_real.le (by omega)
  have hsup : (((range (2 * n)).sup fun j => ‖((ν j : ℚ) : ℚ_[p])‖₊ : NNReal) : ℝ) ≤
      (p : ℝ) ^ L := by
    have : ((range (2 * n)).sup fun j => ‖((ν j : ℚ) : ℚ_[p])‖₊) ≤ (p : NNReal) ^ L := by
      refine Finset.sup_le fun j hj => ?_
      rw [← NNReal.coe_le_coe]
      push_cast
      exact hnorm j (mem_range.mp hj)
    exact_mod_cast this
  rw [minMomentVal_def, neg_le_neg_iff]
  set s : ℝ := (((range (2 * n)).sup fun j => ‖((ν j : ℚ) : ℚ_[p])‖₊ : NNReal) : ℝ) with hs
  have hs0 : 0 ≤ s := NNReal.coe_nonneg _
  rcases hs0.eq_or_lt with h | h
  · rw [← h, Real.logb_zero]; positivity
  · calc Real.logb p s ≤ Real.logb p ((p : ℝ) ^ L) :=
          Real.logb_le_logb_of_le one_lt_prime_real h hsup
      _ = L := by rw [Real.logb_pow, Real.logb_self_eq_one one_lt_prime_real, mul_one]

/-- `aeval` of the rational image of an integer polynomial at a point of `PadicAlgCl p`. -/
theorem aeval_map_intCast_rat (u : ℤ[X]) (z : K) :
    aeval z (u.map (Int.castRingHom ℚ)) = (u.map (Int.castRingHom K)).eval z := by
  rw [aeval_def, eval₂_eq_eval_map, Polynomial.map_map]
  congr 2

theorem map_padicInt_map_eq (u : ℤ[X]) :
    (u.map (Int.castRingHom ℤ_[p])).map (algebraMap ℤ_[p] K) = u.map (Int.castRingHom K) := by
  rw [Polynomial.map_map]
  congr 1

/-- The second polynomial of Lemma 2.2 is the coefficientwise moment quotient. -/
theorem padicMomentQuotient_eq_momentQuotient (H : ℤ_[p][X]) (μ : ℕ → ℚ_[p]) :
    padicMomentQuotient H μ = momentQuotient μ (H.map (algebraMap ℤ_[p] ℚ_[p])) := by
  have hinj : Function.Injective (algebraMap ℤ_[p] ℚ_[p]) := IsFractionRing.injective ℤ_[p] ℚ_[p]
  rw [padicMomentQuotient_def, momentQuotient_apply, sum_over_range _ (by simp),
    natDegree_map_eq_of_injective hinj]
  refine sum_congr rfl fun j _ => ?_
  rw [coeff_map, PadicInt.algebraMap_apply, momentKernel_eq]

/-- `I(X^l P) = ∑_i P_i μ_{i+l}`. -/
theorem momentFunctional_X_pow_mul {R : Type*} [CommRing R] (μ : ℕ → R) (l : ℕ) (P : R[X]) :
    momentFunctional μ (X ^ l * P) =
      ∑ i ∈ range (P.natDegree + 1), P.coeff i * μ (i + l) := by
  have h : momentFunctional μ (X ^ l * P) = momentFunctional (fun i => μ (i + l)) P := by
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ => rw [mul_add, map_add, hP, hQ, map_add]
    | monomial n a => rw [X_pow_mul_monomial, momentFunctional_monomial, momentFunctional_monomial]
  rw [h, momentFunctional_apply, sum_over_range _ (by simp)]
  exact sum_congr rfl fun i _ => mul_comm _ _

/-! ### The projective moment bound for integer polynomials -/

open Classical in
/-- **Lemma 2.2 for integer polynomials.** Let `u ∈ ℤ[X]` have a coefficient prime to `p`,
let `ν : ℕ → ℚ` be moments with `∑_i u_i ν_{i+l} = 0` for `l < deg u`, and suppose that
`z(z+1) u'(z) V_u(z) = c` for some `c ∈ ℚ^×` at every root `z ∈ PadicAlgCl p` of `u`, where
`V_u = I_s((u(X) - u(s))/(X - s))`. If `v_p(ν_j) ≥ -L` for all nonzero `ν_j`, `j < 2 deg u`,
then every root `z` of `u` satisfies `∑_{w ≠ z} δ_p(z,w) ≤ v_p(c) + L`. -/
theorem integer_row_bound {u : ℤ[X]} {j₀ : ℕ} (hu : ¬ (p : ℤ) ∣ u.coeff j₀) {ν : ℕ → ℚ}
    (horth : ∀ l < u.natDegree,
      ∑ i ∈ range (u.natDegree + 1), (u.coeff i : ℚ) * ν (i + l) = 0)
    {c : ℚ} (hc : c ≠ 0)
    (hroot : ∀ z : K, aeval z (u.map (Int.castRingHom ℚ)) = 0 →
      z * (z + 1) * aeval z (derivative (u.map (Int.castRingHom ℚ))) *
        aeval z (momentQuotient ν (u.map (Int.castRingHom ℚ))) = (c : K))
    {L : ℕ} (hν : ∀ j < 2 * u.natDegree, ν j = 0 ∨ -(L : ℤ) ≤ padicValRat p (ν j))
    {z : K} (hz : z ∈ (u.map (Int.castRingHom K)).roots) :
    ∑ w ∈ (u.map (Int.castRingHom K)).roots.toFinset.erase z, projDist p z w ≤
      (padicValRat p c : ℝ) + L := by
  set H := u.map (Int.castRingHom ℤ_[p]) with hHdef
  have hH : H.IsPrimitive := isPrimitive_map_padicInt_of_not_dvd hu
  have hHK : H.map (algebraMap ℤ_[p] K) = u.map (Int.castRingHom K) := map_padicInt_map_eq u
  have hdeg : H.natDegree = u.natDegree := natDegree_map_eq_of_injective Int.cast_injective u
  set μ : ℕ → ℚ_[p] := fun j => (ν j : ℚ_[p]) with hμ
  have hcoeff : ∀ i, (H.coeff i : ℚ_[p]) = ((u.coeff i : ℤ) : ℚ_[p]) := by
    intro i
    rw [hHdef, coeff_map, eq_intCast, PadicInt.coe_intCast]
  have horth' : ∀ l < H.natDegree,
      ∑ i ∈ range (H.natDegree + 1), (H.coeff i : ℚ_[p]) * μ (i + l) = 0 := by
    intro l hl
    rw [hdeg] at hl ⊢
    have h := congrArg (fun q : ℚ => (q : ℚ_[p])) (horth l hl)
    simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast, Rat.cast_zero] at h
    simpa only [hcoeff, hμ] using h
  have hσ : (X ^ 2 + X : ℤ_[p][X]).natDegree = 2 := by compute_degree!
  have hσlc : IsUnit (X ^ 2 + X : ℤ_[p][X]).leadingCoeff := by
    rw [Monic.leadingCoeff (by monicity!)]
    exact isUnit_one
  have hc' : (c : ℚ_[p]) ≠ 0 := Rat.cast_ne_zero.mpr hc
  have hroot' : ∀ w ∈ (H.map (algebraMap ℤ_[p] K)).roots,
      aeval w (X ^ 2 + X : ℤ_[p][X]) * aeval w (derivative H) *
        aeval w (padicMomentQuotient H μ) = algebraMap ℚ_[p] K (c : ℚ_[p]) := by
    intro w hw
    rw [hHK] at hw
    have hu0 : u.map (Int.castRingHom K) ≠ 0 := by
      intro h0; rw [h0] at hw; simp at hw
    have hwr : (u.map (Int.castRingHom K)).eval w = 0 := (mem_roots hu0).mp hw
    have h := hroot w (by rw [aeval_map_intCast_rat]; exact hwr)
    have e1 : aeval w (derivative H) = aeval w (derivative (u.map (Int.castRingHom ℚ))) := by
      rw [aeval_def, aeval_def, eval₂_eq_eval_map, eval₂_eq_eval_map, ← derivative_map,
        ← derivative_map, hHK, Polynomial.map_map]
      congr 3
    have e2 : aeval w (padicMomentQuotient H μ) =
        aeval w (momentQuotient ν (u.map (Int.castRingHom ℚ))) := by
      rw [padicMomentQuotient_eq_momentQuotient, aeval_def, aeval_def, eval₂_eq_eval_map,
        eval₂_eq_eval_map, ← momentQuotient_map, ← momentQuotient_map, Polynomial.map_map,
        Polynomial.map_map, Polynomial.map_map]
      have h1 : ((algebraMap ℚ_[p] K).comp (algebraMap ℤ_[p] ℚ_[p])).comp
          (Int.castRingHom ℤ_[p]) = (algebraMap ℚ K).comp (Int.castRingHom ℚ) :=
        RingHom.ext_int _ _
      rw [h1]
      congr 2
    rw [e1, e2, map_ratCast, ← h]
    simp only [map_add, map_pow, aeval_X]
    ring
  have key := projective_row_bound hH horth' hσ hσlc hc' hroot' (by rw [hHK]; exact hz)
  rw [hHK, padicVal_ratCast hc] at key
  have hη : -(L : ℝ) ≤ minMomentVal p μ H.natDegree :=
    neg_le_minMomentVal (p := p) (ν := ν) (n := H.natDegree) (L := L) (by rw [hdeg]; exact hν)
  linarith

/-! ### Lemma 2.4 -/

/-- `P_n^{(a,b)}(2X+1)` as an integer polynomial:
`∑_{j ≤ n} binom(n+a, n-j) binom(n+a+b+j, j) X^j`. -/
noncomputable def integralJacobiShift (a b n : ℕ) : ℤ[X] :=
  ∑ j ∈ range (n + 1), C (((n + a).choose (n - j) * (n + a + b + j).choose j : ℕ) : ℤ) * X ^ j

theorem integralJacobiShift_eq (a b n : ℕ) : integralJacobiShift a b n =
    ∑ j ∈ range (n + 1), C (((n + a).choose (n - j) * (n + a + b + j).choose j : ℕ) : ℤ) *
      X ^ j := (rfl)

theorem map_integralJacobiShift (a b n : ℕ) :
    (integralJacobiShift a b n).map (Int.castRingHom ℚ) = (jacobiP a b n).comp (2 * X + 1) := by
  ext j
  rw [coeff_jacobiP_comp_two_mul_X_add_one, coeff_map, integralJacobiShift_eq, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow, Finset.sum_ite_eq, mem_range, Nat.lt_succ_iff]
  split_ifs with hj
  · rw [show ((n : ℚ) + a + b + j) = ((n + a + b + j : ℕ) : ℚ) by push_cast; ring,
      show ((n : ℚ) + a) = ((n + a : ℕ) : ℚ) by push_cast; ring,
      Ring.choose_natCast, Ring.choose_natCast]
    simp
  · simp

theorem natDegree_integralJacobiShift_le (a b n : ℕ) :
    (integralJacobiShift a b n).natDegree ≤ n := by
  rw [integralJacobiShift_eq]
  refine (natDegree_sum_le_of_forall_le _ _ fun j hj => ?_)
  refine (natDegree_C_mul_X_pow_le _ _).trans ?_
  exact Nat.lt_succ_iff.mp (mem_range.mp hj)

theorem integralJacobiShift_coeff_zero (a b n : ℕ) :
    (integralJacobiShift a b n).coeff 0 = ((n + a).choose n : ℤ) := by
  rw [integralJacobiShift_eq, finsetSum_coeff]
  simp

/-- `𝒞_n binom(n+a, a)² = -(n+a)! (n+b)! / (n! (n+a+b)!)`. -/
theorem integralWeightConstant_mul_choose_sq (a b n : ℕ) :
    integralWeightConstant a b n * ((n + a).choose a : ℚ) ^ 2 =
      -(((n + a).factorial * (n + b).factorial : ℚ) / (n.factorial * (n + a + b).factorial)) := by
  have hB := Nat.choose_mul_factorial_mul_factorial (n := n + a) (k := a) (by omega)
  rw [show n + a - a = n by omega] at hB
  have hBq : ((n + a).choose a : ℚ) * a.factorial * n.factorial = (n + a).factorial := by
    exact_mod_cast hB
  rw [integralWeightConstant_eq, ← hBq]
  have : (0 : ℚ) < (n + a + b).factorial := by positivity
  have : (0 : ℚ) < a.factorial := by positivity
  have : (0 : ℚ) < n.factorial := by positivity
  have : (0 : ℚ) < (n + a).choose a := by exact_mod_cast Nat.choose_pos (by omega)
  field_simp

open Classical in
/-- **Lemma 2.4, exact form.** Let `a, b ≥ 0`, `n ≥ 1`, `p` prime,
`Q = P_n^{(a,b)}(2X+1) / binom(n+a, a)`, `S = 2n + a + b + 1`, `L_p = ⌊log_p S⌋`, and let
`d_p = -min_j v_p([X^j] Q)` (the minimum over the nonzero coefficients). Then every root `α` of
`Q` in `PadicAlgCl p` satisfies `∑_{γ ≠ α} δ_p(α, γ) ≤ L_p + 2 d_p + v_p(𝒞_n)`, `𝒞_n` the
root constant of Lemma 2.3. The integer `d` below is `d_p`: it is characterized by the first two
conjuncts; moreover `d_p = v_p(binom(n+a,a)) - k` for some `k ≥ 0`. -/
theorem integralWeight_row_bound_exact (a b : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ d : ℤ, (∀ j, (integralWeightQ a b n).coeff j ≠ 0 →
        -d ≤ padicValRat p ((integralWeightQ a b n).coeff j)) ∧
      (∃ j, (integralWeightQ a b n).coeff j ≠ 0 ∧
        padicValRat p ((integralWeightQ a b n).coeff j) = -d) ∧
      (∀ z ∈ ((integralWeightQ a b n).map (algebraMap ℚ K)).roots,
        ∑ w ∈ ((integralWeightQ a b n).map (algebraMap ℚ K)).roots.toFinset.erase z,
            projDist p z w ≤
          (Nat.log p (2 * n + a + b + 1) : ℝ) + 2 * d +
            padicValRat p (integralWeightConstant a b n)) ∧
      ∃ k : ℕ, d = padicValRat p ((n + a).choose a : ℚ) - k := by
  set J := integralJacobiShift a b n with hJdef
  have hJ0 : J ≠ 0 := by
    intro h
    have := integralJacobiShift_coeff_zero a b n
    rw [← hJdef, h, coeff_zero] at this
    exact absurd this.symm (by exact_mod_cast (Nat.choose_pos (by omega)).ne')
  obtain ⟨k, u, hJu, j₀, hj₀⟩ := exists_eq_C_pow_mul_not_dvd hp.out hJ0
  set B : ℚ := ((n + a).choose a : ℚ) with hBdef
  have hB : B ≠ 0 := by rw [hBdef]; exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hpk : ((p : ℚ) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  set lam : ℚ := (p : ℚ) ^ k / B with hlam
  have hlam0 : lam ≠ 0 := div_ne_zero hpk hB
  set U := u.map (Int.castRingHom ℚ) with hU
  have hQ : integralWeightQ a b n = C lam * U := by
    rw [integralWeightQ_eq, ← map_integralJacobiShift, ← hJdef, hJu, Polynomial.map_mul,
      Polynomial.map_C, hU, ← mul_assoc, ← C_mul]
    congr 2
    simp [hlam, hBdef]
    ring
  have hUK : U.map (algebraMap ℚ K) = u.map (Int.castRingHom K) := by
    rw [hU, Polynomial.map_map]; congr 1
  have hlamK : (lam : K) ≠ 0 := by exact_mod_cast hlam0
  have hroots : ((integralWeightQ a b n).map (algebraMap ℚ K)).roots =
      (u.map (Int.castRingHom K)).roots := by
    rw [hQ, Polynomial.map_mul, Polynomial.map_C, hUK]
    exact roots_C_mul _ (by simpa using hlamK)
  have hcoeffQ : ∀ j, (integralWeightQ a b n).coeff j = lam * (u.coeff j : ℚ) := by
    intro j; rw [hQ, coeff_C_mul, hU, coeff_map, eq_intCast]
  have hplam : padicValRat p lam = k - padicValRat p B := by
    rw [hlam, padicValRat.div hpk hB, padicValRat.pow,
      padicValRat.self hp.out.one_lt]
    ring
  refine ⟨padicValRat p B - k, fun j hj => ?_, ⟨j₀, ?_, ?_⟩, fun z hz => ?_, k, rfl⟩
  · rw [hcoeffQ] at hj ⊢
    have hu : (u.coeff j : ℚ) ≠ 0 := right_ne_zero_of_mul hj
    rw [padicValRat.mul hlam0 hu, hplam, padicValRat.of_int]
    have : (0 : ℤ) ≤ padicValInt p (u.coeff j) := Int.natCast_nonneg _
    linarith
  · rw [hcoeffQ]
    refine mul_ne_zero hlam0 ?_
    intro h0
    exact hj₀ (by rw [show u.coeff j₀ = 0 by exact_mod_cast h0]; exact dvd_zero _)
  · have hu : (u.coeff j₀ : ℚ) ≠ 0 := fun h0 =>
      hj₀ (by rw [show u.coeff j₀ = 0 by exact_mod_cast h0]; exact dvd_zero _)
    rw [hcoeffQ, padicValRat.mul hlam0 hu, hplam, padicValRat.of_int,
      padicValInt.eq_zero_of_not_dvd hj₀]
    push_cast
    ring
  rw [hroots] at hz ⊢
  have hUdeg : U.natDegree = u.natDegree := natDegree_map_eq_of_injective Int.cast_injective u
  have hudeg : u.natDegree ≤ n := by
    have h1 : (integralWeightQ a b n).natDegree ≤ n := by
      rw [integralWeightQ_eq, ← map_integralJacobiShift]
      refine (natDegree_C_mul_le _ _).trans ?_
      exact (natDegree_map_le).trans (natDegree_integralJacobiShift_le a b n)
    rw [hQ, natDegree_C_mul hlam0, hUdeg] at h1
    exact h1
  -- orthogonality
  have horth : ∀ l < u.natDegree,
      ∑ i ∈ range (u.natDegree + 1), (u.coeff i : ℚ) * integralWeightMoment a b (i + l) = 0 := by
    intro l hl
    have h := integralWeightFunctional_X_pow_mul_Q a b (n := n) (j := l) (by omega)
    rw [hQ, integralWeightFunctional_eq, mul_left_comm, momentFunctional_C_mul,
      momentFunctional_X_pow_mul, hUdeg] at h
    have h' := (mul_eq_zero.mp h).resolve_left hlam0
    rw [← h']
    refine sum_congr rfl fun i _ => ?_
    rw [hU, coeff_map, eq_intCast]
  -- root identity
  set c : ℚ := integralWeightConstant a b n / lam ^ 2 with hc
  have hC0 : integralWeightConstant a b n ≠ 0 := by
    rw [integralWeightConstant_eq]
    have : (0 : ℚ) < (n + a + b).factorial := by positivity
    have : (0 : ℚ) < (n + a).factorial := by positivity
    have : (0 : ℚ) < a.factorial := by positivity
    have : (0 : ℚ) < n.factorial := by positivity
    have : (0 : ℚ) < (n + b).factorial := by positivity
    exact div_ne_zero (neg_ne_zero.mpr (by positivity)) (by positivity)
  have hc0 : c ≠ 0 := div_ne_zero hC0 (pow_ne_zero _ hlam0)
  have hroot : ∀ w : K, aeval w U = 0 →
      w * (w + 1) * aeval w (derivative U) *
        aeval w (momentQuotient (integralWeightMoment a b) U) = (c : K) := by
    intro w hw
    have hwQ : aeval w (integralWeightQ a b n) = 0 := by
      rw [hQ, map_mul, hw, mul_zero]
    have h := integralWeight_root_identity a b hn hwQ
    rw [integralWeightV_eq, hQ, momentQuotient_C_mul, derivative_C_mul] at h
    simp only [map_mul, aeval_C, eq_ratCast] at h
    rw [hc, Rat.cast_div, Rat.cast_pow, eq_div_iff (pow_ne_zero _ hlamK), ← h]
    ring
  -- moments
  have hν : ∀ j < 2 * u.natDegree, integralWeightMoment a b j = 0 ∨
      -((Nat.log p (2 * n + a + b + 1) : ℕ) : ℤ) ≤ padicValRat p (integralWeightMoment a b j) := by
    intro j hj
    right
    have h1 := neg_log_le_padicValRat_integralWeightMoment p a b j
    have h2 : Nat.log p (j + a + b + 1) ≤ Nat.log p (2 * n + a + b + 1) :=
      Nat.log_mono_right (by omega)
    omega
  have key := integer_row_bound hj₀ horth hc0 hroot hν hz
  have hval : padicValRat p c =
      padicValRat p (integralWeightConstant a b n) + 2 * (padicValRat p B - k) := by
    rw [hc, padicValRat.div hC0 (pow_ne_zero _ hlam0), padicValRat.pow, hplam]
    push_cast
    ring
  rw [hval] at key
  push_cast at key ⊢
  linarith

open Classical in
/-- **Lemma 2.4.** Let `a, b ≥ 0`, `n ≥ 1`, `p` prime,
`Q = P_n^{(a,b)}(2X+1) / binom(n+a, a)` and `S = 2n + a + b + 1`. Every root `α` of `Q` in
`PadicAlgCl p` satisfies
`∑_{γ ≠ α} δ_p(α, γ) ≤ ⌊log_p S⌋ + v_p((n+a)! (n+b)! / (n! (n+a+b)!))`.
The right side is `L_p + 2 v_p(B) + v_p(𝒞_n)`, which bounds `L_p + 2 d_p + v_p(𝒞_n)`; the
valuation of the factorial ratio may be negative. -/
theorem integralWeight_row_bound (a b : ℕ) {n : ℕ} (hn : 1 ≤ n) {z : K}
    (hz : z ∈ ((integralWeightQ a b n).map (algebraMap ℚ K)).roots) :
    ∑ w ∈ ((integralWeightQ a b n).map (algebraMap ℚ K)).roots.toFinset.erase z,
        projDist p z w ≤
      (Nat.log p (2 * n + a + b + 1) : ℝ) +
        padicValRat p (((n + a).factorial * (n + b).factorial : ℚ) /
          (n.factorial * (n + a + b).factorial)) := by
  obtain ⟨d, -, -, hrow, k, hdk⟩ := integralWeight_row_bound_exact (p := p) a b hn
  refine le_trans (hrow z hz) ?_
  have hB : ((n + a).choose a : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hC0 : integralWeightConstant a b n ≠ 0 := by
    intro h0
    have h := integralWeightConstant_mul_choose_sq a b n
    rw [h0, zero_mul] at h
    have : (0 : ℚ) < ((n + a).factorial * (n + b).factorial : ℚ) /
        (n.factorial * (n + a + b).factorial) := by positivity
    linarith
  have hid : padicValRat p (integralWeightConstant a b n) +
      2 * padicValRat p ((n + a).choose a : ℚ) =
      padicValRat p (((n + a).factorial * (n + b).factorial : ℚ) /
        (n.factorial * (n + a + b).factorial)) := by
    have h := congrArg (padicValRat p) (integralWeightConstant_mul_choose_sq a b n)
    rw [padicValRat.mul hC0 (pow_ne_zero _ hB), padicValRat.pow, padicValRat.neg] at h
    push_cast at h
    linarith
  have hk : (0 : ℤ) ≤ k := Int.natCast_nonneg k
  have hid' : ((padicValRat p (integralWeightConstant a b n) : ℤ) : ℝ) +
      2 * (padicValRat p ((n + a).choose a : ℚ) : ℝ) =
      (padicValRat p (((n + a).factorial * (n + b).factorial : ℚ) /
        (n.factorial * (n + a + b).factorial)) : ℝ) := by exact_mod_cast hid
  have hdk' : (d : ℝ) = (padicValRat p ((n + a).choose a : ℚ) : ℝ) - k := by exact_mod_cast hdk
  have hk' : (0 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

/-- The symmetric factorial ratio `A = (n+r)!² / (n! (n+2r)!)` of (2.11) and (3.12). -/
noncomputable def symmetricRatio (n r : ℕ) : ℚ :=
  ((n + r).factorial : ℚ) ^ 2 / (n.factorial * (n + 2 * r).factorial)

theorem symmetricRatio_eq (n r : ℕ) : symmetricRatio n r =
    ((n + r).factorial : ℚ) ^ 2 / (n.factorial * (n + 2 * r).factorial) := (rfl)

open Classical in
/-- **Lemma 2.4, symmetric case (2.11).** For `a = b = r`, every root `α` of
`Q = P_n^{(r,r)}(2X+1) / binom(n+r, r)` in `PadicAlgCl p` satisfies
`∑_{γ ≠ α} δ_p(α, γ) ≤ D_p = ⌊log_p S⌋ + v_p((n+r)!² / (n! (n+2r)!))`, `S = 2n + 2r + 1`,
with the signed valuation of the factorial ratio. -/
theorem integralWeight_row_bound_symmetric (r : ℕ) {n : ℕ} (hn : 1 ≤ n) {z : K}
    (hz : z ∈ ((integralWeightQ r r n).map (algebraMap ℚ K)).roots) :
    ∑ w ∈ ((integralWeightQ r r n).map (algebraMap ℚ K)).roots.toFinset.erase z,
        projDist p z w ≤
      (Nat.log p (2 * n + 2 * r + 1) : ℝ) + padicValRat p (symmetricRatio n r) := by
  have h := integralWeight_row_bound r r hn hz
  rw [show 2 * n + r + r + 1 = 2 * n + 2 * r + 1 by ring,
    show n + r + r = n + 2 * r by ring] at h
  rw [symmetricRatio_eq, sq]
  exact h

/-! ### Simplicity of the roots, the coarse bound and the resultant bound -/

/-- A nonzero polynomial over a field whose derivative does not vanish at its roots has simple
roots. -/
theorem roots_nodup_of_derivative_ne_zero {L : Type*} [Field L] {P : L[X]} (hP : P ≠ 0)
    (h : ∀ z, P.IsRoot z → (derivative P).eval z ≠ 0) : P.roots.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro z
  rw [count_roots]
  by_contra hlt
  push Not at hlt
  obtain ⟨h1, h2⟩ := (one_lt_rootMultiplicity_iff_isRoot hP).mp hlt
  exact h z h1 h2

theorem integralWeightQ_ne_zero (a b n : ℕ) : integralWeightQ a b n ≠ 0 := by
  intro h0
  have h := congrArg (fun q => q.coeff 0) h0
  simp only [integralWeightQ_eq, ← map_integralJacobiShift, coeff_C_mul, coeff_map,
    integralJacobiShift_coeff_zero, coeff_zero, eq_intCast] at h
  have hB : ((n + a).choose a : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hB' : (((n + a).choose n : ℤ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  exact mul_ne_zero (one_div_ne_zero hB) hB' h

/-- The roots of `Q` in any field of characteristic zero are simple (from the root identity of
Lemma 2.3, whose constant is nonzero). -/
theorem integralWeightQ_roots_nodup (a b : ℕ) {n : ℕ} (hn : 1 ≤ n) {L : Type*} [Field L]
    [CharZero L] : ((integralWeightQ a b n).map (algebraMap ℚ L)).roots.Nodup := by
  refine roots_nodup_of_derivative_ne_zero
    ((Polynomial.map_ne_zero_iff (algebraMap ℚ L).injective).mpr (integralWeightQ_ne_zero a b n))
    fun z hz h0 => ?_
  have hz' : aeval z (integralWeightQ a b n) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map]; exact hz
  have h0' : aeval z (derivative (integralWeightQ a b n)) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, ← derivative_map]; exact h0
  have h := integralWeight_root_identity a b hn hz'
  rw [h0', mul_zero, zero_mul] at h
  have hC0 : integralWeightConstant a b n ≠ 0 := by
    rw [integralWeightConstant_eq]
    have : (0 : ℚ) < (n + a + b).factorial := by positivity
    have : (0 : ℚ) < (n + a).factorial := by positivity
    have : (0 : ℚ) < a.factorial := by positivity
    have : (0 : ℚ) < n.factorial := by positivity
    have : (0 : ℚ) < (n + b).factorial := by positivity
    exact div_ne_zero (neg_ne_zero.mpr (by positivity)) (by positivity)
  exact hC0 (by exact_mod_cast h.symm)

/-- `T = ∏_{j=1}^{s} (n+j)` satisfies `n! T = (n+s)!`. -/
theorem factorial_mul_prod_Icc_add (n s : ℕ) :
    n.factorial * ∏ j ∈ Icc 1 s, (n + j) = (n + s).factorial := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ← mul_assoc, ih, show n + (s + 1) = (n + s) + 1 by
      ring, Nat.factorial_succ]
    ring

/-- `v_p((n+a)! (n+b)! / (n! (n+a+b)!)) ≤ v_p(T)`, `T = ∏_{j=1}^{a+b} (n+j)`. -/
theorem padicValRat_factorialRatio_le (p : ℕ) [Fact p.Prime] (a b n : ℕ) :
    padicValRat p (((n + a).factorial * (n + b).factorial : ℚ) /
        (n.factorial * (n + a + b).factorial)) ≤
      padicValNat p (∏ j ∈ Icc 1 (a + b), (n + j)) := by
  have hT := factorial_mul_prod_Icc_add n (a + b)
  have hT0 : ∏ j ∈ Icc 1 (a + b), (n + j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj => by simp only [mem_Icc] at hj; omega
  have hf : ∀ k : ℕ, ((k.factorial : ℕ) : ℚ) ≠ 0 := fun k => by
    exact_mod_cast (Nat.factorial_pos k).ne'
  have hval : ∀ k : ℕ, padicValRat p (k.factorial : ℚ) = padicValNat p k.factorial :=
    fun k => padicValRat.of_nat
  rw [padicValRat.div (mul_ne_zero (hf _) (hf _)) (mul_ne_zero (hf _) (hf _)),
    padicValRat.mul (hf _) (hf _), padicValRat.mul (hf _) (hf _), hval, hval, hval, hval]
  have hTv : padicValNat p (n + a + b).factorial =
      padicValNat p n.factorial + padicValNat p (∏ j ∈ Icc 1 (a + b), (n + j)) := by
    rw [show n + a + b = n + (a + b) by ring, ← hT,
      padicValNat.mul (Nat.factorial_pos n).ne' hT0]
  have hle : ∀ k, k ≤ n + a + b → padicValNat p k.factorial ≤ padicValNat p (n + a + b).factorial :=
    fun k hk => (padicValNat_dvd_iff_le (Nat.factorial_pos _).ne').mp
      (pow_padicValNat_dvd.trans (Nat.factorial_dvd_factorial hk))
  have h1 := hle (n + a) (by omega)
  have h2 := hle (n + b) (by omega)
  omega

open Classical in
/-- **Lemma 2.4, coarse bound (2.10).** Every root `α` of `Q` in `PadicAlgCl p` satisfies
`∑_{γ ≠ α} δ_p(α, γ) ≤ 𝒟_p = ⌊log_p S⌋ + v_p(T)`, `T = ∏_{j=1}^{a+b} (n+j)`. -/
theorem integralWeight_row_bound_coarse (a b : ℕ) {n : ℕ} (hn : 1 ≤ n) {z : K}
    (hz : z ∈ ((integralWeightQ a b n).map (algebraMap ℚ K)).roots) :
    ∑ w ∈ ((integralWeightQ a b n).map (algebraMap ℚ K)).roots.toFinset.erase z,
        projDist p z w ≤
      (Nat.log p (2 * n + a + b + 1) : ℝ) + padicValNat p (∏ j ∈ Icc 1 (a + b), (n + j)) := by
  have h := integralWeight_row_bound a b hn hz
  have h2 : (padicValRat p (((n + a).factorial * (n + b).factorial : ℚ) /
      (n.factorial * (n + a + b).factorial)) : ℝ) ≤
      (padicValNat p (∏ j ∈ Icc 1 (a + b), (n + j)) : ℝ) := by
    have h3 := Int.cast_le (R := ℝ).mpr (padicValRat_factorialRatio_le p a b n)
    rwa [Int.cast_natCast] at h3
  linarith

open Classical in
/-- **Lemma 2.4, resultant bound.** Let `A, B ∈ ℤ_[p][X]` be primitive (Gauss norm `1`) with
`A B` dividing `Q` over `PadicAlgCl p`, so that their root sets are disjoint sets of roots of
`Q`. If every root of `Q` has projective row sum at most `D`, then
`v_p(Res(A, B)) ≤ deg A · D`. -/
theorem integralWeight_resultant_le (a b : ℕ) {n : ℕ} (hn : 1 ≤ n) {A B : ℤ_[p][X]}
    (hA : A.IsPrimitive) (hB : B.IsPrimitive)
    (hAB : (A * B).map (algebraMap ℤ_[p] K) ∣ (integralWeightQ a b n).map (algebraMap ℚ K))
    {D : ℝ} (hD : ∀ z ∈ ((integralWeightQ a b n).map (algebraMap ℚ K)).roots,
      ∑ w ∈ ((integralWeightQ a b n).map (algebraMap ℚ K)).roots.toFinset.erase z,
        projDist p z w ≤ D) :
    padicVal p (resultant A B) ≤ A.natDegree * D := by
  classical
  set φ := algebraMap ℤ_[p] K with hφ
  set QK := (integralWeightQ a b n).map (algebraMap ℚ K) with hQK
  have hQ0 : QK ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ K).injective).mpr (integralWeightQ_ne_zero a b n)
  have hinj : Function.Injective φ := algebraMap_padicInt_injective
  have hAB0 : (A * B).map φ ≠ 0 := fun h => hQ0 (by rw [h] at hAB; exact zero_dvd_iff.mp hAB)
  have hroots : ((A * B).map φ).roots = (A.map φ).roots + (B.map φ).roots := by
    rw [Polynomial.map_mul] at hAB0 ⊢; exact roots_mul hAB0
  have hle : ((A * B).map φ).roots ≤ QK.roots := roots.le_of_dvd hQ0 hAB
  have hnodupQ : QK.roots.Nodup := integralWeightQ_roots_nodup a b hn
  have hnodup : ((A.map φ).roots + (B.map φ).roots).Nodup := by
    rw [← hroots]; exact Multiset.nodup_of_le hle hnodupQ
  obtain ⟨-, hBnd, hdisj⟩ := Multiset.nodup_add.mp hnodup
  have hdisj' : ∀ z ∈ (A.map φ).roots, ∀ w ∈ (B.map φ).roots, z ≠ w := by
    rintro z hz w hw rfl
    exact Multiset.disjoint_left.mp hdisj hz hw
  rw [padicVal_resultant_eq_sum_projDist hA hB hdisj']
  have hcardA : (A.map φ).roots.card = A.natDegree := by
    rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_map_eq_of_injective hinj]
  have hmemQ : ∀ x, x ∈ (A.map φ).roots ∨ x ∈ (B.map φ).roots → x ∈ QK.roots := by
    intro x hx
    refine Multiset.mem_of_le hle ?_
    rw [hroots]; exact Multiset.mem_add.mpr hx
  have hrow : ∀ z ∈ (A.map φ).roots,
      ((B.map φ).roots.map fun w => projDist p z w).sum ≤ D := by
    intro z hz
    refine le_trans ?_ (hD z (hmemQ z (Or.inl hz)))
    have e : ((B.map φ).roots.map fun w => projDist p z w).sum =
        ∑ w ∈ (B.map φ).roots.toFinset, projDist p z w := by
      rw [Finset.sum_eq_multiset_sum, Multiset.toFinset_val, hBnd.dedup]
    rw [e]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun w hw => ?_) fun w _ _ => projDist_nonneg z w
    have hw' := Multiset.mem_toFinset.mp hw
    exact Finset.mem_erase.mpr ⟨(hdisj' z hz w hw').symm,
      Multiset.mem_toFinset.mpr (hmemQ w (Or.inr hw'))⟩
  have hsum := Multiset.sum_le_card_nsmul
    ((A.map φ).roots.map fun z => ((B.map φ).roots.map fun w => projDist p z w).sum) D
    (fun x hx => by
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
      exact hrow z hz)
  rwa [Multiset.card_map, hcardA, nsmul_eq_mul] at hsum

end ArithmeticOfJacobiPolynomials
