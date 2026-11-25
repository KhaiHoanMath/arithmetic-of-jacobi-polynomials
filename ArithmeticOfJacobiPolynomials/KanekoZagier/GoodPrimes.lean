/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.KanekoZagier.CarryBudget
public import ArithmeticOfJacobiPolynomials.Padic.IntegralLocalBound
public import ArithmeticOfJacobiPolynomials.Polynomial.ResultantReduction
public import ArithmeticOfJacobiPolynomials.Jacobi.Wronskian
public import ArithmeticOfJacobiPolynomials.Jacobi.Endpoints
public import ArithmeticOfJacobiPolynomials.Jacobi.SourceStieltjesRational

/-!
# Lemma 4.4: the resultant at primes `p ≥ 5`

Let `λ, μ ∈ {-1,1}`, `n ≥ 1`, and let `H_n = A B` (`kzPrimitive l μ n = A * B`) with
`A, B ∈ ℤ[t]` (necessarily primitive). Then:
* `kz_padicValInt_resultant_le`: for every prime `p ≥ 5`, `v_p(Res(A,B)) ≤ deg A · E_p(n)`;
* `kz_padicValInt_resultant_eq_zero`: if `n ≥ 11` and `p > n` is prime, `v_p(Res(A,B)) = 0`.

The first part applies the projective moment bound (Lemma 2.2, `projective_resultant_bound`)
to `H_n` with `σ = t(1-t)`, the Jacobi moments and the constant `(κ_n/g_n)² C_n`, which comes
from the Wronskian identity (2.2); the moment budget is (4.3) of Lemma 4.2. The second part
applies Lemma 4.3 (`padicInt_not_dvd_resultant_of_ode`) to the image of `H_n` in `ℤ_p[t]`:
the endpoint values and the leading coefficient of `y_n` have valuation at most one.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

section Integer

variable {p : ℕ} [hp : Fact p.Prime]

local notation "K" => PadicAlgCl p

/-- If the nonzero rational moments `ν_j`, `j < 2n`, have valuation at least `L ∈ ℤ` and
`ν_0 ≠ 0`, then `η_p ≥ L`. -/
theorem le_minMomentVal_of_le {ν : ℕ → ℚ} {n : ℕ} (hn : 0 < n) (hν0 : ν 0 ≠ 0) {L : ℤ}
    (hν : ∀ j < 2 * n, ν j = 0 ∨ L ≤ padicValRat p (ν j)) :
    (L : ℝ) ≤ minMomentVal p (fun j => (ν j : ℚ_[p])) n := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (p : ℝ) ≠ 1 := ne_of_gt one_lt_prime_real
  have hnorm : ∀ j < 2 * n, ‖((ν j : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-L) := by
    intro j hj
    by_cases hj0 : ν j = 0
    · rw [hj0, Rat.cast_zero, norm_zero]; positivity
    · have hv := (hν j hj).resolve_left hj0
      rw [Padic.norm_eq_zpow_neg_valuation (Rat.cast_ne_zero.mpr hj0), Padic.valuation_ratCast]
      exact zpow_le_zpow_right₀ one_lt_prime_real.le (by omega)
  set s : NNReal := (range (2 * n)).sup fun j => ‖((ν j : ℚ) : ℚ_[p])‖₊ with hs
  have hsup : (s : ℝ) ≤ (p : ℝ) ^ (-L) := by
    have hpos : (0 : ℝ) ≤ (p : ℝ) ^ (-L) := by positivity
    have : s ≤ Real.toNNReal ((p : ℝ) ^ (-L)) := by
      refine Finset.sup_le fun j hj => ?_
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hpos]
      exact hnorm j (mem_range.mp hj)
    have h := NNReal.coe_le_coe.mpr this
    rwa [Real.coe_toNNReal _ hpos] at h
  have hspos : (0 : ℝ) < s := by
    have h1 : ‖((ν 0 : ℚ) : ℚ_[p])‖₊ ≤ s :=
      Finset.le_sup (f := fun j => ‖((ν j : ℚ) : ℚ_[p])‖₊) (mem_range.mpr (by omega))
    have h2 : (0 : ℝ) < ‖((ν 0 : ℚ) : ℚ_[p])‖ := norm_pos_iff.mpr (Rat.cast_ne_zero.mpr hν0)
    have h3 : (‖((ν 0 : ℚ) : ℚ_[p])‖₊ : ℝ) ≤ s := NNReal.coe_le_coe.mpr h1
    rw [coe_nnnorm] at h3
    linarith
  rw [minMomentVal_def]
  change (L : ℝ) ≤ -Real.logb p (s : ℝ)
  have hlog := Real.logb_le_logb_of_le (one_lt_prime_real (p := p)) hspos hsup
  rw [← Real.rpow_intCast, Real.logb_rpow hp0 hp1] at hlog
  push_cast at hlog
  linarith

open Classical in
/-- **Lemma 2.2 for integer polynomials, resultant form, `σ = t(1-t)`.** Let `u = A B ∈ ℤ[X]`
have a coefficient prime to `p` and positive degree, let `ν : ℕ → ℚ` (with `ν_0 ≠ 0`) satisfy
`∑_i u_i ν_{i+l} = 0` for `l < deg u`, and suppose that `z(1-z) u'(z) V_u(z) = c ∈ ℚ^×` at every
root `z ∈ PadicAlgCl p` of `u`, where `V_u = I_s((u(X) - u(s))/(X - s))`. If
`v_p(c) - v_p(ν_j) ≤ E` for every nonzero `ν_j`, `j < 2 deg u`, with `E ≥ 0`, then
`v_p(Res(A,B)) ≤ deg A · E`. -/
theorem integer_resultant_le_of_moments {u A B : ℤ[X]} {j₀ : ℕ}
    (hu : ¬ (p : ℤ) ∣ u.coeff j₀) (hAB : u = A * B) (hdeg : 0 < u.natDegree) {ν : ℕ → ℚ}
    (hν0 : ν 0 ≠ 0)
    (horth : ∀ l < u.natDegree,
      ∑ i ∈ range (u.natDegree + 1), (u.coeff i : ℚ) * ν (i + l) = 0)
    {c : ℚ} (hc : c ≠ 0)
    (hroot : ∀ z : K, aeval z (u.map (Int.castRingHom ℚ)) = 0 →
      z * (1 - z) * aeval z (derivative (u.map (Int.castRingHom ℚ))) *
        aeval z (momentQuotient ν (u.map (Int.castRingHom ℚ))) = (c : K))
    {E : ℤ} (hE : 0 ≤ E)
    (hν : ∀ j < 2 * u.natDegree, ν j = 0 ∨ padicValRat p c - E ≤ padicValRat p (ν j)) :
    (padicValInt p (resultant A B) : ℤ) ≤ A.natDegree * E := by
  by_cases hR : resultant A B = 0
  · rw [hR, padicValInt.zero, Nat.cast_zero]; exact mul_nonneg (Nat.cast_nonneg _) hE
  set H := u.map (Int.castRingHom ℤ_[p]) with hHdef
  have hH : H.IsPrimitive := isPrimitive_map_padicInt_of_not_dvd hu
  have hHK : H.map (algebraMap ℤ_[p] K) = u.map (Int.castRingHom K) := map_padicInt_map_eq u
  have hdeg' : H.natDegree = u.natDegree := natDegree_map_eq_of_injective Int.cast_injective u
  set μ : ℕ → ℚ_[p] := fun j => (ν j : ℚ_[p]) with hμ
  have hcoeff : ∀ i, (H.coeff i : ℚ_[p]) = ((u.coeff i : ℤ) : ℚ_[p]) := by
    intro i
    rw [hHdef, coeff_map, eq_intCast, PadicInt.coe_intCast]
  have horth' : ∀ l < H.natDegree,
      ∑ i ∈ range (H.natDegree + 1), (H.coeff i : ℚ_[p]) * μ (i + l) = 0 := by
    intro l hl
    rw [hdeg'] at hl ⊢
    have h := congrArg (fun q : ℚ => (q : ℚ_[p])) (horth l hl)
    simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast, Rat.cast_zero] at h
    simpa only [hcoeff, hμ] using h
  have hσ : (X * (1 - X) : ℤ_[p][X]).natDegree = 2 := by compute_degree!
  have hσlc : IsUnit (X * (1 - X) : ℤ_[p][X]).leadingCoeff := by
    have e : (X * (1 - X) : ℤ_[p][X]) = -(X ^ 2 - X) := by ring
    rw [e, leadingCoeff_neg, Monic.leadingCoeff (by monicity!)]
    exact isUnit_one.neg
  have hc' : (c : ℚ_[p]) ≠ 0 := Rat.cast_ne_zero.mpr hc
  have hroot' : ∀ w ∈ (H.map (algebraMap ℤ_[p] K)).roots,
      aeval w (X * (1 - X) : ℤ_[p][X]) * aeval w (derivative H) *
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
    rw [e1, e2, map_ratCast, ← h, map_mul, map_sub, map_one, aeval_X]
  have hAB' : H = A.map (Int.castRingHom ℤ_[p]) * B.map (Int.castRingHom ℤ_[p]) := by
    rw [hHdef, hAB, Polynomial.map_mul]
  have hA' : (A.map (Int.castRingHom ℤ_[p])).IsPrimitive :=
    isPrimitive_of_dvd hH ⟨_, hAB'⟩
  have hB' : (B.map (Int.castRingHom ℤ_[p])).IsPrimitive :=
    isPrimitive_of_dvd hH ⟨_, by rw [hAB', mul_comm]⟩
  have key := projective_resultant_bound hH horth' hσ hσlc hc' hroot' hAB' hA' hB'
  have hinj : Function.Injective (Int.castRingHom ℤ_[p]) := Int.cast_injective
  rw [padicVal_resultant_map_intCast hR, natDegree_map_eq_of_injective hinj,
    padicVal_ratCast hc] at key
  have hη : ((padicValRat p c - E : ℤ) : ℝ) ≤ minMomentVal p μ H.natDegree :=
    le_minMomentVal_of_le (ν := ν) (by rw [hdeg']; exact hdeg) hν0 (by rw [hdeg']; exact hν)
  have hA0 : (0 : ℝ) ≤ A.natDegree := Nat.cast_nonneg _
  push_cast at hη
  have h : ((padicValInt p (resultant A B) : ℤ) : ℝ) ≤ (A.natDegree : ℝ) * (E : ℝ) := by
    push_cast
    calc (padicValInt p (resultant A B) : ℝ) ≤ _ := key
      _ ≤ (A.natDegree : ℝ) * (E : ℝ) := mul_le_mul_of_nonneg_left (by linarith) hA0
  exact_mod_cast h

/-- An integer `z` with `g z = z' ≠ 0` and `v_p(z') ≤ 1` is not divisible by `p²`. -/
theorem not_sq_dvd_of_eq_mul {g z z' : ℤ} (hz : z' = g * z) (hz0 : z' ≠ 0)
    (hv : padicValRat p (z' : ℚ) ≤ 1) : ¬ (p : ℤ) ^ 2 ∣ z := by
  intro h
  have h' : (p : ℤ) ^ 2 ∣ z' := by rw [hz]; exact dvd_mul_of_dvd_right h g
  rw [padicValRat.of_int] at hv
  have := ((padicValInt_dvd_iff 2 z').mp h').resolve_left hz0
  omega

/-- A primitive integer polynomial has a coefficient prime to `p`. -/
theorem exists_coeff_not_dvd_of_isPrimitive {u : ℤ[X]} (hu : u.IsPrimitive) :
    ∃ j, ¬ (p : ℤ) ∣ u.coeff j := by
  by_contra! h
  have hC : C (p : ℤ) ∣ u := (C_dvd_iff_dvd_coeff _ _).mpr h
  have hunit := (isPrimitive_iff_isUnit_of_C_dvd.mp hu) _ hC
  rw [Int.isUnit_iff] at hunit
  rcases hunit with h1 | h1
  · exact hp.out.one_lt.ne' (by exact_mod_cast h1)
  · have : (0 : ℤ) ≤ p := Int.natCast_nonneg p
    omega

end Integer

/-! ### The Kaneko–Zagier data -/

theorem kz_alpha_gt {l : ℤ} (hl : l = 1 ∨ l = -1) : -1 < (l : ℚ) / 3 := by
  rcases hl with rfl | rfl <;> norm_num

theorem kz_beta_gt {μ : ℤ} (hμ : μ = 1 ∨ μ = -1) : -1 < (μ : ℚ) / 2 := by
  rcases hμ with rfl | rfl <;> norm_num

/-- `(κ_n / g_n) ≠ 0`. -/
theorem kzScale_ne_zero {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (n : ℕ) :
    (kzKappa n : ℚ) / kzContent l μ n ≠ 0 :=
  div_ne_zero (by exact_mod_cast (kzKappa_pos n).ne')
    (by exact_mod_cast (kzContent_pos hl hμ n).ne')

/-- Orthogonality of `H_n` against the Jacobi moments. -/
theorem kzPrimitive_orth {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (n : ℕ) :
    ∀ k < (kzPrimitive l μ n).natDegree,
      ∑ i ∈ range ((kzPrimitive l μ n).natDegree + 1),
        ((kzPrimitive l μ n).coeff i : ℚ) * jacobiMoment ((l : ℚ) / 3) ((μ : ℚ) / 2) (i + k) =
          0 := by
  intro k hk
  have h := momentFunctional_X_pow_mul (jacobiMoment ((l : ℚ) / 3) ((μ : ℚ) / 2)) k
    ((kzPrimitive l μ n).map (Int.castRingHom ℚ))
  rw [natDegree_map_eq_of_injective Int.cast_injective] at h
  simp only [coeff_map, eq_intCast] at h
  rw [← h, map_kzPrimitive hl hμ n, mul_left_comm, momentFunctional_C_mul,
    ← jacobiFunctional_eq, mul_comm (X ^ k),
    jacobiFunctional_jacobiShifted_mul_X_pow n (kz_alpha_gt hl) (kz_beta_gt hμ) k
      (by rwa [natDegree_kzPrimitive hl hμ] at hk), mul_zero]

/-- The root identity for `H_n`: `σ(z) H_n'(z) Q_{H_n}(z) = (κ_n/g_n)² C_n` at every root. -/
theorem kzPrimitive_root_identity {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    {n : ℕ} (hn : 1 ≤ n) {L : Type*} [Field L] [CharZero L] (z : L)
    (hz : aeval z ((kzPrimitive l μ n).map (Int.castRingHom ℚ)) = 0) :
    z * (1 - z) * aeval z (derivative ((kzPrimitive l μ n).map (Int.castRingHom ℚ))) *
        aeval z (momentQuotient (jacobiMoment ((l : ℚ) / 3) ((μ : ℚ) / 2))
          ((kzPrimitive l μ n).map (Int.castRingHom ℚ))) =
      ((((kzKappa n : ℚ) / kzContent l μ n) ^ 2 *
        jacobiWronskianConstant ((l : ℚ) / 3) ((μ : ℚ) / 2) n : ℚ) : L) := by
  set lam : ℚ := (kzKappa n : ℚ) / kzContent l μ n with hlam
  have hlam0 : (lam : L) ≠ 0 := by exact_mod_cast kzScale_ne_zero hl hμ n
  rw [map_kzPrimitive hl hμ n, ← hlam] at hz ⊢
  have hy0 : aeval z (jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n) = 0 := by
    rw [map_mul, aeval_C, eq_ratCast] at hz
    exact (mul_eq_zero.mp hz).resolve_left hlam0
  have hW := congrArg (aeval z) (jacobi_wronskian_source (kz_alpha_gt hl) (kz_beta_gt hμ) hn)
  simp only [map_add, map_mul, map_sub, map_pow, aeval_C, aeval_X, map_one] at hW
  rw [hy0] at hW
  rw [derivative_C_mul, momentQuotient_C_mul, map_mul, map_mul, aeval_C,
    ← jacobiSecondPoly_eq]
  simp only [eq_ratCast] at hW ⊢
  push_cast at hW ⊢
  linear_combination (lam : L) ^ 2 * hW

section Good

variable {p : ℕ} [hp : Fact p.Prime]

theorem padicValRat_kzKappa_of_five_le (hp5 : 5 ≤ p) (n : ℕ) :
    padicValRat p (kzKappa n : ℚ) = 0 := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  rw [padicValRat_kzKappa, padicValRat_two_eq, padicValRat_three_eq]
  simp [hp2, hp3]

theorem kzBudget_nonneg {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1) (hp5 : 5 ≤ p)
    (n : ℕ) : 0 ≤ kzBudget l μ n p := by
  rw [kzBudget_eq]
  exact sum_nonneg fun h hh => by
    rcases (kzLevelE_mem hl hμ hp5 (mem_Icc.mp hh).1 n).1 with h0 | h1 <;> omega

/-- **Lemma 4.4, (4.6)**: for `p ≥ 5` and every factorization
`H_n = A B` in `ℤ[t]`, `v_p(Res(A,B)) ≤ deg A · E_p(n)`. -/
theorem kz_padicValInt_resultant_le {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    {n : ℕ} (hn : 1 ≤ n) {A B : ℤ[X]} (hAB : kzPrimitive l μ n = A * B) (hp5 : 5 ≤ p) :
    (padicValInt p (resultant A B) : ℤ) ≤ A.natDegree * kzBudget l μ n p := by
  obtain ⟨j₀, hj₀⟩ := exists_coeff_not_dvd_of_isPrimitive (p := p) (isPrimitive_kzPrimitive hl hμ n)
  have hdeg := natDegree_kzPrimitive hl hμ n
  have hlam := kzScale_ne_zero hl hμ n
  have hC := (jacobiWronskianConstant_pos (kz_alpha_gt hl) (kz_beta_gt hμ) n).ne'
  refine integer_resultant_le_of_moments hj₀ hAB (by omega)
    (ν := jacobiMoment ((l : ℚ) / 3) ((μ : ℚ) / 2)) (by rw [jacobiMoment_zero]; exact one_ne_zero)
    (kzPrimitive_orth hl hμ n) (mul_ne_zero (pow_ne_zero 2 hlam) hC)
    (fun z hz => kzPrimitive_root_identity hl hμ hn z hz) (kzBudget_nonneg hl hμ hp5 n)
    (fun j hj => Or.inr ?_)
  rw [hdeg] at hj
  have hb := (kz_moment_content_budget hl hμ hp5 hn).1 j hj
  have hg : ((kzContent l μ n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (kzContent_pos hl hμ n).ne'
  have hk : ((kzKappa n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (kzKappa_pos n).ne'
  rw [padicValRat.mul (pow_ne_zero 2 hlam) hC, padicValRat.pow, padicValRat.div hk hg,
    padicValRat_kzKappa_of_five_le hp5]
  have hgv : padicValRat p (kzContent l μ n : ℚ) = padicValNat p (kzContent l μ n) :=
    padicValRat.of_nat
  push_cast
  linarith

/-! ### Primes `p > n` -/

theorem kz_div_add_le_div_add_one {X m q : ℕ} (hq : 0 < q) (hm : m < q) :
    (m + X) / q ≤ X / q + 1 := by
  rw [Nat.add_comm m X, add_div_eq_div_add hq]
  have : (X % q + m) / q < 2 :=
    Nat.div_lt_of_lt_mul (by have := Nat.mod_lt X hq; omega)
  omega

theorem kz_eval_one_eq {l μ : ℤ} (n : ℕ) :
    (jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n).eval 1 =
      (-1) ^ n * (kzNumB μ n / 2 ^ n) / (n.factorial : ℚ) := by
  rw [jacobiShifted_eq, eval_comp]
  have e : (1 - 2 * X : ℚ[X]).eval 1 = -1 := by norm_num
  rw [e, jacobiP_eval_neg_one, ring_choose_eq_ascPochhammer_div]
  have e2 : (n : ℚ) + (μ : ℚ) / 2 - (n : ℚ) + 1 = (μ : ℚ) / 2 + ((0 : ℕ) : ℚ) + 1 := by
    push_cast; ring
  rw [e2, ascPochhammer_eval_eq_prod_Ioc, zero_add,
    prod_Ioc_ratCast_div 2 (by norm_num) μ ((μ : ℚ) / 2) (by norm_num), kzNumB_eq]
  simp only [Nat.cast_ofNat, Nat.sub_zero]
  ring

/-- The valuation of `A_0 = ∏_{k ≤ n} (3k + λ)` is at most one when `p > n ≥ 1`. -/
theorem padicValRat_kzNumA_zero_le {l : ℤ} (hl : l = 1 ∨ l = -1) (hp5 : 5 ≤ p) {n : ℕ}
    (hpn : n < p) : padicValRat p (kzNumA l n 0) ≤ 1 := by
  have hpp : 3 * n + 1 < p ^ (1 + 1) := by
    calc 3 * n + 1 < 5 * p := by omega
      _ ≤ p * p := Nat.mul_le_mul_right p hp5
      _ = p ^ (1 + 1) := by ring
  rw [kzNumA_eq, padicValRat_prodA_eq_sum hl hp5 (Nat.zero_le n) hpp, Finset.Icc_self,
    sum_singleton, pow_one, zero_add]
  have := kz_div_add_le_div_add_one (X := kzResA l p) hp.out.pos hpn
  omega

theorem padicValRat_kzNumB_le {μ : ℤ} (hμ : μ = 1 ∨ μ = -1) (hp5 : 5 ≤ p) {n : ℕ}
    (hpn : n < p) : padicValRat p (kzNumB μ n) ≤ 1 := by
  have hpp : 2 * n + 1 < p ^ (1 + 1) := by
    calc 2 * n + 1 < 5 * p := by omega
      _ ≤ p * p := Nat.mul_le_mul_right p hp5
      _ = p ^ (1 + 1) := by ring
  rw [padicValRat_kzNumB_eq_sum hμ hp5 hpp, Finset.Icc_self, sum_singleton, pow_one, zero_add]
  have := kz_div_add_le_div_add_one (X := kzResB μ p) hp.out.pos hpn
  omega

theorem padicValRat_kzNumC_self_le {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    (hp5 : 5 ≤ p) {n : ℕ} (hpn : n < p) (hpn2 : 12 * n + 5 < p ^ 2) :
    padicValRat p (kzNumC l μ n n) ≤ 1 := by
  rw [padicValRat_kzNumC_eq_sum hl hμ hp5 le_rfl (H := 1) hpn2, Finset.Icc_self,
    sum_singleton, pow_one, zero_add]
  have := kz_div_add_le_div_add_one (X := n + kzResA l p + kzResB μ p) hp.out.pos hpn
  omega

theorem padicValRat_factorial_eq_zero_of_lt {m : ℕ} (hm : m < p) :
    padicValRat p (m.factorial : ℚ) = 0 := by
  rw [padicValRat_factorial_eq_sum (m := m) (H := 0) (by rwa [zero_add, pow_one]),
    Finset.Icc_eq_empty (by omega), sum_empty]

/-- **Lemma 4.4, large primes**: if `n ≥ 11` and `p > n` is
prime, then `v_p(Res(A,B)) = 0` for every factorization `H_n = A B` in `ℤ[t]`. -/
theorem kz_padicValInt_resultant_eq_zero {l μ : ℤ} (hl : l = 1 ∨ l = -1) (hμ : μ = 1 ∨ μ = -1)
    {n : ℕ} (hn : 11 ≤ n) {A B : ℤ[X]} (hAB : kzPrimitive l μ n = A * B) (hpn : n < p) :
    padicValInt p (resultant A B) = 0 := by
  have hp5 : 5 ≤ p := by omega
  have hpn2 : 12 * n + 5 < p ^ 2 := by
    have h1 : (n + 1) * (n + 1) ≤ p * p := Nat.mul_le_mul hpn hpn
    have h2 : 11 * n ≤ n * n := Nat.mul_le_mul_right n hn
    nlinarith
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hinjφ : Function.Injective (algebraMap ℤ_[p] ℚ_[p]) :=
    IsFractionRing.injective ℤ_[p] ℚ_[p]
  have hinj : Function.Injective (Int.castRingHom ℤ_[p]) := Int.cast_injective
  obtain ⟨H, hH⟩ : ∃ H : ℤ_[p][X], H = (kzPrimitive l μ n).map (Int.castRingHom ℤ_[p]) :=
    ⟨_, rfl⟩
  have hprim : H.IsPrimitive := by
    obtain ⟨j₀, hj₀⟩ := exists_coeff_not_dvd_of_isPrimitive (p := p)
      (isPrimitive_kzPrimitive hl hμ n)
    rw [hH]
    exact isPrimitive_map_padicInt_of_not_dvd hj₀
  have hdeg : H.natDegree < p := by
    rw [hH, natDegree_map_eq_of_injective hinj, natDegree_kzPrimitive hl hμ n]
    exact hpn
  -- the unit `1/6`
  have h6 : IsUnit ((6 : ℤ) : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun hlt => not_dvd_six hp5 ?_)
    have := (PadicInt.norm_int_lt_one_iff_dvd _).mp hlt
    exact_mod_cast this
  obtain ⟨w, hw⟩ := h6.exists_right_inv
  have hw' : (6 : ℚ_[p]) * algebraMap ℤ_[p] ℚ_[p] w = 1 := by
    have := congrArg (algebraMap ℤ_[p] ℚ_[p]) hw
    rw [map_mul, map_intCast, map_one] at this
    exact_mod_cast this
  -- the differential equation over `ℤ_p`
  have hHq : H.map (algebraMap ℤ_[p] ℚ_[p]) =
      C (algebraMap ℚ ℚ_[p] ((kzKappa n : ℚ) / kzContent l μ n)) *
        (jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n).map (algebraMap ℚ ℚ_[p]) := by
    rw [hH, Polynomial.map_map,
      show (algebraMap ℤ_[p] ℚ_[p]).comp (Int.castRingHom ℤ_[p]) =
        (algebraMap ℚ ℚ_[p]).comp (Int.castRingHom ℚ) from RingHom.ext_int _ _,
      ← Polynomial.map_map, map_kzPrimitive hl hμ n, Polynomial.map_mul, Polynomial.map_C]
  have e1 : algebraMap ℤ_[p] ℚ_[p] (w * (2 * (l : ℤ_[p]) + 6)) =
      algebraMap ℚ ℚ_[p] ((l : ℚ) / 3 + 1) := by
    simp only [map_mul, map_add, map_intCast, map_ofNat, map_div₀, map_one]
    linear_combination ((2 * (l : ℚ_[p]) + 6) / 6) * hw'
  have e2 : algebraMap ℤ_[p] ℚ_[p] (w * (2 * (l : ℤ_[p]) + 3 * (μ : ℤ_[p]) + 12)) =
      algebraMap ℚ ℚ_[p] ((l : ℚ) / 3 + (μ : ℚ) / 2 + 2) := by
    simp only [map_mul, map_add, map_intCast, map_ofNat, map_div₀]
    linear_combination ((2 * (l : ℚ_[p]) + 3 * (μ : ℚ_[p]) + 12) / 6) * hw'
  have e3 : algebraMap ℤ_[p] ℚ_[p]
        (w * ((n : ℤ_[p]) * (6 * n + 2 * (l : ℤ_[p]) + 3 * (μ : ℤ_[p]) + 6))) =
      algebraMap ℚ ℚ_[p] ((n : ℚ) * (n + (l : ℚ) / 3 + (μ : ℚ) / 2 + 1)) := by
    simp only [map_mul, map_add, map_intCast, map_ofNat, map_div₀, map_one, map_natCast]
    linear_combination
      ((n : ℚ_[p]) * (6 * n + 2 * (l : ℚ_[p]) + 3 * (μ : ℚ_[p]) + 6) / 6) * hw'
  have hode : X * (1 - X) * derivative (derivative H) +
      (C (w * (2 * (l : ℤ_[p]) + 6)) -
        C (w * (2 * (l : ℤ_[p]) + 3 * (μ : ℤ_[p]) + 12)) * X) * derivative H +
      C (w * ((n : ℤ_[p]) * (6 * n + 2 * (l : ℤ_[p]) + 3 * (μ : ℤ_[p]) + 6))) * H = 0 := by
    apply Polynomial.map_injective (algebraMap ℤ_[p] ℚ_[p]) hinjφ
    have hy := congrArg (Polynomial.map (algebraMap ℚ ℚ_[p]))
      (jacobiShifted_ode ((l : ℚ) / 3) ((μ : ℚ) / 2) n)
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_one, Polynomial.map_C, ← derivative_map, Polynomial.map_zero] at hy ⊢
    rw [e1, e2, e3, hHq, derivative_C_mul, derivative_C_mul]
    linear_combination C (algebraMap ℚ ℚ_[p] ((kzKappa n : ℚ) / kzContent l μ n)) * hy
  -- endpoint and leading-coefficient valuations
  have hg : ∀ j, (kzScaled l μ n).coeff j =
      (kzContent l μ n : ℤ) * (kzPrimitive l μ n).coeff j := by
    intro j
    conv_lhs => rw [eq_C_content_mul_primPart (kzScaled l μ n)]
    rw [coeff_C_mul, kzContent_intCast, kzPrimitive_eq]
  have hy0 := padicValRat_kz_coeff hl hμ (Nat.zero_le n) p
  have hyn := padicValRat_kz_coeff hl hμ (le_refl n) p
  have hk0 := padicValRat_kzKappa_of_five_le hp5 n
  have hκ : (kzKappa n : ℚ) ≠ 0 := by exact_mod_cast (kzKappa_pos n).ne'
  have hv2 : padicValRat p 2 = 0 := by rw [padicValRat_two_eq]; simp [hp2]
  have hv3 : padicValRat p 3 = 0 := by rw [padicValRat_three_eq]; simp [hp3]
  have hv6 : padicValRat p 6 = 0 := by rw [padicValRat_six_eq, hv2, hv3, add_zero]
  have hf0 := padicValRat_factorial_eq_zero_of_lt (p := p) (m := 0) (by omega)
  have hfn := padicValRat_factorial_eq_zero_of_lt (p := p) (m := n) hpn
  have h0 : ¬ (p : ℤ_[p]) ^ 2 ∣ H.eval 0 := by
    rw [hH, eval_zero_map, eq_intCast, PadicInt.pow_p_dvd_int_iff, ← coeff_zero_eq_eval_zero]
    refine not_sq_dvd_of_eq_mul (hg 0) ?_ ?_
    · intro hz0
      have := coeff_kzScaled hl hμ n 0
      rw [hz0, Int.cast_zero] at this
      exact (mul_ne_zero hκ hy0.1) this.symm
    · have hC0 : kzNumC l μ n 0 = 1 := by rw [kzNumC_eq, Finset.Ioc_self, prod_empty]
      rw [coeff_kzScaled hl hμ, padicValRat.mul hκ hy0.1, hk0, hy0.2, Nat.sub_zero, hv3, hv6,
        hfn, hf0, hC0, padicValRat.one]
      have := padicValRat_kzNumA_zero_le hl hp5 hpn
      linarith
  have hB0 := (kzNumB_pos hμ n).ne'
  have hm1 : ((-1 : ℚ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2n : ((2 : ℚ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hnf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hy1 : (jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n).eval 1 ≠ 0 := by
    rw [kz_eval_one_eq]
    exact div_ne_zero (mul_ne_zero hm1 (div_ne_zero hB0 h2n)) hnf
  have h1 : ¬ (p : ℤ_[p]) ^ 2 ∣ H.eval 1 := by
    rw [hH, eval_one_map, eq_intCast, PadicInt.pow_p_dvd_int_iff]
    have hev : (kzScaled l μ n).eval 1 = (kzContent l μ n : ℤ) * (kzPrimitive l μ n).eval 1 := by
      conv_lhs => rw [eq_C_content_mul_primPart (kzScaled l μ n)]
      rw [eval_mul, eval_C, kzContent_intCast, kzPrimitive_eq]
    have hevq : (((kzScaled l μ n).eval 1 : ℤ) : ℚ) =
        (kzKappa n : ℚ) * (jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n).eval 1 := by
      have := congrArg (eval 1) (map_kzScaled hl hμ n)
      rwa [eval_one_map, eval_mul, eval_C, eq_intCast] at this
    refine not_sq_dvd_of_eq_mul hev ?_ ?_
    · intro hz0
      rw [hz0, Int.cast_zero] at hevq
      exact (mul_ne_zero hκ hy1) hevq.symm
    · rw [hevq, padicValRat.mul hκ hy1, hk0, kz_eval_one_eq,
        padicValRat.div (mul_ne_zero hm1 (div_ne_zero hB0 h2n)) hnf,
        padicValRat.mul hm1 (div_ne_zero hB0 h2n), padicValRat.div hB0 h2n, padicValRat.pow,
        padicValRat.pow, padicValRat.neg, padicValRat.one, hv2, hfn]
      have := padicValRat_kzNumB_le hμ hp5 hpn
      linarith
  have hlc : ¬ (p : ℤ_[p]) ^ 2 ∣ H.leadingCoeff := by
    rw [hH, leadingCoeff_map_of_injective hinj, eq_intCast, PadicInt.pow_p_dvd_int_iff]
    refine not_sq_dvd_of_eq_mul (leadingCoeff_kzScaled_eq l μ n) ?_ ?_
    · intro hz0
      rw [← coeff_natDegree, natDegree_kzScaled hl hμ n] at hz0
      have := coeff_kzScaled hl hμ n n
      rw [hz0, Int.cast_zero] at this
      exact (mul_ne_zero hκ hyn.1) this.symm
    · rw [← coeff_natDegree, natDegree_kzScaled hl hμ n, coeff_kzScaled hl hμ,
        padicValRat.mul hκ hyn.1, hk0, hyn.2, Nat.sub_self, hv3, hv6, hfn, hf0, kzNumA_self,
        padicValRat.one]
      have := padicValRat_kzNumC_self_le hl hμ hp5 hpn hpn2
      linarith
  have hAB' : H = A.map (Int.castRingHom ℤ_[p]) * B.map (Int.castRingHom ℤ_[p]) := by
    rw [hH, hAB, Polynomial.map_mul]
  have key := padicInt_not_dvd_resultant_of_ode p hprim hdeg hode h0 h1 hlc hAB'
  rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj,
    resultant_map_map, eq_intCast] at key
  have key' : ¬ (p : ℤ) ∣ resultant A B := by
    intro h
    apply key
    have := (PadicInt.pow_p_dvd_int_iff (p := p) 1 (resultant A B)).mpr (by rwa [pow_one])
    rwa [pow_one] at this
  exact padicValInt.eq_zero_of_not_dvd key'

end Good

end ArithmeticOfJacobiPolynomials
