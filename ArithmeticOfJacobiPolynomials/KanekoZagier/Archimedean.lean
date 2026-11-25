/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.KanekoZagier.BadPrimes
public import ArithmeticOfJacobiPolynomials.Polynomial.ResultantRoots
public import ArithmeticOfJacobiPolynomials.External
public import ArithmeticOfJacobiPolynomials.Jacobi.Endpoints
public import ArithmeticOfJacobiPolynomials.Jacobi.MonicEndpoint
public import ArithmeticOfJacobiPolynomials.Jacobi.SourceStieltjesRational
public import Mathlib.Analysis.MeanInequalities

/-!
# The archimedean comparison (Proposition 4.7)

* `arch_min`: the minimization in the proof of Proposition 4.7: for `0 ≤ 2k ≤ n` the function
  `(n-2k) log(e^U+e^V) + k(U+V) - n min(U,T₂) - n min(V,T₃)` is minimal at `(U,V) = (T₂,T₃)`;
* `exp_sum_log_div_add_le_one`: the Hölder (AM–GM) inequality
  `(∏ t_i)^{1/k} + (∏ (1-t_i))^{1/k} ≤ 1` for `t_i ∈ (0,1)`;
* `mul_log_exp_add_exp_le_log_leadingCoeff`: the endpoint bound (4.16)
  `a^{1/k} ≥ e^U + e^V` with `U = v_2(A(0)) log 2 / k`, `V = v_3(A(1)) log 3 / k`;
* `log_abs_resultant_ge`: the archimedean bound
  `R ≥ a^{n-2k} (γ c₀)^k k^{-k} 2^{2(k-1)^2}` from the resultant–derivative identity and the
  interval Vandermonde bound;
* `padicValInt_eval_zero_eq`, `padicValInt_eval_one_eq`: the endpoint valuations
  `D_{2,n} = v_2(H(0))`, `D_{3,n} = v_3(H(1))`;
* `kanekoZagier_arch_resultant`: Proposition 4.7, inequality (4.17).
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

/-! ### Real inequalities -/

section RealInequalities

theorem log_exp_add_exp_le_sub_add {T U V : ℝ} (hUT : U ≤ T) :
    Real.log (Real.exp T + Real.exp V) ≤ T - U + Real.log (Real.exp U + Real.exp V) := by
  have hpos : 0 < Real.exp U + Real.exp V := add_pos (Real.exp_pos _) (Real.exp_pos _)
  have hpos' : 0 < Real.exp T + Real.exp V := add_pos (Real.exp_pos _) (Real.exp_pos _)
  have h1 : Real.exp T + Real.exp V ≤ Real.exp (T - U) * (Real.exp U + Real.exp V) := by
    rw [mul_add, ← Real.exp_add, sub_add_cancel]
    have h1 : 1 ≤ Real.exp (T - U) := by linarith [Real.add_one_le_exp (T - U)]
    have hV := Real.exp_pos V
    nlinarith
  have := Real.log_le_log hpos' h1
  rwa [Real.log_mul (Real.exp_pos _).ne' hpos.ne', Real.log_exp] at this

theorem arch_min_step {n k T U V : ℝ} (hk : 0 ≤ k) (hnk : 2 * k ≤ n) :
    (n - 2 * k) * Real.log (Real.exp T + Real.exp V) + k * T - n * T ≤
      (n - 2 * k) * Real.log (Real.exp U + Real.exp V) + k * U - n * min U T := by
  rcases le_total U T with h | h
  · rw [min_eq_left h]
    have h1 := log_exp_add_exp_le_sub_add (V := V) h
    have h2 : (n - 2 * k) * Real.log (Real.exp T + Real.exp V) ≤
        (n - 2 * k) * (T - U + Real.log (Real.exp U + Real.exp V)) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    have h3 : 0 ≤ k * (T - U) := mul_nonneg hk (by linarith)
    nlinarith
  · rw [min_eq_right h]
    have hpos : 0 < Real.exp T + Real.exp V := add_pos (Real.exp_pos _) (Real.exp_pos _)
    have h1 : Real.log (Real.exp T + Real.exp V) ≤ Real.log (Real.exp U + Real.exp V) :=
      Real.log_le_log hpos (by linarith [Real.exp_le_exp.mpr h])
    have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ n - 2 * k)
    have h3 : k * T ≤ k * U := mul_le_mul_of_nonneg_left h hk
    linarith

/-- **The minimization of Proposition 4.7.** For `0 ≤ k` and `2k ≤ n`, the function
`(n-2k) log(e^U+e^V) + k(U+V) - n min(U,T₂) - n min(V,T₃)` attains its minimum at
`(U,V) = (T₂,T₃)`. The statement is the manuscript's. Instead of the sign of the derivative in `U`
(nonpositive below `T₂`, nonnegative above), the proof compares the values directly, separately in
`U` and in `V`, (`arch_min_step`): for `U ≤ T` through the elementary inequality
`log(e^T+e^V) ≤ T - U + log(e^U+e^V)` (`log_exp_add_exp_le_sub_add`), and for `U ≥ T` through the
monotonicity of `log(e^U+e^V)` in `U`. This is the same monotonicity as the derivative signs,
without differentiation. -/
theorem arch_min {n k T₂ T₃ U V : ℝ} (hk : 0 ≤ k) (hnk : 2 * k ≤ n) :
    (n - 2 * k) * Real.log (Real.exp T₂ + Real.exp T₃) - (n - k) * (T₂ + T₃) ≤
      (n - 2 * k) * Real.log (Real.exp U + Real.exp V) + k * (U + V) - n * min U T₂ -
        n * min V T₃ := by
  have h1 := arch_min_step (T := T₂) (U := U) (V := V) hk hnk
  have h2 := arch_min_step (T := T₃) (U := V) (V := T₂) hk hnk
  rw [add_comm (Real.exp T₃) (Real.exp T₂), add_comm (Real.exp V)] at h2
  linarith

/-- AM–GM: `(∏ s_i)^{1/k} ≤ (∑ s_i)/k`, written with logarithms. -/
theorem exp_sum_log_div_le {k : ℕ} (hk : 1 ≤ k) {s : Fin k → ℝ} (hs : ∀ i, 0 < s i) :
    Real.exp ((∑ i, Real.log (s i)) / k) ≤ (∑ i, s i) / k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hw : ∑ _i ∈ (univ : Finset (Fin k)), (1 : ℝ) / k = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_one_div_cancel hk0.ne'
  have h := Real.geom_mean_le_arith_mean_weighted (univ : Finset (Fin k)) (fun _ => (1 : ℝ) / k)
    s (fun _ _ => by positivity) hw (fun i _ => (hs i).le)
  have e1 : ∏ i, s i ^ ((1 : ℝ) / k) = Real.exp ((∑ i, Real.log (s i)) / k) := by
    rw [Finset.sum_div, Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Real.rpow_def_of_pos (hs i)]
    congr 1
    ring
  have e2 : ∑ i, (1 : ℝ) / k * s i = (∑ i, s i) / k := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [← e1, ← e2]
  exact h

/-- **Hölder's inequality of Proposition 4.7.** For `t_i ∈ (0,1)`,
`(∏ t_i)^{1/k} + (∏ (1-t_i))^{1/k} ≤ 1`. -/
theorem exp_sum_log_div_add_le_one {k : ℕ} (hk : 1 ≤ k) {t : Fin k → ℝ}
    (ht : ∀ i, 0 < t i ∧ t i < 1) :
    Real.exp ((∑ i, Real.log (t i)) / k) + Real.exp ((∑ i, Real.log (1 - t i)) / k) ≤ 1 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 := exp_sum_log_div_le hk (fun i => (ht i).1)
  have h2 := exp_sum_log_div_le (s := fun i => 1 - t i) hk (fun i => by linarith [(ht i).2])
  beta_reduce at h2
  have e : (∑ i, t i) / k + (∑ i, (1 - t i)) / k = 1 := by
    rw [← add_div, ← Finset.sum_add_distrib]
    have : ∑ i, (t i + (1 - t i)) = ∑ _i : Fin k, (1 : ℝ) :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      div_self hk0.ne']
  linarith

/-- `p^{v_p(z)} ≤ |z|` for a nonzero integer `z`. -/
theorem pow_padicValInt_le_abs (p : ℕ) [Fact p.Prime] {z : ℤ} (hz : z ≠ 0) :
    (p : ℝ) ^ padicValInt p z ≤ |(z : ℝ)| := by
  have h := Int.le_of_dvd (abs_pos.mpr hz) ((dvd_abs _ _).mpr (padicValInt_dvd (p := p) z))
  have h' : (((p : ℤ) ^ padicValInt p z : ℤ) : ℝ) ≤ ((|z| : ℤ) : ℝ) := Int.cast_le.mpr h
  push_cast at h'
  exact h'

end RealInequalities

/-! ### The endpoint bound (4.16) -/

section Endpoint

/-- **The endpoint bound (4.16).** If `A ∈ ℤ[X]` has leading coefficient `a`, degree `k ≥ 1`
and `A = a ∏ (X - t_i)` over `ℝ` with all `t_i ∈ (0,1)`, then
`k log(e^U + e^V) ≤ log |a|`, where `U = v_2(A(0)) log 2 / k` and `V = v_3(A(1)) log 3 / k`. -/
theorem mul_log_exp_add_exp_le_log_leadingCoeff {A : ℤ[X]} {k : ℕ} (hk : 1 ≤ k)
    {t : Fin k → ℝ}
    (hAt : A.map (Int.castRingHom ℝ) = C (A.leadingCoeff : ℝ) * ∏ j, (polyX - C (t j)))
    (ht : ∀ i, 0 < t i ∧ t i < 1) (hA0 : A ≠ 0) :
    (k : ℝ) * Real.log (Real.exp ((padicValInt 2 (A.eval 0) : ℝ) * Real.log 2 / k) +
      Real.exp ((padicValInt 3 (A.eval 1) : ℝ) * Real.log 3 / k)) ≤
        Real.log |(A.leadingCoeff : ℝ)| := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hu : (A.leadingCoeff : ℝ) ≠ 0 := by exact_mod_cast leadingCoeff_ne_zero.mpr hA0
  have hu' : 0 < |(A.leadingCoeff : ℝ)| := abs_pos.mpr hu
  have hev : ∀ x : ℝ, (A.map (Int.castRingHom ℝ)).eval x =
      (A.leadingCoeff : ℝ) * ∏ j, (x - t j) := by
    intro x
    rw [hAt, eval_mul, eval_C, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
  have hP0 : 0 < ∏ j, t j := Finset.prod_pos fun j _ => (ht j).1
  have hP1 : 0 < ∏ j, (1 - t j) := Finset.prod_pos fun j _ => by linarith [(ht j).2]
  have h0 : |((A.eval 0 : ℤ) : ℝ)| = |(A.leadingCoeff : ℝ)| * ∏ j, t j := by
    rw [← eq_intCast (Int.castRingHom ℝ), ← eval_zero_map, hev, abs_mul, Finset.abs_prod]
    congr 1
    exact Finset.prod_congr rfl fun j _ => by
      rw [zero_sub, abs_neg, abs_of_pos (ht j).1]
  have h1 : |((A.eval 1 : ℤ) : ℝ)| = |(A.leadingCoeff : ℝ)| * ∏ j, (1 - t j) := by
    rw [← eq_intCast (Int.castRingHom ℝ), ← eval_one_map, hev, abs_mul, Finset.abs_prod]
    congr 1
    exact Finset.prod_congr rfl fun j _ => abs_of_pos (by linarith [(ht j).2])
  have hz0 : A.eval 0 ≠ 0 := by
    intro h
    have : |((A.eval 0 : ℤ) : ℝ)| = 0 := by rw [h, Int.cast_zero, abs_zero]
    rw [h0] at this
    exact (mul_pos hu' hP0).ne' this
  have hz1 : A.eval 1 ≠ 0 := by
    intro h
    have : |((A.eval 1 : ℤ) : ℝ)| = 0 := by rw [h, Int.cast_zero, abs_zero]
    rw [h1] at this
    exact (mul_pos hu' hP1).ne' this
  -- logarithmic forms
  have hl0 : Real.log |((A.eval 0 : ℤ) : ℝ)| =
      Real.log |(A.leadingCoeff : ℝ)| + ∑ j, Real.log (t j) := by
    rw [h0, Real.log_mul hu'.ne' hP0.ne', Real.log_prod fun j _ => (ht j).1.ne']
  have hl1 : Real.log |((A.eval 1 : ℤ) : ℝ)| =
      Real.log |(A.leadingCoeff : ℝ)| + ∑ j, Real.log (1 - t j) := by
    rw [h1, Real.log_mul hu'.ne' hP1.ne',
      Real.log_prod fun j _ => (by linarith [(ht j).2] : (0 : ℝ) < 1 - t j).ne']
  have hv0 : (padicValInt 2 (A.eval 0) : ℝ) * Real.log 2 ≤ Real.log |((A.eval 0 : ℤ) : ℝ)| := by
    have := Real.log_le_log (by positivity) (pow_padicValInt_le_abs 2 hz0)
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have hv1 : (padicValInt 3 (A.eval 1) : ℝ) * Real.log 3 ≤ Real.log |((A.eval 1 : ℤ) : ℝ)| := by
    have := Real.log_le_log (by positivity) (pow_padicValInt_le_abs 3 hz1)
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  -- exponentiate
  set a := Real.log |(A.leadingCoeff : ℝ)| with ha
  have hU : Real.exp ((padicValInt 2 (A.eval 0) : ℝ) * Real.log 2 / k) ≤
      Real.exp (a / k) * Real.exp ((∑ j, Real.log (t j)) / k) := by
    rw [← Real.exp_add, ← add_div]
    exact Real.exp_le_exp.mpr ((div_le_div_iff_of_pos_right hk0).mpr (by linarith))
  have hV : Real.exp ((padicValInt 3 (A.eval 1) : ℝ) * Real.log 3 / k) ≤
      Real.exp (a / k) * Real.exp ((∑ j, Real.log (1 - t j)) / k) := by
    rw [← Real.exp_add, ← add_div]
    exact Real.exp_le_exp.mpr ((div_le_div_iff_of_pos_right hk0).mpr (by linarith))
  have hH := exp_sum_log_div_add_le_one hk ht
  have hsum : Real.exp ((padicValInt 2 (A.eval 0) : ℝ) * Real.log 2 / k) +
      Real.exp ((padicValInt 3 (A.eval 1) : ℝ) * Real.log 3 / k) ≤ Real.exp (a / k) := by
    have hea := Real.exp_pos (a / k)
    have := mul_le_mul_of_nonneg_left hH hea.le
    linarith
  have hlog := Real.log_le_log (by positivity) hsum
  rw [Real.log_exp] at hlog
  have := mul_le_mul_of_nonneg_left hlog hk0.le
  rwa [mul_div_cancel₀ _ hk0.ne'] at this

end Endpoint

/-! ### The archimedean resultant bound -/

section ResultantBound

/-- **The archimedean resultant bound of Proposition 4.7.** Let `y ∈ ℚ[X]` of degree `≤ n`
have `n` distinct real roots, all in `(0,1)`, with `|y'(t)| ≥ c₀ > 0` at each of them. Let
`γ > 0`, `H ∈ ℤ[X]` with `H = γ y`, and `H = AB` with `1 ≤ k = deg A` and `2k ≤ n`. Then
`A = a ∏ (X - t_i)` with all `t_i ∈ (0,1)`, `deg A + deg B = n`, `Res(A,B) ≠ 0`, and
`log |Res(A,B)| ≥ (n-2k) log |a| + k log(γ c₀) + 2(k-1)^2 log 2 - k log k`. -/
theorem log_abs_resultant_ge {y : ℚ[X]} {n : ℕ}
    (hcard : (y.map (algebraMap ℚ ℝ)).roots.card = n)
    (hnodup : (y.map (algebraMap ℚ ℝ)).roots.Nodup) (hdegy : y.natDegree ≤ n)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hder : ∀ t ∈ (y.map (algebraMap ℚ ℝ)).roots,
      c₀ ≤ |(derivative (y.map (algebraMap ℚ ℝ))).eval t| ∧ 0 < t ∧ t < 1)
    {γ : ℚ} (hγ : 0 < γ) {H A B : ℤ[X]} (hH : H.map (Int.castRingHom ℚ) = C γ * y)
    (hAB : H = A * B) {k : ℕ} (hkA' : A.natDegree = k) (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    ∃ t : Fin k → ℝ, (∀ i, 0 < t i ∧ t i < 1) ∧
      A.map (Int.castRingHom ℝ) = C (A.leadingCoeff : ℝ) * ∏ j, (polyX - C (t j)) ∧
      A ≠ 0 ∧ k + B.natDegree = n ∧ resultant A B ≠ 0 ∧
      ((n : ℝ) - 2 * k) * Real.log |(A.leadingCoeff : ℝ)| +
          k * Real.log (γ * c₀) + 2 * ((k : ℝ) - 1) ^ 2 * Real.log 2 -
            k * Real.log k ≤ Real.log |((resultant A B : ℤ) : ℝ)| := by
  classical
  have hkA : k = A.natDegree := hkA'.symm
  obtain ⟨e, heB⟩ : ∃ e, e = B.natDegree := ⟨_, rfl⟩
  obtain ⟨yr, hyr⟩ : ∃ yr, yr = y.map (algebraMap ℚ ℝ) := ⟨_, rfl⟩
  obtain ⟨Ar, hAr⟩ : ∃ Ar, Ar = A.map (Int.castRingHom ℝ) := ⟨_, rfl⟩
  obtain ⟨Br, hBr⟩ : ∃ Br, Br = B.map (Int.castRingHom ℝ) := ⟨_, rfl⟩
  rw [← hyr] at hcard hnodup hder
  have hinj : Function.Injective (Int.castRingHom ℝ) := Int.cast_injective
  have hγr : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hHr : Ar * Br = C (γ : ℝ) * yr := by
    have := congrArg (Polynomial.map (algebraMap ℚ ℝ)) hH
    simp only [Polynomial.map_map, Polynomial.map_mul, map_C] at this
    rw [show (algebraMap ℚ ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ from
        RingHom.ext_int _ _] at this
    rw [hAr, hBr, ← Polynomial.map_mul, ← hAB, this, hyr]
    rfl
  have hyr0 : yr ≠ 0 := by
    rintro rfl
    rw [roots_zero, Multiset.card_zero] at hcard
    omega
  have hyrdeg : yr.natDegree = n := by
    refine le_antisymm ?_ ?_
    · rw [hyr]
      exact natDegree_map_le.trans hdegy
    · rw [← hcard]
      exact card_roots' yr
  have hHr0 : Ar * Br ≠ 0 := by
    rw [hHr]
    exact mul_ne_zero (C_ne_zero.mpr hγr.ne') hyr0
  have hAr0 : Ar ≠ 0 := left_ne_zero_of_mul hHr0
  have hBr0 : Br ≠ 0 := right_ne_zero_of_mul hHr0
  have hA0 : A ≠ 0 := by rintro rfl; rw [Polynomial.map_zero] at hAr; exact hAr0 hAr
  have hArdeg : Ar.natDegree = k := by rw [hAr, natDegree_map_eq_of_injective hinj, hkA]
  have hBrdeg : Br.natDegree = e := by rw [hBr, natDegree_map_eq_of_injective hinj, heB]
  have hke : k + e = n := by
    have h1 := natDegree_mul hAr0 hBr0
    rw [hHr, natDegree_C_mul hγr.ne', hyrdeg, hArdeg, hBrdeg] at h1
    omega
  have hroots : Ar.roots + Br.roots = yr.roots := by
    rw [← roots_mul hHr0, hHr, roots_C_mul _ hγr.ne']
  have hAcard : Ar.roots.card = k := by
    have h1 := card_roots' Ar
    have h2 := card_roots' Br
    have h3 := congrArg Multiset.card hroots
    rw [Multiset.card_add, hcard] at h3
    rw [hArdeg] at h1
    rw [hBrdeg] at h2
    omega
  have hAle : Ar.roots ≤ yr.roots := by
    rw [← hroots]
    exact Multiset.le_add_right _ _
  have hAnd : Ar.roots.Nodup := Multiset.nodup_of_le hAle hnodup
  have hsub : ∀ x ∈ Ar.roots, x ∈ yr.roots := fun x hx => Multiset.mem_of_le hAle hx
  -- enumerate the roots of `A`
  have hs : Ar.roots.toFinset.card = k := by rw [Multiset.toFinset_card_of_nodup hAnd, hAcard]
  obtain ⟨t, ht⟩ : ∃ t : Fin k → ℝ, t = fun i => Ar.roots.toFinset.orderEmbOfFin hs i :=
    ⟨_, rfl⟩
  have htinj : Function.Injective t := by
    rw [ht]
    exact (Ar.roots.toFinset.orderEmbOfFin hs).injective
  have hmem : ∀ i, t i ∈ Ar.roots := fun i => by
    rw [ht]
    exact Multiset.mem_toFinset.mp (Finset.orderEmbOfFin_mem _ hs i)
  have hle : univ.val.map t ≤ Ar.roots := by
    refine (Multiset.le_iff_subset (Multiset.Nodup.map htinj univ.nodup)).mpr fun x hx => ?_
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hx
    exact hmem i
  have htroots : univ.val.map t = Ar.roots := by
    refine Multiset.eq_of_le_of_card_le hle ?_
    rw [Multiset.card_map, Finset.card_val, card_univ, Fintype.card_fin, hAcard]
  have hArlc : Ar.leadingCoeff = (A.leadingCoeff : ℝ) := by
    rw [hAr]
    exact leadingCoeff_map_of_injective hinj A
  have hAr_eq : Ar = C (A.leadingCoeff : ℝ) * ∏ j, (polyX - C (t j)) := by
    rw [prod_X_sub_C_eq_multiset, htroots, ← hArlc]
    exact (C_leadingCoeff_mul_prod_multiset_X_sub_C (hAcard.trans hArdeg.symm)).symm
  have ht01 : ∀ i, 0 < t i ∧ t i < 1 := fun i => (hder _ (hsub _ (hmem i))).2
  refine ⟨t, ht01, by rw [← hAr]; exact hAr_eq, hA0, by rw [← heB]; exact hke, ?_⟩
  -- the resultant identity
  have hu : (A.leadingCoeff : ℝ) ≠ 0 := by exact_mod_cast leadingCoeff_ne_zero.mpr hA0
  have hRr : resultant Ar Br = ((resultant A B : ℤ) : ℝ) := by
    have h1 : resultant Ar Br = resultant Ar Br A.natDegree B.natDegree := by
      rw [hAr, hBr, natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj]
    rw [h1, hAr, hBr, resultant_map_map]
    rfl
  have hke' : k ≤ Br.natDegree := by rw [hBrdeg]; omega
  have hid := abs_resultant_eq_div hu htinj Br hke'
  rw [← hAr_eq, hRr, hBrdeg, hHr] at hid
  simp only [derivative_C_mul, eval_mul, eval_C, abs_mul, abs_of_pos hγr] at hid
  set V := ∏ i, ∏ j ∈ univ.filter (fun j => i < j), (t i - t j) ^ 2 with hV_def
  have hVpos : 0 < V := by
    refine Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => ?_
    have hij : i ≠ j := (mem_filter.mp hj).2.ne
    exact lt_of_le_of_ne (sq_nonneg _)
      (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr (htinj.ne hij))))
  have hVle := intervalVandermondeBound k t fun i => ⟨(ht01 i).1.le, (ht01 i).2.le⟩
  have hprod : ((γ : ℝ) * c₀) ^ k ≤ ∏ i, ((γ : ℝ) * |(derivative yr).eval (t i)|) := by
    have : ∏ _i : Fin k, ((γ : ℝ) * c₀) = ((γ : ℝ) * c₀) ^ k := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← this]
    exact Finset.prod_le_prod₀ (fun i _ => (mul_pos hγr hc₀).le)
      (fun i _ => mul_le_mul_of_nonneg_left (hder _ (hsub _ (hmem i))).1 hγr.le)
  have hPpos : 0 < ∏ i, ((γ : ℝ) * |(derivative yr).eval (t i)|) :=
    lt_of_lt_of_le (pow_pos (mul_pos hγr hc₀) _) hprod
  have hupos : 0 < |(A.leadingCoeff : ℝ)| ^ (e - k) := pow_pos (abs_pos.mpr hu) _
  have hRpos : 0 < |((resultant A B : ℤ) : ℝ)| := by
    rw [hid]
    exact div_pos (mul_pos hupos hPpos) hVpos
  refine ⟨fun h => by rw [h, Int.cast_zero, abs_zero] at hRpos; exact lt_irrefl _ hRpos, ?_⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hlogR : Real.log |((resultant A B : ℤ) : ℝ)| =
      ((e - k : ℕ) : ℝ) * Real.log |(A.leadingCoeff : ℝ)| +
        Real.log (∏ i, ((γ : ℝ) * |(derivative yr).eval (t i)|)) - Real.log V := by
    rw [hid, Real.log_div (mul_pos hupos hPpos).ne' hVpos.ne',
      Real.log_mul hupos.ne' hPpos.ne', Real.log_pow]
  have hlogP : (k : ℝ) * Real.log ((γ : ℝ) * c₀) ≤
      Real.log (∏ i, ((γ : ℝ) * |(derivative yr).eval (t i)|)) := by
    have := Real.log_le_log (pow_pos (mul_pos hγr hc₀) _) hprod
    rwa [Real.log_pow] at this
  have hlogV : Real.log V ≤ (k : ℝ) * Real.log k - 2 * ((k : ℝ) - 1) ^ 2 * Real.log 2 := by
    have := Real.log_le_log hVpos hVle
    rw [Real.log_div (pow_pos hk0 _).ne' (by positivity), Real.log_pow, Real.log_pow] at this
    have hc : (((2 * (k - 1) ^ 2 : ℕ)) : ℝ) = 2 * ((k : ℝ) - 1) ^ 2 := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hk]
      norm_num
    rw [hc] at this
    exact this
  have hek : ((e - k : ℕ) : ℝ) = (n : ℝ) - 2 * k := by
    rw [Nat.cast_sub (by omega), ← hke]
    push_cast
    ring
  rw [hek] at hlogR
  linarith

end ResultantBound

/-! ### The Jacobi polynomial `y_n` -/

section JacobiInput

/-- The real zeros of `y_n = P_n^{(α,β)}(1-2t)` (from [DLMF, §18.2(vi)]). -/
theorem jacobiShifted_real_roots (hZ : JacobiSimpleRealZeros) {α β : ℚ} (hα : -1 < α)
    (hβ : -1 < β) (n : ℕ) :
    ((jacobiShifted α β n).map (algebraMap ℚ ℝ)).roots.Nodup ∧
      ((jacobiShifted α β n).map (algebraMap ℚ ℝ)).roots.card = n := by
  obtain ⟨hnd, hcard, -⟩ := hZ.rat α β hα hβ n
  have hL : (C (-2) * polyX + C 1 : ℝ[X]) = 1 - 2 * polyX := by
    rw [C_neg, map_ofNat C 2, C_1]
    ring
  have e : (jacobiShifted α β n).map (algebraMap ℚ ℝ) =
      ((jacobiP α β n).map (algebraMap ℚ ℝ)).comp (C (-2) * polyX + C 1) := by
    rw [jacobiShifted_eq, Polynomial.map_comp, hL]
    simp
  have hu : IsUnit (-2 : ℝ) := IsUnit.mk0 _ (by norm_num)
  have hm := map_roots_comp_C_mul_X_add_C ((jacobiP α β n).map (algebraMap ℚ ℝ)) (-2) 1 hu
  rw [e]
  refine ⟨Multiset.Nodup.of_map (fun x => -2 * x + 1) (by rw [hm]; exact hnd), ?_⟩
  rw [← Multiset.card_map (fun x => -2 * x + 1), hm, hcard]

/-- Lemma 2.1 at the real roots of `y_n`, in the form used by `log_abs_resultant_ge`. -/
theorem jacobiShifted_root_derivative {α β : ℚ} (hα : -1 < α) (hβ : -1 < β) {n : ℕ}
    (hn : 1 ≤ n) :
    ∀ t ∈ ((jacobiShifted α β n).map (algebraMap ℚ ℝ)).roots,
      2 * Real.sqrt (jacobiWronskianConstant α β n) ≤
        |(derivative ((jacobiShifted α β n).map (algebraMap ℚ ℝ))).eval t| ∧ 0 < t ∧ t < 1 := by
  intro t ht
  have h0 : aeval t (jacobiShifted α β n) = 0 := by
    rw [← eval_map_algebraMap]
    exact (mem_roots'.mp ht).2
  rw [derivative_map, eval_map_algebraMap]
  exact jacobi_root_derivative_lower_source hα hβ hn h0

theorem jacobiShifted_eval_zero (α β : ℚ) (n : ℕ) :
    (jacobiShifted α β n).eval 0 = (ascPochhammer ℚ n).eval (α + 1) / n.factorial := by
  rw [jacobiShifted_eq, eval_comp]
  simp only [eval_sub, eval_one, eval_mul, eval_X, mul_zero, sub_zero]
  rw [jacobiP_eval_one, ring_choose_eq_ascPochhammer_div,
    show (n : ℚ) + α - n + 1 = α + 1 by ring]

theorem jacobiShifted_eval_one (α β : ℚ) (n : ℕ) :
    (jacobiShifted α β n).eval 1 =
      (-1) ^ n * ((ascPochhammer ℚ n).eval (β + 1) / n.factorial) := by
  rw [jacobiShifted_eq, eval_comp]
  have h : (1 - 2 * polyX : ℚ[X]).eval 1 = -1 := by norm_num
  rw [h, jacobiP_eval_neg_one, ring_choose_eq_ascPochhammer_div,
    show (n : ℚ) + β - n + 1 = β + 1 by ring]

/-- `v_p((m/q + 1)_n) = ∑_{j=1}^n v_p(qj + m)` for `p ∤ q`. -/
theorem padicValRat_ascPochhammer_int_div {p q : ℕ} [Fact p.Prime] (hq : 0 < q)
    (hpq : ¬ p ∣ q) {m : ℤ} (hm : ∀ j : ℕ, 1 ≤ j → (q : ℤ) * j + m ≠ 0) (n : ℕ) :
    (ascPochhammer ℚ n).eval ((m : ℚ) / q + 1) ≠ 0 ∧
      padicValRat p ((ascPochhammer ℚ n).eval ((m : ℚ) / q + 1)) =
        ∑ j ∈ Finset.Icc 1 n, (padicValInt p ((q : ℤ) * j + m) : ℤ) := by
  induction n with
  | zero =>
    rw [Finset.Icc_eq_empty (by norm_num), Finset.sum_empty]
    simp
  | succ n ih =>
    obtain ⟨h0, hv⟩ := ih
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
    have hz : (q : ℤ) * ((n + 1 : ℕ) : ℤ) + m ≠ 0 := hm (n + 1) (by omega)
    have hz' : ((((q : ℤ) * ((n + 1 : ℕ) : ℤ) + m : ℤ)) : ℚ) ≠ 0 := by exact_mod_cast hz
    have e : (m : ℚ) / q + 1 + n = ((((q : ℤ) * ((n + 1 : ℕ) : ℤ) + m : ℤ)) : ℚ) / q := by
      rw [eq_div_iff hq0, add_mul, add_mul, div_mul_cancel₀ _ hq0]
      push_cast
      ring
    rw [ascPochhammer_succ_eval, e]
    refine ⟨mul_ne_zero h0 (div_ne_zero hz' hq0), ?_⟩
    rw [padicValRat.mul h0 (div_ne_zero hz' hq0), padicValRat.div hz' hq0, hv,
      padicValRat.of_int, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hpq,
      Finset.sum_Icc_succ_top (by omega), Nat.cast_zero, sub_zero]

/-- **The endpoint valuation at `2`.** If `H = γ y_n` with `v_2(γ) = n + v_2(n!)`, then
`v_2(H(0)) = D_{2,n} = n + ∑_{j=1}^n v_2(3j+λ)`, and `H(0) ≠ 0`. -/
theorem padicValInt_eval_zero_eq {l μ : ℤ} (hl : l = 1 ∨ l = -1) {n : ℕ} {γ : ℚ} (hγ : γ ≠ 0)
    (hγ2 : padicValRat 2 γ = n + padicValNat 2 n.factorial) {H : ℤ[X]}
    (hH : H.map (Int.castRingHom ℚ) = C γ * jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n) :
    H.eval 0 ≠ 0 ∧
      (padicValInt 2 (H.eval 0) : ℤ) =
        n + ∑ j ∈ Finset.Icc 1 n, (padicValInt 2 (3 * j + l) : ℤ) := by
  have hP := padicValRat_ascPochhammer_int_div (p := 2) (q := 3) (by norm_num) (by norm_num)
    (m := l) (fun j hj => by rcases hl with rfl | rfl <;> omega) n
  simp only [Nat.cast_ofNat] at hP
  obtain ⟨hP0, hPv⟩ := hP
  have hf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hH0 : ((H.eval 0 : ℤ) : ℚ) = γ * ((ascPochhammer ℚ n).eval ((l : ℚ) / 3 + 1) /
      n.factorial) := by
    have := congrArg (eval 0) hH
    rwa [eval_zero_map, eq_intCast, eval_mul, eval_C, jacobiShifted_eval_zero] at this
  have hne : ((H.eval 0 : ℤ) : ℚ) ≠ 0 := by
    rw [hH0]
    exact mul_ne_zero hγ (div_ne_zero hP0 hf)
  refine ⟨by exact_mod_cast hne, ?_⟩
  rw [← padicValRat.of_int, hH0, padicValRat.mul hγ (div_ne_zero hP0 hf),
    padicValRat.div hP0 hf, hγ2, hPv, padicValRat.of_nat]
  ring

/-- **The endpoint valuation at `3`.** If `H = γ y_n` with `v_3(γ) = n + v_3(n!)`, then
`v_3(H(1)) = D_{3,n} = n + ∑_{j=1}^n v_3(2j+μ)`, and `H(1) ≠ 0`. -/
theorem padicValInt_eval_one_eq {l μ : ℤ} (hμ : μ = 1 ∨ μ = -1) {n : ℕ} {γ : ℚ} (hγ : γ ≠ 0)
    (hγ3 : padicValRat 3 γ = n + padicValNat 3 n.factorial) {H : ℤ[X]}
    (hH : H.map (Int.castRingHom ℚ) = C γ * jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n) :
    H.eval 1 ≠ 0 ∧
      (padicValInt 3 (H.eval 1) : ℤ) =
        n + ∑ j ∈ Finset.Icc 1 n, (padicValInt 3 (2 * j + μ) : ℤ) := by
  have hP := padicValRat_ascPochhammer_int_div (p := 3) (q := 2) (by norm_num) (by norm_num)
    (m := μ) (fun j hj => by rcases hμ with rfl | rfl <;> omega) n
  simp only [Nat.cast_ofNat] at hP
  obtain ⟨hP0, hPv⟩ := hP
  have hf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hs : ((-1 : ℚ)) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hH1 : ((H.eval 1 : ℤ) : ℚ) =
      γ * ((-1) ^ n * ((ascPochhammer ℚ n).eval ((μ : ℚ) / 2 + 1) / n.factorial)) := by
    have := congrArg (eval 1) hH
    rwa [eval_one_map, eq_intCast, eval_mul, eval_C, jacobiShifted_eval_one] at this
  have hne : ((H.eval 1 : ℤ) : ℚ) ≠ 0 := by
    rw [hH1]
    exact mul_ne_zero hγ (mul_ne_zero hs (div_ne_zero hP0 hf))
  refine ⟨by exact_mod_cast hne, ?_⟩
  have hv1 : padicValRat 3 ((-1 : ℚ) ^ n) = 0 := by
    rw [padicValRat.pow, padicValRat.neg, padicValRat.one, mul_zero]
  rw [← padicValRat.of_int, hH1, padicValRat.mul hγ (mul_ne_zero hs (div_ne_zero hP0 hf)),
    padicValRat.mul hs (div_ne_zero hP0 hf), hv1, padicValRat.div hP0 hf, hγ3, hPv,
    padicValRat.of_nat]
  ring

end JacobiInput

/-! ### Proposition 4.7 -/

section Proposition47

/-- The combination of the archimedean, endpoint and local bounds in the proof of
Proposition 4.7 (pure real arithmetic). Here `a₂ = v_2(A(0))`, `b₂ = v_2(B(0))`,
`a₃ = v_3(A(1))`, `b₃ = v_3(B(1))`, `v₂ = v_2(R)`, `v₃ = v_3(R)`. -/
theorem arch_combine {n k e a₂ b₂ a₃ b₃ s₂ s₃ u R v₂ v₃ G T₂ T₃ : ℝ} (hk : 0 < k)
    (hkn : 2 * k ≤ n) (hke : k + e = n)
    (hT₂ : T₂ = (a₂ + b₂) * Real.log 2 / n) (hT₃ : T₃ = (a₃ + b₃) * Real.log 3 / n)
    (hR : (n - 2 * k) * u + k * G ≤ R)
    (hu : k * Real.log (Real.exp (a₂ * Real.log 2 / k) + Real.exp (a₃ * Real.log 3 / k)) ≤ u)
    (h₂ : v₂ ≤ min (e * a₂) (k * b₂) + k * e / 2 + k / 2 * s₂)
    (h₃ : v₃ ≤ min (e * a₃) (k * b₃) + k * e / 3 + k / 6 * s₃) :
    G - (s₂ * Real.log 2 / 2 + s₃ * Real.log 3 / 6) +
        (n - 2 * k) * Real.log (Real.exp T₂ + Real.exp T₃) -
        (n - k) * (T₂ + T₃ + (Real.log 2 / 2 + Real.log 3 / 3)) ≤
      (R - v₂ * Real.log 2 - v₃ * Real.log 3) / k := by
  have hn : 0 < n := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  obtain ⟨U, hU⟩ : ∃ U, U = a₂ * Real.log 2 / k := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, V = a₃ * Real.log 3 / k := ⟨_, rfl⟩
  rw [← hU, ← hV] at hu
  have hkU : k * U = a₂ * Real.log 2 := by rw [hU, mul_div_cancel₀ _ hk.ne']
  have hkV : k * V = a₃ * Real.log 3 := by rw [hV, mul_div_cancel₀ _ hk.ne']
  have hnT₂ : n * T₂ = (a₂ + b₂) * Real.log 2 := by rw [hT₂, mul_div_cancel₀ _ hn.ne']
  have hnT₃ : n * T₃ = (a₃ + b₃) * Real.log 3 := by rw [hT₃, mul_div_cancel₀ _ hn.ne']
  have hM₂ : min (e * a₂) (k * b₂) * Real.log 2 ≤ k * (n * min U T₂ - k * U) := by
    rcases le_total U T₂ with h | h
    · rw [min_eq_left h]
      have := mul_le_mul_of_nonneg_right (min_le_left (e * a₂) (k * b₂)) hl2.le
      have e1 : k * (n * U - k * U) = e * (a₂ * Real.log 2) := by
        rw [← hkU, ← hke]
        ring
      linarith
    · rw [min_eq_right h]
      have := mul_le_mul_of_nonneg_right (min_le_right (e * a₂) (k * b₂)) hl2.le
      have e1 : k * (n * T₂ - k * U) = k * (b₂ * Real.log 2) := by
        rw [hnT₂, hkU]
        ring
      linarith
  have hM₃ : min (e * a₃) (k * b₃) * Real.log 3 ≤ k * (n * min V T₃ - k * V) := by
    rcases le_total V T₃ with h | h
    · rw [min_eq_left h]
      have := mul_le_mul_of_nonneg_right (min_le_left (e * a₃) (k * b₃)) hl3.le
      have e1 : k * (n * V - k * V) = e * (a₃ * Real.log 3) := by
        rw [← hkV, ← hke]
        ring
      linarith
    · rw [min_eq_right h]
      have := mul_le_mul_of_nonneg_right (min_le_right (e * a₃) (k * b₃)) hl3.le
      have e1 : k * (n * T₃ - k * V) = k * (b₃ * Real.log 3) := by
        rw [hnT₃, hkV]
        ring
      linarith
  have hmin := mul_le_mul_of_nonneg_left (arch_min (T₂ := T₂) (T₃ := T₃) (U := U) (V := V)
    hk.le hkn) hk.le
  have hP1 := mul_le_mul_of_nonneg_left hu (by linarith : (0 : ℝ) ≤ n - 2 * k)
  have hP2 := mul_le_mul_of_nonneg_right h₂ hl2.le
  have hP3 := mul_le_mul_of_nonneg_right h₃ hl3.le
  rw [le_div_iff₀ hk]
  have he : e = n - k := by linarith
  subst he
  linarith

/-- **Proposition 4.7, inequality (4.17), with the endpoint valuations
`D_{2,n} = v_2(H(0))`, `D_{3,n} = v_3(H(1))`.** See `kanekoZagier_arch_resultant`. -/
theorem kanekoZagier_arch_resultant_of_endpoint (hZ : JacobiSimpleRealZeros)
    (hNP : NewtonPolygonRootSlopes) {l μ : ℤ} (hl : l = 1 ∨
    l = -1) {δ : ℕ} (hδ : δ ≤ 1)
    (hμ : μ = 2 * δ - 1) {n : ℕ} {γ : ℚ} (hγ : 0 < γ) {H A B : ℤ[X]}
    (hH : H.map (Int.castRingHom ℚ) = C γ * jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n)
    (hlc2 : ¬ (2 : ℤ) ∣ H.leadingCoeff) (hlc3 : ¬ (3 : ℤ) ∣ H.leadingCoeff)
    (hAB : H = A * B) (hk : 1 ≤ A.natDegree) (hkn : 2 * A.natDegree ≤ n)
    (hH0 : H.eval 0 ≠ 0) (hH1 : H.eval 1 ≠ 0)
    {T₂ T₃ : ℝ} (hT₂ : T₂ = (padicValInt 2 (H.eval 0) : ℝ) * Real.log 2 / n)
    (hT₃ : T₃ = (padicValInt 3 (H.eval 1) : ℝ) * Real.log 3 / n) :
    Real.log (2 * γ * Real.sqrt (jacobiWronskianConstant ((l : ℚ) / 3) ((μ : ℚ) / 2) n)) -
        ((Nat.digits 2 n).sum * Real.log 2 / 2 + digitSum3 (2 * n + δ) * Real.log 3 / 6) +
        ((n : ℝ) - 2 * A.natDegree) * Real.log (Real.exp T₂ + Real.exp T₃) -
        ((n : ℝ) - A.natDegree) * (T₂ + T₃ + (Real.log 2 / 2 + Real.log 3 / 3)) +
        2 * ((A.natDegree : ℝ) - 1) ^ 2 * Real.log 2 / A.natDegree - Real.log A.natDegree ≤
      Real.log (|((resultant A B : ℤ) : ℝ)| /
        (2 ^ padicValInt 2 (resultant A B) * 3 ^ padicValInt 3 (resultant A B))) /
          A.natDegree := by
  have hμ' : μ = 1 ∨ μ = -1 := by omega
  have hα : -1 < (l : ℚ) / 3 := by rcases hl with rfl | rfl <;> norm_num
  have hβ : -1 < (μ : ℚ) / 2 := by rcases hμ' with h | h <;> rw [h] <;> norm_num
  have hn : 1 ≤ n := by omega
  obtain ⟨hnd, hcard⟩ := jacobiShifted_real_roots hZ hα hβ n
  have hCpos : (0 : ℝ) < (jacobiWronskianConstant ((l : ℚ) / 3) ((μ : ℚ) / 2) n : ℝ) := by
    exact_mod_cast jacobiWronskianConstant_pos hα hβ n
  have hc₀ : 0 < 2 * Real.sqrt (jacobiWronskianConstant ((l : ℚ) / 3) ((μ : ℚ) / 2) n) := by
    have := Real.sqrt_pos.mpr hCpos
    positivity
  obtain ⟨t, ht, hAt, hA0, hdeg, hR0, hlogR⟩ := log_abs_resultant_ge hcard hnd
    (natDegree_jacobiShifted_le _ _ n) hc₀ (jacobiShifted_root_derivative hα hβ hn) hγ hH hAB
    rfl hk hkn
  have hend := mul_log_exp_add_exp_le_log_leadingCoeff hk hAt ht hA0
  have h2 := padicValInt_two_resultant_le hNP hl hμ' hγ.ne' hH hlc2 hAB
  have h3 := padicValInt_three_resultant_le hNP hl hδ hμ hγ.ne' hH hlc3 hAB
  -- endpoint additivity
  have hev0 : H.eval 0 = A.eval 0 * B.eval 0 := by rw [hAB, eval_mul]
  have hev1 : H.eval 1 = A.eval 1 * B.eval 1 := by rw [hAB, eval_mul]
  have hv2 : (padicValInt 2 (H.eval 0) : ℝ) =
      padicValInt 2 (A.eval 0) + padicValInt 2 (B.eval 0) := by
    rw [hev0] at hH0 ⊢
    rw [padicValInt.mul (left_ne_zero_of_mul hH0) (right_ne_zero_of_mul hH0), Nat.cast_add]
  have hv3 : (padicValInt 3 (H.eval 1) : ℝ) =
      padicValInt 3 (A.eval 1) + padicValInt 3 (B.eval 1) := by
    rw [hev1] at hH1 ⊢
    rw [padicValInt.mul (left_ne_zero_of_mul hH1) (right_ne_zero_of_mul hH1), Nat.cast_add]
  rw [hv2] at hT₂
  rw [hv3] at hT₃
  have hk0 : (0 : ℝ) < A.natDegree := by exact_mod_cast hk
  have hkn' : 2 * (A.natDegree : ℝ) ≤ n := by exact_mod_cast hkn
  have hke : (A.natDegree : ℝ) + B.natDegree = n := by exact_mod_cast hdeg
  have key := arch_combine (G := Real.log ((γ : ℝ) *
      (2 * Real.sqrt (jacobiWronskianConstant ((l : ℚ) / 3) ((μ : ℚ) / 2) n))) +
        2 * ((A.natDegree : ℝ) - 1) ^ 2 * Real.log 2 / A.natDegree - Real.log A.natDegree)
    (R := Real.log |((resultant A B : ℤ) : ℝ)|) hk0 hkn' hke hT₂ hT₃
    (by
      have e1 : (A.natDegree : ℝ) * (Real.log ((γ : ℝ) *
          (2 * Real.sqrt (jacobiWronskianConstant ((l : ℚ) / 3) ((μ : ℚ) / 2) n))) +
          2 * ((A.natDegree : ℝ) - 1) ^ 2 * Real.log 2 / A.natDegree - Real.log A.natDegree) =
          A.natDegree * Real.log ((γ : ℝ) *
            (2 * Real.sqrt (jacobiWronskianConstant ((l : ℚ) / 3) ((μ : ℚ) / 2) n))) +
          2 * ((A.natDegree : ℝ) - 1) ^ 2 * Real.log 2 - A.natDegree * Real.log A.natDegree := by
        rw [mul_sub, mul_add, mul_div_cancel₀ _ hk0.ne']
      rw [e1]
      linarith)
    hend h2 h3
  have hRpos : 0 < |((resultant A B : ℤ) : ℝ)| := abs_pos.mpr (by exact_mod_cast hR0)
  have hsplit : Real.log (|((resultant A B : ℤ) : ℝ)| /
      (2 ^ padicValInt 2 (resultant A B) * 3 ^ padicValInt 3 (resultant A B))) =
      Real.log |((resultant A B : ℤ) : ℝ)| - (padicValInt 2 (resultant A B) : ℝ) * Real.log 2 -
        (padicValInt 3 (resultant A B) : ℝ) * Real.log 3 := by
    rw [Real.log_div hRpos.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]
    ring
  rw [hsplit]
  have hγc : Real.log (2 * (γ : ℝ) *
      Real.sqrt (jacobiWronskianConstant ((l : ℚ) / 3) ((μ : ℚ) / 2) n)) =
      Real.log ((γ : ℝ) *
        (2 * Real.sqrt (jacobiWronskianConstant ((l : ℚ) / 3) ((μ : ℚ) / 2) n))) := by
    congr 1
    ring
  rw [hγc]
  linarith

/-- **Proposition 4.7, inequality (4.17).**

Let `λ = l ∈ {±1}`, `μ = 2δ - 1` with `δ ∈ {0,1}`, `y_n = P_n^{(λ/3,μ/2)}(1-2t)`, and let
`H ∈ ℤ[X]` be `H = γ y_n` with `γ > 0`, `v_2(γ) = n + v_2(n!)`, `v_3(γ) = n + v_3(n!)` and
leading coefficient prime to `6` (for `H = H_n`, `γ = γ_n = κ_n / g_n`, these are Lemma 4.1 and
the definition of `κ_n`). Let `H = AB` with `A, B ∈ ℤ[X]` and `1 ≤ k = deg A ≤ n/2`. With
`R = |Res(A,B)|`, `R^{(6)} = R / (2^{v_2(R)} 3^{v_3(R)})`, `C_n` the Wronskian constant of
Lemma 2.1, `D_{2,n} = n + ∑_{j=1}^n v_2(3j+λ)`, `T_{2,n} = D_{2,n} log 2 / n`,
`D_{3,n} = n + ∑_{j=1}^n v_3(2j+μ)`, `T_{3,n} = D_{3,n} log 3 / n`,
`L_n = log(e^{T_{2,n}} + e^{T_{3,n}})`, `E = log 2 / 2 + log 3 / 3` and
`J_n = s_2(n) log 2 / 2 + s_3(2n+δ) log 3 / 6`:
`log R^{(6)} / k ≥ log(2 γ √C_n) - J_n + (n-2k) L_n - (n-k)(T_{2,n} + T_{3,n} + E)
  + 2(k-1)^2 log 2 / k - log k`.

Conditional on the proved `intervalVandermondeBound` (Lemma 2.5),
`JacobiSimpleRealZeros` ([DLMF, §18.2(vi)]) and `NewtonPolygonRootSlopes`
(Berger, Theorem 2.4; used for the root-valuation count of Proposition 4.6). -/
theorem kanekoZagier_arch_resultant (hZ : JacobiSimpleRealZeros)
    (hNP : NewtonPolygonRootSlopes) {l μ : ℤ} (hl : l = 1 ∨ l = -1) {δ
    : ℕ} (hδ : δ ≤ 1)
    (hμ : μ = 2 * δ - 1) {n : ℕ} {γ : ℚ} (hγ : 0 < γ)
    (hγ2 : padicValRat 2 γ = n + padicValNat 2 n.factorial)
    (hγ3 : padicValRat 3 γ = n + padicValNat 3 n.factorial) {H A B : ℤ[X]}
    (hH : H.map (Int.castRingHom ℚ) = C γ * jacobiShifted ((l : ℚ) / 3) ((μ : ℚ) / 2) n)
    (hlc2 : ¬ (2 : ℤ) ∣ H.leadingCoeff) (hlc3 : ¬ (3 : ℤ) ∣ H.leadingCoeff)
    (hAB : H = A * B) (hk : 1 ≤ A.natDegree) (hkn : 2 * A.natDegree ≤ n)
    {T₂ T₃ L E J : ℝ}
    (hT₂ : T₂ = ((n : ℝ) + ∑ j ∈ Finset.Icc 1 n, (padicValInt 2 (3 * j + l) : ℝ)) *
      Real.log 2 / n)
    (hT₃ : T₃ = ((n : ℝ) + ∑ j ∈ Finset.Icc 1 n, (padicValInt 3 (2 * j + μ) : ℝ)) *
      Real.log 3 / n)
    (hL : L = Real.log (Real.exp T₂ + Real.exp T₃))
    (hE : E = Real.log 2 / 2 + Real.log 3 / 3)
    (hJ : J = (Nat.digits 2 n).sum * Real.log 2 / 2 + digitSum3 (2 * n + δ) * Real.log 3 / 6) :
    Real.log (2 * γ * Real.sqrt (jacobiWronskianConstant ((l : ℚ) / 3) ((μ : ℚ) / 2) n)) - J +
        ((n : ℝ) - 2 * A.natDegree) * L - ((n : ℝ) - A.natDegree) * (T₂ + T₃ + E) +
        2 * ((A.natDegree : ℝ) - 1) ^ 2 * Real.log 2 / A.natDegree - Real.log A.natDegree ≤
      Real.log (|((resultant A B : ℤ) : ℝ)| /
        (2 ^ padicValInt 2 (resultant A B) * 3 ^ padicValInt 3 (resultant A B))) /
          A.natDegree := by
  have hμ' : μ = 1 ∨ μ = -1 := by omega
  obtain ⟨hH0, hv0⟩ := padicValInt_eval_zero_eq hl hγ.ne' hγ2 hH
  obtain ⟨hH1, hv1⟩ := padicValInt_eval_one_eq hμ' hγ.ne' hγ3 hH
  have hT₂' : T₂ = (padicValInt 2 (H.eval 0) : ℝ) * Real.log 2 / n := by
    rw [hT₂]
    have : ((padicValInt 2 (H.eval 0) : ℤ) : ℝ) =
        (((n + ∑ j ∈ Finset.Icc 1 n, (padicValInt 2 (3 * j + l) : ℤ)) : ℤ) : ℝ) := by
      rw [hv0]
    push_cast at this
    rw [this]
  have hT₃' : T₃ = (padicValInt 3 (H.eval 1) : ℝ) * Real.log 3 / n := by
    rw [hT₃]
    have : ((padicValInt 3 (H.eval 1) : ℤ) : ℝ) =
        (((n + ∑ j ∈ Finset.Icc 1 n, (padicValInt 3 (2 * j + μ) : ℤ)) : ℤ) : ℝ) := by
      rw [hv1]
    push_cast at this
    rw [this]
  subst hL hE hJ
  exact kanekoZagier_arch_resultant_of_endpoint hZ hNP hl hδ hμ hγ hH hlc2 hlc3 hAB hk hkn
    hH0 hH1 hT₂' hT₃'

end Proposition47

end ArithmeticOfJacobiPolynomials
