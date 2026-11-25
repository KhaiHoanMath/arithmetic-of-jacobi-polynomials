/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.KanekoZagier.Archimedean
public import Mathlib.LinearAlgebra.Lagrange
public import ArithmeticOfJacobiPolynomials.Jacobi.RealWronskian

/-!
# Gaussian quadrature (remark after Lemma 2.1)

After Lemma 2.1 the manuscript notes that the numbers `ω_i = I(ℓ_i)` are the Gaussian quadrature
weights: if `deg q ≤ 2n-1`, then `I(q) = ∑ ω_i q(t_i)`, the weights are positive and sum to one.

* `momentQuadrature`: the algebraic statement for a linear functional `I` over a field and a monic
  `M = ∏_{t ∈ s} (X - t)` with `I(M g) = 0` for `deg g < #s`;
* `jacobi_gaussian_quadrature`: the statement for the Jacobi probability functional and the roots
  of `y_n = P_n^{(α,β)}(1-2t)`, `α, β > -1` (conditional on `JacobiSimpleRealZeros`).
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

/-- **Quadrature for an orthogonality functional.** Let `I` be linear, `s` a finite set of nodes,
`M = ∏_{t ∈ s} (X - t)` and suppose `I(M g) = 0` whenever `deg g < #s`. Then for `deg q < 2 #s`,
`I(q) = ∑_{t ∈ s} I(ℓ_t) q(t)`, with `ℓ_t` the Lagrange basis polynomials. -/
theorem momentQuadrature {F : Type*} [Field F] [DecidableEq F] (I : F[X] →ₗ[F] F) (s : Finset F)
    (horth : ∀ g : F[X], g.natDegree < #s → I ((∏ t ∈ s, (polyX - C t)) * g) = 0)
    {q : F[X]} (hq : q.natDegree < 2 * #s) :
    I q = ∑ t ∈ s, I (Lagrange.basis s id t) * q.eval t := by
  set M := ∏ t ∈ s, (polyX - C t) with hM
  have hMm : M.Monic := monic_prod_of_monic _ _ fun t _ => monic_X_sub_C t
  have hMdeg : M.natDegree = #s := by
    rw [hM, natDegree_prod_of_monic _ _ fun t _ => monic_X_sub_C t]
    simp
  have hMt : ∀ t ∈ s, M.eval t = 0 := fun t ht => by
    rw [hM, eval_prod]
    exact prod_eq_zero ht (by simp)
  by_cases hs : #s = 0
  · exfalso; rw [hs] at hq; omega
  have hM1 : M ≠ 1 := fun h => by rw [h, natDegree_one] at hMdeg; omega
  set r := q %ₘ M
  have hdecomp := modByMonic_add_div q M
  have hrdeg : r.natDegree < #s := hMdeg ▸ natDegree_modByMonic_lt q hMm hM1
  have hdiv : (q /ₘ M).natDegree < #s := by
    rw [natDegree_divByMonic _ hMm, hMdeg]; omega
  have hIr : I q = I r := by
    conv_lhs => rw [← hdecomp]
    rw [map_add, horth _ hdiv, add_zero]
  have hrq : ∀ t ∈ s, r.eval t = q.eval t := fun t ht => by
    conv_rhs => rw [← hdecomp]
    rw [eval_add, eval_mul, hMt t ht, zero_mul, add_zero]
  have hinj : Set.InjOn (id : F → F) s := Set.injOn_id _
  have hr : r = Lagrange.interpolate s id (fun t => r.eval t) := by
    refine Lagrange.eq_interpolate hinj ?_
    rcases eq_or_ne r 0 with h0 | h0
    · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
    · rw [degree_eq_natDegree h0]; exact_mod_cast hrdeg
  rw [hIr, hr, Lagrange.interpolate_apply, map_sum]
  refine sum_congr rfl fun t ht => ?_
  simp only [← smul_eq_C_mul, map_smul, smul_eq_mul]
  rw [mul_comm, hrq t ht]

/-- **Gaussian quadrature for Jacobi polynomials** (remark after Lemma 2.1). For rational
`α, β > -1` and `n ≥ 1`, let `s` be the set of real roots of `y_n = P_n^{(α,β)}(1-2t)` and `I` the
Jacobi probability functional. Then for every real `q` with `deg q ≤ 2n-1`,
`I(q) = ∑_{t ∈ s} ω_t q(t)` with `ω_t = I(ℓ_t) > 0` and `∑ ω_t = 1`. Conditional on the cited
`JacobiSimpleRealZeros`. -/
theorem jacobi_gaussian_quadrature (hZ : JacobiSimpleRealZeros) {α β : ℚ} (hα : -1 < α)
    (hβ : -1 < β) {n : ℕ} (hn : 1 ≤ n) :
    let s := ((jacobiShifted α β n).map (algebraMap ℚ ℝ)).roots.toFinset
    (∀ q : ℝ[X], q.natDegree < 2 * n →
      jacobiFunctionalReal α β q =
        ∑ t ∈ s, jacobiFunctionalReal α β (Lagrange.basis s id t) * q.eval t) ∧
    (∀ t ∈ s, 0 < jacobiFunctionalReal α β (Lagrange.basis s id t)) ∧
    ∑ t ∈ s, jacobiFunctionalReal α β (Lagrange.basis s id t) = 1 := by
  classical
  intro s
  obtain ⟨hnd, hcard⟩ := jacobiShifted_real_roots hZ hα hβ n
  set y := (jacobiShifted α β n).map (algebraMap ℚ ℝ) with hy
  have hs : #s = n := by rw [Multiset.toFinset_card_of_nodup hnd, hcard]
  have hy0 : y ≠ 0 := fun h => by
    rw [h, roots_zero, Multiset.card_zero] at hcard; omega
  have hydeg : y.natDegree = n := by
    rw [← hcard]
    have := card_roots' y
    have h2 : y.natDegree ≤ n := by
      rw [hy, natDegree_map]; exact natDegree_jacobiShifted_le α β n
    omega
  obtain ⟨lc, hlcdef⟩ : ∃ lc, lc = y.leadingCoeff := ⟨_, rfl⟩
  have hsval : s.val = y.roots := by
    change y.roots.dedup = y.roots
    exact hnd.dedup
  have hprod : y = C lc * ∏ t ∈ s, (polyX - C t) := by
    have h := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := y) (by rw [hcard, hydeg])
    rw [Finset.prod_eq_multiset_prod, hsval, hlcdef]
    exact h.symm
  have hlc : lc ≠ 0 := hlcdef ▸ leadingCoeff_ne_zero.mpr hy0
  have horth : ∀ g : ℝ[X], g.natDegree < #s →
      jacobiFunctionalReal α β ((∏ t ∈ s, (polyX - C t)) * g) = 0 := by
    intro g hg
    have e : (∏ t ∈ s, (polyX - C t)) * g = y * (C lc⁻¹ * g) := by
      rw [hprod, mul_mul_mul_comm, ← C_mul, mul_inv_cancel₀ hlc, C_1, one_mul]
    rw [e]
    refine jacobiFunctionalReal_jacobiShifted_mul hα hβ n ?_
    calc (C lc⁻¹ * g).natDegree ≤ g.natDegree := natDegree_C_mul_le _ _
      _ < n := hs ▸ hg
  have hquad : ∀ q : ℝ[X], q.natDegree < 2 * n →
      jacobiFunctionalReal α β q =
        ∑ t ∈ s, jacobiFunctionalReal α β (Lagrange.basis s id t) * q.eval t :=
    fun q hq => momentQuadrature _ s horth (hs ▸ hq)
  have hinj : Set.InjOn (id : ℝ → ℝ) s := Set.injOn_id _
  refine ⟨hquad, fun t ht => ?_, ?_⟩
  · have hb0 := Lagrange.basis_ne_zero hinj ht
    have hpos := jacobiFunctionalReal_mul_self_pos hα hβ hb0
    have hdeg : (Lagrange.basis s id t * Lagrange.basis s id t).natDegree < 2 * n := by
      rw [natDegree_mul hb0 hb0, Lagrange.natDegree_basis hinj ht, hs]; omega
    rw [hquad _ hdeg] at hpos
    have hself : (Lagrange.basis s id t).eval t = 1 := by
      simpa using Lagrange.eval_basis_self hinj ht
    rw [sum_eq_single t (fun u hu hut => by
      have h0 : (Lagrange.basis s id t).eval u = 0 := by
        simpa using Lagrange.eval_basis_of_ne (v := id) (Ne.symm hut) hu
      rw [eval_mul, h0, zero_mul, mul_zero])
      (fun h => absurd ht h), eval_mul, hself, mul_one, mul_one] at hpos
    exact hpos
  · have h1 := hquad 1 (by rw [natDegree_one]; omega)
    simp only [eval_one, mul_one] at h1
    rw [← h1]
    have : jacobiFunctionalReal α β 1 = ((jacobiMoment α β 0 : ℚ) : ℝ) := by
      rw [jacobiFunctionalReal_eq, ← C_1, momentFunctional_C, mul_one]
    rw [this, jacobiMoment_zero, Rat.cast_one]

/-- The Gaussian-quadrature remark after Lemma 2.1 for all real parameters `α, β > -1`.
The weights are those of the normalized Jacobi integral, as identified by
`JacobiGeneric.Real.jacobiFunctional_mul_integral`. -/
theorem jacobi_gaussian_quadrature_real (hZ : JacobiSimpleRealZeros) {α β : ℝ} (hα : -1 < α)
    (hβ : -1 < β) {n : ℕ} (hn : 1 ≤ n) :
    let s := (JacobiGeneric.jacobiShifted α β n).roots.toFinset
    (∀ q : ℝ[X], q.natDegree < 2 * n →
      JacobiGeneric.jacobiFunctional α β q =
        ∑ t ∈ s, JacobiGeneric.jacobiFunctional α β (Lagrange.basis s id t) * q.eval t) ∧
    (∀ t ∈ s, 0 < JacobiGeneric.jacobiFunctional α β (Lagrange.basis s id t)) ∧
    ∑ t ∈ s, JacobiGeneric.jacobiFunctional α β (Lagrange.basis s id t) = 1 := by
  classical
  intro s
  obtain ⟨hpnd, hpcard, -⟩ := hZ α β hα hβ n
  have hp : JacobiGeneric.jacobiP α β n = jacobiPolynomial α β n := by
    rw [JacobiGeneric.jacobiP_eq, jacobiPolynomial_eq]
  have heq : JacobiGeneric.jacobiShifted α β n =
      (jacobiPolynomial α β n).comp (C (-2) * polyX + C 1) := by
    rw [JacobiGeneric.jacobiShifted_eq, hp]
    congr 1
    simp only [C_neg, map_ofNat C 2, C_1]
    ring
  have hm := map_roots_comp_C_mul_X_add_C (jacobiPolynomial α β n) (-2) 1
    (IsUnit.mk0 (-2 : ℝ) (by norm_num))
  have hnd : (JacobiGeneric.jacobiShifted α β n).roots.Nodup := by
    rw [heq]
    exact Multiset.Nodup.of_map (fun x => -2 * x + 1) (by rw [hm]; exact hpnd)
  have hcard : (JacobiGeneric.jacobiShifted α β n).roots.card = n := by
    rw [heq, ← Multiset.card_map (fun x => -2 * x + 1), hm, hpcard]
  set y := JacobiGeneric.jacobiShifted α β n with hy
  have hs : #s = n := by rw [Multiset.toFinset_card_of_nodup hnd, hcard]
  have hy0 : y ≠ 0 := fun h => by
    rw [h, roots_zero, Multiset.card_zero] at hcard; omega
  have hydeg : y.natDegree = n := by
    rw [← hcard]
    have := card_roots' y
    have h2 : y.natDegree ≤ n := by
      rw [hy]; exact JacobiGeneric.natDegree_jacobiShifted_le α β n
    omega
  obtain ⟨lc, hlcdef⟩ : ∃ lc, lc = y.leadingCoeff := ⟨_, rfl⟩
  have hsval : s.val = y.roots := by
    change y.roots.dedup = y.roots
    exact hnd.dedup
  have hprod : y = C lc * ∏ t ∈ s, (polyX - C t) := by
    have h := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := y) (by rw [hcard, hydeg])
    rw [Finset.prod_eq_multiset_prod, hsval, hlcdef]
    exact h.symm
  have hlc : lc ≠ 0 := hlcdef ▸ leadingCoeff_ne_zero.mpr hy0
  have horth : ∀ g : ℝ[X], g.natDegree < #s →
      JacobiGeneric.jacobiFunctional α β ((∏ t ∈ s, (polyX - C t)) * g) = 0 := by
    intro g hg
    have e : (∏ t ∈ s, (polyX - C t)) * g = y * (C lc⁻¹ * g) := by
      rw [hprod, mul_mul_mul_comm, ← C_mul, mul_inv_cancel₀ hlc, C_1, one_mul]
    rw [e]
    refine JacobiGeneric.Real.jacobiFunctional_jacobiShifted_mul_of_natDegree_lt hα hβ n ?_
    calc (C lc⁻¹ * g).natDegree ≤ g.natDegree := natDegree_C_mul_le _ _
      _ < n := hs ▸ hg
  have hquad : ∀ q : ℝ[X], q.natDegree < 2 * n →
      JacobiGeneric.jacobiFunctional α β q =
        ∑ t ∈ s, JacobiGeneric.jacobiFunctional α β (Lagrange.basis s id t) * q.eval t :=
    fun q hq => momentQuadrature _ s horth (hs ▸ hq)
  have hinj : Set.InjOn (id : ℝ → ℝ) s := Set.injOn_id _
  refine ⟨hquad, fun t ht => ?_, ?_⟩
  · have hb0 := Lagrange.basis_ne_zero hinj ht
    have hpos := JacobiGeneric.Real.jacobiFunctional_mul_self_pos hα hβ hb0
    have hdeg : (Lagrange.basis s id t * Lagrange.basis s id t).natDegree < 2 * n := by
      rw [natDegree_mul hb0 hb0, Lagrange.natDegree_basis hinj ht, hs]; omega
    rw [hquad _ hdeg] at hpos
    have hself : (Lagrange.basis s id t).eval t = 1 := by
      simpa using Lagrange.eval_basis_self hinj ht
    rw [sum_eq_single t (fun u hu hut => by
      have h0 : (Lagrange.basis s id t).eval u = 0 := by
        simpa using Lagrange.eval_basis_of_ne (v := id) (Ne.symm hut) hu
      rw [eval_mul, h0, zero_mul, mul_zero])
      (fun h => absurd ht h), eval_mul, hself, mul_one, mul_one] at hpos
    exact hpos
  · have h1 := hquad 1 (by rw [natDegree_one]; omega)
    simp only [eval_one, mul_one] at h1
    rw [← h1]
    simpa only [← C_1] using JacobiGeneric.jacobiFunctional_C α β 1

end ArithmeticOfJacobiPolynomials
