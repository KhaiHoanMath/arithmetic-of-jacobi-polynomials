/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.InertiaCycle
public import ArithmeticOfJacobiPolynomials.Galois.GaloisBridge

/-!
# The wild inertia cycle in the proof of Lemma 5.16

Let `f = c F` with `F ∈ ℤ[X]` of degree `N < 2p`, `p ∤ lc F`, `p ∣ [x^i] F` for `i < p`,
`p ∥ F(0)` and `p ∤ [x^p] F`. In the manuscript the reduction `F̄ = x^p Ḡ` lifts by Hensel's lemma
to an Eisenstein factor of degree `p`; a root generates a totally ramified extension of `ℚ_p` of
degree `p`, so the inertia group has order divisible by `p` (wild ramification is allowed), and
an element of order `p` is a single `p`-cycle because `N < 2p`.

The global valuation argument below proves the same inertia conclusion from these polynomial
hypotheses. It gives the `p`-cycle results in `UnequalParametersFixedField`. `SourceWildCycle`
follows the manuscript's Hensel argument for Lemma 5.16.

We argue globally, inside the splitting field `K` of `f`, at a prime `P` of `𝓞 K` above `p` with
valuation `v` (so `v p = exp (-e)`, `e = e(P/p) = |I_P|`):

* the product of the roots has valuation `v (F(0)/lc F) = v p < 1`, so some root `y` has
  `v y < 1`;
* comparing the terms of `F(y) = 0` (the constant term, the `x^p` term and the others) gives
  `v y ^ p = v p` (`valuation_pow_eq_of_wild`), so `p ∣ e = |I_P|`;
* Cauchy's theorem gives `σ ∈ I_P` of order `p`; it acts faithfully on the `N < 2p` roots, hence
  as a single `p`-cycle (`exists_isCycle_galPerm_mem_inertia_of_wild`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial NumberField IsDedekindDomain RootResidues

namespace UnequalParameters

section Valuation

variable {K : Type*} [Field K] [CharZero K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀}

/-- A root `y` with `v y < 1` of an integer polynomial `F` with `p ∣ [x^i] F` for `i < p`,
`p ∥ F(0)` and `p ∤ [x^p] F` satisfies `v y ^ p = v p`. -/
theorem valuation_pow_eq_of_wild {p : ℕ} (hv : IsAdicAt v p) (hp : p.Prime) {fZ : ℤ[X]}
    (hpN : p ≤ fZ.natDegree) (hlow : ∀ i < p, (p : ℤ) ∣ fZ.coeff i)
    (h0 : ¬ (p : ℤ) ^ 2 ∣ fZ.coeff 0) (hpp : ¬ (p : ℤ) ∣ fZ.coeff p) {y : K}
    (hy : (fK K fZ).eval y = 0) (hy1 : v y < 1) (hy0 : y ≠ 0) :
    v y ^ p = v (p : K) := by
  have hvy0 : 0 < v y := by rw [zero_lt_iff, Ne, Valuation.zero_iff]; exact hy0
  have hvp0 := valuation_prime_ne_zero (v := v) hp
  have hvp0' : 0 < v (p : K) := zero_lt_iff.mpr hvp0
  have hS := hy
  rw [eval_fK_eq_sum] at hS
  set N := fZ.natDegree with hN
  obtain ⟨u, hu⟩ := hlow 0 hp.pos
  have hu' : ¬ (p : ℤ) ∣ u := fun ⟨w, hw⟩ => h0 ⟨w, by rw [hu, hw]; ring⟩
  have hc0 : v (fZ.coeff 0 : K) = v (p : K) := by
    rw [hu]; push_cast; rw [v.map_mul, hv.eq_one hu', mul_one]
  have hcp : v (fZ.coeff p : K) = 1 := hv.eq_one hpp
  have hterm : ∀ j, v ((fZ.coeff j : K) * y ^ j) = v (fZ.coeff j : K) * v y ^ j := by
    intro j; rw [v.map_mul, v.map_pow]
  rcases lt_trichotomy (v y ^ p) (v (p : K)) with hlt | heq | hgt
  · exfalso
    have key := valuation_sum_eq_of_dominant v (Finset.range (N + 1))
      (fun j => (fZ.coeff j : K) * y ^ j) (j₀ := 0) (by simp)
      (by simp only [pow_zero, mul_one, hc0]; exact hvp0)
      (by
        intro j _ hj0
        simp only [pow_zero, mul_one, hc0, hterm]
        by_cases hjp : j < p
        · calc v (fZ.coeff j : K) * v y ^ j ≤ v (p : K) * v y ^ j :=
                mul_le_mul_left (valuation_le_of_dvd (hlow j hjp)) _
            _ < v (p : K) := mul_lt_of_lt_one_right hvp0' (pow_lt_one₀ zero_le hy1 hj0)
        · calc v (fZ.coeff j : K) * v y ^ j ≤ 1 * v y ^ j :=
                mul_le_mul_left (valuation_intCast_le_one v _) _
            _ ≤ v y ^ p := by
                rw [one_mul]; exact pow_le_pow_of_le_one zero_le hy1.le (by omega)
            _ < v (p : K) := hlt)
    rw [hS, v.map_zero] at key
    simp only [pow_zero, mul_one, hc0] at key
    exact hvp0 key.symm
  · exact heq
  · exfalso
    have key := valuation_sum_eq_of_dominant v (Finset.range (N + 1))
      (fun j => (fZ.coeff j : K) * y ^ j) (j₀ := p) (Finset.mem_range.mpr (by omega))
      (by simp only [hterm, hcp, one_mul]; exact pow_ne_zero _ hvy0.ne')
      (by
        intro j _ hjp
        simp only [hterm, hcp, one_mul]
        rcases lt_or_gt_of_ne hjp with hlt' | hgt'
        · calc v (fZ.coeff j : K) * v y ^ j ≤ v (p : K) * 1 :=
                mul_le_mul' (valuation_le_of_dvd (hlow j hlt')) (pow_le_one₀ zero_le hy1.le)
            _ < v y ^ p := by rw [mul_one]; exact hgt
        · calc v (fZ.coeff j : K) * v y ^ j ≤ 1 * v y ^ j :=
                mul_le_mul_left (valuation_intCast_le_one v _) _
            _ < v y ^ p := by
                rw [one_mul]; exact pow_lt_pow_right_of_lt_one₀ hvy0 hy1 hgt')
    rw [hS, v.map_zero] at key
    simp only [hterm, hcp, one_mul] at key
    exact pow_ne_zero _ hvy0.ne' key.symm

end Valuation

open Classical in
/-- **The wild inertia cycle** (proof of Lemma 5.16). Let `f = c F` with
`c ≠ 0` and `F ∈ ℤ[X]` of degree `< 2p`, where `p` is prime, `p ∤ lc F`, `p` divides the
coefficients of `x^i` for `i < p`, `p² ∤ F(0)` and `p ∤ [x^p] F`. For every prime `P` of the ring
of integers of the splitting field of `f` lying over `p`, some element of the inertia group
`I_P` acts on the roots of `f` as a single `p`-cycle. -/
theorem exists_isCycle_galPerm_mem_inertia_of_wild {p : ℕ} (hp : p.Prime) {f : ℚ[X]}
    {fZ : ℤ[X]} {c : ℚ} (hc : c ≠ 0) (hf : f = C c * fZ.map (Int.castRingHom ℚ))
    (hdeg : fZ.natDegree < 2 * p) (hlc : ¬ (p : ℤ) ∣ fZ.leadingCoeff)
    (hlow : ∀ i < p, (p : ℤ) ∣ fZ.coeff i) (h0 : ¬ (p : ℤ) ^ 2 ∣ fZ.coeff 0)
    (hpp : ¬ (p : ℤ) ∣ fZ.coeff p)
    (P : Ideal (𝓞 f.SplittingField)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    ∃ σ : f.Gal, σ ∈ P.inertia Gal(f.SplittingField/ℚ) ∧ (galPerm f σ).IsCycle ∧
      (galPerm f σ).support.card = p := by
  have : Fact p.Prime := ⟨hp⟩
  have : NumberField f.SplittingField := ⟨⟩
  have : IsGalois ℚ f.SplittingField := IsGalois.mk
  have := Int.ideal_span_isMaximal_of_prime p
  have hPmax : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P (Ideal.span {(p : ℤ)})
  have hP0 : P ≠ ⊥ := Ideal.IsMaximal.ne_bot_of_isIntegral_int P
  let w : HeightOneSpectrum (𝓞 f.SplittingField) := ⟨P, hPmax.isPrime, hP0⟩
  have : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := ‹P.LiesOver _›
  have hv : IsAdicAt (w.valuation f.SplittingField) p := InertiaCycle.isAdicAt w
  -- basic facts on `F`
  have hc00 : fZ.coeff 0 ≠ 0 := fun h => h0 (by rw [h]; exact dvd_zero _)
  have hcp0 : fZ.coeff p ≠ 0 := fun h => hpp (by rw [h]; exact dvd_zero _)
  have hpN : p ≤ fZ.natDegree := le_natDegree_of_ne_zero hcp0
  have hfmap : f.map (algebraMap ℚ f.SplittingField) =
      C (algebraMap ℚ f.SplittingField c) * fK f.SplittingField fZ := by
    have h := congrArg (Polynomial.map (algebraMap ℚ f.SplittingField)) hf
    rw [h, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map,
      RingHom.ext_int ((algebraMap ℚ f.SplittingField).comp (Int.castRingHom ℚ))
        (Int.castRingHom f.SplittingField)]
  have hc' : algebraMap ℚ f.SplittingField c ≠ 0 := (_root_.map_ne_zero _).mpr hc
  have hsplitZ : (fK f.SplittingField fZ).Splits := by
    have h := SplittingField.splits f
    rw [hfmap] at h
    have h2 := h.C_mul (algebraMap ℚ f.SplittingField c)⁻¹
    rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ hc', C_1, one_mul] at h2
  -- a root of valuation `< 1`
  have hprod := hsplitZ.coeff_zero_eq_leadingCoeff_mul_prod_roots
  have hcoeff0 : (fK f.SplittingField fZ).coeff 0 = (fZ.coeff 0 : f.SplittingField) := by
    rw [coeff_map, eq_intCast]
  have hlcK : (fK f.SplittingField fZ).leadingCoeff = (fZ.leadingCoeff : f.SplittingField) := by
    rw [leadingCoeff, natDegree_fK, coeff_map, eq_intCast, leadingCoeff]
  obtain ⟨u, hu⟩ := hlow 0 hp.pos
  have hu' : ¬ (p : ℤ) ∣ u := fun ⟨w, hw⟩ => h0 ⟨w, by rw [hu, hw]; ring⟩
  have hvc0 : w.valuation f.SplittingField (fZ.coeff 0 : f.SplittingField) =
      w.valuation f.SplittingField (p : f.SplittingField) := by
    rw [hu]; push_cast; rw [Valuation.map_mul, hv.eq_one hu', mul_one]
  have hvprod : w.valuation f.SplittingField (fK f.SplittingField fZ).roots.prod =
      w.valuation f.SplittingField (p : f.SplittingField) := by
    have h := congrArg (w.valuation f.SplittingField) hprod
    rw [hcoeff0, hvc0, Valuation.map_mul, Valuation.map_mul, Valuation.map_pow,
      Valuation.map_neg, Valuation.map_one, one_pow, one_mul, hlcK, hv.eq_one hlc,
      one_mul] at h
    exact h.symm
  obtain ⟨y, hyroot, hy1⟩ : ∃ y ∈ (fK f.SplittingField fZ).roots,
      w.valuation f.SplittingField y < 1 := by
    by_contra hcon
    push Not at hcon
    have h1 : 1 ≤ w.valuation f.SplittingField (fK f.SplittingField fZ).roots.prod :=
      Multiset.prod_induction (fun x => 1 ≤ w.valuation f.SplittingField x) _
        (fun a b ha hb => by rw [Valuation.map_mul]; exact one_le_mul ha hb)
        (le_of_eq (Valuation.map_one _).symm) hcon
    rw [hvprod] at h1
    exact absurd hv.lt_one (not_lt.mpr h1)
  have hy : (fK f.SplittingField fZ).eval y = 0 := (mem_roots'.mp hyroot).2
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [← coeff_zero_eq_eval_zero, hcoeff0] at hy
    exact hc00 (by exact_mod_cast hy)
  have hpow := valuation_pow_eq_of_wild hv hp hpN hlow h0 hpp hy hy1 hy0
  -- `p ∣ e(P/p) = |I_P|`
  have hvy0 : w.valuation f.SplittingField y ≠ 0 := by rw [Ne, Valuation.zero_iff]; exact hy0
  have he : p ∣ w.asIdeal.ramificationIdx ℤ := by
    have h := hpow
    rw [InertiaCycle.valuation_prime_eq w, ← WithZero.exp_log hvy0, ← WithZero.exp_nsmul] at h
    have h' := WithZero.exp_injective h
    rw [nsmul_eq_mul] at h'
    have : (p : ℤ) ∣ (w.asIdeal.ramificationIdx ℤ : ℤ) :=
      ⟨-WithZero.log (w.valuation f.SplittingField y), by linarith⟩
    exact_mod_cast this
  have hcard := InertiaCycle.card_inertia w p
  rw [← hcard] at he
  obtain ⟨x, hx⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(w.asIdeal.inertia Gal(f.SplittingField/ℚ))) p he
  have hord : orderOf (galPerm f (x : Gal(f.SplittingField/ℚ))) = p :=
    (orderOf_injective (galPerm f) (galPerm_injective f) (x : Gal(f.SplittingField/ℚ))).trans
      ((Subgroup.orderOf_coe x).trans hx)
  -- the number of roots
  have hroots : Fintype.card (f.rootSet f.SplittingField) ≤ fZ.natDegree := by
    have hfdeg : f.natDegree = fZ.natDegree := by
      rw [hf, natDegree_C_mul hc, natDegree_map_eq_of_injective (RingHom.injective_int _)]
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, rootSet_def, Set.ncard_coe_finset,
      ← hfdeg]
    exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans natDegree_map_le)
  have hsupp : (galPerm f (x : Gal(f.SplittingField/ℚ))).support.card <
      2 * orderOf (galPerm f (x : Gal(f.SplittingField/ℚ))) := by
    rw [hord]
    exact lt_of_le_of_lt ((Finset.card_le_univ _).trans hroots) hdeg
  have hcyc : (galPerm f (x : Gal(f.SplittingField/ℚ))).IsCycle :=
    Equiv.Perm.isCycle_of_prime_order (by rw [hord]; exact hp) hsupp
  refine ⟨(x : Gal(f.SplittingField/ℚ)), x.2, hcyc, ?_⟩
  rw [← hcyc.orderOf, hord]

open Classical in
/-- **The wild cycle** (proof of Lemma 5.16): under the hypotheses of
`exists_isCycle_galPerm_mem_inertia_of_wild`, `Gal(f/ℚ)` contains an element acting on the roots
of `f` as a single `p`-cycle. -/
theorem exists_isCycle_galPerm_of_wild {p : ℕ} (hp : p.Prime) {f : ℚ[X]} {fZ : ℤ[X]} {c : ℚ}
    (hc : c ≠ 0) (hf : f = C c * fZ.map (Int.castRingHom ℚ)) (hdeg : fZ.natDegree < 2 * p)
    (hlc : ¬ (p : ℤ) ∣ fZ.leadingCoeff) (hlow : ∀ i < p, (p : ℤ) ∣ fZ.coeff i)
    (h0 : ¬ (p : ℤ) ^ 2 ∣ fZ.coeff 0) (hpp : ¬ (p : ℤ) ∣ fZ.coeff p) :
    ∃ σ : f.Gal, (galPerm f σ).IsCycle ∧ (galPerm f σ).support.card = p := by
  have : Fact p.Prime := ⟨hp⟩
  have : NumberField f.SplittingField := ⟨⟩
  have := Int.ideal_span_isMaximal_of_prime p
  obtain ⟨P, hPmax, hPover⟩ : ∃ P : Ideal (𝓞 f.SplittingField),
      P.IsMaximal ∧ P.LiesOver (Ideal.span {(p : ℤ)}) :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral _
  obtain ⟨σ, -, h⟩ := exists_isCycle_galPerm_mem_inertia_of_wild hp hc hf hdeg hlc hlow h0 hpp P
  exact ⟨σ, h⟩

end UnequalParameters

end ArithmeticOfJacobiPolynomials
