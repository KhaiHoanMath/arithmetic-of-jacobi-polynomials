/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.Defs
public import ArithmeticOfJacobiPolynomials.Galois.RootResidues
public import Mathlib

/-!
# Shared helpers for the inertia cycle of Lemma 5.1

The proof of Lemma 5.1 follows the manuscript's local argument over `ℚ_p` in `SourceInertiaCycle`.
`SourceInertiaCycleGlobal` transfers the result to the splitting field and proves the `d`-cycle and
`2d`-cycle theorems.

The lemmas below describe valuations, inertia groups and the quadratic substitution.

* valuation facts for a prime `w` of `𝓞 K` (`valuation_coe_eq_one`,
  `valuation_sub_lt_one_of_mem_inertia`, `isAdicAt`, `valuation_prime_eq`, `card_inertia`), used by
  `InertiaCyclePadic` and `SourceWildCycle`;
* `exists_isMaximal_liesOver`;
* the passage `hyp_comp` from the hypotheses of Lemma 5.1 for `f` to those for `f(cX²)`, and the
  negation/centralizer step `pow_apply_eq_of_commute`, `galPerm_comp_pow_apply_eq_neg`
  (the quadratic part of Lemma 5.1).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial NumberField IsDedekindDomain RootResidues

namespace InertiaCycle

variable {K : Type*} [Field K] [NumberField K]

theorem exists_eq_mul_inv_of_valuation_le_one (w : HeightOneSpectrum (𝓞 K)) {x : K}
    (hx : w.valuation K x ≤ 1) : ∃ a s : 𝓞 K, s ∉ w.asIdeal ∧ x = (a : K) * (s : K)⁻¹ := by
  have hx' : x ∈ HeightOneSpectrum.valuationSubringAtPrime K w := by
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]; exact hx
  unfold HeightOneSpectrum.valuationSubringAtPrime at hx'
  rw [ValuationSubring.mem_ofSubring] at hx'
  simp only [Localization.subalgebra.ofField, Ideal.mem_primeCompl_iff, exists_prop,
    Subring.mem_mk, Subalgebra.copy_toSubsemiring] at hx'
  exact hx'

theorem valuation_coe_eq_one (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs : s ∉ w.asIdeal) :
    w.valuation K (s : K) = 1 := by
  change w.valuation K (algebraMap (𝓞 K) K s) = 1
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact le_antisymm (w.intValuation_le_one s)
    (not_lt.mp fun h => hs ((w.intValuation_lt_one_iff_mem s).mp h))

theorem valuation_coe_lt_one (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs : s ∈ w.asIdeal) :
    w.valuation K (s : K) < 1 := by
  change w.valuation K (algebraMap (𝓞 K) K s) < 1
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (w.intValuation_lt_one_iff_mem s).mpr hs

/-- Inertia acts trivially modulo `P` on `P`-integral elements of `K`. -/
theorem valuation_sub_lt_one_of_mem_inertia (w : HeightOneSpectrum (𝓞 K)) {σ : Gal(K/ℚ)}
    (hσ : σ ∈ w.asIdeal.inertia Gal(K/ℚ)) {x : K} (hx : w.valuation K x ≤ 1) :
    w.valuation K (σ x - x) < 1 := by
  obtain ⟨a, s, hs, rfl⟩ := exists_eq_mul_inv_of_valuation_le_one w hx
  have ha : σ • a - a ∈ w.asIdeal := (Ideal.mem_inertia.mp hσ) a
  have hs' : σ • s - s ∈ w.asIdeal := (Ideal.mem_inertia.mp hσ) s
  have hσs : σ • s ∉ w.asIdeal := fun h => hs (by
    have := w.asIdeal.sub_mem h hs'
    rwa [sub_sub_cancel] at this)
  have hs0 : (s : K) ≠ 0 := by
    intro h
    exact hs (by rw [show s = 0 from RingOfIntegers.coe_eq_zero_iff.mp h]; exact w.asIdeal.zero_mem)
  have hσs0 : σ (s : K) ≠ 0 := by rwa [_root_.map_ne_zero]
  have e1 : ((σ • a : 𝓞 K) : K) = σ (a : K) := rfl
  have e2 : ((σ • s : 𝓞 K) : K) = σ (s : K) := rfl
  have key : σ ((a : K) * (s : K)⁻¹) - (a : K) * (s : K)⁻¹ =
      (((σ • a - a) * s - a * (σ • s - s) : 𝓞 K) : K) * ((s : K) * ((σ • s : 𝓞 K) : K))⁻¹ := by
    push_cast [e1, e2]
    rw [map_mul, map_inv₀]
    field_simp
    ring
  rw [key, map_mul, map_inv₀, map_mul, valuation_coe_eq_one w hs, valuation_coe_eq_one w hσs,
    mul_one, inv_one, mul_one]
  exact valuation_coe_lt_one w
    (w.asIdeal.sub_mem (w.asIdeal.mul_mem_right _ ha) (w.asIdeal.mul_mem_left _ hs'))

theorem span_prime_isPrime (p : ℕ) [Fact p.Prime] : (Ideal.span {(p : ℤ)}).IsPrime :=
  (Int.ideal_span_isMaximal_of_prime p).isPrime

/-- The prime `p` as a point of `HeightOneSpectrum ℤ`. -/
noncomputable def primeSpectrum (p : ℕ) [hp : Fact p.Prime] : HeightOneSpectrum ℤ :=
  ⟨Ideal.span {(p : ℤ)}, span_prime_isPrime p, by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.out.ne_zero⟩

variable {p : ℕ} [hp : Fact p.Prime]

variable (w : HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})]

omit hp in
theorem isAdicAt : IsAdicAt (w.valuation K) p := by
  unfold IsAdicAt
  intro n
  have h : ((n : K)) = algebraMap (𝓞 K) K (n : 𝓞 K) := by simp
  rw [h, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_lt_one_iff_mem,
    ← Ideal.mem_span_singleton, Ideal.LiesOver.over (P := w.asIdeal) (p := Ideal.span {(p : ℤ)}),
    Ideal.under_def, Ideal.mem_comap]
  simp

theorem valuation_prime_eq :
    w.valuation K (p : K) = WithZero.exp (-(w.asIdeal.ramificationIdx ℤ : ℤ)) := by
  have : w.asIdeal.LiesOver (primeSpectrum p).asIdeal := inferInstanceAs
    (w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}))
  have h := HeightOneSpectrum.valuation_liesOver (K := ℚ) K (primeSpectrum p) w (p : ℚ)
  rw [show algebraMap ℚ K (p : ℚ) = (p : K) by simp] at h
  rw [← h]
  rw [show (p : ℚ) = algebraMap ℤ ℚ (p : ℤ) by simp, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_singleton (primeSpectrum p)
      (by exact_mod_cast hp.out.ne_zero) rfl, ← WithZero.exp_nsmul]
  congr 1
  simp

omit [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] in
theorem card_inertia [IsGalois ℚ K] (p : ℕ) [Fact p.Prime]
    [w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] :
    Nat.card (w.asIdeal.inertia Gal(K/ℚ)) = w.asIdeal.ramificationIdx ℤ := by
  have := span_prime_isPrime p
  rw [Ideal.card_inertia_eq_ramificationIdxIn (Ideal.span {(p : ℤ)}) w.asIdeal]
  exact Ideal.ramificationIdxIn_eq_ramificationIdx _ w.asIdeal Gal(K/ℚ)

/-- Over a prime `p`, the ring of integers of the splitting field of `f` has a maximal ideal
lying over `p`. -/
theorem exists_isMaximal_liesOver (p : ℕ) [Fact p.Prime] (f : ℤ[X]) :
    ∃ P : Ideal (𝓞 (f.map (Int.castRingHom ℚ)).SplittingField),
      P.IsMaximal ∧ P.LiesOver (Ideal.span {(p : ℤ)}) := by
  have : NumberField (f.map (Int.castRingHom ℚ)).SplittingField := ⟨⟩
  have := Int.ideal_span_isMaximal_of_prime p
  exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral _

/-- The hypotheses of Lemma 5.1 pass from `f` (with drop `d`) to `f(cX²)` (with drop `2d`). -/
theorem hyp_comp {p d : ℕ} {f : ℤ[X]} (hf : Hyp p d f) (hp2 : p ≠ 2) {c : ℤ}
    (hc : ¬ (p : ℤ) ∣ c) (h2d : 2 * d < p) : Hyp p (2 * d) (f.comp (C c * X ^ 2)) := by
  have : Fact p.Prime := ⟨hf.prime⟩
  have hpZ : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hf.prime)
  have hc0 : c ≠ 0 := by rintro rfl; exact hc (dvd_zero _)
  have hq : (C c * X ^ 2 : ℤ[X]).natDegree = 2 := natDegree_C_mul_X_pow 2 c hc0
  have hcbar : ((c : ZMod p)) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hqbar : (C (c : ZMod p) * X ^ 2).natDegree = 2 := natDegree_C_mul_X_pow 2 _ hcbar
  have hmap : (f.comp (C c * X ^ 2)).map (Int.castRingHom (ZMod p)) =
      (f.map (Int.castRingHom (ZMod p))).comp (C (c : ZMod p) * X ^ 2) := by
    rw [Polynomial.map_comp]; simp
  have hdeg : (f.comp (C c * X ^ 2)).natDegree = 2 * f.natDegree := by
    rw [natDegree_comp, hq, mul_comm]
  have hlc : (f.comp (C c * X ^ 2)).leadingCoeff = f.leadingCoeff * c ^ f.natDegree := by
    rw [leadingCoeff_comp (by rw [hq]; norm_num), leadingCoeff_C_mul_X_pow]
  have hcoeff0 : (f.comp (C c * X ^ 2)).coeff 0 = f.coeff 0 := by
    rw [coeff_zero_eq_eval_zero, eval_comp, coeff_zero_eq_eval_zero]; simp
  refine ⟨hf.prime, ?_, ?_, ?_, ?_, ?_, by have := hf.pos; omega, h2d⟩
  · rw [hcoeff0]; exact hf.coeff_zero
  · rw [hlc]; exact dvd_mul_of_dvd_left hf.dvd_lead _
  · rw [hlc]
    intro h
    have hcop : IsCoprime ((p : ℤ) ^ 2) (c ^ f.natDegree) :=
      ((Prime.coprime_iff_not_dvd hpZ).mpr hc).pow
    exact hf.not_sq_dvd_lead (hcop.dvd_of_dvd_mul_right h)
  · rw [hmap, natDegree_comp, hqbar, hdeg]
    have := hf.natDegree_eq
    omega
  · rw [hmap]
    have hsep : (f.map (Int.castRingHom (ZMod p))).Separable :=
      PerfectField.separable_iff_squarefree.mpr hf.squarefree
    apply Polynomial.Separable.squarefree
    set F := f.map (Int.castRingHom (ZMod p)) with hF
    set q := C (c : ZMod p) * X ^ 2 with hq_def
    rw [Polynomial.Separable, derivative_comp]
    apply IsCoprime.mul_right
    · rw [hq_def, derivative_C_mul_X_pow]
      apply IsCoprime.mul_right
      · have h2c : ((c : ZMod p) * ((2 : ℕ) : ZMod p)) ≠ 0 := by
          refine mul_ne_zero hcbar ?_
          rw [Ne, ZMod.natCast_eq_zero_iff]
          intro h
          have := Nat.le_of_dvd (by norm_num) h
          have := hf.prime.two_le
          omega
        refine ⟨0, C ((c : ZMod p) * ((2 : ℕ) : ZMod p))⁻¹, ?_⟩
        rw [zero_mul, zero_add, ← C_mul, inv_mul_cancel₀ h2c, C_1]
      · rw [show 2 - 1 = 1 from rfl, pow_one]
        refine ((Prime.coprime_iff_not_dvd prime_X).mpr ?_).symm
        rw [X_dvd_iff, coeff_zero_eq_eval_zero, eval_comp, ← hq_def]
        have : q.eval 0 = 0 := by simp [hq_def]
        rw [this, ← coeff_zero_eq_eval_zero, hF, coeff_map]
        rw [eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact hf.coeff_zero
    · exact (show IsCoprime F (derivative F) from hsep).map (compRingHom q)

/-- If `τ` is a single `2d`-cycle commuting with a fixed-point-free involution `ν`, then
`τ ^ d = ν` on the support of `τ`. -/
theorem pow_apply_eq_of_commute {α : Type*} [Fintype α] [DecidableEq α] {d : ℕ}
    {τ ν : Equiv.Perm α} (hcyc : τ.IsCycle) (hcard : τ.support.card = 2 * d)
    (hcomm : Commute τ ν) (hνν : ν * ν = 1) (hνne : ∀ y, ν y ≠ y) :
    ∀ x ∈ τ.support, (τ ^ d) x = ν x := by
  have hνinv : ∀ y, ν (ν y) = y := fun y => by
    rw [← Equiv.Perm.mul_apply, hνν, Equiv.Perm.one_apply]
  have hcommz : ∀ (n : ℤ) (y : α), (τ ^ n) (ν y) = ν ((τ ^ n) y) := by
    intro n y
    have := (hcomm.zpow_left n).eq
    exact congrArg (fun π : Equiv.Perm _ => π y) this
  have hνsupp : ∀ y ∈ τ.support, ν y ∈ τ.support := by
    intro y hy
    rw [Equiv.Perm.mem_support] at hy ⊢
    intro h
    apply hy
    have := hcommz 1 y
    simp only [zpow_one] at this
    rw [this] at h
    exact ν.injective h
  intro x hx
  obtain ⟨j, hj⟩ := hcyc.sameCycle (Equiv.Perm.mem_support.mp hx)
    (Equiv.Perm.mem_support.mp (hνsupp x hx))
  have hall : ∀ y ∈ τ.support, (τ ^ j) y = ν y := by
    intro y hy
    obtain ⟨i, rfl⟩ := hcyc.sameCycle (Equiv.Perm.mem_support.mp hx)
      (Equiv.Perm.mem_support.mp hy)
    rw [← Equiv.Perm.mul_apply, ← zpow_add, add_comm, zpow_add, Equiv.Perm.mul_apply, hj,
      hcommz]
  have h2j : τ ^ (2 * j) = 1 := by
    ext y : 1
    by_cases hy : y ∈ τ.support
    · rw [two_mul, zpow_add, Equiv.Perm.mul_apply, hall y hy, hall _ (hνsupp y hy),
        Equiv.Perm.one_apply, hνinv]
    · rw [Equiv.Perm.notMem_support] at hy
      rw [Equiv.Perm.one_apply]
      exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hy _
  have hord : orderOf τ = 2 * d := by rw [hcyc.orderOf, hcard]
  have hdvd : ((2 * d : ℕ) : ℤ) ∣ 2 * j := by
    rw [← hord]; exact orderOf_dvd_iff_zpow_eq_one.mpr h2j
  have hτ2d : τ ^ ((2 * d : ℕ) : ℤ) = 1 := by rw [zpow_natCast, ← hord, pow_orderOf_eq_one]
  obtain ⟨m, hm⟩ : (d : ℤ) ∣ j := by
    obtain ⟨k, hk⟩ := hdvd
    exact ⟨k, by push_cast at hk; linarith⟩
  rcases Int.even_or_odd m with ⟨m', hm'⟩ | ⟨m', hm'⟩
  · exfalso
    have : τ ^ j = 1 := by
      rw [hm, hm', show (d : ℤ) * (m' + m') = ((2 * d : ℕ) : ℤ) * m' by push_cast; ring,
        zpow_mul, hτ2d, one_zpow]
    rw [this, Equiv.Perm.one_apply] at hj
    exact hνne x hj.symm
  · have : τ ^ j = τ ^ d := by
      rw [hm, hm', show (d : ℤ) * (2 * m' + 1) = ((2 * d : ℕ) : ℤ) * m' + d by push_cast; ring,
        zpow_add, zpow_mul, hτ2d, one_zpow, one_mul, zpow_natCast]
    rw [this] at hj
    exact hj

open Classical in
/-- In `Gal(f(cX²)/ℚ)` with `f(0) ≠ 0`, if `σ` acts on the roots as a single `2d`-cycle then
`σ ^ d` is negation on the support of this cycle. -/
theorem galPerm_comp_pow_apply_eq_neg {d : ℕ} {f : ℤ[X]} {c : ℤ} (h0 : f.coeff 0 ≠ 0)
    (σ : ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)).Gal)
    (hcyc : (galPerm ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)) σ).IsCycle)
    (hcard : (galPerm ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)) σ).support.card = 2 * d) :
    ∀ x ∈ (galPerm ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)) σ).support,
      ((galPerm ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)) σ ^ d) x :
        ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)).SplittingField) =
        -(x : ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)).SplittingField) := by
  classical
  revert σ
  set gQ := ((f.comp (C c * X ^ 2)).map (Int.castRingHom ℚ)) with hgQ
  set L := gQ.SplittingField with hL
  intro σ hcyc hcard
  have hgQeval : ∀ x : L, aeval x gQ = aeval (c * x ^ 2) f := by
    intro x
    change aeval x ((f.comp (C c * X ^ 2)).map (algebraMap ℤ ℚ)) = _
    rw [aeval_map_algebraMap, aeval_comp]
    simp
  have hneg_root : ∀ x : L, x ∈ gQ.rootSet L → -x ∈ gQ.rootSet L := by
    intro x hx
    rw [mem_rootSet] at hx ⊢
    refine ⟨hx.1, ?_⟩
    rw [hgQeval, neg_sq, ← hgQeval]
    exact hx.2
  have hroot_ne : ∀ x : gQ.rootSet L, (x : L) ≠ 0 := by
    intro x h
    have hx := (mem_rootSet.mp x.2).2
    rw [hgQeval, h] at hx
    rw [zero_pow two_ne_zero, mul_zero, ← coeff_zero_eq_aeval_zero', eq_intCast,
      Int.cast_eq_zero] at hx
    exact h0 hx
  -- negation as a permutation of the roots, commuting with `τ`
  let ν : Equiv.Perm (gQ.rootSet L) :=
    { toFun := fun x => ⟨-(x : L), hneg_root x x.2⟩
      invFun := fun x => ⟨-(x : L), hneg_root x x.2⟩
      left_inv := fun x => Subtype.ext (neg_neg _)
      right_inv := fun x => Subtype.ext (neg_neg _) }
  have hνapp : ∀ x, ((ν x : gQ.rootSet L) : L) = -(x : L) := fun x => rfl
  have hcomm : Commute (galPerm gQ σ) ν := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change σ (-(x : L)) = -(σ (x : L))
    exact map_neg σ _
  have hνne : ∀ y, ν y ≠ y := by
    intro y h
    have h' := congrArg Subtype.val h
    rw [hνapp] at h'
    have h2 : (2 : L) * (y : L) = 0 := by
      rw [two_mul]; nth_rewrite 1 [← h']; ring
    rcases mul_eq_zero.mp h2 with h2 | h2
    · exact two_ne_zero h2
    · exact hroot_ne y h2
  have hνν : ν * ν = 1 := Equiv.ext fun y => Subtype.ext (neg_neg _)
  intro x hx
  rw [pow_apply_eq_of_commute hcyc hcard hcomm hνν hνne x hx, hνapp]

end InertiaCycle

end ArithmeticOfJacobiPolynomials
