/- Assembled by AxiomProver. -/
module

public import StacksFrontier.RingTheory.Henselian.Characterizations
public import Mathlib

/-!
# The Hensel factorization and the Eisenstein factor over `ℤ_[p]` (Lemmas 5.1 and 5.16)

Both Lemma 5.1 (the reciprocal polynomial `R = Y^N f(1/Y)/a₀`, reduction `Y^d B̄`) and the wild
step of Lemma 5.16 (the monic normalization of `f`, reduction `x^p Ḡ`) use the same source step:
"Hensel factorization gives `R = A B` with `A, B` monic, `deg A = d`, `A ≡ Y^d (mod p)`; since
`B(0)` is a unit and `v_p(R(0)) = 1`, the polynomial `A` is Eisenstein."

`ℤ_[p]` is a Henselian local ring (`instHenselianLocalRing`, from Mathlib's adic completeness).
For every Henselian local ring, coprime factorizations of the reduction lift
(`IsLocalRing.henselian_tfae`, Tag 03QH, condition (2) `HasCoprimeFactorizationLifting`), which
gives `coprimeFactorizationLifting_padicInt`. `exists_monic_eisenstein_factor_of_pow` is the source
step (a monic Eisenstein factor of any degree `d`; `exists_monic_eisenstein_factor` is its
degree-`p` case).
-/

public section

open Polynomial renaming X → polyX

namespace ArithmeticOfJacobiPolynomials

open Polynomial IsLocalRing

variable {p : ℕ} [Fact p.Prime]

/-- `ℤ_[p]` is a Henselian local ring (Mathlib: `ℤ_[p]` is adically complete at its maximal
ideal). -/
instance instHenselianLocalRingPadicInt : HenselianLocalRing ℤ_[p] where
  is_henselian f hf a₀ h₁ h₂ := by
    have H := (inferInstance : HenselianRing ℤ_[p] (maximalIdeal ℤ_[p])).is_henselian f hf a₀ h₁
      (h₂.map (Ideal.Quotient.mk _))
    exact H

/-- **Hensel's lemma for coprime factorizations over `ℤ_[p]`**, from the Stacks library
(`IsLocalRing.henselian_tfae`, Tag 03QH, items 1 and 2). -/
theorem coprimeFactorizationLifting_padicInt :
    IsLocalRing.HasCoprimeFactorizationLifting ℤ_[p] := by
  have h := (IsLocalRing.henselian_tfae.{0, 0} ℤ_[p]).out 1 2
  exact h.mp (instHenselianLocalRingPadicInt (p := p))

/-- An element of `ℤ_[p]` reduces to zero in the residue field iff `p` divides it. -/
theorem residue_eq_zero_iff_dvd (a : ℤ_[p]) : residue ℤ_[p] a = 0 ↔ (p : ℤ_[p]) ∣ a := by
  rw [residue_eq_zero_iff, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]

/-- **The monic Eisenstein factor of degree `d`** (source step of Lemma 5.1 with `d < p`, and of
Lemma 5.16 with `d = p`: "Hensel factorization gives `R = A B` with `A, B` monic, `deg A = d` and
`A ≡ Y^d (mod p)`; since `B(0)` is a unit and `v_p(R(0)) = 1`, the polynomial `A` is Eisenstein").
Let `g ∈ ℤ_[p][X]` be monic with `p ∣ g_i` for `i < d`, `p ∥ g_0` and `g_d` a unit (so that the
reduction is `X^d · h̄` with `h̄(0) ≠ 0`). Then `g = A B` with `A` monic of degree `d`,
the reduction of `A` equal to `X^d`, `B(0) ≠ 0` and `A` Eisenstein at the maximal ideal of
`ℤ_[p]`. -/
theorem exists_monic_eisenstein_factor_of_pow {g : ℤ_[p][X]} {d : ℕ} (hg : g.Monic)
    (hlow : ∀ i < d, (p : ℤ_[p]) ∣ g.coeff i) (h0 : ¬ (p : ℤ_[p]) ^ 2 ∣ g.coeff 0)
    (hdd : IsUnit (g.coeff d)) :
    ∃ A B : ℤ_[p][X], g = A * B ∧ A.Monic ∧ A.natDegree = d ∧
      A.map (residue ℤ_[p]) = polyX ^ d ∧ B.Monic ∧ IsUnit (B.coeff 0) ∧
      A.IsEisensteinAt (maximalIdeal ℤ_[p]) := by
  have hdvd : (polyX : (ResidueField ℤ_[p])[X]) ^ d ∣ g.map (residue ℤ_[p]) := by
    rw [X_pow_dvd_iff]
    intro i hi
    rw [coeff_map, (residue_eq_zero_iff_dvd _).mpr (hlow i hi)]
  obtain ⟨h₀, hh₀⟩ := hdvd
  have hh0 : h₀.coeff 0 ≠ 0 := by
    have h1 := congrArg (fun q => q.coeff d) hh₀
    simp only [coeff_map, coeff_X_pow_mul'] at h1
    simp only [le_refl, ite_true, Nat.sub_self] at h1
    rw [← h1]
    intro h
    exact (residue_eq_zero_iff_dvd _).mp h |> fun hd' => PadicInt.prime_p.not_isUnit
      (isUnit_of_dvd_unit hd' hdd)
  have hcop : IsCoprime ((polyX : (ResidueField ℤ_[p])[X]) ^ d) h₀ := by
    refine IsCoprime.pow_left ?_
    rw [irreducible_X.coprime_iff_not_dvd, X_dvd_iff]
    exact hh0
  obtain ⟨A₁, B₁, hAB, hA₁, hB₁⟩ :=
    coprimeFactorizationLifting_padicInt g (polyX ^ d) h₀ hh₀ hcop
  have hlc : A₁.leadingCoeff * B₁.leadingCoeff = 1 := by
    rw [← leadingCoeff_mul, ← hAB]; exact hg
  have hAlc : residue ℤ_[p] A₁.leadingCoeff ≠ 0 := by
    intro h
    have := congrArg (residue ℤ_[p]) hlc
    rw [map_mul, h, zero_mul, map_one] at this
    exact zero_ne_one this
  have hdeg₁ : A₁.natDegree = d := by
    have h1 := natDegree_map_of_leadingCoeff_ne_zero (residue ℤ_[p]) hAlc
    rw [hA₁, natDegree_X_pow] at h1
    exact h1.symm
  -- normalize `A₁` to be monic
  obtain ⟨v, hv⟩ : IsUnit A₁.leadingCoeff := notMem_maximalIdeal.mp (by
    rw [← residue_eq_zero_iff] at *; exact fun h => hAlc (by simpa [residue_eq_zero_iff] using h))
  have hcoeffd : A₁.coeff d = (v : ℤ_[p]) := by
    have h := hv
    rw [leadingCoeff, hdeg₁] at h
    exact h.symm
  have hres_v : residue ℤ_[p] (v : ℤ_[p]) = 1 := by
    have := congrArg (fun q => q.coeff d) hA₁
    simp only [coeff_map, coeff_X_pow, ite_true] at this
    rw [← hcoeffd]; exact this
  refine ⟨C ((v⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * A₁, C (v : ℤ_[p]) * B₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc g = A₁ * B₁ := hAB
      _ = C ((v⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * A₁ * (C (v : ℤ_[p]) * B₁) := by
        rw [mul_mul_mul_comm, ← C_mul, Units.inv_mul, C_1, one_mul]
  · rw [Monic, leadingCoeff_mul, leadingCoeff_C, ← hv, Units.inv_mul]
  · rw [natDegree_C_mul (Units.ne_zero _), hdeg₁]
  · rw [Polynomial.map_mul, Polynomial.map_C, hA₁]
    have : residue ℤ_[p] ((v⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
      have h1 : residue ℤ_[p] ((v⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * residue ℤ_[p] (v : ℤ_[p]) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      rwa [hres_v, mul_one] at h1
    rw [this, C_1, one_mul]
  · -- `B` is monic, since `g` and the new `A` are
    have hAm : (C ((v⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * A₁).Monic := by
      rw [Monic, leadingCoeff_mul, leadingCoeff_C, ← hv, Units.inv_mul]
    have hprod : (C ((v⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * A₁ * (C (v : ℤ_[p]) * B₁)).Monic := by
      rw [← mul_mul_mul_comm, ← C_mul, Units.inv_mul, C_1, one_mul, ← hAB]; exact hg
    exact hAm.of_mul_monic_left hprod
  · have := congrArg (fun q => q.coeff 0) hB₁
    simp only [coeff_map] at this
    refine notMem_maximalIdeal.mp fun hmem => ?_
    rw [coeff_C_mul, ← residue_eq_zero_iff, map_mul, hres_v, one_mul, this] at hmem
    exact hh0 hmem
  · refine ⟨?_, fun {n} hn => ?_, ?_⟩
    · rw [leadingCoeff, natDegree_C_mul (Units.ne_zero _), hdeg₁, coeff_C_mul, hcoeffd,
        Units.inv_mul]
      exact fun h => (IsLocalRing.maximalIdeal.isMaximal ℤ_[p]).ne_top
        ((Ideal.eq_top_iff_one _).mpr h)
    · rw [coeff_C_mul]
      refine Ideal.mul_mem_left _ _ ?_
      rw [natDegree_C_mul (Units.ne_zero _), hdeg₁] at hn
      have := congrArg (fun q => q.coeff n) hA₁
      have hne : n ≠ d := by omega
      simp only [coeff_map, coeff_X_pow, hne, ↓reduceIte] at this
      exact (residue_eq_zero_iff _).mp this
    · rw [coeff_C_mul]
      intro hmem
      apply h0
      have hmul : g.coeff 0 = A₁.coeff 0 * B₁.coeff 0 := by rw [hAB, mul_coeff_zero]
      have h2 : g.coeff 0 ∈ maximalIdeal ℤ_[p] ^ 2 := by
        rw [hmul]
        have : A₁.coeff 0 = (v : ℤ_[p]) * (((v⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * A₁.coeff 0) := by
          rw [← mul_assoc, Units.mul_inv, one_mul]
        rw [this]
        exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hmem)
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton] at h2
      exact h2

/-- **The monic Eisenstein factor of degree `p`** (the case `d = p` of
`exists_monic_eisenstein_factor_of_pow`, used for the wild cycle of Lemma 5.16). -/
theorem exists_monic_eisenstein_factor {g : ℤ_[p][X]} (hg : g.Monic)
    (hlow : ∀ i < p, (p : ℤ_[p]) ∣ g.coeff i) (h0 : ¬ (p : ℤ_[p]) ^ 2 ∣ g.coeff 0)
    (hpp : IsUnit (g.coeff p)) :
    ∃ A B : ℤ_[p][X], g = A * B ∧ A.Monic ∧ A.natDegree = p ∧
      A.IsEisensteinAt (maximalIdeal ℤ_[p]) := by
  obtain ⟨A, B, hAB, hm, hdeg, -, -, -, hE⟩ :=
    exists_monic_eisenstein_factor_of_pow (d := p) hg hlow h0 hpp
  exact ⟨A, B, hAB, hm, hdeg, hE⟩

end ArithmeticOfJacobiPolynomials
