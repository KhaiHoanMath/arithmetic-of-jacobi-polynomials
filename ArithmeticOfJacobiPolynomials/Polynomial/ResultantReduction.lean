/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Polynomial.ReductionMultiplicity
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Polynomial.Content

/-!
# Resultants of factors whose reductions have no common projective root

Let `φ : R →+* K` be a "reduction map" to an algebraically closed field, with kernel the
multiples of an element `π` (for instance `ℤ_[p] → \bar{𝔽}_p` or `ℤ → \bar{𝔽}_p` with `π = p`).

* `map_resultant_ne_zero_of_isCoprime_reduction`: if the reductions of `A, B ∈ R[X]` have no
  common root in `K` and not both leading coefficients reduce to zero (no common root at
  infinity), then `Res(A,B)` does not reduce to zero. This uses that reduction commutes with
  the resultant taken with the original degrees.
* `map_resultant_ne_zero_of_reduction`: the "root-mass" step of the manuscript in the
  equivalent form used here: if `H = AB` and both `A` and `B` reduce to zero at a point `c`,
  then `π² ∣ H(c)`; similarly at infinity with the leading coefficients. So if every multiple
  root of `\bar H` is the reduction of a point `c` with `π² ∤ H(c)`, and `π² ∤ lc H`, then
  `π ∤ Res(A,B)`. (This replaces the root-mass identities (3.3): a total root-valuation of at
  most `1` in a residue class cannot be shared by two factors.)
* `padicInt_not_dvd_resultant_of_ode`: **Lemma 4.3**.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

section General

variable {R K : Type*} [CommRing R] [Field K] [IsAlgClosed K] (φ : R →+* K)

/-- If the reductions of `A` and `B` have no common root in the algebraically closed field `K`
and they do not both drop degree, then the resultant of `A` and `B` does not reduce to zero. -/
theorem map_resultant_ne_zero_of_isCoprime_reduction {A B : R[X]}
    (hroot : ∀ ξ : K, (A.map φ).eval ξ ≠ 0 ∨ (B.map φ).eval ξ ≠ 0)
    (hlc : φ A.leadingCoeff ≠ 0 ∨ φ B.leadingCoeff ≠ 0) :
    φ (resultant A B) ≠ 0 := by
  rw [← resultant_map_map]
  have hcop : IsCoprime (A.map φ) (B.map φ) :=
    (isCoprime_iff_aeval_ne_zero_of_isAlgClosed K K _ _).mpr fun a => by
      simpa only [coe_aeval_eq_eval] using hroot a
  have hres : resultant (A.map φ) (B.map φ) ≠ 0 := resultant_ne_zero _ _ hcop
  rcases hlc with hA | hB
  · have hdA : (A.map φ).natDegree = A.natDegree := natDegree_map_of_leadingCoeff_ne_zero φ hA
    obtain ⟨k, hk⟩ : ∃ k, B.natDegree = (B.map φ).natDegree + k :=
      ⟨_, (Nat.add_sub_of_le (natDegree_map_le)).symm⟩
    rw [hk, resultant_add_right_deg _ _ _ _ _ le_rfl, ← hdA]
    refine mul_ne_zero (pow_ne_zero _ ?_) hres
    rw [hdA, coeff_map]
    exact hA
  · have hdB : (B.map φ).natDegree = B.natDegree := natDegree_map_of_leadingCoeff_ne_zero φ hB
    obtain ⟨k, hk⟩ : ∃ k, A.natDegree = (A.map φ).natDegree + k :=
      ⟨_, (Nat.add_sub_of_le (natDegree_map_le)).symm⟩
    rw [hk, resultant_add_left_deg _ _ _ _ _ le_rfl, ← hdB]
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (pow_ne_zero _ ?_)) hres
    rw [hdB, coeff_map]
    exact hB

variable [IsDomain R]

/-- **Exclusion of common reduced roots.** Let `φ` have kernel `π R` and `H = A B`. Suppose
`\bar H ≠ 0`, every multiple root of `\bar H` is the reduction of some `c ∈ R` with
`π² ∤ H(c)`, and `π² ∤ lc H`. Then `Res(A,B)` does not reduce to zero. -/
theorem map_resultant_ne_zero_of_reduction (π : R) (hφ : ∀ a, φ a = 0 ↔ π ∣ a) {A B : R[X]}
    (hH : (A * B).map φ ≠ 0)
    (hmult : ∀ ξ : K, 2 ≤ ((A * B).map φ).rootMultiplicity ξ →
      ∃ c : R, φ c = ξ ∧ ¬ π ^ 2 ∣ (A * B).eval c)
    (hlc : ¬ π ^ 2 ∣ (A * B).leadingCoeff) :
    φ (resultant A B) ≠ 0 := by
  refine map_resultant_ne_zero_of_isCoprime_reduction φ (fun ξ => ?_) ?_
  · by_contra h
    push Not at h
    obtain ⟨hAξ, hBξ⟩ := h
    have hdvd : (X - C ξ) ^ 2 ∣ (A * B).map φ := by
      rw [Polynomial.map_mul, sq]
      exact mul_dvd_mul (dvd_iff_isRoot.mpr hAξ) (dvd_iff_isRoot.mpr hBξ)
    obtain ⟨c, rfl, hc⟩ := hmult ξ ((le_rootMultiplicity_iff hH).mpr hdvd)
    apply hc
    have hA : π ∣ A.eval c := (hφ _).mp (by rw [← hAξ, eval_map, eval₂_hom])
    have hB : π ∣ B.eval c := (hφ _).mp (by rw [← hBξ, eval_map, eval₂_hom])
    rw [eval_mul, sq]
    exact mul_dvd_mul hA hB
  · by_contra h
    push Not at h
    apply hlc
    rw [leadingCoeff_mul, sq]
    exact mul_dvd_mul ((hφ _).mp h.1) ((hφ _).mp h.2)

omit [IsAlgClosed K] [IsDomain R] in
/-- A polynomial whose reduction vanishes is divisible by `C π`; so the reduction of a
primitive polynomial is nonzero when `π` is not a unit. -/
theorem map_ne_zero_of_isPrimitive (π : R) (hφ : ∀ a, φ a = 0 ↔ π ∣ a) (hπ : ¬ IsUnit π)
    {H : R[X]} (hH : H.IsPrimitive) : H.map φ ≠ 0 := by
  intro h
  apply hπ
  refine hH π ((C_dvd_iff_dvd_coeff _ _).mpr fun i => (hφ _).mp ?_)
  rw [← coeff_map, h, coeff_zero]

end General

section Padic

variable (p : ℕ) [Fact p.Prime]

/-- The reduction map `ℤ_[p] → \bar{𝔽}_p`. -/
noncomputable def padicIntReduction : ℤ_[p] →+* AlgebraicClosure (ZMod p) :=
  (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).comp PadicInt.toZMod

theorem padicIntReduction_eq_zero_iff (a : ℤ_[p]) :
    padicIntReduction p a = 0 ↔ (p : ℤ_[p]) ∣ a := by
  rw [padicIntReduction, RingHom.comp_apply, map_eq_zero,
    ← ZMod.val_eq_zero, PadicInt.val_toZMod_eq_zmodRepr, PadicInt.zmodRepr_eq_zero_iff_dvd]

/-- **Lemma 4.3**. Let `H ∈ ℤ_p[t]` be primitive of
degree `< p` satisfying `t(1-t)H'' + τ(t)H' + ΛH = 0` with `τ ∈ ℤ_p[t]`, `Λ ∈ ℤ_p`. If
`v_p(H(0)) ≤ 1`, `v_p(H(1)) ≤ 1` and `v_p(lc H) ≤ 1` (i.e. `p²` divides none of them), then
every factorization `H = AB` in `ℤ_p[t]` (necessarily into primitive factors) satisfies
`v_p(Res(A,B)) = 0`. -/
theorem padicInt_not_dvd_resultant_of_ode {H A B τ : ℤ_[p][X]} {Λ : ℤ_[p]}
    (hprim : H.IsPrimitive) (hdeg : H.natDegree < p)
    (hode : X * (1 - X) * derivative (derivative H) + τ * derivative H + C Λ * H = 0)
    (h0 : ¬ (p : ℤ_[p]) ^ 2 ∣ H.eval 0) (h1 : ¬ (p : ℤ_[p]) ^ 2 ∣ H.eval 1)
    (hlc : ¬ (p : ℤ_[p]) ^ 2 ∣ H.leadingCoeff) (hAB : H = A * B) :
    ¬ (p : ℤ_[p]) ∣ resultant A B := by
  have hp := (Fact.out : p.Prime)
  set φ := padicIntReduction p
  have hφ := padicIntReduction_eq_zero_iff p
  have hpu : ¬ IsUnit (p : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_p]
    exact ne_of_lt (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt))
  have hH : H.map φ ≠ 0 := map_ne_zero_of_isPrimitive φ _ hφ hpu hprim
  have hode' : (X * (1 - X)) * derivative (derivative (H.map φ)) +
      τ.map φ * derivative (H.map φ) + C (φ Λ) * H.map φ = 0 := by
    have := congrArg (Polynomial.map φ) hode
    simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_one, Polynomial.map_C, derivative_map, Polynomial.map_zero] using this
  have hdeg' : (H.map φ).natDegree < p := lt_of_le_of_lt natDegree_map_le hdeg
  rw [← hφ]
  subst hAB
  refine map_resultant_ne_zero_of_reduction φ _ hφ hH (fun ξ hξ => ?_) hlc
  by_cases hσ : (X * (1 - X) : (AlgebraicClosure (ZMod p))[X]).eval ξ = 0
  · simp only [eval_mul, eval_X, eval_sub, eval_one, mul_eq_zero, sub_eq_zero] at hσ
    rcases hσ with rfl | rfl
    · exact ⟨0, map_zero φ, h0⟩
    · exact ⟨1, map_one φ, h1⟩
  · have := rootMultiplicity_le_one_of_ode p hp hode' hH hdeg' hσ
    omega

end Padic

end ArithmeticOfJacobiPolynomials
