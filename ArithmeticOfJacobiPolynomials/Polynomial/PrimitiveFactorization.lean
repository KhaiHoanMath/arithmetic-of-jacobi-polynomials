/- Assembled by AxiomProver. -/
module

public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.Algebra.GCDMonoid.Nat

/-!
# Primitive integral factorizations

The irreducibility proofs of the manuscript (Sections 3 and 4) start from a hypothetical
factorization `H = F G` of a primitive integral multiple `H = κ h` of the polynomial
`h ∈ ℚ[X]`, with `F, G ∈ ℤ[X]` primitive, with positive leading coefficients and
`1 ≤ deg F ≤ deg G`, and derive a contradiction. This file proves the corresponding
reduction (Gauss's lemma): if no such factorization exists, `h` is irreducible over `ℚ`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

/-- A nonunit primitive integer polynomial has positive degree. -/
theorem one_le_natDegree_of_isPrimitive {F : ℤ[X]} (hF : F.IsPrimitive) (hu : ¬ IsUnit F) :
    1 ≤ F.natDegree := by
  by_contra h0
  push Not at h0
  have h0' : F.natDegree = 0 := by omega
  apply hu
  rw [eq_C_of_natDegree_eq_zero h0'] at hF ⊢
  exact isUnit_C.mpr (isPrimitive_iff_isUnit_of_C_dvd.mp hF _ dvd_rfl)

/-- **Reduction to primitive factorizations.** Let `h ∈ ℚ[X]` have positive degree and positive
leading coefficient, and suppose `P = c h` for some `P ∈ ℤ[X]` and `c > 0`. If there is no
factorization `H = F G` of a primitive `H ∈ ℤ[X]` with `H = κ h`, `κ > 0`, into primitive
`F, G ∈ ℤ[X]` with positive leading coefficients and `1 ≤ deg F ≤ deg G`, then `h` is
irreducible over `ℚ`. -/
theorem irreducible_of_forall_primitive_factorization {h : ℚ[X]} (hdeg : 1 ≤ h.natDegree)
    (hlc : 0 < h.leadingCoeff) {c : ℚ} (hc : 0 < c) {P : ℤ[X]}
    (hP : P.map (Int.castRingHom ℚ) = C c * h)
    (hno : ∀ (κ : ℚ) (H F G : ℤ[X]), 0 < κ → H.map (Int.castRingHom ℚ) = C κ * h →
      H.IsPrimitive → H = F * G → F.IsPrimitive → G.IsPrimitive → 0 < F.leadingCoeff →
      0 < G.leadingCoeff → 1 ≤ F.natDegree → F.natDegree ≤ G.natDegree → False) :
    Irreducible h := by
  have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have hh0 : h ≠ 0 := by rintro rfl; simp at hdeg
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp only [Polynomial.map_zero] at hP
    exact mul_ne_zero (C_ne_zero.mpr hc.ne') hh0 hP.symm
  set H := P.primPart with hHdef
  have hHprim : H.IsPrimitive := isPrimitive_primPart P
  have hcont0 : P.content ≠ 0 := content_eq_zero_iff.not.mpr hP0
  have hcont : 0 < P.content :=
    lt_of_le_of_ne (Int.nonneg_of_normalize_eq_self normalize_content) (Ne.symm hcont0)
  set κ : ℚ := c / P.content with hκ
  have hκpos : 0 < κ := div_pos hc (by exact_mod_cast hcont)
  have hcq : ((P.content : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hcont0
  have e : C c * h = C ((P.content : ℤ) : ℚ) * H.map (Int.castRingHom ℚ) := by
    rw [← hP]
    conv_lhs => rw [P.eq_C_content_mul_primPart]
    rw [Polynomial.map_mul, Polynomial.map_C, eq_intCast]
  have hHmap : H.map (Int.castRingHom ℚ) = C κ * h := by
    calc H.map (Int.castRingHom ℚ) = C (1 / ((P.content : ℤ) : ℚ)) *
          (C ((P.content : ℤ) : ℚ) * H.map (Int.castRingHom ℚ)) := by
          rw [← mul_assoc, ← C_mul, one_div_mul_cancel hcq, C_1, one_mul]
      _ = C κ * h := by
          rw [← e, ← mul_assoc, ← C_mul, hκ]
          congr 2
          ring
  have hκunit : IsUnit (C κ) := isUnit_C.mpr (IsUnit.mk0 _ hκpos.ne')
  have hHdeg : H.natDegree = h.natDegree := by
    rw [← natDegree_map_eq_of_injective hinj, hHmap, natDegree_C_mul hκpos.ne']
  have hHlc : 0 < H.leadingCoeff := by
    have e := leadingCoeff_map_of_injective hinj H
    rw [hHmap, leadingCoeff_mul, leadingCoeff_C, eq_intCast] at e
    have : (0 : ℚ) < (H.leadingCoeff : ℚ) := by
      rw [← e]; exact mul_pos hκpos hlc
    exact_mod_cast this
  rw [← irreducible_isUnit_mul hκunit, ← hHmap, ← algebraMap_int_eq,
    ← hHprim.irreducible_iff_irreducible_map_fraction_map]
  by_contra hirr
  have hHu : ¬ IsUnit H := fun hu => by
    have := natDegree_eq_zero_of_isUnit hu; omega
  obtain ⟨F, G, hFG, hFu, hGu⟩ : ∃ F G, H = F * G ∧ ¬ IsUnit F ∧ ¬ IsUnit G := by
    by_contra hcon
    push Not at hcon
    apply hirr
    refine irreducible_iff.mpr ⟨hHu, fun a b hab => ?_⟩
    by_contra hab'
    push Not at hab'
    exact hab'.2 (hcon a b hab hab'.1)
  -- signs
  obtain ⟨F, G, hFG, hFu, hGu, hFlc, hGlc⟩ : ∃ F G : ℤ[X], H = F * G ∧ ¬ IsUnit F ∧
      ¬ IsUnit G ∧ 0 < F.leadingCoeff ∧ 0 < G.leadingCoeff := by
    have hlcFG : F.leadingCoeff * G.leadingCoeff = H.leadingCoeff := by
      rw [hFG, leadingCoeff_mul]
    rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr
        (show F ≠ 0 by rintro rfl; rw [zero_mul] at hFG; exact hHprim.ne_zero hFG)) with hneg | hpos
    · refine ⟨-F, -G, by rw [hFG]; ring, fun h' => hFu (by simpa using h'.neg),
        fun h' => hGu (by simpa using h'.neg), ?_, ?_⟩
      · rw [leadingCoeff_neg]; linarith
      · rw [leadingCoeff_neg]
        by_contra hG
        push Not at hG
        nlinarith
    · refine ⟨F, G, hFG, hFu, hGu, hpos, ?_⟩
      by_contra hG
      push Not at hG
      nlinarith
  have hFprim : F.IsPrimitive := isPrimitive_of_dvd hHprim (Dvd.intro G hFG.symm)
  have hGprim : G.IsPrimitive := isPrimitive_of_dvd hHprim (Dvd.intro_left F hFG.symm)
  have hF1 := one_le_natDegree_of_isPrimitive hFprim hFu
  have hG1 := one_le_natDegree_of_isPrimitive hGprim hGu
  rcases le_total F.natDegree G.natDegree with hle | hle
  · exact hno κ H F G hκpos hHmap hHprim hFG hFprim hGprim hFlc hGlc hF1 hle
  · exact hno κ H G F hκpos hHmap hHprim (by rw [hFG, mul_comm]) hGprim hFprim hGlc hFlc hG1 hle

end ArithmeticOfJacobiPolynomials
