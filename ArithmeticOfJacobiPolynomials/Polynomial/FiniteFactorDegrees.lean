/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Polynomial.FactorDegrees
public import Mathlib.FieldTheory.Finite.Extension

/-!
# Lemma C.1 for explicit factorizations, and Rabin's irreducibility test

This file supplies the two facts used to apply Lemma C.1
(`ArithmeticOfJacobiPolynomials.Polynomial.FactorDegrees`) to explicit, machine-checked
factorizations of the
reductions of an integer polynomial:

* `irreducible_of_factorizations`: Lemma C.1, where the factor-degree multiset `𝒟_p` at each
  prime is given by an explicit factorization `H̄ = u · ∏ g_i` into irreducibles over `𝔽_p`.
  The proof is that of the source (Gauss's lemma, `exists_factor_of_not_irreducible`, and
  preservation of the degree of a factor whose leading coefficient survives reduction). As in
  `irreducible_of_factorDegrees_of_natDegree_eq`, squarefreeness of the reductions is not
  needed.
* `irreducible_of_rabin`, `irreducible_of_rabin_of_dvd`: Rabin's test. A polynomial `F` of degree
  `d ≥ 1` over a finite field with `q` elements is irreducible if `F ∣ X^{q^d} - X` and
  `X^{q^e} - X` is invertible modulo `F` for every proper divisor `e` of `d`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial UniqueFactorizationMonoid

/-- A divisor of `u · ∏ g_i` over a field, with `u ≠ 0` and all `g_i` irreducible, has as its
degree a subset sum of the degrees `deg g_i` (each entry used at most once). -/
theorem exists_le_sum_eq_natDegree_of_dvd_prod {K : Type*} [Field K] {u : K}
    (hu : u ≠ 0) (gs : List K[X]) (hgs : ∀ g ∈ gs, Irreducible g) (A : K[X])
    (hA : A ∣ C u * gs.prod) :
    ∃ t ≤ ((gs.map natDegree : List ℕ) : Multiset ℕ), t.sum = A.natDegree := by
  classical
  have hprod0 : gs.prod ≠ 0 := List.prod_ne_zero fun h0 => (hgs 0 h0).ne_zero rfl
  have hCu : C u ≠ 0 := by simpa using hu
  have hH0 : C u * gs.prod ≠ 0 := mul_ne_zero hCu hprod0
  have hA0 : A ≠ 0 := fun h => hH0 (zero_dvd_iff.mp (h ▸ hA))
  have hnf : normalizedFactors (C u * gs.prod) = (gs : Multiset K[X]).map normalize := by
    rw [normalizedFactors_mul hCu hprod0, normalizedFactors_of_isUnit (isUnit_C.mpr hu.isUnit),
      zero_add, ← Multiset.prod_coe,
      normalizedFactors_prod_eq _ fun a ha => hgs a (Multiset.mem_coe.mp ha)]
  have hdeg : ((gs : Multiset K[X]).map normalize).map natDegree =
      ((gs.map natDegree : List ℕ) : Multiset ℕ) := by
    rw [Multiset.map_map, Multiset.map_coe]
    congr 1
    exact List.map_congr_left fun g _ => by simp [natDegree_normalize]
  refine ⟨(normalizedFactors A).map natDegree, ?_, ?_⟩
  · have hle := (dvd_iff_normalizedFactors_le_normalizedFactors hA0 hH0).mp hA
    rw [hnf] at hle
    rw [← hdeg]
    exact Multiset.map_le_map hle
  · rw [← natDegree_multiset_prod _ (zero_notMem_normalizedFactors _)]
    exact natDegree_eq_of_degree_eq
      (degree_eq_degree_of_associated (prod_normalizedFactors hA0))

/-- **Lemma C.1 for explicit factorizations.** Let `H ∈ ℤ[X]` be primitive of degree `D ≥ 1`.
Suppose that for every `k ∈ [1, ⌊D/2⌋]` there is a prime `p` at which the reduction `H̄` of `H`
has degree `D` and factors as `u · ∏ g_i` with `u ≠ 0` and `g_i` irreducible over `𝔽_p`, such
that `k` is not a subset sum of the degrees `deg g_i` (each used at most once). Then `H` is
irreducible over `ℚ`. -/
theorem irreducible_of_factorizations (H : ℤ[X]) (hprim : H.IsPrimitive)
    (hD : 0 < H.natDegree)
    (hfac : ∀ k, 1 ≤ k → k ≤ H.natDegree / 2 →
      ∃ (p : ℕ) (_ : Fact p.Prime) (u : ZMod p) (gs : List (ZMod p)[X]),
        (H.map (Int.castRingHom (ZMod p))).natDegree = H.natDegree ∧ u ≠ 0 ∧
        (∀ g ∈ gs, Irreducible g) ∧ H.map (Int.castRingHom (ZMod p)) = C u * gs.prod ∧
        ¬ ∃ t ≤ ((gs.map natDegree : List ℕ) : Multiset ℕ), t.sum = k) :
    Irreducible (H.map (Int.castRingHom ℚ)) := by
  by_contra hred
  obtain ⟨A, B, hAB, hA1, hA2⟩ := exists_factor_of_not_irreducible H hprim hD hred
  obtain ⟨p, hfact, u, gs, hdeg, hu, hgs, hfac', hk⟩ := hfac A.natDegree hA1 hA2
  have hlcH : (Int.castRingHom (ZMod p)) H.leadingCoeff ≠ 0 := by
    rcases natDegree_map_eq_iff.mp hdeg with h | h
    · exact h
    · omega
  have hlcA : (Int.castRingHom (ZMod p)) A.leadingCoeff ≠ 0 := by
    intro h
    apply hlcH
    rw [hAB, leadingCoeff_mul, map_mul, h, zero_mul]
  have hdvd : A.map (Int.castRingHom (ZMod p)) ∣ C u * gs.prod := by
    rw [← hfac', hAB, Polynomial.map_mul]
    exact dvd_mul_right _ _
  have hmem := exists_le_sum_eq_natDegree_of_dvd_prod hu gs hgs _ hdvd
  rw [natDegree_map_of_leadingCoeff_ne_zero _ hlcA] at hmem
  exact hk hmem

/-- **Rabin's irreducibility test.** Let `F` be a polynomial of degree `d ≥ 1` over a finite
field with `q` elements. If `F ∣ X^{q^d} - X` and every proper divisor `e` of `d` divides some
`e'` for which the polynomial `X^{q^{e'}} - X` is invertible modulo `F`, then `F` is
irreducible. -/
theorem irreducible_of_rabin_of_dvd {K : Type*} [Field K] [Finite K] (F : K[X])
    (hF : 0 < F.natDegree) (hdvd : F ∣ X ^ Nat.card K ^ F.natDegree - X)
    (hcop : ∀ e, 0 < e → e < F.natDegree → e ∣ F.natDegree →
      ∃ e', e ∣ e' ∧ ∃ b : K[X], F ∣ b * (X ^ Nat.card K ^ e' - X) - 1) :
    Irreducible F := by
  have hF0 : F ≠ 0 := by rintro rfl; simp at hF
  obtain ⟨g, hg, hgF⟩ :=
    WfDvdMonoid.exists_irreducible_factor (not_isUnit_of_natDegree_pos F hF) hF0
  have hgd : g.natDegree ∣ F.natDegree :=
    hg.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X (dvd_trans hgF hdvd)
  have hgle : g.natDegree ≤ F.natDegree := natDegree_le_of_dvd hgF hF0
  rcases hgle.lt_or_eq with hlt | heq
  · exfalso
    obtain ⟨e', he', b, hb⟩ := hcop g.natDegree hg.natDegree_pos hlt hgd
    have h1 : g ∣ X ^ Nat.card K ^ e' - X :=
      hg.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp he'
    have h2 : g ∣ b * (X ^ Nat.card K ^ e' - X) - 1 := dvd_trans hgF hb
    have h3 : g ∣ 1 := by
      have := dvd_sub (dvd_mul_of_dvd_right h1 b) h2
      rwa [sub_sub_cancel] at this
    exact hg.not_isUnit (isUnit_of_dvd_one h3)
  · obtain ⟨c, rfl⟩ := hgF
    have hc0 : c ≠ 0 := by rintro rfl; simp at hF0
    rw [natDegree_mul hg.ne_zero hc0] at heq
    have hc : c.natDegree = 0 := by omega
    have hc' : c.coeff 0 ≠ 0 := by
      intro h0
      apply hc0
      rw [eq_C_of_natDegree_eq_zero hc, h0, map_zero]
    rw [eq_C_of_natDegree_eq_zero hc]
    exact (associated_mul_unit_right g _ (isUnit_C.mpr hc'.isUnit)).irreducible hg

/-- **Rabin's irreducibility test.** Let `F` be a polynomial of degree `d ≥ 1` over a finite
field with `q` elements. If `F ∣ X^{q^d} - X` and, for every proper divisor `e` of `d`, the
polynomial `X^{q^e} - X` is invertible modulo `F`, then `F` is irreducible. -/
theorem irreducible_of_rabin {K : Type*} [Field K] [Finite K] (F : K[X])
    (hF : 0 < F.natDegree) (hdvd : F ∣ X ^ Nat.card K ^ F.natDegree - X)
    (hcop : ∀ e, 0 < e → e < F.natDegree → e ∣ F.natDegree →
      ∃ b : K[X], F ∣ b * (X ^ Nat.card K ^ e - X) - 1) :
    Irreducible F :=
  irreducible_of_rabin_of_dvd F hF hdvd fun e he0 hed hedd =>
    ⟨e, dvd_rfl, hcop e he0 hed hedd⟩

end ArithmeticOfJacobiPolynomials
