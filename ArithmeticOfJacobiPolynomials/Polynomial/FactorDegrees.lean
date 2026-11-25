/- Assembled by AxiomProver. -/
module

public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Lemma C.1: a factor-degree criterion

For a primitive `H ∈ ℤ[X]` of degree `D ≥ 1` and a prime `p` at which the reduction `H̄` of `H`
has degree `D`, let `𝒟_p` be the multiset of degrees of the irreducible (monic) factors of `H̄`
over `𝔽_p`, and `Σ_p` the set of its subset sums (each entry used at most once, i.e. sums of
sub-multisets). If no `k ∈ [1, ⌊D/2⌋]` lies in `Σ_p` for all `p` in a finite set `𝒫` of such
primes, then `H` is irreducible over `ℚ`.

The source requires in addition that the reductions be squarefree; this hypothesis is not
needed for the argument (`irreducible_of_factorDegrees_of_natDegree_eq`), and the version with
it is `irreducible_of_factorDegrees`. The source leaves the condition `D ≥ 1` implicit: a
primitive polynomial of degree `0` is a unit, hence not irreducible.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial UniqueFactorizationMonoid

/-- The multiset `𝒟_p` of degrees of the irreducible monic factors of the reduction of `H`
modulo the prime `p`, counted with multiplicity. -/
noncomputable def factorDegrees (p : ℕ) [Fact p.Prime] (H : ℤ[X]) : Multiset ℕ :=
  (normalizedFactors (H.map (Int.castRingHom (ZMod p)))).map natDegree

/-- The set `Σ` of subset sums of a multiset of naturals, each entry used at most once. -/
def subsetSums (m : Multiset ℕ) : Set ℕ := {k | ∃ t ≤ m, t.sum = k}

/-- Unfolding lemma for `factorDegrees`. -/
theorem factorDegrees_eq (p : ℕ) [Fact p.Prime] (H : ℤ[X]) :
    factorDegrees p H =
      (normalizedFactors (H.map (Int.castRingHom (ZMod p)))).map natDegree := by
  unfold factorDegrees; rfl

/-- Unfolding lemma for `subsetSums`. -/
theorem mem_subsetSums {m : Multiset ℕ} {k : ℕ} : k ∈ subsetSums m ↔ ∃ t ≤ m, t.sum = k := by
  unfold subsetSums; rfl

/-- A factor of the reduction of `H` modulo `p` has its degree in `Σ_p`. -/
theorem natDegree_mem_subsetSums_factorDegrees (p : ℕ) [Fact p.Prime] (H A : ℤ[X])
    (hH : H.map (Int.castRingHom (ZMod p)) ≠ 0)
    (hA : A.map (Int.castRingHom (ZMod p)) ∣ H.map (Int.castRingHom (ZMod p))) :
    (A.map (Int.castRingHom (ZMod p))).natDegree ∈ subsetSums (factorDegrees p H) := by
  set f := Int.castRingHom (ZMod p)
  have hA0 : A.map f ≠ 0 := fun h => hH (zero_dvd_iff.mp (h ▸ hA))
  refine ⟨(normalizedFactors (A.map f)).map natDegree, ?_, ?_⟩
  · exact Multiset.map_le_map
      ((dvd_iff_normalizedFactors_le_normalizedFactors hA0 hH).mp hA)
  · rw [← natDegree_multiset_prod _ (zero_notMem_normalizedFactors _)]
    exact natDegree_eq_of_degree_eq
      (degree_eq_degree_of_associated (prod_normalizedFactors hA0))

/-- A primitive integer polynomial of positive degree that is reducible over `ℚ` has a factor
in `ℤ[X]` of degree `k` with `1 ≤ k ≤ ⌊D/2⌋`. -/
theorem exists_factor_of_not_irreducible (H : ℤ[X]) (hprim : H.IsPrimitive)
    (hD : 0 < H.natDegree) (hred : ¬ Irreducible (H.map (Int.castRingHom ℚ))) :
    ∃ A B : ℤ[X], H = A * B ∧ 1 ≤ A.natDegree ∧ A.natDegree ≤ H.natDegree / 2 := by
  rw [← Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim] at hred
  have hH0 : H ≠ 0 := by rintro rfl; simp at hD
  have hHu : ¬ IsUnit H := fun h => by
    rw [natDegree_eq_zero_of_isUnit h] at hD; exact lt_irrefl _ hD
  have hred' : ∃ A B, H = A * B ∧ ¬ IsUnit A ∧ ¬ IsUnit B := by
    by_contra hcon
    push Not at hcon
    exact hred ⟨hHu, fun a b hab => by
      by_contra hab'
      push Not at hab'
      exact hab'.2 (hcon a b hab hab'.1)⟩
  obtain ⟨A, B, hAB, hA, hB⟩ := hred'
  have hA0 : A ≠ 0 := by rintro rfl; exact hH0 (by rw [hAB, zero_mul])
  have hB0 : B ≠ 0 := by rintro rfl; exact hH0 (by rw [hAB, mul_zero])
  have hpos : ∀ C : ℤ[X], C ∣ H → ¬ IsUnit C → 1 ≤ C.natDegree := by
    intro C hC hCu
    by_contra h0
    push Not at h0
    have h0' : C.natDegree = 0 := by omega
    have hCprim := isPrimitive_of_dvd hprim hC
    rw [eq_C_of_natDegree_eq_zero h0'] at hCprim hCu
    exact hCu (isUnit_C.mpr (hCprim _ dvd_rfl))
  have hdeg : H.natDegree = A.natDegree + B.natDegree := by
    rw [hAB, natDegree_mul hA0 hB0]
  have hA1 := hpos A ⟨B, hAB⟩ hA
  have hB1 := hpos B ⟨A, by rw [hAB, mul_comm]⟩ hB
  by_cases hle : A.natDegree ≤ H.natDegree / 2
  · exact ⟨A, B, hAB, hA1, hle⟩
  · exact ⟨B, A, by rw [hAB, mul_comm], hB1, by omega⟩

/-- **Lemma C.1** without the squarefree hypothesis. Let `H ∈ ℤ[X]` be primitive of degree
`D ≥ 1` and `P` a finite set of primes at which the reduction of `H` has degree `D`. If every
`k ∈ [1, ⌊D/2⌋]` fails to be a subset sum of `𝒟_p` for some `p ∈ P`, then `H` is irreducible
over `ℚ`. -/
theorem irreducible_of_factorDegrees_of_natDegree_eq (H : ℤ[X]) (hprim : H.IsPrimitive)
    (hD : 0 < H.natDegree) (P : Finset ℕ)
    (hdeg : ∀ p ∈ P, (H.map (Int.castRingHom (ZMod p))).natDegree = H.natDegree)
    (hsums : ∀ k, 1 ≤ k → k ≤ H.natDegree / 2 →
      ∃ p ∈ P, ∃ _ : Fact p.Prime, k ∉ subsetSums (factorDegrees p H)) :
    Irreducible (H.map (Int.castRingHom ℚ)) := by
  by_contra hred
  obtain ⟨A, B, hAB, hA1, hA2⟩ := exists_factor_of_not_irreducible H hprim hD hred
  obtain ⟨p, hp, hfact, hk⟩ := hsums A.natDegree hA1 hA2
  set f := Int.castRingHom (ZMod p)
  have hlcH : f H.leadingCoeff ≠ 0 := by
    rcases natDegree_map_eq_iff.mp (hdeg p hp) with h | h
    · exact h
    · omega
  have hlcA : f A.leadingCoeff ≠ 0 := by
    intro h
    apply hlcH
    rw [hAB, leadingCoeff_mul, map_mul, h, zero_mul]
  have hHbar : H.map f ≠ 0 := by
    intro h
    have := hdeg p hp
    rw [h, natDegree_zero] at this
    omega
  have hdvd : A.map f ∣ H.map f := by
    rw [hAB, Polynomial.map_mul]
    exact dvd_mul_right _ _
  have hmem := natDegree_mem_subsetSums_factorDegrees p H A hHbar hdvd
  rw [natDegree_map_of_leadingCoeff_ne_zero f hlcA] at hmem
  exact hk hmem

/-- **Lemma C.1.** Let `H ∈ ℤ[X]` be primitive of degree `D ≥ 1` and `P` a finite set of primes
at which the reduction of `H` has degree `D` and is squarefree. If
`{1, …, ⌊D/2⌋} ∩ ⋂_{p ∈ P} Σ_p = ∅`, then `H` is irreducible over `ℚ`. -/
theorem irreducible_of_factorDegrees (H : ℤ[X]) (hprim : H.IsPrimitive)
    (hD : 0 < H.natDegree) (P : Finset ℕ) (_hP : ∀ p ∈ P, p.Prime)
    (hdeg : ∀ p ∈ P, (H.map (Int.castRingHom (ZMod p))).natDegree = H.natDegree)
    (_hsqf : ∀ p ∈ P, Squarefree (H.map (Int.castRingHom (ZMod p))))
    (hsums : ∀ k, 1 ≤ k → k ≤ H.natDegree / 2 →
      ∃ p ∈ P, ∃ _ : Fact p.Prime, k ∉ subsetSums (factorDegrees p H)) :
    Irreducible (H.map (Int.castRingHom ℚ)) :=
  irreducible_of_factorDegrees_of_natDegree_eq H hprim hD P hdeg hsums

end ArithmeticOfJacobiPolynomials
