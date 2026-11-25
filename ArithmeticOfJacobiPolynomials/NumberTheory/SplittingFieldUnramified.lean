/- Assembled by AxiomProver. -/
module

public import Mathlib

/-!
# Primes not dividing `Res(F, F')` are unramified in the splitting field of `F`

Let `F ∈ ℤ[X]` be a **monic** polynomial (a monic defining polynomial with integer
coefficients) and `K` the splitting field of `F` over `ℚ`. If a prime `p` does not divide the
resultant `Res(F, F')` (which is `± disc F`, `Polynomial.resultant_deriv`), then `p` is
unramified in `K` (`isUnramifiedIn_splittingField_of_not_dvd_resultant`).

The proof works with inertia groups instead of composita. Let `P` be a prime of `𝓞 K` above
`p` and `σ` an element of its inertia group. The roots of `F` lie in `𝓞 K` since `F` is monic.
If `σ α = β ≠ α` for a root `α`, then `β - α ∈ P`, and `α - β` divides `F'(α)` in `𝓞 K`
(`sub_dvd_eval_derivative`). The Bézout identity `F u + F' v = Res(F, F')` with `u, v ∈ ℤ[X]`
(`Polynomial.exists_mul_add_mul_eq_C_resultant`), evaluated at `α`, puts `Res(F, F')` into
`P ∩ ℤ = pℤ`, a contradiction. So the inertia group fixes every root, hence is trivial
(`eq_one_of_mem_inertia`), and its order is the ramification index
(`Ideal.card_inertia_eq_ramificationIdxIn`).

`resultant_derivative_ne_zero` records that `Res(F, F') ≠ 0` when `F` is monic and separable
over `ℚ`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial NumberField

namespace SplittingFieldUnramified

/-- If `a ≠ b` are roots of `G` over a domain, then `a - b` divides `G'(a)`. -/
theorem sub_dvd_eval_derivative {S : Type*} [CommRing S] [IsDomain S] {G : S[X]} {a b : S}
    (ha : G.IsRoot a) (hb : G.IsRoot b) (hab : a ≠ b) : a - b ∣ G.derivative.eval a := by
  obtain ⟨Q, rfl⟩ : ∃ Q, (X - C a) * Q = G := ⟨_, mul_divByMonic_eq_iff_isRoot.mpr ha⟩
  have hQb : Q.IsRoot b := by
    have h := hb
    rw [IsRoot.def, eval_mul, eval_sub, eval_X, eval_C] at h
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (Ne.symm hab))
  obtain ⟨Q₂, rfl⟩ : ∃ Q₂, (X - C b) * Q₂ = Q := ⟨_, mul_divByMonic_eq_iff_isRoot.mpr hQb⟩
  refine ⟨Q₂.eval a, ?_⟩
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
    eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero]

variable {F : ℤ[X]}

/-- A root in `K` of `F` (as a rational polynomial) is a root of `F` over `ℤ`. -/
theorem aeval_eq_zero_of_mem_rootSet {K : Type*} [Field K] [Algebra ℚ K] {x : K}
    (hx : x ∈ (F.map (Int.castRingHom ℚ)).rootSet K) : aeval x F = 0 := by
  have h := (mem_rootSet.mp hx).2
  rwa [← algebraMap_int_eq, aeval_map_algebraMap] at h

/-- For a monic `F ∈ ℤ[X]`, every root of `F` in a field is an algebraic integer. -/
theorem isIntegral_of_aeval_eq_zero (hF : F.Monic) {K : Type*} [Field K] {x : K}
    (hx : aeval x F = 0) : IsIntegral ℤ x :=
  ⟨F, hF, by rwa [aeval_def] at hx⟩

/-- A monic `F ∈ ℤ[X]` with a root in a field has positive degree. -/
theorem natDegree_ne_zero_of_aeval_eq_zero (hF : F.Monic) {K : Type*} [Field K] {x : K}
    (hx : aeval x F = 0) : F.natDegree ≠ 0 := by
  intro h0
  rw [eq_one_of_monic_natDegree_zero hF h0, map_one] at hx
  exact one_ne_zero hx

/-- An element of `𝓞 K` is a root of `F` over `𝓞 K` iff it is a root of `F` in `K`. -/
theorem isRoot_map_iff {K : Type*} [Field K] (y : 𝓞 K) :
    (F.map (algebraMap ℤ (𝓞 K))).IsRoot y ↔ aeval (algebraMap (𝓞 K) K y) F = 0 := by
  rw [IsRoot.def, eval_map_algebraMap, aeval_algebraMap_apply,
    map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]

/-- **The inertia groups at primes `p ∤ Res(F, F')` are trivial.** For a monic `F ∈ ℤ[X]`,
`K` the splitting field of `F` over `ℚ` and `P` a prime of `𝓞 K` above `p` with
`p ∤ Res(F, F')`, every element of the inertia group of `P` is the identity. -/
theorem eq_one_of_mem_inertia (hF : F.Monic) {p : ℕ}
    (hres : ¬ (p : ℤ) ∣ F.resultant (derivative F))
    (P : Ideal (𝓞 (F.map (Int.castRingHom ℚ)).SplittingField))
    [P.LiesOver (Ideal.span {(p : ℤ)})]
    (σ : Gal((F.map (Int.castRingHom ℚ)).SplittingField/ℚ))
    (hσ : σ ∈ P.inertia Gal((F.map (Int.castRingHom ℚ)).SplittingField/ℚ)) : σ = 1 := by
  apply Polynomial.Gal.ext
  intro x hx
  by_contra hne
  have hne' : σ x ≠ x := hne
  have hxF := aeval_eq_zero_of_mem_rootSet hx
  let a : 𝓞 (F.map (Int.castRingHom ℚ)).SplittingField :=
    ⟨x, isIntegral_of_aeval_eq_zero hF hxF⟩
  have hb : algebraMap (𝓞 (F.map (Int.castRingHom ℚ)).SplittingField)
      (F.map (Int.castRingHom ℚ)).SplittingField (σ • a) = σ x := rfl
  have hσx : σ x ∈ (F.map (Int.castRingHom ℚ)).rootSet
      (F.map (Int.castRingHom ℚ)).SplittingField := by
    rw [mem_rootSet] at hx ⊢
    refine ⟨hx.1, ?_⟩
    rw [show σ x = (σ : _ →ₐ[ℚ] _) x from rfl, aeval_algHom_apply, hx.2, map_zero]
  have hra : (F.map (algebraMap ℤ _)).IsRoot a := (isRoot_map_iff a).mpr hxF
  have hrb : (F.map (algebraMap ℤ _)).IsRoot (σ • a) := by
    rw [isRoot_map_iff, hb]
    exact aeval_eq_zero_of_mem_rootSet hσx
  have hab : a ≠ σ • a := by
    intro h
    apply hne'
    rw [← hb, ← h]
    rfl
  have hdvd := sub_dvd_eval_derivative hra hrb hab
  rw [derivative_map, eval_map_algebraMap] at hdvd
  have hmem : σ • a - a ∈ P := (Ideal.mem_inertia.mp hσ) a
  have hmem' : a - σ • a ∈ P := by
    rw [← neg_sub]
    exact P.neg_mem hmem
  have hder : aeval a (derivative F) ∈ P := P.mem_of_dvd hdvd hmem'
  obtain ⟨u, v, -, -, huv⟩ := exists_mul_add_mul_eq_C_resultant F (derivative F) le_rfl le_rfl
    (Or.inl (natDegree_ne_zero_of_aeval_eq_zero hF hxF))
  have hFa : aeval a F = 0 := by
    rw [← eval_map_algebraMap]
    exact hra
  have hev := congrArg (aeval a) huv
  rw [map_add, map_mul, map_mul, aeval_C, hFa, zero_mul, zero_add] at hev
  have hres_mem : algebraMap ℤ (𝓞 (F.map (Int.castRingHom ℚ)).SplittingField)
      (F.resultant (derivative F)) ∈ P := by
    rw [← hev]
    exact P.mul_mem_right _ hder
  have hunder : F.resultant (derivative F) ∈ P.under ℤ := hres_mem
  rw [← Ideal.over_def P (Ideal.span {(p : ℤ)}), Ideal.mem_span_singleton] at hunder
  exact hres hunder

/-- **Primes not dividing `Res(F, F')` are unramified in the splitting field.** Let `F ∈ ℤ[X]`
be a monic polynomial (a monic defining polynomial with integer coefficients) and `K` its
splitting field over `ℚ`. Every prime `p ∤ Res(F, F')` is unramified in `K`. -/
theorem isUnramifiedIn_splittingField_of_not_dvd_resultant (hF : F.Monic) {p : ℕ}
    (hp : p.Prime) (hres : ¬ (p : ℤ) ∣ F.resultant (derivative F)) :
    Algebra.IsUnramifiedIn (𝓞 (F.map (Int.castRingHom ℚ)).SplittingField)
      (Ideal.span {(p : ℤ)}) := by
  have : NumberField (F.map (Int.castRingHom ℚ)).SplittingField := ⟨⟩
  have : IsGalois ℚ (F.map (Int.castRingHom ℚ)).SplittingField := IsGalois.mk
  have : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)
  rw [Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
  intro P _ hP
  have := hP
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P
      Gal((F.map (Int.castRingHom ℚ)).SplittingField/ℚ),
    ← Ideal.card_inertia_eq_ramificationIdxIn
      (G := Gal((F.map (Int.castRingHom ℚ)).SplittingField/ℚ)) (Ideal.span {(p : ℤ)}) P,
    Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun σ τ => Subtype.ext ((eq_one_of_mem_inertia hF hres P σ σ.2).trans
    (eq_one_of_mem_inertia hF hres P τ τ.2).symm)⟩, ⟨1⟩⟩

/-- **`Res(F, F') ≠ 0` for separable `F`.** If `F ∈ ℤ[X]` is separable over `ℚ`, its resultant
with its derivative is a nonzero integer. -/
theorem resultant_derivative_ne_zero (hsep : (F.map (Int.castRingHom ℚ)).Separable) :
    F.resultant (derivative F) ≠ 0 := by
  intro h0
  have hφ := (Int.castRingHom ℚ).injective_int
  have e : (F.map (Int.castRingHom ℚ)).resultant (derivative (F.map (Int.castRingHom ℚ))) =
      Int.castRingHom ℚ (F.resultant (derivative F)) := by
    rw [← resultant_map_map, derivative_map, natDegree_map_eq_of_injective hφ,
      natDegree_map_eq_of_injective hφ]
  rw [h0, map_zero, resultant_eq_zero_iff] at e
  exact e.2 hsep

/-- **Primes beyond `|Res(F, F')|` are unramified in the splitting field.** For a monic
`F ∈ ℤ[X]` separable over `ℚ`, every prime `p > |Res(F, F')|` is unramified in the splitting
field of `F` over `ℚ`. -/
theorem isUnramifiedIn_splittingField_of_natAbs_resultant_lt (hF : F.Monic)
    (hsep : (F.map (Int.castRingHom ℚ)).Separable) {p : ℕ} (hp : p.Prime)
    (hlt : (F.resultant (derivative F)).natAbs < p) :
    Algebra.IsUnramifiedIn (𝓞 (F.map (Int.castRingHom ℚ)).SplittingField)
      (Ideal.span {(p : ℤ)}) := by
  refine isUnramifiedIn_splittingField_of_not_dvd_resultant hF hp fun hdvd => ?_
  have := Int.natAbs_le_of_dvd_ne_zero hdvd (resultant_derivative_ne_zero hsep)
  rw [Int.natAbs_natCast] at this
  omega

end SplittingFieldUnramified

end ArithmeticOfJacobiPolynomials
