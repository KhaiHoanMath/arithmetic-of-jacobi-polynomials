/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Effective.FixedFieldThreshold
public import ArithmeticOfJacobiPolynomials.NumberTheory.SplittingFieldUnramified

/-!
# The fixed-field assertion of Theorem 1.3 for `E` given by a monic defining polynomial

The addendum to Theorem 1.3 (§1.2) holds for all `n` beyond a threshold *effective in
`a, b, E`*. `unequalFixedField_of_fixedFieldThreshold_le` gives the threshold
`fixedFieldThreshold a b R` for any `R` beyond which all primes are unramified in a Galois
number field containing `E`. Here the number field `E` is presented by a **monic defining
polynomial** `F ∈ ℤ[X]`, separable over `ℚ`, together with an embedding of `E` into the
splitting field `K` of `F` over `ℚ`, and `R` is computed from the integer coefficients of `F`.

* `derivSylvester F` is the Sylvester matrix of `F` and `F'` (sizes `deg F` and `deg F - 1`),
  with entries written in terms of the coefficients of `F` (`derivSylvester_eq`);
* `fixedFieldPolyBound F` is the absolute value of its determinant, written as the Leibniz sum,
  a computable function of the coefficients of `F`; it equals `|Res(F, F')|`
  (`fixedFieldPolyBound_eq`);
* `isUnramifiedIn_splittingField_of_fixedFieldPolyBound_lt`: every prime
  `p > fixedFieldPolyBound F` is unramified in `K`
  (`SplittingFieldUnramified.isUnramifiedIn_splittingField_of_not_dvd_resultant`);
* `unequalFixedField_of_monicPolynomial`: **the fixed-field assertion of Theorem 1.3 for
  `n ≥ fixedFieldThreshold a b (fixedFieldPolyBound F)`**;
* `unequalFixedField_of_monicPolynomial_adjoinRoot`: the special case `E = ℚ[X]/(F)` for `F`
  irreducible over `ℚ`.

Conditional on the cited literature of `unequalFixedField_of_fixedFieldThreshold_le`.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial NumberField TensorProduct UnequalParameters SplittingFieldUnramified

/-- The Sylvester matrix of a polynomial `F ∈ ℤ[X]` and its derivative `F'`, for the degrees
`deg F` and `deg F - 1`, with the coefficient `[X^k] F' = (k + 1) [X^(k+1)] F` written out in
terms of the coefficients of `F`. -/
def derivSylvester (F : ℤ[X]) :
    Matrix (Fin (F.natDegree + (F.natDegree - 1))) (Fin (F.natDegree + (F.natDegree - 1))) ℤ :=
  .of fun i j ↦ j.addCases
    (fun j₁ ↦ if (i : ℕ) ∈ Set.Icc (j₁ : ℕ) (j₁ + (F.natDegree - 1)) then
      F.coeff (i - j₁ + 1) * (((i - j₁ : ℕ) : ℤ) + 1) else 0)
    (fun j₁ ↦ if (i : ℕ) ∈ Set.Icc (j₁ : ℕ) (j₁ + F.natDegree) then F.coeff (i - j₁) else 0)

/-- `derivSylvester F` is Mathlib's Sylvester matrix of `F` and `F'`. -/
theorem derivSylvester_eq (F : ℤ[X]) :
    derivSylvester F = sylvester F (derivative F) F.natDegree (F.natDegree - 1) := by
  ext i j
  refine Fin.addCases (fun j₁ => ?_) (fun j₁ => ?_) j <;>
    simp [derivSylvester, sylvester, coeff_derivative]

/-- **The explicit ramification bound of a monic defining polynomial.** For `F ∈ ℤ[X]`,
`fixedFieldPolyBound F` is the absolute value of the Leibniz expansion of the determinant of
the Sylvester matrix of `F` and `F'`, a computable function of the integer coefficients of `F`.
It equals `|Res(F, F')| = |disc F|` (`fixedFieldPolyBound_eq`). -/
def fixedFieldPolyBound (F : ℤ[X]) : ℕ :=
  (∑ σ : Equiv.Perm (Fin (F.natDegree + (F.natDegree - 1))),
    Equiv.Perm.sign σ • ∏ i, derivSylvester F (σ i) i).natAbs

/-- `fixedFieldPolyBound F = |Res(F, F')|`. -/
theorem fixedFieldPolyBound_eq (F : ℤ[X]) :
    fixedFieldPolyBound F = (F.resultant (derivative F)).natAbs := by
  rw [fixedFieldPolyBound, ← Matrix.det_apply, derivSylvester_eq, natDegree_derivative]
  rfl

/-- **Primes beyond `fixedFieldPolyBound F` are unramified in the splitting field.** For a
monic defining polynomial `F ∈ ℤ[X]` separable over `ℚ`, every prime
`p > fixedFieldPolyBound F` is unramified in the splitting field of `F` over `ℚ`. -/
theorem isUnramifiedIn_splittingField_of_fixedFieldPolyBound_lt {F : ℤ[X]} (hF : F.Monic)
    (hsep : (F.map (Int.castRingHom ℚ)).Separable) {p : ℕ} (hp : p.Prime)
    (hlt : fixedFieldPolyBound F < p) :
    Algebra.IsUnramifiedIn (𝓞 (F.map (Int.castRingHom ℚ)).SplittingField)
      (Ideal.span {(p : ℤ)}) :=
  isUnramifiedIn_splittingField_of_natAbs_resultant_lt hF hsep hp
    (by rwa [← fixedFieldPolyBound_eq])

/-- **The fixed-field assertion of Theorem 1.3 for `E` given by a monic defining polynomial**
(§1.2). Let `a ≠ b` be nonnegative integers and let the number field `E` be
presented by a monic polynomial `F ∈ ℤ[X]`, separable over `ℚ`, with an embedding `ι` of `E`
into the splitting field of `F` over `ℚ`. For every
`n ≥ fixedFieldThreshold a b (fixedFieldPolyBound F)`, a threshold computed from `a`, `b` and
the integer coefficients of `F`, the splitting field of `P_n^{(a,b)}` is linearly disjoint from
`E` over `ℚ`, and `P_n^{(a,b)}` is irreducible over `E` with Galois group `S_n`. Conditional on
[Hanson, Theorem 1] (`hH`), [DLMF, §18.2(vi)] (`hZ`),
[Jones, Theorem 1.1] (`hJordan`), [Milne, ANT v3.08, Proposition 3.53] (`hEis`), the Jacobi
discriminant formula (`hdisc`) and [Dusart10, Theorem 5.2] (`hDusart`). -/
theorem unequalFixedField_of_monicPolynomial (hH : HansonLcmBound)
     (hZ : JacobiSimpleRealZeros) (hJordan : JordanPrimeCycleTheorem)
     (hEis : EisensteinPrimeTotallyRamified)
    (hdisc : JacobiDiscriminantFormula) (hDusart : DusartThetaBound) {a b : ℕ} (hab : a ≠ b)
    (F : ℤ[X]) (hF : F.Monic) (hsep : (F.map (Int.castRingHom ℚ)).Separable)
    (E : Type*) [Field E] [NumberField E]
    (ι : E →ₐ[ℚ] (F.map (Int.castRingHom ℚ)).SplittingField) :
    ∀ n ≥ fixedFieldThreshold a b (fixedFieldPolyBound F),
      IsField ((jacobiP a b n).SplittingField ⊗[ℚ] E) ∧
      Irreducible ((jacobiP a b n).map (algebraMap ℚ E)) ∧
      GaloisGroupIsSymmetric ((jacobiP a b n).map (algebraMap ℚ E)) := by
  have : NumberField (F.map (Int.castRingHom ℚ)).SplittingField := ⟨⟩
  have : IsGalois ℚ (F.map (Int.castRingHom ℚ)).SplittingField := IsGalois.mk
  exact unequalFixedField_of_fixedFieldThreshold_le hH hZ hJordan hEis hdisc hDusart hab E _ ι _
    fun _ hp hlt => isUnramifiedIn_splittingField_of_fixedFieldPolyBound_lt hF hsep hp hlt

/-- **The fixed-field assertion of Theorem 1.3 for `E = ℚ[X]/(F)`.** Let `a ≠ b` and let
`F ∈ ℤ[X]` be a monic defining polynomial, irreducible over `ℚ`, of the number field
`E = ℚ[X]/(F)`. For every `n ≥ fixedFieldThreshold a b (fixedFieldPolyBound F)` the splitting
field of `P_n^{(a,b)}` is linearly disjoint from `E`, and `P_n^{(a,b)}` is irreducible over `E`
with Galois group `S_n`. Conditional on the same literature as
`unequalFixedField_of_monicPolynomial`. -/
theorem unequalFixedField_of_monicPolynomial_adjoinRoot (hH : HansonLcmBound)
     (hZ : JacobiSimpleRealZeros) (hJordan : JordanPrimeCycleTheorem)
     (hEis : EisensteinPrimeTotallyRamified)
    (hdisc : JacobiDiscriminantFormula) (hDusart : DusartThetaBound) {a b : ℕ} (hab : a ≠ b)
    (F : ℤ[X]) (hF : F.Monic) [hirr : Fact (Irreducible (F.map (Int.castRingHom ℚ)))] :
    ∀ n ≥ fixedFieldThreshold a b (fixedFieldPolyBound F),
      IsField ((jacobiP a b n).SplittingField ⊗[ℚ] AdjoinRoot (F.map (Int.castRingHom ℚ))) ∧
      Irreducible ((jacobiP a b n).map
        (algebraMap ℚ (AdjoinRoot (F.map (Int.castRingHom ℚ))))) ∧
      GaloisGroupIsSymmetric ((jacobiP a b n).map
        (algebraMap ℚ (AdjoinRoot (F.map (Int.castRingHom ℚ))))) := by
  have hf0 : F.map (Int.castRingHom ℚ) ≠ 0 := hirr.out.ne_zero
  have : Module.Finite ℚ (AdjoinRoot (F.map (Int.castRingHom ℚ))) :=
    (AdjoinRoot.powerBasis hf0).finite
  have : CharZero (AdjoinRoot (F.map (Int.castRingHom ℚ))) :=
    charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  have : NumberField (AdjoinRoot (F.map (Int.castRingHom ℚ))) := ⟨⟩
  have hdeg : ((F.map (Int.castRingHom ℚ)).map
      (algebraMap ℚ (F.map (Int.castRingHom ℚ)).SplittingField)).degree ≠ 0 := by
    rw [degree_map]
    exact (degree_pos_of_irreducible hirr.out).ne'
  obtain ⟨x, hx⟩ := (SplittingField.splits (F.map (Int.castRingHom ℚ))).exists_eval_eq_zero hdeg
  rw [eval_map] at hx
  exact unequalFixedField_of_monicPolynomial hH hZ hJordan hEis hdisc hDusart hab F hF
    (PerfectField.separable_of_irreducible hirr.out) _
    (AdjoinRoot.liftAlgHom _ (Algebra.ofId ℚ _) x hx)

end ArithmeticOfJacobiPolynomials
