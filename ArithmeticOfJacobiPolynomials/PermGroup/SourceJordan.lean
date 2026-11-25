/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.External

/-!
# Jordan's prime-cycle theorem and its relation to Jones's theorem

The manuscript ends the proof of Lemma 5.16 with "Jordan's theorem gives `A_n`
[Jones, Theorem 1.1]". `JordanPrimeCycleTheorem` is that classical statement (a primitive group
containing a cycle of prime length with at least three fixed points contains `A_n`).
`JonesCycleTheorem` ([Jones, Corollary 1.3]) is the extension without the primality condition and
depends on the classification of finite simple groups.
`jordanPrimeCycleTheorem_of_jonesCycleTheorem` recovers the prime-length case.
-/

public section

namespace ArithmeticOfJacobiPolynomials

/-- The prime-length case of `JonesCycleTheorem` is `JordanPrimeCycleTheorem`. -/
theorem jordanPrimeCycleTheorem_of_jonesCycleTheorem (h : JonesCycleTheorem) :
    JordanPrimeCycleTheorem :=
  fun α _ _ G hG σ hσG hσ _ h3 => h α G hG σ hσG hσ h3

end ArithmeticOfJacobiPolynomials
