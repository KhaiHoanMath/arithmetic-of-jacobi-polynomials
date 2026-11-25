/- Assembled by AxiomProver. -/
module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Polynomial.GaussNorm
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Projective `p`-adic root distances

Roots of polynomials over `ℤ_[p]` live in `PadicAlgCl p`, the algebraic closure of `ℚ_[p]`
with its (unique) extension of the `p`-adic norm. We use the real-valued valuation
`v_p(x) = -log_p ‖x‖`, so `v_p(p) = 1`.

For roots `z, w` the *projective distance* of Section 2.2 of the manuscript is
`δ_p(z,w) = v_p(z - w) - min{v_p(z), 0} - min{v_p(w), 0}`.

Main results:
* `ArithmeticOfJacobiPolynomials.projDist_nonneg`: `δ_p(z,w) ≥ 0`;
* `ArithmeticOfJacobiPolynomials.padicVal_leadingCoeff_eq`: for a primitive `F ∈ ℤ_[p][X]`,
  `v_p(lc F) = -∑_{F(w)=0} min{v_p(w), 0}` (multiplicativity of the Gauss norm);
* `ArithmeticOfJacobiPolynomials.padicVal_resultant_eq_sum_projDist`: the projective resultant
formula (2.6),
  `v_p(Res(A,B)) = ∑_{A(z)=0} ∑_{B(w)=0} δ_p(z,w)` for primitive `A, B` without common roots.
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial

/-- The real-valued `p`-adic valuation `v_p(x) = -log_p ‖x‖` on a normed type (used for
`ℤ_[p]`, `ℚ_[p]` and `PadicAlgCl p`). For `x ≠ 0` this is the usual valuation normalized by
`v_p(p) = 1`; the junk value at `0` is `0`. -/
noncomputable def padicVal (p : ℕ) {F : Type*} [Norm F] (x : F) : ℝ := -Real.logb p ‖x‖

/-- The projective `p`-adic distance
`δ_p(z,w) = v_p(z - w) - min{v_p(z), 0} - min{v_p(w), 0}` of two (distinct) points of
`PadicAlgCl p`. -/
noncomputable def projDist (p : ℕ) [Fact p.Prime] (z w : PadicAlgCl p) : ℝ :=
  padicVal p (z - w) - min (padicVal p z) 0 - min (padicVal p w) 0

lemma padicVal_def (p : ℕ) {F : Type*} [Norm F] (x : F) :
    padicVal p x = -Real.logb p ‖x‖ := by
  unfold padicVal; rfl

lemma projDist_def (p : ℕ) [Fact p.Prime] (z w : PadicAlgCl p) :
    projDist p z w = padicVal p (z - w) - min (padicVal p z) 0 - min (padicVal p w) 0 := by
  unfold projDist; rfl

variable {p : ℕ} [hp : Fact p.Prime]

lemma one_lt_prime_real : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt

lemma norm_algebraMap_padicInt (x : ℤ_[p]) :
    ‖algebraMap ℤ_[p] (PadicAlgCl p) x‖ = ‖x‖ := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p], PadicAlgCl.norm_extends]
  rfl

lemma algebraMap_padicInt_injective :
    Function.Injective (algebraMap ℤ_[p] (PadicAlgCl p)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have := norm_algebraMap_padicInt (p := p) x
  rw [hx, norm_zero] at this
  exact norm_eq_zero.mp this.symm

lemma min_padicVal_zero (x : PadicAlgCl p) :
    min (padicVal p x) 0 = -Real.logb p (max 1 ‖x‖) := by
  unfold padicVal
  rcases le_or_gt ‖x‖ 1 with h | h
  · rw [max_eq_left h, Real.logb_one, neg_zero]
    exact min_eq_right (neg_nonneg.mpr (Real.logb_nonpos one_lt_prime_real (norm_nonneg _) h))
  · rw [max_eq_right h.le]
    exact min_eq_left (neg_nonpos.mpr (Real.logb_pos one_lt_prime_real h).le)

lemma projDist_eq (z w : PadicAlgCl p) :
    projDist p z w = -Real.logb p ‖z - w‖ + Real.logb p (max 1 ‖z‖) +
      Real.logb p (max 1 ‖w‖) := by
  unfold projDist
  rw [min_padicVal_zero, min_padicVal_zero]
  unfold padicVal
  ring

lemma projDist_comm (z w : PadicAlgCl p) : projDist p z w = projDist p w z := by
  rw [projDist_eq, projDist_eq, norm_sub_rev]
  ring

/-- Projective distances are nonnegative. -/
theorem projDist_nonneg (z w : PadicAlgCl p) : 0 ≤ projDist p z w := by
  rw [projDist_eq]
  have h1 : (1 : ℝ) ≤ max 1 ‖z‖ := le_max_left _ _
  have h2 : (1 : ℝ) ≤ max 1 ‖w‖ := le_max_left _ _
  by_cases hzw : z = w
  · subst hzw
    simp only [sub_self, norm_zero, Real.logb_zero, neg_zero, zero_add]
    exact add_nonneg (Real.logb_nonneg one_lt_prime_real h1)
      (Real.logb_nonneg one_lt_prime_real h2)
  · have hpos : 0 < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzw)
    have hle : ‖z - w‖ ≤ max 1 ‖z‖ * max 1 ‖w‖ := by
      calc ‖z - w‖ ≤ max ‖z‖ ‖w‖ := by
            simpa [sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max z (-w)
        _ ≤ max 1 ‖z‖ * max 1 ‖w‖ := by
          apply max_le
          · nlinarith [le_max_right 1 ‖z‖, norm_nonneg z]
          · nlinarith [le_max_right 1 ‖w‖, norm_nonneg w]
    have := Real.logb_le_logb_of_le (one_lt_prime_real (p := p)) hpos hle
    rw [Real.logb_mul (by positivity) (by positivity)] at this
    linarith

/-- For a nonzero integer `R`, the real valuation of `R ∈ ℤ_[p]` is `padicValInt p R`. -/
theorem padicVal_intCast {R : ℤ} (hR : R ≠ 0) :
    padicVal p (R : ℤ_[p]) = padicValInt p R := by
  have hR' : (R : ℚ_[p]) ≠ 0 := Int.cast_ne_zero.mpr hR
  have hnorm : ‖(R : ℤ_[p])‖ = ‖(R : ℚ_[p])‖ := by
    rw [PadicInt.norm_def, PadicInt.coe_intCast]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (p : ℝ) ≠ 1 := ne_of_gt one_lt_prime_real
  rw [padicVal_def, hnorm, Padic.norm_eq_zpow_neg_valuation hR', Padic.valuation_intCast,
    ← Real.rpow_intCast, Real.logb_rpow hp0 hp1]
  push_cast
  ring

/-- Transport of the resultant of integer polynomials to `ℤ_[p]`: if `A, B ∈ ℤ[X]` have
nonzero resultant, then `v_p(Res(A,B))` computed in `ℤ_[p]` is `padicValInt p (Res(A,B))`. -/
theorem padicVal_resultant_map_intCast {A B : ℤ[X]} (hR : resultant A B ≠ 0) :
    padicVal p (resultant (A.map (Int.castRingHom ℤ_[p])) (B.map (Int.castRingHom ℤ_[p]))) =
      padicValInt p (resultant A B) := by
  have hinj : Function.Injective (Int.castRingHom ℤ_[p]) := Int.cast_injective
  rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj,
    resultant_map_map, eq_intCast]
  exact padicVal_intCast hR

omit hp in
/-- `log_p` of a product of positive reals indexed by a multiset. -/
lemma logb_multiset_prod_map {α : Type*} (s : Multiset α) (f : α → ℝ)
    (hf : ∀ a ∈ s, f a ≠ 0) :
    Real.logb p (s.map f).prod = (s.map fun a => Real.logb p (f a)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    have ha : f a ≠ 0 := hf a (Multiset.mem_cons_self a s)
    have hs : ∀ b ∈ s, f b ≠ 0 := fun b hb => hf b (Multiset.mem_cons_of_mem hb)
    have hprod : (s.map f).prod ≠ 0 := by
      apply Multiset.prod_ne_zero
      intro h
      obtain ⟨b, hb, hb0⟩ := Multiset.mem_map.mp h
      exact hs b hb hb0
    rw [Real.logb_mul ha hprod, ih hs]

/-- The norm of a product over a multiset in `PadicAlgCl p`. -/
lemma norm_multiset_prod_map {α : Type*} (s : Multiset α) (f : α → PadicAlgCl p) :
    ‖(s.map f).prod‖ = (s.map fun a => ‖f a‖).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [norm_mul, ih]

/-! ### The Gauss norm root-mass identity -/

section Gauss

local notation "K" => PadicAlgCl p

local notation "absK" => NormedField.toAbsoluteValue (PadicAlgCl p)

private lemma isNonarchimedean_absK : IsNonarchimedean (absK) :=
  PadicAlgCl.isNonarchimedean p

private lemma gaussNorm_X_sub_C (w : K) :
    (X - C w).gaussNorm absK 1 = max 1 ‖w‖ := by
  apply le_antisymm
  · rw [sub_eq_add_neg, ← C_neg]
    have hna := isNonarchimedean_gaussNorm (hna := isNonarchimedean_absK (p := p))
      (hc := zero_le_one)
    refine (hna X (C (-w))).trans ?_
    have hX : (X : K[X]).gaussNorm absK 1 = 1 := by
      rw [← monomial_one_one_eq_X, gaussNorm_monomial]
      simp
    rw [hX, gaussNorm_C]
    simp
  · apply max_le
    · have := le_gaussNorm absK (p := (X - C w : K[X])) zero_le_one 1
      simpa [coeff_X, coeff_C] using this
    · have := le_gaussNorm absK (p := (X - C w : K[X])) zero_le_one 0
      simpa [coeff_X, coeff_C] using this

private lemma gaussNorm_prod_X_sub_C (s : Multiset K) :
    (s.map fun w => X - C w).prod.gaussNorm absK 1 = (s.map fun w => max 1 ‖w‖).prod := by
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero]
    rw [← C_1, gaussNorm_C]
    simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [gaussNorm_mul isNonarchimedean_absK zero_lt_one, gaussNorm_X_sub_C, ih]

/-- A primitive polynomial over `ℤ_[p]` has a unit coefficient. -/
lemma IsPrimitive.exists_norm_coeff_eq_one {F : ℤ_[p][X]} (hF : F.IsPrimitive) :
    ∃ i, ‖F.coeff i‖ = 1 := by
  by_contra h
  push Not at h
  have hdvd : C (p : ℤ_[p]) ∣ F := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    exact (PadicInt.norm_lt_one_iff_dvd _).mp (lt_of_le_of_ne (F.coeff i).norm_le_one (h i))
  have hu := hF _ hdvd
  have h1 : ‖(p : ℤ_[p])‖ = 1 := PadicInt.isUnit_iff.mp hu
  have h2 : ‖(p : ℤ_[p])‖ < 1 := (PadicInt.norm_lt_one_iff_dvd _).mpr dvd_rfl
  linarith

private lemma gaussNorm_map_eq_one {F : ℤ_[p][X]} (hF : F.IsPrimitive) :
    (F.map (algebraMap ℤ_[p] K)).gaussNorm absK 1 = 1 := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := exists_eq_gaussNorm absK 1 (F.map (algebraMap ℤ_[p] K))
    rw [hi, one_pow, mul_one, coeff_map]
    change ‖algebraMap ℤ_[p] K (F.coeff i)‖ ≤ 1
    rw [norm_algebraMap_padicInt]
    exact (F.coeff i).norm_le_one
  · obtain ⟨i, hi⟩ := IsPrimitive.exists_norm_coeff_eq_one hF
    have := le_gaussNorm absK (p := F.map (algebraMap ℤ_[p] K)) zero_le_one i
    rw [one_pow, mul_one, coeff_map] at this
    change ‖algebraMap ℤ_[p] K (F.coeff i)‖ ≤ _ at this
    rwa [norm_algebraMap_padicInt, hi] at this

/-- **Gauss norm root-mass identity** (multiplicative form): for primitive `F ∈ ℤ_[p][X]`,
`‖lc F‖ · ∏_{F(w)=0} max{1, ‖w‖} = 1`, the roots being taken with multiplicity in
`PadicAlgCl p`. -/
theorem norm_leadingCoeff_mul_prod_roots {F : ℤ_[p][X]} (hF : F.IsPrimitive) :
    ‖F.leadingCoeff‖ *
      ((F.map (algebraMap ℤ_[p] K)).roots.map fun w => max 1 ‖w‖).prod = 1 := by
  have hsplit := (IsAlgClosed.splits (F.map (algebraMap ℤ_[p] K))).eq_prod_roots
  have h := gaussNorm_map_eq_one hF
  rw [hsplit, gaussNorm_mul isNonarchimedean_absK zero_lt_one, gaussNorm_C,
    gaussNorm_prod_X_sub_C, leadingCoeff_map_of_injective algebraMap_padicInt_injective] at h
  simpa [norm_algebraMap_padicInt] using h

/-- Logarithmic form of the root-mass identity:
`log_p ‖lc F‖ + ∑_{F(w)=0} log_p max{1, ‖w‖} = 0`. -/
lemma logb_norm_leadingCoeff_add_sum {F : ℤ_[p][X]} (hF : F.IsPrimitive) :
    Real.logb p ‖F.leadingCoeff‖ +
      ((F.map (algebraMap ℤ_[p] K)).roots.map fun w => Real.logb p (max 1 ‖w‖)).sum = 0 := by
  have h := congrArg (Real.logb p) (norm_leadingCoeff_mul_prod_roots hF)
  have hlc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hF.ne_zero
  have hprod : ((F.map (algebraMap ℤ_[p] K)).roots.map fun w => max 1 ‖w‖).prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro h0
    obtain ⟨b, -, hb⟩ := Multiset.mem_map.mp h0
    have : (1 : ℝ) ≤ max 1 ‖b‖ := le_max_left _ _
    linarith
  rwa [Real.logb_mul (norm_ne_zero_iff.mpr hlc) hprod, Real.logb_one,
    logb_multiset_prod_map _ _ (fun w _ => by positivity)] at h

/-- **Gauss norm root-mass identity**: for primitive `F ∈ ℤ_[p][X]`,
`v_p(lc F) = -∑_{F(w)=0} min{v_p(w), 0}`. -/
theorem padicVal_leadingCoeff_eq {F : ℤ_[p][X]} (hF : F.IsPrimitive) :
    padicVal p F.leadingCoeff =
      -((F.map (algebraMap ℤ_[p] K)).roots.map fun w => min (padicVal p w) 0).sum := by
  have h := logb_norm_leadingCoeff_add_sum hF
  have hfun : (fun w : K => min (padicVal p w) 0) = fun w => -Real.logb p (max 1 ‖w‖) :=
    funext min_padicVal_zero
  rw [hfun, Multiset.sum_map_neg, neg_neg]
  unfold padicVal
  linarith

/-- **The projective resultant formula (2.6).** For primitive `A, B ∈ ℤ_[p][X]` without common
root in `PadicAlgCl p`, `v_p(Res(A,B)) = ∑_{A(z)=0} ∑_{B(w)=0} δ_p(z,w)` (roots with
multiplicity). -/
theorem padicVal_resultant_eq_sum_projDist {A B : ℤ_[p][X]} (hA : A.IsPrimitive)
    (hB : B.IsPrimitive)
    (hdisj : ∀ z ∈ (A.map (algebraMap ℤ_[p] K)).roots,
      ∀ w ∈ (B.map (algebraMap ℤ_[p] K)).roots, z ≠ w) :
    padicVal p (resultant A B) = ((A.map (algebraMap ℤ_[p] K)).roots.map fun z =>
      ((B.map (algebraMap ℤ_[p] K)).roots.map fun w => projDist p z w).sum).sum := by
  set φ := algebraMap ℤ_[p] K with hφ
  set A' := A.map φ with hA'
  set B' := B.map φ with hB'
  have hinj : Function.Injective φ := algebraMap_padicInt_injective
  have hAdeg : A'.natDegree = A.natDegree := natDegree_map_eq_of_injective hinj A
  have hBdeg : B'.natDegree = B.natDegree := natDegree_map_eq_of_injective hinj B
  have hAlc : ‖A'.leadingCoeff‖ = ‖A.leadingCoeff‖ := by
    rw [hA', leadingCoeff_map_of_injective hinj, norm_algebraMap_padicInt]
  have hBlc : ‖B'.leadingCoeff‖ = ‖B.leadingCoeff‖ := by
    rw [hB', leadingCoeff_map_of_injective hinj, norm_algebraMap_padicInt]
  have hres : φ (resultant A B) = A'.leadingCoeff ^ B.natDegree *
      (A'.roots.map fun z => B'.leadingCoeff * (B'.roots.map fun w => z - w).prod).prod := by
    rw [← resultant_map_map, ← hAdeg,
      resultant_eq_prod_eval A' B' _ hBdeg.le (IsAlgClosed.splits _)]
    congr 2
    exact Multiset.map_congr rfl fun z _ => (IsAlgClosed.splits B').eval_eq_prod_roots z
  have hnorm : ‖resultant A B‖ = ‖A.leadingCoeff‖ ^ B.natDegree *
      (A'.roots.map fun z => ‖B.leadingCoeff‖ * (B'.roots.map fun w => ‖z - w‖).prod).prod := by
    rw [← norm_algebraMap_padicInt, hres, norm_mul, norm_pow, hAlc, norm_multiset_prod_map]
    simp only [norm_mul, norm_multiset_prod_map, hBlc]
  have hlcA : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hA.ne_zero
  have hlcB : B.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hB.ne_zero
  have hlcA' : ‖A.leadingCoeff‖ ≠ 0 := norm_ne_zero_iff.mpr hlcA
  have hlcB' : ‖B.leadingCoeff‖ ≠ 0 := norm_ne_zero_iff.mpr hlcB
  have hdist : ∀ z ∈ A'.roots, ∀ w ∈ B'.roots, ‖z - w‖ ≠ 0 := fun z hz w hw =>
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hdisj z hz w hw))
  have hinner : ∀ z ∈ A'.roots, (B'.roots.map fun w => ‖z - w‖).prod ≠ 0 := by
    intro z hz
    apply Multiset.prod_ne_zero
    intro h0
    obtain ⟨w, hw, hw0⟩ := Multiset.mem_map.mp h0
    exact hdist z hz w hw hw0
  have hlog : Real.logb p ‖resultant A B‖ = B.natDegree * Real.logb p ‖A.leadingCoeff‖ +
      (A'.roots.map fun z => Real.logb p ‖B.leadingCoeff‖ +
        (B'.roots.map fun w => Real.logb p ‖z - w‖).sum).sum := by
    rw [hnorm, Real.logb_mul (pow_ne_zero _ hlcA'), Real.logb_pow,
      logb_multiset_prod_map _ _ (fun z hz => mul_ne_zero hlcB' (hinner z hz))]
    · congr 1
      refine congrArg Multiset.sum (Multiset.map_congr rfl fun z hz => ?_)
      rw [Real.logb_mul hlcB' (hinner z hz), logb_multiset_prod_map _ _ (hdist z hz)]
    · apply Multiset.prod_ne_zero
      intro h0
      obtain ⟨z, hz, hz0⟩ := Multiset.mem_map.mp h0
      exact mul_ne_zero hlcB' (hinner z hz) hz0
  have hmassA : Real.logb p ‖A.leadingCoeff‖ +
      (A'.roots.map fun w => Real.logb p (max 1 ‖w‖)).sum = 0 :=
    logb_norm_leadingCoeff_add_sum hA
  have hmassB : Real.logb p ‖B.leadingCoeff‖ +
      (B'.roots.map fun w => Real.logb p (max 1 ‖w‖)).sum = 0 :=
    logb_norm_leadingCoeff_add_sum hB
  have hcardA : A'.roots.card = A.natDegree := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hAdeg]
  have hcardB : B'.roots.card = B.natDegree := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hBdeg]
  have hrow : ∀ z, (B'.roots.map fun w => projDist p z w).sum =
      -(B'.roots.map fun w => Real.logb p ‖z - w‖).sum +
        B.natDegree * Real.logb p (max 1 ‖z‖) - Real.logb p ‖B.leadingCoeff‖ := by
    intro z
    simp only [projDist_eq, Multiset.sum_map_add, Multiset.sum_map_neg, Multiset.map_const',
      Multiset.sum_replicate, nsmul_eq_mul, hcardB]
    linarith
  simp only [hrow, Multiset.sum_map_sub, Multiset.sum_map_add, Multiset.sum_map_neg,
    Multiset.sum_map_mul_left, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul,
    hcardA]
  unfold padicVal
  rw [hlog]
  simp only [Multiset.sum_map_add, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul,
    hcardA]
  linear_combination (-(B.natDegree : ℝ)) * hmassA

end Gauss

end ArithmeticOfJacobiPolynomials
