/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.InertiaCyclePadicUnramified
public import ArithmeticOfJacobiPolynomials.Padic.SourceHensel
public import StacksFrontier.RingTheory.DiscreteValuationRing.Galois
public import Mathlib

/-!
# The tame local cycle in Lemma 5.1

Let `f ∈ ℤ_[p][X]` satisfy `LocalHyp p d f` (`a₀` a unit, `p ∥ a_N`, `f̄` squarefree of degree
`N - d`, `2 ≤ d < p`).  The manuscript's proof of the first assertion:

1. The reciprocal polynomial `R = Y^N f(1/Y)` has reduction `Y^d · B̄` with `B̄(0) ≠ 0`; Hensel's
   lemma (Stacks Tag 03QH, `SourceHensel`) gives `R = a₀ A B` with `A, B` monic,
   `A ≡ Y^d (mod p)`, `deg A = d`, `B(0)` a unit, and `A` is Eisenstein
   (`exists_reciprocal_factor`).
2. The roots `y` of `f` with `1 < v y` are exactly the inverses of the roots of `A`; the other
   roots are inverses of roots of `B`, units, fixed by inertia (`root_inv_of_one_lt`,
   `inv_root_of_eisenstein_root`). The fixation of these other roots is
   `InertiaCyclePadic.apply_eq_of_mem_inertia`: distinct roots `y` with `v y ≤ 1` are incongruent
   modulo `P` (the reduction of `f` is squarefree) and inertia acts trivially modulo `P`. This is
   the equivalent form, for the hypothesis `f̄` squarefree, of the manuscript's statement that
   these roots lie in an unramified extension.
3. `A` is Eisenstein over the unramified inertia field `T = K^I` (the constant term `p·unit`
   is not in `Q²` as `e(Q/p) = 1`), hence irreducible over `T`; so `I = Gal(K/T)` is transitive on
   its `d` roots.
4. Stacks Tag 09EE: the wild inertia `W ◁ I` is a `p`-group and `I/W` embeds in the
   cyclic group of roots of unity of the residue field.  `W` acts faithfully on the `d < p`
   roots of `A`, so `W = 1`, `I` is cyclic, and a generator of the transitive cyclic group `I` is a
   `d`-cycle.
-/

public section

namespace ArithmeticOfJacobiPolynomials

namespace SourceInertia

open Polynomial renaming X → polyX
open Polynomial IsDedekindDomain LocalRootResidues InertiaCyclePadic

variable {p : ℕ} [hp : Fact p.Prime]

theorem isUnit_of_not_dvd {c : ℤ_[p]} (h : ¬ (p : ℤ_[p]) ∣ c) : IsUnit c := by
  rw [← IsLocalRing.notMem_maximalIdeal, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]
  exact h

section Poly

variable {d : ℕ} {f : ℤ_[p][X]}

/-- **Step 1 of Lemma 5.1**: the reciprocal polynomial of `f` is `a₀ A B` with
`A, B` monic, `deg A = d`, `B(0)` a unit and `A` Eisenstein at `p` (Hensel's lemma, Stacks
Tag 03QH). -/
theorem exists_reciprocal_factor (hf : LocalHyp p d f) :
    ∃ A B : ℤ_[p][X], f.reverse = C (f.coeff 0) * (A * B) ∧ A.Monic ∧ B.Monic ∧
      A.natDegree = d ∧ IsUnit (B.coeff 0) ∧
      A.IsEisensteinAt (IsLocalRing.maximalIdeal ℤ_[p]) := by
  obtain ⟨u, hu⟩ := hf.isUnit_coeff_zero
  have hdN : d ≤ f.natDegree := hf.le_natDegree
  have htr : f.natTrailingDegree = 0 :=
    natTrailingDegree_eq_zero.mpr (Or.inr (by rw [← hu]; exact u.ne_zero))
  have hrevdeg : f.reverse.natDegree = f.natDegree := by rw [reverse_natDegree, htr]; simp
  have hrevlc : f.reverse.leadingCoeff = (u : ℤ_[p]) := by
    rw [reverse_leadingCoeff, trailingCoeff, htr, hu]
  set g : ℤ_[p][X] := C ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * f.reverse with hg
  have hgm : g.Monic := by
    rw [Monic, hg, leadingCoeff_mul, leadingCoeff_C, hrevlc, Units.inv_mul]
  have hcoeff : ∀ i ≤ f.natDegree, g.coeff i =
      ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * f.coeff (f.natDegree - i) := by
    intro i hi
    rw [hg, coeff_C_mul, coeff_reverse, revAt_le hi]
  have hlow : ∀ i < d, (p : ℤ_[p]) ∣ g.coeff i := by
    intro i hi
    rw [hcoeff i (by omega)]
    exact dvd_mul_of_dvd_right (hf.dvd_coeff_of_lt (by omega)) _
  obtain ⟨w, hw, hwu⟩ := hf.lead_eq
  have h0 : ¬ (p : ℤ_[p]) ^ 2 ∣ g.coeff 0 := by
    rw [hcoeff 0 (Nat.zero_le _), Nat.sub_zero, hw]
    intro h
    have h1 : (p : ℤ_[p]) ^ 2 ∣ (p : ℤ_[p]) * w := (Units.isUnit _).dvd_mul_left.mp h
    rw [pow_two, mul_dvd_mul_iff_left PadicInt.prime_p.ne_zero] at h1
    exact PadicInt.prime_p.not_isUnit (isUnit_of_dvd_unit h1 hwu)
  have hdd : IsUnit (g.coeff d) := by
    rw [hcoeff d hdN]
    exact (Units.isUnit _).mul (isUnit_of_not_dvd hf.not_dvd_coeff_sub)
  obtain ⟨A, B, hAB, hAm, hAdeg, -, hBm, hB0, hAE⟩ :=
    exists_monic_eisenstein_factor_of_pow hgm hlow h0 hdd
  refine ⟨A, B, ?_, hAm, hBm, hAdeg, hB0, hAE⟩
  have : f.reverse = C (u : ℤ_[p]) * g := by
    rw [hg, ← mul_assoc, ← C_mul, Units.mul_inv, C_1, one_mul]
  rw [this, hAB, hu]

end Poly

section Roots

variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] [Algebra ℤ_[p] K]
  [IsScalarTower ℤ_[p] ℚ_[p] K] (P : HeightOneSpectrum (integralClosure ℤ_[p] K))
  [P.asIdeal.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]

omit [P.asIdeal.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] in
theorem valuation_algebraMap_le_one (a : ℤ_[p]) : P.valuation K (algebraMap ℤ_[p] K a) ≤ 1 :=
  valuation_coe_le_one P ⟨algebraMap ℤ_[p] K a, isIntegral_algebraMap⟩

omit [P.asIdeal.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] in
/-- A root of a monic polynomial over `ℤ_[p]` is `P`-integral. -/
theorem valuation_le_one_of_monic_root {A : ℤ_[p][X]} (hA : A.Monic) {z : K}
    (hz : (A.map (algebraMap ℤ_[p] K)).eval z = 0) : P.valuation K z ≤ 1 :=
  valuation_coe_le_one P ⟨z, ⟨A, hA, by rwa [eval₂_eq_eval_map]⟩⟩

/-- A root `z` of a monic `A ≡ Y^d (mod p)` has `v z < 1`. -/
theorem valuation_lt_one_of_eisenstein_root {A : ℤ_[p][X]} {d : ℕ} (hA : A.Monic)
    (hdeg : A.natDegree = d) (hlow : ∀ i < d, (p : ℤ_[p]) ∣ A.coeff i) {z : K}
    (hz : (A.map (algebraMap ℤ_[p] K)).eval z = 0) : P.valuation K z < 1 := by
  have hv := isPadicAt P
  by_contra hcon
  have hz1 : P.valuation K z = 1 :=
    le_antisymm (valuation_le_one_of_monic_root P hA hz) (not_lt.mp hcon)
  have hcd : A.coeff d = 1 := by rw [← hdeg]; exact hA
  rw [eval_map, eval₂_eq_sum_range' (algebraMap ℤ_[p] K) (n := d + 1) (by omega),
    Finset.sum_range_succ, hcd, map_one, one_mul] at hz
  have hsum : P.valuation K (∑ i ∈ Finset.range d, algebraMap ℤ_[p] K (A.coeff i) * z ^ i) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero (fun i hi => ?_)
    rw [Valuation.map_mul, Valuation.map_pow, hz1, one_pow, mul_one]
    exact (hv _).mpr (hlow i (Finset.mem_range.mp hi))
  have h2 : z ^ d = -(∑ i ∈ Finset.range d, algebraMap ℤ_[p] K (A.coeff i) * z ^ i) := by
    linear_combination hz
  have h3 := congrArg (P.valuation K) h2
  rw [Valuation.map_neg, Valuation.map_pow, hz1, one_pow] at h3
  exact absurd hsum (by rw [← h3]; exact lt_irrefl _)

/-- If `B(0)` is a unit, `B` has no root `z` with `v z < 1`. -/
theorem eval_map_ne_zero_of_valuation_lt_one {B : ℤ_[p][X]} (hB : IsUnit (B.coeff 0)) {z : K}
    (hz : P.valuation K z < 1) : (B.map (algebraMap ℤ_[p] K)).eval z ≠ 0 := by
  have hv := isPadicAt P
  intro h0
  rw [eval_map, eval₂_eq_sum_range' (algebraMap ℤ_[p] K) (n := B.natDegree + 1) (by omega),
    Finset.sum_range_succ'] at h0
  have h1 : P.valuation K
      (∑ i ∈ Finset.range B.natDegree, algebraMap ℤ_[p] K (B.coeff (i + 1)) * z ^ (i + 1)) < 1 := by
    refine Valuation.map_sum_lt _ one_ne_zero (fun i _ => ?_)
    rw [Valuation.map_mul, Valuation.map_pow]
    calc _ ≤ 1 * P.valuation K z ^ (i + 1) :=
          mul_le_mul_left (valuation_algebraMap_le_one P _) _
      _ < 1 := by rw [one_mul]; exact pow_lt_one₀ zero_le hz (Nat.succ_ne_zero i)
  have h2 : P.valuation K (algebraMap ℤ_[p] K (B.coeff 0) * z ^ 0) = 1 := by
    rw [pow_zero, mul_one]; exact hv.eq_one_of_isUnit hB
  have h3 := Valuation.map_add_eq_of_lt_right (P.valuation K) (h2 ▸ h1 :
    P.valuation K (∑ i ∈ Finset.range B.natDegree,
      algebraMap ℤ_[p] K (B.coeff (i + 1)) * z ^ (i + 1)) <
      P.valuation K (algebraMap ℤ_[p] K (B.coeff 0) * z ^ 0))
  rw [h0, Valuation.map_zero, h2] at h3
  exact zero_ne_one h3

omit [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] [Algebra ℤ_[p] K]
  [IsScalarTower ℤ_[p] ℚ_[p] K] in
theorem eval_reverse_inv_eq_zero_iff (φ : ℤ_[p] →+* K) {y : K} (hy : y ≠ 0) (f : ℤ_[p][X]) :
    (f.reverse.map φ).eval y⁻¹ = 0 ↔ (f.map φ).eval y = 0 := by
  let _ : Invertible y := invertibleOfNonzero hy
  have h := eval₂_reverse_eq_zero_iff φ y f
  rwa [invOf_eq_inv, eval₂_eq_eval_map, eval₂_eq_eval_map] at h

variable {d : ℕ} {f A B : ℤ_[p][X]}

/-- **Step 2 of Lemma 5.1**: the inverse of a root of `f` with `1 < v y` is a root
of the Eisenstein factor `A`. -/
theorem root_inv_of_one_lt (hf : LocalHyp p d f)
    (hrev : f.reverse = C (f.coeff 0) * (A * B)) (hBu : IsUnit (B.coeff 0)) {y : K}
    (hy : (f.map (algebraMap ℤ_[p] K)).eval y = 0) (h1 : 1 < P.valuation K y) :
    (A.map (algebraMap ℤ_[p] K)).eval y⁻¹ = 0 := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [Valuation.map_zero] at h1
    exact absurd h1 (not_lt.mpr zero_le)
  have hinv : P.valuation K y⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ h1
  have h := (eval_reverse_inv_eq_zero_iff (algebraMap ℤ_[p] K) hy0 f).mpr hy
  rw [hrev, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_mul, eval_mul, eval_C,
    eval_mul] at h
  have hc : algebraMap ℤ_[p] K (f.coeff 0) ≠ 0 :=
    (hf.isUnit_coeff_zero.map (algebraMap ℤ_[p] K)).ne_zero
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h hc
  rcases mul_eq_zero.mp h with h | h
  · exact h
  · exact absurd h (eval_map_ne_zero_of_valuation_lt_one P hBu hinv)

/-- The inverse of a root of the Eisenstein factor `A` is a root of `f` with `1 < v`. -/
theorem inv_root_of_eisenstein_root (hrev : f.reverse = C (f.coeff 0) * (A * B))
    (hAm : A.Monic) (hdeg : A.natDegree = d)
    (hAE : A.IsEisensteinAt (IsLocalRing.maximalIdeal ℤ_[p])) {z : K}
    (hz : (A.map (algebraMap ℤ_[p] K)).eval z = 0) :
    z ≠ 0 ∧ (f.map (algebraMap ℤ_[p] K)).eval z⁻¹ = 0 ∧ 1 < P.valuation K z⁻¹ := by
  have hlow : ∀ i < d, (p : ℤ_[p]) ∣ A.coeff i := by
    intro i hi
    have := hAE.mem (n := i) (by omega)
    rwa [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this
  have hlt := valuation_lt_one_of_eisenstein_root P hAm hdeg hlow hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [← coeff_zero_eq_eval_zero] at hz
    simp only [coeff_map] at hz
    have h0 : A.coeff 0 = 0 := (algebraMap_padicInt_injective p K) (by rw [hz, map_zero])
    exact hAE.notMem (by rw [h0]; exact Ideal.zero_mem _)
  refine ⟨hz0, ?_, ?_⟩
  · have hz' : (f.reverse.map (algebraMap ℤ_[p] K)).eval z = 0 := by
      rw [hrev, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_mul, eval_mul, eval_C,
        eval_mul, hz, zero_mul, mul_zero]
    have := (eval_reverse_inv_eq_zero_iff (algebraMap ℤ_[p] K) (inv_ne_zero hz0) f).mp
      (by rwa [inv_inv])
    exact this
  · rw [map_inv₀]
    exact one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr (by rwa [Ne, Valuation.zero_iff]), hlt⟩

end Roots

section Irreducible

/-- If `q` has ramification index `1` over `p` (Dedekind case), then `p S ≰ q²`. -/
theorem not_map_le_sq_of_ramificationIdx_eq_one {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain S] [Algebra R S] (p : Ideal R) (q : Ideal S) [q.IsPrime]
    [q.LiesOver p] (hp : p.map (algebraMap R S) ≠ ⊥) (he : q.ramificationIdx R = 1) :
    ¬ p.map (algebraMap R S) ≤ q ^ 2 := by
  intro hle
  have hq : q ≠ ⊥ := ne_bot_of_le_ne_bot hp (Ideal.map_le_of_le_comap (q.over_def p).le)
  have h1 := Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count p q hp
  have h2 := UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors
    (Ideal.prime_of_isPrime hq inferInstance).irreducible hp
  have h3 := le_emultiplicity_of_pow_dvd (Ideal.dvd_iff_le.mpr hle)
  rw [h2, normalize_eq, ← h1, he] at h3
  norm_num at h3

variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] [Algebra ℤ_[p] K]
  [IsScalarTower ℤ_[p] ℚ_[p] K] [IsGalois ℚ_[p] K]
  (P : HeightOneSpectrum (integralClosure ℤ_[p] K))
  [P.asIdeal.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]

/-- **Step 3 of Lemma 5.1**: an Eisenstein polynomial over `ℤ_[p]` stays
irreducible over the inertia field `T = K^{I_P}`: `T/ℚ_p` is unramified at `P ∩ 𝒪_T`, so the
constant term `p·unit` is not in `(P ∩ 𝒪_T)²`, and the Eisenstein criterion applies over `𝒪_T`. -/
theorem irreducible_map_inertiaField {A : ℤ_[p][X]} (hAm : A.Monic) (hd : 0 < A.natDegree)
    (hAE : A.IsEisensteinAt (IsLocalRing.maximalIdeal ℤ_[p])) :
    Irreducible (A.map (algebraMap ℤ_[p] (inertiaField P))) := by
  set T := inertiaField P
  set O := integralClosure ℤ_[p] T
  set 𝔮 : Ideal O := P.asIdeal.under O with h𝔮
  have : 𝔮.IsPrime := Ideal.IsPrime.under _ _
  have : 𝔮.LiesOver (IsLocalRing.maximalIdeal ℤ_[p]) := liesOver_under_intermediateField P T
  have he : 𝔮.ramificationIdx ℤ_[p] = 1 := ramificationIdx_under_inertiaField P
  have hover : IsLocalRing.maximalIdeal ℤ_[p] = 𝔮.comap (algebraMap ℤ_[p] O) :=
    Ideal.over_def 𝔮 _
  have hmem : ∀ a : ℤ_[p], a ∈ IsLocalRing.maximalIdeal ℤ_[p] ↔ algebraMap ℤ_[p] O a ∈ 𝔮 := by
    intro a; rw [hover, Ideal.mem_comap]
  have hAm' : (A.map (algebraMap ℤ_[p] O)).Monic := hAm.map _
  have hdeg' : (A.map (algebraMap ℤ_[p] O)).natDegree = A.natDegree := hAm.natDegree_map _
  have hE : (A.map (algebraMap ℤ_[p] O)).IsEisensteinAt 𝔮 := by
    refine ⟨?_, fun {n} hn => ?_, ?_⟩
    · rw [hAm'.leadingCoeff]; exact (Ideal.ne_top_iff_one _).mp (Ideal.IsPrime.ne_top ‹_›)
    · rw [coeff_map, ← hmem]; exact hAE.mem (by rwa [hdeg'] at hn)
    · rw [coeff_map]
      intro hsq
      obtain ⟨w, hw⟩ : ∃ w, A.coeff 0 = (p : ℤ_[p]) * w := by
        have := hAE.mem (n := 0) hd
        rwa [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this
      have hwu : IsUnit w := by
        refine isUnit_of_not_dvd fun hdvd => hAE.notMem ?_
        obtain ⟨t, ht⟩ := hdvd
        rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
          hw, ht]
        exact ⟨t, by ring⟩
      have hpsq : algebraMap ℤ_[p] O (p : ℤ_[p]) ∈ 𝔮 ^ 2 := by
        have hu' : IsUnit (algebraMap ℤ_[p] O w) := hwu.map _
        obtain ⟨u, hu⟩ := hu'
        have : algebraMap ℤ_[p] O (p : ℤ_[p]) =
            algebraMap ℤ_[p] O (A.coeff 0) * ((u⁻¹ : Oˣ) : O) := by
          rw [hw, map_mul, ← hu, mul_assoc, Units.mul_inv, mul_one]
        rw [this]
        exact Ideal.mul_mem_right _ _ hsq
      have hle : (IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] O) ≤ 𝔮 ^ 2 := by
        rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton,
          Ideal.span_le, Set.singleton_subset_iff]
        exact hpsq
      have hne : (IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] O) ≠ ⊥ := by
        intro h
        have hp0 : algebraMap ℤ_[p] O (p : ℤ_[p]) ∈
            (IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] O) :=
          Ideal.mem_map_of_mem _ (by
            rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _)
        rw [h, Ideal.mem_bot] at hp0
        have hinj : Function.Injective (algebraMap ℤ_[p] O) := fun a b hab =>
          algebraMap_padicInt_injective p T (congrArg (fun z : O => (z : T)) hab)
        exact PadicInt.prime_p.ne_zero (hinj (by rw [hp0, map_zero]))
      exact not_map_le_sq_of_ramificationIdx_eq_one _ 𝔮 hne he hle
  have hirr : Irreducible (A.map (algebraMap ℤ_[p] O)) :=
    hE.irreducible inferInstance hAm'.isPrimitive (by rwa [hdeg'])
  have := (hAm'.irreducible_iff_irreducible_map_fraction_map (K := T)).mp hirr
  rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at this

end Irreducible

section Orbit

variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] [Algebra ℤ_[p] K]
  [IsScalarTower ℤ_[p] ℚ_[p] K] [IsGalois ℚ_[p] K]
  (P : HeightOneSpectrum (integralClosure ℤ_[p] K))
  [P.asIdeal.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]

/-- The minimal polynomial over the inertia field of any root of the Eisenstein factor `A`. -/
theorem minpoly_inertiaField_eq {A : ℤ_[p][X]} (hAm : A.Monic) (hd : 0 < A.natDegree)
    (hAE : A.IsEisensteinAt (IsLocalRing.maximalIdeal ℤ_[p])) {z : K}
    (hz : (A.map (algebraMap ℤ_[p] K)).eval z = 0) :
    minpoly (inertiaField P) z = A.map (algebraMap ℤ_[p] (inertiaField P)) := by
  refine (minpoly.eq_of_irreducible_of_monic (irreducible_map_inertiaField P hAm hd hAE) ?_
    (hAm.map _)).symm
  rw [aeval_map_algebraMap, aeval_def, eval₂_eq_eval_map]
  exact hz

/-- **Step 3 of Lemma 5.1, transitivity**: the inertia group acts transitively on
the roots of the Eisenstein factor `A` (it is `Gal(K/T)`, and `A` is irreducible over `T`). -/
theorem exists_mem_inertia_apply_eq {A : ℤ_[p][X]} (hAm : A.Monic) (hd : 0 < A.natDegree)
    (hAE : A.IsEisensteinAt (IsLocalRing.maximalIdeal ℤ_[p])) {z₁ z₂ : K}
    (h₁ : (A.map (algebraMap ℤ_[p] K)).eval z₁ = 0)
    (h₂ : (A.map (algebraMap ℤ_[p] K)).eval z₂ = 0) :
    ∃ σ ∈ P.asIdeal.inertia Gal(K/ℚ_[p]), σ z₁ = z₂ := by
  have hm : minpoly (inertiaField P) z₂ = minpoly (inertiaField P) z₁ :=
    (minpoly_inertiaField_eq P hAm hd hAE h₂).trans (minpoly_inertiaField_eq P hAm hd hAE h₁).symm
  obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := inertiaField P) (E := K)).mp hm
  refine ⟨g.restrictScalars ℚ_[p], ?_, hg⟩
  rw [← IntermediateField.fixingSubgroup_fixedField (P.asIdeal.inertia Gal(K/ℚ_[p]))]
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun x hx => g.commutes ⟨x, hx⟩

include P in
/-- The Eisenstein factor `A` has `d` distinct roots in `K` as soon as it has one (it is
irreducible over the inertia field, hence separable, and `K/T` is normal). -/
theorem roots_nodup_card {A : ℤ_[p][X]} (hAm : A.Monic) (hd : 0 < A.natDegree)
    (hAE : A.IsEisensteinAt (IsLocalRing.maximalIdeal ℤ_[p])) {z₀ : K}
    (h₀ : (A.map (algebraMap ℤ_[p] K)).eval z₀ = 0) :
    (A.map (algebraMap ℤ_[p] K)).roots.Nodup ∧
      Multiset.card (A.map (algebraMap ℤ_[p] K)).roots = A.natDegree := by
  have := charZero_of_padic p (inertiaField P)
  have hmp := minpoly_inertiaField_eq P hAm hd hAE h₀
  have hsplit := Normal.splits (inferInstance : Normal (inertiaField P) K) z₀
  rw [hmp, Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at hsplit
  have hK : (A.map (algebraMap ℤ_[p] K)) = (A.map (algebraMap ℤ_[p] (inertiaField P))).map
      (algebraMap (inertiaField P) K) := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  refine ⟨?_, ?_⟩
  · rw [hK]
    exact Polynomial.nodup_roots (Polynomial.Separable.map
      (irreducible_map_inertiaField P hAm hd hAE).separable)
  · rw [splits_iff_card_roots.mp hsplit, hAm.natDegree_map]

end Orbit

section Cyclic

variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] [Algebra ℤ_[p] K]
  [IsScalarTower ℤ_[p] ℚ_[p] K] [IsGalois ℚ_[p] K]
  (P : HeightOneSpectrum (integralClosure ℤ_[p] K))
  [P.asIdeal.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])]

omit [FiniteDimensional ℚ_[p] K] [P.asIdeal.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] in
/-- The `Gal(K/ℚ_[p])`-action on `𝒪_K` used by the Stacks theorem
(`IsIntegralClosure.MulSemiringAction`) gives the same inertia group as Mathlib's action on
`integralClosure ℤ_[p] K`: both act by `b ↦ σ b`. -/
theorem inertia_stacks_eq :
    (letI := IsIntegralClosure.MulSemiringAction ℤ_[p] ℚ_[p] K (integralClosure ℤ_[p] K)
     P.asIdeal.inertia Gal(K/ℚ_[p])) = P.asIdeal.inertia Gal(K/ℚ_[p]) := by
  ext σ
  simp only [Ideal.mem_inertia]
  refine forall_congr' fun b => ?_
  apply iff_of_eq
  congr 2
  apply Subtype.ext
  exact algebraMap_galRestrictHom_apply ℤ_[p] ℚ_[p] K (integralClosure ℤ_[p] K) σ b

/-- The permutation of the roots of `A` in `K` induced by a `ℚ_[p]`-automorphism of `K`. -/
@[expose] noncomputable def permRoots (A : ℤ_[p][X]) :
    Gal(K/ℚ_[p]) →* Equiv.Perm {z : K // (A.map (algebraMap ℤ_[p] K)).eval z = 0} :=
  MonoidHom.mk' (fun σ =>
    { toFun := fun z => ⟨σ z.1, by rw [eval_map_galois_apply, z.2, map_zero]⟩
      invFun := fun z => ⟨σ⁻¹ z.1, by rw [eval_map_galois_apply, z.2, map_zero]⟩
      left_inv := fun z => Subtype.ext (by simp [AlgEquiv.aut_inv])
      right_inv := fun z => Subtype.ext (by simp [AlgEquiv.aut_inv]) })
    (fun σ τ => Equiv.ext fun z => Subtype.ext rfl)

omit [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K] in
theorem permRoots_apply (A : ℤ_[p][X]) (σ : Gal(K/ℚ_[p]))
    (z : {z : K // (A.map (algebraMap ℤ_[p] K)).eval z = 0}) :
    ((permRoots A σ z : {z : K // (A.map (algebraMap ℤ_[p] K)).eval z = 0}) : K) = σ z.1 := rfl

/-- **Step 4 of Lemma 5.1, the wild part is trivial**: the Sylow-`p` wild inertia
`W` of Stacks 09EE acts faithfully on the `d < p` roots of `A`, so it is trivial; then the
inertia group embeds in the cyclic group of roots of unity of the residue field. -/
theorem isCyclic_inertia {d : ℕ} {f A B : ℤ_[p][X]} (hf : LocalHyp p d f)
    (hrev : f.reverse = C (f.coeff 0) * (A * B)) (hAm : A.Monic) (hAdeg : A.natDegree = d)
    (hBu : IsUnit (B.coeff 0))
    (hAE : A.IsEisensteinAt (IsLocalRing.maximalIdeal ℤ_[p]))
    (hfaith : ∀ σ : Gal(K/ℚ_[p]),
      (∀ y, (f.map (algebraMap ℤ_[p] K)).eval y = 0 → σ y = y) → σ = 1)
    {z₀ : K} (h₀ : (A.map (algebraMap ℤ_[p] K)).eval z₀ = 0) :
    IsCyclic (P.asIdeal.inertia Gal(K/ℚ_[p])) := by
  classical
  have hPmax : P.asIdeal.IsMaximal := P.isPrime.isMaximal P.ne_bot
  have hd0 : 0 < A.natDegree := by rw [hAdeg]; exact hf.pos
  obtain ⟨hnodup, hcard⟩ := roots_nodup_card P hAm hd0 hAE h₀
  -- the set of roots of `A` in `K` is finite of size `d < p`
  set Rs := (A.map (algebraMap ℤ_[p] K)).roots.toFinset with hRs
  have hmemRs : ∀ z, z ∈ Rs ↔ (A.map (algebraMap ℤ_[p] K)).eval z = 0 := by
    intro z
    rw [hRs, Multiset.mem_toFinset, mem_roots', IsRoot.def]
    exact ⟨fun h => h.2, fun h => ⟨(hAm.map _).ne_zero, h⟩⟩
  have hRscard : Rs.card = d := by
    rw [hRs, Multiset.toFinset_card_of_nodup hnodup, hcard, hAdeg]
  have : Finite {z : K // (A.map (algebraMap ℤ_[p] K)).eval z = 0} :=
    Finite.of_injective (fun z => (⟨z.1, (hmemRs z.1).mpr z.2⟩ : Rs))
      (fun a b h => Subtype.ext (congrArg (fun r : Rs => (r : K)) h))
  let _ : Fintype {z : K // (A.map (algebraMap ℤ_[p] K)).eval z = 0} := Fintype.ofFinite _
  have hRcard : Fintype.card {z : K // (A.map (algebraMap ℤ_[p] K)).eval z = 0} = d := by
    rw [← hRscard, ← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun z => (hmemRs z).symm)
  -- the wild/tame structure of the inertia group (Stacks 09EE)
  have hchar : ringChar (IsLocalRing.ResidueField ℤ_[p]) = p := by
    have : CharP (IsLocalRing.ResidueField ℤ_[p]) p :=
      charP_of_injective_ringHom
        (f := ((PadicInt.residueField (p := p)).symm : ZMod p →+* _))
        (PadicInt.residueField (p := p)).symm.injective p
    exact ringChar.eq _ p
  obtain ⟨W, hWn, -, -, -, hWp, -, -, θ, -, hexact, -, hcyc, -⟩ :=
    IsDiscreteValuationRing.exists_wildInertia_exact_and_tameInertia_equiv_rootsOfUnity
      ℤ_[p] ℚ_[p] K P.asIdeal
  have hWp' : IsPGroup p W := by
    have := hWp (by rw [hchar]; exact hp.out.pos)
    rwa [hchar] at this
  have hWbot : ∀ w : W, w.1.1 = 1 := by
    intro w
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hWp' w
    have hgI : w.1.1 ∈ P.asIdeal.inertia Gal(K/ℚ_[p]) :=
      (SetLike.ext_iff.mp (inertia_stacks_eq P) w.1.1).mp w.1.2
    set g : Gal(K/ℚ_[p]) := w.1.1 with hgdef
    have hg : g ^ (p ^ k) = 1 := by
      have h := pow_orderOf_eq_one w
      rw [hk] at h
      simpa [hgdef] using congrArg (fun x : W => x.1.1) h
    have hρ1 : permRoots (K := K) A g ^ (p ^ k) = 1 := by rw [← map_pow, hg, map_one]
    have hρ2 : permRoots (K := K) A g ^ (Nat.factorial d) = 1 := by
      rw [← hRcard, ← Fintype.card_perm]; exact pow_card_eq_one
    have hcop : Nat.Coprime (p ^ k) (Nat.factorial d) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr
        (by rw [hp.out.dvd_factorial]; exact not_le.mpr hf.lt))
    have hρ : permRoots (K := K) A g = 1 := by
      have := pow_gcd_eq_one.mpr ⟨hρ1, hρ2⟩
      rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
    refine hfaith g (fun y hy => ?_)
    by_cases hy1 : P.valuation K y ≤ 1
    · exact apply_eq_of_mem_inertia P hf hgI hy hy1
    · have hA := root_inv_of_one_lt P hf hrev hBu hy (not_le.mp hy1)
      have h := congrArg Subtype.val (DFunLike.congr_fun hρ ⟨y⁻¹, hA⟩)
      rw [permRoots_apply] at h
      change g y⁻¹ = y⁻¹ at h
      rwa [map_inv₀, inv_inj] at h
  have hinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨w, hw⟩ := (hexact x).mp hx
    rw [← hw]
    exact Subtype.ext (hWbot w)
  have hcycS := isCyclic_of_injective θ hinj
  exact (inertia_stacks_eq P) ▸ hcycS

end Cyclic

section Main

variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] [Algebra ℤ_[p] K]
  [IsScalarTower ℤ_[p] ℚ_[p] K] [IsGalois ℚ_[p] K]
  (P : HeightOneSpectrum (integralClosure ℤ_[p] K))
  [P.asIdeal.LiesOver (IsLocalRing.maximalIdeal ℤ_[p])] {d : ℕ} {f : ℤ_[p][X]}

/-- **The local form of Lemma 5.1, first assertion**:
if `f` splits in `K` and `K` is generated by the roots of `f` (`hfaith`), a generator `τ` of the
inertia group `I_P` acts on the roots of `f` in `K` as a single cycle on the `d` roots `y` with
`1 < v y`, fixing all other roots. -/
theorem exists_mem_inertia_generator [DecidableEq K] (hf : LocalHyp p d f) (hd2 : 2 ≤ d)
    (hsplit : Multiset.card (f.map (algebraMap ℤ_[p] K)).roots = f.natDegree)
    (hfaith : ∀ σ : Gal(K/ℚ_[p]),
      (∀ y, (f.map (algebraMap ℤ_[p] K)).eval y = 0 → σ y = y) → σ = 1) :
    ∃ τ ∈ P.asIdeal.inertia Gal(K/ℚ_[p]),
      (∀ y, (f.map (algebraMap ℤ_[p] K)).eval y = 0 → (τ y ≠ y ↔ 1 < P.valuation K y)) ∧
      ∃ y₀, (f.map (algebraMap ℤ_[p] K)).eval y₀ = 0 ∧ 1 < P.valuation K y₀ ∧
        (∀ y, (f.map (algebraMap ℤ_[p] K)).eval y = 0 → 1 < P.valuation K y →
          ∃ k : ℤ, (τ ^ k) y₀ = y) ∧
        ((f.map (algebraMap ℤ_[p] K)).roots.toFinset.filter
          (fun y => 1 < P.valuation K y)).card = d := by
  have := charZero_of_padic p K
  obtain ⟨A, B, hrev, hAm, hBm, hAdeg, hBu, hAE⟩ := exists_reciprocal_factor hf
  have hd0 : 0 < A.natDegree := by omega
  have hv := isPadicAt P
  have hf0 : f.map (algebraMap ℤ_[p] K) ≠ 0 := by
    refine (Polynomial.map_ne_zero_iff (algebraMap_padicInt_injective p K)).mpr fun h => ?_
    have := hf.isUnit_coeff_zero
    rw [h, coeff_zero] at this
    exact not_isUnit_zero this
  -- a root `y₀` of `f` with `1 < v y₀`
  have hcard := card_filter_roots_one_lt hf hv hsplit
  obtain ⟨y₀, hy₀⟩ := Multiset.card_pos_iff_exists_mem.mp (by rw [hcard]; omega)
  rw [Multiset.mem_filter, mem_roots', IsRoot.def] at hy₀
  obtain ⟨⟨-, hy₀r⟩, hy₀1⟩ := hy₀
  have hA₀ := root_inv_of_one_lt P hf hrev hBu hy₀r hy₀1
  obtain ⟨hnodup, hcardA⟩ := roots_nodup_card P hAm hd0 hAE hA₀
  have hcyc := isCyclic_inertia P hf hrev hAm hAdeg hBu hAE hfaith hA₀
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := P.asIdeal.inertia Gal(K/ℚ_[p]))
  -- the roots with `1 < v` are the inverses of the roots of `A`
  have hSimg : ((f.map (algebraMap ℤ_[p] K)).roots.toFinset.filter
      (fun y => 1 < P.valuation K y)).image (fun y => y⁻¹) =
      (A.map (algebraMap ℤ_[p] K)).roots.toFinset := by
    ext z
    simp only [Finset.mem_image, Finset.mem_filter, Multiset.mem_toFinset]
    constructor
    · rintro ⟨y, ⟨hy, hy1⟩, rfl⟩
      rw [mem_roots', IsRoot.def] at hy ⊢
      exact ⟨(hAm.map _).ne_zero, root_inv_of_one_lt P hf hrev hBu hy.2 hy1⟩
    · intro hz
      rw [mem_roots', IsRoot.def] at hz
      obtain ⟨-, hzr, hz1⟩ := inv_root_of_eisenstein_root P hrev hAm hAdeg hAE hz.2
      refine ⟨z⁻¹, ⟨?_, hz1⟩, inv_inv z⟩
      rw [mem_roots', IsRoot.def]
      exact ⟨hf0, hzr⟩
  have hScard : ((f.map (algebraMap ℤ_[p] K)).roots.toFinset.filter
      (fun y => 1 < P.valuation K y)).card = d := by
    rw [← Finset.card_image_of_injective _ inv_injective, hSimg,
      Multiset.toFinset_card_of_nodup hnodup, hcardA, hAdeg]
  -- transitivity: every root with `1 < v` is `τ^k y₀`
  have horb : ∀ y, (f.map (algebraMap ℤ_[p] K)).eval y = 0 → 1 < P.valuation K y →
      ∃ k : ℤ, ((g : Gal(K/ℚ_[p])) ^ k) y₀ = y := by
    intro y hy hy1
    obtain ⟨σ, hσ, hσz⟩ := exists_mem_inertia_apply_eq P hAm hd0 hAE hA₀
      (root_inv_of_one_lt P hf hrev hBu hy hy1)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨σ, hσ⟩)
    refine ⟨k, ?_⟩
    have hk' : (g : Gal(K/ℚ_[p])) ^ k = σ := by
      have := congrArg Subtype.val hk
      simpa using this
    rw [hk']
    rw [map_inv₀] at hσz
    exact inv_injective (by simpa using hσz)
  refine ⟨g, g.2, ?_, y₀, hy₀r, hy₀1, horb, hScard⟩
  intro y hy
  constructor
  · intro hne
    by_contra hle
    exact hne (apply_eq_of_mem_inertia P hf g.2 hy (not_lt.mp hle))
  · intro hy1 hfix
    -- `τ` fixes a root of the orbit, hence `y₀`, hence the whole orbit, which has `d ≥ 2` points
    obtain ⟨j, hj⟩ := horb y hy hy1
    have hτy₀ : (g : Gal(K/ℚ_[p])) y₀ = y₀ := by
      have h1 : (g : Gal(K/ℚ_[p])) (((g : Gal(K/ℚ_[p])) ^ j) y₀) =
          ((g : Gal(K/ℚ_[p])) ^ j) y₀ := by rw [hj]; exact hfix
      have h2 : ((g : Gal(K/ℚ_[p])) ^ j) ((g : Gal(K/ℚ_[p])) y₀) =
          ((g : Gal(K/ℚ_[p])) ^ j) y₀ := by
        rw [← h1]
        change (((g : Gal(K/ℚ_[p])) ^ j * (g : Gal(K/ℚ_[p]))) y₀) =
          (((g : Gal(K/ℚ_[p])) * (g : Gal(K/ℚ_[p])) ^ j) y₀)
        rw [(Commute.self_zpow _ j).eq]
      exact ((g : Gal(K/ℚ_[p])) ^ j).injective h2
    have hall : ∀ k : ℤ, ((g : Gal(K/ℚ_[p])) ^ k) y₀ = y₀ := by
      intro k
      have hmem : (g : Gal(K/ℚ_[p])) ∈ MulAction.stabilizer Gal(K/ℚ_[p]) y₀ :=
        MulAction.mem_stabilizer_iff.mpr hτy₀
      exact MulAction.mem_stabilizer_iff.mp (zpow_mem hmem k)
    have h2 : 1 < ((f.map (algebraMap ℤ_[p] K)).roots.toFinset.filter
        (fun y => 1 < P.valuation K y)).card := by rw [hScard]; omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2
    rw [Finset.mem_filter, Multiset.mem_toFinset, mem_roots', IsRoot.def] at ha hb
    obtain ⟨ka, hka⟩ := horb a ha.1.2 ha.2
    obtain ⟨kb, hkb⟩ := horb b hb.1.2 hb.2
    rw [hall] at hka hkb
    exact hab (hka.symm.trans hkb)

end Main

end SourceInertia

end ArithmeticOfJacobiPolynomials
