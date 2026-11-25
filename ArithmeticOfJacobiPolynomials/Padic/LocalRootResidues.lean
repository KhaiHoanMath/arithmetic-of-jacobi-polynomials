/- Assembled by AxiomProver. -/
module

public import ArithmeticOfJacobiPolynomials.Galois.RootResidues
public import Mathlib

/-!
# Valuations of the roots of a `p`-adic polynomial with a `d`-fold drop of degree mod `p`

This is the `ℤ_[p]`-coefficient version of `ArithmeticOfJacobiPolynomials.RootResidues`, used for
the local
form of Lemma 5.1.

Let `f = Σ aⱼ Xʲ ∈ ℤ_[p][X]` have degree `N`, with `a₀` a unit, `v_p(a_N) = 1`, and reduction
`f̄ ∈ 𝔽_p[X]` squarefree of degree `N - d`, `1 ≤ d < p` (`LocalHyp p d f`). Let `φ : ℤ_[p] → K`
be a ring map into a field of characteristic zero and `v` a valuation on `K` which restricts
along `φ` to (a power of) the `p`-adic valuation, in the sense that `v (φ a) < 1 ↔ p ∣ a`
(`IsPadicAt v φ`). For the roots `y ∈ K` of `f^φ` we prove:

* every root has `1 ≤ v y` (`one_le_valuation_of_root`);
* two distinct roots with `v y ≤ 1` have `v (y' - y) = 1` (`not_valuation_sub_lt_one`);
* a root with `1 < v y` satisfies `v (y⁻¹) ^ d = v p` (`valuation_inv_pow_eq`);
* two distinct roots with `1 < v y` satisfy `v (y⁻¹) ≤ v (y⁻¹ - y'⁻¹)`
  (`valuation_inv_le_valuation_inv_sub`);
* if `f` splits in `K`, exactly `d` roots (with multiplicity) have `1 < v y`
  (`card_filter_roots_one_lt`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

namespace LocalRootResidues

variable {p : ℕ} [hp : Fact p.Prime]

/-- `p ∣ a` in `ℤ_[p]` iff `a` reduces to zero modulo `p`. -/
theorem dvd_iff_toZMod_eq_zero (a : ℤ_[p]) : (p : ℤ_[p]) ∣ a ↔ PadicInt.toZMod a = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

theorem isUnit_of_not_dvd {a : ℤ_[p]} (h : ¬ (p : ℤ_[p]) ∣ a) : IsUnit a := by
  rw [PadicInt.isUnit_iff]
  exact le_antisymm (PadicInt.norm_le_one a)
    (not_lt.mp fun h' => h ((PadicInt.norm_lt_one_iff_dvd a).mp h'))

theorem not_dvd_of_isUnit {a : ℤ_[p]} (h : IsUnit a) : ¬ (p : ℤ_[p]) ∣ a :=
  fun hd => PadicInt.prime_p.not_isUnit (isUnit_of_dvd_unit hd h)

theorem toZMod_surjective : Function.Surjective (PadicInt.toZMod : ℤ_[p] →+* ZMod p) :=
  ZMod.ringHom_surjective _

theorem natCast_dvd_iff (n : ℤ) : (p : ℤ_[p]) ∣ (n : ℤ_[p]) ↔ (p : ℤ) ∣ n := by
  rw [dvd_iff_toZMod_eq_zero, map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The hypotheses of the first part of Lemma 5.1 for
`f = Σ aⱼ Xʲ ∈ ℤ_[p][X]`: `a₀` is a unit, `v_p(a_N) = 1`, and the reduction `f̄` modulo `p`
is squarefree of degree `N - d`, where `1 ≤ d < p`. -/
structure LocalHyp (p d : ℕ) [Fact p.Prime] (f : ℤ_[p][X]) : Prop where
  isUnit_coeff_zero : IsUnit (f.coeff 0)
  valuation_leadingCoeff : f.leadingCoeff.valuation = 1
  natDegree_eq : (f.map PadicInt.toZMod).natDegree + d = f.natDegree
  squarefree : Squarefree (f.map PadicInt.toZMod)
  pos : 1 ≤ d
  lt : d < p

namespace LocalHyp

variable {d : ℕ} {f : ℤ_[p][X]} (hf : LocalHyp p d f)
include hf

theorem le_natDegree : d ≤ f.natDegree := by
  have := hf.natDegree_eq; omega

theorem dvd_coeff_of_lt {j : ℕ} (hj : f.natDegree - d < j) : (p : ℤ_[p]) ∣ f.coeff j := by
  rw [dvd_iff_toZMod_eq_zero]
  have h := hf.natDegree_eq
  have : (f.map PadicInt.toZMod).coeff j = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  simpa [coeff_map] using this

theorem not_dvd_coeff_sub : ¬ (p : ℤ_[p]) ∣ f.coeff (f.natDegree - d) := by
  rw [dvd_iff_toZMod_eq_zero]
  have h := hf.natDegree_eq
  have hne : (f.map PadicInt.toZMod).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr hf.squarefree.ne_zero
  have : f.natDegree - d = (f.map PadicInt.toZMod).natDegree := by omega
  rw [leadingCoeff, coeff_map] at hne
  rw [this]
  exact hne

theorem lead_eq : ∃ u : ℤ_[p], f.coeff f.natDegree = p * u ∧ IsUnit u := by
  have h1 := hf.valuation_leadingCoeff
  have h0 : f.leadingCoeff ≠ 0 := by
    intro h; rw [h, PadicInt.valuation_zero] at h1; exact zero_ne_one h1
  refine ⟨(PadicInt.unitCoeff h0 : ℤ_[p]), ?_, Units.isUnit _⟩
  have := PadicInt.unitCoeff_spec h0
  rw [h1, pow_one, mul_comm] at this
  exact this

theorem not_dvd_coeff_zero : ¬ (p : ℤ_[p]) ∣ f.coeff 0 :=
  not_dvd_of_isUnit hf.isUnit_coeff_zero

end LocalHyp

section Valuation

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- The valuation `v` on `K` restricts along `φ : ℤ_[p] → K` to a valuation whose
maximal ideal is `p ℤ_[p]` (so it is a power of the `p`-adic valuation). -/
@[expose] def IsPadicAt (v : Valuation K Γ₀) (φ : ℤ_[p] →+* K) : Prop :=
  ∀ a : ℤ_[p], v (φ a) < 1 ↔ (p : ℤ_[p]) ∣ a

variable {v : Valuation K Γ₀} {φ : ℤ_[p] →+* K}

theorem IsPadicAt.eq_one_of_isUnit (hv : IsPadicAt v φ) {a : ℤ_[p]} (ha : IsUnit a) :
    v (φ a) = 1 := by
  obtain ⟨u, rfl⟩ := ha
  have h1 : 1 ≤ v (φ u) := not_lt.mp fun h => not_dvd_of_isUnit u.isUnit ((hv _).mp h)
  have h2 : 1 ≤ v (φ (u⁻¹ : ℤ_[p]ˣ)) :=
    not_lt.mp fun h => not_dvd_of_isUnit (u⁻¹).isUnit ((hv _).mp h)
  have h3 : v (φ u) * v (φ (u⁻¹ : ℤ_[p]ˣ)) = 1 := by
    rw [← v.map_mul, ← map_mul, Units.mul_inv, map_one, v.map_one]
  refine le_antisymm ?_ h1
  calc v (φ u) = v (φ u) * 1 := (mul_one _).symm
    _ ≤ v (φ u) * v (φ (u⁻¹ : ℤ_[p]ˣ)) := by gcongr
    _ = 1 := h3

theorem IsPadicAt.eq_one (hv : IsPadicAt v φ) {a : ℤ_[p]} (ha : ¬ (p : ℤ_[p]) ∣ a) :
    v (φ a) = 1 :=
  hv.eq_one_of_isUnit (isUnit_of_not_dvd ha)

theorem IsPadicAt.le_one (hv : IsPadicAt v φ) (a : ℤ_[p]) : v (φ a) ≤ 1 := by
  by_cases h : (p : ℤ_[p]) ∣ a
  · exact ((hv a).mpr h).le
  · exact (hv.eq_one h).le

theorem IsPadicAt.valuation_le_of_dvd (hv : IsPadicAt v φ) {a : ℤ_[p]}
    (ha : (p : ℤ_[p]) ∣ a) : v (φ a) ≤ v (p : K) := by
  obtain ⟨k, rfl⟩ := ha
  rw [map_mul, v.map_mul, map_natCast]
  calc v (p : K) * v (φ k) ≤ v (p : K) * 1 := by gcongr; exact hv.le_one k
    _ = _ := mul_one _

/-- `IsPadicAt` restricts to `IsAdicAt` on `ℤ`. -/
theorem IsPadicAt.isAdicAt (hv : IsPadicAt v φ) : RootResidues.IsAdicAt v p := by
  unfold RootResidues.IsAdicAt
  intro n
  have := hv (n : ℤ_[p])
  rwa [map_intCast, natCast_dvd_iff] at this

theorem IsPadicAt.lt_one (hv : IsPadicAt v φ) : v (p : K) < 1 :=
  hv.isAdicAt.lt_one

variable (φ) in
/-- A `ℤ_[p]`-polynomial evaluated at a point of valuation `≤ 1`. -/
theorem valuation_eval_le_one (hv : IsPadicAt v φ) (g : ℤ_[p][X]) {y : K} (hy : v y ≤ 1) :
    v ((g.map φ).eval y) ≤ 1 := by
  rw [eval_eq_sum_range]
  refine v.map_sum_le fun i _ => ?_
  rw [v.map_mul, v.map_pow, coeff_map]
  calc v (φ (g.coeff i)) * v y ^ i ≤ 1 * 1 := mul_le_mul' (hv.le_one _) (pow_le_one₀ zero_le hy)
    _ = 1 := one_mul 1

/-- A `ℤ_[p]`-polynomial with all coefficients divisible by `p`, evaluated at a point of
valuation `≤ 1`. -/
theorem valuation_eval_lt_one_of_dvd (hv : IsPadicAt v φ) {g : ℤ_[p][X]}
    (hg : ∀ n, (p : ℤ_[p]) ∣ g.coeff n) {y : K} (hy : v y ≤ 1) : v ((g.map φ).eval y) < 1 := by
  rw [eval_eq_sum_range]
  refine v.map_sum_lt one_ne_zero fun i _ => ?_
  rw [v.map_mul, v.map_pow, coeff_map]
  calc v (φ (g.coeff i)) * v y ^ i ≤ v (φ (g.coeff i)) * 1 :=
        mul_le_mul' le_rfl (pow_le_one₀ zero_le hy)
    _ < 1 := by rw [mul_one]; exact (hv _).mpr (hg i)

theorem eval_map_eq_sum_of_natDegree (f : ℤ_[p][X]) (hdeg : (f.map φ).natDegree = f.natDegree)
    (y : K) :
    (f.map φ).eval y = ∑ j ∈ range (f.natDegree + 1), φ (f.coeff j) * y ^ j := by
  rw [eval_eq_sum_range, hdeg]
  simp [coeff_map]

variable {d : ℕ} {f : ℤ_[p][X]}

variable [CharZero K]

theorem valuation_natCast_prime_ne_zero (w : Valuation K Γ₀) : w (p : K) ≠ 0 := by
  rw [Ne, Valuation.zero_iff]; exact_mod_cast hp.out.ne_zero

variable (hf : LocalHyp p d f) (hv : IsPadicAt v φ)
include hf hv

omit [CharZero K] in
theorem valuation_lead : v (φ (f.coeff f.natDegree)) = v (p : K) := by
  obtain ⟨u, hu, hpu⟩ := hf.lead_eq
  rw [hu, map_mul, v.map_mul, hv.eq_one_of_isUnit hpu, mul_one, map_natCast]

omit [CharZero K] in
theorem valuation_coeff_sub : v (φ (f.coeff (f.natDegree - d))) = 1 :=
  hv.eq_one hf.not_dvd_coeff_sub

omit [CharZero K] in
theorem valuation_coeff_zero : v (φ (f.coeff 0)) = 1 :=
  hv.eq_one_of_isUnit hf.isUnit_coeff_zero

theorem natDegree_map_eq : (f.map φ).natDegree = f.natDegree := by
  apply natDegree_map_of_leadingCoeff_ne_zero
  intro h
  have := valuation_lead hf hv
  change v (φ f.leadingCoeff) = _ at this
  rw [h, v.map_zero] at this
  exact valuation_natCast_prime_ne_zero (p := p) v this.symm

theorem eval_map_eq_sum (y : K) :
    (f.map φ).eval y = ∑ j ∈ range (f.natDegree + 1), φ (f.coeff j) * y ^ j :=
  eval_map_eq_sum_of_natDegree f (natDegree_map_eq hf hv) y

theorem sum_inv_root {y : K} (hy : (f.map φ).eval y = 0) (hy0 : y ≠ 0) :
    ∑ j ∈ range (f.natDegree + 1), φ (f.coeff j) * y⁻¹ ^ (f.natDegree - j) = 0 := by
  have h := congrArg (· * y⁻¹ ^ f.natDegree) hy
  simp only [eval_map_eq_sum hf hv, Finset.sum_mul, zero_mul] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj : j ≤ f.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [← pow_mul_pow_sub y⁻¹ hj, mul_assoc, ← mul_assoc (y ^ j), ← mul_pow,
    mul_inv_cancel₀ hy0, one_pow, one_mul]

theorem one_le_valuation_of_root {y : K} (hy : (f.map φ).eval y = 0) : 1 ≤ v y := by
  by_contra h
  rw [not_le] at h
  rw [eval_map_eq_sum hf hv] at hy
  have h0 := valuation_coeff_zero hf hv
  have key := RootResidues.valuation_sum_eq_of_dominant v (range (f.natDegree + 1))
    (fun j => φ (f.coeff j) * y ^ j) (j₀ := 0) (by simp) (by simp [h0])
    (by
      intro j _ hj
      simp only [pow_zero, mul_one, h0, v.map_mul, v.map_pow]
      calc v (φ (f.coeff j)) * v y ^ j ≤ 1 * v y ^ j := by
            gcongr; exact hv.le_one _
        _ < 1 := by rw [one_mul]; exact pow_lt_one₀ zero_le h hj)
  rw [hy] at key
  simp [h0] at key

theorem ne_zero_of_root {y : K} (hy : (f.map φ).eval y = 0) : y ≠ 0 := by
  intro h
  have := one_le_valuation_of_root hf hv hy
  simp [h] at this

/-- A root `y` with `1 < v y` has `v (y⁻¹) ^ d = v p`. -/
theorem valuation_inv_pow_eq {y : K} (hy : (f.map φ).eval y = 0) (h1 : 1 < v y) :
    v y⁻¹ ^ d = v (p : K) := by
  have hy0 : y ≠ 0 := ne_zero_of_root hf hv hy
  have hS := sum_inv_root hf hv hy hy0
  have hlead := valuation_lead hf hv
  have hmid := valuation_coeff_sub hf hv
  set z := y⁻¹ with hz_def
  have hz0 : z ≠ 0 := inv_ne_zero hy0
  have hvz0 : 0 < v z := by rw [zero_lt_iff, Ne, Valuation.zero_iff]; exact hz0
  have hz : v z < 1 := by
    rw [hz_def, map_inv₀, inv_lt_one₀ (lt_trans zero_lt_one h1)]; exact h1
  have hvp0 := valuation_natCast_prime_ne_zero (p := p) v
  have hvp0' : 0 < v (p : K) := zero_lt_iff.mpr hvp0
  have hdN := hf.le_natDegree
  set N := f.natDegree with hN
  have hterm : ∀ j, v (φ (f.coeff j) * z ^ (N - j)) = v (φ (f.coeff j)) * v z ^ (N - j) := by
    intro j; rw [v.map_mul, v.map_pow]
  rcases lt_trichotomy (v z ^ d) (v (p : K)) with hlt | heq | hgt
  · exfalso
    have key := RootResidues.valuation_sum_eq_of_dominant v (range (N + 1))
      (fun j => φ (f.coeff j) * z ^ (N - j)) (j₀ := N) (by simp)
      (by simp only [Nat.sub_self, pow_zero, mul_one, hlead]; exact hvp0)
      (by
        intro j hj hjN
        have hjN' : j < N := by
          have := Finset.mem_range.mp hj; omega
        simp only [Nat.sub_self, pow_zero, mul_one, hlead, hterm]
        by_cases hjd : N - d < j
        · calc v (φ (f.coeff j)) * v z ^ (N - j) ≤ v (p : K) * v z ^ (N - j) :=
                mul_le_mul_left (hv.valuation_le_of_dvd (hf.dvd_coeff_of_lt hjd)) _
            _ < v (p : K) := mul_lt_of_lt_one_right hvp0' (pow_lt_one₀ zero_le hz (by omega))
        · calc v (φ (f.coeff j)) * v z ^ (N - j) ≤ 1 * v z ^ (N - j) :=
                mul_le_mul_left (hv.le_one _) _
            _ ≤ v z ^ d := by rw [one_mul]; exact pow_le_pow_of_le_one zero_le hz.le (by omega)
            _ < v (p : K) := hlt)
    rw [hS, v.map_zero] at key
    simp only [Nat.sub_self, pow_zero, mul_one, hlead] at key
    exact hvp0 key.symm
  · exact heq
  · exfalso
    have key := RootResidues.valuation_sum_eq_of_dominant v (range (N + 1))
      (fun j => φ (f.coeff j) * z ^ (N - j)) (j₀ := N - d) (Finset.mem_range.mpr (by omega))
      (by
        simp only [hterm]
        rw [hmid, one_mul, Nat.sub_sub_self hdN]
        exact pow_ne_zero _ hvz0.ne')
      (by
        intro j hj hjd
        have hjN : j ≤ N := by have := Finset.mem_range.mp hj; omega
        simp only [hterm]
        rw [hmid, one_mul, Nat.sub_sub_self hdN]
        by_cases hjd' : N - d < j
        · calc v (φ (f.coeff j)) * v z ^ (N - j) ≤ v (p : K) * 1 :=
                mul_le_mul' (hv.valuation_le_of_dvd (hf.dvd_coeff_of_lt hjd'))
                  (pow_le_one₀ zero_le hz.le)
            _ < v z ^ d := by rw [mul_one]; exact hgt
        · calc v (φ (f.coeff j)) * v z ^ (N - j) ≤ 1 * v z ^ (N - j) :=
                mul_le_mul_left (hv.le_one _) _
            _ < v z ^ d := by
                rw [one_mul]; exact pow_lt_pow_right_of_lt_one₀ hvz0 hz (by omega))
    rw [hS, v.map_zero] at key
    simp only [hterm] at key
    rw [hmid, one_mul, Nat.sub_sub_self hdN] at key
    exact pow_ne_zero _ hvz0.ne' key.symm

theorem valuation_inv_eq {y y' : K} (hy : (f.map φ).eval y = 0) (h1 : 1 < v y)
    (hy' : (f.map φ).eval y' = 0) (h1' : 1 < v y') : v y⁻¹ = v y'⁻¹ := by
  have e := valuation_inv_pow_eq hf hv hy h1
  have e' := valuation_inv_pow_eq hf hv hy' h1'
  have hd : d ≠ 0 := by have := hf.pos; omega
  rcases lt_trichotomy (v y⁻¹) (v y'⁻¹) with h | h | h
  · have := pow_lt_pow_left₀ h zero_le hd; rw [e, e'] at this; exact absurd this (lt_irrefl _)
  · exact h
  · have := pow_lt_pow_left₀ h zero_le hd; rw [e, e'] at this; exact absurd this (lt_irrefl _)

/-- Two distinct roots `y, y'` with `1 < v y` have inverses that are not
congruent modulo a higher power of the prime than `y⁻¹` itself:
`v (y⁻¹) ≤ v (y⁻¹ - y'⁻¹)`. -/
theorem valuation_inv_le_valuation_inv_sub {y y' : K} (hy : (f.map φ).eval y = 0)
    (h1 : 1 < v y) (hy' : (f.map φ).eval y' = 0) (hne : y ≠ y') :
    v y⁻¹ ≤ v (y⁻¹ - y'⁻¹) := by
  have hy0 : y ≠ 0 := ne_zero_of_root hf hv hy
  have hy0' : y' ≠ 0 := ne_zero_of_root hf hv hy'
  have hS := sum_inv_root hf hv hy hy0
  have hS' := sum_inv_root hf hv hy' hy0'
  have hpow := valuation_inv_pow_eq hf hv hy h1
  set z := y⁻¹ with hz_def
  set z' := y'⁻¹ with hz'_def
  have hz0 : z ≠ 0 := inv_ne_zero hy0
  have hvz0 : 0 < v z := by rw [zero_lt_iff, Ne, Valuation.zero_iff]; exact hz0
  have hz : v z < 1 := by
    rw [hz_def, map_inv₀, inv_lt_one₀ (lt_trans zero_lt_one h1)]; exact h1
  have hzne : z ≠ z' := fun h => hne (inv_injective h)
  have hvp0 := valuation_natCast_prime_ne_zero (p := p) v
  have hvp0' : 0 < v (p : K) := zero_lt_iff.mpr hvp0
  have hdN := hf.le_natDegree
  set N := f.natDegree with hN
  have hmid := valuation_coeff_sub hf hv
  by_contra hlt
  rw [not_le] at hlt
  set δ := z' / z - 1 with hδ_def
  have hz' : z' = z * (1 + δ) := by rw [hδ_def]; field_simp; ring
  have hδ0 : δ ≠ 0 := by
    intro h; rw [h, add_zero, mul_one] at hz'; exact hzne hz'.symm
  have hvδ : v δ < 1 := by
    have : δ = (z' - z) / z := by rw [hδ_def]; field_simp
    rw [this, map_div₀, Valuation.map_sub_swap]
    exact (div_lt_one₀ hvz0).mpr hlt
  -- the Taylor expansion of `Σ a_j Y^(N-j)` at `z` in the direction `z δ`
  have hb : ∀ j ∈ range (N + 1), v (φ (f.coeff j) * z ^ (N - j)) ≤ v (p : K) := by
    intro j hj
    have hjN : j ≤ N := by have := Finset.mem_range.mp hj; omega
    rw [v.map_mul, v.map_pow]
    by_cases hjd : N - d < j
    · calc v (φ (f.coeff j)) * v z ^ (N - j) ≤ v (p : K) * 1 :=
            mul_le_mul' (hv.valuation_le_of_dvd (hf.dvd_coeff_of_lt hjd))
              (pow_le_one₀ zero_le hz.le)
        _ = v (p : K) := mul_one _
    · calc v (φ (f.coeff j)) * v z ^ (N - j) ≤ 1 * v z ^ d :=
            mul_le_mul' (hv.le_one _)
              (pow_le_pow_of_le_one zero_le hz.le (by omega))
        _ = v (p : K) := by rw [one_mul, hpow]
  have htay := RootResidues.valuation_sum_taylor_le v (range (N + 1))
    (fun j => φ (f.coeff j) * z ^ (N - j))
    (fun j => N - j) hb (x := 1) (δ := δ) (by simp) hvδ.le
  set D := ∑ j ∈ range (N + 1), ((N - j : ℕ) : K) * (φ (f.coeff j) * z ^ (N - j)) with hD
  have hid : ∑ j ∈ range (N + 1), φ (f.coeff j) * z ^ (N - j) *
      ((1 + δ) ^ (N - j) - 1 ^ (N - j) - ((N - j : ℕ) : K) * 1 ^ (N - j - 1) * δ) =
      -(δ * D) := by
    have e1 : ∑ j ∈ range (N + 1), φ (f.coeff j) * z ^ (N - j) *
        ((1 + δ) ^ (N - j) - 1 ^ (N - j) - ((N - j : ℕ) : K) * 1 ^ (N - j - 1) * δ) =
        ∑ j ∈ range (N + 1), φ (f.coeff j) * z' ^ (N - j) -
        ∑ j ∈ range (N + 1), φ (f.coeff j) * z ^ (N - j) - δ * D := by
      rw [hD, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hz', mul_pow]; simp only [one_pow]; ring
    rw [e1, hS, hS']; ring
  rw [hid, Valuation.map_neg, v.map_mul] at htay
  have hd1 : v (d : K) = 1 := hv.isAdicAt.natCast_eq_one (by have := hf.pos; omega) hf.lt
  have hterm2 : ∀ j, v (((N - j : ℕ) : K) * (φ (f.coeff j) * z ^ (N - j))) =
      v ((N - j : ℕ) : K) * (v (φ (f.coeff j)) * v z ^ (N - j)) := by
    intro j; rw [v.map_mul, v.map_mul, v.map_pow]
  have hvD : v D = v (p : K) := by
    rw [hD]
    have key := RootResidues.valuation_sum_eq_of_dominant v (range (N + 1))
      (fun j => ((N - j : ℕ) : K) * (φ (f.coeff j) * z ^ (N - j))) (j₀ := N - d)
      (Finset.mem_range.mpr (by omega))
      (by
        simp only [hterm2]
        rw [Nat.sub_sub_self hdN, hd1, hmid, one_mul, one_mul, hpow]
        exact hvp0)
      (by
        intro j hj hjd
        have hjN : j ≤ N := by have := Finset.mem_range.mp hj; omega
        simp only [hterm2]
        rw [Nat.sub_sub_self hdN, hd1, hmid, one_mul, one_mul, hpow]
        by_cases hjN' : j = N
        · subst hjN'; simp [hvp0']
        by_cases hjd' : N - d < j
        · calc v ((N - j : ℕ) : K) * (v (φ (f.coeff j)) * v z ^ (N - j))
              ≤ 1 * (v (p : K) * v z ^ (N - j)) :=
                mul_le_mul' (RootResidues.valuation_natCast_le_one v _)
                  (mul_le_mul_left (hv.valuation_le_of_dvd (hf.dvd_coeff_of_lt hjd')) _)
            _ < v (p : K) := by
                rw [one_mul]
                exact mul_lt_of_lt_one_right hvp0' (pow_lt_one₀ zero_le hz (by omega))
        · calc v ((N - j : ℕ) : K) * (v (φ (f.coeff j)) * v z ^ (N - j))
              ≤ 1 * (1 * v z ^ (N - j)) :=
                mul_le_mul' (RootResidues.valuation_natCast_le_one v _)
                  (mul_le_mul_left (hv.le_one _) _)
            _ < v z ^ d := by
                rw [one_mul, one_mul]
                exact pow_lt_pow_right_of_lt_one₀ hvz0 hz (by omega)
            _ = v (p : K) := hpow)
    rw [key]
    simp only [hterm2]
    rw [Nat.sub_sub_self hdN, hd1, hmid, one_mul, one_mul, hpow]
  rw [hvD] at htay
  have hvδ0 : 0 < v δ := by rw [zero_lt_iff, Ne, Valuation.zero_iff]; exact hδ0
  have h2 : (v (p : K) * v δ) * 1 ≤ (v (p : K) * v δ) * v δ := by
    calc (v (p : K) * v δ) * 1 = v δ * v (p : K) := by rw [mul_one, mul_comm]
      _ ≤ v (p : K) * v δ ^ 2 := htay
      _ = (v (p : K) * v δ) * v δ := by rw [pow_two, mul_assoc]
  exact absurd hvδ (not_lt.mpr (le_of_mul_le_mul_left h2 (mul_pos hvp0' hvδ0)))

omit [CharZero K] in
/-- At a root `y` of `f` with `v y ≤ 1`, the derivative is a unit: `v (f'(y)) = 1`
(since `f̄` is separable). -/
theorem valuation_derivative_eq_one {y : K} (hy : (f.map φ).eval y = 0) (hy1 : v y ≤ 1) :
    v ((f.map φ).derivative.eval y) = 1 := by
  have hsep : (f.map PadicInt.toZMod).Separable :=
    PerfectField.separable_iff_squarefree.mpr hf.squarefree
  obtain ⟨a, b, hab⟩ := hsep
  obtain ⟨U, rfl⟩ := Polynomial.map_surjective PadicInt.toZMod toZMod_surjective a
  obtain ⟨V, rfl⟩ := Polynomial.map_surjective PadicInt.toZMod toZMod_surjective b
  set E := U * f + V * derivative f - 1 with hE
  have hEmap : E.map PadicInt.toZMod = 0 := by
    rw [hE, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
      Polynomial.map_one, ← derivative_map, hab, sub_self]
  have hEdvd : ∀ n, (p : ℤ_[p]) ∣ E.coeff n := by
    intro n
    rw [dvd_iff_toZMod_eq_zero]
    have := congrArg (fun q => q.coeff n) hEmap
    simpa [coeff_map] using this
  have hlt := valuation_eval_lt_one_of_dvd hv hEdvd hy1
  have hEval : (E.map φ).eval y = (V.map φ).eval y * (f.map φ).derivative.eval y - 1 := by
    rw [hE, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
      Polynomial.map_one, ← derivative_map]
    simp only [eval_sub, eval_add, eval_mul, eval_one]
    rw [hy]
    ring
  rw [hEval] at hlt
  have hge : 1 ≤ v ((V.map φ).eval y * (f.map φ).derivative.eval y) := by
    by_contra h
    rw [not_le] at h
    have h' : v ((V.map φ).eval y * (f.map φ).derivative.eval y) < v 1 := by rwa [v.map_one]
    rw [v.map_sub_eq_of_lt_right h', v.map_one] at hlt
    exact lt_irrefl _ hlt
  have hder : v ((f.map φ).derivative.eval y) ≤ 1 := by
    rw [derivative_map]; exact valuation_eval_le_one φ hv _ hy1
  refine le_antisymm hder (not_lt.mp fun h => ?_)
  rw [v.map_mul] at hge
  have := mul_le_mul' (valuation_eval_le_one φ hv V hy1)
    (le_refl (v ((f.map φ).derivative.eval y)))
  rw [one_mul] at this
  exact absurd (hge.trans this) (not_le.mpr h)

omit [CharZero K] in
/-- Two distinct roots `y, y'` of `f` with `v y ≤ 1` are not congruent modulo the prime:
`v (y' - y) = 1`. -/
theorem not_valuation_sub_lt_one {y y' : K} (hy : (f.map φ).eval y = 0) (hy1 : v y ≤ 1)
    (hy' : (f.map φ).eval y' = 0) (hne : y ≠ y') : ¬ v (y' - y) < 1 := by
  intro hlt
  obtain ⟨δ, rfl⟩ : ∃ δ, y' = y + δ := ⟨y' - y, by ring⟩
  rw [add_sub_cancel_left] at hlt
  have hδ0 : δ ≠ 0 := by rintro rfl; exact hne (add_zero y).symm
  have hder := valuation_derivative_eq_one hf hv hy hy1
  set F := f.map φ with hF
  have htay := RootResidues.valuation_sum_taylor_le v F.support (fun n => F.coeff n) (fun n => n)
    (M := 1)
    (fun n _ => by rw [hF, coeff_map]; exact hv.le_one _) hy1 hlt.le
  have hid : ∑ n ∈ F.support, F.coeff n * ((y + δ) ^ n - y ^ n - (n : K) * y ^ (n - 1) * δ) =
      F.eval (y + δ) - F.eval y - F.derivative.eval y * δ := by
    rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum, derivative_eval, Polynomial.sum_def,
      Polynomial.sum_def, Polynomial.sum_def, Finset.sum_mul, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hid, hy, hy', sub_self, zero_sub, Valuation.map_neg, v.map_mul, hder, one_mul,
    one_mul] at htay
  have hvδ0 : 0 < v δ := by rw [zero_lt_iff, Ne, Valuation.zero_iff]; exact hδ0
  have h2 : v δ * 1 ≤ v δ * v δ := by rwa [mul_one, ← pow_two]
  exact absurd hlt (not_lt.mpr (le_of_mul_le_mul_left h2 hvδ0))

/-- If `f` splits in `K`, exactly `d` of its roots, counted with multiplicity, satisfy
`1 < v y`. -/
theorem card_filter_roots_one_lt (hsplit : Multiset.card (f.map φ).roots = f.natDegree) :
    Multiset.card ((f.map φ).roots.filter (fun y => 1 < v y)) = d := by
  classical
  have hlead := valuation_lead hf hv
  set F := f.map φ with hF
  have hroots : Multiset.card F.roots = F.natDegree := by
    rw [hF, natDegree_map_eq hf hv]; exact hsplit
  have hprod := C_leadingCoeff_mul_prod_multiset_X_sub_C hroots
  have h0 := congrArg (eval 0) hprod
  rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map] at h0
  have hF0 : F.eval 0 = φ (f.coeff 0) := by
    rw [← coeff_zero_eq_eval_zero, hF, coeff_map]
  have hlc : F.leadingCoeff = φ (f.coeff f.natDegree) := by
    rw [leadingCoeff, hF, natDegree_map_eq hf hv, coeff_map]
  have hv0 := congrArg v h0
  rw [v.map_mul, map_multiset_prod, Multiset.map_map, hF0, hlc, hlead,
    valuation_coeff_zero hf hv] at hv0
  have hmap : F.roots.map (v ∘ eval 0 ∘ fun a => X - C a) = F.roots.map v :=
    Multiset.map_congr rfl (fun r _ => by simp)
  rw [hmap, ← Multiset.filter_add_not (fun y => 1 < v y) F.roots, Multiset.map_add,
    Multiset.prod_add] at hv0
  have hQ2 : ((F.roots.filter (fun y => ¬ 1 < v y)).map v).prod = 1 := by
    apply Multiset.prod_eq_one
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
    obtain ⟨hr1, hr2⟩ := Multiset.mem_filter.mp hr
    have hroot : F.eval r = 0 := (mem_roots'.mp hr1).2
    exact le_antisymm (not_lt.mp hr2) (one_le_valuation_of_root hf hv hroot)
  rw [hQ2, mul_one] at hv0
  set Mlt := F.roots.filter (fun y => 1 < v y) with hMlt
  have hQd : ((Mlt.map v).prod) ^ d = (v (p : K))⁻¹ ^ Multiset.card Mlt := by
    rw [← Multiset.prod_map_pow,
      Multiset.map_congr rfl (g := fun _ => (v (p : K))⁻¹) ?_, Multiset.map_const',
      Multiset.prod_replicate]
    intro r hr
    obtain ⟨hr1, hr2⟩ := Multiset.mem_filter.mp hr
    have hroot : F.eval r = 0 := (mem_roots'.mp hr1).2
    have := valuation_inv_pow_eq hf hv hroot hr2
    rw [map_inv₀, inv_pow] at this
    rw [← this, inv_inv]
  have hQ : (Mlt.map v).prod = (v (p : K))⁻¹ := (inv_eq_of_mul_eq_one_right hv0).symm
  rw [hQ] at hQd
  have hvp0 := valuation_natCast_prime_ne_zero (p := p) v
  have hinv1 : (v (p : K))⁻¹ ≠ 1 := by
    intro h; rw [inv_eq_one] at h; exact (ne_of_lt hv.lt_one) h
  exact (pow_right_injective₀ (inv_pos.mpr (zero_lt_iff.mpr hvp0)) hinv1 hQd).symm

end Valuation

end LocalRootResidues

end ArithmeticOfJacobiPolynomials
