/- Assembled by AxiomProver. -/
module

public import Mathlib

/-!
# Valuations of the roots of a polynomial with a `d`-fold drop of degree mod `p`

Let `f ∈ ℤ[X]` have degree `N`, with `p ∤ f(0)`, `p ∥ lc f`, and reduction `f̄` modulo `p`
squarefree of degree `N - d`, `1 ≤ d < p`. Let `v` be a valuation on a field `K` of
characteristic zero which restricts on `ℤ` to (a power of) the `p`-adic one, in the sense
that `v n < 1 ↔ p ∣ n`. This file proves the local facts about the roots `y ∈ K` of `f` that
the inertia argument of Lemma 5.1 uses:

* every root has `1 ≤ v y` (`one_le_valuation_of_root`);
* two distinct roots with `v y = v y' = 1` have `v (y' - y) = 1`
  (`not_valuation_sub_lt_one`);
* a root with `1 < v y` satisfies `v (y⁻¹) ^ d = v p` (`valuation_inv_pow_eq`);
* two distinct roots with `1 < v y`, `1 < v y'` satisfy `v (y⁻¹) ≤ v (y⁻¹ - y'⁻¹)`
  (`valuation_inv_le_valuation_inv_sub`);
* if `f` splits in `K`, exactly `d` roots (with multiplicity) have `1 < v y`
  (`card_filter_roots_one_lt`).
-/

public section

namespace ArithmeticOfJacobiPolynomials

open Polynomial Finset

namespace RootResidues

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation K Γ₀)

theorem valuation_intCast_le_one (n : ℤ) : v (n : K) ≤ 1 := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    have : (((n : ℤ) + 1 : ℤ) : K) = ((n : ℤ) : K) + 1 := by push_cast; ring
    rw [this]; exact v.map_add_le ih (by simp)
  | pred n ih =>
    have : ((-(n : ℤ) - 1 : ℤ) : K) = ((-(n : ℤ) : ℤ) : K) + (-1) := by push_cast; ring
    rw [this]; exact v.map_add_le ih (by simp)

theorem valuation_natCast_le_one (n : ℕ) : v (n : K) ≤ 1 := by
  simpa using valuation_intCast_le_one v n

/-- A sum with one strictly dominant term has the valuation of that term. -/
theorem valuation_sum_eq_of_dominant {ι : Type*} (s : Finset ι) (t : ι → K)
    {j₀ : ι} (hj₀ : j₀ ∈ s) (hne : v (t j₀) ≠ 0)
    (h : ∀ j ∈ s, j ≠ j₀ → v (t j) < v (t j₀)) : v (∑ j ∈ s, t j) = v (t j₀) := by
  classical
  rw [← Finset.add_sum_erase s t hj₀]
  apply Valuation.map_add_eq_of_lt_left
  exact v.map_sum_lt hne
    (fun j hj => h j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj))

/-- Second-order Taylor bound for a monomial at a point of valuation `≤ 1`. -/
theorem valuation_pow_taylor_le {x δ : K} (hx : v x ≤ 1) (hδ : v δ ≤ 1) (n : ℕ) :
    v ((x + δ) ^ n - x ^ n - n * x ^ (n - 1) * δ) ≤ v δ ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases n with _ | n
    · simp
    · have key : (x + δ) ^ (n + 1 + 1) - x ^ (n + 1 + 1) -
            ((n + 1 + 1 : ℕ) : K) * x ^ (n + 1 + 1 - 1) * δ
          = (x + δ) * ((x + δ) ^ (n + 1) - x ^ (n + 1) - ((n + 1 : ℕ) : K) * x ^ (n + 1 - 1) * δ)
            + ((n + 1 : ℕ) : K) * x ^ n * δ ^ 2 := by
        simp only [Nat.add_sub_cancel]; push_cast; ring
      rw [key]
      refine v.map_add_le ?_ ?_
      · rw [v.map_mul]
        calc v (x + δ) * _ ≤ 1 * v δ ^ 2 := mul_le_mul' (v.map_add_le hx hδ) ih
          _ = v δ ^ 2 := one_mul _
      · rw [v.map_mul, v.map_mul, v.map_pow, v.map_pow]
        calc v ((n + 1 : ℕ) : K) * v x ^ n * v δ ^ 2 ≤ 1 * 1 * v δ ^ 2 := by
              gcongr
              · exact valuation_natCast_le_one v _
              · exact pow_le_one₀ zero_le hx
          _ = v δ ^ 2 := by simp

/-- Second-order Taylor bound for a finite sum of monomials. -/
theorem valuation_sum_taylor_le {ι : Type*} (s : Finset ι) (b : ι → K) (m : ι → ℕ) {M : Γ₀}
    (hb : ∀ i ∈ s, v (b i) ≤ M) {x δ : K} (hx : v x ≤ 1) (hδ : v δ ≤ 1) :
    v (∑ i ∈ s, b i * ((x + δ) ^ m i - x ^ m i - (m i : K) * x ^ (m i - 1) * δ)) ≤
      M * v δ ^ 2 := by
  apply v.map_sum_le
  intro i hi
  rw [v.map_mul]
  exact mul_le_mul' (hb i hi) (valuation_pow_taylor_le v hx hδ _)

/-- The hypotheses on `f` in the first part of Lemma 5.1. -/
structure Hyp (p d : ℕ) (f : ℤ[X]) : Prop where
  prime : p.Prime
  coeff_zero : ¬ (p : ℤ) ∣ f.coeff 0
  dvd_lead : (p : ℤ) ∣ f.leadingCoeff
  not_sq_dvd_lead : ¬ (p : ℤ) ^ 2 ∣ f.leadingCoeff
  natDegree_eq : (f.map (Int.castRingHom (ZMod p))).natDegree + d = f.natDegree
  squarefree : Squarefree (f.map (Int.castRingHom (ZMod p)))
  pos : 1 ≤ d
  lt : d < p

namespace Hyp

variable {p d : ℕ} {f : ℤ[X]} (hf : Hyp p d f)
include hf

theorem le_natDegree : d ≤ f.natDegree := by
  have := hf.natDegree_eq; omega

theorem dvd_coeff_of_lt {j : ℕ} (hj : f.natDegree - d < j) : (p : ℤ) ∣ f.coeff j := by
  have : NeZero p := ⟨hf.prime.ne_zero⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h := hf.natDegree_eq
  have : (f.map (Int.castRingHom (ZMod p))).coeff j = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  simpa [coeff_map] using this

theorem not_dvd_coeff_sub : ¬ (p : ℤ) ∣ f.coeff (f.natDegree - d) := by
  have : Fact p.Prime := ⟨hf.prime⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h := hf.natDegree_eq
  have hne : (f.map (Int.castRingHom (ZMod p))).leadingCoeff ≠ 0 :=
    leadingCoeff_ne_zero.mpr hf.squarefree.ne_zero
  have : f.natDegree - d = (f.map (Int.castRingHom (ZMod p))).natDegree := by omega
  rw [leadingCoeff, coeff_map, eq_intCast] at hne
  rw [this]
  exact hne

theorem lead_eq : ∃ u : ℤ, f.coeff f.natDegree = p * u ∧ ¬ (p : ℤ) ∣ u := by
  obtain ⟨u, hu⟩ := hf.dvd_lead
  refine ⟨u, hu, fun ⟨w, hw⟩ => hf.not_sq_dvd_lead ⟨w, ?_⟩⟩
  rw [hu, hw]; ring

end Hyp

section Valuation

variable {p d : ℕ} {f : ℤ[X]}

/-- `v` restricts on `ℤ` to a valuation whose maximal ideal is `pℤ`. -/
@[expose] def IsAdicAt (v : Valuation K Γ₀) (p : ℕ) : Prop := ∀ n : ℤ, v (n : K) < 1 ↔ (p : ℤ) ∣ n

variable {v}

theorem IsAdicAt.eq_one {p : ℕ} (hv : IsAdicAt v p) {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) :
    v (n : K) = 1 :=
  le_antisymm (valuation_intCast_le_one v n) (not_lt.mp fun h => hn ((hv n).mp h))

theorem valuation_le_of_dvd {p : ℕ} {n : ℤ} (hn : (p : ℤ) ∣ n) :
    v (n : K) ≤ v (p : K) := by
  obtain ⟨k, rfl⟩ := hn
  push_cast
  rw [v.map_mul]
  calc v (p : K) * v (k : K) ≤ v (p : K) * 1 := by gcongr; exact valuation_intCast_le_one v k
    _ = _ := mul_one _

theorem IsAdicAt.lt_one {p : ℕ} (hv : IsAdicAt v p) : v (p : K) < 1 := by
  simpa using (hv p).mpr dvd_rfl

theorem IsAdicAt.natCast_eq_one {p : ℕ} (hv : IsAdicAt v p) {n : ℕ} (h0 : 0 < n) (hn : n < p) :
    v (n : K) = 1 := by
  have := hv.eq_one (n := n) (by
    intro h
    have := Int.le_of_dvd (by omega) h
    omega)
  simpa using this

variable [CharZero K]

theorem valuation_prime_ne_zero {p : ℕ} (hp : p.Prime) : v (p : K) ≠ 0 := by
  rw [Ne, Valuation.zero_iff]; exact_mod_cast hp.ne_zero

/-- `f` mapped to `K`. -/
noncomputable abbrev fK (K : Type*) [Field K] (f : ℤ[X]) : K[X] := f.map (Int.castRingHom K)

theorem natDegree_fK (f : ℤ[X]) : (fK K f).natDegree = f.natDegree :=
  natDegree_map_eq_of_injective (RingHom.injective_int _) _

theorem eval_fK_eq_sum (f : ℤ[X]) (y : K) :
    (fK K f).eval y = ∑ j ∈ range (f.natDegree + 1), (f.coeff j : K) * y ^ j := by
  rw [eval_eq_sum_range, natDegree_fK]
  simp [coeff_map]

theorem sum_inv_root {f : ℤ[X]} {y : K} (hy : (fK K f).eval y = 0) (hy0 : y ≠ 0) :
    ∑ j ∈ range (f.natDegree + 1), (f.coeff j : K) * y⁻¹ ^ (f.natDegree - j) = 0 := by
  have h := congrArg (· * y⁻¹ ^ f.natDegree) hy
  simp only [eval_fK_eq_sum, Finset.sum_mul, zero_mul] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj : j ≤ f.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [← pow_mul_pow_sub y⁻¹ hj, mul_assoc, ← mul_assoc (y ^ j), ← mul_pow,
    mul_inv_cancel₀ hy0, one_pow, one_mul]

omit [CharZero K] in
/-- An integer polynomial evaluated at a point of valuation `≤ 1`. -/
theorem valuation_eval_le_one (g : ℤ[X]) {y : K} (hy : v y ≤ 1) :
    v ((fK K g).eval y) ≤ 1 := by
  rw [eval_eq_sum_range]
  refine v.map_sum_le fun i _ => ?_
  rw [v.map_mul, v.map_pow, coeff_map, eq_intCast]
  calc v (g.coeff i : K) * v y ^ i ≤ 1 * 1 :=
        mul_le_mul' (valuation_intCast_le_one v _) (pow_le_one₀ zero_le hy)
    _ = 1 := one_mul 1

omit [CharZero K] in
/-- An integer polynomial with all coefficients divisible by `p`, evaluated at a point of
valuation `≤ 1`. -/
theorem valuation_eval_lt_one_of_dvd (hv : IsAdicAt v p) {g : ℤ[X]}
    (hg : ∀ n, (p : ℤ) ∣ g.coeff n) {y : K} (hy : v y ≤ 1) : v ((fK K g).eval y) < 1 := by
  rw [eval_eq_sum_range]
  refine v.map_sum_lt one_ne_zero fun i _ => ?_
  rw [v.map_mul, v.map_pow, coeff_map, eq_intCast]
  calc v (g.coeff i : K) * v y ^ i ≤ v (g.coeff i : K) * 1 :=
        mul_le_mul' le_rfl (pow_le_one₀ zero_le hy)
    _ < 1 := by rw [mul_one]; exact (hv _).mpr (hg i)

variable (hf : Hyp p d f) (hv : IsAdicAt v p)
include hf hv

theorem one_le_valuation_of_root {y : K} (hy : (fK K f).eval y = 0) : 1 ≤ v y := by
  by_contra h
  rw [not_le] at h
  rw [eval_fK_eq_sum] at hy
  have key := valuation_sum_eq_of_dominant v (range (f.natDegree + 1))
    (fun j => (f.coeff j : K) * y ^ j) (j₀ := 0) (by simp) (by simp [hv.eq_one hf.coeff_zero])
    (by
      intro j _ hj
      simp only [pow_zero, mul_one, hv.eq_one hf.coeff_zero, v.map_mul, v.map_pow]
      calc v (f.coeff j : K) * v y ^ j ≤ 1 * v y ^ j := by
            gcongr; exact valuation_intCast_le_one v _
        _ < 1 := by rw [one_mul]; exact pow_lt_one₀ zero_le h hj)
  rw [hy] at key
  simp [hv.eq_one hf.coeff_zero] at key

theorem ne_zero_of_root {y : K} (hy : (fK K f).eval y = 0) : y ≠ 0 := by
  intro h
  have := one_le_valuation_of_root hf hv hy
  simp [h] at this

omit [CharZero K] in
theorem valuation_lead : v (f.coeff f.natDegree : K) = v (p : K) := by
  obtain ⟨u, hu, hpu⟩ := hf.lead_eq
  rw [hu]; push_cast
  rw [v.map_mul, hv.eq_one hpu, mul_one]

omit [CharZero K] in
theorem valuation_coeff_sub : v (f.coeff (f.natDegree - d) : K) = 1 :=
  hv.eq_one hf.not_dvd_coeff_sub

/-- A root `y` with `1 < v y` has `v (y⁻¹) ^ d = v p`. -/
theorem valuation_inv_pow_eq {y : K} (hy : (fK K f).eval y = 0) (h1 : 1 < v y) :
    v y⁻¹ ^ d = v (p : K) := by
  have hy0 : y ≠ 0 := ne_zero_of_root hf hv hy
  have hS := sum_inv_root hy hy0
  have hlead := valuation_lead hf hv
  have hmid := valuation_coeff_sub hf hv
  set z := y⁻¹ with hz_def
  have hz0 : z ≠ 0 := inv_ne_zero hy0
  have hvz0 : 0 < v z := by rw [zero_lt_iff, Ne, Valuation.zero_iff]; exact hz0
  have hz : v z < 1 := by
    rw [hz_def, map_inv₀, inv_lt_one₀ (lt_trans zero_lt_one h1)]; exact h1
  have hvp0 := valuation_prime_ne_zero (v := v) hf.prime
  have hvp0' : 0 < v (p : K) := zero_lt_iff.mpr hvp0
  have hdN := hf.le_natDegree
  set N := f.natDegree with hN
  have hterm : ∀ j, v ((f.coeff j : K) * z ^ (N - j)) = v (f.coeff j : K) * v z ^ (N - j) := by
    intro j; rw [v.map_mul, v.map_pow]
  rcases lt_trichotomy (v z ^ d) (v (p : K)) with hlt | heq | hgt
  · exfalso
    have key := valuation_sum_eq_of_dominant v (range (N + 1))
      (fun j => (f.coeff j : K) * z ^ (N - j)) (j₀ := N) (by simp)
      (by simp only [Nat.sub_self, pow_zero, mul_one, hlead]; exact hvp0)
      (by
        intro j hj hjN
        have hjN' : j < N := by
          have := Finset.mem_range.mp hj; omega
        simp only [Nat.sub_self, pow_zero, mul_one, hlead, hterm]
        by_cases hjd : N - d < j
        · calc v (f.coeff j : K) * v z ^ (N - j) ≤ v (p : K) * v z ^ (N - j) :=
                mul_le_mul_left (valuation_le_of_dvd (hf.dvd_coeff_of_lt hjd)) _
            _ < v (p : K) := mul_lt_of_lt_one_right hvp0' (pow_lt_one₀ zero_le hz (by omega))
        · calc v (f.coeff j : K) * v z ^ (N - j) ≤ 1 * v z ^ (N - j) :=
                mul_le_mul_left (valuation_intCast_le_one v _) _
            _ ≤ v z ^ d := by rw [one_mul]; exact pow_le_pow_of_le_one zero_le hz.le (by omega)
            _ < v (p : K) := hlt)
    rw [hS, v.map_zero] at key
    simp only [Nat.sub_self, pow_zero, mul_one, hlead] at key
    exact hvp0 key.symm
  · exact heq
  · exfalso
    have key := valuation_sum_eq_of_dominant v (range (N + 1))
      (fun j => (f.coeff j : K) * z ^ (N - j)) (j₀ := N - d) (Finset.mem_range.mpr (by omega))
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
        · calc v (f.coeff j : K) * v z ^ (N - j) ≤ v (p : K) * 1 :=
                mul_le_mul' (valuation_le_of_dvd (hf.dvd_coeff_of_lt hjd'))
                  (pow_le_one₀ zero_le hz.le)
            _ < v z ^ d := by rw [mul_one]; exact hgt
        · calc v (f.coeff j : K) * v z ^ (N - j) ≤ 1 * v z ^ (N - j) :=
                mul_le_mul_left (valuation_intCast_le_one v _) _
            _ < v z ^ d := by
                rw [one_mul]; exact pow_lt_pow_right_of_lt_one₀ hvz0 hz (by omega))
    rw [hS, v.map_zero] at key
    simp only [hterm] at key
    rw [hmid, one_mul, Nat.sub_sub_self hdN] at key
    exact pow_ne_zero _ hvz0.ne' key.symm

theorem valuation_inv_eq {y y' : K} (hy : (fK K f).eval y = 0) (h1 : 1 < v y)
    (hy' : (fK K f).eval y' = 0) (h1' : 1 < v y') : v y⁻¹ = v y'⁻¹ := by
  have e := valuation_inv_pow_eq hf hv hy h1
  have e' := valuation_inv_pow_eq hf hv hy' h1'
  have hd : d ≠ 0 := by have := hf.pos; omega
  rcases lt_trichotomy (v y⁻¹) (v y'⁻¹) with h | h | h
  · have := pow_lt_pow_left₀ h zero_le hd; rw [e, e'] at this; exact absurd this (lt_irrefl _)
  · exact h
  · have := pow_lt_pow_left₀ h zero_le hd; rw [e, e'] at this; exact absurd this (lt_irrefl _)

/-- Two distinct roots `y, y'` with `1 < v y`, `1 < v y'` have inverses that are not
congruent modulo a higher power of the prime than `y⁻¹` itself:
`v (y⁻¹) ≤ v (y⁻¹ - y'⁻¹)`. -/
theorem valuation_inv_le_valuation_inv_sub {y y' : K} (hy : (fK K f).eval y = 0)
    (h1 : 1 < v y) (hy' : (fK K f).eval y' = 0) (h1' : 1 < v y') (hne : y ≠ y') :
    v y⁻¹ ≤ v (y⁻¹ - y'⁻¹) := by
  have hy0 : y ≠ 0 := ne_zero_of_root hf hv hy
  have hy0' : y' ≠ 0 := ne_zero_of_root hf hv hy'
  have hS := sum_inv_root hy hy0
  have hS' := sum_inv_root hy' hy0'
  have hzz := valuation_inv_eq hf hv hy h1 hy' h1'
  have hpow := valuation_inv_pow_eq hf hv hy h1
  set z := y⁻¹ with hz_def
  set z' := y'⁻¹ with hz'_def
  have hz0 : z ≠ 0 := inv_ne_zero hy0
  have hvz0 : 0 < v z := by rw [zero_lt_iff, Ne, Valuation.zero_iff]; exact hz0
  have hz : v z < 1 := by
    rw [hz_def, map_inv₀, inv_lt_one₀ (lt_trans zero_lt_one h1)]; exact h1
  have hzne : z ≠ z' := fun h => hne (inv_injective h)
  have hvp0 := valuation_prime_ne_zero (v := v) hf.prime
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
  have hb : ∀ j ∈ range (N + 1), v ((f.coeff j : K) * z ^ (N - j)) ≤ v (p : K) := by
    intro j hj
    have hjN : j ≤ N := by have := Finset.mem_range.mp hj; omega
    rw [v.map_mul, v.map_pow]
    by_cases hjd : N - d < j
    · calc v (f.coeff j : K) * v z ^ (N - j) ≤ v (p : K) * 1 :=
            mul_le_mul' (valuation_le_of_dvd (hf.dvd_coeff_of_lt hjd)) (pow_le_one₀ zero_le hz.le)
        _ = v (p : K) := mul_one _
    · calc v (f.coeff j : K) * v z ^ (N - j) ≤ 1 * v z ^ d :=
            mul_le_mul' (valuation_intCast_le_one v _)
              (pow_le_pow_of_le_one zero_le hz.le (by omega))
        _ = v (p : K) := by rw [one_mul, hpow]
  have htay := valuation_sum_taylor_le v (range (N + 1)) (fun j => (f.coeff j : K) * z ^ (N - j))
    (fun j => N - j) hb (x := 1) (δ := δ) (by simp) hvδ.le
  set D := ∑ j ∈ range (N + 1), ((N - j : ℕ) : K) * ((f.coeff j : K) * z ^ (N - j)) with hD
  have hid : ∑ j ∈ range (N + 1), (f.coeff j : K) * z ^ (N - j) *
      ((1 + δ) ^ (N - j) - 1 ^ (N - j) - ((N - j : ℕ) : K) * 1 ^ (N - j - 1) * δ) =
      -(δ * D) := by
    have e1 : ∑ j ∈ range (N + 1), (f.coeff j : K) * z ^ (N - j) *
        ((1 + δ) ^ (N - j) - 1 ^ (N - j) - ((N - j : ℕ) : K) * 1 ^ (N - j - 1) * δ) =
        ∑ j ∈ range (N + 1), (f.coeff j : K) * z' ^ (N - j) -
        ∑ j ∈ range (N + 1), (f.coeff j : K) * z ^ (N - j) - δ * D := by
      rw [hD, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hz', mul_pow]; simp only [one_pow]; ring
    rw [e1, hS, hS']; ring
  rw [hid, Valuation.map_neg, v.map_mul] at htay
  have hd1 : v (d : K) = 1 := hv.natCast_eq_one (by have := hf.pos; omega) hf.lt
  have hterm2 : ∀ j, v (((N - j : ℕ) : K) * ((f.coeff j : K) * z ^ (N - j))) =
      v ((N - j : ℕ) : K) * (v (f.coeff j : K) * v z ^ (N - j)) := by
    intro j; rw [v.map_mul, v.map_mul, v.map_pow]
  have hvD : v D = v (p : K) := by
    rw [hD]
    have key := valuation_sum_eq_of_dominant v (range (N + 1))
      (fun j => ((N - j : ℕ) : K) * ((f.coeff j : K) * z ^ (N - j))) (j₀ := N - d)
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
        · calc v ((N - j : ℕ) : K) * (v (f.coeff j : K) * v z ^ (N - j))
              ≤ 1 * (v (p : K) * v z ^ (N - j)) :=
                mul_le_mul' (valuation_natCast_le_one v _)
                  (mul_le_mul_left (valuation_le_of_dvd (hf.dvd_coeff_of_lt hjd')) _)
            _ < v (p : K) := by
                rw [one_mul]
                exact mul_lt_of_lt_one_right hvp0' (pow_lt_one₀ zero_le hz (by omega))
        · calc v ((N - j : ℕ) : K) * (v (f.coeff j : K) * v z ^ (N - j))
              ≤ 1 * (1 * v z ^ (N - j)) :=
                mul_le_mul' (valuation_natCast_le_one v _)
                  (mul_le_mul_left (valuation_intCast_le_one v _) _)
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
theorem valuation_derivative_eq_one {y : K} (hy : (fK K f).eval y = 0) (hy1 : v y ≤ 1) :
    v ((fK K f).derivative.eval y) = 1 := by
  have : Fact p.Prime := ⟨hf.prime⟩
  have hsep : (f.map (Int.castRingHom (ZMod p))).Separable :=
    PerfectField.separable_iff_squarefree.mpr hf.squarefree
  obtain ⟨a, b, hab⟩ := hsep
  obtain ⟨U, rfl⟩ := Polynomial.map_surjective (Int.castRingHom (ZMod p))
    ZMod.intCast_surjective a
  obtain ⟨V, rfl⟩ := Polynomial.map_surjective (Int.castRingHom (ZMod p))
    ZMod.intCast_surjective b
  set E := U * f + V * derivative f - 1 with hE
  have hEmap : E.map (Int.castRingHom (ZMod p)) = 0 := by
    rw [hE, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
      Polynomial.map_one, ← derivative_map, hab, sub_self]
  have hEdvd : ∀ n, (p : ℤ) ∣ E.coeff n := by
    intro n
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have := congrArg (fun q => q.coeff n) hEmap
    simpa [coeff_map] using this
  have hlt := valuation_eval_lt_one_of_dvd hv hEdvd hy1
  have hEval : (fK K E).eval y = (fK K V).eval y * (fK K f).derivative.eval y - 1 := by
    rw [hE, fK, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
      Polynomial.map_one, ← derivative_map]
    simp only [eval_sub, eval_add, eval_mul, eval_one]
    rw [show eval y (Polynomial.map (Int.castRingHom K) f) = 0 from hy]
    ring
  rw [hEval] at hlt
  have hge : 1 ≤ v ((fK K V).eval y * (fK K f).derivative.eval y) := by
    by_contra h
    rw [not_le] at h
    have h' : v ((fK K V).eval y * (fK K f).derivative.eval y) < v 1 := by rwa [v.map_one]
    rw [v.map_sub_eq_of_lt_right h', v.map_one] at hlt
    exact lt_irrefl _ hlt
  have hder : v ((fK K f).derivative.eval y) ≤ 1 := by
    rw [fK, derivative_map]; exact valuation_eval_le_one _ hy1
  refine le_antisymm hder (not_lt.mp fun h => ?_)
  rw [v.map_mul] at hge
  have := mul_le_mul' (valuation_eval_le_one V hy1) (le_refl (v ((fK K f).derivative.eval y)))
  rw [one_mul] at this
  exact absurd (hge.trans this) (not_le.mpr h)

omit [CharZero K] in
/-- Two distinct roots `y, y'` of `f` with `v y ≤ 1` are not congruent modulo the prime:
`v (y' - y) = 1`. -/
theorem not_valuation_sub_lt_one {y y' : K} (hy : (fK K f).eval y = 0) (hy1 : v y ≤ 1)
    (hy' : (fK K f).eval y' = 0) (hne : y ≠ y') : ¬ v (y' - y) < 1 := by
  intro hlt
  obtain ⟨δ, rfl⟩ : ∃ δ, y' = y + δ := ⟨y' - y, by ring⟩
  rw [add_sub_cancel_left] at hlt
  have hδ0 : δ ≠ 0 := by rintro rfl; exact hne (add_zero y).symm
  have hder := valuation_derivative_eq_one hf hv hy hy1
  set F := fK K f with hF
  have htay := valuation_sum_taylor_le v F.support (fun n => F.coeff n) (fun n => n) (M := 1)
    (fun n _ => by rw [hF, coeff_map, eq_intCast]; exact valuation_intCast_le_one v _) hy1 hlt.le
  have hid : ∑ n ∈ F.support, F.coeff n * ((y + δ) ^ n - y ^ n - (n : K) * y ^ (n - 1) * δ) =
      F.eval (y + δ) - F.eval y - F.derivative.eval y * δ := by
    rw [eval_eq_sum, eval_eq_sum, derivative_eval, Polynomial.sum_def, Polynomial.sum_def,
      Polynomial.sum_def, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hid, hy, hy', sub_self, zero_sub, Valuation.map_neg, v.map_mul, hder, one_mul,
    one_mul] at htay
  have hvδ0 : 0 < v δ := by rw [zero_lt_iff, Ne, Valuation.zero_iff]; exact hδ0
  have h2 : v δ * 1 ≤ v δ * v δ := by rwa [mul_one, ← pow_two]
  exact absurd hlt (not_lt.mpr (le_of_mul_le_mul_left h2 hvδ0))

/-- If `f` splits in `K`, exactly `d` of its roots, counted with multiplicity, satisfy
`1 < v y`. -/
theorem card_filter_roots_one_lt (hsplit : Multiset.card (fK K f).roots = f.natDegree) :
    Multiset.card ((fK K f).roots.filter (fun y => 1 < v y)) = d := by
  classical
  have hlead := valuation_lead hf hv
  set F := fK K f with hF
  have hroots : Multiset.card F.roots = F.natDegree := by rw [hF, natDegree_fK]; exact hsplit
  have hprod := C_leadingCoeff_mul_prod_multiset_X_sub_C hroots
  have h0 := congrArg (eval 0) hprod
  rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map] at h0
  have hF0 : F.eval 0 = (f.coeff 0 : K) := by
    rw [← coeff_zero_eq_eval_zero, hF, coeff_map, eq_intCast]
  have hlc : F.leadingCoeff = (f.coeff f.natDegree : K) := by
    rw [leadingCoeff, hF, natDegree_fK, coeff_map, eq_intCast]
  have hv0 := congrArg v h0
  rw [v.map_mul, map_multiset_prod, Multiset.map_map, hF0, hlc, hlead,
    hv.eq_one hf.coeff_zero] at hv0
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
  have hvp0 := valuation_prime_ne_zero (v := v) hf.prime
  have hinv1 : (v (p : K))⁻¹ ≠ 1 := by
    intro h; rw [inv_eq_one] at h; exact (ne_of_lt hv.lt_one) h
  exact (pow_right_injective₀ (inv_pos.mpr (zero_lt_iff.mpr hvp0)) hinv1 hQd).symm

end Valuation

end RootResidues

end ArithmeticOfJacobiPolynomials
