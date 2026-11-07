/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
import Mathlib

/-!

# The area law of a Z₂ gauge theory with no 3-cells

## i. Overview

A Z₂ lattice gauge theory has a spin `σ_l ∈ ℤ/2` on each link and the weight
`∏_p exp (β · s(u_p))`, where `u_p = ∑_l inc p l · σ_l` is the plaquette variable and
`s x = (-1)^x`. When the plaquette map `σ ↦ u` is onto (no 3-cells, as on a planar rectangle with free
boundary), the plaquette variables are independent and uniform under the counting measure, and the
expectation of a product over a set `S` of plaquettes is `tanh(β)^|S|`. A Wilson loop that is the
boundary of `S` is that product: the area law `⟨W⟩ = e^{-σ |S|}`, `σ = -log tanh β > 0`.

This is the exact mechanism of strong coupling (confinement and the exponential decay in the
area), in a case where it is an identity. It is NOT the mass gap of Yang–Mills: the group is
abelian and the lattice has no 3-cells.

## ii. Key results

- `Z2Gauge.expect_eq_tanh_pow` : `⟨∏_{p∈S} s(u_p)⟩ = tanh(β)^|S|`.
- `Z2Gauge.wilson_eq_prod` : the Wilson loop of `∂S` is `∏_{p∈S} s(u_p)`.
- `Z2Gauge.area_law` : `⟨W(∂S)⟩ = tanh(β)^|S| = exp(-σ_β |S|)`.
- `Z2Gauge.stringTension_pos` : `σ_β = -log tanh β > 0` for `β > 0`.

## iii. Table of contents

- A. Spins and plaquettes
- B. The expectation of a product of plaquettes
- C. The Wilson loop and the area law

## iv. References

* K. Osterwalder, E. Seiler, Gauge field theories on a lattice, Ann. Phys. 110 (1978).

-/

open Finset

namespace Z2Gauge

/-! ## A. Spins and plaquettes -/

/-- The value `(-1)^x` of an element of `ℤ/2`. -/
def spin (x : ZMod 2) : ℝ := if x = 0 then 1 else -1

lemma spin_add (x y : ZMod 2) : spin (x + y) = spin x * spin y := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have key : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases key x with rfl | rfl <;> rcases key y with rfl | rfl <;> simp [spin, h11, h10]

lemma spin_zero : spin 0 = 1 := by simp [spin]

lemma spin_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    spin (∑ i ∈ s, f i) = ∏ i ∈ s, spin (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [spin_zero]
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, spin_add, ih]

variable {P L : Type*} [Fintype P] [Fintype L] [DecidableEq P] [DecidableEq L]

/-- The plaquette variable `u_p = ∑_l inc p l · σ_l`. -/
def plaq (inc : P → L → ZMod 2) (σ : L → ZMod 2) (p : P) : ZMod 2 := ∑ l, inc p l * σ l

/-- The plaquette map, additive. -/
def plaqHom (inc : P → L → ZMod 2) : (L → ZMod 2) →+ (P → ZMod 2) where
  toFun σ p := plaq inc σ p
  map_zero' := by ext p; simp [plaq]
  map_add' σ τ := by ext p; simp [plaq, mul_add, sum_add_distrib]

/-- The Boltzmann weight `∏_p exp (β · s(u_p))`. -/
noncomputable def weight (inc : P → L → ZMod 2) (β : ℝ) (σ : L → ZMod 2) : ℝ :=
  ∏ p, Real.exp (β * spin (plaq inc σ p))

/-- The partition function. -/
noncomputable def partition (inc : P → L → ZMod 2) (β : ℝ) : ℝ := ∑ σ, weight inc β σ

/-- The unnormalized expectation of a product of plaquette spins over `S`. -/
noncomputable def numerator (inc : P → L → ZMod 2) (β : ℝ) (S : Finset P) : ℝ :=
  ∑ σ, weight inc β σ * ∏ p ∈ S, spin (plaq inc σ p)

/-! ## B. The expectation of a product of plaquettes -/

/-- If the plaquette map is onto, every fibre has the same number of elements, so a sum over
configurations is that number times a sum over plaquette variables. -/
lemma sum_comp_plaqHom {inc : P → L → ZMod 2} (hs : Function.Surjective (plaqHom inc))
    (g : (P → ZMod 2) → ℝ) :
    ∑ σ, g (plaqHom inc σ) =
      ((univ.filter fun σ => plaqHom inc σ = 0).card : ℝ) * ∑ u, g u := by
  classical
  rw [← sum_fiberwise (univ : Finset (L → ZMod 2)) (plaqHom inc)]
  rw [Finset.mul_sum]
  refine sum_congr rfl fun u _ => ?_
  have hc : (univ.filter fun σ => plaqHom inc σ = u).card =
      (univ.filter fun σ => plaqHom inc σ = 0).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range _ (hs u) (hs 0)
  rw [sum_congr rfl (g := fun _ => g u) (fun σ hσ => by rw [(mem_filter.mp hσ).2]), sum_const,
    hc, nsmul_eq_mul]

lemma univ_zmod_two : (univ : Finset (ZMod 2)) = {0, 1} := by decide

lemma sum_exp_spin (β : ℝ) : ∑ x : ZMod 2, Real.exp (β * spin x) = 2 * Real.cosh β := by
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  rw [univ_zmod_two, sum_pair (by decide), Real.cosh_eq]
  simp [spin, h10]
  ring

lemma sum_exp_spin_mul (β : ℝ) :
    ∑ x : ZMod 2, Real.exp (β * spin x) * spin x = 2 * Real.sinh β := by
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  rw [univ_zmod_two, sum_pair (by decide), Real.sinh_eq]
  simp [spin, h10]
  ring

/-- A sum over plaquette variables of a product factorizes. -/
lemma sum_pi_prod (h : P → ZMod 2 → ℝ) :
    ∑ u : P → ZMod 2, ∏ p, h p (u p) = ∏ p, ∑ x, h p x := by
  rw [Finset.prod_univ_sum]
  simp [Fintype.piFinset_univ]

/-- The partition function is the fibre count times `(2 cosh β)^|P|`. -/
lemma partition_eq {inc : P → L → ZMod 2} (hs : Function.Surjective (plaqHom inc)) (β : ℝ) :
    partition inc β =
      ((univ.filter fun σ => plaqHom inc σ = 0).card : ℝ) * (2 * Real.cosh β) ^ Fintype.card P := by
  unfold partition weight
  have := sum_comp_plaqHom hs (fun u => ∏ p, Real.exp (β * spin (u p)))
  rw [show (∑ σ, ∏ p, Real.exp (β * spin (plaq inc σ p))) =
      ∑ σ, (fun u : P → ZMod 2 => ∏ p, Real.exp (β * spin (u p))) (plaqHom inc σ) from rfl, this,
    sum_pi_prod (fun _ x => Real.exp (β * spin x))]
  simp [sum_exp_spin]

/-- The numerator is the fibre count times a product over the plaquettes: `2 sinh β` in `S` and
`2 cosh β` outside. -/
lemma numerator_eq {inc : P → L → ZMod 2} (hs : Function.Surjective (plaqHom inc)) (β : ℝ)
    (S : Finset P) :
    numerator inc β S =
      ((univ.filter fun σ => plaqHom inc σ = 0).card : ℝ) *
        ∏ p, (if p ∈ S then 2 * Real.sinh β else 2 * Real.cosh β) := by
  unfold numerator weight
  have hg : ∀ σ : L → ZMod 2, (∏ p, Real.exp (β * spin (plaq inc σ p))) *
      ∏ p ∈ S, spin (plaq inc σ p) =
      (fun u : P → ZMod 2 => ∏ p, (Real.exp (β * spin (u p)) *
        (if p ∈ S then spin (u p) else 1))) (plaqHom inc σ) := by
    intro σ
    simp only [prod_mul_distrib]
    rw [Finset.prod_ite_mem]
    simp
    rfl
  rw [sum_congr rfl fun σ _ => hg σ,
    sum_comp_plaqHom hs (fun u => ∏ p, (Real.exp (β * spin (u p)) *
      (if p ∈ S then spin (u p) else 1))),
    sum_pi_prod (fun p x => Real.exp (β * spin x) * (if p ∈ S then spin x else 1))]
  congr 1
  refine prod_congr rfl fun p _ => ?_
  by_cases hp : p ∈ S
  · simp [hp, sum_exp_spin_mul]
  · simp [hp, sum_exp_spin]

/-- **The expectation of a product of plaquette spins is `tanh(β)^|S|`.** -/
theorem expect_eq_tanh_pow {inc : P → L → ZMod 2} (hs : Function.Surjective (plaqHom inc))
    (β : ℝ) (S : Finset P) :
    numerator inc β S / partition inc β = Real.tanh β ^ S.card := by
  rw [numerator_eq hs, partition_eq hs]
  have hc : ((univ.filter fun σ => plaqHom inc σ = 0).card : ℝ) ≠ 0 := by
    have : 0 < (univ.filter fun σ => plaqHom inc σ = 0).card :=
      Finset.card_pos.mpr ⟨0, by simp⟩
    exact_mod_cast this.ne'
  have hch : (2 * Real.cosh β) ≠ 0 := by positivity
  have hfac : ∀ p : P, (if p ∈ S then 2 * Real.sinh β else 2 * Real.cosh β) =
      (if p ∈ S then Real.tanh β else 1) * (2 * Real.cosh β) := by
    intro p
    by_cases hp : p ∈ S
    · simp only [hp, ite_true, Real.tanh_eq_sinh_div_cosh]
      field_simp
    · simp [hp]
  rw [mul_div_mul_left _ _ hc, prod_congr rfl fun p _ => hfac p, prod_mul_distrib, prod_const,
    Finset.card_univ, mul_div_assoc, div_self (pow_ne_zero _ hch), mul_one,
    Finset.prod_ite_mem, univ_inter, prod_const]

/-! ## C. The Wilson loop and the area law -/

/-- The loop `∂S`: the links that belong to an odd number of plaquettes of `S`. -/
def boundary (inc : P → L → ZMod 2) (S : Finset P) : L → ZMod 2 := fun l => ∑ p ∈ S, inc p l

omit [Fintype P] [DecidableEq P] [DecidableEq L] in
/-- **The Wilson loop of `∂S` is the product of the plaquettes of `S`.** -/
lemma wilson_eq_prod (inc : P → L → ZMod 2) (S : Finset P) (σ : L → ZMod 2) :
    spin (∑ l, boundary inc S l * σ l) = ∏ p ∈ S, spin (plaq inc σ p) := by
  have : (∑ l, boundary inc S l * σ l) = ∑ p ∈ S, plaq inc σ p := by
    simp only [boundary, plaq, Finset.sum_mul]
    exact Finset.sum_comm
  rw [this, spin_sum]

/-- The expectation of the Wilson loop of `∂S`. -/
noncomputable def wilsonExpect (inc : P → L → ZMod 2) (β : ℝ) (S : Finset P) : ℝ :=
  (∑ σ, weight inc β σ * spin (∑ l, boundary inc S l * σ l)) / partition inc β

/-- **The area law**: `⟨W(∂S)⟩ = tanh(β)^|S|`, for every `β`. -/
theorem area_law {inc : P → L → ZMod 2} (hs : Function.Surjective (plaqHom inc)) (β : ℝ)
    (S : Finset P) : wilsonExpect inc β S = Real.tanh β ^ S.card := by
  unfold wilsonExpect
  have : (∑ σ, weight inc β σ * spin (∑ l, boundary inc S l * σ l)) = numerator inc β S := by
    unfold numerator
    exact sum_congr rfl fun σ _ => by rw [wilson_eq_prod]
  rw [this, expect_eq_tanh_pow hs]

/-- The string tension `σ_β = -log tanh β`. -/
noncomputable def stringTension (β : ℝ) : ℝ := -Real.log (Real.tanh β)

/-- **The string tension is positive** for `β > 0`: the loop decays. -/
theorem stringTension_pos {β : ℝ} (hβ : 0 < β) : 0 < stringTension β := by
  unfold stringTension
  have h0 : 0 < Real.tanh β := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hβ) (Real.cosh_pos β)
  have h1 : Real.tanh β < 1 := Real.tanh_lt_one β
  have := Real.log_neg h0 h1
  linarith

/-- **Exponential decay in the area**: `⟨W(∂S)⟩ = exp (-σ_β |S|)`. -/
theorem area_law_exp {inc : P → L → ZMod 2} (hs : Function.Surjective (plaqHom inc)) {β : ℝ}
    (hβ : 0 < β) (S : Finset P) :
    wilsonExpect inc β S = Real.exp (-(stringTension β * S.card)) := by
  have h0 : 0 < Real.tanh β := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hβ) (Real.cosh_pos β)
  rw [area_law hs, show -(stringTension β * S.card) = S.card * Real.log (Real.tanh β) by
    unfold stringTension; ring, Real.exp_nat_mul, Real.exp_log h0]

/-! ## D. A concrete lattice: the rectangle of two plaquettes side by side

The links are `0 = h(0,0)`, `1 = h(0,1)`, `2 = h(1,0)`, `3 = h(1,1)`, `4 = v(0,0)`, `5 = v(1,0)`,
`6 = v(2,0)`; the plaquette `0` has the links `0, 1, 4, 5`, the plaquette `1` has `2, 3, 5, 6`. -/

/-- The incidence of the rectangle `2 × 1`. -/
def inc21 : Fin 2 → Fin 7 → ZMod 2
  | 0, l => if l = 0 ∨ l = 1 ∨ l = 4 ∨ l = 5 then 1 else 0
  | 1, l => if l = 2 ∨ l = 3 ∨ l = 5 ∨ l = 6 then 1 else 0

/-- The plaquette map of the rectangle is onto: no 3-cells. -/
theorem plaqHom_surjective_21 : Function.Surjective (plaqHom inc21) := by
  intro u
  refine ⟨fun l => if l = 4 then u 0 else if l = 6 then u 1 else 0, ?_⟩
  ext p
  fin_cases p <;> simp [plaqHom, plaq, inc21, Fin.sum_univ_succ]

/-- **The area law of the rectangle `2 × 1`**: the Wilson loop of its boundary has expectation
`tanh(β)²`, for every `β`. -/
theorem area_law_21 (β : ℝ) : wilsonExpect inc21 β (Finset.univ : Finset (Fin 2)) = Real.tanh β ^ 2 := by
  rw [area_law plaqHom_surjective_21]
  simp

/-! ## E. The transfer matrix of the strip of one plaquette: its gap is the string tension

On a strip one plaquette wide, with free boundary, the gauge variables of one time slice reduce to
one spin, and the transfer matrix is the `2 × 2` matrix `K_β = [[e^β, e^{-β}], [e^{-β}, e^β]]`. Its
eigenvalues are `2 cosh β` (vacuum, the vector `(1, 1)`) and `2 sinh β` (the vector `(1, -1)`, the
spin). The gap `log (λ₀ / λ₁)` is exactly the string tension `-log tanh β`, and the spin
correlation at distance `n` is `tanh(β)ⁿ`, the area law of a `1 × n` loop. -/

open Matrix in
/-- The transfer matrix of the strip of one plaquette. -/
noncomputable def transfer (β : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.exp β, Real.exp (-β); Real.exp (-β), Real.exp β]

open Matrix in
/-- The vacuum `(1, 1)` is an eigenvector with eigenvalue `2 cosh β`. -/
lemma transfer_mulVec_vac (β : ℝ) :
    transfer β *ᵥ ![1, 1] = (2 * Real.cosh β) • ![(1 : ℝ), 1] := by
  ext i
  fin_cases i <;> simp [transfer, Real.cosh_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    ring

open Matrix in
/-- The spin vector `(1, -1)` is an eigenvector with eigenvalue `2 sinh β`. -/
lemma transfer_mulVec_spin (β : ℝ) :
    transfer β *ᵥ ![1, -1] = (2 * Real.sinh β) • ![(1 : ℝ), -1] := by
  ext i
  fin_cases i <;> simp [transfer, Real.sinh_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    ring

open Matrix in
/-- **The transfer matrix is positive** for `β ≥ 0`: its quadratic form is a sum of two squares
with nonnegative coefficients. -/
theorem transfer_quadratic_nonneg {β : ℝ} (hβ : 0 ≤ β) (x : Fin 2 → ℝ) :
    0 ≤ x ⬝ᵥ (transfer β *ᵥ x) := by
  have h : x ⬝ᵥ (transfer β *ᵥ x) =
      Real.cosh β * (x 0 + x 1) ^ 2 + Real.sinh β * (x 0 - x 1) ^ 2 := by
    simp [transfer, Real.cosh_eq, Real.sinh_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  rw [h]
  have := Real.sinh_nonneg_iff.mpr hβ
  positivity

open Matrix in
/-- The vacuum evolves by `(2 cosh β)ⁿ`. -/
lemma transfer_pow_vac (β : ℝ) (n : ℕ) :
    (transfer β ^ n) *ᵥ ![1, 1] = (2 * Real.cosh β) ^ n • ![(1 : ℝ), 1] := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, transfer_mulVec_vac, Matrix.mulVec_smul, ih, smul_smul,
      pow_succ]
    ring_nf

open Matrix in
/-- The spin evolves by `(2 sinh β)ⁿ`. -/
lemma transfer_pow_spin (β : ℝ) (n : ℕ) :
    (transfer β ^ n) *ᵥ ![1, -1] = (2 * Real.sinh β) ^ n • ![(1 : ℝ), -1] := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, transfer_mulVec_spin, Matrix.mulVec_smul, ih, smul_smul,
      pow_succ]
    ring_nf

open Matrix in
/-- **The spin correlation of the strip at distance `n` is `tanh(β)ⁿ`**, the area law of a `1 × n`
loop: the ratio of the spin sector to the vacuum sector of the transfer matrix. -/
theorem transfer_correlation (β : ℝ) (n : ℕ) :
    (![1, -1] ⬝ᵥ ((transfer β ^ n) *ᵥ ![1, -1])) / (![1, 1] ⬝ᵥ ((transfer β ^ n) *ᵥ ![1, 1])) =
      Real.tanh β ^ n := by
  rw [transfer_pow_vac, transfer_pow_spin]
  simp only [dotProduct_smul, smul_eq_mul]
  have h1 : (![1, -1] : Fin 2 → ℝ) ⬝ᵥ ![1, -1] = 2 := by
    simp [dotProduct, Fin.sum_univ_two]; norm_num
  have h2 : (![1, 1] : Fin 2 → ℝ) ⬝ᵥ ![1, 1] = 2 := by
    simp [dotProduct, Fin.sum_univ_two]; norm_num
  rw [h1, h2, Real.tanh_eq_sinh_div_cosh, div_pow]
  have hc : (2 * Real.cosh β) ^ n ≠ 0 := pow_ne_zero _ (by positivity)
  field_simp
  ring

/-- **The gap of the strip is the string tension**: `log (2 cosh β / 2 sinh β) = -log tanh β`. -/
theorem gap_eq_stringTension {β : ℝ} (hβ : 0 < β) :
    Real.log ((2 * Real.cosh β) / (2 * Real.sinh β)) = stringTension β := by
  have hs := Real.sinh_pos_iff.mpr hβ
  have hc := Real.cosh_pos β
  unfold stringTension
  rw [Real.tanh_eq_sinh_div_cosh, Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity)]
  rw [Real.log_mul (by norm_num) hs.ne', Real.log_mul (by norm_num) hc.ne']
  ring

open Matrix in
/-- **The two descriptions agree on the strip of two plaquettes**: the Wilson loop `2 × 1`, computed
by summing over the links (the area law), is the correlation of the transfer matrix at distance
`2`. -/
theorem strip_two_consistent (β : ℝ) :
    wilsonExpect inc21 β (Finset.univ : Finset (Fin 2)) =
      (![1, -1] ⬝ᵥ ((transfer β ^ 2) *ᵥ ![1, -1])) /
        (![1, 1] ⬝ᵥ ((transfer β ^ 2) *ᵥ ![1, 1])) := by
  rw [area_law_21, transfer_correlation]

/-! ## F. The exact high temperature expansion (strong coupling), for any incidence

With `t = tanh β`, `exp (β s) = cosh β (1 + t s)` for a spin `s = ±1`, so the weight is
`cosh(β)^|P| ∏_p (1 + t u_p) = cosh(β)^|P| ∑_{S ⊆ P} t^|S| ∏_{p∈S} u_p`. Summing over the links, the
characters of `ℤ/2` kill every term except those with `∂S = c`, where `∂S = ∑_{p∈S} inc p` is the
boundary of `S`. Hence the expectation of the loop `c` is
`⟨W(c)⟩ = (∑_{∂S = c} t^|S|) / (∑_{∂S = 0} t^|S|)`, an identity in any dimension and any incidence. -/

lemma spin_one : spin 1 = -1 := by
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  simp [spin, h10]

lemma exp_spin_eq (β : ℝ) (x : ZMod 2) :
    Real.exp (β * spin x) = Real.cosh β * (1 + Real.tanh β * spin x) := by
  have hc := (Real.cosh_pos β).ne'
  have key : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases key x with rfl | rfl
  · rw [spin_zero, mul_one, mul_one, Real.tanh_eq_sinh_div_cosh, mul_add, mul_one,
      mul_div_cancel₀ _ hc, Real.cosh_add_sinh]
  · rw [spin_one, mul_neg, mul_one, mul_neg, mul_one, Real.tanh_eq_sinh_div_cosh, ← sub_eq_add_neg,
      mul_sub, mul_one, mul_div_cancel₀ _ hc, Real.cosh_sub_sinh]

omit [DecidableEq P] [DecidableEq L] in
/-- The Boltzmann weight expands over the subsets of plaquettes. -/
lemma weight_expand (inc : P → L → ZMod 2) (β : ℝ) (σ : L → ZMod 2) :
    weight inc β σ = Real.cosh β ^ Fintype.card P *
      ∑ S ∈ (Finset.univ : Finset P).powerset,
        Real.tanh β ^ S.card * ∏ p ∈ S, spin (plaq inc σ p) := by
  unfold weight
  simp only [exp_spin_eq, prod_mul_distrib, prod_const, Finset.card_univ]
  rw [Finset.prod_one_add]
  congr 1
  refine sum_congr rfl fun S _ => ?_
  rw [prod_mul_distrib, prod_const]

lemma sum_spin_mul (c : ZMod 2) : ∑ x : ZMod 2, spin (c * x) = if c = 0 then 2 else 0 := by
  have key : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  rw [univ_zmod_two, sum_pair (by decide)]
  rcases key c with rfl | rfl
  · simp [spin_zero]; norm_num
  · simp [h10, spin_zero, spin_one]

/-- **Orthogonality of the characters of `ℤ/2` over the links**: the sum over configurations of
`spin (∑_l d_l σ_l)` is `2^|L|` if `d = 0` and `0` otherwise. -/
lemma sum_char (d : L → ZMod 2) :
    ∑ σ : L → ZMod 2, spin (∑ l, d l * σ l) =
      if d = 0 then (2 : ℝ) ^ Fintype.card L else 0 := by
  have h1 : ∀ σ : L → ZMod 2, spin (∑ l, d l * σ l) = ∏ l, spin (d l * σ l) :=
    fun σ => spin_sum _ _
  rw [sum_congr rfl fun σ _ => h1 σ, sum_pi_prod (fun l x => spin (d l * x))]
  simp only [sum_spin_mul]
  rw [Finset.prod_ite_zero]
  by_cases hd : d = 0
  · simp [hd]
  · have hex : ∃ l, ¬ d l = 0 := by
      by_contra h
      push Not at h
      exact hd (funext h)
    simp [hd, hex]

/-- The sum over the subsets `S` of plaquettes with boundary `c`, weighted by `t^|S|`. -/
noncomputable def highTempSum (inc : P → L → ZMod 2) (t : ℝ) (c : L → ZMod 2) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset P).powerset with boundary inc S = c, t ^ S.card

lemma add_eq_zero_iff_eq (a b : ZMod 2) : a + b = 0 ↔ a = b := by
  have key : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases key a with rfl | rfl <;> rcases key b with rfl | rfl <;> decide

omit [DecidableEq P] in
/-- **The unnormalized expectation of the loop `c`**: `cosh(β)^|P| 2^|L|` times the sum over the
subsets `S` of plaquettes with boundary `c`. -/
theorem numer_highTemp (inc : P → L → ZMod 2) (β : ℝ) (c : L → ZMod 2) :
    ∑ σ, weight inc β σ * spin (∑ l, c l * σ l) =
      Real.cosh β ^ Fintype.card P * 2 ^ Fintype.card L * highTempSum inc (Real.tanh β) c := by
  have hterm : ∀ (S : Finset P) (σ : L → ZMod 2),
      (∏ p ∈ S, spin (plaq inc σ p)) * spin (∑ l, c l * σ l) =
        spin (∑ l, (boundary inc S l + c l) * σ l) := by
    intro S σ
    rw [← wilson_eq_prod, ← spin_add]
    congr 1
    simp only [add_mul, sum_add_distrib]
  have hexp : ∀ σ : L → ZMod 2, weight inc β σ * spin (∑ l, c l * σ l) =
      ∑ S ∈ (Finset.univ : Finset P).powerset, Real.cosh β ^ Fintype.card P *
        (Real.tanh β ^ S.card * ((∏ p ∈ S, spin (plaq inc σ p)) * spin (∑ l, c l * σ l))) := by
    intro σ
    rw [weight_expand, mul_assoc, Finset.sum_mul, Finset.mul_sum]
    exact sum_congr rfl fun S _ => by ring
  have hS : ∀ S : Finset P, ∑ σ : L → ZMod 2, Real.cosh β ^ Fintype.card P *
      (Real.tanh β ^ S.card * ((∏ p ∈ S, spin (plaq inc σ p)) * spin (∑ l, c l * σ l))) =
      Real.cosh β ^ Fintype.card P * 2 ^ Fintype.card L *
        (if boundary inc S = c then Real.tanh β ^ S.card else 0) := by
    intro S
    have hiff : ((fun l => boundary inc S l + c l) = 0) ↔ boundary inc S = c := by
      constructor
      · intro h
        funext l
        exact (add_eq_zero_iff_eq _ _).mp (congrFun h l)
      · intro h
        funext l
        exact (add_eq_zero_iff_eq _ _).mpr (congrFun h l)
    rw [← Finset.mul_sum, ← Finset.mul_sum, sum_congr rfl fun σ _ => hterm S σ,
      sum_char (fun l => boundary inc S l + c l)]
    by_cases h : boundary inc S = c
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (hiff.mpr h)), ite_eq_left_of_eq_true _ _ (eq_true h)]
      ring
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (mt hiff.mp h)), ite_eq_right_of_eq_false _ _ (eq_false h)]
      ring
  rw [sum_congr rfl fun σ _ => hexp σ, Finset.sum_comm]
  rw [sum_congr rfl fun S _ => hS S]
  unfold highTempSum
  rw [Finset.sum_filter, Finset.mul_sum]

omit [DecidableEq P] in
/-- The partition function is `cosh(β)^|P| 2^|L|` times the sum over the cycles (`∂S = 0`). -/
theorem partition_highTemp (inc : P → L → ZMod 2) (β : ℝ) :
    partition inc β =
      Real.cosh β ^ Fintype.card P * 2 ^ Fintype.card L * highTempSum inc (Real.tanh β) 0 := by
  have h := numer_highTemp inc β 0
  simp only [Pi.zero_apply, zero_mul, sum_const_zero, spin_zero, mul_one] at h
  exact h

omit [DecidableEq P] in
/-- **The exact high temperature expansion**: for any incidence, in any dimension, the expectation
of the loop `c` is `⟨W(c)⟩ = (∑_{∂S = c} t^|S|) / (∑_{∂S = 0} t^|S|)` with `t = tanh β`. -/
theorem highTemp_expect (inc : P → L → ZMod 2) (β : ℝ) (c : L → ZMod 2) :
    (∑ σ, weight inc β σ * spin (∑ l, c l * σ l)) / partition inc β =
      highTempSum inc (Real.tanh β) c / highTempSum inc (Real.tanh β) 0 := by
  rw [numer_highTemp, partition_highTemp]
  have hK : Real.cosh β ^ Fintype.card P * 2 ^ Fintype.card L ≠ 0 := by positivity
  exact mul_div_mul_left _ _ hK

omit [DecidableEq P] [DecidableEq L] in
/-- For `t ≥ 0` the sum over the cycles is at least `1` (the empty surface), so the denominator
never vanishes. -/
theorem one_le_highTempSum_zero (inc : P → L → ZMod 2) {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ highTempSum inc t 0 := by
  unfold highTempSum
  have hmem : (∅ : Finset P) ∈ (Finset.univ : Finset P).powerset.filter
      (fun S => boundary inc S = 0) :=
    Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, by funext l; simp [boundary]⟩
  calc (1 : ℝ) = t ^ (∅ : Finset P).card := by simp
    _ ≤ _ := Finset.single_le_sum (f := fun S : Finset P => t ^ S.card)
      (fun S _ => pow_nonneg ht _) hmem

omit [DecidableEq P] in
/-- **The Wilson loop of `∂S₀` in the high temperature expansion.** -/
theorem wilsonExpect_highTemp (inc : P → L → ZMod 2) (β : ℝ) (S₀ : Finset P) :
    wilsonExpect inc β S₀ =
      highTempSum inc (Real.tanh β) (boundary inc S₀) / highTempSum inc (Real.tanh β) 0 :=
  highTemp_expect inc β (boundary inc S₀)

/-! ## G. Check: with no 3-cells the expansion is the area law

If the plaquette map is onto, the incidence vectors are independent over `ℤ/2`: the only cycle is
the empty one, and a boundary determines its surface. The expansion then has a single term in the
numerator and in the denominator, and gives `tanh(β)^|S₀|` again. With 3-cells there are nontrivial
cycles and the denominator is a sum over them: the corrections of the strong coupling expansion. -/

omit [DecidableEq L] in
/-- If the plaquette map is onto, a combination of the incidence vectors that vanishes has zero
coefficients. -/
lemma coeff_eq_zero {inc : P → L → ZMod 2} (hs : Function.Surjective (plaqHom inc))
    (u : P → ZMod 2) (h : ∀ l, ∑ p, u p * inc p l = 0) : u = 0 := by
  funext p0
  obtain ⟨σ, hσ⟩ := hs (Pi.single p0 1)
  have h1 : ∀ p, plaq inc σ p = (Pi.single p0 (1 : ZMod 2) : P → ZMod 2) p := fun p =>
    congrFun hσ p
  have h2 : ∑ p, u p * plaq inc σ p = 0 := by
    calc ∑ p, u p * plaq inc σ p = ∑ p, ∑ l, u p * (inc p l * σ l) := by
          simp only [plaq, Finset.mul_sum]
      _ = ∑ l, ∑ p, u p * (inc p l * σ l) := Finset.sum_comm
      _ = ∑ l, (∑ p, u p * inc p l) * σ l := by
          simp only [Finset.sum_mul, mul_assoc]
      _ = 0 := by simp [h]
  simp only [h1, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at h2
  simpa using h2

/-- The indicator of a set of plaquettes, with values in `ℤ/2`. -/
def indicator (S : Finset P) (p : P) : ZMod 2 := if p ∈ S then 1 else 0

omit [Fintype L] [DecidableEq L] in
lemma boundary_eq_sum (inc : P → L → ZMod 2) (S : Finset P) (l : L) :
    boundary inc S l = ∑ p, indicator S p * inc p l := by
  simp only [boundary, indicator, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

omit [DecidableEq L] in
/-- **With no 3-cells a boundary determines its surface.** -/
lemma boundary_injective {inc : P → L → ZMod 2} (hs : Function.Surjective (plaqHom inc))
    {S S₀ : Finset P} (h : boundary inc S = boundary inc S₀) : S = S₀ := by
  have hadd : ∀ a : ZMod 2, a + a = 0 := by decide
  have h0 : ∀ l, ∑ p, (indicator S p + indicator S₀ p) * inc p l = 0 := by
    intro l
    simp only [add_mul, Finset.sum_add_distrib, ← boundary_eq_sum, h]
    exact hadd _
  have hu := coeff_eq_zero hs _ h0
  ext p
  have hp := (add_eq_zero_iff_eq _ _).mp (congrFun hu p)
  have key : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  constructor
  · intro hmem
    have h1 : indicator S p = 1 := by simp [indicator, hmem]
    rw [h1] at hp
    by_contra hn
    simp [indicator, hn] at hp
  · intro hmem
    have h1 : indicator S₀ p = 1 := by simp [indicator, hmem]
    rw [h1] at hp
    by_contra hn
    simp [indicator, hn] at hp

set_option linter.unusedSectionVars false in
/-- With no 3-cells the sum over the surfaces with boundary `∂S₀` has the single term `S₀`. -/
theorem highTempSum_boundary {inc : P → L → ZMod 2} (hs : Function.Surjective (plaqHom inc))
    (t : ℝ) (S₀ : Finset P) : highTempSum inc t (boundary inc S₀) = t ^ S₀.card := by
  unfold highTempSum
  have : (Finset.univ : Finset P).powerset.filter (fun S => boundary inc S = boundary inc S₀) =
      {S₀} := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
      Finset.mem_singleton]
    exact ⟨fun h => boundary_injective hs h, fun h => by rw [h]⟩
  rw [this, sum_singleton]

/-- **The expansion recovers the area law when there are no 3-cells.** -/
theorem area_law_of_highTemp {inc : P → L → ZMod 2} (hs : Function.Surjective (plaqHom inc))
    (β : ℝ) (S₀ : Finset P) : wilsonExpect inc β S₀ = Real.tanh β ^ S₀.card := by
  rw [wilsonExpect_highTemp, highTempSum_boundary hs]
  have h0 : boundary inc (∅ : Finset P) = 0 := by funext l; simp [boundary]
  rw [← h0, highTempSum_boundary hs]
  simp

end Z2Gauge
