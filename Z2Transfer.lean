/-
Copyright (c) 2026 Eduardo Nava Hernandez. All rights reserved.
Released under the NRS license (see LICENSE).
-/
import Mathlib

/-!
# The transfer matrix of Wilson's `Z₂` model is positive semidefinite

In temporal (axial) gauge the transfer matrix of Wilson's `Z₂` gauge model on the space of
configurations `σ : L → ℤ/2` of the spatial links is `T = D^{1/2} K D^{1/2}`, where

* `K(σ, σ') = ∏_l exp (β s_l s'_l)` (the time-like plaquettes, `s_l = ±1`),
* `D = diag (w)` is any positive weight (the space-like plaquettes at one time slice).

## Main results

- `Z2Transfer.quad_K` : `x ⬝ K x = ∑_S c_S (∑_σ χ_S(σ) x_σ)²`, `c_S = sinh^{|S|} cosh^{|L|-|S|}`.
- `Z2Transfer.K_posSemidef` : `K` is positive semidefinite for `β ≥ 0`.
- `Z2Transfer.transfer_posSemidef` : `T = D^{1/2} K D^{1/2}` is positive semidefinite.
-/

open Finset Matrix

namespace Z2Transfer

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- The sign `±1` of an element of `ℤ/2`. -/
def sgn (a : ZMod 2) : ℝ := if a = 0 then 1 else -1

/-- The character `χ_S(σ) = ∏_{l ∈ S} s_l`. -/
def chi (S : Finset L) (σ : L → ZMod 2) : ℝ := ∏ l ∈ S, sgn (σ l)

/-- The kernel of the time-like plaquettes. -/
noncomputable def kern (β : ℝ) (σ σ' : L → ZMod 2) : ℝ :=
  ∏ l, Real.exp (β * (sgn (σ l) * sgn (σ' l)))

/-- The matrix `K_β`. -/
noncomputable def K (β : ℝ) : Matrix (L → ZMod 2) (L → ZMod 2) ℝ := fun σ σ' => kern β σ σ'

lemma exp_sgn (β : ℝ) (a b : ZMod 2) :
    Real.exp (β * (sgn a * sgn b)) = Real.sinh β * (sgn a * sgn b) + Real.cosh β := by
  have h : sgn a * sgn b = 1 ∨ sgn a * sgn b = -1 := by
    unfold sgn; split_ifs <;> norm_num
  rcases h with h | h <;> rw [h]
  · rw [mul_one, mul_one, add_comm, Real.cosh_add_sinh]
  · rw [mul_neg_one, mul_neg_one]
    linarith [Real.cosh_sub_sinh β]

/-- The coefficient of the character `S` in `K_β`. -/
noncomputable def coef (β : ℝ) (S : Finset L) : ℝ :=
  (∏ _l ∈ S, Real.sinh β) * ∏ _l ∈ (Finset.univ \ S), Real.cosh β

lemma kern_expand (β : ℝ) (σ σ' : L → ZMod 2) :
    kern β σ σ' = ∑ S ∈ (Finset.univ : Finset L).powerset, coef β S * (chi S σ * chi S σ') := by
  unfold kern
  rw [Finset.prod_congr rfl fun l _ => exp_sgn β (σ l) (σ' l), Finset.prod_add]
  refine Finset.sum_congr rfl fun S _ => ?_
  unfold coef chi
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

/-- The quadratic form of `K` as a sum of squares. -/
theorem quad_K (β : ℝ) (x : (L → ZMod 2) → ℝ) :
    x ⬝ᵥ (K β *ᵥ x) =
      ∑ S ∈ (Finset.univ : Finset L).powerset, coef β S * (∑ σ, chi S σ * x σ) ^ 2 := by
  have h1 : x ⬝ᵥ (K β *ᵥ x) = ∑ σ, ∑ σ', ∑ S ∈ (Finset.univ : Finset L).powerset,
      x σ * (coef β S * (chi S σ * chi S σ')) * x σ' := by
    simp only [dotProduct, mulVec, K, kern_expand, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun σ' _ =>
      Finset.sum_congr rfl fun S _ => ?_
    ring
  rw [h1]
  have h2 : ∀ σ : L → ZMod 2, ∑ σ', ∑ S ∈ (Finset.univ : Finset L).powerset,
      x σ * (coef β S * (chi S σ * chi S σ')) * x σ' = ∑ S ∈ (Finset.univ : Finset L).powerset,
      ∑ σ', x σ * (coef β S * (chi S σ * chi S σ')) * x σ' := fun σ => Finset.sum_comm
  rw [Finset.sum_congr rfl fun σ _ => h2 σ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ' _ => ?_
  ring

lemma coef_nonneg {β : ℝ} (hβ : 0 ≤ β) (S : Finset L) : 0 ≤ coef β S := by
  unfold coef
  exact mul_nonneg (Finset.prod_nonneg fun _ _ => Real.sinh_nonneg_iff.mpr hβ)
    (Finset.prod_nonneg fun _ _ => (Real.cosh_pos β).le)

omit [DecidableEq L] in
lemma K_isHermitian (β : ℝ) : (K (L := L) β).IsHermitian := by
  ext σ σ'
  simp only [conjTranspose_apply, K, kern, star_trivial]
  exact Finset.prod_congr rfl fun l _ => by rw [mul_comm (sgn (σ' l))]

/-- **`K` is positive semidefinite** for `β ≥ 0`. -/
theorem K_posSemidef {β : ℝ} (hβ : 0 ≤ β) : (K (L := L) β).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨K_isHermitian β, fun x => ?_⟩
  rw [star_trivial, quad_K]
  exact Finset.sum_nonneg fun S _ => mul_nonneg (coef_nonneg hβ S) (sq_nonneg _)

/-- The transfer matrix `T = D^{1/2} K D^{1/2}`, with `D = diag (w)` the space-like weight. -/
noncomputable def transfer (β : ℝ) (w : (L → ZMod 2) → ℝ) :
    Matrix (L → ZMod 2) (L → ZMod 2) ℝ :=
  Matrix.diagonal (fun σ => Real.sqrt (w σ)) * K β * Matrix.diagonal (fun σ => Real.sqrt (w σ))

/-- **The transfer matrix is positive semidefinite** for `β ≥ 0` and any weight `w`. -/
theorem transfer_posSemidef {β : ℝ} (hβ : 0 ≤ β) (w : (L → ZMod 2) → ℝ) :
    (transfer β w).PosSemidef := by
  have h := (K_posSemidef (L := L) hβ).conjTranspose_mul_mul_same
    (Matrix.diagonal (fun σ => Real.sqrt (w σ)))
  simpa [transfer, Matrix.diagonal_conjTranspose] using h

end Z2Transfer
