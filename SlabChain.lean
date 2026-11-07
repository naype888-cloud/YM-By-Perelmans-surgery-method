/-
Copyright (c) 2026 Eduardo Nava Hernandez. All rights reserved.
Released under the NRS license (see LICENSE).
-/
import Mathlib

/-!
# Time slicing: a chain of slices is a matrix element of a power of the transfer matrix

A model on `m + 1` time slices whose configurations `s : Fin (m+1) → ι` have weight
`∏_j u (s j) · ∏_{j < m} M (s j) (s (j+1))` (a slice weight `u`, a nearest-slice kernel `M`) has
partition function `√u ⬝ T^m √u` with `T = D^{1/2} M D^{1/2}`, `D = diag u`.

## Main results

- `SlabChain.headSum_eq` : `headSum M u m f = f ⬝ᵥ (P^m *ᵥ u)`, with `P = diag u * M`.
- `SlabChain.chainSum_eq` : `chainSum M u m = 1 ⬝ᵥ (P^m *ᵥ u)`.

## Scope

Pure linear algebra. That the box of the `Z₂` model, in axial gauge, has this form (`u` the weight
of the space-like plaquettes, `M = K_β`) is NOT proved here.
-/

open Finset Matrix

namespace SlabChain

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The partition function of `m + 1` slices. -/
noncomputable def chainSum (M : Matrix ι ι ℝ) (u : ι → ℝ) (m : ℕ) : ℝ :=
  ∑ s : Fin (m + 1) → ι, (∏ j, u (s j)) * ∏ j : Fin m, M (s j.castSucc) (s j.succ)

/-- The chain with a weight `f` on the first slice. -/
noncomputable def headSum (M : Matrix ι ι ℝ) (u : ι → ℝ) (m : ℕ) (f : ι → ℝ) : ℝ :=
  ∑ s : Fin (m + 1) → ι,
    (∏ j, u (s j)) * (∏ j : Fin m, M (s j.castSucc) (s j.succ)) * f (s 0)

omit [DecidableEq ι] in
lemma headSum_zero (M : Matrix ι ι ℝ) (u : ι → ℝ) (f : ι → ℝ) :
    headSum M u 0 f = ∑ i, u i * f i := by
  unfold headSum
  rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
  simp

omit [DecidableEq ι] in
/-- The step of the induction: peel the first slice. -/
lemma headSum_succ (M : Matrix ι ι ℝ) (u : ι → ℝ) (m : ℕ) (f : ι → ℝ) :
    headSum M u (m + 1) f =
      ∑ l, headSum M u m (fun i => f l * u l * M l i) := by
  unfold headSum
  rw [← (Fin.consEquiv (fun _ : Fin (m + 2) => ι)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => ?_
  refine Finset.sum_congr rfl fun s' _ => ?_
  simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.castSucc_zero, Fin.castSucc_succ]
  ring

/-- The first slice weighted by `f`: `f ⬝ᵥ (P^m u)`, with `P = diag u * M`. -/
theorem headSum_eq (M : Matrix ι ι ℝ) (u : ι → ℝ) (m : ℕ) (f : ι → ℝ) :
    headSum M u m f = f ⬝ᵥ (((diagonal u * M) ^ m) *ᵥ u) := by
  induction m generalizing f with
  | zero =>
    rw [headSum_zero]
    simp only [pow_zero, one_mulVec, dotProduct]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  | succ m ih =>
    rw [headSum_succ]
    simp only [ih]
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    simp only [dotProduct, Matrix.mulVec, Matrix.diagonal_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring

/-- **The chain sum is a matrix element**: `chainSum M u m = 1 ⬝ᵥ (P^m u)`. -/
theorem chainSum_eq (M : Matrix ι ι ℝ) (u : ι → ℝ) (m : ℕ) :
    chainSum M u m = (fun _ => (1 : ℝ)) ⬝ᵥ (((diagonal u * M) ^ m) *ᵥ u) := by
  rw [← headSum_eq]
  unfold chainSum headSum
  simp

/-- The symmetric transfer matrix `T = D^{1/2} M D^{1/2}`. -/
noncomputable def transferSym (M : Matrix ι ι ℝ) (u : ι → ℝ) : Matrix ι ι ℝ :=
  diagonal (fun i => Real.sqrt (u i)) * M * diagonal (fun i => Real.sqrt (u i))

lemma diag_sqrt_mul_self {u : ι → ℝ} (hu : ∀ i, 0 ≤ u i) :
    diagonal (fun i => Real.sqrt (u i)) * diagonal (fun i => Real.sqrt (u i)) = diagonal u := by
  rw [diagonal_mul_diagonal]
  congr 1
  funext i
  exact Real.mul_self_sqrt (hu i)

/-- `D T = P D`, with `D = diag √u`. -/
lemma diag_mul_transferSym {M : Matrix ι ι ℝ} {u : ι → ℝ} (hu : ∀ i, 0 ≤ u i) :
    diagonal (fun i => Real.sqrt (u i)) * transferSym M u =
      (diagonal u * M) * diagonal (fun i => Real.sqrt (u i)) := by
  unfold transferSym
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, diag_sqrt_mul_self hu]

lemma diag_mul_transferSym_pow {M : Matrix ι ι ℝ} {u : ι → ℝ} (hu : ∀ i, 0 ≤ u i) (m : ℕ) :
    diagonal (fun i => Real.sqrt (u i)) * transferSym M u ^ m =
      (diagonal u * M) ^ m * diagonal (fun i => Real.sqrt (u i)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, diag_mul_transferSym hu,
      ← Matrix.mul_assoc, ← pow_succ]

/-- **The chain sum is `√u ⬝ T^m √u`** for a nonnegative slice weight. -/
theorem chainSum_eq_transfer (M : Matrix ι ι ℝ) {u : ι → ℝ} (hu : ∀ i, 0 ≤ u i) (m : ℕ) :
    chainSum M u m =
      (fun i => Real.sqrt (u i)) ⬝ᵥ ((transferSym M u ^ m) *ᵥ (fun i => Real.sqrt (u i))) := by
  rw [chainSum_eq]
  have hu' : (fun i => u i) = (diagonal (fun i => Real.sqrt (u i))) *ᵥ (fun i => Real.sqrt (u i)) := by
    funext i
    simp [Matrix.mulVec_diagonal, Real.mul_self_sqrt (hu i)]
  have h1 : (fun _ : ι => (1 : ℝ)) ⬝ᵥ (((diagonal u * M) ^ m) *ᵥ u) =
      (fun _ : ι => (1 : ℝ)) ⬝ᵥ ((((diagonal u * M) ^ m * diagonal (fun i => Real.sqrt (u i)))) *ᵥ
        (fun i => Real.sqrt (u i))) := by
    rw [← Matrix.mulVec_mulVec, ← hu']
  rw [h1, ← diag_mul_transferSym_pow hu, ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec]
  congr 1
  funext i
  rw [Matrix.vecMul_diagonal]
  simp

end SlabChain
