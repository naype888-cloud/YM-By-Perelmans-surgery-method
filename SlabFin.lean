/-
Copyright (c) 2026 Eduardo Nava Hernandez. All rights reserved.
Released under the NRS license (see LICENSE).
-/
import Mathlib

/-!
# Reindexing a matrix to `Fin n`

For an equivalence `e : ι ≃ Fin n`, the matrix `T' = T.submatrix e.symm e.symm` has powers
`T'^m = (T^m).submatrix e.symm e.symm`, the same matrix elements, and inherits Hermitian,
positive semidefinite and entrywise nonnegativity.

## Main results

- `SlabFin.reindex_pow` : `(T.submatrix e.symm e.symm)^m = (T^m).submatrix e.symm e.symm`.
- `SlabFin.dotProduct_reindex` : `v ∘ e.symm ⬝ᵥ (Y' *ᵥ (w ∘ e.symm)) = v ⬝ᵥ (Y *ᵥ w)`.
- `SlabFin.reindex_isHermitian`, `SlabFin.reindex_posSemidef`, `SlabFin.reindex_nonneg`.
-/

open Matrix

namespace SlabFin

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- The reindexed matrix. -/
def reindexFin (e : ι ≃ Fin n) (T : Matrix ι ι ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  T.submatrix e.symm e.symm

/-- Powers commute with reindexing. -/
theorem reindex_pow (e : ι ≃ Fin n) (T : Matrix ι ι ℝ) (m : ℕ) :
    reindexFin e T ^ m = reindexFin e (T ^ m) := by
  induction m with
  | zero =>
    simp only [pow_zero, reindexFin]
    ext i j
    simp [Matrix.one_apply, Matrix.submatrix_apply, e.symm.injective.eq_iff]
  | succ m ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [reindexFin]
    rw [Matrix.submatrix_mul_equiv]

/-- Matrix elements are unchanged by reindexing. -/
theorem dotProduct_reindex (e : ι ≃ Fin n) (Y : Matrix ι ι ℝ) (v w : ι → ℝ) :
    (v ∘ e.symm) ⬝ᵥ (reindexFin e Y *ᵥ (w ∘ e.symm)) = v ⬝ᵥ (Y *ᵥ w) := by
  unfold reindexFin
  rw [Matrix.submatrix_mulVec_equiv]
  have : (w ∘ e.symm) ∘ e.symm.symm = w := by
    funext i; simp
  rw [this]
  simp only [dotProduct, Function.comp]
  exact Equiv.sum_comp e.symm (fun i => v i * (Y *ᵥ w) i)

theorem reindex_isHermitian (e : ι ≃ Fin n) {T : Matrix ι ι ℝ} (h : T.IsHermitian) :
    (reindexFin e T).IsHermitian :=
  h.submatrix _

theorem reindex_posSemidef (e : ι ≃ Fin n) {T : Matrix ι ι ℝ} (h : T.PosSemidef) :
    (reindexFin e T).PosSemidef :=
  h.submatrix _

theorem reindex_nonneg (e : ι ≃ Fin n) {T : Matrix ι ι ℝ} (h : ∀ i j, 0 ≤ T i j) :
    ∀ i j, 0 ≤ reindexFin e T i j := fun i j => h _ _

end SlabFin
