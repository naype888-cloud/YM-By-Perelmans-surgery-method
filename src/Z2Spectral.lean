/-
Copyright (c) 2026 Eduardo Nava Hernandez. All rights reserved.
Released under the NRS license (see LICENSE).
-/
import SlabLimit
import PerronOverlap

/-!
# The projection on the top eigenspace, as a vector

`SlabLimit.top_limit` bounds `∑_{i,l ∈ top} c_i c_l (e_i ⬝ Y e_l)`. For `w = ∑_{j ∈ top} c_j e_j`
this double sum is the quadratic form `w ⬝ Y w`, and `∑_{j ∈ top} c_j² = w ⬝ w`.

## Main results

- `Z2Spectral.dot_eigen` : the eigenvectors are orthonormal for the dot product.
- `Z2Spectral.top_quad` : `w ⬝ Y w = ∑_{i,l ∈ S} c_i c_l (e_i ⬝ Y e_l)`.
- `Z2Spectral.top_sq` : `w ⬝ w = ∑_{j ∈ S} c_j²`.
-/

open Matrix Finset SpectralGap

namespace Z2Spectral

variable {n : ℕ} {T : Matrix (Fin n) (Fin n) ℝ}

/-- The eigenvectors are orthonormal for the dot product. -/
lemma dot_eigen (hT : T.IsHermitian) (i l : Fin n) :
    (hT.eigenvectorBasis i : Fin n → ℝ) ⬝ᵥ (hT.eigenvectorBasis l : Fin n → ℝ) =
      if i = l then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp hT.eigenvectorBasis.orthonormal) i l
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simpa [star_trivial, dotProduct_comm] using h

/-- The projection of `v` on the eigenvectors of `S`. -/
noncomputable def proj (hT : T.IsHermitian) (v : Fin n → ℝ) (S : Finset (Fin n)) : Fin n → ℝ :=
  ∑ j ∈ S, coeff hT j v • (hT.eigenvectorBasis j : Fin n → ℝ)

lemma top_quad (hT : T.IsHermitian) (Y : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (S : Finset (Fin n)) :
    proj hT v S ⬝ᵥ (Y *ᵥ proj hT v S) =
      ∑ i ∈ S, ∑ l ∈ S, coeff hT i v * coeff hT l v *
        ((hT.eigenvectorBasis i : Fin n → ℝ) ⬝ᵥ (Y *ᵥ (hT.eigenvectorBasis l : Fin n → ℝ))) := by
  unfold proj
  rw [Matrix.mulVec_sum, sum_dotProduct]
  refine sum_congr rfl fun i _ => ?_
  rw [dotProduct_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

lemma top_sq (hT : T.IsHermitian) (v : Fin n → ℝ) (S : Finset (Fin n)) :
    proj hT v S ⬝ᵥ proj hT v S = ∑ j ∈ S, coeff hT j v ^ 2 := by
  have h := top_quad hT 1 v S
  simp only [Matrix.one_mulVec] at h
  rw [h]
  refine sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i]
  · rw [dot_eigen hT i i]; simp [sq]
  · intro l _ hli
    rw [dot_eigen hT i l, if_neg (Ne.symm hli)]; simp
  · intro h'; exact absurd hi h'

end Z2Spectral
