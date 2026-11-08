/-
Copyright (c) 2026 Eduardo Nava Hernandez. All rights reserved.
Released under the NRS license (see LICENSE).
-/
import SlabChain

/-!
# Time slicing with two insertions

A chain of `m + 1` slices with a weight `f` on the slice `a` and a weight `g` on the slice `a + b`
(`a + b + c = m`) is the matrix element
`√u ⬝ (T^a diag f T^b diag g T^c) √u` of the symmetric transfer matrix `T = D^{1/2} M D^{1/2}`.

## Main results

- `SlabInsert.insert_one` : one insertion, in terms of `P = diag u * M`.
- `SlabInsert.insert_two` : two insertions, in terms of `P`.
- `SlabInsert.chain_two_insertions` : two insertions, in terms of the symmetric `T`.
-/

open Finset Matrix

namespace SlabInsert

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The chain with a weight `h` on the first slice and an insertion `g` on the slice `b`. -/
theorem insert_one (M : Matrix ι ι ℝ) (u : ι → ℝ) (g : ι → ℝ) :
    ∀ (b c m : ℕ) (hm : b + c = m) (h : ι → ℝ),
      ∑ s : Fin (m + 1) → ι, (∏ j, u (s j)) * (∏ j : Fin m, M (s j.castSucc) (s j.succ)) *
          h (s 0) * g (s ⟨b, by omega⟩) =
        h ⬝ᵥ (((diagonal u * M) ^ b) *ᵥ (diagonal g *ᵥ (((diagonal u * M) ^ c) *ᵥ u))) := by
  intro b
  induction b with
  | zero =>
    intro c m hm h
    obtain rfl : m = c := by omega
    simp only [pow_zero, one_mulVec]
    have := SlabChain.headSum_eq M u m (fun i => h i * g i)
    unfold SlabChain.headSum at this
    have e : ∀ s : Fin (m + 1) → ι, (∏ j, u (s j)) * (∏ j : Fin m, M (s j.castSucc) (s j.succ)) *
        h (s 0) * g (s ⟨0, by omega⟩) = (∏ j, u (s j)) *
          (∏ j : Fin m, M (s j.castSucc) (s j.succ)) * (h (s 0) * g (s 0)) := fun s => by
      rw [← mul_assoc]; rfl
    simp only [e]
    rw [this]
    simp only [dotProduct, Matrix.mulVec_diagonal]
    exact Finset.sum_congr rfl fun i _ => by ring
  | succ b ih =>
    intro c m hm h
    obtain rfl : m = (b + c) + 1 := by omega
    rw [← (Fin.consEquiv (fun _ : Fin (b + c + 1 + 1) => ι)).sum_comp, Fintype.sum_prod_type]
    have step : ∀ l : ι, ∑ s' : Fin (b + c + 1) → ι,
        (∏ j, u ((Fin.consEquiv (fun _ : Fin (b + c + 1 + 1) => ι) (l, s')) j)) *
          (∏ j : Fin (b + c + 1), M ((Fin.consEquiv (fun _ : Fin (b + c + 1 + 1) => ι) (l, s'))
            j.castSucc) ((Fin.consEquiv (fun _ : Fin (b + c + 1 + 1) => ι) (l, s')) j.succ)) *
          h ((Fin.consEquiv (fun _ : Fin (b + c + 1 + 1) => ι) (l, s')) 0) *
          g ((Fin.consEquiv (fun _ : Fin (b + c + 1 + 1) => ι) (l, s')) ⟨b + 1, by omega⟩) =
        (fun i => h l * u l * M l i) ⬝ᵥ (((diagonal u * M) ^ b) *ᵥ
          (diagonal g *ᵥ (((diagonal u * M) ^ c) *ᵥ u))) := by
      intro l
      rw [← ih c (b + c) rfl (fun i => h l * u l * M l i)]
      refine Finset.sum_congr rfl fun s' _ => ?_
      simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
        Fin.castSucc_zero, Fin.castSucc_succ]
      have hc : (Fin.cons l s' : Fin (b + c + 1 + 1) → ι) ⟨b + 1, by omega⟩ =
          s' ⟨b, by omega⟩ := rfl
      rw [hc]
      ring
    simp only [step]
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    simp only [dotProduct, Matrix.mulVec, Matrix.diagonal_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring

/-- Two insertions: `f` on the slice `a`, `g` on the slice `d = a + b`. -/
theorem insert_two (M : Matrix ι ι ℝ) (u : ι → ℝ) (f g : ι → ℝ) :
    ∀ (a b c d m : ℕ) (hd : a + b = d) (hm : d + c = m) (h : ι → ℝ),
      ∑ s : Fin (m + 1) → ι, (∏ j, u (s j)) * (∏ j : Fin m, M (s j.castSucc) (s j.succ)) *
          h (s 0) * (f (s ⟨a, by omega⟩) * g (s ⟨d, by omega⟩)) =
        h ⬝ᵥ (((diagonal u * M) ^ a) *ᵥ (diagonal f *ᵥ (((diagonal u * M) ^ b) *ᵥ
          (diagonal g *ᵥ (((diagonal u * M) ^ c) *ᵥ u))))) := by
  intro a
  induction a with
  | zero =>
    intro b c d m hd hm h
    obtain rfl : d = b := by omega
    obtain rfl : m = d + c := by omega
    have := insert_one M u g d c (d + c) rfl (fun i => h i * f i)
    have e : ∀ s : Fin (d + c + 1) → ι,
        (∏ j, u (s j)) * (∏ j : Fin (d + c), M (s j.castSucc) (s j.succ)) *
          h (s 0) * (f (s ⟨0, by omega⟩) * g (s ⟨d, by omega⟩)) =
        (∏ j, u (s j)) * (∏ j : Fin (d + c), M (s j.castSucc) (s j.succ)) *
          (h (s 0) * f (s 0)) * g (s ⟨d, by omega⟩) := fun s => by
      have : s ⟨0, by omega⟩ = s 0 := rfl
      rw [this]
      ring
    simp only [e]
    rw [this]
    simp only [dotProduct, Matrix.mulVec_diagonal, pow_zero, Matrix.one_mulVec]
    exact Finset.sum_congr rfl fun i _ => by ring
  | succ a ih =>
    intro b c d m hd hm h
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    obtain rfl : m = (d' + c) + 1 := by omega
    rw [← (Fin.consEquiv (fun _ : Fin (d' + c + 1 + 1) => ι)).sum_comp, Fintype.sum_prod_type]
    have step : ∀ l : ι, ∑ s' : Fin (d' + c + 1) → ι,
        (∏ j, u ((Fin.consEquiv (fun _ : Fin (d' + c + 1 + 1) => ι) (l, s')) j)) *
          (∏ j : Fin (d' + c + 1), M ((Fin.consEquiv (fun _ : Fin (d' + c + 1 + 1) => ι) (l, s'))
            j.castSucc) ((Fin.consEquiv (fun _ : Fin (d' + c + 1 + 1) => ι) (l, s')) j.succ)) *
          h ((Fin.consEquiv (fun _ : Fin (d' + c + 1 + 1) => ι) (l, s')) 0) *
          (f ((Fin.consEquiv (fun _ : Fin (d' + c + 1 + 1) => ι) (l, s')) ⟨a + 1, by omega⟩) *
            g ((Fin.consEquiv (fun _ : Fin (d' + c + 1 + 1) => ι) (l, s')) ⟨d' + 1, by omega⟩)) =
        (fun i => h l * u l * M l i) ⬝ᵥ (((diagonal u * M) ^ a) *ᵥ (diagonal f *ᵥ
          (((diagonal u * M) ^ b) *ᵥ (diagonal g *ᵥ (((diagonal u * M) ^ c) *ᵥ u))))) := by
      intro l
      rw [← ih b c d' (d' + c) (by omega) rfl (fun i => h l * u l * M l i)]
      refine Finset.sum_congr rfl fun s' _ => ?_
      simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
        Fin.castSucc_zero, Fin.castSucc_succ]
      have hc1 : (Fin.cons l s' : Fin (d' + c + 1 + 1) → ι) ⟨a + 1, by omega⟩ =
          s' ⟨a, by omega⟩ := rfl
      have hc2 : (Fin.cons l s' : Fin (d' + c + 1 + 1) → ι) ⟨d' + 1, by omega⟩ =
          s' ⟨d', by omega⟩ := rfl
      rw [hc1, hc2]
      ring
    simp only [step]
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    simp only [dotProduct, Matrix.mulVec, Matrix.diagonal_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring

section Symmetric

variable {M : Matrix ι ι ℝ} {u : ι → ℝ}

lemma pow_mulVec_diag (hu : ∀ i, 0 ≤ u i) (k : ℕ) (y : ι → ℝ) :
    ((diagonal u * M) ^ k) *ᵥ (diagonal (fun i => Real.sqrt (u i)) *ᵥ y) =
      diagonal (fun i => Real.sqrt (u i)) *ᵥ ((SlabChain.transferSym M u ^ k) *ᵥ y) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← SlabChain.diag_mul_transferSym_pow hu]

lemma diag_mulVec_diag (f : ι → ℝ) (v y : ι → ℝ) :
    diagonal f *ᵥ (diagonal v *ᵥ y) = diagonal v *ᵥ (diagonal f *ᵥ y) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 2
  funext i
  exact mul_comm _ _

/-- **A chain with two insertions is a matrix element of the symmetric transfer matrix**:
`f` on the slice `a`, `g` on the slice `a + b`, `a + b + c = m`. -/
theorem chain_two_insertions (hu : ∀ i, 0 ≤ u i) (f g : ι → ℝ) (a b c m : ℕ)
    (hm : a + b + c = m) :
    ∑ s : Fin (m + 1) → ι, (∏ j, u (s j)) * (∏ j : Fin m, M (s j.castSucc) (s j.succ)) *
        (f (s ⟨a, by omega⟩) * g (s ⟨a + b, by omega⟩)) =
      (fun i => Real.sqrt (u i)) ⬝ᵥ
        (((SlabChain.transferSym M u ^ a * diagonal f * SlabChain.transferSym M u ^ b *
            diagonal g * SlabChain.transferSym M u ^ c)) *ᵥ (fun i => Real.sqrt (u i))) := by
  have h := insert_two M u f g a b c (a + b) m rfl (by omega) (fun _ => 1)
  simp only [mul_one] at h
  rw [h]
  have hu' : u = diagonal (fun i => Real.sqrt (u i)) *ᵥ (fun i => Real.sqrt (u i)) := by
    funext i
    simp [Matrix.mulVec_diagonal, Real.mul_self_sqrt (hu i)]
  have hc := pow_mulVec_diag (M := M) hu c (fun i => Real.sqrt (u i))
  rw [← hu'] at hc
  rw [hc, diag_mulVec_diag, pow_mulVec_diag hu, diag_mulVec_diag, pow_mulVec_diag hu]
  simp only [← Matrix.mulVec_mulVec]
  simp [dotProduct, Matrix.mulVec_diagonal]

end Symmetric

end SlabInsert
