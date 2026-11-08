/-
Copyright (c) 2026 Eduardo Nava Hernandez. All rights reserved.
Released under the NRS license (see LICENSE).
-/
import AxialSlab
import AxialSeeds

/-!
# The boundary of the axial rectangle is the loop of two rows

For `j₀ + k ≤ B`, the boundary (mod 2) of the `xy` plaquettes of `rectAx R k j₀ k₀` is the loop
`cLoop R k₀ j₀ (j₀ + k)`: the `x` links of the rows `j₀` and `j₀ + k`, at height `k₀`, in the
columns `i < R`. For `k = 0` both sides vanish.

## Main results

- `AreaBound.boundary_rectAx_eq_cLoop` : the identity of the two functions on the axial links.
-/

open Finset

namespace AreaBound

variable (A B C : ℕ)

/-- A sum of an indicator of `j = m` over `Fin B`. -/
lemma sum_fin_ind (m : ℕ) (Q : Prop) [Decidable Q] :
    ∑ j : Fin B, (if j.val = m ∧ Q then (1 : ZMod 2) else 0) =
      if m < B ∧ Q then 1 else 0 := by
  by_cases h : m < B
  · rw [Finset.sum_eq_single (⟨m, h⟩ : Fin B)]
    · simp [h]
    · intro j _ hj
      have : j.val ≠ m := fun e => hj (Fin.ext e)
      simp [this]
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [h]
    · intro j _
      have : j.val ≠ m := by have := j.2; omega
      simp [this]

open Classical in
/-- The boundary of the rectangle on an `x` link. -/
lemma boundary_rectAx_inl (R k j₀ : ℕ) (k₀ : Fin (C + 1)) (i' : Fin A) (j' : Fin (B + 1))
    (k' : Fin (C + 1)) :
    Z2Gauge.boundary (ainc A B C) (rectAx A B C R k j₀ k₀) (.inl (i', j', k')) =
      if i'.val < R ∧ k' = k₀ then
        (if j'.val < B ∧ (j₀ ≤ j'.val ∧ j'.val < j₀ + k) then 1 else 0) +
          (if 1 ≤ j'.val ∧ (j₀ ≤ j'.val - 1 ∧ j'.val - 1 < j₀ + k) then 1 else 0)
      else 0 := by
  unfold Z2Gauge.boundary rectAx
  rw [Finset.sum_filter, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type, ite_false, Finset.sum_const_zero, add_zero]
  simp only [ainc, aemb, cinc, ite_and]
  by_cases hi : i'.val < R
  · by_cases hk : k' = k₀
    · subst hk
      simp only [hi, true_and, ite_true, and_self]
      refine Eq.trans (b := ∑ x : Fin A, ∑ x1 : Fin B, ∑ x2 : Fin (C + 1),
            if x = i' ∧ x2 = k' then
              (if (j₀ ≤ x1.val ∧ x1.val < j₀ + k) ∧ (j'.val = x1.val ∨ j'.val = x1.val + 1)
                then (1 : ZMod 2) else 0)
            else 0) ?_ ?_
      · refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x1 _ =>
          Finset.sum_congr rfl fun x2 _ => ?_
        by_cases h1 : x = i'
        · subst h1
          by_cases h2 : x2 = k'
          · subst h2
            simp only [hi, true_and, and_self, eq_self_iff_true, ite_true]
            by_cases hj1 : j₀ ≤ x1.val ∧ x1.val < j₀ + k <;>
              by_cases hj2 : j'.val = x1.val ∨ j'.val = x1.val + 1 <;> simp [hj1, hj2]
          · simp [h2, Ne.symm h2]
        · have h1' : ¬ i'.val = x.val := fun h => h1 (Fin.ext h.symm)
          simp [h1, h1']
      simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true]
      have e2 : ∀ x1 : Fin B, (if j₀ ≤ x1.val then if x1.val < j₀ + k then
          if j'.val = x1.val ∨ j'.val = x1.val + 1 then (1 : ZMod 2) else 0 else 0 else 0) =
          (if x1.val = j'.val ∧ (j₀ ≤ j'.val ∧ j'.val < j₀ + k) then 1 else 0) +
            (if x1.val = j'.val - 1 ∧ (1 ≤ j'.val ∧ j₀ ≤ j'.val - 1 ∧ j'.val - 1 < j₀ + k)
              then 1 else 0) := by
        intro x1
        split_ifs <;> first | rfl | (exfalso; omega) | decide
      simp only [e2, Finset.sum_add_distrib]
      rw [sum_fin_ind B j'.val (j₀ ≤ j'.val ∧ j'.val < j₀ + k),
        sum_fin_ind B (j'.val - 1) (1 ≤ j'.val ∧ j₀ ≤ j'.val - 1 ∧ j'.val - 1 < j₀ + k)]
      congr 1 <;> split_ifs <;> first | rfl | (exfalso; omega)
    · simp only [hk, and_false, ite_false, ite_self]
      refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun x1 _ =>
        Finset.sum_eq_zero fun x2 _ => ?_
      split_ifs with c1 c2 c3
      · exfalso
        apply hk
        apply Fin.ext
        rw [c3, c1.2.2.2]
      all_goals rfl
  · simp only [hi, false_and, ite_false]
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun x1 _ =>
      Finset.sum_eq_zero fun x2 _ => ?_
    split_ifs with c1 c2
    · exfalso
      apply hi
      rw [c2]
      exact c1.1
    all_goals rfl

open Classical in
/-- **The boundary of the axial rectangle is the loop of the two rows `j₀` and `j₀ + k`.** -/
theorem boundary_rectAx_eq_cLoop (R k j₀ : ℕ) (hjk : j₀ + k ≤ B) (k₀ : Fin (C + 1)) :
    Z2Gauge.boundary (ainc A B C) (rectAx A B C R k j₀ k₀) =
      cLoop A B C R k₀ ⟨j₀, by omega⟩ ⟨j₀ + k, by omega⟩ := by
  funext l
  rcases l with ⟨i', j', k'⟩ | z
  · rw [boundary_rectAx_inl]
    simp only [cLoop, rowInd, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega) | decide
  · unfold Z2Gauge.boundary
    rw [Finset.sum_eq_zero]
    · simp [cLoop, rowInd]
    · intro p hp
      obtain ⟨i, j, k'', rfl, -⟩ := (mem_rectAx A B C).mp hp
      simp [ainc, aemb, cinc]

end AreaBound
