/-
Copyright (c) 2026 Eduardo Nava Hernandez. All rights reserved.
Released under the NRS license (see LICENSE).
-/
import AxialBox
import Z2Transfer
import SlabChain
import Z2AreaLaw

/-!
# The box in axial gauge, cut in time slices

The links of the axial box `ALink A B C` are the pairs (time, link of one slice): the equivalence
`AreaBound.sliceEquiv` identifies `ALink A B C` with `Fin (B + 1) × LS A C`. In these terms the
weight of a configuration is the product of a slice weight `uW` over the `B + 1` slices and the
kernel `Z2Transfer.kern` between consecutive slices, so the partition function is a `SlabChain`.

## Main results

- `AreaBound.weight_slice` : the weight of `ainc` factors over slices.
- `AreaBound.partition_slice` : `partition ainc β = chainSum (K β) (uW β) B`.
- `AreaBound.spin_loop_slice` : the Wilson loop of two rows of `x` links is a product of two
  characters of slices.

## Scope

The slicing of the model of Wilson in axial gauge, as a computation. Nothing is said here on the
transfer matrix spectrum.
-/

open Finset

namespace AreaBound

variable (A B C : ℕ)

/-- The links of one time slice: `x` links `(i, k)` and `z` links `(i, k)`. -/
abbrev LS := (Fin A × Fin (C + 1)) ⊕ (Fin (A + 1) × Fin C)

/-- A link of the axial box is a pair (time, link of a slice). -/
def sliceEquiv : ALink A B C ≃ Fin (B + 1) × LS A C where
  toFun
    | .inl (i, j, k) => (j, .inl (i, k))
    | .inr (i, j, k) => (j, .inr (i, k))
  invFun
    | (j, .inl (i, k)) => .inl (i, j, k)
    | (j, .inr (i, k)) => .inr (i, j, k)
  left_inv := by rintro (⟨i, j, k⟩ | ⟨i, j, k⟩) <;> rfl
  right_inv := by rintro ⟨j, (⟨i, k⟩ | ⟨i, k⟩)⟩ <;> rfl

/-- The slice at time `j` of a configuration. -/
def slice (σ : ALink A B C → ZMod 2) (j : Fin (B + 1)) : LS A C → ZMod 2 :=
  fun l => σ ((sliceEquiv A B C).symm (j, l))


/-- A plaquette variable, if the incidence is the indicator of two links. -/
lemma plaq_of_two {P : Type*} (inc : P → ALink A B C → ZMod 2) (p : P) (l₁ l₂ : ALink A B C)
    (h : ∀ l, inc p l = (if l = l₁ then 1 else 0) + (if l = l₂ then 1 else 0))
    (σ : ALink A B C → ZMod 2) :
    Z2Gauge.plaq inc σ p = σ l₁ + σ l₂ := by
  unfold Z2Gauge.plaq
  simp [h, add_mul, Finset.sum_add_distrib, ite_mul]

lemma plaq_xy (σ : ALink A B C → ZMod 2) (i : Fin A) (j : Fin B) (k : Fin (C + 1)) :
    Z2Gauge.plaq (ainc A B C) σ (.inl (i, j, k)) =
      slice A B C σ j.castSucc (.inl (i, k)) + slice A B C σ j.succ (.inl (i, k)) := by
  refine plaq_of_two A B C _ _ (.inl (i, j.castSucc, k)) (.inl (i, j.succ, k)) ?_ σ
  rintro (⟨i', j', k'⟩ | ⟨i', j', k'⟩)
  · simp only [ainc, aemb, cinc, Fin.ext_iff, Sum.inl.injEq, Prod.mk.injEq, Fin.val_succ,
      Fin.val_castSucc]
    split_ifs <;> first | rfl | (exfalso; omega)
  · simp [ainc, aemb, cinc]


lemma plaq_yz (σ : ALink A B C → ZMod 2) (i : Fin (A + 1)) (j : Fin B) (k : Fin C) :
    Z2Gauge.plaq (ainc A B C) σ (.inr (.inr (i, j, k))) =
      slice A B C σ j.castSucc (.inr (i, k)) + slice A B C σ j.succ (.inr (i, k)) := by
  refine plaq_of_two A B C _ _ (.inr (i, j.castSucc, k)) (.inr (i, j.succ, k)) ?_ σ
  rintro (⟨i', j', k'⟩ | ⟨i', j', k'⟩)
  · simp [ainc, aemb, cinc]
  · simp only [ainc, aemb, cinc, Fin.ext_iff, Sum.inr.injEq, Prod.mk.injEq, Fin.val_succ,
      Fin.val_castSucc]
    split_ifs <;> first | rfl | (exfalso; omega)

lemma plaq_of_four {P : Type*} (inc : P → ALink A B C → ZMod 2) (p : P)
    (l₁ l₂ l₃ l₄ : ALink A B C)
    (h : ∀ l, inc p l = (if l = l₁ then 1 else 0) + (if l = l₂ then 1 else 0) +
      (if l = l₃ then 1 else 0) + (if l = l₄ then 1 else 0))
    (σ : ALink A B C → ZMod 2) :
    Z2Gauge.plaq inc σ p = σ l₁ + σ l₂ + σ l₃ + σ l₄ := by
  unfold Z2Gauge.plaq
  simp [h, add_mul, Finset.sum_add_distrib, ite_mul]

lemma plaq_xz (σ : ALink A B C → ZMod 2) (i : Fin A) (j : Fin (B + 1)) (k : Fin C) :
    Z2Gauge.plaq (ainc A B C) σ (.inr (.inl (i, j, k))) =
      slice A B C σ j (.inl (i, k.castSucc)) + slice A B C σ j (.inl (i, k.succ)) +
        slice A B C σ j (.inr (i.castSucc, k)) + slice A B C σ j (.inr (i.succ, k)) := by
  refine plaq_of_four A B C _ _ (.inl (i, j, k.castSucc)) (.inl (i, j, k.succ))
    (.inr (i.castSucc, j, k)) (.inr (i.succ, j, k)) ?_ σ
  rintro (⟨i', j', k'⟩ | ⟨i', j', k'⟩)
  · simp only [ainc, aemb, cinc, Fin.ext_iff, Sum.inl.injEq, reduceCtorEq,
      Prod.mk.injEq, Fin.val_succ, Fin.val_castSucc, ite_false, add_zero]
    split_ifs <;> first | rfl | (exfalso; omega)
  · simp only [ainc, aemb, cinc, Fin.ext_iff, Sum.inr.injEq, reduceCtorEq,
      Prod.mk.injEq, Fin.val_succ, Fin.val_castSucc, ite_false, zero_add]
    split_ifs <;> first | rfl | (exfalso; omega)


/-- The weight of the space-like plaquettes of one slice. -/
noncomputable def uW (β : ℝ) (s : LS A C → ZMod 2) : ℝ :=
  ∏ x : Fin A × Fin C, Real.exp (β * Z2Gauge.spin
    (s (.inl (x.1, x.2.castSucc)) + s (.inl (x.1, x.2.succ)) +
      s (.inr (x.1.castSucc, x.2)) + s (.inr (x.1.succ, x.2))))

lemma sgn_eq_spin (a : ZMod 2) : Z2Transfer.sgn a = Z2Gauge.spin a := rfl

/-- The kernel between two slices, as a product over the `x` and the `z` links. -/
lemma kern_eq (β : ℝ) (s t : LS A C → ZMod 2) :
    Z2Transfer.kern β s t =
      (∏ x : Fin A × Fin (C + 1), Real.exp (β * (Z2Gauge.spin (s (.inl x)) *
          Z2Gauge.spin (t (.inl x))))) *
        ∏ x : Fin (A + 1) × Fin C, Real.exp (β * (Z2Gauge.spin (s (.inr x)) *
          Z2Gauge.spin (t (.inr x)))) := by
  unfold Z2Transfer.kern
  rw [Fintype.prod_sum_type]
  simp only [sgn_eq_spin]

/-- **The weight of the axial box factors over the time slices.** -/
theorem weight_slice (β : ℝ) (σ : ALink A B C → ZMod 2) :
    Z2Gauge.weight (ainc A B C) β σ =
      (∏ j : Fin (B + 1), uW A C β (slice A B C σ j)) *
        ∏ j : Fin B, Z2Transfer.kern β (slice A B C σ j.castSucc) (slice A B C σ j.succ) := by
  unfold Z2Gauge.weight
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Fintype.prod_prod_type, plaq_xy, plaq_yz, plaq_xz, Z2Gauge.spin_add, kern_eq,
    Finset.prod_mul_distrib, uW]
  rw [mul_comm (∏ x, ∏ x_1, ∏ x_2, _) (_ * _), mul_assoc]
  congr 1
  · exact Finset.prod_comm
  · rw [mul_comm]
    congr 1
    · exact Finset.prod_comm
    · exact Finset.prod_comm


/-- The configurations of the axial box are the families of slices. -/
def sliceCfg : (ALink A B C → ZMod 2) ≃ (Fin (B + 1) → LS A C → ZMod 2) :=
  (Equiv.arrowCongr (sliceEquiv A B C) (Equiv.refl _)).trans
    (Equiv.curry (Fin (B + 1)) (LS A C) (ZMod 2))

lemma sliceCfg_apply (σ : ALink A B C → ZMod 2) (j : Fin (B + 1)) :
    sliceCfg A B C σ j = slice A B C σ j := by
  funext l
  simp [sliceCfg, slice, Equiv.arrowCongr]

/-- **The partition function of the axial box is a chain of slices.** -/
theorem partition_slice (β : ℝ) :
    Z2Gauge.partition (ainc A B C) β =
      SlabChain.chainSum (Z2Transfer.K β) (uW A C β) B := by
  unfold Z2Gauge.partition SlabChain.chainSum
  rw [← (sliceCfg A B C).sum_comp]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [weight_slice]
  simp only [sliceCfg_apply, Z2Transfer.K]


open Classical in
/-- The indicator of the row of `x` links at time `j`, height `k₀`, columns `i < R`. -/
noncomputable def rowInd (R : ℕ) (k₀ : Fin (C + 1)) (j : Fin (B + 1)) : ALink A B C → ZMod 2
  | .inl (i, j', k) => if i.val < R ∧ k = k₀ ∧ j' = j then 1 else 0
  | .inr _ => 0

/-- The Wilson loop in axial gauge: two rows of `x` links, at the times `j₀` and `j₁`, at the height
`k₀`, in the columns `i < R`. -/
noncomputable def cLoop (R : ℕ) (k₀ : Fin (C + 1)) (j₀ j₁ : Fin (B + 1)) :
    ALink A B C → ZMod 2 :=
  fun l => rowInd A B C R k₀ j₀ l + rowInd A B C R k₀ j₁ l

open Classical in
/-- The character of a slice: the product of the `x` links of the row at height `k₀`, columns
`i < R`. -/
noncomputable def rowChar (R : ℕ) (k₀ : Fin (C + 1)) (s : LS A C → ZMod 2) : ℝ :=
  ∏ i ∈ (Finset.univ : Finset (Fin A)).filter (fun i => i.val < R),
    Z2Transfer.sgn (s (.inl (i, k₀)))

open Classical in
lemma rowInd_sum (R : ℕ) (k₀ : Fin (C + 1)) (j : Fin (B + 1)) (σ : ALink A B C → ZMod 2) :
    ∑ l, rowInd A B C R k₀ j l * σ l =
      ∑ i ∈ (Finset.univ : Finset (Fin A)).filter (fun i => i.val < R),
        slice A B C σ j (.inl (i, k₀)) := by
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type, rowInd, ite_and, ite_mul, one_mul, zero_mul,
    Finset.sum_const_zero, add_zero, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i.val < R
  · simp [h, slice, sliceEquiv, Finset.sum_ite_eq']
  · simp [h]

open Classical in
/-- **The Wilson loop of two rows is a product of two characters of slices.** -/
theorem spin_loop_slice (R : ℕ) (k₀ : Fin (C + 1)) (j₀ j₁ : Fin (B + 1))
    (σ : ALink A B C → ZMod 2) :
    Z2Gauge.spin (∑ l, cLoop A B C R k₀ j₀ j₁ l * σ l) =
      rowChar A C R k₀ (slice A B C σ j₀) * rowChar A C R k₀ (slice A B C σ j₁) := by
  have h : ∑ l, cLoop A B C R k₀ j₀ j₁ l * σ l =
      ∑ l, rowInd A B C R k₀ j₀ l * σ l + ∑ l, rowInd A B C R k₀ j₁ l * σ l := by
    simp only [cLoop, add_mul, Finset.sum_add_distrib]
  rw [h, Z2Gauge.spin_add, rowInd_sum, rowInd_sum, Z2Gauge.spin_sum, Z2Gauge.spin_sum]
  rfl

/-- The numerator of the Wilson loop of two rows, as a sum over families of slices. -/
theorem numerator_slice (β : ℝ) (R : ℕ) (k₀ : Fin (C + 1)) (j₀ j₁ : Fin (B + 1)) :
    ∑ σ : ALink A B C → ZMod 2, Z2Gauge.weight (ainc A B C) β σ *
        Z2Gauge.spin (∑ l, cLoop A B C R k₀ j₀ j₁ l * σ l) =
      ∑ s : Fin (B + 1) → LS A C → ZMod 2, (∏ j, uW A C β (s j)) *
        (∏ j : Fin B, Z2Transfer.kern β (s j.castSucc) (s j.succ)) *
          (rowChar A C R k₀ (s j₀) * rowChar A C R k₀ (s j₁)) := by
  rw [← (sliceCfg A B C).sum_comp]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [weight_slice, spin_loop_slice]
  simp only [sliceCfg_apply]

end AreaBound
