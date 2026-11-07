/-
Copyright (c) 2026 Eduardo Nava Hernandez. All rights reserved.
Released under the NRS license (see LICENSE).
-/
import AxialBox
import PolymerBound

/-!
# The seeds of the axial rectangle: at most `8 R`, independent of the time extent

The boundary of the rectangle `rectAx R k j₀ k₀` of `xy` plaquettes in the axial incidence `ainc`
is supported on the `x` links of the two rows `j₀` and `j₀ + k` (the interior links lie on two
plaquettes of the rectangle, and the sum is zero mod 2). An `x` link lies on at most four
plaquettes (two `xy`, two `xz`). Hence the number of seeds of the boundary is at most `2 R · 4`.

## Main results

- `AreaBound.boundary_rectAx_ne_zero` : a link of non-zero boundary is an `x` link of the row `j₀`
  or `j₀ + k`, at height `k₀`, in a column `i < R`.
- `AreaBound.seeds_rectAx_card_le` : the number of seeds is at most `8 * R`.

## Scope

Counting for the model of Wilson in axial gauge. The bound does not depend on `k` and `j₀`.
-/

open Finset

namespace AreaBound

variable (A B C : ℕ)

open Classical in
/-- Membership in the rectangle. -/
lemma mem_rectAx {R k j₀ : ℕ} {k₀ : Fin (C + 1)} {p : CPlaq A B C} :
    p ∈ rectAx A B C R k j₀ k₀ ↔ ∃ i : Fin A, ∃ j : Fin B, ∃ k' : Fin (C + 1),
      p = .inl (i, j, k') ∧ i.val < R ∧ j₀ ≤ j.val ∧ j.val < j₀ + k ∧ k' = k₀ := by
  unfold rectAx
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨-, h⟩
    rcases p with ⟨i, j, k'⟩ | _ | _
    · exact ⟨i, j, k', rfl, h⟩
    · exact h.elim
    · exact h.elim
  · rintro ⟨i, j, k', rfl, h⟩
    exact ⟨Finset.mem_univ _, h⟩

/-- A link of non-zero boundary is an `x` link of one of the two rows, at height `k₀`, in a column
`i < R`. -/
theorem boundary_rectAx_ne_zero (R k j₀ : ℕ) (hjk : j₀ + k ≤ B) (k₀ : Fin (C + 1))
    (l : ALink A B C)
    (h : Z2Gauge.boundary (ainc A B C) (rectAx A B C R k j₀ k₀) l ≠ 0) :
    ∃ i : Fin A, ∃ j : Fin (B + 1), ∃ k' : Fin (C + 1), l = .inl (i, j, k') ∧ i.val < R ∧
      k' = k₀ ∧ (j.val = j₀ ∨ j.val = j₀ + k) := by
  classical
  unfold Z2Gauge.boundary at h
  rcases l with ⟨i', j', k'⟩ | z
  · by_contra hcon
    refine h ?_
    by_cases hin : i'.val < R ∧ k' = k₀ ∧ j₀ < j'.val ∧ j'.val < j₀ + k
    · -- interior link: two plaquettes of the rectangle, the sum is zero mod 2
      obtain ⟨hi, hk, hj1, hj2⟩ := hin
      have hjB : j'.val < B := by omega
      let p₁ : CPlaq A B C := .inl (i', ⟨j'.val - 1, by omega⟩, k')
      let p₂ : CPlaq A B C := .inl (i', ⟨j'.val, hjB⟩, k')
      have hp₁ : p₁ ∈ rectAx A B C R k j₀ k₀ :=
        (mem_rectAx A B C).mpr ⟨i', ⟨j'.val - 1, by omega⟩, k', rfl, hi, by simp; omega,
          by simp; omega, hk⟩
      have hp₂ : p₂ ∈ rectAx A B C R k j₀ k₀ :=
        (mem_rectAx A B C).mpr ⟨i', ⟨j'.val, hjB⟩, k', rfl, hi, by simp; omega,
          by simp; omega, hk⟩
      have hterm : ∀ p ∈ rectAx A B C R k j₀ k₀, ainc A B C p (.inl (i', j', k')) =
          (if p = p₁ then 1 else 0) + (if p = p₂ then 1 else 0) := by
        intro p hp
        obtain ⟨i, j, k'', rfl, hi', hj1', hj2', hk''⟩ := (mem_rectAx A B C).mp hp
        simp only [ainc, aemb, cinc, p₁, p₂, Sum.inl.injEq, Prod.mk.injEq, Fin.ext_iff]
        split_ifs <;> first | rfl | (exfalso; omega)
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq',
        Finset.sum_ite_eq', if_pos hp₁, if_pos hp₂]
      decide
    · refine Finset.sum_eq_zero fun p hp => ?_
      obtain ⟨i, j, k'', rfl, hi', hj1', hj2', hk''⟩ := (mem_rectAx A B C).mp hp
      simp only [ainc, aemb, cinc]
      rw [if_neg]
      intro ⟨h1, h2, h3⟩
      apply hcon
      refine ⟨i', j', k', rfl, by omega, ?_, ?_⟩
      · apply Fin.ext; omega
      · omega
  · exfalso
    refine h (Finset.sum_eq_zero fun p hp => ?_)
    obtain ⟨i, j, k'', rfl, -⟩ := (mem_rectAx A B C).mp hp
    simp [ainc, aemb, cinc]


omit A B C in
lemma card_filter_two (n m : ℕ) :
    (Finset.univ.filter fun j : Fin n => j.val = m ∨ j.val + 1 = m).card ≤ 2 := by
  have h1 : (Finset.univ.filter fun j : Fin n => j.val = m).card ≤ 1 :=
    Finset.card_le_one.mpr fun a ha b hb => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact Fin.ext (by omega)
  have h2 : (Finset.univ.filter fun j : Fin n => j.val + 1 = m).card ≤ 1 :=
    Finset.card_le_one.mpr fun a ha b hb => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact Fin.ext (by omega)
  calc _ ≤ ((Finset.univ.filter fun j : Fin n => j.val = m) ∪
        (Finset.univ.filter fun j : Fin n => j.val + 1 = m)).card := by
          apply Finset.card_le_card
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hj ⊢
          exact hj
    _ ≤ 2 := (Finset.card_union_le _ _).trans (by omega)

open Classical in
/-- An `x` link lies on at most four plaquettes of the axial box. -/
lemma card_touching_le (i : Fin A) (j : Fin (B + 1)) (k : Fin (C + 1)) :
    (Finset.univ.filter fun p : CPlaq A B C => ainc A B C p (.inl (i, j, k)) ≠ 0).card ≤ 4 := by
  set Txy : Finset (Fin A × Fin B × Fin (C + 1)) := Finset.univ.filter fun q =>
    q.1 = i ∧ q.2.2 = k ∧ (q.2.1.val = j.val ∨ q.2.1.val + 1 = j.val) with hTxy
  set Txz : Finset (Fin A × Fin (B + 1) × Fin C) := Finset.univ.filter fun q =>
    q.1 = i ∧ q.2.1 = j ∧ (q.2.2.val = k.val ∨ q.2.2.val + 1 = k.val) with hTxz
  have h1 : Txy.card ≤ 2 := by
    refine (Finset.card_le_card_of_injOn (fun q => q.2.1) ?_ ?_).trans (card_filter_two B j.val)
    · intro q hq
      simp only [hTxy, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hq
      simpa using hq.2.2
    · intro q hq q' hq' hqq
      simp only [hTxy, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hq hq'
      obtain ⟨a, b, c⟩ := q
      obtain ⟨a', b', c'⟩ := q'
      simp only at hqq hq hq'
      rw [hq.1, hq'.1, hq.2.1, hq'.2.1, hqq]
  have h2 : Txz.card ≤ 2 := by
    refine (Finset.card_le_card_of_injOn (fun q => q.2.2) ?_ ?_).trans (card_filter_two C k.val)
    · intro q hq
      simp only [hTxz, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hq
      simpa using hq.2.2
    · intro q hq q' hq' hqq
      simp only [hTxz, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hq hq'
      obtain ⟨a, b, c⟩ := q
      obtain ⟨a', b', c'⟩ := q'
      simp only at hqq hq hq'
      rw [hq.1, hq'.1, hq.2.1, hq'.2.1, hqq]
  have hsub : (Finset.univ.filter fun p : CPlaq A B C => ainc A B C p (.inl (i, j, k)) ≠ 0) ⊆
      Txy.image Sum.inl ∪ Txz.image (fun q => Sum.inr (Sum.inl q)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [Finset.mem_union]
    rcases p with ⟨i', j', k'⟩ | ⟨i', j', k'⟩ | ⟨i', j', k'⟩
    · left
      refine Finset.mem_image.mpr ⟨(i', j', k'), ?_, rfl⟩
      simp only [ainc, aemb, cinc] at hp
      split_ifs at hp with hc
      · simp only [hTxy, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨Fin.ext hc.1.symm, Fin.ext hc.2.1.symm, ?_⟩
        omega
      · exact absurd rfl hp
    · right
      refine Finset.mem_image.mpr ⟨(i', j', k'), ?_, rfl⟩
      simp only [ainc, aemb, cinc] at hp
      split_ifs at hp with hc
      · simp only [hTxz, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨Fin.ext hc.1.symm, Fin.ext hc.2.1.symm, ?_⟩
        omega
      · exact absurd rfl hp
    · exact absurd (by simp [ainc, aemb, cinc]) hp
  calc _ ≤ (Txy.image Sum.inl ∪ Txz.image (fun q => Sum.inr (Sum.inl q))).card :=
        Finset.card_le_card hsub
    _ ≤ (Txy.image Sum.inl).card + (Txz.image (fun q => Sum.inr (Sum.inl q))).card :=
        Finset.card_union_le _ _
    _ ≤ Txy.card + Txz.card := add_le_add Finset.card_image_le Finset.card_image_le
    _ ≤ 4 := by omega


open Classical in
/-- The `x` links of the row at time `m`, height `k₀`, in the columns `i < R`. -/
noncomputable def rowX (R m : ℕ) (k₀ : Fin (C + 1)) : Finset (Fin A × Fin (B + 1) × Fin (C + 1)) :=
  Finset.univ.filter fun x => x.1.val < R ∧ x.2.2 = k₀ ∧ x.2.1.val = m

lemma card_rowX_le (R m : ℕ) (k₀ : Fin (C + 1)) : (rowX A B C R m k₀).card ≤ R := by
  classical
  have h : (rowX A B C R m k₀).card ≤ (Finset.univ.filter fun i : Fin A => i.val < R).card := by
    refine Finset.card_le_card_of_injOn (fun x => x.1) ?_ ?_
    · intro x hx
      simp only [rowX, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx
      simpa using hx.1
    · intro x hx y hy hxy
      simp only [rowX, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx hy
      obtain ⟨a, b, c⟩ := x
      obtain ⟨a', b', c'⟩ := y
      simp only at hxy hx hy
      rw [hxy, hx.2.1, hy.2.1, Fin.ext (hx.2.2.trans hy.2.2.symm)]
  rw [Fin.card_filter_val_lt] at h
  exact h.trans (min_le_right _ _)

open Classical in
/-- **The number of seeds of the axial rectangle is at most `8 R`**, whatever the time extent. -/
theorem seeds_rectAx_card_le (R k j₀ : ℕ) (hjk : j₀ + k ≤ B) (k₀ : Fin (C + 1)) :
    (Finset.univ.filter (Z2Gauge.IsSeed (ainc A B C)
      (Z2Gauge.boundary (ainc A B C) (rectAx A B C R k j₀ k₀)))).card ≤ 8 * R := by
  set L : Finset (ALink A B C) :=
    (rowX A B C R j₀ k₀ ∪ rowX A B C R (j₀ + k) k₀).image Sum.inl with hL
  have hsub : (Finset.univ.filter (Z2Gauge.IsSeed (ainc A B C)
      (Z2Gauge.boundary (ainc A B C) (rectAx A B C R k j₀ k₀)))) ⊆
      L.biUnion fun l => Finset.univ.filter fun p : CPlaq A B C => ainc A B C p l ≠ 0 := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Z2Gauge.IsSeed] at hp
    obtain ⟨l, hl, hpl⟩ := hp
    obtain ⟨i, j, k', rfl, hi, hk, hj⟩ := boundary_rectAx_ne_zero A B C R k j₀ hjk k₀ l hl
    refine Finset.mem_biUnion.mpr ⟨.inl (i, j, k'), ?_, by simpa using hpl⟩
    rw [hL, Finset.mem_image]
    refine ⟨(i, j, k'), ?_, rfl⟩
    simp only [rowX, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hj with hj | hj
    · exact Or.inl ⟨hi, hk, hj⟩
    · exact Or.inr ⟨hi, hk, hj⟩
  have hL2 : L.card ≤ 2 * R := by
    refine Finset.card_image_le.trans ((Finset.card_union_le _ _).trans ?_)
    have := card_rowX_le A B C R j₀ k₀
    have := card_rowX_le A B C R (j₀ + k) k₀
    omega
  calc _ ≤ (L.biUnion fun l => Finset.univ.filter fun p : CPlaq A B C => ainc A B C p l ≠ 0).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ l ∈ L, (Finset.univ.filter fun p : CPlaq A B C => ainc A B C p l ≠ 0).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ l ∈ L, 4 := by
        refine Finset.sum_le_sum fun l hl => ?_
        obtain ⟨⟨i, j, k'⟩, -, rfl⟩ := Finset.mem_image.mp hl
        exact card_touching_le A B C i j k'
    _ = L.card * 4 := by simp
    _ ≤ 8 * R := by omega

end AreaBound
