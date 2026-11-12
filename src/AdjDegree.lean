/-
Copyright (c) 2026 Eduardo Nava Hernandez. All rights reserved.
Released under the NRS license (see LICENSE).
-/
import AxialBox
import AxialSeeds

/-!
# The adjacency degree of the plaquettes of the cubic box is at most `12`

A plaquette of the box lies on at most four links, and a link lies on at most four plaquettes;
a plaquette is adjacent to the other plaquettes of its links, so to at most `4 · (4 - 1) = 12`.

## Main results

- `AreaBound.card_links_le` : a plaquette lies on at most `4` links.
- `AreaBound.card_plaqs_le` : a link lies on at most `4` plaquettes.
- `AreaBound.adj_degree_le_twelve` : at most `12` plaquettes are adjacent to a given one.
-/

open Finset

namespace AreaBound

variable {a b c : ℕ}

/-- Two values of the second coordinate. -/
lemma card_le_two₂ (T : Finset (Fin a × Fin b × Fin c)) (x z m₁ m₂ : ℕ)
    (h : ∀ q ∈ T, q.1.val = x ∧ q.2.2.val = z ∧ (q.2.1.val = m₁ ∨ q.2.1.val = m₂)) :
    T.card ≤ 2 := by
  classical
  refine (Finset.card_le_card_of_injOn (fun q => q.2.1.val) (t := ({m₁, m₂} : Finset ℕ))
    (fun q hq => by simpa using (h q hq).2.2) ?_).trans (Finset.card_le_two)
  intro q hq q' hq' hqq
  have h1 := h q hq
  have h2 := h q' hq'
  obtain ⟨q1, q2, q3⟩ := q
  obtain ⟨r1, r2, r3⟩ := q'
  simp only at h1 h2 hqq
  have e1 : q1 = r1 := Fin.ext (by omega)
  have e2 : q2 = r2 := Fin.ext hqq
  have e3 : q3 = r3 := Fin.ext (by omega)
  rw [e1, e2, e3]

/-- Two values of the first coordinate. -/
lemma card_le_two₁ (T : Finset (Fin a × Fin b × Fin c)) (y z m₁ m₂ : ℕ)
    (h : ∀ q ∈ T, q.2.1.val = y ∧ q.2.2.val = z ∧ (q.1.val = m₁ ∨ q.1.val = m₂)) :
    T.card ≤ 2 := by
  classical
  refine (Finset.card_le_card_of_injOn (fun q => q.1.val) (t := ({m₁, m₂} : Finset ℕ))
    (fun q hq => by simpa using (h q hq).2.2) ?_).trans (Finset.card_le_two)
  intro q hq q' hq' hqq
  have h1 := h q hq
  have h2 := h q' hq'
  obtain ⟨q1, q2, q3⟩ := q
  obtain ⟨r1, r2, r3⟩ := q'
  simp only at h1 h2 hqq
  have e1 : q1 = r1 := Fin.ext hqq
  have e2 : q2 = r2 := Fin.ext (by omega)
  have e3 : q3 = r3 := Fin.ext (by omega)
  rw [e1, e2, e3]

/-- Two values of the third coordinate. -/
lemma card_le_two₃ (T : Finset (Fin a × Fin b × Fin c)) (x y m₁ m₂ : ℕ)
    (h : ∀ q ∈ T, q.1.val = x ∧ q.2.1.val = y ∧ (q.2.2.val = m₁ ∨ q.2.2.val = m₂)) :
    T.card ≤ 2 := by
  classical
  refine (Finset.card_le_card_of_injOn (fun q => q.2.2.val) (t := ({m₁, m₂} : Finset ℕ))
    (fun q hq => by simpa using (h q hq).2.2) ?_).trans (Finset.card_le_two)
  intro q hq q' hq' hqq
  have h1 := h q hq
  have h2 := h q' hq'
  obtain ⟨q1, q2, q3⟩ := q
  obtain ⟨r1, r2, r3⟩ := q'
  simp only at h1 h2 hqq
  have e1 : q1 = r1 := Fin.ext (by omega)
  have e2 : q2 = r2 := Fin.ext (by omega)
  have e3 : q3 = r3 := Fin.ext hqq
  rw [e1, e2, e3]


lemma card_filter_sum3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (P : α ⊕ (β ⊕ γ) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      (Finset.univ.filter fun x => P (.inl x)).card +
        (Finset.univ.filter fun x => P (.inr (.inl x))).card +
          (Finset.univ.filter fun x => P (.inr (.inr x))).card := by
  simp only [Finset.card_filter, Fintype.sum_sum_type]
  ring

lemma card_filter_eq_zero {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P]
    (h : ∀ x, ¬ P x) : (Finset.univ.filter P).card = 0 :=
  Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun x _ => h x)

local macro "inc_omega" : tactic =>
  `(tactic| (rintro ⟨q1, q2, q3⟩ hq
             replace hq := (Finset.mem_filter.mp hq).2
             simp only [cinc] at hq
             split_ifs at hq <;> simp only <;> first | omega | exact absurd rfl hq))

open Classical in
/-- **A plaquette lies on at most four links.** -/
theorem card_links_le (A B C : ℕ) (p : CPlaq A B C) :
    (Finset.univ.filter fun l : CLink A B C => cinc A B C p l ≠ 0).card ≤ 4 := by
  rw [card_filter_sum3]
  rcases p with ⟨i, j, k⟩ | ⟨i, j, k⟩ | ⟨i, j, k⟩
  · have hx := card_le_two₂ (Finset.univ.filter fun l : Fin A × Fin (B + 1) × Fin (C + 1) =>
      cinc A B C (.inl (i, j, k)) (.inl l) ≠ 0) i.val k.val j.val (j.val + 1) (by inc_omega)
    have hy := card_le_two₁ (Finset.univ.filter fun l : Fin (A + 1) × Fin B × Fin (C + 1) =>
      cinc A B C (.inl (i, j, k)) (.inr (.inl l)) ≠ 0) j.val k.val i.val (i.val + 1) (by inc_omega)
    have hz := card_filter_eq_zero (fun l : Fin (A + 1) × Fin (B + 1) × Fin C =>
      cinc A B C (.inl (i, j, k)) (.inr (.inr l)) ≠ 0) (by simp [cinc])
    omega
  · have hx := card_le_two₃ (Finset.univ.filter fun l : Fin A × Fin (B + 1) × Fin (C + 1) =>
      cinc A B C (.inr (.inl (i, j, k))) (.inl l) ≠ 0) i.val j.val k.val (k.val + 1) (by inc_omega)
    have hy := card_filter_eq_zero (fun l : Fin (A + 1) × Fin B × Fin (C + 1) =>
      cinc A B C (.inr (.inl (i, j, k))) (.inr (.inl l)) ≠ 0) (by simp [cinc])
    have hz := card_le_two₁ (Finset.univ.filter fun l : Fin (A + 1) × Fin (B + 1) × Fin C =>
      cinc A B C (.inr (.inl (i, j, k))) (.inr (.inr l)) ≠ 0) j.val k.val i.val (i.val + 1)
      (by inc_omega)
    omega
  · have hx := card_filter_eq_zero (fun l : Fin A × Fin (B + 1) × Fin (C + 1) =>
      cinc A B C (.inr (.inr (i, j, k))) (.inl l) ≠ 0) (by simp [cinc])
    have hy := card_le_two₃ (Finset.univ.filter fun l : Fin (A + 1) × Fin B × Fin (C + 1) =>
      cinc A B C (.inr (.inr (i, j, k))) (.inr (.inl l)) ≠ 0) i.val j.val k.val (k.val + 1)
      (by inc_omega)
    have hz := card_le_two₂ (Finset.univ.filter fun l : Fin (A + 1) × Fin (B + 1) × Fin C =>
      cinc A B C (.inr (.inr (i, j, k))) (.inr (.inr l)) ≠ 0) i.val k.val j.val (j.val + 1)
      (by inc_omega)
    omega

open Classical in
/-- **A link lies on at most four plaquettes.** -/
theorem card_plaqs_le (A B C : ℕ) (l : CLink A B C) :
    (Finset.univ.filter fun p : CPlaq A B C => cinc A B C p l ≠ 0).card ≤ 4 := by
  rw [card_filter_sum3]
  rcases l with ⟨i, j, k⟩ | ⟨i, j, k⟩ | ⟨i, j, k⟩
  · have hx := card_le_two₂ (Finset.univ.filter fun p : Fin A × Fin B × Fin (C + 1) =>
      cinc A B C (.inl p) (.inl (i, j, k)) ≠ 0) i.val k.val j.val (j.val - 1) (by inc_omega)
    have hy := card_le_two₃ (Finset.univ.filter fun p : Fin A × Fin (B + 1) × Fin C =>
      cinc A B C (.inr (.inl p)) (.inl (i, j, k)) ≠ 0) i.val j.val k.val (k.val - 1)
      (by inc_omega)
    have hz := card_filter_eq_zero (fun p : Fin (A + 1) × Fin B × Fin C =>
      cinc A B C (.inr (.inr p)) (.inl (i, j, k)) ≠ 0) (by simp [cinc])
    omega
  · have hx := card_le_two₁ (Finset.univ.filter fun p : Fin A × Fin B × Fin (C + 1) =>
      cinc A B C (.inl p) (.inr (.inl (i, j, k))) ≠ 0) j.val k.val i.val (i.val - 1) (by inc_omega)
    have hy := card_filter_eq_zero (fun p : Fin A × Fin (B + 1) × Fin C =>
      cinc A B C (.inr (.inl p)) (.inr (.inl (i, j, k))) ≠ 0) (by simp [cinc])
    have hz := card_le_two₃ (Finset.univ.filter fun p : Fin (A + 1) × Fin B × Fin C =>
      cinc A B C (.inr (.inr p)) (.inr (.inl (i, j, k))) ≠ 0) i.val j.val k.val (k.val - 1)
      (by inc_omega)
    omega
  · have hx := card_filter_eq_zero (fun p : Fin A × Fin B × Fin (C + 1) =>
      cinc A B C (.inl p) (.inr (.inr (i, j, k))) ≠ 0) (by simp [cinc])
    have hy := card_le_two₁ (Finset.univ.filter fun p : Fin A × Fin (B + 1) × Fin C =>
      cinc A B C (.inr (.inl p)) (.inr (.inr (i, j, k))) ≠ 0) j.val k.val i.val (i.val - 1)
      (by inc_omega)
    have hz := card_le_two₂ (Finset.univ.filter fun p : Fin (A + 1) × Fin B × Fin C =>
      cinc A B C (.inr (.inr p)) (.inr (.inr (i, j, k))) ≠ 0) i.val k.val j.val (j.val - 1)
      (by inc_omega)
    omega

open Classical in
/-- **The adjacency degree of a plaquette of the box is at most `12`.** -/
theorem adj_degree_le_twelve (A B C : ℕ) (p : CPlaq A B C) :
    (Finset.univ.filter (Z2Gauge.Adj (cinc A B C) p)).card ≤ 12 := by
  set Lp : Finset (CLink A B C) := Finset.univ.filter fun l => cinc A B C p l ≠ 0 with hLp
  have hsub : (Finset.univ.filter (Z2Gauge.Adj (cinc A B C) p)) ⊆
      Lp.biUnion fun l => (Finset.univ.filter fun q : CPlaq A B C => cinc A B C q l ≠ 0).erase p := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    obtain ⟨hne, l, h1, h2⟩ := hq
    refine Finset.mem_biUnion.mpr ⟨l, ?_, ?_⟩
    · simp [hLp, h1]
    · exact Finset.mem_erase.mpr ⟨Ne.symm hne, by simp [h2]⟩
  calc _ ≤ (Lp.biUnion fun l =>
        (Finset.univ.filter fun q : CPlaq A B C => cinc A B C q l ≠ 0).erase p).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ l ∈ Lp, ((Finset.univ.filter fun q : CPlaq A B C => cinc A B C q l ≠ 0).erase p).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ l ∈ Lp, 3 := by
        refine Finset.sum_le_sum fun l hl => ?_
        have hp : p ∈ (Finset.univ.filter fun q : CPlaq A B C => cinc A B C q l ≠ 0) := by
          simpa [hLp] using hl
        rw [Finset.card_erase_of_mem hp]
        have := card_plaqs_le A B C l
        omega
    _ = Lp.card * 3 := by simp
    _ ≤ 12 := by
        have : Lp.card ≤ 4 := card_links_le A B C p
        omega

end AreaBound
