/-
Copyright (c) 2026 Eduardo Nava Hernandez. All rights reserved.
Released under the NRS license (see LICENSE).
-/
import AxialBox

/-!
# The area bound for a loop in axial gauge

In axial gauge the loop of `R` columns and `k` time steps is the pair of rows of `x` links at the
times `j₀` and `j₀ + k`, and a surface with that boundary must contain at least `R · k`
plaquettes: projecting on the `x` links of the plane (forgetting the height) turns every `xz`
plaquette into zero (its two `x` links project to the same plane link) and every `yz` plaquette
into zero (no `x` links), and the `xy` plaquettes into the `1`-dimensional complex of each column,
which has no cycles.

## Main results

- `AreaBound.ax_proj` : the projection property of `ainc`.
- `AreaBound.ax_no_cycles` : the plane complex of a column has no cycles.
- `AreaBound.area_bound_rectAx` : `R * k ≤ |S|` for every `S` with the boundary of `rectAx`.
-/

open Finset

namespace AreaBound

variable (A B C : ℕ)

/-- The incidence of the plane plaquette `(i, j)` on the `x` links `(a, b)` of the plane. -/
def xinc : Fin A × Fin B → Fin A × Fin (B + 1) → ZMod 2 := fun q m =>
  if m.1.val = q.1.val ∧ (m.2.val = q.2.val ∨ m.2.val = q.2.val + 1) then 1 else 0

/-- The projection of the axial links on the `x` links of the plane: forget the height. -/
def axρ : ALink A B C → Fin A × Fin (B + 1) → ZMod 2
  | .inl (i, j, _), m => if i = m.1 ∧ j = m.2 then 1 else 0
  | .inr _, _ => 0

/-- **The projection property of `ainc`.** -/
theorem ax_proj (p : CPlaq A B C) (m : Fin A × Fin (B + 1)) :
    ∑ l, axρ A B C l m * ainc A B C p l = (pplaq A B C p).elim 0 (fun q => xinc A B q m) := by
  rcases p with ⟨i, j, k⟩ | ⟨i, j, k⟩ | ⟨i, j, k⟩ <;> rcases m with ⟨a, b⟩ <;>
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, axρ, ainc, aemb, cinc, pplaq, xinc] <;>
    simp only [mul_zero, Finset.sum_const_zero, add_zero, Option.elim_some, Option.elim_none] <;>
    simp [ite_and, Fin.val_inj, Finset.sum_ite_eq']
  · by_cases hia : i = a
    · subst hia
      simpa using sum_collapse (fun x : Fin (B + 1) => x.val = j.val ∨ x.val = j.val + 1) b
    · simp [hia, Ne.symm hia]
  · by_cases hia : i = a <;> by_cases hjb : j = b <;> simp [hia, hjb]
    exact card_two k

/-- The equation of the column complex at the plane link `(a, n)`: it involves `u (a, n)` and
`u (a, n - 1)`. -/
lemma ax_eval (u : Fin A × Fin B → ZMod 2) (a : Fin A) {n : ℕ} (hn : n < B) :
    ∑ q, u q * xinc A B q (a, ⟨n, by omega⟩) =
      u (a, ⟨n, hn⟩) + (if h : 0 < n then u (a, ⟨n - 1, by omega⟩) else 0) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · have hsplit : ∀ j : Fin B, u (a, j) * xinc A B (a, j) (a, ⟨n, by omega⟩) =
        (if j.val = n then u (a, j) else 0) + (if j.val + 1 = n then u (a, j) else 0) := by
      intro j
      unfold xinc
      by_cases h1 : j.val = n
      · have h2 : ¬ (j.val + 1 = n) := by omega
        simp [h1, h2]
      · by_cases h2 : j.val + 1 = n
        · simp [h1, h2]
        · have h3 : ¬ (n = j.val ∨ n = j.val + 1) := by omega
          simp [h1, h2, h3]
    rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single (⟨n, hn⟩ : Fin B)]
      · simp
      · intro j _ hj
        have : j.val ≠ n := fun h => hj (Fin.ext h)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · by_cases h : 0 < n
      · rw [dif_pos h, Finset.sum_eq_single (⟨n - 1, by omega⟩ : Fin B)]
        · have : (n - 1) + 1 = n := by omega
          simp [this]
        · intro j _ hj
          have : j.val + 1 ≠ n := fun h' => hj (Fin.ext (by show j.val = n - 1; omega))
          simp [this]
        · intro h'; exact absurd (Finset.mem_univ _) h'
      · rw [dif_neg h]
        refine Finset.sum_eq_zero fun j _ => ?_
        have : ¬ (j.val + 1 = n) := by omega
        simp [this]
  · intro a' _ ha'
    refine Finset.sum_eq_zero fun j _ => ?_
    have : ¬ (a.val = a'.val) := fun h => ha' (Fin.ext h.symm)
    simp [xinc, this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The plane complex of a column has no cycles.** -/
theorem ax_no_cycles : ∀ u : Fin A × Fin B → ZMod 2,
    (∀ m, ∑ q, u q * xinc A B q m = 0) → u = 0 := by
  intro u hu
  have key : ∀ n (hn : n < B) (a : Fin A), u (a, ⟨n, hn⟩) = 0 := by
    intro n
    induction n with
    | zero =>
      intro hn a
      have h := hu (a, ⟨0, by omega⟩)
      rw [ax_eval A B u a hn] at h
      simpa using h
    | succ n ih =>
      intro hn a
      have h := hu (a, ⟨n + 1, by omega⟩)
      rw [ax_eval A B u a hn] at h
      have h0 := ih (by omega) a
      simp only [Nat.succ_pos, dif_pos, Nat.add_sub_cancel] at h
      rw [h0, add_zero] at h
      exact h
  funext ⟨a, j⟩
  exact key j.val j.isLt a

lemma mem_rectAx_inl (R k j0 : ℕ) (k₀ : Fin (C + 1)) (i : Fin A) (j : Fin B) (k' : Fin (C + 1)) :
    Sum.inl (i, j, k') ∈ rectAx A B C R k j0 k₀ ↔
      i.val < R ∧ j0 ≤ j.val ∧ j.val < j0 + k ∧ k' = k₀ := by
  simp [rectAx]

lemma not_mem_rectAx_inr (R k j0 : ℕ) (k₀ : Fin (C + 1))
    (x : (Fin A × Fin (B + 1) × Fin C) ⊕ (Fin (A + 1) × Fin B × Fin C)) :
    Sum.inr x ∉ rectAx A B C R k j0 k₀ := by
  simp [rectAx]

lemma chain_rectAx (R k j0 : ℕ) (k₀ : Fin (C + 1)) (q : Fin A × Fin B) :
    chain (pplaq A B C) (rectAx A B C R k j0 k₀) q =
      if q.1.val < R ∧ j0 ≤ q.2.val ∧ q.2.val < j0 + k then 1 else 0 := by
  obtain ⟨qi, qj⟩ := q
  unfold chain
  by_cases hq : qi.val < R ∧ j0 ≤ qj.val ∧ qj.val < j0 + k
  · have : (rectAx A B C R k j0 k₀).filter (fun p => pplaq A B C p = some (qi, qj)) =
        {Sum.inl (qi, qj, k₀)} := by
      ext p
      rcases p with ⟨i, j, k'⟩ | x
      · rw [Finset.mem_filter, mem_rectAx_inl]
        simp only [pplaq, Option.some.injEq, Prod.mk.injEq, Finset.mem_singleton, Sum.inl.injEq]
        constructor
        · rintro ⟨⟨_, _, _, hk⟩, hi, hj⟩
          exact ⟨hi, hj, hk⟩
        · rintro ⟨hi, hj, hk⟩
          subst hi; subst hj; subst hk
          exact ⟨⟨hq.1, hq.2.1, hq.2.2, rfl⟩, rfl, rfl⟩
      · simp [not_mem_rectAx_inr]
    rw [this, if_pos hq]
    simp
  · have : (rectAx A B C R k j0 k₀).filter (fun p => pplaq A B C p = some (qi, qj)) = ∅ := by
      ext p
      rcases p with ⟨i, j, k'⟩ | x
      · rw [Finset.mem_filter, mem_rectAx_inl]
        simp only [pplaq, Option.some.injEq, Prod.mk.injEq, Finset.notMem_empty, iff_false,
          not_and]
        rintro ⟨hi, hj, hk, _⟩ hi' hj'
        subst hi'; subst hj'
        exact hq ⟨hi, hj, hk⟩
      · simp [not_mem_rectAx_inr]
    rw [this, if_neg hq]
    simp

/-- **The area bound for a loop in axial gauge, with a time offset**: a surface `S` with the
boundary of `rectAx` (the rows of `x` links at times `j₀` and `j₀ + k`) has at least `R · k`
plaquettes. -/
theorem area_bound_rectAx (R k j0 : ℕ) (hR : R ≤ A) (hjk : j0 + k ≤ B) (k₀ : Fin (C + 1))
    {S : Finset (CPlaq A B C)}
    (h : bdry (ainc A B C) S = bdry (ainc A B C) (rectAx A B C R k j0 k₀)) : R * k ≤ S.card := by
  have h1 := card_ge_of_boundary_eq (ainc A B C) (xinc A B) (pplaq A B C) (axρ A B C)
    (ax_proj A B C) (ax_no_cycles A B) h
  have hfil : (Finset.univ.filter fun q : Fin A × Fin B =>
      chain (pplaq A B C) (rectAx A B C R k j0 k₀) q = 1) =
      (Finset.univ.filter fun i : Fin A => i.val < R) ×ˢ
        ((Finset.univ.filter fun j : Fin B => j.val < j0 + k) \
          (Finset.univ.filter fun j : Fin B => j.val < j0)) := by
    ext q
    simp only [chain_rectAx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_sdiff]
    by_cases hq : q.1.val < R ∧ j0 ≤ q.2.val ∧ q.2.val < j0 + k
    · simp only [if_pos hq]
      refine ⟨fun _ => ⟨hq.1, hq.2.2, by omega⟩, fun _ => trivial⟩
    · simp only [if_neg hq]
      constructor
      · intro h0; exact absurd h0 (by decide)
      · rintro ⟨hi, hj, hj'⟩
        exact absurd ⟨hi, by omega, hj⟩ hq
  rw [hfil, Finset.card_product, Finset.card_sdiff_of_subset, Fin.card_filter_val_lt,
    Fin.card_filter_val_lt, Fin.card_filter_val_lt, Nat.min_eq_right hR,
    Nat.min_eq_right hjk, Nat.min_eq_right (by omega : j0 ≤ B)] at h1
  · have : j0 + k - j0 = k := by omega
    rw [this] at h1
    exact h1
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    omega

end AreaBound
