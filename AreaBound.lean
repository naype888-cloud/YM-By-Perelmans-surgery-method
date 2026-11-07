/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
import Mathlib

/-!

# A surface with a planar boundary has at least the planar area

## i. Overview

Let `inc` be the incidence of plaquettes on links of a complex and `inc2` the one of a plane complex
`Q`, `M`. A *projection* sends each plaquette `p` to a plane plaquette `κ p` or to nothing, and each
link to a combination of plane links, so that the projected boundary of `p` is the plane boundary
of `κ p` (and `0` when `κ p` is nothing). Then the projected boundary of a set `S` of plaquettes is
the plane boundary of the chain `f S`, where `f S q` is the parity of the number of plaquettes of
`S` over the plane plaquette `q`.

If the plane complex has no 2-cycles (its plaquette vectors are independent over `ℤ/2`), two sets
with the same boundary project to the same chain. So a surface `S` bounding the same loop as a flat
region `S₀` has at least one plaquette over each plane plaquette of `S₀`: `|S| ≥ |S₀|`.

## ii. Key results

- `AreaBound.project_boundary` : the projected boundary of `S` is the plane boundary of `f S`.
- `AreaBound.chain_eq_of_boundary_eq` : same boundary, same projected chain.
- `AreaBound.card_ge_of_boundary_eq` : `|S| ≥ #{q | f S₀ q = 1}`.

## iii. Table of contents

- A. The projected chain
- B. The area bound

## iv. References


**Scope.** The box, links and plaquettes are the computational scaffold of Wilson's `Z₂` model (like a
choice of coordinates). The theorem is a true statement about that model; it is not a description of
space. See `docs/PUENTE_TdPd_LEY_DEL_AREA.md`.
-/

open Finset

namespace AreaBound

variable {P L Q M : Type*} [Fintype P] [Fintype L] [Fintype Q] [Fintype M]
  [DecidableEq P] [DecidableEq Q]

/-- The boundary of a set `S` of plaquettes: the links that belong to an odd number of them. -/
def bdry (inc : P → L → ZMod 2) (S : Finset P) : L → ZMod 2 := fun l => ∑ p ∈ S, inc p l

/-- The parity of the number of plaquettes of `S` over the plane plaquette `q`. -/
def chain (κ : P → Option Q) (S : Finset P) (q : Q) : ZMod 2 :=
  ((S.filter fun p => κ p = some q).card : ZMod 2)

/-! ## A. The projected chain -/

omit [Fintype P] [Fintype M] [DecidableEq P] in
/-- **The projected boundary of `S` is the plane boundary of its chain.** -/
theorem project_boundary (inc : P → L → ZMod 2) (inc2 : Q → M → ZMod 2) (κ : P → Option Q)
    (ρ : L → M → ZMod 2)
    (hproj : ∀ p m, ∑ l, ρ l m * inc p l = (κ p).elim 0 (fun q => inc2 q m))
    (S : Finset P) (m : M) :
    ∑ l, ρ l m * bdry inc S l = ∑ q, chain κ S q * inc2 q m := by
  have h1 : ∑ l, ρ l m * bdry inc S l = ∑ p ∈ S, (κ p).elim 0 (fun q => inc2 q m) := by
    simp only [bdry, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact sum_congr rfl fun p _ => hproj p m
  have h3 : ∀ q, chain κ S q * inc2 q m = ∑ p ∈ S, if κ p = some q then inc2 q m else 0 := by
    intro q
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rfl
  rw [h1, sum_congr rfl fun q _ => h3 q, Finset.sum_comm]
  refine sum_congr rfl fun p _ => ?_
  cases hκ : κ p with
  | none => simp
  | some q0 => simp

lemma add_eq_zero_iff_eq (a b : ZMod 2) : a + b = 0 ↔ a = b := by
  have key : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases key a with rfl | rfl <;> rcases key b with rfl | rfl <;> decide

/-! ## B. The area bound -/

omit [Fintype P] [Fintype M] [DecidableEq P] in
/-- **Same boundary, same projected chain**, if the plane complex has no 2-cycles. -/
theorem chain_eq_of_boundary_eq (inc : P → L → ZMod 2) (inc2 : Q → M → ZMod 2)
    (κ : P → Option Q) (ρ : L → M → ZMod 2)
    (hproj : ∀ p m, ∑ l, ρ l m * inc p l = (κ p).elim 0 (fun q => inc2 q m))
    (hinj2 : ∀ u : Q → ZMod 2, (∀ m, ∑ q, u q * inc2 q m = 0) → u = 0)
    {S S₀ : Finset P} (h : bdry inc S = bdry inc S₀) : chain κ S = chain κ S₀ := by
  have hadd : ∀ a : ZMod 2, a + a = 0 := by decide
  have h0 : ∀ m, ∑ q, (chain κ S q + chain κ S₀ q) * inc2 q m = 0 := by
    intro m
    simp only [add_mul, Finset.sum_add_distrib, ← project_boundary inc inc2 κ ρ hproj, h]
    exact hadd _
  have hu := hinj2 _ h0
  funext q
  exact (add_eq_zero_iff_eq _ _).mp (congrFun hu q)

omit [Fintype P] [Fintype M] [DecidableEq P] in
/-- **A surface has at least the area of its projection**: if `S` and `S₀` have the same boundary
and the plane complex has no 2-cycles, then `|S|` is at least the number of plane plaquettes `q`
over which `S₀` has an odd number of plaquettes. -/
theorem card_ge_of_boundary_eq (inc : P → L → ZMod 2) (inc2 : Q → M → ZMod 2)
    (κ : P → Option Q) (ρ : L → M → ZMod 2)
    (hproj : ∀ p m, ∑ l, ρ l m * inc p l = (κ p).elim 0 (fun q => inc2 q m))
    (hinj2 : ∀ u : Q → ZMod 2, (∀ m, ∑ q, u q * inc2 q m = 0) → u = 0)
    {S S₀ : Finset P} (h : bdry inc S = bdry inc S₀) :
    (univ.filter fun q => chain κ S₀ q = 1).card ≤ S.card := by
  have hc := chain_eq_of_boundary_eq inc inc2 κ ρ hproj hinj2 h
  rw [← hc]
  have hsub : (univ.filter fun q => chain κ S q = 1).image some ⊆ S.image κ := by
    intro o ho
    obtain ⟨q, hq, rfl⟩ := mem_image.mp ho
    have hq1 : chain κ S q = 1 := (mem_filter.mp hq).2
    have hne : (S.filter fun p => κ p = some q).card ≠ 0 := by
      intro h0
      have : chain κ S q = 0 := by simp [chain, h0]
      rw [this] at hq1
      exact absurd hq1 (by decide)
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
    exact mem_image.mpr ⟨p, (mem_filter.mp hp).1, (mem_filter.mp hp).2⟩
  calc (univ.filter fun q => chain κ S q = 1).card
      = ((univ.filter fun q => chain κ S q = 1).image some).card :=
        (card_image_of_injective _ (Option.some_injective _)).symm
    _ ≤ (S.image κ).card := card_le_card hsub
    _ ≤ S.card := card_image_le

/-! ## C. The cubic box -/

section Cube

variable (A B C : ℕ)

/-- Links of a box of `A × B × C` cubes: `x`, `y` and `z` links. -/
abbrev CLink := (Fin A × Fin (B + 1) × Fin (C + 1)) ⊕
  ((Fin (A + 1) × Fin B × Fin (C + 1)) ⊕ (Fin (A + 1) × Fin (B + 1) × Fin C))

/-- Plaquettes of the box: `xy`, `xz` and `yz`. -/
abbrev CPlaq := (Fin A × Fin B × Fin (C + 1)) ⊕
  ((Fin A × Fin (B + 1) × Fin C) ⊕ (Fin (A + 1) × Fin B × Fin C))

/-- The incidence of the plaquettes on the links of the box. -/
def cinc : CPlaq A B C → CLink A B C → ZMod 2
  | .inl (i, j, k), .inl (i', j', k') =>
      if i'.val = i.val ∧ k'.val = k.val ∧ (j'.val = j.val ∨ j'.val = j.val + 1) then 1 else 0
  | .inl (i, j, k), .inr (.inl (i', j', k')) =>
      if j'.val = j.val ∧ k'.val = k.val ∧ (i'.val = i.val ∨ i'.val = i.val + 1) then 1 else 0
  | .inl _, .inr (.inr _) => 0
  | .inr (.inl (i, j, k)), .inl (i', j', k') =>
      if i'.val = i.val ∧ j'.val = j.val ∧ (k'.val = k.val ∨ k'.val = k.val + 1) then 1 else 0
  | .inr (.inl _), .inr (.inl _) => 0
  | .inr (.inl (i, j, k)), .inr (.inr (i', j', k')) =>
      if j'.val = j.val ∧ k'.val = k.val ∧ (i'.val = i.val ∨ i'.val = i.val + 1) then 1 else 0
  | .inr (.inr _), .inl _ => 0
  | .inr (.inr (i, j, k)), .inr (.inl (i', j', k')) =>
      if i'.val = i.val ∧ j'.val = j.val ∧ (k'.val = k.val ∨ k'.val = k.val + 1) then 1 else 0
  | .inr (.inr (i, j, k)), .inr (.inr (i', j', k')) =>
      if i'.val = i.val ∧ k'.val = k.val ∧ (j'.val = j.val ∨ j'.val = j.val + 1) then 1 else 0

/-- Links of the plane `A × B`: `x` and `y` links. -/
abbrev PLink := (Fin A × Fin (B + 1)) ⊕ (Fin (A + 1) × Fin B)

/-- The incidence of the plane plaquettes `Fin A × Fin B` on the plane links. -/
def pinc : Fin A × Fin B → PLink A B → ZMod 2
  | (i, j), .inl (a, b) => if a.val = i.val ∧ (b.val = j.val ∨ b.val = j.val + 1) then 1 else 0
  | (i, j), .inr (a, b) => if b.val = j.val ∧ (a.val = i.val ∨ a.val = i.val + 1) then 1 else 0

/-- The projection of the links to the plane: forget the height; the `z` links go to `0`. -/
def proj : CLink A B C → PLink A B → ZMod 2
  | .inl (i, j, _), .inl (a, b) => if i = a ∧ j = b then 1 else 0
  | .inl _, .inr _ => 0
  | .inr (.inl (i, j, _)), .inr (a, b) => if i = a ∧ j = b then 1 else 0
  | .inr (.inl _), .inl _ => 0
  | .inr (.inr _), _ => 0

/-- The projection of the plaquettes: forget the height; the vertical plaquettes go to nothing. -/
def pplaq : CPlaq A B C → Option (Fin A × Fin B)
  | .inl (i, j, _) => some (i, j)
  | .inr _ => none

/-- A sum with a condition and a point collapses to the condition at the point. -/
lemma sum_collapse {n : ℕ} (c : Fin n → Prop) [DecidablePred c] (b : Fin n) :
    ∑ x : Fin n, (if c x then (if x = b then (1 : ZMod 2) else 0) else 0) =
      if c b then 1 else 0 := by
  rw [Finset.sum_eq_single b]
  · simp
  · intro x _ hx
    simp [hx]
  · intro h
    exact absurd (Finset.mem_univ b) h

/-- Two links over the same plane link cancel: `∑ x, [x = k ∨ x = k + 1] = 2 = 0`. -/
lemma sum_two {C : ℕ} (k : Fin C) :
    ∑ x : Fin (C + 1), (if x.val = k.val ∨ x.val = k.val + 1 then (1 : ZMod 2) else 0) = 0 := by
  have hk : k.val < C := k.isLt
  have hfil : (Finset.univ.filter fun x : Fin (C + 1) => x.val = k.val ∨ x.val = k.val + 1) =
      {⟨k.val, by omega⟩, ⟨k.val + 1, by omega⟩} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff]
  rw [← Finset.sum_filter, hfil, Finset.sum_pair (by simp [Fin.ext_iff])]
  decide

/-- The same, as a cardinality: two links over the same plane link. -/
lemma card_two {C : ℕ} (k : Fin C) :
    (((Finset.univ.filter fun x : Fin (C + 1) => x.val = k.val ∨ x.val = k.val + 1).card : ℕ) :
      ZMod 2) = 0 := by
  have hk : k.val < C := k.isLt
  have hfil : (Finset.univ.filter fun x : Fin (C + 1) => x.val = k.val ∨ x.val = k.val + 1) =
      {⟨k.val, by omega⟩, ⟨k.val + 1, by omega⟩} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff]
  rw [hfil, Finset.card_pair (by simp [Fin.ext_iff])]
  decide

/-- **The projection property of the cubic box**: the projected boundary of a plaquette is the plane
boundary of its projection (`0` for a vertical plaquette). -/
theorem cube_proj (p : CPlaq A B C) (m : PLink A B) :
    ∑ l, proj A B C l m * cinc A B C p l = (pplaq A B C p).elim 0 (fun q => pinc A B q m) := by
  rcases p with ⟨i, j, k⟩ | ⟨i, j, k⟩ | ⟨i, j, k⟩ <;> rcases m with ⟨a, b⟩ | ⟨a, b⟩ <;>
    simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, proj, cinc, pplaq, pinc] <;>
    simp only [mul_zero, Finset.sum_const_zero, add_zero, Option.elim_some, Option.elim_none] <;>
    simp [ite_and, Fin.val_inj, Finset.sum_ite_eq']
  · by_cases hia : i = a
    · subst hia
      simpa using sum_collapse (fun x : Fin (B + 1) => x.val = j.val ∨ x.val = j.val + 1) b
    · simp [hia, Ne.symm hia]
  · by_cases hjb : j = b
    · subst hjb
      simpa using sum_collapse (fun x : Fin (A + 1) => x.val = i.val ∨ x.val = i.val + 1) a
    · simp [hjb, Ne.symm hjb]
  · by_cases hia : i = a <;> by_cases hjb : j = b <;> simp [hia, hjb]
    exact card_two k
  · by_cases hia : i = a <;> by_cases hjb : j = b <;> simp [hia, hjb]
    exact card_two k

/-- **The plane `A × B` has no 2-cycles**: a combination of the plane plaquettes with zero boundary
is zero (induction on the row, using the horizontal links). -/
theorem plane_no_cycles (u : Fin A × Fin B → ZMod 2)
    (h : ∀ m : PLink A B, ∑ q, u q * pinc A B q m = 0) : u = 0 := by
  have key : ∀ n : ℕ, ∀ (a : Fin A) (j : Fin B), j.val = n → u (a, j) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a j hj
      have hm := h (.inl (a, ⟨j.val, by omega⟩))
      simp only [Fintype.sum_prod_type, pinc] at hm
      rw [Finset.sum_eq_single a (fun x _ hx => by
        have hax : ¬ (a.val = x.val) := fun h' => hx (Fin.ext h'.symm)
        simp [hax]) (fun h' => absurd (Finset.mem_univ a) h')] at hm
      simp only [eq_self_iff_true, true_and] at hm
      have hz : ∀ x1 ∈ (Finset.univ : Finset (Fin B)), x1 ≠ j →
          u (a, x1) * (if j.val = x1.val ∨ j.val = x1.val + 1 then 1 else 0) = 0 := by
        intro x1 _ hx1
        by_cases hlt : x1.val < j.val
        · have := ih x1.val (by omega) a x1 rfl
          simp [this]
        · have hne : x1.val ≠ j.val := fun h' => hx1 (Fin.ext h')
          have : ¬ (j.val = x1.val ∨ j.val = x1.val + 1) := by omega
          simp [this]
      rw [Finset.sum_eq_single j hz (fun h' => absurd (Finset.mem_univ j) h')] at hm
      simpa using hm
  funext ⟨a, j⟩
  exact key _ a j rfl

/-- **A surface has at least the area of its projection, in the cubic box.** -/
theorem cube_area_bound {S S₀ : Finset (CPlaq A B C)}
    (h : bdry (cinc A B C) S = bdry (cinc A B C) S₀) :
    (Finset.univ.filter fun q => chain (pplaq A B C) S₀ q = 1).card ≤ S.card :=
  card_ge_of_boundary_eq (cinc A B C) (pinc A B) (pplaq A B C) (proj A B C) (cube_proj A B C)
    (plane_no_cycles A B) h

/-- The flat rectangle `R × T` of `xy` plaquettes at the height `k₀`. -/
def rect (R T : ℕ) (k₀ : Fin (C + 1)) : Finset (CPlaq A B C) :=
  (Finset.univ.filter fun x : Fin A × Fin B × Fin (C + 1) =>
    x.1.val < R ∧ x.2.1.val < T ∧ x.2.2 = k₀).image Sum.inl

lemma chain_rect (R T : ℕ) (k₀ : Fin (C + 1)) (q : Fin A × Fin B) :
    chain (pplaq A B C) (rect A B C R T k₀) q =
      if q.1.val < R ∧ q.2.val < T then 1 else 0 := by
  unfold chain
  by_cases hq : q.1.val < R ∧ q.2.val < T
  · have : (rect A B C R T k₀).filter (fun p => pplaq A B C p = some q) =
        {Sum.inl (q.1, q.2, k₀)} := by
      ext p
      simp only [rect, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · rintro ⟨⟨⟨i, j, k⟩, ⟨hi, hj, hk⟩, rfl⟩, hp⟩
        simp only [pplaq, Option.some.injEq] at hp
        subst hp
        simp only [Sum.inl.injEq, Prod.mk.injEq, true_and]
        exact hk
      · rintro rfl
        exact ⟨⟨(q.1, q.2, k₀), ⟨hq.1, hq.2, rfl⟩, rfl⟩, by simp [pplaq]⟩
    rw [this, if_pos hq]
    simp
  · have : (rect A B C R T k₀).filter (fun p => pplaq A B C p = some q) = ∅ := by
      ext p
      simp only [rect, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.notMem_empty, iff_false, not_and]
      rintro ⟨⟨i, j, k⟩, ⟨hi, hj, hk⟩, rfl⟩ hp
      simp only [pplaq, Option.some.injEq] at hp
      subst hp
      exact hq ⟨hi, hj⟩
    rw [this, if_neg hq]
    simp

/-- **The area law bound for a flat rectangle**: a surface `S` of the cubic box with the same boundary
as the flat rectangle `R × T` has at least `R · T` plaquettes. -/
theorem area_bound_rect (R T : ℕ) (hR : R ≤ A) (hT : T ≤ B) (k₀ : Fin (C + 1))
    {S : Finset (CPlaq A B C)}
    (h : bdry (cinc A B C) S = bdry (cinc A B C) (rect A B C R T k₀)) : R * T ≤ S.card := by
  have h1 := cube_area_bound A B C h
  have hfil : (Finset.univ.filter fun q : Fin A × Fin B =>
      chain (pplaq A B C) (rect A B C R T k₀) q = 1) =
      (Finset.univ.filter fun i : Fin A => i.val < R) ×ˢ
        (Finset.univ.filter fun j : Fin B => j.val < T) := by
    ext q
    simp only [chain_rect, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    by_cases hq : q.1.val < R ∧ q.2.val < T
    · simp [hq]
    · simp only [if_neg hq]
      constructor
      · intro h0
        exact absurd h0 (by decide)
      · intro h0
        exact absurd h0 hq
  rw [hfil, Finset.card_product, Fin.card_filter_val_lt, Fin.card_filter_val_lt,
    Nat.min_eq_right hR, Nat.min_eq_right hT] at h1
  exact h1

end Cube

end AreaBound
