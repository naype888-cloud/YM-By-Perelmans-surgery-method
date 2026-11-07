/-
Copyright (c) 2026 Eduardo Nava Hernandez. All rights reserved.
Released under the NRS license (see LICENSE).
-/
import AreaLawBound
import AreaBound

/-!
# The box in axial gauge: the incidence without the `y` links, and a rectangle with a time offset

In axial gauge the links in the time direction (`y`) are set to `+1`: the incidence `ainc` of the
plaquettes of the box `A × B × C` on the remaining links (`x` and `z`) is the restriction of
`AreaBound.cinc` to those links. The loop `rectAx R k j₀ k₀` is the set of `xy` plaquettes of the
rectangle of `R` columns and `k` time steps starting at time `j₀`, at height `k₀`.

## Main results

- `AreaBound.ALink`, `AreaBound.aemb`, `AreaBound.ainc`, `AreaBound.rectAx` : the definitions.
- `AreaBound.adj_ainc` : adjacency for `ainc` implies adjacency for `cinc` (so the degree bound
  `Δ` for the box also bounds the degree for `ainc`).

## Scope

Definitions and one trivial lemma. The area bound for `ainc` and the factorization of the weight
in time slices are NOT proved here.
-/

open Finset

namespace AreaBound

variable (A B C : ℕ)

/-- Links of the box in axial gauge: `x` and `z` links (the `y` links are gauge fixed to `+1`). -/
abbrev ALink := (Fin A × Fin (B + 1) × Fin (C + 1)) ⊕ (Fin (A + 1) × Fin (B + 1) × Fin C)

/-- The embedding of the axial links in the links of the box. -/
def aemb : ALink A B C → CLink A B C
  | .inl x => .inl x
  | .inr z => .inr (.inr z)

/-- The incidence of the plaquettes on the axial links. -/
def ainc : CPlaq A B C → ALink A B C → ZMod 2 := fun p l => cinc A B C p (aemb A B C l)

open Classical in
/-- The `xy` plaquettes of the rectangle of `R` columns and `k` time steps starting at time `j₀`,
at height `k₀`. -/
noncomputable def rectAx (R k j₀ : ℕ) (k₀ : Fin (C + 1)) : Finset (CPlaq A B C) :=
  Finset.univ.filter fun p => match p with
    | .inl (i, j, k') => i.val < R ∧ j₀ ≤ j.val ∧ j.val < j₀ + k ∧ k' = k₀
    | _ => False

/-- Adjacency for `ainc` implies adjacency for `cinc`. -/
lemma adj_ainc {p q : CPlaq A B C} (h : Z2Gauge.Adj (ainc A B C) p q) :
    Z2Gauge.Adj (cinc A B C) p q := by
  obtain ⟨hne, l, h1, h2⟩ := h
  exact ⟨hne, aemb A B C l, h1, h2⟩

end AreaBound
