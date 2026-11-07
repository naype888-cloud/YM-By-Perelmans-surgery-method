/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
import AreaBound
import AreaLawBound

/-!
# Concrete Area Law for the 3D Cubic Lattice Box

This file glues the minimal area bound from `AreaBound.lean`
with the uniform-in-volume decay from `AreaLawBound.lean`.

**Scope.** The box, links and plaquettes are the computational scaffold of Wilson's `Z₂` model (like a
choice of coordinates). The theorem is a true statement about that model; it is not a description of
space. See `docs/PUENTE_TdPd_LEY_DEL_AREA.md`.
-/

namespace Z2Gauge

open AreaBound

/-- The equivalence between `AreaBound.bdry` and `Z2Gauge.boundary`. -/
lemma bdry_eq_boundary {P L : Type*} [Fintype P] (inc : P → L → ZMod 2) (S : Finset P) :
    AreaBound.bdry inc S = Z2Gauge.boundary inc S := rfl

open Classical in
/-- **The concrete uniform-in-volume area law in the 3D cubic box**:
for any box `A × B × C` and any flat rectangle `R × T` (`R ≤ A`, `T ≤ B`),
the Wilson loop expectation decays exponentially with the area `R * T`. -/
theorem cube_wilson_area_law (A B C R T : ℕ) (hR : R ≤ A) (hT : T ≤ B) (k₀ : Fin (C + 1))
    {Δ : ℕ} (hdeg : ∀ p : CPlaq A B C, (Finset.univ.filter (Adj (cinc A B C) p)).card ≤ Δ)
    {β t' a : ℝ} (hβ : 0 ≤ β) (htt' : Real.tanh β ≤ t') (ht' : 0 < t') (ha : 0 ≤ a)
    (hta : t' * (1 + a) ^ Δ ≤ a) :
    wilsonExpect (cinc A B C) β (rect A B C R T k₀) ≤
      (Real.tanh β / t') ^ (R * T) *
        (1 + a) ^ (Finset.univ.filter (IsSeed (cinc A B C) (boundary (cinc A B C) (rect A B C R T k₀)))).card := by
  refine area_law_uniform hdeg hβ htt' ht' ha hta (rect A B C R T k₀) (m := R * T) ?_
  intro γ hγ
  have hbdry : AreaBound.bdry (cinc A B C) γ = AreaBound.bdry (cinc A B C) (rect A B C R T k₀) := hγ
  exact area_bound_rect A B C R T hR hT k₀ hbdry

#print axioms cube_wilson_area_law

end Z2Gauge
