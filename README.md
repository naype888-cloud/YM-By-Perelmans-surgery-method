# Yang–Mills: By Perelman's Surgery Method

**Formalized in Lean 4 (Mathlib puro, 0 sorry, standard logical axioms `[propext, Classical.choice, Quot.sound]`).**

Authors: Eduardo Nava-Hernández (naype888-cloud) & Claude Sonnet 5.5 (Anthropic) & Antigravity (Google DeepMind).

---

## Overview

This repository proves, in Lean 4, the area law of Wilson's `Z₂` gauge model, uniformly in the volume,
and a family of tools around it (Kotecký–Preiss for non-negative weights, the decomposition of the
partition function into polymers, a spectral bridge from a gap to decay of correlations).

**Scope.** The plaquettes, links and boxes in these files are the *computational scaffold* of Wilson's
model, in the same way Cartesian coordinates are a scaffold: the theorems are true statements about
that model, and they say nothing about what space is. Elementary motion is `T_d : P_d`
(`D3`, `D5`, `D21`, `D22` of the independent corpus); stating the area law and the gap in terms of
`T_d : P_d` is not done yet (see `docs/PUENTE_TdPd_LEY_DEL_AREA.md`).

**Proved:**

$$\langle W(R \times T) \rangle \le \left(\frac{\tanh \beta}{t'}\right)^{R \cdot T} (1 + a)^{8(R + T)}$$

$$\text{String tension: } \quad \sigma(\beta) \ge \ln\left(\frac{t'}{\tanh \beta}\right) > 0 \quad \text{uniformly in the volume.}$$

**Not proved here:** a mass gap for non-abelian Yang–Mills, `SU(N)` (no Peter–Weyl in Mathlib), the
bridge from the defect `massSq` to a spectral bound (`FibreBound`), Osterwalder–Schrader/Wightman.

---

## Core Formalized Modules

1. **`Z2AreaLaw.lean`**:
   - Exact high-temperature character expansion of the Wilson loop for arbitrary lattice incidence and dimension (`highTemp_expect`).
   - Transfer matrix $2 \times 2$ for the single-plaquette strip with $\text{Gap} = \sigma = -\ln \tanh \beta$ (`gap_eq_stringTension`).
2. **`PolymerBound.lean`**:
   - Injective cluster decomposition $S \mapsto (\gamma, R)$ where $\gamma$ is attached to the loop and $\partial R = 0$ (vacuum bubbles).
   - Exact cancellation of vacuum bubbles without cluster expansion: $\langle W(C) \rangle \le \sum_{\gamma \text{ attached}} t^{|\gamma|}$ (`numerator_le`, `expect_le_attached`).
3. **`TreeBound.lean`**:
   - Path surgery lemma (`reach_erase`).
   - Finite induction on plaquette sets proving that the sum of attached surfaces is bounded by $(1 + a)^{|\text{seeds}|}$ whenever $t(1 + a)^\Delta \le a$ (`rootedSum_le`). Completely independent of the lattice volume.
4. **`AreaBound.lean`**:
   - Abstract boundary-respecting projection theorem (`card_ge_of_boundary_eq`).
   - Absence of 2-cycles in the 2D plane over $\mathbb{Z}/2$ (`plane_no_cycles`).
   - Minimal area bound for any surface spanning the flat Wilson loop in the 3D cubic box: $|S| \ge R \times T$ (`area_bound_rect`).
5. **`AreaLawBound.lean`**:
   - Uniform-in-volume area law under general local incidence hypotheses (`area_law_uniform`):
     $$\langle W(\partial S_0) \rangle \le \left(\frac{\tanh \beta}{t'}\right)^m (1 + a)^{\#\text{seeds}}$$
6. **`CubeAreaLaw.lean`**:
   - The concrete area law for the 3D cubic lattice box, connecting `area_bound_rect` with `area_law_uniform`:
     `Z2Gauge.cube_wilson_area_law`.
   - Kernel axiom check: depends strictly on standard Lean 4 axioms `[propext, Classical.choice, Quot.sound]`. Zero custom axioms.
7. **`FibreSurgery.lean` & `FibreBand.lean`**:
   - The topological surgery: strictly monotone defect quantity $\text{massSq}(d) = C_N(d)^2 - 1$ on $d \ge 4$.
   - Suture function $\text{massFn}(L)$ with strictly positive lower bound $\min(1/4, \text{massSq}(4)/L^2) > 0$.
   - Defect lower bound on the high-tension band: $\text{surplus}(\psi) \ge \frac{C_N(d)^2 - 1}{2(d-1)^2}$.
8. **`SpectralGap.lean`**:
   - Universal spectral bridge: a spectral gap $\Delta = \ln(\mu_0 / \lambda_1) > 0$ strictly forces exponential decay of connected correlations $\le e^{-\Delta k} \|x\|^2$ (`connected_le_exp`).

---

## Directory Structure

```text
lattice-gauge-gap/
├── AreaBound.lean               # 3D cubic box minimal area bound (|S| ≥ R × T)
├── AreaLawBound.lean            # Uniform-in-volume area law
├── CubeAreaLaw.lean             # Concrete 3D cubic box Wilson area law (0 sorry)
├── FibreBand.lean               # High-tension band defect lower bound
├── FibreSurgery.lean            # Perelman-style surgery and monotone defect mass
├── PolymerBound.lean            # Attached cluster decomposition & vacuum bubble cancellation
├── SpectralGap.lean             # Transfer matrix spectral gap ↔ exponential decay
├── TreeBound.lean               # Path surgery & rooted sum perimeter bound
├── Z2AreaLaw.lean               # General high-temperature Wilson expansion
├── build/                       # Compiled .olean bytecode for Lean 4 v4.34.0
└── docs/                        # Theoretical foundations & Kotecký–Preiss formal statement
```

9. **`KoteckyPreiss.lean`**: Kotecký–Preiss for non-negative weights, proved (`ratio_le_exp_of_kp`: Z(Λ) ≤ Z(Λ_γ₀)·e^{a γ₀}, uniform in the volume; `exp_neg_le_ratio`; `log_polymerZ_le`). Standard axioms only, 0 sorry. Not covered: complex weights, extraction of the decay `d`.

10. **`PolymerDecomposition.lean`**: `highTempSum inc t 0 = polymerZ (Compat inc) (polyWeight inc t) univ` (closed surface = unique family of connected closed components sharing no link), plus `z2_ratio_le_exp` and `z2_log_le`: Kotecký–Preiss now applies to the Z2 partition function for `t ≥ 0`. Standard axioms, 0 sorry.

11. **`Z2Transfer.lean`, `Z2Gap.lean`**: the transfer matrix `T = D^{1/2} K D^{1/2}` of Wilson's `Z₂` model (time-like plaquette kernel `K`, any positive space-like weight `D`) is positive semidefinite (`transfer_posSemidef`); combined with `TransferBridge` this discharges `hPSD` (`z2_spectral_gap`). Still a hypothesis: the decay of `x ⬝ T^k x`, i.e. that the Euclidean Wilson loop of the box is `⟨x, T^k x⟩ / (μ₀^k ‖x‖²)` (gauge fixing of the time-like links).

12. **`SlabChain.lean`**: time slicing as linear algebra: `chainSum M u m = 1 ⬝ᵥ (P^m u)` and, for `u ≥ 0`, `chainSum M u m = √u ⬝ᵥ (T^m √u)` with `T = D^{1/2} M D^{1/2}` (`chainSum_eq`, `chainSum_eq_transfer`). Piece A of the `wilson_rep` plan; that the `Z₂` box has this form is not proved yet.

13. **`SlabLimit.lean`**: the infinite-time limit (piece B of the `wilson_rep` plan): for PSD `T` with top eigenvalue `μ₀`, if `(T^N v) ⬝ Y (T^N v) ≤ D · v ⬝ T^{2N+k} v` for all `N`, then `∑_{i,l ∈ top} c_i c_l (e_i ⬝ Y e_l) ≤ D μ₀^k ∑_{j ∈ top} c_j²` (`top_limit`). Not proved: that `v` overlaps the top eigenspace (Perron–Frobenius), piece B2.

14. **`PerronOverlap.lean`**: piece B2: a symmetric matrix with nonnegative entries and a vector with positive entries have `∃ j, μ_j = μ₀ ∧ c_j(v) ≠ 0` (`top_overlap`): the positive vector overlaps the top eigenspace (the argument with `|e|`, no Perron–Frobenius needed). Not claimed: that the top eigenvalue is simple.

15. **`AxialBox.lean`, `AxialArea.lean`**: the box in axial gauge (incidence `ainc` without the `y` links, rectangle `rectAx` with a time offset) and the area bound `area_bound_rectAx`: a surface with the boundary of `rectAx` (rows of `x` links at times `j₀` and `j₀ + k`) has at least `R · k` plaquettes (projection to the plane complex of each column, which has no cycles). Piece C2 of the `wilson_rep` plan.
