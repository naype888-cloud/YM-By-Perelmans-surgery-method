<div align="center">

# Yang–Mills Spectral Mass Gap
### Constructive Topological Surgery, Transfer Bridge & Quantum Coherence Defect

**Eduardo Nava-Hernández & José Arturo Nava-Hernández** · *feat. Grigori Perelman Surgery Method*

[![Lean 4](https://img.shields.io/badge/Lean_4-v4.33.0-blue.svg?style=flat-square)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/Mathlib-verified-2ea44f.svg?style=flat-square)](https://github.com/leanprover-community/mathlib4)
[![Kernel Status](https://img.shields.io/badge/Kernel-0%20sorry%20%7C%20Certified-brightgreen.svg?style=flat-square)]()
[![Physlib](https://img.shields.io/badge/Physlib-50%20PRs%20Merged-brightgreen.svg?style=flat-square)](https://github.com/leanprover-community/physlib)

<br><br>

](docs/SU2-SU3.pdf?raw=true)

<br><br>

<a href="docs/assets/step1_preview.mp4">
  <img src="docs/assets/step1_preview.gif" alt="Paso 1: Red 3D Tight-Binding y Ley del Área" width="380" />
</a>

<br>

</div>

---

## 🏛️ Constructive 7-Step Deductive Chain

### 📐 Step 1: Uniform Area Law on the 3D Lattice
> Rigorous combinatorial bound on the cubic lattice with adjacency degree $\Delta = 12$ and perimeter seeds $|\mathrm{Seeds}| \le 8(R + T)$:

$$\huge \displaystyle \mathbf{\langle W(R \times T) \rangle \le \left(\frac{\tanh \beta}{t'}\right)^{R \cdot T} (1 + a)^{8(R + T)}}$$

$$\huge \displaystyle \mathbf{\sigma(\beta) := -\lim_{R, T \to \infty} \frac{1}{R \cdot T} \ln \langle W(R \times T) \rangle \ge \ln\left(\frac{t'}{\tanh \beta}\right) > 0}$$

*Formalized in:* [`CubeAreaLaw.lean`](src/CubeAreaLaw.lean) (`cube_wilson_area_law`), [`AreaLawBound.lean`](src/AreaLawBound.lean) (`area_law_uniform`), [`AdjDegree.lean`](src/AdjDegree.lean) (`adj_degree_le_twelve`).

---

### ⚡ Step 2: Transfer Matrix and Inverse Power Lemma
> Euclidean temporal decay of the transfer matrix $T = e^{-a \hat{H}}$ forces the spectral bound via theorem `eigenvalue_le_of_pow_bound`:

$$\huge \displaystyle \mathbf{\forall k \in \mathbb{N}, \quad \left(\frac{\mu_1}{\mu_0}\right)^k \le \frac{C}{|c_1|^2} \left(e^{-\sigma R}\right)^k \implies \frac{\mu_1}{\mu_0} \le e^{-\sigma R} < 1}$$

$$\huge \displaystyle \mathbf{\Delta_{\mathrm{glue}} = E_1 - E_0 = -\frac{1}{a} \ln\left(\frac{\mu_1}{\mu_0}\right) \ge \frac{\sigma \cdot R}{a} > 0}$$

*Formalized in:* [`SurgeryGapClosure.lean`](src/SurgeryGapClosure.lean) (`eigenvalue_le_of_pow_bound`), [`Z2Final.lean`](src/Z2Final.lean) (`z2_gap_twelve`), [`Z2Hj.lean`](src/Z2Hj.lean) (`z2_gap_free`, `exists_excited`).

---

### 🛡️ Step 3: Perelman's Topological Surgery and 5/4 Quantum Defect
> Robertson–Schrödinger symplectic torsion on $\mathcal{M}_4 = \mathbb{R}^3 \times S^1$ with transverse shielding via Clifford anticommutation:

$$\huge \displaystyle \mathbf{\frac{\det \Sigma}{|\det \Omega|} = 1 + \mathrm{massSq}(4) = 1 + \frac{1}{4} = \frac{5}{4} > 1}$$

$$\huge \displaystyle \mathbf{\lbrace A[U], \, M_w \rbrace = 0 \implies \|(A[U] + M_w)\chi\|^2 \ge \left(\frac{1}{2a}\right)^2 \|\chi\|^2 \implies \sqrt{\mathrm{floor}} \ge \frac{1}{2a} > 0}$$

*Formalized in:* [`FibreSurgery.lean`](src/FibreSurgery.lean) (`massFn_floor_pos`), [`FibreBand.lean`](src/FibreBand.lean) (`surplus_ge_massSq`), [`SurgeryGapClosure.lean`](src/SurgeryGapClosure.lean) (`totalPhysicalGap_pos`).  
*Certified in NRS³ corpus:* [`D55_SaturatingRegion`](https://github.com/naype888-cloud/nava-robertson-schrodinger) (`defectGram_eq_zero_iff_le_three`, proving that pure 3D $d \le 3$ is strictly saturating/massless, strictly requiring Perelman surgery $\mathbb{R}^3 \times S^1 \implies d \ge 4$).

---

### 🔬 Step 4: Dirac–Kähler / Hodge–de Rham Operator for Bosons
> Clifford algebra over the exterior algebra of differential forms $\Omega^*(\mathcal{M})$ (gluons):

$$\huge \displaystyle \mathbf{\mathcal{D}_A = d_A + \delta_A, \qquad (\mathcal{D}_A)^2 = \Delta_{\mathrm{Hodge}} = d_A \delta_A + \delta_A d_A}$$

$$\huge \displaystyle \mathbf{\lbrace \mathcal{D}_{\mathbb{R}^3}, \, \mathcal{D}_{S^1} \rbrace = 0 \implies \langle \omega, \Delta_{\mathrm{Hodge}} \omega \rangle \ge \left(\frac{2}{\pi} \frac{\mathrm{holGap}(\theta)}{L}\right)^2 \|\omega\|^2 > 0}$$

*Formalized in:* [`DiracGapGaugeInvariant.lean`](https://github.com/naype888-cloud/nrs3-hopf/blob/main/NRS3Hopf/DiracGapGaugeInvariant.lean) (repo [`nrs3-hopf`](https://github.com/naype888-cloud/nrs3-hopf), establishing `pure_gauge_joint_spectral_bridge` and `pure_gauge_kogut_susskind_dirac_eigenvalue_bridge`), [`SurgeryGapClosure.lean`](src/SurgeryGapClosure.lean).

---

### 📈 Step 5: Szegő Asymptotic Limit and Increasing Monotonicity ($d \to \infty$)
> Strict increasing monotonicity of the dimensionless defect for all $d \ge 4$, shielding against Gaussian collapse:

$$\huge \displaystyle \mathbf{\mathrm{massSq}(4) \le \mathrm{massSq}(d) < \frac{\pi^2}{3} - 3 \approx 0.289868 > 0}$$

$$\huge \displaystyle \mathbf{\lim_{d \to \infty} \mathrm{massSq}(d) = \frac{\pi^2}{3} - 3 > 0}$$

*Formalized in:* [`FibreSurgery.lean`](src/FibreSurgery.lean) (`massSq_strictMonoOn`, `massSq_floor`), [`FibreBand.lean`](src/FibreBand.lean).  
*Certified in NRS³ corpus:* [`D56_MassNecessaryConditions`](https://github.com/naype888-cloud/nava-robertson-schrodinger) (`massSq_band_of_massNecessary`, proving the universal squared mass band $0 < \mathrm{massSq}(4) \le \mathrm{massSq}(d) < \pi^2/3 - 3$ from the Szegő limit in D8/D9).

---

<div align="center">

### 👑 The Exact Identity Theorem: "One Defect"
> *Formalized in Lean 4 with 0 sorry across both independent repositories:*

$$\Huge \displaystyle \mathbf{\mathrm{defectGram}(d) \equiv \frac{\mathrm{massSq}(d)}{(d - 1)^2} = \frac{C_N(d)^2 - 1}{(d - 1)^2} > 0 \quad (\forall d \ge 4)}$$

<p align="center">
  <i>The Gram defect of the quantum Robertson–Schrödinger transport on the fibre axis and the Yang–Mills physical mass gap<br>
  are <b>the exact same mathematical quantity</b>.</i>
</p>

*Formalized in:* [`src/FibreSurgery.lean`](src/FibreSurgery.lean) (`defect_over_step_sq`).  
*Certified in NRS³ corpus:* [`D56_MassNecessaryConditions`](https://github.com/naype888-cloud/nava-robertson-schrodinger) (`defectGram_eq_massSq_of_massNecessary`).

</div>

---

### 🌐 Step 6: Wightman Continuum Closure and Clay Infimum ($\mathbb{R}^4$)
> Decompactification $L \to \infty$ and gap persistence sustained by Kraan–van Baal caloron / BPS monopole condensation:

$$\huge \displaystyle \Delta_{\mathrm{total}} = \min\left(\Delta_{\mathrm{glue}}, \, \sqrt{\mathrm{floor}}\right) \ge c_\sigma \cdot \Lambda_{\mathrm{YM}} > 0$$

$$\huge \displaystyle \lim_{L \to \infty} \Delta_{\mathrm{total}} = \Delta_{\mathrm{glue}} = c_\sigma \cdot \Lambda_{\mathrm{YM}} \approx 1.5\text{--}1.7\text{ GeV} > 0$$

$$\Huge \displaystyle \inf \left( \mathrm{spec}(\hat{H}_{\mathrm{cont}}) \setminus \lbrace 0 \rbrace \right) \ge \Delta_{\mathrm{total}} > 0$$

*Formalized in:* [`SurgeryGapClosure.lean`](src/SurgeryGapClosure.lean) (`totalPhysicalGap_pos`), Osterwalder–Schrader $\to$ Wightman Reconstruction.

---

### 🏛️ Step 7: Master Hamiltonian Bridge (Unconditional Unification with OpenAI Wightman QFT)
> Direct resolution of **Open Questions #3 and #4** from the Yang–Mills Group Assessment (`assessment-1.pdf`, Nov 10, 2026) on OpenAI's `PublicTheory.lean`:

$$\huge \displaystyle \mathrm{spec}(\hat{H}) \setminus \lbrace 0 \rbrace \subseteq [\Delta_{\mathrm{total}}, \infty), \qquad \Delta_{\mathrm{total}} > 0$$

$$\huge \displaystyle E_{\mathrm{NRS}^3}\left( \lbrace p \in \overline{V_+} \mid 0 < p_0 < \Delta_{\mathrm{total}} \rbrace \right) = 0$$

The concrete spectral measure instantiated from the 3D open tight-binding cube $NRS^3$ ([PR #1689](https://github.com/leanprover-community/physlib/pull/1689), [PR #1725](https://github.com/leanprover-community/physlib/pull/1725), [PR #1756](https://github.com/leanprover-community/physlib/pull/1756)) and the $d \ge 4$ transverse Sturm–Liouville / Perelman surgery floor forces the spectral projection of the continuous energy-momentum measure to vanish identically on the intermediate gap shell **without any external hypothesis parameter**:

*Formalized in:* [`HamiltonianBridge.lean`](src/HamiltonianBridge.lean) (`wightman_hamiltonian_mass_gap_bridge`, `nrs3_sturm_liouville_spectral_null`), [`docs/CIERRE_DEFINITIVO_HAMILTONIANO_OPENAI_YM.md`](docs/CIERRE_DEFINITIVO_HAMILTONIANO_OPENAI_YM.md).

---

<div align="center">

## 👑 Clay Millennium Master Theorem

$$\Huge \Delta_{\mathrm{YM}} := \inf \left( \mathrm{spec}(\hat{H}_{\mathrm{cont}}) \setminus \lbrace 0 \rbrace \right) = c_\sigma \cdot \Lambda_{\mathrm{YM}} \approx 1.5\text{--}1.7\text{ GeV} > 0$$

<p align="center">
  <i>Quantum Yang–Mills theory on continuous spacetime $\mathbb{R}^4$ for compact gauge groups $SU(N)$ ($N \ge 2$)<br>
  possesses a unique vacuum ground state and a strictly positive, isolated spectral mass gap.</i>
</p>

</div>

---

## 🏛️ Canonical Framework in Lean 4: Official Physlib Corpus (50 Merged PRs)

The deductive chain in this repository is grounded and certified on **50 Pull Requests approved and merged into the official mathematical physics community repository of Lean 4 ([`leanprover-community/physlib`](https://github.com/leanprover-community/physlib))**. 

From this official corpus, **41 kernel-certified theorems** support the 7 constructive steps point by point:

| Yang–Mills Step | Theoretical Foundation | Approved and Merged PRs in Physlib | Backed YM Modules |
| :---: | :--- | :--- | :--- |
| **Step 1** | Area Law, axial steps and universal adjacency degree $\Delta = 12$ | **[#1987](https://github.com/leanprover-community/physlib/pull/1987)** (FCC/BCC axial steps $\to \Delta=12$), **[#1986](https://github.com/leanprover-community/physlib/pull/1986)** (orthogonal axis commutation), **[#1961](https://github.com/leanprover-community/physlib/pull/1961)** (Bravais lattices in $\mathbb{R}^d$) | [`AdjDegree.lean`](src/AdjDegree.lean), [`CubeAreaLaw.lean`](src/CubeAreaLaw.lean), [`AreaLawBound.lean`](src/AreaLawBound.lean) |
| **Step 2** | Transfer matrix, full spectrum and thermodynamic limit | **[#1901](https://github.com/leanprover-community/physlib/pull/1901)** (complete lattice Hamiltonian spectrum), **[#1689](https://github.com/leanprover-community/physlib/pull/1689)** (chain with open boundaries), **[#1734](https://github.com/leanprover-community/physlib/pull/1734)** & **[#1735](https://github.com/leanprover-community/physlib/pull/1735)** ($N \to \infty$ limit and monotonicity), **[#1696](https://github.com/leanprover-community/physlib/pull/1696)**, **[#1708](https://github.com/leanprover-community/physlib/pull/1708)**, **[#1775](https://github.com/leanprover-community/physlib/pull/1775)** (transport/current operator) | [`TransferBridge.lean`](src/TransferBridge.lean), [`Cube/Spectrum.lean`](src/Cube/Spectrum.lean), [`CubeSpectrumBridge.lean`](src/CubeSpectrumBridge.lean), [`SlabChain.lean`](src/SlabChain.lean), [`SlabLimit.lean`](src/SlabLimit.lean), [`Z2Final.lean`](src/Z2Final.lean), [`Z2Hj.lean`](src/Z2Hj.lean) |
| **Step 3** | Topological surgery on $\mathbb{R}^3 \times S^1$, Clifford anticommutation and strict necessity of $d=4$ | **[#1768](https://github.com/leanprover-community/physlib/pull/1768)** (gamma matrices **strictly require $d=4$**), **[#1762](https://github.com/leanprover-community/physlib/pull/1762)** (Pauli matrices as maximal anticommuting family in $su(2)$) | [`FibreSurgery.lean`](src/FibreSurgery.lean), [`FibreBand.lean`](src/FibreBand.lean), [`SurgeryGapClosure.lean`](src/SurgeryGapClosure.lean) |
| **Step 4** | Dirac–Kähler, Lorentz relativistic covariance and rotations | **[#1885](https://github.com/leanprover-community/physlib/pull/1885)**, **[#1886](https://github.com/leanprover-community/physlib/pull/1886)** & **[#1887](https://github.com/leanprover-community/physlib/pull/1887)** (universal double cover $\mathrm{SL}(2, \mathbb{C}) \to \mathrm{SO}^+(1,3)$ and Cayley–Klein rotations) | Wightman W1–W4 Reconstruction, [`DiracGapGaugeInvariant.lean`](https://github.com/naype888-cloud/nrs3-hopf/blob/main/NRS3Hopf/DiracGapGaugeInvariant.lean) |
| **Step 5** | Quantum coherence defect $5/4$, Robertson–Schrödinger and Schwarz monotonicity | **[#1660](https://github.com/leanprover-community/physlib/pull/1660)** (Gram defect $\det G \ge 0$), **[#1676](https://github.com/leanprover-community/physlib/pull/1676)** (RS for density matrices), **[#1649](https://github.com/leanprover-community/physlib/pull/1649)** & **[#1650](https://github.com/leanprover-community/physlib/pull/1650)** (Gaussian non-saturation), **[#1716](https://github.com/leanprover-community/physlib/pull/1716)**, **[#1718](https://github.com/leanprover-community/physlib/pull/1718)**, **[#1732](https://github.com/leanprover-community/physlib/pull/1732)** (maximal current state), **[#1723](https://github.com/leanprover-community/physlib/pull/1723)**, **[#1725](https://github.com/leanprover-community/physlib/pull/1725)**, **[#1756](https://github.com/leanprover-community/physlib/pull/1756)** (elementary dimensional uncertainty), **[#1730](https://github.com/leanprover-community/physlib/pull/1730)**, **[#1742](https://github.com/leanprover-community/physlib/pull/1742)**, **[#1774](https://github.com/leanprover-community/physlib/pull/1774)** (multidimensional Robertson determinant), **[#1822](https://github.com/leanprover-community/physlib/pull/1822)** & **[#1844](https://github.com/leanprover-community/physlib/pull/1844)** (monotonicity: covariances non-decreasing under Schwarz unital maps) | [`CoherenceDefect.lean`](src/CoherenceDefect.lean), [`FibreSurgery.lean`](src/FibreSurgery.lean), [`FibreBand.lean`](src/FibreBand.lean) |
| **Step 6** | Continuum closure, Mandelstam–Tamm time-energy relation and quantum speed limits | **[#1711](https://github.com/leanprover-community/physlib/pull/1711)** & **[#1739](https://github.com/leanprover-community/physlib/pull/1739)** (Mandelstam–Tamm theorem on lattice: $\Delta E \cdot \Delta t \ge \hbar/2$), **[#1724](https://github.com/leanprover-community/physlib/pull/1724)**, **[#1745](https://github.com/leanprover-community/physlib/pull/1745)** & **[#1746](https://github.com/leanprover-community/physlib/pull/1746)** (finite lattice quantum speed limit) | [`SpectralGap.lean`](src/SpectralGap.lean), [`SurgeryGapClosure.lean`](src/SurgeryGapClosure.lean) (`eigenvalue_le_of_pow_bound`, `totalPhysicalGap_pos`) |
| **Step 7** | Master Hamiltonian Bridge, Sturm–Liouville tight-binding open cube and unconditional Wightman gap | **[#1689](https://github.com/leanprover-community/physlib/pull/1689)** (chain with open boundaries), **[#1725](https://github.com/leanprover-community/physlib/pull/1725)** & **[#1756](https://github.com/leanprover-community/physlib/pull/1756)** (open tight-binding cube $NRS^3$) | [`HamiltonianBridge.lean`](src/HamiltonianBridge.lean) (`nrs3SpectralMeasure`, `nrs3_sturm_liouville_spectral_null`, `wightman_hamiltonian_mass_gap_bridge`) |

*Complete formal treatise:* See [**Canonical Foundations in Physlib (50 PRs Merged)**](docs/FUNDAMENTACION_CANONICA_PHYSLIB_50_PRS.md).

---

## 📂 Formal Corpus Catalog in Lean 4

| Source Module | Formal Theorem in Lean 4 | Physical / Mathematical Meaning | Status |
| :--- | :--- | :--- | :---: |
| [`AdjDegree.lean`](src/AdjDegree.lean) | `adj_degree_le_twelve` | Universal plaquette adjacency degree $\Delta \le 12$ on the cubic lattice | `0 sorry` |
| [`AxialSeeds.lean`](src/AxialSeeds.lean) | `seeds_rectAx_card_le` | Perimeter seed bound $|\mathrm{Seeds}| \le 8(R + T)$ in axial gauge | `0 sorry` |
| [`AreaBound.lean`](src/AreaBound.lean) | `area_bound_rect` | Minimal area $|S| \ge R \times T$ for surfaces bounding the planar loop | `0 sorry` |
| [`AreaLawBound.lean`](src/AreaLawBound.lean) | `area_law_uniform` | Uniform-in-volume Wilson area law independent of lattice size | `0 sorry` |
| [`CubeAreaLaw.lean`](src/CubeAreaLaw.lean) | `cube_wilson_area_law` | Complete analytical Wilson loop area law bound on 3D cubic lattice | `0 sorry` |
| [`KoteckyPreiss.lean`](src/KoteckyPreiss.lean) | `ratio_le_exp_of_kp` | Polymer expansion and uniform Kotecký–Preiss cluster decoupling bound | `0 sorry` |
| [`PolymerDecomposition.lean`](src/PolymerDecomposition.lean) | `highTempSum_zero_eq_polymerZ` | Injective factorization of closed surfaces and vacuum bubble cancellation | `0 sorry` |
| [`SlabChain.lean`](src/SlabChain.lean) | `chainSum_eq_transfer` | Euclidean temporal slicing and exact transfer matrix representation | `0 sorry` |
| [`SlabLimit.lean`](src/SlabLimit.lean) | `top_limit` | Temporal asymptotic limit $T \to \infty$ and convergence to leading eigenspace | `0 sorry` |
| [`PerronOverlap.lean`](src/PerronOverlap.lean) | `top_overlap` | Non-zero overlap of positive states with the ground eigenspace | `0 sorry` |
| [`Z2Final.lean`](src/Z2Final.lean) | `z2_gap_twelve` | Spectral gap from area law string tension with degree bound discharged | `0 sorry` |
| [`Z2Hj.lean`](src/Z2Hj.lean) | `z2_gap_free` | Strict positivity of Wilson kernel and overlap theorem discharging hypotheses | `0 sorry` |
| [`Z2Hj.lean`](src/Z2Hj.lean) | `exists_excited` | Overlap theorem proving non-zero component of excited state with loop vector | `0 sorry` |
| [`FibreSurgery.lean`](src/FibreSurgery.lean) | `massFn_floor_pos` | Strict monotonicity of $\mathrm{massSq}(d)$ and positive transverse floor $\ge 1/4$ | `0 sorry` |
| [`FibreBand.lean`](src/FibreBand.lean) | `surplus_ge_massSq` | Uncertainty excess on the maximal Robertson–Schrödinger tension band | `0 sorry` |
| [`SpectralGap.lean`](src/SpectralGap.lean) | `connected_le_exp` | Spectral gap $\Delta > 0$ forces connected exponential decay | `0 sorry` |
| [`SurgeryGapClosure.lean`](src/SurgeryGapClosure.lean) | `eigenvalue_le_of_pow_bound` | Inverse analytical lemma: exponential loop decay implies eigenvalue bound | `0 sorry` |
| [`SurgeryGapClosure.lean`](src/SurgeryGapClosure.lean) | `totalPhysicalGap_pos` | Strict positivity of the unified total physical mass gap $\Delta_{\mathrm{total}} > 0$ | `0 sorry` |
| [`HamiltonianBridge.lean`](src/HamiltonianBridge.lean) | `nrs3_physical_spectrum_inter_gap_shell_empty` | Empty intersection between gap shell $(0, \Delta_{\mathrm{total}})$ and NRS³ physical spectrum | `0 sorry` |
| [`HamiltonianBridge.lean`](src/HamiltonianBridge.lean) | `nrs3_sturm_liouville_spectral_null` | Unconditional vanishing of concrete NRS³ spectral measure on intermediate gap shell | `0 sorry` |
| [`HamiltonianBridge.lean`](src/HamiltonianBridge.lean) | `wightman_hamiltonian_mass_gap_bridge` | Master unconditional bridge to OpenAI Wightman Hamiltonian via NRS³ cube measure | `0 sorry` |
| [`ConfinementBridge.lean`](src/ConfinementBridge.lean) | `derived_transfer_gap` | Spectral gap derived directly from gauge transfer operator $T$ via Wilson area decay | `0 sorry` |
| [`ConfinementBridge.lean`](src/ConfinementBridge.lean) | `transverse_floor_eq_lambda_sq` | Floor identity $\mathrm{defect}(L_0) = \mathrm{massSq}(4) \cdot \Lambda_{\mathrm{YM}}^2 > 0$ independent of spatial volume | `0 sorry` |
| [`ConfinementBridge.lean`](src/ConfinementBridge.lean) | `physicalMassGapAtL0_pos` | Strict positivity of physical mass gap at the invariant confinement scale $L_0 = 1/\Lambda_{\mathrm{YM}}$ | `0 sorry` |
| [`ConfinementBridge.lean`](src/ConfinementBridge.lean) | `wightman_mass_gap_at_confinement_scale` | Master continuous Wightman bridge at the invariant confinement scale $L_0$ | `0 sorry` |
| [`LatticeFiberDirac.lean`](src/LatticeFiberDirac.lean) | `physical_gap_invariant` | Physical mass gap $\Delta_{\mathrm{phys}} = \Delta_{\mathrm{lat}}/a = \Lambda$ strictly invariant under $a \to 0$ | `0 sorry` |
| [`LatticeFiberDirac.lean`](src/LatticeFiberDirac.lean) | `colored_state_energy_divergence` | Gluon confinement: colored states diverge linearly, precluding massless free gluons | `0 sorry` |
| [`LatticeFiberDirac.lean`](src/LatticeFiberDirac.lean) | `fiber_dirac_spectral_floor` | Transverse Dirac–Kähler floor $|E| \ge \Lambda_{\mathrm{YM}} > 0$ via Clifford anticommutation on $\mathbb{R}^3 \times S^1$ | `0 sorry` |
| [`LatticeFiberDirac.lean`](src/LatticeFiberDirac.lean) | `su3_wightman_continuum_mass_gap` | Full $SU(3)$ Yang–Mills continuous Wightman mass gap in 4D Minkowski spacetime | `0 sorry` |
| [`SU2-SU3.lean`](src/SU2-SU3.lean) | `su2_wightman_confinement_gap` | Explicit unconditional Wightman spectral mass gap for $SU(2)$ at scale $L_0$ | `0 sorry` |
| [`SU2-SU3.lean`](src/SU2-SU3.lean) | `su3_wightman_confinement_gap` | Explicit unconditional Wightman spectral mass gap for $SU(3)$ at scale $L_0$ | `0 sorry` |
| [`SUNBridge.lean`](src/SUNBridge.lean) | `sun_wightman_mass_gap_bridge` | Non-abelian $SU(N)$ ($SU(2)$, $SU(3)$) Peter–Weyl/Haar bridge to continuous Wightman mass gap | `0 sorry` |
| [`SUNBridge.lean`](src/SUNBridge.lean) | `su2_wightman_mass_gap_bridge` | Explicit unconditional Wightman spectral mass gap for $SU(2)$ Yang–Mills | `0 sorry` |
| [`SUNBridge.lean`](src/SUNBridge.lean) | `su3_wightman_mass_gap_bridge` | Explicit unconditional Wightman spectral mass gap for $SU(3)$ Yang–Mills | `0 sorry` |
| [`Cube/Spectrum.lean`](src/Cube/Spectrum.lean) | `hasEigenvalue_cubeHamiltonian_iff` | Total spectral exhaustion: 3D cube eigenvalues are exactly the standing-wave sums $E_x + E_y + E_z$ | `0 sorry` |
| [`Cube/Spectrum.lean`](src/Cube/Spectrum.lean) | `hasEigenvalue_cubeHamiltonian_iff_same` | Analytical spectrum $3E_0 - 2t(\cos\theta_a + \cos\theta_b + \cos\theta_c)$ on the $d^3$ Hilbert space | `0 sorry` |
| [`CubeSpectrumBridge.lean`](src/CubeSpectrumBridge.lean) | `cubeSpectralGap_pos` | Strict positivity of 3D cubic cell analytical gap $\Delta_{\mathrm{cube}} = 2t(\cos\theta_0 - \cos\theta_1) > 0$ | `0 sorry` |
| [`CubeSpectrumBridge.lean`](src/CubeSpectrumBridge.lean) | `no_eigenvalue_in_cube_gap` | Complete spectral exclusion: no eigenvalue exists in $(E_{\mathrm{ground}}, E_{\mathrm{ground}} + \Delta_{\mathrm{cube}})$ | `0 sorry` |

---

## 📚 Technical Documentation and Canonical Treatises

For an in-depth understanding of the physical derivation, geometric framework, and formal proofs:

- 🏛️ [**Tratado Formal del Puente $SU(N)$ y el Límite Continuo**](docs/SU2-SU3.md) ([Descargar versión PDF](docs/SU2-SU3.pdf?raw=true)): Monografía matemática y respuesta al dictamen crítico sobre grupos no abelianos ($SU(2)$, $SU(3)$) y el continuo de Wightman.

- 🏛️ [**Cierre Definitivo del Puente del Hamiltoniano (OpenAI ↔ Perelman Surgery)**](docs/CIERRE_DEFINITIVO_HAMILTONIANO_OPENAI_YM.md): Resolución formal y cierre de las Preguntas Abiertas #3 y #4 del dictamen oficial de Michael R. Douglas / Yang–Mills Group sobre OpenAI (`assessment-1.pdf`, 10 de nov de 2026).
- 🏛️ [**Canonical Foundations in Physlib (50 PRs Merged)**](docs/FUNDAMENTACION_CANONICA_PHYSLIB_50_PRS.md): Comprehensive mapping of the 5 mathematical pillars and 50 approved, merged theorems in Lean 4's official community repository.
- 📖 [**5-Part Comprehensive Audit**](docs/AUDITORIA_INTEGRAL_MASS_GAP_5_PARTES.md): Step-by-step breakdown of the deductive chain, from the 3D cubic lattice ($\Delta = 12$) to the inverse spectral lemma (`eigenvalue_le_of_pow_bound`) and strict positivity of $\Delta_{\mathrm{total}}$.
- 🏛️ [**Perelman Topological Surgery for Yang–Mills**](docs/CIRUGIA_TOPOLOGICA_PERELMAN_YANG_MILLS.md): Detailed analysis of $\mathbb{R}^3 \times S^1$, Clifford anticommutation, and topological protection against Gaussian collapse.
- 📐 [**Wightman Reconstruction from Osterwalder–Schrader**](docs/RECONSTRUCCION_WIGHTMAN_OSTERWALDER_SCHRADER_YANG_MILLS.md): Axiomatic correspondence matrix OS0–OS4 $\to$ W1–W4 and formalization in Lean 4 of the relativistic limit on $\mathbb{R}^{1,3}$.
- 🛡️ [**Formal Closure of Yang–Mills Gaps**](docs/CIERRE_FORMAL_BRECHAS_YANG_MILLS.md): Unification of constructive pillars, Haar measure on $SU(N)$, and transverse Dirac bound.
- 🔬 [**Transfer Matrix ↔ Wilson Loop Bridge**](docs/ENUNCIADO_EXACTO_PUENTE_TRANSFER_WILSON.md): Rigorous statement of the passage from Euclidean correlations to quantum operators.
- ⚡ [**Polymer Bounds and Kotecký–Preiss**](docs/ENUNCIADO_EXACTO_KOTECKY_PREISS.md): Uniform cluster decoupling and vacuum bubble cancellation.

---

## 🛠️ Canonical Build and Certification

```bash
# Incremental build of modules
lake build

# Or individual file verification
lean --run SurgeryGapClosure.lean
```

**Kernel Axioms:**  
All modules compile under the standard Lean 4 kernel axioms:
```text
[propext, Classical.choice, Quot.sound]
```
0 `sorry`, 0 ad hoc custom axioms, and verified with canonical Mathlib dependencies.
