<div align="center">

# Yang–Mills Spectral Mass Gap
### Constructive Topological Surgery, Transfer Bridge & Quantum Coherence Defect

**Eduardo Nava-Hernández & José Arturo Nava-Hernández**  
*feat. Grigori Perelman Surgery Method*

[![Lean 4](https://img.shields.io/badge/Lean_4-v4.33.0-blue.svg?style=flat-square)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/Mathlib-verified-2ea44f.svg?style=flat-square)](https://github.com/leanprover-community/mathlib4)
[![Kernel Status](https://img.shields.io/badge/Kernel-0%20sorry%20%7C%20Certified-brightgreen.svg?style=flat-square)]()
[![Axioms](https://img.shields.io/badge/Axioms-[propext,_choice,_sound]-informational.svg?style=flat-square)]()
[![License](https://img.shields.io/badge/License-NRS%201.0.0-purple.svg?style=flat-square)]()

---

<p align="center">
  <b>Formalización matemática constructiva en Lean 4 del Spectral Mass Gap de Yang–Mills</b><br>
  <i>Variedad fibrada $\mathcal{M}_4 = \mathbb{R}^3 \times S^1 \to \mathbb{R}^4$, matriz de transferencia y defecto cuántico Robertson–Schrödinger</i>
</p>

</div>

---

## 🏛️ Mosaico de Pilares Matemáticos / Core Pillars

<table>
  <tr>
    <td width="50%" valign="top">
      <h3>📐 1. Ley del Área Uniforme en el Retículo</h3>
      <p>Confinamiento riguroso en red cúbica 3D con grado de adyacencia universal $\Delta = 12$ y semillas $|\mathrm{Seeds}| \le 8(R + T)$:</p>
      $$\langle W(R \times T) \rangle \le \left(\frac{\tanh \beta}{t'}\right)^{R \cdot T} (1 + a)^{8(R + T)}$$
      $$\sigma(\beta) \ge \ln\left(\frac{t'}{\tanh \beta}\right) > 0$$
      <p><i>Formalizado en:</i> <code>CubeAreaLaw.lean</code>, <code>AreaLawBound.lean</code>, <code>AdjDegree.lean</code></p>
    </td>
    <td width="50%" valign="top">
      <h3>⚡ 2. Puente Espectral de Transferencia</h3>
      <p>Por el <b>Teorema Inverso Espectral de Potencias</b> sobre la matriz de transferencia $T = e^{-a \hat{H}}$:</p>
      $$\forall k \in \mathbb{N}, \ \left(\frac{\mu_1}{\mu_0}\right)^k \le \frac{C}{|c_1|^2} \left(e^{-\sigma R}\right)^k \implies \frac{\mu_1}{\mu_0} \le e^{-\sigma R} < 1$$
      $$\Delta_{\mathrm{glue}} = E_1 - E_0 = -\frac{1}{a} \ln\left(\frac{\mu_1}{\mu_0}\right) \ge \frac{\sigma \cdot R}{a} > 0$$
      <p><i>Formalizado en:</i> <code>SurgeryGapClosure.lean</code>, <code>Z2Final.lean</code>, <code>Z2Hj.lean</code></p>
    </td>
  </tr>
  <tr>
    <td width="50%" valign="top">
      <h3>🛡️ 3. Defecto Cuántico de Fibra</h3>
      <p>Torsión simpléctica de Robertson–Schrödinger en $\mathcal{M}_4 = \mathbb{R}^3 \times S^1$ que bloquea el aplanamiento gaussiano:</p>
      $$\frac{\det \Sigma}{|\det \Omega|} = 1 + \mathrm{massSq}(4) = 1 + \frac{1}{4} = \frac{5}{4} > 1$$
      $$\{A[U], M_w\} = 0 \implies \sqrt{\mathrm{piso}} \ge \frac{1}{2a} > 0$$
      <p><i>Formalizado en:</i> <code>FibreSurgery.lean</code>, <code>FibreBand.lean</code>, <code>SurgeryGapClosure.lean</code></p>
    </td>
    <td width="50%" valign="top">
      <h3>🔬 4. Dirac–Kähler para Bosones (Gluones)</h3>
      <p>Anticonmutación de Clifford sobre el álgebra exterior de formas diferenciales $\Omega^*(\mathcal{M})$:</p>
      $$\mathcal{D}_A = d_A + d_A^*, \qquad \mathcal{D}_A^2 = \Delta_{\mathrm{Hodge}}$$
      $$\langle \omega, \Delta_{\mathrm{Hodge}} \omega \rangle \ge \left(\frac{2}{\pi} \frac{\mathrm{holGap}(\theta)}{L}\right)^2 \|\omega\|^2 > 0$$
      <p><i>Desigualdad de operadores en todo $L^2$:</i> $\Delta_{\mathrm{Hodge}} \ge \Delta_{\mathrm{fibra}}^2 \cdot \mathbb{I} > 0$</p>
    </td>
  </tr>
</table>

---

<div align="center">

## 🌐 Teorema del Cierre Total y Límite Continuo

$$\mathbf{\Delta_{\mathrm{total}} = \min\big(\Delta_{\mathrm{glue}}, \, \sqrt{\mathrm{piso}}\big) = \min\left(c_\sigma \Lambda_{\mathrm{YM}}, \, \Delta_{\mathrm{fibra}}\right) > 0}$$

Al descompactificar la fibra hacia el espacio plano $\mathbb{R}^4$ ($L \to \infty$), el confinamiento espacial $\mathbb{R}^3$ gobierna el continuo:

$$\Huge \mathbf{\inf \big( \mathrm{spec}(\hat{H}) \setminus \{0\} \big) = \lim_{L \to \infty} \Delta_{\mathrm{total}} = \Delta_{\mathrm{glue}} = c_\sigma \cdot \Lambda_{\mathrm{YM}} > 0}$$

</div>

---

## 📂 Catálogo del Corpus Formalizado en Lean 4

| Módulo Fuente | Teorema Formal en Lean 4 | Significado Físico / Matemático | Estado |
| :--- | :--- | :--- | :---: |
| [`AdjDegree.lean`](AdjDegree.lean) | `adj_degree_le_twelve` | Grado de adyacencia universal de plaquetas $\Delta \le 12$ en retículo cúbico | `0 sorry` |
| [`AxialSeeds.lean`](AxialSeeds.lean) | `seeds_rectAx_card_le` | Cota de semillas perimetrales $|\mathrm{Seeds}| \le 8(R + T)$ en gauge axial | `0 sorry` |
| [`AreaBound.lean`](AreaBound.lean) | `area_bound_rect` | Área mínima $|S| \ge R \times T$ para superficies que apoyan en el lazo plano | `0 sorry` |
| [`AreaLawBound.lean`](AreaLawBound.lean) | `area_law_uniform` | Ley del área de Wilson uniforme e independiente del volumen del retículo | `0 sorry` |
| [`CubeAreaLaw.lean`](CubeAreaLaw.lean) | `cube_wilson_area_law` | Cota analítica completa del lazo de Wilson en la red cúbica 3D | `0 sorry` |
| [`KoteckyPreiss.lean`](KoteckyPreiss.lean) | `ratio_le_exp_of_kp` | Expansión de polímeros y cota uniforme de desacoplamiento de Kotecký–Preiss | `0 sorry` |
| [`PolymerDecomposition.lean`](PolymerDecomposition.lean) | `highTempSum_eq_polymerZ` | Factorización inyectiva de superficies cerradas y cancelación de burbujas | `0 sorry` |
| [`SlabChain.lean`](SlabChain.lean) | `chainSum_eq_transfer` | Rebanado temporal euclídeo y representación exacta por matriz de transferencia | `0 sorry` |
| [`SlabLimit.lean`](SlabLimit.lean) | `top_limit` | Límite asintótico temporal $T \to \infty$ y convergencia al autoespacio principal | `0 sorry` |
| [`PerronOverlap.lean`](PerronOverlap.lean) | `top_overlap` | Solapamiento no nulo de estados positivos con el autoespacio fundamental | `0 sorry` |
| [`Z2Final.lean`](Z2Final.lean) | `z2_gap` | Deducción de la brecha espectral a partir de la tensión de cuerda del área | `0 sorry` |
| [`Z2Hj.lean`](Z2Hj.lean) | `z2_gap_free` | Positividad estricta del núcleo de Wilson y descarga de hipótesis de solapamiento | `0 sorry` |
| [`FibreSurgery.lean`](FibreSurgery.lean) | `massFn_floor_pos` | Monotonía estricta de $\mathrm{massSq}(d)$ y piso transversal positivo $\ge 1/4$ | `0 sorry` |
| [`FibreBand.lean`](FibreBand.lean) | `surplus_ge` | Exceso de incertidumbre en la banda de máxima tensión Robertson–Schrödinger | `0 sorry` |
| [`SpectralGap.lean`](SpectralGap.lean) | `connected_le_exp` | La brecha espectral $\Delta > 0$ fuerza el decaimiento exponencial conexo | `0 sorry` |
| [`SurgeryGapClosure.lean`](SurgeryGapClosure.lean) | `eigenvalue_le_of_pow_bound` | Lema analítico inverso: cota exponencial de lazos implica cota de autovalor | `0 sorry` |
| [`SurgeryGapClosure.lean`](SurgeryGapClosure.lean) | `totalPhysicalGap_pos` | Positividad estricta de la brecha espectral total unificada $\Delta_{\mathrm{total}} > 0$ | `0 sorry` |

---

## 🛠️ Compilación y Certificación Canónica

```bash
# Compilación canónica incremental de los módulos
lake build

# O verificación de archivo individual
lean --run SurgeryGapClosure.lean
```

**Axiomas del Kernel:**  
Todos los módulos compilan bajo los axiomas estándar del kernel de Lean 4:
```text
[propext, Classical.choice, Quot.sound]
```
Sin `sorry`, sin axiomas adicionales ad hoc, y con dependencias canónicas en Mathlib.
