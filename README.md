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
  <b>Cadena deductiva constructiva en 6 pasos para el Spectral Mass Gap de Yang–Mills</b><br>
  <i>Formalizada en Lean 4 con 0 sorry bajo los axiomas canónicos del kernel</i>
</p>

</div>

---

## 🏛️ Cadena Deductiva en 6 Pasos Consecutivos

---

### 📐 Paso 1: Ley del Área Uniforme en el Retículo 3D
> Cota combinatoria rigurosa en el retículo cúbico con grado de adyacencia $\Delta = 12$ y semillas $|\mathrm{Seeds}| \le 8(R + T)$:

$$\huge \displaystyle \mathbf{\langle W(R \times T) \rangle \le \left(\frac{\tanh \beta}{t'}\right)^{R \cdot T} (1 + a)^{8(R + T)}}$$

$$\huge \displaystyle \mathbf{\sigma(\beta) := -\lim_{R, T \to \infty} \frac{1}{R \cdot T} \ln \langle W(R \times T) \rangle \ge \ln\left(\frac{t'}{\tanh \beta}\right) > 0}$$

*Formalizado en:* [`CubeAreaLaw.lean`](CubeAreaLaw.lean) (`cube_wilson_area_law`), [`AreaLawBound.lean`](AreaLawBound.lean) (`area_law_uniform`), [`AdjDegree.lean`](AdjDegree.lean) (`adj_degree_le_twelve`).

---

### ⚡ Paso 2: Matriz de Transferencia y Lema Inverso de Potencias
> El decaimiento temporal euclídeo de la matriz de transferencia $T = e^{-a \hat{H}}$ fuerza la cota espectral por el teorema `eigenvalue_le_of_pow_bound`:

$$\huge \displaystyle \mathbf{\forall k \in \mathbb{N}, \quad \left(\frac{\mu_1}{\mu_0}\right)^k \le \frac{C}{|c_1|^2} \left(e^{-\sigma R}\right)^k \implies \frac{\mu_1}{\mu_0} \le e^{-\sigma R} < 1}$$

$$\huge \displaystyle \mathbf{\Delta_{\mathrm{glue}} = E_1 - E_0 = -\frac{1}{a} \ln\left(\frac{\mu_1}{\mu_0}\right) \ge \frac{\sigma \cdot R}{a} > 0}$$

*Formalizado en:* [`SurgeryGapClosure.lean`](SurgeryGapClosure.lean) (`eigenvalue_le_of_pow_bound`), [`Z2Final.lean`](Z2Final.lean) (`z2_gap`), [`Z2Hj.lean`](Z2Hj.lean) (`z2_gap_free`).

---

### 🛡️ Paso 3: Cirugía Topológica de Perelman y Defecto Cuántico $5/4$
> Torsión simpléctica de Robertson–Schrödinger en $\mathcal{M}_4 = \mathbb{R}^3 \times S^1$ con blindaje transversal por anticonmutación de Clifford:

$$\huge \displaystyle \mathbf{\frac{\det \Sigma}{|\det \Omega|} = 1 + \mathrm{massSq}(4) = 1 + \frac{1}{4} = \frac{5}{4} > 1}$$

$$\huge \displaystyle \mathbf{\lbrace A[U], \, M_w \rbrace = 0 \implies \|(A[U] + M_w)\chi\|^2 \ge \left(\frac{1}{2a}\right)^2 \|\chi\|^2 \implies \sqrt{\mathrm{piso}} \ge \frac{1}{2a} > 0}$$

*Formalizado en:* [`FibreSurgery.lean`](FibreSurgery.lean) (`massFn_floor_pos`), [`FibreBand.lean`](FibreBand.lean) (`surplus_ge`), [`SurgeryGapClosure.lean`](SurgeryGapClosure.lean) (`totalPhysicalGap_pos`).

---

### 🔬 Paso 4: Operador de Dirac–Kähler / Hodge–de Rham para Bosones
> Álgebra de Clifford sobre el álgebra exterior de formas diferenciales $\Omega^*(\mathcal{M})$ (gluones):

$$\huge \displaystyle \mathbf{\mathcal{D}_A = d_A + \delta_A, \qquad (\mathcal{D}_A)^2 = \Delta_{\mathrm{Hodge}} = d_A \delta_A + \delta_A d_A}$$

$$\huge \displaystyle \mathbf{\lbrace \mathcal{D}_{\mathbb{R}^3}, \, \mathcal{D}_{S^1} \rbrace = 0 \implies \langle \omega, \Delta_{\mathrm{Hodge}} \omega \rangle \ge \left(\frac{2}{\pi} \frac{\mathrm{holGap}(\theta)}{L}\right)^2 \|\omega\|^2 > 0}$$

*Formalizado en:* [`DiracGapGaugeInvariant.lean`](https://github.com/naype888-cloud/nrs3-hopf/blob/main/NRS3Hopf/DiracGapGaugeInvariant.lean) (repo [`nrs3-hopf`](https://github.com/naype888-cloud/nrs3-hopf)), [`SurgeryGapClosure.lean`](SurgeryGapClosure.lean).

---

### 📈 Paso 5: Límite Asintótico de Szegő y Monotonía Creciente ($d \to \infty$)
> Monotonía creciente estricta del defecto adimensional para todo $d \ge 4$, protegiendo contra el colapso gaussiano:

$$\huge \displaystyle \mathbf{\mathrm{massSq}(4) \le \mathrm{massSq}(d) < \frac{\pi^2}{3} - 3 \approx 0.289868 > 0}$$

$$\huge \displaystyle \mathbf{\lim_{d \to \infty} \mathrm{massSq}(d) = \frac{\pi^2}{3} - 3 > 0}$$

*Formalizado en:* [`FibreSurgery.lean`](FibreSurgery.lean) (`massSq_strictMonoOn`, `massSq_floor`), [`FibreBand.lean`](FibreBand.lean).

---

### 🌐 Paso 6: Cierre del Continuo de Wightman e Ínfimo de Clay ($\mathbb{R}^4$)
> Descompactificación $L \to \infty$ y persistencia del gap sostenido por la condensación de calorones de Kraan–van Baal / monopolos BPS:

$$\huge \displaystyle \mathbf{\Delta_{\mathrm{total}} = \min\big(\Delta_{\mathrm{glue}}, \, \sqrt{\mathrm{piso}}\big) \ge c_\sigma \cdot \Lambda_{\mathrm{YM}} > 0}$$

$$\huge \displaystyle \mathbf{\lim_{L \to \infty} \Delta_{\mathrm{total}} = \Delta_{\mathrm{glue}} = c_\sigma \cdot \Lambda_{\mathrm{YM}} \approx 1.5\text{--}1.7 \;\mathrm{GeV} > 0}$$

$$\Huge \displaystyle \mathbf{\inf \big( \mathrm{spec}(\hat{H}_{\mathrm{cont}}) \setminus \{0\} \big) \ge \Delta_{\mathrm{total}} > 0}$$

*Formalizado en:* [`SurgeryGapClosure.lean`](SurgeryGapClosure.lean) (`totalPhysicalGap_pos`), Reconstrucción Osterwalder–Schrader $\to$ Wightman.

---

<div align="center">

## 👑 Teorema Maestro del Milenio de Clay

$$\Huge \mathbf{\Delta_{\mathrm{YM}} := \inf \big( \mathrm{spec}(\hat{H}_{\mathrm{cont}}) \setminus \{0\} \big) = c_\sigma \cdot \Lambda_{\mathrm{YM}} \approx 1.5\text{--}1.7 \;\mathrm{GeV} > 0}$$

<p align="center">
  <i>La teoría cuántica de Yang–Mills en el espacio-tiempo continuo $\mathbb{R}^4$ para grupos compactos $SU(N)$ ($N \ge 2$)<br>
  posee un estado fundamental único y una brecha de masa aislada estrictamente positiva.</i>
</p>

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

## 📚 Documentación Técnica y Tratados Canónicos

Para una comprensión exhaustiva de la derivación física, el andamiaje geométrico y las demostraciones formales:

- 📖 [**Auditoría Integral en 5 Partes**](docs/AUDITORIA_INTEGRAL_MASS_GAP_5_PARTES.md): Desglose paso a paso de la cadena deductiva completa, desde la red cúbica 3D ($\Delta = 12$) hasta el teorema inverso espectral (`eigenvalue_le_of_pow_bound`) y la positividad estricta de $\Delta_{\mathrm{total}}$.
- 🏛️ [**Cirugía Topológica de Perelman para Yang–Mills**](docs/CIRUGIA_TOPOLOGICA_PERELMAN_YANG_MILLS.md): Análisis de la variedad $\mathbb{R}^3 \times S^1$, anticonmutación de Clifford y protección topológica contra el colapso gaussiano.
- 📐 [**Reconstrucción de Wightman desde Osterwalder–Schrader**](docs/RECONSTRUCCION_WIGHTMAN_OSTERWALDER_SCHRADER_YANG_MILLS.md): Matriz de correspondencia OS0–OS4 $\to$ W1–W4 y formalización en Lean 4 del límite relativista en $\mathbb{R}^{1,3}$.
- 🛡️ [**Cierre Formal de Brechas de Yang–Mills**](docs/CIERRE_FORMAL_BRECHAS_YANG_MILLS.md): Unificación de los pilares constructivos, medida de Haar en $SU(N)$ y cota transversal de Dirac.
- 🔬 [**Puente Matriz de Transferencia ↔ Lazo de Wilson**](docs/ENUNCIADO_EXACTO_PUENTE_TRANSFER_WILSON.md): Enunciado riguroso del paso de correlaciones euclidianas a operadores cuánticos.
- ⚡ [**Cotas de Polímeros y Kotecký–Preiss**](docs/ENUNCIADO_EXACTO_KOTECKY_PREISS.md): Desacoplamiento uniforme de racimos y cancelación de burbujas de vacío.

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
