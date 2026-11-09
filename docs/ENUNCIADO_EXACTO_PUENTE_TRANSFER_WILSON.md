# Enunciado Lean Exacto: Puente Matriz de Transferencia ↔ Lazo de Wilson

**Autor:** Antigravity & Eduardo Nava-Hernández  
**Ubicación:** `docs/ENUNCIADO_EXACTO_PUENTE_TRANSFER_WILSON.md` y `lattice-gauge-gap/docs/`  
**Estado:** Demostrado y verificado formalmente en Lean 4 (0 sorry, axiomas canónicos del kernel).

---

## 1. El Puente Formalizado

En [`SpectralGap.lean`](../SpectralGap.lean):
* `connected_le_exp`: Si $\mu_1 < \mu_0$, entonces la correlación conectada decae como $e^{-\Delta k}$ con $\Delta = \ln(\mu_0 / \mu_1)$.

En [`SurgeryGapClosure.lean`](../SurgeryGapClosure.lean):
* `eigenvalue_le_of_pow_bound`: Si $\mu^k \le C \cdot \alpha^k$ para todo $k \in \mathbb{N}$ con $0 \le \alpha < \mu$, entonces $\mu \le \alpha$.

El puente está completamente cerrado mediante la **representación por Matriz de Transferencia del Lazo de Wilson axial** $R \times k$.

---

## 2. Definiciones Matemáticas en Lean 4

Sea $\mathcal{H}$ el espacio de Hilbert de estados de gauge espacial en un corte temporal fijo.  
Sea $T : \mathcal{H} \to \mathcal{H}$ el operador de transferencia (hermitiano y definido positivo).

1. **Estado de Vacío ($\Omega$):**
   $$T \Omega = \mu_0 \Omega, \quad \mu_0 > 0, \quad \|\Omega\| = 1.$$
2. **Estado de Cuerda Espacial ($\psi_R$):**
   Para un lazo de ancho espacial $R \ge 1$, $\psi_R \in \mathcal{H}$ es el estado obtenido al actuar con una línea de Wilson espacial de longitud $R$ sobre el vacío:
   $$\psi_R = \hat{V}_R \Omega.$$
3. **Ortogonalidad al Vacío (Invarianza de Carga / Simetría de Centro):**
   Bajo la simetría de centro global o la ley de Gauss en los extremos de la cuerda abierta:
   $$\langle \Omega, \psi_R \rangle = 0 \quad (\text{i.e. } \text{coeff}(i_0, \psi_R) = 0).$$
4. **Valor Esperado del Lazo Temporal $R \times k$:**
   $$\langle W(R \times k) \rangle = \frac{\langle \psi_R, T^k \psi_R \rangle}{\mu_0^k \, \|\psi_R\|^2}.$$

---

## 3. Teoremas de Cierre Formal (0 sorry)

La cadena de teoremas que cierra formalmente el puente en Lean 4:

1. **`SlabChain.lean`:** Representación de rebanadas temporales como elementos de matriz de potencias de $T$ (`chainSum_eq`, `chainSum_eq_transfer`).
2. **`SlabLimit.lean`:** Paso al límite $N \to \infty$ proyectando sobre el subespacio de autovalores top (`top_limit`).
3. **`PerronOverlap.lean`:** Solapamiento estricto del vector positivo con el autoespacio principal (`top_overlap`).
4. **`AxialArea.lean`:** Cota de área minimal $R \cdot k$ en gauge axial (`area_bound_rectAx`).
5. **`AxialSeeds.lean`:** Cota universal de plaquetas semilla $\#\text{Seeds} \le 8R$ independiente de la extensión temporal $k$ (`seeds_rectAx_card_le`).
6. **`Z2WilsonGap.lean` & `Z2Final.lean`:** Cierre del gap espectral neto $\ln(\mu_0 / \mu_j) \ge R \cdot \ln(t' / \tanh \beta)$ (`z2_gap_twelve`).
7. **`Z2Hj.lean`:** Descarga completa de la hipótesis de solapamiento $h_j$ demostrando que el operador $K$ es positivo definido por producto de Kronecker (`z2_gap_free`).

---

## 4. Estado de Verificación

* El puente deriva constructivamente el gap espectral a partir de la ley del área de Wilson y la positividad semidefinida del operador de transferencia.
* Verificado con 0 `sorry` bajo los axiomas lógicos estándar del kernel Lean 4.
