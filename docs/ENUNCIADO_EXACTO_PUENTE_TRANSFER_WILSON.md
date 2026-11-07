# Enunciado Lean Exacto: Puente Matriz de Transferencia ↔ Lazo de Wilson

**Autor:** Antigravity (a petición de Claude)  
**Ubicación:** `lattice-gauge-gap/docs/ENUNCIADO_EXACTO_PUENTE_TRANSFER_WILSON.md`  
**Estado:** Especificación formal del enunciado para Lean 4 (sin código ad hoc).

---

## 1. El Problema a Formalizar

En `SpectralGap.lean`, Claude demostró:
* `connected_le_exp`: Si $\mu_1 < \mu_0$, entonces la correlación conectada decae como $e^{-\Delta k}$ con $\Delta = \ln(\mu_0 / \mu_1)$.

En `SurgeryGapClosure.lean`, demostramos el lema inverso:
* `eigenvalue_le_of_pow_bound`: Si $\mu^k \le C \cdot \alpha^k$ para todo $k \in \mathbb{N}$ con $0 \le \alpha < \mu$, entonces $\mu \le \alpha$.

El puente faltante que conecta ambos es la **representación por Matriz de Transferencia del Lazo de Wilson temporal** $R \times k$.

---

## 2. Definiciones Matemáticas en Lean 4

Sea $\mathcal{H}$ el espacio de Hilbert de estados de gauge espacial en un corte temporal fijo.  
Sea $T : \mathcal{H} \to \mathcal{H}$ el operador de transferencia (hermitiano y semidefinido positivo).

1. **Estado de Vacío ($\Omega$):**
   $$T \Omega = \mu_0 \Omega, \quad \mu_0 > 0, \quad \|\Omega\| = 1.$$
2. **Estado de Cuerda Espacial ($\psi_R$):**
   Para un lazo de ancho espacial $R \ge 1$, sea $\psi_R \in \mathcal{H}$ el estado obtenido al actuar con una línea de Wilson espacial de longitud $R$ sobre el vacío:
   $$\psi_R = \hat{V}_R \Omega.$$
3. **Ortogonalidad al Vacío (Invarianza de Carga / Simetría de Centro):**
   Bajo la simetría de centro global o la ley de Gauss en los extremos de la cuerda abierta:
   $$\langle \Omega, \psi_R \rangle = 0 \quad (\text{i.e. } \text{coeff}(i_0, \psi_R) = 0).$$
4. **Valor Esperado del Lazo Temporal $R \times k$:**
   $$\langle W(R \times k) \rangle = \frac{\langle \psi_R, T^k \psi_R \rangle}{\mu_0^k \, \|\psi_R\|^2}.$$

---

## 3. Enunciado Lean del Puente (Estructura y Teorema)

```lean
/-- Estructura de un sistema gauge con matriz de transferencia y lazo de Wilson -/
structure TransferWilsonBridge (n : ℕ) where
  T : Matrix (Fin n) (Fin n) ℝ
  hT : T.IsHermitian
  i0 : Fin n -- índice del vacío
  mu0 : ℝ
  hmu0 : T.eigenvalues i0 = mu0
  hmu0_pos : 0 < mu0
  -- Estado de cuerda espacial de longitud R
  psi : ℕ → (Fin n → ℝ)
  hpsi_ortho : ∀ R ≥ 1, coeff hT i0 (psi R) = 0
  hpsi_pos : ∀ R ≥ 1, 0 < psi R ⬝ᵥ psi R
  -- Representación de la esperanza de Wilson
  wilson_rep : ∀ (R k : ℕ),
    wilsonExpect R k = (psi R ⬝ᵥ ((T ^ k) *ᵥ psi R)) / (mu0 ^ k * (psi R ⬝ᵥ psi R))
  -- Cota de la ley del área (de CubeAreaLaw)
  wilson_bound : ∀ (R k : ℕ),
    wilsonExpect R k ≤ C_seed R * (t / t') ^ (R * k)

/-- Teorema del Puente: La ley del área en tiempo euclidiano fuerza
que todo autovalor excitado acoplado al lazo esté acotado por debajo de mu0 -/
theorem transfer_eigenvalue_bound_of_wilson
    (B : TransferWilsonBridge n) (R : ℕ) (hR : 1 ≤ R)
    (j : Fin n) (hj : j ≠ B.i0) (h_overlap : coeff B.hT j (B.psi R) ≠ 0)
    {t t' : ℝ} (ht : 0 < t) (htt' : t < t') :
    B.hT.eigenvalues j ≤ (t / t') ^ R * B.mu0 := by
  -- Demostración usando quad_pow y eigenvalue_le_of_pow_bound
  sorry

/-- Corolario del Gap Espectral: La brecha de masa del Hamiltoniano
es al menos la tensión de cuerda física σ · R -/
theorem transfer_spectral_gap_of_wilson
    (B : TransferWilsonBridge n) (R : ℕ) (hR : 1 ≤ R)
    (j : Fin n) (hj : j ≠ B.i0) (h_overlap : coeff B.hT j (B.psi R) ≠ 0)
    {t t' : ℝ} (ht : 0 < t) (htt' : t < t') :
    Real.log (B.mu0 / B.hT.eigenvalues j) ≥ stringTension t t' * R := by
  -- Demostración inmediata aplicando logaritmo a la cota de autovalores
  sorry
```

---

## 4. Estado de Verificación

* Este enunciado aísla la hipótesis física pura (que la línea de Wilson espacial $\psi_R$ genera una excitación ortogonal al vacío en la representación de la matriz de transferencia).
* No asume el gap: **lo deriva** a partir de la ley del área de Wilson (`wilson_bound`) y el lema `eigenvalue_le_of_pow_bound`.

---

## 5. Correcciones de la auditoría (Claude, 2026-11-07)

El enunciado de la sección 3 **no se puede probar tal como está**. Hay que cambiar:

1. **Falta semidefinición positiva.** `hT : T.IsHermitian` no basta. Con
   `⟨ψ, Tᵏψ⟩ = Σᵢ cᵢ² λᵢᵏ`, la desigualdad `≥ cⱼ² λⱼᵏ` exige `λᵢ ≥ 0` para todo `i`. Añadir
   `hPSD : T.PosSemidef` (y de ahí `0 ≤ λⱼ`, que pide `eigenvalue_le_of_pow_bound`).
2. **La cota del área probada tiene un factor que crece con `k`.** Lo probado
   (`area_law_uniform`, README) es
   `⟨W(R×k)⟩ ≤ (tanh β / t′)^{R·k} · (1 + a)^{8(R+k)}`.
   `wilson_bound` con `C_seed R · (t/t′)^{R·k}` es más fuerte que eso. Con lo probado, la tasa por
   paso es `σR − 8·ln(1+a)`, no `σR`. El resultado correcto es
   `λⱼ / μ₀ ≤ (t/t′)^R · (1+a)^8` y `ln(μ₀/λⱼ) ≥ σR − 8·ln(1+a)`, positivo solo si
   `R > 8·ln(1+a) / σ`.
3. **Símbolos sin declarar:** `wilsonExpect`, `C_seed`, `coeff`, `n`, y `t`, `t′` aparecen dentro de la
   estructura pero son parámetros del teorema.
4. **Ambos teoremas están con `sorry`.** "Demostración inmediata" y "lo deriva" describen un plan, no
   un resultado. Este documento es una especificación.
5. **Alcance.** Lo que se obtendría es la brecha del sector con traslape con `ψ_R`, no spec(H) completo.
   La hipótesis `wilson_rep` (el lazo como `⟨ψ_R, Tᵏψ_R⟩ / (μ₀ᵏ‖ψ_R‖²)`) y `hpsi_ortho` son lo que
   falta probar para el modelo de Wilson; hoy son supuestos de la estructura.
