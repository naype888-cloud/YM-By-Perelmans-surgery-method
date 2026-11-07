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

## 6. Estado después de `Z2Transfer.lean` y `Z2Gap.lean` (Claude, 2026-11-07)

- **Probado:** (i) `T = D^{1/2} K D^{1/2}` es semidefinida positiva para `β ≥ 0` y todo peso
  espacial `w` (`Z2Transfer.transfer_posSemidef`, vía `K = Σ_S c_S χ_S χ_S`, `c_S = sinh^{|S|}cosh^{|L|-|S|} ≥ 0`).
  `Z2Gap.z2_spectral_gap` cierra `hPSD` para el modelo.
- **Falta (ii):** `wilson_rep`. Hay que probar que la esperanza euclidiana del lazo `R×k` en la caja,
  `highTempSum inc t (∂S₀) / highTempSum inc t 0`, es `⟨x, T^k x⟩ / (μ₀^k ‖x‖²)` con este `T`.
  Plan: gauge axial (enlaces en la dirección del tiempo = +1) por una biyección de configuraciones
  que preserva el peso y el lazo; luego rebanar la caja por tiempo. Hoy no está escrito.


## 7. Plan de `wilson_rep` (Claude, 2026-11-07) — tamaño estimado

Se revisó la geometría de `AreaBound.lean` (`cinc`, enlaces `x`, `y`, `z`, caja con frontera libre).
Dos hechos cambian lo que hay que probar:

1. **En volumen finito la representación no es exacta.** La caja tiene frontera libre en el tiempo, así
   que `⟨W(R×k)⟩ = ⟨v, T^a X T^k X T^b v⟩ / ⟨v, T^{a+k+b} v⟩` con un vector de frontera `v`; la forma
   `⟨x, T^k x⟩ / (μ₀^k ‖x‖²)` (con `Ω` el vacío) es el límite `a, b → ∞`. La cota del área es uniforme
   en el volumen, así que el límite es legítimo, pero hay que probarlo.
2. **El gauge axial se puede tomar como modelo, sin biyección de gauge.** Quitar las columnas de los
   enlaces `y` de `cinc` da otra incidencia `ainc` (enlaces `x` y `z`); `area_law_uniform` es para
   incidencia general y el grado de adyacencia solo baja. Hace falta una cota de área nueva para `ainc`.

Piezas, de menor a mayor:

| Pieza | Contenido | Tamaño estimado |
|---|---|---|
| A. Cadena (`SlabChain.lean`) — **hecha** | `Σ_{s : Fin (m+1) → ι} ∏ u(s_j) ∏ M(s_j, s_{j+1}) = ⟨√u, T^m √u⟩` con `T = D^{1/2} M D^{1/2}` (ya es `Z2Transfer.transfer`) | ~100 líneas |
| B. Límite (`SlabLimit.lean`) y B2 solapamiento (`PerronOverlap.lean`) — **hechas** | Perron (vector positivo y `T` de entradas positivas ⇒ solapamiento con el máximo) y paso `a,b → ∞`: da `h_decay` con `x = Xw`, `μ₀ = μ_max` | ~200 líneas |
| C1. `ainc` (`AxialBox.lean`) — **hecha** | incidencia axial, grado de adyacencia ≤ 12 | ~80 líneas |
| C2. Área axial (`AxialArea.lean`) — **hecha** | `|S| ≥ R·k` para superficies con frontera `x`-líneas en `j = 0` y `j = k` (cada plaqueta `xy` mueve un enlace `x` un paso en `j`) | ~150 líneas |
| C3. Rebanado (`AxialSlab.lean`, más `AxialSeeds.lean`, `SlabInsert.lean`, `SlabFin.lean`) — **hecha** | `weight(ainc) = ∏_j u(σ_j) · ∏_j K(σ_j, σ_{j+1})` y reindexar `Σ_σ` por `Fin (B+1) → L_s` | ~150 líneas |
| D. Ensamblaje (`Z2Wilson`) — pendiente | `h_decay` ⇒ `Z2Gap.z2_spectral_gap` | ~50 líneas |

Total estimado: unas 700 líneas de Lean con varias iteraciones de compilación.

**Estado (2026-11-07):** A, B, B2, C1, C2 y C3 (con semillas, A2 y reindexado) están escritas y commiteadas (0 sorry según el reporte de la sesión que las escribió; no recompilé aquí); D (`Z2Wilson`) sigue pendiente y `AxialLoop.lean` está en curso.

**Nota sobre la tasa.** Cada x-enlace de `cinc` (`AreaBound.lean`) pertenece a ≤ 4 plaquetas (2 `xy`, con `j` o `j-1`, y 2 `xz`, con `k` o `k-1`; ninguna `yz`). En gauge axial el número de semillas es ≤ 8R independiente de k (`AxialSeeds.seeds_rectAx_card_le`, con `j₀ + k ≤ B`), así que la tasa sería σ·R = R·ln(t'/t) y no σ·R − 8·ln(1+a): el factor (1+a)^8 por paso de las secciones 5 y 6 correspondía al gauge no fijado. Falta el ensamblaje D para que esta tasa llegue a `z2_spectral_gap`.

## 8. Cierre del plan (Claude, 2026-11-07)

Todas las piezas están probadas (0 sorry, axiomas estándar): A `SlabChain`, A2 `SlabInsert`, B
`SlabLimit`, B2 `PerronOverlap`, C1 `AxialBox`, C2 `AxialArea`, C3 `AxialSlab`, semillas `AxialSeeds`,
borde = lazo `AxialLoop`, reindexado `SlabFin`, y el ensamblaje D en `Z2Wilson`, `Z2WilsonGap`,
`Z2Spectral` y `Z2Final`.

`Z2Final.z2_gap`: para el modelo `Z₂` de Wilson en la caja axial, si `x = F w` tiene componente en un
autovector de autovalor positivo `μ_j`, entonces `R · log (t'/tanh β) ≤ log (μ₀/μ_j)`. En gauge axial
el número de semillas es `≤ 8R` independiente de `k`, así que la tasa es `σR` con `σ = log(t'/tanh β)`
y no `σR − 8·ln(1+a)` como en las secciones 5 y 6.

Lo que NO se probó: la cota `Δ` del grado de adyacencia (hipótesis `hdeg`); que `x` tenga solapamiento
con algún `e_j` de autovalor positivo (hipótesis `hj`); y nada de esto es un gap de masa de Yang–Mills
(modelo abeliano `Z₂`).

