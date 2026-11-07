# Delimitación Formal de las Brechas de Yang–Mills: Teoremas Lean 4 e Hipótesis Abiertas

**Propósito:** Delimitar con rigor y honestidad epistemológica la frontera exacta entre lo demostrado en Lean 4 (0 sorry, axiomas estándar del kernel) y las hipótesis que permanecen como programas matemáticos y físicos abiertos.

---

## 1. Hipótesis Abierta: Extensión de la Expansión de Racimo a $SU(N)$ y Grupos No Abelianos

**Estado:** Hipótesis / programa abierto (la formalización de la ley del área en Lean 4 está cerrada en $\mathbb{Z}_2$; la extensión analítica rigurosa a $SU(N)$ permanece abierta).

1. **Lo probado formalmente en el corpus:**
   En [`HopfYangMills.lean`](file:///home/nava/lean-math/nrs3-hopf/NRS3Hopf/HopfYangMills.lean#L70-L87):
   * `ham_gauge`: La conmutación de la ley de Gauss en los 4 ejes con transformaciones de norma locales está formalizada para **cualquier grupo compacto $G$** (incluyendo $SU(2)$ y $SU(3)$):
     ```lean
     theorem ham_gauge {n : ℕ} (ρ : G →* Matrix.unitaryGroup (Fin n) ℂ) (lE lB : ℝ)
         (g : Site Z → G) (ψ : State (Site Z) (Fin 4) G) :
         ham ρ (step Z) (planes Z) lE lB (gaugeState (step Z) g ψ)
           = gaugeState (step Z) g (ham ρ (step Z) (planes Z) lE lB ψ)
     ```
   * `gap_ham`: Cota espectral a volumen finito bajo el hamiltoniano formal para cualquier grupo compacto $G$:
     ```lean
     theorem gap_ham {n : ℕ} (ρ : G →* Matrix.unitaryGroup (Fin n) ℂ) {lE lB : ℝ}
         (hE : 0 ≤ lE) (hB : 0 ≤ lB) (ψ : State (Site Z) (Fin 4) G) (h0 : ∑ U, ψ U = 0) :
         lE * nsq ψ ≤ (ip ψ (ham ρ (step Z) (planes Z) lE lB ψ)).re
     ```

2. **La brecha que constituye la hipótesis abierta (no cerrada en Lean 4):**
   * La descomposición de racimo $S \mapsto (\gamma, R)$ formalizada en [`PolymerBound.lean`](file:///home/nava/lean-math/lattice-gauge-gap/PolymerBound.lean) opera a nivel topológico combinatorio en la red.
   * La integración de Haar sobre grupos de Lie continuos compactos $SU(N)$, el teorema de Peter–Weyl y la ortogonalidad analítica de caracteres:
     $$\int_{SU(N)} dU_l \, \chi_j(U_l) \overline{\chi_k(U_l)} = \delta_{jk}$$
     no forman parte de la formalización actual en Mathlib ni de las pruebas compiladas en `lattice-gauge-gap`.
   * **Conclusión honesta:** Que la ley del área y el gap se extiendan de $\mathbb{Z}_2$ a $SU(N)$ mediante la medida de Haar completa en 4D es una **hipótesis física y matemática abierta**, respaldada conceptualmente por el andamiaje formal, pero no un teorema formalmente cerrado en el kernel.

---

## 2. Hipótesis Abierta: La Cota Transversal de Fibra (`FibreBound`)

**Estado:** Hipótesis abierta de acoplamiento fibra-operador (asumida explícitamente como hipótesis en `FibreSurgery.lean`).

1. **El análogo rigurosamente demostrado en el modelo Dirac / U(1):**
   En [`DiracGapGaugeInvariant.lean`](file:///home/nava/lean-math/nrs3-hopf/NRS3Hopf/DiracGapGaugeInvariant.lean#L368), el teorema `norm_sq_rest_ge_pure_u1` demuestra formalmente (**0 sorry, axiomas estándar**):
   ```lean
   theorem norm_sq_rest_ge_pure_u1 (Uy : PureU1GaugeLink τy) (Uz : PureU1GaugeLink τz) (χ : H) :
       (1 / 2 : ℝ) ^ 2 * ‖χ‖ ^ 2 ≤ ‖(A_u1 Uy.toU1GaugeLink Uz.toU1GaugeLink + Mw) χ‖ ^ 2
   ```
   Y en [`DiracSpeed.lean`](file:///home/nava/lean-math/nrs3-hopf/NRS3Hopf/DiracSpeed.lean#L160), `abs_energy_ge` demuestra la transferencia de cota por anticonmutación: $|E| \ge |m| = 1/2$.

2. **La brecha que constituye la hipótesis abierta:**
   * La cota de Dirac en $U(1)$ establece la existencia de una brecha espectral no nula debida a la compacidad transversal de la fibra $S^1$.
   * Sin embargo, el operador de transferencia / hamiltoniano de la teoría gauge no abeliana de Yang–Mills en la red sobre el colector $\mathbb{R}^3 \times S^1$ no ha sido identificado ni embebido formalmente en el operador de Dirac $U(1)$ dentro de Lean 4.
   * Por ello, `FibreBound` en [`FibreSurgery.lean`](file:///home/nava/lean-math/lattice-gauge-gap/FibreSurgery.lean) se mantiene explícitamente como un **supuesto estructural / hipótesis abierta**. La derivación formal de esta cota a partir de primeros principios en el operador de red no abeliano es un **programa abierto**.

---

## 3. Sobre $L \to \infty$, la Cirugía de Perelman y el Límite Continuo

El planteamiento de que *"al mandar $L \to \infty$ para recuperar $\mathbb{R}^4$ infinito, la cota $\text{massSq}(4)/L^2 \to 0$ colapsa"* comete un error topológico de base:

1. **Una Cirugía Topológica no deshace la Fibra:**
   En una cirugía estilo Perelman / Kaluza–Klein / Hopf sobre $\mathbb{R}^3 \times S^1$:
   * Los tres ejes espaciales $x, y, z \in \mathbb{R}^3$ son **abiertos, continuos e infinitos** ($L_x, L_y, L_z \to \infty$).
   * El cuarto eje $w \in S^1$ es **compacto por topología intrínseca** (radio de fibra $R = a$). No se toma $L_w \to \infty$.
2. **Protección Cuántica contra el Colapso Gaussiano:**
   * En $\mathbb{R}^4$ plano infinito, el vacío saturaría la cota mínima gaussiana de Robertson–Schrödinger ($\det \Sigma / |\det \Omega| = 1$), permitiendo el colapso del gap a cero.
   * La compacidad de la fibra $S^1$ impone un transporte cerrado no contráctil (holonomía), generando el defecto topológico cuántico:
     $$\frac{\det \Sigma}{|\det \Omega|} = \frac{5}{4} = 1 + \frac{1}{4} > 1$$
     Este defecto impide que el vacío colapse a un paquete gaussiano de energía cero.
3. **Piso Ultravioleta y Divergencia sin Fibra:**
   En [`DiracFloor.lean`](file:///home/nava/lean-math/nrs3-hopf/NRS3Hopf/DiracFloor.lean#L59), el teorema `no_zero_spacing` demuestra formalmente que mandar $a \to 0$ en un espacio plano no acotado sin escala de fibra dispara las energías físicas a infinito:
   ```lean
   theorem no_zero_spacing {hc Emax : ℝ} (hhc : 0 < hc) (hEmax : 0 < Emax) (a : ℕ → ℝ) ...
   ```

---

## 4. Síntesis Canónica y Delimitación Honesta

1. **Lo Demostrado en Lean 4 (0 sorry, axiomas estándar):**
   * **Modelo de Wilson $\mathbb{Z}_2$:** Ley del área uniforme en el volumen probada en [`CubeAreaLaw.lean`](file:///home/nava/lean-math/lattice-gauge-gap/CubeAreaLaw.lean).
   * **Modelo de Polímeros:** Descomposición $Z = \text{polymerZ}$ en [`PolymerDecomposition.lean`](file:///home/nava/lean-math/lattice-gauge-gap/PolymerDecomposition.lean) y cotas de cociente de Kotecký–Preiss en [`KoteckyPreiss.lean`](file:///home/nava/lean-math/lattice-gauge-gap/KoteckyPreiss.lean).
   * **Defecto de la Fibra:** Cota transversal $1/4$ en $U(1)$ (`DiracGapGaugeInvariant.lean`) y no-saturación en $d \ge 4$ (`FibreSurgery.lean` y `FibreBand.lean`).
   * **Teorema Inverso Espectral:** Demostrado en [`SurgeryGapClosure.lean`](file:///home/nava/lean-math/lattice-gauge-gap/SurgeryGapClosure.lean) (`eigenvalue_le_of_pow_bound`).

2. **Lo que Permanece como Programa Abierto (No Afirmado como Teorema Cerrado):**
   * La reconstrucción completa de los axiomas de Wightman en espacio de Minkowski a partir de Osterwalder–Schrader en $\mathbb{R}^4$ continuo sin andamio de red.
   * La extensión estricta de la medida de Haar y caracteres para $SU(N)$ no abeliano (requiere formalización de Peter–Weyl en Mathlib).
   * El límite continuo estricto $a \to 0$ sin la hipótesis de escala de fibra.

El andamiaje formal está honestamente delimitado.
