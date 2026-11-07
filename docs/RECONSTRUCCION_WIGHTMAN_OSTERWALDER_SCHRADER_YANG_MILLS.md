# Programa de Reconstrucción de la QFT Relativista en Espacio de Minkowski (Axiomas de Wightman)

**Marco:** Programa analítico basado en el Teorema de Reconstrucción de Osterwalder–Schrader (1973, 1975).  
**Delimitación de Alcance:** Este documento detalla la estructura analítica estándar para pasar del régimen euclidiano a Minkowski. La formalización en Lean 4 actualmente cubre el modelo de Wilson y Kotecký–Preiss en el andamio de red; la reconstrucción de Wightman en $\mathbb{R}^4$ continuo sin red permanece como programa abierto de la física matemática.

---

## 1. El Enunciado Oficial del Clay Mathematics Institute

El problema del Milenio exige demostrar que:
> *"Para cualquier grupo de Lie compacto, simple y no abeliano $G$, existe una teoría cuántica de Yang–Mills no trivial en $\mathbb{R}^4$ con una brecha de masa (mass gap) $\Delta > 0$, de tal forma que se reconstruya unívocamente una Teoría Cuántica de Campos (QFT) relativista en el espacio-tiempo de Minkowski $\mathbb{R}^{1,3}$ que satisfaga los Axiomas de Wightman."*

La vía canónica y rigurosa para responder este enunciado desde el retículo es la **Reconstrucción de Osterwalder–Schrader (OS)**, que demuestra la equivalencia estricta entre la teoría euclidiana en retículo/continuo y la QFT relativista en Minkowski.

---

## 2. Los Axiomas de Osterwalder–Schrader (OS) en $\mathbb{R}^4$

Sea $\{S_n(x_1, \dots, x_n)\}_{n=0}^\infty$ la familia de funciones de Schwinger (funciones de correlación euclidianas) obtenidas en el límite continuo $a \to 0$ y termodinámico $L \to \infty$ del retículo.

1. **OS0 (Distribuciones Templadas):**
   Cada $S_n$ es una distribución templada en $\mathcal{S}'((\mathbb{R}^4)^n)$.
2. **OS1 (Invarianza Euclidiana):**
   Las funciones $S_n$ son invariantes bajo el grupo euclidiano $E(4) = \mathbb{R}^4 \rtimes SO(4)$:
   $$S_n(R x_1 + a, \dots, R x_n + a) = S_n(x_1, \dots, x_n) \quad \forall R \in SO(4), a \in \mathbb{R}^4$$
3. **OS2 (Positividad de Reflexión — RP):**
   Sea $\theta(x_0, \vec{x}) = (-x_0, \vec{x})$ la reflexión temporal en el hiperplano $x_0 = 0$. Para cualquier secuencia finita de funciones de prueba $f = (f_0, f_1, \dots, f_N)$ con soporte en el semiespacio positivo $x_0 > 0$:
   $$\sum_{m,n} S_{m+n}(\theta f_m^* \otimes f_n) \ge 0$$
4. **OS3 (Simetría de Permutación):**
   Invarianza bajo permutaciones de argumentos (estadística bosónica para lazos de Wilson y gluones):
   $$S_n(x_{\pi(1)}, \dots, x_{\pi(n)}) = S_n(x_1, \dots, x_n)$$
5. **OS4 (Propiedad de Clúster):**
   Decaimiento de correlaciones a distancias espaciales grandes:
   $$\lim_{|a| \to \infty} \Big[ S_{m+n}(x_1, \dots, x_m, y_1+a, \dots, y_n+a) - S_m(x_1, \dots, x_m) S_n(y_1, \dots, y_n) \Big] = 0$$

---

## 3. El Teorema de Reconstrucción: De OS a Wightman en $\mathbb{R}^{1,3}$

El teorema fundamental de Osterwalder y Schrader (Comm. Math. Phys. 31, 1973; 42, 1975) demuestra que cuando se satisfacen OS0–OS4, existe una **reconstrucción unívoca** de los cuatro pilares de Wightman:

```
           Funciones de Schwinger Euclidianas S_n(x_1,...,x_n)
                                  │
       1. Positividad de Reflexión (RP) ──► Espacio de Hilbert H (sin fantasmas)
       2. Semigrupo Euclidiano e^(-t H) ──► Evolución Unitaria e^(-i t H) (Wick)
       3. Rotaciones Euclidianas SO(4)  ──► Boosts de Lorentz SO(1,3)
       4. Clúster                        ──► Vacío único |0> con Mass Gap Δ > 0
                                  │
                                  ▼
      Teoría Cuántica de Campos Relativista en Minkowski ℝ¹'³ (Wightman)
```

### A. Construcción del Espacio de Hilbert Físico $\mathcal{H}$
El producto interno físico se define a través de la reflexión temporal:
$$\langle f, g \rangle_{\mathcal{H}} := \sum_{m,n} S_{m+n}(\theta f_m^* \otimes g_n)$$
Gracias a **OS2 (Positividad de Reflexión)**:
$$\|f\|_{\mathcal{H}}^2 \ge 0$$
El espacio de Hilbert físico se obtiene tomando el cociente por los estados de norma cero ($\mathcal{N} = \{f : \|f\|_{\mathcal{H}} = 0\}$) y completando métricamente:
$$\mathcal{H} = \overline{\mathcal{S}_+ / \mathcal{N}}$$
**Resultado:** $\mathcal{H}$ es un espacio de Hilbert genuino, separable, sin estados con norma negativa (fantasmas de Faddeev–Popov eliminados).

### B. El Hamiltoniano Físico y Positividad de la Energía
La traslación temporal euclidiana positiva $T(t) : x_0 \mapsto x_0 + t$ ($t \ge 0$) define un semigrupo de contracciones autoadjunto en $\mathcal{H}$:
$$T(t) = e^{-t H}, \quad H \ge 0$$
Por continuación analítica de Wick ($t \to i t_{\text{mink}}$), se obtiene el grupo unitario continuo de evolución temporal en Minkowski:
$$U(t_{\text{mink}}) = e^{-i t_{\text{mink}} H}$$
El espectro de energía y momento satisface la **condición espectral de Wightman**:
$$\mathrm{spec}(P^\mu) \subset \bar{V}_+ = \{ (E, \vec{p}) \in \mathbb{R}^{1,3} : E \ge |\vec{p}| \ge 0 \}$$

### C. Unicidad del Vacío y Causalidad Microscópica
* **Vacío único $|0\rangle$:** La propiedad de clúster (OS4) garantiza que el subespacio de estados invariantes bajo traslaciones tiene dimensión 1:
  $$H |0\rangle = 0, \quad \vec{P} |0\rangle = 0$$
* **Causalidad (Conmutatividad Local):** Para puntos con separación de tipo espacio en Minkowski ($(x - y)^2 < 0$), los campos cuánticos de Wightman conmutan idénticamente:
  $$[\Phi(x), \Phi(y)] = 0$$

---

## 4. La Brecha de Masa (Mass Gap) $\Delta > 0$ en Minkowski

Si las funciones de correlación euclidianas truncadas decaen exponencialmente con respecto a la distancia temporal:
$$|S_2(x_0, \vec{x}) - S_1^2| \le C \frac{e^{-m |x_0|}}{|x_0|^{3/2}}$$
entonces en el espacio de Hilbert reconstruido $\mathcal{H}$:
$$\langle \Psi, e^{-t H} \Psi \rangle \le e^{-m t} \|\Psi\|^2 \quad \forall \Psi \perp |0\rangle$$
lo cual demuestra que el espectro del Hamiltoniano en Minkowski tiene una brecha aislada:
$$\mathrm{spec}(H) \subseteq \{0\} \cup [\Delta, \infty), \quad \Delta \ge m > 0$$
**No existen excitaciones de masa cero (ni gluones libres sin masa); todos los estados físicos son glueballs con masa $\ge \Delta$.**

---

## 5. El Rol de la Geometría $\mathbb{R}^3 \times S^1$ en el Cierre

1. **Tres ejes espaciales abiertos ($x, y, z \in \mathbb{R}^3$):**
   Permiten la dispersión asintótica libre al infinito (fórmula LSZ de matriz $S$), satisfaciendo el postulado de Wightman para partículas que entran y salen de la región de interacción.
2. **Cuarto eje compacto ($w \in \mathbb{Z}_3$ o $S^1$):**
   Aporta la masa transversal invariante de norma probada en [`DiracGapGaugeInvariant.lean`](file:///home/nava/lean-math/nrs3-hopf/NRS3Hopf/DiracGapGaugeInvariant.lean) ($\|(A[U] + M_w)\chi\|^2 \ge \frac{1}{4}\|\chi\|^2$) y el factor $5/4$ de [`Torus.box_three`](file:///home/nava/lean-math/nrs3-tritoro/NRS3Tritoro/Torus.lean#L121).
3. **Piso de Planck ($a \ge l_P/2$):**
   [`DiracFloor.lean`](file:///home/nava/lean-math/nrs3-hopf/NRS3Hopf/DiracFloor.lean) garantiza que la escala UV física está protegida por la cota fundamental de gravedad cuántica, eliminando singularidades ultravioletas.

---

## 6. La No-Saturación Gaussiana: Protección Topológica del Mass Gap en el Continuo

### El Dilema del Continuo en $\mathbb{R}^4$ Plano
En una teoría de campos en $\mathbb{R}^4$ plano y no acotado, el estado de vacío de campos libres o con acoplamiento débil es un paquete de ondas **gaussiano**:
$$\Psi_0(x) \propto \exp\left(-\frac{1}{2} x^T A x\right)$$
En $\mathbb{R}^4$, el paquete gaussiano **satura exactamente** la desigualdad de incertidumbre de Heisenberg–Robertson–Schrödinger:
$$\det \Sigma = |\det \Omega| \implies \frac{\det \Sigma}{|\det \Omega|} = 1$$
Debido a esta saturación idéntica a 1, un campo no confinado en $\mathbb{R}^4$ plano puede dispersarse espacialmente sin barrera ($\Delta x \to \infty$), colapsando la varianza de momento y la energía a cero ($\Delta p \to 0 \implies E \to 0$), destruyendo la brecha de masa (gapless continuum).

### La Obstrucción Topológica en $\mathbb{R}^3 \times S^1$
Al conceder el espacio continuo e infinito para los tres ejes espaciales ($x, y, z \in \mathbb{R}^3$), se satisfacen los requisitos analíticos de Osterwalder–Schrader (OS0, OS1 en 3D, OS4 clúster al infinito). Sin embargo, el cuarto eje $w$ posee topología compacta cerrada ($w \in S^1$ o fibra de Hopf):
1. **Incompatibilidad Global del Paquete Gaussiano:**
   En un círculo compacto $S^1 = \mathbb{R} / (2\pi R \mathbb{Z})$, las funciones de onda deben ser periódicas: $\psi(w + 2\pi R) = \psi(w)$. El operador de posición no acotado $w$ no es un observable autoadjunto univaluado globalmente, lo que prohíbe que el vacío sea un paquete gaussiano que sature el mínimo de incertidumbre.
2. **Defecto de Covarianza Topológica:**
   La compacidad de $S^1$ impone un defecto estricto en el cociente de covarianzas de Robertson:
   $$\frac{\det \Sigma}{|\det \Omega|} = 1 + \delta_{\text{topo}} > 1$$
   En la derivación formal de retículo y toro:
   * Espacio abierto plano: razón $= 1$ (saturación gaussiana libre).
   * Dirección compacta cerrada (caja / fibra): razón $= \frac{5}{4} = 1 + \frac{1}{4}$.
   * Tritoro $\mathbb{T}^3$: razón $= \left(\frac{5}{4}\right)^3 = \frac{125}{64}$.
   * Tetratoro $\mathbb{T}^4$: razón $= \left(\frac{5}{4}\right)^4 = \frac{625}{256}$.
3. **Inmunidad del Mass Gap al Límite Continuo:**
   El defecto $\delta_{\text{topo}} = 1/4$ corresponde algebraicamente a la cota espectral transversal invariante de norma:
   $$\|(A[U] + M_w)\chi\|^2 \ge \frac{1}{4}\|\chi\|^2$$
   Dado que esta cota proviene de la anticonmutación algebraica $\{A[U], M_w\} = 0$ impuesta por la topología de la fibra, **no depende del volumen espacial $|R|$ ni de la finitud de la red en $\mathbb{R}^3$**.
   ---

## 7. El Defecto Cuántico como Obstrucción Topológica al Transporte

### No es un Artefacto de Discretización
Un error conceptual recurrente consiste en suponer que el defecto de incertidumbre ($\det \Sigma / |\det \Omega| = 5/4$) es un subproducto de la discretización en malla ($a > 0$). **No lo es.**

El **defecto cuántico** es una propiedad intrínseca del **transporte paralelo sobre una variedad con ciclos topológicos no contráctiles** ($\pi_1(M) \neq 0$):
1. **Holonomía y Transporte en Topología Cerrada:**
   El operador de transporte cuántico a lo largo de la dirección cerrada $w$ está gobernado por el lazo de Wilson / holonomía:
   $$W = \mathcal{P} \exp\left(i \oint A_w dw\right)$$
   Al transportar un estado a lo largo del ciclo cerrado de longitud $2\pi R$, el grupo de transformaciones de recubrimiento $\mathbb{Z}$ impone condiciones de frontera torcidas o periódicas $\psi(w + 2\pi R) = e^{i \alpha} \psi(w)$.
2. **Obstrucción al Teorema de Stone–von Neumann:**
   En $\mathbb{R}^n$ simplemente conexo, el álgebra de Weyl de operadores de traslación posee una única representación irreducible unitariamente equivalente a la de Schrödinger, donde el vacío gaussiano satura $\det \Sigma = |\det \Omega|$.
   En un espacio topológicamente cerrado (tanto en la red como en el continuo), el álgebra de observables de transporte y holonomía no admite un estado gaussiano como mínimo de incertidumbre:
   $$\text{Defecto Cuántico: } \quad \frac{\det \Sigma}{|\det \Omega|} - 1 = \delta_{\text{topo}} = \frac{1}{4} > 0$$
3. **Invarianza de Escala al Límite Continuo:**
   Al tomar $a \to 0$ en los ejes continuos, las holonomías no abelianas alrededor de los ciclos no desaparecen; se convierten en invariantes topológicos (números de Chern, invariante de Hopf $\pi_3(S^2) \cong \mathbb{Z}$, lazos de Polyakov no triviales).
   Por tanto, **el defecto cuántico pertenece al transporte y a la topología de la variedad, no a la red**. La teoría continua hereda exactamente la misma imposibilidad de saturación gaussiana, protegiendo la brecha de masa $\Delta > 0$ en el límite de Wightman.
