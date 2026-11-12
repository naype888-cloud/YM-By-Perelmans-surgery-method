# Enunciado Canónico del Teorema de Kotecký–Preiss (1986) y Conexión a la Red de Wilson

**Propósito:** Proporcionar la definición matemática rigurosa, las cotas verificables y la hoja de ruta exacta para conectar el modelo abstracto de polímeros al confinamiento y Mass Gap en la teoría gauge de retículo.

---

## 1. El Teorema Abstracto de Kotecký–Preiss

### Referencia Bibliográfica Verificable:
* **R. Kotecký, D. Preiss**, *Cluster expansion for abstract polymer models*, **Communications in Mathematical Physics**, Vol. 103, No. 3 (1986), págs. 491–498.  
  [DOI: 10.1007/BF01211762](https://doi.org/10.1007/BF01211762).
* *(Nota sobre citas accesorias: La referencia histórica "Dobrushin–Pechersky 1983" sobre espines continuos queda marcada como **NO VERIFICADA EN ESTE ARCHIVO**; la referencia estándar verificable para la técnica de Dobrushin–Shlosman en espines continuos es R. L. Dobrushin, S. B. Shlosman, Comm. Math. Phys. 98, 1985).*

---

### Definiciones Matemáticas Exactas

Sea $\Gamma$ un conjunto (finito o numerable) cuyos elementos $\gamma \in \Gamma$ se denominan **polímeros**.
1. **Relación de Incompatibilidad ($\sim$):**  
   Una relación simétrica y reflexiva en $\Gamma$:
   $$\gamma \sim \gamma' \iff \gamma \text{ y } \gamma' \text{ son incompatibles (interactúan).}$$
   Se define el vecindario de incompatibilidad de $\gamma$ como:
   $$[\gamma] := \{ \gamma' \in \Gamma : \gamma' \sim \gamma \}.$$
   Dos polímeros son compatibles si $\gamma \not\sim \gamma'$.
2. **Familias Compatibles y Función de Partición:**  
   Para cualquier subconjunto finito $\Lambda \subseteq \Gamma$, una familia $X \subseteq \Lambda$ es compatible si todos sus pares son distintos y compatibles ($\forall \gamma_1 \neq \gamma_2 \in X, \, \gamma_1 \not\sim \gamma_2$).  
   La función de partición del modelo de polímeros en $\Lambda$ con pesos $w : \Gamma \to \mathbb{C}$ es:
   $$\Xi(\Lambda) := 1 + \sum_{\substack{X \subseteq \Lambda, \, X \neq \emptyset \\ X \text{ compatible}}} \prod_{\gamma \in X} w(\gamma).$$
3. **Funcionales de Cota:**  
   Sean $a : \Gamma \to [0, \infty)$ y $d : \Gamma \to [0, \infty)$ dos funciones no negativas sobre el espacio de polímeros.

---

### Enunciado del Teorema (Kotecký–Preiss 1986, Teorema 1)

> **Condición de Kotecký–Preiss (KP):**  
> Supóngase que para todo polímero $\gamma \in \Gamma$ se satisface la desigualdad:
> $$\sum_{\gamma' \in [\gamma]} |w(\gamma')| e^{a(\gamma') + d(\gamma')} \le a(\gamma).$$
> 
> **Consecuencias:**
> 1. **No anulación de la Función de Partición:**  
>    Para todo $\Lambda \subseteq \Gamma$ finito, $\Xi(\Lambda) \neq 0$, y para pesos no negativos $w(\gamma) \ge 0$, $\Xi(\Lambda) \ge 1$.
> 2. **Cota de Cociente y Desacoplamiento (Uniforme en $\Lambda$):**  
>    Para cualquier polímero $\gamma_0 \in \Lambda$:
>    $$\left| \frac{\Xi(\Lambda \setminus [\gamma_0])}{\Xi(\Lambda)} \right| \le e^{-d(\gamma_0)}.$$
>    Esta cota es **estrictamente independiente del tamaño del volumen $\Lambda$**.
> 3. **Convergencia Absoluta de la Expansión de Cúmulos:**  
>    El logaritmo de la función de partición admite la representación en serie:
>    $$\ln \Xi(\Lambda) = \sum_{X \subseteq \Lambda \text{ conexo}} \phi(X) \prod_{\gamma \in X} w(\gamma),$$
>    donde los coeficientes combinatorios de Ursell $\phi(X)$ satisfacen:
>    $$\sum_{X : \gamma \in X} |\phi(X)| \prod_{\gamma' \in X} |w(\gamma')| e^{d(\gamma')} \le a(\gamma).$$

---

## 2. Hoja de Ruta: Conexión a la Red de Wilson 3D

Para aterrizar el teorema abstracto de Kotecký–Preiss a la red gauge de Wilson $A \times B \times C$:

1. **Identificación de Polímeros:**  
   Los polímeros $\gamma$ son las **superficies cerradas conexas de plaquetas** con borde nulo ($\partial \gamma = 0$, "burbujas de vacío").
2. **Tamaño Mínimo en 3D:**  
   En la red cúbica 3D, el polímero cerrado no trivial más pequeño es la frontera de un cubo elemental (3-celda), que contiene:
   $$|\gamma| \ge 6 \quad \text{plaquetas.}$$
3. **Incompatibilidad Geométrica:**  
   Dos superficies $\gamma_1 \sim \gamma_2$ si comparten al menos un enlace ($l \in \gamma_1 \cap \gamma_2$).
4. **Pesos en Acoplamiento Fuerte:**  
   $$w(\gamma) = (\tanh \beta)^{|\gamma|} \quad (\text{para } \mathbb{Z}_2).$$
5. **Cotas de Adyacencia y Semillas (Revisadas y Aprobadas en Doc):**  
   * **Grado de adyacencia:** Cada plaqueta comparte enlaces con a lo más $\Delta = 12$ vecinas (4 enlaces $\times$ 3 plaquetas ajenas).
   * **Semillas del lazo $R \times T$:** El lazo plano tiene perímetro $2(R + T)$; cada enlace toca a lo más 4 plaquetas en la red:
     $$|\text{Seeds}| \le 8(R + T).$$
6. **Verificación de la Condición KP en la Red:**  
   Eligiendo $a(\gamma) = c_1 |\gamma|$ y $d(\gamma) = c_2 |\gamma|$, la suma $\sum_{\gamma' \sim \gamma} t^{|\gamma'|} e^{(c_1 + c_2)|\gamma'|}$ converge y satisface la condición KP para todo $\tanh \beta \le t_c$ suficientemente pequeño (acoplamiento fuerte), lo que garantiza el desacoplamiento de las burbujas de vacío con factor $\le e^{-c_2 |\text{Seeds}|}$.

---

## 3. Matemática (Lean 4 - Verificado con 0 sorry)

Todos los teoremas constructivos del andamiaje se encuentran formalizados y verificados con **0 sorry** bajo los axiomas canónicos del kernel (`propext`, `Classical.choice`, `Quot.sound`):
* [`AreaBound.lean`](../src/AreaBound.lean): `area_bound_rect` ($|S| \ge R \times T$ para toda superficie que tape el lazo plano en la caja cúbica).
* [`SpectralGap.lean`](../src/SpectralGap.lean): `connected_le_exp` (un gap espectral $\mu_0 > \lambda_1$ implica decaimiento exponencial conexo con tasa $\Delta = \ln(\mu_0/\lambda_1)$).
* [`AreaLawBound.lean`](../src/AreaLawBound.lean): `area_law_uniform` (cota uniforme en volumen para la red abeliana bajo hipótesis abstractas de grado y área mínima).
* [`FibreSurgery.lean`](../src/FibreSurgery.lean): Monotonía de $C_N(d)^2 - 1$ y sutura de la masa con piso $\min(1/4, \text{massSq}(4)/L^2) > 0$.
* [`DiracFloor.lean`](https://github.com/naype888-cloud/nrs3-hopf/blob/main/NRS3Hopf/DiracFloor.lean): Teorema `no_zero_spacing` (imposibilidad matemática de $a \to 0$ con energías acotadas por Planck).
