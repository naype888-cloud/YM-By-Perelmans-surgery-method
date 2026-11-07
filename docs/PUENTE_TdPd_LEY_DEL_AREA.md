# Puente: ley del área de Wilson ↔ movimiento elemental T_d : P_d

Estado: **enunciado del hueco, nada de esto está en Lean todavía.** Cada nombre citado se verificó
con grep en el archivo indicado.

## 1. Qué hay probado (y es válido como teorema del modelo)

El modelo de Wilson `Z₂` usa plaquetas, enlaces y cajas como andamio de cálculo, como una elección
de coordenadas. Los teoremas son verdaderos para ese modelo y no dicen qué es el espacio.

| Resultado | Archivo | Nombre Lean |
|---|---|---|
| Superficie mínima: `R·T ≤ |S|` | `AreaBound.lean:312` | `area_bound_rect` |
| Ley del área uniforme en el volumen | `AreaLawBound.lean` | `area_law_uniform` |
| Caso concreto (`Z2Gauge`) | `CubeAreaLaw.lean` | `Z2Gauge.cube_wilson_area_law` |
| `Z = polymerZ` | `PolymerDecomposition.lean` | `highTempSum_zero_eq_polymerZ` |
| Kotecký–Preiss, pesos ≥ 0 | `KoteckyPreiss.lean` | `ratio_le_exp_of_kp`, `exp_neg_le_ratio` |

## 2. Qué es el movimiento elemental (corpus independiente, `icarm_lean_independent`)

| Hecho | Archivo | Nombre Lean |
|---|---|---|
| Paso mínimo entre posiciones adyacentes | `D3_GrafoCamino.lean` | `pasoMinimo_iff_adj`, `grafoTP_es_pathGraph` |
| `C = 1 + δ` | `D21_DesigualdadElementalNRS.lean` | `CNava_eq_one_add_deltaGeom` |
| Defecto intrínseco de T_d:P_d = defecto de Gram | `D22_InstanciaPosicionTransporteTdPd.lean` | `defectoIntrinseco_TdPd_eq_defectoGram` |
| Saturación de T_d:P_d | idem | `saturada_TdPd_iff` |
| `δ > 0` para `d ≥ 4` | idem | `defecto_pos_TdPd` |
| Palabras: defecto = suma por letra | `NavaRobertsonCertificados/D50g_WordDefect.lean` | `wordDefect_eq_sum_count` |

(`pathGraph` en D3 es un artefacto que une Fiedler con Niven; no describe el espacio.)

## 3. El hueco, dicho sin red ni caja

La ley del área acota el costo de un lazo por el número de plaquetas de la superficie que lo llena.
En el lenguaje de T_d : P_d, ese costo debería leerse como **defecto acumulado de una palabra de
pasos elementales** (D50g: `Σ_k (letras de tipo k) · δ_k`). Para cerrar el puente hay que escribir
en Lean tres cosas que hoy no existen:

1. **El observable.** Definir el lazo de Wilson como una palabra de pasos T_d:P_d (sin plaquetas
   como ontología), y su valor esperado `⟨W⟩` en esa palabra.
2. **El costo.** Un teorema que compare el número mínimo de plaquetas (`area_bound_rect`) con el
   defecto de la palabra, **candidato (no probado)**: defecto(palabra de la superficie) ≥ `R·T · δ_min`.
3. **La tensión.** Relacionar `σ(β) ≥ ln(t′/tanh β)` con `δ` (`massSq`, `FibreSurgery.lean`) y no con
   un parámetro del modelo. Hoy `t′`, `a` y `Δ = 12` son datos del andamio, no de T_d:P_d.

## 4. Lo que sigue abierto aparte del puente

- Brecha de masa no abeliana, `SU(N)`: Mathlib no trae Peter–Weyl. La integral de Haar de un
  enlace compartido no es un producto de unos, así que la inyección de `PolymerBound` no pasa tal
  cual. Pista: para `SU(2)` los coeficientes de caracteres del peso de Wilson son positivos
  (por probar), lo que permitiría reusar `KoteckyPreiss.lean` sin pesos complejos.
- `FibreBound`: `norm_sq_rest_ge_pure_u1` (`DiracGapGaugeInvariant.lean:368`) es la brecha del
  operador de Dirac para enlaces U(1), con constante ½; el paso al defecto `massSq` no está escrito.
- Osterwalder–Schrader/Wightman: no se afirma. `connected_le_exp` supone la brecha, no la produce.
