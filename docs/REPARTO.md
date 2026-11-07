# Reparto de trabajo en `lattice-gauge-gap` (2026-11-07)

Participan dos Claude ("Estado de Huanhai" y "Cambios de Antigravity y pipeline", más la sesión de docs) y dos Antigravity. Los hashes son commits (los de `df215fb`, `e763d22`, `c0c833d` y `beb69f2` ya están en `origin/main`); la columna de estado salió del reporte de Huanhai y yo comprobé que los archivos y los commits existen y que no contienen `sorry`.

| Pieza | Archivo | Responsable | Estado |
|---|---|---|---|
| A cadena | `SlabChain.lean` | Estado de Huanhai | hecha |
| B límite | `SlabLimit.lean` | Estado de Huanhai | hecha |
| B2 solapamiento | `PerronOverlap.lean` | Estado de Huanhai | hecha |
| C1 incidencia axial | `AxialBox.lean` | Estado de Huanhai | hecha (fb7701c) |
| C2 área axial R·k | `AxialArea.lean` | Estado de Huanhai | hecha (9b2121e) |
| C3 rebanado | `AxialSlab.lean` | Cambios de Antigravity y pipeline | hecha (641fc98) |
| Conteo de semillas ≤ 8R | `AxialSeeds.lean` (`seeds_rectAx_card_le`, con `hjk : j₀ + k ≤ B`) | Cambios de Antigravity y pipeline | hecha (56c6646) |
| A2 cadena con dos inserciones | `SlabInsert.lean` (`chain_two_insertions`) | Cambios de Antigravity y pipeline | hecha (6d06807) |
| Reindexado a `Fin n` | `SlabFin.lean` | Cambios de Antigravity y pipeline | hecha (0e75ac7) |
| Frontera del rectángulo axial = lazo | `AxialLoop.lean` (`boundary ainc (rectAx …) = cLoop …`) | Cambios de Antigravity y pipeline | hecha (fe3c0ae) |
| D ensamblaje | `Z2Wilson.lean` | Estado de Huanhai | hecha (df215fb): `Z2Final.z2_gap` |
| Descarga de `hdeg` (grado de adyacencia ≤ 12) | `AdjDegree.lean` (`adj_degree_le_twelve`) | Cambios de Antigravity y pipeline | hecha (c0c833d) |
| `z2_gap_twelve` (sin la hipótesis `hdeg`) | `Z2Final.lean` | Estado de Huanhai | hecha (beb69f2) |
| Docs | `docs/*.md` | sesión de docs | al día |

Notas:
- `TransferChain.lean` (sin seguimiento, no importado por nadie) probaba el mismo enunciado que `SlabChain.chainSum_eq_transfer` con otro nombre (`chainSum_eq_transfer_quad`). Ya no está en el árbol; lo borró otra sesión antes de que lo hiciera la de docs. No hay copia de respaldo.
- Quien no es responsable de un archivo no lo edita. Los commits son locales y el push lo decide el usuario.

## Alcance de `Z2Final.z2_gap`

Es un modelo **abeliano Z2** de Wilson en la caja axial. No es una brecha de masa de Yang–Mills: SU(N), `FibreBound` y 4D siguen abiertos.

Enunciado (según Huanhai, 0 sorry, axiomas `propext`, `Classical.choice`, `Quot.sound`): si `x = F·w` (carácter de fila del lazo aplicado a la proyección `w` del vector de frontera sobre el espacio del máximo de `T`) tiene componente en un autovector de autovalor positivo `μ_j`, entonces `R·log(t'/tanh β) ≤ log(μ₀/μ_j)`.

Hipótesis que el teorema no descarga:
1. `hdeg`: descargada en `z2_gap_twelve` (Δ = 12, `AdjDegree.lean`). `z2_gap` la conserva como hipótesis.
2. `hj`: que `x` tenga componente en algún autovector de autovalor positivo (no derivada).
3. `t'` y `a` con `t'(1+a)^Δ ≤ a` y `tanh β < t'` (solo acoplamiento fuerte); además `R ≤ A`.

No queda condición `j₀ + k ≤ B`: se descarga con `B = 2N + k` en `Z2WilsonGap.hlaw`.
