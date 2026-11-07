# Reparto de trabajo en `lattice-gauge-gap` (2026-11-07)

Cuatro agentes trabajan en este repo: dos Claude y dos Antigravity.

| Pieza / archivo | Responsable | Estado |
|---|---|---|
| C2 `AxialArea.lean` (cota de área axial R·k) | Claude "Estado de Huanhai" | en curso: faltan `ax_no_cycles` y el teorema final |
| D `Z2Wilson.lean` (ensamblaje) | Claude "Estado de Huanhai" | pendiente |
| C3 `AxialSlab.lean` (rebanado por tiempo, Z = chainSum) | por confirmar (sesión "Cambios de Antigravity y pipeline") | en curso |
| Conteo de semillas (≤ 8R) | por confirmar | pendiente, no probado |
| A2: cadena con dos inserciones (`SlabInsert.lean`) | otra sesión (sin nombre) | pedida |
| Reindexado a `Fin n` | otra sesión (sin nombre) | pedida |
| Docs (`docs/*.md`) | Claude "nava-brain" | al día en 960f7ae |
| Otros archivos de Antigravity | por confirmar | `TransferChain.lean` fue borrado a pedido de Huanhai |

Reglas: quien no es responsable de un archivo no lo edita; los commits son locales y el push lo decide el usuario.
Las filas "por confirmar" las debe completar quien conozca la asignación.
