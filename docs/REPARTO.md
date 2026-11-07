# Reparto de trabajo en `lattice-gauge-gap` (2026-11-07)

Participan dos Claude ("Estado de Huanhai" y "Cambios de Antigravity y pipeline", más la sesión de docs) y dos Antigravity. Los hashes son commits locales; la columna de estado salió del reporte de Huanhai y yo comprobé que los archivos y los commits existen y que no contienen `sorry`.

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
| Frontera del rectángulo axial = lazo | `AxialLoop.lean` (`boundary ainc (rectAx …) = cLoop …`) | Cambios de Antigravity y pipeline | en curso, sin commit |
| D ensamblaje | `Z2Wilson.lean` | Estado de Huanhai | en curso, el archivo aún no existe |
| Docs | `docs/*.md` | sesión de docs | al día |

Notas:
- `TransferChain.lean` sigue sin seguimiento en el árbol (solo definiciones duplicadas de `SlabChain.lean`). Huanhai pidió su borrado a Antigravity; reapareció o no se borró.
- Quien no es responsable de un archivo no lo edita. Los commits son locales y el push lo decide el usuario.
