# Estructuralismo teológico

Modelación en Lean 4 (sin Mathlib) de las ocho especializaciones funcionales de Lonergan
(*Método en teología*, E1–E8) y de su fase previa E0, con un caso común sobre Nicea–Constantinopla III
y los módulos `Ciclo*` que enlazan las etapas.

## Contenido
- `lean/` — E0–E8, `E2Nicea`, `E3Nicea` y los módulos `Ciclo*`.
- `tools/Axioms.lean` — auditoría de axiomas de todos los teoremas.
- `mapas/` — mapa técnico y mapa para lectores del ciclo, con el grafo en CSV y GraphML.
- `resultados/` — salida guardada de `lake build` y de la auditoría (Lean 4.22.0).

## Cómo comprobarlo
Requiere [elan](https://github.com/leanprover/elan). La versión de Lean está fijada en `lean-toolchain`.

```
lake build
lake env lean tools/Axioms.lean
```

## Estado verificado
Lean 4.22.0: compila sin errores. 1843 teoremas revisados, 0 con `sorryAx`; únicos axiomas:
`propext`, `Classical.choice`, `Quot.sound`. Verificado no equivale a auditado: Lean comprueba la
consistencia de los modelos, no que los enunciados reproduzcan el texto de Lonergan.
No se ha probado con otras versiones de Lean.

## Versiones y licencias
| Material | Licencia |
|---|---|
| Versión **v0.1.0** (etiqueta `v0.1.0`; DOI 10.5281/zenodo.23697821) — código | Apache-2.0 (`LICENSE`) |
| Versión **v0.1.0** — textos y documentación | CC BY 4.0 (`LICENSE-docs`) |
| **Todo lo añadido después de v0.1.0** | Todos los derechos reservados, con permiso académico (`LICENCIA-POSTERIOR-A-v0.1.0.md`) |

Cada carpeta posterior a v0.1.0 lleva un `AVISO-DERECHOS.txt` (modelo en `plantillas/`). Los nombres no están licenciados.

## Cita
Ver `CITATION.cff`. DOI de la versión v0.1.0: 10.5281/zenodo.23697821. DOI de todas las versiones: 10.5281/zenodo.23697770.
