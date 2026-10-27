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

## Licencias
Código: Apache-2.0 (`LICENSE`). Textos y documentación: CC BY 4.0 (`LICENSE-docs`).
Los nombres no están licenciados.

## Cita
Ver `CITATION.cff`. El DOI se añadirá al publicar el primer release.
