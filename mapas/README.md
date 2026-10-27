# Mapas del ciclo E0–E8

Estado del 27-oct-2026, reconstruido desde los documentos `ciclo/*.md` y los módulos `lean/Ciclo*.lean`.

- `mapa_tecnico.html` — grafo dirigido con 36 vínculos (cadena formal, retornos formalizados, entradas directas, hipotéticos), con nombre en Lean y origen [T]/[L]/[E].
- `mapa_lectores.html` — versión en lenguaje llano.
- `aristas_E0_E8.csv`, `grafo_E0_E8.graphml` — los mismos vínculos para otras herramientas.
- `fuente/` — `edges_v3.py` (fuente única de las aristas) y `grafo_v3.py` (métricas y exportación; requiere `networkx`).

Las 17 aristas autorizadas entre E1 y E8 forman un grafo fuertemente conexo (9 críticas, 8 redundantes). Los retornos son relaciones permitidas, no flujos obligatorios. Los HTML usan una base de datos de votos que solo funciona dentro de Claude; fuera de allí se ven sin votación.
