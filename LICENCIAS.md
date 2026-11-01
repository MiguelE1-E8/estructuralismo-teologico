# Licencias por archivo
Regla general: el `LICENSE` y el `LICENSE-docs` de la raíz se aplican **solo** a los archivos de la versión v0.1.0 (etiqueta `v0.1.0`, commit 54e6474, DOI 10.5281/zenodo.23697821) tal como estaban en ese commit. Todo archivo añadido o modificado después tiene todos los derechos reservados, con permiso académico (`LICENCIA-POSTERIOR-A-v0.1.0.md`), salvo que esta tabla o el propio archivo digan otra cosa.

| Ruta | Régimen |
|---|---|
| `lean/*.lean`, `tools/Axioms.lean`, `lakefile.toml`, `lean-toolchain` (como en v0.1.0) | Apache-2.0 |
| Textos y documentación de v0.1.0, `resultados/*` | CC BY 4.0 |
| `README.md`, `NOTICE`, `CITATION.cff` | Avisos del titular; describen ambos regímenes |
| `ficha/`, `sitio/`, `docs/`, `prototipo/`, `tools/` (salvo `Axioms.lean`), `MANTENIMIENTO.md`, `TERMINOS_DE_USO.md` | Todos los derechos reservados, con permiso académico |
| `prototipo/chat/vendor/pdfjs-3.11.174/` | Apache-2.0, © 2023 Mozilla Foundation (sin cambios) |

Un archivo Lean que se modifique después de v0.1.0 pasa al régimen reservado desde esa modificación; la versión v0.1.0 sigue disponible en la etiqueta con su licencia.

Última actualización: 1-nov-2026. Este documento es un aviso del titular y no sustituye asesoría jurídica.
