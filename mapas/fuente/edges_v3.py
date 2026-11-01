# Fuente única del grafo v3 (27-oct-2026). Estado del Project: archivos ciclo/*.md y lean/Ciclo*.lean.
# tipos: F cadena formal | R retorno formalizado (relación, "permiso") | D entrada directa | H hipotético
# (a, b, tipo, qué fluye, dónde está en Lean / estado, origen [T] texto [L] lectura [E] estipulación, trazo SVG)
EDGES = [
 ("E0","E1","F","V2′: cada área de E1 es unión de bloques de D/ de E0","`yNi_compatible`, `vincN` (campos de `CasoNicea`, no teorema general)","[E] E0 no es una de las ocho de Lonergan; la condición es de modelado","M118 50 L141 50"),
 ("E1","E2","F","Em/Ea/Er de E2 se definen desde la evidencia Ev de E1 (compatibilidad antítona)","`CompE`, `toMpD`, `casoNicea_E2`, `comp_creciente_excluida`","[T] orden de las ocho (pp. 138-139) · [E] condición","M253 50 L276 50"),
 ("E2","E3","F","E3 lleva por dentro su modelo de E2 (`M3.xM`); au/ub salen de las circunstancias a","`Cadena38`, `NiceaE3.xM = NiceaE2`, `contexto_de_L3`","[T] orden de las ocho · [E] condición","M388 50 L411 50"),
 ("E3","E4","F","Lo que E3 declara incompatible (Inc) es discrepancia (Dsc) para E4","`IncEnDsc`, `enlace34_consistente`, `enlace34_independiente`","[T] orden de las ocho · [E] condición","M523 50 L546 50"),
 ("E4","E5","F","Una conversión de la dialéctica no es sucesión genética; las bases 𝔅 alimentan a Fundamentos","`enlace45`","[T] orden de las ocho · [E] condición","M590 78 L590 206"),
 ("E5","E6","F","La sucesión genética entre horizontes no cambia el perfil","`enlace56`","[T] orden de las ocho · [E] condición","M546 222 L388 222"),
 ("E6","E7","F","Una posición implica conversión plena y horizonte auténtico; Dom(E7) = Dc","`enlace67`","[T] orden de las ocho · [E] condición","M310 254 L228 356"),
 ("E7","E8","F","Solo los sistemas que son posiciones (Sis) llegan a Comunicaciones; hz(s) es receptivo","`enlace78`","[T] orden de las ocho · [E] condición","M141 368 L118 368"),
 # retornos
 ("E8","E7","R","De la comunicación surgen problemas para la sistematización","`RetornoE8E7`, `retorno87_nicea_excluye`","[T] p. 141 (dependencia «en sentido inverso»)","M118 392 L141 392"),
 ("E7","E6","R","Los modos de conceptualización de la sistemática se emplean en las doctrinas","`RetornoE7E6`, `retorno76_nicea_excluye_sA`","[T] p. 141","M245 358 L330 253"),
 ("E6","E5","R","La conversión tiene dimensión doctrinal (`dim : horizonte → doctrina`); no toca pf ni rep","`RetornoE6E5`, `retorno65_nicea_excluye_inaut`, `fase2_recip`","[T] reciprocidad intrafase (p. 141) · [L] qué fluye (Lonergan no lo dice)","M388 238 L546 238"),
 ("E5","E4","R","Los fundamentos son principio de selección de doctrinas: cubren los perfiles de E4","`RetornoE5E4`, `retorno54_nicea_cubre_necesaria`","[T] fundamentos↔dialéctica (pp. 141-142) · [L] forma","M620 206 L620 80"),
 ("E6","E3","R","Las doctrinas se aprehenden desde la historia doctrinal (dominio de lo aprehendido)","`RetornoE6E3`, `retorno63_nicea_dominio`","[T] doctrinas↔historia (p. 142)","M368 206 L452 78"),
 ("E2","E1","R","Una cuestión pendiente de E2 pide un dato más: nueva cuestión con `falta` no vacío","`ExtE1`, `Pide`, `pideE2N`, `res_mono`, `yMalD/G/K_no_ext`","[T] interpretación↔investigación (p. 140) · [E] solo ampliar Q1, Ad, K","M276 66 L253 66"),
 ("E3","E1","R","La historia suscita cuestiones y revisa el área adoptada de E1","`ExtE1`, `Pide`, `pideE3N`, `fase1_abierta`, `fase1_no_pierde`","[T] historia↔investigación (p. 140) · [E] solo ampliar","M425 78 L425 94 L190 94 L190 80"),
 ("E3","E2","R","Las circunstancias del autor (lugar, época) cambian el contexto C2; Pend no se formaliza","`ContextoA`, `contexto_mal_excluido`, `cambiar_a_cambia_C2` (media formalizada: L13)","[T] p. 140 · [L] solo la mitad formalizable","M411 66 L388 66"),
 ("E4","E2","R","La dialéctica clasifica modos de pensamiento (perfil parcial `car2`) como estructura heurística","`ClasifE4`, `clasifE2N`, `clasif_mala_excluida`","[T] dialéctica da estructuras heurísticas (p. 140)","M590 34 L590 2 L330 2 L330 32"),
 ("E4","E3","R","Idem para los puntos de vista de la historia (clasificación parcial)","`ClasifE4`, `clasifE3N` (parcial), `clasif_mala_excluida`","[T] p. 140","M546 66 L523 66"),
 # entradas directas
 ("E0","E3","D","h ⊑ E0 y h entra en E3 (el universo U de datos es el mismo)","`CasoNicea`: misma U = Fin 4","[E] decisión de modelado","M40 34 L40 12 L490 12 L490 32"),
 ("E1","E3","D","Todo dato que E3 usa o cita como evidencia está reunido por E1 (y es relevante)","campos de `CasoNicea` (no teorema derivado)","[E] decisión de modelado","M175 34 L175 22 L440 22 L440 32"),
 ("E2","E4","D","Los resultados de E2 (R2) son ítems de la dialéctica","`Items`, `injR2`","[T] cap. 5 §IV · [E] forma","M360 78 L360 105 L560 105 L560 80"),
 ("E3","E5","D","Cada punto de vista de E3 clasificado por E4 tiene un horizonte de E5 con ese perfil","`EnlaceHz`, `hzNicea`, `hz_mal_excluido`","[E] decisión de modelado (no es cita de Lonergan)","M492 78 L566 206"),
 ("E4","E6","D","Pc, ≈, ≺ y Yo/sost/ind","`NiceaY` sobre `NiceaE4`; `NY2_no_ley` (E4 condiciona E6)","[E] componentes importados","M585 78 L372 207"),
 ("E2","E6","D","Contextos de E2 importados a Ctx de E6 (parcial, no inyectiva)","`CtxImport`, `ctxNicea` (`CicloCtx`); no entra aún en `Ciclo.Modelo`","[L]/[E] Lonergan no dice cómo","M310 78 L310 206"),
 ("E3","E6","D","Contextos de E3 importados a Ctx de E6 (idem)","`CtxImport` (`CicloCtx`)","[L]/[E]","M440 78 L352 206"),
 ("E6","E8","D","El Ap real de E6 define Rec(s); la identidad se mide contra Dc_s","`NiceaW` sobre `NiceaZ`","[E] componentes importados","M278 240 L95 356"),
 ("E5","E7","D","hz: Σ → Ω; pf, Df y Aut deciden si un sistema es posición (L14a)","`E7.Posc`, `enlace67`","[E] componentes importados","M560 253 L253 398"),
 ("E4","E7","D","Cierre transitivo TG (unidad, L6) y el par posición/contraposición","`NiceaZ` sobre `NiceaY`","[E] componentes importados","M656 62 L670 62 L670 446 L215 446 L215 404"),
 ("E2","E7","D","Niveles de certeza Ct y probabilidad Pt (cz) de E2","E7.`Ct` ↔ E2.`Grado` sigue abierto","[E] decisión pendiente","M290 78 L170 357"),
 ("E5","E8","D","hzA: Ag → Ω; Hor deriva de los horizontes de la población","`NiceaW`, `enlace78`","[E] componentes importados","M620 253 L620 428 L40 428 L40 404"),
 # hipotéticos
 ("E2","E5","H","Entenderse a sí mismo (Ξ, Alc)","sin formalizar","[L] por precisar","M376 78 L548 214"),
 ("E1","E6","H","Enlace diferido","sin formalizar","—","M220 78 L290 206"),
 ("E4","E8","H","Segundo uso de la dialéctica (Pur) al integrar las ciencias humanas","sin enlace formal con E4","[T] cap. 14 (p. 351)","M656 48 L682 48 L682 458 L90 458 L90 404"),
 ("E7","E4","H","Retorno anotado fuera de la tupla","no figura entre las 17 aristas autorizadas","—","M253 372 L610 80"),
 ("E7","E1","H","Retorno anotado fuera de la tupla","no figura entre las 17 aristas autorizadas","—","M200 358 L200 80"),
 ("E8","E0","H","Cierre externo: lo comunicado entra en la vida cristiana y de ahí salen datos nuevos para U. Solo amplía U; fuera de la tupla","`Ciclo.lean` (D); no hay primitivo `Con` E8→E1","[E] hipótesis","M24 358 L24 80"),
]
