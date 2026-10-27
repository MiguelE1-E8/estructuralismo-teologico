import E2
/-
  E2Nicea · E2 del caso común E0–E8 sobre Nicea — Lean 4 (sin Mathlib, sin sorry).

  Es un modelo de `E2.Mp` con su ley (fuerte y débil, con RE) cuya interpretación es la de Nicea:
  el sentido de ousía, hypóstasis y homooúsios en el Símbolo de Nicea (325) y en su recepción.
  Todo lo histórico es ESTIPULACIÓN de modelado (como el resto del caso); no es una historia de la exégesis.

  ─── Lectura de los índices ───────────────────────────────────────────────────────────────────────
  U (la de E0/E1 del caso): u0 carta de Eusebio de Nicomedia a Paulino de Tiro (c. 320-321) · u1 Símbolo de
     Nicea (325) · u2 Definición de Calcedonia (451) · u3 Definición de Constantinopla III (680-681),
     «compilación» que recoge definiciones anteriores (en E0 es del tipo 3, y hace de instrumento: índice de
     términos y catálogo de fuentes).
  W = Fin 3 (escritos; `inW w u := u = w`, como en E3): w0 = {u0} · w1 = {u1} · w2 = {u2}.
  Evidencia (`Ev w u := u = 3`, como en E3): Constantinopla III es la evidencia de E1 para los tres escritos.
  X1 = Fin 3 (modos de pensamiento): 0 sentido común (lenguaje de la fe sin términos de escuela) ·
     1 técnico incoativo (términos de escuela usados sin teoría articulada) · 2 teórico (distinciones sistemáticas).
     m: w0 ↦ 1 (Eusebio razona con términos de escuela para rechazar el homooúsios), w1 ↦ 1 (Nicea toma el término
     prestado sin teoría de la unidad ni de la distinción), w2 ↦ 2 (Calcedonia distingue naturaleza e hypóstasis).
  X2 = Ag × (Lg × Iv) (quién, dónde, cuándo): Ag: 0 Constantino · 1 el episcopado conciliar · 2 Eusebio de Nicomedia
     (**NUEVA lectura del índice 2**: en E3Nicea era «Máximo el Confesor», que no es autor de ninguno de los tres
     escritos); Lg: 0 Asia Menor · 1 Constantinopla · 2 Roma; Iv: 0 s. IV · 1 s. V · 2 s. VII.
     a: w0 ↦ (2,(0,0)) · w1 ↦ (1,(0,0)) · w2 ↦ (1,(0,1)).  (En E3, `(1,1,0,1)` de `Hc` coincide con w2.)
  X3 = Ob = Fin 3 (objeto que el autor tenía en mente): 0 el Hijo respecto del Padre (su ser) · 1 Cristo: divinidad
     y humanidad (una persona, dos naturalezas) · 2 la unidad y distinción en Dios (ousía / hypóstasis).
     ref: w0 ↦ 0 · w1 ↦ 0 (no 2: el Símbolo no tematiza la distinción) · w2 ↦ 1.
  H = Fin 3 (contextos reconstruidos, uno por escrito): h0 correspondencia arriana (c. 320) · h1 concilio de 325
     y su anatema · h2 controversia cristológica del s. V.  g(w, m, a, ref) = 2 si el modo es el teórico y w si no
     (leer con modo teórico lleva al contexto del s. V: el anacronismo tiene efecto).
  S = Fin 3 (sentidos): s0 en Nicea, ousía e hypóstasis son sinónimos (la «realidad» del Padre) y el homooúsios dice
     que el Hijo es de la misma realidad, no una criatura · s1 en Eusebio, el homooúsios implicaría dividir o identificar
     la sustancia, y por eso lo rechaza · s2 en Calcedonia, ousía es naturaleza e hypóstasis es el subsistente: se
     distinguen.  σ(h0) = s1, σ(h1) = s0, σ(h2) = s2.
  Q = Cuestiones = Fin 3: q0 ¿son sinónimos ousía e hypóstasis en el anatema? · q1 ¿el homooúsios dice identidad
     numérica o semejanza específica? · q2 ¿qué trasfondo (Antioquía 268, Pablo de Samosata) tiene el rechazo?
  Grados: w0 altamente probable (queda q2) · w1 probable (queda q1: es lo discutido) · w2 cierto (nada pendiente).
  R = Unit: E3 y E4 del caso toman `R2` de `M3.xM`, y `itm` de `CicloNicea` usa `⟨(), ⟨0, rfl⟩⟩`. El resultado de E2 es
     un único elemento, y el contenido va en S y en Jz.

  ─── Relación con p₃ de E4 (tesis contraria, perfil (1,0,0)) ───────────────────────────────────
  E2 solo establece qué quisieron decir los autores (m*, a*, ref*), no si el dogma desarrolla o desfigura. El ítem de p₃ es
  ese resultado leído como tesis cerrada: «los términos no estaban diferenciados en Nicea y la distinción es posterior».
  Que esa lectura excluya el desarrollo ya no es resultado de E2: sale de un horizonte (1,0,0) y es lo que E4 registra como
  discrepancia (§7.12 del Doc de E2: la divergencia no se debe a la evidencia). Aquí se prueba solo lo que E2 sí establece.

  ─── Citas de Lonergan (Método en teología, Sígueme, Salamanca 1988, cap. 7 «Interpretación») ──────
  Abreviatura [L p. N]: página impresa N de esa edición. Las páginas se leyeron de una extracción OCR del capítulo y
  pueden desviarse en una página donde el escaneo mezcla bloques (pp. 160-162). Solo se cita el cap. 7: el texto de
  Lonergan sobre Nicea mismo (capítulo de las doctrinas) no estaba disponible, así que no se cita.
  - Objeto → `ref`: «saber qué objetos, reales o imaginarios, tenía en mente el autor del texto» [L p. 152].
  - Palabras → `m`, `S`: «el autor puede estar hablando de P y el lector puede estar pensando en Q» [L p. 154];
    el intérprete, a diferencia del controversista, «considera la posibilidad de su propia equivocación» [L p. 154].
  - Autor → `a` (X2 = Ag × Lg × Iv): se trata de entender al autor, «su país, su lengua, su época, su cultura, su manera
    de vivir y su mentalidad» [L p. 155]; entender el sentido común del otro es «entender lo que él diría en cualquiera
    de las situaciones que se presentan comúnmente en su lugar y tiempo» [L p. 156].
  - Contexto → `H`, `Pt`: «el contexto es un nido de preguntas y respuestas interconexas y entretejidas» [L p. 158].
  - Criterio de corrección → `Pend`, `Jz`: no quedan «cuestiones ulteriores susceptibles de conducir a ulteriores
    intelecciones que completen, maticen o rectifiquen» [L p. 157]; «si realmente no surgen cuestiones ulteriores, su
    interpretación será cierta» [L p. 162]; el grado: «probable, altamente probable y, quizás, en algunos aspectos,
    cierta» [L p. 160]; el exegeta «deberá presentar su contribución modestamente» [L p. 162].
  - Reconstruir, no reproducir → `m*`, `a*`, `ref*` como lo que se gestaba: «el intérprete o el historiador
    reconstruye el pasado, pero no es verdad que lo reproduzca en su pensamiento» [L p. 161].
  - Anacronismo → `RetroE2` y los teoremas `retro_*`: el exegeta «tendrá cuidado de evitar cualquier transposición
    prematura a un lenguaje posterior, aunque este lenguaje haya sido aprobado por una tradición teológica» [L p. 166];
    su lenguaje no debe ser «el del Enchiridion de Denzinger» [L p. 164].
  - Evidencia → `Ev`, RE: la crítica textual determina «lo que escribió» y no «lo que el autor quiso significar»
    [L p. 163]; el intérprete usa los instrumentos de la investigación (cronologías, léxicos…) [L p. 165]. Ninguna
    cita dice que la evidencia fije m*, a*, ref*; RE es decisión de modelado (§8.6 del Doc).
  - Relación con p₃: las divergencias «no pueden eliminarse con un estudio ulterior de los datos, ya que sus divergencias
    surgen de la opción y de los horizontes personales de cada uno» [L pp. 162-163, a propósito de la dialéctica].

  ─── Límites ────────────────────────────────────────────────────────────────────────────────
  - Nicea 325, Calcedonia 451, el anatema del Símbolo («de otra hypóstasis u ousía»), la sinonimia de los términos en Nicea
    y su distinción por los capadocios no se han verificado hoy en fuentes (el encargo los lista como pendientes).
  - Lo que no varía en este modelo: R (Unit) y los tipos de W y X1.
-/
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 200000
namespace E2Nicea
open E2

/-! ## El modelo potencial -/

abbrev senseOf (w : Fin 3) : Fin 3 := if w.val = 0 then 1 else if w.val = 1 then 0 else 2

abbrev ptN (w : Fin 3) : List (Fin 3) :=
  if w.val = 0 then [1, 2] else if w.val = 1 then [0, 1, 2] else [0]

abbrev pendN (w : Fin 3) : List (Fin 3) :=
  if w.val = 0 then [2] else if w.val = 1 then [1] else []

abbrev mT (w : Fin 3) : Fin 3 := if w.val = 2 then 2 else 1
abbrev aT (w : Fin 3) : Fin 3 × (Fin 3 × Fin 3) :=
  if w.val = 0 then (2, (0, 0)) else if w.val = 1 then (1, (0, 0)) else (1, (0, 1))
abbrev rT (w : Fin 3) : Fin 3 := if w.val = 2 then 1 else 0

/-- E2 del caso Nicea: tres escritos, tres sentidos, tres grados. -/
abbrev NiceaE2 : Mp (Fin 3) (Fin 3) (Fin 3 × (Fin 3 × Fin 3)) (Fin 3) (Fin 3) (Fin 3) Unit (Fin 3) where
  m := mT
  a := aT
  ref := rT
  g := fun w x _ _ => if x.val = 2 then 2 else w
  sg := fun h => if h.val = 0 then 1 else if h.val = 1 then 0 else 2
  Pt := ptN
  Pend := fun w s => if s = senseOf w then pendN w else ptN w
  Jz := fun w s =>
    if s = senseOf w then (if w.val = 2 then Grado.cierto else if w.val = 0 then Grado.altamente_probable else Grado.probable)
    else Grado.probable
  O2 := fun _ _ _ => ()
  pend_sub := by decide
  jz_cierto := by decide

/-- Mp′: lo que el autor efectivamente tenía (m*, a*, ref*) es lo estipulado. -/
abbrev NiceaE2F : MpF (Fin 3) (Fin 3) (Fin 3 × (Fin 3 × Fin 3)) (Fin 3) (Fin 3) (Fin 3) Unit (Fin 3) :=
  { toMp := NiceaE2, mS := mT, aS := aT, rS := rT }

/-- Ley fuerte: la reconstrucción usó lo propio de cada autor. -/
theorem ley_fuerte : LeyFuerte NiceaE2F := by
  unfold LeyFuerte
  decide

/-! ## Evidencia de E1 y ley débil

  `Ev` es el de E3 (`u = 3`: Constantinopla III, compilación que recoge definiciones anteriores). La compatibilidad se
  define como en §7.15 del Doc: `Em w x ⇔ ∀ u ∈ Ev w, ok w u x`, antitónica en la evidencia por construcción. -/

abbrev evN (_ : Fin 3) (u : Fin 4) : Prop := u.val = 3
abbrev inWN (w : Fin 3) (u : Fin 4) : Prop := u.val = w.val

abbrev compat {W U α : Type} (Ev : W → U → Prop) (ok : W → U → α → Prop) : W → α → Prop :=
  fun w x => ∀ u, Ev w u → ok w u x

/-- Más evidencia deja menos candidatos compatibles. -/
theorem compat_antitona {W U α : Type} (Ev Ev' : W → U → Prop) (ok : W → U → α → Prop)
    (h : ∀ w u, Ev w u → Ev' w u) : ∀ w x, compat Ev' ok w x → compat Ev ok w x :=
  fun w _ hc u hu => hc u (h w u hu)

/-- Constantinopla III, leída como compilación de definiciones anteriores, es compatible con que los escritos anteriores
    a Calcedonia usen términos de escuela sin teoría (modos 0 y 1), y con que Calcedonia use el modo teórico. -/
abbrev okM (w : Fin 3) (u : Fin 4) (x : Fin 3) : Prop :=
  u.val = 3 → ((w.val ≤ 1 → x.val ≤ 1) ∧ (w.val = 2 → 1 ≤ x.val))

/-- La compilación sitúa cada escrito en su época: s. IV los dos primeros y s. V el tercero. -/
abbrev okA (w : Fin 3) (u : Fin 4) (a : Fin 3 × (Fin 3 × Fin 3)) : Prop :=
  u.val = 3 → ((w.val ≤ 1 → a.2.2.val = 0) ∧ (w.val = 2 → a.2.2.val = 1))

/-- Objetos: el Hijo respecto del Padre o la unidad y distinción en Dios (antes de Calcedonia); la unión en Cristo o esa
    unidad y distinción (Calcedonia). -/
abbrev okO (w : Fin 3) (u : Fin 4) (r : Fin 3) : Prop :=
  u.val = 3 → ((w.val ≤ 1 → r.val = 0 ∨ r.val = 2) ∧ (w.val = 2 → r.val = 1 ∨ r.val = 2))

abbrev NiceaE2D : MpD (Fin 3) (Fin 3) (Fin 3 × (Fin 3 × Fin 3)) (Fin 3) (Fin 3) (Fin 3) Unit (Fin 3) :=
  { toMp := NiceaE2, Em := compat evN okM, Ea := compat evN okA, Er := compat evN okO }

/-- Ley débil: lo que usó el intérprete es compatible con la evidencia. -/
theorem ley_debil : LeyDebil NiceaE2D := by
  show ∀ w : Fin 3, (∀ u : Fin 4, evN w u → okM w u (mT w)) ∧ (∀ u : Fin 4, evN w u → okA w u (aT w)) ∧
    (∀ u : Fin 4, evN w u → okO w u (rT w))
  decide

/-- El modelo parcial ⟨Em, Ea, Er⟩ que E1 ofrece (E1 → E2). -/
abbrev pN : Mpp (Fin 3) (Fin 3) (Fin 3 × (Fin 3 × Fin 3)) (Fin 3) :=
  ⟨compat evN okM, compat evN okA, compat evN okO⟩

/-- RE: lo propio de cada autor es compatible con la evidencia. -/
theorem re_nicea : RE pN NiceaE2F := by
  show ∀ w : Fin 3, (∀ u : Fin 4, evN w u → okM w u (mT w)) ∧ (∀ u : Fin 4, evN w u → okA w u (aT w)) ∧
    (∀ u : Fin 4, evN w u → okO w u (rT w))
  decide

/-- Contenido empírico cumplido: el modelo parcial se extiende a un modelo de la Ley fuerte con RE. -/
theorem nicea_extiende : Extiende pN :=
  ⟨Fin 3, Fin 3, Unit, Fin 3, NiceaE2F, ley_fuerte, re_nicea⟩

/-- Con RE, la ley fuerte implica la débil (instancia de `fuerte_RE_implica_debil`). -/
theorem debil_de_fuerte : ∀ w, pN.Em w (NiceaE2.m w) ∧ pN.Ea w (NiceaE2.a w) ∧ pN.Er w (NiceaE2.ref w) :=
  fuerte_RE_implica_debil pN NiceaE2F ley_fuerte re_nicea

/-! ## Lectura: qué establece E2 sobre ousía, hypóstasis y homooúsios -/

/-- En el sentido s, ousía e hypóstasis son sinónimas (no se diferencian). Entender las palabras [L pp. 154-155]. -/
abbrev sinonimos (s : Fin 3) : Prop := s.val ≤ 1
/-- En el sentido s se distingue la naturaleza (ousía) del subsistente (hypóstasis). -/
abbrev distingue (s : Fin 3) : Prop := s.val = 2

theorem nicea_sinonimos : sinonimos (NiceaE2.O1 1) := by decide
theorem nicea_no_distingue : ¬ distingue (NiceaE2.O1 1) := by decide
theorem calcedonia_distingue : distingue (NiceaE2.O1 2) := by decide

/-- La distinción es posterior: ningún escrito anterior a Calcedonia la tiene, y Calcedonia sí. -/
theorem distincion_posterior :
    (∀ w : Fin 3, w.val ≤ 1 → ¬ distingue (NiceaE2.O1 w)) ∧ distingue (NiceaE2.O1 2) := by decide

/-- Entender el objeto [L p. 152]: lo que Nicea tenía en mente no es la unidad y distinción en Dios (objeto 2) sino el Hijo respecto del Padre (objeto 0). -/
theorem nicea_objeto : NiceaE2.ref 1 = 0 ∧ NiceaE2.ref 1 ≠ 2 := by decide

/-- Los tres grados aparecen, y solo Calcedonia es cierta [L pp. 160, 162]. -/
theorem grados :
    NiceaE2.Jz 0 (NiceaE2.O1 0) = Grado.altamente_probable ∧
    NiceaE2.Jz 1 (NiceaE2.O1 1) = Grado.probable ∧
    NiceaE2.Jz 2 (NiceaE2.O1 2) = Grado.cierto := by decide

/-- Criterio de la sección VI [L p. 157]: la pendiente de Nicea es q1: ¿identidad numérica o semejanza específica? (por eso es solo probable). -/
theorem nicea_pendiente : NiceaE2.Pend 1 (NiceaE2.O1 1) = [1] := by decide

theorem nicea_no_cierta : NiceaE2.Jz 1 (NiceaE2.O1 1) ≠ Grado.cierto := by decide

/-- El resultado de E2 existe en la imagen: hay un elemento de `R2` para cada escrito (el ítem de p₃ en `CicloNicea`). -/
theorem imagen_no_vacia : ∃ r, ∃ w, NiceaE2.E2 w = r := ⟨(), 0, rfl⟩

/-! ## Negativos: la lectura anacrónica -/

/-- «Transposición prematura a un lenguaje posterior» [L p. 166]. Leer a los escritos anteriores a Calcedonia con el modo teórico (lo que hacen las lecturas que proyectan la metafísica
    plena hacia atrás): m(w1) y m(w2) = 2. -/
abbrev retroM (w : Fin 3) : Fin 3 := if w.val = 0 then 1 else 2

abbrev RetroE2 : Mp (Fin 3) (Fin 3) (Fin 3 × (Fin 3 × Fin 3)) (Fin 3) (Fin 3) (Fin 3) Unit (Fin 3) :=
  { NiceaE2 with m := retroM }

/-- El modo importa al sentido: con el modo teórico, Nicea queda leída en el sentido de Calcedonia. -/
theorem retro_sentido : RetroE2.O1 1 = 2 ∧ NiceaE2.O1 1 = 0 := by decide

theorem retro_distingue : distingue (RetroE2.O1 1) := by decide

/-- … y esa lectura no alcanza la certeza: con otro sentido queda todo pendiente. -/
theorem retro_no_cierta : RetroE2.Jz 1 (RetroE2.O1 1) ≠ Grado.cierto := by decide

abbrev RetroF : MpF (Fin 3) (Fin 3) (Fin 3 × (Fin 3 × Fin 3)) (Fin 3) (Fin 3) (Fin 3) Unit (Fin 3) :=
  { toMp := RetroE2, mS := mT, aS := aT, rS := rT }

/-- Un intérprete anacrónico no cumple la Ley fuerte (el «su propio» del modo de pensamiento, [L p. 156]): usó un modo que el autor no tenía. -/
theorem retro_no_ley : ¬ LeyFuerte RetroF := by
  intro h
  exact absurd (h 1).1 (by decide)

/-- Una afirmación retroactiva del autor: m*(w1) = 2. La Ley se cumple (m = m*), pero RE falla: la evidencia de E1 refuta
    que el autor de Nicea tuviera ese modo. -/
abbrev RetroStarF : MpF (Fin 3) (Fin 3) (Fin 3 × (Fin 3 × Fin 3)) (Fin 3) (Fin 3) (Fin 3) Unit (Fin 3) :=
  { toMp := RetroE2, mS := retroM, aS := aT, rS := rT }

theorem retroStar_ley : LeyFuerte RetroStarF := by
  unfold LeyFuerte
  decide

theorem retroStar_no_RE : ¬ RE pN RetroStarF := by
  intro h
  exact absurd (h 1).1 (by decide)

/-! ## Interfaz con E3: lo que necesita L3 -/

/-- Autor y lugar-época de cada escrito, leídos de `a` (L3 de E3). -/
abbrev auN (f : Fin 3) : Fin 3 := (NiceaE2.a f).1
abbrev ubN (f : Fin 3) : Fin 3 × Fin 3 := (NiceaE2.a f).2

theorem tabla_au_ub :
    (auN 0 = 2 ∧ ubN 0 = (0, 0)) ∧ (auN 1 = 1 ∧ ubN 1 = (0, 0)) ∧ (auN 2 = 1 ∧ ubN 2 = (0, 1)) := by decide

/-- La primera conjunción de L3: `xM` es la parte de Mp de un modelo de la Ley fuerte y de otro de la débil. -/
theorem L3_para_E3 :
    (∃ xf : MpF (Fin 3) (Fin 3) (Fin 3 × (Fin 3 × Fin 3)) (Fin 3) (Fin 3) (Fin 3) Unit (Fin 3),
        xf.toMp = NiceaE2 ∧ LeyFuerte xf) ∧
    (∃ xd : MpD (Fin 3) (Fin 3) (Fin 3 × (Fin 3 × Fin 3)) (Fin 3) (Fin 3) (Fin 3) Unit (Fin 3),
        xd.toMp = NiceaE2 ∧ LeyDebil xd) :=
  ⟨⟨NiceaE2F, rfl, ley_fuerte⟩, ⟨NiceaE2D, rfl, ley_debil⟩⟩

/-- `ref` no entra en `au` ni en `ub`: dos E2 que solo difieren en `ref` dan el mismo autor y lugar. -/
theorem au_ub_indep_ref (x : Mp (Fin 3) (Fin 3) (Fin 3 × (Fin 3 × Fin 3)) (Fin 3) (Fin 3) (Fin 3) Unit (Fin 3))
    (h : x.a = NiceaE2.a) (f : Fin 3) : (x.a f).1 = auN f ∧ (x.a f).2 = ubN f := by
  rw [h]; exact ⟨rfl, rfl⟩

#print axioms ley_fuerte
#print axioms ley_debil
#print axioms re_nicea
#print axioms nicea_extiende
#print axioms distincion_posterior
#print axioms retro_sentido
#print axioms retro_no_ley
#print axioms retroStar_no_RE
#print axioms L3_para_E3
#print axioms compat_antitona

end E2Nicea
