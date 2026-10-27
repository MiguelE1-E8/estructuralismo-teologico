import E3
import E2Nicea
/-
  E3Nicea · E3 del caso común Nicea–Constantinopla III, sobre el E2 nicénico (`E2Nicea.NiceaE2`) — Lean 4 (sin Mathlib, sin sorry).

  `NiceaE3 := { B with … }` conserva los TIPOS de `E3.B` salvo los de la interfaz con E2 (`H, S, Ob, Q2 := Fin 3`) y cambia
  valores: `xM := NiceaE2`, `au`/`ub` se leen de `a` (L3), `src`, `dc`, `ip`, `tg`. L1–L20 se re-prueban (`NiceaE3_ley`,
  que parte de `B_ley` y rehace solo L3 y L15). Se mantienen `NiceaE3`, `NiceaE3_ley` y `NiceaE3_inc : Inc 1 2`.
  Todo lo histórico es ESTIPULACIÓN de modelado (no historia de la exégesis ni de los concilios).

  Citas de Lonergan: *Método en teología*, Sígueme, Salamanca 1988, cap. 8 «Historia» y cap. 9 «Historia e historiadores».
  [L p. N] = página impresa N de esa edición, leída de la capa de texto (OCR) del PDF; solo se cita lo que está en esos
  dos capítulos. El texto de Lonergan sobre Nicea mismo (doctrinas) no estaba disponible y no se cita.

  ─── Lectura de los índices ───────────────────────────────────────────────────────────────────────
  Escritos (W = Fu = Fin 3; `fw = id`, como en E2Nicea) y datos (Dat = U = Fin 4; `datU = id`; `inW w u := u = w`;
    `src d f := d = f`): f₀ = carta de Eusebio de Nicomedia a Paulino de Tiro (c. 320-321) · f₁ = Símbolo de Nicea (325) ·
    f₂ = Definición de Calcedonia (451). d₃ = Definición de Constantinopla III (680-681): «compilación» que recoge definiciones
    anteriores; no es una fuente de la serie sino la evidencia (`Ev w u := u = 3`) y no tiene `src`.
    CAMBIO respecto de la versión anterior: antes Fu₀ = Símbolo y las fuentes se desplazaban un lugar respecto de U (E0/E1);
    ahora E3, E2 y E1 usan la misma lectura de U.
  Agentes (Ag = Fin 3): 0 Constantino · 1 el episcopado conciliar · 2 Eusebio de Nicomedia (antes «Máximo el Confesor», que no
    es autor de ninguno de los tres escritos; lo corrige la pestaña de E2).
  Lugares (Lg): 0 Asia Menor (Nicea, Calcedonia) · 1 Constantinopla · 2 Roma. Intervalos (Iv): 0 s. IV · 1 s. V · 2 s. VII.
  L3: `au f = (a f).1`, `ub f = (a f).2` con `a = (autor, (lugar, época))`: f₀ ↦ (2,(0,0)), f₁ ↦ (1,(0,0)), f₂ ↦ (1,(0,1)).
    [L p. 155]: entender al autor es entender «su país, su lengua, su época, su cultura, su manera de vivir y su mentalidad»;
    `ref` (el objeto) queda aparte [L p. 152, cap. 7, citado por la pestaña de E2].
  Hechos básicos (`Hc`): (0,0,0,0) Constantino convoca y preside Nicea (Asia Menor, s. IV); (1,1,0,1) el episcopado define en
    Calcedonia las dos naturalezas (Asia Menor, s. V), que coincide con `a(f₂)`. `ev3 q₂`, `Jz3 q₂ = cierto`: q₂ se responde con
    d₂ = la definición de Calcedonia (ahora de f₂ = Calcedonia, no de Constantinopla III). Sobre el hecho como «concreto»,
    «preciso» e «innegable» y su relación con la cuestión agotada [L p. 196]; «los datos son una cosa y los hechos son otra» [L p. 195].
  Movimientos (Mv = Fin 4; `tp` de B): 0 cultural (helenización del lenguaje cristiano: ousía, hypóstasis, homooúsios) ·
    1 institucional (sistema conciliar-imperial) · 2 doctrinal (controversia trinitaria, 325 y 381) · 3 doctrinal (controversia
    cristológica, 431, 451 y 680-681).
  Narraciones canónicas (L10: Cp mi = r1, Cp mc = r2, Cp md = r3): r1 institucional (la Iglesia imperial frente a arrianos y
    monotelitas) · r2 cultural (fe bíblica y pensamiento griego) · r3 doctrinal (desarrollo de las doctrinas, de Nicea a
    Constantinopla III).
  Enunciados en contradicción (`ctr`: 1 ↔ 3): e₁ (lo sostiene r2) «traducir al griego cambió el contenido» (tesis de la
    helenización como desfiguración, Harnack); e₃ (lo sostiene r3) «el dogma desarrolla de modo homogéneo lo que el evangelio
    ya decía» (tesis del desarrollo, Newman; Lonergan en «The Way to Nicea»).
  Factor perturbador (`ip`): r3 (n = 2) y ν″ (n = 5): la intervención imperial en el rumbo doctrinal (Constantino y Constancio II
    en el s. IV; Ekthesis de Heraclio y Typos de Constante II, 648, en el monotelismo).
    Lonergan: la historia crítica «se mueve por sí misma hacia el conocimiento objetivo del pasado, aunque puede ser impedida
    por factores tales como puntos de vista erróneos acerca de la posibilidad, por juicios de valor equivocados o engañosos, o por
    una visión del mundo, o una óptica o estado de la cuestión inadecuados» [L p. 188] (ceteris paribus, L15).
    Las narraciones históricas «tienen que ser compatibles entre sí y tender a formar una sola visión» [L p. 212], y el
    perspectivismo «da cuenta de las diferencias entre los relatos históricos, pero no de las incompatibilidades» [L p. 217, n. 91]:
    por eso la incompatibilidad r2/r3 exige un factor (`Ip`) y su solución «no pertenece a esta especialización funcional […]
    sino a especializaciones posteriores, como la dialéctica y la explicitación de los fundamentos» [L p. 217].
  Perspectivas (n = 3, 4, 5; `vn`: 3 ↦ vista 0, 4 y 5 ↦ vista 1): ν = Nicea según la memoria atanasiana; ν′ = según los
    eusebianos; ν″ = lectura de Constantinopla III desde el horizonte de la vista 1. ν y ν′ difieren sin incompatibilidad
    (`perspectivas_no_incompatibles`): el perspectivismo resulta de que el historiador es limitado, de que la selección no puede
    objetivarse del todo y de que hay diferencias de horizonte [L p. 211].
  Procesos de gestación (Pr = Fin 3; `Pg` = {γ₀, γ₁}, `Rut` = {γ₂}; `tg` cambia respecto de B): γ₀ diseminación (la fórmula de
    Nicea se extiende y se impone, de 325 a 381) · γ₁ decadencia (el Typos de Constante II, 648, prohíbe discutir si en Cristo hay
    una o dos voluntades: se suprime la pregunta) · γ₂ rutina (repetición litúrgica del símbolo; fuera de `Pg`, L8).
    [L p. 172]: «Por «irse gestando» entiendo la exclusión de la mera repetición de una rutina. Entiendo el cambio que originó la
    rutina y su diseminación. Entiendo el proceso y el desarrollo pero, no menos, la decadencia y la desintegración».
  Lectura de la lógica del proceso de B donde es coherente con la historia crítica: la serie de cuestiones (L5, «pista correcta»
    [L p. 180-181]); el proceso ocurre «dos veces», sobre las fuentes y sobre el objeto [L p. 182]; es «heurístico, extático,
    selectivo, crítico, constructivo» y también «reflexivo y judicativo» [L pp. 182-184]; el juicio es verdadero cuando «ya no hay
    cuestiones ulteriores pertinentes» [L p. 184] (L6, `Pend3 = [] ↔ Jz3 = cierto`); una fuente se usa directa o indirectamente
    (como elemento de prueba de «sus intenciones»: «procedimiento indirecto basado en su narración») [L p. 182; L p. 201] (L7).
  Horizontes y credibilidad (nuevo, 20-oct; lectura propuesta, valores estipulados): dos horizontes, v₀ (tipo Harnack: el dogma se
    transforma al helenizarse) y v₁ (tipo Newman: desarrollo con continuidad) [L pp. 214-215, caso Becker]. α₀ el Símbolo de Nicea
    incluye el homoousios (sin choque); α₁ el Símbolo presenta la fórmula como expresión de la fe recibida; α₂ Calcedonia entiende
    el homoousios en el sentido de Nicea (la Definición ratifica el Símbolo de 325 y el de Constantinopla). v₀ da por imposibles α₁ y α₂.
    α₂ se lee primero como testimonio directo (cr = 2: choque) y luego como indicio indirecto de lo que querían sus autores
    (cr = 0: el choque se disuelve), con la fuente usada «dos veces» [L p. 182] y la revisión motivada (L13) [L p. 201]. α₁ conserva
    su credibilidad: el choque es de horizonte y no se resuelve revisando fuentes [L pp. 214-217]; pasa a la dialéctica (E4).
    `dos_tipos_de_choque`. Negativos: ocho variantes de `NiceaE3` que violan UNA cláusula (L3, L8, L10, L13, L15, L16, L18, L20),
    reunidas en `negativos`.
  Lo que NO tiene referente histórico asignado: las cuestiones q₀, q₁ y q₃, los datos d₀…d₂ fuera de lo dicho arriba, las ideas (Ih),
    las conjeturas (Cj), los juicios de valor (Jh) y el tipo-ideal (Ti). Los valores de `cr` y la asignación de α₀–α₂ a las fuentes
    son estipulaciones del modelo, no resultados de investigación. Los cardinales de B (6 narraciones, 4 movimientos) son
    minúsculos para una historia real: es una instanciación mínima de cada cláusula, no una historia de los concilios.
  Verificación histórica (20-oct, fuentes web consultadas):
    · Ekthesis: 638, emperador Heraclio con el patriarca Sergio; enseña una sola voluntad (en.wikipedia.org/wiki/Ecthesis). CONFIRMADO.
    · Nicea: 325, convocado por Constantino; el credo incluye homoousios (orthodoxwiki.org/First_Council_of_Nicea). CONFIRMADO.
      (Que Eusebio de Nicomedia presentó un credo arriano que fue rechazado lo dice esa misma fuente, de tradición ortodoxa:
      no se usa en el modelo.)
    · Calcedonia: 451; la Definición ratifica el Símbolo de 325 y el de Constantinopla 381 (en.wikipedia.org/wiki/Chalcedonian_Definition).
      CONFIRMADO.
    · Harnack: Lehrbuch der Dogmengeschichte (1886-89; 4.ª ed. 1909); el dogma como obra del espíritu griego helenístico
      (Britannica). CONFIRMADO en lo básico. La etiqueta «desfiguración» es interpretación mía y no la dice la fuente consultada.
    · Newman: Essay on the Development of Christian Doctrine (1845); desarrollo orgánico frente a corrupción, con siete notas
      (cbcew.org.uk). CONFIRMADO en lo básico. «Homogéneo» como adjetivo de Newman no se verificó.
    · Ya confirmados el 19-oct: Typos 648 (Constante II), Constantinopla III 680-681, carta de Eusebio de Nicomedia c. 320-321.
    Sigue pendiente leer las obras de Harnack y Newman, no resúmenes: las fuentes consultadas son secundarias o de divulgación.
-/
namespace E3

/-- Credibilidad de las afirmaciones del caso (As = Fin 3, Cd = Fin 3; cd_c = 1):
    α₀ (el Símbolo de Nicea incluye el homoousios): cd₂ = 1, estable;
    α₁ (el Símbolo presenta la fórmula como expresión de la fe recibida): 2, estable;
    α₂ (Calcedonia entiende el homoousios en el sentido de Nicea): 2 si se lee su declaración de continuidad como
    testimonio directo (n = 0) y 0 si se la lee como indicio indirecto de lo que querían sus autores (n ≥ 1). -/
def crN (n : Nat) (a : Fin 3) : Fin 3 := if a = 2 then (if n = 0 then 2 else 0) else if a = 1 then 2 else 1

/-- E3 del caso Nicea: forma de `E3.B` con dos narraciones canónicas (r2, r3) incompatibles; r3 y ν″ impedidas. -/
abbrev NiceaE3 : Mp :=
  { B with
    H := Fin 3, S := Fin 3, Ob := Fin 3, Q2 := Fin 3
    xM := E2Nicea.NiceaE2
    au := fun f => (E2Nicea.NiceaE2.a f).1
    ub := fun f => (E2Nicea.NiceaE2.a f).2
    src := fun d f => d.val = f.val
    dc := fun n e => (n.val = 3 ∧ (e = 0 ∨ e = 1)) ∨ (n.val = 4 ∧ e = 2) ∨ (n.val = 5 ∧ e = 3) ∨
                     (n.val = 1 ∧ e = 1) ∨ (n.val = 2 ∧ e = 3)
    ip := fun _ n => n.val = 5 ∨ n.val = 2
    tg := fun g => if g.val = 0 then Tg.diseminacion else Tg.decadencia
    cr := crN
    -- el horizonte v₀ (tipo Harnack: el dogma se transforma al helenizarse) da por imposibles α₁ y α₂;
    -- el horizonte v₁ (tipo Newman: desarrollo con continuidad) no da por imposible ninguna
    vd := fun z a => z.val = 0 ∧ (a.val = 1 ∨ a.val = 2) }

private theorem crN_cambia (n : Nat) (a : Fin 3) (h : crN (n+1) a ≠ crN n a) : a = 2 ∧ n = 0 := by
  unfold crN at h
  by_cases ha : a = 2
  · subst ha
    by_cases hn : n = 0
    · exact ⟨rfl, hn⟩
    · exfalso; apply h; simp [hn]
  · exfalso; apply h; simp [ha]

private theorem aux15N (n n' : Fin 6) (e e' : Fin 4)
    (h1 : (n.val = 3 ∧ (e = 0 ∨ e = 1)) ∨ (n.val = 4 ∧ e = 2) ∨ (n.val = 5 ∧ e = 3) ∨
          (n.val = 1 ∧ e = 1) ∨ (n.val = 2 ∧ e = 3))
    (h2 : (n'.val = 3 ∧ (e' = 0 ∨ e' = 1)) ∨ (n'.val = 4 ∧ e' = 2) ∨ (n'.val = 5 ∧ e' = 3) ∨
          (n'.val = 1 ∧ e' = 1) ∨ (n'.val = 2 ∧ e' = 3))
    (h3 : (e = 1 ∧ e' = 3) ∨ (e = 3 ∧ e' = 1)) :
    (n.val = 5 ∨ n.val = 2) ∨ (n'.val = 5 ∨ n'.val = 2) := by
  rcases h3 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp at h1 h2 <;> omega

theorem NiceaE3_ley : Ley NiceaE3 :=
  { B_ley with
    L3 := ⟨Or.inl E2Nicea.L3_para_E3.1, fun _ => ⟨rfl, rfl⟩⟩
    L13 := fun n f h =>
      B_ley.L13 n f (h.elim Or.inl (fun ⟨a, ha, hc⟩ =>
        Or.inr ⟨a, ha, by obtain ⟨rfl, rfl⟩ := crN_cambia n a hc; exact B_cr_motivado⟩))
    L15 := by
      intro n n' h
      obtain ⟨e, e', h1, h2, h3⟩ := h
      rcases aux15N n n' e e' h1 h2 h3 with h5 | h5
      · exact Or.inl ⟨(), h5⟩
      · exact Or.inr ⟨(), h5⟩ }

/-- Las narraciones canónicas r2 (cultural) y r3 (doctrinal) son incompatibles. -/
theorem NiceaE3_inc : NiceaE3.Inc 1 2 :=
  ⟨1, 3, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))), Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))),
   Or.inl ⟨rfl, rfl⟩⟩

/-! ## Lectura histórica: los teoremas con nombre -/
namespace Hist

/-- Los cuatro movimientos son: helenización (cultural), sistema conciliar-imperial (institucional) y las
    dos controversias (doctrinales). -/
theorem movimientos_tipos :
    NiceaE3.tp 0 = Tipo.mc ∧ NiceaE3.tp 1 = Tipo.mi ∧ NiceaE3.tp 2 = Tipo.md ∧ NiceaE3.tp 3 = Tipo.md := by
  decide

/-- Las tres narraciones canónicas del caso: institucional, cultural, doctrinal (L10). -/
theorem canonicas :
    NiceaE3.Cp Tipo.mi = NiceaE3.r1 ∧ NiceaE3.Cp Tipo.mc = NiceaE3.r2 ∧ NiceaE3.Cp Tipo.md = NiceaE3.r3 :=
  ⟨NiceaE3_ley.L10.1, NiceaE3_ley.L10.2.1, NiceaE3_ley.L10.2.2.1⟩

/-- La narración cultural (helenización) y la doctrinal (desarrollo) son incompatibles. -/
theorem cultural_vs_doctrinal : NiceaE3.Inc NiceaE3.r2 NiceaE3.r3 := NiceaE3_inc

/-- La narración doctrinal está afectada por un factor perturbador (la intervención imperial). -/
theorem doctrinal_perturbada : NiceaE3.Ip NiceaE3.r3 := ⟨(), Or.inr rfl⟩

/-- La narración cultural no lo está. -/
theorem cultural_no_perturbada : ¬ NiceaE3.Ip NiceaE3.r2 := by
  rintro ⟨_, h⟩
  change (1 : Fin 6).val = 5 ∨ (1 : Fin 6).val = 2 at h
  omega

/-- La incompatibilidad no puede resolverse en E3: lo impide el factor perturbador (instancia de L15). -/
theorem incompatibilidad_sin_resolver_en_E3 :
    NiceaE3.Inc NiceaE3.r2 NiceaE3.r3 ∧ NiceaE3.Ip NiceaE3.r3 :=
  ⟨cultural_vs_doctrinal, doctrinal_perturbada⟩

/-- Si el factor imperial no actuara sobre ninguna de las dos, no habría incompatibilidad (ceteris paribus):
    la incompatibilidad del caso depende del factor perturbador, no de las narraciones solas. -/
theorem sin_factor_no_hay_inc (h1 : ¬ NiceaE3.Ip NiceaE3.r2) (h2 : ¬ NiceaE3.Ip NiceaE3.r3) :
    ¬ NiceaE3.Inc NiceaE3.r2 NiceaE3.r3 :=
  sin_impedimento_no_inc NiceaE3 NiceaE3_ley _ _ h1 h2

/-- Las perspectivas ν (memoria atanasiana) y ν′ (eusebianos) difieren de punto de vista sin ser incompatibles. -/
theorem perspectivas_no_incompatibles : ¬ NiceaE3.Inc 3 4 := by
  have h : ∀ n : Fin 6, n.val ≤ 4 → n.val ≠ 2 → ¬ NiceaE3.Ip n := by
    rintro n h1 h2 ⟨_, h⟩
    change n.val = 5 ∨ n.val = 2 at h
    omega
  exact sin_impedimento_no_inc NiceaE3 NiceaE3_ley 3 4 (h 3 (by decide) (by decide)) (h 4 (by decide) (by decide))

/-! ### Declive (D6, lado de E3) -/

/-- Hay un proceso de gestación que es decadencia (el Typos) y otro que es diseminación. -/
theorem hay_decadencia :
    (∃ g, NiceaE3.Pg g ∧ NiceaE3.tg g = Tg.decadencia) ∧ (∃ g, NiceaE3.Pg g ∧ NiceaE3.tg g = Tg.diseminacion) :=
  ⟨⟨1, show (1 : Fin 3).val < 2 by decide, rfl⟩, ⟨0, show (0 : Fin 3).val < 2 by decide, rfl⟩⟩

/-- La decadencia no es rutina (L8): es un proceso de gestación, no mera repetición. -/
theorem decadencia_no_rutina : ∀ g, NiceaE3.tg g = Tg.decadencia → NiceaE3.Pg g → ¬ NiceaE3.Rut g :=
  fun g _ hp hr => NiceaE3_ley.L8 g ⟨hp, hr⟩

/-- La ley de E3 admite la decadencia: el modelo con decadencia cumple L1–L20. -/
theorem ley_con_decadencia : Ley NiceaE3 ∧ ∃ g, NiceaE3.Pg g ∧ NiceaE3.tg g = Tg.decadencia :=
  ⟨NiceaE3_ley, hay_decadencia.1⟩

/-! ### E3 no queda determinada por E2 (U7, lado de E3) -/

/-- Variante de E3 sobre el MISMO E2 del caso (`NiceaE2`) en la que r2 y r3 no son incompatibles: se toman `dc` e `ip` de B. -/
abbrev NiceaE3b : Mp := { NiceaE3 with dc := B.dc, ip := B.ip }

theorem NiceaE3b_ley : Ley NiceaE3b :=
  { NiceaE3_ley with L15 := B_ley.L15 }

/-- Dos modelos de E3 con ley sobre el mismo `NiceaE2` (mismos escritos, mismos sentidos, mismos grados) difieren en E3:
    en uno r2 y r3 son incompatibles y en el otro no. E2 no determina E3. -/
theorem E3_no_determinada_por_E2 :
    NiceaE3.xM = NiceaE3b.xM ∧ Ley NiceaE3 ∧ Ley NiceaE3b ∧ NiceaE3.Inc 1 2 ∧ ¬ NiceaE3b.Inc 1 2 := by
  refine ⟨rfl, NiceaE3_ley, NiceaE3b_ley, NiceaE3_inc, ?_⟩
  rintro ⟨e, e', h1, h2, h3⟩
  change (1 : Fin 6).val = 3 ∧ _ ∨ _ at h1
  change _ at h2
  simp at h1 h2

/-! ### Choque horizonte–fuente y revisión de credibilidad (caso Becker, ahora sobre Nicea) -/

/-- Calcedonia leída como testimonio directo de continuidad con Nicea (α₂, n = 0): la afirmación está respaldada
    (cr = 2 ⪰ cd_c) y el horizonte v₀ la da por imposible. -/
theorem choque_calcedonia : NiceaE3.Ch 0 0 2 :=
  ⟨show (0 : Fin 2).val = 0 ∧ ((2 : Fin 3).val = 1 ∨ (2 : Fin 3).val = 2) by decide,
   Or.inr (show (1 : Fin 3).val < (2 : Fin 3).val by decide)⟩

/-- La revisión de credibilidad (Calcedonia leída como indicio indirecto de lo que querían sus autores, n = 1)
    disuelve el choque. -/
theorem revision_disuelve : ¬ NiceaE3.Ch 0 1 2 := by
  rintro ⟨_, h⟩
  rcases h with h | h
  · exact absurd (congrArg Fin.val h) (by decide)
  · exact absurd h (by decide)

/-- La revisión no es arbitraria: cambia el uso de la fuente (directo → indirecto) y L13 exige una cuestión
    intermedia que la motive. -/
theorem revision_motivada :
    NiceaE3.Uc3 0 2 = Uc.directo ∧ NiceaE3.Uc3 1 2 = Uc.indirecto ∧ NiceaE3.cr 1 2 ≠ NiceaE3.cr 0 2 ∧
    ∃ q, NiceaE3.Qint q ∧ NiceaE3.Sbr q (NiceaE3.sa 2) :=
  ⟨B_uc.1, B_uc.2, by decide, cr_cambia_motivado NiceaE3 NiceaE3_ley 0 2 (by decide)⟩

/-- α₁ (el Símbolo presenta la fórmula como expresión de la fe recibida): su credibilidad es estable y el horizonte
    v₀ la rechaza en toda revisión. Es un choque de horizonte, no de fuente: revisar credibilidades no lo disuelve. -/
theorem choque_persistente : ∀ n, NiceaE3.Ch 0 n 1 := by
  intro n
  refine ⟨show (0 : Fin 2).val = 0 ∧ ((1 : Fin 3).val = 1 ∨ (1 : Fin 3).val = 2) by decide, Or.inr ?_⟩
  show (1 : Fin 3).val < (crN n 1).val
  unfold crN
  simp

/-- El horizonte v₁ no tiene choques con ninguna afirmación en ningún momento (diferencia de horizonte sin choque). -/
theorem horizonte_continuidad_sin_choque : ∀ n a, ¬ NiceaE3.Ch 1 n a := by
  rintro n a ⟨⟨h, _⟩, _⟩
  exact absurd h (by decide)

/-- Dos tipos de choque: uno se resuelve por revisión (fuente), otro no (horizonte). -/
theorem dos_tipos_de_choque :
    (NiceaE3.Ch 0 0 2 ∧ ¬ NiceaE3.Ch 0 1 2) ∧ (∀ n, NiceaE3.Ch 0 n 1) :=
  ⟨⟨choque_calcedonia, revision_disuelve⟩, choque_persistente⟩

/-! ### Negativos de E3 sobre Nicea: cada variante cambia UN campo y viola UNA cláusula -/

/-- L15: la incompatibilidad r2–r3 sin ningún factor perturbador viola la ley. -/
theorem neg_L15 : ¬ Ley { NiceaE3 with ip := fun _ _ => False } := by
  intro L
  rcases L.L15 1 2 NiceaE3_inc with ⟨_, h⟩ | ⟨_, h⟩ <;> exact h

/-- L8: un proceso que es a la vez gestación y rutina viola la ley. -/
theorem neg_L8 : ¬ Ley { NiceaE3 with Rut := fun g => g.val = 1 } := by
  intro L
  exact L.L8 1 ⟨show (1 : Fin 3).val < 2 by decide, rfl⟩

/-- L13: una revisión de credibilidad sin cuestión que la motive viola la ley. -/
theorem neg_L13 : ¬ Ley { NiceaE3 with Sbr := fun _ _ => False } := by
  intro L
  obtain ⟨_, _, _, _, q, _, _, hs⟩ := L.L13 0 2 (Or.inl (by decide))
  exact hs

/-- L3: un autor que no es el que E2 reconstruye viola la ley. -/
theorem neg_L3 : ¬ Ley { NiceaE3 with au := fun _ => 2 } := by
  intro L
  have h := (L.L3.2 1).1
  exact absurd h (by decide)

/-- L10: una narración canónica que no es la del tipo correspondiente viola la ley. -/
theorem neg_L10 : ¬ Ley { NiceaE3 with Cp := fun _ => 0 } := by
  intro L
  exact absurd L.L10.2.1 (by decide)

/-- L20: una selección sin juicio de valor que la guíe viola la ley. -/
theorem neg_L20 : ¬ Ley { NiceaE3 with vl := fun _ _ => False } := by
  intro L
  obtain ⟨j, h, _⟩ := L.L20 0 0 (Or.inl rfl)
  exact h

/-- L18: la semejanza afirmada como necesaria en una serie no impedida viola la ley. -/
theorem neg_L18 : ¬ Ley { NiceaE3 with Imp := fun _ _ => False } := by
  intro L
  obtain ⟨e, h⟩ := L.L18.2 3 rfl 1 ⟨0, by decide, rfl⟩
  exact h

/-- L16: una narración sin lugar ni tiempo viola la ley. -/
theorem neg_L16 : ¬ Ley { NiceaE3 with ref3 := fun _ _ => False } := by
  intro L
  obtain ⟨⟨l, h⟩, _⟩ := L.L16 0
  exact h

/-- Libro de cuentas de los negativos. -/
theorem negativos :
    ¬ Ley { NiceaE3 with ip := fun _ _ => False } ∧ ¬ Ley { NiceaE3 with Rut := fun g => g.val = 1 } ∧
    ¬ Ley { NiceaE3 with Sbr := fun _ _ => False } ∧ ¬ Ley { NiceaE3 with au := fun _ => 2 } ∧
    ¬ Ley { NiceaE3 with Cp := fun _ => 0 } ∧ ¬ Ley { NiceaE3 with vl := fun _ _ => False } ∧
    ¬ Ley { NiceaE3 with Imp := fun _ _ => False } ∧ ¬ Ley { NiceaE3 with ref3 := fun _ _ => False } :=
  ⟨neg_L15, neg_L8, neg_L13, neg_L3, neg_L10, neg_L20, neg_L18, neg_L16⟩

end Hist
end E3

#print axioms E3.Hist.dos_tipos_de_choque
#print axioms E3.Hist.negativos
#print axioms E3.NiceaE3_ley
#print axioms E3.Hist.E3_no_determinada_por_E2
