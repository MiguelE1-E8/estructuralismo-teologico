import E2
/-
  E3 · Historia — verificación en Lean 4 (sin Mathlib, sin sorry).
  Estructura: Mp (modelo potencial), Ley (L1–L20), modelo actual Bultmann/sinópticos.
  Entrega 1 de la Fase 10: afirmaciones y credibilidad (As, Cd, cr), hechos (ev3, Hh, L14), L13 ampliada,
  perspectivismo (Vt, sel, Inc, L15–L17).
  Entrega 2: horizontes (Hz, ho, vd, cd_c, Ve, Ch; parámetros, sin cláusula) y estructuras heurísticas
  (qd, qi, Ti, ap, sus, Pj, tpj, Jh, vl, gj; L18–L20). Los símbolos τ→tf (por E1) y ψ→κ (por E1) ya están renombrados.
  Corrección de L3 (ciclo completo, 18-oct): `a` lleva autor, lugar y momento (X2 := Ag × (Lg × Iv)); `ref` es solo el objeto
  (X3 := Ob, campo nuevo de Mp). L3: au f = (a (fw f)).1 y ub f = (a (fw f)).2. `ref` deja de estar ligado a `ub`.
  Citas de Lonergan (*Método en teología*, Sígueme, Salamanca 1988, cap. 8 «Historia» y cap. 9 «Historia e historiadores»;
  [L p. N] = página impresa de esa edición, leída de la capa de texto del PDF; las capturas teológicas r1–r3 y Cp son del cap. 5
  y no se cita página porque ese capítulo no estaba disponible):
    L2 (gr3): la historia opera en los cuatro niveles «con un interés principal por juzgar» [L p. 179].
    L3 (interfaz con E2): la historia parte «de los datos obtenidos por la investigación» y presupone interpretación [L p. 178];
       a, ref y el contexto son de E2 (Lonergan, cap. 7, citado en E2Nicea).
    L4–L5 (Pa ⊆ Pf, pista correcta): «si durante un tiempo largo se permanece en la pista correcta» las cuestiones ulteriores
       provienen de datos y no de conjeturas [L pp. 180-181].
    L6 (Pend3, Jz3): la corriente de cuestiones ulteriores «disminuye gradualmente, y finalmente se seca»; «si de hecho ya no hay
       cuestiones ulteriores pertinentes, entonces, de hecho, el juicio que se haga será verdadero» [L p. 184].
    L7 (Uc3): los documentos se usan como elementos de prueba de «sus intenciones […]; este es un procedimiento indirecto basado
       en su narración» [L p. 182]; revelan «directa o indirectamente» [L p. 201].
    L8 (Pg, Rut): «irse gestando» es «la exclusión de la mera repetición de una rutina», con diseminación, desarrollo, decadencia
       y desintegración [L p. 172].
    L9 (Ds3): las investigaciones «llegan a su término» cuando se alcanza «un conjunto de intelecciones que dan exactamente en el
       clavo» [L p. 184].
    L11 (Hf, crt): «la historia crítica de segundo grado»; plantear cuestiones presupone conocimiento histórico previo [L pp. 186-187].
    L12 (xt monótona): las nuevas fuentes y los sucesos ulteriores no invalidan «el trabajo anterior hecho competentemente» [L p. 185].
    L13 (Uc, cr): el conocimiento avanza «como en espiral»; con él «una nueva luz se proyecta sobre el carácter de los documentos»
       [L p. 201]; el proceso ocurre «dos veces» [L p. 182].
    L14 (ev3): los hechos aparecen «cuando la corriente de cuestiones ulteriores comienza a agotarse» [L p. 196]; son «concretos»,
       «precisos» e «innegables»; «los datos son una cosa y los hechos son otra» [L pp. 195-196].
    L15 (ip): la historia crítica «puede ser impedida» por puntos de vista erróneos, juicios de valor engañosos o un horizonte
       inadecuado [L p. 188]; el perspectivismo no da cuenta de las incompatibilidades [L p. 217, n. 91].
    L16 (ref3): los descubrimientos del historiador «se refieren a personas, lugares y tiempos particulares» [L p. 173].
    L17 (qn, sel): el perspectivismo resulta de tres factores: el historiador es limitado, hace una selección y sus diferencias de
       horizonte [L p. 211]; las narraciones deben ser compatibles y formar «una sola visión» [L p. 212].
    L18 (qd, qi): sin pruebas de diversidad, afirmar semejanza proyecta «el clima de opinión» del historiador [L p. 218].
    L19 (ap, sus): el tipo-ideal «pone al descubierto diferencias precisas» y «suscita interrogantes» [L pp. 220-221].
    L20 (vl, gj): los juicios de valor son «el medio que [el historiador] utiliza para hacer de su obra una selección de cosas dignas
       de conocerse» [L p. 226]; su valoración pertenece a la dialéctica y los fundamentos [L pp. 217, 226].
    Horizontes (sin cláusula): el caso de Becker y la regla de Bernheim; el historiador vive «en un mundo mediado por la
       significación» con «opciones fundamentales» [L pp. 214-215]. Caso Bultmann: «se interesó por exponer ese proceso como un todo»
       y sus elementos de prueba «no presuponían la fe en la verdad de las afirmaciones evangélicas» [L p. 179].
  Componentes del Doc que el Mp de Lean NO incluye (decisión 19-oct): ef (Hc ⇀ éxito/revés/influencia), ins (Hc ∪ Mv → 𝒫(Cx)),
  Prd (períodos ⊆ 𝒫(Cx)) y Sit (situaciones concretas). Lonergan los describe (cap. 8, pp. 173-178: movimientos, contextos,
  períodos), pero ninguna cláusula L1–L20 los usa, y la comprobación de la unidad dinámica (CicloModelo, CicloPaso, CicloF2,
  CicloF4) sólo toca U, Q, Qint, Q2, X1, Vt, xM, Ev e Inc. Añadirlos sería adorno formal sin ley que los ate y cambiaría el Mp
  del que dependen CicloNicea…CicloCaso. Se añadirían si una ley (p. ej. sobre períodos) o el contraste de L10 con un caso real
  lo exigiera. (`Pr` de Lean es el tipo de procesos γ, no los períodos `Prd` del Doc.)
  La interfaz con E2 usa las estructuras reales de E2.lean (E2.Mp, MpF, MpD, LeyFuerte, LeyDebil, Grado).
-/
namespace E3

/-! ## Tipos enumerados -/
inductive Tipo | mc | mi | md deriving DecidableEq
inductive Niv3 | hh | hp | hpp deriving DecidableEq      -- h, h′, h″
inductive Forma | presuposicion | foco_de_interes | no_margen deriving DecidableEq
abbrev Grado := E2.Grado   -- importado de E2
inductive Nv | experimentar | entender | juzgar | decidir deriving DecidableEq
inductive Uc | directo | indirecto deriving DecidableEq
inductive Tg | origen | diseminacion | desarrollo | decadencia | desintegracion deriving DecidableEq
inductive Td | evidencia | perspectiva | seleccion | exclusion | estructura deriving DecidableEq
inductive Pd | confiable | limitado | a_revisar deriving DecidableEq
inductive Tpe | pvx | jv | vm | oe | otro deriving DecidableEq
inductive Tpj | inconsciente | egoismo_individual | egoismo_colectivo | sentido_comun deriving DecidableEq
inductive Ajuste | ajusta | difiere deriving DecidableEq

/-- Cadena (orden estricto total). El carácter "abierto" no se formaliza. -/
def IsChain {α : Type} (lt : α → α → Prop) : Prop :=
  (∀ a, ¬ lt a a) ∧ (∀ a b c, lt a b → lt b c → lt a c) ∧ (∀ a b, a ≠ b → lt a b ∨ lt b a)

def IsStrictPO {α : Type} (lt : α → α → Prop) : Prop :=
  (∀ a, ¬ lt a a) ∧ (∀ a b c, lt a b → lt b c → lt a c)

/-! ## Modelo potencial Mp(E3): solo tipos -/
structure Mp where
  -- A. Bloques
  Lg : Type
  Ag : Type
  Iv : Type
  Mv : Type
  Cx : Type
  Vg : Type
  Gr : Type
  Am : Type
  Nz : Type
  Ac : Type
  As : Type
  Cd : Type
  Vt : Type
  Eh : Type
  Hz : Type
  Ti : Type
  Jh : Type
  tp : Mv → Tipo                      -- Φc, Φi, Φd
  Fc : Mv → Prop                      -- foco cristiano
  ltAm : Am → Am → Prop
  ltVg : Vg → Vg → Prop
  ltg : Gr → Gr → Prop
  gmin : Gr
  gpral : Gr
  tf : Niv3 → Forma × Gr
  cob : Vg → Tipo → Nat
  cobMin : Nat
  -- B. Interfaz
  -- tipos de E2 (X2 := Ag × (Lg × Iv): quién, dónde, cuándo; X3 := Ob, el objeto que el autor tenía en mente)
  W : Type
  X1 : Type
  H : Type
  S : Type
  R : Type
  Q2 : Type
  Ob : Type
  xM : E2.Mp W X1 (Ag × (Lg × Iv)) Ob H S R Q2   -- x ∈ M(E2): parte de Mp(E2); la ley va en L3
  Dat : Type
  Fu : Type
  fw : Fu → W                         -- Fu3 ↔ W2′
  U : Type                            -- universo de datos de E0
  inW : W → U → Prop                  -- u ∈ w (un escrito es un conjunto de datos de U)
  Ev : W → U → Prop                   -- Ev(w): evidencia de E1 para w (E2, 7.11); su relación con Em/Ea/Er queda primitiva (pendiente (h) de E2)
  datU : Dat → U
  Us3 : Fu → Prop
  au : Fu → Ag
  ub : Fu → Lg × Iv
  src : Dat → Fu → Prop
  -- C. Proceso
  Q : Type
  Ih : Type
  Cj : Type
  Se : Type
  Qint : Q → Prop
  ent : Q → Dat → Option Ih
  cjf : Ih → Option Cj
  nq : Ih → Option Q
  Fd : Dat → Q → Prop
  hr : Q → Dat → Prop
  Co : Cj → Dat → Prop
  sLen : Se → Nat
  sq : Se → Nat → Q
  sc : Se → Nat → Cj
  si : Se → Nat → Ih
  term : Se → Prop
  isGst : Se → Prop
  Ps : Type
  obLe : Ps → Ps → Prop               -- ≼ob
  xt : Se → Nat → Ps
  Pt3 : Q → List Q
  Pend3 : Q → List Q
  Jz3 : Q → Grado
  Uc3 : Nat → Fu → Uc
  fund : Nat → Fu → Q → Prop
  Sbr : Q → Fu → Prop
  gr3 : Nv → Gr
  -- C′. Afirmaciones de las fuentes, credibilidad y hechos (Fase 1)
  ltCd : Cd → Cd → Prop
  sa : As → Fu
  cr : Nat → As → Cd
  Hc : Ag × Ac × Lg × Iv → Prop
  ev3 : Q → Option (Ag × Ac × Lg × Iv)
  -- D. Salida
  Pr : Type
  Pg : Pr → Prop
  Rut : Pr → Prop
  tg : Pr → Tg
  Nr : Type
  Th : Type
  ltTh : Th → Th → Prop              -- ≻
  nv : Th → Nz
  ltNz : Nz → Nz → Prop
  ref3 : Nr → (Ag ⊕ Lg ⊕ Iv ⊕ Mv) → Prop
  Ds3 : Ih → Prop
  td : Ih → Td
  r1 : Nr
  r2 : Nr
  r3 : Nr
  Cp : Tipo → Nr
  -- E. Segundo grado y ceteris paribus
  Hf : Type
  niv : Hf → Nat
  crt : Hf → Hf → Prop
  Af : Nr → Prop
  ud : {b : Hf // niv b = 1} → {n : Nr // Af n} → Pd
  pr : Q → Hf → Prop
  Pe : Type
  Imp : Pe → Se → Prop
  -- F. Perspectivismo (Fase 2)
  pvi : Vt → Ps
  sel : Vt → Q → Prop
  vn : Nr → Vt
  qn : Nr → Q → Prop
  dc : Nr → Eh → Prop
  ctr : Eh → Eh → Prop
  ip : Pe → Nr → Prop
  -- G. Horizontes (Fase 3): parámetros, sin cláusula
  ho : Vt → Hz
  vd : Hz → As → Prop
  cd_c : Cd
  -- H. Estructuras heurísticas (Fase 4); Qh := Q
  qd : Q → Prop
  qi : Q → Prop
  ap : Ti → Cx → Option Ajuste
  sus : Ti → Cx → Option (Q → Prop)
  tpe : Pe → Tpe
  Pj : Pe → Prop
  tpj : Pe → Tpj                      -- en el documento: tpj: Pj → …; aquí total sobre Pe, solo importa en Pj
  vl : Vt → Jh → Prop
  gj : Jh → Q → Prop
  -- tipos de componentes (condiciones de Mp)
  cadena_Gr : IsChain ltg
  cadena_Am : IsChain ltAm
  cadena_Vg : IsChain ltVg
  cadena_Nz : IsChain ltNz
  orden_Th : IsStrictPO ltTh
  gmin_lt : ltg gmin gpral
  cadena_Cd : IsChain ltCd
  ev3_Hc : ∀ q h, ev3 q = some h → Hc h
  ctr_sim : ∀ a b, ctr a b → ctr b a
  ctr_irr : ∀ a, ¬ ctr a a

namespace Mp
variable (M : Mp)

/-- Pf(q) := {d | (q,d) ∈ dom(ent)} -/
def Pf (q : M.Q) (d : M.Dat) : Prop := (M.ent q d).isSome = true
/-- Pa(q) := {d ∈ Pf(q) | (d,q) ∈ Fd} -/
def Pa (q : M.Q) (d : M.Dat) : Prop := M.Pf q d ∧ M.Fd d q
/-- pista correcta (L5) -/
def pc (s : M.Se) : Prop :=
  ∀ n, n + 1 < M.sLen s → ∃ d, M.Pf (M.sq s (n+1)) d ∧ M.Co (M.sc s n) d
def Hist3 := {b : M.Hf // M.niv b = 1}
def R3 (n : M.Nr) : Prop := n = M.r1 ∨ n = M.r2 ∨ n = M.r3
/-- Hh := {ev3(q) | q ∈ dom(ev3), Jz3(q) = cierto} -/
def Hh (h : M.Ag × M.Ac × M.Lg × M.Iv) : Prop := ∃ q, M.ev3 q = some h ∧ M.Jz3 q = .cierto
/-- Inc: narraciones incompatibles (algún par de enunciados en contradicción). -/
def Inc (n n' : M.Nr) : Prop := ∃ e e', M.dc n e ∧ M.dc n' e' ∧ M.ctr e e'
/-- Ip: narraciones afectadas por algún factor perturbador. -/
def Ip (n : M.Nr) : Prop := ∃ e, M.ip e n
/-- Ve(v): afirmaciones que el horizonte de v da por imposibles. -/
def Ve (v : M.Vt) (a : M.As) : Prop := M.vd (M.ho v) a
/-- Ch(v,n): afirmaciones respaldadas por la pasada fte (cr_n ⪰ cd_c) que el horizonte rechaza (caso Becker). -/
def Ch (v : M.Vt) (n : Nat) (a : M.As) : Prop :=
  M.Ve v a ∧ (M.cr n a = M.cd_c ∨ M.ltCd M.cd_c (M.cr n a))
end Mp

/-- La ley de E3: L1–L20 (L5 es la definición `Mp.pc`; se verifica en el modelo con `B_pc`). -/
structure Ley (M : Mp) : Prop where
  L1 : M.tf .hh = (.presuposicion, M.gpral) ∧ M.tf .hp = (.foco_de_interes, M.gpral)
        ∧ M.tf .hpp = (.no_margen, M.gmin)
  L2 : M.gr3 .juzgar = M.gpral ∧ ∀ n, n ≠ Nv.juzgar → M.ltg (M.gr3 n) M.gpral
  L3 : ((∃ xf : E2.MpF M.W M.X1 (M.Ag × (M.Lg × M.Iv)) M.Ob M.H M.S M.R M.Q2, xf.toMp = M.xM ∧ E2.LeyFuerte xf)
         ∨ (∃ xd : E2.MpD M.W M.X1 (M.Ag × (M.Lg × M.Iv)) M.Ob M.H M.S M.R M.Q2, xd.toMp = M.xM ∧ E2.LeyDebil xd))
        ∧ (∀ f, M.au f = (M.xM.a (M.fw f)).1 ∧ M.ub f = (M.xM.a (M.fw f)).2)
  L3b : ∀ d, ∃ f, M.inW (M.fw f) (M.datU d) ∨ M.Ev (M.fw f) (M.datU d)   -- Dat3 ⊆ ⋃(w ∪ Ev(w))
  L4 : (∀ q d, M.Pa q d → M.Pf q d) ∧ (∀ q d, M.Pf q d → M.hr q d)
  L6 : ∀ q, (∀ p, p ∈ M.Pend3 q → p ∈ M.Pt3 q) ∧ (M.Jz3 q = .cierto ↔ M.Pend3 q = [])
  L7 : ∀ n f q, M.Uc3 n f = .indirecto → M.fund n f q → M.Qint q
  L8 : ∀ g, ¬ (M.Pg g ∧ M.Rut g)
  L9 : ∀ d, M.Ds3 d → ∃ s, M.term s ∧ 0 < M.sLen s ∧ d = M.si s (M.sLen s - 1)
  L10 : M.Cp .mi = M.r1 ∧ M.Cp .mc = M.r2 ∧ M.Cp .md = M.r3
        ∧ (∀ n, M.R3 n → ∃ t, M.Cp t = n)
        ∧ (∀ t, M.R3 (M.Cp t))
        ∧ (∀ n, M.R3 n → ∃ m, M.Fc m ∧ M.ref3 n (.inr (.inr (.inr m))))
        ∧ ∃ g, ∀ t, M.cobMin ≤ M.cob g t
  L11 : (∀ a b, M.crt a b → M.niv b < M.niv a) ∧ (∀ q, ∃ b, M.pr q b)
  L12 : ∀ s, M.pc s → (∀ e, ¬ M.Imp e s) → ∀ n m, n ≤ m → M.obLe (M.xt s n) (M.xt s m)
  L13 : ∀ n f, (M.Uc3 (n+1) f ≠ M.Uc3 n f ∨ ∃ a, M.sa a = f ∧ M.cr (n+1) a ≠ M.cr n a) →
        ∃ s, M.isGst s ∧ ∃ k, k < M.sLen s ∧ ∃ q, M.nq (M.si s k) = some q ∧ M.Qint q ∧ M.Sbr q f
  L14 : ∀ q h, M.ev3 q = some h → M.Jz3 q = .cierto →
        (∃ d, M.Pa q d) ∧ ∃ s, M.term s ∧ ∃ k, k < M.sLen s ∧ M.sq s k = q
  L15 : ∀ n n', M.Inc n n' → M.Ip n ∨ M.Ip n'
  L16 : ∀ n, (∃ l, M.ref3 n (.inr (.inl l))) ∧ (∃ i, M.ref3 n (.inr (.inr (.inl i))))
  L17 : ∀ n q, M.qn n q → M.sel (M.vn n) q ∧ ∃ d, M.Pa q d
  L18 : (∀ q, M.qd q → ∃ d, M.Pa q d) ∧
        (∀ q, M.qi q → ∀ s, (∃ k, k < M.sLen s ∧ M.sq s k = q) → ∃ e, M.Imp e s)
  L19 : ∀ T c, ((∃ S, M.sus T c = some S) ↔ M.ap T c = some Ajuste.difiere) ∧
        (∀ S, M.sus T c = some S → ∃ q, S q)
  L20 : ∀ v q, M.sel v q → ∃ j, M.vl v j ∧ M.gj j q

/-! ## Consecuencias generales (sobre cualquier modelo) -/
theorem Pa_sub_Pf (M : Mp) : ∀ q d, M.Pa q d → M.Pf q d := fun _ _ h => h.1
theorem Im_Cp (M : Mp) (L : Ley M) : ∀ n, M.R3 n ↔ ∃ t, M.Cp t = n := by
  intro n; constructor
  · exact L.L10.2.2.2.1 n
  · rintro ⟨t, rfl⟩; exact L.L10.2.2.2.2.1 t
theorem Jz_cierto_sii (M : Mp) (L : Ley M) (q : M.Q) : M.Jz3 q = .cierto ↔ M.Pend3 q = [] :=
  (L.L6 q).2
/-- Un juicio pendiente impide la certeza. -/
theorem pend_no_cierto (M : Mp) (L : Ley M) (q p : M.Q) (h : p ∈ M.Pend3 q) :
    M.Jz3 q ≠ .cierto := by
  intro hc
  have := ((L.L6 q).2.1 hc)
  rw [this] at h; cases h
theorem uc_cambia_motivado (M : Mp) (L : Ley M) (n : Nat) (f : M.Fu)
    (h : M.Uc3 (n+1) f ≠ M.Uc3 n f) : ∃ q, M.Qint q ∧ M.Sbr q f := by
  obtain ⟨_, _, _, _, q, _, hq, hs⟩ := L.L13 n f (Or.inl h)
  exact ⟨q, hq, hs⟩
/-- La revisión de la credibilidad de una afirmación también es motivada (L13 ampliada). -/
theorem cr_cambia_motivado (M : Mp) (L : Ley M) (n : Nat) (a : M.As)
    (h : M.cr (n+1) a ≠ M.cr n a) : ∃ q, M.Qint q ∧ M.Sbr q (M.sa a) := by
  obtain ⟨_, _, _, _, q, _, hq, hs⟩ := L.L13 n (M.sa a) (Or.inr ⟨a, rfl, h⟩)
  exact ⟨q, hq, hs⟩

/-- Un hecho histórico es un evento conocido: su cuestión no tiene pendientes. -/
theorem Hh_sin_pendientes (M : Mp) (L : Ley M) (h : M.Ag × M.Ac × M.Lg × M.Iv)
    (hh : M.Hh h) : ∃ q, M.Pend3 q = [] := by
  obtain ⟨q, _, hj⟩ := hh
  exact ⟨q, (L.L6 q).2.1 hj⟩
/-- Un hecho está fundado (L14) y es un evento de la historia básica. -/
theorem Hh_fundado (M : Mp) (L : Ley M) (h : M.Ag × M.Ac × M.Lg × M.Iv)
    (hh : M.Hh h) : M.Hc h ∧ ∃ q d, M.Pa q d := by
  obtain ⟨q, he, hj⟩ := hh
  exact ⟨M.ev3_Hc q h he, q, (L.L14 q h he hj).1⟩

/-- El perspectivismo por sí solo no produce incompatibilidad (L15). -/
theorem sin_impedimento_no_inc (M : Mp) (L : Ley M) (n n' : M.Nr)
    (h1 : ¬ M.Ip n) (h2 : ¬ M.Ip n') : ¬ M.Inc n n' :=
  fun h => (L.L15 n n' h).elim h1 h2
/-- Una narración responde solo cuestiones que su punto de vista selecciona, y con evidencia (L17). -/
theorem narracion_justificada (M : Mp) (L : Ley M) (n : M.Nr) (q : M.Q) (h : M.qn n q) :
    M.sel (M.vn n) q ∧ ∃ d, M.Pa q d := L.L17 n q h

/-- Diversidad afirmada entre pasado y presente exige prueba (L18 i). -/
theorem diversidad_probada (M : Mp) (L : Ley M) (q : M.Q) (h : M.qd q) : ∃ d, M.Pa q d :=
  L.L18.1 q h
/-- La semejanza afirmada como necesaria impide toda serie que contenga la cuestión (L18 ii). -/
theorem semejanza_necesaria_impide (M : Mp) (L : Ley M) (q : M.Q) (h : M.qi q) (s : M.Se)
    (hs : ∃ k, k < M.sLen s ∧ M.sq s k = q) : ∃ e, M.Imp e s := L.L18.2 q h s hs
/-- Un tipo-ideal que difiere de un contexto suscita al menos una cuestión (L19). -/
theorem tipo_suscita (M : Mp) (L : Ley M) (T : M.Ti) (c : M.Cx)
    (h : M.ap T c = some Ajuste.difiere) : ∃ S, M.sus T c = some S ∧ ∃ q, S q := by
  obtain ⟨S, hS⟩ := ((L.L19 T c).1).2 h
  exact ⟨S, hS, (L.L19 T c).2 S hS⟩
/-- Un juicio de valor guía toda cuestión seleccionada, pero no es prueba (Jh ≠ Dat) (L20). -/
theorem seleccion_guiada (M : Mp) (L : Ley M) (v : M.Vt) (q : M.Q) (h : M.sel v q) :
    ∃ j, M.vl v j ∧ M.gj j q := L.L20 v q h
/-- El horizonte no cambia la credibilidad: Ch sólo lee cr_n. -/
theorem Ch_lee_cr (M : Mp) (v : M.Vt) (n : Nat) (a : M.As) (h : M.Ch v n a) : M.Ve v a := h.1

/-! ## Modelo actual: Bultmann y los sinópticos (esquemático, valores estipulados) -/
section Bultmann
-- Índices: Q: q₁..q₄ = 0..3 ; D: d₁..d₄ = 0..3 ; F: f_Mc,f_Mt,f_Lc = 0,1,2
-- Ih: ι₁ι₂ι₃ = 0,1,2 ; Cj: c₁,c₂ = 0,1 ; Hf: b₀,n₂,n₃ = 0,1,2 ; Pr: γ₁,γ₂,ρ = 0,1,2
-- Nr: r1,r2,r3,ν,ν′,ν″ = 0..5 ; Mv: tr, ig, teo, (otro) = 0..3
-- Se: s = 0 (serie terminada), s″ = 1 (serie (q₄), sin terminar, impedida por pe₁)
-- As: α₁,α₂,α₃ = 0,1,2 ; Cd: cd₁,cd₂,cd₃ = 0,1,2 ; Vt: v₁,v₂ = 0,1 ; Eh: e₁..e₄ = 0..3
-- Ag: com = 0, red = 1 ; Ac: transmitir = 0, componer = 1 ; Lg: ℓ = 0 ; Iv: i₁ = 0, i₂ = 1

@[reducible] def Lt {n : Nat} (a b : Fin n) : Prop := a.val < b.val

/-- Mp(E2) concreto del caso: tres escritos, sin pendientes, Jz = cierto. -/
abbrev X : E2.Mp (Fin 3) (Fin 3) (Fin 3 × (Fin 3 × Fin 3)) Unit Unit Unit Unit Unit :=
  { m := fun w => w, a := fun w => (w, (w, w)), ref := fun _ => ()
    g := fun _ _ _ _ => (), sg := fun _ => ()
    Pt := fun _ => [], Pend := fun _ _ => [], Jz := fun _ _ => E2.Grado.cierto
    O2 := fun _ _ _ => ()
    pend_sub := fun _ _ q hq => by simp at hq
    jz_cierto := fun _ _ => by simp }

abbrev ucB (n : Nat) (f : Fin 3) : Uc := if f = 2 ∧ n = 0 then .directo else .indirecto

abbrev pendB (q : Fin 4) : List (Fin 4) := if q = 0 then [3] else []

abbrev B : Mp where
  Lg := Fin 3
  Ag := Fin 3
  Iv := Fin 3
  Mv := Fin 4
  Cx := Fin 2
  Ac := Fin 2
  As := Fin 3
  Cd := Fin 3
  Vt := Fin 2
  Eh := Fin 4
  Hz := Fin 2
  Ti := Unit
  Jh := Fin 2
  Vg := Fin 2
  Gr := Fin 2
  Am := Fin 2
  Nz := Fin 2
  tp := fun m => if m.val = 0 then .mc else if m.val = 1 then .mi else .md
  Fc := fun m => m.val < 3
  ltAm := Lt
  ltVg := Lt
  ltg := Lt
  gmin := 0
  gpral := 1
  tf := fun
    | .hh => (.presuposicion, 1)
    | .hp => (.foco_de_interes, 1)
    | .hpp => (.no_margen, 0)
  cob := fun g _ => if g = 1 then 5 else 0
  cobMin := 3
  W := Fin 3
  X1 := Fin 3
  H := Unit
  S := Unit
  R := Unit
  Q2 := Unit
  Ob := Unit
  xM := X
  Dat := Fin 4
  Fu := Fin 3
  fw := fun f => f
  U := Fin 4
  inW := fun w u => u.val = w.val
  Ev := fun _ u => u.val = 3
  datU := fun d => d
  Us3 := fun _ => True
  au := fun f => f
  ub := fun f => (f, f)
  src := fun d f => (d = 1 ∧ f = 0) ∨ (d = 2 ∧ f = 2)
  Q := Fin 4
  Ih := Fin 3
  Cj := Fin 2
  Se := Fin 2
  Qint := fun _ => True
  ent := fun q d =>
    if q = 0 ∧ d = 0 then some 0 else if q = 1 ∧ d = 1 then some 1
    else if q = 2 ∧ d = 2 then some 2 else none
  cjf := fun i => if i = 0 then some 0 else if i = 1 then some 1 else none
  nq := fun i => if i = 0 then some 1 else if i = 1 then some 2 else none
  Fd := fun d q => (d = 0 ∧ q = 0) ∨ (d = 2 ∧ q = 2)
  hr := fun _ d => d ≠ 3
  Co := fun c d => (c = 0 ∧ d = 1) ∨ (c = 1 ∧ d = 2)
  sLen := fun s => if s = 0 then 3 else 1
  sq := fun s n => if s = 0 then (if n = 0 then 0 else if n = 1 then 1 else 2) else 3
  sc := fun _ n => if n = 0 then 0 else 1
  si := fun _ n => if n = 0 then 0 else if n = 1 then 1 else 2
  term := fun s => s = 0
  isGst := fun s => s = 0
  Ps := Nat
  obLe := fun a b => a ≤ b
  xt := fun _ n => if n ≤ 2 then n else 2
  Pt3 := fun q => if q = 0 then [1, 2, 3] else []
  Pend3 := pendB
  Jz3 := fun q => if q = 0 then .altamente_probable else .cierto
  Uc3 := ucB
  fund := fun n f q => n = 1 ∧ f = 2 ∧ q = 2
  Sbr := fun q f => q = 1 ∧ f = 2
  gr3 := fun | .juzgar => 1 | _ => 0
  Pr := Fin 3
  Pg := fun g => g.val < 2
  Rut := fun g => g.val = 2
  tg := fun g => if g.val = 0 then .diseminacion else .desarrollo
  Nr := Fin 6
  Th := Fin 2
  ltTh := fun a b => b.val < a.val
  nv := fun t => t
  ltNz := Lt
  ref3 := fun n e => match e with
    | .inr (.inr (.inr m)) => m.val = n.val ∨ m.val = 0
    | .inr (.inl l) => l.val = 0
    | .inr (.inr (.inl i)) => i.val = 0
    | .inl _ => False
  Ds3 := fun i => i = 2
  td := fun _ => .estructura
  r1 := 0
  r2 := 1
  r3 := 2
  Cp := fun | .mi => 0 | .mc => 1 | .md => 2
  Hf := Fin 3
  niv := fun b => b.val + 1
  crt := fun a b => (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 1)
  Af := fun _ => True
  ud := fun _ _ => .confiable
  pr := fun _ b => b = 0
  Pe := Unit
  Imp := fun _ s => s = 1
  ltCd := Lt
  sa := fun a => a
  cr := fun n a => if a = 2 then (if n = 0 then 2 else 0) else 1
  Hc := fun h => h = (0, 0, 0, 0) ∨ h = (1, 1, 0, 1)
  ev3 := fun q => if q = 2 then some (1, 1, 0, 1) else none
  pvi := fun v => v.val
  sel := fun v q => v = 0 ∨ q = 2
  vn := fun n => if n.val = 4 ∨ n.val = 5 then 1 else 0
  qn := fun n q => (n.val = 3 ∧ (q = 0 ∨ q = 2)) ∨ ((n.val = 4 ∨ n.val = 5) ∧ q = 2)
  dc := fun n e => (n.val = 3 ∧ (e = 0 ∨ e = 1)) ∨ (n.val = 4 ∧ e = 2) ∨ (n.val = 5 ∧ e = 3)
  ctr := fun a b => (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1)
  ip := fun _ n => n.val = 5
  ho := fun v => v
  vd := fun z a => z = 0 ∧ a = 2
  cd_c := 1
  qd := fun q => q = 0
  qi := fun q => q = 3
  ap := fun _ x => if x = 0 then some Ajuste.ajusta else some Ajuste.difiere
  sus := fun _ x => if x = 1 then some (fun q => q = 3) else none
  tpe := fun _ => Tpe.vm
  Pj := fun _ => True
  tpj := fun _ => Tpj.sentido_comun
  vl := fun v j => v.val = j.val
  gj := fun j q => j = 0 ∨ (j = 1 ∧ q = 2)
  cadena_Gr := by unfold IsChain Lt; refine ⟨?_, ?_, ?_⟩ <;> decide
  cadena_Am := by unfold IsChain Lt; refine ⟨?_, ?_, ?_⟩ <;> decide
  cadena_Vg := by unfold IsChain Lt; refine ⟨?_, ?_, ?_⟩ <;> decide
  cadena_Nz := by unfold IsChain Lt; refine ⟨?_, ?_, ?_⟩ <;> decide
  orden_Th := by unfold IsStrictPO; refine ⟨?_, ?_⟩ <;> decide
  gmin_lt := by decide
  cadena_Cd := by unfold IsChain Lt; refine ⟨?_, ?_, ?_⟩ <;> decide
  ev3_Hc := by
    intro q h hq
    change (if q = 2 then some ((1 : Fin 3), (1 : Fin 2), (0 : Fin 3), (1 : Fin 3)) else none) = some h at hq
    by_cases h2 : q = 2
    · rw [if_pos h2] at hq; cases hq; exact Or.inr rfl
    · rw [if_neg h2] at hq; cases hq
  ctr_sim := by intro a b h; change (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1) at h; change (b = 1 ∧ a = 3) ∨ (b = 3 ∧ a = 1); omega
  ctr_irr := by intro a h; change (a = 1 ∧ a = 3) ∨ (a = 3 ∧ a = 1) at h; omega


/-- L5: la serie del caso está en pista correcta. -/
theorem B_pc : B.pc 0 := by
  intro n hn
  have h : n = 0 ∨ n = 1 := by
    change n + 1 < 3 at hn; omega
  rcases h with rfl | rfl
  · exact ⟨1, by simp [Mp.Pf, B], by simp [B]⟩
  · exact ⟨2, by simp [Mp.Pf, B], by simp [B]⟩


private theorem aux15 (n n' : Fin 6) (e e' : Fin 4)
    (h1 : (n.val = 3 ∧ (e = 0 ∨ e = 1)) ∨ (n.val = 4 ∧ e = 2) ∨ (n.val = 5 ∧ e = 3))
    (h2 : (n'.val = 3 ∧ (e' = 0 ∨ e' = 1)) ∨ (n'.val = 4 ∧ e' = 2) ∨ (n'.val = 5 ∧ e' = 3))
    (h3 : (e = 1 ∧ e' = 3) ∨ (e = 3 ∧ e' = 1)) : n.val = 5 ∨ n'.val = 5 := by
  rcases h3 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp at h1 h2 <;> omega

private theorem aux17a (n : Fin 6) (q : Fin 4)
    (h : (n.val = 3 ∧ (q = 0 ∨ q = 2)) ∨ ((n.val = 4 ∨ n.val = 5) ∧ q = 2)) :
    (q = 0 ∨ q = 2) ∧ (q = 0 → n.val = 3) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h2, fun _ => h1⟩
  · subst h2; exact ⟨Or.inr rfl, fun h => by simp at h⟩

private theorem aux18 (s : Fin 2) (k : Nat) (q : Fin 4)
    (_hk : k < (if s = 0 then 3 else 1))
    (h : (if s = 0 then (if k = 0 then (0 : Fin 4) else if k = 1 then 1 else 2) else 3) = q)
    (hq : q = 3) : s = 1 := by
  subst hq
  by_cases hs : s = 0
  · rw [if_pos hs] at h
    by_cases h0 : k = 0
    · rw [if_pos h0] at h; exact absurd h (by decide)
    · rw [if_neg h0] at h
      by_cases h1 : k = 1
      · rw [if_pos h1] at h; exact absurd h (by decide)
      · rw [if_neg h1] at h; exact absurd h (by decide)
  · omega

private theorem auxni (e e' : Fin 4)
    (h1 : (3 = 3 ∧ (e = 0 ∨ e = 1)) ∨ (3 = 4 ∧ e = 2) ∨ (3 = 5 ∧ e = 3))
    (h2 : (4 = 3 ∧ (e' = 0 ∨ e' = 1)) ∨ (4 = 4 ∧ e' = 2) ∨ (4 = 5 ∧ e' = 3))
    (h3 : (e = 1 ∧ e' = 3) ∨ (e = 3 ∧ e' = 1)) : False := by
  rcases h3 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> revert h1 h2 <;> decide

theorem B_ley : Ley B where
  L1 := by simp [B]
  L2 := by
    refine ⟨rfl, ?_⟩
    intro n h; cases n <;> first | exact absurd rfl h | decide
  L3 := ⟨Or.inl ⟨E2.conLey X, rfl, E2.contenido_trivial X⟩, fun f => by simp [B, X]⟩
  L3b := by
    intro d
    by_cases h : d.val = 3
    · exact ⟨0, Or.inr h⟩
    · exact ⟨⟨d.val, by omega⟩, Or.inl rfl⟩
  L4 := by
    refine ⟨fun q d h => h.1, ?_⟩
    intro q d h
    have hd : ∀ q : Fin 4, ((B.ent q 3).isSome = true) → False := by decide
    show d ≠ 3
    intro hd; subst hd
    exact hd q h
  L6 := by
    intro q
    refine ⟨?_, ?_⟩
    · revert q; decide
    · revert q; decide
  L7 := by intro n f q _ _; trivial
  L8 := by intro g ⟨h1, h2⟩; change g.val < 2 at h1; change g.val = 2 at h2; omega
  L9 := by
    intro d h
    refine ⟨0, rfl, by decide, ?_⟩
    change d = 2 at h
    simp [B, h]
  L10 := by
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · intro n h
      rcases h with rfl | rfl | rfl
      · exact ⟨.mi, rfl⟩
      · exact ⟨.mc, rfl⟩
      · exact ⟨.md, rfl⟩
    · intro t; cases t
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
    · intro n _
      exact ⟨0, by decide, Or.inr rfl⟩
    · exact ⟨1, fun t => by cases t <;> simp [B]⟩
  L11 := by
    refine ⟨?_, fun q => ⟨0, rfl⟩⟩
    intro a b h
    change (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 1) at h
    show b.val + 1 < a.val + 1
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  L12 := by
    intro s _ _ n m h
    show (if n ≤ 2 then n else 2) ≤ (if m ≤ 2 then m else 2)
    split <;> split <;> omega
  L13 := by
    intro n f h
    refine ⟨0, rfl, 0, by decide, 1, rfl, trivial, ?_⟩
    have hf : f = 2 := by
      rcases h with h | ⟨a, ha, hc⟩
      · by_cases hc : f = 2 ∧ n = 0
        · exact hc.1
        · exfalso; apply h
          simp only [B, ucB] at *
          by_cases h2 : f = 2 ∧ n + 1 = 0
          · omega
          · simp [hc, h2]
      · by_cases ha2 : a = 2
        · subst ha2; exact ha.symm
        · exfalso; apply hc; simp [B, ha2]
    subst hf
    exact ⟨rfl, rfl⟩
  L14 := by
    intro q h hq hj
    by_cases h2 : q = 2
    · subst h2
      exact ⟨⟨2, by simp [Mp.Pa, Mp.Pf, B]⟩, 0, rfl, 2, by decide, rfl⟩
    · exfalso
      change (if q = 2 then some ((1 : Fin 3), (1 : Fin 2), (0 : Fin 3), (1 : Fin 3)) else none) = some h at hq
      rw [if_neg h2] at hq; cases hq
  L15 := by
    intro n n' h
    obtain ⟨e, e', h1, h2, h3⟩ := h
    rcases aux15 n n' e e' h1 h2 h3 with h5 | h5
    · exact Or.inl ⟨(), h5⟩
    · exact Or.inr ⟨(), h5⟩
  L16 := by
    intro n
    exact ⟨⟨0, rfl⟩, ⟨0, rfl⟩⟩
  L18 := by
    refine ⟨?_, ?_⟩
    · intro q h
      change q = 0 at h
      subst h
      exact ⟨0, by simp [Mp.Pa, Mp.Pf, B]⟩
    · intro q h s ⟨k, hk, hs⟩
      change q = 3 at h
      have h1 : s = 1 := aux18 s k q hk hs h
      exact ⟨(), h1⟩
  L19 := by
    intro T c
    by_cases hc : c = 0
    · subst hc
      refine ⟨⟨fun ⟨S, hS⟩ => ?_, fun h => ?_⟩, fun S hS => ?_⟩
      · exact absurd hS (by simp [B])
      · exact absurd h (by simp [B])
      · exact absurd hS (by simp [B])
    · have hc1 : c = 1 := (by decide : ∀ c : Fin 2, ¬ c = 0 → c = 1) c hc
      subst hc1
      refine ⟨⟨fun _ => by simp [B], fun _ => ⟨fun q => q = 3, by simp [B]⟩⟩, fun S hS => ?_⟩
      have : S = fun q => q = 3 := by
        have : (some (fun q : Fin 4 => q = 3) : Option (Fin 4 → Prop)) = some S := by
          simpa [B] using hS
        exact (Option.some.inj this).symm
      subst this
      exact ⟨3, rfl⟩
  L20 := by
    intro v q h
    change v = 0 ∨ q = 2 at h
    rcases h with rfl | rfl
    · exact ⟨0, rfl, Or.inl rfl⟩
    · by_cases hv : v = 0
      · subst hv; exact ⟨0, rfl, Or.inl rfl⟩
      · have hv1 : v = 1 := (by decide : ∀ c : Fin 2, ¬ c = 0 → c = 1) v hv
        subst hv1
        exact ⟨1, rfl, Or.inr ⟨rfl, rfl⟩⟩
  L17 := by
    intro n q h
    obtain ⟨hq, hn⟩ := aux17a n q h
    refine ⟨?_, ?_⟩
    · rcases hq with hq | hq
      · have hn3 := hn hq
        left
        show (if n.val = 4 ∨ n.val = 5 then (1 : Fin 2) else 0) = 0
        rw [if_neg (by omega)]
      · exact Or.inr hq
    · rcases hq with rfl | rfl
      · exact ⟨0, by simp [Mp.Pa, Mp.Pf, B]⟩
      · exact ⟨2, by simp [Mp.Pa, Mp.Pf, B]⟩

/-- Jz3(q₁) = altamente_probable y Jz3(q₃) = cierto, como en la sección 6. -/
theorem B_juicios : B.Jz3 0 = .altamente_probable ∧ B.Jz3 2 = .cierto := ⟨rfl, rfl⟩
/-- f_Lc: directa en n = 0, indirecta en n = 1. -/
theorem B_uc : B.Uc3 0 2 = .directo ∧ B.Uc3 1 2 = .indirecto := by decide

theorem B_inc : B.Inc 3 5 := ⟨1, 3, Or.inl ⟨rfl, Or.inr rfl⟩, Or.inr (Or.inr ⟨rfl, rfl⟩), Or.inl ⟨rfl, rfl⟩⟩

theorem B_Hh : B.Hh (1,1,0,1) := ⟨2, rfl, rfl⟩

/-- Caso Becker: v₁ rechaza α₃ aunque cr₀(α₃) = cd₃ ⪰ cd₂; con la revisión (n = 1) deja de serlo. -/
theorem B_Ch : B.Ch 0 0 2 ∧ ¬ B.Ch 0 1 2 ∧ ∀ n a, ¬ B.Ch 1 n a := by
  refine ⟨⟨⟨rfl, rfl⟩, Or.inr (by decide)⟩, ?_, ?_⟩
  · rintro ⟨_, h⟩
    revert h; decide
  · rintro n a ⟨⟨h, _⟩, _⟩
    exact absurd h (by decide)

/-- El perspectivismo del caso: ν y ν′ difieren de punto de vista, sin Inc entre ellos (ninguno impedido). -/
theorem B_no_inc : ¬ B.Inc 3 4 := by
  rintro ⟨e, e', h1, h2, h3⟩
  exact auxni e e' h1 h2 h3

/-- La semejanza afirmada como necesaria (q₄) sólo aparece en la serie impedida s″. -/
theorem B_qi : B.qi 3 ∧ B.Imp () 1 := ⟨rfl, rfl⟩

theorem B_cr_motivado : B.cr 1 2 ≠ B.cr 0 2 := by decide


end Bultmann
end E3
