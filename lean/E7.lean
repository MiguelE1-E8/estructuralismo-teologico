import E6
set_option linter.deprecated false

/-
  E7 · Sistematización — verificación en Lean 4 (sin Mathlib, sin sorry).
  Traduce la tupla, Mp(E7), la ley (L1–L16) y el modelo actual Nicea–Constantinopla III.

  Convenciones:
   - E7 se parametriza por Y : E6.Mp X (que a su vez depende de M : E4.Mp y X : E5.Mp M).
     Dc, Ctx, Sg, Ap, en, sg, sle, ant, cd, pf, Aut, Df vienen de E6/E5 sin redefinirse.
   - Cada cláusula por sistema L1–L13 es un predicado `Kn` (abbrev); `Adec s` las reúne;
     `Posc s` añade L14. L15–L16 relacionan pares de sistemas y forman la `Ley` global.
   - E7(d) = {s : d ∈ Dc_s ∧ Posc s}; Sis = Im(E7). Adecuación y posición NO son primitivas.
   - Cn y Rl (conceptos y relaciones) son tipos globales con pertenencia por sistema (Cns, Rls).
   - Ci = Op ⊔ Nx ⊔ Est ⊔ Es (don, testimonio) ⊔ {su}: `su` es ESTIPULACIÓN del modelo.
   - Solo se anotan (no se formalizan): revisión, propagación de la reinterpretación, reciprocidad
     E7→E6, elitismo, «falaz», orgullo; Esb ⊆ Dc×Σ solo existe en el modelo; t y sen de las doctrinas
     (la permanencia de L1 se formula con E6.sg/E6.sle).

  ESTADO (22 oct 2026). Compila sin errores ni `sorry` contra E2–E6 con `E5.Cs5` de SIETE constructores
  (sc | teo | int | tra | arte | erud | met) y `E6.fld`/`decAllCs5` con `met` (Lean 4.35.0; E2–E4 como
  adjuntados el 19-oct, E5 y E6 con ese solo cambio en copia local). Por eso `decExCs5` lista siete casos:
  con seis falla (`simp_all made no progress`). Axiomas: `nicea_Ley`, `summa_Ley`, `summa_Sis` usan solo
  `propext` y `Quot.sound`; `nicea_Sis` añade `Classical.choice`. Confirmado contra la estructura del `E5.lean` y el `E6.lean` del Project (20-oct; el E5
  actual añade `Eco_pluralismo_radical` y el E6 actual renombra tr/Gen/md: E7 no usa ninguno). Sin cambios de ley ni de campos de `Mp`.
  RENOMBRES aplicados el 20-oct (renombres_enlaces_y_cierre_E0-E8.md #5–#8, #10): Pt→cz, Dsc→Dsp, Ep→Epc,
  Cp→Rsp, Cps→Rsps, Eh→Ejm (colisiones con E2/E3/E4). E8 no usa ninguno de ellos. Sigue ABIERTA la
  ligadura Ct := E2.Grado (#4.2), sin aplicar.

  Citas de Lonergan: Método en teología, Sígueme, Salamanca 1988, cap. 13 «Sistematización»
  (pp. 323–340; el cap. 14 empieza en la p. 341). Páginas impresas, comprobadas sobre las láminas del
  texto (el número encabeza cada página). Etiquetas, como en E4 y E5: [T] lo dice el texto (con página) ·
  [L] lectura formal propia · [E] estipulación de modelado. Verificado ≠ auditado: Lean comprueba la
  consistencia del modelo; el vínculo con el texto es interpretación. Tabla completa en la sección 8
  del Doc de E7.
   - p. 323 [T] la sistematización «se ocupa de promover la comprensión de las realidades afirmadas» en
     las doctrinas; dos operaciones: ¿quid sit? ¿cur ita sit? / ¿an sit? ¿utrum ita sit? → `Tq`, E7(d).
   - p. 324 [T] «La finalidad de la sistematización no es la de aumentar la certeza, sino la de promover
     la comprensión» → L2; tres vías del Vaticano I (DS 3016): analogía, nexo de los misterios entre sí
     y con el fin último → L5 (`an`, `ns`, `nf`).
   - p. 325 [T] razones frente a autoridades (Quodl. IV, q. 9, a. 3) → L3.   p. 326 [T] «en la
     concretez del método lo fundamental es la conversión» → L13.   p. 327 [T] «todo unificado y no
     en dos partes separadas» → L6.
   - p. 328 [T] la orientación al misterio da a la palabra Dios «su significación primaria y
     fundamental» → `Su` (L9, [E]).   p. 329 [T] Lateranense IV, «desemejanza mayor» (DS 806) → L7.
   - pp. 330–331 [T] términos básicos = operaciones intencionales; especiales = el don y el testimonio;
     derivados = los objetos → `Ci`; metafísica crítica y criterio literal/metafórico, nocional/real → L9.
   - p. 332 [T] reinterpretación del símbolo; Nicea, Éfeso, Calcedonia → L10, caso Nicea.   p. 333 [T]
     ordo disciplinae; Scriptum frente a SCG y ST (cuestiones 27–29) → L11, `SummaZ`.
   - p. 334 [T] «posiciones» y «contraposiciones»; la falta de comprensión «tiende a ser múltiple» →
     L14, L15.   pp. 336–337 [T] comprensión «no más que probable»; «a la altura de cada época» →
     L2, L12.   p. 337 [T] «un asunto muy sencillo» → L8.   p. 338 [T] tres desviaciones de la
     estructura normativa → `vn` (L14b).   p. 339 [T] «in eodem dogmate…» (DS 3020) → L1; «se da
     también el desarrollo» → L16.   p. 340 [T] revisión: solo anotada, no formalizada.
-/
namespace E7
open E4 (Perfil)
open E5 (Cs5)

inductive Mx | fig | des | vag | inc deriving DecidableEq
inductive Vi | an | nis | nf deriving DecidableEq
inductive Tq | quid | cur | ansit deriving DecidableEq
inductive Mj | razon | autoridad deriving DecidableEq
inductive Ci | op | nx | est | don | tes | su deriving DecidableEq
inductive Bs | gen | esp | der deriving DecidableEq
inductive Lm | lit | met deriving DecidableEq
inductive Dn | noc | real deriving DecidableEq
inductive Sgn | prim | sec deriving DecidableEq
inductive Pm | conv | prueba deriving DecidableEq
inductive Vl | ven | fal | aj deriving DecidableEq
inductive Dvk | inc | dif | dia deriving DecidableEq

instance decAllVl (p : Vl → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p .ven ∧ p .fal ∧ p .aj) (by
    constructor
    · rintro ⟨h1, h2, h3⟩ x; cases x <;> assumption
    · intro h; exact ⟨h _, h _, h _⟩)

instance decExCs5 (p : Cs5 → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  decidable_of_iff (p .sc ∨ p .teo ∨ p .int ∨ p .tra ∨ p .arte ∨ p .erud ∨ p .met) (by
    constructor
    · rintro (h | h | h | h | h | h | h)
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
    · rintro ⟨x, hx⟩; cases x <;> simp_all)

/-! ## Modelo potencial Mp(E7) -/
structure Mp {PV I : Type} {M : E4.Mp PV I} {X : E5.Mp M} (Y : E6.Mp X) where
  -- conjuntos
  Sy : Type      -- Σ: sistemas
  Cq : Type      -- cuestiones
  Rs : Type      -- realidades
  Gc : Type      -- grados de comprensión (cadena con ⊤)
  Epc : Type      -- épocas
  Dsp : Type     -- disciplinas
  Cn : Type      -- conceptos
  Rl : Type      -- relaciones
  Rsp : Type      -- respuestas
  Sb : Type      -- símbolos
  Sig : Type     -- significaciones de los símbolos
  Ejm : Type      -- ejemplares de la analogía
  Ct : Type      -- niveles de certeza (E2)
  -- A. doctrinas
  cz : Y.Dc → Ct
  leC : Ct → Ct → Prop
  pb : Ct
  -- B. problemas
  mx : Y.Dc → Mx → Prop
  qs : Y.Dc → Cq → Prop
  nuq : Cq → Mx
  Ca : Y.Dc → Y.Dc → Prop
  -- C. sistemas
  Dcs : Sy → Y.Dc → Prop
  Cqs : Sy → Cq → Prop
  Rsps : Sy → Rsp → Prop
  Cns : Sy → Cn → Prop
  Rls : Sy → Rl → Prop
  hzs : Sy → X.Om
  eps : Sy → Epc
  cts : Sy → Dsp → Prop
  evo : Sy → Prop
  cxs : Sy → Y.Ctx
  pmS : Sy → Pm
  vnS : Sy → Vl → Prop
  -- D. comprensión
  rm : Y.Dc → Rs → Prop
  El : Sy → Y.Dc → Y.Dc → Prop
  vS : Sy → Rs → Vi → Prop
  anS : Sy → Rs → Option Ejm
  nsS : Sy → Rs → Rs → Prop
  nfS : Sy → Rs → Prop
  smS : Sy → Rs → Gc
  dsS : Sy → Rs → Gc
  gcS : Sy → Rs → Gc
  ltG : Gc → Gc → Prop
  topG : Gc
  -- E. respuestas y orden
  tq : Rsp → Tq
  mj : Rsp → Mj
  ptc : Rsp → Ct
  rc : Rsp → Rs → Prop
  Orr : Rsp → Cq → Prop
  Pre : Sy → Cq → Cq → Prop
  ltE : Sy → Cq → Cq → Prop
  -- F. términos
  bas : Cn → Bs
  co : Cn → Option Ci
  rco : Rl → Option Ci
  Mtf : Sy → Cn → Prop
  lm : Cn → Lm
  dnR : Rl → Dn
  NomD : Sy → Cn → Prop
  sgN : Cn → Sgn
  fd : Cn → Option Cn
  Sbs : Sy → Sb → Prop
  desS : Sb → Sig → Prop
  indS : Sb → Sig → Prop
  sigS : Sb → Sig → Prop
  rr : Sb → Sb
  Req : Epc → Dsp → Prop
  -- G. pluralidad
  Opp : Sy → Sy → Prop
  Irr : Sy → Sy → Prop
  -- H. desarrollo
  Suc : Sy → Sy → Prop
  ltEp : Epc → Epc → Prop
  dvt : Sy → Sy → Dvk → Prop
  -- condiciones de tipo
  cadenaG : E6.IsChain ltG
  top_max : ∀ g, g ≠ topG → ltG g topG
  nu_sub : ∀ d q, qs d q → mx d (nuq q)
  ca_inc : ∀ d d', Ca d d' → mx d Mx.inc ∧ mx d' Mx.inc
  dcs_ne : ∀ s, ∃ d, Dcs s d
  opp_symm : ∀ s s', Opp s s' → Opp s' s
  opp_irrefl : ∀ s, ¬ Opp s s
  irr_opp : ∀ s s', Irr s s' → Opp s s'
  suc_irrefl : ∀ s, ¬ Suc s s
  suc_trans : ∀ a b c, Suc a b → Suc b c → Suc a c
  dvt_suc : ∀ s s' k, dvt s s' k → Suc s s'

namespace Mp
variable {PV I : Type} {M : E4.Mp PV I} {X : E5.Mp M} {Y : E6.Mp X} (Z : Mp Y)

/-- g ⪯ g′ en la cadena de grados. -/
abbrev leG (g g' : Z.Gc) : Prop := g = g' ∨ Z.ltG g g'
/-- a ≺ b en los niveles de certeza. -/
abbrev ltC (a b : Z.Ct) : Prop := Z.leC a b ∧ ¬ Z.leC b a
abbrev epLe (e e' : Z.Epc) : Prop := e = e' ∨ Z.ltEp e e'
/-- ⋃ rm(d) para d ∈ Dc_s: las realidades que s debe comprender. -/
abbrev Rcub (s : Z.Sy) (r : Z.Rs) : Prop := ∃ d, Z.Dcs s d ∧ Z.rm d r
/-- dom(v_s). -/
abbrev dom (s : Z.Sy) (r : Z.Rs) : Prop := Z.vS s r Vi.an ∨ Z.vS s r Vi.nis ∨ Z.vS s r Vi.nf
abbrev symNs (s : Z.Sy) (a b : Z.Rs) : Prop := Z.nsS s a b ∨ Z.nsS s b a

/-- rz(s,s′) ≠ ∅: razón de la oposición (horizonte de perfil distinto o diferenciación distinta). -/
abbrev RzNe (s s' : Z.Sy) : Prop :=
  X.pf (Z.hzs s) ≠ X.pf (Z.hzs s') ∨ ∃ x, ¬ (X.Df (Z.hzs s) x ↔ X.Df (Z.hzs s') x)

/-! ### Cláusulas por sistema (L1–L13) -/
/-- L1: permanencia en el contexto del sistema y ninguna respuesta an_sit.
    [T p. 339] «ha de ser siempre in eodem dogmate, eodem sensu eademque sententia» (DS 3020; cf. p. 334);
    [T p. 323] la sistemática responde a quid sit / cur ita sit, no a an sit; [L] la permanencia se
    formula con E6.sg y E6.sle, pues Lonergan no da un sentido único. -/
abbrev K1 (s : Z.Sy) : Prop :=
  (∀ d, Z.Dcs s d → Y.en d (Z.cxs s) ∧
      ∀ a b, Y.sg d (Y.cd d) = some a → Y.sg d (Z.cxs s) = some b → Y.sle a b) ∧
  (∀ c, Z.Rsps s c → Z.tq c ≠ Tq.ansit)
/-- L2: probabilidad. [T p. 336] la comprensión «será necesariamente imperfecta, meramente análoga y por lo
    general no más que probable»; [T p. 337] el asentimiento de fe es «el más firme de todos»;
    [T p. 324] no se busca «aumentar la certeza». [L] `Ct` es un orden abstracto con `pb`. -/
abbrev K2 (s : Z.Sy) : Prop :=
  (∀ c, Z.Rsps s c → Z.leC (Z.ptc c) Z.pb) ∧ (∀ d, Z.Dcs s d → Z.ltC Z.pb (Z.cz d))
/-- L3: razón. [T p. 325] hay que apoyarse «en las razones que hacen salir a la luz el fundamento de la
    verdad»; quien invoca solo autoridades da certeza pero «lo despedirá vacío» (Quodl. IV, q. 9, a. 3). -/
abbrev K3 (s : Z.Sy) : Prop := ∀ c, Z.Rsps s c → Z.mj c = Mj.razon
/-- L4: eliminación de las contradicciones aparentes. [T p. 324] la sistemática «se esfuerza por entrever
    cómo es posible que los hechos sean lo que son»; [L] que eso disuelva las contradicciones aparentes
    de sus propias doctrinas es lectura propia (apoyo indirecto). -/
abbrev K4 (s : Z.Sy) : Prop := ∀ d d', Z.El s d d' ↔ (Z.Ca d d' ∧ Z.Dcs s d ∧ Z.Dcs s d')
/-- L5: comprensión. [T p. 324] «tanto por analogía con lo que conoce naturalmente, como por la relación de
    los misterios entre sí y con el fin último del hombre» (Vaticano I, DS 3016); [L] an/nis/nf. -/
abbrev K5 (s : Z.Sy) : Prop :=
  ∀ r, Z.Rcub s r → Z.dom s r ∧ (Z.vS s r Vi.an → (Z.anS s r).isSome = true) ∧
    (Z.vS s r Vi.nf → Z.nfS s r)
/-- L6: unidad. [T p. 327] la sistematización «debe presentarse como un todo unificado y no en dos partes
    separadas»; [L] el grafo (⋃ rm(d), ns_s) es la formalización de «todo unificado». -/
abbrev K6 (s : Z.Sy) : Prop :=
  ∀ r r', Z.Rcub s r → Z.Rcub s r' → r = r' ∨ E4.TG (Z.symNs s) r r'
/-- L7: límite de la comprensión. [T p. 329] «entre el Creador y la criatura no se puede indicar ninguna
    semejanza sin que al mismo tiempo se indique una desemejanza mayor» (Lateranense IV, DS 806); y los
    misterios «permanecen recubiertos por el velo mismo de la fe» (Vaticano I, DS 3016). -/
abbrev K7 (s : Z.Sy) : Prop :=
  ∀ r, Z.dom s r → Z.ltG (Z.gcS s r) Z.topG ∧ (Z.vS s r Vi.an → Z.ltG (Z.smS s r) (Z.dsS s r))
/-- L8: sin especulación. [T p. 337] la teología sistemática por la que aboga Lonergan «es en realidad un
    asunto muy sencillo. Pretende una comprensión de las verdades de la fe, un Glaubensverständnis»,
    es decir, de «las confesiones de fe de la Iglesia». [L] rc ⊆ ⋃ rm(d). -/
abbrev K8 (s : Z.Sy) : Prop := ∀ c, Z.Rsps s c → ∀ r, Z.rc c r → Z.Rcub s r
/-- L9: metafísica crítica. [T pp. 330–331] hacer «derivados, y no básicos, los términos y relaciones
    metafísicas» da una metafísica crítica: se pueden eliminar los términos «vacíos o falaces»; ofrece
    «un criterio para establecer la diferencia entre la significación literal y la significación
    metafórica y, además, entre la distinción nocional y la distinción real» (p. 331); [T p. 328] la
    «significación primaria y fundamental» de Dios es el término de la orientación al misterio.
    [E] Su en Ci (persona ↦ Su) y los nombres secundarios con fd/co del modelo. -/
abbrev K9 (s : Z.Sy) : Prop :=
  (∀ c, Z.Mtf s c → Z.bas c ≠ Bs.gen ∧ Z.bas c ≠ Bs.esp) ∧
  (∀ c, Z.Cns s c → (Z.co c).isSome = true) ∧
  (∀ l, Z.Rls s l → (Z.rco l).isSome = true) ∧
  (∀ c, Z.NomD s c → Z.sgN c = Sgn.sec →
      ∃ n, Z.fd c = some n ∧ Z.NomD s n ∧ Z.sgN n = Sgn.prim ∧ Z.co n = some Ci.don) ∧
  (∀ c c', Z.Cns s c → Z.Cns s c' → Z.co c = Z.co c' → Z.lm c = Z.lm c') ∧
  (∀ l l', Z.Rls s l → Z.Rls s l' → Z.rco l = Z.rco l' → Z.dnR l = Z.dnR l')
/-- L10: reinterpretación de los símbolos. [T p. 332] «la inadecuación de las expresiones se corrige por
    medio de la reinterpretación, modificando el símbolo de manera que se excluyan las significaciones
    indeseables y se aclaren las significaciones deseadas»; ejemplo: el Dios bíblico «que está de pie o
    sentado, que tiene una mano derecha». -/
abbrev K10 (s : Z.Sy) : Prop :=
  ∀ e, Z.Sbs s e → (∀ g, Z.desS e g → Z.sigS (Z.rr e) g) ∧ (∀ g, Z.sigS (Z.rr e) g → ¬ Z.indS e g)
/-- L11: orden de las cuestiones. [T p. 333] «el profesor pospone aquellas soluciones que presuponen otras,
    y comienza por aquellos problemas cuya solución no presupone la solución de otros» (ordo
    disciplinae; Summa theologiae, Prologus). [L] ltE como extensión lineal estricta de Pre. -/
abbrev K11 (s : Z.Sy) : Prop :=
  (∀ a b, Z.Pre s a b → Z.ltE s a b) ∧ (∀ a, ¬ Z.ltE s a a) ∧
  (∀ a b c, Z.ltE s a b → Z.ltE s b c → Z.ltE s a c) ∧
  (∀ a b, Z.Cqs s a → Z.Cqs s b → a ≠ b → Z.ltE s a b ∨ Z.ltE s b a)
/-- L12: época. [T p. 337] la comprensión «debe estar a la altura de cada época. En la edad media bastaba
    un sistema estático. Pero en el mundo contemporáneo la teología ha de sentirse en su casa con la
    ciencia, la erudición y la filosofía contemporáneas». [E] Req(época) como estipulación. -/
abbrev K12 (s : Z.Sy) : Prop :=
  (∀ x, Z.Req (Z.eps s) x → Z.cts s x) ∧ ((∃ x, Z.Req (Z.eps s) x) → Z.evo s)
/-- L13: primacía de la conversión. [T p. 326] «En la lógica abstracta del clasicismo lo fundamental es la
    prueba; en la concretez del método lo fundamental es la conversión»; [T p. 327] la conversión
    religiosa «precede normalmente» al esfuerzo por elaborar pruebas de la existencia de Dios. -/
abbrev K13 (s : Z.Sy) : Prop := Z.pmS s = Pm.conv

end Mp

/-- Sistema adecuado: L1–L13. -/
structure Adec {PV I : Type} {M : E4.Mp PV I} {X : E5.Mp M} {Y : E6.Mp X} (Z : Mp Y) (s : Z.Sy) : Prop where
  L1 : Z.K1 s
  L2 : Z.K2 s
  L3 : Z.K3 s
  L4 : Z.K4 s
  L5 : Z.K5 s
  L6 : Z.K6 s
  L7 : Z.K7 s
  L8 : Z.K8 s
  L9 : Z.K9 s
  L10 : Z.K10 s
  L11 : Z.K11 s
  L12 : Z.K12 s
  L13 : Z.K13 s

/-- Posición: adecuado + L14 (todas las doctrinas son aprehendidas realmente desde hz(s) y vn(s) = ∅).
    [T p. 334] «se juzgará cuáles son los sistemas que expresan posiciones y cuáles los que expresan
    contraposiciones»; [T p. 338] la estructura normativa puede violarse de tres modos: maximizar
    ventajas individuales o de grupo, falsas concepciones de la verdad, normas «objetivas» ajenas a la
    comprensión (→ `vn`). [L] Ap real por E6 L14: perfil (1,1,1) y horizonte auténtico. -/
structure Posc {PV I : Type} {M : E4.Mp PV I} {X : E5.Mp M} {Y : E6.Mp X} (Z : Mp Y) (s : Z.Sy) : Prop
    extends Adec Z s where
  L14a : ∀ d, Z.Dcs s d → Y.Ap (Z.hzs s) d
  L14b : ∀ v, ¬ Z.vnS s v

namespace Mp
variable {PV I : Type} {M : E4.Mp PV I} {X : E5.Mp M} {Y : E6.Mp X} (Z : Mp Y)

/-- E7(d) = {s : d ∈ Dc_s, s posición}. -/
abbrev E7 (d : Y.Dc) (s : Z.Sy) : Prop := Z.Dcs s d ∧ Posc Z s
/-- Sis := Im(E7). -/
abbrev Sis (s : Z.Sy) : Prop := ∃ d, Z.E7 d s
/-- Contraposición: sistema que no es posición. -/
abbrev Contrap (s : Z.Sy) : Prop := ¬ Posc Z s
end Mp

/-! ## Ley global: L15–L16 (relacionan pares de sistemas)
  L15 [T p. 334] «mientras la genuina comprensión tiende a ser única, la falta de comprensión tiende a ser
  múltiple», y «se puede esperar que haya un abanico de sistemas opuestos»; [T pp. 337–338] la
  incomprensión también puede sistematizarse; las raíces se buscan por dialéctica (contexto, formación
  del autor, conversión, concepción del método). [L] RzNe es derivada de E5 (pf y Df de hz).
  L16 [T p. 333] lo tratado «en libros bien separados» en la SCG «se presenta unido y en continuidad» en la
  ST; [T pp. 338–339] cuatro factores de continuidad (estructura normativa, don, permanencia de los
  dogmas, realizaciones genuinas) y «se da también el desarrollo». [L] sus ⊆ y ⪯ de gc entre posiciones. -/
structure Ley {PV I : Type} {M : E4.Mp PV I} {X : E5.Mp M} {Y : E6.Mp X} (Z : Mp Y) : Prop where
  /-- L15: toda oposición tiene razón; dos posiciones no son irreconciliables. -/
  L15a : ∀ s s', Z.Opp s s' → Z.RzNe s s'
  L15b : ∀ s s', Posc Z s → Posc Z s' → ¬ Z.Irr s s'
  /-- L16: sucesión de sistemas. -/
  L16a : ∀ s s', Z.Suc s s' →
    Z.epLe (Z.eps s) (Z.eps s') ∧ (∀ d, Z.Dcs s d → Z.Dcs s' d) ∧ Y.ant (Z.cxs s) (Z.cxs s')
  L16b : ∀ s s', Z.Suc s s' → Posc Z s → Posc Z s' →
    (∀ r, Z.Rcub s r → Z.Rcub s' r) ∧ (∀ r, Z.Rcub s r → Z.leG (Z.gcS s r) (Z.gcS s' r))

/-! ## Consecuencias generales -/
section General
variable {PV I : Type} {M : E4.Mp PV I} {X : E5.Mp M} {Y : E6.Mp X} {Z : Mp Y}

theorem e7_adec {d : Y.Dc} {s : Z.Sy} (h : Z.E7 d s) : Adec Z s := h.2.toAdec

/-- Lo que E7 entrega a E8 son solo posiciones: la imagen de E7 excluye las contraposiciones. -/
theorem sis_posc {s : Z.Sy} (h : Z.Sis s) : Posc Z s := by
  obtain ⟨_, _, hp⟩ := h; exact hp

theorem contrap_no_sis {s : Z.Sy} (h : Z.Contrap s) : ¬ Z.Sis s := fun hs => h (sis_posc hs)

/-- La permanencia, la razón y la probabilidad son propiedades de todo sistema adecuado. -/
theorem adec_razon {s : Z.Sy} (h : Adec Z s) {c : Z.Rsp} (hc : Z.Rsps s c) : Z.mj c = Mj.razon :=
  h.L3 c hc

/-- Posición ⇒ conversión plena y horizonte auténtico en hz(s) (por L14 de E6). -/
theorem posc_conversion (LY : E6.Ley Y) {s : Z.Sy} (h : Posc Z s) :
    ∀ d, Z.Dcs s d → X.pf (Z.hzs s) = (true, true, true) ∧ X.Aut (Z.hzs s) :=
  fun d hd => LY.L14 _ d (h.L14a d hd)

/-- hz(s) auténtico y con conversión plena: de ahí hz(s) ∈ Rec(s) en E8 (Nuc(s) ⊆ Dc_s). -/
theorem posc_pm (s : Z.Sy) (h : Posc Z s) : Z.pmS s = Pm.conv := h.L13

/-- Pre acíclica se sigue de L11 (extensión lineal estricta). -/
theorem pre_acyclic {s : Z.Sy} (h : Z.K11 s) : ∀ q, ¬ E4.TG (Z.Pre s) q q := by
  have key : ∀ a b, E4.TG (Z.Pre s) a b → Z.ltE s a b := by
    intro a b t
    induction t with
    | base hr => exact h.1 _ _ hr
    | step _ hr ih => exact h.2.2.1 _ _ _ ih (h.1 _ _ hr)
  intro q t
  exact h.2.1 q (key q q t)

/-- Dos posiciones oponentes difieren por conversión o por diferenciación (L15). -/
theorem opp_razon (L : Ley Z) {s s' : Z.Sy} (h : Z.Opp s s') : Z.RzNe s s' := L.L15a s s' h

/-- La sucesión entre posiciones no pierde realidades comprendidas (L16). -/
theorem suc_sus (L : Ley Z) {s s' : Z.Sy} (h : Z.Suc s s') (p : Posc Z s) (p' : Posc Z s') :
    ∀ r, Z.Rcub s r → Z.Rcub s' r := (L.L16b s s' h p p').1

/-- El grafo ns no puede ser el vacío si hay dos realidades distintas que comprender (L6). -/
theorem k6_ns_nonempty {s : Z.Sy} (h : Z.K6 s) {r r' : Z.Rs} (hr : Z.Rcub s r) (hr' : Z.Rcub s r')
    (hne : r ≠ r') : ∃ a b, Z.symNs s a b := by
  rcases h r r' hr hr' with he | ht
  · exact absurd he hne
  · induction ht with
    | base hh => exact ⟨_, _, hh⟩
    | step _ hh _ => exact ⟨_, _, hh⟩

end General

/-! ## Modelo actual: Nicea–Constantinopla III
  Sobre E6.NiceaY (Dc = Fin 9; d₁ = Nicea, d₄ = Calcedonia, d₆ y d₇ esbozos).
  Σ = Fin 3: 0 = s₆, 1 = s₇, 2 = s_A.  Cq = Fin 3: q₁, q₂, q₃.  Rs = Fin 4: r₁…r₄.
  Gc = Fin 3: g₁ < g₂ < ⊤ = g₃.  Cn = Fin 2: persona (0), naturaleza (1).  Rsp = Fin 2: c₁, c₂.
  Ct = Fin 3 con pb = 1 y cz(d) = 2 (certeza de fe). Epc = Fin 1. Dsp = Fin 2 (0 = filosofía).
  Citas: [T p. 332] las crisis de Arrio, Nestorio y Eutiques y «las declaraciones possistemáticas de
  Nicea, Éfeso y Calcedonia»; [T p. 328] el don y la orientación al misterio dan a Dios su significación
  primaria. ESTIPULACIONES (ver Doc de E7): persona ↦ Su; en(d₄,k₆), en(d₄,k₇) y d₄ ∈ Ap(ω_cd) son datos
  de E6 que el caso supone. dvt(s₆,s₇) = ∅ (el modo tsi de E6 no está en los tipos de E7). -/
section Nicea
open E6 (NiceaY NiceaX)

abbrev NiceaZ : Mp NiceaY where
  Sy := Fin 3
  Cq := Fin 3
  Rs := Fin 4
  Gc := Fin 3
  Epc := Fin 1
  Dsp := Fin 2
  Cn := Fin 2
  Rl := Fin 1
  Rsp := Fin 2
  Sb := Fin 1
  Sig := Fin 1
  Ejm := Fin 1
  Ct := Fin 3
  cz := fun _ => 2
  leC := fun a b => a.val ≤ b.val
  pb := 1
  mx := fun d m => (d.val = 4 ∧ (m = Mx.vag ∨ m = Mx.inc)) ∨ (d.val = 1 ∧ m = Mx.vag)
  qs := fun d q => (d.val = 4 ∧ q.val ≤ 1) ∨ (d.val = 1 ∧ q.val = 2)
  nuq := fun q => if q.val = 1 then Mx.inc else Mx.vag
  Ca := fun d d' => d.val = 4 ∧ d'.val = 4
  Dcs := fun s d => (s.val ≤ 1 ∧ d.val = 4) ∨ (s.val = 2 ∧ d.val = 1)
  Cqs := fun s q => (s.val ≤ 1 ∧ q.val ≤ 1) ∨ (s.val = 2 ∧ q.val = 2)
  Rsps := fun s _ => s.val ≤ 1
  Cns := fun s _ => s.val ≤ 1
  Rls := fun _ _ => False
  hzs := fun s => if s.val = 2 then (0 : Fin 3) else (2 : Fin 3)
  eps := fun _ => 0
  cts := fun _ x => x.val = 0
  evo := fun _ => False
  cxs := fun s => if s.val = 0 then (6 : Fin 8) else if s.val = 1 then (7 : Fin 8) else (1 : Fin 8)
  pmS := fun s => if s.val = 2 then Pm.prueba else Pm.conv
  vnS := fun s v => s.val = 2 ∧ v = Vl.fal
  rm := fun d r => (d.val = 4 ∧ r.val ≤ 2) ∨ (d.val = 1 ∧ r.val = 3)
  El := fun s d d' => s.val ≤ 1 ∧ d.val = 4 ∧ d'.val = 4
  vS := fun s r v => ((s.val ≤ 1 ∧ r.val ≤ 2) ∨ (s.val = 2 ∧ r.val = 3)) ∧ v = Vi.nis
  anS := fun _ _ => none
  nsS := fun s a b => s.val ≤ 1 ∧ ((a.val = 0 ∧ b.val = 1) ∨ (a.val = 1 ∧ b.val = 2))
  nfS := fun _ _ => False
  smS := fun _ _ => 0
  dsS := fun _ _ => 0
  gcS := fun s _ => if s.val = 1 then (1 : Fin 3) else (0 : Fin 3)
  ltG := fun a b => a.val < b.val
  topG := 2
  tq := fun _ => Tq.quid
  mj := fun _ => Mj.razon
  ptc := fun _ => 1
  rc := fun c r => (c.val = 0 ∧ r.val ≤ 1) ∨ (c.val = 1 ∧ r.val = 2)
  Orr := fun c q => c.val = 0 ∧ q.val = 1
  Pre := fun s a b => s.val ≤ 1 ∧ a.val = 0 ∧ b.val = 1
  ltE := fun _ a b => a.val < b.val
  bas := fun _ => Bs.der
  co := fun c => some (if c.val = 0 then Ci.su else Ci.op)
  rco := fun _ => none
  Mtf := fun s _ => s.val ≤ 1
  lm := fun _ => Lm.lit
  dnR := fun _ => Dn.noc
  NomD := fun _ _ => False
  sgN := fun _ => Sgn.prim
  fd := fun _ => none
  Sbs := fun _ _ => False
  desS := fun _ _ => False
  indS := fun _ _ => False
  sigS := fun _ _ => False
  rr := fun e => e
  Req := fun _ _ => False
  Opp := fun s s' => (s.val = 2 ∧ s'.val ≤ 1) ∨ (s.val ≤ 1 ∧ s'.val = 2)
  Irr := fun _ _ => False
  Suc := fun s s' => s.val = 0 ∧ s'.val = 1
  ltEp := fun _ _ => False
  dvt := fun _ _ _ => False
  cadenaG := by unfold E6.IsChain; refine ⟨?_, ?_, ?_⟩ <;> decide
  top_max := by decide
  nu_sub := by decide
  ca_inc := by decide
  dcs_ne := by decide
  opp_symm := by decide
  opp_irrefl := by decide
  irr_opp := by decide
  suc_irrefl := by decide
  suc_trans := by decide
  dvt_suc := fun _ _ _ h => h.elim


set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 8192

/-! Instancias de decidibilidad sobre los tipos proyectados (se reducen a `Fin n`). -/
instance (p : NiceaZ.Sy → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NiceaZ.Sy → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NiceaZ.Sy) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NiceaZ.Cq → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NiceaZ.Cq → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NiceaZ.Cq) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NiceaZ.Rs → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 4, p x))
instance (p : NiceaZ.Rs → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 4, p x))
instance (a b : NiceaZ.Rs) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 4) = b))
instance (p : NiceaZ.Gc → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NiceaZ.Gc → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NiceaZ.Gc) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NiceaZ.Epc → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NiceaZ.Epc → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NiceaZ.Epc) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NiceaZ.Dsp → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NiceaZ.Dsp → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NiceaZ.Dsp) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NiceaZ.Cn → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NiceaZ.Cn → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NiceaZ.Cn) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NiceaZ.Rl → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NiceaZ.Rl → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NiceaZ.Rl) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NiceaZ.Rsp → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NiceaZ.Rsp → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NiceaZ.Rsp) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NiceaZ.Sb → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NiceaZ.Sb → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NiceaZ.Sb) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NiceaZ.Sig → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NiceaZ.Sig → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NiceaZ.Sig) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NiceaZ.Ejm → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NiceaZ.Ejm → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NiceaZ.Ejm) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NiceaZ.Ct → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NiceaZ.Ct → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NiceaZ.Ct) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))

/-! ### Los sistemas del caso son adecuados (s₆, s₇) o no (s_A) -/
theorem nicea_K6 : ∀ s : Fin 3, NiceaZ.K6 s := by
  have key : ∀ (s r r' : Fin 4) (s' : Fin 3), s'.val ≤ 1 → (r.val ≤ 2) → (r'.val ≤ 2) →
      r = r' ∨ NiceaZ.symNs s' r r' ∨ ∃ c, NiceaZ.symNs s' r c ∧ NiceaZ.symNs s' c r' := by
    intro _ r r' s' h1 h2 h3; revert r r'; revert s'; decide
  intro s r r' hr hr'
  have rr : ∀ (s : Fin 3) (r : Fin 4), NiceaZ.Rcub s r → (s.val ≤ 1 ∧ r.val ≤ 2) ∨ (s.val = 2 ∧ r.val = 3) := by
    decide
  rcases rr s r hr with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases rr s r' hr' with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · rcases key 0 r r' s h1 h2 h4 with h | h | ⟨c, hc, hc'⟩
    · exact Or.inl h
    · exact Or.inr (E4.TG.base h)
    · exact Or.inr (E4.TG.step (E4.TG.base hc) hc')
  · omega
  · omega
  · left
    apply Fin.ext; omega

theorem nicea_K1 : ∀ s : Fin 3, s.val ≤ 1 → NiceaZ.K1 s := by decide
theorem nicea_K2 : ∀ s : Fin 3, s.val ≤ 1 → NiceaZ.K2 s := by decide
theorem nicea_K3 : ∀ s : Fin 3, s.val ≤ 1 → NiceaZ.K3 s := by decide
theorem nicea_K4 : ∀ s : Fin 3, s.val ≤ 1 → NiceaZ.K4 s := by decide
theorem nicea_K5 : ∀ s : Fin 3, s.val ≤ 1 → NiceaZ.K5 s := by decide
theorem nicea_K7 : ∀ s : Fin 3, s.val ≤ 1 → NiceaZ.K7 s := by decide
theorem nicea_K8 : ∀ s : Fin 3, s.val ≤ 1 → NiceaZ.K8 s := by decide
theorem nicea_K9 : ∀ s : Fin 3, s.val ≤ 1 → NiceaZ.K9 s := by decide
theorem nicea_K10 : ∀ s : Fin 3, s.val ≤ 1 → NiceaZ.K10 s := by decide
theorem nicea_K11 : ∀ s : Fin 3, s.val ≤ 1 → NiceaZ.K11 s := by decide
theorem nicea_K12 : ∀ s : Fin 3, s.val ≤ 1 → NiceaZ.K12 s := by decide
theorem nicea_K13 : ∀ s : Fin 3, s.val ≤ 1 → NiceaZ.K13 s := by decide

theorem nicea_Adec_01 : ∀ s : Fin 3, s.val ≤ 1 → Adec NiceaZ s := fun s hs =>
  ⟨nicea_K1 s hs, nicea_K2 s hs, nicea_K3 s hs, nicea_K4 s hs, nicea_K5 s hs, nicea_K6 s,
   nicea_K7 s hs, nicea_K8 s hs, nicea_K9 s hs, nicea_K10 s hs, nicea_K11 s hs, nicea_K12 s hs,
   nicea_K13 s hs⟩

/-- s_A no es adecuado: pm = prueba (L13). -/
theorem nicea_sA_no_adec : ¬ Adec NiceaZ 2 := fun h => absurd h.L13 (by decide)

theorem nicea_Posc_01 : ∀ s : Fin 3, s.val ≤ 1 → Posc NiceaZ s := fun s hs =>
  ⟨nicea_Adec_01 s hs, (show ∀ s : Fin 3, s.val ≤ 1 → ∀ d, NiceaZ.Dcs s d → E6.NiceaY.Ap (NiceaZ.hzs s) d by decide) s hs, (show ∀ s : Fin 3, s.val ≤ 1 → ∀ v, ¬ NiceaZ.vnS s v by decide) s hs⟩

/-- s_A es contraposición. -/
theorem nicea_sA_contrap : NiceaZ.Contrap 2 := fun h => nicea_sA_no_adec h.toAdec

/-! ### E7 y su imagen -/
theorem nicea_E7_d4 : ∀ s : Fin 3, NiceaZ.E7 4 s ↔ s.val ≤ 1 := by
  intro s; constructor
  · rintro ⟨hd, hp⟩
    exact (show ∀ s : Fin 3, NiceaZ.Dcs s 4 → s.val ≤ 1 by decide) s hd
  · intro hs; exact ⟨(show ∀ s : Fin 3, s.val ≤ 1 → NiceaZ.Dcs s 4 by decide) s hs, nicea_Posc_01 s hs⟩

theorem nicea_E7_d1 : ∀ s : Fin 3, ¬ NiceaZ.E7 1 s := by
  intro s ⟨hd, hp⟩
  have : s = 2 := (show ∀ s : Fin 3, NiceaZ.Dcs s 1 → s = 2 by decide) s hd
  subst this; exact nicea_sA_contrap hp

/-- E7(d) = ∅ para las doctrinas que ningún sistema posición sostiene (d₆, d₇ son esbozos). -/
theorem nicea_E7_otros : ∀ d : Fin 9, d.val ≠ 4 → ∀ s : Fin 3, ¬ NiceaZ.E7 d s := by
  intro d hd s ⟨hdc, hp⟩
  by_cases h1 : d.val = 1
  · have : d = 1 := Fin.ext h1
    subst this; exact nicea_E7_d1 s ⟨hdc, hp⟩
  · have := (show ∀ d : Fin 9, ∀ s : Fin 3, NiceaZ.Dcs s d → d.val = 4 ∨ d.val = 1 by decide) d s hdc
    omega

/-- Im(E7) = Sis = {s₆, s₇}. -/
theorem nicea_Sis : ∀ s : Fin 3, NiceaZ.Sis s ↔ s.val ≤ 1 := by
  intro s; constructor
  · rintro ⟨d, hd⟩
    by_cases h : d.val = 4
    · have : d = 4 := Fin.ext h
      subst this; exact (nicea_E7_d4 s).1 hd
    · exact absurd hd (nicea_E7_otros d h s)
  · intro hs; exact ⟨4, (nicea_E7_d4 s).2 hs⟩

/-- La ley global L15–L16 se cumple en el caso. -/
theorem nicea_Ley : Ley NiceaZ where
  L15a := by decide
  L15b := by
    intro s s' _ _ h; exact h
  L16a := by decide
  L16b := by
    intro s s' h _ _
    have : s = 0 ∧ s' = 1 := (show ∀ s s' : Fin 3, NiceaZ.Suc s s' → s = 0 ∧ s' = 1 by decide) s s' h
    obtain ⟨rfl, rfl⟩ := this
    decide

/-- Mod(E7) ≠ ∅, sobre Mod(E4), Mod(E5), Mod(E6) no vacíos. -/
theorem Mod_noVacio : ∃ Z : Mp E6.NiceaY, Ley Z := ⟨NiceaZ, nicea_Ley⟩

/-- hz(s) auténtico y con conversión plena para todo s ∈ Sis (por L14 de E6). -/
theorem nicea_hz (LY : E6.Ley E6.NiceaY) : ∀ s : Fin 3, NiceaZ.Sis s →
    E6.NiceaX.pf (NiceaZ.hzs s) = (true, true, true) ∧ E6.NiceaX.Aut (NiceaZ.hzs s) := by
  intro s hs
  obtain ⟨d, hd, hp⟩ := hs
  exact posc_conversion LY hp d hd

/-- Pluralidad: s_A se opone a s₆ y s₇ por el perfil de su horizonte. -/
theorem nicea_pluralidad :
    NiceaZ.Opp 2 0 ∧ NiceaZ.Opp 2 1 ∧ NiceaZ.RzNe 2 0 ∧ NiceaZ.RzNe 2 1 := by decide

/-- Sucesión s₆ → s₇ (L16). -/
theorem nicea_suc : NiceaZ.Suc 0 1 := by decide

/-! ### Mp ⊋ Mod: modelos bien tipados que violan una cláusula (s₆ = 0) -/
theorem bad_L1 : ¬ { NiceaZ with tq := fun _ => Tq.ansit }.K1 0 := by decide
theorem bad_L1p : ¬ { NiceaZ with cxs := fun _ => (3 : Fin 8) }.K1 0 := by decide
theorem bad_L2 : ¬ { NiceaZ with ptc := fun _ => 2 }.K2 0 := by decide
theorem bad_L3 : ¬ { NiceaZ with mj := fun _ => Mj.autoridad }.K3 0 := by decide
theorem bad_L4 : ¬ { NiceaZ with El := fun _ _ _ => False }.K4 0 := by decide
theorem bad_L5 : ¬ { NiceaZ with vS := fun _ _ _ => False }.K5 0 := by decide
theorem bad_L6 : ¬ { NiceaZ with nsS := fun _ _ _ => False }.K6 0 := by
  intro h
  obtain ⟨a, b, hab⟩ := k6_ns_nonempty h (r := 0) (r' := 1) (by decide) (by decide) (by decide)
  rcases hab with h | h <;> exact h
theorem bad_L7 : ¬ { NiceaZ with gcS := fun _ _ => 2 }.K7 0 := by decide
theorem bad_L8 : ¬ { NiceaZ with rc := fun _ _ => True }.K8 0 := by decide
theorem bad_L9 : ¬ { NiceaZ with co := fun _ => none }.K9 0 := by decide
theorem bad_L11 : ¬ { NiceaZ with ltE := fun _ a b => b.val < a.val }.K11 0 := by decide
theorem bad_L12 : ¬ { NiceaZ with Req := fun _ _ => True }.K12 0 := by decide
theorem bad_L13 : ¬ { NiceaZ with pmS := fun _ => Pm.prueba }.K13 0 := by decide
theorem bad_L14 : ¬ Posc { NiceaZ with hzs := fun _ => (0 : Fin 3) } 0 :=
  fun h => absurd (h.L14a 4 (by decide)) (by decide)
theorem bad_L15 : ¬ Ley { NiceaZ with hzs := fun _ => (2 : Fin 3) } := fun L =>
  absurd (L.L15a 2 0 (by decide)) (by decide)
theorem bad_L16 : ¬ Ley { NiceaZ with cxs := fun _ => (6 : Fin 8) } := fun L =>
  absurd (L.L16a 0 1 (by decide)).2.2 (by decide)

/-- Los esbozos d₆ y d₇ no tienen sistema propio: E7(d₆) = E7(d₇) = ∅. -/
theorem nicea_esbozos : (∀ s : Fin 3, ¬ NiceaZ.E7 6 s) ∧ (∀ s : Fin 3, ¬ NiceaZ.E7 7 s) :=
  ⟨nicea_E7_otros 6 (by decide), nicea_E7_otros 7 (by decide)⟩


/-! ## Segundo caso: la escolástica (Scriptum → SCG IV → ST III) sobre d₄
  Mismo E6.NiceaY, solo con d₄ (el Verbo se encarnó): lo único que ese caso de E6 permite
  para sistemas con un único contexto de enunciación (L1). Los sistemas son
  Σ = Fin 3: 0 = Scriptum (s_α), 1 = SCG IV (s_β), 2 = ST (s_γ); cx = k₄, k₆, k₇.
  Ejerce lo que Nicea no toca: analogía (L5, L7), vía del fin (nf), reinterpretación de un símbolo
  (L10: «sentado a la derecha», cf. p. 332), nombres de Dios (NomD, sg, fd, L9), y L11 con un
  sistema que falla (el Scriptum, cuyas cuestiones se tratan «al azar», p. 333).
  ESTIPULACIONES: an(r₁) = el sujeto consciente, nf = {r₀}, co(Dios Uno y Trino) = don y la
  asignación cx = k₄, k₆, k₇ son lecturas mías; la parte trinitaria (q. 27–29) queda para
  un modelo de E6 con esas doctrinas. -/
abbrev SummaZ : Mp NiceaY where
  Sy := Fin 3
  Cq := Fin 2
  Rs := Fin 3
  Gc := Fin 3
  Epc := Fin 1
  Dsp := Fin 2
  Cn := Fin 4
  Rl := Fin 1
  Rsp := Fin 2
  Sb := Fin 1
  Sig := Fin 2
  Ejm := Fin 1
  Ct := Fin 3
  cz := fun _ => 2
  leC := fun a b => a.val ≤ b.val
  pb := 1
  mx := fun d m => d.val = 4 ∧ (m = Mx.vag ∨ m = Mx.inc)
  qs := fun d q => d.val = 4
  nuq := fun q => if q.val = 1 then Mx.inc else Mx.vag
  Ca := fun d d' => d.val = 4 ∧ d'.val = 4
  Dcs := fun _ d => d.val = 4
  Cqs := fun _ _ => True
  Rsps := fun _ _ => True
  Cns := fun _ _ => True
  Rls := fun _ _ => False
  hzs := fun _ => (2 : Fin 3)
  eps := fun _ => 0
  cts := fun _ x => x.val = 0
  evo := fun _ => False
  cxs := fun s => if s.val = 0 then (4 : Fin 8) else if s.val = 1 then (6 : Fin 8) else (7 : Fin 8)
  pmS := fun _ => Pm.conv
  vnS := fun _ _ => False
  rm := fun d r => d.val = 4
  El := fun _ d d' => d.val = 4 ∧ d'.val = 4
  vS := fun _ r v => (r.val = 0 ∧ (v = Vi.nis ∨ v = Vi.nf)) ∨ (r.val = 1 ∧ (v = Vi.nis ∨ v = Vi.an)) ∨
    (r.val = 2 ∧ v = Vi.nis)
  anS := fun _ r => if r.val = 1 then some (0 : Fin 1) else none
  nsS := fun _ a b => (a.val = 0 ∧ b.val = 1) ∨ (a.val = 1 ∧ b.val = 2)
  nfS := fun _ r => r.val = 0
  smS := fun _ _ => 0
  dsS := fun _ _ => 1
  gcS := fun s _ => if s.val = 2 then (1 : Fin 3) else (0 : Fin 3)
  ltG := fun a b => a.val < b.val
  topG := 2
  tq := fun _ => Tq.quid
  mj := fun _ => Mj.razon
  ptc := fun _ => 1
  rc := fun c r => (c.val = 0 ∧ r.val ≤ 1) ∨ (c.val = 1 ∧ r.val = 2)
  Orr := fun c q => c.val = 0 ∧ q.val = 1
  Pre := fun _ a b => a.val = 0 ∧ b.val = 1
  ltE := fun s a b => s.val ≠ 0 ∧ a.val < b.val
  bas := fun _ => Bs.der
  co := fun c => some (if c.val = 0 then Ci.su else if c.val = 1 then Ci.op else Ci.don)
  rco := fun _ => none
  Mtf := fun s c => s.val ≠ 0 ∧ c.val ≤ 1
  lm := fun _ => Lm.lit
  dnR := fun _ => Dn.noc
  NomD := fun s c => s.val ≠ 0 ∧ 2 ≤ c.val
  sgN := fun c => if c.val = 3 then Sgn.sec else Sgn.prim
  fd := fun c => if c.val = 3 then some (2 : Fin 4) else none
  Sbs := fun s _ => s.val ≠ 0
  desS := fun _ g => g.val = 0
  indS := fun _ g => g.val = 1
  sigS := fun _ g => g.val = 0
  rr := fun e => e
  Req := fun _ _ => False
  Opp := fun _ _ => False
  Irr := fun _ _ => False
  Suc := fun s s' => s.val < s'.val
  ltEp := fun _ _ => False
  dvt := fun _ _ _ => False
  cadenaG := by unfold E6.IsChain; refine ⟨?_, ?_, ?_⟩ <;> decide
  top_max := by decide
  nu_sub := by decide
  ca_inc := by decide
  dcs_ne := by decide
  opp_symm := by decide
  opp_irrefl := by decide
  irr_opp := by decide
  suc_irrefl := by decide
  suc_trans := by decide
  dvt_suc := fun _ _ _ h => h.elim

/-! Instancias de decidibilidad para SummaZ. -/
instance (p : SummaZ.Sy → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : SummaZ.Sy → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : SummaZ.Sy) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : SummaZ.Cq → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : SummaZ.Cq → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : SummaZ.Cq) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : SummaZ.Rs → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : SummaZ.Rs → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : SummaZ.Rs) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : SummaZ.Gc → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : SummaZ.Gc → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : SummaZ.Gc) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : SummaZ.Epc → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : SummaZ.Epc → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : SummaZ.Epc) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : SummaZ.Dsp → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : SummaZ.Dsp → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : SummaZ.Dsp) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : SummaZ.Cn → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 4, p x))
instance (p : SummaZ.Cn → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 4, p x))
instance (a b : SummaZ.Cn) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 4) = b))
instance (p : SummaZ.Rl → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : SummaZ.Rl → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : SummaZ.Rl) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : SummaZ.Rsp → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : SummaZ.Rsp → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : SummaZ.Rsp) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : SummaZ.Sb → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : SummaZ.Sb → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : SummaZ.Sb) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : SummaZ.Sig → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : SummaZ.Sig → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : SummaZ.Sig) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : SummaZ.Ejm → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : SummaZ.Ejm → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : SummaZ.Ejm) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : SummaZ.Ct → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : SummaZ.Ct → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : SummaZ.Ct) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))

theorem summa_K6 : ∀ s : Fin 3, SummaZ.K6 s := by
  have key : ∀ r r' : Fin 3, r = r' ∨ SummaZ.symNs 0 r r' ∨ ∃ c, SummaZ.symNs 0 r c ∧ SummaZ.symNs 0 c r' := by
    decide
  intro s r r' _ _
  rcases key r r' with h | h | ⟨c, hc, hc'⟩
  · exact Or.inl h
  · exact Or.inr (E4.TG.base h)
  · exact Or.inr (E4.TG.step (E4.TG.base hc) hc')

theorem summa_K1 : ∀ s : Fin 3, SummaZ.K1 s := by decide
theorem summa_K2 : ∀ s : Fin 3, SummaZ.K2 s := by decide
theorem summa_K3 : ∀ s : Fin 3, SummaZ.K3 s := by decide
theorem summa_K4 : ∀ s : Fin 3, SummaZ.K4 s := by decide
theorem summa_K5 : ∀ s : Fin 3, SummaZ.K5 s := by decide
theorem summa_K7 : ∀ s : Fin 3, SummaZ.K7 s := by decide
theorem summa_K8 : ∀ s : Fin 3, SummaZ.K8 s := by decide
theorem summa_K9 : ∀ s : Fin 3, SummaZ.K9 s := by decide
theorem summa_K10 : ∀ s : Fin 3, SummaZ.K10 s := by decide
theorem summa_K12 : ∀ s : Fin 3, SummaZ.K12 s := by decide
theorem summa_K13 : ∀ s : Fin 3, SummaZ.K13 s := by decide
theorem summa_K11 : ∀ s : Fin 3, s.val ≠ 0 → SummaZ.K11 s := by decide

/-- El Scriptum no es adecuado: sus cuestiones no tienen orden (L11). -/
theorem summa_scriptum_no_adec : ¬ Adec SummaZ 0 := fun h => by
  have := h.L11.1 0 1 (by decide)
  exact absurd this (by decide)

theorem summa_Adec : ∀ s : Fin 3, s.val ≠ 0 → Adec SummaZ s := fun s hs =>
  ⟨summa_K1 s, summa_K2 s, summa_K3 s, summa_K4 s, summa_K5 s, summa_K6 s, summa_K7 s,
   summa_K8 s, summa_K9 s, summa_K10 s, summa_K11 s hs, summa_K12 s, summa_K13 s⟩

theorem summa_Posc : ∀ s : Fin 3, s.val ≠ 0 → Posc SummaZ s := fun s hs =>
  ⟨summa_Adec s hs, (show ∀ s : Fin 3, ∀ d, SummaZ.Dcs s d → E6.NiceaY.Ap (SummaZ.hzs s) d by decide) s,
   (show ∀ s : Fin 3, ∀ v, ¬ SummaZ.vnS s v by decide) s⟩

theorem summa_Contrap : SummaZ.Contrap 0 := fun h => summa_scriptum_no_adec h.toAdec

/-- E7(d₄) = {SCG IV, ST}; el Scriptum queda fuera de Sis. -/
theorem summa_E7_d4 : ∀ s : Fin 3, SummaZ.E7 4 s ↔ s.val ≠ 0 := by
  intro s; constructor
  · rintro ⟨_, hp⟩ h0
    have : s = 0 := Fin.ext h0
    subst this; exact summa_Contrap hp
  · intro hs; exact ⟨(show ∀ s : Fin 3, SummaZ.Dcs s 4 by decide) s, summa_Posc s hs⟩

theorem summa_Sis : ∀ s : Fin 3, SummaZ.Sis s ↔ s.val ≠ 0 := by
  intro s; constructor
  · rintro ⟨d, hd, hp⟩
    have hd4 : d.val = 4 := (show ∀ s : Fin 3, ∀ d : Fin 9, SummaZ.Dcs s d → d.val = 4 by decide) s d hd
    have : d = 4 := Fin.ext hd4
    subst this; exact (summa_E7_d4 s).1 ⟨hd, hp⟩
  · intro hs; exact ⟨4, (summa_E7_d4 s).2 hs⟩

theorem summa_Ley : Ley SummaZ where
  L15a := by decide
  L15b := fun s s' _ _ h => h
  L16a := by decide
  L16b := by
    intro s s' h _ _
    exact ⟨fun r _ => (show ∀ (s : Fin 3) (r : Fin 3), SummaZ.Rcub s r by decide) s' r,
      fun r _ => (show ∀ s s' : Fin 3, s.val < s'.val → ∀ r : Fin 3, SummaZ.leG (SummaZ.gcS s r) (SummaZ.gcS s' r) by decide) s s' h r⟩

/-- Sucesión Scriptum → SCG → ST (L16). -/
theorem summa_suc : SummaZ.Suc 0 1 ∧ SummaZ.Suc 1 2 ∧ SummaZ.Suc 0 2 := by decide

theorem Mod_noVacio_summa : ∃ Z : Mp E6.NiceaY, Ley Z := ⟨SummaZ, summa_Ley⟩

/-! ### Contraejemplos del caso (s = 1, la SCG IV) -/
theorem sbad_L10 : ¬ { SummaZ with sigS := fun _ _ => True }.K10 1 := by decide
theorem sbad_L10b : ¬ { SummaZ with desS := fun _ _ => True, sigS := fun _ g => g.val = 1 }.K10 1 := by decide
theorem sbad_L9fd : ¬ { SummaZ with fd := fun _ => none }.K9 1 := by decide
theorem sbad_L9co : ¬ { SummaZ with co := fun c => if c.val = 3 then none else SummaZ.co c }.K9 1 := by decide
theorem sbad_L7 : ¬ { SummaZ with dsS := fun _ _ => 0 }.K7 1 := by decide
theorem sbad_L5 : ¬ { SummaZ with anS := fun _ _ => none }.K5 1 := by decide
theorem sbad_L5nf : ¬ { SummaZ with nfS := fun _ _ => False }.K5 1 := by decide
theorem sbad_L12 : ¬ { SummaZ with Req := fun _ _ => True, cts := fun _ _ => True }.K12 1 := by decide
theorem sbad_L2 : ¬ { SummaZ with ptc := fun _ => 2 }.K2 1 := by decide
theorem sbad_L16 : ¬ (∀ r : Fin 3, { SummaZ with gcS := fun s _ => if s.val = 1 then (1 : Fin 3) else (0 : Fin 3) }.Rcub 1 r →
    { SummaZ with gcS := fun s _ => if s.val = 1 then (1 : Fin 3) else (0 : Fin 3) }.leG (1 : Fin 3) (0 : Fin 3)) := by decide

end Nicea
end E7
