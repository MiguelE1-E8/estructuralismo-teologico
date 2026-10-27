import E4
/-
  E5 · Fundamentos — verificación en Lean 4 (sin Mathlib, sin sorry).
  Traduce la tupla, Mp(E5), la ley (D1–D3, C1–C4) y el modelo actual (conversión ecológica).

  ESTADO (19 oct 2026). La versión del 14 oct (sin `met`) compiló sin errores ni `sorry` en Lean 4 web
  (v4.35), como parte de un único archivo con el subconjunto de E4.lean que E5 usa (este archivo es ese
  mismo bloque con `import E4`); quedaban solo avisos de nombres obsoletos (if_pos, if_neg) en la prueba
  de D2. La versión de hoy añade: `met` en Cs5 (E6 ya lo usa), las citas de este encabezado y de cada
  cláusula, y el teorema `Eco_pluralismo_radical`. Ningún nombre, campo ni orden de campos de `Mp` o
  `Ley` cambió. PENDIENTE: recompilar (Lean 4 web) y confirmar.

  Citas de Lonergan: Método en teología, Sígueme, Salamanca 1988, cap. 11 «Explicitación de los
  fundamentos» (pp. 261–285). Etiquetas, como en E4: [T] lo dice el texto (con página) · [L] lectura
  formal propia · [E] estipulación de modelado. Verificado ≠ auditado: Lean comprueba la consistencia
  del modelo; el vínculo con el texto es interpretación. Tabla completa en el apartado «Concordancia con
  el texto de Lonergan» del documento E5.
   - p. 261 [T] «La realidad fundante [...] es la conversión religiosa, moral e intelectual» → `pm`, `pp`, `Tp`.
   - p. 261 [T] E5 da «el fundamento suplementario indispensable para quien quiere pasar del discurso
     indirecto [...] al discurso directo» y es el de «estas tres últimas funciones» → E6, E7, E8 leen E5.
   - pp. 261–262 [T] «De ordinario, la conversión intelectual depende de la conversión moral y religiosa»;
     p. 276 [T] la religiosa «fundamenta la conversión intelectual y moral». NO es cláusula: E4 admite los
     ocho perfiles (Pc) porque el texto dice «de ordinario».
   - p. 262 [T] «la conversión es el paso de la inautenticidad a la autenticidad» → D1.
   - p. 262 [T] «el partido que toma dependerá del hecho de que se haya convertido o no» → D3.
   - p. 262 [T] decisión «acerca del propio horizonte, del propio punto de vista, de la propia visión del
     mundo»; escoge «el marco en el que las doctrinas cobrarán sentido» → `hzm`, `hzp`.
   - p. 263 [T] «un acontecimiento eminentemente personal, no es puramente privado» → `k5`.
   - p. 263 [T] quién fundó el grupo y qué servicios presta «pertenecen [...] a la sexta» → fuera de E5.
   - p. 264 [T] la triple conversión «no es un conjunto de proposiciones [...], sino un cambio fundamental
     y decisivo en la realidad humana del teólogo» → `Cv` son cambios del sujeto, no enunciados.
   - p. 264 [T] cambio de «los juicios básicos [...] que se descubren no ser posiciones sino
     contraposiciones» → las contraposiciones coherentes siguen en 𝔅 (E4), distinguidas por Pc.
   - p. 265 [T] «La conversión consiste justamente en pasar de un conjunto de raíces a otro» → `tr`, D2.
   - p. 265 [T] «horizontes radicalmente diferentes» → `pf`, C1.
   - pp. 265, 269 [T] pluralismo en la expresión de «una misma opción fundamental» (benigno, por la
     diferenciación) frente al «pluralismo radical» (presencia o ausencia de conversión) → `Df`,
     `Eco_pluralismo`, `Eco_pluralismo_radical`.
   - pp. 265–269 [T] campos de significación, 31 tipos de consciencia diferenciada (p. 266), grados
     «incipiente, madura, o regresiva» (p. 268), indiferenciada de «la inmensa mayoría de creyentes»
     (p. 269) → `Df`, `deg`.
   - p. 316 [T, por verificar] los siete campos (sentido común, transcendencia, belleza, sistema, método,
     erudición, interioridad) → `Cs5`; belleza (p. 267) y sistema (p. 269) apoyan arte y teo dentro del cap. 11.
   - pp. 275, 278–279 [T] categorías generales (base: «el teólogo particular que está haciendo teología»)
     y especiales → `CatG`, `CatS`; p. 283 [T] los cinco grupos → `gs`; p. 285 [T] origen, génesis, estado
     actual, transformaciones, adaptaciones → `Tm`.
   - pp. 277, 284 [T] las categorías se toman «únicamente como modelos»; su uso como hipótesis o
     descripciones (pp. 284–285) es de E6–E8 y la decisión es del teólogo (p. 278).
   - p. 283 [T] concepciones de existencia auténtica/inauténtica = cuarto grupo → C3 (`gs = 3`).
   - p. 284 [T] «no se puede esperar el descubrimiento de un criterio, de un test, o de un control
     “objetivo”» → `Aut` es un predicado primitivo; C4.

  Convenciones:
   - E5 se parametriza por un modelo M : E4.Mp PV I (un solo perfil de dialéctico).
     De E4 se usan, sin redefinir: Perfil, Base (= 𝔅), π, aprx (≈), prec (≺ = anterior),
     Pc, PosB, Yo, sost, ind, E4.TG, y los teoremas prec_Pc y Ley.L3a.
   - p⁻ = pm, p⁺ = pp (perfiles antes y después de la conversión); hz⁻ = hzm, hz⁺ = hzp.
   - Los cinco grupos de categorías especiales se numeran 0..4; el grupo 4 del texto es el índice 3.
   - Ω_aut es `Aut`; rep es parcial (Option).
   - ob_I, ob_H, Tem, Cv_I, Cv_H son lecturas del autor y quedan fuera de Mp y de la ley.
   - Consumidores: lean/E6.lean (`import E5`) lee Om, pf, Aut, Df, CatG, CatS, Cs5 (siete constructores),
     Esc, Gr5, tg_prec_Pc y los campos de Ley; las copias *_web de E6–E8 repiten `Mp`. No cambiar nombres
     ni orden de campos sin avisar a esas pestañas.
   - Retornos (ciclo/aristas_retorno.md, ciclo/e6_e5_restitucion.md; cap. 5 pp. 141–142 según esas notas):
     E5→E4 usa `pf (hzp c)` como índice q de la familia {E4_q}; E6→E5 (`RetornoE6E5.dim`) no determina
     `pf` ni `rep`. Ambos viven en Ciclo*, no en esta tupla.
-/
namespace E5
open E4 (Perfil Cs)

/-! ## Tipos enumerados -/
-- Esc: p. 263 [T] la conversión es «eminentemente personal» pero «no es puramente privado» (solo en el
-- grupo social); personal y comunitaria son [T]; histórica es [L] (cap. 5 y borrador).
inductive Esc | personal | comunitaria | historica deriving DecidableEq
-- Gr5: p. 268 [T] «Cada una de las precedentes diferenciaciones de la consciencia puede ser incipiente,
-- madura, o regresiva».
inductive Gr5 | incipiente | madura | regresiva deriving DecidableEq
/-- Campos de significación de E5 (sc = sentido común). Los cuatro de E4 (p. 265 [T] «el campo del sentido
    común, el campo de la teoría, el campo de la interioridad y el campo de la transcendencia») más
    «por motivos prácticos, el campo de la erudición y el del arte» (p. 265 [T]) y el método: los siete
    campos que Lonergan lista en la p. 316 [T, por verificar] (teo = sistema; arte = belleza, cf. p. 267
    «el campo de la belleza» y p. 269 «teología sistemática»). El sentido común siempre opera (pp. 265–266 [T]). -/
inductive Cs5 | sc | teo | int | tra | arte | erud | met deriving DecidableEq
-- Coord: p. 261 [T] conversión «religiosa, moral e intelectual»; i, m, r son las coordenadas de Pc (E4).
inductive Coord | i | m | r deriving DecidableEq

/-- Inclusión Cs ↪ Cs5. -/
def Cs5.ofCs : Cs → Cs5
  | .sentido_comun => .sc
  | .teoria => .teo
  | .interioridad => .int
  | .trascendencia => .tra

/-- Orden componente a componente en 𝒫 = {0,1}³ [L]: 1 = compatible con esa conversión (E4). -/
def leP (p q : Perfil) : Bool :=
  (!p.1 || q.1) && (!p.2.1 || q.2.1) && (!p.2.2 || q.2.2)

/-- p < q: ≤ en cada coordenada y distintos. -/
def ltP (p q : Perfil) : Prop := leP p q = true ∧ p ≠ q

instance (p q : Perfil) : Decidable (ltP p q) := by
  unfold ltP; exact inferInstance

theorem lt_exists_coord : ∀ p q : Perfil, ltP p q →
    (p.1 = false ∧ q.1 = true) ∨ (p.2.1 = false ∧ q.2.1 = true) ∨ (p.2.2 = false ∧ q.2.2 = true) := by
  intro ⟨p1, p2, p3⟩ ⟨q1, q2, q3⟩
  cases p1 <;> cases p2 <;> cases p3 <;> cases q1 <;> cases q2 <;> cases q3 <;> decide

/-! ## Modelo potencial Mp(E5): solo tipos -/
structure Mp {PV I : Type} (M : E4.Mp PV I) where
  -- conjuntos
  Cv : Type      -- conversiones: p. 264 [T] son «un cambio fundamental y decisivo en la realidad humana del teólogo», no proposiciones
  Om : Type      -- horizontes: p. 263 [T] «el propio punto de vista, la propia visión del mundo»; primitivo (no hay definición más fina)
  CatG : Type    -- categorías generales: p. 275 [T] las de «objetos pertenecientes tanto al dominio de la teología como de otras disciplinas»
  CatS : Type    -- categorías especiales: p. 275 [T] las de «los objetos propios de la teología»
  Orig : Type    -- Orig, Gen, Act, Trf, Ada: p. 285 [T] «los orígenes, [...] la génesis, [...] el estado actual, [...] las
  Gen : Type     --   transformaciones y posibles adaptaciones de estas categorías»
  Act : Type
  Trf : Type
  Ada : Type
  -- conversiones
  k5 : Cv → Esc                        -- p. 263 [T] personal / «no es puramente privado»; p. 263: solo dentro del grupo social
  pm : Cv → Perfil                     -- p⁻: p. 261 [T] conversión religiosa, moral e intelectual, tipada por Pc (E4) [L]
  pp : Cv → Perfil                     -- p⁺
  tr : Cv → Option (M.Base × M.Base)   -- p. 265 [T] «pasar de un conjunto de raíces a otro»; parcial: solo donde E4 da evidencia [L]
  cv : M.Yo → Option Cv                -- p. 262 [T] «Es la persona la que toma partido»; p. 278 [T] «el teólogo particular» (Θ := Yo de E4)
  -- horizontes
  hzm : Cv → Om                        -- hz⁻, hz⁺: p. 262 [T] decisión acerca «del propio horizonte»; p. 263 [T] conversión «algo más que un cambio de horizonte»
  hzp : Cv → Om
  pf : Om → Perfil                     -- p. 265 [T] convertido y no convertido «tienen horizontes radicalmente diferentes»
  ex : Cv → Om → Prop                  -- explicitación del horizonte: [E] construcción (el texto no dice cómo se calcula)
  Aut : Om → Prop                      -- Ω_aut: p. 284 [T] no hay «criterio, [...] test, o [...] control “objetivo”»: primitivo
  rep : Om → Option CatS               -- p. 283 [T] cuarto grupo: existencia «auténtica o inauténtica»; la asignación es [L]
  -- diferenciación de la consciencia
  Df : Om → Cs5 → Prop                 -- pp. 265–269 [T]; p. 266: 31 tipos con cinco campos diferenciables; Df ω = ∅ es la indiferenciada (p. 269)
  deg : Om → Cs5 → Option Gr5          -- p. 268 [T] incipiente, madura o regresiva
  -- categorías
  gs : CatS → Fin 5                    -- p. 283 [T] los cinco grupos de categorías especiales
  Tm : CatG ⊕ CatS → Orig × Gen × Act × Trf × Ada   -- p. 285 [T]
  -- condiciones de tipo
  Df_sc : ∀ w, ¬ Df w Cs5.sc           -- pp. 265–266 [T] «todo adulto normal opera en el campo del sentido común»: no es diferenciación
  deg_def : ∀ w x, (deg w x).isSome = true ↔ Df w x   -- [L] el grado solo existe donde hay diferenciación

namespace Mp
variable {PV I : Type} {M : E4.Mp PV I} (X : Mp M)

/-- Cv_D := dom(tr) -/
abbrev CvD (c : X.Cv) : Prop := (X.tr c).isSome = true

/-- Tp(c): coordenadas que cambian de 0 a 1 (tipo de conversión: intelectual, moral, religiosa). -/
def Tp (c : X.Cv) : Coord → Prop
  | .i => (X.pm c).1 = false ∧ (X.pp c).1 = true
  | .m => (X.pm c).2.1 = false ∧ (X.pp c).2.1 = true
  | .r => (X.pm c).2.2 = false ∧ (X.pp c).2.2 = true

/-- Aut(c) :⇔ hz⁺(c) ∈ Ω_aut -/
abbrev AutC (c : X.Cv) : Prop := X.Aut (X.hzp c)
end Mp

/-! ## La ley de E5: D1–D3 (dominio) y C1–C4 (codominio) -/
structure Ley {PV I : Type} {M : E4.Mp PV I} (X : Mp M) : Prop where
  /-- D1 [p. 262 T]: «la conversión es el paso de la inautenticidad a la autenticidad». Se lee sobre el
      perfil de E4: p⁻(c) < p⁺(c) [L]. Vale para cada conversión, no para la vida entera: p. 276 [T]
      «este apartarse nunca es total y permanece siempre precario» (la recaída no está excluida). -/
  D1 : ∀ c, ltP (X.pm c) (X.pp c)
  /-- D2 [p. 265 T + E4]: «La conversión consiste justamente en pasar de un conjunto de raíces a otro»
      (y la dialéctica «reduce» las diferencias de horizonte «a sus raíces»). tr(c) es un enlace ≈ (no ≺)
      entre una base de perfil p⁻ y otra de perfil p⁺ [L]; p. 276 [T] «su realización es dialéctica». -/
  D2 : ∀ c b b', X.tr c = some (b, b') →
        M.aprx b b' ∧ M.PosB (X.pm c) b ∧ M.PosB (X.pp c) b'
  /-- D3 [p. 262 T]: «Es la persona la que toma partido, y el partido que toma dependerá del hecho de que
      se haya convertido o no». Quien se ha convertido sostiene un punto de vista con el perfil posterior [L]. -/
  D3 : ∀ y c, X.cv y = some c → M.ind y (X.pp c)
  /-- C1 [p. 265 T]: «el convertido y el no-convertido tienen horizontes radicalmente diferentes». El perfil
      de un horizonte es el de la conversión que lo vive [L]. -/
  C1 : ∀ c, X.pf (X.hzm c) = X.pm c ∧ X.pf (X.hzp c) = X.pp c
  /-- C2 [E]: fidelidad débil (construcción): el texto no dice cómo se calcula la explicitación. -/
  C2 : ∀ c, X.ex c (X.hzp c)
  /-- C3 [p. 283 T]: «Un cuarto grupo de categorías resulta de la diferenciación»: existencia cristiana
      «auténtica o inauténtica». Las concepciones de conversión auténtica son del grupo 4 (índice 3) [L]. -/
  C3 : ∀ w a, X.rep w = some a → X.gs a = 3
  /-- C4 [p. 284 T, p. 283 T]: sin «criterio, [...] test, o [...] control “objetivo”» y con lo inauténtico
      que «parece auténtico» (p. 283): Ω_aut = dom(rep) ⊊ Ω [L]. -/
  C4a : ∀ w, X.Aut w ↔ (X.rep w).isSome = true
  C4b : ∃ w, ¬ X.Aut w

/-! ## Consecuencias generales -/
section Consecuencias
variable {PV I : Type} {M : E4.Mp PV I} {X : Mp M}

/-- ≺⁺ conserva Pc (por E4: ≺ conserva Pc). -/
theorem tg_prec_Pc (L : E4.Ley M) {x y : M.Base} (h : E4.TG M.prec x y) :
    ∀ {a b : PV}, M.Odl3 a → M.Odl3 b → M.π a = x → M.π b = y → M.Pc a = M.Pc b := by
  induction h with
  | base h' =>
    intro a b ha hb hx hy
    exact E4.prec_Pc L h' ha hb hx hy
  | step h1 h2 ih =>
    intro a b ha hb hx hy
    have h2' := h2
    obtain ⟨a', b', ha', hb', hx', hy', hr⟩ := h2
    have e1 := ih ha ha' hx hx'
    have e2 := E4.prec_Pc L h2' ha' hb hx' hy
    exact e1.trans e2

/-- [L] Consecuencia de D1 y D2 con la ley de E4: una conversión de la dialéctica no es sucesión genética
    (p. 265 T «pasar de un conjunto de raíces a otro»; p. 276 T «su realización es dialéctica»). -/
theorem tr_no_prec_plus (L : E4.Ley M) (LX : Ley X) {c : X.Cv} {b b' : M.Base}
    (h : X.tr c = some (b, b')) : ¬ E4.TG M.prec b b' := by
  intro ht
  obtain ⟨_, ⟨a, ha, hab, hpa⟩, ⟨a', ha', hab', hpa'⟩⟩ := LX.D2 c b b' h
  have e := tg_prec_Pc L ht ha ha' hab hab'
  exact (LX.D1 c).2 (hpa.symm.trans (e.trans hpa'))

/-- [L] Toda conversión cambia al menos una coordenada del perfil: Tp(c) ≠ ∅ (p. 261 T conversión «religiosa,
    moral e intelectual»; D1 asegura que alguna de las tres cambia). -/
theorem Tp_nonempty (LX : Ley X) (c : X.Cv) : ∃ k, X.Tp c k := by
  rcases lt_exists_coord _ _ (LX.D1 c) with h | h | h
  · exact ⟨.i, h⟩
  · exact ⟨.m, h⟩
  · exact ⟨.r, h⟩

/-- [L] La conversión es cambio de horizonte: hz⁻(c) ≠ hz⁺(c) (p. 263 T: es «algo más que un cambio de
    horizonte», no menos). Se deduce de C1 y D1; no se postula. -/
theorem hz_distinct (LX : Ley X) (c : X.Cv) : X.hzm c ≠ X.hzp c := by
  intro h
  have h1 := (LX.C1 c).1
  have h2 := (LX.C1 c).2
  rw [h] at h1
  exact (LX.D1 c).2 (h1.symm.trans h2)
end Consecuencias

/-! ## Modelo actual: la conversión ecológica
  [E] Todos los valores de este modelo (perfiles, horizontes, ex, rep, Df, deg) son estipulaciones para
  comprobar que la ley es satisfacible; no afirman qué horizontes son auténticos (p. 284 T: no hay criterio
  objetivo) ni son un veredicto histórico. Fuentes del caso: Laudato si’ (217–219, números por verificar
  salvo el 5) y el mensaje de León XIV del 15 ago 2026 (vatican.va, texto oficial).
  PV (7): t₁,t₂,t₃ = 0,1,2 (técnica autónoma); i₁,i₂,i₃,i₄ = 3,4,5,6 (ecología integral).
  Ítems I = Fin 7 (uno por punto de vista; V i p := i = p). Bases: b_tec = 0, b_int = 1, b_int⁺ = 2.
  Perfiles: t_k ↦ (1,0,0); i_k ↦ (1,1,1).
  Cv (4): c₁ personal, c₂ comunitaria, c₃ histórica, c₄ comunitaria hipotética.
  Ω (5): ω_tec, ω_cat, ω_ort, ω_mis, ω_ins = 0..4. 𝒜 = {a₁, a₂} (grupo 4), s₅ (grupo 5). -/
section Eco

def ecoRel : List (Nat × Nat × E4.Rel) :=
  [(0,1,.complementaria),(1,2,.complementaria),(0,2,.complementaria),
   (3,4,.complementaria),(4,5,.complementaria),(3,5,.complementaria),
   (3,6,.anterior),(4,6,.anterior),(5,6,.anterior),
   (0,3,.irreductible),(0,4,.irreductible),(0,5,.irreductible),(0,6,.irreductible),
   (1,3,.irreductible),(1,4,.irreductible),(1,5,.irreductible),(1,6,.irreductible),
   (2,3,.irreductible),(2,4,.irreductible),(2,5,.irreductible),(2,6,.irreductible)]

/-- Toda pareja comparada es una discrepancia de horizonte (raíz única z₀). -/
def ecoDsc : List (Nat × Nat × Nat) := ecoRel.map (fun t => (t.1, t.2.1, 0))

/-- El E4 del caso (perfil único). -/
abbrev EcoE4 : E4.Mp (Fin 7) (Fin 7) where
  CT := Bool
  Ep := Bool
  Mf := Bool
  Et := Bool
  Vr := Bool
  car := fun p => ((true, true, true), decide (3 ≤ p.val), decide (3 ≤ p.val))
  cvi := fun x => decide (x = (true, true, true))
  cvm := fun b => b
  cvr := fun b => b
  sgE := fun c e => c = e
  sgM := fun x m => x.1 = m
  Odl3 := fun p => p.val < 7
  rel := fun a b => E4.mkRel ecoRel a.val b.val
  Dsc := fun a b => E4.inT ecoDsc a.val b.val = true
  Afn := fun a b => E4.inT [] a.val b.val = true
  Rz := Fin 1
  red := fun _ _ => 0
  cls := fun _ o => o = E4.Op.horizonte
  ot := fun _ _ o => o = E4.Op.horizonte
  V := fun i p => i.val = p.val
  Va := Fin 1
  vl4 := fun _ _ => False
  sgV := fun _ => true
  Yo := Fin 2
  sost := fun y p => (y.val, p.val) ∈ [(0, 3), (0, 5), (1, 0)]
  df := fun _ _ => False
  Base := Fin 3
  π := fun p => if p.val < 3 then 0 else if p.val < 6 then 1 else 2
  dsc_afn_disj := by decide
  cls_ne := fun _ => ⟨E4.Op.horizonte, rfl⟩

theorem EcoE4_ley : E4.Ley EcoE4 where
  L1 := by decide
  L2 := by decide
  L3a := by decide
  L3b := by
    intro a b ha hb
    constructor
    · intro h
      have key : ∀ a b : Fin 7, EcoE4.Odl3 a → EcoE4.Odl3 b → EcoE4.π a = EcoE4.π b →
          b ∈ E4.reach EcoE4 a 7 := by decide
      exact E4.reach_sound EcoE4 a ha 7 b (key a b ha hb h)
    · exact E4.EqC_pi EcoE4 (by decide)
  L6a := by decide
  L6b := by decide
  L6c := E4.TG.irrefl_of_rank _ (fun x => x.val) (by decide)
  L7 := by
    have key : ∀ a b : Fin 7, (EcoE4.rel a b).isSome → EcoE4.rel a b ≠ some E4.Rel.irreductible →
        EcoE4.Pc a = EcoE4.Pc b := by decide
    intro a b r hr hne
    have hs : (EcoE4.rel a b).isSome = true := by rw [hr]; rfl
    exact key a b hs (by rw [hr]; intro h; exact hne (Option.some.inj h))
  L9 := fun _ _ _ => Iff.rfl
  L10 := by decide

/-- E5 del caso. -/
abbrev EcoX : Mp EcoE4 where
  Cv := Fin 4
  Om := Fin 5
  CatG := Fin 1
  CatS := Fin 3
  Orig := Unit
  Gen := Unit
  Act := Unit
  Trf := Unit
  Ada := Unit
  k5 := fun c => if c.val = 0 then Esc.personal else if c.val = 2 then Esc.historica else Esc.comunitaria
  pm := fun _ => (true, false, false)
  pp := fun c => if c.val = 3 then (true, true, false) else (true, true, true)
  tr := fun c => if c.val = 1 ∨ c.val = 2 then some (0, 1) else none
  cv := fun y => if y.val = 0 then some 0 else none
  hzm := fun _ => 0
  hzp := fun c => if c.val = 3 then 4 else 1
  pf := fun w => if w.val = 0 then (true, false, false) else if w.val = 4 then (true, true, false)
                 else (true, true, true)
  ex := fun c w => (c.val ≤ 1 ∧ (w.val = 1 ∨ w.val = 2 ∨ w.val = 4)) ∨
                   (c.val = 2 ∧ (w.val = 1 ∨ w.val = 2)) ∨
                   (c.val = 3 ∧ (w.val = 4 ∨ w.val = 1))
  Aut := fun w => w.val = 1 ∨ w.val = 2 ∨ w.val = 3
  rep := fun w => if w.val = 1 ∨ w.val = 3 then some 0 else if w.val = 2 then some 1 else none
  Df := fun w x => (w.val = 0 ∧ x = Cs5.teo) ∨ (w.val = 1 ∧ x = Cs5.teo) ∨
                   (w.val = 2 ∧ (x = Cs5.tra ∨ x = Cs5.arte)) ∨ (w.val = 3 ∧ x = Cs5.tra)
  deg := fun w x =>
    if w.val = 3 ∧ x = Cs5.tra then some Gr5.incipiente
    else if (w.val = 0 ∧ x = Cs5.teo) ∨ (w.val = 1 ∧ x = Cs5.teo) ∨
            (w.val = 2 ∧ (x = Cs5.tra ∨ x = Cs5.arte)) then some Gr5.madura
    else none
  gs := fun a => if a.val = 2 then 4 else 3
  Tm := fun _ => ((), (), (), (), ())
  Df_sc := by decide
  deg_def := by
    intro w x
    cases x <;> revert w <;> decide

theorem EcoX_ley : Ley EcoX where
  D1 := by decide
  D2 := by
    -- Prueba manual: `decide` no sintetiza la decidibilidad del enunciado completo.
    have hA : EcoE4.aprx (0 : Fin 3) 1 :=
      ⟨0, 3, by decide, by decide, by decide, by decide, by decide⟩
    have hP0 : EcoE4.PosB (true, false, false) (0 : Fin 3) :=
      ⟨0, by decide, by decide, by decide⟩
    have hP1 : EcoE4.PosB (true, true, true) (1 : Fin 3) :=
      ⟨3, by decide, by decide, by decide⟩
    intro c b b' h
    have h' : (if c.val = 1 ∨ c.val = 2 then some ((0 : Fin 3), (1 : Fin 3)) else none)
        = some (b, b') := h
    by_cases hc : c.val = 1 ∨ c.val = 2
    · rw [if_pos hc] at h'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
      have h3 : ¬ c.val = 3 := by omega
      have hpp : EcoX.pp c = (true, true, true) := by
        show (if c.val = 3 then (true, true, false) else (true, true, true)) = _
        rw [if_neg h3]
      refine ⟨hA, hP0, ?_⟩
      rw [hpp]
      exact hP1
    · rw [if_neg hc] at h'
      cases h'
  D3 := by decide
  C1 := by decide
  C2 := by decide
  C3 := by decide
  C4a := by decide
  C4b := ⟨0, by decide⟩

/-! ### Lo que muestra el modelo -/

/-- Mod(E5) ≠ ∅: el modelo actual satisface la ley, sobre un E4 que satisface la suya. -/
theorem Mod_noVacio : ∃ (M : E4.Mp (Fin 7) (Fin 7)) (_ : E4.Ley M) (X : Mp M), Ley X :=
  ⟨EcoE4, EcoE4_ley, EcoX, EcoX_ley⟩

/-- Derivado: las conversiones c₂ y c₃ (en la dialéctica) no son sucesión genética. -/
theorem Eco_no_prec : ¬ E4.TG EcoE4.prec 0 1 :=
  tr_no_prec_plus EcoE4_ley EcoX_ley (c := 1) (by decide)

/-- Tipos: c₁, c₂, c₃ son conversión moral y religiosa; c₄ solo moral. -/
theorem Eco_Tp :
    (EcoX.Tp 0 .m ∧ EcoX.Tp 0 .r ∧ ¬ EcoX.Tp 0 .i) ∧ (EcoX.Tp 3 .m ∧ ¬ EcoX.Tp 3 .r) := by
  simp only [Mp.Tp]
  decide

/-- c₄: el perfil sube pero el horizonte no es auténtico (el perfil describe el punto de vista;
    la autenticidad vivida es otro plano). p. 283 T: «lo que parece auténtico a un hombre o a un cristiano
    inauténtico, es precisamente lo inauténtico»; p. 263 T: distinguir la conversión auténtica de la
    inauténtica «por sus frutos» exige «una profunda seriedad y una sabiduría madura». [L] -/
theorem Eco_c4 : ltP (EcoX.pm 3) (EcoX.pp 3) ∧ ¬ EcoX.AutC 3 := by decide

/-- No trivialidad 1: rep no es inyectiva. -/
theorem Eco_rep_noinj :
    ∃ w w' : Fin 5, w ≠ w' ∧ EcoX.rep w = EcoX.rep w' ∧ (EcoX.rep w).isSome = true :=
  ⟨1, 3, by decide⟩

/-- No trivialidad 2 (p. 265 T): «un pluralismo en la expresión de una misma opción fundamental» y «una
    multiplicidad de teologías que expresan la misma fe»: mismo perfil, distinta diferenciación y distinta
    expresión. Es el pluralismo «más benigno» que se enraiza «en la diferenciación de la consciencia
    humana» (p. 269 T). -/
theorem Eco_pluralismo :
    ∃ w w' : Fin 5, EcoX.Aut w ∧ EcoX.Aut w' ∧ EcoX.pf w = EcoX.pf w' ∧
      (∃ x, EcoX.Df w x ∧ ¬ EcoX.Df w' x) ∧ EcoX.rep w ≠ EcoX.rep w' :=
  ⟨1, 2, by decide, by decide, by decide, ⟨Cs5.teo, by decide⟩, by decide⟩

/-- No trivialidad 3 (p. 269 T): «el pluralismo radical que resulta de la presencia o ausencia de la
    conversión intelectual, moral, o religiosa»: hay horizontes de perfil distinto (ω_tec y ω_cat). Es el
    contraste con `Eco_pluralismo`, donde el perfil es el mismo. [L] -/
theorem Eco_pluralismo_radical : ∃ w w' : Fin 5, EcoX.pf w ≠ EcoX.pf w' :=
  ⟨0, 1, by decide⟩

/-! ### Mp ⊋ Mod: modelos bien tipados que violan una cláusula
  Un modelo negativo por cláusula (D1–D3, C1–C4), como en E4 y E6: es un `Mp` bien tipado, obtenido
  de `EcoX` cambiando lo mínimo, para el cual la cláusula falla. Que cada uno cumple TODAS las demás
  cláusulas (la cláusula es independiente) se comprobó con `check_neg.py`, no en Lean; aquí se prueba
  solo `¬ Ley`. [L] Lectura de cada violación:
   - D1: un cambio que no va de la inautenticidad a la autenticidad (p. 262).
   - D2: la «conversión» es una sucesión genética (b_int → b_int⁺), no «pasar de un conjunto de raíces a otro» (p. 265).
   - D3: un teólogo «convertido» que solo sostiene puntos de vista del perfil anterior (p. 262).
   - C1: horizontes que no distinguen el perfil, contra «horizontes radicalmente diferentes» (p. 265).
   - C2: una explicitación que no alcanza el horizonte de llegada [E].
   - C3: una concepción de conversión auténtica clasificada fuera del cuarto grupo (p. 283).
   - C4a: autenticidad y concepción desacopladas: un horizonte con concepción que no es auténtico.
   - C4b: todo horizonte es auténtico, contra «auténtica o inauténtica» (p. 283) y «lo que parece
     auténtico a [...] un cristiano inauténtico, es precisamente lo inauténtico». -/

/-- D1 falla: perfil y horizonte no cambian (y sin traza). -/
abbrev NegD1 : Mp EcoE4 :=
  { EcoX with pm := EcoX.pp, hzm := EcoX.hzp, tr := fun _ => none }
theorem NegD1_no_ley : ¬ Ley NegD1 := by
  intro L
  exact (L.D1 0).2 rfl

/-- D2 falla: la traza de c₂ y c₃ es (b_int, b_int⁺), un par de ≺ y no de ≈. -/
abbrev NegD2 : Mp EcoE4 :=
  { EcoX with tr := fun c => if c.val = 1 ∨ c.val = 2 then some (1, 2) else none }
theorem NegD2_no_ley : ¬ Ley NegD2 := by
  intro L
  have key : ¬ EcoE4.aprx (1 : Fin 3) 2 := by decide
  exact key (L.D2 1 1 2 (by decide)).1

/-- D3 falla: y₂ (que solo sostiene t₁, de perfil (1,0,0)) pasa por convertido en c₁. -/
abbrev NegD3 : Mp EcoE4 := { EcoX with cv := fun _ => some 0 }
theorem NegD3_no_ley : ¬ Ley NegD3 := by
  intro L
  exact absurd (L.D3 1 0 rfl) (by decide)

/-- C1 falla: todos los horizontes tienen el perfil (1,1,1). -/
abbrev NegC1 : Mp EcoE4 := { EcoX with pf := fun _ => (true, true, true) }
theorem NegC1_no_ley : ¬ Ley NegC1 := by
  intro L
  exact absurd (L.C1 0).1 (by decide)

/-- C2 falla: la explicitación es vacía. -/
abbrev NegC2 : Mp EcoE4 := { EcoX with ex := fun _ _ => False }
theorem NegC2_no_ley : ¬ Ley NegC2 := fun L => L.C2 0

/-- C3 falla: las concepciones de conversión auténtica se clasifican en el grupo 5 (índice 4). -/
abbrev NegC3 : Mp EcoE4 := { EcoX with gs := fun _ => 4 }
theorem NegC3_no_ley : ¬ Ley NegC3 := by
  intro L
  exact absurd (L.C3 1 0 (by decide)) (by decide)

/-- C4 (parte a) falla: ω_mis tiene concepción (rep) pero no es auténtico. -/
abbrev NegC4a : Mp EcoE4 := { EcoX with Aut := fun w => w.val = 1 ∨ w.val = 2 }
theorem NegC4a_no_ley : ¬ Ley NegC4a := by
  intro L
  have h : (3 : Fin 5).val = 1 ∨ (3 : Fin 5).val = 2 := (L.C4a 3).2 (by decide)
  revert h
  decide

/-- C4 (parte b) falla: todo horizonte es auténtico (y tiene concepción). -/
abbrev NegC4b : Mp EcoE4 :=
  { EcoX with Aut := fun _ => True, rep := fun w => if w.val = 2 then some 1 else some 0 }
theorem NegC4b_no_ley : ¬ Ley NegC4b := by
  intro L
  obtain ⟨w, h⟩ := L.C4b
  exact h trivial

/-- Las siete cláusulas (ocho con C4a y C4b) son necesarias: ninguna se deduce de las demás por tipo. -/
theorem Mp_ne_Mod :
    ¬ Ley NegD1 ∧ ¬ Ley NegD2 ∧ ¬ Ley NegD3 ∧ ¬ Ley NegC1 ∧ ¬ Ley NegC2 ∧ ¬ Ley NegC3 ∧
    ¬ Ley NegC4a ∧ ¬ Ley NegC4b :=
  ⟨NegD1_no_ley, NegD2_no_ley, NegD3_no_ley, NegC1_no_ley, NegC2_no_ley, NegC3_no_ley,
   NegC4a_no_ley, NegC4b_no_ley⟩

end Eco
end E5
