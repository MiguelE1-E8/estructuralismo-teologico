import E5
/-
  E6 · Establecimiento de las doctrinas — verificación en Lean 4 (sin Mathlib, sin sorry).
  Traduce la tupla, Mp(E6), la ley (L1–L14) y el modelo actual Nicea–Constantinopla III.

  Convenciones:
   - E6 se parametriza por M : E4.Mp PV I y X : E5.Mp M. De E4 se usan, sin redefinir: Perfil, Odl3,
     Pc, π, PosB, aprx (≈), prec (≺), E4.TG y prec_Pc (vía E5.tg_prec_Pc). De E5: Om (= Ω), pf, Aut,
     Df, Cs5, CatG, CatS. Ω y Dc son tipos distintos: Ω ∩ Dc = ∅ por tipado.
   - `en` = «in» (el enunciado se sostiene en el contexto), `ant` = ⊏, `sle` = ⊑, `nu` = ν.
   - Propiedades fuera de la ley (Perm, Hist, Clas) y el estatuto de las categorías (`st`) no entran a Ley.
   - Los derivados (Le, Gnt, DiaH, DesP, DesM, Pos, Contra, At, Est = E6(ω), Rt) son `abbrev`.

  Actualización 19-oct-2026 (E6 en el ciclo; sin cambios en la ley L1–L14):
   - Renombres de `ciclo/renombres_enlaces_y_cierre_E0-E8.md` (filas 1, 19 y 20) aplicados a E6:
       tr → trt (tratados; el `tr` de E5 —enlace ≈ de la conversión— se queda), tr_ne → trt_ne,
       Gen → Gnt (sucesión genética; `Gen` de E5 es otro conjunto), md → mdd, md_def → mdd_def.
     `sg` se queda (fila 2: el de E3 pasó a `sus`). Los nombres de teoremas (gen_pf, desP_gen,
     no_gen_conversion, Nicea_no_gen) no cambian.
     Los archivos que usen `Y.md`, `Y.tr`, `E6.Gen` o construyan `E6.Mp` con `md := …`/`tr := …`
     (p. ej. las copias del caso en `CicloNicea` y su cadena, `CicloF5`: `nicea38.Y.md 0 1`)
     deben seguir el renombre.
   - Reciprocidad intrafase de la fase 2 (Lonergan, cap. 5 §V, pp. 139–143, según `ciclo/e6_e5_restitucion.md`):
     «Hay, pues, una dependencia recíproca dentro de cada una de las dos fases»; la conversión
     «formulada como horizonte de fundamentación, tiene dimensiones no sólo personales, sino también
     sociales y doctrinales» (E6→E5). Esa arista no vive en esta tupla (los enlaces viven en `Ciclo*`:
     `RetornoE6E5`, relación `dim : Ω → Dc → Prop`); aquí la respalda L14: sólo un horizonte auténtico
     con conversión plena aprehende realmente una doctrina (`Ap`).
   - Citas del cap. 12 que respaldan cada cláusula (páginas de la edición de Sígueme, 1988): ver los
     comentarios de `Ley` y el Doc «E6 · Establecimiento de las doctrinas (versión ampliada)».
-/
namespace E6
open E4 (Perfil)
open E5 (Cs5)

/-! ## Tipos enumerados -/
inductive Cl | mo | rel | ig | te | me deriving DecidableEq
inductive Fn | com | efi | cog | coni | conc | nor deriving DecidableEq
inductive Tr | vr | ld | ec | is | lt deriving DecidableEq
inductive Kc | mat | frm | evo deriving DecidableEq
inductive Md | sim | fil | uso | tsi | ecl | mod | dia | nt deriving DecidableEq
inductive Es | mod | hip | des deriving DecidableEq

def IsChain {α : Type} (lt : α → α → Prop) : Prop :=
  (∀ a, ¬ lt a a) ∧ (∀ a b c, lt a b → lt b c → lt a c) ∧ (∀ a b, a ≠ b → lt a b ∨ lt b a)

/-- fld: los campos de significación que presupone cada modo de desarrollo (lectura del autor). -/
def fld : Md → Cs5 → Prop
  | .sim, x => x = .arte
  | .fil, x => x = .teo
  | .uso, x => x = .teo
  | .tsi, x => x = .teo
  | .ecl, x => x = .teo
  | .mod, x => x = .int ∨ x = .erud ∨ x = .met
  | .dia, _ => False
  | .nt, _ => False

instance (m : Md) (x : Cs5) : Decidable (fld m x) := by
  cases m <;> simp only [fld] <;> infer_instance

instance decAllCs5 (p : Cs5 → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p .sc ∧ p .teo ∧ p .int ∧ p .tra ∧ p .arte ∧ p .erud ∧ p .met) (by
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩ x; cases x <;> assumption
    · intro h; exact ⟨h _, h _, h _, h _, h _, h _, h _⟩)

instance decAllMd (p : Md → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p .sim ∧ p .fil ∧ p .uso ∧ p .tsi ∧ p .ecl ∧ p .mod ∧ p .dia ∧ p .nt) (by
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ x; cases x <;> assumption
    · intro h; exact ⟨h _, h _, h _, h _, h _, h _, h _, h _⟩)

/-! ## Relaciones sobre Ω inducidas por E4 (derivadas) -/
section Rel
variable {PV I : Type} {M : E4.Mp PV I}

/-- Gnt(ω,ω′): sucesión genética entre las bases con posición del perfil de cada horizonte. -/
abbrev Gnt (X : E5.Mp M) (w w' : X.Om) : Prop :=
  ∃ b b', M.PosB (X.pf w) b ∧ M.PosB (X.pf w') b' ∧ E4.TG M.prec b b'

/-- Dia(ω,ω′): enlace ≈ entre las bases con posición del perfil de cada horizonte. -/
abbrev DiaH (X : E5.Mp M) (w w' : X.Om) : Prop :=
  ∃ b b', M.PosB (X.pf w) b ∧ M.PosB (X.pf w') b' ∧ M.aprx b b'

end Rel

/-! ## Modelo potencial Mp(E6): tipos -/
structure Mp {PV I : Type} {M : E4.Mp PV I} (X : E5.Mp M) where
  -- conjuntos
  Dc : Type
  Au : Type
  Nt : Type
  Ctx : Type
  Fo : Type
  Sg : Type
  -- clases, funciones, tratados, notas
  cl : Dc → Cl
  au0 : Cl → Au
  fn : Dc → Fn → Prop
  trt : Dc → Tr → Prop
  nt : Dc → Option Nt
  ltNt : Nt → Nt → Prop
  Dep : Dc → Dc → Prop
  -- contextos, significación, expresión
  tc : Ctx → Kc
  en : Dc → Ctx → Prop
  sg : Dc → Ctx → Option Sg
  fo : Dc → Fo
  cd : Dc → Ctx
  ant : Ctx → Ctx → Prop
  Dv : Ctx → Ctx → Prop
  It : Ctx → Ctx → Prop
  sle : Sg → Sg → Prop
  -- desarrollos
  Dsr : Dc → Dc → Prop
  mdd : Dc → Dc → Option Md
  hz : Dc → Option X.Om
  Ctp : Dc → Dc → Prop
  rq : Ctx → Cs5 → Prop
  nu : Dc → PV → Prop
  -- aprehensión y estatuto de las categorías
  Ap : X.Om → Dc → Prop
  Apn : X.Om → Dc → Prop
  st : X.Om → X.CatG ⊕ X.CatS → Es
  -- condiciones de tipo
  trt_ne : ∀ d, ∃ t, trt d t
  sg_def : ∀ d c, (sg d c).isSome = true ↔ en d c
  mdd_def : ∀ d d', (mdd d d').isSome = true ↔ Dsr d d'
  nt_def : ∀ d, (nt d).isSome = true ↔ (cl d = Cl.ig ∨ cl d = Cl.te)
  cadena_Nt : IsChain ltNt

namespace Mp
variable {PV I : Type} {M : E4.Mp PV I} {X : E5.Mp M} (Y : Mp X)

/-- Le(ω,c): el horizonte ω está diferenciado en todos los campos que exige el contexto c. -/
abbrev Le (w : X.Om) (c : Y.Ctx) : Prop := ∀ x, Y.rq c x → X.Df w x

/-- Des⁺: desarrollo guiado por conversión (el horizonte de formulación del resultado tiene pf = (1,1,1)). -/
abbrev DesP (d d' : Y.Dc) : Prop :=
  Y.Dsr d d' ∧ ∃ w, Y.hz d' = some w ∧ X.pf w = (true, true, true)
/-- Des⁻: desarrollo evaluado cuyo horizonte de formulación no es (1,1,1). -/
abbrev DesM (d d' : Y.Dc) : Prop :=
  Y.Dsr d d' ∧ ∃ w, Y.hz d' = some w ∧ X.pf w ≠ (true, true, true)

/-- Pos_ω(d): todos los puntos de vista que d expresa son coherentes y de perfil pf ω. -/
abbrev Pos (w : X.Om) (d : Y.Dc) : Prop :=
  (∃ p, Y.nu d p) ∧ ∀ p, Y.nu d p → M.Odl3 p ∧ M.Pc p = X.pf w
abbrev Contra (w : X.Om) (d : Y.Dc) : Prop :=
  (∃ p, Y.nu d p) ∧ ¬ (∀ p, Y.nu d p → M.Odl3 p ∧ M.Pc p = X.pf w)

/-- At(ω,d): aprehensión teológica (histórica y dialéctica). -/
abbrev At (w : X.Om) (d : Y.Dc) : Prop :=
  (∃ p, Y.nu d p) ∧ ∀ c, Y.en d c → Y.Le w c

/-- E6(ω): doctrinas que se establecen desde el horizonte ω. -/
abbrev Est (w : X.Om) (d : Y.Dc) : Prop := Y.cl d = Cl.te ∧ Y.At w d ∧ Y.Pos w d
/-- Rt(ω): doctrinas que se hace retroceder. -/
abbrev Rt (w : X.Om) (d : Y.Dc) : Prop := Y.cl d = Cl.te ∧ Y.At w d ∧ Y.Contra w d

/-- Propiedades fuera de la ley (fase 3). -/
abbrev Perm (d : Y.Dc) : Prop :=
  ∀ c s s', Y.ant (Y.cd d) c → Y.sg d (Y.cd d) = some s → Y.sg d c = some s' → Y.sle s s'
abbrev Hist (d : Y.Dc) : Prop :=
  ∃ c c' s s', Y.sg d c = some s ∧ Y.sg d c' = some s' ∧ s ≠ s'
abbrev Clas (d : Y.Dc) : Prop :=
  ∀ c c' s s', Y.sg d c = some s → Y.sg d c' = some s' → s = s'

end Mp

/-! ## La ley de E6: L1–L14 -/
structure Ley {PV I : Type} {M : E4.Mp PV I} {X : E5.Mp M} (Y : Mp X) : Prop where
  /-- L1 [p. 287]: la autoridad distingue las clases. «Es común a todas ellas el ser enseñadas. Difieren y se distinguen entre sí por la autoridad con que las enseñan sus maestros.» -/
  L1 : ∀ a b, Y.au0 a = Y.au0 b → a = b
  /-- L2 [p. 291]: toda doctrina teológica depende de una que no lo es. -/
  L2 : (∀ d, Y.cl d = Cl.te → ∃ d', (Y.cl d' = Cl.mo ∨ Y.cl d' = Cl.rel ∨ Y.cl d' = Cl.ig) ∧ Y.Dep d d') ∧
       (∀ d d', Y.Dep d d' → Y.cl d = Cl.te ∧ (Y.cl d' = Cl.mo ∨ Y.cl d' = Cl.rel ∨ Y.cl d' = Cl.ig))
  /-- L3 [p. 290]: la doctrina común cumple las cuatro funciones de la significación. -/
  L3 : ∀ d, (Y.cl d = Cl.mo ∨ Y.cl d = Cl.rel ∨ Y.cl d = Cl.ig) →
        Y.fn d Fn.com ∧ Y.fn d Fn.efi ∧ Y.fn d Fn.cog ∧ Y.fn d Fn.coni ∧ Y.fn d Fn.conc
  /-- L4 [pp. 290–291]: la normatividad viene del método basado en la conversión. «Otra especialización funcional, la explicitación de los fundamentos, permite discriminar la verdad del error haciendo apelación a esa realidad fundante que es la conversión intelectual, moral y religiosa. El resultado de dicha discriminación es la especialización funcional que llamamos establecimiento de las doctrinas.» -/
  L4 : ∀ d, Y.fn d Fn.nor ↔ ∃ w, X.pf w = (true, true, true) ∧ Y.Est w d
  /-- L5 [p. 314]: la doctrina se sostiene en su contexto de definición. -/
  L5 : ∀ d, Y.en d (Y.cd d)
  /-- L6 [pp. 303–304]: anterior/posterior es un orden parcial estricto sobre los contextos evolutivos. -/
  L6 : (∀ c, ¬ Y.ant c c) ∧ (∀ a b c, Y.ant a b → Y.ant b c → Y.ant a c) ∧
       (∀ a b, Y.ant a b → Y.tc a = Kc.evo ∧ Y.tc b = Kc.evo)
  /-- L7 [pp. 304–305]: derivación asimétrica; interacción simétrica. -/
  L7 : (∀ a, ¬ Y.Dv a a) ∧ (∀ a b, Y.Dv a b → ¬ Y.Dv b a) ∧
       (∀ a b, Y.It a b → Y.It b a) ∧ (∀ a, ¬ Y.It a a)
  /-- L8 [p. 314]: «comprende al menos» es un preorden. -/
  L8 : (∀ s, Y.sle s s) ∧ (∀ a b c, Y.sle a b → Y.sle b c → Y.sle a c)
  /-- L9 [pp. 294, 304]: un desarrollo va de un contexto anterior a uno posterior o derivado. -/
  L9 : ∀ d d', Y.Dsr d d' → Y.ant (Y.cd d) (Y.cd d') ∨ Y.Dv (Y.cd d) (Y.cd d')
  /-- L10 [pp. 297, 309]: cada modo de desarrollo exige las diferenciaciones del contexto del resultado. -/
  L10 : ∀ d d' m, Y.mdd d d' = some m → ∀ x, fld m x → Y.rq (Y.cd d') x
  /-- L11 [p. 318]: el autor de la doctrina está diferenciado en lo que su contexto exige. -/
  L11 : ∀ d w, Y.hz d = some w → Y.Le w (Y.cd d)
  /-- L12 [p. 309]: el desarrollo dialéctico presupone una contraposición de horizonte ≈-enlazado. «Con frecuencia, el desarrollo es dialéctico: se descubre la verdad porque se ha afirmado un error contrario.» -/
  L12 : ∀ d d', Y.mdd d d' = some Md.dia →
        ∃ d'' w'' w', Y.Ctp d'' d' ∧ Y.hz d'' = some w'' ∧ Y.hz d' = some w' ∧ DiaH X w'' w'
  /-- L13 [cap. 10, p. 244]: lo real incluye lo nocional. -/
  L13 : ∀ w d, Y.Ap w d → Y.Apn w d
  /-- L14: la aprehensión real exige conversión plena y horizonte autentico. -/
  L14 : ∀ w d, Y.Ap w d → X.pf w = (true, true, true) ∧ X.Aut w

/-! ## Consecuencias generales -/
section General
variable {PV I : Type} {M : E4.Mp PV I} {X : E5.Mp M} {Y : Mp X}

/-- Autonomía [pp. 319–321]: lo que E6 establece o hace retroceder es teológico y depende de lo que no lo es. -/
theorem est_teologica (LY : Ley Y) {w : X.Om} {d : Y.Dc} (h : Y.Est w d) :
    Y.cl d = Cl.te ∧ ∃ d', (Y.cl d' = Cl.mo ∨ Y.cl d' = Cl.rel ∨ Y.cl d' = Cl.ig) ∧ Y.Dep d d' :=
  ⟨h.1, LY.L2.1 d h.1⟩

theorem est_no_eclesial (_LY : Ley Y) {w : X.Om} {d : Y.Dc} (h : Y.Est w d) :
    ¬ (Y.cl d = Cl.mo ∨ Y.cl d = Cl.rel ∨ Y.cl d = Cl.ig) := by
  rintro (h' | h' | h') <;> rw [h.1] at h' <;> cases h'

/-- La sucesión genética no cambia el perfil del horizonte. -/
theorem gen_pf (L : E4.Ley M) {w w' : X.Om} (h : Gnt X w w') : X.pf w = X.pf w' := by
  obtain ⟨b, b', ⟨a, ha, hab, hpa⟩, ⟨a', ha', hab', hpa'⟩, ht⟩ := h
  have e := E5.tg_prec_Pc L ht ha ha' hab hab'
  exact hpa.symm.trans (e.trans hpa')

/-- Si los horizontes de formulación están en sucesión genética, la legitimidad se hereda. -/
theorem desP_gen (L : E4.Ley M) {d d' : Y.Dc} {w w' : X.Om} (h : Y.Dsr d d')
    (_hz : Y.hz d = some w) (hz' : Y.hz d' = some w') (hg : Gnt X w w') :
    Y.DesP d d' ↔ X.pf w = (true, true, true) := by
  constructor
  · rintro ⟨_, v, hv, hp⟩
    have : w' = v := Option.some.inj (hz'.symm.trans hv)
    subst this
    exact (gen_pf L hg).trans hp
  · intro hp
    exact ⟨h, w', hz', (gen_pf L hg).symm.trans hp⟩

/-- Pasar de un horizonte no guiado a uno guiado no es sucesión genética (análogo a `tr_no_prec_plus`). -/
theorem no_gen_conversion (L : E4.Ley M) {w w' : X.Om}
    (h0 : X.pf w ≠ (true, true, true)) (h1 : X.pf w' = (true, true, true)) : ¬ Gnt X w w' :=
  fun hg => h0 ((gen_pf L hg).trans h1)

theorem desP_desM_disj {d d' : Y.Dc} : ¬ (Y.DesP d d' ∧ Y.DesM d d') := by
  rintro ⟨⟨_, w, hw, hp⟩, ⟨_, v, hv, hq⟩⟩
  have : w = v := Option.some.inj (hw.symm.trans hv)
  subst this
  exact hq hp

/-- Monotonía [p. 319, regla 5]: más diferenciación, al mismo perfil, no pierde lo establecido. -/
theorem at_mono {w w' : X.Om} {d : Y.Dc} (hd : ∀ x, X.Df w x → X.Df w' x) (h : Y.At w d) :
    Y.At w' d :=
  ⟨h.1, fun c hc x hx => hd x (h.2 c hc x hx)⟩

theorem pos_pf {w w' : X.Om} {d : Y.Dc} (hp : X.pf w = X.pf w') (h : Y.Pos w d) : Y.Pos w' d :=
  ⟨h.1, fun p hp' => by
    obtain ⟨a, b⟩ := h.2 p hp'
    exact ⟨a, b.trans hp⟩⟩

theorem contra_pf {w w' : X.Om} {d : Y.Dc} (hp : X.pf w = X.pf w') (h : Y.Contra w d) :
    Y.Contra w' d :=
  ⟨h.1, fun hh => h.2 (fun p hp' => by
    obtain ⟨a, b⟩ := hh p hp'
    exact ⟨a, b.trans hp.symm⟩)⟩

theorem est_mono {w w' : X.Om} {d : Y.Dc} (hp : X.pf w = X.pf w')
    (hd : ∀ x, X.Df w x → X.Df w' x) (h : Y.Est w d) : Y.Est w' d :=
  ⟨h.1, at_mono hd h.2.1, pos_pf hp h.2.2⟩

theorem rt_mono {w w' : X.Om} {d : Y.Dc} (hp : X.pf w = X.pf w')
    (hd : ∀ x, X.Df w x → X.Df w' x) (h : Y.Rt w d) : Y.Rt w' d :=
  ⟨h.1, at_mono hd h.2.1, contra_pf hp h.2.2⟩

/-- Pluralismo [pp. 315–318]: a igual perfil y diferenciación, igual selección. -/
theorem est_plural {w w' : X.Om} {d : Y.Dc} (hp : X.pf w = X.pf w')
    (hd : ∀ x, X.Df w x ↔ X.Df w' x) : Y.Est w d ↔ Y.Est w' d :=
  ⟨est_mono hp (fun x => (hd x).1), est_mono hp.symm (fun x => (hd x).2)⟩

/-- Historicidad excluye clasicismo; el clasicismo implica permanencia (con L8). -/
theorem hist_no_clas {d : Y.Dc} (h : Y.Hist d) : ¬ Y.Clas d := by
  obtain ⟨c, c', s, s', h1, h2, hne⟩ := h
  exact fun hc => hne (hc c c' s s' h1 h2)

theorem clas_perm (LY : Ley Y) {d : Y.Dc} (h : Y.Clas d) : Y.Perm d := by
  intro c s s' _ h1 h2
  have : s = s' := h (Y.cd d) c s s' h1 h2
  subst this
  exact LY.L8.1 s

/-- El método no decide el estatuto de las categorías [cap. 11, p. 278]. -/
theorem st_indep (LY : Ley Y) (s' : X.Om → X.CatG ⊕ X.CatS → Es) : Ley { Y with st := s' } :=
  ⟨LY.L1, LY.L2, LY.L3, LY.L4, LY.L5, LY.L6, LY.L7, LY.L8, LY.L9, LY.L10, LY.L11, LY.L12,
    LY.L13, LY.L14⟩

end General


/-! ## Modelo actual: Nicea–Constantinopla III
  E4 (PV = Fin 4): p₀ = homoousios, p₁ = enhypostasía, p₂ = metafísica plena (perfil (1,1,1));
     p₃ = tesis contraria (perfil (1,0,0), estipulación del modelo). Bases: {p₀,p₁,p₂} y {p₃}; p₃ ≈ p₀,p₁,p₂.
  E5 (Ω = Fin 3): ω_sd = 0 (diferenciado sin conversión), ω_cs = 1 (convertido sin diferenciación),
     ω_cd = 2 (convertido y diferenciado). Una conversión c₀ : ω_sd → ω_cd.
  Dc = Fin 9: d₀ (tres primeros siglos, rel); d₁..d₅ = Nicea, Cp I, Éfeso, Calcedonia, Cp III (ig);
     d₆ = enhypostasía, d₇ = metafísica plena, d₈ = tesis contraria (te).
  Ctx = Fin 8: k₀ (tres primeros siglos), k₁..k₅ (estadios conciliares; k₄ = contexto lógico),
     k₆ = incoativamente metafísico, k₇ = plenamente metafísico. -/
section Nicea
open E4 (Perfil)

def niceaRel : List (Nat × Nat × E4.Rel) :=
  [(0,1,.complementaria),(1,2,.complementaria),(0,2,.complementaria),
   (0,3,.irreductible),(1,3,.irreductible),(2,3,.irreductible)]

def niceaDsc : List (Nat × Nat × Nat) := niceaRel.map (fun t => (t.1, t.2.1, 0))

abbrev NiceaE4 : E4.Mp (Fin 4) (Fin 4) where
  CT := Bool
  Ep := Bool
  Mf := Bool
  Et := Bool
  Vr := Bool
  car := fun p => ((true, true, true), decide (p.val < 3), decide (p.val < 3))
  cvi := fun x => decide (x = (true, true, true))
  cvm := fun b => b
  cvr := fun b => b
  sgE := fun c e => c = e
  sgM := fun x m => x.1 = m
  Odl3 := fun p => p.val < 4
  rel := fun a b => E4.mkRel niceaRel a.val b.val
  Dsc := fun a b => E4.inT niceaDsc a.val b.val = true
  Afn := fun a b => E4.inT [] a.val b.val = true
  Rz := Fin 1
  red := fun _ _ => 0
  cls := fun _ o => o = E4.Op.horizonte
  ot := fun _ _ o => o = E4.Op.horizonte
  V := fun i p => i.val = p.val
  Va := Fin 1
  vl4 := fun _ _ => False
  sgV := fun _ => true
  Yo := Fin 1
  sost := fun _ p => p.val = 0
  df := fun _ _ => False
  Base := Fin 2
  π := fun p => if p.val < 3 then 0 else 1
  dsc_afn_disj := by decide
  cls_ne := fun _ => ⟨E4.Op.horizonte, rfl⟩

theorem NiceaE4_ley : E4.Ley NiceaE4 where
  L1 := by decide
  L2 := by decide
  L3a := by decide
  L3b := by
    intro a b ha hb
    constructor
    · intro h
      have key : ∀ a b : Fin 4, NiceaE4.Odl3 a → NiceaE4.Odl3 b → NiceaE4.π a = NiceaE4.π b →
          b ∈ E4.reach NiceaE4 a 4 := by decide
      exact E4.reach_sound NiceaE4 a ha 4 b (key a b ha hb h)
    · exact E4.EqC_pi NiceaE4 (by decide)
  L6a := by decide
  L6b := by decide
  L6c := E4.TG.irrefl_of_rank _ (fun x => x.val) (by decide)
  L7 := by
    have key : ∀ a b : Fin 4, (NiceaE4.rel a b).isSome → NiceaE4.rel a b ≠ some E4.Rel.irreductible →
        NiceaE4.Pc a = NiceaE4.Pc b := by decide
    intro a b r hr hne
    have hs : (NiceaE4.rel a b).isSome = true := by rw [hr]; rfl
    exact key a b hs (by rw [hr]; intro h; exact hne (Option.some.inj h))
  L9 := fun _ _ _ => Iff.rfl
  L10 := by decide

abbrev NiceaX : E5.Mp NiceaE4 where
  Cv := Fin 1
  Om := Fin 3
  CatG := Fin 1
  CatS := Fin 1
  Orig := Unit
  Gen := Unit
  Act := Unit
  Trf := Unit
  Ada := Unit
  k5 := fun _ => E5.Esc.personal
  pm := fun _ => (true, false, false)
  pp := fun _ => (true, true, true)
  tr := fun _ => none
  cv := fun _ => none
  hzm := fun _ => 0
  hzp := fun _ => 2
  pf := fun w => if w.val = 0 then (true, false, false) else (true, true, true)
  ex := fun _ w => w.val = 2
  Aut := fun w => w.val ≠ 0
  rep := fun w => if w.val = 0 then none else some 0
  Df := fun w x => (w.val = 0 ∧ x = Cs5.teo) ∨ (w.val = 2 ∧ (x = Cs5.teo ∨ x = Cs5.int))
  deg := fun w x =>
    if (w.val = 0 ∧ x = Cs5.teo) ∨ (w.val = 2 ∧ (x = Cs5.teo ∨ x = Cs5.int))
    then some E5.Gr5.madura else none
  gs := fun _ => 3
  Tm := fun _ => ((), (), (), (), ())
  Df_sc := by decide
  deg_def := by
    intro w x
    cases x <;> revert w <;> decide

theorem NiceaX_ley : E5.Ley NiceaX where
  D1 := by decide
  D2 := by intro c b b' h; simp at h
  D3 := by intro y c h; simp at h
  C1 := by decide
  C2 := by decide
  C3 := by intro w a _; rfl
  C4a := by decide
  C4b := ⟨0, by decide⟩

/-- E6 del caso. -/
abbrev NiceaY : Mp NiceaX where
  Dc := Fin 9
  Au := Cl
  Nt := Fin 3
  Ctx := Fin 8
  Fo := Fin 9
  Sg := Fin 12
  cl := fun d =>
    if d.val = 0 then Cl.rel else if d.val ≤ 5 then Cl.ig else Cl.te
  au0 := fun c => c
  fn := fun d x => (d.val ≤ 5 ∧ x ≠ Fn.nor) ∨ ((d.val = 6 ∨ d.val = 7) ∧ (x = Fn.cog ∨ x = Fn.nor))
  trt := fun d t => (d.val = 0 ∧ t = Tr.lt) ∨ (d.val ≠ 0 ∧ t = Tr.ld)
  nt := fun d =>
    if d.val = 0 then none else if d.val ≤ 5 then some 2 else if d.val ≤ 7 then some 1 else some 0
  ltNt := fun a b => a.val < b.val
  Dep := fun d d' => (d.val = 6 ∧ d'.val = 4) ∨ (d.val = 7 ∧ d'.val = 4) ∨ (d.val = 8 ∧ d'.val = 1)
  tc := fun _ => Kc.evo
  en := fun d c => (d.val = 0 ∧ c.val = 0) ∨ (d.val = 1 ∧ (c.val = 1 ∨ c.val = 5)) ∨
    (d.val = 2 ∧ c.val = 2) ∨ (d.val = 3 ∧ c.val = 3) ∨
    (d.val = 4 ∧ (c.val = 4 ∨ c.val = 6 ∨ c.val = 7)) ∨ (d.val = 5 ∧ c.val = 5) ∨
    (d.val = 6 ∧ c.val = 6) ∨ (d.val = 7 ∧ c.val = 7) ∨ (d.val = 8 ∧ c.val = 1)
  sg := fun d c =>
    if d.val = 0 ∧ c.val = 0 then some 0
    else if d.val = 1 ∧ c.val = 1 then some 1
    else if d.val = 1 ∧ c.val = 5 then some 2
    else if d.val = 2 ∧ c.val = 2 then some 3
    else if d.val = 3 ∧ c.val = 3 then some 4
    else if d.val = 4 ∧ c.val = 4 then some 5
    else if d.val = 4 ∧ c.val = 6 then some 6
    else if d.val = 4 ∧ c.val = 7 then some 7
    else if d.val = 5 ∧ c.val = 5 then some 8
    else if d.val = 6 ∧ c.val = 6 then some 9
    else if d.val = 7 ∧ c.val = 7 then some 10
    else if d.val = 8 ∧ c.val = 1 then some 11
    else none
  fo := fun d => d
  cd := fun d =>
    if d.val = 0 then 0 else if h : d.val ≤ 5 then ⟨d.val, by omega⟩
    else if d.val = 6 then 6 else if d.val = 7 then 7 else 1
  ant := fun a b => (1 ≤ a.val ∧ a.val < b.val ∧ b.val ≤ 5) ∨
    (1 ≤ a.val ∧ a.val ≤ 4 ∧ (b.val = 6 ∨ b.val = 7)) ∨ (a.val = 6 ∧ b.val = 7)
  Dv := fun a b => (a.val = 0 ∧ b.val = 1) ∨ (a.val = 4 ∧ b.val = 6)
  It := fun _ _ => False
  sle := fun a b => a = b ∨ (a.val = 1 ∧ b.val = 2) ∨ (a.val = 5 ∧ b.val = 6) ∨
    (a.val = 6 ∧ b.val = 7) ∨ (a.val = 5 ∧ b.val = 7)
  Dsr := fun d d' => (d.val, d'.val) ∈ [(0,1),(1,2),(2,3),(3,4),(4,5),(4,6),(6,7)]
  mdd := fun d d' =>
    if d.val = 0 ∧ d'.val = 1 then some Md.dia
    else if d.val = 1 ∧ d'.val = 2 then some Md.nt
    else if d.val = 2 ∧ d'.val = 3 then some Md.nt
    else if d.val = 3 ∧ d'.val = 4 then some Md.uso
    else if d.val = 4 ∧ d'.val = 5 then some Md.uso
    else if d.val = 4 ∧ d'.val = 6 then some Md.tsi
    else if d.val = 6 ∧ d'.val = 7 then some Md.tsi
    else none
  hz := fun d => if d.val = 0 then some 1 else if d.val = 8 then some 0 else some 2
  Ctp := fun d d' => d.val = 8 ∧ d'.val = 1
  rq := fun c x => 4 ≤ c.val ∧ x = Cs5.teo
  nu := fun d p => (d.val = 6 ∧ p.val = 1) ∨ (d.val = 7 ∧ p.val = 2) ∨ (d.val = 8 ∧ p.val = 3)
  Ap := fun w d => w.val ≠ 0 ∧ d.val ≤ 5
  Apn := fun _ d => d.val ≤ 5
  st := fun _ _ => Es.mod
  trt_ne := fun d => by
    by_cases h : d.val = 0
    · exact ⟨Tr.lt, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨Tr.ld, Or.inr ⟨h, rfl⟩⟩
  sg_def := by decide
  mdd_def := by decide
  nt_def := by decide
  cadena_Nt := by unfold IsChain; refine ⟨?_, ?_, ?_⟩ <;> decide


set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 8192

/-! Instancias de decidibilidad sobre los tipos proyectados (se reducen a `Fin n`). -/
instance (p : NiceaY.Dc → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 9, p x))
instance (p : NiceaY.Dc → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 9, p x))
instance (p : NiceaY.Ctx → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 8, p x))
instance (p : NiceaY.Ctx → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 8, p x))
instance (p : NiceaY.Sg → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 12, p x))
instance (p : NiceaX.Om → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NiceaX.Om → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NiceaY.Sg) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 12) = b))
instance (a b : NiceaY.Ctx) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 8) = b))
instance (a b : NiceaY.Dc) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 9) = b))


theorem NiceaY_ley : Ley NiceaY where
  L1 := fun a b h => h
  L2 := ⟨by decide, by decide⟩
  L3 := by decide
  L4 := by decide
  L5 := by decide
  L6 := by decide
  L7 := by decide
  L8 := by decide
  L9 := by decide
  L10 := by decide
  L11 := by decide
  L12 := by decide
  L13 := by decide
  L14 := by decide

/-! ### Lo que muestra el modelo -/

/-- Mod(E6) ≠ ∅, sobre un E4 y un E5 que satisfacen las suyas. -/
theorem Mod_noVacio :
    ∃ (M : E4.Mp (Fin 4) (Fin 4)) (_ : E4.Ley M) (X : E5.Mp M) (_ : E5.Ley X) (Y : Mp X), Ley Y :=
  ⟨NiceaE4, NiceaE4_ley, NiceaX, NiceaX_ley, NiceaY, NiceaY_ley⟩

/-- La piedra de toque [p. 320]: cada horizonte establece lo que su perfil reconoce como posición. -/
theorem Nicea_Est_cd : ∀ d : Fin 9, NiceaY.Est 2 d ↔ d.val = 6 ∨ d.val = 7 := by decide
theorem Nicea_Est_sd : ∀ d : Fin 9, NiceaY.Est 0 d ↔ d.val = 8 := by decide
theorem Nicea_Est_cs : ∀ d : Fin 9, ¬ NiceaY.Est 1 d := by decide
theorem Nicea_Rt_cd : ∀ d : Fin 9, NiceaY.Rt 2 d ↔ d.val = 8 := by decide
theorem Nicea_Rt_cs : ∀ d : Fin 9, NiceaY.Rt 1 d ↔ d.val = 8 := by decide
theorem Nicea_Rt_sd : ∀ d : Fin 9, NiceaY.Rt 0 d ↔ d.val = 6 ∨ d.val = 7 := by decide

/-- Desde ω_sd la tesis contraria es posición y desde ω_cd es contraposición. -/
theorem Nicea_piedra : ∃ d : Fin 9, NiceaY.Est 0 d ∧ NiceaY.Rt 2 d := ⟨8, by decide, by decide⟩

/-- L4: solo d₆ y d₇ llevan la función normativa. -/
theorem Nicea_nor : ∀ d : Fin 9, NiceaY.fn d Fn.nor ↔ d.val = 6 ∨ d.val = 7 := by decide

/-- Todos los desarrollos del caso son guiados; Des⁻ = ∅. -/
theorem Nicea_Des : (∀ d d' : Fin 9, NiceaY.Dsr d d' → NiceaY.DesP d d') ∧
    (∀ d d' : Fin 9, ¬ NiceaY.DesM d d') := by decide

/-- Permanencia, historicidad y no-clasicismo en Nicea (d₁) y en Calcedonia (d₄). -/
theorem Nicea_perm_hist :
    (NiceaY.Perm 1 ∧ NiceaY.Hist 1 ∧ ¬ NiceaY.Clas 1) ∧
    (NiceaY.Perm 4 ∧ NiceaY.Hist 4 ∧ ¬ NiceaY.Clas 4) := by decide

/-- Ap y At son independientes [p. 322]. -/
theorem Nicea_Ap_At :
    (∃ (w : Fin 3) (d : Fin 9), NiceaY.Ap w d ∧ ¬ NiceaY.At w d) ∧
    (∃ (w : Fin 3) (d : Fin 9), NiceaY.At w d ∧ ¬ NiceaY.Ap w d) :=
  ⟨⟨1, 1, by decide, by decide⟩, ⟨0, 6, by decide, by decide⟩⟩

/-- Pluralismo: mismo perfil, distinta diferenciación, distinta selección. -/
theorem Nicea_plural :
    NiceaX.pf 1 = NiceaX.pf 2 ∧ (∃ x, NiceaX.Df 2 x ∧ ¬ NiceaX.Df 1 x) ∧
    (∃ d : Fin 9, NiceaY.Est 2 d ∧ ¬ NiceaY.Est 1 d) :=
  ⟨by decide, ⟨Cs5.teo, by decide, by decide⟩, ⟨6, by decide, by decide⟩⟩

/-- El enlace ≈ entre ω_sd y ω_cd existe (L12), pero no hay sucesión genética entre ellos. -/
theorem Nicea_dia : DiaH NiceaX 0 2 := by decide
theorem Nicea_no_gen : ¬ Gnt NiceaX 0 2 :=
  no_gen_conversion NiceaE4_ley (by decide) (by decide)

/-! ### Mp ⊋ Mod: modelos bien tipados que violan una cláusula -/
theorem bad_L1 : ¬ Ley { NiceaY with au0 := fun _ => Cl.me } := by
  intro L; exact absurd (L.L1 Cl.mo Cl.rel rfl) (by decide)
theorem bad_L2 : ¬ Ley { NiceaY with Dep := fun _ _ => False } := by
  intro L; obtain ⟨d', _, h⟩ := L.L2.1 6 (by decide); exact h
theorem bad_L3 : ¬ Ley { NiceaY with fn := fun _ _ => False } := by
  intro L; exact (L.L3 1 (by decide)).1
theorem bad_L4 : ¬ Ley { NiceaY with fn := fun d x => NiceaY.fn d x ∨ (d.val = 8 ∧ x = Fn.nor) } := by
  intro L
  obtain ⟨w, hw, h⟩ := (L.L4 8).1 (Or.inr ⟨rfl, rfl⟩)
  have key : ∀ w : Fin 3, NiceaX.pf w = (true, true, true) → ¬ NiceaY.Est w 8 := by decide
  exact key w hw h
theorem bad_L5 : ¬ Ley { NiceaY with cd := fun _ => 7 } := by
  intro L; exact absurd (L.L5 6) (by decide)
theorem bad_L6 : ¬ Ley { NiceaY with ant := fun _ _ => True } := by
  intro L; exact L.L6.1 0 trivial
theorem bad_L7 : ¬ Ley { NiceaY with Dv := fun _ _ => True } := by
  intro L; exact L.L7.1 0 trivial
theorem bad_L8 : ¬ Ley { NiceaY with sle := fun _ _ => False } := by
  intro L; exact L.L8.1 0
theorem bad_L9 : ¬ Ley { NiceaY with cd := fun d => if d.val = 5 then 0 else NiceaY.cd d } := by
  intro L; exact absurd (L.L9 4 5 (by decide)) (by decide)
theorem bad_L10 : ¬ Ley { NiceaY with rq := fun _ _ => False } := by
  intro L; exact L.L10 3 4 Md.uso (by decide) Cs5.teo (by decide)
theorem bad_L11 : ¬ Ley { NiceaY with hz := fun d => if d.val = 6 then some (1 : Fin 3) else NiceaY.hz d } := by
  intro L; exact absurd (L.L11 6 1 (by decide)) (by decide)
theorem bad_L12 : ¬ Ley { NiceaY with Ctp := fun _ _ => False } := by
  intro L; obtain ⟨d'', w'', w', h, _⟩ := L.L12 0 1 (by decide); exact h
theorem bad_L13 : ¬ Ley { NiceaY with Apn := fun _ _ => False } := by
  intro L; exact L.L13 1 0 (by decide)
theorem bad_L14 : ¬ Ley { NiceaY with Ap := fun _ _ => True } := by
  intro L; exact absurd (L.L14 0 0 trivial) (by decide)

/-- Perm no es parte de la ley: hay un modelo de la ley donde la permanencia de Nicea falla. -/
abbrev NiceaY' : Mp NiceaX := { NiceaY with sle := fun a b => a = b }

theorem perm_independiente : Ley NiceaY' ∧ ¬ NiceaY'.Perm (1 : Fin 9) :=
  ⟨⟨NiceaY_ley.L1, NiceaY_ley.L2, NiceaY_ley.L3, NiceaY_ley.L4, NiceaY_ley.L5, NiceaY_ley.L6,
    NiceaY_ley.L7, ⟨fun _ => rfl, fun _ _ _ h1 h2 => h1.trans h2⟩, NiceaY_ley.L9,
    NiceaY_ley.L10, NiceaY_ley.L11, NiceaY_ley.L12, NiceaY_ley.L13, NiceaY_ley.L14⟩,
   by decide⟩

end Nicea

end E6
