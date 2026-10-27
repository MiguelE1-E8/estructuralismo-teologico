import E7
/-
  E8 · Comunicaciones — verificación en Lean 4 (sin Mathlib, sin sorry).
  Traduce la tupla, Mp(E8), las condiciones de tipo, la ley (L1–L8; L9 es la definición de la salida
  E8(s)) y los dos modelos actuales: Nicea–Constantinopla III y la escolástica (SCG IV / ST).

  Convenciones:
   - E8 se parametriza por Z : E7.Mp Y (que depende de Y : E6.Mp X, X : E5.Mp M, M : E4.Mp).
     De E7 se usan, sin redefinir: Sy (Σ), Dcs (Dc_s), hzs (hz), Sis (= Im(E7)), Posc (L14a).
     De E6/E5: Y.Ap (aprehensión real) y X.Om (horizontes).
   - Nuc (núcleo que debe conservarse) se declara en E8, con Nuc(s) ⊆ Dc_s.
   - Rcp(s) = Rec(s) := {ω : Nuc(s) ⊆ Ap(ω)} (con Ap real; E6 L14: Ap(ω,d) ⇒ ω auténtico).
   - tpx(x) := tpc[ctn(x)] se DEFINE (no es campo); Hor, Sc, Pl, Ipc, Cnc, Div, Apt, Out, Fr son derivados.
   - Las condiciones de tipo (`Tipo`) se separan de `Mp` (como Prop) para poder modificar un campo
     sin reconstruir pruebas: los contraejemplos de Mp ⊋ Mod son `{ W with campo := … }`.
   - Cada cláusula por sistema L1–L8 es un predicado `Kn s`; `Ley` exige Kn s para todo s ∈ Sis.
   - Esfera E8:Sis → 𝒫(Msj) es `Out` con Msj := Ex × Med × Dst × Lug × Tiempo (Tmp = Tiempo).
   - Estipulaciones del modelo (no de Lonergan): las dos confesiones i₁, i₂, los agentes, la
     división de culturas Cu = {c, u, n} y las expresiones x_c, x_u, p_c, p_u, p_n.

  Textos de Lonergan (Método en Teología, Sígueme 1988). Cap. 14 «La comunicación», pp. 341–353 (citas
  verificadas contra el libro): L1 y L2 ← p. 350 («solamente cuando la teología se una a todas las demás ramas
  importantes de las ciencias humanas», «se pueden liberar de toda intrusión ideológica las investigaciones»);
  L4 ← p. 348 («El mensaje cristiano debe ser comunicado a todas las naciones»); L5 ← pp. 347–348 (conocer,
  vivir, poner en práctica; comprender «desde el interior» la cultura y el lenguaje de los pueblos);
  L6 ← p. 348 («La comunicación supone una comunidad constituida»); L7 ← p. 353 («la división reside
  principalmente en la significación cognoscitiva… Las significaciones constitutiva y eficiente son el objeto
  de un amplio acuerdo entre los cristianos»); L3 (Nuc) NO es del cap. 14: viene de la caracterización inicial
  de E8 dada por el usuario («conservar su identidad»).
  Cap. 5 §V «Una unidad dinámica» (pp. 139–143; citas tomadas de ciclo/e6_e5_restitucion.md y
  ciclo/aristas_retorno.md, pendientes de cotejar con el libro): E7→E8, la sistemática «determina lo esencial
  de lo que deberá ser comunicado» (p. 141) ⇒ Sis := Im(E7), Nuc ⊆ Dc_s; E8→E7, «De la comunicación pueden surgir
  problemas para la sistematización» (p. 141): NO es campo de esta tupla; vive en lean/CicloRetornos.lean
  (`Ciclo.RetornoE8E7`) como relación aparte sobre `Cadena38` (no interferencia por construcción). No hay
  enlace primitivo E8→E1: la vuelta es la clausura transitiva de los retornos autorizados («interdependencia
  general o indirecta»). E8 solo usa de E7 Sy, Dcs, hzs, Sis, Posc; los renombres de E7 (Pt→cz, Dsc→Dsp,
  Ep→Epc, Cp→Rsp, Eh→Ejm; aplicados el 20-oct) no lo afectan. Comprobado en la pasada del ciclo del 22-oct
  (ciclo/cierre_pendientes_22oct.md, Lean 4.22.0: E0…E8 y Ciclo* sin errores ni sorry). Los nombres de campos de esta tupla coinciden con los de la copia NiceaW de
  lean/CicloNicea.lean: si se cambia aquí, resincronizar allí.
  Compilado con `import E7` real (E7_web.lean guardado como módulo) y en E8_web.lean, Lean 4.35.0: 0 errores.
-/
namespace E8
open E6 (NiceaY NiceaX)

inductive Tsg | cog | con | efe deriving DecidableEq
inductive Nvs | exp | com | jui | val deriving DecidableEq

instance decAllTsg (p : Tsg → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff (p .cog ∧ p .con ∧ p .efe) (by
    constructor
    · rintro ⟨h1, h2, h3⟩ x; cases x <;> assumption
    · intro h; exact ⟨h _, h _, h _⟩)
instance decExTsg (p : Tsg → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  decidable_of_iff (p .cog ∨ p .con ∨ p .efe) (by
    constructor
    · rintro (h | h | h) <;> exact ⟨_, h⟩
    · rintro ⟨x, hx⟩; cases x <;> simp [hx])

/-! ## Modelo potencial Mp(E8): solo tipos -/
structure Mp {PV I : Type} {M : E4.Mp PV I} {X : E5.Mp M} {Y : E6.Mp X} (Z : E7.Mp Y) where
  -- conjuntos
  Esf : Type     -- esferas de saber (las de ρ_I son las que E8 consulta)
  Cu : Type      -- culturas
  Csc : Type      -- clases
  Prs : Type      -- agentes (personas)
  Ctn : Type      -- contenidos de significación
  Cmu : Type     -- comunidades
  Ex : Type      -- expresiones
  Med : Type     -- medios
  Lug : Type     -- lugares
  Tmp : Type      -- tiempos
  -- A. interfaz con E7 y las esferas
  Nuc : Z.Sy → Y.Dc → Prop
  rI : Z.Sy → Esf → Prop
  hum : Esf → Prop
  Len : Esf → Cu → Ex → Prop
  Pur : Esf → Prop
  -- B. destinatarios
  Pob : Cu → Csc → Prs → Prop
  hzA : Prs → X.Om
  -- C. significaciones y comunidades
  nvs : Ctn → Nvs
  tpc : Ctn → Tsg
  cnv : Prs → Ctn → Prop
  mb : Prs → Cmu → Prop
  Cpl : Ctn → Ctn → Prop
  Igs : Cmu → Prop
  -- D. expresiones
  Prep : Ex → Prop
  Ori : Ex → Z.Sy → Prop
  iota : Ex → Y.Dc → Prop
  ctn : Ex → Ctn → Prop
  ntg : Z.Sy → Cu → Csc → Ex → Prop
  Acs : Tsg → Ex → Cu → Csc → X.Om → Prop
  -- E. emisores
  Emi : Ex → Prs → Prop
  kn : Prs → Z.Sy → Prop
  prc : Prs → Ctn → Prop
  culA : Prs → Cu
  Cmp : Prs → Cu → Prop
  -- F. ecumenismo y medios
  Ec : Ex → Cmu → Prop
  Disp : Lug → Tmp → Med → Prop
  Adp : Ex → Med → Prop

namespace Mp
variable {PV I : Type} {M : E4.Mp PV I} {X : E5.Mp M} {Y : E6.Mp X} {Z : E7.Mp Y} (W : Mp Z)

/-- tpx(x) := tpc[ctn(x)]: los tipos de significación que x porta. -/
abbrev tpx (x : W.Ex) (t : Tsg) : Prop := ∃ k, W.ctn x k ∧ W.tpc k = t
/-- Hor(d) := hzA[Pob(d)]: los horizontes presentes en la población de d = (c, l). -/
abbrev Hor (c : W.Cu) (l : W.Csc) (w : X.Om) : Prop := ∃ a, W.Pob c l a ∧ W.hzA a = w
/-- Rec(s) := {ω : Nuc(s) ⊆ Ap(ω)} (Ap real, de E6). -/
abbrev Rcp (s : Z.Sy) (w : X.Om) : Prop := ∀ d, W.Nuc s d → Y.Ap w d
/-- Sc(i) := ⋂_{a ∈ i} Cn(a), con i no vacía. -/
abbrev Sc (i : W.Cmu) (k : W.Ctn) : Prop := (∃ a, W.mb a i) ∧ ∀ a, W.mb a i → W.cnv a k
/-- Pl(i): comunidad plena (cada significación de un miembro es compartida o complementada). -/
abbrev Pl (i : W.Cmu) : Prop :=
  (∃ a, W.mb a i) ∧ ∀ a b k, W.mb a i → W.mb b i → W.cnv a k → ∃ k', W.cnv b k' ∧ (k' = k ∨ W.Cpl k k')
/-- Ipc(x, c, a): imposición cultural (x de la cultura del emisor, no de la del destinatario). -/
abbrev Ipc (x : W.Ex) (c : W.Cu) (a : W.Prs) : Prop :=
  W.Emi x a ∧ (∃ e, W.Len e (W.culA a) x) ∧ ¬ ∃ e, W.Len e c x
/-- Cnc(i, j): tipos en los que las confesiones i y j coinciden. -/
abbrev Cnc (i j : W.Cmu) (t : Tsg) : Prop := ∀ k, W.tpc k = t → (W.Sc i k ↔ W.Sc j k)
/-- Div(i, j) := Tsg ∖ Cnc(i, j). -/
abbrev Div (i j : W.Cmu) (t : Tsg) : Prop := ¬ W.Cnc i j t
/-- Apt(a, x, s, c): idoneidad del emisor a de x (para el sistema s, hacia la cultura c). -/
abbrev Apt (a : W.Prs) (x : W.Ex) (s : Z.Sy) (c : W.Cu) : Prop :=
  (∀ k, W.ctn x k → W.cnv a k) ∧ (W.tpx x Tsg.cog → W.kn a s) ∧
  (W.tpx x Tsg.con → W.Rcp s (W.hzA a)) ∧ (∀ k, W.ctn x k → W.tpc k = Tsg.efe → W.prc a k) ∧ W.Cmp a c
/-- E8(s) = Out s: mensajes (x, m, d, l, t) con s ∈ Sis que satisfacen L1–L8. -/
abbrev Out (s : Z.Sy) (x : W.Ex) (m : W.Med) (c : W.Cu) (l : W.Csc) (g : W.Lug) (t : W.Tmp) : Prop :=
  Z.Sis s ∧ W.ntg s c l x ∧ W.Disp g t m ∧ W.Adp x m
/-- Fr(s): s da fruto (E8(s) ≠ ∅). -/
abbrev Fr (s : Z.Sy) : Prop := ∃ x m c l g t, W.Out s x m c l g t

/-- Condiciones de tipo de Mp(E8). -/
abbrev Tipo : Prop :=
  (∀ c l, ∃ a, W.Pob c l a) ∧ (∀ x, ∃ a, W.Emi x a) ∧
  (∀ x, (∃ d, W.iota x d) ↔ W.tpx x Tsg.cog) ∧
  (∀ x, W.Prep x → ∀ d, ¬ W.iota x d) ∧
  (∀ s d, W.Nuc s d → Z.Dcs s d)

/-- L1 (interdisciplinar): cada expresión entregada a d está en una esfera de ρ_I(s), en la cultura de d. -/
abbrev K1 (s : Z.Sy) : Prop := ∀ c l x, W.ntg s c l x → ∃ e, W.rI s e ∧ W.Len e c x
/-- L2 (integración): toda esfera humana consultada se depura (segundo uso de la dialéctica). -/
abbrev K2 (s : Z.Sy) : Prop := ∀ e, W.rI s e → W.hum e → W.Pur e
/-- L3 (identidad): preparatoria u orientada a s, o doctrinal con Nuc(s) ⊆ ι(x) ⊆ Dc_s. -/
abbrev K3 (s : Z.Sy) : Prop := ∀ c l x, W.ntg s c l x →
  (W.Prep x → W.Ori x s) ∧
  (¬ W.Prep x → (∃ d, W.iota x d) ∧ (∀ d, W.Nuc s d → W.iota x d) ∧ (∀ d, W.iota x d → Z.Dcs s d))
/-- L4 (cobertura y acceso): a cada horizonte de la población, una expresión accesible;
    receptivo ⇒ doctrinal con ι(x) ⊆ Ap(ω); no receptivo ⇒ preparatoria. -/
abbrev K4 (s : Z.Sy) : Prop := ∀ c l w, W.Hor c l w → ∃ x, W.ntg s c l x ∧
  (∀ t, W.tpx x t → W.Acs t x c l w) ∧
  (W.Rcp s w → ¬ W.Prep x ∧ ∀ d, W.iota x d → Y.Ap w d) ∧ (¬ W.Rcp s w → W.Prep x)
/-- L5 (idoneidad del emisor): conocer, vivir, practicar, comprender la cultura. -/
abbrev K5 (s : Z.Sy) : Prop := ∀ c l x, W.ntg s c l x → ∀ a, W.Emi x a → W.Apt a x s c
/-- L6 (eclesialidad): una expresión doctrinal sale de una confesión que la sostiene. -/
abbrev K6 (s : Z.Sy) : Prop := ∀ c l x, W.ntg s c l x → (∃ d, W.iota x d) →
  ∃ i, W.Igs i ∧ (∀ k, W.ctn x k → W.Sc i k) ∧ ∃ a, W.Emi x a ∧ W.mb a i
/-- L7 (ecumenismo): una expresión ecuménica solo porta tipos en los que las confesiones coinciden. -/
abbrev K7 (s : Z.Sy) : Prop := ∀ c l x, W.ntg s c l x → ∀ j, W.Ec x j → W.Igs j →
  ∀ i a, W.Igs i → W.Emi x a → W.mb a i → ∀ t, W.tpx x t → W.Cnc i j t
/-- L8 (adaptación): cada expresión tiene un medio adecuado en algún lugar y tiempo. -/
abbrev K8 (s : Z.Sy) : Prop := ∀ c l x, W.ntg s c l x → ∃ g t m, W.Disp g t m ∧ W.Adp x m
end Mp

/-- La ley de E8: L1–L8 para todo sistema de Sis; L9 es la definición de `Out`. -/
structure Ley {PV I : Type} {M : E4.Mp PV I} {X : E5.Mp M} {Y : E6.Mp X} {Z : E7.Mp Y} (W : Mp Z) : Prop where
  L1 : ∀ s, Z.Sis s → W.K1 s
  L2 : ∀ s, Z.Sis s → W.K2 s
  L3 : ∀ s, Z.Sis s → W.K3 s
  L4 : ∀ s, Z.Sis s → W.K4 s
  L5 : ∀ s, Z.Sis s → W.K5 s
  L6 : ∀ s, Z.Sis s → W.K6 s
  L7 : ∀ s, Z.Sis s → W.K7 s
  L8 : ∀ s, Z.Sis s → W.K8 s

/-! ## Consecuencias generales -/
section General
variable {PV I : Type} {M : E4.Mp PV I} {X : E5.Mp M} {Y : E6.Mp X} {Z : E7.Mp Y} {W : Mp Z}

/-- Interfaz con E7: hz(s) ∈ Rec(s) para todo s ∈ Sis (por L14a de E7 y Nuc ⊆ Dc_s). -/
theorem hz_rcp (T : W.Tipo) {s : Z.Sy} (h : Z.Sis s) : W.Rcp s (Z.hzs s) := by
  obtain ⟨_, _, hp⟩ := h
  intro d hd
  exact hp.L14a d (T.2.2.2.2 s d hd)

/-- Un sistema que no es posición no produce mensajes. -/
theorem sin_Sis_sin_salida {s : Z.Sy} (h : ¬ Z.Sis s) {x m c l g t} : ¬ W.Out s x m c l g t :=
  fun ho => h ho.1

/-- Una expresión preparatoria no porta significación cognoscitiva. -/
theorem prep_sin_cog (T : W.Tipo) {x : W.Ex} (h : W.Prep x) : ¬ W.tpx x Tsg.cog := by
  intro hc
  obtain ⟨d, hd⟩ := (T.2.2.1 x).2 hc
  exact T.2.2.2.1 x h d hd

/-- Con L1 no hay imposición cultural en lo que se entrega. -/
theorem sin_imposicion (L : Ley W) {s : Z.Sy} (hs : Z.Sis s) {c l x} (h : W.ntg s c l x) (a : W.Prs) :
    ¬ W.Ipc x c a := by
  rintro ⟨_, _, hn⟩
  obtain ⟨e, _, he⟩ := L.L1 s hs c l x h
  exact hn ⟨e, he⟩

/-- Con L7: si i y j divergen en el tipo t, una expresión ecuménica para j no porta t. -/
theorem ecum_sin_div (L : Ley W) {s : Z.Sy} (hs : Z.Sis s) {c l x} (h : W.ntg s c l x)
    {i j : W.Cmu} {a : W.Prs} (hij : W.Div i j t) (hE : W.Ec x j) (hj : W.Igs j) (hi : W.Igs i)
    (he : W.Emi x a) (hm : W.mb a i) : ¬ W.tpx x t :=
  fun ht => hij (L.L7 s hs c l x h j hE hj i a hi he hm t ht)

/-- Con L4 y L3: a todo horizonte no receptivo se le entrega una expresión sin contenido doctrinal. -/
theorem no_receptivo_prep (T : W.Tipo) (L : Ley W) {s : Z.Sy} (hs : Z.Sis s) {c l w}
    (hw : W.Hor c l w) (hn : ¬ W.Rcp s w) :
    ∃ x, W.ntg s c l x ∧ W.Prep x ∧ ¬ W.tpx x Tsg.cog := by
  obtain ⟨x, hx, _, _, hp⟩ := L.L4 s hs c l w hw
  exact ⟨x, hx, hp hn, prep_sin_cog T (hp hn)⟩

end General

/-! ## Modelo actual: Nicea–Constantinopla III
  Sis = {s₆, s₇} (E7.NiceaZ: 0, 1); s_A = 2 no es posición. Dc_s = Nuc(s) = {d₄}; hz(s) = ω_cd = 2.
  Horizontes (E6.NiceaX.Om = Fin 3): ω_sd = 0, ω_cs = 1, ω_cd = 2.
  Culturas Cu (estipulación del modelo): c = 0, u = 1, n = 2; una sola clase (Csc = Fin 1).
  Destinatarios: δ_c = (c, ·) y δ_u = (u, ·) con Hor = {ω_cd, ω_sd}; δ_n = (n, ·) con Hor = {ω_sd}.
  Agentes (Prs = Fin 6): a₀ (c, ω_cd, i₁), a₁ (c, ω_cd, i₂), a₂ (u, ω_cd, i₁), a₃ (c, ω_sd),
    a₄ (u, ω_sd), a₅ (n, ω_sd).
  Contenidos (Ctn = Fin 4): k₀ «dos voluntades y dos operaciones» (cog, juicio),
    k₁ «fraternidad convertida» (con, valor), k₂ «servicio y testimonio» (efe, valor),
    k₃ «una sola voluntad» (cog, juicio; solo i₂).
  Expresiones (Ex = Fin 5): x_c = 0, x_u = 1 (doctrinales, ι = {d₄}); p_c = 2, p_u = 3, p_n = 4
    (preparatorias). Comunidades: i₁ = 0 (Sc = {k₀,k₁,k₂}), i₂ = 1 (Sc = {k₁,k₂,k₃}); Div = {cog}.
  Esferas (Esf = Fin 3): historia = 0, ciencias humanas = 1 (humanas), teoría = 2.
  Medios (Med = Fin 2): palabra = 0, obra = 1; lugares (Lug = Fin 2); Tmp = Fin 1. -/
section Nicea
open E6 (NiceaY NiceaX)

def nCul (a : Fin 6) : Fin 3 := if a.val = 2 ∨ a.val = 4 then 1 else if a.val = 5 then 2 else 0

abbrev NiceaW : Mp E7.NiceaZ where
  Esf := Fin 3
  Cu := Fin 3
  Csc := Fin 1
  Prs := Fin 6
  Ctn := Fin 4
  Cmu := Fin 2
  Ex := Fin 5
  Med := Fin 2
  Lug := Fin 2
  Tmp := Fin 1
  Nuc := fun s d => E7.NiceaZ.Dcs s d
  rI := fun s _ => s.val ≤ 1
  hum := fun e => e.val ≤ 1
  Len := fun e c x =>
    (x.val = 0 ∧ c.val = 0 ∨ x.val = 1 ∧ c.val = 1 ∨ x.val = 2 ∧ c.val = 0 ∨
     x.val = 3 ∧ c.val = 1 ∨ x.val = 4 ∧ c.val = 2) ∧
    ((x.val ≤ 1 ∧ e.val = 2) ∨ (2 ≤ x.val ∧ e.val ≤ 1))
  Pur := fun e => e.val ≤ 1
  Pob := fun c _ a => nCul a = c
  hzA := fun a => if a.val ≤ 2 then (2 : Fin 3) else (0 : Fin 3)
  nvs := fun k => if k.val = 0 ∨ k.val = 3 then Nvs.jui else Nvs.val
  tpc := fun k => if k.val = 0 ∨ k.val = 3 then Tsg.cog else if k.val = 1 then Tsg.con else Tsg.efe
  cnv := fun a k => ((a.val = 0 ∨ a.val = 2) ∧ k.val ≤ 2) ∨ (a.val = 1 ∧ 1 ≤ k.val)
  mb := fun a i => ((a.val = 0 ∨ a.val = 2) ∧ i.val = 0) ∨ (a.val = 1 ∧ i.val = 1)
  Cpl := fun k k' => (k.val = 1 ∧ k'.val = 2) ∨ (k.val = 2 ∧ k'.val = 1)
  Igs := fun _ => True
  Prep := fun x => 2 ≤ x.val
  Ori := fun x s => 2 ≤ x.val ∧ s.val ≤ 1
  iota := fun x d => x.val ≤ 1 ∧ d.val = 4
  ctn := fun x k => (x.val ≤ 1 ∧ k.val ≤ 1) ∨ (2 ≤ x.val ∧ k.val = 2)
  ntg := fun s c _ x => s.val ≤ 1 ∧
    ((c.val = 0 ∧ (x.val = 0 ∨ x.val = 2)) ∨ (c.val = 1 ∧ (x.val = 1 ∨ x.val = 3)) ∨ (c.val = 2 ∧ x.val = 4))
  Acs := fun t x _ _ w => (x.val ≤ 1 ∧ 1 ≤ w.val) ∨ (2 ≤ x.val ∧ t = Tsg.efe)
  Emi := fun x a => (x.val = 0 ∧ a.val = 0) ∨ (x.val = 1 ∧ a.val = 2) ∨ (x.val = 2 ∧ a.val = 0) ∨
    (x.val = 3 ∧ a.val = 2) ∨ (x.val = 4 ∧ a.val = 2)
  kn := fun a s => (a.val = 0 ∨ a.val = 2) ∧ s.val ≤ 1
  prc := fun a k => (a.val = 0 ∨ a.val = 2) ∧ k.val = 2
  culA := nCul
  Cmp := fun a c => (a.val = 0 ∧ c.val = 0) ∨ (a.val = 2 ∧ (c.val = 1 ∨ c.val = 2))
  Ec := fun x j => x.val = 2 ∧ j.val = 1
  Disp := fun g _ m => g.val = m.val
  Adp := fun x m => (x.val ≤ 1 ∧ m.val = 0) ∨ (2 ≤ x.val ∧ m.val = 1)

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 8192

instance (a b : E7.NiceaZ.Sy) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (a b : NiceaX.Om) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NiceaW.Esf → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NiceaW.Esf → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NiceaW.Esf) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NiceaW.Cu → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NiceaW.Cu → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NiceaW.Cu) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NiceaW.Csc → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NiceaW.Csc → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NiceaW.Csc) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NiceaW.Prs → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 6, p x))
instance (p : NiceaW.Prs → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 6, p x))
instance (a b : NiceaW.Prs) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 6) = b))
instance (p : NiceaW.Ctn → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 4, p x))
instance (p : NiceaW.Ctn → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 4, p x))
instance (a b : NiceaW.Ctn) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 4) = b))
instance (p : NiceaW.Cmu → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NiceaW.Cmu → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NiceaW.Cmu) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NiceaW.Ex → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 5, p x))
instance (p : NiceaW.Ex → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 5, p x))
instance (a b : NiceaW.Ex) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 5) = b))
instance (p : NiceaW.Med → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NiceaW.Med → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NiceaW.Med) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NiceaW.Lug → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NiceaW.Lug → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NiceaW.Lug) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NiceaW.Tmp → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NiceaW.Tmp → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NiceaW.Tmp) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))

theorem nicea_Tipo : NiceaW.Tipo := by decide

theorem nicea_Ley : Ley NiceaW where
  L1 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NiceaW.K1 s by decide) s ((E7.nicea_Sis s).1 hs)
  L2 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NiceaW.K2 s by decide) s ((E7.nicea_Sis s).1 hs)
  L3 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NiceaW.K3 s by decide) s ((E7.nicea_Sis s).1 hs)
  L4 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NiceaW.K4 s by decide) s ((E7.nicea_Sis s).1 hs)
  L5 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NiceaW.K5 s by decide) s ((E7.nicea_Sis s).1 hs)
  L6 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NiceaW.K6 s by decide) s ((E7.nicea_Sis s).1 hs)
  L7 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NiceaW.K7 s by decide) s ((E7.nicea_Sis s).1 hs)
  L8 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NiceaW.K8 s by decide) s ((E7.nicea_Sis s).1 hs)

/-- Mod(E8) ≠ ∅, sobre Mod(E7) ≠ ∅. -/
theorem Mod_noVacio : ∃ W : Mp E7.NiceaZ, W.Tipo ∧ Ley W := ⟨NiceaW, nicea_Tipo, nicea_Ley⟩

/-! ### Lo que muestra el modelo -/

/-- Nuc(s) = Dc_s = {d₄} en Sis. -/
theorem nicea_Nuc : ∀ s : Fin 3, s.val ≤ 1 → ∀ d : Fin 9, (NiceaW.Nuc s d ↔ d.val = 4) := by decide

/-- Rec(s) = {ω_cs, ω_cd}: el horizonte ω_sd no es receptivo (E6: Ap(ω) ⇒ ω auténtico). -/
theorem nicea_Rcp : ∀ s : Fin 3, s.val ≤ 1 → ∀ w : Fin 3, (NiceaW.Rcp s w ↔ w.val ≠ 0) := by decide

/-- hz(s) = ω_cd ∈ Rec(s) (instancia de la interfaz hz_rcp). -/
theorem nicea_hz_rcp : ∀ s : Fin 3, E7.NiceaZ.Sis s → NiceaW.Rcp s (E7.NiceaZ.hzs s) :=
  fun _ hs => hz_rcp nicea_Tipo hs

/-- Horizontes por destinatario: δ_c y δ_u tienen {ω_sd, ω_cd}; δ_n solo {ω_sd}. -/
theorem nicea_Hor :
    (∀ w : Fin 3, NiceaW.Hor (0 : Fin 3) (0 : Fin 1) w ↔ w.val = 0 ∨ w.val = 2) ∧
    (∀ w : Fin 3, NiceaW.Hor (1 : Fin 3) (0 : Fin 1) w ↔ w.val = 0 ∨ w.val = 2) ∧
    (∀ w : Fin 3, NiceaW.Hor (2 : Fin 3) (0 : Fin 1) w ↔ w.val = 0) := by decide

/-- A δ_n solo se le entregan expresiones preparatorias (y sin contenido cognoscitivo). -/
theorem nicea_dn_prep : ∀ s : Fin 3, s.val ≤ 1 → ∀ x : Fin 5,
    NiceaW.ntg s (2 : Fin 3) (0 : Fin 1) x → NiceaW.Prep x ∧ ¬ NiceaW.tpx x Tsg.cog := by decide

/-- A δ_c se le entregan una doctrinal (x_c) y una preparatoria (p_c): ambos horizontes cubiertos. -/
theorem nicea_dc : ∀ s : Fin 3, s.val ≤ 1 → ∀ x : Fin 5,
    NiceaW.ntg s (0 : Fin 3) (0 : Fin 1) x ↔ x.val = 0 ∨ x.val = 2 := by decide

/-- Las confesiones i₁ e i₂ coinciden en lo constitutivo y lo efectivo y divergen en lo cognoscitivo. -/
theorem nicea_Div : ∀ t : Tsg, NiceaW.Div (0 : Fin 2) (1 : Fin 2) t ↔ t = Tsg.cog := by decide

/-- Una expresión ecuménica para i₂ (p_c) no porta significación cognoscitiva. -/
theorem nicea_ecum : ∀ x : Fin 5, NiceaW.Ec x (1 : Fin 2) → ¬ NiceaW.tpx x Tsg.cog := by decide

/-- Comunidades plenas (Pl no es obligatoria en la ley; aquí se cumple). -/
theorem nicea_Pl : NiceaW.Pl (0 : Fin 2) ∧ NiceaW.Pl (1 : Fin 2) := by decide

/-- Sc(i₁) = {k₀, k₁, k₂}; Sc(i₂) = {k₁, k₂, k₃}. -/
theorem nicea_Sc : (∀ k : Fin 4, NiceaW.Sc (0 : Fin 2) k ↔ k.val ≤ 2) ∧
    (∀ k : Fin 4, NiceaW.Sc (1 : Fin 2) k ↔ 1 ≤ k.val) := by decide

/-- Sin imposición cultural: ninguna expresión entregada es una imposición (consecuencia de L1). -/
theorem nicea_sin_imposicion : ∀ s : Fin 3, s.val ≤ 1 → ∀ c : Fin 3, ∀ l : Fin 1, ∀ x : Fin 5, ∀ a : Fin 6,
    NiceaW.ntg s c l x → ¬ NiceaW.Ipc x c a := by decide

/-- E8(s) ≠ ∅ para s ∈ Sis: s da fruto. -/
theorem nicea_Fr : ∀ s : Fin 3, E7.NiceaZ.Sis s → NiceaW.Fr s := by
  intro s hs
  have h : s.val ≤ 1 := (E7.nicea_Sis s).1 hs
  refine ⟨(0 : Fin 5), (0 : Fin 2), (0 : Fin 3), (0 : Fin 1), (0 : Fin 2), (0 : Fin 1), hs, ?_, ?_, ?_⟩
  · exact (show ∀ s : Fin 3, s.val ≤ 1 → NiceaW.ntg s (0 : Fin 3) (0 : Fin 1) (0 : Fin 5) by decide) s h
  · decide
  · decide

/-- s_A (no posición) no produce mensajes. -/
theorem nicea_sA_sin_salida : ∀ x m c l g t, ¬ NiceaW.Out 2 x m c l g t :=
  fun _ _ _ _ _ _ => sin_Sis_sin_salida (fun hs => absurd ((E7.nicea_Sis 2).1 hs) (by decide))

/-- La misma doctrina d₄ llega a culturas distintas con expresiones distintas (evangelio ≠ vehículo). -/
theorem nicea_vehiculos : ∀ s : Fin 3, s.val ≤ 1 →
    (∃ x : Fin 5, NiceaW.ntg s (0 : Fin 3) (0 : Fin 1) x ∧ NiceaW.iota x (4 : Fin 9)) ∧
    (∃ x : Fin 5, NiceaW.ntg s (1 : Fin 3) (0 : Fin 1) x ∧ NiceaW.iota x (4 : Fin 9)) ∧
    (∀ x : Fin 5, NiceaW.ntg s (0 : Fin 3) (0 : Fin 1) x → NiceaW.iota x (4 : Fin 9) →
      ¬ NiceaW.ntg s (1 : Fin 3) (0 : Fin 1) x) := by decide

/-! ### Mp ⊋ Mod: modelos bien tipados que violan UNA cláusula (s₆ = 0) -/

-- L1: x_c entregada a la cultura u (imposición cultural).
abbrev BadL1 : Mp E7.NiceaZ := { NiceaW with
    Cmp := fun a c => (a.val = 0 ∧ (c.val = 0 ∨ c.val = 1)) ∨ (a.val = 2 ∧ (c.val = 1 ∨ c.val = 2)),
    ntg := fun s c _ x => s.val ≤ 1 ∧
    ((c.val = 0 ∧ (x.val = 0 ∨ x.val = 2)) ∨ (c.val = 1 ∧ (x.val = 0 ∨ x.val = 1 ∨ x.val = 3)) ∨
     (c.val = 2 ∧ x.val = 4)) }
theorem bad_L1 : BadL1.Tipo ∧ ¬ BadL1.K1 0 := by decide
theorem bad_L1_imp : BadL1.Ipc (0 : Fin 5) (1 : Fin 3) (0 : Fin 6) := by decide

-- L2: la historia (esfera humana consultada) no se depura.
abbrev BadL2 : Mp E7.NiceaZ := { NiceaW with Pur := fun e => e.val = 1 }
theorem bad_L2 : BadL2.Tipo ∧ ¬ BadL2.K2 0 := by decide

-- L3: x_c afirma además d₁ (fuera de Dc_s).
abbrev BadL3a : Mp E7.NiceaZ := { NiceaW with iota := fun x d => x.val ≤ 1 ∧ (d.val = 4 ∨ (x.val = 0 ∧ d.val = 1)) }
theorem bad_L3a : BadL3a.Tipo ∧ ¬ BadL3a.K3 0 := by decide
-- L3: x_u sustituye d₄ por d₁: ι ≠ ∅ pero no conserva el núcleo.
abbrev BadL3b : Mp E7.NiceaZ := { NiceaW with iota := fun x d => (x.val = 0 ∧ d.val = 4) ∨ (x.val = 1 ∧ d.val = 1) }
theorem bad_L3b : BadL3b.Tipo ∧ ¬ BadL3b.K3 0 := by decide

-- L4: δ_n queda sin expresión (falta cobertura).
abbrev BadL4a : Mp E7.NiceaZ := { NiceaW with ntg := fun s c _ x => s.val ≤ 1 ∧
    ((c.val = 0 ∧ (x.val = 0 ∨ x.val = 2)) ∨ (c.val = 1 ∧ (x.val = 1 ∨ x.val = 3))) }
theorem bad_L4a : BadL4a.Tipo ∧ ¬ BadL4a.K4 0 := by decide
-- L4: δ_c solo recibe la doctrinal: el horizonte no receptivo ω_sd queda mal servido.
abbrev BadL4b : Mp E7.NiceaZ := { NiceaW with ntg := fun s c _ x => s.val ≤ 1 ∧
    ((c.val = 0 ∧ x.val = 0) ∨ (c.val = 1 ∧ (x.val = 1 ∨ x.val = 3)) ∨ (c.val = 2 ∧ x.val = 4)) }
theorem bad_L4b : BadL4b.Tipo ∧ ¬ BadL4b.K4 0 := by decide

-- L5: emisor sin conocimiento de s.
abbrev BadL5a : Mp E7.NiceaZ := { NiceaW with kn := fun _ _ => False }
theorem bad_L5a : BadL5a.Tipo ∧ ¬ BadL5a.K5 0 := by decide
-- L5: emisor cuyo horizonte no es receptivo (no vive el mensaje).
abbrev BadL5b : Mp E7.NiceaZ := { NiceaW with hzA := fun a => if a.val ≤ 2 ∧ a.val ≠ 0 then (2 : Fin 3) else (0 : Fin 3) }
theorem bad_L5b : BadL5b.Tipo ∧ ¬ BadL5b.K5 0 := by decide
-- L5: emisor que no practica lo efectivo.
abbrev BadL5c : Mp E7.NiceaZ := { NiceaW with prc := fun _ _ => False }
theorem bad_L5c : BadL5c.Tipo ∧ ¬ BadL5c.K5 0 := by decide
-- L5: emisor que no comprende la cultura del destinatario.
abbrev BadL5d : Mp E7.NiceaZ := { NiceaW with Cmp := fun _ _ => False }
theorem bad_L5d : BadL5d.Tipo ∧ ¬ BadL5d.K5 0 := by decide

-- L6: no hay confesión que sostenga la expresión (sin Iglesia).
abbrev BadL6a : Mp E7.NiceaZ := { NiceaW with mb := fun _ _ => False }
theorem bad_L6a : BadL6a.Tipo ∧ ¬ BadL6a.K6 0 := by decide
-- L6: x_c porta k₃, que el emisor a₀ tiene pero a₂ (también de i₁) no comparte.
abbrev BadL6b : Mp E7.NiceaZ := { NiceaW with
    cnv := fun a k => ((a.val = 0 ∨ a.val = 2) ∧ k.val ≤ 2) ∨ (a.val = 0 ∧ k.val = 3) ∨ (a.val = 1 ∧ 1 ≤ k.val),
    ctn := fun x k => (x.val ≤ 1 ∧ k.val ≤ 1) ∨ (x.val = 0 ∧ k.val = 3) ∨ (2 ≤ x.val ∧ k.val = 2) }
theorem bad_L6b : BadL6b.Tipo ∧ ¬ BadL6b.K6 0 := by decide

-- L7: una expresión ecuménica con contenido cognoscitivo (x_c para i₂).
abbrev BadL7 : Mp E7.NiceaZ := { NiceaW with Ec := fun x j => x.val = 0 ∧ j.val = 1 }
theorem bad_L7 : BadL7.Tipo ∧ ¬ BadL7.K7 0 := by decide

-- L8: ningún medio adecuado para las doctrinales.
abbrev BadL8 : Mp E7.NiceaZ := { NiceaW with Adp := fun x m => 2 ≤ x.val ∧ m.val = 1 }
theorem bad_L8 : BadL8.Tipo ∧ ¬ BadL8.K8 0 := by decide

/-- Cada contraejemplo viola solo su cláusula: las otras siete se cumplen en s₆. -/
theorem bad_L1_aislada : BadL1.K2 0 ∧ BadL1.K3 0 ∧ BadL1.K4 0 ∧ BadL1.K5 0 ∧ BadL1.K6 0 ∧ BadL1.K7 0 ∧ BadL1.K8 0 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
theorem bad_L2_aislada : BadL2.K1 0 ∧ BadL2.K3 0 ∧ BadL2.K4 0 ∧ BadL2.K5 0 ∧ BadL2.K6 0 ∧ BadL2.K7 0 ∧ BadL2.K8 0 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
theorem bad_L3a_aislada : BadL3a.K1 0 ∧ BadL3a.K2 0 ∧ BadL3a.K4 0 ∧ BadL3a.K5 0 ∧ BadL3a.K6 0 ∧ BadL3a.K7 0 ∧ BadL3a.K8 0 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
theorem bad_L3b_aislada : BadL3b.K1 0 ∧ BadL3b.K2 0 ∧ BadL3b.K4 0 ∧ BadL3b.K5 0 ∧ BadL3b.K6 0 ∧ BadL3b.K7 0 ∧ BadL3b.K8 0 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
theorem bad_L4a_aislada : BadL4a.K1 0 ∧ BadL4a.K2 0 ∧ BadL4a.K3 0 ∧ BadL4a.K5 0 ∧ BadL4a.K6 0 ∧ BadL4a.K7 0 ∧ BadL4a.K8 0 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
theorem bad_L4b_aislada : BadL4b.K1 0 ∧ BadL4b.K2 0 ∧ BadL4b.K3 0 ∧ BadL4b.K5 0 ∧ BadL4b.K6 0 ∧ BadL4b.K7 0 ∧ BadL4b.K8 0 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
theorem bad_L5a_aislada : BadL5a.K1 0 ∧ BadL5a.K2 0 ∧ BadL5a.K3 0 ∧ BadL5a.K4 0 ∧ BadL5a.K6 0 ∧ BadL5a.K7 0 ∧ BadL5a.K8 0 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
theorem bad_L5b_aislada : BadL5b.K1 0 ∧ BadL5b.K2 0 ∧ BadL5b.K3 0 ∧ BadL5b.K4 0 ∧ BadL5b.K6 0 ∧ BadL5b.K7 0 ∧ BadL5b.K8 0 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
theorem bad_L5c_aislada : BadL5c.K1 0 ∧ BadL5c.K2 0 ∧ BadL5c.K3 0 ∧ BadL5c.K4 0 ∧ BadL5c.K6 0 ∧ BadL5c.K7 0 ∧ BadL5c.K8 0 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
theorem bad_L5d_aislada : BadL5d.K1 0 ∧ BadL5d.K2 0 ∧ BadL5d.K3 0 ∧ BadL5d.K4 0 ∧ BadL5d.K6 0 ∧ BadL5d.K7 0 ∧ BadL5d.K8 0 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
theorem bad_L6a_aislada : BadL6a.K1 0 ∧ BadL6a.K2 0 ∧ BadL6a.K3 0 ∧ BadL6a.K4 0 ∧ BadL6a.K5 0 ∧ BadL6a.K7 0 ∧ BadL6a.K8 0 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
theorem bad_L6b_aislada : BadL6b.K1 0 ∧ BadL6b.K2 0 ∧ BadL6b.K3 0 ∧ BadL6b.K4 0 ∧ BadL6b.K5 0 ∧ BadL6b.K7 0 ∧ BadL6b.K8 0 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
theorem bad_L7_aislada : BadL7.K1 0 ∧ BadL7.K2 0 ∧ BadL7.K3 0 ∧ BadL7.K4 0 ∧ BadL7.K5 0 ∧ BadL7.K6 0 ∧ BadL7.K8 0 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
theorem bad_L8_aislada : BadL8.K1 0 ∧ BadL8.K2 0 ∧ BadL8.K3 0 ∧ BadL8.K4 0 ∧ BadL8.K5 0 ∧ BadL8.K6 0 ∧ BadL8.K7 0 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Cada contraejemplo viola una cláusula y por tanto no es modelo de la ley. -/
theorem bad_no_ley : ¬ Ley BadL1 ∧ ¬ Ley BadL2 ∧ ¬ Ley BadL3a ∧ ¬ Ley BadL4a ∧ ¬ Ley BadL5a ∧
    ¬ Ley BadL6a ∧ ¬ Ley BadL7 ∧ ¬ Ley BadL8 := by
  have h0 : E7.NiceaZ.Sis 0 := (E7.nicea_Sis 0).2 (by decide)
  exact ⟨fun L => bad_L1.2 (L.L1 0 h0), fun L => bad_L2.2 (L.L2 0 h0), fun L => bad_L3a.2 (L.L3 0 h0),
    fun L => bad_L4a.2 (L.L4 0 h0), fun L => bad_L5a.2 (L.L5 0 h0), fun L => bad_L6a.2 (L.L6 0 h0),
    fun L => bad_L7.2 (L.L7 0 h0), fun L => bad_L8.2 (L.L8 0 h0)⟩

end Nicea

/-! ## Segundo caso: la escolástica (SCG IV y ST)
  Sis = {SCG IV, ST} = {1, 2}; el Scriptum (0) no es posición. Dc_s = Nuc(s) = {d₄}; hz(s) = ω_cd.
  Mismo núcleo y mismo Rec(s), pero el sistema cambia QUIÉN puede emitir (kn) y qué se entrega a cada s.
  Culturas (Cu = Fin 2): 0 = universitaria escolástica, 1 = fieles sin formación. Una clase.
  Agentes (Prs = Fin 4): a₀ (cult. 0, ω_cd, conoce SCG IV), a₁ (cult. 0, ω_cd, conoce ST),
    a₂ (cult. 0, ω_cd, practica; comprende la cultura 1), a₃ (cult. 1, ω_sd).
  Expresiones (Ex = Fin 3): x₀ (SCG IV, doctrinal), x₁ (ST, doctrinal), p (preparatoria, cultura 1).
  Una sola confesión (Cmu = Fin 1): L7 se cumple vacuamente (Ec = ∅). -/
section Summa
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 8192

def sCul (a : Fin 4) : Fin 2 := if a.val = 3 then 1 else 0

abbrev SummaW : Mp E7.SummaZ where
  Esf := Fin 3
  Cu := Fin 2
  Csc := Fin 1
  Prs := Fin 4
  Ctn := Fin 3
  Cmu := Fin 1
  Ex := Fin 3
  Med := Fin 2
  Lug := Fin 2
  Tmp := Fin 1
  Nuc := fun s d => E7.SummaZ.Dcs s d
  rI := fun s _ => s.val ≠ 0
  hum := fun e => e.val ≤ 1
  Len := fun e c x => (x.val ≤ 1 ∧ c.val = 0 ∧ e.val = 2) ∨ (x.val = 2 ∧ c.val = 1 ∧ e.val ≤ 1)
  Pur := fun e => e.val ≤ 1
  Pob := fun c _ a => sCul a = c
  hzA := fun a => if a.val ≤ 2 then (2 : Fin 3) else (0 : Fin 3)
  nvs := fun k => if k.val = 0 then Nvs.jui else Nvs.val
  tpc := fun k => if k.val = 0 then Tsg.cog else if k.val = 1 then Tsg.con else Tsg.efe
  cnv := fun a _ => a.val ≤ 2
  mb := fun a _ => a.val ≤ 2
  Cpl := fun _ _ => False
  Igs := fun _ => True
  Prep := fun x => x.val = 2
  Ori := fun x s => x.val = 2 ∧ s.val ≠ 0
  iota := fun x d => x.val ≤ 1 ∧ d.val = 4
  ctn := fun x k => (x.val ≤ 1 ∧ k.val ≤ 1) ∨ (x.val = 2 ∧ k.val = 2)
  ntg := fun s c _ x => s.val ≠ 0 ∧
    ((c.val = 0 ∧ ((s.val = 1 ∧ x.val = 0) ∨ (s.val = 2 ∧ x.val = 1))) ∨ (c.val = 1 ∧ x.val = 2))
  Acs := fun t x _ _ w => (x.val ≤ 1 ∧ 1 ≤ w.val) ∨ (x.val = 2 ∧ t = Tsg.efe)
  Emi := fun x a => (x.val = 0 ∧ a.val = 0) ∨ (x.val = 1 ∧ a.val = 1) ∨ (x.val = 2 ∧ a.val = 2)
  kn := fun a s => (a.val = 0 ∧ s.val = 1) ∨ (a.val = 1 ∧ s.val = 2)
  prc := fun a k => a.val = 2 ∧ k.val = 2
  culA := sCul
  Cmp := fun a c => (a.val ≤ 1 ∧ c.val = 0) ∨ (a.val = 2 ∧ c.val = 1)
  Ec := fun _ _ => False
  Disp := fun g _ m => g.val = m.val
  Adp := fun x m => (x.val ≤ 1 ∧ m.val = 0) ∨ (x.val = 2 ∧ m.val = 1)

instance (a b : E7.SummaZ.Sy) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : SummaW.Esf → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : SummaW.Esf → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : SummaW.Esf) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : SummaW.Cu → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : SummaW.Cu → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : SummaW.Cu) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : SummaW.Csc → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : SummaW.Csc → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : SummaW.Csc) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : SummaW.Prs → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 4, p x))
instance (p : SummaW.Prs → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 4, p x))
instance (a b : SummaW.Prs) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 4) = b))
instance (p : SummaW.Ctn → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : SummaW.Ctn → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : SummaW.Ctn) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : SummaW.Cmu → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : SummaW.Cmu → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : SummaW.Cmu) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : SummaW.Ex → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : SummaW.Ex → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : SummaW.Ex) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : SummaW.Med → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : SummaW.Med → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : SummaW.Med) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : SummaW.Lug → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : SummaW.Lug → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : SummaW.Lug) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : SummaW.Tmp → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : SummaW.Tmp → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : SummaW.Tmp) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))

theorem summa_Tipo : SummaW.Tipo := by decide

theorem summa_Ley : Ley SummaW where
  L1 := fun s hs => (show ∀ s : Fin 3, s.val ≠ 0 → SummaW.K1 s by decide) s ((E7.summa_Sis s).1 hs)
  L2 := fun s hs => (show ∀ s : Fin 3, s.val ≠ 0 → SummaW.K2 s by decide) s ((E7.summa_Sis s).1 hs)
  L3 := fun s hs => (show ∀ s : Fin 3, s.val ≠ 0 → SummaW.K3 s by decide) s ((E7.summa_Sis s).1 hs)
  L4 := fun s hs => (show ∀ s : Fin 3, s.val ≠ 0 → SummaW.K4 s by decide) s ((E7.summa_Sis s).1 hs)
  L5 := fun s hs => (show ∀ s : Fin 3, s.val ≠ 0 → SummaW.K5 s by decide) s ((E7.summa_Sis s).1 hs)
  L6 := fun s hs => (show ∀ s : Fin 3, s.val ≠ 0 → SummaW.K6 s by decide) s ((E7.summa_Sis s).1 hs)
  L7 := fun s hs => (show ∀ s : Fin 3, s.val ≠ 0 → SummaW.K7 s by decide) s ((E7.summa_Sis s).1 hs)
  L8 := fun s hs => (show ∀ s : Fin 3, s.val ≠ 0 → SummaW.K8 s by decide) s ((E7.summa_Sis s).1 hs)

theorem Mod_noVacio_summa : ∃ W : Mp E7.SummaZ, W.Tipo ∧ Ley W := ⟨SummaW, summa_Tipo, summa_Ley⟩

/-- Mismo núcleo y mismo Rec: Rec(s) = {ω_cs, ω_cd} para SCG IV y ST. -/
theorem summa_Rcp : ∀ s : Fin 3, s.val ≠ 0 → ∀ w : Fin 3, (SummaW.Rcp s w ↔ w.val ≠ 0) := by decide

theorem summa_hz_rcp : ∀ s : Fin 3, E7.SummaZ.Sis s → SummaW.Rcp s (E7.SummaZ.hzs s) :=
  fun _ hs => hz_rcp summa_Tipo hs

/-- Lo que se entrega depende del sistema: x₀ solo para SCG IV, x₁ solo para ST. -/
theorem summa_sistema_importa :
    SummaW.ntg (1 : Fin 3) (0 : Fin 2) (0 : Fin 1) (0 : Fin 3) ∧ ¬ SummaW.ntg (2 : Fin 3) (0 : Fin 2) (0 : Fin 1) (0 : Fin 3) ∧
    SummaW.ntg (2 : Fin 3) (0 : Fin 2) (0 : Fin 1) (1 : Fin 3) ∧ ¬ SummaW.ntg (1 : Fin 3) (0 : Fin 2) (0 : Fin 1) (1 : Fin 3) := by decide

/-- ... y quién puede emitirlo: el emisor de x₀ conoce SCG IV pero no ST. -/
theorem summa_kn : SummaW.kn (0 : Fin 4) (1 : Fin 3) ∧ ¬ SummaW.kn (0 : Fin 4) (2 : Fin 3) ∧
    SummaW.kn (1 : Fin 4) (2 : Fin 3) ∧ ¬ SummaW.kn (1 : Fin 4) (1 : Fin 3) := by decide

/-- La cultura 1 (fieles sin formación) solo recibe lo preparatorio: su único horizonte es ω_sd. -/
theorem summa_pueblo : ∀ s : Fin 3, s.val ≠ 0 → ∀ x : Fin 3, SummaW.ntg s (1 : Fin 2) (0 : Fin 1) x →
    SummaW.Prep x ∧ ¬ SummaW.tpx x Tsg.cog := by decide

theorem summa_Fr : ∀ s : Fin 3, E7.SummaZ.Sis s → SummaW.Fr s := by
  intro s hs
  have h : s.val ≠ 0 := (E7.summa_Sis s).1 hs
  refine ⟨(2 : Fin 3), (1 : Fin 2), (1 : Fin 2), (0 : Fin 1), (1 : Fin 2), (0 : Fin 1), hs, ?_, ?_, ?_⟩
  · exact (show ∀ s : Fin 3, s.val ≠ 0 → SummaW.ntg s (1 : Fin 2) (0 : Fin 1) (2 : Fin 3) by decide) s h
  · decide
  · decide

theorem summa_Scriptum_sin_salida : ∀ x m c l g t, ¬ SummaW.Out 0 x m c l g t :=
  fun _ _ _ _ _ _ => sin_Sis_sin_salida (fun hs => absurd ((E7.summa_Sis 0).1 hs) (by decide))

/-! ### Contraejemplos del caso (s = 1, la SCG IV) -/
-- L5: x₀ emitida por quien conoce la ST pero no la SCG IV.
abbrev SBadL5 : Mp E7.SummaZ := { SummaW with
  Emi := fun x a => (x.val = 0 ∧ a.val = 1) ∨ (x.val = 1 ∧ a.val = 1) ∨ (x.val = 2 ∧ a.val = 2) }
theorem sbad_L5 : SBadL5.Tipo ∧ ¬ SBadL5.K5 1 := by decide

-- L4: la cultura 1 recibe la doctrinal (no receptivo servido con doctrina).
abbrev SBadL4 : Mp E7.SummaZ := { SummaW with
  ntg := fun s c _ x => s.val ≠ 0 ∧
    ((c.val = 0 ∧ ((s.val = 1 ∧ x.val = 0) ∨ (s.val = 2 ∧ x.val = 1))) ∨ (c.val = 1 ∧ x.val = 0)) }
theorem sbad_L4 : ¬ SBadL4.K4 1 := by decide

-- L1: x₀ entregada a la cultura 1 (imposición cultural).
abbrev SBadL1 : Mp E7.SummaZ := { SummaW with
  ntg := fun s c _ x => s.val ≠ 0 ∧
    ((c.val = 0 ∧ ((s.val = 1 ∧ x.val = 0) ∨ (s.val = 2 ∧ x.val = 1))) ∨ (c.val = 1 ∧ (x.val = 2 ∨ x.val = 0))) }
theorem sbad_L1 : ¬ SBadL1.K1 1 := by decide

-- L3: x₀ no conserva el núcleo (ι = ∅ sin ser preparatoria).
abbrev SBadL3 : Mp E7.SummaZ := { SummaW with iota := fun x d => x.val = 1 ∧ d.val = 4 }
theorem sbad_L3 : ¬ SBadL3.K3 1 := by decide

end Summa
end E8
