import E2
import E3
/-
  E4 · Dialéctica — verificación en Lean 4 (sin Mathlib, sin sorry).
  Traduce la tupla, Mp(E4), la ley de diez cláusulas y los dos modelos actuales
  (la Reforma y la teología de la liberación) del documento E4.
  Convenciones:
   - PV, I (ítems de Nr, R2, R3, In) son parámetros: no dependen de q.
   - Todo lo que depende de q (Dsc, Afn, red, cls, ot, Odl3, Relación, B) vive en `Mp PV I`;
     la familia {E4_q} es `Perfil → Mp PV I`.
   - rel = Relación = Odl2; Cmp a b := (rel a b).isSome.
   - π: PV → Base es la proyección a la base; Base y π son campos de Mp y la cláusula (iii)
     los caracteriza: π a = π b ↔ a, b equivalentes por la cerradura de «complementaria».
   - Los elementos de CT, Ep, Mf, Et, Vr son primitivos (Lonergan no los enumera).
   - La interfaz con E2 y E3 usa las estructuras reales (E2.Mp, E3.Mp).

  Citas de Lonergan: Método en teología, Sígueme, Salamanca 1988, cap. 10 «Dialéctica» (pp. 229–259).
  Etiquetas: [T] lo dice el texto · [L] lectura formal propia · [E] estipulación de modelado.
  Verificado ≠ auditado: Lean comprueba la consistencia de los modelos; el vínculo con el texto es interpretación.
  Tabla completa en el apartado «Concordancia con el texto de Lonergan» del documento E4.
   - p. 229 [T] «No toda oposición es dialéctica»; solo cuentan los conflictos fundamentales → `Sel`, cláusula (ii).
   - p. 229 [T] los conflictos vienen de una teoría del conocimiento, una actitud ética, una visión religiosa → `car`, `cvi/cvm/cvr`.
   - p. 230 [T] diferencias de horizonte complementarias, genéticas o dialécticas → `Rel`.
   - p. 231 [T] conversión «se sale del anterior al repudiar sus rasgos»; pp. 232–234 las tres conversiones → `Pc`, (vii).
   - p. 241 [T] «las diferencias dialécticas implican un rechazo mutuo»; «ocho tipos» → (vi), (vii), `Perfil`.
   - p. 243 [T] dos niveles (operadores/materiales); reunir, completar, comparar, reducir, clasificar, seleccionar
     → `Mp`, `Ms`, `Dsc/Afn`, `red`, `cls`, `ot`, `Sel`; «los resultados no serán uniformes» → familia {E4_q}, (viii).
   - pp. 243–244 [T] desarrollar posiciones, hacer retroceder contraposiciones → `Ms`, `VisS`; p. 244 [T] última objetivación → (viii).
   - p. 245 [T] «ocho maneras»; p. 246 [T] elementos de prueba sobre la realización personal → `Yo`, `sost`, `ind`.
   - p. 247 [T] el teólogo no prueba ni refuta: ningún veredicto de verdad sobre las bases (no hay tal campo en `Mp`).
   - p. 250 [T] cuatro campos de significación → `Cs`, `df`; p. 254 [T] cadena gnoseológica-epistemológica-metafísica → `CohX`, (x).
-/
namespace E4

/-- Decidibilidad de ∃ sobre Fin n (sin Mathlib). -/
instance decExistsFin (n : Nat) (p : Fin n → Prop) [DecidablePred p] : Decidable (∃ i, p i) :=
  decidable_of_iff (∃ i, ∃ h : i < n, p ⟨i, h⟩) (by
    constructor
    · rintro ⟨i, h, hp⟩; exact ⟨⟨i, h⟩, hp⟩
    · rintro ⟨⟨i, h⟩, hp⟩; exact ⟨i, h, hp⟩)

/-! ## Tipos enumerados -/
-- Rel: p. 230 [T] complementarias, genéticas, dialécticas (anterior/posterior = genéticas; irreductible = dialécticas) [L].
-- Op: p. 243 [T] conflictos de datos, de perspectiva y de horizonte; solo el horizonte es dialéctico.
-- Acc: p. 243 [T] hacer retroceder = eliminar los elementos incompatibles; posponer y consagrar atención son [L] (cap. 5).
-- Cs: p. 250 [T] los cuatro campos de significación.
inductive Rel | irreductible | complementaria | anterior | posterior deriving DecidableEq
inductive Op | datos | perspectiva | horizonte deriving DecidableEq
inductive Acc | eliminar | posponer | consagrar_atencion deriving DecidableEq
inductive Cs | sentido_comun | teoria | interioridad | trascendencia deriving DecidableEq

/-- Converso de Relación: anterior ↔ posterior; irreductible y complementaria son simétricas. -/
def Rel.conv : Rel → Rel
  | .anterior => .posterior
  | .posterior => .anterior
  | r => r

theorem Rel.conv_conv (r : Rel) : r.conv.conv = r := by cases r <;> rfl

abbrev Perfil := Bool × Bool × Bool

/-- Cerradura transitiva. -/
inductive TG {α : Type} (r : α → α → Prop) : α → α → Prop
  | base {a b} : r a b → TG r a b
  | step {a b c} : TG r a b → r b c → TG r a c

theorem TG.irrefl_of_rank {α : Type} (r : α → α → Prop) (rk : α → Nat)
    (h : ∀ a b, r a b → rk a < rk b) : ∀ a, ¬ TG r a a := by
  have key : ∀ a b, TG r a b → rk a < rk b := by
    intro a b t
    induction t with
    | base hr => exact h _ _ hr
    | step _ hr ih => exact Nat.lt_trans ih (h _ _ hr)
  intro a t
  exact Nat.lt_irrefl _ (key a a t)

/-! ## Modelo potencial Mp(E4): solo tipos -/
structure Mp (PV I : Type) where
  -- Carácter: PV → X × Et × Vr, con X = CT × Ep × Mf
  CT : Type
  Ep : Type
  Mf : Type
  Et : Type
  Vr : Type
  car : PV → (CT × Ep × Mf) × Et × Vr
  cvi : CT × Ep × Mf → Bool
  cvm : Et → Bool
  cvr : Vr → Bool
  sgE : CT → Ep → Prop
  sgM : CT × Ep → Mf → Prop
  -- crítica y comparación
  Odl3 : PV → Prop                    -- coherente
  rel : PV → PV → Option Rel          -- Relación (= Odl2); Cmp := isSome
  -- lo contradictorio: Dsc, Afn y las seis operaciones
  Dsc : I → I → Prop
  Afn : I → I → Prop
  Rz : Type
  red : I → I → Rz
  cls : Rz → Op → Prop
  ot : I → I → Op → Prop
  V : I → PV → Prop
  -- valoraciones, sujetos, campos de significación
  Va : Type
  vl4 : I → Va → Prop
  sgV : Va → Bool                     -- positivo / negativo
  Yo : Type
  sost : Yo → PV → Prop
  df : PV → Cs → Prop
  -- codominio: bases
  Base : Type
  π : PV → Base
  -- condiciones de tipo
  dsc_afn_disj : ∀ a b, ¬ (Dsc a b ∧ Afn a b)
  cls_ne : ∀ z, ∃ o, cls z o

namespace Mp
variable {PV I : Type} (M : Mp PV I)

/-- Pc := cv ∘ Carácter -/
abbrev Pc (p : PV) : Bool × Bool × Bool :=
  (M.cvi (M.car p).1, M.cvm (M.car p).2.1, M.cvr (M.car p).2.2)

/-- Coh_X -/
abbrev CohX (x : M.CT × M.Ep × M.Mf) : Prop := M.sgE x.1 x.2.1 ∧ M.sgM (x.1, x.2.1) x.2.2

/-- Sel(x) := {d ∈ Dsc ∪ Afn : horizonte ∈ ot(d)} -/
abbrev Sel (a b : I) : Prop := (M.Dsc a b ∨ M.Afn a b) ∧ M.ot a b Op.horizonte

/-- ind(y) -/
abbrev ind (y : M.Yo) (c : Bool × Bool × Bool) : Prop := ∃ p, M.sost y p ∧ M.Pc p = c

/-- Cerradura reflexiva, simétrica y transitiva de «complementaria» sobre PVc. -/
inductive EqC : PV → PV → Prop
  | refl {a} : M.Odl3 a → EqC a a
  | step {a b} : M.Odl3 a → M.Odl3 b → M.rel a b = some Rel.complementaria → EqC a b
  | symm {a b} : EqC a b → EqC b a
  | trans {a b c} : EqC a b → EqC b c → EqC a c

/-- ≈ sobre las bases -/
abbrev aprx (x y : M.Base) : Prop :=
  ∃ a b, M.Odl3 a ∧ M.Odl3 b ∧ M.π a = x ∧ M.π b = y ∧ M.rel a b = some Rel.irreductible
/-- ≺ sobre las bases -/
abbrev prec (x y : M.Base) : Prop :=
  ∃ a b, M.Odl3 a ∧ M.Odl3 b ∧ M.π a = x ∧ M.π b = y ∧ M.rel a b = some Rel.anterior

/-- Pos_q(b), sobre un representante. -/
abbrev PosB (q : Perfil) (x : M.Base) : Prop := ∃ a, M.Odl3 a ∧ M.π a = x ∧ M.Pc a = q

/-- Vis_q, leída sobre PV: soporte (𝔅⁺_q) y las restricciones de ≈ y ≺. -/
abbrev VisS (q : Perfil) (a : PV) : Prop := M.Odl3 a ∧ M.Pc a = q
abbrev VisA (q : Perfil) (a b : PV) : Prop := M.VisS q a ∧ M.VisS q b ∧ M.aprx (M.π a) (M.π b)
abbrev VisP (q : Perfil) (a b : PV) : Prop := M.VisS q a ∧ M.VisS q b ∧ M.prec (M.π a) (M.π b)

/-- Lecturas sobre PV de B (para comparar B_q con B_q′). -/
abbrev sameB (a b : PV) : Prop := M.Odl3 a ∧ M.Odl3 b ∧ M.π a = M.π b
abbrev aprxP (a b : PV) : Prop := M.Odl3 a ∧ M.Odl3 b ∧ M.aprx (M.π a) (M.π b)
abbrev precP (a b : PV) : Prop := M.Odl3 a ∧ M.Odl3 b ∧ M.prec (M.π a) (M.π b)

end Mp

/-- Discrepancia entre B_q y B_q′. -/
def BDiff {PV I : Type} (M M' : Mp PV I) : Prop :=
  ∃ a b, ¬ (M.sameB a b ↔ M'.sameB a b) ∨ ¬ (M.aprxP a b ↔ M'.aprxP a b)
    ∨ ¬ (M.precP a b ↔ M'.precP a b)

/-- Discrepancia entre Vis_q (en M) y Vis_q′ (en M′). -/
def VisDiff {PV I : Type} (M M' : Mp PV I) (q q' : Perfil) : Prop :=
  ∃ a b, ¬ (M.VisS q a ↔ M'.VisS q' a) ∨ ¬ (M.VisA q a b ↔ M'.VisA q' a b)
    ∨ ¬ (M.VisP q a b ↔ M'.VisP q' a b)

/-! ## La ley de E4: diez cláusulas -/
-- Cada cláusula lleva su cita: [T] texto, [L] lectura, [E] estipulación.
structure Ley {PV I : Type} (M : Mp PV I) : Prop where
  /-- (i) Odl2 = Relación: Odl2 es `rel` por definición. Se recoge aquí la forma del converso.
      p. 230 [T] anterior/posterior (genéticas); la simetría de las otras dos es [L]. -/
  L1 : ∀ a b, M.rel b a = (M.rel a b).map Rel.conv
  /-- (ii) Odl1 compara solo la manifestación en PV de Sel, sobre puntos de vista coherentes.
      p. 229 [T] «no toda oposición es dialéctica»; p. 243 [T] seleccionar = «escoger las afinidades y oposiciones
      fundadas en horizontes dialécticamente opuestos». -/
  L2 : ∀ a b, (M.rel a b).isSome →
        M.Odl3 a ∧ M.Odl3 b ∧ ∃ i j, (M.Sel i j ∨ M.Sel j i) ∧ M.V i a ∧ M.V j b
  /-- (iii)–(iv) 𝔅 es la partición de PVc por la cerradura de «complementaria».
      p. 243 [T] reunir y comparar; la partición y la cerradura son [L]. -/
  L3a : ∀ x : M.Base, ∃ a, M.Odl3 a ∧ M.π a = x
  L3b : ∀ a b, M.Odl3 a → M.Odl3 b → (M.π a = M.π b ↔ M.EqC a b)
  /-- (vi) consistencia. p. 241 [T] las diferencias dialécticas implican un rechazo mutuo; el resto es [L]. -/
  L6a : ∀ a b, M.Odl3 a → M.Odl3 b → M.rel a b = some Rel.irreductible → M.π a ≠ M.π b
  L6b : ∀ x y, ¬ (M.aprx x y ∧ M.prec x y)
  L6c : ∀ x, ¬ TG M.prec x x
  /-- (vii) horizonte y conversión. pp. 231, 241 [T] la conversión repudia el horizonte anterior; las
      diferencias complementarias o genéticas pueden superarse; la forma de la implicación es [L]. -/
  L7 : ∀ a b r, M.rel a b = some r → r ≠ Rel.irreductible → M.Pc a = M.Pc b
  /-- (ix) raíces: ot = cls ∘ red. p. 243 [T] reducir («ir a la raíz subyacente») y clasificar; la composición es [L]. -/
  L9 : ∀ a b o, M.ot a b o ↔ M.cls (M.red a b) o
  /-- (x) cadena filosófica. p. 254 [T] gnoseológica, epistemológica y metafísica en orden («prioridad lógica»);
      solo condición suficiente [L]. -/
  L10 : ∀ p, ¬ M.CohX (M.car p).1 → ¬ M.Odl3 p

/-- (v) Mₛ: Odl3(crist). pp. 243–244 [T] desarrollar posiciones y hacer retroceder contraposiciones
    (eliminar sus elementos incompatibles); la asignación eliminar/posponer/consagrar atención es [L]. -/
structure Ms {PV I : Type} (M : Mp PV I) where
  pv : PV → Option Acc
  edge : M.Base → M.Base → Option Acc

structure LeyMs {PV I : Type} {M : Mp PV I} (S : Ms M) : Prop where
  elim : ∀ p, (¬ M.Odl3 p → S.pv p = some Acc.eliminar) ∧ (M.Odl3 p → S.pv p = none)
  arista : ∀ x y, (S.edge x y).isSome ↔ M.aprx x y
  tipo : ∀ x y, S.edge x y ≠ some Acc.eliminar
  sim : ∀ x y, S.edge x y = S.edge y x

/-! ## Consecuencias generales de la ley -/
section Consecuencias
variable {PV I : Type} {M : Mp PV I}

theorem EqC_odl3 {a b : PV} (h : M.EqC a b) : M.Odl3 a ∧ M.Odl3 b := by
  induction h with
  | refl h => exact ⟨h, h⟩
  | step h1 h2 _ => exact ⟨h1, h2⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih1 ih2 => exact ⟨ih1.1, ih2.2⟩

theorem EqC_Pc (L : Ley M) {a b : PV} (e : M.EqC a b) : M.Pc a = M.Pc b := by
  induction e with
  | refl _ => rfl
  | step _ _ hr => exact L.L7 _ _ _ hr (by intro h; cases h)
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- (vii) ⇒ Pc está bien definido sobre 𝔅: dos puntos de vista de la misma base tienen el mismo Pc. -/
theorem pi_eq_Pc (L : Ley M) {a b : PV} (ha : M.Odl3 a) (hb : M.Odl3 b)
    (h : M.π a = M.π b) : M.Pc a = M.Pc b :=
  EqC_Pc L ((L.L3b a b ha hb).1 h)

/-- ≈ es simétrica (por el converso de Relación). -/
theorem aprx_symm (L : Ley M) {x y : M.Base} (h : M.aprx x y) : M.aprx y x := by
  obtain ⟨a, b, ha, hb, hx, hy, hr⟩ := h
  refine ⟨b, a, hb, ha, hy, hx, ?_⟩
  rw [L.L1 a b, hr]; rfl

/-- ≈ es irreflexiva: un enlace une siempre bases distintas. -/
theorem aprx_irrefl (L : Ley M) (x : M.Base) : ¬ M.aprx x x := by
  rintro ⟨a, b, ha, hb, hx, hy, hr⟩
  exact L.L6a a b ha hb hr (hx.trans hy.symm)

/-- anterior ⇔ converso posterior. -/
theorem anterior_posterior (L : Ley M) (a b : PV) :
    M.rel a b = some Rel.anterior ↔ M.rel b a = some Rel.posterior := by
  constructor
  · intro h; rw [L.L1 a b, h]; rfl
  · intro h
    have := L.L1 b a
    rw [h] at this
    exact this

/-- ≺ conserva Pc: la sucesión genética no cruza una conversión. -/
theorem prec_Pc (L : Ley M) {x y : M.Base} (h : M.prec x y) {a b : PV}
    (ha : M.Odl3 a) (hb : M.Odl3 b) (hx : M.π a = x) (hy : M.π b = y) : M.Pc a = M.Pc b := by
  obtain ⟨a', b', ha', hb', hx', hy', hr⟩ := h
  have h1 : M.Pc a = M.Pc a' := pi_eq_Pc L ha ha' (hx.trans hx'.symm)
  have h2 : M.Pc b = M.Pc b' := pi_eq_Pc L hb hb' (hy.trans hy'.symm)
  have h3 : M.Pc a' = M.Pc b' := L.L7 a' b' _ hr (by intro h; cases h)
  exact h1.trans (h3.trans h2.symm)

/-- ≺ es asimétrica (su cerradura es irreflexiva). -/
theorem prec_asymm (L : Ley M) {x y : M.Base} (h : M.prec x y) : ¬ M.prec y x :=
  fun h' => L.L6c x (TG.step (TG.base h) h')

/-- Pos_q está bien definida sobre 𝔅. -/
theorem PosB_iff (L : Ley M) (q : Perfil) (x : M.Base) :
    M.PosB q x ↔ ∀ a, M.Odl3 a → M.π a = x → M.Pc a = q := by
  constructor
  · rintro ⟨a, ha, hx, hq⟩ b hb hbx
    exact (pi_eq_Pc L hb ha (hbx.trans hx.symm)).trans hq
  · intro h
    obtain ⟨a, ha, hx⟩ := L.L3a x
    exact ⟨a, ha, hx, h a ha hx⟩

/-- Todo par comparado es de horizonte: los conflictos de solo datos o perspectiva no entran a Cmp. -/
theorem cmp_horizonte (L : Ley M) {a b : PV} (h : (M.rel a b).isSome) :
    ∃ i j, M.ot i j Op.horizonte ∧ (M.Dsc i j ∨ M.Afn i j ∨ M.Dsc j i ∨ M.Afn j i) := by
  obtain ⟨_, _, i, j, hs, _, _⟩ := L.L2 a b h
  rcases hs with ⟨hd, ho⟩ | ⟨hd, ho⟩
  · exact ⟨i, j, ho, by rcases hd with hd | hd <;> simp [hd]⟩
  · exact ⟨j, i, ho, by rcases hd with hd | hd <;> simp [hd]⟩

/-- Un punto de vista incoherente por la cadena filosófica no está en ninguna base. -/
theorem incoherente_de_X (L : Ley M) (p : PV) (h : ¬ M.CohX (M.car p).1) : ¬ M.Odl3 p :=
  L.L10 p h

/-- Con la ley, ninguna base contiene un par irreductible. -/
theorem base_sin_irreductible (L : Ley M) {a b : PV} (ha : M.Odl3 a) (hb : M.Odl3 b)
    (h : M.π a = M.π b) : M.rel a b ≠ some Rel.irreductible :=
  fun hr => L.L6a a b ha hb hr h

end Consecuencias

/-! ## Interfaz con E2 y E3 (estructuras reales) -/
-- p. 243 [T] reunir «las investigaciones realizadas, las interpretaciones propuestas, las explicaciones históricas».
-- Fc, R3 ⊆ Nr y la simetría de Inc (H4.1) son [E].
section Interfaz

/-- R2 := Im(E2): los resultados de la interpretación. -/
def R2 {W X1 X2 X3 H S R Q : Type} (x : E2.Mp W X1 X2 X3 H S R Q) : Type :=
  {r : R // ∃ w, x.E2 w = r}

/-- M := Fc ⊆ Mv: los movimientos cristianos que E3 exporta. -/
def Mcr (M3 : E3.Mp) : Type := {m : M3.Mv // M3.Fc m}

/-- R3 ⊆ Nr. -/
def R3E (M3 : E3.Mp) : Type := {n : M3.Nr // M3.R3 n}

theorem R3_sub_Nr (M3 : E3.Mp) (n : M3.Nr) (h : M3.R3 n) : ∃ r : R3E M3, r.val = n :=
  ⟨⟨n, h⟩, rfl⟩

/-- Cada interpretación del dominio es imagen de algún escrito. -/
theorem R2_img {W X1 X2 X3 H S R Q : Type} (x : E2.Mp W X1 X2 X3 H S R Q) (r : R2 x) :
    ∃ w, x.E2 w = r.val := r.property

/-- H4.1: Inc es simétrica (por ctr_sim), como exige que alimente a Dsc(Nr). -/
theorem Inc_sim (M3 : E3.Mp) (n n' : M3.Nr) (h : M3.Inc n n') : M3.Inc n' n := by
  obtain ⟨e, e', h1, h2, h3⟩ := h
  exact ⟨e', e, h2, h1, M3.ctr_sim _ _ h3⟩

end Interfaz


/-! ## Recursión de objetivaciones: Dom⁽¹⁾ y la cláusula (viii) -/
-- p. 244 [T] «una última objetivación del horizonte se realizará cuando los resultados del proceso precedente
-- sean considerados ellos mismos como materiales»; p. 243 [T] «los resultados no serán uniformes». Dom¹ es [L].
inductive It1 (I : Type) | old (i : I) | B (q : Perfil) | Vis (q : Perfil)

structure Dom1 (I : Type) where
  Dsc1 : It1 I → It1 I → Prop
  ot1 : It1 I → It1 I → Op → Prop

/-- (viii): las discrepancias entre B_q y B_q′, y entre Vis_q y Vis_q′, con q ≠ q′, entran a Dsc
    con horizonte ∈ ot. -/
structure LeyRec {PV I : Type} (Q : List Perfil) (Mq : Perfil → Mp PV I) (D : Dom1 I) : Prop where
  viii : ∀ q, q ∈ Q → ∀ q', q' ∈ Q → q ≠ q' →
    (BDiff (Mq q) (Mq q') → D.Dsc1 (.B q) (.B q') ∧ D.ot1 (.B q) (.B q') Op.horizonte) ∧
    (VisDiff (Mq q) (Mq q') q q' → D.Dsc1 (.Vis q) (.Vis q') ∧ D.ot1 (.Vis q) (.Vis q') Op.horizonte)

/-- La regla de Dom⁽¹⁾ por construcción: toda pareja de perfiles distintos entra a Dsc con horizonte. -/
def domRec (I : Type) : Dom1 I where
  Dsc1 x y := ∃ q q', q ≠ q' ∧ ((x = .B q ∧ y = .B q') ∨ (x = .Vis q ∧ y = .Vis q'))
  ot1 _ _ o := o = Op.horizonte

/-- Con un solo perfil no hay discrepancia que registrar: se recupera la ley anterior (n = 0). -/
theorem leyRec_unitaria {PV I : Type} (q : Perfil) (Mq : Perfil → Mp PV I) (D : Dom1 I) :
    LeyRec [q] Mq D := by
  refine ⟨?_⟩
  intro a ha b hb hne
  simp at ha hb
  exact absurd (ha.trans hb.symm) hne

theorem leyRec_domRec {PV I : Type} (Q : List Perfil) (Mq : Perfil → Mp PV I) :
    LeyRec Q Mq (domRec I) := by
  refine ⟨?_⟩
  intro q _ q' _ hne
  refine ⟨fun _ => ⟨⟨q, q', hne, Or.inl ⟨rfl, rfl⟩⟩, rfl⟩, fun _ => ⟨⟨q, q', hne, Or.inr ⟨rfl, rfl⟩⟩, rfl⟩⟩

/-! ## Verificación computable de la cláusula (iii) sobre PV = Fin n -/
section Reach
variable {n : Nat} {I : Type} (M : Mp (Fin n) I) [DecidablePred M.Odl3]

def cb (a b : Fin n) : Bool :=
  decide (M.Odl3 a) && decide (M.Odl3 b) && decide (M.rel a b = some Rel.complementaria)

def grow (S : List (Fin n)) : List (Fin n) :=
  S ++ (List.range n).filterMap (fun m =>
    if h : m < n then (if S.any (fun s => cb M s ⟨m, h⟩) then some ⟨m, h⟩ else none) else none)

def reach (a : Fin n) : Nat → List (Fin n)
  | 0 => [a]
  | k+1 => grow M (reach a k)

theorem reach_sound (a : Fin n) (ha : M.Odl3 a) : ∀ k s, s ∈ reach M a k → M.EqC a s := by
  intro k
  induction k with
  | zero =>
    intro s hs
    simp [reach] at hs
    subst hs
    exact Mp.EqC.refl ha
  | succ k ih =>
    intro s hs
    simp only [reach, grow, List.mem_append, List.mem_filterMap] at hs
    rcases hs with hs | ⟨m, _, hm⟩
    · exact ih s hs
    · by_cases h : m < n
      · rw [dif_pos h] at hm
        by_cases hany : (reach M a k).any (fun s => cb M s ⟨m, h⟩) = true
        · rw [if_pos hany] at hm
          cases hm
          obtain ⟨s', hs', hcb⟩ := List.any_eq_true.1 hany
          simp [cb] at hcb
          obtain ⟨⟨h1, h2⟩, h3⟩ := hcb
          exact Mp.EqC.trans (ih s' hs') (Mp.EqC.step h1 h2 h3)
        · rw [if_neg hany] at hm; cases hm
      · rw [dif_neg h] at hm; cases hm

omit [DecidablePred M.Odl3] in
/-- Si π respeta «complementaria», entonces respeta toda la cerradura EqC. -/
theorem EqC_pi (h : ∀ a b, M.Odl3 a → M.Odl3 b → M.rel a b = some Rel.complementaria → M.π a = M.π b)
    {a b : Fin n} (e : M.EqC a b) : M.π a = M.π b := by
  induction e with
  | refl _ => rfl
  | step h1 h2 h3 => exact h _ _ h1 h2 h3
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

end Reach


/-! ## Datos auxiliares para los modelos actuales -/
def mkRel (T : List (Nat × Nat × Rel)) (a b : Nat) : Option Rel :=
  match T.find? (fun t => t.1 == a && t.2.1 == b) with
  | some t => some t.2.2
  | none => (T.find? (fun t => t.1 == b && t.2.1 == a)).map (fun t => t.2.2.conv)

def inT (T : List (Nat × Nat × Nat)) (a b : Nat) : Bool := T.any (fun t => t.1 == a && t.2.1 == b)
def rootT (T : List (Nat × Nat × Nat)) (a b : Nat) : Nat :=
  ((T.find? (fun t => t.1 == a && t.2.1 == b)).map (fun t => t.2.2)).getD 0

/-- Raíces: z0, z1, z2 son de horizonte; z3 de datos; z4 de perspectiva. -/
def clsF (z : Nat) (o : Op) : Prop :=
  (z ≤ 2 ∧ o = Op.horizonte) ∨ (z = 3 ∧ o = Op.datos) ∨ (z = 4 ∧ o = Op.perspectiva)

instance (z : Nat) (o : Op) : Decidable (clsF z o) := by unfold clsF; infer_instance

theorem clsF_ne (z : Fin 5) : ∃ o, clsF z.val o := by
  have hz := z.isLt
  by_cases h1 : z.val ≤ 2
  · exact ⟨Op.horizonte, Or.inl ⟨h1, rfl⟩⟩
  · by_cases h2 : z.val = 3
    · exact ⟨Op.datos, Or.inr (Or.inl ⟨h2, rfl⟩)⟩
    · exact ⟨Op.perspectiva, Or.inr (Or.inr ⟨by omega, rfl⟩)⟩

def edgeT (T : List (Nat × Nat × Acc)) (a b : Nat) : Option Acc :=
  match T.find? (fun t => t.1 == a && t.2.1 == b) with
  | some t => some t.2.2
  | none => (T.find? (fun t => t.1 == b && t.2.1 == a)).map (fun t => t.2.2)

def dfT (T : List (Nat × Cs)) (p : Nat) (c : Cs) : Prop := (p, c) ∈ T

instance (T : List (Nat × Cs)) (p : Nat) (c : Cs) : Decidable (dfT T p c) := by
  unfold dfT; infer_instance

/-- Coordenadas: CT = Ep = Mf = Bool (true = rc, vj, mr), Et = Bool (true = at), Vr = Bool (true = gr).
    cv_i = 1 solo en (rc, vj, mr); Coh_X = {(rc, vj, mr), (emp, ve, mm)}. -/
def carF (L : List (Bool × Bool × Bool × Bool × Bool)) (p : Nat) :
    (Bool × Bool × Bool) × Bool × Bool :=
  let t := L.getD p (false, false, false, false, false)
  ((t.1, t.2.1, t.2.2.1), t.2.2.2.1, t.2.2.2.2)

/-! ## Modelo actual A: la Reforma (PV = Fin 15, ítems = Fin 17, bases = Fin 8 o Fin 9) -/
section Reforma
-- PV: j0..j3 = 0..3; j4, j5 = 4, 5 (caricaturas); w1 = 6; a1, a2 = 7, 8; s1, s2 = 9, 10;
--     c1..c4 = 11..14. Ítems: los 15 anteriores y i₁, i₂ = 15, 16 (conflicto de datos).

def refCar : List (Bool × Bool × Bool × Bool × Bool) :=
  [(true,true,true,true,true),(true,true,true,true,true),(true,true,true,true,true),(true,true,true,true,true),
   (true,true,true,false,true),(true,true,true,false,true),
   (true,false,true,true,true),
   (true,true,true,true,true),(true,true,true,true,true),(true,true,true,true,true),(true,true,true,true,true),
   (true,true,true,true,true),(true,true,true,true,true),(true,true,true,true,true),
   (false,false,false,true,false)]

def refInc : List Nat := [4, 5, 6]

def refDsc : List (Nat × Nat × Nat) :=
  [(0,1,0),(2,3,0),(1,3,0),(7,8,1),(9,10,1),(11,13,2),(12,13,2),(13,14,2),(11,12,4),(15,16,3)]
def refAfn : List (Nat × Nat × Nat) := [(1,2,0)]

def refRel1 : List (Nat × Nat × Rel) :=
  [(0,1,.anterior),(1,3,.complementaria),(2,3,.complementaria),(1,2,.complementaria),
   (11,13,.complementaria),(12,13,.complementaria),
   (7,8,.irreductible),(9,10,.irreductible),(13,14,.irreductible)]
def refRel2 : List (Nat × Nat × Rel) :=
  [(0,1,.anterior),(1,3,.complementaria),(2,3,.irreductible),(1,2,.irreductible),
   (11,13,.complementaria),(12,13,.complementaria),
   (7,8,.irreductible),(9,10,.irreductible),(13,14,.irreductible)]

def refPi1 : List Nat := [0,1,1,1,0,0,0,2,3,4,5,6,6,6,7]
def refPi2 : List Nat := [0,1,2,1,0,0,0,3,4,5,6,7,7,7,8]

def refVl4 : List (Nat × Nat) := [(11,0),(12,1)]
def refSost : List (Nat × Nat) :=
  [(0,0),(0,1),(0,7),(0,9),(1,2),(1,8),(1,10),(2,13),(3,14),(4,4),(4,5),(5,6)]
def refDf : List (Nat × Cs) :=
  [(0,.interioridad),(1,.interioridad),(1,.trascendencia),(2,.teoria),(3,.teoria),
   (7,.sentido_comun),(7,.teoria),(8,.sentido_comun),(8,.teoria)]

/-- La Reforma, parametrizada por la tabla de Relación (que depende de q) y por π. -/
abbrev refMp (relT : List (Nat × Nat × Rel)) (piL : List Nat) (k : Nat) : Mp (Fin 15) (Fin 17) where
  CT := Bool
  Ep := Bool
  Mf := Bool
  Et := Bool
  Vr := Bool
  car := fun p => carF refCar p.val
  cvi := fun x => decide (x = (true, true, true))
  cvm := fun b => b
  cvr := fun b => b
  sgE := fun c e => c = e
  sgM := fun x m => x.1 = m
  Odl3 := fun p => refInc.contains p.val = false
  rel := fun a b => mkRel relT a.val b.val
  Dsc := fun a b => inT refDsc a.val b.val = true
  Afn := fun a b => inT refAfn a.val b.val = true
  Rz := Fin 5
  red := fun a b => Fin.ofNat' 5 (rootT (refDsc ++ refAfn) a.val b.val)
  cls := fun z o => clsF z.val o
  ot := fun a b o => clsF (Fin.ofNat' 5 (rootT (refDsc ++ refAfn) a.val b.val)).val o
  V := fun i p => i.val = p.val
  Va := Fin 2
  vl4 := fun i v => (i.val, v.val) ∈ refVl4
  sgV := fun v => decide (v.val = 0)
  Yo := Fin 6
  sost := fun y p => (y.val, p.val) ∈ refSost
  df := fun p c => dfT refDf p.val c
  Base := Fin (k + 1)
  π := fun p => Fin.ofNat' (k + 1) (piL.getD p.val 0)
  dsc_afn_disj := by decide
  cls_ne := clsF_ne

abbrev Ref1 := refMp refRel1 refPi1 7
abbrev Ref2 := refMp refRel2 refPi2 8

end Reforma


def refEdge1 : List (Nat × Nat × Acc) := [(2,3,.consagrar_atencion),(4,5,.posponer),(6,7,.consagrar_atencion)]
def refEdge2 : List (Nat × Nat × Acc) :=
  [(1,2,.consagrar_atencion),(3,4,.consagrar_atencion),(5,6,.posponer),(7,8,.consagrar_atencion)]

section ReformaLey

theorem Ref1_ley : Ley Ref1 where
  L1 := by decide
  L2 := by decide
  L3a := by decide
  L3b := by
    intro a b ha hb
    constructor
    · intro h
      have key : ∀ a b : Fin 15, Ref1.Odl3 a → Ref1.Odl3 b → Ref1.π a = Ref1.π b → b ∈ reach Ref1 a 15 := by decide
      exact reach_sound Ref1 a ha 15 b (key a b ha hb h)
    · exact EqC_pi Ref1 (by decide)
  L6a := by decide
  L6b := by decide
  L6c := TG.irrefl_of_rank _ (fun x => x.val) (by decide)
  L7 := by
    have key : ∀ a b : Fin 15, (Ref1.rel a b).isSome → Ref1.rel a b ≠ some Rel.irreductible →
        Ref1.Pc a = Ref1.Pc b := by decide
    intro a b r hr hne
    have hs : (Ref1.rel a b).isSome = true := by rw [hr]; rfl
    exact key a b hs (by rw [hr]; intro h; exact hne (Option.some.inj h))
  L9 := fun _ _ _ => Iff.rfl
  L10 := by decide

def Ref1_ms : Ms Ref1 := ⟨fun p => if refInc.contains p.val then some Acc.eliminar else none,
  fun x y => edgeT refEdge1 x.val y.val⟩

theorem Ref1_leyMs : LeyMs Ref1_ms where
  elim := by decide
  arista := by decide
  tipo := by decide
  sim := by decide

theorem Ref2_ley : Ley Ref2 where
  L1 := by decide
  L2 := by decide
  L3a := by decide
  L3b := by
    intro a b ha hb
    constructor
    · intro h
      have key : ∀ a b : Fin 15, Ref2.Odl3 a → Ref2.Odl3 b → Ref2.π a = Ref2.π b → b ∈ reach Ref2 a 15 := by decide
      exact reach_sound Ref2 a ha 15 b (key a b ha hb h)
    · exact EqC_pi Ref2 (by decide)
  L6a := by decide
  L6b := by decide
  L6c := TG.irrefl_of_rank _ (fun x => x.val) (by decide)
  L7 := by
    have key : ∀ a b : Fin 15, (Ref2.rel a b).isSome → Ref2.rel a b ≠ some Rel.irreductible →
        Ref2.Pc a = Ref2.Pc b := by decide
    intro a b r hr hne
    have hs : (Ref2.rel a b).isSome = true := by rw [hr]; rfl
    exact key a b hs (by rw [hr]; intro h; exact hne (Option.some.inj h))
  L9 := fun _ _ _ => Iff.rfl
  L10 := by decide

def Ref2_ms : Ms Ref2 := ⟨fun p => if refInc.contains p.val then some Acc.eliminar else none,
  fun x y => edgeT refEdge2 x.val y.val⟩

theorem Ref2_leyMs : LeyMs Ref2_ms where
  elim := by decide
  arista := by decide
  tipo := by decide
  sim := by decide

end ReformaLey

/-! ## Modelo actual B: teología de la liberación (PV = Fin 12, ítems = Fin 14, bases = Fin 5) -/
section Liberacion
-- PV: d0 = 0, l1 = 1, l2 = 2, pr_rev = 3, pr_pas = 4, pr_his = 5, pr_cul = 6, am = 7, m84 = 8,
--     pf = 9, e1 = 10, e2 = 11. Ítems: los 12 anteriores y i₁, i₂ = 12, 13 (conflicto de datos).

def libCar : List (Bool × Bool × Bool × Bool × Bool) :=
  [(true,true,true,true,true),(true,true,true,true,true),(true,true,true,true,true),
   (true,true,true,true,true),(true,true,true,true,true),(true,true,true,true,true),
   (true,true,true,true,true),(true,true,true,true,true),(true,true,true,true,true),
   (false,false,false,true,false),
   (true,true,true,false,true),(true,true,true,false,true)]
def libInc : List Nat := [10, 11]
def libDsc : List (Nat × Nat × Nat) :=
  [(0,1,0),(1,2,0),(4,5,1),(5,6,1),(3,5,1),(2,5,1),(7,3,2),(7,8,2),(12,13,3)]
def libAfn : List (Nat × Nat × Nat) := [(9,2,2)]
def libRel : List (Nat × Nat × Rel) :=
  [(0,1,.anterior),(1,2,.anterior),(4,5,.complementaria),(5,6,.complementaria),
   (3,5,.complementaria),(2,5,.complementaria),(7,3,.complementaria),
   (7,8,.irreductible),(9,2,.irreductible)]
def libPi : List Nat := [0,1,2,2,2,2,2,2,3,4,0,0]
def libVl4 : List (Nat × Nat) := [(4,0),(8,1)]
def libSost : List (Nat × Nat) := [(0,4),(0,5),(0,2),(1,8),(2,9),(3,10),(3,11)]
def libDf : List (Nat × Cs) :=
  [(0,.sentido_comun),(0,.teoria),
   (1,.sentido_comun),(1,.teoria),(1,.trascendencia),
   (2,.sentido_comun),(2,.teoria),(2,.interioridad),(2,.trascendencia)]
def libEdge : List (Nat × Nat × Acc) := [(2,3,.consagrar_atencion),(2,4,.consagrar_atencion)]

abbrev Lib : Mp (Fin 12) (Fin 14) where
  CT := Bool
  Ep := Bool
  Mf := Bool
  Et := Bool
  Vr := Bool
  car := fun p => carF libCar p.val
  cvi := fun x => decide (x = (true, true, true))
  cvm := fun b => b
  cvr := fun b => b
  sgE := fun c e => c = e
  sgM := fun x m => x.1 = m
  Odl3 := fun p => libInc.contains p.val = false
  rel := fun a b => mkRel libRel a.val b.val
  Dsc := fun a b => inT libDsc a.val b.val = true
  Afn := fun a b => inT libAfn a.val b.val = true
  Rz := Fin 5
  red := fun a b => Fin.ofNat' 5 (rootT (libDsc ++ libAfn) a.val b.val)
  cls := fun z o => clsF z.val o
  ot := fun a b o => clsF (Fin.ofNat' 5 (rootT (libDsc ++ libAfn) a.val b.val)).val o
  V := fun i p => i.val = p.val
  Va := Fin 2
  vl4 := fun i v => (i.val, v.val) ∈ libVl4
  sgV := fun v => decide (v.val = 0)
  Yo := Fin 4
  sost := fun y p => (y.val, p.val) ∈ libSost
  df := fun p c => dfT libDf p.val c
  Base := Fin 5
  π := fun p => Fin.ofNat' 5 (libPi.getD p.val 0)
  dsc_afn_disj := by decide
  cls_ne := clsF_ne

theorem Lib_ley : Ley Lib where
  L1 := by decide
  L2 := by decide
  L3a := by decide
  L3b := by
    intro a b ha hb
    constructor
    · intro h
      have key : ∀ a b : Fin 12, Lib.Odl3 a → Lib.Odl3 b → Lib.π a = Lib.π b → b ∈ reach Lib a 12 := by decide
      exact reach_sound Lib a ha 12 b (key a b ha hb h)
    · exact EqC_pi Lib (by decide)
  L6a := by decide
  L6b := by decide
  L6c := TG.irrefl_of_rank _ (fun x => x.val) (by decide)
  L7 := by
    have key : ∀ a b : Fin 12, (Lib.rel a b).isSome → Lib.rel a b ≠ some Rel.irreductible →
        Lib.Pc a = Lib.Pc b := by decide
    intro a b r hr hne
    have hs : (Lib.rel a b).isSome = true := by rw [hr]; rfl
    exact key a b hs (by rw [hr]; intro h; exact hne (Option.some.inj h))
  L9 := fun _ _ _ => Iff.rfl
  L10 := by decide

def Lib_ms : Ms Lib := ⟨fun p => if libInc.contains p.val then some Acc.eliminar else none,
  fun x y => edgeT libEdge x.val y.val⟩

theorem Lib_leyMs : LeyMs Lib_ms where
  elim := by decide
  arista := by decide
  tipo := by decide
  sim := by decide

end Liberacion


/-! ## Lo que muestran los modelos -/
section Resultados

/-- H4.10 (hipótesis, fuera de la ley): anterior ⇒ df(a) ⊆ df(b).
    p. 250 [T] los cuatro campos son «horizontes genéticamente distintos»; la implicación es [E]. -/
def H410 {n : Nat} {I : Type} (M : Mp (Fin n) I) : Prop :=
  ∀ a b, M.rel a b = some Rel.anterior →
    (M.df a Cs.sentido_comun → M.df b Cs.sentido_comun) ∧ (M.df a Cs.teoria → M.df b Cs.teoria) ∧
    (M.df a Cs.interioridad → M.df b Cs.interioridad) ∧
    (M.df a Cs.trascendencia → M.df b Cs.trascendencia)

theorem Ref1_H410 : H410 Ref1 := by unfold H410; decide
theorem Ref2_H410 : H410 Ref2 := by unfold H410; decide
theorem Lib_H410 : H410 Lib := by unfold H410; decide

/-- Mod(E4) ≠ ∅: los tres modelos satisfacen la ley. -/
theorem Mod_noVacio : ∃ M : Mp (Fin 15) (Fin 17), Ley M := ⟨Ref1, Ref1_ley⟩
theorem Mod_noVacio_lib : ∃ M : Mp (Fin 12) (Fin 14), Ley M := ⟨Lib, Lib_ley⟩

/-- Los valores de Pc del caso (Reforma). -/
theorem Ref_Pc :
    Ref1.Pc 0 = (true, true, true) ∧ Ref1.Pc 14 = (false, true, false) ∧
    Ref1.Pc 4 = (true, false, true) ∧ Ref1.Pc 6 = (false, true, true) := by decide

/-- Incoherentes: w1 por la cadena filosófica (cláusula x); j4 por estereotipo, aunque su X es coherente. -/
theorem Ref_incoherentes :
    (¬ Ref1.CohX (Ref1.car 6).1 ∧ ¬ Ref1.Odl3 6) ∧ (Ref1.CohX (Ref1.car 4).1 ∧ ¬ Ref1.Odl3 4) := by
  decide

/-- Bases y enlaces de la Reforma para q = (1,1,1): ≈ y ≺ explícitas. -/
theorem Ref1_aprx : ∀ x y : Fin 8, Ref1.aprx x y ↔
    (x.val, y.val) ∈ [(2,3),(3,2),(4,5),(5,4),(6,7),(7,6)] := by decide
theorem Ref1_prec : ∀ x y : Fin 8, Ref1.prec x y ↔ (x.val, y.val) ∈ [(0,1)] := by decide
/-- Para q′ = (0,1,0), J se parte: aparecen las aristas j1–j2 (bases 1 y 2). -/
theorem Ref2_aprx : ∀ x y : Fin 9, Ref2.aprx x y ↔
    (x.val, y.val) ∈ [(1,2),(2,1),(3,4),(4,3),(5,6),(6,5),(7,8),(8,7)] := by decide
theorem Ref2_prec : ∀ x y : Fin 9, Ref2.prec x y ↔ (x.val, y.val) ∈ [(0,1)] := by decide
theorem Lib_aprx : ∀ x y : Fin 5, Lib.aprx x y ↔ (x.val, y.val) ∈ [(2,3),(3,2),(2,4),(4,2)] := by decide
theorem Lib_prec : ∀ x y : Fin 5, Lib.prec x y ↔ (x.val, y.val) ∈ [(0,1),(1,2)] := by decide

/-- Posiciones por perfil: 𝔅⁺ para q = (1,1,1) es todo salvo c4; para q = (0,1,0), solo c4. -/
theorem Ref_Pos111 : ∀ x : Fin 8, Ref1.PosB (true, true, true) x ↔ x.val ≠ 7 := by decide
theorem Ref_Pos010 : ∀ x : Fin 8, Ref1.PosB (false, true, false) x ↔ x.val = 7 := by decide
theorem Lib_Pos111 : ∀ x : Fin 5, Lib.PosB (true, true, true) x ↔ x.val ≠ 4 := by decide
theorem Lib_Pos010 : ∀ x : Fin 5, Lib.PosB (false, true, false) x ↔ x.val = 4 := by decide

/-- Los conflictos de datos (i₁–i₂) y de perspectiva (c1–c2) no están en Sel: no entran a Cmp. -/
theorem Ref_filtros : ¬ Ref1.Sel 15 16 ∧ ¬ Ref1.Sel 11 12 := by decide
theorem Lib_filtros : ¬ Lib.Sel 12 13 := by decide

/-- Indicios de realización personal: ind(y). -/
theorem Ref_ind : Ref1.ind 3 (false, true, false) ∧ Ref1.ind 4 (true, false, true) ∧
    Ref1.ind 0 (true, true, true) := by decide
theorem Lib_ind : Lib.ind 2 (false, true, false) ∧ Lib.ind 3 (true, false, true) := by decide

/-! ### La familia {E4_q} y la cláusula (viii) -/
-- Retorno E5 → E4 (cap. 5 §V, pp. 141–142, según ciclo/aristas_retorno.md): el perfil del horizonte elige E4_q.
def refQ : List Perfil := [(true, true, true), (false, true, false)]
def refFam : Perfil → Mp (Fin 15) (Fin 17) := fun q => if q = (true, true, true) then Ref1 else Ref2
def libFam : Perfil → Mp (Fin 12) (Fin 14) := fun _ => Lib

theorem ref_rec : LeyRec refQ refFam (domRec (Fin 17)) := leyRec_domRec _ _
theorem lib_rec : LeyRec refQ libFam (domRec (Fin 14)) := leyRec_domRec _ _

/-- En la Reforma, B_q ≠ B_q′ (J se parte para q′) y Vis_q ≠ Vis_q′. -/
theorem ref_BDiff : BDiff Ref1 Ref2 := ⟨2, 3, Or.inl (by decide)⟩
theorem ref_VisDiff : VisDiff Ref1 Ref2 (true, true, true) (false, true, false) :=
  ⟨14, 0, Or.inl (by decide)⟩
/-- En liberación, B_q = B_q′ pero Vis_q ≠ Vis_q′: la discrepancia aparece por las visiones. -/
theorem lib_B_igual : ¬ BDiff Lib Lib := by
  rintro ⟨a, b, h⟩
  rcases h with h | h | h <;> exact h Iff.rfl
theorem lib_VisDiff : VisDiff Lib Lib (true, true, true) (false, true, false) :=
  ⟨9, 0, Or.inl (by decide)⟩

/-! ### Mp ⊋ Mod: modelos bien tipados que NO satisfacen la ley -/
/-- (vi): un par irreductible dentro de una base. -/
def refRelBad : List (Nat × Nat × Rel) :=
  (1, 2, Rel.irreductible) :: (refRel1.filter (fun t => !(t.1 == 1 && t.2.1 == 2)))
theorem refBad_no_ley : ¬ Ley (refMp refRelBad refPi1 7) := by
  intro L
  have h := L.L6a 1 2 (by decide) (by decide) (by decide)
  exact h (by decide)
/-- (vii): una sucesión que cruza una conversión (c4 posterior a j0). -/
def refRelBad2 : List (Nat × Nat × Rel) := (0, 14, Rel.anterior) :: refRel1
theorem refBad2_no_ley : ¬ Ley (refMp refRelBad2 refPi1 7) := by
  intro L
  have h := L.L7 0 14 Rel.anterior (by decide) (by intro h; cases h)
  exact absurd h (by decide)

/-- Con Afn = ∅, Sel se reduce a las discrepancias de horizonte: se recupera la ley anterior. -/
theorem sel_sin_afn {PV I : Type} (M : Mp PV I) (h : ∀ a b, ¬ M.Afn a b) (a b : I)
    (hs : M.Sel a b) : M.Dsc a b ∧ M.ot a b Op.horizonte := by
  obtain ⟨hd, ho⟩ := hs
  rcases hd with hd | hd
  · exact ⟨hd, ho⟩
  · exact absurd hd (h a b)

end Resultados

end E4
