import CicloRetornos
import E1
/-
  CicloRetornosB · retornos de la FASE 1 (grupo B) — Lean 4.22 (sin Mathlib, sin sorry).

  Decisiones tomadas en las pestañas de E1 y E2 (ciclo/confirmacion_E1.md, ciclo/confirmacion_E2_grupo_B.md):
    E2→E1, E3→E1 : `ExtE1` (extensión monótona de E1Base: sólo crecen Q1, Ad, K; D1 y G, intactos)
                   + relación `Pide ⊆ Cuestiones × Q1'` que apunta a un vacío (`falta`).
    E4→E2, E4→E3 : clasificación PARCIAL `car2 : X → Option (CT × Ep × Mf)` coherente con `car` de E4.
    E3→E2        : `a` lleva autor, lugar y momento (X2 = Ag × Lg × Iv); `ref` es sólo el objeto.
                   (Requiere que la pestaña de E3 corrija L3; aquí es un enlace sobre cualquier E2.Mp.)
    E1→E2        : `Em/Ea/Er` desde `Ev` con compatibilidad ANTÍTONA.
  Todos son relaciones («pueden surgir»), viven fuera de las tuplas, y llevan caso no vacío + exclusión.
-/
namespace CicloB
open E1

/-! ## 1. ExtE1: extensión monótona de E1Base -/

structure ExtE1 {U : Type} (y y' : E1Base U) where
  ι     : y.Q1 → y'.Q1
  D1_ι  : ∀ q u, y'.D1 (some (ι q)) u ↔ y.D1 (some q) u     -- D¹ de las cuestiones viejas, intacta
  G_eq  : ∀ u, y'.G u ↔ y.G u                                -- la apertura (datos reunidos) no se toca
  K_mono : ∀ u, y.K u = true → y'.K u = true                 -- K sólo crece
  Ad_mono : ∀ u, y.Ad u → y'.Ad u                            -- el área sólo crece

theorem ExtE1.res_mono {U : Type} {y y' : E1Base U} (e : ExtE1 y y') (q : y.Q1) (u : U)
    (h : y.res y.Ad q u) : y'.res y'.Ad (e.ι q) u :=
  ⟨(e.D1_ι q u).mpr h.1, e.Ad_mono u h.2.1, e.K_mono u h.2.2.1, (e.G_eq u).mpr h.2.2.2⟩

/-- Si además K y Ad no crecieron en u, lo procurado coincide (no interferencia). -/
theorem ExtE1.res_iff {U : Type} {y y' : E1Base U} (e : ExtE1 y y')
    (hA : ∀ u, y'.Ad u → y.Ad u) (hK : ∀ u, y'.K u = true → y.K u = true) (q : y.Q1) (u : U) :
    y'.res y'.Ad (e.ι q) u ↔ y.res y.Ad q u :=
  ⟨fun h => ⟨(e.D1_ι q u).mp h.1, hA u h.2.1, hK u h.2.2.1, (e.G_eq u).mp h.2.2.2⟩, e.res_mono q u⟩

/-- Lo ya reunido y procurado para una cuestión vieja sigue siendo procurado: sólo se puede ganar. -/
theorem ExtE1.no_pierde {U : Type} {y y' : E1Base U} (e : ExtE1 y y') (q : y.Q1) :
    Sub (y.res y.Ad q) (fun u => y'.res y'.Ad (e.ι q) u) :=
  fun u h => e.res_mono q u h

/-! ## 2. Pide: E2→E1 y E3→E1 -/

/-- Un retorno hacia E1: una relación entre cuestiones pendientes (de E2 o de E3) y cuestiones
    de E1 en la extensión, que sólo puede apuntar a un VACÍO (dato necesario, relevante, en el área,
    no reunido). No es función ni total: «pueden surgir». -/
structure Pide {U : Type} {y y' : E1Base U} (e : ExtE1 y y') (Cu : Type) (pend : Cu → Prop) where
  rel : Cu → y'.Q1 → Prop
  de_pend : ∀ c q, rel c q → pend c
  hay_falta : ∀ c q, rel c q → ∃ u, y'.falta y'.Ad q u

/-- Sin vacíos en E1 no puede haber petición alguna: la condición es una restricción real. -/
theorem Pide.vacia_sin_vacios {U : Type} {y y' : E1Base U} {e : ExtE1 y y'} {Cu : Type}
    {pend : Cu → Prop} (P : Pide e Cu pend) (h : ∀ q u, ¬ y'.falta y'.Ad q u) :
    ∀ c q, ¬ P.rel c q :=
  fun c q hr => by obtain ⟨u, hu⟩ := P.hay_falta c q hr; exact h q u hu

/-- Lo que pide E2: una cuestión está pendiente en alguna lectura. -/
def pendE2 {W X1 X2 X3 H S R Q : Type} (x : E2.Mp W X1 X2 X3 H S R Q) (q : Q) : Prop :=
  ∃ w s, q ∈ x.Pend w s

/-- Pendiente de E2 ⇒ el grado no es «cierto» (criterio de §VI de E2). -/
theorem pendE2_no_cierto {W X1 X2 X3 H S R Q : Type} (x : E2.Mp W X1 X2 X3 H S R Q) (q : Q)
    (h : pendE2 x q) : ∃ w s, x.Jz w s ≠ E2.Grado.cierto := by
  obtain ⟨w, s, hq⟩ := h
  refine ⟨w, s, fun hj => ?_⟩
  have := (x.jz_cierto w s).1 hj
  rw [this] at hq
  simp at hq

/-! ### Caso mínimo (E1 sobre `Fin 4`) -/

section CasoE1
open E1

def lowA : Fin 4 → Prop := fun u => u.val < 3

theorem lowA_todo : Sub lowA todo := fun _ _ => trivial

def ar2 : (Fin 4 → Prop) → Prop := fun c => c = lowA ∨ c = todo

theorem ar2_cadena : ∀ a b, ar2 a → ar2 b → Sub a b ∨ Sub b a := by
  intro a b ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    first
    | exact Or.inl (fun _ h => h)
    | exact Or.inl lowA_todo
    | exact Or.inr lowA_todo

/-- E1 antes: una cuestión, G = {0,1}, K = {0,1,2}, área adoptada {0,1,2}. Falta el dato 2. -/
def yN : E1Base (Fin 4) where
  Q1 := Unit
  D1 := fun _ _ => True
  D1_Delta := fun _ => trivial
  Ar := ar2
  Ar_todo := Or.inr rfl
  Ar_cadena := ar2_cadena
  Ad := lowA
  Ad_mem := Or.inl rfl
  K := fun u => decide (u.val < 3)
  G := fun u => u.val < 2

/-- E1 después: nueva cuestión (sobre el dato 3), K y área crecen, D1 vieja y G intactas. -/
def yN' : E1Base (Fin 4) where
  Q1 := Bool
  D1 := fun o u => match o with
    | none => True
    | some false => True
    | some true => u.val = 3
  D1_Delta := fun _ => trivial
  Ar := ar2
  Ar_todo := Or.inr rfl
  Ar_cadena := ar2_cadena
  Ad := todo
  Ad_mem := Or.inr rfl
  K := fun _ => true
  G := fun u => u.val < 2

def extN : ExtE1 yN yN' where
  ι := fun _ => false
  D1_ι := fun _ _ => Iff.rfl
  G_eq := fun _ => Iff.rfl
  K_mono := fun _ _ => rfl
  Ad_mono := fun _ _ => trivial

/-- La extensión no es trivial: la cuestión nueva tiene un vacío que la vieja no tenía (dato 3). -/
theorem extN_falta_nueva : yN'.falta yN'.Ad true 3 :=
  ⟨rfl, trivial, rfl, fun h => absurd (show (3 : Fin 4).val < 2 from h) (by decide)⟩

/-- La extensión cambia el panorama de vacíos: el dato 3 no era vacío antes (K no lo pedía) y ahora sí. -/
theorem extN_vacio_nuevo : ¬ yN.falta yN.Ad () 3 ∧ yN'.falta yN'.Ad false 3 := by
  refine ⟨fun h => ?_, ?_⟩
  · have : (decide ((3 : Fin 4).val < 3)) = true := h.2.2.1
    simp at this
    exact absurd this (by decide)
  · exact ⟨trivial, trivial, rfl, fun h => absurd (show (3 : Fin 4).val < 2 from h) (by decide)⟩

/-- Una «extensión» que estrecha D¹ de una cuestión vieja NO es ExtE1 (se abre la apertura de fase 1). -/
def yMalD : E1Base (Fin 4) where
  Q1 := Unit
  D1 := fun o _ => match o with | none => True | some _ => False
  D1_Delta := fun _ => trivial
  Ar := ar2
  Ar_todo := Or.inr rfl
  Ar_cadena := ar2_cadena
  Ad := lowA
  Ad_mem := Or.inl rfl
  K := fun u => decide (u.val < 3)
  G := fun u => u.val < 2

theorem yMalD_no_ext : ¬ Nonempty (ExtE1 yN yMalD) := by
  rintro ⟨e⟩
  exact (e.D1_ι () 0).mpr trivial

/-- Idem con G: una extensión que cambia lo reunido (G) no es ExtE1. -/
def yMalG : E1Base (Fin 4) := { yN with G := fun u => u.val < 3 }

theorem yMalG_no_ext : ¬ Nonempty (ExtE1 yN yMalG) := by
  rintro ⟨e⟩
  have h := (e.G_eq 2).mp (show (2 : Fin 4).val < 3 by decide)
  exact absurd (show (2 : Fin 4).val < 2 from h) (by decide)

/-- Idem con K: encoger K (quitar lo necesario) no es ExtE1. -/
def yMalK : E1Base (Fin 4) := { yN with K := fun _ => false }

theorem yMalK_no_ext : ¬ Nonempty (ExtE1 yN yMalK) := by
  rintro ⟨e⟩
  have := e.K_mono 0 rfl
  cases this

end CasoE1

/-! ### E3→E1 sobre la cadena de Nicea: cuestiones `Qint` de E3 -/

open Ciclo in
/-- Las cuestiones de interés de la historia (Qint) piden datos a E1. -/
def pideE3N : Pide extN (Fin 4) (fun q => N.nicea38.M3.Qint q) where
  rel := fun _ b => b = true
  de_pend := fun _ _ _ => trivial
  hay_falta := fun _ _ h => by subst h; exact ⟨3, extN_falta_nueva⟩

/-- El mismo enlace mal formado: apunta a la cuestión vieja con un área sin vacío → no hay Pide. -/
def yLleno : E1Base (Fin 4) := { yN' with G := fun _ => True }

theorem yLleno_sin_vacios : ∀ q u, ¬ yLleno.falta yLleno.Ad q u :=
  fun _ _ h => h.2.2.2 trivial

/-- E2→E1 sobre un E2 con una cuestión pendiente (el E2 de E3.B tiene `Pend` vacío). -/
def Xp : E2.Mp (Fin 3) (Fin 3) (Fin 3 × Fin 3 × Fin 3) Unit Unit Unit Unit Unit :=
  { E3.X with
    Pt := fun _ => [()]
    Pend := fun _ _ => [()]
    Jz := fun _ _ => E2.Grado.probable
    pend_sub := fun _ _ _ h => h
    jz_cierto := fun _ _ => by simp }

theorem Xp_pendiente : pendE2 Xp () := ⟨0, (), by simp [Xp]⟩

def pideE2N : Pide extN Unit (pendE2 Xp) where
  rel := fun _ b => b = true
  de_pend := fun _ _ _ => Xp_pendiente
  hay_falta := fun _ _ h => by subst h; exact ⟨3, extN_falta_nueva⟩

theorem pideE2N_apunta_a_vacio : ∃ u, yN'.falta yN'.Ad true u := ⟨3, extN_falta_nueva⟩

/-! ## 3. E4→E2 y E4→E3: clasificación parcial por perfil -/

structure ClasifE4 {PV I : Type} (M : E4.Mp PV I) (X : Type) where
  car2  : X → Option (M.CT × M.Ep × M.Mf)
  modo  : PV → X → Prop
  coh   : ∀ p x, modo p x → car2 x = some (M.car p).1

/-- Heurística: si el modo x de pensamiento del punto de vista p se clasifica con un perfil
    incoherente, p no es coherente (E4.L10). -/
theorem ClasifE4.heuristica {PV I : Type} {M : E4.Mp PV I} {X : Type} (C : ClasifE4 M X)
    (L : E4.Ley M) (p : PV) (x : X) (hm : C.modo p x)
    (hn : ∃ t, C.car2 x = some t ∧ ¬ M.CohX t) : ¬ M.Odl3 p := by
  obtain ⟨t, ht, hnc⟩ := hn
  have e := C.coh p x hm
  rw [ht] at e
  have : t = (M.car p).1 := Option.some.inj e
  subst this
  exact E4.incoherente_de_X L p hnc

open Ciclo in
/-- E4→E2: modos X1 de E2 (aquí `Fin 3`): los de los puntos de vista 0..2 tienen perfil; no es total. -/
def clasifE2N : ClasifE4 N.NM (Fin 3) where
  car2 := fun _ => some (true, true, true)
  modo := fun p x => x.val = p.val ∧ p.val < 3
  coh := fun p x h => rfl

open Ciclo in
/-- E4→E3: perspectivas `Vt` de E3 (aquí `Fin 2`); la 1 no tiene perfil determinado. -/
def clasifE3N : ClasifE4 N.NM (Fin 2) where
  car2 := fun v => if v.val = 0 then some (true, true, true) else none
  modo := fun p v => v.val = 0 ∧ p.val = 0
  coh := fun p v h => by simp [h.1]

open Ciclo in
theorem clasifE3N_parcial : ∃ v, clasifE3N.car2 v = none := ⟨1, by simp [clasifE3N]⟩

open Ciclo in
/-- Una clasificación que contradice a `car` queda excluida por `coh`. -/
theorem clasif_mala_excluida :
    ¬ ∀ p x, (fun (p : Fin 4) (x : Fin 3) => x.val = p.val ∧ p.val < 3) p x →
      (some (false, true, true) : Option (Bool × Bool × Bool)) = some (N.NM.car p).1 := by
  intro h
  have := h 0 0 ⟨rfl, by decide⟩
  simp at this

-- No interferencia por construcción: `ClasifE4` no contiene campos de E2/E3; LeyFuerte y E3.Ley no se tocan.

/-! ## 4. E3→E2: `a` lleva autor, lugar y momento -/

/-- Lectura corregida de la interfaz de E3 con E2: con `X2 = Ag × Lg × Iv`,
    el autor es la primera componente de `a` y el lugar-intervalo, el resto. `ref` queda libre. -/
structure ContextoA {W X1 Ag Lg Iv X3 H S R Q Fu : Type}
    (x : E2.Mp W X1 (Ag × Lg × Iv) X3 H S R Q) (fw : Fu → W) (au : Fu → Ag) (ub : Fu → Lg × Iv) : Prop where
  autor : ∀ f, au f = (x.a (fw f)).1
  lugar : ∀ f, ub f = (x.a (fw f)).2

/-- Con L3 corregida (E3), el enlace E3→E2 ya vale en la cadena: todo modelo de la ley de E3 cumple `ContextoA`. -/
theorem contexto_de_L3 (M : E3.Mp) (L : E3.Ley M) : ContextoA M.xM M.fw M.au M.ub :=
  ⟨fun f => (L.L3.2 f).1, fun f => (L.L3.2 f).2⟩

/-- Dos modelos de E2 que sólo difieren en `ref` satisfacen el mismo `ContextoA`: ref sale del enlace. -/
theorem ContextoA.indep_ref {W X1 Ag Lg Iv X3 H S R Q Fu : Type}
    (x x' : E2.Mp W X1 (Ag × Lg × Iv) X3 H S R Q) (hA : x.a = x'.a) {fw : Fu → W}
    {au : Fu → Ag} {ub : Fu → Lg × Iv} (h : ContextoA x fw au ub) : ContextoA x' fw au ub :=
  ⟨fun f => by rw [← hA]; exact h.autor f, fun f => by rw [← hA]; exact h.lugar f⟩

/-- E2 cuyo `a` lleva (autor, lugar, momento). -/
def Xa : E2.Mp (Fin 3) (Fin 3) (Fin 3 × Fin 3 × Fin 3) (Fin 3) Unit Unit Unit Unit :=
  { m := fun w => w, a := fun w => (w, w, w), ref := fun w => w
    g := fun _ _ _ _ => (), sg := fun _ => ()
    Pt := fun _ => [], Pend := fun _ _ => [], Jz := fun _ _ => E2.Grado.cierto
    O2 := fun _ _ _ => ()
    pend_sub := fun _ _ q hq => by simp at hq
    jz_cierto := fun _ _ => by simp }

theorem Xa_contexto : ContextoA Xa (fun f => f) (fun f => f) (fun f => (f, f)) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- Variante con `ref` distinto: mismo contexto. -/
theorem Xa_ref_libre :
    ContextoA { Xa with ref := fun _ => (0 : Fin 3) } (fun f => f) (fun f => f) (fun f => (f, f)) :=
  ContextoA.indep_ref Xa { Xa with ref := fun _ => (0 : Fin 3) } rfl Xa_contexto

/-- El contexto es una condición real: un `ub` que no sale de `a` la viola. -/
theorem contexto_mal_excluido : ¬ ContextoA Xa (fun f => f) (fun f => f) (fun _ => (0, 1)) := by
  intro h
  have := h.lugar 2
  simp [Xa] at this

/-- Cambiar `a` cambia el contexto C2 (la mitad del círculo hermenéutico que E2 deja anotada). -/
def Xa' : E2.Mp (Fin 3) (Fin 3) (Fin 3 × Fin 3 × Fin 3) (Fin 3) (Fin 3) Unit Unit Unit :=
  { m := fun w => w, a := fun w => (w, w, w), ref := fun w => w
    g := fun _ _ a _ => a.1, sg := fun _ => ()
    Pt := fun _ => [], Pend := fun _ _ => [], Jz := fun _ _ => E2.Grado.cierto
    O2 := fun _ _ _ => ()
    pend_sub := fun _ _ q hq => by simp at hq
    jz_cierto := fun _ _ => by simp }

theorem cambiar_a_cambia_C2 :
    Xa'.C2 0 ≠ { Xa' with a := fun _ => (1, 1, 1) }.C2 0 := by
  decide

/-- `Pend` no se toca en este enlace: dos modelos con el mismo `Pend` y distinto `a` lo comparten. -/
theorem Pend_no_tocado : ({ Xa' with a := fun _ => (1, 1, 1) }).Pend = Xa'.Pend := rfl

/-! ## 5. E1→E2 (hacia adelante): `Em/Ea/Er` desde `Ev` con compatibilidad antítona -/

structure CompE (U X : Type) where
  comp  : (U → Prop) → X → Prop
  antit : ∀ (E E' : U → Prop) x, (∀ u, E u → E' u) → comp E' x → comp E x

def CompE.lee {U X W : Type} (c : CompE U X) (Ev : W → U → Prop) : W → X → Prop :=
  fun w x => c.comp (Ev w) x

/-- Más evidencia, menos candidatos compatibles. -/
theorem CompE.lee_antit {U X W : Type} (c : CompE U X) (Ev Ev' : W → U → Prop) (w : W) (x : X)
    (h : ∀ u, Ev w u → Ev' w u) : c.lee Ev' w x → c.lee Ev w x :=
  fun hc => c.antit _ _ x h hc

def toMpD {W X1 X2 X3 H S R Q U : Type} (x : E2.Mp W X1 X2 X3 H S R Q) (Ev : W → U → Prop)
    (cm : CompE U X1) (ca : CompE U X2) (cr : CompE U X3) : E2.MpD W X1 X2 X3 H S R Q :=
  { x with Em := cm.lee Ev, Ea := ca.lee Ev, Er := cr.lee Ev }

theorem toMpD_toMp {W X1 X2 X3 H S R Q U : Type} (x : E2.Mp W X1 X2 X3 H S R Q) (Ev : W → U → Prop)
    (cm : CompE U X1) (ca : CompE U X2) (cr : CompE U X3) : (toMpD x Ev cm ca cr).toMp = x := rfl

/-- Compatibilidad del caso: x es compatible con la evidencia si ningún dato de la evidencia lo contradice. -/
def compN (f : X → Nat) : CompE (Fin 4) X where
  comp := fun E x => ∀ u, E u → u.val ≠ f x
  antit := fun _ _ _ h hc u hu => hc u (h u hu)

def EvN : Fin 3 → Fin 4 → Prop := fun _ u => u.val = 3

def mpdN : E2.MpD (Fin 3) (Fin 3) (Fin 3 × Fin 3 × Fin 3) Unit Unit Unit Unit Unit :=
  toMpD E3.X EvN (compN (fun x : Fin 3 => x.val)) (compN (fun x : Fin 3 × Fin 3 × Fin 3 => x.1.val))
    (compN (fun _ : Unit => 0))

/-- La ley débil vale en el caso: E1→E2 no es vacío. -/
theorem mpdN_debil : E2.LeyDebil mpdN := by
  intro w
  refine ⟨?_, ?_, ?_⟩ <;>
    (intro u hu; have h3 : u.val = 3 := hu; have := w.isLt; simp [E3.X]; omega)

/-- Una compatibilidad CRECIENTE (hay algún dato) no es antítona: queda excluida. -/
theorem comp_creciente_excluida :
    ¬ ∀ (E E' : Fin 4 → Prop) (x : Fin 3), (∀ u, E u → E' u) →
      (fun (E : Fin 4 → Prop) (_ : Fin 3) => ∃ u, E u) E' x → (fun (E : Fin 4 → Prop) (_ : Fin 3) => ∃ u, E u) E x := by
  intro h
  obtain ⟨u, hu⟩ := h (fun _ => False) (fun _ => True) 0 (fun _ h => h.elim) ⟨0, trivial⟩
  exact hu

end CicloB

#print axioms CicloB.ExtE1.res_iff
#print axioms CicloB.yMalD_no_ext
#print axioms CicloB.pideE3N
#print axioms CicloB.pideE2N
#print axioms CicloB.ClasifE4.heuristica
#print axioms CicloB.clasifE3N
#print axioms CicloB.contexto_de_L3
#print axioms CicloB.Xa_ref_libre
#print axioms CicloB.cambiar_a_cambia_C2
#print axioms CicloB.mpdN_debil
#print axioms CicloB.comp_creciente_excluida
