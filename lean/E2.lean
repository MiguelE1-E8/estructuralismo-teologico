/-
  E2 (Interpretación) en Lean 4, sin Mathlib.
  Traduce la sección 8 del documento E2: tupla, Mp(E2), Mp', Mp'', Leyes fuerte y débil.
  Convenciones:
   - W = W2, X1 = X1, X2 = X2, X3 = X3, H, S, R = R2, Q = Cuestiones.
   - g es un campo de la estructura (el documento dice "existe g"); C2 se define con él.
   - Pt(w) y Pend(w,s) son listas: la finitud de Pt (7.10) queda codificada en el tipo.
   - sg es σ.
  Fuente: Lonergan, Método en teología (Sígueme, Salamanca 1988), cap. 7 «Interpretación». Páginas impresas aproximadas.
   - Tres operaciones: comprender, juzgar la propia comprensión, establecer la comprensión correcta [p. 151].
   - Cuatro aspectos del comprender: objeto, palabras, autor [pp. 151-156] → X3, X1, X2.
   - Contexto como «nido de preguntas y respuestas» [p. 158] → Cuestiones, Pt.
   - Criterio «no quedan cuestiones ulteriores» [p. 157] → Pend, Jz (jz_cierto); grados [p. 160].
   - Reconstruir sin reproducir [p. 161] → m*, a*, ref* en las leyes (E2.lean no los usa: `LeyFuerte` los toma de `MpF`).
-/
namespace E2

inductive Grado where
  | cierto | altamente_probable | probable
  deriving DecidableEq, Repr

/-- Mp(E2): condiciones 1 a 7 de 8.2. -/
structure Mp (W X1 X2 X3 H S R Q : Type) where
  m    : W → X1
  a    : W → X2
  ref  : W → X3
  g    : W → X1 → X2 → X3 → H
  sg   : H → S
  Pt   : W → List Q
  Pend : W → S → List Q
  Jz   : W → S → Grado
  O2   : W → S → Grado → R
  pend_sub  : ∀ w s q, q ∈ Pend w s → q ∈ Pt w
  jz_cierto : ∀ w s, Jz w s = Grado.cierto ↔ Pend w s = []

namespace Mp
variable {W X1 X2 X3 H S R Q : Type}

def C2 (x : Mp W X1 X2 X3 H S R Q) (w : W) : H := x.g w (x.m w) (x.a w) (x.ref w)
def O1 (x : Mp W X1 X2 X3 H S R Q) (w : W) : S := x.sg (x.C2 w)
def E2 (x : Mp W X1 X2 X3 H S R Q) (w : W) : R := x.O2 w (x.O1 w) (x.Jz w (x.O1 w))

/-- Condición 7 de 8.2 como identidad. -/
theorem E2_eq (x : Mp W X1 X2 X3 H S R Q) (w : W) :
    x.E2 w = x.O2 w (x.sg (x.g w (x.m w) (x.a w) (x.ref w)))
      (x.Jz w (x.sg (x.g w (x.m w) (x.a w) (x.ref w)))) := rfl

/-- Criterio de la sección VI: Jz es cierto exactamente cuando no queda nada pendiente. -/
theorem jz_iff (x : Mp W X1 X2 X3 H S R Q) (w : W) (s : S) :
    x.Jz w s = Grado.cierto ↔ x.Pend w s = [] := x.jz_cierto w s

theorem no_cierto_pend (x : Mp W X1 X2 X3 H S R Q) (w : W) (s : S)
    (h : x.Jz w s ≠ Grado.cierto) : x.Pend w s ≠ [] :=
  fun hp => h ((x.jz_cierto w s).2 hp)

end Mp

/-- Mp'(E2): añade m*, a*, ref* (condición 8). -/
structure MpF (W X1 X2 X3 H S R Q : Type) extends Mp W X1 X2 X3 H S R Q where
  mS : W → X1
  aS : W → X2
  rS : W → X3

/-- Mp''(E2): añade Em, Ea, Er (condición 8''). -/
structure MpD (W X1 X2 X3 H S R Q : Type) extends Mp W X1 X2 X3 H S R Q where
  Em : W → X1 → Prop
  Ea : W → X2 → Prop
  Er : W → X3 → Prop

variable {W X1 X2 X3 H S R Q : Type}

/-- Ley fuerte. -/
def LeyFuerte (x : MpF W X1 X2 X3 H S R Q) : Prop :=
  ∀ w, x.m w = x.mS w ∧ x.a w = x.aS w ∧ x.ref w = x.rS w

/-- Ley débil. -/
def LeyDebil (x : MpD W X1 X2 X3 H S R Q) : Prop :=
  ∀ w, x.Em w (x.m w) ∧ x.Ea w (x.a w) ∧ x.Er w (x.ref w)

/-- Con la ley fuerte, la reconstrucción del contexto usa exactamente m*, a*, ref*. -/
theorem fuerte_C2 (x : MpF W X1 X2 X3 H S R Q) (hF : LeyFuerte x) (w : W) :
    x.toMp.C2 w = x.g w (x.mS w) (x.aS w) (x.rS w) := by
  obtain ⟨h1, h2, h3⟩ := hF w
  unfold Mp.C2
  rw [h1, h2, h3]

/-- La ley fuerte implica la débil cuando Em, Ea, Er contienen lo propio (m*, a*, ref*). -/
theorem fuerte_implica_debil (x : MpF W X1 X2 X3 H S R Q)
    (Em : W → X1 → Prop) (Ea : W → X2 → Prop) (Er : W → X3 → Prop)
    (hm : ∀ w, Em w (x.mS w)) (ha : ∀ w, Ea w (x.aS w)) (hr : ∀ w, Er w (x.rS w))
    (hF : LeyFuerte x) :
    ∀ w, Em w (x.m w) ∧ Ea w (x.a w) ∧ Er w (x.ref w) := by
  intro w
  obtain ⟨h1, h2, h3⟩ := hF w
  rw [h1, h2, h3]
  exact ⟨hm w, ha w, hr w⟩

/-- 7.4: la Ley no incluye a Jz. Dos modelos con los mismos m, a, ref, m*, a*, ref*
    satisfacen la Ley fuerte a la vez, aunque difieran en Pt, Pend, Jz y O2. -/
theorem ley_indep_Jz (x y : MpF W X1 X2 X3 H S R Q)
    (hm : x.m = y.m) (ha : x.a = y.a) (hr : x.ref = y.ref)
    (hms : x.mS = y.mS) (has : x.aS = y.aS) (hrs : x.rS = y.rS) :
    LeyFuerte x ↔ LeyFuerte y := by
  unfold LeyFuerte
  rw [hm, ha, hr, hms, has, hrs]

/-- 7.12: dos interpretaciones con los mismos g, σ, O2, Jz y los mismos m*, a*, ref*
    que cumplen ambas la Ley fuerte dan el mismo resultado. Contrarrecíproco:
    una divergencia implica que al menos una no cumple la Ley. -/
theorem fuerte_misma_salida (x y : MpF W X1 X2 X3 H S R Q)
    (hg : x.g = y.g) (hsg : x.sg = y.sg) (hO : x.O2 = y.O2) (hJ : x.Jz = y.Jz)
    (hm : x.mS = y.mS) (ha : x.aS = y.aS) (hr : x.rS = y.rS)
    (fx : LeyFuerte x) (fy : LeyFuerte y) :
    ∀ w, x.toMp.E2 w = y.toMp.E2 w := by
  intro w
  have hC : x.toMp.C2 w = y.toMp.C2 w := by
    rw [fuerte_C2 x fx w, fuerte_C2 y fy w, hg, hm, ha, hr]
  have hO1 : x.toMp.O1 w = y.toMp.O1 w := by
    unfold Mp.O1; rw [hC, hsg]
  unfold Mp.E2
  rw [hO1, hO, hJ]

/-- Hallazgo: todo modelo potencial se extiende a un modelo de la Ley fuerte
    (basta tomar m*, a*, ref* iguales a m, a, ref). Como m*, a*, ref* son teóricos
    en E2, la Ley fuerte, sola, no restringe nada sobre Mp(E2). -/
def conLey (x : Mp W X1 X2 X3 H S R Q) : MpF W X1 X2 X3 H S R Q :=
  { x with mS := x.m, aS := x.a, rS := x.ref }

theorem contenido_trivial (x : Mp W X1 X2 X3 H S R Q) : LeyFuerte (conLey x) :=
  fun _ => ⟨rfl, rfl, rfl⟩

/-- Vínculo con E5 (7.6), hipótesis de trabajo: si la interpretación acierta en w,
    el horizonte desde el que se hizo alcanza w. Consecuencias formales. -/
theorem link_E5 {Ξ : Type} (x : MpF W X1 X2 X3 H S R Q) (Alc : Ξ → W → Prop) (ξ : Ξ)
    (hV : ∀ w, (x.m w = x.mS w ∧ x.a w = x.aS w ∧ x.ref w = x.rS w) → Alc ξ w) :
    (LeyFuerte x → ∀ w, Alc ξ w) ∧
    (∀ w, ¬ Alc ξ w → ¬ (x.m w = x.mS w ∧ x.a w = x.aS w ∧ x.ref w = x.rS w)) :=
  ⟨fun hF w => hV w (hF w), fun w hn hc => hn (hV w hc)⟩

/-! ## Modelos concretos: Mp ⊋ M e independencia de Jz y la Ley -/

def ejemplo (mv ms : Bool) (pend : List Unit) :
    MpF Unit Bool Bool Bool Unit Unit Grado Unit where
  m := fun _ => mv
  a := fun _ => true
  ref := fun _ => true
  g := fun _ _ _ _ => ()
  sg := fun _ => ()
  Pt := fun _ => [()]
  Pend := fun _ _ => pend
  Jz := fun _ _ => if pend = [] then Grado.cierto else Grado.probable
  O2 := fun _ _ g => g
  pend_sub := fun _ _ q _ => by cases q; simp
  jz_cierto := fun _ _ => by by_cases h : pend = [] <;> simp [h]
  mS := fun _ => ms
  aS := fun _ => true
  rS := fun _ => true

/-- La Ley se cumple en algún modelo. -/
theorem ley_se_cumple : LeyFuerte (ejemplo true true []) :=
  fun _ => ⟨rfl, rfl, rfl⟩

/-- Mp contiene estrictamente a M: hay un modelo bien tipado que falla la Ley. -/
theorem ley_puede_fallar : ¬ LeyFuerte (ejemplo true false []) := by
  intro h
  have := (h ()).1
  simp [ejemplo] at this

/-- 7.4, primera dirección: Ley satisfecha y, aun así, Jz ≠ cierto. -/
theorem ley_sin_certeza :
    LeyFuerte (ejemplo true true [()]) ∧
    (ejemplo true true [()]).Jz () ((ejemplo true true [()]).toMp.O1 ()) ≠ Grado.cierto := by
  refine ⟨fun _ => ⟨rfl, rfl, rfl⟩, ?_⟩
  simp [ejemplo]

/-- 7.4, segunda dirección: Jz = cierto y, aun así, la Ley falla. -/
theorem certeza_sin_ley :
    ¬ LeyFuerte (ejemplo true false []) ∧
    (ejemplo true false []).Jz () ((ejemplo true false []).toMp.O1 ()) = Grado.cierto := by
  refine ⟨ley_puede_fallar, ?_⟩
  simp [ejemplo]

/-! ## Contenido empírico (como en E1): modelos parciales que se extienden o no

  Decisión de modelado: la restricción empírica (RE) exige que lo propio del escrito
  (m*, a*, ref*) sea compatible con la evidencia de E1, es decir, que (w, m*(w)) ∈ Em,
  (w, a*(w)) ∈ Ea y (w, ref*(w)) ∈ Er. Em, Ea y Er llegan por el vínculo con E1 (Ev);
  el modelo parcial es p = ⟨Em, Ea, Er⟩ y todo lo demás (H, S, R, Q, g, σ, Pt, Pend, Jz, O2,
  m, a, ref, m*, a*, ref*) es teórico y se completa.
-/

structure Mpp (W X1 X2 X3 : Type) where
  Em : W → X1 → Prop
  Ea : W → X2 → Prop
  Er : W → X3 → Prop

/-- RE: lo propio es compatible con la evidencia. -/
def RE (p : Mpp W X1 X2 X3) (x : MpF W X1 X2 X3 H S R Q) : Prop :=
  ∀ w, p.Em w (x.mS w) ∧ p.Ea w (x.aS w) ∧ p.Er w (x.rS w)

/-- p se extiende a un modelo de la Ley fuerte que cumple RE. -/
def Extiende (p : Mpp W X1 X2 X3) : Prop :=
  ∃ (H S R Q : Type) (x : MpF W X1 X2 X3 H S R Q), LeyFuerte x ∧ RE p x

/-- Con RE, la Ley fuerte implica la débil sobre las mismas relaciones. -/
theorem fuerte_RE_implica_debil (p : Mpp W X1 X2 X3) (x : MpF W X1 X2 X3 H S R Q)
    (hF : LeyFuerte x) (hR : RE p x) :
    ∀ w, p.Em w (x.m w) ∧ p.Ea w (x.a w) ∧ p.Er w (x.ref w) :=
  fuerte_implica_debil x p.Em p.Ea p.Er
    (fun w => (hR w).1) (fun w => (hR w).2.1) (fun w => (hR w).2.2) hF

/-- Caracterización: p se extiende si y solo si, para cada escrito, la evidencia deja
    al menos un modo de pensamiento, unas circunstancias y un objeto compatibles. -/
theorem extiende_iff (p : Mpp W X1 X2 X3) :
    Extiende p ↔ ∀ w, (∃ x, p.Em w x) ∧ (∃ y, p.Ea w y) ∧ (∃ z, p.Er w z) := by
  constructor
  · rintro ⟨H, S, R, Q, x, _, hR⟩ w
    exact ⟨⟨x.mS w, (hR w).1⟩, ⟨x.aS w, (hR w).2.1⟩, ⟨x.rS w, (hR w).2.2⟩⟩
  · intro h
    have hm : ∀ w, ∃ x, p.Em w x := fun w => (h w).1
    have ha : ∀ w, ∃ y, p.Ea w y := fun w => (h w).2.1
    have hr : ∀ w, ∃ z, p.Er w z := fun w => (h w).2.2
    let m  : W → X1 := fun w => Classical.choose (hm w)
    let a  : W → X2 := fun w => Classical.choose (ha w)
    let rf : W → X3 := fun w => Classical.choose (hr w)
    refine ⟨Unit, Unit, Unit, Unit,
      { m := m, a := a, ref := rf
        g := fun _ _ _ _ => ()
        sg := fun _ => ()
        Pt := fun _ => []
        Pend := fun _ _ => []
        Jz := fun _ _ => Grado.cierto
        O2 := fun _ _ _ => ()
        pend_sub := fun _ _ q hq => by simp at hq
        jz_cierto := fun _ _ => by simp
        mS := m, aS := a, rS := rf }, ?_, ?_⟩
    · exact fun _ => ⟨rfl, rfl, rfl⟩
    · exact fun w => ⟨Classical.choose_spec (hm w), Classical.choose_spec (ha w),
        Classical.choose_spec (hr w)⟩

/-- Un modelo parcial que se extiende. -/
def pOk : Mpp Unit Bool Bool Bool := ⟨fun _ _ => True, fun _ _ => True, fun _ _ => True⟩

theorem pOk_extiende : Extiende pOk :=
  (extiende_iff pOk).2 fun _ => ⟨⟨true, trivial⟩, ⟨true, trivial⟩, ⟨true, trivial⟩⟩

/-- Un modelo parcial refutador: la evidencia no deja ningún modo de pensamiento compatible. -/
def pBad : Mpp Unit Bool Bool Bool := ⟨fun _ _ => False, fun _ _ => True, fun _ _ => True⟩

theorem pBad_no_extiende : ¬ Extiende pBad := by
  intro h
  have h1 := ((extiende_iff pBad).1 h) ()
  obtain ⟨b, hb⟩ := h1.1
  exact hb

end E2
