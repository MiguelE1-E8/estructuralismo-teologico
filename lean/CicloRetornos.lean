import CicloPaso
/-
  CicloRetornos · aristas de retorno del grupo A + E6→E3 — Lean 4 (sin Mathlib, sin sorry).

  Cada retorno es una estructura APARTE sobre una `Cadena38` cualquiera: no modifica ninguna tupla, de modo que
  las leyes de E3–E8 son las que cada pestaña verificó (no interferencia por construcción). Todos son
  RELACIONES («pueden surgir»), no funciones obligatorias, como en el texto (cap. 5 §V, pp. 140–143).
  Para cada uno: la estructura, lo que se deduce de la ley, un caso (Nicea) donde es no vacío y un enlace
  mal formado que la condición excluye.
  - E8→E7: «De la comunicación pueden surgir problemas para la sistematización» (p. 141).
  - E7→E6: «Los modos de conceptualización de la sistematización pueden ser empleados en las doctrinas» (p. 141).
  - E5→E4: los fundamentos objetivan la conversión y dan «profundidad y seriedad» a la dialéctica (p. 142):
    los perfiles que E5 objetiva son los de la familia {E4_q} de la cláusula (viii).
  - E6→E3: «para escribir la historia es preciso entender la doctrina» (p. 142): forma mínima.
  - E6→E5 (restituida el 18-oct): «la conversión, formulada como horizonte de fundamentación, tiene dimensiones
    no sólo personales, sino también sociales y doctrinales» (p. 141), tercera de las dependencias «en sentido
    inverso» (tras E8→E7 y E7→E6). Es lectura por paralelismo y por el principio de los niveles, no cita literal.
-/
namespace Ciclo
open N

variable (C : N.Cadena38)

/-! ## E8→E7 -/
structure RetornoE8E7 where
  plantea : C.W.Ex → C.Z.Sy → C.Z.Cq → Prop
  /-- la expresión es una de las entregadas por el sistema -/
  de_s : ∀ x s q, plantea x s q → ∃ c l, C.W.ntg s c l x
  /-- la cuestión es del sistema -/
  en_s : ∀ x s q, plantea x s q → C.Z.Cqs s q
  /-- y es un problema: ninguna respuesta del sistema la responde -/
  pendiente : ∀ x s q, plantea x s q → ∀ c, C.Z.Rsps s c → ¬ C.Z.Orr c q

/-- Con la ley de E7 no se deduce que toda expresión plantee algo: el vacío es un retorno válido. -/
def RetornoE8E7.vacio : RetornoE8E7 C :=
  ⟨fun _ _ _ => False, fun _ _ _ h => h.elim, fun _ _ _ h => h.elim, fun _ _ _ h => h.elim⟩

/-- En Nicea el retorno no es vacío: la expresión 0 plantea al sistema s₆ la cuestión q₁, que ninguna respuesta atiende. -/
def retorno87_nicea : RetornoE8E7 nicea38 :=
  { plantea := fun x s q => x = 0 ∧ s = 0 ∧ q = 0
    de_s := by decide
    en_s := by decide
    pendiente := by decide }

theorem retorno87_nicea_no_vacio : ∃ x s q, retorno87_nicea.plantea x s q := ⟨0, 0, 0, rfl, rfl, rfl⟩

/-- La condición `pendiente` es una restricción real: la cuestión q₂ del mismo sistema ya está respondida, y no puede plantearse. -/
theorem retorno87_nicea_excluye :
    ¬ ∃ R : RetornoE8E7 nicea38, R.plantea 0 0 1 := by
  rintro ⟨R, h⟩
  exact R.pendiente 0 0 1 h 0 (by decide) (by decide)

/-! ## E7→E6 -/
structure RetornoE7E6 where
  emplea : C.Z.Sy → C.Y.Dc → Prop
  /-- solo un sistema adecuado aporta modos de conceptualización -/
  adecuado : ∀ s d', emplea s d' → E7.Adec C.Z s
  /-- se emplean en un desarrollo de doctrinas del sistema, por el modo de sistematización (`tsi`) -/
  modo : ∀ s d', emplea s d' → ∃ d, C.Z.Dcs s d ∧ C.Y.Dsr d d' ∧ C.Y.mdd d d' = some E6.Md.tsi

/-- Consecuencia de la ley de E6: emplear la sistematización exige un contexto teóricamente diferenciado. -/
theorem RetornoE7E6.exige_teoria (R : RetornoE7E6 C) {s d'} (h : R.emplea s d') :
    C.Y.rq (C.Y.cd d') E5.Cs5.teo := by
  obtain ⟨d, _, _, hm⟩ := R.modo s d' h
  exact C.LY.L10 d d' _ hm E5.Cs5.teo rfl

def retorno76_nicea : RetornoE7E6 nicea38 :=
  { emplea := fun s d' => s.val ≤ 1 ∧ d' = 6
    adecuado := fun s d' h => nicea_Adec_01 s h.1
    modo := fun s d' h => by
      obtain ⟨hs, rfl⟩ := h
      exact ⟨4, (show ∀ s : Fin 3, s.val ≤ 1 → nicea38.Z.Dcs s 4 by decide) s hs, by decide, by decide⟩ }

theorem retorno76_nicea_no_vacio : ∃ s d', retorno76_nicea.emplea s d' := ⟨0, 6, by decide, rfl⟩

/-- El sistema no adecuado (s_A) no puede aportar nada a las doctrinas. -/
theorem retorno76_nicea_excluye_sA :
    ¬ ∃ R : RetornoE7E6 nicea38, ∃ d', R.emplea 2 d' := by
  rintro ⟨R, d', h⟩
  exact nicea_sA_no_adec (R.adecuado 2 d' h)

/-! ## E5→E4 -/
/-- Los perfiles que E5 objetiva son los de la familia {E4_q} (cláusula viii de E4); el miembro del perfil
    del horizonte al que se llega por conversión es el E4 de la cadena. -/
structure RetornoE5E4 where
  Fam : E4.Perfil → E4.Mp C.PV (Itm C)
  ley_fam : ∀ q, E4.Ley (Fam q)
  Q : List E4.Perfil
  cubre : ∀ w, C.X.pf w ∈ Q
  actual : ∀ c, Fam (C.X.pf (C.X.hzp c)) = C.M
  D : E4.Dom1 (Itm C)
  viii : E4.LeyRec Q Fam D

/-- En Nicea: familia constante y la regla `domRec`. -/
def retorno54_nicea : RetornoE5E4 nicea38 :=
  { Fam := fun _ => NM, ley_fam := fun _ => NM_ley
    Q := [(true, true, true), (true, false, false)]
    cubre := by decide
    actual := fun _ => rfl
    D := E4.domRec _
    viii := E4.leyRec_domRec _ _ }

/-- La cobertura es una restricción real: una lista que omita el perfil de algún horizonte no sirve. -/
theorem retorno54_nicea_cubre_necesaria :
    ¬ ∃ R : RetornoE5E4 nicea38, R.Q = [] := by
  rintro ⟨R, h⟩
  have := R.cubre 0
  rw [h] at this
  cases this

/-! ## E6→E3 (forma mínima; se enriquece con el E3 nicénico) -/
structure RetornoE6E3 where
  /-- la historia de una doctrina es una narración de E3, y solo de doctrinas comprendidas en algún horizonte -/
  hdoc : {d : C.Y.Dc // ∃ w, C.Y.Ap w d} → C.M3.Nr

def retorno63_nicea : RetornoE6E3 nicea38 := ⟨fun _ => (0 : Fin 6)⟩

theorem retorno63_nicea_no_vacio : Nonempty (RetornoE6E3 nicea38) := ⟨retorno63_nicea⟩

/-- No hay historia de una doctrina que ningún horizonte comprende: el tipo de partida excluye d₈ sin horizonte. -/
theorem retorno63_nicea_dominio : ∀ d : nicea38.Y.Dc, (∃ w, nicea38.Y.Ap w d) ↔ d.val ≤ 5 := by decide

/-! ## E6→E5 (restituida): la dimensión doctrinal de la conversión -/
/-- Un horizonte de fundamentación tiene dimensión doctrinal cuando algunas doctrinas se aprehenden desde él.
    Solo relaciona: no determina `pf` ni `rep` (el perfil del horizonte lo da la conversión, no las doctrinas). -/
structure RetornoE6E5 where
  dim : C.X.Om → C.Y.Dc → Prop
  en_hz : ∀ w d, dim w d → C.Y.Ap w d

/-- Solo un horizonte auténtico, con conversión plena, tiene dimensión doctrinal (por L14 de E6). -/
theorem RetornoE6E5.dim_aut (R : RetornoE6E5 C) (w : C.X.Om) (d : C.Y.Dc) (h : R.dim w d) :
    C.X.pf w = (true, true, true) ∧ C.X.Aut w :=
  C.LY.L14 w d (R.en_hz w d h)

def retorno65_nicea : RetornoE6E5 nicea38 := ⟨fun w d => w.val = 2 ∧ d.val = 4, fun w d h => by
  have : ∀ w : Fin 3, ∀ d : Fin 9, w.val = 2 ∧ d.val = 4 → nicea38.Y.Ap w d := by decide
  exact this w d h⟩

theorem retorno65_nicea_no_vacio : ∃ w d, retorno65_nicea.dim w d := ⟨2, 4, rfl, rfl⟩

/-- El horizonte inauténtico (ω₀) no admite dimensión doctrinal: la condición es una restricción real. -/
theorem retorno65_nicea_excluye_inaut : ¬ ∃ R : RetornoE6E5 nicea38, ∃ d, R.dim 0 d := by
  rintro ⟨R, d, h⟩
  have := (RetornoE6E5.dim_aut nicea38 R 0 d h).2
  exact absurd this (by decide)

end Ciclo
