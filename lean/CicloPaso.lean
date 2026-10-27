import CicloNicea
/-
  CicloPaso · F3 en esqueleto: el «giro» del ciclo — Lean 4 (sin Mathlib, sin sorry).

  Dos efectos, ambos con apoyo en Lonergan (ver ciclo/paso_esqueleto.md):
  (a) E4 clasifica: la dialéctica incorpora discrepancias (objetivaciones) a `Dsc`. No determina el horizonte
      ni la conversión de E5 (la dialéctica no puede «ir a las raíces de todos los conflictos», cap. 5 §V p. 140; el horizonte es decisión).
  (b) Cierre externo: llegan datos nuevos de la vida cristiana (retroalimentación de la ejecución, cap. 14;
      la teología está dentro de la vida cristiana, p. 143). Solo amplía los datos; no toca ninguna ley.
  El paso es una RELACIÓN (hay elecciones). Lo que cambia es monótono; las leyes se conservan.
-/
namespace Ciclo

section Dsc
variable {PV I : Type}

/-- E4 con otra relación de discrepancias `D` (todo lo demás igual); `D` no puede solapar `Afn`. -/
def conDsc (M : E4.Mp PV I) (D : I → I → Prop) (h : ∀ a b, D a b → ¬ M.Afn a b) : E4.Mp PV I :=
  { M with Dsc := D, dsc_afn_disj := fun a b hh => h a b hh.1 hh.2 }

theorem eqC_conDsc {M : E4.Mp PV I} {D : I → I → Prop} {h : ∀ a b, D a b → ¬ M.Afn a b} {a b : PV}
    (e : M.EqC a b) : (conDsc M D h).EqC a b := by
  induction e with
  | refl h => exact E4.Mp.EqC.refl h
  | step h1 h2 h3 => exact E4.Mp.EqC.step h1 h2 h3
  | symm _ ih => exact E4.Mp.EqC.symm ih
  | trans _ _ ih1 ih2 => exact E4.Mp.EqC.trans ih1 ih2

theorem eqC_conDsc_back {M : E4.Mp PV I} {D : I → I → Prop} {h : ∀ a b, D a b → ¬ M.Afn a b} {a b : PV}
    (e : (conDsc M D h).EqC a b) : M.EqC a b := by
  induction e with
  | refl h => exact E4.Mp.EqC.refl h
  | step h1 h2 h3 => exact E4.Mp.EqC.step h1 h2 h3
  | symm _ ih => exact E4.Mp.EqC.symm ih
  | trans _ _ ih1 ih2 => exact E4.Mp.EqC.trans ih1 ih2

/-- La ley de E4 se conserva al añadir discrepancias (monotonía de `Sel` en `Dsc`). -/
theorem ley_conDsc {M : E4.Mp PV I} (L : E4.Ley M) {D : I → I → Prop}
    {h : ∀ a b, D a b → ¬ M.Afn a b} (hD : ∀ a b, M.Dsc a b → D a b) :
    E4.Ley (conDsc M D h) where
  L1 := L.L1
  L2 := fun a b hab => by
    obtain ⟨h1, h2, i, j, hs, hi, hj⟩ := L.L2 a b hab
    refine ⟨h1, h2, i, j, ?_, hi, hj⟩
    rcases hs with ⟨s, o⟩ | ⟨s, o⟩
    · exact Or.inl ⟨Or.imp (hD i j) id s, o⟩
    · exact Or.inr ⟨Or.imp (hD j i) id s, o⟩
  L3a := L.L3a
  L3b := fun a b ha hb => (L.L3b a b ha hb).trans ⟨eqC_conDsc, eqC_conDsc_back⟩
  L6a := L.L6a
  L6b := L.L6b
  L6c := L.L6c
  L7 := L.L7
  L9 := L.L9
  L10 := L.L10

end Dsc

/-! ## Estados y paso -/
section Paso
variable (C : N.Cadena38)

abbrev Itm := Items C.M3 C.M3.xM

/-- Estado dinámico del ciclo sobre una cadena fija: discrepancias objetivadas por E4 (contienen las de
    partida y no solapan `Afn`) y datos disponibles (de `U`, universo de E3/E0). -/
structure Est where
  D : Itm C → Itm C → Prop
  base : ∀ a b, C.M.Dsc a b → D a b
  disj : ∀ a b, D a b → ¬ C.M.Afn a b
  dat : C.M3.U → Prop

variable {C}

def Est.M4 (s : Est C) : E4.Mp C.PV (Itm C) := conDsc C.M s.D s.disj

/-- Cada estado conserva la ley de E4 y el enlace E3→E4. -/
theorem Est.ley (s : Est C) : E4.Ley s.M4 := ley_conDsc C.LM s.base
theorem Est.enlace (s : Est C) : IncEnDsc C.M3 C.M3.xM s.M4 :=
  fun n n' h => s.base _ _ (C.enlace n n' h)

/-- El giro: relación (no función). Lo objetivado y los datos solo crecen. -/
def Paso (s s' : Est C) : Prop :=
  (∀ a b, s.D a b → s'.D a b) ∧ (∀ u, s.dat u → s'.dat u)

theorem Paso.refl (s : Est C) : Paso s s := ⟨fun _ _ h => h, fun _ h => h⟩
theorem Paso.trans {s s' s'' : Est C} (h : Paso s s') (h' : Paso s' s'') : Paso s s'' :=
  ⟨fun a b x => h'.1 a b (h.1 a b x), fun u x => h'.2 u (h.2 u x)⟩

/-- Invarianza: el estado al que se llega es de nuevo modelo del ciclo (E4 con su ley y el enlace),
    de modo que el paso puede iterarse. -/
theorem Paso.invariante {s s' : Est C} (_ : Paso s s') :
    E4.Ley s'.M4 ∧ IncEnDsc C.M3 C.M3.xM s'.M4 := ⟨s'.ley, s'.enlace⟩

/-- Progreso estricto: algo crece y nada decrece. -/
def Prog (s s' : Est C) : Prop := Paso s s' ∧ ¬ Paso s' s

/-- Efecto (b): un dato nuevo que aún no estaba da un paso de progreso estricto. -/
theorem prog_dato (s : Est C) (u : C.M3.U) (hu : ¬ s.dat u) :
    ∃ s' : Est C, Prog s s' := by
  refine ⟨{ s with dat := fun v => s.dat v ∨ v = u }, ⟨fun _ _ h => h, fun v h => Or.inl h⟩, ?_⟩
  intro h
  exact hu ((h.2 u (Or.inr rfl)))

/-- Efecto (a): una discrepancia nueva (que no es afinidad) objetivada por E4 da un paso de progreso estricto. -/
theorem prog_dsc (s : Est C) (i j : Itm C) (hn : ¬ s.D i j) (hA : ¬ C.M.Afn i j) :
    ∃ s' : Est C, Prog s s' := by
  refine ⟨{ s with
      D := fun a b => s.D a b ∨ (a = i ∧ b = j)
      base := fun a b h => Or.inl (s.base a b h)
      disj := fun a b h => by
        rcases h with h | ⟨rfl, rfl⟩
        · exact s.disj a b h
        · exact hA }, ⟨fun _ _ h => Or.inl h, fun _ h => h⟩, ?_⟩
  intro h
  exact hn (h.1 i j (Or.inr ⟨rfl, rfl⟩))

/-- Coherencia con Lonergan: la clasificación de E4 no determina la conversión de E5. Las conversiones
    admisibles dependen de `≈` (relación `rel`), que el paso no toca. -/
theorem paso_conserva_conversiones {s s' : Est C} (_ : Paso s s') {c : C.X.Cv} {b b' : C.M.Base}
    (h : C.X.tr c = some (b, b')) : s'.M4.aprx b b' := (C.LX.D2 c b b' h).1

end Paso

/-! ## Contraejemplo: un «paso» que quita objetivaciones viola la ley -/
section Declive
open N

/-- En el caso Nicea, vaciar `Dsc` rompe la ley de E4 (L2: toda pareja comparada exige una discrepancia
    de horizonte). El progreso no es trivial: sin monotonía la invarianza falla. -/
theorem declive_rompe_ley :
    ¬ E4.Ley (conDsc NM (fun _ _ => False) (fun _ _ h => h.elim)) := by
  intro L
  obtain ⟨_, _, i, j, hs, _, _⟩ := L.L2 (0 : Fin 4) 1 (by decide)
  rcases hs with ⟨s, _⟩ | ⟨s, _⟩ <;> rcases s with s | s <;> exact s

end Declive

/-! ## El esqueleto en el caso Nicea -/
section Caso
open N

/-- Estado inicial del caso: las discrepancias de partida y ningún dato incorporado. -/
def est0 : Est nicea38 :=
  { D := NM.Dsc, base := fun _ _ h => h, disj := fun _ _ _ h => h, dat := fun _ => False }

/-- Hay un giro de progreso estricto desde el estado inicial (entra un dato nuevo de la vida cristiana). -/
theorem nicea_giro : ∃ s' : Est nicea38, Prog est0 s' :=
  prog_dato est0 (0 : Fin 4) (fun h => h)

/-- Dos giros explícitos: entra primero el dato 0 y luego el dato 1 (estados concretos). -/
def estD (k : Nat) : Est nicea38 :=
  { D := NM.Dsc, base := fun _ _ h => h, disj := fun _ _ _ h => h, dat := fun u => u.val < k }

theorem nicea_dos_giros : Prog est0 (estD 1) ∧ Prog (estD 1) (estD 2) := by
  have hm : ∀ k k' : Nat, k ≤ k' → Paso (estD k) (estD k') :=
    fun k k' h => ⟨fun _ _ x => x, fun u hu => Nat.lt_of_lt_of_le hu h⟩
  have h0 : Paso est0 (estD 1) := ⟨fun _ _ x => x, fun u hu => hu.elim⟩
  refine ⟨⟨h0, fun h => ?_⟩, hm 1 2 (by decide), fun h => ?_⟩
  · exact absurd (h.2 (0 : Fin 4) (show (0 : Fin 4).val < 1 by decide)) (fun x => x)
  · have : (1 : Fin 4).val < 1 := h.2 (1 : Fin 4) (show (1 : Fin 4).val < 2 by decide)
    exact absurd this (by decide)

end Caso
end Ciclo
