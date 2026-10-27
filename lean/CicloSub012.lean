import CicloDeclive
/-
  CicloSub012 · subdeterminación de E0, E1 y E2 por lo anterior — Lean 4.22 (sin Mathlib, sin sorry).

  Misma lectura que en CicloF6 (`E3_no_determinada_por_E2`, `E4_subdeterminado`…): «E_i no derivable de lo anterior» =
  existen dos modelos con ley, sobre el MISMO contexto anterior, que difieren en E_i.
  · E2 ← E1: dos E2 con ley fuerte y RE respecto de la MISMA evidencia de E1 (`pN`) difieren en el objeto (`ref`) que el
    autor de Nicea tenía en mente. Es el punto histórico real: la evidencia no decide si Nicea tematiza la distinción.
  · E1 ← E0: dos E1 con ley (`Ax`) compatibles con el MISMO E0 difieren en el área adoptada (`Ad`) y por tanto en lo procurado.
  · E0 ← U: dos E0 `Actual` sobre el mismo universo de datos difieren en qué documentos producen qué resultados (`D`).
  LÍMITES: es subdeterminación, no necesidad. Los campos que difieren los deja libres la ley (como en E5, E7, E8):
  fuerza media en E2 (afecta un resultado interpretativo), débil en E1 y E0. «Ninguna E_i es derivable de TODAS las demás»
  (falsador 4) sigue sin probarse.
-/
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000
namespace Ciclo
open N E2Nicea

/-! ## E2 subdeterminada por la evidencia de E1 -/

abbrev rT2 (w : Fin 3) : Fin 3 := if w.val = 2 then 1 else 2

/-- Misma lectura de Nicea salvo el objeto: el Símbolo tematiza la unidad y distinción en Dios (objeto 2). -/
abbrev NiceaE2r : E2.Mp (Fin 3) (Fin 3) (Fin 3 × (Fin 3 × Fin 3)) (Fin 3) (Fin 3) (Fin 3) Unit (Fin 3) :=
  { NiceaE2 with ref := rT2 }

abbrev NiceaE2rF : E2.MpF (Fin 3) (Fin 3) (Fin 3 × (Fin 3 × Fin 3)) (Fin 3) (Fin 3) (Fin 3) Unit (Fin 3) :=
  { toMp := NiceaE2r, mS := mT, aS := aT, rS := rT2 }

theorem E2r_ley : E2.LeyFuerte NiceaE2rF := by
  unfold E2.LeyFuerte
  decide

theorem E2r_RE : E2.RE pN NiceaE2rF := by
  show ∀ w : Fin 3, (∀ u : Fin 4, evN w u → okM w u (mT w)) ∧ (∀ u : Fin 4, evN w u → okA w u (aT w)) ∧
    (∀ u : Fin 4, evN w u → okO w u (rT2 w))
  decide

/-- U7 para E2: con la misma evidencia de E1 (`pN`), dos E2 con ley fuerte y RE difieren en el objeto de Nicea. -/
theorem E2_subdeterminada :
    E2.LeyFuerte NiceaE2F ∧ E2.RE pN NiceaE2F ∧ E2.LeyFuerte NiceaE2rF ∧ E2.RE pN NiceaE2rF ∧
    NiceaE2.ref 1 ≠ NiceaE2r.ref 1 :=
  ⟨ley_fuerte, re_nicea, E2r_ley, E2r_RE, by decide⟩

/-- Y la divergencia pasa al resultado: sus cuestiones aceptadas por la evidencia no coinciden, y E2 no puede
    declararla error (ambas cumplen la ley): es lo que E4 recoge como discrepancia de horizonte (§7.12 del Doc de E2). -/
theorem E2_diverge_sin_error : NiceaE2.ref 1 = 0 ∧ NiceaE2r.ref 1 = 2 := by decide

/-! ## E1 subdeterminada por E0 -/

/-- Misma E1 salvo el área adoptada: solo los documentos 2 y 3 (Calcedonia y Constantinopla III). -/
abbrev yNi2 : E1.E1Base (Fin 4) :=
  { N.yNi with
    Ad := fun u => 2 ≤ u.val
    Ad_mem := ⟨2, fun _ => Iff.rfl⟩ }

theorem yNi2_compatible : E1.Compatible N.N0 yNi2 := by
  intro c hc
  exact N.yNi_compatible c hc

abbrev y1Core2 : E1.E1Core (Fin 4) :=
  { yNi2 with
    E1 := fun q u => yNi2.res yNi2.Ad q u
    E1_tipo := fun _ _ _ => rfl }

theorem y1Core2_ax : y1Core2.Ax := fun _ _ => Iff.rfl

/-- U7 para E1: con el mismo E0 del caso, dos E1 con ley y compatibles con E0 difieren en lo procurado
    (el Símbolo de Nicea, dato 1, entra en una y no en la otra para la cuestión q0). -/
theorem E1_subdeterminada :
    E0.Actual N.N0 ∧ E1.Compatible N.N0 N.yNi ∧ N.y1Core.Ax ∧ E1.Compatible N.N0 yNi2 ∧ y1Core2.Ax ∧
    N.y1Core.E1 ⟨0, by decide⟩ 1 ∧ ¬ y1Core2.E1 ⟨0, by decide⟩ 1 := by
  refine ⟨N.N0_actual, N.yNi_compatible, N.y1Core_ax, yNi2_compatible, y1Core2_ax, ?_, ?_⟩
  · exact ⟨Or.inl ⟨rfl, by decide⟩, show 1 ≤ (1 : Fin 4).val by decide, rfl, trivial⟩
  · rintro ⟨_, h, _, _⟩
    exact absurd h (by decide)

/-! ## E0 subdeterminada por el universo de datos -/

/-- Misma lectura del universo U = Fin 4 pero con otra función de producción: cada documento produce un solo tipo de salida. -/
abbrev DN2 : Fin 4 → Fin 3 → Prop := fun u r =>
  (u.val = 0 ∧ r.val = 2) ∨ (u.val = 1 ∧ r.val = 0) ∨ (u.val = 2 ∧ r.val = 1) ∨ (u.val = 3 ∧ r.val = 1)

abbrev N0b : E0.Mp :=
  { N.N0 with
    D := DN2
    D_ne := by decide }

theorem N0b_actual : E0.Actual N0b := by
  refine ⟨?_, ?_⟩
  · show ∀ (u : Fin 4) (r : Fin 3), DN2 u r → N.rhoN u r
    decide
  · intro A r _
    show (3 : Fin 4).val = 3
    rfl

/-- U7 para E0: sobre el mismo universo de datos, dos E0 con sus dos leyes difieren en qué produce el documento 1. -/
theorem E0_subdeterminada :
    E0.Actual N.N0 ∧ E0.Actual N0b ∧ N.N0.U = N0b.U ∧ N.N0.D 1 1 ∧ ¬ N0b.D 1 1 := by
  refine ⟨N.N0_actual, N0b_actual, rfl, Or.inr (Or.inl ⟨rfl, by decide⟩), ?_⟩
  intro h
  exact absurd h (by decide)

/-- U7 completo para E0–E8: lo anterior (CicloF6) más E0–E2. -/
theorem U7_E0_E2 :
    (E0.Actual N.N0 ∧ E0.Actual N0b) ∧ (N.y1Core.Ax ∧ y1Core2.Ax) ∧
    (E2.LeyFuerte NiceaE2F ∧ E2.LeyFuerte NiceaE2rF) :=
  ⟨⟨N.N0_actual, N0b_actual⟩, ⟨N.y1Core_ax, y1Core2_ax⟩, ⟨ley_fuerte, E2r_ley⟩⟩

#print axioms E2_subdeterminada
#print axioms E1_subdeterminada
#print axioms E0_subdeterminada
#print axioms U7_E0_E2

end Ciclo
