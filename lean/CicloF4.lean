import CicloModelo
/-
  CicloF4 · F4 (autocorrección y creatividad) — Lean 4.22 (sin Mathlib, sin sorry).

  (c) Los dos subgrafos de Lonergan, el creativo (hacia adelante, E1→…→E8) y el crítico (retornos), existen, cada
      uno alcanza lo que el otro no, y solo juntos cierran el ciclo.
  (a) El paso depende de E4: con los mismos datos de E1–E3, la admisibilidad de un paso depende de las discrepancias
      `D` de E4 (no basta mirar los datos).
  (a′) Un giro dialéctico (entra una discrepancia nueva) es un paso de progreso estricto que conserva la ley de E4.
-/
namespace Ciclo
open N

/-! ## (c) Subgrafos creativo y crítico -/
def creativa (x y : Fin 8) : Bool := aristas todas x y && decide (y.val = x.val + 1)
def critica (x y : Fin 8) : Bool := aristas todas x y && decide (y.val < x.val)

/-- Toda arista autorizada es creativa o crítica. -/
theorem creativa_o_critica : ∀ x y : Fin 8, aristas todas x y = true → creativa x y = true ∨ critica x y = true := by
  decide

/-- El subgrafo creativo lleva de E1 a todo E_i … -/
theorem creativa_ida : ∀ b : Fin 8, Camino creativa 0 b := by
  intro b
  apply alc_sound _ 0 8 b
  revert b
  decide

/-- … pero no vuelve: desde E8 no se alcanza E1. -/
theorem creativa_sin_vuelta : ¬ Camino creativa 7 0 := by
  intro h
  have hc : ∀ x y : Fin 8, x.val = 7 → creativa x y = true → y.val = 7 := by decide
  exact absurd (cerrado (fun x : Fin 8 => x.val = 7) hc h rfl) (by decide)

/-- El subgrafo crítico lleva de E8 a todo E_i … -/
theorem critica_vuelta : ∀ b : Fin 8, Camino critica 7 b := by
  intro b
  apply alc_sound _ 7 8 b
  revert b
  decide

/-- … pero no sube: desde E1 no se alcanza E8. -/
theorem critica_sin_ida : ¬ Camino critica 0 7 := by
  intro h
  have hc : ∀ x y : Fin 8, x.val = 0 → critica x y = true → y.val = 0 := by decide
  exact absurd (cerrado (fun x : Fin 8 => x.val = 0) hc h rfl) (by decide)

/-! ## (a) El paso depende de E4 -/
section Dep
open N

/-- Una narración canónica (r₁) y la interpretación (ítem del punto de vista 3): pareja que la dialéctica puede
    poner de manifiesto como discrepancia nueva (Lonergan: conflictos entre narraciones e interpretaciones). -/
def nar0 : It := injR3 (M3 := N3) (x := N3.xM) ⟨(0 : Fin 6), Or.inl rfl⟩

/-- Estado con una discrepancia más entre la narración r₁ y la interpretación. -/
def estNueva : Est nicea38 :=
  { D := fun a b => NM.Dsc a b ∨ (a = nar0 ∧ b = itm 3)
    base := fun _ _ h => Or.inl h
    disj := fun a b h => by
      rcases h with h | ⟨rfl, rfl⟩
      · exact fun hh => hh
      · exact fun hh => hh
    dat := fun _ => False }

theorem nueva_no_en_Dsc : ¬ NM.Dsc nar0 (itm 3) := by
  intro h
  rcases (show DscN nar0 (itm 3) from h) with ⟨a, b, ha, _, _⟩ | ⟨n, n', _, h2, _⟩
  · have e : pvOf nar0 = none := rfl
    rw [e] at ha
    cases ha
  · have := congrArg pvOf h2
    rw [pvOf_itm] at this
    have e : pvOf (injR3 (M3 := N3) (x := N3.xM) n') = none := rfl
    rw [e] at this
    cases this

/-- Hay progreso estricto por pura dialéctica (sin dato nuevo): entra una discrepancia. -/
theorem giro_dialectico : Prog est0 estNueva :=
  ⟨⟨fun a b h => Or.inl h, fun _ h => h⟩, fun h => nueva_no_en_Dsc (h.1 _ _ (Or.inr ⟨rfl, rfl⟩))⟩

/-- El estado al que se llega conserva la ley de E4 y el enlace E3→E4. -/
theorem giro_dialectico_ley : E4.Ley estNueva.M4 ∧ IncEnDsc nicea38.M3 nicea38.M3.xM estNueva.M4 :=
  ⟨estNueva.ley, estNueva.enlace⟩

/-- Con los MISMOS datos (E1–E3), un paso es admisible desde un estado y no desde otro: depende de `D` (E4). -/
theorem paso_depende_de_E4 :
    ∃ s1 s2 s' : Est nicea38, s1.dat = s2.dat ∧ Paso s1 s' ∧ ¬ Paso s2 s' :=
  ⟨est0, estNueva, est0, rfl, Paso.refl _,
    fun h => nueva_no_en_Dsc (h.1 _ _ (Or.inr ⟨rfl, rfl⟩))⟩

end Dep


/-! ## (b) La cadena superior acompaña al giro dialéctico
  Un giro que solo añade discrepancias (D) no modifica nada de lo que E5–E8 usan de E4 (bases, perfiles,
  relaciones): la cadena E5–E8 se transporta tal cual sobre `s.M4`, con sus leyes. Es un HALLAZGO de la
  formalización: en el modelo, E4 alimenta a E5–E8 por perfiles y bases, no por el volumen de `Dsc`; el
  efecto de una corrección que cambie esos perfiles (eliminar un punto de vista) no está modelado. -/
section Transporte
variable {C : N.Cadena38}
abbrev Est.X (s : Est C) : E5.Mp s.M4 := { C.X with }
theorem Est.X_ley (s : Est C) : E5.Ley s.X := by
  have h := C.LX
  cases h
  constructor <;> assumption
abbrev Est.Y (s : Est C) : E6.Mp s.X := { C.Y with }
theorem Est.Y_ley (s : Est C) : E6.Ley s.Y := by
  have h := C.LY
  cases h
  constructor <;> assumption
abbrev Est.Z (s : Est C) : E7.Mp s.Y := { C.Z with }
theorem Est.posc (s : Est C) {σ : C.Z.Sy} (h : E7.Posc C.Z σ) : E7.Posc s.Z σ := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩, b, c⟩ := h
  exact ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩, b, c⟩
theorem Est.posc' (s : Est C) {σ : C.Z.Sy} (h : E7.Posc s.Z σ) : E7.Posc C.Z σ := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩, b, c⟩ := h
  exact ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩, b, c⟩
theorem Est.Z_ley (s : Est C) : E7.Ley s.Z :=
  ⟨C.LZ.L15a, fun a b ha hb => C.LZ.L15b a b (s.posc' ha) (s.posc' hb), C.LZ.L16a,
   fun a b h ha hb => C.LZ.L16b a b h (s.posc' ha) (s.posc' hb)⟩

abbrev Est.W (s : Est C) : E8.Mp s.Z := { C.W with }
theorem Est.sis (s : Est C) {σ : C.Z.Sy} (h : s.Z.Sis σ) : C.Z.Sis σ := by
  obtain ⟨d, hd, hp⟩ := h
  exact ⟨d, hd, s.posc' hp⟩
theorem Est.W_ley (s : Est C) : E8.Ley s.W :=
  ⟨fun a h => C.LW.L1 a (s.sis h), fun a h => C.LW.L2 a (s.sis h), fun a h => C.LW.L3 a (s.sis h),
   fun a h => C.LW.L4 a (s.sis h), fun a h => C.LW.L5 a (s.sis h), fun a h => C.LW.L6 a (s.sis h),
   fun a h => C.LW.L7 a (s.sis h), fun a h => C.LW.L8 a (s.sis h)⟩

/-- La cadena completa en el estado `s`: E3 y E5–E8 son los de `C`; E4 es el de `s`. -/
def Est.cadena (s : Est C) : N.Cadena38 where
  M3 := C.M3
  L3 := C.L3
  PV := C.PV
  M := s.M4
  LM := s.ley
  enlace := s.enlace
  X := s.X
  LX := s.X_ley
  Y := s.Y
  LY := s.Y_ley
  Z := s.Z
  LZ := s.Z_ley
  W := s.W
  TW := C.TW
  LW := s.W_ley

/-- Cada giro dialéctico produce un modelo completo del ciclo E3–E8 (iterable). -/
theorem giro_dialectico_cadena : ∃ C' : N.Cadena38, C'.M3 = nicea38.M3 := ⟨estNueva.cadena, rfl⟩

end Transporte

end Ciclo

#print axioms Ciclo.creativa_ida
#print axioms Ciclo.critica_vuelta
#print axioms Ciclo.paso_depende_de_E4
#print axioms Ciclo.giro_dialectico
#print axioms Ciclo.Est.cadena
#print axioms Ciclo.giro_dialectico_cadena
