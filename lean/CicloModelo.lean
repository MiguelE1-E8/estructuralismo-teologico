import CicloF2
/-
  CicloModelo · F1(5): el modelo conjunto `Ciclo.Modelo` (= Mp y Ley del ciclo) — Lean 4.22 (sin Mathlib, sin sorry).

  Un `Modelo` agrupa:
   · la cadena E3–E8 con sus leyes y el enlace E3→E4 (`Cadena38`; E2 entra como `M3.xM`);
   · E1 en dos tiempos (`y`, `y'`) unidos por una extensión monótona `ExtE1` (los retornos de la fase 1 solo la usan);
   · los retornos como RELACIONES aparte (E8→E7, E7→E6, E6→E5, E5→E4, E6→E3; Pide desde E2 y E3; clasificación
     parcial desde E4; compatibilidad antítona E1→E2);
   · la única condición conjunta nueva: `debil`, que obliga a que Em/Ea/Er definidos desde la evidencia de E1 (`Ev`)
     hagan valer la ley débil de E2 sobre el `xM` de la cadena.
  Las leyes de cada E_i están dentro de `C` y no se tocan (no interferencia por construcción).

  LÍMITE (declarado): los retornos son permisos («pueden surgir»), de modo que un modelo con retornos vacíos también
  es `Modelo`. La unidad que este archivo garantiza es estructural (tipos, leyes, grafo conexo, condiciones de enlace);
  que los retornos se EJERZAN es `Modelo.activo`, y se prueba en el caso Nicea, incluido E2→E1: el E2 nicénico
  (`E2Nicea.NiceaE2`) sí tiene cuestiones pendientes (Nicea queda «probable» por q1).
-/
namespace Ciclo
open N CicloB E1

/-- La fase 1 es fuertemente conexa por dentro (reciprocidad de p. 140). -/
theorem fase1_recip : ∀ a b : Fin 8, a.val < 4 → b.val < 4 →
    Camino (fun x y => aristas todas x y && decide (x.val < 4) && decide (y.val < 4)) a b := by
  intro a b ha hb
  apply alc_sound _ a 8 b
  revert a b
  decide

structure Modelo where
  C   : N.Cadena38
  y   : E1Base C.M3.U
  y'  : E1Base C.M3.U
  e   : ExtE1 y y'
  r87 : RetornoE8E7 C
  r76 : RetornoE7E6 C
  r65 : RetornoE6E5 C
  r54 : RetornoE5E4 C
  r63 : RetornoE6E3 C
  p21 : Pide e C.M3.Q2 (pendE2 C.M3.xM)
  p31 : Pide e C.M3.Q C.M3.Qint
  c42 : ClasifE4 C.M C.M3.X1
  c43 : ClasifE4 C.M C.M3.Vt
  cm  : CompE C.M3.U C.M3.X1
  ca  : CompE C.M3.U (C.M3.Ag × (C.M3.Lg × C.M3.Iv))
  cr  : CompE C.M3.U C.M3.Ob
  debil : E2.LeyDebil (toMpD C.M3.xM C.M3.Ev cm ca cr)

/-- El caso Nicea–Constantinopla III (E2 y E3 esquemáticos; E1 estipulado). -/
abbrev Modelo.nicea : Modelo where
  C := nicea38
  y := yN
  y' := yN'
  e := extN
  r87 := retorno87_nicea
  r76 := retorno76_nicea
  r65 := retorno65_nicea
  r54 := retorno54_nicea
  r63 := retorno63_nicea
  p21 :=
    { rel := fun _ b => b = true
      de_pend := fun c _ _ => by
        show ∃ (w : Fin 3) (s : Fin 3), c ∈ E2Nicea.NiceaE2.Pend w s
        revert c; decide
      hay_falta := fun _ _ h => by subst h; exact ⟨3, extN_falta_nueva⟩ }
  p31 := pideE3N
  c42 := clasifE2N
  c43 := clasifE3N
  cm := compN (fun x : Fin 3 => x.val)
  ca := compN (fun x : Fin 3 × Fin 3 × Fin 3 => x.1.val)
  cr := compN (fun _ : Fin 3 => 0)
  debil := by
    intro w
    refine ⟨?_, ?_, ?_⟩ <;>
      (intro u hu
       have h3 : u.val = 3 := hu
       have h1 := (E2Nicea.mT w).isLt
       have h2 := (E2Nicea.aT w).1.isLt
       first
         | (show u.val ≠ (E2Nicea.mT w).val; omega)
         | (show u.val ≠ (E2Nicea.aT w).1.val; omega)
         | (show u.val ≠ 0; omega))

/-- Mod(Ciclo) ≠ ∅ . -/
theorem Modelo.noVacio : Nonempty Modelo := ⟨Modelo.nicea⟩

/-- Ley del ciclo: todo modelo conjunto cumple las leyes de E3–E8, el enlace E3→E4, la reciprocidad de cada fase
    y la conexidad fuerte del grafo de aristas autorizadas. -/
theorem Modelo.unidad (m : Modelo) :
    E3.Ley m.C.M3 ∧ E4.Ley m.C.M ∧ IncEnDsc m.C.M3 m.C.M3.xM m.C.M ∧ E5.Ley m.C.X ∧ E6.Ley m.C.Y ∧
    E7.Ley m.C.Z ∧ E8.Ley m.C.W ∧
    Fuerte (aristas todas) ∧
    (∀ a b : Fin 8, a.val < 4 → b.val < 4 →
      Camino (fun x y => aristas todas x y && decide (x.val < 4) && decide (y.val < 4)) a b) ∧
    (∀ a b : Fin 8, 4 ≤ a.val → 4 ≤ b.val →
      Camino (fun x y => aristas todas x y && decide (4 ≤ x.val) && decide (4 ≤ y.val)) a b) :=
  ⟨m.C.L3, m.C.LM, m.C.enlace, m.C.LX, m.C.LY, m.C.LZ, m.C.LW, conexo, fase1_recip, fase2_recip⟩

/-- No interferencia: olvidar los retornos y E1 deja una `Cadena38` (los retornos no cambian las leyes). -/
def Modelo.cadena (m : Modelo) : N.Cadena38 := m.C

/-- Modelo ACTIVO: los retornos se ejercen (hay al menos un caso en cada relación). -/
def Modelo.Activo (m : Modelo) : Prop :=
  (∃ x s q, m.r87.plantea x s q) ∧ (∃ s d, m.r76.emplea s d) ∧ (∃ w d, m.r65.dim w d) ∧
  (∃ c b, m.p31.rel c b) ∧ (∃ c b, m.p21.rel c b)

theorem Modelo.nicea_activo : Modelo.nicea.Activo :=
  ⟨retorno87_nicea_no_vacio, retorno76_nicea_no_vacio, retorno65_nicea_no_vacio, ⟨0, true, rfl⟩, ⟨0, true, rfl⟩⟩

end Ciclo

#print axioms Ciclo.Modelo.nicea
#print axioms Ciclo.Modelo.unidad
#print axioms Ciclo.Modelo.nicea_activo
