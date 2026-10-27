import CicloF6
/-
  CicloCaso · un caso común E0–E8 sobre Nicea — Lean 4 (sin Mathlib, sin sorry).

  Lo nuevo: E0 y E1 con datos del caso, sobre el MISMO universo de datos U = Fin 4 que usa E3 (`N3.U`).
  Lectura de U (ESTIPULACIÓN de modelado, a confirmar por las pestañas de E0, E1 y E3; fechas por verificar):
    u0  carta de Eusebio de Nicomedia a Paulino de Tiro (c. 320-321), documento privado
    u1  Símbolo de Nicea (325), con anatemas, documento conciliar
    u2  Definición de Calcedonia (451), documento conciliar
    u3  Definición de Constantinopla III (680-681): documento conciliar que recopila definiciones anteriores
        (por eso su tipo es «compilación», un dato que nace de resultados).
  E2 (rehecho 22-oct): `N3.xM = E2Nicea.NiceaE2` (lectura nicénica de la pestaña E2: Eusebio, Nicea, Calcedonia; sentidos y grados).
  `CasoNicea` exige ahora la ley fuerte de E2 sobre ese `xM` con RE respecto de la evidencia de E1 (`e2`).
  Enlaces E0→E1 (Compatible, Vinculo) y E1→E3 (`ev_en_E1`: todo dato que E3 usa o cita como evidencia
  está reunido por E1, y la evidencia es relevante) como campos de `CasoNicea`.
-/
set_option maxRecDepth 8192
namespace Ciclo
namespace N

section E0N
open E0

/-- Índices (lectura): tipos de dato 0 carta · 1 símbolo · 2 definición · 3 compilación.
    Tipos de salida 0 edición · 1 índice · 2 catálogo. Resultados 0 edición crítica de los textos conciliares ·
    1 índice de términos (ousía, hypóstasis, homooúsios, voluntad…) · 2 catálogo de fuentes (k' = id).
    Géneros 0 privado · 1 conciliar. -/
abbrev rhoN : Fin 4 → Fin 3 → Prop := fun t s =>
  (t.val = 0 ∧ s.val = 2) ∨ (t.val = 1 ∧ s.val ≤ 1) ∨ (t.val = 2 ∧ s.val ≤ 1) ∨ (t.val = 3 ∧ 1 ≤ s.val)
abbrev pteN : Fin 3 → Fin 4 → Prop := fun _ t => t.val = 3
abbrev DN : Fin 4 → Fin 3 → Prop := fun u r =>
  (u.val = 0 ∧ r.val = 2) ∨ (u.val = 1 ∧ r.val ≤ 1) ∨ (u.val = 2 ∧ r.val ≤ 1) ∨ (u.val = 3 ∧ 1 ≤ r.val)
abbrev gnN : Fin 4 → Fin 2 := fun u => if u.val = 0 then 0 else 1

def cadenaN : Cadena (Fin 4) where
  N := 1
  π := fun n => match n with | 0 => Modelo.ker gnN | _ => Modelo.ker id
  refina := by
    intro n hn a b h
    have : n = 0 := by omega
    subst this
    have hab : a = b := h
    subst hab
    rfl

theorem cadenaN_estricta : Estricta cadenaN := by
  intro n hn
  have : n = 0 := by have : n < 1 := hn; omega
  subst this
  refine ⟨1, 2, rfl, ?_⟩
  intro h
  have h' : (1 : Fin 4) = 2 := h
  cases h'

/-- E0 del caso: documentos de la controversia, sus tipos, los resultados de E0 y su recomposición. -/
abbrev N0 : E0.Mp where
  U := Fin 4
  R0 := Fin 3
  F := Fin 4
  Fs := Fin 3
  Gn := Fin 2
  dslash := cadenaN
  gen := gnN
  k := id
  k' := id
  ρ := rhoN
  pte := pteN
  D := DN
  D_ne := by decide
  Dhat := fun _ => 3
  U_ne := ⟨0⟩
  R0_ne := ⟨0⟩
  gen_ker := fun _ _ => Iff.rfl
  gen_surj := by decide
  estricta := cadenaN_estricta

theorem N0_coherente : Coherente N0 := by
  show ∀ (u : Fin 4) (r : Fin 3), DN u r → rhoN u r
  decide

theorem N0_composicion : Composicion N0 := by
  intro A r _
  show (3 : Fin 4).val = 3
  rfl

theorem N0_actual : Actual N0 := ⟨N0_coherente, N0_composicion⟩

/-! Negativos de E0 sobre el mismo universo -/

/-- Un E0 incoherente: la carta produce una edición, tipo de salida que ρ no admite para una carta. -/
abbrev N0_mal : E0.Mp :=
  { N0 with
    D := fun u r => DN u r ∨ (u.val = 0 ∧ r.val = 0)
    D_ne := fun u => (N0.D_ne u).imp fun _ h => Or.inl h }

theorem N0_mal_incoherente : ¬ Coherente N0_mal := by
  intro h
  have := h (0 : Fin 4) (0 : Fin 3) (Or.inr ⟨rfl, rfl⟩)
  exact absurd this (by decide)

/-- Un E0 cuya D/ solo llega a los géneros: no distingue Nicea de Calcedonia. -/
def cadenaPlanaN : Cadena (Fin 4) where
  N := 0
  π := fun _ => Modelo.ker gnN
  refina := fun n (hn : n < 0) => absurd hn (Nat.not_lt_zero _)

abbrev N0_plano : E0.Mp :=
  { N0 with dslash := cadenaPlanaN, estricta := fun n (hn : n < 0) => absurd hn (Nat.not_lt_zero _) }
end E0N

section E1N
open E0 E1

/-- E1 del caso: dos cuestiones (q0 sobre la relación Hijo-Padre, q1 sobre las voluntades de Cristo),
    áreas por umbral, área adoptada = los documentos conciliares, todo dato necesario y reunido. -/
abbrev yNi : E1Base (Fin 4) where
  Q1 := Fin 2
  D1 := fun q u => match q with
    | none => True
    | some q => (q.val = 0 ∧ u.val ≤ 2) ∨ (q.val = 1 ∧ 2 ≤ u.val)
  D1_Delta := fun _ => trivial
  Ar := fun c => ∃ t : Fin 3, ∀ u, c u ↔ t.val ≤ u.val
  Ar_todo := ⟨0, fun u => ⟨fun _ => Nat.zero_le _, fun _ => trivial⟩⟩
  Ar_cadena := by
    intro a b ⟨t, ha⟩ ⟨t', hb⟩
    rcases Nat.le_total t.val t'.val with h | h
    · right; intro u hu; exact (ha u).2 (Nat.le_trans h ((hb u).1 hu))
    · left; intro u hu; exact (hb u).2 (Nat.le_trans h ((ha u).1 hu))
  Ad := fun u => 1 ≤ u.val
  Ad_mem := ⟨1, fun _ => Iff.rfl⟩
  K := fun _ => true
  G := fun _ => True

theorem yNi_compatible : Compatible N0 yNi := by
  intro c _
  refine ⟨1, Nat.le_refl _, ?_⟩
  intro u v huv hu
  have : u = v := huv
  subst this; exact hu

abbrev τNi : Option yNi.Q1 → Fin 4 → Prop := fun q t => match q with
  | none => True
  | some q => (q.val = 0 ∧ t.val ≤ 2) ∨ (q.val = 1 ∧ 2 ≤ t.val)

def vincN : Vinculo N0 yNi where
  compat := yNi_compatible
  τ := τNi
  tip := by
    intro q u h
    cases q with
    | none => exact trivial
    | some q =>
      revert q u
      decide
  tau0 := fun _ => trivial

/-- E1 como modelo de M(E1): E1(q) := lo procurado en el área adoptada (la ley, por construcción). -/
abbrev y1Core : E1Core (Fin 4) :=
  { yNi with
    E1 := fun q u => yNi.res yNi.Ad q u
    E1_tipo := fun _ _ _ => rfl }

theorem y1Core_ax : y1Core.Ax := fun _ _ => Iff.rfl

/-- Lo procurado para q1 (voluntades): Calcedonia y Constantinopla III, y no hay vacío. -/
theorem q1_procurado : (∀ u : Fin 4, yNi.res yNi.Ad ⟨1, by decide⟩ u ↔ 2 ≤ u.val) ∧
    (∀ u : Fin 4, ¬ yNi.falta yNi.Ad ⟨1, by decide⟩ u) := by
  constructor
  · intro u
    constructor
    · rintro ⟨h1, h2, _, _⟩
      rcases h1 with ⟨h, _⟩ | ⟨_, h⟩
      · exact absurd h (by decide)
      · exact h
    · intro h
      exact ⟨Or.inr ⟨rfl, h⟩, show 1 ≤ u.val by omega, rfl, trivial⟩
  · rintro u ⟨_, _, _, h⟩; exact h trivial

/-- Negativo de E1: con un E0 que solo llega a géneros, las áreas de E1 dejan de ser compatibles
    (el área {Calcedonia, Constantinopla III} parte el género conciliar). -/
theorem plano_incompatible : ¬ Compatible N0_plano yNi := by
  intro h
  obtain ⟨n, hn, hs⟩ := h (fun u => 2 ≤ u.val) ⟨2, fun _ => Iff.rfl⟩
  have hn0 : n = 0 := by
    have : n ≤ 0 := hn
    omega
  subst hn0
  have := hs (2 : Fin 4) (1 : Fin 4) rfl (by decide)
  exact absurd this (by decide)
end E1N

/-- Un caso común: E0 (con sus dos leyes), E1 (ley y vínculos con E0), y la cadena E3–E8 sobre el mismo
    universo de datos; los datos que E3 usa o cita como evidencia están reunidos por E1 y la evidencia es
    relevante. -/
structure CasoNicea where
  x : E0.Mp
  Lx : E0.Actual x
  y : E1.E1Core x.U
  Ly : y.Ax
  V : E1.Vinculo x y.toE1Base
  C : Cadena38
  hU : C.M3.U = x.U
  ev_en_E1 : ∀ w (u : x.U), C.M3.Ev w (cast hU.symm u) → y.R1 u ∧ y.G u
  uso_en_E1 : ∀ w (u : x.U), C.M3.inW w (cast hU.symm u) → y.G u
  cm : CicloB.CompE C.M3.U C.M3.X1
  ca : CicloB.CompE C.M3.U (C.M3.Ag × (C.M3.Lg × C.M3.Iv))
  cr : CicloB.CompE C.M3.U C.M3.Ob
  /-- E1→E2: el `xM` de la cadena cumple la ley fuerte de E2 y la restricción empírica respecto de la evidencia de E1. -/
  e2 : ∃ xf : E2.MpF C.M3.W C.M3.X1 (C.M3.Ag × (C.M3.Lg × C.M3.Iv)) C.M3.Ob C.M3.H C.M3.S C.M3.R C.M3.Q2,
    xf.toMp = C.M3.xM ∧ E2.LeyFuerte xf ∧
    E2.RE ⟨cm.lee C.M3.Ev, ca.lee C.M3.Ev, cr.lee C.M3.Ev⟩ xf

def casoNicea : CasoNicea where
  x := N0
  Lx := N0_actual
  y := y1Core
  Ly := y1Core_ax
  V := vincN
  C := nicea38c
  hU := rfl
  ev_en_E1 := fun _ _ _ => ⟨rfl, trivial⟩
  uso_en_E1 := fun _ _ _ => trivial
  cm := CicloB.compN (fun x : Fin 3 => x.val)
  ca := CicloB.compN (fun x : Fin 3 × Fin 3 × Fin 3 => x.1.val)
  cr := CicloB.compN (fun _ : Fin 3 => 0)
  e2 := ⟨E2Nicea.NiceaE2F, rfl, E2Nicea.ley_fuerte, by
    intro w
    refine ⟨?_, ?_, ?_⟩ <;>
      (intro u hu
       have h3 : u.val = 3 := hu
       have h1 := (E2Nicea.mT w).isLt
       have h2 := (E2Nicea.aT w).1.isLt
       first
         | (show u.val ≠ (E2Nicea.mT w).val; omega)
         | (show u.val ≠ (E2Nicea.aT w).1.val; omega)
         | (show u.val ≠ 0; omega))⟩

theorem CasoNicea_noVacio : Nonempty CasoNicea := ⟨casoNicea⟩

/-- El caso atraviesa E0→E1→E3→E4→E5→E6→E7→E8 con una sola ley en cada nivel. -/
theorem casoNicea_leyes :
    E0.Actual casoNicea.x ∧ casoNicea.y.Ax ∧ E1.Compatible casoNicea.x casoNicea.y.toE1Base ∧
    E3.Ley casoNicea.C.M3 ∧ E4.Ley casoNicea.C.M ∧ E5.Ley casoNicea.C.X ∧ E6.Ley casoNicea.C.Y ∧
    E7.Ley casoNicea.C.Z ∧ E8.Ley casoNicea.C.W :=
  ⟨casoNicea.Lx, casoNicea.Ly, casoNicea.V.compat, casoNicea.C.L3, casoNicea.C.LM, casoNicea.C.LX,
   casoNicea.C.LY, casoNicea.C.LZ, casoNicea.C.LW⟩

/-- E2 en el caso: el `xM` de la cadena ES el E2 nicénico, y de él salen tres teoremas de contenido
    (la distinción ousía/hypóstasis es posterior a Nicea; Nicea queda en «probable»; el anacronismo viola la ley). -/
theorem casoNicea_E2 :
    casoNicea.C.M3.xM = E2Nicea.NiceaE2 ∧
    (∀ w : Fin 3, w.val ≤ 1 → ¬ E2Nicea.distingue (E2Nicea.NiceaE2.O1 w)) ∧
    E2Nicea.distingue (E2Nicea.NiceaE2.O1 2) ∧
    E2Nicea.NiceaE2.Jz 1 (E2Nicea.NiceaE2.O1 1) ≠ E2.Grado.cierto ∧
    ¬ E2.LeyFuerte E2Nicea.RetroF :=
  ⟨rfl, E2Nicea.distincion_posterior.1, E2Nicea.distincion_posterior.2, E2Nicea.nicea_no_cierta,
   E2Nicea.retro_no_ley⟩

end N
end Ciclo
