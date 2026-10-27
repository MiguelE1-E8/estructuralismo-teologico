import E8
/-
  Ciclo · E0–E8 en conjunto — Lean 4 (sin Mathlib, sin sorry).
  ESTADO: compila (Lean 4.22, sin sorry) contra los archivos COMPLETOS E2–E8 del Project (18-oct-2026).
  Único cambio necesario fuera de este archivo: en E7.lean, `decExCs5` debe listar los 7 constructores de Cs5
  (faltaba `met`). El caso que cruza E3→E8 está en `CicloNicea.lean`.

  Contenido (decisiones aprobadas 1–3):
  (A) Items := Mcr ⊕ R3E ⊕ R2 : los «ítems» de la dialéctica (E4) como suma de imágenes de E3 y E2.
      Movimientos primarios (Lonergan, cap. 5 §4); descripciones (R3E) e interpretaciones (R2) secundarias.
      PV, Dsc, Afn y V siguen siendo propios de E4. Única condición de interfaz: Inc ⊆ Dsc sobre narraciones.
  (B) El grafo de las ocho especialidades con aristas «A influye en B», etiquetadas por su estado de
      formalización. Nodos 0..7 = E1..E8 (E1 = investigación, ..., E8 = comunicaciones).
  (E) Enlace E3→E4 formal: `enlace34_consistente` (A) y `enlace34_independiente` (B), para todo modelo de E3.
  (F) Cadena48: tupla E4–E8 + `Ciclo_noVacio` (caso Nicea) + enlaces hacia adelante enlace45/56/67/78 para toda cadena.
  (C) El cierre es INDIRECTO (cap. 5 §V; cap. 13). La arista E6→E5 estuvo retirada y se RESTITUYE (18-oct): las tres
      dependencias «en sentido inverso» de p. 141 siguen el orden inverso de los tres pasos de la fase 2
      (8→7, 7→6, 6→5) y la reciprocidad intrafase se sigue del principio de los niveles (ver ciclo/e6_e5_restitucion.md).
      Con ella, UNA cruzada basta (`conexo_solo_63`, `conexo_solo_54`); sin ninguna no hay vuelta (`sin_cruces`).
      8→7 y 7→6 son críticas; la fase 2 es recíproca por dentro (`fase2_recip`, `fase2_sin_65`).
      No hay primitivo `Con` (E8→E1).
  (D) Cierre externo (fuera de la tupla, hipotético): E8 actúa sobre la vida cristiana y de ahí salen
      datos nuevos para U (E0). Solo amplía U; la ley de E1 no cambia.
-/
set_option maxRecDepth 8192

namespace Ciclo

/-! ## (A) Ítems de la dialéctica y condición de interfaz E3→E4 -/
section Items
variable {W X1 X2 X3 H S R Q : Type}

/-- Ítems de E4: movimientos cristianos (primarios), narraciones de E3 y resultados de E2 (secundarios). -/
abbrev Items (M3 : E3.Mp) (x : E2.Mp W X1 X2 X3 H S R Q) : Type :=
  E4.Mcr M3 ⊕ E4.R3E M3 ⊕ E4.R2 x

def injMcr {M3 : E3.Mp} {x : E2.Mp W X1 X2 X3 H S R Q} (m : E4.Mcr M3) : Items M3 x := Sum.inl m
def injR3 {M3 : E3.Mp} {x : E2.Mp W X1 X2 X3 H S R Q} (n : E4.R3E M3) : Items M3 x := Sum.inr (Sum.inl n)
def injR2 {M3 : E3.Mp} {x : E2.Mp W X1 X2 X3 H S R Q} (r : E4.R2 x) : Items M3 x := Sum.inr (Sum.inr r)

/-- Condición de compatibilidad E3→E4: lo que E3 declara incompatible (`Inc`) es discrepancia (`Dsc`) para E4. -/
def IncEnDsc {PV : Type} (M3 : E3.Mp) (x : E2.Mp W X1 X2 X3 H S R Q)
    (M4 : E4.Mp PV (Items M3 x)) : Prop :=
  ∀ n n' : E4.R3E M3, M3.Inc n.val n'.val → M4.Dsc (injR3 n) (injR3 n')

/-- Las inyecciones son disjuntas: un ítem es de una sola procedencia. -/
theorem injR3_ne_injMcr {M3 : E3.Mp} {x : E2.Mp W X1 X2 X3 H S R Q} (n : E4.R3E M3) (m : E4.Mcr M3) :
    (injR3 n : Items M3 x) ≠ injMcr m := by
  intro h; cases h

theorem injR2_ne_injR3 {M3 : E3.Mp} {x : E2.Mp W X1 X2 X3 H S R Q} (r : E4.R2 x) (n : E4.R3E M3) :
    (injR2 r : Items M3 x) ≠ injR3 n := by
  intro h; cases h

end Items

/-- Los tipos de ítems del caso Bultmann no son vacíos (movimiento 0 y narración r1). -/
theorem Items_B_habitado : Nonempty (E4.Mcr E3.B) ∧ Nonempty (E4.R3E E3.B) :=
  ⟨⟨⟨0, show (0 : Fin 4).val < 3 by decide⟩⟩, ⟨⟨0, Or.inl rfl⟩⟩⟩

/-! ## (B) El grafo de las ocho especialidades -/

/-- Estado de formalización de un enlace. -/
inductive Estado
  | formal          -- demostrado en Lean
  | parcial         -- formalizado a medias (p. ej. 3→2 por L13)
  | anotada         -- decidido y documentado, aún sin cláusula en Lean
  | porFormalizar   -- por formalizar
  deriving DecidableEq

/-- Aristas «A influye en B». Nodos 0..7 = E1..E8. -/
def todas : List (Fin 8 × Fin 8 × Estado) :=
  [ -- cadena hacia adelante E1→E2→…→E8
    (0, 1, .porFormalizar), (1, 2, .formal), (2, 3, .formal), (3, 4, .formal),
    (4, 5, .formal), (5, 6, .formal), (6, 7, .formal),
    -- retornos dentro de cada fase
    (1, 0, .anotada), (2, 0, .porFormalizar), (2, 1, .parcial), (3, 1, .porFormalizar),
    (3, 2, .porFormalizar), (7, 6, .porFormalizar), (6, 5, .anotada), (5, 4, .porFormalizar),   -- E6→E5 (restituida, 18-oct)
    -- cruces entre fases
    (5, 2, .porFormalizar),   -- E6→E3
    (4, 3, .porFormalizar) ]  -- E5→E4

def aristas (ls : List (Fin 8 × Fin 8 × Estado)) (a b : Fin 8) : Bool :=
  ls.any (fun t => t.1 == a && t.2.1 == b)

/-- Quita la arista p→q. -/
def sin (ls : List (Fin 8 × Fin 8 × Estado)) (p q : Fin 8) : List (Fin 8 × Fin 8 × Estado) :=
  ls.filter (fun t => !(t.1 == p && t.2.1 == q))

/-- Caminos dirigidos. -/
inductive Camino (e : Fin 8 → Fin 8 → Bool) : Fin 8 → Fin 8 → Prop
  | nil (a : Fin 8) : Camino e a a
  | cons {a b c : Fin 8} : e a b = true → Camino e b c → Camino e a c

theorem Camino.trans {e : Fin 8 → Fin 8 → Bool} {a b c : Fin 8}
    (h1 : Camino e a b) (h2 : Camino e b c) : Camino e a c := by
  induction h1 with
  | nil _ => exact h2
  | cons hab _ ih => exact Camino.cons hab (ih h2)

/-- Fuertemente conexo: todo nodo alcanza a todo nodo. -/
def Fuerte (e : Fin 8 → Fin 8 → Bool) : Prop := ∀ a b, Camino e a b

/-- Una familia de conjuntos cerrados bajo aristas no deja salir un camino. -/
theorem cerrado {e : Fin 8 → Fin 8 → Bool} (P : Fin 8 → Prop)
    (hP : ∀ x y, P x → e x y = true → P y) {a b : Fin 8} (h : Camino e a b) (ha : P a) : P b := by
  induction h with
  | nil _ => exact ha
  | cons hab _ ih => exact ih (hP _ _ ha hab)

/-! ### Alcance computable (BFS) y su corrección -/
def crece (e : Fin 8 → Fin 8 → Bool) (S : List (Fin 8)) : List (Fin 8) :=
  S ++ (List.range 8).filterMap (fun m =>
    if h : m < 8 then (if S.any (fun s => e s ⟨m, h⟩) then some ⟨m, h⟩ else none) else none)

def alc (e : Fin 8 → Fin 8 → Bool) (a : Fin 8) : Nat → List (Fin 8)
  | 0 => [a]
  | k+1 => crece e (alc e a k)

theorem alc_sound (e : Fin 8 → Fin 8 → Bool) (a : Fin 8) :
    ∀ k s, s ∈ alc e a k → Camino e a s := by
  intro k
  induction k with
  | zero =>
    intro s hs
    simp [alc] at hs
    subst hs
    exact Camino.nil _
  | succ k ih =>
    intro s hs
    simp only [alc, crece, List.mem_append, List.mem_filterMap] at hs
    rcases hs with hs | ⟨m, _, hm⟩
    · exact ih s hs
    · by_cases h : m < 8
      · rw [dif_pos h] at hm
        by_cases hany : (alc e a k).any (fun s => e s ⟨m, h⟩) = true
        · rw [if_pos hany] at hm
          cases hm
          obtain ⟨s', hs', hcb⟩ := List.any_eq_true.1 hany
          exact (ih s' hs').trans (Camino.cons hcb (Camino.nil _))
        · rw [if_neg hany] at hm; cases hm
      · rw [dif_neg h] at hm; cases hm

/-! ### Resultados -/

/-- Con todas las aristas autorizadas, el grafo es fuertemente conexo. -/
theorem conexo : Fuerte (aristas todas) := by
  intro a b
  apply alc_sound _ a 8 b
  revert a b
  decide

/-- E5→E4 no es necesaria para la conexidad: sin ella (solo E6→E3) el grafo sigue siendo fuertemente conexo. -/
theorem conexo_solo_63 : Fuerte (aristas (sin todas 4 3)) := by
  intro a b
  apply alc_sound _ a 8 b
  revert a b
  decide

/-- Con E6→E5 restituida, UNA cruzada basta: sin E6→E3 (solo E5→E4) el grafo sigue siendo fuertemente conexo. -/
theorem conexo_solo_54 : Fuerte (aristas (sin todas 5 2)) := by
  intro a b
  apply alc_sound _ a 8 b
  revert a b
  decide

/-- E6→E5 es crítica para la reciprocidad de la fase 2: sin ella E5 no recibe nada de E6–E8. -/
theorem fase2_sin_65 : ¬ Camino (fun x y => aristas (sin todas 5 4) x y && decide (4 ≤ x.val) && decide (4 ≤ y.val)) 5 4 := by
  intro h
  have hc : ∀ x y : Fin 8, 5 ≤ x.val →
      (aristas (sin todas 5 4) x y && decide (4 ≤ x.val) && decide (4 ≤ y.val)) = true → 5 ≤ y.val := by
    decide
  have h4 : 5 ≤ (4 : Fin 8).val :=
    cerrado (fun x : Fin 8 => 5 ≤ x.val) hc h (show 5 ≤ (5 : Fin 8).val by decide)
  exact absurd h4 (by decide)

/-- La fase 2 es fuertemente conexa por dentro (reciprocidad de p. 141) gracias a E6→E5. -/
theorem fase2_recip : ∀ a b : Fin 8, 4 ≤ a.val → 4 ≤ b.val →
    Camino (fun x y => aristas todas x y && decide (4 ≤ x.val) && decide (4 ≤ y.val)) a b := by
  intro a b ha hb
  apply alc_sound _ a 8 b
  revert a b
  decide

/-- Sin ninguna arista cruzada, E8 no alcanza a E1: los retornos internos solos no cierran el ciclo. -/
theorem sin_cruces : ¬ Camino (aristas (sin (sin todas 5 2) 4 3)) 7 0 := by
  intro h
  have hc : ∀ x y : Fin 8, 4 ≤ x.val → aristas (sin (sin todas 5 2) 4 3) x y = true → 4 ≤ y.val := by
    decide
  have h4 : 4 ≤ (0 : Fin 8).val :=
    cerrado (fun x : Fin 8 => 4 ≤ x.val) hc h (show 4 ≤ (7 : Fin 8).val by decide)
  exact absurd h4 (by decide)

/-- La arista E8→E7 es crítica: sin ella E8 no alcanza a nadie. -/
theorem critica_87 : ¬ Camino (aristas (sin todas 7 6)) 7 0 := by
  intro h
  have hc : ∀ x y : Fin 8, x.val = 7 → aristas (sin todas 7 6) x y = true → y.val = 7 := by
    decide
  have h4 : (0 : Fin 8).val = 7 :=
    cerrado (fun x : Fin 8 => x.val = 7) hc h (show (7 : Fin 8).val = 7 by decide)
  exact absurd h4 (by decide)

/-- La arista E7→E6 es crítica: {E7, E8} quedaría cerrado. -/
theorem critica_76 : ¬ Camino (aristas (sin todas 6 5)) 7 0 := by
  intro h
  have hc : ∀ x y : Fin 8, 6 ≤ x.val → aristas (sin todas 6 5) x y = true → 6 ≤ y.val := by
    decide
  have h4 : 6 ≤ (0 : Fin 8).val :=
    cerrado (fun x : Fin 8 => 6 ≤ x.val) hc h (show 6 ≤ (7 : Fin 8).val by decide)
  exact absurd h4 (by decide)


/-! ## (E) Enlace E2→E3→E4: consistencia e independencia (grados A y B)

  E3 trae su propio modelo de E2 (`M3.xM`), de modo que los ítems de E4 se construyen solo desde `M3`.
  `M4gen D` es un modelo de E4 sobre `ItemsE3 M3` con relación `rel` vacía y discrepancias `D` a elección:
  la ley de E4 se cumple para cualquier `D`; la condición `IncEnDsc` es lo que ata `D` a E3.
-/
section Enlace34

abbrev ItemsE3 (M3 : E3.Mp) : Type := Items M3 M3.xM

def M4gen (M3 : E3.Mp) (D : ItemsE3 M3 → ItemsE3 M3 → Prop) : E4.Mp Unit (ItemsE3 M3) where
  CT := Unit
  Ep := Unit
  Mf := Unit
  Et := Unit
  Vr := Unit
  car := fun _ => (((), (), ()), (), ())
  cvi := fun _ => true
  cvm := fun _ => true
  cvr := fun _ => true
  sgE := fun _ _ => True
  sgM := fun _ _ => True
  Odl3 := fun _ => True
  rel := fun _ _ => none
  Dsc := D
  Afn := fun _ _ => False
  Rz := Unit
  red := fun _ _ => ()
  cls := fun _ _ => True
  ot := fun _ _ _ => True
  V := fun _ _ => False
  Va := Unit
  vl4 := fun _ _ => False
  sgV := fun _ => true
  Yo := Unit
  sost := fun _ _ => False
  df := fun _ _ => False
  Base := Unit
  π := fun _ => ()
  dsc_afn_disj := fun _ _ h => h.2
  cls_ne := fun _ => ⟨E4.Op.datos, trivial⟩

theorem M4gen_ley (M3 : E3.Mp) (D : ItemsE3 M3 → ItemsE3 M3 → Prop) : E4.Ley (M4gen M3 D) := by
  have hp : ∀ x y, ¬ (M4gen M3 D).prec x y := by
    rintro x y ⟨a, b, _, _, _, _, hr⟩
    simp [M4gen] at hr
  exact
    { L1 := fun _ _ => rfl
      L2 := fun a b h => absurd h (by simp [M4gen])
      L3a := fun _ => ⟨(), trivial, rfl⟩
      L3b := fun _ _ _ _ => ⟨fun _ => E4.Mp.EqC.refl trivial, fun _ => rfl⟩
      L6a := fun a b _ _ h => by simp [M4gen] at h
      L6b := fun x y h => by
        obtain ⟨⟨a, b, _, _, _, _, hr⟩, _⟩ := h
        simp [M4gen] at hr
      L6c := fun x h => by
        cases h with
        | base h => exact hp _ _ h
        | step _ h => exact hp _ _ h
      L7 := fun a b r h _ => by simp [M4gen] at h
      L9 := fun _ _ _ => Iff.rfl
      L10 := fun p h _ => h ⟨trivial, trivial⟩ }

/-- Discrepancias canónicas: las narraciones incompatibles de E3. -/
def DscInc (M3 : E3.Mp) : ItemsE3 M3 → ItemsE3 M3 → Prop :=
  fun i j => ∃ n n' : E4.R3E M3, i = injR3 n ∧ j = injR3 n' ∧ M3.Inc n.val n'.val

/-- A: la ley de E4 y la condición de enlace E3→E4 son compatibles, para cualquier modelo de E3. -/
theorem enlace34_consistente (M3 : E3.Mp) :
    ∃ M4 : E4.Mp Unit (ItemsE3 M3), E4.Ley M4 ∧ IncEnDsc M3 M3.xM M4 :=
  ⟨M4gen M3 (DscInc M3), M4gen_ley M3 _, fun n n' h => ⟨n, n', rfl, rfl, h⟩⟩

/-- B: la ley de E4 no implica el enlace. Si E3 declara alguna incompatibilidad, hay un modelo de E4
    que cumple la ley y no la recoge: la condición `IncEnDsc` es una restricción genuina. -/
theorem enlace34_independiente (M3 : E3.Mp) (h : ∃ n n' : E4.R3E M3, M3.Inc n.val n'.val) :
    ∃ M4 : E4.Mp Unit (ItemsE3 M3), E4.Ley M4 ∧ ¬ IncEnDsc M3 M3.xM M4 := by
  obtain ⟨n, n', hi⟩ := h
  exact ⟨M4gen M3 (fun _ _ => False), M4gen_ley M3 _, fun hc => hc n n' hi⟩

end Enlace34


/-! ## (F) La cadena E4→E5→E6→E7→E8 como un solo objeto

  `Cadena48` reúne un modelo de cada especialidad, cada uno sobre el anterior, con su ley. Es la tupla
  conjunta de la parte formalizada del ciclo. `Ciclo_noVacio` la instancia con el caso Nicea–Constantinopla III.
  Los enlaces hacia adelante se enuncian como teoremas generales sobre CUALQUIER `Cadena48`.
-/
structure Cadena48 where
  PV : Type
  I : Type
  M : E4.Mp PV I
  LM : E4.Ley M
  X : E5.Mp M
  LX : E5.Ley X
  Y : E6.Mp X
  LY : E6.Ley Y
  Z : E7.Mp Y
  LZ : E7.Ley Z
  W : E8.Mp Z
  TW : W.Tipo
  LW : E8.Ley W

def nicea48 : Cadena48 :=
  { PV := Fin 4, I := Fin 4
    M := E6.NiceaE4, LM := E6.NiceaE4_ley
    X := E6.NiceaX, LX := E6.NiceaX_ley
    Y := E6.NiceaY, LY := E6.NiceaY_ley
    Z := E7.NiceaZ, LZ := E7.nicea_Ley
    W := E8.NiceaW, TW := E8.nicea_Tipo, LW := E8.nicea_Ley }

/-- No vacuidad de la cadena E4–E8. -/
theorem Ciclo_noVacio : Nonempty Cadena48 := ⟨nicea48⟩

section EnlacesAdelante
variable (C : Cadena48)

/-- E4→E5: una conversión de la dialéctica no es sucesión genética. -/
theorem enlace45 {c : C.X.Cv} {b b' : C.M.Base} (h : C.X.tr c = some (b, b')) :
    ¬ E4.TG C.M.prec b b' := by
  intro ht
  obtain ⟨_, ⟨a, ha, hab, hpa⟩, ⟨a', ha', hab', hpa'⟩⟩ := C.LX.D2 c b b' h
  have e := E5.tg_prec_Pc C.LM ht ha ha' hab hab'
  exact (C.LX.D1 c).2 (hpa.symm.trans (e.trans hpa'))

/-- E5→E6: la sucesión genética entre horizontes no cambia el perfil. -/
theorem enlace56 {w w' : C.X.Om} (h : E6.Gnt C.X w w') : C.X.pf w = C.X.pf w' := by
  obtain ⟨b, b', ⟨a, ha, hab, hpa⟩, ⟨a', ha', hab', hpa'⟩, ht⟩ := h
  have e := E5.tg_prec_Pc C.LM ht ha ha' hab hab'
  exact hpa.symm.trans (e.trans hpa')

/-- E6→E7: una posición implica conversión plena y horizonte auténtico en hz(s). -/
theorem enlace67 {s : C.Z.Sy} (h : E7.Posc C.Z s) :
    ∀ d, C.Z.Dcs s d → C.X.pf (C.Z.hzs s) = (true, true, true) ∧ C.X.Aut (C.Z.hzs s) :=
  fun d hd => C.LY.L14 _ d (h.L14a d hd)

/-- E7→E8: hz(s) es receptivo para todo s ∈ Sis. -/
theorem enlace78 {s : C.Z.Sy} (h : C.Z.Sis s) : C.W.Rcp s (C.Z.hzs s) := by
  obtain ⟨_, _, hp⟩ := h
  intro d hd
  exact hp.L14a d (C.TW.2.2.2.2 s d hd)

end EnlacesAdelante

/-- Los cuatro enlaces se cumplen en el caso Nicea (no vacuidad con contenido). -/
theorem nicea48_enlaces :
    (∀ s : Fin 3, E7.NiceaZ.Sis s → E8.NiceaW.Rcp s (E7.NiceaZ.hzs s)) :=
  fun _ hs => enlace78 nicea48 hs

/-! ## (D) Cierre externo (fuera de la tupla)
  E8 actúa sobre la vida cristiana vivida; de ahí surgen datos nuevos para el universo U de E0.
  No se formaliza como arista del grafo: solo amplía U y no toca la ley de E1.
-/

end Ciclo
