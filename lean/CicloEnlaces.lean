import CicloCaso
/-
  CicloEnlaces · enlaces sueltos y no interferencia — Lean 4.22 (sin Mathlib, sin sorry).

  1. NO INTERFERENCIA COMO TEOREMA. Hasta ahora «los retornos no tocan las leyes» valía por construcción (la estructura
     `Modelo` guarda la `Cadena38` aparte). Aquí se prueba que es una propiedad real y no un accidente de la definición:
     · `conservativa`: TODA `Cadena38` (con sus leyes E3–E8 y el enlace E3→E4) se extiende a un `Modelo` con retornos
       mínimos; es decir, ninguna condición de los retornos ni de E1 restringe lo que pueden ser las leyes (extensión
       conservativa). Con `Modelo.cadena` (olvidar) la proyección Modelo → Cadena38 es sobreyectiva.
     · `fase1_abierta`: los retornos hacia E1 no pueden tocar D¹ de las cuestiones viejas ni G (la cautela de
       Lonergan, pp. 141-142, sobre la apertura de la primera fase) — consecuencia de `ExtE1`, no promesa.
  2. HORIZONTES E3→E5 (`EnlaceHz`): cada punto de vista de E3 clasificado por E4 (`ClasifE4.modo p v`) tiene un horizonte
     de E5 cuyo perfil `pf` es el `Pc` del punto de vista de E4. Es [E] (decisión de modelado), no cita de Lonergan.
  3. Lg ↔ Lug (E3 ↔ E8): decisión de NO identificar (ver `lug_decision`).
  4. E3→E4: ya vive en `Cadena38.enlace` (`IncEnDsc`); no estaba suelto. Se deja constancia (`enlace34_en_cadena`).
-/
namespace Ciclo
open N CicloB E1

/-! ## 1. No interferencia -/

/-- E1 trivial sobre cualquier universo de datos (sin cuestiones; área = todo; todo necesario; todo reunido). -/
def yTriv (U : Type) : E1Base U where
  Q1 := Empty
  D1 := fun _ _ => True
  D1_Delta := fun _ => trivial
  Ar := fun c => c = todo
  Ar_todo := rfl
  Ar_cadena := by
    intro a b ha hb
    subst ha; subst hb
    exact Or.inl (fun _ h => h)
  Ad := todo
  Ad_mem := rfl
  K := fun _ => true
  G := fun _ => True

def extId (U : Type) : ExtE1 (yTriv U) (yTriv U) where
  ι := id
  D1_ι := fun _ _ => Iff.rfl
  G_eq := fun _ => Iff.rfl
  K_mono := fun _ h => h
  Ad_mono := fun _ h => h

def compTriv (U X : Type) : CompE U X := ⟨fun _ _ => True, fun _ _ _ _ _ => trivial⟩

def clasifVacia {PV I : Type} (M : E4.Mp PV I) (X : Type) : ClasifE4 M X :=
  ⟨fun _ => none, fun _ _ => False, fun _ _ h => h.elim⟩

theorem todos_los_perfiles (p : E4.Perfil) :
    p ∈ [((false, false, false) : E4.Perfil), (false, false, true), (false, true, false), (false, true, true),
         (true, false, false), (true, false, true), (true, true, false), (true, true, true)] := by
  obtain ⟨a, b, c⟩ := p
  cases a <;> cases b <;> cases c <;> decide

/-- Retornos mínimos sobre cualquier cadena: todas las relaciones vacías (o constantes donde la estructura lo exige). -/
def retornosMinimos (C : N.Cadena38) : Modelo where
  C := C
  y := yTriv C.M3.U
  y' := yTriv C.M3.U
  e := extId C.M3.U
  r87 := RetornoE8E7.vacio C
  r76 := ⟨fun _ _ => False, fun _ _ h => h.elim, fun _ _ h => h.elim⟩
  r65 := ⟨fun _ _ => False, fun _ _ h => h.elim⟩
  r54 :=
    { Fam := fun _ => C.M
      ley_fam := fun _ => C.LM
      Q := [((false, false, false) : E4.Perfil), (false, false, true), (false, true, false), (false, true, true),
            (true, false, false), (true, false, true), (true, true, false), (true, true, true)]
      cubre := fun w => todos_los_perfiles _
      actual := fun _ => rfl
      D := E4.domRec _
      viii := E4.leyRec_domRec _ _ }
  r63 := ⟨fun _ => C.M3.r1⟩
  p21 := ⟨fun _ _ => False, fun _ _ h => h.elim, fun _ _ h => h.elim⟩
  p31 := ⟨fun _ _ => False, fun _ _ h => h.elim, fun _ _ h => h.elim⟩
  c42 := clasifVacia C.M C.M3.X1
  c43 := clasifVacia C.M C.M3.Vt
  cm := compTriv _ _
  ca := compTriv _ _
  cr := compTriv _ _
  debil := fun _ => ⟨trivial, trivial, trivial⟩

/-- NO INTERFERENCIA (extensión conservativa): toda cadena E3–E8 con sus leyes y el enlace E3→E4 es la cadena de algún
    `Modelo` del ciclo. Los retornos y E1 no imponen ninguna condición sobre las leyes de E3–E8. -/
theorem conservativa (C : N.Cadena38) : ∃ m : Modelo, m.cadena = C := ⟨retornosMinimos C, rfl⟩

/-- … y por tanto el ciclo no añade ni quita modelos de la cadena: las dos clases tienen la misma proyección. -/
theorem sin_nuevas_restricciones (P : N.Cadena38 → Prop) :
    (∀ m : Modelo, P m.cadena) ↔ (∀ C : N.Cadena38, P C) :=
  ⟨fun h C => by obtain ⟨m, rfl⟩ := conservativa C; exact h m, fun h m => h m.cadena⟩

/-- Cautela de Lonergan sobre la fase 1 (pp. 141-142): lo que vuelve a E1 desde E2 y E3 no cambia D¹ de las cuestiones
    ya planteadas ni la apertura G (datos reunidos). Teorema sobre todo `Modelo`. -/
theorem fase1_abierta (m : Modelo) :
    (∀ q u, m.y'.D1 (some (m.e.ι q)) u ↔ m.y.D1 (some q) u) ∧ (∀ u, m.y'.G u ↔ m.y.G u) :=
  ⟨m.e.D1_ι, m.e.G_eq⟩

/-- Y lo ya procurado se conserva: la extensión solo puede ganar. -/
theorem fase1_no_pierde (m : Modelo) (q : m.y.Q1) :
    Sub (m.y.res m.y.Ad q) (fun u => m.y'.res m.y'.Ad (m.e.ι q) u) :=
  m.e.no_pierde q

/-- E3→E4 no estaba suelto: el enlace vive en la cadena (`IncEnDsc`) y lo trae todo `Modelo`. -/
theorem enlace34_en_cadena (m : Modelo) : IncEnDsc m.C.M3 m.C.M3.xM m.C.M := m.C.enlace

/-! ## 2. Horizontes E3 → E5 -/

/-- Cada punto de vista `v` de E3 que E4 clasifica (`modo p v`) tiene un horizonte `hzE (ho v)` de E5 con el perfil del
    punto de vista `p`. Pasa por `ho` de E3 y por `pf` de E5 con `Pc` de E4: liga las tres. -/
structure EnlaceHz (C : N.Cadena38) (c : ClasifE4 C.M C.M3.Vt) where
  hzE : C.M3.Hz → C.X.Om
  coh : ∀ p v, c.modo p v → C.X.pf (hzE (C.M3.ho v)) = C.M.Pc p

/-- E4→E3 en la cadena con dialéctica de dos giros (`nicea38c`): solo el punto de vista 0 de E3 tiene perfil. -/
def c43c : ClasifE4 nicea38c.M nicea38c.M3.Vt where
  car2 := fun v => if v.val = 0 then some (nicea38c.M.car 0).1 else none
  modo := fun p v => v.val = 0 ∧ p.val = 0
  coh := fun p v h => by
    have hp : p = 0 := Fin.ext h.2
    subst hp
    simp [h.1]

def hzNicea : EnlaceHz nicea38c c43c where
  hzE := fun h => if h.val = 0 then 1 else 2
  coh := fun p v h => by
    have hp : p = 0 := Fin.ext h.2
    have hv : v = 0 := Fin.ext h.1
    subst hp; subst hv
    decide

theorem EnlaceHz_noVacio : Nonempty (EnlaceHz nicea38c c43c) := ⟨hzNicea⟩

/-- La condición es real: un `hzE` que manda todo al horizonte 0 (perfil (1,0,0)) contradice el perfil del punto de vista 0. -/
theorem hz_mal_excluido :
    ¬ ∀ p v, c43c.modo p v → nicea38c.X.pf ((fun _ => (0 : nicea38c.X.Om)) (nicea38c.M3.ho v)) = nicea38c.M.Pc p := by
  intro h
  have := h 0 0 ⟨rfl, rfl⟩
  revert this
  decide

/-! ## 3. Lg ↔ Lug: no se identifican -/

/-- DECISIÓN. `E3.Lg` (lugares de las fuentes: pasado) y `E8.Lug` (lugares de comunicación: futuro) no se identifican.
    Ninguna cláusula de E3 ni de E8 mira a la otra; Lonergan no las liga; y en el caso los cardinales son 3 y 2 (el `Lug`
    de la lectura de E8 no tiene asignación histórica). Un enlace `Lug → Lg` sin condición no ataría nada: se omite.
    Lo que sí se prueba: en el caso no hay inyección `Lg → Lug`, de modo que «identificar» sería falso, no solo gratuito. -/
theorem lug_decision : ¬ ∃ f : nicea38c.M3.Lg → nicea38c.W.Lug, ∀ a b, f a = f b → a = b := by
  rintro ⟨f, hf⟩
  have h0 : (f 0).val < 2 := (f 0).isLt
  have h1 : (f 1).val < 2 := (f 1).isLt
  have h2 : (f 2).val < 2 := (f 2).isLt
  by_cases e01 : f 0 = f 1
  · exact absurd (hf _ _ e01) (by decide)
  by_cases e02 : f 0 = f 2
  · exact absurd (hf _ _ e02) (by decide)
  by_cases e12 : f 1 = f 2
  · exact absurd (hf _ _ e12) (by decide)
  have n01 : (f 0).val ≠ (f 1).val := fun h => e01 (Fin.ext h)
  have n02 : (f 0).val ≠ (f 2).val := fun h => e02 (Fin.ext h)
  have n12 : (f 1).val ≠ (f 2).val := fun h => e12 (Fin.ext h)
  omega

#print axioms conservativa
#print axioms sin_nuevas_restricciones
#print axioms fase1_abierta
#print axioms hzNicea
#print axioms hz_mal_excluido
#print axioms lug_decision

end Ciclo
