import CicloRetornosB
/-
  CicloF2 · F2 (independencia y rigidez) — Lean 4.22 (sin Mathlib, sin sorry).

  Tres cosas, con su alcance exacto:
  (1) Criticidad de cada una de las 17 aristas del grafo para la conexidad fuerte (grado D del plan en su parte
      de cerradura): una arista es CRÍTICA si sin ella el grafo deja de ser fuertemente conexo; REDUNDANTE si
      el grafo sigue conexo. Esto NO dice que una arista redundante sobre: su justificación es el texto de Lonergan
      y la no redundancia de su condición (2).
  (2) Un libro de cuentas (`ledger`) que reúne, en un solo enunciado, los teoremas de exclusión/independencia
      ya probados en Ciclo, CicloNicea, CicloRetornos y CicloRetornosB (grado B: la condición del enlace no es
      redundante: hay un caso que cumple las leyes de cada E_i y viola el enlace).
  (3) La cerradura es la mínima (grado D, unicidad): `Camino` es la menor relación reflexiva y transitiva que
      contiene a las aristas autorizadas.
-/
namespace Ciclo

/-! ## (3) Cerradura mínima -/
theorem camino_minima {e : Fin 8 → Fin 8 → Bool} (R : Fin 8 → Fin 8 → Prop)
    (hr : ∀ a, R a a) (ht : ∀ a b c, R a b → R b c → R a c) (he : ∀ a b, e a b = true → R a b)
    {a b : Fin 8} (h : Camino e a b) : R a b := by
  induction h with
  | nil _ => exact hr _
  | cons hab _ ih => exact ht _ _ _ (he _ _ hab) ih


/-! ## (1) Criticidad de las 17 aristas -/

/-- E1→E2: CRÍTICA (sin ella, desde E1 no se alcanza E2). -/
theorem critica_01_ : ¬ Fuerte (aristas (sin todas 0 1)) := by
  intro h
  have hc : ∀ x y : Fin 8, x.val ∈ [0] → aristas (sin todas 0 1) x y = true → y.val ∈ [0] := by
    decide
  have h2 := cerrado (fun x : Fin 8 => x.val ∈ [0]) hc (h 0 1) (by decide)
  exact absurd h2 (by decide)

/-- E2→E3: CRÍTICA (sin ella, desde E1 no se alcanza E3). -/
theorem critica_12_ : ¬ Fuerte (aristas (sin todas 1 2)) := by
  intro h
  have hc : ∀ x y : Fin 8, x.val ∈ [0, 1] → aristas (sin todas 1 2) x y = true → y.val ∈ [0, 1] := by
    decide
  have h2 := cerrado (fun x : Fin 8 => x.val ∈ [0, 1]) hc (h 0 2) (by decide)
  exact absurd h2 (by decide)

/-- E3→E4: CRÍTICA (sin ella, desde E1 no se alcanza E4). -/
theorem critica_23_ : ¬ Fuerte (aristas (sin todas 2 3)) := by
  intro h
  have hc : ∀ x y : Fin 8, x.val ∈ [0, 1, 2] → aristas (sin todas 2 3) x y = true → y.val ∈ [0, 1, 2] := by
    decide
  have h2 := cerrado (fun x : Fin 8 => x.val ∈ [0, 1, 2]) hc (h 0 3) (by decide)
  exact absurd h2 (by decide)

/-- E4→E5: CRÍTICA (sin ella, desde E1 no se alcanza E5). -/
theorem critica_34_ : ¬ Fuerte (aristas (sin todas 3 4)) := by
  intro h
  have hc : ∀ x y : Fin 8, x.val ∈ [0, 1, 2, 3] → aristas (sin todas 3 4) x y = true → y.val ∈ [0, 1, 2, 3] := by
    decide
  have h2 := cerrado (fun x : Fin 8 => x.val ∈ [0, 1, 2, 3]) hc (h 0 4) (by decide)
  exact absurd h2 (by decide)

/-- E5→E6: CRÍTICA (sin ella, desde E1 no se alcanza E6). -/
theorem critica_45_ : ¬ Fuerte (aristas (sin todas 4 5)) := by
  intro h
  have hc : ∀ x y : Fin 8, x.val ∈ [0, 1, 2, 3, 4] → aristas (sin todas 4 5) x y = true → y.val ∈ [0, 1, 2, 3, 4] := by
    decide
  have h2 := cerrado (fun x : Fin 8 => x.val ∈ [0, 1, 2, 3, 4]) hc (h 0 5) (by decide)
  exact absurd h2 (by decide)

/-- E6→E7: CRÍTICA (sin ella, desde E1 no se alcanza E7). -/
theorem critica_56_ : ¬ Fuerte (aristas (sin todas 5 6)) := by
  intro h
  have hc : ∀ x y : Fin 8, x.val ∈ [0, 1, 2, 3, 4, 5] → aristas (sin todas 5 6) x y = true → y.val ∈ [0, 1, 2, 3, 4, 5] := by
    decide
  have h2 := cerrado (fun x : Fin 8 => x.val ∈ [0, 1, 2, 3, 4, 5]) hc (h 0 6) (by decide)
  exact absurd h2 (by decide)

/-- E7→E8: CRÍTICA (sin ella, desde E1 no se alcanza E8). -/
theorem critica_67_ : ¬ Fuerte (aristas (sin todas 6 7)) := by
  intro h
  have hc : ∀ x y : Fin 8, x.val ∈ [0, 1, 2, 3, 4, 5, 6] → aristas (sin todas 6 7) x y = true → y.val ∈ [0, 1, 2, 3, 4, 5, 6] := by
    decide
  have h2 := cerrado (fun x : Fin 8 => x.val ∈ [0, 1, 2, 3, 4, 5, 6]) hc (h 0 7) (by decide)
  exact absurd h2 (by decide)

/-- E2→E1: REDUNDANTE para la conexidad. -/
theorem redundante_10 : Fuerte (aristas (sin todas 1 0)) := by
  intro a b
  apply alc_sound _ a 8 b
  revert a b
  decide

/-- E3→E1: REDUNDANTE para la conexidad. -/
theorem redundante_20 : Fuerte (aristas (sin todas 2 0)) := by
  intro a b
  apply alc_sound _ a 8 b
  revert a b
  decide

/-- E3→E2: REDUNDANTE para la conexidad. -/
theorem redundante_21 : Fuerte (aristas (sin todas 2 1)) := by
  intro a b
  apply alc_sound _ a 8 b
  revert a b
  decide

/-- E4→E2: REDUNDANTE para la conexidad. -/
theorem redundante_31 : Fuerte (aristas (sin todas 3 1)) := by
  intro a b
  apply alc_sound _ a 8 b
  revert a b
  decide

/-- E4→E3: REDUNDANTE para la conexidad. -/
theorem redundante_32 : Fuerte (aristas (sin todas 3 2)) := by
  intro a b
  apply alc_sound _ a 8 b
  revert a b
  decide

/-- E8→E7: CRÍTICA (sin ella, desde E8 no se alcanza E1). -/
theorem critica_76_ : ¬ Fuerte (aristas (sin todas 7 6)) := by
  intro h
  have hc : ∀ x y : Fin 8, x.val ∈ [7] → aristas (sin todas 7 6) x y = true → y.val ∈ [7] := by
    decide
  have h2 := cerrado (fun x : Fin 8 => x.val ∈ [7]) hc (h 7 0) (by decide)
  exact absurd h2 (by decide)

/-- E7→E6: CRÍTICA (sin ella, desde E7 no se alcanza E1). -/
theorem critica_65_ : ¬ Fuerte (aristas (sin todas 6 5)) := by
  intro h
  have hc : ∀ x y : Fin 8, x.val ∈ [6, 7] → aristas (sin todas 6 5) x y = true → y.val ∈ [6, 7] := by
    decide
  have h2 := cerrado (fun x : Fin 8 => x.val ∈ [6, 7]) hc (h 6 0) (by decide)
  exact absurd h2 (by decide)

/-- E6→E5: REDUNDANTE para la conexidad. -/
theorem redundante_54 : Fuerte (aristas (sin todas 5 4)) := by
  intro a b
  apply alc_sound _ a 8 b
  revert a b
  decide

/-- E6→E3: REDUNDANTE para la conexidad. -/
theorem redundante_52 : Fuerte (aristas (sin todas 5 2)) := by
  intro a b
  apply alc_sound _ a 8 b
  revert a b
  decide

/-- E5→E4: REDUNDANTE para la conexidad. -/
theorem redundante_43 : Fuerte (aristas (sin todas 4 3)) := by
  intro a b
  apply alc_sound _ a 8 b
  revert a b
  decide

/-- Clasificación de las 17 aristas. -/
theorem clasificacion :
    ¬ Fuerte (aristas (sin todas 0 1)) ∧
    ¬ Fuerte (aristas (sin todas 1 2)) ∧
    ¬ Fuerte (aristas (sin todas 2 3)) ∧
    ¬ Fuerte (aristas (sin todas 3 4)) ∧
    ¬ Fuerte (aristas (sin todas 4 5)) ∧
    ¬ Fuerte (aristas (sin todas 5 6)) ∧
    ¬ Fuerte (aristas (sin todas 6 7)) ∧
    ¬ Fuerte (aristas (sin todas 7 6)) ∧
    ¬ Fuerte (aristas (sin todas 6 5)) ∧
    Fuerte (aristas (sin todas 1 0)) ∧
    Fuerte (aristas (sin todas 2 0)) ∧
    Fuerte (aristas (sin todas 2 1)) ∧
    Fuerte (aristas (sin todas 3 1)) ∧
    Fuerte (aristas (sin todas 3 2)) ∧
    Fuerte (aristas (sin todas 5 4)) ∧
    Fuerte (aristas (sin todas 5 2)) ∧
    Fuerte (aristas (sin todas 4 3)) :=
  ⟨critica_01_, critica_12_, critica_23_, critica_34_, critica_45_, critica_56_, critica_67_, critica_76_, critica_65_, redundante_10, redundante_20, redundante_21, redundante_31, redundante_32, redundante_54, redundante_52, redundante_43⟩

/-! ## (2) Libro de cuentas de la no redundancia de las condiciones de enlace (grado B) -/

/-- Cada enunciado es el de un teorema ya compilado; su reunión comprueba que todos existen en esta versión de la cadena
    (con E3 de L3 corregida). -/
theorem ledger :
    (type_of% @N.nicea_enlace_independiente) ∧
    (type_of% @retorno87_nicea_excluye) ∧
    (type_of% @retorno76_nicea_excluye_sA) ∧
    (type_of% @retorno54_nicea_cubre_necesaria) ∧
    (type_of% @retorno63_nicea_dominio) ∧
    (type_of% @retorno65_nicea_excluye_inaut) ∧
    (type_of% @CicloB.yMalD_no_ext) ∧
    (type_of% @CicloB.yMalG_no_ext) ∧
    (type_of% @CicloB.yMalK_no_ext) ∧
    (type_of% @CicloB.clasif_mala_excluida) ∧
    (type_of% @CicloB.contexto_mal_excluido) ∧
    (type_of% @CicloB.comp_creciente_excluida) :=
  ⟨N.nicea_enlace_independiente, retorno87_nicea_excluye, retorno76_nicea_excluye_sA,
   retorno54_nicea_cubre_necesaria, retorno63_nicea_dominio, retorno65_nicea_excluye_inaut, CicloB.yMalD_no_ext, CicloB.yMalG_no_ext,
   CicloB.yMalK_no_ext, CicloB.clasif_mala_excluida, CicloB.contexto_mal_excluido,
   CicloB.comp_creciente_excluida⟩

end Ciclo

#print axioms Ciclo.clasificacion
#print axioms Ciclo.ledger
#print axioms Ciclo.camino_minima
