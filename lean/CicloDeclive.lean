import CicloEnlaces
/-
  CicloDeclive · el declive como dinámica con mecanismo — Lean 4.22 (sin Mathlib, sin sorry).

  Antes (CicloF6): el declive era un ESTADO admitido por la ley (`NM4`: toda posición reclasificada como contraposición).
  Aquí se añade una DINÁMICA: un paso `Declina` con mecanismo, su iteración y una medida que decrece.

  MECANISMO [L] (lectura propia de Lonergan, pp. 58-60: el declive nace del rechazo de la autotrascendencia y se
  acumula: la situación empeora y deja de mostrar lo que habría mostrado): una base clasificada como POSICIÓN pasa a
  CONTRAPOSICIÓN cuando el horizonte desde el que se la clasifica no tiene la conversión plena (`hor b ≠ (1,1,1)`).
  Es el contrario del giro 2 de F5 (la dialéctica corrige y reclasifica una contraposición como posición).
  El horizonte de cada base se toma de E5 (`pf`), no se estipula aparte.

  Lo que se prueba: (1) cada paso quita exactamente una posición (medida `pos` estrictamente decreciente), (2) toda
  iteración de k pasos cumple `pos u + k = pos s` (luego k ≤ pos s: el declive termina), (3) es irreversible por este
  mecanismo (no hay vuelta), (4) si ningún horizonte tiene la conversión, el declive alcanza el estado de contraposición
  total en exactamente `pos s` pasos, (5) el puente: en Nicea el paso real de `NM` a `NM4` (ambos con `E4.Ley`) es un
  paso `Declina` con el horizonte 0 de E5.

  LÍMITES: (a) el mecanismo es abstracto sobre bases; sus extremos están realizados por modelos de E4 con ley
  (`NM`, `NM4`), pero los estados intermedios de una cadena larga no lo están (el E4 de Nicea tiene 2 bases, así que
  la cadena concreta tiene un solo paso); (b) que el horizonte no convertido CAUSE la reclasificación es [L], no está
  en una cláusula de E4 ni de E5; (c) el declive de Lonergan incluye el sesgo de grupo y la longitud del ciclo largo:
  no se modela; (d) no hay una medida común de progreso y declive (el progreso del giro 2 no es un `Paso`).
-/
namespace Ciclo
namespace Declive
open N

abbrev Conv : E4.Perfil := (true, true, true)

/-- Número de bases (entre las k primeras) clasificadas como posición. -/
def pos (s : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k+1 => pos s k + (if s k then 1 else 0)

/-- Poner la base b en contraposición. -/
def flip (s : Nat → Bool) (b : Nat) : Nat → Bool := fun c => if c = b then false else s c

/-- Paso de declive: una base con posición pasa a contraposición si su horizonte no tiene la conversión plena. -/
def Declina (n : Nat) (hor : Nat → E4.Perfil) (s t : Nat → Bool) : Prop :=
  ∃ b, b < n ∧ s b = true ∧ hor b ≠ Conv ∧ t = flip s b

/-- Iteración de k pasos. -/
def Itera (n : Nat) (hor : Nat → E4.Perfil) : Nat → (Nat → Bool) → (Nat → Bool) → Prop
  | 0, s, u => s = u
  | k+1, s, u => ∃ t, Declina n hor s t ∧ Itera n hor k t u

theorem pos_congr (f g : Nat → Bool) : ∀ k, (∀ c, c < k → f c = g c) → pos f k = pos g k
  | 0, _ => rfl
  | k+1, h => by
    simp only [pos]
    rw [pos_congr f g k (fun c hc => h c (by omega)), h k (by omega)]

theorem pos_flip (s : Nat → Bool) (b : Nat) :
    ∀ k, b < k → s b = true → pos (flip s b) k + 1 = pos s k
  | 0, hb, _ => absurd hb (Nat.not_lt_zero _)
  | k+1, hb, hs => by
    by_cases hk : b = k
    · subst hk
      have h1 : pos (flip s b) b = pos s b :=
        pos_congr _ _ b (fun c hc => by simp [flip, Nat.ne_of_lt hc])
      have h2 : flip s b b = false := by simp [flip]
      simp only [pos, h1, h2, hs]
      simp
    · have ih := pos_flip s b k (by omega) hs
      have hk' : k ≠ b := fun h => hk h.symm
      have h2 : flip s b k = s k := by simp [flip, hk']
      simp only [pos, h2]
      omega

/-- (1) Cada paso quita exactamente una posición. -/
theorem declina_decrece {n hor s t} (h : Declina n hor s t) : pos t n + 1 = pos s n := by
  obtain ⟨b, hb, hs, _, rfl⟩ := h
  exact pos_flip s b n hb hs

/-- (2) Una iteración de k pasos quita k posiciones. -/
theorem itera_cota {n hor} : ∀ k s u, Itera n hor k s u → pos u n + k = pos s n
  | 0, s, u, h => by
    have : s = u := h
    subst this; rfl
  | k+1, s, u, ⟨t, ht, hi⟩ => by
    have h1 := declina_decrece ht
    have h2 := itera_cota k t u hi
    omega

/-- El declive termina: ninguna cadena de pasos es más larga que el número de posiciones. -/
theorem declive_acotado {n hor k s u} (h : Itera n hor k s u) : k ≤ pos s n := by
  have := itera_cota k s u h
  omega

/-- (3) Sin vuelta: por este mecanismo un estado no se alcanza a sí mismo en ≥ 1 pasos. -/
theorem sin_vuelta {n hor k s} (hk : 0 < k) : ¬ Itera n hor k s s := by
  intro h
  have := itera_cota k s s h
  omega

/-- Estable: ninguna base con posición tiene un horizonte sin conversión. -/
def Estable (n : Nat) (hor : Nat → E4.Perfil) (s : Nat → Bool) : Prop :=
  ∀ b, b < n → s b = true → hor b = Conv

theorem estable_iff {n hor s} : (¬ ∃ t, Declina n hor s t) ↔ Estable n hor s := by
  constructor
  · intro h b hb hs
    by_cases e : hor b = Conv
    · exact e
    · exact absurd ⟨_, b, hb, hs, e, rfl⟩ h
  · rintro h ⟨t, b, hb, hs, hne, _⟩
    exact hne (h b hb hs)

theorem pos_cero (s : Nat → Bool) : ∀ k, pos s k = 0 → ∀ c, c < k → s c = false
  | 0, _, c, hc => absurd hc (Nat.not_lt_zero _)
  | k+1, h, c, hc => by
    simp only [pos] at h
    by_cases hk : c = k
    · subst hk
      by_cases e : s c = true
      · simp [e] at h
      · simpa using e
    · exact pos_cero s k (by omega) c (by omega)

theorem existe_pos (s : Nat → Bool) : ∀ k, pos s k ≠ 0 → ∃ b, b < k ∧ s b = true
  | 0, h => absurd rfl h
  | k+1, h => by
    simp only [pos] at h
    by_cases e : s k = true
    · exact ⟨k, by omega, e⟩
    · have h' : pos s k ≠ 0 := by simp [e] at h; exact h
      obtain ⟨b, hb, hs⟩ := existe_pos s k h'
      exact ⟨b, by omega, hs⟩

/-- (4) Si ningún horizonte tiene la conversión, el declive llega a la contraposición total en exactamente `pos s` pasos. -/
theorem declive_total {n : Nat} {hor : Nat → E4.Perfil} (hh : ∀ b, b < n → hor b ≠ Conv) :
    ∀ m s, pos s n = m → ∃ u, Itera n hor m s u ∧ ∀ b, b < n → u b = false
  | 0, s, h => ⟨s, rfl, pos_cero s n h⟩
  | m+1, s, h => by
    obtain ⟨b, hb, hs⟩ := existe_pos s n (by omega)
    have hf := pos_flip s b n hb hs
    obtain ⟨u, hi, hu⟩ := declive_total hh m (flip s b) (by omega)
    exact ⟨u, ⟨_, ⟨b, hb, hs, hh b hb, rfl⟩, hi⟩, hu⟩

/-! ## Puente con Nicea: los extremos son modelos de E4 con ley -/

/-- Horizontes de las dos bases de Nicea, tomados de E5: la base 0 se clasifica desde el horizonte 0 (perfil (1,0,0)),
    la base 1 desde el horizonte 2 (perfil (1,1,1)). -/
def horN (b : Nat) : E4.Perfil := if b = 0 then nicea38c.X.pf 0 else nicea38c.X.pf 2

/-- Bases con posición: en `NM` solo la 0; en `NM4` ninguna. -/
def sNM (b : Nat) : Bool := decide (b = 0)
def sNM4 (_ : Nat) : Bool := false

theorem sNM_es_NM : ∀ b : Fin 2, N.NM.PosB Conv b ↔ sNM b.val = true := by decide
theorem sNM4_es_NM4 : ∀ b : Fin 2, N.NM4.PosB Conv b ↔ sNM4 b.val = true := by decide

/-- El paso real de `NM` a `NM4` es un paso `Declina` con el horizonte de E5 de la base 0. -/
theorem paso_nicea : Declina 2 horN sNM sNM4 := by
  refine ⟨0, by decide, rfl, by decide, ?_⟩
  funext c
  by_cases h : c = 0
  · subst h; simp [flip, sNM4]
  · simp [flip, sNM, sNM4, h]

/-- Puente completo: ambos extremos cumplen la ley de E4 y conservan el enlace con E3; el paso entre ellos es de declive. -/
theorem puente_nicea :
    E4.Ley N.NM ∧ E4.Ley N.NM4 ∧ IncEnDsc N.N3 N.N3.xM N.NM4 ∧ Declina 2 horN sNM sNM4 ∧
    pos sNM 2 = 1 ∧ pos sNM4 2 = 0 :=
  ⟨N.NM_ley, N.NM4_ley, N.NM_enlace, paso_nicea, by decide, by decide⟩

/-- La base 1 (contraposición) tiene un horizonte con conversión: el mecanismo no la toca; y la 0 sí. -/
theorem horizontes_nicea : horN 0 ≠ Conv ∧ horN 1 = Conv := by decide

/-- El mecanismo es sensible al horizonte: con un horizonte convertido en la base 0 el paso no existe. -/
theorem sin_sesgo_no_declina : ¬ Declina 2 (fun _ => Conv) sNM sNM4 := by
  rintro ⟨b, _, _, h, _⟩
  exact h rfl

#print axioms declina_decrece
#print axioms itera_cota
#print axioms declive_total
#print axioms puente_nicea
#print axioms sin_sesgo_no_declina

end Declive
end Ciclo
