import E0

/-!
# E1 (Investigación especial): núcleo, vínculo E0→E1, fase 3 (verificado en Lean 4, sin Mathlib)

Cambios respecto a E0E1v2.lean:

1. R1 deja de ser primitivo. Se recupera la definición del documento: `K : U → Bool` es primitivo
   y `R1 := K⁻¹(Sí)` (datos que la teología necesita). Se añade `G : U → Prop` (datos reunidos,
   en mano), que es lo que antes se llamaba R1 en el Lean. Un vacío es un dato necesario que no
   está reunido.
2. Δ ya no es un elemento de Q1: `Q1⁺ = Option Q1` con `none = Δ`. `D1 : Option Q1 → _` y
   `E1 : Q1 → _`, de modo que E1 no está definida en Δ.
3. E1 es un componente de Mp(E1) (con solo su tipo `E1 q ⊆ R1`) y la ley es el predicado `Ax`.
   M(E1) es el subtipo de los modelos que cumplen `Ax`. Vuelve a existir Mp ⊋ M.

Notación: D⁰ = D de E0; D¹ = D de E1 (aquí, `D1`).

Renombres (16 oct 2026, ver ciclo/renombres_enlaces_y_cierre_E0-E8.md): `a` → `Ad` (área adoptada,
choca con `a` de E2) y `a_mem` → `Ad_mem`. En E0: `G` → `Gn` (géneros; la G de E1 son los datos
reunidos) y `σ` → `pte` (puente f*→f; en el documento β, para no chocar con σ de E2).

Retornos hacia E1 (E3→E1, E2→E1; 18 oct 2026): viven fuera de esta tupla, en lean/CicloRetornosB.lean
(`ExtE1`: Q1, Ad y K solo se amplían; D¹ de las cuestiones viejas y G intactos; `Pide` apunta a un vacío).
Este archivo no cambia: la ley y los teoremas de abajo son los verificados con los renombres.

  Ley:  ∀ q ∈ Q1,  E1(q) = D¹(q) ∩ Ad ∩ R1 ∩ G

  (V1) E0 y E1 comparten U.
  (V2′) ∀ b ∈ Á, ∃ n ≤ N, b es unión de bloques de π_n.
  (V3) ∃ τ : Q1⁺ → 𝒫(f), D¹(q) ⊆ k⁻¹[τ(q)] y τ(Δ) = f.
-/

namespace E1
open E0

def todo {U : Type} : U → Prop := fun _ => True

/-- Inclusión de predicados (subconjuntos). -/
def Sub {U : Type} (a b : U → Prop) : Prop := ∀ u, a u → b u

/-- Mp(E1) sin el componente E1: todo lo que la ley usa. -/
structure E1Base (U : Type) where
  Q1        : Type
  D1        : Option Q1 → U → Prop                       -- D¹ sobre Q1⁺ (none = Δ)
  D1_Delta  : ∀ u, D1 none u                             -- D¹(Δ) = U
  Ar        : (U → Prop) → Prop                          -- Á: áreas de datos
  Ar_todo   : Ar todo                                    -- U ∈ Á
  Ar_cadena : ∀ a b, Ar a → Ar b → Sub a b ∨ Sub b a    -- (Á, ⊆) es cadena
  Ad        : U → Prop                                   -- área adoptada
  Ad_mem    : Ar Ad
  K         : U → Bool                                   -- K : U → {Sí, No}
  G         : U → Prop                                   -- datos reunidos (en mano)

/-- R1 := K⁻¹(Sí): término derivado, datos que la teología necesita. -/
def E1Base.R1 {U : Type} (b : E1Base U) : U → Prop := fun u => b.K u = true

/-- Lo procurado con un área c: D¹(q) ∩ c ∩ R1 ∩ G. -/
def E1Base.res {U : Type} (b : E1Base U) (c : U → Prop) (q : b.Q1) : U → Prop :=
  fun u => b.D1 (some q) u ∧ c u ∧ b.R1 u ∧ b.G u

/-- Vacío: relevante, en el área y necesario, pero no reunido. -/
def E1Base.falta {U : Type} (b : E1Base U) (c : U → Prop) (q : b.Q1) : U → Prop :=
  fun u => b.D1 (some q) u ∧ c u ∧ b.R1 u ∧ ¬ b.G u

/-- Mp(E1): E1 entra solo con su tipo, E1 q ⊆ R1. -/
structure E1Core (U : Type) extends E1Base U where
  E1      : Q1 → U → Prop
  E1_tipo : ∀ q u, E1 q u → K u = true

/-- Predicado conjuntista Ax_E1: la ley. -/
def E1Core.Ax {U : Type} (y : E1Core U) : Prop :=
  ∀ q u, y.E1 q u ↔ y.toE1Base.res y.Ad q u

/-- ME1 U = M(E1): subtipo de Mp(E1) que cumple la ley. -/
def ME1 (U : Type) : Type 1 := {y : E1Core U // y.Ax}

/-! ## E1 solo -/

theorem res_todo {U : Type} (b : E1Base U) (q : b.Q1) (u : U) :
    b.res todo q u ↔ (b.D1 (some q) u ∧ b.R1 u ∧ b.G u) :=
  ⟨fun ⟨h1, _, h3, h4⟩ => ⟨h1, h3, h4⟩, fun ⟨h1, h3, h4⟩ => ⟨h1, trivial, h3, h4⟩⟩

theorem res_mono {U : Type} (b : E1Base U) (q : b.Q1) {c c' : U → Prop}
    (h : Sub c c') : Sub (b.res c q) (b.res c' q) :=
  fun _ ⟨h1, h2, h3, h4⟩ => ⟨h1, h _ h2, h3, h4⟩

/-- Buena formación: lo procurado cae en R1. -/
theorem res_sub_R1 {U : Type} (b : E1Base U) (c : U → Prop) (q : b.Q1) :
    Sub (b.res c q) b.R1 :=
  fun _ h => h.2.2.1

/-- Con área total se recupera la ley sin áreas. -/
theorem Ax_area_total {U : Type} (y : E1Core U) (ha : y.Ad = todo) :
    y.Ax ↔ ∀ q u, y.E1 q u ↔ (y.D1 (some q) u ∧ y.toE1Base.R1 u ∧ y.G u) := by
  unfold E1Core.Ax
  constructor
  · intro h q u
    have h1 := h q u
    rw [ha] at h1
    exact h1.trans (res_todo y.toE1Base q u)
  · intro h q u
    rw [ha]
    exact (h q u).trans (res_todo y.toE1Base q u).symm

/-- Entre dos áreas del mismo Á, una contiene a la otra y por tanto lo procurado es comparable. -/
theorem E1_comparable {U : Type} (b : E1Base U) (q : b.Q1) (c : U → Prop) (hc : b.Ar c) :
    Sub (b.res b.Ad q) (b.res c q) ∨ Sub (b.res c q) (b.res b.Ad q) := by
  rcases b.Ar_cadena b.Ad c b.Ad_mem hc with h | h
  · exact Or.inl (res_mono b q h)
  · exact Or.inr (res_mono b q h)

/-! ## Vacíos -/

/-- Lo relevante, en el área y necesario se parte en procurado y faltante. -/
theorem needed_partition {U : Type} (b : E1Base U) (q : b.Q1) (c : U → Prop) (u : U) :
    (b.D1 (some q) u ∧ c u ∧ b.R1 u) ↔ (b.res c q u ∨ b.falta c q u) := by
  constructor
  · intro ⟨h1, h2, h3⟩
    by_cases hg : b.G u
    · exact Or.inl ⟨h1, h2, h3, hg⟩
    · exact Or.inr ⟨h1, h2, h3, hg⟩
  · intro h
    rcases h with ⟨h1, h2, h3, _⟩ | ⟨h1, h2, h3, _⟩
    · exact ⟨h1, h2, h3⟩
    · exact ⟨h1, h2, h3⟩

theorem falta_vacio_iff {U : Type} (b : E1Base U) (c : U → Prop) (q : b.Q1) :
    (∀ u, ¬ b.falta c q u) ↔ (∀ u, b.D1 (some q) u → c u → b.R1 u → b.G u) := by
  constructor
  · intro h u h1 h2 h3
    by_cases hg : b.G u
    · exact hg
    · exact absurd ⟨h1, h2, h3, hg⟩ (h u)
  · intro h u ⟨h1, h2, h3, h4⟩
    exact h4 (h u h1 h2 h3)

/-! ## V2′: compatibilidad de las áreas de E1 con D/ de E0 -/

/-- c es unión de bloques de π_n: cerrada bajo la equivalencia de nivel n. -/
def Saturada (x : Mp) (n : Nat) (c : x.U → Prop) : Prop :=
  ∀ u v, (x.dslash.π n).r u v → c u → c v

def Compatible (x : Mp) (y : E1Base x.U) : Prop :=
  ∀ c, y.Ar c → ∃ n, n ≤ x.dslash.N ∧ Saturada x n c

theorem saturada_todo (x : Mp) (n : Nat) : Saturada x n todo :=
  fun _ _ _ _ => trivial

/-- Bloque de π_n alrededor de u0. -/
def area (x : Mp) (u0 : x.U) (n : Nat) : x.U → Prop :=
  fun u => (x.dslash.π n).r u0 u

theorem area_saturada (x : Mp) (u0 : x.U) (n : Nat) : Saturada x n (area x u0 n) :=
  fun u v huv hu => (x.dslash.π n).iseqv.trans hu huv

/-- Si un área es describible en un nivel, lo es en todo nivel más fino. -/
theorem saturada_afina (x : Mp) {n m : Nat} (h : n ≤ m) (hm : m ≤ x.dslash.N)
    (c : x.U → Prop) (hs : Saturada x n c) : Saturada x m c :=
  fun u v huv hu => hs u v (x.dslash.refina_le m n h hm u v huv) hu

/-- V2′ equivale a exigir saturación en el nivel más fino: el "∃ n" es redundante. -/
theorem compatible_iff_fino (x : Mp) (y : E1Base x.U) :
    Compatible x y ↔ ∀ c, y.Ar c → Saturada x x.dslash.N c := by
  constructor
  · intro h c hc
    obtain ⟨n, hn, hs⟩ := h c hc
    exact saturada_afina x hn (Nat.le_refl _) c hs
  · intro h c hc
    exact ⟨x.dslash.N, Nat.le_refl _, h c hc⟩

/-- V2′ generaliza la versión anterior: áreas = U o bloques de D/ cumplen la compatibilidad. -/
theorem compat_de_areas_de_D (x : Mp) (y : E1Base x.U)
    (h : ∀ c, y.Ar c → c = todo ∨ ∃ u0 n, n ≤ x.dslash.N ∧ c = area x u0 n) :
    Compatible x y := by
  intro c hc
  rcases h c hc with rfl | ⟨u0, n, hn, rfl⟩
  · exact ⟨0, Nat.zero_le _, saturada_todo x 0⟩
  · exact ⟨n, hn, area_saturada x u0 n⟩

/-- LÍMITE: si el nivel más fino de D/ es discreto, TODO subconjunto es unión de bloques
    y V2′ no restringe nada. -/
theorem compat_trivial_si_discreta (x : Mp) (y : E1Base x.U)
    (h : ∀ u v, (x.dslash.π x.dslash.N).r u v → u = v) : Compatible x y := by
  intro c _
  refine ⟨x.dslash.N, Nat.le_refl _, ?_⟩
  intro u v huv hu
  have := h u v huv
  subst this
  exact hu

/-- El área adoptada es legible desde E0 (a un nivel). -/
theorem adoptada_legible (x : Mp) (y : E1Base x.U) (h : Compatible x y) :
    ∃ n, n ≤ x.dslash.N ∧ Saturada x n y.Ad :=
  h y.Ad y.Ad_mem

/-- Un vacío invita a recorrer su sector entero: los datos de su mismo bloque están en el área. -/
theorem falta_sector (x : Mp) (y : E1Base x.U) {n : Nat} (hs : Saturada x n y.Ad)
    (q : y.Q1) (u : x.U) (h : y.falta y.Ad q u) :
    ∀ v, (x.dslash.π n).r u v → y.Ad v :=
  fun v hv => hs u v hv h.2.1

/-! ## V3: tipos -/

/-- El vínculo completo: compatibilidad de áreas (V2′) y tipos (V3). V1 va en el tipo. -/
structure Vinculo (x : Mp) (y : E1Base x.U) where
  compat : Compatible x y
  τ      : Option y.Q1 → x.F → Prop
  tip    : ∀ q u, y.D1 q u → τ q (x.k u)
  tau0   : ∀ t, τ none t

theorem res_tipo {x : Mp} {y : E1Base x.U} (v : Vinculo x y) (c : x.U → Prop) (q : y.Q1)
    (u : x.U) (h : y.res c q u) : v.τ (some q) (x.k u) :=
  v.tip (some q) u h.1

theorem falta_tipo {x : Mp} {y : E1Base x.U} (v : Vinculo x y) (c : x.U → Prop) (q : y.Q1)
    (u : x.U) (h : y.falta c q u) : v.τ (some q) (x.k u) :=
  v.tip (some q) u h.1

/-! ## Fase 3: Mpp(E1) — se quita K, el único componente teórico -/

/-- Mpp(E1): Mp(E1) sin K (y sin R1, que se deriva de K). E1 es no teórico: es lo procurado. -/
structure E1Parcial (U : Type) where
  Q1        : Type
  D1        : Option Q1 → U → Prop
  D1_Delta  : ∀ u, D1 none u
  Ar        : (U → Prop) → Prop
  Ar_todo   : Ar todo
  Ar_cadena : ∀ a b, Ar a → Ar b → Sub a b ∨ Sub b a
  Ad        : U → Prop
  Ad_mem    : Ar Ad
  G         : U → Prop
  E1        : Q1 → U → Prop

/-- Un modelo parcial se completa a un modelo de M(E1) si existe un K que cumple la ley. -/
def Extiende {U : Type} (p : E1Parcial U) : Prop :=
  ∃ K : U → Bool, ∀ q u, p.E1 q u ↔ (p.D1 (some q) u ∧ p.Ad u ∧ K u = true ∧ p.G u)

/-- Contenido empírico de la ley: (i) E1(q) ⊆ D¹(q) ∩ Ad ∩ G, y (ii) coherencia entre cuestiones:
    un dato relevante, en el área y reunido para dos cuestiones entra en una si y solo si entra en la otra. -/
theorem extiende_iff {U : Type} (p : E1Parcial U) :
    Extiende p ↔
      (∀ q u, p.E1 q u → (p.D1 (some q) u ∧ p.Ad u ∧ p.G u)) ∧
      (∀ q q' u, (p.D1 (some q) u ∧ p.Ad u ∧ p.G u) →
                 (p.D1 (some q') u ∧ p.Ad u ∧ p.G u) → (p.E1 q u ↔ p.E1 q' u)) := by
  unfold Extiende
  constructor
  · rintro ⟨K, h⟩
    refine ⟨?_, ?_⟩
    · intro q u hu
      have h1 := (h q u).mp hu
      exact ⟨h1.1, h1.2.1, h1.2.2.2⟩
    · intro q q' u hq hq'
      constructor
      · intro h1
        have h1' := (h q u).mp h1
        exact (h q' u).mpr ⟨hq'.1, hq'.2.1, h1'.2.2.1, hq'.2.2⟩
      · intro h1
        have h1' := (h q' u).mp h1
        exact (h q u).mpr ⟨hq.1, hq.2.1, h1'.2.2.1, hq.2.2⟩
  · rintro ⟨h1, h2⟩
    classical
    have hK : ∀ u, (decide (∃ q, p.E1 q u) = true) ↔ ∃ q, p.E1 q u := fun u => by simp
    refine ⟨fun u => decide (∃ q, p.E1 q u), ?_⟩
    intro q u
    constructor
    · intro hE
      exact ⟨(h1 q u hE).1, (h1 q u hE).2.1, (hK u).mpr ⟨q, hE⟩, (h1 q u hE).2.2⟩
    · rintro ⟨hd, ha, hk, hg⟩
      obtain ⟨q', hq'⟩ := (hK u).mp hk
      exact (h2 q q' u ⟨hd, ha, hg⟩ (h1 q' u hq')).mpr hq'

/-- La reducción de un modelo de Mp(E1) a su parte no teórica. -/
def E1Core.parcial {U : Type} (y : E1Core U) : E1Parcial U where
  Q1 := y.Q1
  D1 := y.D1
  D1_Delta := y.D1_Delta
  Ar := y.Ar
  Ar_todo := y.Ar_todo
  Ar_cadena := y.Ar_cadena
  Ad := y.Ad
  Ad_mem := y.Ad_mem
  G := y.G
  E1 := y.E1

/-- Todo modelo de M(E1) tiene una reducción que se completa (con su propio K). -/
theorem parcial_extiende {U : Type} (y : E1Core U) (h : y.Ax) : Extiende y.parcial :=
  ⟨y.K, fun q u => h q u⟩

/-! # Pruebas: modelo concreto sobre E0.Modelo (D/ no discreta), ley, vínculo y fase 3 -/

namespace Pruebas
open E0.Modelo

/-! # V2′ sobre un modelo cuyo nivel más fino NO es discreto -/

/-- Subespecies: ciudades, manuscritos, ediciones, compilaciones. -/
def sp : U2 → Nat
  | .esmirna => 0 | .pergamo => 0
  | .fuenteQ => 1 | .cartasPablo => 1
  | .edicionQ => 2 | .compendio => 3

/-- D/: π₀ = géneros (como antes), π₁ = subespecies (bloques de varios datos). -/
def cadena4 : E0.Cadena U2 where
  N := 1
  π := fun n => match n with | 0 => ker gD | _ => ker sp
  refina := by
    intro n hn a b h
    have : n = 0 := by omega
    subst this
    have h' : sp a = sp b := h
    cases a <;> cases b <;> first | rfl | exact absurd h' (by decide)

theorem cadena4_estricta : Estricta cadena4 := by
  intro n hn
  have hn1 : n < 1 := hn
  have : n = 0 := by omega
  subst this
  refine ⟨.fuenteQ, .edicionQ, rfl, ?_⟩
  intro h
  have h' : sp U2.fuenteQ = sp U2.edicionQ := h
  exact absurd h' (by decide)

noncomputable def mAmp4 : Mp :=
  { mAmp with
    dslash := cadena4
    gen_ker := fun _ _ => Iff.rfl
    estricta := cadena4_estricta }

/-! ## Datos de E1 sobre ese modelo -/

/-- Una sola cuestión (la de los manuscritos); Δ es `none : Option QD`. -/
inductive QD | qM
  deriving DecidableEq

/-- D¹ sobre Q1⁺: Δ no restringe; qM es relevante para Fuente Q, Cartas y la Edición. -/
def D1m : Option QD → U2 → Prop
  | none, _ => True
  | some QD.qM, U2.fuenteQ => True
  | some QD.qM, U2.cartasPablo => True
  | some QD.qM, U2.edicionQ => True
  | some QD.qM, _ => False

/-- K : U → {Sí, No}: lo que la teología necesita. -/
def Knec : U2 → Bool
  | U2.fuenteQ => true
  | U2.cartasPablo => true
  | U2.edicionQ => true
  | U2.esmirna => true
  | _ => false

/-- G: lo que está reunido. Las Cartas de Pablo son necesarias pero no están reunidas. -/
def Greu : U2 → Prop
  | U2.fuenteQ => True
  | U2.edicionQ => True
  | U2.esmirna => True
  | _ => False

def tau : Option QD → F2 → Prop
  | none, _ => True
  | some QD.qM, F2.manuscrito => True
  | some QD.qM, F2.edicion => True
  | some QD.qM, _ => False

/-- Áreas: todo U; el género "textos" {Fuente Q, Cartas, Edición}; la subespecie "manuscritos". -/
def aTodo : U2 → Prop := todo
def aTextos : U2 → Prop := fun u => gD u = GD.textos
def aMan : U2 → Prop := fun u => sp u = 1
/-- Un área "suelta": solo la Fuente Q. No es unión de bloques de ningún nivel. -/
def aSolo : U2 → Prop := fun u => u = U2.fuenteQ

theorem man_textos : Sub aMan aTextos := by
  intro u h
  have h' : sp u = 1 := h
  cases u <;> first | rfl | exact absurd h' (by decide)

theorem textos_todo : Sub aTextos aTodo := fun _ _ => trivial
theorem man_todo : Sub aMan aTodo := fun _ _ => trivial

theorem solo_man : Sub aSolo aMan := by
  intro u h
  have h' : u = U2.fuenteQ := h
  subst h'
  rfl

theorem solo_textos : Sub aSolo aTextos := fun u h => man_textos u (solo_man u h)
theorem solo_todo : Sub aSolo aTodo := fun _ _ => trivial

/-- Base de E1 con áreas compatibles con D/. -/
def baseOk : E1Base U2 where
  Q1 := QD
  D1 := D1m
  D1_Delta := fun _ => trivial
  Ar := fun b => b = aTodo ∨ b = aTextos ∨ b = aMan
  Ar_todo := Or.inl rfl
  Ar_cadena := by
    intro a b ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first
      | exact Or.inl (fun _ h => h)
      | exact Or.inl man_textos | exact Or.inl textos_todo | exact Or.inl man_todo
      | exact Or.inr man_textos | exact Or.inr textos_todo | exact Or.inr man_todo
  Ad := aTextos
  Ad_mem := Or.inr (Or.inl rfl)
  K := Knec
  G := Greu

/-- Base de E1 con un área suelta {Fuente Q}: es cadena por inclusión, pero no legible desde D/. -/
def baseBad : E1Base U2 where
  Q1 := QD
  D1 := D1m
  D1_Delta := fun _ => trivial
  Ar := fun b => b = aTodo ∨ b = aTextos ∨ b = aSolo
  Ar_todo := Or.inl rfl
  Ar_cadena := by
    intro a b ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      first
      | exact Or.inl (fun _ h => h)
      | exact Or.inl solo_textos | exact Or.inl textos_todo | exact Or.inl solo_todo
      | exact Or.inr solo_textos | exact Or.inr textos_todo | exact Or.inr solo_todo
  Ad := aTextos
  Ad_mem := Or.inr (Or.inl rfl)
  K := Knec
  G := Greu

/-! ## Mp frente a M: la ley es sustantiva -/

/-- Un modelo de M(E1): E1 se toma exactamente como lo manda la ley. -/
def y4ok : E1Core U2 where
  toE1Base := baseOk
  E1 := fun q u => baseOk.res baseOk.Ad q u
  E1_tipo := fun _ _ h => h.2.2.1

theorem y4ok_Ax : y4ok.Ax := fun _ _ => Iff.rfl

/-- Un elemento de Mp(E1) con E1 vacío: bien tipado, pero NO cumple la ley. -/
def y4vacio : E1Core U2 where
  toE1Base := baseOk
  E1 := fun _ _ => False
  E1_tipo := fun _ _ h => h.elim

theorem y4vacio_no_Ax : ¬ y4vacio.Ax := by
  intro h
  exact (h QD.qM U2.fuenteQ).mpr ⟨trivial, rfl, rfl, trivial⟩

/-- Mp(E1) ⊋ M(E1): hay un elemento de M y otro de Mp fuera de M. -/
def y4ok_en_M : ME1 U2 := ⟨y4ok, y4ok_Ax⟩

/-! ## Pruebas de la ley -/

theorem fuenteQ_entra : y4ok.E1 QD.qM U2.fuenteQ := ⟨trivial, rfl, rfl, trivial⟩
theorem edicionQ_entra : y4ok.E1 QD.qM U2.edicionQ := ⟨trivial, rfl, rfl, trivial⟩

/-- Las Cartas de Pablo son necesarias y relevantes, pero no están reunidas: un vacío. -/
theorem cartas_faltan : baseOk.falta baseOk.Ad QD.qM U2.cartasPablo :=
  ⟨trivial, rfl, rfl, fun h => h⟩

/-- Lo necesario, relevante y en el área se parte en procurado y faltante. -/
theorem edicion_particion :
    baseOk.res baseOk.Ad QD.qM U2.edicionQ ∨ baseOk.falta baseOk.Ad QD.qM U2.edicionQ :=
  (needed_partition baseOk QD.qM baseOk.Ad U2.edicionQ).mp ⟨trivial, rfl, rfl⟩

/-- K filtra: si la Edición no fuera necesaria, dejaría de entrar aunque esté reunida. -/
def KnecSinEd : U2 → Bool
  | U2.edicionQ => false
  | v => Knec v

def baseNoEd : E1Base U2 := { baseOk with K := KnecSinEd }

theorem edicion_ya_no_entra : ¬ baseNoEd.res baseNoEd.Ad QD.qM U2.edicionQ := by
  intro h
  have h' : (false : Bool) = true := h.2.2.1
  cases h'

theorem fuente_sigue_entrando : baseNoEd.res baseNoEd.Ad QD.qM U2.fuenteQ :=
  ⟨trivial, rfl, rfl, trivial⟩

/-! ## Pruebas de V2′ -/

theorem ok_compatible : Compatible mAmp4 baseOk := by
  intro b hb
  rcases hb with rfl | rfl | rfl
  · exact ⟨0, Nat.zero_le _, saturada_todo mAmp4 0⟩
  · refine ⟨0, Nat.zero_le _, ?_⟩
    intro u v huv hu
    have h' : gD u = gD v := huv
    have hu' : gD u = GD.textos := hu
    exact (h'.symm.trans hu' : gD v = GD.textos)
  · refine ⟨1, by decide, ?_⟩
    intro u v huv hu
    have h' : sp u = sp v := huv
    have hu' : sp u = 1 := hu
    exact (h'.symm.trans hu' : sp v = 1)

/-- Con D/ no discreta, V2′ RECHAZA el área suelta. -/
theorem bad_incompatible : ¬ Compatible mAmp4 baseBad := by
  intro h
  obtain ⟨n, hn, hs⟩ := h aSolo (Or.inr (Or.inr rfl))
  have hn1 : n ≤ 1 := hn
  have e : n = 0 ∨ n = 1 := by omega
  rcases e with rfl | rfl
  · have := hs U2.fuenteQ U2.cartasPablo (by exact rfl) rfl
    have h' : U2.cartasPablo = U2.fuenteQ := this
    cases h'
  · have := hs U2.fuenteQ U2.cartasPablo (by exact rfl) rfl
    have h' : U2.cartasPablo = U2.fuenteQ := this
    cases h'

/-- LÍMITE: con la D/ discreta de mAmp, la misma familia de áreas SÍ pasa. -/
theorem bad_compatible_con_discreta : Compatible mAmp baseBad :=
  compat_trivial_si_discreta mAmp baseBad (fun _ _ h => h)

/-- El vínculo completo (V2′ + V3) sobre el modelo con áreas compatibles. -/
def v4 : Vinculo mAmp4 baseOk where
  compat := ok_compatible
  τ := tau
  tip := by
    intro q u h
    rcases q with _ | q
    · exact trivial
    · cases q
      cases u <;> first | exact trivial | exact False.elim h
  tau0 := fun _ => trivial

theorem sector_de_cartas :
    ∀ v, (mAmp4.dslash.π 1).r U2.cartasPablo v → baseOk.Ad v :=
  falta_sector mAmp4 baseOk (n := 1)
    (fun u v huv hu => by
      have h' : sp u = sp v := huv
      have hu' : gD u = GD.textos := hu
      cases u <;> cases v <;> first | exact rfl | exact absurd h' (by decide) | exact absurd hu' (by decide))
    QD.qM U2.cartasPablo cartas_faltan

/-- Cualquier otra área de la cadena da resultados comparables con la adoptada. -/
theorem comparables :
    Sub (baseOk.res baseOk.Ad QD.qM) (baseOk.res aMan QD.qM) ∨
    Sub (baseOk.res aMan QD.qM) (baseOk.res baseOk.Ad QD.qM) :=
  E1_comparable baseOk QD.qM aMan (Or.inr (Or.inr rfl))

/-! ## Fase 3: la condición de coherencia entre cuestiones es una restricción real -/

/-- Dos cuestiones; todo es relevante, reunido y en el área; el dato `true` entra para la
    cuestión `true` pero no para la cuestión `false`: viola la coherencia. -/
def pBad : E1Parcial Bool where
  Q1 := Bool
  D1 := fun _ _ => True
  D1_Delta := fun _ => trivial
  Ar := fun c => c = todo
  Ar_todo := rfl
  Ar_cadena := by
    intro a b ha hb
    subst ha
    subst hb
    exact Or.inl (fun _ h => h)
  Ad := todo
  Ad_mem := rfl
  G := fun _ => True
  E1 := fun q u => q = u

theorem pBad_no_extiende : ¬ Extiende pBad := by
  intro h
  have h2 := ((extiende_iff pBad).mp h).2
  have h3 := h2 true false true ⟨trivial, trivial, trivial⟩ ⟨trivial, trivial, trivial⟩
  have h4 : (false : Bool) = true := h3.mp (rfl : (true : Bool) = true)
  cases h4

/-- Mismo universo, pero el dato `true` entra para ambas cuestiones: coherente. -/
def pOk : E1Parcial Bool where
  Q1 := Bool
  D1 := fun _ _ => True
  D1_Delta := fun _ => trivial
  Ar := fun c => c = todo
  Ar_todo := rfl
  Ar_cadena := by
    intro a b ha hb
    subst ha
    subst hb
    exact Or.inl (fun _ h => h)
  Ad := todo
  Ad_mem := rfl
  G := fun _ => True
  E1 := fun _ u => u = true

theorem pOk_extiende : Extiende pOk :=
  (extiende_iff pOk).mpr ⟨fun _ _ _ => ⟨trivial, trivial, trivial⟩, fun _ _ _ _ _ => Iff.rfl⟩

#print axioms y4ok_Ax
#print axioms y4vacio_no_Ax
#print axioms edicion_ya_no_entra
#print axioms ok_compatible
#print axioms bad_incompatible
#print axioms bad_compatible_con_discreta
#print axioms sector_de_cartas
#print axioms comparables
#print axioms E1.compatible_iff_fino
#print axioms E1.compat_trivial_si_discreta
#print axioms E1.needed_partition
#print axioms pBad_no_extiende
#print axioms pOk_extiende
#print axioms E1.extiende_iff
#print axioms E1.parcial_extiende

end Pruebas

end E1
