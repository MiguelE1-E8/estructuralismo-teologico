/-
  E0 (Investigación general) en Lean 4, sin Mathlib.
  Traduce la sección "Consideraciones desde el estructuralismo formal" del documento E0:
  tupla, Mp(E0) y las dos leyes de fase 2 (coherencia tipológica y composición).
  Convenciones:
   - U = datos particulares; R0 = resultados de E0 (en el documento R1; se renombra para no
     chocar con el R1 de E1, que es lo efectivamente reunido).
   - F = f (tipos de entrada), Fs = f* (tipos de salida), Gn = géneros (la G de E1 son los datos reunidos).
   - Un subconjunto de R0 es un predicado `R0 → Prop`; 𝒫(R0)∖{∅} es `{A : R0 → Prop // ∃ r, A r}`.
   - D⁰ (aquí `D`) es la producción de resultados de E0; D¹ es la relevancia de E1.
   - Dhat es D̂. `dslash` es D/ (cadena finita de particiones de U).
   - ρ ⊆ f × f* es muchos-a-muchos; pte ⊆ f* × f es el puente de composición (hallazgo de Lean; β en el documento, para no chocar con la σ de E2).
-/
namespace E0

/-! ## 1. D/ : cadena finita de particiones anidadas -/

/-- Cadena de longitud `N`; cada nivel n+1 refina el nivel n. -/
structure Cadena (U : Type) where
  N      : Nat
  π      : Nat → Setoid U
  refina : ∀ n, n < N → ∀ a b, (π (n+1)).r a b → (π n).r a b

/-- La condición entre niveles adyacentes implica el refinamiento global. -/
theorem Cadena.refina_le {U : Type} (c : Cadena U) :
    ∀ m n, n ≤ m → m ≤ c.N → ∀ a b, (c.π m).r a b → (c.π n).r a b := by
  intro m
  induction m with
  | zero =>
    intro n hn _ a b h
    have : n = 0 := Nat.le_zero.mp hn
    subst this; exact h
  | succ m ih =>
    intro n hn hm a b h
    rcases Nat.lt_or_ge n (m+1) with hlt | hge
    · have h1 : (c.π m).r a b := c.refina m (by omega) a b h
      exact ih n (by omega) (by omega) a b h1
    · have : n = m+1 := by omega
      subst this; exact h

/-- Estricta: cada subdivisión divide al menos un bloque ("dividiendo y subdividiendo"). -/
def Estricta {U : Type} (c : Cadena U) : Prop :=
  ∀ n, n < c.N → ∃ a b, (c.π n).r a b ∧ ¬ (c.π (n+1)).r a b

/-- El estrechamiento es global: para n < m hay datos que comparten sector en n y no en m. -/
theorem estricta_global {U : Type} (c : Cadena U) (h : Estricta c) :
    ∀ n m, n < m → m ≤ c.N → ∃ a b, (c.π n).r a b ∧ ¬ (c.π m).r a b := by
  intro n m hnm hm
  obtain ⟨a, b, hab, hnab⟩ := h (m-1) (by omega)
  have e : m - 1 + 1 = m := by omega
  rw [e] at hnab
  exact ⟨a, b, c.refina_le (m-1) n (by omega) (by omega) a b hab, hnab⟩

/-! ## 2. Mp(E0) -/

structure Mp where
  U      : Type
  R0     : Type
  F      : Type
  Fs     : Type
  Gn     : Type
  dslash : Cadena U
  gen    : U → Gn
  k      : U → F
  k'     : R0 → Fs
  ρ      : F → Fs → Prop
  pte    : Fs → F → Prop
  D      : U → R0 → Prop
  D_ne   : ∀ u, ∃ r, D u r
  Dhat   : {A : R0 → Prop // ∃ r, A r} → U
  U_ne   : Nonempty U
  R0_ne  : Nonempty R0
  gen_ker  : ∀ a b, (dslash.π 0).r a b ↔ gen a = gen b
  gen_surj : ∀ g, ∃ u, gen u = g
  estricta : Estricta dslash

namespace Mp

/-- Una especie o subespecie nunca cruza dos géneros. -/
theorem especie_en_genero (x : Mp) (m : Nat) (hm : m ≤ x.dslash.N) (a b : x.U)
    (h : (x.dslash.π m).r a b) : x.gen a = x.gen b :=
  (x.gen_ker a b).mp (x.dslash.refina_le m 0 (Nat.zero_le _) hm a b h)

end Mp

/-! ## 3. Leyes de fase 2 -/

/-- Ley 1 (coherencia tipológica): si u es de tipo t, todo r ∈ D(u) es de un tipo s con (t,s) ∈ ρ. -/
def Coherente (x : Mp) : Prop :=
  ∀ u r, x.D u r → x.ρ (x.k u) (x.k' r)

/-- Ley 2 (composición): todo resultado recompuesto es constituyente admisible del dato resultante. -/
def Composicion (x : Mp) : Prop :=
  ∀ (A : {A : x.R0 → Prop // ∃ r, A r}) (r : x.R0), A.1 r →
    x.pte (x.k' r) (x.k (x.Dhat A))

/-- Modelo actual de E0: Mp + las dos leyes. -/
def Actual (x : Mp) : Prop := Coherente x ∧ Composicion x

/-- La relación mínima de tipos que D usa efectivamente. -/
def rhoMin (x : Mp) : x.F → x.Fs → Prop :=
  fun t s => ∃ u r, x.D u r ∧ x.k u = t ∧ x.k' r = s

/-- La Ley 1 dice exactamente que ρ contiene la imagen tipada de D. -/
theorem coherente_iff (x : Mp) :
    Coherente x ↔ ∀ t s, rhoMin x t s → x.ρ t s := by
  constructor
  · intro h t s ⟨u, r, hD, hk, hk'⟩
    subst hk; subst hk'
    exact h u r hD
  · intro h u r hD
    exact h _ _ ⟨u, r, hD, rfl, rfl⟩

/-! ## 4. Hallazgo: con D̂ total, un puente FUNCIONAL θ : f* → f es imposible -/

/-- Variante rechazada: el tipo del dato recompuesto es función del tipo de cada resultado. -/
def TipoRec (x : Mp) (θ : x.Fs → x.F) : Prop :=
  ∀ (A : {A : x.R0 → Prop // ∃ r, A r}) (r : x.R0), A.1 r → x.k (x.Dhat A) = θ (x.k' r)

theorem tiporec_imposible (x : Mp) (θ : x.Fs → x.F) (r1 r2 : x.R0)
    (h : θ (x.k' r1) ≠ θ (x.k' r2)) : ¬ TipoRec x θ := by
  intro hT
  let A : {A : x.R0 → Prop // ∃ r, A r} := ⟨fun r => r = r1 ∨ r = r2, ⟨r1, Or.inl rfl⟩⟩
  have e1 : x.k (x.Dhat A) = θ (x.k' r1) := hT A r1 (Or.inl rfl)
  have e2 : x.k (x.Dhat A) = θ (x.k' r2) := hT A r2 (Or.inr rfl)
  exact h (e1.symm.trans e2)

/-- Variante D̂ parcial: conjuntos θ-homogéneos. Excluye todo conjunto heterogéneo. -/
def Hom {R Fs F : Type} (k' : R → Fs) (θ : Fs → F) (A : R → Prop) : Prop :=
  ∃ r, A r ∧ ∀ r', A r' → θ (k' r') = θ (k' r)

theorem hom_excluye_heterogeneo {R Fs F : Type} (k' : R → Fs) (θ : Fs → F) (r1 r2 : R)
    (h : θ (k' r1) ≠ θ (k' r2)) : ¬ Hom k' θ (fun r => r = r1 ∨ r = r2) := by
  rintro ⟨r, _, hall⟩
  have e1 := hall r1 (Or.inl rfl)
  have e2 := hall r2 (Or.inr rfl)
  exact h (e1.trans e2.symm)

/-! ## 5. Modelo concreto con los ejemplos del documento -/

namespace Modelo

/-- Datos: Esmirna, Pérgamo, Fuente Q, Cartas de Pablo, una edición, un compendio. -/
inductive U2 | esmirna | pergamo | fuenteQ | cartasPablo | edicionQ | compendio
  deriving DecidableEq
inductive R2 | planoAsia | edCritQ | copiaQ | catalogoQ | indiceQ
  deriving DecidableEq
/-- f del documento + EDICIÓN y COMPILACIÓN (tipos de dato que nacen de resultados). -/
inductive F2 | ciudad | inscripcion | escritura | manuscrito | edicion | compilacion
  deriving DecidableEq
/-- f* del documento + CATÁLOGO e ÍNDICE (salidas que Lonergan menciona). -/
inductive S2 | plano | reproduccion | descifram | edicionCritica | catalogo | indice
  deriving DecidableEq
inductive GD | arqueologia | textos | compilaciones
  deriving DecidableEq

def ker {α β : Type} (f : α → β) : Setoid α :=
  ⟨fun a b => f a = f b, ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩⟩

def gD : U2 → GD
  | .esmirna => .arqueologia | .pergamo => .arqueologia
  | .fuenteQ => .textos | .cartasPablo => .textos | .edicionQ => .textos
  | .compendio => .compilaciones

/-- D/: nivel 0 = géneros; nivel 1 = cada dato por separado. -/
def cadena : Cadena U2 where
  N := 1
  π := fun n => match n with | 0 => ker gD | _ => ker id
  refina := by
    intro n hn a b h
    have : n = 0 := by omega
    subst this
    have hab : a = b := h
    subst hab
    rfl

theorem cadena_estricta : Estricta cadena := by
  intro n hn
  have hn1 : n < 1 := hn
  have : n = 0 := by omega
  subst this
  refine ⟨.esmirna, .pergamo, rfl, ?_⟩
  intro h
  have h' : U2.esmirna = U2.pergamo := h
  cases h'

def kU : U2 → F2
  | .esmirna => .ciudad | .pergamo => .ciudad
  | .fuenteQ => .manuscrito | .cartasPablo => .manuscrito
  | .edicionQ => .edicion | .compendio => .compilacion

def kR : R2 → S2
  | .planoAsia => .plano | .edCritQ => .edicionCritica | .copiaQ => .reproduccion
  | .catalogoQ => .catalogo | .indiceQ => .indice

/-- ρ literal del documento (cuatro parejas). -/
def rhoDoc : F2 → S2 → Prop
  | .ciudad, .plano => True
  | .inscripcion, .reproduccion => True
  | .escritura, .descifram => True
  | .manuscrito, .edicionCritica => True
  | _, _ => False

/-- ρ muchos-a-muchos: las cuatro parejas + las que exige la multiplicidad de D. -/
def rho : F2 → S2 → Prop
  | .ciudad, .plano => True
  | .inscripcion, .reproduccion => True
  | .escritura, .descifram => True
  | .manuscrito, .edicionCritica => True
  | .manuscrito, .catalogo => True
  | .manuscrito, .reproduccion => True
  | .manuscrito, .descifram => True
  | .edicion, .catalogo => True
  | .edicion, .indice => True
  | .compilacion, .indice => True
  | .compilacion, .catalogo => True
  | _, _ => False

/-- pte (β en el documento): todo resultado puede constituir una COMPILACIÓN; una edición crítica, también una EDICIÓN. -/
def sigma : S2 → F2 → Prop
  | .edicionCritica, .edicion => True
  | _, .compilacion => True
  | _, _ => False

theorem sigma_comp (s : S2) : sigma s F2.compilacion := by
  cases s <;> exact trivial

def DD : U2 → R2 → Prop
  | .esmirna, .planoAsia => True
  | .pergamo, .planoAsia => True
  | .fuenteQ, .edCritQ => True
  | .fuenteQ, .catalogoQ => True
  | .fuenteQ, .copiaQ => True
  | .cartasPablo, .edCritQ => True
  | .cartasPablo, .catalogoQ => True
  | .edicionQ, .catalogoQ => True
  | .edicionQ, .indiceQ => True
  | .compendio, .indiceQ => True
  | _, _ => False

def DDne : ∀ u, ∃ r, DD u r
  | .esmirna => ⟨.planoAsia, trivial⟩
  | .pergamo => ⟨.planoAsia, trivial⟩
  | .fuenteQ => ⟨.edCritQ, trivial⟩
  | .cartasPablo => ⟨.edCritQ, trivial⟩
  | .edicionQ => ⟨.catalogoQ, trivial⟩
  | .compendio => ⟨.indiceQ, trivial⟩

open Classical in
/-- D̂: solo la edición crítica vuelve como EDICIÓN; cualquier otra reunión, como COMPILACIÓN. -/
noncomputable def DDhat : {A : R2 → Prop // ∃ r, A r} → U2 :=
  fun A => if (∀ r, A.1 r → r = R2.edCritQ) then U2.edicionQ else U2.compendio

noncomputable def mAmp : Mp where
  U := U2
  R0 := R2
  F := F2
  Fs := S2
  Gn := GD
  dslash := cadena
  gen := gD
  k := kU
  k' := kR
  ρ := rho
  pte := sigma
  D := DD
  D_ne := DDne
  Dhat := DDhat
  U_ne := ⟨.esmirna⟩
  R0_ne := ⟨.planoAsia⟩
  gen_ker := fun _ _ => Iff.rfl
  gen_surj := fun g => by
    cases g with
    | arqueologia => exact ⟨.esmirna, rfl⟩
    | textos => exact ⟨.fuenteQ, rfl⟩
    | compilaciones => exact ⟨.compendio, rfl⟩
  estricta := cadena_estricta

/-! ### Pruebas -/

theorem mp_no_vacio : Nonempty Mp := ⟨mAmp⟩

theorem mAmp_coherente : Coherente mAmp := by
  intro u r hD
  cases u <;> cases r <;> first | exact False.elim hD | exact trivial

theorem mAmp_composicion : Composicion mAmp := by
  intro A r hr
  show sigma (kR r) (kU (DDhat A))
  by_cases h : ∀ r, A.1 r → r = R2.edCritQ
  · have e : DDhat A = U2.edicionQ := by unfold DDhat; exact if_pos h
    rw [e]
    have := h r hr
    subst this
    exact trivial
  · have e : DDhat A = U2.compendio := by unfold DDhat; exact if_neg h
    rw [e]
    exact sigma_comp _

theorem mAmp_actual : Actual mAmp := ⟨mAmp_coherente, mAmp_composicion⟩

theorem esmirna_pergamo_mismo_genero : mAmp.gen U2.esmirna = mAmp.gen U2.pergamo := rfl

/-- Hallazgo 1: con la ρ literal de cuatro parejas, la coherencia falla
    (un manuscrito produce también reproducciones). -/
noncomputable def mDoc : Mp := { mAmp with ρ := rhoDoc }

theorem mDoc_incoherente : ¬ Coherente mDoc :=
  fun h => h .fuenteQ .copiaQ trivial

/-- La coherencia es independiente de Mp: hay modelos potenciales que la cumplen y otros que no. -/
theorem coherencia_independiente :
    (∃ x : Mp, Coherente x) ∧ (∃ x : Mp, ¬ Coherente x) :=
  ⟨⟨mAmp, mAmp_coherente⟩, ⟨mDoc, mDoc_incoherente⟩⟩

/-- Lo mismo para la composición. -/
noncomputable def mSinSigma : Mp := { mAmp with Dhat := fun _ => U2.esmirna }

theorem mSinSigma_sin_composicion : ¬ Composicion mSinSigma :=
  fun h => h ⟨fun r => r = R2.edCritQ, ⟨.edCritQ, rfl⟩⟩ .edCritQ rfl

theorem leyes_independientes :
    (∃ x : Mp, Actual x) ∧ (∃ x : Mp, ¬ Coherente x) ∧ (∃ x : Mp, ¬ Composicion x) :=
  ⟨⟨mAmp, mAmp_actual⟩, ⟨mDoc, mDoc_incoherente⟩, ⟨mSinSigma, mSinSigma_sin_composicion⟩⟩

/-- Hallazgo 2: un puente funcional θ es imposible con D̂ total (plano + edición crítica). -/
def theta : S2 → F2
  | .plano => .ciudad | .reproduccion => .inscripcion | .descifram => .escritura
  | .edicionCritica => .edicion | .catalogo => .compilacion | .indice => .compilacion

theorem mAmp_tiporec_imposible : ¬ TipoRec mAmp theta :=
  tiporec_imposible mAmp theta .planoAsia .edCritQ
    (by show theta (kR .planoAsia) ≠ theta (kR .edCritQ); decide)

/-- Con σ relacional, el conjunto heterogéneo (plano + edición crítica) sí se recompone. -/
def Ahet : {A : R2 → Prop // ∃ r, A r} :=
  ⟨fun r => r = R2.planoAsia ∨ r = R2.edCritQ, ⟨.planoAsia, Or.inl rfl⟩⟩

theorem sigma_admite_heterogeneo :
    mAmp.Dhat Ahet = U2.compendio ∧
    (∀ r, Ahet.1 r → mAmp.pte (mAmp.k' r) (mAmp.k (mAmp.Dhat Ahet))) := by
  refine ⟨?_, fun r hr => mAmp_composicion Ahet r hr⟩
  show DDhat Ahet = U2.compendio
  unfold DDhat
  refine if_neg ?_
  intro h
  have := h R2.planoAsia (Or.inl rfl)
  cases this

theorem heterogeneo_fuera_de_Hom :
    ¬ Hom kR theta (fun r => r = R2.planoAsia ∨ r = R2.edCritQ) :=
  hom_excluye_heterogeneo kR theta R2.planoAsia R2.edCritQ (by decide)

/-- La estrictitud es restricción real: una cadena que no subdivide no es D/. -/
def cadenaPlana : Cadena U2 where
  N := 1
  π := fun _ => ker gD
  refina := fun _ _ _ _ h => h

theorem cadenaPlana_no_estricta : ¬ Estricta cadenaPlana := by
  intro h
  obtain ⟨a, b, hab, hn⟩ := h 0 (by decide)
  exact hn hab

theorem mAmp_estrecha :
    ∃ a b, (mAmp.dslash.π 0).r a b ∧ ¬ (mAmp.dslash.π 1).r a b :=
  estricta_global mAmp.dslash mAmp.estricta 0 1 (by decide) (by decide)

end Modelo

end E0
