import Ciclo
import E3Nicea
/-
  CicloNicea · el caso Nicea–Constantinopla III cruzando E3→E8 sobre `Items` — Lean 4 (sin Mathlib, sin sorry).

  Rebase del E4 de Nicea (decisión del usuario, punto 2): los ítems de la dialéctica ya no son `Fin 4`
  sino `Items M3 M3.xM = Mcr ⊕ R3E ⊕ R2`, tomados de un modelo de E3 (que trae su E2: `M3.xM`).
  - E3 del caso: `E3.NiceaE3` (archivo E3Nicea.lean), modelo ESQUEMÁTICO con la forma de `E3.B` (tres
    movimientos cristianos, tres narraciones canónicas, una interpretación) y dos narraciones canónicas
    incompatibles (`Inc r2 r3`), de modo que `IncEnDsc` tiene contenido. El contenido histórico real queda
    pendiente (pestaña de E3); basta cambiar `N3` más abajo.
  - E4: mismos 4 puntos de vista y la misma relación que `E6.NiceaE4`; los ítems de los puntos de vista
    p₀,p₁,p₂ son los tres movimientos de E3 y el de p₃ (tesis contraria) es la interpretación de E2.
    Las narraciones (R3E) son ítems secundarios sin punto de vista propio. Dsc: las discrepancias de
    `niceaDsc` entre ítems más las narraciones incompatibles de E3 (`Inc`): así vale `IncEnDsc`.
  - E5–E8: las secciones Nicea de E6, E7, E8 copiadas con renombre mecánico (NiceaE4→NM, …, NiceaW→NW)
    y re-elaboradas sobre el nuevo E4; las pruebas son las mismas (`decide`).
-/
set_option maxRecDepth 8192

namespace Ciclo
namespace N

/-- E3 del caso (ver cabecera). -/
abbrev N3 : E3.Mp := E3.NiceaE3

abbrev It := Items N3 N3.xM

/-- Punto de vista (p₀..p₃) al que pertenece un ítem, si tiene alguno. -/
def pvOf : It → Option (Fin 4)
  | Sum.inl m => some m.val
  | Sum.inr (Sum.inl _) => none
  | Sum.inr (Sum.inr _) => some 3

/-- Un ítem representante de cada punto de vista. -/
def itm (a : Fin 4) : It :=
  if h : a.val < 3 then injMcr (M3 := N3) (x := N3.xM) ⟨a, h⟩
  else injR2 (M3 := N3) (x := N3.xM) ⟨(), ⟨0, rfl⟩⟩

theorem pvOf_itm : ∀ a : Fin 4, pvOf (itm a) = some a := by decide

/-- Discrepancias: las de `niceaDsc` entre ítems con punto de vista, y las narraciones incompatibles de E3. -/
def DscN : It → It → Prop := fun i j =>
  (∃ a b : Fin 4, pvOf i = some a ∧ pvOf j = some b ∧ E4.inT E6.niceaDsc a.val b.val = true) ∨
  (∃ n n' : E4.R3E N3, i = injR3 n ∧ j = injR3 n' ∧ N3.Inc n.val n'.val)

abbrev NM : E4.Mp (Fin 4) It where
  CT := Bool
  Ep := Bool
  Mf := Bool
  Et := Bool
  Vr := Bool
  car := fun p => ((true, true, true), decide (p.val < 3), decide (p.val < 3))
  cvi := fun x => decide (x = (true, true, true))
  cvm := fun b => b
  cvr := fun b => b
  sgE := fun c e => c = e
  sgM := fun x m => x.1 = m
  Odl3 := fun p => p.val < 4
  rel := fun a b => E4.mkRel E6.niceaRel a.val b.val
  Dsc := DscN
  Afn := fun _ _ => False
  Rz := Fin 1
  red := fun _ _ => 0
  cls := fun _ o => o = E4.Op.horizonte
  ot := fun _ _ o => o = E4.Op.horizonte
  V := fun i p => pvOf i = some p
  Va := Fin 1
  vl4 := fun _ _ => False
  sgV := fun _ => true
  Yo := Fin 1
  sost := fun _ p => p.val = 0
  df := fun _ _ => False
  Base := Fin 2
  π := fun p => if p.val < 3 then 0 else 1
  dsc_afn_disj := fun _ _ h => h.2
  cls_ne := fun _ => ⟨E4.Op.horizonte, rfl⟩

theorem NM_ley : E4.Ley NM where
  L1 := by decide
  L2 := by
    have key : ∀ a b : Fin 4, (E4.mkRel E6.niceaRel a.val b.val).isSome →
        E4.inT E6.niceaDsc a.val b.val = true ∨ E4.inT E6.niceaDsc b.val a.val = true := by decide
    intro a b h
    refine ⟨a.isLt, b.isLt, itm a, itm b, ?_, pvOf_itm a, pvOf_itm b⟩
    rcases key a b h with h1 | h1
    · exact Or.inl ⟨Or.inl (Or.inl ⟨a, b, pvOf_itm a, pvOf_itm b, h1⟩), rfl⟩
    · exact Or.inr ⟨Or.inl (Or.inl ⟨b, a, pvOf_itm b, pvOf_itm a, h1⟩), rfl⟩
  L3a := by decide
  L3b := by
    intro a b ha hb
    constructor
    · intro h
      have key : ∀ a b : Fin 4, NM.Odl3 a → NM.Odl3 b → NM.π a = NM.π b →
          b ∈ E4.reach NM a 4 := by decide
      exact E4.reach_sound NM a ha 4 b (key a b ha hb h)
    · exact E4.EqC_pi NM (by decide)
  L6a := by decide
  L6b := by decide
  L6c := E4.TG.irrefl_of_rank _ (fun x => x.val) (by decide)
  L7 := by
    have key : ∀ a b : Fin 4, (NM.rel a b).isSome → NM.rel a b ≠ some E4.Rel.irreductible →
        NM.Pc a = NM.Pc b := by decide
    intro a b r hr hne
    have hs : (NM.rel a b).isSome = true := by rw [hr]; rfl
    exact key a b hs (by rw [hr]; intro h; exact hne (Option.some.inj h))
  L9 := fun _ _ _ => Iff.rfl
  L10 := by decide

/-- La condición de enlace E3→E4: toda incompatibilidad de E3 entre narraciones es discrepancia de E4. -/
theorem NM_enlace : IncEnDsc N3 N3.xM NM :=
  fun n n' h => Or.inr ⟨n, n', rfl, rfl, h⟩

section PX
open E5
abbrev NX : E5.Mp NM where
  Cv := Fin 1
  Om := Fin 3
  CatG := Fin 1
  CatS := Fin 1
  Orig := Unit
  Gen := Unit
  Act := Unit
  Trf := Unit
  Ada := Unit
  k5 := fun _ => E5.Esc.personal
  pm := fun _ => (true, false, false)
  pp := fun _ => (true, true, true)
  tr := fun _ => none
  cv := fun _ => none
  hzm := fun _ => 0
  hzp := fun _ => 2
  pf := fun w => if w.val = 0 then (true, false, false) else (true, true, true)
  ex := fun _ w => w.val = 2
  Aut := fun w => w.val ≠ 0
  rep := fun w => if w.val = 0 then none else some 0
  Df := fun w x => (w.val = 0 ∧ x = Cs5.teo) ∨ (w.val = 2 ∧ (x = Cs5.teo ∨ x = Cs5.int))
  deg := fun w x =>
    if (w.val = 0 ∧ x = Cs5.teo) ∨ (w.val = 2 ∧ (x = Cs5.teo ∨ x = Cs5.int))
    then some E5.Gr5.madura else none
  gs := fun _ => 3
  Tm := fun _ => ((), (), (), (), ())
  Df_sc := by decide
  deg_def := by
    intro w x
    cases x <;> revert w <;> decide

theorem NX_ley : E5.Ley NX where
  D1 := by decide
  D2 := by intro c b b' h; simp at h
  D3 := by intro y c h; simp at h
  C1 := by decide
  C2 := by decide
  C3 := by intro w a _; rfl
  C4a := by decide
  C4b := ⟨0, by decide⟩


end PX

section PY
open E4 (Perfil)
open E5 (Cs5)
open E6
/-- E6 del caso. -/
abbrev NY : E6.Mp NX where
  Dc := Fin 9
  Au := Cl
  Nt := Fin 3
  Ctx := Fin 8
  Fo := Fin 9
  Sg := Fin 12
  cl := fun d =>
    if d.val = 0 then Cl.rel else if d.val ≤ 5 then Cl.ig else Cl.te
  au0 := fun c => c
  fn := fun d x => (d.val ≤ 5 ∧ x ≠ Fn.nor) ∨ ((d.val = 6 ∨ d.val = 7) ∧ (x = Fn.cog ∨ x = Fn.nor))
  trt := fun d t => (d.val = 0 ∧ t = Tr.lt) ∨ (d.val ≠ 0 ∧ t = Tr.ld)
  nt := fun d =>
    if d.val = 0 then none else if d.val ≤ 5 then some 2 else if d.val ≤ 7 then some 1 else some 0
  ltNt := fun a b => a.val < b.val
  Dep := fun d d' => (d.val = 6 ∧ d'.val = 4) ∨ (d.val = 7 ∧ d'.val = 4) ∨ (d.val = 8 ∧ d'.val = 1)
  tc := fun _ => Kc.evo
  en := fun d c => (d.val = 0 ∧ c.val = 0) ∨ (d.val = 1 ∧ (c.val = 1 ∨ c.val = 5)) ∨
    (d.val = 2 ∧ c.val = 2) ∨ (d.val = 3 ∧ c.val = 3) ∨
    (d.val = 4 ∧ (c.val = 4 ∨ c.val = 6 ∨ c.val = 7)) ∨ (d.val = 5 ∧ c.val = 5) ∨
    (d.val = 6 ∧ c.val = 6) ∨ (d.val = 7 ∧ c.val = 7) ∨ (d.val = 8 ∧ c.val = 1)
  sg := fun d c =>
    if d.val = 0 ∧ c.val = 0 then some 0
    else if d.val = 1 ∧ c.val = 1 then some 1
    else if d.val = 1 ∧ c.val = 5 then some 2
    else if d.val = 2 ∧ c.val = 2 then some 3
    else if d.val = 3 ∧ c.val = 3 then some 4
    else if d.val = 4 ∧ c.val = 4 then some 5
    else if d.val = 4 ∧ c.val = 6 then some 6
    else if d.val = 4 ∧ c.val = 7 then some 7
    else if d.val = 5 ∧ c.val = 5 then some 8
    else if d.val = 6 ∧ c.val = 6 then some 9
    else if d.val = 7 ∧ c.val = 7 then some 10
    else if d.val = 8 ∧ c.val = 1 then some 11
    else none
  fo := fun d => d
  cd := fun d =>
    if d.val = 0 then 0 else if h : d.val ≤ 5 then ⟨d.val, by omega⟩
    else if d.val = 6 then 6 else if d.val = 7 then 7 else 1
  ant := fun a b => (1 ≤ a.val ∧ a.val < b.val ∧ b.val ≤ 5) ∨
    (1 ≤ a.val ∧ a.val ≤ 4 ∧ (b.val = 6 ∨ b.val = 7)) ∨ (a.val = 6 ∧ b.val = 7)
  Dv := fun a b => (a.val = 0 ∧ b.val = 1) ∨ (a.val = 4 ∧ b.val = 6)
  It := fun _ _ => False
  sle := fun a b => a = b ∨ (a.val = 1 ∧ b.val = 2) ∨ (a.val = 5 ∧ b.val = 6) ∨
    (a.val = 6 ∧ b.val = 7) ∨ (a.val = 5 ∧ b.val = 7)
  Dsr := fun d d' => (d.val, d'.val) ∈ [(0,1),(1,2),(2,3),(3,4),(4,5),(4,6),(6,7)]
  mdd := fun d d' =>
    if d.val = 0 ∧ d'.val = 1 then some Md.dia
    else if d.val = 1 ∧ d'.val = 2 then some Md.nt
    else if d.val = 2 ∧ d'.val = 3 then some Md.nt
    else if d.val = 3 ∧ d'.val = 4 then some Md.uso
    else if d.val = 4 ∧ d'.val = 5 then some Md.uso
    else if d.val = 4 ∧ d'.val = 6 then some Md.tsi
    else if d.val = 6 ∧ d'.val = 7 then some Md.tsi
    else none
  hz := fun d => if d.val = 0 then some 1 else if d.val = 8 then some 0 else some 2
  Ctp := fun d d' => d.val = 8 ∧ d'.val = 1
  rq := fun c x => 4 ≤ c.val ∧ x = Cs5.teo
  nu := fun d p => (d.val = 6 ∧ p.val = 1) ∨ (d.val = 7 ∧ p.val = 2) ∨ (d.val = 8 ∧ p.val = 3)
  Ap := fun w d => w.val ≠ 0 ∧ d.val ≤ 5
  Apn := fun _ d => d.val ≤ 5
  st := fun _ _ => Es.mod
  trt_ne := fun d => by
    by_cases h : d.val = 0
    · exact ⟨Tr.lt, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨Tr.ld, Or.inr ⟨h, rfl⟩⟩
  sg_def := by decide
  mdd_def := by decide
  nt_def := by decide
  cadena_Nt := by unfold IsChain; refine ⟨?_, ?_, ?_⟩ <;> decide


set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 8192

/-! Instancias de decidibilidad sobre los tipos proyectados (se reducen a `Fin n`). -/
instance (p : NY.Dc → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 9, p x))
instance (p : NY.Dc → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 9, p x))
instance (p : NY.Ctx → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 8, p x))
instance (p : NY.Ctx → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 8, p x))
instance (p : NY.Sg → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 12, p x))
instance (p : NX.Om → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NX.Om → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NY.Sg) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 12) = b))
instance (a b : NY.Ctx) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 8) = b))
instance (a b : NY.Dc) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 9) = b))


theorem NY_ley : E6.Ley NY where
  L1 := fun a b h => h
  L2 := ⟨by decide, by decide⟩
  L3 := by decide
  L4 := by decide
  L5 := by decide
  L6 := by decide
  L7 := by decide
  L8 := by decide
  L9 := by decide
  L10 := by decide
  L11 := by decide
  L12 := by decide
  L13 := by decide
  L14 := by decide

end PY

section PZ
open E4 (Perfil)
open E5 (Cs5)
open E7
abbrev NZ : E7.Mp NY where
  Sy := Fin 3
  Cq := Fin 3
  Rs := Fin 4
  Gc := Fin 3
  Epc := Fin 1
  Dsp := Fin 2
  Cn := Fin 2
  Rl := Fin 1
  Rsp := Fin 2
  Sb := Fin 1
  Sig := Fin 1
  Ejm := Fin 1
  Ct := Fin 3
  cz := fun _ => 2
  leC := fun a b => a.val ≤ b.val
  pb := 1
  mx := fun d m => (d.val = 4 ∧ (m = Mx.vag ∨ m = Mx.inc)) ∨ (d.val = 1 ∧ m = Mx.vag)
  qs := fun d q => (d.val = 4 ∧ q.val ≤ 1) ∨ (d.val = 1 ∧ q.val = 2)
  nuq := fun q => if q.val = 1 then Mx.inc else Mx.vag
  Ca := fun d d' => d.val = 4 ∧ d'.val = 4
  Dcs := fun s d => (s.val ≤ 1 ∧ d.val = 4) ∨ (s.val = 2 ∧ d.val = 1)
  Cqs := fun s q => (s.val ≤ 1 ∧ q.val ≤ 1) ∨ (s.val = 2 ∧ q.val = 2)
  Rsps := fun s _ => s.val ≤ 1
  Cns := fun s _ => s.val ≤ 1
  Rls := fun _ _ => False
  hzs := fun s => if s.val = 2 then (0 : Fin 3) else (2 : Fin 3)
  eps := fun _ => 0
  cts := fun _ x => x.val = 0
  evo := fun _ => False
  cxs := fun s => if s.val = 0 then (6 : Fin 8) else if s.val = 1 then (7 : Fin 8) else (1 : Fin 8)
  pmS := fun s => if s.val = 2 then Pm.prueba else Pm.conv
  vnS := fun s v => s.val = 2 ∧ v = Vl.fal
  rm := fun d r => (d.val = 4 ∧ r.val ≤ 2) ∨ (d.val = 1 ∧ r.val = 3)
  El := fun s d d' => s.val ≤ 1 ∧ d.val = 4 ∧ d'.val = 4
  vS := fun s r v => ((s.val ≤ 1 ∧ r.val ≤ 2) ∨ (s.val = 2 ∧ r.val = 3)) ∧ v = Vi.nis
  anS := fun _ _ => none
  nsS := fun s a b => s.val ≤ 1 ∧ ((a.val = 0 ∧ b.val = 1) ∨ (a.val = 1 ∧ b.val = 2))
  nfS := fun _ _ => False
  smS := fun _ _ => 0
  dsS := fun _ _ => 0
  gcS := fun s _ => if s.val = 1 then (1 : Fin 3) else (0 : Fin 3)
  ltG := fun a b => a.val < b.val
  topG := 2
  tq := fun _ => Tq.quid
  mj := fun _ => Mj.razon
  ptc := fun _ => 1
  rc := fun c r => (c.val = 0 ∧ r.val ≤ 1) ∨ (c.val = 1 ∧ r.val = 2)
  Orr := fun c q => c.val = 0 ∧ q.val = 1
  Pre := fun s a b => s.val ≤ 1 ∧ a.val = 0 ∧ b.val = 1
  ltE := fun _ a b => a.val < b.val
  bas := fun _ => Bs.der
  co := fun c => some (if c.val = 0 then Ci.su else Ci.op)
  rco := fun _ => none
  Mtf := fun s _ => s.val ≤ 1
  lm := fun _ => Lm.lit
  dnR := fun _ => Dn.noc
  NomD := fun _ _ => False
  sgN := fun _ => Sgn.prim
  fd := fun _ => none
  Sbs := fun _ _ => False
  desS := fun _ _ => False
  indS := fun _ _ => False
  sigS := fun _ _ => False
  rr := fun e => e
  Req := fun _ _ => False
  Opp := fun s s' => (s.val = 2 ∧ s'.val ≤ 1) ∨ (s.val ≤ 1 ∧ s'.val = 2)
  Irr := fun _ _ => False
  Suc := fun s s' => s.val = 0 ∧ s'.val = 1
  ltEp := fun _ _ => False
  dvt := fun _ _ _ => False
  cadenaG := by unfold E6.IsChain; refine ⟨?_, ?_, ?_⟩ <;> decide
  top_max := by decide
  nu_sub := by decide
  ca_inc := by decide
  dcs_ne := by decide
  opp_symm := by decide
  opp_irrefl := by decide
  irr_opp := by decide
  suc_irrefl := by decide
  suc_trans := by decide
  dvt_suc := fun _ _ _ h => h.elim


set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 8192

/-! Instancias de decidibilidad sobre los tipos proyectados (se reducen a `Fin n`). -/
instance (p : NZ.Sy → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NZ.Sy → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NZ.Sy) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NZ.Cq → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NZ.Cq → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NZ.Cq) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NZ.Rs → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 4, p x))
instance (p : NZ.Rs → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 4, p x))
instance (a b : NZ.Rs) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 4) = b))
instance (p : NZ.Gc → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NZ.Gc → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NZ.Gc) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NZ.Epc → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NZ.Epc → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NZ.Epc) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NZ.Dsp → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NZ.Dsp → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NZ.Dsp) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NZ.Cn → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NZ.Cn → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NZ.Cn) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NZ.Rl → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NZ.Rl → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NZ.Rl) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NZ.Rsp → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NZ.Rsp → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NZ.Rsp) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NZ.Sb → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NZ.Sb → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NZ.Sb) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NZ.Sig → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NZ.Sig → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NZ.Sig) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NZ.Ejm → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NZ.Ejm → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NZ.Ejm) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NZ.Ct → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NZ.Ct → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NZ.Ct) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))

/-! ### Los sistemas del caso son adecuados (s₆, s₇) o no (s_A) -/
theorem nicea_K6 : ∀ s : Fin 3, NZ.K6 s := by
  have key : ∀ (s r r' : Fin 4) (s' : Fin 3), s'.val ≤ 1 → (r.val ≤ 2) → (r'.val ≤ 2) →
      r = r' ∨ NZ.symNs s' r r' ∨ ∃ c, NZ.symNs s' r c ∧ NZ.symNs s' c r' := by
    intro _ r r' s' h1 h2 h3; revert r r'; revert s'; decide
  intro s r r' hr hr'
  have rr : ∀ (s : Fin 3) (r : Fin 4), NZ.Rcub s r → (s.val ≤ 1 ∧ r.val ≤ 2) ∨ (s.val = 2 ∧ r.val = 3) := by
    decide
  rcases rr s r hr with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases rr s r' hr' with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · rcases key 0 r r' s h1 h2 h4 with h | h | ⟨c, hc, hc'⟩
    · exact Or.inl h
    · exact Or.inr (E4.TG.base h)
    · exact Or.inr (E4.TG.step (E4.TG.base hc) hc')
  · omega
  · omega
  · left
    apply Fin.ext; omega

theorem nicea_K1 : ∀ s : Fin 3, s.val ≤ 1 → NZ.K1 s := by decide
theorem nicea_K2 : ∀ s : Fin 3, s.val ≤ 1 → NZ.K2 s := by decide
theorem nicea_K3 : ∀ s : Fin 3, s.val ≤ 1 → NZ.K3 s := by decide
theorem nicea_K4 : ∀ s : Fin 3, s.val ≤ 1 → NZ.K4 s := by decide
theorem nicea_K5 : ∀ s : Fin 3, s.val ≤ 1 → NZ.K5 s := by decide
theorem nicea_K7 : ∀ s : Fin 3, s.val ≤ 1 → NZ.K7 s := by decide
theorem nicea_K8 : ∀ s : Fin 3, s.val ≤ 1 → NZ.K8 s := by decide
theorem nicea_K9 : ∀ s : Fin 3, s.val ≤ 1 → NZ.K9 s := by decide
theorem nicea_K10 : ∀ s : Fin 3, s.val ≤ 1 → NZ.K10 s := by decide
theorem nicea_K11 : ∀ s : Fin 3, s.val ≤ 1 → NZ.K11 s := by decide
theorem nicea_K12 : ∀ s : Fin 3, s.val ≤ 1 → NZ.K12 s := by decide
theorem nicea_K13 : ∀ s : Fin 3, s.val ≤ 1 → NZ.K13 s := by decide

theorem nicea_Adec_01 : ∀ s : Fin 3, s.val ≤ 1 → Adec NZ s := fun s hs =>
  ⟨nicea_K1 s hs, nicea_K2 s hs, nicea_K3 s hs, nicea_K4 s hs, nicea_K5 s hs, nicea_K6 s,
   nicea_K7 s hs, nicea_K8 s hs, nicea_K9 s hs, nicea_K10 s hs, nicea_K11 s hs, nicea_K12 s hs,
   nicea_K13 s hs⟩

/-- s_A no es adecuado: pm = prueba (L13). -/
theorem nicea_sA_no_adec : ¬ Adec NZ 2 := fun h => absurd h.L13 (by decide)

theorem nicea_Posc_01 : ∀ s : Fin 3, s.val ≤ 1 → Posc NZ s := fun s hs =>
  ⟨nicea_Adec_01 s hs, (show ∀ s : Fin 3, s.val ≤ 1 → ∀ d, NZ.Dcs s d → NY.Ap (NZ.hzs s) d by decide) s hs, (show ∀ s : Fin 3, s.val ≤ 1 → ∀ v, ¬ NZ.vnS s v by decide) s hs⟩

/-- s_A es contraposición. -/
theorem nicea_sA_contrap : NZ.Contrap 2 := fun h => nicea_sA_no_adec h.toAdec

/-! ### E7 y su imagen -/
theorem nicea_E7_d4 : ∀ s : Fin 3, NZ.E7 4 s ↔ s.val ≤ 1 := by
  intro s; constructor
  · rintro ⟨hd, hp⟩
    exact (show ∀ s : Fin 3, NZ.Dcs s 4 → s.val ≤ 1 by decide) s hd
  · intro hs; exact ⟨(show ∀ s : Fin 3, s.val ≤ 1 → NZ.Dcs s 4 by decide) s hs, nicea_Posc_01 s hs⟩

theorem nicea_E7_d1 : ∀ s : Fin 3, ¬ NZ.E7 1 s := by
  intro s ⟨hd, hp⟩
  have : s = 2 := (show ∀ s : Fin 3, NZ.Dcs s 1 → s = 2 by decide) s hd
  subst this; exact nicea_sA_contrap hp

/-- E7(d) = ∅ para las doctrinas que ningún sistema posición sostiene (d₆, d₇ son esbozos). -/
theorem nicea_E7_otros : ∀ d : Fin 9, d.val ≠ 4 → ∀ s : Fin 3, ¬ NZ.E7 d s := by
  intro d hd s ⟨hdc, hp⟩
  by_cases h1 : d.val = 1
  · have : d = 1 := Fin.ext h1
    subst this; exact nicea_E7_d1 s ⟨hdc, hp⟩
  · have := (show ∀ d : Fin 9, ∀ s : Fin 3, NZ.Dcs s d → d.val = 4 ∨ d.val = 1 by decide) d s hdc
    omega

/-- Im(E7) = Sis = {s₆, s₇}. -/
theorem nicea_Sis : ∀ s : Fin 3, NZ.Sis s ↔ s.val ≤ 1 := by
  intro s; constructor
  · rintro ⟨d, hd⟩
    by_cases h : d.val = 4
    · have : d = 4 := Fin.ext h
      subst this; exact (nicea_E7_d4 s).1 hd
    · exact absurd hd (nicea_E7_otros d h s)
  · intro hs; exact ⟨4, (nicea_E7_d4 s).2 hs⟩

/-- La ley global L15–L16 se cumple en el caso. -/
theorem nicea_LeyZ : E7.Ley NZ where
  L15a := by decide
  L15b := by
    intro s s' _ _ h; exact h
  L16a := by decide
  L16b := by
    intro s s' h _ _
    have : s = 0 ∧ s' = 1 := (show ∀ s s' : Fin 3, NZ.Suc s s' → s = 0 ∧ s' = 1 by decide) s s' h
    obtain ⟨rfl, rfl⟩ := this
    decide

end PZ

section PW
open E4 (Perfil)
open E5 (Cs5)
open E8
def nCul (a : Fin 6) : Fin 3 := if a.val = 2 ∨ a.val = 4 then 1 else if a.val = 5 then 2 else 0

abbrev NW : E8.Mp NZ where
  Esf := Fin 3
  Cu := Fin 3
  Csc := Fin 1
  Prs := Fin 6
  Ctn := Fin 4
  Cmu := Fin 2
  Ex := Fin 5
  Med := Fin 2
  Lug := Fin 2
  Tmp := Fin 1
  Nuc := fun s d => NZ.Dcs s d
  rI := fun s _ => s.val ≤ 1
  hum := fun e => e.val ≤ 1
  Len := fun e c x =>
    (x.val = 0 ∧ c.val = 0 ∨ x.val = 1 ∧ c.val = 1 ∨ x.val = 2 ∧ c.val = 0 ∨
     x.val = 3 ∧ c.val = 1 ∨ x.val = 4 ∧ c.val = 2) ∧
    ((x.val ≤ 1 ∧ e.val = 2) ∨ (2 ≤ x.val ∧ e.val ≤ 1))
  Pur := fun e => e.val ≤ 1
  Pob := fun c _ a => nCul a = c
  hzA := fun a => if a.val ≤ 2 then (2 : Fin 3) else (0 : Fin 3)
  nvs := fun k => if k.val = 0 ∨ k.val = 3 then Nvs.jui else Nvs.val
  tpc := fun k => if k.val = 0 ∨ k.val = 3 then Tsg.cog else if k.val = 1 then Tsg.con else Tsg.efe
  cnv := fun a k => ((a.val = 0 ∨ a.val = 2) ∧ k.val ≤ 2) ∨ (a.val = 1 ∧ 1 ≤ k.val)
  mb := fun a i => ((a.val = 0 ∨ a.val = 2) ∧ i.val = 0) ∨ (a.val = 1 ∧ i.val = 1)
  Cpl := fun k k' => (k.val = 1 ∧ k'.val = 2) ∨ (k.val = 2 ∧ k'.val = 1)
  Igs := fun _ => True
  Prep := fun x => 2 ≤ x.val
  Ori := fun x s => 2 ≤ x.val ∧ s.val ≤ 1
  iota := fun x d => x.val ≤ 1 ∧ d.val = 4
  ctn := fun x k => (x.val ≤ 1 ∧ k.val ≤ 1) ∨ (2 ≤ x.val ∧ k.val = 2)
  ntg := fun s c _ x => s.val ≤ 1 ∧
    ((c.val = 0 ∧ (x.val = 0 ∨ x.val = 2)) ∨ (c.val = 1 ∧ (x.val = 1 ∨ x.val = 3)) ∨ (c.val = 2 ∧ x.val = 4))
  Acs := fun t x _ _ w => (x.val ≤ 1 ∧ 1 ≤ w.val) ∨ (2 ≤ x.val ∧ t = Tsg.efe)
  Emi := fun x a => (x.val = 0 ∧ a.val = 0) ∨ (x.val = 1 ∧ a.val = 2) ∨ (x.val = 2 ∧ a.val = 0) ∨
    (x.val = 3 ∧ a.val = 2) ∨ (x.val = 4 ∧ a.val = 2)
  kn := fun a s => (a.val = 0 ∨ a.val = 2) ∧ s.val ≤ 1
  prc := fun a k => (a.val = 0 ∨ a.val = 2) ∧ k.val = 2
  culA := nCul
  Cmp := fun a c => (a.val = 0 ∧ c.val = 0) ∨ (a.val = 2 ∧ (c.val = 1 ∨ c.val = 2))
  Ec := fun x j => x.val = 2 ∧ j.val = 1
  Disp := fun g _ m => g.val = m.val
  Adp := fun x m => (x.val ≤ 1 ∧ m.val = 0) ∨ (2 ≤ x.val ∧ m.val = 1)

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 8192

instance (a b : NZ.Sy) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (a b : NX.Om) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NW.Esf → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NW.Esf → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NW.Esf) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NW.Cu → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NW.Cu → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NW.Cu) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NW.Csc → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NW.Csc → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NW.Csc) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NW.Prs → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 6, p x))
instance (p : NW.Prs → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 6, p x))
instance (a b : NW.Prs) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 6) = b))
instance (p : NW.Ctn → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 4, p x))
instance (p : NW.Ctn → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 4, p x))
instance (a b : NW.Ctn) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 4) = b))
instance (p : NW.Cmu → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NW.Cmu → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NW.Cmu) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NW.Ex → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 5, p x))
instance (p : NW.Ex → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 5, p x))
instance (a b : NW.Ex) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 5) = b))
instance (p : NW.Med → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NW.Med → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NW.Med) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NW.Lug → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NW.Lug → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NW.Lug) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NW.Tmp → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NW.Tmp → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NW.Tmp) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))

theorem nicea_Tipo : NW.Tipo := by decide

theorem nicea_LeyW : E8.Ley NW where
  L1 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NW.K1 s by decide) s ((nicea_Sis s).1 hs)
  L2 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NW.K2 s by decide) s ((nicea_Sis s).1 hs)
  L3 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NW.K3 s by decide) s ((nicea_Sis s).1 hs)
  L4 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NW.K4 s by decide) s ((nicea_Sis s).1 hs)
  L5 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NW.K5 s by decide) s ((nicea_Sis s).1 hs)
  L6 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NW.K6 s by decide) s ((nicea_Sis s).1 hs)
  L7 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NW.K7 s by decide) s ((nicea_Sis s).1 hs)
  L8 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NW.K8 s by decide) s ((nicea_Sis s).1 hs)

end PW

/-! ## La cadena E3→E8 como un solo objeto, y no vacuidad con el caso -/

/-- Tupla conjunta de la parte formalizada del ciclo con E3 incluido: el modelo de E3 trae el de E2;
    los ítems de E4 se construyen desde él; E5–E8 van encima. -/
structure Cadena38 where
  M3 : E3.Mp
  L3 : E3.Ley M3
  PV : Type
  M : E4.Mp PV (Items M3 M3.xM)
  LM : E4.Ley M
  enlace : IncEnDsc M3 M3.xM M
  X : E5.Mp M
  LX : E5.Ley X
  Y : E6.Mp X
  LY : E6.Ley Y
  Z : E7.Mp Y
  LZ : E7.Ley Z
  W : E8.Mp Z
  TW : W.Tipo
  LW : E8.Ley W

/-- Olvidar el origen de los ítems: toda `Cadena38` es una `Cadena48`. -/
def Cadena38.toCadena48 (C : Cadena38) : Cadena48 :=
  { PV := C.PV, I := Items C.M3 C.M3.xM, M := C.M, LM := C.LM, X := C.X, LX := C.LX,
    Y := C.Y, LY := C.LY, Z := C.Z, LZ := C.LZ, W := C.W, TW := C.TW, LW := C.LW }

abbrev nicea38 : Cadena38 :=
  { M3 := N3, L3 := E3.NiceaE3_ley, PV := Fin 4, M := NM, LM := NM_ley, enlace := NM_enlace,
    X := NX, LX := NX_ley, Y := NY, LY := NY_ley, Z := NZ, LZ := nicea_LeyZ,
    W := NW, TW := nicea_Tipo, LW := nicea_LeyW }

/-- Un modelo conjunto de E3, E4, E5, E6, E7 y E8 (con el E2 de E3 dentro): la cadena no es vacía
    cruzando E3→E8 con ítems tomados de E3 y E2. -/
theorem Ciclo38_noVacio : Nonempty Cadena38 := ⟨nicea38⟩

/-- Los enlaces hacia adelante E4→E5→E6→E7→E8 valen en esta cadena (instancias de los teoremas generales). -/
theorem nicea38_enlace78 {s : nicea38.Z.Sy} (h : nicea38.Z.Sis s) :
    nicea38.W.Rcp s (nicea38.Z.hzs s) :=
  enlace78 nicea38.toCadena48 h

/-- El enlace E3→E4 tiene contenido en el caso: hay dos narraciones canónicas incompatibles (E3) y E4 las
    registra como discrepancia. -/
theorem nicea_inc_en_dsc :
    ∃ n n' : E4.R3E N3, N3.Inc n.val n'.val ∧ NM.Dsc (injR3 n) (injR3 n') :=
  ⟨⟨1, Or.inr (Or.inl rfl)⟩, ⟨2, Or.inr (Or.inr rfl)⟩, E3.NiceaE3_inc,
   Or.inr ⟨⟨1, Or.inr (Or.inl rfl)⟩, ⟨2, Or.inr (Or.inr rfl)⟩, rfl, rfl, E3.NiceaE3_inc⟩⟩

/-- … y no es consecuencia de la ley de E4: hay un E4 que cumple la ley y no recoge la incompatibilidad. -/
theorem nicea_enlace_independiente :
    ∃ M4 : E4.Mp Unit (Items N3 N3.xM), E4.Ley M4 ∧ ¬ IncEnDsc N3 N3.xM M4 :=
  enlace34_independiente N3 ⟨⟨1, Or.inr (Or.inl rfl)⟩, ⟨2, Or.inr (Or.inr rfl)⟩, E3.NiceaE3_inc⟩

end N
end Ciclo
