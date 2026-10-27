import CicloF5a
/-
  CicloF5 · dos giros sobre el caso Nicea: giro 1 (dialéctico: entra una discrepancia, `estNueva`) y
  giro 2 (corrección: reclasificación de p₃ sobre el E4 resultante del giro 1; E6 se reconstruye, E7–E8 se reinstancian).
  Lean 4 (sin Mathlib, sin sorry).
-/
set_option maxRecDepth 8192
namespace Ciclo
namespace N
open E5 (Cs5)
open E6
open E4 (Perfil)

/-- E4 del estado final: el del giro 1 (`estNueva`: `Dsc` más la discrepancia nueva) con p₃ reclasificado como posición. -/
abbrev NM3 : E4.Mp (Fin 4) It :=
  { NM with
    Dsc := fun i j => DscN i j ∨ (i = nar0 ∧ j = itm 3)
    car := fun p => ((true, true, true), decide (p.val < 4), decide (p.val < 4))
    dsc_afn_disj := fun _ _ h => h.2 }

theorem NM3_ley : E4.Ley NM3 where
  L1 := NM2_ley.L1
  L2 := by
    have key : ∀ a b : Fin 4, (E4.mkRel E6.niceaRel a.val b.val).isSome →
        E4.inT E6.niceaDsc a.val b.val = true ∨ E4.inT E6.niceaDsc b.val a.val = true := by decide
    intro a b h
    refine ⟨a.isLt, b.isLt, itm a, itm b, ?_, pvOf_itm a, pvOf_itm b⟩
    rcases key a b h with h1 | h1
    · exact Or.inl ⟨Or.inl (Or.inl (Or.inl ⟨a, b, pvOf_itm a, pvOf_itm b, h1⟩)), rfl⟩
    · exact Or.inr ⟨Or.inl (Or.inl (Or.inl ⟨b, a, pvOf_itm b, pvOf_itm a, h1⟩)), rfl⟩
  L3a := NM2_ley.L3a
  L3b := by
    intro a b ha hb
    constructor
    · intro h
      have key : ∀ a b : Fin 4, NM3.Odl3 a → NM3.Odl3 b → NM3.π a = NM3.π b →
          b ∈ E4.reach NM3 a 4 := by decide
      exact E4.reach_sound NM3 a ha 4 b (key a b ha hb h)
    · exact E4.EqC_pi NM3 (by decide)
  L6a := NM2_ley.L6a
  L6b := NM2_ley.L6b
  L6c := NM2_ley.L6c
  L7 := NM2_ley.L7
  L9 := fun _ _ _ => Iff.rfl
  L10 := NM2_ley.L10

theorem NM3_enlace : IncEnDsc N3 N3.xM NM3 :=
  fun n n' h => Or.inl (Or.inr ⟨n, n', rfl, rfl, h⟩)

abbrev NX3 : E5.Mp NM3 where
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

theorem NX3_ley : E5.Ley NX3 where
  D1 := by decide
  D2 := by intro c b b' h; simp at h
  D3 := by intro y c h; simp at h
  C1 := by decide
  C2 := by decide
  C3 := by intro w a _; rfl
  C4a := by decide
  C4b := ⟨0, by decide⟩



abbrev NY3 : E6.Mp NX3 where
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
instance (p : NY3.Dc → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 9, p x))
instance (p : NY3.Dc → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 9, p x))
instance (p : NY3.Ctx → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 8, p x))
instance (p : NY3.Ctx → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 8, p x))
instance (p : NY3.Sg → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 12, p x))
instance (p : NX3.Om → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NX3.Om → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NY3.Sg) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 12) = b))
instance (a b : NY3.Ctx) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 8) = b))
instance (a b : NY3.Dc) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 9) = b))

abbrev NY3r : E6.Mp NX3 :=
  { NY3 with
    fn := (fun d x => (d.val ≤ 5 ∧ x ≠ Fn.nor) ∨ ((d.val = 6 ∨ d.val = 7 ∨ d.val = 8) ∧ (x = Fn.cog ∨ x = Fn.nor)))
    mdd := (fun d d' =>
      if d.val = 0 ∧ d'.val = 1 then some Md.nt
      else if d.val = 1 ∧ d'.val = 2 then some Md.nt
      else if d.val = 2 ∧ d'.val = 3 then some Md.nt
      else if d.val = 3 ∧ d'.val = 4 then some Md.uso
      else if d.val = 4 ∧ d'.val = 5 then some Md.uso
      else if d.val = 4 ∧ d'.val = 6 then some Md.tsi
      else if d.val = 6 ∧ d'.val = 7 then some Md.tsi
      else none)
    mdd_def := by decide }

instance (p : NY3r.Dc → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 9, p x))
instance (p : NY3r.Dc → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 9, p x))
instance (p : NY3r.Ctx → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 8, p x))
instance (p : NY3r.Ctx → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 8, p x))
instance (p : NY3r.Sg → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 12, p x))
instance (a b : NY3r.Sg) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 12) = b))
instance (a b : NY3r.Ctx) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 8) = b))
instance (a b : NY3r.Dc) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 9) = b))

theorem NY3r_ley : E6.Ley NY3r where
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


section PZ
open E4 (Perfil)
open E5 (Cs5)
open E7
abbrev NZ3 : E7.Mp NY3r where
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
instance (p : NZ3.Sy → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NZ3.Sy → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NZ3.Sy) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NZ3.Cq → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NZ3.Cq → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NZ3.Cq) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NZ3.Rs → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 4, p x))
instance (p : NZ3.Rs → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 4, p x))
instance (a b : NZ3.Rs) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 4) = b))
instance (p : NZ3.Gc → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NZ3.Gc → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NZ3.Gc) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NZ3.Epc → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NZ3.Epc → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NZ3.Epc) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NZ3.Dsp → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NZ3.Dsp → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NZ3.Dsp) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NZ3.Cn → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NZ3.Cn → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NZ3.Cn) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NZ3.Rl → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NZ3.Rl → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NZ3.Rl) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NZ3.Rsp → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NZ3.Rsp → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NZ3.Rsp) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NZ3.Sb → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NZ3.Sb → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NZ3.Sb) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NZ3.Sig → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NZ3.Sig → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NZ3.Sig) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NZ3.Ejm → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NZ3.Ejm → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NZ3.Ejm) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NZ3.Ct → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NZ3.Ct → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NZ3.Ct) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))

/-! ### Los sistemas del caso son adecuados (s₆, s₇) o no (s_A) -/
theorem nicea3_K6 : ∀ s : Fin 3, NZ3.K6 s := by
  have key : ∀ (s r r' : Fin 4) (s' : Fin 3), s'.val ≤ 1 → (r.val ≤ 2) → (r'.val ≤ 2) →
      r = r' ∨ NZ3.symNs s' r r' ∨ ∃ c, NZ3.symNs s' r c ∧ NZ3.symNs s' c r' := by
    intro _ r r' s' h1 h2 h3; revert r r'; revert s'; decide
  intro s r r' hr hr'
  have rr : ∀ (s : Fin 3) (r : Fin 4), NZ3.Rcub s r → (s.val ≤ 1 ∧ r.val ≤ 2) ∨ (s.val = 2 ∧ r.val = 3) := by
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

theorem nicea3_K1 : ∀ s : Fin 3, s.val ≤ 1 → NZ3.K1 s := by decide
theorem nicea3_K2 : ∀ s : Fin 3, s.val ≤ 1 → NZ3.K2 s := by decide
theorem nicea3_K3 : ∀ s : Fin 3, s.val ≤ 1 → NZ3.K3 s := by decide
theorem nicea3_K4 : ∀ s : Fin 3, s.val ≤ 1 → NZ3.K4 s := by decide
theorem nicea3_K5 : ∀ s : Fin 3, s.val ≤ 1 → NZ3.K5 s := by decide
theorem nicea3_K7 : ∀ s : Fin 3, s.val ≤ 1 → NZ3.K7 s := by decide
theorem nicea3_K8 : ∀ s : Fin 3, s.val ≤ 1 → NZ3.K8 s := by decide
theorem nicea3_K9 : ∀ s : Fin 3, s.val ≤ 1 → NZ3.K9 s := by decide
theorem nicea3_K10 : ∀ s : Fin 3, s.val ≤ 1 → NZ3.K10 s := by decide
theorem nicea3_K11 : ∀ s : Fin 3, s.val ≤ 1 → NZ3.K11 s := by decide
theorem nicea3_K12 : ∀ s : Fin 3, s.val ≤ 1 → NZ3.K12 s := by decide
theorem nicea3_K13 : ∀ s : Fin 3, s.val ≤ 1 → NZ3.K13 s := by decide

theorem nicea3_Adec_01 : ∀ s : Fin 3, s.val ≤ 1 → Adec NZ3 s := fun s hs =>
  ⟨nicea3_K1 s hs, nicea3_K2 s hs, nicea3_K3 s hs, nicea3_K4 s hs, nicea3_K5 s hs, nicea3_K6 s,
   nicea3_K7 s hs, nicea3_K8 s hs, nicea3_K9 s hs, nicea3_K10 s hs, nicea3_K11 s hs, nicea3_K12 s hs,
   nicea3_K13 s hs⟩

/-- s_A no es adecuado: pm = prueba (L13). -/
theorem nicea3_sA_no_adec : ¬ Adec NZ3 2 := fun h => absurd h.L13 (by decide)

theorem nicea3_Posc_01 : ∀ s : Fin 3, s.val ≤ 1 → Posc NZ3 s := fun s hs =>
  ⟨nicea3_Adec_01 s hs, (show ∀ s : Fin 3, s.val ≤ 1 → ∀ d, NZ3.Dcs s d → NY3r.Ap (NZ3.hzs s) d by decide) s hs, (show ∀ s : Fin 3, s.val ≤ 1 → ∀ v, ¬ NZ3.vnS s v by decide) s hs⟩

/-- s_A es contraposición. -/
theorem nicea3_sA_contrap : NZ3.Contrap 2 := fun h => nicea3_sA_no_adec h.toAdec

/-! ### E7 y su imagen -/
theorem nicea3_E7_d4 : ∀ s : Fin 3, NZ3.E7 4 s ↔ s.val ≤ 1 := by
  intro s; constructor
  · rintro ⟨hd, hp⟩
    exact (show ∀ s : Fin 3, NZ3.Dcs s 4 → s.val ≤ 1 by decide) s hd
  · intro hs; exact ⟨(show ∀ s : Fin 3, s.val ≤ 1 → NZ3.Dcs s 4 by decide) s hs, nicea3_Posc_01 s hs⟩

theorem nicea3_E7_d1 : ∀ s : Fin 3, ¬ NZ3.E7 1 s := by
  intro s ⟨hd, hp⟩
  have : s = 2 := (show ∀ s : Fin 3, NZ3.Dcs s 1 → s = 2 by decide) s hd
  subst this; exact nicea3_sA_contrap hp

/-- E7(d) = ∅ para las doctrinas que ningún sistema posición sostiene (d₆, d₇ son esbozos). -/
theorem nicea3_E7_otros : ∀ d : Fin 9, d.val ≠ 4 → ∀ s : Fin 3, ¬ NZ3.E7 d s := by
  intro d hd s ⟨hdc, hp⟩
  by_cases h1 : d.val = 1
  · have : d = 1 := Fin.ext h1
    subst this; exact nicea3_E7_d1 s ⟨hdc, hp⟩
  · have := (show ∀ d : Fin 9, ∀ s : Fin 3, NZ3.Dcs s d → d.val = 4 ∨ d.val = 1 by decide) d s hdc
    omega

/-- Im(E7) = Sis = {s₆, s₇}. -/
theorem nicea3_Sis : ∀ s : Fin 3, NZ3.Sis s ↔ s.val ≤ 1 := by
  intro s; constructor
  · rintro ⟨d, hd⟩
    by_cases h : d.val = 4
    · have : d = 4 := Fin.ext h
      subst this; exact (nicea3_E7_d4 s).1 hd
    · exact absurd hd (nicea3_E7_otros d h s)
  · intro hs; exact ⟨4, (nicea3_E7_d4 s).2 hs⟩

/-- La ley global L15–L16 se cumple en el caso. -/
theorem nicea3_LeyZ : E7.Ley NZ3 where
  L15a := by decide
  L15b := by
    intro s s' _ _ h; exact h
  L16a := by decide
  L16b := by
    intro s s' h _ _
    have : s = 0 ∧ s' = 1 := (show ∀ s s' : Fin 3, NZ3.Suc s s' → s = 0 ∧ s' = 1 by decide) s s' h
    obtain ⟨rfl, rfl⟩ := this
    decide

end PZ

section PW
open E4 (Perfil)
open E5 (Cs5)
open E8
def nCul3 (a : Fin 6) : Fin 3 := if a.val = 2 ∨ a.val = 4 then 1 else if a.val = 5 then 2 else 0

abbrev NW3 : E8.Mp NZ3 where
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
  Nuc := fun s d => NZ3.Dcs s d
  rI := fun s _ => s.val ≤ 1
  hum := fun e => e.val ≤ 1
  Len := fun e c x =>
    (x.val = 0 ∧ c.val = 0 ∨ x.val = 1 ∧ c.val = 1 ∨ x.val = 2 ∧ c.val = 0 ∨
     x.val = 3 ∧ c.val = 1 ∨ x.val = 4 ∧ c.val = 2) ∧
    ((x.val ≤ 1 ∧ e.val = 2) ∨ (2 ≤ x.val ∧ e.val ≤ 1))
  Pur := fun e => e.val ≤ 1
  Pob := fun c _ a => nCul3 a = c
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
  culA := nCul3
  Cmp := fun a c => (a.val = 0 ∧ c.val = 0) ∨ (a.val = 2 ∧ (c.val = 1 ∨ c.val = 2))
  Ec := fun x j => x.val = 2 ∧ j.val = 1
  Disp := fun g _ m => g.val = m.val
  Adp := fun x m => (x.val ≤ 1 ∧ m.val = 0) ∨ (2 ≤ x.val ∧ m.val = 1)

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 8192

instance (a b : NZ3.Sy) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (a b : NX3.Om) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NW3.Esf → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NW3.Esf → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NW3.Esf) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NW3.Cu → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NW3.Cu → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NW3.Cu) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NW3.Csc → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NW3.Csc → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NW3.Csc) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NW3.Prs → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 6, p x))
instance (p : NW3.Prs → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 6, p x))
instance (a b : NW3.Prs) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 6) = b))
instance (p : NW3.Ctn → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 4, p x))
instance (p : NW3.Ctn → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 4, p x))
instance (a b : NW3.Ctn) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 4) = b))
instance (p : NW3.Cmu → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NW3.Cmu → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NW3.Cmu) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NW3.Ex → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 5, p x))
instance (p : NW3.Ex → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 5, p x))
instance (a b : NW3.Ex) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 5) = b))
instance (p : NW3.Med → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NW3.Med → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NW3.Med) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NW3.Lug → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NW3.Lug → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NW3.Lug) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NW3.Tmp → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NW3.Tmp → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NW3.Tmp) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))

theorem nicea3_Tipo : NW3.Tipo := by decide

theorem nicea3_LeyW : E8.Ley NW3 where
  L1 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NW3.K1 s by decide) s ((nicea3_Sis s).1 hs)
  L2 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NW3.K2 s by decide) s ((nicea3_Sis s).1 hs)
  L3 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NW3.K3 s by decide) s ((nicea3_Sis s).1 hs)
  L4 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NW3.K4 s by decide) s ((nicea3_Sis s).1 hs)
  L5 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NW3.K5 s by decide) s ((nicea3_Sis s).1 hs)
  L6 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NW3.K6 s by decide) s ((nicea3_Sis s).1 hs)
  L7 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NW3.K7 s by decide) s ((nicea3_Sis s).1 hs)
  L8 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NW3.K8 s by decide) s ((nicea3_Sis s).1 hs)

end PW


/-- La cadena tras los dos giros: E1–E3 los de Nicea; E4 con la discrepancia nueva y p₃ reclasificado;
    E5 igual salvo el tipo; E6 reconstruido; E7 y E8 reinstanciados. -/
abbrev nicea38c : Cadena38 :=
  { M3 := N3, L3 := E3.NiceaE3_ley, PV := Fin 4, M := NM3, LM := NM3_ley, enlace := NM3_enlace,
    X := NX3, LX := NX3_ley, Y := NY3r, LY := NY3r_ley, Z := NZ3, LZ := nicea3_LeyZ,
    W := NW3, TW := nicea3_Tipo, LW := nicea3_LeyW }

section DosGiros

/-- Giro 1 (acumulativo): las discrepancias crecen, con una estrictamente nueva, y el mismo `Dsc` que `estNueva`. -/
theorem giro1_acumula :
    (∀ i j, NM.Dsc i j → NM3.Dsc i j) ∧ NM3.Dsc nar0 (itm 3) ∧ ¬ NM.Dsc nar0 (itm 3) ∧
    (∀ i j, estNueva.M4.Dsc i j ↔ NM3.Dsc i j) :=
  ⟨fun _ _ h => Or.inl h, Or.inr ⟨rfl, rfl⟩, nueva_no_en_Dsc, fun _ _ => Iff.rfl⟩

/-- Giro 2 (revisor): el conjunto de bases con posición de la contraposición (1,0,0) pasa de {1} a ∅. -/
theorem giro2_revisa :
    NM.PosB (true, false, false) (1 : Fin 2) ∧ ∀ x : Fin 2, ¬ NM3.PosB (true, false, false) x := by
  refine ⟨NM_hay_contraposicion, ?_⟩
  intro x ⟨a, _, _, h⟩
  revert x a
  decide

/-- El giro 2 no es un `Paso` de `CicloPaso`: ningún estado de `Est nicea38` tiene los perfiles de `NM3`. -/
theorem giro2_no_es_paso : ∀ s : Est nicea38, ∃ p, s.M4.Pc p ≠ NM3.Pc p :=
  fun _ => ⟨3, by show NM.Pc 3 ≠ NM3.Pc 3; decide⟩

/-- Cuánto cambia arriba: E6 pierde el desarrollo dialéctico 0→1 (y la doctrina 8 pasa de retroceder a establecerse). -/
theorem giro2_cambia_E6 :
    nicea38.Y.mdd 0 1 = some Md.dia ∧ nicea38c.Y.mdd 0 1 = some Md.nt ∧ nicea38c.Y.Est 1 8 :=
  ⟨by decide, by decide, by decide⟩

/-- Cuánto NO cambia: E1–E3 son los mismos, y los enlaces E3→E4 y E4→…→E8 valen en la cadena final. -/
theorem dos_giros_conserva :
    nicea38c.M3 = nicea38.M3 ∧ IncEnDsc nicea38c.M3 nicea38c.M3.xM nicea38c.M ∧
    ∀ {s : nicea38c.Z.Sy}, nicea38c.Z.Sis s → nicea38c.W.Rcp s (nicea38c.Z.hzs s) :=
  ⟨rfl, nicea38c.enlace, fun h => enlace78 nicea38c.toCadena48 h⟩

/-- Los dos giros recorren cadenas completas válidas: Nicea → (giro 1) → (giro 2), cada una un `Cadena38`. -/
theorem trayectoria : ∃ C0 C1 C2 : Cadena38, C0.M3 = C1.M3 ∧ C1.M3 = C2.M3 :=
  ⟨nicea38, estNueva.cadena, nicea38c, rfl, rfl⟩

end DosGiros

end N
end Ciclo
