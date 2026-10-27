import CicloF5
/-
  CicloF6 · (1) el declive como estado admitido por la ley: reclasificar toda posición como contraposición;
  (2) subdeterminación de E4–E8 por sus predecesores (lectura de «no derivable» como en `E3_no_determinada_por_E2`).
  Lean 4 (sin Mathlib, sin sorry).
-/
set_option maxRecDepth 8192
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000
namespace Ciclo
namespace N
open E5 (Cs5)
open E6
open E4 (Perfil)
open E7
open E8

section Declive
abbrev NM4 : E4.Mp (Fin 4) It where
  CT := Bool
  Ep := Bool
  Mf := Bool
  Et := Bool
  Vr := Bool
  car := fun p => ((true, true, true), false, false)
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

theorem NM4_ley : E4.Ley NM4 where
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
      have key : ∀ a b : Fin 4, NM4.Odl3 a → NM4.Odl3 b → NM4.π a = NM4.π b →
          b ∈ E4.reach NM4 a 4 := by decide
      exact E4.reach_sound NM4 a ha 4 b (key a b ha hb h)
    · exact E4.EqC_pi NM4 (by decide)
  L6a := by decide
  L6b := by decide
  L6c := E4.TG.irrefl_of_rank _ (fun x => x.val) (by decide)
  L7 := by
    have key : ∀ a b : Fin 4, (NM4.rel a b).isSome → NM4.rel a b ≠ some E4.Rel.irreductible →
        NM4.Pc a = NM4.Pc b := by decide
    intro a b r hr hne
    have hs : (NM4.rel a b).isSome = true := by rw [hr]; rfl
    exact key a b hs (by rw [hr]; intro h; exact hne (Option.some.inj h))
  L9 := fun _ _ _ => Iff.rfl
  L10 := by decide


section PX
open E5
abbrev NX4 : E5.Mp NM4 where
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

theorem NX4_ley : E5.Ley NX4 where
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
abbrev NY4 : E6.Mp NX4 where
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
instance (p : NY4.Dc → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 9, p x))
instance (p : NY4.Dc → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 9, p x))
instance (p : NY4.Ctx → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 8, p x))
instance (p : NY4.Ctx → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 8, p x))
instance (p : NY4.Sg → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 12, p x))
instance (p : NX4.Om → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NX4.Om → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NY4.Sg) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 12) = b))
instance (a b : NY4.Ctx) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 8) = b))
instance (a b : NY4.Dc) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 9) = b))



end PY

/-- Declive: el mismo E4 con las mismas discrepancias y relaciones, pero toda posición reclasificada como
    contraposición. La ley de E4 y el enlace E3→E4 se conservan: la ley *admite* el declive
    (a diferencia de borrar objetivaciones, `declive_rompe_ley`). -/
theorem declive_admitido : E4.Ley NM4 ∧ IncEnDsc N3 N3.xM NM4 := ⟨NM4_ley, NM_enlace⟩

theorem NM_hay_posicion : NM.PosB (true, true, true) (0 : Fin 2) :=
  ⟨(0 : Fin 4), by decide, by decide, by decide⟩

theorem NM4_sin_posicion : ∀ x : NM4.Base, ¬ NM4.PosB (true, true, true) x := by
  intro x ⟨a, _, _, h⟩
  revert x a
  decide

theorem NM4_todo_contraposicion : ∀ x : NM4.Base, NM4.PosB (true, false, false) x := by
  intro x
  revert x
  decide

/-- El E6 de Nicea no es modelo sobre el E4 en declive: L12 exige un enlace ≈ hacia un horizonte de posición. -/
theorem NY4_no_ley : ¬ E6.Ley NY4 := by
  intro L
  have h := L.L12 (0 : Fin 9) (1 : Fin 9) (by decide)
  rcases h with ⟨d'', w'', w', _, _, hh', ⟨b, b', _, hb', _⟩⟩
  have h1 : NY4.hz (1 : Fin 9) = some 2 := rfl
  rw [h1] at hh'
  have hw : w' = 2 := (Option.some.inj hh').symm
  subst hw
  exact NM4_sin_posicion b' (by simpa using hb')

/-- En declive, ninguna doctrina se establece desde un horizonte pleno: E6 pierde todo lo normativo. -/
theorem NY4_sin_est : ∀ (w : NX4.Om) (d : NY4.Dc), NX4.pf w = (true, true, true) → ¬ NY4.Est w d := by
  decide

/-- Progreso y declive son ambos pasos admitidos por la ley, con orientación opuesta:
    el giro 2 vacía las bases de contraposición; el declive vacía las de posición. -/
theorem progreso_y_declive :
    (NM.PosB (true, false, false) (1 : Fin 2) ∧ ∀ x : NM2.Base, ¬ NM2.PosB (true, false, false) x) ∧
    (NM.PosB (true, true, true) (0 : Fin 2) ∧ ∀ x : NM4.Base, ¬ NM4.PosB (true, true, true) x) ∧
    E4.Ley NM2 ∧ E4.Ley NM4 :=
  ⟨⟨NM_hay_contraposicion, NM2_sin_contraposicion⟩, ⟨NM_hay_posicion, NM4_sin_posicion⟩, NM2_ley, NM4_ley⟩

end Declive

section Sub
section PZ
open E4 (Perfil)
open E5 (Cs5)
open E7
abbrev NZb : E7.Mp NY where
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
  tq := fun _ => Tq.cur
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
instance (p : NZb.Sy → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NZb.Sy → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NZb.Sy) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NZb.Cq → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NZb.Cq → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NZb.Cq) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NZb.Rs → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 4, p x))
instance (p : NZb.Rs → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 4, p x))
instance (a b : NZb.Rs) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 4) = b))
instance (p : NZb.Gc → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NZb.Gc → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NZb.Gc) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NZb.Epc → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NZb.Epc → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NZb.Epc) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NZb.Dsp → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NZb.Dsp → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NZb.Dsp) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NZb.Cn → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NZb.Cn → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NZb.Cn) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NZb.Rl → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NZb.Rl → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NZb.Rl) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NZb.Rsp → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NZb.Rsp → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NZb.Rsp) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NZb.Sb → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NZb.Sb → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NZb.Sb) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NZb.Sig → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NZb.Sig → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NZb.Sig) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NZb.Ejm → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NZb.Ejm → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NZb.Ejm) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NZb.Ct → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NZb.Ct → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NZb.Ct) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))

/-! ### Los sistemas del caso son adecuados (s₆, s₇) o no (s_A) -/
theorem niceab_K6 : ∀ s : Fin 3, NZb.K6 s := by
  have key : ∀ (s r r' : Fin 4) (s' : Fin 3), s'.val ≤ 1 → (r.val ≤ 2) → (r'.val ≤ 2) →
      r = r' ∨ NZb.symNs s' r r' ∨ ∃ c, NZb.symNs s' r c ∧ NZb.symNs s' c r' := by
    intro _ r r' s' h1 h2 h3; revert r r'; revert s'; decide
  intro s r r' hr hr'
  have rr : ∀ (s : Fin 3) (r : Fin 4), NZb.Rcub s r → (s.val ≤ 1 ∧ r.val ≤ 2) ∨ (s.val = 2 ∧ r.val = 3) := by
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

theorem niceab_K1 : ∀ s : Fin 3, s.val ≤ 1 → NZb.K1 s := by decide
theorem niceab_K2 : ∀ s : Fin 3, s.val ≤ 1 → NZb.K2 s := by decide
theorem niceab_K3 : ∀ s : Fin 3, s.val ≤ 1 → NZb.K3 s := by decide
theorem niceab_K4 : ∀ s : Fin 3, s.val ≤ 1 → NZb.K4 s := by decide
theorem niceab_K5 : ∀ s : Fin 3, s.val ≤ 1 → NZb.K5 s := by decide
theorem niceab_K7 : ∀ s : Fin 3, s.val ≤ 1 → NZb.K7 s := by decide
theorem niceab_K8 : ∀ s : Fin 3, s.val ≤ 1 → NZb.K8 s := by decide
theorem niceab_K9 : ∀ s : Fin 3, s.val ≤ 1 → NZb.K9 s := by decide
theorem niceab_K10 : ∀ s : Fin 3, s.val ≤ 1 → NZb.K10 s := by decide
theorem niceab_K11 : ∀ s : Fin 3, s.val ≤ 1 → NZb.K11 s := by decide
theorem niceab_K12 : ∀ s : Fin 3, s.val ≤ 1 → NZb.K12 s := by decide
theorem niceab_K13 : ∀ s : Fin 3, s.val ≤ 1 → NZb.K13 s := by decide

theorem niceab_Adec_01 : ∀ s : Fin 3, s.val ≤ 1 → Adec NZb s := fun s hs =>
  ⟨niceab_K1 s hs, niceab_K2 s hs, niceab_K3 s hs, niceab_K4 s hs, niceab_K5 s hs, niceab_K6 s,
   niceab_K7 s hs, niceab_K8 s hs, niceab_K9 s hs, niceab_K10 s hs, niceab_K11 s hs, niceab_K12 s hs,
   niceab_K13 s hs⟩

/-- s_A no es adecuado: pm = prueba (L13). -/
theorem niceab_sA_no_adec : ¬ Adec NZb 2 := fun h => absurd h.L13 (by decide)

theorem niceab_Posc_01 : ∀ s : Fin 3, s.val ≤ 1 → Posc NZb s := fun s hs =>
  ⟨niceab_Adec_01 s hs, (show ∀ s : Fin 3, s.val ≤ 1 → ∀ d, NZb.Dcs s d → NY.Ap (NZb.hzs s) d by decide) s hs, (show ∀ s : Fin 3, s.val ≤ 1 → ∀ v, ¬ NZb.vnS s v by decide) s hs⟩

/-- s_A es contraposición. -/
theorem niceab_sA_contrap : NZb.Contrap 2 := fun h => niceab_sA_no_adec h.toAdec

/-! ### E7 y su imagen -/
theorem niceab_E7_d4 : ∀ s : Fin 3, NZb.E7 4 s ↔ s.val ≤ 1 := by
  intro s; constructor
  · rintro ⟨hd, hp⟩
    exact (show ∀ s : Fin 3, NZb.Dcs s 4 → s.val ≤ 1 by decide) s hd
  · intro hs; exact ⟨(show ∀ s : Fin 3, s.val ≤ 1 → NZb.Dcs s 4 by decide) s hs, niceab_Posc_01 s hs⟩

theorem niceab_E7_d1 : ∀ s : Fin 3, ¬ NZb.E7 1 s := by
  intro s ⟨hd, hp⟩
  have : s = 2 := (show ∀ s : Fin 3, NZb.Dcs s 1 → s = 2 by decide) s hd
  subst this; exact niceab_sA_contrap hp

/-- E7(d) = ∅ para las doctrinas que ningún sistema posición sostiene (d₆, d₇ son esbozos). -/
theorem niceab_E7_otros : ∀ d : Fin 9, d.val ≠ 4 → ∀ s : Fin 3, ¬ NZb.E7 d s := by
  intro d hd s ⟨hdc, hp⟩
  by_cases h1 : d.val = 1
  · have : d = 1 := Fin.ext h1
    subst this; exact niceab_E7_d1 s ⟨hdc, hp⟩
  · have := (show ∀ d : Fin 9, ∀ s : Fin 3, NZb.Dcs s d → d.val = 4 ∨ d.val = 1 by decide) d s hdc
    omega

/-- Im(E7) = Sis = {s₆, s₇}. -/
theorem niceab_Sis : ∀ s : Fin 3, NZb.Sis s ↔ s.val ≤ 1 := by
  intro s; constructor
  · rintro ⟨d, hd⟩
    by_cases h : d.val = 4
    · have : d = 4 := Fin.ext h
      subst this; exact (niceab_E7_d4 s).1 hd
    · exact absurd hd (niceab_E7_otros d h s)
  · intro hs; exact ⟨4, (niceab_E7_d4 s).2 hs⟩

/-- La ley global L15–L16 se cumple en el caso. -/
theorem niceab_LeyZ : E7.Ley NZb where
  L15a := by decide
  L15b := by
    intro s s' _ _ h; exact h
  L16a := by decide
  L16b := by
    intro s s' h _ _
    have : s = 0 ∧ s' = 1 := (show ∀ s s' : Fin 3, NZb.Suc s s' → s = 0 ∧ s' = 1 by decide) s s' h
    obtain ⟨rfl, rfl⟩ := this
    decide

end PZ
section PW
open E4 (Perfil)
open E5 (Cs5)
open E8
def nCulw (a : Fin 6) : Fin 3 := if a.val = 2 ∨ a.val = 4 then 1 else if a.val = 5 then 2 else 0

abbrev NWb : E8.Mp NZ where
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
  Pob := fun c _ a => nCulw a = c
  hzA := fun a => if a.val ≤ 2 then (2 : Fin 3) else (0 : Fin 3)
  nvs := fun _ => Nvs.exp
  tpc := fun k => if k.val = 0 ∨ k.val = 3 then Tsg.cog else if k.val = 1 then Tsg.con else Tsg.efe
  -- variante libre: niveles de significación todos «exp»
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
  culA := nCulw
  Cmp := fun a c => (a.val = 0 ∧ c.val = 0) ∨ (a.val = 2 ∧ (c.val = 1 ∨ c.val = 2))
  Ec := fun x j => x.val = 2 ∧ j.val = 1
  Disp := fun g _ m => g.val = m.val
  Adp := fun x m => (x.val ≤ 1 ∧ m.val = 0) ∨ (2 ≤ x.val ∧ m.val = 1)

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 8192

instance (a b : NZ.Sy) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (a b : NX.Om) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NWb.Esf → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NWb.Esf → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NWb.Esf) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NWb.Cu → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NWb.Cu → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NWb.Cu) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NWb.Csc → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NWb.Csc → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NWb.Csc) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NWb.Prs → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 6, p x))
instance (p : NWb.Prs → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 6, p x))
instance (a b : NWb.Prs) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 6) = b))
instance (p : NWb.Ctn → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 4, p x))
instance (p : NWb.Ctn → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 4, p x))
instance (a b : NWb.Ctn) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 4) = b))
instance (p : NWb.Cmu → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NWb.Cmu → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NWb.Cmu) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NWb.Ex → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 5, p x))
instance (p : NWb.Ex → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 5, p x))
instance (a b : NWb.Ex) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 5) = b))
instance (p : NWb.Med → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NWb.Med → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NWb.Med) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NWb.Lug → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NWb.Lug → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NWb.Lug) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NWb.Tmp → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NWb.Tmp → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NWb.Tmp) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))

theorem niceaw_Tipo : NWb.Tipo := by decide

theorem niceaw_LeyW : E8.Ley NWb where
  L1 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NWb.K1 s by decide) s ((nicea_Sis s).1 hs)
  L2 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NWb.K2 s by decide) s ((nicea_Sis s).1 hs)
  L3 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NWb.K3 s by decide) s ((nicea_Sis s).1 hs)
  L4 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NWb.K4 s by decide) s ((nicea_Sis s).1 hs)
  L5 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NWb.K5 s by decide) s ((nicea_Sis s).1 hs)
  L6 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NWb.K6 s by decide) s ((nicea_Sis s).1 hs)
  L7 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NWb.K7 s by decide) s ((nicea_Sis s).1 hs)
  L8 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NWb.K8 s by decide) s ((nicea_Sis s).1 hs)

end PW

/-- E4 está subdeterminado por E1–E3: tres modelos con ley sobre los mismos ítems, con perfiles distintos. -/
theorem E4_subdeterminado :
    E4.Ley NM ∧ E4.Ley NM2 ∧ E4.Ley NM4 ∧ NM.Pc 3 ≠ NM2.Pc 3 ∧ NM.Pc 0 ≠ NM4.Pc 0 :=
  ⟨NM_ley, NM2_ley, NM4_ley, by decide, by decide⟩

/-- E5 subdeterminado por E4: dos modelos con ley sobre el mismo E4 que difieren en la escala de cada conversión. -/
abbrev NXb : E5.Mp NM := { NX with k5 := fun _ => E5.Esc.comunitaria }
theorem NXb_ley : E5.Ley NXb := by
  cases NX_ley
  constructor <;> assumption
theorem E5_subdeterminado : E5.Ley NX ∧ E5.Ley NXb ∧ NX.k5 0 ≠ NXb.k5 0 :=
  ⟨NX_ley, NXb_ley, by decide⟩

section Y6
open E4 (Perfil)
open E5 (Cs5)
open E6
/-- E6 subdeterminado por E5: el desarrollo 0→1 puede ser de nota en lugar de dialéctico sobre el mismo X. -/
abbrev NYb : E6.Mp NX :=
  { NY with
    mdd := (fun d d' => if d.val = 0 ∧ d'.val = 1 then some Md.nt else NY.mdd d d')
    mdd_def := by decide }

instance (p : NYb.Dc → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 9, p x))
instance (p : NYb.Dc → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 9, p x))
instance (p : NYb.Ctx → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 8, p x))
instance (p : NYb.Ctx → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 8, p x))
instance (p : NYb.Sg → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 12, p x))
instance (a b : NYb.Sg) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 12) = b))
instance (a b : NYb.Ctx) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 8) = b))
instance (a b : NYb.Dc) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 9) = b))

theorem NYb_ley : E6.Ley NYb where
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

theorem E6_subdeterminado : E6.Ley NY ∧ E6.Ley NYb ∧ NY.mdd 0 1 ≠ NYb.mdd 0 1 :=
  ⟨NY_ley, NYb_ley, by decide⟩
end Y6

theorem E7_subdeterminado : E7.Ley NZ ∧ E7.Ley NZb ∧ NZ.tq 0 ≠ NZb.tq 0 :=
  ⟨nicea_LeyZ, niceab_LeyZ, by decide⟩

theorem E8_subdeterminado : E8.Ley NW ∧ E8.Ley NWb ∧ NW.nvs 0 ≠ NWb.nvs 0 :=
  ⟨nicea_LeyW, niceaw_LeyW, by decide⟩

end Sub

end N
end Ciclo
