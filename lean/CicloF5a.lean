import CicloF4b
set_option maxRecDepth 8192
namespace Ciclo
namespace N
open E5 (Cs5)
open E6
open E4 (Perfil)

section PZ
open E4 (Perfil)
open E5 (Cs5)
open E7
abbrev NZ2 : E7.Mp NY2r where
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
instance (p : NZ2.Sy → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NZ2.Sy → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NZ2.Sy) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NZ2.Cq → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NZ2.Cq → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NZ2.Cq) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NZ2.Rs → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 4, p x))
instance (p : NZ2.Rs → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 4, p x))
instance (a b : NZ2.Rs) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 4) = b))
instance (p : NZ2.Gc → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NZ2.Gc → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NZ2.Gc) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NZ2.Epc → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NZ2.Epc → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NZ2.Epc) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NZ2.Dsp → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NZ2.Dsp → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NZ2.Dsp) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NZ2.Cn → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NZ2.Cn → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NZ2.Cn) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NZ2.Rl → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NZ2.Rl → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NZ2.Rl) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NZ2.Rsp → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NZ2.Rsp → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NZ2.Rsp) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NZ2.Sb → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NZ2.Sb → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NZ2.Sb) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NZ2.Sig → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NZ2.Sig → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NZ2.Sig) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NZ2.Ejm → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NZ2.Ejm → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NZ2.Ejm) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NZ2.Ct → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NZ2.Ct → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NZ2.Ct) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))

/-! ### Los sistemas del caso son adecuados (s₆, s₇) o no (s_A) -/
theorem nicea2_K6 : ∀ s : Fin 3, NZ2.K6 s := by
  have key : ∀ (s r r' : Fin 4) (s' : Fin 3), s'.val ≤ 1 → (r.val ≤ 2) → (r'.val ≤ 2) →
      r = r' ∨ NZ2.symNs s' r r' ∨ ∃ c, NZ2.symNs s' r c ∧ NZ2.symNs s' c r' := by
    intro _ r r' s' h1 h2 h3; revert r r'; revert s'; decide
  intro s r r' hr hr'
  have rr : ∀ (s : Fin 3) (r : Fin 4), NZ2.Rcub s r → (s.val ≤ 1 ∧ r.val ≤ 2) ∨ (s.val = 2 ∧ r.val = 3) := by
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

theorem nicea2_K1 : ∀ s : Fin 3, s.val ≤ 1 → NZ2.K1 s := by decide
theorem nicea2_K2 : ∀ s : Fin 3, s.val ≤ 1 → NZ2.K2 s := by decide
theorem nicea2_K3 : ∀ s : Fin 3, s.val ≤ 1 → NZ2.K3 s := by decide
theorem nicea2_K4 : ∀ s : Fin 3, s.val ≤ 1 → NZ2.K4 s := by decide
theorem nicea2_K5 : ∀ s : Fin 3, s.val ≤ 1 → NZ2.K5 s := by decide
theorem nicea2_K7 : ∀ s : Fin 3, s.val ≤ 1 → NZ2.K7 s := by decide
theorem nicea2_K8 : ∀ s : Fin 3, s.val ≤ 1 → NZ2.K8 s := by decide
theorem nicea2_K9 : ∀ s : Fin 3, s.val ≤ 1 → NZ2.K9 s := by decide
theorem nicea2_K10 : ∀ s : Fin 3, s.val ≤ 1 → NZ2.K10 s := by decide
theorem nicea2_K11 : ∀ s : Fin 3, s.val ≤ 1 → NZ2.K11 s := by decide
theorem nicea2_K12 : ∀ s : Fin 3, s.val ≤ 1 → NZ2.K12 s := by decide
theorem nicea2_K13 : ∀ s : Fin 3, s.val ≤ 1 → NZ2.K13 s := by decide

theorem nicea2_Adec_01 : ∀ s : Fin 3, s.val ≤ 1 → Adec NZ2 s := fun s hs =>
  ⟨nicea2_K1 s hs, nicea2_K2 s hs, nicea2_K3 s hs, nicea2_K4 s hs, nicea2_K5 s hs, nicea2_K6 s,
   nicea2_K7 s hs, nicea2_K8 s hs, nicea2_K9 s hs, nicea2_K10 s hs, nicea2_K11 s hs, nicea2_K12 s hs,
   nicea2_K13 s hs⟩

/-- s_A no es adecuado: pm = prueba (L13). -/
theorem nicea2_sA_no_adec : ¬ Adec NZ2 2 := fun h => absurd h.L13 (by decide)

theorem nicea2_Posc_01 : ∀ s : Fin 3, s.val ≤ 1 → Posc NZ2 s := fun s hs =>
  ⟨nicea2_Adec_01 s hs, (show ∀ s : Fin 3, s.val ≤ 1 → ∀ d, NZ2.Dcs s d → NY2r.Ap (NZ2.hzs s) d by decide) s hs, (show ∀ s : Fin 3, s.val ≤ 1 → ∀ v, ¬ NZ2.vnS s v by decide) s hs⟩

/-- s_A es contraposición. -/
theorem nicea2_sA_contrap : NZ2.Contrap 2 := fun h => nicea2_sA_no_adec h.toAdec

/-! ### E7 y su imagen -/
theorem nicea2_E7_d4 : ∀ s : Fin 3, NZ2.E7 4 s ↔ s.val ≤ 1 := by
  intro s; constructor
  · rintro ⟨hd, hp⟩
    exact (show ∀ s : Fin 3, NZ2.Dcs s 4 → s.val ≤ 1 by decide) s hd
  · intro hs; exact ⟨(show ∀ s : Fin 3, s.val ≤ 1 → NZ2.Dcs s 4 by decide) s hs, nicea2_Posc_01 s hs⟩

theorem nicea2_E7_d1 : ∀ s : Fin 3, ¬ NZ2.E7 1 s := by
  intro s ⟨hd, hp⟩
  have : s = 2 := (show ∀ s : Fin 3, NZ2.Dcs s 1 → s = 2 by decide) s hd
  subst this; exact nicea2_sA_contrap hp

/-- E7(d) = ∅ para las doctrinas que ningún sistema posición sostiene (d₆, d₇ son esbozos). -/
theorem nicea2_E7_otros : ∀ d : Fin 9, d.val ≠ 4 → ∀ s : Fin 3, ¬ NZ2.E7 d s := by
  intro d hd s ⟨hdc, hp⟩
  by_cases h1 : d.val = 1
  · have : d = 1 := Fin.ext h1
    subst this; exact nicea2_E7_d1 s ⟨hdc, hp⟩
  · have := (show ∀ d : Fin 9, ∀ s : Fin 3, NZ2.Dcs s d → d.val = 4 ∨ d.val = 1 by decide) d s hdc
    omega

/-- Im(E7) = Sis = {s₆, s₇}. -/
theorem nicea2_Sis : ∀ s : Fin 3, NZ2.Sis s ↔ s.val ≤ 1 := by
  intro s; constructor
  · rintro ⟨d, hd⟩
    by_cases h : d.val = 4
    · have : d = 4 := Fin.ext h
      subst this; exact (nicea2_E7_d4 s).1 hd
    · exact absurd hd (nicea2_E7_otros d h s)
  · intro hs; exact ⟨4, (nicea2_E7_d4 s).2 hs⟩

/-- La ley global L15–L16 se cumple en el caso. -/
theorem nicea2_LeyZ : E7.Ley NZ2 where
  L15a := by decide
  L15b := by
    intro s s' _ _ h; exact h
  L16a := by decide
  L16b := by
    intro s s' h _ _
    have : s = 0 ∧ s' = 1 := (show ∀ s s' : Fin 3, NZ2.Suc s s' → s = 0 ∧ s' = 1 by decide) s s' h
    obtain ⟨rfl, rfl⟩ := this
    decide

end PZ

section PW
open E4 (Perfil)
open E5 (Cs5)
open E8
def nCul2 (a : Fin 6) : Fin 3 := if a.val = 2 ∨ a.val = 4 then 1 else if a.val = 5 then 2 else 0

abbrev NW2 : E8.Mp NZ2 where
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
  Nuc := fun s d => NZ2.Dcs s d
  rI := fun s _ => s.val ≤ 1
  hum := fun e => e.val ≤ 1
  Len := fun e c x =>
    (x.val = 0 ∧ c.val = 0 ∨ x.val = 1 ∧ c.val = 1 ∨ x.val = 2 ∧ c.val = 0 ∨
     x.val = 3 ∧ c.val = 1 ∨ x.val = 4 ∧ c.val = 2) ∧
    ((x.val ≤ 1 ∧ e.val = 2) ∨ (2 ≤ x.val ∧ e.val ≤ 1))
  Pur := fun e => e.val ≤ 1
  Pob := fun c _ a => nCul2 a = c
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
  culA := nCul2
  Cmp := fun a c => (a.val = 0 ∧ c.val = 0) ∨ (a.val = 2 ∧ (c.val = 1 ∨ c.val = 2))
  Ec := fun x j => x.val = 2 ∧ j.val = 1
  Disp := fun g _ m => g.val = m.val
  Adp := fun x m => (x.val ≤ 1 ∧ m.val = 0) ∨ (2 ≤ x.val ∧ m.val = 1)

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 8192

instance (a b : NZ2.Sy) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (a b : NX2.Om) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NW2.Esf → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NW2.Esf → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NW2.Esf) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NW2.Cu → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NW2.Cu → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NW2.Cu) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 3) = b))
instance (p : NW2.Csc → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NW2.Csc → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NW2.Csc) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))
instance (p : NW2.Prs → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 6, p x))
instance (p : NW2.Prs → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 6, p x))
instance (a b : NW2.Prs) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 6) = b))
instance (p : NW2.Ctn → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 4, p x))
instance (p : NW2.Ctn → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 4, p x))
instance (a b : NW2.Ctn) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 4) = b))
instance (p : NW2.Cmu → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NW2.Cmu → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NW2.Cmu) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NW2.Ex → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 5, p x))
instance (p : NW2.Ex → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 5, p x))
instance (a b : NW2.Ex) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 5) = b))
instance (p : NW2.Med → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NW2.Med → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NW2.Med) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NW2.Lug → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 2, p x))
instance (p : NW2.Lug → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 2, p x))
instance (a b : NW2.Lug) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 2) = b))
instance (p : NW2.Tmp → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 1, p x))
instance (p : NW2.Tmp → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 1, p x))
instance (a b : NW2.Tmp) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 1) = b))

theorem nicea2_Tipo : NW2.Tipo := by decide

theorem nicea2_LeyW : E8.Ley NW2 where
  L1 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NW2.K1 s by decide) s ((nicea2_Sis s).1 hs)
  L2 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NW2.K2 s by decide) s ((nicea2_Sis s).1 hs)
  L3 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NW2.K3 s by decide) s ((nicea2_Sis s).1 hs)
  L4 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NW2.K4 s by decide) s ((nicea2_Sis s).1 hs)
  L5 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NW2.K5 s by decide) s ((nicea2_Sis s).1 hs)
  L6 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NW2.K6 s by decide) s ((nicea2_Sis s).1 hs)
  L7 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NW2.K7 s by decide) s ((nicea2_Sis s).1 hs)
  L8 := fun s hs => (show ∀ s : Fin 3, s.val ≤ 1 → NW2.K8 s by decide) s ((nicea2_Sis s).1 hs)

end PW

end N
end Ciclo
