import CicloF4
/-
  CicloF4b · F4 parte fuerte: una corrección de E4 que cambia perfiles obliga a reconstruir E6 (y lo que depende).
  Corrección: la dialéctica reclasifica el punto de vista p₃ (tesis contraria, antes contraposición (1,0,0))
  como posición (1,1,1): ya no hay base con posición de perfil (1,0,0).
  Lean 4 (sin Mathlib, sin sorry).
-/
set_option maxRecDepth 8192
namespace Ciclo
namespace N
open E5 (Cs5)
open E6
open E4 (Perfil)

abbrev NM2 : E4.Mp (Fin 4) It where
  CT := Bool
  Ep := Bool
  Mf := Bool
  Et := Bool
  Vr := Bool
  car := fun p => ((true, true, true), decide (p.val < 4), decide (p.val < 4))
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

theorem NM2_ley : E4.Ley NM2 where
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
      have key : ∀ a b : Fin 4, NM2.Odl3 a → NM2.Odl3 b → NM2.π a = NM2.π b →
          b ∈ E4.reach NM2 a 4 := by decide
      exact E4.reach_sound NM2 a ha 4 b (key a b ha hb h)
    · exact E4.EqC_pi NM2 (by decide)
  L6a := by decide
  L6b := by decide
  L6c := E4.TG.irrefl_of_rank _ (fun x => x.val) (by decide)
  L7 := by
    have key : ∀ a b : Fin 4, (NM2.rel a b).isSome → NM2.rel a b ≠ some E4.Rel.irreductible →
        NM2.Pc a = NM2.Pc b := by decide
    intro a b r hr hne
    have hs : (NM2.rel a b).isSome = true := by rw [hr]; rfl
    exact key a b hs (by rw [hr]; intro h; exact hne (Option.some.inj h))
  L9 := fun _ _ _ => Iff.rfl
  L10 := by decide


abbrev NX2 : E5.Mp NM2 where
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

theorem NX2_ley : E5.Ley NX2 where
  D1 := by decide
  D2 := by intro c b b' h; simp at h
  D3 := by intro y c h; simp at h
  C1 := by decide
  C2 := by decide
  C3 := by intro w a _; rfl
  C4a := by decide
  C4b := ⟨0, by decide⟩



abbrev NY2 : E6.Mp NX2 where
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
instance (p : NY2.Dc → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 9, p x))
instance (p : NY2.Dc → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 9, p x))
instance (p : NY2.Ctx → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 8, p x))
instance (p : NY2.Ctx → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 8, p x))
instance (p : NY2.Sg → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 12, p x))
instance (p : NX2.Om → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 3, p x))
instance (p : NX2.Om → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 3, p x))
instance (a b : NY2.Sg) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 12) = b))
instance (a b : NY2.Ctx) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 8) = b))
instance (a b : NY2.Dc) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 9) = b))



/-- Tras la reclasificación ninguna base tiene posición de perfil (1,0,0). -/
theorem NM2_sin_contraposicion : ∀ x : NM2.Base, ¬ NM2.PosB (true, false, false) x := by
  intro x ⟨a, _, _, h⟩
  revert x a
  decide

/-- Antes sí la había (base 1): el E4 original. -/
theorem NM_hay_contraposicion : NM.PosB (true, false, false) (1 : Fin 2) :=
  ⟨(3 : Fin 4), by decide, by decide, by decide⟩

/-- El horizonte inauténtico (ω₀, perfil (1,0,0)) ya no tiene enlace ≈ con ningún otro. -/
theorem NX2_sin_dia : ∀ w : NX2.Om, ¬ E6.DiaH NX2 0 w := by
  intro w ⟨b, b', hb, _, _⟩
  exact NM2_sin_contraposicion b (by simpa using hb)

/-- El E6 anterior (misma `NY`) no es modelo sobre el E4 corregido: L12 falla (su desarrollo dialéctico 0→1
    exige un enlace ≈ desde el horizonte de la contraposición). -/
theorem NY2_no_ley : ¬ E6.Ley NY2 := by
  intro L
  have h := L.L12 (0 : Fin 9) (1 : Fin 9) (by decide)
  rcases h with ⟨d'', w'', w', hc, hh, _, hD⟩
  have hd : d'' = (8 : Fin 9) := Fin.ext hc.1
  subst hd
  have h8 : NY2.hz (8 : Fin 9) = some 0 := rfl
  rw [h8] at hh
  have hw : w'' = 0 := (Option.some.inj hh).symm
  subst hw
  exact NX2_sin_dia w' hD

/-- Reconstrucción mínima de E6: el paso 0→1 deja de ser desarrollo dialéctico y pasa a ser de nota (`nt`);
    ya no hay contraposición de horizonte que enlazar. -/
abbrev NY2r : E6.Mp NX2 :=
  { NY2 with
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

instance (p : NY2r.Dc → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 9, p x))
instance (p : NY2r.Dc → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 9, p x))
instance (p : NY2r.Ctx → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 8, p x))
instance (p : NY2r.Ctx → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=
  inferInstanceAs (Decidable (∃ x : Fin 8, p x))
instance (p : NY2r.Sg → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=
  inferInstanceAs (Decidable (∀ x : Fin 12, p x))
instance (a b : NY2r.Sg) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 12) = b))
instance (a b : NY2r.Ctx) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 8) = b))
instance (a b : NY2r.Dc) : Decidable (a = b) := inferInstanceAs (Decidable ((a : Fin 9) = b))

theorem NY2r_ley : E6.Ley NY2r where
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

/-- El cambio es real: el E6 reconstruido ya no tiene el desarrollo dialéctico que tenía el original. -/
theorem NY2r_cambia : NY2r.mdd 0 1 ≠ NY.mdd 0 1 := by decide

/-- Segundo efecto, sobre el contenido: la doctrina 8 (apoyada en p₃) era una contraposición para el horizonte
    pleno; con p₃ reclasificado pasa a posición, así que E6 ya no la hace retroceder sino que la establece. -/
theorem original_doctrina8_contra : NY.Contra 1 8 := by decide
theorem corregido_doctrina8_pos : NY2r.Pos 1 8 := by decide
theorem corregido_doctrina8_est : NY2r.Est 1 8 := by decide

end N
end Ciclo
