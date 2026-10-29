/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The common cube-free geometry and LOW defect estimates retain Sil and
OpenAI's original source-step attribution. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.Ledger
import Candidate.Local.Qrh.JointDetector.FinePointwiseLedger
import Candidate.Local.Qrh.JointDetector.FineSourceChains.Common

namespace Qrh.JointDetector.RepeatedMarks.CurvedSourceStep
noncomputable section
set_option autoImplicit false
open Set
open QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree
open QRH.SilDensitySplit.Hybrid QRH.SilDensitySplit.Density

structure Params where
  B0 : ℝ
  L0 : ℝ
  c0 : ℝ
  B : ℝ
  L : ℝ
  c : ℝ
  A : ℝ
  D : ℝ

def crossing (p : Params) : ℝ := Hybrid.cross p.B0 p.L0 p.B p.L

def data (p : Params) (q : ℝ → ℝ) (F : ℝ → WeightedFamily) (hL : 0 < p.L0)
    (hq : ∀ w, q w ∈ Icc (0:ℝ) 1) : StepData where
  B₀ := p.B0
  L₀ := p.L0
  c₀ := p.c0
  B := p.B
  L := p.L
  c := p.c
  κ := 3/4
  s₀ := crossing p
  Hmin := 9/10
  Hmax := 3
  sel := fun _ w => sel p.A p.D (max 0 (w-crossing p))
  price := weightedPrice p.B0 p.L0 p.c0 hL (fun w => q (max (crossing p) w)) (fun w => hq _) (fun w => F (max (crossing p) w))

/-- Every HIGH gate ranges over the full common label family. Finite
certificates must discharge it, including both amplitude regimes. -/
structure Gates (p : Params) (q : ℝ → ℝ) (F : ℝ → WeightedFamily) : Prop where
  face : DSFace p.B0 p.L0 p.c0 p.B p.L p.c
  B0_pos : 0 < p.B0
  A_pos : 0 < p.A
  A_lt : p.A < 1
  D_nonneg : 0 ≤ p.D
  cut_mem : ∀ w, q w ∈ Icc (0:ℝ) (3/4)
  width_pos : 0 < p.c-crossing p
  low_payment : ∀ w ∈ Icc (crossing p) p.c,
    0 ≤ p.L0*sel p.A p.D (w-crossing p)-q w*((p.L0-p.L)*(w-crossing p)+(6*p.B0-p.L0)*sel p.A p.D (w-crossing p))
  low_overshoot : ∀ w ∈ Icc (crossing p) p.c, q w*(6*p.B0-p.L0) ≤ p.L0
  height : ∃ r, 0 < r ∧ ∀ w ∈ Icc (crossing p) p.c,
    9/10+r ≤ 1-6*(sel p.A p.D (w-crossing p))
  cap : ∃ r, 0 < r ∧ ∀ w ∈ Icc (crossing p) p.c,
    r ≤ p.c0*(1-6*(sel p.A p.D (w-crossing p)))-(w-sel p.A p.D (w-crossing p))
  high : ∃ r, 0 < r ∧ ∀ w ∈ Icc (crossing p) p.c,
    HighReserve (F w) p.B p.L w (sel p.A p.D (w-crossing p)) r
  reference : ∃ r, 0 < r ∧ ∀ w ∈ Icc (crossing p) p.c,
    r ≤ (1-p.B)+(p.L-2)*w-9/2*(sel p.A p.D (w-crossing p)) ∧
    r ≤ 1/20+3/2*(1-p.B)+(3/2*p.L-5/2)*w-9/2*(sel p.A p.D (w-crossing p)) ∧
    r ≤ (1-p.B)+(p.L-1)*w-4*(sel p.A p.D (w-crossing p)) ∧
    r ≤ 1/3-2*w-3*(sel p.A p.D (w-crossing p))

namespace Gates
variable {p : Params} {q : ℝ → ℝ} {F : ℝ → WeightedFamily} (h : Gates p q F)
include h
theorem L0_pos : 0 < p.L0 := by linarith [h.face.one_lt_L,h.face.L_lt]
theorem cut_unit (w : ℝ) : q w ∈ Icc (0:ℝ) 1 := ⟨(h.cut_mem w).1,by linarith [(h.cut_mem w).2]⟩
theorem crossing_nonneg : 0 ≤ crossing p := h.face.cross_nonneg

theorem crossing_cap : crossing p < p.c0 := by
  obtain ⟨r,hr,hcap⟩ := h.cap
  have hc := hcap (crossing p) ⟨le_rfl,by linarith [h.width_pos]⟩
  simp only [sub_self,sel_zero,sub_zero] at hc
  linarith

theorem ledger {ε : ℝ} (hε : 0 < ε) :
    ∃ z : ℝ × ℝ × ℝ, LedgerAt (data p q F h.L0_pos h.cut_unit) ε z.1 z.2.1 z.2.2 := by
  have hD := h.D_nonneg
  obtain ⟨rH,hrH,hHnom⟩ := h.height
  obtain ⟨rC,hrC,hCnom⟩ := h.cap
  obtain ⟨rJ,hrJ,hJnom⟩ := h.high
  let m := min rJ rH
  have hm : 0 < m := lt_min hrJ hrH
  have hmJ : m ≤ rJ := min_le_left _ _
  have hmH : m ≤ rH := min_le_right _ _
  refine ⟨(ε/16,m/12,min (m/4) (min rC (min 1 (min (p.L0*ε/24) (ε/32))))), ?_⟩
  refine ⟨by positivity, ?_,by positivity,
    lt_min (by positivity) (lt_min hrC (lt_min one_pos (lt_min (by positivity [h.L0_pos]) (by positivity)))),?_⟩
  · change ε/16 ≤ ε/(16*(3/4))
    linarith
  intro mesh hm0 hm1 tl htl htlL g hfloor
  have ht1 : tl ≤ m/4 := htlL.trans (min_le_left _ _)
  have ht2 : tl ≤ rC := htlL.trans ((min_le_right _ _).trans (min_le_left _ _))
  have ht3 : tl ≤ 1 := htlL.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have ht4 : tl ≤ p.L0*ε/24 := htlL.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hS := g.hS
  have hroot := g.hroot
  have hsel := g.hsel
  have hs := g.hs
  simp only [data] at hS hroot hsel
  let v := max 0 (g.w-crossing p)
  let W := crossing p+v
  have hv0 : 0 ≤ v := le_max_left _ _
  have hv1 : v ≤ p.c-crossing p := by
    apply max_le (by linarith [h.width_pos])
    dsimp [SideGeometry.w]
    linarith [g.hf.1]
  have hW : W ∈ Icc (crossing p) p.c := ⟨by dsimp [W]; linarith,by dsimp [W]; linarith⟩
  have hWS : W ≤ g.S := by
    dsimp [W,v,SideGeometry.w]
    rw [add_max]
    apply max_le <;> linarith [g.hf.1]
  have hwv : g.S-g.f-crossing p ≤ v := le_max_right _ _
  have hu0 : sel p.A p.D v ≤ g.u := hsel.1
  have hu1 : g.u ≤ sel p.A p.D v+mesh := hsel.2
  have hu0p : 0 ≤ sel p.A p.D v := div_nonneg (mul_nonneg h.A_pos.le hv0) (by positivity)
  have hPC : g.PC ≤ p.B-p.L*W+tl := by
    have hp := mul_le_mul_of_nonneg_left hWS (by linarith [h.face.one_lt_L] : 0 ≤ p.L)
    linarith [g.hf.2]
  have hslot : g.s ≤ W-g.u := by
    have hw : g.w ≤ W := by dsimp [W,v]; linarith [le_max_right (0:ℝ) (g.w-crossing p)]
    linarith [g.hs.2]
  have hHL : (9/10:ℝ) ≤ g.H := by
    have hn := hHnom W hW
    have he : W-crossing p=v := by dsimp [W]; ring
    rw [he] at hn
    change (9/10:ℝ) ≤ 1+g.t-6*g.u
    linarith [g.ht.1]
  have hHU : g.H ≤ 3 := by change 1+g.t-6*g.u ≤ 3; linarith [g.ht.2]
  have hcapParent : g.s-p.c0*g.H ≤ 0 := by
    have hc := hCnom W hW
    have he : W-crossing p=v := by dsimp [W]; ring
    rw [he] at hc
    have haux := ds_cap_aux h.face.c₀_lt (by linarith [h.crossing_cap,h.crossing_nonneg] : 0 ≤ p.c0)
      g.hs.2 hwv hu0 g.ht.1 htl ht2 hc
    exact haux
  refine ⟨hHL,hHU,?_⟩
  have hWmax : W=max (crossing p) g.w := by
    dsimp [W,v]
    rw [add_max]
    rw [add_zero,show crossing p+(g.w-crossing p)=g.w by ring]
  change max (q (max (crossing p) g.w)*deletionNeed p.B0 p.L0 p.c0 g.PC g.s g.H)
    ((F (max (crossing p) g.w)).high g.PC g.s g.H) ≤ g.u+ε/16
  rw [← hWmax]
  apply max_le
  · have hdef : g.PC+p.L0*g.s-p.B0*g.H ≤
        (p.L0-p.L)*v+(6*p.B0-p.L0)*g.u+(p.B0*tl+tl) := by
      change g.PC+p.L0*g.s-p.B0*(1+g.t-6*g.u) ≤ _
      exact ds_defect_aux h.L0_pos.le (by linarith [h.face.one_lt_L])
        (by linarith [h.face.L_lt]) h.B0_pos.le h.face.cross_mul
        g.hf.1 g.hf.2 hroot g.hs.2 hwv g.ht.1
    have hC0 : 0 ≤ p.L0*(sel p.A p.D v)-q W*((p.L0-p.L)*v+(6*p.B0-p.L0)*(sel p.A p.D v)) := by
      have hh := h.low_payment W hW
      have he : W-crossing p=v := by dsimp [W]; ring
      simpa only [he] using hh
    have hqd := AdaptiveLedger.low_aux (h.cut_mem W).1 (h.cut_mem W).2 h.face.B₀_lt h.L0_pos.le hu0p hu0
      hdef hC0 (h.low_overshoot W hW) htl ht4
    have hn := deletionNeed_le_defect (B₀:=p.B0) (L₀:=p.L0) (P:=g.PC) hcapParent
    have hd := mul_le_mul_of_nonneg_left hn (h.cut_unit W).1
    have hzero : 0 ≤ g.u+ε/16 := by linarith
    have hdiv : q W*max 0 ((g.PC+p.L0*g.s-p.B0*g.H)/p.L0) ≤ g.u+ε/16 := by
      rw [mul_max_of_nonneg _ _ (h.cut_unit W).1,mul_zero]
      apply max_le hzero
      rw [← mul_div_assoc,div_le_iff₀ h.L0_pos]
      linarith
    exact hd.trans hdiv
  · have hnom := hJnom W hW
    have he : W-crossing p=v := by dsimp [W]; ring
    rw [he] at hnom
    have hh := weighted_high_paid hPC hslot (show g.H=1+g.t-6*g.u from rfl)
      g.ht.1 htl hu0 hu1 hnom (by linarith : 5*mesh+2*tl ≤ rJ)
    linarith

theorem stepGates : StepGates (data p q F h.L0_pos h.cut_unit) where
  face := ⟨h.face.B_le,h.face.B₀_lt,h.face.L_lt,h.face.one_lt_L,(by change 0 < p.c; linarith [h.width_pos,h.crossing_nonneg]),h.face.c_lt,h.face.c₀_lt⟩
  kappa := rfl
  crossing := ⟨h.crossing_nonneg,h.face.cross_mul.le,fun _ => h.crossing_cap.le⟩
  envelope := by norm_num [data]
  sel_spec := by
    have hD := h.D_nonneg
    intro ε hε
    constructor
    · intro x hx y hy hxy
      have hvx : 0 ≤ max 0 (x-crossing p) := le_max_left _ _
      have hvy : 0 ≤ max 0 (y-crossing p) := le_max_left _ _
      have hvs : max 0 (x-crossing p) ≤ max 0 (y-crossing p) :=
        max_le_max le_rfl (sub_le_sub_right hxy _)
      change sel p.A p.D _ ≤ sel p.A p.D _
      unfold sel
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith [h.A_pos]
    · intro w hw hwc
      change 0 ≤ sel p.A p.D (max 0 (w-crossing p)) ∧ sel p.A p.D (max 0 (w-crossing p)) ≤ w
      have hmax : max 0 (w-crossing p) ≤ w := max_le hw (by linarith [h.crossing_nonneg])
      have hmax0 : 0 ≤ max 0 (w-crossing p) := le_max_left _ _
      have hD := h.D_nonneg
      unfold sel
      constructor
      · exact div_nonneg (mul_nonneg h.A_pos.le hmax0) (by positivity)
      · apply (div_le_iff₀ (by positivity)).2
        nlinarith [mul_nonneg hD hmax0,h.A_lt]
  ledger := fun _ hε => h.ledger hε
  reference := by
    obtain ⟨r,hr,href⟩ := h.reference
    refine ⟨r,hr,?_⟩
    intro ε hε w hw hwc
    change crossing p ≤ w at hw
    change w ≤ p.c at hwc
    have hh := href w ⟨hw,hwc⟩
    simpa only [data,max_eq_right (sub_nonneg.mpr hw)] using hh

/-- One genuine source step, with the actual weighted packed supplier
supplied separately. Scalar gates cannot stand in for that supplier. -/
theorem source_step
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hp : QRH.Record1252270103Source.GlobalSource p.B0 p.L0 p.c0)
    (hleaf : PricedPackedSource (data p q F h.L0_pos h.cut_unit).price (9/10) 4 4) :
    QRH.Record1252270103Source.GlobalSource p.B p.L p.c := by
  let D := data p q F h.L0_pos h.cut_unit
  let G : StepGates D := h.stepGates
  have hI := Assembly.step_inputs_of_provider D G 4 (fun _ hl =>
    Second.Provider.contrary_raw_side_provider G 4 le_rfl hl (Second.ProviderDiag.diag_supply G))
  exact cubefree_step D G 4 hI hβ hp (by simpa only [D,data,show (3:ℝ)+1=4 by norm_num] using hleaf)

end Gates
end
end Qrh.JointDetector.RepeatedMarks.CurvedSourceStep
