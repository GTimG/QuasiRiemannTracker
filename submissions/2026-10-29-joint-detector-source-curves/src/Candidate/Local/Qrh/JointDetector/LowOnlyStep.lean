/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.LowOnlySupplier
import Candidate.Local.Qrh.JointDetector.NativeDirectSource

/-! Constant-intercept source transfer from an already proved global Hecke ceiling. -/
namespace Qrh.JointDetector.LowOnlyStep
noncomputable section
set_option autoImplicit false
open Set OAI.SevenEighths
open QRH.SilDensitySplit.CubeFree QRH.Record1252270103Source

structure Params where
  B : ℝ
  L₀ : ℝ
  c₀ : ℝ
  L : ℝ
  c : ℝ
  q : ℝ
  A : ℝ

def data (p : Params) (hL : 0 < p.L₀) (hq : 0 ≤ p.q) : StepData where
  B₀ := p.B
  L₀ := p.L₀
  c₀ := p.c₀
  B := p.B
  L := p.L
  c := p.c
  κ := 3/4
  s₀ := 0
  Hmin := (1-6*p.A*p.c)/2
  Hmax := 3
  sel := fun _ w => p.A*w
  price := parentPrice p.q p.B p.L₀ p.c₀ hq hL

/-- Finite scalar obligations of a LOW-only step. Both zero-width and terminal
width reference reserves are retained; no division by marked width is used. -/
structure Gates (p : Params) : Prop where
  B_pos : 0 < p.B
  B_lt : p.B < 1
  L_lt : p.L < p.L₀
  L_one : 1 < p.L
  c_pos : 0 < p.c
  c_lt : p.c < 1/6
  c₀_pos : 0 < p.c₀
  c₀_lt : p.c₀ < 1/6
  A_pos : 0 < p.A
  A_lt : p.A < 1
  q_mem : p.q ∈ Icc (1/50:ℝ) (3/4)
  envelope : 0 < 1-6*p.A*p.c
  cap : 0 < p.c₀*(1-6*p.A*p.c)-(1-p.A)*p.c
  payment : p.q*(p.L₀-p.L+(6*p.B-p.L₀)*p.A) ≤ p.L₀*p.A
  overshoot : p.q*(6*p.B-p.L₀) ≤ p.L₀
  principal : 0 < (1-p.B)+(p.L-2-9/2*p.A)*p.c
  second : 0 < 1/20+3/2*(1-p.B)+(3/2*p.L-5/2-9/2*p.A)*p.c
  diagonal : 0 < (1-p.B)+(p.L-1-4*p.A)*p.c
  reference : 0 < 1/3-(2+3*p.A)*p.c

namespace Gates
variable {p : Params} (G : Gates p)
include G
theorem L₀_pos : 0 < p.L₀ := by linarith [G.L_lt, G.L_one]
theorem q_nonneg : 0 ≤ p.q := by linarith [G.q_mem.1]

/-- Nonnegative nominal payment and overshoot suffice, including at width zero. -/
theorem payment_aux {w u tl ε : ℝ} (hw : 0 ≤ w) (hu : p.A*w ≤ u)
    (htl : 0 ≤ tl) (htlε : tl ≤ p.L₀*ε/24) :
    p.q*(((p.L₀-p.L)*w+(6*p.B-p.L₀)*u+(p.B*tl+tl))/p.L₀) ≤ u+ε/16 := by
  have hL := G.L₀_pos
  have hq := G.q_nonneg
  have hB := G.B_pos
  have heq : p.q*(((p.L₀-p.L)*w+(6*p.B-p.L₀)*u+(p.B*tl+tl))/p.L₀) =
      u-((p.L₀*p.A-p.q*(p.L₀-p.L+(6*p.B-p.L₀)*p.A))/p.L₀)*w
      -((p.L₀-p.q*(6*p.B-p.L₀))/p.L₀)*(u-p.A*w)
      +p.q*((p.B*tl+tl)/p.L₀) := by field_simp; ring
  rw [heq]
  have h1 : 0 ≤ ((p.L₀*p.A-p.q*(p.L₀-p.L+(6*p.B-p.L₀)*p.A))/p.L₀)*w :=
    mul_nonneg (div_nonneg (by linarith [G.payment]) hL.le) hw
  have h2 : 0 ≤ ((p.L₀-p.q*(6*p.B-p.L₀))/p.L₀)*(u-p.A*w) :=
    mul_nonneg (div_nonneg (by linarith [G.overshoot]) hL.le) (by linarith)
  have herr : (p.B*tl+tl)/p.L₀ ≤ ε/12 := by
    rw [div_le_iff₀ hL]
    nlinarith [G.B_lt, mul_nonneg (show 0 ≤ 1-p.B by linarith [G.B_lt]) htl]
  have heps : 0 ≤ ε/12 := (div_nonneg (by positivity : 0 ≤ p.B*tl+tl) hL.le).trans herr
  have := mul_le_mul G.q_mem.2 herr (div_nonneg (by positivity : 0 ≤ p.B*tl+tl) hL.le)
    (by norm_num : (0:ℝ) ≤ 3/4)
  linarith

theorem stepGates : StepGates (data p G.L₀_pos G.q_nonneg) where
  face := ⟨le_rfl, G.B_lt, G.L_lt, G.L_one, G.c_pos, G.c_lt, G.c₀_lt⟩
  kappa := rfl
  crossing := by simp [data]
  envelope := by
    change 0 < (1-6*p.A*p.c)/2 ∧ (1-6*p.A*p.c)/2 < 1 ∧ (3:ℝ) ≤ 3
    have := G.envelope
    have := mul_pos G.A_pos G.c_pos
    constructor
    · positivity
    constructor <;> nlinarith
  sel_spec := by
    intro ε hε
    refine ⟨fun x hx y hy hxy => mul_le_mul_of_nonneg_left hxy G.A_pos.le, ?_⟩
    intro w hw hwc
    change 0 ≤ p.A*w ∧ p.A*w ≤ w
    constructor
    · exact mul_nonneg G.A_pos.le hw
    · nlinarith [G.A_lt]
  ledger := by
    intro ε hε
    let R := p.c₀*(1-6*p.A*p.c)-(1-p.A)*p.c
    let H := 1-6*p.A*p.c
    refine ⟨(ε/16, min (H/24) (R/2),
      min (min (H/4) 1) (min (3*R) (p.L₀*ε/24))), ?_⟩
    refine ⟨by positivity, ?_, lt_min (by positivity [G.envelope]) (by positivity [G.cap]),
      lt_min (lt_min (by positivity [G.envelope]) one_pos)
        (lt_min (by positivity [G.cap]) (by positivity [G.L₀_pos])), ?_⟩
    · change ε/16 ≤ ε/(16*(3/4))
      linarith
    intro mesh hm hmL tl ht htL g hfloor
    have hm1 : mesh ≤ H/24 := hmL.trans (min_le_left _ _)
    have hm2 : mesh ≤ R/2 := hmL.trans (min_le_right _ _)
    have ht1 : tl ≤ H/4 := htL.trans ((min_le_left _ _).trans (min_le_left _ _))
    have ht2 : tl ≤ 1 := htL.trans ((min_le_left _ _).trans (min_le_right _ _))
    have ht3 : tl ≤ 3*R := htL.trans ((min_le_right _ _).trans (min_le_left _ _))
    have ht4 : tl ≤ p.L₀*ε/24 := htL.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hS := g.hS
    have hf := g.hf
    have hs := g.hs
    have hsel := g.hsel
    have hgt := g.ht
    have hroot := g.hroot
    change 0 ≤ g.S ∧ g.S ≤ p.c at hS
    change p.A*(g.S-g.f) ≤ g.u ∧ g.u ≤ p.A*(g.S-g.f)+mesh at hsel
    change g.PC+(g.cg-g.f)+p.L*g.S ≤ p.B+tl at hroot
    have hw : 0 ≤ g.w := (show 0 ≤ ε/16 by positivity).trans hfloor
    have hwc : g.w ≤ p.c := by change g.S-g.f ≤ p.c; linarith
    have hu0 : p.A*g.w ≤ g.u := hsel.1
    have hu1 : g.u ≤ p.A*g.w+mesh := hsel.2
    have hu : 0 ≤ g.u := (mul_nonneg G.A_pos.le hw).trans hu0
    have huc : g.u ≤ p.A*p.c+mesh := by
      have := mul_le_mul_of_nonneg_left hwc G.A_pos.le
      linarith
    refine ⟨?_, ?_, ?_⟩
    · change H/2 ≤ 1+g.t-6*g.u
      dsimp [H] at *
      linarith
    · change 1+g.t-6*g.u ≤ 3
      linarith
    change p.q*deletionNeed p.B p.L₀ p.c₀ g.PC g.s g.H ≤ g.u+ε/16
    have hcapH : g.s-p.c₀*g.H ≤ 0 := by
      change g.s-p.c₀*(1+g.t-6*g.u) ≤ 0
      refine native_cap_aux G.A_pos G.A_lt G.c₀_pos hwc hu0 hu1 g.hs.2 hgt.1 ?_
      have hh : p.c₀*(tl+6*mesh) ≤ (1/6)*(tl+6*mesh) :=
        mul_le_mul_of_nonneg_right G.c₀_lt.le (by positivity)
      dsimp [R] at *
      linarith
    have hneed := deletionNeed_le_defect (B₀:=p.B) (L₀:=p.L₀) (P:=g.PC) hcapH
    have hdef : g.PC+p.L₀*g.s-p.B*g.H ≤
        (p.L₀-p.L)*g.w+(6*p.B-p.L₀)*g.u+(p.B*tl+tl) := by
      change g.PC+p.L₀*g.s-p.B*(1+g.t-6*g.u) ≤ _
      exact native_defect_aux le_rfl G.B_pos.le (by linarith [G.L_one])
        G.L₀_pos.le hf.1 hf.2 rfl hroot g.hs.2 hgt.1
    have hkey := G.payment_aux hw hu0 ht ht4
    calc p.q*deletionNeed p.B p.L₀ p.c₀ g.PC g.s g.H
        ≤ p.q*max 0 ((g.PC+p.L₀*g.s-p.B*g.H)/p.L₀) :=
          mul_le_mul_of_nonneg_left hneed G.q_nonneg
      _ ≤ p.q*max 0 (((p.L₀-p.L)*g.w+(6*p.B-p.L₀)*g.u+(p.B*tl+tl))/p.L₀) := by
          apply mul_le_mul_of_nonneg_left _ G.q_nonneg
          exact max_le_max le_rfl (div_le_div_of_nonneg_right hdef G.L₀_pos.le)
      _ ≤ _ := by
          rw [mul_max_of_nonneg _ _ G.q_nonneg]
          exact max_le (by linarith) hkey
  reference := by
    let r := min (min (min (min (1-p.B)
      ((1-p.B)+(p.L-2-9/2*p.A)*p.c))
      (1/20+3/2*(1-p.B)+(3/2*p.L-5/2-9/2*p.A)*p.c))
      ((1-p.B)+(p.L-1-4*p.A)*p.c)) (1/3-(2+3*p.A)*p.c)
    have hr : 0 < r := lt_min (lt_min (lt_min (lt_min (by linarith [G.B_lt])
      G.principal) G.second) G.diagonal) G.reference
    have h1 : r ≤ 1-p.B := (min_le_left _ _).trans ((min_le_left _ _).trans
      ((min_le_left _ _).trans (min_le_left _ _)))
    have h2 : r ≤ (1-p.B)+(p.L-2-9/2*p.A)*p.c := (min_le_left _ _).trans
      ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
    have h3 : r ≤ 1/20+3/2*(1-p.B)+(3/2*p.L-5/2-9/2*p.A)*p.c :=
      (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
    have h4 : r ≤ (1-p.B)+(p.L-1-4*p.A)*p.c :=
      (min_le_left _ _).trans (min_le_right _ _)
    have h5 : r ≤ 1/3-(2+3*p.A)*p.c := min_le_right _ _
    refine ⟨r, hr, ?_⟩
    intro ε hε S hS hSc
    change 0 ≤ S at hS
    change S ≤ p.c at hSc
    simp only [data]
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_cases hcoef : 0 ≤ p.L-2-9/2*p.A
      · nlinarith [mul_nonneg hcoef hS]
      · have := mul_le_mul_of_nonpos_left hSc (le_of_not_ge hcoef)
        nlinarith
    · by_cases hcoef : 0 ≤ 3/2*p.L-5/2-9/2*p.A
      · nlinarith [mul_nonneg hcoef hS, G.B_lt]
      · have := mul_le_mul_of_nonpos_left hSc (le_of_not_ge hcoef)
        nlinarith
    · by_cases hcoef : 0 ≤ p.L-1-4*p.A
      · nlinarith [mul_nonneg hcoef hS]
      · have := mul_le_mul_of_nonpos_left hSc (le_of_not_ge hcoef)
        nlinarith
    · have := mul_le_mul_of_nonneg_left hSc (show 0 ≤ 2+3*p.A by linarith [G.A_pos])
      nlinarith

/-- One finite source update using only a preceding global Hecke ceiling. -/
theorem global_source (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hcut : 2*HeckeZeroSupremum.beta-1 < p.q)
    (hp : GlobalSource p.B p.L₀ p.c₀) : GlobalSource p.B p.L p.c := by
  let D := data p G.L₀_pos G.q_nonneg
  let g := G.stepGates
  have hleaf : PricedPackedSource D.price D.Hmin (D.Hmax+1) 4 := by
    exact LowOnlySupplier.priced_source p.B p.L₀ p.c₀ D.Hmin (D.Hmax+1) 4 p.q
      G.L₀_pos hβ ⟨G.B_pos, G.B_lt.le, G.c₀_pos⟩ g.envelope.1
      (by have := g.envelope; linarith) hp G.q_mem hcut
  have I : StepInputs D g 4 := Assembly.step_inputs_of_provider D g 4
    (fun _ hl => Second.Provider.contrary_raw_side_provider g 4 (by norm_num) hl
      (Second.ProviderDiag.diag_supply g))
  exact cubefree_step D g 4 I hβ hp hleaf

end Gates
end
end Qrh.JointDetector.LowOnlyStep

#print axioms Qrh.JointDetector.LowOnlyStep.Gates.global_source
