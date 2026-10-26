/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109.Bernstein
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section
structure Cell where
  B : ℝ
  L : ℝ
  q : ℝ
  lo : ℝ
  hi : ℝ
  plainLo : ℝ
  plainHi : ℝ
  priorB : ℝ
  priorL : ℝ
  priorLo : ℝ
  priorHi : ℝ
  priorPlainLo : ℝ
  priorPlainHi : ℝ
  cut : ℝ
  tinyRadius : ℝ

def incumbent : ℝ := 37483/50000
def K : ℝ := 6*incumbent
def mesh : ℝ := 1/1000000000
def pad : ℝ := 1/10000000000
def lowFee : ℝ := 1/100000000
def highFee : ℝ := 1/10000000
def omega : ℝ := 51/100
def Pmix (c : Cell) : ℝ := (1-omega)/K+omega*c.priorB/c.priorL
def Qmix (c : Cell) : ℝ := (1-omega)/K+omega/c.priorL
def scheduleDenominator (c : Cell) : ℝ := 1-6*c.q*Pmix c
def plainCap (c : Cell) (b : ℝ) : ℝ := c.B-c.L*(b-mesh)
def amplifier (c : Cell) (b : ℝ) : ℝ :=
  (c.q*(Qmix c*plainCap c b+b-Pmix c)+lowFee)/scheduleDenominator c
def nominalRadius (c : Cell) (b : ℝ) : ℝ := 1-6*amplifier c b
def retainedWidth (b : ℝ) : ℝ := b-mesh-pad
def totalCap (c : Cell) (b : ℝ) : ℝ := plainCap c b+b
def highRadius (c : Cell) (b : ℝ) : ℝ := nominalRadius c b-pad
def radiusLo (c : Cell) (b : ℝ) : ℝ := nominalRadius c b-c.cut-pad
def radiusHi (c : Cell) (b : ℝ) : ℝ := nominalRadius c b+5/4*c.cut+pad
def naturalDelta (c : Cell) (b : ℝ) : ℝ :=
 c.q/K*(plainCap c b+K*b-nominalRadius c b)-amplifier c b
def bufferedDelta (c : Cell) (b : ℝ) : ℝ := naturalDelta c b+c.q/K*pad+pad
def rawGain (c : Cell) (b : ℝ) : ℝ :=
 amplifier c b-c.q*(b+(plainCap c b-c.priorB*nominalRadius c b)/c.priorL)
def partner (c : Cell) (b : ℝ) : ℝ := max 0 (bufferedDelta c b)
def d (ν : ℝ) : ℝ := 5-2*ν
def aa (ν : ℝ) : ℝ := 115-54*ν
def cc (ν : ℝ) : ℝ := 185-138*ν
def w (ν : ℝ) : ℝ := 5-6*ν
def rr (ν : ℝ) : ℝ := d ν-10/3*ν
def rho (ν : ℝ) : ℝ := 1-10*ν/(3*d ν)
def gamma (c : Cell) : ℝ := c.q+1/4-rho c.q
def core (c : Cell) (b ν : ℝ) : ℝ :=
 d ν*(1-ν*totalCap c b-5*amplifier c b)-rr ν*nominalRadius c b

/-- Cleared ordinary HIGH channels, including the two additional base/RAW channels. -/
def regular (T a S F ν : ℝ) (j : ℕ) : ℝ :=
 let H := d ν*(1-ν*T-5*a)-rr ν*(1-6*a)
 match j with
 | 0 => H*aa ν*cc ν+(ν-3/19)*S*d ν*aa ν*cc ν-highFee*d ν*aa ν*cc ν
 | 1 => H*aa ν*cc ν+(ν*d ν-4*rr ν+5/4*d ν)*S*aa ν*cc ν-highFee*d ν*aa ν*cc ν
 | 2 => H*aa ν*cc ν+ν*w ν*S*aa ν*cc ν-highFee*d ν*aa ν*cc ν
 | 3 => H*aa ν*cc ν+14*ν*w ν*S*d ν*cc ν+2/3*ν*(w ν)^2*F*cc ν-highFee*d ν*aa ν*cc ν
 | 4 => H*aa ν*cc ν+16/3*ν*(w ν)^2*F*aa ν-highFee*d ν*aa ν*cc ν
 | _ => 0

def exceptional (T a F b tiny Γ fee ν : ℝ) (j : ℕ) : ℝ :=
 let H := d ν*(1-ν*T-5*a)-rr ν*(1-6*a)
 let C := (1-ν)*d ν*b+(highFee+fee)*d ν
 match j with
 | 0 => H+(ν-3/19)*d ν*F/2-C
 | 1 => H+(ν*d ν-4*rr ν+5/4*d ν)*F/2-C
 | 2 => H+(rr ν-d ν/6)*F-C
 | 3 => H+(ν-3/19)*d ν*(F-tiny)/2-(d ν-rr ν)*tiny-C
 | 4 => H+(ν*d ν-4*rr ν+5/4*d ν)*(F-tiny)/2-(d ν-rr ν)*tiny-C
 | 5 => H+Γ*d ν*F/2-C
 | 6 => H+(rr ν-d ν/6)*F-C
 | 7 => H+Γ*d ν*(F-tiny)/2-(d ν-rr ν)*tiny-C
 | _ => 0

def highRegular (c : Cell) (j : ℕ) (b ν : ℝ) : ℝ :=
 regular (totalCap c b) (amplifier c b) (retainedWidth b) (highRadius c b) ν j

def highExceptional (c : Cell) (j : ℕ) (b ν : ℝ) : ℝ :=
 exceptional (totalCap c b) (amplifier c b) (highRadius c b) b c.tinyRadius (gamma c) (partner c b) ν j

def highBranch (c : Cell) (j : ℕ) (paid : Bool) (b ν : ℝ) : ℝ :=
 exceptional (totalCap c b) (amplifier c b) (highRadius c b) b c.tinyRadius (gamma c)
   (if paid then bufferedDelta c b else 0) ν j

/-- Each radius alternative in the nine padded R21 inequalities. -/
def domainBranch (c : Cell) (j : ℕ) (upper : Bool) (b : ℝ) : ℝ :=
 let Q := if upper then radiusHi c b else radiusLo c b
 let t := plainCap c b
 let F := nominalRadius c b
 (match j with
 | 0 => c.q/K*c.cut-3*bufferedDelta c b
 | 1 => (c.priorB-c.priorL*c.priorLo)*Q-t
 | 2 => t-c.cut-(c.priorB-c.priorL*c.priorHi)*Q
 | 3 => t+c.priorL*b-c.priorB*radiusHi c b-c.priorL*c.cut
 | 4 => c.priorPlainHi*radiusLo c b-c.plainHi
 | 5 => (1-K*c.priorLo)*Q-t
 | 6 => (1-c.priorPlainLo-K*c.priorB/c.priorL)*Q+K/c.priorL*(t-c.cut)-c.plainHi
 | 7 => t+K*b-F-c.cut
 | 8 => (1/2-K*c.priorHi)*Q-1/4
 | _ => 0)-lowFee

def ordinary (c : Cell) (j : ℕ) (b : ℝ) : ℝ :=
 match j with
 | 0 => amplifier c b
 | 1 => 1/75-amplifier c b
 | 2 => radiusLo c b
 | 3 => retainedWidth b
 | 4 => highRadius c b-2*retainedWidth b
 | 5 => lowFee-c.q*Pmix c*pad-pad
 | _ => 0

def complementary (c : Cell) (j : ℕ) (b : ℝ) : ℝ :=
 let a := amplifier c b
 let T := totalCap c b
 let DE := plainCap c b+9/2*b-1
 match j with
 | 0 => a
 | 1 => 1-T-5*a
 | 2 => 1-T-9*a
 | 3 => 49/50-T-4*a
 | 4 => 49/50-T-9/2*a
 | 5 => 1-1/4-1/2-K*b
 | 6 => 1/4-7*a
 | 7 => a/2-DE/6
 | 8 => 9/2*a-DE/6
 | 9 => 11/2*a-DE/6
 | 10 => a
 | 11 => 6*a
 | 12 => 7*a
 | _ => 0

def complementBranch (c : Cell) (j : ℕ) (paid : Bool) (b : ℝ) : ℝ :=
 complementary c j b-(if paid then bufferedDelta c b else 0)-highFee

def complementReserve (c : Cell) (j : ℕ) (b : ℝ) : ℝ :=
 complementary c j b-partner c b-highFee

theorem highExceptional_pos_of_branches {c : Cell} {j : ℕ} {b ν : ℝ}
 (h0 : 0 < highBranch c j false b ν) (h1 : 0 < highBranch c j true b ν) :
 0 < highExceptional c j b ν := by
 by_cases h : 0 ≤ bufferedDelta c b
 · simpa [highExceptional, highBranch, partner, max_eq_right h] using h1
 · simpa [highExceptional, highBranch, partner, max_eq_left (le_of_not_ge h)] using h0

theorem complementReserve_pos_of_branches {c : Cell} {j : ℕ} {b : ℝ}
 (h0 : 0 < complementBranch c j false b) (h1 : 0 < complementBranch c j true b) :
 0 < complementReserve c j b := by
 by_cases h : 0 ≤ bufferedDelta c b
 · simpa [complementReserve, complementBranch, partner, max_eq_right h] using h1
 · simpa [complementReserve, complementBranch, partner, max_eq_left (le_of_not_ge h)] using h0
end
end Record12518109Admission
