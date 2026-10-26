/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Source.GlobalFloor
set_option autoImplicit false
namespace QRH.Record12518109Source
noncomputable section
open Record12518109Admission

def firstFlip (v : Fin 8→ℝ) : Fin 8→ℝ :=
  ![v 1,v 0,v 2,v 3,v 5,v 4,v 7,v 6]

def globalNatural (c : Cell) (v : Fin 8→ℝ) : ℝ :=
  -(c.q/K)*min (v 0) (v 1)-globalB false v-globalSigma v
def globalRaw (c : Cell) (v : Fin 8→ℝ) : ℝ :=
  -2*v 3-globalB false v+v 4+v 6-globalSigma v-
    (c.q/c.priorL)*(v 0+c.priorB*(v 4-v 3-max (v 0-v 1) 0))
def globalLow (c : Cell) (w : ℝ) (v : Fin 8→ℝ) : ℝ :=
  (1-w)*globalNatural c v+w*globalRaw c v
def globalHighScaled (ν : ℝ) (v : Fin 8→ℝ) : ℝ :=
  (d ν-rr ν)*max (v 0-v 1) 0-(d ν+rr ν)*v 3-d ν*globalB false v+
    rr ν*v 4+d ν*v 6-d ν*globalSigma v-etaD ν*v 0
def globalHigh (ν : ℝ) (v : Fin 8→ℝ) : ℝ :=
  (1-rho ν)*max (v 0-v 1) 0-(1+rho ν)*v 3-globalB false v+
    rho ν*v 4+v 6-globalSigma v-ν*v 0

theorem globalSigma_flip (v : Fin 8→ℝ) : globalSigma (firstFlip v)=globalSigma v := by
  simp [globalSigma,globalB_false,globalB_true,firstFlip,firstLinear]
  ring

/-- The ordered LOW--LOW expression is the actual pair of common costs.
Only the global ideal-norm order is used. -/
theorem ordered_pair_identity (c : Cell) (v : Fin 8→ℝ) (hv : v 0≤v 1) :
    globalLow c (17/50) v+globalLow c (17/25) (firstFlip v)=globalOrdered c v := by
  have hm : min (v 0) (v 1)=v 0 := min_eq_left hv
  have hp : max (v 0-v 1) 0=0 := max_eq_right (sub_nonpos.mpr hv)
  have hn : max (v 1-v 0) 0=v 1-v 0 := max_eq_left (sub_nonneg.mpr hv)
  simp only [globalLow,globalNatural,globalRaw,globalSigma_flip]
  simp [globalOrdered,globalSigma,globalB_false,globalB_true,firstFlip,firstLinear,
    hm,hp,hn,min_comm (v 1) (v 0)]
  ring

theorem mixed_pair_identity (c : Cell) (ν : ℝ) (v : Fin 8→ℝ) :
    -d ν*globalLow c omega v-globalHighScaled ν (firstFlip v)=globalMixed c ν v := by
  simp only [globalLow,globalNatural,globalRaw,globalHighScaled,globalSigma_flip]
  simp [globalMixed,minMaxLinear,minMaxCone,globalSigma,globalB_false,globalB_true,
    firstFlip,firstLinear]
  ring

theorem paired_high_identity (c : Cell) (l r : ℝ) (v : Fin 8→ℝ) :
    -globalHigh l v-globalHigh r (firstFlip v)-gamma c*(v 0+v 1)=globalPaired c l r v := by
  simp only [globalHigh,globalSigma_flip]
  simp [globalPaired,minMaxLinear,minMaxCone,globalSigma,globalB_false,globalB_true,
    firstFlip,firstLinear]
  ring

theorem mixed_pair_payment (c : Cell) (ν : ℝ) (v : Fin 8→ℝ)
    (h : 0≤globalMixed c ν v) :
    d ν*globalLow c omega v+globalHighScaled ν (firstFlip v)≤0 := by
  rw [←mixed_pair_identity] at h
  linarith only [h]

theorem paired_high_payment (c : Cell) (l r : ℝ) (v : Fin 8→ℝ)
    (h : 0≤globalPaired c l r v) :
    globalHigh l v+globalHigh r (firstFlip v)≤-gamma c*(v 0+v 1) := by
  rw [←paired_high_identity] at h
  linarith only [h]

end
end QRH.Record12518109Source
#print axioms QRH.Record12518109Source.ordered_pair_identity
#print axioms QRH.Record12518109Source.mixed_pair_payment
#print axioms QRH.Record12518109Source.paired_high_payment
