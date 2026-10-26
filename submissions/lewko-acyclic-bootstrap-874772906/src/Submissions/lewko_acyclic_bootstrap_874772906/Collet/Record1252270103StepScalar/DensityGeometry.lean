/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103StepScalar.UniformMargins
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103StepScalar
noncomputable section
open Record1252270103Finite QRH.Record1252270103Graph

structure DensityDenominators (L ν : ℝ) : Prop where
  t_pos : 0<15-6*ν
  w_pos : 0<5-6*ν
  none_two : 0<115-54*ν
  none_three : 0<185-138*ν
  high_thirteen : 0<L*(15-6*ν)-10
  high_four : 0<10+3*(5-6*ν)
  high_twothree : 0<L*(10+3*(5-6*ν))-(10+2*(5-6*ν))

theorem density_denominators {L ν : ℝ} (hL : 1<L) (hν : ν≤3/4) :
    DensityDenominators L ν := by
  have ht : 0<15-6*ν := by linarith
  have hw : 0<5-6*ν := by linarith
  have hfour : 0<10+3*(5-6*ν) := by linarith
  have hp:=mul_pos (sub_pos.mpr hL) ht
  have hq:=mul_pos (sub_pos.mpr hL) hfour
  refine ⟨ht,hw,by linarith,by linarith,by nlinarith,hfour,by nlinarith⟩

theorem nf_density_denominators (n low : Source) (high : Option Source)
    (hv : SourceValid n low high) (h : Source) (hh : h∈high)
    {ν : ℝ} (hν : ν∈Set.Icc (n.q:ℝ) (3/4)) :
    DensityDenominators (h.L:ℝ) ν := by
  have hgood:=hv.2.2.2.2.2.2.2.2.2.2.2.1 h hh
  apply density_denominators _ hν.2
  exact_mod_cast hgood.2.2.1

theorem raw_factor_positive {K : ℚ} {n low : Source} {b : ℝ}
    (hg : RealGeometry K n low b) : 0<sourceFReal n low b := by
  dsimp [sourceFReal]
  linarith [hg.a_small]
end
end QRH.Record1252270103StepScalar
#print axioms QRH.Record1252270103StepScalar.density_denominators
#print axioms QRH.Record1252270103StepScalar.nf_density_denominators
#print axioms QRH.Record1252270103StepScalar.raw_factor_positive
