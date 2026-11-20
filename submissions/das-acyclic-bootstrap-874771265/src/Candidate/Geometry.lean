/- Copyright (c) 2026 Subhanjan Das. MIT; AI-assisted with OpenAI Codex.
Uses Lewko/Collet's admitted generic return interfaces (Apache-2.0).
Exact parameter instances for the two ordered ordinary-source returns. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage2.Return.TransportGeometry
set_option autoImplicit false
namespace Das.QRH.TrackerGeometry
noncomputable section
open QRH.LewkoStage2Return

def height : ℝ := 80008783 / 100000000

def thetaA : ℝ := 87477127 / 100000000
def ellA : ℝ := 11/3 - 4*thetaA
def xA : ℝ := 1+ellA-height
def yA : ℝ := height-2*ellA
@[instance_reducible] noncomputable def parametersA : Geometry.Parameters where
  theta := thetaA
  ell := ellA
  x := xA
  y := yA
  ell_pos := by norm_num [thetaA, ellA, xA, yA, height]
  sixth_lt_ell := by norm_num [thetaA, ellA, xA, yA, height]
  ell_lt_fifth := by norm_num [thetaA, ellA, xA, yA, height]
  ell_lt_x := by norm_num [thetaA, ellA, xA, yA, height]
  x_lt_y := by norm_num [thetaA, ellA, xA, yA, height]
  y_lt_half := by norm_num [thetaA, ellA, xA, yA, height]
  x_add_y := by norm_num [thetaA, ellA, xA, yA, height]
  dilation_gap := by norm_num [thetaA, ellA, xA, yA, height]
  tuple_margin_neg := by norm_num [thetaA, ellA, xA, yA, height]
  signal_boundary := by norm_num [thetaA, ellA, xA, yA, height]

@[instance_reducible] noncomputable def boundsA : @Geometry.Bounds parametersA := by
  refine @Geometry.Bounds.mk parametersA ?_ ?_ ?_ ?_ ?_ ?_
  · change (874/1000:ℝ)<thetaA ∧ thetaA<7/8
    norm_num [thetaA,ellA,xA,yA,height]
  · change (793/1000:ℝ)<1+ellA-xA ∧ 1+ellA-xA<802/1000
    norm_num [thetaA,ellA,xA,yA,height]
  · change (458/1000:ℝ)<yA ∧ yA<466/1000
    norm_num [thetaA,ellA,xA,yA,height]
  · change (1672/10000:ℝ)<ellA ∧ ellA<1677/10000
    norm_num [thetaA,ellA,xA,yA,height]
  · change (7/100:ℝ)<yA/2-(1+ellA-xA)*(17/50-1/6)-1/50
    norm_num [thetaA,ellA,xA,yA,height]
  · change (4/25:ℝ)*xA-3/20-51/100*yA+67/100*(1+ellA-xA+1/10000000000)-3/20*ellA ≤ thetaA+(-(4+yA-xA)/6)-1/200
    norm_num [thetaA,ellA,xA,yA,height]


def thetaB : ℝ := 174954253 / 200000000
def ellB : ℝ := 11/3 - 4*thetaB
def xB : ℝ := 1+ellB-height
def yB : ℝ := height-2*ellB
@[instance_reducible] noncomputable def parametersB : Geometry.Parameters where
  theta := thetaB
  ell := ellB
  x := xB
  y := yB
  ell_pos := by norm_num [thetaB, ellB, xB, yB, height]
  sixth_lt_ell := by norm_num [thetaB, ellB, xB, yB, height]
  ell_lt_fifth := by norm_num [thetaB, ellB, xB, yB, height]
  ell_lt_x := by norm_num [thetaB, ellB, xB, yB, height]
  x_lt_y := by norm_num [thetaB, ellB, xB, yB, height]
  y_lt_half := by norm_num [thetaB, ellB, xB, yB, height]
  x_add_y := by norm_num [thetaB, ellB, xB, yB, height]
  dilation_gap := by norm_num [thetaB, ellB, xB, yB, height]
  tuple_margin_neg := by norm_num [thetaB, ellB, xB, yB, height]
  signal_boundary := by norm_num [thetaB, ellB, xB, yB, height]

@[instance_reducible] noncomputable def boundsB : @Geometry.Bounds parametersB := by
  refine @Geometry.Bounds.mk parametersB ?_ ?_ ?_ ?_ ?_ ?_
  · change (874/1000:ℝ)<thetaB ∧ thetaB<7/8
    norm_num [thetaB,ellB,xB,yB,height]
  · change (793/1000:ℝ)<1+ellB-xB ∧ 1+ellB-xB<802/1000
    norm_num [thetaB,ellB,xB,yB,height]
  · change (458/1000:ℝ)<yB ∧ yB<466/1000
    norm_num [thetaB,ellB,xB,yB,height]
  · change (1672/10000:ℝ)<ellB ∧ ellB<1677/10000
    norm_num [thetaB,ellB,xB,yB,height]
  · change (7/100:ℝ)<yB/2-(1+ellB-xB)*(17/50-1/6)-1/50
    norm_num [thetaB,ellB,xB,yB,height]
  · change (4/25:ℝ)*xB-3/20-51/100*yB+67/100*(1+ellB-xB+1/10000000000)-3/20*ellB ≤ thetaB+(-(4+yB-xB)/6)-1/200
    norm_num [thetaB,ellB,xB,yB,height]

end
end Das.QRH.TrackerGeometry

#print axioms Das.QRH.TrackerGeometry.boundsA
#print axioms Das.QRH.TrackerGeometry.boundsB
