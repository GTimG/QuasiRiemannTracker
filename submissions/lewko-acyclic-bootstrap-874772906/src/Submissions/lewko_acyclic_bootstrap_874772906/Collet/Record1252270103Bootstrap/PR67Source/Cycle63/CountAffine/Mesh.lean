import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle25.Energy.Endpoint
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.LocalReserves
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The slot mesh of the detector affine moment, early in the import order.
Released under Apache 2.0. -/
/-! This repeats the formula of `Cycle63.FinalAssembly.geometryChosenMesh`, which is defined
after the final assembly in the import order; `Cycle63.CountAffine.Supply` proves the two equal. -/

namespace Cycle63.CountAffine
noncomputable section
open OAI.SevenEighths.CenteredMomentEnergyWidthRanges

def meshLossUnit (Mmin εaffine : ℝ) : ℝ :=
  min (εaffine/128) (min ((Cycle63.Arithmetic.lowReserve)*Mmin/128) (min (Mmin/128) (1/128)))

def meshComparison (Mmin Mmax ε : ℝ) : ℝ :=
  Cycle25.Energy.commonMesh (2*Mmax+1) 0 ((2*Mmax+1)+Mmin/100+1) ((ε/2)/(4*((2*Mmax+1)+2)))

def meshAnalytic (Mmin Mmax εaffine Mcap Bmask L : ℝ) : ℝ :=
  let μ := meshLossUnit Mmin εaffine
  min (meshComparison Mmin Mmax εaffine)
    (min (Cycle25.Energy.commonMesh Mcap Bmask L (μ/8))
      (min (μ/8) (Mmin*Cycle63.Arithmetic.amplifierFloor/4)))/2

def meshMarkedCap : ℝ :=
  min (fineMesh 2 0 1 Cycle63.Optimization.plainCapacityCost (min (Cycle63.Optimization.markedRate/4) (1/4)))
    Cycle63.Optimization.markedRate*(4/5*Cycle63.Optimization.coreFactor)/64

/-- The slot mesh that the second step of the two-level ledger admits at the affine loss `εaffine` of the first step
(`Cycle63InitialMass.twoLevelSlotMesh`). -/
def meshTwoLevel (εaffine : ℝ) : ℝ :=
  min (Cycle25.Energy.commonMesh (101/100) 28 1 (meshLossUnit 1 εaffine/8))
    (2/5*min (Cycle63.Optimization.lowReserveWeight/4)
      (min (Cycle25.Energy.commonMesh 2 (28+20) 1 (meshLossUnit 1 (1/10^10)/8))
        (min (Cycle25.Energy.commonMesh 2 28 1 (meshLossUnit 1 (1/10^10)/8))
          (Cycle25.Energy.commonMesh 1 20 1 (meshLossUnit 1 εaffine/8/(101/100)/2)))))

/-- The detector slot mesh at loss `ε`. -/
def detectorMesh (ε : ℝ) : ℝ :=
  min (min (min (meshAnalytic 1 1 (ε/4) 2 28 1) (meshComparison 1 1 (ε/2))) (meshTwoLevel (ε/4))) meshMarkedCap

theorem meshComparison_pos {Mmax ε : ℝ} (Mmin : ℝ) (hMmax : 0 ≤ Mmax) (hε : 0 < ε) :
    0 < meshComparison Mmin Mmax ε := by
  unfold meshComparison
  exact Cycle25.Energy.commonMesh_pos _ _ _ _ (by linarith) le_rfl (by positivity)

theorem detectorMesh_pos {ε : ℝ} (hε : 0 < ε) : 0 < detectorMesh ε := by
  have hfl := Cycle63.Arithmetic.amplifierFloor_pos
  have hμ : 0 < meshLossUnit 1 (ε/4) := by
    unfold meshLossUnit
    exact lt_min (by positivity) (lt_min (div_pos (mul_pos Cycle63.Arithmetic.lowReserve_pos one_pos)
      (by norm_num)) (lt_min (by norm_num) (by norm_num)))
  have h1 : 0 < meshAnalytic 1 1 (ε/4) 2 28 1 := by
    have hc := meshComparison_pos 1 (by norm_num : (0:ℝ) ≤ 1) (by positivity : 0 < ε/4)
    have ho := Cycle25.Energy.commonMesh_pos 2 28 1 (meshLossUnit 1 (ε/4)/8) (by norm_num)
      (by norm_num) (by positivity)
    unfold meshAnalytic
    have h3 : 0 < min (meshLossUnit 1 (ε/4)/8) (1*Cycle63.Arithmetic.amplifierFloor/4) :=
      lt_min (by positivity) (by positivity)
    have h4 := lt_min ho h3
    have h5 := lt_min hc h4
    positivity
  have h2 := meshComparison_pos 1 (by norm_num : (0:ℝ) ≤ 1) (by positivity : 0 < ε/2)
  have h3 : 0 < meshMarkedCap := by
    unfold meshMarkedCap
    have hr := Cycle63.Optimization.markedRate_pos
    have hf := fineMesh_pos 2 0 1 Cycle63.Optimization.plainCapacityCost (min (Cycle63.Optimization.markedRate/4) (1/4))
      (by norm_num [Cycle63.Optimization.plainCapacityCost]) le_rfl (by norm_num [Cycle63.Optimization.plainCapacityCost]) (lt_min (by positivity) (by norm_num))
    have := lt_min hf hr
    have hc : 0 < 4/5*Cycle63.Optimization.coreFactor := by linarith [Cycle63.Optimization.coreFactor_bounds.1]
    exact div_pos (mul_pos this hc) (by norm_num)
  have h4 : 0 < meshTwoLevel (ε/4) := by
    have hμ2 : 0 < meshLossUnit 1 (1/10^10) := by
      unfold meshLossUnit
      exact lt_min (by positivity) (lt_min (div_pos (mul_pos Cycle63.Arithmetic.lowReserve_pos one_pos)
        (by norm_num)) (lt_min (by norm_num) (by norm_num)))
    have hw : (0:ℝ) < Cycle63.Optimization.lowReserveWeight := by
      norm_num [Cycle63.Optimization.lowReserveWeight, Cycle63.Optimization.allowanceUnit]
    have e1 := Cycle25.Energy.commonMesh_pos (101/100) 28 1 (meshLossUnit 1 (ε/4)/8) (by norm_num) (by norm_num)
      (by positivity)
    have e2 := Cycle25.Energy.commonMesh_pos 2 (28+20) 1 (meshLossUnit 1 (1/10^10)/8) (by norm_num) (by norm_num)
      (by positivity)
    have e3 := Cycle25.Energy.commonMesh_pos 2 28 1 (meshLossUnit 1 (1/10^10)/8) (by norm_num) (by norm_num)
      (by positivity)
    have e4 := Cycle25.Energy.commonMesh_pos 1 20 1 (meshLossUnit 1 (ε/4)/8/(101/100)/2) (by norm_num) (by norm_num)
      (by positivity)
    unfold meshTwoLevel
    exact lt_min e1 (mul_pos (by norm_num) (lt_min (by positivity) (lt_min e2 (lt_min e3 e4))))
  exact lt_min (lt_min (lt_min h1 h2) h4) h3

end
end Cycle63.CountAffine

end Record1252270103Bootstrap.PR67
