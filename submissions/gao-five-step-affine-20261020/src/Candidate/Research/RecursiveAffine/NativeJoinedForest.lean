/- Copyright (c) 2026 Hailey Collet; forest specialization (c) 2026 Zhongpai Gao.
Released under Apache 2.0. The normalization is the native joined-row proof. -/
import Candidate.Research.RecursiveAffine.ActualSourceWeight
import Candidate.Research.RecursiveAffine.ActualFamilyRebase
import Candidate.Cycle63.Physical.InitialMass.LowChildJoinedTotal

set_option autoImplicit false
set_option maxHeartbeats 450000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open Cycle63FinalCapacity CenteredMomentSectorLocalization Cycle153SourceReturn
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSecondPhysicalBlock

/-- Bind the actual first-row coefficient and own-second reciprocal norm
to a whole returned forest. The column estimate is the output of the
actual common/column source operator; the pay0 estimate is the native
first-child mass payment. Their native normalization constructs the
literal X0 edge weight. No returned-count estimate is assumed here. -/
theorem actual_joined_column_forest
    {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    {hH : RayOrthogonality.globalUnits M ≤ H}
    {Depth : Type} [Fintype Depth] {junction : Depth→ℝ} {Base : Depth→Type}
    {base : (d : Depth)→Character→Base d→Character}
    {eta : Character} {Bnorm Tz : ℝ} {root : O}
    (reflected second left : Bool) (first label : FirstSourceLabel)
    (Z Mrow A amp xi reserve eps unit common pad loss epsV normCap shellLoss
      slotLoss q deletion mesh mass childVolume radius Cg fixed physical oldExponent allowance
      columnEnergy : ℝ) (hZ : 1 < Z)
    (hC : Supported label.1.1) (hD : Supported label.1.2)
    (F : DepthReturnedFamily M H hH junction Base base eta Z Bnorm Tz root)
    (hCg : 0 ≤ Cg) (hfixed : 0 ≤ fixed) (hmass : 0 ≤ mass)
    (hvolume : 0 < childVolume) (hradius : 0 ≤ radius) (hphysical : 0 ≤ physical) :
    let ownNorm := ((if second then label.1.2 else label.1.1).absNorm : ℝ)
    let nominal := secondNominal unit Z amp (frequencyLoss Z 32 xi+reserve)
      (if reflected then first.1.2 else first.1.1)
      (if reflected then first.1.1 else first.1.2) label.1.1 label.1.2 label.2.val
    let oldEnergyExponent := nominal+amp+common
    let payExponent := lowGeometryExponent reflected Z A first+(common+pad)+(unit-Mrow)+epsV+normCap*shellLoss
    let coefficient := mass/childVolume*radius*normalizer label.1.1 label.1.2 label.2.val
    let pay0 := Z^(-amp)*(radius/childVolume)*
      (normalizer label.1.1 label.1.2 label.2.val*ownNorm^(shellLoss-1))*
      Z^(nominal+amp+common+pad)
    oldExponent ≤ oldEnergyExponent+allowance →
    pay0 ≤ Z^payExponent/ownNorm → mass ≤ physical*Z^loss →
    columnEnergy ≤ Cg*fixed*ownNorm^(shellLoss-1)*
      (Z^oldExponent+Z^(slotLoss+q*(deletion+mesh))*F.value)*Z^pad →
    coefficient*columnEnergy ≤
      Cg*fixed*(mass*Z^amp)*(pay0*Z^allowance)+
      Cg*fixed*physical*(Z^(loss+amp+epsV+normCap*shellLoss+pad+slotLoss+
        actualHighCoordinates reflected left second first label.1.1 label.1.2 label.2.val
          Z Mrow A amp xi reserve eps 0+q*(deletion+mesh))*F.value) := by
  intro ownNorm nominal oldEnergyExponent payExponent coefficient pay0 hOld hpay hmasscap hcolumn
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hnorm : 0 < ownNorm := second_norm_pos second hC hD
  have hnormal : 0 ≤ normalizer label.1.1 label.1.2 label.2.val :=
    (normalizer_pos _ _ hC _).le
  have hcoefficient : 0 ≤ coefficient :=
    mul_nonneg (mul_nonneg (div_nonneg hmass hvolume.le) hradius) hnormal
  have hpay0 : 0 ≤ pay0 := by
    dsimp only [pay0]
    exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hZ0.le _)
      (div_nonneg hradius hvolume.le))
      (mul_nonneg hnormal (Real.rpow_nonneg hnorm.le _))) (Real.rpow_nonneg hZ0.le _)
  have hid : coefficient*(Cg*fixed*ownNorm^(shellLoss-1)*Z^pad)*Z^oldEnergyExponent =
      Cg*fixed*(mass*Z^amp)*pay0 := by
    dsimp only [coefficient,pay0,oldEnergyExponent]
    have hpower : Z^(nominal+amp+common)*Z^pad = Z^(nominal+amp+common+pad) :=
      (Real.rpow_add hZ0 _ _).symm
    have hcancel : Z^amp*Z^(-amp) = (1:ℝ) := by
      rw [←Real.rpow_add hZ0]
      simp only [add_neg_cancel,Real.rpow_zero]
    simpa only [mul_one,one_mul] using
      (joined_identity (c:=mass/childVolume*radius*normalizer label.1.1 label.1.2 label.2.val)
        (mass:=mass) (vol:=childVolume) (Kf:=radius)
        (normal:=normalizer label.1.1 label.1.2 label.2.val) (Nn:=ownNorm^(shellLoss-1))
        (Cg:=Cg) (c2:=fixed) (dg:=1) (ctrl:=1) (Hh:=1) (Tt:=1) rfl rfl hpower hcancel)
  have hW := physical_low_return_weight_eq reflected second left first label
    Z Mrow A amp xi reserve eps unit common pad loss epsV normCap shellLoss slotLoss q deletion mesh hZ hC hD
  dsimp only at hW
  unfold physicalLowReturnWeight at hW
  have hK : 0 ≤ coefficient*(Cg*fixed*ownNorm^(shellLoss-1)*Z^pad) :=
    mul_nonneg hcoefficient (mul_nonneg (mul_nonneg (mul_nonneg hCg hfixed)
      (Real.rpow_nonneg hnorm.le _)) (Real.rpow_nonneg hZ0.le _))
  apply (mul_le_mul_of_nonneg_left hcolumn hcoefficient).trans
  exact joined_row_bound hZ hid hOld hK hpay0 hpay hmasscap hphysical
    (mul_nonneg hCg hfixed) hnorm rfl (F.value_nonneg hZ0.le)
    (Real.rpow_nonneg hZ0.le _) hW

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_joined_column_forest
