/- Literal native common witnesses for the complete selected physical family.
Copyright (c)2026 Zhongpai Gao. Native source choices by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeCanonicalSelectedFamily
import Candidate.Research.RecursiveAffine.NativeCanonicalActual
import Candidate.Research.RecursiveAffine.NativeSelectedForest
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowPayment
import Candidate.Research.RecursiveAffine.NativeSelectedResidualIdentity

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 500000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153ActualColumn
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentSectorLocalization CenteredMomentSourceLiveColumn
open CenteredMomentDivisorAllocation CenteredMomentSecondCanonical CenteredMomentFirstDiscardedEnergy
open Cycle63Moment Cycle63InitialMass Cycle63FinalLow Cycle153RegionalLow Cycle153CanonicalLow
open CenteredMomentSecondCanonicalScalar
/-- A generic equality transport for the literal weighted column sum. -/
theorem unit_weighted_energy_transport {Row Divisor Point : Type*}[Fintype Row]
    (A outer : ℝ)(coefficient nextCoefficient : Row→ℝ)
    (Ds : Finset Divisor)(zs : Row→Finset Point)(energy : Row→Divisor→Point→ℝ)
    (hc : ∀r,coefficient r=nextCoefficient r)
    (h : A=outer*(∑r,coefficient r*(∑D∈Ds,∑z∈zs r,energy r D z))) :
    A=outer*(∑r,nextCoefficient r*(∑D∈Ds,∑z∈zs r,(1:ℝ)*energy r D z)) :=by
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [hc r]
  simp only [one_mul]

/-- Rewrite only the OLD scalar in an actual source bound, leaving its
returned term and its actual family untouched. -/
theorem replace_selected_old_cost {source outer oldCost canonicalOld returned : ℝ}
    (h : source≤outer*oldCost+returned)(heq : oldCost=canonicalOld) :
    source≤outer*canonicalOld+returned :=by
  simpa only [heq] using h

variable {alpha Label : Type} [Fintype alpha] [DecidableEq alpha] [Fintype Label]
variable (reflected second : Bool)(s : Input alpha)(R seed : Ideal O)
variable (Z Mrow amp xi reserve b firstHeight : ℝ)(budget : ℕ)(hZ : 1<Z)
variable (key : ℤ×(Fin 5→ℤ))(hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
variable (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z xi
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
local notation "Rows"=>NativeLowRows reflected s R seed Z Mrow amp xi reserve b firstHeight budget
  hZ key hz1 hz2 firstIndex
local notation "datum"=>fun r : Rows=>geometryLowSecondDatum reflected s R seed Z Mrow amp xi reserve b
  firstHeight budget hZ key (firstIndex r.val.1) hz1 hz2 r.val.2

variable (F : CanonicalSelectedFamily reflected second s R seed Z Mrow amp xi reserve b firstHeight budget hZ key hz1 hz2 firstIndex)
variable (hf1 : ∀l,frozenCoefficient (firstIndex l).2.val
  (geometryColumnIdeal reflected s R seed (Z^Mrow) Z xi
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val) R s.ν s.W s.P≠0)

/-- Exact actual-selected canonical source identity. The physical first
mass/volume ratio, first radius, and second normalizer are unchanged. -/
def CanonicalSelectedFamily.actualResidualIdentity
    (hE : ∀r : Rows,Supported (if second then (datum r).D else (datum r).C))
    (chi0 : Rows→RayFourExpansion.RayCharacter)(Q : Ideal O)(m : O)(mass : Label→ℝ)
    (ray : RayFourExpansion.RayCharacter)(sourceHeight : ℝ)(zs : Rows→Finset O)
    (Ds : Finset (Ideal O))(rawOuter : ℝ) :=
  actual_selected_raw_residual_shell_eq_columns s
    (F.chain reflected second s R seed Z Mrow amp xi reserve b firstHeight budget hZ key hz1 hz2 firstIndex)
    (F.geometry reflected second s R seed Z Mrow amp xi reserve b firstHeight budget hZ key hz1 hz2 firstIndex hf1)
    datum second
    (F.frame reflected second s R seed Z Mrow amp xi reserve b firstHeight budget hZ key hz1 hz2 firstIndex hf1)
    hE chi0 Q m (fun r=>mass r.val.1)
    (fun r=>volume (geometryLowFirstChild reflected s R seed (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key firstHeight (firstIndex r.val.1)))
    (fun _=>ray) (fun _=>sourceHeight) zs Ds rawOuter

/-- The canonical physical coefficient is literally the native weighted
selected-row coefficient, with the original first-source volume. -/
theorem CanonicalSelectedFamily.physicalCoefficient (mass : Label→ℝ)(r : Rows) :
    selectedPhysicalCoefficient datum (fun r : Rows=>mass r.val.1)
      (fun r : Rows=>volume (geometryLowFirstChild reflected s R seed (Z^Mrow) Z xi
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key firstHeight (firstIndex r.val.1))) r =
    mass r.val.1/volume (geometryLowFirstChild reflected s R seed (Z^Mrow) Z xi
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key firstHeight (firstIndex r.val.1))*
      firstMainRadius reflected (Z^Mrow) (volume s) Z xi (3*amp) reserve
        (geometryFirstLabel s R seed (Z^Mrow) Z xi
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex r.val.1).1.val)*
      normalizer
        (actualSecondSupportedLabel _ _ _ _ _ _ _ r.val.2
          (actual_main_low_selected_inactive reflected s R seed Z Mrow amp xi reserve b firstHeight budget
            hZ key hz1 hz2 firstIndex r)).1.1
        (actualSecondSupportedLabel _ _ _ _ _ _ _ r.val.2
          (actual_main_low_selected_inactive reflected s R seed Z Mrow amp xi reserve b firstHeight budget
            hZ key hz1 hz2 firstIndex r)).1.2
        (actualSecondSupportedLabel _ _ _ _ _ _ _ r.val.2
          (actual_main_low_selected_inactive reflected s R seed Z Mrow amp xi reserve b firstHeight budget
            hZ key hz1 hz2 firstIndex r)).2.val :=by
  rfl
/-- Exact canonical residual identity in the literal unit-weighted form
used by the actual selected source theorem. -/
def CanonicalSelectedFamily.actualUnitWeightedResidualIdentity
    (hE : ∀r : Rows,Supported (if second then (datum r).D else (datum r).C))
    (chi0 : Rows→RayFourExpansion.RayCharacter)(Q : Ideal O)(m : O)(mass : Label→ℝ)
    (ray : RayFourExpansion.RayCharacter)(sourceHeight : ℝ)(zs : Rows→Finset O)
    (Ds : Finset (Ideal O))(rawOuter : ℝ) :=
  unit_weighted_energy_transport _ (Z^rawOuter) _
    (fun r : Rows=>mass r.val.1/volume (geometryLowFirstChild reflected s R seed (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key firstHeight (firstIndex r.val.1))*
      firstMainRadius reflected (Z^Mrow) (volume s) Z xi (3*amp) reserve
        (geometryFirstLabel s R seed (Z^Mrow) Z xi
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex r.val.1).1.val)*
      normalizer
        (actualSecondSupportedLabel _ _ _ _ _ _ _ r.val.2
          (actual_main_low_selected_inactive reflected s R seed Z Mrow amp xi reserve b firstHeight budget
            hZ key hz1 hz2 firstIndex r)).1.1
        (actualSecondSupportedLabel _ _ _ _ _ _ _ r.val.2
          (actual_main_low_selected_inactive reflected s R seed Z Mrow amp xi reserve b firstHeight budget
            hZ key hz1 hz2 firstIndex r)).1.2
        (actualSecondSupportedLabel _ _ _ _ _ _ _ r.val.2
          (actual_main_low_selected_inactive reflected s R seed Z Mrow amp xi reserve b firstHeight budget
            hZ key hz1 hz2 firstIndex r)).2.val)
    Ds zs _
    (fun r=>CanonicalSelectedFamily.physicalCoefficient reflected s R seed Z Mrow amp xi reserve b
      firstHeight budget hZ key hz1 hz2 firstIndex mass r)
    (F.actualResidualIdentity reflected second s R seed Z Mrow amp xi reserve b firstHeight budget
      hZ key hz1 hz2 firstIndex hf1 hE chi0 Q m mass ray sourceHeight zs Ds rawOuter)

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.CanonicalSelectedFamily.actualResidualIdentity
#print axioms OAI.SevenEighths.Cycle153ActualColumn.CanonicalSelectedFamily.physicalCoefficient

#print axioms OAI.SevenEighths.Cycle153ActualColumn.CanonicalSelectedFamily.actualUnitWeightedResidualIdentity
