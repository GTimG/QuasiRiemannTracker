/- Genuine absolute dyads and arithmetic licences for every ROOT selected row.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootAllRowKeyFacts
import Candidate.Research.RecursiveAffine.NativeGlobalDyadBox
import Candidate.Research.RecursiveAffine.ActualSourcePrimitiveSchedule
import Candidate.Cycle63.Physical.InitialMass.GeometryMainHighSourceCaps
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineLowPayment

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentFirstCanonicalFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonical CenteredMomentSectorLocalization
open Cycle153Reachable Cycle153JointCount Cycle153SourceSchedule Cycle153SourceUniform
open Cycle153.RegionalSchedule Cycle153ActualSourceGates
open CenteredMomentSourceLiveColumn CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyState
noncomputable local instance rootAllRowSourceLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger
attribute [local irreducible] nativeLowHistoryCode mainLowSelectedNonzeroRows

/-- One cutoff covers every actual source cardinal up to the ORIGINAL
budget. First height and every row, including zero/direct/OLD, remain
arbitrary. Native dyad membership and second source caps are derived,
not postulated. The real subsequent boxes can all be this one root box. -/
theorem eventual_actual_root_all_row_source_facts (budget : ℕ) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(hZ : 1<Z){Current : Type}[Fintype Current][DecidableEq Current]
      (reflected : Bool)(s : Input Current)(p : Profiles (1/4) (9/4))(Cs : ℝ)
      (caps : GeometryAffineLowSourceGates s p Cs Z)
      (R seed : Ideal O)(hseed : Squarefree seed)(amp firstHeight : ℝ)
      (hamp0 : 0≤amp)(hamp1 : amp≤1)(hcard : Fintype.card Current≤budget)
      (bin : ℤ×(Fin 5→ℤ)){Label : Type}[Fintype Label]
      (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^(1:ℝ)) Z (nativeMu/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
      (∀l,frozenCoefficient (firstIndex l).2.val (geometryColumnIdeal reflected s R seed
        (Z^(1:ℝ)) Z (nativeMu/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
        R s.ν s.W s.P≠0)→
    ∀(units : FirstSourceLabel→O),(∀l,IsUnit (units l))→
    ∀r : NativeLowRows reflected s R seed Z 1 amp (nativeMu/64) (nativeMu/8) (9/4) firstHeight
      (Fintype.card Current) hZ bin caps.zero₁ caps.zero₂ firstIndex,
      DecoratedFacts (fun _ : Unit=>(1:O)) (!reflected) (fun _=>units)
        Z 250000 (rootNativeDyadBox Z budget)
        ((),nativeLowHistoryCode reflected s R seed Z 1 amp (nativeMu/64) (nativeMu/8) (9/4)
          firstHeight (Fintype.card Current) hZ bin caps.zero₁ caps.zero₂ firstIndex r) :=by
  have hmu0:=div_pos nativeMu_pos (by norm_num : (0:ℝ)<8)
  have hmu1 : nativeMu/8≤1:=by norm_num [nativeMu,primitiveError]
  have hc:=eventual_actual_geometry_main_high_source_caps budget (9/4) (9/4) (nativeMu/8)
    (by norm_num) (by norm_num) hmu0 hmu1
  choose Cb hCb hboxNative using fun n : Fin (budget+1)=>
    eventual_actual_geometry_main_absolute_box n.val 4 (nativeMu/8)
      (9/4) (9/4) (nativeMu/64) 1 (by norm_num) hmu0 (by norm_num) (by norm_num)
      (div_nonneg nativeMu_pos.le (by norm_num)) (by nlinarith only [nativeMu_pos]) (by norm_num)
  filter_upwards [hc,Filter.eventually_all.mpr hboxNative,eventually_actual_source_small budget]
    with Z hcaps hb hs
  refine ⟨hcaps.1,?_⟩
  intro hZ Current _ _ reflected s p Cs caps R seed hseed amp firstHeight hamp0 hamp1 hcard bin
    Label _ firstIndex hf units hunits r
  have hsmall:=hs.2 1 (by norm_num)
  simp only [Real.rpow_one] at hsmall
  have hbLocal:=(hb ⟨Fintype.card Current,by omega⟩).2.2 (α:=Current)
  let original:=mainLowSelectedOriginal reflected s R seed Z 1 amp (nativeMu/64) (nativeMu/8)
    (9/4) firstHeight (Fintype.card Current) hZ bin caps.zero₁ caps.zero₂ firstIndex r
  have hvolume3 : volume s≤Z^(3:ℝ):=
    caps.volume.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num))
  have hc2:=hcaps.2 reflected s R seed 1 amp (nativeMu/64) (nativeMu/8) firstHeight hZ
    hcard caps.endpoints hseed caps.zero₁ caps.zero₂ caps.sourceCap hvolume3 bin 1 1 1
    original.val (hf r.val.1)
  have hsecondC:=hc2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (show (4:ℝ)≤130 by norm_num))
  have hsecondD:=hc2.2.2.2.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (show (4:ℝ)≤130 by norm_num))
  have hboxLocal:=hbLocal reflected s R seed 1 amp (nativeMu/8) firstHeight
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) le_rfl caps.endpoints hseed caps.zero₁ caps.zero₂
    (caps.sourceCap.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)))
    (caps.volumeLog.trans (by norm_num)) (by norm_num)
    (by rw [abs_of_nonneg hamp0];linarith only [hamp1])
    (by rw [abs_of_nonneg hsmall.1];exact hsmall.2.1.trans (by norm_num))
    hamp0 (div_nonneg nativeMu_pos.le (by norm_num)) bin (firstIndex r.val.1).1.val
    (firstIndex r.val.1).1.property (firstIndex r.val.1).2 (hf r.val.1) r.val.2
  have hboxRoot:=local_native_dyad_subset_root Z 1 (Fintype.card Current) budget hZ
    (by norm_num) (by norm_num) hcard
  simp only [Real.rpow_one] at hboxRoot
  exact actual_root_selected_all_row_key_facts Z hZ reflected s R seed 1 amp (nativeMu/64)
    (nativeMu/8) (9/4) firstHeight (Fintype.card Current) bin hseed caps.zero₁ caps.zero₂
    caps.sourceCap firstIndex units hunits (rootNativeDyadBox Z budget) r
    (by simpa only [nativeLowHistoryCode,original,mainLowSelectedOriginal,geometryMainOrdinaryDatum,
      ordinarySecondDatum,geometryLowSecondDatum,actualSecondBlockDatum,actualSecondInputDatum,
      Cycle63InitialMass.actualSecondArithmeticLabel] using hsecondC)
    (by simpa only [nativeLowHistoryCode,original,mainLowSelectedOriginal,geometryMainOrdinaryDatum,
      ordinarySecondDatum,geometryLowSecondDatum,actualSecondBlockDatum,actualSecondInputDatum,
      Cycle63InitialMass.actualSecondArithmeticLabel] using hsecondD)
    (hboxRoot (by simpa only [nativeLowHistoryCode,geometryLowFirstChild] using hboxLocal))

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.eventual_actual_root_all_row_source_facts
