/- Actual all-row scalar payment, with the original reciprocal ideal norm.
Native geometry by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeSelectedSourceOld
import Candidate.Research.RecursiveAffine.ActualSelectedSourceGates
import Candidate.Cycle63.Physical.InitialMass.GeometryMainHighSourceCaps
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowNormalizedPayment
import Candidate.Cycle63.Physical.InitialMass.SecondChildLowPayment

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153ActualSourceGates
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSectorLocalization
open CenteredMomentSecondCanonical CenteredMomentSecondInputCapacitySource
open CenteredMomentSecondCanonicalScalar
open Cycle63FinalCapacity Cycle153RegionalLow Cycle153SourceSchedule Cycle153SourceUniform Cycle153.RegionalSchedule
open CenteredMomentFiniteProfileExceptional Cycle153JointCount

/-- The native inverse-volume payment is applied to every literal selected
row. Supported labels, exact first allocations and both second-ideal caps
are obtained from that source; the desired scalar bound is not a premise. -/
theorem eventual_actual_selected_scalar_payment_uniform (budget : ℕ) (epsV : ℝ) (hepsV : 0<epsV) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(ledger : Cycle63.AffineLedger), letI : Cycle63.AffineLedger:=ledger
    ∀(hZ : 1<Z){alpha : Type}[Fintype alpha][DecidableEq alpha]
      (s : Input alpha)(p : Profiles (1/4) (9/4))(Cs : ℝ)
      (caps : GeometryAffineLowSourceGates s p Cs Z),
    Fintype.card alpha ≤ budget→
    ∀{Label : Type}[Fintype Label](reflected second : Bool)(R seed : Ideal O)
      (hseed : Squarefree seed)(Mrow amp firstHeight common pad shellLoss : ℝ)
      (key : ℤ×(Fin 5→ℤ))
      (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z (nativeMu/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key),
    (∀l,frozenCoefficient (firstIndex l).2.val
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z (nativeMu/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val)
      R s.ν s.W s.P≠0)→
    0 ≤ shellLoss→
    ∀r : NativeLowRows reflected s R seed Z Mrow amp (nativeMu/64) (nativeMu/8) (9/4)
      firstHeight (Fintype.card alpha) hZ key caps.zero₁ caps.zero₂ firstIndex,
    let first : FirstSourceLabel :=geometryFirstLabel s R seed (Z^Mrow) Z (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex r.val.1).1.val
    let src:=geometryLowFirstChild reflected s R seed (Z^Mrow) Z (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key firstHeight (firstIndex r.val.1)
    let datum:=geometryLowSecondDatum reflected s R seed Z Mrow amp (nativeMu/64) (nativeMu/8) (9/4)
      firstHeight (Fintype.card alpha) hZ key (firstIndex r.val.1) caps.zero₁ caps.zero₂ r.val.2
    let ownNorm:ℝ:=(if second then datum.D else datum.C).absNorm
    let nominal : ℝ :=secondNominal 1 Z amp (frequencyLoss Z 32 (nativeMu/64)+nativeMu/8)
      (if reflected then first.1.2 else first.1.1) (if reflected then first.1.1 else first.1.2)
      datum.C datum.D datum.inactive
    Z^(-amp)*(firstMainRadius reflected (Z^Mrow) (volume s) Z (nativeMu/64) (3*amp) (nativeMu/8) first/
      volume src)*(normalizer datum.C datum.D datum.inactive*ownNorm^(shellLoss-1))*
        Z^(nominal+amp+common+pad) ≤
      Z^(lowGeometryExponent reflected Z (Real.logb Z (volume s)) first+(common+pad)+
        (1-Mrow)+epsV+130*shellLoss)/ownNorm :=by
  have hm0:=div_pos nativeMu_pos (by norm_num : (0:ℝ)<8)
  have hm1 : nativeMu/8 ≤ 1 :=by norm_num[nativeMu,primitiveError]
  filter_upwards [eventual_actual_child_low_mass_payment budget 1 epsV (by norm_num) hepsV,
    eventual_actual_geometry_main_high_source_caps budget (9/4) (9/4) (nativeMu/8)
      (by norm_num) (by norm_num) hm0 hm1] with Z hp hc
  refine ⟨hp.1,?_⟩
  intro ledger
  letI : Cycle63.AffineLedger:=ledger
  intro hZ alpha _ _ s p Cs caps hcard Label _ reflected second R seed hseed Mrow amp firstHeight common pad shellLoss
  intro key firstIndex hf hShell r first src datum ownNorm nominal
  have hf1:=actual_main_low_first_source_gates reflected s R seed (Z^Mrow) Z (nativeMu/64) 3
    (Real.rpow_pos_of_pos (zero_lt_one.trans hp.1) _) hseed caps.zero₁ caps.zero₂ caps.sourceCap key firstIndex r.val.1
  let original:=mainLowSelectedOriginal reflected s R seed Z Mrow amp (nativeMu/64) (nativeMu/8)
    (9/4) firstHeight (Fintype.card alpha) hp.1 key caps.zero₁ caps.zero₂ firstIndex r
  have hvol3 : volume s ≤ Z^(3:ℝ):=caps.volume.trans
    (Real.rpow_le_rpow_of_exponent_le hp.1.le (by norm_num))
  have hc2:=hc.2 reflected s R seed Mrow amp (nativeMu/64) (nativeMu/8) firstHeight hp.1 hcard
    caps.endpoints hseed caps.zero₁ caps.zero₂ caps.sourceCap hvol3 key 1 1 1 original.val (hf r.val.1)
  have hown : ownNorm ≤ Z^(130:ℝ):=by
    apply le_trans (by cases second; exact hc2.2.2.1; exact hc2.2.2.2)
    exact Real.rpow_le_rpow_of_exponent_le hp.1.le (by norm_num)
  have hfirstIdeal : geometryColumnIdeal reflected s R seed (Z^Mrow) Z (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hp.1) _) key (firstIndex r.val.1).1.val=
      (if reflected then first.1.2 else first.1.1):=by cases reflected <;> rfl
  have hFirstFrozen : frozenCoefficient (firstIndex r.val.1).2.val
      (if reflected then first.1.2 else first.1.1) R s.ν s.W s.P≠0:=by
    rw [←hfirstIdeal];exact hf r.val.1
  have hpay:=hp.2 s hcard (by rw[caps.lower]) reflected second first hf1.1 hf1.2.1 hf1.2.2.1
    R (firstIndex r.val.1).2
    (geometryColumnCharacter reflected s R seed (Z^Mrow) Z (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hp.1) _) key (firstIndex r.val.1).1.val)
    firstHeight hFirstFrozen datum.C datum.D datum.hC datum.hD datum.inactive
    1 Mrow amp (nativeMu/64) (nativeMu/8) (common+pad) shellLoss 130 hShell hown
  have hsrc : child s (if reflected then first.1.2 else first.1.1) R (firstIndex r.val.1).2
      (geometryColumnCharacter reflected s R seed (Z^Mrow) Z (nativeMu/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hp.1) _) key (firstIndex r.val.1).1.val)
      firstHeight=src :=by rfl
  simpa only[hsrc,ownNorm,nominal,add_assoc] using hpay
end
end OAI.SevenEighths.Cycle153ActualSourceGates
#print axioms OAI.SevenEighths.Cycle153ActualSourceGates.eventual_actual_selected_scalar_payment_uniform
