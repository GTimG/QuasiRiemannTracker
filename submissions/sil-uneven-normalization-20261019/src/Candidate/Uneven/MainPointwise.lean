import Candidate.Uneven.ActualCommon
import Candidate.Target836.SourceProvider.HighCoordinates
import Candidate.Target830.Source.BalancedPayment
import Candidate.Target830.High.Payment
import Candidate.Target830.High.ActualAllocation
import Candidate.Target830.High.Frequency
import Candidate.Uneven.MainRemovedPayment
import Candidate.Uneven.HighMass

/- Original module: Candidate.Uneven.HighPayment. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.TargetHigh830
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic LocalMoment
open ConcretePrimeRowBridge CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstExceptionalPrefactor
open CenteredMomentAmplifiedRetainedRadius CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle63Moment Cycle63HighGeometry Cycle63InitialMass
open CenteredMomentAmplificationChildSourceCaps CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentFirstSourceReduction Cycle63FinalCapacity
local notation "O" => HeckeFamily.O

theorem actual_high_joint_uneven_valuation (reflected second : Bool)
    (l : FirstSourceLabel) (hC : Supported l.1.1) (hD : Supported l.1.2)
    (C2 D2 : Ideal O) (hC2 : Supported C2) (hD2 : Supported D2)
    (heq2 : primeSupport C2=primeSupport D2) (U : Finset (CommonIndex C2 D2))
    (Z delta M A a gamma skew : ℝ) (hZ : 1<Z)
    (hfirst : labelFirstCommon reflected l Z delta-labelSurplus reflected l Z-skew≤
      -gamma*labelC reflected l Z) :
    Cycle63.Physical.highJointExcess M A a delta
      (labelC reflected l Z) (labelD reflected l Z) (labelP l Z) (labelR l Z) (labelE l Z)
      (max (3*labelC reflected l Z-5*labelD reflected l Z-labelR l Z) 0/6)
      (Real.logb Z ((Ideal.span {firstSourceNumerator (!reflected) l}).absNorm:ℝ))
      (Real.logb Z ((cancelledRadical (!reflected) l.1.1 l.1.2).absNorm:ℝ))
      (Real.logb Z ((if second then D2 else C2).absNorm:ℝ))
      (Real.logb Z (normValue (commonFrequencyGenerator C2 D2)))
      (Real.logb Z ((∏P∈U,P.val).absNorm:ℝ))-labelSurplus reflected l Z-skew≤
      M*(unmarkedDensity delta-1)+delta*A+a*(5-6*unmarkedDensity delta)-
        gamma*labelC reflected l Z-delta*Real.logb Z ((if second then D2 else C2).absNorm:ℝ) := by
  have hg2 : Real.logb Z (normValue (commonFrequencyGenerator C2 D2))≤
      Real.logb Z ((if second then D2 else C2).absNorm:ℝ) := by
    apply Real.logb_le_logb_of_le hZ
      (normValue_pos _ (commonFrequencyGenerator_ne_zero C2 D2 hC2))
    cases second
    · exact actual_common_norm_le C2 D2 hC2 hD2 heq2
    · exact actual_common_norm_le_right C2 D2 hC2 hD2 heq2
  have ht2 := Cycle63FinalCapacity.actual_unit_log_nonneg C2 D2 hC2 U Z hZ
  dsimp [Cycle63.Physical.highJointExcess,labelFirstCommon,ValuationGain.firstCommon] at *
  linarith

/-- Literal first-label and second-child coordinates, with physical orientation
left=!reflected throughout. No historical rho<=.4 estimate is used. -/
theorem actual_high_coordinate_uneven_payment (reflected second : Bool)
    (l : FirstSourceLabel) (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (C2 D2 : Ideal O) (hC2 : Supported C2) (hD2 : Supported D2)
    (heq2 : primeSupport C2=primeSupport D2) (U : Finset (CommonIndex C2 D2))
    (Z delta M A a xi reserve err gamma skew : ℝ) (hZ : 1<Z)
    (hfirst : labelFirstCommon reflected l Z delta-labelSurplus reflected l Z-skew≤
      -gamma*labelC reflected l Z) :
    highExponentValue delta
      (actualHighCoordinates reflected (!reflected) second l C2 D2 U Z M A a xi reserve err)≤
      labelSide reflected l Z A+labelSurplus reflected l Z+skew+
        (1-unmarkedDensity delta)*(frequencyLoss Z 32 xi+reserve)+unmarkedDensity delta*err-
        (M*(1-unmarkedDensity delta)-delta*A-a*(5-6*unmarkedDensity delta))-
        gamma*labelC reflected l Z-delta*Real.logb Z ((if second then D2 else C2).absNorm:ℝ) := by
  have hid := Target874836.SourceProvider.actual_high_coordinate_excess_identity
    reflected (!reflected) second l hC hD heq C2 D2 hC2 hD2 heq2 U Z 0 delta M A a xi reserve err hZ
  have hh := actual_high_joint_uneven_valuation reflected second l hC hD C2 D2 hC2 hD2 heq2
    U Z delta M A a gamma skew hZ hfirst
  dsimp only at hid
  dsimp [labelC,labelD,labelR,labelE,labelP,labelSide] at hh ⊢
  rw [hid]
  linarith

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]

theorem actual_geometry_uneven_high_payment
    (s : Input alpha) (R seed : Ideal O) (K Z xi : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z xi hK bin))
    (d2 : SecondInputDatum alpha) (reflected second : Bool)
    (U : Finset (CommonIndex d2.C d2.D))
    (D A a reserve err errv delta : ℝ) (hZ : 1<Z)
    (hd : 31/50 ≤ delta) (hdhi : delta ≤ 3/4) :
    let l:=geometryFirstLabel s R seed K Z xi hK bin j
    let side:=balancedGeometrySide reflected A (geometryExponents s R seed K Z xi j.1.val)+
      labelSkew reflected l Z
    let x:=compensatedHighCoordinates (childHighCoordinates
      (actualHighCoordinates reflected (!reflected) second l d2.C d2.D U Z D A a xi reserve err) errv) side
    highExponentValue delta x≤
      (1-unmarkedDensity delta)*(frequencyLoss Z 32 xi+reserve)+unmarkedDensity delta*err+errv-
        (D*(1-unmarkedDensity delta)-delta*A-a*(5-6*unmarkedDensity delta))-
        (delta-2/5)*labelC reflected l Z-delta*Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ) := by
  intro l side x
  have hC : Supported l.1.1 := (geometryFirstSource s R seed K Z xi hK bin j.1).hC
  have hD : Supported l.1.2 := (geometryFirstSource s R seed K Z xi hK bin j.1).hD
  have heq : primeSupport l.1.1=primeSupport l.1.2 :=
    (geometryFirstSource s R seed K Z xi hK bin j.1).sameSupport
  have hfirst := actual_geometry_label_common_skew s R seed K Z xi hK bin j reflected delta hZ hd hdhi
  have hh := actual_high_coordinate_uneven_payment reflected second l hC hD heq
    d2.C d2.D d2.hC d2.hD d2.sameSupport U Z delta D A a xi reserve err (delta-2/5) (labelSkew reflected l Z) hZ hfirst
  have he := actual_geometry_high_side_identity s R seed K Z xi hK bin j reflected A
  have hbase := balanced_geometry_side_eq s R seed K Z xi hK bin j reflected A
  change geometryHighSide reflected A (geometryExponents s R seed K Z xi j.1.val)=labelSide reflected l Z A at he
  have hside : side=labelSide reflected l Z A+labelSurplus reflected l Z+labelSkew reflected l Z := by
    dsimp only [side]
    rw [hbase,he]
  rw [←hside] at hh
  dsimp only [x]
  rw [compensated_high_exponent,child_high_exponent_value]
  linarith only [hh]

end OAI.SevenEighths.TargetHigh830
end

/- Original module: Candidate.Uneven.MainPointwise. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace OAI.SevenEighths.TargetHigh830
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic LocalMoment
open ConcretePrimeRowBridge CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstExceptionalPrefactor
open CenteredMomentAmplifiedRetainedRadius CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle63Moment Cycle63HighGeometry Cycle63InitialMass
open CenteredMomentAmplificationChildSourceCaps CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentFirstSourceReduction Cycle63FinalCapacity
open Target830
local notation "O" => HeckeFamily.O

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]

theorem actual_geometry_main_bootstrap_retained_payment
    (P : Sil.Uneven.MainSource.Plane)
    (s : Input alpha) (R seed : Ideal O) (K Z xi : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z xi hK bin))
    (d2 : SecondInputDatum alpha) (reflected second : Bool)
    (U : Finset (CommonIndex d2.C d2.D))
    (A a reserve err errv b delta live : ℝ) (hZ : 1<Z)
    (hb : b∈Set.Icc Sil.Uneven.MainSource.widthLo Sil.Uneven.MainSource.widthHi)
    (hd : P.q ≤ delta) (hu : delta ≤ 33/50)
    (hA : A ≤ Sil.Uneven.MainSource.total P b) (ha : a ≤ Sil.Uneven.MainSource.amp P b)
    (homega : frequencyLoss Z 32 xi+reserve ≤ Sil.Uneven.MainSource.frequencyAllowance)
    (herr : 0 ≤ err) (hlive : 0 ≤ live) :
    let l:=geometryFirstLabel s R seed K Z xi hK bin j
    let side:=unevenGeometrySide reflected A (geometryExponents s R seed K Z xi j.1.val)
    let x:=childHighCoordinates
      (actualHighCoordinates reflected (!reflected) second l d2.C d2.D U Z 1 A a xi reserve err) errv
    let c:=labelC reflected l Z
    let b2:=Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ)
    let target:=(1-unmarkedDensity delta)*(frequencyLoss Z 32 xi+reserve)+unmarkedDensity delta*err+errv
    c+b2 ≤ Sil.Uneven.MainSource.supplied b → Sil.Uneven.MainSource.supplied b ≤ c+b2+live →
    retainedHighExponent delta (fun freq=>Sil.Uneven.Bootstrap.physicalGain delta live freq) x
      ≤ side+target-Sil.Uneven.MainSource.highReserve := by
  intro l side x c b2 target hsmall hsupply
  let xc:=compensatedHighCoordinates x side
  have hdelta : 31/50 ≤ delta := (Sil.Uneven.MainSource.parameter_gates P).1.trans hd
  have hcone:=actual_geometry_uneven_high_payment s R seed K Z xi hK bin j d2
    reflected second U 1 A a reserve err errv delta hZ hdelta (by linarith)
  dsimp only at hcone
  rw [←uneven_geometry_side_label s R seed K Z xi hK hZ bin j reflected A] at hcone
  have hf:=actual_geometry_balanced_moving_frequency s R seed K Z xi hK bin j d2 reflected second U
    1 A a reserve err errv (Sil.Uneven.MainSource.amp P b) Sil.Uneven.MainSource.frequencyAllowance 1 hZ
    (by simpa using ha) (by simpa using homega) herr (by norm_num) (by norm_num)
  simp only [mul_one,one_mul] at hf
  change 0 ≤ c ∧ 0 ≤ b2 ∧ xc 3=A-(c+b2) ∧ Sil.Uneven.MainSource.frequency P b-2*(c+b2) ≤ xc 2 at hf
  have hg:=Sil.Uneven.MainSource.gamma_bounds hdelta (by linarith)
  have hAA:=mul_le_mul_of_nonneg_left hA (show 0 ≤ delta by linarith)
  have haa:=mul_le_mul_of_nonneg_right ha hg.2.2
  have hsource : highExponentValue delta xc ≤ target-Sil.Uneven.MainSource.highBase P b delta-Sil.Uneven.MainSource.gamma delta*c-delta*b2 := by
    change highExponentValue delta xc ≤ target-
      (1*(1-unmarkedDensity delta)-delta*A-a*(5-6*unmarkedDensity delta))-
        Sil.Uneven.MainSource.gamma delta*c-delta*b2 at hcone
    change a*(5-6*unmarkedDensity delta) ≤ Sil.Uneven.MainSource.amp P b*(5-6*unmarkedDensity delta) at haa
    change highExponentValue delta xc ≤ target-
      (1-unmarkedDensity delta-delta*Sil.Uneven.MainSource.total P b-Sil.Uneven.MainSource.amp P b*(5-6*unmarkedDensity delta))-
        Sil.Uneven.MainSource.gamma delta*c-delta*b2
    linarith only [hcone,hAA,haa]
  obtain ⟨_,_,_,_,_,_,_,_,_,hFstrict,_⟩ := Sil.Uneven.MainSource.scheduling_guards P hb
  have hF : 2*Sil.Uneven.MainSource.supplied b ≤ Sil.Uneven.MainSource.frequency P b := hFstrict.le
  have hx2 : 0 ≤ xc 2 := by linarith only [hf.2.2.2,hF,hsmall]
  have hfrequency : Sil.Uneven.MainSource.frequency P b ≤ 2*(c+b2)+xc 2 := by linarith only [hf.2.2.2]
  have hp:=Sil.Uneven.MainSource.bootstrap_retained_payment P hb hd hu hf.1 hf.2.1 hlive hx2 hsupply hfrequency hsource
  have hid:=compensated_high_exponent delta side x
  have hx : xc 2=x 2 := by simp [xc,compensatedHighCoordinates,childHighCoordinates]
  unfold retainedHighExponent
  rw [hx] at hp
  change highExponentValue delta (compensatedHighCoordinates x side)=_ at hid
  linarith only [hp,hid]

theorem actual_geometry_main_saturated_retained_payment
    (P : Sil.Uneven.MainSource.Plane)
    (s : Input alpha) (R seed : Ideal O) (K Z xi : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z xi hK bin))
    (d2 : SecondInputDatum alpha) (reflected second : Bool)
    (U : Finset (CommonIndex d2.C d2.D))
    (A a reserve err errv b delta live : ℝ) (hZ : 1<Z)
    (hb : b∈Set.Icc Sil.Uneven.MainSource.widthLo Sil.Uneven.MainSource.widthHi)
    (hd : P.q ≤ delta) (hu : delta ≤ 3/4) (hmid : 33/50 ≤ delta)
    (hA : A ≤ Sil.Uneven.MainSource.total P b) (ha : a ≤ Sil.Uneven.MainSource.amp P b)
    (homega : frequencyLoss Z 32 xi+reserve ≤ Sil.Uneven.MainSource.frequencyAllowance)
    (herr : 0 ≤ err) (hlive : 0 ≤ live) :
    let l:=geometryFirstLabel s R seed K Z xi hK bin j
    let side:=unevenGeometrySide reflected A (geometryExponents s R seed K Z xi j.1.val)
    let x:=childHighCoordinates
      (actualHighCoordinates reflected (!reflected) second l d2.C d2.D U Z 1 A a xi reserve err) errv
    let c:=labelC reflected l Z
    let b2:=Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ)
    let target:=(1-unmarkedDensity delta)*(frequencyLoss Z 32 xi+reserve)+unmarkedDensity delta*err+errv
    c+b2 ≤ Sil.Uneven.MainSource.supplied b → Sil.Uneven.MainSource.supplied b ≤ c+b2+live →
    retainedHighExponent delta (fun freq=>Sil.Uneven.Saturated.physicalGain delta live freq) x
      ≤ side+target-Sil.Uneven.MainSource.highReserve := by
  intro l side x c b2 target hsmall hsupply
  let xc:=compensatedHighCoordinates x side
  have hdelta : 31/50 ≤ delta := (Sil.Uneven.MainSource.parameter_gates P).1.trans hd
  have hcone:=actual_geometry_uneven_high_payment s R seed K Z xi hK bin j d2
    reflected second U 1 A a reserve err errv delta hZ hdelta (by linarith)
  dsimp only at hcone
  rw [←uneven_geometry_side_label s R seed K Z xi hK hZ bin j reflected A] at hcone
  have hf:=actual_geometry_balanced_moving_frequency s R seed K Z xi hK bin j d2 reflected second U
    1 A a reserve err errv (Sil.Uneven.MainSource.amp P b) Sil.Uneven.MainSource.frequencyAllowance 1 hZ
    (by simpa using ha) (by simpa using homega) herr (by norm_num) (by norm_num)
  simp only [mul_one,one_mul] at hf
  change 0 ≤ c ∧ 0 ≤ b2 ∧ xc 3=A-(c+b2) ∧ Sil.Uneven.MainSource.frequency P b-2*(c+b2) ≤ xc 2 at hf
  have hg:=Sil.Uneven.MainSource.gamma_bounds hdelta (by linarith)
  have hAA:=mul_le_mul_of_nonneg_left hA (show 0 ≤ delta by linarith)
  have haa:=mul_le_mul_of_nonneg_right ha hg.2.2
  have hsource : highExponentValue delta xc ≤ target-Sil.Uneven.MainSource.highBase P b delta-Sil.Uneven.MainSource.gamma delta*c-delta*b2 := by
    change highExponentValue delta xc ≤ target-
      (1*(1-unmarkedDensity delta)-delta*A-a*(5-6*unmarkedDensity delta))-
        Sil.Uneven.MainSource.gamma delta*c-delta*b2 at hcone
    change a*(5-6*unmarkedDensity delta) ≤ Sil.Uneven.MainSource.amp P b*(5-6*unmarkedDensity delta) at haa
    change highExponentValue delta xc ≤ target-
      (1-unmarkedDensity delta-delta*Sil.Uneven.MainSource.total P b-Sil.Uneven.MainSource.amp P b*(5-6*unmarkedDensity delta))-
        Sil.Uneven.MainSource.gamma delta*c-delta*b2
    linarith only [hcone,hAA,haa]
  obtain ⟨_,_,_,_,_,_,_,_,_,hFstrict,_⟩ := Sil.Uneven.MainSource.scheduling_guards P hb
  have hF : 2*Sil.Uneven.MainSource.supplied b ≤ Sil.Uneven.MainSource.frequency P b := hFstrict.le
  have hx2 : 0 ≤ xc 2 := by linarith only [hf.2.2.2,hF,hsmall]
  have hfrequency : Sil.Uneven.MainSource.frequency P b ≤ 2*(c+b2)+xc 2 := by linarith only [hf.2.2.2]
  have hp:=Sil.Uneven.MainSource.saturated_retained_payment P hb hmid hu hf.1 hf.2.1 hlive hx2 hsupply hfrequency hsource
  have hid:=compensated_high_exponent delta side x
  have hx : xc 2=x 2 := by simp [xc,compensatedHighCoordinates,childHighCoordinates]
  unfold retainedHighExponent
  rw [hx] at hp
  change highExponentValue delta (compensatedHighCoordinates x side)=_ at hid
  linarith only [hp,hid]

theorem actual_geometry_main_unmarked_payment
    (P : Sil.Uneven.MainSource.Plane)
    (s : Input alpha) (R seed : Ideal O) (K Z xi : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z xi hK bin))
    (d2 : SecondInputDatum alpha) (reflected second : Bool)
    (U : Finset (CommonIndex d2.C d2.D))
    (A a reserve err errv b delta : ℝ) (hZ : 1<Z)
    (hb : b∈Set.Icc Sil.Uneven.MainSource.widthLo Sil.Uneven.MainSource.widthHi) (hd : P.q ≤ delta) (hu : delta ≤ 3/4)
    (hA : A ≤ Sil.Uneven.MainSource.total P b) (ha : a ≤ Sil.Uneven.MainSource.amp P b) :
    let l:=geometryFirstLabel s R seed K Z xi hK bin j
    let side:=unevenGeometrySide reflected A (geometryExponents s R seed K Z xi j.1.val)
    let x:=childHighCoordinates
      (actualHighCoordinates reflected (!reflected) second l d2.C d2.D U Z 1 A a xi reserve err) errv
    let c:=labelC reflected l Z
    let b2:=Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ)
    let target:=(1-unmarkedDensity delta)*(frequencyLoss Z 32 xi+reserve)+unmarkedDensity delta*err+errv
    (Sil.Uneven.MainSource.supplied b ≤ c+b2) →
    highExponentValue delta x ≤ side+target-Sil.Uneven.MainSource.highReserve := by
  intro l side x c b2 target hbranch
  let xc:=compensatedHighCoordinates x side
  have hdelta : 31/50 ≤ delta := (Sil.Uneven.MainSource.parameter_gates P).1.trans hd
  have hcone:=actual_geometry_uneven_high_payment s R seed K Z xi hK bin j d2
    reflected second U 1 A a reserve err errv delta hZ hdelta hu
  dsimp only at hcone
  rw [←uneven_geometry_side_label s R seed K Z xi hK hZ bin j reflected A] at hcone
  have hC := (geometryFirstSource s R seed K Z xi hK bin j.1).hC
  have hD := (geometryFirstSource s R seed K Z xi hK bin j.1).hD
  have hc : 0 ≤ c := by
    apply Real.logb_nonneg hZ
    cases reflected
    · exact norm_ge_one l.1.1 hC.1
    · exact norm_ge_one l.1.2 hD.1
  have hb2 : 0 ≤ b2 := by
    apply Real.logb_nonneg hZ
    cases second
    · exact norm_ge_one d2.C d2.hC.1
    · exact norm_ge_one d2.D d2.hD.1
  have hg:=Sil.Uneven.MainSource.gamma_bounds hdelta hu
  have hr:=Target830.Source.Valuation.rho_extended_range
    (show (405/662:ℝ) ≤ delta by linarith) hu
  have hcoeff : 0 ≤ 5-6*unmarkedDensity delta := by
    change 0 ≤ 5-6*rho delta
    linarith [hr.2]
  have hAA:=mul_le_mul_of_nonneg_left hA (show 0 ≤ delta by linarith)
  have haa:=mul_le_mul_of_nonneg_left ha hcoeff
  have hbb:=mul_le_mul_of_nonneg_right hg.2.1 hb2
  have hsource : highExponentValue delta xc ≤ target-Sil.Uneven.MainSource.highBase P b delta-Sil.Uneven.MainSource.gamma delta*(c+b2) := by
    change highExponentValue delta xc ≤ target-
      (1*(1-rho delta)-delta*A-a*(5-6*rho delta))-Sil.Uneven.MainSource.gamma delta*c-delta*b2 at hcone
    change highExponentValue delta xc ≤ target-
      (1-rho delta-delta*Sil.Uneven.MainSource.total P b-Sil.Uneven.MainSource.amp P b*(5-6*rho delta))-Sil.Uneven.MainSource.gamma delta*(c+b2)
    have haa2 : a*(5-6*rho delta) ≤ Sil.Uneven.MainSource.amp P b*(5-6*rho delta) := by
      simpa only [←Target830.Source.Valuation.rho_eq_local,mul_comm] using haa
    linarith only [hcone,hAA,haa2,hbb]
  have hreserve : Sil.Uneven.MainSource.highReserve ≤ Sil.Uneven.MainSource.highBase P b delta+Sil.Uneven.MainSource.gamma delta*(c+b2) := by
    have hh:=Sil.Uneven.MainSource.removed_channel_reserve P hb hd hu
    have hm:=mul_le_mul_of_nonneg_left hbranch hg.1
    linarith only [hh,hm]
  have hid:=compensated_high_exponent delta side x
  change highExponentValue delta xc=highExponentValue delta x-side at hid
  linarith only [hsource,hreserve,hid]

end OAI.SevenEighths.TargetHigh830
end
