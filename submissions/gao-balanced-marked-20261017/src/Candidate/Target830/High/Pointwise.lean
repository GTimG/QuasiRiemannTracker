import Candidate.Target830.High.ActualAllocation
import Candidate.Target830.High.Frequency
import Candidate.Target830.High.Channels
import Candidate.Target830.Source.Schedule

set_option autoImplicit false
set_option maxHeartbeats 1800000
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

theorem plane_q_lower (P : SourcePlane) : (31/50:ℝ) ≤ P.q := by
  cases P <;> norm_num [SourcePlane.q]

theorem plane_core_bounds (P : SourcePlane) :
    0 ≤ 1-6*P.rootCutoff ∧ 1-6*P.rootCutoff ≤ 1 ∧ 0 ≤ P.rootCutoff := by
  cases P <;> norm_num [SourcePlane.rootCutoff]

theorem source_gamma_bounds (P : SourcePlane) (delta : ℝ)
    (hd : P.q ≤ delta) (hu : delta ≤ 3/4) :
    0 ≤ commonGamma delta ∧ commonGamma delta ≤ delta ∧
    0 ≤ P.rootCutoff*(6*rho delta-1) := by
  have hr:=Target830.Source.Valuation.rho_extended_range
    (show (405/662:ℝ) ≤ delta by linarith [plane_q_lower P]) hu
  have ht : 0 ≤ P.rootCutoff*(6*rho delta-1) :=
    mul_nonneg (plane_core_bounds P).2.2 (by linarith [hr.1])
  exact ⟨by linarith [gamma_root_slope P delta hd hu],common_gamma_le delta,ht⟩

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]

/-- Literal small-allocation HIGH payment, in the paired physical first
orientation and with the exact adaptive marked/root gain. -/
theorem actual_geometry_retained_high_payment
    (P : SourcePlane) (s : Input alpha) (R seed : Ideal O) (K Z xi : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z xi hK bin))
    (d2 : SecondInputDatum alpha) (reflected second : Bool)
    (U : Finset (CommonIndex d2.C d2.D))
    (A a reserve err errv b delta live : ℝ) (hZ : 1<Z)
    (hb : b∈Set.Icc widthLower widthUpper) (hd : P.q ≤ delta) (hu : delta ≤ 7/10)
    (hA : A ≤ P.total b) (ha : a ≤ P.amp b)
    (homega : frequencyLoss Z 32 xi+reserve ≤ frequencyAllowance) (herr : 0 ≤ err)
    (hlive : 0 ≤ live) :
    let l:=geometryFirstLabel s R seed K Z xi hK bin j
    let side:=balancedGeometrySide reflected A (geometryExponents s R seed K Z xi j.1.val)
    let x:=childHighCoordinates
      (actualHighCoordinates reflected (!reflected) second l d2.C d2.D U Z 1 A a xi reserve err) errv
    let c:=labelC reflected l Z
    let b2:=Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ)
    let target:=(1-unmarkedDensity delta)*(frequencyLoss Z 32 xi+reserve)+unmarkedDensity delta*err+errv
    c+b2 ≤ P.supplied b → P.supplied b ≤ c+b2+live →
    retainedHighExponent delta
      (fun q=>min (Marked830.VariableSupply.physicalGain delta live ((1-6*P.rootCutoff)*q))
        (P.rootCutoff*(6*rho delta-1)*q)) x ≤ side+target-highFee := by
  intro l side x c b2 target hsmall hsupply
  let xc:=compensatedHighCoordinates x side
  have hdelta : 31/50 ≤ delta := (plane_q_lower P).trans hd
  have hdu : delta ≤ 3/4 := by linarith
  have hcone:=actual_geometry_balanced_common_payment s R seed K Z xi hK bin j d2
    reflected second U 1 A a reserve err errv delta hZ hdelta hdu
  have hf:=actual_geometry_balanced_moving_frequency s R seed K Z xi hK bin j d2 reflected second U
    1 A a reserve err errv (P.amp b) frequencyAllowance (1-6*P.rootCutoff) hZ
    (by simpa using ha) (by simpa using homega) herr
    (plane_core_bounds P).1 (plane_core_bounds P).2.1
  simp only [mul_one] at hf
  change 0 ≤ c ∧ 0 ≤ b2 ∧ xc 3=A-(c+b2) ∧
    (1-6*P.rootCutoff)*(1-6*P.amp b-frequencyAllowance)-2*(c+b2) ≤ (1-6*P.rootCutoff)*xc 2 at hf
  have hg:=source_gamma_bounds P delta hd hdu
  have hr:=Target830.Source.Valuation.rho_extended_range (show (405/662:ℝ) ≤ delta by linarith) hdu
  have hcoeff : 0 ≤ 5-6*unmarkedDensity delta := by change 0 ≤ 5-6*rho delta; linarith [hr.2]
  have hAA:=mul_le_mul_of_nonneg_left hA (show 0 ≤ delta by linarith)
  have haa:=mul_le_mul_of_nonneg_left ha hcoeff
  have hbb:=mul_le_mul_of_nonneg_right hg.2.1 hf.2.1
  have hsource : highExponentValue delta xc ≤ target-highBase P b delta-commonGamma delta*(c+b2) := by
    change highExponentValue delta xc ≤ target-
      (1*(1-unmarkedDensity delta)-delta*A-a*(5-6*unmarkedDensity delta))-
        commonGamma delta*c-delta*b2 at hcone
    change highExponentValue delta xc ≤ target-
      (1-rho delta-delta*P.total b-P.amp b*(5-6*rho delta))-commonGamma delta*(c+b2)
    change highExponentValue delta xc ≤ target-
      (1*(1-rho delta)-delta*A-a*(5-6*rho delta))-commonGamma delta*c-delta*b2 at hcone
    change delta*A ≤ delta*P.total b at hAA
    have haa2 : a*(5-6*rho delta) ≤ P.amp b*(5-6*rho delta) := by simpa only [←Target830.Source.Valuation.rho_eq_local,mul_comm] using haa
    linarith only [hcone,hAA,haa2,hbb]
  have guards:=Target830.Source.source_guards P hb
  obtain ⟨_,_,_,_,_,_,_,hSpos,_,hSFstrict,_⟩:=guards
  have hS : 0 ≤ P.supplied b := hSpos.le
  have hSF : 2*P.supplied b ≤ P.frequency b := hSFstrict.le
  have hfq : P.frequency b-2*(c+b2) ≤ (1-6*P.rootCutoff)*xc 2 := by
    simpa [SourcePlane.frequency,mul_assoc] using hf.2.2.2
  have hx2 : 0 ≤ xc 2 := by
    have hc:=plane_core_bounds P
    have hh : 0 ≤ (1-6*P.rootCutoff)*xc 2 := by linarith
    cases P <;> norm_num [SourcePlane.rootCutoff] at hh ⊢ <;> linarith
  have hh:=channel_reserves P b delta hb hd hu
  have hp:=retained_high_payment delta xc 0 target (highBase P b delta) highFee
    (commonGamma delta) (c+b2) (P.supplied b) live (P.frequency b)
    (1-6*P.rootCutoff) (P.rootCutoff*(6*rho delta-1)) hdelta hu hg.1
    (add_nonneg hf.1 hf.2.1) hS hSF hlive (plane_core_bounds P).1
    (plane_core_bounds P).2.1 hx2 hsupply (by linarith) hg.2.2
    (gamma_root_slope P delta hd hdu) (by linarith) hh.1
    (by simpa only [marked_phi_eq,marked_capI_eq,marked_capP_eq] using hh.2.1) (by simpa only [marked_phi_eq,marked_capI_eq,marked_capP_eq] using hh.2.2.1) (by simpa only [marked_phi_eq,marked_capI_eq,marked_capP_eq] using hh.2.2.2.1)
    (by simpa only [marked_phi_eq,marked_capI_eq,marked_capP_eq] using hh.2.2.2.2.1) hh.2.2.2.2.2
  have hid:=compensated_high_exponent delta side x
  have hx : xc 2=x 2 := by simp [xc,compensatedHighCoordinates,childHighCoordinates]
  unfold retainedHighExponent at hp ⊢
  change highExponentValue delta xc-_ ≤ _ at hp
  rw [hx] at hp
  change highExponentValue delta (compensatedHighCoordinates x side)=_ at hid
  linarith only [hp,hid]


/-- The complementary HIGH branch pays either by the upper density range
or by its actual removed width, in the same balanced source normalization. -/
theorem actual_geometry_unmarked_high_payment
    (P : SourcePlane) (s : Input alpha) (R seed : Ideal O) (K Z xi : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z xi hK bin))
    (d2 : SecondInputDatum alpha) (reflected second : Bool)
    (U : Finset (CommonIndex d2.C d2.D))
    (A a reserve err errv b delta : ℝ) (hZ : 1<Z)
    (hb : b∈Set.Icc widthLower widthUpper) (hd : P.q ≤ delta) (hu : delta ≤ 3/4)
    (hA : A ≤ P.total b) (ha : a ≤ P.amp b) :
    let l:=geometryFirstLabel s R seed K Z xi hK bin j
    let side:=balancedGeometrySide reflected A (geometryExponents s R seed K Z xi j.1.val)
    let x:=childHighCoordinates
      (actualHighCoordinates reflected (!reflected) second l d2.C d2.D U Z 1 A a xi reserve err) errv
    let c:=labelC reflected l Z
    let b2:=Real.logb Z ((if second then d2.D else d2.C).absNorm:ℝ)
    let target:=(1-unmarkedDensity delta)*(frequencyLoss Z 32 xi+reserve)+unmarkedDensity delta*err+errv
    (7/10 ≤ delta ∨ P.supplied b ≤ c+b2) →
    highExponentValue delta x ≤ side+target-highFee := by
  intro l side x c b2 target hbranch
  let xc:=compensatedHighCoordinates x side
  have hdelta : 31/50 ≤ delta := (plane_q_lower P).trans hd
  have hcone:=actual_geometry_balanced_common_payment s R seed K Z xi hK bin j d2
    reflected second U 1 A a reserve err errv delta hZ hdelta hu
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
  have hg:=source_gamma_bounds P delta hd hu
  have hr:=Target830.Source.Valuation.rho_extended_range
    (show (405/662:ℝ) ≤ delta by linarith) hu
  have hcoeff : 0 ≤ 5-6*unmarkedDensity delta := by
    change 0 ≤ 5-6*rho delta
    linarith [hr.2]
  have hAA:=mul_le_mul_of_nonneg_left hA (show 0 ≤ delta by linarith)
  have haa:=mul_le_mul_of_nonneg_left ha hcoeff
  have hbb:=mul_le_mul_of_nonneg_right hg.2.1 hb2
  have hsource : highExponentValue delta xc ≤ target-highBase P b delta-commonGamma delta*(c+b2) := by
    change highExponentValue delta xc ≤ target-
      (1*(1-rho delta)-delta*A-a*(5-6*rho delta))-commonGamma delta*c-delta*b2 at hcone
    change highExponentValue delta xc ≤ target-
      (1-rho delta-delta*P.total b-P.amp b*(5-6*rho delta))-commonGamma delta*(c+b2)
    have haa2 : a*(5-6*rho delta) ≤ P.amp b*(5-6*rho delta) := by
      simpa only [←Target830.Source.Valuation.rho_eq_local,mul_comm] using haa
    linarith only [hcone,hAA,haa2,hbb]
  have hreserve : highFee ≤ highBase P b delta+commonGamma delta*(c+b2) := by
    by_cases hup : 7/10 ≤ delta
    · have hh:=unmarked_high_reserve P b delta hb hup hu
      linarith [mul_nonneg hg.1 (add_nonneg hc hb2)]
    · have hs : P.supplied b ≤ c+b2 := hbranch.resolve_left hup
      have hh:=(channel_reserves P b delta hb hd (le_of_not_ge hup)).1
      have hm:=mul_le_mul_of_nonneg_left hs hg.1
      linarith only [hh,hm]
  have hid:=compensated_high_exponent delta side x
  change highExponentValue delta xc=highExponentValue delta x-side at hid
  linarith only [hsource,hreserve,hid]

end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.actual_geometry_retained_high_payment
#print axioms OAI.SevenEighths.TargetHigh830.actual_geometry_unmarked_high_payment
