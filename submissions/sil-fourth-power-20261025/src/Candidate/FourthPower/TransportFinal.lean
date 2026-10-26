/- Adapted from the pinned Hailey Collet/OpenAI transport.
Apache-2.0 attribution is retained in each source block.
Only guard class/namespace references are generalized; analytic proof bodies
and original physical objects are preserved.  -/
import Candidate.FourthPower.TransportGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional
import Candidate.FourthPower.TransportSignal
import Candidate.FourthPower.ReturnCarrierInterfaces
import Candidate.FourthPower.TransportNonfloor
import Submissions.hailey_collet_1252270103.Record1252270103Return.Low.Probe

/- BEGIN pinned source: Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.FinalFixedHigh -/
/- Source integration: PR50 8cb265dc base; PR56 67edfb7a detector affine interfaces.
   Original Hailey Collet, OpenAI and predecessor notices are retained.
   Detector affine contribution: DaysSky, with Claude assistance; Apache-2.0. -/

                                         
                                    
                                      
                                                   

set_option autoImplicit false
namespace QRH.Record1252270103Return.GenericPhysical.FourthPowerFinalAssembly
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [Candidate.FourthPower.TransportBounds]
open scoped Classical BigOperators
open QRH.Record1252270103Return.Geometry
open Filter Asymptotics OAI.SevenEighths
open QRH.Record1252270103Return.GenericPhysical.Assembly
open HeckeFamily ProbePhysical QRH.Record1252270103Return.GenericPhysical PrincipalSignalComparison SilFourthPowerTransportHighTransport

theorem baseline_beta : HeckeZeroSupremum.beta ≤ (7/8:ℝ) :=
  HeckeCommonProbe.beta_le_seven_eighths
    (ProbeFinalAssembly.common_probe_of_chosen_moments
      (ProbeFinalAssemblyCertifiedBands.chosen_moments_of_certified
        ProbeFinalAssemblyUnconditional.detector_certified_bands))

/-- The finite numerator remains the honest analytic integration prerequisite. -/
def FixedFiniteNumeratorInput (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (τ : ℝ) : Prop :=
  ∀n : ℕ,0< n → ∀η : Character,
    FiniteNonfloorNumeratorBound F.modulus ⊤ le_top F.S F.exclusions F.maximal
      D.length 1 2 Candidate.FourthPower.ReturnCarrierInterfaces.rowPadding D.e τ P.sigma (fun _=>F.w) F.W F.W n η

/-- The finite numerator bound for one character. -/
def FixedFiniteNumeratorInputAt (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (τ : ℝ) (η : Character) : Prop :=
  ∀n : ℕ,0< n →
    FiniteNonfloorNumeratorBound F.modulus ⊤ le_top F.S F.exclusions F.maximal
      D.length 1 2 Candidate.FourthPower.ReturnCarrierInterfaces.rowPadding D.e τ P.sigma (fun _=>F.w) F.W F.W n η

theorem sourceProbe_high_of_finite_numerator (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (J τ : ℝ) (hheight : Candidate.FourthPower.ReturnCarrierInterfaces.HeightAdmissible D P J τ)
    (hβ : theta≤ HeckeZeroSupremum.beta)
    (hfinite : FixedFiniteNumeratorInput D F P τ) :
    ∀η : Character,
      (fun Z=>sourceProbe D F η Z-HeckeSignal.signal
        (η.excludePrimes F.S F.exclusions.prime) (sourceCorrection η F.S) Assembly.signalShift Z)
        =O[atTop](fun Z : ℝ=>Z^(HeckeZeroSupremum.beta+Assembly.signalShift-P.sigma)) := by
  rcases hheight with ⟨hτ,hτd,hτcost,hτt,hτeps,hτJ⟩
  have hlarge : P.sigma+P.nu≤1+Assembly.signal theta := by
    have hn:=P.nu_eq
    have hs:=P.sigma_small
    have ht:=D.t_small
    have hsig : (1/10:ℝ)< Assembly.signal theta := by
      have hb := SilFourthPowerTransport.Assembly.signal_at_boundary
      have hx : 1672/10000<Geometry.x := Candidate.FourthPower.TransportBounds.ell_interval.1.trans Geometry.ell_lt_x
      have hy : 458/1000<Geometry.y := Candidate.FourthPower.TransportBounds.ly_coarse.1
      change Assembly.signal theta=Geometry.x/2+(Geometry.y-Geometry.x)/12 at hb
      linarith
    linarith
  have hcap : h+Candidate.FourthPower.ReturnCarrierInterfaces.rowPadding≤(7/8:ℝ)-1/100 := by
    have hb : h<802/1000 := Candidate.FourthPower.TransportBounds.h_interval.2
    dsimp [Candidate.FourthPower.ReturnCarrierInterfaces.rowPadding]
    linarith
  have hh := normalizedProbe_high_of_finite_nonfloor_numerator F.modulus ⊤ le_top
    D.N D.e (1/100) 1 2 1 Candidate.FourthPower.ReturnCarrierInterfaces.rowPadding 1 τ P.ellMin P.nu
    D.e_pos D.e_small (by norm_num) (by norm_num)
    (by norm_num [QRH.Record1252270103Return.Geometry.theta,QRH.Record1252270103Return.Geometry.h,QRH.Record1252270103Return.Geometry.ell,QRH.Record1252270103Return.Geometry.x,QRH.Record1252270103Return.Geometry.y,Candidate.FourthPower.ReturnCarrierInterfaces.rowPadding]) (by norm_num [QRH.Record1252270103Return.Geometry.theta,QRH.Record1252270103Return.Geometry.h,QRH.Record1252270103Return.Geometry.ell,QRH.Record1252270103Return.Geometry.x,QRH.Record1252270103Return.Geometry.y,Candidate.FourthPower.ReturnCarrierInterfaces.rowPadding])
    hτ (by norm_num) (by norm_num) (by norm_num) P.ellMin_pos P.nu_pos
    hβ baseline_beta F.S F.exclusions F.maximal F.first
    D.length P.slots_min D.slots_injective D.slots_sum
    (fun _=>F.w) (fun _=>F.smooth) (fun _=>F.compact) (fun _=>F.support)
    (fun _=>F.bounded) (fun _=>F.nonzero)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative
    F.complex_nonzero F.complex_nonzero P.sigma P.sigma_pos
    P.geometric_budget P.principal_budget P.window_budget hlarge
    P.eps D.t (1/200) (7/8) P.rmin P.phaseEpsilon P.phaseKappa
    D.cost P.mesh (1/100) D.t
    P.eps_pos D.t_pos.le (by norm_num) (by norm_num) (by norm_num)
    P.rmin_pos P.phaseEpsilon_pos P.phaseKappa_pos D.cost_pos.le P.mesh_pos (by norm_num)
    P.phase_budget P.phase_gap (by linarith) hτeps hcap
    P.slots_lower D.slots_small (by norm_num [QRH.Record1252270103Return.Geometry.theta,QRH.Record1252270103Return.Geometry.h,QRH.Record1252270103Return.Geometry.ell,QRH.Record1252270103Return.Geometry.x,QRH.Record1252270103Return.Geometry.y,Candidate.FourthPower.ReturnCarrierInterfaces.rowPadding,SilFourthPowerTransport.Transport.rowExtension]) P.floor_budget hfinite
  simpa only [sourceProbe,Record1252270103Low.normalizedProbe,Record1252270103Low.normalizedProbe,SilFourthPowerTransport.Arithmetic.y,SilFourthPowerTransport.Assembly.signalShift,Assembly.signalShift,Record1252270103Return.Transport.Assembly.signalShift,Record1252270103Return.Transport.Arithmetic.x,Record1252270103Return.Transport.Arithmetic.ell,SilFourthPowerTransport.Arithmetic.x,SilFourthPowerTransport.Arithmetic.ell] using hh
theorem sourceProbe_high_of_finite_numerator_at (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (J τ : ℝ) (hheight : Candidate.FourthPower.ReturnCarrierInterfaces.HeightAdmissible D P J τ)
    (hβ : theta≤ HeckeZeroSupremum.beta)
    (η : Character) (hfinite : FixedFiniteNumeratorInputAt D F P τ η) :
      (fun Z=>sourceProbe D F η Z-HeckeSignal.signal
        (η.excludePrimes F.S F.exclusions.prime) (sourceCorrection η F.S) Assembly.signalShift Z)
        =O[atTop](fun Z : ℝ=>Z^(HeckeZeroSupremum.beta+Assembly.signalShift-P.sigma)) := by
  rcases hheight with ⟨hτ,hτd,hτcost,hτt,hτeps,hτJ⟩
  have hlarge : P.sigma+P.nu≤1+Assembly.signal theta := by
    have hn:=P.nu_eq
    have hs:=P.sigma_small
    have ht:=D.t_small
    have hsig : (1/10:ℝ)< Assembly.signal theta := by
      have hb := SilFourthPowerTransport.Assembly.signal_at_boundary
      have hx : 1672/10000<Geometry.x := Candidate.FourthPower.TransportBounds.ell_interval.1.trans Geometry.ell_lt_x
      have hy : 458/1000<Geometry.y := Candidate.FourthPower.TransportBounds.ly_coarse.1
      change Assembly.signal theta=Geometry.x/2+(Geometry.y-Geometry.x)/12 at hb
      linarith
    linarith
  have hcap : h+Candidate.FourthPower.ReturnCarrierInterfaces.rowPadding≤(7/8:ℝ)-1/100 := by
    have hb : h<802/1000 := Candidate.FourthPower.TransportBounds.h_interval.2
    dsimp [Candidate.FourthPower.ReturnCarrierInterfaces.rowPadding]
    linarith
  have hh := normalizedProbe_high_of_finite_nonfloor_numerator_at F.modulus ⊤ le_top
    D.N D.e (1/100) 1 2 1 Candidate.FourthPower.ReturnCarrierInterfaces.rowPadding 1 τ P.ellMin P.nu
    D.e_pos D.e_small (by norm_num) (by norm_num)
    (by norm_num [QRH.Record1252270103Return.Geometry.theta,QRH.Record1252270103Return.Geometry.h,QRH.Record1252270103Return.Geometry.ell,QRH.Record1252270103Return.Geometry.x,QRH.Record1252270103Return.Geometry.y,Candidate.FourthPower.ReturnCarrierInterfaces.rowPadding]) (by norm_num [QRH.Record1252270103Return.Geometry.theta,QRH.Record1252270103Return.Geometry.h,QRH.Record1252270103Return.Geometry.ell,QRH.Record1252270103Return.Geometry.x,QRH.Record1252270103Return.Geometry.y,Candidate.FourthPower.ReturnCarrierInterfaces.rowPadding])
    hτ (by norm_num) (by norm_num) (by norm_num) P.ellMin_pos P.nu_pos
    hβ baseline_beta F.S F.exclusions F.maximal F.first
    D.length P.slots_min D.slots_injective D.slots_sum
    (fun _=>F.w) (fun _=>F.smooth) (fun _=>F.compact) (fun _=>F.support)
    (fun _=>F.bounded) (fun _=>F.nonzero)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative
    F.complex_nonzero F.complex_nonzero P.sigma P.sigma_pos
    P.geometric_budget P.principal_budget P.window_budget hlarge
    P.eps D.t (1/200) (7/8) P.rmin P.phaseEpsilon P.phaseKappa
    D.cost P.mesh (1/100) D.t
    P.eps_pos D.t_pos.le (by norm_num) (by norm_num) (by norm_num)
    P.rmin_pos P.phaseEpsilon_pos P.phaseKappa_pos D.cost_pos.le P.mesh_pos (by norm_num)
    P.phase_budget P.phase_gap (by linarith) hτeps hcap
    P.slots_lower D.slots_small (by norm_num [QRH.Record1252270103Return.Geometry.theta,QRH.Record1252270103Return.Geometry.h,QRH.Record1252270103Return.Geometry.ell,QRH.Record1252270103Return.Geometry.x,QRH.Record1252270103Return.Geometry.y,Candidate.FourthPower.ReturnCarrierInterfaces.rowPadding,SilFourthPowerTransport.Transport.rowExtension]) P.floor_budget η hfinite
  simpa only [sourceProbe,Record1252270103Low.normalizedProbe,Record1252270103Low.normalizedProbe,SilFourthPowerTransport.Arithmetic.y,SilFourthPowerTransport.Assembly.signalShift,Assembly.signalShift,Record1252270103Return.Transport.Assembly.signalShift,Record1252270103Return.Transport.Arithmetic.x,Record1252270103Return.Transport.Arithmetic.ell,SilFourthPowerTransport.Arithmetic.x,SilFourthPowerTransport.Arithmetic.ell] using hh
end
end QRH.Record1252270103Return.GenericPhysical.FourthPowerFinalAssembly
/- END pinned source: Submissions.hailey_collet_1252270103.Record1252270103Return.Transport.FinalFixedHigh -/
