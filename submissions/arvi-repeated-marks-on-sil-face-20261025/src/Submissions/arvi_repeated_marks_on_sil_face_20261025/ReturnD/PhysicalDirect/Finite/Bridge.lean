/- Repeated marks: fork of Collet's generic return module PhysicalDirect.Finite.Bridge (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Private .874836 actual numerator specialization; predecessor attribution retained. Apache-2.0. -/
/- Source integration: PR50 8cb265dc base; PR56 67edfb7a detector affine interfaces.
   Original Hailey Collet, OpenAI and predecessor notices are retained.
   Detector affine contribution: DaysSky, with Claude assistance; Apache-2.0. -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.ReturnD.PhysicalDirect.Finite.SourceCells
import Submissions.arvi_repeated_marks_on_sil_face_20261025.ReturnD.PhysicalDirect.Finite.Transfer
import Submissions.arvi_repeated_marks_on_sil_face_20261025.ReturnD.Schedule
import Submissions.arvi_repeated_marks_on_sil_face_20261025.ReturnD.GenericScalar

                                           
                                        

set_option autoImplicit false
namespace QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect.FiniteNumerator
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
noncomputable section
set_option maxHeartbeats 200000
variable [QRH.Record1252270103Return.Geometry.Parameters] [QRH.Record1252270103Return.Geometry.BoundsR]
variable [scheme : QRH.Record1252270103Return.CountScheme] [QRH.RepeatedMarks.Return.GenericArithmetic.PhysicalSchedule]
open QRH.RepeatedMarks.Return.GenericArithmetic QRH.Record1252270103Return.GenericPhysical OAI OAI.SevenEighths
open scoped Classical BigOperators
open QRH.Record1252270103Return.GenericPhysical (baselineSource)
open Filter OAI.SevenEighths ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical
open QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect QRH.RepeatedMarks.Return.GenericPhysical.FinalAssembly OAI.SevenEighths.RepeatedMarksReturn.TransportHighTransport
open QRH.RepeatedMarks.Return.GenericPhysical.Assembly

theorem target_positive (A : ChosenData) (hgap : QRH.RepeatedMarks.Return.GenericArithmetic.theta< HeckeZeroSupremum.beta) :
    0< HeckeZeroSupremum.beta+QRH.RepeatedMarks.Return.GenericPhysical.Assembly.signalShift-A.P.sigma := by
  have ht:=A.P.t_padding
  have hs:=A.P.sigma_small
  have ha : (1/10:ℝ)< QRH.RepeatedMarks.Return.GenericArithmetic.theta+QRH.RepeatedMarks.Return.GenericPhysical.Assembly.signalShift := by
    change (1/10:ℝ)<QRH.Record1252270103Return.Geometry.theta-(5/6-QRH.Record1252270103Return.Geometry.x/3-QRH.Record1252270103Return.Geometry.ell/6)
    linarith [QRH.Record1252270103Return.Geometry.BoundsR.theta_bounds.1,QRH.Record1252270103Return.Geometry.BoundsR.ell_interval.1,QRH.Record1252270103Return.Geometry.ell_lt_x]
  linarith

/-- Actual cell bounds and actual count moments imply the literal finite cube bound. -/
theorem fixed_numerator_of_cells (hgap : QRH.RepeatedMarks.Return.GenericArithmetic.theta< HeckeZeroSupremum.beta)
    (A : ChosenData) (J : ℝ) (hcell : ActualFullWCellInput A J)
    (τ : ℝ) (hheight : HeightAdmissible A.D A.P J τ) (η : Character)
    (hcount : ∃C : ℝ,1≤ C ∧ ∀ᶠZ : ℝ in atTop,
      SourceMomentBound A.D (baselineSource A.D A.F) A.counts η Z τ
        (C*Z^A.D.t) (Z^(2*τ))) : FixedFiniteNumeratorInputAt A.D A.F A.P τ η := by
  intro n _
  obtain ⟨Cc,hCc,hcount⟩:=hcount
  obtain ⟨Cs,hCs,hcell⟩:=hcell τ hheight n η
  have hCcpos : 0< Cc:=zero_lt_one.trans_le hCc
  have hηpos : (0:ℝ)<(η.modulus.absNorm:ℝ) :=
    zero_lt_one.trans_le (HeckeLogarithmicInput.modulus_norm_ge_one η)
  let C : ℝ:=Cs*Cc*(η.modulus.absNorm:ℝ)^(2*A.P.eps)
  have hC : 0< C:=by dsimp [C];positivity
  obtain ⟨Csum,hCsum,hsum⟩:=fullW_sum_bound A τ n η C hC
  obtain ⟨Ce,hCe,herror⟩:=actual_selected_error A τ hheight.1
  change ∃Ctot : ℝ,0< Ctot ∧ ∀ᶠZ : ℝ in atTop,∀idx grid : FreeRow→ℕ,
    ActualBufferedSelection A.F.modulus ⊤ le_top A.F.S A.F.exclusions A.F.maximal
      η rowPadding A.D.e τ n Z idx grid →
    ‖finiteNonfloorNumerator A.F.modulus ⊤ A.F.S A.F.exclusions A.F.maximal A.D.length
      1 2 rowPadding A.D.e τ (fun _=>A.F.w) A.F.W A.F.W η Z idx grid‖ ≤
      Ctot*‖normalizer A.D A.F Z‖*Z^(HeckeZeroSupremum.beta+QRH.RepeatedMarks.Return.GenericPhysical.Assembly.signalShift-A.P.sigma)
  refine ⟨Csum+1,by positivity,?_⟩
  filter_upwards [hcount,hcell,hsum,herror,eventually_ge_atTop ((Ce+1)*(η.modulus.absNorm:ℝ)^2),
    eventually_ge_atTop (1:ℝ)] with Z hc hcells hs he hlarge hZ
  intro idx grid hsel
  have hcells : FullWCellsAt A τ n η C Z:=hcells Cc hCc hc
  have hb:=hs hcells idx grid hsel
  obtain ⟨hN,herr⟩:=he n η idx grid hsel
  have hZp : 0< Z:=zero_lt_one.trans_le hZ
  have hsaving : Ce*(η.modulus.absNorm:ℝ)^2*Z^(-(1:ℝ))≤1 := by
    calc
      _ ≤ Z*Z^(-(1:ℝ)) := mul_le_mul_of_nonneg_right
        (by nlinarith only [hlarge,sq_nonneg (η.modulus.absNorm:ℝ)]) (by positivity)
      _ = 1 := by rw [Real.rpow_neg_one];exact mul_inv_cancel₀ hZp.ne'
  have hone : (1:ℝ)≤ Z^(HeckeZeroSupremum.beta+QRH.RepeatedMarks.Return.GenericPhysical.Assembly.signalShift-A.P.sigma) :=
    Real.one_le_rpow hZ (target_positive A hgap).le
  let V := finiteNonfloorNumerator A.F.modulus ⊤ A.F.S A.F.exclusions A.F.maximal A.D.length
    1 2 rowPadding A.D.e τ (fun _=>A.F.w) A.F.W A.F.W η Z idx grid
  let W := fullW A.D A.F η Z (selectedRows A.D A.F Z grid)
    (fun u=>51/100+A.D.e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)
  let N := normalizer A.D A.F Z
  let E := Z^(HeckeZeroSupremum.beta+QRH.RepeatedMarks.Return.GenericPhysical.Assembly.signalShift-A.P.sigma)
  have hnormalized : ‖V/N‖≤(Csum+1)*E := by
    calc
      _ = ‖(V/N-W/N)+W/N‖ := by rw [sub_add_cancel]
      _ ≤ ‖V/N-W/N‖+‖W/N‖ := norm_add_le _ _
      _ ≤ 1+Csum*E := add_le_add (herr.trans hsaving) hb
      _ ≤ (Csum+1)*E := by dsimp [E];nlinarith only [hone]
  rw [norm_div] at hnormalized
  have hraw:=(div_le_iff₀ (norm_pos_iff.mpr hN)).mp hnormalized
  simpa only [V,N,E,mul_assoc,mul_comm,mul_left_comm] using hraw

/-- The only remaining analytic input is the initial affine moment at this fixed data. -/
theorem fixed_numerator_of_affine (hgap : QRH.RepeatedMarks.Return.GenericArithmetic.theta< HeckeZeroSupremum.beta)
    (A : ChosenData) (hAffine : Source.ActualAffineInput A) :
    ∃J : ℝ,0≤ J ∧ ∀τ : ℝ,HeightAdmissible A.D A.P J τ →
      ∀η : Character,(∃C : ℝ,1≤ C ∧ ∀ᶠZ : ℝ in atTop,
        SourceMomentBound A.D (baselineSource A.D A.F) A.counts η Z τ
          (C*Z^A.D.t) (Z^(2*τ))) → FixedFiniteNumeratorInputAt A.D A.F A.P τ η := by
  obtain ⟨J,hJ,hcells⟩:=actual_cells_of_affine hgap A hAffine
  exact ⟨J,hJ,fun τ hheight η hcount=>fixed_numerator_of_cells hgap A J hcells τ hheight η hcount⟩
end
end QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect.FiniteNumerator


