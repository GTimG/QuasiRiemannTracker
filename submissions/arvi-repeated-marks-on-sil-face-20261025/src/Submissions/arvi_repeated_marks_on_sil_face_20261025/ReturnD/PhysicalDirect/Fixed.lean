/- Repeated marks: fork of Collet's generic return module PhysicalDirect.Fixed (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Adapted from Zhongpai Gao Target830 physical closure, inherited OpenAI/Hailey Collet; Apache-2.0. -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.ReturnD.Schedule
import Submissions.arvi_repeated_marks_on_sil_face_20261025.ReturnD.PhysicalDirect.Retained
import Submissions.hailey_collet_1252270103.Cycle25.Energy.Physical.RetainedFixed
noncomputable section
set_option autoImplicit false
open OAI.SevenEighths.CenteredMomentDetectorPlainFiberSource
open scoped Classical BigOperators SchwartzMap
open Filter
open QRH.Record1252270103Return

namespace QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Geometry.BoundsR] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open QRH.RepeatedMarks.Return.GenericArithmetic OAI OAI.SevenEighths
open Cycle25WeightedNumeratorPhysical QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect
open CenteredMomentDetectorPlainFiberSource CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentRetainedWeightedSource CenteredMomentUniformReflectionApproximation
local notation "O" => HeckeFamily.O
set_option maxHeartbeats 200000

/-- Fixed source profile version with all restoration and logarithmic losses
absorbed into any prescribed positive exponent loss. The constant is independent
of rowwise coefficient choices and all amplitude/count constants. -/
theorem affine_retained_fixed_profile {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (κ : ℝ) (hκlo : 7/10 ≤ κ) (hκhi : κ ≤ 3/4)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ κ)
    (bΦ mesh affineError : ℝ) (hAffineError : 0< affineError)
    (hsΦ : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0< Ci)
    (hinput : ∀ᶠU:ℝ in atTop,AffineAt F bΦ mesh affineError U di control Ci)
    (G:𝓢(ℝ,ℂ)) (loss Cscale Ccond xi:ℝ)
    (hloss:0 < loss) (hCscale:0 < Cscale) (hCcond:0 < Ccond) (hxi:0 < xi) :
    ∃degree:ℕ, ∃C:ℝ, 0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀rows:Finset FreeRow,
      (∀u∈rows, U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀(τ ψ:rows→Character) (X:rows→ℝ) (m:ℝ),
      (∀i, ∀n:O, elementCoeff (rowCharacter F.S F.exclusions.prime i.val) n = elementCoeff (τ i) n) →
      (∀i, 0 < X i) → 0 ≤ m → m+xi ≤ 2 →
      (∀i, (Ideal.absNorm (∏P∈sourcePrimes (τ i) (ψ i),P):ℝ) ≤ Ccond*U) →
      (∀i, ((ψ i).modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈sourcePrimes (τ i) (ψ i),P):ℝ)
        ≤ Cscale*U^m*X i) →
      ∀T:Finset (Fin D.N), ∀width:T→ℝ, ∀z:T→ℂ, ∀height:ℝ,
      (∀i, 0 ≤ width i) →
      (∀i,width i≤ mesh) →
      (∀i, width i ≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)) →
      (∀i, (z i).re = 17/50) → 0 ≤ height → (∀i, |(z i).im| ≤ height) →
      ((∃d t:ℝ,GenericArithmetic.dm≤ d ∧ d≤ GenericArithmetic.dp ∧
        0≤ t ∧ m+xi=plainScale d t ∧
        (∑i,width i)≤ clippedCapacity d t) ∨
        (2*(m+xi)+6*κ*(∑i,width i)≤1 ∨ T=∅)) →
      (∑i:rows, ‖retainedSchwartz (τ i) (ψ i) G (X i) (U^(xi/4))‖^4 *
        ‖∏s,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(width s)) (z s)‖^2)
        ≤ C*(1+height)^degree*U^(1+D.t+affineError+loss) := by
  obtain ⟨degree,H,Cr,hCr,hr⟩ := affine_actual_retained_fourth F κ hκlo hκhi hbeta hκbeta
    bΦ mesh affineError hAffineError hsΦ di control Ci hCi hinput (loss/2) Cscale xi
    (by linarith) hCscale hxi
  let B := 1+H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G
  let K := max 1 Ccond
  have hB : 0 < B := by have := apply_nonneg (H.sup (schwartzSeminormFamily ℝ ℝ ℂ)) G; dsimp [B]; linarith
  have hK : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  refine ⟨degree,25*Cr*K^(loss/2)*B^4,by positivity,?_⟩
  filter_upwards [hr,eventually_retained_log_cost loss hloss] with U hr hl
  have hU := hr.1
  have hUp := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows τ ψ X m he hX hm hmmax hred hcombined T width z height
    hw hwmesh hwmax hreal hh him hcapacity
  have hRcap : 1 ≤ K*U := by nlinarith
  have hred' (i:rows) : (Ideal.absNorm (∏P∈sourcePrimes (τ i) (ψ i),P):ℝ) ≤ K*U :=
    (hred i).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hUp.le)
  have hGB (i:rows) : H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G ≤ B := by dsimp [B]; linarith
  have hb := hr.2 rows hrows τ ψ (fun _=>G) X m B (K*U) he hX hm hmmax hB hGB
    hRcap hred' hcombined T width z height hw hwmesh hwmax hreal hh him hcapacity
  have hlog := hl.2 (m+xi) (by linarith) hmmax
  apply hb.trans
  calc
    _ ≤ Cr*(K*U)^(loss/2)*B^4*(25*U^(loss/2))*(1+height)^degree*U^(1+D.t+affineError) := by
      gcongr
    _ = _ := by
      rw [Real.mul_rpow hKpos.le hUp.le]
      calc
        _ = (25*Cr*K^(loss/2)*B^4)*(1+height)^degree*
            (U^(loss/2)*U^(loss/2)*U^(1+D.t+affineError)) := by ring
        _ = _ := by rw [←Real.rpow_add hUp,←Real.rpow_add hUp]; congr 2; ring

end QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect
end

/- Adapted from Cycle25 retained profile restoration, Apache-2.0. -/

