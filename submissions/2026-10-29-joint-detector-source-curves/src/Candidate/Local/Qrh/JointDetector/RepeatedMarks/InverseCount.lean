/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Cycle63.Marked.DeletionInverseOverlap
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorPlainFiberCount

/-! An inverse witness count with an arbitrary fixed common product.
The lower response is used literally; no individual-slot amplitude cap
or disjoint-support hypothesis enters this adapter. -/
namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Set OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount
theorem inverse_fiber_count_of_response {Row Label : Type*}
    (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U) (ha : 1/2≤a)
    (witness : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u∈rows,(witness u).label=label)
    (hJ : ∀ u∈rows,(witness u).left=J) (hK : ∀ u∈rows,(witness u).right=K)
    (Q : Row → ℂ) (v z slotLoss εm C height : ℝ)
    (hspike : ∀ u ∈ rows, U^(v*z-slotLoss) ≤ ‖Q u‖^2)
    (hC : 0≤C) (hheight : 0≤height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hraw : ∀ n : ℕ,n≤2 → ∀ σ∈Icc (0 : ℝ) 1,∀ freq∈Icc (-height) height,
        ∑ u∈rows,‖polynomial (χ u label) true
          ((logProfile^[n]) (inverseTest U tstar (Real.logb U ((2 : ℝ)^J.val))))
          (U^(Real.logb U ((2 : ℝ)^J.val))) σ freq*
            Q u‖^2≤C*U^(1+εm)) :
    (rows.card : ℝ) ≤ (12*(1+height)*C)*
      U^(1-(2*a-1)*Real.logb U ((2 : ℝ)^J.val)-v*z+2*ε+slotLoss+εm) := by
  let r := Real.logb U ((2 : ℝ)^J.val)
  have hsp := HeckeDetectorFiberSpikes.fiber_spikes rows χ U a ε tstar T allowance i hU
    (by linarith) witness label J K hlabel hJ hK
  have hUp : 0<U := zero_lt_one.trans hU
  have hDp : 0<U^r := Real.rpow_pos_of_pos hUp _
  have hE : 0≤C*U^(1+εm) := mul_nonneg hC (Real.rpow_nonneg hUp.le _)
  have he := HeckeDetectorFiberEnergy.inverse_energy rows χ U a ε tstar T allowance i
    (by linarith) witness label (inverseTest U tstar r) (U^r) (1/4) (9/4) (C*U^(1+εm))
    Q hDp (by norm_num)
    (HeckeDetectorDyadicActual.inverse_profile_support _ _) hE height hheight hfreq
    hraw
  have he' : ∑ u∈rows,
      ‖polynomial (χ u label) true (inverseTest U tstar r) (U^r) (witness u).zero.re
        (witness u).frequency*Q u‖^2≤
      (12*(1+height)*C)*U^(1+εm) := by
    convert he using 1; ring
  have hc := HeckeDetectorRowCount.inverse_count rows (fun u => χ u label)
    (inverseTest U tstar r) (U^r) (fun u => (witness u).zero.re) (fun u => (witness u).frequency)
    Q
    U (2*a-1) r (v/2) z (2*ε) slotLoss εm
    (12*(1+height)*C) hUp (fun u hu => (hsp u hu).2.2.1) (by intro u hu; convert hspike u hu using 1 <;> congr 2 <;> ring) he'
  convert hc using 1 <;> dsimp [r] <;> congr 2 <;> ring

theorem plain_fiber_count_of_response {Row Label : Type*}
    (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U) (ha : 1/2≤a)
    (witness : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u∈rows,(witness u).label=label)
    (hJ : ∀ u∈rows,(witness u).left=J) (hK : ∀ u∈rows,(witness u).right=K)
    (Q : Row → ℂ) (v z slotLoss εm C height : ℝ)
    (hspike : ∀ u ∈ rows, U^(v*z-slotLoss) ≤ ‖Q u‖^2)
    (hC : 0≤C) (hheight : 0≤height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hraw : ∀ j k : ℕ, j+k≤2 → ∀ σ∈Icc (0 : ℝ) 1,∀ freq∈Icc (-height) height,
        ∑ u∈rows,‖polynomial (χ u label) false ((logProfile^[j]) positiveAnnular)
          (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*
          polynomial (χ u label) false ((logProfile^[k]) positiveAnnular)
          (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*Q u‖^2≤C*U^(1+εm)) :
    (rows.card : ℝ) ≤ (192*(1+height)*C)*
      U^(1-2*(2*a-1)*Real.logb U ((2 : ℝ)^K.val)-v*z+4*ε+slotLoss+εm) := by
  let r := Real.logb U ((2 : ℝ)^K.val)
  have hsp := HeckeDetectorFiberSpikes.fiber_spikes rows χ U a ε tstar T allowance i hU
    (by linarith) witness label J K hlabel hJ hK
  have hUp : 0<U := zero_lt_one.trans hU
  have hDp : 0<U^r := Real.rpow_pos_of_pos hUp _
  have hE : 0≤C*U^(1+εm) := mul_nonneg hC (Real.rpow_nonneg hUp.le _)
  have he := HeckeDetectorFiberEnergy.plain_energy rows χ U a ε tstar T allowance i
    (by linarith) witness label positiveAnnular (U^r) (1/4) (9/4) (C*U^(1+εm))
    Q hDp (by norm_num) positiveAnnular_support hE height hheight hfreq hraw
  have he' : ∑ u∈rows,
      ‖polynomial (χ u label) false positiveAnnular (U^r) (witness u).zero.re (witness u).frequency*
        polynomial (χ u label) false positiveAnnular (U^r) (witness u).zero.re (witness u).frequency*
        Q u‖^2≤ (192*(1+height)*C)*U^(1+εm) := by
    convert he using 1; ring
  have hc := HeckeDetectorRowCount.plain_count rows (fun u => χ u label)
    positiveAnnular (U^r) (fun u => (witness u).zero.re) (fun u => (witness u).frequency)
    Q
    U (2*a-1) r (v/2) z (2*ε) slotLoss εm
    (192*(1+height)*C) hUp (fun u hu => (hsp u hu).2.2.2) (by intro u hu; convert hspike u hu using 1 <;> congr 2 <;> ring) he'
  convert hc using 1 <;> dsimp [r] <;> congr 2 <;> ring

end
end Qrh.JointDetector.RepeatedMarks
