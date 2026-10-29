/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.FiberCount

/-! The short actual detector fiber uses the literal Möbius inverse witness
and two literal plain witnesses. Its repeated products are common on the
fiber; their moment estimates and lower responses remain explicit. -/
namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped Classical BigOperators
open Set OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount

private theorem plain_capacity_identity (B L c ν v m : ℝ) (hv : 0 ≤ v) :
    1-2*ν*m-v*min c ((B-2*m)/L) =
      max (plainCapArm c ν v m) (plainBudgetArm B L ν v m) := by
  have hform : 1-2*ν*m-v*((B-2*m)/L) = plainBudgetArm B L ν v m := by
    unfold plainBudgetArm
    ring
  by_cases h : c ≤ (B-2*m)/L
  · rw [min_eq_left h, max_eq_left]
    · unfold plainCapArm; ring
    · rw [← hform]
      unfold plainCapArm
      nlinarith [mul_le_mul_of_nonneg_left h hv]
  · rw [min_eq_right (le_of_not_ge h), max_eq_right]
    · exact hform
    · rw [← hform]
      unfold plainCapArm
      nlinarith [mul_le_mul_of_nonneg_left (le_of_not_ge h) hv]

theorem short_actual_fiber_count {Row Label : Type*}
    (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U) (ha : 1/2≤a)
    (witness : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u∈rows,(witness u).label=label)
    (hJ : ∀ u∈rows,(witness u).left=J) (hK : ∀ u∈rows,(witness u).right=K)
    (QI QP : Row → ℂ) (B L c v τ slotLoss εm C height lengthLoss : ℝ)
    (hC : 0≤C) (hheight : 0≤height) (hε : 0≤ε)
    (hν : 0 < 2*a-1) (hνhi : 2*a-1 ≤ 3/4) (hv0 : 0≤v) (hv : v≤2*a-1)
    (hB0 : 0≤B) (hB : B≤1) (hL : 3/2≤L) (hlen0 : 0≤lengthLoss)
    (hlength : max (crossingCut (2*a-1) (v/(2*(2*a-1))) 2 (2*(v/(2*(2*a-1)))*c))
      (crossingCut (2*a-1) (v/(2*(2*a-1))) (2-4*(v/(2*(2*a-1)))/L)
        (2*(v/(2*(2*a-1)))*B/L)) ≤
      Real.logb U ((2:ℝ)^J.val)+Real.logb U ((2:ℝ)^K.val)+lengthLoss)
    (hspikeI : ∀ u ∈ rows,
      U^(v*((1-Real.logb U ((2:ℝ)^J.val))/2-τ)-slotLoss) ≤ ‖QI u‖^2)
    (hspikeP : ∀ u ∈ rows,
      U^(v*(min c ((B-2*Real.logb U ((2:ℝ)^K.val))/L)-τ)-slotLoss) ≤ ‖QP u‖^2)
    (hfreq : 2*Real.pi*allowance+(3*i:ℕ)*T≤height)
    (hrawI : ∀ n : ℕ,n≤2 → ∀ σ∈Icc (0:ℝ) 1,∀ freq∈Icc (-height) height,
      ∑ u∈rows,‖polynomial (χ u label) true
        ((logProfile^[n]) (inverseTest U tstar (Real.logb U ((2:ℝ)^J.val))))
        (U^(Real.logb U ((2:ℝ)^J.val))) σ freq*QI u‖^2≤C*U^(1+εm))
    (hrawP : ∀ j k : ℕ,j+k≤2 → ∀ σ∈Icc (0:ℝ) 1,∀ freq∈Icc (-height) height,
      ∑ u∈rows,‖polynomial (χ u label) false ((logProfile^[j]) positiveAnnular)
        (U^(Real.logb U ((2:ℝ)^K.val))) σ freq*
        polynomial (χ u label) false ((logProfile^[k]) positiveAnnular)
        (U^(Real.logb U ((2:ℝ)^K.val))) σ freq*QP u‖^2≤C*U^(1+εm)) :
    (rows.card:ℝ) ≤ (192*(1+height)*C)*
      U^(rawRepeatedCountRate B L c (2*a-1) v+(2*a-1)*lengthLoss+
        (v*τ+4*ε+slotLoss+εm)) := by
  let r := Real.logb U ((2:ℝ)^J.val)
  let m := Real.logb U ((2:ℝ)^K.val)
  let loss := v*τ+4*ε+slotLoss+εm
  let C' := 192*(1+height)*C
  have hUp : 0<U := zero_lt_one.trans hU
  have hC' : 0≤C' := by dsimp [C']; positivity
  have hi := inverse_fiber_count_of_response rows χ U a ε tstar T allowance i hU ha
    witness label J K hlabel hJ hK QI v ((1-r)/2-τ) slotLoss εm C height
    hspikeI hC hheight hfreq hrawI
  have hp := plain_fiber_count_of_response rows χ U a ε tstar T allowance i hU ha
    witness label J K hlabel hJ hK QP v (min c ((B-2*m)/L)-τ) slotLoss εm C height
    hspikeP hC hheight hfreq hrawP
  have hi' : (rows.card:ℝ) ≤ C'*U^(inverseArm (2*a-1) v r+loss) := by
    apply hi.trans
    apply mul_le_mul
    · dsimp [C']; nlinarith
    · apply Real.rpow_le_rpow_of_exponent_le hU.le
      dsimp [inverseArm, loss,r]
      nlinarith
    · exact (Real.rpow_pos_of_pos hUp _).le
    · exact hC'
  have hp' : (rows.card:ℝ) ≤ C'*U^(max (plainCapArm c (2*a-1) v m)
      (plainBudgetArm B L (2*a-1) v m)+loss) := by
    convert hp using 1
    dsimp [C',loss,m]
    congr 2
    rw [← plain_capacity_identity B L c (2*a-1) v _ hv0]
    ring
  exact short_fiber_count hU.le hC' hν hνhi hv0 hv hB0 hB hL hlen0 hlength hi' hp'

end
end Qrh.JointDetector.RepeatedMarks
