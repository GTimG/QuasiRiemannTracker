/- Own HIGH at the literal fixed-depth reachable source. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.ReachableNode
import Candidate.Research.RecursiveAffine.ActualHighNodeProducer

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentSecondInputCapacitySource CenteredMomentEnergyState
open CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentInductionEnergy CenteredMomentPrimeSlot
open CenteredMomentFirstSourceReduction CenteredMomentAllocatedRayDictionary
open Cycle63Moment Cycle63Moment.LowBranch Cycle63InitialMass Cycle63InitialSource
open Cycle153HighProvider Cycle153SourceReturn Cycle153RecursiveHighProvider

variable {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}

/-- Put the actual own HIGH record in the first terminal depth and leave
all deeper carriers empty. This is a genuine sparse suffix family. -/
def ownSuffixFamily {start : ℕ} (count : ℕ) (hcount : 0 < count)
    {eta : Character} {Z Bnorm Tz : ℝ} {root : O}
    (own : ReturnedPartAt M H hH (innerStage start).q
      (prefixDictionary (start+1)) eta Z Bnorm Tz root) :
    SuffixFamily (hH:=hH) start count eta Z Bnorm Tz root :=
  match count, hcount with
  | 0, h => False.elim (Nat.not_lt_zero _ h)
  | n+1, _ => attachSuffixFamily own 1 zero_le_one
      (fun r : Empty => nomatch r) (fun r : Empty => nomatch r)
      (fun r : Empty => nomatch r) (fun r : Empty => nomatch r)
      (fun r : Empty => nomatch r) (fun r : Empty => nomatch r)
      (fun r : Empty => nomatch r)

theorem ownSuffixFamily_value {start : ℕ} (count : ℕ) (hcount : 0 < count)
    {eta : Character} {Z Bnorm Tz : ℝ} {root : O}
    (own : ReturnedPartAt M H hH (innerStage start).q
      (prefixDictionary (start+1)) eta Z Bnorm Tz root) :
    (ownSuffixFamily count hcount own).value = own.value := by
  cases count with
  | zero => exact False.elim (Nat.not_lt_zero _ hcount)
  | succ n =>
    rw [ownSuffixFamily,attachSuffixFamily_value]
    simp only [Fintype.sum_empty,one_mul,add_zero]

variable {α : Type} [Fintype α] [DecidableEq α]
variable (hH : RayOrthogonality.globalUnits M ≤ H)
variable {C : SourceContext (α:=α) M H} {j : Fin 4} (N : ReachableNode C j)

/-- Apply the already proved native HIGH producer to the same actual
state, source coefficients, volume and prefix as the reachable LOW
continuation. `hsource` is its uniform eventual producer conclusion,
proved by `actual_high_node_producer`; no HIGH record or source energy cap
is postulated by the node or by this adapter. -/
theorem actual_reachable_own_high :
    letI : Cycle63.AffineLedger := N.ledger
    ∀ (hβlo : 51/100 ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8)
    (g : GeometryAffineLowSchedule) (ε τlow lossNeeded : ℝ)
    (Ψ : 𝓢(ℝ,ℂ)) (SH : Finset (ℕ×ℕ)) (dh : ℕ) (Kclass Kh : ℝ)
    (hsource : ActualHighNodeAt (base:=prefixDictionary j.val) (α:=α) M H hH
      C.W C.W_smooth C.W_support hβlo hβhi g (1/4) (9/4) 2 20
      C.slotMesh ε τlow C.Bnorm lossNeeded (by norm_num)
      Ψ SH dh Kclass Kh C.etaSeed C.Q C.Q_le_M C.fixed_small N.localBase)
    (hT : 2 < N.localBase^g.τ) (τT : ℝ) (hτT : τlow ≤ τT)
    (hheight : C.Tz = N.localBase^τT),
    let amp := Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑ i : N.slots, C.originalWeight i/N.unit)))
    ∃ part : ReturnedPartAt M H hH (innerStage j.val).q
      (prefixDictionary (j.val+1)) C.etaSeed N.localBase C.Bnorm C.Tz N.presentation.mult,
      part.scale = N.state.rowWidth ∧ part.length = Real.logb N.localBase (volume (N.input hH)) ∧
      part.amp = amp ∧ part.loss = lossNeeded+ε ∧
      (∀ b, (Fintype.card (part.record b).Class:ℝ) ≤ Kclass) ∧
      (ownSuffixFamily (4-j.val) (by omega) part : N.Family hH).value = part.value ∧
      GeometryAffineHighGiven (α:=N.slots) M H hH g C.etaSeed C.Q C.Q_le_M C.fixed_small
        hβlo hβhi N.localBase N.localBase_gt_one hT (1/4) (9/4)
        (N.input hH) N.profiles N.state.puncture 1 N.state.rowWidth amp Ψ
        (profile_zero_of_pos N.profiles (by norm_num) 0)
        (profile_zero_of_pos N.profiles (by norm_num) 1) SH dh N.height
        (Kh*(N.localBase^(-(N.state.rowWidth+3*g.δ-amp+ε))*part.value+1)) := by
  letI : Cycle63.AffineLedger := N.ledger
  intro hβlo hβhi g ε τlow lossNeeded Ψ SH dh Kclass Kh hsource hT τT hτT hheight amp
  rw [hheight]
  obtain ⟨part,hm,hA,ha,hl,hcard,hgiven⟩ := hsource N.localBase_gt_one hT N.slots
    (fun i => C.theta i) (fun i => C.originalWeight i/N.unit)
    (fun i => C.sigma i) (fun i => C.frequency i) (fun i => C.sigma_fixed i) N.t N.height
    (fun i => div_nonneg (C.originalWeight_nonneg i) N.unit_pos.le)
    N.weight_mesh N.height_nonneg N.frequency_bound N.state N.fixedModulus N.width_le_one
    N.profiles N.X1 N.X2 N.X1_pos N.X2_pos N.window N.presentation τT hτT N.presentation_norm
  refine ⟨part,hm,hA,ha,hl,hcard,ownSuffixFamily_value _ _ part,?_⟩
  exact hgiven

end
end OAI.SevenEighths.Cycle153Reachable

#print axioms OAI.SevenEighths.Cycle153Reachable.actual_reachable_own_high
#print axioms OAI.SevenEighths.Cycle153Reachable.ownSuffixFamily_value
