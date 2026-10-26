/- One fully licensed arithmetic majorant for all inner physical returns.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeWholeNodeForest

set_option autoImplicit false
set_option maxHeartbeats 300000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle153SourceReturn Cycle153Reachable Cycle153JointCount

variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}{N : ReachableNode C j}
variable {Bsrc : ℝ}{boxes : ℕ→Finset (Fin 4→ℤ)}

/-- A single whole licensed arithmetic receipt dominates every admissible
whole physical return at this node. Every terminal depth, source weight,
missing radical, path, residual factor and count witness stays together.
The majorant need not itself be an attained physical source run. -/
structure NativeArithmeticEnvelope (hH : RayOrthogonality.globalUnits M ≤ H)
    (N : ReachableNode C j)(Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ)) where
  receipt : NativeNodeForestReceipt hH N Bsrc boxes
  dominates : ∀actual : NativeNodeForestReceipt hH N Bsrc boxes,
    actual.family.value ≤ 2*receipt.family.value

/-- The genuine native coarse count bounds this ENTIRE licensed domain,
without the current node energy. The actual own-HIGH receipt supplies a
nonempty domain, including when every returned value is zero. Classical
selection is performed once on complete receipts, never per depth. -/
theorem actual_whole_arithmetic_envelope
    (hBsrc : 0 ≤ Bsrc)(hbudget : ∀d : SuffixDepth (4-j.val),
      (suffixOffset (4-j.val) d:ℝ)*Bsrc ≤ C.Bnorm)
    (hZ : 2 ≤ N.localBase)(hT : 0 ≤ C.Tz)
    (own : NativeNodeForestReceipt hH N Bsrc boxes) :
    Nonempty (NativeArithmeticEnvelope hH N Bsrc boxes) := by
  letI : Nonempty (NativeNodeForestReceipt hH N Bsrc boxes):=⟨own⟩
  obtain ⟨chosen,hchosen⟩:=actual_whole_node_forest_attainer hH N Bsrc boxes hBsrc hbudget hZ hT
    (fun actual : NativeNodeForestReceipt hH N Bsrc boxes=>actual)
  exact ⟨⟨chosen,hchosen⟩⟩

/-- Apply the SAME majorant to an actual source return after all native
operator normalizations. Dynamic bin/profile factors stay outside the
fixed source coefficient, and no second raw AtState scale is inserted. -/
theorem NativeArithmeticEnvelope.source_bound
    (envelope : NativeArithmeticEnvelope hH N Bsrc boxes)
    (actual : NativeNodeForestReceipt hH N Bsrc boxes)
    (sourceCoefficient oldTerm energy : ℝ)(hcoefficient : 0 ≤ sourceCoefficient)
    (hsource : energy ≤ oldTerm+sourceCoefficient*actual.family.value) :
    energy ≤ oldTerm+(2*sourceCoefficient)*envelope.receipt.family.value := by
  apply hsource.trans
  have h:=mul_le_mul_of_nonneg_left (envelope.dominates actual) hcoefficient
  nlinarith only [h]

/-- The actual own-HIGH family is paid by that same majorant, independent
of which actual LOW source is being estimated. -/
theorem NativeArithmeticEnvelope.own_bound
    (envelope : NativeArithmeticEnvelope hH N Bsrc boxes)
    (own : NativeNodeForestReceipt hH N Bsrc boxes)(ownValue : ℝ)
    (hown : ownValue ≤ own.family.value) :
    ownValue ≤ 2*envelope.receipt.family.value :=
  hown.trans (envelope.dominates own)

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_whole_arithmetic_envelope
#print axioms OAI.SevenEighths.Cycle153RegionalLow.NativeArithmeticEnvelope.source_bound
