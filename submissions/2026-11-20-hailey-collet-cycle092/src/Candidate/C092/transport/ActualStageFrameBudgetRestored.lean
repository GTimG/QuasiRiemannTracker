/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual collision/inverse family supplies the early frame-bank metadata
and the unchanged original homogeneous profile/height amplitude. -/
import Candidate.C092.transport.ActualStageFrameBudgetProducer
import Candidate.C092.transport.OrderedPairActualRestoredFamily
import Candidate.C092.transport.FirstRootCompleteCaps
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily
open QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedFirstProfileEnvelope
open NativeMaskedEnergy
open MixedCanonicalSource RestoredRootDictionary RestoredInitialSource RepairedSourceSideSupply
open QRH.SilDensitySplit.CubeFree.FP.RestorationFamily
open QRH.SilDensitySplit.CubeFree.FP.RestorationCollisionEnergy
open Candidate.FourthPower.KernelCollisionEnergy Candidate.FourthPower.NativeFiniteHoles
open QRH.Record1252270103KernelMass QRH.Record1252270103TwoIdeal
open QRH.Cycle092.OrderedPairActualRestored QRH.Cycle092.FixedFramePacking
open QRH.Cycle092.TwistedRawBallRootProducer
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O
variable {α:Type}[Fintype α]

/-- The bound is fixed from the original slot type, before any actual
restoration tuple, injective prime map or selected first allocation. -/
theorem actual_restoration_holes (N:ℕ)(hN:Fintype.card α ≤ N)(r:Setoid α)
    (Z:ℝ)(tc:{q // ¬singletonBlock r q}→primeEnclosure Z)
    (A:Finset {q // singletonBlock r q})(ti:A→primeEnclosure Z) :
    (restorationHoles r (primeEnclosure Z) tc A ti).card ≤ 2*N :=
  (restoration_holes_card r _ tc A ti).trans (Nat.mul_le_mul_left 2 hN)

/-- Width is inherited from the SAME original mark array. No positive
minimum width or new descriptor family is introduced. -/
theorem actual_survivor_width (r:Setoid α)(A:Finset {q // singletonBlock r q})
    (w:α→ℝ)(hw:∀i,0 ≤ w i) : (∑i:remainingSet r A,w i.val) ≤ ∑i,w i :=
  width_injected ⟨Subtype.val,Subtype.val_injective⟩ w hw

variable (M:Id)[NeZero M](Hr:Subgroup (O⧸M)ˣ)(hHr:RayOrthogonality.globalUnits M ≤ Hr)
variable (r:RestoredRootSource.Data M Hr α)
variable (X₁ X₂ Y₁ Y₂ t₁ t₂:ℝ)(d:IdealPair)(g:DividedLengths r.Z X₁ X₂ Y₁ Y₂ d)
local notation "s"=>dividedCanonicalSource M Hr hHr r X₁ X₂ Y₁ Y₂ t₁ t₂ d g

/-- This is exactly the amplitude requested at the original phase-aligned
endpoint, on every actual divided canonical child. -/
theorem actual_divided_amplitude (height:ℝ)(degree:ℕ)(controls:Finset (ℕ×ℕ)) :
    amplitude s 0 height degree controls 1 =
      (r.p.control controls)^2*(1+|t₁|+|t₂|+height)^degree := by
  change 1*(r.p.control controls)^2*(1+|0|+height+‖t₁‖+‖t₂‖)^degree = _
  simp only [abs_zero,Real.norm_eq_abs,add_zero,one_mul]
  congr 1
  ring

#print axioms actual_restoration_holes
#print axioms actual_survivor_width
#print axioms actual_divided_amplitude
end
end QRH.Cycle092.ActualStageFrameBudget
