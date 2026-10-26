/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual complete family retains one common Mellin height and the full
original marked-pool avoidance required by both source branches. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalRegularNormalized
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalNestedHeights
import Submissions.hailey_collet_1252270103.Record1252270103Source.Second.RestoredNewtonBound
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentSecondHeightFamily
open CenteredMomentAmplificationChildInput CenteredMomentHeckeSlots
open CenteredMomentWholeSlotDeletion CenteredMomentHeckeExpansion
open Record1252270103Second Cycle61Moment
open QRH.Record1252270103Low QRH.Record1252270103KernelMass
open Admission.SelectedRegularSourceData Admission.SelectedHighCofactorFamily
local notation "O"=>HeckeFamily.O
local instance regularDictionaryDecidable {ι:Type*}:DecidableEq ι:=Classical.decEq _

theorem regular_datum_height {α Label:Type}[Fintype α][Fintype Label]
    {Z:ℝ}{a:Anchor α Z}(F:Family a Label)(r:F.Rows):
    (F.datum r.val.1).input.t=(F.stage r.val.1.1).t:=rfl

theorem regular_common_residual_height {α Label:Type}[Fintype α][Fintype Label]
    {Z:ℝ}{a:Anchor α Z}(F:Family a Label)(origin t u:ℝ)(second:Bool)
    (hstage:∀l,(F.stage l).t=origin)(r:F.Rows):
    residualHeight second F.datum t u r.val=mellinShift origin second t u:=by
  change (F.datum r.val.1).input.t+2*Real.pi*(u-(if second then -t else t))=_
  rw [regular_datum_height F r,hstage]
  rfl

/-- This uses every member of each original canonical pool, including terms
whose smooth coefficient vanishes. No tuple-level coprimality is substituted. -/
theorem regular_original_newton_avoidance {α:Type}[Fintype α]
    (s:Input α)(P S A:Finset (Ideal O))(Z amp ell mesh loss BD Bsource:ℝ)(depth:ℕ)
    (hpool:Pool.FixedCellPoolData P Z amp ell mesh loss BD Bsource depth)
    (slotM:Ideal O)(slotH:Subgroup (O⧸slotM)ˣ)(w:α→ℝ)
    (hslots:∀i,s.slots i=CenteredMomentPrimeSlot.primePool slotM slotH 2 (Z^(w i)))
    (hw:∀i,w i≤mesh)(hS:S⊆P)(hA:A⊆S):
    ∀i I,I∈s.slots i→IsCoprime I ((newtonDivisorPair S A).1*(newtonDivisorPair S A).2):=by
  have havoid:∀p∈P,∀i I,I∈s.slots i→¬p∣I:=by
    intro p hp i I hI
    exact hpool.avoids_canonical_slot slotM slotH (w i) (hw i) p hp I
      (by simpa only [hslots i] using hI)
  exact newton_divisor_avoids_marked s P S A hS hA hpool.prime havoid

/-- The literal final input has the original ordinary profile cutoffs. -/
theorem regular_selected_plain_upper {α:Type}[Fintype α]
    {s:Input α}{reflected second:Bool}{l:FirstSourceLabel}{C D R:Ideal O}
    (sel:Selection s reflected second l C D R):
    sel.finalInput.b₁=s.b₁ ∧ sel.finalInput.b₂=s.b₂:=by
  rcases sel with ⟨B₁,τ₁,t₁,hf₁,B₂,τ₂,t₂,hf₂,Cf,Bf,τf,tf,hff⟩
  exact ⟨rfl,rfl⟩
end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_common_residual_height
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_original_newton_avoidance
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_selected_plain_upper
