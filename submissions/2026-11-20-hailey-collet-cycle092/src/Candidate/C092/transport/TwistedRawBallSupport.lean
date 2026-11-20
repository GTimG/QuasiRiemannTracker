/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Source support comes from actual colored tuple witnesses, never old aggregate cancellation. -/
import Candidate.C092.transport.TwistedRawBallCoefficient
set_option autoImplicit false
namespace QRH.Cycle092.TwistedRawBall
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSupportedZeroEnergy
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open QRH.Cycle092.TwistedRawSource
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance (priority := 2000) sumSupportDecEq {κ κ₂ : Type*} :
    DecidableEq (κ ⊕ κ₂) := Classical.decEq _

theorem source_fifth_free (s : Source ι a b) (ha : 0 < a)
    (ω₁ ω₂ : Id → ℂ) (seed I : Id) (hne : sourceColumn s ha ω₁ ω₂ seed I ≠ 0) :
    Candidate.FourthPower.SexticSieve.PowerFree 3 I := by
  obtain ⟨v,hv,hn,hprod⟩ := finiteColumnCoefficient_witness
    (Fintype.piFinset (MixedPrincipalAllocations.tuplePools s))
    (fun v => MixedOriginalSecondZero.originalTuple s ha seed v * ordinaryColor ω₁ ω₂ v) I hne
  have htw : MixedCommonCoefficient.tupleWeight (MixedCommonRestriction.punctureProduct s.S s.H) v ≠ 0 := by
    intro hz
    exact hn (by simp only [MixedOriginalSecondZero.originalTuple,hz,zero_mul])
  have hr : MixedCommonAllocation.tupleRestriction (MixedCommonRestriction.punctureProduct s.S s.H) v := by
    by_contra hh
    exact htw (by simp only [MixedCommonCoefficient.tupleWeight,hh,ite_false])
  rw [← hprod]
  have hs := MixedLiteralAllocation.source_pools_nonzero s.pool s.hp s.d s.hd b s.X₁ s.X₂ s.Y₁ s.Y₂
  exact MixedArtificialRestriction.restricted_tuple_fifth_free _ v
    (fun j => hs j _ (Fintype.mem_piFinset.mp hv j))
    (fun i => s.hp i _ (Fintype.mem_piFinset.mp hv (Sum.inl i))) hr

#print axioms source_fifth_free
end
end QRH.Cycle092.TwistedRawBall
