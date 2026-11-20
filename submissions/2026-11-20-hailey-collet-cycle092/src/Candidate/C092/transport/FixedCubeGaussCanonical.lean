/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedCubeGaussAllocated

set_option autoImplicit false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentAddedZeroUniform CenteredMomentSourceLiveColumn CenteredMomentCommonProfile
open CenteredMomentDivisorAllocation
open QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedCommonRestriction MixedCommonCoefficient
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance c092LocalInst_Candidate_C092_transport_FixedCubeGaussCanonical_d832a35fe0d0f0f7_001 {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

/-- Residual source after the whole common G and full L-primary parts have
been extracted. The two ordinary prefixes are exactly d_j*B_j*E_j. -/
def primaryCanonicalSource (r : Source ι a b) (χ : Character) (G L : Id)
    (B : commonAlloc r G) (E : fullPrimaryAlloc r G B L)
    (ν : ι→Id→ℂ) (W₁ W₂ : ℝ→ℂ) : ℂ :=
  MixedCanonicalSource.source χ r.S r.H ((r.R*G)*L)
    (fun i:liveIndices E.val=>r.pool i.val.val)
    (fun i:liveIndices E.val=>ν i.val.val)
    (fun i:liveIndices E.val=>r.Wslot i.val.val)
    (fun i:liveIndices E.val=>r.P i.val.val)
    W₁ W₂ b r.X₁ r.X₂ r.Y₁ r.Y₂
    ((commonLiveD r G B).1*E.val (Sum.inr 0),(commonLiveD r G B).2*E.val (Sum.inr 1))

def primaryCanonicalScalar (r : Source ι a b) (χ : Character) (G L : Id)
    (B : commonAlloc r G) (E : fullPrimaryAlloc r G B L)
    (ν : ι→Id→ℂ) (aL : Allocation L (Finset.univ : Finset (liveIndices B.val⊕Fin 2))) : ℂ :=
  frozenWeight (punctureProduct r.S r.H) E.val*
    allocationTerm L Finset.univ E.val aL*idealCoeff χ (finiteTupleProduct E.val)*
    (MixedLiveNormalization.normalization (r.X₁*r.X₂) (fun i:liveIndices B.val=>r.P i.val)*
      frozenCoefficient E.val (finiteTupleProduct E.val) (r.R*G)
        (fun i:liveIndices B.val=>ν i.val) (fun i:liveIndices B.val=>r.Wslot i.val)
        (fun i:liveIndices B.val=>r.P i.val))

/-- The exact endpoint uses the native canonical source, with full puncture
R*G*L and every signed rectangle and supplying-prime mask retained. -/
theorem fullPrimaryRow_eq_canonical (r : Source ι a b) (χ : Character) (G L : Id)
    (B : commonAlloc r G) (ν : ι→Id→ℂ) (W₁ W₂ : ℝ→ℂ)
    (aL : Allocation L (Finset.univ : Finset (liveIndices B.val⊕Fin 2))) :
    fullPrimaryRow r χ G L B ν W₁ W₂ aL=
      ∑E : fullPrimaryAlloc r G B L,
        primaryCanonicalScalar r χ G L B E ν aL*primaryCanonicalSource r χ G L B E ν W₁ W₂ := by
  unfold fullPrimaryRow
  apply Finset.sum_congr rfl
  intro E _
  rw [MixedAllocationSource.frozenRow,MixedFrozenSource.live_sum_eq_source]
  unfold primaryCanonicalScalar primaryCanonicalSource commonLivePool
  ring

#print axioms fullPrimaryRow_eq_canonical
end
end QRH.Cycle092.FixedCubeGauss
