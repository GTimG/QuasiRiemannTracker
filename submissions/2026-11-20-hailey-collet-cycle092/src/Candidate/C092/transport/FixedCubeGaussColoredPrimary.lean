/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedCubeGaussColoredActual
import Candidate.C092.transport.TwistedRawSourcePrimary

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentCommonProfile CenteredMomentDivisorAllocation CenteredMomentSourceLiveColumn
open QRH.Cycle092.SignedCenter
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedCommonRestriction MixedCommonCoefficient
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance c092LocalInst_Candidate_C092_transport_FixedCubeGaussColoredPrimary_5dbc6d2b2057376d_001 {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

def coloredFullPrimaryRow (r : Source ι a b) (D : FixedCubeDatum) (ω₁ ω₂ : Character)
    (G L : Id) (B : commonAlloc r G) (ν : ι→Id→ℂ) (W₁ W₂ : ℝ→ℂ)
    (aL : Allocation L (Finset.univ : Finset (liveIndices B.val⊕Fin 2))) : ℂ :=
  TwistedRawSource.allocatedRow (idealCoeff ω₁) (idealCoeff ω₂) D.row.χ r.S r.H
    (commonLivePool r G B) (commonLiveD r G B) (commonLiveD_ne r G B) L (r.R*G) aL
    (fun i=>ν i.val) (fun i=>r.Wslot i.val) (fun i=>r.P i.val)
    W₁ W₂ b r.X₁ r.X₂ r.Y₁ r.Y₂

/-- The second full-primary allocation extracts its actual two ordinary
colors and ends in two genuinely twisted H8 rows, without character division. -/
theorem coloredFullPrimaryRow_eq_physical (r : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (D : FixedCubeDatum) (ω₁ ω₂ : Character) (G L : Id) (hG : G≠0) (hL : L≠0)
    (B : commonAlloc r G) (aL : Allocation L (Finset.univ : Finset (liveIndices B.val⊕Fin 2))) (v : ℝ) :
    coloredFullPrimaryRow r D ω₁ ω₂ G L B (shiftedSlotCoefficient r v)
      (shiftedProfile₁ r ha v) (shiftedProfile₂ r ha v) aL=
    ∑E : fullPrimaryAlloc r G B L,
      (primaryCanonicalScalar r D.row.χ G L B E (shiftedSlotCoefficient r v) aL*
        TwistedRawSource.ordinaryColor (idealCoeff ω₁) (idealCoeff ω₂) E.val)*
        coloredPrimaryPhysicalSource r ha hb D ω₁ ω₂ G L B E v := by
  unfold coloredFullPrimaryRow
  rw [TwistedRawSource.allocated_row_canonical (idealCoeff ω₁) (idealCoeff ω₂) D.row.χ r.S r.H
    (commonLivePool r G B) (fun i I hi=>r.hp i.val I hi)
    (commonLiveD r G B) (commonLiveD_ne r G B) L L (r.R*G) hL (dvd_refl L)]
  apply Finset.sum_congr rfl
  intro E _
  rw [←coloredPrimaryCanonicalSource_eq_physical r ha hb D ω₁ ω₂ G L hG hL B E v]
  unfold primaryCanonicalScalar coloredPrimaryCanonicalSource primaryOrdinaryPrefix commonLivePool
  ring

#print axioms coloredFullPrimaryRow_eq_physical
end
end QRH.Cycle092.FixedCubeGauss
