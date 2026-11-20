/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedCubeGaussColoredFourier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve FourierBridge
open CenteredMomentLattice CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondActivePhysicalDictionary CenteredMomentActiveSource
open QRH.Cycle092.SignedCenter
open QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalWindow MixedHeightEnergy MixedCommonHeights MixedCommonRestriction
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance c092LocalInst_Candidate_C092_transport_FixedCubeGaussColoredShift_cbfe3389a83c4e4a_001 {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

def coloredProjectedColumn (r : Source ι a b) (ω₁ ω₂ : Id→ℂ)
    (ν : ι→Id→ℂ) (W₁ W₂ : ℝ→ℂ) : Id→ℂ :=
  TwistedRawSource.coloredColumn (Fintype.piFinset (sourcePools r)) (punctureProduct r.S r.H) ω₁ ω₂
    (profileCoefficient r.R ν r.Wslot r.P W₁ W₂ r.X₁ r.X₂ r.Y₁ r.Y₂ r.d.1 r.d.2 1)

lemma coloredSourceColumn_eq_projected (r : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id→ℂ) :
    TwistedRawSource.sourceColumn r ha ω₁ ω₂ 1=
      coloredProjectedColumn r ω₁ ω₂ r.ν (sourceProfile₁ r ha) (sourceProfile₂ r ha) := by
  unfold TwistedRawSource.sourceColumn coloredProjectedColumn TwistedRawSource.coloredColumn
  congr 1
  funext v
  unfold MixedOriginalSecondZero.originalTuple TwistedRawSource.coloredTuple sourceProfile₁ sourceProfile₂
  ring

/-- The native common Fourier shift preserves both independent arithmetic
colors, including their true zero values. -/
theorem coloredSourceColumn_height_shift (r : Source ι a b) (ha : 0<a)
    (ω₁ ω₂ : Id→ℂ) (G I : Id) (hG : G≠0) (hI : I≠0) (v : ℝ) :
    TwistedRawSource.sourceColumn r ha ω₁ ω₂ 1 (G*I)*(Ideal.absNorm I:ℂ)^(Complex.I*v)=
      residualPhase (r.X₁*r.X₂) r.d G v*
        coloredProjectedColumn r ω₁ ω₂ (shiftedSlotCoefficient r v)
          (shiftedProfile₁ r ha v) (shiftedProfile₂ r ha v) (G*I) := by
  have hdec : (MixedCommonHeights.instDecidableEqSumFinOfNatNat_submissions : DecidableEq (ι⊕Fin 2))=
      (inferInstance : DecidableEq (ι⊕Fin 2)) := Subsingleton.elim _ _
  have hQ : ∀u∈Fintype.piFinset (sourcePools r),∀j,u j≠0 := by
    intro u hu j
    exact MixedLiteralAllocation.source_pools_nonzero r.pool r.hp r.d r.hd b r.X₁ r.X₂ r.Y₁ r.Y₂
      j _ (Fintype.mem_piFinset.mp hu j)
  have hh := residual_column_height (Fintype.piFinset (sourcePools r)) hQ
    (fun u=>MixedCommonCoefficient.tupleWeight (punctureProduct r.S r.H) u*
      TwistedRawSource.ordinaryColor ω₁ ω₂ u) r.R 1 G hG
    r.ν r.Wslot r.P (sourceProfile₁ r ha) (sourceProfile₂ r ha) 0 0 v
    r.X₁ r.X₂ r.Y₁ r.Y₂ (r.hL.trans_le r.hX₁) (r.hL.trans_le r.hX₂)
    (r.hL.trans_le r.hY₁) (r.hL.trans_le r.hY₂) (r.hpX.trans r.hpY.symm) r.d r.hd I
  rw [phaseProfile_zero,phaseProfile_zero,idealHeight_normPower v I hI] at hh
  rw [coloredSourceColumn_eq_projected]
  unfold coloredProjectedColumn TwistedRawSource.coloredColumn TwistedRawSource.coloredTuple
  dsimp only [shiftedSlotCoefficient,shiftedProfile₁,shiftedProfile₂,sourceProfile₁,sourceProfile₂,
    sourcePools,MixedPrincipalAllocations.tuplePools]
  simp only [sourceProfile₁,sourceProfile₂,sourcePools,MixedPrincipalAllocations.tuplePools,zero_add] at hh
  convert hh using 1
  rfl

#print axioms coloredSourceColumn_eq_projected
#print axioms coloredSourceColumn_height_shift
end
end QRH.Cycle092.FixedCubeGauss
