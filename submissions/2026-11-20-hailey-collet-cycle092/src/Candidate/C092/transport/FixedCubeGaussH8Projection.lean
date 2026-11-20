/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Actual fixed-arm Fourier/common/primary source identification. -/
import Candidate.C092.transport.FixedCubeGaussActual

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion FourierBridge
open CenteredMomentSecondSectorColumns CenteredMomentChildRows CenteredMomentHeckeColumnWindow
open CenteredMomentSmooth CenteredMomentRowNorm CenteredMomentChildAssembly CenteredMomentSecondScaled
open QRH.Cycle092.SignedCenter
open QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalWindow MixedCommonHeights MixedCommonCoefficient MixedCommonRestriction
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance c092LocalInst_Candidate_C092_transport_FixedCubeGaussH8Projection_b2f41bfd1895c3c8_001 {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

open CenteredMomentDivisorAllocation CenteredMomentSourceLiveColumn CenteredMomentCommonProfile

/-- Full signed L-allocation with the literal physical H8 source as endpoint. -/
theorem fullPrimaryRow_eq_physical (r : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (D : FixedCubeDatum) (G L : Id) (hG : G≠0) (hL : L≠0) (B : commonAlloc r G)
    (aL : Allocation L (Finset.univ : Finset (liveIndices B.val⊕Fin 2))) (v : ℝ) :
    fullPrimaryRow r D.row.χ G L B (shiftedSlotCoefficient r v)
      (shiftedProfile₁ r ha v) (shiftedProfile₂ r ha v) aL=
    ∑E : fullPrimaryAlloc r G B L,
      primaryCanonicalScalar r D.row.χ G L B E (shiftedSlotCoefficient r v) aL*
        primaryPhysicalSource r ha hb D G L B E v := by
  rw [fullPrimaryRow_eq_canonical]
  apply Finset.sum_congr rfl
  intro E _
  rw [primaryCanonicalSource_eq_physical r ha hb D G L hG hL B E v]

/-- All actual primary allocations and their original coefficients, before
Cauchy–Schwarz or H13/H14 losses. Every summand is a literal H8 source. -/
def fullyAllocatedPhysicalHeight (r : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (D : FixedCubeDatum) (G L : Id) (v : ℝ) : ℂ :=
  residualPhase (r.X₁*r.X₂) r.d G v*
    ∑B : commonAlloc r G,
      (frozenWeight (punctureProduct r.S r.H) B.val*
        frozenCoefficient B.val G r.R (shiftedSlotCoefficient r v) r.Wslot r.P)*
      (MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P*
        (MixedLiveNormalization.normalization (r.X₁*r.X₂) (fun i:liveIndices B.val=>r.P i.val))⁻¹)*
      ∑aL : Allocation L (Finset.univ : Finset (liveIndices B.val⊕Fin 2)),
      ∑E : fullPrimaryAlloc r G B L,
        primaryCanonicalScalar r D.row.χ G L B E (shiftedSlotCoefficient r v) aL*
          primaryPhysicalSource r ha hb D G L B E v

theorem fullyAllocatedHeight_eq_physical (r : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (D : FixedCubeDatum) (G L : Id) (hG : G≠0) (hL : L≠0) (v : ℝ) :
    fullyAllocatedHeight r ha D G L v=fullyAllocatedPhysicalHeight r ha hb D G L v := by
  unfold fullyAllocatedHeight fullyAllocatedCommonRow fullyAllocatedPhysicalHeight
  simp_rw [fullPrimaryRow_eq_physical r ha hb D G L hG hL]

/-- Direct original second fixed Gauss polynomial equals the Fourier integral
of the fully allocated literal H8 sources, with all native prefactors intact. -/
theorem source_rowPolynomial_window_physical (r : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (D : FixedCubeDatum) (η : Character) (χ : RayCharacter)
    (hη : D.η=childCharacter η χ) (hm : D.m=nativeSourceMask r)
    (G : Id) (hG : Supported G) (L : Id) (hL : Squarefree L)
    (t θ X : ℝ) (hX : 0<X) (V : ℝ→ℂ) (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V) :
    MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P*
      rowPolynomial Finset.univ (sectorElement G hG.1 (Second.Concrete.S0 r ha))
        (fun I=>divisorCoefficient L (sectorElement G hG.1 (Second.Concrete.S0 r ha))
          (movingCoefficient D.A (sectorElement G hG.1 (Second.Concrete.S0 r ha))
            (fun I=>sourceCoefficient r ha 1 (G*I)*heightCoeff η t I)) χ I*
          columnPhase V (Real.log ((Ideal.absNorm (I:Id):ℝ)/X)) θ) D.z=
      ∫ w : ℝ,columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        fullyAllocatedPhysicalHeight r ha hb D G L (t+2*Real.pi*(w-θ)) := by
  rw [source_rowPolynomial_window_fullyAllocated r ha D η χ hη hm G hG L hL t θ X hX V hVc hVs]
  apply integral_congr_ae
  filter_upwards [] with w
  rw [fullyAllocatedHeight_eq_physical r ha hb D G L hG.1 hL.ne_zero]

#print axioms fullPrimaryRow_eq_physical
#print axioms fullyAllocatedHeight_eq_physical
#print axioms source_rowPolynomial_window_physical
end
end QRH.Cycle092.FixedCubeGauss
