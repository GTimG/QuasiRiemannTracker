/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedCubeGaussColoredShift
import Candidate.C092.transport.FixedCubeGaussColoredPayments
import Candidate.C092.transport.FixedCubeGaussColoredNativePrimary
import Candidate.C092.transport.TwistedRawSourceClosure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion FourierBridge
open CenteredMomentSecondSectorColumns CenteredMomentChildRows CenteredMomentHeckeColumnWindow
open CenteredMomentSmooth CenteredMomentChildAssembly CenteredMomentSecondScaled
open CenteredMomentRowNorm CenteredMomentSourceLiveColumn CenteredMomentCommonProfile CenteredMomentDivisorAllocation
open QRH.Cycle092.SignedCenter
open QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalWindow MixedCommonHeights MixedCommonCoefficient MixedCommonRestriction
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance c092LocalInst_Candidate_C092_transport_FixedCubeGaussColoredH8Projection_7a0b78487f1d1abb_001 {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

def coloredNativePrimaryPhysicalRow (r : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (D : FixedCubeDatum) (ω₁ ω₂ : Character) (G L : Id)
    (B : TwistedRawSource.commonAllocations r G)
    (aL : Allocation L (Finset.univ : Finset (liveIndices B.val⊕Fin 2))) (v : ℝ) : ℂ :=
  ∑E : TwistedRawSource.primaryAllocations r G B L,
    TwistedRawSource.primaryCanonicalScalar r (idealCoeff ω₁) (idealCoeff ω₂) D.row.χ
      G L B E (shiftedSlotCoefficient r v) aL*
      coloredNativePrimaryPhysicalSource r ha hb D ω₁ ω₂ G L B E v

lemma coloredNativeFullPrimaryRow_eq_physical (r : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (D : FixedCubeDatum) (ω₁ ω₂ : Character) (G L : Id) (hG : G≠0) (hL : L≠0)
    (B : TwistedRawSource.commonAllocations r G)
    (aL : Allocation L (Finset.univ : Finset (liveIndices B.val⊕Fin 2))) (v : ℝ) :
    TwistedRawSource.fullPrimaryRow r (idealCoeff ω₁) (idealCoeff ω₂) D.row.χ G L B
      (shiftedSlotCoefficient r v) (shiftedProfile₁ r ha v) (shiftedProfile₂ r ha v) aL=
    coloredNativePrimaryPhysicalRow r ha hb D ω₁ ω₂ G L B aL v := by
  unfold TwistedRawSource.fullPrimaryRow coloredNativePrimaryPhysicalRow
  apply Finset.sum_congr rfl
  intro E _
  exact congrArg (fun z:ℂ=>TwistedRawSource.primaryCanonicalScalar r (idealCoeff ω₁) (idealCoeff ω₂)
    D.row.χ G L B E (shiftedSlotCoefficient r v) aL*z)
    (coloredNativePrimaryCanonical_eq_physical r ha hb D ω₁ ω₂ G L hG hL B E v)

/-- Original common and full-primary scalar factors with their actual two
ordinary colors. Each final source uses two genuinely twisted fixed rows. -/
def coloredFullyAllocatedPhysicalHeight (r : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (D : FixedCubeDatum) (ω₁ ω₂ : Character) (G L : Id) (v : ℝ) : ℂ :=
  residualPhase (r.X₁*r.X₂) r.d G v*
    ∑B : TwistedRawSource.commonAllocations r G,
      (frozenWeight (punctureProduct r.S r.H) B.val*
        TwistedRawSource.ordinaryColor (idealCoeff ω₁) (idealCoeff ω₂) B.val*
        frozenCoefficient B.val G r.R (shiftedSlotCoefficient r v) r.Wslot r.P)*
      (MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P*
        (MixedLiveNormalization.normalization (r.X₁*r.X₂) (fun i:liveIndices B.val=>r.P i.val))⁻¹)*
      ∑aL : Allocation L (Finset.univ : Finset (liveIndices B.val⊕Fin 2)),
        coloredNativePrimaryPhysicalRow r ha hb D ω₁ ω₂ G L B aL v

theorem colored_allocated_height_eq_physical (r : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (D : FixedCubeDatum) (ω₁ ω₂ : Character) (G L : Id) (hG : G≠0) (hL : L≠0) (v : ℝ) :
    residualPhase (r.X₁*r.X₂) r.d G v*
      TwistedRawSource.fullyAllocatedCommonRow r (idealCoeff ω₁) (idealCoeff ω₂) D.row.χ G L
        (shiftedSlotCoefficient r v) (shiftedProfile₁ r ha v) (shiftedProfile₂ r ha v)=
      coloredFullyAllocatedPhysicalHeight r ha hb D ω₁ ω₂ G L v := by
  unfold TwistedRawSource.fullyAllocatedCommonRow coloredFullyAllocatedPhysicalHeight
  simp_rw [coloredNativeFullPrimaryRow_eq_physical r ha hb D ω₁ ω₂ G L hG hL]

/-- Actual colored sector height, with both fixed characters retained under
all native allocation projectors. -/
theorem coloredSectorFixedHeight_eq_physical (r : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (D : FixedCubeDatum) (ω₁ ω₂ : Character) (G : Id) (hG : Supported G)
    (L : Id) (hL : Squarefree L) (v : ℝ) :
    MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P*
      coloredSectorFixedHeight r ha (idealCoeff ω₁) (idealCoeff ω₂) D G hG L v=
      coloredFullyAllocatedPhysicalHeight r ha hb D ω₁ ω₂ G L v := by
  unfold coloredSectorFixedHeight
  have he (I : sectorPool G hG.1 (sourceColumns r)) :
      (if L∣(I:Id) then TwistedRawSource.sourceColumn r ha (idealCoeff ω₁) (idealCoeff ω₂) 1 (G*I) else 0)*
        heightCoeff D.row.χ v I=
      residualPhase (r.X₁*r.X₂) r.d G v*
        ((if L∣(I:Id) then coloredProjectedColumn r (idealCoeff ω₁) (idealCoeff ω₂)
          (shiftedSlotCoefficient r v) (shiftedProfile₁ r ha v) (shiftedProfile₂ r ha v) (G*I) else 0)*
          idealCoeff D.row.χ I) := by
    by_cases hdiv : L∣(I:Id)
    · simp only [hdiv,ite_true,heightCoeff]
      have hh := congrArg (fun z:ℂ=>z*idealCoeff D.row.χ I)
        (coloredSourceColumn_height_shift r ha (idealCoeff ω₁) (idealCoeff ω₂) G I
          hG.1 (sectorPool_supported G hG.1 _ I).1 v)
      convert hh using 1 <;> ring
    · simp only [hdiv,ite_false,zero_mul,mul_zero]
  simp_rw [he]
  rw [←Finset.mul_sum,mul_left_comm]
  change residualPhase (r.X₁*r.X₂) r.d G v*
    (MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P*
      (∑I : sectorPool G hG.1 (sourceColumns r),
        (if L∣(I:Id) then TwistedRawSource.projectedColumn r (idealCoeff ω₁) (idealCoeff ω₂)
          (shiftedSlotCoefficient r v) (shiftedProfile₁ r ha v) (shiftedProfile₂ r ha v) (G*I) else 0)*
          idealCoeff D.row.χ I))=_
  rw [TwistedRawSource.sector_projectedColumn_eq_fullyAllocated r (idealCoeff ω₁) (idealCoeff ω₂)
    D.row.χ (fixedRow_unsupported_zero D) G hG L hL,
    colored_allocated_height_eq_physical r ha hb D ω₁ ω₂ G L hG.1 hL.ne_zero v]

/-- Direct original colored second fixed Gauss polynomial. The full original
column pool, both ordinary colors, signed allocations, full seed puncture and
both genuinely twisted H8 rows occur in one exact Fourier identity. -/
theorem colored_source_rowPolynomial_window_physical (r : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (D : FixedCubeDatum) (ω₁ ω₂ : Character) (η : Character) (χ : RayCharacter)
    (hη : D.η=childCharacter η χ) (hm : D.m=nativeSourceMask r)
    (G : Id) (hG : Supported G) (L : Id) (hL : Squarefree L)
    (t θ X : ℝ) (hX : 0<X) (V : ℝ→ℂ) (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V) :
    MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P*
      rowPolynomial Finset.univ (sectorElement G hG.1 (sourceColumns r))
        (fun I=>divisorCoefficient L (sectorElement G hG.1 (sourceColumns r))
          (movingCoefficient D.A (sectorElement G hG.1 (sourceColumns r))
            (fun I=>TwistedRawSource.sourceColumn r ha (idealCoeff ω₁) (idealCoeff ω₂) 1 (G*I)*heightCoeff η t I)) χ I*
          columnPhase V (Real.log ((Ideal.absNorm (I:Id):ℝ)/X)) θ) D.z=
    ∫w : ℝ,columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
      coloredFullyAllocatedPhysicalHeight r ha hb D ω₁ ω₂ G L (t+2*Real.pi*(w-θ)) := by
  have he : rowPolynomial Finset.univ (sectorElement G hG.1 (sourceColumns r))
        (fun I=>divisorCoefficient L (sectorElement G hG.1 (sourceColumns r))
          (movingCoefficient D.A (sectorElement G hG.1 (sourceColumns r))
            (fun I=>TwistedRawSource.sourceColumn r ha (idealCoeff ω₁) (idealCoeff ω₂) 1 (G*I)*heightCoeff η t I)) χ I*
          columnPhase V (Real.log ((Ideal.absNorm (I:Id):ℝ)/X)) θ) D.z=
      ∑I : sectorPool G hG.1 (sourceColumns r),
        nativeGaussArm η t (sourceColumns r) (TwistedRawSource.sourceColumn r ha (idealCoeff ω₁) (idealCoeff ω₂) 1)
          G hG L χ D.A D.z I*columnPhase V (Real.log ((Ideal.absNorm (I:Id):ℝ)/X)) θ := by
    simp only [rowPolynomial,sectorElement_span,nativeGaussArm]
    apply Finset.sum_congr rfl
    intro I _
    ring
  rw [he,colored_nativeGaussArm_window_integral r ha (idealCoeff ω₁) (idealCoeff ω₂)
    D η χ hη hm G hG L t θ X hX V hVc hVs,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with w
  have hh := coloredSectorFixedHeight_eq_physical r ha hb D ω₁ ω₂ G hG L hL (t+2*Real.pi*(w-θ))
  calc
    _ = (columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X))*
        (MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P*
          coloredSectorFixedHeight r ha (idealCoeff ω₁) (idealCoeff ω₂) D G hG L (t+2*Real.pi*(w-θ))) := by ring
    _ = _ := by rw [hh]

#print axioms coloredNativeFullPrimaryRow_eq_physical
#print axioms colored_allocated_height_eq_physical
#print axioms coloredSectorFixedHeight_eq_physical
#print axioms colored_source_rowPolynomial_window_physical
end
end QRH.Cycle092.FixedCubeGauss
