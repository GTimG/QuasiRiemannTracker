/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Exact first retained expansion on actual colored support. -/
import Candidate.C092.transport.TwistedRawBallBlock
import Candidate.C092.transport.TwistedRawBallMass
import Submissions.sil_density_split_20261026.CubeFree.FP.MixedFirstRetainedFixed
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TwistedRawBall
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily
open CenteredMomentActiveSource CenteredMomentSupportedCorrelation CenteredMomentCommonSupport
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst CenteredMomentFirstColumns
open CenteredMomentFirstRetainedAssembly CenteredMomentFirstRetainedActive
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentFirstPhysicalActiveDictionary CenteredMomentFirstSectorLocalization
open CenteredMomentFirstDiscardedEnergy CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFirstScale
open CenteredMomentFirstSectorTransform
open CenteredMomentSecondRetainedRows CenteredMomentRowNorm CenteredMomentFirstReduced
open QRH.SilDensitySplit.CubeFree.FP
open QRH.Cycle092.TwistedRawSource
open MixedFirstRetainedFixed
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalTail MixedOriginalNormCap
open MixedInnerExceptionalBlock MixedInnerExceptionalLedger
open MixedFirstPhysicalApplication MixedFirstPhysicalBudget MixedFirstCommonSum
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- Exact expansion for one selected product, with fixed actual labels.
The source is unrestricted here; in applications it is avoidSource s u. -/
theorem selected_retained_fixed (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id → ℂ) (seed F : Id)
    (η : Character) (t : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K Z ξ H : ℝ)
    (hK : 0<K) (hH : sourceNormCap s.P b s.T s.d≤H) :
    retainedEnergy η (fixedBadMask*idealGenerator s.R) 1 t (sourceColumns s)
      (selectedCoefficient s ha ω₁ ω₂ seed F) Φ K (sourceVolume s) Z ξ=
    ∑p : Labels s ha ω₁ ω₂ seed,∑E∈inactiveSubsets p.val.1 p.val.2,
      ∑n : Blocks (effectiveScale p.val.1 p.val.2 E K)
        (firstRadius s p.val.1 p.val.2 E K Z ξ)
        (H/p.val.1.absNorm) (H/p.val.2.absNorm),
      commonHeight s η t p.val.1 p.val.2*
        block η (fixedBadMask*idealGenerator s.R) 1 t (sourceColumns s)
          (selectedCoefficient s ha ω₁ ω₂ seed F) p.val.1 p.val.2
          (commonLabels_supported (activeSource (sourceColumns s) (sourceColumn s ha ω₁ ω₂ seed)) p).1
          (commonLabels_supported (activeSource (sourceColumns s) (sourceColumn s ha ω₁ ω₂ seed)) p).2
          E (fixedRows (firstRadius s p.val.1 p.val.2 E K Z ξ) (fun i=>n i))
          Φ (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
            (dyadicScale (n 2)) (dyadicScale (n 3)) := by
  dsimp only [firstRadius]
  have hz (I : Id) (hI : sourceColumn s ha ω₁ ω₂ seed I=0) :
      selectedCoefficient s ha ω₁ ω₂ seed F I=0 := by
    simp only [selectedCoefficient,hI,zero_mul]
  have hcap (I : Id) (hI : selectedCoefficient s ha ω₁ ω₂ seed F I≠0) :
      (I.absNorm:ℝ)≤H :=
    (sourceColumn_cap s ha ω₁ ω₂ seed I (selected_support s ha ω₁ ω₂ seed F I hI)).2.trans hH
  rw [←retained_on_fixed_support η (fixedBadMask*idealGenerator s.R) 1 t
    (sourceColumns s) (sourceColumn s ha ω₁ ω₂ seed) (selectedCoefficient s ha ω₁ ω₂ seed F) hz]
  rw [retained_energy_blocks]
  apply Finset.sum_congr rfl
  intro p hp
  change commonHeight s η t p.val.1 p.val.2*
    infiniteSector η (fixedBadMask*idealGenerator s.R) 1 t
      (activeSource (sourceColumns s) (sourceColumn s ha ω₁ ω₂ seed))
      (selectedCoefficient s ha ω₁ ω₂ seed F) p.val.1 p.val.2 _ _ Φ K (sourceVolume s) Z ξ=_
  unfold infiniteSector
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro E hE
  rw [retainedInfiniteBlock_eq_finite,retainedBlock_eq_blocks _ _ _ _ _ _ _ _ _ _ _ _
    (retained_rows_nonzero _) _ _ _ H hK hcap,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [block_on_fixed_support _ _ _ _ _ _ _ hz,
    block_activeRows (n:=fun i=>(n i:ℤ))]
  rfl

theorem summed_retained_blocks (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id → ℂ) (η : Character) (t : ℝ)
    (Φ : 𝓢(ℝ,ℂ)) (K Z ξ H : ℝ) (hK : 0 < K) (hsource : sourceNormCap s.P b s.T s.d ≤ H) :
    retainedEnergy η (fixedBadMask*idealGenerator s.R) 1 t (sourceColumns s)
      (sourceColumn s ha ω₁ ω₂ 1) Φ K (sourceVolume s) Z ξ =
      ∑ p : Labels s ha ω₁ ω₂ 1, ∑ E ∈ inactiveSubsets p.val.1 p.val.2,
        ∑ n : Blocks (effectiveScale p.val.1 p.val.2 E K) (firstRadius s p.val.1 p.val.2 E K Z ξ)
            (H/p.val.1.absNorm) (H/p.val.2.absNorm),
          blockTerm s ha ω₁ ω₂ η t p.val.1 p.val.2
            (commonLabels_supported (activeSource (sourceColumns s) (sourceColumn s ha ω₁ ω₂ 1)) p).1
            (commonLabels_supported (activeSource (sourceColumns s) (sourceColumn s ha ω₁ ω₂ 1)) p).2 E
            (fixedRows (firstRadius s p.val.1 p.val.2 E K Z ξ) (fun i => (n i:ℤ)))
            Φ K (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)) := by
  have he := selected_retained_fixed s ha ω₁ ω₂ 1 1 η t Φ K Z ξ H hK hsource
  rw [retained_selected_one] at he
  simpa only [blockTerm, block_selected_one] using he


#print axioms selected_retained_fixed
#print axioms summed_retained_blocks
end
end QRH.Cycle092.TwistedRawBall
