/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   First colored Gauss rows are sums of actual allocated-live Gauss rows. -/
import Candidate.C092.transport.TwistedRawBallGauss
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TwistedRawBall
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile CenteredMomentFirstSectors
open CenteredMomentCommonAllocationSum CenteredMomentLiveDomain CenteredMomentSourceRectangle
open CenteredMomentGaussEnergy CenteredMomentFirstPhysicalSource CenteredMomentHeckeColumnWindow
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open MixedFirstLiveSource MixedPrincipalAllocations
open QRH.Cycle092.TwistedRawSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance (priority := 2000) sumLiveDecEq {κ κ₂ : Type*} :
    DecidableEq (κ ⊕ κ₂) := Classical.decEq _

theorem source_column_eq_coloredColumn (s : Source ι a b) (ha : 0 < a)
    (ω₁ ω₂ : Id → ℂ) (seed : Id) :
    sourceColumn s ha ω₁ ω₂ seed = coloredColumn (Fintype.piFinset (tuplePools s))
      (MixedCommonRestriction.punctureProduct s.S s.H) ω₁ ω₂
      (profileCoefficient s.R s.ν s.Wslot s.P
        (CenteredMomentLattice.normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
        (CenteredMomentLattice.normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
        s.X₁ s.X₂ s.Y₁ s.Y₂ s.d.1 s.d.2 seed) := by
  funext I
  unfold sourceColumn coloredColumn finiteColumnCoefficient
  apply Finset.sum_congr rfl
  intro v hv
  unfold MixedOriginalSecondZero.originalTuple coloredTuple
  ring

theorem live_source_gauss_tuples (s : Source ι a b) (ha : 0 < a)
    (ω₁ ω₂ : Id → ℂ) (D : Id) (τ : Character) (t : ℝ) (k : O) :
    gaussPolynomial Finset.univ (CenteredMomentSourceRow.sourceGenerator (sourceColumns (liveSource s)))
      (CenteredMomentSourceRow.sourceGenerator_supported _)
      (fun I => sourceColumn (liveSource s) ha ω₁ ω₂ D I * heightCoeff τ t I) k =
      ∑ v ∈ liveBox (tuplePools s) s.B s.hB,
        (if D ∣ finiteTupleProduct v then coloredTuple (MixedCommonRestriction.punctureProduct s.S s.H) ω₁ ω₂
          (liveProfile s.B s.G s.R s.ν s.Wslot s.P
            (CenteredMomentLattice.normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
            (CenteredMomentLattice.normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
            s.X₁ s.X₂ s.Y₁ s.Y₂ s.d.1 s.d.2) v else 0) *
        (heightCoeff τ t (finiteTupleProduct v)*primaryGaussRow (finiteTupleProduct v) k) := by
  have hh := source_gauss_sum (sourceColumns (liveSource s))
    (fun I : Id => sourceColumn (liveSource s) ha ω₁ ω₂ D I * heightCoeff τ t I) k
  refine hh.trans ?_
  simp_rw [live_source_colored_coefficient]
  rw [live_source_columns]
  let V := liveBox (tuplePools s) s.B s.hB
  let β := coloredTuple (MixedCommonRestriction.punctureProduct s.S s.H) ω₁ ω₂
    (liveProfile s.B s.G s.R s.ν s.Wslot s.P
      (CenteredMomentLattice.normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
      (CenteredMomentLattice.normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
      s.X₁ s.X₂ s.Y₁ s.Y₂ s.d.1 s.d.2)
  calc
    _ = ∑ I ∈ finiteColumns V, finiteColumnCoefficient V β I *
      (if D ∣ I then heightCoeff τ t I*primaryGaussRow I k else 0) := by
      apply Finset.sum_congr rfl
      intro I hI
      dsimp only [V, β, coloredColumn]
      split_ifs <;> ring
    _ = _ := (finite_column_regroup V β _).trans (by
      apply Finset.sum_congr rfl
      intro v hv
      split_ifs <;> ring)

def rawCoefficient (s : Source ι a b) (ha : 0 < a) (ω₁ ω₂ : Id → ℂ)
    (seed G D I : Id) : ℂ := if D ∣ I then sourceColumn s ha ω₁ ω₂ seed (G*I) else 0

theorem first_gauss_live_sources (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (ω₁ ω₂ : Id →*₀ ℂ)
    (C G seed D : Id) (hC : Supported C) (hG : Supported G)
    (hCG : QRH.Record1252270103KernelMass.primeSupport C =
      QRH.Record1252270103KernelMass.primeSupport G) (hseed : seed ∣ G)
    (τ : Character) (t : ℝ) (k : O) :
    gaussPolynomial Finset.univ (element C G hG.1 (sourceColumns s))
      (element_supported C G hG.1 (sourceColumns s))
      (fun I => rawCoefficient s ha ω₁ ω₂ seed G D I * heightCoeff τ t I) k =
      ∑ B : actualAllocations (tuplePools s) G,
        (MixedCommonCoefficient.frozenWeight (MixedCommonRestriction.punctureProduct s.S s.H) B.val *
          ordinaryColor ω₁ ω₂ B.val * frozenCoefficient B.val G s.R s.ν s.Wslot s.P) *
        gaussPolynomial Finset.univ
          (CenteredMomentSourceRow.sourceGenerator (sourceColumns (allocatedLiveSource s hb cover G B)))
          (CenteredMomentSourceRow.sourceGenerator_supported _)
          (fun I => sourceColumn (allocatedLiveSource s hb cover G B) ha ω₁ ω₂ D I * heightCoeff τ t I) k := by
  have hh := first_gauss_common_tuples ω₁ ω₂ (MixedCommonRestriction.punctureProduct s.S s.H)
    (tuplePools s) (MixedLiteralAllocation.source_pools_nonzero s.pool s.hp s.d s.hd b s.X₁ s.X₂ s.Y₁ s.Y₂)
    (by intro i I hI; exact s.hp i I hI) C G s.R seed D hC hG hCG hseed s.ν s.Wslot s.P
    (CenteredMomentLattice.normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
    (CenteredMomentLattice.normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
    s.X₁ s.X₂ s.Y₁ s.Y₂ s.d τ t k
  dsimp only at hh
  unfold rawCoefficient
  rw [source_column_eq_coloredColumn]
  refine hh.trans ?_
  apply Finset.sum_congr rfl
  intro B hB
  congr 1
  have hl := live_source_gauss_tuples (allocationSource s hb cover G B) ha ω₁ ω₂ D τ t k
  exact hl.symm

#print axioms source_column_eq_coloredColumn
#print axioms live_source_gauss_tuples
#print axioms first_gauss_live_sources
end
end QRH.Cycle092.TwistedRawBall
