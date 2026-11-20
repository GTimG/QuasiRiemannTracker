/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Genuine colored first raw-side allocation, before whole-mark selection. -/
import Candidate.C092.transport.TwistedRawBallLive
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TwistedRawBall
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentAddedZeroUniform CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentGaussEnergy CenteredMomentFirstPhysicalSource CenteredMomentHeckeColumnWindow
open CenteredMomentFirstAmplificationChoice CenteredMomentSourceRow CenteredMomentSmoothedWindowEnergy
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open MixedFirstLiveSource MixedPrincipalAllocations
open QRH.Cycle092.TwistedRawSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}
local instance (priority := 2000) sumAllocationDecEq {κ κ₂ : Type*} :
    DecidableEq (κ ⊕ κ₂) := Classical.decEq _

def rawEnergy (s : Source ι a b) (ha : 0 < a) (ω₁ ω₂ : Id → ℂ)
    (C G : Id) (hG : Supported G) (D : Id) (τ : Character) (t K : ℝ) : ℝ :=
  (gaussEnergy Finset.univ (element C G hG.1 (sourceColumns s))
    (element_supported C G hG.1 (sourceColumns s))
    (fun I => rawCoefficient s ha ω₁ ω₂ 1 G D I * heightCoeff τ t I) ballProfile K).re

def allocationScalar (s : Source ι a b) (ω₁ ω₂ : Id → ℂ) (G : Id)
    (B : actualAllocations (tuplePools s) G) : ℂ :=
  MixedCommonCoefficient.frozenWeight (MixedCommonRestriction.punctureProduct s.S s.H) B.val *
    ordinaryColor ω₁ ω₂ B.val * frozenCoefficient B.val G s.R s.ν s.Wslot s.P

def allocationWeight (s : Source ι a b) (ω₁ ω₂ : Id → ℂ) (G : Id)
    (B : actualAllocations (tuplePools s) G) : ℝ := ‖allocationScalar s ω₁ ω₂ G B‖^2

/-- Cauchy on the exact colored Gauss identity. The RHS is the genuine
    allocated colored energy consumed by the selected second Poisson theorem. -/
theorem actual_common_energy (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (ω₁ ω₂ : Id →*₀ ℂ)
    (C G : Id) (hC : Supported C) (hG : Supported G)
    (hCG : QRH.Record1252270103KernelMass.primeSupport C =
      QRH.Record1252270103KernelMass.primeSupport G)
    (D : Id) (τ : Character) (t K : ℝ) (hK : 0 < K) :
    rawEnergy s ha ω₁ ω₂ C G hG D τ t K ≤
      ((actualAllocations (tuplePools s) G).card : ℝ) *
      ∑ B : actualAllocations (tuplePools s) G,
        allocationWeight s ω₁ ω₂ G B *
          QRH.Cycle092.RootColoredSeed.energy (allocatedLiveSource s hb cover G B) ha ω₁ ω₂ D τ t K := by
  let poly (B : actualAllocations (tuplePools s) G) (z : O) : ℂ :=
    gaussPolynomial Finset.univ (sourceGenerator (sourceColumns (allocatedLiveSource s hb cover G B)))
      (sourceGenerator_supported _) (fun I => sourceColumn (allocatedLiveSource s hb cover G B) ha ω₁ ω₂ D I * heightCoeff τ t I) z
  let w (z : O) : ℝ := (ballProfile (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re
  have hf := gaussEnergy_hasSum_re Finset.univ (element C G hG.1 (sourceColumns s))
    (element_supported C G hG.1 (sourceColumns s))
    (fun I => rawCoefficient s ha ω₁ ω₂ 1 G D I * heightCoeff τ t I) ballProfile K hK
  have hg : HasSum (fun z : O =>
      ((actualAllocations (tuplePools s) G).card : ℝ) *
        ∑ B : actualAllocations (tuplePools s) G, allocationWeight s ω₁ ω₂ G B * (‖poly B z‖^2*w z))
      (((actualAllocations (tuplePools s) G).card : ℝ) *
        ∑ B : actualAllocations (tuplePools s) G, allocationWeight s ω₁ ω₂ G B *
          QRH.Cycle092.RootColoredSeed.energy (allocatedLiveSource s hb cover G B) ha ω₁ ω₂ D τ t K) := by
    apply HasSum.mul_left
    apply hasSum_sum
    intro B hB
    apply HasSum.mul_left
    exact gaussEnergy_hasSum_re Finset.univ
      (sourceGenerator (sourceColumns (allocatedLiveSource s hb cover G B)))
      (sourceGenerator_supported _)
      (fun I => sourceColumn (allocatedLiveSource s hb cover G B) ha ω₁ ω₂ D I * heightCoeff τ t I) ballProfile K hK
  apply hasSum_le _ hf hg
  intro z
  have hz := CubicEisenstein.norm_sum_sq_le_card Finset.univ
    (fun B : actualAllocations (tuplePools s) G => allocationScalar s ω₁ ω₂ G B * poly B z)
  have he := first_gauss_live_sources s ha hb cover ω₁ ω₂ C G 1 D hC hG hCG (one_dvd G) τ t z
  rw [he]
  change ‖∑ B, allocationScalar s ω₁ ω₂ G B * poly B z‖^2*w z ≤ _
  calc
    _ ≤ ((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ) *
      (∑ B, ‖allocationScalar s ω₁ ω₂ G B * poly B z‖^2) * w z :=
      mul_le_mul_of_nonneg_right hz (ballProfile_nonneg _)
    _ = _ := by
      simp only [Finset.card_univ, Fintype.card_coe, norm_mul, mul_pow, Finset.sum_mul,
        Finset.mul_sum, allocationWeight]
      apply Finset.sum_congr rfl
      intro B hB
      ring

/-- The original first artificial divisor sum remains unweighted. -/
theorem raw_sum_le_allocated (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (ω₁ ω₂ : Id →*₀ ℂ)
    (C G : Id) (hC : Supported C) (hG : Supported G)
    (hCG : QRH.Record1252270103KernelMass.primeSupport C =
      QRH.Record1252270103KernelMass.primeSupport G)
    (Us : Finset Id) (τ : Character) (t K : ℝ) (hK : 0 < K) :
    (∑ D ∈ Us, rawEnergy s ha ω₁ ω₂ C G hG D τ t K) ≤
      ((actualAllocations (tuplePools s) G).card : ℝ) *
      ∑ B : actualAllocations (tuplePools s) G,
        allocationWeight s ω₁ ω₂ G B *
          ∑ D ∈ Us, QRH.Cycle092.RootColoredSeed.energy (allocatedLiveSource s hb cover G B) ha ω₁ ω₂ D τ t K := by
  apply (Finset.sum_le_sum (fun D hD => actual_common_energy s ha hb cover ω₁ ω₂ C G hC hG hCG D τ t K hK)).trans_eq
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro B hB
  rw [Finset.mul_sum]

#print axioms actual_common_energy
#print axioms raw_sum_le_allocated
end
end QRH.Cycle092.TwistedRawBall
