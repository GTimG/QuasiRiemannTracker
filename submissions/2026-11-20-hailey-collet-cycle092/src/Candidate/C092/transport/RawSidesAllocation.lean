/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   The unweighted first-divisor lift at the original two raw sides. Allocation
   and Gauss identities are reused from Sil's existing repaired FP source. -/
import Candidate.C092.transport.RawSidesPoisson
import Submissions.sil_density_split_20261026.CubeFree.First.RawSidesRetained

set_option autoImplicit false
namespace QRH.Cycle092.RawSides
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentFirstAmplificationChoice CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentOriginalChildEnergy
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open MixedPrincipalAllocations MixedFirstLiveSource MixedCommonCoefficient MixedCommonRestriction
open QRH.SilDensitySplit.CubeFree.Second.Concrete
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

abbrev Allocations (s : Source ι a b) (G : Id) := actualAllocations (tuplePools s) G

def allocationWeight (s : Source ι a b) (G : Id) (B : Allocations s G) : ℝ :=
  ‖frozenWeight (punctureProduct s.S s.H) B.val *
    frozenCoefficient B.val G s.R s.ν s.Wslot s.P‖^2

/-- First common allocation, with all first artificial divisors still inside
    one positive side. Neither the seed sum nor the allocation scalar carries
    a reciprocal seed weight. Both shortened ordinary factors are those of
    `allocatedLiveSource`; the original profiles and phases remain inside it. -/
theorem raw_sum_le_allocated (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (C G : Id) (hC : Supported C) (hG : Supported G)
    (hCG : QRH.Record1252270103KernelMass.primeSupport C =
      QRH.Record1252270103KernelMass.primeSupport G)
    (Us : Finset Id) (τ : Character) (t K : ℝ) (hK : 0 < K) :
    ∑ v ∈ Us, RepairedFirstRawSides.rawEnergy s ha C G hG v τ t K ≤
      ((Allocations s G).card : ℝ) * ∑ B : Allocations s G,
        allocationWeight s G B * ∑ v ∈ Us,
          Qenergy (allocatedLiveSource s hb cover G B) ha v τ t K := by
  have h (v : Id) : RepairedFirstRawSides.rawEnergy s ha C G hG v τ t K ≤
      ((Allocations s G).card : ℝ) * ∑ B : Allocations s G,
        allocationWeight s G B * Qenergy (allocatedLiveSource s hb cover G B) ha v τ t K := by
    simpa only [RepairedFirstRawSides.rawEnergy, Qenergy, allocationWeight, sourceGaussEnergy] using
      MixedFirstLiveEnergy.actual_common_energy s ha hb cover C G 1 v hC hG hCG
      (one_dvd G) τ t ballProfile K hK (fun _ => ballProfile_nonneg _)
  refine (Finset.sum_le_sum (fun v _ => h v)).trans_eq ?_
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro B _
  rw [Finset.mul_sum]

/-- The first side follows directly from bounds on its actual allocated
    residual Gauss energies. This keeps the finite allocation multiplicity
    separate from the subsequent grouped second labels. -/
theorem raw_sum_of_allocated (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (C G : Id) (hC : Supported C) (hG : Supported G)
    (hCG : QRH.Record1252270103KernelMass.primeSupport C =
      QRH.Record1252270103KernelMass.primeSupport G)
    (Us : Finset Id) (τ : Character) (t K : ℝ) (hK : 0 < K)
    (E : Allocations s G → ℝ)
    (hE : ∀ B : Allocations s G,
      ∑ v ∈ Us, Qenergy (allocatedLiveSource s hb cover G B) ha v τ t K ≤ E B) :
    ∑ v ∈ Us, RepairedFirstRawSides.rawEnergy s ha C G hG v τ t K ≤
      ((Allocations s G).card : ℝ) * ∑ B : Allocations s G, allocationWeight s G B * E B := by
  refine (raw_sum_le_allocated s ha hb cover C G hC hG hCG Us τ t K hK).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum (fun B _ => mul_le_mul_of_nonneg_left (hE B) (show 0 ≤ allocationWeight s G B from sq_nonneg _))

/-- H.5's raw side with only literal Poisson child bounds left as premises.
    The completed seed set may depend on the actual allocation. -/
theorem raw_sum_of_physical_terms (s : Source ι a b) (ha : 0 < a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (C G : Id) (hC : Supported C) (hG : Supported G)
    (hCG : QRH.Record1252270103KernelMass.primeSupport C =
      QRH.Record1252270103KernelMass.primeSupport G)
    (Us : Finset Id) (τ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O)
    (t K Tsec Z ξ H : ℝ) (hK : 0 < K)
    (V : Allocations s G → Finset Id)
    (hUV : ∀ B, Us ⊆ V B)
    (hV : ∀ B, CompleteSeeds (allocatedLiveSource s hb cover G B) ha (V B))
    (hH : ∀ B, ∀ I ∈ sourceColumns (allocatedLiveSource s hb cover G B),
      sourceCoefficient (allocatedLiveSource s hb cover G B) ha 1 I ≠ 0 → (I.absNorm : ℝ) ≤ H)
    (E₀ Ef Et Er : Allocations s G → ℝ)
    (hz : ∀ B, zeroTerms (allocatedLiveSource s hb cover G B) ha (V B) τ t K ≤ E₀ B)
    (hf : ∀ B, fixedTerms (allocatedLiveSource s hb cover G B) ha (V B) τ χ₀ Q m t K Tsec Z ξ H ≤ Ef B)
    (ht : ∀ B, tailTerms (allocatedLiveSource s hb cover G B) ha (V B) τ t K Tsec Z ξ ≤ Et B)
    (hr : ∀ B, regularTerms (allocatedLiveSource s hb cover G B) ha τ χ₀ Q m t K Tsec Z ξ H ≤ Er B) :
    ∑ v ∈ Us, RepairedFirstRawSides.rawEnergy s ha C G hG v τ t K ≤
      ((Allocations s G).card : ℝ) * ∑ B : Allocations s G,
        allocationWeight s G B * (E₀ B + Ef B + Et B + Er B) := by
  apply raw_sum_of_allocated s ha hb cover C G hC hG hCG Us τ t K hK
  intro B
  exact residual_subset_of_terms (allocatedLiveSource s hb cover G B) ha Us (V B)
    (hUV B) (hV B) τ χ₀ Q m t K Tsec Z ξ H (E₀ B) (Ef B) (Et B) (Er B) hK
    (hH B) (hz B) (hf B) (ht B) (hr B)

#print axioms raw_sum_le_allocated
#print axioms raw_sum_of_allocated
#print axioms raw_sum_of_physical_terms
end
end QRH.Cycle092.RawSides
