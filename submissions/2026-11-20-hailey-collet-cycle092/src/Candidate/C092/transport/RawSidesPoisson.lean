/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   H.5 at the actual residual coefficients. The Poisson and signed common-label
   reconstruction are Sil's; their OAI dependencies retain their notices.
   No replacement source-energy or analytic split hypothesis is introduced. -/
import Submissions.sil_density_split_20261026.CubeFree.Second.ConcreteLabelAssembly12

set_option autoImplicit false
namespace QRH.Cycle092.RawSides
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSectorLocalization CenteredMomentSecondEnergySplit
open CenteredMomentSourceSecondZeroEnergy CenteredMomentSupportedTailAggregate
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.SilDensitySplit.CubeFree.Second.ConcreteLabelAssembly
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

/-- The original zero-frequency terms, including their actual radial scalar. -/
def zeroTerms (r : Source ι a b) (ha : 0 < a) (V : Finset Id)
    (ψ : Character) (t K : ℝ) : ℝ :=
  ∑ v ∈ V, ‖(K : ℂ) * EisensteinSchwartzPoisson.paperRadialFourier ballProfile 0 *
    sourceSecondZero (sourceColumns r) (sourceCoefficient r ha v) ψ t‖

/-- The original fixed inducing rows, before any attempt to price them. -/
def fixedTerms (r : Source ι a b) (ha : 0 < a) (V : Finset Id)
    (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O)
    (t K Tsec Z ξ H : ℝ) : ℝ :=
  ∑ v ∈ V, ‖partEnergy true ψ χ₀ Q m t (sourceColumns r)
    (sourceCoefficient r ha v) ballProfile K Tsec Z ξ H‖

/-- The original discarded-frequency terms; their seed sum is a count. -/
def tailTerms (r : Source ι a b) (ha : 0 < a) (V : Finset Id)
    (ψ : Character) (t K Tsec Z ξ : ℝ) : ℝ :=
  ∑ v ∈ V, ‖secondDiscardedEnergy ψ t (sourceColumns r)
    (sourceCoefficient r ha v) ballProfile K Tsec Z ξ‖

/-- The actual retained regular physical blocks after the complete signed seed
    reconstruction. This is not an independently assumed positive comparison. -/
def regularTerms (r : Source ι a b) (ha : 0 < a)
    (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O)
    (t K Tsec Z ξ H : ℝ) : ℝ :=
  splitLabel (S0 r ha) (sourceCoefficient r ha 1) ψ χ₀ Q m t K
    (frequencyRadius Tsec Z ξ) H

/-- The seed set contains every squarefree divisor needed by the original
    second common labels. Enlarging an incomplete sum without this condition
    would not justify the signed reconstruction. -/
def CompleteSeeds (r : Source ι a b) (ha : 0 < a) (V : Finset Id) : Prop :=
  (∀ v ∈ V, Squarefree v) ∧
  ∀ q ∈ commonLabels (supportedColumns (S0 r ha)) (supportedColumns (S0 r ha)),
    ∀ v : Id, Squarefree v → v ∣ q.1 → v ∈ V

/-- Authentic second Poisson at the actual residual source. The completed
    squarefree seed sum is taken before the regular blocks' absolute values. -/
theorem residual_poisson_terms (r : Source ι a b) (ha : 0 < a) (V : Finset Id)
    (hV : CompleteSeeds r ha V) (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O)
    (t K Tsec Z ξ H : ℝ) (hK : 0 < K)
    (hH : ∀ I ∈ sourceColumns r, sourceCoefficient r ha 1 I ≠ 0 → (I.absNorm : ℝ) ≤ H) :
    ∑ v ∈ V, Qenergy r ha v ψ t K ≤
      zeroTerms r ha V ψ t K + fixedTerms r ha V ψ χ₀ Q m t K Tsec Z ξ H +
      tailTerms r ha V ψ t K Tsec Z ξ + regularTerms r ha ψ χ₀ Q m t K Tsec Z ξ H := by
  exact QRH.SilDensitySplit.CubeFree.Second.Concrete.residual_poisson
    r ha V hV.1 hV.2 ψ χ₀ Q m t K Tsec Z ξ H hK hH

/-- Child consumers supply bounds only for the four literal physical terms. -/
theorem residual_of_terms (r : Source ι a b) (ha : 0 < a) (V : Finset Id)
    (hV : CompleteSeeds r ha V) (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O)
    (t K Tsec Z ξ H E₀ Ef Et Er : ℝ) (hK : 0 < K)
    (hH : ∀ I ∈ sourceColumns r, sourceCoefficient r ha 1 I ≠ 0 → (I.absNorm : ℝ) ≤ H)
    (hz : zeroTerms r ha V ψ t K ≤ E₀)
    (hf : fixedTerms r ha V ψ χ₀ Q m t K Tsec Z ξ H ≤ Ef)
    (ht : tailTerms r ha V ψ t K Tsec Z ξ ≤ Et)
    (hr : regularTerms r ha ψ χ₀ Q m t K Tsec Z ξ H ≤ Er) :
    ∑ v ∈ V, Qenergy r ha v ψ t K ≤ E₀ + Ef + Et + Er := by
  exact (residual_poisson_terms r ha V hV ψ χ₀ Q m t K Tsec Z ξ H hK hH).trans
    (add_le_add (add_le_add (add_le_add hz hf) ht) hr)

theorem residual_energy_nonneg (r : Source ι a b) (ha : 0 < a) (v : Id)
    (ψ : Character) (t K : ℝ) (hK : 0 < K) : 0 ≤ Qenergy r ha v ψ t K := by
  exact gaussEnergy_ball_nonneg _ _ _ _ K hK

/-- Complete a positive first-seed sub-sum only after its Gauss energy has been
    formed. There is no reciprocal-divisor factor in this statement. -/
theorem residual_subset_of_terms (r : Source ι a b) (ha : 0 < a)
    (Us V : Finset Id) (hUV : Us ⊆ V) (hV : CompleteSeeds r ha V)
    (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O)
    (t K Tsec Z ξ H E₀ Ef Et Er : ℝ) (hK : 0 < K)
    (hH : ∀ I ∈ sourceColumns r, sourceCoefficient r ha 1 I ≠ 0 → (I.absNorm : ℝ) ≤ H)
    (hz : zeroTerms r ha V ψ t K ≤ E₀)
    (hf : fixedTerms r ha V ψ χ₀ Q m t K Tsec Z ξ H ≤ Ef)
    (ht : tailTerms r ha V ψ t K Tsec Z ξ ≤ Et)
    (hr : regularTerms r ha ψ χ₀ Q m t K Tsec Z ξ H ≤ Er) :
    ∑ v ∈ Us, Qenergy r ha v ψ t K ≤ E₀ + Ef + Et + Er := by
  exact (Finset.sum_le_sum_of_subset_of_nonneg hUV
    (fun v _ _ => residual_energy_nonneg r ha v ψ t K hK)).trans
    (residual_of_terms r ha V hV ψ χ₀ Q m t K Tsec Z ξ H E₀ Ef Et Er hK hH hz hf ht hr)

#print axioms residual_poisson_terms
#print axioms residual_of_terms
#print axioms residual_energy_nonneg
#print axioms residual_subset_of_terms
end
end QRH.Cycle092.RawSides
