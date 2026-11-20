/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Complete the signed seed sum before bounding either fixed or regular rows.
   The bool-parametric seed reconstruction is Sil's actual labelSum_regroup. -/
import Candidate.C092.transport.RawSidesPoisson

set_option autoImplicit false
namespace QRH.Cycle092.RawSides
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSectorLocalization CenteredMomentSecondEnergySplit
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondPhysicalBlock CenteredMomentCanonicalFirst
open CenteredMomentHeckeColumnWindow CenteredMomentOriginalChildEnergy CenteredMomentSecondLocalization
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open QRH.SilDensitySplit.CubeFree.Second.Concrete
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

/-- The completed physical blocks of either part. The seed indicators have
    already been summed on the original signed block; only now take norms. -/
def groupedPartTerms (part : Bool) (r : Source ι a b) (ha : 0 < a)
    (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O)
    (t K Tsec Z ξ H : ℝ) : ℝ :=
  ∑ p : commonLabels (supportedColumns (S0 r ha)) (supportedColumns (S0 r ha)),
    ‖rhoC p.val.1‖ * ∑ U : Finset (CommonIndex p.val.1 p.val.2),
      ∑ n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
        ‖physicalBlock ψ t (S0 r ha) (sourceCoefficient r ha 1) p.val.1 p.val.2
          (commonLabels_supported (S0 r ha) _ _ p.property).1
          (commonLabels_supported (S0 r ha) _ _ p.property).2 U (frequencyRadius Tsec Z ξ)
          (partRows part ψ χ₀ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
          ballProfile K (fun i => (n i : ℤ))‖

/-- Both fixed and regular parts use the same exact completed-seed identity. -/
theorem completed_part_eq (part : Bool) (r : Source ι a b) (ha : 0 < a)
    (V : Finset Id) (hV : CompleteSeeds r ha V) (ψ : Character) (χ₀ : RayCharacter)
    (Q : Id) (m : O) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ H : ℝ) :
    ∑ v ∈ V, partEnergy part ψ χ₀ Q m t (sourceColumns r)
      (sourceCoefficient r ha v) W K Tsec Z ξ H =
    ∑ p : commonLabels (supportedColumns (S0 r ha)) (supportedColumns (S0 r ha)),
      rhoC p.val.1 * (heightCoeff ψ t p.val.1 * star (heightCoeff ψ t p.val.2) *
        ∑ U : Finset (CommonIndex p.val.1 p.val.2),
        ∑ n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
          physicalBlock ψ t (S0 r ha) (sourceCoefficient r ha 1) p.val.1 p.val.2
            (commonLabels_supported (S0 r ha) _ _ p.property).1
            (commonLabels_supported (S0 r ha) _ _ p.property).2 U (frequencyRadius Tsec Z ξ)
            (partRows part ψ χ₀ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
            W K (fun i => (n i : ℤ))) := by
  have he (v : Id) : partEnergy part ψ χ₀ Q m t (sourceColumns r)
      (sourceCoefficient r ha v) W K Tsec Z ξ H =
      labelSum part ψ χ₀ Q m t (S0 r ha)
        (fun I => if v ∣ I then sourceCoefficient r ha 1 I else 0) W K Tsec Z ξ H := by
    rw [partEnergy_eq_labelSum, labelSum_mono part ψ χ₀ Q m t
      (active_seed_subset r ha v) (sourceCoefficient r ha v) (active_seed_zero r ha v), seed_fun r ha v]
  simp_rw [he]
  exact labelSum_regroup part ψ χ₀ Q m t (S0 r ha) (sourceCoefficient r ha 1)
    W K Tsec Z ξ H V hV.1 hV.2

/-- No number of seeds is paid when the completed fixed/regular blocks are
    passed to the physical child bound. -/
theorem completed_part_norm_le (part : Bool) (r : Source ι a b) (ha : 0 < a)
    (V : Finset Id) (hV : CompleteSeeds r ha V) (ψ : Character) (χ₀ : RayCharacter)
    (Q : Id) (m : O) (t K Tsec Z ξ H : ℝ) :
    ‖∑ v ∈ V, partEnergy part ψ χ₀ Q m t (sourceColumns r)
      (sourceCoefficient r ha v) ballProfile K Tsec Z ξ H‖ ≤
      groupedPartTerms part r ha ψ χ₀ Q m t K Tsec Z ξ H := by
  rw [completed_part_eq part r ha V hV ψ χ₀ Q m t ballProfile K Tsec Z ξ H]
  unfold groupedPartTerms
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro p _
  rw [norm_mul, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hp := commonLabels_supported (S0 r ha) _ _ p.property
  have hh := common_height_norm_le_one ψ t p.val.1 p.val.2 hp.1.1 hp.2.1
  refine (mul_le_of_le_one_left (norm_nonneg _) hh).trans ?_
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro U _
  exact norm_sum_le _ _

/-- The regular ledger from the native residual theorem is precisely the
    false part of the same completed physical construction. -/
theorem grouped_regular_eq (r : Source ι a b) (ha : 0 < a)
    (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (t K Tsec Z ξ H : ℝ) :
    groupedPartTerms false r ha ψ χ₀ Q m t K Tsec Z ξ H =
      regularTerms r ha ψ χ₀ Q m t K Tsec Z ξ H := rfl

/-- Exact seeded norm caps come from the unseeded coefficient. -/
theorem seeded_norm_cap (r : Source ι a b) (ha : 0 < a) (v : Id) (H : ℝ)
    (hH : ∀ I ∈ sourceColumns r, sourceCoefficient r ha 1 I ≠ 0 → (I.absNorm : ℝ) ≤ H) :
    ∀ I ∈ sourceColumns r, sourceCoefficient r ha v I ≠ 0 → (I.absNorm : ℝ) ≤ H := by
  intro I hI hne
  apply hH I hI
  intro hz
  apply hne
  rw [seed_fun r ha v]
  simp only [hz, ite_self]

/-- Strong H.5 Poisson: the full finite seed sum is formed before the fixed
    and regular block norms. Zero and tail remain their actual original sums. -/
theorem residual_poisson_grouped (r : Source ι a b) (ha : 0 < a) (V : Finset Id)
    (hV : CompleteSeeds r ha V) (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O)
    (t K Tsec Z ξ H : ℝ) (hK : 0 < K)
    (hH : ∀ I ∈ sourceColumns r, sourceCoefficient r ha 1 I ≠ 0 → (I.absNorm : ℝ) ≤ H) :
    ∑ v ∈ V, Qenergy r ha v ψ t K ≤
      zeroTerms r ha V ψ t K + groupedPartTerms true r ha ψ χ₀ Q m t K Tsec Z ξ H +
      tailTerms r ha V ψ t K Tsec Z ξ + groupedPartTerms false r ha ψ χ₀ Q m t K Tsec Z ξ H := by
  let z (v : Id) := (K : ℂ) * EisensteinSchwartzPoisson.paperRadialFourier ballProfile 0 *
    CenteredMomentSourceSecondZeroEnergy.sourceSecondZero (sourceColumns r) (sourceCoefficient r ha v) ψ t
  let f (v : Id) := partEnergy true ψ χ₀ Q m t (sourceColumns r) (sourceCoefficient r ha v)
    ballProfile K Tsec Z ξ H
  let g (v : Id) := partEnergy false ψ χ₀ Q m t (sourceColumns r) (sourceCoefficient r ha v)
    ballProfile K Tsec Z ξ H
  let e (v : Id) := CenteredMomentSupportedTailAggregate.secondDiscardedEnergy ψ t
    (sourceColumns r) (sourceCoefficient r ha v) ballProfile K Tsec Z ξ
  have hq (v : Id) : Qenergy r ha v ψ t K = (z v + f v + e v + g v).re := by
    have he := sourceGaussEnergy_localized ψ t (sourceColumns r) (sourceCoefficient r ha v)
      ballProfile K Tsec Z ξ hK
    rw [original_energy_split ψ χ₀ Q m t (sourceColumns r) (sourceCoefficient r ha v)
      ballProfile K Tsec Z ξ H hK (seeded_norm_cap r ha v H hH)] at he
    have hr := congrArg Complex.re he
    simpa only [Qenergy, sourceGaussEnergy, z, f, g, e, add_assoc, add_comm, add_left_comm] using hr
  have hs : ∑ v ∈ V, Qenergy r ha v ψ t K =
      (∑ v ∈ V, z v).re + (∑ v ∈ V, f v).re + (∑ v ∈ V, e v).re + (∑ v ∈ V, g v).re := by
    simp_rw [hq, Complex.add_re, Finset.sum_add_distrib]
    simp only [Complex.re_sum]
  have hz : (∑ v ∈ V, z v).re ≤ zeroTerms r ha V ψ t K := by
    rw [Complex.re_sum]
    exact Finset.sum_le_sum (fun v _ => Complex.re_le_norm (z v))
  have ht : (∑ v ∈ V, e v).re ≤ tailTerms r ha V ψ t K Tsec Z ξ := by
    rw [Complex.re_sum]
    exact Finset.sum_le_sum (fun v _ => Complex.re_le_norm (e v))
  have hf := (Complex.re_le_norm (∑ v ∈ V, f v)).trans
    (completed_part_norm_le true r ha V hV ψ χ₀ Q m t K Tsec Z ξ H)
  have hg := (Complex.re_le_norm (∑ v ∈ V, g v)).trans
    (completed_part_norm_le false r ha V hV ψ χ₀ Q m t K Tsec Z ξ H)
  rw [hs]
  exact add_le_add (add_le_add (add_le_add hz hf) ht) hg

#print axioms completed_part_eq
#print axioms completed_part_norm_le
#print axioms grouped_regular_eq
#print axioms seeded_norm_cap
#print axioms residual_poisson_grouped
end
end QRH.Cycle092.RawSides
