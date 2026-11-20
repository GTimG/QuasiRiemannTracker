/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Complete the signed seed sum before bounding either fixed or regular rows.
   The bool-parametric seed reconstruction is Sil's actual labelSum_regroup. -/
import Candidate.C092.transport.RawSidesGrouped
import Candidate.C092.transport.TwistedRawSourceTailPower

set_option autoImplicit false
namespace QRH.Cycle092.RootColoredSeed
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

open CenteredMomentActiveSource CenteredMomentSecondSectorRetained CenteredMomentSourceSecondZeroEnergy
open CenteredMomentSupportedTailAggregate CenteredMomentOriginalChildEnergy
open QRH.Cycle092.TwistedRawSource

/-- The actual active coefficient is recomputed after the independent ordinary
twists. A cancellation in an uncolored column does not erase a colored one. -/
def active (r : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id→ℂ) : Finset Id :=
  activeSource (sourceColumns r) (sourceColumn r ha ω₁ ω₂ 1)

def CompleteSeeds (r : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id→ℂ) (V : Finset Id) : Prop :=
  (∀ v∈V,Squarefree v) ∧ ∀ q∈commonLabels (supportedColumns (active r ha ω₁ ω₂))
    (supportedColumns (active r ha ω₁ ω₂)), ∀ v : Id, Squarefree v → v ∣ q.1 → v∈V

theorem exact_seed_completion (r : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id→ℂ) :
    ∃ V : Finset Id,CompleteSeeds r ha ω₁ ω₂ V := by
  let S := active r ha ω₁ ω₂
  let labels := commonLabels (supportedColumns S) (supportedColumns S)
  let V := labels.biUnion (fun q => (IdealMobiusDivisorSum.idealDivisors q.1).filter Squarefree)
  refine ⟨V,?_,?_⟩
  · intro v hv
    obtain ⟨q,hq,hv⟩ := Finset.mem_biUnion.mp hv
    exact (Finset.mem_filter.mp hv).2
  · intro q hq v hsv hdiv
    apply Finset.mem_biUnion.mpr
    exact ⟨q,hq,Finset.mem_filter.mpr ⟨(IdealMobiusDivisorSum.mem_idealDivisors
      (commonLabels_supported S _ _ hq).1.1).mpr hdiv,hsv⟩⟩

theorem seeded_subset (r : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id→ℂ) (v : Id) :
    activeSource (sourceColumns r) (sourceColumn r ha ω₁ ω₂ v) ⊆ active r ha ω₁ ω₂ := by
  intro I hI
  rw [mem_activeSource] at hI
  unfold active;rw [mem_activeSource]
  refine ⟨hI.1,fun h => hI.2 ?_⟩
  rw [sourceColumn_seed,h,ite_self]

theorem seeded_zero (r : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id→ℂ) (v : Id) :
    ∀ I ∈ active r ha ω₁ ω₂,I ∉ activeSource (sourceColumns r) (sourceColumn r ha ω₁ ω₂ v) →
      sourceColumn r ha ω₁ ω₂ v I = 0 := by
  intro I hI hn
  unfold active at hI;rw [mem_activeSource] at hI hn
  by_contra h;exact hn ⟨hI.1,h⟩

/-- The completed physical blocks of either part. The seed indicators have
    already been summed on the original signed block; only now take norms. -/
def groupedPartTerms (part : Bool) (r : Source ι a b) (ha : 0 < a) (ω₁ ω₂ : Id→ℂ)
    (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O)
    (t K Tsec Z ξ H : ℝ) : ℝ :=
  ∑ p : commonLabels (supportedColumns (active r ha ω₁ ω₂)) (supportedColumns (active r ha ω₁ ω₂)),
    ‖rhoC p.val.1‖ * ∑ U : Finset (CommonIndex p.val.1 p.val.2),
      ∑ n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
        ‖physicalBlock ψ t (active r ha ω₁ ω₂) (sourceColumn r ha ω₁ ω₂ 1) p.val.1 p.val.2
          (commonLabels_supported (active r ha ω₁ ω₂) _ _ p.property).1
          (commonLabels_supported (active r ha ω₁ ω₂) _ _ p.property).2 U (frequencyRadius Tsec Z ξ)
          (partRows part ψ χ₀ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
          ballProfile K (fun i => (n i : ℤ))‖

/-- Both fixed and regular parts use the same exact completed-seed identity. -/
theorem completed_part_eq (part : Bool) (r : Source ι a b) (ha : 0 < a) (ω₁ ω₂ : Id→ℂ)
    (V : Finset Id) (hV : CompleteSeeds r ha ω₁ ω₂ V) (ψ : Character) (χ₀ : RayCharacter)
    (Q : Id) (m : O) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ H : ℝ) :
    ∑ v ∈ V, partEnergy part ψ χ₀ Q m t (sourceColumns r)
      (sourceColumn r ha ω₁ ω₂ v) W K Tsec Z ξ H =
    ∑ p : commonLabels (supportedColumns (active r ha ω₁ ω₂)) (supportedColumns (active r ha ω₁ ω₂)),
      rhoC p.val.1 * (heightCoeff ψ t p.val.1 * star (heightCoeff ψ t p.val.2) *
        ∑ U : Finset (CommonIndex p.val.1 p.val.2),
        ∑ n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
          physicalBlock ψ t (active r ha ω₁ ω₂) (sourceColumn r ha ω₁ ω₂ 1) p.val.1 p.val.2
            (commonLabels_supported (active r ha ω₁ ω₂) _ _ p.property).1
            (commonLabels_supported (active r ha ω₁ ω₂) _ _ p.property).2 U (frequencyRadius Tsec Z ξ)
            (partRows part ψ χ₀ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
            W K (fun i => (n i : ℤ))) := by
  have he (v : Id) : partEnergy part ψ χ₀ Q m t (sourceColumns r)
      (sourceColumn r ha ω₁ ω₂ v) W K Tsec Z ξ H =
      labelSum part ψ χ₀ Q m t (active r ha ω₁ ω₂)
        (fun I => if v ∣ I then sourceColumn r ha ω₁ ω₂ 1 I else 0) W K Tsec Z ξ H := by
    rw [partEnergy_eq_labelSum, labelSum_mono part ψ χ₀ Q m t
      (seeded_subset r ha ω₁ ω₂ v) (sourceColumn r ha ω₁ ω₂ v) (seeded_zero r ha ω₁ ω₂ v), show sourceColumn r ha ω₁ ω₂ v = _ from funext (sourceColumn_seed r ha ω₁ ω₂ v)]
  simp_rw [he]
  exact labelSum_regroup part ψ χ₀ Q m t (active r ha ω₁ ω₂) (sourceColumn r ha ω₁ ω₂ 1)
    W K Tsec Z ξ H V hV.1 hV.2

/-- No number of seeds is paid when the completed fixed/regular blocks are
    passed to the physical child bound. -/
theorem completed_part_norm_le (part : Bool) (r : Source ι a b) (ha : 0 < a) (ω₁ ω₂ : Id→ℂ)
    (V : Finset Id) (hV : CompleteSeeds r ha ω₁ ω₂ V) (ψ : Character) (χ₀ : RayCharacter)
    (Q : Id) (m : O) (t K Tsec Z ξ H : ℝ) :
    ‖∑ v ∈ V, partEnergy part ψ χ₀ Q m t (sourceColumns r)
      (sourceColumn r ha ω₁ ω₂ v) ballProfile K Tsec Z ξ H‖ ≤
      groupedPartTerms part r ha ω₁ ω₂ ψ χ₀ Q m t K Tsec Z ξ H := by
  rw [completed_part_eq part r ha ω₁ ω₂ V hV ψ χ₀ Q m t ballProfile K Tsec Z ξ H]
  unfold groupedPartTerms
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro p _
  rw [norm_mul, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hp := commonLabels_supported (active r ha ω₁ ω₂) _ _ p.property
  have hh := common_height_norm_le_one ψ t p.val.1 p.val.2 hp.1.1 hp.2.1
  refine (mul_le_of_le_one_left (norm_nonneg _) hh).trans ?_
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro U _
  exact norm_sum_le _ _

def zeroTerms (r : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id→ℂ) (V : Finset Id)
    (ψ : Character) (t K : ℝ) : ℝ :=
  ∑ v ∈ V,‖(K:ℂ)*EisensteinSchwartzPoisson.paperRadialFourier ballProfile 0*
    sourceSecondZero (sourceColumns r) (sourceColumn r ha ω₁ ω₂ v) ψ t‖

def tailTerms (r : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id→ℂ) (V : Finset Id)
    (ψ : Character) (t K Tsec Z ξ : ℝ) : ℝ :=
  ∑ v ∈ V, ‖secondDiscardedEnergy ψ t (sourceColumns r) (sourceColumn r ha ω₁ ω₂ v) ballProfile K Tsec Z ξ‖

def energy (r : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id→ℂ) (v : Id) (ψ : Character) (t K : ℝ) : ℝ :=
  (sourceGaussEnergy (sourceColumns r) (sourceColumn r ha ω₁ ω₂ v) (heightCoeff ψ t) ballProfile K).re
/-- Exact seeded norm caps come from the unseeded coefficient. -/
theorem seeded_norm_cap (r : Source ι a b) (ha : 0 < a) (ω₁ ω₂ : Id→ℂ) (v : Id) (H : ℝ)
    (hH : ∀ I ∈ sourceColumns r, sourceColumn r ha ω₁ ω₂ 1 I ≠ 0 → (I.absNorm : ℝ) ≤ H) :
    ∀ I ∈ sourceColumns r, sourceColumn r ha ω₁ ω₂ v I ≠ 0 → (I.absNorm : ℝ) ≤ H := by
  intro I hI hne
  apply hH I hI
  intro hz
  apply hne
  rw [show sourceColumn r ha ω₁ ω₂ v = _ from funext (sourceColumn_seed r ha ω₁ ω₂ v)]
  simp only [hz, ite_self]

/-- Strong H.5 Poisson: the full finite seed sum is formed before the fixed
    and regular block norms. Zero and tail remain their actual original sums. -/
theorem residual_poisson_grouped (r : Source ι a b) (ha : 0 < a) (ω₁ ω₂ : Id→ℂ) (V : Finset Id)
    (hV : CompleteSeeds r ha ω₁ ω₂ V) (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O)
    (t K Tsec Z ξ H : ℝ) (hK : 0 < K)
    (hH : ∀ I ∈ sourceColumns r, sourceColumn r ha ω₁ ω₂ 1 I ≠ 0 → (I.absNorm : ℝ) ≤ H) :
    ∑ v ∈ V, energy r ha ω₁ ω₂ v ψ t K ≤
      zeroTerms r ha ω₁ ω₂ V ψ t K + groupedPartTerms true r ha ω₁ ω₂ ψ χ₀ Q m t K Tsec Z ξ H +
      tailTerms r ha ω₁ ω₂ V ψ t K Tsec Z ξ + groupedPartTerms false r ha ω₁ ω₂ ψ χ₀ Q m t K Tsec Z ξ H := by
  let z (v : Id) := (K : ℂ) * EisensteinSchwartzPoisson.paperRadialFourier ballProfile 0 *
    CenteredMomentSourceSecondZeroEnergy.sourceSecondZero (sourceColumns r) (sourceColumn r ha ω₁ ω₂ v) ψ t
  let f (v : Id) := partEnergy true ψ χ₀ Q m t (sourceColumns r) (sourceColumn r ha ω₁ ω₂ v)
    ballProfile K Tsec Z ξ H
  let g (v : Id) := partEnergy false ψ χ₀ Q m t (sourceColumns r) (sourceColumn r ha ω₁ ω₂ v)
    ballProfile K Tsec Z ξ H
  let e (v : Id) := CenteredMomentSupportedTailAggregate.secondDiscardedEnergy ψ t
    (sourceColumns r) (sourceColumn r ha ω₁ ω₂ v) ballProfile K Tsec Z ξ
  have hq (v : Id) : energy r ha ω₁ ω₂ v ψ t K = (z v + f v + e v + g v).re := by
    have he := sourceGaussEnergy_localized ψ t (sourceColumns r) (sourceColumn r ha ω₁ ω₂ v)
      ballProfile K Tsec Z ξ hK
    rw [original_energy_split ψ χ₀ Q m t (sourceColumns r) (sourceColumn r ha ω₁ ω₂ v)
      ballProfile K Tsec Z ξ H hK (seeded_norm_cap r ha ω₁ ω₂ v H hH)] at he
    have hr := congrArg Complex.re he
    simpa only [energy, sourceGaussEnergy, z, f, g, e, add_assoc, add_comm, add_left_comm] using hr
  have hs : ∑ v ∈ V, energy r ha ω₁ ω₂ v ψ t K =
      (∑ v ∈ V, z v).re + (∑ v ∈ V, f v).re + (∑ v ∈ V, e v).re + (∑ v ∈ V, g v).re := by
    simp_rw [hq, Complex.add_re, Finset.sum_add_distrib]
    simp only [Complex.re_sum]
  have hz : (∑ v ∈ V, z v).re ≤ zeroTerms r ha ω₁ ω₂ V ψ t K := by
    rw [Complex.re_sum]
    exact Finset.sum_le_sum (fun v _ => Complex.re_le_norm (z v))
  have ht : (∑ v ∈ V, e v).re ≤ tailTerms r ha ω₁ ω₂ V ψ t K Tsec Z ξ := by
    rw [Complex.re_sum]
    exact Finset.sum_le_sum (fun v _ => Complex.re_le_norm (e v))
  have hf := (Complex.re_le_norm (∑ v ∈ V, f v)).trans
    (completed_part_norm_le true r ha ω₁ ω₂ V hV ψ χ₀ Q m t K Tsec Z ξ H)
  have hg := (Complex.re_le_norm (∑ v ∈ V, g v)).trans
    (completed_part_norm_le false r ha ω₁ ω₂ V hV ψ χ₀ Q m t K Tsec Z ξ H)
  rw [hs]
  exact add_le_add (add_le_add (add_le_add hz hf) ht) hg

#print axioms exact_seed_completion
#print axioms residual_poisson_grouped
end
end QRH.Cycle092.RootColoredSeed
