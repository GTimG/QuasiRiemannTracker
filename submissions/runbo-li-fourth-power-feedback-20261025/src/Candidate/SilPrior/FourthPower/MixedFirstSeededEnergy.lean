/- Copyright (c) 2026 Sil. Apache-2.0.
Positive energy transfer for the literal selected seed allocation.
The child energies are the actual constructed rebased Sources, with
the original character, height and selected twist. Parent checks Lean.
-/
import Candidate.SilPrior.FourthPower.MixedFirstSeededSource
import Candidate.SilPrior.FourthPower.MixedAllocationCost
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AbsoluteEnergy
import Candidate.SilPrior.FourthPower.MixedSelectedVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.MixedFirstSeededEnergy
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcreteTraceCRT QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation
open CenteredMomentCommonRawScale CenteredMomentOriginalRadialComparison
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentLattice
open CenteredMomentSourceLiveColumn ConcretePrimeRowBridge
open CenteredMomentFirstTailAggregate CenteredMomentSecondHeightFamily
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedCommonCoefficient MixedCommonRestriction MixedFixedSupport
open MixedLiveNormalization MixedInnerExceptionalBlock MixedFirstPhysicalApplication
open MixedFirstSeededSource MixedFirstReferenceChoice MixedAllocationCost
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α ⊕ Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- The actual frozen amplitude, independent of the radial frequency z.
Its sign, zero masks and canonical marked factors are all retained. -/
def staticFrozen (s : Source ι a b) (D : Id)
    (alloc : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (B : boundedLabels (MixedPrincipalAllocations.tuplePools s) D) : ℂ :=
  frozenWeight (punctureProduct s.S s.H) B.val *
    allocationTerm D Finset.univ B.val alloc *
    frozenCoefficient B.val (finiteTupleProduct B.val) s.R s.ν s.Wslot s.P

theorem frozen_scalar_split (s : Source ι a b) (D : Id)
    (alloc : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (B : boundedLabels (MixedPrincipalAllocations.tuplePools s) D)
    (η : Character) (m A z : O) (t : ℝ) (F : Id) :
    frozenScalar s D D alloc B (selectedRowHom η m A z t F) =
      staticFrozen s D alloc B * selectedRowHom η m A z t F (finiteTupleProduct B.val) := rfl

theorem frozen_phase_norm (s : Source ι a b) (D : Id)
    (B : boundedLabels (MixedPrincipalAllocations.tuplePools s) D)
    (η : Character) (m A z : O) (t : ℝ) (F : Id) :
    ‖selectedRowHom η m A z t F (finiteTupleProduct B.val)‖ ≤ 1 := by
  have hB := (allocation_data (MixedPrincipalAllocations.tuplePools s) D B.val
    (Finset.mem_filter.mp B.property).1).1
  exact selected_row_hom_norm η m A z t F _
    (Finset.prod_ne_zero_iff.mpr (fun j _ => hB j))

/-- The literal selected finite row, with no new character presentation. -/
def selectedPolynomial (s : Source ι a b) (ha : 0 < a) (seed F : Id)
    (η : Character) (m A : O) (t : ℝ) (z : O) : ℂ :=
  ∑ I ∈ sourceColumns s, selectedCoefficient s ha seed F I * rowWeight η m A z t I

def selectedEnergy (s : Source ι a b) (ha : 0 < a) (seed F : Id)
    (η : Character) (m A : O) (t : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  radialEnergy (selectedPolynomial s ha seed F η m A t) keep Φ K

/-- The complement of the nonzero-source hypothesis in UniformEnergy
vanishes coefficient by coefficient; no small-source estimate is assumed. -/
theorem selected_zero_of_sharp_small (s : Source ι a b) (ha : 0 < a)
    (hsmall : MixedFirstGeometricCaps.sharpSupport s < 1) (seed F I : Id) :
    selectedCoefficient s ha seed F I = 0 := by
  by_contra hI
  exact (not_le_of_gt hsmall) (MixedFirstGeometricCaps.sharp_support_one_le s ha seed I
    (selected_support s ha seed F I hI))

theorem selected_energy_zero_of_sharp_small (s : Source ι a b) (ha : 0 < a)
    (hsmall : MixedFirstGeometricCaps.sharpSupport s < 1) (seed F : Id)
    (η : Character) (m A : O) (t : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    selectedEnergy s ha seed F η m A t keep Φ K = 0 := by
  have hrow : selectedPolynomial s ha seed F η m A t = fun _ => 0 := by
    funext z
    simp only [selectedPolynomial,selected_zero_of_sharp_small s ha hsmall,
      zero_mul,Finset.sum_const_zero]
  simp only [selectedEnergy,hrow,radialEnergy,norm_zero,zero_pow (by norm_num : 2≠0),
    zero_mul,ite_self,tsum_zero]

theorem finite_selected_energy_zero_of_sharp_small (s : Source ι a b) (ha : 0 < a)
    (hsmall : MixedFirstGeometricCaps.sharpSupport s < 1) (seed F : Id)
    (η : Character) (m A : O) (t : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    finiteHeckeEnergy η m A t (sourceColumns s) (selectedCoefficient s ha seed F) Φ K = 0 := by
  simp only [finiteHeckeEnergy,selected_zero_of_sharp_small s ha hsmall,
    zero_mul,Finset.sum_const_zero,norm_zero,zero_pow (by norm_num : 2≠0),
    Complex.ofReal_zero,tsum_zero]

theorem selected_energy_nonneg (s : Source ι a b) (ha : 0 < a) (seed F : Id)
    (η : Character) (m A : O) (t : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hΦ : ∀ z, 0 ≤ (Φ (‖eisEmbedding z‖^2/K)).re) :
    0 ≤ selectedEnergy s ha seed F η m A t keep Φ K := by
  unfold selectedEnergy radialEnergy
  apply tsum_nonneg
  intro z
  split_ifs
  · exact mul_nonneg (sq_nonneg _) (hΦ z)
  · exact le_rfl

/-- Apply finite Cauchy once to the actual pair of allocation indices.
The RHS consists of actual child energies, not assumed energy bounds. -/
theorem selected_energy_allocation (s : Source ι a b) (ha : 0 < a)
    (hb : 0 ≤ b) (cover : OriginalEnclosure s) (D : Id) (hD : Squarefree D)
    (F : Id) (η : Character) (m A : O) (t : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K radial : ℝ) (hK : 0 < K)
    (hs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic radial)
    (hΦ : ∀ z, 0 ≤ (Φ (‖eisEmbedding z‖^2/K)).re) :
    selectedEnergy s ha D F η m A t keep Φ K ≤
      ((Fintype.card (Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) : ℝ) *
        (boundedLabels (MixedPrincipalAllocations.tuplePools s) D).card) *
      ∑ alloc : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
        ∑ B : boundedLabels (MixedPrincipalAllocations.tuplePools s) D,
          ‖staticFrozen s D alloc B‖^2 *
            selectedEnergy (seededRebasedSource s hb cover D hD.ne_zero B) ha 1 F
              η m A t keep Φ K := by
  let T := Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)) ×
    boundedLabels (MixedPrincipalAllocations.tuplePools s) D
  let phase := fun (q : T) (z : O) =>
    selectedRowHom η m A z t F (finiteTupleProduct q.2.val)
  let f := fun (q : T) (z : O) => staticFrozen s D q.1 q.2 *
    selectedPolynomial (seededRebasedSource s hb cover D hD.ne_zero q.2) ha 1 F η m A t z
  have hphase : ∀ q z, keep z → ‖phase q z‖ ≤ 1 := by
    intro q z hz
    exact frozen_phase_norm s D q.2 η m A z t F
  have he := radial_phase_family phase f (fun q => radialEnergy (f q) keep Φ K)
    keep Φ K radial hK hs hΦ hphase (fun _ => le_rfl)
  have hrow : selectedPolynomial s ha D F η m A t = fun z => ∑ q : T, phase q z * f q z := by
    funext z
    rw [Fintype.sum_prod_type]
    change (∑ I ∈ sourceColumns s, selectedCoefficient s ha D F I*rowWeight η m A z t I) = _
    rw [seeded_selected_row s ha hb cover D hD η m A z t F]
    apply Finset.sum_congr rfl
    intro alloc ha'
    apply Finset.sum_congr rfl
    intro B hB'
    dsimp only [phase,f,selectedPolynomial]
    rw [frozen_scalar_split]
    ring
  have hcost (q : T) : radialEnergy (f q) keep Φ K =
      ‖staticFrozen s D q.1 q.2‖^2 *
        selectedEnergy (seededRebasedSource s hb cover D hD.ne_zero q.2) ha 1 F
          η m A t keep Φ K :=
    radial_mul _ _ _ _ _
  unfold selectedEnergy
  rw [hrow]
  simpa only [hcost,T,Fintype.card_prod,Fintype.card_coe,Nat.cast_mul,
    Fintype.sum_prod_type,selectedEnergy] using he

/-- The exact weight after passing to the actual rebased child volume.
There is precisely one original prefix denominator. -/
def normalizedFrozen (s : Source ι a b) (D : Id)
    (alloc : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (B : boundedLabels (MixedPrincipalAllocations.tuplePools s) D) : ℝ :=
  (‖staticFrozen s D alloc B‖^2 / rawReduction B.val s.P) / pairNorm s.d

theorem normalized_frozen_nonneg (s : Source ι a b) (D : Id)
    (alloc : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (B : boundedLabels (MixedPrincipalAllocations.tuplePools s) D) :
    0 ≤ normalizedFrozen s D alloc B := by
  have hB := (allocation_data (MixedPrincipalAllocations.tuplePools s) D B.val
    (Finset.mem_filter.mp B.property).1).1
  exact div_nonneg (div_nonneg (sq_nonneg _)
    (rawReduction_pos B.val hB s.P (fun i => zero_lt_one.trans_le (s.hP i))).le)
    (pairNorm_pos s.hd.1 s.hd.2).le

theorem selected_energy_normalized (s : Source ι a b) (ha : 0 < a)
    (hb : 0 ≤ b) (cover : OriginalEnclosure s) (D : Id) (hD : Squarefree D)
    (F : Id) (η : Character) (m A : O) (t : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K radial : ℝ) (hK : 0 < K)
    (hs : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic radial)
    (hΦ : ∀ z, 0 ≤ (Φ (‖eisEmbedding z‖^2/K)).re) :
    selectedEnergy s ha D F η m A t keep Φ K / sourceVolume s ≤
      ((Fintype.card (Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) : ℝ) *
        (boundedLabels (MixedPrincipalAllocations.tuplePools s) D).card) *
      ∑ alloc : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
        ∑ B : boundedLabels (MixedPrincipalAllocations.tuplePools s) D,
          normalizedFrozen s D alloc B *
            (selectedEnergy (seededRebasedSource s hb cover D hD.ne_zero B) ha 1 F
              η m A t keep Φ K / sourceVolume (seededRebasedSource s hb cover D hD.ne_zero B)) := by
  have he := div_le_div_of_nonneg_right
    (selected_energy_allocation s ha hb cover D hD F η m A t keep Φ K radial hK hs hΦ)
    (sourceVolume_pos s).le
  refine he.trans_eq ?_
  rw [mul_div_assoc]
  simp only [Finset.sum_div]
  apply congrArg (fun x : ℝ =>
    ((Fintype.card (Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) : ℝ) *
      (boundedLabels (MixedPrincipalAllocations.tuplePools s) D).card) * x)
  apply Finset.sum_congr rfl
  intro alloc ha'
  apply Finset.sum_congr rfl
  intro B hB'
  rw [seeded_normalization s hb cover D hD.ne_zero B]
  unfold normalizedFrozen
  ring

theorem normalized_frozen_seed (s : Source ι a b) (D : Id) (hD : Squarefree D)
    (alloc : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (B : boundedLabels (MixedPrincipalAllocations.tuplePools s) D) :
    normalizedFrozen s D alloc B ≤
      (∏ i, s.M i)^2 * (2 : ℝ)^Fintype.card ι / (pairNorm s.d * (D.absNorm : ℝ)) := by
  exact seed_frozen_cost_with_prefix (punctureProduct s.S s.H) s.R D hD alloc B.val
    (allocation_data (MixedPrincipalAllocations.tuplePools s) D B.val
      (Finset.mem_filter.mp B.property).1).1 s.d s.hd s.ν s.Wslot s.P s.M
    (fun i => zero_lt_one.trans_le (s.hP i)) s.hν s.hWnorm s.hM s.hW

/-- The genuine allocation counts and all static amplitudes together
retain the full reciprocal seed norm, with only the proved subpower.
This is a coefficient-mass theorem, not a live-energy hypothesis. -/
theorem uniform_normalized_frozen_mass (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b : ℝ) (s : Source ι a b) (D : Id), Squarefree D →
      ((Fintype.card (Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) : ℝ) *
        (boundedLabels (MixedPrincipalAllocations.tuplePools s) D).card) *
        (∑ alloc : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
          ∑ B : boundedLabels (MixedPrincipalAllocations.tuplePools s) D,
            normalizedFrozen s D alloc B) ≤
      C * (D.absNorm : ℝ)^ε * ((∏ i, s.M i)^2 * (2 : ℝ)^Fintype.card ι) /
        (pairNorm s.d * (D.absNorm : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := uniform_seed_scalar_mass (ι := ι) ε hε
  refine ⟨C,hC,?_⟩
  intro a b s D hD
  have he := div_le_div_of_nonneg_right
    (hbound (MixedPrincipalAllocations.tuplePools s) (punctureProduct s.S s.H) s.R D hD
      s.ν s.Wslot s.P s.M (fun i => zero_lt_one.trans_le (s.hP i))
      s.hν s.hWnorm s.hM s.hW) (pairNorm_pos s.hd.1 s.hd.2).le
  have hleft :
      (((Fintype.card (Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) : ℝ) *
        (boundedLabels (MixedPrincipalAllocations.tuplePools s) D).card) *
        (∑ alloc : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
          ∑ B : boundedLabels (MixedPrincipalAllocations.tuplePools s) D,
            ‖staticFrozen s D alloc B‖^2 / rawReduction B.val s.P)) / pairNorm s.d =
      ((Fintype.card (Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) : ℝ) *
        (boundedLabels (MixedPrincipalAllocations.tuplePools s) D).card) *
        (∑ alloc : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
          ∑ B : boundedLabels (MixedPrincipalAllocations.tuplePools s) D,
            normalizedFrozen s D alloc B) := by
    simp only [mul_div_assoc,Finset.sum_div,normalizedFrozen]
  dsimp only [staticFrozen] at hleft
  rw [hleft] at he
  exact he.trans_eq (by ring)

/-- Arbitrary keep masks are allowed: the old/new sixth-power mask
equality is established on each literal selected coefficient first. -/
theorem selected_energy_mask (s : Source ι a b) (ha : 0 < a) (seed F R : Id)
    (hR : R ∣ s.R) (η : Character) (A : O) (t : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    selectedEnergy s ha seed F η (fixedBadMask*idealGenerator R) A t keep Φ K =
      selectedEnergy s ha seed F η fixedBadMask A t keep Φ K := by
  apply congrArg (fun f : O → ℂ => radialEnergy f keep Φ K)
  funext z
  unfold selectedPolynomial
  apply Finset.sum_congr rfl
  intro I hI
  unfold selectedCoefficient
  calc
    _ = (sourceCoefficient s ha seed I *
          rowWeight η (fixedBadMask*idealGenerator R) A z t I) * selectedTwist F I := by ring
    _ = (sourceCoefficient s ha seed I * rowWeight η fixedBadMask A z t I) *
          selectedTwist F I := by rw [source_weight_mask s ha seed R hR]
    _ = _ := by ring

theorem seeded_selected_energy_mask (s : Source ι a b) (ha : 0 < a)
    (hb : 0 ≤ b) (cover : OriginalEnclosure s) (D : Id) (hD : D ≠ 0)
    (B : boundedLabels (MixedPrincipalAllocations.tuplePools s) D)
    (F : Id) (η : Character) (A : O) (t : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let r := seededRebasedSource s hb cover D hD B
    selectedEnergy r ha 1 F η (fixedBadMask*idealGenerator r.R) A t keep Φ K =
      selectedEnergy r ha 1 F η (fixedBadMask*idealGenerator s.R) A t keep Φ K := by
  dsimp only
  rw [selected_energy_mask _ ha 1 F _ (dvd_refl _)]
  exact (selected_energy_mask _ ha 1 F s.R (dvd_mul_right s.R D) η A t keep Φ K).symm

open CenteredMomentAbsoluteEnergy MixedSupplierPositive

/-- Exact complete positive-energy dictionary at A=1. The source, seed,
selected twist F, original character, mask and height are unchanged. -/
theorem selected_energy_eq_re (s : Source ι a b) (ha : 0<a) (seed F : Id)
    (η : Character) (m : O) (t : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    selectedEnergy s ha seed F η m 1 t (fun _=>True) Φ K =
      (finiteHeckeEnergy η m 1 t (sourceColumns s)
        (selectedCoefficient s ha seed F) Φ K).re := by
  have hs := finite_hecke_energy_summable η m 1 t (sourceColumns s)
    (selectedCoefficient s ha seed F) Φ K hK
  have hr : HasSum
      (fun z : O=>‖selectedPolynomial s ha seed F η m 1 t z‖^2 *
        (Φ (‖eisEmbedding z‖^2/K)).re)
      (finiteHeckeEnergy η m 1 t (sourceColumns s)
        (selectedCoefficient s ha seed F) Φ K).re := by
    simpa only [selectedPolynomial,finiteHeckeEnergy,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using
      (Complex.hasSum_re hs.hasSum)
  simpa only [selectedEnergy,radialEnergy,ite_true] using hr.tsum_eq

/-- Real-part passage through the SAME finite grouped average. This is
an identity and does not require positivity of weights or the profile. -/
theorem grouped_selected_energy_eq_re (s : Source ι a b) (ha : 0<a)
    (seed : Id) (η : Character) (m : O) (t : ℝ)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (Ds : Finset Id)
    (weight : Id→ℝ) (W : ℝ) :
    (∑F∈Ds,(weight F/W)*selectedEnergy s ha seed F η m 1 t (fun _=>True) Φ K) =
      (∑F∈Ds,((weight F/W:ℝ):ℂ)*finiteHeckeEnergy η m 1 t
        (sourceColumns s) (selectedCoefficient s ha seed F) Φ K).re := by
  classical
  induction Ds using Finset.induction_on with
  | empty => simp
  | @insert F Ds hF ih =>
    simp only [Finset.sum_insert hF,Complex.add_re,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,←ih,
      selected_energy_eq_re s ha seed F η m t Φ K hK]

/-- Actual grouped positive energy, with the literal selectedProducts,
groupedWeight and padded scale. The norm is outside the SAME complex
sum used in uniform_grouped_first_energy, not a sum of separate norms.
The full source-volume denominator occurs exactly once on each side.

For UniformEnergy instantiate s := avoidSource s0 u, seed := 1 and
m := fixedBadMask*idealGenerator s0.R. Its source volume is definitionally
the original sourceVolume s0; no seed/prefix factors are discarded here.
-/
theorem grouped_selected_positive_le_norm {α : Type*} [Fintype α]
    (q : MixedSupplierFourthRow.Data α) (hP : ∀i,0<q.P i)
    (s : Source ι a b) (ha : 0<a) (seed : Id) (η : Character)
    (m : O) (t : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hΦ : ∀x : ℝ,0≤(Φ x).re) :
    0≤(∑F∈selectedProducts q,(groupedWeight q F/MixedSelectedVolume.scale q)*
        selectedEnergy s ha seed F η m 1 t (fun _=>True) Φ K)/sourceVolume s ∧
    (∑F∈selectedProducts q,(groupedWeight q F/MixedSelectedVolume.scale q)*
        selectedEnergy s ha seed F η m 1 t (fun _=>True) Φ K)/sourceVolume s ≤
      ‖∑F∈selectedProducts q,((groupedWeight q F/MixedSelectedVolume.scale q:ℝ):ℂ)*
        finiteHeckeEnergy η m 1 t (sourceColumns s)
          (selectedCoefficient s ha seed F) Φ K‖/sourceVolume s := by
  have hW := MixedSelectedVolume.scale_pos q hP
  constructor
  · apply div_nonneg _ (sourceVolume_pos s).le
    apply Finset.sum_nonneg
    intro F hF
    exact mul_nonneg (div_nonneg (grouped_weight_nonneg q F) hW.le)
      (selected_energy_nonneg s ha seed F η m 1 t (fun _=>True) Φ K
        (fun z=>hΦ _))
  · rw [grouped_selected_energy_eq_re s ha seed η m t Φ K hK
      (selectedProducts q) (groupedWeight q) (MixedSelectedVolume.scale q)]
    exact div_le_div_of_nonneg_right (Complex.re_le_norm _) (sourceVolume_pos s).le

/-- A positive compact smoothing permits enlargement of the centered
row family. The reference estimate still keeps its nonprincipal rows;
this lemma does not assert a reference bound on the enlarged family. -/
theorem selected_energy_le_full (s : Source ι a b) (ha : 0<a) (seed F : Id)
    (η : Character) (m A : O) (t : ℝ) (keep : O→Prop)
    (Φ : 𝓢(ℝ,ℂ)) (K radial : ℝ) (hK : 0<K)
    (hs : Function.support (Φ : ℝ→ℂ)⊆Set.Iic radial)
    (hΦ : ∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) :
    selectedEnergy s ha seed F η m A t keep Φ K≤
      selectedEnergy s ha seed F η m A t (fun _=>True) Φ K := by
  have hleft := CenteredMomentEnergyCapacityRemoval.compact_radial_summable
    (selectedPolynomial s ha seed F η m A t) keep Φ K radial hK hs
  have hright := CenteredMomentEnergyCapacityRemoval.compact_radial_summable
    (selectedPolynomial s ha seed F η m A t) (fun _=>True) Φ K radial hK hs
  unfold selectedEnergy radialEnergy
  apply hleft.tsum_le_tsum _ hright
  intro z
  simp only [ite_true]
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (sq_nonneg _) (hΦ z)

/-- The eligibility mask can depend on the selected product F, as the
actual cubic nonprincipal predicate does. Enlargement is paid inside
the original positive grouped average, before its complex norm. -/
theorem grouped_selected_kept_positive_le_norm {α : Type*} [Fintype α]
    (q : MixedSupplierFourthRow.Data α) (hP : ∀i,0<q.P i)
    (s : Source ι a b) (ha : 0<a) (seed : Id) (η : Character)
    (m : O) (t : ℝ) (keep : Id→O→Prop)
    (Φ : 𝓢(ℝ,ℂ)) (K radial : ℝ) (hK : 0<K)
    (hs : Function.support (Φ : ℝ→ℂ)⊆Set.Iic radial)
    (hΦ : ∀x : ℝ,0≤(Φ x).re) :
    (∑F∈selectedProducts q,(groupedWeight q F/MixedSelectedVolume.scale q)*
        selectedEnergy s ha seed F η m 1 t (keep F) Φ K)/sourceVolume s ≤
      ‖∑F∈selectedProducts q,((groupedWeight q F/MixedSelectedVolume.scale q:ℝ):ℂ)*
        finiteHeckeEnergy η m 1 t (sourceColumns s)
          (selectedCoefficient s ha seed F) Φ K‖/sourceVolume s := by
  have hW := MixedSelectedVolume.scale_pos q hP
  have he :
      (∑F∈selectedProducts q,(groupedWeight q F/MixedSelectedVolume.scale q)*
        selectedEnergy s ha seed F η m 1 t (keep F) Φ K) ≤
      ∑F∈selectedProducts q,(groupedWeight q F/MixedSelectedVolume.scale q)*
        selectedEnergy s ha seed F η m 1 t (fun _=>True) Φ K := by
    apply Finset.sum_le_sum
    intro F hF
    exact mul_le_mul_of_nonneg_left
      (selected_energy_le_full s ha seed F η m 1 t (keep F) Φ K radial hK hs
        (fun z=>hΦ _))
      (div_nonneg (grouped_weight_nonneg q F) hW.le)
  exact (div_le_div_of_nonneg_right he (sourceVolume_pos s).le).trans
    (grouped_selected_positive_le_norm q hP s ha seed η m t Φ K hK hΦ).2

/- This finishes ONLY the positive-smoothing dictionary. Applying the
proved UniformEnergy estimate still requires its actual canonical/scalar
source gates. Original seed/prefix allocation and loss payment remain
their separate exact steps; this insertion supplies no endpoint assertion.
-/

end
end Candidate.SilPrior.FourthPower.MixedFirstSeededEnergy
