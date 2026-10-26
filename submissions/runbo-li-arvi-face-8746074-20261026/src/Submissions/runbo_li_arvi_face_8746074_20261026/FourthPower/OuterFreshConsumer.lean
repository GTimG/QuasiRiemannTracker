/- Copyright (c) 2026 Sil. Apache-2.0.
Exact outer consumer on a fixed canonical support, before the D average.
No analytic estimate is an input.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.OuterFreshAssembly
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.OuterFreshNonexceptionalFamily
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedSupplierOuterFamily
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedLocalizedDictionary
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedPoissonCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.OuterFreshConsumer
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion
open ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentGaussEnergy
open CenteredMomentFirstAmplificationChoice CenteredMomentSmoothedWindowEnergy
open CenteredMomentOriginalChildEnergy CenteredMomentFirstSectors CenteredMomentCompleteCommon
open CenteredMomentActiveSource CenteredMomentSecondActivePhysicalDictionary
open CenteredMomentSecondSectorFrequency CenteredMomentSecondSectorColumns
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondWholeKernel
open CenteredMomentChildAssembly CenteredMomentSecondScaled CenteredMomentSupportedTailAggregate
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondBlockAggregate
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondRetainedRows
open CenteredMomentSecondActiveDyadic CenteredMomentSecondEnergySplit CenteredMomentFirstColumns
open CenteredMomentSecondSectorRetained CenteredMomentSecondDyadicPartition
open CenteredMomentSecondPhysicalWindow CenteredMomentSecondLiveBlock
open CenteredMomentSecondLocalization CenteredMomentSectorLocalization
open CenteredMomentLogDyadic CenteredMomentSmooth
open MixedSupplierKernel MixedSupplierFourthRow MixedSupplierSource MixedSupplierPositive MixedSupplierOuterActive
open MixedSupplierOriginalFrequency OuterFreshRows OuterFreshWindowPair
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedPoissonCompletion MixedPoissonLocalization
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α] {a b : ℝ}

/-- A zero-completion fact. Only the implication between actual supports
is required; no inequality is moved through a complex sum. -/
theorem nested_active (S : Finset Id) (β₀ β : Id→ℂ)
    (hβ : ∀I,β I≠0→β₀ I≠0) :
    activeSource (activeSource S β₀) β=activeSource S β := by
  ext I
  simp only [mem_activeSource]
  exact ⟨fun h=>⟨h.1.1,h.2⟩,fun h=>⟨⟨h.1,hβ I h.2⟩,h.2⟩⟩

theorem energy_fixed_support (S : Finset Id) (β₀ β f : Id→ℂ)
    (hβ : ∀I,β I≠0→β₀ I≠0) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy S β f Φ K=sourceGaussEnergy (activeSource S β₀) β f Φ K := by
  rw [←sourceGaussEnergy_active S β f Φ K,
    ←sourceGaussEnergy_active (activeSource S β₀) β f Φ K,nested_active S β₀ β hβ]

theorem retained_fixed_support (τ : Character) (t : ℝ) (S : Finset Id)
    (β₀ β : Id→ℂ) (hβ : ∀I,β I≠0→β₀ I≠0)
    (Φ : 𝓢(ℝ,ℂ)) (K T Z ζ : ℝ) :
    secondRetainedEnergy τ t S β Φ K T Z ζ=
      secondRetainedEnergy τ t (activeSource S β₀) β Φ K T Z ζ := by
  rw [←secondRetainedEnergy_active τ t S β Φ K T Z ζ,
    ←secondRetainedEnergy_active τ t (activeSource S β₀) β Φ K T Z ζ,
    nested_active S β₀ β hβ]

theorem sector_fixed_support (τ : Character) (t : ℝ) (S : Finset Id)
    (β₀ β : Id→ℂ) (hβ : ∀I,β I≠0→β₀ I≠0)
    (C E : Id) (hC : Supported C) (hE : Supported E)
    (F : O→Id→Id→ℂ) (z : O) :
    sectorFrequency τ t S β C E hC hE F z=
      sectorFrequency τ t (activeSource S β₀) β C E hC hE F z := by
  rw [sectorFrequency_active τ t S β C E hC hE F z,
    sectorFrequency_active τ t (activeSource S β₀) β C E hC hE F z,
    nested_active S β₀ β hβ]

theorem block_fixed_support (τ : Character) (t : ℝ) (S : Finset Id)
    (β₀ β : Id→ℂ) (hβ : ∀I,β I≠0→β₀ I≠0)
    (C E : Id) (hC : Supported C) (hE : Supported E) (U : Finset (CommonIndex C E))
    (R : ℝ) (rows : Finset O) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ) :
    physicalBlock τ t S β C E hC hE U R rows Φ K n=
      physicalBlock τ t (activeSource S β₀) β C E hC hE U R rows Φ K n := by
  rw [physicalBlock_active τ t S β C E hC hE U R rows Φ K n,
    physicalBlock_active τ t (activeSource S β₀) β C E hC hE U R rows Φ K n,
    nested_active S β₀ β hβ]

/-- The fixed support contains the original punctures and the artificial
seed, but does not depend on D, the Hecke height, or either finite ray. -/
def fixedPool (q : Data α) (x : Frozen q) (s : Source (RestIndex q) a b)
    (seed : Id) : Finset Id := activeSource (sourceColumns s) (commonColumn q x seed)

theorem outer_supported_by_common (q : Data α) (x : Frozen q) (y : Selected q)
    (seed : Id) (ξ : RayCharacter) (I : Id) (h : outerColumn q x y seed ξ I≠0) :
    commonColumn q x seed I≠0 := by
  intro hz
  exact h (by simp only [outerColumn,hz,zero_mul])

theorem actual_retained_fixed (q : Data α) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (seed : Id) (τ : Character) (ξ : RayCharacter)
    (t : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K T Z ζ : ℝ) :
    secondRetainedEnergy τ t (sourceColumns s) (outerColumn q x y seed ξ) Φ K T Z ζ=
      secondRetainedEnergy τ t (fixedPool q x s seed) (outerColumn q x y seed ξ) Φ K T Z ζ :=
  retained_fixed_support τ t _ _ _ (outer_supported_by_common q x y seed ξ) Φ K T Z ζ

/-- The fixed-pool version of the upstream dyadic partition. Its H
controls the fixed pool, so every dyadic profile is chosen BEFORE D.
The auxiliary coefficient 1 is used solely to invoke support geometry. -/
theorem fixed_kernel_windows (τ : Character) (S : Finset Id) (H : ℝ)
    (hH : ∀I∈S,(I.absNorm:ℝ)≤H) (C E : Id) (hC : Supported C) (hE : Supported E) :
    ∀(I : sectorPool C hC.1 S)(J : sectorPool E hE.1 S)(A z : O),A≠0→z≠0→
    ∀(Φ : 𝓢(ℝ,ℂ))(K R : ℝ),0<K→
      physicalKernel C E Φ K R (A*z) I J=
        ∑n : Blocks (sourceLower C E A K) (sourceUpper C E A K R H),
          physicalKernel C E Φ K R (A*z) I J*
            ((dyadicWeight (n 0) (secondEffectiveScale C E A K)*dyadicWeight (n 1) (normValue z)*
              dyadicWeight (n 2) (I.val.absNorm:ℝ)*dyadicWeight (n 3) (J.val.absNorm:ℝ):ℝ):ℂ) := by
  have ha : activeSource S (fun _ : Id=>(1:ℂ))=S := by simp [activeSource]
  intro I J A z hA hz Φ K R hK
  let I' : sectorPool C hC.1 (activeSource S (fun _ : Id=>(1:ℂ))) :=
    ⟨I.val,by rw [ha];exact I.property⟩
  let J' : sectorPool E hE.1 (activeSource S (fun _ : Id=>(1:ℂ))) :=
    ⟨J.val,by rw [ha];exact J.property⟩
  exact active_kernel_windows τ S (fun _=>(1:ℂ)) H
    (fun I hI _=>hH I hI) C E hC hE I' J' A z hA hz Φ K R hK

/-- Exact signed sum, not a norm bound. This is the upstream
sector_finite_blocks proof with coefficient-independent support geometry. -/
theorem fixed_sector_blocks (τ : Character) (t : ℝ) (S : Finset Id) (β : Id→ℂ)
    (H : ℝ) (hH : ∀I∈S,(I.absNorm:ℝ)≤H)
    (C E : Id) (hC : Supported C) (hE : Supported E) (U : Finset (CommonIndex C E))
    (Φ : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) :
    let A:=commonFrequencyGenerator C E*nonunitFrequencyGenerator C E U
    (∑z∈retainedRows R A,if canonicalPartition C E U (nonunitFrequencyGenerator C E U*z) then
      sectorFrequency τ t S β C E hC hE (physicalKernel C E Φ K R) (A*z) else 0)=
      ∑n : SourceBlocks C E U K R H,
        physicalBlock τ t S β C E hC hE U R (retainedRows R A) Φ K (fun i=>(n i:ℤ)) := by
  dsimp only
  have hA : commonFrequencyGenerator C E*nonunitFrequencyGenerator C E U≠0 :=
    mul_ne_zero (commonFrequencyGenerator_ne_zero C E hC)
      (nonunitFrequencyGenerator_ne_zero C E hC U)
  unfold physicalBlock
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hp : canonicalPartition C E U (nonunitFrequencyGenerator C E U*z)
  · simp only [hp,ite_true]
    unfold sectorFrequency
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro I hI
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro J hJ
    conv_lhs => rw [fixed_kernel_windows τ S H hH C E hC hE I J _ z hA
      (retainedRows_ne_zero R _ z hz) Φ K R hK,Finset.mul_sum]
  · simp only [hp,ite_false,Finset.sum_const_zero]

abbrev FixedLabel (S : Finset Id) :=
  ↥(commonLabels (supportedColumns S) (supportedColumns S))

theorem fixed_retained_blocks (τ : Character) (t : ℝ) (S : Finset Id) (β : Id→ℂ)
    (Φ : 𝓢(ℝ,ℂ)) (K T Z ζ H : ℝ) (hK : 0<K) (hH : ∀I∈S,(I.absNorm:ℝ)≤H) :
    secondRetainedEnergy τ t S β Φ K T Z ζ=
      ∑p : FixedLabel S,heightCoeff τ t p.val.1*star (heightCoeff τ t p.val.2)*
        ∑U : Finset (CommonIndex p.val.1 p.val.2),
          ∑n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius T Z ζ) H,
            physicalBlock τ t S β p.val.1 p.val.2
              (commonLabels_supported S _ _ p.property).1 (commonLabels_supported S _ _ p.property).2 U
              (frequencyRadius T Z ζ)
              (retainedRows (frequencyRadius T Z ζ)
                (commonFrequencyGenerator p.val.1 p.val.2*nonunitFrequencyGenerator p.val.1 p.val.2 U))
              Φ K (fun i=>(n i:ℤ)) := by
  rw [original_retained_energy_GV τ t S β Φ K T Z ζ hK]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  rw [actual_GV_finite_rows]
  exact fixed_sector_blocks τ t S β H hH _ _ _ _ U Φ K _ hK

/-- The true new outer partition, now on one D-independent label set,
one fixed canonical pool and one fixed collection of dyadic profiles.
The full commonHeight remains in every complex summand. -/
def fixedPart (exceptional : Bool) (q : Data α) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (seed : Id) (τ : Character) (ξ χ : RayCharacter)
    (Q : Id) (t : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K T Z ζ H : ℝ) : ℂ :=
  let S:=fixedPool q x s seed
  ∑p : FixedLabel S,heightCoeff τ t p.val.1*star (heightCoeff τ t p.val.2)*
    ∑U : Finset (CommonIndex p.val.1 p.val.2),
      ∑n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius T Z ζ) H,
        physicalBlock τ t S (outerColumn q x y seed ξ) p.val.1 p.val.2
          (commonLabels_supported S _ _ p.property).1 (commonLabels_supported S _ _ p.property).2 U
          (frequencyRadius T Z ζ)
          (outerRows exceptional q x y τ ξ χ Q p.val.1 p.val.2 U (frequencyRadius T Z ζ))
          Φ K (fun i=>(n i:ℤ))

theorem fixed_retained_split (q : Data α) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (seed : Id) (τ : Character) (ξ χ : RayCharacter)
    (Q : Id) (t : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K T Z ζ H : ℝ) (hK : 0<K)
    (hH : ∀I∈fixedPool q x s seed,(I.absNorm:ℝ)≤H) :
    secondRetainedEnergy τ t (sourceColumns s) (outerColumn q x y seed ξ) Φ K T Z ζ=
      fixedPart true q x y s seed τ ξ χ Q t Φ K T Z ζ H+
      fixedPart false q x y s seed τ ξ χ Q t Φ K T Z ζ H := by
  rw [actual_retained_fixed q x y s seed τ ξ t Φ K T Z ζ,
    fixed_retained_blocks τ t _ _ Φ K T Z ζ H hK hH]
  unfold fixedPart
  dsimp only
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [←mul_add,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [physicalBlock_live_rows]
  exact physical_block_outer_split q x y seed τ t ξ χ Q (fixedPool q x s seed)
    p.val.1 p.val.2 _ _ U (frequencyRadius T Z ζ) Φ K (fun i=>(n i:ℤ))

/-- Signed exact interchange. In particular it is legal to choose the
common sector, U, and all four dyadic profiles before averaging over D.
No active-label set depends on the averaging variable. -/
theorem selected_fixed_parts (exceptional : Bool) (q : Data α) (x : Frozen q)
    (s : Source (RestIndex q) a b) (seed : Id) (τ : Character) (ξ χ : RayCharacter)
    (Q : Id) (t : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K T Z ζ H : ℝ) :
    (∑y∈activeSelected q,(selectedPositiveWeight q x y τ:ℂ)*
      fixedPart exceptional q x y s seed τ ξ χ Q t Φ K T Z ζ H)=
      ∑p : FixedLabel (fixedPool q x s seed),
        (heightCoeff τ t p.val.1*star (heightCoeff τ t p.val.2))*
        ∑U : Finset (CommonIndex p.val.1 p.val.2),
          ∑n : SourceBlocks p.val.1 p.val.2 U K (frequencyRadius T Z ζ) H,
            ∑y∈activeSelected q,(selectedPositiveWeight q x y τ:ℂ)*
              physicalBlock τ t (fixedPool q x s seed) (outerColumn q x y seed ξ)
                p.val.1 p.val.2
                (commonLabels_supported (fixedPool q x s seed) _ _ p.property).1
                (commonLabels_supported (fixedPool q x s seed) _ _ p.property).2 U
                (frequencyRadius T Z ζ)
                (outerRows exceptional q x y τ ξ χ Q p.val.1 p.val.2 U (frequencyRadius T Z ζ))
                Φ K (fun i=>(n i:ℤ)) := by
  unfold fixedPart
  dsimp only
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U hU
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro y hy
  ring

/-- Sharp character families are chosen before the selected tuple D.
Neither the selected active support nor its frequency partition occurs
in this choice. Linear N(f) conductor control is supplied by SharpFamily. -/
theorem fixed_sharp_families (q : Data α) (x : Frozen q) (hf : Supported (frozenProduct q x))
    (s : Source (RestIndex q) a b) (seed : Id) (τ : Character) (ξ : RayCharacter) :
    ∃ψ : (p : FixedLabel (fixedPool q x s seed))→Finset (CommonIndex p.val.1 p.val.2)→
      RayCharacter→Character,
    ∀p U,OuterFreshNonexceptionalFamily.SharpFamily τ (frozenProduct q x) ξ p.val.1 p.val.2
      (commonLabels_supported (fixedPool q x s seed) _ _ p.property).1
      (commonLabels_supported (fixedPool q x s seed) _ _ p.property).2 U (ψ p U) := by
  have hh : ∀(p : FixedLabel (fixedPool q x s seed))(U : Finset (CommonIndex p.val.1 p.val.2)),
      ∃ψ : RayCharacter→Character,
        OuterFreshNonexceptionalFamily.SharpFamily τ (frozenProduct q x) ξ p.val.1 p.val.2
          (commonLabels_supported (fixedPool q x s seed) _ _ p.property).1
          (commonLabels_supported (fixedPool q x s seed) _ _ p.property).2 U ψ := by
    intro p U
    exact OuterFreshNonexceptionalFamily.exists_sharp_family τ (frozenProduct q x) hf ξ _ _ _ _
      (commonLabels_data _ _ _ _ p.property).2.2 U
  choose ψ hψ using hh
  exact ⟨ψ,hψ⟩

/-- Exact child vector after fixing a common label and a Fourier profile.
The vector inside the sum is independent of D. Its only moving factor
is the genuine cubic value at D, with all natural zeros still present.
The arbitrary profile here is a coefficient identity, not an estimate. -/
theorem fixed_child_polynomial (q : Data α) (x : Frozen q) (y : Selected q)
    (τ : Character) (ξ χ : RayCharacter) (C E : Id) (hC : Supported C) (hE : Supported E)
    (U : Finset (CommonIndex C E)) (ψ : RayCharacter→Character)
    (hψ : OuterFreshNonexceptionalFamily.SharpFamily τ (frozenProduct q x) ξ C E hC hE U ψ)
    (seed G L : Id) (Is : Finset Id) (hIs : ∀I∈Is,Supported I)
    (hcop : ∀I∈Is,IsCoprime C I ∨ IsCoprime E I) (profile : Id→ℂ) (t : ℝ) (z : O) :
    (∑I∈Is,profile I*
      (divisorCoefficient L (fun J : Id=>primaryGenerator J)
        (movingCoefficient (OuterFreshStructure.oldMoving C E U) (fun J : Id=>primaryGenerator J)
          (fun J=>outerColumn q x y seed ξ (G*J)*heightCoeff τ t J)) χ I*idealRowHom z I))=
      twist (primaryGenerator (frozenProduct q x)) (primaryGenerator (selectedProduct q y)) ξ G*
        ∑I∈Is,(profile I*(if L∣I then commonColumn q x seed (G*I) else 0))*
          (heightCoeff (ψ χ) t I*(idealRowHom (primaryGenerator (selectedProduct q y)) I)^2*
            idealRowHom z I) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [OuterFreshNonexceptionalFamily.actual_child_coefficient q x y τ ξ χ C E hC hE U ψ hψ
    seed G L I (hIs I hI) (hcop I hI) t z]
  ring

/-- D-dependent zeros outside the source polynomial. This predicate is
independent of the representation of D by a tuple of marked primes. -/
def outerGate (q : Data α) (x : Frozen q) (τ : Character) (D : Id) : Prop :=
  selectedGate q.R (frozenProduct q x) D ∧ Supported (frozenProduct q x*D) ∧
    idealCoeff τ (frozenProduct q x*D)≠0

def outerGroupedWeight (q : Data α) (x : Frozen q) (τ : Character) (D : Id) : ℝ :=
  if outerGate q x τ D then groupedWeight q D else 0

theorem selected_weight_gate (q : Data α) (x : Frozen q) (y : Selected q) (τ : Character) :
    selectedPositiveWeight q x y τ=
      if outerGate q x τ (selectedProduct q y) then ‖selectedWeight q y‖^2 else 0 := by
  by_cases hg : outerGate q x τ (selectedProduct q y)
  · rw [if_pos hg]
    by_cases hw : selectedWeight q y=0
    · unfold selectedPositiveWeight
      split_ifs <;> simp only [hw,norm_zero,zero_pow (by decide : 2≠0)]
    · exact if_pos ⟨hg.1,hw,hg.2.1,hg.2.2⟩
  · rw [if_neg hg]
    apply if_neg
    intro h
    exact hg ⟨h.gate,h.support,h.coefficient⟩

theorem positive_weight_zero_unsupported (q : Data α) (x : Frozen q) (y : Selected q)
    (τ : Character) (h : ¬Supported (selectedProduct q y)) : selectedPositiveWeight q x y τ=0 := by
  by_contra hn
  have hs := (selected_positive_active q x y τ hn).support
  exact h ((supported_mul_iff _ _).mp hs).2

/-- Exact grouping of the actual natural-zero weight. The previously
proved groupedWeight divisor bound therefore applies without alteration. -/
theorem selected_positive_grouping (q : Data α) (x : Frozen q) (τ : Character) (F : Id→ℝ) :
    (∑y∈activeSelected q,selectedPositiveWeight q x y τ*F (selectedProduct q y))=
      ∑D∈selectedProducts q,outerGroupedWeight q x τ D*F D := by
  have hs : (∑y∈activeSelected q,selectedPositiveWeight q x y τ*F (selectedProduct q y))=
      ∑y∈supportedSelected q,selectedPositiveWeight q x y τ*F (selectedProduct q y) := by
    unfold supportedSelected
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases h : Supported (selectedProduct q y)
    · rw [if_pos h]
    · rw [if_neg h,positive_weight_zero_unsupported q x y τ h,zero_mul]
  rw [hs]
  calc
    _=∑y∈supportedSelected q,‖selectedWeight q y‖^2*
        (if outerGate q x τ (selectedProduct q y) then F (selectedProduct q y) else 0) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [selected_weight_gate]
      split_ifs <;> simp only [mul_zero,zero_mul]
    _=∑D∈selectedProducts q,groupedWeight q D*(if outerGate q x τ D then F D else 0) :=
      selected_grouping q (fun D : Id=>if outerGate q x τ D then F D else 0)
    _=_ := by
      apply Finset.sum_congr rfl
      intro D hD
      unfold outerGroupedWeight
      split_ifs <;> simp only [mul_zero,zero_mul]

theorem outer_grouped_nonneg (q : Data α) (x : Frozen q) (τ : Character) (D : Id) :
    0≤outerGroupedWeight q x τ D := by
  unfold outerGroupedWeight
  split_ifs
  · exact grouped_weight_nonneg q D
  · exact le_refl _

theorem outer_grouped_le (q : Data α) (x : Frozen q) (τ : Character) (D : Id) :
    outerGroupedWeight q x τ D≤groupedWeight q D := by
  unfold outerGroupedWeight
  split_ifs
  · exact le_refl _
  · exact grouped_weight_nonneg q D

def parameterColumn (q : Data α) (x : Frozen q) (seed : Id) (ξ : RayCharacter)
    (D I : Id) : ℂ :=
  commonColumn q x seed I*(idealRowHom (primaryGenerator (frozenProduct q x)) I)^2*
    (idealRowHom (primaryGenerator D) I)^2*rayCharacter ξ (primaryGenerator I)

theorem outer_column_parameter (q : Data α) (x : Frozen q) (y : Selected q)
    (seed : Id) (ξ : RayCharacter) :
    outerColumn q x y seed ξ=parameterColumn q x seed ξ (selectedProduct q y) := rfl

/-- The full original-K energies group by the actual selected product,
with the same canonical source pool, not independently varying vectors. -/
theorem selected_energy_grouping (q : Data α) (x : Frozen q)
    (s : Source (RestIndex q) a b) (seed : Id) (τ : Character) (ξ : RayCharacter)
    (t : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑y∈activeSelected q,selectedPositiveWeight q x y τ*
      (sourceGaussEnergy (sourceColumns s) (outerColumn q x y seed ξ) (heightCoeff τ t) Φ K).re)=
      ∑D∈selectedProducts q,outerGroupedWeight q x τ D*
        (sourceGaussEnergy (fixedPool q x s seed) (parameterColumn q x seed ξ D)
          (heightCoeff τ t) Φ K).re := by
  have he (y : Selected q) :
      sourceGaussEnergy (sourceColumns s) (outerColumn q x y seed ξ) (heightCoeff τ t) Φ K=
        sourceGaussEnergy (fixedPool q x s seed) (outerColumn q x y seed ξ) (heightCoeff τ t) Φ K :=
    energy_fixed_support _ _ _ _ (outer_supported_by_common q x y seed ξ) Φ K
  simp_rw [he,outer_column_parameter]
  exact selected_positive_grouping q x τ (fun D : Id=>
    (sourceGaussEnergy (fixedPool q x s seed) (parameterColumn q x seed ξ D)
      (heightCoeff τ t) Φ K).re)

/-- The literal original-K zero mode. K/16, W=1 merely specializes the
existing Poisson dictionary to scale K; no K4 completion occurs here. -/
def outerZero (q : Data α) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (seed : Id) (τ : Character) (ξ : RayCharacter)
    (t K : ℝ) : ℂ :=
  zeroDensity Finset.univ (sourceGenerator (sourceColumns s))
    (sourceGenerator_supported (sourceColumns s))
    (fun I : supportedColumns (sourceColumns s)=>outerColumn q x y seed ξ I*heightCoeff τ t I)
    (K/16) 1

def fourCost (q : Data α) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (seed : Id) (τ : Character) (ξ χ : RayCharacter)
    (Q : Id) (t K T Z ζ H : ℝ) : ℝ :=
  ‖outerZero q x y s seed τ ξ t K‖+
    ‖fixedPart false q x y s seed τ ξ χ Q t ballProfile K T Z ζ H‖+
    ‖fixedPart true q x y s seed τ ξ χ Q t ballProfile K T Z ζ H‖+
    ‖secondDiscardedEnergy τ t (sourceColumns s) (outerColumn q x y seed ξ) ballProfile K T Z ζ‖

/-- An actual four-component energy interface. Both retained terms use
the NEW combined partition and the same fixed pool and fixed profiles.
The zero and discarded terms are explicit original-K Fourier sums. -/
theorem actual_four_components (q : Data α) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (seed : Id) (τ : Character) (ξ χ : RayCharacter)
    (Q : Id) (t K T Z ζ H : ℝ) (hK : 0<K)
    (hH : ∀I∈fixedPool q x s seed,(I.absNorm:ℝ)≤H) :
    (sourceGaussEnergy (sourceColumns s) (outerColumn q x y seed ξ)
      (heightCoeff τ t) ballProfile K).re≤fourCost q x y s seed τ ξ χ Q t K T Z ζ H := by
  have hscale : 16*(K/16)*(1:ℝ)^4=K := by ring
  have he := density_normalized_poisson Finset.univ
    (sourceGenerator (sourceColumns s)) (sourceGenerator_supported (sourceColumns s))
    (fun I : supportedColumns (sourceColumns s)=>outerColumn q x y seed ξ I*heightCoeff τ t I)
    (K/16) 1 (by positivity) (by norm_num)
  rw [hscale,Complex.ofReal_one,div_one,density_split _ _ _ _ (K/16) 1
    (frequencyRadius T Z ζ) (by positivity) (by norm_num)] at he
  rw [MixedLocalizedDictionary.source_retained τ t _ _ (K/16) 1 T Z ζ (by norm_num),
    MixedLocalizedDictionary.source_discarded τ t _ _ (K/16) 1 T Z ζ (by norm_num),
    hscale,Complex.ofReal_one,div_one,div_one] at he
  have hr := fixed_retained_split q x y s seed τ ξ χ Q t ballProfile K T Z ζ H hK hH
  rw [hr] at he
  change (gaussEnergy _ _ _ _ _ _).re≤_
  rw [he]
  unfold fourCost outerZero
  simp only [Complex.add_re]
  have h₀ := Complex.re_le_norm (outerZero q x y s seed τ ξ t K)
  have h₁ := Complex.re_le_norm (fixedPart true q x y s seed τ ξ χ Q t ballProfile K T Z ζ H)
  have h₂ := Complex.re_le_norm (fixedPart false q x y s seed τ ξ χ Q t ballProfile K T Z ζ H)
  have h₃ := Complex.re_le_norm
    (secondDiscardedEnergy τ t (sourceColumns s) (outerColumn q x y seed ξ) ballProfile K T Z ζ)
  unfold outerZero at h₀
  linarith

private theorem finite_original_energy (q : Data α) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (ha : 0<a) (hm : Matches q x s ha)
    (seed : Id) (τ : Character) (t : ℝ) (ξ : RayCharacter)
    (Ks : Finset O) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hΦ : ∀z : O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (∑k∈Ks,(Φ (‖ConcreteTraceCRT.eisEmbedding k‖^2/K)).re*
      ‖originalPolynomial q x y seed τ t ξ k‖^2)≤
      (sourceGaussEnergy (sourceColumns s) (outerColumn q x y seed ξ)
        (heightCoeff τ t) Φ K).re := by
  have hh := finite_weighted_le_gaussEnergy Finset.univ
    (sourceGenerator (sourceColumns s)) (sourceGenerator_supported (sourceColumns s))
    (fun I : supportedColumns (sourceColumns s)=>outerColumn q x y seed ξ I*heightCoeff τ t I)
    Φ K hK hΦ Ks
  apply le_trans _ hh
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro k hk
  rw [canonical_source_polynomial q x y s ha hm seed τ t ξ]
  exact mul_comm _ _

/-- Real positive supplier reduction all the way to the canonical
source energies, at the original scale. The seed precedes all profiles,
Hecke characters, heights and finite frequency pools. -/
theorem uniform_supplier_energies (q : Data α) (x : Frozen q) (hx : Function.Injective x)
    (s : Source (RestIndex q) a b) (ha : 0<a) (hm : Matches q x s ha) :
    ∃seed : Id,(frozenWeight q x≠0→q.u=frozenProduct q x*seed) ∧
      ∀(τ : Character)(t : ℝ)(Ks : Finset O)(Φ : 𝓢(ℝ,ℂ))(K : ℝ),0<K→
      (∀z : O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)→
      (∑k∈Ks,(Φ (‖ConcreteTraceCRT.eisEmbedding k‖^2/K)).re*
        ‖frozenWeight q x*originalFamily q x τ t k‖^2)≤
      ‖frozenWeight q x‖^2*(256*((activeSelected q).card:ℝ)*
        ∑y∈activeSelected q,∑χ : RayCharacter,∑ξ : RayCharacter,
          ‖pairCoeff firstPhaseTable χ ξ‖*selectedPositiveWeight q x y τ*
            (sourceGaussEnergy (sourceColumns s) (outerColumn q x y seed ξ)
              (heightCoeff τ t) Φ K).re) := by
  obtain ⟨seed,hseed,hbound⟩ := MixedSupplierOuterFamily.uniform_weighted_original_sum q x hx
  refine ⟨seed,hseed,?_⟩
  intro τ t Ks Φ K hK hΦ
  apply (hbound τ t Ks (fun z=>(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (fun z _=>hΦ z)).trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro y hy
  apply Finset.sum_le_sum
  intro χ hχ
  apply Finset.sum_le_sum
  intro ξ hξ
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (norm_nonneg _) (selected_positive_nonneg q x y τ))
  exact finite_original_energy q x y s ha hm seed τ t ξ Ks Φ K hK hΦ

/-- Every component of every selected tuple is present. This is a
proved interface, not an estimate assumed for the nonexceptional part. -/
theorem uniform_supplier_four_components (q : Data α) (x : Frozen q) (hx : Function.Injective x)
    (s : Source (RestIndex q) a b) (ha : 0<a) (hm : Matches q x s ha) :
    ∃seed : Id,(frozenWeight q x≠0→q.u=frozenProduct q x*seed) ∧
      ∀(τ : Character)(t : ℝ)(Ks : Finset O)(K T Z ζ H : ℝ),0<K→
      (∀z : O,0≤(ballProfile (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)→
      (∀I∈fixedPool q x s seed,(I.absNorm:ℝ)≤H)→∀(χ₀ : RayCharacter)(Q : Id),
      (∑k∈Ks,(ballProfile (‖ConcreteTraceCRT.eisEmbedding k‖^2/K)).re*
        ‖frozenWeight q x*originalFamily q x τ t k‖^2)≤
      ‖frozenWeight q x‖^2*(256*((activeSelected q).card:ℝ)*
        ∑y∈activeSelected q,∑χ : RayCharacter,∑ξ : RayCharacter,
          ‖pairCoeff firstPhaseTable χ ξ‖*selectedPositiveWeight q x y τ*
            fourCost q x y s seed τ ξ χ₀ Q t K T Z ζ H) := by
  obtain ⟨seed,hseed,hbound⟩ := uniform_supplier_energies q x hx s ha hm
  refine ⟨seed,hseed,?_⟩
  intro τ t Ks K T Z ζ H hK hΦ hH χ₀ Q
  apply (hbound τ t Ks ballProfile K hK hΦ).trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro y hy
  apply Finset.sum_le_sum
  intro χ hχ
  apply Finset.sum_le_sum
  intro ξ hξ
  exact mul_le_mul_of_nonneg_left
    (actual_four_components q x y s seed τ ξ χ₀ Q t K T Z ζ H hK hH)
    (mul_nonneg (norm_nonneg _) (selected_positive_nonneg q x y τ))

end
end Candidate.FourthPower.OuterFreshConsumer
