/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact complete-prime-part extraction of the forced divisor at the source row. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Second.RestoredDivisor
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Second.RestoredNewtonEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RestrictedSourceNormalization

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Second
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve IdealMobiusDivisorSum
open CenteredMomentSupport CenteredMomentFirstSectors CenteredMomentCommonAllocation
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass
open CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy CenteredMomentSourceRectangleEnergy
open CenteredMomentSourceRectangle CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow
open CenteredMomentSourceRow CenteredMomentRowNorm CenteredMomentRestrictedWindow
open CenteredMomentActiveSource CenteredMomentSecondHeightFamily CenteredMomentAbsoluteEnergy
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale CenteredMomentCommonRawCost
open CenteredMomentRestrictedSourceNormalization
open Record1252270103Source
local notation "O" => ActualEisensteinCubic.O

def forcedLabels (L : Ideal O) (S : Finset (Ideal O)) : Finset (Ideal O) :=
  S.image (forcedPart L)

theorem forcedLabel_ne_zero (L : Ideal O) (S : Finset (Ideal O)) (C : forcedLabels L S) :
    (C:Ideal O)≠0 := by
  obtain ⟨I,hI,he⟩ := Finset.mem_image.mp C.property
  rw [←he]
  exact supportExtract_ne_zero _ _

theorem forcedLabel_support (L : Ideal O) (S : Finset (Ideal O)) (hL : L≠0)
    (hS : ∀I∈S,I≠0) (hLS : ∀I∈S,L∣I) (C : forcedLabels L S) :
    primeSupport (C:Ideal O)=primeSupport L := by
  obtain ⟨I,hI,he⟩ := Finset.mem_image.mp C.property
  rw [←he]
  exact forcedPart_support L I hL (hS I hI) (hLS I hI)

theorem forced_sector_image (L C : Ideal O) (hC : C≠0)
    (hCL : primeSupport C=primeSupport L) (S : Finset (Ideal O))
    (hS : ∀I∈S,I≠0) :
    ((residualPool C hC S).filter (fun J=>IsCoprime C J)).image (fun J=>C*J)=
      S.filter (fun I=>forcedPart L I=C) := by
  ext I
  constructor
  · intro h
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hJ,hcop⟩ := Finset.mem_filter.mp hJ
    have hCJ : C*J∈S := (mem_residualPool C hC S J).mp hJ
    refine Finset.mem_filter.mpr ⟨hCJ,?_⟩
    unfold forcedPart
    rw [←hCL]
    exact extract_coprime_product C J hC (right_ne_zero_of_mul (hS _ hCJ)) hcop
  · intro h
    obtain ⟨hI,hpart⟩ := Finset.mem_filter.mp h
    have he : C*supportResidual I (primeSupport L)=I := by
      rw [←hpart]
      exact support_reconstruct I (hS I hI) _
    refine Finset.mem_image.mpr ⟨supportResidual I (primeSupport L),?_,he⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply (mem_residualPool C hC S _).mpr
      rw [he]
      exact hI
    · rw [←hpart]
      exact extracted_residual_coprime _ _ _

theorem forced_sector_sum (L C : Ideal O) (hC : C≠0)
    (hCL : primeSupport C=primeSupport L) (S : Finset (Ideal O))
    (hS : ∀I∈S,I≠0) (f : Ideal O→ℂ) :
    (∑I∈S.filter (fun I=>forcedPart L I=C),f I)=
      ∑J∈residualPool C hC S,if IsCoprime C J then f (C*J) else 0 := by
  rw [←forced_sector_image L C hC hCL S hS,Finset.sum_image]
  · rw [Finset.sum_filter]
  · intro I hI J hJ h
    exact mul_left_cancel₀ hC h

/-- Exact row decomposition. The entire L-prime part is removed, so all
marked/ordinary coincidences remain in the frozen common factor. -/
theorem forced_source_sum (L : Ideal O) (S : Finset (Ideal O)) (hL : L≠0)
    (hS : ∀I∈S,I≠0) (hLS : ∀I∈S,L∣I) (β : Ideal O→ℂ) (ψ : Ideal O→*ℂ) :
    (∑I∈S,β I*ψ I)=
      ∑C : forcedLabels L S,ψ C*
        ∑J∈residualPool C (forcedLabel_ne_zero L S C) S,
          if IsCoprime (C:Ideal O) J then β (C*J)*ψ J else 0 := by
  have h := Finset.sum_fiberwise_of_maps_to (s:=S) (t:=forcedLabels L S) (g:=forcedPart L)
    (fun I hI=>Finset.mem_image.mpr ⟨I,hI,rfl⟩) (fun I=>β I*ψ I)
  rw [←h,←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro C hC
  rw [forced_sector_sum L C (forcedLabel_ne_zero L S C)
    (forcedLabel_support L S hL hS hLS C) S hS,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  split_ifs <;> simp only [map_mul,mul_zero]
  ring

/-- A finite complete-prime-part decomposition passes through the same
completed positive norm, without removing or changing any selected row. -/
theorem forced_source_energy (L : Ideal O) (S : Finset (Ideal O)) (hL : L≠0)
    (hS : ∀I∈S,I≠0) (hLS : ∀I∈S,L∣I) (β : Ideal O→ℂ)
    (τ : Character) (t : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) (hH : 0<H)
    (hΦ : ∀z : O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re) :
    sourceRestrictedEnergy keep S β (heightCoeff τ t) Φ H≤
      ((forcedLabels L S).card:ℝ)*∑C : forcedLabels L S,
        sourceRestrictedEnergy keep (residualPool C (forcedLabel_ne_zero L S C) S)
          (fun J=>if IsCoprime (C:Ideal O) J then β (C*J) else 0) (heightCoeff τ t) Φ H := by
  have hh := restricted_energy_divisor_transfer keep Finset.univ (sourceGenerator S)
    (sourceGenerator_supported S) (fun I=>β I*heightCoeff τ t I)
    (Finset.univ : Finset (forcedLabels L S))
    (fun C=>Finset.univ)
    (fun C=>sourceGenerator (residualPool C (forcedLabel_ne_zero L S C) S))
    (fun C=>sourceGenerator_supported (residualPool C (forcedLabel_ne_zero L S C) S))
    (fun C J=>(if IsCoprime (C:Ideal O) J then β (C*J) else 0)*heightCoeff τ t J)
    (fun C z=>rowWeight τ fixedBadMask 1 z t C) (fun _=>1)
    (fun _ _=>zero_le_one) (fun C _ z=>rowWeight_norm_le_one_all τ fixedBadMask 1 z t C)
    (by
      intro z
      rw [height_source_row τ t S β z]
      have hsum := forced_source_sum L S hL hS hLS β (rowWeight τ fixedBadMask 1 z t).toMonoidHom
      change (∑I∈S,β I*rowWeight τ fixedBadMask 1 z t I)=_ at hsum
      rw [hsum]
      apply Finset.sum_congr rfl
      intro C hC
      rw [height_source_row τ t (residualPool C (forcedLabel_ne_zero L S C) S)
        (fun J=>if IsCoprime (C:Ideal O) J then β (C*J) else 0) z]
      apply congrArg (fun x : ℂ=>rowWeight τ fixedBadMask 1 z t C*x)
      apply Finset.sum_congr rfl
      intro J hJ
      split_ifs <;> simp) Φ H hH hΦ
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,mul_one,
    one_mul,sourceRestrictedEnergy] using hh

theorem source_energy_active_supported (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (τ : Character) (t : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) :
    sourceRestrictedEnergy keep (supportedColumns (activeSource S β)) β (heightCoeff τ t) Φ H=
      sourceRestrictedEnergy keep S β (heightCoeff τ t) Φ H := by
  unfold sourceRestrictedEnergy restrictedEnergy
  apply tsum_congr
  intro z
  rw [height_source_row,height_source_row]
  have he : (∑I∈supportedColumns (activeSource S β),β I*rowWeight τ fixedBadMask 1 z t I)=
      ∑I∈S,β I*rowWeight τ fixedBadMask 1 z t I := by
    rw [supportedColumns,activeSource,Finset.filter_filter,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro I hI
    by_cases hb : β I=0
    · simp only [hb,zero_mul,ite_self]
    by_cases hs : Supported I
    · rw [ite_eq_left ⟨hb,hs⟩]
    · rw [rowWeight_zero_of_not_supported τ fixedBadMask 1 z t
        (dvd_mul_right _ _) (dvd_mul_left _ _) I hs]
      simp only [mul_zero,ite_self]
  rw [he]

theorem residual_energy_active_supported (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C : Ideal O) (hC : Supported C) (τ : Character) (t : ℝ) (keep : O→Prop)
    (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) :
    sourceRestrictedEnergy keep
      (residualPool C hC.1 (supportedColumns (activeSource S β)))
      (fun J=>if IsCoprime C J then β (C*J) else 0) (heightCoeff τ t) Φ H=
    sourceRestrictedEnergy keep (residualPool C hC.1 S)
      (fun J=>if IsCoprime C J then β (C*J) else 0) (heightCoeff τ t) Φ H := by
  have hset : residualPool C hC.1 (supportedColumns (activeSource S β))=
      (residualPool C hC.1 S).filter (fun J=>β (C*J)≠0 ∧ Supported J) := by
    ext J
    simp only [mem_residualPool,supportedColumns,activeSource,Finset.mem_filter,
      supported_mul_iff,hC,true_and,and_assoc]
  rw [hset]
  unfold sourceRestrictedEnergy restrictedEnergy
  apply tsum_congr
  intro z
  rw [height_source_row τ t _ (fun J=>if IsCoprime C J then β (C*J) else 0),
    height_source_row τ t _ (fun J=>if IsCoprime C J then β (C*J) else 0)]
  have he : (∑J∈(residualPool C hC.1 S).filter (fun J=>β (C*J)≠0 ∧ Supported J),
      (if IsCoprime C J then β (C*J) else 0)*rowWeight τ fixedBadMask 1 z t J)=
      ∑J∈residualPool C hC.1 S,(if IsCoprime C J then β (C*J) else 0)*rowWeight τ fixedBadMask 1 z t J := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro J hJ
    by_cases hb : β (C*J)=0
    · simp only [hb,ite_self,zero_mul]
    by_cases hs : Supported J
    · rw [ite_eq_left ⟨hb,hs⟩]
    · rw [rowWeight_zero_of_not_supported τ fixedBadMask 1 z t
        (dvd_mul_right _ _) (dvd_mul_left _ _) J hs]
      simp only [mul_zero,ite_self]
  rw [he]

variable {ι : Type*} [Fintype ι]
local instance restoredChildDecidable : DecidableEq (ι⊕Fin 2) := Classical.decEq _
local notation "coefficient" => QRH.Record1252270103Source.High.CoupledFirst.coefficient

def forcedSource (s : Input ι) (modifier : Tuple ι→ℂ) (R L : Ideal O) : Finset (Ideal O) :=
  supportedColumns (activeSource (finiteColumns (Fintype.piFinset s.pools)) (coefficient s modifier R L))

theorem forcedSource_seed (s : Input ι) (modifier : Tuple ι→ℂ) (R L : Ideal O)
    (I : Ideal O) (hI : I∈forcedSource s modifier R L) : L∣I := by
  have hn : coefficient s modifier R L I≠0 :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2
  unfold QRH.Record1252270103Source.High.CoupledFirst.coefficient
    QRH.Record1252270103Source.High.CoupledFirst.tupleCoefficient finiteColumnCoefficient at hn
  obtain ⟨v,hv,hvn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hprof : profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 L v≠0 :=
    right_ne_zero_of_mul hvn
  rw [←(Finset.mem_filter.mp hv).2]
  by_contra hbad
  exact hprof (by simp [profileCoefficient,hbad])

theorem forcedSource_label_supported (s : Input ι) (modifier : Tuple ι→ℂ) (R L : Ideal O)
    (C : forcedLabels L (forcedSource s modifier R L)) : Supported (C:Ideal O) := by
  obtain ⟨I,hI,he⟩ := Finset.mem_image.mp C.property
  rw [←he]
  exact supportExtract_supported I (Finset.mem_filter.mp hI).2 _

theorem forcedSource_label_seed (s : Input ι) (modifier : Tuple ι→ℂ) (R L : Ideal O)
    (hL : L≠0) (C : forcedLabels L (forcedSource s modifier R L)) : L∣(C:Ideal O) := by
  obtain ⟨I,hI,he⟩ := Finset.mem_image.mp C.property
  rw [←he]
  exact forcedPart_contains_seed L I hL (Finset.mem_filter.mp hI).2.1
    (forcedSource_seed s modifier R L I hI)

/-- The artificial seed is discharged by full common extraction. Every RHS
term is an actual allocated Input with seed 1 and the pulled original
modifier. All complete allocation cardinalities and keep predicates survive. -/
theorem actual_forced_allocated_energy (s : Input ι) (modifier : Tuple ι→ℂ)
    (R L : Ideal O) (hL : L≠0) (τ : Character) (t : ℝ) (keep : O→Prop)
    (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) (hH : 0<H)
    (hΦ : ∀z : O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re) :
    sourceRestrictedEnergy keep (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s modifier R L) (heightCoeff τ t) Φ H≤
      ((forcedLabels L (forcedSource s modifier R L)).card:ℝ)*
        ∑C : forcedLabels L (forcedSource s modifier R L),
          allocatedDivisorEnergy s modifier C R 1 τ t keep Φ H := by
  rw [←source_energy_active_supported _ (coefficient s modifier R L) τ t keep Φ H]
  apply (forced_source_energy L (forcedSource s modifier R L) hL
    (fun I hI=>(Finset.mem_filter.mp hI).2.1)
    (forcedSource_seed s modifier R L) (coefficient s modifier R L) τ t keep Φ H hH hΦ).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro C hC
  have hc := forcedSource_label_supported s modifier R L C
  unfold forcedSource
  rw [residual_energy_active_supported (finiteColumns (Fintype.piFinset s.pools))
    (coefficient s modifier R L) C hc τ t keep Φ H]
  simpa only [one_dvd,and_true] using actual_allocated_divisor_energy s modifier C R L 1 hc
    (forcedSource_label_seed s modifier R L hL C) τ t keep Φ H hH hΦ

def forcedProfileCost (s : Input ι) : ℝ :=
  (∏i,s.M i)^2*(max 1 s.upper)^Fintype.card ι

theorem forcedProfileCost_nonneg (s : Input ι) : 0≤forcedProfileCost s := by
  unfold forcedProfileCost
  positivity

theorem child_volume_remaining (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    volume (child s C R B τ t)=remainingRaw B.val (s.X₁*s.X₂) s.P := by
  unfold volume child commonData remainingRaw plainNorm
  ring

theorem allocated_energy_normalized_eq (s : Input ι) (modifier : Tuple ι→ℂ)
    (C R L : Ideal O) (τ : Character) (t : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) :
    allocatedDivisorEnergy s modifier C R L τ t keep Φ H/volume s=
      ((actualAllocations s.pools C).card:ℝ)*∑B : actualAllocations s.pools C,
        (‖frozenCoefficient B C R s.ν s.W s.P‖^2/rawReduction B.val s.P)*
          (childDivisorEnergy s modifier C R L B τ t keep Φ H/volume (child s C R B τ t)) := by
  unfold allocatedDivisorEnergy
  rw [mul_div_assoc,Finset.sum_div]
  apply congrArg (fun x : ℝ=>((actualAllocations s.pools C).card:ℝ)*x)
  apply Finset.sum_congr rfl
  intro B hB
  have hb := (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1
  have hr := raw_scale_identity B.val hb (s.X₁*s.X₂) s.P
  have hred := rawReduction_pos B.val hb s.P s.P_pos
  have hvol := volume_pos (child s C R B τ t)
  rw [child_volume_remaining] at hvol ⊢
  change remainingRaw B.val (s.X₁*s.X₂) s.P*rawReduction B.val s.P=volume s at hr
  rw [←hr]
  field_simp [hred.ne',hvol.ne']

/-- Quantitative common norm saving for the exact modified children. The
analytic premise is on normalized seed-1 children after complete extraction,
not on the seed-L source being bounded. -/
theorem allocated_energy_from_normalized_children (s : Input ι) (modifier : Tuple ι→ℂ)
    (C R : Ideal O) (hC : C≠0) (τ : Character) (t : ℝ) (keep : O→Prop)
    (Φ : 𝓢(ℝ,ℂ)) (H E : ℝ) (hE : 0≤E)
    (hchild : ∀B : actualAllocations s.pools C,
      childDivisorEnergy s modifier C R 1 B τ t keep Φ H/volume (child s C R B τ t)≤E) :
    allocatedDivisorEnergy s modifier C R 1 τ t keep Φ H/volume s≤
      ((actualAllocations s.pools C).card:ℝ)^2*forcedProfileCost s*E/C.absNorm := by
  rw [allocated_energy_normalized_eq]
  calc
    _≤((actualAllocations s.pools C).card:ℝ)*
        ∑_B : actualAllocations s.pools C,(forcedProfileCost s/C.absNorm)*E := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B hB
      have hb := (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1
      have hprod : finiteTupleProduct B.val=C := (Finset.mem_filter.mp B.property).2
      have hc := frozen_normalized_cost B.val hb C R hC hprod s.ν s.W s.P s.M
        s.P_pos s.ν_bound s.W_bound s.M_ge_one s.lower s.upper s.lower_pos s.slot_support
      have hf : 0≤‖frozenCoefficient B C R s.ν s.W s.P‖^2/rawReduction B.val s.P :=
        div_nonneg (sq_nonneg _) (rawReduction_pos B.val hb s.P s.P_pos).le
      exact (mul_le_mul_of_nonneg_left (hchild B) hf).trans
        (mul_le_mul_of_nonneg_right hc hE)
    _=_ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul];ring

theorem actual_forced_norm_saving (s : Input ι) (modifier : Tuple ι→ℂ)
    (R L : Ideal O) (hL : L≠0) (τ : Character) (t : ℝ) (keep : O→Prop)
    (Φ : 𝓢(ℝ,ℂ)) (H E : ℝ) (hH : 0<H) (hE : 0≤E)
    (hΦ : ∀z : O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re)
    (hchild : ∀C : forcedLabels L (forcedSource s modifier R L),
      ∀B : actualAllocations s.pools (C:Ideal O),
      childDivisorEnergy s modifier C R 1 B τ t keep Φ H/volume (child s C R B τ t)≤E) :
    sourceRestrictedEnergy keep (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s modifier R L) (heightCoeff τ t) Φ H/volume s≤
      (((forcedLabels L (forcedSource s modifier R L)).card:ℝ)*
        ∑C : forcedLabels L (forcedSource s modifier R L),((actualAllocations s.pools (C:Ideal O)).card:ℝ)^2)*
          (forcedProfileCost s*E)/(L.absNorm:ℝ) := by
  have h := div_le_div_of_nonneg_right
    (actual_forced_allocated_energy s modifier R L hL τ t keep Φ H hH hΦ) (volume_pos s).le
  apply h.trans
  rw [mul_div_assoc,Finset.sum_div]
  calc
    _≤((forcedLabels L (forcedSource s modifier R L)).card:ℝ)*
        ∑C : forcedLabels L (forcedSource s modifier R L),
          ((actualAllocations s.pools (C:Ideal O)).card:ℝ)^2*forcedProfileCost s*E/(L.absNorm:ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro C hC
      apply (allocated_energy_from_normalized_children s modifier C R
        (forcedLabel_ne_zero L _ C) τ t keep Φ H E hE (hchild C)).trans
      have hnC : (0:ℝ)<(C:Ideal O).absNorm := by
        exact_mod_cast Nat.pos_of_ne_zero
          (Ideal.absNorm_eq_zero_iff.not.mpr (forcedLabel_ne_zero L _ C))
      have hnL : (0:ℝ)<L.absNorm := by
        exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hL)
      have hn : (L.absNorm:ℝ)≤(C:Ideal O).absNorm := by
        exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero
          (Ideal.absNorm_eq_zero_iff.not.mpr (forcedLabel_ne_zero L _ C)))
          (map_dvd Ideal.absNorm (forcedSource_label_seed s modifier R L hL C))
      exact div_le_div_of_nonneg_left
        (mul_nonneg (mul_nonneg (sq_nonneg _) (forcedProfileCost_nonneg s)) hE) hnL hn
    _=_ := by
      rw [←Finset.sum_div,←Finset.sum_mul,←Finset.sum_mul]
      ring

/-- Only subpower many complete forced parts occur, even with overlapping
marked pools. This count concerns actual nonzero columns. -/
theorem forced_labels_small_power (ε : ℝ) (hε : 0<ε) :
    ∃K : ℝ,0<K ∧ ∀(s : Input ι) (A₁ A₂ D R L : Ideal O) (F : Ideal O→ℂ),
      Squarefree L →
      ((forcedLabels L (forcedSource s (sourceModifier A₁ A₂ D F) R L)).card:ℝ)≤
        K*(L.absNorm:ℝ)^ε := by
  let n : ℕ:=Fintype.card ι+1
  have hn : (0:ℝ)<n := by dsimp [n];positivity
  obtain ⟨K,hK,hbound⟩ := IdealDivisorBound.ideal_divisor_small_power (ε/n) (div_pos hε hn)
  refine ⟨K,hK,?_⟩
  intro s A₁ A₂ D R L F hL
  have hsub : forcedLabels L (forcedSource s (sourceModifier A₁ A₂ D F) R L)⊆idealDivisors (L^n) := by
    intro C hC
    obtain ⟨I,hI,he⟩ := Finset.mem_image.mp hC
    have hcoeff : coefficient s (sourceModifier A₁ A₂ D F) R L I≠0 :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2
    rw [←he]
    exact (mem_idealDivisors (pow_ne_zero n hL.ne_zero)).mpr
      (actual_forced_part_bounds s A₁ A₂ D R L I F hL hcoeff).2.1
  apply (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
  apply (hbound (L^n) (pow_ne_zero n hL.ne_zero)).trans_eq
  rw [map_pow,Nat.cast_pow,←Real.rpow_natCast_mul (Nat.cast_nonneg _)]
  congr 2
  exact mul_div_cancel₀ ε hn.ne'

def forcedAllocationMass (s : Input ι) (modifier : Tuple ι→ℂ) (R L : Ideal O) : ℝ :=
  ((forcedLabels L (forcedSource s modifier R L)).card:ℝ)*
    ∑C : forcedLabels L (forcedSource s modifier R L),((actualAllocations s.pools (C:Ideal O)).card:ℝ)^2

theorem forced_allocation_mass_small_power (ε : ℝ) (hε : 0<ε) :
    ∃K : ℝ,0<K ∧ ∀(s : Input ι) (A₁ A₂ D R L : Ideal O) (F : Ideal O→ℂ),
      Squarefree L → forcedAllocationMass s (sourceModifier A₁ A₂ D F) R L≤K*(L.absNorm:ℝ)^ε := by
  let n : ℕ:=Fintype.card ι+1
  have hn : (0:ℝ)<n := by dsimp [n];positivity
  obtain ⟨K,hK,hlabels⟩ := forced_labels_small_power (ι:=ι) (ε/4) (by positivity)
  obtain ⟨D0,hD0,halloc⟩ := CenteredMomentAllocationCost.actualAllocations_uniform_small_power
    (Fintype.card (ι⊕Fin 2)) (ε/(4*n)) (by positivity)
  refine ⟨(K*D0)^2,by positivity,?_⟩
  intro s A₁ A₂ D R L F hL
  let mod := sourceModifier (ι:=ι) A₁ A₂ D F
  let T := forcedLabels L (forcedSource s mod R L)
  have hcard : (T.card:ℝ)≤K*(L.absNorm:ℝ)^(ε/4) := hlabels s A₁ A₂ D R L F hL
  have hone : (0:ℝ)≤L.absNorm := Nat.cast_nonneg _
  have heach (C : T) : ((actualAllocations s.pools (C:Ideal O)).card:ℝ)≤D0*(L.absNorm:ℝ)^(ε/4) := by
    obtain ⟨I,hI,he⟩ := Finset.mem_image.mp C.property
    have hcoeff : coefficient s mod R L I≠0 := (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2
    have hdiv : (C:Ideal O)∣L^n := by
      rw [←he]
      exact (actual_forced_part_bounds s A₁ A₂ D R L I F hL hcoeff).2.1
    have hnorm : ((C:Ideal O).absNorm:ℝ)≤(L.absNorm:ℝ)^n := by
      have hh := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (pow_ne_zero n hL.ne_zero))) (map_dvd Ideal.absNorm hdiv)
      simpa only [map_pow,Nat.cast_pow] using (Nat.cast_le (α:=ℝ)).mpr hh
    apply (halloc (le_refl _) s.pools C (forcedLabel_ne_zero L _ C)).trans
    apply mul_le_mul_of_nonneg_left _ hD0.le
    apply (Real.rpow_le_rpow (Nat.cast_nonneg _) hnorm (by positivity)).trans_eq
    rw [←Real.rpow_natCast_mul hone]
    congr 1
    field_simp
  have ha0 : 0≤D0*(L.absNorm:ℝ)^(ε/4) := mul_nonneg hD0.le (Real.rpow_nonneg hone _)
  have hh : forcedAllocationMass s mod R L≤(T.card:ℝ)^2*(D0*(L.absNorm:ℝ)^(ε/4))^2 := by
    unfold forcedAllocationMass
    apply le_trans (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun C _=>pow_le_pow_left₀ (Nat.cast_nonneg _) (heach C) 2)) (Nat.cast_nonneg _))
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
    dsimp only [T]
    exact le_of_eq (by ring)
  apply hh.trans
  apply le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2) (sq_nonneg _))
  apply le_of_eq
  have hpow : ((L.absNorm:ℝ)^(ε/4))^4=(L.absNorm:ℝ)^ε := by
    rw [←Real.rpow_mul_natCast hone]
    congr 1
    ring
  calc
    _=(K*D0)^2*((L.absNorm:ℝ)^(ε/4))^4 := by ring
    _=_ := by rw [hpow]

/-- The artificial-divisor payment is derived from complete extraction and
actual frozen coefficient/volume costs. Only normalized seed-1 source
estimates remain; no seed-L replacement-energy hypothesis is introduced. -/
theorem corrected_forced_source_bound (ε : ℝ) (hε : 0<ε) :
    ∃K : ℝ,0<K ∧ ∀(s : Input ι) (A₁ A₂ D R L : Ideal O) (F : Ideal O→ℂ),
      Squarefree L → ∀(τ : Character) (t : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (H E : ℝ),
      0<H → 0≤E → (∀z : O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re) →
      (∀C : forcedLabels L (forcedSource s (sourceModifier A₁ A₂ D F) R L),
        ∀B : actualAllocations s.pools (C:Ideal O),
        childDivisorEnergy s (sourceModifier A₁ A₂ D F) C R 1 B τ t keep Φ H/
          volume (child s C R B τ t)≤E) →
      sourceRestrictedEnergy keep (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s (sourceModifier A₁ A₂ D F) R L) (heightCoeff τ t) Φ H/volume s≤
        K*(L.absNorm:ℝ)^ε*(forcedProfileCost s*E)/(L.absNorm:ℝ) := by
  obtain ⟨K,hK,hbound⟩ := forced_allocation_mass_small_power (ι:=ι) ε hε
  refine ⟨K,hK,?_⟩
  intro s A₁ A₂ D R L F hL τ t keep Φ H E hH hE hΦ hchild
  apply (actual_forced_norm_saving s (sourceModifier A₁ A₂ D F) R L hL.ne_zero
    τ t keep Φ H E hH hE hΦ hchild).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_right (hbound s A₁ A₂ D R L F hL)
    (mul_nonneg (forcedProfileCost_nonneg s) hE)

end
end OAI.SevenEighths.Record1252270103Second

#print axioms OAI.SevenEighths.Record1252270103Second.forced_source_sum
#print axioms OAI.SevenEighths.Record1252270103Second.forced_source_energy
#print axioms OAI.SevenEighths.Record1252270103Second.actual_forced_allocated_energy
#print axioms OAI.SevenEighths.Record1252270103Second.actual_forced_norm_saving
#print axioms OAI.SevenEighths.Record1252270103Second.forced_labels_small_power
#print axioms OAI.SevenEighths.Record1252270103Second.corrected_forced_source_bound
