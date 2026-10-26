/- Copyright (c) 2026 Sil. Apache-2.0.
Exact zero-completion of EACH outer retained component separately.
Full common heights, natural zeros, original K and arbitrary row selectors.

-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.OuterFreshConsumer
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.OuterFreshRemainders

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.OuterFreshCompletion
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion ConcretePrimeRowBridge
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentGaussEnergy
open CenteredMomentFirstSectors CenteredMomentActiveSource CenteredMomentSecondActivePhysicalDictionary
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondBlockAggregate
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondLiveBlock CenteredMomentSecondLocalization
open CenteredMomentSectorLocalization CenteredMomentSourceSecondZeroEnergy
open CenteredMomentSupportedTailAggregate
open CenteredMomentFirstAmplificationChoice EisensteinSchwartzPoisson
open MixedSupplierFourthRow MixedSupplierSource MixedSupplierOuterActive MixedSupplierOriginalFrequency
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedPrincipalBudget
open MixedInnerExceptionalBlock
open MixedOriginalTail MixedOriginalSource MixedPoissonLocalization
open OuterFreshRows OuterFreshWindowPair OuterFreshAssembly OuterFreshConsumer
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- Every nonzero WHOLE physical summand has an actual active common
label. An isolated block would not retain the original tau natural zeros. -/
theorem full_block_active_label (τ : Character) (t : ℝ) (S : Finset Id) (β : Id→ℂ)
    (C E : Id) (hC : Supported C) (hE : Supported E) (hCE : primeSupport C=primeSupport E)
    (U : Finset (CommonIndex C E)) (R : ℝ) (rows : Finset O)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ)
    (hne : (heightCoeff τ t C*star (heightCoeff τ t E))*
      physicalBlock τ t S β C E hC hE U R rows Φ K n≠0) :
    (C,E)∈commonLabels (supportedColumns (activeSource S β)) (supportedColumns (activeSource S β)) := by
  obtain ⟨I,J,hpair,hcoeff⟩ := OuterFreshPhysical.exists_pair_of_full_block τ t S β
    C E hC hE hCE U R rows Φ K n hne
  have hp := Finset.mem_filter.mp hpair
  have hIJ := Finset.mem_product.mp hp.1
  have hi : β I≠0 := left_ne_zero_of_mul (left_ne_zero_of_mul hcoeff)
  have hjh : β J*heightCoeff τ t J≠0 := by
    simpa only [star_ne_zero] using right_ne_zero_of_mul hcoeff
  have hj : β J≠0 := left_ne_zero_of_mul hjh
  have hI : I∈supportedColumns (activeSource S β) := by
    rw [supportedColumns_active]
    exact Finset.mem_filter.mpr ⟨hIJ.1,hi⟩
  have hJ : J∈supportedColumns (activeSource S β) := by
    rw [supportedColumns_active]
    exact Finset.mem_filter.mpr ⟨hIJ.2,hj⟩
  exact Finset.mem_image.mpr ⟨(I,J),Finset.mem_product.mpr ⟨hI,hJ⟩,Prod.ext hp.2.1 hp.2.2⟩

/-- A nondependent label function makes finite support completion simple.
Its value contains the entire common-height coefficient. -/
def labelTerm (τ : Character) (t : ℝ) (S : Finset Id) (β : Id→ℂ)
    (rows : (C E : Id)→Finset (CommonIndex C E)→Finset O)
    (Φ : 𝓢(ℝ,ℂ)) (K R H : ℝ) (C E : Id) : ℂ :=
  if hC : Supported C then if hE : Supported E then
    (heightCoeff τ t C*star (heightCoeff τ t E))*
      ∑U : Finset (CommonIndex C E),∑n : SourceBlocks C E U K R H,
        physicalBlock τ t S β C E hC hE U R (rows C E U) Φ K (fun i=>(n i:ℤ))
  else 0 else 0

theorem labelTerm_zero_off_active (τ : Character) (t : ℝ) (S : Finset Id) (β : Id→ℂ)
    (rows : (C E : Id)→Finset (CommonIndex C E)→Finset O)
    (Φ : 𝓢(ℝ,ℂ)) (K R H : ℝ) (C E : Id) (hCE : primeSupport C=primeSupport E)
    (hn : (C,E)∉commonLabels (supportedColumns (activeSource S β))
      (supportedColumns (activeSource S β))) : labelTerm τ t S β rows Φ K R H C E=0 := by
  unfold labelTerm
  split_ifs with hC hE
  · simp_rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro U hU
    apply Finset.sum_eq_zero
    intro n hn'
    by_contra hne
    exact hn (full_block_active_label τ t S β C E hC hE hCE U R (rows C E U) Φ K _ hne)
  · rfl
  · rfl

theorem labelTerm_active (τ : Character) (t : ℝ) (S : Finset Id) (β : Id→ℂ)
    (rows : (C E : Id)→Finset (CommonIndex C E)→Finset O)
    (Φ : 𝓢(ℝ,ℂ)) (K R H : ℝ) (C E : Id) :
    labelTerm τ t S β rows Φ K R H C E=
      labelTerm τ t (activeSource S β) β rows Φ K R H C E := by
  unfold labelTerm
  split_ifs with hC hE
  · congr 1
    apply Finset.sum_congr rfl
    intro U hU
    apply Finset.sum_congr rfl
    intro n hn
    exact physicalBlock_active τ t S β C E hC hE U R (rows C E U) Φ K _
  · rfl
  · rfl

theorem active_commonLabels_subset (S : Finset Id) (β : Id→ℂ) :
    commonLabels (supportedColumns (activeSource S β)) (supportedColumns (activeSource S β))⊆
      commonLabels (supportedColumns S) (supportedColumns S) := by
  intro p hp
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨hI,hJ⟩ := Finset.mem_product.mp hv
  rw [supportedColumns_active] at hI hJ
  exact Finset.mem_image.mpr ⟨v,Finset.mem_product.mpr
    ⟨(Finset.mem_filter.mp hI).1,(Finset.mem_filter.mp hJ).1⟩,rfl⟩

theorem label_sum_active (τ : Character) (t : ℝ) (S : Finset Id) (β : Id→ℂ)
    (rows : (C E : Id)→Finset (CommonIndex C E)→Finset O)
    (Φ : 𝓢(ℝ,ℂ)) (K R H : ℝ) :
    (∑p∈commonLabels (supportedColumns S) (supportedColumns S),
      labelTerm τ t S β rows Φ K R H p.1 p.2)=
      ∑p∈commonLabels (supportedColumns (activeSource S β)) (supportedColumns (activeSource S β)),
        labelTerm τ t (activeSource S β) β rows Φ K R H p.1 p.2 := by
  have hs : (∑p∈commonLabels (supportedColumns (activeSource S β)) (supportedColumns (activeSource S β)),
      labelTerm τ t S β rows Φ K R H p.1 p.2)=
        ∑p∈commonLabels (supportedColumns S) (supportedColumns S),
          labelTerm τ t S β rows Φ K R H p.1 p.2 := by
    apply Finset.sum_subset (active_commonLabels_subset S β)
    intro p hp hn
    exact labelTerm_zero_off_active τ t S β rows Φ K R H p.1 p.2
      (commonLabels_data _ _ _ _ hp).2.2 hn
  rw [←hs]
  apply Finset.sum_congr rfl
  intro p hp
  exact labelTerm_active τ t S β rows Φ K R H p.1 p.2

def fixedRowEnergy (τ : Character) (t : ℝ) (S : Finset Id) (β : Id→ℂ)
    (rows : (C E : Id)→Finset (CommonIndex C E)→Finset O)
    (Φ : 𝓢(ℝ,ℂ)) (K R H : ℝ) : ℂ :=
  ∑p : FixedLabel S,(heightCoeff τ t p.val.1*star (heightCoeff τ t p.val.2))*
    ∑U : Finset (CommonIndex p.val.1 p.val.2),∑n : SourceBlocks p.val.1 p.val.2 U K R H,
      physicalBlock τ t S β p.val.1 p.val.2
        (commonLabels_supported S _ _ p.property).1 (commonLabels_supported S _ _ p.property).2 U R
        (rows p.val.1 p.val.2 U) Φ K (fun i=>(n i:ℤ))

def liveRowEnergy (τ : Character) (t : ℝ) (S : Finset Id) (β : Id→ℂ)
    (rows : (C E : Id)→Finset (CommonIndex C E)→Finset O)
    (Φ : 𝓢(ℝ,ℂ)) (K R H : ℝ) : ℂ :=
  ∑p∈liveLabels τ S β,(heightCoeff τ t p.val.1*star (heightCoeff τ t p.val.2))*
    ∑U : Finset (CommonIndex p.val.1 p.val.2),∑n : SourceBlocks p.val.1 p.val.2 U K R H,
      physicalBlock τ t (activeSource S β) β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U R
        (rows p.val.1 p.val.2 U) Φ K (fun i=>(n i:ℤ))

theorem fixedRowEnergy_eq_label_sum (τ : Character) (t : ℝ) (S : Finset Id) (β : Id→ℂ)
    (rows : (C E : Id)→Finset (CommonIndex C E)→Finset O)
    (Φ : 𝓢(ℝ,ℂ)) (K R H : ℝ) :
    fixedRowEnergy τ t S β rows Φ K R H=
      ∑p∈commonLabels (supportedColumns S) (supportedColumns S),
        labelTerm τ t S β rows Φ K R H p.1 p.2 := by
  rw [←Finset.sum_coe_sort]
  unfold fixedRowEnergy
  apply Finset.sum_congr rfl
  intro p hp
  rw [labelTerm,dif_pos (commonLabels_supported S _ _ p.property).1,
    dif_pos (commonLabels_supported S _ _ p.property).2]

theorem fixedRowEnergy_active_live (τ : Character) (t : ℝ) (S : Finset Id) (β : Id→ℂ)
    (rows : (C E : Id)→Finset (CommonIndex C E)→Finset O)
    (Φ : 𝓢(ℝ,ℂ)) (K R H : ℝ) :
    fixedRowEnergy τ t S β rows Φ K R H=liveRowEnergy τ t S β rows Φ K R H := by
  rw [fixedRowEnergy_eq_label_sum,label_sum_active,←fixedRowEnergy_eq_label_sum]
  unfold fixedRowEnergy liveRowEnergy
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro p hp hn
  rw [common_height_zero_of_not_live τ t S β p hn,zero_mul]

/-- Generic completion for every row-selector separately. No relation
between the chosen row selectors is needed; true and false are both valid. -/
theorem zero_completed_rows (τ : Character) (t : ℝ) (S : Finset Id) (β₀ β : Id→ℂ)
    (hβ : ∀I,β I≠0→β₀ I≠0)
    (rows : (C E : Id)→Finset (CommonIndex C E)→Finset O)
    (Φ : 𝓢(ℝ,ℂ)) (K R H : ℝ) :
    fixedRowEnergy τ t (activeSource S β₀) β rows Φ K R H=
      liveRowEnergy τ t S β rows Φ K R H := by
  have hfixed (S' : Finset Id) :
      fixedRowEnergy τ t S' β rows Φ K R H=
        fixedRowEnergy τ t (activeSource S' β) β rows Φ K R H := by
    rw [fixedRowEnergy_eq_label_sum,label_sum_active,←fixedRowEnergy_eq_label_sum]
  rw [hfixed (activeSource S β₀),nested_active S β₀ β hβ,←hfixed S]
  exact fixedRowEnergy_active_live τ t S β rows Φ K R H

/-- Separate equality of both actual components. This is stronger than
the equality of their sum and permits exact reuse of the exceptional bound. -/
theorem fixedPart_eq_outerPart (exceptional : Bool) (q : Data ι) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (seed : Id) (τ : Character) (ξ χ : RayCharacter)
    (Q : Id) (t : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K T Z ζ H : ℝ) :
    fixedPart exceptional q x y s seed τ ξ χ Q t Φ K T Z ζ H=
      outerPartEnergy exceptional q x y s seed τ ξ χ Q t Φ K T Z ζ H := by
  exact zero_completed_rows τ t (sourceColumns s) (commonColumn q x seed)
    (outerColumn q x y seed ξ) (outer_supported_by_common q x y seed ξ)
    (fun C E U=>outerRows exceptional q x y τ ξ χ Q C E U (frequencyRadius T Z ζ))
    Φ K (frequencyRadius T Z ζ) H

/-- The already proved exceptional estimate, transported by an exact
identity. All constants and uniform quantifiers are inherited unchanged. -/
theorem uniform_fixed_outer_exceptional_part (N : ℕ)
    (saving Bcap a b ε δ Bnorm Lrad Cr εsum : ℝ)
    (hs : (2/3:ℝ)≤saving) (hs4 : saving<4/5) (hBcap : 0≤Bcap)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hδ : 0<δ) (hgap : saving+2*δ<1)
    (hBnorm : 0≤Bnorm) (hLrad : 0≤Lrad) (hCr : 0<Cr) (hεsum : 0<εsum) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),(0,0)∈control ∧
      ∀Φ : 𝓢(ℝ,ℂ),∃Ckernel : ℝ,0≤Ckernel ∧
      ∀Q : Id,Q≠0→Q≠⊤→Q≤Ideal.span {(72:O)}→∃A Csum : ℝ,0<A ∧ 0<Csum ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(κ : Type u) [Fintype κ],∀q : Data κ,∀x : Frozen q,∀y : Selected q,
      Function.Injective y→∀s : Source (RestIndex q) a b,Matches q x s ha→
      ∀cover : OriginalEnclosure s,Fintype.card (RestIndex q)≤N→
      (s.Fhole.absNorm:ℝ)≤Z^Bcap→(∏i,2*s.P i)≤Z^Bcap→poolCap s≤Z^Bnorm→
      ∀(seed : Id)(τ : Character)(ξ χ : RayCharacter),Squarefree seed→seed≠0→
      selectedPositiveWeight q x y τ≠0→
      ∀(t K Tsec ζ Hsource : ℝ),0<K→0≤Tsec→
      poolCap s≤Hsource→Hsource≤Z^Bnorm→
      frequencyRadius Tsec Z ζ≤Cr*Z^Lrad→
      outerFamilyConductorBudget q x y s τ (frequencyRadius Tsec Z ζ)≤Z^Bcap→
      ‖fixedPart true q x y s seed τ ξ χ Q t Φ K Tsec Z ζ Hsource‖/sourceVolume s≤
        (Ckernel*A*heightBase t^(2*J)*(windowMoment J)^2)*
          outerSavedBudget q y s J control Q Z ε K*
            Z^(2*Bnorm*δ)*(Csum*Z^εsum/(seed.absNorm:ℝ)) := by
  simpa only [fixedPart_eq_outerPart] using
    uniform_actual_outer_exceptional_part N saving Bcap a b ε δ Bnorm Lrad Cr εsum
      hs hs4 hBcap ha hb hε hδ hgap hBnorm hLrad hCr hεsum

/-- Exact connection to OuterFreshRemainders.outer_second_zero.
The scalar is K, not 16 K, and there is no W denominator at original K. -/
theorem outerZero_eq_sourceSecondZero (q : Data ι) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (seed : Id) (τ : Character) (ξ : RayCharacter) (t K : ℝ) :
    outerZero q x y s seed τ ξ t K=(K:ℂ)*paperRadialFourier ballProfile 0*
      sourceSecondZero (sourceColumns s) (outerColumn q x y seed ξ) τ t := by
  unfold outerZero zeroDensity sourceSecondZero
  rw [show 16*(K/16)*(1:ℝ)^3=K by ring]

theorem outerZero_norm (q : Data ι) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (seed : Id) (τ : Character) (ξ : RayCharacter)
    (t K : ℝ) (hK : 0≤K) :
    ‖outerZero q x y s seed τ ξ t K‖=K*‖paperRadialFourier ballProfile 0‖*
      ‖sourceSecondZero (sourceColumns s) (outerColumn q x y seed ξ) τ t‖ := by
  rw [outerZero_eq_sourceSecondZero,norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg hK]

/-- Exact connection to the literal density estimated by
OuterFreshRemainders.outer_tail_arbitrary_saving, at Kargument=K/16,W=1. -/
theorem discarded_eq_outer_tail (q : Data ι) (x : Frozen q) (y : Selected q)
    (s : Source (RestIndex q) a b) (seed : Id) (τ : Character) (ξ : RayCharacter)
    (t K T Z ζ : ℝ) :
    secondDiscardedEnergy τ t (sourceColumns s) (outerColumn q x y seed ξ) ballProfile K T Z ζ=
      localizedDensity Finset.univ (sourceGenerator (sourceColumns s))
        (sourceGenerator_supported (sourceColumns s))
        (fun I : supportedColumns (sourceColumns s)=>outerColumn q x y seed ξ I*heightCoeff τ t I)
        (K/16) 1 (discardedWeight (frequencyRadius T Z ζ)) := by
  have he := MixedLocalizedDictionary.source_discarded τ t (sourceColumns s)
    (outerColumn q x y seed ξ) (K/16) 1 T Z ζ (by norm_num)
  rw [show 16*(K/16)*(1:ℝ)^4=K by ring,Complex.ofReal_one,div_one] at he
  exact he.symm

end
end Candidate.FourthPower.OuterFreshCompletion
