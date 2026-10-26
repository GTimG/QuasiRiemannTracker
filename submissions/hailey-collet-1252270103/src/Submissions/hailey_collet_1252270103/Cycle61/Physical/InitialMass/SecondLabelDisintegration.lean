/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondRetainedContraction
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondRowFibres

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss Cycle61Moment
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondLiveBlock
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondLedger
open CenteredMomentFirstDiscardedEnergy CenteredMomentActive
open CenteredMomentSecondBlockAggregate CenteredMomentSecondPhysicalBlock
open CenteredMomentSectorLocalization CenteredMomentSecondDyadicPartition
open CenteredMomentDyadicCount CenteredMomentActiveSource CenteredMomentFirstSectors
open CenteredMomentSecondRetainedAggregate
local notation "O" => HeckeFamily.O
local instance secondLabelSumDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- The exact raw arithmetic label, before vanishing partitions are removed. -/
abbrev SecondArithmeticLabel := (CD : Ideal O×Ideal O)×Finset (CommonIndex CD.1 CD.2)

def actualSecondArithmeticLabel {ι : Type*}[Fintype ι](s : Input ι)
    (R seed : Ideal O)(K Tsec Z ξ : ℝ)
    (q : ActualSecondBlockIndex s R seed K Tsec Z ξ) : SecondArithmeticLabel :=
  ⟨q.1.val.val,q.2.1⟩

def actualSecondDyad {ι : Type*}[Fintype ι](s : Input ι)
    (R seed : Ideal O)(K Tsec Z ξ : ℝ)
    (q : ActualSecondBlockIndex s R seed K Tsec Z ξ) : Fin 4→ℤ := fun i=>(q.2.2 i:ℤ)

/-- All four dyads, together with the literal ideal pair and partition,
recover the actual retained block index without further multiplicity. -/
theorem actual_second_label_dyad_injective {ι : Type*}[Fintype ι](s : Input ι)
    (R seed : Ideal O)(K Tsec Z ξ : ℝ) :
    Function.Injective (fun q : ActualSecondBlockIndex s R seed K Tsec Z ξ=>
      (actualSecondArithmeticLabel s R seed K Tsec Z ξ q,actualSecondDyad s R seed K Tsec Z ξ q)) := by
  intro q v h
  apply actual_second_block_code_injective s R seed K Tsec Z ξ
  exact congrArg (fun x : SecondArithmeticLabel×(Fin 4→ℤ)=>
    (⟨x.1.1,x.1.2,x.2⟩ : SecondBlockCode)) h

/-- A literal canonical unit partition belongs to the genuine principal
inactive subset family used by the arithmetic scalar payments. -/
lemma canonical_partition_inactive (C D : Ideal O)(U : Finset (CommonIndex C D))(z : O)
    (h : canonicalPartition C D U z) : U∈inactiveSubsets C D := by
  rw [inactiveSubsets,Finset.mem_powerset]
  intro i hi
  rw [←h] at hi
  have he := (Finset.mem_filter.mp hi).2.1
  apply Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
  dsimp only [netExponent]
  omega

/-- Nonzero original physical blocks have valid arithmetic partitions.
This uses the original physical sum, independently of any ordinary filter. -/
theorem second_block_nonzero_inactive (d : SecondBlockSource)(W : 𝓢(ℝ,ℂ))
    (hn : d.value W≠0) : d.inactive∈inactiveSubsets d.C d.D := by
  by_contra hU
  apply hn
  unfold SecondBlockSource.value physicalBlock
  apply Finset.sum_eq_zero
  intro z hz
  simp only [show ¬canonicalPartition d.C d.D d.inactive _ from
    fun h=>hU (canonical_partition_inactive d.C d.D d.inactive _ h),ite_false]

def actualSecondSupportedLabel {ι : Type*}[Fintype ι](s : Input ι)
    (R seed : Ideal O)(K Tsec Z ξ : ℝ)
    (q : ActualSecondBlockIndex s R seed K Tsec Z ξ)
    (hU : q.2.1∈inactiveSubsets q.1.val.val.1 q.1.val.val.2) : FirstSourceLabel :=
  ⟨q.1.val.val,⟨q.2.1,hU⟩⟩

/-- An original-nonzero selected block subset has genuine supported labels.
The nonzero evidence refers to the unrestricted datum. -/
theorem actual_second_original_nonzero_supported {α : Type*}[Fintype α][DecidableEq α]
    (slots : Finset α)(s : Input slots)(R seed : Ideal O)(hseed : Squarefree seed)
    (hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)(K Tsec Z ξ : ℝ)(hK : 0<K)
    (W : 𝓢(ℝ,ℂ))(rows : Finset (ActualSecondBlockIndex s R seed K Tsec Z ξ))
    (hn : ∀q∈rows,(actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK q).block.value W≠0) :
    ∀q∈rows,q.2.1∈inactiveSubsets q.1.val.val.1 q.1.val.val.2 := by
  intro q hq
  have hh := second_block_nonzero_inactive
    (actualSecondBlockDatum slots s R seed hseed hz₁ hz₂ K Tsec Z ξ hK q).block W (hn q hq)
  simpa only [actualSecondBlockDatum,actualSecondInputDatum,SecondInputDatum.block,originalSecondBlock] using hh

/-- Full supported arithmetic labels of the original live ideal pairs. -/
def actualSecondLabels {ι : Type*}[Fintype ι](s : Input ι)(R seed : Ideal O) :
    Finset FirstSourceLabel :=
  Finset.univ.image (fun q : (p : liveLabels s.η (finiteColumns (Fintype.piFinset s.pools))
    (coefficient s R seed))×↥(inactiveSubsets p.val.val.1 p.val.val.2)=>
      (⟨q.1.val.val,q.2⟩ : FirstSourceLabel))

lemma actual_second_supported_label_mem {ι : Type*}[Fintype ι](s : Input ι)
    (R seed : Ideal O)(K Tsec Z ξ : ℝ)
    (q : ActualSecondBlockIndex s R seed K Tsec Z ξ)
    (hU : q.2.1∈inactiveSubsets q.1.val.val.1 q.1.val.val.2) :
    actualSecondSupportedLabel s R seed K Tsec Z ξ q hU∈actualSecondLabels s R seed := by
  exact Finset.mem_image.mpr ⟨⟨q.1,⟨q.2.1,hU⟩⟩,Finset.mem_univ _,rfl⟩

/-- Arithmetic gates of every full supported label follow from the actual
source coefficients, including both seed divisibilities. -/
theorem actual_second_labels_gates {ι : Type*}[Fintype ι](s : Input ι)
    (R seed : Ideal O)(hseed : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (l : FirstSourceLabel)(hl : l∈actualSecondLabels s R seed) :
    Supported l.1.1 ∧ Supported l.1.2 ∧ primeSupport l.1.1=primeSupport l.1.2 ∧
    seed∣l.1.1 ∧ seed∣l.1.2 ∧
    (l.1.1.absNorm:ℝ)≤sourceRadius s ∧ (l.1.2.absNorm:ℝ)≤sourceRadius s := by
  obtain ⟨q,_,rfl⟩:=Finset.mem_image.mp hl
  have hg:=actual_common_gates s R seed hseed hz₁ hz₂ _ _ q.1.val.property
  have hs:=commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
    (coefficient s R seed)) _ _ q.1.val.property
  exact ⟨hs.1,hs.2,hg.2.2.1,hg.2.2.2.1,hg.2.2.2.2.1,hg.2.2.2.2.2⟩

/-- Exact subset image identity before enlargement to the full arithmetic
label set. Original block filters and ratio-fiber filters remain in `rows`. -/
theorem actual_second_label_dyad_image_sum {ι : Type*}[Fintype ι](s : Input ι)
    (R seed : Ideal O)(K Tsec Z ξ : ℝ)
    (rows : Finset (ActualSecondBlockIndex s R seed K Tsec Z ξ))
    (hU : ∀q∈rows,q.2.1∈inactiveSubsets q.1.val.val.1 q.1.val.val.2)
    (cost : FirstSourceLabel→(Fin 4→ℤ)→ℝ) :
    let code:=fun q : rows=>(actualSecondSupportedLabel s R seed K Tsec Z ξ q.val
      (hU q.val q.property),actualSecondDyad s R seed K Tsec Z ξ q.val);
    (∑q : rows,cost (code q).1 (code q).2)=∑x∈Finset.univ.image code,cost x.1 x.2 := by
  dsimp only
  rw [Finset.sum_image]
  intro q _ v _ h
  apply Subtype.ext
  apply actual_second_label_dyad_injective s R seed K Tsec Z ξ
  exact congrArg (fun x : FirstSourceLabel×(Fin 4→ℤ)=>
    ((⟨x.1.1,x.1.2.val⟩ : SecondArithmeticLabel),x.2)) h

/-- Exact positive-sum disintegration, retaining all four dyads. The cost
may contain the complete residual-projector and common-allocation sums. -/
theorem actual_second_positive_disintegration {ι : Type*}[Fintype ι](s : Input ι)
    (R seed : Ideal O)(K Tsec Z ξ : ℝ)
    (rows : Finset (ActualSecondBlockIndex s R seed K Tsec Z ξ))
    (hU : ∀q∈rows,q.2.1∈inactiveSubsets q.1.val.val.1 q.1.val.val.2)
    (box : Finset (Fin 4→ℤ))
    (hbox : ∀q∈rows,actualSecondDyad s R seed K Tsec Z ξ q∈box)
    (cost : FirstSourceLabel→(Fin 4→ℤ)→ℝ)
    (hcost : ∀l∈actualSecondLabels s R seed,∀n∈box,0≤cost l n) :
    (∑q : rows,cost (actualSecondSupportedLabel s R seed K Tsec Z ξ q.val (hU q.val q.property))
      (actualSecondDyad s R seed K Tsec Z ξ q.val))≤
      ∑n∈box,∑l∈actualSecondLabels s R seed,cost l n := by
  let code := fun q : rows=>(actualSecondSupportedLabel s R seed K Tsec Z ξ q.val
    (hU q.val q.property),actualSecondDyad s R seed K Tsec Z ξ q.val)
  have hinj : Function.Injective code := by
    intro q v h
    apply Subtype.ext
    apply actual_second_label_dyad_injective s R seed K Tsec Z ξ
    exact congrArg (fun x : FirstSourceLabel×(Fin 4→ℤ)=>
      ((⟨x.1.1,x.1.2.val⟩ : SecondArithmeticLabel),x.2)) h
  have hsub : Finset.univ.image code⊆actualSecondLabels s R seed×ˢbox := by
    intro x hx
    obtain ⟨q,_,rfl⟩:=Finset.mem_image.mp hx
    exact Finset.mem_product.mpr ⟨actual_second_supported_label_mem s R seed K Tsec Z ξ
      q.val (hU q.val q.property),hbox q.val q.property⟩
  calc
    _=∑x∈Finset.univ.image code,cost x.1 x.2 := by
      rw [Finset.sum_image (fun _ _ _ _ h=>hinj h)]
    _≤∑x∈actualSecondLabels s R seed×ˢbox,cost x.1 x.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro x hx _
      exact hcost x.1 (Finset.mem_product.mp hx).1 x.2 (Finset.mem_product.mp hx).2
    _=_ := by rw [Finset.sum_product,Finset.sum_comm]

/-- The finite common absolute box retains every coordinate. -/
def secondAbsoluteBox (Z A D B L Cr : ℝ) : Finset (Fin 4→ℤ) :=
  Fintype.piFinset (fun i=>indices (![Z^(-(D+2*B)),1,1,1] i)
    (![Z^(A+2*B),max 1 (4*Cr)*Z^L,Z^B,Z^B] i))

lemma second_absolute_box_card (Z A D B L Cr : ℝ) :
    (secondAbsoluteBox Z A D B L Cr).card=Fintype.card (SecondAbsoluteEnvelope Z A D B L Cr) := by
  simp only [secondAbsoluteBox,Fintype.card_piFinset,SecondAbsoluteEnvelope,Fintype.card_pi,
    Fintype.card_coe]

/-- A subset of actual supported blocks pays the complete four-coordinate
box once. This applies verbatim to nonzero-block and exact ratio subsets. -/
theorem actual_second_positive_subpower {α : Type*}[Fintype α][DecidableEq α]
    (A D₀ B L Cr ε : ℝ)(hA : 0≤A)(hD₀ : 0≤D₀)(hB : 0≤B)(hL : 0≤L)
    (hCr : 0<Cr)(hε : 0<ε) :
    ∃C₀ : ℝ,0<C₀ ∧ ∀ᶠZ : ℝ in atTop,1≤Z ∧
    ∀(slots : Finset α)(s : Input slots)(R seed : Ideal O)(_hseed : Squarefree seed)
      (_hz₁ : s.W₁ 0=0)(_hz₂ : s.W₂ 0=0)(K Tsec ξ : ℝ)(_hK : 0<K),
      Z^(-D₀)≤K → K≤Z^A → frequencyRadius Tsec Z ξ≤Cr*Z^L → sourceRadius s≤Z^B →
    ∀(rows : Finset (ActualSecondBlockIndex s R seed K Tsec Z ξ))
      (hU : ∀q∈rows,q.2.1∈inactiveSubsets q.1.val.val.1 q.1.val.val.2)
      (cost : FirstSourceLabel→ℝ),
      (∀l∈actualSecondLabels s R seed,0≤cost l) →
      (∑q : rows,cost (actualSecondSupportedLabel s R seed K Tsec Z ξ q.val (hU q.val q.property)))≤
        C₀*Z^ε*(∑l∈actualSecondLabels s R seed,cost l) := by
  obtain ⟨C₀,hC₀,hcount⟩:=second_absolute_envelope_subpower A D₀ B L Cr ε hA hD₀ hB hL hCr hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hcount,eventually_ge_atTop (1:ℝ)] with Z hcount hZ
  refine ⟨hZ,?_⟩
  intro slots s R seed _hseed _hz₁ _hz₂ K Tsec ξ _hK hKlo hKhi hR hsource rows hU cost hcost
  let box:=secondAbsoluteBox Z A D₀ B L Cr
  have hbox (q : ActualSecondBlockIndex s R seed K Tsec Z ξ) :
      actualSecondDyad s R seed K Tsec Z ξ q∈box := by
    have hg:=actual_common_gates s R seed _hseed _hz₁ _hz₂ _ _ q.1.val.property
    have hs:=commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s R seed)) _ _ q.1.val.property
    apply Fintype.mem_piFinset.mpr
    intro i
    exact actual_second_dyads_absolute Z A D₀ B L Cr hZ hA hD₀ hB hL hCr
      _ _ hs.1 hs.2 hg.2.2.1 q.2.1 K (frequencyRadius Tsec Z ξ) (sourceRadius s)
      _hK hKlo hKhi hR hsource (hg.2.2.2.2.2.1.trans hsource)
      (hg.2.2.2.2.2.2.trans hsource) q.2.2 i
  have hh:=actual_second_positive_disintegration s R seed K Tsec Z ξ rows hU box
    (fun q _=>hbox q) (fun l _=>cost l) (fun l hl _ _=>hcost l hl)
  have hnonneg : 0≤∑l∈actualSecondLabels s R seed,cost l := Finset.sum_nonneg hcost
  have hcard : (box.card:ℝ)≤C₀*Z^ε := by
    rw [show box.card=Fintype.card (SecondAbsoluteEnvelope Z A D₀ B L Cr) from
      second_absolute_box_card Z A D₀ B L Cr]
    exact hcount
  have heq : (∑_n∈box,∑l∈actualSecondLabels s R seed,cost l)=
      (box.card:ℝ)*(∑l∈actualSecondLabels s R seed,cost l) := by simp
  rw [heq] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hcard hnonneg)

/-- Heterogeneous source identities and projector keys remain injective
when the exact second arithmetic label and all four dyads are retained. -/
theorem actual_second_joint_label_dyad_injective {α Label : Type*}
    [Fintype α][DecidableEq α]
    (slots : Label→Finset α)(s : (l : Label)→Input (slots l))
    (R seed : Label→Ideal O)(K Tsec : Label→ℝ)(Z ξ : ℝ)
    (first : Label→FirstSourceLabel)
    (hfirst : Function.Injective (fun l=>(first l,seed l))) :
    Function.Injective (fun q : (l : Label)×ActualSecondBlockIndex (s l) (R l) (seed l)
      (K l) (Tsec l) Z ξ=>
      (first q.1,seed q.1,actualSecondArithmeticLabel (s q.1) (R q.1) (seed q.1)
        (K q.1) (Tsec q.1) Z ξ q.2,
        actualSecondDyad (s q.1) (R q.1) (seed q.1) (K q.1) (Tsec q.1) Z ξ q.2)) := by
  intro q v h
  apply actual_second_joint_block_code_injective slots s R seed K Tsec Z ξ first hfirst
  exact congrArg (fun x : FirstSourceLabel×Ideal O×SecondArithmeticLabel×(Fin 4→ℤ)=>
    (x.1,x.2.1,(⟨x.2.2.1.1,x.2.2.1.2,x.2.2.2⟩ : SecondBlockCode))) h

/-- A heterogeneous selected block subset reindexes into its full supported
second labels and the same absolute dyadic box. First source identities are
retained; no ordinary block norm or arithmetic label cardinality is paid. -/
theorem actual_second_joint_positive_disintegration {α Label : Type*}
    [Fintype α][DecidableEq α][Fintype Label]
    (slots : Label→Finset α)(s : (l : Label)→Input (slots l))
    (R seed : Label→Ideal O)(K Tsec : Label→ℝ)(Z ξ : ℝ)
    (rows : Finset ((l : Label)×ActualSecondBlockIndex (s l) (R l) (seed l)
      (K l) (Tsec l) Z ξ))
    (hU : ∀q∈rows,q.2.2.1∈inactiveSubsets q.2.1.val.val.1 q.2.1.val.val.2)
    (box : Finset (Fin 4→ℤ))
    (hbox : ∀q∈rows,actualSecondDyad (s q.1) (R q.1) (seed q.1)
      (K q.1) (Tsec q.1) Z ξ q.2∈box)
    (cost : Label→FirstSourceLabel→(Fin 4→ℤ)→ℝ)
    (hcost : ∀l,∀v∈actualSecondLabels (s l) (R l) (seed l),∀n∈box,0≤cost l v n) :
    (∑q : rows,cost q.val.1
      (actualSecondSupportedLabel (s q.val.1) (R q.val.1) (seed q.val.1)
        (K q.val.1) (Tsec q.val.1) Z ξ q.val.2 (hU q.val q.property))
      (actualSecondDyad (s q.val.1) (R q.val.1) (seed q.val.1)
        (K q.val.1) (Tsec q.val.1) Z ξ q.val.2))≤
      ∑n∈box,∑l,∑v∈actualSecondLabels (s l) (R l) (seed l),cost l v n := by
  let code := fun q : rows=>
    ((⟨q.val.1,actualSecondSupportedLabel (s q.val.1) (R q.val.1) (seed q.val.1)
      (K q.val.1) (Tsec q.val.1) Z ξ q.val.2 (hU q.val q.property)⟩ :
      (l : Label)×FirstSourceLabel),
      actualSecondDyad (s q.val.1) (R q.val.1) (seed q.val.1)
        (K q.val.1) (Tsec q.val.1) Z ξ q.val.2)
  have hinj : Function.Injective code := by
    rintro ⟨⟨l,q⟩,hq⟩ ⟨⟨m,v⟩,hv⟩ h
    have hl : l=m := congrArg (fun x=>x.1.1) h
    cases hl
    have hqv : q=v := actual_second_label_dyad_injective (s l) (R l) (seed l) (K l) (Tsec l) Z ξ
      (congrArg (fun x : ((l : Label)×FirstSourceLabel)×(Fin 4→ℤ)=>
        ((⟨x.1.2.1,x.1.2.2.val⟩ : SecondArithmeticLabel),x.2)) h)
    cases hqv
    rfl
  let labels := Finset.univ.sigma (fun l=>actualSecondLabels (s l) (R l) (seed l))
  have hsub : Finset.univ.image code⊆labels×ˢbox := by
    intro x hx
    obtain ⟨q,_,rfl⟩:=Finset.mem_image.mp hx
    exact Finset.mem_product.mpr ⟨Finset.mem_sigma.mpr ⟨Finset.mem_univ _,
      actual_second_supported_label_mem _ _ _ _ _ _ _ q.val.2 (hU q.val q.property)⟩,
      hbox q.val q.property⟩
  calc
    _=∑x∈Finset.univ.image code,cost x.1.1 x.1.2 x.2 := by
      rw [Finset.sum_image (fun _ _ _ _ h=>hinj h)]
    _≤∑x∈labels×ˢbox,cost x.1.1 x.1.2 x.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro x hx _
      obtain ⟨hl,hn⟩:=Finset.mem_product.mp hx
      exact hcost x.1.1 x.1.2 (Finset.mem_sigma.mp hl).2 x.2 hn
    _=_ := by
      rw [Finset.sum_product,Finset.sum_comm]
      simp only [labels,Finset.sum_sigma]

/-- The heterogeneous selected scalar family pays only the common absolute
four-dyad cardinality. The remaining sum is exactly the finite supported
arithmetic-label payment, including its first projector identity. -/
theorem actual_second_joint_positive_subpower {α : Type*}[Fintype α][DecidableEq α]
    (A D₀ B L Cr ε : ℝ)(hA : 0≤A)(hD₀ : 0≤D₀)(hB : 0≤B)(hL : 0≤L)
    (hCr : 0<Cr)(hε : 0<ε) :
    ∃C₀ : ℝ,0<C₀ ∧ ∀ᶠZ : ℝ in atTop,1≤Z ∧
    ∀{Label : Type*}[Fintype Label]
      (slots : Label→Finset α)(s : (l : Label)→Input (slots l))
      (R seed : Label→Ideal O)(_hseed : ∀l,Squarefree (seed l))
      (_hz₁ : ∀l,(s l).W₁ 0=0)(_hz₂ : ∀l,(s l).W₂ 0=0)
      (K Tsec : Label→ℝ)(ξ : ℝ)(_hK : ∀l,0<K l),
      (∀l,Z^(-D₀)≤K l) → (∀l,K l≤Z^A) →
      (∀l,frequencyRadius (Tsec l) Z ξ≤Cr*Z^L) → (∀l,sourceRadius (s l)≤Z^B) →
    ∀(rows : Finset ((l : Label)×ActualSecondBlockIndex (s l) (R l) (seed l)
      (K l) (Tsec l) Z ξ))
      (hU : ∀q∈rows,q.2.2.1∈inactiveSubsets q.2.1.val.val.1 q.2.1.val.val.2)
      (cost : Label→FirstSourceLabel→ℝ),
      (∀l,∀v∈actualSecondLabels (s l) (R l) (seed l),0≤cost l v) →
      (∑q : rows,cost q.val.1
        (actualSecondSupportedLabel (s q.val.1) (R q.val.1) (seed q.val.1)
          (K q.val.1) (Tsec q.val.1) Z ξ q.val.2 (hU q.val q.property)))≤
        C₀*Z^ε*(∑l,∑v∈actualSecondLabels (s l) (R l) (seed l),cost l v) := by
  obtain ⟨C₀,hC₀,hcount⟩:=second_absolute_envelope_subpower A D₀ B L Cr ε hA hD₀ hB hL hCr hε
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hcount,eventually_ge_atTop (1:ℝ)] with Z hcount hZ
  refine ⟨hZ,?_⟩
  intro Label _ slots s R seed _hseed _hz₁ _hz₂ K Tsec ξ _hK hKlo hKhi hR hsource rows hU cost hcost
  let box:=secondAbsoluteBox Z A D₀ B L Cr
  have hbox (q : (l : Label)×ActualSecondBlockIndex (s l) (R l) (seed l)
      (K l) (Tsec l) Z ξ) :
      actualSecondDyad (s q.1) (R q.1) (seed q.1) (K q.1) (Tsec q.1) Z ξ q.2∈box := by
    have hg:=actual_common_gates (s q.1) (R q.1) (seed q.1) (_hseed q.1) (_hz₁ q.1) (_hz₂ q.1)
      _ _ q.2.1.val.property
    have hs:=commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset (s q.1).pools))
      (coefficient (s q.1) (R q.1) (seed q.1))) _ _ q.2.1.val.property
    apply Fintype.mem_piFinset.mpr
    intro i
    exact actual_second_dyads_absolute Z A D₀ B L Cr hZ hA hD₀ hB hL hCr
      _ _ hs.1 hs.2 hg.2.2.1 q.2.2.1 (K q.1) (frequencyRadius (Tsec q.1) Z ξ) (sourceRadius (s q.1))
      (_hK q.1) (hKlo q.1) (hKhi q.1) (hR q.1) (hsource q.1)
      (hg.2.2.2.2.2.1.trans (hsource q.1)) (hg.2.2.2.2.2.2.trans (hsource q.1)) q.2.2.2 i
  have hh:=actual_second_joint_positive_disintegration slots s R seed K Tsec Z ξ rows hU box
    (fun q _=>hbox q) (fun l v _=>cost l v) (fun l v hv _ _=>hcost l v hv)
  have hn : 0≤∑l,∑v∈actualSecondLabels (s l) (R l) (seed l),cost l v := by
    apply Finset.sum_nonneg
    intro l _
    exact Finset.sum_nonneg (hcost l)
  have hcard : (box.card:ℝ)≤C₀*Z^ε := by
    rw [show box.card=Fintype.card (SecondAbsoluteEnvelope Z A D₀ B L Cr) from
      second_absolute_box_card Z A D₀ B L Cr]
    exact hcount
  have heq : (∑_n∈box,∑l,∑v∈actualSecondLabels (s l) (R l) (seed l),cost l v)=
      (box.card:ℝ)*(∑l,∑v∈actualSecondLabels (s l) (R l) (seed l),cost l v) := by simp
  rw [heq] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hcard hn)

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_label_dyad_injective
#print axioms OAI.SevenEighths.Cycle61InitialMass.second_block_nonzero_inactive
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_positive_disintegration

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_positive_subpower

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_labels_gates
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_joint_label_dyad_injective
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_joint_positive_disintegration

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_original_nonzero_supported

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_joint_positive_subpower

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_label_dyad_image_sum
