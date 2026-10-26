import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondRetainedContraction
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondRowFibres
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss Cycle63Moment
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondLiveBlock
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondLedger
open CenteredMomentFirstDiscardedEnergy CenteredMomentActive
open CenteredMomentSecondBlockAggregate CenteredMomentSecondPhysicalBlock
open CenteredMomentSectorLocalization CenteredMomentSecondDyadicPartition
open CenteredMomentDyadicCount CenteredMomentActiveSource CenteredMomentFirstSectors
open CenteredMomentSecondRetainedAggregate
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
    (hU : ActualSecondBlockIndex.IsInactive q) : FirstSourceLabel :=
  ⟨q.1.val.val,⟨q.2.1,hU⟩⟩

/-- Full supported arithmetic labels of the original live ideal pairs. -/
def actualSecondLabels {ι : Type*}[Fintype ι](s : Input ι)(R seed : Ideal O) :
    Finset FirstSourceLabel :=
  Finset.univ.image (fun q : (p : liveLabels s.η (finiteColumns (Fintype.piFinset s.pools))
    (coefficient s R seed))×↥(inactiveSubsets p.val.val.1 p.val.val.2)=>
      (⟨q.1.val.val,q.2⟩ : FirstSourceLabel))

lemma actual_second_supported_label_mem {ι : Type*}[Fintype ι](s : Input ι)
    (R seed : Ideal O)(K Tsec Z ξ : ℝ)
    (q : ActualSecondBlockIndex s R seed K Tsec Z ξ)
    (hU : ActualSecondBlockIndex.IsInactive q) :
    actualSecondSupportedLabel s R seed K Tsec Z ξ q hU∈actualSecondLabels s R seed := by
  exact Finset.mem_image.mpr ⟨⟨q.1,⟨q.2.1,hU⟩⟩,Finset.mem_univ _,rfl⟩

/-- Arithmetic gates of every full supported label follow from the actual
source coefficients, including both seed divisibilities. -/
theorem actual_second_labels_gates {ι : Type*}[Fintype ι](s : Input ι)
    (R seed : Ideal O)(hseed : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (l : FirstSourceLabel)(hl : l∈actualSecondLabels s R seed) :
    Supported l.1.1 ∧ Supported l.1.2 ∧ primeSupport l.1.1=primeSupport l.1.2 ∧
    seed∣l.1.1 ∧ seed∣l.1.2 ∧
    (l.1.1.absNorm:ℝ)≤ sourceRadius s ∧ (l.1.2.absNorm:ℝ)≤ sourceRadius s := by
  obtain ⟨q,_,rfl⟩:=Finset.mem_image.mp hl
  have hg:=actual_common_gates s R seed hseed hz₁ hz₂ _ _ q.1.val.property
  have hs:=commonLabels_supported (activeSource (finiteColumns (Fintype.piFinset s.pools))
    (coefficient s R seed)) _ _ q.1.val.property
  exact ⟨hs.1,hs.2,hg.2.2.1,hg.2.2.2.1,hg.2.2.2.2.1,hg.2.2.2.2.2⟩

/-- Exact positive-sum disintegration, retaining all four dyads. The cost
may contain the complete residual-projector and common-allocation sums. -/
theorem actual_second_positive_disintegration {ι : Type*}[Fintype ι](s : Input ι)
    (R seed : Ideal O)(K Tsec Z ξ : ℝ)
    (rows : Finset (ActualSecondBlockIndex s R seed K Tsec Z ξ))
    (hU : ∀q∈rows,ActualSecondBlockIndex.IsInactive q)
    (box : Finset (Fin 4→ℤ))
    (hbox : ∀q∈rows,actualSecondDyad s R seed K Tsec Z ξ q∈box)
    (cost : FirstSourceLabel→(Fin 4→ℤ)→ℝ)
    (hcost : ∀l∈actualSecondLabels s R seed,∀n∈box,0≤ cost l n) :
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

/-- A heterogeneous selected block subset reindexes into its full supported
second labels and the same absolute dyadic box. First source identities are
retained; no ordinary block norm or arithmetic label cardinality is paid. -/
theorem actual_second_joint_positive_disintegration {α Label : Type*}
    [Fintype α][DecidableEq α][Fintype Label]
    (slots : Label→Finset α)(s : (l : Label)→ Input (slots l))
    (R seed : Label→ Ideal O)(K Tsec : Label→ℝ)(Z ξ : ℝ)
    (rows : Finset ((l : Label)×ActualSecondBlockIndex (s l) (R l) (seed l)
      (K l) (Tsec l) Z ξ))
    (hU : ∀q∈rows,ActualSecondBlockIndex.IsInactive q.2)
    (box : Finset (Fin 4→ℤ))
    (hbox : ∀q∈rows,actualSecondDyad (s q.1) (R q.1) (seed q.1)
      (K q.1) (Tsec q.1) Z ξ q.2∈box)
    (cost : Label→FirstSourceLabel→(Fin 4→ℤ)→ℝ)
    (hcost : ∀l,∀v∈actualSecondLabels (s l) (R l) (seed l),∀n∈box,0≤ cost l v n) :
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

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
