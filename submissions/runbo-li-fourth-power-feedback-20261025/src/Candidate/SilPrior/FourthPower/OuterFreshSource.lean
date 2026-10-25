/- Copyright (c) 2026 Sil. Apache-2.0.
Concrete supplier Data and its canonical remaining Source, constructed
from the actual original Source data. No arbitrary-Data existence claim.

-/
import Candidate.SilPrior.FourthPower.OuterFreshWindowPair

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.OuterFreshSource
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentAddedZeroUniform CenteredMomentFirstSectors CenteredMomentSourceRectangle
open CenteredMomentSourceMass CenteredMomentLattice CenteredMomentHeckeColumnWindow
open CenteredMomentSourceRow CenteredMomentGaussEnergy CenteredMomentSecondHeightFamily
open MixedCommonRestriction MixedLiteralAllocation MixedPrincipalPair MixedPrincipalAllocations
open MixedSupplierFourthRow MixedSupplierSource MixedPrincipalWindow OuterFreshWindowPair
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}
local instance {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

/-- The literal supplier input from an actual original source. L is
the live/supplier split and J is its selected subset. Original ordinary
prefixes, all four lengths, profiles, character zeros and puncture survive. -/
def supplierData (s : Source ι a b) (ha : 0<a) (u : Id) (L : Finset ι)
    (J : Finset {i // i∉Lᶜ}) : Data ι where
  pool := s.pool
  prime := s.hp
  A := residualPool s.d.1 s.hd.1 (plainSupportPool b s.X₁ s.Y₁)
  B := residualPool s.d.2 s.hd.2 (plainSupportPool b s.X₂ s.Y₂)
  H := punctureProduct s.S s.H
  R := s.R
  u := u
  ν := s.ν
  Wslot := s.Wslot
  P := s.P
  W₁ := normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁
  W₂ := normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂
  X₁ := s.X₁
  X₂ := s.X₂
  Y₁ := s.Y₁
  Y₂ := s.Y₂
  d := s.d
  L := L
  J := J

/-- These data occur in the exact complete supplier expansion of the
original Source column, with the original mask u and every original
frequency. This pins the constructor to the actual analytic input. -/
theorem source_supplier_expansion (s : Source ι a b) (ha : 0<a) (u : Id)
    (J : (L : Finset ι)→Finset {i // i∉Lᶜ})
    (τ : Character) (t : ℝ) (k : O) :
    gaussPolynomial Finset.univ (sourceGenerator (sourceColumns s))
      (sourceGenerator_supported (sourceColumns s))
      (fun I : supportedColumns (sourceColumns s)=>sourceCoefficient s ha u I*
        heightCoeff τ t I) k =
      ∑L : Finset ι,∑x : Frozen (supplierData s ha u L (J L)),
        if Function.Injective x then
          frozenWeight (supplierData s ha u L (J L)) x*
            originalFamily (supplierData s ha u L (J L)) x τ t k else 0 := by
  exact MixedSupplierReconstruction.original_gauss_supplier_expansion u J
    s.S s.H s.pool s.d s.hd s.R u s.ν s.Wslot s.P
    (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
    (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
    b s.X₁ s.X₂ s.Y₁ s.Y₂ τ t k

/-- The remaining canonical source is built explicitly. Its neutral
allocation B=1,G=1 is just the base record for subsequent actual common
allocations; no original prefix is divided out or replaced. -/
def residualSource (s : Source ι a b) (ha : 0<a) (cover : OriginalEnclosure s)
    (u : Id) (L : Finset ι) (J : Finset {i // i∉Lᶜ})
    (x : Frozen (supplierData s ha u L J)) :
    Source (RestIndex (supplierData s ha u L J)) a b where
  S := s.S
  H := s.H
  pool := fun j=>s.pool j.val.val
  d := s.d
  hd := s.hd
  B := fun _=>1
  hB := fun _=>one_ne_zero
  G := 1
  R := s.R*frozenProduct (supplierData s ha u L J) x
  Fhole := s.Fhole
  hprod := by simp only [finiteTupleProduct,Finset.prod_const_one]
  hR := mul_ne_zero s.hR (frozen_nonzero (supplierData s ha u L J) x)
  hFhole := s.hFhole
  ν := fun j=>avoid u s.ν j.val.val
  Wslot := fun j=>s.Wslot j.val.val
  P := fun j=>s.P j.val.val
  M := fun j=>s.M j.val.val
  W₁ := s.W₁
  W₂ := s.W₂
  hs₁ := s.hs₁
  hs₂ := s.hs₂
  t₁ := s.t₁
  t₂ := s.t₂
  X₁ := s.X₁
  X₂ := s.X₂
  Y₁ := s.Y₁
  Y₂ := s.Y₂
  U₁ := s.U₁
  U₂ := s.U₂
  T := s.T
  L := s.L
  hL := s.hL
  hX₁ := s.hX₁
  hX₂ := s.hX₂
  hY₁ := s.hY₁
  hY₂ := s.hY₂
  hXU₁ := s.hXU₁
  hXU₂ := s.hXU₂
  hYU₁ := s.hYU₁
  hYU₂ := s.hYU₂
  hpX := s.hpX
  hpY := s.hpY
  hP := fun j=>s.hP j.val.val
  hM := fun j=>s.hM j.val.val
  hpool := fun j=>s.hpool j.val.val
  hp := fun j=>s.hp j.val.val
  hpn := fun j=>s.hpn j.val.val
  hν := by
    intro j I
    unfold avoid
    split_ifs
    · simp
    · exact s.hν j.val.val I
  hWnorm := fun j=>s.hWnorm j.val.val
  hW := fun j=>s.hW j.val.val
  hS := s.hS
  hH := s.hH
  henclose := by
    intro I hI hlen
    apply cover I hI
    simpa only [mul_one] using hlen

theorem residual_matches (s : Source ι a b) (ha : 0<a) (cover : OriginalEnclosure s)
    (u : Id) (L : Finset ι) (J : Finset {i // i∉Lᶜ})
    (x : Frozen (supplierData s ha u L J)) :
    Matches (supplierData s ha u L J) x (residualSource s ha cover u L J x) ha := by
  constructor <;> rfl

theorem residual_enclosure (s : Source ι a b) (ha : 0<a) (cover : OriginalEnclosure s)
    (u : Id) (L : Finset ι) (J : Finset {i // i∉Lᶜ})
    (x : Frozen (supplierData s ha u L J)) :
    OriginalEnclosure (residualSource s ha cover u L J x) := cover

/-- Both nested selections are genuine subsets of the original slots. -/
theorem rest_injective (q : Data ι) :
    Function.Injective (fun j : RestIndex q=>j.val.val) := by
  intro j k h
  exact Subtype.ext (Subtype.ext h)

theorem rest_card_le (q : Data ι) : Fintype.card (RestIndex q)≤Fintype.card ι :=
  Fintype.card_le_of_injective _ (rest_injective q)

theorem injected_prod_le {κ : Type*} [Fintype κ] (inc : κ→ι)
    (hinj : Function.Injective inc) (f : ι→ℝ) (hf : ∀i,1≤f i) :
    (∏j : κ,f (inc j))≤∏i,f i := by
  have he : (∏i∈(Finset.univ : Finset κ).image inc,f i)=
      ∏j : κ,f (inc j) := by
    rw [Finset.prod_image (fun j _ k _ h=>hinj h)]
  rw [←he]
  exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
    (fun i _=>zero_le_one.trans (hf i)) (fun i _ _=>hf i)

theorem rest_prod_le (q : Data ι) (f : ι→ℝ) (hf : ∀i,1≤f i) :
    (∏j : RestIndex q,f j.val.val)≤∏i,f i :=
  injected_prod_le _ (rest_injective q) f hf

/-- Nonzero ACTUAL supplier weights force membership in the original
slot pools. Membership is not inferred merely from the larger alphabet. -/
theorem frozen_slot_mem (s : Source ι a b) (ha : 0<a)
    (u : Id) (L : Finset ι) (J : Finset {i // i∉Lᶜ})
    (x : Frozen (supplierData s ha u L J))
    (hw : frozenWeight (supplierData s ha u L J) x≠0) (i : ↥Lᶜ) :
    (x i).val∈s.pool i.val := by
  have hi : amplitude (supplierData s ha u L J) i.val (x i)≠0 :=
    Finset.prod_ne_zero_iff.mp hw i (Finset.mem_univ i)
  by_contra hn
  have hnq : (x i).val∉(supplierData s ha u L J).pool i.val := hn
  exact hi (by simp only [amplitude,MixedSupplierSplit.slotAmplitude,if_neg hnq])

theorem selected_slot_mem (s : Source ι a b) (ha : 0<a)
    (u : Id) (L : Finset ι) (J : Finset {i // i∉Lᶜ})
    (y : Selected (supplierData s ha u L J))
    (hw : selectedWeight (supplierData s ha u L J) y≠0) (j : J) :
    (y j).val∈s.pool j.val.val := by
  have hj : amplitude (supplierData s ha u L J) j.val.val (y j)≠0 :=
    Finset.prod_ne_zero_iff.mp hw j (Finset.mem_univ j)
  by_contra hn
  have hnq : (y j).val∉(supplierData s ha u L J).pool j.val.val := hn
  exact hj (by simp only [amplitude,MixedSupplierSplit.slotAmplitude,if_neg hnq])

/-- These are polynomial admissibility bounds only. They do not replace
the sharper linear fixed-f cubic conductor in the nonexceptional family. -/
theorem frozen_norm_le (s : Source ι a b) (ha : 0<a)
    (u : Id) (L : Finset ι) (J : Finset {i // i∉Lᶜ})
    (x : Frozen (supplierData s ha u L J))
    (hw : frozenWeight (supplierData s ha u L J) x≠0) :
    ((frozenProduct (supplierData s ha u L J) x).absNorm:ℝ)≤∏i,2*s.P i := by
  calc
    ((frozenProduct (supplierData s ha u L J) x).absNorm:ℝ)
        =∏i : ↥Lᶜ,((x i).val.absNorm:ℝ) := by
          simp only [frozenProduct,map_prod,Nat.cast_prod]
          rfl
    _ ≤∏i : ↥Lᶜ,2*s.P i.val := by
      apply Finset.prod_le_prod₀ (fun i _=>Nat.cast_nonneg _) (fun i _=>?_)
      exact (s.hpn i.val _ (frozen_slot_mem s ha u L J x hw i)).2
    _ ≤∏i,2*s.P i := injected_prod_le (fun i : ↥Lᶜ=>i.val)
      Subtype.val_injective (fun i=>2*s.P i) (fun i=>by linarith [s.hP i])

theorem selected_norm_le (s : Source ι a b) (ha : 0<a)
    (u : Id) (L : Finset ι) (J : Finset {i // i∉Lᶜ})
    (y : Selected (supplierData s ha u L J))
    (hw : selectedWeight (supplierData s ha u L J) y≠0) :
    ((selectedProduct (supplierData s ha u L J) y).absNorm:ℝ)≤∏i,2*s.P i := by
  calc
    ((selectedProduct (supplierData s ha u L J) y).absNorm:ℝ)
        =∏j : J,((y j).val.absNorm:ℝ) := by
          simp only [selectedProduct,map_prod,Nat.cast_prod]
          rfl
    _ ≤∏j : J,2*s.P j.val.val := by
      apply Finset.prod_le_prod₀ (fun j _=>Nat.cast_nonneg _) (fun j _=>?_)
      exact (s.hpn j.val.val _ (selected_slot_mem s ha u L J y hw j)).2
    _ ≤∏i,2*s.P i := injected_prod_le (fun j : J=>j.val.val)
      (fun j k h=>Subtype.ext (Subtype.ext h)) (fun i=>2*s.P i)
      (fun i=>by linarith [s.hP i])

theorem residual_puncture_norm_le (s : Source ι a b) (ha : 0<a)
    (cover : OriginalEnclosure s) (u : Id) (L : Finset ι)
    (J : Finset {i // i∉Lᶜ}) (x : Frozen (supplierData s ha u L J))
    (hw : frozenWeight (supplierData s ha u L J) x≠0) :
    ((residualSource s ha cover u L J x).R.absNorm:ℝ)≤
      (s.R.absNorm:ℝ)*(∏i,2*s.P i) := by
  change ((s.R*frozenProduct (supplierData s ha u L J) x).absNorm:ℝ)≤_
  simp only [map_mul,Nat.cast_mul]
  exact mul_le_mul_of_nonneg_left (frozen_norm_le s ha u L J x hw) (Nat.cast_nonneg _)

theorem residual_scale_product (s : Source ι a b) (ha : 0<a) (cover : OriginalEnclosure s)
    (u : Id) (L : Finset ι) (J : Finset {i // i∉Lᶜ})
    (x : Frozen (supplierData s ha u L J)) :
    (∏j,2*(residualSource s ha cover u L J x).P j)≤∏i,2*s.P i := by
  exact rest_prod_le (supplierData s ha u L J) (fun i=>2*s.P i)
    (fun i=>by linarith [s.hP i])

theorem residual_slot_mass (s : Source ι a b) (ha : 0<a) (cover : OriginalEnclosure s)
    (u : Id) (L : Finset ι) (J : Finset {i // i∉Lᶜ})
    (x : Frozen (supplierData s ha u L J)) :
    (∏j,(residualSource s ha cover u L J x).M j)≤∏i,s.M i :=
  rest_prod_le (supplierData s ha u L J) s.M s.hM

/-- Actual original geometric caps are inherited, with no enlarged slot
count and no changed ordinary lengths or fixed-hole norm. -/
theorem residual_caps (s : Source ι a b) (ha : 0<a) (cover : OriginalEnclosure s)
    (u : Id) (L : Finset ι) (J : Finset {i // i∉Lᶜ})
    (x : Frozen (supplierData s ha u L J)) (N : ℕ) (Z Bcap Lcap : ℝ)
    (hN : Fintype.card ι≤N) (hF : (s.Fhole.absNorm:ℝ)≤Z^Bcap)
    (hP : (∏i,2*s.P i)≤Z^Bcap)
    (hX₁ : s.X₁≤Z^Lcap) (hX₂ : s.X₂≤Z^Lcap)
    (hY₁ : s.Y₁≤Z^Lcap) (hY₂ : s.Y₂≤Z^Lcap) :
    let r := residualSource s ha cover u L J x
    Fintype.card (RestIndex (supplierData s ha u L J))≤N ∧
      (r.Fhole.absNorm:ℝ)≤Z^Bcap ∧ (∏j,2*r.P j)≤Z^Bcap ∧
      r.X₁≤Z^Lcap ∧ r.X₂≤Z^Lcap ∧ r.Y₁≤Z^Lcap ∧ r.Y₂≤Z^Lcap :=
  ⟨(rest_card_le (supplierData s ha u L J)).trans hN,hF,
    (residual_scale_product s ha cover u L J x).trans hP,hX₁,hX₂,hY₁,hY₂⟩

/-- The combined constructor theorem, specialized to actual source-made
supplier data. It is independent of any analytic source or energy bound. -/
theorem exists_residual_source (s : Source ι a b) (ha : 0<a) (cover : OriginalEnclosure s)
    (u : Id) (L : Finset ι) (J : Finset {i // i∉Lᶜ})
    (x : Frozen (supplierData s ha u L J)) :
    ∃r : Source (RestIndex (supplierData s ha u L J)) a b,
      Matches (supplierData s ha u L J) x r ha ∧ OriginalEnclosure r ∧
      r.R=s.R*frozenProduct (supplierData s ha u L J) x ∧ r.d=s.d ∧
      r.L=s.L ∧ r.T=s.T ∧ r.X₁=s.X₁ ∧ r.X₂=s.X₂ ∧ r.Y₁=s.Y₁ ∧ r.Y₂=s.Y₂ ∧
      Fintype.card (RestIndex (supplierData s ha u L J))≤Fintype.card ι ∧
      (∏j,2*r.P j)≤∏i,2*s.P i := by
  refine ⟨residualSource s ha cover u L J x,residual_matches s ha cover u L J x,
    residual_enclosure s ha cover u L J x,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,
    rest_card_le (supplierData s ha u L J),residual_scale_product s ha cover u L J x⟩

end
end Candidate.SilPrior.FourthPower.OuterFreshSource
