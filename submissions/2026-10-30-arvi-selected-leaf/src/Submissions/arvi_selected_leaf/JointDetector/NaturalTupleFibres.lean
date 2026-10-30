/- Copyright (c) 2026 Joseph Bebel. All rights reserved. -/
import Submissions.arvi_selected_leaf.JointDetector.NaturalSelectedNorm
import Submissions.arvi_selected_leaf.JointDetector.NaturalSharedTables

/-! Exact nonrectangular higher-tuple/pivot fibre indexing. Arbitrary coefficient
vectors retain their squared mass; no independent-product enlargement occurs. -/
namespace Qrh.JointDetector.NaturalSelectedNorm
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalQuadraticSieve CompletedGauss
local notation "O" => ActualEisensteinCubic.O

abbrev IdealFibre (F : Finset ColourTuple) :=
  (v : F.image higherTuple) × pivotFamily F v.val

def tupleToFibre (F : Finset ColourTuple) (c : F) : IdealFibre F :=
  ⟨⟨higherTuple c.val,Finset.mem_image.mpr ⟨c.val,c.property,rfl⟩⟩,
    ⟨c.val 0,mem_pivotFamily.mpr ⟨c.val,c.property,rfl,rfl⟩⟩⟩

theorem tupleToFibre_injective (F : Finset ColourTuple) : Function.Injective (tupleToFibre F) := by
  intro c d he
  have hh := congrArg (fun v : IdealFibre F => v.1.val) he
  have h0 := congrArg (fun v : IdealFibre F => v.2.val) he
  apply Subtype.ext
  funext j
  refine Fin.cases h0 (fun k => ?_) j
  exact congrFun hh k

theorem tupleToFibre_surjective (F : Finset ColourTuple) : Function.Surjective (tupleToFibre F) := by
  rintro ⟨⟨v,hv⟩,⟨I,hI⟩⟩
  obtain ⟨c,hc,rfl,rfl⟩ := mem_pivotFamily.mp hI
  exact ⟨⟨c,hc⟩,rfl⟩

def tupleIdealFibreEquiv (F : Finset ColourTuple) : F ≃ IdealFibre F :=
  Equiv.ofBijective (tupleToFibre F) ⟨tupleToFibre_injective F,tupleToFibre_surjective F⟩

abbrev ElementFibre (F : Finset ColourTuple) :=
  (v : F.image higherTuple) × (pivotFamily F v.val).image primaryGenerator

def tupleElementFibreEquiv (F : Finset ColourTuple) (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) :
    F ≃ ElementFibre F :=
  (tupleIdealFibreEquiv F).trans (Equiv.sigmaCongrRight fun v =>
    primaryRowEquiv (pivotFamily F v.val) (pivotFamily_admissible F hF v.val))

theorem tupleElementFibreEquiv_higher (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c : F) :
    (tupleElementFibreEquiv F hF c).1.val=higherTuple c.val := rfl

theorem tupleElementFibreEquiv_pivot (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (c : F) :
    (tupleElementFibreEquiv F hF c).2.val=primaryGenerator (c.val 0) := rfl

theorem tupleElementFibre_row (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (v : ElementFibre F) :
    tupleRow ((tupleElementFibreEquiv F hF).symm v).val=higherRow v.1.val*v.2.val := by
  obtain ⟨c,rfl⟩ := (tupleElementFibreEquiv F hF).surjective v
  rw [Equiv.symm_apply_apply]
  exact tupleRow_pivot c.val

theorem tupleElementFibre_mass (F : Finset ColourTuple)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (a : F → ℂ) :
    (∑ v : ElementFibre F, ‖a ((tupleElementFibreEquiv F hF).symm v)‖^2)=
      ∑ c : F, ‖a c‖^2 :=
  (tupleElementFibreEquiv F hF).symm.sum_comp (fun c => ‖a c‖^2)

open NaturalSharedTables

theorem tupleRow_mul (a b : ColourTuple) :
    tupleRow (fun j => a j*b j)=tupleRow a*tupleRow b := by
  unfold tupleRow
  simp only [primaryGenerator_mul,mul_pow,Finset.prod_mul_distrib]

theorem recoverLeft_row (g : SharedTable) (a : ColourTuple) :
    tupleRow (recoverLeft g a)=tupleRow (rowProduct g)*tupleRow a := tupleRow_mul _ _

theorem recoverRight_row (g : SharedTable) (b : ColourTuple) :
    tupleRow (recoverRight g b)=tupleRow (columnProduct g)*tupleRow b := tupleRow_mul _ _

def leftFamily (F : Finset ColourTuple) (g : SharedTable) : Finset ColourTuple :=
  (residualFibre F g).image Prod.fst

def rightFamily (F : Finset ColourTuple) (g : SharedTable) : Finset ColourTuple :=
  (residualFibre F g).image Prod.snd

theorem leftFamily_ok {F : Finset ColourTuple} {g : SharedTable}
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hgn : ∀ j k,g j k ≠ 0)
    (hgp : Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)))
    {a : ColourTuple} (ha : a ∈ leftFamily F g) : LeftOK F g a := by
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ha
  exact ((mem_residualFibre_iff_factorized hF hpF hgn hgp r).mp hr).1

theorem rightFamily_ok {F : Finset ColourTuple} {g : SharedTable}
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hgn : ∀ j k,g j k ≠ 0)
    (hgp : Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2)))
    {b : ColourTuple} (hb : b ∈ rightFamily F g) : RightOK F g b := by
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hb
  exact ((mem_residualFibre_iff_factorized hF hpF hgn hgp r).mp hr).2.1

/-- Projected left/right families are fixed before both free pivots and the
ordinary source. Their full product is restricted by the exact cross masks. -/
theorem residualFibre_eq_cross_filter {F : Finset ColourTuple} {g : SharedTable}
    (hF : ∀ c ∈ F,∀ j,Admissible (c j))
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hgn : ∀ j k,g j k ≠ 0)
    (hgp : Pairwise (fun p q : Fin 5 × Fin 5 => IsCoprime (g p.1 p.2) (g q.1 q.2))) :
    residualFibre F g = ((leftFamily F g).product (rightFamily F g)).filter
      (fun r => ∀ j k, IsCoprime (r.1 j) (r.2 k)) := by
  ext r
  constructor
  · intro hr
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_,?_⟩,?_⟩
    · exact Finset.mem_image.mpr ⟨r,hr,rfl⟩
    · exact Finset.mem_image.mpr ⟨r,hr,rfl⟩
    · exact ((mem_residualFibre_iff_factorized hF hpF hgn hgp r).mp hr).2.2
  · intro hr
    obtain ⟨hab,hcross⟩ := Finset.mem_filter.mp hr
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    exact (mem_residualFibre_iff_factorized hF hpF hgn hgp r).mpr
      ⟨leftFamily_ok hF hpF hgn hgp ha,rightFamily_ok hF hpF hgn hgp hb,hcross⟩

theorem leftFamily_selects {N : ℕ} {d : SelectedSlotData N} {Z : ℝ}
    {F : Finset ColourTuple} {g : SharedTable}
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hs : d.Selects Z (F.image tupleRow)) :
    (d.quotient (tupleRow (rowProduct g))).Selects Z ((leftFamily F g).image tupleRow) := by
  apply SelectedSlotData.quotient_selects hs
  intro z hz
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hr
  have he := recover_pair_of_mem hpF hp
  apply Finset.mem_image.mpr
  refine ⟨p.1,(Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1,?_⟩
  have hl : recoverLeft g (residualPair p).1=p.1 := congrArg Prod.fst he
  rw [← hl,recoverLeft_row]

theorem rightFamily_selects {N : ℕ} {d : SelectedSlotData N} {Z : ℝ}
    {F : Finset ColourTuple} {g : SharedTable}
    (hpF : ∀ c ∈ F,Pairwise (fun j k => IsCoprime (c j) (c k)))
    (hs : d.Selects Z (F.image tupleRow)) :
    (d.quotient (tupleRow (columnProduct g))).Selects Z ((rightFamily F g).image tupleRow) := by
  apply SelectedSlotData.quotient_selects hs
  intro z hz
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hr
  have he := recover_pair_of_mem hpF hp
  apply Finset.mem_image.mpr
  refine ⟨p.2,(Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2,?_⟩
  have hl : recoverRight g (residualPair p).2=p.2 := congrArg Prod.snd he
  rw [← hl,recoverRight_row]

end
end Qrh.JointDetector.NaturalSelectedNorm

#print axioms Qrh.JointDetector.NaturalSelectedNorm.tupleElementFibre_mass

#print axioms Qrh.JointDetector.NaturalSelectedNorm.residualFibre_eq_cross_filter
#print axioms Qrh.JointDetector.NaturalSelectedNorm.leftFamily_selects
