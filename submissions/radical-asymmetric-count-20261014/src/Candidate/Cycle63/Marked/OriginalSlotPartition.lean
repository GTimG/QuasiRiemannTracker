import Candidate.Cycle63.Marked.CommonStageSupply

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63CommonSupply
noncomputable section
open scoped Classical BigOperators
open CenteredMomentCommonProfile

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The surviving slots are indexed by a subset of the original fixed slots. -/
def originalSlots {J : Type*} [Fintype J] (f : J→ι) : Finset ι :=
  Finset.univ.image f

theorem prod_originalSlots {J : Type*} [Fintype J] (f : J→ι)
    (hf : Function.Injective f) {R : Type*} [CommMonoid R] (g : ι→R) :
    (∏j,g (f j))=∏i∈originalSlots f,g i := by
  rw [originalSlots,Finset.prod_image]
  exact fun _ _ _ _ h => hf h

theorem sum_originalSlots {J : Type*} [Fintype J] (f : J→ι)
    (hf : Function.Injective f) (g : ι→ℝ) :
    (∑j,g (f j))=∑i∈originalSlots f,g i := by
  rw [originalSlots,Finset.sum_image]
  exact fun _ _ _ _ h => hf h

/-- Both common allocations only take subtypes, so their surviving index map
is injective independently of the values of either allocation. -/
theorem double_subtype_injective (s : Finset ι) (t : Finset s) :
    Function.Injective (fun i : t => i.val.val) := by
  intro a b h
  exact Subtype.ext (Subtype.ext h)

theorem double_subtype_prod (s : Finset ι) (t : Finset s)
    {R : Type*} [CommMonoid R] (g : ι→R) :
    (∏i : t,g i.val.val)=∏i∈originalSlots (fun i : t=>i.val.val),g i :=
  prod_originalSlots _ (double_subtype_injective s t) g

theorem double_subtype_sum (s : Finset ι) (t : Finset s) (g : ι→ℝ) :
    (∑i : t,g i.val.val)=∑i∈originalSlots (fun i : t=>i.val.val),g i :=
  sum_originalSlots _ (double_subtype_injective s t) g

/-- Reindexing varying slot sets costs only the fixed number of subsets of
the original family; no row-dependent finite type is counted as a constant. -/
theorem slot_partition_sum {Label : Type*} (labels : Finset Label)
    (S : Label→Finset ι) (F : Label→ℝ) :
    (∑l∈labels,F l)=∑s∈(Finset.univ : Finset ι).powerset,
      ∑l∈labels.filter (fun l=>S l=s),F l := by
  symm
  exact Finset.sum_fiberwise_of_maps_to (fun _ _=>Finset.mem_powerset.mpr
    (Finset.subset_univ _)) F

theorem slot_partition_bound {Label : Type*} (labels : Finset Label)
    (S : Label→Finset ι) (F : Label→ℝ) (E : ℝ)
    (hE : ∀s : Finset ι,(∑l∈labels.filter (fun l=>S l=s),F l)≤E) :
    (∑l∈labels,F l)≤(2:ℝ)^(Fintype.card ι)*E := by
  rw [slot_partition_sum labels S F]
  calc
    _≤∑_s∈(Finset.univ : Finset ι).powerset,E :=
      Finset.sum_le_sum (fun s _=>hE s)
    _=(2:ℝ)^(Fintype.card ι)*E := by simp

/-- The variable products can be put into fixed original-slot fibers before
applying the natural row count. -/
theorem variable_slot_partition_bound {Label : Type*} (labels : Finset Label)
    (J : Label→Type*) [∀l,Fintype (J l)] (f : ∀l,J l→ι)
    (hf : ∀l,Function.Injective (f l)) (coeff : Label→ℝ)
    (g : Label→ι→ℝ) (E : ℝ)
    (hE : ∀s : Finset ι,
      (∑l∈labels.filter (fun l=>originalSlots (f l)=s),coeff l*(∏i∈s,g l i))≤E) :
    (∑l∈labels,coeff l*(∏j,g l (f l j)))≤(2:ℝ)^(Fintype.card ι)*E := by
  apply slot_partition_bound labels (fun l=>originalSlots (f l)) _ E
  intro s
  convert hE s using 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [prod_originalSlots (f l) (hf l),(Finset.mem_filter.mp hl).2]

end
end OAI.SevenEighths.Cycle63CommonSupply
#print axioms OAI.SevenEighths.Cycle63CommonSupply.variable_slot_partition_bound
