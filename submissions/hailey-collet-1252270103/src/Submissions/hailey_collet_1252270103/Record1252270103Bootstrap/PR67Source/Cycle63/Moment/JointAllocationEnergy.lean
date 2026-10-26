import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.JointColumnExtraction
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AllocationCost
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators

/-- Select a maximizing allocation separately at each source label, then
apply one joint bound. Only the allocation weight is paid; there is no
additional count of source labels. Empty allocation sets contribute zero. -/
theorem joint_weighted_selection {Label : Type*} [Fintype Label]
    {β : Label→Type*} [∀l,Fintype (β l)] (weight cost : (l : Label)→β l→ℝ)
    (W E : ℝ) (hW : 0≤W)
    (hw : ∀l a,0≤weight l a) (hc : ∀l a,0≤ cost l a)
    (hmass : ∀l,∑a,weight l a≤W)
    (hjoint : ∀S : Finset Label,∀pick : (l : S)→β l.val,
      (∑l : S,cost l.val (pick l))≤E) :
    (∑l,∑a,weight l a*cost l a)≤W*E := by
  let S : Finset Label := Finset.univ.filter (fun l=>Nonempty (β l))
  have hnonempty (l : S) : (Finset.univ : Finset (β l.val)).Nonempty := by
    have : Nonempty (β l.val) := (Finset.mem_filter.mp l.property).2
    exact Finset.univ_nonempty
  choose pick hpick hmax using (fun l : S=>
    Finset.exists_max_image Finset.univ (cost l.val) (hnonempty l))
  have he := hjoint S pick
  have hsum : (∑l,∑a,weight l a*cost l a)=
      ∑l : S,∑a,weight l.val a*cost l.val a := by
    rw [Finset.sum_coe_sort S (fun l=>∑a,weight l a*cost l a)]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro l hl hnot
    have hempty : IsEmpty (β l) := ⟨fun a=>hnot (Finset.mem_filter.mpr ⟨hl,⟨a⟩⟩)⟩
    let _ := hempty
    simp
  rw [hsum]
  calc
    _ ≤ ∑l : S,W*cost l.val (pick l) := by
      refine Finset.sum_le_sum fun l hl => ?_
      calc
        _ ≤ ∑a,weight l.val a*cost l.val (pick l) :=
          Finset.sum_le_sum (fun a ha=>mul_le_mul_of_nonneg_left (hmax l a ha) (hw _ _))
        _ = (∑a,weight l.val a)*cost l.val (pick l) := (Finset.sum_mul ..).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right (hmass _) (hc _ _)
    _ = W*∑l : S,cost l.val (pick l) := (Finset.mul_sum ..).symm
    _ ≤ W*E := mul_le_mul_of_nonneg_left he hW

/-- Zero-weight allocations are excluded before choosing maxima. This
retains the support information required for the sharp common-ideal shift. -/
theorem joint_supported_weighted_selection {Label : Type*} [Fintype Label]
    {β : Label→Type*} [∀l,Fintype (β l)] (weight cost : (l : Label)→β l→ℝ)
    (W E : ℝ) (hW : 0≤W)
    (hw : ∀l a,0≤weight l a) (hc : ∀l a,0≤ cost l a)
    (hmass : ∀l,∑a,weight l a≤W)
    (hjoint : ∀S : Finset Label,∀pick : (l : S)→β l.val,
      (∀l,weight l.val (pick l)≠0) → (∑l : S,cost l.val (pick l))≤E) :
    (∑l,∑a,weight l a*cost l a)≤W*E := by
  let live (l : Label) : Finset (β l) := Finset.univ.filter (fun a=>weight l a≠0)
  have he := joint_weighted_selection (β:=fun l=>live l)
    (fun l a=>weight l a.val) (fun l a=>cost l a.val) W E hW
    (fun l a=>hw l a.val) (fun l a=>hc l a.val)
    (fun l=> (le_of_eq (Finset.sum_coe_sort (live l) (weight l))).trans
      ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _=>hw l a)).trans
        (hmass l)))
    (fun S pick=>hjoint S (fun l=>(pick l).val)
      (fun l=>(Finset.mem_filter.mp (pick l).property).2))
  have heq (l : Label) : (∑a : live l,weight l a.val*cost l a.val)=
      ∑a,weight l a*cost l a := by
    rw [Finset.sum_coe_sort (live l) (fun a=>weight l a*cost l a)]
    simp only [live,Finset.sum_filter]
    refine Finset.sum_congr rfl fun a ha => ?_
    by_cases h:weight l a=0 <;> simp [h]
  simpa only [heq] using he

/-- Repeated physical rows are selected jointly over their encoded image.
The fiber size is paid once; the bound on selected costs still ranges over
all encoded rows together. -/
theorem joint_fiber_selection {Row Key : Type*} [Fintype Row] [DecidableEq Key]
    (key : Row→Key) (cost : Row→ℝ) (W E : ℝ) (hW : 0≤W)
    (hc : ∀r,0≤ cost r)
    (hmass : ∀k∈Finset.univ.image key,
      ((Finset.univ.filter (fun r=>key r=k)).card:ℝ)≤W)
    (hjoint : ∀pick : (k : Finset.univ.image key)→Row,
      (∀k,key (pick k)=k.val) → (∑k : Finset.univ.image key,cost (pick k))≤E) :
    (∑r,cost r)≤W*E := by
  let keys := Finset.univ.image key
  let fiber (k : Key) := Finset.univ.filter (fun r=>key r=k)
  have hnonempty (k : keys) : (fiber k.val).Nonempty := by
    obtain ⟨r,hr,he⟩ := Finset.mem_image.mp k.property
    exact ⟨r,Finset.mem_filter.mpr ⟨hr,he⟩⟩
  choose pick hpick hmax using (fun k : keys=>
    Finset.exists_max_image (fiber k.val) cost (hnonempty k))
  have he := hjoint pick (fun k=>(Finset.mem_filter.mp (hpick k)).2)
  have hsum : (∑k : keys,∑r∈fiber k.val,cost r)=∑r,cost r := by
    rw [Finset.sum_coe_sort keys (fun k=>∑r∈fiber k,cost r)]
    exact Finset.sum_fiberwise_of_maps_to (fun r hr=>Finset.mem_image_of_mem key hr) cost
  rw [←hsum]
  calc
    _≤∑k : keys,W*cost (pick k) := by
      refine Finset.sum_le_sum fun k hk => ?_
      calc
        _≤∑_r∈fiber k.val,cost (pick k) := Finset.sum_le_sum (fun r hr=>hmax k r hr)
        _=(fiber k.val).card*cost (pick k) := by simp
        _≤W*cost (pick k) := mul_le_mul_of_nonneg_right (hmass k.val k.property) (hc _)
    _=W*∑k : keys,cost (pick k) := (Finset.mul_sum ..).symm
    _≤W*E := mul_le_mul_of_nonneg_left he hW

open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentCommonLinearNormalization
local notation "O" => HeckeFamily.O

/-- The actual squared common coefficients, including the allocation
Cauchy factor, cost only a small power of the common ideal beyond its
inverse norm. Slot controls remain exactly quadratic. -/
theorem uniform_common_scalar_mass (N : ℕ) (b ε : ℝ) (hε : 0<ε) :
    ∃K : ℝ,0<K ∧ ∀{ι : Type*}[Fintype ι][DecidableEq ι],
      Fintype.card ι≤N → ∀s : Input ι,s.upper≤b → ∀C R : Ideal O,C≠0 →
      ((actualAllocations s.pools C).card:ℝ)*
        (∑B : actualAllocations s.pools C,‖commonScalar s C R B‖^2)≤
          K*(∏i,s.M i)^2*(C.absNorm:ℝ)^(ε-1) := by
  obtain ⟨D,hD,hcard⟩ := CenteredMomentAllocationCost.actualAllocations_uniform_small_power
    (N+2) (ε/2) (half_pos hε)
  refine ⟨D^2*(max 1 b)^N,by positivity,?_⟩
  intro ι _ _ hn s hs C R hC
  have hnorm : 0<(C.absNorm:ℝ) := CenteredMomentFirstScale.norm_pos C hC
  have hc := hcard (ι:=ι⊕Fin 2)
    (by simp only [Fintype.card_sum,Fintype.card_fin];omega) s.pools C hC
  have hc₂ := pow_le_pow_left₀ (Nat.cast_nonneg (actualAllocations s.pools C).card) hc 2
  rw [mul_pow,←Real.rpow_mul_natCast hnorm.le,show ε/2*(2:ℕ)=ε by norm_num] at hc₂
  have hsup : (max 1 s.upper)^Fintype.card ι≤(max 1 b)^N :=
    (pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) (max_le_max_left 1 hs) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) hn)
  have hpoint (B : actualAllocations s.pools C) : ‖commonScalar s C R B‖^2≤
      (∏i,s.M i)^2*(max 1 b)^N/(C.absNorm:ℝ) :=
    (commonScalar_sq_bound s C R hC B).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsup (sq_nonneg _)) hnorm.le)
  calc
    _ ≤ ((actualAllocations s.pools C).card:ℝ)*
        ∑_B : actualAllocations s.pools C,(∏i,s.M i)^2*(max 1 b)^N/(C.absNorm:ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun B _=>hpoint B)) (Nat.cast_nonneg _)
    _ = ((actualAllocations s.pools C).card:ℝ)^2*
        ((∏i,s.M i)^2*(max 1 b)^N/(C.absNorm:ℝ)) := by simp;ring
    _ ≤ (D^2*(C.absNorm:ℝ)^ε)*
        ((∏i,s.M i)^2*(max 1 b)^N/(C.absNorm:ℝ)) :=
      mul_le_mul_of_nonneg_right hc₂ (by positivity)
    _ = _ := by rw [Real.rpow_sub hnorm,Real.rpow_one];ring

end
end OAI.SevenEighths.Cycle63Moment

end Record1252270103Bootstrap.PR67
