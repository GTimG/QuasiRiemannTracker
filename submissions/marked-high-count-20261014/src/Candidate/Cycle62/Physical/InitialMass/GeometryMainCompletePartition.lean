/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle62.Physical.InitialMass.GeometryMainLowPhysicalPayment
import Candidate.Cycle62.Physical.InitialMass.SecondFullNormalizedContraction

set_option autoImplicit false
set_option maxHeartbeats 60000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentAmplificationChildInput CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondLiveBlock CenteredMomentSourceRow
open LocalMoment CenteredMomentSecondInputCapacitySource CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondEnergySplit ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]

/-- Lift the per-source selector to the physical family before dividing it
into low and high rows. The signed row and its original block are unchanged. -/
def mainPhysicalFamilySelector (second : Bool) (d : Label→SecondInputDatum α) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→BufferIndex e) :
    secondLiveRows (fun l=>(d l).block)→BufferIndex e :=
  fun r=>select r.val.1 r.val.2.1 r.val.2.2.1
    ⟨mainLowSignedRow second r.val.2.2.2.val,by
      apply (mem_main_low_source_rows second _ (fun _=>True) _).mpr
      refine ⟨r.val.2.2.2,?_,rfl,True.intro⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp r.property).2⟩⟩

theorem main_low_physical_predicate_iff (second : Bool) (d : Label→SecondInputDatum α) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→BufferIndex e)
    (r : secondLiveRows (fun l=>(d l).block)) :
    mainLowPhysicalSourcePredicate (mainLowSourceRows second (d r.val.1) (fun _=>True))
      (select r.val.1 r.val.2.1 r.val.2.2.1) (mainLowSignedRow second r.val.2.2.2.val) ↔
    bufferValue e (mainPhysicalFamilySelector second d select r)<21/25 := by
  have hz : mainLowSignedRow second r.val.2.2.2.val∈
      mainLowSourceRows second (d r.val.1) (fun _=>True) := by
    apply (mem_main_low_source_rows second _ (fun _=>True) _).mpr
    exact ⟨r.val.2.2.2,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,(Finset.mem_filter.mp r.property).2⟩,rfl,True.intro⟩
  simp only [mainLowPhysicalSourcePredicate,dite_eq_left hz,mainPhysicalFamilySelector]

/-- Exact complementary physical costs on one selector. Both ray sums,
both signed Mellin heights, the lower factor, and all residual divisors remain
literal. No arithmetic-label or allocation count is introduced. -/
theorem actual_main_complete_low_high_partition
    (N : ℕ) (a ap : ℝ) (second : Bool) (d : Label→SecondInputDatum α)
    (coefficient : Label→ℝ) (t u : ℝ) {e : ℝ}
    (select : (l : Label)→(χ ψ : RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→BufferIndex e) :
    (∑l,coefficient l*mainNormalizedBlockCost N a ap second (d l) t u)=
      mainLowPhysicalCompleteCost N a ap second d coefficient t u select+
      ∑r∈Finset.univ.filter (fun r : secondLiveRows (fun l=>(d l).block)=>
        21/25≤bufferValue e (mainPhysicalFamilySelector second d select r)),
        (coefficient r.val.1*((d r.val.1).K/lowerFactor N a ap)*
          normalizer (d r.val.1).C (d r.val.1).D (d r.val.1).inactive)*
        highNormalizedRowCost second d r
          ((d r.val.1).input.t+2*Real.pi*(u-(if second then -t else t)))
          ((d r.val.1).block.divisors.filter Squarefree) := by
  rw [actual_main_block_cost_rows]
  rw [←Finset.sum_coe_sort]
  rw [actual_main_low_physical_ordinary_row_cost]
  unfold mainLowPhysicalOrdinaryRows
  rw [Finset.sum_filter,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  have hcost : (∑D∈secondResidualIdeals (fun l=>(d l).block) r.val,
      mainNormalizedPhysicalCost N a ap second d coefficient t u r.val D)=
      (coefficient r.val.1*((d r.val.1).K/lowerFactor N a ap)*
        normalizer (d r.val.1).C (d r.val.1).D (d r.val.1).inactive)*
      highNormalizedRowCost second d r
        ((d r.val.1).input.t+2*Real.pi*(u-(if second then -t else t)))
        ((d r.val.1).block.divisors.filter Squarefree) := by
    rw [actual_second_residual_ideals_label]
    cases second <;> simp [mainNormalizedPhysicalCost,highNormalizedRowCost,Finset.mul_sum]
  rw [hcost]
  have hp:=main_low_physical_predicate_iff second d select r
  by_cases hl : bufferValue e (mainPhysicalFamilySelector second d select r)<21/25
  · simp only [hp,hl,ite_true,not_le.mpr hl,ite_false,add_zero]
  · simp only [hp,hl,ite_false,le_of_not_gt hl,ite_true,zero_add]

/-- The lift used in the exact partition is the existing canonical family
selector. This equality fixes the same selector on both complementary costs. -/
theorem main_physical_family_canonical_selector_eq
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (d : Label→SecondInputDatum α) (χ₀ : Label→RayCharacter) (Q : Ideal O)
    (hQ : Q≤Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (Z Bmask : ℝ) (hZ : 1<Z) (second : Bool)
    (hP : ∀l,(d l).R*(if second then (d l).D else (d l).C)≠0)
    (hPN : ∀l,(((d l).R*(if second then (d l).D else (d l).C)).absNorm:ℝ)≤Z^Bmask)
    (η₀ : Character) (hQM : Q≤M) (hQη : Q≤η₀.modulus)
    (e T : ℝ) (he : 0<e) (hT : 2<T)
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8) :
    mainPhysicalFamilySelector second (fun l=>ordinarySecondDatum (d l) (χ₀ l) Q m)
      (fun l χ ψ=>mainLowCanonicalSelector M H hH (d l) (χ₀ l) χ ψ Q hQ m hm hml hm2
        Z Bmask hZ second (hP l) (hPN l) η₀ hQM hQη e T he hT hβlo hβhi)=
    mainLowFamilyCanonicalSelector M H hH d χ₀ Q hQ m hm hml hm2 Z Bmask hZ second
      hP hPN η₀ hQM hQη e T he hT hβlo hβhi := rfl

/-- Complete complementary physical bounds give the exact normalized
ratio-fiber contract. The original source height belongs in `CL` and `CH`;
only the two inner Mellin heights are paid by the common degree here. -/
theorem second_normalized_bound_of_complete_low_high
    (N : ℕ) (a ap : ℝ) (ha : 0<a) (hap : 0<ap)
    (d : Label→SecondInputDatum α) (w : Label→ℂ) (W : 𝓢(ℝ,ℂ))
    (coefficient : Label→ℝ) (hw : ∀l,‖w l‖≤coefficient l)
    (hcard : Fintype.card α≤N) (hlower : ∀l,a≤(d l).input.lower)
    (hW₁ : ∀l x,(d l).input.W₁ x≠0→ap≤x)
    (hW₂ : ∀l x,(d l).input.W₂ x≠0→ap≤x)
    {e : ℝ} (select : (second : Bool)→(l : Label)→(χ ψ : RayCharacter)→
      mainLowSourceRows second (d l) (fun _=>True)→BufferIndex e)
    (CL CH : ℝ) (dl dh : ℕ) (hCL : 0≤CL) (hCH : 0≤CH)
    (hlow : ∀(second : Bool)(t u : ℝ),
      mainLowPhysicalCompleteCost N a ap second d coefficient t u (select second)≤
        (CL*(1+‖t‖)^dl)*(1+‖u‖)^dl)
    (hhigh : ∀(second : Bool)(t u : ℝ),
      (∑r∈Finset.univ.filter (fun r : secondLiveRows (fun l=>(d l).block)=>
        21/25≤bufferValue e (mainPhysicalFamilySelector second d (select second) r)),
        (coefficient r.val.1*((d r.val.1).K/lowerFactor N a ap)*
          normalizer (d r.val.1).C (d r.val.1).D (d r.val.1).inactive)*
        highNormalizedRowCost second d r
          ((d r.val.1).input.t+2*Real.pi*(u-(if second then -t else t)))
          ((d r.val.1).block.divisors.filter Squarefree))≤
        (CH*(1+‖t‖)^dh)*(1+‖u‖)^dh) :
    SecondNormalizedBound W (max dl dh) (max dl dh) d w (fun _=>CL+CH) (fun _=>1) := by
  apply second_normalized_bound_of_full
  intro second t u
  have hc:=actual_main_normalized_coefficient_cost N a ap ha hap d w W coefficient hw
    hcard hlower hW₁ hW₂ second t u
  rw [actual_main_complete_low_high_partition N a ap second d coefficient t u (select second)] at hc
  have hsplit:=hc.trans (add_le_add (hlow second t u) (hhigh second t u))
  have hm (C : ℝ) (k : ℕ) (hC : 0≤C) (hk : k≤max dl dh) :
      (C*(1+‖t‖)^k)*(1+‖u‖)^k≤
        (C*(1+‖t‖)^(max dl dh))*(1+‖u‖)^(2*max dl dh) := by
    have ht : 1≤1+‖t‖ := by linarith [norm_nonneg t]
    have hu : 1≤1+‖u‖ := by linarith [norm_nonneg u]
    have hku : k≤2*max dl dh := by omega
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht hk) hC)
      (pow_le_pow_right₀ hu hku) (pow_nonneg (zero_le_one.trans hu) _)
      (mul_nonneg hC (pow_nonneg (zero_le_one.trans ht) _))
  apply (hsplit.trans (add_le_add (hm CL dl hCL (le_max_left _ _))
    (hm CH dh hCH (le_max_right _ _)))).trans_eq
  ring

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.main_low_physical_predicate_iff
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_main_complete_low_high_partition
#print axioms OAI.SevenEighths.Cycle62InitialMass.main_physical_family_canonical_selector_eq
#print axioms OAI.SevenEighths.Cycle62InitialMass.second_normalized_bound_of_complete_low_high
