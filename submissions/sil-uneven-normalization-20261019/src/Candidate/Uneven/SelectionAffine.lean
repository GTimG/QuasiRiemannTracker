import Candidate.Uneven.Amplification
import Candidate.Uneven.HighMass
import Candidate.Cycle63.Physical.InitialMass.GeometryAllocationMass
import Candidate.Cycle63.Moment.JointAllocationEnergy
import Candidate.Cycle63.Physical.InitialMass.GeometryCostSelection
import Candidate.Uneven.SelectionCostReduction
import Candidate.Cycle63.Physical.InitialMass.GeometryHighPayment
import Candidate.Uneven.SecondWeight
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineExceptionalGates

/- Original module: Candidate.Uneven.SelectionAllocationMass. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.UnevenSelection
noncomputable section
open OAI.SevenEighths.TargetHigh830
open OAI.SevenEighths.Target830.Source.Uneven
open Cycle63InitialMass Target830.Source
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentFirstAllocationGaussEnergy CenteredMomentAllocationCost
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplificationChoice CenteredMomentGaussNormalization
open CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O

/-- The actual amplification weights pay a small power of the common
ideal and its inverse norm. The two allocation cardinalities are included. -/
theorem actual_geometry_allocation_mass (N : ℕ) (Cs b ε : ℝ) (hCs : 1≤ Cs) (hε : 0<ε) :
    ∃D : ℝ,0< D ∧ ∀{ι : Type*}[Fintype ι][DecidableEq ι](s : Input ι),
      Fintype.card ι≤ N → (∀i,s.M i≤ Cs) →
      ∀(reflected : Bool)(R seed : Ideal O)(K Z ξ M A : ℝ)(hK : 0< K)
        (key : ℤ×(Fin 5→ℤ))
        (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
        (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)),
      geometryColumnIdeal reflected s R seed K Z ξ hK key j≠0 →
      (∑B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j),
        unevenAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j B)≤
      D*‖unevenColumnScalar reflected s R seed K Z ξ M A hK key weight j‖^2*
        ((geometryColumnIdeal reflected s R seed K Z ξ hK key j).absNorm:ℝ)^(ε-1) := by
  obtain ⟨D,hD,hcard⟩ := actualAllocations_uniform_small_power (N+2) (ε/2) (half_pos hε)
  refine ⟨D^2*(max 1 b)^N*(Cs^N)^2,by positivity,?_⟩
  intro ι _ _ s hn hM reflected R seed K Z ξ M A hK key weight j hC
  let C := geometryColumnIdeal reflected s R seed K Z ξ hK key j
  let scalar := unevenColumnScalar reflected s R seed K Z ξ M A hK key weight j
  have hnorm : 0<(C.absNorm:ℝ) := CenteredMomentFirstScale.norm_pos _ hC
  have hc := hcard (ι:=ι⊕Fin 2) (by simp only [Fintype.card_sum,Fintype.card_fin];omega) s.pools C hC
  have hc₂ := pow_le_pow_left₀ (Nat.cast_nonneg (actualAllocations s.pools C).card) hc 2
  rw [mul_pow,←Real.rpow_mul_natCast hnorm.le,show ε/2*(2:ℕ)=ε by norm_num] at hc₂
  have hf (B : actualAllocations s.pools C) : (frozenControl B.val s.M)^2≤(Cs^N)^2 := by
    apply pow_le_pow_left₀ (frozenControl_nonneg B.val s.M (fun i=> zero_le_one.trans (s.M_ge_one i)))
    unfold frozenControl
    calc
      _≤∏_i∈Finset.univ.filter (fun i=> B.val (Sum.inl i)≠1),Cs :=
        Finset.prod_le_prod₀ (fun i _=> zero_le_one.trans (s.M_ge_one i)) (fun i _=> hM i)
      _=Cs^((Finset.univ.filter (fun i=> B.val (Sum.inl i)≠1)).card) := by simp
      _≤ Cs^N := pow_le_pow_right₀ hCs ((Finset.card_le_univ _).trans hn)
  have hp (B : actualAllocations s.pools C) :
      unevenAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j B≤
        ‖scalar‖^2*((max 1 b)^N*((actualAllocations s.pools C).card:ℝ)/C.absNorm)*(Cs^N)^2 := by
    unfold unevenAllocationWeight
    dsimp only
    split_ifs
    · exact mul_le_mul_of_nonneg_left (hf B) (by positivity)
    · positivity
  calc
    _≤∑_B : actualAllocations s.pools C,
        ‖scalar‖^2*((max 1 b)^N*((actualAllocations s.pools C).card:ℝ)/C.absNorm)*(Cs^N)^2 :=
      Finset.sum_le_sum (fun B _=> hp B)
    _=((actualAllocations s.pools C).card:ℝ)^2*
        (‖scalar‖^2*(max 1 b)^N*(Cs^N)^2/C.absNorm) := by simp;ring
    _≤(D^2*(C.absNorm:ℝ)^ε)*(‖scalar‖^2*(max 1 b)^N*(Cs^N)^2/C.absNorm) :=
      mul_le_mul_of_nonneg_right hc₂ (by positivity)
    _=_ := by rw [Real.rpow_sub hnorm,Real.rpow_one];ring


end
end OAI.SevenEighths.UnevenSelection
end

/- Original module: Candidate.Uneven.SelectionCost. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.UnevenSelection
noncomputable section
open OAI.SevenEighths.TargetHigh830
open OAI.SevenEighths.Target830.Source.Uneven
open Cycle63InitialMass Target830.Source
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentPrimeElements
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationErrorEnergy
open CenteredMomentGaussNormalization CenteredMomentSectorLocalization
open CenteredMomentAmplifiedRetainedRadius RayFourExpansion
local notation "O" => HeckeFamily.O
local instance geometryCostSelectionDecidable {ι : Type*} : DecidableEq ι := Classical.decEq _

/-- First common-allocation mass is paid with its literal column scalar.
The cost can be the complete extracted source, with all prime/ray sums
still inside it. Only allocations with nonzero frozen coefficient are selected. -/
theorem actual_geometry_weighted_cost_selection (N : ℕ)(Cs b ε : ℝ)
    (hCs : 1≤ Cs)(hε : 0<ε) :
    ∃D : ℝ,0< D ∧ ∀{ι : Type*}[Fintype ι][DecidableEq ι](s : Input ι),
      Fintype.card ι≤ N → (∀i,s.M i≤ Cs) →
      ∀(reflected : Bool)(R seed : Ideal O)(K Z ξ M A : ℝ)
        (hK : 0< K)(key : ℤ×(Fin 5→ℤ))
        (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
        (rows : Finset (FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)))
        (E : ℝ),
      let C := fun j : rows=> geometryColumnIdeal reflected s R seed K Z ξ hK key j.val
      let w := fun j : rows=> unevenAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j.val
      let mass := fun j : rows=>‖unevenColumnScalar reflected s R seed K Z ξ M A hK key weight j.val‖^2*
        ((C j).absNorm:ℝ)^(ε-1)
      ∀cost : (j : rows)→actualAllocations s.pools (C j)→ℝ,
      (∀j B,0≤ cost j B) → (∀j,C j≠0) →
      (∀S : Finset rows,∀pick : (j : S)→actualAllocations s.pools (C j.val),
        (∀j,frozenCoefficient (pick j).val (C j.val) R s.ν s.W s.P≠0) →
        (∑j : S,mass j.val*cost j.val (pick j))≤ E) →
      (∑j : rows,∑B : actualAllocations s.pools (C j),w j B*cost j B)≤ D*E := by
  obtain ⟨D,hD,hmass⟩ := actual_geometry_allocation_mass N Cs b ε hCs hε
  refine ⟨D,hD,?_⟩
  intro ι _ _ s hn hM reflected R seed K Z ξ M A hK key weight rows E C w mass cost hc hC hjoint
  apply joint_variable_mass_selection w cost mass D E hD.le
    (fun j B=> unevenAllocationWeight_nonneg reflected s R seed K Z ξ M A hK key weight N b j.val B)
    hc (fun j=> mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · intro j
    simpa only [mass,mul_assoc] using hmass s hn hM reflected R seed K Z ξ M A hK key weight j.val (hC j)
  · intro S pick hne
    apply hjoint S pick
    intro j hf
    apply hne j
    simp only [w,unevenAllocationWeight]
    dsimp only [C] at hf
    simp only [hf,ne_eq,not_true_eq_false,ite_false]

/-- Full first-label selection for a nonnegative actual allocation cost.
Only the proved dyadic/ray multiplicity is paid; ideal labels and residual
projectors remain injectively indexed inside the selected joint sum. -/
theorem actual_geometry_weighted_selected_cost {ι : Type*}[Fintype ι][DecidableEq ι]
    (N : ℕ)(Cs b ε Amax Dmax B ξ : ℝ)
    (hCs : 1≤ Cs)(hε : 0<ε)(hA : 0≤ Amax)(hD : 0≤ Dmax)(hB : 0≤ B)(hξ : 0≤ξ) :
    ∃K₀ : ℝ,0< K₀ ∧ ∀ᶠZ : ℝ in atTop,1≤ Z ∧
      ∀(s : Input ι),Fintype.card ι≤ N → (∀i,s.M i≤ Cs) →
      ∀(reflected : Bool)(R seed : Ideal O)(K M A : ℝ)
        (hK : 0< K)(key : ℤ×(Fin 5→ℤ))
        (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ),
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 →
      0< sourceRadius s → sourceRadius s≤ Z^B → volume s≤ Z^Amax → K⁻¹≤ Z^Dmax →
      ∀(rows : Finset (FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))) (E : ℝ),
      let C := fun j : rows=> geometryColumnIdeal reflected s R seed K Z ξ hK key j.val
      let w := fun j : rows=> unevenAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j.val
      let mass := fun j : rows=>‖unevenColumnScalar reflected s R seed K Z ξ M A hK key weight j.val‖^2*
        ((C j).absNorm:ℝ)^(ε-1)
      ∀cost : (j : rows)→actualAllocations s.pools (C j)→ℝ,
      (∀j B,0≤ cost j B) → (∀j,C j≠0) →
      (∀{Label : Type}[Fintype Label](column : Label → rows),
        Function.Injective (fun j=>(geometryFirstLabel s R seed K Z ξ hK key (column j).val,
          (column j).val.2.1.val)) →
        ∀alloc : (j : Label)→actualAllocations s.pools (C (column j)),
        (∀j,frozenCoefficient (alloc j).val (C (column j)) R s.ν s.W s.P≠0) →
        (∑j : Label,mass (column j)*cost (column j) (alloc j))≤ E) →
      (∑j : rows,∑alloc : actualAllocations s.pools (C j),w j alloc*cost j alloc)≤
        (K₀*Z^ε)*E := by
  obtain ⟨D,hDmass,hmass⟩ := actual_geometry_weighted_cost_selection N Cs b ε hCs hε
  obtain ⟨F,hF,hcolumns⟩ := actual_first_selected_column_budget_indexed (ι:=ι)
    Amax Dmax B ξ ε hA hD hB hξ hε
  refine ⟨D*F,mul_pos hDmass hF,?_⟩
  filter_upwards [hcolumns] with Z hz
  refine ⟨hz.1,?_⟩
  intro s hn hM reflected R seed K M A hK key weight hseed hz₁ hz₂ hsource hsourcecap hV hKi
    rows E C w mass cost hc hC hselected
  have hh := hmass s hn hM reflected R seed K Z ξ M A hK key weight
    rows ((F*Z^ε)*E) cost hc hC (by
      intro S alloc halloc
      apply hz.2 s R seed K hK key hseed hz₁ hz₂ hsource hsourcecap hV hKi
        (fun j : rows=> j.val) Subtype.val_injective S
        (fun j=> mass j.val*cost j.val (alloc j)) E
        (fun j=> mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          (hc j.val (alloc j)))
      intro chosen hchosen
      have hinj : Function.Injective (fun j=>
          (geometryFirstLabel s R seed K Z ξ hK key (chosen j).val.val,
            (chosen j).val.val.2.1.val)) := by
        intro j k he
        apply Subtype.ext
        exact (hchosen j).symm.trans (he.trans (hchosen k))
      exact hselected (fun j=>(chosen j).val) hinj
        (fun j=> alloc (chosen j)) (fun j=> halloc (chosen j)))
  apply hh.trans_eq
  ring

end
end OAI.SevenEighths.UnevenSelection
end

/- Original module: Candidate.Uneven.SelectionSelectedCost. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.UnevenSelection
noncomputable section
open OAI.SevenEighths.TargetHigh830
open OAI.SevenEighths.Target830.Source.Uneven
open Cycle63InitialMass Target830.Source
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceLiveColumn CenteredMomentCommonPairedSource
open CenteredMomentSecondEnergySplit CenteredMomentSectorLocalization
open CenteredMomentSecondLiveBlock CenteredMomentSecondCanonical CenteredMomentSourceRow
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentSourceMass CenteredMomentCommonAllocationSum
open CenteredMomentSecondInputCapacitySource CenteredMomentOriginalCommonHarmonic
open CenteredMomentCommonWindowColumn CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O
local instance mainSelectedSumDecidable {α : Type*} [DecidableEq α] :
    DecidableEq (α⊕Fin 2) := Classical.decEq _

/-- The literal original-nonzero main family is paid by complete selected
first-allocation costs. The remaining premise is precisely the selected
analytic family estimate; there is no independent label-count loss. -/
theorem actual_geometry_main_selected_cost {α : Type*} [Fintype α] [DecidableEq α]
    (N : ℕ) (Cs b ε Amax Dmax B ξ slotlo plainlo : ℝ)
    (hCs : 1≤ Cs) (hε : 0<ε) (hA : 0≤ Amax) (hD : 0≤ Dmax)
    (hB : 0≤ B) (hξ : 0≤ξ) (hslot : 0< slotlo) (hplain : 0< plainlo) :
    ∃K₀ : ℝ,0< K₀ ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1< Z,
      ∀(reflected : Bool)(s : Input α)(R seed : Ideal O)(Mrow amp reserve t Mprice Aprice : ℝ),
      Fintype.card α≤ N → (∀i,s.M i≤ Cs) → Squarefree seed →
      ∀(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0),
      0< sourceRadius s → sourceRadius s≤ Z^B → volume s≤ Z^Amax → (Z^Mrow)⁻¹≤ Z^Dmax →
      slotlo≤ s.lower → (∀x,s.W₁ x≠0→plainlo≤ x) → (∀x,s.W₂ x≠0→plainlo≤ x) →
      ∀(key : ℤ×(Fin 5→ℤ))
        (weight : Cycle63JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ)
        (χ : RayCharacter)(Q : Ideal O)(m : O)(W : 𝓢(ℝ,ℂ))(second : Bool)(t₀ u E : ℝ),
      let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
      let rows := firstLiveColumns (geometryFirstSource s R seed (Z^Mrow) Z ξ hK key) (fun _=> logAnnulus)
      let C := fun j : rows=> geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ hK key j.val
      let mass := fun j : rows=>‖unevenColumnScalar reflected s R seed (Z^Mrow) Z ξ Mprice Aprice hK key weight j.val‖^2*
        ((C j).absNorm:ℝ)^(ε-1)
      (∀{Label : Type}[Fintype Label](column : Label → rows),
        Function.Injective (fun j=>(geometryFirstLabel s R seed (Z^Mrow) Z ξ hK key (column j).val,
          (column j).val.2.1.val)) →
        ∀alloc : (j : Label)→actualAllocations s.pools (C (column j)),
        (∀j,frozenCoefficient (alloc j).val (C (column j)) R s.ν s.W s.P≠0) →
        (∑j : Label,mass (column j)*geometryMainFirstCost reflected s R seed Z Mrow amp ξ reserve b t N hZ key
          hz₁ hz₂ χ Q m slotlo plainlo second t₀ u ⟨column j,alloc j⟩)≤ E) →
      let datum := fun j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂=>
        geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ χ Q m j.val
      let w := fun j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂=>
        unevenMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mprice Aprice weight j.val
      secondNormalizedSum second datum (secondEffectiveWeight (fun j=>(datum j).block) w W) t₀ u≤
        (K₀*Z^ε)*E := by
  obtain ⟨K₀,hK₀,hselection⟩ := actual_geometry_weighted_selected_cost (ι:=α)
    N Cs b ε Amax Dmax B ξ hCs hε hA hD hB hξ
  refine ⟨K₀,hK₀,?_⟩
  filter_upwards [hselection] with Z hsel
  intro hZ reflected s R seed Mrow amp reserve t Mprice Aprice hn hM hseed hz₁ hz₂
    hsource hcap hV hKi hlo hW₁ hW₂ key weight χ Q m W second t₀ u E hK rows C mass hselected datum w
  apply (actual_geometry_main_first_cost_uniform reflected s R seed Z Mrow amp ξ reserve b t N hZ key
    hz₁ hz₂ χ Q m Mprice Aprice slotlo plainlo hslot hplain weight hn hlo hW₁ hW₂ W second t₀ u).trans
  exact hsel.2 s hn hM reflected R seed (Z^Mrow) Mprice Aprice hK key weight hseed hz₁ hz₂
    hsource hcap hV hKi rows E
    (fun j alloc=> geometryMainFirstCost reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      hz₁ hz₂ χ Q m slotlo plainlo second t₀ u ⟨j,alloc⟩)
    (fun j alloc=> geometry_main_first_cost_nonneg reflected s R seed Z Mrow amp ξ reserve b t N hZ key
      hz₁ hz₂ χ Q m slotlo plainlo hslot hplain second t₀ u ⟨j,alloc⟩)
    (by
      intro j
      cases reflected
      · exact (geometryFirstSource s R seed (Z^Mrow) Z ξ hK key j.val.1).hC.1
      · exact (geometryFirstSource s R seed (Z^Mrow) Z ξ hK key j.val.1).hD.1)
    hselected

end
end OAI.SevenEighths.UnevenSelection
end

/- Original module: Candidate.Uneven.SelectionPhysical. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.UnevenSelection
noncomputable section
open OAI.SevenEighths.TargetHigh830
open OAI.SevenEighths.Target830.Source.Uneven
open Cycle63InitialMass Target830.Source
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceLiveColumn CenteredMomentCommonPairedSource
open CenteredMomentSecondEnergySplit CenteredMomentSectorLocalization
open CenteredMomentSecondLiveBlock CenteredMomentSecondCanonical CenteredMomentSourceRow
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentSourceMass CenteredMomentCommonAllocationSum
open CenteredMomentSecondInputCapacitySource CenteredMomentOriginalCommonHarmonic
open CenteredMomentCommonWindowColumn CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O
local instance mainPhysicalSelectionSumDecidable {α : Type*} [DecidableEq α] :
    DecidableEq (α⊕Fin 2) := Classical.decEq _

/-- Physical phase-weight specialization. Its selected mass is exactly the
mass used by the genuine low, high and coarse analytic family bounds. -/
theorem actual_geometry_main_physical_selection {α : Type} [Fintype α] [DecidableEq α]
    (N : ℕ) (Cs b ε Amax Dmax B ξ slotlo plainlo : ℝ)
    (hCs : 1≤ Cs) (hε : 0<ε) (hA : 0≤ Amax) (hD : 0≤ Dmax)
    (hB : 0≤ B) (hξ : 0≤ξ) (hslot : 0< slotlo) (hplain : 0< plainlo) :
    ∃K₀ : ℝ,0< K₀ ∧ ∀ᶠ Z : ℝ in atTop,∀hZ : 1< Z,
      ∀(reflected : Bool)(s : Input α)(R seed : Ideal O)(Mrow amp reserve t : ℝ),
      Fintype.card α≤ N → (∀i,s.M i≤ Cs) → Squarefree seed →
      ∀(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0),
      0< sourceRadius s → sourceRadius s≤ Z^B → volume s≤ Z^Amax → (Z^Mrow)⁻¹≤ Z^Dmax →
      slotlo ≤ s.lower → (∀x,s.W₁ x≠0→plainlo≤ x) → (∀x,s.W₂ x≠0→plainlo≤ x) →
      ∀(key : ℤ×(Fin 5→ℤ))
        (Ψ : 𝓢(ℝ,ℂ))
        (χ : RayCharacter)(Q : Ideal O)(m : O)(W : 𝓢(ℝ,ℂ))(second : Bool)(t₀ u E : ℝ),
      let hK := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
      let rows := firstLiveColumns (geometryFirstSource s R seed (Z^Mrow) Z ξ hK key) (fun _=> logAnnulus)
      let C := fun j : rows=> geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ hK key j.val
      let mass := fun j : rows=> unevenFirstHighMass reflected s R seed Ψ Mrow Z ξ ε hK key j.val
      (∀{Label : Type}[Fintype Label](column : Label → rows),
        Function.Injective (fun j=>(geometryFirstLabel s R seed (Z^Mrow) Z ξ hK key (column j).val,
          (column j).val.2.1.val)) →
        ∀alloc : (j : Label)→actualAllocations s.pools (C (column j)),
        (∀j,frozenCoefficient (alloc j).val (C (column j)) R s.ν s.W s.P≠0) →
        (∑j : Label,mass (column j)*geometryMainFirstCost reflected s R seed Z Mrow amp ξ reserve b t N hZ key
          hz₁ hz₂ χ Q m slotlo plainlo second t₀ u ⟨column j,alloc j⟩)≤ E) →
      let datum := fun j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂=>
        geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ χ Q m j.val
      let w := fun j : geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂=>
        unevenMainSecondWeight reflected s R seed Z Mrow amp ξ reserve b t N hZ key Mrow (Real.logb Z (volume s.toData))
          (fun q=> normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z ξ q)) j.val
      secondNormalizedSum second datum (secondEffectiveWeight (fun j=>(datum j).block) w W) t₀ u≤
        (K₀*Z^ε)*E := by
  obtain ⟨K₀,hK₀,hselection⟩ := actual_geometry_main_selected_cost (α:=α)
    N Cs b ε Amax Dmax B ξ slotlo plainlo hCs hε hA hD hB hξ hslot hplain
  refine ⟨K₀,hK₀,?_⟩
  filter_upwards [hselection] with Z hsel
  intro hZ reflected s R seed Mrow amp reserve t hn hM hseed hz₁ hz₂
    hsource hcap hV hKi hlo hW₁ hW₂ key Ψ χ Q m W second t₀ u E hK rows C mass hselected datum w
  apply hsel hZ reflected s R seed Mrow amp reserve t Mrow (Real.logb Z (volume s.toData))
    hn hM hseed hz₁ hz₂ hsource hcap hV hKi hlo hW₁ hW₂ key
    (fun q=> normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z ξ q)) χ Q m W second t₀ u E
  intro Label _ column hi alloc ha
  simpa only [mass,uneven_first_high_mass_formula reflected s R seed Ψ Mrow Z ξ ε hK (zero_lt_one.trans hZ) key] using (hselected column hi alloc ha)

end
end OAI.SevenEighths.UnevenSelection
end

/- Original module: Candidate.Uneven.SelectionAffine. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.UnevenSelection
noncomputable section
open OAI.SevenEighths.TargetHigh830
open OAI.SevenEighths.Target830.Source.Uneven
open OAI.SevenEighths.Cycle63InitialMass
open OAI.SevenEighths.Target830.Source
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceLiveColumn CenteredMomentCommonPairedSource
open CenteredMomentSecondEnergySplit CenteredMomentSectorLocalization
open CenteredMomentSecondLiveBlock CenteredMomentSecondCanonical CenteredMomentSourceRow
open CenteredMomentSecondRetainedAggregate CenteredMomentSecondBlockAggregate
open CenteredMomentSourceMass CenteredMomentCommonAllocationSum
open CenteredMomentSecondInputCapacitySource CenteredMomentOriginalCommonHarmonic
open CenteredMomentCommonWindowColumn CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O
local instance affinePhysicalSelectionSumDecidable {ι : Type*} [DecidableEq ι] :
    DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Only the card field uses the ambient cap in the saved affine source record. -/
theorem geometry_affine_source_gates_actual_card {ι : Type*} [Fintype ι]
    (s : Input ι)(p : Profiles (1/4) (9/4))(N : ℕ)(Cs Z : ℝ)
    (caps : GeometryAffineExceptionalSourceGates s p N Cs Z) :
    GeometryAffineExceptionalSourceGates s p (Fintype.card ι) Cs Z where
  card := le_rfl
  controls := caps.controls
  lower := caps.lower
  lo := caps.lo
  hi := caps.hi
  endpoints := caps.endpoints
  scales := caps.scales
  profile₁ := caps.profile₁
  profile₂ := caps.profile₂
  zero₁ := caps.zero₁
  zero₂ := caps.zero₂
  support₁ := caps.support₁
  support₂ := caps.support₂
  volume := caps.volume
  volumeLog := caps.volumeLog
  sourcePositive := caps.sourcePositive
  sourceCap := caps.sourceCap
  poolCap := caps.poolCap
  plain₁ := caps.plain₁
  plain₂ := caps.plain₂
  plain₃ := caps.plain₃
  plain₄ := caps.plain₄

/-- The supported allocation is selected before the complete second cost.
The original full-block filter and actual-cardinality Fourier cutoff remain literal. -/
def GeometryAffinePhysicalSelectionSpec {ι : Type} [Fintype ι] [DecidableEq ι]
    (Cs ε ξ K Z : ℝ) : Prop :=
  ∀(hZ : 1< Z)(reflected : Bool)(s : Input ι)(p : Profiles (1/4) (9/4)),
    GeometryAffineExceptionalSourceGates s p (Fintype.card ι) Cs Z →
  ∀(amp reserve height : ℝ)(key : ℤ×(Fin 5→ℤ))(Ψ : 𝓢(ℝ,ℂ))
    (χ : RayCharacter)(Q : Ideal O)(m : O)(W : 𝓢(ℝ,ℂ))(second : Bool)(t₀ u E : ℝ),
  ∀(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0),
  let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
  let rows:=firstLiveColumns (geometryFirstSource s 1 1 (Z^(1:ℝ)) Z ξ hK key) (fun _=> logAnnulus)
  let C:=fun j : rows=> geometryColumnIdeal reflected s 1 1 (Z^(1:ℝ)) Z ξ hK key j.val
  let mass:=fun j : rows=> unevenFirstHighMass reflected s 1 1 Ψ 1 Z ξ ε hK key j.val
  (∀{Label : Type}[Fintype Label](column : Label → rows),
    Function.Injective (fun j=>(geometryFirstLabel s 1 1 (Z^(1:ℝ)) Z ξ hK key (column j).val,
      (column j).val.2.1.val)) →
    ∀alloc : (j : Label)→actualAllocations s.pools (C (column j)),
    (∀j,frozenCoefficient (alloc j).val (C (column j)) 1 s.ν s.W s.P≠0) →
    (∑j : Label,mass (column j)*geometryMainFirstCost reflected s 1 1 Z 1 amp ξ reserve
      (9/4) height (Fintype.card ι) hZ key hz₁ hz₂ χ Q m 1 (1/4) second t₀ u
      ⟨column j,alloc j⟩)≤ E) →
  let selected:=geometryMainNonzeroBlocks reflected s 1 1 Z 1 amp ξ reserve (9/4) height
    (Fintype.card ι) hZ key hz₁ hz₂
  let datum:=fun j : selected=> geometryMainOrdinaryDatum reflected s 1 1 Z 1 amp ξ reserve
    (9/4) height (Fintype.card ι) hZ key hz₁ hz₂ χ Q m j.val
  let w:=fun j : selected=> unevenMainSecondWeight reflected s 1 1 Z 1 amp ξ reserve
    (9/4) height (Fintype.card ι) hZ key 1 (Real.logb Z (volume s.toData))
    (fun q=> normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z ξ q)) j.val
  secondNormalizedSum second datum (secondEffectiveWeight (fun j=>(datum j).block) w W) t₀ u≤
    (K*Z^ε)*E

/-- All constants and thresholds precede the live subset and source.
The caps record supplies every physical source gate of the selection theorem. -/
theorem uniform_actual_affine_physical_selection {α : Type} [Fintype α] [DecidableEq α]
    (Cs ε ξ : ℝ)(hCs : 1≤ Cs)(hε : 0<ε)(hξ : 0≤ξ) :
    ∃K : ℝ,0< K ∧ ∀ᶠZ : ℝ in atTop,∀T : Finset α,
      GeometryAffinePhysicalSelectionSpec (ι:=T) Cs ε ξ K Z := by
  have data (T : Finset α) := actual_geometry_main_physical_selection (α:=T)
    (Fintype.card T) Cs (9/4) ε 2 2 3 ξ 1 (1/4)
    hCs hε (by norm_num) (by norm_num) (by norm_num) hξ (by norm_num) (by norm_num)
  choose K hK hpaid using data
  let total:=1+∑T : Finset α,K T
  have hn : ∀T : Finset α,0≤ K T := fun T=>(hK T).le
  have ht : 0< total := by
    have hh:=Finset.sum_nonneg (s:=Finset.univ) (fun T _=> hn T)
    dsimp only [total]
    linarith
  have hle (T : Finset α) : K T≤ total := by
    have hh:=Finset.single_le_sum (fun T (_ : T∈(Finset.univ:Finset (Finset α)))=> hn T)
      (Finset.mem_univ T)
    dsimp only [total]
    linarith
  refine ⟨total,ht,?_⟩
  filter_upwards [Filter.eventually_all.mpr hpaid] with Z hz
  intro T
  unfold GeometryAffinePhysicalSelectionSpec
  intro hZ reflected s p caps amp reserve height key Ψ χ Q m W second t₀ u E hz₁ hz₂
    hKfirst rows C mass hselected selected datum w
  have hKi : (Z^(1:ℝ))⁻¹≤ Z^(2:ℝ) := by
    rw [Real.rpow_one]
    exact (inv_le_one_of_one_le₀ hZ.le).trans (Real.one_le_rpow hZ.le (by norm_num))
  have hlo : (1:ℝ)≤ s.lower := le_of_eq caps.lower.symm
  have hbound := hz T hZ reflected s 1 1 1 amp reserve height caps.card caps.controls
    squarefree_one hz₁ hz₂ caps.sourcePositive caps.sourceCap caps.volume hKi hlo
    caps.support₁ caps.support₂ key Ψ χ Q m W second t₀ u E hselected
  have hE : 0≤ E := by
    have hh:=hselected (fun j : Fin 0=> Fin.elim0 j)
      (fun j k _=> Fin.elim0 j) (fun j=> Fin.elim0 j) (fun j=> Fin.elim0 j)
    simpa using hh
  apply hbound.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hle T) (Real.rpow_nonneg (zero_lt_one.trans hZ).le ε)) hE

end
end OAI.SevenEighths.UnevenSelection
end
