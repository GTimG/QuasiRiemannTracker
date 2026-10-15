/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle62.Physical.InitialMass.GeometryWeightedSelection

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve Cycle62Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentPrimeElements
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationErrorEnergy
open CenteredMomentGaussNormalization CenteredMomentSectorLocalization
open CenteredMomentAmplifiedRetainedRadius RayFourExpansion
local notation "O" => HeckeFamily.O
local instance geometryCostSelectionDecidable {ι : Type*} : DecidableEq ι := Classical.decEq _

/-- Every literal extracted branch is nonnegative before any source split. -/
theorem actual_error_sources_nonneg {ι : Type*} [Fintype ι]
    (s : Input ι) (g : FirstBranchGeometry) (Z sigma Csec ξ reserve : ℝ)
    (hZ : 0<Z) (P : Finset (Ideal O))
    (τ : elementPool P→Fin 3→RayCharacter→Character) :
    0≤actualErrorSources s g Z sigma Csec ξ reserve P τ := by
  unfold actualErrorSources
  apply Finset.sum_nonneg
  intro p _
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg
  · exact mul_nonneg (by positivity) (localErrorCost_nonneg p (errorIndex i))
  · apply Finset.sum_nonneg
    intro χ _
    apply Finset.sum_nonneg
    intro B _
    unfold childNormalizedGaussSource normalizedGaussSource
    exact div_nonneg (sourceGaussEnergy_nonneg _ _ _ _ _
      (Real.rpow_pos_of_pos hZ _) (fun _=>ballProfile_nonneg _)) (volume_pos _).le

/-- First common-allocation mass is paid with its literal column scalar.
The cost can be the complete extracted source, with all prime/ray sums
still inside it. Only allocations with nonzero frozen coefficient are selected. -/
theorem actual_geometry_weighted_cost_selection (N : ℕ)(Cs b ε : ℝ)
    (hCs : 1≤Cs)(hε : 0<ε) :
    ∃D : ℝ,0<D ∧ ∀{ι : Type*}[Fintype ι][DecidableEq ι](s : Input ι),
      Fintype.card ι≤N → (∀i,s.M i≤Cs) →
      ∀(reflected : Bool)(R seed : Ideal O)(K Z ξ M A : ℝ)
        (hK : 0<K)(key : ℤ×(Fin 5→ℤ))
        (weight : Cycle62JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
        (rows : Finset (FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)))
        (E : ℝ),
      let C := fun j : rows=>geometryColumnIdeal reflected s R seed K Z ξ hK key j.val
      let w := fun j : rows=>geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j.val
      let mass := fun j : rows=>‖geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j.val‖^2*
        ((C j).absNorm:ℝ)^(ε-1)
      ∀cost : (j : rows)→actualAllocations s.pools (C j)→ℝ,
      (∀j B,0≤cost j B) → (∀j,C j≠0) →
      (∀S : Finset rows,∀pick : (j : S)→actualAllocations s.pools (C j.val),
        (∀j,frozenCoefficient (pick j).val (C j.val) R s.ν s.W s.P≠0) →
        (∑j : S,mass j.val*cost j.val (pick j))≤E) →
      (∑j : rows,∑B : actualAllocations s.pools (C j),w j B*cost j B)≤D*E := by
  obtain ⟨D,hD,hmass⟩ := actual_geometry_allocation_mass N Cs b ε hCs hε
  refine ⟨D,hD,?_⟩
  intro ι _ _ s hn hM reflected R seed K Z ξ M A hK key weight rows E C w mass cost hc hC hjoint
  apply joint_variable_mass_selection w cost mass D E hD.le
    (fun j B=>geometryAllocationWeight_nonneg reflected s R seed K Z ξ M A hK key weight N b j.val B)
    hc (fun j=>mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · intro j
    simpa only [mass,mul_assoc] using hmass s hn hM reflected R seed K Z ξ M A hK key weight j.val (hC j)
  · intro S pick hne
    apply hjoint S pick
    intro j hf
    apply hne j
    simp only [w,geometryAllocationWeight]
    dsimp only [C] at hf
    simp only [hf,ne_eq,not_true_eq_false,ite_false]

/-- Full first-label selection for a nonnegative actual allocation cost.
Only the proved dyadic/ray multiplicity is paid; ideal labels and residual
projectors remain injectively indexed inside the selected joint sum. -/
theorem actual_geometry_weighted_selected_cost {ι : Type*}[Fintype ι][DecidableEq ι]
    (N : ℕ)(Cs b ε Amax Dmax B ξ : ℝ)
    (hCs : 1≤Cs)(hε : 0<ε)(hA : 0≤Amax)(hD : 0≤Dmax)(hB : 0≤B)(hξ : 0≤ξ) :
    ∃K₀ : ℝ,0<K₀ ∧ ∀ᶠZ : ℝ in atTop,1≤Z ∧
      ∀(s : Input ι),Fintype.card ι≤N → (∀i,s.M i≤Cs) →
      ∀(reflected : Bool)(R seed : Ideal O)(K M A : ℝ)
        (hK : 0<K)(key : ℤ×(Fin 5→ℤ))
        (weight : Cycle62JointSource.SourceCoordinate s R seed K Z ξ→ℂ),
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 →
      0<sourceRadius s → sourceRadius s≤Z^B → volume s≤Z^Amax → K⁻¹≤Z^Dmax →
      ∀(rows : Finset (FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))) (E : ℝ),
      let C := fun j : rows=>geometryColumnIdeal reflected s R seed K Z ξ hK key j.val
      let w := fun j : rows=>geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j.val
      let mass := fun j : rows=>‖geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j.val‖^2*
        ((C j).absNorm:ℝ)^(ε-1)
      ∀cost : (j : rows)→actualAllocations s.pools (C j)→ℝ,
      (∀j B,0≤cost j B) → (∀j,C j≠0) →
      (∀{Label : Type}[Fintype Label](column : Label → rows),
        Function.Injective (fun j=>(geometryFirstLabel s R seed K Z ξ hK key (column j).val,
          (column j).val.2.1.val)) →
        ∀alloc : (j : Label)→actualAllocations s.pools (C (column j)),
        (∀j,frozenCoefficient (alloc j).val (C (column j)) R s.ν s.W s.P≠0) →
        (∑j : Label,mass (column j)*cost (column j) (alloc j))≤E) →
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
        (fun j : rows=>j.val) Subtype.val_injective S
        (fun j=>mass j.val*cost j.val (alloc j)) E
        (fun j=>mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          (hc j.val (alloc j)))
      intro chosen hchosen
      have hinj : Function.Injective (fun j=>
          (geometryFirstLabel s R seed K Z ξ hK key (chosen j).val.val,
            (chosen j).val.val.2.1.val)) := by
        intro j k he
        apply Subtype.ext
        exact (hchosen j).symm.trans (he.trans (hchosen k))
      exact hselected (fun j=>(chosen j).val) hinj
        (fun j=>alloc (chosen j)) (fun j=>halloc (chosen j)))
  apply hh.trans_eq
  ring

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_error_sources_nonneg
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_weighted_cost_selection
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_geometry_weighted_selected_cost
