import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.GeometrySelectedSources

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic
local notation "O" => HeckeFamily.O

/-- Variable label mass stays inside the selected sum, including labels
whose mass vanishes. No maximum over the varying masses is introduced. -/
theorem joint_variable_mass_selection {Label : Type*} [Fintype Label]
    {β : Label→Type*} [∀l,Fintype (β l)] (weight cost : (l : Label)→β l→ℝ)
    (mass : Label→ℝ) (W E : ℝ) (hW : 0≤W)
    (hw : ∀l a,0≤weight l a) (hc : ∀l a,0≤cost l a)
    (hm : ∀l,0≤mass l) (hmass : ∀l,∑a,weight l a≤W*mass l)
    (hjoint : ∀S : Finset Label,∀pick : (l : S)→β l.val,
      (∀l,weight l.val (pick l)≠0) →
      (∑l : S,mass l.val*cost l.val (pick l))≤E) :
    (∑l,∑a,weight l a*cost l a)≤W*E := by
  have hzero (l : Label)(h : mass l=0)(a : β l) : weight l a=0 := by
    have ht := (Finset.single_le_sum (fun a _=>hw l a) (Finset.mem_univ a)).trans (hmass l)
    rw [h,mul_zero] at ht
    exact le_antisymm ht (hw l a)
  have hh := joint_supported_weighted_selection
    (fun l a=>weight l a/mass l) (fun l a=>mass l*cost l a) W E hW
    (fun l a=>div_nonneg (hw l a) (hm l)) (fun l a=>mul_nonneg (hm l) (hc l a))
    (by
      intro l
      by_cases hz : mass l=0
      · simp only [hz,div_zero,Finset.sum_const_zero]; exact hW
      · rw [←Finset.sum_div]
        exact (div_le_iff₀ (lt_of_le_of_ne (hm l) (Ne.symm hz))).mpr (hmass l))
    (by
      intro S pick hne
      exact hjoint S pick (fun l hw0=>hne l (by simp [hw0])))
  have heq (l : Label)(a : β l) :
      weight l a/mass l*(mass l*cost l a)=weight l a*cost l a := by
    by_cases hz : mass l=0
    · simp [hz,hzero l hz a]
    · field_simp
  simpa only [heq] using hh

/-- Supported first common allocations are selected while their literal
column scalar and inverse-ideal mass remain inside the joint source sum. -/
theorem actual_geometry_weighted_main_selection (N : ℕ)(Cs b ε : ℝ)
    (hCs : 1≤Cs)(hε : 0<ε) :
    ∃D : ℝ,0<D ∧ ∀{ι : Type*}[Fintype ι][DecidableEq ι](s : Input ι),
      Fintype.card ι≤N → (∀i,s.M i≤Cs) →
      ∀(reflected : Bool)(R seed : Ideal O)(K Z ξ M A sigma reserve t : ℝ)
        (hK : 0<K)(hZ : 0<Z)(key : ℤ×(Fin 5→ℤ))
        (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
        (rows : Finset (FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)))
        (E : ℝ),
      let C := fun j : rows=>geometryColumnIdeal reflected s R seed K Z ξ hK key j.val
      let χ := fun j : rows=>geometryColumnCharacter reflected s R seed K Z ξ hK key j.val
      let g := fun j : rows=>geometryBranch reflected s R seed K Z ξ hK key j.val
      let w := fun j : rows=>geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j.val
      let mass := fun j : rows=>‖geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j.val‖^2*
        ((C j).absNorm:ℝ)^(ε-1)
      (∀j,C j≠0) →
      (∀S : Finset rows,∀pick : (j : S)→actualAllocations s.pools (C j.val),
        (∀j,frozenCoefficient (pick j).val (C j.val) R s.ν s.W s.P≠0) →
        (∑j : S,mass j.val*actualMainSource (child s (C j.val) R (pick j) (χ j.val) t)
          (g j.val) Z sigma 1 ξ reserve)≤E) →
      (∑j : rows,∑B : actualAllocations s.pools (C j),
        w j B*actualMainSource (child s (C j) R B (χ j) t) (g j) Z sigma 1 ξ reserve)≤D*E := by
  obtain ⟨D,hD,hmass⟩ := actual_geometry_allocation_mass N Cs b ε hCs hε
  refine ⟨D,hD,?_⟩
  intro ι _ _ s hn hM reflected R seed K Z ξ M A sigma reserve t hK hZ key weight rows E
    C χ g w mass hC hjoint
  apply joint_variable_mass_selection w
    (fun j B=>actualMainSource (child s (C j) R B (χ j) t) (g j) Z sigma 1 ξ reserve)
    mass D E hD.le
    (fun j B=>geometryAllocationWeight_nonneg reflected s R seed K Z ξ M A hK key weight N b j.val B)
    (fun j B=>actual_geometry_main_nonneg reflected s R seed K Z ξ sigma reserve hK hZ key j.val B t)
    (fun j=>mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · intro j
    simpa only [mass,mul_assoc] using hmass s hn hM reflected R seed K Z ξ M A hK key weight j.val (hC j)
  · intro S pick hne
    apply hjoint S pick
    intro j hf
    apply hne j
    simp only [w,geometryAllocationWeight]
    dsimp only [C] at hf
    simp only [hf,ne_eq,not_true_eq_false,ite_false]

/-- Select actual arithmetic-label/projector representatives while retaining
the varying normalized column mass inside the joint sum. -/
theorem actual_geometry_weighted_selected_main_budget {ι : Type*}[Fintype ι][DecidableEq ι]
    (N : ℕ)(Cs b ε Amax Dmax B ξ : ℝ)
    (hCs : 1≤Cs)(hε : 0<ε)(hA : 0≤Amax)(hD : 0≤Dmax)(hB : 0≤B)(hξ : 0≤ξ) :
    ∃K₀ : ℝ,0<K₀ ∧ ∀ᶠZ : ℝ in atTop,1≤Z ∧
      ∀(s : Input ι),Fintype.card ι≤N → (∀i,s.M i≤Cs) →
      ∀(reflected : Bool)(R seed : Ideal O)(K M A sigma reserve t : ℝ)
        (hK : 0<K)(key : ℤ×(Fin 5→ℤ))
        (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ),
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 →
      0<sourceRadius s → sourceRadius s≤Z^B → volume s≤Z^Amax → K⁻¹≤Z^Dmax →
      ∀(rows : Finset (FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)))
        (E : ℝ),
      let C := fun j : rows=>geometryColumnIdeal reflected s R seed K Z ξ hK key j.val
      let χ := fun j : rows=>geometryColumnCharacter reflected s R seed K Z ξ hK key j.val
      let g := fun j : rows=>geometryBranch reflected s R seed K Z ξ hK key j.val
      let w := fun j : rows=>geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j.val
      let mass := fun j : rows=>‖geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j.val‖^2*
        ((C j).absNorm:ℝ)^(ε-1)
      (∀j,C j≠0) →
      (∀{Label : Type}[Fintype Label](column : Label → rows),
        Function.Injective (fun j=>(geometryFirstLabel s R seed K Z ξ hK key (column j).val,
          (column j).val.2.1.val)) →
        ∀alloc : (j : Label)→actualAllocations s.pools (C (column j)),
        (∀j,frozenCoefficient (alloc j).val (C (column j)) R s.ν s.W s.P≠0) →
        (∑j : Label,mass (column j)*actualMainSource (child s (C (column j)) R (alloc j) (χ (column j)) t)
          (g (column j)) Z sigma 1 ξ reserve)≤E) →
      (∑j : rows,∑alloc : actualAllocations s.pools (C j),
        w j alloc*actualMainSource (child s (C j) R alloc (χ j) t) (g j) Z sigma 1 ξ reserve)≤
          (K₀*Z^ε)*E := by
  obtain ⟨D,hDmass,hmass⟩ := actual_geometry_weighted_main_selection N Cs b ε hCs hε
  obtain ⟨F,hF,hcolumns⟩ := actual_first_selected_column_budget_indexed (ι:=ι)
    Amax Dmax B ξ ε hA hD hB hξ hε
  refine ⟨D*F,mul_pos hDmass hF,?_⟩
  filter_upwards [hcolumns] with Z hz
  refine ⟨hz.1,?_⟩
  intro s hn hM reflected R seed K M A sigma reserve t hK key weight hseed hz₁ hz₂
    hsource hsourcecap hV hKi rows E C χ g w mass hC hselected
  have hZ : 0<Z := zero_lt_one.trans_le hz.1
  have hh := hmass s hn hM reflected R seed K Z ξ M A sigma reserve t hK hZ key weight
    rows ((F*Z^ε)*E) hC (by
      intro S alloc halloc
      apply hz.2 s R seed K hK key hseed hz₁ hz₂ hsource hsourcecap hV hKi
        (fun j : rows=>j.val) Subtype.val_injective S
        (fun j=>mass j.val*actualMainSource (child s (C j.val) R (alloc j) (χ j.val) t)
          (g j.val) Z sigma 1 ξ reserve) E
        (fun j=>mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          (actual_geometry_main_nonneg reflected s R seed K Z ξ sigma reserve hK hZ
            key j.val.val (alloc j) t))
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
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.joint_variable_mass_selection
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_weighted_main_selection

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_weighted_selected_main_budget
