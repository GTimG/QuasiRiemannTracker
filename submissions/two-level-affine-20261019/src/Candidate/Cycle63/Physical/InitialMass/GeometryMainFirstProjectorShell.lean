import Candidate.Cycle63.Physical.InitialMass.SecondProjectorShell

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily CenteredMomentWholeDivisorShell CenteredMomentSectorLocalization
open CenteredMomentSourceRow CenteredMomentCommonAllocationSum
open CenteredMomentCommonRadialData CenteredMomentLogDyadic CenteredMomentSourceLiveColumn

/-- Singleton sets retain the allocator attached to each selected column. -/
def selectedFirstProjectors {ι Label : Type*} [Fintype Label]
    {src : ι→FirstBlockSource} (column : Label→FirstColumnIndex src) : Finset (Ideal O) :=
  sharedProjectors (fun j=>{(column j).2.1.val})

abbrev SelectedFirstShell {ι Label : Type*} [Fintype Label]
    {src : ι→FirstBlockSource} (column : Label→FirstColumnIndex src) (n : ℤ) :=
  {j : Label // (column j).2.1.val∈shell (selectedFirstProjectors column) n}

lemma selected_first_projectors_eq_image {ι Label : Type*} [Fintype Label]
    {src : ι→FirstBlockSource} (column : Label→FirstColumnIndex src) :
    selectedFirstProjectors column=Finset.univ.image (fun j=>(column j).2.1.val) := by
  ext D
  simp [selectedFirstProjectors,sharedProjectors,eq_comm]

/-- Cost may include the original allocation, scalar, mass and complete
second-block cost; restriction neither changes nor duplicates them. -/
theorem selected_first_shell_sum {ι Label : Type*} [Fintype Label]
    {src : ι→FirstBlockSource} (column : Label→FirstColumnIndex src)
    (hs : ∀j,Squarefree (column j).2.1.val) (cost : Label→ℝ) :
    (∑j,cost j)=∑n∈selectedShells (selectedFirstProjectors column),
      ∑j : SelectedFirstShell column n,cost j.val := by
  have h:=shared_projector_shell_sum (fun j=>{(column j).2.1.val})
    (by
      intro j D hD
      have he : D=(column j).2.1.val:=Finset.mem_singleton.mp hD
      simpa only [he] using hs j)
    (fun j _=>cost j)
  simp only [Finset.sum_singleton,Finset.mem_singleton,Finset.sum_ite_eq'] at h
  change (∑j,cost j)=∑n∈selectedShells (selectedFirstProjectors column),
    ∑j,if (column j).2.1.val∈shell (selectedFirstProjectors column) n then cost j else 0 at h
  rw [h]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [←Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) cost

theorem selected_first_shell_gates {ι Label : Type*} [Fintype Label]
    {src : ι→FirstBlockSource} (column : Label→FirstColumnIndex src) (n : ℤ)
    (j : SelectedFirstShell column n) :
    Squarefree (column j.val).2.1.val ∧
      dyadicScale n≤((column j.val).2.1.val.absNorm:ℝ) ∧
      ((column j.val).2.1.val.absNorm:ℝ)<2*dyadicScale n := by
  have h:=shell_member_data (selectedFirstProjectors column) n _ j.property
  exact ⟨h.2.2.1,h.2.2.2.2⟩

/-- A modular per-shell estimate pays only the number of norm shells. -/
theorem selected_first_shell_payment {ι Label : Type*} [Fintype Label]
    {src : ι→FirstBlockSource} (column : Label→FirstColumnIndex src)
    (hs : ∀j,Squarefree (column j).2.1.val) (cost : Label→ℝ) (E C Z ε : ℝ)
    (hE : 0≤E)
    (hcard : ((selectedShells (selectedFirstProjectors column)).card:ℝ)≤C*Z^ε)
    (hbound : ∀n∈selectedShells (selectedFirstProjectors column),
      (∑j : SelectedFirstShell column n,cost j.val)≤E) :
    (∑j,cost j)≤C*Z^ε*E := by
  rw [selected_first_shell_sum column hs cost]
  calc
    _≤∑_n∈selectedShells (selectedFirstProjectors column),E :=
      Finset.sum_le_sum hbound
    _=((selectedShells (selectedFirstProjectors column)).card:ℝ)*E := by simp
    _≤C*Z^ε*E := mul_le_mul_of_nonneg_right hcard hE

/-- The stored-pool cap controls the common FIRST projector union, including
columns whose allocations have zero coefficient. -/
theorem actual_geometry_selected_first_projector_cap {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (s : Input α) (N : ℕ) (R seed : Ideal O) (K Z ξ U : ℝ) (hK : 0<K)
    (hN : Fintype.card α≤N) (hZ : 1≤Z) (hU : 0≤U)
    (hpool : ∀i I,I∈s.pools i→(I.absNorm:ℝ)≤Z^U)
    (bin : ℤ×(Fin 5→ℤ))
    (column : Label→FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin)) :
    ∀D∈selectedFirstProjectors column,(D.absNorm:ℝ)≤Z^(((N:ℝ)+2)*U) := by
  intro D hD
  rw [selected_first_projectors_eq_image] at hD
  obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hD
  exact actual_geometry_projector_cap s N R seed K Z ξ U hK hN hZ hU hpool bin (column j)

theorem actual_geometry_selected_first_shell_scale {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (s : Input α) (N : ℕ) (R seed : Ideal O) (K Z ξ U : ℝ) (hK : 0<K)
    (hN : Fintype.card α≤N) (hZ : 1≤Z) (hU : 0≤U)
    (hpool : ∀i I,I∈s.pools i→(I.absNorm:ℝ)≤Z^U)
    (bin : ℤ×(Fin 5→ℤ))
    (column : Label→FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (n : ℤ) (hn : n∈selectedShells (selectedFirstProjectors column)) :
    1≤dyadicScale n ∧ dyadicScale n≤Z^(((N:ℝ)+2)*U) := by
  exact selected_scale_bounds _ _
    (fun D hD _=>actual_geometry_selected_first_projector_cap s N R seed K Z ξ U hK
      hN hZ hU hpool bin column D hD) n hn

theorem eventual_actual_geometry_selected_first_shell_subpower (N : ℕ) (U ε : ℝ)
    (hU : 0≤U) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀{α Label : Type*}[Fintype α][DecidableEq α][Fintype Label]
        (s : Input α),Fintype.card α≤N →
        (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤Z^U) →
        ∀(R seed : Ideal O)(K ξ : ℝ)(hK : 0<K)(bin : ℤ×(Fin 5→ℤ))
          (column : Label→FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin)),
        ((selectedShells (selectedFirstProjectors column)).card:ℝ)≤C*Z^ε := by
  obtain ⟨C,hC,hbound⟩:=actual_first_projector_shell_subpower N U ε hU hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro α Label _ _ _ s hN hpool R seed K ξ hK bin column
  have h:=hz.2 s hN hpool R seed K ξ hK bin (Finset.univ.image column)
  simpa only [firstProjectorSet,Finset.image_image,Function.comp_def,
    selected_first_projectors_eq_image] using h

theorem actual_geometry_selected_first_shell_restriction {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (column : Label→ firstLiveColumns (geometryFirstSource s R seed K Z ξ hK bin) (fun _=>logAnnulus))
    (alloc : (j : Label)→actualAllocations s.pools
      (geometryColumnIdeal reflected s R seed K Z ξ hK bin (column j).val))
    (hinj : Function.Injective (fun j=>(geometryFirstLabel s R seed K Z ξ hK bin (column j).val,
      (column j).val.2.1.val)))
    (hf : ∀j,frozenCoefficient (alloc j).val
      (geometryColumnIdeal reflected s R seed K Z ξ hK bin (column j).val) R s.ν s.W s.P≠0)
    (n : ℤ) :
    Function.Injective (fun j : SelectedFirstShell (fun j=>(column j).val) n=>
      (geometryFirstLabel s R seed K Z ξ hK bin (column j.val).val,(column j.val).val.2.1.val)) ∧
    (∀j : SelectedFirstShell (fun j=>(column j).val) n,
      frozenCoefficient (alloc j.val).val
        (geometryColumnIdeal reflected s R seed K Z ξ hK bin (column j.val).val) R s.ν s.W s.P≠0) ∧
    (∀j : SelectedFirstShell (fun j=>(column j).val) n,
      dyadicScale n≤((column j.val).val.2.1.val.absNorm:ℝ) ∧
      ((column j.val).val.2.1.val.absNorm:ℝ)<2*dyadicScale n) := by
  refine ⟨hinj.comp Subtype.val_injective,(fun j=>hf j.val),?_⟩
  intro j
  exact (selected_first_shell_gates (fun j=>(column j).val) n j).2

end
end OAI.SevenEighths.Cycle63InitialMass
