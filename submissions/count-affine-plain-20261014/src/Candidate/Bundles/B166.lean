/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B090
import Candidate.Bundles.B135
import Candidate.Bundles.B147
import Candidate.Bundles.B161

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryLowSidePayment; sha256 9d7d3588f932bb5db90906c83d664a7ac7220566cc75623e4f2f405c247724da -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                       
                                                        

set_option autoImplicit false
set_option maxHeartbeats 300000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
open ActualEisensteinCubic Cycle61Moment
local notation "O" => HeckeFamily.O

/-- The low scalar uses the same literal first-label coordinates as the
physical normalization, before any dyadic endpoints are substituted. -/
theorem actual_low_geometry_exponent_coordinates
    {α : Type*} [Fintype α] [DecidableEq α]
    (s : Input α) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0< K)
    (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))
    (reflected : Bool) (A : ℝ) :
    let x := geometryExponents s R seed K Z ξ j.1.val
    lowGeometryExponent reflected Z A (geometryFirstLabel s R seed K Z ξ hK key j)=
      A-x (if reflected then 1 else 0)+x 3+x 4 := by
  intro x
  let l:=geometryFirstLabel s R seed K Z ξ hK key j
  have he : Ideal.span {primeSubsetGenerator
      (fun P : CommonIndex l.1.1 l.1.2=>P.val) l.2.val}=
      firstProjectorRadical l.1.1 l.1.2 l.2.val := by
    rw [primeSubsetGenerator,span_idealGenerator]
    rfl
  change Ideal.span {primeSubsetGenerator
    (fun P : CommonIndex j.1.val.1.val.1 j.1.val.1.val.2=>P.val) j.1.val.2.1.val}=_ at he
  cases reflected <;>
    dsimp [lowGeometryExponent,x,geometryExponents,geometryNorms,geometryIdeals,
      geometryFirstLabel,l] <;> rw [he] <;> rfl

/-- One common first-geometry bin supplies all three low-branch scalar
gates. Their combined loss is exactly four binary-bin widths, hence a
fixed factor rather than a new power of the source scale. -/
theorem actual_geometry_low_bin_scalar_gates
    {α : Type*} [Fintype α] [DecidableEq α]
    (s : Input α) (R seed : Ideal O) (K Z ξ B A : ℝ) (hK : 0< K)
    (hZ : 1< Z) (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤ Z^B) (key : ℤ×(Fin 5→ℤ)) (reflected : Bool) :
    let w:=Real.logb Z 2
    let c : Fin 5:=if reflected then 1 else 0
    let p:=((key.2 2:ℝ)+1)*w
    let exponent:=A-(key.2 c:ℝ)*w+((key.2 3:ℝ)+1)*w+((key.2 4:ℝ)+1)*w
    let sideLower:=(key.2 2:ℝ)*w+A-((key.2 c:ℝ)+1)*w+
      (key.2 3:ℝ)*w+(key.2 4:ℝ)*w
    p+exponent-sideLower=4*w ∧
    ∀j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key),
      ((commonRadical
        (geometryFirstLabel s R seed K Z ξ hK key j).1.1
        (geometryFirstLabel s R seed K Z ξ hK key j).1.2).absNorm:ℝ)≤ Z^p ∧
      lowGeometryExponent reflected Z A
        (geometryFirstLabel s R seed K Z ξ hK key j)≤ exponent ∧
      sideLower≤ geometryHighSide reflected A (geometryExponents s R seed K Z ξ j.1.val) := by
  intro w c p exponent sideLower
  refine ⟨by dsimp [p,exponent,sideLower];ring,?_⟩
  intro j
  let x:=geometryExponents s R seed K Z ξ j.1.val
  have hx (i : Fin 5) : (key.2 i:ℝ)*w≤ x i ∧ x i≤((key.2 i:ℝ)+1)*w := by
    have h:=actual_geometry_fiber_range s R seed K Z ξ B hZ hs hz₁ hz₂ hsource key j.1 i
    exact ⟨h.1,h.2.le⟩
  refine ⟨?_,?_,?_⟩
  · have hn:=actual_geometry_norm_caps s R seed K Z ξ B hs hz₁ hz₂ hsource j.1.val 2
    exact (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hn.1)).mp (hx 2).2
  · rw [actual_low_geometry_exponent_coordinates]
    change A-x c+x 3+x 4≤ exponent
    dsimp only [exponent]
    linarith [(hx c).1,(hx 3).2,(hx 4).2]
  · have hbase : sideLower≤ x 2+A-x c+x 3+x 4 := by
      dsimp only [sideLower]
      linarith [(hx 2).1,(hx c).2,(hx 3).1,(hx 4).1]
    cases reflected <;>
      simp only [geometryHighSide,Bool.false_eq_true,ite_false,ite_true,leftExponent,rightExponent] <;>
      simp only [c,Bool.false_eq_true,ite_false,ite_true] at hbase
    all_goals change sideLower≤ x 2+A-x _+x 3+x 4+max (3*x _-5*x _-x 3) 0/6
    · linarith [le_max_right (3*x 0-5*x 1-x 3) (0:ℝ)]
    · linarith [le_max_right (3*x 1-5*x 0-x 3) (0:ℝ)]

/-- The complete bin slack costs sixteen, independently of the scale. -/
theorem geometry_low_bin_slack_payment (Z : ℝ) (hZ : 1< Z) :
    Z^(4*Real.logb Z 2)=(16:ℝ) := by
  rw [mul_comm (4:ℝ),Real.rpow_mul (zero_lt_one.trans hZ).le,
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (by norm_num : (0:ℝ)<2)]
  norm_num

/-- A nonempty first geometry bin has a uniformly bounded radical upper
endpoint. The extra one is only the last binary interval at Z at least two. -/
theorem actual_geometry_low_bin_radical_exponent_cap
    {α : Type*} [Fintype α] [DecidableEq α]
    (s : Input α) (R seed : Ideal O) (K Z ξ B : ℝ)
    (hZ : 2≤ Z) (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤ Z^B) (key : ℤ×(Fin 5→ℤ))
    (q : CommonGeometryFiber s R seed K Z ξ key) :
    ((key.2 2:ℝ)+1)*Real.logb Z 2≤ B+1 := by
  have hZ1 : 1< Z := by linarith
  have hn:=actual_geometry_norm_caps s R seed K Z ξ B hs hz₁ hz₂ hsource q.val 2
  have hx:=actual_geometry_fiber_range s R seed K Z ξ B hZ1 hs hz₁ hz₂ hsource key q 2
  have hcap : geometryExponents s R seed K Z ξ q.val 2≤ B :=
    (Real.logb_le_iff_le_rpow hZ1 (zero_lt_one.trans_le hn.1)).mpr hn.2
  have hw : Real.logb Z 2≤1 := by
    apply (Real.logb_le_iff_le_rpow hZ1 (by norm_num : (0:ℝ)<2)).mpr
    simpa only [Real.rpow_one] using hZ
  nlinarith

/-- The original main amplifier and all first-label scalar exponents
cancel, leaving the analytic small losses and the fixed bin constant. -/
theorem geometry_low_complete_exponent_payment
    (Z amp p exponent sideLower loss : ℝ) (hZ : 1< Z)
    (hledger : p+exponent-sideLower=4*Real.logb Z 2) :
    Z^(-amp)*Z^(amp+p+exponent-sideLower+loss)=16*Z^loss := by
  rw [←Real.rpow_add (zero_lt_one.trans hZ)]
  have he : -amp+(amp+p+exponent-sideLower+loss)=4*Real.logb Z 2+loss := by linarith
  rw [he,Real.rpow_add (zero_lt_one.trans hZ),geometry_low_bin_slack_payment Z hZ]

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_low_geometry_exponent_coordinates
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_low_bin_scalar_gates
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_low_bin_slack_payment
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_low_bin_radical_exponent_cap
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_low_complete_exponent_payment

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryLowSidePayment -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainFirstProjectorShell; sha256 aacf120e55b2d8cb2a72c7afb0443495523d82c758ae177f7955f6a05276f049 -/
section
                                                        

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CenteredMomentWholeDivisorShell CenteredMomentSectorLocalization
open CenteredMomentSourceRow CenteredMomentCommonAllocationSum
open CenteredMomentCommonRadialData CenteredMomentLogDyadic CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O

/-- Singleton sets retain the allocator attached to each selected column. -/
def selectedFirstProjectors {ι Label : Type*} [Fintype Label]
    {src : ι→ FirstBlockSource} (column : Label→ FirstColumnIndex src) : Finset (Ideal O) :=
  sharedProjectors (fun j=>{(column j).2.1.val})

abbrev SelectedFirstShell {ι Label : Type*} [Fintype Label]
    {src : ι→ FirstBlockSource} (column : Label→ FirstColumnIndex src) (n : ℤ) :=
  {j : Label // (column j).2.1.val∈shell (selectedFirstProjectors column) n}

lemma selected_first_projectors_eq_image {ι Label : Type*} [Fintype Label]
    {src : ι→ FirstBlockSource} (column : Label→ FirstColumnIndex src) :
    selectedFirstProjectors column=Finset.univ.image (fun j=>(column j).2.1.val) := by
  ext D
  simp [selectedFirstProjectors,sharedProjectors,eq_comm]

/-- Cost may include the original allocation, scalar, mass and complete
second-block cost; restriction neither changes nor duplicates them. -/
theorem selected_first_shell_sum {ι Label : Type*} [Fintype Label]
    {src : ι→ FirstBlockSource} (column : Label→ FirstColumnIndex src)
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
  apply Finset.sum_congr rfl
  intro n hn
  rw [←Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) cost

theorem selected_first_shell_injective {ι Label Key : Type*} [Fintype Label]
    {src : ι→ FirstBlockSource} (column : Label→ FirstColumnIndex src)
    (key : Label→ Key) (hinj : Function.Injective key) (n : ℤ) :
    Function.Injective (fun j : SelectedFirstShell column n=>key j.val) :=
  hinj.comp Subtype.val_injective

theorem selected_first_shell_gates {ι Label : Type*} [Fintype Label]
    {src : ι→ FirstBlockSource} (column : Label→ FirstColumnIndex src) (n : ℤ)
    (j : SelectedFirstShell column n) :
    Squarefree (column j.val).2.1.val ∧
      dyadicScale n≤((column j.val).2.1.val.absNorm:ℝ) ∧
      ((column j.val).2.1.val.absNorm:ℝ)<2*dyadicScale n := by
  have h:=shell_member_data (selectedFirstProjectors column) n _ j.property
  exact ⟨h.2.2.1,h.2.2.2.2⟩

/-- A modular per-shell estimate pays only the number of norm shells. -/
theorem selected_first_shell_payment {ι Label : Type*} [Fintype Label]
    {src : ι→ FirstBlockSource} (column : Label→ FirstColumnIndex src)
    (hs : ∀j,Squarefree (column j).2.1.val) (cost : Label→ℝ) (E C Z ε : ℝ)
    (hE : 0≤ E)
    (hcard : ((selectedShells (selectedFirstProjectors column)).card:ℝ)≤ C*Z^ε)
    (hbound : ∀n∈selectedShells (selectedFirstProjectors column),
      (∑j : SelectedFirstShell column n,cost j.val)≤ E) :
    (∑j,cost j)≤ C*Z^ε*E := by
  rw [selected_first_shell_sum column hs cost]
  calc
    _≤∑_n∈selectedShells (selectedFirstProjectors column),E :=
      Finset.sum_le_sum hbound
    _=((selectedShells (selectedFirstProjectors column)).card:ℝ)*E := by simp
    _≤ C*Z^ε*E := mul_le_mul_of_nonneg_right hcard hE

/-- The stored-pool cap controls the common FIRST projector union, including
columns whose allocations have zero coefficient. -/
theorem actual_geometry_selected_first_projector_cap {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (s : Input α) (N : ℕ) (R seed : Ideal O) (K Z ξ U : ℝ) (hK : 0< K)
    (hN : Fintype.card α≤ N) (hZ : 1≤ Z) (hU : 0≤ U)
    (hpool : ∀i I,I∈s.pools i→(I.absNorm:ℝ)≤ Z^U)
    (bin : ℤ×(Fin 5→ℤ))
    (column : Label→ FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin)) :
    ∀D∈selectedFirstProjectors column,(D.absNorm:ℝ)≤ Z^(((N:ℝ)+2)*U) := by
  intro D hD
  rw [selected_first_projectors_eq_image] at hD
  obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hD
  exact actual_geometry_projector_cap s N R seed K Z ξ U hK hN hZ hU hpool bin (column j)

theorem actual_geometry_selected_first_shell_scale {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (s : Input α) (N : ℕ) (R seed : Ideal O) (K Z ξ U : ℝ) (hK : 0< K)
    (hN : Fintype.card α≤ N) (hZ : 1≤ Z) (hU : 0≤ U)
    (hpool : ∀i I,I∈s.pools i→(I.absNorm:ℝ)≤ Z^U)
    (bin : ℤ×(Fin 5→ℤ))
    (column : Label→ FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (n : ℤ) (hn : n∈selectedShells (selectedFirstProjectors column)) :
    1≤ dyadicScale n ∧ dyadicScale n≤ Z^(((N:ℝ)+2)*U) := by
  exact selected_scale_bounds _ _
    (fun D hD _=>actual_geometry_selected_first_projector_cap s N R seed K Z ξ U hK
      hN hZ hU hpool bin column D hD) n hn

theorem eventual_actual_geometry_selected_first_shell_subpower (N : ℕ) (U ε : ℝ)
    (hU : 0≤ U) (hε : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
      ∀{α Label : Type*}[Fintype α][DecidableEq α][Fintype Label]
        (s : Input α),Fintype.card α≤ N →
        (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤ Z^U) →
        ∀(R seed : Ideal O)(K ξ : ℝ)(hK : 0< K)(bin : ℤ×(Fin 5→ℤ))
          (column : Label→ FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin)),
        ((selectedShells (selectedFirstProjectors column)).card:ℝ)≤ C*Z^ε := by
  obtain ⟨C,hC,hbound⟩:=actual_first_projector_shell_subpower N U ε hU hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro α Label _ _ _ s hN hpool R seed K ξ hK bin column
  have h:=hz.2 s hN hpool R seed K ξ hK bin (Finset.univ.image column)
  simpa only [firstProjectorSet,Finset.image_image,Function.comp_def,
    selected_first_projectors_eq_image] using h

/-- Literal live selected columns keep their original allocation and source
geometry when the weighted complete cost is disintegrated. -/
theorem actual_geometry_selected_first_cost_shell_sum {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0< K)
    (bin : ℤ×(Fin 5→ℤ))
    (column : Label→ firstLiveColumns (geometryFirstSource s R seed K Z ξ hK bin) (fun _=>logAnnulus))
    (alloc : (j : Label)→ actualAllocations s.pools
      (geometryColumnIdeal reflected s R seed K Z ξ hK bin (column j).val))
    (mass : Label→ℝ) (cost : (j : Label)→ actualAllocations s.pools
      (geometryColumnIdeal reflected s R seed K Z ξ hK bin (column j).val)→ℝ) :
    (∑j,mass j*cost j (alloc j))=
      ∑n∈selectedShells (selectedFirstProjectors (fun j=>(column j).val)),
        ∑j : SelectedFirstShell (fun j=>(column j).val) n,
          mass j.val*cost j.val (alloc j.val) := by
  exact selected_first_shell_sum (fun j=>(column j).val)
    (fun j=>actual_first_live_squarefree _ _ _ (column j).property)
    (fun j=>mass j*cost j (alloc j))

theorem actual_geometry_selected_first_shell_restriction {α Label : Type*}
    [Fintype α] [DecidableEq α] [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0< K)
    (bin : ℤ×(Fin 5→ℤ))
    (column : Label→ firstLiveColumns (geometryFirstSource s R seed K Z ξ hK bin) (fun _=>logAnnulus))
    (alloc : (j : Label)→ actualAllocations s.pools
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
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.selected_first_shell_sum
#print axioms OAI.SevenEighths.Cycle61InitialMass.selected_first_shell_injective
#print axioms OAI.SevenEighths.Cycle61InitialMass.selected_first_shell_gates
#print axioms OAI.SevenEighths.Cycle61InitialMass.selected_first_shell_payment
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_selected_first_projector_cap
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_selected_first_shell_scale
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_geometry_selected_first_shell_subpower

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_selected_first_cost_shell_sum
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_selected_first_shell_restriction
#print axioms OAI.SevenEighths.Cycle61InitialMass.selected_first_projectors_eq_image

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainFirstProjectorShell -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryHeightAbsorption; sha256 e45181d7b5ffd83f1e05147a1791eecc3bbb5ccc8d03553eb239aa643f25e49c -/
section
                                                             

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section

/-- At large outer heights, a fixed polynomial height factor absorbs any
fixed coarse power of the scale. The degree precedes the scale and height. -/
theorem geometry_large_height_absorption (coarse target τ : ℝ)(hτ : 0<τ) :
    ∃n : ℕ,∀Z H : ℝ,1≤ Z → Z^τ≤ H → Z^coarse≤ Z^target*H^n := by
  obtain ⟨n,hn⟩:=exists_nat_gt ((coarse-target)/τ)
  refine ⟨n,?_⟩
  intro Z H hZ hH
  have hz : 0< Z := zero_lt_one.trans_le hZ
  have hn' : coarse≤ target+τ*(n:ℝ) := by
    have hh:=(div_lt_iff₀ hτ).mp hn
    linarith
  calc
    Z^coarse≤ Z^(target+τ*(n:ℝ)) := Real.rpow_le_rpow_of_exponent_le hZ hn'
    _=Z^target*(Z^τ)^n := by rw [Real.rpow_add hz,Real.rpow_mul hz.le,Real.rpow_natCast]
    _≤ Z^target*H^n := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.rpow_nonneg hz.le _) hH n) (Real.rpow_nonneg hz.le _)

/-- Combine a truncated analytic estimate with an all-height coarse one.
The coarse estimate is used only beyond the proved analytic height range. -/
theorem geometry_extend_height_bound (coarse target τ : ℝ)(hτ : 0<τ)(smallDegree : ℕ) :
    ∃degree : ℕ,∀Z H E Csmall Ccoarse control : ℝ,
      1≤ Z → 1≤ H → 0≤ Csmall → 0≤ Ccoarse → 0≤ control →
      (H≤ Z^τ → E≤ Csmall*control*Z^target*H^smallDegree) →
      E≤ Ccoarse*control*Z^coarse →
      E≤(Csmall+Ccoarse)*control*Z^target*H^degree := by
  obtain ⟨n,hn⟩:=geometry_large_height_absorption coarse target τ hτ
  refine ⟨max n smallDegree,?_⟩
  intro Z H E Cs Cc control hZ hH hCs hCc hc hsmall hcoarse
  have hz : 0≤ Z := zero_le_one.trans hZ
  by_cases h : H≤ Z^τ
  · apply (hsmall h).trans
    apply mul_le_mul
    · gcongr; linarith
    · exact pow_le_pow_right₀ hH (le_max_right _ _)
    · positivity
    · positivity
  · have hh:=hn Z H hZ (le_of_lt (lt_of_not_ge h))
    calc
      E≤ Cc*control*Z^coarse := hcoarse
      _≤ Cc*control*(Z^target*H^n) := mul_le_mul_of_nonneg_left hh (mul_nonneg hCc hc)
      _≤(Cs+Cc)*control*Z^target*H^(max n smallDegree) := by
        rw [←mul_assoc]
        apply mul_le_mul
        · gcongr; linarith
        · exact pow_le_pow_right₀ hH (le_max_left _ _)
        · positivity
        · positivity

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_large_height_absorption
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_extend_height_bound

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryHeightAbsorption -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryShiftedHeight; sha256 290b6c05a7ddfa8176a72e9e9b81aefe0ac5aa23b8605d6e9d97bfb86b5ca610 -/
section
                                                            

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section

/-- The original height and both Mellin shifts admit separate polynomial
weights. This lets an all-height coarse bound cover the complement of the
analytic range without restricting either integration variable. -/
theorem geometry_shifted_height_product (v height t u : ℝ) (hh : 0≤ height) :
    2*(1+|v|+height+2*Real.pi*(|t|+|u|))≤
      (2+4*Real.pi)*(1+|v|+height)*(1+|t|)*(1+|u|) := by
  have hp : 0≤ Real.pi := Real.pi_pos.le
  have hv := abs_nonneg v
  have ht := abs_nonneg t
  have hu := abs_nonneg u
  have htu : 0≤|t| * |u| := mul_nonneg ht hu
  have hsum : |t|+|u|≤(1+|t|)*(1+|u|) := by nlinarith
  have hbase : 1+|v|+height≤(1+|v|+height)*(1+|t|)*(1+|u|) := by
    nlinarith [mul_nonneg (add_nonneg hv hh) ht,
      mul_nonneg (add_nonneg hv hh) hu,
      mul_nonneg (add_nonneg hv hh) htu]
  have hshifts : |t|+|u|≤(1+|v|+height)*(1+|t|)*(1+|u|) := by
    nlinarith [mul_nonneg (add_nonneg hv hh) (by positivity : 0≤(1+|t|)*(1+|u|))]
  nlinarith

theorem geometry_extend_shifted_height_bound (coarse target τ : ℝ)
    (hτ : 0<τ) (smallDegree : ℕ) :
    ∃degree : ℕ,∀Z v height t u E Cs Cc control : ℝ,
      1≤ Z → 0≤ height → 0≤ Cs → 0≤ Cc → 0≤ control →
      (2*(1+|v|+height+2*Real.pi*(|t|+|u|))≤ Z^τ →
        E≤ Cs*control*Z^target*
          (2*(1+|v|+height+2*Real.pi*(|t|+|u|)))^smallDegree) →
      E≤ Cc*control*Z^coarse →
      E≤(2+4*Real.pi)^degree*(Cs+Cc)*control*Z^target*
        (1+|v|+height)^degree*(1+|t|)^degree*(1+|u|)^degree := by
  obtain ⟨degree,hext⟩ := geometry_extend_height_bound coarse target τ hτ smallDegree
  refine ⟨degree,?_⟩
  intro Z v height t u E Cs Cc control hZ hh hCs hCc hc hs hb
  have hH : 1≤2*(1+|v|+height+2*Real.pi*(|t|+|u|)) := by
    have hp : 0≤2*Real.pi*(|t|+|u|) := by positivity
    linarith [abs_nonneg v]
  have h := hext Z _ E Cs Cc control hZ hH hCs hCc hc hs hb
  apply h.trans
  have hp := pow_le_pow_left₀ (by positivity : 0≤2*(1+|v|+height+2*Real.pi*(|t|+|u|)))
    (geometry_shifted_height_product v height t u hh) degree
  have hm := mul_le_mul_of_nonneg_left hp
    (by positivity : 0≤(Cs+Cc)*control*Z^target)
  simpa only [mul_pow,mul_assoc,mul_left_comm,mul_comm] using hm

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_shifted_height_product
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_extend_shifted_height_bound

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryShiftedHeight -/
