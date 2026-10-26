import Candidate.Cycle63.Physical.InitialMass.GeometryAllocationMass
import Candidate.Cycle63.Physical.InitialMass.GeometryColumnFibres

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic
local notation "O" => HeckeFamily.O

/-- Reduce the actual weighted main source sum to supported common
allocations with unique arithmetic-label/projector keys. First dyads and
ray characters incur only the proved small-power cost. -/
theorem actual_geometry_selected_main_budget {ι : Type*}[Fintype ι][DecidableEq ι]
    (N : ℕ)(Cs b ε Amax Dmax B ξ : ℝ)
    (hCs : 1≤Cs)(hε : 0<ε)(hA : 0≤Amax)(hD : 0≤Dmax)(hB : 0≤B)(hξ : 0≤ξ) :
    ∃K₀ : ℝ,0<K₀ ∧ ∀ᶠZ : ℝ in atTop,1≤Z ∧
      ∀(s : Input ι),Fintype.card ι≤N → (∀i,s.M i≤Cs) →
      ∀(reflected : Bool)(R seed : Ideal O)(K M A sigma reserve t : ℝ)
        (hK : 0<K)(key : ℤ×(Fin 5→ℤ))
        (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ),
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 →
      0<sourceRadius s → sourceRadius s≤Z^B → volume s≤Z^Amax → K⁻¹≤Z^Dmax →
      ∀(rows : Finset (FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)))
        (G E : ℝ),0≤G →
      let C := fun j : rows=>geometryColumnIdeal reflected s R seed K Z ξ hK key j.val
      let χ := fun j : rows=>geometryColumnCharacter reflected s R seed K Z ξ hK key j.val
      let g := fun j : rows=>geometryBranch reflected s R seed K Z ξ hK key j.val
      let w := fun j : rows=>geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j.val
      (∀j,C j≠0) →
      (∀j,‖geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j.val‖^2*
        ((C j).absNorm:ℝ)^(ε-1)≤G) →
      (∀{Label : Type}[Fintype Label](column : Label → rows),
        Function.Injective (fun j=>(geometryFirstLabel s R seed K Z ξ hK key (column j).val,
          (column j).val.2.1.val)) →
        ∀alloc : (j : Label)→actualAllocations s.pools (C (column j)),
        (∀j,frozenCoefficient (alloc j).val (C (column j)) R s.ν s.W s.P≠0) →
        (∑j : Label,actualMainSource (child s (C (column j)) R (alloc j) (χ (column j)) t)
          (g (column j)) Z sigma 1 ξ reserve)≤E) →
      (∑j : rows,∑alloc : actualAllocations s.pools (C j),
        w j alloc*actualMainSource (child s (C j) R alloc (χ j) t) (g j) Z sigma 1 ξ reserve)≤
          (K₀*G*Z^ε)*E := by
  obtain ⟨D,hDmass,hmass⟩ := actual_geometry_main_selection N Cs b ε hCs hε
  obtain ⟨F,hF,hcolumns⟩ := actual_first_selected_column_budget_indexed (ι:=ι)
    Amax Dmax B ξ ε hA hD hB hξ hε
  refine ⟨D*F,mul_pos hDmass hF,?_⟩
  filter_upwards [hcolumns] with Z hz
  refine ⟨hz.1,?_⟩
  intro s hn hM reflected R seed K M A sigma reserve t hK key weight hseed hz₁ hz₂
    hsource hsourcecap hV hKi rows G E hG C χ g w hC hscalar hselected
  have hZ : 0<Z := zero_lt_one.trans_le hz.1
  have hh := hmass s hn hM reflected R seed K Z ξ M A sigma reserve t hK hZ key weight
    rows G ((F*Z^ε)*E) hG hC hscalar (by
      intro S alloc halloc
      apply hz.2 s R seed K hK key hseed hz₁ hz₂ hsource hsourcecap hV hKi
        (fun j : rows=>j.val) Subtype.val_injective S
        (fun j=>actualMainSource (child s (C j.val) R (alloc j) (χ j.val) t)
          (g j.val) Z sigma 1 ξ reserve) E
        (fun j=>actual_geometry_main_nonneg reflected s R seed K Z ξ sigma reserve hK hZ
          key j.val.val (alloc j) t)
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
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_selected_main_budget
