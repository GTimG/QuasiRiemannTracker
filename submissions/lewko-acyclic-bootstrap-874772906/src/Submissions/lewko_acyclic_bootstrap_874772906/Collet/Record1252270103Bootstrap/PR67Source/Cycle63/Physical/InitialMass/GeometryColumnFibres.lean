import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainRadius
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.JointAllocationEnergy
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentDyadicCount

/-- The first dyads and ray choices may be selected at each arithmetic
label/projector pair for a uniform small-power cost. The projector remains
in the selected family for its later joint-frequency divisor bound. -/
theorem actual_first_selected_column_budget_indexed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A D B ξ ε : ℝ) (hA : 0≤A) (hD : 0≤D) (hB : 0≤B) (hξ : 0≤ξ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,1≤Z ∧
      ∀(s : Input ι)(R seed : Ideal O)(K : ℝ)(hK : 0<K)(key : ℤ×(Fin 5→ℤ)),
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 →
      0<sourceRadius s → sourceRadius s≤Z^B → volume s≤Z^A → K⁻¹≤Z^D →
      ∀{κ : Type*}(column : κ→FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)),
      Function.Injective column → ∀(rows : Finset κ)
        (cost : rows→ℝ)(E : ℝ),(∀r,0≤ cost r) →
      let code := fun r : rows=>(geometryFirstLabel s R seed K Z ξ hK key (column r.val),(column r.val).2.1.val)
      (∀pick : (j : Finset.univ.image code)→ ↥rows,
        (∀j,code (pick j)=j.val) → (∑j : Finset.univ.image code,cost (pick j))≤E) →
      (∑r : rows,cost r)≤(C*Z^ε)*E := by
  have hL : 0≤3*max A D+ξ/2 := by positivity
  obtain ⟨C,hC,hdyad⟩ := source_dyadic_envelope_subpower B (3*max A D+ξ/2) ε hB hL hε
  have hray : (0:ℝ)<Fintype.card RayCharacter := by exact_mod_cast Fintype.card_pos
  refine ⟨C*(Fintype.card RayCharacter:ℝ)^2,by positivity,?_⟩
  filter_upwards [hdyad,eventually_ge_atTop (1:ℝ)] with Z hdyad hZ
  refine ⟨hZ,?_⟩
  intro s R seed K hK key hseed hz₁ hz₂ hsource hsourcecap hV hKi κ column hinj rows cost E hc
  dsimp only
  intro hjoint
  let N : Finset (Fin 4→ℤ) := Fintype.piFinset (fun i=>
    indices (![K/Z^(2*B),1,1,1] i) (![K,Z^(3*max A D+ξ/2),Z^B,Z^B] i))
  have hN : (N.card:ℝ)≤C*Z^ε := by
    have hh := hdyad K hK
    simpa only [N,SourceDyadicEnvelope,Fintype.card_piFinset,Fintype.card_pi,Fintype.card_coe] using hh
  let code := fun r : rows=>(geometryFirstLabel s R seed K Z ξ hK key (column r.val),(column r.val).2.1.val)
  apply joint_fiber_selection code cost ((C*(Fintype.card RayCharacter:ℝ)^2)*Z^ε) E
    (by positivity) hc _ hjoint
  intro j hj
  let fiber := Finset.univ.filter (fun r : rows=>code r=j)
  let target := N ×ˢ ((Finset.univ : Finset RayCharacter) ×ˢ (Finset.univ : Finset RayCharacter))
  have hcard : fiber.card≤target.card := Finset.card_le_card_of_injOn
    (fun r : rows=>((fun i=>((column r.val).1.val.2.2 i:ℤ)),(column r.val).2.2.1,(column r.val).2.2.2))
    (by
      intro r hr
      refine Finset.mem_product.mpr ⟨?_,by simp⟩
      exact Fintype.mem_piFinset.mpr (actual_dyads_in_envelope s R seed K Z ξ A D B
        hK hZ hB hA hD hξ hseed hz₁ hz₂ hsource hsourcecap hV hKi (column r.val).1.val))
    (by
      intro r hr t ht he
      apply Subtype.ext
      apply hinj
      apply geometry_first_column_code_injective s R seed K Z ξ hK key
      have hcode : code r=code t := (Finset.mem_filter.mp hr).2.trans (Finset.mem_filter.mp ht).2.symm
      exact congrArg₂ (fun (x : FirstSourceLabel×Ideal O) (y : (Fin 4→ℤ)×RayCharacter×RayCharacter)=>
        (x.1,x.2,y)) hcode he)
  have hcard' : (fiber.card:ℝ)≤N.card*(Fintype.card RayCharacter:ℝ)^2 := by
    have hh : target.card=N.card*(Fintype.card RayCharacter)^2 := by
      simp only [target,Finset.card_product,Finset.card_univ,pow_two]
    rw [hh] at hcard
    exact_mod_cast hcard
  exact hcard'.trans ((mul_le_mul_of_nonneg_right hN (sq_nonneg _)).trans_eq (by ring))

/-- Specialization to the original column type. -/
theorem actual_first_selected_column_budget {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A D B ξ ε : ℝ) (hA : 0≤A) (hD : 0≤D) (hB : 0≤B) (hξ : 0≤ξ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,1≤Z ∧
      ∀(s : Input ι)(R seed : Ideal O)(K : ℝ)(hK : 0<K)(key : ℤ×(Fin 5→ℤ)),
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 →
      0<sourceRadius s → sourceRadius s≤Z^B → volume s≤Z^A → K⁻¹≤Z^D →
      ∀(rows : Finset (FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)))
        (cost : rows→ℝ)(E : ℝ),(∀r,0≤ cost r) →
      let code := fun r : rows=>(geometryFirstLabel s R seed K Z ξ hK key r.val,r.val.2.1.val)
      (∀pick : (j : Finset.univ.image code)→ ↥rows,
        (∀j,code (pick j)=j.val) → (∑j : Finset.univ.image code,cost (pick j))≤E) →
      (∑r : rows,cost r)≤(C*Z^ε)*E := by
  obtain ⟨C,hC,hbound⟩ := actual_first_selected_column_budget_indexed (ι:=ι)
    A D B ξ ε hA hD hB hξ hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro s R seed K hK key hseed hz₁ hz₂ hsource hsourcecap hV hKi rows cost E hc code hjoint
  exact hz.2 s R seed K hK key hseed hz₁ hz₂ hsource hsourcecap hV hKi
    id Function.injective_id rows cost E hc hjoint

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
