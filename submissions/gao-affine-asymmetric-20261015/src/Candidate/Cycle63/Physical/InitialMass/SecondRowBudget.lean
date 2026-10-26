import Candidate.Cycle63.Physical.InitialMass.SecondRowFibres

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment RayFourExpansion
local notation "O" => HeckeFamily.O

/-- The joint density estimate may be applied after selecting one actual
source in each encoded fiber. This applies to any selected row bin and
charges only the first-projector small power, dyads and finite rays. -/
theorem actual_second_fiber_dyad_budget (B ε : ℝ) (hB : 0≤B) (hε : 0<ε) :
    ∃K : ℝ,0<K ∧ ∀Z : ℝ,1≤Z → ∀{Label : Type*}[Fintype Label]
      (s : Label→SecondBlockSource) (first : Label→FirstSourceLabel) (seed : Label→Ideal O),
      Function.Injective (fun l=>(first l,seed l,secondBlockCode (s l))) →
      (∀l,Squarefree (seed l)) → (∀l,seed l∣(s l).C ∧ seed l∣(s l).D) →
      ∀(left : Bool)(u₀ : O)(unit : FirstSourceLabel→O)
        (hf : ∀r : secondLiveRows s,
          jointFirstFrequency left u₀ unit (secondEncodedRow s first r)≠0)
        (rows : Finset (secondLiveRows s))
        (N : NonzeroJointSourceLabel left u₀ unit→Finset (Fin 4→ℤ)) (D : ℝ)
        (cost : rows→ℝ) (E : ℝ),
      (∀r : rows,((Ideal.span {jointSourceRow left u₀ unit
        (secondEncodedRow s first r.val)}).absNorm:ℝ)≤Z^B) →
      0≤D → (∀r : rows,
        (N (secondEncodedNonzeroRow s first r.val left u₀ unit (hf r.val))).card≤D) →
      (∀r : secondLiveRows s,(s r.val.1).dyad∈N (secondEncodedNonzeroRow s first r left u₀ unit (hf r))) →
      (∀r,0≤cost r) →
      let key := fun r : rows=>secondEncodedNonzeroRow s first r.val left u₀ unit (hf r.val)
      (∀pick : (j : Finset.univ.image key)→ ↥rows,
        (∀j,key (pick j)=j.val) → (∑j : Finset.univ.image key,cost (pick j))≤E) →
      (∑r : rows,cost r)≤((K*Z^ε)*D*(Fintype.card RayCharacter:ℝ)^2)*E := by
  obtain ⟨K,hK,hbound⟩ := actual_second_projector_fiber_bound B ε hB hε
  refine ⟨K,hK,?_⟩
  intro Z hZ Label _ s first seed hinj hseed hdiv left u₀ unit hf rows N D cost E hnorm hD hcard hdyad hc
  dsimp only
  intro hjoint
  let key := fun r : rows=>secondEncodedNonzeroRow s first r.val left u₀ unit (hf r.val)
  apply joint_fiber_selection key cost _ E (by positivity) hc _ hjoint
  intro j hj
  have hjnorm : ((Ideal.span {jointSourceRow left u₀ unit j.val}).absNorm:ℝ)≤Z^B := by
    obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hj
    subst j
    exact hnorm r
  have hcardj : (N j).card≤D := by
    obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hj
    subst j
    exact hcard r
  have hglobal := hbound Z hZ s first seed hinj hseed hdiv left u₀ unit j (N j) hjnorm
    (fun r hr=>by
      have hk : secondEncodedNonzeroRow s first r left u₀ unit (hf r)=j := Subtype.ext hr
      simpa only [hk] using hdyad r)
  have hsub : (Finset.univ.filter (fun r : rows=>key r=j)).card≤
      (Finset.univ.filter (fun r : secondLiveRows s=>secondEncodedRow s first r=j.val)).card := by
    apply Finset.card_le_card_of_injOn (fun r : rows=>r.val)
    · intro r hr
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
      exact congrArg Subtype.val (Finset.mem_filter.mp hr).2
    · intro r hr t ht he
      exact Subtype.ext he
  exact (show ((Finset.univ.filter (fun r : rows=>key r=j)).card:ℝ)≤
      (Finset.univ.filter (fun r : secondLiveRows s=>secondEncodedRow s first r=j.val)).card
      from by exact_mod_cast hsub).trans (hglobal.trans (by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcardj (by positivity)) (sq_nonneg _)))

/-- The joint density estimate may be applied after selecting one actual
source in each encoded fiber. This applies to any selected row bin and
charges only the first-projector small power, dyads and finite rays. -/
theorem actual_second_selected_row_budget (B ε : ℝ) (hB : 0≤B) (hε : 0<ε) :
    ∃K : ℝ,0<K ∧ ∀Z : ℝ,1≤Z → ∀{Label : Type*}[Fintype Label]
      (s : Label→SecondBlockSource) (first : Label→FirstSourceLabel) (seed : Label→Ideal O),
      Function.Injective (fun l=>(first l,seed l,secondBlockCode (s l))) →
      (∀l,Squarefree (seed l)) → (∀l,seed l∣(s l).C ∧ seed l∣(s l).D) →
      ∀(left : Bool)(u₀ : O)(unit : FirstSourceLabel→O)
        (hf : ∀r : secondLiveRows s,
          jointFirstFrequency left u₀ unit (secondEncodedRow s first r)≠0)
        (rows : Finset (secondLiveRows s)) (N : Finset (Fin 4→ℤ))
        (cost : rows→ℝ) (E : ℝ),
      (∀r : rows,((Ideal.span {jointSourceRow left u₀ unit
        (secondEncodedRow s first r.val)}).absNorm:ℝ)≤Z^B) →
      (∀r : secondLiveRows s,(s r.val.1).dyad∈N) → (∀r,0≤cost r) →
      let key := fun r : rows=>secondEncodedNonzeroRow s first r.val left u₀ unit (hf r.val)
      (∀pick : (j : Finset.univ.image key)→ ↥rows,
        (∀j,key (pick j)=j.val) → (∑j : Finset.univ.image key,cost (pick j))≤E) →
      (∑r : rows,cost r)≤((K*Z^ε)*N.card*(Fintype.card RayCharacter:ℝ)^2)*E := by
  obtain ⟨K,hK,hbound⟩ := actual_second_fiber_dyad_budget B ε hB hε
  refine ⟨K,hK,?_⟩
  intro Z hZ Label _ s first seed hinj hseed hdiv left u₀ unit hf rows N cost E hnorm hdyad hc
  dsimp only
  intro hjoint
  exact hbound Z hZ s first seed hinj hseed hdiv left u₀ unit hf rows (fun _=>N) N.card
    cost E hnorm (Nat.cast_nonneg _) (fun _=>le_rfl) hdyad hc hjoint

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_second_selected_row_budget

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_second_fiber_dyad_budget
