import Candidate.Cycle63.Physical.InitialMass.SecondRowBudget
import Candidate.Cycle63.Physical.InitialMass.SecondDyadEnvelope

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment RayFourExpansion
local notation "O" => HeckeFamily.O

/-- Moving dyad positions cost only their uniform interval cardinalities.
The main radius and cutoff depend on the encoded first label, so each joint
fiber has one envelope even when its first projector varies. -/
theorem actual_second_envelope_row_budget (Brow Bsource L Cr ε : ℝ)
    (hBrow : 0≤Brow) (hBsource : 0≤Bsource) (hL : 0≤L) (hCr : 0<Cr) (hε : 0<ε) :
    ∃K₀ : ℝ,0<K₀ ∧ ∀ᶠ Z : ℝ in atTop,1≤Z ∧
      ∀{Label : Type*}[Fintype Label](s : Label→SecondBlockSource)
        (first : Label→FirstSourceLabel)(seed : Label→Ideal O)
        (K R : FirstSourceLabel→ℝ)(H : ℝ),
      Function.Injective (fun l=>(first l,seed l,secondBlockCode (s l))) →
      (∀l,Squarefree (seed l)) → (∀l,seed l∣(s l).C ∧ seed l∣(s l).D) →
      (∀l,(s l).K=K (first l) ∧ (s l).radius=R (first l)) →
      (∀l,(s l).radius≤Cr*Z^L) → H≤Z^Bsource →
      (∀l,(s l).dyad∈secondDyadEnvelope (s l).C (s l).D (s l).inactive (s l).K (s l).radius H) →
      ∀(left : Bool)(u₀ : O)(unit : FirstSourceLabel→O)
        (hf : ∀r : secondLiveRows s,jointFirstFrequency left u₀ unit (secondEncodedRow s first r)≠0)
        (rows : Finset (secondLiveRows s))(cost : rows→ℝ)(E : ℝ),
      (∀r : rows,((Ideal.span {jointSourceRow left u₀ unit
        (secondEncodedRow s first r.val)}).absNorm:ℝ)≤Z^Brow) → (∀r,0≤cost r) →
      let key := fun r : rows=>secondEncodedNonzeroRow s first r.val left u₀ unit (hf r.val)
      (∀pick : (j : Finset.univ.image key)→ ↥rows,
        (∀j,key (pick j)=j.val) → (∑j : Finset.univ.image key,cost (pick j))≤E) →
      (∑r : rows,cost r)≤(K₀*Z^(2*ε))*E := by
  obtain ⟨K₁,hK₁,hrows⟩ := actual_second_fiber_dyad_budget Brow ε hBrow hε
  obtain ⟨D₀,hD₀,hdyads⟩ := second_dyad_envelope_subpower Bsource L Cr ε hBsource hL hCr hε
  have hray : (0:ℝ)<Fintype.card RayCharacter := by exact_mod_cast Fintype.card_pos
  refine ⟨K₁*D₀*(Fintype.card RayCharacter:ℝ)^2,by positivity,?_⟩
  filter_upwards [hdyads,eventually_ge_atTop (1:ℝ)] with Z hdyads hZ
  refine ⟨hZ,?_⟩
  intro Label _ s first seed K R H hinj hseed hdiv hphysical hR hH hdyad
    left u₀ unit hf rows cost E hnorm hc
  dsimp only
  intro hjoint
  let N := fun j : NonzeroJointSourceLabel left u₀ unit=>
    secondDyadEnvelope j.val.2.1.1 j.val.2.1.2 j.val.2.2.val.1
      (K j.val.1) (R j.val.1) H
  have hcard (r : rows) :
      (N (secondEncodedNonzeroRow s first r.val left u₀ unit (hf r.val))).card≤D₀*Z^ε := by
    change ((secondDyadEnvelope (s r.val.val.1).C (s r.val.val.1).D (s r.val.val.1).inactive
      (K (first r.val.val.1)) (R (first r.val.val.1)) H).card:ℝ)≤_
    rw [←(hphysical r.val.val.1).1,←(hphysical r.val.val.1).2]
    exact hdyads _ _ (s r.val.val.1).hC (s r.val.val.1).hD _ _ _ _
      (s r.val.val.1).K_pos (hR _) hH
  have hmem (r : secondLiveRows s) :
      (s r.val.1).dyad∈N (secondEncodedNonzeroRow s first r left u₀ unit (hf r)) := by
    change (s r.val.1).dyad∈secondDyadEnvelope (s r.val.1).C (s r.val.1).D (s r.val.1).inactive
      (K (first r.val.1)) (R (first r.val.1)) H
    rw [←(hphysical r.val.1).1,←(hphysical r.val.1).2]
    exact hdyad _
  have hh := hrows Z hZ s first seed hinj hseed hdiv left u₀ unit hf rows N (D₀*Z^ε)
    cost E hnorm (by positivity) hcard hmem hc hjoint
  apply hh.trans_eq
  rw [show 2*ε=ε+ε by ring,Real.rpow_add (zero_lt_one.trans_le hZ)]
  ring

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_second_envelope_row_budget
