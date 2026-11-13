/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B084
import Candidate.Bundles.B088
import Candidate.Bundles.B115

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondRowBudget; sha256 7678bc82e8b3761cb90c3efa644c2818badcbbe5cf80fe55580cf2732d078fa6 -/
section
                                                   

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment RayFourExpansion
local notation "O" => HeckeFamily.O

/-- The joint density estimate may be applied after selecting one actual
source in each encoded fiber. This applies to any selected row bin and
charges only the first-projector small power, dyads and finite rays. -/
theorem actual_second_fiber_dyad_budget (B ε : ℝ) (hB : 0≤ B) (hε : 0<ε) :
    ∃K : ℝ,0< K ∧ ∀Z : ℝ,1≤ Z → ∀{Label : Type*}[Fintype Label]
      (s : Label→ SecondBlockSource) (first : Label→ FirstSourceLabel) (seed : Label→ Ideal O),
      Function.Injective (fun l=>(first l,seed l,secondBlockCode (s l))) →
      (∀l,Squarefree (seed l)) → (∀l,seed l∣(s l).C ∧ seed l∣(s l).D) →
      ∀(left : Bool)(u₀ : O)(unit : FirstSourceLabel→ O)
        (hf : ∀r : secondLiveRows s,
          jointFirstFrequency left u₀ unit (secondEncodedRow s first r)≠0)
        (rows : Finset (secondLiveRows s))
        (N : NonzeroJointSourceLabel left u₀ unit→ Finset (Fin 4→ℤ)) (D : ℝ)
        (cost : rows→ℝ) (E : ℝ),
      (∀r : rows,((Ideal.span {jointSourceRow left u₀ unit
        (secondEncodedRow s first r.val)}).absNorm:ℝ)≤ Z^B) →
      0≤ D → (∀r : rows,
        (N (secondEncodedNonzeroRow s first r.val left u₀ unit (hf r.val))).card≤ D) →
      (∀r : secondLiveRows s,(s r.val.1).dyad∈N (secondEncodedNonzeroRow s first r left u₀ unit (hf r))) →
      (∀r,0≤ cost r) →
      let key := fun r : rows=>secondEncodedNonzeroRow s first r.val left u₀ unit (hf r.val)
      (∀pick : (j : Finset.univ.image key)→ ↥rows,
        (∀j,key (pick j)=j.val) → (∑j : Finset.univ.image key,cost (pick j))≤ E) →
      (∑r : rows,cost r)≤((K*Z^ε)*D*(Fintype.card RayCharacter:ℝ)^2)*E := by
  obtain ⟨K,hK,hbound⟩ := actual_second_projector_fiber_bound B ε hB hε
  refine ⟨K,hK,?_⟩
  intro Z hZ Label _ s first seed hinj hseed hdiv left u₀ unit hf rows N D cost E hnorm hD hcard hdyad hc
  dsimp only
  intro hjoint
  let key := fun r : rows=>secondEncodedNonzeroRow s first r.val left u₀ unit (hf r.val)
  apply joint_fiber_selection key cost _ E (by positivity) hc _ hjoint
  intro j hj
  have hjnorm : ((Ideal.span {jointSourceRow left u₀ unit j.val}).absNorm:ℝ)≤ Z^B := by
    obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hj
    subst j
    exact hnorm r
  have hcardj : (N j).card≤ D := by
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
theorem actual_second_selected_row_budget (B ε : ℝ) (hB : 0≤ B) (hε : 0<ε) :
    ∃K : ℝ,0< K ∧ ∀Z : ℝ,1≤ Z → ∀{Label : Type*}[Fintype Label]
      (s : Label→ SecondBlockSource) (first : Label→ FirstSourceLabel) (seed : Label→ Ideal O),
      Function.Injective (fun l=>(first l,seed l,secondBlockCode (s l))) →
      (∀l,Squarefree (seed l)) → (∀l,seed l∣(s l).C ∧ seed l∣(s l).D) →
      ∀(left : Bool)(u₀ : O)(unit : FirstSourceLabel→ O)
        (hf : ∀r : secondLiveRows s,
          jointFirstFrequency left u₀ unit (secondEncodedRow s first r)≠0)
        (rows : Finset (secondLiveRows s)) (N : Finset (Fin 4→ℤ))
        (cost : rows→ℝ) (E : ℝ),
      (∀r : rows,((Ideal.span {jointSourceRow left u₀ unit
        (secondEncodedRow s first r.val)}).absNorm:ℝ)≤ Z^B) →
      (∀r : secondLiveRows s,(s r.val.1).dyad∈N) → (∀r,0≤ cost r) →
      let key := fun r : rows=>secondEncodedNonzeroRow s first r.val left u₀ unit (hf r.val)
      (∀pick : (j : Finset.univ.image key)→ ↥rows,
        (∀j,key (pick j)=j.val) → (∑j : Finset.univ.image key,cost (pick j))≤ E) →
      (∑r : rows,cost r)≤((K*Z^ε)*N.card*(Fintype.card RayCharacter:ℝ)^2)*E := by
  obtain ⟨K,hK,hbound⟩ := actual_second_fiber_dyad_budget B ε hB hε
  refine ⟨K,hK,?_⟩
  intro Z hZ Label _ s first seed hinj hseed hdiv left u₀ unit hf rows N cost E hnorm hdyad hc
  dsimp only
  intro hjoint
  exact hbound Z hZ s first seed hinj hseed hdiv left u₀ unit hf rows (fun _=>N) N.card
    cost E hnorm (Nat.cast_nonneg _) (fun _=>le_rfl) hdyad hc hjoint

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_selected_row_budget

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_fiber_dyad_budget

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondRowBudget -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondEnvelopeBudget; sha256 420800abe995c223c1eab254c09625f14276436557c2980e97f2b0103ca44016 -/
section
                                                   
                                                      

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61Moment RayFourExpansion
local notation "O" => HeckeFamily.O

/-- Moving dyad positions cost only their uniform interval cardinalities.
The main radius and cutoff depend on the encoded first label, so each joint
fiber has one envelope even when its first projector varies. -/
theorem actual_second_envelope_row_budget (Brow Bsource L Cr ε : ℝ)
    (hBrow : 0≤ Brow) (hBsource : 0≤ Bsource) (hL : 0≤ L) (hCr : 0< Cr) (hε : 0<ε) :
    ∃K₀ : ℝ,0< K₀ ∧ ∀ᶠ Z : ℝ in atTop,1≤ Z ∧
      ∀{Label : Type*}[Fintype Label](s : Label→ SecondBlockSource)
        (first : Label→ FirstSourceLabel)(seed : Label→ Ideal O)
        (K R : FirstSourceLabel→ℝ)(H : ℝ),
      Function.Injective (fun l=>(first l,seed l,secondBlockCode (s l))) →
      (∀l,Squarefree (seed l)) → (∀l,seed l∣(s l).C ∧ seed l∣(s l).D) →
      (∀l,(s l).K=K (first l) ∧ (s l).radius=R (first l)) →
      (∀l,(s l).radius≤ Cr*Z^L) → H≤ Z^Bsource →
      (∀l,(s l).dyad∈secondDyadEnvelope (s l).C (s l).D (s l).inactive (s l).K (s l).radius H) →
      ∀(left : Bool)(u₀ : O)(unit : FirstSourceLabel→ O)
        (hf : ∀r : secondLiveRows s,jointFirstFrequency left u₀ unit (secondEncodedRow s first r)≠0)
        (rows : Finset (secondLiveRows s))(cost : rows→ℝ)(E : ℝ),
      (∀r : rows,((Ideal.span {jointSourceRow left u₀ unit
        (secondEncodedRow s first r.val)}).absNorm:ℝ)≤ Z^Brow) → (∀r,0≤ cost r) →
      let key := fun r : rows=>secondEncodedNonzeroRow s first r.val left u₀ unit (hf r.val)
      (∀pick : (j : Finset.univ.image key)→ ↥rows,
        (∀j,key (pick j)=j.val) → (∑j : Finset.univ.image key,cost (pick j))≤ E) →
      (∑r : rows,cost r)≤(K₀*Z^(2*ε))*E := by
  obtain ⟨K₁,hK₁,hrows⟩ := actual_second_fiber_dyad_budget Brow ε hBrow hε
  obtain ⟨D₀,hD₀,hdyads⟩ := second_dyad_envelope_subpower Bsource L Cr ε hBsource hL hCr hε
  have hray : (0:ℝ)< Fintype.card RayCharacter := by exact_mod_cast Fintype.card_pos
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
      (N (secondEncodedNonzeroRow s first r.val left u₀ unit (hf r.val))).card≤ D₀*Z^ε := by
    change ((secondDyadEnvelope (s r.val.val.1).C (s r.val.val.1).D (s r.val.val.1).inactive
      (K (first r.val.val.1)) (R (first r.val.val.1)) H).card:ℝ)≤ _
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
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_envelope_row_budget

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondEnvelopeBudget -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondActualRowBudget; sha256 1020c21e339140c3252b1859c045bf6e3c3c2216ec99dc2ed143bfe3aff750a7 -/
section
                                                        

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve Cycle61Moment
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentSecondLocalization CenteredMomentOriginalCommonHarmonic
open CenteredMomentSecondRetainedAggregate CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

/-- The actual retained blocks satisfy the source-key, seed-divisibility,
and dyad-envelope gates of the joint row selection bound. The only
remaining selection is over distinct nonzero joint arithmetic rows. -/
theorem actual_retained_source_row_budget (Brow Bsource L Cr ε : ℝ)
    (hBrow : 0≤ Brow) (hBsource : 0≤ Bsource) (hL : 0≤ L) (hCr : 0< Cr) (hε : 0<ε) :
    ∃K₀ : ℝ,0< K₀ ∧ ∀ᶠ Z : ℝ in atTop,1≤ Z ∧
      ∀{α Label : Type}[Fintype α][DecidableEq α][Fintype Label]
        (slots : Label→ Finset α)(s : (l : Label)→ Input (slots l))
        (R seed : Label→ Ideal O)(hseed : ∀l,Squarefree (seed l))
        (hz₁ : ∀l,(s l).W₁ 0=0)(hz₂ : ∀l,(s l).W₂ 0=0)
        (first : Label→ FirstSourceLabel)(K Tsec : FirstSourceLabel→ℝ)
        (ξ H : ℝ)(hK : ∀l,0< K (first l)),
      Function.Injective (fun l=>(first l,seed l)) →
      (∀l,sourceRadius (s l)≤ H) → H≤ Z^Bsource →
      (∀l,frequencyRadius (Tsec (first l)) Z ξ≤ Cr*Z^L) →
      let Index := (l : Label)×ActualSecondBlockIndex (s l) (R l) (seed l)
        (K (first l)) (Tsec (first l)) Z ξ
      let block := fun q : Index=>(actualSecondBlockDatum (slots q.1) (s q.1) (R q.1) (seed q.1)
        (hseed q.1) (hz₁ q.1) (hz₂ q.1) (K (first q.1)) (Tsec (first q.1)) Z ξ (hK q.1) q.2).block
      let label := fun q : Index=>first q.1
      ∀(left : Bool)(u₀ : O)(unit : FirstSourceLabel→ O)
        (hf : ∀r : secondLiveRows block,jointFirstFrequency left u₀ unit (secondEncodedRow block label r)≠0)
        (rows : Finset (secondLiveRows block))(cost : rows→ℝ)(E : ℝ),
      (∀r : rows,((Ideal.span {jointSourceRow left u₀ unit
        (secondEncodedRow block label r.val)}).absNorm:ℝ)≤ Z^Brow) → (∀r,0≤ cost r) →
      let key := fun r : rows=>secondEncodedNonzeroRow block label r.val left u₀ unit (hf r.val)
      (∀pick : (j : Finset.univ.image key)→ ↥rows,
        (∀j,key (pick j)=j.val) → (∑j : Finset.univ.image key,cost (pick j))≤ E) →
      (∑r : rows,cost r)≤(K₀*Z^(2*ε))*E := by
  obtain ⟨K₀,hK₀,hevent⟩ := actual_second_envelope_row_budget
    Brow Bsource L Cr ε hBrow hBsource hL hCr hε
  refine ⟨K₀,hK₀,?_⟩
  filter_upwards [hevent] with Z hz
  refine ⟨hz.1,?_⟩
  intro α Label _ _ _ slots s R seed hseed hz₁ hz₂ first K Tsec ξ H hK hinj hsource hH hcut
    Index block label left u₀ unit hf rows cost E hnorm hcost key hpick
  have hkeys := actual_second_joint_source_keys slots s R seed hseed hz₁ hz₂
    (fun l=>K (first l)) (fun l=>Tsec (first l)) Z ξ hK first hinj
  apply hz.2 block label (fun q=>seed q.1) K (fun l=>frequencyRadius (Tsec l) Z ξ) H
    hkeys (fun q=>hseed q.1) _ (fun q=>⟨rfl,rfl⟩) (fun q=>hcut q.1) hH _
    left u₀ unit hf rows cost E hnorm hcost hpick
  · intro q
    exact ⟨(actual_retained_block_gates (slots q.1) (s q.1) (R q.1) (seed q.1)
      (hseed q.1) (hz₁ q.1) (hz₂ q.1) (K (first q.1)) (Tsec (first q.1)) Z ξ (hK q.1) q.2).1,
      (actual_retained_block_gates (slots q.1) (s q.1) (R q.1) (seed q.1)
      (hseed q.1) (hz₁ q.1) (hz₂ q.1) (K (first q.1)) (Tsec (first q.1)) Z ξ (hK q.1) q.2).2.1⟩
  · intro q
    exact actual_second_dyad_envelope (s q.1) (R q.1) (seed q.1)
      (K (first q.1)) (Tsec (first q.1)) Z ξ H (hsource q.1) q.2

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_retained_source_row_budget

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondActualRowBudget -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryMainRadius; sha256 a8a679220a1f368580be52b59d0e0a9c98bb1d85d4750158e510ac3171f63cdb -/
section
                                                     
                                                        
                                   

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily Cycle61Moment CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCanonicalFirst CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentAmplificationChildInput
open CenteredMomentSectorLocalization CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O

/-- First-stage arithmetic label after fixing the dyad/geometry bin. -/
def geometryFirstLabel {ι : Type*} [Fintype ι] (s : Input ι) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 0< K) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)) : FirstSourceLabel :=
  ⟨j.1.val.1.val,j.1.val.2.1⟩

/-- Recording the arithmetic label and four dyads recovers the entire
original first-source coordinate, including its dependent interval data. -/
theorem first_coordinate_code_injective {ι : Type*} [Fintype ι]
    (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ) :
    Function.Injective (fun q : FirstSourceCoordinate s R seed K Z ξ=>
      ((⟨q.1.val,q.2.1⟩ : FirstSourceLabel),fun i=>(q.2.2 i:ℤ))) := by
  rintro ⟨p,E,n⟩ ⟨p',E',n'⟩ h
  have hp : p.val=p'.val := congrArg (fun x=>x.1.1) h
  have hp' : p=p' := Subtype.ext hp
  cases hp'
  have hE : E=E' := eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.fst h)).2
  cases hE
  have hn : n=n' := funext (fun i=>Subtype.ext (congrFun (congrArg Prod.snd h) i))
  cases hn
  rfl

/-- The first projector alone does not identify a source column: its four
first-stage dyads and two ray characters must also be retained or selected. -/
theorem geometry_first_column_code_injective {ι : Type*} [Fintype ι]
    (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0< K) (key : ℤ×(Fin 5→ℤ)) :
    Function.Injective (fun j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)=>
      (geometryFirstLabel s R seed K Z ξ hK key j,j.2.1.val,
        (fun i=>(j.1.val.2.2 i:ℤ)),j.2.2.1,j.2.2.2)) := by
  rintro ⟨q,L,χ,ψ⟩ ⟨q',L',χ',ψ'⟩ h
  have hq : q=q' := by
    apply Subtype.ext
    apply first_coordinate_code_injective s R seed K Z ξ
    change ((⟨q.val.1.val,q.val.2.1⟩ : FirstSourceLabel),fun i=>(q.val.2.2 i:ℤ))=
      ((⟨q'.val.1.val,q'.val.2.1⟩ : FirstSourceLabel),fun i=>(q'.val.2.2 i:ℤ))
    exact congrArg (fun x=>(x.1,x.2.2.1)) h
  cases hq
  have hL : L=L' := Subtype.ext (congrArg (fun x=>x.2.1) h)
  cases hL
  have hχ : χ=χ' := congrArg (fun x=>x.2.2.2.1) h
  have hψ : ψ=ψ' := congrArg (fun x=>x.2.2.2.2) h
  cases hχ
  cases hψ
  rfl

def firstMainRadius (reflected : Bool) (K V Z ξ sigma reserve : ℝ)
    (l : FirstSourceLabel) : ℝ :=
  mainCommonRadius Z (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ))
    (nominalLog l.1.1 l.1.2
      (Ideal.span {primeSubsetGenerator (fun p : CommonIndex l.1.1 l.1.2=>p.val) l.2.val}) K V Z)
    (Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)) sigma
    (frequencyLoss Z 32 ξ) reserve

def firstMainFourierScale (reflected : Bool) (K V Z ξ sigma reserve b : ℝ) (N : ℕ)
    (l : FirstSourceLabel) : ℝ :=
  (b^N*V/((if reflected then l.1.2 else l.1.1).absNorm:ℝ))^2/
    firstMainRadius reflected K V Z ξ sigma reserve l

theorem first_main_radius_pos (reflected : Bool) (K V Z ξ sigma reserve : ℝ)
    (hZ : 0< Z) (l : FirstSourceLabel) : 0< firstMainRadius reflected K V Z ξ sigma reserve l := by
  unfold firstMainRadius mainCommonRadius
  positivity

/-- The literal main source has a radius depending only on the first
arithmetic label, not the first projector or either common allocation. -/
theorem actual_geometry_main_source_radius {ι : Type*} [Fintype ι]
    (reflected : Bool) (s : Input ι) (R seed : Ideal O) (K Z ξ sigma reserve : ℝ)
    (hK : 0< K) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))
    (B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j))
    (t : ℝ) :
    actualMainSource
      (child s (geometryColumnIdeal reflected s R seed K Z ξ hK key j) R B
        (geometryColumnCharacter reflected s R seed K Z ξ hK key j) t)
      (geometryBranch reflected s R seed K Z ξ hK key j) Z sigma 1 ξ reserve =
    normalizedGaussSource
      (child s (geometryColumnIdeal reflected s R seed K Z ξ hK key j) R B
        (geometryColumnCharacter reflected s R seed K Z ξ hK key j) t)
      (R*geometryColumnIdeal reflected s R seed K Z ξ hK key j) j.2.1.val ballProfile
      (firstMainRadius reflected K (volume s) Z ξ sigma reserve
        (geometryFirstLabel s R seed K Z ξ hK key j)) := by
  simp only [actualMainSource,geometryBranch,firstMainRadius,geometryFirstLabel,mul_one]
  rfl

/-- A declared Fourier scale depending only on that same label dominates
the actual common child's squared volume divided by its main radius. -/
theorem actual_geometry_main_fourier_admissible {ι : Type*} [Fintype ι]
    (reflected : Bool) (s : Input ι) (R seed : Ideal O) (K Z ξ sigma reserve b : ℝ)
    (N : ℕ) (hK : 0< K) (hZ : 0< Z) (hb : 1≤ b) (hcard : Fintype.card ι≤ N) (hs : s.upper≤ b)
    (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))
    (B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j))
    (t : ℝ)
    (hne : frozenCoefficient B.val (geometryColumnIdeal reflected s R seed K Z ξ hK key j)
      R s.ν s.W s.P≠0) :
    let l := geometryFirstLabel s R seed K Z ξ hK key j
    (volume (child s (geometryColumnIdeal reflected s R seed K Z ξ hK key j) R B
      (geometryColumnCharacter reflected s R seed K Z ξ hK key j) t))^2/
        firstMainRadius reflected K (volume s) Z ξ sigma reserve l≤
      firstMainFourierScale reflected K (volume s) Z ξ sigma reserve b N l := by
  dsimp only
  exact Cycle61FinalRadius.actual_second_radius_admissible N b hb s hcard hs _ R B _ t _
    (first_main_radius_pos reflected K (volume s) Z ξ sigma reserve hZ _) hne

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.first_main_radius_pos
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_source_radius
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_fourier_admissible

#print axioms OAI.SevenEighths.Cycle61InitialMass.first_coordinate_code_injective
#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_first_column_code_injective

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryMainRadius -/
