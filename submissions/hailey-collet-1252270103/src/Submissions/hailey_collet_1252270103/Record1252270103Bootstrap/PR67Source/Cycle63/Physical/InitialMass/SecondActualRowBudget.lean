import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondEnvelopeBudget
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.JointHighDensity
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentSecondLocalization CenteredMomentOriginalCommonHarmonic
open CenteredMomentSecondRetainedAggregate CenteredMomentSectorLocalization

/-- The actual retained blocks satisfy the source-key, seed-divisibility,
and dyad-envelope gates of the joint row selection bound. The only
remaining selection is over distinct nonzero joint arithmetic rows. -/
theorem actual_retained_source_row_budget (Brow Bsource L Cr ε : ℝ)
    (hBrow : 0≤Brow) (hBsource : 0≤Bsource) (hL : 0≤L) (hCr : 0<Cr) (hε : 0<ε) :
    ∃K₀ : ℝ,0<K₀ ∧ ∀ᶠ Z : ℝ in atTop,1≤Z ∧
      ∀{α Label : Type}[Fintype α][DecidableEq α][Fintype Label]
        (slots : Label→Finset α)(s : (l : Label)→ Input (slots l))
        (R seed : Label→ Ideal O)(hseed : ∀l,Squarefree (seed l))
        (hz₁ : ∀l,(s l).W₁ 0=0)(hz₂ : ∀l,(s l).W₂ 0=0)
        (first : Label→FirstSourceLabel)(K Tsec : FirstSourceLabel→ℝ)
        (ξ H : ℝ)(hK : ∀l,0<K (first l)),
      Function.Injective (fun l=>(first l,seed l)) →
      (∀l,sourceRadius (s l)≤H) → H≤Z^Bsource →
      (∀l,frequencyRadius (Tsec (first l)) Z ξ≤Cr*Z^L) →
      let Index := (l : Label)×ActualSecondBlockIndex (s l) (R l) (seed l)
        (K (first l)) (Tsec (first l)) Z ξ
      let block := fun q : Index=>(actualSecondBlockDatum (slots q.1) (s q.1) (R q.1) (seed q.1)
        (hseed q.1) (hz₁ q.1) (hz₂ q.1) (K (first q.1)) (Tsec (first q.1)) Z ξ (hK q.1) q.2).block
      let label := fun q : Index=>first q.1
      ∀(left : Bool)(u₀ : O)(unit : FirstSourceLabel→O)
        (hf : ∀r : secondLiveRows block,jointFirstFrequency left u₀ unit (secondEncodedRow block label r)≠0)
        (rows : Finset (secondLiveRows block))(cost : rows→ℝ)(E : ℝ),
      (∀r : rows,((Ideal.span {jointSourceRow left u₀ unit
        (secondEncodedRow block label r.val)}).absNorm:ℝ)≤Z^Brow) → (∀r,0≤ cost r) →
      let key := fun r : rows=>secondEncodedNonzeroRow block label r.val left u₀ unit (hf r.val)
      (∀pick : (j : Finset.univ.image key)→ ↥rows,
        (∀j,key (pick j)=j.val) → (∑j : Finset.univ.image key,cost (pick j))≤E) →
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
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
