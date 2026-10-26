import Candidate.Cycle63.Physical.InitialMass.SecondEnvelopeBudget
import Candidate.Cycle63.Physical.InitialMass.SecondChildCaps

/- Original module: Candidate.Cycle63.Physical.InitialMass.SecondActualRowBudget. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentSecondLocalization CenteredMomentOriginalCommonHarmonic
open CenteredMomentSecondRetainedAggregate CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

/-- The actual retained blocks satisfy the source-key, seed-divisibility,
and dyad-envelope gates of the joint row selection bound. The only
remaining selection is over distinct nonzero joint arithmetic rows. -/
theorem actual_retained_source_row_budget (Brow Bsource L Cr ε : ℝ)
    (hBrow : 0≤Brow) (hBsource : 0≤Bsource) (hL : 0≤L) (hCr : 0<Cr) (hε : 0<ε) :
    ∃K₀ : ℝ,0<K₀ ∧ ∀ᶠ Z : ℝ in atTop,1≤Z ∧
      ∀{α Label : Type}[Fintype α][DecidableEq α][Fintype Label]
        (slots : Label→Finset α)(s : (l : Label)→Input (slots l))
        (R seed : Label→Ideal O)(hseed : ∀l,Squarefree (seed l))
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
        (secondEncodedRow block label r.val)}).absNorm:ℝ)≤Z^Brow) → (∀r,0≤cost r) →
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
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_retained_source_row_budget
end

/- Original module: Candidate.Cycle63.Physical.InitialMass.GeometrySecondCaps. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstCanonicalFamily
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

/-- The actual label-dependent cutoff satisfies the polynomial envelope
needed for second-dyad selection. It holds for either first rectangle. -/
theorem actual_geometry_main_cutoff_cap {ι : Type*}[Fintype ι][DecidableEq ι]
    (reflected : Bool)(s : Input ι)(R seed : Ideal O)(K Z ξ sigma reserve b M : ℝ)
    (N : ℕ)(hK : 0<K)(hZ : 1<Z)(hb : 0<b)(hξ : 0≤ξ)
    (hsigma : 0≤sigma)(hreserve : 0≤reserve)(hKM : K≤Z^M)
    (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)) :
    frequencyRadius (firstMainFourierScale reflected K (volume s) Z ξ sigma reserve b N
      (geometryFirstLabel s R seed K Z ξ hK key j)) Z ξ≤b^(2*N)*Z^(M+ξ/2) := by
  let src := geometryFirstSource s R seed K Z ξ hK key j.1
  have hh := main_fourier_scale_upper reflected src.C src.D
    (Ideal.span {primeSubsetGenerator (fun p : CommonIndex src.C src.D=>p.val) src.inactive})
    src.hC.1 src.hD.1 (subsetGenerator_supported src.C src.D src.hC src.inactive).1
    src.sameSupport K (volume s) Z sigma (frequencyLoss Z 32 ξ) reserve b N
    hK (volume_pos s) hZ hb hsigma (frequencyLoss_nonneg Z 32 ξ hZ (by norm_num) hξ) hreserve
  change firstMainFourierScale reflected K (volume s) Z ξ sigma reserve b N
    (geometryFirstLabel s R seed K Z ξ hK key j)≤b^(2*N)*K at hh
  unfold frequencyRadius
  calc
    _≤(b^(2*N)*K)*Z^(ξ/2) := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg (by linarith) _)
    _≤(b^(2*N)*Z^M)*Z^(ξ/2) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hKM (pow_nonneg hb.le _)) (Real.rpow_nonneg (by linarith) _)
    _=_ := by rw [Real.rpow_add (zero_lt_one.trans hZ)];ring

/-- A single threshold bounds all supported first-child source radii.
It is fixed before the original source, the selected columns and allocations. -/
theorem eventual_geometry_child_source_cap (N : ℕ)(b bs ε : ℝ)
    (hb : 1≤b)(hbs : 1≤bs)(hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀{ι : Type}[Fintype ι][DecidableEq ι]
      (s : Input ι)(A : ℝ),Fintype.card ι≤N → Endpoints b bs bs s → volume s≤Z^A →
      ∀(C R : Ideal O)(B : actualAllocations s.pools C)(χ : Character)(t : ℝ),
      frozenCoefficient B.val C R s.ν s.W s.P≠0 → sourceRadius (child s C R B χ t)≤Z^(A+ε) := by
  filter_upwards [(tendsto_rpow_atTop hε).eventually
    (eventually_ge_atTop (geometry N b bs bs)),eventually_gt_atTop (1:ℝ)] with Z hgeom hZ
  refine ⟨hZ,?_⟩
  intro ι _ _ s A hcard he hV C R B χ t hne
  have hn := norm_ge_one C (allocation_ne s C B)
  have hg : 0≤geometry N b bs bs := (geometry_ge_one N b bs bs hb hbs hbs).trans' (by norm_num)
  calc
    _≤geometry N b bs bs*volume s/(C.absNorm:ℝ) :=
      actual_common_child_source_cap N b bs hb hbs s hcard he C R B χ t hne
    _≤geometry N b bs bs*volume s := div_le_self (mul_nonneg hg (volume_pos s).le) hn
    _≤Z^ε*Z^A := mul_le_mul hgeom hV (volume_pos s).le (Real.rpow_nonneg (by linarith) _)
    _=_ := by rw [←Real.rpow_add (zero_lt_one.trans hZ),add_comm]

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_main_cutoff_cap
#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_geometry_child_source_cap
end
