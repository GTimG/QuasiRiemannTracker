/- Coarse bounds for literal depth-indexed returned forests. Source caps
and full-key injection give uniformity before whole-source selection. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.CoarseActualCarrierBound
import Candidate.Research.RecursiveAffine.DepthReturnedFamily

set_option autoImplicit false
set_option maxHeartbeats 350000
namespace OAI.SevenEighths.Cycle153JointCount
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle63Moment Cycle153SourceReturn

section Reindex
variable {Base : Type} {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
  {hH : RayOrthogonality.globalUnits M≤H} {base : Base→Character} {eta : Character}
  {Z B T : ℝ} {left : Bool} {v v' : O} {unit : FirstSourceLabel→O}
private def reindexRecord (R : SecondStepHighCount M H hH base eta Z B T left v unit)
    (h : v=v') : SecondStepHighCount M H hH base eta Z B T left v' unit := h ▸ R
private theorem reindexRecord_value (R : SecondStepHighCount M H hH base eta Z B T left v unit)
    (h : v=v') : (reindexRecord R h).value=R.value := by cases h;rfl
private theorem reindexRecord_card (R : SecondStepHighCount M H hH base eta Z B T left v unit)
    (h : v=v') : Fintype.card (reindexRecord R h).Class=Fintype.card R.Class := by cases h;rfl
private theorem reindexRecord_pays (R : SecondStepHighCount M H hH base eta Z B T left v unit)
    (h : v=v') {q scale len amp loss : ℝ} (hp : R.Pays q scale len amp loss) :
    (reindexRecord R h).Pays q scale len amp loss := by cases h;exact hp
end Reindex

/-- Bind the proved native-Pays coarse bound to one actual depth of the
constructed forest. Multiplier transport uses its literal history identity;
units, source weights and actual records are never replaced. Constants are
chosen before the actual family, physical configuration or Mellin height. -/
theorem depth_family_component_coarse_bound {Depth : Type} [Fintype Depth]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    {Base : Depth→Type} [∀d,Fintype (Base d)] (d : Depth)
    (Bsrc B loss : ℝ) (hBsrc : 0≤Bsrc) (hB : 0≤B) (hloss : 0<loss)
    (n : ℕ) (hbudget : (n:ℝ)*Bsrc≤B) :
    ∃J : ℕ,∀(base : (d : Depth)→Character→Base d→Character)(eta : Character),
    ∃C : ℝ,0<C ∧
    ∀(junction : Depth→ℝ)(Z T : ℝ)(root : O),2≤Z → 0≤T →
    ∀F : DepthReturnedFamily M H hH junction Base base eta Z B T root,
    ∀(boxes : ℕ→Finset (Fin 4→ℤ))(units : ∀k,History k→FirstSourceLabel→O)
      (lefts : ℕ→Bool)(code : F.Prefix d→History n),
      Function.Injective code →
      (∀p,F.multiplier d p=historyMultiplier units lefts root n (code p)) →
    ∀(K S A Amp Loss V weightCap : ℝ),3/5≤junction d →
      0≤K → 0≤S → 0≤A → 0≤Amp → 0≤V →
      (∀p,HistoryFacts units lefts root Z Bsrc boxes n (code p)) →
      (∀p,F.weight d p≤Z^weightCap) →
      (∀p,(F.part d p).scale≤S ∧ (F.part d p).length≤A ∧
        (F.part d p).amp≤Amp ∧ (F.part d p).loss≤Loss ∧
        Real.logb Z ((Ideal.span {F.multiplier d p}).absNorm:ℝ)≤V) →
      (∀b p,(Fintype.card ((F.part d p).record b).Class:ℝ)≤K) →
      ∑p,F.weight d p*(F.part d p).value≤
        C*(∏k∈Finset.range n,(((boxes k).card:ℝ)+1))*(1+T)^J*K*
          Z^(weightCap+Loss+S+A+5*Amp+V+(n:ℝ)*Bsrc+loss) := by
  obtain ⟨J,hJ⟩:=actual_carrier_coarse_returned_bound (Base:=Base d) M H hH
    Bsrc B loss hBsrc hB hloss n hbudget
  refine ⟨J,fun base eta=>?_⟩
  obtain ⟨C,hC,hbound⟩:=hJ (base d eta) eta
  refine ⟨C,hC,?_⟩
  intro junction Z T root hZ hT F boxes units lefts code hcode hmult K S A Amp Loss V weightCap
    hq hK hS hA hAmp hV hvalid hweight hcaps hclass
  have hb:=hbound boxes units lefts root code hcode (fun b p=>(F.part d p).unit b) Z T hZ hT
  let records:=fun b p=>reindexRecord ((F.part d p).record b) (hmult p)
  have hresult:=hb records Finset.univ (F.weight d)
    (fun p=>(F.part d p).scale) (fun p=>(F.part d p).length)
    (fun p=>(F.part d p).amp) (fun p=>(F.part d p).loss)
    (junction d) K S A Amp Loss V weightCap hq hK hS hA hAmp hV
    (fun p _=>hvalid p) (fun p _=>F.weight_nonneg d p)
    (fun p _=>hweight p) (fun p _=>by
      have hc:=hcaps p
      simpa only [←hmult p] using hc)
    (fun b p _=>reindexRecord_pays ((F.part d p).record b) (hmult p) ((F.part d p).pays b))
    (fun b p _=>by
      dsimp only [records]
      rw [reindexRecord_card]
      exact hclass b p)
  simpa only [records,reindexRecord_value,ReturnedPartAt.value] using hresult

/-- The finite sum over terminal depths is bounded before one whole-family
approximate attainer is chosen. The component bounds can be supplied by
`depth_family_component_coarse_bound`; no configuration is summed and no
individual F or depth is maximized separately. -/
theorem bddAbove_whole_depth_family_values
    {Depth : Type} [Fintype Depth] {Config : Type*}
    {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    {hH : RayOrthogonality.globalUnits M≤H}
    {junction : Depth→ℝ} {Base : Depth→Type}
    {base : (d : Depth)→Character→Base d→Character}
    {eta : Character} {Z B T : ℝ} {root : O}
    (family : Config→DepthReturnedFamily M H hH junction Base base eta Z B T root)
    (bound : Depth→ℝ)
    (hbound : ∀c d,∑p,(family c).weight d p*((family c).part d p).value≤bound d) :
    BddAbove (Set.range (fun c=>(family c).value)) := by
  refine ⟨∑d,bound d,?_⟩
  rintro _ ⟨c,rfl⟩
  exact Finset.sum_le_sum (fun d _=>hbound c d)

end
end OAI.SevenEighths.Cycle153JointCount
#print axioms OAI.SevenEighths.Cycle153JointCount.depth_family_component_coarse_bound
#print axioms OAI.SevenEighths.Cycle153JointCount.bddAbove_whole_depth_family_values
