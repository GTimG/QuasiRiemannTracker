/- Native joint-density payment on constructed literal source histories. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.AttachedFamilyHistory
import Candidate.Research.RecursiveAffine.ActualCarrierReturnedSum

set_option autoImplicit false
set_option maxHeartbeats 350000
namespace OAI.SevenEighths.Cycle153JointCount
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle63Moment Cycle153SourceReturn LocalMoment

section Transport
variable {Base : Type} {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    {hH : RayOrthogonality.globalUnits M≤H} {base : Base→Character} {eta : Character}
    {Z B T : ℝ} {b : Bool} {v v' : O} {unit : FirstSourceLabel→O}
private def historyRecord (R : SecondStepHighCount M H hH base eta Z B T b v unit)
    (h : v=v') : SecondStepHighCount M H hH base eta Z B T b v' unit := h ▸ R
private theorem historyRecord_value (R : SecondStepHighCount M H hH base eta Z B T b v unit)
    (h : v=v') : (historyRecord R h).value=R.value := by cases h;rfl
private theorem historyRecord_card (R : SecondStepHighCount M H hH base eta Z B T b v unit)
    (h : v=v') : Fintype.card (historyRecord R h).Class=Fintype.card R.Class := by cases h;rfl
private theorem historyRecord_pays (R : SecondStepHighCount M H hH base eta Z B T b v unit)
    (h : v=v') {q m A a loss : ℝ} (hp : R.Pays q m A a loss) :
    (historyRecord R h).Pays q m A a loss := by cases h;exact hp
private theorem historyRecord_payment (R : SecondStepHighCount M H hH base eta Z B T b v unit)
    (h : v=v') {W E missing : ℝ}
    (hp : ∀c,W*Z^(R.exponent c+R.missExp c+unmarkedDensity (2*R.zeroBin c-1)*R.rowExp c+missing)≤Z^E) :
    ∀c,W*Z^((historyRecord R h).exponent c+(historyRecord R h).missExp c+
      unmarkedDensity (2*(historyRecord R h).zeroBin c-1)*(historyRecord R h).rowExp c+missing)≤Z^E := by
  cases h;exact hp
end Transport

/-- Apply one terminal native density estimate to an actual constructed
family component. `history` is produced by actual source attachment; no
prefix cardinality or injection is separately assumed. The bin domain is
derived from the SAME record's native Pays proof. `hpay` is the literal raw
path/payment inequality, retaining every original edge weight and every
historical missing radical with coefficient one. -/
theorem literal_family_component_returned_bound {Depth : Type} [Fintype Depth]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    {Base : Depth→Type} [∀d,Fintype (Base d)] (d : Depth)
    (Bsrc B loss : ℝ) (hBsrc : 0≤Bsrc) (hB : 0≤B) (hloss : 0<loss)
    (n : Depth→ℕ) (hbudget : (n d:ℝ)*Bsrc≤B) :
    ∃J : ℕ,∀(base : (d : Depth)→Character→Base d→Character)(eta : Character),
    ∃C : ℝ,0<C ∧
    ∀(junction : Depth→ℝ)(Z T : ℝ)(root : O),2≤Z → 0≤T →
    ∀(F : DepthReturnedFamily M H hH junction Base base eta Z B T root)
      (boxes : ℕ→Finset (Fin 4→ℤ))(units : ∀k,History k→FirstSourceLabel→O)(lefts : ℕ→Bool),
    ∀history : LiteralFamilyHistory F n units lefts Bsrc boxes,
    ∀(K E : ℝ),3/5≤junction d → 0≤K →
      (∀b p,(Fintype.card ((F.part d p).record b).Class:ℝ)≤K) →
      (∀b p c,F.weight d p*Z^(((F.part d p).record b).exponent c+
        ((F.part d p).record b).missExp c+
        unmarkedDensity (2*((F.part d p).record b).zeroBin c-1)*((F.part d p).record b).rowExp c+
        F.historyMissing d p)≤Z^E) →
      ∑p,F.weight d p*(F.part d p).value≤
        C*(∏k∈Finset.range (n d),(((boxes k).card:ℝ)+1))*(1+T)^J*K*Z^(E+loss) := by
  obtain ⟨J,hJ⟩:=actual_carrier_returned_sum (Base:=Base d) M H hH Bsrc B loss
    hBsrc hB hloss (n d) hbudget
  refine ⟨J,fun base eta=>?_⟩
  obtain ⟨C,hC,hbound⟩:=hJ (base d eta) eta
  refine ⟨C,hC,?_⟩
  intro junction Z T root hZ hT F boxes units lefts history K E hq hK hclass hpay
  let records:=fun b p=>historyRecord ((F.part d p).record b) (history.multiplier d p)
  have hresult:=hbound boxes units lefts root (history.code d) (history.injective d)
    (fun b p=>(F.part d p).unit b) Z T hZ hT records Finset.univ (F.weight d) K E
    (fun p _=>history.facts d p) (fun p _=>F.weight_nonneg d p) hK
    (fun b p _=>by
      dsimp only [records]
      rw [historyRecord_card]
      exact hclass b p)
    (fun b p _ c=>by
      have hp:=(historyRecord_pays ((F.part d p).record b) (history.multiplier d p) ((F.part d p).pays b)) c
      constructor <;> linarith [hp.1,hp.2.1])
    (fun b p _=>by
      have hp:=historyRecord_payment ((F.part d p).record b) (history.multiplier d p) (hpay b p)
      simpa only [records,history.missing d p] using hp)
  simpa only [records,historyRecord_value,ReturnedPartAt.value] using hresult

end
end OAI.SevenEighths.Cycle153JointCount
#print axioms OAI.SevenEighths.Cycle153JointCount.literal_family_component_returned_bound
