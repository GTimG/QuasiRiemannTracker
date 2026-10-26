/- Coarse uniform bound for the same actual returned forest used in source
selection. This does not use the sharp candidate-price certificate. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.ActualCarrierReturnedSum

set_option autoImplicit false
set_option maxHeartbeats 250000
namespace OAI.SevenEighths.Cycle153JointCount
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass LocalMoment

/-- A genuine native Pays record supplies a coarse weighted class bound.
Only source-domain caps enter; the sharp affine reserve is not assumed. -/
theorem native_pays_coarse_class {Base : Type}
    {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    {hH : RayOrthogonality.globalUnits M≤H} {base : Base→Character}
    {eta : Character} {Z B T : ℝ} {left : Bool} {v : O} {unit : FirstSourceLabel→O}
    (R : SecondStepHighCount M H hH base eta Z B T left v unit)
    {q scale len amp loss S A Amp Loss V : ℝ} (hpays : R.Pays q scale len amp loss)
    (hq : 3/5≤q) (hS : 0≤S) (hA : 0≤A) (hAmp : 0≤Amp) (hV : 0≤V)
    (hscale : scale≤S) (hlen : len≤A) (hamp : amp≤Amp) (hloss : loss≤Loss)
    (hv : Real.logb Z ((Ideal.span {v}).absNorm:ℝ)≤V) (c : R.Class) :
    R.exponent c+R.missExp c+unmarkedDensity (2*R.zeroBin c-1)*R.rowExp c≤
      Loss+S+A+5*Amp+V := by
  have hp := hpays c
  let delta:=2*R.zeroBin c-1
  let rho:=unmarkedDensity delta
  have hdlo : 3/5≤delta := hq.trans hp.1
  have hdhi : delta≤3/4 := hp.2.1
  have hd0 : 0≤delta := by linarith
  have hd1 : delta≤1 := by linarith
  have hr0 : 0≤rho := (show (0:ℝ)≤2/7 by norm_num).trans (unmarkedDensity_ge_two_sevenths hdhi)
  have hr1 : rho≤5/6 := by
    have hden : 0<3*(5-2*delta) := by linarith
    have hfrac : (1/6:ℝ)≤10*delta/(3*(5-2*delta)) :=
      (le_div_iff₀ hden).mpr (by linarith)
    dsimp only [rho,unmarkedDensity]
    linarith
  have hrle1 : rho≤1 := by linarith
  have hc0 : 0≤5-6*rho := by linarith
  have hc5 : 5-6*rho≤5 := by linarith
  have hs : rho*scale≤S :=
    (mul_le_mul_of_nonneg_left hscale hr0).trans
      (by nlinarith only [hS,hrle1])
  have ha : delta*len≤A :=
    (mul_le_mul_of_nonneg_left hlen hd0).trans
      (by nlinarith only [hA,hd1])
  have hamp' : (5-6*rho)*amp≤5*Amp :=
    (mul_le_mul_of_nonneg_left hamp hc0).trans
      (mul_le_mul_of_nonneg_right hc5 hAmp)
  have hv' : rho*Real.logb Z ((Ideal.span {v}).absNorm:ℝ)≤V :=
    (mul_le_mul_of_nonneg_left hv hr0).trans
      (by nlinarith only [hV,hrle1])
  have hpay:=hp.2.2
  change R.exponent c-scale+R.missExp c+
    rho*(R.rowExp c-Real.logb Z ((Ideal.span {v}).absNorm:ℝ))≤
    loss-(scale*(1-rho)-delta*len-amp*(5-6*rho)) at hpay
  nlinarith only [hpay,hs,ha,hamp',hv',hloss]

/-- All actual configurations having these native source caps have one
uniform coarse returned-value bound. Full-key injection derives prefix
multiplicity; no prefix-cardinality bound is supplied. Original positive
source weights are unchanged. Thus, once actual finite source families
are constructed, their normalized whole values are bounded above before
choosing one whole-source approximate maximizer. -/
theorem actual_carrier_coarse_returned_bound {Base : Type} [Fintype Base]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (Bsrc B loss : ℝ) (hBsrc : 0≤Bsrc) (hB : 0≤B) (hloss : 0<loss)
    (n : ℕ) (hbudget : (n:ℝ)*Bsrc≤B) :
    ∃J : ℕ,∀(base : Base→Character)(eta : Character),∃C : ℝ,0<C ∧
    ∀(boxes : ℕ→Finset (Fin 4→ℤ))(units : ∀k,History k→FirstSourceLabel→O)
      (lefts : ℕ→Bool)(root : O){P : Type*}(code : P→History n)
      (hcode : Function.Injective code)(unit : Bool→P→FirstSourceLabel→O)
      (Z T : ℝ),2≤Z → 0≤T →
    ∀R : ∀b p,SecondStepHighCount M H hH base eta Z B T b
      (historyMultiplier units lefts root n (code p)) (unit b p),
    ∀(rows : Finset P)(W scale len amp payLoss : P→ℝ)
      (q K S A Amp Loss V weightCap : ℝ),
      3/5≤q → 0≤K → 0≤S → 0≤A → 0≤Amp → 0≤V →
      (∀p∈rows,HistoryFacts units lefts root Z Bsrc boxes n (code p)) →
      (∀p∈rows,0≤W p) →
      (∀p∈rows,W p≤Z^weightCap) →
      (∀p∈rows,scale p≤S ∧ len p≤A ∧ amp p≤Amp ∧ payLoss p≤Loss ∧
        Real.logb Z ((Ideal.span {historyMultiplier units lefts root n (code p)}).absNorm:ℝ)≤V) →
      (∀b,∀p∈rows,(R b p).Pays q (scale p) (len p) (amp p) (payLoss p)) →
      (∀b,∀p∈rows,(Fintype.card (R b p).Class:ℝ)≤K) →
      ∑p∈rows,W p*∑b,(R b p).value≤
        C*(∏k∈Finset.range n,(((boxes k).card:ℝ)+1))*(1+T)^J*K*
          Z^(weightCap+Loss+S+A+5*Amp+V+(n:ℝ)*Bsrc+loss) := by
  obtain ⟨J,hJ⟩:=actual_carrier_returned_sum (Base:=Base) M H hH Bsrc B loss hBsrc hB hloss n hbudget
  refine ⟨J,fun base eta=>?_⟩
  obtain ⟨C,hC,hbound⟩:=hJ base eta
  refine ⟨C,hC,?_⟩
  intro boxes units lefts root P code hcode unit Z T hZ hT R rows W scale len amp payLoss
    q K S A Amp Loss V weightCap hq hK hS hA hAmp hV hvalid hW hweight hcaps hpays hclass
  have hzero : ∀b,∀p∈rows,∀c,4/5≤(R b p).zeroBin c ∧ (R b p).zeroBin c≤7/8 := by
    intro b p hp c
    have hpay:=hpays b p hp c
    constructor <;> linarith [hq]
  apply hbound boxes units lefts root code hcode unit Z T hZ hT R rows W K
    (weightCap+Loss+S+A+5*Amp+V+(n:ℝ)*Bsrc) hvalid hW hK hclass hzero
  intro b p hp c
  obtain ⟨hs,ha,ham,hl,hv⟩:=hcaps p hp
  have hc:=native_pays_coarse_class (R b p) (hpays b p hp) hq hS hA hAmp hV hs ha ham hl hv c
  have hm:=(historyMissing_bounds units lefts root Z Bsrc (by linarith) boxes n (code p) (hvalid p hp)).2
  have hZ0 : 0<Z := by linarith
  calc W p*Z^((R b p).exponent c+(R b p).missExp c+
      unmarkedDensity (2*(R b p).zeroBin c-1)*(R b p).rowExp c+historyMissing lefts Z n (code p))
      ≤Z^weightCap*Z^((R b p).exponent c+(R b p).missExp c+
        unmarkedDensity (2*(R b p).zeroBin c-1)*(R b p).rowExp c+historyMissing lefts Z n (code p)) :=
          mul_le_mul_of_nonneg_right (hweight p hp) (Real.rpow_nonneg hZ0.le _)
    _=Z^(weightCap+((R b p).exponent c+(R b p).missExp c+
        unmarkedDensity (2*(R b p).zeroBin c-1)*(R b p).rowExp c+historyMissing lefts Z n (code p))) :=
          (Real.rpow_add hZ0 _ _).symm
    _≤Z^(weightCap+Loss+S+A+5*Amp+V+(n:ℝ)*Bsrc) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤Z) (by linarith only [hc,hm])

end
end OAI.SevenEighths.Cycle153JointCount
#print axioms OAI.SevenEighths.Cycle153JointCount.native_pays_coarse_class
#print axioms OAI.SevenEighths.Cycle153JointCount.actual_carrier_coarse_returned_bound
