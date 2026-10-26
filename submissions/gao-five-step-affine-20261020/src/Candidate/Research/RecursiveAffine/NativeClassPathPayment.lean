/- Pointwise payment for an actual native HIGH class after a physical path. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativePaidPathNode
import Candidate.Research.RecursiveAffine.CorrectedPathPayment
import Candidate.Research.RecursiveAffine.RegionalReturned

set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OAI.SevenEighths.Cycle153JointCount
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle63Moment Cycle153RegionalLow LocalMoment

/-- Discharge the weighted class inequality consumed by the joint count.
The first/second common labels and side cancellation are those of the
actual nodes; native reserve_E supplies every parent payment. The actual
capacity and exact coordinate recurrences supply corrected common/F
credit. Original raw edge products and all historical X1 terms remain.
The certificate premise is the checked corrected scalar budget at this
terminal bin, rather than an assumed bound for a count or an energy. -/
theorem native_class_path_payment
    {Base : Type} {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    {hH : RayOrthogonality.globalUnits M≤H} {base : Base→Character} {eta : Character}
    {Z B T : ℝ} {b : Bool} {v : O} {unit : FirstSourceLabel→O}
    (R : SecondStepHighCount M H hH base eta Z B T b v unit)
    (c : R.Class) (n : ℕ) (nodes : ℕ→NativePaidPathNode Z)
    (m A amp prefixLog D V Red residualF pad scalePad q fees : ℕ→ℝ)
    (qTerminal terminalLoss rootLength modelAmp ampError error reserve weight historyMissing : ℝ)
    (hZ : 1<Z) (hq : 3/5 ≤ qTerminal) (hqn : Cycle63.Arithmetic.q0 ≤ qTerminal)
    (hpays : R.Pays qTerminal (m n) (A n) (amp n) terminalLoss)
    (hnodes : ∀i<n,m i=(nodes i).scale ∧ A i=(nodes i).volumeLength ∧ amp i=(nodes i).amplification)
    (hprefix : prefixLog n=Real.logb Z ((Ideal.span {v}).absNorm:ℝ))
    (hrootPrefix : prefixLog 0=0)
    (hscale : ∀i<n,m (i+1)+prefixLog (i+1)-prefixLog i ≤ (nodes i).coordinate 2+scalePad i)
    (hA : ∀i<n,A (i+1)=A i-D i-V i-Red i)
    (hF : ∀i<n,0 ≤ residualF i)
    (hcapacity : ∀i<n,A (i+1) ≤ A i-D i-(nodes i).commonLog-residualF i+pad i)
    (hrootM : m 0 ≤ 1) (hrootA : A 0 ≤ rootLength)
    (hampError : 0 ≤ ampError)
    (hamp : (∑i∈Finset.range n,amp i)+amp n ≤ modelAmp+ampError)
    (hweight : weight=∏i∈Finset.range n,Z^(m i+(nodes i).shiftedOutside+q i*D i+fees i))
    (hmissing : historyMissing=∑i∈Finset.range n,(nodes i).coordinate 1)
    (herror : terminalLoss+5*ampError+
      (∑i∈Finset.range n,((nodes i).small (2*R.zeroBin c-1)+fees i+
        unmarkedDensity (2*R.zeroBin c-1)*scalePad i+Cycle153.commonLoss (2*R.zeroBin c-1)*pad i)) ≤ error)
    (hcertificate : reserve ≤ Cycle153.correctedJointBudget (2*R.zeroBin c-1)
      (1-(∑i∈Finset.range n,V i)-6*modelAmp)
      (rootLength-(∑i∈Finset.range n,V i)-(∑i∈Finset.range n,Red i)-(∑i∈Finset.range n,D i))
      modelAmp (∑i∈Finset.range n,q i*D i) (∑i∈Finset.range n,V i) (∑i∈Finset.range n,Red i)) :
    weight*Z^(R.exponent c+R.missExp c+
      unmarkedDensity (2*R.zeroBin c-1)*R.rowExp c+historyMissing) ≤ Z^(1-reserve+error) := by
  let delta:=2*R.zeroBin c-1
  let rho:=unmarkedDensity delta
  let cost:=5-6*rho
  let h:=Cycle153.commonLoss delta
  let extra:=fun i=>A i-D i-A (i+1)-(nodes i).commonLog
  have hp:=hpays c
  have hdlo : 3/5 ≤ delta := hq.trans hp.1
  have hdhi : delta ≤ 3/4 := hp.2.1
  have hd0 : 0 ≤ delta := by linarith only [hdlo]
  have hr0 : 0 ≤ rho := (show (0:ℝ) ≤ 2/7 by norm_num).trans (unmarkedDensity_ge_two_sevenths hdhi)
  have hr5 : rho ≤ 5/6 := by
    have hden : 0<3*(5-2*delta) := by linarith only [hdhi]
    have hfrac : (1/6:ℝ) ≤ 10*delta/(3*(5-2*delta)) :=
      (le_div_iff₀ hden).mpr (by linarith only [hdlo])
    dsimp only [rho,unmarkedDensity]
    linarith only [hfrac]
  have hr1 : rho ≤ 1 := by linarith only [hr5]
  have hc0 : 0 ≤ cost := by dsimp only [cost];linarith only [hr5]
  have hc5 : cost ≤ 5 := by dsimp only [cost];linarith only [hr0]
  have hh0 : 0 ≤ h := le_trans (by norm_num) (le_max_left _ _)
  have hparent : ∀i<n,(nodes i).shiftedOutside+(nodes i).coordinate 1+
      rho*(nodes i).coordinate 2+delta*(nodes i).coordinate 3 ≤
      (nodes i).small delta-(m i*(1-rho)-delta*A i-amp i*cost)-(nodes i).saving delta := by
    intro i hi
    have hpi:=(nodes i).payment delta ⟨hqn.trans hp.1,hdhi⟩
    rw [(hnodes i hi).1,(hnodes i hi).2.1,(hnodes i hi).2.2]
    exact hpi
  have hvolume : ∀i<n,A (i+1) ≤ (nodes i).coordinate 3-D i-extra i+0 := by
    intro i hi
    rw [(nodes i).coordinate_three]
    dsimp only [extra]
    rw [←(hnodes i hi).2.1]
    linarith
  have hcredit : ∀i<n,(delta-h)*(V i+Red i) ≤ (nodes i).saving delta+delta*extra i+h*pad i := by
    intro i hi
    exact corrected_common_credit_from_actual_source (A i) (A (i+1)) (D i) (V i) (Red i)
      (nodes i).commonLog (residualF i) (pad i) delta h ((nodes i).saving delta)
      hh0 (hF i hi) (hA i hi) (hcapacity i hi) le_rfl
  have hterminal : R.exponent c-m n+R.missExp c+rho*(R.rowExp c-prefixLog n) ≤
      terminalLoss-(m n*(1-rho)-delta*A n-amp n*cost) := by
    simpa only [hprefix] using hp.2.2
  have hprice:=finite_corrected_physical_path_price n delta rho cost h (R.exponent c) (R.missExp c)
    (R.rowExp c) terminalLoss rootLength modelAmp ampError error m A amp prefixLog
    (fun i=>(nodes i).shiftedOutside) (fun i=>(nodes i).coordinate 1) (fun i=>(nodes i).coordinate 2)
    (fun i=>(nodes i).coordinate 3) (fun i=>(nodes i).small delta) (fun i=>(nodes i).saving delta)
    D extra scalePad (fun _=>0) q fees V Red pad rfl rfl rfl hr0 hr1 hc0 hc5 hd0 hampError
    hparent hscale hvolume hterminal hrootM hrootA hamp hcredit (by simpa only [mul_zero,add_zero] using herror)
  have htarget : (∑i∈Finset.range n,(m i+(nodes i).shiftedOutside+q i*D i+fees i))+
      (R.exponent c+R.missExp c+rho*R.rowExp c+historyMissing) ≤ 1-reserve+error := by
    rw [hrootPrefix] at hprice
    rw [hmissing]
    dsimp only [delta] at hprice
    linarith only [hprice,hcertificate]
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hprod : ∀k : ℕ,(∏i∈Finset.range k,Z^(m i+(nodes i).shiftedOutside+q i*D i+fees i))=
      Z^(∑i∈Finset.range k,(m i+(nodes i).shiftedOutside+q i*D i+fees i)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.prod_range_succ,Finset.sum_range_succ,ih,←Real.rpow_add hZ0]
  rw [hweight,hprod,←Real.rpow_add hZ0]
  exact Real.rpow_le_rpow_of_exponent_le hZ.le htarget

end
end OAI.SevenEighths.Cycle153JointCount
#print axioms OAI.SevenEighths.Cycle153JointCount.native_class_path_payment
