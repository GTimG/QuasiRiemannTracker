/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Fixed actual count/profile coefficient with two tiny powers, uniformly in D*. -/
import Candidate.C092.transport.MixedMiddleReturnPaidSliceNative
set_option autoImplicit false
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorRawFiber
open QRH.Cycle092.MixedOffsetCount

/-- Only source constants, the original finite phase alphabet and the actual
profile enter this coefficient. Live row cardinalities and moments are absent. -/
theorem paid_coefficient_envelope (labels : ℕ) (binCap : ℝ) (K : CountConstants)
    (Cs Cf Csource diag : ℝ) (degree Jw : ℕ)
    (hbcap : 0 ≤ binCap) (hCs : 0<Cs) (hCf : 0<Cf) (hC : 0<Csource) (hdiag : 0 ≤ diag) :
    ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,1 ≤ Z ∧
    ∀(d height Hw window : ℝ) (bins : ℕ),(1/100:ℝ) ≤ d →
      0 ≤ height → 0 ≤ Hw → Hw ≤ height → window ≤ RawTicket.nHi → (bins:ℝ) ≤ binCap →
    max 1 (countCoefficient labels bins (Z^d) height K.K₀ K.Ki K.C₀ K.Cr K.Ci K.J₀ K.Jr K.Ji)*
      paidMoment Cs Cf Csource diag degree Jw (Z^d) height Hw window ≤
    C*(1+height)^(paidCountDegree K+paidMomentDegree degree Jw)*(Z^d)^(1/50000000000000:ℝ) := by
  let sigma : ℝ := 1/100000000000000
  have hs : 0<sigma := by norm_num [sigma]
  obtain ⟨Cd,hCd,hdy⟩ := paid_dyadic_uniform hs
  let A := paidCountConstant labels binCap K
  let B := paidMomentConstant Cs Cf Csource diag
  let L := 1+2*RawTicket.nHi/sigma
  have hA : 0<A := by
    dsimp [A,paidCountConstant]
    positivity [K.C₀_pos.le,K.Cr_pos.le,K.Ci_pos.le,K.Ki_nonneg]
  have hB : 0<B := by dsimp [B,paidMomentConstant];positivity
  have hL : 0<L := by norm_num [L,RawTicket.nHi,sigma]
  refine ⟨A*B*L*Cd,by positivity,?_⟩
  filter_upwards [hdy] with Z hdy
  refine ⟨hdy.1,?_⟩
  intro d height Hw window bins hd hh hHw hfreq hw hb
  have hU : 1 ≤ Z^d := Real.one_le_rpow hdy.1 (by linarith)
  have hc := paid_count_coefficient labels bins binCap K (U:=Z^d) hh hb
  have hm := paid_moment_coefficient (degree:=degree) (Jw:=Jw) hCs.le hCf.le hC.le hdiag hU hh hHw hfreq hw
  have hl := paid_log_window hU hs
  have hd' := hdy.2 d hd
  have hp := mul_le_mul hc hm (by unfold paidMoment;exact zero_le_one.trans (le_max_left _ _))
    (by positivity [hA.le])
  have hlog : 0 ≤ 1+2*RawTicket.nHi*Real.log (Z^d) := by
    have hn : 0 ≤ RawTicket.nHi := by norm_num [RawTicket.nHi]
    positivity [Real.log_nonneg hU]
  have hp' := mul_le_mul hd' hl hlog (by positivity)
  calc
    _ ≤ (A*(1+(dyadicLength (Z^d):ℝ)^2)*(1+height)^(paidCountDegree K))*
      (B*(1+2*RawTicket.nHi*Real.log (Z^d))*(1+height)^(paidMomentDegree degree Jw)) := hp
    _ = A*B*((1+(dyadicLength (Z^d):ℝ)^2)*(1+2*RawTicket.nHi*Real.log (Z^d)))*
      (1+height)^(paidCountDegree K+paidMomentDegree degree Jw) := by rw [pow_add];ring
    _ ≤ A*B*((Cd*(Z^d)^sigma)*(L*(Z^d)^sigma))*
      (1+height)^(paidCountDegree K+paidMomentDegree degree Jw) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp' (by positivity)) (by positivity)
    _ = _ := by
      have he : (Z^d)^sigma*(Z^d)^sigma=(Z^d)^(1/50000000000000:ℝ) := by
        rw [←Real.rpow_add (zero_lt_one.trans_le hU)]
        congr 1
        norm_num [sigma]
      calc
        _ = A*B*L*Cd*(1+height)^(paidCountDegree K+paidMomentDegree degree Jw)*((Z^d)^sigma*(Z^d)^sigma) := by ring
        _ = _ := by rw [he]

#print axioms paid_coefficient_envelope
end
end QRH.Cycle092.MixedMiddleReturn
