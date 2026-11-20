/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Recenter the actual four counts on one Q.2 bank subclass before adding
the ordinary witness saving. The constant face uses the actual m. -/
import Candidate.C092.transport.ActualMixedPriceAll
set_option autoImplicit false
namespace QRH.Cycle092.MixedCenteredFaces
noncomputable section
open QRH.Cycle090 QRH.Cycle092.ActualMixedPrice QRH.Cycle092.TopData

def center (k x z m h : ℝ) : ℝ := max (k*(x-2*m)) (max h (2*k*max 0 (z-m)))

theorem directed_penalty {k lo hi x z m M ξ step fee h : ℝ}
    (h₀ : 0 ≤ lo) (hk : lo ≤ k) (hk' : k ≤ hi) (hm : m ≤ M)
    (hx : 0 ≤ ξ) (hfee : 0 ≤ fee)
    (hsupport : 3*m-ξ-fee ≤ x+z) :
    witnessPenalty lo hi (-hi*(ξ+fee)) h M z ≤ k*(z-m)+center k x z m h := by
  have hp := h₀.trans hk
  have hsign : witnessSignedCoefficient lo hi (z-M)*(z-M) ≤ k*(z-m) := by
    unfold witnessSignedCoefficient
    split_ifs with hh
    · exact (mul_le_mul_of_nonpos_right hk' hh.le).trans (mul_le_mul_of_nonneg_left (by linarith) hp)
    · exact (mul_le_mul_of_nonneg_right hk (le_of_not_gt hh)).trans (mul_le_mul_of_nonneg_left (by linarith) hp)
  have hI : k*(x-2*m) ≤ center k x z m h := le_max_left _ _
  have hH : h ≤ center k x z m h := (le_max_left _ _).trans (le_max_right _ _)
  have hO : 2*lo*max 0 (z-M) ≤ center k x z m h := by
    refine (mul_le_mul (show 2*lo ≤ 2*k by linarith) (max_le_max_left 0 (by linarith))
       (le_max_left _ _) (by linarith)).trans ((le_max_right _ _).trans (le_max_right _ _))
  unfold witnessPenalty
  refine max_le ?_ (add_le_add hsign (max_le hH hO))
  have hpay := mul_le_mul_of_nonneg_left hsupport hp
  have hcollar := mul_le_mul_of_nonneg_right hk' (add_nonneg hx hfee)
  nlinarith only [hI,hpay,hcollar]

/-- The baseline and ordinary bound together give the positive part. -/
theorem centered_count {ι : Type*} (rows : Finset ι) {U C R δ A k x z m h loss : ℝ}
    (hU : 1 ≤ U) (hδ : 0 ≤ δ) (hk : 0 ≤ k)
    (hR : R=1-δ*(A+k*(2*m)))
    (hbase : (rows.card:ℝ) ≤ C*U^(R+loss))
    (hinv : (rows.card:ℝ) ≤ C*U^(1-δ*(A+k*x)+loss))
    (hord : (rows.card:ℝ) ≤ C*U^(1-δ*(A+2*k*z)+loss))
    (hprev : (rows.card:ℝ) ≤ C*U^(R-δ*h+loss)) :
    (rows.card:ℝ) ≤ C*U^(R-δ*center k x z m h+loss) := by
  have hI : (rows.card:ℝ) ≤ C*U^(R-δ*(k*(x-2*m))+loss) := by
    simpa only [hR,show 1-δ*(A+k*(2*m))-δ*(k*(x-2*m))+loss=1-δ*(A+k*x)+loss by ring] using hinv
  have hO : (rows.card:ℝ) ≤ C*U^(R-δ*(2*k*max 0 (z-m))+loss) := by
    rcases le_total z m with h|h
    · simpa [max_eq_left (sub_nonpos.mpr h)] using hbase
    · simpa only [max_eq_right (sub_nonneg.mpr h),hR,
        show 1-δ*(A+k*(2*m))-δ*(2*k*(z-m))+loss=1-δ*(A+2*k*z)+loss by ring] using hord
  unfold center
  rcases le_total (k*(x-2*m)) (max h (2*k*max 0 (z-m))) with a|a
  · rw [max_eq_right a]
    rcases le_total h (2*k*max 0 (z-m)) with b|b
    · rw [max_eq_right b]; exact hO
    · rw [max_eq_left b]; exact hprev
  · rw [max_eq_left a];exact hI

theorem tangent_inverse_identity (δ p g₀ g₁ x : ℝ) :
    δ*x+2*(δ*p)*((1-x)/2+g₀-g₁*x) =
      δ*(p*(1+2*g₀)+(1-p*(1+2*g₁))*x) := by ring

/-- Use the actual amplified predecessor when the directed face is positive.
A zero directed face requires only the original paired count. -/
theorem predecessor_count {ι : Type*} (rows : Finset ι)
    {C U R δ v factor ξ step fee m cutoff loss : ℝ} (hU : 1 ≤ U) (hC : 0 ≤ C)
    (hv : 0 ≤ v) (hscale : δ*factor ≤ v) (hR : R=1/6+v*(3*m))
    (hbase : (rows.card:ℝ) ≤ C*U^(R+loss))
    (hprev : 0 < ξ-step-fee → cutoff ≤ 3*m-(ξ-step-fee) ∧ (rows.card:ℝ) ≤ C*U^(1/6+v*cutoff+loss)) :
    (rows.card:ℝ) ≤ C*U^(R-δ*(factor*max 0 (ξ-step-fee))+loss) := by
  by_cases hh : 0 < ξ-step-fee
  · rw [max_eq_right hh.le]
    obtain ⟨hc,hn⟩ := hprev hh
    refine hn.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU ?_) hC)
    nlinarith only [hR,mul_le_mul_of_nonneg_left hc hv,mul_le_mul_of_nonneg_right hscale hh.le]
  · simpa only [max_eq_left (le_of_not_gt hh),mul_zero,sub_zero] using hbase

#print axioms directed_penalty
#print axioms centered_count
#print axioms predecessor_count
end
end QRH.Cycle092.MixedCenteredFaces
