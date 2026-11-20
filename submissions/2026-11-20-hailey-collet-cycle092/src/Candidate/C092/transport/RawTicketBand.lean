/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal old-fee thresholds and the closed old conductor/primal band. -/
import Candidate.C092.transport.RawTicketEnvelope
set_option autoImplicit false
namespace QRH.Cycle092.RawTicket
noncomputable section
open QRH.Cycle090

def sourceSlope (b : ℝ) := 3/4*(1-b)-9/100-b*(17/200)/4
def funded (debit weight : ℝ) := ceilAt ((max 0 debit+10*oldFee)/weight) (10^(9:ℕ))
def Dlow (a b f e sep : ℝ) := hLower-funded (oldDebit a b f e sep) (sourceSlope b)

theorem funded_bounds {debit weight lower upper : ℝ}
    (hd : debit≤oldDebitCap) (hw : lower≤weight) (hl : 0<lower)
    (hu : budgetMax/lower+1/10^(9:ℕ)≤upper) :
    0≤funded debit weight ∧ funded debit weight≤upper := by
  have hw0 : 0<weight := hl.trans_le hw
  have hb : max 0 debit+10*oldFee≤budgetMax := by
    have hm : max 0 debit≤oldDebitCap := max_le (by norm_num [oldDebitCap]) hd
    dsimp [oldFee,oldDebitCap,budgetMax] at hm ⊢
    linarith only [hm]
  have hquot := div_le_div₀ (by norm_num [budgetMax] : 0≤budgetMax) hb hl hw
  have hr:=rounding (x:=(max 0 debit+10*oldFee)/weight) (n:=10^(9:ℕ)) (by norm_num)
  have hq0 : 0≤(max 0 debit+10*oldFee)/weight := div_nonneg (by have := le_max_left (0:ℝ) debit;norm_num [oldFee];linarith) hw0.le
  exact ⟨hq0.trans hr.2.2.1,le_of_lt (hr.2.2.2.trans_le (by linarith only [hquot,hu]))⟩

theorem source_slope_lower {b : ℝ} (hb : b≤dHi) : slopeMin≤sourceSlope b := by
  dsimp [slopeMin,sourceSlope];linarith

theorem original_conductor_band {a b f e sep : ℝ}
    (ha : dLo≤a ∧ a≤dHi) (hb : dLo≤b ∧ b≤dHi)
    (hf : pLo≤f ∧ f≤pHi) (he : pLo≤e ∧ e≤pHi) :
    Dmin≤Dlow a b f e sep ∧ Dlow a b f e sep≤hLower := by
  have hd:=old_debit_bound ha hb hf he (sep:=sep)
  have hh:=funded_bounds hd (source_slope_lower hb.2)
    (by norm_num [slopeMin,dHi] : 0<slopeMin)
    (show budgetMax/slopeMin+1/10^(9:ℕ)≤hLower-Dmin by
      norm_num [budgetMax,slopeMin,dHi,hLower,Dmin])
  dsimp [Dlow];constructor <;> linarith only [hh.1,hh.2]

/-- All seven original discarded-branch thresholds, in order:
conductor, v, down reciprocal, up reciprocal, x, y, gamma. -/
def originalThresholds (debit D a b e : ℝ) : List (ℝ × ℝ) :=
  let k := 1-e*(1+2*(379981/5000000))
  let V := 5/6-b
  [(sourceSlope b,funded debit (sourceSlope b)),
   (D*a/4,funded debit (D*a/4)),
   (D/10,funded debit (D/10)),
   (27*D/100,funded debit (27*D/100)),
   (3*D*a*k/4,funded debit (3*D*a*k/4)),
   (3*D*a*k/2,funded debit (3*D*a*k/2)),
   (3*D*V/4,funded debit (3*D*V/4))]

theorem original_thresholds_uniform {debit D a b e : ℝ}
    (hd : debit≤oldDebitCap) (hD : Dmin≤D) (ha : dLo≤a)
    (hb : b≤dHi) (he : e≤pHi) :
    funded debit (D*a/4)≤vMax ∧
    funded debit (D/10)≤downMax ∧
    funded debit (27*D/100)≤upMax ∧
    funded debit (3*D*a*(1-e*(1+2*(379981/5000000)))/4)≤xMax ∧
    funded debit (3*D*a*(1-e*(1+2*(379981/5000000)))/2)≤yMax ∧
    funded debit (3*D*(5/6-b)/4)≤gammaMax := by
  have hD0 : 0≤D := by norm_num [Dmin] at hD;linarith
  have ha0 : 0≤a := by norm_num [dLo] at ha;linarith
  have hDa:=mul_le_mul hD ha (by norm_num [dLo]) hD0
  have hk : kMin≤1-e*(1+2*(379981/5000000)) := by norm_num [pHi,kMin] at he ⊢;linarith
  have hDak:=mul_le_mul hDa hk (by norm_num [kMin]) (mul_nonneg hD0 ha0)
  have hV : Vmin≤5/6-b := by norm_num [Vmin,dHi] at hb ⊢;linarith
  have hDV:=mul_le_mul hD hV (by norm_num [Vmin]) hD0
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact (funded_bounds hd (by linarith only [hDa] : Dmin*dLo/4≤D*a/4)
      (by norm_num [Dmin,dLo]) (by norm_num [budgetMax,Dmin,dLo,vMax])).2
  · exact (funded_bounds hd (by linarith only [hD] : Dmin/10≤D/10)
      (by norm_num [Dmin]) (by norm_num [budgetMax,Dmin,downMax])).2
  · exact (funded_bounds hd (by linarith only [hD] : 27*Dmin/100≤27*D/100)
      (by norm_num [Dmin]) (by norm_num [budgetMax,Dmin,upMax])).2
  · exact (funded_bounds hd (by linarith only [hDak] : 3*(Dmin*dLo)*kMin/4≤3*D*a*(1-e*(1+2*(379981/5000000)))/4)
      (by norm_num [Dmin,dLo,kMin]) (by norm_num [budgetMax,Dmin,dLo,kMin,xMax])).2
  · exact (funded_bounds hd (by linarith only [hDak] : 3*(Dmin*dLo)*kMin/2≤3*D*a*(1-e*(1+2*(379981/5000000)))/2)
      (by norm_num [Dmin,dLo,kMin]) (by norm_num [budgetMax,Dmin,dLo,kMin,yMax])).2
  · exact (funded_bounds hd (by linarith only [hDV] : 3*Dmin*Vmin/4≤3*D*(5/6-b)/4)
      (by norm_num [Dmin,Vmin]) (by norm_num [budgetMax,Dmin,Vmin,gammaMax])).2

theorem original_thresholds_paid {debit D a b e : ℝ}
    (hD : Dmin≤D) (ha : dLo≤a) (hb : b≤dHi) (he : e≤pHi) :
    ∀ pair∈originalThresholds debit D a b e, 8*oldFee<pair.1*pair.2-debit := by
  have hD0 : 0<D := lt_of_lt_of_le (by norm_num [Dmin]) hD
  have ha0 : 0<a := lt_of_lt_of_le (by norm_num [dLo]) ha
  have hs : 0<sourceSlope b := lt_of_lt_of_le (by norm_num [slopeMin,dHi]) (source_slope_lower hb)
  have hk : 0<1-e*(1+2*(379981/5000000)) := by norm_num [pHi] at he;linarith
  have hV : 0<5/6-b := by norm_num [dHi] at hb;linarith
  intro pair hp
  simp only [originalThresholds,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    exact ceil_funds_original_fee (by positivity)

/-- Original primal endpoints, including both original 15-digit upward rounds. -/
def primalLo (D : ℝ) := 1-(hUpper-2*ell)/D
def primalHi (v : ℝ) := ceilAt (ceilAt ((2*ell+rowPad)/(hLower+rowPad)) (10^(15:ℕ))+v+oldAnn) (10^(15:ℕ))

theorem original_primal_band {D v : ℝ} (hD : Dmin≤D) (hv : v≤vMax) :
    nLo≤primalLo D ∧ primalHi v≤nHi := by
  have hq:=div_le_div₀ (by norm_num [hUpper,ell,theta] : 0≤hUpper-2*ell)
    (le_refl (hUpper-2*ell)) (by norm_num [Dmin] : 0<Dmin) hD
  have hp0 : 0≤rowPad := by unfold rowPad;positivity
  have hpad : rowPad≤1/10^(20:ℕ) := by
    change 1/(10:ℝ)^258≤1/(10:ℝ)^20
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
  have ht : (2*ell+rowPad)/(hLower+rowPad) ≤ (2*ell+1/10^(20:ℕ))/hLower := by
    apply div_le_div₀ (by norm_num [ell,theta]) (by linarith only [hpad])
      (by norm_num [hLower]) (by linarith only [hp0])
  have h₁:=(rounding (x:=(2*ell+rowPad)/(hLower+rowPad)) (n:=10^(15:ℕ)) (by norm_num)).2.2.2
  have h₂:=(rounding (x:=ceilAt ((2*ell+rowPad)/(hLower+rowPad)) (10^(15:ℕ))+v+oldAnn) (n:=10^(15:ℕ)) (by norm_num)).2.2.2
  constructor
  · dsimp [primalLo];norm_num [nLo,hUpper,ell,theta,Dmin] at *;linarith only [hq]
  · dsimp [primalHi];norm_num [nHi,vMax,oldAnn,ell,theta,hLower] at *;linarith only [ht,h₁,h₂,hv]

end
end QRH.Cycle092.RawTicket
