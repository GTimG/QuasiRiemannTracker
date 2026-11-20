/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Original annular middle allowance and original mark/volume ceilings. -/
import Candidate.C092.transport.RawTicketSupport
set_option autoImplicit false
namespace QRH.Cycle092.RawTicket
noncomputable section

def originalNeed (debit D a f e γ : ℝ) :=
  ceilAt (((max 0 debit+10*oldFee)/(D*a)+
    (1-f*(1+2*(3799809/50000000)))*(γ+3*oldAnn)/2+e*oldAnn/2)/f) (10^(9:ℕ))

theorem original_need_paid {debit D a f e γ : ℝ} (hD : 0<D) (ha : 0<a) (hf : 0<f) :
    8*oldFee<D*a*(f*originalNeed debit D a f e γ-
      (1-f*(1+2*(3799809/50000000)))*(γ+3*oldAnn)/2-e*oldAnn/2)-debit := by
  have hr:=(rounding (x:=((max 0 debit+10*oldFee)/(D*a)+
    (1-f*(1+2*(3799809/50000000)))*(γ+3*oldAnn)/2+e*oldAnn/2)/f) (n:=10^(9:ℕ)) (by norm_num)).2.2.1
  have hrf:=mul_le_mul_of_nonneg_left hr hf.le
  rw [mul_div_cancel₀ _ hf.ne'] at hrf
  have hDa:=mul_le_mul_of_nonneg_left hrf (mul_pos hD ha).le
  have heq : D*a*((max 0 debit+10*oldFee)/(D*a)+
    (1-f*(1+2*(3799809/50000000)))*(γ+3*oldAnn)/2+e*oldAnn/2)=
    max 0 debit+10*oldFee+D*a*((1-f*(1+2*(3799809/50000000)))*(γ+3*oldAnn)/2+e*oldAnn/2) := by
    field_simp;ring
  rw [heq] at hDa
  have hm:=le_max_right 0 debit
  dsimp [originalNeed,oldFee] at *
  linarith only [hDa,hm]

theorem original_need_uniform {debit D a f e γ : ℝ}
    (hd : debit≤oldDebitCap) (hD : Dmin≤D) (ha : dLo≤a)
    (hf : pLo≤f ∧ f≤pHi) (he : e≤pHi) (hg : 0≤γ ∧ γ≤gammaMax) :
    originalNeed debit D a f e γ≤needMax := by
  have hD0 : 0≤D := (by norm_num [Dmin] : (0:ℝ)≤Dmin).trans hD
  have hf0 : 0<f := lt_of_lt_of_le (by norm_num [pLo]) hf.1
  have hDa:=mul_le_mul hD ha (by norm_num [dLo]) hD0
  have hb : max 0 debit+10*oldFee≤budgetMax := by
    have hm : max 0 debit≤oldDebitCap := max_le (by norm_num [oldDebitCap]) hd
    dsimp [oldFee,oldDebitCap,budgetMax] at hm ⊢
    linarith only [hm]
  have hquot:=div_le_div₀ (by norm_num [budgetMax] : 0≤budgetMax) hb
    (by norm_num [Dmin,dLo] : 0<Dmin*dLo) hDa
  have hk : 1-f*(1+2*(3799809/50000000))≤kMax := by norm_num [pLo,kMax] at hf ⊢;linarith only [hf.1]
  have hm:=mul_le_mul hk (by linarith only [hg.2] : γ+3*oldAnn≤gammaMax+3*oldAnn)
    (by norm_num [oldAnn];linarith only [hg.1] : 0≤γ+3*oldAnn) (by norm_num [kMax] : 0≤kMax)
  have hnum : (max 0 debit+10*oldFee)/(D*a)+(1-f*(1+2*(3799809/50000000)))*(γ+3*oldAnn)/2+e*oldAnn/2 ≤
      budgetMax/(Dmin*dLo)+kMax*(gammaMax+3*oldAnn)/2+pHi*oldAnn/2 := by
    norm_num [oldAnn] at hm
    norm_num [oldAnn,pHi] at he ⊢
    linarith only [hquot,hm,he]
  have htop:=div_le_div₀ (by norm_num [budgetMax,Dmin,dLo,kMax,gammaMax,oldAnn,pHi] :
      0≤budgetMax/(Dmin*dLo)+kMax*(gammaMax+3*oldAnn)/2+pHi*oldAnn/2)
    hnum (by norm_num [pLo] : 0<pLo) hf.1
  have hr:=(rounding (x:=((max 0 debit+10*oldFee)/(D*a)+
    (1-f*(1+2*(3799809/50000000)))*(γ+3*oldAnn)/2+e*oldAnn/2)/f) (n:=10^(9:ℕ)) (by norm_num)).2.2.2
  dsimp [originalNeed]
  apply le_of_lt (hr.trans_le ?_)
  have hmax : (budgetMax/(Dmin*dLo)+kMax*(gammaMax+3*oldAnn)/2+pHi*oldAnn/2)/pLo+1/10^(9:ℕ)≤needMax := by
    norm_num [budgetMax,Dmin,dLo,kMax,gammaMax,oldAnn,pHi,pLo,needMax]
  linarith only [htop,hmax]

theorem original_mark_volume {n₀ n₁ y₀ y₁ need : ℝ}
    (hn₀ : nLo≤n₀) (hn₁ : n₁≤nHi) (hy₀ : rawYLo≤y₀) (hy₁ : y₁≤rawYHi)
    (hneed : need≤needMax) :
    (1+(5805913/100000000:ℝ)-n₀-(1+2*(3799809/50000000))*y₀)/2+need<1/5 ∧
    (1+(5805913/100000000:ℝ)+n₁+(1-2*(3799809/50000000))*y₁)/2+need<1 := by
  norm_num [nLo,nHi,rawYLo,rawYHi,needMax] at hn₀ hn₁ hy₀ hy₁ hneed ⊢
  constructor <;> linarith only [hn₀,hn₁,hy₀,hy₁,hneed]

end
end QRH.Cycle092.RawTicket
#print axioms QRH.Cycle092.RawTicket.original_need_paid
#print axioms QRH.Cycle092.RawTicket.original_need_uniform
