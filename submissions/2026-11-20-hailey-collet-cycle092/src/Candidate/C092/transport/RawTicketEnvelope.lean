/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Stronger uniform closed-domain guards. All constants are rational; the broad
old-debit envelope remains distinct from the refined central budget. -/
import Candidate.C092.transport.RawTicketCore
set_option autoImplicit false
namespace QRH.Cycle092.RawTicket
noncomputable section

def Dmin : ℝ := 40859/50000
def budgetMax : ℝ := 12701/100000000
def vMax : ℝ := 787/500000
def gammaMax : ℝ := 53/100000
def xMax : ℝ := 619/500000
def yMax : ℝ := 619/1000000
def downMax : ℝ := 311/200000
def upMax : ℝ := 72/125000
def nLo : ℝ := 4237/10000
def nHi : ℝ := 266/625
def rawYLo : ℝ := 36953/100000
def rawYHi : ℝ := 380153/1000000
def innerGammaMax : ℝ := 71/250000
def innerXMax : ℝ := 663/1000000
def innerYMax : ℝ := 83/250000
def innerLeft : ℝ := tLo/3-innerGammaMax-innerXMax-2/10^(13:ℕ)
def innerRight : ℝ := tHi/3+innerYMax+1/10^(13:ℕ)
def kMin : ℝ := 2120019/5000000
def kMax : ℝ := 44310785247/102400000000
def Vmin : ℝ := 2405/6144
def needMax : ℝ := 11/10000
def slopeMin : ℝ := 3/4*(1-dHi)-9/100-dHi*(17/200)/4

def GlobalGuards : Prop :=
  0<Dmin ∧ Dmin*dLo>3/10 ∧
  (1+dHi)/2+27/100<1 ∧ (1+dLo)/2-1/10>51/100 ∧
  0<dLo*(1-pHi)/2-17/200 ∧
  1<tLo-gammaMax ∧ tHi<3/2 ∧
  tLo-gammaMax>2*tHi/3+xMax+oldAnn ∧
  18/25<2*tLo/3-gammaMax-yMax-3*oldAnn ∧
  2*tHi/3+2*xMax+3*oldAnn<311/400 ∧
  1/(QRH.Cycle090.hUpper+1/10^(20:ℕ))-downMax>tHi ∧
  (369/1000:ℝ)≤rawYLo ∧ rawYHi≤243/625 ∧
  (369/1000:ℝ)≤ innerLeft ∧ innerLeft≤ innerRight ∧ innerRight≤243/625 ∧
  innerRight≤nLo ∧ nHi≤(23/20)*innerLeft ∧
  slopeMin>(17/250000+1/10^(12:ℕ))/QRH.Cycle090.hLower ∧
  (1+(5805913/100000000:ℝ)-nLo-(1+2*(3799809/50000000))*rawYLo)/2+needMax<1/5 ∧
  (1+(5805913/100000000:ℝ)+nHi+(1-2*(3799809/50000000))*rawYHi)/2+needMax<1

theorem global_guards : GlobalGuards := by
  norm_num [GlobalGuards,Dmin,dLo,dHi,pHi,tLo,tHi,gammaMax,xMax,yMax,oldAnn,
    downMax,rawYLo,rawYHi,innerLeft,innerRight,innerGammaMax,innerXMax,innerYMax,
    nLo,nHi,needMax,slopeMin,QRH.Cycle090.hLower,QRH.Cycle090.hUpper]

/-- The exact original six continuation gaps, in original source order.
The affine ordinary source retains its literal positive B and L. -/
def continuationGaps (f e thi : ℝ) : List ℝ :=
  let cp := e*(1+2*(5805913/100000000))+(1-f*(1+2*(3799809/50000000)))*2*thi/3
  [311/400+f*(1-311/400)-cp, 9/10-cp,
   311/400+2*f*(3/20-1/10^(7:ℕ))-cp,
   311/400+2*f*((1-1/10^(12:ℕ))-311/400)/(2+1/10^(11:ℕ))-cp,
   (1-(9/2)*(27/1000))+2*f*(27/1000)-cp, 9/10-cp]

theorem continuation_gaps_uniform {f e thi : ℝ}
    (hf : pLo≤f ∧ f≤pHi) (he : pLo≤e ∧ e≤pHi)
    (ht : 0≤thi ∧ thi≤tHi) :
    ∀ gap∈continuationGaps f e thi, (54/100000:ℝ)≤gap := by
  have hk0 : 0≤1-f*(1+2*(3799809/50000000)) := by norm_num [pLo,pHi] at hf;linarith
  have hk : 1-f*(1+2*(3799809/50000000)) ≤ kMax := by norm_num [pLo,kMax] at hf ⊢;linarith
  have hm := mul_le_mul hk ht.2 ht.1 (by norm_num [kMax] : 0≤kMax)
  have hcp : e*(1+2*(5805913/100000000))+(1-f*(1+2*(3799809/50000000)))*2*thi/3 ≤
      (1/2:ℝ)*(1+2*(5805913/100000000))+kMax*2*tHi/3 := by
    norm_num [pHi] at he
    nlinarith only [hm,he.2]
  intro gap hg
  simp only [continuationGaps,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl <;>
    norm_num [pLo,pHi] at hf <;> norm_num [kMax,tHi] at hcp ⊢ <;> linarith only [hf.1,hcp]

/-- Genuine strictly positive fees for all SIX discarded continuation branches,
uniformly on the broadened old physical band. -/
theorem continuation_fees_uniform {debit D a f e thi : ℝ}
    (hd : debit≤oldDebitCap) (hD : Dmin≤D) (ha : dLo≤a)
    (hf : pLo≤f ∧ f≤pHi) (he : pLo≤e ∧ e≤pHi)
    (ht : 0≤thi ∧ thi≤tHi) :
    ∀ gap∈continuationGaps f e thi, 8*oldFee < 3*D*a*gap/4-debit := by
  have hD0 : 0≤D := by norm_num [Dmin] at hD;linarith
  have ha0 : 0≤a := by norm_num [dLo] at ha;linarith
  have hDa:=mul_le_mul hD ha (by norm_num [dLo]) hD0
  intro gap hg
  have hgap:=continuation_gaps_uniform hf he ht gap hg
  have hval:=mul_le_mul hDa hgap (by norm_num) (mul_nonneg hD0 ha0)
  norm_num [Dmin,dLo,oldDebitCap,oldFee] at *
  nlinarith only [hval,hd]

/-- The physically admitted length ratio is checked with the OLD primal band
and the NEW witness interval. Closed endpoints are retained. -/
theorem primal_dual_ratio {n y : ℝ} (hn : nLo≤n ∧ n≤nHi)
    (hy : innerLeft≤y ∧ y≤ innerRight) :
    0<y ∧ 1≤n/y ∧ n/y≤23/20 := by
  have hg:=global_guards
  have hy0 : 0< innerLeft := by norm_num [innerLeft,tLo,innerGammaMax,innerXMax]
  have hrl : innerRight≤nLo := by norm_num [innerRight,tHi,innerYMax,nLo]
  have hratio : nHi≤(23/20)*innerLeft := by norm_num [nHi,innerLeft,tLo,innerGammaMax,innerXMax]
  have hypos : 0<y := hy0.trans_le hy.1
  refine ⟨hypos,(le_div_iff₀ hypos).mpr ?_,(div_le_iff₀ hypos).mpr ?_⟩
  · linarith
  · nlinarith

end
end QRH.Cycle092.RawTicket
