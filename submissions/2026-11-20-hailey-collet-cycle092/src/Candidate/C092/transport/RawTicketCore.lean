/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uniform conservative admission of the ORIGINAL raw ticket band. The old debit
and the refined central debit are deliberately separate. -/
import Candidate.C092.transport.TopActual
import Mathlib.Algebra.Order.Floor.Ring
set_option autoImplicit false
namespace QRH.Cycle092.RawTicket
noncomputable section

def dLo : ℝ := 809/2048
def dHi : ℝ := 905/2048
def pLo : ℝ := 2017/4096
def pHi : ℝ := 1/2
def oldDebitCap : ℝ := 127/1000000
def oldFee : ℝ := 1/1000000000
def oldAnn : ℝ := 1/100000000
def tLo : ℝ := 11139/10000
def tHi : ℝ := 5693/5000

def Hull (r : QRH.Cycle092.TopData.Row) : Prop :=
  (809/2048:ℚ) ≤ r.box.uLo ∧ r.box.uHi ≤ (905/2048:ℚ) ∧
  (2017/4096:ℚ) ≤ r.box.vLo ∧ r.box.vHi ≤ (1/2:ℚ) ∧ r.B ≤ (17/250000:ℚ)
instance (r : QRH.Cycle092.TopData.Row) : Decidable (Hull r) := inferInstanceAs
  (Decidable ((809/2048:ℚ) ≤ r.box.uLo ∧ r.box.uHi ≤ (905/2048:ℚ) ∧
  (2017/4096:ℚ) ≤ r.box.vLo ∧ r.box.vHi ≤ (1/2:ℚ) ∧ r.B ≤ (17/250000:ℚ)))
def hullCheck (r : QRH.Cycle092.TopData.Row) : Bool := decide (Hull r)

def U (p a₀ a₁ : ℝ) := 1-p*(1+6*a₀-4*a₁)
def J (d p a₁ : ℝ) := 5/2-d*(1+2*p*(1+2*a₁))
def crossing (d p a₀ a₁ : ℝ) := 1+d*U p a₀ a₁/J d p a₁

theorem crossing_bounds {d p a₀ a₁ : ℝ}
    (hd : dLo ≤ d ∧ d ≤ dHi) (hp : pLo ≤ p ∧ p ≤ pHi)
    (h₀ : 5805911/100000000 ≤ a₀ ∧ a₀ ≤ 5805913/100000000)
    (h₁ : 3799809/50000000 ≤ a₁ ∧ a₁ ≤ 379981/5000000) :
    0<J d p a₁ ∧ tLo ≤ crossing d p a₀ a₁ ∧ crossing d p a₀ a₁ ≤ tHi := by
  norm_num [dLo,dHi,pLo,pHi] at hd hp
  have hc : 0 ≤ 1+6*a₀-4*a₁ := by linarith
  have hcL : 104436986/100000000 ≤ 1+6*a₀-4*a₁ := by linarith
  have hcH : 104437006/100000000 ≥ 1+6*a₀-4*a₁ := by linarith
  have hp0 : 0≤p := by linarith
  have hmulL := mul_le_mul (show (2017/4096:ℝ)≤p from hp.1) hcL (by norm_num) hp0
  have hmulH := mul_le_mul hp.2 hcH hc (by norm_num : (0:ℝ)≤1/2)
  have hU : 1-(1/2:ℝ)*(104437006/100000000) ≤ U p a₀ a₁ ∧
      U p a₀ a₁ ≤ 1-(2017/4096:ℝ)*(104436986/100000000) := by
    dsimp [U];constructor <;> linarith
  have hfL : (1+2*(2017/4096:ℝ)*(1+2*(3799809/50000000))) ≤ 1+2*p*(1+2*a₁) := by nlinarith
  have hfH : (1+2*p*(1+2*a₁)) ≤ (1+2*(1/2:ℝ)*(1+2*(379981/5000000))) := by nlinarith
  have hf0 : 0≤1+2*p*(1+2*a₁) := by nlinarith
  have hjL := mul_le_mul hd.2 hfH hf0 (by norm_num : (0:ℝ)≤905/2048)
  have hjH := mul_le_mul hd.1 hfL (by norm_num) (by linarith : 0≤d)
  have hj : (5/2:ℝ)-(905/2048)*(1+2*(1/2)*(1+2*(379981/5000000))) ≤ J d p a₁ ∧
      J d p a₁ ≤ (5/2:ℝ)-(809/2048)*(1+2*(2017/4096)*(1+2*(3799809/50000000))) := by
    dsimp [J];constructor <;> linarith
  have hj0 : 0<J d p a₁ := by linarith
  have hnL := mul_le_mul hd.1 hU.1 (by norm_num) (by linarith : 0≤d)
  have hnH := mul_le_mul hd.2 hU.2 (by linarith [hU.1] : 0≤U p a₀ a₁) (by norm_num : (0:ℝ)≤905/2048)
  refine ⟨hj0,?_,?_⟩
  · dsimp [crossing,tLo]
    have : (1139/10000:ℝ) ≤ d*U p a₀ a₁/J d p a₁ := (le_div_iff₀ hj0).mpr (by nlinarith [hj.2])
    linarith
  · dsimp [crossing,tHi]
    have : d*U p a₀ a₁/J d p a₁ ≤ (693/5000:ℝ) := (div_le_iff₀ hj0).mpr (by nlinarith [hj.1])
    linarith

/-- These directed roundings are the literal mathematical floor/ceiling
operations used by EXTENDED_ENGINE.py, rather than imported JSON verdicts. -/
def floorAt (x n : ℝ) := (⌊x*n⌋:ℝ)/n
def ceilAt (x n : ℝ) := (⌈x*n⌉:ℝ)/n

theorem rounding {x n : ℝ} (hn : 0<n) :
    x-1/n < floorAt x n ∧ floorAt x n ≤ x ∧ x ≤ ceilAt x n ∧ ceilAt x n < x+1/n := by
  have hf:=Int.floor_le (x*n)
  have hff:=Int.lt_floor_add_one (x*n)
  have hc:=Int.le_ceil (x*n)
  have hcc:=Int.ceil_lt_add_one (x*n)
  dsimp [floorAt,ceilAt]
  constructor
  · apply (lt_div_iff₀ hn).mpr
    have : (x-1/n)*n=x*n-1 := by field_simp <;> ring
    rw [this];linarith
  constructor
  · exact (div_le_iff₀ hn).mpr hf
  constructor
  · exact (le_div_iff₀ hn).mpr hc
  · apply (div_lt_iff₀ hn).mpr
    have : (x+1/n)*n=x*n+1 := by field_simp <;> ring
    rw [this];exact hcc

def oldQ (a e : ℝ) := -140952330598569/10^(15:ℕ)+a*(117667768631473/200000000000000-328860096935511/10^(15:ℕ)*e)
def oldJmax (a f : ℝ) := J a f (3799809/50000000)
def oldRhi (a f e : ℝ) := 1-a*(f*(1+2*(5805911/100000000))+2*(1-e*(1+2*(379981/5000000)))*crossing a e (5805913/100000000) (3799809/50000000)/3)
def oldSlope (a f e : ℝ) := -5/12-a*f/4+3*oldRhi a f e/4
def xi : ℝ := 174669171221343715360237/200000000000000000000000-436666397/500000000
/-- The squared stationary separation is retained as an arbitrary nonnegative
input. Its exact value cannot worsen this conservative upper debit bound. -/
def oldMargin (a b f e sep : ℝ) :=
  floorAt ((205830466908273/10^(15:ℕ)*sep^2+(1/2-e)*a*oldQ a e)/oldJmax a f) (10^(15:ℕ))-
    (3+8*b*e)*xi-(22595743/10000000000)*oldSlope a f e

def oldDebit (a b f e sep : ℝ) := ceilAt (-oldMargin a b f e sep) (10^(15:ℕ))

theorem old_debit_bound {a b f e sep : ℝ}
    (ha : dLo≤a ∧ a≤dHi) (hb : dLo≤b ∧ b≤dHi)
    (hf : pLo≤f ∧ f≤pHi) (he : pLo≤e ∧ e≤pHi) :
    oldDebit a b f e sep ≤ oldDebitCap := by
  have ht:=crossing_bounds (a₀:=5805913/100000000) (a₁:=3799809/50000000) ha he (by norm_num) (by norm_num)
  have hj:=(crossing_bounds (a₀:=5805913/100000000) (a₁:=3799809/50000000) ha hf (by norm_num) (by norm_num)).1
  norm_num [dLo,dHi,pLo,pHi] at ha hb hf he
  have hq : 0≤oldQ a e := by
    dsimp [oldQ]
    have hz : 0≤117667768631473/200000000000000-(328860096935511:ℝ)/10^(15:ℕ)*e := by linarith
    have hm:=mul_le_mul_of_nonneg_right ha.1 hz
    nlinarith only [hm,he.2]
  have hnum : 0≤(205830466908273:ℝ)/10^(15:ℕ)*sep^2+(1/2-e)*a*oldQ a e := by
    apply add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) hq
  have hbase:= (rounding (x:=((205830466908273/10^(15:ℕ)*sep^2+(1/2-e)*a*oldQ a e)/oldJmax a f)) (n:=10^(15:ℕ)) (by norm_num)).1
  have hbase0 : 0≤(205830466908273/10^(15:ℕ)*sep^2+(1/2-e)*a*oldQ a e)/oldJmax a f := div_nonneg hnum hj.le
  have hprod := mul_le_mul ha.1 hf.1 (by norm_num) (by linarith : 0≤a)
  have hk : (1-(1/2:ℝ)*(1+2*(379981/5000000))) ≤ 1-e*(1+2*(379981/5000000)) := by linarith
  have hk0 : 0≤1-e*(1+2*(379981/5000000)) := by linarith
  have hterm : (2017/4096:ℝ)*(1+2*(5805911/100000000))+2*(1-(1/2:ℝ)*(1+2*(379981/5000000)))*(11139/10000)/3 ≤
      f*(1+2*(5805911/100000000))+2*(1-e*(1+2*(379981/5000000)))*crossing a e (5805913/100000000) (3799809/50000000)/3 := by
    have hm:=mul_le_mul hk ht.2.1 (by norm_num [tLo]) hk0
    norm_num [tLo] at hm
    nlinarith only [hm,hf.1]
  have htotal:=mul_le_mul ha.1 hterm (by norm_num) (by linarith : 0≤a)
  have hslope : oldSlope a f e ≤ 143/5000 := by
    dsimp [oldSlope,oldRhi];nlinarith only [htotal,hprod]
  have hbe:=mul_le_mul hb.2 he.2 (by linarith : 0≤e) (by norm_num : (0:ℝ)≤905/2048)
  have hr:=(rounding (x:=-oldMargin a b f e sep) (n:=10^(15:ℕ)) (by norm_num)).2.2.2
  dsimp only [oldDebit]
  apply le_of_lt (hr.trans ?_)
  dsimp [oldMargin,oldDebitCap,xi] at *
  nlinarith only [hbase,hbase0,hslope,hbe]

/-- Every original ceil-funded discarded branch retains TEN original fees;
the checker only asks for eight. This includes x/y/r/v dilation branches. -/
theorem ceil_funds_original_fee {debit weight : ℝ} (hw : 0<weight) :
    8*oldFee < weight*ceilAt ((max 0 debit+10*oldFee)/weight) (10^(9:ℕ))-debit := by
  have hr:=(rounding (x:=(max 0 debit+10*oldFee)/weight) (n:=10^(9:ℕ)) (by norm_num)).2.2.1
  have hf:=mul_le_mul_of_nonneg_left hr hw.le
  rw [mul_div_cancel₀ _ hw.ne'] at hf
  have hm:=le_max_right 0 debit
  dsimp [oldFee] at *
  linarith only [hf,hm]

end
end QRH.Cycle092.RawTicket
