/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The refined continuous witness keeps the OLD primal band. -/
import Candidate.C092.transport.RawTicketActual
import Candidate.C092.Mixed
import Mathlib.Data.Rat.Floor
set_option autoImplicit false
namespace QRH.Cycle092.RawTicket
noncomputable section
open QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.Mixed QRH.ContactCertificate

def centralBudgetMax : ℝ := (17/250000+1/10^(12:ℕ))/hLower

theorem ceil13_cast (q : ℚ) : (Mixed.ceil13 q:ℝ)=ceilAt (q:ℝ) (10^(13:ℕ)) := by
  have he : (10:ℝ)^13=10000000000000 := by norm_num
  rw [ceilAt,he]
  simp only [Mixed.ceil13,Rat.cast_div,Rat.cast_intCast,Rat.cast_ofNat]
  rw [←Rat.ceil_cast (α:=ℝ)]
  push_cast
  rfl

theorem inner_width_bounds {m γ v d k budget ξ : ℝ}
    (hm : tLo/3≤m ∧ m≤tHi/3) (hv : Vmin≤v ∧ v≤5/6-dLo)
    (hd : dLo≤d) (hk : kMin≤k) (hb : budget≤centralBudgetMax)
    (hγ0 : 0≤γ) (hγ : γ≤4*budget/(3*v)+1/10^(13:ℕ))
    (hξ : 0≤ξ ∧ ξ≤γ) :
    γ≤ innerGammaMax ∧
    innerLeft≤offsetWidth m (1/10^(13:ℕ)) (γ/65536) v d k ξ ∧
    offsetWidth m (1/10^(13:ℕ)) (γ/65536) v d k ξ≤ innerRight := by
  have hv0 : 0<v := lt_of_lt_of_le (by norm_num [Vmin]) hv.1
  have hd0 : 0<d := lt_of_lt_of_le (by norm_num [dLo]) hd
  have hk0 : 0<k := lt_of_lt_of_le (by norm_num [kMin]) hk
  have hdk:=mul_le_mul hd hk (by norm_num [kMin]) hd0.le
  have hbud0 : 0≤centralBudgetMax := by norm_num [centralBudgetMax,hLower]
  have hgquot:=div_le_div₀ (mul_nonneg (by norm_num : (0:ℝ)≤4) hbud0)
    (mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤4))
    (by norm_num [Vmin] : 0<3*Vmin) (by linarith only [hv.1] : 3*Vmin≤3*v)
  have hgmax : γ≤ innerGammaMax := by
    norm_num [centralBudgetMax,hLower,Vmin,innerGammaMax] at *
    linarith only [hγ,hgquot]
  have hvg:=mul_le_mul_of_nonneg_left hγ hv0.le
  have heq : v*(4*budget/(3*v)+1/10^(13:ℕ))=4*budget/3+v/10^(13:ℕ) := by field_simp <;> ring
  rw [heq] at hvg
  have hvγ : v*γ ≤ 4*centralBudgetMax/3+(5/6-dLo)/10^(13:ℕ) := by linarith only [hvg,hb,hv.2]
  have hxq:=div_le_div₀ (by norm_num [centralBudgetMax,hLower,dLo] : 0≤4*centralBudgetMax/3+(5/6-dLo)/10^(13:ℕ))
    hvγ (by norm_num [dLo,kMin] : 0<dLo*kMin) hdk
  have hx : (v/(d*k))*γ≤ innerXMax := by
    have hid : (v/(d*k))*γ=(v*γ)/(d*k) := by ring
    rw [hid]
    apply hxq.trans
    norm_num [centralBudgetMax,hLower,dLo,kMin,innerXMax]
  have hmax : max 0 (ξ-γ/65536-3*(1/10^(13:ℕ)))≤γ := max_le hγ0 (by linarith only [hξ.2,hγ0])
  have hf0 : 0≤v/(d*k) := div_nonneg hv0.le (mul_pos hd0 hk0).le
  have hterm:=mul_le_mul_of_nonneg_left hmax hf0
  have hnterm : 0≤v/(d*k)*max 0 (ξ-γ/65536-3*(1/10^(13:ℕ))) := mul_nonneg hf0 (le_max_left _ _)
  refine ⟨hgmax,?_,?_⟩
  · dsimp [offsetWidth,innerLeft]
    linarith only [hm.1,hξ.2,hgmax,hterm,hx]
  · dsimp [offsetWidth,innerRight,innerYMax]
    linarith only [hm.2,hξ.1,hnterm]

theorem receipt_original_bounds :
    (5805911/100000000:ℝ)≤g0Receipt.lo ∧ (g0Receipt.lo:ℝ)≤5805913/100000000 ∧
    (5805911/100000000:ℝ)≤g0Receipt.hi ∧ (g0Receipt.hi:ℝ)≤5805913/100000000 ∧
    (3799809/50000000:ℝ)≤g1Receipt.lo ∧ (g1Receipt.lo:ℝ)≤379981/5000000 ∧
    (3799809/50000000:ℝ)≤g1Receipt.hi ∧ (g1Receipt.hi:ℝ)≤379981/5000000 := by
  norm_num [g0Receipt,g1Receipt]

theorem crossing_eq_paired (d p a₀ a₁ : ℝ) : crossing d p a₀ a₁=pairedCrossing d p a₀ a₁ := by
  dsimp [crossing,pairedCrossing,U,pairedU]
  congr 2
  dsimp [J,pairedJ,pairedV,pairedK]
  ring

theorem row_inner_parameters {r : Row} (hr : r∈rows) :
    (tLo/3≤(rowM r.box:ℝ) ∧ (rowM r.box:ℝ)≤tHi/3) ∧
    (Vmin≤(rowV r.box:ℝ) ∧ (rowV r.box:ℝ)≤5/6-dLo) ∧
    dLo≤(r.box.uHi:ℝ) ∧ kMin≤(rowKUpper r.box:ℝ) ∧
    (rowBudget r.B:ℝ)≤centralBudgetMax ∧
    0≤(rowGamma r.box r.B:ℝ) ∧
    (rowGamma r.box r.B:ℝ)≤4*(rowBudget r.B:ℝ)/(3*(rowV r.box:ℝ))+1/10^(13:ℕ) := by
  have h:=row_endpoint_hull hr
  have hreceipt:=receipt_original_bounds
  have hc:=crossing_bounds h.2.1 h.2.2.1 ⟨hreceipt.1,hreceipt.2.1⟩ ⟨hreceipt.2.2.2.2.2.2.1,hreceipt.2.2.2.2.2.2.2⟩
  rw [crossing_eq_paired] at hc
  have hm : tLo/3≤(rowM r.box:ℝ) ∧ (rowM r.box:ℝ)≤tHi/3 := by
    rw [rowM_cast];constructor <;> linarith only [hc.2.1,hc.2.2]
  have hv : Vmin≤(rowV r.box:ℝ) ∧ (rowV r.box:ℝ)≤5/6-dLo := by
    norm_num [rowV,Rat.cast_sub,Rat.cast_div,Rat.cast_ofNat,Vmin,dLo,dHi] at *
    constructor <;> linarith only [h.2.1.1,h.2.1.2]
  have hf0 : 0≤(r.box.vLo:ℝ) := (by norm_num [pLo] : (0:ℝ)≤pLo).trans h.2.2.1.1
  have hg10 : 0≤1+2*(g1Receipt.lo:ℝ) := by linarith only [hreceipt.2.2.2.2.1]
  have hp := mul_le_mul h.2.2.1.2 (show 1+2*(g1Receipt.lo:ℝ)≤1+2*(379981/5000000) by linarith only [hreceipt.2.2.2.2.2.1]) hg10 (by norm_num [pHi] : 0≤pHi)
  have hk : kMin≤(rowKUpper r.box:ℝ) := by
    norm_num [rowKUpper,Rat.cast_sub,Rat.cast_mul,Rat.cast_add,Rat.cast_one,Rat.cast_ofNat,kMin,pHi] at hp ⊢
    linarith only [hp]
  have hs:=Top.shape_of_check (List.all_eq_true.mp Top.all_rows_checked r hr)
  have hb0 : 0≤(r.B:ℝ) := Rat.cast_nonneg.mpr hs.1
  have hbmax : (r.B:ℝ)≤17/250000 := by
    have hh:=(hull_of_row hr).2.2.2.2
    simpa only [Rat.cast_div,Rat.cast_ofNat] using ((Rat.cast_le (K:=ℝ)).mpr hh)
  have hb : (rowBudget r.B:ℝ)≤centralBudgetMax := by
    simp only [rowBudget,Rat.cast_div,Rat.cast_add,Rat.cast_max,Rat.cast_zero,Rat.cast_one,Rat.cast_ofNat]
    rw [max_eq_right hb0]
    dsimp [centralBudgetMax]
    norm_num [hLower]
    linarith only [hbmax]
  have hbnn : 0≤(rowBudget r.B:ℝ) := by
    simp only [rowBudget,Rat.cast_div,Rat.cast_add,Rat.cast_max,Rat.cast_zero,Rat.cast_one,Rat.cast_ofNat]
    positivity
  have hgamma : (rowGamma r.box r.B:ℝ)=ceilAt (4*(rowBudget r.B:ℝ)/(3*(rowV r.box:ℝ))) (10^(13:ℕ)) := by
    rw [rowGamma,ceil13_cast]
    push_cast
    rfl
  have hg:=rounding (x:=4*(rowBudget r.B:ℝ)/(3*(rowV r.box:ℝ))) (n:=10^(13:ℕ)) (by norm_num)
  have hq0 : 0≤4*(rowBudget r.B:ℝ)/(3*(rowV r.box:ℝ)) := div_nonneg (mul_nonneg (by norm_num) hbnn) (by have :=hv.1;norm_num [Vmin] at this;linarith)
  exact ⟨hm,hv,h.2.1.1,hk,hb,(hgamma.symm ▸ hq0.trans hg.2.2.1),(hgamma.symm ▸ hg.2.2.2.le)⟩

/-- Genuine closed continuous witness range for every checked mixed row. -/
theorem every_inner_width {r : Row} (hr : r∈rows) {ξ : ℝ}
    (hξ : 0≤ξ ∧ ξ≤(rowGamma r.box r.B:ℝ)) :
    innerLeft≤offsetWidth (rowM r.box) (1/10^(13:ℕ)) ((rowGamma r.box r.B:ℝ)/65536)
      (rowV r.box) r.box.uHi (rowKUpper r.box) ξ ∧
    offsetWidth (rowM r.box) (1/10^(13:ℕ)) ((rowGamma r.box r.B:ℝ)/65536)
      (rowV r.box) r.box.uHi (rowKUpper r.box) ξ≤ innerRight := by
  rcases row_inner_parameters hr with ⟨hm,hv,hd,hk,hb,hg0,hg⟩
  exact (inner_width_bounds hm hv hd hk hb hg0 hg hξ).2

end
end QRH.Cycle092.RawTicket
#print axioms QRH.Cycle092.RawTicket.every_inner_width
