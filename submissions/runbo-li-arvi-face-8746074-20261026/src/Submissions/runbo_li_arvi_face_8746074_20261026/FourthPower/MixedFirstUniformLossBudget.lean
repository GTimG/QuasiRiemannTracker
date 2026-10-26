/- Copyright (c) 2026 Sil. Apache-2.0.
One loss choice before source allocations. The actual cutoff exponents,
selected padding and chosenParameters are retained. Parent checks Lean.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstPaidCosts

set_option autoImplicit false
namespace Candidate.FourthPower.MixedFirstUniformLossBudget
universe u
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths
open CenteredMomentSectorLocalization
open MixedFirstPaidCosts MixedFirstCutoffs MixedFirstExceptionalApplication

/-- The common event depends only on the fixed dimension and losses.
In particular every shortened ordinary/marked width and the reference
choice occur AFTER the event. No allocation-dependent threshold is used. -/
theorem uniform_actual_gates_varying (N : ℕ) (M BG BX loss : ℝ)
    (hM : 0≤M) (hBG : 0≤BG) (hBX : 0≤BX) (hloss : 0<loss) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      ∀R P S d l c0 : ℝ, 0≤S → 0≤d → 0<c0 →
        P+2*S+4*d<R → (3/4:ℝ)*S<d → ReferenceChoice R P S d l →
      ∀(α : Type u) [Fintype α], ∀q : MixedSupplierFourthRow.Data α,
        Fintype.card α≤N → (∀i,0<q.P i) →
        MixedSelectedVolume.volume q=Z^d →
      ∀Bnorm : ℝ, 0≤Bnorm → Bnorm≤M →
      ∀Kfirst Tfirst : ℝ, 0<Kfirst →
        Gates (chosenParameters M BG BX loss Bnorm R P S d l c0 Z Kfirst Tfirst
          (MixedSelectedVolume.scale q)) := by
  let h := lossStep M BG BX loss
  have hh : 0<h := lossStep_pos M BG BX loss hM hBG hBX hloss
  have hcap : ∀ᶠ Z : ℝ in atTop, max (4:ℝ) ((2:ℝ)^N)≤Z^h :=
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hh)) _
  filter_upwards [hcap,Filter.eventually_gt_atTop (1:ℝ)] with Z hcap hZ
  refine ⟨hZ,?_⟩
  intro R P S d l c0 hS hd hc0 hmixed hnative href
    α instα q hN hP hvolume Bnorm hBnorm hBM Kfirst Tfirst hK
  have hz : 0<Z := zero_lt_one.trans hZ
  have hpad : MixedSelectedVolume.padding q≤Z^h :=
    (MixedSelectedVolume.padding_le q N hN).trans ((le_max_right _ _).trans hcap)
  have hfour : (4:ℝ)≤Z^h := (le_max_left _ _).trans hcap
  have hlog := Real.logb_le_logb_of_le hZ (by norm_num : (0:ℝ)<4) hfour
  rw [Real.logb_rpow hz hZ.ne'] at hlog
  have hfrequency : frequencyLoss Z 1 h+h≤3*h := by
    unfold frequencyLoss
    simp only [mul_one]
    linarith
  have hW := actual_padding_gates q hP Z d h hZ hvolume hpad
  have hb := lossStep_budgets M BG BX loss hM hBG hBX hloss Bnorm hBnorm hBM
  dsimp only at hb
  exact {
    hZ := hZ
    hK := hK
    hW := MixedSelectedVolume.scale_pos q hP
    hc0 := hc0
    hCfirst := le_refl 1
    hξ := hh.le
    hε := hh.le
    hδ := hh.le
    hS := hS
    hd := hd
    mixed := hmixed
    native := hnative
    reference := href
    Wlower := hW.1
    Wupper := hW.2
    frequency := hfrequency
    zero_loss := hb.1
    native_loss := hb.2.1
    exceptional_loss := hb.2.2.1
    tail_loss := hb.2.2.2 }

/-- FullEnergy applies the cutoff at sourceExponent B, not at B. -/
def tailCap (B : ℝ) : ℝ := 25*sourceExponent B+5

def budgetDenominator (B Bseed : ℝ) : ℝ :=
  1+tailCap B+sourceExponent B+Bseed

/-- This step pays the selected fiber, seed count, reference and finite
common sums. The smaller inherited lossStep pays the physical ledger.
rho is a fixed strict reserve before any shortening/allocation. -/
def budgetStep (B Bseed εfinal rho : ℝ) : ℝ :=
  min (rho/100) ((min 1 εfinal)/(100*budgetDenominator B Bseed))

def physicalStep (B Bseed εfinal rho : ℝ) : ℝ :=
  lossStep (sourceExponent B) (sourceExponent B) (sourceExponent B)
    (budgetStep B Bseed εfinal rho)

theorem budget_step_pos (B Bseed εfinal rho : ℝ)
    (hB : 1≤B) (hseed : 0≤Bseed) (hε : 0<εfinal) (hrho : 0<rho) :
    0<budgetStep B Bseed εfinal rho := by
  have hB0 : 0<sourceExponent B := by unfold sourceExponent;linarith
  have hc : 0<tailCap B := by unfold tailCap;positivity
  have hden : 0<budgetDenominator B Bseed := by unfold budgetDenominator;positivity
  unfold budgetStep
  exact lt_min (div_pos hrho (by norm_num))
    (div_pos (lt_min zero_lt_one hε) (by positivity))

/-- These are exactly the three exponents of uniform_grouped_first_energy.
epsilonSum=deltaFiber=deltaSeed=epsilonReference=q. The additive
Bseed*q+q conservatively pays seed mass and the reference loss even on
the centered branch. The actual normExponent and tailExponent remain.
-/
theorem chosen_loss_budgets (B Bseed εfinal rho : ℝ)
    (hB : 1≤B) (hseed : 0≤Bseed) (hε : 0<εfinal) (hrho : 0<rho) :
    let q := budgetStep B Bseed εfinal rho
    let h := physicalStep B Bseed εfinal rho
    let B0 := sourceExponent B
    let Bt := tailExponent B0 h h
    0<q ∧ 0<h ∧ h≤q ∧ h≤1/100 ∧ q≤rho/100 ∧
      (7/10:ℝ)+2*h<1 ∧
      (0≤normExponent B B h ∧ normExponent B B h≤B0) ∧
      (q+5*Bt*h+q+Bt*q)+(Bseed*q+q)≤εfinal ∧
      (B0*h+Bt*q)+(Bseed*q+q)≤εfinal ∧
      (-(2*B0+1)+Bt*q)+(Bseed*q+q)≤-B0 := by
  dsimp only
  let q := budgetStep B Bseed εfinal rho
  let h := physicalStep B Bseed εfinal rho
  let B0 := sourceExponent B
  let Tc := tailCap B
  let den := budgetDenominator B Bseed
  let Bt := tailExponent B0 h h
  have hB0 : 1≤B0 := by dsimp only [B0,sourceExponent];linarith
  have hB00 : 0≤B0 := zero_le_one.trans hB0
  have hTc : 0≤Tc := by dsimp only [Tc,tailCap];positivity
  have hden : 0<den := by dsimp only [den,budgetDenominator];positivity
  have hq : 0<q := budget_step_pos B Bseed εfinal rho hB hseed hε hrho
  have hh : 0<h := lossStep_pos B0 B0 B0 q hB00 hB00 hB00 hq
  have hhsmall : h≤1/100 := lossStep_le B0 B0 B0 q
  have hh1 : h≤1 := by linarith
  have hqsmall : q*(100*den)≤min 1 εfinal :=
    (le_div_iff₀ (by positivity : 0<100*den)).mp
      (show q≤(min 1 εfinal)/(100*den) from min_le_right _ _)
  have hqe : q*(100*den)≤εfinal := hqsmall.trans (min_le_right _ _)
  have hqone : q*(100*den)≤1 := hqsmall.trans (min_le_left _ _)
  have hphys : h*(100*(1+B0+B0+B0))≤q :=
    (le_div_iff₀ (by positivity : 0<100*(1+B0+B0+B0))).mp
      (show h≤q/(100*(1+B0+B0+B0)) from min_le_right _ _)
  have hhq : h≤q := by nlinarith [mul_nonneg hh.le hB00]
  have hBt : Bt≤Tc := by
    dsimp only [Bt,tailExponent,secondExponent,childExponent,Tc,tailCap,B0]
    linarith
  have hBth : Bt*h≤Tc*q := mul_le_mul hBt hhq hh.le hTc
  have hBtq : Bt*q≤Tc*q := mul_le_mul_of_nonneg_right hBt hq.le
  have hB0h : B0*h≤B0*q := mul_le_mul_of_nonneg_left hhq hB00
  have hTq := mul_nonneg hTc hq.le
  have hBq := mul_nonneg hB00 hq.le
  have hseedq := mul_nonneg hseed hq.le
  have hdeneq : den=1+Tc+B0+Bseed := rfl
  have hnorm : 0≤normExponent B B h ∧ normExponent B B h≤B0 := by
    unfold normExponent
    dsimp only [B0,sourceExponent]
    constructor <;> linarith
  refine ⟨hq,hh,hhq,hhsmall,min_le_left _ _,by linarith,hnorm,?_,?_,?_⟩
  · change (q+5*Bt*h+q+Bt*q)+(Bseed*q+q)≤εfinal
    rw [hdeneq] at hqe
    nlinarith
  · change (B0*h+Bt*q)+(Bseed*q+q)≤εfinal
    rw [hdeneq] at hqe
    nlinarith
  · change (-(2*B0+1)+Bt*q)+(Bseed*q+q)≤-B0
    rw [hdeneq] at hqone
    nlinarith

/-- A direct instance of the common event with the actual exceptional
normExponent. R,P,S,d,l,c0, supplier and all allocations remain later.
The proof neither changes the actual Bnorm nor increases the cutoffs. -/
theorem uniform_chosen_gates (N : ℕ) (B Bseed εfinal rho : ℝ)
    (hB : 1≤B) (hseed : 0≤Bseed) (hε : 0<εfinal) (hrho : 0<rho) :
    let q := budgetStep B Bseed εfinal rho
    let h := physicalStep B Bseed εfinal rho
    let B0 := sourceExponent B
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      ∀R P S d l c0 : ℝ, 0≤S → 0≤d → 0<c0 →
        P+2*S+4*d<R → (3/4:ℝ)*S<d → ReferenceChoice R P S d l →
      ∀(α : Type u) [Fintype α], ∀v : MixedSupplierFourthRow.Data α,
        Fintype.card α≤N → (∀i,0<v.P i) → MixedSelectedVolume.volume v=Z^d →
      ∀Kfirst Tfirst : ℝ, 0<Kfirst →
        Gates (chosenParameters B0 B0 B0 q (normExponent B B h)
          R P S d l c0 Z Kfirst Tfirst (MixedSelectedVolume.scale v)) := by
  dsimp only
  have hb := chosen_loss_budgets B Bseed εfinal rho hB hseed hε hrho
  dsimp only at hb
  have hB0 : 0≤sourceExponent B := by unfold sourceExponent;linarith
  filter_upwards [uniform_actual_gates_varying N (sourceExponent B) (sourceExponent B)
    (sourceExponent B) (budgetStep B Bseed εfinal rho) hB0 hB0 hB0 hb.1] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro R P S d l c0 hS hd hc0 hmixed hnative href α instα v hN hP hvol Kfirst Tfirst hK
  exact hZ.2 R P S d l c0 hS hd hc0 hmixed hnative href α v hN hP hvol
    (normExponent B B (physicalStep B Bseed εfinal rho))
    hb.2.2.2.2.2.2.1.1 hb.2.2.2.2.2.2.1.2 Kfirst Tfirst hK

/-- Literal scalar RHS of uniform_grouped_first_energy after the chosen
losses, with seed and reference payment. The physical row-width cap
Neta*K≤Z^R is explicit; no energy hypothesis occurs. Original prefix
and full seed denominators are preserved exactly. -/
theorem normalized_grouped_rhs_paid
    (B Bseed εfinal rho Z R Neta K Nseed pair : ℝ)
    (hB : 1≤B) (hseed : 0≤Bseed) (hε : 0<εfinal) (hrho : 0<rho)
    (hZ : 1≤Z) (hR : 0≤R) (hη : 1≤Neta) (hK : 0≤K)
    (hwidth : Neta*K≤Z^R) (hNs : 0<Nseed) (hNcap : Nseed≤Z^Bseed)
    (hpair : 0<pair) :
    let q := budgetStep B Bseed εfinal rho
    let h := physicalStep B Bseed εfinal rho
    let B0 := sourceExponent B
    let Bt := tailExponent B0 h h
    (Nseed^q*Z^q)*
      (Neta*K*Z^(q+5*Bt*h+q+Bt*q)+K*Z^(B0*h+Bt*q)+
        Z^(-(2*B0+1)+Bt*q))/(pair*Nseed)≤
      3*Z^(R+εfinal)/(pair*Nseed) := by
  dsimp only
  let q := budgetStep B Bseed εfinal rho
  let h := physicalStep B Bseed εfinal rho
  let B0 := sourceExponent B
  let Bt := tailExponent B0 h h
  let e := Bseed*q+q
  have hb := chosen_loss_budgets B Bseed εfinal rho hB hseed hε hrho
  dsimp only at hb
  have hq : 0<q := hb.1
  have hret : (q+5*Bt*h+q+Bt*q)+e≤εfinal := hb.2.2.2.2.2.2.2.1
  have hzero : (B0*h+Bt*q)+e≤εfinal := hb.2.2.2.2.2.2.2.2.1
  have htail : (-(2*B0+1)+Bt*q)+e≤-B0 := hb.2.2.2.2.2.2.2.2.2
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hB0 : 0≤B0 := by dsimp only [B0,sourceExponent];linarith
  have hNsq : Nseed^q≤Z^(Bseed*q) := by
    calc
      _≤(Z^Bseed)^q := Real.rpow_le_rpow hNs.le hNcap hq.le
      _=_ := by rw [←Real.rpow_mul hz.le]
  have hfac : Nseed^q*Z^q≤Z^e := by
    calc
      _≤Z^(Bseed*q)*Z^q := mul_le_mul_of_nonneg_right hNsq (Real.rpow_nonneg hz.le _)
      _=_ := by rw [←Real.rpow_add hz]
  have hKwidth : K≤Z^R :=
    (le_mul_of_one_le_left hK hη).trans hwidth
  have hpowret : Z^e*Z^(q+5*Bt*h+q+Bt*q)≤Z^εfinal := by
    rw [←Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    linarith
  have hpowzero : Z^e*Z^(B0*h+Bt*q)≤Z^εfinal := by
    rw [←Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    linarith
  have hpowtail : Z^e*Z^(-(2*B0+1)+Bt*q)≤Z^(R+εfinal) := by
    rw [←Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    linarith
  have hNk : 0≤Neta*K := mul_nonneg (zero_le_one.trans hη) hK
  have hr : Z^e*(Neta*K*Z^(q+5*Bt*h+q+Bt*q))≤Z^(R+εfinal) := by
    calc
      _=(Neta*K)*(Z^e*Z^(q+5*Bt*h+q+Bt*q)) := by ring
      _≤Z^R*Z^εfinal := mul_le_mul hwidth hpowret
        (mul_nonneg (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hz.le _))
        (Real.rpow_nonneg hz.le _)
      _=_ := by rw [←Real.rpow_add hz]
  have hzterm : Z^e*(K*Z^(B0*h+Bt*q))≤Z^(R+εfinal) := by
    calc
      _=K*(Z^e*Z^(B0*h+Bt*q)) := by ring
      _≤Z^R*Z^εfinal := mul_le_mul hKwidth hpowzero
        (mul_nonneg (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hz.le _))
        (Real.rpow_nonneg hz.le _)
      _=_ := by rw [←Real.rpow_add hz]
  apply div_le_div_of_nonneg_right _ (mul_pos hpair hNs).le
  apply (mul_le_mul_of_nonneg_right hfac (by positivity)).trans
  rw [mul_add,mul_add]
  linarith

end
end Candidate.FourthPower.MixedFirstUniformLossBudget
