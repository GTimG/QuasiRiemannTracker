import Candidate.Cycle63.Physical.NonexceptionalLedger
import Mathlib.Tactic

/- Original module: Candidate.Cycle63.Physical.MarkedHighReserve. -/
section

namespace Cycle63.Physical
noncomputable section
open Cycle63.Arithmetic OAI.SevenEighths.LocalMoment

/-- Quantitative reserve growth above the lower high-zero cutoff. -/
theorem high_main_reserve_increase {b δ : ℝ}
    (hb : 3401/100000≤b ∧ b≤1/25) (hd : q0≤δ ∧ δ≤3/4) :
    highMainReserve b q0+(δ-q0)/4≤highMainReserve b δ := by
  have hδ : 0<5-2*δ := by linarith [hd.2]
  have hq : 0<5-2*q0 := by norm_num [q0]
  have hden : 0<3*(5-2*δ)*(5-2*q0) := by positivity
  have hn : 0≤50*(1-6*amp b) := by
    have ha := (amp_bounds hb).2
    linarith
  have hprod : 3*(5-2*δ)*(5-2*q0)≤3*(5-2*q0)^2 := by nlinarith [hd.1]
  have hfrac := div_le_div_of_nonneg_left hn hden hprod
  have hbase := high_derivative_reserve hb
  have hder : 1/4≤50*(1-6*amp b)/(3*(5-2*δ)*(5-2*q0))-totalA b := by linarith
  have hid : highMainReserve b δ-highMainReserve b q0=
      (δ-q0)*(50*(1-6*amp b)/(3*(5-2*δ)*(5-2*q0))-totalA b) := by
    unfold highMainReserve unmarkedDensity
    field_simp [hδ.ne',hq.ne',show 5-δ*2≠0 by linarith [hd.2]]
    ring
  have hh := mul_le_mul_of_nonneg_left hder (sub_nonneg.mpr hd.1)
  rw [←hid] at hh
  linarith

/-- The marked-count saving pays for the enlarged affine intercept. -/
theorem marked_high_reserve {b δ : ℝ}
    (hb : 3401/100000≤b ∧ b≤1/25) (hd : q0≤δ ∧ δ≤3/4) :
    720486667/30493190000000≤highMainReserve b δ+73/20000 := by
  have hh := high_main_reserve_bound hb hd
  linarith

/-- The unmarked argument already suffices above delta = 7/10. -/
theorem unmarked_upper_high_reserve {b δ : ℝ}
    (hb : 3401/100000≤b ∧ b≤1/25) (hd : 7/10≤δ ∧ δ≤3/4) :
    720486667/30493190000000≤highMainReserve b δ := by
  have hδ : q0≤δ ∧ δ≤3/4 := by norm_num [q0];constructor <;> linarith [hd.1,hd.2]
  have hh := high_main_reserve_increase hb hδ
  have hr := high_main_reserve_bound hb (show q0≤q0 ∧ q0≤3/4 by
    norm_num [q0])
  norm_num [q0] at hh hr
  linarith [hd.1]

end
end Cycle63.Physical
#print axioms Cycle63.Physical.marked_high_reserve
#print axioms Cycle63.Physical.unmarked_upper_high_reserve
end

/- Original module: Candidate.Cycle63.Physical.CoupledRadicalSaving. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace CoupledRadicalSaving
noncomputable section

/-- Retaining the radical penalty prevents an unbalanced common allocation
from exhausting the source width at the weak unmarked rate. -/
theorem first_common_coupled (ρ δ c d p R E Lc R₀ : ℝ)
    (hρ : 1/4 ≤ ρ) (hρmax : ρ ≤ 2/5)
    (hp : 0 ≤ p) (hpC : p ≤ c) (hpD : p ≤ d) (hRp : R ≤ p)
    (hR₀ : 0 ≤ R₀) (hLc : Lc ≤ 5*(R-R₀)) :
    (1-ρ)*max (c-d) 0-δ*c-(1+ρ)*R-E-
      max (3*c-5*d-R) 0/6+ρ*Lc+R₀ ≤ -(δ-3*ρ/2)*c-E := by
  have hρ0 : 0 ≤ ρ := by linarith
  have hc : 0 ≤ c := by linarith
  have hRc : R ≤ c := hRp.trans hpC
  have hRd : R ≤ d := hRp.trans hpD
  have hnum := mul_le_mul_of_nonneg_left hLc hρ0
  have hcancel := mul_nonneg (show 0 ≤ 5*ρ-1 by linarith) hR₀
  have hpen0 : 0 ≤ max (3*c-5*d-R) 0 := le_max_right _ _
  have hpen : 3*c-5*d-R ≤ max (3*c-5*d-R) 0 := le_max_left _ _
  by_cases hcd : d ≤ c
  · rw [max_eq_left (sub_nonneg.mpr hcd)]
    have hrad := mul_le_mul_of_nonneg_left hRd (show 0 ≤ 4*ρ-1 by linarith)
    by_cases hd : d ≤ c/2
    · have hbalance := mul_le_mul_of_nonneg_left hd (show 0 ≤ 5*ρ-1 by linarith)
      nlinarith
    · have hbalance := mul_le_mul_of_nonneg_left (show c/2 ≤ d by linarith)
        (show 0 ≤ 2-5*ρ by linarith)
      nlinarith
  · rw [max_eq_right (show c-d ≤ 0 by linarith)]
    have hrad := mul_le_mul_of_nonneg_left hRc (show 0 ≤ 4*ρ-1 by linarith)
    have hbalance := mul_nonneg (show 0 ≤ 1-5*ρ/2 by linarith) hc
    nlinarith

theorem first_common_uniform (ρ δ c d p R E Lc R₀ : ℝ)
    (hρ : 1/4 ≤ ρ) (hρmax : ρ ≤ 103/273) (hδ : 17/25 ≤ δ)
    (hp : 0 ≤ p) (hpC : p ≤ c) (hpD : p ≤ d) (hRp : R ≤ p)
    (hR₀ : 0 ≤ R₀) (hLc : Lc ≤ 5*(R-R₀)) :
    (1-ρ)*max (c-d) 0-δ*c-(1+ρ)*R-E-
      max (3*c-5*d-R) 0/6+ρ*Lc+R₀ ≤ -(519/4550)*c-E := by
  have hh := first_common_coupled ρ δ c d p R E Lc R₀
    hρ (by linarith) hp hpC hpD hRp hR₀ hLc
  have hh' := mul_nonneg (show 0 ≤ δ-3*ρ/2-519/4550 by linarith)
    (show 0 ≤ c by linarith)
  nlinarith

end
end CoupledRadicalSaving

#print axioms CoupledRadicalSaving.first_common_coupled
#print axioms CoupledRadicalSaving.first_common_uniform
end

/- Original module: Candidate.Cycle63.Physical.MarkedAllocationReserve. -/
section

namespace MarkedAllocationReserve
noncomputable section

/-- Retaining the first allocation norm gives a strict loss when slots disappear. -/
theorem first_common_saving (ρ δ κ c d p R E Bc Lc R₀ : ℝ)
    (hρ : 0 ≤ ρ) (hκ : 0 ≤ κ) (hδ : κ ≤ δ)
    (hsum : 1 + κ ≤ ρ + δ) (hfive : 1 ≤ 5*ρ) (hfour : 1 ≤ 4*ρ)
    (hgap : 4*ρ-1-δ ≤ -κ)
    (hp : 0 ≤ p) (hpC : p ≤ c) (hpD : p ≤ d) (hRp : R ≤ p)
    (hR₀ : 0 ≤ R₀) (hLc : Lc ≤ 5*(R-R₀)) :
    (1-ρ)*max (c-d) 0-δ*c-(1+ρ)*R-E-Bc+ρ*Lc+R₀ ≤
      -κ*c-E-Bc := by
  have hfirst : (1-ρ)*max (c-d) 0-δ*c ≤ -κ*c-(δ-κ)*p := by
    by_cases hcd : d ≤ c
    · rw [max_eq_left (sub_nonneg.mpr hcd)]
      have h1 := mul_nonneg (show 0 ≤ ρ+δ-1-κ by linarith) (sub_nonneg.mpr hcd)
      have h2 := mul_nonneg (sub_nonneg.mpr hδ) (sub_nonneg.mpr hpD)
      nlinarith
    · rw [max_eq_right (show c-d ≤ 0 by linarith)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hδ) (sub_nonneg.mpr hpC)]
  have hnum := mul_le_mul_of_nonneg_left hLc hρ
  have hcancel := mul_nonneg (show 0 ≤ 5*ρ-1 by linarith) hR₀
  have hrad := mul_le_mul_of_nonneg_left hRp (show 0 ≤ 4*ρ-1 by linarith)
  have hrest := mul_nonpos_of_nonpos_of_nonneg (show 4*ρ-1-δ+κ ≤ 0 by linarith) hp
  nlinarith

/-- The second allocation has the stronger direct delta loss. -/
theorem second_common_saving (δ b g t : ℝ) (hg : g ≤ b) :
    g-t-(1+δ)*b ≤ -δ*b-t := by nlinarith

theorem both_common_saving (ρ δ κ c d p R E Bc Lc R₀ b g t : ℝ)
    (hρ : 0 ≤ ρ) (hκ : 0 ≤ κ) (hδ : κ ≤ δ)
    (hsum : 1 + κ ≤ ρ + δ) (hfive : 1 ≤ 5*ρ) (hfour : 1 ≤ 4*ρ)
    (hgap : 4*ρ-1-δ ≤ -κ)
    (hp : 0 ≤ p) (hpC : p ≤ c) (hpD : p ≤ d) (hRp : R ≤ p)
    (hR₀ : 0 ≤ R₀) (hLc : Lc ≤ 5*(R-R₀))
    (hb : 0 ≤ b) (hg : g ≤ b) (hE : 0 ≤ E) (hB : 0 ≤ Bc) (ht : 0 ≤ t) :
    (1-ρ)*max (c-d) 0-δ*c-(1+ρ)*R-E-Bc+ρ*Lc+R₀+g-t-(1+δ)*b ≤
      -κ*(c+b) := by
  have h1 := first_common_saving ρ δ κ c d p R E Bc Lc R₀
    hρ hκ hδ hsum hfive hfour hgap hp hpC hpD hRp hR₀ hLc
  have h2 := second_common_saving δ b g t hg
  nlinarith [mul_nonneg (sub_nonneg.mpr hδ) hb]

/-- In the narrow high-zero range the first allocation can pay one twentieth. -/
theorem density_sum_gap (δ : ℝ) (hlo : 17/25 ≤ δ) (hhi : δ ≤ 7/10) :
    1 + 1/20 ≤ (1-10*δ/(3*(5-2*δ))) + δ := by
  have hd : 0 < 3*(5-2*δ) := by linarith
  have hpoly := mul_nonneg (show 0 ≤ 7/10-δ by linarith)
    (show 0 ≤ 120*δ-22 by linarith)
  have hf : 10*δ/(3*(5-2*δ)) ≤ δ-1/20 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  linarith

/-- Few removed slots leave both enough frequency scale and enough live width.
The constants allow one thousandth of source rounding loss. -/
theorem small_allocation_geometry (M c d b a R Lc ω err live q : ℝ)
    (hM : 0 ≤ M) (hc : 0 ≤ c) (hd : 0 ≤ d) (hb : 0 ≤ b)
    (hsmall : c+b ≤ M/50) (hR : R ≤ c) (hLc : 0 ≤ Lc)
    (ha : a ≤ 3*M/250) (hω : ω ≤ M/1000) (herr : 0 ≤ err)
    (hq : q = M-R-max (c-d) 0+Lc-6*a-ω+err)
    (hlive : 17*M/500-c-b-M/1000 ≤ live) :
    887*M/1000 ≤ q ∧ 13*M/1000 ≤ live := by
  have hm : max (c-d) 0 ≤ c := max_le (by linarith) hc
  constructor <;> linarith

/-- The same small-allocation range bounds the frequency above and supplies
one hundredth of its logarithmic scale in live slots. -/
theorem small_allocation_supply (M c d b a R Lc ω err live q : ℝ)
    (hc : 0 ≤ c) (hb : 0 ≤ b) (ha : 0 ≤ a)
    (hsmall : c+b ≤ M/50) (hR : R ≤ c) (hLc : Lc ≤ 5*R)
    (herr : err-ω ≤ M/1000)
    (hq : q = M-R-max (c-d) 0+Lc-6*a-ω+err)
    (hlive : 17*M/500-c-b-M/1000 ≤ live) :
    q ≤ 1081*M/1000 ∧ q/100 ≤ live := by
  have hm : 0 ≤ max (c-d) 0 := le_max_right _ _
  have hM : 0 ≤ M := by linarith
  constructor <;> linarith

/-- The sixthpower tail and the almost-full core both retain a thousandth. -/
theorem sixthpower_split_saving (ρ v : ℝ) (hρ : 2/7 ≤ ρ) (hv : 247/250 ≤ v) :
    1/1000 ≤ (6*ρ-1)/500 ∧ 1/1000 ≤ v*(3/2800) := by
  constructor <;> linarith

/-- A uniform saving follows by separating large allocations from marked rows. -/
theorem allocation_or_marked (M removed q E base : ℝ)
    (hM : 0 ≤ M)
    (hplain : E ≤ base-removed/20)
    (hmarked : removed ≤ M/50 → 887*M/1000 ≤ q ∧
      E ≤ base-q*(3/2800)) :
    E ≤ base-19*M/20000 := by
  by_cases hsmall : removed ≤ M/50
  · obtain ⟨hq,he⟩ := hmarked hsmall
    linarith
  · have hlarge : M/50 ≤ removed := le_of_lt (lt_of_not_ge hsmall)
    linarith

/-- A reserve after the raw-row split, retaining room for analytic losses. -/
theorem allocation_or_raw_marked (M removed q E base : ℝ)
    (hM : 0 ≤ M)
    (hplain : E ≤ base-removed/20)
    (hmarked : removed ≤ M/50 → 887*M/1000 ≤ q ∧
      E ≤ base-q/1000) :
    E ≤ base-887*M/1000000 := by
  by_cases hsmall : removed ≤ M/50
  · obtain ⟨hq,he⟩ := hmarked hsmall
    linarith
  · have hlarge : M/50 ≤ removed := le_of_lt (lt_of_not_ge hsmall)
    linarith

/-- The source frequency loses at most twice the common allocation norm,
in addition to the amplifier and the controlled frequency loss. -/
theorem raw_frequency_lower (M c d b a R Lc ω err q : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hb : 0 ≤ b)
    (hR : R ≤ c) (hLc : 0 ≤ Lc)
    (ha : a ≤ M/75) (hω : ω ≤ M/1000) (herr : 0 ≤ err)
    (hq : q = M-R-max (c-d) 0+Lc-6*a-ω+err) :
    919*M/1000-2*(c+b) ≤ q := by
  have hm : max (c-d) 0 ≤ c := max_le (by linarith) hc
  linarith

/-- Removing a sixth power of norm at most U^(1/250) preserves the
frequency lower bound required by the continuous allocation ledger. -/
theorem small_core_frequency_lower (M removed q qcore : ℝ)
    (hM : 0 ≤ M) (hu : 0 ≤ removed)
    (hq : 919*M/1000-2*removed ≤ q)
    (hcore : (122/125)*q ≤ qcore) :
    1121*M/1250-2*removed ≤ qcore := by linarith

/-- Coupled radical loss and asymmetric marked moments cover every split of
the conserved width between common, frozen, and surviving slots. -/
theorem continuous_marked_ledger (M removed frozen live q δ : ℝ)
    (hM : 0 ≤ M) (hu : 0 ≤ removed) (hf : 0 ≤ frozen) (hl : 0 ≤ live)
    (hδ : 519/4550 ≤ δ)
    (hsupply : 33*M/1000 ≤ removed+frozen+live)
    (hq : 1121*M/1250-2*removed ≤ q) :
    37*M/10000 ≤ (519/4550)*removed+δ*frozen+(224/1755)*min live (13*q/400) := by
  have hdf : (519/4550)*frozen ≤ δ*frozen := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ δ-519/4550) hf]
  by_cases hs : live ≤ 13*q/400
  · rw [min_eq_left hs]
    linarith
  · rw [min_eq_right (le_of_lt (lt_of_not_ge hs))]
    linarith

/-- The large-root tail covers the same reserve in the narrow high-zero range. -/
theorem continuous_tail_ledger (M removed frozen q δ ρ : ℝ)
    (hM : 0 ≤ M) (hu : 0 ≤ removed) (hf : 0 ≤ frozen) (hq0 : 0 ≤ q)
    (hδ : 0 ≤ δ) (hρ : 19/54 ≤ ρ)
    (hq : 1121*M/1250-2*removed ≤ q) :
    37*M/10000 ≤ (519/4550)*removed+δ*frozen+(6*ρ-1)*q/250 := by
  have hprod := mul_nonneg (by linarith : 0 ≤ 6*ρ-1-10/9) hq0
  have hdf := mul_nonneg hδ hf
  nlinarith

theorem continuous_reserve_after_losses (M E base loss : ℝ)
    (hM : 0 ≤ M) (hE : E ≤ base-37*M/10000+loss)
    (hloss : loss ≤ M/20000) : E ≤ base-73*M/20000 := by linarith

end
end MarkedAllocationReserve
#print axioms MarkedAllocationReserve.first_common_saving
#print axioms MarkedAllocationReserve.both_common_saving
#print axioms MarkedAllocationReserve.density_sum_gap
#print axioms MarkedAllocationReserve.small_allocation_geometry
#print axioms MarkedAllocationReserve.allocation_or_marked

#print axioms MarkedAllocationReserve.small_allocation_supply
#print axioms MarkedAllocationReserve.sixthpower_split_saving
#print axioms MarkedAllocationReserve.allocation_or_raw_marked

#print axioms MarkedAllocationReserve.continuous_marked_ledger
#print axioms MarkedAllocationReserve.continuous_tail_ledger
#print axioms MarkedAllocationReserve.continuous_reserve_after_losses
#print axioms MarkedAllocationReserve.raw_frequency_lower
#print axioms MarkedAllocationReserve.small_core_frequency_lower
end

/- Original module: Candidate.Cycle63.Physical.MarkedHighLedger. -/
section

namespace Cycle63.Physical
noncomputable section
open Cycle63.Arithmetic OAI.SevenEighths.LocalMoment MarkedAllocationReserve

def highJointExcess (M A a δ c d p R E Bc Lc R₀ b₂ g₂ t₂ : ℝ) : ℝ :=
  M*(unmarkedDensity δ-1)+δ*A+a*(5-6*unmarkedDensity δ)+
    (1-unmarkedDensity δ)*max (c-d) 0-δ*c-(1+unmarkedDensity δ)*R-E-Bc+
    unmarkedDensity δ*Lc+R₀+g₂-t₂-(1+δ)*b₂

/-- Keep the strict loss from both common allocations instead of discarding it. -/
theorem high_joint_allocation_saving {b δ M A a c d p R E Bc Lc R₀ b₂ g₂ t₂ : ℝ}
    (hb : 3401/100000≤b ∧ b≤1/25) (hd : q0≤δ ∧ δ≤7/10)
    (hM : 0≤M) (hA : A≤M*totalA b) (ha : a≤M*amp b)
    (hp : 0≤p) (hE : 0≤E) (hB : max (3*c-5*d-R) 0/6≤Bc)
    (hpC : p≤c) (hpD : p≤d) (hRp : R≤p) (hR₀ : 0≤R₀)
    (hLc : Lc≤5*(R-R₀)) (hb₂ : 0≤b₂) (ht₂ : 0≤t₂) (hg₂ : g₂≤b₂) :
    highJointExcess M A a δ c d p R E Bc Lc R₀ b₂ g₂ t₂≤
      -M*highMainReserve b δ-(519/4550)*(c+b₂) := by
  have hd' : q0≤δ ∧ δ≤3/4 := ⟨hd.1,by linarith [hd.2]⟩
  obtain ⟨hlo,hhi,hsum,hfive,hfour,hgap⟩ := high_density_bounds hd'
  have hcommon := CoupledRadicalSaving.first_common_uniform (unmarkedDensity δ) δ
    c d p R E Lc R₀ (by linarith) (by simpa only [rho0] using hhi) hd.1
    hp hpC hpD hRp hR₀ hLc
  have hsecond := second_common_saving δ b₂ g₂ t₂ hg₂
  have hsecondgap := mul_nonneg (show 0≤δ-519/4550 by have := hd.1; norm_num [q0] at this; linarith) hb₂
  have hcoef : 0≤5-6*unmarkedDensity δ := by norm_num [rho0] at hhi;linarith
  have hA' := mul_le_mul_of_nonneg_left hA (by linarith : 0≤δ)
  have ha' := mul_le_mul_of_nonneg_right ha hcoef
  unfold highJointExcess highMainReserve
  nlinarith

/-- The continuous marked saving and the common allocation loss jointly
restore the positive reserve at the enlarged intercept. -/
theorem high_joint_marked_payment {b δ M A a c d p R E Bc Lc R₀ b₂ g₂ t₂ live q loss : ℝ}
    (hb : 3401/100000≤b ∧ b≤1/25) (hd : q0≤δ ∧ δ≤7/10)
    (hM : 0≤M) (hA : A≤M*totalA b) (ha : a≤M*amp b)
    (hp : 0≤p) (hE : 0≤E) (hB : max (3*c-5*d-R) 0/6≤Bc)
    (hpC : p≤c) (hpD : p≤d) (hRp : R≤p) (hR₀ : 0≤R₀)
    (hLc : Lc≤5*(R-R₀)) (hb₂ : 0≤b₂) (ht₂ : 0≤t₂) (hg₂ : g₂≤b₂)
    (hlive : 0≤live) (hsupply : 33*M/1000≤c+b₂+live)
    (hq : 1121*M/1250-2*(c+b₂)≤q) (hloss : loss≤M/20000) :
    highJointExcess M A a δ c d p R E Bc Lc R₀ b₂ g₂ t₂-
      (224/1755)*min live (13*q/400)+loss≤ -M*(720486667/30493190000000) := by
  have hh := high_joint_allocation_saving hb hd hM hA ha hp hE hB hpC hpD hRp hR₀ hLc hb₂ ht₂ hg₂
  have hu : 0≤c+b₂ := by linarith
  have hδ : 519/4550≤δ := by have := hd.1;norm_num [q0] at this;linarith
  have hs := continuous_marked_ledger M (c+b₂) 0 live q δ hM hu (by norm_num) hlive hδ
    (by simpa using hsupply) hq
  have hr := mul_le_mul_of_nonneg_left (marked_high_reserve hb
    ⟨hd.1,by linarith [hd.2]⟩) hM
  nlinarith

/-- The large sixth-power tail pays the same reserve without using marked slots. -/
theorem high_joint_tail_payment {b δ M A a c d p R E Bc Lc R₀ b₂ g₂ t₂ q loss : ℝ}
    (hb : 3401/100000≤b ∧ b≤1/25) (hd : q0≤δ ∧ δ≤7/10)
    (hM : 0≤M) (hA : A≤M*totalA b) (ha : a≤M*amp b)
    (hp : 0≤p) (hE : 0≤E) (hB : max (3*c-5*d-R) 0/6≤Bc)
    (hpC : p≤c) (hpD : p≤d) (hRp : R≤p) (hR₀ : 0≤R₀)
    (hLc : Lc≤5*(R-R₀)) (hb₂ : 0≤b₂) (ht₂ : 0≤t₂) (hg₂ : g₂≤b₂)
    (hq0 : 0≤q) (hq : 1121*M/1250-2*(c+b₂)≤q) (hloss : loss≤M/20000) :
    highJointExcess M A a δ c d p R E Bc Lc R₀ b₂ g₂ t₂-
      (6*unmarkedDensity δ-1)*q/250+loss≤ -M*(720486667/30493190000000) := by
  have hh := high_joint_allocation_saving hb hd hM hA ha hp hE hB hpC hpD hRp hR₀ hLc hb₂ ht₂ hg₂
  have hu : 0≤c+b₂ := by linarith
  have hδ : 0≤δ := by have := hd.1;norm_num [q0] at this;linarith
  have hd' : q0≤δ ∧ δ≤3/4 := ⟨hd.1,by linarith [hd.2]⟩
  have hs := continuous_tail_ledger M (c+b₂) 0 q δ (unmarkedDensity δ)
    hM hu (by norm_num) hq0 hδ (by
      have hden : 0<3*(5-2*δ) := by linarith [hd.2]
      have hfrac : 10*δ/(3*(5-2*δ))≤35/54 := by
        apply (div_le_iff₀ hden).mpr
        linarith [hd.2]
      unfold unmarkedDensity
      linarith) hq
  have hr := mul_le_mul_of_nonneg_left (marked_high_reserve hb hd') hM
  nlinarith

theorem high_joint_excess_of_reserve {b δ M A a c d p R E Bc Lc R₀ b₂ g₂ t₂ μ : ℝ}
    (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) (hd : q0 ≤ δ ∧ δ ≤ 3/4)
    (hM : 0 ≤ M) (hA : A ≤ M*totalA b) (ha : a ≤ M*amp b) (hreserve : μ≤highMainReserve b δ)
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hB : 0 ≤ Bc)
    (hpC : p ≤ c) (hpD : p ≤ d) (hRp : R ≤ p) (hR₀ : 0 ≤ R₀)
    (hLc : Lc ≤ 5*(R-R₀)) (hb₂ : 0 ≤ b₂) (ht₂ : 0 ≤ t₂) (hg₂ : g₂ ≤ b₂) :
    M*(unmarkedDensity δ-1)+δ*A+a*(5-6*unmarkedDensity δ)+
      (1-unmarkedDensity δ)*max (c-d) 0-δ*c-(1+unmarkedDensity δ)*R-E-Bc+
      unmarkedDensity δ*Lc+R₀+g₂-t₂-(1+δ)*b₂ ≤
        -M*μ := by
  have hδ : 0 ≤ δ := by have := hd.1; norm_num [q0] at this; linarith
  have hρ := (high_density_bounds hd).2.1
  have hcoef : 0 ≤ 5-6*unmarkedDensity δ := by norm_num [rho0] at hρ; linarith
  have ha' := mul_le_mul_of_nonneg_right ha hcoef
  have hA' := mul_le_mul_of_nonneg_left hA hδ
  have hcommon := high_common_part_nonpos hd hp hE hB hpC hpD hRp hR₀ hLc
  have hsecond := high_second_part_nonpos hδ hb₂ ht₂ hg₂
  have hpaid := mul_le_mul_of_nonneg_left hreserve hM
  unfold highMainReserve at hpaid
  nlinarith


end
end Cycle63.Physical
#print axioms Cycle63.Physical.high_joint_marked_payment
#print axioms Cycle63.Physical.high_joint_tail_payment
end
