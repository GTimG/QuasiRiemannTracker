import Candidate.Cycle63.Arithmetic.LocalReserves
import Candidate.LocalMoment.UnmarkedDensity

namespace Cycle63.Physical

noncomputable section
open Cycle63.Arithmetic
open OAI.SevenEighths.LocalMoment

/-- The high-bin reserve before the common-part and projector savings. -/
def highMainReserve (b δ : ℝ) : ℝ :=
  1-unmarkedDensity δ-δ*totalA b-amp b*(5-6*unmarkedDensity δ)

theorem high_density_bounds {δ : ℝ} (hd : q0 ≤ δ ∧ δ ≤ 3/4) :
    2/7 ≤ unmarkedDensity δ ∧ unmarkedDensity δ ≤ rho0 ∧
    1/28 ≤ unmarkedDensity δ+δ-1 ∧
    3/7 ≤ 5*unmarkedDensity δ-1 ∧ 1/7 ≤ 4*unmarkedDensity δ-1 ∧
    4*unmarkedDensity δ-1-δ ≤ 4*rho0-1-q0 := by
  have hq0b := Cycle63.Arithmetic.q0_bounds
  have hq := q0_bounds
  have hlo := unmarkedDensity_ge_two_sevenths hd.2
  have hden : 0 < 3*(5-2*δ) := by linarith [hd.2]
  have hden0 : 0 < 3*(5-2*q0) := by linarith [hq.2]
  have hquot : 10*q0/(3*(5-2*q0)) ≤ 10*δ/(3*(5-2*δ)) := by
    rw [div_le_div_iff₀ hden0 hden]
    nlinarith [hd.1]
  have hhi : unmarkedDensity δ ≤ rho0 := by
    unfold unmarkedDensity rho0 Cycle63.Optimization.density
    linarith
  have hsum : 1/28 ≤ unmarkedDensity δ+δ-1 := by
    have hm := mul_nonneg (show 0 ≤ 3/4-δ by linarith [hd.2])
      (show 0 ≤ 168*δ-20 by linarith [hd.1, hq.1])
    have hq' : 10*δ/(3*(5-2*δ)) ≤ δ-1/28 := by
      apply (div_le_iff₀ hden).mpr
      nlinarith
    unfold unmarkedDensity
    linarith
  refine ⟨hlo,hhi,hsum,by linarith,by linarith,?_⟩
  linarith [hd.1]

/-- The density gap `4 rho0 - 1 - q0` at the bin split is negative. -/
theorem density_gap_neg : 4*rho0-1-q0 < 0 := by
  have hq0b := Cycle63.Arithmetic.q0_bounds
  have hq := q0_bounds
  rw [← sub_neg, sub_zero]
  have : 0 < -(4*rho0-1-q0) := by
    unfold rho0 Cycle63.Optimization.density
    rat_pos [hq]
  linarith

/-- The HIGH reserve grows with the zero bin: by the algebraic difference formula it is at least
its value at the bin split, the room `lowReserve` minus the net marked saving. -/
theorem high_main_reserve_bound {b δ : ℝ}
    (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop) (hd : q0 ≤ δ ∧ δ ≤ 3/4) :
    lowReserve - (markedPrice*Cycle63.Optimization.suppliedAt b - Cycle63.Optimization.markedLoss) ≤ highMainReserve b δ := by
  have hq0b := Cycle63.Arithmetic.q0_bounds
  have hδ : 0 < 5-2*δ := by linarith [hd.2]
  have hq : 0 < 5-2*q0 := by linarith [q0_bounds.2]
  have hden : 0 < 3*(5-2*δ)*(5-2*q0) := by positivity
  have hn : 0 ≤ 50*(1-6*amp b) := by
    have ha := (amp_bounds hb).2
    linarith [Cycle63.Optimization.amplifierCap_bounds.2]
  have hprod : 3*(5-2*δ)*(5-2*q0) ≤ 3*(5-2*q0)^2 := by
    nlinarith [hd.1]
  have hfrac := div_le_div_of_nonneg_left hn hden hprod
  have hbase := high_derivative_reserve hb
  have hpos : 0 ≤ 50*(1-6*amp b)/(3*(5-2*δ)*(5-2*q0))-totalA b := by
    linarith [Cycle63.Optimization.reserveGrowth_bounds.1]
  have heq : highMainReserve b δ-highMainReserve b q0 =
      (δ-q0)*(50*(1-6*amp b)/(3*(5-2*δ)*(5-2*q0))-totalA b) := by
    unfold highMainReserve unmarkedDensity
    field_simp [ne_of_gt hδ, ne_of_gt hq, show 5-δ*2 ≠ 0 by linarith,
      show 5-q0*2 ≠ 0 by linarith]
    ring
  have hm : 0 ≤ highMainReserve b δ-highMainReserve b q0 := by
    rw [heq]
    exact mul_nonneg (sub_nonneg.mpr hd.1) hpos
  have hr : highMainReserve b q0 = lowReserve - (markedPrice*Cycle63.Optimization.suppliedAt b - Cycle63.Optimization.markedLoss) := by
    have hρ : unmarkedDensity q0 = rho0 := rfl
    simpa only [highMainReserve,hρ] using high_reserve b
  linarith

theorem rho0_le : rho0 ≤ 2/5 := rho0_bounds.2

/-- All first common labels are already included in the joint row count.
The remaining common-part exponent is nonpositive. -/
theorem high_common_part_bound (ρ δ c d p R E Bc Lc R₀ : ℝ)
    (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ) (hρδ : 1 ≤ ρ+δ)
    (hfive : 1 ≤ 5*ρ) (hfour : 1 ≤ 4*ρ)
    (hpC : p ≤ c) (hpD : p ≤ d) (hRp : R ≤ p) (hR₀ : 0 ≤ R₀)
    (hLc : Lc ≤ 5*(R-R₀)) :
    (1-ρ)*max (c-d) 0-δ*c-(1+ρ)*R-E-Bc+ρ*Lc+R₀ ≤
      (4*ρ-1-δ)*p-E-Bc := by
  have hfirst : (1-ρ)*max (c-d) 0-δ*c ≤ -δ*p := by
    by_cases hcd : d ≤ c
    · rw [max_eq_left (sub_nonneg.mpr hcd)]
      nlinarith [mul_nonneg (show 0 ≤ ρ+δ-1 by linarith)
        (sub_nonneg.mpr hcd),mul_nonneg hδ (sub_nonneg.mpr hpD)]
    · rw [max_eq_right (show c-d ≤ 0 by linarith)]
      nlinarith [mul_nonneg hδ (sub_nonneg.mpr hpC)]
  have hnum := mul_le_mul_of_nonneg_left hLc hρ
  have hcancel := mul_nonneg (show 0 ≤ 5*ρ-1 by linarith) hR₀
  have hrad := mul_le_mul_of_nonneg_left hRp (show 0 ≤ 4*ρ-1 by linarith)
  nlinarith

theorem high_common_part_nonpos {δ c d p R E Bc Lc R₀ : ℝ}
    (hd : q0 ≤ δ ∧ δ ≤ 3/4) (hp : 0 ≤ p) (hE : 0 ≤ E) (hB : 0 ≤ Bc)
    (hpC : p ≤ c) (hpD : p ≤ d) (hRp : R ≤ p) (hR₀ : 0 ≤ R₀)
    (hLc : Lc ≤ 5*(R-R₀)) :
    (1-unmarkedDensity δ)*max (c-d) 0-δ*c-(1+unmarkedDensity δ)*R-E-Bc+
      unmarkedDensity δ*Lc+R₀ ≤ 0 := by
  have hq0b := Cycle63.Arithmetic.q0_bounds
  obtain ⟨hlo,hhi,hsum,hfive,hfour,hlast⟩ := high_density_bounds hd
  have hδ : 0 ≤ δ := by linarith [hd.1, q0_bounds.1]
  have hb := high_common_part_bound (unmarkedDensity δ) δ c d p R E Bc Lc R₀
    (by linarith) hδ (by linarith) (by linarith) (by linarith)
    hpC hpD hRp hR₀ hLc
  have hm := mul_nonpos_of_nonpos_of_nonneg (show 4*unmarkedDensity δ-1-δ ≤ 0 by linarith [density_gap_neg]) hp
  linarith

theorem high_second_part_nonpos {δ b₂ g₂ t₂ : ℝ}
    (hδ : 0 ≤ δ) (hb : 0 ≤ b₂) (ht : 0 ≤ t₂) (hg : g₂ ≤ b₂) :
    g₂-t₂-(1+δ)*b₂ ≤ 0 := by
  nlinarith [mul_nonneg hδ hb]

/-- The full exponent in (2.20), including the joint source count and both
common-part savings, has the same strict reserve throughout each cell. -/
theorem high_joint_excess_bound {b δ M A a c d p R E Bc Lc R₀ b₂ g₂ t₂ : ℝ}
    (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop) (hd : q0 ≤ δ ∧ δ ≤ 3/4)
    (hM : 0 ≤ M) (hA : A ≤ M*totalA b) (ha : a ≤ M*amp b)
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hB : 0 ≤ Bc)
    (hpC : p ≤ c) (hpD : p ≤ d) (hRp : R ≤ p) (hR₀ : 0 ≤ R₀)
    (hLc : Lc ≤ 5*(R-R₀)) (hb₂ : 0 ≤ b₂) (ht₂ : 0 ≤ t₂) (hg₂ : g₂ ≤ b₂) :
    M*(unmarkedDensity δ-1)+δ*A+a*(5-6*unmarkedDensity δ)+
      (1-unmarkedDensity δ)*max (c-d) 0-δ*c-(1+unmarkedDensity δ)*R-E-Bc+
      unmarkedDensity δ*Lc+R₀+g₂-t₂-(1+δ)*b₂ ≤
        -M*(lowReserve - (markedPrice*Cycle63.Optimization.suppliedAt b - Cycle63.Optimization.markedLoss)) := by
  have hq0b := Cycle63.Arithmetic.q0_bounds
  have hδ : 0 ≤ δ := by linarith [hd.1, q0_bounds.1]
  have hρ := (high_density_bounds hd).2.1
  have hcoef : 0 ≤ 5-6*unmarkedDensity δ := by linarith [rho0_le]
  have ha' := mul_le_mul_of_nonneg_right ha hcoef
  have hA' := mul_le_mul_of_nonneg_left hA hδ
  have hcommon := high_common_part_nonpos hd hp hE hB hpC hpD hRp hR₀ hLc
  have hsecond := high_second_part_nonpos hδ hb₂ ht₂ hg₂
  have hreserve := mul_le_mul_of_nonneg_left (high_main_reserve_bound hb hd) hM
  unfold highMainReserve at hreserve
  nlinarith


end
end Cycle63.Physical

#print axioms Cycle63.Physical.high_main_reserve_bound
#print axioms Cycle63.Physical.high_joint_excess_bound
