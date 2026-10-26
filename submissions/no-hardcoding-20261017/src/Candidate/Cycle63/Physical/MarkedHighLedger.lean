import Candidate.Cycle63.Physical.MarkedHighReserve
import Candidate.Cycle63.Physical.MarkedAllocationReserve

namespace Cycle63.Physical
noncomputable section
open Cycle63.Arithmetic OAI.SevenEighths.LocalMoment MarkedAllocationReserve

def highJointExcess (M A a δ c d p R E Bc Lc R₀ b₂ g₂ t₂ : ℝ) : ℝ :=
  M*(unmarkedDensity δ-1)+δ*A+a*(5-6*unmarkedDensity δ)+
    (1-unmarkedDensity δ)*max (c-d) 0-δ*c-(1+unmarkedDensity δ)*R-E-Bc+
    unmarkedDensity δ*Lc+R₀+g₂-t₂-(1+δ)*b₂

/-- Keep the strict loss from both common allocations instead of discarding it. -/
theorem high_joint_allocation_saving {b δ M A a c d p R E Bc Lc R₀ b₂ g₂ t₂ : ℝ}
    (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop) (hd : q0≤δ ∧ δ≤Cycle63.Optimization.markedBinTop)
    (hM : 0≤M) (hA : A≤M*totalA b) (ha : a≤M*amp b)
    (hp : 0≤p) (hE : 0≤E) (hB : max (3*c-5*d-R) 0/6≤Bc)
    (hpC : p≤c) (hpD : p≤d) (hRp : R≤p) (hR₀ : 0≤R₀)
    (hLc : Lc≤5*(R-R₀)) (hnorm : 4*Lc≤5*(c+d)) (hb₂ : 0≤b₂) (ht₂ : 0≤t₂) (hg₂ : g₂≤b₂) :
    highJointExcess M A a δ c d p R E Bc Lc R₀ b₂ g₂ t₂≤
      -M*highMainReserve b δ-markedPrice*(c+b₂) := by
  have hd' : q0≤δ ∧ δ≤3/4 := ⟨hd.1,by linarith [hd.2, Cycle63.Optimization.markedBinTop_bounds.2]⟩
  obtain ⟨hlo,hhi,hsum,hfive,hfour,hgap⟩ := high_density_bounds hd'
  have hcommon := CoupledRadicalSaving.first_common_valuation_uniform q0 rho0 (unmarkedDensity δ) δ
    c d p R E Lc R₀ (by linarith) hhi rho0_le hd.1 hp hpC hRp hR₀ hLc hnorm
  have hmp : markedPrice = q0-max (4*rho0-1) ((2+22*rho0)/21) := rfl
  rw [← hmp] at hcommon
  have hsecond := second_common_saving δ b₂ g₂ t₂ hg₂
  have hprice : markedPrice ≤ δ := markedPrice_le_q0.trans hd.1
  have hsecondgap := mul_nonneg (show 0≤δ-markedPrice by linarith) hb₂
  have hcoef : 0≤5-6*unmarkedDensity δ := by linarith [rho0_le]
  have hA' := mul_le_mul_of_nonneg_left hA (by linarith [q0_bounds.1] : 0≤δ)
  have ha' := mul_le_mul_of_nonneg_right ha hcoef
  have hBc : -Bc ≤ -(max (3*c-5*d-R) 0/6) := by linarith
  unfold highJointExcess highMainReserve
  nlinarith

theorem high_joint_excess_of_reserve {b δ M A a c d p R E Bc Lc R₀ b₂ g₂ t₂ μ : ℝ}
    (hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop) (hd : q0 ≤ δ ∧ δ ≤ 3/4)
    (hM : 0 ≤ M) (hA : A ≤ M*totalA b) (ha : a ≤ M*amp b) (hreserve : μ≤highMainReserve b δ)
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hB : 0 ≤ Bc)
    (hpC : p ≤ c) (hpD : p ≤ d) (hRp : R ≤ p) (hR₀ : 0 ≤ R₀)
    (hLc : Lc ≤ 5*(R-R₀)) (hb₂ : 0 ≤ b₂) (ht₂ : 0 ≤ t₂) (hg₂ : g₂ ≤ b₂) :
    M*(unmarkedDensity δ-1)+δ*A+a*(5-6*unmarkedDensity δ)+
      (1-unmarkedDensity δ)*max (c-d) 0-δ*c-(1+unmarkedDensity δ)*R-E-Bc+
      unmarkedDensity δ*Lc+R₀+g₂-t₂-(1+δ)*b₂ ≤
        -M*μ := by
  have hδ : 0 ≤ δ := by linarith [hd.1, q0_bounds.1]
  have hρ := (high_density_bounds hd).2.1
  have hcoef : 0 ≤ 5-6*unmarkedDensity δ := by linarith [rho0_le]
  have ha' := mul_le_mul_of_nonneg_right ha hcoef
  have hA' := mul_le_mul_of_nonneg_left hA hδ
  have hcommon := high_common_part_nonpos hd hp hE hB hpC hpD hRp hR₀ hLc
  have hsecond := high_second_part_nonpos hδ hb₂ ht₂ hg₂
  have hpaid := mul_le_mul_of_nonneg_left hreserve hM
  unfold highMainReserve at hpaid
  nlinarith

end
end Cycle63.Physical
