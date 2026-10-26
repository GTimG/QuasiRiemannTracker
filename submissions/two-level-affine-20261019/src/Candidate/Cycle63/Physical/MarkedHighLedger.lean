import Candidate.Cycle63.Physical.MarkedHighReserve
import Candidate.Cycle63.Physical.ValuationCone

namespace Cycle63.Physical
noncomputable section
open Cycle63.Arithmetic OAI.SevenEighths.LocalMoment

def highJointExcess (M A a δ c d _p R E Bc Lc R₀ b₂ g₂ t₂ : ℝ) : ℝ :=
  M*(unmarkedDensity δ-1)+δ*A+a*(5-6*unmarkedDensity δ)+
    (1-unmarkedDensity δ)*max (c-d) 0-δ*c-(1+unmarkedDensity δ)*R-E-Bc+
    unmarkedDensity δ*Lc+R₀+g₂-t₂-(1+δ)*b₂

/-- The rate of the valuation cone is nonnegative in every bin of the HIGH range. -/
theorem commonRate_nonneg {δ : ℝ} (hd : q0≤δ ∧ δ≤3/4) :
    0≤OAI.SevenEighths.Cycle63Moment.ValuationCone.commonRate δ := by
  obtain ⟨_,hhi,_⟩ := high_density_bounds hd
  have hq := q0_bounds
  have hρ : 4*rho0-5/4<q0 := by
    unfold rho0 Cycle63.Optimization.density
    rat_pos [hq]
  unfold OAI.SevenEighths.Cycle63Moment.ValuationCone.commonRate
  rw [sub_nonneg]
  apply max_le <;> linarith [hd.1, hq.1]

/-- On the plane and at the amplifier of the cell `b`, the reserve `M (1 - ρ) - δ A - a (5 - 6ρ)` of a parent is at
least `M` times the HIGH-bin reserve of the cell. -/
theorem highMainReserve_le_reserve {b δ M A a : ℝ} (hd : q0 ≤ δ ∧ δ ≤ 3/4) (hA : A ≤ M*totalA b)
    (ha : a ≤ M*amp b) :
    M*highMainReserve b δ ≤ M*(1-unmarkedDensity δ)-δ*A-a*(5-6*unmarkedDensity δ) := by
  have hcoef : 0 ≤ 5-6*unmarkedDensity δ := by linarith [rho0_bounds.2, (high_density_bounds hd).2.1]
  have hA' := mul_le_mul_of_nonneg_left hA (by linarith [q0_bounds.1, hd.1] : 0 ≤ δ)
  have ha' := mul_le_mul_of_nonneg_right ha hcoef
  unfold highMainReserve
  linarith

/-- With the label's surplus `σ` kept, the common part is paid at a rate `γ` of the valuation cone
(`ValuationCone.actual_first_common_saving`), the second label at its zero parameter, and the parent keeps its reserve
`M (1 - ρ) - δ A - a (5 - 6ρ)`. -/
theorem high_joint_allocation_saving_reserve {δ M A a c d p R E Bc Lc R₀ b₂ g₂ t₂ σ γ : ℝ}
    (hE : 0 ≤ E) (hB : max (3*c-5*d-R) 0/6 ≤ Bc) (hb₂ : 0 ≤ b₂) (hg₂ : g₂ ≤ b₂) (hγ : γ ≤ δ)
    (hcommon : (1-unmarkedDensity δ)*max (c-d) 0-δ*c-(1+unmarkedDensity δ)*R-E-
      max (3*c-5*d-R) 0/6+unmarkedDensity δ*Lc+R₀-σ ≤ -γ*c-E) (ht₂ : 0 ≤ t₂) :
    highJointExcess M A a δ c d p R E Bc Lc R₀ b₂ g₂ t₂-σ ≤
      -(M*(1-unmarkedDensity δ)-δ*A-a*(5-6*unmarkedDensity δ))-γ*(c+b₂) := by
  have hsecondgap := mul_nonneg (show 0 ≤ δ-γ by linarith) hb₂
  unfold highJointExcess
  linarith

/-- With the label's surplus `σ` kept, the common part is paid at a rate `γ` of the valuation cone
(`ValuationCone.actual_first_common_saving`), the second label at its zero parameter, and the
strict loss of both common allocations is kept. -/
theorem high_joint_allocation_saving {b δ M A a c d p R E Bc Lc R₀ b₂ g₂ t₂ σ γ : ℝ}
    (_hb : Cycle63.Optimization.firstCellTop≤b ∧ b≤Cycle63.Optimization.slotTop) (hd : q0≤δ ∧ δ≤3/4)
    (_hM : 0≤M) (hA : A≤M*totalA b) (ha : a≤M*amp b)
    (hE : 0≤E) (hB : max (3*c-5*d-R) 0/6≤Bc) (hb₂ : 0≤b₂) (hg₂ : g₂≤b₂) (hγ : γ≤δ)
    (hcommon : (1-unmarkedDensity δ)*max (c-d) 0-δ*c-(1+unmarkedDensity δ)*R-E-
      max (3*c-5*d-R) 0/6+unmarkedDensity δ*Lc+R₀-σ≤-γ*c-E) (ht₂ : 0≤t₂) :
    highJointExcess M A a δ c d p R E Bc Lc R₀ b₂ g₂ t₂-σ≤
      -M*highMainReserve b δ-γ*(c+b₂) := by
  have h := high_joint_allocation_saving_reserve (M := M) (A := A) (a := a) (p := p) hE hB hb₂ hg₂ hγ hcommon ht₂
  have hr := highMainReserve_le_reserve hd hA ha
  linarith

end
end Cycle63.Physical
