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
