/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine LOW prior-source budget uses one fixed original profile control.
The inherited height and logarithmic Sobolev estimates are reused exactly. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalRaw
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Raw.MomentFees
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.RegularLowBudgetControl
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths Filter
open CenteredMomentFiniteProfileExceptional CenteredMomentLattice
open Record12518109Raw OAI.SevenEighths.Record1252270103Low

theorem global_raw_profile_control (a b : ℝ) (ha : 0<a) (TP : Finset (ℕ×ℕ)) :
    ∃j : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
    ∀(CP DP : ℝ),0≤CP → 0≤DP → ∀(degreeP : ℕ)(Φ : 𝓢(ℝ,ℂ))
      (p : Profiles a b)(t height Z M ε : ℝ),0≤height → 0≤Z →
      globalRawBudget CP DP TP degreeP Φ
        (normPowerProfile (p.profile 0) a b ha (p.support 0) ((p.profile 0).smooth ⊤) t)
        (normPowerProfile (p.profile 1) a b ha (p.support 1) ((p.profile 1).smooth ⊤) t)
        t height Z M ε≤
      C*(CP*DP^2)*QuadraticInitialBound.diagonalControl Φ*(p.control S)^2*
        (1+|t|+height)^(j+degreeP)*Z^(M+ε) := by
  obtain ⟨j,S,C,hC,hbound⟩ := raw_source_budget_profile_control a b ha TP TP
  refine ⟨j,S,C,hC,?_⟩
  intro CP DP hCP hDP degreeP Φ p t height Z M ε hh hZ
  simpa only [rawSourceBudget,globalRawBudget,rawHeightProfile,zero_mul,add_zero,
    Nat.max_zero] using hbound CP 0 DP 0 hCP (by norm_num) hDP (by norm_num)
      degreeP 0 Φ p t height Z M ε hh hZ

def positiveWindow (b C : ℝ) : ℝ :=
  1+2*(Real.log (max 1 C)-Real.log ((max 1 b)⁻¹))

theorem positiveWindow_nonneg (b C : ℝ) : 0≤positiveWindow b C := by
  have hb := Real.log_nonneg (le_max_left (1:ℝ) b)
  have hC := Real.log_nonneg (le_max_left (1:ℝ) C)
  dsimp only [positiveWindow]
  rw [Real.log_inv]
  linarith only [hb,hC]

/-- The cap C can be subunit. The fixed floor is the actual profileFloor b,
written by its definition to avoid importing an unrelated analytic source. -/
theorem eventual_positive_windows (b Bscale ε : ℝ) (hB : 0≤Bscale) (hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀C₁ C₂ : ℝ,C₁≤Z^Bscale → C₂≤Z^Bscale →
      positiveWindow b C₁*positiveWindow b C₂≤
        (1+2*(Bscale+Real.log (max 1 b)))^2*Z^ε := by
  let width := Bscale+Real.log (max 1 b)
  have hb : 0≤Real.log (max 1 b) := Real.log_nonneg (le_max_left _ _)
  have hw : 0≤width := add_nonneg hB hb
  filter_upwards [eventual_common_sobolev_fee width ε hw hε,
    eventually_ge_atTop (Real.exp 1)] with Z hz hZe
  refine ⟨hz.1,?_⟩
  intro C₁ C₂ hC₁ hC₂
  have hZ0 : 0<Z := zero_lt_one.trans hz.1
  have hlogZ : 1≤Real.log Z := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (1:ℝ)) hZe
  have hone : 1≤Z^Bscale := Real.one_le_rpow hz.1.le hB
  have hcap (C : ℝ) (hC : C≤Z^Bscale) :
      Real.log (max 1 C)-Real.log ((max 1 b)⁻¹)≤width*Real.log Z := by
    have hlog := Real.log_le_log (zero_lt_one.trans_le (le_max_left (1:ℝ) C))
      (max_le hone hC)
    rw [Real.log_rpow hZ0] at hlog
    rw [Real.log_inv]
    have hh := mul_le_mul_of_nonneg_left hlogZ hb
    dsimp only [width]
    nlinarith only [hlog,hh]
  have hfloor (C : ℝ) : Real.log ((max 1 b)⁻¹)≤Real.log (max 1 C) := by
    rw [Real.log_inv]
    linarith only [hb,Real.log_nonneg (le_max_left (1:ℝ) C)]
  exact hz.2 (Real.log ((max 1 b)⁻¹)) (Real.log (max 1 C₁))
    (Real.log ((max 1 b)⁻¹)) (Real.log (max 1 C₂))
    (hfloor C₁) (hfloor C₂) (hcap C₁ hC₁) (hcap C₂ hC₂)

end
end QRH.Record1252270103Source.RegularLowBudgetControl
#print axioms QRH.Record1252270103Source.RegularLowBudgetControl.global_raw_profile_control
#print axioms QRH.Record1252270103Source.RegularLowBudgetControl.positiveWindow_nonneg
#print axioms QRH.Record1252270103Source.RegularLowBudgetControl.eventual_positive_windows
