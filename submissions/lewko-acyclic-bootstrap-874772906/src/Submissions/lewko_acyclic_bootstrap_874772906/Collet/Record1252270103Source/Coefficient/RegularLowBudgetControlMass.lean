/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal LOW logarithmic, profile, restoration and fixed-mask costs.
Moving source radius, row weights, erasure and missing factors remain outside. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.RegularLowBudgetControl
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Restoration.ForwardFull
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.RegularLowBudgetControl
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentFiniteProfileExceptional CenteredMomentLattice
open Record12518109Raw OAI.SevenEighths.Record1252270103Low
open QRH.Record1252270103Restoration QRH.Record1252270103KernelMass
local notation "O" => HeckeFamily.O

theorem radical_mask_power (R : Ideal O) (hR : R≠0) (Z B ε : ℝ)
    (hZ : 0<Z) (hε : 0≤ε) (hcap : (R.absNorm:ℝ)≤Z^B) :
    ((∏I∈CompletedGauss.primeSupport R,I).absNorm:ℝ)^ε≤Z^(B*ε) := by
  rw [CenteredMomentAllocatedNaturalSource.primeSupport_product_radical R hR]
  have hrad : (R.radical.absNorm:ℝ)≤(R.absNorm:ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hR))
      (Ideal.absNorm_dvd_absNorm_of_le Ideal.le_radical)
  apply (Real.rpow_le_rpow (Nat.cast_nonneg _) (hrad.trans hcap) hε).trans_eq
  rw [←Real.rpow_mul hZ.le]

/-- A fixed Euler coefficient. Its square is paid before the moving root. -/
def restorationCoefficient (δ Brestore : ℝ) : ℝ :=
  holeDeletionMass*(eulerBound 5 (1/2+δ/(Brestore+1))+
    eulerBound 432 (1/2+δ/(Brestore+1)))

theorem restoration_power_identity (δ Brestore Z : ℝ) (hZ : 0≤Z) :
    (holeDeletionMass*((eulerBound 5 (1/2+δ/(Brestore+1))+
      eulerBound 432 (1/2+δ/(Brestore+1)))*Z^δ))^2=
      (restorationCoefficient δ Brestore)^2*Z^(2*δ) := by
  rw [←mul_assoc,mul_pow,←Real.rpow_mul_natCast hZ]
  dsimp only [restorationCoefficient]
  congr 2
  norm_num
  ring

/-- The controls and degree precede every moving profile, height, positive cap,
mask and radial exponent. The fixed Phi may be the actual chosen ball profile. -/
theorem global_raw_restored_budget (a b : ℝ) (ha : 0<a) (TP : Finset (ℕ×ℕ))
    (CP DP Craw : ℝ) (hCP : 0≤CP) (hDP : 0≤DP) (hCraw : 0≤Craw)
    (degreeP : ℕ) (Φ : 𝓢(ℝ,ℂ))
    (Bscale Bmask εmask δ Brestore εwindow : ℝ)
    (hBscale : 0≤Bscale) (hεmask : 0≤εmask) (hεwindow : 0<εwindow) :
    ∃J : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(p : Profiles a b)(t height M εsource loss C₁ C₂ : ℝ),0≤height →
      C₁≤Z^Bscale → C₂≤Z^Bscale → ∀R : Ideal O,R≠0 → (R.absNorm:ℝ)≤Z^Bmask →
      (holeDeletionMass*((eulerBound 5 (1/2+δ/(Brestore+1))+
        eulerBound 432 (1/2+δ/(Brestore+1)))*Z^δ))^2*
        (Craw*Z^loss*(positiveWindow b C₁*(positiveWindow b C₂*
          globalRawBudget CP DP TP degreeP Φ
            (normPowerProfile (p.profile 0) a b ha (p.support 0) ((p.profile 0).smooth ⊤) t)
            (normPowerProfile (p.profile 1) a b ha (p.support 1) ((p.profile 1).smooth ⊤) t)
            t height Z M εsource)))*((∏I∈CompletedGauss.primeSupport R,I).absNorm:ℝ)^εmask≤
      C*(p.control S)^2*(1+|t|+height)^J*
        Z^(M+εsource+loss+2*δ+Bmask*εmask+εwindow) := by
  obtain ⟨j,S,Cp,hCp,hprofiles⟩ := global_raw_profile_control a b ha TP
  let Wcost := (1+2*(Bscale+Real.log (max 1 b)))^2
  let Pcost := Cp*(CP*DP^2)*QuadraticInitialBound.diagonalControl Φ
  let K := (restorationCoefficient δ Brestore)^2*Craw*Wcost*Pcost
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg Φ
  have hWcost : 0≤Wcost := sq_nonneg _
  have hPcost : 0≤Pcost := by dsimp only [Pcost];positivity
  have hK : 0≤K := mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hCraw) hWcost) hPcost
  refine ⟨j+degreeP,S,1+K,by linarith only [hK],?_⟩
  filter_upwards [eventual_positive_windows b Bscale εwindow hBscale hεwindow] with Z hz
  refine ⟨hz.1,?_⟩
  intro p t height M εsource loss C₁ C₂ hh hC₁ hC₂ R hR hRcap
  have hZ : 0<Z := zero_lt_one.trans hz.1
  let raw := globalRawBudget CP DP TP degreeP Φ
    (normPowerProfile (p.profile 0) a b ha (p.support 0) ((p.profile 0).smooth ⊤) t)
    (normPowerProfile (p.profile 1) a b ha (p.support 1) ((p.profile 1).smooth ⊤) t)
    t height Z M εsource
  have hraw0 : 0≤raw := by dsimp only [raw,globalRawBudget];positivity
  have hp := hprofiles CP DP hCP hDP degreeP Φ p t height Z M εsource hh hZ.le
  change raw≤Pcost*(p.control S)^2*(1+|t|+height)^(j+degreeP)*Z^(M+εsource) at hp
  have hw := hz.2 C₁ C₂ hC₁ hC₂
  change positiveWindow b C₁*positiveWindow b C₂≤Wcost*Z^εwindow at hw
  have hr := radical_mask_power R hR Z Bmask εmask hZ hεmask hRcap
  have hwp := mul_le_mul hw hp hraw0 (mul_nonneg hWcost (Real.rpow_nonneg hZ.le _))
  have hthree := mul_le_mul hwp hr (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
  have hmain := mul_le_mul_of_nonneg_left hthree
    (show 0≤(restorationCoefficient δ Brestore)^2*Craw*Z^loss*Z^(2*δ) by positivity)
  calc
    _=((restorationCoefficient δ Brestore)^2*Craw*Z^loss*Z^(2*δ))*
        ((positiveWindow b C₁*positiveWindow b C₂)*raw*((∏I∈CompletedGauss.primeSupport R,I).absNorm:ℝ)^εmask) := by
      rw [restoration_power_identity δ Brestore Z hZ.le]
      dsimp only [raw]
      ring
    _≤((restorationCoefficient δ Brestore)^2*Craw*Z^loss*Z^(2*δ))*
        ((Wcost*Z^εwindow)*(Pcost*(p.control S)^2*(1+|t|+height)^(j+degreeP)*Z^(M+εsource))*
          Z^(Bmask*εmask)) := hmain
    _=K*(p.control S)^2*(1+|t|+height)^(j+degreeP)*
        (Z^loss*Z^(2*δ)*Z^εwindow*Z^(M+εsource)*Z^(Bmask*εmask)) := by
      dsimp only [K]
      ring
    _=K*(p.control S)^2*(1+|t|+height)^(j+degreeP)*
        Z^(M+εsource+loss+2*δ+Bmask*εmask+εwindow) := by
      rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
      congr 2
      ring
    _≤_ := by gcongr <;> linarith

end
end QRH.Record1252270103Source.RegularLowBudgetControl
#print axioms QRH.Record1252270103Source.RegularLowBudgetControl.radical_mask_power
#print axioms QRH.Record1252270103Source.RegularLowBudgetControl.restoration_power_identity
#print axioms QRH.Record1252270103Source.RegularLowBudgetControl.global_raw_restored_budget
