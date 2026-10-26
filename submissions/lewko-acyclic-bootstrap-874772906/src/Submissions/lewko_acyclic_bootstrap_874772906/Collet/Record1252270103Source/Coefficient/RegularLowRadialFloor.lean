/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A genuine positive corner forces a fixed positive radial floor.
The alternative below the floor is exact vanishing, not an assumed source bound. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.RegularLowActualCapacityErasure
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.RegularLowRadialFloor
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open CenteredMomentAmplificationChildSourceCaps CenteredMomentEnergyBands
open QRH.Record1252270103Source.RegularLowActualCapacity
open QRH.Record1252270103Restoration
local notation "O" => HeckeFamily.O
local instance regularLowFloorDecidable {κ : Type*} : DecidableEq κ := Classical.decEq _

theorem radial_floor_of_supported_capacity (e B F t delta rho c f loss b : ℝ)
    (he : 0<e) (hB0 : 0≤B) (hB1 : B≤1) (hd : 0≤delta) (hdc : delta≤c)
    (hf : f≤b) (hcapacity : 0≤t-c+f+loss)
    (hguard : loss+B*rho+2*e≤B*F-t-b) :
    2*e≤F-delta-rho := by
  have hBd := mul_le_mul_of_nonneg_right hB1 hd
  have hBQ : 2*e≤B*(F-delta-rho) := by
    nlinarith only [hBd,hdc,hf,hcapacity,hguard]
  have hQ : 0≤F-delta-rho := by
    by_contra hn
    have hm := mul_nonpos_of_nonneg_of_nonpos hB0 (not_le.mp hn).le
    linarith only [hm,hBQ,he]
  have hBq := mul_le_mul_of_nonneg_right hB1 hQ
  linarith only [hBQ,hBq]

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable (s : Input ι) (C₁ R : Ideal O) (B₁ : actualAllocations s.pools C₁)
    (τ₁ : Character) (t₁ : ℝ) (C₂ : Ideal O)
    (B₂ : actualAllocations (child s C₁ R B₁ τ₁ t₁).pools C₂)
    (τ₂ : Character) (t₂ : ℝ) (C₃ : Ideal O)
    (B₃ : actualAllocations (child (child s C₁ R B₁ τ₁ t₁)
      C₂ (R*C₁) B₂ τ₂ t₂).pools C₃) (τ₃ : Character) (t₃ : ℝ)

/-- Apply to either actual positive corner. The floor depends only on the
fixed allowance e, before the ambient slot type and all subsequent choices. -/
theorem three_positive_corner_floor_or_zero (w : ι→ℝ) (N : ℕ)
    (upper Z t b F delta rho B plainUpper plainRound e : ℝ)
    (hupper : 1≤upper) (hZ : 1<Z) (hN : Fintype.card ι≤N) (hu : s.upper≤upper)
    (hscale : ∀i,s.P i=Z^w i) (ht : length Z s.X₁+length Z s.X₂≤t)
    (hw : ∀i,0≤w i) (htotal : (∑i,w i)≤b)
    (hround : 0≤plainRound) (he : 0<e) (hB0 : 0≤B) (hB1 : B≤1)
    (hd : 0≤delta) (hdc : delta≤Real.logb Z (C₁.absNorm:ℝ))
    (hguard : (3*(N:ℝ)*Real.logb Z upper+2*Real.logb Z (max 1 plainUpper)+2*plainRound)+
      B*rho+2*e≤B*F-t-b)
    (hf₁ : frozenCoefficient B₁.val C₁ R s.ν s.W s.P≠0)
    (hf₂ : frozenCoefficient B₂.val C₂ (R*C₁)
      (child s C₁ R B₁ τ₁ t₁).ν (child s C₁ R B₁ τ₁ t₁).W
      (child s C₁ R B₁ τ₁ t₁).P≠0)
    (hf₃ : frozenCoefficient B₃.val C₃ ((R*C₁)*C₂)
      (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).ν
      (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).W
      (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂).P≠0)
    (X₁ X₂ d₁ d₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hd₁ : 1≤d₁) (hd₂ : 1≤d₂)
    (hprod : X₁*X₂=(child (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂)
        C₃ ((R*C₁)*C₂) B₃ τ₃ t₃).X₁*
      (child (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂)
        C₃ ((R*C₁)*C₂) B₃ τ₃ t₃).X₂)
    (η : Character) (m A z : O) (W₁ W₂ : ℝ→ℂ)
    (pool : κ→Finset (Ideal O)) (β : κ→Ideal O→ℂ) (scales : κ→ℝ) (height : ℝ) :
    squarefreePositiveSlotRow η m A z W₁ W₂ plainUpper pool β scales height (X₁/d₁) (X₂/d₂)=0 ∨
      2*e≤F-delta-rho := by
  have hc := three_positive_corner_capacity_or_zero
    s C₁ R B₁ τ₁ t₁ C₂ B₂ τ₂ t₂ C₃ B₃ τ₃ t₃ w N upper Z t hupper hZ hN hu hscale ht
    hf₁ hf₂ hf₃ X₁ X₂ d₁ d₂ plainUpper hX₁ hX₂ (zero_lt_one.trans_le hd₁)
    (zero_lt_one.trans_le hd₂) hprod η m A z W₁ W₂ pool β scales height
  rcases hc with hz|hcap
  · exact Or.inl hz
  · apply Or.inr
    let c := Real.logb Z (C₁.absNorm:ℝ)+Real.logb Z (C₂.absNorm:ℝ)+Real.logb Z (C₃.absNorm:ℝ)
    let f := (∑i,w i)-∑i:liveIndices B₃.val,w i.val.val.val
    let loss := 3*(N:ℝ)*Real.logb Z upper+2*Real.logb Z (max 1 plainUpper)+2*plainRound
    have hc₂ := Real.logb_nonneg hZ (norm_ge_one _
      (allocation_ne (child s C₁ R B₁ τ₁ t₁) C₂ B₂))
    have hc₃ := Real.logb_nonneg hZ (norm_ge_one _
      (allocation_ne (child (child s C₁ R B₁ τ₁ t₁) C₂ (R*C₁) B₂ τ₂ t₂) C₃ B₃))
    have hdc' : delta≤c := by dsimp only [c];linarith only [hdc,hc₂,hc₃]
    have hf := three_live_width_bounds s C₁ R B₁ τ₁ t₁ C₂ B₂ τ₂ t₂ C₃ B₃ w b hw htotal
    have hpositive : 0≤t-c+f+loss := by
      have hl₁ := length_nonneg Z (X₁/d₁) hZ
      have hl₂ := length_nonneg Z (X₂/d₂) hZ
      have hn₁ := Real.logb_nonneg hZ hd₁
      have hn₂ := Real.logb_nonneg hZ hd₂
      dsimp only [c,f,loss]
      linarith only [hcap,hl₁,hl₂,hn₁,hn₂,hround]
    exact radial_floor_of_supported_capacity e B F t delta rho c f loss b
      he hB0 hB1 hd hdc' hf.2.1 hpositive hguard

end
end QRH.Record1252270103Source.RegularLowRadialFloor
#print axioms QRH.Record1252270103Source.RegularLowRadialFloor.radial_floor_of_supported_capacity
#print axioms QRH.Record1252270103Source.RegularLowRadialFloor.three_positive_corner_floor_or_zero
