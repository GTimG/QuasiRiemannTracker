/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual Fourier window retains its full Schwartz moment and height cost. -/
import Candidate.C092.transport.FixedCubeGaussColoredH8Projection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion FourierBridge
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentSmooth
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentDivisorAllocation
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedCommonHeights
open CenteredMomentRowNorm CenteredMomentSecondSectorColumns CenteredMomentChildRows CenteredMomentChildAssembly
open QRH.Cycle092.SignedCenter MixedPrincipalWindow MixedCommonRestriction
open QRH.Cycle092.FixedCubeGauss
namespace QRH.Cycle092.FixedFourierH15
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

/-- The entire Fourier mass, with the degree required by the genuine bound. -/
def windowMass (V : ℝ→ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V) (J : ℕ) : ℝ :=
  ∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hc hs w‖

lemma windowMass_nonneg (V : ℝ→ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V) (J : ℕ) :
    0 ≤ windowMass V hc hs J := integral_nonneg (fun w=>by positivity)

/-- One fixed original row, with its honest absolute Fourier mass. -/
theorem window_integral_square (V : ℝ→ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V)
    (J : ℕ) (F : ℝ→ℂ) (E t θ X : ℝ) (hE : 0 ≤ E)
    (hi : Integrable (fun w : ℝ=>columnDensity V hc hs w*logPhase (θ-w) (Real.log X)*F (t+2*Real.pi*(w-θ))))
    (hF : ∀ v : ℝ,‖F v‖^2 ≤ E*(1+‖v‖)^(2*J)) :
    ‖∫ w : ℝ,columnDensity V hc hs w*logPhase (θ-w) (Real.log X)*F (t+2*Real.pi*(w-θ))‖^2 ≤
      (E*heightCost t θ^(2*J))*(windowMass V hc hs J)^2 := by
  let φ : Unit→ℝ→ℂ := fun _ w=>logPhase (θ-w) (Real.log X)*F (t+2*Real.pi*(w-θ))
  have hb (w : ℝ) : (∑ z : Unit,‖φ z w‖^2) ≤ (E*heightCost t θ^(2*J))*((1+‖w‖)^J)^2 := by
    simp only [φ,norm_mul,logPhase_norm,one_mul,Fintype.sum_unique]
    calc
      _ ≤ E*(1+‖t+2*Real.pi*(w-θ)‖)^(2*J) := hF _
      _ ≤ E*(heightCost t θ*(1+‖w‖))^(2*J) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (norm_height_shift t θ w) _) hE
      _ = _ := by rw [mul_pow,←pow_mul];ring
  have hint (_ : Unit) : Integrable (fun w=>columnDensity V hc hs w*φ () w) := by
    simpa only [φ,mul_assoc] using hi
  have hh := finite_weighted_integral_energy (columnDensity V hc hs) φ
    (fun w=>(1+‖w‖)^J) (fun w=>by positivity) (E*heightCost t θ^(2*J))
    (mul_nonneg hE (pow_nonneg (heightCost_pos t θ).le _))
    (columnDensity_moments V hc hs J) hint hb
  simpa only [φ,Fintype.sum_unique,←mul_assoc,windowMass] using hh

/-- This is the literal original colored sector polynomial in H.15. -/
def nativeWindowPolynomial (r : Source ι a b) (ha : 0<a) (D : FixedCubeDatum)
    (ω₁ ω₂ η : Character) (χ : RayCharacter) (G : Id) (hG : Supported G) (L : Id)
    (t θ X : ℝ) (V : ℝ→ℂ) : ℂ :=
  rowPolynomial Finset.univ (CenteredMomentSecondSectorColumns.sectorElement G hG.1 (sourceColumns r))
    (fun I=>divisorCoefficient L
      (CenteredMomentSecondSectorColumns.sectorElement G hG.1 (sourceColumns r))
      (CenteredMomentSecondScaled.movingCoefficient D.A
        (CenteredMomentSecondSectorColumns.sectorElement G hG.1 (sourceColumns r))
        (fun I=>TwistedRawSource.sourceColumn r ha (idealCoeff ω₁) (idealCoeff ω₂) 1 (G*I)*heightCoeff η t I)) χ I*
      columnPhase V (Real.log ((Ideal.absNorm (I:Id):ℝ)/X)) θ) D.z

/-- Integrability follows from the original finite source columns. -/
lemma colored_physical_window_integrable (r : Source ι a b) (ha : 0<a) (hb : 0 ≤ b)
    (D : FixedCubeDatum) (ω₁ ω₂ : Character) (G : Id) (hG : Supported G) (L : Id) (hL : Squarefree L)
    (t θ X : ℝ) (hX : 0<X) (V : ℝ→ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V) :
    Integrable (fun w : ℝ=>columnDensity V hc hs w*logPhase (θ-w) (Real.log X)*
      coloredFullyAllocatedPhysicalHeight r ha hb D ω₁ ω₂ G L (t+2*Real.pi*(w-θ))) := by
  let c (I : CenteredMomentSecondSectorColumns.sectorPool G hG.1 (sourceColumns r)) : ℂ :=
    if L∣(I:Id) then TwistedRawSource.sourceColumn r ha (idealCoeff ω₁) (idealCoeff ω₂) 1 (G*I) else 0
  have hi (I : CenteredMomentSecondSectorColumns.sectorPool G hG.1 (sourceColumns r)) :=
    (height_column_integrable V hc hs D.row.χ I
      (CenteredMomentSecondSectorColumns.sectorPool_supported G hG.1 _ I).1 t θ X hX).const_mul (c I)
  have hh := (integrable_finsetSum Finset.univ (fun I _=>hi I)).const_mul
    (MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P)
  convert hh using 1
  funext w
  rw [←coloredSectorFixedHeight_eq_physical r ha hb D ω₁ ω₂ G hG L hL]
  unfold coloredSectorFixedHeight
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  dsimp only [c]
  ring

/-- The genuine fixed Fourier identity transfers the actual allocated-height
bound, retaining every profile and the complete Fourier moment. -/
theorem colored_window_square (r : Source ι a b) (ha : 0<a) (hb : 0 ≤ b)
    (D : FixedCubeDatum) (ω₁ ω₂ η : Character) (χ : RayCharacter)
    (hη : D.η=CenteredMomentChildRows.childCharacter η χ) (hm : D.m=nativeSourceMask r)
    (G : Id) (hG : Supported G) (L : Id) (hL : Squarefree L)
    (t θ X : ℝ) (hX : 0<X) (V : ℝ→ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V)
    (J : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (hheight : ∀ v : ℝ,‖coloredFullyAllocatedPhysicalHeight r ha hb D ω₁ ω₂ G L v‖^2 ≤ E*(1+‖v‖)^(2*J)) :
    ‖MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P*
      nativeWindowPolynomial r ha D ω₁ ω₂ η χ G hG L t θ X V‖^2 ≤
      (E*heightCost t θ^(2*J))*(windowMass V hc hs J)^2 := by
  rw [show MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P*
      nativeWindowPolynomial r ha D ω₁ ω₂ η χ G hG L t θ X V=_ from
    colored_source_rowPolynomial_window_physical r ha hb D ω₁ ω₂ η χ hη hm G hG L hL t θ X hX V hc hs]
  exact window_integral_square V hc hs J _ E t θ X hE
    (colored_physical_window_integrable r ha hb D ω₁ ω₂ G hG L hL t θ X hX V hc hs) hheight

#print axioms colored_window_square
end QRH.Cycle092.FixedFourierH15
