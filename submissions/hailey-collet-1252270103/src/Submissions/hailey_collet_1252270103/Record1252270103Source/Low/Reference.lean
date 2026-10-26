/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Uses Hailey Collet's Cycle61 first-reflection/independent-height interfaces;
underlying natural terminal and reflection analysis: OpenAI/math, Apache-2.0.
The natural incumbent assembly retains Zhongpai Gao and DaysSky attribution. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.Geometry
import Submissions.hailey_collet_1252270103.Record12518109Source.Incumbent
import Submissions.hailey_collet_1252270103.Cycle61.Physical.FirstBranches.Reflection
import Submissions.hailey_collet_1252270103.Cycle61.Physical.FirstBranches.Direct

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Low
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily HeckeDyadic ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentAllocatedNaturalRadial CenteredMomentSectorLocalization
open CenteredMomentCommonMaskEnergy CenteredMomentSecondHeightFamily CenteredMomentNaturalRowSource
open Cycle61FirstGeometry Cycle61FirstReflection
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O ⧸ rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- The actual ordinary short-factor/reference energy for the C28 adjustable
reference. The proved incumbent supplies every daughter. The full effective mask,
canonical relative slots and independent plain heights remain literal. The
reflection tail is explicit. There is no quarter-width or .04 slot restriction. -/
theorem actual_short_reference
    (κ Kcap : ℝ) (hκlo : 7/10 ≤ κ) (hκhi : κ ≤ 3/4)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ κ) (hKcap : 6*κ ≤ Kcap)
    (Fmax : Finset α) (Wslot : ℝ → ℂ) (aslot bslot lo hi : ℝ)
    (haslot : 0 < aslot) (hsSlot : Function.support Wslot ⊆ Set.Icc aslot bslot)
    (hWslot : ContDiff ℝ ∞ Wslot) (hbslot : 0 ≤ bslot)
    (a b bΦ epsilon xi saving Bmask L Mcap ε : ℝ)
    (ha : 0 < a) (hlo : a ≤ 1/4) (hhi : 1 ≤ b) (hbΦ : 0 < bΦ)
    (hepsilon : 0 < epsilon) (hxi : 0 < xi)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hε : 0 < ε) (hL : Mcap+xi ≤ L)
    (hbeta : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (B : ℕ) (hB : 2 ≤ B) :
    ∃ degree : ℕ, ∃ Sd : Finset (ℕ × ℕ), ∃ n : ℕ,
    ∃ T : Finset (ℕ × ℕ), ∃ Dchild : ℝ, 0 < Dchild ∧
    ∃ nlong : ℕ, ∃ Slong : Finset (ℕ × ℕ), ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
    ∀ η₀ : Character, ∀ Q : Ideal O, Q ≤ rayM → internalQ Q η₀ ≠ 0 →
      internalQ Q η₀ ≠ ⊤ → internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (F : Finset α), F ⊆ Fmax →
    ∀ (θ : α → RayQuotient.Characters rayM H) (w σ freq : α → ℝ) (u t height : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ Cycle25.Energy.commonMesh Mcap Bmask L ε) →
      (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) → 0 ≤ height → (∀ i, |freq i| ≤ height) →
    ∀ s : NaturalState Z Bmask bΦ, s.fixedModulus = internalQ Q η₀ → s.width ≤ Mcap →
    ∀ (Wlong Wshort : 𝓢(ℝ,ℂ)),
    ∀ hsLong : Function.support (Wlong : ℝ→ℂ) ⊆ Set.Icc a b,
    ∀ hsShort : Function.support (Wshort : ℝ→ℂ) ⊆ Set.Icc a b,
    ∀ Mrow along short r cap : ℝ,
      0 ≤ Mrow → Mrow ≤ s.width → 0 ≤ r → 0 ≤ cap → short ≤ r →
      (∑ i ∈ F, w i) ≤ cap → r+Kcap*cap ≤ 49*Mrow/100 → xi ≤ Mrow/100 →
    let direct := K*diagonalControl s.radial.profile*
      ((independentProfiles ha Wlong Wshort hsLong hsShort u t).control Sd)^2*
      (1+|t|+height)^degree*Z^(s.width+ε)
    let E := K*diagonalControl s.radial.profile*Dchild*(sourceControl T Wshort)^2*
      (1+|t|+height)^(degree+2*n)*Z^(s.width+ε)
    let reflected :=
      C*(max 1 ((fixedConductorFactor : ℝ)*bΦ*Z^s.width))^epsilon*
        (sourceControl Slong Wlong)^2*(1+‖u‖)^(2*nlong)*
        (1+2*(max 0 (s.width-along+xi)*Real.log Z))*E +
      D*(max 1 ((fixedConductorFactor : ℝ)*bΦ*Z^s.width))^(2*epsilon)*
        (sourceControl Slong Wlong)^2*(1+‖u‖)^(2*nlong)*Z^(-2*saving)*
        ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) Wshort)^2*
          diagonalControl s.radial.profile*max 1 s.radial.scale*Z^short*∏ i ∈ F, Z^(w i)
    radialEnergy (fun z =>
      polynomial (naturalCharacter s.character z) false Wlong (Z^along) 0 u *
      polynomial (naturalCharacter s.character z) false Wshort (Z^short) 0 t *
      ∏ i ∈ F, naturalSlot (naturalCharacter s.character z) (primePool rayM H bslot (Z^(w i)))
        (heightCoefficient (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i)))
      (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤ direct+reflected := by
  obtain ⟨degree,Sd,hterminal⟩ := Record12518109SourceLow.incumbent_at (α:=α)
    rayM H hH κ hκlo hκhi hκbeta Wslot aslot bslot a b bΦ Bmask L lo hi Mcap ε
    haslot hsSlot hWslot hbslot ha hlo hhi hbΦ hmask hMcap hε hbeta
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩ :=
    reference_from_positive_with_error (α:=α) rayM H hH Fmax Wslot aslot bslot lo hi
      haslot hsSlot hWslot.continuous a b bΦ epsilon xi saving L
      ha hlo hhi hbΦ hepsilon hxi B hB degree Sd
  refine ⟨degree,Sd,n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Kzero,K,hKzero,hK,ht⟩ := hterminal η₀ Q hQM hQ0 hQt hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [ht,href] with Z hz hrfl
  refine ⟨hz.1,?_⟩
  intro F hF θ w σ freq u t height hw hwmesh hσlo hσhi hheight hfreq
    s hQ hs Wlong Wshort hsLong hsShort Mrow along short r cap
    hM hMw hr hcap hshort hslots hbudget hpad
  dsimp only
  have hZ : 0 < Z := zero_lt_one.trans hz.1
  have hκ : 0 ≤ 6*κ := by linarith
  have hKcap0 : 0 ≤ Kcap := hκ.trans hKcap
  have hscalar : r+(6*κ)*cap ≤ 49*Mrow/100 := by
    have hh := mul_le_mul_of_nonneg_right hKcap hcap
    linarith
  have hrcap : r ≤ Mcap := by
    have hkc := mul_nonneg hKcap0 hcap
    linarith
  have hshortL : short ≤ L := by linarith
  have hdiag := diagonalControl_nonneg s.radial.profile
  have hlog : 0 ≤ Real.log Z := (Real.log_pos hz.1).le
  by_cases hlong : along ≤ Mrow/2
  · have hc := direct_short_capacity Z Mrow s.width short along (∑ i ∈ F,w i)
      r cap (6*κ) hz.1 hM hMw hr hκ hshort hslots hscalar hlong
    have hl : along ≤ L := by linarith
    have hd := Cycle61FirstDirect.direct_child_from_positive rayM H hH Wslot bslot a b bΦ
      Bmask L (Cycle25.Energy.commonMesh Mcap Bmask L ε) lo hi Mcap ε κ Z η₀ Q
      degree Sd K hz.2.2 hmask ha F θ w σ freq u t height hw hwmesh hσlo hσhi hheight hfreq
      s hQ hs Wlong Wshort hsLong hsShort (Z^along) (Z^short)
      (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
      (Real.rpow_le_rpow_of_exponent_le hz.1.le hl)
      (Real.rpow_le_rpow_of_exponent_le hz.1.le hshortL) hc
    exact hd.trans (le_add_of_nonneg_right (by positivity))
  · have hlong' : Mrow/2 ≤ along := le_of_not_ge hlong
    have hlength : s.width ≤ L+along := by linarith
    have hwindow : max 0 (s.width-along+xi) ≤ L :=
      max_le (by linarith) (by linarith)
    have hc := clipped_short_capacity Z Mrow s.width short along (∑ i ∈ F,w i)
      r cap (6*κ) xi hz.1 hM hMw hr hcap hκ hshort hslots hscalar hlong' hxi.le hpad
    have hh := hrfl.2 Bmask L (Cycle25.Energy.commonMesh Mcap Bmask L ε) Mcap ε κ
      η₀ Q K hK.le hz.2.2 hmask F hF θ w σ freq u t height hw hwmesh hσlo hσhi
      hheight hfreq s hQ hs Wlong Wshort hsLong hsShort along short hlength hwindow hshortL hc
    exact hh.trans (le_add_of_nonneg_left (by positivity))

end
end OAI.SevenEighths.Record1252270103Low
#print axioms OAI.SevenEighths.Record1252270103Low.actual_short_reference
