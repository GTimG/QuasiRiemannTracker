/- Copyright (c) 2026 Sil. Apache-2.0.
The outer physical width is a declared paid allowance, not a lower bound
on the modulus of its sharp character or on its actual dyadic radius.
This exact adapter chooses the corresponding source-theorem cutoff and
inserts its radial majorant on the literal physical rows. No moment
estimate or mixed capacity gate is assumed or proved here.
The global numerical cutoff allowance is a separate explicit obligation.
-/
import Candidate.Feedback.FourthPower.OuterFreshSelectedWindow
import Candidate.Feedback.FourthPower.MixedFirstChosenEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondChildRadialWidth

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.OuterFreshDeclaredRadius
universe u v
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss RayFourExpansion
open QRH.Record1252270103KernelMass
open CenteredMomentSecondCanonical CenteredMomentSecondHeightFamily
open CenteredMomentCanonicalFirst CenteredMomentSecondRadicalBudget
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondLiveBlock
open CenteredMomentSecondDyadicRowSupport CenteredMomentSecondChildRadialWidth
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentHeckeColumnWindow CenteredMomentOriginalRadialComparison
open CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentFirstPhysicalSource
open MixedPrincipalPair MixedFirstGeometricCaps MixedFirstChosenEnergy
open MixedInnerExceptionalBlock
open MixedFirstSourceWindow MixedFirstSeededEnergy MixedSupplierFourthRow
open MixedSupplierPositive OuterFreshNonexceptionalFamily
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α⊕Fin 2) := Classical.decEq _

def paddedRadius (η : Character) (Z R : ℝ) : ℝ :=
  Z^R/(fixedPresentationCost*(η.modulus.absNorm:ℝ))

theorem padded_pos (η : Character) (Z R : ℝ) (hZ : 0<Z) :
    0<paddedRadius η Z R := by
  have hη := zero_lt_one.trans_le (ideal_norm_one_le η.modulus_ne_bot)
  exact div_pos (Real.rpow_pos_of_pos hZ _) (mul_pos fixedPresentationCost_pos hη)

/-- The exact source input width, including its fixed presentation factor. -/
theorem padded_input_width (η : Character) (Z R : ℝ) (hZ : 1<Z) :
    inputWidth η (paddedRadius η Z R) Z=R := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hη : 0<(η.modulus.absNorm:ℝ) :=
    zero_lt_one.trans_le (ideal_norm_one_le η.modulus_ne_bot)
  unfold inputWidth paddedRadius
  rw [Real.logb_div (Real.rpow_pos_of_pos hz _).ne'
      (mul_pos fixedPresentationCost_pos hη).ne',
    Real.logb_mul fixedPresentationCost_pos.ne' hη.ne',
    Real.logb_rpow hz hZ.ne']
  ring

/-- N(eta) is paid once. It is never replaced by an upper modulus bound
inside a premise requiring a lower available width. -/
theorem padded_paid (η : Character) (Z R : ℝ) :
    (η.modulus.absNorm:ℝ)*paddedRadius η Z R=Z^R/fixedPresentationCost := by
  have hη : (η.modulus.absNorm:ℝ)≠0 :=
    (zero_lt_one.trans_le (ideal_norm_one_le η.modulus_ne_bot)).ne'
  unfold paddedRadius
  field_simp [hη,fixedPresentationCost_pos.ne']

theorem row_le_padded (η : Character) (Z R : ℝ) (hZ : 1<Z)
    (z : O) (hz : z≠0)
    (hwidth : Real.logb Z (normValue z)+Real.logb Z (η.modulus.absNorm:ℝ)+
      Real.logb Z fixedPresentationCost≤R) :
    normValue z≤paddedRadius η Z R := by
  have hn := normValue_pos z hz
  have hη : 0<(η.modulus.absNorm:ℝ) :=
    zero_lt_one.trans_le (ideal_norm_one_le η.modulus_ne_bot)
  have hden := mul_pos fixedPresentationCost_pos hη
  change normValue z≤Z^R/(fixedPresentationCost*(η.modulus.absNorm:ℝ))
  apply (le_div_iff₀ hden).mpr
  apply (Real.logb_le_iff_le_rpow hZ (mul_pos hn hden)).mp
  rw [Real.logb_mul hn.ne' hden.ne',
    Real.logb_mul fixedPresentationCost_pos.ne' hη.ne']
  linarith

/-- All fixed factors can be admitted before eta, its actual modulus,
and the declared width are chosen. A nonnegative declared width makes
the inverse cutoff cost only the actual conductor and one fixed slack. -/
theorem padded_caps_eventually (ε : ℝ) (hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀(η : Character)(R B Bη : ℝ),
      0≤R→R≤B→(η.modulus.absNorm:ℝ)≤Z^Bη→
      paddedRadius η Z R≤Z^B ∧ (paddedRadius η Z R)⁻¹≤Z^(Bη+ε) := by
  have hfixed : ∀ᶠZ : ℝ in atTop,fixedPresentationCost≤Z^ε :=
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) fixedPresentationCost
  filter_upwards [Filter.eventually_gt_atTop (1:ℝ),hfixed] with Z hZ hf
  refine ⟨hZ,?_⟩
  intro η R B Bη hR hRB hη
  have hz : 0<Z := zero_lt_one.trans hZ
  have hη1 : (1:ℝ)≤η.modulus.absNorm := ideal_norm_one_le η.modulus_ne_bot
  have hden1 : 1≤fixedPresentationCost*(η.modulus.absNorm:ℝ) :=
    one_le_mul_of_one_le_of_one_le fixed_presentation_one_le hη1
  have hR1 : 1≤Z^R := Real.one_le_rpow hZ.le hR
  constructor
  · exact (div_le_self (Real.rpow_nonneg hz.le _) hden1).trans
      (Real.rpow_le_rpow_of_exponent_le hZ.le hRB)
  · rw [paddedRadius,inv_div]
    calc
      _≤fixedPresentationCost*(η.modulus.absNorm:ℝ) :=
        div_le_self (mul_nonneg fixedPresentationCost_pos.le (Nat.cast_nonneg _)) hR1
      _≤Z^ε*Z^Bη := mul_le_mul hf hη (Nat.cast_nonneg _) (Real.rpow_nonneg hz.le _)
      _=Z^(Bη+ε) := by rw [←Real.rpow_add hz];congr 1;ring

/-- This is exactly the sharp physical upper width plus the source
presentation factor. The fixed supplier f occurs linearly, not as f^4.
The later root ledger must bound this expression by its paid Rdecl. -/
def physicalWidth (τ : Character) (f C E : Id)
    (U : Finset (CommonIndex C E)) (Rfreq Z : ℝ) : ℝ :=
  Real.logb Z Rfreq+Real.logb Z (τ.modulus.absNorm:ℝ)-
    Real.logb Z (normValue (commonFrequencyGenerator C E))+
    Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ))+
    Real.logb Z (ReferenceCubicCharacter.conductorConstant*f.absNorm:ℝ)+
    Real.logb Z fixedPresentationCost

theorem physical_rows_padded (τ : Character) (f : Id) (ξ : RayCharacter)
    (C E : Id) (hC : Supported C) (hE : Supported E)
    (U : Finset (CommonIndex C E)) (ψ : RayCharacter→Character)
    (hψ : SharpFamily τ f ξ C E hC hE U ψ)
    (t : ℝ) (S : Finset Id) (β : Id→ℂ) (Rfreq : ℝ) (rows : Finset O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (n : Fin 4→ℤ)
    (hne : physicalBlock τ t S β C E hC hE U Rfreq rows W K n≠0)
    (Z Rdecl : ℝ) (hZ : 1<Z) (hpaid : physicalWidth τ f C E U Rfreq Z≤Rdecl)
    (χ : RayCharacter) (z : O) (hz : z∈liveRows C E U Rfreq rows) :
    normValue z≤paddedRadius (ψ χ) Z Rdecl := by
  have hw := (hψ.physical_budget t S β Rfreq rows W K hK n hne χ).2 Z hZ z hz
  apply row_le_padded (ψ χ) Z Rdecl hZ z
    (liveRows_geometry C E U Rfreq rows z hz).2.1
  unfold physicalWidth at hpaid
  linarith

/-- The nonempty physical block itself supplies nonnegative declared
width and the native floor's dyadic scale >=1. Empty subunit annuli need
no analytic estimate. -/
theorem physical_nonempty_admission (τ : Character) (f : Id) (ξ : RayCharacter)
    (C E : Id) (hC : Supported C) (hE : Supported E)
    (U : Finset (CommonIndex C E)) (ψ : RayCharacter→Character)
    (hψ : SharpFamily τ f ξ C E hC hE U ψ)
    (t : ℝ) (S : Finset Id) (β : Id→ℂ) (Rfreq : ℝ) (rows : Finset O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (n : Fin 4→ℤ)
    (hne : physicalBlock τ t S β C E hC hE U Rfreq rows W K n≠0)
    (Z Rdecl : ℝ) (hZ : 1<Z) (hpaid : physicalWidth τ f C E U Rfreq Z≤Rdecl)
    (χ : RayCharacter) :
    0≤Rdecl ∧ 1≤dyadicScale (n 1) := by
  obtain ⟨z,hzl,hzd,hz,_⟩ := physicalBlock_live_dyadic_witness
    τ t S β C E hC hE U Rfreq rows W K n hne
  have hn : 1≤normValue z := normValue_ge_one z hz
  have hk := hn.trans (physical_rows_padded τ f ξ C E hC hE U ψ hψ
    t S β Rfreq rows W K hK n hne Z Rdecl hZ hpaid χ z hzl)
  have hlogK := Real.logb_nonneg hZ hk
  have hlogη := Real.logb_nonneg hZ (ideal_norm_one_le (ψ χ).modulus_ne_bot)
  have hlogF := Real.logb_nonneg hZ fixed_presentation_one_le
  have hi := padded_input_width (ψ χ) Z Rdecl hZ
  unfold inputWidth at hi
  exact ⟨by linarith,hn.trans (dyadicRows_norm rows n z hzd).2.le⟩

/-- Literal selected full-seed/window family on a finite set inside the
declared disk. The majorant equals 1, so no radius/cardinality loss is
inserted and the selected/source-volume denominators occur exactly once. -/
theorem finite_window_eq_padded {ι : Type u} [Fintype ι]
    {α : Type v} [Fintype α] {a b : ℝ} (q : Data α)
    (s : Source ι a b) (ha : 0<a) (D : Id) (η : Character) (tp : ℝ)
    (keep : Id→O→Prop) (Z Rdecl : ℝ) (hZ : 0<Z)
    (Vwin : ℝ→ℂ) (X θ : ℝ) (rows : Finset O)
    (hrows : ∀z∈rows,normValue z≤paddedRadius η Z Rdecl) :
    (∑F : selectedProducts q,(groupedWeight q F.val/MixedSelectedVolume.scale q)*
      ∑z∈rows,if keep F.val z then
        ‖windowedPolynomial s ha D F.val η fixedBadMask 1 tp Vwin X θ z‖^2 else 0)/
        sourceVolume s=
      seededGroupedWindowRows q s ha D η tp keep ballProfile
        (paddedRadius η Z Rdecl) Vwin X θ rows := by
  unfold seededGroupedWindowRows
  congr 1
  apply Finset.sum_congr rfl
  intro F hF
  apply congrArg (fun r : ℝ=>(groupedWeight q F.val/MixedSelectedVolume.scale q)*r)
  apply Finset.sum_congr rfl
  intro z hz
  have hball : (ballProfile (‖eisEmbedding z‖^2/paddedRadius η Z Rdecl)).re=1 :=
    le_antisymm (ballProfile_le_one _)
      (ballProfile_majorizes _ (padded_pos η Z Rdecl hZ) z (hrows z hz))
  by_cases hk : keep F.val z <;> simp only [hk,ite_true,ite_false,hball,one_mul,zero_mul]

/-- Direct specialization to the actual nonzero physical annulus. This
is the row-set to use after physicalBlock_live_dyadic_rows. Both original
characters and the selected parameter remain exactly as in the source. -/
theorem physical_window_eq_padded {ι : Type u} [Fintype ι]
    {α : Type v} [Fintype α] {a b : ℝ} (q : Data α)
    (s : Source ι a b) (ha : 0<a) (D : Id)
    (τ : Character) (f : Id) (ξ : RayCharacter)
    (C E : Id) (hC : Supported C) (hE : Supported E)
    (U : Finset (CommonIndex C E)) (ψ : RayCharacter→Character)
    (hψ : SharpFamily τ f ξ C E hC hE U ψ)
    (t : ℝ) (S : Finset Id) (β : Id→ℂ) (Rfreq : ℝ) (rows : Finset O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (n : Fin 4→ℤ)
    (hne : physicalBlock τ t S β C E hC hE U Rfreq rows W K n≠0)
    (Z Rdecl : ℝ) (hZ : 1<Z) (hpaid : physicalWidth τ f C E U Rfreq Z≤Rdecl)
    (χ : RayCharacter) (tp : ℝ) (keep : Id→O→Prop) (Vwin : ℝ→ℂ) (X θ : ℝ) :
    let actualRows:=dyadicRows (liveRows C E U Rfreq rows) n
    (∑F : selectedProducts q,(groupedWeight q F.val/MixedSelectedVolume.scale q)*
      ∑z∈actualRows,if keep F.val z then
        ‖windowedPolynomial s ha D F.val (ψ χ) fixedBadMask 1 tp Vwin X θ z‖^2 else 0)/
        sourceVolume s=
      seededGroupedWindowRows q s ha D (ψ χ) tp keep ballProfile
        (paddedRadius (ψ χ) Z Rdecl) Vwin X θ actualRows := by
  apply finite_window_eq_padded q s ha D (ψ χ) tp keep Z Rdecl
    (zero_lt_one.trans hZ) Vwin X θ
  intro z hz
  exact physical_rows_padded τ f ξ C E hC hE U ψ hψ t S β Rfreq rows W K hK n hne
    Z Rdecl hZ hpaid χ z (dyadicRows_subset _ n hz)

end
end Candidate.Feedback.FourthPower.OuterFreshDeclaredRadius
