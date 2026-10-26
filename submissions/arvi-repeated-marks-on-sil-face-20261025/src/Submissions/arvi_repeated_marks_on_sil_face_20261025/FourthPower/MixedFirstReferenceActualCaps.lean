/- Copyright (c) 2026 Sil. Apache-2.0.
Actual selected-character conductor and reference exponent caps.
The extra omega is used only in the reference conductor exponent. The
physical selected volume, its exponent d, and all coefficient punctures
remain unchanged. 
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstReferenceEnergy
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstChosenEnergy

set_option autoImplicit false
namespace Candidate.FourthPower.MixedFirstReferenceActualCaps
universe u
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily
open CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentSecondHeightFamily CenteredMomentFirstPhysicalSource
open MixedFirstReferenceEnergy MixedFirstReferenceDispatch
open MixedFirstGeometricCaps MixedFirstChosenEnergy MixedFirstUniformLossBudget
open MixedSupplierFourthRow MixedSupplierPositive
open QRH.Record1252270103KernelMass (ideal_norm_one_le)
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

theorem fixed_seventytwo_norm : ((Ideal.span {(72 : O)}).absNorm : ℝ) = 5184 := by
  rw [←eisEmbedding_norm_sq_eq_absNorm_span,map_ofNat]
  norm_num

/-- In particular the actual ballProfile radius 2 is already covered by
the fixed presentation factor; no eta or moving conductor is charged twice. -/
theorem fixed_presentation_two_le : (2 : ℝ) ≤ fixedPresentationCost := by
  have hm := ideal_norm_one_le
    (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero)
  unfold fixedPresentationCost
  rw [fixed_seventytwo_norm]
  linarith

theorem actual_conductor_identity (η : Character) (F : Id) (K Z : ℝ)
    (hK : 0 < K) (hZ : 1 < Z) :
    conductorFactor η fixedBadMask F * (2*K) =
      (ReferenceCubicCharacter.conductorConstant : ℝ)*2*(F.absNorm : ℝ)*
        Z^(inputWidth η K Z) := by
  rw [input_width_power η K Z hK hZ]
  unfold conductorFactor fixedPresentationCost
  ring

theorem actual_row_disk_cap (η : Character) (K Z : ℝ)
    (hK : 0 < K) (hZ : 1 < Z) : 2*K ≤ Z^(inputWidth η K Z) := by
  rw [input_width_power η K Z hK hZ]
  have hη := ideal_norm_one_le η.modulus_ne_bot
  have hcost : (2 : ℝ) ≤ fixedPresentationCost*(η.modulus.absNorm : ℝ) :=
    fixed_presentation_two_le.trans
      (le_mul_of_one_le_right fixedPresentationCost_pos.le hη)
  exact mul_le_mul_of_nonneg_right hcost hK.le

/-- The actual selected products, including their annular padding.
No hypothetical dyadic F-window replaces selectedProducts. -/
theorem selected_norm_cap {α : Type u} [Fintype α]
    (q : Data α) (N : ℕ) (hN : Fintype.card α ≤ N)
    (hpool : ∀ i, ∀ I ∈ q.pool i, (I.absNorm : ℝ) ≤ 2*q.P i)
    (Z d : ℝ) (hZ : 0 < Z) (hvolume : MixedSelectedVolume.volume q = Z^d)
    (F : Id) (hF : F ∈ selectedProducts q) :
    (F.absNorm : ℝ) ≤ (2 : ℝ)^N*Z^d := by
  apply (MixedSelectedVolume.selected_products_norm q hpool F hF).trans
  unfold MixedSelectedVolume.scale
  rw [hvolume]
  exact mul_le_mul_of_nonneg_right (MixedSelectedVolume.padding_le q N hN)
    (Real.rpow_nonneg hZ.le d)

/-- This is a literal cap for the actual presented selected character.
R*seed is absent: it remains solely in the coefficient sixth-power mask. -/
def actualConductorCap (η : Character) (F : Id) (K : ℝ) : ℝ :=
  max 1 (conductorFactor η fixedBadMask F*(2*K))

theorem selected_character_cap (η : Character) (F : Id) (hF : Supported F)
    (K : ℝ) (z : O) (hz : z ≠ 0) (hrow : ‖eisEmbedding z‖^2 ≤ 2*K) :
    ((selectedCharacterAt η fixedBadMask F fixedBadMask_ne_zero hF
      (dvd_mul_right _ _) (dvd_mul_left _ _) z).modulus.absNorm : ℝ) ≤
        actualConductorCap η F K := by
  have hspan : ((Ideal.span {z}).absNorm : ℝ) ≤ 2*K := by
    simpa only [eisEmbedding_norm_sq_eq_absNorm_span] using hrow
  exact (selected_modulus η fixedBadMask F fixedBadMask_ne_zero hF
      (dvd_mul_right _ _) (dvd_mul_left _ _) z hz).trans
    ((mul_le_mul_of_nonneg_left hspan (conductor_factor_nonneg η fixedBadMask F)).trans
      (le_max_right _ _))

/-- A single threshold pays only the fixed cubic-character constant and
the fixed annular padding. All source types of card <= N, selected sets,
characters, K and actual d occur AFTER that threshold. -/
theorem eventually_actual_caps (N : ℕ) (omega : ℝ) (homega : 0 < omega) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (α : Type u) [Fintype α], ∀ q : Data α,
      Fintype.card α ≤ N →
      (∀ i, ∀ I ∈ q.pool i, (I.absNorm : ℝ) ≤ 2*q.P i) →
      ∀ d : ℝ, 0 ≤ d → MixedSelectedVolume.volume q = Z^d →
      ∀ (η : Character) (K : ℝ), 0 < K → 0 ≤ inputWidth η K Z →
      ∀ F ∈ selectedProducts q,
      let R := inputWidth η K Z
      let U := actualConductorCap η F K
      (F.absNorm : ℝ) ≤ (2 : ℝ)^N*Z^d ∧
      2*K ≤ Z^R ∧ 1 ≤ U ∧ conductorFactor η fixedBadMask F*(2*K) ≤ U ∧
      U ≤ Z^(R+(d+omega)) ∧
      (∀ Kcap : ℝ, R+d+omega ≤ Kcap → U ≤ Z^Kcap) := by
  have hfixed : ∀ᶠ Z : ℝ in atTop,
      (ReferenceCubicCharacter.conductorConstant : ℝ)*2*(2 : ℝ)^N ≤ Z^omega :=
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop homega)) _
  filter_upwards [hfixed,Filter.eventually_gt_atTop (1 : ℝ)] with Z hfixed hZ
  refine ⟨hZ,?_⟩
  intro α instα q hN hpool d hd hvolume η K hK hR F hF
  dsimp only
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hFcap := selected_norm_cap q N hN hpool Z d hz hvolume F hF
  have hpaid : conductorFactor η fixedBadMask F*(2*K) ≤
      Z^(inputWidth η K Z+(d+omega)) := by
    rw [actual_conductor_identity η F K Z hK hZ]
    calc
      _ ≤ ((ReferenceCubicCharacter.conductorConstant : ℝ)*2*
          ((2 : ℝ)^N*Z^d))*Z^(inputWidth η K Z) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hFcap (by positivity))
          (Real.rpow_nonneg hz.le _)
      _ = ((ReferenceCubicCharacter.conductorConstant : ℝ)*2*(2 : ℝ)^N)*
          (Z^d*Z^(inputWidth η K Z)) := by ring
      _ ≤ Z^omega*(Z^d*Z^(inputWidth η K Z)) :=
        mul_le_mul_of_nonneg_right hfixed (by positivity)
      _ = _ := by
        rw [←Real.rpow_add hz,←Real.rpow_add hz]
        congr 1
        ring
  have hcap : actualConductorCap η F K ≤ Z^(inputWidth η K Z+(d+omega)) :=
    max_le (Real.one_le_rpow hZ.le (by linarith)) hpaid
  refine ⟨hFcap,actual_row_disk_cap η K Z hK hZ,le_max_left _ _,le_max_right _ _,hcap,?_⟩
  intro Kcap hKcap
  exact hcap.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))

/-- Coarse polynomial admissibility follows from actual width and volume
caps; this is separate from the sharp R+d+omega conductor bound. -/
theorem coarse_cap (η : Character) (F : Id) (K Z R d omega BR Bd : ℝ)
    (hZ : 1 ≤ Z) (hcap : actualConductorCap η F K ≤ Z^(R+(d+omega)))
    (hR : R ≤ BR) (hd : d ≤ Bd) :
    actualConductorCap η F K ≤ Z^(BR+Bd+omega) :=
  hcap.trans (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))

/-- The actual finite slot dimension pays the fixed short-reference
constant on a common event. This is not a profile or energy assumption. -/
theorem eventually_reference_padding (N : ℕ) (b deltaRef : ℝ)
    (hb : 0 ≤ b) (hdelta : 0 < deltaRef) :
    ∀ᶠ Z : ℝ in atTop, ∀ (α : Type u) [Fintype α], Fintype.card α ≤ N →
      (b+4)*b*(2 : ℝ)^Fintype.card α ≤ Z^deltaRef := by
  have hf : ∀ᶠ Z : ℝ in atTop, (b+4)*b*(2 : ℝ)^N ≤ Z^deltaRef :=
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hdelta)) _
  filter_upwards [hf] with Z hf
  intro α instα hN
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hN)
    (by positivity)).trans hf

/-- The midpoint chosen with PHYSICAL d has room for d+omega only in
the short-reference call. Both precise short-reference inequalities and
the strengthened mixed gate are derived from the original strict reserve. -/
theorem centered_reference_gates (R P S d rho omega deltaRef L : ℝ)
    (hrho : 0 < rho) (hS : 0 ≤ S) (hd : 0 ≤ d)
    (hcap : P+2*S+4*d ≤ R-rho) (hcenter : 5*R/6-7*d/3 < P+S)
    (homega : 0 ≤ omega) (homegaSmall : omega ≤ rho/100)
    (hdelta : 0 ≤ deltaRef) (hdeltaSmall : deltaRef ≤ rho/200)
    (hL : (9/5 : ℝ)*R ≤ L) :
    let l := referenceExponent R P S d
    0 < l ∧ l < P/2 ∧ 0 ≤ d+omega ∧ 0 ≤ deltaRef ∧
      P+2*S+4*(d+omega) < R ∧
      R+(l+(R+(d+omega))/2+S+2*deltaRef) ≤ L ∧
      l+(R+(d+omega))/2+S+2*deltaRef ≤ (4/5)*R ∧
      R+(d+omega)+2*l-P+S+2*deltaRef ≤ R/2 := by
  have hm := reference_exponent_margins R P S d rho omega deltaRef
    hrho hS hd hcap hcenter homegaSmall hdeltaSmall
  dsimp only at hm ⊢
  refine ⟨hm.1,hm.2.1,by linarith,hdelta,by linarith,?_,hm.2.2.1,hm.2.2.2⟩
  linarith [hm.2.2.1]

end
end Candidate.FourthPower.MixedFirstReferenceActualCaps
