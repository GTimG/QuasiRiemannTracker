/- Copyright (c) 2026 Sil. Apache-2.0.
The actual selected-product short reference with its conductor, radial
cutoff, fixed padding, midpoint and all profile costs supplied. The
physical d remains log_Z of the selected volume; only the reference
character call uses d+rho/100. Parent alone runs the pinned Lean check.
-/
import Candidate.SilPrior.FourthPower.MixedFirstReferenceOrientation
import Candidate.SilPrior.FourthPower.MixedFirstReferenceActualCaps

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.MixedFirstActualReference
universe u v
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CompletedGauss (primaryGenerator)
open QRH.Record1252270103KernelMass
open CenteredMomentSourceProfileMass CenteredMomentFiniteProfileExceptional
open CenteredMomentOriginalRadialComparison CenteredMomentAddedZeroUniform
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredExceptionalProfile ReferencePrimeEnclosure
open MixedPrincipalPair MixedCanonicalSource MixedSupplierFourthRow MixedSupplierPositive
open MixedFirstReferenceDispatch MixedFirstReferenceEnergy MixedFirstReferenceOrientation
open MixedFirstReferenceProfileBudget MixedFirstReferenceActualCaps
open MixedFirstGeometricCaps MixedFirstChosenEnergy
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α ⊕ Fin 2) := Classical.decEq _

/-- Constants and the eventual threshold precede all live subsets,
selected supplier data, original profiles, heights and actual characters.
The only exponent hypotheses are the original mixed reserve, centered
branch, and coarse polynomial caps. All short-reference scalar gates,
the actual U, and the fixed annular/cubic constants are constructed.

The marked exponent S is still explicit with prod(s.P) <= Z^S; its
canonical specialization S=sum(w) is the later source dispatcher input.
The short-length alternative is the literal branch being estimated. -/
theorem uniform_actual_reference {ι : Type u} [Fintype ι]
    (N : ℕ) (hcard : Fintype.card ι ≤ N)
    (ε a b BR Bd rho Bf : ℝ)
    (hε : 0 < ε) (ha : 0 < a) (hb : 0 ≤ b)
    (hBR : 0 ≤ BR) (hBd : 0 ≤ Bd) (hrho : 0 < rho) (hBf : 1 ≤ Bf) :
    let L := 2*(BR+1)
    let Kcap := BR+Bd+rho+1
    ∃ J : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧ (0,0) ∈ control ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (T : Finset ι) (s : Source T a b), (∀ i, s.M i ≤ Bf) →
      ∀ (α : Type v) [Fintype α], ∀ q : Data α,
      Fintype.card α ≤ N →
      (∀ i, ∀ I ∈ q.pool i, (I.absNorm : ℝ) ≤ 2*q.P i) →
      1 ≤ MixedSelectedVolume.volume q → MixedSelectedVolume.volume q ≤ Z^Bd →
      ∀ (η : Character) (K X₁ X₂ S : ℝ), 0 < K → 0 < X₁ → 0 < X₂ → 0 ≤ S →
      let R := inputWidth η K Z
      let P := Real.logb Z (X₁*X₂)
      let d := Real.logb Z (MixedSelectedVolume.volume q)
      let l := referenceExponent R P S d
      R ≤ BR → P+2*S+4*d ≤ R-rho → 5*R/6-7*d/3 < P+S →
      (X₁ ≤ Z^l ∨ X₂ ≤ Z^l) →
      ((s.Fhole*s.R).absNorm : ℝ) ≤ Z^Kcap →
      (∀ P ∈ s.S, (P.val.absNorm : ℝ) ≤ Z^Kcap) →
      (∀ I, Supported I → ((I.absNorm : ℝ) ≤ b*X₁ ∨ (I.absNorm : ℝ) ≤ b*X₂) →
        primeSupport I ⊆ primeValues s.S) →
      (∏ i, 2*s.P i) ≤ Z^L → b*X₁*(∏ i, 2*s.P i) ≤ Z^L →
      b*X₂*(∏ i, 2*s.P i) ≤ Z^L → (∏ i, s.P i) ≤ Z^S →
      ∀ (t t₀ V : ℝ) (ν : T → Character) (R₀ : T → Finset Id),
      0 ≤ V → s.ν = slotCoefficient ν R₀ t₀ → (∀ i P, P ∈ s.H → P.val ∈ R₀ i) →
      ∀ (F : Id) (hF : F ∈ selectedProducts q) (Q : Id) (keep : O → Prop),
      (∀ z, keep z → z ≠ 0) →
      (∀ z, keep z → ¬FixedInducingRow η Q fixedBadMask ((primaryGenerator F)^2) z) →
      ∀ Φ : 𝓢(ℝ,ℂ), Function.support (Φ : ℝ → ℂ) ⊆ Iic 2 →
      radialEnergy (fun z => heightRectangle s ha
        (selectedCharacterAt η fixedBadMask F fixedBadMask_ne_zero
          (selected_products_supported q F hF) (dvd_mul_right _ _) (dvd_mul_left _ _) z)
        t X₁ X₂) keep Φ K ≤
        radialControl Φ * (C*(sourceControl control s.W₁*sourceControl control s.W₂)^2*
          (MixedFirstProfileEnvelope.height t V s.t₁ s.t₂)^J*
          ((η.modulus.absNorm : ℝ)*K)*Z^ε) := by
  dsimp only
  let L : ℝ := 2*(BR+1)
  let Kcap : ℝ := BR+Bd+rho+1
  let omega : ℝ := rho/100
  let deltaRef : ℝ := omega/2
  have hL : 0 < L := by dsimp [L]; linarith
  have hKcap : 0 < Kcap := by dsimp [Kcap]; linarith
  have homega : 0 < omega := by dsimp [omega]; positivity
  have hdelta : 0 < deltaRef := half_pos homega
  have homegaSmall : omega ≤ rho/100 := le_rfl
  have hdeltaSmall : deltaRef ≤ rho/200 := by dsimp [deltaRef,omega]; linarith
  have hxi : omega/2 ≤ deltaRef := le_rfl
  obtain ⟨J,control,C,hC,h00,hbound⟩ := uniform_profiled_reference_energy_either (ι := ι)
    ε L Kcap a b omega Bf hε hL hKcap ha hb homega hBf
  have hc := eventually_actual_caps.{v} N omega homega
  have hp := eventually_reference_padding.{u} N b deltaRef hb hdelta
  refine ⟨J,control,C*fixedPresentationCost,mul_pos hC fixedPresentationCost_pos,h00,?_⟩
  filter_upwards [hc,hp] with Z hcZ hpZ
  have hZ : 1 < Z := hcZ.1
  have hz : 0 < Z := zero_lt_one.trans hZ
  refine ⟨hZ,?_⟩
  intro T s hMs α instα q hα hqpool hqvolume hqcap η K X₁ X₂ S hK hX₁ hX₂ hS
    hRcap hcap hcenter hshort hholes hScap henclose hVcap hvolume₁ hvolume₂ hVsharp
    t t₀ V ν R₀ hV hν hHR F hF Q keep hkeep heligible Φ hΦ
  let R := inputWidth η K Z
  let P := Real.logb Z (X₁*X₂)
  let d := Real.logb Z (MixedSelectedVolume.volume q)
  let l := referenceExponent R P S d
  have hd : 0 ≤ d := Real.logb_nonneg hZ hqvolume
  have hR : 0 ≤ R := by linarith
  have hdCap : d ≤ Bd := by
    have hh := Real.logb_le_logb_of_le hZ (zero_lt_one.trans_le hqvolume) hqcap
    simpa only [Real.logb_rpow hz hZ.ne'] using hh
  have hqpower : MixedSelectedVolume.volume q = Z^d :=
    (Real.rpow_logb hz hZ.ne' (zero_lt_one.trans_le hqvolume)).symm
  have hproduct : X₁*X₂ = Z^P :=
    (Real.rpow_logb hz hZ.ne' (mul_pos hX₁ hX₂)).symm
  have hLwidth : (9/5 : ℝ)*R ≤ L := by dsimp [L]; linarith
  have hg := centered_reference_gates R P S d rho omega deltaRef L
    hrho hS hd hcap hcenter homega.le homegaSmall hdelta.le hdeltaSmall hLwidth
  dsimp only at hg
  have hactual := hcZ.2 α q hα hqpool d hd hqpower η K hK hR F hF
  dsimp only at hactual
  let U := actualConductorCap η F K
  have hUcap : U ≤ Z^Kcap := hactual.2.2.2.2.2 Kcap (by
    dsimp only [Kcap,omega]
    linarith)
  have hcardT : Fintype.card T ≤ N := by
    rw [Fintype.card_coe]
    exact (Finset.card_le_card (Finset.subset_univ T)).trans (by simpa using hcard)
  have hpadding : (b+4)*b*(2:ℝ)^Fintype.card T ≤ Z^deltaRef := hpZ T hcardT
  have hβ (i : T) (I : Id) (hI : I ∈ s.pool i) :
      ‖slotCoefficient ν R₀ (t₀+t) i I*s.Wslot i (I.absNorm/s.P i)‖ ≤ Bf := by
    rw [shifted_slot_norm ν R₀ t₀ t i I (s.hpn i I hI).1.1 (s.Wslot i) (s.P i),←hν,norm_mul]
    exact (mul_le_mul (s.hν i I) (s.hWnorm i (I.absNorm/s.P i))
      (norm_nonneg _) zero_le_one).trans (by simpa only [one_mul] using hMs i)
  have he := hbound T s Z R P S (d+omega) l deltaRef hZ.le hR hS hg.2.2.1 hg.1.le
    hg.2.2.2.1 hg.2.2.2.2.1 hg.2.2.2.2.2.1 hg.2.2.2.2.2.2.1 hg.2.2.2.2.2.2.2
    hpadding hxi η fixedBadMask F Q fixedBadMask_ne_zero
    (selected_products_supported q F hF) (dvd_mul_right _ _) (dvd_mul_left _ _)
    keep hkeep heligible U X₁ X₂ t t₀ V ν R₀ hν
    hactual.2.2.1 hUcap hactual.2.2.2.2.1 hX₁ hX₂ hproduct hshort hV
    hholes hScap henclose hβ hHR hVcap hvolume₁ hvolume₂ hVsharp
    Φ K 2 hK (by norm_num) hΦ hactual.2.1 hactual.2.2.2.1
  apply he.trans_eq
  rw [Real.rpow_add hz,input_width_power η K Z hK hZ]
  ring

/- APPENDIX FRAGMENT for MixedFirstActualReference.lean.
Insert before the final `end` / namespace end. The existing imports
already contain MixedFirstSelectedMass through MixedFirstChosenEnergy.
No extra source module is needed. Parent alone checks Lean.
-/
open MixedFirstSelectedMass

/-- The actual normalized grouped family of short references. The source,
displayed lengths, profiles and all exponents are common to every F,
while the retained nonprincipal restriction is allowed to depend on F.
No positivity of Phi is needed for this upper bound: the weights and
the common upper budget are nonnegative. -/
theorem uniform_actual_reference_weighted {ι : Type u} [Fintype ι]
    (N : ℕ) (hcard : Fintype.card ι ≤ N)
    (ε a b BR Bd Bsel rho Bf : ℝ)
    (hε : 0 < ε) (ha : 0 < a) (hb : 0 ≤ b)
    (hBR : 0 ≤ BR) (hBd : 0 ≤ Bd) (hBsel : 0 ≤ Bsel)
    (hrho : 0 < rho) (hBf : 1 ≤ Bf) :
    let L := 2*(BR+1)
    let Kcap := BR+Bd+rho+1
    ∃ J : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧ (0,0) ∈ control ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (T : Finset ι) (s : Source T a b), (∀ i, s.M i ≤ Bf) →
      ∀ (α : Type v) [Fintype α], ∀ q : Data α,
      Fintype.card α ≤ N → (∀ i, 0 < q.P i) →
      (∀ i, ∀ I ∈ q.pool i, (I.absNorm : ℝ) ≤ 2*q.P i) →
      1 ≤ MixedSelectedVolume.volume q → MixedSelectedVolume.volume q ≤ Z^Bd →
      MixedSelectedVolume.scale q ≤ Z^Bsel →
      ∀ Kslot : ℝ, 1 ≤ Kslot →
      (∀ i, ∀ I ∈ q.pool i, ‖q.ν i I‖ ≤ 1) →
      (∀ i x, ‖q.Wslot i x‖ ≤ Kslot) →
      ∀ (η : Character) (K X₁ X₂ S : ℝ), 0 < K → 0 < X₁ → 0 < X₂ → 0 ≤ S →
      let R := inputWidth η K Z
      let P := Real.logb Z (X₁*X₂)
      let d := Real.logb Z (MixedSelectedVolume.volume q)
      let l := referenceExponent R P S d
      R ≤ BR → P+2*S+4*d ≤ R-rho → 5*R/6-7*d/3 < P+S →
      (X₁ ≤ Z^l ∨ X₂ ≤ Z^l) →
      ((s.Fhole*s.R).absNorm : ℝ) ≤ Z^Kcap →
      (∀ P ∈ s.S, (P.val.absNorm : ℝ) ≤ Z^Kcap) →
      (∀ I, Supported I → ((I.absNorm : ℝ) ≤ b*X₁ ∨ (I.absNorm : ℝ) ≤ b*X₂) →
        primeSupport I ⊆ primeValues s.S) →
      (∏ i, 2*s.P i) ≤ Z^L → b*X₁*(∏ i, 2*s.P i) ≤ Z^L →
      b*X₂*(∏ i, 2*s.P i) ≤ Z^L → (∏ i, s.P i) ≤ Z^S →
      ∀ (t t₀ V : ℝ) (ν : T → Character) (R₀ : T → Finset Id),
      0 ≤ V → s.ν = slotCoefficient ν R₀ t₀ → (∀ i P, P ∈ s.H → P.val ∈ R₀ i) →
      ∀ (Q : Id) (keep : Id → O → Prop),
      (∀ F ∈ selectedProducts q, ∀ z, keep F z → z ≠ 0) →
      (∀ F ∈ selectedProducts q, ∀ z, keep F z →
        ¬FixedInducingRow η Q fixedBadMask ((primaryGenerator F)^2) z) →
      ∀ Φ : 𝓢(ℝ,ℂ), Function.support (Φ : ℝ → ℂ) ⊆ Iic 2 →
      (∑ F : selectedProducts q, (groupedWeight q F.val/MixedSelectedVolume.scale q)*
        radialEnergy (fun z => heightRectangle s ha
          (selectedCharacterAt η fixedBadMask F.val fixedBadMask_ne_zero
            (selected_products_supported q F.val F.property) (dvd_mul_right _ _) (dvd_mul_left _ _) z)
          t X₁ X₂) (keep F.val) Φ K) ≤
        radialControl Φ * (C*Kslot^(2*N)*(sourceControl control s.W₁*sourceControl control s.W₂)^2*
          (MixedFirstProfileEnvelope.height t V s.t₁ s.t₂)^J*
          ((η.modulus.absNorm : ℝ)*K)*Z^ε) := by
  dsimp only
  let δ : ℝ := ε/(2*(Bsel+1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδid : δ*(2*(Bsel+1)) = ε := by
    exact div_mul_cancel₀ ε (by positivity : (2*(Bsel+1) : ℝ) ≠ 0)
  have hloss : Bsel*δ+ε/2 ≤ ε := by nlinarith
  obtain ⟨J,control,Cr,hCr,h00,href⟩ := uniform_actual_reference (ι := ι)
    N hcard (ε/2) a b BR Bd rho Bf (half_pos hε) ha hb hBR hBd hrho hBf
  obtain ⟨Cf,hCf,hweights⟩ := uniform_grouped_window.{v} N δ hδ
  refine ⟨J,control,256*Cf*Cr,by positivity,h00,?_⟩
  filter_upwards [href] with Z hrefZ
  have hZ : 1 < Z := hrefZ.1
  have hz : 0 < Z := zero_lt_one.trans hZ
  refine ⟨hZ,?_⟩
  intro T s hMs α instα q hα hqP hqpool hqvolume hqcap hscale Kslot hKslot hqν hqW
    η K X₁ X₂ S hK hX₁ hX₂ hS hRcap hcap hcenter hshort
    hholes hScap henclose hVcap hvolume₁ hvolume₂ hVsharp
    t t₀ V ν R₀ hV hν hHR Q keep hkeep heligible Φ hΦ
  let W := MixedSelectedVolume.scale q
  have hW : 0 < W := MixedSelectedVolume.scale_pos q hqP
  have hDN (F : Id) (hF : F ∈ selectedProducts q) : (F.absNorm : ℝ) ≤ 2*W :=
    (MixedSelectedVolume.selected_products_norm q hqpool F hF).trans (by linarith)
  have hw := hweights α q hα Kslot hKslot hqν hqW Z W Bsel hZ.le hW hscale hDN
  have hmass : (∑ F : selectedProducts q, groupedWeight q F.val/W) ≤
      256*(Cf*Kslot^(2*N)*Z^(Bsel*δ)) := by
    rw [Finset.sum_coe_sort (selectedProducts q) (fun F : Id => groupedWeight q F/W),
      ←Finset.sum_div]
    exact hw.2
  let A := sourceControl control s.W₁*sourceControl control s.W₂
  let H := MixedFirstProfileEnvelope.height t V s.t₁ s.t₂
  let E := radialControl Φ*(Cr*A^2*H^J*((η.modulus.absNorm : ℝ)*K)*Z^(ε/2))
  have hH : 0 ≤ H := by dsimp [H,MixedFirstProfileEnvelope.height]; positivity
  have hΦcontrol : 0 ≤ radialControl Φ := radial_control_nonneg Φ
  have hKslot0 : 0 ≤ Kslot := zero_le_one.trans hKslot
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hpoint (F : selectedProducts q) :
      radialEnergy (fun z => heightRectangle s ha
        (selectedCharacterAt η fixedBadMask F.val fixedBadMask_ne_zero
          (selected_products_supported q F.val F.property) (dvd_mul_right _ _) (dvd_mul_left _ _) z)
        t X₁ X₂) (keep F.val) Φ K ≤ E :=
    hrefZ.2 T s hMs α q hα hqpool hqvolume hqcap η K X₁ X₂ S hK hX₁ hX₂ hS
      hRcap hcap hcenter hshort hholes hScap henclose hVcap hvolume₁ hvolume₂ hVsharp
      t t₀ V ν R₀ hV hν hHR F.val F.property Q (keep F.val)
      (hkeep F.val F.property) (heligible F.val F.property) Φ hΦ
  have hpower : Z^(Bsel*δ)*Z^(ε/2) ≤ Z^ε := by
    rw [←Real.rpow_add hz]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le hloss
  calc
    _ ≤ ∑ F : selectedProducts q, (groupedWeight q F.val/W)*E := by
      apply Finset.sum_le_sum
      intro F hF
      exact mul_le_mul_of_nonneg_left (hpoint F)
        (div_nonneg (grouped_weight_nonneg q F.val) hW.le)
    _ = (∑ F : selectedProducts q, groupedWeight q F.val/W)*E := by rw [Finset.sum_mul]
    _ ≤ (256*(Cf*Kslot^(2*N)*Z^(Bsel*δ)))*E := mul_le_mul_of_nonneg_right hmass hE
    _ = (radialControl Φ*((256*Cf*Cr)*Kslot^(2*N)*A^2*H^J*((η.modulus.absNorm : ℝ)*K)))*
        (Z^(Bsel*δ)*Z^(ε/2)) := by dsimp [E]; ring
    _ ≤ (radialControl Φ*((256*Cf*Cr)*Kslot^(2*N)*A^2*H^J*((η.modulus.absNorm : ℝ)*K)))*Z^ε :=
      mul_le_mul_of_nonneg_left hpower (by positivity)
    _ = _ := by dsimp only [A,H]; ring

end
end Candidate.SilPrior.FourthPower.MixedFirstActualReference
