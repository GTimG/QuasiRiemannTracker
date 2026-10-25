/- Copyright (c) 2026 Sil. Apache-2.0.
Actual same-slot reference geometry. The original finite enclosure and
all punctures, coefficients, characters and heights remain literal.
Only ordinary reference lengths and their maximum support caps change.

-/
import Candidate.SilPrior.FourthPower.MixedFirstChosenReferenceSource
import Candidate.SilPrior.FourthPower.MixedFirstActualReference

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.MixedFirstSourceGeometry
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonProfile CenteredMomentUncenteredTerminal
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationBox
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentOriginalRadialComparison CenteredMomentSourceProfileMass
open QRH.Record1252270103KernelMass (ideal_norm_one_le primeSupport primeValues)
open ConcreteTraceCRT ConcretePrimeRowBridge MixedLiveNormalization
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedFirstRebase MixedFirstSeededSource MixedFirstCanonicalGeometry
open MixedFirstChosenReferenceSource MixedFirstActualNonexceptional
open MixedFirstReferenceDispatch MixedFirstReferenceChoice MixedFirstChosenEnergy
open MixedFirstGeometricCaps MixedInnerExceptionalBlock MixedFixedSupport
open ReferencePrimeEnclosure MixedCanonicalSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α ⊕ Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- Four exact support caps, in the SAME original finite enclosure.
The lower floor c is allowed to be below one. -/
theorem enclosure_caps (s : Source ι a b) (hb : 0 ≤ b)
    (Z Lorig Lcap Cap q : ℝ) (hZ : 1 ≤ Z) (hL : 0 ≤ Lorig)
    (hLc : 2*Lorig ≤ Lcap) (hCap : b/comparisonScale b ≤ Cap)
    (hX₁ : s.X₁ ≤ Z^Lorig) (hX₂ : s.X₂ ≤ Z^Lorig)
    (hq : comparisonScale b ≤ q) (hq₁ : q ≤ s.X₁) :
    b*s.X₁ ≤ Cap*Z^Lcap ∧ b*s.X₂ ≤ Cap*Z^Lcap ∧
      b*q ≤ Cap*Z^Lcap ∧ b*(s.T/q) ≤ Cap*Z^Lcap := by
  have hz := zero_lt_one.trans_le hZ
  have hc := comparisonScale_pos b
  have hc1 : comparisonScale b ≤ 1 := (comparison_scale_le_half b).trans (by norm_num)
  have hbCap : b ≤ Cap :=
    ((le_div_iff₀ hc).mpr (mul_le_of_le_one_right hb hc1)).trans hCap
  have hCap0 : 0 ≤ Cap := hb.trans hbCap
  have hpow : Z^Lorig ≤ Z^Lcap := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hx₁ : b*s.X₁ ≤ Cap*Z^Lcap := mul_le_mul hbCap (hX₁.trans hpow)
    (s.hL.trans_le s.hX₁).le hCap0
  have hx₂ : b*s.X₂ ≤ Cap*Z^Lcap := mul_le_mul hbCap (hX₂.trans hpow)
    (s.hL.trans_le s.hX₂).le hCap0
  have hT : s.T ≤ Z^(2*Lorig) := by
    rw [←s.hpX]
    calc
      _ ≤ Z^Lorig*Z^Lorig := mul_le_mul hX₁ hX₂
        (s.hL.trans_le s.hX₂).le (Real.rpow_nonneg hz.le _)
      _ = Z^(2*Lorig) := by rw [←Real.rpow_add hz]; congr 1; ring
  refine ⟨hx₁,hx₂,(mul_le_mul_of_nonneg_left hq₁ hb).trans hx₁,?_⟩
  calc
    b*(s.T/q) ≤ b*(Z^(2*Lorig)/comparisonScale b) :=
      mul_le_mul_of_nonneg_left
        ((div_le_div_of_nonneg_left s.total_pos.le hc hq).trans
          (div_le_div_of_nonneg_right hT hc.le)) hb
    _ = (b/comparisonScale b)*Z^(2*Lorig) := by ring
    _ ≤ Cap*Z^Lcap := mul_le_mul hCap (Real.rpow_le_rpow_of_exponent_le hZ hLc)
      (Real.rpow_nonneg hz.le _) hCap0

/-- A reference with unchanged S and H. All support assertions are
derived from the numerical enclosure; none is assumed for a new Source. -/
def reference (s : Source ι a b) (hb : 0 ≤ b) (C q : ℝ)
    (hS : s.S = enclosure C) (hq : 0 < q) (hq₁ : q ≤ s.X₁) (hq₂ : q ≤ s.X₂)
    (hx₁ : b*s.X₁ ≤ C) (hx₂ : b*s.X₂ ≤ C)
    (hy₁ : b*q ≤ C) (hy₂ : b*(s.T/q) ≤ C) : Source ι a b :=
  { s with
    Y₁ := q
    Y₂ := s.T/q
    L := q
    U₁ := max s.X₁ q
    U₂ := max s.X₂ (s.T/q)
    hL := hq
    hX₁ := hq₁
    hX₂ := hq₂
    hY₁ := le_refl _
    hY₂ := (le_div_iff₀ hq).mpr (by
      rw [←s.hpX]
      exact mul_le_mul hq₁ hq₂ hq.le (hq.le.trans hq₁))
    hXU₁ := le_max_left _ _
    hXU₂ := le_max_left _ _
    hYU₁ := le_max_right _ _
    hYU₂ := le_max_right _ _
    hpY := by field_simp [hq.ne']
    henclose := by
      intro I hI hlen
      have hm₁ : 0 ≤ max s.X₁ q := (s.hL.trans_le s.hX₁).le.trans (le_max_left _ _)
      have hm₂ : 0 ≤ max s.X₂ (s.T/q) := (s.hL.trans_le s.hX₂).le.trans (le_max_left _ _)
      have hcap₁ : b*max s.X₁ q ≤ C := by
        rw [mul_max_of_nonneg _ _ hb]; exact max_le hx₁ hy₁
      have hcap₂ : b*max s.X₂ (s.T/q) ≤ C := by
        rw [mul_max_of_nonneg _ _ hb]; exact max_le hx₂ hy₂
      have hcap : (I.absNorm : ℝ) ≤ C := by
        rcases hlen with hlen | hlen
        · exact hlen.trans ((mul_le_mul_of_nonneg_left
            (div_le_self hm₁ (ideal_norm_one_le (mul_ne_zero s.hd.1 (s.hB (Sum.inr 0))))) hb).trans hcap₁)
        · exact hlen.trans ((mul_le_mul_of_nonneg_left
            (div_le_self hm₂ (ideal_norm_one_le (mul_ne_zero s.hd.2 (s.hB (Sum.inr 1))))) hb).trans hcap₂)
      rw [hS]
      exact support_enclosed C I hI hcap }

theorem reference_original_enclosure (s : Source ι a b) (hb : 0 ≤ b) (C q : ℝ)
    (hS : s.S = enclosure C) (hq : 0 < q) (hq₁ : q ≤ s.X₁) (hq₂ : q ≤ s.X₂)
    (hx₁ : b*s.X₁ ≤ C) (hx₂ : b*s.X₂ ≤ C)
    (hy₁ : b*q ≤ C) (hy₂ : b*(s.T/q) ≤ C) :
    OriginalEnclosure (reference s hb C q hS hq hq₁ hq₂ hx₁ hx₂ hy₁ hy₂) := by
  intro I hI hlen
  have hm₁ : 0 ≤ max s.X₁ q := (s.hL.trans_le s.hX₁).le.trans (le_max_left _ _)
  have hm₂ : 0 ≤ max s.X₂ (s.T/q) := (s.hL.trans_le s.hX₂).le.trans (le_max_left _ _)
  have hcap₁ : b*max s.X₁ q ≤ C := by
    rw [mul_max_of_nonneg _ _ hb]; exact max_le hx₁ hy₁
  have hcap₂ : b*max s.X₂ (s.T/q) ≤ C := by
    rw [mul_max_of_nonneg _ _ hb]; exact max_le hx₂ hy₂
  have hcap : (I.absNorm : ℝ) ≤ C := by
    rcases hlen with hlen | hlen
    · exact hlen.trans ((mul_le_mul_of_nonneg_left
        (div_le_self hm₁ (ideal_norm_one_le s.hd.1)) hb).trans hcap₁)
    · exact hlen.trans ((mul_le_mul_of_nonneg_left
        (div_le_self hm₂ (ideal_norm_one_le s.hd.2)) hb).trans hcap₂)
  change primeSupport I ⊆ primeValues s.S
  rw [hS]
  exact support_enclosed C I hI hcap

/-- The choice is made from this source's actual total T and marked S.
The two q<=X premises are precisely the complement of the short branch. -/
def chosenReference (s : Source ι a b) (hb : 0 ≤ b)
    (Z R S d Lorig Lcap Cap : ℝ) (hZ : 1 ≤ Z) (hL : 0 ≤ Lorig)
    (hLc : 2*Lorig ≤ Lcap) (hCap : b/comparisonScale b ≤ Cap)
    (hS : s.S = enclosure (Cap*Z^Lcap))
    (hX₁ : s.X₁ ≤ Z^Lorig) (hX₂ : s.X₂ ≤ Z^Lorig)
    (hmix : Real.logb Z s.T+2*S+4*d < R)
    (hq₁ : qReference b Z R (Real.logb Z s.T) S d ≤ s.X₁)
    (hq₂ : qReference b Z R (Real.logb Z s.T) S d ≤ s.X₂) : Source ι a b := by
  let q := qReference b Z R (Real.logb Z s.T) S d
  have hgeo := reference_length_geometry b Z R (Real.logb Z s.T) S d hZ hmix
  have hc := enclosure_caps s hb Z Lorig Lcap Cap q hZ hL hLc hCap hX₁ hX₂ hgeo.1 hq₁
  exact reference s hb (Cap*Z^Lcap) q hS hgeo.2.1 hq₁ hq₂ hc.1 hc.2.1 hc.2.2.1 hc.2.2.2

section Chosen
variable (s : Source ι a b) (hb : 0 ≤ b)
  (Z R S d Lorig Lcap Cap : ℝ) (hZ : 1 ≤ Z) (hL : 0 ≤ Lorig)
  (hLc : 2*Lorig ≤ Lcap) (hCap : b/comparisonScale b ≤ Cap)
  (hS : s.S = enclosure (Cap*Z^Lcap))
  (hX₁ : s.X₁ ≤ Z^Lorig) (hX₂ : s.X₂ ≤ Z^Lorig)
  (hmix : Real.logb Z s.T+2*S+4*d < R)
  (hq₁ : qReference b Z R (Real.logb Z s.T) S d ≤ s.X₁)
  (hq₂ : qReference b Z R (Real.logb Z s.T) S d ≤ s.X₂)
local notation "r" => chosenReference s hb Z R S d Lorig Lcap Cap hZ hL hLc hCap hS hX₁ hX₂ hmix hq₁ hq₂

/-- No allocated factor, finite hole set, profile or height changes. -/
theorem chosen_data :
    (r).S=s.S ∧ (r).H=s.H ∧ (r).R=s.R ∧ (r).Fhole=s.Fhole ∧ (r).d=s.d ∧ (r).B=s.B ∧ (r).G=s.G ∧
    (r).X₁=s.X₁ ∧ (r).X₂=s.X₂ ∧ (r).T=s.T ∧ (r).P=s.P ∧ (r).M=s.M ∧
    sourceVolume r=sourceVolume s ∧
    (r).Y₁=qReference b Z R (Real.logb Z s.T) S d ∧ (r).Y₂=s.T/(r).Y₁ ∧ (r).L=(r).Y₁ ∧
    OriginalEnclosure r ∧
    comparisonScale b*Z^(referenceExponent R (Real.logb Z (r).T) S d) ≤ (r).L ∧
    comparisonScale b ≤ (r).L := by
  have hg := reference_length_geometry b Z R (Real.logb Z s.T) S d hZ hmix
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,hg.2.2.1,hg.1⟩
  unfold chosenReference
  exact reference_original_enclosure _ _ _ _ _ _ _ _ _ _ _ _

theorem chosen_rectangle_eq (ha : 0 < a) (χ : Character) (t X₁ X₂ : ℝ) :
    heightRectangle r ha χ t X₁ X₂ = heightRectangle s ha χ t X₁ X₂ := rfl

/-- Exact selected polynomial decomposition. The original short
comparison rectangle is zero; the newly chosen reference is not dropped. -/
theorem chosen_selected_split (ha : 0 < a) (hd : s.d=(1,1)) (hG : s.G=1)
    (hY : s.Y₁ ≤ comparisonScale b ∨ s.Y₂ ≤ comparisonScale b)
    (η : Character) (m : O) (F : Id) (z : O)
    (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (χ : SelectedCharacter η m F z) (t : ℝ) :
    normalization (s.X₁*s.X₂) s.P*MixedFirstSeededEnergy.selectedPolynomial s ha 1 F η m 1 t z =
      normalization (s.X₁*s.X₂) s.P*MixedFirstSeededEnergy.selectedPolynomial r ha 1 F η m 1 t z +
        heightRectangle s ha χ.character t (r).Y₁ (r).Y₂ := by
  rw [selected_uncentered s ha hd hG hY η m F z hmLam hm2 χ t]
  have he := selected_centering r ha hd hG η m F z hmLam hm2 χ t
  exact he

theorem chosen_uncentered_zero (ha : 0 < a) (χ : Character) (t : ℝ)
    (hbranch : Real.logb Z s.T+S ≤ 5*R/6-7*d/3) :
    heightRectangle s ha χ t (r).Y₁ (r).Y₂ = 0 := by
  apply height_rectangle_small s ha χ t (r).Y₁ (r).Y₂
    ((r).hL.trans_le (r).hY₁) ((r).hL.trans_le (r).hY₂)
  left
  change qReference b Z R (Real.logb Z s.T) S d ≤ comparisonScale b
  simp only [qReference,hbranch,ite_true,le_refl]

theorem chosen_sharp_or_zero (ha : 0 < a) (hd : s.d=(1,1)) (hb1 : 1 ≤ b) :
    (5*R/6-7*d/3 < Real.logb Z s.T+S → 1 ≤ sharpSupport r) ∧
    (sharpSupport r < 1 → ∀ seed I : Id, sourceCoefficient r ha seed I=0) := by
  constructor
  · intro hc
    apply unit_source_sharp_support r hb1 hd
    change 1 ≤ qReference b Z R (Real.logb Z s.T) S d
    rw [qReference,if_neg (not_le.mpr hc)]
    exact Real.one_le_rpow hZ
      (reference_length_geometry b Z R (Real.logb Z s.T) S d hZ hmix).2.2.2.1
  · exact below_unit_source_zero r ha
end Chosen

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M ≤ Hray)

theorem chosen_canonical (W : ℝ→ℂ) (Cap Lcap Z Lorig : ℝ) (η₀ : Character)
    (θ : ι→RayQuotient.Characters M Hray) (w σ freq : ι→ℝ) (t : ℝ)
    (R₀ : ι→Finset Id) (s : Source ι a b)
    (hs : Canonical M Hray hHray W Cap Lcap Z η₀ θ w σ freq t R₀ s)
    (hb : 0 ≤ b) (R S d : ℝ) (hZ : 1 ≤ Z) (hL : 0 ≤ Lorig)
    (hLc : 2*Lorig ≤ Lcap) (hCap : b/comparisonScale b ≤ Cap)
    (hX₁ : s.X₁ ≤ Z^Lorig) (hX₂ : s.X₂ ≤ Z^Lorig)
    (hmix : Real.logb Z s.T+2*S+4*d < R)
    (hq₁ : qReference b Z R (Real.logb Z s.T) S d ≤ s.X₁)
    (hq₂ : qReference b Z R (Real.logb Z s.T) S d ≤ s.X₂) :
    Canonical M Hray hHray W Cap Lcap Z η₀ θ w σ freq t R₀
      (chosenReference s hb Z R S d Lorig Lcap Cap hZ hL hLc hCap hs.1 hX₁ hX₂ hmix hq₁ hq₂) := hs

/-- The marked width is exactly the actual finite product, uniformly in
the index type or live subset. A global card bound pays no loss per slot. -/
theorem canonical_product (W : ℝ→ℂ) (Cap Lcap Z : ℝ) (η₀ : Character)
    (θ : ι→RayQuotient.Characters M Hray) (w σ freq : ι→ℝ) (t : ℝ)
    (R₀ : ι→Finset Id) (s : Source ι a b)
    (hs : Canonical M Hray hHray W Cap Lcap Z η₀ θ w σ freq t R₀ s)
    (N : ℕ) (Lslot B : ℝ) (hZ : 1 < Z) (hcard : Fintype.card ι ≤ N)
    (hLslot : 0 ≤ Lslot) (hw : ∀ i, 0 ≤ w i) (hwL : ∀ i, w i ≤ Lslot)
    (hB : (N:ℝ)*Lslot ≤ B) :
    (∏ i,s.P i)=Z^(∑ i,w i) ∧ 0 ≤ ∑ i,w i ∧ (∏ i,s.P i) ≤ Z^B := by
  have hp : (∏ i,s.P i)=Z^(∑ i,w i) := by
    rw [hs.2.2.2.2,←Real.rpow_sum_of_pos (zero_lt_one.trans hZ)]
  have hsum : (∑ i,w i) ≤ (N:ℝ)*Lslot := by
    calc
      _ ≤ ∑ _i : ι,Lslot := Finset.sum_le_sum (fun i _=>hwL i)
      _ = (Fintype.card ι:ℝ)*Lslot := by simp
      _ ≤ (N:ℝ)*Lslot := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hLslot
  refine ⟨hp,Finset.sum_nonneg (fun i _=>hw i),?_⟩
  rw [hp]
  exact Real.rpow_le_rpow_of_exponent_le hZ.le (hsum.trans hB)

/-- A fixed admissibility width, not the actual physical R. It is chosen
before Z and before source, selected product, profiles and characters. -/
def referenceWidth (Binput B Lcap BR0 BH : ℝ) : ℝ := Binput+B+Lcap+BR0+BH+4

theorem reference_width_bounds (Binput B Lcap BR0 BH : ℝ)
    (hinput : 0 ≤ Binput) (hB : 0 ≤ B) (hLcap : 0 ≤ Lcap)
    (hBR0 : 0 ≤ BR0) (hBH : 0 ≤ BH) :
    0 ≤ referenceWidth Binput B Lcap BR0 BH ∧
    Binput ≤ referenceWidth Binput B Lcap BR0 BH ∧
    B ≤ referenceWidth Binput B Lcap BR0 BH ∧
    Lcap+1 ≤ referenceWidth Binput B Lcap BR0 BH ∧
    BR0+BH ≤ referenceWidth Binput B Lcap BR0 BH := by
  dsimp only [referenceWidth]
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

/-- Literal ActualReference admission for either displayed pair.
The four support-cap facts used below are supplied by enclosure_caps;
the marked product is supplied by canonical_product. No norm of a
radical is substituted for the full puncture norm. -/
theorem eventually_reference_admission (N : ℕ) (b Cap B Binput Lcap BR0 BH Bd rho : ℝ)
    (hb : 0 ≤ b) (hCap : 0 ≤ Cap) (hB : 0 ≤ B) (hinput : 0 ≤ Binput)
    (hLcap : 0 ≤ Lcap) (hBR0 : 0 ≤ BR0) (hBH : 0 ≤ BH)
    (hBd : 0 ≤ Bd) (hrho : 0 ≤ rho) :
    let BR := referenceWidth Binput B Lcap BR0 BH
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (ι : Type u) [Fintype ι], Fintype.card ι ≤ N → ∀ a : ℝ, ∀ s : Source ι a b,
      s.S=enclosure (Cap*Z^Lcap) → (s.R.absNorm:ℝ) ≤ Z^BR0 →
      (s.Fhole.absNorm:ℝ) ≤ Z^BH → (∏ i,s.P i) ≤ Z^B →
      ∀ X₁ X₂ : ℝ, X₁ ≤ Z^B → X₂ ≤ Z^B →
      b*X₁ ≤ Cap*Z^Lcap → b*X₂ ≤ Cap*Z^Lcap →
      ((s.Fhole*s.R).absNorm:ℝ) ≤ Z^(BR+Bd+rho+1) ∧
      (∀ P∈s.S,(P.val.absNorm:ℝ) ≤ Z^(BR+Bd+rho+1)) ∧
      (∀ I,Supported I → ((I.absNorm:ℝ) ≤ b*X₁ ∨ (I.absNorm:ℝ) ≤ b*X₂) →
        primeSupport I ⊆ primeValues s.S) ∧
      (∏ i,2*s.P i) ≤ Z^(2*(BR+1)) ∧
      b*X₁*(∏ i,2*s.P i) ≤ Z^(2*(BR+1)) ∧
      b*X₂*(∏ i,2*s.P i) ≤ Z^(2*(BR+1)) := by
  dsimp only
  let BR := referenceWidth Binput B Lcap BR0 BH
  have hh := reference_width_bounds Binput B Lcap BR0 BH hinput hB hLcap hBR0 hBH
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_ge_atTop Cap,
    eventually_ge_atTop b,eventually_ge_atTop ((2:ℝ)^N)] with Z hZ hZCap hZb hZN
  have hz := zero_lt_one.trans hZ
  have hbound : B ≤ BR := hh.2.2.1
  have hprime : Cap*Z^Lcap ≤ Z^(BR+Bd+rho+1) := by
    calc
      _ ≤ Z*Z^Lcap := mul_le_mul_of_nonneg_right hZCap (Real.rpow_nonneg hz.le _)
      _ = Z^(Lcap+1) := by rw [Real.rpow_add hz,Real.rpow_one]; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [hh.2.2.2.1])
  refine ⟨hZ,?_⟩
  intro κ instκ hκ a s hS hR hF hP X₁ X₂ hX₁ hX₂ hcap₁ hcap₂
  have h2 : (∏ i : κ,2*s.P i) ≤ Z^(B+1) := by
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
    calc
      (2:ℝ)^Fintype.card κ*(∏ i,s.P i) ≤ (2:ℝ)^N*Z^B :=
        mul_le_mul (pow_le_pow_right₀ (by norm_num) hκ) hP
          (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.hP i))) (by positivity)
      _ ≤ Z*Z^B := mul_le_mul_of_nonneg_right hZN (Real.rpow_nonneg hz.le _)
      _ = Z^(B+1) := by rw [Real.rpow_add hz,Real.rpow_one]; ring
  have hvolume (X : ℝ) (hX : X ≤ Z^B) :
      b*X*(∏ i : κ,2*s.P i) ≤ Z^(2*(BR+1)) := by
    have hP0 : 0 ≤ ∏ i : κ,2*s.P i :=
      Finset.prod_nonneg (fun i _=>mul_nonneg (by norm_num) (zero_le_one.trans (s.hP i)))
    calc
      _ ≤ b*Z^B*(∏ i : κ,2*s.P i) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX hb) hP0
      _ ≤ Z*Z^B*Z^(B+1) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hZb (Real.rpow_nonneg hz.le _)) h2 hP0
          (mul_nonneg hz.le (Real.rpow_nonneg hz.le _))
      _ = Z^(2*(B+1)) := by
        rw [show 2*(B+1)=(B+1)+(B+1) by ring,
          Real.rpow_add hz (B+1) (B+1),Real.rpow_add hz B 1,Real.rpow_one]
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  refine ⟨?_,?_,?_,h2.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)),
    hvolume X₁ hX₁,hvolume X₂ hX₂⟩
  · rw [map_mul,Nat.cast_mul]
    calc
      _ ≤ Z^BH*Z^BR0 := mul_le_mul hF hR (Nat.cast_nonneg _) (Real.rpow_nonneg hz.le _)
      _ = Z^(BH+BR0) := (Real.rpow_add hz _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [hh.2.2.2.2])
  · intro P hP
    rw [hS] at hP
    exact (enclosure_bound _ P hP).2.trans hprime
  · intro I hI hIlen
    rw [hS]
    exact support_enclosed _ I hI (hIlen.elim (fun h=>h.trans hcap₁) (fun h=>h.trans hcap₂))

/-- All actual chosen lengths, including the possibly larger T/q, fit
the same preselected coarse B. This also supplies the subunit minimum
needed by ChosenEnergy. Choosing B<=Lcap is done once at setup. -/
theorem eventually_chosen_power_caps (b Lorig B : ℝ) (hL : 0 ≤ Lorig)
    (hB : 2*Lorig+1 ≤ B) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ (ι : Type u) [Fintype ι], ∀ a : ℝ, ∀ s : Source ι a b,
      s.X₁ ≤ Z^Lorig → s.X₂ ≤ Z^Lorig →
      ∀ q : ℝ, comparisonScale b ≤ q → q ≤ s.X₁ →
      Z^(-B) ≤ q ∧ s.X₁ ≤ Z^B ∧ s.X₂ ≤ Z^B ∧ q ≤ Z^B ∧ s.T/q ≤ Z^B := by
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_ge_atTop ((comparisonScale b)⁻¹)]
    with Z hZ hfixed
  have hz := zero_lt_one.trans hZ
  have hc := comparisonScale_pos b
  refine ⟨hZ,?_⟩
  intro κ instκ a s hX₁ hX₂ q hq hq₁
  have hpower : Z^Lorig ≤ Z^B := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hT : s.T ≤ Z^(2*Lorig) := by
    rw [←s.hpX]
    calc
      _ ≤ Z^Lorig*Z^Lorig := mul_le_mul hX₁ hX₂ (s.hL.trans_le s.hX₂).le (Real.rpow_nonneg hz.le _)
      _ = Z^(2*Lorig) := by rw [←Real.rpow_add hz]; congr 1; ring
  refine ⟨?_,hX₁.trans hpower,hX₂.trans hpower,hq₁.trans (hX₁.trans hpower),?_⟩
  · calc
      Z^(-B) ≤ Z^(-1:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
      _ = Z⁻¹ := Real.rpow_neg_one Z
      _ ≤ comparisonScale b := by
        have hh := mul_le_mul_of_nonneg_right hfixed hc.le
        rw [inv_mul_cancel₀ hc.ne'] at hh
        rw [←one_div]
        apply (div_le_iff₀ hz).mpr
        nlinarith
      _ ≤ q := hq
  · calc
      _ ≤ Z^(2*Lorig)/comparisonScale b :=
        (div_le_div_of_nonneg_left s.total_pos.le hc hq).trans (div_le_div_of_nonneg_right hT hc.le)
      _ ≤ Z^(2*Lorig)*Z := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hfixed (Real.rpow_nonneg hz.le _)
      _ = Z^(2*Lorig+1) := by rw [Real.rpow_add hz,Real.rpow_one]
      _ ≤ Z^B := Real.rpow_le_rpow_of_exponent_le hZ.le hB

end
end Candidate.SilPrior.FourthPower.MixedFirstSourceGeometry
