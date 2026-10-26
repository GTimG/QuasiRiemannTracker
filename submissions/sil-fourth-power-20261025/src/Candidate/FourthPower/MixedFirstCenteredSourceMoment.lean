/- Copyright (c) 2026 Sil. Apache-2.0.
Exact two-rectangle reduction and the whole actual centered source
moment. Both uncentered sources have the original total and normalization.

-/
import Candidate.FourthPower.MixedFirstSourceMoment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedFirstCenteredSourceMoment
universe u v
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ConcretePrimeRowBridge ConcreteTraceCRT ActualEisensteinCubic RayFourExpansion
open CompletedGauss (primaryGenerator)
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentOriginalRadialComparison CenteredMomentEnergyCapacityRemoval
open CenteredMomentFiniteProfileExceptional
open CenteredMomentUncenteredTerminal CenteredExceptionalProfile
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedInnerExceptionalBlock MixedFirstPhysicalApplication MixedLiveNormalization
open MixedFirstSeededEnergy MixedFirstReferenceDispatch MixedFirstProfileEnvelope
open MixedSupplierFourthRow MixedSupplierPositive MixedFirstGeometricCaps
open MixedFirstUniformLossBudget MixedFirstChosenEnergy MixedFirstSourceMoment
open MixedFirstSourceGeometry MixedCanonicalSource ReferencePrimeEnclosure
open MixedFirstActualNonexceptional MixedFirstReferenceChoice
open MixedCommonHeights
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- Exchange only the original and reference rectangle. The character,
whole puncture, profiles, slot pools and total ordinary volume stay fixed. -/
def swapRectangles (s : Source ι a b) : Source ι a b :=
  {s with X₁:=s.Y₁
          X₂:=s.Y₂
          Y₁:=s.X₁
          Y₂:=s.X₂
          hX₁:=s.hY₁
          hX₂:=s.hY₂
          hY₁:=s.hX₁
          hY₂:=s.hX₂
          hXU₁:=s.hYU₁
          hXU₂:=s.hYU₂
          hYU₁:=s.hXU₁
          hYU₂:=s.hXU₂
          hpX:=s.hpY
          hpY:=s.hpX}

theorem swap_volume (s : Source ι a b) : sourceVolume (swapRectangles s)=sourceVolume s := by
  change (s.Y₁*s.Y₂)*(∏i,s.P i)=(s.X₁*s.X₂)*(∏i,s.P i)
  rw [s.hpY,s.hpX]

/-- Choosing min(c,X1,X2), rather than min(c,s.L), prevents an arbitrary
stored lower scale from creating a huge auxiliary ordinary length. -/
def tinyLength (s : Source ι a b) : ℝ := min (comparisonScale b) (min s.X₁ s.X₂)

theorem tiny_length (s : Source ι a b) :
    0<tinyLength s ∧ tinyLength s≤comparisonScale b ∧ tinyLength s≤s.X₁ ∧ tinyLength s≤s.X₂ := by
  refine ⟨lt_min (comparisonScale_pos b)
    (lt_min (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂)),min_le_left _ _,?_,?_⟩
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

theorem tiny_cases (s : Source ι a b) :
    tinyLength s=comparisonScale b ∨ tinyLength s=s.X₁ ∨ tinyLength s=s.X₂ := by
  unfold tinyLength
  by_cases hc : comparisonScale b≤min s.X₁ s.X₂
  · exact Or.inl (min_eq_left hc)
  · rw [min_eq_right (le_of_not_ge hc)]
    by_cases hX : s.X₁≤s.X₂
    · exact Or.inr (Or.inl (min_eq_left hX))
    · exact Or.inr (Or.inr (min_eq_right (le_of_not_ge hX)))

theorem tiny_second_cap (s : Source ι a b) (C : ℝ)
    (hX₁ : b*s.X₁≤C) (hX₂ : b*s.X₂≤C) (hT : b*(s.T/comparisonScale b)≤C) :
    b*(s.T/tinyLength s)≤C := by
  rcases tiny_cases s with hc|h₁|h₂
  · simpa only [hc] using hT
  · rw [h₁,←s.hpX,mul_div_cancel_left₀ _ (s.hL.trans_le s.hX₁).ne']
    exact hX₂
  · rw [h₂,←s.hpX,mul_div_cancel_right₀ _ (s.hL.trans_le s.hX₂).ne']
    exact hX₁

/-- Actual finite source with a tiny comparison rectangle. All its
enclosure fields are discharged from literal numerical support caps. -/
def tinySource (s : Source ι a b) (hb : 0≤b) (C : ℝ)
    (hS : s.S=enclosure C) (hX₁ : b*s.X₁≤C) (hX₂ : b*s.X₂≤C)
    (hT : b*(s.T/comparisonScale b)≤C) : Source ι a b :=
  reference s hb C (tinyLength s) hS (tiny_length s).1
    (tiny_length s).2.2.1 (tiny_length s).2.2.2 hX₁ hX₂
    ((mul_le_mul_of_nonneg_left (tiny_length s).2.2.1 hb).trans hX₁)
    (tiny_second_cap s C hX₁ hX₂ hT)

theorem tiny_small (s : Source ι a b) (hb : 0≤b) (C : ℝ)
    (hS : s.S=enclosure C) (hX₁ : b*s.X₁≤C) (hX₂ : b*s.X₂≤C)
    (hT : b*(s.T/comparisonScale b)≤C) :
    (tinySource s hb C hS hX₁ hX₂ hT).Y₁≤comparisonScale b := (tiny_length s).2.1

theorem tiny_volume (s : Source ι a b) (hb : 0≤b) (C : ℝ)
    (hS : s.S=enclosure C) (hX₁ : b*s.X₁≤C) (hX₂ : b*s.X₂≤C)
    (hT : b*(s.T/comparisonScale b)≤C) :
    sourceVolume (tinySource s hb C hS hX₁ hX₂ hT)=sourceVolume s := rfl

/-- Both displayed rectangles and their tiny comparison fit the same
original enclosure. No additional fixed hole or conductor is inserted. -/
theorem rectangle_caps (s : Source ι a b) (hb : 0≤b)
    (Z Lorig Lcap Cap : ℝ) (hZ : 1≤Z) (hL : 0≤Lorig)
    (hLc : 2*Lorig≤Lcap) (hCap : b/comparisonScale b≤Cap)
    (hX₁ : s.X₁≤Z^Lorig) (hX₂ : s.X₂≤Z^Lorig)
    (hY₁ : s.Y₁≤Z^Lorig) (hY₂ : s.Y₂≤Z^Lorig) :
    b*s.X₁≤Cap*Z^Lcap ∧ b*s.X₂≤Cap*Z^Lcap ∧
    b*s.Y₁≤Cap*Z^Lcap ∧ b*s.Y₂≤Cap*Z^Lcap ∧
    b*(s.T/comparisonScale b)≤Cap*Z^Lcap := by
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hc := comparisonScale_pos b
  have hc1 : comparisonScale b≤1 := (comparison_scale_le_half b).trans (by norm_num)
  have hbCap : b≤Cap := ((le_div_iff₀ hc).mpr (mul_le_of_le_one_right hb hc1)).trans hCap
  have hCap0 : 0≤Cap := hb.trans hbCap
  have hpower : Z^Lorig≤Z^Lcap := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hlen (X : ℝ) (hX : 0≤X) (hXL : X≤Z^Lorig) : b*X≤Cap*Z^Lcap :=
    mul_le_mul hbCap (hXL.trans hpower) hX hCap0
  have hT : s.T≤Z^(2*Lorig) := by
    rw [←s.hpX]
    calc
      _≤Z^Lorig*Z^Lorig := mul_le_mul hX₁ hX₂ (s.hL.trans_le s.hX₂).le (Real.rpow_nonneg hz.le _)
      _=Z^(2*Lorig) := by rw [←Real.rpow_add hz];congr 1;ring
  refine ⟨hlen _ (s.hL.trans_le s.hX₁).le hX₁,hlen _ (s.hL.trans_le s.hX₂).le hX₂,
    hlen _ (s.hL.trans_le s.hY₁).le hY₁,hlen _ (s.hL.trans_le s.hY₂).le hY₂,?_⟩
  calc
    _=(b/comparisonScale b)*s.T := by ring
    _≤Cap*Z^(2*Lorig) := mul_le_mul hCap hT s.total_pos.le hCap0
    _≤Cap*Z^Lcap := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ hLc) hCap0

section Exact
variable (s : Source ι a b) (hb : 0≤b) (C : ℝ) (hS : s.S=enclosure C)
  (hX₁ : b*s.X₁≤C) (hX₂ : b*s.X₂≤C) (hY₁ : b*s.Y₁≤C) (hY₂ : b*s.Y₂≤C)
  (hT : b*(s.T/comparisonScale b)≤C)
local notation "sx" => tinySource s hb C hS hX₁ hX₂ hT
local notation "sy" => tinySource (swapRectangles s) hb C hS hY₁ hY₂ hT

theorem tiny_x_rectangle (ha : 0<a) (χ : Character) (tp : ℝ) :
    heightRectangle sx ha χ tp (sx).X₁ (sx).X₂=heightRectangle s ha χ tp s.X₁ s.X₂ := rfl

theorem tiny_y_rectangle (ha : 0<a) (χ : Character) (tp : ℝ) :
    heightRectangle sy ha χ tp (sy).X₁ (sy).X₂=heightRectangle s ha χ tp s.Y₁ s.Y₂ := by
  unfold heightRectangle
  change residualPhase (s.Y₁*s.Y₂) s.d 1 tp*_=
    residualPhase (s.X₁*s.X₂) s.d 1 tp*_
  rw [s.hpY,s.hpX]
  rfl

/-- Literal selected row identity, including both old/new normalizations,
the original moving selected square, fixed mask and all physical heights. -/
theorem selected_difference (ha : 0<a) (hd : s.d=(1,1)) (hG : s.G=1)
    (η : Character) (m : O) (F : Id) (z : O)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) (χ : SelectedCharacter η m F z) (tp : ℝ) :
    selectedPolynomial s ha 1 F η m 1 tp z=
      selectedPolynomial sx ha 1 F η m 1 tp z-selectedPolynomial sy ha 1 F η m 1 tp z := by
  have hc := selected_centering s ha hd hG η m F z hmLam hm2 χ tp
  have hx := selected_uncentered sx ha hd hG
    (Or.inl (tiny_small s hb C hS hX₁ hX₂ hT)) η m F z hmLam hm2 χ tp
  have hy := selected_uncentered sy ha hd hG
    (Or.inl (tiny_small (swapRectangles s) hb C hS hY₁ hY₂ hT)) η m F z hmLam hm2 χ tp
  rw [tiny_x_rectangle s hb C hS hX₁ hX₂ hT ha χ.character tp] at hx
  rw [tiny_y_rectangle s hb C hS hY₁ hY₂ hT ha χ.character tp] at hy
  have hnormal : normalization ((sy).X₁*(sy).X₂) (sy).P=normalization (s.X₁*s.X₂) s.P := by
    change normalization (s.Y₁*s.Y₂) s.P=normalization (s.X₁*s.X₂) s.P
    rw [s.hpY,s.hpX]
  rw [hnormal] at hy
  have hn : normalization (s.X₁*s.X₂) s.P≠0 := by
    unfold normalization
    apply mul_ne_zero
    · exact inv_ne_zero (Complex.ofReal_ne_zero.mpr
        (Real.sqrt_pos.2 (mul_pos (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂))).ne')
    · apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      exact inv_ne_zero (Complex.ofReal_ne_zero.mpr
        (Real.sqrt_pos.2 (zero_lt_one.trans_le (s.hP i))).ne')
  apply mul_left_cancel₀ hn
  have hx' : normalization (s.X₁*s.X₂) s.P * selectedPolynomial sx ha 1 F η m 1 tp z =
      heightRectangle s ha χ.character tp s.X₁ s.X₂ := hx
  calc
    _ = heightRectangle s ha χ.character tp s.X₁ s.X₂ -
        heightRectangle s ha χ.character tp s.Y₁ s.Y₂ := eq_sub_of_add_eq hc.symm
    _ = normalization (s.X₁*s.X₂) s.P * selectedPolynomial sx ha 1 F η m 1 tp z -
        normalization (s.X₁*s.X₂) s.P * selectedPolynomial sy ha 1 F η m 1 tp z :=
      congrArg₂ (fun x y : ℂ => x-y) hx'.symm hy.symm
    _ = _ := (mul_sub _ _ _).symm

theorem selected_energy_split (ha : 0<a) (hd : s.d=(1,1)) (hG : s.G=1)
    (η : Character) (F : Id) (hF : Supported F) (tp : ℝ)
    (keep : O→Prop) (hkeep : ∀z,keep z→z≠0)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hΦs : Function.support (Φ : ℝ→ℂ)⊆Iic 2) (hΦ : ∀x,0≤(Φ x).re) :
    selectedEnergy s ha 1 F η fixedBadMask 1 tp keep Φ K≤
      2*(selectedEnergy sx ha 1 F η fixedBadMask 1 tp keep Φ K+
        selectedEnergy sy ha 1 F η fixedBadMask 1 tp keep Φ K) := by
  let f := selectedPolynomial s ha 1 F η fixedBadMask 1 tp
  let g := selectedPolynomial sx ha 1 F η fixedBadMask 1 tp
  let h := selectedPolynomial sy ha 1 F η fixedBadMask 1 tp
  have hf := compact_radial_summable f keep Φ K 2 hK hΦs
  have hg := compact_radial_summable g keep Φ K 2 hK hΦs
  have hh := compact_radial_summable h keep Φ K 2 hK hΦs
  change radialEnergy f keep Φ K≤2*(radialEnergy g keep Φ K+radialEnergy h keep Φ K)
  unfold radialEnergy
  calc
    _≤∑'z:O,2*((if keep z then ‖g z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0)+
      (if keep z then ‖h z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0)) := by
      apply hf.tsum_le_tsum _ ((hg.add hh).mul_left 2)
      intro z
      by_cases hz : keep z
      · let χ := Classical.choice (selected_character_exists η fixedBadMask F z
          fixedBadMask_ne_zero hF (hkeep z hz) (dvd_mul_right _ _) (dvd_mul_left _ _))
        have he : f z=g z-h z := selected_difference s hb C hS hX₁ hX₂ hY₁ hY₂ hT
          ha hd hG η fixedBadMask F z (dvd_mul_right _ _) (dvd_mul_left _ _) χ tp
        have hn := norm_sub_le (g z) (h z)
        have hsquare : ‖f z‖^2≤2*(‖g z‖^2+‖h z‖^2) := by
          rw [he]
          nlinarith [norm_nonneg (g z),norm_nonneg (h z),norm_nonneg (g z-h z),
            sq_nonneg (‖g z‖-‖h z‖)]
        simp only [if_pos hz]
        convert mul_le_mul_of_nonneg_right hsquare (hΦ _) using 1 <;> ring
      · simp only [if_neg hz,zero_add,mul_zero,le_refl]
    _=_ := by rw [tsum_mul_left,hg.tsum_add hh]

/-- Exactly the same original source volume and exactly the same
selected weights occur on all three sides. No fresh selected mass. -/
theorem grouped_energy_split {α : Type v} [Fintype α] (q : Data α) (hP : ∀i,0<q.P i)
    (ha : 0<a) (hd : s.d=(1,1)) (hG : s.G=1) (η : Character) (tp : ℝ)
    (keep : Id→O→Prop) (hkeep : ∀F∈selectedProducts q,∀z,keep F z→z≠0)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hΦs : Function.support (Φ : ℝ→ℂ)⊆Iic 2) (hΦ : ∀x,0≤(Φ x).re) :
    groupedMoment q s ha η tp keep Φ K≤
      2*(groupedMoment q sx ha η tp keep Φ K+groupedMoment q sy ha η tp keep Φ K) := by
  have hsy : sourceVolume sy=sourceVolume s := swap_volume s
  have hsx : sourceVolume sx=sourceVolume s := rfl
  unfold groupedMoment
  rw [hsx,hsy,←add_div,←mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (sourceVolume_pos s).le
  calc
    _≤∑F:selectedProducts q,(groupedWeight q F.val/MixedSelectedVolume.scale q)*
        (2*(selectedEnergy sx ha 1 F.val η fixedBadMask 1 tp (keep F.val) Φ K+
          selectedEnergy sy ha 1 F.val η fixedBadMask 1 tp (keep F.val) Φ K)) := by
      apply Finset.sum_le_sum
      intro F hF
      exact mul_le_mul_of_nonneg_left
        (selected_energy_split s hb C hS hX₁ hX₂ hY₁ hY₂ hT ha hd hG η F.val
          (selected_products_supported q F.val F.property) tp (keep F.val)
          (hkeep F.val F.property) Φ K hK hΦs hΦ)
        (div_nonneg (grouped_weight_nonneg q F.val) (MixedSelectedVolume.scale_pos q hP).le)
    _=_ := by
      rw [mul_add]
      simp only [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro F hF
      ring
end Exact

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- Whole actual centered source moment. There is NO small-Y hypothesis.
Both original rectangles satisfy the stated original scale caps. Their
exact two-source decomposition uses the same constant, selected family,
input width, marked width, source volume and fixed seed reserve.
-/
theorem uniform_centered_source_moment
    (Φ : 𝓢(ℝ,ℂ)) (N Holes : ℕ) (hcard : Fintype.card ι≤N) (Wslot : ℝ→ℂ)
    (a b Lorig B Lslot Lcap Cap BR0 BH Bη lo hi Kslot Bseed ε rho : ℝ)
    (hΦs : Function.support (Φ : ℝ→ℂ)⊆Iic 2) (hΦ : ∀x,0≤(Φ x).re)
    (hWs : Function.support Wslot⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hLorig : 0≤Lorig) (hB : 2*Lorig+1≤B)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hBcap : B≤Lcap)
    (hslots : (N:ℝ)*Lslot≤B) (hCap : 2≤Cap) (hCapc : b/comparisonScale b≤Cap)
    (hBR0 : 0≤BR0) (hBH : 0≤BH) (hBη : 0≤Bη)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hKslot : 1≤Kslot)
    (hBseed : 0≤Bseed) (hε : 0<ε) (hrho : 0<rho)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    let step := budgetStep B Bseed ε rho
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus→
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀T : Finset ι,
    ∀(θ : ι→RayQuotient.Characters M Hray)(w σ freq : ι→ℝ)
      (t₀ tp V : ℝ)(R₀ : ι→Finset Id),
      (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
      0≤V→(∀i,|freq i|≤V)→(∀i,(R₀ i).card≤Holes)→
    ∀s : Source T a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀
      (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val)
      t₀ (fun i=>R₀ i.val) s→
      s.d=(1,1)→s.G=1→(∀i,s.M i≤Kslot)→(s.R.absNorm:ℝ)≤Z^BR0→
      s.H⊆enclosure (Cap*Z^Lcap)→((∏I∈MixedCompletedRows.holes s.H,I).absNorm:ℝ)≤Z^BH→
      (∀i : T,∀P∈s.H,P.val∈R₀ i.val)→(s.Fhole.absNorm:ℝ)≤Z^BH→
      s.X₁≤Z^Lorig→s.X₂≤Z^Lorig→s.Y₁≤Z^Lorig→s.Y₂≤Z^Lorig→
    ∀η : Character,(η.modulus.absNorm:ℝ)≤Z^Bη→
    ∀K : ℝ,0<K→K≤Z^B→K⁻¹≤Z^B→
    ∀(χ₀ : RayCharacter)(msecond : O),msecond≠0→goodLambda∣msecond→(2:O)∣msecond→
    ∀(α : Type v) [Fintype α],∀q : Data α,
      Fintype.card α≤N→(∀i,0<q.P i)→(∀i,∀I∈q.pool i,(I.absNorm:ℝ)≤2*q.P i)→
      (∀i,∀I∈q.pool i,‖q.ν i I‖≤1)→(∀i x,‖q.Wslot i x‖≤Kslot)→
      MixedSelectedVolume.scale q≤Z^B→(MixedSelectedVolume.scale q)⁻¹≤Z^B→
      1≤MixedSelectedVolume.volume q→
    let R := inputWidth η K Z
    let P := Real.logb Z s.T
    let S := ∑i : T,w i.val
    let d := Real.logb Z (MixedSelectedVolume.volume q)
    0≤R→P+2*S+4*d≤R-rho→(3/4:ℝ)*S<d→
    ∀keep : Id→O→Prop,
      (∀F∈selectedProducts q,∀z,keep F z→z≠0)→
      (∀F∈selectedProducts q,∀z,keep F z→
        ¬FixedInducingRow η Q fixedBadMask ((primaryGenerator F)^2) z)→
    ∀Dseed : Id,Dseed≠0→(Dseed.absNorm:ℝ)≤Z^Bseed→
    ((Dseed.absNorm:ℝ)^step*Z^step)*groupedMoment q s ha η tp keep Φ K≤
      C*Kslot^(2*N)*(sourceControl control s.W₁*sourceControl control s.W₂)^2*
        (height t₀ V s.t₁ s.t₂)^J*(1+|tp|)^J*((η.modulus.absNorm:ℝ)*K)*Z^ε := by
  dsimp only
  obtain ⟨J,control,hbase⟩ := uniform_source_moment (ι:=ι) M Hray hHray
    Φ N Holes hcard Wslot a b Lorig B Lslot Lcap Cap BR0 BH Bη lo hi Kslot Bseed ε rho
    hΦs hΦ hWs hW ha haUpper hb hLorig hB hLslot hLcap hBcap hslots hCap hCapc
    hBR0 hBH hBη hβ hKslot hBseed hε hrho Q hQt hQ72 hQM
  refine ⟨J,control,?_⟩
  intro η₀ hη₀
  obtain ⟨C,hC,hbound⟩ := hbase η₀ hη₀
  refine ⟨4*C,by positivity,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T θ w σ freq t₀ tp V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical hd hG hMs
    hR hHholes hholes hHR hFhole hX₁ hX₂ hY₁ hY₂ η hη K hK hKcap hKinv
    χ₀ msecond hm hml hm2 α instα q hα hqP hqpool hqν hqW hWcap hWinv hqvolume
    hR0 hmixed hnative keep hkeep heligible Dseed hDseed hDcap
  have hb0 : 0≤b := zero_le_one.trans hb
  have hLc : 2*Lorig≤Lcap := by linarith
  have hc := rectangle_caps s hb0 Z Lorig Lcap Cap hZ.1.le hLorig hLc hCapc hX₁ hX₂ hY₁ hY₂
  let sx := tinySource s hb0 (Cap*Z^Lcap) hcanonical.1 hc.1 hc.2.1 hc.2.2.2.2
  let sy := tinySource (swapRectangles s) hb0 (Cap*Z^Lcap) hcanonical.1
    hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2
  have hsx : Canonical M Hray hHray Wslot Cap Lcap Z η₀
      (fun i:T=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val)
      t₀ (fun i=>R₀ i.val) sx := hcanonical
  have hsy : Canonical M Hray hHray Wslot Cap Lcap Z η₀
      (fun i:T=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val)
      t₀ (fun i=>R₀ i.val) sy := hcanonical
  have hsmallx : (sx).Y₁≤comparisonScale b ∨ (sx).Y₂≤comparisonScale b :=
    Or.inl (tiny_small s hb0 (Cap*Z^Lcap) hcanonical.1 hc.1 hc.2.1 hc.2.2.2.2)
  have hsmally : (sy).Y₁≤comparisonScale b ∨ (sy).Y₂≤comparisonScale b :=
    Or.inl (tiny_small (swapRectangles s) hb0 (Cap*Z^Lcap) hcanonical.1
      hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2)
  have hx := hZ.2 T θ w σ freq t₀ tp V R₀ hw hwL hσ hσhi hV hfreq hR₀ sx hsx hd hG hMs
    hR hHholes hholes hHR hFhole hX₁ hX₂ hsmallx η hη K hK hKcap hKinv
    χ₀ msecond hm hml hm2 α q hα hqP hqpool hqν hqW hWcap hWinv hqvolume
    hR0 hmixed hnative keep hkeep heligible Dseed hDseed hDcap
  have hy := hZ.2 T θ w σ freq t₀ tp V R₀ hw hwL hσ hσhi hV hfreq hR₀ sy hsy hd hG hMs
    hR hHholes hholes hHR hFhole hY₁ hY₂ hsmally η hη K hK hKcap hKinv
    χ₀ msecond hm hml hm2 α q hα hqP hqpool hqν hqW hWcap hWinv hqvolume
    hR0 hmixed hnative keep hkeep heligible Dseed hDseed hDcap
  have hsplit := grouped_energy_split s hb0 (Cap*Z^Lcap) hcanonical.1
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2 q hqP ha hd hG η tp keep hkeep Φ K hK hΦs hΦ
  let reserve := (Dseed.absNorm:ℝ)^(budgetStep B Bseed ε rho)*Z^(budgetStep B Bseed ε rho)
  have hz : 0<Z := zero_lt_one.trans hZ.1
  let cost := C*Kslot^(2*N)*(sourceControl control s.W₁*sourceControl control s.W₂)^2*
    (height t₀ V s.t₁ s.t₂)^J*(1+|tp|)^J*((η.modulus.absNorm:ℝ)*K)*Z^ε
  have hreserve : 0≤reserve := by dsimp only [reserve];positivity
  change reserve*groupedMoment q sx ha η tp keep Φ K≤cost at hx
  change reserve*groupedMoment q sy ha η tp keep Φ K≤cost at hy
  calc
    _≤reserve*(2*(groupedMoment q sx ha η tp keep Φ K+groupedMoment q sy ha η tp keep Φ K)) :=
      mul_le_mul_of_nonneg_left hsplit hreserve
    _=2*(reserve*groupedMoment q sx ha η tp keep Φ K+reserve*groupedMoment q sy ha η tp keep Φ K) := by ring
    _≤2*(cost+cost) := mul_le_mul_of_nonneg_left (add_le_add hx hy) (by norm_num)
    _=_ := by dsimp only [cost];ring

end
end Candidate.FourthPower.MixedFirstCenteredSourceMoment
