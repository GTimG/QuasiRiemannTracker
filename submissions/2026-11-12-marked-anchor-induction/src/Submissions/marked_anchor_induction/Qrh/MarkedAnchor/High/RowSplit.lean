/- Copyright (c) 2026 Sil. Apache-2.0.
Adapted from sil-density-split `Density/LeafHighRow.lean` (`high_row_bound`, Apache-2.0): the supplier
`actual_high_retained_row` (whole row, slots paid by the zero bin) is replaced by Hailey Collet's
`actual_buffered_retained_plain_factors` (Cycle61, Apache-2.0), which pays only the two ordinary
factors and keeps the normalized slots literally. -/
import Submissions.sil_density_split_20261026.Density.LeafHighRow

/-!
# High.RowSplit

The ORDINARY-ONLY pointwise bound of a HIGH packed row. For a kept row `z`
of nonzero weight whose whole ray-twisted family has zero maximum `< b + 2e` at the supplier height
`3(i+1)Z^τ`, with ordinary profiles `Profiles (1/4) (9/4)` and lengths `ℓ(X₁), ℓ(X₂) ≤ Lplain`:

`‖positiveSlotRow st.character st.mask 1 z W₁ W₂ S β P t X₁ X₂‖² ≤
  K (p.control S₀)² Z^((2b-1)(ℓ(X₁)+ℓ(X₂)) + 2ε₁d) · ∏ₖ ‖normalizedSlot … z (S k) (β k) t (P k)‖²`

for ARBITRARY slot data `(S, β, P)` (`P > 0`). The slot product is left to the detector count
(`High.Batch`), which pays it by `e·s` instead of `ν·s`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Qrh.MarkedAnchor.High
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily CenteredMomentEnergyState CenteredMomentInductionEnergy
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open CenteredMomentPrimeSlot CenteredMomentEnergyCapacityRemoval ConcreteTraceCRT
open CenteredMomentWholeSlotDeletion CenteredMomentRetainedProfile
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open LocalMoment Cycle61HighProfiles HeckeDetectorZeros
open QRH.SilDensitySplit.Density HeckeDyadic HeckeDetectorCoefficientTransfer
local notation "O" => HeckeFamily.O

section
variable (rayM : Ideal O) [NeZero rayM]
local instance rowSplitQuotientFinite : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- **Ordinary-only HIGH pointwise bound.** Constants (and the profile control set) first, then
the scale threshold; then the zero bin `b`, the state, the row, the slot data and the profiles. -/
theorem high_row_split (bΦ Mcap Lplain τ ε₁ e kap v d : ℝ) (hbΦ : 0 ≤ bΦ) (hL : 0 ≤ Lplain)
    (hτ : 0 < τ) (hε₁ : 0 < ε₁) (he : 0 < e) (he' : e < 1/1000) (hkap : 0 < kap)
    (hkap' : kap ≤ 1) (hv : 0 ≤ v) (hd : 0 < d) (hdsupply : Mcap+0+1 ≤ d)
    (hplainBudget : 12*e*(Lplain/d+2)+8*kap+2*v ≤ ε₁) :
    ∃ K : ℝ, 0 < K ∧ ∃ S₀ : Finset (ℕ×ℕ), ∀ η₀ : Character, ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ st : NaturalState Z 0 bΦ, st.puncture = 1 → st.width ≤ Mcap →
    ∀ (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus)
      (b : ℝ) (i : ℕ), 51/100 ≤ b → b ≤ 1 →
    ∀ z : O, ∀ hz : st.radial.keep z,
      st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0 →
      Cycle61InitialMass.geometryRowMaximum rayM H hH st η₀ hQM hQη z hz
        (3*(i+1 : ℕ)*Z^τ) < b + 2*e →
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t : ℝ),
      (∀ k, 0 < P k) →
      |t|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^4 ≤ (Z^d)^v →
    ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ →
      length Z X₁ ≤ Lplain → length Z X₂ ≤ Lplain →
      ‖positiveSlotRow st.character st.mask 1 z (p.profile 0) (p.profile 1) S β P t X₁ X₂‖^2 ≤
      K * (p.control S₀)^2 *
        Z^((2*b-1)*(length Z X₁ + length Z X₂) + 2*ε₁*d) *
        ∏ k, ‖normalizedSlot st.character st.mask 1 z (S k) (β k) t (P k)‖^2 := by
  have ha : (0:ℝ) < 1/4 := by norm_num
  obtain ⟨bound, hbound, hnorm⟩ := fixed_clipped_normalization (1/4) (9/4) ha
  obtain ⟨n, Cp, hCp, hplain⟩ := actual_buffered_retained_plain_factors (Lplain/d) d τ ε₁ e kap v
    (div_nonneg hL hd.le) hd.le hτ hε₁ he he' hkap hkap' hv hplainBudget bound
    (fun k => (hbound k).le)
  obtain ⟨S₀, Tc, Cc, hS, hCc, hclip⟩ := hnorm n
  refine ⟨(9/4)^2*Cc^2*Cp^2, by positivity, Tc, ?_⟩
  intro η₀
  have hT : ∀ᶠ Z : ℝ in atTop, 2 < Z^τ :=
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop _)
  filter_upwards [eventual_state_conductor bΦ Mcap hbΦ, hT, eventually_gt_atTop (1:ℝ)]
    with Z hZc hZT hZ1
  refine ⟨hZ1, ?_⟩
  intro st hu hwidth hQM hQη b i hb hb1 z hz hp hupper ι _ _ S β P t hP hwinP hgate p X₁ X₂
    hX₁ hX₂ hl₁ hl₂
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  let X : Fin 2 → ℝ := ![X₁, X₂]
  have hX : ∀ k, 0 < X k := by
    intro k; fin_cases k
    · exact hX₁
    · exact hX₂
  have hslot0 : 0 ≤ ∏ k, ‖normalizedSlot st.character st.mask 1 z (S k) (β k) t (P k)‖^2 :=
    Finset.prod_nonneg (fun _ _ => sq_nonneg _)
  by_cases hne : positiveSlotRow st.character st.mask 1 z (p.profile 0) (p.profile 1)
      S β P t X₁ X₂ = 0
  · rw [hne, norm_zero]
    have hK : 0 ≤ (9/4:ℝ)^2*Cc^2*Cp^2 := by positivity
    have hz := Real.rpow_nonneg hZ0.le ((2*b-1)*(length Z X₁ + length Z X₂) + 2*ε₁*d)
    have := p.control_nonneg Tc
    calc (0:ℝ)^2 = 0 := by norm_num
      _ ≤ _ := by positivity
  have hret : ∀ k, 1 ≤ X k * (9/4) :=
    OAI.SevenEighths.Record1252270103Source.positive_row_surviving_scales p st.character
      st.mask z S β P t X hX hne
  obtain ⟨hcc, -, hsupp, hsmooth, hmellin⟩ := hclip p X hX hret
  -- the plain-factor supplier
  let F := naturalRow st.character z (st.row_ne_zero z hz)
  have hcond := hZc.2 0 st hwidth z (st.row_ne_zero z hz) hp
  have hmod : (((excluded F.character st.puncture).modulus.absNorm : ℕ) : ℝ) ≤ Z^d := by
    have hR : (st.puncture.absNorm : ℝ) ≤ Z^(0:ℝ) := by rw [hu]; simp
    have := QRH.Record1252270103Low.excluded_character_power_bound Z (Mcap+1) 0 hZ0
      F.character st.puncture st.puncture_ne_zero hcond hR
    refine this.trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))
  let Wn : Fin 2 → ℝ → ℂ := fun k => ((normalizedPlains ha S₀ p X hX).profile k : ℝ → ℂ)
  let r : Fin 2 → ℝ := fun k => length Z (X k)/d
  have hr0 : ∀ k, 0 ≤ r k := fun k => div_nonneg (length_nonneg Z _ hZ1) hd.le
  have hrR : ∀ k, r k ≤ Lplain/d := by
    intro k
    apply div_le_div_of_nonneg_right _ hd.le
    fin_cases k
    · exact hl₁
    · exact hl₂
  have hcoeff : ∀ I : Ideal O,
      idealCoeff st.character I*CanonicalRowCompletion.idealRowHom (st.mask^6*(1*z)) I =
        if false then star (idealCoeff
          (Cycle61InitialMass.geometryRowFamily rayM H hH st η₀ z hz (Sum.inl ())) I)
        else idealCoeff (Cycle61InitialMass.geometryRowFamily rayM H hH st η₀ z hz (Sum.inl ())) I := by
    intro I
    have hj : Cycle61InitialMass.geometryRowFamily rayM H hH st η₀ z hz (Sum.inl ()) =
        excluded F.character st.puncture := rfl
    simp only [Bool.false_eq_true, ite_false, one_mul, hj]
    simpa only [NaturalState.mask] using (F.masked_ideal st.puncture st.puncture_ne_zero I).symm
  have hbd := hplain Z d hZ1.le hd.le le_rfl hZT
    (Cycle61InitialMass.geometryRowFamily rayM H hH st η₀ z hz)
    (Cycle61InitialMass.geometry_row_family_nonprincipal rayM H hH st η₀ hQM hQη z hz)
    b i hb hb1 hupper (Sum.inl ()) st.character st.mask z false hcoeff S β P hP Wn X r
    (fun _ => 1/9) (fun _ => 9/4) t hX (fun k => clippedScale_eq_rpow hZ1 hd)
    (fun _ => by norm_num)
    (fun k => by
      have := hsupp k
      simp only [orientedProfile, Bool.false_eq_true, ite_false]
      norm_num at this ⊢
      exact this)
    (fun k => by simpa only [orientedProfile, Bool.false_eq_true, ite_false] using hsmooth k)
    hmod hr0 hrR hwinP hgate
    (fun k x hx u => by
      simpa only [orientedProfile, Bool.false_eq_true, ite_false] using
        hmellin k 2 (Or.inl rfl) x (high_strip_mem hb1 he'.le hx) u)
    (fun k x hx u => by
      simpa only [orientedProfile, Bool.false_eq_true, ite_false] using
        hmellin k (n+2) (Or.inr rfl) x (high_strip_mem hb1 he'.le hx) u)
  -- reduce the packed row to the normalised retained row
  have hraw := retained_rectangle_raw_energy st.character st.mask 1 z (p.profile 0)
    (p.profile 1) S β P hP t X₁ X₂ (X₁*X₂) hX₁ hX₂ (mul_pos hX₁ hX₂)
  have hnormsq : ‖retainedPositiveRow st.character st.mask 1 z (p.profile 0) (p.profile 1)
      S β P t X₁ X₂‖^2 =
      (clippedControl ha S₀ p X hX 0 * clippedControl ha S₀ p X hX 1)^2 *
      ‖retainedPositiveRow st.character st.mask 1 z (Wn 0) (Wn 1) S β P t X₁ X₂‖^2 :=
    OAI.SevenEighths.Record1252270103Source.retained_plain_normalized_norm_sq ha S₀ hS p
      st.character st.mask z S β P t X hX hret
  have hclip1 : clipDilation X₁ ≤ 9/4 := by
    have := clipDilation_le (9/4) X₁ hX₁ (hret 0)
    rwa [max_eq_right (by norm_num : (1:ℝ) ≤ 9/4)] at this
  have hclip2 : clipDilation X₂ ≤ 9/4 := by
    have := clipDilation_le (9/4) X₂ hX₂ (hret 1)
    rwa [max_eq_right (by norm_num : (1:ℝ) ≤ 9/4)] at this
  have hfac : clippedScale X₁ * clippedScale X₂ / (X₁*X₂) ≤ (9/4)^2 := by
    rw [← div_mul_div_comm]
    change clipDilation X₁ * clipDilation X₂ ≤ _
    have h1 := clipDilation_ge_one X₁ hX₁
    nlinarith [clipDilation_ge_one X₂ hX₂]
  have hc0 := clippedControl_nonneg ha S₀ p X hX 0
  have hc1 := clippedControl_nonneg ha S₀ p X hX 1
  have hpc := p.control_nonneg Tc
  have hcc2 : (clippedControl ha S₀ p X hX 0 * clippedControl ha S₀ p X hX 1)^2 ≤
      Cc^2 * (p.control Tc)^2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg hc0 hc1) hcc 2
  have hexp : (Z^d)^((2*b-1)*(r 0+r 1)+2*ε₁) =
      Z^((2*b-1)*(length Z X₁ + length Z X₂) + 2*ε₁*d) := by
    rw [← Real.rpow_mul hZ0.le]
    congr 1
    change d*((2*b-1)*(length Z X₁/d + length Z X₂/d)+2*ε₁) = _
    field_simp
  have hbd' : ‖retainedPositiveRow st.character st.mask 1 z (Wn 0) (Wn 1) S β P t X₁ X₂‖^2 ≤
      Cp^2*Z^((2*b-1)*(length Z X₁ + length Z X₂) + 2*ε₁*d) *
        ∏ k, ‖normalizedSlot st.character st.mask 1 z (S k) (β k) t (P k)‖^2 := by
    rw [← hexp]; exact hbd
  have hrow0 : ‖positiveSlotRow st.character st.mask 1 z (p.profile 0) (p.profile 1)
      S β P t X₁ X₂‖^2 = clippedScale X₁ * clippedScale X₂ / (X₁*X₂) *
      ‖retainedPositiveRow st.character st.mask 1 z (p.profile 0) (p.profile 1)
        S β P t X₁ X₂‖^2 := by
    unfold positiveSlotRow
    exact hraw
  rw [hrow0, hnormsq]
  have hR0 := sq_nonneg ‖retainedPositiveRow st.character st.mask 1 z (Wn 0) (Wn 1)
    S β P t X₁ X₂‖
  have hfac0 : 0 ≤ clippedScale X₁ * clippedScale X₂ / (X₁*X₂) := by
    have := clippedScale_ge_one X₁
    have := clippedScale_ge_one X₂
    positivity
  have hZe := Real.rpow_nonneg hZ0.le ((2*b-1)*(length Z X₁ + length Z X₂) + 2*ε₁*d)
  calc clippedScale X₁ * clippedScale X₂ / (X₁*X₂) *
        ((clippedControl ha S₀ p X hX 0 * clippedControl ha S₀ p X hX 1)^2 *
        ‖retainedPositiveRow st.character st.mask 1 z (Wn 0) (Wn 1) S β P t X₁ X₂‖^2)
      ≤ (9/4)^2 * ((Cc^2 * (p.control Tc)^2) *
        (Cp^2*Z^((2*b-1)*(length Z X₁ + length Z X₂) + 2*ε₁*d) *
          ∏ k, ‖normalizedSlot st.character st.mask 1 z (S k) (β k) t (P k)‖^2)) := by
        apply mul_le_mul hfac _ (by positivity) (by norm_num)
        exact mul_le_mul hcc2 hbd' hR0 (by positivity)
    _ = _ := by ring

end
end
end Qrh.MarkedAnchor.High
