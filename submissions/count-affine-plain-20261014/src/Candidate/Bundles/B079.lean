/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B020
import Candidate.Bundles.B063
import Candidate.Bundles.B078
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.PaidBands
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.Counting

/- BEGIN ORIGINAL Cycle61.Moment.LowBranch.Incumbent; sha256 1547465fe6192651dd2c9441866b437e3b5783f98c31354c1ca31282761a708e -/
section
                              
                                

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Moment.LowBranch
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthSchedule
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Both incumbent endpoints are genuine original analytic inputs, with a
single degree and profile control. No affine or improved endpoint is used. -/
theorem original_incumbent
    (W : ℝ → ℂ) (aslot bslot a b radial Bmask L lo hi Mcap ε : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hε : 0 < ε)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) :
    ∃ degree : ℕ, ∃ S : Finset (ℕ × ℕ), ∀ η₀ : Character, ∀ Q : Ideal O, Q ≤ M →
      internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
      ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
        ZeroAt (internalQ Q η₀) a b radial Bmask L Mcap ε Z degree S C₀ ∧
        PositiveAt (α := α) M H hH W bslot a b radial Bmask L
          (Cycle25.Energy.commonMesh Mcap Bmask L ε) lo hi Mcap ε (3/4)
          Z η₀ Q degree S C₁ := by
  have hκ : 2*HeckeZeroSupremum.beta-1 ≤ (3/4 : ℝ) := by
    linarith [Cycle61.Assembly.baseline_beta]
  have hcert := Cycle25CenteredMomentEnergyCertifiedExistence.terminal_certificate
    (α := α) M H hH W aslot bslot a b radial Bmask L lo hi Mcap (3/4) ε
    haslot hWs hW hbslot ha haUpper hb hrad hmask hMcap (by norm_num) hε hbeta hκ
  exact certified_terminal (α := α) M H hH W bslot a b radial Bmask L lo hi Mcap
    (3/4) ε hmask hMcap.le (by norm_num) hε hcert

#print axioms original_incumbent
end
end OAI.SevenEighths.Cycle61Moment.LowBranch

end
/- END ORIGINAL Cycle61.Moment.LowBranch.Incumbent -/

/- BEGIN ORIGINAL LocalMoment.RestrictedIncumbent; sha256 188b456c8477ae12cf7ae466be7687fd0c6e32c9dd8a00e95ade2227c3e33ff2 -/
section
                                                   

/-! Low-bin source payment: remove slots only on the restricted rows,
then apply the incumbent moment to the remaining exact natural state. -/

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.LocalMoment
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyPaidBands CenteredMomentEnergyCapacityRemoval
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot CenteredMomentHeckeSlots
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource QuadraticInitialBound
open CenteredMomentRetainedEnergy
local notation "O" => HeckeFamily.O

variable {α : Type*}

/-- Post-transform row restriction is kept while paying removed slots.
The remaining nonnegative norm is enlarged only after this payment. -/
theorem restricted_energy_remove {Z Bmask bΦ : ℝ}
    (s : NaturalState Z Bmask bΦ) (low : O → Prop)
    (J R : Finset α) (hR : R ⊆ J)
    (W₁ W₂ : ℝ → ℂ) (slots : α → Finset (Ideal O))
    (coeff : α → Ideal O → ℂ) (P : α → ℝ)
    (t X₁ X₂ κlow : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hP : ∀ i, 0 ≤ P i) (w B : α → ℝ) (hB : ∀ i ∈ R, 0 ≤ B i)
    (hslot : ∀ z, s.radial.keep z → low z → ∀ i ∈ R,
      ‖normalizedSlot s.character s.mask 1 z (slots i) (coeff i) t (P i)‖ ^ 2 ≤
        B i * Z ^ (κlow * w i)) :
    energy s.character s.mask 1 t W₁ W₂ (fun i : J => slots i)
      (fun i : J => coeff i) (fun i : J => P i) X₁ X₂
      (fun z => s.radial.keep z ∧ low z) s.radial.profile s.radial.scale ≤
      ((∏ i ∈ R, B i) * Z ^ (κlow * ∑ i ∈ R, w i)) *
        energy s.character s.mask 1 t W₁ W₂ (fun i : ↥(J \ R) => slots i)
          (fun i : ↥(J \ R) => coeff i) (fun i : ↥(J \ R) => P i) X₁ X₂
          s.radial.keep s.radial.profile s.radial.scale := by
  classical
  have hZ : 0 < Z := zero_lt_one.trans_le s.base_ge_one
  let cost := (∏ i ∈ R, B i) * Z ^ (κlow * ∑ i ∈ R, w i)
  have hcost : 0 ≤ cost := mul_nonneg (Finset.prod_nonneg hB) (Real.rpow_nonneg hZ.le _)
  have hsum (T : Finset α) (keep : O → Prop) := compact_radial_summable
    (fun z => positiveSlotRow s.character s.mask 1 z W₁ W₂
      (fun i : T => slots i) (fun i : T => coeff i) (fun i : T => P i) t X₁ X₂)
    keep s.radial.profile s.radial.scale bΦ s.radial.scale_pos s.radial_support
  unfold energy
  rw [← tsum_mul_left]
  apply (hsum J (fun z => s.radial.keep z ∧ low z)).tsum_le_tsum _
    ((hsum (J \ R) s.radial.keep).mul_left cost)
  intro z
  by_cases hk : s.radial.keep z
  · by_cases hl : low z
    · simp only [hk, hl, and_self, ite_true]
      have hh := selectedProduct_energy_remove J R hR s.character s.mask 1 z W₁ W₂
        slots coeff P t X₁ X₂ Z κlow hZ w B hB (hslot z hk hl)
      rw [selected_eq_positive J s.character s.mask 1 z W₁ W₂ slots coeff P t X₁ X₂
        (mul_pos hX₁ hX₂).le hP,
        selected_eq_positive (J \ R) s.character s.mask 1 z W₁ W₂ slots coeff P
          t X₁ X₂ (mul_pos hX₁ hX₂).le hP] at hh
      exact (mul_le_mul_of_nonneg_right hh (s.radial.nonneg z)).trans_eq (by ring)
    · simp only [hk, hl, and_false, ite_false, ite_true]
      exact mul_nonneg hcost (mul_nonneg (sq_nonneg _) (s.radial.nonneg z))
  · simp only [hk, false_and, ite_false, mul_zero, le_refl]

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The low-bin removal rate and the incumbent capacity rate are separate.
This theorem calls only the incumbent positive or zero-slot moment on the
remaining state, including every original mask and eligibility predicate. -/
theorem restricted_paid_incumbent
    (W : ℝ → ℂ) (bslot a b bΦ Bmask L Lslot lo hi Mcap ε κbase Z : ℝ)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ × ℕ)) (C₀ C₁ : ℝ)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hzero : ZeroAt (internalQ Q η₀) a b bΦ Bmask L Mcap ε Z degree S C₀)
    (hpositive : PositiveAt (α := α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
      Mcap ε κbase Z η₀ Q degree S C₁)
    (J R : Finset α) (hR : R ⊆ J) (θ : α → RayQuotient.Characters M H)
    (w σ v : α → ℝ) (t height κlow : ℝ) (B : α → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwL : ∀ i, w i ≤ Lslot)
    (hσlo : ∀ i, lo ≤ σ i) (hσhi : ∀ i, σ i ≤ hi)
    (hheight : 0 ≤ height) (hv : ∀ i, |v i| ≤ height) (hB : ∀ i ∈ R, 0 ≤ B i)
    (s : NaturalState Z Bmask bΦ) (hQ : s.fixedModulus = internalQ Q η₀)
    (hs : s.width ≤ Mcap) (low : O → Prop) (p : Profiles a b) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hc₁ : X₁ ≤ Z ^ L) (hc₂ : X₂ ≤ Z ^ L)
    (hcapacity : R = J ∨
      length Z X₁ + length Z X₂ + 6 * κbase * (∑ i ∈ J \ R, w i) ≤ s.width)
    (hslot : ∀ z, s.radial.keep z → low z → ∀ i ∈ R,
      ‖normalizedSlot s.character s.mask 1 z (primePool M H bslot (Z ^ (w i)))
        (fun I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight W (Z ^ (w i)) (σ i) (v i) I)
        t (Z ^ (w i))‖ ^ 2 ≤ B i * Z ^ (κlow * w i)) :
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i : J => primePool M H bslot (Z ^ (w i)))
      (fun (i : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight W (Z ^ (w i)) (σ i) (v i) I)
      (fun i : J => Z ^ (w i)) X₁ X₂ (fun z => s.radial.keep z ∧ low z)
      s.radial.profile s.radial.scale ≤
      (∏ i ∈ R, B i) * ((C₀ + C₁) * diagonalControl s.radial.profile *
        (p.control S) ^ 2 * (1 + |t| + height) ^ degree) *
        Z ^ (s.width + ε + κlow * ∑ i ∈ R, w i) := by
  classical
  have hZ : 0 < Z := zero_lt_one.trans_le s.base_ge_one
  have he := restricted_energy_remove s low J R hR (p.profile 0) (p.profile 1)
    (fun i => primePool M H bslot (Z ^ (w i)))
    (fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
      HeckePrimeAnnular.annularWeight W (Z ^ (w i)) (σ i) (v i) I)
    (fun i => Z ^ (w i)) t X₁ X₂ κlow hX₁ hX₂
    (fun i => Real.rpow_nonneg hZ.le _) w B hB hslot
  have hb := remaining_energy_bound M H hH W bslot a b bΦ Bmask L Lslot lo hi
    Mcap ε κbase Z η₀ Q degree S C₀ C₁ hC₀ hC₁ hzero hpositive
    J R θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂
    hX₁ hX₂ hc₁ hc₂ hcapacity
  apply he.trans ((mul_le_mul_of_nonneg_left hb
    (mul_nonneg (Finset.prod_nonneg hB) (Real.rpow_nonneg hZ.le _))).trans_eq ?_)
  simp only [Real.rpow_add hZ]
  ring

end SevenEighths.LocalMoment
end
end OAI

end
/- END ORIGINAL LocalMoment.RestrictedIncumbent -/

/- BEGIN ORIGINAL Cycle61.Physical.CoarseEnergy; sha256 5bbdadd7a91f9cb44ce85bcf45cfa53f0207120d507b2e27e686dd4f458f0117 -/
section
/-
Copyright (c) 2026 Hailey Collet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
                                      
                                                   

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Physical
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily HeckePrimeRay HeckePrimeAnnular HeckeDyadic
open CenteredMomentRetainedEnergy
open CenteredMomentCounting CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentSecondHeightFamily CenteredMomentHeckeSlots
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open CenteredMomentDetectorDictionary CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ)

/-- Absolute finite ideal counting gives a uniform slot bound even at tiny
scales and arbitrarily large frequencies. No zero-family condition is used. -/
theorem ray_slot_coarse (W : ℝ → ℂ) (a b lo hi : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) (hW : Continuous W) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (χ : Character) (P σ freq : ℝ),
      1 ≤ P → lo ≤ σ → σ ≤ hi →
      ‖rayPrimePolynomial M H χ W b P σ freq‖ ^ 2 ≤ C * P ^ 2 := by
  obtain ⟨B,hB,hprofile⟩ := fixed_profile_norm_bound W hW a b lo hi ha
  let K := 128*B*max 1 b
  refine ⟨max 1 (K^2),le_max_left _ _,?_⟩
  intro χ P σ freq hP hσ hσhi
  have hPp : 0 < P := zero_lt_one.trans_le hP
  let S := (annulusSet b P).filter (fun I => Prime I ∧ I ∈ RayQuotient.identityClass M H)
  let f : Ideal O → ℂ := fun I =>
    if I ∈ S then idealCoeff χ I * annularWeight W P σ freq I else 0
  have hn (I : Ideal O) : ‖idealCoeff χ I * annularWeight W P σ freq I‖ ≤ B := by
    apply (show ‖idealCoeff χ I * annularWeight W P σ freq I‖ ≤
      ‖annularWeight W P σ freq I‖ by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one χ I)).trans
    by_cases hz : W ((I.absNorm : ℝ)/P) = 0
    · simp [annularWeight,hz,hB.le]
    · have hs := hWs hz
      rw [annularWeight,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans_le hs.1)]
      simpa only [Complex.neg_re,shift_re] using hprofile σ ⟨hσ,hσhi⟩ _ hs
  have hsum := norm_tsum_ideal_ball f (max 1 b*P) B (by positivity) hB.le
    (by
      change f (0 : Ideal O) = 0
      simp only [f,idealCoeff_zero,zero_mul,ite_self])
    (by intro I; dsimp only [f]; split_ifs; exact hn I; simpa using hB.le)
    (by
      intro I hI
      have hmem : I ∈ S := by
        by_contra hnot
        exact hI (by simp only [f,ite_eq_right hnot])
      have hw : W ((I.absNorm : ℝ)/P) ≠ 0 := by
        intro hz
        exact hI (by simp only [f,ite_eq_left hmem,annularWeight,hz,zero_mul,mul_zero])
      exact ((div_le_iff₀ hPp).mp (hWs hw).2).trans
        (mul_le_mul_of_nonneg_right (le_max_right 1 b) hPp.le))
  have he : (∑' I : Ideal O, f I) = ∑ I ∈ S, idealCoeff χ I * annularWeight W P σ freq I := by
    rw [tsum_eq_sum (s := S) (fun I hI => by simp only [f,ite_eq_right hI])]
    exact Finset.sum_congr rfl (fun I hI => by simp only [f,ite_eq_left hI])
  rw [he] at hsum
  have hnorm : ‖(P : ℂ)^(-(1/2 : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hPp]
    norm_num only [Complex.neg_re,show ((1/2 : ℂ).re) = 1/2 by norm_num]
    exact Real.rpow_le_one_of_one_le_of_nonpos hP (by norm_num)
  have hb : ‖rayPrimePolynomial M H χ W b P σ freq‖ ≤ K*P := by
    unfold rayPrimePolynomial
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hnorm).trans
      (hsum.trans_eq (by dsimp only [K]; ring))
  calc
    _ ≤ (K*P)^2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = K^2*P^2 := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right 1 _) (sq_nonneg P)

/-- The natural masked relative coefficient is transported exactly; the
puncture mask is never removed in applying the absolute ray bound. -/
theorem natural_slot_coarse (W : ℝ → ℂ) (a b lo hi : ℝ) (ha : 0 < a)
    (hWs : Function.support W ⊆ Set.Icc a b) (hW : Continuous W) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Z Bmask bΦ : ℝ} (s : NaturalState Z Bmask bΦ),
      ∀ (ν : Character) (z : O), s.radial.keep z →
      ∀ P σ t v : ℝ, 1 ≤ P → lo ≤ σ → σ ≤ hi →
      ‖normalizedSlot s.character s.mask 1 z (primePool M H b P)
        (fun I => idealCoeff ν I * annularWeight W P σ v I) t P‖^2 ≤ C*P^2 := by
  obtain ⟨C,hC,hbound⟩ := ray_slot_coarse M H W a b lo hi ha hWs hW
  refine ⟨C,hC,?_⟩
  intro Z Bmask bΦ s ν z hz P σ t v hP hσ hσhi
  let F := naturalRow s.character z (s.row_ne_zero z hz)
  have hPp : 0 < P := zero_lt_one.trans_le hP
  rw [relative_normalizedSlot_eq_ray M H s.character (excluded F.character s.puncture)
    ν s.mask 1 z (by
      simpa only [one_mul,NaturalState.mask] using F.masked_element _ s.puncture_ne_zero)
    W b P σ t v hPp,norm_mul,
    CenteredMomentTwist.norm_real_imaginary_power P t hPp,one_mul]
  exact hbound _ P σ (t+v) hP hσ hσhi

variable {α : Type*} [Fintype α]
variable (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Paying every actual slot reduces to the unrestricted original plain
moment. The fixed extra exponent is bounded by the ambient slot count. -/
theorem coarse_energy_at (W : ℝ → ℂ) (aslot bslot lo hi : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (hW : Continuous W) (Lslot : ℝ) (hLslot : 0 ≤ Lslot) :
    ∃ Cslot : ℝ, 1 ≤ Cslot ∧
    ∀ (a b bΦ Bmask L Mcap ε Z : ℝ) (η₀ : Character) (Q : Ideal O)
      (degree : ℕ) (S : Finset (ℕ × ℕ)) (C₀ : ℝ), 0 ≤ C₀ →
    ZeroAt (internalQ Q η₀) a b bΦ Bmask L Mcap ε Z degree S C₀ →
    ∀ (J : Finset α) (θ : α → RayQuotient.Characters M H) (w σ v : α → ℝ)
      (t height : ℝ), (∀ i, 0 ≤ w i) → (∀ i, w i ≤ Lslot) →
      (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) → 0 ≤ height →
    ∀ (s : NaturalState Z Bmask bΦ), s.fixedModulus = internalQ Q η₀ → s.width ≤ Mcap →
    ∀ (p : Profiles a b) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ → X₁ ≤ Z^L → X₂ ≤ Z^L →
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i : J => primePool M H bslot (Z^(w i)))
      (fun (i : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
        annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i : J => Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      (Cslot^(Fintype.card α)*C₀)*diagonalControl s.radial.profile*(p.control S)^2*
        (1+|t|+height)^degree*Z^(s.width+ε+2*(Fintype.card α : ℝ)*Lslot) := by
  classical
  obtain ⟨Cs,hCs,hslot⟩ := natural_slot_coarse M H W aslot bslot lo hi haslot hWs hW
  refine ⟨Cs,hCs,?_⟩
  intro a b bΦ Bmask L Mcap ε Z η₀ Q degree S C₀ hC₀ hzero J θ w σ v t height
    hw hwL hσlo hσhi hheight s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hZ : 0 < Z := zero_lt_one.trans_le s.base_ge_one
  have hd := diagonalControl_nonneg s.radial.profile
  have hCs0 : 0 ≤ Cs := zero_le_one.trans hCs
  have hremove := LocalMoment.restricted_energy_remove s (fun _ => True) J J
    (Finset.Subset.refl J) (p.profile 0) (p.profile 1)
    (fun i => primePool M H bslot (Z^(w i)))
    (fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
      annularWeight W (Z^(w i)) (σ i) (v i) I)
    (fun i => Z^(w i)) t X₁ X₂ 2 hX₁ hX₂ (fun i => Real.rpow_nonneg hZ.le _)
    w (fun _ => Cs) (fun _ _ => zero_le_one.trans hCs) (by
      intro z hz _ i _
      have hb := hslot s (relativeCharacter M H hH η₀ (θ i)) z hz
        (Z^(w i)) (σ i) t (v i) (Real.one_le_rpow s.base_ge_one (hw i))
        (hσlo i) (hσhi i)
      have he : (Z^(w i))^2 = Z^(2*w i) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
        congr 1
        norm_num
        ring
      rw [he] at hb
      exact hb)
  let : IsEmpty ↥(J \ J) := ⟨fun i => by simpa using i.property⟩
  have hid : energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i : ↥(J \ J) => primePool M H bslot (Z^(w i)))
      (fun (i : ↥(J \ J)) I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
        annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i : ↥(J \ J) => Z^(w i)) X₁ X₂ s.radial.keep
      s.radial.profile s.radial.scale = s.plainEnergy p t X₁ X₂ := by
    simp only [energy,positiveSlotRow,NaturalState.plainEnergy,Fintype.prod_empty,mul_one]
  simp only [and_true,hid,Finset.prod_const] at hremove
  have hplain := hzero s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  simp only [Real.norm_eq_abs] at hplain
  have hcard : J.card ≤ Fintype.card α := Finset.card_le_univ J
  have hsum : (∑ i ∈ J, w i) ≤ (Fintype.card α : ℝ)*Lslot := by
    calc
      _ ≤ ∑ _i ∈ J, Lslot := Finset.sum_le_sum (fun i _ => hwL i)
      _ = (J.card : ℝ)*Lslot := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hLslot
  have hpow : (1+|t|)^degree ≤ (1+|t|+height)^degree :=
    pow_le_pow_left₀ (by positivity) (by linarith) degree
  apply hremove.trans
  calc
    _ ≤ (Cs^J.card*Z^(2*∑ i ∈ J, w i))*
        (C₀*diagonalControl s.radial.profile*(p.control S)^2*
          (1+|t|)^degree*Z^(s.width+ε)) :=
      mul_le_mul_of_nonneg_left hplain (by positivity)
    _ = (Cs^J.card*C₀)*diagonalControl s.radial.profile*(p.control S)^2*
        (1+|t|)^degree*Z^(s.width+ε+2*∑ i ∈ J, w i) := by
      rw [Real.rpow_add hZ (s.width+ε) (2*∑ i ∈ J, w i)]; ring
    _ ≤ _ := by
      have he : Z^(s.width+ε+2*∑ i ∈ J, w i) ≤
          Z^(s.width+ε+2*(Fintype.card α : ℝ)*Lslot) :=
        Real.rpow_le_rpow_of_exponent_le s.base_ge_one (by linarith)
      apply mul_le_mul _ he (by positivity) (by positivity)
      have hc := pow_le_pow_right₀ hCs hcard
      gcongr

/-- The live slot parameters and external heights are all quantified after
this bound's constant and eventual base threshold. -/
def CoarseEnergyAt (W : ℝ → ℂ) (bslot a b bΦ Bmask L Lslot lo hi Mcap ε Z : ℝ)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) : Prop :=
  ∀ (J : Finset α) (θ : α → RayQuotient.Characters M H) (w σ v : α → ℝ)
    (t height : ℝ), (∀ i, 0 ≤ w i) → (∀ i, w i ≤ Lslot) →
    (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) → 0 ≤ height →
  ∀ (s : NaturalState Z Bmask bΦ), s.fixedModulus = internalQ Q η₀ → s.width ≤ Mcap →
  ∀ (p : Profiles a b) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ → X₁ ≤ Z^L → X₂ ≤ Z^L →
  energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
    (fun i : J => primePool M H bslot (Z^(w i)))
    (fun (i : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
      annularWeight W (Z^(w i)) (σ i) (v i) I)
    (fun i : J => Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
    C*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+height)^degree*
      Z^(s.width+ε+2*(Fintype.card α : ℝ)*Lslot)

/-- Only the original unrestricted plain moment is an analytic prerequisite.
The coarse slot exponent is derived by finite counting and complete removal. -/
theorem eventual_coarse_energy (W : ℝ → ℂ) (aslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (hW : Continuous W) (hLslot : 0 ≤ Lslot)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ × ℕ))
    (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hzero : ∀ᶠ Z : ℝ in atTop,
      ZeroAt (internalQ Q η₀) a b bΦ Bmask L Mcap ε Z degree S C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
      CoarseEnergyAt (α := α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε Z η₀ Q degree S C := by
  obtain ⟨Cs,hCs,hbound⟩ := coarse_energy_at (α := α) M H hH W aslot bslot lo hi
    haslot hWs hW Lslot hLslot
  refine ⟨Cs^(Fintype.card α)*C₀,mul_pos (pow_pos (zero_lt_one.trans_le hCs) _) hC₀,?_⟩
  filter_upwards [hzero] with Z hz
  exact hbound a b bΦ Bmask L Mcap ε Z η₀ Q degree S C₀ hC₀.le hz

#print axioms ray_slot_coarse
#print axioms natural_slot_coarse
#print axioms coarse_energy_at
#print axioms eventual_coarse_energy
end
end OAI.SevenEighths.Cycle61Physical

end
/- END ORIGINAL Cycle61.Physical.CoarseEnergy -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialCoarse; sha256 115f5a8b9f8a88b1908f6f1ab10d492a49d630d232efc05c1dbda2494db99a75 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                    
                                  
                                         

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Physical
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
open CenteredMomentRetainedEnergy CenteredMomentPrimeSlot
open CenteredMomentDetectorEnergyInitialState ConcretePrimeRowBridge
open QuadraticInitialBound Cycle61Moment
local notation "O" => HeckeFamily.O
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
variable (R : Ideal O) [NeZero R]
local instance : Finite (O ⧸ R) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne R)
variable (H : Subgroup (O ⧸ R)ˣ) (hH : RayOrthogonality.globalUnits R ≤ H)

/-- The literal initial energy, including the original fixed mask and keep
predicate. Slot parameters retain their finite-subtype indexing. -/
def initialEnergy (W : ℝ → ℂ) (bslot Z width : ℝ) (η η₀ : Character) (Q : Ideal O)
    (T : Finset α) (θ : T → RayQuotient.Characters R H) (w σ v : T → ℝ)
    (t X₁ X₂ : ℝ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) : ℝ :=
  energy η (fixedBadMask*idealGenerator 1) 1 t W₁ W₂
    (fun i => primePool R H bslot (Z^(w i)))
    (fun i I => idealCoeff (relativeCharacter R H hH η₀ (θ i)) I *
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
    (fun i => Z^(w i)) X₁ X₂ (initialKeep η (internalQ Q η₀)) Φ (Z^width)

def InitialCoarseAt (W : ℝ → ℂ) (bslot a b bΦ mesh lo hi Mmin Mmax extra Z : ℝ)
    (η η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) : Prop :=
  ∀ T : Finset α, ∀ (θ : T → RayQuotient.Characters R H) (w σ v : T → ℝ)
    (t height : ℝ), (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
    (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) → 0 ≤ height →
  ∀ width : ℝ, Mmin ≤ width → width ≤ Mmax →
  ∀ Φ : 𝓢(ℝ,ℂ), Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ →
    (∀ x, 0 ≤ (Φ x).re) →
  ∀ p : Profiles a b, ∀ X₁ X₂ : ℝ, 0 < X₁ → 0 < X₂ →
    X₁ ≤ Z^(Mmax+1) → X₂ ≤ Z^(Mmax+1) →
    initialEnergy R H hH W bslot Z width η η₀ Q T θ w σ v t X₁ X₂
      (p.profile 0) (p.profile 1) Φ ≤
      C*diagonalControl Φ*(p.control S)^2*(1+|t|+height)^degree*Z^(width+extra)

/-- The original incumbent supplies the plain moment. The fixed anchor's
logarithmic conductor width is paid uniformly over the finite dictionary. -/
theorem original_initial_coarse (W : ℝ → ℂ) (aslot bslot a b bΦ mesh lo hi Mmin Mmax ε : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b) (hbΦ : 0 < bΦ)
    (hmesh : 0 ≤ mesh) (hMmin : 0 < Mmin) (hMM : Mmin ≤ Mmax)
    (hε : 0 < ε) (hεone : ε ≤ 1) (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (η : Label → Character) :
    ∃ degree : ℕ, ∃ S : Finset (ℕ × ℕ), ∀ η₀ : Character, ∀ Q : Ideal O,
      Q ≤ R → internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ label : Label,
      InitialCoarseAt (α := α) R H hH W bslot a b bΦ mesh lo hi Mmin Mmax
        (ε+2*(Fintype.card α : ℝ)*mesh) Z (η label) η₀ Q degree S C := by
  classical
  have hMmax : 0 < Mmax := hMmin.trans_le hMM
  have hhalf : 0 < ε/2 := by positivity
  obtain ⟨degree,S,hinc⟩ := Cycle61Moment.LowBranch.original_incumbent (α := α)
    R H hH W aslot bslot a b bΦ 0 (Mmax+1) lo hi (Mmax+1) (ε/2)
    haslot hWs hW hbslot ha haUpper hb hbΦ (by norm_num) (by linarith) hhalf hbeta
  have hchoices (T : Finset α) := coarse_energy_at (α := T) R H hH W aslot bslot lo hi
    haslot hWs hW.continuous mesh hmesh
  choose Cs hCs hcoarse using hchoices
  let K : ℝ := 1+∑ T : Finset α, Cs T ^ Fintype.card T
  have hCs0 (T : Finset α) : 0 ≤ Cs T := zero_le_one.trans (hCs T)
  have hK : 0 < K := by
    have hh := Finset.sum_nonneg (fun T (_ : T ∈ (Finset.univ : Finset (Finset α))) =>
      pow_nonneg (hCs0 T) (Fintype.card T))
    dsimp [K]; linarith
  have hCT (T : Finset α) : Cs T ^ Fintype.card T ≤ K := by
    have hh := Finset.single_le_sum (fun T (_ : T ∈ (Finset.univ : Finset (Finset α))) =>
      pow_nonneg (hCs0 T) (Fintype.card T)) (Finset.mem_univ T)
    dsimp [K]; linarith
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQR hQ0 hQt hQ72
  obtain ⟨C₀,C₁,hC₀,_,hz⟩ := hinc η₀ Q hQR hQ0 hQt hQ72
  refine ⟨K*C₀,mul_pos hK hC₀,?_⟩
  have hanchor := fixed_anchor_width_uniform η Mmin (ε/(2*Mmax)) hMmin (by positivity)
  filter_upwards [hz,hanchor] with Z hz hanchor
  refine ⟨hz.1,?_⟩
  intro label T θ w σ v t height hw hwm hσlo hσhi hheight width hwidth hwidthmax
    Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have hwidth0 : 0 ≤ width := hMmin.le.trans hwidth
  let s := fixedParentState (η label) (internalQ Q η₀) Φ bΦ Z width hz.1 hwidth0 hΦ hΦpos
  have hlog : Real.logb Z ((η label).modulus.absNorm : ℝ) ≤ ε/2 := by
    apply (hanchor.2 label width hwidth).trans
    apply (mul_le_mul_of_nonneg_left hwidthmax (by positivity : 0 ≤ ε/(2*Mmax))).trans_eq
    field_simp
  have hs : s.width ≤ Mmax+1 := by
    dsimp only [s,fixedParentState_width]
    linarith
  have hh := hcoarse T a b bΦ 0 (Mmax+1) (Mmax+1) (ε/2) Z η₀ Q degree S C₀ hC₀.le
    hz.2.1 Finset.univ θ w σ v t height hw hwm hσlo hσhi hheight s rfl hs
    p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  have henergy : energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i : (Finset.univ : Finset T) => primePool R H bslot (Z^(w i)))
      (fun (i : (Finset.univ : Finset T)) I =>
        idealCoeff (relativeCharacter R H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i : (Finset.univ : Finset T) => Z^(w i)) X₁ X₂ s.radial.keep
        s.radial.profile s.radial.scale =
      initialEnergy R H hH W bslot Z width (η label) η₀ Q T θ w σ v t X₁ X₂
        (p.profile 0) (p.profile 1) Φ := by
    have hp : (∏ i : (Finset.univ : Finset T), Z^(w i)) = ∏ i : T, Z^(w i) :=
      Finset.prod_coe_sort Finset.univ (fun i : T => Z^(w i))
    have hr (z : O) :
        (∏ i : (Finset.univ : Finset T), CenteredMomentHeckeSlots.rowSlot
          s.character s.mask 1 z (primePool R H bslot (Z^(w i)))
          (fun I => idealCoeff (relativeCharacter R H hH η₀ (θ i)) I *
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) =
        ∏ i : T, CenteredMomentHeckeSlots.rowSlot
          s.character s.mask 1 z (primePool R H bslot (Z^(w i)))
          (fun I => idealCoeff (relativeCharacter R H hH η₀ (θ i)) I *
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t :=
      Finset.prod_coe_sort Finset.univ (fun i : T => CenteredMomentHeckeSlots.rowSlot
          s.character s.mask 1 z (primePool R H bslot (Z^(w i)))
          (fun I => idealCoeff (relativeCharacter R H hH η₀ (θ i)) I *
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t)
    simp only [energy,positiveSlotRow,hp,hr,initialEnergy]
    rfl
  rw [henergy] at hh
  have hcard : (Fintype.card T : ℝ) ≤ Fintype.card α := by
    exact_mod_cast (show Fintype.card T ≤ Fintype.card α by
      simpa using Finset.card_le_univ T)
  have he : s.width+ε/2+2*(Fintype.card T : ℝ)*mesh ≤
      width+(ε+2*(Fintype.card α : ℝ)*mesh) := by
    have hc := mul_le_mul_of_nonneg_right hcard hmesh
    change width + Real.logb Z ((η label).modulus.absNorm : ℝ) + ε/2 +
      2*(Fintype.card T : ℝ)*mesh ≤ _
    linarith
  have hd := diagonalControl_nonneg Φ
  have hZp : 0 < Z := zero_lt_one.trans hz.1
  apply hh.trans
  change (Cs T ^ Fintype.card T * C₀)*diagonalControl Φ*(p.control S)^2*
      (1+|t|+height)^degree*Z^(s.width+ε/2+2*(Fintype.card T : ℝ)*mesh) ≤ _
  have hcp := hCT T
  have hzp := Real.rpow_le_rpow_of_exponent_le hz.1.le he
  gcongr

#print axioms original_initial_coarse
end
end OAI.SevenEighths.Cycle61Physical

end
/- END ORIGINAL Cycle61.Physical.InitialCoarse -/
