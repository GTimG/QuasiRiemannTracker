/-
Copyright (c) 2026 Hailey Collet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Candidate.LocalMoment.RestrictedIncumbent
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.Counting

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Physical
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily HeckePrimeRay HeckePrimeAnnular HeckeDyadic
open CenteredMomentRetainedEnergy
open CenteredMomentCounting CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentSecondHeightFamily CenteredMomentHeckeSlots
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open CenteredMomentDetectorDictionary CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ)

omit [NeZero M] in
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

omit [NeZero M] in
/-- The natural masked relative coefficient is transported exactly; the
omit [NeZero M] in
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

end
end OAI.SevenEighths.Cycle63Physical
