/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.SelectedReflection

/-! Whole-operator assembly for the selected squarefree sextic norm.
All analytic kernels are the actual pair kernels; every scalar budget below
is explicit in descendant selected norms and the proved Schwartz tail. -/
namespace Qrh.JointDetector
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic ActualEisensteinCoordinates
open CanonicalRowCompletion CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss
open ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson QuadraticAllOddCRT
local notation "O" => ActualEisensteinCubic.O

def supportedPairSummand (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (L : ℝ) (H : Ideal O) : ℂ :=
  if Supported H then
    (idealRowHom (primaryGenerator I) H * star (idealRowHom (primaryGenerator J) H)) *
      W ((Ideal.absNorm H : ℝ)/L) else 0

theorem supportedPairSummand_summable (I J : Ideal O)
    (W : 𝓢(ℝ, ℂ)) (L : ℝ) (hL : 0 < L) :
    Summable (supportedPairSummand I J W L) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (supported_radial_norm_summable W L hL)
  intro H
  by_cases hH : Supported H
  · simp only [supportedPairSummand, hH, ite_true, norm_mul, norm_star]
    have hh : ‖idealRowHom (primaryGenerator I) H‖ * ‖idealRowHom (primaryGenerator J) H‖ ≤ 1 :=
      (mul_le_mul (idealRowHom_norm _ _) (idealRowHom_norm _ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hh (norm_nonneg (W _))
  · simp only [supportedPairSummand, hH, ite_false, norm_zero, le_refl]

def supportedSmoothGram (F : Finset (Ideal O)) (a : F → ℂ) (L : ℝ) : ℝ :=
  ∑' H : Ideal O, if Supported H then
    QuadraticInitialBound.sieveBump ((Ideal.absNorm H : ℝ)/L) *
      ‖∑ I : F, idealRowHom (primaryGenerator I.val) H * a I‖^2 else 0

theorem supportedSmoothGram_summable (F : Finset (Ideal O)) (a : F → ℂ)
    (L : ℝ) (hL : 0 < L) : Summable (fun H : Ideal O => if Supported H then
    QuadraticInitialBound.sieveBump ((Ideal.absNorm H : ℝ)/L) *
      ‖∑ I : F, idealRowHom (primaryGenerator I.val) H * a I‖^2 else 0) := by
  let M : ℝ := (∑ I : F, ‖a I‖)^2
  have hM : 0 ≤ M := sq_nonneg _
  apply Summable.of_nonneg_of_le (fun H => by split_ifs; exact mul_nonneg QuadraticInitialBound.sieveBump.nonneg (sq_nonneg _); exact le_rfl) _
    ((supported_radial_norm_summable QuadraticInitialBound.sieveCutoff L hL).mul_left M)
  intro H
  by_cases hH : Supported H
  · simp only [hH, ite_true, QuadraticInitialBound.sieveCutoff_apply, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg QuadraticInitialBound.sieveBump.nonneg]
    have hh : ‖∑ I : F, idealRowHom (primaryGenerator I.val) H * a I‖ ≤ ∑ I : F, ‖a I‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro I hI
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (idealRowHom_norm _ _)
    have hs := pow_le_pow_left₀ (norm_nonneg _) hh 2
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hs QuadraticInitialBound.sieveBump.nonneg
  · simp only [hH, ite_false, mul_zero, le_refl]

theorem supportedSmoothGram_nonneg (F : Finset (Ideal O)) (a : F → ℂ) (L : ℝ) :
    0 ≤ supportedSmoothGram F a L :=
  tsum_nonneg fun H => by split_ifs; exact mul_nonneg QuadraticInitialBound.sieveBump.nonneg (sq_nonneg _); exact le_rfl

/-- The positive smooth Gram is exactly the sum of the actual ordinary-ideal
pair kernels. No signed diagonal is subtracted. -/
theorem supportedSmoothGram_eq_pairs (F : Finset (Ideal O)) (a : F → ℂ)
    (L : ℝ) (hL : 0 < L) :
    (supportedSmoothGram F a L : ℂ) =
      ∑ I : F, ∑ J : F, a I * star (a J) *
        selectedSupportedPairSource I.val J.val QuadraticInitialBound.sieveCutoff L := by
  let W := QuadraticInitialBound.sieveCutoff
  let f := fun (I J : F) (H : Ideal O) =>
    a I * star (a J) * supportedPairSummand I.val J.val W L H
  have hf (I J : F) : Summable (f I J) :=
    (supportedPairSummand_summable I.val J.val W L hL).mul_left _
  have he (H : Ideal O) :
      ((if Supported H then QuadraticInitialBound.sieveBump ((Ideal.absNorm H : ℝ)/L) *
        ‖∑ I : F, idealRowHom (primaryGenerator I.val) H * a I‖^2 else 0 : ℝ) : ℂ) =
      ∑ I : F, ∑ J : F, f I J H := by
    by_cases hH : Supported H
    · simp only [hH, ite_true, Complex.ofReal_mul]
      rw [CoprimeSieveOperator.square_norm_sum, Finset.sum_comm]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro J hJ
      simp only [f, supportedPairSummand, hH, ite_true, W,
        QuadraticInitialBound.sieveCutoff_apply, star_mul]
      ring
    · simp only [hH, ite_false, Complex.ofReal_zero, f, supportedPairSummand,
        mul_zero, Finset.sum_const_zero]
  unfold supportedSmoothGram
  rw [Complex.ofReal_tsum, tsum_congr he,
    Summable.tsum_finsetSum (fun I hI => summable_sum fun J hJ => hf I J)]
  apply Finset.sum_congr rfl
  intro I hI
  rw [Summable.tsum_finsetSum (fun J hJ => hf I J)]
  apply Finset.sum_congr rfl
  intro J hJ
  exact tsum_mul_left

/-- An arbitrary finite supported source selection lies below the positive
whole-source Gram, provided its ordinary ideal norms are at most L. -/
theorem supported_energy_le_smoothGram (F S : Finset (Ideal O)) (a : F → ℂ)
    (L : ℝ) (hL : 0 < L) (hS : ∀ H ∈ S, Supported H)
    (hN : ∀ H ∈ S, (Ideal.absNorm H : ℝ) ≤ L) :
    (∑ H : S, ‖∑ I : F, idealRowHom (primaryGenerator I.val) H.val * a I‖^2) ≤
      supportedSmoothGram F a L := by
  rw [Finset.sum_coe_sort S (fun H => ‖∑ I : F, idealRowHom (primaryGenerator I.val) H * a I‖^2)]
  calc
    _ = ∑ H ∈ S, if Supported H then
        QuadraticInitialBound.sieveBump ((Ideal.absNorm H : ℝ)/L) *
          ‖∑ I : F, idealRowHom (primaryGenerator I.val) H * a I‖^2 else 0 := by
      apply Finset.sum_congr rfl
      intro H hH
      rw [ite_eq_left (hS H hH), QuadraticInitialBound.sieveBump_eq_one
        (div_nonneg (Nat.cast_nonneg _) hL.le) ((div_le_one hL).mpr (hN H hH)), one_mul]
    _ ≤ _ := (supportedSmoothGram_summable F a L hL).sum_le_tsum S
      (fun H hH => by split_ifs; exact mul_nonneg QuadraticInitialBound.sieveBump.nonneg (sq_nonneg _); exact le_rfl)


def selectedRightRayPhase (z : O) : ℂ :=
  MixedCrossSeparation.quadraticRayPair (residue z) (residue z)

theorem selectedRightRayPhase_norm (z : O) (hz : Supported (Ideal.span {z})) :
    ‖selectedRightRayPhase z‖ = 1 := by
  unfold selectedRightRayPhase
  rw [quadraticRayPair_eq_sign _ _ (supported_residue_odd z hz) (supported_residue_odd z hz)]
  unfold quadraticRaySign
  rw [ite_eq_left ⟨supported_residue_odd z hz, supported_residue_odd z hz⟩]
  split_ifs <;> norm_num

def reflectionCutoff (T : ℝ) : Finset O := insert 0 (rowNormDisk ⌊T⌋₊)

def reflectionFrequencies (T : ℝ) : Finset BadFrequencySectors.NonzeroFrequency :=
  (rowNormDisk ⌊T⌋₊).attach.image (fun h =>
    ⟨h.val, fun hz => by have hp := (mem_rowNormDisk.mp h.property).1; simp [hz] at hp⟩)

theorem reflectionFrequencies_bound (T : ℝ) (hT : 0 ≤ T)
    (h : BadFrequencySectors.NonzeroFrequency) (hh : h ∈ reflectionFrequencies T) :
    ‖eisEmbedding h.val‖^2 ≤ T := by
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hh
  exact (TruncatedPrincipalPoisson.mem_rowNormDisk_floor hT z.val).mp z.property |>.2

theorem reflectionCutoff_tail (T : ℝ) (hT : 0 ≤ T) (h : O) (hh : h ∉ reflectionCutoff T) :
    T ≤ ‖eisEmbedding h‖^2 := by
  have hn : h ≠ 0 ∧ h ∉ rowNormDisk ⌊T⌋₊ := by
    simpa only [reflectionCutoff, Finset.mem_insert, not_or] using hh
  exact (lt_of_not_ge fun hle => hn.2
    ((TruncatedPrincipalPoisson.mem_rowNormDisk_floor hT h).mpr ⟨hn.1, hle⟩)).le

theorem reflectionCutoff_sum (T : ℝ) (f : O → ℂ) :
    (∑ h ∈ reflectionCutoff T, f h) = f 0 + ∑ h ∈ reflectionFrequencies T, f h.val := by
  have hn : (0 : O) ∉ rowNormDisk ⌊T⌋₊ := by simp only [mem_rowNormDisk]; simp
  rw [reflectionCutoff, Finset.sum_insert hn]
  congr 1
  unfold reflectionFrequencies
  rw [Finset.sum_image]
  · exact (Finset.sum_attach _ _).symm
  · intro x hx y hy he
    exact Subtype.ext (congrArg (fun h : BadFrequencySectors.NonzeroFrequency => h.val) he)

theorem selectedRawPhysicalPairKernel_summable
    (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (W : 𝓢(ℝ, ℂ)) (L : ℝ) (hL : 0 < L) (d : O) (hd : d ≠ 0)
    (r s : O) (hr : 0 < (Ideal.absNorm (Ideal.span {r}) : ℝ))
    (hs : 0 < (Ideal.absNorm (Ideal.span {s}) : ℝ)) :
    Summable (fun h => selectedRawPhysicalPairKernel F hF W L d h r s) := by
  let K := L / (‖eisEmbedding d‖^2 *
    ((Ideal.absNorm (Ideal.span {r}) : ℝ)*(Ideal.absNorm (Ideal.span {s}) : ℝ)))
  have hdN : 0 < ‖eisEmbedding d‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd))
  have hK : 0 < K := by dsimp [K]; positivity
  have ht : Summable (fun h : O => star (primitivePair (Ideal.span {r}) (Ideal.span {s}) h) *
      paperRadialFourier W (K*‖eisEmbedding h‖^2)) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
      (paperRadialFourier_lattice_summable_norm W K hK)
    intro h
    rw [norm_mul, norm_star]
    exact mul_le_of_le_one_left (norm_nonneg _) (primitivePair_norm_le _ _ _)
  have he (h : O) : selectedRawPhysicalPairKernel F hF W L d h r s =
      (((L / (‖eisEmbedding d‖^2 * Real.sqrt
        ((Ideal.absNorm (Ideal.span {r}) : ℝ)*(Ideal.absNorm (Ideal.span {s}) : ℝ)))) : ℝ) *
        admissibleUnaryGauss F hF (Ideal.span {r}) 1 *
        admissibleUnaryGauss F hF (Ideal.span {s}) 5 * primitivePair (Ideal.span {r}) (Ideal.span {s}) d) *
      (star (primitivePair (Ideal.span {r}) (Ideal.span {s}) h) *
        paperRadialFourier W (K*‖eisEmbedding h‖^2)) := by
    have ha : L * ‖eisEmbedding h‖^2 /
        (‖eisEmbedding d‖^2 *((Ideal.absNorm (Ideal.span {r}) : ℝ)*(Ideal.absNorm (Ideal.span {s}) : ℝ))) =
        K*‖eisEmbedding h‖^2 := by dsimp [K]; ring
    unfold selectedRawPhysicalPairKernel
    rw [ha]
    ring
  exact (ht.mul_left _).congr (fun h => (he h).symm)

/-- One actual source-mask mode, with the original ray phase absorbed only
into the second row vector. -/
def selectedFullMode (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (rows : Finset O) (a : rows → ℂ) (W : 𝓢(ℝ, ℂ)) (L : ℝ) (d : O) : ℂ :=
  ∑ r : rows, ∑ s : rows,
    if IsCoprime (Ideal.span {r.val}) (Ideal.span {s.val}) then
      a r * star (a s) * selectedRightRayPhase s.val *
        ∑' h : O, selectedRawPhysicalPairKernel F hF W L d h r.val s.val else 0

def selectedModeZero (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (rows : Finset O) (a : rows → ℂ) (W : 𝓢(ℝ, ℂ)) (L : ℝ) (d : O) : ℂ :=
  ∑ r : rows, ∑ s : rows,
    if IsCoprime (Ideal.span {r.val}) (Ideal.span {s.val}) then
      a r * star (a s) * selectedRightRayPhase s.val *
        selectedRawPhysicalPairKernel F hF W L d 0 r.val s.val else 0

def selectedModeTail (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (rows : Finset O) (a : rows → ℂ) (W : 𝓢(ℝ, ℂ)) (L T : ℝ) (d : O) : ℂ :=
  ∑ r : rows, ∑ s : rows,
    if IsCoprime (Ideal.span {r.val}) (Ideal.span {s.val}) then
      a r * star (a s) * selectedRightRayPhase s.val *
        ∑' h : {h : O // h ∉ reflectionCutoff T},
          selectedRawPhysicalPairKernel F hF W L d h.val r.val s.val else 0

theorem selectedFullMode_split (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (rows : Finset O) (a : rows → ℂ) (W : 𝓢(ℝ, ℂ)) (L T : ℝ) (hL : 0 < L)
    (d : O) (hd : d ≠ 0)
    (hrows : ∀ r : rows, 0 < (Ideal.absNorm (Ideal.span {r.val}) : ℝ)) :
    selectedFullMode F hF rows a W L d =
      selectedModeZero F hF rows a W L d +
        selectedRawCoprimePacket F hF rows (reflectionFrequencies T)
          a (fun r => star (a r) * selectedRightRayPhase r.val) (fun _ => 1) W L d +
        selectedModeTail F hF rows a W L T d := by
  have he (r s : rows) :=
    (selectedRawPhysicalPairKernel_summable F hF W L hL d hd r.val s.val (hrows r) (hrows s)).sum_add_tsum_subtype_compl
      (reflectionCutoff T)
  have hn : selectedRawCoprimePacket F hF rows (reflectionFrequencies T)
      a (fun r => star (a r) * selectedRightRayPhase r.val) (fun _ => 1) W L d =
      ∑ r : rows, ∑ s : rows,
        if IsCoprime (Ideal.span {r.val}) (Ideal.span {s.val}) then
          a r * star (a s) * selectedRightRayPhase s.val *
            ∑ h ∈ reflectionFrequencies T, selectedRawPhysicalPairKernel F hF W L d h.val r.val s.val else 0 := by
    unfold selectedRawCoprimePacket
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    split_ifs with hc
    · simp only [hc, ite_true, one_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      ring
    · simp only [hc, ite_false, Finset.sum_const_zero]
  rw [hn]
  unfold selectedFullMode selectedModeZero selectedModeTail
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  split_ifs with hc
  · rw [← he r s, reflectionCutoff_sum]
    ring
  · ring


theorem selectedRawPhysicalPairKernel_norm_le
    (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (W : 𝓢(ℝ, ℂ)) (L : ℝ) (hL : 0 ≤ L) (d h r s : O) :
    ‖selectedRawPhysicalPairKernel F hF W L d h r s‖ ≤
      (L / (‖eisEmbedding d‖^2 * Real.sqrt
        ((Ideal.absNorm (Ideal.span {r}) : ℝ)*(Ideal.absNorm (Ideal.span {s}) : ℝ)))) *
      ‖paperRadialFourier W (L*‖eisEmbedding h‖^2 /
        (‖eisEmbedding d‖^2 *((Ideal.absNorm (Ideal.span {r}) : ℝ)*(Ideal.absNorm (Ideal.span {s}) : ℝ))))‖ := by
  unfold selectedRawPhysicalPairKernel
  simp only [norm_mul, norm_star, admissibleUnaryGauss_norm F hF _ 1 (by decide) (by decide),
    admissibleUnaryGauss_norm F hF _ 5 (by decide) (by decide), one_mul,
    Complex.norm_real, Real.norm_eq_abs]
  have hpref : 0 ≤ L / (‖eisEmbedding d‖^2 * Real.sqrt
      ((Ideal.absNorm (Ideal.span {r}) : ℝ)*(Ideal.absNorm (Ideal.span {s}) : ℝ))) :=
    div_nonneg hL (by positivity)
  rw [abs_of_nonneg hpref]
  have hp : ‖primitivePair (Ideal.span {r}) (Ideal.span {s}) d‖ *
      ‖primitivePair (Ideal.span {r}) (Ideal.span {s}) h‖ ≤ 1 := by
    exact (mul_le_mul (primitivePair_norm_le _ _ _) (primitivePair_norm_le _ _ _)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right hpref hp) (norm_nonneg _)

theorem selectedRawPhysicalPairKernel_zero_offdiag
    (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (W : 𝓢(ℝ, ℂ)) (L : ℝ) (d r s : O)
    (hr : Ideal.span {r} ∈ F) (hs : Ideal.span {s} ∈ F)
    (hr0 : r ≠ 0) (hs0 : s ≠ 0) (hpr : lambda^2 ∣ r-1) (hps : lambda^2 ∣ s-1)
    (hne : r ≠ s) : selectedRawPhysicalPairKernel F hF W L d 0 r s = 0 := by
  have hneI : (Ideal.span {r} : Ideal O) ≠ Ideal.span {s} := by
    intro he
    apply hne
    rw [← primaryGenerator_span r hr0 hpr, ← primaryGenerator_span s hs0 hps, he]
  have hp : primitivePair (Ideal.span {r}) (Ideal.span {s}) 0 = 0 := by
    unfold primitivePair
    by_cases hi : (Ideal.span {r} : Ideal O) = 1
    · have hj : (Ideal.span {s} : Ideal O) ≠ 1 := fun hj => hneI (hi.trans hj.symm)
      rw [admissibleIdealRow_zero F hF _ hs hj, star_zero, mul_zero]
    · rw [admissibleIdealRow_zero F hF _ hr hi, zero_mul]
  unfold selectedRawPhysicalPairKernel
  rw [hp, star_zero, mul_zero, mul_zero, zero_mul]

/-- The zero mode has diagonal mass only. Its size is linear in the reduced
source length, uniformly in the selected row family. -/
theorem selectedModeZero_bound
    (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (rows : Finset O) (hrows : ∀ r : rows, Ideal.span {r.val} ∈ F)
    (hn : ∀ r : rows, r.val ≠ 0) (hp : ∀ r : rows, lambda^2 ∣ r.val-1)
    (a : rows → ℂ) (W : 𝓢(ℝ, ℂ)) (L : ℝ) (hL : 0 < L) (d : O) (hd : d ≠ 0) :
    ‖selectedModeZero F hF rows a W L d‖ ≤
      (L/‖eisEmbedding d‖^2) * ‖paperRadialFourier W 0‖ * ∑ r, ‖a r‖^2 := by
  have hdiag : selectedModeZero F hF rows a W L d =
      ∑ r : rows, if IsCoprime (Ideal.span {r.val}) (Ideal.span {r.val}) then
        a r * star (a r) * selectedRightRayPhase r.val *
          selectedRawPhysicalPairKernel F hF W L d 0 r.val r.val else 0 := by
    unfold selectedModeZero
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_eq_single r
    · intro s hs hsr
      have hneq : r.val ≠ s.val := fun he => hsr (Subtype.ext he.symm)
      rw [selectedRawPhysicalPairKernel_zero_offdiag F hF W L d r.val s.val
        (hrows r) (hrows s) (hn r) (hn s) (hp r) (hp s) hneq]
      split_ifs <;> simp
    · simp
  rw [hdiag]
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  split_ifs with hc
  · have hNr : 1 ≤ (Ideal.absNorm (Ideal.span {r.val}) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (hF _ (hrows r)).1)
    have hker := selectedRawPhysicalPairKernel_norm_le F hF W L hL.le d 0 r.val r.val
    simp only [map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div] at hker
    rw [← pow_two, Real.sqrt_sq (Nat.cast_nonneg _)] at hker
    have hdN : 0 < ‖eisEmbedding d‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd))
    have hpref : L/(‖eisEmbedding d‖^2 * (Ideal.absNorm (Ideal.span {r.val}) : ℝ)) ≤
        L/‖eisEmbedding d‖^2 :=
      div_le_div_of_nonneg_left hL.le hdN (le_mul_of_one_le_right hdN.le hNr)
    have hb := hker.trans (mul_le_mul_of_nonneg_right hpref (norm_nonneg _))
    rw [norm_mul, norm_mul, norm_mul, norm_star,
      selectedRightRayPhase_norm r.val (admissible_supported (hF _ (hrows r))), mul_one]
    have hh := mul_le_mul_of_nonneg_left hb (mul_nonneg (norm_nonneg (a r)) (norm_nonneg (a r)))
    simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc] using hh
  · simp only [norm_zero]
    positivity


def modeTailCost (rows : Finset O) (L B H C₀ : ℝ) (d : O) (A : ℕ) : ℝ :=
  ((L/‖eisEmbedding d‖^2)/B) * (rows.card : ℝ) * C₀ /
    ((min 1 ((L/‖eisEmbedding d‖^2)/(4*B^2)))^2 * (1+H)^A)

def modeFrequencyCutoff (L B H : ℝ) (d : O) : ℝ :=
  (4*B^2/(L/‖eisEmbedding d‖^2))*H

/-- The complete omitted raw-frequency tail, with the original coprime
selector and Gauss/ray phases kept inside its bounded coefficient. -/
theorem selectedModeTail_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
        (rows : Finset O) (hrows : ∀ r : rows, Ideal.span {r.val} ∈ F)
        (a : rows → ℂ) (W : 𝓢(ℝ, ℂ)) (L B H : ℝ) (d : O),
      0 < L → 0 < B → 0 ≤ H → d ≠ 0 →
      (∀ r : rows, (Ideal.absNorm (Ideal.span {r.val}) : ℝ) ∈ Set.Icc B (2*B)) →
      ‖selectedModeTail F hF rows a W L (modeFrequencyCutoff L B H d) d‖ ≤
        modeTailCost rows L B H (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) d A *
          ∑ r, ‖a r‖^2 := by
  obtain ⟨s, C, hC, ht⟩ := physical_pair_radial_tail A
  refine ⟨s, C, hC, ?_⟩
  intro F hF rows hrows a W L B H d hL hB hH hd hN
  let Ld := L/‖eisEmbedding d‖^2
  let T := modeFrequencyCutoff L B H d
  have hdN : 0 < ‖eisEmbedding d‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd))
  have hLd : 0 < Ld := div_pos hL hdN
  have hT : 0 ≤ T := by dsimp [T, modeFrequencyCutoff]; positivity
  let G : rows → rows → O → ℂ := fun r t h =>
    if IsCoprime (Ideal.span {r.val}) (Ideal.span {t.val}) then
      selectedRightRayPhase t.val * admissibleUnaryGauss F hF (Ideal.span {r.val}) 1 *
        admissibleUnaryGauss F hF (Ideal.span {t.val}) 5 *
        primitivePair (Ideal.span {r.val}) (Ideal.span {t.val}) d *
        star (primitivePair (Ideal.span {r.val}) (Ideal.span {t.val}) h) else 0
  have hG (r t : rows) (h : O) : ‖G r t h‖ ≤ 1 := by
    dsimp only [G]
    split_ifs
    · simp only [norm_mul, norm_star,
        selectedRightRayPhase_norm t.val (admissible_supported (hF _ (hrows t))),
        admissibleUnaryGauss_norm F hF _ 1 (by decide) (by decide),
        admissibleUnaryGauss_norm F hF _ 5 (by decide) (by decide), one_mul]
      exact (mul_le_mul (primitivePair_norm_le _ _ _) (primitivePair_norm_le _ _ _)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    · simp
  have hh := ht W {h : O | h ∉ reflectionCutoff T} B Ld H hB hLd hH
    (fun r : rows => (Ideal.absNorm (Ideal.span {r.val}) : ℝ))
    (fun r => (hN r).1) (fun r => (hN r).2)
    (fun h hh => reflectionCutoff_tail T hT h hh) G (fun r t h _ => hG r t h) a
  have he : selectedModeTail F hF rows a W L T d =
      ∑ r : rows, ∑ t : rows, (a r * star (a t)) *
        ∑' h : {h : O // h ∉ reflectionCutoff T},
          (((Ld/Real.sqrt ((Ideal.absNorm (Ideal.span {r.val}) : ℝ)*
            (Ideal.absNorm (Ideal.span {t.val}) : ℝ))) : ℝ) * G r t h.val) *
            paperRadialFourier W
              ((Ld/((Ideal.absNorm (Ideal.span {r.val}) : ℝ)*
                (Ideal.absNorm (Ideal.span {t.val}) : ℝ)))*‖eisEmbedding h.val‖^2) := by
    unfold selectedModeTail
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hc : IsCoprime (Ideal.span {r.val}) (Ideal.span {t.val})
    · rw [ite_eq_left hc]
      calc
        _ = (a r * star (a t)) * ∑' h : {h : O // h ∉ reflectionCutoff T},
            selectedRightRayPhase t.val * selectedRawPhysicalPairKernel F hF W L d h.val r.val t.val := by
          rw [tsum_mul_left]
          ring
        _ = _ := by
          congr 1
          apply tsum_congr
          intro h
          have ha : L * ‖eisEmbedding h.val‖^2 /
              (‖eisEmbedding d‖^2 *((Ideal.absNorm (Ideal.span {r.val}) : ℝ)*(Ideal.absNorm (Ideal.span {t.val}) : ℝ))) =
              (Ld/((Ideal.absNorm (Ideal.span {r.val}) : ℝ)*(Ideal.absNorm (Ideal.span {t.val}) : ℝ)))*‖eisEmbedding h.val‖^2 := by
            dsimp [Ld]; ring
          have hpref : L/(‖eisEmbedding d‖^2 * Real.sqrt
              ((Ideal.absNorm (Ideal.span {r.val}) : ℝ)*(Ideal.absNorm (Ideal.span {t.val}) : ℝ))) =
              Ld/Real.sqrt ((Ideal.absNorm (Ideal.span {r.val}) : ℝ)*(Ideal.absNorm (Ideal.span {t.val}) : ℝ)) := by
            dsimp [Ld]; ring
          unfold selectedRawPhysicalPairKernel
          rw [ha, hpref]
          dsimp only [G]
          rw [ite_eq_left hc]
          ring
    · simp only [hc, ite_false, G, mul_zero, zero_mul, tsum_zero]
  rw [he]
  convert hh using 1
  · rfl
  · simp only [Fintype.card_coe]
    dsimp [modeTailCost, Ld]
    ring


def modeNearCost (rows : Finset O) (L B H C : ℝ) (d : O) (ε : ℝ) (hε : 0 < ε) : ℝ :=
  let T := modeFrequencyCutoff L B H d
  ((BadFrequencySectors.boundedKeys T).card : ℝ) * (columnDyadicLength T + 1 : ℕ) *
    ((L/(‖eisEmbedding d‖^2*B))*C*
      selectedNorm rows (selectedFrequencyPool (reflectionFrequencies T) T) *
      (idealDivisorConstant ε hε*(2*B)^ε))

def modeBudget (rows : Finset O) (W : 𝓢(ℝ, ℂ))
    (L B H Cnear Ctail : ℝ) (d : O) (ε : ℝ) (hε : 0 < ε) (A : ℕ) : ℝ :=
  (L/‖eisEmbedding d‖^2)*‖paperRadialFourier W 0‖ +
    modeNearCost rows L B H Cnear d ε hε + modeTailCost rows L B H Ctail d A

/-- A COMPLETE reflected source-mask mode: zero, finite near frequencies and
infinite tail. Its budget is explicit and contains no analytic hypothesis. -/
theorem selectedFullMode_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ (Cnear Ctail : ℝ), 0 ≤ Cnear ∧ 0 ≤ Ctail ∧
      ∀ (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
        (rows : Finset O) (hrows : ∀ r : rows, Ideal.span {r.val} ∈ F)
        (hn : ∀ r : rows, r.val ≠ 0) (hp : ∀ r : rows, lambda^2 ∣ r.val-1)
        (hmod : ∀ r s : rows, r.val-s.val ∈ (Ideal.span {(36 : O)} : Ideal O))
        (a : rows → ℂ) (L B H : ℝ) (d : O) (ε : ℝ) (hε : 0 < ε),
      0 < L → 0 < B → 0 ≤ H → d ≠ 0 →
      (∀ r : rows, (Ideal.absNorm (Ideal.span {r.val}) : ℝ) ∈ Set.Icc B (2*B)) →
      ‖selectedFullMode F hF rows a W L d‖ ≤
        modeBudget rows W L B H Cnear Ctail d ε hε A * ∑ r, ‖a r‖^2 := by
  obtain ⟨Cnear, hCn, hnBound⟩ := selected_coprime_raw_finite_reflection W
  obtain ⟨s, C, hC, htBound⟩ := selectedModeTail_bound A
  let Ctail := C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  refine ⟨Cnear, Ctail, hCn, mul_nonneg hC.le (apply_nonneg _ _), ?_⟩
  intro F hF rows hrows hn hp hmod a L B H d ε hε hL hB hH hd hN
  let T := modeFrequencyCutoff L B H d
  have hdN : 0 < ‖eisEmbedding d‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd))
  have hT : 0 ≤ T := by dsimp [T, modeFrequencyCutoff]; positivity
  let c : rows → ℂ := fun r => star (a r)*selectedRightRayPhase r.val
  have hc : (∑ r, ‖c r‖^2) = ∑ r, ‖a r‖^2 := by
    apply Finset.sum_congr rfl
    intro r hr
    simp only [c, norm_mul, norm_star,
      selectedRightRayPhase_norm r.val (admissible_supported (hF _ (hrows r))), mul_one]
  have hnear := hnBound F hF rows (reflectionFrequencies T) hrows hn hp hmod a c
    (fun _ => 1) d hd L B T ε hL hB hε hN (reflectionFrequencies_bound T hT) (by simp)
  rw [hc] at hnear
  have hnCost : ‖selectedRawCoprimePacket F hF rows (reflectionFrequencies T) a c (fun _ => 1) W L d‖ ≤
      modeNearCost rows L B H Cnear d ε hε * ∑ r, ‖a r‖^2 := by
    apply hnear.trans_eq
    calc
      _ = modeNearCost rows L B H Cnear d ε hε *
          (Real.sqrt (∑ r, ‖a r‖^2)*Real.sqrt (∑ r, ‖a r‖^2)) := by
        dsimp [modeNearCost, T]
        ring
      _ = _ := by rw [Real.mul_self_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  have hz := selectedModeZero_bound F hF rows hrows hn hp a W L hL d hd
  have ht := htBound F hF rows hrows a W L B H d hL hB hH hd hN
  rw [selectedFullMode_split F hF rows a W L T hL d hd
    (fun r => hB.trans_le (hN r).1)]
  calc
    _ ≤ ‖selectedModeZero F hF rows a W L d‖ +
        ‖selectedRawCoprimePacket F hF rows (reflectionFrequencies T) a c (fun _ => 1) W L d‖ +
        ‖selectedModeTail F hF rows a W L T d‖ := (norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by
      have hh := add_le_add (add_le_add hz hnCost) ht
      simpa only [modeBudget, add_mul, Ctail] using hh


def originalGcdBlock (F : Finset (Ideal O)) (a : Ideal O → ℂ)
    (W : 𝓢(ℝ, ℂ)) (L : ℝ) (D : Ideal O) : ℂ :=
  ∑ I ∈ F, ∑ J ∈ F, if gcd I J = D then
    a I * star (a J) * selectedSupportedPairSource I J W L else 0

theorem supportedSmoothGram_eq_gcd (F : Finset (Ideal O)) (a : Ideal O → ℂ)
    (L : ℝ) (hL : 0 < L) :
    (supportedSmoothGram F (fun I => a I.val) L : ℂ) =
      ∑ D ∈ gcdPool (fun I : F => I.val),
        originalGcdBlock F a QuadraticInitialBound.sieveCutoff L D := by
  rw [supportedSmoothGram_eq_pairs F (fun I => a I.val) L hL]
  unfold originalGcdBlock
  simp_rw [← Finset.sum_coe_sort F]
  conv_rhs => rw [Finset.sum_comm]; arg 2; ext I; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  symm
  rw [Finset.sum_eq_single (gcd I.val J.val)]
  · simp
  · intro D hD hn
    exact ite_eq_right (Ne.symm hn)
  · exact fun hn => (hn (mem_gcdPool (fun I : F => I.val) I J)).elim

/-- Exact transport of a signed gcd-selected pair form to primary quotient
rows. The kernel is arbitrary, so this also transports the complete Poisson
sum before any estimate or truncation is applied. -/
theorem gcd_quotient_pair_transport (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (D : Ideal O) (hD : D ≠ 0)
    (a : Ideal O → ℂ) (K : Ideal O → Ideal O → ℂ) :
    (∑ I ∈ F, ∑ J ∈ F, if gcd I J = D then
      a I * star (a J) * K (idealQuotient D I) (idealQuotient D J) else 0) =
      ∑ r : selectedQuotientRows F D, ∑ s : selectedQuotientRows F D,
        if IsCoprime (Ideal.span {r.val}) (Ideal.span {s.val}) then
          selectedDescendantCoefficient F hF D (fun I => a I.val) r *
            star (selectedDescendantCoefficient F hF D (fun I => a I.val) s) *
            K (Ideal.span {r.val}) (Ideal.span {s.val}) else 0 := by
  let E := selectedQuotientEquiv F hF D
  let f := fun r s : selectedQuotientRows F D =>
    if IsCoprime (Ideal.span {r.val}) (Ideal.span {s.val}) then
      selectedDescendantCoefficient F hF D (fun I => a I.val) r *
        star (selectedDescendantCoefficient F hF D (fun I => a I.val) s) *
        K (Ideal.span {r.val}) (Ideal.span {s.val}) else 0
  have hcoef (I : F.filter fun I => D ∣ I) :
      selectedDescendantCoefficient F hF D (fun I => a I.val) (E I) = a I.val := by
    change a (E.symm (E I)).val = a I.val
    rw [E.symm_apply_apply]
  have hspan (I : F.filter fun I => D ∣ I) :
      (Ideal.span {(E I).val} : Ideal O) = idealQuotient D I.val := by
    change Ideal.span {primaryGenerator (idealQuotient D I.val)} = _
    exact (primaryGenerator_spec _ (primaryGenerator_admissible _
      (admissible_idealQuotient (hF I.val (Finset.mem_filter.mp I.property).1)
        (Finset.mem_filter.mp I.property).2))).1
  have hre : (∑ r, ∑ s, f r s) =
      ∑ I : F.filter fun I => D ∣ I, ∑ J : F.filter fun I => D ∣ I, f (E I) (E J) := by
    rw [← E.sum_comp (fun r => ∑ s, f r s)]
    apply Finset.sum_congr rfl
    intro I hI
    exact (E.sum_comp (f (E I))).symm
  change _ = ∑ r, ∑ s, f r s
  rw [hre]
  simp only [f, hcoef, hspan]
  conv_rhs =>
    arg 2
    ext I
    rw [Finset.sum_coe_sort (F.filter fun I => D ∣ I) (fun J =>
      if IsCoprime (idealQuotient D I.val) (idealQuotient D J) then
        a I.val * star (a J) * K (idealQuotient D I.val) (idealQuotient D J) else 0)]
  rw [Finset.sum_coe_sort (F.filter fun I => D ∣ I) (fun I =>
    ∑ J ∈ F.filter (fun J => D ∣ J), if IsCoprime (idealQuotient D I) (idealQuotient D J) then
      a I * star (a J) * K (idealQuotient D I) (idealQuotient D J) else 0)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hi : D ∣ I
  · rw [ite_eq_left hi, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro J hJ
    by_cases hj : D ∣ J
    · rw [ite_eq_left hj, ← gcd_eq_iff_quotient_coprime D I J hD hi hj]
      rfl
    · have hg : gcd I J ≠ D := fun he => hj (he ▸ gcd_dvd_right I J)
      simp only [hg, hj, ite_false]
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro J hJ
    have hg : gcd I J ≠ D := fun he => hi (he ▸ gcd_dvd_left I J)
    exact ite_eq_right hg

def descendantIdealFamily (F : Finset (Ideal O)) (D : Ideal O) : Finset (Ideal O) :=
  (selectedQuotientRows F D).image (fun z => Ideal.span {z})

theorem descendantIdealFamily_admissible (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (D : Ideal O) :
    ∀ I ∈ descendantIdealFamily F D, Admissible I := by
  intro I hI
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
  exact (selectedQuotientRows_spec F hF D ⟨z,hz⟩).2.2

theorem quotient_mem_descendantIdealFamily (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (D I : Ideal O) (hI : I ∈ F) (hDI : D ∣ I) :
    idealQuotient D I ∈ descendantIdealFamily F D := by
  have hq := admissible_idealQuotient (hF I hI) hDI
  exact Finset.mem_image.mpr ⟨primaryGenerator (idealQuotient D I),
    Finset.mem_image.mpr ⟨I, Finset.mem_filter.mpr ⟨hI,hDI⟩,rfl⟩,
    (primaryGenerator_spec _ (primaryGenerator_admissible _ hq)).1⟩


def reflectedModePair (G : Finset (Ideal O)) (hG : ∀ I ∈ G, Admissible I)
    (W : 𝓢(ℝ, ℂ)) (L : ℝ) (d : O) (I J : Ideal O) : ℂ :=
  selectedRightRayPhase (primaryGenerator J) *
    ∑' h : O, selectedRawPhysicalPairKernel G hG W L d h (primaryGenerator I) (primaryGenerator J)

/-- The full actual pair Poisson identity in the normalization consumed by
`selectedFullMode_bound`, including the original source mask and all modes. -/
theorem supportedPair_eq_reflectedModes
    (G : Finset (Ideal O)) (hG : ∀ I ∈ G, Admissible I)
    (D I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hgcd : gcd I J = D)
    (hiG : idealQuotient D I ∈ G) (hjG : idealQuotient D J ∈ G)
    (hmod : primaryGenerator I-primaryGenerator J ∈ (Ideal.span {(36 : O)} : Ideal O))
    (W : 𝓢(ℝ, ℂ)) (L : ℝ) (hL : 0 < L) :
    selectedSupportedPairSource I J W L = (6 : ℂ)⁻¹ *
      ∑ e ∈ idealDivisors (commonMaskIdeal D), (UniqueFactorizationMonoid.moebius e : ℂ) *
        reflectedModePair G hG W L (idealGenerator e) (idealQuotient D I) (idealQuotient D J) := by
  have hi : D ∣ I := hgcd ▸ gcd_dvd_left I J
  have hj : D ∣ J := hgcd ▸ gcd_dvd_right I J
  have hD := admissible_of_dvd hI hi
  have hqi := admissible_idealQuotient hI hi
  have hqj := admissible_idealQuotient hJ hj
  have hspi := (primaryGenerator_spec _ (primaryGenerator_admissible _ hqi)).1
  have hspj := (primaryGenerator_spec _ (primaryGenerator_admissible _ hqj)).1
  have hp := admissible_shared_masked_pair_poisson D hD G hG
    (idealQuotient D I) (idealQuotient D J) hiG hjG
    ((gcd_eq_iff_quotient_coprime D I J hD.1 hi hj).mp hgcd)
    (primaryQuotient_congruent_mod36 D I J hI hi hj hmod)
    (residue (primaryGenerator (idealQuotient D J))) rfl W L hL
  rw [idealQuotient_mul hi, idealQuotient_mul hj] at hp
  rw [selectedSupportedPairSource_eq_element I J hI hJ hmod W L hL, hp,
    maskedPairDual_eq_idealDivisors, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  unfold reflectedModePair selectedRightRayPhase
  have hk (h : O) : selectedRawPhysicalPairKernel G hG W L (idealGenerator e) h
      (primaryGenerator (idealQuotient D I)) (primaryGenerator (idealQuotient D J)) =
      (((L : ℂ)/((Ideal.absNorm e : ℂ) *
        (Real.sqrt ((Ideal.absNorm (idealQuotient D I) : ℝ)*(Ideal.absNorm (idealQuotient D J) : ℝ)) : ℂ))) *
        admissibleUnaryGauss G hG (idealQuotient D I) 1 *
        admissibleUnaryGauss G hG (idealQuotient D J) 5 *
        primitivePair (idealQuotient D I) (idealQuotient D J) (idealGenerator e)) *
      (star (primitivePair (idealQuotient D I) (idealQuotient D J) h) *
        paperRadialFourier W (L*‖eisEmbedding h‖^2 /
          ((Ideal.absNorm e : ℝ)*((Ideal.absNorm (idealQuotient D I) : ℝ)*
            (Ideal.absNorm (idealQuotient D J) : ℝ))))) := by
    unfold selectedRawPhysicalPairKernel
    rw [hspi, hspj, idealGenerator_norm_sq]
    push_cast
    ring
  simp_rw [hk]
  rw [tsum_mul_left]
  ring

theorem originalGcdBlock_eq_modes (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (D : Ideal O) (hD : D ≠ 0)
    (hmod : ∀ I ∈ F, ∀ J ∈ F, primaryGenerator I-primaryGenerator J ∈
      (Ideal.span {(36 : O)} : Ideal O))
    (a : Ideal O → ℂ) (W : 𝓢(ℝ, ℂ)) (L : ℝ) (hL : 0 < L) :
    originalGcdBlock F a W L D = (6 : ℂ)⁻¹ *
      ∑ e ∈ idealDivisors (commonMaskIdeal D), (UniqueFactorizationMonoid.moebius e : ℂ) *
        selectedFullMode (descendantIdealFamily F D) (descendantIdealFamily_admissible F hF D)
          (selectedQuotientRows F D) (selectedDescendantCoefficient F hF D (fun I => a I.val)) W L (idealGenerator e) := by
  let G := descendantIdealFamily F D
  let hG := descendantIdealFamily_admissible F hF D
  let K := fun e => reflectedModePair G hG W L (idealGenerator e)
  have hp (I : Ideal O) (hi : I ∈ F) (J : Ideal O) (hj : J ∈ F) :
      (if gcd I J = D then a I * star (a J) * selectedSupportedPairSource I J W L else 0) =
      (6 : ℂ)⁻¹ * ∑ e ∈ idealDivisors (commonMaskIdeal D), (UniqueFactorizationMonoid.moebius e : ℂ) *
        (if gcd I J = D then a I * star (a J) * K e (idealQuotient D I) (idealQuotient D J) else 0) := by
    by_cases hg : gcd I J = D
    · rw [ite_eq_left hg, supportedPair_eq_reflectedModes G hG D I J (hF I hi) (hF J hj) hg
        (quotient_mem_descendantIdealFamily F hF D I hi (hg ▸ gcd_dvd_left I J))
        (quotient_mem_descendantIdealFamily F hF D J hj (hg ▸ gcd_dvd_right I J))
        (hmod I hi J hj) W L hL]
      simp only [hg, ite_true, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      dsimp only [K]
      ring
    · simp only [hg, ite_false, mul_zero, Finset.sum_const_zero]
  have he : originalGcdBlock F a W L D = (6 : ℂ)⁻¹ *
      ∑ e ∈ idealDivisors (commonMaskIdeal D), (UniqueFactorizationMonoid.moebius e : ℂ) *
        ∑ I ∈ F, ∑ J ∈ F, if gcd I J = D then
          a I * star (a J) * K e (idealQuotient D I) (idealQuotient D J) else 0 := by
    unfold originalGcdBlock
    simp_rw [Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]; arg 2; ext I; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro I hi
    apply Finset.sum_congr rfl
    intro J hj
    simpa only [Finset.mul_sum, mul_assoc] using hp I hi J hj
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  rw [gcd_quotient_pair_transport F hF D hD a (K e)]
  congr 1
  unfold selectedFullMode
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hc : IsCoprime (Ideal.span {r.val}) (Ideal.span {s.val})
  · rw [ite_eq_left hc, ite_eq_left hc]
    unfold K reflectedModePair
    rw [primaryGenerator_span r.val (selectedQuotientRows_spec F hF D r).1
        (selectedQuotientRows_spec F hF D r).2.1,
      primaryGenerator_span s.val (selectedQuotientRows_spec F hF D s).1
        (selectedQuotientRows_spec F hF D s).2.1]
    ring
  · simp only [hc, ite_false]


/-- Divisors arising as gcds remain admissible and below the original row height. -/
theorem selectedGcd_spec (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (B : ℝ) (hN : ∀ I ∈ F, (Ideal.absNorm I : ℝ) ≤ B)
    (D : Ideal O) (hD : D ∈ gcdPool (fun I : F => I.val)) :
    Admissible D ∧ (Ideal.absNorm D : ℝ) ≤ B := by
  obtain ⟨⟨I,J⟩, _, rfl⟩ := Finset.mem_image.mp hD
  refine ⟨admissible_of_dvd (hF I.val I.property) (gcd_dvd_left _ _), ?_⟩
  apply le_trans _ (hN I.val I.property)
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (fun h => (hF I.val I.property).1 (Ideal.absNorm_eq_zero_iff.mp h)))
    (map_dvd Ideal.absNorm (gcd_dvd_left I.val J.val))

def reflectionBadIdeal : Ideal O := ∏ P ∈ fixedBadPrimes, P

def sourceMaskDivisorCost (B ε : ℝ) (hε : 0 < ε) : ℝ :=
  idealDivisorConstant ε hε * (B * (Ideal.absNorm reflectionBadIdeal : ℝ))^ε

theorem sourceMaskDivisors_bound (D : Ideal O) (hD : Admissible D)
    (B ε : ℝ) (hε : 0 < ε) (hN : (Ideal.absNorm D : ℝ) ≤ B) :
    ((idealDivisors (commonMaskIdeal D)).card : ℝ) ≤ sourceMaskDivisorCost B ε hε := by
  apply (idealDivisorConstant_bound ε hε _ (commonMaskIdeal_squarefree D).ne_zero).trans
  apply mul_le_mul_of_nonneg_left _ (idealDivisorConstant_pos ε hε).le
  apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ hε.le
  rw [commonMaskIdeal_norm D hD, Nat.cast_mul]
  simpa only [reflectionBadIdeal, mul_comm] using
    mul_le_mul_of_nonneg_left hN (show 0 ≤ (Ideal.absNorm reflectionBadIdeal : ℝ) from Nat.cast_nonneg _)

/-- The complete gcd block is bounded by a scalar envelope of its displayed
mode budgets. This premise only compares explicit finite expressions; all
Poisson, zero-frequency, near-frequency and tail estimates are proved above. -/
theorem originalGcdBlock_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ (Cnear Ctail : ℝ), 0 ≤ Cnear ∧ 0 ≤ Ctail ∧
      ∀ (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
        (hmod : ∀ I ∈ F, ∀ J ∈ F, primaryGenerator I-primaryGenerator J ∈
          (Ideal.span {(36 : O)} : Ideal O))
        (a : Ideal O → ℂ) (L B H ε K : ℝ) (hε : 0 < ε),
      0 < L → 0 < B → 0 ≤ H → 0 ≤ K →
      (∀ I ∈ F, (Ideal.absNorm I : ℝ) ∈ Set.Icc B (2*B)) →
      ∀ D ∈ gcdPool (fun I : F => I.val),
      (∀ e ∈ idealDivisors (commonMaskIdeal D),
        modeBudget (selectedQuotientRows F D) W L (B/(Ideal.absNorm D : ℝ))
          H Cnear Ctail (idealGenerator e) ε hε A ≤ K) →
      ‖originalGcdBlock F a W L D‖ ≤
        (1/6 : ℝ)*sourceMaskDivisorCost (2*B) ε hε*K *
          ∑ I : F, if D ∣ I.val then ‖a I.val‖^2 else 0 := by
  obtain ⟨Cn,Ct,hCn,hCt,hbound⟩ := selectedFullMode_bound W A
  refine ⟨Cn,Ct,hCn,hCt,?_⟩
  intro F hF hmod a L B H ε K hε hL hB hH hK hN D hD hbudget
  have hd := selectedGcd_spec F hF (2*B) (fun I hI => (hN I hI).2) D hD
  have hdpos : 0 < (Ideal.absNorm D : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h => hd.1.1 (Ideal.absNorm_eq_zero_iff.mp h))
  let G := descendantIdealFamily F D
  let hG := descendantIdealFamily_admissible F hF D
  let rows := selectedQuotientRows F D
  let b := selectedDescendantCoefficient F hF D (fun I => a I.val)
  have hm (e : Ideal O) (he : e ∈ idealDivisors (commonMaskIdeal D)) :
      ‖selectedFullMode G hG rows b W L (idealGenerator e)‖ ≤
        K * ∑ I : F, if D ∣ I.val then ‖a I.val‖^2 else 0 := by
    have hediv := (mem_idealDivisors (commonMaskIdeal_squarefree D).ne_zero).mp he
    have he0 : e ≠ 0 := by
      intro hz
      rw [hz, zero_dvd_iff] at hediv
      exact (commonMaskIdeal_squarefree D).ne_zero hediv
    have hh := hbound G hG rows (fun r => Finset.mem_image.mpr ⟨r.val,r.property,rfl⟩)
      (fun r => (selectedQuotientRows_spec F hF D r).1)
      (fun r => (selectedQuotientRows_spec F hF D r).2.1)
      (selectedQuotientRows_mod36 F hF D hmod) b L (B/(Ideal.absNorm D : ℝ)) H
      (idealGenerator e) ε hε hL (div_pos hB hdpos) hH
      (ConcretePrimeRowBridge.idealGenerator_ne_zero e he0)
      (selectedQuotientRows_norm F hF D hd.1.1 B hN)
    apply (hh.trans (mul_le_mul_of_nonneg_right (hbudget e he)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _))).trans_eq
    rw [selectedDescendantCoefficient_energy]
  rw [originalGcdBlock_eq_modes F hF D hd.1.1 hmod a W L hL, norm_mul]
  have h6 : ‖(6 : ℂ)⁻¹‖ = (1/6 : ℝ) := by norm_num
  rw [h6]
  calc
    _ ≤ (1/6 : ℝ) * ∑ e ∈ idealDivisors (commonMaskIdeal D),
        K * ∑ I : F, if D ∣ I.val then ‖a I.val‖^2 else 0 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro e he
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (QuadraticInitialBound.norm_ideal_moebius_le_one e)).trans (hm e he)
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hmass : 0 ≤ ∑ I : F, if D ∣ I.val then ‖a I.val‖^2 else 0 := by
        apply Finset.sum_nonneg
        intro I hI
        split_ifs <;> positivity
      have hh := mul_le_mul_of_nonneg_right (sourceMaskDivisors_bound D hd.1 (2*B) ε hε hd.2)
        (mul_nonneg hK hmass)
      nlinarith

/-- The sum of every descendant dual mass costs only the original row's
ordinary divisor bound. No total gcd-pool cardinality appears. -/
theorem descendant_mass_sum_le (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (a : F → ℂ) (B ε : ℝ) (hε : 0 < ε)
    (hN : ∀ I ∈ F, (Ideal.absNorm I : ℝ) ≤ B) :
    (∑ D ∈ gcdPool (fun I : F => I.val), ∑ I : F, if D ∣ I.val then ‖a I‖^2 else 0) ≤
      (idealDivisorConstant ε hε * B^ε) * ∑ I, ‖a I‖^2 := by
  have hh := sum_maskedEnergy_le
    (idealDivisorMask (gcdPool (fun I : F => I.val)) (fun I : F => I.val)) a
    (idealDivisorConstant ε hε * B^ε)
    (fun I => idealDivisorMask_incidence_small_power _ _ I (hF I.val I.property).1
      ε hε B (hN I.val I.property))
  have he : (∑ e : gcdPool (fun I : F => I.val),
      maskedEnergy (idealDivisorMask (gcdPool (fun I : F => I.val)) (fun I : F => I.val)) a e) =
      ∑ e : gcdPool (fun I : F => I.val), ∑ I : F, if e.val ∣ I.val then ‖a I‖^2 else 0 := by
    apply Finset.sum_congr rfl
    intro e he
    simp only [maskedEnergy, Finset.sum_filter]
    rfl
  rw [he] at hh
  rw [Finset.sum_coe_sort (gcdPool (fun I : F => I.val))
    (fun D => ∑ I : F, if D ∣ I.val then ‖a I‖^2 else 0)] at hh
  exact hh


/-- Whole positive Gram reflection, with both divisor incidences paid. The
only envelope premise bounds the explicit complete-mode budget. -/
theorem supportedSmoothGram_reflection (A : ℕ) :
    ∃ (Cnear Ctail : ℝ), 0 ≤ Cnear ∧ 0 ≤ Ctail ∧
      ∀ (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
        (hmod : ∀ I ∈ F, ∀ J ∈ F, primaryGenerator I-primaryGenerator J ∈
          (Ideal.span {(36 : O)} : Ideal O))
        (a : Ideal O → ℂ) (L B H ε K : ℝ) (hε : 0 < ε),
      0 < L → 0 < B → 0 ≤ H → 0 ≤ K →
      (∀ I ∈ F, (Ideal.absNorm I : ℝ) ∈ Set.Icc B (2*B)) →
      (∀ D ∈ gcdPool (fun I : F => I.val), ∀ e ∈ idealDivisors (commonMaskIdeal D),
        modeBudget (selectedQuotientRows F D) QuadraticInitialBound.sieveCutoff L
          (B/(Ideal.absNorm D : ℝ)) H Cnear Ctail (idealGenerator e) ε hε A ≤ K) →
      supportedSmoothGram F (fun I => a I.val) L ≤
        ((1/6 : ℝ)*sharedDivisorCost reflectionBadIdeal (2*B) ε hε*K) *
          ∑ I : F, ‖a I.val‖^2 := by
  obtain ⟨Cn,Ct,hCn,hCt,hbound⟩ := originalGcdBlock_bound QuadraticInitialBound.sieveCutoff A
  refine ⟨Cn,Ct,hCn,hCt,?_⟩
  intro F hF hmod a L B H ε K hε hL hB hH hK hN hbudget
  have hcoeff : 0 ≤ (1/6 : ℝ)*sourceMaskDivisorCost (2*B) ε hε*K := by
    unfold sourceMaskDivisorCost
    exact mul_nonneg (mul_nonneg (by norm_num)
      (mul_nonneg (idealDivisorConstant_pos ε hε).le
        (Real.rpow_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _)) ε))) hK
  calc
    _ = ‖(supportedSmoothGram F (fun I => a I.val) L : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (supportedSmoothGram_nonneg F _ L)]
    _ ≤ ∑ D ∈ gcdPool (fun I : F => I.val),
        ((1/6 : ℝ)*sourceMaskDivisorCost (2*B) ε hε*K) *
          ∑ I : F, if D ∣ I.val then ‖a I.val‖^2 else 0 := by
      rw [supportedSmoothGram_eq_gcd F a L hL]
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum fun D hD => hbound F hF hmod a L B H ε K hε hL hB hH hK hN D hD (hbudget D hD)
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      have hh := mul_le_mul_of_nonneg_left
        (descendant_mass_sum_le F hF (fun I => a I.val) (2*B) ε hε
          (fun I hI => (hN I hI).2)) hcoeff
      apply hh.trans_eq
      unfold sourceMaskDivisorCost sharedDivisorCost
      ring

/-- Finite maximum of the actual complete descendant-mode budgets, including
zero to cover empty row families. -/
def reflectionBudgetValues (F : Finset (Ideal O)) (L B H Cnear Ctail ε : ℝ)
    (hε : 0 < ε) (A : ℕ) : Finset ℝ :=
  insert 0 ((gcdPool (fun I : F => I.val)).biUnion fun D =>
    (idealDivisors (commonMaskIdeal D)).image fun e =>
      modeBudget (selectedQuotientRows F D) QuadraticInitialBound.sieveCutoff L
        (B/(Ideal.absNorm D : ℝ)) H Cnear Ctail (idealGenerator e) ε hε A)

def reflectionBudget (F : Finset (Ideal O)) (L B H Cnear Ctail ε : ℝ)
    (hε : 0 < ε) (A : ℕ) : ℝ :=
  (reflectionBudgetValues F L B H Cnear Ctail ε hε A).sup'
    (Finset.insert_nonempty _ _) (fun x => x)

theorem reflectionBudget_nonneg (F : Finset (Ideal O)) (L B H Cnear Ctail ε : ℝ)
    (hε : 0 < ε) (A : ℕ) : 0 ≤ reflectionBudget F L B H Cnear Ctail ε hε A := by
  unfold reflectionBudget reflectionBudgetValues
  exact Finset.le_sup' (fun x : ℝ => x) (Finset.mem_insert_self _ _)

theorem modeBudget_le_reflectionBudget (F : Finset (Ideal O)) (L B H Cnear Ctail ε : ℝ)
    (hε : 0 < ε) (A : ℕ) (D : Ideal O) (hD : D ∈ gcdPool (fun I : F => I.val))
    (e : Ideal O) (he : e ∈ idealDivisors (commonMaskIdeal D)) :
    modeBudget (selectedQuotientRows F D) QuadraticInitialBound.sieveCutoff L
      (B/(Ideal.absNorm D : ℝ)) H Cnear Ctail (idealGenerator e) ε hε A ≤
        reflectionBudget F L B H Cnear Ctail ε hε A := by
  unfold reflectionBudget
  apply Finset.le_sup' (fun x : ℝ => x)
  exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨D,hD,Finset.mem_image.mpr ⟨e,he,rfl⟩⟩)

def primaryRowEquiv (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I) :
    F ≃ F.image primaryGenerator :=
  Equiv.ofBijective (fun I => ⟨primaryGenerator I.val, Finset.mem_image.mpr ⟨I.val,I.property,rfl⟩⟩)
    ⟨by
      intro I J h
      apply Subtype.ext
      have he := congrArg (fun z : F.image primaryGenerator => Ideal.span {z.val}) h
      simpa only [(primaryGenerator_spec I.val (primaryGenerator_admissible I.val (hF _ I.property))).1,
        (primaryGenerator_spec J.val (primaryGenerator_admissible J.val (hF _ J.property))).1] using he,
      by
      intro z
      obtain ⟨I,hI,he⟩ := Finset.mem_image.mp z.property
      exact ⟨⟨I,hI⟩,Subtype.ext he⟩⟩

theorem selectedDualEnergy_primary_image (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (S : Finset (Ideal O))
    (a : F.image primaryGenerator → ℂ) :
    selectedDualEnergy (F.image primaryGenerator) S a =
      ∑ H : S, ‖∑ I : F, idealRowHom (primaryGenerator I.val) H.val * a (primaryRowEquiv F hF I)‖^2 := by
  unfold selectedDualEnergy selectedMatrix
  apply Finset.sum_congr rfl
  intro H hH
  congr 2
  symm
  exact (primaryRowEquiv F hF).sum_comp (fun z => idealRowHom z.val H.val * a z)

/-- Closed whole squarefree1/5 reflection for the ACTUAL selected operator,
with explicit finite divisor, bad-frequency, dyadic and tail costs. No
reflection or selected-norm estimate is assumed. -/
theorem squarefree_supported_reflection (A : ℕ) :
    ∃ (Cnear Ctail : ℝ), 0 ≤ Cnear ∧ 0 ≤ Ctail ∧
      ∀ (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
        (hmod : ∀ I ∈ F, ∀ J ∈ F, primaryGenerator I-primaryGenerator J ∈
          (Ideal.span {(36 : O)} : Ideal O))
        (S : Finset (Ideal O)) (L B H ε : ℝ) (hε : 0 < ε),
      0 < L → 0 < B → 0 ≤ H →
      (∀ I ∈ F, (Ideal.absNorm I : ℝ) ∈ Set.Icc B (2*B)) →
      (∀ I ∈ S, Supported I) → (∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ L) →
      selectedNorm (F.image primaryGenerator) S ≤
        (1/6 : ℝ)*sharedDivisorCost reflectionBadIdeal (2*B) ε hε *
          reflectionBudget F L B H Cnear Ctail ε hε A := by
  obtain ⟨Cn,Ct,hCn,hCt,hbound⟩ := supportedSmoothGram_reflection A
  refine ⟨Cn,Ct,hCn,hCt,?_⟩
  intro F hF hmod S L B H ε hε hL hB hH hN hS hSN
  let K := reflectionBudget F L B H Cn Ct ε hε A
  have hK : 0 ≤ K := reflectionBudget_nonneg F L B H Cn Ct ε hε A
  have hcost : 0 ≤ (1/6 : ℝ)*sharedDivisorCost reflectionBadIdeal (2*B) ε hε*K := by
    unfold sharedDivisorCost
    exact mul_nonneg (mul_nonneg (by norm_num)
      (mul_nonneg
        (mul_nonneg (idealDivisorConstant_pos ε hε).le (Real.rpow_nonneg (by positivity) ε))
        (mul_nonneg (idealDivisorConstant_pos ε hε).le
          (Real.rpow_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _)) ε)))) hK
  apply selectedNorm_le_of_energy _ _ _ hcost
  intro a
  let b : Ideal O → ℂ := fun I => if hi : I ∈ F then a (primaryRowEquiv F hF ⟨I,hi⟩) else 0
  have hb (I : F) : b I.val = a (primaryRowEquiv F hF I) := by simp only [b, dite_eq_left I.property]
  have he := supported_energy_le_smoothGram F S (fun I => b I.val) L hL hS hSN
  rw [selectedDualEnergy_primary_image F hF S a]
  simp_rw [hb] at he
  apply he.trans
  have hh := hbound F hF hmod b L B H ε K hε hL hB hH hK hN
    (modeBudget_le_reflectionBudget F L B H Cn Ct ε hε A)
  simp_rw [hb] at hh
  rw [(primaryRowEquiv F hF).sum_comp (fun z => ‖a z‖^2)] at hh
  exact hh


/-- Nonzero ordinary input ideals represented by their canonical generators.
The zero ideal is removed only by its exact zero column. -/
def inputFrequencies (S : Finset (Ideal O)) : Finset BadFrequencySectors.NonzeroFrequency :=
  (S.erase 0).attach.image fun I =>
    ⟨idealGenerator I.val, ConcretePrimeRowBridge.idealGenerator_ne_zero I.val
      (Finset.mem_erase.mp I.property).1⟩

theorem inputFrequencies_norm_le (S : Finset (Ideal O)) (L : ℝ)
    (hS : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ L)
    (h : BadFrequencySectors.NonzeroFrequency) (hh : h ∈ inputFrequencies S) :
    ‖eisEmbedding h.val‖^2 ≤ L := by
  obtain ⟨I,hi,rfl⟩ := Finset.mem_image.mp hh
  rw [idealGenerator_norm_sq]
  exact hS I.val (Finset.mem_erase.mp I.property).2

def inputSectorScale (k : Oˣ × ℕ × ℕ) : ℝ := (3 : ℝ)^k.2.1*(4 : ℝ)^k.2.2

theorem inputSectorScale_pos (k : Oˣ × ℕ × ℕ) : 0 < inputSectorScale k := by
  unfold inputSectorScale
  positivity

theorem inputSectorIdeal_ne_zero (k : Oˣ × ℕ × ℕ) : BadFrequencySectors.keyIdeal k ≠ 0 := by
  have hn : BadFrequencySectors.keyFactor k ≠ 0 :=
    mul_ne_zero (mul_ne_zero k.1.ne_zero
      (pow_ne_zero _ PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero))
      (pow_ne_zero _ (by norm_num))
  change Ideal.span {BadFrequencySectors.keyFactor k} ≠ ⊥
  exact fun h => hn (Ideal.span_singleton_eq_bot.mp h)

theorem inputSectorSources_norm_le (S : Finset (Ideal O)) (L : ℝ)
    (hS : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ L)
    (k : Oˣ × ℕ × ℕ) (I : Ideal O)
    (hI : I ∈ selectedFrequencySources (inputFrequencies S) k) :
    (Ideal.absNorm I : ℝ) ≤ L/inputSectorScale k := by
  obtain ⟨H,hH,rfl⟩ := Finset.mem_image.mp hI
  apply (le_div_iff₀ (inputSectorScale_pos k)).mpr
  simpa only [inputSectorScale, mul_comm] using
    BadFrequencySectors.fiberSource_norm_le (inputFrequencies S) L
      (inputFrequencies_norm_le S L hS) k H hH

/-- Every input bad-place sector is retained, with its actual row multiplier.
The chosen section gives a common source selector. -/
theorem inputSource_sector_cover (S : Finset (Ideal O)) (L : ℝ)
    (hS : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ L) :
    S.erase 0 ⊆ (BadFrequencySectors.boundedKeys L).biUnion
      (fun k => (selectedFrequencySources (inputFrequencies S) k).image
        (fun I => BadFrequencySectors.keyIdeal k * I)) := by
  intro I hI
  let h : BadFrequencySectors.NonzeroFrequency :=
    ⟨idealGenerator I, ConcretePrimeRowBridge.idealGenerator_ne_zero I (Finset.mem_erase.mp hI).1⟩
  have hh : h ∈ inputFrequencies S :=
    Finset.mem_image.mpr ⟨⟨I,hI⟩,Finset.mem_attach _ _,rfl⟩
  let s := BadFrequencySectors.choose h
  let k := BadFrequencySectors.key s
  have hs : s ∈ (inputFrequencies S).image BadFrequencySectors.choose :=
    Finset.mem_image.mpr ⟨h,hh,rfl⟩
  have hk : k ∈ BadFrequencySectors.boundedKeys L :=
    BadFrequencySectors.chosen_keys_subset (inputFrequencies S) L
      (inputFrequencies_norm_le S L hS) (Finset.mem_image.mpr ⟨s,hs,rfl⟩)
  have hsource : s.source ∈ BadFrequencySectors.fiberSources (inputFrequencies S) k :=
    Finset.mem_image.mpr ⟨s,Finset.mem_filter.mpr ⟨hs,rfl⟩,rfl⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨k,hk,Finset.mem_image.mpr ⟨s.source.val,Finset.mem_image.mpr ⟨s.source,hsource,rfl⟩,?_⟩⟩
  rw [← BadFrequencySectors.span_decode_rebuild, BadFrequencySectors.rebuild_key_source,
    BadFrequencySectors.decode_choose]
  exact ConcretePrimeRowBridge.span_idealGenerator I

/-- Exhaustive ordinary-source operator decomposition. The sector multiplier
contracts arbitrary dual coefficients, so no special-vector hypothesis occurs. -/
theorem selectedNorm_input_sectors (rows : Finset O) (S : Finset (Ideal O)) (L : ℝ)
    (hS : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ L) :
    selectedNorm rows S ≤ ∑ k ∈ BadFrequencySectors.boundedKeys L,
      selectedNorm rows (selectedFrequencySources (inputFrequencies S) k) := by
  rw [← selectedNorm_erase_zero rows S]
  apply (selectedNorm_mono_sources rows (inputSource_sector_cover S L hS)).trans
  apply (selectedNorm_sources_biUnion_le rows (BadFrequencySectors.boundedKeys L) _).trans
  exact Finset.sum_le_sum fun k hk => selectedNorm_mul_sources_le rows _ _ (inputSectorIdeal_ne_zero k)

def allSourceReflectionBudgetValues (F : Finset (Ideal O)) (L B H Cnear Ctail ε : ℝ)
    (hε : 0 < ε) (A : ℕ) : Finset ℝ :=
  insert 0 ((BadFrequencySectors.boundedKeys L).image fun k =>
    reflectionBudget F (L/inputSectorScale k) B H Cnear Ctail ε hε A)

def allSourceReflectionBudget (F : Finset (Ideal O)) (L B H Cnear Ctail ε : ℝ)
    (hε : 0 < ε) (A : ℕ) : ℝ :=
  (allSourceReflectionBudgetValues F L B H Cnear Ctail ε hε A).sup'
    (Finset.insert_nonempty _ _) (fun x => x)

theorem allSourceReflectionBudget_nonneg (F : Finset (Ideal O)) (L B H Cnear Ctail ε : ℝ)
    (hε : 0 < ε) (A : ℕ) : 0 ≤ allSourceReflectionBudget F L B H Cnear Ctail ε hε A := by
  unfold allSourceReflectionBudget allSourceReflectionBudgetValues
  exact Finset.le_sup' (fun x : ℝ => x) (Finset.mem_insert_self _ _)

theorem reflectionBudget_le_allSourceReflectionBudget (F : Finset (Ideal O))
    (L B H Cnear Ctail ε : ℝ) (hε : 0 < ε) (A : ℕ)
    (k : Oˣ × ℕ × ℕ) (hk : k ∈ BadFrequencySectors.boundedKeys L) :
    reflectionBudget F (L/inputSectorScale k) B H Cnear Ctail ε hε A ≤
      allSourceReflectionBudget F L B H Cnear Ctail ε hε A := by
  unfold allSourceReflectionBudget
  apply Finset.le_sup' (fun x : ℝ => x)
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨k,hk,rfl⟩)

/-- WHOLE squarefree1/5 reflection on ALL ordinary source ideals. This is a
closed bound for the actual operator, with explicit finite/polylogarithmic
costs and the complete Schwartz tail. Natural zeros, bad-prime input and
output sectors, gcd descendants and source-mask divisors are all retained. -/
theorem squarefree_all_source_reflection (A : ℕ) :
    ∃ (Cnear Ctail : ℝ), 0 ≤ Cnear ∧ 0 ≤ Ctail ∧
      ∀ (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
        (hmod : ∀ I ∈ F, ∀ J ∈ F, primaryGenerator I-primaryGenerator J ∈
          (Ideal.span {(36 : O)} : Ideal O))
        (S : Finset (Ideal O)) (L B H ε : ℝ) (hε : 0 < ε),
      0 < L → 0 < B → 0 ≤ H →
      (∀ I ∈ F, (Ideal.absNorm I : ℝ) ∈ Set.Icc B (2*B)) →
      (∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ L) →
      selectedNorm (F.image primaryGenerator) S ≤
        (1/6 : ℝ)*sharedDivisorCost reflectionBadIdeal (2*B) ε hε *
          ((BadFrequencySectors.boundedKeys L).card : ℝ) *
            allSourceReflectionBudget F L B H Cnear Ctail ε hε A := by
  obtain ⟨Cn,Ct,hCn,hCt,hbound⟩ := squarefree_supported_reflection A
  refine ⟨Cn,Ct,hCn,hCt,?_⟩
  intro F hF hmod S L B H ε hε hL hB hH hN hS
  have hcost : 0 ≤ (1/6 : ℝ)*sharedDivisorCost reflectionBadIdeal (2*B) ε hε := by
    unfold sharedDivisorCost
    exact mul_nonneg (by norm_num) (mul_nonneg
      (mul_nonneg (idealDivisorConstant_pos ε hε).le (Real.rpow_nonneg (by positivity) ε))
      (mul_nonneg (idealDivisorConstant_pos ε hε).le
        (Real.rpow_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _)) ε)))
  apply (selectedNorm_input_sectors _ S L hS).trans
  calc
    _ ≤ ∑ k ∈ BadFrequencySectors.boundedKeys L,
        (1/6 : ℝ)*sharedDivisorCost reflectionBadIdeal (2*B) ε hε *
          allSourceReflectionBudget F L B H Cn Ct ε hε A := by
      apply Finset.sum_le_sum
      intro k hk
      apply (hbound F hF hmod (selectedFrequencySources (inputFrequencies S) k)
        (L/inputSectorScale k) B H ε hε (div_pos hL (inputSectorScale_pos k)) hB hH hN
        (selectedFrequencySources_supported (inputFrequencies S) k)
        (inputSectorSources_norm_le S L hS k)).trans
      exact mul_le_mul_of_nonneg_left
        (reflectionBudget_le_allSourceReflectionBudget F L B H Cn Ct ε hε A k hk) hcost
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end
end Qrh.JointDetector

#print axioms Qrh.JointDetector.squarefree_supported_reflection
#print axioms Qrh.JointDetector.squarefree_all_source_reflection
