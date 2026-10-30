/- Copyright (c) 2026 Joseph Bebel. All rights reserved. -/
import Submissions.arvi_selected_leaf.JointDetector.NaturalSelectedNorm

/-! Positive smooth completion of the actual natural five-colour matrix.
The original bad-source mask is retained in the ideal-to-element conversion. -/
namespace Qrh.JointDetector.NaturalSelectedNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic ActualEisensteinCoordinates
open CanonicalRowCompletion CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss
open ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson QuadraticAllOddCRT
local notation "O" => ActualEisensteinCubic.O

def weightedIdeal (c : ColourTuple) : Ideal O := NaturalRowColours.colourProduct c

theorem tupleRow_eq_primary (c : ColourTuple) : tupleRow c=primaryGenerator (weightedIdeal c) := by
  change (∏ j : Fin 5, primaryGeneratorHom (c j)^(j.val+1)) =
    primaryGeneratorHom (∏ j : Fin 5, c j^(j.val+1))
  rw [map_prod]
  simp only [map_pow]

theorem tuple_weighted_supported (c : ColourTuple) (h : ∀ j, Admissible (c j)) :
    Supported (weightedIdeal c) := by
  have hp (S : Finset (Fin 5)) : Supported (∏ j ∈ S, c j^(j.val+1)) := by
    induction S using Finset.induction_on with
    | empty =>
      simpa only [Finset.prod_empty,pow_zero] using supported_pow (admissible_supported (h 0)) 0
    | @insert j S hj ih =>
      rw [Finset.prod_insert hj]
      exact (supported_mul_iff _ _).mpr ⟨supported_pow (admissible_supported (h j)) _,ih⟩
  exact hp Finset.univ

def tupleSmoothGram (F : Finset ColourTuple) (a : F → ℂ) (L : ℝ) : ℝ :=
  ∑' H : Ideal O, if Supported H then
    QuadraticInitialBound.sieveBump ((Ideal.absNorm H : ℝ)/L) *
      ‖∑ I : F, idealRowHom (tupleRow I.val) H * a I‖^2 else 0

theorem tupleSmoothGram_summable (F : Finset ColourTuple) (a : F → ℂ)
    (L : ℝ) (hL : 0 < L) : Summable (fun H : Ideal O => if Supported H then
    QuadraticInitialBound.sieveBump ((Ideal.absNorm H : ℝ)/L) *
      ‖∑ I : F, idealRowHom (tupleRow I.val) H * a I‖^2 else 0) := by
  let M : ℝ := (∑ I : F, ‖a I‖)^2
  have hM : 0 ≤ M := sq_nonneg _
  apply Summable.of_nonneg_of_le (fun H => by split_ifs; exact mul_nonneg QuadraticInitialBound.sieveBump.nonneg (sq_nonneg _); exact le_rfl) _
    ((supported_radial_norm_summable QuadraticInitialBound.sieveCutoff L hL).mul_left M)
  intro H
  by_cases hH : Supported H
  · simp only [hH, ite_true, QuadraticInitialBound.sieveCutoff_apply, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg QuadraticInitialBound.sieveBump.nonneg]
    have hh : ‖∑ I : F, idealRowHom (tupleRow I.val) H * a I‖ ≤ ∑ I : F, ‖a I‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro I hI
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (idealRowHom_norm _ _)
    have hs := pow_le_pow_left₀ (norm_nonneg _) hh 2
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hs QuadraticInitialBound.sieveBump.nonneg
  · simp only [hH, ite_false, mul_zero, le_refl]

theorem tupleSmoothGram_nonneg (F : Finset ColourTuple) (a : F → ℂ) (L : ℝ) :
    0 ≤ tupleSmoothGram F a L :=
  tsum_nonneg fun H => by split_ifs; exact mul_nonneg QuadraticInitialBound.sieveBump.nonneg (sq_nonneg _); exact le_rfl

/-- The positive smooth Gram is exactly the sum of the actual ordinary-ideal
pair kernels. No signed diagonal is subtracted. -/
theorem tupleSmoothGram_eq_pairs (F : Finset ColourTuple) (a : F → ℂ)
    (L : ℝ) (hL : 0 < L) :
    (tupleSmoothGram F a L : ℂ) =
      ∑ I : F, ∑ J : F, a I * star (a J) *
        selectedSupportedPairSource (weightedIdeal I.val) (weightedIdeal J.val) QuadraticInitialBound.sieveCutoff L := by
  let W := QuadraticInitialBound.sieveCutoff
  let f := fun (I J : F) (H : Ideal O) =>
    a I * star (a J) * supportedPairSummand (weightedIdeal I.val) (weightedIdeal J.val) W L H
  have hf (I J : F) : Summable (f I J) :=
    (supportedPairSummand_summable (weightedIdeal I.val) (weightedIdeal J.val) W L hL).mul_left _
  have he (H : Ideal O) :
      ((if Supported H then QuadraticInitialBound.sieveBump ((Ideal.absNorm H : ℝ)/L) *
        ‖∑ I : F, idealRowHom (tupleRow I.val) H * a I‖^2 else 0 : ℝ) : ℂ) =
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
        QuadraticInitialBound.sieveCutoff_apply, star_mul,tupleRow_eq_primary]
      ring
    · simp only [hH, ite_false, Complex.ofReal_zero, f, supportedPairSummand,
        mul_zero, Finset.sum_const_zero]
  unfold tupleSmoothGram
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
theorem tuple_energy_le_smoothGram (F : Finset ColourTuple) (S : Finset (Ideal O)) (a : F → ℂ)
    (L : ℝ) (hL : 0 < L) (hS : ∀ H ∈ S, Supported H)
    (hN : ∀ H ∈ S, (Ideal.absNorm H : ℝ) ≤ L) :
    (∑ H : S, ‖∑ I : F, idealRowHom (tupleRow I.val) H.val * a I‖^2) ≤
      tupleSmoothGram F a L := by
  rw [Finset.sum_coe_sort S (fun H => ‖∑ I : F, idealRowHom (tupleRow I.val) H * a I‖^2)]
  calc
    _ = ∑ H ∈ S, if Supported H then
        QuadraticInitialBound.sieveBump ((Ideal.absNorm H : ℝ)/L) *
          ‖∑ I : F, idealRowHom (tupleRow I.val) H * a I‖^2 else 0 := by
      apply Finset.sum_congr rfl
      intro H hH
      rw [ite_eq_left (hS H hH), QuadraticInitialBound.sieveBump_eq_one
        (div_nonneg (Nat.cast_nonneg _) hL.le) ((div_le_one hL).mpr (hN H hH)), one_mul]
    _ ≤ _ := (tupleSmoothGram_summable F a L hL).sum_le_tsum S
      (fun H hH => by split_ifs; exact mul_nonneg QuadraticInitialBound.sieveBump.nonneg (sq_nonneg _); exact le_rfl)


theorem supportedPairSource_eq_element (I J : Ideal O)
    (hI : Supported I) (hJ : Supported J)
    (hmod : primaryGenerator I-primaryGenerator J ∈ (Ideal.span {(36 : O)} : Ideal O))
    (W : 𝓢(ℝ, ℂ)) (L : ℝ) (hL : 0 < L) :
    selectedSupportedPairSource I J W L = (6 : ℂ)⁻¹ *
      ∑' z : O, rowCoprimeMask badPrime Finset.univ z * primitivePair I J z *
        W (‖eisEmbedding z‖^2/L) := by
  let mask : Ideal O → ℂ := fun H => if Supported H then 1 else 0
  have hi := primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)
  have hj := primaryGenerator_spec J (supported_primaryGenerator_ne_zero J hJ)
  have he := masked_actual_pair_mod36 (primaryGenerator I) (primaryGenerator J)
    hi.2 hj.2 (hi.1.symm ▸ hI) (hj.1.symm ▸ hJ)
    hmod mask (fun H hn => ite_eq_right hn) (fun H => by dsimp [mask]; split_ifs <;> simp) W L hL
  have hl : (∑' z : O, if lambda ∣ z then 0 else
      maskedPairRadial (Ideal.span {primaryGenerator I}) (Ideal.span {primaryGenerator J}) mask W L z) =
      ∑' z : O, rowCoprimeMask badPrime Finset.univ z * primitivePair I J z *
        W (‖eisEmbedding z‖^2/L) := by
    apply tsum_congr
    intro z
    rw [badPrime_mask]
    unfold maskedPairRadial mask
    rw [hi.1, hj.1]
    by_cases hs : Supported (Ideal.span {z})
    · have hn := (supported_span_iff z).mp hs
      simp only [hs, hn.1, ite_false, ite_true, one_mul]
    · simp only [hs, ite_false, zero_mul]
      split_ifs <;> rfl
  rw [hl] at he
  have hr : (∑' H : Ideal O, mask H *
      (idealRowHom (primaryGenerator I) H * star (idealRowHom (primaryGenerator J) H)) *
        W ((Ideal.absNorm H : ℝ)/L)) = selectedSupportedPairSource I J W L := by
    unfold selectedSupportedPairSource
    apply tsum_congr
    intro H
    dsimp only [mask]
    split_ifs <;> simp
  rw [hr] at he
  rw [he]
  ring

/-- Positive completion controls the exact selected matrix. A chosen preimage
handles any duplicate tuple presentations without charging their multiplicity. -/
theorem tuple_selectedNorm_supported_le (F : Finset ColourTuple) (S : Finset (Ideal O))
    (L K : ℝ) (hL : 0 < L) (hK : 0 ≤ K)
    (hS : ∀ I ∈ S, Supported I) (hN : ∀ I ∈ S, (Ideal.absNorm I:ℝ) ≤ L)
    (hgram : ∀ a : F → ℂ, tupleSmoothGram F a L ≤ K*∑ c, ‖a c‖^2) :
    selectedNorm (F.image tupleRow) S ≤ K := by
  let M : Matrix S F ℂ := fun I c => idealRowHom (tupleRow c.val) I.val
  have hM : ‖FiniteSieveOperator.operator M‖^2 ≤ K := by
    apply FiniteSieveOperator.squared_norm_le_of_energy M K hK
    intro a
    exact (tuple_energy_le_smoothGram F S a L hL hS hN).trans (hgram a)
  have hex (z : F.image tupleRow) : ∃ c : F, tupleRow c.val=z.val := by
    obtain ⟨c,hc,he⟩ := Finset.mem_image.mp z.property
    exact ⟨⟨c,hc⟩,he⟩
  let f : F.image tupleRow → F := fun z => Classical.choose (hex z)
  have hfval (z : F.image tupleRow) : tupleRow (f z).val=z.val := Classical.choose_spec (hex z)
  have hf : Function.Injective f := by
    intro z w he
    apply Subtype.ext
    rw [← hfval z,← hfval w,he]
  have hre := FiniteSieveRestriction.column_restriction_norm_le f hf M
  have he : (fun I z => M I (f z))=selectedMatrix (F.image tupleRow) S := by
    funext I z
    simp only [M,selectedMatrix,hfval]
  rw [he] at hre
  exact (pow_le_pow_left₀ (norm_nonneg _) hre 2).trans hM

/-- Exhaustive bad input-source sectors retain the ORIGINAL length L. This
preserves the long-source condition L≥natural height in every sector. -/
theorem tuple_selectedNorm_all_sources_le (F : Finset ColourTuple) (S : Finset (Ideal O))
    (L K : ℝ) (hL : 0 < L) (hK : 0 ≤ K)
    (hN : ∀ I ∈ S, (Ideal.absNorm I:ℝ) ≤ L)
    (hgram : ∀ a : F → ℂ, tupleSmoothGram F a L ≤ K*∑ c, ‖a c‖^2) :
    selectedNorm (F.image tupleRow) S ≤ ((BadFrequencySectors.boundedKeys L).card:ℝ)*K := by
  apply (selectedNorm_input_sectors _ S L hN).trans
  calc
    _ ≤ ∑ _k ∈ BadFrequencySectors.boundedKeys L, K := by
      apply Finset.sum_le_sum
      intro k hk
      exact tuple_selectedNorm_supported_le F _ L K hL hK
        (selectedFrequencySources_supported (inputFrequencies S) k)
        (selectedFrequencySources_norm_le (inputFrequencies S) L (inputFrequencies_norm_le S L hN) k) hgram
    _ = _ := by simp

/-- Absolute lattice control is used only for the actual diagonal and tails. -/
theorem bounded_pair_radial_sum_le (I J : Ideal O) (mask : O → ℂ)
    (hmask : ∀ z, ‖mask z‖ ≤ 1) (W : 𝓢(ℝ,ℂ)) (L : ℝ) (hL : 1 ≤ L) :
    ‖∑' z : O, mask z*primitivePair I J z*W (‖eisEmbedding z‖^2/L)‖ ≤
      QuadraticInitialBound.diagonalControl W*L := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hw : Summable (fun z : O => ‖W (‖eisEmbedding z‖^2/L)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W L hL0)
  have hpoint (z : O) : ‖mask z*primitivePair I J z*W (‖eisEmbedding z‖^2/L)‖ ≤
      ‖W (‖eisEmbedding z‖^2/L)‖ := by
    rw [norm_mul,norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    exact (mul_le_mul (hmask z) (primitivePair_norm_le I J z) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hs : Summable (fun z : O => ‖mask z*primitivePair I J z*W (‖eisEmbedding z‖^2/L)‖) :=
    Summable.of_nonneg_of_le (fun z => norm_nonneg _) hpoint hw
  exact (norm_tsum_le_tsum_norm hs).trans
    ((hs.tsum_le_tsum hpoint hw).trans (QuadraticInitialBound.radial_weight_lattice_bound W L hL))

theorem supportedPairSource_diagonal_le (I : Ideal O) (hI : Supported I)
    (W : 𝓢(ℝ,ℂ)) (L : ℝ) (hL : 1 ≤ L) :
    ‖selectedSupportedPairSource I I W L‖ ≤
      (1/6:ℝ)*QuadraticInitialBound.diagonalControl W*L := by
  rw [supportedPairSource_eq_element I I hI hI (by simp) W L (by linarith),norm_mul]
  have hm (z : O) : ‖rowCoprimeMask badPrime Finset.univ z‖ ≤ 1 := by
    rw [badPrime_mask]
    split_ifs <;> norm_num
  have hb := bounded_pair_radial_sum_le I I _ hm W L hL
  norm_num only [norm_div,norm_one,Complex.norm_ofNat]
  calc
    _ ≤ (1/6:ℝ)*(QuadraticInitialBound.diagonalControl W*L) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

def tupleOffDiagonalGram (F : Finset ColourTuple) (a : F → ℂ) (L : ℝ) : ℂ :=
  ∑ c : F, ∑ d : F, if c=d then 0 else
    a c*star (a d)*selectedSupportedPairSource (weightedIdeal c.val) (weightedIdeal d.val)
      QuadraticInitialBound.sieveCutoff L

theorem tupleSmoothGram_diagonal_offDiagonal (F : Finset ColourTuple) (a : F → ℂ)
    (L : ℝ) (hL : 0 < L) :
    (tupleSmoothGram F a L:ℂ)=
      (∑ c : F, a c*star (a c)*selectedSupportedPairSource (weightedIdeal c.val) (weightedIdeal c.val)
        QuadraticInitialBound.sieveCutoff L)+tupleOffDiagonalGram F a L := by
  rw [tupleSmoothGram_eq_pairs F a L hL]
  unfold tupleOffDiagonalGram
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  have he : a c*star (a c)*selectedSupportedPairSource (weightedIdeal c.val) (weightedIdeal c.val)
      QuadraticInitialBound.sieveCutoff L =
      ∑ d : F, if c=d then a c*star (a d)*selectedSupportedPairSource (weightedIdeal c.val) (weightedIdeal d.val)
        QuadraticInitialBound.sieveCutoff L else 0 := by simp
  conv_rhs => lhs; rw [he]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs <;> simp_all

theorem tupleSmoothGram_le_diagonal_offDiagonal (F : Finset ColourTuple) (a : F → ℂ)
    (hF : ∀ c ∈ F, ∀ j, Admissible (c j)) (L : ℝ) (hL : 1 ≤ L) :
    tupleSmoothGram F a L ≤
      ((1/6:ℝ)*QuadraticInitialBound.diagonalControl QuadraticInitialBound.sieveCutoff*L)*
        (∑ c, ‖a c‖^2)+‖tupleOffDiagonalGram F a L‖ := by
  have hdiag (c : F) := supportedPairSource_diagonal_le (weightedIdeal c.val)
    (tuple_weighted_supported c.val (hF c.val c.property)) QuadraticInitialBound.sieveCutoff L hL
  calc
    _ = ‖(tupleSmoothGram F a L:ℂ)‖ := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (tupleSmoothGram_nonneg F a L)]
    _ ≤ ‖∑ c : F, a c*star (a c)*selectedSupportedPairSource (weightedIdeal c.val) (weightedIdeal c.val)
        QuadraticInitialBound.sieveCutoff L‖+‖tupleOffDiagonalGram F a L‖ := by
      rw [tupleSmoothGram_diagonal_offDiagonal F a L (by linarith)]
      exact norm_add_le _ _
    _ ≤ _ := by
      apply add_le_add _ le_rfl
      apply (norm_sum_le _ _).trans
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro c hc
      rw [norm_mul,norm_mul,norm_star]
      exact (mul_le_mul_of_nonneg_left (hdiag c) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (by ring)

end
end Qrh.JointDetector.NaturalSelectedNorm

#print axioms Qrh.JointDetector.NaturalSelectedNorm.tupleSmoothGram_eq_pairs
#print axioms Qrh.JointDetector.NaturalSelectedNorm.supportedPairSource_eq_element

#print axioms Qrh.JointDetector.NaturalSelectedNorm.tuple_selectedNorm_all_sources_le

#print axioms Qrh.JointDetector.NaturalSelectedNorm.tupleSmoothGram_le_diagonal_offDiagonal
