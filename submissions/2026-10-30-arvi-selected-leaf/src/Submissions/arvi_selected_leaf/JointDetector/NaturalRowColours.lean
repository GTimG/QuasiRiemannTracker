/- Copyright (c) 2026 Joseph Bebel. All rights reserved. -/
import Submissions.arvi_selected_leaf.JointDetector.SelectedNormIteration
import Submissions.arvi_selected_leaf.JointDetector.NaturalSelectedNormContract

/-! Canonical five-colour and finite bad-place decomposition of actual
sixth-power-free rows. The bad factors are removed before good-prime Poisson
by an exact bounded common source multiplier, not a ramified Gauss premise. -/
namespace Qrh.JointDetector.NaturalRowColours
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic
open CanonicalRowCompletion CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss
open ConcretePrimeRowBridge IdealMobiusDivisorSum UniqueFactorizationMonoid
open CenteredExceptionalCount HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O

def colourSupport (I : Ideal O) (j : Fin 5) : Finset (Ideal O) :=
  (IdealMobiusDivisorSum.primeSupport I).filter fun P => valuation I P = j.val+1

def colourIdeal (I : Ideal O) (j : Fin 5) : Ideal O := ∏ P ∈ colourSupport I j, P

def colourProduct (c : Fin 5 → Ideal O) : Ideal O := ∏ j, c j^(j.val+1)

theorem colourIdeal_ne_zero (I : Ideal O) (j : Fin 5) : colourIdeal I j ≠ 0 :=
  support_product_ne_zero (show colourSupport I j ⊆ IdealMobiusDivisorSum.primeSupport I from Finset.filter_subset _ _)

theorem colourIdeal_squarefree (I : Ideal O) (j : Fin 5) : Squarefree (colourIdeal I j) :=
  squarefree_support_product (show colourSupport I j ⊆ IdealMobiusDivisorSum.primeSupport I from Finset.filter_subset _ _)

theorem colourIdeal_valuation (I P : Ideal O) (j : Fin 5) :
    valuation (colourIdeal I j) P = if valuation I P = j.val+1 then 1 else 0 := by
  unfold valuation colourIdeal
  rw [factors_support_product (show colourSupport I j ⊆ IdealMobiusDivisorSum.primeSupport I from Finset.filter_subset _ _)]
  by_cases h : valuation I P = j.val+1
  · have hp : P ∈ IdealMobiusDivisorSum.primeSupport I := Multiset.mem_toFinset.mpr (Multiset.count_pos.mp (by
      change 0 < valuation I P
      rw [h]
      omega))
    have hmem : P ∈ colourSupport I j := Finset.mem_filter.mpr ⟨hp,h⟩
    simpa only [show Multiset.count P (normalizedFactors I) = j.val+1 from h,
      ite_true] using (Multiset.count_eq_one_of_mem (colourSupport I j).nodup hmem)
  · have hp : P ∉ colourSupport I j := fun hh => h (Finset.mem_filter.mp hh).2
    simpa only [show ¬Multiset.count P (normalizedFactors I) = j.val+1 from h,
      ite_false] using (Multiset.count_eq_zero.mpr hp)

theorem valuation_prod {ι : Type*} (S : Finset ι) (f : ι → Ideal O)
    (hn : ∀ i ∈ S, f i ≠ 0) (P : Ideal O) :
    valuation (∏ i ∈ S, f i) P = ∑ i ∈ S, valuation (f i) P := by
  induction S using Finset.induction_on with
  | empty =>
    change valuation (1 : Ideal O) P = 0
    simp only [valuation, normalizedFactors_one, Multiset.count_zero]
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha,Finset.sum_insert ha,valuation_mul _ _ _ (hn a (Finset.mem_insert_self _ _))
      (Finset.prod_ne_zero_iff.mpr (fun i hi => hn i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hn i (Finset.mem_insert_of_mem hi))]

theorem colourProduct_eq (I : Ideal O) (hI : I ≠ 0) (hfree : SixthFree I) :
    colourProduct (colourIdeal I) = I := by
  unfold colourProduct
  apply ideal_eq_of_valuation_eq
    (Finset.prod_ne_zero_iff.mpr (fun j hj => pow_ne_zero _ (colourIdeal_ne_zero I j))) hI
  intro P
  rw [valuation_prod _ _ (fun j hj => pow_ne_zero _ (colourIdeal_ne_zero I j))]
  simp_rw [valuation_pow,colourIdeal_valuation]
  have hn : valuation I P < 6 := hfree P
  generalize he : valuation I P = n at *
  interval_cases n <;> norm_num [Fin.sum_univ_succ]

theorem colourIdeal_pairwise (I : Ideal O) : Pairwise (fun j k : Fin 5 => IsCoprime (colourIdeal I j) (colourIdeal I k)) := by
  intro j k hjk
  apply IsCoprime.prod_left
  intro P hP
  apply IsCoprime.prod_right
  intro Q hQ
  have hp := support_prime (Finset.mem_filter.mp hP).1
  have hq := support_prime (Finset.mem_filter.mp hQ).1
  letI : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  letI : Q.IsMaximal := (Ideal.isPrime_of_prime hq).isMaximal hq.ne_zero
  apply Ideal.isCoprime_of_isMaximal
  intro he
  have hv := (Finset.mem_filter.mp hP).2
  have hw := (Finset.mem_filter.mp hQ).2
  rw [he] at hv
  apply hjk
  apply Fin.ext
  omega

def goodColour (I : Ideal O) (j : Fin 5) : Ideal O := goodSquarefreePart (colourIdeal I j)

def badColour (I : Ideal O) (j : Fin 5) : Ideal O := ∏ P ∈ badPrimeSupport (colourIdeal I j), P

theorem goodColour_admissible (I : Ideal O) (j : Fin 5) : Admissible (goodColour I j) :=
  goodSquarefreePart_admissible _

theorem badColour_mul_goodColour (I : Ideal O) (j : Fin 5) :
    badColour I j*goodColour I j = colourIdeal I j :=
  squarefree_bad_good_product _ (colourIdeal_squarefree I j)

theorem badColour_ne_zero (I : Ideal O) (j : Fin 5) : badColour I j ≠ 0 := by
  apply left_ne_zero_of_mul
  rw [badColour_mul_goodColour]
  exact colourIdeal_ne_zero I j

theorem goodColour_dvd_colourIdeal (I : Ideal O) (j : Fin 5) : goodColour I j ∣ colourIdeal I j :=
  ⟨badColour I j,(badColour_mul_goodColour I j).symm.trans (mul_comm _ _)⟩

theorem goodColour_pairwise (I : Ideal O) : Pairwise (fun j k : Fin 5 => IsCoprime (goodColour I j) (goodColour I k)) := by
  intro j k hjk
  exact ((colourIdeal_pairwise I hjk).of_isCoprime_of_dvd_left (goodColour_dvd_colourIdeal I j)).of_isCoprime_of_dvd_right
    (goodColour_dvd_colourIdeal I k)

theorem bad_good_colourProduct (I : Ideal O) (hI : I ≠ 0) (hfree : SixthFree I) :
    colourProduct (badColour I)*colourProduct (goodColour I) = I := by
  calc
    _ = colourProduct (colourIdeal I) := ?_
    _ = I := colourProduct_eq I hI hfree
  unfold colourProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  rw [← mul_pow,badColour_mul_goodColour]

theorem badColour_dvd_fixed (I : Ideal O) (j : Fin 5) : badColour I j ∣ reflectionBadIdeal := by
  exact Finset.prod_dvd_prod_of_subset _ _ id (badPrimeSupport_subset _)

theorem badProduct_dvd_fixed (I : Ideal O) : colourProduct (badColour I) ∣ reflectionBadIdeal^15 := by
  have h := Finset.prod_dvd_prod_of_dvd (s := Finset.univ) (fun j : Fin 5 => badColour I j^(j.val+1)) (fun j : Fin 5 => reflectionBadIdeal^(j.val+1))
    (fun j _ => pow_dvd_pow_of_dvd (badColour_dvd_fixed I j) (j.val+1))
  change (∏ j : Fin 5, badColour I j^(j.val+1)) ∣ _
  convert h using 1
  rw [Finset.prod_pow_eq_pow_sum]
  norm_num [Fin.sum_univ_succ]

/-- A fixed row factor is a contractive common source multiplier.  Collisions
in the image are handled by an injective chosen preimage, not by multiplicity. -/
theorem selectedNorm_mul_image_le (a : O) (rows : Finset O) (S : Finset (Ideal O)) :
    selectedNorm (rows.image (a * ·)) S ≤ selectedNorm rows S := by
  let imageRows := rows.image (a * ·)
  have hex (z : imageRows) : ∃ r : rows, a*r.val = z.val := by
    obtain ⟨r,hr,he⟩ := Finset.mem_image.mp z.property
    exact ⟨⟨r,hr⟩,he⟩
  let f : imageRows → rows := fun z => Classical.choose (hex z)
  have hfval (z : imageRows) : a*(f z).val=z.val := Classical.choose_spec (hex z)
  have hf : Function.Injective f := by
    intro z w he
    apply Subtype.ext
    rw [← hfval z,← hfval w,he]
  let M : Matrix S rows ℂ := fun I z => idealRowHom a I.val * selectedMatrix rows S I z * 1
  have htw := FiniteSieveOperator.diagonal_twist_norm_le (selectedMatrix rows S)
    (fun I => idealRowHom a I.val) (fun _ => (1:ℂ))
    (fun I => idealRowHom_norm a I.val) (by simp)
  have hre := FiniteSieveRestriction.column_restriction_norm_le f hf M
  have he : (fun I z => M I (f z)) = selectedMatrix imageRows S := by
    funext I z
    simp only [M,selectedMatrix,mul_one,← idealRowHom_argument_mul,hfval]
  rw [he] at hre
  exact pow_le_pow_left₀ (norm_nonneg _) (hre.trans htw) 2

/-- The canonical good row is built only from admissible squarefree colours. -/
def goodElement (I : Ideal O) : O := ∏ j : Fin 5, primaryGenerator (goodColour I j)^(j.val+1)

theorem span_goodElement (I : Ideal O) :
    Ideal.span {goodElement I} = colourProduct (goodColour I) := by
  unfold goodElement colourProduct
  rw [← Ideal.prod_span_singleton]
  apply Finset.prod_congr rfl
  intro j hj
  rw [← Ideal.span_singleton_pow]
  rw [(primaryGenerator_spec _ (primaryGenerator_admissible _ (goodColour_admissible I j))).1]

theorem goodProduct_ne_zero (I : Ideal O) : colourProduct (goodColour I) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun j hj => pow_ne_zero _ (goodColour_admissible I j).1)

theorem goodElement_ne_zero (I : Ideal O) : goodElement I ≠ 0 := by
  intro he
  have h := goodProduct_ne_zero I
  rw [← span_goodElement,he] at h
  exact h (by simp)

theorem badProduct_ne_zero (I : Ideal O) : colourProduct (badColour I) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun j hj => pow_ne_zero _ (badColour_ne_zero I j))

/-- Every natural row retains its unit and its fixed finite bad ideal state. -/
theorem exists_bad_good_factor (z : FreeRow) :
    ∃ (u : Oˣ) (J : Ideal O), J ≠ 0 ∧ J ∣ reflectionBadIdeal^15 ∧
      z.val = (u.val*idealGenerator J)*goodElement (Ideal.span {z.val}) := by
  let I : Ideal O := Ideal.span {z.val}
  let J := colourProduct (badColour I)
  have hI : I ≠ 0 := by simpa [I] using z.property.1
  have hspan : Ideal.span {idealGenerator J*goodElement I} = Ideal.span {z.val} := by
    rw [← Ideal.span_singleton_mul_span_singleton,span_idealGenerator,span_goodElement]
    exact bad_good_colourProduct I hI z.property.2
  obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  refine ⟨u,J,badProduct_ne_zero I,badProduct_dvd_fixed I,?_⟩
  change z.val = (u.val*idealGenerator J)*goodElement I
  calc
    _ = idealGenerator J*goodElement I*u.val := hu.symm
    _ = _ := by ring

def higherProduct (c : Fin 5 → Ideal O) : Ideal O := ∏ j : Fin 4, c j.succ

theorem pivot_anchor_dvd (c : Fin 5 → Ideal O) :
    c 0*(higherProduct c)^2 ∣ colourProduct c := by
  unfold colourProduct higherProduct
  rw [Fin.prod_univ_succ (fun j : Fin 5 => c j^(j.val+1))]
  simp only [Fin.val_zero,zero_add,pow_one,Fin.val_succ]
  apply mul_dvd_mul_left
  rw [← Finset.prod_pow]
  apply Finset.prod_dvd_prod_of_dvd
  intro j hj
  exact pow_dvd_pow _ (by omega : 2 ≤ (j.val+1)+1)

theorem goodProduct_dvd (I : Ideal O) (hI : I ≠ 0) (hfree : SixthFree I) :
    colourProduct (goodColour I) ∣ I := by
  exact ⟨colourProduct (badColour I), (bad_good_colourProduct I hI hfree).symm.trans (mul_comm _ _)⟩

/-- The natural height dominates the colour-one pivot anchor U V². -/
theorem pivot_anchor_norm_le (I : Ideal O) (hI : I ≠ 0) (hfree : SixthFree I) :
    (Ideal.absNorm (goodColour I 0):ℝ)*
      (Ideal.absNorm (higherProduct (goodColour I)):ℝ)^2 ≤ (Ideal.absNorm I:ℝ) := by
  have h := norm_le_of_dvd hI ((pivot_anchor_dvd (goodColour I)).trans (goodProduct_dvd I hI hfree))
  simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using h

theorem goodElement_norm_le (I : Ideal O) (hI : I ≠ 0) (hfree : SixthFree I) :
    (Ideal.absNorm (Ideal.span {goodElement I}):ℝ) ≤ (Ideal.absNorm I:ℝ) := by
  rw [span_goodElement]
  exact norm_le_of_dvd hI (goodProduct_dvd I hI hfree)

end
end Qrh.JointDetector.NaturalRowColours

#print axioms Qrh.JointDetector.NaturalRowColours.exists_bad_good_factor
#print axioms Qrh.JointDetector.NaturalRowColours.selectedNorm_mul_image_le
#print axioms Qrh.JointDetector.NaturalRowColours.pivot_anchor_norm_le
