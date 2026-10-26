/- Copyright (c) 2026 Sil. Apache-2.0.
Finite bookkeeping for all nonzero frequencies, including the primes 2 and 3.
No frequency is removed. The number of bad-factor labels costs a small power.
-/
import Candidate.FourthPower.SieveDualGeometry

set_option autoImplicit false
namespace Candidate.FourthPower.SieveFrequencyGeometry
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CompletedGauss ConcreteTraceCRT
open ConcretePrimeRowBridge CanonicalRowCompletion CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

noncomputable instance : Fintype Oˣ := by
  let : Finite Oˣ := PrimaryIdealUnitReindex.finite_units
  exact Fintype.ofFinite _

def badFactor (u : Oˣ) (a b : ℕ) : O := u.val*lambda^a*(2 : O)^b

theorem badFactor_norm_sq (u : Oˣ) (a b : ℕ) :
    ‖eisEmbedding (badFactor u a b)‖^2 = (3 : ℝ)^a*4^b := by
  have hl : ‖eisEmbedding lambda‖^2 = (3 : ℝ) := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,CubicEisenstein.absNorm_span_lambda]
    norm_num
  have ht : ‖eisEmbedding (2 : O)‖^2 = (4 : ℝ) := by
    rw [map_ofNat]
    norm_num
  simp only [badFactor,map_mul,map_pow,norm_mul,norm_pow,mul_pow,
    GaussGeneratorTransport.norm_eisEmbedding_unit,one_pow,one_mul,
    pow_right_comm _ a 2,pow_right_comm _ b 2,hl,ht]

theorem exists_good_frequency (x : O) (hx : x ≠ 0) :
    ∃ u : Oˣ, ∃ a b : ℕ, ∃ K : Id, Supported K ∧
      x = badFactor u a b*primaryGenerator K := by
  obtain ⟨u,a,b,r,hr,hprimary,he⟩ := exists_supported_numerator_factorization x hx
  have hr0 : r ≠ 0 := by
    intro hzero
    apply hr.1
    simp only [hzero,Ideal.span_singleton_zero]
    rfl
  refine ⟨u,a,b,Ideal.span {r},hr,?_⟩
  rw [primaryGenerator_span r hr0 hprimary]
  exact he

theorem frequency_norm (u : Oˣ) (a b : ℕ) (K : Id) (hK : Supported K) :
    (Ideal.absNorm (Ideal.span {badFactor u a b*primaryGenerator K}) : ℝ) =
      (3 : ℝ)^a*4^b*(Ideal.absNorm K : ℝ) := by
  rw [← eisEmbedding_norm_sq_eq_absNorm_span,map_mul,norm_mul,mul_pow,badFactor_norm_sq,
    primaryGenerator_norm_sq K (supported_primaryGenerator_ne_zero K hK)]

abbrev BadLabel (X : ℝ) := Oˣ × Fin (columnDyadicLength X+1) × Fin (columnDyadicLength X+1)

def factor (X : ℝ) (l : BadLabel X) : O := badFactor l.1 l.2.1.val l.2.2.val

theorem factor_nonzero (X : ℝ) (l : BadLabel X) : factor X l ≠ 0 := by
  intro he
  have hn := badFactor_norm_sq l.1 l.2.1.val l.2.2.val
  change badFactor l.1 l.2.1.val l.2.2.val = 0 at he
  rw [he,map_zero,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0)] at hn
  have hp : 0 < (3 : ℝ)^l.2.1.val*4^l.2.2.val := by positivity
  linarith

theorem factor_labels (X : ℝ) (x : O) (hx : x ≠ 0)
    (hX : (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ X) :
    ∃ l : BadLabel X, ∃ K : SieveRanges.fullRange X, x = factor X l*primaryGenerator K.val := by
  obtain ⟨u,a,b,K,hK,rfl⟩ := exists_good_frequency x hx
  rw [frequency_norm u a b K hK] at hX
  have hKn : 1 ≤ (Ideal.absNorm K : ℝ) := CenteredExceptionalCount.norm_one_le hK.1
  have h3 : 1 ≤ (3 : ℝ)^a := one_le_pow₀ (by norm_num)
  have h4 : 1 ≤ (4 : ℝ)^b := one_le_pow₀ (by norm_num)
  have hprod : (3 : ℝ)^a*4^b ≤ X :=
    (le_mul_of_one_le_right (by positivity) hKn).trans hX
  have ha : (2 : ℝ)^a ≤ X :=
    ((pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 3) a).trans
      (le_mul_of_one_le_right (by positivity) h4)).trans hprod
  have hb : (2 : ℝ)^b ≤ X :=
    ((pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 4) b).trans
      (le_mul_of_one_le_left (by positivity) h3)).trans hprod
  have ha' : a ≤ columnDyadicLength X :=
    (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp (ha.trans (columnDyadicLength_cover X))
  have hb' : b ≤ columnDyadicLength X :=
    (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp (hb.trans (columnDyadicLength_cover X))
  have hKX : (Ideal.absNorm K : ℝ) ≤ X :=
    (le_mul_of_one_le_left (by positivity) (one_le_mul_of_one_le_of_one_le h3 h4)).trans hX
  exact ⟨(u,⟨a,Nat.lt_succ_of_le ha'⟩,⟨b,Nat.lt_succ_of_le hb'⟩),
    ⟨K,SieveRanges.mem_fullRange.mpr ⟨hK,hKX⟩⟩,rfl⟩

theorem labels_card (X : ℝ) : Fintype.card (BadLabel X) = 6*(columnDyadicLength X+1)^2 := by
  have hu : Fintype.card Oˣ = 6 := by
    simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six
  simp only [BadLabel,Fintype.card_prod,Fintype.card_fin,hu,pow_two,mul_assoc]

theorem labels_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → (Fintype.card (BadLabel X) : ℝ) ≤ C*X^ε := by
  let C : ℝ := 6*(2+1/((ε/2)*Real.log 2))^2
  have hc : 0 < C := by
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp only [C]
    positivity
  refine ⟨C,hc,?_⟩
  intro X hX
  have hn : 0 ≤ (columnDyadicLength X+1 : ℝ) := by positivity
  have hh := pow_le_pow_left₀ hn (columnDyadicLength_small_power (ε/2) (by positivity) X hX) 2
  have hp : (X^(ε/2))^2 = X^ε := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (zero_le_one.trans hX)]
    congr 1
    ring
  rw [mul_pow,hp] at hh
  rw [labels_card]
  push_cast
  exact (mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 6)).trans_eq (mul_assoc _ _ _).symm

theorem exists_representation (X : ℝ) (x : O) (hx : x ≠ 0)
    (hX : (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ X) :
    ∃ p : BadLabel X × ↥(SieveRanges.fullRange X), x = factor X p.1*primaryGenerator p.2.val := by
  obtain ⟨l,K,h⟩ := factor_labels X x hx hX
  exact ⟨(l,K),h⟩

def representation (X : ℝ) (R : Finset O)
    (hR : ∀ x ∈ R, x ≠ 0 ∧ (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ X)
    (x : R) : BadLabel X × ↥(SieveRanges.fullRange X) :=
  Classical.choose (exists_representation X x.val (hR x.val x.property).1 (hR x.val x.property).2)

theorem representation_spec (X : ℝ) (R : Finset O)
    (hR : ∀ x ∈ R, x ≠ 0 ∧ (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ X) (x : R) :
    x.val = factor X (representation X R hR x).1*primaryGenerator (representation X R hR x).2.val :=
  Classical.choose_spec (exists_representation X x.val (hR x.val x.property).1 (hR x.val x.property).2)

theorem representation_injective (X : ℝ) (R : Finset O)
    (hR : ∀ x ∈ R, x ≠ 0 ∧ (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ X) :
    Function.Injective (representation X R hR) := by
  intro x y he
  apply Subtype.ext
  rw [representation_spec X R hR x,representation_spec X R hR y,he]

def frequencies (X : ℝ) (R : Finset O)
    (hR : ∀ x ∈ R, x ≠ 0 ∧ (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ X)
    (l : BadLabel X) : Finset Id :=
  (Finset.univ.filter (fun x : R => (representation X R hR x).1 = l)).image
    (fun x => (representation X R hR x).2.val)

theorem frequency_fiber_eq (X : ℝ) (R : Finset O)
    (hR : ∀ x ∈ R, x ≠ 0 ∧ (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ X)
    (l : BadLabel X) (F : O → ℂ) :
    (∑ K ∈ frequencies X R hR l, F (factor X l*primaryGenerator K)) =
      ∑ x : R, if (representation X R hR x).1 = l then F x.val else 0 := by
  unfold frequencies
  rw [Finset.sum_image]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hl : (representation X R hR x).1 = l
    · rw [ite_eq_left hl,ite_eq_left hl,representation_spec X R hR x,hl]
    · simp only [ite_eq_right hl]
  · intro x hx y hy he
    apply representation_injective X R hR
    apply Prod.ext
    · exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    · exact Subtype.ext he

/-- Exact reindexing of every finite nonzero frequency family. The choice
of a representation creates no multiplicity loss because it is injective. -/
theorem frequency_sum (X : ℝ) (R : Finset O)
    (hR : ∀ x ∈ R, x ≠ 0 ∧ (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ X) (F : O → ℂ) :
    (∑ x ∈ R, F x) =
      ∑ l : BadLabel X, ∑ K ∈ frequencies X R hR l, F (factor X l*primaryGenerator K) := by
  simp_rw [frequency_fiber_eq]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  exact (Finset.sum_coe_sort R F).symm

theorem frequency_geometry (X : ℝ) (R : Finset O)
    (hR : ∀ x ∈ R, x ≠ 0 ∧ (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ X)
    (Y : ℝ) (hY : ∀ x ∈ R, Y ≤ (Ideal.absNorm (Ideal.span {x}) : ℝ))
    (l : BadLabel X) (K : Id) (hK : K ∈ frequencies X R hR l) :
    Supported K ∧ Y/‖eisEmbedding (factor X l)‖^2 ≤ (Ideal.absNorm K : ℝ) ∧
      (Ideal.absNorm K : ℝ) ≤ X/‖eisEmbedding (factor X l)‖^2 := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hK
  have hl := (Finset.mem_filter.mp hx).2
  have hs := (SieveRanges.mem_fullRange.mp (representation X R hR x).2.property).1
  have he : (Ideal.absNorm (Ideal.span {x.val}) : ℝ) =
      ‖eisEmbedding (factor X l)‖^2*(Ideal.absNorm (representation X R hR x).2.val : ℝ) := by
    rw [representation_spec X R hR x,hl,← eisEmbedding_norm_sq_eq_absNorm_span,
      map_mul,norm_mul,mul_pow,primaryGenerator_norm_sq _ (supported_primaryGenerator_ne_zero _ hs)]
  have hp : 0 < ‖eisEmbedding (factor X l)‖^2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (factor_nonzero X l)))
  refine ⟨hs,(div_le_iff₀ hp).mpr ?_,(le_div_iff₀ hp).mpr ?_⟩
  · simpa only [he,mul_comm] using hY x.val x.property
  · simpa only [he,mul_comm] using (hR x.val x.property).2

end
end Candidate.FourthPower.SieveFrequencyGeometry
