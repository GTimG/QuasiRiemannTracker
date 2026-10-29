/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.WholeWordAmplification
import Candidate.Local.Qrh.JointDetector.BalancedSlotSelection
import Candidate.Local.Qrh.JointDetector.SelectedSlotData
import Candidate.Local.Qrh.JointDetector.SelectedReflection

/-! Actual finite word production at an arbitrary amplification crossing.
Selection uses only common slot widths and fixed amplitude-cell labels.
The summed ordinary source variable never enters the choice of word.
-/
namespace Qrh.JointDetector.SlotWordProducer
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentAddedZero CenteredMomentSourceMass
open WholeWordAmplification
local notation "O" => ActualEisensteinCubic.O

abbrev Letters {ι : Type*} (n : ℕ) (J R : Finset ι) := (Fin n × J) ⊕ R

def letter {ι : Type*} (n : ℕ) (J R : Finset ι) : Letters n J R → ι :=
  Sum.elim (fun p => p.2.val) (fun i => i.val)

def letterAt {ι : Type*} (n : ℕ) (J R : Finset ι) :
    Fin (Fintype.card (Letters n J R)) → ι :=
  fun i => letter n J R ((Fintype.equivFin (Letters n J R)).symm i)

theorem letterAt_sum {ι : Type*} (n : ℕ) (J R : Finset ι) (f : ι → ℝ) :
    (∑ i, f (letterAt n J R i)) = (n:ℝ)*(∑ j ∈ J, f j)+(∑ j ∈ R, f j) := by
  unfold letterAt
  rw [(Fintype.equivFin (Letters n J R)).symm.sum_comp (fun a => f (letter n J R a))]
  change (∑ i : (Fin n × J) ⊕ R, f (Sum.elim (fun p : Fin n × J => p.2.val)
    (fun i : R => i.val) i)) = _
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type]
  rw [Finset.sum_coe_sort J f, Finset.sum_coe_sort R f]
  simp

theorem letterAt_mem {ι : Type*} (n : ℕ) (J R : Finset ι) (hR : R ⊆ J)
    (i : Fin (Fintype.card (Letters n J R))) : letterAt n J R i ∈ J := by
  unfold letterAt
  cases h : (Fintype.equivFin (Letters n J R)).symm i with
  | inl p => exact p.2.property
  | inr r => exact hR r.property

/-- The integer word degree is finite and depends on later slot data, while
its number of complete cycles is controlled by target/total-width. -/
theorem crossing_word {ι : Type*} (J : Finset ι) (w energy : ι → ℝ)
    (δ target mesh : ℝ) (hm : 0 ≤ mesh)
    (hw : ∀ i ∈ J, 0 ≤ w i) (hwm : ∀ i ∈ J, w i ≤ mesh)
    (ht : 0 ≤ target) (hW : 0 < ∑ i ∈ J, w i)
    (henergy : δ*(∑ i ∈ J, w i) ≤ ∑ i ∈ J, energy i) :
    ∃ (r : ℕ) (f : Fin r → ι), (∀ i, f i ∈ J) ∧
      target ≤ ∑ i, w (f i) ∧ (∑ i, w (f i)) ≤ target+mesh ∧
      δ*(∑ i, w (f i)) ≤ ∑ i, energy (f i) ∧
      (r:ℝ) ≤ (target/(∑ i ∈ J, w i)+1)*(J.card:ℝ) := by
  obtain ⟨n,R,hR,hn,hlo,hhi,hE⟩ := BalancedSlotSelection.repeated_balanced_subset
    J w energy δ target mesh hm hw hwm ht hW henergy
  refine ⟨Fintype.card (Letters n J R),letterAt n J R,letterAt_mem n J R hR,?_,?_,?_,?_⟩
  · rwa [letterAt_sum]
  · rwa [letterAt_sum]
  · rwa [letterAt_sum,letterAt_sum]
  · have hc : (R.card:ℝ) ≤ J.card := by exact_mod_cast Finset.card_le_card hR
    change ((Fintype.card ((Fin n × J) ⊕ R) : ℕ):ℝ) ≤ _
    simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_coe,
      Nat.cast_add,Nat.cast_mul]
    have hh := mul_le_mul_of_nonneg_right hn (Nat.cast_nonneg J.card : (0:ℝ) ≤ J.card)
    nlinarith

theorem word_source_nonzero {r : ℕ} (pools : Fin r → Finset (Ideal O))
    (hzero : ∀ i, ∀ I ∈ pools i, I ≠ 0)
    (I : Ideal O) (hI : I ∈ tupleColumns (wordTuples pools)) : I ≠ 0 := by
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
  have hmem : ∀ i, v i ∈ pools i := by simpa only [wordTuples,Fintype.mem_piFinset] using hv
  exact Finset.prod_ne_zero_iff.mpr fun i _ => hzero i (v i) (hmem i)

theorem word_source_norm {r : ℕ} (pools : Fin r → Finset (Ideal O))
    (bounds : Fin r → ℝ)
    (hN : ∀ i, ∀ I ∈ pools i, (Ideal.absNorm I:ℝ) ≤ bounds i)
    (I : Ideal O) (hI : I ∈ tupleColumns (wordTuples pools)) :
    (Ideal.absNorm I:ℝ) ≤ ∏ i, bounds i := by
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
  have hmem : ∀ i, v i ∈ pools i := by simpa only [wordTuples,Fintype.mem_piFinset] using hv
  simp only [tupleProduct,map_prod,Nat.cast_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
    (fun i _ => hN i (v i) (hmem i))

theorem word_source_norm_rpow {r : ℕ} (pools : Fin r → Finset (Ideal O))
    (width : Fin r → ℝ) (Z : ℝ) (hZ : 0 < Z)
    (hN : ∀ i, ∀ I ∈ pools i, (Ideal.absNorm I:ℝ) ≤ 2*Z^(width i))
    (I : Ideal O) (hI : I ∈ tupleColumns (wordTuples pools)) :
    (Ideal.absNorm I:ℝ) ≤ 2^r*Z^(∑ i, width i) := by
  have hh := word_source_norm pools (fun i => 2*Z^(width i)) hN I hI
  simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
    Fintype.card_fin,← Real.rpow_sum_of_pos hZ] using hh

def amplifierSources {N r : ℕ} (d : SelectedSlotData N) (f : Fin r → Fin N) : Finset (Ideal O) :=
  tupleColumns (wordTuples (fun i => d.sources (f i)))

def amplifierCoefficient {N r : ℕ} (d : SelectedSlotData N) (f : Fin r → Fin N)
    (I : Ideal O) : ℂ :=
  tupleCoefficient (wordTuples (fun i => d.sources (f i)))
    (wordCoefficient (fun i => d.coefficient (f i))) I

def wordWidth {N r : ℕ} (d : SelectedSlotData N) (f : Fin r → Fin N) : ℝ :=
  ∑ i, d.width (f i)

def wordScale {N r : ℕ} (d : SelectedSlotData N) (f : Fin r → Fin N) (Z : ℝ) : ℝ :=
  2^r*Z^(wordWidth d f)

/-- An actual amplifier is produced from common individual-amplitude cells.
Its coefficients, response, support and both divisor losses are proved,
including the zero ideal and all non-squarefree merged products.

The explicit factors depending on r are late constants. The degree bound
is uniform in the analytic scale once target and positive total width are
bounded; thus they do not multiply the requested exponent loss by N.
-/
theorem slot_crossing_amplification {N : ℕ} (d : SelectedSlotData N)
    (rows : Finset O) (S : Finset (Ideal O)) (Z mesh C L δ target ε : ℝ)
    (hZ : 1 ≤ Z) (hm : 0 ≤ mesh) (hC : 0 ≤ C) (hL : 0 ≤ L) (ht : 0 ≤ target)
    (hε : 0 < ε) (hbounded : d.Bounded Z mesh C) (hselected : d.Selects Z rows)
    (hwidth : 0 < ∑ i, d.width i) (hslope : d.HasSlope δ)
    (hS : ∀ I ∈ S, (Ideal.absNorm I:ℝ) ≤ L) :
    ∃ (r : ℕ) (f : Fin r → Fin N),
      target ≤ wordWidth d f ∧ wordWidth d f ≤ target+mesh ∧
      (r:ℝ) ≤ (target/(∑ i, d.width i)+1)*N ∧
      (∀ I ∈ amplifierSources d f, I ≠ 0 ∧ (Ideal.absNorm I:ℝ) ≤ wordScale d f Z) ∧
      (∀ I ∈ idealProductSources (S.erase 0) (amplifierSources d f),
        I ≠ 0 ∧ (Ideal.absNorm I:ℝ) ≤ L*wordScale d f Z) ∧
      selectedNorm rows S ≤
        (wordDivisorConstant r ε hε*(wordScale d f Z)^ε*C^r)*
          idealDivisorConstant ε hε*(L*wordScale d f Z)^ε*
          selectedNorm rows (idealProductSources (S.erase 0) (amplifierSources d f))/
            Z^(δ*wordWidth d f) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  obtain ⟨r,f,hf,hlo,hhi,henergy,hdegree⟩ := crossing_word Finset.univ d.width d.energy
    δ target mesh hm (fun i _ => hbounded.width_nonneg i)
    (fun i _ => hbounded.width_le_mesh i) ht hwidth hslope
  have hdegree' : (r:ℝ) ≤ (target/(∑ i, d.width i)+1)*N := by simpa using hdegree
  have hX : 1 ≤ wordScale d f Z := by
    have hpow : 1 ≤ Z^(wordWidth d f) :=
      Real.one_le_rpow hZ (by
        change 0 ≤ ∑ i, d.width (f i)
        exact Finset.sum_nonneg fun i _ => hbounded.width_nonneg (f i))
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) hpow
  have hsource (I : Ideal O) (hI : I ∈ amplifierSources d f) :
      I ≠ 0 ∧ (Ideal.absNorm I:ℝ) ≤ wordScale d f Z := by
    constructor
    · exact word_source_nonzero _ (fun i => hbounded.source_nonzero (f i)) I hI
    · exact word_source_norm_rpow _ (fun i => d.width (f i)) Z hZ0
        (fun i => hbounded.source_norm (f i)) I hI
  have hmerged (I : Ideal O)
      (hI : I ∈ idealProductSources (S.erase 0) (amplifierSources d f)) :
      I ≠ 0 ∧ (Ideal.absNorm I:ℝ) ≤ L*wordScale d f Z := by
    obtain ⟨A,hA,B,hB,rfl⟩ := (mem_idealProductSources _ _ _).mp hI
    have hA0 : A ≠ 0 := (Finset.mem_erase.mp hA).1
    have hA1 : (Ideal.absNorm A:ℝ) ≤ L := hS A (Finset.mem_erase.mp hA).2
    have hB1 := hsource B hB
    refine ⟨mul_ne_zero hA0 hB1.1,?_⟩
    rw [map_mul,Nat.cast_mul]
    exact mul_le_mul hA1 hB1.2 (Nat.cast_nonneg _) hL
  have hmass : (∑ I : amplifierSources d f, ‖amplifierCoefficient d f I.val‖^2) ≤
      wordDivisorConstant r ε hε*(wordScale d f Z)^ε*C^r := by
    rw [Finset.sum_coe_sort _ (fun I => ‖amplifierCoefficient d f I‖^2)]
    have hh := word_square_mass (fun i => d.sources (f i))
      (fun i => d.coefficient (f i)) (fun _ => C)
      (fun i => hbounded.coefficient_mass (f i)) ε (wordScale d f Z) hε hX
      (fun I hI => (hsource I hI).1) (fun I hI => (hsource I hI).2)
    simpa only [amplifierSources,amplifierCoefficient,Finset.prod_const,
      Finset.card_univ,Fintype.card_fin] using hh
  have hresponse (z : rows) : Z^(δ*wordWidth d f) ≤
      ‖∑ I : amplifierSources d f, amplifierCoefficient d f I.val*idealRowHom z.val I.val‖^2 := by
    rw [Finset.sum_coe_sort _ (fun I => amplifierCoefficient d f I*idealRowHom z.val I)]
    apply (Real.rpow_le_rpow_of_exponent_le hZ henergy).trans
    exact word_response_rpow _ _ (fun i => d.energy (f i)) z.val Z hZ0
      (fun i => hselected z.val z.property (f i))
  refine ⟨r,f,hlo,hhi,hdegree',hsource,hmerged,?_⟩
  have hX0 : 0 ≤ wordScale d f Z := zero_le_one.trans hX
  have hmass0 : 0 ≤ wordDivisorConstant r ε hε*(wordScale d f Z)^ε*C^r :=
    mul_nonneg (mul_nonneg (wordDivisorConstant_pos r ε hε).le
      (Real.rpow_nonneg hX0 _)) (pow_nonneg hC _)
  calc
    selectedNorm rows S = selectedNorm rows (S.erase 0) := (selectedNorm_erase_zero rows S).symm
    _ ≤ _ := selectedNorm_inverse_amplification_small_power rows (S.erase 0)
      (amplifierSources d f) (idealProductSources (S.erase 0) (amplifierSources d f))
      (fun _ hI _ hJ => mul_mem_idealProductSources hI hJ)
      (fun I => amplifierCoefficient d f I.val) (Z^(δ*wordWidth d f))
      (wordDivisorConstant r ε hε*(wordScale d f Z)^ε*C^r) (L*wordScale d f Z) ε
      (Real.rpow_pos_of_pos hZ0 _) hmass0 (mul_nonneg hL hX0) hε hresponse hmass
      (fun I hI => (hmerged I hI).1) (fun I hI => (hmerged I hI).2)

end
end Qrh.JointDetector.SlotWordProducer

#print axioms Qrh.JointDetector.SlotWordProducer.crossing_word
#print axioms Qrh.JointDetector.SlotWordProducer.word_source_norm_rpow
#print axioms Qrh.JointDetector.SlotWordProducer.slot_crossing_amplification
