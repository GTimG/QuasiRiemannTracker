import Candidate.Cycle63.Marked.DeletionInverse
import Candidate.Cycle63.Marked.DeletionAnnular

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Deletion26
noncomputable section
open scoped Classical BigOperators
open HeckeFamily HeckeDyadic HeckeInverseAmplification Set ActualEisensteinCubic
open ConcreteTraceCRT
open CenteredMomentCommonMaskExpansion CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentSecondHeightFamily
open CanonicalRowCompletion
open DetectorDictionaryInverseRawInitialGates
local notation "O" => HeckeFamily.O

/-- Exact conversion of an actual natural prime slot, with arbitrary
relative coefficient, into the coefficient-uniform marked inverse input. -/
theorem naturalSlot_eq_direct {η : Character} {u : O} (F : NaturalRow η u)
    (L : Finset (Ideal O)) (β : Ideal O → ℂ) (P : ℝ) :
    naturalSlot F.character L β P = directPrimeSlot u L
      (fun I=>idealCoeff η I*idealRowHom (fixedBadMask^6) I*β I) P := by
  unfold naturalSlot directPrimeSlot
  congr 1
  refine Finset.sum_congr rfl fun I hI => ?_
  rw [F.ideal,idealRowHom_argument_mul]
  ring

theorem natural_direct_coeff_bound (η : Character) (β : Ideal O → ℂ)
    (I : Ideal O) (B : ℝ) (hβ : ‖β I‖≤B) :
    ‖idealCoeff η I*idealRowHom (fixedBadMask^6) I*β I‖≤B := by
  rw [norm_mul,norm_mul]
  have hbase : ‖idealCoeff η I‖*‖idealRowHom (fixedBadMask^6) I‖≤1 := by
    exact (mul_le_mul_of_nonneg_right (idealCoeff_norm_le_one η I) (norm_nonneg _)).trans
      (by simpa only [one_mul] using idealRowHom_norm (fixedBadMask^6) I)
  exact (mul_le_of_le_one_left (norm_nonneg _) hbase).trans hβ

theorem directPrimeSlot_const_mul (u : O) (L : Finset (Ideal O))
    (β : Ideal O → ℂ) (P : ℝ) (c : ℂ) :
    directPrimeSlot u L (fun I=>c*β I) P = c*directPrimeSlot u L β P := by
  unfold directPrimeSlot
  simp only [mul_assoc,←Finset.mul_sum]
  ring

theorem directPrimeSlot_div (u : O) (L : Finset (Ideal O))
    (β : Ideal O → ℂ) (P B : ℝ) (hB : B≠0) :
    directPrimeSlot u L β P = (B : ℂ)*directPrimeSlot u L (fun I=>β I/(B : ℂ)) P := by
  rw [←directPrimeSlot_const_mul]
  congr 2
  funext I
  rw [mul_comm (B : ℂ),div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hB)]

theorem direct_slot_energy_scale {ι Row : Type*} [Fintype ι]
    (rows : Finset Row) (u : Row → O) (D : Row → ℂ)
    (L : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (P : ι → ℝ) (B : ℝ) (hB : 0<B) :
    (∑v∈rows,‖D v*(∏i,directPrimeSlot (u v) (L i) (β i) (P i))‖^2) =
      B^(2*Fintype.card ι) *
        ∑v∈rows,‖D v*(∏i,directPrimeSlot (u v) (L i) (fun I=>β i I/(B : ℂ)) (P i))‖^2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hs : (∏i,directPrimeSlot (u v) (L i) (β i) (P i)) =
      (B : ℂ)^Fintype.card ι *
        (∏i,directPrimeSlot (u v) (L i) (fun I=>β i I/(B : ℂ)) (P i)) := by
    calc
      _ = ∏i,(B : ℂ)*directPrimeSlot (u v) (L i) (fun I=>β i I/(B : ℂ)) (P i) :=
        Finset.prod_congr rfl (fun i _=>directPrimeSlot_div _ _ _ _ B hB.ne')
      _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
  rw [hs]
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hB,mul_pow]
  rw [←pow_mul]
  ring

/-- Uniform coefficient-size version of the actual marked inverse moment.
The fixed cost is independent of the selected prime slots. -/
theorem bounded_inverse_marked_energy (εm B : ℝ) (hεm : 0<εm) (hB : 1≤B) (K : ℕ) :
    ∃ degree : ℕ, ∀ data : RowData, ∃ C U₀ : ℝ, 0<C ∧ 1<U₀ ∧
      ∀ U : ℝ, U₀≤U → ∀ {ι : Type} [Fintype ι] [DecidableEq ι], Fintype.card ι≤K →
      ∀ (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ),
        (∀i,0≤ell i) → (∀i,∀P∈L i,Prime P) →
        (((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint L) →
        (∀i,∀P∈L i,((P.absNorm : ℝ)/U^(ell i))∈Icc (1 : ℝ) 2) →
        (∀i,∀P∈L i,‖β i P‖≤B) →
        (∀i,((deletedBase data).modulus.absNorm : ℝ)<U^(ell i)) →
      ∀r : ℝ, 0≤ r → r+2*(∑i,ell i)<1 → 2*r+8*(∑i,ell i)<3 →
      ∀rows : Finset NonzeroElement, (∀u∈rows,‖eisEmbedding u.val‖^2≤U) →
      ∀tstar : ℝ, ∀reverse : Bool, ∀n : ℕ,n≤2 → ∀σ∈Icc (0 : ℝ) 1,
      ∀height t : ℝ, 0≤height → t∈Icc (-height) height →
      (∑u∈rows,‖polynomial (data.character u) true
        ((HeckeDetectorRowwisePolynomial.logProfile^[n])
          (HeckeDetectorCoefficientTransfer.orientedProfile reverse
            (HeckeDetectorInverseFiberCount.inverseTest U tstar r))) (U^r) σ t *
          (∏i,directPrimeSlot u.val (L i) (β i) (U^(ell i)))‖^2) ≤
        (C*(1+height)^degree)*U^(1+εm) := by
  obtain ⟨degree,henergy⟩ := actual_inverse_marked_energy εm hεm K
  refine ⟨degree,?_⟩
  intro data
  obtain ⟨C,U₀,hC,hU₀,henergy⟩ := henergy data
  have hBp : 0<B := zero_lt_one.trans_le hB
  refine ⟨B^(2*K)*C,U₀,mul_pos (pow_pos hBp _) hC,hU₀,?_⟩
  intro U hU ι inst dec hK L ell β hell hp hdis hratio hβ hlarge r hr hfirst hsecond rows hrows
    tstar reverse n hn σ hσ height t hh ht
  have hb (i : ι) (P : Ideal O) (hP : P∈L i) : ‖β i P/(B : ℂ)‖≤1 := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hBp]
    exact (div_le_one hBp).mpr (hβ i P hP)
  have he := henergy U hU hK L ell (fun i P=>β i P/(B : ℂ)) hell hp hdis hratio hb
    hlarge r hr hfirst hsecond rows hrows tstar reverse n hn σ hσ height t hh ht
  rw [direct_slot_energy_scale rows (fun u=>u.val) _ L β (fun i=>U^(ell i)) B hBp]
  apply (mul_le_mul_of_nonneg_left he (pow_nonneg hBp.le _)).trans
  calc
    _ ≤ B^(2*K)*((C*(1+height)^degree)*U^(1+εm)) := by
      apply mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hB (Nat.mul_le_mul_left 2 hK))
      have hUp : 0<U := (zero_lt_one.trans hU₀).trans_le hU
      positivity
    _ = _ := by ring

end
end OAI.SevenEighths.Deletion26
