import Candidate.Cycle62.Marked.DeletionInverseOverlap
import Candidate.Cycle62.Marked.NaturalSlotHeight

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Deletion26
noncomputable section
open scoped Classical BigOperators ContDiff
open HeckeFamily HeckeDyadic HeckeInverseAmplification Set ActualEisensteinCubic
open ConcreteTraceCRT
open CenteredMomentCommonMaskExpansion CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentSecondHeightFamily
open CanonicalRowCompletion
open DetectorDictionaryInverseRawInitialGates
local notation "O" => HeckeFamily.O

/-- The full actual inverse moment with row-dependent common prime height.
Fixed-profile Fourier uniformity and finite interpolation pay one height power. -/
theorem annular_rowwise_inverse_marked_energy (W : ℝ → ℂ) (lo hi εm : ℝ)
    (hWs : Function.support W⊆Icc (1 : ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hεm : 0<εm) (K : ℕ) :
    ∃ degree : ℕ, ∀ data : RowData, ∃ C U₀ : ℝ, 0<C ∧ 1<U₀ ∧
      ∀ U : ℝ, U₀≤U → ∀ {ι : Type} [Fintype ι] [DecidableEq ι], Fintype.card ι≤K →
      ∀ (L : ι → Finset (Ideal O)) (ell : ι → ℝ),
        (∀i,0≤ell i) → (∀i,∀P∈L i,Prime P) →
        (∀i,∀P∈L i,((P.absNorm : ℝ)/U^(ell i))∈Icc (1 : ℝ) 2) →
        (∀i,((deletedBase data).modulus.absNorm : ℝ)<U^(ell i)) →
      ∀ (ηslot : Character) (ν : ι → Character) (σslot vslot : ι → ℝ) (choice : NonzeroElement→ℝ),
        (∀i,lo≤σslot i) → (∀i,σslot i≤hi) →
      ∀r : ℝ, 0≤r → r+2*(∑i,ell i)<1 → 2*r+8*(∑i,ell i)<3 →
      ∀rows : Finset NonzeroElement, (∀u∈rows,‖eisEmbedding u.val‖^2≤U) →
      ∀tstar : ℝ, ∀reverse : Bool, ∀n : ℕ,n≤2 → ∀σ∈Icc (0 : ℝ) 1,
      ∀height t : ℝ, 0≤height → t∈Icc (-height) height →
      (∀u∈rows,|choice u|≤height) →
      (∑u∈rows,‖polynomial (data.character u) true
        ((HeckeDetectorRowwisePolynomial.logProfile^[n])
          (HeckeDetectorCoefficientTransfer.orientedProfile reverse
            (HeckeDetectorInverseFiberCount.inverseTest U tstar r))) (U^r) σ t *
          (∏i,naturalSlot (naturalRow ηslot u.val u.property).character (L i)
            (fun I=>idealCoeff (ν i) I*
              HeckePrimeAnnular.annularWeight W (U^(ell i)) (σslot i) (choice u+vslot i) I)
            (U^(ell i)))‖^2) ≤ (C*(1+height)^degree)*U^(1+εm) := by
  have hnode (node : Fin (K+1)) := overlapping_annular_inverse_marked_energy
    (Cycle62MarkedHeight.commonProfile W node.val) lo hi εm
    ((Cycle62MarkedHeight.commonProfile_support W node.val).trans hWs)
    (Cycle62MarkedHeight.commonProfile_smooth W 1 2 (by norm_num) hWs hW node.val).continuous
    hεm K
  choose degree hfield using hnode
  let J := ∑node,degree node
  let Hcost := Cycle62MarkedHeight.commonProfileCost K
  have hHcost : 0<Hcost := zero_lt_one.trans_le (Cycle62MarkedHeight.commonProfileCost_ge_one K)
  refine ⟨J+1,?_⟩
  intro data
  choose C U₀ hC hU₀ hb using fun node=>hfield node data
  let Csum := ∑node,C node
  let Ubase := 1+∑node,U₀ node
  have hne : (Finset.univ : Finset (Fin (K+1))).Nonempty := ⟨⟨0,by omega⟩,Finset.mem_univ _⟩
  have hCsum : 0<Csum := Finset.sum_pos (fun node _=>hC node) hne
  have hUbase : 1<Ubase := by
    have hh : 0<∑node,U₀ node := Finset.sum_pos (fun node _=>lt_trans zero_lt_one (hU₀ node)) hne
    dsimp [Ubase]
    linarith
  refine ⟨4*Hcost*Csum,Ubase,by positivity,hUbase,?_⟩
  intro U hU ι inst dec hK L ell hell hp hratio hlarge ηslot ν σslot vslot choice hσlo hσhi
    r hr hfirst hsecond rows hrows tstar reverse n hn σ hσ height t hh ht hchoice
  have hUp : 0<U := zero_lt_one.trans (hUbase.trans_le hU)
  let factor := fun u=>polynomial (data.character u) true
    ((HeckeDetectorRowwisePolynomial.logProfile^[n])
      (HeckeDetectorCoefficientTransfer.orientedProfile reverse
        (HeckeDetectorInverseFiberCount.inverseTest U tstar r))) (U^r) σ t
  let E := (Csum*(1+height)^J)*U^(1+εm)
  have hE : 0≤E := by dsimp [E];positivity
  have hmoment (node : Fin (K+1)) (t' : ℝ)(ht' : t'∈Icc (-height) height) :
      (∑u∈rows,‖factor u*(∏i,naturalSlot (naturalRow ηslot u.val u.property).character (L i)
        (fun I=>idealCoeff (ν i) I*
          HeckePrimeAnnular.annularWeight (Cycle62MarkedHeight.commonProfile W node.val)
            (U^(ell i)) (σslot i) (t'+vslot i) I) (U^(ell i)))‖^2)≤E := by
    have hUnode : U₀ node≤U := by
      have hh := Finset.single_le_sum (fun j _=>(lt_trans zero_lt_one (hU₀ j)).le)
        (Finset.mem_univ node)
      dsimp [Ubase] at hU
      linarith
    have he := hb node U hUnode hK L ell hell hp hratio hlarge ηslot ν σslot
      (fun i=>t'+vslot i) 0 hσlo hσhi r hr hfirst hsecond rows hrows
      tstar reverse n hn σ hσ height t hh ht
    have hzero (β : Ideal O→ℂ) : heightCoefficient β 0=β := by
      funext I
      simp [heightCoefficient]
    simp only [hzero] at he
    apply he.trans
    have hc : C node≤Csum := Finset.single_le_sum (fun j _=>(hC j).le) (Finset.mem_univ node)
    have hj : degree node≤J := Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ node)
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hUp.le _)
    exact mul_le_mul hc (pow_le_pow_right₀ (by linarith) hj) (by positivity) hCsum.le
  have he := Cycle62MarkedHeight.naturalSlot_rowwise_energy rows Finset.univ K
    (by simpa only [Finset.card_univ] using hK)
    (fun u=> (naturalRow ηslot u.val u.property).character) L
    (fun i _ I hI=>(hp i I hI).ne_zero) (fun i I=>idealCoeff (ν i) I) W
    (fun i=>U^(ell i)) σslot vslot
    (fun i _=>Real.rpow_pos_of_pos hUp _) factor (-height) height E (by linarith)
    hE choice (fun u hu=>abs_le.mp (hchoice u hu)) hmoment
  apply he.trans
  change (1+2*(height- -height))*Hcost*((Csum*(1+height)^J)*U^(1+εm))≤_
  calc
    _≤(4*(1+height))*Hcost*((Csum*(1+height)^J)*U^(1+εm)) := by
      gcongr
      linarith
    _=_ := by rw [pow_succ];ring

end
end OAI.SevenEighths.Deletion26
#print axioms OAI.SevenEighths.Deletion26.annular_rowwise_inverse_marked_energy
