/- Adapted from PR63 gao-balanced-marked-20261017; Apache-2.0. Exact source provenance is in evidence/homogeneous-gain/upstream-provenance.json. -/
import Submissions.hailey_collet_1252270103.Record12518109Gain.Upstream.DeletionOverlapEnergy
import Submissions.hailey_collet_1252270103.Record12518109Gain.Upstream.ColoringEnergy

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Record12518109GainDeletion
noncomputable section
open scoped Classical BigOperators
open HeckeFamily HeckeDyadic HeckeInverseAmplification Set ActualEisensteinCubic
open ConcreteTraceCRT
open CenteredMomentCommonMaskExpansion CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentSecondHeightFamily
open CanonicalRowCompletion
open DetectorDictionaryInverseRawInitialGates
local notation "O" => HeckeFamily.O

theorem overlapping_inverse_marked_energy (εm B : ℝ) (hεm : 0<εm) (hB : 1≤B) (K : ℕ) :
    ∃ degree : ℕ, ∀ data : RowData, ∃ C U₀ : ℝ, 0<C ∧ 1<U₀ ∧
      ∀ U : ℝ, U₀≤U → ∀ {ι : Type} [Fintype ι] [DecidableEq ι], Fintype.card ι≤K →
      ∀ (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ),
        (∀i,0≤ell i) → (∀i,∀P∈L i,Prime P) →
        (∀i,∀P∈L i,((P.absNorm : ℝ)/U^(ell i))∈Icc (1 : ℝ) 2) →
        (∀i,∀P∈L i,‖β i P‖≤B) →
        (∀i,((deletedBase data).modulus.absNorm : ℝ)<U^(ell i)) →
      ∀r : ℝ, 0≤r → r+2*(∑i,ell i)<1 → 2*r+8*(∑i,ell i)<3 →
      ∀rows : Finset NonzeroElement, (∀u∈rows,‖eisEmbedding u.val‖^2≤U) →
      ∀tstar : ℝ, ∀reverse : Bool, ∀n : ℕ,n≤2 → ∀σ∈Icc (0 : ℝ) 1,
      ∀height t : ℝ, 0≤height → t∈Icc (-height) height →
      (∑u∈rows,‖polynomial (data.character u) true
        ((HeckeDetectorRowwisePolynomial.logProfile^[n])
          (HeckeDetectorCoefficientTransfer.orientedProfile reverse
            (HeckeDetectorInverseFiberCount.inverseTest U tstar r))) (U^r) σ t *
          (∏i,directPrimeSlot u.val (L i) (β i) (U^(ell i)))‖^2) ≤
        (C*(1+height)^degree)*U^(1+εm) := by
  obtain ⟨degree,henergy⟩ := bounded_inverse_marked_energy εm B hεm hB K
  refine ⟨degree,?_⟩
  intro data
  obtain ⟨C,U₀,hC,hU₀,henergy⟩ := henergy data
  refine ⟨overlapCost B K*C,U₀,mul_pos (overlapCost_pos B hB K) hC,hU₀,?_⟩
  intro U hU ι inst dec hK L ell β hell hp hratio hβ hlarge r hr hfirst hsecond rows hrows
    tstar reverse n hn σ hσ height t hh ht
  have hU1 : 1<U := hU₀.trans_le hU
  have hUp : 0<U := zero_lt_one.trans hU1
  let D : NonzeroElement→ℂ := fun u=>polynomial (data.character u) true
    ((HeckeDetectorRowwisePolynomial.logProfile^[n])
      (HeckeDetectorCoefficientTransfer.orientedProfile reverse
        (HeckeDetectorInverseFiberCount.inverseTest U tstar r))) (U^r) σ t
  have hP (i : ι) : 1≤U^(ell i) := Real.one_le_rpow hU1.le (hell i)
  have hN (i : ι) (p : Ideal O) (hp' : p∈L i) : (p.absNorm:ℝ)≤2*U^(ell i) :=
    (div_le_iff₀ (Real.rpow_pos_of_pos hUp _)).mp (hratio i p hp').2
  have hsep : ∀{J : Type} [Fintype J] [DecidableEq J],
      ∀f : J→ι,Function.Injective f →∀L' : J→Finset (Ideal O),
      (∀j,L' j⊆L (f j)) →
      (((Finset.univ : Finset J) : Set J).PairwiseDisjoint L') →
      (∑v∈rows,‖D v*(∏j,directPrimeSlot v.val (L' j) (β (f j)) (U^(ell (f j))))‖^2)≤
        (C*(1+height)^degree)*U^(1+εm) := by
    intro J instJ decJ f hf L' hsub hdis
    have hJK : Fintype.card J≤K := (Fintype.card_le_of_injective f hf).trans hK
    have hsum : (∑j,ell (f j))≤∑i,ell i :=
      RepeatedPrimeSlots.sum_comp_le_total f hf ell hell
    exact henergy U hU hJK L' (fun j=>ell (f j)) (fun j=>β (f j))
      (fun j=>hell (f j)) (fun j p hp'=>hp (f j) p (hsub j hp')) hdis
      (fun j p hp'=>hratio (f j) p (hsub j hp'))
      (fun j p hp'=>hβ (f j) p (hsub j hp')) (fun j=>hlarge (f j))
      r hr (by linarith) (by linarith) rows hrows tstar reverse n hn σ hσ height t hh ht
  have he := overlapping_direct_energy rows (fun u=>u.val) D L β (fun i=>U^(ell i)) B
    ((C*(1+height)^degree)*U^(1+εm)) hB (by positivity) K hK hP hβ
    (fun i p hp'=> (hp i p hp').ne_zero) hN hsep
  convert he using 1
  ring

theorem overlapping_annular_inverse_marked_energy (W : ℝ → ℂ) (lo hi εm : ℝ)
    (hWs : Function.support W⊆Icc (1 : ℝ) 2) (hW : Continuous W)
    (hεm : 0<εm) (K : ℕ) :
    ∃ degree : ℕ, ∀ data : RowData, ∃ C U₀ : ℝ, 0<C ∧ 1<U₀ ∧
      ∀ U : ℝ, U₀≤U → ∀ {ι : Type} [Fintype ι] [DecidableEq ι], Fintype.card ι≤K →
      ∀ (L : ι → Finset (Ideal O)) (ell : ι → ℝ),
        (∀i,0≤ell i) → (∀i,∀P∈L i,Prime P) →
        (∀i,∀P∈L i,((P.absNorm : ℝ)/U^(ell i))∈Icc (1 : ℝ) 2) →
        (∀i,((deletedBase data).modulus.absNorm : ℝ)<U^(ell i)) →
      ∀ (ηslot : Character) (ν : ι → Character) (σslot vslot : ι → ℝ) (tslot : ℝ),
        (∀i,lo≤σslot i) → (∀i,σslot i≤hi) →
      ∀r : ℝ, 0≤r → r+2*(∑i,ell i)<1 → 2*r+8*(∑i,ell i)<3 →
      ∀rows : Finset NonzeroElement, (∀u∈rows,‖eisEmbedding u.val‖^2≤U) →
      ∀tstar : ℝ, ∀reverse : Bool, ∀n : ℕ,n≤2 → ∀σ∈Icc (0 : ℝ) 1,
      ∀height t : ℝ, 0≤height → t∈Icc (-height) height →
      (∑u∈rows,‖polynomial (data.character u) true
        ((HeckeDetectorRowwisePolynomial.logProfile^[n])
          (HeckeDetectorCoefficientTransfer.orientedProfile reverse
            (HeckeDetectorInverseFiberCount.inverseTest U tstar r))) (U^r) σ t *
          (∏i,naturalSlot (naturalRow ηslot u.val u.property).character (L i)
            (heightCoefficient (fun I=>idealCoeff (ν i) I*
              HeckePrimeAnnular.annularWeight W (U^(ell i)) (σslot i) (vslot i) I) tslot)
            (U^(ell i)))‖^2) ≤ (C*(1+height)^degree)*U^(1+εm) := by
  obtain ⟨B,hB,hcoeff⟩ := annular_coefficient_bounds W 1 2 lo hi (by norm_num) hWs hW
  obtain ⟨degree,henergy⟩ := overlapping_inverse_marked_energy εm (max 1 B) hεm
    (le_max_left _ _) K
  refine ⟨degree,?_⟩
  intro data
  obtain ⟨C,U₀,hC,hU₀,henergy⟩ := henergy data
  refine ⟨C,U₀,hC,hU₀,?_⟩
  intro U hU ι inst dec hK L ell hell hp hratio hlarge ηslot ν σslot vslot tslot hσlo hσhi
    r hr hfirst hsecond rows hrows tstar reverse n hn σ hσ height t hh ht
  have hUp : 0<U := zero_lt_one.trans (hU₀.trans_le hU)
  let β := fun i=>heightCoefficient (fun I=>idealCoeff (ν i) I*
    HeckePrimeAnnular.annularWeight W (U^(ell i)) (σslot i) (vslot i) I) tslot
  let coeff := fun i I=>idealCoeff ηslot I*idealRowHom (fixedBadMask^6) I*β i I
  have hc (i : ι) (I : Ideal O) (hI : I∈L i) : ‖coeff i I‖≤ max 1 B := by
    apply natural_direct_coeff_bound ηslot (β i) I (max 1 B)
    exact (hcoeff (ν i) (U^(ell i)) (σslot i) (vslot i) tslot
      (Real.rpow_pos_of_pos hUp _) (hσlo i) (hσhi i) I (hp i I hI).ne_zero).trans
        (le_max_right _ _)
  have he := henergy U hU hK L ell coeff hell hp hratio hc hlarge
    r hr hfirst hsecond rows hrows tstar reverse n hn σ hσ height t hh ht
  simpa only [naturalSlot_eq_direct] using he

end
end OAI.SevenEighths.Record12518109GainDeletion
#print axioms OAI.SevenEighths.Record12518109GainDeletion.overlapping_inverse_marked_energy

#print axioms OAI.SevenEighths.Record12518109GainDeletion.overlapping_annular_inverse_marked_energy
