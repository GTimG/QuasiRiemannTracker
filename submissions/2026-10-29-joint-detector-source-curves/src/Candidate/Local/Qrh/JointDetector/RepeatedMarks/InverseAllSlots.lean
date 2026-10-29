/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SmallSlots

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped Classical BigOperators ComplexConjugate
open Set OAI OAI.SevenEighths ConcreteTraceCRT
open HeckeFamily HeckeDyadic HeckeInverseAmplification CanonicalRowCompletion
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount
open CenteredMomentCommonMaskExpansion CenteredMomentNaturalRowSource CenteredMomentCommonMaskEnergy
open CenteredMomentSecondHeightFamily CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentDetectorDictionary Deletion26 DetectorDictionaryInverseRawInitialGates
local notation "O" => HeckeFamily.O

/-- All finite source slots, including slots shorter than the fixed
modulus. Their cost is one later constant, with no new mesh or power loss. -/
theorem normalized_inverse_marked_energy_no_separation (W : ℝ → ℂ) (lo hi εm : ℝ)
    (hWs : Function.support W ⊆ Icc (1:ℝ) 2) (hW : Continuous W)
    (hεm : 0 < εm) (K : ℕ) :
    ∃ degree : ℕ, ∀ data : RowData, ∃ C U₀ : ℝ, 0<C ∧ 1<U₀ ∧
      ∀ U : ℝ, U₀≤U → ∀ {ι : Type} [Fintype ι] [DecidableEq ι], Fintype.card ι≤K →
      ∀ (L : ι → Finset (Ideal O)) (ell : ι → ℝ),
        (∀ i,0≤ell i) → (∀ i,∀ P∈L i,Prime P) →
        (∀ i,∀ P∈L i,((P.absNorm:ℝ)/U^(ell i))∈Icc (1:ℝ) 2) →
      ∀ (η : Character) (m A root : O) (ν : ι → Character)
        (σslot vslot : ι → ℝ) (tslot : ℝ),
        (∀ i,lo≤σslot i) → (∀ i,σslot i≤hi) →
      ∀ r : ℝ,0≤r → r+2*(∑ i,ell i)<1 → 2*r+8*(∑ i,ell i)<3 →
      ∀ rows : Finset NonzeroElement, (∀ u∈rows,‖eisEmbedding u.val‖^2≤U) →
      ∀ (χ : NonzeroElement → Character) (reverse : Bool),
        (∀ u∈rows,∀ I : Ideal O, idealCoeff (χ u) I =
          if reverse then conj (idealCoeff (data.character u) I) else idealCoeff (data.character u) I) →
      ∀ tstar : ℝ,∀ n : ℕ,n≤2 → ∀ σ∈Icc (0:ℝ) 1,
      ∀ height freq : ℝ,0≤height → freq∈Icc (-height) height →
      (∑ u∈rows,‖polynomial (χ u) true
        ((logProfile^[n]) (inverseTest U tstar r)) (U^r) σ freq *
          (∏ i, normalizedSlot η m A (u.val*root^6) (L i)
            (fun I => idealCoeff (ν i) I*
              HeckePrimeAnnular.annularWeight W (U^(ell i)) (σslot i) (vslot i) I)
            tslot (U^(ell i)))‖^2) ≤ (C*(1+height)^degree)*U^(1+εm) := by
  obtain ⟨B,hB,hcoeff⟩ := annular_coefficient_bounds W 1 2 lo hi (by norm_num) hWs hW
  obtain ⟨degree,henergy⟩ := normalized_inverse_marked_energy W lo hi εm hWs hW hεm K
  refine ⟨degree,?_⟩
  intro data
  obtain ⟨C,U₀,hC,hU₀,henergy⟩ := henergy data
  let D := ((deletedBase data).modulus.absNorm:ℝ)
  let cost := max 1 (256*(max 1 D)*(max 1 B))
  have hcost : 1 ≤ cost := le_max_left _ _
  refine ⟨cost^(2*K)*C,U₀,mul_pos (pow_pos (zero_lt_one.trans_le hcost) _) hC,hU₀,?_⟩
  intro U hU ι inst dec hK L ell hell hp hratio η m A root ν σslot vslot tslot hσlo hσhi
    r hr hfirst hsecond rows hrows χ reverse hχ tstar n hn σ hσ height freq hh ht
  have hUp : 0<U := zero_lt_one.trans (hU₀.trans_le hU)
  have hU1 : 1≤U := (hU₀.trans_le hU).le
  let large : Finset ι := Finset.univ.filter (fun j => D<U^(ell j))
  let β := fun j I => idealCoeff (ν j) I*
    HeckePrimeAnnular.annularWeight W (U^(ell j)) (σslot j) (vslot j) I
  let F := fun j (u : NonzeroElement) => normalizedSlot η m A (u.val*root^6)
    (L j) (β j) tslot (U^(ell j))
  let factor := fun u => polynomial (χ u) true ((logProfile^[n]) (inverseTest U tstar r)) (U^r) σ freq
  have hsmall (u : NonzeroElement) (hu : u∈rows) (j : ι)
      (hj : j∈(Finset.univ:Finset ι)\large) : ‖F j u‖≤cost := by
    have hnot : ¬D<U^(ell j) := by simpa only [large,Finset.mem_filter,Finset.mem_univ,true_and] using (Finset.mem_sdiff.mp hj).2
    have hP : U^(ell j)≤D := le_of_not_gt hnot
    dsimp [F]
    rw [normalizedSlot_root_eq_direct]
    apply (directPrimeSlot_small_norm u.val (L j)
      (maskedDirectCoefficient η m A root (β j) tslot) (U^(ell j)) (max 1 D) (max 1 B)
      (Real.one_le_rpow hU1 (hell j)) (hP.trans (le_max_right _ _))
      (zero_le_one.trans (le_max_left _ _)) (fun I hI => (hp j I hI).ne_zero)
      (fun I hI => (div_le_iff₀ (Real.rpow_pos_of_pos hUp _)).mp (hratio j I hI).2)
      (fun I hI => maskedDirectCoefficient_norm η m A root (β j) tslot I _
        ((hcoeff (ν j) (U^(ell j)) (σslot j) (vslot j) tslot
          (Real.rpow_pos_of_pos hUp _) (hσlo j) (hσhi j) I (hp j I hI).ne_zero).trans
          (le_max_right _ _)))).trans (le_max_right _ _)
  have hcard : Fintype.card large≤K :=
    (Fintype.card_le_of_injective (fun j : large => j.val) Subtype.val_injective).trans hK
  have hsum : (∑ j : large,ell j.val)≤∑ j,ell j :=
    RepeatedPrimeSlots.sum_comp_le_total (fun j : large => j.val) Subtype.val_injective ell hell
  have he := henergy U hU hcard (fun j : large => L j.val) (fun j => ell j.val)
    (fun j => hell j.val) (fun j => hp j.val) (fun j => hratio j.val)
    (fun j => (Finset.mem_filter.mp j.property).2) η m A root
    (fun j => ν j.val) (fun j => σslot j.val) (fun j => vslot j.val) tslot
    (fun j => hσlo j.val) (fun j => hσhi j.val) r hr (by linarith) (by linarith)
    rows hrows χ reverse hχ tstar n hn σ hσ height freq hh ht
  have helarge : (∑ u∈rows,‖factor u*(∏ j∈large,F j u)‖^2)≤
      (C*(1+height)^degree)*U^(1+εm) := by
    change (∑ u∈rows,‖factor u*(∏ j : large,F j.val u)‖^2)≤_ at he
    have hprod (u : NonzeroElement) : (∏ j : large,F j.val u) = ∏ j∈large,F j u :=
      Finset.prod_coe_sort large (fun j => F j u)
    simp_rw [hprod] at he
    exact he
  have htotal := finite_short_factor_cost rows large F factor cost
    ((C*(1+height)^degree)*U^(1+εm)) K hcost hK hsmall helarge
  convert htotal using 1
  ring

end
end Qrh.JointDetector.RepeatedMarks
