import Candidate.Cycle63.Marked.ActualRowwiseMarkedInverse
import Candidate.Cycle63.Marked.ActualRowwiseMarkedPlain
import Candidate.Cycle63.Density.NaturalEndpoint
import Candidate.Cycle63.Marked.Route.ActualUnmarkedGates

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace OAI.SevenEighths.Cycle63ActualMarked
open HeckeFamily HeckeDyadic HeckeInverseAmplification ActualEisensteinCubic
open ConcreteTraceCRT CenteredMomentCommonMaskExpansion CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentSecondHeightFamily CanonicalRowCompletion
open HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount HeckeDetectorCoefficientTransfer
open LocalMoment ProbeHighRowFamily DetectorDictionaryInverseRawInitialGates
local notation "O" => HeckeFamily.O

theorem momentElement_injective : Function.Injective momentElement := by
  intro u v h
  exact Subtype.ext (congrArg (fun z : NonzeroElement=>z.val) h)

/-- Actual marked inverse energy pulled back to the sixth-power-free row
population used by the detector count. No inverse-moment premise remains. -/
theorem actual_free_inverse_energy (W : ℝ→ℂ) (lo hi εm : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hεm : 0<εm) (K : ℕ) :
    ∃degree : ℕ,∀data : RowData,∃C U₀ : ℝ,0<C ∧ 1<U₀ ∧
      ∀U : ℝ,U₀≤U → ∀{ι : Type}[Fintype ι][DecidableEq ι],Fintype.card ι≤K →
      ∀(L : ι→Finset (Ideal O))(ell : ι→ℝ),
      (∀s,0≤ell s) → (∀s,∀P∈L s,Prime P) →
      (∀s,∀P∈L s,((P.absNorm:ℝ)/U^(ell s))∈Icc (1:ℝ) 2) →
      (∀s,((deletedBase data).modulus.absNorm:ℝ)<U^(ell s)) →
      ∀(ηslot : Character)(ν : ι→ Character)(σslot vslot : ι→ℝ)(choice : FreeRow→ℝ),
      (∀s,lo≤σslot s) → (∀s,σslot s≤hi) →
      ∀r : ℝ,0≤ r → r+2*(∑s,ell s)<1 → 2*r+8*(∑s,ell s)<3 →
      ∀rows : Finset FreeRow,(∀u∈rows,‖eisEmbedding u.val‖^2≤U) →
      ∀χ : FreeRow→ Character,
      (∀u∈rows,∀I,idealCoeff (χ u) I=idealCoeff (data.character (momentElement u)) I) →
      ∀tstar : ℝ,∀n : ℕ,n≤2 → ∀σ∈Icc (0:ℝ) 1,
      ∀height t : ℝ,0≤height → t∈Icc (-height) height →
      (∀u∈rows,|choice u|≤height) →
      (∑u∈rows,‖polynomial (χ u) true ((logProfile^[n]) (inverseTest U tstar r)) (U^r) σ t*
        (∏s,naturalSlot (naturalRow ηslot u.val u.property.1).character (L s)
          (fun I=>idealCoeff (ν s) I*HeckePrimeAnnular.annularWeight W (U^(ell s))
            (σslot s) (choice u+vslot s) I) (U^(ell s)))‖^2)≤
        (C*(1+height)^degree)*U^(1+εm) := by
  obtain ⟨degree,hfield⟩ := Deletion26.annular_rowwise_inverse_marked_energy W lo hi εm hWs hW hεm K
  refine ⟨degree,?_⟩
  intro data
  obtain ⟨C,U₀,hC,hU₀,hfield⟩ := hfield data
  refine ⟨C,U₀,hC,hU₀,?_⟩
  intro U hU ι inst dec hK L ell hell hprime hratio hlarge ηslot ν σslot vslot choice hσlo hσhi
    r hr hcap1 hcap2 rows hrows χ hcoeff tstar n hn σ hσ height t hh ht hchoice
  let choice' : NonzeroElement→ℝ := Function.extend momentElement choice (fun _=>0)
  have hchoice' (u : FreeRow) : choice' (momentElement u)=choice u :=
    momentElement_injective.extend_apply choice (fun _=>0) u
  have hnorm (u : NonzeroElement) (hu : u∈rows.image momentElement) : ‖eisEmbedding u.val‖^2≤U := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
    exact hrows v hv
  have hheight (u : NonzeroElement) (hu : u∈rows.image momentElement) : |choice' u|≤height := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
    rw [hchoice']
    exact hchoice v hv
  have he := hfield U hU hK L ell hell hprime hratio hlarge ηslot ν σslot vslot choice'
    hσlo hσhi r hr hcap1 hcap2 (rows.image momentElement) hnorm tstar false n hn σ hσ
    height t hh ht hheight
  rw [Finset.sum_image (fun u _ v _ huv=>momentElement_injective huv)] at he
  simp only [orientedProfile,Bool.false_eq_true,ite_false,hchoice'] at he
  convert he using 1
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [polynomial_eq_of_idealCoeff (χ u) (data.character (momentElement u)) (hcoeff u hu)]
  rfl

end OAI.SevenEighths.Cycle63ActualMarked
