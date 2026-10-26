/- Adapted from PR63 gao-balanced-marked-20261017; Apache-2.0. Exact source provenance is in evidence/homogeneous-gain/upstream-provenance.json. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.Bands
import Submissions.hailey_collet_1252270103.Record12518109Gain.Upstream.FinitePositiveEnergy

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61MarkedPlain
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Set
open HeckeFamily CenteredMomentEnergyBands CenteredMomentEnergyState
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentPositiveSummability CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
open CenteredMomentCommonMaskExpansion CenteredMomentWholeSlotDeletion
open CenteredMomentHeckeSlots CenteredMomentHeckeTwist CenteredMomentDetectorDictionary
open HeckeRowClosure HeckeDyadic
open ConcreteTraceCRT QuadraticInitialBound HeckeInverseAmplification
local notation "O" => HeckeFamily.O

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- A direct marked finite-row plain moment from the incumbent analytic
induction, with arbitrary fixed relative anchor and common slot profile.
It can therefore be applied to each common-profile interpolation node. -/
theorem actual_finite_marked_plain
    (W : ℝ→ℂ) (bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ U : ℝ)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ) (seminorms : Finset (ℕ×ℕ)) (C : ℝ)
    (hinput : PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
      Mcap ε κ U η₀ Q degree seminorms C)
    (slots : Finset α) (θ : slots→RayQuotient.Characters M H)
    (w σ v : slots→ℝ) (t height : ℝ)
    (hw : ∀s,0≤w s) (hwm : ∀s,w s≤Lslot)
    (hσlo : ∀s,lo≤σ s) (hσhi : ∀s,σ s≤hi)
    (hheight : 0≤height) (hv : ∀s,|v s|≤height)
    (st : NaturalState U Bmask bΦ) (hQ : st.fixedModulus=internalQ Q η₀)
    (hst : st.width≤Mcap) (p : Profiles a b) (X₁ X₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hXL₁ : X₁≤U^L) (hXL₂ : X₂≤U^L)
    (hcap : length U X₁+length U X₂+6*κ*(∑s,w s)≤st.width)
    (rows : Finset O) (hkeep : ∀u∈rows,st.radial.keep u)
    (hΦ : ∀x,0≤(st.radial.profile x).re)
    (hone : ∀u∈rows,st.radial.profile (‖eisEmbedding u‖^2/st.radial.scale)=1) :
    (∑u∈rows,‖positiveSlotRow st.character st.mask 1 u
      (p.profile 0) (p.profile 1)
      (fun s=>primePool M H bslot (U^(w s)))
      (fun s I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
        HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (v s) I)
      (fun s=>U^(w s)) t X₁ X₂‖^2)≤
        C*diagonalControl st.radial.profile*(p.control seminorms)^2*
          (1+|t|+height)^degree*U^(st.width+ε) := by
  have hK : 0<st.radial.scale := by
    rw [st.scale_eq]
    exact Real.rpow_pos_of_pos (zero_lt_one.trans_le st.base_ge_one) _
  have hfinite := finite_positive_energy (Slot:=slots) rows st.character st.mask 1 t
    (p.profile 0) (p.profile 1) b b X₁ X₂
    (fun x hx=>(p.support 0 hx).2) (fun x hx=>(p.support 1 hx).2)
    hX₁ hX₂ (fun s=>primePool M H bslot (U^(w s)))
    (fun s I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
      HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (v s) I)
    (fun s=>U^(w s)) st.radial.keep st.radial.profile st.radial.scale hK hkeep hΦ hone
  exact hfinite.trans (hinput slots θ w σ v t height hw hwm hσlo hσhi hheight hv
    st hQ hst p X₁ X₂ hX₁ hX₂ hXL₁ hXL₂ hcap)

/-- The finite marked source estimate in the exact detector-polynomial and
natural-slot representation. The slot height is independent of the detector
height: it is absorbed in the arbitrary bounded external shifts `v`. -/
theorem actual_finite_marked_polynomials
    (W : ℝ→ℂ) (bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ U : ℝ)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ) (seminorms : Finset (ℕ×ℕ)) (C : ℝ)
    (hinput : PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
      Mcap ε κ U η₀ Q degree seminorms C)
    (slots : Finset α) (θ : slots→RayQuotient.Characters M H)
    (w σ v : slots→ℝ) (height : ℝ)
    (hw : ∀s,0≤w s) (hwm : ∀s,w s≤Lslot)
    (hσlo : ∀s,lo≤σ s) (hσhi : ∀s,σ s≤hi)
    (hheight : 0≤height) (hv : ∀s,|v s|≤height)
    (st : NaturalState U Bmask bΦ) (hQ : st.fixedModulus=internalQ Q η₀)
    (hst : st.width≤Mcap) (p : Profiles a b) (X₁ X₂ σd td : ℝ)
    (V₁ V₂ : ℝ→ℂ) (hp₁ : (p.profile 0 : ℝ→ℂ)=twistProfile V₁ σd td)
    (hp₂ : (p.profile 1 : ℝ→ℂ)=twistProfile V₂ σd td)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hXL₁ : X₁≤U^L) (hXL₂ : X₂≤U^L)
    (hcap : length U X₁+length U X₂+6*κ*(∑s,w s)≤st.width)
    (rows : Finset O) (χ : O→Character)
    (hrow : ∀u∈rows,∀n,elementCoeff (χ u) n=
      CanonicalRowCompletion.rowTwist (elementHom st.character) st.mask 1 (1*u) n)
    (hkeep : ∀u∈rows,st.radial.keep u) (hΦ : ∀x,0≤(st.radial.profile x).re)
    (hone : ∀u∈rows,st.radial.profile (‖eisEmbedding u‖^2/st.radial.scale)=1) :
    (∑u∈rows,‖polynomial (χ u) false V₁ X₁ σd td*
      polynomial (χ u) false V₂ X₂ σd td*
      ∏s,naturalSlot (χ u) (primePool M H bslot (U^(w s)))
        (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
          HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (v s) I)
        (U^(w s))‖^2)≤
      C*diagonalControl st.radial.profile*(p.control seminorms)^2*
        (1+height)^degree*U^(st.width+ε) := by
  have he := actual_finite_marked_plain M H hH W bslot a b bΦ Bmask L Lslot lo hi
    Mcap ε κ U η₀ Q degree seminorms C hinput slots θ w σ v 0 height
    hw hwm hσlo hσhi hheight hv st hQ hst p X₁ X₂ hX₁ hX₂ hXL₁ hXL₂ hcap
    rows hkeep hΦ hone
  simp only [abs_zero,add_zero] at he
  apply le_trans _ he
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro u hu
  rw [hp₁,hp₂,positiveSlotRow_eq_product st.character (χ u) st.mask 1 u
    (hrow u hu) V₁ V₂ _ _ _ X₁ X₂ σd td hX₁ hX₂
    (fun s=>Real.rpow_pos_of_pos (zero_lt_one.trans_le st.base_ge_one) _)]
  congr 2
  congr 1
  apply Finset.prod_congr rfl
  intro s hs
  exact naturalSlot_of_row st.character (χ u) st.mask 1 u (hrow u hu) _ _ _

/-- Injective finite row parametrizations, including the sixth-power-free row type,
preserve the literal finite marked plain moment. -/
theorem actual_finite_marked_polynomials_of_injective {Row : Type*}
    (W : ℝ→ℂ) (bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ U : ℝ)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ) (seminorms : Finset (ℕ×ℕ)) (C : ℝ)
    (hinput : PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
      Mcap ε κ U η₀ Q degree seminorms C)
    (slots : Finset α) (θ : slots→RayQuotient.Characters M H)
    (w σ v : slots→ℝ) (height : ℝ)
    (hw : ∀s,0≤w s) (hwm : ∀s,w s≤Lslot)
    (hσlo : ∀s,lo≤σ s) (hσhi : ∀s,σ s≤hi)
    (hheight : 0≤height) (hv : ∀s,|v s|≤height)
    (st : NaturalState U Bmask bΦ) (hQ : st.fixedModulus=internalQ Q η₀)
    (hst : st.width≤Mcap) (p : Profiles a b) (X₁ X₂ σd td : ℝ)
    (V₁ V₂ : ℝ→ℂ) (hp₁ : (p.profile 0 : ℝ→ℂ)=twistProfile V₁ σd td)
    (hp₂ : (p.profile 1 : ℝ→ℂ)=twistProfile V₂ σd td)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hXL₁ : X₁≤U^L) (hXL₂ : X₂≤U^L)
    (hcap : length U X₁+length U X₂+6*κ*(∑s,w s)≤st.width)
    (rows : Finset Row) (row : Row→O) (hinj : Function.Injective row) (χ : Row→Character)
    (hrow : ∀u∈rows,∀n,elementCoeff (χ u) n=
      CanonicalRowCompletion.rowTwist (elementHom st.character) st.mask 1 (1*row u) n)
    (hkeep : ∀u∈rows,st.radial.keep (row u)) (hΦ : ∀x,0≤(st.radial.profile x).re)
    (hone : ∀u∈rows,st.radial.profile (‖eisEmbedding (row u)‖^2/st.radial.scale)=1) :
    (∑u∈rows,‖polynomial (χ u) false V₁ X₁ σd td*
      polynomial (χ u) false V₂ X₂ σd td*
      ∏s,naturalSlot (χ u) (primePool M H bslot (U^(w s)))
        (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
          HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (v s) I)
        (U^(w s))‖^2)≤
      C*diagonalControl st.radial.profile*(p.control seminorms)^2*
        (1+height)^degree*U^(st.width+ε) := by
  have he := actual_finite_marked_plain M H hH W bslot a b bΦ Bmask L Lslot lo hi
    Mcap ε κ U η₀ Q degree seminorms C hinput slots θ w σ v 0 height
    hw hwm hσlo hσhi hheight hv st hQ hst p X₁ X₂ hX₁ hX₂ hXL₁ hXL₂ hcap
    (rows.image row)
    (fun u hu=>by obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu; exact hkeep v hv) hΦ
    (fun u hu=>by obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu; exact hone v hv)
  simp only [abs_zero,add_zero] at he
  rw [Finset.sum_image (fun x _ y _ h=>hinj h)] at he
  apply le_trans _ he
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro u hu
  rw [hp₁,hp₂,positiveSlotRow_eq_product st.character (χ u) st.mask 1 (row u)
    (hrow u hu) V₁ V₂ _ _ _ X₁ X₂ σd td hX₁ hX₂
    (fun s=>Real.rpow_pos_of_pos (zero_lt_one.trans_le st.base_ge_one) _)]
  congr 2
  congr 1
  apply Finset.prod_congr rfl
  intro s hs
  exact naturalSlot_of_row st.character (χ u) st.mask 1 (row u) (hrow u hu) _ _ _

end
end OAI.SevenEighths.Cycle61MarkedPlain
#print axioms OAI.SevenEighths.Cycle61MarkedPlain.actual_finite_marked_plain

#print axioms OAI.SevenEighths.Cycle61MarkedPlain.actual_finite_marked_polynomials

#print axioms OAI.SevenEighths.Cycle61MarkedPlain.actual_finite_marked_polynomials_of_injective
