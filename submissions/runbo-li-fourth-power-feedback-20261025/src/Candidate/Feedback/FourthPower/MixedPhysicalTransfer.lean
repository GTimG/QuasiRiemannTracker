/- Copyright (c) 2026 Sil. Apache-2.0.
The fourth-power transfer on the actual first-Poisson residual columns.
The complete centered coefficient, artificial divisor and fixed phases are
retained. Fifth-freeness is required only where the coefficient is nonzero.
-/
import Candidate.Feedback.FourthPower.MixedCenteredZero
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSource

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.MixedPhysicalTransfer
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CanonicalRowCompletion CompletedGauss CenteredMomentGaussEnergy
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open SexticSieve ReferenceConvolution
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem grouped_support {ι : Type*} [Fintype ι]
    (S : Finset (ι→Id)) (β : (ι→Id)→ℂ) (I : Id)
    (h : ReferenceConvolution.coefficient S β I≠0) :
    ∃v∈S,product v=I ∧ β v≠0 := by
  obtain ⟨v,hv,hβ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨v,(Finset.mem_filter.mp hv).1,(Finset.mem_filter.mp hv).2,hβ⟩

theorem centered_coefficient_fifth_free {ι : Type*} [Fintype ι]
    (S T : Finset (ι→Id)) (β γ : (ι→Id)→ℂ)
    (hf : ∀v∈S∪T,PowerFree 5 (product v)) (I : Id)
    (h : ReferenceConvolution.coefficient (S∪T) (MixedCenteredZero.difference S T β γ) I≠0) :
    PowerFree 5 I := by
  obtain ⟨v,hv,he,_⟩ := grouped_support (S∪T) _ I h
  exact he ▸ hf v hv

/-- The same residual coefficient used in the first physical Gauss side,
with its artificial divisibility mask and any fixed column phase. -/
def physicalCoefficient (η : Character) (m A : O) (t : ℝ) (c : Id→ℂ)
    (D seed : Id) (μ : Id→ℂ) (I : Id) : ℂ :=
  (if seed∣I then CenteredMomentFirstPhysicalSource.coefficient η m A t c D I else 0)*μ I

theorem physical_coefficient_fifth_free (η : Character) (m A : O) (t : ℝ) (c : Id→ℂ)
    (D seed : Id) (μ : Id→ℂ) (hf : ∀I,c I≠0→PowerFree 5 I) (I : Id)
    (h : physicalCoefficient η m A t c D seed μ I≠0) : PowerFree 5 I := by
  have hc : c (D*I)≠0 := by
    intro hz
    exact h (by simp [physicalCoefficient,CenteredMomentFirstPhysicalSource.coefficient,hz])
  intro P hp hd
  exact hf (D*I) hc P hp (hd.trans (dvd_mul_left I D))

theorem sparse_fourth_power {ι : Type*} (S : Finset ι) (a : ι→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (b : ι→ℂ)
    (hf : ∀i∈S,b i≠0→GaussTransfer.FifthFree (a i)) (D k : O) :
    gaussPolynomial S a ha b (D^4*k)=
      ∑i∈S,b i*(idealRowHom D (Ideal.span {a i}))^2*gaussRow (a i) (ha i) k := by
  unfold gaussPolynomial
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hb : b i=0
  · simp [hb]
  · rw [GaussTransfer.normalized_fourth_power (a i) (ha i) (hf i hi hb)]
    ring

/-- Nonnegative row weights may depend jointly on D and k. They are removed
only after the whole polynomial has been squared; its coefficients are common.
The output has the actual fourth-power radius and the original 1/W average. -/
theorem sparse_weighted_average (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(Ds : Finset Id)(Ks : Finset O),
    (∀D∈Ds,Supported D) → (∀k∈Ks,k≠0) →
    ∀(w : Id→ℝ)(ρ : Id→O→ℝ)(W K L : ℝ),0<W → 0≤L →
    (∀D∈Ds,0≤w D ∧ w D≤L) → (∀D∈Ds,∀k∈Ks,0≤ρ D k ∧ ρ D k≤1) →
    (∀D∈Ds,(Ideal.absNorm D:ℝ)≤2*W) →
    (∀k∈Ks,(Ideal.absNorm (Ideal.span {k}):ℝ)≤K) →
    ∀{ι : Type*}(S : Finset ι)(a : ι→O)(ha : ∀i,Supported (Ideal.span {a i}))(b : ι→ℂ),
    (∀i∈S,b i≠0→GaussTransfer.FifthFree (a i)) →
    (∑D∈Ds,w D*∑k∈Ks,ρ D k*
      ‖∑i∈S,b i*(idealRowHom (primaryGenerator D) (Ideal.span {a i}))^2*gaussRow (a i) (ha i) k‖^2)/W ≤
      (L*C*(16*K*W^4)^ε/W)*∑r∈(Ds×ˢKs).image PositiveFamily.frequency,
        ‖gaussPolynomial S a ha b r‖^2 := by
  obtain ⟨C,hC,hbound⟩ := PositiveFamily.weighted_pushforward ε hε
  refine ⟨C,hC,?_⟩
  intro Ds Ks hDs hk w ρ W K L hW hL hw hρ hDN hkN ι S a ha b hf
  have hR : ∀r∈(Ds×ˢKs).image PositiveFamily.frequency,
      r≠0 ∧ (Ideal.absNorm (Ideal.span {r}):ℝ)≤16*K*W^4 := by
    intro r hr
    obtain ⟨⟨D,k⟩,hz,rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hD,hk'⟩ := Finset.mem_product.mp hz
    exact ⟨PositiveFamily.frequency_ne_zero D (hDs D hD) k (hk k hk'),
      PositiveFamily.frequency_norm_bound D (hDs D hD) k W K hW.le (hDN D hD) (hkN k hk')⟩
  have hb := hbound Ds Ks ((Ds×ˢKs).image PositiveFamily.frequency) hDs hk w
    (gaussPolynomial S a ha b) L (16*K*W^4) hL hw
    (fun z hz=>Finset.mem_image.mpr ⟨z,hz,rfl⟩) hR
  have hm : (∑D∈Ds,w D*∑k∈Ks,ρ D k*
      ‖gaussPolynomial S a ha b (PositiveFamily.frequency (D,k))‖^2) ≤
      L*C*(16*K*W^4)^ε*∑r∈(Ds×ˢKs).image PositiveFamily.frequency,
        ‖gaussPolynomial S a ha b r‖^2 := by
    apply le_trans _ hb
    apply Finset.sum_le_sum
    intro D hD
    apply mul_le_mul_of_nonneg_left _ (hw D hD).1
    apply Finset.sum_le_sum
    intro k hk'
    exact mul_le_of_le_one_left (sq_nonneg _) (hρ D hD k hk').2
  have he (D : Id) (k : O) :
      gaussPolynomial S a ha b (PositiveFamily.frequency (D,k))=
        ∑i∈S,b i*(idealRowHom (primaryGenerator D) (Ideal.span {a i}))^2*gaussRow (a i) (ha i) k :=
    sparse_fourth_power S a ha b hf (primaryGenerator D) k
  simp_rw [he] at hm
  exact (div_le_div_of_nonneg_right hm hW.le).trans_eq (by ring)

/-- Direct application to the literal first physical column pool and its
original coefficient. There is no fifth-free hypothesis on zero columns. -/
theorem actual_first_physical_average (ε : ℝ) (hε : 0<ε) :
    ∃C0 : ℝ,0<C0 ∧ ∀(Ds : Finset Id)(Ks : Finset O),
    (∀D∈Ds,Supported D) → (∀k∈Ks,k≠0) →
    ∀(w : Id→ℝ)(ρ : Id→O→ℝ)(W K L : ℝ),0<W → 0≤L →
    (∀D∈Ds,0≤w D ∧ w D≤L) → (∀D∈Ds,∀k∈Ks,0≤ρ D k ∧ ρ D k≤1) →
    (∀D∈Ds,(Ideal.absNorm D:ℝ)≤2*W) →
    (∀k∈Ks,(Ideal.absNorm (Ideal.span {k}):ℝ)≤K) →
    ∀(C D : Id)(hD : Supported D)(S : Finset Id)(η : Character)(m A : O)(t : ℝ)
      (c : Id→ℂ)(seed : Id)(μ : Id→ℂ),
    (∀I,c I≠0→PowerFree 5 I) →
    let a := CenteredMomentFirstPhysicalSource.element C D hD.1 S
    let ha := CenteredMomentFirstPhysicalSource.element_supported C D hD.1 S
    let b := fun i : CenteredMomentFirstPhysicalSource.columns C D hD.1 S=>
      physicalCoefficient η m A t c D seed μ i
    (∑F∈Ds,w F*∑k∈Ks,ρ F k*
      ‖∑i,b i*(idealRowHom (primaryGenerator F) (Ideal.span {a i}))^2*gaussRow (a i) (ha i) k‖^2)/W ≤
      (L*C0*(16*K*W^4)^ε/W)*∑r∈(Ds×ˢKs).image PositiveFamily.frequency,
        ‖gaussPolynomial Finset.univ a ha b r‖^2 := by
  obtain ⟨C0,hC0,hbound⟩ := sparse_weighted_average ε hε
  refine ⟨C0,hC0,?_⟩
  intro Ds Ks hDs hk w ρ W K L hW hL hw hρ hDN hkN C D hD S η m A t c seed μ hf
  dsimp only
  apply hbound Ds Ks hDs hk w ρ W K L hW hL hw hρ hDN hkN
  intro i _ hi
  apply KernelWholeColumns.element_fifth_free
  rw [CenteredMomentFirstPhysicalSource.element_span]
  exact physical_coefficient_fifth_free η m A t c D seed μ hf i hi

end
end Candidate.Feedback.FourthPower.MixedPhysicalTransfer
