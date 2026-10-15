/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCountParameters
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentMono
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrimeConstants
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ChildState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.PaidBands
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorCountFromMoments
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorRowCountEndpoint
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorZeros
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.FiniteDeletion
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationShortening
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstColumns
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceNaturalPrime
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondCanonicalNonunit
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondSourceMask
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.WholeSlotDeletion
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorSourceCount

/- BEGIN ORIGINAL MODULE LocalMoment.LowSourceAdapters ; sha256 fb32a39b12b378805effde9c72d3d9a4db84ded2c71259da8bf2cf99f0c6ee53 -/
section






namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.LocalMomentSourceAudit
open HeckeFamily CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondNonexceptionalChosenBlock HeckePrimeRay HeckeDetectorZeros
open HeckeFiniteDeletion CenteredMomentWholeSlotDeletion
local notation "O" => HeckeFamily.O

/-- The moving child character is τ.  The relative-slot base η₀ and the
fixed exclusion ideal internalQ Q η₀ remain independent of τ. -/
theorem canonical_all_twists
    (M : Ideal O) [NeZero M]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (τ η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M)
    (n : Fin 4 → ℤ) (z : O)
    (hz : (canonicalRadial τ (internalQ Q η₀) n).keep z)
    (F : NaturalRow τ z) :
    ∀ θ : RayQuotient.Characters M H,
      (twistedFamily M H hH (F.character.product η₀.inverse) θ).residue ≠ 1 := by
  exact natural_relative_twists M H hH F hz.1 η₀ Q hQM hz.2

/-- Removing Euler factors does not change any buffered maximum; this includes
height T and the sentinel 51/100, rather than only individual positive zeros. -/
theorem zeroMaximum_eq_of_mask {ι : Type*} [Fintype ι]
    (χ ψ : ι → Character)
    (hχ : ∀ i, (χ i).residue ≠ 1) (hψ : ∀ i, (ψ i).residue ≠ 1)
    (hm : ∀ i I, idealCoeff (χ i) I =
      if IsCoprime I (χ i).modulus then idealCoeff (ψ i) I else 0)
    (T : ℝ) : zeroMaximum χ hχ T = zeroMaximum ψ hψ T := by
  have he (i : ι) (s : ℂ) (hs : (51/100 : ℝ) ≤ s.re) :
      LFunction (χ i) s = 0 ↔ LFunction (ψ i) s = 0 := by
    have hs0 : 0 < s.re := by linarith
    rw [LFunction_eq_of_mask_nonprincipal (χ i) (ψ i) (hm i) (hχ i) hs0,
      mul_eq_zero]
    exact or_iff_left (factors_ne_zero (χ i).modulus (ψ i) hs0)
  apply le_antisymm
  · rcases lt_or_ge (51/100 : ℝ) (zeroMaximum χ hχ T) with h | h
    · obtain ⟨i,s,hz,ht,hs⟩ := maximum_attained χ hχ T h
      have hr : (51/100 : ℝ) ≤ s.re := by rw [hs]; exact h.le
      have hh := zero_re_le_maximum ψ hψ T i hr ht ((he i s hr).mp hz)
      simpa only [hs] using hh
    · exact h.trans (zeroMaximum_bounds ψ hψ T).1
  · rcases lt_or_ge (51/100 : ℝ) (zeroMaximum ψ hψ T) with h | h
    · obtain ⟨i,s,hz,ht,hs⟩ := maximum_attained ψ hψ T h
      have hr : (51/100 : ℝ) ≤ s.re := by rw [hs]; exact h.le
      have hh := zero_re_le_maximum χ hχ T i hr ht ((he i s hr).mpr hz)
      simpa only [hs] using hh
    · exact h.trans (zeroMaximum_bounds χ hχ T).1

/-- Greedy removal uses the incumbent capacity, while its payment uses the low
bin rate.  Exhaustion is a valid alternative and needs no extra residual cost. -/
theorem greedy_low_selection {α : Type*}
    (J : Finset α) (w : α → ℝ) (l₁ l₂ width κbase κlow mesh : ℝ)
    (hb : 0 < κbase) (hl : 0 ≤ κlow) (hm : 0 ≤ mesh)
    (hw : ∀ i ∈ J, 0 ≤ w i) (hwm : ∀ i ∈ J, w i ≤ mesh) :
    let F := max (l₁+l₂+6*κbase*(∑ i ∈ J, w i)-width) 0
    ∃ R : Finset α, R ⊆ J ∧
      (R = J ∨ l₁+l₂+6*κbase*(∑ i ∈ J \ R, w i) ≤ width) ∧
      κlow*(∑ i ∈ R, w i) ≤ κlow/(6*κbase)*F+κlow*mesh := by
  classical
  dsimp only
  let F := max (l₁+l₂+6*κbase*(∑ i ∈ J, w i)-width) 0
  obtain ⟨R,hR,hbound,hpay,_⟩ := whole_removal J w F κbase mesh
    (le_max_right _ _) hb hm hw hwm
  refine ⟨R,hR,?_,?_⟩
  · rcases hpay with he | hp
    · exact Or.inl he
    · right
      have hsum := Finset.sum_sdiff hR (f := w)
      have hF : l₁+l₂+6*κbase*(∑ i ∈ J, w i)-width ≤ F := le_max_left _ _
      nlinarith
  · have hp := mul_le_mul_of_nonneg_left (hbound.trans (min_le_right _ _)) hl
    convert hp using 1 <;> dsimp only [F] <;> ring

/-- Canonical children have an exact width, possibly smaller than the nominal
ledger width.  Pay width and defect together instead of dropping that deficit. -/
theorem width_plus_low_defect (d F pad rate : ℝ)
    (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) (hpad : 0 ≤ pad) (hd : d ≤ pad) :
    d + rate*max (F-d) 0 ≤ pad + rate*max F 0 := by
  by_cases h : 0 ≤ F-d
  · rw [max_eq_left h]
    by_cases hf : 0 ≤ F
    · rw [max_eq_left hf]
      nlinarith
    · rw [max_eq_right (le_of_not_ge hf)]
      nlinarith
  · rw [max_eq_right (le_of_not_ge h)]
    have hnn : 0 ≤ rate*max F 0 := mul_nonneg hrate0 (le_max_right _ _)
    linarith

#print axioms canonical_all_twists
#print axioms zeroMaximum_eq_of_mask
#print axioms greedy_low_selection
#print axioms width_plus_low_defect
end SevenEighths.LocalMomentSourceAudit
end
end OAI
end
/- END ORIGINAL MODULE LocalMoment.LowSourceAdapters -/

/- BEGIN ORIGINAL MODULE LocalMoment.RestrictedIncumbent ; sha256 188b456c8477ae12cf7ae466be7687fd0c6e32c9dd8a00e95ade2227c3e33ff2 -/
section


/-! Low-bin source payment: remove slots only on the restricted rows,
then apply the incumbent moment to the remaining exact natural state. -/

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.LocalMoment
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyPaidBands CenteredMomentEnergyCapacityRemoval
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot CenteredMomentHeckeSlots
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource QuadraticInitialBound
open CenteredMomentRetainedEnergy
local notation "O" => HeckeFamily.O

variable {α : Type*}

/-- Post-transform row restriction is kept while paying removed slots.
The remaining nonnegative norm is enlarged only after this payment. -/
theorem restricted_energy_remove {Z Bmask bΦ : ℝ}
    (s : NaturalState Z Bmask bΦ) (low : O → Prop)
    (J R : Finset α) (hR : R ⊆ J)
    (W₁ W₂ : ℝ → ℂ) (slots : α → Finset (Ideal O))
    (coeff : α → Ideal O → ℂ) (P : α → ℝ)
    (t X₁ X₂ κlow : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hP : ∀ i, 0 ≤ P i) (w B : α → ℝ) (hB : ∀ i ∈ R, 0 ≤ B i)
    (hslot : ∀ z, s.radial.keep z → low z → ∀ i ∈ R,
      ‖normalizedSlot s.character s.mask 1 z (slots i) (coeff i) t (P i)‖ ^ 2 ≤
        B i * Z ^ (κlow * w i)) :
    energy s.character s.mask 1 t W₁ W₂ (fun i : J => slots i)
      (fun i : J => coeff i) (fun i : J => P i) X₁ X₂
      (fun z => s.radial.keep z ∧ low z) s.radial.profile s.radial.scale ≤
      ((∏ i ∈ R, B i) * Z ^ (κlow * ∑ i ∈ R, w i)) *
        energy s.character s.mask 1 t W₁ W₂ (fun i : ↥(J \ R) => slots i)
          (fun i : ↥(J \ R) => coeff i) (fun i : ↥(J \ R) => P i) X₁ X₂
          s.radial.keep s.radial.profile s.radial.scale := by
  classical
  have hZ : 0 < Z := zero_lt_one.trans_le s.base_ge_one
  let cost := (∏ i ∈ R, B i) * Z ^ (κlow * ∑ i ∈ R, w i)
  have hcost : 0 ≤ cost := mul_nonneg (Finset.prod_nonneg hB) (Real.rpow_nonneg hZ.le _)
  have hsum (T : Finset α) (keep : O → Prop) := compact_radial_summable
    (fun z => positiveSlotRow s.character s.mask 1 z W₁ W₂
      (fun i : T => slots i) (fun i : T => coeff i) (fun i : T => P i) t X₁ X₂)
    keep s.radial.profile s.radial.scale bΦ s.radial.scale_pos s.radial_support
  unfold energy
  rw [← tsum_mul_left]
  apply (hsum J (fun z => s.radial.keep z ∧ low z)).tsum_le_tsum _
    ((hsum (J \ R) s.radial.keep).mul_left cost)
  intro z
  by_cases hk : s.radial.keep z
  · by_cases hl : low z
    · simp only [hk, hl, and_self, ite_true]
      have hh := selectedProduct_energy_remove J R hR s.character s.mask 1 z W₁ W₂
        slots coeff P t X₁ X₂ Z κlow hZ w B hB (hslot z hk hl)
      rw [selected_eq_positive J s.character s.mask 1 z W₁ W₂ slots coeff P t X₁ X₂
        (mul_pos hX₁ hX₂).le hP,
        selected_eq_positive (J \ R) s.character s.mask 1 z W₁ W₂ slots coeff P
          t X₁ X₂ (mul_pos hX₁ hX₂).le hP] at hh
      exact (mul_le_mul_of_nonneg_right hh (s.radial.nonneg z)).trans_eq (by ring)
    · simp only [hk, hl, and_false, ite_false, ite_true]
      exact mul_nonneg hcost (mul_nonneg (sq_nonneg _) (s.radial.nonneg z))
  · simp only [hk, false_and, ite_false, mul_zero, le_refl]

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The low-bin removal rate and the incumbent capacity rate are separate.
This theorem calls only the incumbent positive or zero-slot moment on the
remaining state, including every original mask and eligibility predicate. -/
theorem restricted_paid_incumbent
    (W : ℝ → ℂ) (bslot a b bΦ Bmask L Lslot lo hi Mcap ε κbase Z : ℝ)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ × ℕ)) (C₀ C₁ : ℝ)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hzero : ZeroAt (internalQ Q η₀) a b bΦ Bmask L Mcap ε Z degree S C₀)
    (hpositive : PositiveAt (α := α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
      Mcap ε κbase Z η₀ Q degree S C₁)
    (J R : Finset α) (hR : R ⊆ J) (θ : α → RayQuotient.Characters M H)
    (w σ v : α → ℝ) (t height κlow : ℝ) (B : α → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwL : ∀ i, w i ≤ Lslot)
    (hσlo : ∀ i, lo ≤ σ i) (hσhi : ∀ i, σ i ≤ hi)
    (hheight : 0 ≤ height) (hv : ∀ i, |v i| ≤ height) (hB : ∀ i ∈ R, 0 ≤ B i)
    (s : NaturalState Z Bmask bΦ) (hQ : s.fixedModulus = internalQ Q η₀)
    (hs : s.width ≤ Mcap) (low : O → Prop) (p : Profiles a b) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hc₁ : X₁ ≤ Z ^ L) (hc₂ : X₂ ≤ Z ^ L)
    (hcapacity : R = J ∨
      length Z X₁ + length Z X₂ + 6 * κbase * (∑ i ∈ J \ R, w i) ≤ s.width)
    (hslot : ∀ z, s.radial.keep z → low z → ∀ i ∈ R,
      ‖normalizedSlot s.character s.mask 1 z (primePool M H bslot (Z ^ (w i)))
        (fun I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight W (Z ^ (w i)) (σ i) (v i) I)
        t (Z ^ (w i))‖ ^ 2 ≤ B i * Z ^ (κlow * w i)) :
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i : J => primePool M H bslot (Z ^ (w i)))
      (fun (i : J) I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight W (Z ^ (w i)) (σ i) (v i) I)
      (fun i : J => Z ^ (w i)) X₁ X₂ (fun z => s.radial.keep z ∧ low z)
      s.radial.profile s.radial.scale ≤
      (∏ i ∈ R, B i) * ((C₀ + C₁) * diagonalControl s.radial.profile *
        (p.control S) ^ 2 * (1 + |t| + height) ^ degree) *
        Z ^ (s.width + ε + κlow * ∑ i ∈ R, w i) := by
  classical
  have hZ : 0 < Z := zero_lt_one.trans_le s.base_ge_one
  have he := restricted_energy_remove s low J R hR (p.profile 0) (p.profile 1)
    (fun i => primePool M H bslot (Z ^ (w i)))
    (fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
      HeckePrimeAnnular.annularWeight W (Z ^ (w i)) (σ i) (v i) I)
    (fun i => Z ^ (w i)) t X₁ X₂ κlow hX₁ hX₂
    (fun i => Real.rpow_nonneg hZ.le _) w B hB hslot
  have hb := remaining_energy_bound M H hH W bslot a b bΦ Bmask L Lslot lo hi
    Mcap ε κbase Z η₀ Q degree S C₀ C₁ hC₀ hC₁ hzero hpositive
    J R θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂
    hX₁ hX₂ hc₁ hc₂ hcapacity
  apply he.trans ((mul_le_mul_of_nonneg_left hb
    (mul_nonneg (Finset.prod_nonneg hB) (Real.rpow_nonneg hZ.le _))).trans_eq ?_)
  simp only [Real.rpow_add hZ]
  ring

end SevenEighths.LocalMoment
end
end OAI
end
/- END ORIGINAL MODULE LocalMoment.RestrictedIncumbent -/

/- BEGIN ORIGINAL MODULE LocalMoment.SignedRows ; sha256 0c71c83f4ca774cdfe48684ef74d38c03674c003b8e935f5d8cf1c1e9aaf64ba -/
section






namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.LocalMomentSignedRows
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentSupportedCorrelation CenteredMomentFirstColumns
open CenteredMomentAmplificationShortening
local notation "O" => ActualEisensteinCubic.O
set_option autoImplicit false

/-- Reciprocity fixes the sign: the left coefficient uses exponent 1+t. -/
theorem left_local (p n : O) (t : ℕ)
    (hp : Supported (Ideal.span {p})) (hn : Supported (Ideal.span {n}))
    (hpp : goodLambda^2 ∣ p-1) (hnp : goodLambda^2 ∣ n-1) :
    idealRowHom p (Ideal.span {n}) * idealRowHom n (Ideal.span {p})^t =
      sexticReciprocityPhase p n^t * idealRowHom (p^(1+t)) (Ideal.span {n}) := by
  rw [idealRowHom_primary_reciprocity p n hpp hnp hp hn, mul_pow,
      idealRowHom_argument_pow p (1+t) _ hn, pow_add, pow_one]
  ring

/-- A sixth power retains its original puncture, including on nonunits. -/
theorem left_canceled (p n : O)
    (hp : Supported (Ideal.span {p})) (hn : Supported (Ideal.span {n}))
    (hpp : goodLambda^2 ∣ p-1) (hnp : goodLambda^2 ∣ n-1) :
    idealRowHom p (Ideal.span {n}) * idealRowHom n (Ideal.span {p})^5 =
      sexticReciprocityPhase p n^5 *
        (if IsCoprime n p then (1:ℂ) else 0) := by
  rw [left_local p n 5 hp hn hpp hnp]
  norm_num only
  rw [idealRowHom_sixth_mask _ _ hn, Ideal.isCoprime_span_singleton_iff]

/-- Conjugation reverses the first active exponent. The raw representative
7-t is positive, so the nonunit zero is never replaced by 0^0. -/
theorem right_local (p n : O) [(Ideal.span {p}).IsMaximal] (t : ℕ)
    (ht : 0< t) (ht6 : t<6)
    (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hp : Supported (Ideal.span {p})) (hn : Supported (Ideal.span {n}))
    (hpp : goodLambda^2 ∣ p-1) (hnp : goodLambda^2 ∣ n-1) :
    idealRowHom p (Ideal.span {n}) * star (idealRowHom n (Ideal.span {p})^t) =
      sexticReciprocityPhase p n^(6-t) * idealRowHom (p^(7-t)) (Ideal.span {n}) := by
  let χ := ActualEisensteinCubic.canonicalSextic (Ideal.span {p}) hg
  have hinv : (χ^t)⁻¹=χ^(6-t) := by
    apply inv_eq_of_mul_eq_one_right
    rw [←pow_add,Nat.add_sub_of_le ht6.le]
    exact ProbePrimePower.actualSextic_six _ hg hc
  have hs : star (idealRowHom n (Ideal.span {p})^t) =
      idealRowHom n (Ideal.span {p})^(6-t) := by
    rw [idealRowHom_prime n _ hg]
    change star (χ (Ideal.Quotient.mk _ n)^t)=χ (Ideal.Quotient.mk _ n)^(6-t)
    rw [←MulChar.pow_apply' χ (by omega : t≠0),MulChar.star_apply',hinv,
      MulChar.pow_apply' χ (by omega : 6-t≠0)]
  rw [hs,left_local p n (6-t) hp hn hpp hnp]
  rw [show 1+(6-t)=7-t by omega]

/-- At t=1 the right coefficient is exactly a puncture, not one. -/
theorem right_canceled (p n : O) [(Ideal.span {p}).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hp : Supported (Ideal.span {p})) (hn : Supported (Ideal.span {n}))
    (hpp : goodLambda^2 ∣ p-1) (hnp : goodLambda^2 ∣ n-1) :
    idealRowHom p (Ideal.span {n}) * star (idealRowHom n (Ideal.span {p})) =
      sexticReciprocityPhase p n^5 *
        (if IsCoprime n p then (1:ℂ) else 0) := by
  have h := right_local p n 1 (by decide) (by decide) hg hc hp hn hpp hnp
  norm_num only [pow_one] at h
  rw [h,idealRowHom_sixth_mask _ _ hn,Ideal.isCoprime_span_singleton_iff]

/-- Multiplying all already retained row numerators is literal, before
reducing any sixth powers and before taking absolute values. -/
theorem effective_row (e F G V h : O) (I : Ideal O) :
    idealRowHom (e*F) I * idealRowHom ((G*V)*h) I =
      idealRowHom ((e*F)*(G*V)*h) I := by
  simp only [idealRowHom_argument_mul]
  ring

#print axioms left_local
#print axioms left_canceled
#print axioms right_local
#print axioms right_canceled
#print axioms effective_row
end SevenEighths.LocalMomentSignedRows
end
end OAI
end
/- END ORIGINAL MODULE LocalMoment.SignedRows -/

/- BEGIN ORIGINAL MODULE LocalMoment.UnmarkedDensity ; sha256 de4fff9416258deadcc0c6cd023ecd5fb8dd1c90f698c587aa2899201258098d -/
section



/-! The unmarked zero-density source interface used by the proposed local
physical moment.  These lemmas use only the existing unmarked plain and
inverse moments.  They do not assert the local physical moment. -/

namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set Filter

namespace SevenEighths.LocalMoment
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open HeckeDetectorCoefficientTransfer HeckeDetectorDyadicProfiles
open HeckeDetectorRawFiber HeckeDetectorBranchBudget HeckeDetectorRowCount
open HeckeDetectorInverseFiberCount
open HeckeDetectorRowwisePolynomial

def unmarkedDensity (δ : ℝ) : ℝ := 1 - 10 * δ / (3 * (5 - 2 * δ))

def unmarkedCutoff (δ : ℝ) : ℝ := Endpoint.balancedCutoff δ (1 / 2)

theorem unmarkedDensity_ge_two_sevenths {δ : ℝ} (hδ : δ ≤ 3 / 4) :
    2 / 7 ≤ unmarkedDensity δ := by
  have hden : 0 < 3 * (5 - 2 * δ) := by linarith
  have hquot : 10 * δ / (3 * (5 - 2 * δ)) ≤ 5 / 7 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  unfold unmarkedDensity
  linarith

theorem unmarkedDensity_gt_one_sixth {δ : ℝ} (hδ : δ ≤ 3 / 4) :
    1 / 6 < unmarkedDensity δ := by
  linarith [unmarkedDensity_ge_two_sevenths hδ]

theorem unmarkedCutoff_eq {δ : ℝ} (hδ : δ ≤ 5 / 6) :
    unmarkedCutoff δ = 5 / (5 - 2 * δ) := by
  have hden : 5 - 2 * δ ≠ 0 := by linarith
  have hden' : (5 : ℝ) - δ * 2 ≠ 0 := by linarith
  have hD : Endpoint.balanceDenominator δ (1 / 2) = (5 - 2 * δ) / 2 := by
    unfold Endpoint.balanceDenominator Endpoint.denominator Endpoint.primeWeight
    ring
  unfold unmarkedCutoff Endpoint.balancedCutoff
  rw [hD, show 2 * ((5 - 2 * δ) / 2) = 5 - 2 * δ by ring]
  norm_num [Endpoint.primeWeight]
  field_simp [hden, hden']
  ring

theorem unmarkedDensity_eq_balanced {δ : ℝ} (hδ : δ ≤ 5 / 6) :
    unmarkedDensity δ = Endpoint.balancedRowCount δ (1 / 2) := by
  have hden : 5 - 2 * δ ≠ 0 := by linarith
  have hden' : (5 : ℝ) - δ * 2 ≠ 0 := by linarith
  unfold Endpoint.balancedRowCount
  change unmarkedDensity δ = 1 - 5 / 6 + (5 / 6 - δ) * unmarkedCutoff δ
  rw [unmarkedCutoff_eq hδ]
  unfold unmarkedDensity
  field_simp [hden, hden']
  ring

theorem unmarkedCutoff_bounds {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 5 / 6) :
    1 ≤ unmarkedCutoff δ ∧ unmarkedCutoff δ ≤ 3 / 2 := by
  simpa only [unmarkedCutoff, sub_zero] using
    balanced_cutoff_bounds hδ hδ' (show (0 : ℝ) ≤ 0 by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)

/-- Two existing unmarked source bounds suffice for the density exponent.
The support tolerance is kept explicitly; no prime amplitude or marked
moment is used in this interpolation. -/
theorem unmarked_count_bound (B C U δ r m ε γ : ℝ)
    (hC : 0 ≤ C) (hU : 1 ≤ U) (hδ : 0 ≤ δ) (hδ' : δ ≤ 5 / 6)
    (hγ : 0 ≤ γ)
    (hleft : unmarkedCutoff δ - r - γ ≤ m)
    (hright : r ≤ unmarkedCutoff δ + γ)
    (hI : B ≤ C * U ^ (max 1 ((1 + 5 * r) / 6) - δ * r + ε))
    (hP : B ≤ C * U ^ (1 - 2 * δ * m + ε)) :
    B ≤ C * U ^ (unmarkedDensity δ + ε + 2 * γ) := by
  have hbounds := unmarkedCutoff_bounds hδ hδ'
  have hbal := balanced_count_identity hδ hδ'
    (show (0 : ℝ) ≤ 0 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have hbal' : max (shortExponent δ 0 (unmarkedCutoff δ))
      (longExponent δ (unmarkedCutoff δ)) = unmarkedDensity δ := by
    simpa only [unmarkedCutoff, sub_zero, ← unmarkedDensity_eq_balanced hδ'] using hbal
  have hs : shortExponent δ 0 (unmarkedCutoff δ) ≤ unmarkedDensity δ := by
    rw [← hbal']
    exact le_max_left _ _
  have hl : longExponent δ (unmarkedCutoff δ) ≤ unmarkedDensity δ := by
    rw [← hbal']
    exact le_max_right _ _
  have promote (p : ℝ) (hp : B ≤ C * U ^ p)
      (hpt : p ≤ unmarkedDensity δ + ε + 2 * γ) :
      B ≤ C * U ^ (unmarkedDensity δ + ε + 2 * γ) :=
    hp.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hU hpt) hC)
  by_cases hr1 : 1 ≤ r
  · rw [max_eq_right (show (1 : ℝ) ≤ (1 + 5 * r) / 6 by linarith)] at hI
    apply promote _ hI
    have hh := long_count_bound hδ' hγ hright
    have hg : (5 / 6 - δ) * γ ≤ 2 * γ := by nlinarith
    linarith
  · rw [max_eq_left (show (1 + 5 * r) / 6 ≤ (1 : ℝ) by linarith)] at hI
    have hchoose := selected_short_bound (δ := δ) (x := 0)
      (t := unmarkedCutoff δ) (r := r) hδ (by norm_num) (by norm_num)
    by_cases hrc : crossing 0 (unmarkedCutoff δ) ≤ r
    · apply promote _ hI
      have hh := hchoose.2 hrc
      unfold inverseExponent at hh
      nlinarith
    · apply promote _ hP
      have hh := hchoose.1 (le_of_not_ge hrc)
      have hm := mul_le_mul_of_nonneg_left hleft (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hδ)
      have hg : 2 * δ * γ ≤ 2 * γ := by nlinarith
      unfold plainExponent at hh
      nlinarith

/-- A detector fiber with no required prime-slot supply.  Unlike the existing
marked `HeckeDetectorRawFiber.Fiber`, it admits a truly unmarked source. -/
structure UnmarkedFiber (U a ε tstar T allowance : ℝ) (i : ℕ) (Label : Type*) where
  rows : Finset FreeRow
  nonempty : rows.Nonempty
  family : FreeRow → Label → Character
  witness : ∀ u, SupportedWitness (family u) U a ε tstar T allowance i
  label : Label
  left : Fin (dyadicLength U)
  right : Fin (dyadicLength U)
  fixed_label : ∀ u ∈ rows, (witness u).label = label
  fixed_left : ∀ u ∈ rows, (witness u).left = left
  fixed_right : ∀ u ∈ rows, (witness u).right = right
  row_norm : ∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ U
  rowData : RowData
  reverse : Bool
  row_coeff : ∀ u ∈ rows, ∀ J : Ideal O, idealCoeff (family u label) J =
    if reverse then starRingEnd ℂ (idealCoeff (rowData.character ⟨u.val, u.property.1⟩) J)
    else idealCoeff (rowData.character ⟨u.val, u.property.1⟩) J

def UnmarkedFiber.r {U a ε tstar T allowance : ℝ} {i : ℕ} {Label : Type*}
    (F : UnmarkedFiber U a ε tstar T allowance i Label) : ℝ :=
  Real.logb U ((2 : ℝ) ^ F.left.val)

def UnmarkedFiber.m {U a ε tstar T allowance : ℝ} {i : ℕ} {Label : Type*}
    (F : UnmarkedFiber U a ε tstar T allowance i Label) : ℝ :=
  Real.logb U ((2 : ℝ) ^ F.right.val)

structure UnmarkedMoments {U a ε tstar T allowance : ℝ} {i : ℕ} {Label : Type*}
    (F : UnmarkedFiber U a ε tstar T allowance i Label)
    (c κ C height εm : ℝ) : Prop where
  inverse_raw : ∀ n : ℕ, n ≤ 2 → ∀ s ∈ Icc (0 : ℝ) 1,
    ∀ t ∈ Icc (-height) height,
      let W := twistProfile (logTest
        (orientedProfile F.reverse (inverseTest U tstar F.r)) n) s t
      RawMoment F.rowData W c κ C ∧ RawMoment F.rowData (scaleProfile W) c κ C
  plain_unmarked : ∀ j k : ℕ, j + k ≤ 2 → ∀ s ∈ Icc (0 : ℝ) 1,
    ∀ t ∈ Icc (-height) height,
      ∑ u ∈ F.rows, ‖polynomial (F.family u F.label) false
        ((logProfile^[j]) positiveAnnular) (U^F.m) s t *
        polynomial (F.family u F.label) false
        ((logProfile^[k]) positiveAnnular) (U^F.m) s t‖^2 ≤
          C * U ^ (max 1 (2 * F.m) + εm)

/-- The actual unmarked detector density bound follows from the established
raw inverse moment and the established two-plain zero-slot moment.  The
statement retains coefficient orientation, all source profiles and frequencies,
and the full finite row set; its only loss is the displayed source padding. -/
theorem count_from_unmarked_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm : ℝ) (hεm : 0 < εm) :
    ∃ c κ K₀ : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < κ ∧ 0 ≤ K₀ ∧
      ∀ᶠ U : ℝ in atTop,
        ∀ (a ε T allowance C height : ℝ) (i : ℕ),
        1 < U → 1 / 2 ≤ a → 2 * a - 1 ≤ 5 / 6 → 0 ≤ ε → ε ≤ 1 / 1000 →
        0 ≤ C → 0 ≤ height → 2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height →
        ∀ {Label : Type*}
          (F : UnmarkedFiber U a ε (unmarkedCutoff (2 * a - 1)) T allowance i Label),
        UnmarkedMoments F c κ C height εm →
          (F.rows.card : ℝ) ≤ fiberConstant C height K₀ *
            U ^ (unmarkedDensity (2 * a - 1) + 156 * ε + εm) := by
  obtain ⟨c, κ, K₀, hc, hc1, hκ, hK, hamp⟩ :=
    HeckeDetectorNoSlotInverseCount.no_slot_inverse_count M H hH S φ hφ hφc hφp hφ0
      hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB 2 εm (by norm_num) hεm
  refine ⟨c, κ, K₀, hc, hc1, hκ, hK, ?_⟩
  filter_upwards [hamp] with U hamp
  intro a ε T allowance C height i hU ha hδcap hε hεsmall hC hh hf Label F moments
  let δ := 2 * a - 1
  have hδ : 0 ≤ δ := by dsimp [δ]; linarith
  have ht := unmarkedCutoff_bounds hδ hδcap
  have hgeom := fiber_lengths F.rows F.nonempty F.family U a ε (unmarkedCutoff δ)
    T allowance i hU F.witness F.left F.right F.fixed_left F.fixed_right
  change unmarkedCutoff δ - F.r - ε ≤ F.m ∧ F.r ≤ unmarkedCutoff δ + ε ∧
    F.m ≤ 1 / 2 + 75 * ε ∧ unmarkedCutoff δ - 1 / 2 - 76 * ε ≤ F.r ∧
    0 ≤ F.m at hgeom
  have hr0 : 0 ≤ F.r := by linarith [hgeom.2.2.2.1]
  have hr2 : F.r ≤ 2 := by linarith [hgeom.2.1]
  have hUp : 0 < U := zero_lt_one.trans hU
  obtain ⟨hconst, hconstP, hconstI, hconstI0⟩ :=
    fiberConstant_bounds C height K₀ hC hh hK
  have hi0 := hamp F.rows F.family a ε (unmarkedCutoff δ) T allowance i hU ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label
    F.fixed_left F.fixed_right hr0 hr2 F.rowData F.reverse C height hC hh hf
    F.row_norm F.row_coeff moments.inverse_raw
  have hp0 := HeckeDetectorNoSlotPlainCount.no_slot_plain_count F.rows F.family U a ε
    (unmarkedCutoff δ) T allowance i hU (by linarith)
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label
    F.fixed_left F.fixed_right εm C height hC hh hf moments.plain_unmarked
  have promote (C' p q : ℝ) (hC' : C' ≤ fiberConstant C height K₀)
      (hb : (F.rows.card : ℝ) ≤ C' * U ^ p) (hpq : p ≤ q) :
      (F.rows.card : ℝ) ≤ fiberConstant C height K₀ * U ^ q := by
    exact hb.trans ((mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg hUp.le _)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le hpq) hconst))
  have hI : (F.rows.card : ℝ) ≤ fiberConstant C height K₀ *
      U ^ (max 1 ((1 + 5 * F.r) / 6) - δ * F.r + (154 * ε + εm)) := by
    apply promote _ _ _ hconstI0 hi0
    change max 1 ((1 + 5 * F.r) / 6) - δ * F.r + 2 * ε + εm ≤
      max 1 ((1 + 5 * F.r) / 6) - δ * F.r + (154 * ε + εm)
    linarith
  have hP : (F.rows.card : ℝ) ≤ fiberConstant C height K₀ *
      U ^ (1 - 2 * δ * F.m + (154 * ε + εm)) := by
    apply promote _ _ _ hconstP hp0
    change max 1 (2 * F.m) - 2 * δ * F.m + 4 * ε + εm ≤
      1 - 2 * δ * F.m + (154 * ε + εm)
    have hm : max 1 (2 * F.m) ≤ 1 + 150 * ε := max_le (by linarith) (by linarith [hgeom.2.2.1])
    linarith
  have hbound := unmarked_count_bound (F.rows.card : ℝ) (fiberConstant C height K₀)
    U δ F.r F.m (154 * ε + εm) ε hconst hU.le hδ hδcap hε
    hgeom.1 hgeom.2.1 hI hP
  convert hbound using 1
  congr 2
  ring

end SevenEighths.LocalMoment
end
end OAI
end
/- END ORIGINAL MODULE LocalMoment.UnmarkedDensity -/

/- BEGIN ORIGINAL MODULE OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentInput ; sha256 74edb2e0b51c5913639bde386c51c45083817dabfd1e7fbf4afa46f693436ba7 -/
section



namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters
open HeckeInverseAmplification

def SourceMomentBound {Δ : ℝ} {D : HighData Δ} (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t) (η : Character)
    (Z τ C height : ℝ) : Prop :=
  ∀rows : Finset FreeRow,∀d a : ℝ, (1/200:ℝ)≤ d → d≤7/8 → 51/100< a → a≤1 →
    (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-D.t)) →
    ∀i : ℕ,∀z : ℂ,z.re=17/50 → |z.im|≤ height →
    SourceMomentsAt F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell (fun _ y=>(F.w y:ℂ))
      Z d a D.ε τ (7/8) 2 D.t D.t i z Δ
      (if 2*a-1≤5/6 then counts.cB else counts.cH)
      (if 2*a-1≤5/6 then counts.kB else counts.kH) C height D.t

lemma SourceMomentBound.mono_constant {Δ : ℝ} {D : HighData Δ} {F : SourceData D}
    {counts : CountParameters F.modulus ⊤ D.t} {η : Character} {Z τ C C' height : ℝ}
    (hZ : 0≤ Z) (h : SourceMomentBound F counts η Z τ C height) (hC : C≤ C') :
    SourceMomentBound F counts η Z τ C' height := by
  intro rows d a hd hd' ha ha' hrows i z hz hzh
  exact sourceMomentsAt_mono_constant F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell
    (fun _ y=>(F.w y:ℂ)) Z d a D.ε τ (7/8) 2 D.t D.t i z Δ _ _ C C' height D.t
    hZ hC (h rows d a hd hd' ha ha' hrows i z hz hzh)

def RawMomentInput : Prop :=
  ∀_hβ : (7/8:ℝ)< HeckeZeroSupremum.beta,
    ∀D : HighData (HeckeZeroSupremum.beta-7/8),∀F : SourceData D,
    ∀counts : CountParameters F.modulus ⊤ D.t,
    ∃J : ℝ,0≤ J ∧ ∀η : Character,∃C : ℝ,0< C ∧
      ∀τ : ℝ,0<τ → τ≤1 → ∀ᶠZ : ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))

lemma polynomial_height_absorption (C Z τ J t : ℝ)
    (hC : 0≤ C) (hZ : 1≤ Z) (hτ : 0≤τ) (hJ : 0≤ J) (hbudget : 2*τ*(1+J)≤ t) :
    C*(1+Z^(2*τ))^J≤(C*2^J)*Z^t := by
  have hZp : 0< Z := zero_lt_one.trans_le hZ
  have hscale : 1≤ Z^(2*τ) := Real.one_le_rpow hZ (by positivity)
  calc
    _≤ C*(2*Z^(2*τ))^J := by gcongr;linarith
    _=(C*2^J)*Z^(2*τ*J) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Real.rpow_nonneg hZp.le _),←Real.rpow_mul hZp.le]
      ring
    _≤(C*2^J)*Z^t := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)

theorem raw_input_chosen_height (h : RawMomentInput) (hβ : (7/8:ℝ)< HeckeZeroSupremum.beta)
    (D : HighData (HeckeZeroSupremum.beta-7/8)) (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t) :
    ∃τ : ℝ,0<τ ∧ τ<(1/200:ℝ)/2 ∧ 4*τ<(1/200:ℝ)*D.cost ∧ τ< D.t ∧
      2*τ≤ D.t ∧ τ*(2+4*D.eps)< D.t ∧
      ∀η : Character,∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*Z^D.t) (Z^(2*τ)) := by
  obtain ⟨J,hJ,hbound⟩ := h hβ D F counts
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτJ,hτeps⟩ := D.height_choice J hJ
  have htau1 : τ≤1 := by linarith
  refine ⟨τ,hτ,hτd,hτcost,hτt,by nlinarith,hτeps,?_⟩
  intro η
  obtain ⟨C,hC,hbound⟩ := hbound η
  refine ⟨C*2^J,by positivity,?_⟩
  filter_upwards [hbound τ hτ htau1,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  exact hb.mono_constant (by linarith) (polynomial_height_absorption C Z τ J D.t hC.le hZ hτ.le hJ hτJ)

end SevenEighths.ProbeFinalAssembly

end

end OAI
end
/- END ORIGINAL MODULE OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentInput -/

/- BEGIN ORIGINAL MODULE OAI.NumberTheory.DirichletL.Detector.FinalAssemblySourceCount ; sha256 e98e4fb99e2d1809acfbf2c7630d71c7a1ef1d37d19ce9be5a28e58959811f07 -/
section



namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorRowCount HeckeDetectorAdaptiveCutoff
open ProbeHighRowFamily

theorem balanced_source_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (_hH : RayOrthogonality.globalUnits M≤ H) (_S : Finset (Ideal O))
    (φ : ℝ→ℝ) (_hφ : ContDiff ℝ ∞ φ) (_hφc : HasCompactSupport φ)
    (_hφp : tsupport φ⊆Ioi 0) (_hφ0 : ∀y,0≤φ y) (_hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (_ha₀ : 0< a₀) (_hab₀ : a₀≤ b₀) (_hB₀ : 0< B₀)
    (_hφs : Function.support φ⊆Ioo a₀ b₀) (_hφB : ∀y,φ y≤ B₀)
    (εm : ℝ) (_hεm : 0<εm)
    (Label : Type) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth : ℝ)
    (hdmin : 0< dmin) (hdmax : 0< dmax) (hτ : 0<τ)
    (hl : 0< logCost) (hh : τ< heightCost) (hb : 0< binWidth) (counts : CountParameters M H εm) :
    ∃K : ℝ,0< K ∧ ∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax →
      ∀(a ε Δ ν C q : ℝ) (i : ℕ),i≤ n → 51/100< a → 2*a-1≤5/6 → a≤1 → 0≤ε → ε≤1/1000 →
      0≤Δ → Δ≤1/8 → 0<ν → 0≤ C →
      ∀{Slot : Type} (B : Batch M H Label Slot (Z^d) a ε
        (cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i),
      B.slots.card≤ N → B.binWidth=binWidth →
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=> u.val) B.profile B.upper B.widths B.external (Z^d)) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ counts.cB counts.kB (C*Z^momentCost) (Z^heightCost) εm) →
      (B.rows.card:ℝ)≤ K*C*Z^(logCost+heightCost+momentCost)*(Z^d)^(Endpoint.balancedRowCount (2*a-1) (1/2-q/(2*a-1))+Δ/4+159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨K₀,hK₀,hcount⟩ := counts.balanced
  obtain ⟨K,hK,hpref⟩ := source_count_prefactor_eventually (Label:=Label)
    N dmin dmax logCost heightCost momentCost binWidth K₀ hdmin hdmax hl (by linarith) hb
  refine ⟨K,hK,?_⟩
  filter_upwards [eventually_all_rpow_ge hcount dmin hdmin,hpref,
    source_count_frequency_eventually n dmax τ heightCost hdmax hτ hh,
    eventually_all_rpow_ge (eventually_gt_atTop (1:ℝ)) dmin hdmin,
    eventually_ge_atTop (1:ℝ)] with Z hcount hpref hfreq hU hZ
  intro d hd hd' a ε Δ ν C q i hi ha haδ ha' hε hε' hΔ hΔ' hν hC Slot B hslots hbin hne hq hmom
  have hcard := hcount d hd a ε (Z^τ) ((Z^d)^(τ/(2*dmax))) Δ ν
    (C*Z^momentCost) (Z^heightCost) q i (hU d hd) ha haδ hε hε' hΔ hΔ' hν (by positivity)
    (by positivity) (hfreq d hd' i hi) B hne hq hmom
  apply hcard.trans
  exact mul_le_mul_of_nonneg_right
    (hpref d hd hd' C a ε (cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i
      hC ha' B hslots hbin) (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _)

theorem high_source_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (_hH : RayOrthogonality.globalUnits M≤ H) (_S : Finset (Ideal O))
    (φ : ℝ→ℝ) (_hφ : ContDiff ℝ ∞ φ) (_hφc : HasCompactSupport φ)
    (_hφp : tsupport φ⊆Ioi 0) (_hφ0 : ∀y,0≤φ y) (_hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (_ha₀ : 0< a₀) (_hab₀ : a₀≤ b₀) (_hB₀ : 0< B₀)
    (_hφs : Function.support φ⊆Ioo a₀ b₀) (_hφB : ∀y,φ y≤ B₀)
    (εm : ℝ) (_hεm : 0<εm)
    (Label : Type) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth : ℝ)
    (hdmin : 0< dmin) (hdmax : 0< dmax) (hτ : 0<τ)
    (hl : 0< logCost) (hh : τ< heightCost) (hb : 0< binWidth) (counts : CountParameters M H εm) :
    ∃K : ℝ,0< K ∧ ∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax →
      ∀(a ε Δ C q : ℝ) (i : ℕ),i≤ n → 5/6<2*a-1 → a≤1 → 0≤ε → ε≤1/1000 → 0≤ C →
      ∀{Slot : Type} (B : Batch M H Label Slot (Z^d) a ε
        (cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i),
      B.slots.card≤ N → B.binWidth=binWidth →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ counts.cH counts.kH (C*Z^momentCost) (Z^heightCost) εm) →
      (B.rows.card:ℝ)≤ K*C*Z^(logCost+heightCost+momentCost)*(Z^d)^(1-(2*a-1)+78*ε+εm) := by
  obtain ⟨K₀,hK₀,hcount⟩ := counts.high
  obtain ⟨K,hK,hpref⟩ := source_count_prefactor_eventually (Label:=Label)
    N dmin dmax logCost heightCost momentCost binWidth K₀ hdmin hdmax hl (by linarith) hb
  refine ⟨K,hK,?_⟩
  filter_upwards [eventually_all_rpow_ge hcount dmin hdmin,hpref,
    source_count_frequency_eventually n dmax τ heightCost hdmax hτ hh,
    eventually_all_rpow_ge (eventually_gt_atTop (1:ℝ)) dmin hdmin,
    eventually_ge_atTop (1:ℝ)] with Z hcount hpref hfreq hU hZ
  intro d hd hd' a ε Δ C q i hi ha ha' hε hε' hC Slot B hslots hbin hmom
  have hcard := hcount d hd a ε (Z^τ) ((Z^d)^(τ/(2*dmax))) Δ
    (C*Z^momentCost) (Z^heightCost) q i (hU d hd) ha ha' hε hε' (by positivity)
    (by positivity) (hfreq d hd' i hi) B hmom
  apply hcard.trans
  exact mul_le_mul_of_nonneg_right
    (hpref d hd hd' C a ε (cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i
      hC ha' B hslots hbin) (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _)

theorem adaptive_source_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm : ℝ) (hεm : 0<εm)
    (Label : Type) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth : ℝ)
    (hdmin : 0< dmin) (hdmax : 0< dmax) (hτ : 0<τ)
    (hl : 0< logCost) (hh : τ< heightCost) (hb : 0< binWidth) (counts : CountParameters M H εm) :
    ∃K : ℝ,0< K ∧ ∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax →
      ∀(a ε Δ ν C q : ℝ) (i : ℕ),i≤ n → 51/100< a → a≤1 → 0≤ε → ε≤1/1000 →
      0≤Δ → Δ≤1/8 → 0<ν → 0≤ C →
      ∀{Slot : Type} (B : Batch M H Label Slot (Z^d) a ε
        (cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i),
      B.slots.card≤ N → B.binWidth=binWidth →
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=> u.val) B.profile B.upper B.widths B.external (Z^d)) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ (if 2*a-1≤5/6 then counts.cB else counts.cH) (if 2*a-1≤5/6 then counts.kB else counts.kH) (C*Z^momentCost) (Z^heightCost) εm) →
      (B.rows.card:ℝ)≤ K*C*Z^(logCost+heightCost+momentCost)*(Z^d)^(adaptiveRowExponent (2*a-1) q Δ ε εm B.mesh ν) := by
  obtain ⟨KB,hKB,hbalanced⟩ := balanced_source_count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
    Label N n dmin dmax τ logCost heightCost momentCost binWidth hdmin hdmax hτ hl hh hb counts
  obtain ⟨KH,hKH,hhigh⟩ := high_source_count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
    Label N n dmin dmax τ logCost heightCost momentCost binWidth hdmin hdmax hτ hl hh hb counts
  refine ⟨max KB KH,lt_of_lt_of_le hKB (le_max_left _ _),?_⟩
  filter_upwards [hbalanced,hhigh,eventually_ge_atTop (1:ℝ)] with Z hb hh hZ
  intro d hd hd' a ε Δ ν C q i hi ha ha' hε hε' hΔ hΔ' hν hC Slot B hslots hbin hne hq hmom
  by_cases hδ : 2*a-1≤5/6
  · simp only [ite_eq_left hδ] at hmom
    have hc := hb d hd hd' a ε Δ ν C q i hi ha hδ ha' hε hε' hΔ hΔ' hν hC B hslots hbin hne hq hmom
    simp only [adaptiveRowExponent,ite_eq_left hδ]
    exact hc.trans (by gcongr;exact le_max_left _ _)
  · simp only [ite_eq_right hδ] at hmom
    have hc := hh d hd hd' a ε Δ C q i hi (lt_of_not_ge hδ) ha' hε hε' hC B hslots hbin hmom
    simp only [adaptiveRowExponent,ite_eq_right hδ]
    exact hc.trans (by gcongr;exact le_max_right _ _)

end SevenEighths.ProbeFinalAssembly

end

end OAI
end
/- END ORIGINAL MODULE OAI.NumberTheory.DirichletL.Detector.FinalAssemblySourceCount -/
