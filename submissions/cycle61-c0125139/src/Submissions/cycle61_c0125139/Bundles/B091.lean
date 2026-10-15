/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B084
import Submissions.cycle61_c0125139.Bundles.B085
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorCoefficientTransfer
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DyadicSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonPairedSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SlotNormalization

/- BEGIN ORIGINAL Cycle61.Moment.JointColumnExtraction; sha256 7f3b285ca6ae7ce2188c5074f15bc3380f0e2574812778fdcdf78e7006b1e034 -/
section
                                             
                                                             

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentEligibleEnergy CenteredMomentExceptionalMaskedSource
open CenteredMomentActiveDivisorShell
open CenteredMomentExceptionalAmplitudePair CenteredMomentActiveAllocation
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentCommonRadialData CenteredMomentCommonLinearNormalization
open CenteredMomentCommonLinearSource CenteredMomentCommonPairedSource
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def retainedAllocationCost (s : Data ι) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2))) (z : O) : ℝ :=
  ((2*(max 1 s.b₁*max 1 s.b₂))*(∏ i ∈ frozenIndices L a, s.M i)^2 /
    formalReductionFactor L a s.P)*
    (‖Cycle61.Physical.sourcePositiveRow s.toSource false L a z‖^2+
     ‖Cycle61.Physical.sourcePositiveRow s.toSource true L a z‖^2)

theorem retained_allocation_cost_nonneg (s : Data ι) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2))) (z : O) :
    0 ≤ retainedAllocationCost s L a z := by
  unfold retainedAllocationCost
  exact mul_nonneg (div_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
    (s.reduction_pos L a).le) (add_nonneg (sq_nonneg _) (sq_nonneg _))

def RetainedPointwiseBound (ι : Type*) [Fintype ι] [DecidableEq ι]
    (C ε : ℝ) : Prop :=
  ∀ (s : Data ι) (L : Ideal O), Squarefree L → ∀ z : O,
    ‖maskedAmplitude s L z‖^2 ≤ C*(L.absNorm:ℝ)^ε*
      ∑ a ∈ s.toSource.active L, retainedAllocationCost s L a z

theorem actual_retained_pointwise (N : ℕ) (hslots : Fintype.card ι ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ RetainedPointwiseBound ι C ε := by
  obtain ⟨C,hC,hbound⟩ := active_raw_to_retained_energy (ι := ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro s L hL z
  have hh := hbound s.η s.m s.A s.t s.slots s.prime s.coefficient s.M s.P
    (fun i => zero_le_one.trans (s.M_ge_one i)) s.P_pos s.coefficient_bound L hL
    s.W₁ s.W₂ s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)
    s.support₁ s.support₂ s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos rfl s.same_product
    {z} (fun _ => 1) (by intros; norm_num)
  have hc : s.coefficient = (fun i I => s.ν i I*s.W i ((I.absNorm:ℝ)/s.P i)) := rfl
  rw [hc] at hh
  unfold maskedAmplitude
  rw [hc]
  simpa only [Finset.sum_singleton, one_mul, maskedAmplitude, volume,
    retainedAllocationCost, Cycle61.Physical.sourcePositiveRow,
    Cycle61.Physical.sourcePlainScales, ite_false, ite_true,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Bool.false_eq_true,
    Source.active,
    CenteredMomentEligibleEnergy.Data.coefficient] using hh

theorem uniform_retained_pointwise (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ J : Finset ι, RetainedPointwiseBound J C ε := by
  have he (J : Finset ι) : ∃ C : ℝ, 0 < C ∧ RetainedPointwiseBound J C ε :=
    actual_retained_pointwise (Fintype.card ι) (by simpa using Finset.card_le_univ J) ε hε
  choose C hC hb using he
  let D := 1+∑ J : Finset ι, C J
  have hs : 0 ≤ ∑ J : Finset ι, C J := Finset.sum_nonneg (fun J _ => (hC J).le)
  refine ⟨D,by dsimp only [D]; linarith,?_⟩
  intro J s L hL z
  have hd : C J ≤ D := by
    have hh := Finset.single_le_sum (fun J _ => (hC J).le) (Finset.mem_univ J)
    dsimp only [D]
    linarith
  exact (hb J s L hL z).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (Finset.sum_nonneg (fun a _ => retained_allocation_cost_nonneg s L a z)))

def commonRetainedCost (s : Input ι) (C R L : Ideal O) (z : O) : ℝ :=
  ((actualAllocations s.pools C).card:ℝ)*
    ∑ B : actualAllocations s.pools C, ‖commonScalar s C R B‖^2*
      ∑ a ∈ (commonData s C R B).toSource.active L,
        retainedAllocationCost (commonData s C R B) L a z

theorem common_retained_cost_nonneg (s : Input ι) (C R L : Ideal O) (z : O) :
    0 ≤ commonRetainedCost s C R L z := by
  unfold commonRetainedCost
  exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun B _ =>
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun a _ =>
      retained_allocation_cost_nonneg _ _ _ _))))

/-- Both extraction steps are performed on the literal column. No uniform
per-label child envelope has been taken at this stage. -/
theorem actual_common_column_extraction (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s : Input ι) (C : Ideal O) (hC : Supported C)
      (R seed L : Ideal O), seed ∣ C → Squarefree L → ∀ z : O,
      ‖normalizedColumn s C hC R seed L z‖^2 ≤
        K*(L.absNorm:ℝ)^ε*commonRetainedCost s C R L z := by
  obtain ⟨K,hK,hbound⟩ := uniform_retained_pointwise (ι := ι) ε hε
  refine ⟨K,hK,?_⟩
  intro s C hC R seed L hseed hL z
  have hh := CubicEisenstein.norm_sum_sq_le_card
    (Finset.univ : Finset (actualAllocations s.pools C))
    (fun B => commonScalar s C R B*maskedAmplitude (commonData s C R B) L z)
  rw [←source_normalized s C hC R seed L hseed z] at hh
  change ‖normalizedColumn s C hC R seed L z‖^2 ≤ _ at hh
  simp only [Finset.card_univ, Fintype.card_coe, norm_mul, mul_pow] at hh
  apply hh.trans
  calc
    _ ≤ ((actualAllocations s.pools C).card:ℝ)*
        ∑ B : actualAllocations s.pools C, ‖commonScalar s C R B‖^2*
          (K*(L.absNorm:ℝ)^ε*
            ∑ a ∈ (commonData s C R B).toSource.active L,
              retainedAllocationCost (commonData s C R B) L a z) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum (fun B _ => mul_le_mul_of_nonneg_left
        (hbound (liveIndices B.val) (commonData s C R B) L hL z) (sq_nonneg _))
    _ = _ := by
      unfold commonRetainedCost
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B hB
      apply Finset.sum_congr rfl
      intro a ha
      ring

theorem actual_joint_column_extraction {Label : Type*}
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (source : Label → Input ι)
      (C R seed L : Label → Ideal O) (hC : ∀ l, Supported (C l))
      (hseed : ∀ l, seed l ∣ C l) (hL : ∀ l, Squarefree (L l))
      (rows : Finset (Label×O)) (weight : Label×O → ℝ),
      (∀ k ∈ rows, 0 ≤ weight k) →
      (∑ k ∈ rows, weight k*
        ‖normalizedColumn (source k.1) (C k.1) (hC k.1) (R k.1) (seed k.1) (L k.1) k.2‖^2) ≤
      K*∑ k ∈ rows, weight k*(L k.1).absNorm^ε*
        commonRetainedCost (source k.1) (C k.1) (R k.1) (L k.1) k.2 := by
  obtain ⟨K,hK,hbound⟩ := actual_common_column_extraction (ι := ι) ε hε
  refine ⟨K,hK,?_⟩
  intro source C R seed L hC hseed hL rows weight hweight
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  exact (mul_le_mul_of_nonneg_left
    (hbound (source k.1) (C k.1) (hC k.1) (R k.1) (seed k.1) (L k.1)
      (hseed k.1) (hL k.1) k.2) (hweight k hk)).trans_eq (by ring)

#print axioms actual_retained_pointwise
#print axioms uniform_retained_pointwise
#print axioms actual_common_column_extraction
#print axioms actual_joint_column_extraction
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.JointColumnExtraction -/

/- BEGIN ORIGINAL Cycle61.Physical.BufferedPlain; sha256 1bfa34753971065c537c3da794a1768154f6ce5d26648eb975da3d106f322dc5 -/
section
                                          
                                                     
                                                                    

/-! Actual normalized retained plain rows and the genuine buffered Hecke dyadic bound.
Uses OpenAI/math family003 `Hecke.DyadicSource` without modifying frozen upstream.
Apache-2.0 upstream attribution retained. -/
namespace Cycle61.Physical
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators ContDiff
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic
open CenteredMomentHeckeHeight CenteredMomentRetainedProfile
open HeckeDetectorCoefficientTransfer
local notation "O" => HeckeFamily.O

/-- The all-ideal identity is structural; it is not a plain-row analytic bound. -/
theorem row_polynomial_phase (η χ : Character) (m z : O)
    (hcoeff : ∀ I : Ideal O, idealCoeff χ I =
      idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(1*z)) I)
    (W : ℝ→ℂ) (t X : ℝ) (hX : 0< X) :
    (Real.sqrt X : ℂ)⁻¹*rowTwistedSum η m 1 z W t X =
      (X : ℂ)^(Complex.I*t)*polynomial χ false W X 0 t := by
  have he := tsum_subtype_eq_of_support_subset
    (s := {I : Ideal O | I≠0})
    (f := fun I : Ideal O =>
      (idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(1*z)) I)*
        (Ideal.absNorm I : ℂ)^(Complex.I*t)*W ((Ideal.absNorm I : ℝ)/X))
    (by intro I hI hi; subst I; exact hI (by simp only [idealCoeff_zero,zero_mul]))
  have hs : (∑' I : NonzeroIdeal, twistedCoefficient χ false 0 t I*W (norm I/X)) =
      rowTwistedSum η m 1 z W t X := by
    unfold rowTwistedSum
    rw [←he]
    apply tsum_congr
    intro I
    simp only [twistedCoefficient,coefficient,Bool.false_eq_true,ite_false,hcoeff,HeckeDyadic.norm,
      HeckeDyadic.shift,Complex.ofReal_zero,zero_sub,neg_neg]
    push_cast
    simp only [mul_comm]
  rw [polynomial_eq_weighted χ false W X 0 t hX,hs,←mul_assoc,
    ←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hX.ne')]
  have hexp : Complex.I*t+(HeckeDyadic.shift 0 t-(1/2 : ℂ)) = -(1/2 : ℂ) := by
    unfold HeckeDyadic.shift
    push_cast
    ring
  rw [hexp,Complex.cpow_neg,Real.sqrt_eq_rpow]
  congr 2
  simpa using (Complex.ofReal_cpow hX.le (1/2 : ℝ))

/-- Both whole-character orientations preserve the normalized row norm.
The frequency is `t`; the raw row's missing phase has unit modulus. -/
theorem row_polynomial_norm_oriented (η χ : Character) (m z : O) (reverse : Bool)
    (hcoeff : ∀ I : Ideal O,
      idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(1*z)) I =
        if reverse then star (idealCoeff χ I) else idealCoeff χ I)
    (W : ℝ→ℂ) (t X : ℝ) (hX : 0< X) :
    ‖(Real.sqrt X : ℂ)⁻¹*rowTwistedSum η m 1 z W t X‖ =
      ‖polynomial χ false (orientedProfile reverse W) X 0 (orientedFrequency reverse t)‖ := by
  have hnorm (ψ : Character)
      (hc : ∀ I : Ideal O, idealCoeff ψ I =
        idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(1*z)) I) :
      ‖(Real.sqrt X : ℂ)⁻¹*rowTwistedSum η m 1 z W t X‖ =
        ‖polynomial ψ false W X 0 t‖ := by
    rw [row_polynomial_phase η ψ m z hc W t X hX,norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hX]
    simp
  cases reverse
  · simpa only [orientedProfile,orientedFrequency,Bool.false_eq_true,ite_false] using
      hnorm χ (fun I => (hcoeff I).symm)
  · have hc : ∀ I : Ideal O, idealCoeff χ.inverse I =
        idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(1*z)) I := by
      intro I
      simpa only [idealCoeff_inverse_conj,ite_true,starRingEnd_apply] using (hcoeff I).symm
    rw [hnorm χ.inverse hc]
    exact norm_of_oriented_coefficients χ.inverse χ true
      (fun I => by simp only [idealCoeff_inverse_conj,ite_true]) false W X 0 t hX

/-- Clipping changes the profile, while the scalar normalizer still uses the literal
clipped scale. Raw scales below one are included. -/
theorem clipped_row_polynomial_norm (η χ : Character) (m z : O) (reverse : Bool)
    (hcoeff : ∀ I : Ideal O,
      idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(1*z)) I =
        if reverse then star (idealCoeff χ I) else idealCoeff χ I)
    (W : ℝ→ℂ) (t X : ℝ) (hX : 0< X) :
    ‖(Real.sqrt (clippedScale X) : ℂ)⁻¹*rowTwistedSum η m 1 z W t X‖ =
      ‖polynomial χ false (orientedProfile reverse (dilated W (clipDilation X)))
        (clippedScale X) 0 (orientedFrequency reverse t)‖ := by
  rw [clipped_rowTwistedSum η m 1 z W t X hX]
  exact row_polynomial_norm_oriented η χ m z reverse hcoeff _ t _
    (zero_lt_one.trans_le (clippedScale_ge_one X))


/-- The retained square-root normalizer is exactly the complex power at exponent
`-1/2`; this equality does not move any clipping ratio into the row estimate. -/
theorem sqrt_inverse_eq_cpow (X : ℝ) (hX : 0< X) :
    (Real.sqrt X : ℂ)⁻¹=(X : ℂ)^(-(1/2 : ℂ)) := by
  rw [Complex.cpow_neg,Real.sqrt_eq_rpow]
  congr 1
  simpa using Complex.ofReal_cpow hX.le (1/2 : ℝ)

/-- The allocation parameter is obtained from the actual clipped scale, even when
the raw logarithmic scale is negative. Its upper cap is a separate scalar gate. -/
theorem clipped_scale_parameter (U X R : ℝ) (hU : 1< U)
    (hcap : clippedScale X≤ U^R) :
    0≤ Real.logb U (clippedScale X) ∧
    Real.logb U (clippedScale X)≤ R ∧
    U^(Real.logb U (clippedScale X))=clippedScale X := by
  have hX : 0< clippedScale X := zero_lt_one.trans_le (clippedScale_ge_one X)
  refine ⟨Real.logb_nonneg hU (clippedScale_ge_one X),?_,?_⟩
  · have hh := Real.logb_le_logb_of_le hU hX hcap
    simpa only [Real.logb_rpow (zero_lt_one.trans hU) hU.ne'] using hh
  · exact Real.rpow_logb (zero_lt_one.trans hU) hU.ne' hX

/-- Uniform buffered plain estimate for actual retained rows. The constants and the
Mellin order are chosen before the finite character family, the row, its orientation,
and its profile. Consequently one pair of constants works for all four finite
Mellin derivative pairs when their two displayed profile budgets hold.

The all-ideal coefficient gate belongs to the actual natural masked character.
The buffered zero gate is on that same character family. Its transfer from a raw
family is a separate algebraic zero-transport obligation, not an analytic assumption
inside this theorem. The scale equality retains the literal clipping allocation. -/
theorem buffered_clipped_plain_bounds (R dmax τ ε e κ v : ℝ)
    (hR : 0≤ R) (hdmax : 0≤ dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hv : 0≤ v)
    (hbudget : 12*e*(R+2)+8*κ+2*v≤ε)
    (profileBound : ℕ→ℝ) (hprofile : ∀ k, 0≤ profileBound k) :
    ∃ n : ℕ, ∃ C : ℝ, 0< C ∧
    ∀ (Z d : ℝ), 1≤ Z → 0≤ d → d≤ dmax → 2< Z^τ →
    ∀ {ι : Type*} [Fintype ι] (χ : ι→ Character)
      (hχ : ∀ j, (χ j).residue≠1) (a : ℝ) (i : ℕ),
      51/100≤ a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*Z^τ)< a+2*e →
    ∀ (j : ι) (η : Character) (m z : O) (reverse : Bool),
      (∀ I : Ideal O,
        idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(1*z)) I =
          if reverse then star (idealCoeff (χ j) I) else idealCoeff (χ j) I) →
    ∀ (W : ℝ→ℂ) (X r t A B : ℝ), 0< X →
      clippedScale X=(Z^d)^r → 0< A →
      Function.support (orientedProfile reverse (dilated W (clipDilation X)))⊆Set.Icc A B →
      ContDiff ℝ ∞ (orientedProfile reverse (dilated W (clipDilation X))) →
      (χ j).modulus.absNorm≤ Z^d → 0≤ r → r≤ R →
      |t|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^4≤(Z^d)^v →
      (∀ x ∈ Set.Icc (1-a-6*e) 2, ∀ u : ℝ,
        (1+|u|)^2*‖mellin (orientedProfile reverse (dilated W (clipDilation X)))
          ((x : ℂ)+u*Complex.I)‖≤ profileBound 2) →
      (∀ x ∈ Set.Icc (1-a-6*e) 2, ∀ u : ℝ,
        (1+|u|)^(n+2)*‖mellin (orientedProfile reverse (dilated W (clipDilation X)))
          ((x : ℂ)+u*Complex.I)‖≤ profileBound (n+2)) →
      ‖(Real.sqrt (clippedScale X) : ℂ)⁻¹*rowTwistedSum η m 1 z W t X‖^2
        ≤ C*(Z^d)^((2*a-1)*r+ε) ∧
      ‖(Real.sqrt (clippedScale X) : ℂ)⁻¹*rowTwistedSum η m 1 z W t X‖^2
        ≤ C*(Z^d)^((2*a-1)*min r (1-r)+ε) := by
  obtain ⟨n,C,hC,hsource⟩ := source_dyadic_bounds R dmax τ ε e κ v
    hR hdmax hτ hε he he' hκ hκ' hv hbudget profileBound hprofile
  refine ⟨n,C,hC,?_⟩
  intro Z d hZ hd hdmax' hT ι _ χ hχ a i ha ha' hzero j η m z reverse hcoeff
    W X r t A B hX hscale hA hsupport hsmooth hmod hr hrR hfreq hheight hm₂ hmn
  have hf : |orientedFrequency reverse t|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ := by
    simpa only [orientedFrequency_abs] using hfreq
  have hm₂' : ∀ x ∈ Set.Icc (1-a-6*e-0) (2-0), ∀ u : ℝ,
      (1+|u|)^2*‖mellin (orientedProfile reverse (dilated W (clipDilation X)))
        ((x : ℂ)+u*Complex.I)‖≤ profileBound 2 := by simpa only [sub_zero] using hm₂
  have hmn' : ∀ x ∈ Set.Icc (1-a-6*e-0) (2-0), ∀ u : ℝ,
      (1+|u|)^(n+2)*‖mellin (orientedProfile reverse (dilated W (clipDilation X)))
        ((x : ℂ)+u*Complex.I)‖≤ profileBound (n+2) := by simpa only [sub_zero] using hmn
  have hbound := hsource Z d hZ hd hdmax' hT χ hχ a i ha ha' hzero j false
    (orientedProfile reverse (dilated W (clipDilation X))) A B hA hsupport hsmooth
    r 0 (orientedFrequency reverse t) hmod hr hrR hf hheight hm₂' hmn'
  rw [clipped_row_polynomial_norm η (χ j) m z reverse hcoeff W t X hX,hscale]
  exact hbound

end
end Cycle61.Physical

#print axioms Cycle61.Physical.row_polynomial_phase
#print axioms Cycle61.Physical.row_polynomial_norm_oriented
#print axioms Cycle61.Physical.clipped_row_polynomial_norm
#print axioms Cycle61.Physical.buffered_clipped_plain_bounds


-- Check actual theorem dependencies, rather than the set of imported modules.
-- This command writes no auxiliary file and uses no evaluation-based proof shortcut.
set_option maxHeartbeats 0 in
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let root := ``Cycle61.Physical.buffered_clipped_plain_bounds
  let mut todo : Array Name := #[root]
  let mut seen : NameSet := {}
  let mut idx := 0
  let mut denied : Array Name := #[]
  let mut missing : Array Name := #[]
  while idx < todo.size do
    let n := todo[idx]!
    idx := idx+1
    if seen.contains n then continue
    seen := seen.insert n
    if n == ``sorryAx || #["Cycle25.", "WeightedQRH.", "ZetaZeroFree.Final",
        "ZetaZeroFree.Analytic.Final", "beta_le_seven_eighths", "UnconditionalOAI",
        "ZetaUnconditional"].any (fun ban => (n.toString.splitOn ban).length>1) then
      denied := denied.push n
    match env.find? n with
    | none => missing := missing.push n
    | some ci =>
      for dep in ci.getUsedConstantsAsSet.toArray do
        if #["OAI.", "Cycle25.", "Cycle61.", "ZetaZeroFree.",
            "_private.OAI.", "_private.Cycle61.", "_private.Cycle25.",
            "_private.ZetaZeroFree."].any (fun p => dep.toString.startsWith p) then
          todo := todo.push dep
  unless seen.contains ``OAI.SevenEighths.HeckeDyadic.source_dyadic_bounds &&
      seen.contains ``Cycle61.Physical.row_polynomial_phase do
    throwError "The actual row/source dyadic theorem is missing from the proof closure"
  logInfo m!"{root}: {seen.size} project constants; genuine source dyadic + actual phase present; denied={denied}; missing={missing}"
  unless denied.isEmpty && missing.isEmpty do
    throwError "BufferedPlain actual dependency audit rejected"

end
/- END ORIGINAL Cycle61.Physical.BufferedPlain -/

/- BEGIN ORIGINAL Cycle61.Moment.PositiveRowFactors; sha256 413cf16558eb3e51833c23f402329a5a782a329af57f1714af20a646b08e7c0d -/
section
                                           
                                     
                                                            

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
open CenteredMomentHeckeSlots CenteredMomentHeckeHeight CenteredMomentWholeSlotDeletion
open CenteredMomentSlotNormalization CenteredMomentEligibleEnergy
open CenteredMomentDivisorRetained CenteredMomentDivisorAllocation
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actual_positive_row_factors (η : Character) (m A z : O)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hP : ∀ i, 0 < P i) :
    positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂ =
      ((Real.sqrt X₁ : ℂ)⁻¹*rowTwistedSum η m A z W₁ t X₁)*
      ((Real.sqrt X₂ : ℂ)⁻¹*rowTwistedSum η m A z W₂ t X₂)*
      ∏ i, normalizedSlot η m A z (S i) (β i) t (P i) := by
  rw [←selectedProduct_univ η m A z W₁ W₂ S β P t X₁ X₂
    (mul_pos hX₁ hX₂).le (fun i => (hP i).le)]
  unfold selectedProduct
  rw [Real.sqrt_mul hX₁.le, Complex.ofReal_mul, mul_inv_rev]
  ring

theorem actual_retained_row_factors (η : Character) (m A z : O)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hP : ∀ i, 0 < P i) :
    retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂ =
      ((Real.sqrt (clippedScale X₁) : ℂ)⁻¹*rowTwistedSum η m A z W₁ t X₁)*
      ((Real.sqrt (clippedScale X₂) : ℂ)⁻¹*rowTwistedSum η m A z W₂ t X₂)*
      ∏ i, normalizedSlot η m A z (S i) (β i) t (P i) := by
  unfold retainedPositiveRow
  rw [actual_positive_row_factors η m A z _ _ S β P t _ _
    (zero_lt_one.trans_le (clippedScale_ge_one X₁))
    (zero_lt_one.trans_le (clippedScale_ge_one X₂)) hP,
    clipped_rowTwistedSum η m A z W₁ t X₁ hX₁,
    clipped_rowTwistedSum η m A z W₂ t X₂ hX₂]

theorem actual_retained_row_squared_factors (η : Character) (m A z : O)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hP : ∀ i, 0 < P i) :
    ‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2 =
      ‖(Real.sqrt (clippedScale X₁) : ℂ)⁻¹*rowTwistedSum η m A z W₁ t X₁‖^2*
      ‖(Real.sqrt (clippedScale X₂) : ℂ)⁻¹*rowTwistedSum η m A z W₂ t X₂‖^2*
      ∏ i, ‖normalizedSlot η m A z (S i) (β i) t (P i)‖^2 := by
  rw [actual_retained_row_factors η m A z W₁ W₂ S β P t X₁ X₂ hX₁ hX₂ hP]
  simp only [norm_mul, mul_pow, norm_prod, Finset.prod_pow]

theorem actual_retained_row_bound (η : Character) (m A z : O)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hP : ∀ i, 0 < P i)
    (B₁ B₂ : ℝ) (B : ι → ℝ)
    (h₁ : ‖(Real.sqrt (clippedScale X₁) : ℂ)⁻¹*rowTwistedSum η m A z W₁ t X₁‖^2 ≤ B₁)
    (h₂ : ‖(Real.sqrt (clippedScale X₂) : ℂ)⁻¹*rowTwistedSum η m A z W₂ t X₂‖^2 ≤ B₂)
    (hslot : ∀ i, ‖normalizedSlot η m A z (S i) (β i) t (P i)‖^2 ≤ B i) :
    ‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2 ≤ B₁*B₂*∏ i, B i := by
  rw [actual_retained_row_squared_factors η m A z W₁ W₂ S β P t X₁ X₂ hX₁ hX₂ hP]
  exact mul_le_mul
    (mul_le_mul h₁ h₂ (sq_nonneg _) ((sq_nonneg _).trans h₁))
    (Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _) (fun i _ => hslot i))
    (Finset.prod_nonneg (fun _ _ => sq_nonneg _))
    (mul_nonneg ((sq_nonneg _).trans h₁) ((sq_nonneg _).trans h₂))

#print axioms actual_positive_row_factors
#print axioms actual_retained_row_factors
#print axioms actual_retained_row_squared_factors
#print axioms actual_retained_row_bound
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.PositiveRowFactors -/

/- BEGIN ORIGINAL Cycle61.Moment.BufferedRetainedRows; sha256 46bd9f50787c34a644cd2863d38a75414013a8755ea77196c203d47b07abcd5c -/
section
                                        

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators ContDiff
open HeckeFamily HeckeDyadic HeckeDetectorCoefficientTransfer
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
open CenteredMomentWholeSlotDeletion
local notation "O" => HeckeFamily.O

/-- The two genuine buffered plain estimates enter the literal retained row.
Every live normalized slot remains in the bound, to be charged at the same bin. -/
theorem actual_buffered_retained_plain_factors
    (R dmax τ ε e κ v : ℝ)
    (hR : 0 ≤ R) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hκ' : κ ≤ 1) (hv : 0 ≤ v)
    (hbudget : 12*e*(R+2)+8*κ+2*v ≤ ε)
    (profileBound : ℕ → ℝ) (hprofile : ∀ k, 0 ≤ profileBound k) :
    ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ Z d : ℝ, 1 ≤ Z → 0 ≤ d → d ≤ dmax → 2 < Z^τ →
    ∀ {Dict : Type*} [Fintype Dict] (χ : Dict → Character)
      (hχ : ∀ j, (χ j).residue ≠ 1) (a : ℝ) (i : ℕ),
      51/100 ≤ a → a ≤ 1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*Z^τ) < a+2*e →
    ∀ (j : Dict) (η : Character) (m z : O) (reverse : Bool),
      (∀ I : Ideal O,
        idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(1*z)) I =
          if reverse then star (idealCoeff (χ j) I) else idealCoeff (χ j) I) →
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ),
      (∀ k, 0 < P k) →
    ∀ (W : Fin 2 → ℝ → ℂ) (X r A B : Fin 2 → ℝ) (t : ℝ),
      (∀ k, 0 < X k) → (∀ k, clippedScale (X k) = (Z^d)^(r k)) →
      (∀ k, 0 < A k) →
      (∀ k, Function.support (orientedProfile reverse (dilated (W k) (clipDilation (X k))))
        ⊆ Set.Icc (A k) (B k)) →
      (∀ k, ContDiff ℝ ∞ (orientedProfile reverse (dilated (W k) (clipDilation (X k))))) →
      (χ j).modulus.absNorm ≤ Z^d →
      (∀ k, 0 ≤ r k) → (∀ k, r k ≤ R) →
      |t|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^4 ≤ (Z^d)^v →
      (∀ k, ∀ x ∈ Set.Icc (1-a-6*e) 2, ∀ u : ℝ,
        (1+|u|)^2*‖mellin (orientedProfile reverse (dilated (W k) (clipDilation (X k))))
          ((x : ℂ)+u*Complex.I)‖ ≤ profileBound 2) →
      (∀ k, ∀ x ∈ Set.Icc (1-a-6*e) 2, ∀ u : ℝ,
        (1+|u|)^(n+2)*‖mellin (orientedProfile reverse (dilated (W k) (clipDilation (X k))))
          ((x : ℂ)+u*Complex.I)‖ ≤ profileBound (n+2)) →
      ‖retainedPositiveRow η m 1 z (W 0) (W 1) S β P t (X 0) (X 1)‖^2 ≤
        C^2*(Z^d)^((2*a-1)*(r 0+r 1)+2*ε)*
          ∏ k, ‖normalizedSlot η m 1 z (S k) (β k) t (P k)‖^2 := by
  obtain ⟨n,C,hC,hplain⟩ := Cycle61.Physical.buffered_clipped_plain_bounds
    R dmax τ ε e κ v hR hdmax hτ hε he he' hκ hκ' hv hbudget profileBound hprofile
  refine ⟨n,C,hC,?_⟩
  intro Z d hZ hd hdm hT Dict _ χ hχ a i ha ha' hzero j η m z reverse hcoeff
    ι _ _ S β P hP W X r A B t hX hscale hA hsupport hsmooth hmod hr hrR
    hfreq hheight hm₂ hmn
  have hb (k : Fin 2) := (hplain Z d hZ hd hdm hT χ hχ a i ha ha' hzero
    j η m z reverse hcoeff (W k) (X k) (r k) t (A k) (B k)
    (hX k) (hscale k) (hA k) (hsupport k) (hsmooth k) hmod
    (hr k) (hrR k) hfreq hheight (hm₂ k) (hmn k)).1
  have hh := actual_retained_row_bound η m 1 z (W 0) (W 1) S β P t (X 0) (X 1)
    (hX 0) (hX 1) hP (C*(Z^d)^((2*a-1)*r 0+ε))
    (C*(Z^d)^((2*a-1)*r 1+ε))
    (fun k => ‖normalizedSlot η m 1 z (S k) (β k) t (P k)‖^2)
    (hb 0) (hb 1) (fun _ => le_rfl)
  apply hh.trans_eq
  have hZd : 0 < Z^d := Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _
  rw [show (C*(Z^d)^((2*a-1)*r 0+ε))*(C*(Z^d)^((2*a-1)*r 1+ε)) =
      C^2*((Z^d)^((2*a-1)*r 0+ε)*(Z^d)^((2*a-1)*r 1+ε)) by ring,
    ←Real.rpow_add hZd]
  congr 2
  ring

#print axioms actual_buffered_retained_plain_factors
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.BufferedRetainedRows -/
