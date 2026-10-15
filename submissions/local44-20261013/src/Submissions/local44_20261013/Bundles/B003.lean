/- Deterministically bundled proof sources; original notices are retained below. -/
import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.Euler
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.HighRowsClosed
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.Local
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.MellinBoundary
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DyadicContour
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.BufferedIntegral
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CentralCube
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonprincipalBoundary
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.TupleGrowth

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Damping ; sha256 a492680bf8b3444dd814caf9b9fc7fa230fab3d8d35fc4efe552c1f14f043d93 -/
section






/-!
Variable-κ conductor damping for the Cycle25 physical numerator.

The finite coefficient-removal argument is adapted from
akashlevy/QuasiRiemannTracker, commit
2fd60c0926b66ea18d7436f5ed55250fd006ab5d,
WeightedQRH/NumeratorDamping.lean (Apache-2.0).

These are scalar and finite-sum lemmas. Their use in a physical moment still
requires the actual coefficient/conductor dictionary, which is not an axiom
or an implicit hypothesis of this file.
-/

noncomputable section
open scoped BigOperators

namespace Cycle25.Numerator

def selectedCapacity (κ z t : ℝ) : ℝ := max 0 (z - t / (3 * κ))

theorem selectedCapacity_nonneg (κ z t : ℝ) : 0 ≤ selectedCapacity κ z t :=
  le_max_left _ _

theorem capacity_damping {κ δ q z t : ℝ}
    (hκ : 0 < κ) (hq : 0 ≤ q) (hqδ : q ≤ δ / 2) (ht : 0 ≤ t) :
    -δ * t / 4 - q * selectedCapacity κ z t / 2 ≤
      -q * z / 2 - δ * t * (1 / 4 - 1 / (12 * κ)) := by
  have hcap : z - t / (3 * κ) ≤ selectedCapacity κ z t := le_max_right _ _
  have hmul := mul_le_mul_of_nonneg_left hcap hq
  have hqt := mul_le_mul_of_nonneg_right hqδ ht
  have hcost : q * t / (3 * κ) ≤ δ * t / (6 * κ) := by
    calc
      _ ≤ (δ / 2) * t / (3 * κ) := div_le_div_of_nonneg_right hqt (by positivity)
      _ = _ := by field_simp; ring
  have hmul' : q * z - q * t / (3 * κ) ≤ q * selectedCapacity κ z t := by
    nlinarith [show q * (z - t / (3 * κ)) = q * z - q * t / (3 * κ) by ring]
  have hidentity : δ * t * (1 / 4 - 1 / (12 * κ)) =
      δ * t / 4 - (δ * t / (6 * κ)) / 2 := by field_simp; ring
  rw [hidentity]
  linarith

theorem damping_reserve {κ : ℝ} (hκ : 7 / 10 ≤ κ) :
    11 / 84 ≤ 1 / 4 - 1 / (12 * κ) := by
  have hκpos : 0 < κ := by linarith
  have hfrac : 1 / (12 * κ) ≤ 5 / 42 := by
    apply (div_le_iff₀ (show 0 < 12 * κ by positivity)).2
    linarith
  linarith

theorem capacity_damping_uniform {κ δ q z t : ℝ}
    (hκ : 7 / 10 ≤ κ) (hq : 0 ≤ q) (hqδ : q ≤ δ / 2) (ht : 0 ≤ t) :
    -δ * t / 4 - q * selectedCapacity κ z t / 2 ≤
      -q * z / 2 - 11 * δ * t / 84 := by
  have hδ : 0 ≤ δ := by linarith
  have h := capacity_damping (by linarith : 0 < κ) hq hqδ ht (z := z)
  have hr := mul_le_mul_of_nonneg_left (damping_reserve hκ) (mul_nonneg hδ ht)
  nlinarith

theorem capacity_damping_weak {κ δ q z t : ℝ}
    (hκ : 7 / 10 ≤ κ) (hq : 0 ≤ q) (hqδ : q ≤ δ / 2) (ht : 0 ≤ t) :
    -δ * t / 4 - q * selectedCapacity κ z t / 2 ≤ -q * z / 2 := by
  have hδ : 0 ≤ δ := by linarith
  have h := capacity_damping_uniform hκ hq hqδ ht (z := z)
  have := mul_nonneg hδ ht
  linarith

theorem capacity_feasible {κ n z t : ℝ} (hκ : 0 < κ)
    (hbase : 2 * n + 6 * κ * z ≤ 1) (hbranch : 0 ≤ z - t / (3 * κ)) :
    2 * (n + t) + 6 * κ * selectedCapacity κ z t ≤ 1 := by
  rw [selectedCapacity, max_eq_right hbranch]
  have hid : 2 * (n + t) + 6 * κ * (z - t / (3 * κ)) = 2 * n + 6 * κ * z := by
    field_simp
    nlinarith [ne_of_gt hκ]
  rw [hid]
  exact hbase

/-- Remove the finite row-dependent coefficient expansion before applying a
common moment estimate. The weighted mass remains an explicit proved input. -/
theorem coefficient_mass_removal {ι : Type*} (s : Finset ι) (A S : ι → ℂ)
    (w : ι → ℝ) (M B : ℝ) (hM : 0 ≤ M)
    (hmass : ∑ i ∈ s, ‖A i‖ * w i ≤ B)
    (hS : ∀ i ∈ s, ‖S i‖ ≤ M * w i) :
    ‖∑ i ∈ s, A i * S i‖ ≤ M * B := by
  calc
    _ ≤ ∑ i ∈ s, ‖A i * S i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ‖A i‖ * (M * w i) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hS i hi) (norm_nonneg _)
    _ = M * ∑ i ∈ s, ‖A i‖ * w i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ M * B := mul_le_mul_of_nonneg_left hmass hM

end Cycle25.Numerator
end
/- END ORIGINAL MODULE Cycle25.Numerator.Damping -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.FiniteHeight ; sha256 fab662a92c2267391fd519673993b289ec867d0ca6875ae1d4ba4481e7e24132 -/
section


/-! One height degree, positive constant and eventual threshold for a fixed finite
family. In particular the finite error masks do not alter the order in which the
height parameter is chosen. The empty indexing family is permitted. -/
noncomputable section
open scoped Classical BigOperators
open Filter
namespace Cycle25.Numerator

/-- A finite family has a common real height degree and positive constant,
controlling each term and their sum. All choices precede H and epsilon. -/
theorem finite_height_envelope {ι:Type*} [Fintype ι]
    (degree:ι→ℕ) (C:ι→ℝ) (hC:∀i,0< C i) :
    ∃J:ℝ,0≤ J ∧ ∃Ctot:ℝ,1≤ Ctot ∧
      (∀i,(degree i:ℝ)≤ J ∧ C i≤ Ctot) ∧
      ∀H eps:ℝ,0≤ H → 0≤ eps →
        (∀i,C i*(3+H)^((degree i:ℝ)+2*eps)≤ Ctot*(3+H)^(J+2*eps)) ∧
        (∑i,C i*(3+H)^((degree i:ℝ)+2*eps))≤ Ctot*(3+H)^(J+2*eps) := by
  let J:ℝ := (∑i,degree i:ℕ)
  let Ctot:ℝ := 1+∑i,C i
  have hsum : 0≤∑i,C i := Finset.sum_nonneg (fun i _=>(hC i).le)
  have hCtot : 1≤ Ctot := by dsimp [Ctot];linarith
  have hdegree (i:ι) : (degree i:ℝ)≤ J := by
    dsimp only [J]
    exact_mod_cast (Finset.single_le_sum (fun j (_:j∈Finset.univ)=> Nat.zero_le (degree j))
      (Finset.mem_univ i))
  have hcoeff (i:ι) : C i≤ Ctot := by
    have hi := Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(hC j).le) (Finset.mem_univ i)
    dsimp only [Ctot]
    linarith
  refine ⟨J,by dsimp [J];positivity,Ctot,hCtot,fun i=>⟨hdegree i,hcoeff i⟩,?_⟩
  intro H eps hH heps
  have hbase : 1≤3+H := by linarith
  have hpow : 0≤(3+H)^(J+2*eps) := Real.rpow_nonneg (by linarith) _
  have hterm (i:ι) : C i*(3+H)^((degree i:ℝ)+2*eps)≤ C i*(3+H)^(J+2*eps) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hbase (by linarith [hdegree i])) (hC i).le
  constructor
  · intro i
    exact (hterm i).trans (mul_le_mul_of_nonneg_right (hcoeff i) hpow)
  · calc
      _ ≤ ∑i,C i*(3+H)^(J+2*eps) := Finset.sum_le_sum (fun i _=> hterm i)
      _ = (∑i,C i)*(3+H)^(J+2*eps) := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp only [Ctot];linarith) hpow

/-- Finite many eventual estimates have one threshold, for an arbitrary filter. -/
theorem eventually_finite_all {ι α:Type*} [Finite ι] (l:Filter α) (P:ι→α→Prop)
    (hP:∀i,∀ᶠx in l,P i x) : ∀ᶠx in l,∀i,P i x :=
  Filter.eventually_all.mpr hP

/-- Simultaneous collection of fixed degrees, constants and eventual estimates.
This is convenient when each finite error-mask theorem first produces its own
height degree and threshold. -/
theorem finite_height_eventual_envelope {ι α:Type*} [Fintype ι]
    (l:Filter α) (P:ι→ℕ→ℝ→α→Prop)
    (hP:∀i,∃degree:ℕ,∃C:ℝ,0< C ∧ ∀ᶠx in l,P i degree C x) :
    ∃degree:ι→ℕ,∃C:ι→ℝ,∃J:ℝ,∃Ctot:ℝ,
      0≤ J ∧ 1≤ Ctot ∧ (∀i,0< C i) ∧
      (∀i,(degree i:ℝ)≤ J ∧ C i≤ Ctot) ∧
      (∀H eps:ℝ,0≤ H → 0≤ eps →
        (∀i,C i*(3+H)^((degree i:ℝ)+2*eps)≤ Ctot*(3+H)^(J+2*eps)) ∧
        (∑i,C i*(3+H)^((degree i:ℝ)+2*eps))≤ Ctot*(3+H)^(J+2*eps)) ∧
      ∀ᶠx in l,∀i,P i (degree i) (C i) x := by
  choose degree C hC hevent using hP
  obtain ⟨J,hJ,Ctot,hCtot,hbounds,hheight⟩ := finite_height_envelope degree C hC
  exact ⟨degree,C,J,Ctot,hJ,hCtot,hC,hbounds,hheight,eventually_finite_all l _ hevent⟩

end Cycle25.Numerator
end

/- Adapted from weighted-numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.FiniteHeight -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Holder ; sha256 988093cb56bec632ed763a61acee0fcbe08619ee838ecc2c8b66d4592e6d1e1a -/
section




/-! Finite-row inequalities for the weighted physical numerator.

These are unconditional inequalities about the actual finite sums.  In particular, the
selected prime factors occur inside the fourth moment with exponent two, not four.
-/

noncomputable section
open scoped BigOperators
namespace Cycle25.Numerator

theorem sum_fourth_le_card_cube {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 4 ≤ (s.card : ℝ) ^ 3 * ∑ i ∈ s, f i ^ 4 := by
  have h₁ := Finset.sum_mul_sq_le_sq_mul_sq s f (fun _ => (1 : ℝ))
  have h₂ := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => f i ^ 2) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h₁ h₂
  have h₁' : ((∑ i ∈ s, f i) ^ 2) ^ 2 ≤
      ((∑ i ∈ s, f i ^ 2) * (s.card : ℝ)) ^ 2 := by
    exact pow_le_pow_left₀ (sq_nonneg _) h₁ 2
  have h₂' := mul_le_mul_of_nonneg_right h₂ (sq_nonneg (s.card : ℝ))
  simp only [← pow_mul] at h₂
  calc
    _ ≤ ((∑ i ∈ s, f i ^ 2) * (s.card : ℝ)) ^ 2 := by
      simpa only [← pow_mul] using h₁'
    _ = (s.card : ℝ) ^ 2 * (∑ i ∈ s, f i ^ 2) ^ 2 := by ring
    _ ≤ (s.card : ℝ) ^ 2 * ((∑ i ∈ s, f i ^ 4) * (s.card : ℝ)) :=
      mul_le_mul_of_nonneg_left h₂ (sq_nonneg _)
    _ = _ := by ring

/-- The exact fourth-power form of the weighted Hölder step.  Only a pointwise lower
bound for the selected prime product is required. -/
theorem weighted_row_holder {ι : Type*} (s : Finset ι) (S Q : ι → ℂ)
    (L : ℝ) (hL : 0 ≤ L) (hQ : ∀ i ∈ s, L ≤ ‖Q i‖) :
    L ^ 2 * (∑ i ∈ s, ‖S i‖) ^ 4 ≤
      (s.card : ℝ) ^ 3 * ∑ i ∈ s, ‖S i‖ ^ 4 * ‖Q i‖ ^ 2 := by
  calc
    _ ≤ L ^ 2 * ((s.card : ℝ) ^ 3 * ∑ i ∈ s, ‖S i‖ ^ 4) :=
      mul_le_mul_of_nonneg_left (sum_fourth_le_card_cube s (fun i => ‖S i‖))
        (sq_nonneg _)
    _ = (s.card : ℝ) ^ 3 * ∑ i ∈ s, ‖S i‖ ^ 4 * L ^ 2 := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL (hQ i hi) 2)
        (by positivity)

/-- Full prime factors may be removed using their upper amplitude bound, while the
selected factors remain in the fourth moment. -/
theorem weighted_row_holder_with_full {ι : Type*} (s : Finset ι) (S Q P : ι → ℂ)
    (L A : ℝ) (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hQ : ∀ i ∈ s, L ≤ ‖Q i‖) (hP : ∀ i ∈ s, ‖P i‖ ≤ A) :
    L ^ 2 * (∑ i ∈ s, ‖S i * P i‖) ^ 4 ≤
      A ^ 4 * (s.card : ℝ) ^ 3 * ∑ i ∈ s, ‖S i‖ ^ 4 * ‖Q i‖ ^ 2 := by
  have hsum : (∑ i ∈ s, ‖S i * P i‖) ≤ A * ∑ i ∈ s, ‖S i‖ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [norm_mul, mul_comm A]
    exact mul_le_mul_of_nonneg_left (hP i hi) (norm_nonneg _)
  calc
    _ ≤ L ^ 2 * (A * ∑ i ∈ s, ‖S i‖) ^ 4 := by
      gcongr
    _ = A ^ 4 * (L ^ 2 * (∑ i ∈ s, ‖S i‖) ^ 4) := by ring
    _ ≤ A ^ 4 * ((s.card : ℝ) ^ 3 * ∑ i ∈ s, ‖S i‖ ^ 4 * ‖Q i‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (weighted_row_holder s S Q L hL hQ) (by positivity)
    _ = _ := by ring

end Cycle25.Numerator

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Holder -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.FullWContour ; sha256 9080b01f0bb1128fc4778a011c92baeca21ee644c2dafa4ad645b41d5133541f -/
section




/-! Full-w contour transport on the retained s,z rectangle. The extension of
BufferedGrowth/BufferedIntegral below leaves the actual row kernel unchanged,
and allows every w line to the right of the original buffered line.
-/
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
open OAI OAI.SevenEighths
namespace Cycle25.Weighted.FullWContour
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem calibrated_buffered_strip_growth
    (e a B H : ℝ) (i : ℕ) (he : 0< e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤ a) (ha1 : a≤1) (hB : 2< B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e) :
    ∃C : ℝ,0≤ C ∧ ∀x w z : ℂ,a+16*e≤ x.re → x.re≤2 → |x.im|≤ H → 1-a-6*e≤ w.re → (17/50:ℝ)≤ z.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS T hT η u x w z‖≤ C*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_first_growth S hS hmax u hu
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  obtain ⟨Cr,hCr,hreciprocal⟩ := buffered_rectangle_reciprocal_bound e 1 he he' (by norm_num)
  let R : ℝ := Cr*(HeckeReciprocalGrowth.presentationComplexity ((targetRow η u).excludePrimes S hS.prime) H)^(1:ℝ)
  have hR : 0≤ R := by
    dsimp [R,HeckeReciprocalGrowth.presentationComplexity,HeckeLogarithmic.complexity]
    positivity
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=> selectedFirstBound P.val.val.absNorm 2
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0≤ L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  have hA (P : T) : 0≤ A P := selectedFirstBound_nonneg _ _ (by positivity)
  have hprod : 0≤∏P:T,A P := Finset.prod_nonneg (fun P _=> hA P)
  refine ⟨L*R*Cn*(Ch*N)*(∏P:T,A P),by dsimp [N];positivity,?_⟩
  intro x w z hxl hxr hxi hw hz
  have hwlow : -(1/100:ℝ)≤ w.re := by linarith
  have hn' := hn w hwlow
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤ Ch*N := by
    simpa only [Real.rpow_one] using hh (4*e) S hS hfirst T η u x w z (by linarith) hwlow hz
      (by linarith)
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤ L :=
    HeckeStripActual.LFunction_norm_le _ (by norm_num) (by simp only [Complex.mul_re];norm_num;linarith)
  have hrec : ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖≤ R :=
    hreciprocal (sourceDetectorFamily S hS.prime η u ψ) B a H i hB ha ha1 hH hbin
      (Sum.inl false) x hxl hxr hxi
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤∏P:T,A P := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _=> norm_nonneg _)
    intro P hP
    exact continuedCompensatedLocal_first_bound η u P.val _
      (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) 2 x w z
      (by linarith) hxr hwlow hz (by linarith)
  have heq : star ((calibrationForSet S hmax).residueMonoid u.val)*physicalCompensatedRow S hS T hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T.attach,continuedCompensatedLocal η u P.val
        (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w)) := by
    unfold physicalCompensatedRow continuedCompensatedRow
    ring
  rw [heq,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (L*R)*(Cn*(3+|w.im|)^2)*(Ch*N)*(∏P:T,A P) := by
      apply mul_le_mul _ hg (norm_nonneg _) (by dsimp [N];positivity)
      apply mul_le_mul _ hh' (norm_nonneg _) (by positivity)
      apply mul_le_mul _ hn' (norm_nonneg _) (mul_nonneg hL hR)
      rw [norm_mul]
      exact mul_le_mul hl hrec (norm_nonneg _) hL
    _ = _ := by ring


lemma rowAmplitude_buffered_strip_bound {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0< e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤ a) (haTop : a≤1) (hB : 2< B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e)
    (σ υ r : ℝ) (hσ : a+16*e≤σ) (hσ2 : σ≤2) (hr : (17/50:ℝ)≤ r) (hυ : 1-a-6*e≤υ) :
    ∃C : ℝ,0≤ C ∧ ∀t : HeightSpace, |t.1.1|≤ H →
      ‖rowAmplitudeOnLines S hS hmax P hPS η u σ υ r t‖≤ C*(3+|t.2|)^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_buffered_strip_growth e a B H i he he' ha haTop hB hH S hS hfirst hmax _
    (contourTupleOutside S P hPS) η u hu ψ hbin
  let A : ℝ := (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val))^(r-1))*(elementNorm u.val)^(-r)
  have hA : 0≤ A := by
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun i _=> Real.rpow_nonneg (by unfold elementNorm; positivity) _)
    · exact Real.rpow_nonneg (by unfold elementNorm; positivity) _
  refine ⟨A*C,mul_nonneg hA hC,?_⟩
  intro t ht
  have hn (i : Fin K) : ‖(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(((r:ℂ)+t.1.2*I)-1)‖=
      (elementNorm (CompletedGauss.primaryGenerator (P i).val))^(r-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _
      (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero)]
    simp
  have hf : ‖frequencyWeight ((r:ℂ)+t.1.2*I) ⟨u.val,u.property.1⟩‖=(elementNorm u.val)^(-r) := by
    unfold frequencyWeight
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _ u.property.1)]
    simp
  have hh := hbound ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
    (by simpa using hσ) (by simpa using hσ2) (by simpa using ht) (by simpa using hυ) (by simpa using hr)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hh
  unfold rowAmplitudeOnLines
  rw [norm_mul,norm_mul,norm_prod]
  simp_rw [hn,hf]
  exact (mul_le_mul_of_nonneg_left hh hA).trans_eq (by ring)

theorem continued_kernel_strip_integrable {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0< e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤ a) (haTop : a≤1) (hB : 2< B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (σ υ r : ℝ) (hσ : a+16*e≤σ) (hσ2 : σ≤2) (hr : (17/50:ℝ)≤ r) (hυ : 1-a-6*e≤υ) :
    IntegrableOn (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r)
      {t : HeightSpace | |t.1.1|≤ H} heightMeasure := by
  let E : Set HeightSpace := {t | |t.1.1|≤ H}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  let A := E.indicator (rowAmplitudeOnLines S hS hmax P hPS η u σ υ r)
  have hA : Measurable A := (rowAmplitudeOnLines_measurable S hS hmax P hPS η u σ υ r).indicator hE
  obtain ⟨C,hC,hbound⟩ := rowAmplitude_buffered_strip_bound e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu ψ hbin σ υ r hσ hσ2 hr hυ
  have hb (t : HeightSpace) : ‖A t‖≤ C*(3+|t.2|)^2 := by
    by_cases ht : t∈E
    · simpa only [A,Set.indicator_of_mem ht] using hbound t ht
    · simp only [A,Set.indicator_of_notMem ht,norm_zero]
      positivity
  obtain ⟨D,hD,hprofile⟩ := source_profile_integral_bound W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    σ σ r r υ υ (by linarith)
  have htwo (t : HeightSpace) : ‖A t‖≤ C*(3+|t.1.1|)^2*(3+|t.2|)^2 := by
    apply (hb t).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hh : 1≤(3+|t.1.1|)^2 := by nlinarith [abs_nonneg t.1.1]
    exact le_mul_of_one_le_right hC hh
  have hi := (hprofile σ ⟨le_rfl,le_rfl⟩ r ⟨le_rfl,le_rfl⟩ υ ⟨le_rfl,le_rfl⟩
    X Y Z hX hY hZ C hC (fun t=>‖A t‖) hA.norm.aestronglyMeasurable (fun _=> norm_nonneg _) htwo).1
  have hs := sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ σ r υ (by linarith)
  let F := fun t : HeightSpace => sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+t.1.1*I)
      ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*A t
  have hm : AEStronglyMeasurable F heightMeasure := hs.aestronglyMeasurable.mul hA.aestronglyMeasurable
  have hf : Integrable F heightMeasure := hi.mono' hm (Filter.Eventually.of_forall fun t=> by dsimp [F];rw [norm_mul])
  have heq : E.indicator (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r)=F := by
    funext t
    by_cases ht : t∈E
    · simp only [Set.indicator_of_mem ht,F,A,continuedRowOnLines_eq_amplitude]
    · simp only [Set.indicator_of_notMem ht,F,A,mul_zero]
  exact (integrable_indicator_iff hE).mp (heq ▸ hf)


/-- The complete w integral may be moved right on a detector-controlled s line. -/
theorem buffered_w_integral_eq {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0< e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤ a) (haTop : a≤1) (hB : 2< B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0< a1)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hY : 0< Y) (x z : ℂ)
    (hσ : a+16*e≤ x.re) (hσ2 : x.re≤2) (hxi : |x.im|≤ H)
    (hz : (17/50:ℝ)≤ z.re) (l r : ℝ) (hl : 1-a-6*e≤ l) (hlr : l≤ r) :
    (∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((l:ℂ)+t*I) z)=
      ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((r:ℂ)+t*I) z := by
  obtain ⟨C,hC,hbound⟩ := calibrated_buffered_strip_growth e a B H i he he' ha haTop hB hH
    S hS hfirst hmax _ (contourTupleOutside S P hPS) η u hu ψ hbin
  have hf : FirstTail ((8*e)/2) S := by convert hfirst using 1 <;> ring
  apply nonprincipal_w_integral_eq_of_polynomial (8*e) (by positivity) S hS hf hmax P hPS η u hu
    W0 W1 a1 b1 ha1 hW1 X Y Z hY x z l r (9*C) 2 (by positivity) hlr
    (by linarith) (by linarith) hz (by linarith)
  intro v hv t
  have hb := hbound x ((v:ℂ)+t*I) z hσ hσ2 hxi (by simpa using hl.trans hv.1) hz
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hb
  apply hb.trans
  have ht : (3+|t|)^2≤9*(height t)^2 := by
    unfold height
    nlinarith [abs_nonneg t]
  nlinarith

def szRectangle (T : ℝ) : Set (ℝ×ℝ) := {q | |q.1|≤ T ∧ |q.2|≤ T}
def fullWSlab (T : ℝ) : Set HeightSpace := szRectangle T ×ˢ Set.univ

lemma szRectangle_measurable (T : ℝ) : MeasurableSet (szRectangle T) := by
  unfold szRectangle
  measurability
lemma fullWSlab_measurable (T : ℝ) : MeasurableSet (fullWSlab T) :=
  (szRectangle_measurable T).prod MeasurableSet.univ

/-- Fubini is applied with the whole w axis, never a truncated w interval. -/
theorem fullWSlab_fubini (T : ℝ) (f : HeightSpace→ℂ)
    (hf : IntegrableOn f (fullWSlab T) heightMeasure) :
    (∫p in fullWSlab T,f p ∂heightMeasure)=
      ∫q in szRectangle T,(∫w : ℝ,f (q,w)) ∂(volume.prod volume) := by
  simpa only [fullWSlab, Measure.restrict_univ] using setIntegral_prod f hf

def centralFullWIntegral {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H υ : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3 * ∫p in fullWSlab H,
    continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) υ (17/50) p ∂heightMeasure

/-- Exact equality of the full-w slab integrals, prior to amplitude partition. -/
theorem centralFullWIntegral_transport {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0< e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤ a) (haTop : a≤1) (hB : 2< B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (l r : ℝ) (hl : 1-a-6*e≤ l) (hlr : l≤ r) :
    centralFullWIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H l =
      centralFullWIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H r := by
  have hi (v : ℝ) (hv : 1-a-6*e≤ v) :
      IntegrableOn (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) v (17/50))
        (fullWSlab H) heightMeasure :=
    (continued_kernel_strip_integrable e a B H i he he' ha haTop hB hH S hS hmax hfirst P hPS η u hu ψ hbin
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ (a+16*e) v (17/50)
      le_rfl (by linarith) le_rfl hv).mono_set (fun _ ht=> ht.1.1)
  unfold centralFullWIntegral
  rw [fullWSlab_fubini _ _ (hi l hl), fullWSlab_fubini _ _ (hi r (hl.trans hlr))]
  congr 1
  apply setIntegral_congr_fun (szRectangle_measurable H)
  intro q hq
  simpa only [continuedRowOnLines,Complex.ofReal_div,Complex.ofReal_ofNat] using
    buffered_w_integral_eq e a B H i he he' ha haTop hB hH S hS hmax hfirst P hPS η u hu ψ hbin
    W0 W1 a1 b1 ha1 hW1 X Y Z hY (((a+16*e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I)
    (by simp) (by simp;linarith) (by simpa using hq.1) (by simp) l r hl hlr

end Cycle25.Weighted.FullWContour
end

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.FullWContour -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.MellinReconstruction ; sha256 b7d0faf376435484e06de73d22cdd38501e5cbf5e9b24cc1bcf9893770e58386 -/
section






/-! Mellin reconstruction for the actual nonprincipal numerator L-function.
The coefficient index will be arbitrary countable, with positive real scales. -/
noncomputable section
open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
open OAI OAI.SevenEighths
namespace Cycle25.Weighted.MellinReconstruction
open HeckeFamily ProbeHighRowFamily ProbeMellinBoundary

def plainIntegrand (χ : Character) (W : ℝ→ℂ) (D : ℝ) (s : ℂ) : ℂ :=
  mellin W s * (D:ℂ)^(s-(1/2:ℂ)) * LFunction χ s

lemma plainIntegrand_eq (χ : Character) (W : ℝ→ℂ) (D : ℝ) (s : ℂ) :
    plainIntegrand χ W D s = HeckeDyadic.integrand χ false W D 0 0 s := by
  simp [plainIntegrand,HeckeDyadic.integrand,HeckeDyadic.shift,HeckeDyadic.series]

lemma plainIntegrand_differentiableAt (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a) (hsupp : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (D : ℝ) (hD : 0< D) (s : ℂ) :
    DifferentiableAt ℂ (plainIntegrand χ W D) s := by
  have heq : plainIntegrand χ W D = HeckeDyadic.integrand χ false W D 0 0 :=
    funext (plainIntegrand_eq χ W D)
  rw [heq]
  exact HeckeDyadic.integrand_differentiableAt χ false W a b ha hsupp hW D 0 0 hD
    (HeckeDyadic.series_differentiableAt_nonprincipal χ hχ false (by intro hh; cases hh))

/-- A common integrable envelope for the Mellin transform times L on the full strip. -/
theorem mellin_L_cauchy (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a) (hsupp : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) :
    ∃C : ℝ,0≤ C ∧ ∀v∈Icc (1/2:ℝ) 2,∀t : ℝ,
      ‖mellin W ((v:ℂ)+t*I)*LFunction χ ((v:ℂ)+t*I)‖≤ C*cauchy t := by
  obtain ⟨A,hA,hgrowth⟩ := nonprincipal_positive_growth (1/2) 1 (by norm_num) (by norm_num)
  obtain ⟨D,hD,hdecay⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W a b ha hsupp hW (1/2) 2 4
  let B := A*(χ.modulus.absNorm:ℝ)^(3/5+1:ℝ)
  have hB : 0≤ B := by dsimp [B];positivity
  refine ⟨9*B*D,by positivity,?_⟩
  intro v hv t
  have hg := hgrowth χ hχ ((v:ℂ)+t*I) (by simpa using hv.1)
  simp only [HeckeOrigin.continued,ite_eq_right hχ,add_im,ofReal_im,mul_im,
    ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hg
  change ‖LFunction χ ((v:ℂ)+t*I)‖≤ B*(3+|t|)^2 at hg
  have hpow : (3+|t|)^2≤9*(height t)^2 := by
    unfold height
    nlinarith [abs_nonneg t]
  have hg' : ‖LFunction χ ((v:ℂ)+t*I)‖≤9*B*(height t)^2 :=
    hg.trans ((mul_le_mul_of_nonneg_left hpow hB).trans_eq (by ring))
  have hm : (height t)^4*‖mellin W ((v:ℂ)+t*I)‖≤ D := by
    simpa only [height] using hdecay v hv t
  apply CubicReflectionKernel.weighted_two_to_cauchy (norm_nonneg _) t
  rw [norm_mul]
  calc
    _ ≤ (height t)^2*(‖mellin W ((v:ℂ)+t*I)‖*(9*B*(height t)^2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg' (norm_nonneg _)) (sq_nonneg _)
    _ = 9*B*((height t)^4*‖mellin W ((v:ℂ)+t*I)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)

theorem plainIntegrand_cauchy (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a) (hsupp : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (D : ℝ) (hD : 0< D) :
    ∃C : ℝ,0≤ C ∧ ∀v∈Icc (1/2:ℝ) 2,∀t : ℝ,
      ‖plainIntegrand χ W D ((v:ℂ)+t*I)‖≤ C*cauchy t := by
  obtain ⟨C,hC,hbound⟩ := mellin_L_cauchy χ hχ W a b ha hsupp hW
  refine ⟨scaleBound D 0 (3/2)*C,mul_nonneg (scaleBound_pos _ _ _).le hC,?_⟩
  intro v hv t
  have hd := cpow_le_scaleBound hD (((v:ℂ)+t*I)-(1/2:ℂ))
    (show (((v:ℂ)+t*I)-(1/2:ℂ)).re∈Icc 0 (3/2) by simp;constructor <;> linarith [hv.1,hv.2])
  have heq : plainIntegrand χ W D ((v:ℂ)+t*I)=
      (D:ℂ)^(((v:ℂ)+t*I)-(1/2:ℂ))*(mellin W ((v:ℂ)+t*I)*LFunction χ ((v:ℂ)+t*I)) := by
    unfold plainIntegrand;ring
  rw [heq,norm_mul]
  exact (mul_le_mul hd (hbound v hv t) (norm_nonneg _) (scaleBound_pos _ _ _).le).trans_eq (by ring)

theorem plainIntegrand_vertical_integrable (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a) (hsupp : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (D : ℝ) (hD : 0< D) (v : ℝ) (hv : v∈Icc (1/2:ℝ) 2) :
    Integrable (fun t : ℝ=> plainIntegrand χ W D ((v:ℂ)+t*I)) := by
  obtain ⟨C,hC,hbound⟩ := plainIntegrand_cauchy χ hχ W a b ha hsupp hW D hD
  have hc : Continuous (fun t : ℝ=> plainIntegrand χ W D ((v:ℂ)+t*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (plainIntegrand_differentiableAt χ hχ W a b ha hsupp hW D hD _).continuousAt.comp (by fun_prop)
  exact (cauchy_integrable.const_mul C).mono' hc.aestronglyMeasurable (ae_of_all _ (hbound v hv))

/-- Exact inversion on Re(w)=1/2 for the original dyadic polynomial. -/
theorem polynomial_central_mellin (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a) (hsupp : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (D : ℝ) (hD : 0< D) :
    HeckeDyadic.polynomial χ false W D 0 0 = (1/(2*Real.pi):ℂ)*
      ∫t : ℝ,plainIntegrand χ W D ((1/2:ℂ)+t*I) := by
  obtain ⟨C,hC,hbound⟩ := plainIntegrand_cauchy χ hχ W a b ha hsupp hW D hD
  have heq := Continuation.vertical_integral_eq_of_even_envelope
    (plainIntegrand χ W D) cauchy cauchy_integrable (by intro t;simp [cauchy])
    cauchy_tendsto (by norm_num : (1/2:ℝ)≤2)
    (fun s _=>(plainIntegrand_differentiableAt χ hχ W a b ha hsupp hW D hD s).differentiableWithinAt) hbound
  rw [HeckeDyadic.polynomial_mellin χ false W a b ha hsupp hW D 2 0 0 hD (by norm_num)]
  simp only [HeckeDyadic.shift,ofReal_zero,zero_mul,sub_zero,add_zero,HeckeDyadic.series,Bool.false_eq_true,ite_false,Complex.ofReal_ofNat]
  change (1/(2*Real.pi):ℂ)*(∫t : ℝ,plainIntegrand χ W D ((2:ℂ)+t*I))=_
  simpa only [Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_one] using congrArg (fun z=>(1/(2*Real.pi):ℂ)*z) heq.symm

lemma coefficient_line_norm (A : ℂ) (N c t : ℝ) (hN : 0< N) :
    ‖A*(N:ℂ)^(-((c:ℂ)+t*I))‖=‖A‖*N^(-c) := by
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hN]
  simp

/-- Absolute mass also proves genuine integrability of the whole coefficient
series, which is needed before separating finite error subsets. -/
theorem coefficient_series_integrable {κ : Type*}
    (A : κ→ℂ) (N : κ→ℝ) (hN : ∀i,0< N i) (c : ℝ)
    (hmass : Summable (fun i=>‖A i‖*(N i)^(-c)))
    (g : ℝ→ℂ) (hg : Integrable g) :
    Integrable (fun t : ℝ=> g t*(∑'i,A i*(N i:ℂ)^(-((c:ℂ)+t*I)))) := by
  have hc (i : κ) : Continuous (fun t : ℝ=> A i*(N i:ℂ)^(-((c:ℂ)+t*I))) := by
    exact continuous_const.mul ((show Continuous (fun t : ℝ=>-((c:ℂ)+t*I)) by fun_prop).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr (hN i).ne')))
  have hs := continuous_tsum hc hmass (fun i t=>(coefficient_line_norm (A i) (N i) c t (hN i)).le)
  apply hg.mul_bdd hs.aestronglyMeasurable
  apply ae_of_all
  intro t
  have hn : Summable (fun i=>‖A i*(N i:ℂ)^(-((c:ℂ)+t*I))‖) := by
    simpa only [coefficient_line_norm _ _ _ _ (hN _)] using hmass
  simpa only [coefficient_line_norm _ _ _ _ (hN _)] using norm_tsum_le_tsum_norm hn

/-- Countable coefficient interchange uses absolute mass on the exact w line. -/
theorem coefficient_integral_interchange {κ : Type*} [Countable κ]
    (A : κ→ℂ) (N : κ→ℝ) (hN : ∀i,0< N i) (c : ℝ)
    (hmass : Summable (fun i=>‖A i‖*(N i)^(-c)))
    (g : ℝ→ℂ) (hg : Integrable g) :
    (∫t : ℝ,g t*(∑'i,A i*(N i:ℂ)^(-((c:ℂ)+t*I))))=
      ∑'i,∫t : ℝ,g t*(A i*(N i:ℂ)^(-((c:ℂ)+t*I))) := by
  let F := fun i t=> g t*(A i*(N i:ℂ)^(-((c:ℂ)+t*I)))
  have hi (i : κ) : Integrable (F i) := by
    have hc : Continuous (fun t : ℝ=> A i*(N i:ℂ)^(-((c:ℂ)+t*I))) := by
      exact continuous_const.mul ((show Continuous (fun t : ℝ=>-((c:ℂ)+t*I)) by fun_prop).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr (hN i).ne')))
    exact hg.mul_bdd hc.aestronglyMeasurable
      (ae_of_all _ (fun t=>(coefficient_line_norm (A i) (N i) c t (hN i)).le))
  have hint (i : κ) : (∫t : ℝ,‖F i t‖)=(∫t : ℝ,‖g t‖)*(‖A i‖*(N i)^(-c)) := by
    simp only [F,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hN i)]
    simp only [neg_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_self,add_zero]
    rw [←integral_mul_const]
  have hs : Summable (fun i=>∫t : ℝ,‖F i t‖) := by
    simp_rw [hint]
    exact hmass.mul_left _
  simp_rw [←tsum_mul_left]
  exact (integral_tsum_of_summable_integral_norm hi hs).symm

lemma reconstruction_scale (Y N : ℝ) (hY : 0< Y) (hN : 0< N) (w : ℂ) :
    (Y:ℂ)^(w-1)*(N:ℂ)^(-w)=
      (Y:ℂ)^(-(1/2:ℂ))*(N:ℂ)^(-(1/2:ℂ))*((Y/N:ℝ):ℂ)^(w-(1/2:ℂ)) := by
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg hY.le hN.le]
  simp only [div_eq_mul_inv]
  rw [←Complex.cpow_neg]
  symm
  calc
    _ = ((Y:ℂ)^(-(1/2:ℂ))*(Y:ℂ)^(w-(1/2:ℂ)))*
        ((N:ℂ)^(-(1/2:ℂ))*(N:ℂ)^(-(w-(1/2:ℂ)))) := by ring
    _ = _ := by
      rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hY.ne'),
        ←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hN.ne')]
      congr 2 <;> ring

lemma coefficient_kernel_identity (χ : Character) (W : ℝ→ℂ) (A : ℂ)
    (Y N : ℝ) (hY : 0< Y) (hN : 0< N) (w : ℂ) :
    (Y:ℂ)^(w-1)*mellin W w*LFunction χ w*(A*(N:ℂ)^(-w))=
      ((Y:ℂ)^(-(1/2:ℂ))*(A*(N:ℂ)^(-(1/2:ℂ))))*plainIntegrand χ W (Y/N) w := by
  have hs := reconstruction_scale Y N hY hN w
  unfold plainIntegrand
  calc
    _ = ((Y:ℂ)^(w-1)*(N:ℂ)^(-w))*(A*mellin W w*LFunction χ w) := by ring
    _ = _ := by rw [hs];ring

/-- Reconstruction of one coefficient at its physical scale Y/N. -/
theorem coefficient_central_mellin (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a) (hsupp : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (A : ℂ) (Y N : ℝ) (hY : 0< Y) (hN : 0< N) :
    (1/(2*Real.pi):ℂ)*(∫t : ℝ,
      (Y:ℂ)^(((1/2:ℂ)+t*I)-1)*mellin W ((1/2:ℂ)+t*I)*LFunction χ ((1/2:ℂ)+t*I)*
        (A*(N:ℂ)^(-((1/2:ℂ)+t*I))))=
      (Y:ℂ)^(-(1/2:ℂ))*(A*(N:ℂ)^(-(1/2:ℂ)))*HeckeDyadic.polynomial χ false W (Y/N) 0 0 := by
  simp_rw [coefficient_kernel_identity χ W A Y N hY hN]
  rw [integral_const_mul,polynomial_central_mellin χ hχ W a b ha hsupp hW (Y/N) (div_pos hY hN)]
  ring

lemma reconstruction_kernel_integrable (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a) (hsupp : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (Y : ℝ) (hY : 0< Y) :
    Integrable (fun t : ℝ=>(Y:ℂ)^(((1/2:ℂ)+t*I)-1)*mellin W ((1/2:ℂ)+t*I)*
      LFunction χ ((1/2:ℂ)+t*I)) := by
  have hi := (plainIntegrand_vertical_integrable χ hχ W a b ha hsupp hW Y hY (1/2) ⟨le_rfl,by norm_num⟩).const_mul
    ((Y:ℂ)^(-(1/2:ℂ)))
  apply hi.congr
  apply ae_of_all
  intro t
  simp only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  unfold plainIntegrand
  have hpow : (Y:ℂ)^(-(1/2:ℂ))*(Y:ℂ)^(((1/2:ℂ)+t*I)-(1/2:ℂ))=
      (Y:ℂ)^(((1/2:ℂ)+t*I)-1) := by
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hY.ne')]
    congr 1
    ring
  calc
    _ = ((Y:ℂ)^(-(1/2:ℂ))*(Y:ℂ)^(((1/2:ℂ)+t*I)-(1/2:ℂ)))*
        mellin W ((1/2:ℂ)+t*I)*LFunction χ ((1/2:ℂ)+t*I) := by ring
    _ = _ := by rw [hpow]

/-- Actual L-function reconstruction with any countable coefficient index. -/
theorem weighted_numerator_mellin {κ : Type*} [Countable κ]
    (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a) (hsupp : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (Y : ℝ) (hY : 0< Y)
    (A : κ→ℂ) (N : κ→ℝ) (hN : ∀i,0< N i)
    (hmass : Summable (fun i=>‖A i‖*(N i)^(-(1/2:ℝ)))) :
    (1/(2*Real.pi):ℂ)*(∫t : ℝ,
      (Y:ℂ)^(((1/2:ℂ)+t*I)-1)*mellin W ((1/2:ℂ)+t*I)*HeckeOrigin.continued χ ((1/2:ℂ)+t*I)*
        (∑'i,A i*(N i:ℂ)^(-((1/2:ℂ)+t*I))))=
      (Y:ℂ)^(-(1/2:ℂ))*∑'i,A i*(N i:ℂ)^(-(1/2:ℂ))*HeckeDyadic.polynomial χ false W (Y/N i) 0 0 := by
  simp only [HeckeOrigin.continued,ite_eq_right hχ]
  have hint := coefficient_integral_interchange A N hN (1/2) hmass _
    (reconstruction_kernel_integrable χ hχ W a b ha hsupp hW Y hY)
  simp only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] at hint
  rw [hint,←tsum_mul_left,←tsum_mul_left]
  apply tsum_congr
  intro i
  simpa only [mul_assoc] using coefficient_central_mellin χ hχ W a b ha hsupp hW (A i) Y (N i) hY (hN i)


/-- Absolute summability survives the actual Mellin reconstruction.  The common
integrable Mellin--L envelope bounds every coefficient before inversion. -/
theorem reconstructed_series_norm_summable {κ : Type*}
    (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a) (hsupp : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (Y : ℝ) (hY : 0< Y)
    (A : κ→ℂ) (N : κ→ℝ) (hN : ∀i,0< N i)
    (hmass : Summable (fun i=>‖A i‖*(N i)^(-(1/2:ℝ)))) :
    Summable (fun i=>‖A i*(N i:ℂ)^(-(1/2:ℂ))*HeckeDyadic.polynomial χ false W (Y/N i) 0 0‖) := by
  let g (t : ℝ) := (Y:ℂ)^(((1/2:ℂ)+t*I)-1)*mellin W ((1/2:ℂ)+t*I)*
    LFunction χ ((1/2:ℂ)+t*I)
  let F (i : κ) (t : ℝ) := g t*(A i*(N i:ℂ)^(-((1/2:ℂ)+t*I)))
  have hint (i : κ) : (∫t : ℝ,‖F i t‖)=(∫t : ℝ,‖g t‖)*(‖A i‖*(N i)^(-(1/2:ℝ))) := by
    have hr (t : ℝ) : (-((1/2:ℂ)+t*I)).re=-(1/2:ℝ) := by simp
    simp only [F,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hN i),hr]
    rw [integral_mul_const]
  have hs : Summable (fun i=>∫t : ℝ,‖F i t‖) := by
    simp_rw [hint]
    exact hmass.mul_left _
  have hi : Summable (fun i=>‖∫t : ℝ,F i t‖) :=
    hs.of_nonneg_of_le (fun _=> norm_nonneg _) (fun _=> norm_integral_le_integral_norm _)
  have hn := hi.mul_left ‖(1/(2*Real.pi):ℂ)‖
  have hid (i : κ) : (1/(2*Real.pi):ℂ)*(∫t : ℝ,F i t)=
      (Y:ℂ)^(-(1/2:ℂ))*(A i*(N i:ℂ)^(-(1/2:ℂ)))*HeckeDyadic.polynomial χ false W (Y/N i) 0 0 :=
    coefficient_central_mellin χ hχ W a b ha hsupp hW (A i) Y (N i) hY (hN i)
  simp_rw [←norm_mul,hid,mul_assoc,norm_mul] at hn
  have hy : ‖(Y:ℂ)^(-(1/2:ℂ))‖≠0 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
    exact (Real.rpow_pos_of_pos hY _).ne'
  apply (summable_mul_left_iff hy).mp
  simpa only [norm_mul,mul_assoc] using hn

/-- Compact support cuts off the actual numerator before reflection. -/
theorem polynomial_zero_of_scale_cutoff (χ : Character) (W : ℝ→ℂ)
    (a b Y N : ℝ) (hsupp : Function.support W⊆Icc a b)
    (hY : 0< Y) (hN : 0< N) (hcut : b*Y< N) :
    HeckeDyadic.polynomial χ false W (Y/N) 0 0=0 := by
  unfold HeckeDyadic.polynomial
  suffices hh : (∑'J : HeckeDyadic.NonzeroIdeal,HeckeDyadic.summand χ false W (Y/N) 0 0 J)=0 by
    rw [hh,mul_zero]
  suffices hzero : ∀J : HeckeDyadic.NonzeroIdeal,HeckeDyadic.summand χ false W (Y/N) 0 0 J=0 by
    simp only [hzero,tsum_zero]
  intro J
  have hJ : 1≤ HeckeDyadic.norm J := by
    have hj := HeckeDyadic.norm_pos J
    unfold HeckeDyadic.norm at *
    exact_mod_cast (Nat.succ_le_iff.mpr (by exact_mod_cast hj) : 1≤ J.val.absNorm)
  have harg : b< HeckeDyadic.norm J/(Y/N) := by
    rw [div_div_eq_mul_div]
    apply (lt_div_iff₀ hY).mpr
    exact hcut.trans_le (le_mul_of_one_le_left hN.le hJ)
  have hz : W (HeckeDyadic.norm J/(Y/N))=0 := by
    by_contra hn
    exact (not_le_of_gt harg) (hsupp hn).2
  simp [HeckeDyadic.summand,hz]

/-- The countable reconstructed sum has no contribution at N>bY. -/
theorem reconstruction_exact_cutoff {κ : Type*} [Countable κ]
    (χ : Character) (W : ℝ→ℂ) (a b Y : ℝ) (hsupp : Function.support W⊆Icc a b)
    (hY : 0< Y) (A : κ→ℂ) (N : κ→ℝ) (hN : ∀i,0< N i) :
    (∑'i,A i*(N i:ℂ)^(-(1/2:ℂ))*HeckeDyadic.polynomial χ false W (Y/N i) 0 0)=
      ∑'i,if N i≤ b*Y then
        A i*(N i:ℂ)^(-(1/2:ℂ))*HeckeDyadic.polynomial χ false W (Y/N i) 0 0 else 0 := by
  apply tsum_congr
  intro i
  split_ifs with hi
  · rfl
  · rw [polynomial_zero_of_scale_cutoff χ W a b Y (N i) hsupp hY (hN i) (lt_of_not_ge hi),mul_zero]

end Cycle25.Weighted.MellinReconstruction
end

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.MellinReconstruction -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorLocalCoefficients ; sha256 e3bfb0b967d5c587dcdf520952fe04446b512da94aaeaa3b91e5c23ded8b16cc -/
section





/-! Exact finite coefficient expansions of the original local numerator factors.

The local variable is `T = Q^(-w)`.  All coefficients below are independent of `T`.
We use finite lists of terms, so no cancellation is lost by replacing a polynomial by
its values on a vertical line.  These lemmas refer directly to the original continued
correction and compensated replacement.
-/

noncomputable section
open scoped BigOperators
namespace Cycle25.Weighted.Numerator
open OAI.SevenEighths ProbeLocal ProbeEuler

def affine (a b T : ℂ) : ℂ := a + b * T
def quadratic (a b c T : ℂ) : ℂ := a + b * T + c * T ^ 2
def cubic (a b c d T : ℂ) : ℂ := a + b * T + c * T ^ 2 + d * T ^ 3

/-- The two coefficients of the marked defect after the original unramified
cancellation. -/
def markedDefectConstant (R V qInv D : ℂ) : ℂ :=
  (R * (1 - qInv) / (1 - V) - D * R) / (1 - R)
def markedDefectLinear (R V chi K : ℂ) : ℂ :=
  (chi * R - K * V / (1 - V)) / (1 - R)

theorem marked_defect_affine (R V qInv D chi K T : ℂ)
    (hR : 1 - R ≠ 0) (hV : 1 - V ≠ 0) :
    markedFactor R V qInv (K * T) (-D + chi * T * R) 1 + D =
      affine (markedDefectConstant R V qInv D) (markedDefectLinear R V chi K) T := by
  unfold markedFactor affine markedDefectConstant markedDefectLinear
  simp only [pow_one]
  field_simp
  ring

def correctionDefectConstant (V D E₀ : ℂ) : ℂ :=
  (D * V + (1 - V) * E₀) / (1 - D)
def correctionDefectLinear (V D chi E₀ E₁ : ℂ) : ℂ :=
  (D * chi * (1 - V) - V * chi + (1 - V) * (E₁ - chi * E₀)) / (1 - D)
def correctionDefectQuadratic (V D chi E₁ : ℂ) : ℂ :=
  (-(1 - V) * chi * E₁) / (1 - D)

theorem correction_defect_quadratic (V D chi E₀ E₁ T : ℂ) (hD : 1 - D ≠ 0) :
    continuedCorrection V (chi * T) D (affine E₀ E₁ T - D) - 1 =
      quadratic (correctionDefectConstant V D E₀)
        (correctionDefectLinear V D chi E₀ E₁)
        (correctionDefectQuadratic V D chi E₁) T := by
  unfold continuedCorrection affine quadratic correctionDefectConstant
    correctionDefectLinear correctionDefectQuadratic
  field_simp
  ring

/-- Coefficients of the error bracket after the exact normalized cancellation. -/
def errorBracketConstant (V D B nu E₀ : ℂ) : ℂ :=
  nu * (V / (1 - V) - D) + (B + nu) * E₀
def errorBracketLinear (V D B nu E₀ E₁ : ℂ) : ℂ :=
  -(V / (1 - V) - D) + (B + nu) * E₁ - E₀
def errorBracketQuadratic (E₁ : ℂ) : ℂ := -E₁

theorem compensated_error_cubic (V D chi B nu E₀ E₁ T : ℂ)
    (hV : 1 - V ≠ 0) (hD : 1 - D ≠ 0)
    (hBD : B * D = nu) (hchi : nu * chi = 1) :
    compensatedReplacement V (chi * T) D (affine E₀ E₁ T - D) B T +
      continuedCorrection V (chi * T) D (affine E₀ E₁ T - D) * nu =
    let c := (1 - V) / (1 - D)
    let a := errorBracketConstant V D B nu E₀
    let b := errorBracketLinear V D B nu E₀ E₁
    let d := errorBracketQuadratic E₁
    cubic (c * a) (c * (b - chi * a)) (c * (d - chi * b))
      (-c * chi * d) T := by
  have hvW : nu * (chi * T) = T := by rw [← mul_assoc, hchi, one_mul]
  rw [continued_normalized_cancellation _ _ _ _ _ _ _ hV hD hBD hvW]
  dsimp only
  unfold affine cubic errorBracketConstant errorBracketLinear errorBracketQuadratic
  ring

/-- The ramified replacement is quadratic, including its strict term. -/
theorem ramified_error_quadratic (V B A C T : ℂ) :
    compensatedReplacement V 0 0 (affine A C T) B T =
      quadratic (B * (1 - V) * A)
        (B * (1 - V) * C - 1 - (1 - V) * A)
        (-(1 - V) * C) T := by
  simp only [compensatedReplacement, affine, quadratic, mul_zero, sub_zero,
    mul_one, div_one]
  ring

theorem norm_affine_le (a b T : ℂ) :
    ‖affine a b T‖ ≤ ‖a‖ + ‖b‖ * ‖T‖ := by
  simpa only [affine, norm_mul] using norm_add_le a (b * T)

theorem norm_quadratic_le (a b c T : ℂ) :
    ‖quadratic a b c T‖ ≤ ‖a‖ + ‖b‖ * ‖T‖ + ‖c‖ * ‖T‖ ^ 2 := by
  calc
    _ ≤ ‖a + b * T‖ + ‖c * T ^ 2‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [norm_mul, norm_pow]
      exact add_le_add (norm_affine_le a b T) le_rfl

theorem norm_cubic_le (a b c d T : ℂ) :
    ‖cubic a b c d T‖ ≤
      ‖a‖ + ‖b‖ * ‖T‖ + ‖c‖ * ‖T‖ ^ 2 + ‖d‖ * ‖T‖ ^ 3 := by
  calc
    _ ≤ ‖a + b * T + c * T ^ 2‖ + ‖d * T ^ 3‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [norm_mul, norm_pow]
      exact add_le_add (norm_quadratic_le a b c T) le_rfl

section ActualMarkedRow
open OAI.ActualEisensteinCubic OAI.CompletedGauss
open OAI.ConcretePrimeRowBridge OAI.SevenEighths.ProbePrimePower
local notation "O" => OAI.ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p})

/-- Every original marked term has exactly the declared degree in `Q^(-w)`. -/
theorem rowMarkedTerm_monomial (eta a X W V rho : ℂ) (j e l k m : ℕ) :
    rowMarkedTerm p hp hg eta a X W V rho j e l k m =
      rowMarkedTerm p hp hg eta a X 1 V rho j e l k m * W ^ k := by
  unfold rowMarkedTerm
  split_ifs
  · simp
  · unfold rowWeightedScalar weightedScalar
    simp only [one_pow, mul_one]
    ring

/-- The closed marked factor is genuinely affine in the Mellin local variable,
including ramified rows.  This derives the degree bound from the original Gauss
sum definition, rather than imposing it as a hypothesis. -/
theorem rowClosedMarked_affine (eta a X W V rho : ℂ) (j : ℕ) :
    rowClosedMarked p hp hg eta a X W V rho j =
      rowClosedMarked p hp hg eta a X 0 V rho j +
        (rowClosedMarked p hp hg eta a X 1 V rho j -
          rowClosedMarked p hp hg eta a X 0 V rho j) * W := by
  unfold rowClosedMarked rowBaseFinite
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
  norm_num only [rowMarkedTerm, Nat.reduceMul, Nat.reduceAdd, Nat.reduceEqDiff,
    if_false, rowWeightedScalar, weightedScalar, pow_zero, pow_one,
    zero_pow, one_pow, mul_one, one_mul, mul_zero, zero_mul, zero_add, add_zero]
  ring

end ActualMarkedRow
end Cycle25.Weighted.Numerator

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorLocalCoefficients -/
