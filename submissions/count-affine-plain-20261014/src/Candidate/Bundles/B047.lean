/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B046
import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/- BEGIN ORIGINAL Cycle25.Numerator.FullWBound; sha256 3ada4002305fd7ca24c61c2e426de762d6b1b5a8c6f8ea2fd48f67f58cb630ad -/
section
                                      

/-! Convert the actual w-integrated numerator estimate into a full physical cell bound. -/
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
open OAI OAI.SevenEighths
namespace Cycle25.Weighted.FullWContour
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary ProbeHighRowFamily
local notation "O" => HeckeFamily.O
set_option maxHeartbeats 400000

theorem finiteFullW_uniform_norm_bound (W0 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ)
    (ha0 : 0<a0) (hW0 : Function.support W0⊆Icc a0 b0) :
    ∃C : ℝ,0<C ∧ ∀{K : ℕ} {ι : Type*} [Fintype ι],
      ∀(e a B H : ℝ) (i : ℕ),0<e→e<1/1000→(51/100:ℝ)≤a→a≤1→2<B→H≤(3*i+2:ℕ)*B→
      ∀(S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal),
      FirstTail (4*e) S→∀(η : Character) (R : Finset FreeRow),(∀u∈R,u.val≠1)→
      ∀(T : Fin K→Finset PrimeIdeal) (hT : ∀j P,P∈T j→P.val∉S) (ψ : FreeRow→ι→Character),
      (∀u∈R,detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(i+1:ℕ)*B)<a+2*e)→
      ∀(W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ),
      0<a1→Function.support W1⊆Icc a1 b1→∀X Y Z A : ℝ,0<X→0<Y→0<Z→0≤A→
      (∀q∈szRectangle H,‖integratedDyadValue S hS hmax η R T hT W Yp W1 Y
        (((a+16*e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I)‖≤A)→
      ‖finiteCentralFullWRows S hS hmax η R T hT W Yp W0 W1 X Y Z e (fun _=>a) (fun _=>H)‖≤
        C*X^(1/2-17/50:ℝ)*Z^(a+16*e+17/50-1)*A := by
  obtain ⟨C,hC,hprofile⟩ := sourceSZ_uniform_integral_bound W0 a0 b0 ha0 hW0
    (51/100) 2 (17/50) (17/50) (by norm_num) 0
  let c : ℂ := ((1/(2*Real.pi):ℝ):ℂ)^3
  refine ⟨(‖c‖+1)*C,by positivity,?_⟩
  intro K ι _ e a B H i he he' ha haTop hB hH S hS hmax hfirst η R hR T hT ψ hbin W Yp W1
    a1 b1 ha1 hW1 X Y Z A hX hY hZ hA hbound
  let G (q : ℝ×ℝ) := integratedDyadValue S hS hmax η R T hT W Yp W1 Y
    (((a+16*e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I)
  have hh := finiteFullW_reconstruction e a B H i he he' ha haTop hB hH S hS hmax hfirst
    η R hR T hT ψ hbin W Yp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  dsimp only at hh
  have hp := hprofile (a+16*e) ⟨by linarith,by linarith⟩ (17/50) ⟨le_rfl,le_rfl⟩
    X Z hX hZ H A hA G
  simp only [ofReal_div,ofReal_ofNat,pow_zero,mul_one] at hp
  have hb := hp hh.1 hbound
  rw [hh.2,norm_mul]
  change ‖c‖*‖∫q in szRectangle H,sourceSZWeight W0 X Z (((a+16*e:ℝ):ℂ)+q.1*I)
      ((17/50:ℂ)+q.2*I)*G q ∂(volume.prod volume)‖≤_
  calc
    _ ≤ ‖c‖*(C*X^(1/2-17/50:ℝ)*Z^(a+16*e+17/50-1)*A) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ ≤ (‖c‖+1)*(C*X^(1/2-17/50:ℝ)*Z^(a+16*e+17/50-1)*A) := by
      apply mul_le_mul_of_nonneg_right (by linarith)
      positivity
    _ = _ := by ring

end Cycle25.Weighted.FullWContour
end

/- Adapted from weighted-numerator PR6, 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/

end
/- END ORIGINAL Cycle25.Numerator.FullWBound -/

/- BEGIN ORIGINAL Cycle25.Numerator.FiniteHeight; sha256 fab662a92c2267391fd519673993b289ec867d0ca6875ae1d4ba4481e7e24132 -/
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
    (degree:ι→ℕ) (C:ι→ℝ) (hC:∀i,0<C i) :
    ∃J:ℝ,0≤J ∧ ∃Ctot:ℝ,1≤Ctot ∧
      (∀i,(degree i:ℝ)≤J ∧ C i≤Ctot) ∧
      ∀H eps:ℝ,0≤H → 0≤eps →
        (∀i,C i*(3+H)^((degree i:ℝ)+2*eps)≤Ctot*(3+H)^(J+2*eps)) ∧
        (∑i,C i*(3+H)^((degree i:ℝ)+2*eps))≤Ctot*(3+H)^(J+2*eps) := by
  let J:ℝ := (∑i,degree i:ℕ)
  let Ctot:ℝ := 1+∑i,C i
  have hsum : 0≤∑i,C i := Finset.sum_nonneg (fun i _=>(hC i).le)
  have hCtot : 1≤Ctot := by dsimp [Ctot];linarith
  have hdegree (i:ι) : (degree i:ℝ)≤J := by
    dsimp only [J]
    exact_mod_cast (Finset.single_le_sum (fun j (_:j∈Finset.univ)=>Nat.zero_le (degree j))
      (Finset.mem_univ i))
  have hcoeff (i:ι) : C i≤Ctot := by
    have hi := Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(hC j).le) (Finset.mem_univ i)
    dsimp only [Ctot]
    linarith
  refine ⟨J,by dsimp [J];positivity,Ctot,hCtot,fun i=>⟨hdegree i,hcoeff i⟩,?_⟩
  intro H eps hH heps
  have hbase : 1≤3+H := by linarith
  have hpow : 0≤(3+H)^(J+2*eps) := Real.rpow_nonneg (by linarith) _
  have hterm (i:ι) : C i*(3+H)^((degree i:ℝ)+2*eps)≤C i*(3+H)^(J+2*eps) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hbase (by linarith [hdegree i])) (hC i).le
  constructor
  · intro i
    exact (hterm i).trans (mul_le_mul_of_nonneg_right (hcoeff i) hpow)
  · calc
      _ ≤ ∑i,C i*(3+H)^(J+2*eps) := Finset.sum_le_sum (fun i _=>hterm i)
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
    (hP:∀i,∃degree:ℕ,∃C:ℝ,0<C ∧ ∀ᶠx in l,P i degree C x) :
    ∃degree:ι→ℕ,∃C:ι→ℝ,∃J:ℝ,∃Ctot:ℝ,
      0≤J ∧ 1≤Ctot ∧ (∀i,0<C i) ∧
      (∀i,(degree i:ℝ)≤J ∧ C i≤Ctot) ∧
      (∀H eps:ℝ,0≤H → 0≤eps →
        (∀i,C i*(3+H)^((degree i:ℝ)+2*eps)≤Ctot*(3+H)^(J+2*eps)) ∧
        (∑i,C i*(3+H)^((degree i:ℝ)+2*eps))≤Ctot*(3+H)^(J+2*eps)) ∧
      ∀ᶠx in l,∀i,P i (degree i) (C i) x := by
  choose degree C hC hevent using hP
  obtain ⟨J,hJ,Ctot,hCtot,hbounds,hheight⟩ := finite_height_envelope degree C hC
  exact ⟨degree,C,J,Ctot,hJ,hCtot,hC,hbounds,hheight,eventually_finite_all l _ hevent⟩

end Cycle25.Numerator
end

/- Adapted from weighted-numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. -/

end
/- END ORIGINAL Cycle25.Numerator.FiniteHeight -/

/- BEGIN ORIGINAL Cycle25.Numerator.Damping; sha256 a492680bf8b3444dd814caf9b9fc7fa230fab3d8d35fc4efe552c1f14f043d93 -/
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
/- END ORIGINAL Cycle25.Numerator.Damping -/

/- BEGIN ORIGINAL Cycle25.Numerator.Holder; sha256 988093cb56bec632ed763a61acee0fcbe08619ee838ecc2c8b66d4592e6d1e1a -/
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
/- END ORIGINAL Cycle25.Numerator.Holder -/
