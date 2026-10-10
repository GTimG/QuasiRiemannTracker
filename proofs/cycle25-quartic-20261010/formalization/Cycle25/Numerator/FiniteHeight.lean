import Mathlib

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
