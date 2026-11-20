/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.Intake.QRH.Constants
import Candidate.C092.Intake.QRH.AnalyticClosure
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The precise ordinary target and its remaining analytic input

`OrdinaryTarget` is the canonical all-positive-moduli/all-characters claim at
the exact Appendix Q boundary.  `target_of_return_data` proves it CONDITIONALLY
on the explicitly typed `PhysicalReturn` input.  No such input is constructed
here.  In particular this file does not prove a new unconditional zero-free
region or supply a tracker `Candidate.bound` theorem.

The record states the closing data directly for mathlib's ordinary Dirichlet
L-function.  Constructing it from the manuscript's actual Hecke-family probe,
finite source certificates, norm pullback and Euler-factor restoration is a
remaining obligation; those transports are not hidden in a new axiom.
-/

set_option autoImplicit false

open Set Filter MeasureTheory Asymptotics
open scoped Topology

namespace QRH.Cycle090

noncomputable section

/-- Exactly the principal-pole exclusion used in the reference submissions. -/
def ordinaryAllowed {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) : Prop :=
  ¬ (χ = 1 ∧ s = 1)

/-- The actual allowed ordinary zero set, expressed through its real parts. -/
def ordinaryZeroRealParts {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) : Set ℝ :=
  zeroRealParts (DirichletCharacter.LFunction χ) (ordinaryAllowed χ)

/-- The supremum used by the conditional ordinary return interface.
Its nonemptiness is established from a hypothetical counterexample. -/
def ordinaryZeroSup {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) : ℝ :=
  sSup (ordinaryZeroRealParts χ)

/-- Existing mathlib nonvanishing on `Re s ≥ 1` bounds every eligible zero. -/
theorem ordinary_zero_re_lt_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hpole : ordinaryAllowed χ s)
    (hzero : DirichletCharacter.LFunction χ s = 0) : s.re < 1 := by
  by_contra h
  have hχs : χ ≠ 1 ∨ s ≠ 1 := by
    unfold ordinaryAllowed at hpole
    tauto
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hχs (le_of_not_gt h) hzero

/-- Boundedness of the actual ordinary zero-real-part set is not an assumption
of `PhysicalReturn`; it follows from existing mathlib nonvanishing. -/
theorem ordinary_zero_set_bddAbove {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) : BddAbove (ordinaryZeroRealParts χ) := by
  refine ⟨1, ?_⟩
  rintro r ⟨s, hpole, hzero, rfl⟩
  exact (ordinary_zero_re_lt_one χ hpole hzero).le

/-- The ordinary L-function is analytic on any open domain avoiding its
actual principal pole, including for imprimitive presentations. -/
theorem ordinary_L_analytic_off_pole {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {U : Set ℂ}
    (hU : IsOpen U) (hpole : ∀ s ∈ U, ordinaryAllowed χ s) :
    AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) U := by
  apply DifferentiableOn.analyticOnNhd _ hU
  intro s hs
  have hχs : s ≠ 1 ∨ χ ≠ 1 := by
    have hp := hpole s hs
    unfold ordinaryAllowed at hp
    tauto
  exact (DirichletCharacter.differentiableAt_LFunction χ s hχs).differentiableWithinAt

/-- The exact nonzero Gaussian multiplier in H47, with its original center. -/
def gaussianNumerator (H : ℂ → ℂ) (s : ℂ) : ℂ :=
  Complex.exp ((s - 5 / 6) ^ 2) * H s

/-- Multiplication by the original Gaussian preserves numerator analyticity. -/
theorem gaussianNumerator_analytic {H : ℂ → ℂ} {U : Set ℂ}
    (hH : AnalyticOnNhd ℂ H U) : AnalyticOnNhd ℂ (gaussianNumerator H) U := by
  exact (((analyticOnNhd_id.sub analyticOnNhd_const).pow 2).cexp).mul hH

/-- The manuscript's half-bound prevents cancellation of a denominator zero;
the Gaussian factor itself never vanishes. -/
theorem gaussianNumerator_nonzero {H : ℂ → ℂ} {s : ℂ}
    (hH : ‖H s - 1‖ ≤ (1 / 2 : ℝ)) : gaussianNumerator H s ≠ 0 := by
  exact mul_ne_zero (Complex.exp_ne_zero _) (numerator_nonzero_of_half_bound hH)

/-- Explicit missing Q.4 return data at a given actual zero supremum `β`.

`J` and `f` map a real scale to a complex scalar; `H` is a complex scalar
numerator.  The original Gaussian is inserted by `gaussianNumerator`.
All losses are real.  The open connected domain can omit the principal pole.
This structure has no instance in the present development. -/
structure ReturnData {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (β : ℝ) where
  J : ℝ → ℂ
  f : ℝ → ℂ
  H : ℂ → ℂ
  k : ℝ
  ω : ℝ
  σ : ℝ
  m : ℝ
  omega_pos : 0 < ω
  omega_lt : ω < (β - theta) / 4
  m_pos : 0 < m
  m_gap : m < β - theta - ω
  m_error : m < σ
  m_numerator : m < β - 87 / 100
  U : Set ℂ
  U_open : IsOpen U
  U_preconnected : IsPreconnected U
  U_subset : U ⊆ rightHalfPlane (β - m)
  U_pole_free : ∀ s ∈ U, ordinaryAllowed χ s
  zeros_in_U : ∀ s : ℂ, ordinaryAllowed χ s →
    DirichletCharacter.LFunction χ s = 0 →
    β - m / 2 < s.re → s.re ≤ β → s ∈ U
  f_local : LocallyIntegrableOn f (Ioi 0)
  J_bound : J =O[atTop] (fun Z : ℝ => Z ^ (theta - k + ω))
  error_bound : (fun Z => J Z - f Z) =O[atTop]
    (fun Z : ℝ => Z ^ (β - k - σ))
  zero_decay : ∀ b : ℝ, f =O[𝓝[>] 0] (fun Z : ℝ => Z ^ (-b))
  H_analytic : AnalyticOnNhd ℂ H U
  H_half_bound : ∀ s ∈ U, (87 / 100 : ℝ) < s.re →
    ‖H s - 1‖ ≤ (1 / 2 : ℝ)
  initial_identity : ∃ s₀ ∈ U,
    gaussianNumerator H =ᶠ[𝓝 s₀]
      fun s => DirichletCharacter.LFunction χ s * mellin f ((k : ℂ) - s)

/-- The still-unproved physical-return construction, requested only in the
contrary case and always at the supremum of the actual allowed zero set. -/
def PhysicalReturn {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) : Prop :=
  theta < ordinaryZeroSup χ → Nonempty (ReturnData χ (ordinaryZeroSup χ))

/-- Completed closing implication for one arbitrary ordinary presentation.
The substantive physical-return construction is an explicit hypothesis. -/
theorem nonvanishing_of_return_data {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hreturn : PhysicalReturn χ)
    {s : ℂ} (hs : theta < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  intro hzero
  have hmember : s.re ∈ ordinaryZeroRealParts χ := ⟨s, hpole, hzero, rfl⟩
  have hne : (ordinaryZeroRealParts χ).Nonempty := ⟨s.re, hmember⟩
  have hbdd := ordinary_zero_set_bddAbove χ
  have hsup : s.re ≤ ordinaryZeroSup χ := le_csSup hbdd hmember
  have hgap : theta < ordinaryZeroSup χ := hs.trans_le hsup
  obtain ⟨D⟩ := hreturn hgap
  have htop : D.f =O[atTop]
      (fun Z : ℝ => Z ^ (ordinaryZeroSup χ - D.k - D.m)) :=
    combine_probe_isBigO D.J D.f D.J_bound D.error_bound
      (by linarith [D.m_gap]) D.m_error.le
  exact supremum_contradiction_from_mellin_on_domain
    (DirichletCharacter.LFunction χ) (gaussianNumerator D.H) D.f
    (ordinaryAllowed χ) hne hbdd rfl D.m_pos D.m_numerator D.f_local htop
    D.zero_decay D.U_preconnected D.U_subset
    (gaussianNumerator_analytic D.H_analytic)
    (ordinary_L_analytic_off_pole χ D.U_open D.U_pole_free) D.zeros_in_U
    (fun z hz _ha hreal => gaussianNumerator_nonzero (D.H_half_bound z hz hreal))
    D.initial_identity

/-- Canonical exact target: all positive moduli, all ordinary Dirichlet
characters, all complex heights, and only the actual principal pole excluded. -/
def OrdinaryTarget : Prop :=
  ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ},
    theta < s.re → ¬ (χ = 1 ∧ s = 1) → DirichletCharacter.LFunction χ s ≠ 0

/-- The exact all-character target follows IF its physical-return data are
constructed for every presentation.  This is a conditional completion theorem,
not a proof that the missing data exist. -/
theorem target_of_return_data
    (hreturn : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), PhysicalReturn χ) :
    OrdinaryTarget := by
  intro q _hq χ s hs hpole
  exact nonvanishing_of_return_data χ (hreturn χ) hs hpole

end

end QRH.Cycle090
