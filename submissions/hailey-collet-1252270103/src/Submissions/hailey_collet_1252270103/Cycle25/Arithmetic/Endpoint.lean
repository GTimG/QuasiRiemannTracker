import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! Exact arithmetic for T1 of the selected Cycle25 proof packet.
The endpoint is an algebraic real, specified by its polynomial and isolating interval.
These declarations make no assertion about Hecke or Dirichlet L-functions. -/

namespace Cycle25.Arithmetic

def quartic (x : ℝ) : ℝ := 927*x^4 - 3135*x^3 + 2433*x^2 + 275*x - 100
noncomputable def rootLo : ℝ := 16712007850680 / 100000000000000
noncomputable def rootHi : ℝ := 16712007850682 / 100000000000000

theorem rootLo_lt_rootHi : rootLo < rootHi := by norm_num [rootLo, rootHi]
theorem rootLo_coarse : (1:ℝ)/6 < rootLo := by norm_num [rootLo]
theorem rootHi_coarse : rootHi < (1:ℝ)/5 := by norm_num [rootHi]
theorem quartic_rootLo_neg : quartic rootLo < 0 := by norm_num [quartic, rootLo]
theorem quartic_rootHi_pos : 0 < quartic rootHi := by norm_num [quartic, rootHi]

theorem quartic_continuous : Continuous quartic := by unfold quartic; fun_prop

theorem quartic_hasDerivAt (x : ℝ) :
    HasDerivAt quartic (3708*x^3 - 9405*x^2 + 4866*x + 275) x := by
  unfold quartic
  convert ((((((hasDerivAt_id x).pow 4).const_mul 927).sub
    (((hasDerivAt_id x).pow 3).const_mul 3135)).add
    (((hasDerivAt_id x).pow 2).const_mul 2433)).add
    ((hasDerivAt_id x).const_mul 275)).sub_const 100 using 1
  · ext y; simp
  · simp; ring

theorem quartic_derivative_lower {x : ℝ} (hx : x ∈ Set.Icc (1/6:ℝ) (1/5)) :
    (3549:ℝ)/5 ≤ 3708*x^3 - 9405*x^2 + 4866*x + 275 := by
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hx2 : x^2 ≤ (1:ℝ)/25 := by nlinarith [hx.2]
  have hx3 : 0 ≤ x^3 := pow_nonneg hx0 _
  nlinarith [hx.1]

theorem quartic_strictMonoOn : StrictMonoOn quartic (Set.Icc (1/6:ℝ) (1/5)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) quartic_continuous.continuousOn
  intro x hx
  rw [(quartic_hasDerivAt x).deriv]
  have hxc : x ∈ Set.Icc (1/6:ℝ) (1/5) := interior_subset hx
  linarith [quartic_derivative_lower hxc]

theorem exists_isolated_root : ∃ x : ℝ, rootLo < x ∧ x < rootHi ∧ quartic x = 0 := by
  have h := intermediate_value_Icc (le_of_lt rootLo_lt_rootHi)
    quartic_continuous.continuousOn
  obtain ⟨x, hx, hpx⟩ := h (show (0:ℝ) ∈ Set.Icc (quartic rootLo) (quartic rootHi) from
    ⟨le_of_lt quartic_rootLo_neg, le_of_lt quartic_rootHi_pos⟩)
  refine ⟨x, ?_, ?_, hpx⟩
  · exact lt_of_le_of_ne hx.1 (by intro he; subst x; linarith [quartic_rootLo_neg])
  · exact lt_of_le_of_ne hx.2 (by intro he; subst x; linarith [quartic_rootHi_pos])

noncomputable def ell0 : ℝ := Classical.choose exists_isolated_root
theorem ell0_lo : rootLo < ell0 := (Classical.choose_spec exists_isolated_root).1
theorem ell0_hi : ell0 < rootHi := (Classical.choose_spec exists_isolated_root).2.1
theorem ell0_quartic : quartic ell0 = 0 := (Classical.choose_spec exists_isolated_root).2.2
theorem ell0_coarse : ell0 ∈ Set.Icc (1/6:ℝ) (1/5) :=
  ⟨le_of_lt (rootLo_coarse.trans ell0_lo), le_of_lt (ell0_hi.trans rootHi_coarse)⟩

theorem quartic_root_unique {x : ℝ} (hx : x ∈ Set.Icc (1/6:ℝ) (1/5))
    (hp : quartic x = 0) : x = ell0 :=
  quartic_strictMonoOn.injOn hx ell0_coarse (hp.trans ell0_quartic.symm)

noncomputable def b0 : ℝ := 11/12 - ell0/4
noncomputable def kappa0 : ℝ := (5-3*ell0)/6
noncomputable def theta : ℝ := 683505193/781250000

theorem kappa0_eq : kappa0 = 2*b0-1 := by unfold kappa0 b0; ring
theorem b0_lt_theta : b0 < theta := by
  have h := ell0_lo
  norm_num [rootLo] at h
  unfold b0 theta
  linarith

theorem theta_gap : 0 < theta-b0 ∧ theta-b0 < (4:ℝ)/100000000000000 := by
  constructor
  · linarith [b0_lt_theta]
  · have h := ell0_hi
    norm_num [rootHi] at h
    unfold theta b0
    linarith

theorem kappa0_range : (7:ℝ)/10 < kappa0 ∧ kappa0 < (3:ℝ)/4 := by
  have h := ell0_lo
  have h' := ell0_hi
  norm_num [rootLo, rootHi] at h h'
  unfold kappa0
  constructor <;> linarith

theorem theta_catalogue_chain : theta < (10499:ℝ)/12000 ∧
    (10499:ℝ)/12000 < 874957019420098946128604623/1000000000000000000000000000 ∧
    (874957019420098946128604623:ℝ)/1000000000000000000000000000 < 7/8 := by
  norm_num [theta]

end Cycle25.Arithmetic
