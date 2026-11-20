/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Mathlib.Tactic

/-!
# Exact data for Appendix Q of the supplied Cycle 090 manuscript

These are literal rational data, not a pointwise certification of the numerical
physical-return margins. In particular, the constants prefixed `reported` are
reported lower bounds whose applicability to the physical cover is not proved
by this file. The input manuscript is `proof-c1876d05ad73.md`.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace QRH.Cycle090

noncomputable section

/-- The coefficient in Theorem Q and equation Q0. -/
def coefficient : ℝ := 63333603 / 500000000

/-- The strict half-plane boundary in Theorem Q and equation Q0. -/
def theta : ℝ := 436666397 / 500000000

/-- The preceding Appendix P boundary, used only for exact comparison. -/
def previousTheta : ℝ := 174666559 / 200000000

/-- Lower directed conductor endpoint in Q.1. -/
def hLower : ℝ := 8175840773 / 10000000000

/-- Upper directed conductor endpoint in Q.1. -/
def hUpper : ℝ := 8175840793 / 10000000000

/-- Source cost `s₀` from Q.1. -/
def sourceCost : ℝ := 1 / 10 ^ (260 : ℕ)

/-- Support extension `F_pad` from Q.1. -/
def rowPad : ℝ := 1 / 10 ^ (258 : ℕ)

/-- The separate padding debit from Q.1, not an extra inward fee. -/
def paddingDebit : ℝ := 15 * sourceCost / 16 + 2 * rowPad

/-- The witness collar `ε_a` in Q.1. -/
def witnessCollar : ℝ := 1 / 10000000000000

/-- The allocated inward debit `ε_b` in Q.1. -/
def inwardDebit : ℝ := 1 / 1000000000000

/-- The physical source cap `0.085` in Q.1. -/
def physicalCap : ℝ := 17 / 200

/-- The normalized mixed margin reported in Q.3; its cover is not certified here. -/
def reportedNormalizedMargin : ℝ := 500541 / 1000000000000000

/-- The mixed physical reserve reported in Q.3; its cover is not certified here. -/
def reportedPhysicalReserve : ℝ := 174177 / 1000000000000000

/-- The original-route reserve reported in Q.3, before separate padding. -/
def reportedOriginalReserve : ℝ := 1245083 / 200000000000000

/-- The source coefficient and boundary add to one exactly. -/
theorem coefficient_add_theta : coefficient + theta = 1 := by
  norm_num [coefficient, theta]

/-- The latest improvement is exactly one billionth. -/
theorem exact_improvement : previousTheta - theta = 1 / 1000000000 := by
  norm_num [previousTheta, theta]

/-- The directed conductor interval is nonempty and positive. -/
theorem conductor_interval : 0 < hLower ∧ hLower < hUpper ∧ hUpper < 1 := by
  norm_num [hLower, hUpper]

/-- The target lies strictly between 0.87 and the preceding boundary. -/
theorem target_interval : (87 / 100 : ℝ) < theta ∧ theta < previousTheta := by
  norm_num [theta, previousTheta]

/-- All separately budgeted allowances are positive. -/
theorem allowances_pos :
    0 < sourceCost ∧ 0 < rowPad ∧ 0 < paddingDebit ∧
    0 < witnessCollar ∧ 0 < inwardDebit := by
  have hs : 0 < sourceCost := by unfold sourceCost; positivity
  have hp : 0 < rowPad := by unfold rowPad; positivity
  refine ⟨hs, hp, ?_, ?_, ?_⟩
  · unfold paddingDebit
    positivity
  · norm_num [witnessCollar]
  · norm_num [inwardDebit]

/-- A loose rational upper bound sufficient for the geometric guards. -/
theorem rowPad_small : rowPad < 1 / 1000000000000 := by
  have hpow : (10 : ℝ) ^ 12 < 10 ^ (258 : ℕ) :=
    pow_lt_pow_right₀ (by norm_num) (by norm_num)
  have h := one_div_lt_one_div_of_lt (by positivity : (0 : ℝ) < 10 ^ (12 : ℕ)) hpow
  norm_num [rowPad] at h ⊢
  exact h

/-- The source cost is smaller than the support extension. -/
theorem sourceCost_le_rowPad : sourceCost ≤ rowPad := by
  apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 10 ^ (258 : ℕ))
  exact pow_le_pow_right₀ (by norm_num) (by norm_num)

/-- The chosen physical cap is strictly below the declared 0.11 cap. -/
theorem physicalCap_admissible : 0 < physicalCap ∧ physicalCap < 11 / 100 := by
  norm_num [physicalCap]

/-- The quoted reserves are positive numbers, independently of their claimed use. -/
theorem reported_reserves_pos :
    0 < reportedNormalizedMargin ∧ 0 < reportedPhysicalReserve ∧
    0 < reportedOriginalReserve := by
  norm_num [reportedNormalizedMargin, reportedPhysicalReserve, reportedOriginalReserve]

/-- If applicable, the quoted physical reserve exceeds the separate padding debit. -/
theorem padding_below_reported_reserve : paddingDebit < reportedPhysicalReserve := by
  have hs := sourceCost_le_rowPad
  have hp := rowPad_small
  norm_num [paddingDebit, reportedPhysicalReserve]
  linarith

/-- The declared outer-loss scale fits below the exterior acceptance threshold. -/
theorem outer_scale_below_inward : (1 / 100000000000000 : ℝ) < inwardDebit := by
  norm_num [inwardDebit]

/-- The reported leaf counts satisfy the four-way forest cardinality identity.
This identity alone does not certify any geometric coverage. -/
theorem reported_leaf_count : (9681 : ℕ) + 47 = 2045 + 3 * 2561 := by
  norm_num

/-- The reported visit count satisfies the corresponding forest node identity. -/
theorem reported_visit_count : (12289 : ℕ) = 2045 + 4 * 2561 := by
  norm_num

end

end QRH.Cycle090
