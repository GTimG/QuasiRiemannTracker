/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.Intake.QRH.SourceCertificate.LengthBridge
import Candidate.C092.Intake.QRH.SourceCertificate.QuotaBridge

/-!
# The actual zero-band parameter above the diagonal response

The finite checker evaluates the three high-response costs on the diagonal
`ν = e`.  The actual source has `ν ≥ e`.  This module uses the literal P.5/P.6
cost formulas and the certified support guards to prove that increasing `ν`
can only improve all three costs at radius `H`.

The optional curved-quota comparison uses the actual real fifth root.  These
are scalar inequalities; selecting genuine same-zero witnesses, extending to
other radii, and admitting the original analytic source are separate steps.
-/

set_option autoImplicit false

namespace QRH.SourceCertificate

noncomputable section

/-- Literal P.6 short-inverse cost at real length `y`, response `e`, and the
actual zero-band exponent `ν`, using the conservative certified quota. -/
def shortCostWithBand (y e ν : ℝ) (c : Cutoff) : ℝ :=
  ν*y+e*capacityAt y-(H : ℝ)*
    (ν*(c.inverse : ℝ)+e*(quota c.inverse c.rootUpper : ℝ))/2

/-- Literal P.6 amplified long-inverse cost with the actual zero-band exponent. -/
def longCostWithBand (y e ν : ℝ) (c : Cutoff) : ℝ :=
  ν*y+e*capacityAt y-(H : ℝ)*
    ((5/6)-((5/6)-ν)*((c.inverse : ℝ)+(c.ordinary : ℝ)))/2

/-- Literal P.5 ordinary-substitution cost with the actual zero-band exponent,
the original positive part, and the certified cutoff's native continuation. -/
def ordinaryCostWithBand (y e ν : ℝ) (c : Cutoff) : ℝ :=
  let delta := (H : ℝ)*(c.ordinary : ℝ)-y;
  -ν*delta+e*max 0 (2*(u : ℝ)+delta/2+QRH.Cycle090.sourceGain y-
    (H : ℝ)*(ordinaryGain c.ordinary : ℝ))

/-- All three actual zero-band costs are strictly paid at the original radius. -/
def PaidWithBand (y e ν : ℝ) (c : Cutoff) : Prop :=
  shortCostWithBand y e ν c < (u-rho : ℚ) ∧
  longCostWithBand y e ν c < (u-rho : ℚ) ∧
  ordinaryCostWithBand y e ν c < (u-rho : ℚ)

/-- The short-inverse diagonal reduction has exactly the support coefficient
`y - H*r/2`; no other term depends on the increased zero band. -/
theorem shortCostWithBand_difference (y e ν : ℝ) (c : Cutoff) :
    shortCostWithBand y e ν c-shortCostAt y e c =
      (ν-e)*(y-(H : ℝ)*(c.inverse : ℝ)/2) := by
  unfold shortCostWithBand shortCostAt
  ring

/-- The amplified inverse diagonal reduction uses the simultaneous sum cutoff. -/
theorem longCostWithBand_difference (y e ν : ℝ) (c : Cutoff) :
    longCostWithBand y e ν c-longCostAt y e c =
      (ν-e)*(y-(H : ℝ)*((c.inverse : ℝ)+(c.ordinary : ℝ))/2) := by
  unfold longCostWithBand longCostAt
  ring

/-- The ordinary diagonal reduction keeps its positive part unchanged and
improves only the actual witness comparison term. -/
theorem ordinaryCostWithBand_difference (y e ν : ℝ) (c : Cutoff) :
    ordinaryCostWithBand y e ν c-ordinaryCostAt y e c =
      (ν-e)*(y-(H : ℝ)*(c.ordinary : ℝ)) := by
  unfold ordinaryCostWithBand ordinaryCostAt
  dsimp only
  ring

/-- The literal support guards make all three diagonal values upper bounds
for every larger actual zero band.  No upper bound on `ν` is needed here. -/
theorem costsWithBand_le_diagonal (c : Cutoff) {y e ν : ℝ}
    (hν : e ≤ ν)
    (hr : 2*y/(H : ℝ) ≤ (c.inverse : ℝ))
    (hm : y/(H : ℝ) ≤ (c.ordinary : ℝ))
    (hsum : y < (H : ℝ)*((c.inverse : ℝ)+(c.ordinary : ℝ))/2) :
    shortCostWithBand y e ν c ≤ shortCostAt y e c ∧
    longCostWithBand y e ν c ≤ longCostAt y e c ∧
    ordinaryCostWithBand y e ν c ≤ ordinaryCostAt y e c := by
  have hH : (0 : ℝ) < (H : ℝ) := by norm_num [H,u]
  have hdiff : 0 ≤ ν-e := sub_nonneg.mpr hν
  have hr' := (div_le_iff₀ hH).mp hr
  have hm' := (div_le_iff₀ hH).mp hm
  refine ⟨sub_nonpos.mp ?_, sub_nonpos.mp ?_, sub_nonpos.mp ?_⟩
  · rw [shortCostWithBand_difference]
    apply mul_nonpos_of_nonneg_of_nonpos hdiff
    nlinarith
  · rw [longCostWithBand_difference]
    exact mul_nonpos_of_nonneg_of_nonpos hdiff (sub_nonpos.mpr hsum.le)
  · rw [ordinaryCostWithBand_difference]
    apply mul_nonpos_of_nonneg_of_nonpos hdiff
    nlinarith

/-- A paid diagonal response pays the literal three high costs for every
actual zero-band exponent above it, using the same simultaneous cutoffs. -/
theorem paidAt_with_band (c : Cutoff) {y e ν : ℝ}
    (hν : e ≤ ν)
    (hr : 2*y/(H : ℝ) ≤ (c.inverse : ℝ))
    (hm : y/(H : ℝ) ≤ (c.ordinary : ℝ))
    (hsum : y < (H : ℝ)*((c.inverse : ℝ)+(c.ordinary : ℝ))/2)
    (hpaid : PaidAt y e c) : PaidWithBand y e ν c := by
  obtain ⟨hi, hl, ho⟩ := costsWithBand_le_diagonal c hν hr hm hsum
  exact ⟨hi.trans_lt hpaid.1, hl.trans_lt hpaid.2.1, ho.trans_lt hpaid.2.2⟩

/-- Every accepted length cell pays every real high response and every larger
real zero band, at every real length in the cell, with an actual recorded cutoff. -/
theorem cellCheck_real_band_response (c : Cell) (h : cellCheck c = true) {y e ν : ℝ}
    (hyl : (c.lower : ℝ) ≤ y) (hyu : y ≤ (c.upper : ℝ))
    (hel : (c.threshold : ℝ) ≤ e) (heu : e ≤ (responseUpper : ℝ))
    (hν : e ≤ ν) :
    ∃ p ∈ c.cutoffs.zipIdx, CutoffGuard c.upper p.1 ∧ PaidWithBand y e ν p.1 ∧
      2*y/(H : ℝ) ≤ (p.1.inverse : ℝ) ∧ y/(H : ℝ) ≤ (p.1.ordinary : ℝ) ∧
        y < (H : ℝ)*((p.1.inverse : ℝ)+(p.1.ordinary : ℝ))/2 := by
  obtain ⟨p, hp, hg, hpaid, hr, hm, hsum⟩ :=
    cellCheck_real_length_response c h hyl hyu hel heu
  exact ⟨p, hp, hg, paidAt_with_band p.1 hν hr hm hsum hpaid, hr, hm, hsum⟩

/-- The actual short-inverse zero-band cost using the genuine curved radical,
at a real source length and real response. -/
def shortCurvedCostWithBand (y e ν : ℝ) (c : Cutoff) : ℝ :=
  ν*y+e*capacityAt y-(H : ℝ)*
    (ν*(c.inverse : ℝ)+e*curvedQuota (c.inverse : ℝ))/2

/-- Replacing the conservative quota with the actual curved radical improves
the full zero-band short-inverse cost at any real source length. -/
theorem shortCurvedCostWithBand_le (y ν : ℝ) (c : Cutoff) {e : ℝ}
    (he : 0 ≤ e) (hlo : (3 : ℚ)/4 ≤ c.inverse) (hhi : c.inverse < (7 : ℚ)/9)
    (hguard : RootGuard c.inverse c.rootUpper) :
    shortCurvedCostWithBand y e ν c ≤ shortCostWithBand y e ν c := by
  have hquota := quota_le_curvedQuota hlo hhi hguard
  have hH : (0 : ℝ) ≤ (H : ℝ) := by norm_num [H,u]
  have hmul := mul_le_mul_of_nonneg_left hquota he
  have hsum : ν*(c.inverse : ℝ)+e*(quota c.inverse c.rootUpper : ℝ) ≤
      ν*(c.inverse : ℝ)+e*curvedQuota (c.inverse : ℝ) := by linarith
  have hscale := mul_le_mul_of_nonneg_left hsum hH
  unfold shortCurvedCostWithBand shortCostWithBand
  exact sub_le_sub_left (div_le_div_of_nonneg_right hscale (by norm_num : (0 : ℝ) ≤ 2)) _

/-- Paid conservative zero-band data also pay the actual curved short cost. -/
theorem shortCurvedCostWithBand_paid (y ν : ℝ) (c : Cutoff) {e : ℝ}
    (he : 0 ≤ e) (hlo : (3 : ℚ)/4 ≤ c.inverse) (hhi : c.inverse < (7 : ℚ)/9)
    (hguard : RootGuard c.inverse c.rootUpper) (hpaid : PaidWithBand y e ν c) :
    shortCurvedCostWithBand y e ν c < (u-rho : ℚ) :=
  (shortCurvedCostWithBand_le y ν c he hlo hhi hguard).trans_lt hpaid.1

end

end QRH.SourceCertificate
