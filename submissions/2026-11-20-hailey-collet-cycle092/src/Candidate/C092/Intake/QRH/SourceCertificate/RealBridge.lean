/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.Intake.QRH.SourceCertificate.Core

/-!
# Real-response meaning of the literal source endpoint tests

The length endpoint and cutoff data in the certificate are rational, but the
response exponent in the proof is real.  This module defines the exact real
extensions of all three checked costs and proves their bounds throughout every
closed response bin.  The quota coefficient remains the certified conservative
rational quota, including its fifth-root upper enclosure.

This does not prove the separate monotonicity reductions in the real length,
zero band, ordinary witness, or radius.  Nor does it construct the analytic
source from the finite terminal arithmetic.
-/

set_option autoImplicit false

namespace QRH.SourceCertificate

noncomputable section

/-- Real-response extension of the literal short-inverse endpoint cost. -/
def shortCostReal (b : ℚ) (e : ℝ) (c : Cutoff) : ℝ :=
  e*((b : ℝ)+(capacity b : ℝ)-(H : ℝ)*
    ((c.inverse : ℝ)+(quota c.inverse c.rootUpper : ℝ))/2)

/-- Real-response extension of the literal amplified long-inverse cost. -/
def longCostReal (b : ℚ) (e : ℝ) (c : Cutoff) : ℝ :=
  e*((b : ℝ)+(capacity b : ℝ))-(H : ℝ)*
    ((5/6)-((5/6)-e)*((c.inverse : ℝ)+(c.ordinary : ℝ)))/2

/-- Real-response extension of the literal ordinary substitution cost, with
the same native continuation and positive part as the rational checker. -/
def ordinaryCostReal (b : ℚ) (e : ℝ) (c : Cutoff) : ℝ :=
  let delta := (H : ℝ)*(c.ordinary : ℝ)-(b : ℝ)
  e*(-delta+max 0 (2*(u : ℝ)+delta/2+(gain b : ℝ)-
    (H : ℝ)*(ordinaryGain c.ordinary : ℝ)))

/-- Simultaneous strict payment of all three real-response costs. -/
def EndpointPaidReal (b : ℚ) (e : ℝ) (c : Cutoff) : Prop :=
  shortCostReal b e c < (u-rho : ℚ) ∧
  longCostReal b e c < (u-rho : ℚ) ∧
  ordinaryCostReal b e c < (u-rho : ℚ)

/-- The real short cost agrees exactly with the checked rational value. -/
theorem shortCostReal_rat (b e : ℚ) (c : Cutoff) :
    shortCostReal b (e : ℝ) c = (shortCost b e c : ℝ) := by
  simp [shortCostReal, shortCost]

/-- The real long cost agrees exactly with the checked rational value. -/
theorem longCostReal_rat (b e : ℚ) (c : Cutoff) :
    longCostReal b (e : ℝ) c = (longCost b e c : ℝ) := by
  simp [longCostReal, longCost]

/-- Casting preserves the positive part in the checked ordinary cost. -/
theorem ordinaryCostReal_rat (b e : ℚ) (c : Cutoff) :
    ordinaryCostReal b (e : ℝ) c = (ordinaryCost b e c : ℝ) := by
  simp [ordinaryCostReal, ordinaryCost]

/-- A checked rational response endpoint gives the identical real inequality. -/
theorem endpointPaidReal_of_rat (b e : ℚ) (c : Cutoff)
    (h : EndpointPaid b e c) : EndpointPaidReal b (e : ℝ) c := by
  unfold EndpointPaidReal
  rw [shortCostReal_rat, longCostReal_rat, ordinaryCostReal_rat]
  exact_mod_cast h

/-- A real affine function bounded at two endpoints is bounded at every
intermediate real argument; no rationality assumption is placed on that argument. -/
theorem real_affine_lt_between {c d e e₀ e₁ B : ℝ}
    (h₀ : e₀ ≤ e) (h₁ : e ≤ e₁)
    (hc₀ : c*e₀+d < B) (hc₁ : c*e₁+d < B) : c*e+d < B := by
  rcases le_total 0 c with hc | hc
  · have := mul_le_mul_of_nonneg_left h₁ hc
    linarith
  · have := mul_le_mul_of_nonpos_left h₀ hc
    linarith

/-- Both checked rational endpoints pay every real response in their closed
bin.  The common diagonal response may be irrational. -/
theorem endpointPaidReal_between (b : ℚ) (c : Cutoff) {e : ℝ} {e₀ e₁ : ℚ}
    (h₀ : (e₀ : ℝ) ≤ e) (h₁ : e ≤ (e₁ : ℝ))
    (hp₀ : EndpointPaid b e₀ c) (hp₁ : EndpointPaid b e₁ c) :
    EndpointPaidReal b e c := by
  rcases endpointPaidReal_of_rat b e₀ c hp₀ with ⟨hs₀, hl₀, ho₀⟩
  rcases endpointPaidReal_of_rat b e₁ c hp₁ with ⟨hs₁, hl₁, ho₁⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold shortCostReal at *
    have h := real_affine_lt_between
      (c := (b : ℝ)+(capacity b : ℝ)-(H : ℝ)*
        ((c.inverse : ℝ)+(quota c.inverse c.rootUpper : ℝ))/2)
      (d := 0) (B := (u-rho : ℚ)) h₀ h₁
      (by simpa [mul_comm] using hs₀) (by simpa [mul_comm] using hs₁)
    nlinarith
  · have identity (x : ℝ) : longCostReal b x c =
        ((b : ℝ)+(capacity b : ℝ)-(H : ℝ)*
          ((c.inverse : ℝ)+(c.ordinary : ℝ))/2)*x +
        (H : ℝ)*((5/6)*((c.inverse : ℝ)+(c.ordinary : ℝ))-(5/6))/2 := by
      unfold longCostReal
      ring
    rw [identity] at hl₀ hl₁ ⊢
    exact real_affine_lt_between h₀ h₁ hl₀ hl₁
  · unfold ordinaryCostReal at *
    dsimp only at *
    have h := real_affine_lt_between
      (c := -((H : ℝ)*(c.ordinary : ℝ)-(b : ℝ))+
        max 0 (2*(u : ℝ)+((H : ℝ)*(c.ordinary : ℝ)-(b : ℝ))/2+
          (gain b : ℝ)-(H : ℝ)*(ordinaryGain c.ordinary : ℝ)))
      (d := 0) (B := (u-rho : ℚ)) h₀ h₁
      (by simpa [mul_comm] using ho₀) (by simpa [mul_comm] using ho₁)
    nlinarith

/-- A kernel-accepted source response bin supplies its literal support guards
and the cost bounds for every real response between its rational endpoints. -/
theorem binCheck_real_response (b k : ℚ) (i : ℕ) (c : Cutoff)
    (h : binCheck b k i c = true) {e : ℝ}
    (h₀ : ((k+(responseUpper-k)*(i:ℚ)/8 : ℚ) : ℝ) ≤ e)
    (h₁ : e ≤ ((k+(responseUpper-k)*(i+1:ℕ)/8 : ℚ) : ℝ)) :
    CutoffGuard b c ∧ EndpointPaidReal b e c := by
  rcases binCheck_sound b k i c h with ⟨hguard, hleft, hright⟩
  exact ⟨hguard, endpointPaidReal_between b c h₀ h₁ hleft hright⟩

/-- A uniform finite subdivision covers its complete closed real interval,
including shared edges and the final right endpoint. -/
theorem uniform_grid_cover (n : ℕ) {a d x : ℝ} (hn : 0 < n)
    (hlower : a ≤ x) (hupper : x ≤ a+(n : ℝ)*d) :
    ∃ i : ℕ, i < n ∧ a+(i : ℝ)*d ≤ x ∧ x ≤ a+(i+1 : ℕ)*d := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hnzero : n = 0
    · subst n
      exact ⟨0, by omega, by simpa using hlower, by simpa using hupper⟩
    · by_cases hlast : a+(n : ℝ)*d ≤ x
      · exact ⟨n, Nat.lt_succ_self n, hlast, hupper⟩
      · obtain ⟨i, hi, hleft, hright⟩ :=
          ih (Nat.pos_of_ne_zero hnzero) (le_of_not_ge hlast)
        exact ⟨i, hi.trans (Nat.lt_succ_self n), hleft, hright⟩

/-- An accepted source cell pays every real response in its entire high
range, using one of its eight actual recorded simultaneous cutoffs.  The length
argument of these costs is the cell's checked upper endpoint. -/
theorem cellCheck_high_response (c : Cell) (h : cellCheck c = true) {e : ℝ}
    (h₀ : (c.threshold : ℝ) ≤ e) (h₁ : e ≤ (responseUpper : ℝ)) :
    ∃ p ∈ c.cutoffs.zipIdx, CutoffGuard c.upper p.1 ∧ EndpointPaidReal c.upper e p.1 := by
  have hraw := h
  simp only [cellCheck, Bool.and_eq_true] at hraw
  obtain ⟨_, _, _, _, _, _, _, hlength⟩ := of_decide_eq_true hraw.1.1
  have hcast (j : ℕ) :
      ((c.threshold+(responseUpper-c.threshold)*(j:ℚ)/8 : ℚ) : ℝ) =
        (c.threshold : ℝ)+(j : ℝ)*(((responseUpper-c.threshold : ℚ) : ℝ)/8) := by
    push_cast
    ring
  have hend : (c.threshold : ℝ)+(8 : ℝ)*
      (((responseUpper-c.threshold : ℚ) : ℝ)/8) = (responseUpper : ℝ) := by
    push_cast
    ring
  obtain ⟨i, hi, hleft, hright⟩ := uniform_grid_cover 8 (by omega) h₀
    (show e ≤ (c.threshold : ℝ)+(8 : ℝ)*
      (((responseUpper-c.threshold : ℚ) : ℝ)/8) by rwa [hend])
  have hilength : i < c.cutoffs.length := by omega
  let cutoff : Cutoff := c.cutoffs[i]
  have hmem : (cutoff, i) ∈ c.cutoffs.zipIdx := by
    apply List.mk_mem_zipIdx_iff_getElem?.mpr
    exact List.getElem?_eq_getElem hilength
  obtain ⟨hguard, hp₀, hp₁⟩ := (cellCheck_sound c h).2.2.2 (cutoff, i) hmem
  refine ⟨(cutoff, i), hmem, hguard,
    endpointPaidReal_between c.upper cutoff ?_ ?_ hp₀ hp₁⟩
  · rwa [hcast]
  · rwa [hcast]

end

end QRH.SourceCertificate
