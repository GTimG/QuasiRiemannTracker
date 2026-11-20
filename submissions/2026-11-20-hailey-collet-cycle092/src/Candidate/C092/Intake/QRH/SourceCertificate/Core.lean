/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Mathlib.Tactic

/-!
# Literal rational source tests from the recovered Cycle 088 certificate

This checker computes the actual P.2 endpoint costs from each recorded cutoff.
Floating-point proposals from the original generator are not used here. Curved
quota values carry an explicit rational upper enclosure of the fifth root and
are checked by an exact fifth-power inequality. Analytic source admission is a
separate obligation.
-/

set_option autoImplicit false
namespace QRH.SourceCertificate

/-- Source induction cost from P.1. -/
def u : ℚ := 3 / 1000000
/-- Regular-core radial cutoff from P.1. -/
def H : ℚ := 1 - 6 * u
/-- Strict source reserve from P.1. -/
def rho : ℚ := 1 / 50000000000
/-- Upper endpoint of the response interval. -/
def responseUpper : ℚ := 2501 / 5000
/-- Upper ordinary source cap. -/
def Y : ℚ := 243 / 625
/-- Source gain seam. -/
def seam : ℚ := 747 / 2000
/-- Cubic source gain on and above the seam. -/
def upperGain (y : ℚ) : ℚ :=
  (2309 / 500) * (Y - y)^2 + (101 / 2) * (Y - y)^3 +
    (31 / 100000) * (Y - y) - 1 / 10000000
/-- Literal piecewise P1 source gain. -/
def gain (y : ℚ) : ℚ :=
  if y < seam then upperGain seam + (87 / 500) * (seam-y) + (67 / 10)*(seam-y)^2
  else upperGain y
/-- Ordinary source gain with the genuine native continuation above Y. -/
def ordinaryGain (m : ℚ) : ℚ := if m ≤ Y then gain m else 0
/-- The radicand of the scaled fifth root appearing in the curved quota. -/
def quotaRadicand (r : ℚ) : ℚ := (5 / 16)^5 * 7 * r^4 * (r - 2 / 3)
/-- A rational lower quota; `rootUpper` bounds the scaled fifth root. -/
def quota (r rootUpper : ℚ) : ℚ :=
  if r < 3 / 4 then (1-r)/2 + 5805911 / 100000000 - (379981 / 5000000)*r
  else if 7 / 9 ≤ r then (1-r)/2
  else (1-r)/2 + (11/16)*r - 7/24 - rootUpper
/-- A root enclosure is needed only on the actual curved branch. -/
def RootGuard (r rootUpper : ℚ) : Prop :=
  (3 / 4 ≤ r ∧ r < 7 / 9) → 0 ≤ rootUpper ∧ quotaRadicand r ≤ rootUpper^5
instance (r rootUpper : ℚ) : Decidable (RootGuard r rootUpper) := inferInstanceAs
  (Decidable ((3 / 4 ≤ r ∧ r < 7 / 9) → 0 ≤ rootUpper ∧ quotaRadicand r ≤ rootUpper^5))

/-- A simultaneous inverse and ordinary cutoff plus its exact radical enclosure. -/
structure Cutoff where
  inverse : ℚ
  ordinary : ℚ
  rootUpper : ℚ
  deriving Repr, DecidableEq

/-- The native/count capacity P in the original source checker. -/
def capacity (b : ℚ) : ℚ := 1/2-H/4-b/2+gain b-u
/-- Short-inverse cost from P6 on the common diagonal response. -/
def shortCost (b e : ℚ) (c : Cutoff) : ℚ :=
  e*(b+capacity b-H*(c.inverse+quota c.inverse c.rootUpper)/2)
/-- Amplified long-inverse cost from P6. -/
def longCost (b e : ℚ) (c : Cutoff) : ℚ :=
  e*(b+capacity b)-H*((5/6)-((5/6)-e)*(c.inverse+c.ordinary))/2
/-- Positive ordinary-substitution cost from P5, including the native continuation. -/
def ordinaryCost (b e : ℚ) (c : Cutoff) : ℚ :=
  let delta := H*c.ordinary-b
  e*(-delta+max 0 (2*u+delta/2+gain b-H*ordinaryGain c.ordinary))
/-- The exact three high-response inequalities at a response endpoint. -/
def EndpointPaid (b e : ℚ) (c : Cutoff) : Prop :=
  shortCost b e c < u-rho ∧ longCost b e c < u-rho ∧ ordinaryCost b e c < u-rho
instance (b e : ℚ) (c : Cutoff) : Decidable (EndpointPaid b e c) := inferInstanceAs
  (Decidable (shortCost b e c < u-rho ∧ longCost b e c < u-rho ∧ ordinaryCost b e c < u-rho))
/-- Original support and simultaneous-cutoff guards for a high-response bin. -/
def CutoffGuard (b : ℚ) (c : Cutoff) : Prop :=
  2*b/H ≤ c.inverse ∧ b/H ≤ c.ordinary ∧ b < H*(c.inverse+c.ordinary)/2 ∧
  27/25 < c.inverse+c.ordinary ∧ c.inverse+c.ordinary < 6/5 ∧
  367/500 < c.inverse ∧ c.inverse < 4/5 ∧ c.ordinary < 39/100 ∧
  RootGuard c.inverse c.rootUpper
instance (b : ℚ) (c : Cutoff) : Decidable (CutoffGuard b c) := inferInstanceAs
  (Decidable (2*b/H ≤ c.inverse ∧ b/H ≤ c.ordinary ∧ b < H*(c.inverse+c.ordinary)/2 ∧
  27/25 < c.inverse+c.ordinary ∧ c.inverse+c.ordinary < 6/5 ∧
  367/500 < c.inverse ∧ c.inverse < 4/5 ∧ c.ordinary < 39/100 ∧
  RootGuard c.inverse c.rootUpper))
/-- Check the literal support and both endpoint costs of one recorded response bin. -/
def binCheck (b k : ℚ) (i : ℕ) (c : Cutoff) : Bool :=
  decide (CutoffGuard b c ∧
    EndpointPaid b (k+(responseUpper-k)*(i:ℚ)/8) c ∧
    EndpointPaid b (k+(responseUpper-k)*(i+1:ℕ)/8) c)

/-- Acceptance means every literal support and cost inequality holds. -/
theorem binCheck_sound (b k : ℚ) (i : ℕ) (c : Cutoff)
    (h : binCheck b k i c = true) :
    CutoffGuard b c ∧ EndpointPaid b (k+(responseUpper-k)*(i:ℚ)/8) c ∧
    EndpointPaid b (k+(responseUpper-k)*(i+1:ℕ)/8) c := by
  exact of_decide_eq_true h

end QRH.SourceCertificate

namespace QRH.SourceCertificate

/-- An affine function is below a strict bound throughout an interval if both endpoints are. -/
theorem affine_lt_between {c d e e₀ e₁ B : ℚ}
    (h₀ : e₀ ≤ e) (h₁ : e ≤ e₁)
    (hc₀ : c*e₀+d < B) (hc₁ : c*e₁+d < B) : c*e+d < B := by
  rcases le_total 0 c with hc | hc
  · have := mul_le_mul_of_nonneg_left h₁ hc
    linarith
  · have := mul_le_mul_of_nonpos_left h₀ hc
    linarith

/-- All three checked costs are affine in the common diagonal response. -/
theorem endpointPaid_between (b : ℚ) (c : Cutoff) {e e₀ e₁ : ℚ}
    (h₀ : e₀ ≤ e) (h₁ : e ≤ e₁)
    (hp₀ : EndpointPaid b e₀ c) (hp₁ : EndpointPaid b e₁ c) :
    EndpointPaid b e c := by
  rcases hp₀ with ⟨hs₀, hl₀, ho₀⟩
  rcases hp₁ with ⟨hs₁, hl₁, ho₁⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold shortCost at *
    have h := affine_lt_between (c := b+capacity b-H*(c.inverse+quota c.inverse c.rootUpper)/2)
      (d := 0) (B := u-rho) h₀ h₁ (by simpa [mul_comm] using hs₀) (by simpa [mul_comm] using hs₁)
    nlinarith
  · have identity (x : ℚ) : longCost b x c =
        (b+capacity b-H*(c.inverse+c.ordinary)/2)*x +
        H*((5/6)*(c.inverse+c.ordinary)-(5/6))/2 := by
      unfold longCost
      ring
    rw [identity] at hl₀ hl₁ ⊢
    exact affine_lt_between h₀ h₁ hl₀ hl₁
  · unfold ordinaryCost at *
    dsimp only at *
    have h := affine_lt_between
      (c := -(H*c.ordinary-b)+max 0 (2*u+(H*c.ordinary-b)/2+gain b-H*ordinaryGain c.ordinary))
      (d := 0) (B := u-rho) h₀ h₁ (by simpa [mul_comm] using ho₀) (by simpa [mul_comm] using ho₁)
    nlinarith

/-- The fifth-power guard makes the recorded curved quota a lower bound for any genuine root. -/
theorem curved_quota_lower {r rootUpper root : ℝ}
    (hupper : 0 ≤ rootUpper)
    (hguard : (5/16)^5*7*r^4*(r-2/3) ≤ rootUpper^5)
    (hroot : root^5 = (5/16)^5*7*r^4*(r-2/3)) :
    (1-r)/2+(11/16)*r-7/24-rootUpper ≤ (1-r)/2+(11/16)*r-7/24-root := by
  have h : root ≤ rootUpper :=
    le_of_pow_le_pow_left₀ (by norm_num : (5 : ℕ) ≠ 0) hupper (by rw [hroot]; exact hguard)
  linarith

/-- One length cell, including the eight simultaneous response cutoffs recorded in JSON. -/
structure Cell where
  lower : ℚ
  upper : ℚ
  threshold : ℚ
  cutoffs : List Cutoff
  deriving Repr, DecidableEq

/-- Literal low-response regular-core replacement bracket from P4. -/
def lowBracket (y : ℚ) : ℚ := 2*u+gain y-H*gain (y/H)
/-- The low-response cost is strictly paid at one checked length and response threshold. -/
def LowPaid (k y : ℚ) : Prop := k*lowBracket y < u-rho
instance (k y : ℚ) : Decidable (LowPaid k y) := inferInstanceAs
  (Decidable (k*lowBracket y < u-rho))
/-- Test both length endpoints and the sole possible displaced source seam. -/
def lowCheck (c : Cell) : Bool :=
  decide (LowPaid c.threshold c.lower ∧ LowPaid c.threshold c.upper ∧
    (c.lower < H*seam ∧ H*seam < c.upper → LowPaid c.threshold (H*seam)))
/-- Validate the source grid, low-response tests, and all eight high-response bins. -/
def cellCheck (c : Cell) : Bool :=
  decide ((369:ℚ)/1000 ≤ c.lower ∧ c.lower < c.upper ∧ c.upper ≤ Y ∧
    c.upper-c.lower = 1/200000 ∧ ¬(c.lower < seam ∧ seam < c.upper) ∧
    (19:ℚ)/50 < c.threshold ∧ c.threshold ≤ responseUpper ∧ c.cutoffs.length = 8) &&
  lowCheck c && c.cutoffs.zipIdx.all (fun p => binCheck c.upper c.threshold p.2 p.1)

/-- An accepted cell exposes every low test and every actual high-bin inequality. -/
theorem cellCheck_sound (c : Cell) (h : cellCheck c = true) :
    LowPaid c.threshold c.lower ∧ LowPaid c.threshold c.upper ∧
    (c.lower < H*seam ∧ H*seam < c.upper → LowPaid c.threshold (H*seam)) ∧
    ∀ p ∈ c.cutoffs.zipIdx, CutoffGuard c.upper p.1 ∧
      EndpointPaid c.upper (c.threshold+(responseUpper-c.threshold)*(p.2:ℚ)/8) p.1 ∧
      EndpointPaid c.upper (c.threshold+(responseUpper-c.threshold)*(p.2+1:ℕ)/8) p.1 := by
  simp only [cellCheck, Bool.and_eq_true] at h
  have hlow : LowPaid c.threshold c.lower ∧ LowPaid c.threshold c.upper ∧
      (c.lower < H*seam ∧ H*seam < c.upper → LowPaid c.threshold (H*seam)) :=
    of_decide_eq_true h.1.2
  refine ⟨hlow.1, hlow.2.1, hlow.2.2, ?_⟩
  intro p hp
  exact binCheck_sound c.upper c.threshold p.2 p.1 ((List.all_eq_true.mp h.2) p hp)

/-- Compute acceptance for a finite batch of literal source cells. -/
def cellsCheck (cells : List Cell) : Bool := cells.all cellCheck
/-- Batch acceptance implies the full tests for each member. -/
theorem cellsCheck_sound (cells : List Cell) (h : cellsCheck cells = true)
    (c : Cell) (hc : c ∈ cells) : cellCheck c = true :=
  (List.all_eq_true.mp h) c hc

end QRH.SourceCertificate

namespace QRH.SourceCertificate

/-- Check that a sequence of nondegenerate rational cells exactly joins two endpoints. -/
def chainCheck (start finish : ℚ) : List Cell → Bool
  | [] => decide (start = finish)
  | c :: cs => decide (start = c.lower ∧ c.lower < c.upper) && chainCheck c.upper finish cs

/-- A checked chain covers every real point after its left endpoint through its right endpoint. -/
theorem chainCheck_openCover (cs : List Cell) (start finish : ℚ)
    (h : chainCheck start finish cs = true) {y : ℝ}
    (hstart : (start : ℝ) < y) (hfinish : y ≤ (finish : ℝ)) :
    ∃ c ∈ cs, (c.lower : ℝ) ≤ y ∧ y ≤ (c.upper : ℝ) := by
  induction cs generalizing start with
  | nil =>
    have heq : start = finish := of_decide_eq_true h
    rw [heq] at hstart
    exact False.elim (not_lt_of_ge hfinish hstart)
  | cons c cs ih =>
    simp only [chainCheck, Bool.and_eq_true] at h
    have hfirst : start = c.lower ∧ c.lower < c.upper := of_decide_eq_true h.1
    by_cases hy : y ≤ (c.upper : ℝ)
    · refine ⟨c, List.mem_cons_self, ?_, hy⟩
      rw [hfirst.1] at hstart
      exact le_of_lt hstart
    · obtain ⟨d, hd, hlow, hupp⟩ := ih c.upper h.2 (lt_of_not_ge hy)
      exact ⟨d, List.mem_cons_of_mem c hd, hlow, hupp⟩

/-- A nonempty checked chain covers its entire closed real interval. -/
theorem chainCheck_closedCover (cs : List Cell) (start finish : ℚ)
    (h : chainCheck start finish cs = true) (hne : cs ≠ []) {y : ℝ}
    (hstart : (start : ℝ) ≤ y) (hfinish : y ≤ (finish : ℝ)) :
    ∃ c ∈ cs, (c.lower : ℝ) ≤ y ∧ y ≤ (c.upper : ℝ) := by
  rcases eq_or_lt_of_le hstart with heq | hlt
  · cases cs with
    | nil => exact False.elim (hne rfl)
    | cons c cs =>
      simp only [chainCheck, Bool.and_eq_true] at h
      have hfirst : start = c.lower ∧ c.lower < c.upper := of_decide_eq_true h.1
      refine ⟨c, List.mem_cons_self, ?_, ?_⟩
      · rw [←hfirst.1, heq]
      · have hlt : (c.lower : ℝ) < (c.upper : ℝ) := by exact_mod_cast hfirst.2
        rw [←hfirst.1, heq] at hlt
        exact le_of_lt hlt
  · exact chainCheck_openCover cs start finish h hlt hfinish

end QRH.SourceCertificate
