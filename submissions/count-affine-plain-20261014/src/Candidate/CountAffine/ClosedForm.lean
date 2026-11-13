/- A48 (AI-assisted, for liqsweep): the closed-form count of the detector game in which the
critical plain witness is controlled by Collet's interior affine moment (cycle61 Thm 2.2).
Released under Apache 2.0, like the Cycle61 source it extends. -/
import Mathlib.Tactic

set_option autoImplicit false

namespace Cycle61.CountAffine
noncomputable section

/-- Collet/Gao affine-moment constants (Cycle61.Arithmetic.lambda, Cycle61.Arithmetic.B at q0 = 67/100). -/
def lambda : ℝ := 16281/4106
def B : ℝ := 202497947/205300000

/-- Upper end of the plain window used with the affine moment (Collet's `N`). -/
def plainTop : ℝ := 264/625

def sI (δ p : ℝ) : ℝ := δ - δ*p
def sP (δ p : ℝ) : ℝ := 2*δ - 4*(δ*p)/lambda
def aP (δ p : ℝ) : ℝ := 1 - 2*(δ*p)*B/lambda
def tNum (δ p : ℝ) : ℝ := (1-δ*p)*sP δ p + aP δ p*sI δ p - (sI δ p + sP δ p)/6
def tDen (δ p : ℝ) : ℝ := (5/6-δ)*(sI δ p + sP δ p) + sI δ p*sP δ p
/-- The balanced prover cut-off. -/
def tStar (δ p : ℝ) : ℝ := tNum δ p / tDen δ p
/-- The closed-form count. -/
def RStar (δ p : ℝ) : ℝ := 1/6 + (5/6-δ)*tStar δ p
/-- The crossing plain length and inverse length. -/
def mC (δ p : ℝ) : ℝ := (aP δ p - 1 + δ*p + sI δ p*tStar δ p)/(sI δ p + sP δ p)
def rC (δ p : ℝ) : ℝ := tStar δ p - mC δ p
/-- Slot capacity supplied by the interior affine moment at plain length `m`. -/
def zS (m : ℝ) : ℝ := min (1/25) ((B-2*m)/lambda)
def plainNew (δ p m : ℝ) : ℝ := 1 - 2*δ*m - 2*(δ*p)*zS m
def plainOld (κ δ p m : ℝ) : ℝ := 1 - 2*δ*m - 2*(δ*p)*(1-2*m)/(6*κ)
def inverseLine (δ p r : ℝ) : ℝ := 1 - δ*p - sI δ p*r
def mcNum (δ p : ℝ) : ℝ := (aP δ p - 1 + δ*p)*tDen δ p + sI δ p*tNum δ p
def condTlo (δ p : ℝ) : ℝ := tNum δ p - 1927/1850*tDen δ p
def condThi (δ p : ℝ) : ℝ := 3/2*tDen δ p - tNum δ p
def condRC (δ p : ℝ) : ℝ :=
  tNum δ p*(sI δ p + sP δ p) - mcNum δ p - 2337/3700*tDen δ p*(sI δ p + sP δ p)
def condCap (δ p : ℝ) : ℝ := 2*mcNum δ p - (B - lambda/25)*tDen δ p*(sI δ p + sP δ p)
def condB3 (δ p : ℝ) : ℝ :=
  tDen δ p/6 + (5/6-δ)*tNum δ p - ((1-δ*p)*tDen δ p - sI δ p*(tNum δ p - 41/100*tDen δ p))
/-- The new branch count: the closed form, or the old plain moment just above the window. -/
def newBranch (κ δ p : ℝ) : ℝ := max (RStar δ p) (plainOld κ δ p plainTop)

/-- The two rectangles on which the closed form is used. Each δ-slice is an upper set in `p`. -/
def inRegion (δ p : ℝ) : Prop :=
  (29/64 ≤ δ ∧ δ ≤ 63/128 ∧ 15/32 ≤ p ∧ p ≤ 1/2) ∨
  (115/256 ≤ δ ∧ δ ≤ 29/64 ∧ 31/64 ≤ p ∧ p ≤ 1/2)

theorem inRegion_up {δ p p' : ℝ} (h : inRegion δ p) (hp : p ≤ p') (hp' : p' ≤ 1/2) :
    inRegion δ p' := by
  rcases h with h | h
  · exact Or.inl ⟨h.1, h.2.1, by linarith [h.2.2.1], hp'⟩
  · exact Or.inr ⟨h.1, h.2.1, by linarith [h.2.2.1], hp'⟩

theorem inRegion_bounds {δ p : ℝ} (h : inRegion δ p) :
    115/256 ≤ δ ∧ δ ≤ 63/128 ∧ 15/32 ≤ p ∧ p ≤ 1/2 := by
  rcases h with h | h
  · exact ⟨by linarith [h.1], h.2.1, h.2.2.1, h.2.2.2⟩
  · exact ⟨h.1, by linarith [h.2.1], by linarith [h.2.2.1], h.2.2.2⟩

theorem lambda_bounds : (39/10:ℝ) < lambda ∧ lambda < 4 := by
  constructor <;> norm_num [lambda]

theorem B_bounds : (98/100:ℝ) < B ∧ B < 1 := by
  constructor <;> norm_num [B]

/-- The two crossing identities defining the closed form. -/
theorem crossing_identities {δ p : ℝ} (hD : tDen δ p ≠ 0) (hS : sI δ p + sP δ p ≠ 0) :
    inverseLine δ p (rC δ p) = RStar δ p ∧
      aP δ p - sP δ p*mC δ p = RStar δ p := by
  have hl : lambda ≠ 0 := by norm_num [lambda]
  constructor
  · unfold inverseLine rC mC RStar tStar
    field_simp
    unfold tNum tDen
    ring
  · unfold mC RStar tStar
    field_simp
    unfold tNum tDen
    ring

theorem RStar_ge_base {δ p : ℝ} (hδ : δ ≤ 5/6) (ht : 1 ≤ tStar δ p) : 1 - δ ≤ RStar δ p := by
  unfold RStar
  nlinarith

theorem inverseLine_anti {δ p r r' : ℝ} (hs : 0 ≤ sI δ p) (hr : r ≤ r') :
    inverseLine δ p r' ≤ inverseLine δ p r := by
  unfold inverseLine
  nlinarith

theorem sI_nonneg {δ p : ℝ} (hδ : 0 ≤ δ) (hp : p ≤ 1) : 0 ≤ sI δ p := by
  unfold sI
  nlinarith

/-- `plainNew` is nonincreasing in the plain length. -/
theorem plainNew_anti {δ p m m' : ℝ} (hδ : 0 ≤ δ) (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (hm : m ≤ m') : plainNew δ p m' ≤ plainNew δ p m := by
  have hl := lambda_bounds
  have hlp : 0 < lambda := by linarith
  have hq : 0 ≤ δ*p := mul_nonneg hδ hp0
  have hqd : δ*p ≤ δ/2 := by nlinarith
  -- zS m' ≥ zS m - 2(m'-m)/lambda
  have hz : zS m - 2*(m'-m)/lambda ≤ zS m' := by
    unfold zS
    rcases le_total (1/25:ℝ) ((B-2*m')/lambda) with h | h
    · rw [min_eq_left h]
      have h1 : min (1/25:ℝ) ((B-2*m)/lambda) ≤ 1/25 := min_le_left _ _
      have h2 : 0 ≤ 2*(m'-m)/lambda := div_nonneg (by linarith) hlp.le
      linarith
    · rw [min_eq_right h]
      have h1 : min (1/25:ℝ) ((B-2*m)/lambda) ≤ (B-2*m)/lambda := min_le_right _ _
      have he : (B-2*m)/lambda - 2*(m'-m)/lambda = (B-2*m')/lambda := by
        field_simp; ring
      linarith
  have hcoef : 2*(δ*p)*(2*(m'-m)/lambda) ≤ 2*δ*(m'-m) := by
    have h1 : 2*(m'-m)/lambda ≤ (m'-m) := by
      rw [div_le_iff₀ hlp]
      nlinarith
    have h2 : 0 ≤ 2*(m'-m)/lambda := div_nonneg (by linarith) hlp.le
    nlinarith
  unfold plainNew
  nlinarith

theorem plainOld_anti {κ δ p m m' : ℝ} (hk : 7/10 ≤ κ) (hδ : 0 ≤ δ) (hp0 : 0 ≤ p)
    (hp : p ≤ 1/2) (hm : m ≤ m') : plainOld κ δ p m' ≤ plainOld κ δ p m := by
  have hk0 : 0 < 6*κ := by linarith
  have hq : 0 ≤ δ*p := mul_nonneg hδ hp0
  have hqd : δ*p ≤ δ/2 := by nlinarith
  have hid : plainOld κ δ p m - plainOld κ δ p m' =
      (m'-m)*(2*δ - 4*(δ*p)/(6*κ)) := by
    unfold plainOld; field_simp; ring
  have hc : 4*(δ*p)/(6*κ) ≤ 2*δ := by
    rw [div_le_iff₀ hk0]; nlinarith
  have : 0 ≤ (m'-m)*(2*δ - 4*(δ*p)/(6*κ)) := mul_nonneg (by linarith) (by linarith)
  linarith

/-- At the crossing, under the region gate `(B-2 mC)/λ ≤ 1/25`, the affine plain line is the
closed form. -/
theorem plainNew_at_crossing {δ p : ℝ} (hD : tDen δ p ≠ 0) (hS : sI δ p + sP δ p ≠ 0)
    (hcap : (B - 2*mC δ p)/lambda ≤ 1/25) :
    plainNew δ p (mC δ p) = RStar δ p := by
  have hz : zS (mC δ p) = (B - 2*mC δ p)/lambda := by
    unfold zS; exact min_eq_right hcap
  rw [← (crossing_identities hD hS).2]
  unfold plainNew
  rw [hz]
  unfold aP sP
  have hl : lambda ≠ 0 := by norm_num [lambda]
  field_simp
  ring

end
end Cycle61.CountAffine
