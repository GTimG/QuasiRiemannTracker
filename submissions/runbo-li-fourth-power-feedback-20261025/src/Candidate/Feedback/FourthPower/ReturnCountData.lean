/- Copyright (c) 2026 Sil. Apache-2.0.
Exact count data for the 0.8746935 return. The crossing algebra follows the
identities used in Hailey Collet's PR69 CountAdmission/CountDecode, instantiated
here with our own source faces and parameters; no endpoint module is imported.
No admission rectangle, analytic count estimate, or final bound is assumed. -/
import Candidate.Feedback.FourthPower.ReturnCertificate
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

namespace Candidate.Feedback.FourthPower.ReturnCountData
noncomputable section
open ReturnCertificate

inductive Role where
  | count | physical | x | y
  deriving DecidableEq

def roleFace : Role → Face
  | .count => countFace
  | .physical => physicalFace
  | .x => xFace
  | .y => yFace

structure ImprovedBranch where
  role : Role
  capped : Bool
  shift : Fin 9
  deriving DecidableEq

inductive Branch where
  | old
  | improved (data : ImprovedBranch)
  deriving DecidableEq

def ImprovedBranch.face (b : ImprovedBranch) : Face :=
  ⟨(roleFace b.role).intercept - (b.shift.val : ℝ)/4000,
    (roleFace b.role).slope, (roleFace b.role).cap⟩

def usedBranches : List Branch :=
  [.old,
   .improved ⟨.count, false, 0⟩,
   .improved ⟨.physical, true, 0⟩,
   .improved ⟨.x, false, 8⟩,
   .improved ⟨.physical, false, 0⟩,
   .improved ⟨.y, false, 0⟩,
   .improved ⟨.y, false, 3⟩]

theorem used_branches_length : usedBranches.length = 7 := rfl

theorem role_face_included (r : Role) : (roleFace r).Included := by
  cases r
  · exact countFace_included
  · exact physicalFace_included
  · exact xFace_included
  · exact yFace_included

/-- Every weakened intercept j/4000 is a subface of the same complete source. -/
theorem improved_face_included (b : ImprovedBranch) : b.face.Included := by
  rcases role_face_included b.role with ⟨h0, hc, hs, hs', hb⟩
  have hj : (0:ℝ) ≤ b.shift.val := Nat.cast_nonneg _
  refine ⟨h0, hc, hs, hs', ?_⟩
  dsimp [ImprovedBranch.face]
  nlinarith

theorem improved_slope_positive (b : ImprovedBranch) : 0 < b.face.slope := by
  cases hr : b.role <;>
    norm_num [ImprovedBranch.face, roleFace, hr, countFace, physicalFace,
      xFace, yFace, sourceSlope, physicalSlope]

def V (δ : ℝ) : ℝ := 5/6-δ
def capWidth (b : ImprovedBranch) : ℝ := b.face.cap-eta
def A (b : ImprovedBranch) (p : ℝ) : ℝ :=
  if b.capped then 2 else 2-4*p/b.face.slope
def D (b : ImprovedBranch) (p : ℝ) : ℝ :=
  if b.capped then 3-p else 3-p-4*p/b.face.slope
def Z (b : ImprovedBranch) (p : ℝ) : ℝ :=
  if b.capped then 2*p*capWidth b else 2*p*b.face.intercept/b.face.slope
def C0 (b : ImprovedBranch) (p : ℝ) : ℝ := 1-Z b p
def U (b : ImprovedBranch) (p : ℝ) : ℝ := (1-p)*C0 b p
def J (b : ImprovedBranch) (δ p : ℝ) : ℝ :=
  V δ*D b p+δ*(1-p)*A b p
def N (b : ImprovedBranch) (δ p : ℝ) : ℝ :=
  (1-δ)*J b δ p+V δ*δ*U b p
def T (b : ImprovedBranch) (δ p : ℝ) : ℝ := J b δ p+δ*U b p
def RN (b : ImprovedBranch) (δ p : ℝ) : ℝ :=
  A b p*T b δ p+(Z b p-p)*J b δ p
def MN (b : ImprovedBranch) (δ p : ℝ) : ℝ := D b p*T b δ p-RN b δ p
def DJ (b : ImprovedBranch) (δ p : ℝ) : ℝ := D b p*J b δ p

def APrime (b : ImprovedBranch) : ℝ := if b.capped then 0 else -4/b.face.slope
def DPrime (b : ImprovedBranch) : ℝ := if b.capped then -1 else -1-4/b.face.slope
def CPrime (b : ImprovedBranch) : ℝ :=
  if b.capped then -2*capWidth b else -2*b.face.intercept/b.face.slope
def UPrime (b : ImprovedBranch) (p : ℝ) : ℝ :=
  -C0 b p+(1-p)*CPrime b
def JPrime (b : ImprovedBranch) (δ p : ℝ) : ℝ :=
  V δ*DPrime b+δ*(-A b p+(1-p)*APrime b)

def lowerM (b : ImprovedBranch) : ℝ :=
  if b.capped then mMinus+eta else
    max (mMinus+eta) ((b.face.intercept-b.face.slope*capWidth b)/2+eta)
def upperM (b : ImprovedBranch) : ℝ :=
  min (min (mPlus-eta) (mHigh-eta))
    (if b.capped then (b.face.intercept-b.face.slope*capWidth b)/2-eta
      else (b.face.intercept-b.face.slope*(sMinus+eta))/2-eta)

/-- The first fourteen guards are common. The last is the capped-width guard;
for an affine branch it is the positive constant one. -/
def admissionGuard (b : ImprovedBranch) (δ p : ℝ) (i : Fin 15) : ℝ :=
  match i.val with
  | 0 => D b p
  | 1 => A b p
  | 2 => C0 b p
  | 3 => J b δ p
  | 4 => T b δ p-J b δ p
  | 5 => (12499/10000)*J b δ p-T b δ p
  | 6 => RN b δ p-(23/37)*DJ b δ p
  | 7 => DJ b δ p-RN b δ p
  | 8 => MN b δ p-lowerM b*DJ b δ p
  | 9 => upperM b*DJ b δ p-MN b δ p
  | 10 => N b δ p-(1-2*δ*mHigh-2*δ*p*sMinus)*J b δ p
  | 11 => U b p*JPrime b δ p-UPrime b p*J b δ p
  | 12 => mPlus-mHigh-eta
  | 13 => b.face.intercept-2*mHigh-b.face.slope*(sMinus+eta)-2*eta
  | _ => if b.capped then (capWidth b-sMinus-eta)*DJ b δ p else 1

def Admitted (b : ImprovedBranch) (δ p : ℝ) : Prop :=
  ∀ i : Fin 15, 0 < admissionGuard b δ p i

def cutoff (b : ImprovedBranch) (δ p : ℝ) : ℝ := T b δ p/J b δ p
def inverse (b : ImprovedBranch) (δ p : ℝ) : ℝ := RN b δ p/DJ b δ p
def plain (b : ImprovedBranch) (δ p : ℝ) : ℝ := MN b δ p/DJ b δ p
def count (b : ImprovedBranch) (δ p : ℝ) : ℝ := N b δ p/J b δ p
def plainWidth (b : ImprovedBranch) (m : ℝ) : ℝ :=
  min (capWidth b) ((b.face.intercept-2*m)/b.face.slope)

def oldD (k p : ℝ) : ℝ := 3-p-2*p/(3*k)
def oldC (k p : ℝ) : ℝ := 2*(1-p)*(1-p/(3*k))
def oldJ (k δ p : ℝ) : ℝ := V δ*oldD k p+δ*oldC k p
def oldN (k δ p : ℝ) : ℝ := (1-δ)*oldJ k δ p+δ*oldC k p*V δ/2

def countJ (b : Branch) (k δ p : ℝ) : ℝ :=
  match b with | .old => oldJ k δ p | .improved b => J b δ p
def countN (b : Branch) (k δ p : ℝ) : ℝ :=
  match b with | .old => oldN k δ p | .improved b => N b δ p

theorem D_identity (b : ImprovedBranch) (p : ℝ) : D b p = 1-p+A b p := by
  cases hc : b.capped <;> simp [D, A, hc] <;> ring

/-- Exact quadratic Taylor identity, validating the numerator derivative data. -/
theorem U_increment (b : ImprovedBranch) (p v : ℝ) :
    U b (p+v) = U b p+v*UPrime b p-v^2*CPrime b := by
  cases hc : b.capped <;> simp [U, UPrime, C0, CPrime, Z, hc] <;> ring

/-- Exact quadratic Taylor identity, validating the denominator derivative data. -/
theorem J_increment (b : ImprovedBranch) (δ p v : ℝ) :
    J b δ (p+v) = J b δ p+v*JPrime b δ p-δ*v^2*APrime b := by
  cases hc : b.capped <;> simp [J, JPrime, D, DPrime, A, APrime, hc] <;> ring

theorem old_denominator_positive {k δ p : ℝ}
    (hk : 7/10 ≤ k) (hδ : 0 ≤ δ) (hδ' : δ ≤ 3/4)
    (_hp : 0 ≤ p) (hp' : p ≤ 1/2) : 0 < oldJ k δ p := by
  have hk0 : 0 < 3*k := by linarith
  have hr : p/(3*k) ≤ 1/2 := (div_le_iff₀ hk0).2 (by linarith)
  have hD : 0 < oldD k p := by
    have he : 2*p/(3*k) = 2*(p/(3*k)) := by ring
    dsimp [oldD]
    rw [he]
    linarith
  have hC : 0 ≤ oldC k p :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
  have hV : 0 < V δ := by dsimp [V]; linarith
  exact add_pos_of_pos_of_nonneg (mul_pos hV hD) (mul_nonneg hδ hC)

theorem old_count_formula {k δ p : ℝ} (hJ : oldJ k δ p ≠ 0) :
    oldN k δ p/oldJ k δ p = 1-δ+δ*oldC k p*V δ/(2*oldJ k δ p) := by
  dsimp [oldN]
  field_simp [hJ]

theorem improved_denominator_positive (b : ImprovedBranch) {δ p : ℝ}
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 3/4) (hp : p ≤ 1)
    (hD : 0 < D b p) (hA : 0 ≤ A b p) : 0 < J b δ p := by
  have hV : 0 < V δ := by dsimp [V]; linarith
  exact add_pos_of_pos_of_nonneg (mul_pos hV hD)
    (mul_nonneg (mul_nonneg hδ (by linarith)) hA)

theorem crossing_algebra {δ p D A Z U J : ℝ}
    (hD : D = 1-p+A) (hU : U = (1-p)*(1-Z))
    (hJ : J = (5/6-δ)*D+δ*(1-p)*A) (hD0 : D ≠ 0) (hJ0 : J ≠ 0) :
    1-δ*(p+(1-p)*((A*(J+δ*U)+(Z-p)*J)/(D*J))) =
      ((1-δ)*J+(5/6-δ)*δ*U)/J := by
  field_simp [hD0, hJ0]
  rw [hJ, hD, hU]
  ring

theorem inverse_crossing (b : ImprovedBranch) {δ p : ℝ}
    (hD : 0 < D b p) (hJ : 0 < J b δ p) :
    1-δ*(p+(1-p)*inverse b δ p) = count b δ p := by
  unfold inverse count RN DJ T N
  exact crossing_algebra (D_identity b p) rfl rfl hD.ne' hJ.ne'

theorem long_crossing (b : ImprovedBranch) {δ p : ℝ} (hJ : 0 < J b δ p) :
    1/6+V δ*cutoff b δ p = count b δ p := by
  unfold cutoff count T N
  field_simp [hJ.ne']
  dsimp [V]
  ring

theorem lengths (b : ImprovedBranch) {δ p : ℝ}
    (hD : 0 < D b p) (hJ : 0 < J b δ p) :
    inverse b δ p+plain b δ p = cutoff b δ p := by
  unfold inverse plain cutoff MN DJ
  field_simp [hD.ne', hJ.ne']
  ring

theorem linear_plain_crossing (b : ImprovedBranch) {δ p : ℝ}
    (hD : 0 < D b p) (hJ : 0 < J b δ p) :
    1-δ*A b p*plain b δ p-δ*Z b p = count b δ p := by
  rw [← inverse_crossing b hD hJ]
  have hrel : D b p*inverse b δ p = A b p*cutoff b δ p+Z b p-p := by
    unfold inverse cutoff RN DJ
    field_simp [hD.ne', hJ.ne']
    ring
  have hsum := lengths b hD hJ
  rw [D_identity, ← hsum] at hrel
  have hm := congrArg (fun z : ℝ => δ*z) hrel
  nlinarith [hm]

theorem admitted_witness_ranges (b : ImprovedBranch) {δ p : ℝ}
    (hg : Admitted b δ p) :
    0 < D b p ∧ 0 < J b δ p ∧
    1 < cutoff b δ p ∧ cutoff b δ p < 12499/10000 ∧
    23/37 < inverse b δ p ∧ inverse b δ p < 1 ∧
    lowerM b < plain b δ p ∧ plain b δ p < upperM b := by
  have hD : 0 < D b p := by simpa only [admissionGuard] using (hg ⟨0, by decide⟩)
  have hJ : 0 < J b δ p := by simpa only [admissionGuard] using (hg ⟨3, by decide⟩)
  have ht0 : 0 < T b δ p-J b δ p := by simpa only [admissionGuard] using (hg ⟨4, by decide⟩)
  have ht1 : 0 < (12499/10000)*J b δ p-T b δ p := by simpa only [admissionGuard] using (hg ⟨5, by decide⟩)
  have hr0 : 0 < RN b δ p-(23/37)*DJ b δ p := by simpa only [admissionGuard] using (hg ⟨6, by decide⟩)
  have hr1 : 0 < DJ b δ p-RN b δ p := by simpa only [admissionGuard] using (hg ⟨7, by decide⟩)
  have hm0 : 0 < MN b δ p-lowerM b*DJ b δ p := by simpa only [admissionGuard] using (hg ⟨8, by decide⟩)
  have hm1 : 0 < upperM b*DJ b δ p-MN b δ p := by simpa only [admissionGuard] using (hg ⟨9, by decide⟩)
  have hDJ : 0 < DJ b δ p := mul_pos hD hJ
  dsimp only [cutoff, inverse, plain]
  refine ⟨hD, hJ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (lt_div_iff₀ hJ).2 (by linarith)
  · exact (div_lt_iff₀ hJ).2 (by linarith)
  · exact (lt_div_iff₀ hDJ).2 (by linarith)
  · exact (div_lt_iff₀ hDJ).2 (by linarith)
  · exact (lt_div_iff₀ hDJ).2 (by linarith)
  · exact (div_lt_iff₀ hDJ).2 (by linarith)

/-- The crossing lies on the correct side of the affine/cap switch. -/
theorem admitted_plain_width (b : ImprovedBranch) {δ p : ℝ}
    (hg : Admitted b δ p) :
    plainWidth b (plain b δ p) =
      if b.capped then capWidth b else (b.face.intercept-2*plain b δ p)/b.face.slope := by
  obtain ⟨_, _, _, _, _, _, hmlo, hmhi⟩ := admitted_witness_ranges b hg
  have hL := improved_slope_positive b
  have heta : 0 < eta := by norm_num [eta]
  cases hc : b.capped
  · have hlo : (b.face.intercept-b.face.slope*capWidth b)/2+eta ≤ lowerM b := by
      simp [lowerM, hc]
    have hz : (b.face.intercept-2*plain b δ p)/b.face.slope ≤ capWidth b :=
      (div_le_iff₀ hL).2 (by nlinarith)
    simpa [plainWidth, hc] using min_eq_right hz
  · have hhi : upperM b ≤ (b.face.intercept-b.face.slope*capWidth b)/2-eta := by
      simp [upperM, hc]
    have hz : capWidth b ≤ (b.face.intercept-2*plain b δ p)/b.face.slope :=
      (le_div_iff₀ hL).2 (by nlinarith)
    simpa [plainWidth, hc] using min_eq_left hz

theorem plain_crossing (b : ImprovedBranch) {δ p : ℝ}
    (hg : Admitted b δ p) :
    1-2*δ*plain b δ p-2*δ*p*plainWidth b (plain b δ p) = count b δ p := by
  have hr := admitted_witness_ranges b hg
  have he := linear_plain_crossing b hr.1 hr.2.1
  rw [admitted_plain_width b hg]
  calc
    _ = 1-δ*A b p*plain b δ p-δ*Z b p := by
      cases hc : b.capped <;> simp [A, Z, hc] <;> ring
    _ = count b δ p := he

theorem admitted_tail (b : ImprovedBranch) {δ p : ℝ}
    (hg : Admitted b δ p) :
    1-2*δ*mHigh-2*δ*p*sMinus < count b δ p := by
  have hJ := (admitted_witness_ranges b hg).2.1
  have htail : 0 < N b δ p-(1-2*δ*mHigh-2*δ*p*sMinus)*J b δ p := by simpa only [admissionGuard] using (hg ⟨10, by decide⟩)
  exact (lt_div_iff₀ hJ).2 (by linarith)

/-- The determinant guard has the correct sign for a quotient derivative.
This is an algebraic identity; no differentiability claim is hidden here. -/
theorem quotient_derivative_sign (b : ImprovedBranch) {δ p : ℝ}
    (hJ : 0 < J b δ p)
    (hguard : 0 < U b p*JPrime b δ p-UPrime b p*J b δ p) :
    (UPrime b p*J b δ p-U b p*JPrime b δ p)/(J b δ p)^2 < 0 := by
  apply div_neg_of_neg_of_pos
  · linarith
  · exact sq_pos_of_pos hJ

def clearedReturn (b : Branch) (d C δ p : ℝ) : ℝ :=
  countJ b kappa δ p*(theta-reserve-returnValue d C δ p 0)-
    (3/4)*d*countN b kappa δ p

theorem cleared_return_sound (b : Branch) {d C δ p R : ℝ}
    (hd : 0 ≤ d) (hJ : 0 < countJ b kappa δ p)
    (hR : R ≤ countN b kappa δ p/countJ b kappa δ p)
    (hf : 0 ≤ clearedReturn b d C δ p) :
    returnValue d C δ p R ≤ theta-reserve :=
  return_from_cleared hd hJ hR hf

end
end Candidate.Feedback.FourthPower.ReturnCountData
