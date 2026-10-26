import Candidate.Cycle63.Arithmetic.Bernstein.Feedback
import Candidate.Target830.Parameters
import Candidate.Target836.Detector836.Antitone

/- Original module: Candidate.Target830.Count.FiniteEnvelope. -/
section

set_option autoImplicit false
set_option maxHeartbeats 0

namespace OAI.SevenEighths.Target830.Count
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A fixed affine count is available on an upward interval in the amplitude.
The value and its availability do not depend on the feedback parameter. -/
structure Branch where
  available : ℝ → ℝ → Prop
  value : ℝ → ℝ → ℝ
  upward : ∀ {δ p q : ℝ}, available δ p → p ≤ q → q ≤ 1/2 → available δ q
  antitone : ∀ {δ p q : ℝ}, available δ p → available δ q → p ≤ q →
    value δ q ≤ value δ p

def finiteEnvelope (base : ℝ → ℝ → ℝ → ℝ) :
    List Branch → ℝ → ℝ → ℝ → ℝ
  | [], κ, δ, p => base κ δ p
  | b :: bs, κ, δ, p =>
      if b.available δ p then min (b.value δ p) (finiteEnvelope base bs κ δ p)
      else finiteEnvelope base bs κ δ p

theorem finiteEnvelope_le_base (base : ℝ → ℝ → ℝ → ℝ)
    (bs : List Branch) (κ δ p : ℝ) : finiteEnvelope base bs κ δ p ≤ base κ δ p := by
  induction bs with
  | nil => exact le_rfl
  | cons b bs ih =>
    simp only [finiteEnvelope]
    split_ifs
    · exact (min_le_right _ _).trans ih
    · exact ih

theorem finiteEnvelope_le_branch (base : ℝ → ℝ → ℝ → ℝ)
    {b : Branch} {bs : List Branch} (hb : b ∈ bs) {κ δ p : ℝ}
    (ha : b.available δ p) : finiteEnvelope base bs κ δ p ≤ b.value δ p := by
  induction bs with
  | nil => simp at hb
  | cons c cs ih =>
    simp only [List.mem_cons] at hb
    simp only [finiteEnvelope]
    rcases hb with h | h
    · subst c
      rw [if_pos ha]
      exact min_le_left _ _
    · split_ifs
      · exact (min_le_right _ _).trans (ih h)
      · exact ih h

theorem min_one_sided_gap {c x y g : ℝ} (hg : 0 ≤ g) (hxy : x-y ≤ g) :
    min c x-min c y ≤ g := by
  rcases le_total c y with h | h
  · rw [min_eq_left h]
    have := min_le_left c x
    linarith
  · rw [min_eq_right h]
    have := min_le_right c x
    linarith

/-- Fixed minima preserve the old global one-sided feedback estimate. -/
theorem finiteEnvelope_gap (base : ℝ → ℝ → ℝ → ℝ) (bs : List Branch)
    {a κ δ p g : ℝ} (hg : 0 ≤ g) (hbase : base κ δ p-base a δ p ≤ g) :
    finiteEnvelope base bs κ δ p-finiteEnvelope base bs a δ p ≤ g := by
  induction bs with
  | nil => exact hbase
  | cons b bs ih =>
    simp only [finiteEnvelope]
    split_ifs
    · exact min_one_sided_gap hg ih
    · exact ih

theorem finiteEnvelope_antitone (base : ℝ → ℝ → ℝ → ℝ) (bs : List Branch)
    {κ δ p q : ℝ} (hpq : p ≤ q) (hq : q ≤ 1/2)
    (hbase : base κ δ q ≤ base κ δ p) :
    finiteEnvelope base bs κ δ q ≤ finiteEnvelope base bs κ δ p := by
  induction bs with
  | nil => exact hbase
  | cons b bs ih =>
    by_cases hp : b.available δ p
    · have ha := b.upward hp hpq hq
      simp only [finiteEnvelope, if_pos hp, if_pos ha]
      exact min_le_min (b.antitone hp ha hpq) ih
    · simp only [finiteEnvelope, if_neg hp]
      split_ifs
      · exact (min_le_right _ _).trans ih
      · exact ih

/-- A finite minimum is attained at the old count or an actually available
fixed count. This is the interface for abstract count-moment premises. -/
theorem finiteEnvelope_attained (base : ℝ → ℝ → ℝ → ℝ) (bs : List Branch)
    (κ δ p : ℝ) :
    finiteEnvelope base bs κ δ p=base κ δ p ∨
      ∃ b ∈ bs, b.available δ p ∧ finiteEnvelope base bs κ δ p=b.value δ p := by
  induction bs with
  | nil => exact Or.inl rfl
  | cons b bs ih =>
    by_cases ha : b.available δ p
    · simp only [finiteEnvelope, if_pos ha]
      rcases le_total (b.value δ p) (finiteEnvelope base bs κ δ p) with h | h
      · exact Or.inr ⟨b, by simp, ha, min_eq_left h⟩
      · rw [min_eq_right h]
        rcases ih with ih | ⟨c,hc,hac,heq⟩
        · exact Or.inl ih
        · exact Or.inr ⟨c, by simp [hc], hac, heq⟩
    · simp only [finiteEnvelope, if_neg ha]
      rcases ih with ih | ⟨c,hc,hac,heq⟩
      · exact Or.inl ih
      · exact Or.inr ⟨c, by simp [hc], hac, heq⟩

/-- Any common finite-family bound transfers at the selected exponent.
Analytic count-moment estimates are explicit hypotheses, not axioms. -/
theorem finiteEnvelope_bound (base : ℝ → ℝ → ℝ → ℝ) (bs : List Branch)
    {κ δ p : ℝ} {P : ℝ → Prop} (hold : P (base κ δ p))
    (hfixed : ∀ b ∈ bs, b.available δ p → P (b.value δ p)) :
    P (finiteEnvelope base bs κ δ p) := by
  rcases finiteEnvelope_attained base bs κ δ p with h | ⟨b,hb,ha,h⟩
  · rw [h]
    exact hold
  · rw [h]
    exact hfixed b hb ha

end
end OAI.SevenEighths.Target830.Count

#print axioms OAI.SevenEighths.Target830.Count.finiteEnvelope_gap
#print axioms OAI.SevenEighths.Target830.Count.finiteEnvelope_antitone
#print axioms OAI.SevenEighths.Target830.Count.finiteEnvelope_bound
end

/- Original module: Candidate.Target830.Count.Arithmetic. -/
section

set_option autoImplicit false
set_option maxHeartbeats 0

namespace OAI.SevenEighths.Target830.Count
noncomputable section

inductive Plane where
  | PR62 | PR60 | A | C | oldWeak
  deriving DecidableEq

namespace Plane
def B : Plane → ℝ
  | .PR62 => 987047/1000000
  | .PR60 => 142100527/143610000
  | .A => SourcePlane.A.B
  | .C => SourcePlane.C.B
  | .oldWeak => 1005451199/1000000000
def lambda : Plane → ℝ
  | .PR62 => 19793/5000
  | .PR60 => 19312/4787
  | .A => SourcePlane.A.lambda
  | .C => SourcePlane.C.lambda
  | .oldWeak => 44999/10000
end Plane

def reserve : ℝ := 1/10000000
def d0 : ℝ := 1/200
def mHi : ℝ := (1-6*kappa0*widthLower)/2
def affineD (L p : ℝ) : ℝ := 3-p-4*p/L
def affineA (L p : ℝ) : ℝ := 2-4*p/L
def affineC (L B p : ℝ) : ℝ := 1-2*p*B/L
def affineU (L B p : ℝ) : ℝ := (1-p)*affineC L B p
def affineJ (L δ p : ℝ) : ℝ :=
  (5/6-δ)*affineD L p+δ*(1-p)*affineA L p
def affineN (L B δ p : ℝ) : ℝ :=
  (1-δ)*affineJ L δ p+(5/6-δ)*δ*affineU L B p
def affineR (L B δ p : ℝ) : ℝ :=
  1-δ+(5/6-δ)*δ*affineU L B p/affineJ L δ p
def affineTNum (L B δ p : ℝ) : ℝ := affineJ L δ p+δ*affineU L B p
def affineRNum (L B δ p : ℝ) : ℝ :=
  affineA L p*affineTNum L B δ p+(2*p*B/L-p)*affineJ L δ p
def affineMNum (L B δ p : ℝ) : ℝ :=
  affineD L p*affineTNum L B δ p-affineRNum L B δ p

def oldCount : ℝ → ℝ → ℝ → ℝ := Cycle63.Arithmetic.Bernstein.countingR0
def oldD (p : ℝ) : ℝ := 3-p-2*p/(3*kappaStar)
def oldP (p : ℝ) : ℝ := 2*(1-p)*(1-p/(3*kappaStar))
def oldJ (δ p : ℝ) : ℝ := (5/6-δ)*oldD p+δ*oldP p
def oldN (δ p : ℝ) : ℝ := (1-δ)*oldJ δ p+δ*oldP p*(5/6-δ)/2
def oldCapacityAt (κ d : ℝ) : ℝ := min d (2*y-d)/(6*κ)
def newCapacity (d : ℝ) : ℝ :=
  min (slotClip*d) ((2*y-(2-SourcePlane.A.B)*d)/SourcePlane.A.lambda)
def rowBase (d cap δ p : ℝ) : ℝ :=
  (1+δ)/2+13*h/75-y/2-ell/2+ell*δ*p+d*(1/4-17/50)-δ*p*cap/2

theorem oldJ_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) : 0 < oldJ δ p := by
  have hV : 0 < 5/6-δ := by linarith [hδ.2]
  have hD : 0 < oldD p := by norm_num [oldD,kappaStar,theta];linarith [hp.1,hp.2]
  have hP : 0 < oldP p := by
    have h1 : 0 < 1-p := by linarith [hp.2]
    have h2 : 0 < 1-p/(3*kappaStar) := by
      norm_num [kappaStar,theta];linarith [hp.2]
    exact mul_pos (mul_pos (by norm_num) h1) h2
  unfold oldJ
  nlinarith [mul_pos hV hD,mul_nonneg hδ.1 hP.le]

theorem old_count_mul {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4))
    (hp : p ∈ Set.Icc 0 (1/2)) : oldCount kappaStar δ p*oldJ δ p=oldN δ p := by
  have hJ := oldJ_pos hδ hp
  have hD : 0 < oldD p := by norm_num [oldD,kappaStar,theta];linarith [hp.1,hp.2]
  have hc : Cycle63.Arithmetic.Bernstein.countingCoefficient kappaStar p=oldP p/oldD p := by
    rw [Cycle63.Arithmetic.Bernstein.canonical_counting_formula
      (show (7/10:ℝ) ≤ kappaStar by norm_num [kappaStar,theta])]
    rfl
  have he : (5/6-δ)+δ*(oldP p/oldD p)=oldJ δ p/oldD p := by
    unfold oldJ
    field_simp <;> ring
  unfold oldCount Cycle63.Arithmetic.Bernstein.countingR0 Cycle63.Arithmetic.Bernstein.rowDen
  rw [hc,he]
  unfold oldN
  field_simp [hD.ne',hJ.ne']
  <;> ring

theorem affine_count_mul {L B δ p : ℝ} (hJ : affineJ L δ p ≠ 0) :
    affineR L B δ p*affineJ L δ p=affineN L B δ p := by
  unfold affineR affineN
  field_simp
  <;> ring

theorem positive_polynomial_to_row {J N R d cap δ p P : ℝ}
    (hJ : 0 < J) (hN : R*J=N)
    (hi : P=J*(theta-reserve-rowBase d cap δ p)-3*d*N/4)
    (hP : 0 < P) : rowBase d cap δ p+3*d*R/4 ≤ theta-reserve := by
  have he : (theta-reserve-(rowBase d cap δ p+3*d*R/4))*J=P := by
    rw [hi,←hN]
    ring
  have hp' : 0 < (theta-reserve-(rowBase d cap δ p+3*d*R/4))*J := he.symm ▸ hP
  have := (mul_pos_iff_of_pos_right hJ).mp hp'
  linarith

end
end OAI.SevenEighths.Target830.Count
end
