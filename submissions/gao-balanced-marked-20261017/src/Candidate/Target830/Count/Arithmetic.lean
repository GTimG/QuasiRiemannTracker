import Candidate.Target830.Parameters
import Candidate.Target830.Count.FiniteEnvelope
import Candidate.Target836.Detector836.Antitone

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
