import Candidate.Target836.Target836Geometry
import Candidate.Target836.Detector836.Masked

set_option autoImplicit false
namespace Target836.EndpointArithmetic
noncomputable section
open Target836.Arithmetic

def reserve : ℝ := 1/10000000
def oldCapacity (d : ℝ) : ℝ := min d (2*y-d)/(6*kappaStar)
def newCapacity (d : ℝ) : ℝ := (2*y-(2-B)*d)/lambda
def rowBase (d C δ p : ℝ) : ℝ :=
  (1+δ)/2+13*h/75-y/2-ell/2+ell*δ*p+d*(1/4-17/50)-δ*p*C/2
def rowAt (κ d C δ p : ℝ) : ℝ := rowBase d C δ p+3*d*Detector836.count κ δ p/4
def oldExponent (d δ p : ℝ) : ℝ := rowAt kappaStar d (oldCapacity d) δ p
def newExponent (d δ p : ℝ) : ℝ := rowAt kappaStar d (newCapacity d) δ p

def oldD (p : ℝ) : ℝ := 3-p-2*p/(3*kappaStar)
def oldP (p : ℝ) : ℝ := 2*(1-p)*(1-p/(3*kappaStar))
def oldJ (δ p : ℝ) : ℝ := (5/6-δ)*oldD p+δ*oldP p
def oldN (δ p : ℝ) : ℝ := (1-δ)*oldJ δ p+δ*oldP p*(5/6-δ)/2
def newN (δ p : ℝ) : ℝ := (1-δ)*Detector836.JN δ p+
  (5/6-δ)*δ*(1-p)*Detector836.cN p
def acceptedN (δ p : ℝ) : ℝ := (1-δ)*DetectorAffine.JN δ p+
  (5/6-δ)*δ*(1-p)*DetectorAffine.cN p

theorem kappaStar_eq_detector : kappaStar = Detector836.kStar := by
  norm_num [kappaStar,Detector836.kStar]
theorem lambda_eq_detector : lambda = Detector836.lam := by
  norm_num [lambda,Detector836.lam]
theorem B_eq_detector : B = Detector836.Bc := by norm_num [B,Detector836.Bc]

theorem oldD_pos {p : ℝ} (hp : p ∈ Set.Icc 0 (1/2)) : 0 < oldD p := by
  norm_num [oldD,kappaStar]
  linarith [hp.1,hp.2]
theorem oldP_pos {p : ℝ} (hp : p ∈ Set.Icc 0 (1/2)) : 0 < oldP p := by
  have h1 : 0 < 1-p := by linarith [hp.2]
  have h2 : 0 < 1-p/(3*kappaStar) := by norm_num [kappaStar];linarith [hp.2]
  unfold oldP
  positivity
theorem oldJ_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    0 < oldJ δ p := by
  have hV : 0 < 5/6-δ := by linarith [hδ.2]
  have hD := oldD_pos hp
  have hP := oldP_pos hp
  have hterm : 0 ≤ δ*oldP p := mul_nonneg hδ.1 hP.le
  unfold oldJ
  nlinarith [mul_pos hV hD]

theorem old_count_mul {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    Cycle63.Arithmetic.Bernstein.countingR0 kappaStar δ p*oldJ δ p = oldN δ p := by
  have hJ := oldJ_pos hδ hp
  have hD := oldD_pos hp
  have hcoef : Cycle63.Arithmetic.Bernstein.countingCoefficient kappaStar p = oldP p/oldD p := by
    rw [Cycle63.Arithmetic.Bernstein.canonical_counting_formula
      (show 7/10 ≤ kappaStar by norm_num [kappaStar])]
    rfl
  have hden : (5/6-δ)+δ*(oldP p/oldD p)=oldJ δ p/oldD p := by
    unfold oldJ
    field_simp <;> ring
  calc
    _ = (1-δ+δ*(oldP p/oldD p)*(5/6-δ)/(2*(oldJ δ p/oldD p)))*oldJ δ p := by
      unfold Cycle63.Arithmetic.Bernstein.countingR0 Cycle63.Arithmetic.Bernstein.rowDen
      rw [hcoef,hden]
    _ = (1-δ)*oldJ δ p+δ*oldP p*(5/6-δ)/2 := by
      field_simp [hD.ne',hJ.ne']
      <;> ring
    _ = oldN δ p := rfl

theorem new_count_mul {δ p : ℝ} (h : Detector836.InRegion δ p) :
    Detector836.RNew δ p*Detector836.JN δ p = newN δ p := by
  have hh := Detector836.region_RNew_mul h
  unfold newN
  nlinarith
theorem accepted_count_mul {δ p : ℝ} (h : Detector836.InAcceptedRegion δ p) :
    DetectorAffine.RNew δ p*DetectorAffine.JN δ p = acceptedN δ p := by
  have hh := DetectorAffine.region_RNew_mul (Detector836.accepted_region_subset h)
  unfold acceptedN
  nlinarith

theorem positive_polynomial_to_row {J N R d C δ p P : ℝ}
    (hJ : 0 < J) (hN : R*J=N)
    (hidentity : P=J*(theta-reserve-rowBase d C δ p)-3*d*N/4)
    (hP : 0 < P) : rowBase d C δ p+3*d*R/4 ≤ theta-reserve := by
  have hh : (theta-reserve-(rowBase d C δ p+3*d*R/4))*J=P := by
    rw [hidentity,←hN]
    ring
  have hpos : 0 < (theta-reserve-(rowBase d C δ p+3*d*R/4))*J := hh.symm ▸ hP
  have := (mul_pos_iff_of_pos_right hJ).mp hpos
  linarith

theorem old_region_cover {δ p : ℝ} (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2))
    (hn : ¬Detector836.InRegion δ p) (ha : ¬Detector836.InAcceptedRegion δ p) :
    (δ ∈ Set.Icc 0 (89/200) ∧ p ∈ Set.Icc 0 (1/2)) ∨
    (δ ∈ Set.Icc (49/100) (3/4) ∧ p ∈ Set.Icc 0 (1/2)) ∨
    (δ ∈ Set.Icc (89/200) (451/1000) ∧ p ∈ Set.Icc 0 (199/400)) ∨
    (δ ∈ Set.Icc (451/1000) (49/100) ∧ p ∈ Set.Icc 0 (49/100)) := by
  by_cases h0 : δ ≤ 89/200
  · exact Or.inl ⟨⟨hδ.1,h0⟩,hp⟩
  by_cases h1 : 49/100 ≤ δ
  · exact Or.inr (Or.inl ⟨⟨h1,hδ.2⟩,hp⟩)
  by_cases h2 : δ ≤ 451/1000
  · apply Or.inr;apply Or.inr;apply Or.inl
    have hp' : p ≤ 199/400 := by
      by_contra hbad
      apply ha
      exact ⟨by linarith,h2,by linarith,hp.2⟩
    exact ⟨⟨by linarith,h2⟩,⟨hp.1,hp'⟩⟩
  · apply Or.inr;apply Or.inr;apply Or.inr
    have hp' : p ≤ 49/100 := by
      by_contra hbad
      apply hn
      exact ⟨by linarith,by linarith,by linarith,hp.2⟩
    exact ⟨⟨by linarith,by linarith⟩,⟨hp.1,hp'⟩⟩

end
end Target836.EndpointArithmetic

#print axioms Target836.EndpointArithmetic.old_count_mul
#print axioms Target836.EndpointArithmetic.positive_polynomial_to_row
