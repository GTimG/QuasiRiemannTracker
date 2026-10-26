/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Candidate.Uneven.SaturatedMonotone


set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.Saturated
open PR63Adaptation

def slope (d : ℝ) : Fin 4 → ℝ :=
  ![d*(5-6*d)/(5-2*d), d*(5-6*d)/(25-18*d), 14*d*(5-6*d)/(115-54*d), 0]
def offset (d : ℝ) : Fin 4 → ℝ :=
  ![0, 2*d*(5-6*d)^2/(3*(5-2*d)*(25-18*d)),
    2*d*(5-6*d)^2/(3*(5-2*d)*(115-54*d)),
    16*d*(5-6*d)^2/(3*(5-2*d)*(185-138*d))]
def physicalGain (d S D : ℝ) : ℝ := fourGain (slope d) (offset d) S D

theorem coefficient_bounds {d : ℝ} (hd0 : 31/50≤ d) (hd : d≤3/4) :
    (∀i,0 ≤ slope d i) ∧ (∀i,0 ≤ offset d i) ∧ (∀i,offset d i≤3/200) := by
  have h0 : 0≤ d := by linarith
  have h1 : 0≤5-6*d := by linarith
  have h2 : 0<5-2*d := by linarith
  have h3 : 0<25-18*d := by linarith
  have h4 : 0<115-54*d := by linarith
  have h5 : 0<185-138*d := by linarith
  have hlo : 0≤ d-31/50 := by linarith
  have hhi : 0≤3/4-d := by linarith
  constructor
  · intro i
    fin_cases i <;> dsimp [slope] <;> positivity
  constructor
  · intro i
    fin_cases i <;> dsimp [offset] <;> positivity
  intro i
  fin_cases i
  · norm_num [offset]
  · have hp : 0≤(1125+(-14400*(d^3))+(-11260*d)+(24324*(d^2))) := by
      have he : (1125+(-14400*(d^3))+(-11260*d)+(24324*(d^2)))=(62022400/2197:ℝ)*(d-31/50)^0*(3/4-d)^3+(484505600/2197:ℝ)*(d-31/50)^1*(3/4-d)^2+(741370000/2197:ℝ)*(d-31/50)^2*(3/4-d)^1+(287250000/2197:ℝ)*(d-31/50)^3*(3/4-d)^0 := by ring
      rw [he]
      positivity
    norm_num [offset]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hp]
  · have hp : 0≤(5175+(-14500*d)+(-14400*(d^3))+(24972*(d^2))) := by
      have he : (5175+(-14500*d)+(-14400*(d^3))+(24972*(d^2)))=(180947200/169:ℝ)*(d-31/50)^0*(3/4-d)^3+(541433600/169:ℝ)*(d-31/50)^1*(3/4-d)^2+(537670000/169:ℝ)*(d-31/50)^2*(3/4-d)^1+(174750000/169:ℝ)*(d-31/50)^3*(3/4-d)^0 := by ring
      rw [he]
      positivity
    norm_num [offset]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hp]
  · have hp : 0≤(8325+(-115200*(d^3))+(-89540*d)+(194484*(d^2))) := by
      have he : (8325+(-115200*(d^3))+(-89540*d)+(194484*(d^2)))=(114464000/2197:ℝ)*(d-31/50)^0*(3/4-d)^3+(2783689600/2197:ℝ)*(d-31/50)^1*(3/4-d)^2+(4889570000/2197:ℝ)*(d-31/50)^2*(3/4-d)^1+(1967250000/2197:ℝ)*(d-31/50)^3*(3/4-d)^0 := by ring
      rw [he]
      positivity
    norm_num [offset]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hp]

theorem max_sub (r x y : ℝ) : r-max x y=min (r-x) (r-y) := by
  rcases le_total x y with h|h
  · rw [max_eq_right h,min_eq_right (by linarith)]
  · rw [max_eq_left h,min_eq_left (by linarith)]

theorem face_identities {d : ℝ} (hd0 : 0≤ d) (hd : d<5/6) (S : ℝ) :
    rho d-c00 d S=slope d 0*S+offset d 0 ∧
    rho d-c10 d S=slope d 1*S+offset d 1 ∧
    rho d-c01 d S=slope d 2*S+offset d 2 ∧
    rho d-c11 d=slope d 3*S+offset d 3 := by
  have hp2 : 0<5-2*d := by linarith
  have hp3 : 0<25-18*d := by linarith
  have hp4 : 0<115-54*d := by linarith
  have hp5 : 0<185-138*d := by linarith
  have h2 : 5-2*d≠0 := by linarith
  have h3 : 25-18*d≠0 := by linarith
  have h4 : 115-54*d≠0 := by linarith
  have h5 : 185-138*d≠0 := by linarith
  have e0 : 3*a d+2*d=(5-2*d)/2 := by unfold a;ring
  have e1 : 5*a d+2*d=(25-18*d)/6 := by unfold a;ring
  have e2 : 23*a d+14*d=(115-54*d)/6 := by unfold a;ring
  have e3 : 37*a d+14*d=(185-138*d)/6 := by unfold a;ring
  simp only [c00,c10,c01,c11,e0,e1,e2,e3]
  dsimp [slope,offset,rho,a]
  constructor
  · field_simp (disch := first | linarith | positivity) <;> ring
  constructor
  · field_simp (disch := first | linarith | positivity) <;> ring
  constructor
  · field_simp (disch := first | linarith | positivity) <;> ring
  · field_simp (disch := first | linarith | positivity) <;> ring

theorem physicalGain_rescale {d S D : ℝ} (hd0 : 0≤ d) (hd : d<5/6) (hD : 0<D) :
    D*(rho d-fullCount d (S/D))=physicalGain d S D := by
  obtain ⟨e0,e1,e2,e3⟩ := face_identities hd0 hd (S/D)
  have hc : D*(S/D)=S := mul_div_cancel₀ _ hD.ne'
  have he (i : Fin 4) : D*(slope d i*(S/D)+offset d i)=slope d i*S+offset d i*D := by
    linear_combination slope d i*hc
  simp only [fullCount,max_sub,mul_min_of_nonneg _ _ hD.le,e0,e1,e2,e3,he,physicalGain,fourGain]

theorem physicalGain_le_cap {d S D : ℝ} (hd0 : 31/50≤ d) (hd : d≤3/4) (hD : 0≤ D) :
    physicalGain d S D≤(3/200)*D := by
  have hh := fourGain_le (slope d) (offset d) S D 3
  have hb := mul_le_mul_of_nonneg_right ((coefficient_bounds hd0 hd).2.2 3) hD
  norm_num [slope] at hh
  exact hh.trans hb

theorem physicalGain_root {d S D q pad : ℝ}
    (hd0 : 31/50≤ d) (hd : d≤3/4) (hD : 0≤ D) (hq : q≤1) (hpad : 0≤ pad) :
    physicalGain d S D-(3/200)*D*(1-q)≤ physicalGain d S (D*q+pad) := by
  have hh := root_gain_lower (a:=slope d) (b:=offset d) (S:=S) (D:=D)
    (c:=3/200) (z:=D*(1-q)/6) (pad:=pad)
    (coefficient_bounds hd0 hd).2.1 (coefficient_bounds hd0 hd).2.2
    (by positivity) hpad
  convert hh using 1 <;> unfold physicalGain <;> congr 1 <;> ring

end Sil.Uneven.Saturated
