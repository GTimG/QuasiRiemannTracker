import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace PR63Adaptation

def face00 (d t S : ℝ) := 1 - 2*d*t/3 - d*S
def face10 (d t S : ℝ) := 1 - 2*d*t/5 - 2*d/5 - d*S/5
def face01 (d t S : ℝ) := 1 - 14*d*t/23 - 2*d/23 - 14*d*S/23
def face11 (d t : ℝ) := 1 - 14*d*t/37 - 16*d/37

/-- The four exact affine faces of the saturated inverse/plain count. -/
theorem four_face_fiber {d r m t S E R : ℝ}
    (hd : 0 ≤ d) (hlen : t ≤ r+m)
    (hI : E ≤ max (1-d*r-d*S) (1-d/2-d*r/2))
    (hP : E ≤ max (1-2*d*m-d*S) (1-2*d/9-14*d*m/9))
    (h00 : face00 d t S ≤ R) (h10 : face10 d t S ≤ R)
    (h01 : face01 d t S ≤ R) (h11 : face11 d t ≤ R) : E ≤ R := by
  have hlen' := mul_le_mul_of_nonneg_left hlen hd
  unfold face00 at h00
  unfold face10 at h10
  unfold face01 at h01
  unfold face11 at h11
  rcases le_max_iff.mp hI with hi | hi
  · rcases le_max_iff.mp hP with hp | hp
    · linarith
    · linarith
  · rcases le_max_iff.mp hP with hp | hp
    · linarith
    · linarith

/-- The worst weighted amplitude is the endpoint p=1/2. -/
theorem amplitude_to_half {d p S w E b : ℝ}
    (hd : 0 ≤ d) (hp : p ≤ 1/2) (hw : w ≤ S)
    (hE : E ≤ b-2*d*p*w) : E+2*d*p*S-d*S ≤ b-d*w := by
  have hh := mul_nonneg (mul_nonneg hd (show 0 ≤ 1-2*p by linarith))
    (sub_nonneg.mpr hw)
  nlinarith only [hE,hh]

theorem inverse_half_faces {d r S E : ℝ} (hd : 0 ≤ d)
    (hE : E ≤ 1-d*r-d*min S ((1-r)/2)) :
    E ≤ max (1-d*r-d*S) (1-d/2-d*r/2) := by
  rcases le_total S ((1-r)/2) with h | h
  · rw [min_eq_left h] at hE
    exact hE.trans (le_max_left _ _)
  · rw [min_eq_right h] at hE
    have he : 1-d*r-d*((1-r)/2) = 1-d/2-d*r/2 := by ring
    rw [he] at hE
    exact hE.trans (le_max_right _ _)

theorem plain_half_faces {d m S E : ℝ} (hd : 0 ≤ d)
    (hE : E ≤ 1-2*d*m-d*min S (2*(1-2*m)/9)) :
    E ≤ max (1-2*d*m-d*S) (1-2*d/9-14*d*m/9) := by
  rcases le_total S (2*(1-2*m)/9) with h | h
  · rw [min_eq_left h] at hE
    exact hE.trans (le_max_left _ _)
  · rw [min_eq_right h] at hE
    have he : 1-2*d*m-d*(2*(1-2*m)/9)=1-2*d/9-14*d*m/9 := by ring
    rw [he] at hE
    exact hE.trans (le_max_right _ _)

def a (d : ℝ) := 5/6-d
def c00 (d S : ℝ) := (3*a d+d/3-3*a d*d*S)/(3*a d+2*d)
def c10 (d S : ℝ) := (5*a d+d/3-2*a d*d-a d*d*S)/(5*a d+2*d)
def c01 (d S : ℝ) := (23*a d+7*d/3-2*a d*d-14*a d*d*S)/(23*a d+14*d)
def c11 (d : ℝ) := (37*a d+7*d/3-16*a d*d)/(37*a d+14*d)
def fullCount (d S : ℝ) := max (max (c00 d S) (c10 d S)) (max (c01 d S) (c11 d))
def cutoff (d S : ℝ) := (fullCount d S-1/6)/a d

theorem exact_faces {d S : ℝ} (hd0 : 0 ≤ d) (hd : d < 5/6) :
    face00 d (cutoff d S) S ≤ fullCount d S ∧
    face10 d (cutoff d S) S ≤ fullCount d S ∧
    face01 d (cutoff d S) S ≤ fullCount d S ∧
    face11 d (cutoff d S) ≤ fullCount d S := by
  have ha : 0 < a d := by unfold a; linarith
  have h00 : c00 d S ≤ fullCount d S := (le_max_left _ _).trans (le_max_left _ _)
  have h10 : c10 d S ≤ fullCount d S := (le_max_right _ _).trans (le_max_left _ _)
  have h01 : c01 d S ≤ fullCount d S := (le_max_left _ _).trans (le_max_right _ _)
  have h11 : c11 d ≤ fullCount d S := (le_max_right _ _).trans (le_max_right _ _)
  have p00 : 0 < 3*a d+2*d := by positivity
  have p10 : 0 < 5*a d+2*d := by positivity
  have p01 : 0 < 23*a d+14*d := by positivity
  have p11 : 0 < 37*a d+14*d := by positivity
  have n00 := (div_le_iff₀ p00).mp h00
  have n10 := (div_le_iff₀ p10).mp h10
  have n01 := (div_le_iff₀ p01).mp h01
  have n11 := (div_le_iff₀ p11).mp h11
  have ht : a d*cutoff d S=fullCount d S-1/6 := by
    unfold cutoff
    field_simp
  have htd := congrArg (fun z : ℝ => d*z) ht
  have f00 : a d*(fullCount d S-face00 d (cutoff d S) S) ≥ 0 := by
    unfold face00
    nlinarith only [n00,htd]
  have f10 : a d*(fullCount d S-face10 d (cutoff d S) S) ≥ 0 := by
    unfold face10
    nlinarith only [n10,htd]
  have f01 : a d*(fullCount d S-face01 d (cutoff d S) S) ≥ 0 := by
    unfold face01
    nlinarith only [n01,htd]
  have f11 : a d*(fullCount d S-face11 d (cutoff d S)) ≥ 0 := by
    unfold face11
    nlinarith only [n11,htd]
  exact ⟨sub_nonneg.mp ((mul_nonneg_iff_of_pos_left ha).mp f00),
    sub_nonneg.mp ((mul_nonneg_iff_of_pos_left ha).mp f10),
    sub_nonneg.mp ((mul_nonneg_iff_of_pos_left ha).mp f01),
    sub_nonneg.mp ((mul_nonneg_iff_of_pos_left ha).mp f11)⟩

theorem weighted_short_fiber {d p S r m E : ℝ}
    (hd0 : 0 ≤ d) (hd : d < 5/6) (hp : p ≤ 1/2)
    (hlen : cutoff d S ≤ r+m)
    (hI : E ≤ 1-d*r-2*d*p*min S ((1-r)/2))
    (hP : E ≤ 1-2*d*m-2*d*p*min S (2*(1-2*m)/9)) :
    E+2*d*p*S ≤ fullCount d S+d*S := by
  have hi := inverse_half_faces hd0 (amplitude_to_half hd0 hp (min_le_left _ _) hI)
  have hm := plain_half_faces hd0 (amplitude_to_half hd0 hp (min_le_left _ _) hP)
  have hf := exact_faces (S:=S) hd0 hd
  have he := four_face_fiber hd0 hlen hi hm hf.1 hf.2.1 hf.2.2.1 hf.2.2.2
  linarith

theorem weighted_long_fiber {d p S r E : ℝ}
    (hd : d < 5/6) (hp : p ≤ 1/2) (hS : 0 ≤ S) (hd0 : 0 ≤ d)
    (hr : r ≤ cutoff d S) (hE : E ≤ 1/6+(5/6-d)*r) :
    E+2*d*p*S ≤ fullCount d S+d*S := by
  have ha : 0 < a d := by unfold a; linarith
  have ht : a d*cutoff d S=fullCount d S-1/6 := by
    unfold cutoff
    field_simp
  have hh := mul_le_mul_of_nonneg_left hr ha.le
  have hs := mul_nonneg (mul_nonneg hd0 hS) (show 0 ≤ 1-2*p by linarith)
  unfold a at hh ht
  nlinarith only [hh,ht,hE,hs]

def fourGain (a b : Fin 4 → ℝ) (S D : ℝ) : ℝ :=
  min (min (a 0*S+b 0*D) (a 1*S+b 1*D))
      (min (a 2*S+b 2*D) (a 3*S+b 3*D))

theorem fourGain_le (a b : Fin 4 → ℝ) (S D : ℝ) (i : Fin 4) :
    fourGain a b S D ≤ a i*S+b i*D := by
  fin_cases i <;> unfold fourGain
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

theorem fourGain_lower {a b : Fin 4 → ℝ} {S D t : ℝ}
    (hh : ∀ i, t ≤ a i*S+b i*D) : t ≤ fourGain a b S D := by
  unfold fourGain
  exact le_min (le_min (hh 0) (hh 1)) (le_min (hh 2) (hh 3))

theorem root_gain_lower {a b : Fin 4 → ℝ} {S D c z pad : ℝ}
    (hb0 : ∀ i, 0 ≤ b i) (hbc : ∀ i, b i ≤ c)
    (hz : 0 ≤ z) (hpad : 0 ≤ pad) :
    fourGain a b S D-6*c*z ≤ fourGain a b S (D-6*z+pad) := by
  apply fourGain_lower
  intro i
  have hh := fourGain_le a b S D i
  have hp := mul_nonneg (hb0 i) hpad
  have hc := mul_nonneg (sub_nonneg.mpr (hbc i)) hz
  nlinarith only [hh,hp,hc]


theorem one_form_width_transport {a b gamma R L Q S F : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hg : 0 ≤ gamma)
    (hR : 0 ≤ R) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hS : 0 ≤ S) (hF : 2*S ≤ F)
    (hlive : S ≤ R+L) (hfreq : F ≤ 2*R+Q) :
    min (gamma*S) (a*S+b*F) ≤ gamma*R+a*L+b*Q := by
  by_cases hr : S ≤ R
  · apply (min_le_left _ _).trans
    have hp := mul_le_mul_of_nonneg_left hr hg
    nlinarith only [hp,mul_nonneg ha hL,mul_nonneg hb hQ]
  · have hr' : R ≤ S := le_of_not_ge hr
    have hl := mul_le_mul_of_nonneg_left hlive ha
    have hq := mul_le_mul_of_nonneg_left hfreq hb
    by_cases hslope : 0 ≤ gamma-a-2*b
    · apply (min_le_right _ _).trans
      nlinarith only [hl,hq,mul_nonneg hslope hR]
    · apply (min_le_left _ _).trans
      have hsmall := mul_le_mul_of_nonpos_left hr' (le_of_not_ge hslope)
      have hf := mul_le_mul_of_nonneg_left hF hb
      nlinarith only [hl,hq,hsmall,hf]

theorem four_gain_width_transport {a b : Fin 4 → ℝ} {gamma R L Q S F : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hg : 0 ≤ gamma)
    (hR : 0 ≤ R) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hS : 0 ≤ S) (hF : 2*S ≤ F)
    (hlive : S ≤ R+L) (hfreq : F ≤ 2*R+Q) :
    min (gamma*S) (fourGain a b S F) ≤ gamma*R+fourGain a b L Q := by
  have hh : ∀ i, min (gamma*S) (fourGain a b S F)-gamma*R ≤ a i*L+b i*Q := by
    intro i
    have hm := min_le_min_left (gamma*S) (fourGain_le a b S F i)
    have hp := one_form_width_transport (ha i) (hb i) hg hR hL hQ hS hF hlive hfreq
    linarith
  have ht := fourGain_lower hh
  linarith

end PR63Adaptation
