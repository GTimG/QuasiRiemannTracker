/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/
import Candidate.Uneven.JointMarkedGain

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Sil.Uneven.Saturated
open PR63Adaptation

theorem cutoff_bounds {d S : ℝ} (hd0 : 0 ≤ d) (hd : d < 5/6) (hS : 0 ≤ S) :
    1 ≤ cutoff d S ∧ cutoff d S ≤ 3/2 := by
  have ha : 0 < a d := by unfold a;linarith
  have p00 : 0 < 3*a d+2*d := by positivity
  have p10 : 0 < 5*a d+2*d := by positivity
  have p01 : 0 < 23*a d+14*d := by positivity
  have p11 : 0 < 37*a d+14*d := by positivity
  have had : 0 ≤ a d*d := mul_nonneg ha.le hd0
  have hadS : 0 ≤ a d*d*S := mul_nonneg had hS
  have hal : 1/6+a d ≤ c11 d := by
    apply (le_div_iff₀ p11).mpr
    dsimp [a] at had ⊢
    nlinarith only [had]
  have hlo : 1/6+a d ≤ fullCount d S :=
    hal.trans ((le_max_right _ _).trans (le_max_right _ _))
  let H := 1/6+3/2*a d
  have h00 : c00 d S ≤ H := by
    apply (div_le_iff₀ p00).mpr
    have hid : H*(3*a d+2*d)-(3*a d+d/3-3*a d*d*S)=
        3*(a d)^2/2+3*a d*d*S := by dsimp [H,a];ring
    nlinarith only [hid,sq_nonneg (a d),hadS]
  have h10 : c10 d S ≤ H := by
    apply (div_le_iff₀ p10).mpr
    have hid : H*(5*a d+2*d)-(5*a d+d/3-2*a d*d-a d*d*S)=
        5*(a d)^2/2+a d*d*S := by dsimp [H,a];ring
    nlinarith only [hid,sq_nonneg (a d),hadS]
  have h01 : c01 d S ≤ H := by
    apply (div_le_iff₀ p01).mpr
    have hid : H*(23*a d+14*d)-(23*a d+7*d/3-2*a d*d-14*a d*d*S)=
        23*(a d)^2/2+14*a d*d*S := by dsimp [H,a];ring
    nlinarith only [hid,sq_nonneg (a d),hadS]
  have h11 : c11 d ≤ H := by
    apply (div_le_iff₀ p11).mpr
    have hid : H*(37*a d+14*d)-(37*a d+7*d/3-16*a d*d)=
        37*(a d)^2/2 := by dsimp [H,a];ring
    nlinarith only [hid,sq_nonneg (a d)]
  have hhi : fullCount d S ≤ H := max_le (max_le h00 h10) (max_le h01 h11)
  constructor
  · apply (le_div_iff₀ ha).mpr
    linarith only [hlo]
  · apply (div_le_iff₀ ha).mpr
    dsimp [H] at hhi
    linarith only [hhi]

/-- Count the amplitude and detector together with a cutoff independent of the amplitude bin. -/
theorem fiber_exponent {d p S r m E loss eps : ℝ}
    (hd0 : 31/50 ≤ d) (hd : d ≤ 3/4) (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (hS : 0 ≤ S) (heps : 0 ≤ eps)
    (hlen : cutoff d S-eps ≤ r+m) (hrcap : r ≤ cutoff d S+eps)
    (hI : E ≤ max 1 ((1+5*r)/6)-d*r+loss)
    (hP : E ≤ 1-2*d*m+loss)
    (hIM : r < 1 → E ≤ 1-d*r-2*d*p*min S ((1-r)/2)+loss)
    (hPM : m ≤ 1/2 → E ≤ 1-2*d*m-2*d*p*min S (2*(1-2*m)/9)+loss) :
    E+2*d*p*S ≤ fullCount d S+d*S+loss+eps := by
  have hdpos : 0 ≤ d := by linarith
  have hdlt : d < 5/6 := by linarith
  by_cases hr : r < 1
  · have hi := hIM hr
    have hi' : E-loss ≤ 1-d*r-2*d*p*min S ((1-r)/2) := by linarith only [hi]
    have hpi : E-loss ≤ 1-2*d*m-2*d*p*min S (2*(1-2*m)/9) := by
      by_cases hm : m ≤ 1/2
      · linarith only [hPM hm]
      · have hneg : min S (2*(1-2*m)/9) ≤ 0 := (min_le_right _ _).trans (by linarith)
        have hmul := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by positivity : 0 ≤ 2*d) hp0) hneg
        linarith only [hP,hmul]
    have hinv := inverse_half_faces hdpos
      (amplitude_to_half hdpos hp (min_le_left _ _) hi')
    have hplain := plain_half_faces hdpos
      (amplitude_to_half hdpos hp (min_le_left _ _) hpi)
    obtain ⟨h00,h10,h01,h11⟩ := exact_faces (S:=S) hdpos hdlt
    have hde : d*eps ≤ 3/4*eps := mul_le_mul_of_nonneg_right hd heps
    have f00 : face00 d (cutoff d S-eps) S ≤ fullCount d S+eps := by
      unfold face00 at *
      nlinarith only [h00,hde,heps]
    have f10 : face10 d (cutoff d S-eps) S ≤ fullCount d S+eps := by
      unfold face10 at *
      nlinarith only [h10,hde,heps]
    have f01 : face01 d (cutoff d S-eps) S ≤ fullCount d S+eps := by
      unfold face01 at *
      nlinarith only [h01,hde,heps]
    have f11 : face11 d (cutoff d S-eps) ≤ fullCount d S+eps := by
      unfold face11 at *
      nlinarith only [h11,hde,heps]
    have hh := four_face_fiber hdpos hlen hinv hplain f00 f10 f01 f11
    linarith only [hh]
  · have hr' : 1 ≤ r := le_of_not_gt hr
    rw [max_eq_right (by linarith : 1 ≤ (1+5*r)/6)] at hI
    have he : E-loss-(5/6-d)*eps ≤ 1/6+(5/6-d)*(r-eps) := by
      nlinarith only [hI]
    have hh := weighted_long_fiber hdlt hp hS hdpos
      (show r-eps ≤ cutoff d S by linarith only [hrcap]) he
    have hfee := mul_le_mul_of_nonneg_right (show 5/6-d ≤ 1 by linarith) heps
    linarith only [hh,hfee]

/-- A small strict shrink respects both inverse moment capacities, including the lower length error. -/
theorem inverse_width_gates {r S eps : ℝ}
    (hS : 0 ≤ S) (heps : 0 < eps) (hrlo : 1/2-76*eps ≤ r) (hrhi : r < 1) :
    let w := max 0 (min S ((1-r)/2)-100*eps)
    0 ≤ w ∧ w ≤ S ∧ min S ((1-r)/2)-w ≤ 100*eps ∧
      r+2*w < 1 ∧ 2*r+8*w < 3 := by
  intro w
  have hmin0 : 0 ≤ min S ((1-r)/2) := le_min hS (by linarith)
  have hminS := min_le_left S ((1-r)/2)
  have hminR := min_le_right S ((1-r)/2)
  by_cases h : 0 ≤ min S ((1-r)/2)-100*eps
  · dsimp only [w]
    rw [max_eq_right h]
    constructor
    · exact h
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  · have heq : w=0 := max_eq_left (le_of_not_ge h)
    rw [heq]
    constructor
    · norm_num
    constructor
    · exact hS
    constructor
    · linarith
    constructor <;> linarith

end Sil.Uneven.Saturated
