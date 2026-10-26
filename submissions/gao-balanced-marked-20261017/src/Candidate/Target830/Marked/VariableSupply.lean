import Candidate.Target830.Kernel.ExactMarkedGain
import Mathlib.Tactic

/-! Variable-width marked detector count.  The analytic moment bounds
remain explicit hypotheses.  The resulting saving pays surviving physical
slot width at the same rate as the allocation ledger pays removed width. -/

namespace Marked830.VariableSupply
noncomputable section

def cutoff (d p s : ℝ) : ℝ := (5-12*d*p*s)/(5-2*d)
def count (d p s : ℝ) : ℝ := 1/6+(5/6-d)*cutoff d p s
def density (d : ℝ) : ℝ := 1-10*d/(3*(5-2*d))
def gain (d p s : ℝ) : ℝ := d*p*s*(10-12*d)/(5-2*d)
def phi (d : ℝ) : ℝ := d*(5-6*d)/(5-2*d)

def cap (d : ℝ) : ℝ := (1-1/1000000)*9*(5-6*d)/(380-240*d)
def plainCap (d : ℝ) : ℝ := 4*cap d/9
def gap : ℝ := 1/42000000
def inverseThreshold (d : ℝ) : ℝ := 1-2*cap d-gap
def plainThreshold (d : ℝ) : ℝ := inverseThreshold d/2
def inverseWidth (d S : ℝ) : ℝ := min S (cap d)
def plainWidth (d S : ℝ) : ℝ := min S (plainCap d)
def chosenWidth (d S : ℝ) : ℝ := (2*inverseWidth d S+plainWidth d S)/3

theorem count_identity {d p s : ℝ} (hd : d ≤ 7/10) :
    count d p s = 1-2*d/3*cutoff d p s-2*d*p*s := by
  have hn : 5-2*d ≠ 0 := by linarith
  apply mul_left_cancel₀ hn
  unfold count cutoff
  field_simp [hn]
  <;> ring

theorem gain_identity {d p s : ℝ} (hd : d ≤ 7/10) :
    density d-count d p s = gain d p s := by
  have hn : 5-2*d ≠ 0 := by linarith
  apply mul_left_cancel₀ hn
  unfold density count cutoff gain
  field_simp [hn]
  <;> ring

theorem cap_bounds {d : ℝ} (hd0 : 31/50 ≤ d) (hd : d ≤ 7/10) :
    0 < cap d ∧ cap d ≤ 9/76 := by
  have hden : 0 < 380-240*d := by linarith
  unfold cap
  constructor
  · exact div_pos (by nlinarith) hden
  · apply (div_le_iff₀ hden).mpr
    nlinarith

theorem plainCap_nonneg {d : ℝ} (hd0 : 31/50 ≤ d) (hd : d ≤ 7/10) :
    0 ≤ plainCap d := by
  unfold plainCap
  have hc := (cap_bounds hd0 hd).1
  linarith

theorem inverseWidth_bounds {d S : ℝ} (hd0 : 31/50 ≤ d) (hd : d ≤ 7/10)
    (hS : 0 ≤ S) :
    0 ≤ inverseWidth d S ∧ inverseWidth d S ≤ S ∧ inverseWidth d S ≤ cap d := by
  exact ⟨le_min hS (cap_bounds hd0 hd).1.le,min_le_left _ _,min_le_right _ _⟩

theorem plainWidth_bounds {d S : ℝ} (hd0 : 31/50 ≤ d) (hd : d ≤ 7/10)
    (hS : 0 ≤ S) :
    0 ≤ plainWidth d S ∧ plainWidth d S ≤ S ∧ plainWidth d S ≤ plainCap d := by
  exact ⟨le_min hS (plainCap_nonneg hd0 hd),min_le_left _ _,min_le_right _ _⟩

theorem chosenWidth_bounds {d S : ℝ} (hd0 : 31/50 ≤ d) (hd : d ≤ 7/10)
    (hS : 0 ≤ S) :
    0 ≤ chosenWidth d S ∧ chosenWidth d S ≤ S ∧ chosenWidth d S ≤ 11/114 := by
  have hi := inverseWidth_bounds hd0 hd hS
  have hp := plainWidth_bounds hd0 hd hS
  have hc := (cap_bounds hd0 hd).2
  dsimp [chosenWidth]
  dsimp [plainCap] at hp
  constructor
  · linarith [hi.1,hp.1]
  constructor <;> linarith

theorem chosenWidth_pos {d S : ℝ} (hd0 : 31/50 ≤ d) (hd : d ≤ 7/10)
    (hS : 0 < S) : 0 < chosenWidth d S := by
  have hi : 0 < inverseWidth d S := lt_min hS (cap_bounds hd0 hd).1
  have hpc : 0 < plainCap d := by
    unfold plainCap
    have hc := (cap_bounds hd0 hd).1
    linarith
  have hp : 0 < plainWidth d S := lt_min hS hpc
  dsimp [chosenWidth]
  positivity

theorem chosenWidth_mono {d S T : ℝ} (h : S ≤ T) :
    chosenWidth d S ≤ chosenWidth d T := by
  have hi := min_le_min_right (cap d) h
  have hp := min_le_min_right (plainCap d) h
  dsimp [chosenWidth,inverseWidth,plainWidth]
  linarith

theorem cutoff_bounds {d p s : ℝ} (hd0 : 31/50 ≤ d) (hd : d ≤ 7/10)
    (hp0 : 0 ≤ p) (hp : p ≤ 1/2) (hs0 : 0 ≤ s) (hs : s ≤ 11/114) :
    1 ≤ cutoff d p s ∧ cutoff d p s ≤ 3/2 := by
  have hden : 0 < 5-2*d := by linarith
  have hdpos : 0 ≤ d := by linarith
  have hps : p*s ≤ 11/228 := by nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hs)]
  have hps0 : 0 ≤ p*s := mul_nonneg hp0 hs0
  have hbound := mul_le_mul_of_nonneg_left hps hdpos
  have hnon := mul_nonneg hdpos hps0
  unfold cutoff
  constructor
  · apply (le_div_iff₀ hden).mpr
    nlinarith
  · apply (div_le_iff₀ hden).mpr
    nlinarith

theorem inverse_capacities {d r s : ℝ} (hd0 : 31/50 ≤ d) (hd : d ≤ 7/10)
    (hr : r ≤ inverseThreshold d) (hs : s ≤ cap d) :
    r+2*s < 1 ∧ 2*r+8*s < 3 := by
  have hc := (cap_bounds hd0 hd).2
  dsimp [inverseThreshold,gap] at hr
  constructor <;> linarith

theorem plain_capacity {d m Δ s : ℝ} (hm : m ≤ plainThreshold d)
    (hΔ0 : 0 ≤ Δ) (hΔ : Δ=0) (hs : s ≤ plainCap d) :
    2*m+6*(3/4+2*Δ)*s ≤ 1 := by
  subst Δ
  dsimp [plainThreshold,inverseThreshold,gap,plainCap] at *
  linarith

/-- The strict adaptive cap leaves both unmarked fallback branches below
its full chosen-width target; the positive shrink is retained exactly. -/
theorem count_lower {d p S : ℝ} (hd0 : 31/50 ≤ d) (hd : d ≤ 7/10)
    (hp : p ≤ 1/2) (hS : 0 ≤ S) :
    1-inverseThreshold d*d ≤ count d p (chosenWidth d S) := by
  have hden : 0 < 5-2*d := by linarith
  have hcapden : 0 < 380-240*d := by linarith
  have hi := (inverseWidth_bounds hd0 hd hS).2.2
  have hpw := (plainWidth_bounds hd0 hd hS).2.2
  have hs0 := (chosenWidth_bounds hd0 hd hS).1
  have hschosen : chosenWidth d S ≤ 22*cap d/27 := by
    dsimp [chosenWidth,plainCap] at *
    linarith
  have hmono := mul_nonneg (by linarith : 0 ≤ 1/2-p) hs0
  have hpos : 0 ≤ d*(5-6*d) := mul_nonneg (by linarith) (by linarith)
  have hps := mul_le_mul_of_nonneg_left hmono hpos
  have hwidth := mul_le_mul_of_nonneg_left hschosen hpos
  have haux : (5-2*d)*(count d p (chosenWidth d S) - (1-inverseThreshold d*d)) =
      d*(((5-6*d)/3) -(5-2*d)*(2*cap d+gap)-2*(5-6*d)*p*chosenWidth d S) := by
    unfold count cutoff inverseThreshold
    field_simp
    <;> ring
  have hid : (380-240*d)*(((5-6*d)/3)-(5-2*d)*(2*cap d+gap)-
      (5-6*d)*(22*cap d/27)) =
      (380-240*d)*((5-6*d)/3000000-(5-2*d)*gap) := by
    unfold cap
    field_simp
    <;> ring
  have hsmall : 0 ≤ (5-6*d)/3000000-(5-2*d)*gap := by
    unfold gap
    linarith
  have hge : 0 ≤ ((5-6*d)/3)-(5-2*d)*(2*cap d+gap)-
      (5-6*d)*(22*cap d/27) := by
    have hh := mul_nonneg hcapden.le hsmall
    rw [←hid] at hh
    exact (mul_nonneg_iff_of_pos_left hcapden).mp hh
  have hh : 0 ≤ (5-2*d)*(count d p (chosenWidth d S) - (1-inverseThreshold d*d)) := by
    rw [haux]
    nlinarith
  have hh' := (mul_nonneg_iff_of_pos_left hden).mp hh
  linarith

theorem fiber_exponent {d p S r m E loss eps : ℝ}
    (hd0 : 31/50 ≤ d) (hd : d ≤ 7/10)
    (hp0 : 0 ≤ p) (hp : p ≤ 1/2) (hS : 0 ≤ S)
    (heps : 0 ≤ eps)
    (hlength : cutoff d p (chosenWidth d S)-eps ≤ r+m)
    (hrcap : r ≤ cutoff d p (chosenWidth d S)+eps)
    (hI : E ≤ max 1 ((1+5*r)/6)-d*r+loss)
    (hP : E ≤ 1-2*d*m+loss)
    (hIM : r ≤ inverseThreshold d → E ≤ 1-d*r-2*d*p*inverseWidth d S+loss)
    (hPM : m ≤ plainThreshold d → E ≤ 1-2*d*m-2*d*p*plainWidth d S+loss) :
    E ≤ count d p (chosenWidth d S)+loss+eps := by
  have hdpos : 0 ≤ d := by linarith
  obtain ⟨hs0,hsS,hs⟩ := chosenWidth_bounds hd0 hd hS
  have hlow := count_lower hd0 hd hp hS
  have hid := count_identity (p:=p) (s:=chosenWidth d S) hd
  have hmix : 3*chosenWidth d S=2*inverseWidth d S+plainWidth d S := by
    unfold chosenWidth
    ring
  by_cases hr : r ≤ 1
  · rw [max_eq_left (by linarith : (1+5*r)/6 ≤ 1)] at hI
    by_cases hir : r ≤ inverseThreshold d
    · by_cases hpm : m ≤ plainThreshold d
      · have hi := hIM hir
        have hp' := hPM hpm
        have hlen := mul_le_mul_of_nonneg_left hlength hdpos
        have he := mul_nonneg hdpos heps
        have he' := mul_le_mul_of_nonneg_right hd heps
        have hmix' := congrArg (fun x : ℝ => d*p*x) hmix
        nlinarith
      · have hm : plainThreshold d ≤ m := le_of_lt (lt_of_not_ge hpm)
        have hmul := mul_le_mul_of_nonneg_left hm hdpos
        dsimp [plainThreshold] at hmul
        linarith
    · have hr' : inverseThreshold d ≤ r := le_of_lt (lt_of_not_ge hir)
      have hmul := mul_le_mul_of_nonneg_left hr' hdpos
      nlinarith
  · have hr' : 1 ≤ r := le_of_lt (lt_of_not_ge hr)
    rw [max_eq_right (by linarith : 1 ≤ (1+5*r)/6)] at hI
    have hV : 0 ≤ 5/6-d := by linarith
    have hh := mul_le_mul_of_nonneg_left hrcap hV
    have he := mul_le_mul_of_nonneg_right hd0 heps
    unfold count
    nlinarith

theorem gain_one_upper {d s S : ℝ} (hd0 : 31/50 ≤ d) (hd : d ≤ 7/10)
    (hs0 : 0 ≤ s) (hsS : s ≤ S) : gain d 1 s ≤ 2*d*S := by
  have hdpos : 0 ≤ d := by linarith
  have hden : 0 < 5-2*d := by linarith
  have hratio : (10-12*d)/(5-2*d) ≤ 2 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  have hh := mul_le_mul_of_nonneg_left hratio (mul_nonneg hdpos hs0)
  have hh' := mul_le_mul_of_nonneg_left hsS hdpos
  calc
    gain d 1 s = d*s*((10-12*d)/(5-2*d)) := by unfold gain; ring
    _ ≤ d*s*2 := hh
    _ ≤ 2*d*S := by linarith

theorem joint_width_gap {d p s S : ℝ}
    (hd0 : 31/50 ≤ d) (hd : d ≤ 7/10) (hp : p ≤ 1/2)
    (hs0 : 0 ≤ s) (hsS : s ≤ S) :
    count d p s+2*d*p*S ≤ density d+d*S-phi d*s := by
  have hgain : phi d*s = gain d (1/2) s := by unfold phi gain; ring
  have hupper := gain_one_upper hd0 hd hs0 hsS
  have hlinear : gain d p s = p*gain d 1 s := by unfold gain; ring
  have hhalf : gain d (1/2) s = gain d 1 s/2 := by unfold gain; ring
  have hid := gain_identity (p:=p) (s:=s) hd
  have hcoeff : 0 ≤ 2*d*S-gain d 1 s := by linarith
  have hh := mul_le_mul_of_nonneg_right hp hcoeff
  nlinarith

theorem joint_chosen_gap {d p S : ℝ}
    (hd0 : 31/50 ≤ d) (hd : d ≤ 7/10) (hp : p ≤ 1/2) (hS0 : 0 ≤ S) :
    count d p (chosenWidth d S)+2*d*p*S ≤
      density d+d*S-phi d*chosenWidth d S := by
  have hb := chosenWidth_bounds hd0 hd hS0
  exact joint_width_gap hd0 hd hp hb.1 hb.2.1

theorem phi_nonneg {d : ℝ} (hd0 : 31/50 ≤ d) (hd : d ≤ 7/10) : 0 ≤ phi d := by
  unfold phi
  exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)

theorem phi_le_delta {d : ℝ} (hd0 : 31/50 ≤ d) (hd : d ≤ 7/10) : phi d ≤ d := by
  unfold phi
  apply (div_le_iff₀ (by linarith : 0 < 5-2*d)).mpr
  nlinarith

theorem density_eq_unmarked (d : ℝ) :
    density d = 1-10*d/(3*(5-2*d)) := rfl

def physicalGain (d S D : ℝ) : ℝ :=
  OAI.SevenEighths.ExactMarkedGain.scaledGain (phi d) (cap d) (plainCap d) S D

theorem physicalGain_one (d S : ℝ) : physicalGain d S 1 = phi d*chosenWidth d S := by
  dsimp [physicalGain,OAI.SevenEighths.ExactMarkedGain.scaledGain,
    OAI.SevenEighths.ExactMarkedGain.gain,chosenWidth,inverseWidth,plainWidth]
  simp only [mul_one]
  ring

theorem physicalGain_rescale (d S D : ℝ) (hD : 0 < D) :
    D*(phi d*chosenWidth d (S/D)) = physicalGain d S D := by
  have hi : D*min (S/D) (cap d) = min S (cap d*D) := by
    rw [mul_min_of_nonneg _ _ hD.le,mul_div_cancel₀ _ hD.ne']
    congr 1
    ring
  have hp : D*min (S/D) (plainCap d) = min S (plainCap d*D) := by
    rw [mul_min_of_nonneg _ _ hD.le,mul_div_cancel₀ _ hD.ne']
    congr 1
    ring
  dsimp [physicalGain,OAI.SevenEighths.ExactMarkedGain.scaledGain,
    OAI.SevenEighths.ExactMarkedGain.gain,chosenWidth,inverseWidth,plainWidth]
  rw [←hi,←hp]
  ring

theorem physicalGain_mono_scale {d S D E : ℝ}
    (hd0 : 31/50 ≤ d) (hd : d ≤ 7/10) (hDE : D ≤ E) :
    physicalGain d S D ≤ physicalGain d S E := by
  exact OAI.SevenEighths.ExactMarkedGain.scaledGain_mono_scale _ _ _ _
    (phi_nonneg hd0 hd) (cap_bounds hd0 hd).1.le (plainCap_nonneg hd0 hd) hDE

theorem capacity_rate_le_density {d : ℝ} (hd0 : 31/50 ≤ d) (hd : d ≤ 7/10) :
    phi d*(2*cap d+plainCap d)/3 ≤ density d := by
  have hc := (cap_bounds hd0 hd).2
  have hp := phi_nonneg hd0 hd
  have hpd := phi_le_delta hd0 hd
  have hr : 2/7 ≤ density d := by
    unfold density
    have hh : 10*d/(3*(5-2*d)) ≤ 5/7 := by
      apply (div_le_iff₀ (by linarith : 0 < 3*(5-2*d))).mpr
      nlinarith
    linarith
  unfold plainCap
  have hm := mul_le_mul_of_nonneg_left hc hp
  nlinarith

#print axioms count_lower
#print axioms fiber_exponent
#print axioms joint_chosen_gap
end
end Marked830.VariableSupply
