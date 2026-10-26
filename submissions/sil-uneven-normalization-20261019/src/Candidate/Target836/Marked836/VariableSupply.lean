import Mathlib.Tactic

/-! Variable-width marked detector count.  The analytic moment bounds
remain explicit hypotheses.  The resulting saving pays surviving physical
slot width at the same rate as the allocation ledger pays removed width. -/

namespace Marked836.VariableSupply
noncomputable section

def cutoff (d p s : ℝ) : ℝ := (5-12*d*p*s)/(5-2*d)
def count (d p s : ℝ) : ℝ := 1/6+(5/6-d)*cutoff d p s
def density (d : ℝ) : ℝ := 1-10*d/(3*(5-2*d))
def gain (d p s : ℝ) : ℝ := d*p*s*(10-12*d)/(5-2*d)
def phi (d : ℝ) : ℝ := d*(5-6*d)/(5-2*d)

def inverseWidth (S : ℝ) : ℝ := min S (13/400)
def plainWidth (S : ℝ) : ℝ := min S (3/200)
def chosenWidth (S : ℝ) : ℝ := (2*inverseWidth S+plainWidth S)/3

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

theorem inverseWidth_bounds {S : ℝ} (hS : 0 ≤ S) :
    0 ≤ inverseWidth S ∧ inverseWidth S ≤ S ∧ inverseWidth S ≤ 13/400 := by
  exact ⟨le_min hS (by norm_num),min_le_left _ _,min_le_right _ _⟩

theorem plainWidth_bounds {S : ℝ} (hS : 0 ≤ S) :
    0 ≤ plainWidth S ∧ plainWidth S ≤ S ∧ plainWidth S ≤ 3/200 := by
  exact ⟨le_min hS (by norm_num),min_le_left _ _,min_le_right _ _⟩

theorem chosenWidth_bounds {S : ℝ} (hS : 0 ≤ S) :
    0 ≤ chosenWidth S ∧ chosenWidth S ≤ S ∧ chosenWidth S ≤ 2/75 := by
  have hi := inverseWidth_bounds hS
  have hp := plainWidth_bounds hS
  dsimp [chosenWidth]
  constructor
  · linarith [hi.1,hp.1]
  constructor <;> linarith

theorem chosenWidth_pos {S : ℝ} (hS : 0 < S) : 0 < chosenWidth S := by
  have hi : 0 < inverseWidth S := lt_min hS (by norm_num)
  have hp : 0 < plainWidth S := lt_min hS (by norm_num)
  dsimp [chosenWidth]
  positivity

theorem chosenWidth_lower {S : ℝ} (hS : 0 ≤ S) :
    (32/39)*min S (13/400) ≤ chosenWidth S := by
  have hsmall : (6/13)*min S (13/400) ≤ min S (3/200) := by
    apply le_min
    · have hm := min_le_left S (13/400)
      have hn := le_min hS (by norm_num : (0:ℝ)≤13/400)
      linarith
    · have hm := min_le_right S (13/400)
      linarith
  dsimp [chosenWidth,inverseWidth,plainWidth]
  linarith

theorem chosenWidth_mono {S T : ℝ} (h : S ≤ T) : chosenWidth S ≤ chosenWidth T := by
  have hi := min_le_min_right (13/400:ℝ) h
  have hp := min_le_min_right (3/200:ℝ) h
  dsimp [chosenWidth,inverseWidth,plainWidth]
  linarith

theorem zero_width_count {d p : ℝ} (hd : d ≤ 7/10) : count d p 0 = density d := by
  have hh := gain_identity (p:=p) (s:=0) hd
  simp only [gain,mul_zero,zero_mul,zero_div] at hh
  linarith

theorem cutoff_bounds {d p s : ℝ} (hd0 : 839/1250 ≤ d) (hd : d ≤ 7/10)
    (hp0 : 0 ≤ p) (hp : p ≤ 1/2) (hs0 : 0 ≤ s) (hs : s ≤ 2/75) :
    1 ≤ cutoff d p s ∧ cutoff d p s ≤ 3/2 := by
  have hden : 0 < 5-2*d := by linarith
  have hdpos : 0 ≤ d := by linarith
  have hps : p*s ≤ 1/75 := by nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hs)]
  have hps0 : 0 ≤ p*s := mul_nonneg hp0 hs0
  have hbound := mul_le_mul_of_nonneg_left hps hdpos
  have hnon := mul_nonneg hdpos hps0
  unfold cutoff
  constructor
  · apply (le_div_iff₀ hden).mpr
    nlinarith
  · apply (div_le_iff₀ hden).mpr
    nlinarith

theorem inverse_capacities {r s : ℝ} (hr : r ≤ 467/500) (hs : s ≤ 13/400) :
    r+2*s < 1 ∧ 2*r+8*s < 3 := by constructor <;> linarith

theorem plain_capacity {m Δ s : ℝ} (hm : m ≤ 233/500)
    (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ 1/1000) (hs : s ≤ 3/200) :
    2*m+6*(3/4+2*Δ)*s ≤ 1 := by
  have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ 6*(3/4+2*Δ) by positivity)
  nlinarith

theorem count_lower {d p s : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 7/10)
    (hp : p ≤ 1/2) (hs0 : 0 ≤ s) (hs : s ≤ 2/75) :
    1-233/250*d ≤ count d p s := by
  have hden : 0 < 5-2*d := by linarith
  have hid : (5-2*d)*(count d p s-(1-233/250*d)) =
      d*(1/1875+213/125*(7/10-d)+(2/75-s)*(5-6*d)+
        2*s*(1/2-p)*(5-6*d)) := by
    unfold count cutoff
    field_simp
    <;> ring
  have hn : 0 ≤ d*(1/1875+213/125*(7/10-d)+(2/75-s)*(5-6*d)+
      2*s*(1/2-p)*(5-6*d)) := by
    have h1 : 0 ≤ 7/10-d := by linarith
    have h2 : 0 ≤ 1/2-p := by linarith
    have h3 : 0 ≤ 5-6*d := by linarith
    have h4 : 0 ≤ 2/75-s := by linarith
    positivity
  have hh : 0 ≤ count d p s-(1-233/250*d) :=
    (mul_nonneg_iff_of_pos_left hden).mp (hid.symm ▸ hn)
  linarith

/-- The inverse and plain estimates select independent subproducts. The
weighted effective width reflects their different coefficients in the length
balance, and each selected subproduct obeys its own moment capacity. -/
theorem fiber_exponent {d p S r m E loss eps : ℝ}
    (hd0 : 839/1250 ≤ d) (hd : d ≤ 7/10)
    (hp0 : 0 ≤ p) (hp : p ≤ 1/2) (hS : 0 ≤ S)
    (heps : 0 ≤ eps)
    (hlength : cutoff d p (chosenWidth S)-eps ≤ r+m)
    (hrcap : r ≤ cutoff d p (chosenWidth S)+eps)
    (hI : E ≤ max 1 ((1+5*r)/6)-d*r+loss)
    (hP : E ≤ 1-2*d*m+loss)
    (hIM : r ≤ 467/500 → E ≤ 1-d*r-2*d*p*inverseWidth S+loss)
    (hPM : m ≤ 233/500 → E ≤ 1-2*d*m-2*d*p*plainWidth S+loss) :
    E ≤ count d p (chosenWidth S)+loss+eps := by
  have hdpos : 0 ≤ d := by linarith
  obtain ⟨hs0,hsS,hs⟩ := chosenWidth_bounds hS
  have hlow := count_lower hdpos hd hp hs0 hs
  have hid := count_identity (p:=p) (s:=chosenWidth S) hd
  have hmix : 3*chosenWidth S=2*inverseWidth S+plainWidth S := by
    unfold chosenWidth
    ring
  by_cases hr : r ≤ 1
  · rw [max_eq_left (by linarith : (1+5*r)/6 ≤ 1)] at hI
    by_cases hir : r ≤ 467/500
    · by_cases hpm : m ≤ 233/500
      · have hi := hIM hir
        have hp' := hPM hpm
        have hlen := mul_le_mul_of_nonneg_left hlength hdpos
        have he := mul_nonneg hdpos heps
        have he' := mul_le_mul_of_nonneg_right hd heps
        have hmix' := congrArg (fun x : ℝ => d*p*x) hmix
        nlinarith
      · have hm : 233/500 ≤ m := le_of_lt (lt_of_not_ge hpm)
        have hmul := mul_le_mul_of_nonneg_left hm hdpos
        linarith
    · have hr' : 467/500 ≤ r := le_of_lt (lt_of_not_ge hir)
      have hmul := mul_le_mul_of_nonneg_left hr' hdpos
      nlinarith
  · have hr' : 1 ≤ r := le_of_lt (lt_of_not_ge hr)
    rw [max_eq_right (by linarith : 1 ≤ (1+5*r)/6)] at hI
    have hV : 0 ≤ 5/6-d := by linarith
    have hh := mul_le_mul_of_nonneg_left hrcap hV
    have he := mul_le_mul_of_nonneg_right hd0 heps
    unfold count
    nlinarith

theorem gain_half_per_width {d s : ℝ} (hd0 : 839/1250 ≤ d) (hd : d ≤ 7/10)
    (hs0 : 0 ≤ s) : (7/45)*s ≤ gain d (1/2) s := by
  have hden : 0 < 5-2*d := by linarith
  have hnon : 0 ≤ (7/10-d)*(d-5/27) :=
    mul_nonneg (by linarith) (by linarith)
  have hratio : 7/45 ≤ d*(5-6*d)/(5-2*d) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hratio hs0
  convert hh using 1 <;> unfold gain <;> ring

theorem gain_one_upper {d s S : ℝ} (hd0 : 839/1250 ≤ d) (hd : d ≤ 7/10)
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
    (hd0 : 839/1250 ≤ d) (hd : d ≤ 7/10) (hp : p ≤ 1/2)
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
    (hd0 : 839/1250 ≤ d) (hd : d ≤ 7/10) (hp : p ≤ 1/2) (hS0 : 0 ≤ S) :
    count d p (chosenWidth S)+2*d*p*S ≤
      density d+d*S-phi d*chosenWidth S := by
  have hb := chosenWidth_bounds hS0
  exact joint_width_gap hd0 hd hp hb.1 hb.2.1

/-- The asymmetric selection survives row rescaling with a single
minimum. The slope is the exact worst ratio between effective and inverse
selected widths. -/
theorem physical_rescale_min {q d p z : ℝ}
    (hq : 0 < q) (hd0 : 839/1250 ≤ d) (hd : d ≤ 7/10) (hp : p ≤ 1/2)
    (hz0 : 0 ≤ z) :
    q*count d p (chosenWidth (z/q))+2*d*p*z ≤
      q*density d+d*z-((32/39)*phi d)*min z (13*q/400) := by
  have hh := mul_le_mul_of_nonneg_left
    (joint_chosen_gap hd0 hd hp (div_nonneg hz0 hq.le)) hq.le
  have hlo := mul_le_mul_of_nonneg_left
    (chosenWidth_lower (div_nonneg hz0 hq.le)) hq.le
  have hmin : q*min (z/q) (13/400) = min z (13*q/400) := by
    rw [mul_min_of_nonneg _ _ hq.le,mul_div_cancel₀ _ hq.ne']
    congr 1
    ring
  have hcancel : q*(z/q)=z := mul_div_cancel₀ _ hq.ne'
  have hleft : q*(count d p (chosenWidth (z/q))+2*d*p*(z/q)) =
      q*count d p (chosenWidth (z/q))+2*d*p*z := by field_simp <;> ring
  have hright : q*(density d+d*(z/q)-phi d*chosenWidth (z/q)) =
      q*density d+d*z-phi d*(q*chosenWidth (z/q)) := by field_simp <;> ring
  have hlo' : (32/39)*min z (13*q/400) ≤ q*chosenWidth (z/q) := by
    calc
      _=(32/39)*(q*min (z/q) (13/400)) := by rw [hmin]
      _=q*((32/39)*min (z/q) (13/400)) := by ring
      _≤_ := hlo
  have hphi : 0 ≤ phi d := by
    unfold phi
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hscale := mul_le_mul_of_nonneg_left hlo' hphi
  rw [hleft,hright] at hh
  nlinarith


#print axioms fiber_exponent
#print axioms joint_chosen_gap
#print axioms physical_rescale_min
end
end Marked836.VariableSupply
