/- Adapted from Zhongpai Gao, gao-balanced-marked-20261017, Apache-2.0;
upstream math snapshot 9c0e14f985041e397f71c574028193ee595a0f98.
Underlying Cycle61: Hailey Collet; original analytic interfaces: OpenAI, Apache-2.0. -/
import Mathlib.Tactic

/-! Scalar balanced-source normalization and its cross-label bin bound.
This module does not assert an analytic moment or an endpoint. -/

noncomputable section

namespace QRH.Record12518109Assembly.Scalar

def side (c d r : ℝ) : ℝ := max (3*c-5*d-r) 0 / 6

def surplus (c d r p : ℝ) : ℝ :=
  (c+d-r-2*p-side c d r-side d c r)/2

def oldLeft (a c d r e p : ℝ) : ℝ := p+a-c+r+e+side c d r

def oldRight (a c d r e p : ℝ) : ℝ := p+a-d+r+e+side d c r

def left (a c d r e : ℝ) : ℝ :=
  a+(d-c)/2+r/2+e+(side c d r-side d c r)/2

def right (a c d r e : ℝ) : ℝ :=
  a+(c-d)/2+r/2+e+(side d c r-side c d r)/2

def outer (m a r e : ℝ) : ℝ := m-a-r/2-e

theorem surplus_nonneg {c d r p : ℝ}
    (h : 2*p+side c d r+side d c r+r ≤ c+d) :
    0 ≤ surplus c d r p := by
  unfold surplus
  linarith

theorem left_normalization (a c d r e p : ℝ) :
    oldLeft a c d r e p+surplus c d r p = left a c d r e := by
  unfold oldLeft surplus left
  ring

theorem right_normalization (a c d r e p : ℝ) :
    oldRight a c d r e p+surplus c d r p = right a c d r e := by
  unfold oldRight surplus right
  ring

theorem old_budget (m a c d r e p : ℝ) :
    outer m a r e+(oldLeft a c d r e p+oldRight a c d r e p)/2 =
      m-surplus c d r p := by
  unfold outer oldLeft oldRight surplus
  ring

theorem balanced_budget (m a c d r e : ℝ) :
    outer m a r e+(left a c d r e+right a c d r e)/2 = m := by
  unfold outer left right
  ring

theorem side_bin_bound {c d r c' d' r' w : ℝ}
    (hc : |c'-c| ≤ w) (hd : |d'-d| ≤ w) (hr : |r'-r| ≤ w) :
    |side c' d' r'-side c d r| ≤ 3*w/2 := by
  rcases abs_le.mp hc with ⟨hc₁,hc₂⟩
  rcases abs_le.mp hd with ⟨hd₁,hd₂⟩
  rcases abs_le.mp hr with ⟨hr₁,hr₂⟩
  rw [abs_le]
  unfold side
  simp only [max_def]
  split_ifs <;> constructor <;> linarith

theorem right_bin_bound {a c d r e c' d' r' e' w : ℝ}
    (hc : |c'-c| ≤ w) (hd : |d'-d| ≤ w)
    (hr : |r'-r| ≤ w) (he : |e'-e| ≤ w) :
    |right a c' d' r' e'-right a c d r e| ≤ 4*w := by
  have hb := side_bin_bound hc hd hr
  have hb' := side_bin_bound hd hc hr
  rcases abs_le.mp hc with ⟨hc₁,hc₂⟩
  rcases abs_le.mp hd with ⟨hd₁,hd₂⟩
  rcases abs_le.mp hr with ⟨hr₁,hr₂⟩
  rcases abs_le.mp he with ⟨he₁,he₂⟩
  rcases abs_le.mp hb with ⟨hb₁,hb₂⟩
  rcases abs_le.mp hb' with ⟨hb'₁,hb'₂⟩
  rw [abs_le]
  unfold right
  constructor <;> linarith

theorem cross_label_budget {m a c d r e c' d' r' e' w : ℝ}
    (hc : |c'-c| ≤ w) (hd : |d'-d| ≤ w)
    (hr : |r'-r| ≤ w) (he : |e'-e| ≤ w) :
    outer m a r e+(left a c d r e+right a c' d' r' e')/2 ≤ m+2*w := by
  have hb := (abs_le.mp (right_bin_bound (a := a) hc hd hr he)).2
  have heq := balanced_budget m a c d r e
  linarith

end QRH.Record12518109Assembly.Scalar

#print axioms QRH.Record12518109Assembly.Scalar.surplus_nonneg
#print axioms QRH.Record12518109Assembly.Scalar.left_normalization
#print axioms QRH.Record12518109Assembly.Scalar.right_normalization
#print axioms QRH.Record12518109Assembly.Scalar.old_budget
#print axioms QRH.Record12518109Assembly.Scalar.balanced_budget
#print axioms QRH.Record12518109Assembly.Scalar.side_bin_bound
#print axioms QRH.Record12518109Assembly.Scalar.right_bin_bound
#print axioms QRH.Record12518109Assembly.Scalar.cross_label_budget
