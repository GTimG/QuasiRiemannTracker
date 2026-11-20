/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Fill the intervals between the four tested conductor edges at the actual
minimum capacity. The chosen valid count at each endpoint can differ. -/
import Candidate.C092.transport.DirectAll
import Candidate.C092.transport.PacketFinalPower

namespace QRH.Cycle092.Direct
noncomputable section
set_option autoImplicit false
open QRH.Cycle090 QRH.Coverage

def blend (v A B : ℝ) : ℝ := (1-v)*A+v*B

theorem blend_mono {v a b A B : ℝ} (hv : 0 ≤ v) (hv' : v ≤ 1)
    (ha : a ≤ A) (hb : b ≤ B) : blend v a b ≤ blend v A B := by
  exact add_le_add (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hv')) (mul_le_mul_of_nonneg_left hb hv)

theorem edge_chord {lo hi D cap₀ cap₁ R₀ R₁ R T : ℝ}
    (base delta p a b c f : ℝ) (hlo : 0 ≤ lo) (hgap : lo < hi)
    (hD : lo ≤ D) (hD' : D ≤ hi) (hprod : 0 ≤ delta*p)
    (hR₀ : R ≤ R₀) (hR₁ : R ≤ R₁)
    (hcap₀ : cap₀ ≤ min (a+b*lo) (c+f*lo)) (hcap₁ : cap₁ ≤ min (a+b*hi) (c+f*hi))
    (he₀ : conductorPrice base delta p R₀ cap₀ lo ≤ T)
    (he₁ : conductorPrice base delta p R₁ cap₁ hi ≤ T) :
    conductorPrice base delta p R (min (a+b*D) (c+f*D)) D ≤ T := by
  let v := (D-lo)/(hi-lo)
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr hD) (sub_nonneg.mpr hgap.le)
  have hv' : v ≤ 1 := (div_le_one (sub_pos.mpr hgap)).mpr (by linarith)
  have hd : blend v lo hi = D := by
    have hz : v*(hi-lo)=D-lo := div_mul_cancel₀ _ (sub_ne_zero.mpr hgap.ne')
    dsimp only [blend]; linarith only [hz]
  have haff (a b : ℝ) : blend v (a+b*lo) (a+b*hi) = a+b*D := by rw [←hd]; unfold blend; ring
  have hcap : blend v cap₀ cap₁ ≤ min (a+b*D) (c+f*D) := le_min
    ((blend_mono hv hv' (le_min_iff.mp hcap₀).1 (le_min_iff.mp hcap₁).1).trans_eq (haff _ _))
    ((blend_mono hv hv' (le_min_iff.mp hcap₀).2 (le_min_iff.mp hcap₁).2).trans_eq (haff _ _))
  have hpay : conductorPrice base delta p R (min (a+b*D) (c+f*D)) D ≤
      conductorPrice base delta p R (blend v cap₀ cap₁) D := by
    unfold conductorPrice; linarith only [mul_le_mul_of_nonneg_left hcap hprod]
  have hlin : conductorPrice base delta p R (blend v cap₀ cap₁) D =
      blend v (conductorPrice base delta p R cap₀ lo) (conductorPrice base delta p R cap₁ hi) := by
    rw [←hd]; unfold conductorPrice blend; ring
  have hr (x k c : ℝ) (hx : 0 ≤ x) (hc : R ≤ k) : conductorPrice base delta p R c x ≤ conductorPrice base delta p k c x := by
    unfold conductorPrice; linarith only [mul_le_mul_of_nonneg_left hc hx]
  exact hpay.trans (hlin.le.trans ((blend_mono hv hv' ((hr _ _ _ hlo hR₀).trans he₀)
    ((hr _ _ _ (hlo.trans hgap.le) hR₁).trans he₁)).trans_eq (by unfold blend; ring)))

theorem natural_chord {D h R R₀ R₁ T : ℝ} (base delta p : ℝ)
    (hlo : (1/200:ℝ) ≤ D) (hhi : D ≤ 19/25) (hprod : 0 ≤ delta*p)
    (hR₀ : R ≤ R₀) (hR₁ : R ≤ R₁)
    (he₀ : conductorPrice base delta p R₀ (originalCapacity 0 h) (1/200) ≤ T)
    (he₁ : conductorPrice base delta p R₁ (originalCapacity 1 h) (19/25) ≤ T) :
    conductorPrice base delta p R (min D (2*yLength h-D)/(6*kap)) D ≤ T := by
  have hk : 0 < 6*kap := by norm_num [kap,QRH.ContactCertificate.alphaHi]
  have hi (X : ℝ) : min X (2*yLength h-X)/(6*kap) =
      min (0+(1/(6*kap))*X) ((2*yLength h)/(6*kap)+(-1/(6*kap))*X) := by
    rw [←min_div_div_right hk.le]
    congr 1 <;> ring
  rw [hi D]
  apply edge_chord base delta p 0 (1/(6*kap)) ((2*yLength h)/(6*kap)) (-1/(6*kap))
    (by norm_num) (by norm_num) hlo hhi hprod hR₀ hR₁ _ _ he₀ he₁
  · exact (hi _).le
  · exact (hi _).le

/-- The upper interval uses the physical cap and the actual reserve cost
in both affine arms. Its tested top capacity is a directed lower bound. -/
theorem native_chord {D h R R₂ R₃ T : ℝ} (base delta p : ℝ)
    (hh : hLower ≤ h)
    (hlo : (19/25:ℝ) ≤ D) (hhi : D ≤ h) (hprod : 0 ≤ delta*p)
    (hR₂ : R ≤ R₂) (hR₃ : R ≤ R₃)
    (he₂ : conductorPrice base delta p R₂ (originalCapacity 2 h) (19/25) ≤ T)
    (he₃ : conductorPrice base delta p R₃ (originalCapacity 3 h) h ≤ T) :
    conductorPrice base delta p R (cappedCapacity physicalCap (yLength h) sourceCost D) D ≤ T := by
  let den := 2+10*sourceCost
  have hrepr (X : ℝ) : cappedCapacity physicalCap (yLength h) sourceCost X =
      min (0+physicalCap*X) (2*yLength h/den+(-(1+sourceCost)/den)*X) := by
    unfold cappedCapacity; rw [zero_add]; congr 1; dsimp [den]; ring
  rw [hrepr]
  refine edge_chord base delta p 0 physicalCap (2*yLength h/den) (-(1+sourceCost)/den)
    (by norm_num) (lt_of_lt_of_le (by norm_num [hLower] : (19/25:ℝ)<hLower) hh) hlo hhi hprod hR₂ hR₃ ?_ ?_ he₂ he₃
  · rw [←hrepr]; exact le_rfl
  · rw [←hrepr]; exact le_rfl

#print axioms native_chord
#print axioms edge_chord
#print axioms natural_chord
end
end QRH.Cycle092.Direct
