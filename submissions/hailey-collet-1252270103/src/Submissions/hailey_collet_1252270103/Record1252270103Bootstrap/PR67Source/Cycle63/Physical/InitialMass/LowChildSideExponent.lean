import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildLabelGate
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryHighPayment
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The side exponent of the labels of a LOW child at the second step: the exponent of the old region, the surplus of the
label and the cone surplus, that is the high side of the label less its radical, and the scalar gate of a first-geometry
bin for it. Released under Apache 2.0. -/
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
open CenteredMomentFirstCanonicalAllowance CenteredMomentActive
open ActualEisensteinCubic Cycle63Moment

/-- The cone surplus of a first label, taken from its own first ideal and the other one. -/
def lowConeSurplus (reflected : Bool) (Z : ℝ) (l : FirstSourceLabel) : ℝ :=
  ValuationCone.surplus (Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm : ℝ))
    (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm : ℝ))
    (Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm : ℝ))
    (Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm : ℝ))

/-- The side exponent of the labels of a LOW child at the second step: the exponent `lowAllowedExponent` of the old
region with the surplus of the label, and the cone surplus when positive. For the labels of a first geometry it is
the high side of the label less the logarithm of its common radical (`lowSideExponent_coordinates`). -/
def lowSideExponent (reflected : Bool) (Z A : ℝ) (l : FirstSourceLabel) : ℝ :=
  lowAllowedExponent reflected Z A l + max (lowConeSurplus reflected Z l) 0

/-- The side exponent is at least the exponent of the old region. -/
theorem lowAllowedExponent_le_lowSideExponent (reflected : Bool) (Z A : ℝ) (l : FirstSourceLabel) :
    lowAllowedExponent reflected Z A l ≤ lowSideExponent reflected Z A l :=
  le_add_of_nonneg_right (le_max_right _ _)

/-- The side exponent of the label of a column is read from its coordinates: it is the high side less the radical. -/
theorem lowSideExponent_coordinates
    {α : Type} [Fintype α] [DecidableEq α]
    (s : Input α) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K) (hZ : 1<Z)
    (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))
    (reflected : Bool) (A : ℝ) (x : Fin 5→ℝ) (hx : x=geometryExponents s R seed K Z ξ j.1.val) :
    lowSideExponent reflected Z A (geometryFirstLabel s R seed K Z ξ hK key j)=
      geometryHighSide reflected A x-x 2 := by
  subst hx
  have h₁ := lowAllowedExponent_coordinates s R seed K Z ξ hK key j reflected A _ rfl
  have h₂ := geometryHighSide_coordinates reflected A (geometryExponents s R seed K Z ξ j.1.val)
  have h₃ := actual_geometry_surplus_eq s R seed K Z ξ hK key j reflected
  have h₄ := actual_geometry_surplus_nonneg s R seed K Z ξ hZ j.1.val
  dsimp only at h₃
  unfold lowSideExponent lowConeSurplus
  rw [max_eq_left (h₃ ▸ h₄)]
  linarith only [h₁, h₂, h₃]

/-- The maximum with zero is monotone with slope at most one. -/
theorem max_zero_sub_le {x y : ℝ} (h : x≤y) : max y 0-max x 0≤y-x := by
  rcases le_total y 0 with hy | hy
  · rw [max_eq_right hy,max_eq_right (h.trans hy)]
    linarith
  · rcases le_total x 0 with hx | hx
    · rw [max_eq_left hy,max_eq_right hx]
      linarith
    · rw [max_eq_left hy,max_eq_left hx]

/-- The bounds of a bin for the side exponent and for the high side: the side exponent
`A-xc+x3+x4+max (3xc-5xd-x3) 0/6+gs` of a column with coordinates in the bin is at most the upper edge, and the upper
edge less five binary-bin widths and the radical edge is the high side `x2+A-xc+x3+x4+max (3xc-5xd-x3) 0/6+gs` of the
lower edges. The surplus `gs` is the one of the geometry, `(xc+xd-x3-2x2-Bc-Bd)/2`. -/
theorem low_bin_side_bounds (w A kc kd k2 k3 k4 xc xd x2 x3 x4 gs : ℝ) (hw : 0≤w)
    (hc : kc*w≤xc ∧ xc≤(kc+1)*w) (hd : kd*w≤xd ∧ xd≤(kd+1)*w) (h2 : k2*w≤x2 ∧ x2≤(k2+1)*w)
    (h3 : k3*w≤x3 ∧ x3≤(k3+1)*w) (h4 : k4*w≤x4 ∧ x4≤(k4+1)*w)
    (hgs : gs=(xc+xd-x3-2*x2-max (3*xc-5*xd-x3) 0/6-max (3*xd-5*xc-x3) 0/6)/2) :
    A-xc+x3+x4+max (3*xc-5*xd-x3) 0/6+gs≤
        A-kc*w/2+(kd+1)*w/2+(k3+1)*w/2+(k4+1)*w-k2*w+max (3*(kc+1)*w-5*kd*w-k3*w) 0/12-
          max (3*kd*w-5*(kc+1)*w-(k3+1)*w) 0/12 ∧
      (k2+1)*w+(A-kc*w/2+(kd+1)*w/2+(k3+1)*w/2+(k4+1)*w-k2*w+max (3*(kc+1)*w-5*kd*w-k3*w) 0/12-
          max (3*kd*w-5*(kc+1)*w-(k3+1)*w) 0/12)-6*w≤
        x2+(A-xc+x3+x4+max (3*xc-5*xd-x3) 0/6+gs) := by
  have haup : max (3*xc-5*xd-x3) 0 ≤ max (3*(kc+1)*w-5*kd*w-k3*w) 0 :=
    max_le_max (by linarith [hc.2,hd.1,h3.1]) le_rfl
  have halow : max (3*kc*w-5*(kd+1)*w-(k3+1)*w) 0 ≤ max (3*xc-5*xd-x3) 0 :=
    max_le_max (by linarith [hc.1,hd.2,h3.2]) le_rfl
  have hbup : max (3*xd-5*xc-x3) 0 ≤ max (3*(kd+1)*w-5*kc*w-k3*w) 0 :=
    max_le_max (by linarith [hd.2,hc.1,h3.1]) le_rfl
  have hblow : max (3*kd*w-5*(kc+1)*w-(k3+1)*w) 0 ≤ max (3*xd-5*xc-x3) 0 :=
    max_le_max (by linarith [hd.1,hc.2,h3.2]) le_rfl
  have hgapa := max_zero_sub_le (x:=3*kc*w-5*(kd+1)*w-(k3+1)*w) (y:=3*(kc+1)*w-5*kd*w-k3*w) (by linarith)
  have hgapb := max_zero_sub_le (x:=3*kd*w-5*(kc+1)*w-(k3+1)*w) (y:=3*(kd+1)*w-5*kc*w-k3*w) (by linarith)
  constructor
  · rw [hgs]
    linarith [hc.1, hd.2, h3.2, h4.2, h2.1]
  · rw [hgs]
    linarith [hc.2, hd.1, h3.1, h4.1, h2.1, h2.2]

/-- The first-level gates of one common first-geometry bin for the side exponent of the labels: the radical is bounded
by the upper edge of the bin, the side exponent by the upper edge of the exponent, and the high side is bounded below,
with the combined loss six binary-bin widths (in fact at most five, since the radical `x2` cancels in the high side
less the radical, and the surplus couples with the other coordinates). -/
theorem actual_geometry_low_bin_gate_side : LowBinGate lowSideExponent 6 := by
  intro α _ _ s R seed K Z ξ B A hK hZ hs hz₁ hz₂ hsource key reflected
  have hw : 0≤Real.logb Z 2 := Real.logb_nonneg hZ (by norm_num)
  obtain ⟨c,hc⟩ : ∃c : Fin 5,c=(if reflected then 1 else 0) := ⟨_,rfl⟩
  obtain ⟨d,hd⟩ : ∃d : Fin 5,d=(if reflected then 0 else 1) := ⟨_,rfl⟩
  obtain ⟨E,hE⟩ : ∃E : ℝ,E=A-(key.2 c:ℝ)*Real.logb Z 2/2+((key.2 d:ℝ)+1)*Real.logb Z 2/2+
      ((key.2 3:ℝ)+1)*Real.logb Z 2/2+((key.2 4:ℝ)+1)*Real.logb Z 2-(key.2 2:ℝ)*Real.logb Z 2+
      max (3*((key.2 c:ℝ)+1)*Real.logb Z 2-5*(key.2 d:ℝ)*Real.logb Z 2-(key.2 3:ℝ)*Real.logb Z 2) 0/12-
      max (3*(key.2 d:ℝ)*Real.logb Z 2-5*((key.2 c:ℝ)+1)*Real.logb Z 2-((key.2 3:ℝ)+1)*Real.logb Z 2) 0/12 :=
    ⟨_,rfl⟩
  refine ⟨E,((key.2 2:ℝ)+1)*Real.logb Z 2+E-6*Real.logb Z 2,by ring,fun j=>?_⟩
  obtain ⟨x,hx⟩ : ∃x : Fin 5→ℝ,x=geometryExponents s R seed K Z ξ j.1.val := ⟨_,rfl⟩
  have hfiber (i : Fin 5) : (key.2 i:ℝ)*Real.logb Z 2≤x i ∧ x i≤((key.2 i:ℝ)+1)*Real.logb Z 2 := by
    have h:=actual_geometry_fiber_range s R seed K Z ξ B hZ hs hz₁ hz₂ hsource key j.1 i
    rw [hx]
    exact ⟨h.1,h.2.le⟩
  have hgs : geometrySurplus x=(x c+x d-x 3-2*x 2-max (3*x c-5*x d-x 3) 0/6-max (3*x d-5*x c-x 3) 0/6)/2 := by
    subst hc hd
    cases reflected
    · simp only [geometrySurplus,Bool.false_eq_true,ite_false]
    · simp only [geometrySurplus,ite_true]
      ring
  have hbounds:=low_bin_side_bounds (Real.logb Z 2) A (key.2 c:ℝ) (key.2 d:ℝ) (key.2 2:ℝ) (key.2 3:ℝ)
    (key.2 4:ℝ) (x c) (x d) (x 2) (x 3) (x 4) (geometrySurplus x) hw (hfiber c) (hfiber d) (hfiber 2)
    (hfiber 3) (hfiber 4) hgs
  refine ⟨?_,?_,?_⟩
  · have hn:=actual_geometry_norm_caps s R seed K Z ξ B hs hz₁ hz₂ hsource j.1.val 2
    have hcap : geometryExponents s R seed K Z ξ j.1.val 2≤((key.2 2:ℝ)+1)*Real.logb Z 2 := by
      rw [← hx]
      exact (hfiber 2).2
    exact (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hn.1)).mp hcap
  · rw [lowSideExponent_coordinates s R seed K Z ξ hK hZ key j reflected A x hx,geometryHighSide_coordinates,← hc,
      ← hd,hE]
    have h2 := hbounds.1
    linarith only [h2]
  · rw [← hx,geometryHighSide_coordinates,← hc,← hd,hE]
    have h2 := hbounds.2
    linarith only [h2]

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
