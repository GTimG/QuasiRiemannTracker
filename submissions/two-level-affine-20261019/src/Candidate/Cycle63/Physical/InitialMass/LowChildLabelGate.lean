/- The scalar gate of a first-geometry bin for the exponent of the labels of a LOW child at the second step: the exponent
of the old region and the surplus of the label. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryLowSidePayment
import Candidate.Cycle63.Physical.InitialMass.LowChildReturned
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstCanonicalAllowance

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
open CenteredMomentFirstCanonicalAllowance CenteredMomentActive
open ActualEisensteinCubic Cycle63Moment

/-- The exponent of the labels of a LOW child at the second step: the exponent of the old region and the surplus of
the label, taken from the own first ideal and the other one. -/
def lowAllowedExponent (reflected : Bool) (Z A : ℝ) (l : FirstSourceLabel) : ℝ :=
  lowGeometryExponent reflected Z A l +
    lowSurplus Z (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2)

/-- The active conductor of a pair of ideals generates the ideal of the active conductor of the swapped pair. -/
theorem span_activeConductor_comm (I J : Ideal O) :
    Ideal.span {activeConductor I J}=Ideal.span {activeConductor J I} := by
  rw [activeConductor_span_filter,activeConductor_span_filter,commonSupport_comm J I]
  refine Finset.prod_congr (Finset.filter_congr fun P _=>?_) fun _ _=>rfl
  unfold netExponent
  omega

/-- The surplus of the label of a column is read from the coordinates `c, d, R` of its first label. -/
theorem lowSurplus_coordinates
    {α : Type*} [Fintype α] [DecidableEq α]
    (s : Input α) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
    (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))
    (reflected : Bool) (x : Fin 5→ℝ) (hx : x=geometryExponents s R seed K Z ξ j.1.val) :
    lowSurplus Z (if reflected then (geometryFirstLabel s R seed K Z ξ hK key j).1.2
        else (geometryFirstLabel s R seed K Z ξ hK key j).1.1)
      (if reflected then (geometryFirstLabel s R seed K Z ξ hK key j).1.1
        else (geometryFirstLabel s R seed K Z ξ hK key j).1.2)=
      max (3*x (if reflected then 1 else 0)-5*x (if reflected then 0 else 1)-x 3) 0/6 := by
  subst hx
  cases reflected
  · change lowSurplus Z (geometryFirstLabel s R seed K Z ξ hK key j).1.1
        (geometryFirstLabel s R seed K Z ξ hK key j).1.2=
      max (3*geometryExponents s R seed K Z ξ j.1.val 0-5*geometryExponents s R seed K Z ξ j.1.val 1-
        geometryExponents s R seed K Z ξ j.1.val 3) 0/6
    rfl
  · change lowSurplus Z (geometryFirstLabel s R seed K Z ξ hK key j).1.2
        (geometryFirstLabel s R seed K Z ξ hK key j).1.1=
      max (3*geometryExponents s R seed K Z ξ j.1.val 1-5*geometryExponents s R seed K Z ξ j.1.val 0-
        geometryExponents s R seed K Z ξ j.1.val 3) 0/6
    unfold lowSurplus
    rw [span_activeConductor_comm]
    rfl

/-- The exponent of the labels with the surplus is read from the coordinates `c, d, R, E` of the first label. -/
theorem lowAllowedExponent_coordinates
    {α : Type*} [Fintype α] [DecidableEq α]
    (s : Input α) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
    (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))
    (reflected : Bool) (A : ℝ) (x : Fin 5→ℝ) (hx : x=geometryExponents s R seed K Z ξ j.1.val) :
    lowAllowedExponent reflected Z A (geometryFirstLabel s R seed K Z ξ hK key j)=
      A-x (if reflected then 1 else 0)+x 3+x 4+
        max (3*x (if reflected then 1 else 0)-5*x (if reflected then 0 else 1)-x 3) 0/6 := by
  have h₁:=actual_low_geometry_exponent_coordinates s R seed K Z ξ hK key j reflected A
  have h₂:=lowSurplus_coordinates s R seed K Z ξ hK key j reflected x hx
  subst hx
  dsimp only at h₁
  unfold lowAllowedExponent
  rw [h₁,h₂]

/-- The high side of a first label is read from its coordinates. -/
theorem geometryHighSide_coordinates (reflected : Bool) (A : ℝ) (x : Fin 5→ℝ) :
    geometryHighSide reflected A x=
      x 2+A-x (if reflected then 1 else 0)+x 3+x 4+
        max (3*x (if reflected then 1 else 0)-5*x (if reflected then 0 else 1)-x 3) 0/6+
        geometrySurplus x := by
  cases reflected <;> rfl

/-- The bounds of a bin for the exponent with the surplus and for the high side: the exponent
`A-c+R+E+max(3c-5d-R,0)/6` of a column with coordinates in the bin is at most that of the upper edges, and six bin
widths below that exponent and the exponent `p` of the radical there is the high side of the lower edges. -/
theorem low_bin_allowance_bounds (w A kc kd k2 k3 k4 xc xd x2 x3 x4 gs : ℝ) (hw : 0≤w)
    (hc : kc*w≤xc ∧ xc≤(kc+1)*w) (hd : kd*w≤xd ∧ xd≤(kd+1)*w) (h2 : k2*w≤x2)
    (h3 : k3*w≤x3 ∧ x3≤(k3+1)*w) (h4 : k4*w≤x4 ∧ x4≤(k4+1)*w) (hgs : 0≤gs) :
    A-xc+x3+x4+max (3*xc-5*xd-x3) 0/6≤
        A-kc*w+(k3+1)*w+(k4+1)*w+max (3*(kc+1)*w-5*kd*w-k3*w) 0/6 ∧
      (k2+1)*w+(A-kc*w+(k3+1)*w+(k4+1)*w+max (3*(kc+1)*w-5*kd*w-k3*w) 0/6)-6*w≤
        x2+A-xc+x3+x4+max (3*xc-5*xd-x3) 0/6+gs := by
  have hup : max (3*xc-5*xd-x3) 0 ≤ max (3*(kc+1)*w-5*kd*w-k3*w) 0 :=
    max_le_max (by linarith [hc.2,hd.1,h3.1]) le_rfl
  have hlow : max (3*kc*w-5*(kd+1)*w-(k3+1)*w) 0 ≤ max (3*xc-5*xd-x3) 0 :=
    max_le_max (by linarith [hc.1,hd.2,h3.2]) le_rfl
  have hgap : max (3*(kc+1)*w-5*kd*w-k3*w) 0 ≤ max (3*kc*w-5*(kd+1)*w-(k3+1)*w) 0+9*w := by
    rcases le_total (3*(kc+1)*w-5*kd*w-k3*w) 0 with h|h
    · rw [max_eq_right h]
      linarith [le_max_right (3*kc*w-5*(kd+1)*w-(k3+1)*w) 0]
    · rw [max_eq_left h]
      linarith [le_max_left (3*kc*w-5*(kd+1)*w-(k3+1)*w) 0]
  constructor
  · linarith [hc.1,h3.2,h4.2]
  · linarith [hc.2,h2,h3.1,h4.1]

/-- The first-geometry bin gate for the exponent of the labels with the surplus of the second step: the combined loss
is six binary-bin widths. -/
theorem actual_geometry_low_bin_gate_allowance : LowBinGate lowAllowedExponent 6 := by
  intro α _ _ s R seed K Z ξ B A hK hZ hs hz₁ hz₂ hsource key reflected
  have hw : 0≤Real.logb Z 2 := Real.logb_nonneg hZ (by norm_num)
  obtain ⟨c,hc⟩ : ∃c : Fin 5,c=(if reflected then 1 else 0) := ⟨_,rfl⟩
  obtain ⟨d,hd⟩ : ∃d : Fin 5,d=(if reflected then 0 else 1) := ⟨_,rfl⟩
  obtain ⟨E,hE⟩ : ∃E : ℝ,E=A-(key.2 c:ℝ)*Real.logb Z 2+((key.2 3:ℝ)+1)*Real.logb Z 2+
      ((key.2 4:ℝ)+1)*Real.logb Z 2+
      max (3*((key.2 c:ℝ)+1)*Real.logb Z 2-5*(key.2 d:ℝ)*Real.logb Z 2-(key.2 3:ℝ)*Real.logb Z 2) 0/6 :=
    ⟨_,rfl⟩
  refine ⟨E,((key.2 2:ℝ)+1)*Real.logb Z 2+E-6*Real.logb Z 2,by ring,fun j=>?_⟩
  obtain ⟨x,hx⟩ : ∃x : Fin 5→ℝ,x=geometryExponents s R seed K Z ξ j.1.val := ⟨_,rfl⟩
  have hfiber (i : Fin 5) : (key.2 i:ℝ)*Real.logb Z 2≤x i ∧ x i≤((key.2 i:ℝ)+1)*Real.logb Z 2 := by
    have h:=actual_geometry_fiber_range s R seed K Z ξ B hZ hs hz₁ hz₂ hsource key j.1 i
    rw [hx]
    exact ⟨h.1,h.2.le⟩
  have hbounds:=low_bin_allowance_bounds (Real.logb Z 2) A (key.2 c:ℝ) (key.2 d:ℝ) (key.2 2:ℝ)
    (key.2 3:ℝ) (key.2 4:ℝ) (x c) (x d) (x 2) (x 3) (x 4) (geometrySurplus x) hw (hfiber c) (hfiber d)
    (hfiber 2).1 (hfiber 3) (hfiber 4)
    (by rw [hx]; exact actual_geometry_surplus_nonneg s R seed K Z ξ hZ j.1.val)
  refine ⟨?_,?_,?_⟩
  · have hn:=actual_geometry_norm_caps s R seed K Z ξ B hs hz₁ hz₂ hsource j.1.val 2
    have hcap : geometryExponents s R seed K Z ξ j.1.val 2≤((key.2 2:ℝ)+1)*Real.logb Z 2 := by
      rw [← hx]
      exact (hfiber 2).2
    exact (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hn.1)).mp hcap
  · rw [lowAllowedExponent_coordinates s R seed K Z ξ hK key j reflected A x hx,← hc,← hd,hE]
    exact hbounds.1
  · rw [← hx,geometryHighSide_coordinates,← hc,← hd,hE]
    exact hbounds.2

end
end OAI.SevenEighths.Cycle63InitialMass
