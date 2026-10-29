/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.CurvedSourceStep

namespace Qrh.JointDetector.RepeatedMarks.CurvedSourceStep
noncomputable section
open Set QRH.SilDensitySplit.Density
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- A strict Bernstein certificate for a quadratic on a whole interval.
Unlike endpoint sampling, the middle coefficient controls its interior. -/
def QuadraticSigns (a b c V : ℝ) : Prop :=
  0 < a ∧ 0 < a+b*V/2 ∧ 0 < a+b*V+c*V^2

theorem QuadraticSigns.uniform {a b c V : ℝ} (h : QuadraticSigns a b c V)
    (hV : 0 < V) : ∃ r, 0 < r ∧ ∀ v ∈ Icc (0:ℝ) V, r ≤ a+b*v+c*v^2 := by
  let r := min a (min (a+b*V/2) (a+b*V+c*V^2))
  refine ⟨r,lt_min h.1 (lt_min h.2.1 h.2.2),?_⟩
  intro v hv
  let x := v/V
  have hx0 : 0 ≤ x := div_nonneg hv.1 hV.le
  have hx1 : x ≤ 1 := (div_le_one hV).2 hv.2
  have ha : r ≤ a := min_le_left _ _
  have hb : r ≤ a+b*V/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hc : r ≤ a+b*V+c*V^2 := (min_le_right _ _).trans (min_le_right _ _)
  have h0 := mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg (1-x))
  have h1 := mul_nonneg (sub_nonneg.mpr hb) (by positivity : 0 ≤ 2*x*(1-x))
  have h2 := mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg x)
  have he : a+b*v+c*v^2-r =
      (a-r)*(1-x)^2+(a+b*V/2-r)*(2*x*(1-x))+(a+b*V+c*V^2-r)*x^2 := by
    dsimp [x]
    field_simp
    <;> ring
  linarith

/-- Coefficients of the six cleared physical geometry reserves, in the
excess width v=w-crossing. LOW is handled separately per unit width. -/
def geometryCoeff (p : Params) (i : Fin 6) (j : Fin 3) : ℝ :=
  let s := crossing p
  let a := ![1/10, p.c0-s, 1-p.B+(p.L-2)*s,
    1/20+3/2*(1-p.B)+(3/2*p.L-5/2)*s,
    1-p.B+(p.L-1)*s, 1/3-2*s] i
  let b := ![p.D/10-6*p.A, p.c0*(p.D-6*p.A)-1-p.D*s+p.A,
    p.D*(1-p.B+(p.L-2)*s)+(p.L-2)-9/2*p.A,
    p.D*(1/20+3/2*(1-p.B)+(3/2*p.L-5/2)*s)+(3/2*p.L-5/2)-9/2*p.A,
    p.D*(1-p.B+(p.L-1)*s)+(p.L-1)-4*p.A,
    p.D*(1/3-2*s)-2-3*p.A] i
  let c := ![0,-p.D,p.D*(p.L-2),p.D*(3/2*p.L-5/2),p.D*(p.L-1),-2*p.D] i
  ![a,b,c] j

/-- Either one whole interval or its two exact halves. A split is needed
for a few convex principal-reserve quadratics near the start of the chain. -/
def QuadraticCover (a b c V : ℝ) : Prop :=
  QuadraticSigns a b c V ∨
    (QuadraticSigns a b c (V/2) ∧
      QuadraticSigns (a+b*(V/2)+c*(V/2)^2) (b+2*c*(V/2)) c (V/2))

theorem QuadraticCover.uniform {a b c V : ℝ} (h : QuadraticCover a b c V)
    (hV : 0 < V) : ∃ r, 0 < r ∧ ∀ v ∈ Icc (0:ℝ) V, r ≤ a+b*v+c*v^2 := by
  rcases h with h | ⟨h1,h2⟩
  · exact h.uniform hV
  · obtain ⟨r1,hr1,hh1⟩ := h1.uniform (by positivity)
    obtain ⟨r2,hr2,hh2⟩ := h2.uniform (by positivity)
    refine ⟨min r1 r2,lt_min hr1 hr2,?_⟩
    intro v hv
    by_cases hhalf : v ≤ V/2
    · exact (min_le_left _ _).trans (hh1 v ⟨hv.1,hhalf⟩)
    · have hh := hh2 (v-V/2) ⟨by linarith,by linarith [hv.2]⟩
      have he : a+b*(V/2)+c*(V/2)^2+(b+2*c*(V/2))*(v-V/2)+c*(v-V/2)^2 =
          a+b*v+c*v^2 := by ring
      rw [he] at hh
      exact (min_le_right _ _).trans hh

def GeometrySigns (p : Params) : Prop :=
  ∀ i, QuadraticCover (geometryCoeff p i 0) (geometryCoeff p i 1)
    (geometryCoeff p i 2) (p.c-crossing p)

theorem GeometrySigns.uniform {p : Params} (h : GeometrySigns p)
    (hV : 0 < p.c-crossing p) :
    ∃ r, 0 < r ∧ ∀ i, ∀ v ∈ Icc (0:ℝ) (p.c-crossing p),
      r ≤ geometryCoeff p i 0+geometryCoeff p i 1*v+geometryCoeff p i 2*v^2 := by
  classical
  have hh i := (h i).uniform hV
  choose r hr hri using hh
  let rs := Finset.univ.image r
  have hne : rs.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  refine ⟨rs.min' hne,?_,?_⟩
  · obtain ⟨i,hi,he⟩ := Finset.mem_image.mp (Finset.min'_mem rs hne)
    rw [←he]
    exact hr i
  · intro i v hv
    exact (Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i,by simp,rfl⟩)).trans (hri i v hv)

def nominalGeometry (p : Params) (v : ℝ) : Fin 6 → ℝ :=
  let w := crossing p+v
  let u := p.A*v/(1+p.D*v)
  ![1/10-6*u, p.c0*(1-6*u)-(w-u),
    1-p.B+(p.L-2)*w-9/2*u,
    1/20+3/2*(1-p.B)+(3/2*p.L-5/2)*w-9/2*u,
    1-p.B+(p.L-1)*w-4*u, 1/3-2*w-3*u]

theorem geometry_identity (p : Params) (v : ℝ) (hD : 1+p.D*v ≠ 0) (i : Fin 6) :
    geometryCoeff p i 0+geometryCoeff p i 1*v+geometryCoeff p i 2*v^2 =
      (1+p.D*v)*nominalGeometry p v i := by
  fin_cases i <;> norm_num [geometryCoeff,nominalGeometry] <;> field_simp <;> ring

theorem GeometrySigns.nominal_uniform {p : Params} (h : GeometrySigns p)
    (hV : 0 < p.c-crossing p) (hD : 0 ≤ p.D) :
    ∃ r, 0 < r ∧ ∀ v ∈ Icc (0:ℝ) (p.c-crossing p),
      ∀ i, r ≤ nominalGeometry p v i := by
  obtain ⟨m,hm,hall⟩ := h.uniform hV
  let cap := 1+p.D*(p.c-crossing p)
  have hcap : 0 < cap := by dsimp [cap]; positivity
  refine ⟨m/cap,div_pos hm hcap,?_⟩
  intro v hv i
  have hv0 := hv.1
  have hW : 0 < 1+p.D*v := by positivity
  have hWcap : 1+p.D*v ≤ cap := by
    dsimp [cap]
    nlinarith [mul_le_mul_of_nonneg_left hv.2 hD]
  have hh := hall i v hv
  rw [geometry_identity p v hW.ne' i] at hh
  have hr : m/cap*(1+p.D*v) ≤ m := by
    calc m/cap*(1+p.D*v) ≤ m/cap*cap :=
      mul_le_mul_of_nonneg_left hWcap (div_pos hm hcap).le
      _ = m := div_mul_cancel₀ _ hcap.ne'
  nlinarith

def cutNumerator (p : Params) (phi : ℝ) : ℝ := phi*p.L0*p.A
def cutIntercept (p : Params) : ℝ := p.L0-p.L+(6*p.B0-p.L0)*p.A
def matchedCut (p : Params) (phi v : ℝ) : ℝ :=
  cutNumerator p phi/(cutIntercept p+(p.L0-p.L)*p.D*v)
def clippedExcess (p : Params) (w : ℝ) : ℝ :=
  max 0 (min (p.c-crossing p) (w-crossing p))
def cut (p : Params) (phi w : ℝ) : ℝ := matchedCut p phi (clippedExcess p w)

theorem clippedExcess_mem {p : Params} (hV : 0 ≤ p.c-crossing p) (w : ℝ) :
    clippedExcess p w ∈ Icc (0:ℝ) (p.c-crossing p) := by
  exact ⟨le_max_left _ _, max_le hV (min_le_left _ _)⟩

theorem clippedExcess_eq {p : Params} {w : ℝ} (hw : w ∈ Icc (crossing p) p.c) :
    clippedExcess p w = w-crossing p := by
  unfold clippedExcess
  rw [min_eq_right (by linarith [hw.2]),max_eq_right (by linarith [hw.1])]

theorem matchedCut_den_pos {p : Params} (hL : p.L < p.L0) (hD : 0 ≤ p.D)
    (hE : 0 < cutIntercept p) {v : ℝ} (hv : 0 ≤ v) :
    0 < cutIntercept p+(p.L0-p.L)*p.D*v := by
  have hd := sub_pos.mpr hL
  positivity

theorem matchedCut_bounds {p : Params} {phi V v : ℝ}
    (hL : p.L < p.L0) (hD : 0 ≤ p.D) (hE : 0 < cutIntercept p)
    (hK : 0 ≤ cutNumerator p phi) (hv : v ∈ Icc (0:ℝ) V) :
    matchedCut p phi V ≤ matchedCut p phi v ∧ matchedCut p phi v ≤ matchedCut p phi 0 := by
  have hEv := matchedCut_den_pos hL hD hE hv.1
  have hEV := matchedCut_den_pos hL hD hE (hv.1.trans hv.2)
  unfold matchedCut
  constructor
  · apply div_le_div_of_nonneg_left hK hEv
    nlinarith [mul_le_mul_of_nonneg_left hv.2 (mul_nonneg (sub_pos.mpr hL).le hD)]
  · simp only [mul_zero,add_zero]
    apply div_le_div_of_nonneg_left hK hE
    exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (sub_pos.mpr hL).le hD) hv.1)

private theorem low_identity_algebra (l A v W E phi dl g : ℝ)
    (hW : W ≠ 0) (hE : E ≠ 0) (he : E = dl*W+g*A) :
    l*(A*v/W)-(phi*l*A/E)*(dl*v+g*(A*v/W)) = (1-phi)*l*(A*v/W) := by
  field_simp [hW,hE]
  rw [he]
  ring

theorem matchedCut_low_identity (p : Params) (phi v : ℝ)
    (hW : 1+p.D*v ≠ 0) (hE : cutIntercept p+(p.L0-p.L)*p.D*v ≠ 0) :
    p.L0*(p.A*v/(1+p.D*v))-
      matchedCut p phi v*((p.L0-p.L)*v+(6*p.B0-p.L0)*(p.A*v/(1+p.D*v))) =
      (1-phi)*p.L0*(p.A*v/(1+p.D*v)) := by
  exact low_identity_algebra p.L0 p.A v (1+p.D*v)
    (cutIntercept p+(p.L0-p.L)*p.D*v) phi (p.L0-p.L) (6*p.B0-p.L0) hW hE
    (by unfold cutIntercept; ring)

/-- Finite quadratic signs and rational endpoint cuts for a curved step.
The full HIGH count is a separate certificate. -/
structure GeometryCertificate (p : Params) (phi floor : ℝ) : Prop where
  face : DSFace p.B0 p.L0 p.c0 p.B p.L p.c
  B0_pos : 0 < p.B0
  A_pos : 0 < p.A
  A_lt : p.A < 1
  D_nonneg : 0 ≤ p.D
  phi_pos : 0 < phi
  phi_le : phi ≤ 1
  floor_pos : 0 < floor
  width_pos : 0 < p.c-crossing p
  cut_intercept : 0 < cutIntercept p
  lower_cut : floor ≤ matchedCut p phi (p.c-crossing p)
  upper_cut : matchedCut p phi 0 ≤ 3/4
  overshoot : matchedCut p phi 0*(6*p.B0-p.L0) ≤ p.L0
  signs : GeometrySigns p

namespace GeometryCertificate
variable {p : Params} {phi floor : ℝ} (g : GeometryCertificate p phi floor)
include g

theorem L0_pos : 0 < p.L0 := by linarith [g.face.one_lt_L,g.face.L_lt]

theorem cut_bounds (w : ℝ) : cut p phi w ∈ Icc floor (3/4:ℝ) := by
  have hK : 0 ≤ cutNumerator p phi := by
    unfold cutNumerator
    exact (mul_pos (mul_pos g.phi_pos g.L0_pos) g.A_pos).le
  have hb := matchedCut_bounds g.face.L_lt g.D_nonneg g.cut_intercept hK
    (clippedExcess_mem g.width_pos.le w)
  exact ⟨g.lower_cut.trans hb.1,hb.2.trans g.upper_cut⟩

theorem gates (F : ℝ → WeightedFamily)
    (hhigh : ∃ r, 0 < r ∧ ∀ w ∈ Icc (crossing p) p.c,
      HighReserve (F w) p.B p.L w
        (QRH.SilDensitySplit.Hybrid.sel p.A p.D (w-crossing p)) r) :
    Gates p (cut p phi) F := by
  obtain ⟨r,hr,hgeom⟩ := g.signs.nominal_uniform g.width_pos g.D_nonneg
  refine ⟨g.face,g.B0_pos,g.A_pos,g.A_lt,g.D_nonneg,?_,g.width_pos,?_,?_,?_,?_,hhigh,?_⟩
  · intro w
    exact ⟨g.floor_pos.le.trans (g.cut_bounds w).1,(g.cut_bounds w).2⟩
  · intro w hw
    have hv : 0 ≤ w-crossing p := sub_nonneg.mpr hw.1
    have hDv := mul_nonneg g.D_nonneg hv
    have hW : 0 < 1+p.D*(w-crossing p) := by linarith
    have hE := matchedCut_den_pos g.face.L_lt g.D_nonneg g.cut_intercept hv
    rw [cut,clippedExcess_eq hw]
    change 0 ≤ p.L0*(p.A*(w-crossing p)/(1+p.D*(w-crossing p)))-
      matchedCut p phi (w-crossing p)*
        ((p.L0-p.L)*(w-crossing p)+(6*p.B0-p.L0)*(p.A*(w-crossing p)/(1+p.D*(w-crossing p))))
    rw [matchedCut_low_identity p phi _ hW.ne' hE.ne']
    exact mul_nonneg (mul_nonneg (sub_nonneg.mpr g.phi_le) g.L0_pos.le)
      (div_nonneg (mul_nonneg g.A_pos.le hv) hW.le)
  · intro w hw
    by_cases hh : 0 ≤ 6*p.B0-p.L0
    · have hK : 0 ≤ cutNumerator p phi := by
        unfold cutNumerator
        exact (mul_pos (mul_pos g.phi_pos g.L0_pos) g.A_pos).le
      have hb := (matchedCut_bounds g.face.L_lt g.D_nonneg g.cut_intercept hK
        (clippedExcess_mem g.width_pos.le w)).2
      exact (mul_le_mul_of_nonneg_right hb hh).trans g.overshoot
    · exact (mul_nonpos_of_nonneg_of_nonpos
        (g.floor_pos.le.trans (g.cut_bounds w).1) (by linarith)).trans g.L0_pos.le
  · refine ⟨r,hr,?_⟩
    intro w hw
    have h := hgeom (w-crossing p) ⟨by linarith [hw.1],by linarith [hw.2]⟩ 0
    norm_num [nominalGeometry] at h
    change 9/10+r ≤ 1-6*(p.A*(w-crossing p)/(1+p.D*(w-crossing p)))
    linarith
  · refine ⟨r,hr,?_⟩
    intro w hw
    have h := hgeom (w-crossing p) ⟨by linarith [hw.1],by linarith [hw.2]⟩ 1
    norm_num [nominalGeometry] at h
    simpa only [QRH.SilDensitySplit.Hybrid.sel,add_sub_cancel] using h
  · refine ⟨r,hr,?_⟩
    intro w hw
    have h2 := hgeom (w-crossing p) ⟨by linarith [hw.1],by linarith [hw.2]⟩ 2
    have h3 := hgeom (w-crossing p) ⟨by linarith [hw.1],by linarith [hw.2]⟩ 3
    have h4 := hgeom (w-crossing p) ⟨by linarith [hw.1],by linarith [hw.2]⟩ 4
    have h5 := hgeom (w-crossing p) ⟨by linarith [hw.1],by linarith [hw.2]⟩ 5
    norm_num [nominalGeometry] at h2 h3 h4 h5
    simpa only [QRH.SilDensitySplit.Hybrid.sel,add_sub_cancel] using ⟨h2,h3,h4,h5⟩

end GeometryCertificate
#print axioms GeometryCertificate.gates
end
end Qrh.JointDetector.RepeatedMarks.CurvedSourceStep
