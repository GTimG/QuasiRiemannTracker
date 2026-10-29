/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceStep

namespace Qrh.JointDetector.RepeatedMarks.SourceStep
noncomputable section
set_option autoImplicit false
open Set QRH.SilDensitySplit.Density

/-- Every non-HIGH interval expression in one linear-selector source step. -/
def affineIntercepts (p : Params) : Fin 6 → ℝ :=
 ![1/10+6*p.A*crossing p,
   p.c0+(6*p.c0-1)*p.A*crossing p,
   1-p.B+9/2*p.A*crossing p,
   1/20+3/2*(1-p.B)+9/2*p.A*crossing p,
   1-p.B+4*p.A*crossing p,
   1/3+3*p.A*crossing p]
def affineSlopes (p : Params) : Fin 6 → ℝ :=
 ![-6*p.A, -6*p.c0*p.A-1+p.A, p.L-2-9/2*p.A,
   3/2*p.L-5/2-9/2*p.A, p.L-1-4*p.A, -2-3*p.A]

def GeometryEndpoints (p : Params) : Prop :=
 (∀ i, 0 < affineIntercepts p i+affineSlopes p i*crossing p) ∧
 (∀ i, 0 < affineIntercepts p i+affineSlopes p i*p.c)

theorem linear_interval_margin {a b lo hi : ℝ}
 (hlo : 0 < a+b*lo) (hhi : 0 < a+b*hi) :
 ∃ r, 0 < r ∧ ∀ w ∈ Icc lo hi, r ≤ a+b*w := by
 refine ⟨min (a+b*lo) (a+b*hi),lt_min hlo hhi,?_⟩
 intro w hw
 by_cases hb : 0 ≤ b
 · exact (min_le_left _ _).trans (by nlinarith [mul_nonneg hb (sub_nonneg.mpr hw.1)])
 · exact (min_le_right _ _).trans (by nlinarith [mul_nonneg (by linarith : 0 ≤ -b) (sub_nonneg.mpr hw.2)])

theorem GeometryEndpoints.uniform {p : Params} (h : GeometryEndpoints p) :
 ∃ r, 0 < r ∧ ∀ i, ∀ w ∈ Icc (crossing p) p.c,
 r ≤ affineIntercepts p i+affineSlopes p i*w := by
 classical
 have hh i := linear_interval_margin (h.1 i) (h.2 i)
 choose r hr hri using hh
 let rs := Finset.univ.image r
 have hne : rs.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
 refine ⟨rs.min' hne,?_,?_⟩
 · have hm := Finset.min'_mem rs hne
   obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hm
   rw [←he]
   exact hr i
 · intro i w hw
   exact (Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i,by simp,rfl⟩)).trans (hri i w hw)

/-- The crossing width is a lower bound for the retained width/height ratio.
This is the exact inequality used to transport the amplitude derivative. -/
theorem nominal_slot_ratio {p : Params} (hA : 0 ≤ p.A) (hAhi : p.A ≤ 1)
 (hs : 0 ≤ crossing p) {w : ℝ} (hw : crossing p ≤ w) :
 crossing p*(1-6*(p.A*(w-crossing p))) ≤ w-p.A*(w-crossing p) := by
 have hh := mul_nonneg (by nlinarith [mul_nonneg hA hs] :
   0 ≤ 1-p.A+6*p.A*crossing p) (sub_nonneg.mpr hw)
 nlinarith only [hh]

/-- The genuinely finite geometry part of a stage. HIGH is deliberately
absent: its whole density/amplitude certificate is a separate obligation. -/
structure GeometryCertificate (p : Params) : Prop where
 face : DSFace p.B0 p.L0 p.c0 p.B p.L p.c
 B0_pos : 0 < p.B0
 A_pos : 0 < p.A
 A_lt : p.A < 1
 q_mem : p.q ∈ Icc (0:ℝ) (3/4)
 width_pos : 0 < p.c-crossing p
 low_payment : p.q*(p.L0-p.L+(6*p.B0-p.L0)*p.A) ≤ p.L0*p.A
 low_overshoot : p.q*(6*p.B0-p.L0) ≤ p.L0
 endpoints : GeometryEndpoints p

/-- Scalar endpoint data yields a genuine source-step gate only after the
full density/amplitude HIGH reserve has independently been established. -/
theorem gates_of_endpoints {p : Params} {F : WeightedFamily}
 (hface : DSFace p.B0 p.L0 p.c0 p.B p.L p.c)
 (hB0 : 0 < p.B0) (hA : 0 < p.A) (hAhi : p.A < 1)
 (hq : p.q ∈ Icc (0:ℝ) (3/4)) (hw : 0 < p.c-crossing p)
 (hlow : p.q*(p.L0-p.L+(6*p.B0-p.L0)*p.A) ≤ p.L0*p.A)
 (hover : p.q*(6*p.B0-p.L0) ≤ p.L0)
 (hends : GeometryEndpoints p)
 (hhigh : ∃ r, 0 < r ∧ ∀ w ∈ Icc (crossing p) p.c,
   HighReserve F p.B p.L w (p.A*(w-crossing p)) r) : Gates p F := by
 obtain ⟨r,hr,hh⟩ := hends.uniform
 refine ⟨hface,hB0,hA,hAhi,hq,hw,hlow,hover,?_,?_,hhigh,?_⟩
 · refine ⟨r,hr,?_⟩
   intro w hw
   have h := hh 0 w hw
   norm_num [affineIntercepts,affineSlopes] at h
   nlinarith
 · refine ⟨r,hr,?_⟩
   intro w hw
   have h := hh 1 w hw
   norm_num [affineIntercepts,affineSlopes] at h
   nlinarith
 · refine ⟨r,hr,?_⟩
   intro w hw
   have h₂ := hh 2 w hw
   have h₃ := hh 3 w hw
   have h₄ := hh 4 w hw
   have h₅ := hh 5 w hw
   norm_num [affineIntercepts,affineSlopes] at h₂ h₃ h₄ h₅
   constructor
   · nlinarith
   constructor
   · nlinarith
   constructor <;> nlinarith

theorem GeometryCertificate.gates {p : Params} {F : WeightedFamily}
 (h : GeometryCertificate p)
 (hhigh : ∃ r, 0 < r ∧ ∀ w ∈ Icc (crossing p) p.c,
   HighReserve F p.B p.L w (p.A*(w-crossing p)) r) : Gates p F :=
 gates_of_endpoints h.face h.B0_pos h.A_pos h.A_lt h.q_mem h.width_pos
   h.low_payment h.low_overshoot h.endpoints hhigh

end
end Qrh.JointDetector.RepeatedMarks.SourceStep
