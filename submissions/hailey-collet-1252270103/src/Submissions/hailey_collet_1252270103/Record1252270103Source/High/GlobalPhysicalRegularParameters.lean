/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The Newton depth and puncture exponents are chosen at the fixed width cell,
before the ambient slot type. Each assignment prime is charged exactly once. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalPaidSome
import Submissions.hailey_collet_1252270103.Record1252270103StepScalar.Geometry
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.Contract
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open Record1252270103Finite Record1252270103StepScalar

def cellNewtonDepth (amp:ℝ) : ℕ := ⌈4/amp⌉₊

theorem cell_newton_depth (amp:ℝ)(ha:0<amp)(ha1:amp<1) :
    0<amp/2 ∧ amp/2<amp ∧ 2/(amp/2)≤(cellNewtonDepth amp:ℝ) ∧
      (cellNewtonDepth amp:ℝ)*amp<5 ∧
      1+2+2+8+(cellNewtonDepth amp:ℝ)*amp≤20 ∧
      4+(cellNewtonDepth amp:ℝ)*amp+1≤10 := by
  have hlo:=Nat.le_ceil (4/amp)
  have hhi:=Nat.ceil_lt_add_one (show 0≤4/amp by positivity)
  have hmult:=mul_lt_mul_of_pos_right hhi ha
  rw [add_mul,div_mul_cancel₀ _ ha.ne',one_mul] at hmult
  change (cellNewtonDepth amp:ℝ)*amp<4+amp at hmult
  have he:2/(amp/2)=4/amp:=by field_simp;ring
  refine ⟨by positivity,by linarith,?_,by linarith,by linarith,by linarith⟩
  simpa only [he,cellNewtonDepth] using hlo

/-- The actual node supplies the small positive amplification interval.
No cardinality or moving profile enters either mask exponent. -/
theorem node_newton_depth (K:ℚ)(n low:Source)(b:ℝ)(hg:RealGeometry K n low b) :
    0<sourceAReal n low b/2 ∧ sourceAReal n low b/2<sourceAReal n low b ∧
      2/(sourceAReal n low b/2)≤(cellNewtonDepth (sourceAReal n low b):ℝ) ∧
      (cellNewtonDepth (sourceAReal n low b):ℝ)*sourceAReal n low b<5 ∧
      1+2+2+8+(cellNewtonDepth (sourceAReal n low b):ℝ)*sourceAReal n low b≤20 ∧
      4+(cellNewtonDepth (sourceAReal n low b):ℝ)*sourceAReal n low b+1≤10 :=
  cell_newton_depth _ hg.a_pos (hg.a_small.trans (by norm_num))

/-- One original mesh satisfies the parent source, RAW root and full-pool gap.
All three ceilings are fixed before a slot type or its cardinality is chosen. -/
theorem cell_mesh_ceiling (lowMesh highMesh θ amp:ℝ)
    (hlow:0<lowMesh)(hhigh:0<highMesh)(hθ:0<θ)(ha:0<amp) :
    ∃m:ℝ,0<m ∧ ∀mesh:ℝ,0<mesh→mesh≤m→
      mesh≤lowMesh ∧ 100*mesh≤highMesh ∧ 100*mesh≤θ ∧ mesh<amp/2 := by
  refine ⟨min lowMesh (min (highMesh/100) (min (θ/100) (amp/4))),by positivity,?_⟩
  intro mesh hm hcap
  have h₁:=hcap.trans (min_le_left _ _)
  have h₂:mesh≤highMesh/100:=hcap.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h₃:mesh≤θ/100:=hcap.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have h₄:mesh≤amp/4:=hcap.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  exact ⟨h₁,by linarith,by linarith,by linarith⟩
/-- A genuine earlier source, or the checked natural source, fixes one HIGH
mesh before any slot type, source anchor or moving family. -/
theorem selected_high_parent_mesh (high:Option Source)(ε:ℝ)(hε:0<ε)
    (hG:∀h∈high,GlobalSource (h.B:ℝ) (h.L:ℝ) (h.cap:ℝ)) :
    ∃m:ℝ,0<m ∧ ∀mesh:ℝ,mesh≤m→
      (match high with
        | none => mesh≤OAI.SevenEighths.Cycle61MarkedPlain.markedPlainMesh (3/4) ε
        | some h => QRH.Record12518109Existence.UnitFaceSource
          (globalFace (h.B:ℝ) (h.L:ℝ) (h.cap:ℝ)) mesh ε) := by
  cases high with
  | none =>
    exact ⟨_,OAI.SevenEighths.Cycle61MarkedPlain.markedPlainMesh_pos le_rfl hε,fun _ h=>h⟩
  | some h =>
    obtain ⟨m,hm,hsource⟩:=hG h (by simp) ε hε
    exact ⟨m,hm,fun mesh hmesh=>hsource.mono_mesh hmesh⟩

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.cell_newton_depth
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.node_newton_depth
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.cell_mesh_ceiling

#print axioms QRH.Record1252270103Source.High.GlobalPhysical.selected_high_parent_mesh
