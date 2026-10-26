/- Reindex the SAME native root geometry without transporting its data fields.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeCanonicalRootPackagePort
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Cycle153ActualColumn
noncomputable section
open scoped Classical HeckeNotation
open HeckeFamily Cycle153Reachable Cycle153ReachableGeometry
variable {alpha : Type}{M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=alpha) M H}

/-- Only dependent propositions are transported. Source coordinates,
plane and rounded position are literal fields of the same geometry. -/
def rootGeometryFieldwiseTransport
    {u1 u2 X11 X12 X21 X22 : ℝ}{J1 J2 : Finset alpha}
    (hu : u1=u2)(hJ : J1=J2)(h1 : X11=X12)(h2 : X21=X22)
    (g : NativeChildGeometry C (0:Fin 4) C.globalBase 1 u1 J1 X11 X21) :
    NativeChildGeometry C (0:Fin 4) C.globalBase 1 u2 J2 X12 X22 where
  coordinates:=g.coordinates
  prefixRows:=g.prefixRows
  physical_nonnegative:=g.physical_nonnegative
  unit_eq:=by cases hu;exact g.unit_eq
  unit_floor:=by cases hu;exact g.unit_floor
  unit_le_one:=by cases hu;exact g.unit_le_one
  length_eq:=by cases hu;cases hJ;cases h1;cases h2;exact g.length_eq
  slots_eq:=by cases hJ;exact g.slots_eq
  plane:=g.plane
  plane_eq:=by cases hu;exact g.plane_eq
  position:=g.position
  rounded:=by cases hu;cases hJ;cases h1;cases h2;exact g.rounded
  facts:=g.facts
  window:=by cases hu;cases hJ;cases h1;cases h2;exact g.window
  overshoot:=by cases hu;cases hJ;cases h1;cases h2;exact g.overshoot

@[simp] theorem rootGeometryFieldwiseTransport_coordinates
    {u1 u2 X11 X12 X21 X22 : ℝ}{J1 J2 : Finset alpha}
    (hu : u1=u2)(hJ : J1=J2)(h1 : X11=X12)(h2 : X21=X22)
    (g : NativeChildGeometry C (0:Fin 4) C.globalBase 1 u1 J1 X11 X21) :
    (rootGeometryFieldwiseTransport hu hJ h1 h2 g).coordinates=g.coordinates:=rfl

/-- The existing history and mask facts follow the same reindex; no new
source, physical quantity, energy estimate or count is introduced. -/
def rootPackageFieldwiseTransport
    {u1 u2 X11 X12 X21 X22 : ℝ}{J1 J2 : Finset alpha}{P1 P2 : Ideal O}
    (hu : u1=u2)(hJ : J1=J2)(h1 : X11=X12)(h2 : X21=X22)(hP : P1=P2)
    (pack : {geom : NativeChildGeometry C (0:Fin 4) C.globalBase 1 u1 J1 X11 X21 //
      Real.logb C.globalBase (P1.absNorm:ℝ)≤
        modelMissing (0:Fin 4) geom.coordinates+modelReduction (0:Fin 4) geom.coordinates+
          1/1000000000000000 ∧ (P1.absNorm:ℝ)≤(C.globalBase^u1)^(20:ℝ)}) :
    {geom : NativeChildGeometry C (0:Fin 4) C.globalBase 1 u2 J2 X12 X22 //
      Real.logb C.globalBase (P2.absNorm:ℝ)≤
        modelMissing (0:Fin 4) geom.coordinates+modelReduction (0:Fin 4) geom.coordinates+
          1/1000000000000000 ∧ (P2.absNorm:ℝ)≤(C.globalBase^u2)^(20:ℝ)} :=
  ⟨rootGeometryFieldwiseTransport hu hJ h1 h2 pack.val,by
    constructor
    · change Real.logb C.globalBase (P2.absNorm:ℝ)≤_
      rw [←hP]
      exact pack.property.1
    · rw [←hu,←hP]
      exact pack.property.2⟩

@[simp] theorem rootPackageFieldwiseTransport_coordinates
    {u1 u2 X11 X12 X21 X22 : ℝ}{J1 J2 : Finset alpha}{P1 P2 : Ideal O}
    (hu : u1=u2)(hJ : J1=J2)(h1 : X11=X12)(h2 : X21=X22)(hP : P1=P2)
    (pack : {geom : NativeChildGeometry C (0:Fin 4) C.globalBase 1 u1 J1 X11 X21 //
      Real.logb C.globalBase (P1.absNorm:ℝ)≤
        modelMissing (0:Fin 4) geom.coordinates+modelReduction (0:Fin 4) geom.coordinates+
          1/1000000000000000 ∧ (P1.absNorm:ℝ)≤(C.globalBase^u1)^(20:ℝ)}) :
    (rootPackageFieldwiseTransport hu hJ h1 h2 hP pack).val.coordinates=pack.val.coordinates:=rfl
end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.rootPackageFieldwiseTransport_coordinates
