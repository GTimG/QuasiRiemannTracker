/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The paid native energy sum is exactly the original free-row common sum.
Reflection data are required only on the genuine selected fiber. -/
import Candidate.C092.transport.MixedMiddleReturnPaidSlice
set_option autoImplicit false
set_option allowUnsafeReducibility true
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open ProbeRowRadicalConductor HeckeDetectorRawFiber Cycle25.Numerator Cycle25.Weighted.Numerator
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.SelectedNonfloor
attribute [local reducible] BaselineData.toMomentData
variable [Geometry.Parameters]

/-- Extension by zero is only a bookkeeping operation outside the genuine
selected fiber. No reflection object on a principal row is asserted. -/
def paidOriginalOnRows (D : BaselineData) (F : BaselineSourceData D)
    (J : Finset (Fin D.N)) (η : Character) (Z : ℝ) (x z : ℂ) (rows : Finset FreeRow)
    (data : ∀u : rows,PhysicalReflectionData F.S F.exclusions.prime u.val)
    (Y U : ℝ) (r : TopData.Row) (u : FreeRow) : ℂ :=
  if hu : u∈rows then paidOriginalSmall D F J η Z x z Y U r u (data ⟨u,hu⟩) else 0

/-- This is the literal original per-mask common sum; only the excluded
carrier is zero-extended. Every counted common row uses its genuine data. -/
theorem paid_common_original (D : BaselineData) (F : BaselineSourceData D)
    (J : Finset (Fin D.N)) (η : Character) (Z : ℝ) (x z : ℂ)
    (rows common : Finset FreeRow) (hsub : common⊆rows)
    (data : ∀u : rows,PhysicalReflectionData F.S F.exclusions.prime u.val)
    (Y U : ℝ) (r : TopData.Row) :
    (∑u∈commonIndices rows common,‖paidOriginalSmall D F J η Z x z Y U r u.val (data u)*
      mainProduct D F J u.val Z z‖)=
    ∑u∈common,‖paidOriginalOnRows D F J η Z x z rows data Y U r u*mainProduct D F J u Z z‖ := by
  rw [←common_sum rows common hsub]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [paidOriginalOnRows,dite_eq_left u.property]

/-- The actual native witness/physical height stays in the displayed
polynomial factor. No live height exponent is absorbed into a reserve. -/
theorem paid_native_height [ActualGeometry.WidenedCoreBounds] (M : ℕ) {Z d tau : ℝ} (i : ℕ)
    (hZ : 1 ≤ Z) (hd : d ≤ 7/8) (ht : 0 ≤ tau) :
    (1+PacketJoin.nativeHeight Z d tau i)^M ≤
      (2*Real.pi+2)^M*(3+(3*i+1:ℕ)*Z^tau)^M := by
  have hb : 0 ≤ 1+PacketJoin.nativeHeight Z d tau i := by
    unfold PacketJoin.nativeHeight
    positivity
  calc
    _ ≤ ((2*Real.pi+2)*(3+(3*i+1:ℕ)*Z^tau))^M :=
      pow_le_pow_left₀ hb (PacketJoin.nativeHeight_le Z d tau i hZ hd ht) M
    _ = _ := mul_pow _ _ _

#print axioms paid_common_original
#print axioms paid_native_height
end
end QRH.Cycle092.MixedMiddleReturn
