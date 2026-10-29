/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.ActualCoreCount

/-! Actual selected-word short count. The finite moment inputs are the
fields proved from the parent source in ActualCoreCount; this module
performs their finite repeated-word and actual-witness composition. -/
namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped Classical BigOperators
open Set OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDyadic HeckeDetectorWitnessRows
open HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount HeckeDetectorDyadicProfiles

abbrev InverseTests (height : ℝ) := Fin 3 × Icc (0:ℝ) 1 × Icc (-height) height
abbrev PlainTests (height : ℝ) := {p : ℕ×ℕ // p.1+p.2≤2} × Icc (0:ℝ) 1 × Icc (-height) height

/-- Each selected word is first estimated with fixed coefficients; the
finite multiplicity dictionary is paid only after all derivative tests. -/
theorem short_count_from_fields {Label Slot : Type} [Fintype Slot] [DecidableEq Slot]
    {M : Ideal HeckeFamily.O} [NeZero M] {H : Subgroup (HeckeFamily.O⧸M)ˣ}
    {hH : RayOrthogonality.globalUnits M≤H}
    {base anchor : Label→Character} {bad : Label→Ideal HeckeFamily.O}
    {W : ℝ→ℂ} {U Aroot : ℝ}
    (N : RootedBatch (Slot:=Slot) M H hH base anchor bad W U Aroot)
    (rows : Finset FreeRow) (hrows : rows⊆N.rows) (χ : FreeRow→Label→Character)
    (a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U) (ha : 1/2≤a)
    (witness : ∀u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (Jdy Kdy : Fin (dyadicLength U))
    (hlabel : ∀u∈rows,(witness u).label=label)
    (hJ : ∀u∈rows,(witness u).left=Jdy) (hKdy : ∀u∈rows,(witness u).right=Kdy)
    (B L c δ β smin loss mesh τ zmax C εm height lengthLoss : ℝ) (K : ℕ)
    (error : Slot→ℝ) (hC : 0≤C) (hheight : 0≤height) (hε : 0≤ε)
    (hν : 0<2*a-1) (hνhi : 2*a-1≤3/4) (hδ : 0≤δ) (hδν : δ≤2*a-1)
    (hB0 : 0≤B) (hB : B≤1) (hL : 3/2≤L) (hlen0 : 0≤lengthLoss)
    (hwm : ∀s∈N.slots,N.widths s≤mesh) (herr : ∀s∈N.slots,0≤error s)
    (hβ : 0<β) (hsmin : 0<smin) (hs : smin≤∑s∈N.slots,N.widths s)
    (hupper : ∀u∈N.rows,∀s∈N.slots,‖N.Q u s‖^2≤U^(N.widths s+error s))
    (herrors : (∑s∈N.slots,error s)≤loss)
    (hlower : ∀u∈N.rows,U^((δ+β)*(∑s∈N.slots,N.widths s)-loss)≤∏s∈N.slots,‖N.Q u s‖^2)
    (hbudget : 4*loss≤β*smin) (hm : 0≤mesh)
    (hKI : zmax/(β*smin/2)+1≤(K:ℝ))
    (hcapI : max 0 ((1-Real.logb U ((2:ℝ)^Jdy.val))/2-τ)≤zmax)
    (hcapP : max 0 (min c ((B-2*Real.logb U ((2:ℝ)^Kdy.val))/L)-τ)≤zmax)
    (hlength : max (crossingCut (2*a-1) (δ/(2*(2*a-1))) 2 (2*(δ/(2*(2*a-1)))*c))
      (crossingCut (2*a-1) (δ/(2*(2*a-1))) (2-4*(δ/(2*(2*a-1)))/L)
        (2*(δ/(2*(2*a-1)))*B/L)) ≤
      Real.logb U ((2:ℝ)^Jdy.val)+Real.logb U ((2:ℝ)^Kdy.val)+lengthLoss)
    (hfreq : 2*Real.pi*allowance+(3*i:ℕ)*T≤height)
    (hinverse : ∀selected : Finset (Slot×Fin K),selected⊆(N.copy K).slots →
      (∑s∈selected,(N.copy K).widths s)≤max 0 ((1-Real.logb U ((2:ℝ)^Jdy.val))/2-τ) →
      ∀n : ℕ,n≤2 → ∀σ∈Icc (0:ℝ) 1,∀freq∈Icc (-height) height,
      (∑u∈rows,‖polynomial (χ u label) true ((logProfile^[n])
        (inverseTest U tstar (Real.logb U ((2:ℝ)^Jdy.val))))
        (U^(Real.logb U ((2:ℝ)^Jdy.val))) σ freq*(∏s∈selected,(N.copy K).Q u s)‖^2)≤C*U^(1+εm))
    (hplain : ∀selected : Finset (Slot×Fin K),selected⊆(N.copy K).slots →
      (∑s∈selected,(N.copy K).widths s)≤max 0 (min c ((B-2*Real.logb U ((2:ℝ)^Kdy.val))/L)-τ) →
      ∀j k : ℕ,j+k≤2 → ∀σ∈Icc (0:ℝ) 1,∀freq∈Icc (-height) height,
      (∑u∈rows,‖polynomial (χ u label) false ((logProfile^[j]) positiveAnnular)
        (U^(Real.logb U ((2:ℝ)^Kdy.val))) σ freq*
        polynomial (χ u label) false ((logProfile^[k]) positiveAnnular)
        (U^(Real.logb U ((2:ℝ)^Kdy.val))) σ freq*(∏s∈selected,(N.copy K).Q u s)‖^2)≤C*U^(1+εm)) :
    (rows.card:ℝ) ≤ (192*(1+height)*((Fintype.card (Finset (Slot×Fin K)):ℝ)*C))*
      U^(rawRepeatedCountRate B L c (2*a-1) δ+(2*a-1)*lengthLoss+
        (δ*τ+4*ε+δ*mesh+εm)) := by
  let r := Real.logb U ((2:ℝ)^Jdy.val)
  let m := Real.logb U ((2:ℝ)^Kdy.val)
  let zi := max 0 ((1-r)/2-τ)
  let zp := max 0 (min c ((B-2*m)/L)-τ)
  have hselectI := response_subcollections N error δ β smin loss mesh zi zmax K hU hwm herr hδ hβ hsmin hs
    hupper herrors hlower hbudget hm (le_max_left _ _) hcapI hKI
  have hselectP := response_subcollections N error δ β smin loss mesh zp zmax K hU hwm herr hδ hβ hsmin hs
    hupper herrors hlower hbudget hm (le_max_left _ _) hcapP hKI
  let DI := fun (test : InverseTests height) u => polynomial (χ u label) true
    ((logProfile^[test.1.val]) (inverseTest U tstar r)) (U^r) test.2.1.val test.2.2.val
  let DP := fun (test : PlainTests height) u => polynomial (χ u label) false
    ((logProfile^[test.1.val.1]) positiveAnnular) (U^m) test.2.1.val test.2.2.val*
    polynomial (χ u label) false ((logProfile^[test.1.val.2]) positiveAnnular) (U^m) test.2.1.val test.2.2.val
  have hbound : 0≤C*U^(1+εm) := mul_nonneg hC (Real.rpow_nonneg (zero_lt_one.trans hU).le _)
  obtain ⟨QI,hQI,hrawI⟩ := chosen_subcollection_moments rows (N.copy K).slots (N.copy K).widths (N.copy K).Q
    U (δ*(zi-mesh)) zi DI (fun _=>C*U^(1+εm)) (fun _=>hbound)
    (fun u hu=>by obtain ⟨T,hT,hlo,hhi,he⟩:=hselectI u (hrows hu);exact ⟨T,hT,hhi,he⟩)
    (fun test selected hT hwidth=>hinverse selected hT hwidth test.1.val (by omega)
      test.2.1.val test.2.1.property test.2.2.val test.2.2.property)
  obtain ⟨QP,hQP,hrawP⟩ := chosen_subcollection_moments rows (N.copy K).slots (N.copy K).widths (N.copy K).Q
    U (δ*(zp-mesh)) zp DP (fun _=>C*U^(1+εm)) (fun _=>hbound)
    (fun u hu=>by obtain ⟨T,hT,hlo,hhi,he⟩:=hselectP u (hrows hu);exact ⟨T,hT,hhi,he⟩)
    (fun test selected hT hwidth=>hplain selected hT hwidth test.1.val.1 test.1.val.2 test.1.property
      test.2.1.val test.2.1.property test.2.2.val test.2.2.property)
  have hiResponse (u : FreeRow) (hu : u∈rows) : U^(δ*((1-r)/2-τ)-δ*mesh)≤‖QI u‖^2 := by
    apply (Real.rpow_le_rpow_of_exponent_le hU.le ?_).trans (hQI u hu)
    have hz : (1-r)/2-τ≤zi := le_max_right _ _
    nlinarith only [mul_le_mul_of_nonneg_left hz hδ]
  have hpResponse (u : FreeRow) (hu : u∈rows) : U^(δ*(min c ((B-2*m)/L)-τ)-δ*mesh)≤‖QP u‖^2 := by
    apply (Real.rpow_le_rpow_of_exponent_le hU.le ?_).trans (hQP u hu)
    have hz : min c ((B-2*m)/L)-τ≤zp := le_max_right _ _
    nlinarith only [mul_le_mul_of_nonneg_left hz hδ]
  apply short_actual_fiber_count rows χ U a ε tstar T allowance i hU ha witness label Jdy Kdy hlabel hJ hKdy
    QI QP B L c δ τ (δ*mesh) εm ((Fintype.card (Finset (Slot×Fin K)):ℝ)*C) height lengthLoss
    (mul_nonneg (Nat.cast_nonneg _) hC) hheight hε hν hνhi hδ hδν hB0 hB hL hlen0 hlength
    hiResponse hpResponse hfreq
  · intro n hn σ hσ freq hf
    have hh := hrawI (⟨n,by omega⟩,⟨σ,hσ⟩,⟨freq,hf⟩)
    convert hh using 1
    ring
  · intro j k hjk σ hσ freq hf
    have hh := hrawP (⟨(j,k),hjk⟩,⟨σ,hσ⟩,⟨freq,hf⟩)
    convert hh using 1
    ring

end
end Qrh.JointDetector.RepeatedMarks
