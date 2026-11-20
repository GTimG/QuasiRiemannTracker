/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
All original masks and native reverse orientations share early constants. -/
import Candidate.C092.transport.MixedMiddleReturnPaidSliceActualSelected
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true
namespace QRH.Cycle092.MixedMiddleReturn
noncomputable section
attribute [local reducible] QRH.Record1252270103Return.GenericPhysical.BaselineData.toMomentData
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open HeckeDetectorRawFiber HeckeDetectorWitnessRows
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.SelectedNonfloor QRH.Cycle092.MixedUpperFinal QRH.Cycle090
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- One genuine supplier for all finite original masks and both native
orientations, with C and degree before every transport, height and live bank. -/
theorem earlier_P1_paid_finite
    (h : ℝ) (hh : hLower ≤ h) (hh' : h ≤ hUpper)
    (hgeometry : (inferInstance : Geometry.Parameters)=ActualGeometry.parameters h hh hh')
    (hP1 : RawTicket.EarlierP1) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    {decrement epsilon : ℝ} (hdec : 0<decrement ∧ decrement ≤ 1/1000) (hepsilon : 0<epsilon) :
    ∃mp : ℝ→ℝ,∃cap : ℝ,(∀t,0<t → 0 < mp t) ∧ 0<cap ∧
    ∀(D : BaselineData) (F : BaselineSourceData D),
      (∀s,D.length s ≤ mp D.t/200) → (∀s,D.length s ≤ Cycle25.sourceMesh D.t/200) →
      D.ε ≤ 1/10000000 → D.t ≤ 1/10000000 →
      2*HeckeZeroSupremum.beta-1 ≤ D.momentKappa →
    ∀(massEps xi ann loss : ℝ),0 < massEps → 0<xi → 0 ≤ ann →
      2*xi+ann ≤ witnessCollar → 0<loss →
    ∀η : Character,∃M : ℕ,∃C : ℝ,0<C ∧ (∀s,D.length s ≤ cap/200) ∧
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(J : Finset (Fin D.N)) (reverse : Bool),
    ∀Q : PaidSliceInput h decrement epsilon xi ann loss massEps cap (sourceWidthMin D) reverse D F J η Z,
    mainFront D J Z*(∑u∈commonIndices Q.bank.currentSlice.fiber.rows Q.bank.common,
      ‖paidOriginalSmall D F J η Z Q.x Q.z (Z^Geometry.y) Q.bank.baseScale Q.r u.val (Q.data u)*
        mainProduct D F J u.val Z Q.z‖) ≤
    C*(1+Q.bank.height)^M*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-4*Geometry.ell/25)*
      Q.bank.baseScale^(finalPower Q.bank.a Q.bank.d sourceCost Q.outerFee (theta-1/2500000000000)) := by
  classical
  obtain ⟨mesh,cap,hm,hcap,hpacket⟩ := earlier_P1_paid_small_slice h hh hh' hgeometry hP1 hβ hdec hepsilon
  let mp := fun t=>min (mesh t) cap
  refine ⟨mp,cap,(fun t ht=>lt_min (hm t ht) hcap),hcap,?_⟩
  intro D F hf hs he ht hβD massEps xi ann loss hmass hxi hann hcollar hloss η
  have hfmesh : ∀s,D.length s ≤ mesh D.t/200 := fun s=>(hf s).trans
    (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hfcap : ∀s,D.length s ≤ cap/200 := fun s=>(hf s).trans
    (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  let T := Finset (Fin D.N)×Bool
  have hall (t : T) := hpacket D F hfmesh hs he ht D.momentKappa D.momentKappa_lo D.momentKappa_hi hβD
    t.1 massEps hmass t.2 xi ann loss (sourceWidthMin D) hxi hann hcollar hloss (sourceWidthMin_pos D) η
  choose degree C hC hp using hall
  let M := Finset.univ.sup degree
  let C0 := ∑t : T,C t
  have hC0 : 0<C0 := Finset.sum_pos (fun t _=>hC t) Finset.univ_nonempty
  have hdegree (t : T) : degree t ≤ M := Finset.le_sup (Finset.mem_univ t)
  have hCle (t : T) : C t ≤ C0 := Finset.single_le_sum (fun j _=>(hC j).le) (Finset.mem_univ t)
  refine ⟨M,C0,hC0,hfcap,?_⟩
  have hAll : ∀ᶠ Z : ℝ in atTop,∀t : T,1<Z ∧ _ := Filter.eventually_all.mpr hp
  filter_upwards [hAll] with Z hAll
  refine ⟨(hAll (∅,false)).1,?_⟩
  intro J reverse Q
  have hbound := (hAll (J,reverse)).2 Q
  have hH : 1 ≤ 1+Q.bank.height := by linarith [Q.bank.height_nonneg]
  have hcoef : C (J,reverse)*(1+Q.bank.height)^(degree (J,reverse)) ≤ C0*(1+Q.bank.height)^M :=
    mul_le_mul (hCle _) (pow_le_pow_right₀ hH (hdegree _)) (by positivity) hC0.le
  have hZ0 : 0<Z := zero_lt_one.trans (hAll (J,reverse)).1
  exact hbound.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef
      (Real.rpow_nonneg (Real.rpow_nonneg hZ0.le _) _)) (Real.rpow_nonneg hZ0.le _))
      (Real.rpow_nonneg (Real.rpow_nonneg hZ0.le _) _))

#print axioms earlier_P1_paid_finite
end
end QRH.Cycle092.MixedMiddleReturn
