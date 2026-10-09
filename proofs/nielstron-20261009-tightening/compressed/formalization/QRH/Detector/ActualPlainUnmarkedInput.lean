import QRH.Detector.DynamicMomentInput
import QRH.Detector.DetectorPlainMarkedSlots
import QRH.Detector.PlainUnmarkedSlots

/-! Arbitrary independent physical slot vector, actual detector row polynomials.
The energy premise is discharged from the extended analytic width induction. -/
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Filter
namespace SevenEighths.QRHDynamicSlotMomentInput
open HeckeFamily ProbeFinalAssembly CenteredMomentEnergyBands
open CenteredMomentEnergyWidthRanges CenteredMomentDetectorPlainMomentParameters
open CenteredMomentDetectorPlainSlotProfile CenteredMomentNaturalFixedRaySource
open ProbeDetectorPlainMarkedFineField QRHPlainMoment
open CenteredMomentDetectorEnergyInitialState

open QRHDynamicMomentInput
open HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles ProbeHighRowFamily
open CenteredMomentDetectorDictionary

theorem actual_zero_source_input {Δ : ℝ} {D : Parameters.HighData Δ}
    (F : SourceData D) (hbeta : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    ∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0<A ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal F) η₀) (1/4) (9/4)
        ProbeDetectorPlainUnmarkedField.radialSupportUpper 0 1 2 (D.t/4) U degree control A := by
  obtain ⟨_, degree, control, hbound⟩ := actual_uniform_moment (α := Fin 0) F.modulus ⊤ le_top
    (fun x => conj (F.W x)) 1 2 (1/4) (9/4) ProbeDetectorPlainUnmarkedField.radialSupportUpper
    0 1 (33/50) (33/50) 2 (D.t/4)
    (by norm_num) (conjugate_source_support F)
    (Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) ProbeDetectorPlainUnmarkedField.radialSupportUpper_spec.1
    (by norm_num) (by norm_num) (by linarith [D.t_pos]) hbeta
  refine ⟨degree, control, ?_⟩
  intro η₀
  obtain ⟨Cz, Cp, hCz, hCp, hbound⟩ := hbound η₀ (sourceFixedIdeal F)
    (sourceFixedIdeal_le_modulus F) (source_fixed_gates F η₀).1
    (internalQ_ne_top _ (sourceFixedIdeal_ne_top F) η₀) (source_fixed_gates F η₀).2.2.2
  exact ⟨Cz, hCz, hbound.mono (fun U h => h.2.1)⟩

theorem actual_source_batch_plain_unmarked_slots {Δ:ℝ} (D:Parameters.HighData Δ)
    (S:ProbeFinalAssembly.SourceData D)
    (nslots:ℕ)(lengths:Fin nslots→ℝ)(hpos:∀s,0<lengths s)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta):
    ∃Jheight:ℕ,∀η:Character,∃C:ℝ,0<C ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤rowNorm u)→
      ∀d:ℝ,(1/200:ℝ)≤d→∀(a tstar T heightAllowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin nslots)
        (Z^d) a D.ε tstar T heightAllowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=>lengths s/d)→
      ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
      ∀height:ℝ,0≤height→∀j k:ℕ,j+k≤2→
      ∀σ∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      let F:=B.fiber bin label left right hne;
      let value:=∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z^d)^F.m) σ t‖^2;
      value≤C*(1+height)^Jheight*(Z^d)^(max 1 (2*F.m)+D.t) ∧
      value≤C*(1+height)^Jheight*max (Z^d) (((Z^d)^F.m)^2)*(Z^d)^D.t := by
  exact ProbeDetectorPlainUnmarkedRestrictedField.source_batch_plain_unmarked_slots D S nslots lengths hpos
    (actual_zero_source_input S hbeta)

end SevenEighths.QRHDynamicSlotMomentInput
end
end OAI
