import QRH.Detector.DynamicMomentInput
import QRH.Detector.DetectorPlainMarkedSlots

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

theorem dynamic_source_input_slots {Δ : ℝ} {D : Parameters.HighData Δ}
    (F : SourceData D) (nslots : ℕ) (κ : ℝ) (hκ : (13/18 : ℝ) ≤ κ)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ κ)
    (hbeta : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    PositiveSlotsSourceInput F nslots (dynamicMesh D.t) κ := by
  intro bΦ hbΦ
  obtain ⟨_, degree, S, hbound⟩ := actual_uniform_moment (α := Fin nslots) F.modulus ⊤ le_top
    (fun x => conj (F.W x)) 1 2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2 (D.t/4)
    (by norm_num) (conjugate_source_support F)
    (Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hbΦ (by norm_num) (by norm_num)
    (by linarith [D.t_pos]) hbeta
  refine ⟨degree, S, ?_⟩
  intro η₀
  obtain ⟨Cz, Cp, hCz, hCp, hbound⟩ := hbound η₀ (sourceFixedIdeal F)
    (sourceFixedIdeal_le_modulus F) (source_fixed_gates F η₀).1
    (internalQ_ne_top _ (sourceFixedIdeal_ne_top F) η₀) (source_fixed_gates F η₀).2.2.2
  exact ⟨Cp, hCp, hbound.mono (fun U h => h.2.2 κ hκ hκbeta)⟩

theorem actual_source_batch_plain_marked_slots {Δ:ℝ}{D:Parameters.HighData Δ}
    (S:SourceData D)(nslots:ℕ)(lengths:Fin nslots→ℝ)(hpos:∀s,0<lengths s)
    (κ:ℝ)(hκ:(13/18:ℝ)≤κ)(hκbeta:2*HeckeZeroSupremum.beta-1≤κ)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hfine:∀j,lengths j≤dynamicMesh D.t/200):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
    1<Z ∧ ∀rows:Finset FreeRow,(∀u∈rows,Z^(1/100:ℝ)≤rowNorm u)→
    ∀d:ℝ,(1/200:ℝ)≤d→∀(a tstar T allowance:ℝ)(i:ℕ)
    (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin nslots)
      (Z^d) a D.ε tstar T allowance i),B.rows⊆rows→
    B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
    B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=>lengths s/d)→
    (∀s,B.upper s=2)→(∀s,(B.external s).re=17/50)→
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0≤height→(∀s,|(B.external s).im|≤height)→
    let F:=B.fiber bin label left right hne;
    ∀selected:Finset (Fin nslots),selected⊆F.slots→
      2*F.m+6*κ*(∑s∈selected,F.widths s)≤1→
    ∀j k:ℕ,j+k≤2→∀σ∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z^d)^F.m) σ t*F.physicalProduct selected u‖^2)≤
        (C*(1+height)^J)*(Z^d)^(1+D.t):= by
  exact source_batch_plain_marked_slots S nslots lengths hpos (dynamicMesh D.t) κ
    (dynamicMesh_pos D.t D.t_pos) hfine (dynamic_source_input_slots S nslots κ hκ hκbeta hbeta)

end SevenEighths.QRHDynamicSlotMomentInput
end
end OAI
