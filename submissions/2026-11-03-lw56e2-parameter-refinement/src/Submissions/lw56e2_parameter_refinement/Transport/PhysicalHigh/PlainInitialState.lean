/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/PhysicalHigh/PlainInitialState.lean
Original SHA-256: 19e29ece298d0c28f01a8c4d5f64b68f00f783cd11b2f2ba95caca8146a39eb7
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalHigh.PlainRetained
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainMarkedState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainCapacity
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.Bands
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorRawBranches

/-!
# Actual initial plain energy state with an independent capacity parameter

The construction uses the actual retained detector rows and coefficient
identity. The capacity parameter is explicit, allowing the terminal
energy certificate at kappa=3/4 to be used without an old positive gap.
-/

namespace LW56e2.Transport.PhysicalHigh

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate Topology ContDiff
open Filter

open OAI OAI.SevenEighths
open CenteredMomentDetectorPlainMarkedState
open HeckeFamily HeckeDyadic HeckeDetectorRawFiber HeckeDetectorBatch HeckePrimeAnnular
open HeckeInverseAmplification HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorPlainStateDictionary CenteredMomentDetectorPlainExceptional
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorPlainCapacity
open CenteredMomentDetectorPlainSlotProfile CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorDictionary CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open ConcretePrimeRowBridge ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}
variable {Δ:ℝ}{D:Parameters.HighData Δ}

theorem source_batch_marked_initial (S:ProbeFinalAssembly.SourceData D)(N:ℕ)(ell:Fin N→ℝ)
    (hell:∀j,0<ell j)(κ:ℝ):
    ∃bΦ:ℝ,0<bΦ ∧ ∀η:Character,∀δ:ℝ,0<δ→
      ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤rowNorm u)→
      ∀d:ℝ,(1/200:ℝ)≤d→∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin N)
        (Z^d) a ε tstar T allowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=>ell s/d)→
      (∀s,B.upper s=2)→(∀s,(B.external s).re=17/50)→
      ∀bin label J K,∀hne:(B.fiberRows bin label J K).Nonempty,
      ∀selected:Finset (Fin N),selected⊆B.slots→
      let F:=B.fiber bin label J K hne;
      2*F.m+6*κ*(∑s∈selected,F.widths s)≤1→
      let η₀:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label;
      ∃state:NaturalState (Z^d) 0 bΦ,
        state.character=η₀ ∧ state.fixedModulus=internalQ (sourceFixedIdeal S) η₀ ∧
        state.puncture=1 ∧ state.radial.profile=radialMajorant ∧ state.radial.scale=Z^d ∧
        state.radial.keep=initialKeep η₀ (internalQ (sourceFixedIdeal S) η₀) ∧
        state.width=1+δ ∧
        length (Z^d) ((Z^d)^F.m)+length (Z^d) ((Z^d)^F.m)+
          6*κ*(∑s:selected,F.widths s.val)≤state.width ∧
        (∀s:selected,0<F.widths s.val ∧ F.widths s.val≤F.mesh) ∧
        ∀j k:ℕ,∀σ t:ℝ,
        (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
          ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
          ((Z^d)^F.m) σ t*F.physicalProduct selected u‖^2)≤
          energy state.character state.mask 1 0
            ((detectorProfiles F.reverse j k σ t).profile 0)
            ((detectorProfiles F.reverse j k σ t).profile 1)
            (fun s:selected=>CenteredMomentPrimeSlot.primePool S.modulus ⊤ 2 ((Z^d)^(F.widths s.val)))
            (fun (s:selected) I=>idealCoeff η₀.inverse I*
              annularWeight (fun x=>conj (S.W x)) ((Z^d)^(F.widths s.val)) (33/50)
                (-(F.external s.val).im) I)
            (fun s:selected=>(Z^d)^(F.widths s.val)) ((Z^d)^F.m) ((Z^d)^F.m)
            state.radial.keep state.radial.profile state.radial.scale := by
  obtain ⟨bΦ,hbΦ,hs⟩:=radialMajorant_support_bound
  refine ⟨bΦ,hbΦ,?_⟩
  intro η δ hδ
  filter_upwards [source_label_modulus_eventually S η δ hδ,source_batch_plain_retained S N ell hell η] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro rows hrows d hd a ε tstar T allowance i B hB hdata hprofile hwidth hupper hreal
    bin label J K hne selected hselected F hcap η₀
  have hdpos:0<d:=by linarith
  have hU:1<Z^d:=Real.one_lt_rpow hz.1 hdpos
  have hη:(η₀.modulus.absNorm:ℝ)≤(Z^d)^δ:=hz.2 label d hd
  let state:=initialState η₀ (internalQ (sourceFixedIdeal S) η₀) radialMajorant bΦ
    (Z^d) δ hU.le hδ.le hs radialMajorant_nonneg hη
  refine ⟨state,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,?_⟩
  · exact marked_capacity F hU selected _ δ hδ.le hcap
  · intro s
    exact ⟨F.widths_pos s.val (hselected s.property),F.widths_mesh s.val (hselected s.property)⟩
  · intro j k σ t
    have hb:=hr.2 rows hrows d hdpos.ne' a ε tstar T allowance i B hB hdata hprofile hwidth
      bin label J K hne selected j k σ t
    have hprof:∀s x,F.profile s x=S.W x:=by
      intro s x
      change B.profile s x=S.W x
      rw [hprofile,S.complex_eq]
    have he:=retained_eq_initial_energy S F hprof hupper η₀ (internalQ (sourceFixedIdeal S) η₀) selected
      (fun s _=>hreal s) radialMajorant bΦ δ hU.le hδ.le hs radialMajorant_nonneg hη j k σ t
    exact hb.trans_eq he

end
end LW56e2.Transport.PhysicalHigh
