/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual original source dictionary supplies the moving middle return's
whole presentation, with fixed pre-scale controls and no keep/Q/source-record
premise. Earlier P.1 and the literal physical/raw-window guards are explicit. -/
import Candidate.C092.transport.SourceWindowCompactOriginalGates
set_option autoImplicit false
namespace QRH.Cycle092.SourceWindowCompact
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional
open CenteredMomentDetectorEnergyInitialState CenteredMomentEnergyBands
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorDictionary HeckeDetectorRawFiber
open Cycle25ProbeFinalAssembly
open QRH.Cycle092.StrongPair QRH.Cycle092.RawTicket QRH.Cycle092.Mixed
open QRH.Cycle092.MixedMiddleReturn
local notation "O" => ActualEisensteinCubic.O

/-- SourceWindowCompact's analytic source join for the genuine original
weighted source. QL/QW and both initial keeps are discharged internally.
The source mesh precedes the fixed source/slot/ray dictionary; all source
metadata precede Z,d,nref,z, the actual offset fiber and physical height. -/
theorem uniform_original_presentations (hP1 : EarlierP1)
    {decrement epsilon : ℝ} (hd : 0<decrement ∧ decrement≤1/1000)
    (hepsilon : 0<epsilon) :
    ∃ mesh : ℝ,0 < mesh ∧
    ∀ (Slot : Type) [Fintype Slot] [DecidableEq Slot],
    ∀ {D0 : Cycle25.Weighted.MomentData} (F0 : WeightedSourceData D0) (etaOuter : Character),
    ∀ (bPhi : ℝ),2≤bPhi → Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bPhi →
    ∀ (dmin wmin : ℝ),0<dmin → 0<wmin →
    ∃ degree : ℕ,∃ controls : Finset (ℕ×ℕ),∃ C : ℝ,0<C ∧
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀ d : ℝ,dmin≤d →
    ∀ (n z quota : ℝ),nLo≤n → n≤nHi → widthLo≤z → z≤widthHi → 0≤quota →
      quota ≤ max 0 (QRH.Cycle090.sourceWidth n z-decrement) →
    ∀ (label : Sum Bool (RayQuotient.Characters F0.modulus ⊤))
      {WitnessLabel : Type} {a eps cutoff T allowance : ℝ} {i : ℕ}
      (F : Fiber F0.modulus ⊤ WitnessLabel Slot (Z^d) a eps cutoff T allowance i),
      (∀u∈F.rows,Z^(1/100:ℝ)≤rowNorm u) →
      F.mesh ≤ mesh → (∀s∈F.slots,wmin≤F.widths s) →
      (∀s∈F.slots,F.profile s=F0.W) → (∀s∈F.slots,F.upper s=2) →
      (∀s∈F.slots,(F.external s).re=17/50) →
    ∀ height : ℝ,0≤height → (∀s∈F.slots,|(F.external s).im|≤height) →
    ∃ P : WholePresentation F0.modulus ⊤ le_top F0.S F0.exclusions.prime F
      (sourceMomentBase F0.modulus ⊤ le_top F0.S F0.exclusions.prime etaOuter label) controls,
      P.seed.N=n ∧ P.seed.Y=z ∧ P.seed.l=quota ∧ P.seed.degree=degree ∧
      P.seed.C=C ∧ P.seed.epsilon=epsilon ∧ P.seed.height=height := by
  obtain ⟨mesh,hm,hsource⟩ := uniform_native_presentations hP1 hd hepsilon
  refine ⟨mesh,hm,?_⟩
  intro Slot _ _ D0 F0 etaOuter bPhi hbPhi hPhi dmin wmin hdmin hwmin
  have hg := original_source_dictionary_gates F0
  let Q := Cycle25WeightedNumeratorPhysical.weighted_sourceFixedIdeal F0
  let etaW := sourceMomentBase F0.modulus ⊤ le_top F0.S F0.exclusions.prime etaOuter
  obtain ⟨degree,controls,C,hC,hpres⟩ := hsource Slot F0.modulus ⊤ le_top hg.2.2.2.2.1
    F0.S F0.exclusions.prime F0.W (F0.W.smooth ⊤) F0.complex_support bPhi hbPhi hPhi etaW
    (fun _=>Q) (fun _=>Q)
    (fun _=>hg.1) (fun _=>(hg.2.2.2.2.2 _).1) (fun _=>(hg.2.2.2.2.2 _).2.1)
    (fun _=>(hg.2.2.2.2.2 _).2.2)
    (fun _=>hg.1) (fun _=>(hg.2.2.2.2.2 _).1) (fun _=>(hg.2.2.2.2.2 _).2.1)
    (fun _=>(hg.2.2.2.2.2 _).2.2) dmin wmin hdmin hwmin
  refine ⟨degree,controls,C,hC,?_⟩
  filter_upwards [hpres,original_source_keeps_on_rows F0 etaOuter] with Z hpres hkeep
  refine ⟨hpres.1,?_⟩
  intro d hd n z quota hn0 hn1 hz0 hz1 hquota hq label WitnessLabel a eps cutoff T allowance i
    F hrows hmesh hwidth hprofile hupper hreal height hh him
  exact hpres.2 d hd n z quota hn0 hn1 hz0 hz1 hquota hq label F hmesh hwidth hprofile
    hupper hreal height hh him (hkeep F.rows hrows label).1 (hkeep F.rows hrows label).2

end
end QRH.Cycle092.SourceWindowCompact
#print axioms QRH.Cycle092.SourceWindowCompact.uniform_original_presentations
