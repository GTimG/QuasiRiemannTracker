/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The finite earlier source bank supplies actual whole physical presentations
uniformly before the live scale, reference pair, offset fiber and radius. -/
import Candidate.C092.transport.SourceWindowCompactPresentation
set_option autoImplicit false
namespace QRH.Cycle092.SourceWindowCompact
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional
open CenteredMomentDetectorEnergyInitialState CenteredMomentEnergyBands
open CenteredMomentDetectorPlainFiberSource HeckeDetectorRawFiber
open QRH.Cycle092.StrongPair QRH.Cycle092.RawTicket QRH.Cycle092.Mixed
open QRH.Cycle092.MixedMiddleReturn
local notation "O" => ActualEisensteinCubic.O

/-- One source degree, finite control set, constant and threshold precede all
live scales, radii, reference pairs, labels, actual offset fibers and physical
heights. Native whole-mark identities and finite-label prime-hole removal are
discharged here; the explicit row keeps are the original two exclusions. -/
theorem uniform_native_presentations (hP1 : EarlierP1)
    {decrement epsilon : ℝ} (hd : 0<decrement ∧ decrement≤1/1000)
    (hepsilon : 0<epsilon) :
    ∃ mesh : ℝ,0 < mesh ∧
    ∀ (Slot : Type) [Fintype Slot] [DecidableEq Slot],
    ∀ (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
      (hH : RayOrthogonality.globalUnits M≤H),M≤Ideal.span {fixedBadMask} →
    ∀ (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P),
    ∀ (V : ℝ→ℂ),ContDiff ℝ ∞ V → Function.support V⊆Set.Icc (1:ℝ) 2 →
    ∀ (bPhi : ℝ),2≤bPhi → Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bPhi →
    ∀ {Label : Type*} [Fintype Label] (etaW : Label→Character) (QL QW : Label→Ideal O),
      (∀j,QL j≤M) → (∀j,internalQ (QL j) (fixedSourcePrincipal S hS)≠0) →
      (∀j,internalQ (QL j) (fixedSourcePrincipal S hS)≠⊤) →
      (∀j,internalQ (QL j) (fixedSourcePrincipal S hS)≤Ideal.span {(72:O)}) →
      (∀j,QW j≤M) → (∀j,internalQ (QW j) (etaW j)≠0) →
      (∀j,internalQ (QW j) (etaW j)≠⊤) →
      (∀j,internalQ (QW j) (etaW j)≤Ideal.span {(72:O)}) →
    ∀ (Vmin wmin : ℝ),0<Vmin → 0<wmin →
    ∃ degree : ℕ,∃ controls : Finset (ℕ×ℕ),∃ C : ℝ,0<C ∧
    ∀ᶠ U : ℝ in atTop,1<U ∧ ∀ radius : ℝ,Vmin≤radius →
    ∀ (n z quota : ℝ),nLo≤n → n≤nHi → widthLo≤z → z≤widthHi → 0≤quota →
      quota ≤ max 0 (QRH.Cycle090.sourceWidth n z-decrement) →
    ∀ (j : Label) {WitnessLabel : Type} {a eps cutoff T allowance : ℝ} {i : ℕ}
      (F : Fiber M H WitnessLabel Slot (U^radius) a eps cutoff T allowance i),
      F.mesh ≤ mesh → (∀s∈F.slots,wmin≤F.widths s) →
      (∀s∈F.slots,F.profile s=V) → (∀s∈F.slots,F.upper s=2) →
      (∀s∈F.slots,(F.external s).re=17/50) →
    ∀ height : ℝ,0≤height → (∀s∈F.slots,|(F.external s).im|≤height) →
      (∀u∈F.rows,initialKeep (fixedSourcePrincipal S hS)
        (internalQ (QL j) (fixedSourcePrincipal S hS)) u.val) →
      (∀u∈F.rows,initialKeep (etaW j) (internalQ (QW j) (etaW j)) u.val) →
    ∃ P : WholePresentation M H hH S hS F (etaW j) controls,
      P.seed.N=n ∧ P.seed.Y=z ∧ P.seed.l=quota ∧ P.seed.degree=degree ∧
      P.seed.C=C ∧ P.seed.epsilon=epsilon ∧ P.seed.height=height := by
  obtain ⟨mesh,hm,hsource⟩ := uniform_live_reference_source hP1 hd hepsilon
  refine ⟨mesh,hm,?_⟩
  intro Slot _ _ M _ H hH hM S hS V hV hVs bPhi hbPhi hPhi Label _ etaW QL QW
    hQLray hQL0 hQLtop hQL72 hQWray hQW0 hQWtop hQW72 Vmin wmin hVmin hwmin
  have hstar : ContDiff ℝ ∞ (fun x=>star (V x)) := Complex.conjCLE.contDiff.comp hV
  have hstars : Function.support (fun x=>star (V x))⊆Set.Icc (1:ℝ) 2 := by
    intro x hx
    exact hVs (by simpa only [Function.mem_support,star_ne_zero] using hx)
  obtain ⟨degree,controls,C,hC,hpair⟩ := hsource Slot M H hH (fun x=>star (V x)) hstar hstars
    bPhi hbPhi hPhi (fun _ : Label=>fixedSourcePrincipal S hS) etaW
    (fun _ : Label=>fixedSourcePrincipal S hS) etaW QL QW
    hQLray hQL0 hQLtop hQL72 hQWray hQW0 hQWtop hQW72 Vmin hVmin
  refine ⟨degree,controls,C,hC,?_⟩
  filter_upwards [hpair,finite_label_annuli_eventually
    (fun _ : Label=>fixedSourcePrincipal S hS) etaW hVmin hwmin] with U hpair hlarge
  refine ⟨hlarge.1,?_⟩
  intro radius hradius n z quota hn0 hn1 hz0 hz1 hquota hq j WitnessLabel a eps cutoff T allowance i
    F hmesh hwidth hprofile hupper hreal height hh him hkeepL hkeepW
  let P := wholePresentation_of_native M H hH S hS F (etaW j) controls n z quota bPhi mesh
    epsilon C degree V (QL j) (QW j)
    (hpair radius hradius n z hn0 hn1 hz0 hz1 quota hq j)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hlarge.1) _) hquota hm.le hmesh hM hVs
    hprofile hupper hreal height hh him
    (fun s hs=>(hlarge.2 radius (F.widths s) hradius (hwidth s hs) j).1)
    (fun s hs=>(hlarge.2 radius (F.widths s) hradius (hwidth s hs) j).2) hkeepL hkeepW
  exact ⟨P,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end
end QRH.Cycle092.SourceWindowCompact
#print axioms QRH.Cycle092.SourceWindowCompact.uniform_native_presentations
