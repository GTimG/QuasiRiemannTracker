/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Repeated-mark improved inverse P6 on the original supported Batch rows. Count, retained-long
native fourth and buffered shorter upper are all supplied by genuine sources. -/
import Candidate.C092.transport.MediumInversePriceRepeatRect

namespace QRH.Cycle092.MediumInversePrice
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open HeckeDetectorRawFiber HeckeDetectorWitnessRows
open CenteredMomentWholeSlotDeletion
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorPlainFiberSource
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily
open CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyBands
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.MediumWitness QRH.Cycle092.MediumReplace
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.WholeSlot ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
variable [Geometry.Parameters]

/-- The native short-inverse P6 branch on any further frozen subclass of the literal
same-zero fiber. There is no assumed count, ordinary upper or fourth moment.
The lower descriptor and upper product bounds define the actual response bin.
The source presentation and the retained-long ray remain distinct data. -/
theorem original_rect_repeated_inverse_P6
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (ρ : Qrh.MarkedAnchor.Interface.Contract.AnchorRect)
    (hsource : Qrh.MarkedAnchor.Interface.Contract.UniformInverseRectSource
      Qrh.MarkedAnchor.Interface.Contract.canonicalFamily ρ)
    {N quota : ℝ} (hN : N ≤ 1/2) (hq0 : 0 ≤ quota)
    (hqcap : quota < 3/20) (hqmean : quota < (1-2*N)/2)
    (nativeError : ℝ) (hnativeError : 0 < nativeError)
    (D : BaselineData) (F : BaselineSourceData D)
    (τ : ℝ) (hτ : 0 < τ) (hheight : 4*τ < (1/200 : ℝ)*D.cost)
    (profileBound : ℕ → ℝ) (hprofile : ∀ j, 0 ≤ profileBound j) :
    ∃ inverseMesh : ℝ, 0 < inverseMesh ∧ ∀ _hfine : (∀ j, D.length j ≤ inverseMesh/200),
    ∀ Kbig : ℕ, ∃ mesh : ℝ, 0 < mesh ∧ ∃ order : ℕ, ∃ Cy : ℝ, 0 < Cy ∧
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ηsource : Character) (selectionN : ℕ),
    ∃ Jc : ℕ, ∃ Cc : ℝ, 0 < Cc ∧ ∀ repeats : ℕ,
    ∀ (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
      (hHr : RayOrthogonality.globalUnits rayM ≤ Hr),
    ∀ (W : ℝ → ℂ), ContDiff ℝ ∞ W → Function.support W ⊆ Set.Icc (1 : ℝ) 2 →
    ∀ bΦ : ℝ, 2 ≤ bΦ →
      Function.support (radialMajorant : ℝ → ℂ) ⊆ Set.Iic bΦ →
    ∀ (ηlong η₀ : Character) (Qray : Ideal O),
      Qray ≤ rayM → internalQ Qray η₀ ≠ 0 → internalQ Qray η₀ ≠ ⊤ →
      internalQ Qray η₀ ≤ Ideal.span {(72 : O)} →
    ∃ degree : ℕ, ∃ controls : Finset (ℕ×ℕ), ∃ Cl : ℝ, 0 < Cl ∧
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (padding d threshold lowPay y : ℝ) (idx grid : FreeRow → ℕ),
      (1/200 : ℝ) ≤ d → d ≤ 7/8 → 0 ≤ y → y/d ≤ 22 →
      ProbeAssembly.selected D F padding τ selectionN ηsource Z idx grid →
    ∀ (i k : ℕ) (z : FreeRow → Fin D.N → ℂ) (cutoff T allowance height : ℝ),
      0 ≤ height → 1/2 ≤ bandLower D k → 2*Real.pi*allowance+(3*i : ℕ)*T ≤ height →
    ∀ B : HeckeDetectorBatch.Batch F.modulus ⊤ (Sum Bool (RayQuotient.Characters F.modulus ⊤))
      (Fin D.N) (Z^d) (bandLower D k) D.ε cutoff T allowance i,
      B.rows ⊆ sharedRows D F (Z^(Geometry.h+padding)) Z d threshold lowPay idx grid z i k →
      B.data=sourceMomentData F.modulus ⊤ le_top F.S F.exclusions.prime ηsource →
      B.profile=(fun _ x => (F.w x : ℂ)) → B.upper=(fun _ => 2) →
      B.widths=(fun j => D.length j/d) → (∀ j, (B.external j).re=17/50) →
      (∀ j, |(B.external j).im| ≤ height) →
    ∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
      let fiber := B.fiber bin label left right hne
    ∀ rows : Finset FreeRow, rows ⊆ fiber.rows → rows.Nonempty →
    ∀ inverseSlot : Fin D.N, inverseSlot∈fiber.slots →
      (7/37 : ℝ) ≤ (Kbig : ℝ)*fiber.widths inverseSlot →
    ∀ selectedInverse : Finset (Fin Kbig),
      ρ.Admissible fiber.r ((selectedInverse.card : ℝ)*fiber.widths inverseSlot) 1 →
    ∀ shorter : ShortDataOn D F ηsource Z τ d y idx grid order profileBound rows,
    ∀ (θ : RayQuotient.Characters rayM Hr) (w σ v t e L buffer inverseBuffer X : ℝ)
      (p : Profiles (1/4) (9/4)) (j : Fin 2) (marks : FreeRow → ℂ),
      0 ≤ w → w/d ≤ mesh → (33/50 : ℝ) ≤ σ → σ ≤ (33/50 : ℝ) →
      |v| ≤ height → (repeats : ℝ)*w ≤ d*quota → 0 < X →
      length (Z^d) X ≤ N →
      (∀ u ∈ rows, initialKeep ηlong (internalQ Qray η₀) u.val) →
      (∀ u ∈ rows, Z^(e*w-buffer) ≤
        ‖normalizedSlot ηlong (fixedBadMask*idealGenerator 1) 1 u.val
          (CenteredMomentPrimeSlot.primePool rayM Hr 2 (Z^w))
          (fun I => idealCoeff (relativeCharacter rayM Hr hHr η₀ θ) I *
            HeckePrimeAnnular.annularWeight W (Z^w) σ v I) t (Z^w)‖^2) →
      (∀ u∈rows,(Z^d)^(e*fiber.widths inverseSlot-inverseBuffer) ≤
        ‖HeckeDetectorPhysicalSelection.physical F.modulus ⊤ (fun u : FreeRow => u.val)
          fiber.profile fiber.upper fiber.widths fiber.external (Z^d) u inverseSlot‖^2) →
      (∀ u ∈ rows, ‖marks u‖^2 ≤ Z^(e*L)) →
    (∑ u ∈ rows,
      ‖original ηlong (fixedBadMask*idealGenerator 1) 1 u.val (p.profile j) t X*
        shorter.value u*marks u‖^2) ≤
      Cy*Real.sqrt (12*(1+height)*((Cc*(1+height)^Jc)*K))*
        Real.sqrt (Cl*QuadraticInitialBound.diagonalControl radialMajorant*
          (sourceControl controls (p.profile j))^4*(1+|t|+height)^degree)*
      Z^(d+(2*bandLower D k-1)*y+e*(L-(repeats : ℝ)*w/2)-
        d*((2*bandLower D k-1)*fiber.r+e*((selectedInverse.card : ℝ)*fiber.widths inverseSlot))/2+d*D.ε+
        (d*(2*D.ε+(selectedInverse.card : ℝ)*inverseBuffer+D.t)+d*nativeError+(repeats : ℝ)*buffer)/2) := by
  obtain ⟨inverseMesh,hInverseMesh,hrect⟩ := original_rect_repeated_inverse_count ρ hsource D.t D.t_pos
  refine ⟨inverseMesh,hInverseMesh,?_⟩
  intro hfine Kbig
  obtain ⟨mesh,hm,hnative⟩ := repeated_native_fourth hβ hN hq0 hqcap hqmean
    (by norm_num : (0 : ℝ)<1/200) nativeError hnativeError
  obtain ⟨order,Cy,hCy,hshort⟩ := original_short_on_rows D F τ hτ hheight profileBound hprofile
  let K : ℝ := 1
  have hK : 0 ≤ K := by norm_num [K]
  refine ⟨mesh,hm,order,Cy,hCy,K,hK,?_⟩
  intro ηsource selectionN
  obtain ⟨Jc,Cc,hCc,hcount⟩ := hrect Kbig D.toMomentData F rfl hfine ηsource
  refine ⟨Jc,Cc,hCc,?_⟩
  intro repeats rayM _ Hr hHr W hW hWs bΦ hbΦ hsΦ ηlong η₀ Qray hQray hQ0 hQt hQ72
  obtain ⟨degree,controls,Cl,hCl,hnative⟩ := hnative repeats rayM Hr hHr W hW hWs
    bΦ hbΦ hsΦ ηlong η₀ Qray hQray hQ0 hQt hQ72
  refine ⟨degree,controls,Cl,hCl,?_⟩
  filter_upwards [hcount,hshort ηsource selectionN,hnative] with Z hc hs hn
  refine ⟨hc.1,?_⟩
  intro padding d threshold lowPay y idx grid hd hd' hy hy' hsel i k z cutoff T allowance height
    hh ha hfreq B hB hdata hprofile' hupper hwidth hreal hexternal
    bin label left right hne
  dsimp only
  intro rows hrows hneRows inverseSlot hInvSlot hSupply selectedInverse hInvAdmissible shorter θ w σ v t e L buffer inverseBuffer X p j marks
    hw hwm hσlo hσhi hv hquota hX hXN hkeep hamp hInverseAttain hmarks
  let fiber := B.fiber bin label left right hne
  have hZp : 0 < Z := zero_lt_one.trans hc.1
  have hcard := hc.2 d hd (bandLower D k) D.ε cutoff T allowance i B hdata hprofile'
    hupper hwidth hreal bin label left right hne height hh ha hexternal hfreq rows hrows hneRows inverseSlot hInvSlot hSupply selectedInverse e inverseBuffer hInvAdmissible hInverseAttain
  rw [←Real.rpow_mul hZp.le] at hcard
  have hcard' : (rows.card : ℝ) ≤ (12*(1+height)*((Cc*(1+height)^Jc)*K))*
      Z^(d*(1-((2*bandLower D k-1)*fiber.r+e*((selectedInverse.card : ℝ)*fiber.widths inverseSlot)))+d*(2*D.ε+(selectedInverse.card : ℝ)*inverseBuffer+D.t)) := by
    convert hcard using 1 <;> dsimp only [BaselineData.toMomentData,K,fiber] <;> congr 2 <;> ring
  have hparent : ∀ u ∈ fiber.rows, u ∈ B.rows := by
    intro u hu
    simp only [fiber,HeckeDetectorBatch.Batch.fiber,HeckeDetectorFiberPartition.toFiber,
      HeckeDetectorFiberPartition.fiber,Finset.mem_filter] at hu
    exact hu.1
  have hsubset : rows ⊆ sharedRows D F (Z^(Geometry.h+padding)) Z d threshold lowPay idx grid z i k := by
    intro u hu
    apply hB
    exact hparent u (hrows hu)
  have hupperShort := hs.2 padding d threshold lowPay y idx grid hd hd' hy hy' hsel
    i k z rows hsubset shorter
  have hrad : ∀ u ∈ rows, rowNorm u ≤ Z^d := by
    intro u hu
    exact fiber.row_norm u (hrows hu)
  have hfourth := hn d hd θ w σ v t height e buffer hw hwm hσlo hσhi hh hv hquota
    p j X hX hXN rows hkeep hrad hamp
  have hfourth' : (∑ u ∈ rows,
      ‖original ηlong (fixedBadMask*idealGenerator 1) 1 u.val (p.profile j) t X‖^4) ≤
      (Cl*QuadraticInitialBound.diagonalControl radialMajorant*
        (sourceControl controls (p.profile j))^4*(1+|t|+height)^degree)*
      Z^(d-e*((repeats : ℝ)*w)+(d*nativeError+(repeats : ℝ)*buffer)) := by
    convert hfourth using 1 <;> congr 2 <;> ring
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
  have result := same_rows_price rows
    (fun u => original ηlong (fixedBadMask*idealGenerator 1) 1 u.val (p.profile j) t X)
    shorter.value marks Z d (2*bandLower D k-1) y e L ((repeats : ℝ)*w)
    (((2*bandLower D k-1)*fiber.r+e*((selectedInverse.card : ℝ)*fiber.widths inverseSlot))) (d*(2*D.ε+(selectedInverse.card : ℝ)*inverseBuffer+D.t))
    (d*nativeError+(repeats : ℝ)*buffer) (d*D.ε)
    (12*(1+height)*((Cc*(1+height)^Jc)*K))
    (Cl*QuadraticInitialBound.diagonalControl radialMajorant*
      (sourceControl controls (p.profile j))^4*(1+|t|+height)^degree) Cy
    hZp (by positivity) (by positivity) hCy.le hcard' hfourth' hupperShort hmarks
  convert result using 1 <;> congr 2 <;> ring

#print axioms original_rect_repeated_inverse_P6
end
end QRH.Cycle092.MediumInversePrice
