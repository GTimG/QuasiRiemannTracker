/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Native four-exit count/payment on literal actual bank common classes. -/
import Candidate.C092.transport.MixedUpperFinalPresentation
import Candidate.C092.transport.MixedOutsidePaidAll
set_option autoImplicit false
set_option allowUnsafeReducibility true
namespace QRH.Cycle092.MixedUpperFinal
noncomputable section
attribute [local reducible] QRH.Record1252270103Return.GenericPhysical.BaselineData.toMomentData
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition HeckeDetectorPhysicalSelection
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.MediumWitness QRH.Cycle092.MixedOffsetBank QRH.Cycle092.MixedOffsetCount
open QRH.Cycle092.PacketJoinE49 QRH.Cycle090 QRH.Cycle092.MixedTicketTails
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- Earlier/native source counts, rather than a supplied count, handle all
four outside-anchor first-short common classes of the actual bank. -/
theorem actual_bank_outside_count_paid (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκ : 2*HeckeZeroSupremum.beta-1 ≤ (3/4:ℝ)) :
    ∃mesh : ℝ→ℝ,(∀t,0<t → 0 < mesh t) ∧
    ∀ (D : BaselineData) (F : BaselineSourceData D),
      (∀s,D.length s ≤ mesh D.t/200) → (∀s,D.length s ≤ Cycle25.sourceMesh D.t/200) →
    ∀η : Character,∃J : ℕ,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀ (P : TransportParameters D) (d a : ℝ) (rows : Finset FreeRow) (z : ℂ)
      (bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t) (t₀ γ τ : ℝ) (i : ℕ)
      (B : CellBank D F η Z d a rows z bin t₀ γ τ i)
      (hd : (1/200:ℝ) ≤ d) (hdhi : d ≤ 7/8),
      51/100<a → a ≤ 7/8 → D.ε ≤ 1/10000000 → D.t ≤ 1/10000000 →
      (∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u) →
      z.re=17/50 → |z.im| ≤ (3*i+1:ℕ)*Z^τ →
    ∀ (σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)))
      (hne : ((B.layout P hd hdhi).common σ).Nonempty) (j : Offset),
      firstShort (inverseLength (Z^d) σ)=some j →
      ¬centralLengths (inverseLength (Z^d) σ j) (ordinaryLength (Z^d) σ j) →
    ∀r : TopData.Row,r∈TopData.rows →
      r.box.Contains (2*a-1,classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)) →
      t₀=Return.cutoffI (2*a-1) (classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)) →
      γ=(Mixed.rowGamma r.box r.B:ℝ) →
      hLower ≤ Geometry.h → Geometry.h ≤ hUpper → Geometry.ell=Physical.ell →
      originalDlow r ≤ d → d ≤ Geometry.h+rowPad →
    ∀moment mass fee : ℝ,
      d*(3*countLoss D.ε P.mesh D.t/4+moment/4+mass)+fee+2*rowPad ≤ 7*RawTicket.oldFee →
    ∃R : ℝ,
      (((B.layout P hd hdhi).common σ).card:ℝ) ≤
        192*(1+QRH.Cycle092.PacketJoin.nativeHeight Z d τ i)*
          (C*(1+QRH.Cycle092.PacketJoin.nativeHeight Z d τ i)^J)*(Z^d)^(R+countLoss D.ε P.mesh D.t) ∧
      SelectedNonfloor.rowPrice (2*a-1)
        (classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1))
        (R+countLoss D.ε P.mesh D.t) d sourceCost+d*(moment/4+mass)+fee ≤ theta-RawTicket.oldFee := by
  obtain ⟨mesh,hm,hsource⟩:=MixedOutsidePaid.actual_outside_count_paid hβ hκ
  refine ⟨mesh,hm,?_⟩
  intro D F hf hs η
  obtain ⟨J,C,hC,hsource⟩:=hsource D.toMomentData F hf hs η
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hsource] with Z h
  refine ⟨h.1,?_⟩
  intro P d a rows z bin t₀ γ τ i B hd hdhi ha hahi he ht hl hz him σ hne j first hout
    r hr hp hbase hγ hh hh' hell hdlo hdh moment mass fee hbudget
  let L:=B.layout P hd hdhi
  let height:=QRH.Cycle092.PacketJoin.nativeHeight Z d τ i
  have hZpos : 0 < Z := zero_lt_one.trans h.1
  have hheight:0 ≤ height:=by dsimp [height,QRH.Cycle092.PacketJoin.nativeHeight];positivity
  have hf:2*Real.pi*(Z^d)^(τ/(2*(7/8:ℝ)))+(3*i:ℕ)*Z^τ ≤ height:=by
    dsimp [height,QRH.Cycle092.PacketJoin.nativeHeight]
    push_cast
    have hpos:=Real.rpow_nonneg (zero_lt_one.trans h.1).le τ
    linarith
  have hext:∀s,|((B.presented P hd hdhi hl hz j).batch.external s).im| ≤ height:=by
    intro s
    change |z.im| ≤ height
    exact him.trans (le_add_of_nonneg_left (by positivity))
  have hb:=original_bank_admission hr hp
  have hξ:offset γ j ≤ RawTicket.gammaMax:=
    (offset_bounds γ (by rw [hγ];exact hb.2.1) j).2.trans (by rw [hγ];exact hb.2.2.1)
  have hlong: (B.slice P hd hdhi hl hz σ hne j).fiber.r<1:=
    (L.first_short σ hne j first).1
  have hstar:cutoff t₀ γ j=Return.cutoffI (2*a-1)
      ((B.slice P hd hdhi hl hz σ hne j).fiber.q/(2*a-1))-offset γ j:=by
    change t₀-offset γ j=Return.cutoffI (2*a-1)
      (classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1))-offset γ j
    exact congrArg (fun t : ℝ=>t-offset γ j) hbase
  exact h.2 d a (cutoff t₀ γ j) (Z^τ) ((Z^d)^(τ/(2*(7/8:ℝ)))) height (offset γ j) i
    hd ha (by linarith) ht he hheight hf hξ (B.presented P hd hdhi hl hz j)
    (B.slice P hd hdhi hl hz σ hne j) hext hlong hstar hout (L.common σ)
    (L.common_subset σ hne j) r hr hp hh hh' hell hdlo hdh moment mass fee hbudget

#print axioms actual_bank_outside_count_paid
end
end QRH.Cycle092.MixedUpperFinal
