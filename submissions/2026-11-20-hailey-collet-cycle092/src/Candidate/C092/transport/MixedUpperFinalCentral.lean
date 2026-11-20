/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Source-backed sufficient-count or true narrow middle on actual bank classes. -/
import Candidate.C092.transport.MixedUpperFinalMiddleClamp
import Candidate.C092.transport.MixedInnerActualWidthSupplier
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
open QRH.Cycle092.PacketJoinE49 QRH.Cycle090
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- All native counts and the narrow physical source interval are derived.
The caller supplies only the actual selected bank and literal geometric branch. -/
theorem actual_bank_central_routes (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    ∃mesh : ℝ→ℝ,(∀t,0<t → 0 < mesh t) ∧
    ∀ (D : BaselineData) (F : BaselineSourceData D),
      (∀s,D.length s ≤ mesh D.t/200) → (∀s,D.length s ≤ Cycle25.sourceMesh D.t/200) →
      D.ε ≤ 1/10000000 → D.t ≤ 1/10000000 →
    ∀κ : ℝ,7/10 ≤ κ → κ ≤ 3/4 → 2*HeckeZeroSupremum.beta-1 ≤ κ →
    ∀η : Character,∃K : CountConstants,∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀ (P : TransportParameters D) (cap : ℝ) (hcap : 0<cap) (hfine : ∀s,D.length s ≤ cap/200)
      (d a : ℝ) (rows : Finset FreeRow) (z : ℂ)
      (bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t) (t₀ γ τ : ℝ) (i : ℕ)
      (B : CellBank D F η Z d a rows z bin t₀ γ τ i)
      (hZ : 1<Z) (hd : (1/200:ℝ) ≤ d) (hdhi : d ≤ 7/8)
      (ha : 51/100<a) (hahi : a ≤ 7/8)
      (hl : ∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u) (hz : z.re=17/50)
      (him : |z.im| ≤ (3*i+1:ℕ)*Z^τ)
      (r : TopData.Row) (hr : r∈TopData.rows)
      (hp : r.box.Contains (2*a-1,classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)))
      (ht : t₀=Return.cutoffI (2*a-1) (classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)))
      (hg : γ=(Mixed.rowGamma r.box r.B:ℝ)) (hs : D.ε ≤ 3*witnessCollar)
      (σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)))
      (hne : ((B.layoutCap P hd hdhi cap hcap hfine).common σ).Nonempty) (j : Offset)
      (first : firstShort (inverseLength (Z^d) σ)=some j)
      (central : centralLengths (inverseLength (Z^d) σ j) (ordinaryLength (Z^d) σ j)),
    let M:=B.middleCap P cap hcap hfine hZ hd hdhi ha hahi hl hz him r hr hp ht hg hs σ hne j first central
    (4*(Mixed.rowBudget r.B:ℝ)/3 ≤ M.delta*M.centered ∧
      (M.common.card:ℝ) ≤ M.coefficient K*M.baseScale^(M.R-4*(Mixed.rowBudget r.B:ℝ)/3+M.loss)) ∨
    (Mixed.widthLo ≤ M.currentSlice.fiber.m ∧ M.currentSlice.fiber.m ≤ Mixed.widthHi ∧ M.CountConclusion K) := by
  obtain ⟨mesh,hm,hsource⟩:=MixedInnerActualWidth.actual_inner_width_branches hβ
  refine ⟨mesh,hm,?_⟩
  intro D F hf hs he ht κ hk hk' hκ η
  obtain ⟨K,hsource⟩:=hsource D.toMomentData F hf hs he ht κ hk hk' hκ η
  refine ⟨K,?_⟩
  filter_upwards [hsource] with Z h
  refine ⟨h.1,?_⟩
  intro P cap hcap hfine d a rows z bin t₀ γ τ i B hZ hd hdhi ha hahi hl hz him r hr hp hbase hg hs
    σ hne j first central
  let M:=B.middleCap P cap hcap hfine hZ hd hdhi ha hahi hl hz him r hr hp hbase hg hs σ hne j first central
  exact h.2 r hr M hp (show γ ≤ (Mixed.rowGamma r.box r.B:ℝ) from hg.le)
    (by change witnessCollar ≤ (1:ℝ)/10^(13:ℕ);norm_num [witnessCollar])

#print axioms actual_bank_central_routes
end
end QRH.Cycle092.MixedUpperFinal
