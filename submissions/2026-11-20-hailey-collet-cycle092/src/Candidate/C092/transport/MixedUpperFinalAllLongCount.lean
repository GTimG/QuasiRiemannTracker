/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual last-response source count on literal selected bank common classes. -/
import Candidate.C092.transport.MixedUpperFinalPresentation
import Candidate.C092.transport.MixedUpperFinalAllLong
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

theorem actual_bank_all_long_count (D : BaselineData) (F : BaselineSourceData D) :
    ∃Ki : ℝ,0 ≤ Ki ∧ ∃Ji : ℕ,∀η : Character,∃Ci : ℝ,0<Ci ∧
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀ (P : TransportParameters D) (d a : ℝ) (rows : Finset FreeRow) (z : ℂ)
      (bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t) (t₀ γ τ : ℝ) (i : ℕ)
      (B : CellBank D F η Z d a rows z bin t₀ γ τ i)
      (hd : (1/200:ℝ) ≤ d) (hdhi : d ≤ 7/8),
      51/100<a → a ≤ 7/8 → D.ε ≤ 1/10000000 →
      (∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u) → z.re=17/50 →
    ∀ (σ : Descriptor (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (dyadicLength (Z^d)))
      (hne : ((B.layout P hd hdhi).common σ).Nonempty),
      firstShort (inverseLength (Z^d) σ)=none →
    ∀r : TopData.Row,r∈TopData.rows →
      r.box.Contains (2*a-1,classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)) →
      t₀=Return.cutoffI (2*a-1) (classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)) →
      γ=(Mixed.rowGamma r.box r.B:ℝ) →
    let height:=QRH.Cycle092.PacketJoin.nativeHeight Z d τ i
    let C:=max 1 (12*(1+height)*((Ci*(1+height)^Ji)*Ki))
    (((B.layout P hd hdhi).common σ).card:ℝ) ≤ C*(Z^d)^(
      Return.valueI (2*a-1) (classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1))-
        4*(Mixed.rowBudget r.B:ℝ)/3+countLoss D.ε P.mesh D.t) := by
  obtain ⟨Ki,hKi,Ji,hsource⟩:=QRH.Cycle092.DirectCount.source_inverse_fiber_count D.toMomentData F
  refine ⟨Ki,hKi,Ji,?_⟩
  intro η
  obtain ⟨Ci,hCi,hsource⟩:=hsource η
  refine ⟨Ci,hCi,?_⟩
  filter_upwards [hsource] with Z h
  refine ⟨h.1,?_⟩
  intro P d a rows z bin t₀ γ τ i B hd hdhi ha hahi he hl hz σ hne hall r hr hp hbase hγ
  dsimp only
  let L:=B.layout P hd hdhi
  let last : Offset:=⟨65536,by omega⟩
  let pres:=B.presented P hd hdhi hl hz last
  let sl:=B.slice P hd hdhi hl hz σ hne last
  let f:=sl.fiber
  let height:=QRH.Cycle092.PacketJoin.nativeHeight Z d τ i
  let p:=classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)
  let v:=5/6-(2*a-1)
  have hZpos:0<Z:=zero_lt_one.trans h.1
  have hU:1<Z^d:=Real.one_lt_rpow h.1 (by linarith)
  have hheight:0 ≤ height:=by dsimp [height,QRH.Cycle092.PacketJoin.nativeHeight];positivity
  have hf:2*Real.pi*(Z^d)^(τ/(2*(7/8:ℝ)))+(3*i:ℕ)*Z^τ ≤ height:=by
    dsimp [height,QRH.Cycle092.PacketJoin.nativeHeight];push_cast
    have hpos:=Real.rpow_nonneg hZpos.le τ
    linarith
  have hb:=original_bank_admission hr hp
  have hr1:1 ≤ f.r:=L.last_long σ hne hall
  have hgeo:=f.lengths hU
  have hrg:f.r ≤ t₀-γ+D.ε:=by
    simpa only [cutoff,last,offset_last] using hgeo.2.1
  have hγ0:0 ≤ γ:=by rw [hγ];exact hb.2.1
  have ht0:t₀ ≤ 3/2:=hbase ▸ hb.2.2.2.2.1
  have hr2:f.r ≤ 2:=by linarith only [hrg,hγ0,ht0,he]
  have hc:=h.2 d hd a D.ε (cutoff t₀ γ last) (Z^τ) ((Z^d)^(τ/(2*(7/8:ℝ)))) i
    pres.batch pres.data pres.profile pres.upper pres.widths pres.real
    sl.bin sl.label sl.left sl.right sl.nonempty height hheight (by linarith) hf (by linarith) hr2
  have hcard:((L.common σ).card:ℝ) ≤ (f.rows.card:ℝ):=by
    exact_mod_cast Finset.card_le_card (L.common_subset σ hne last)
  have hv:0 ≤ v:=by dsimp [v];linarith
  have hvhi:v ≤ 1:=by dsimp [v];linarith
  have hvr:=mul_le_mul_of_nonneg_left hrg hv
  have hvε:=mul_le_mul_of_nonneg_right hvhi D.epsilon_pos.le
  have hRI:1/6+v*t₀=Return.valueI (2*a-1) p:=by
    have hi:=Return.long_identity (2*a-1) p (Return.hJ hb.1.1 hb.1.2).ne'
    have hbt:v*t₀=v*Return.cutoffI (2*a-1) p:=congrArg (fun t : ℝ=>v*t) hbase
    dsimp [v] at hbt ⊢
    nlinarith only [hi,hbt]
  have hgain:4*(Mixed.rowBudget r.B:ℝ)/3 ≤ v*γ:=by
    rw [hγ]
    exact all_long_count_funds hr hp
  have hE:sourceExponent f.r-(2*a-1)*f.r+2*D.ε+D.t ≤
      Return.valueI (2*a-1) p-4*(Mixed.rowBudget r.B:ℝ)/3+countLoss D.ε P.mesh D.t:=by
    unfold sourceExponent
    rw [max_eq_right (by linarith only [hr1] : (1:ℝ) ≤ (1+5*f.r)/6)]
    unfold countLoss
    dsimp [v] at hvr hgain hRI hvε
    nlinarith only [hvr,hvε,hRI,hgain,D.epsilon_pos,D.t_pos,P.mesh_pos]
  exact (hcard.trans hc).trans
    ((mul_le_mul_of_nonneg_right (le_max_right 1 _) (Real.rpow_nonneg (zero_lt_one.trans hU).le _)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le hE)
        (zero_le_one.trans (le_max_left 1 _))))

#print axioms actual_bank_all_long_count
end
end QRH.Cycle092.MixedUpperFinal
