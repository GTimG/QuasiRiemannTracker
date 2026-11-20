/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Genuine selected-band physical slot uppers on the original amplitude cell. -/
import Candidate.C092.transport.MixedOffsetCountPhaseUnion
import Candidate.C092.transport.DirectPhaseBins
set_option autoImplicit false
namespace QRH.Cycle092.MixedOffsetCount
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open HeckeDetectorFiberPartition HeckeDetectorAmplitudeFirst
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.MediumWitness QRH.Cycle092.MixedOffsetBank
variable [Geometry.Parameters]

/-- Capped amplitude-label membership alone gives no numerical upper.
Here the actual selected detector band supplies the original phase upper;
only then is the original physical phase label substituted. The independent
physical height z is retained and is never a witness frequency. -/
theorem actual_buffered_cell_slot_upper (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (padding τ : ℝ) (hτ : 0<τ)
    (hheight : 4*τ<(1/200:ℝ)*D.cost) (n : ℕ) (η : Character) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀ (idx grid : FreeRow→ℕ),ProbeAssembly.selected D F padding τ n η Z idx grid →
    ∀ (d threshold : ℝ),(1/200:ℝ) ≤ d → d ≤ 7/8 → 1/50<threshold →
    ∀ (i k : ℕ) (z : Fin D.N→ℂ),(∀s,(z s).re=17/50) →
      (∀s,|(z s).im| ≤ (3*i+1:ℕ)*Z^τ) →
    let rows:=mediumRows D F (Z^(Geometry.h+padding)) Z d threshold idx grid (fun _=>z) i k
    rows.Nonempty →
    ∀bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*bandLower D k-1)/2) D.t,
    ∀u∈amplitudeCell D F Z d (bandLower D k) rows z bin,∀s : Fin D.N,
      ‖originalPhysical D F Z d z u s‖ ≤ ((Z^d)^(D.length s/d))^
        (binValue Finset.univ ((2*bandLower D k-1)/2) D.t bin s+D.t) := by
  have hcells:=actual_buffered_cell_bank D F P padding τ hτ hheight n η
  have hphase:=DirectEnergy.Source.source_prime_bins D F P τ n hτ hheight
  filter_upwards [hcells,hphase] with Z hcells hphase
  refine ⟨hcells.1,?_⟩
  intro idx grid hsel d threshold hd hd' hthreshold i k z hz him
  dsimp only
  intro hne bin u hu s
  have hb:=(hcells.2 idx grid hsel d threshold hd hd' hthreshold i k z hz him hne).1
  have hnext:=hb.next
  rw [mediumRows_cellHeights] at hnext
  have hmem : u∈mediumRows D F (Z^(Geometry.h+padding)) Z d threshold idx grid (fun _=>z) i k:=
    (Finset.mem_filter.mp hu).1
  have hm:=(mem_mediumRows D F (Z^(Geometry.h+padding)) Z d threshold idx grid (fun _=>z) i k u).mp hmem
  have hs:=hphase d hd hd' η u (mem_rowBand.mp hm.1).2.1 hm.2.1 hm.2.2.1 (bandLower D k) i hb.index_bound
    hb.nonfloor.le (hb.a_upper.trans (by norm_num)) (hnext u hmem) (z s) (hz s) (him s) s
  have hupper : ‖HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) (z s)‖ ≤
      (Z^(D.length s))^(HeckePrimeAmplitudeBins.amplitude (Z^(D.length s)) ((2*bandLower D k-1)/2) D.t
        (HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) (z s))+D.t) := by
    simpa only [show bandLower D k-1/2=(2*bandLower D k-1)/2 by ring] using hs.2.2.2.1
  have hdpos : 0<d:=by linarith
  have hZpos : 0<Z:=zero_lt_one.trans hcells.1
  have hP : (Z^d)^(D.length s/d)=Z^(D.length s) := by
    rw [←Real.rpow_mul hZpos.le,mul_div_cancel₀ _ hdpos.ne']
  have hQ:=originalPhysical_eq D F Z d hZpos hdpos z u s
  have he:=(Finset.mem_filter.mp hu).2
  have hbin : HeckePrimeAmplitudeBins.amplitude ((Z^d)^(D.length s/d)) ((2*bandLower D k-1)/2) D.t
      (originalPhysical D F Z d z u s)=binValue Finset.univ ((2*bandLower D k-1)/2) D.t bin s := by
    have hv:=congrArg (fun b : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*bandLower D k-1)/2) D.t =>
      (b ⟨s,Finset.mem_univ _⟩).val) he
    simpa only [amplitudeLabel,binValue,dif_pos (Finset.mem_univ s)] using hv
  rw [hP,hQ] at hbin ⊢
  rw [←hbin]
  exact hupper

#print axioms actual_buffered_cell_slot_upper
end
end QRH.Cycle092.MixedOffsetCount
