/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Entire original error packets on actual selected natural-direct cell slices. -/
import Candidate.C092.transport.NaturalPacketLowFixedLabel
import Candidate.C092.transport.PacketJoinFixedCellData
import Candidate.C092.transport.PacketJoinActual
import Candidate.C092.transport.ConductorActual
import Candidate.C092.transport.PacketFinalPower
import Candidate.C092.transport.Direct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths
open ProbePhysical HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition HeckeDetectorBatch
open HeckeDetectorWitnessRows HeckeDetectorRawFiber
open Cycle25.Weighted.Numerator Cycle25.Numerator
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.ProbeAssembly QRH.Cycle092.SelectedNonfloor
open QRH.Cycle092.Direct QRH.Cycle092.DirectCount
open QRH.Cycle092.PacketJoin
namespace QRH.Cycle092.NaturalPacketLow
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

def naturalFixedR (D : BaselineData) (P : TransportParameters D) (δ p : ℝ) : ℝ :=
  PacketJoinFixed.Return.value δ p+159*D.ε+8*D.t+P.mesh

/-- Fully applied direct-natural error-mask bound. Original selected cells
supply the Batch, original phase bins and source geometry. There is no external
Batch, count, phase-amplitude or packet estimate. -/
theorem actual_natural_fixed_mask_bound (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hkβ : 2*HeckeZeroSupremum.beta-1≤kap) :
    ∃ mc : ℝ→ℝ,(∀ t,0<t → 0 < mc t) ∧
    ∀ (D : BaselineData) (F : BaselineSourceData D),
    (∀ s,D.length s≤ mc D.t/200) → (∀ s,D.length s≤Cycle25.sourceMesh D.t/200) →
    ∃ K : ℝ,0≤K ∧ ∀ η : Character,∃ Jc : ℕ,∃ Cc : ℝ,0<Cc ∧
    ∀ J : Finset (Fin D.N),∃ degree : ℕ,∃ C : ℝ,0<C ∧
    ∀ (P : TransportParameters D) (padding τ : ℝ),0<τ →
    4*τ<(1/200:ℝ)*D.cost → padding+2*D.t≤1/10000000000 → ∀ n : ℕ,
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀ idx grid : FreeRow→ℕ,
    selected D F padding τ n η Z idx grid →
    ∀ k∈smallDyadicIndices (Z^(Geometry.h+padding)),∀ i∈Finset.range (n+1),∀ j : ℕ,
    (cellRows D F padding Z idx grid k i j).Nonempty →
    let d := sourceDyadConductor Z D.t k
    let a : ℝ := 51/100+D.e*j
    let rows := cellRows D F padding Z idx grid k i j
    d≤19/25 → ∀ (x z : ℂ),x.re=a+16*D.e → z.re=17/50 → |z.im|≤(3*i+1:ℕ)*Z^τ →
    ∀ bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t,
    let slice := MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) bin
    let p := classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)
    slice.Nonempty →
    maskNorm D F J slice η Z x z (Z^Geometry.y) ≤
      actualMaskWeight D F J K Cc C Jc degree Z d a τ i*
        (Z^d)^(naturalPacketPower a p (naturalFixedR D P (2*a-1) p) d
          (2*D.t) (nativeMass D a d)) := by
  obtain ⟨mc,hmc,hpacket⟩ := q_natural_fixed_label_packet hβ hkβ
  refine ⟨mc,hmc,?_⟩
  intro D F hfCount hfSource
  obtain ⟨K,hK,hpacket⟩ := hpacket D F hfCount hfSource
  refine ⟨K,hK,?_⟩
  intro η
  obtain ⟨Jc,Cc,hCc,hpacket⟩ := hpacket η
  refine ⟨Jc,Cc,hCc,?_⟩
  intro J
  obtain ⟨degree,C,hC,hpacket⟩ := hpacket J
  refine ⟨degree,C,hC,?_⟩
  intro P padding τ hτ hheight hpad n
  filter_upwards [hpacket,actual_cell_fixed_data D F P padding τ hτ hheight hpad n η,
    actual_cell_conductor D F padding,source_prime_reconstruction_geometry F η,SelectedFloorEstimate.source_pools_nonempty D F] with Z hp hc hcond hg hpools
  refine ⟨hp.1,?_⟩
  intro idx grid hs k hk i hi j hn
  dsimp only
  intro hdtop x z hx hz him bin hne
  let d := sourceDyadConductor Z D.t k
  let a : ℝ := 51/100+D.e*j
  let rows := cellRows D F padding Z idx grid k i j
  have hZ : 0<Z := zero_lt_one.trans hp.1
  obtain ⟨hdhi,ha,hahi,hrow,hrest⟩ := hc.2 idx grid hs k hk i hi j hn
  have hdlo := (hcond idx grid k hk i j hn).1
  have hd0 : 0<d := by change 1/100≤d at hdlo; linarith
  have hd : (1/200:ℝ)≤d := by change 1/100≤d at hdlo; linarith
  have heq := amplitudeCell_eq_original D F Z d a hZ hd0 rows z bin
  have hne' := hne
  rw [heq] at hne'
  obtain ⟨hphase,hbatch⟩ := hrest z hz him
  obtain ⟨B,hBr,hData,hProfile,hWidth,hUpper,hExt,hMesh,hSlots,hBin,hMean⟩ := hbatch bin hne
  rw [heq] at hBr
  let H := nativeHeight Z d τ i
  have hH : 0≤H := by dsimp [H,nativeHeight];positivity
  have himH : |z.im|≤H := him.trans (by dsimp [H,nativeHeight];exact le_add_of_nonneg_left (by positivity))
  have hBim (s : Fin D.N) : |(B.external s).im|≤H := by rw [hExt];exact himH
  have hReal (s : Fin D.N) : (B.external s).re=17/50 := by rw [hExt];exact hz
  have hHlower : 2*Real.pi*(Z^d)^(τ/(2*(7/8:ℝ)))+(3*i:ℕ)*Z^τ≤H := by
    dsimp [H,nativeHeight]
    push_cast
    have ht := Real.rpow_pos_of_pos hZ τ
    linarith
  have hrows (u : FreeRow) (hu : u∈rows) : Z^(1/100:ℝ)≤rowNorm u ∧ rowNorm u≤Z^d :=
    ⟨(hrow u hu).1, (hrow u hu).2.1 |>.trans (Real.rpow_le_rpow_of_exponent_le hp.1.le (by linarith [D.t_pos]))⟩
  have hraw := hp.2 rows d hd hdtop hrows (fun u hu=>(hrow u hu).2.2)
    (hg.2.1 J) hg.2.2.2.1 (fun s=>⟨(hpools s.val).choose,(hpools s.val).choose_spec⟩)
    x z a (Z^τ) ((Z^d)^(τ/(2*(7/8:ℝ)))) D.t H i ha hahi hx hz D.t_pos
    (by linarith [D.t_small]) le_rfl hH himH hHlower bin hne' B hBr hData hProfile hWidth hUpper hReal hBim hMean
    (fun u hu s=>hphase u (Finset.filter_subset _ _ hu) s)
  have hY : (Z^d)^(Geometry.y/d)=Z^Geometry.y := by
    rw [←Real.rpow_mul hZ.le,mul_div_cancel₀ _ hd0.ne']
  rw [hY,hMesh] at hraw
  simp only [←Nat.card_eq_fintype_card,Batch.Bin,hSlots,hBin] at hraw
  let q := classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin
  have hpow : D.t+q*(Geometry.ell/d)-q*baseCapacity kap d/2+
      (3*(PacketJoinFixed.Return.value (2*a-1) (q/(2*a-1))+159*D.ε+D.t+P.mesh+7*D.t)+1+D.t+D.t)/4+
      (2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*(D.t+D.t)/2+D.t*(Geometry.ell/d) =
      naturalPacketPower a (q/(2*a-1)) (naturalFixedR D P (2*a-1) (q/(2*a-1)))
      d (2*D.t) (nativeMass D a d) := by
    dsimp only [naturalPacketPower,naturalFixedR,nativeMass]
    have hδ : 2*a-1≠0 := by dsimp [a];linarith
    field_simp [hδ,hd0.ne']
    <;> ring
  rw [hpow] at hraw
  unfold maskNorm
  rw [heq]
  have hraw' := mul_le_mul_of_nonneg_left hraw (show 0 ≤ mainFront D J Z by unfold mainFront;positivity)
  convert hraw' using 1
  · simp only [errorPacket,mainProduct]
    rw [←Finset.sum_coe_sort]
  · dsimp only [actualMaskWeight,nativeCountPrefactor,H]
    ring

end QRH.Cycle092.NaturalPacketLow
#print axioms QRH.Cycle092.NaturalPacketLow.actual_natural_fixed_mask_bound
