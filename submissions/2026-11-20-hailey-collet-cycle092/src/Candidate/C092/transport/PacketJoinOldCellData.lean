/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual selected-cell dictionary and phase bins, at the original source dyad. -/
import Candidate.C092.transport.PacketJoinOldLabel
import Candidate.C092.transport.PacketConductorWindow
import Candidate.C092.transport.ExistentialPacketBatches
import Candidate.C092.transport.DirectPhaseBins
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths
open ProbePhysical HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition HeckeDetectorBatch
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.ProbeAssembly QRH.Cycle092.SelectedNonfloor
open QRH.Cycle092.Direct QRH.Cycle092.DirectCount
namespace QRH.Cycle092.PacketJoin
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

def safeUpperOldCutoff (δ p : ℝ) : ℝ := Cycle25DetectorRowCount.cutoff δ p Direct.kap

lemma safeUpperOldCutoff_range (δ p : ℝ) (hδ : 0≤δ) (hδ' : δ≤3/4)
    (hp : 0≤p) (hp' : p≤1/2) : 1 ≤ safeUpperOldCutoff δ p ∧ safeUpperOldCutoff δ p≤3/2 :=
  Cycle25DetectorRowCount.cutoff_bounds hδ hδ' hp hp'
    (by norm_num [Direct.kap,QRH.ContactCertificate.alphaHi]) source_contact_guards.2.2.2

/-- Original source Batches and true phase upper bins on every actual selected
cell. No Batch, amplitude estimate or analytic packet conclusion is a premise. -/
theorem actual_cell_upper_old_data (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (padding τ : ℝ) (hτ : 0<τ)
    (hheight : 4*τ<(1/200:ℝ)*D.cost) (hpad : padding+2*D.t≤1/10000000000)
    (n : ℕ) (η : Character) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀ idx grid : FreeRow→ℕ,
    selected D F padding τ n η Z idx grid →
    ∀ k∈smallDyadicIndices (Z^(Geometry.h+padding)),∀ i∈Finset.range (n+1),∀ j : ℕ,
    (cellRows D F padding Z idx grid k i j).Nonempty →
    let d := sourceDyadConductor Z D.t k
    let a : ℝ := 51/100+D.e*j
    let rows := cellRows D F padding Z idx grid k i j
    d≤7/8 ∧ 51/100<a ∧ a≤7/8 ∧
    (∀ u∈rows,Z^(1/100:ℝ)≤rowNorm u ∧ rowNorm u≤Z^(d-D.t) ∧
      (rowCharacter F.S F.exclusions.prime u).residue≠1) ∧
    ∀ z : ℂ,z.re=17/50 → |z.im|≤(3*i+1:ℕ)*Z^τ →
    (∀ u∈rows,∀ s,‖HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z‖ ≤
      (Z^(D.length s))^(HeckePrimeAmplitudeBins.amplitude (Z^(D.length s)) ((2*a-1)/2) D.t
        (HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z)+D.t)) ∧
    ∀ bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t,
    (MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty →
    let q := classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin
    ∃ B : Batch F.modulus ⊤ (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (Fin D.N)
      (Z^d) a D.ε (Cycle25DetectorRowCount.cutoff (2*a-1) (q/(2*a-1)) Direct.kap)
      (Z^τ) ((Z^d)^(τ/(2*(7/8:ℝ)))) i,
    B.rows=MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) bin ∧
    B.data=sourceMomentData F.modulus ⊤ le_top F.S F.exclusions.prime η ∧
    B.profile=(fun _ r=>(F.w r:ℂ)) ∧ B.widths=(fun s=>D.length s/d) ∧
    B.upper=(fun _=>2) ∧ B.external=(fun _=>z) ∧ B.mesh=P.mesh ∧ B.slots=Finset.univ ∧ B.binWidth=D.t ∧
    (∀ u∈B.rows,rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
      (physical F.modulus ⊤ (fun u:FreeRow=>u.val) B.profile B.upper B.widths B.external (Z^d)) u=q) := by
  have hbatch := GenericCount.actual_source_amplitude_batches_at_cutoff F.modulus ⊤ le_top
    F.S F.exclusions F.maximal η (1/200) (7/8) τ D.ε D.e D.witnessKappa D.cost D.t P.mesh D.t n
    safeUpperOldCutoff safeUpperOldCutoff_range
    (by norm_num) (by norm_num) hτ (MediumWitness.witness_zero_height_from_budget D hheight) hheight
    D.epsilon_pos D.e_pos D.e_small D.witnessKappa_pos D.witnessKappa_small D.cost_pos.le
    D.t_pos P.mesh_pos.le D.t_pos D.detector_budget
  filter_upwards [hbatch,actual_cell_conductor D F padding,
    DirectEnergy.Source.source_prime_bins D F P τ n hτ hheight,eventually_gt_atTop (1:ℝ)] with Z hbatch hcond hphase hZ
  refine ⟨hZ,?_⟩
  intro idx grid hsel k hk i hi j hne
  let rows := cellRows D F padding Z idx grid k i j
  let d := sourceDyadConductor Z D.t k
  let a : ℝ := 51/100+D.e*j
  have hc := hcond idx grid k hk i j hne
  have hdhi : d≤7/8 := by
    have hh := ActualGeometry.WidenedCoreBounds.h_interval.2
    dsimp only [d]
    linarith [hc.2.1]
  have hdlo : (1/200:ℝ)≤d := (by norm_num : (1/200:ℝ)≤1/100).trans hc.1
  have hsub (u : FreeRow) (hu : u∈rows) :
      u∈SelectedActualIntegral.selectedRows D F padding Z grid ∧ idx u=i ∧ grid u=j := by
    have hb := (mem_cubeBinRows _ idx grid i j u).mp hu
    exact ⟨(Finset.mem_inter.mp hb.1).1,hb.2⟩
  have hband (u : FreeRow) (hu : u∈rows) :=
    (mem_supportedNonfloorRows F.S F.maximal _ grid u).mp (hsub u hu).1
  have hrows (u : FreeRow) (hu : u∈rows) :
      u∈rowBand (Z^(1/100:ℝ)) (Z^(Geometry.h+padding)) := (hband u hu).1
  have hcal (u : FreeRow) (hu : u∈rows) :
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 := (hband u hu).2.1
  have ⟨u,hu⟩ := hne
  have hj0 : j≠0 := by
    intro he
    exact (hband u hu).2.2 ((hsub u hu).2.2.trans he)
  have ha : 51/100<a := by
    dsimp [a]
    have hj : (0:ℝ)<j := by exact_mod_cast Nat.pos_of_ne_zero hj0
    nlinarith [D.e_pos]
  have ha' : a≤7/8 := by simpa only [(hsub u hu).2.2] using (hsel.2.1 u).2.1
  have hcur (v : FreeRow) (hv : v∈rows) : a≤detectorMaximum
      (sourceDetectorFamily F.S F.exclusions.prime η v (rayCubeFamily F.modulus ⊤ le_top v)) ((3*i:ℕ)*Z^τ) := by
    simpa only [a,(hsub v hv).2.1,(hsub v hv).2.2,Nat.cast_mul,Nat.cast_ofNat] using (hsel.2.1 v).2.2.1
  have hnext (v : FreeRow) (hv : v∈rows) : detectorMaximum
      (sourceDetectorFamily F.S F.exclusions.prime η v (rayCubeFamily F.modulus ⊤ le_top v)) (3*(i+1:ℕ)*Z^τ)<a+2*D.e := by
    simpa only [a,(hsub v hv).2.1,(hsub v hv).2.2,Nat.cast_mul,Nat.cast_ofNat] using (hsel.2.1 v).2.2.2.2.1
  refine ⟨hdhi,ha,ha',?_,?_⟩
  · intro v hv
    have hband' := mem_rowBand.mp (hrows v hv)
    exact ⟨hband'.2.1,(hc.2.2 v hv).2,
      calibrated_row_nonprincipal F.S F.exclusions.prime F.maximal F.exclusions.bad v hband'.1 (hcal v hv)⟩
  · intro z hz him
    refine ⟨?_,?_⟩
    · intro v hv s
      have hh := hphase d hdlo hdhi η v (mem_rowBand.mp (hrows v hv)).2.1 (hcal v hv)
        (hc.2.2 v hv).2 a i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) ha.le (ha'.trans (by norm_num))
        (hnext v hv) z hz him s
      simpa only [show a-1/2=(2*a-1)/2 by ring] using hh.2.2.2.1
    · intro bin hneBin
      dsimp only
      have hsmall (s : Fin D.N) : D.length s≤(1/200:ℝ)*P.mesh := by
        simpa only [div_eq_mul_inv,one_mul,mul_comm] using P.slots_mesh s
      have hsum : (7/37:ℝ)*(7/8)≤∑s,D.length s := by rw [D.slots_sum];linarith [Geometry.sixth_lt_ell]
      have hb := hbatch d hdlo hdhi (Z^(Geometry.h+padding)) rows hne hrows hcal
        (fun v hv=>(hc.2.2 v hv).2) a i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
        ha ha' hnext hcur D.N D.length D.slots_pos hsmall hsum
        (fun _ r=>(F.w r:ℂ)) (fun _=>2) (fun _=>z) bin hneBin
      have heq : safeUpperOldCutoff (2*a-1)
          ((classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin)/(2*a-1)) =
          Cycle25DetectorRowCount.cutoff (2*a-1)
          ((classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin)/(2*a-1)) Direct.kap := rfl
      dsimp only at hb
      rw [heq] at hb
      obtain ⟨B,hBr,hData,hRev,hSlots,hWidths,hW,hUpper,hExternal,hMesh,hBin,hFamily,hMean⟩ := hb
      exact ⟨B,hBr,hData,hW,hWidths,hUpper,hExternal,hMesh,hSlots,hBin,hMean⟩

end QRH.Cycle092.PacketJoin
#print axioms QRH.Cycle092.PacketJoin.actual_cell_upper_old_data
