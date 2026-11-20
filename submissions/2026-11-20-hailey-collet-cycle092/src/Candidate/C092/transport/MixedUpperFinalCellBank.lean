/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual selected cell source banks and their literal original phase layouts. -/
import Candidate.C092.transport.MixedOffsetCountFromLayout
import Candidate.C092.transport.MixedOffsetCountCellUpper
import Candidate.C092.transport.PacketJoinE49CellData
set_option autoImplicit false
namespace QRH.Cycle092.MixedUpperFinal
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open HeckeDetectorWitnessRows HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition HeckeDetectorPhysicalSelection
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.ProbeAssembly QRH.Cycle092.SelectedNonfloor QRH.Cycle092.MediumWitness
open QRH.Cycle092.MixedOffsetBank QRH.Cycle092.MixedOffsetCount
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- A genuine bank on the original selected amplitude cell. The layout is
constructed below from original slot data, rather than supplied as a field. -/
structure CellBank (D : BaselineData) (F : BaselineSourceData D) (η : Character)
    (Z d a : ℝ) (rows : Finset FreeRow) (z : ℂ)
    (bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t)
    (t₀ γ τ : ℝ) (i : ℕ) where
  source : SourceBank F.modulus ⊤ le_top F.S F.exclusions η
    (amplitudeCell D F Z d a rows (fun _=>z) bin) (Z^d) a D.ε t₀ γ
      (Z^τ) ((Z^d)^(τ/(2*(7/8:ℝ)))) i
  nonempty : (amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty
  row_upper : ∀u∈amplitudeCell D F Z d a rows (fun _=>z) bin,rowNorm u ≤ Z^d

namespace CellBank
variable {D : BaselineData} {F : BaselineSourceData D} {η : Character}
variable {Z d a : ℝ} {rows : Finset FreeRow} {z : ℂ}
variable {bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t}
variable {t₀ γ τ : ℝ} {i : ℕ}

/-- All phase labels, widths, physical heights and slots are copied literally. -/
def layout (B : CellBank D F η Z d a rows z bin t₀ γ τ i)
    (P : TransportParameters D) (hd : (1/200:ℝ) ≤ d) (hdhi : d ≤ 7/8) :
    BankLayout (Slot:=Fin D.N) B.source := by
  have hdpos : 0<d:=by linarith
  have hwp : ∀s∈(Finset.univ:Finset (Fin D.N)),0<D.length s/d:=
    fun s _=>div_pos (D.slots_pos s) hdpos
  have hwm : ∀s∈(Finset.univ:Finset (Fin D.N)),D.length s/d ≤ P.mesh := by
    intro s _
    apply (div_le_iff₀ hdpos).mpr
    nlinarith [P.slots_mesh s,P.mesh_pos]
  have hsum : 7/37 ≤ ∑s : Fin D.N,D.length s/d := by
    rw [←Finset.sum_div,D.slots_sum]
    apply (le_div_iff₀ hdpos).mpr
    linarith [Geometry.sixth_lt_ell]
  exact BankLayout.ofAmplitudeCell rows (Z^d) a D.ε t₀ γ (Z^τ)
    ((Z^d)^(τ/(2*(7/8:ℝ)))) i Finset.univ (fun _ x=>(F.w x:ℂ)) (fun _=>2)
    (fun s=>D.length s/d) (fun _=>z) P.mesh D.t P.mesh_pos.le D.t_pos hwp hwm hsum bin
    B.source B.nonempty B.row_upper

end CellBank

/-- A single attaining zero is fixed before all cutoffs on the ACTUAL
selected dyad/height/grid cell. No native layout or analytic estimate is
assumed. The scale threshold is uniform in both cutoff endpoints. -/
theorem actual_selected_cell_banks (D : BaselineData) (F : BaselineSourceData D)
    (P : TransportParameters D) (padding τ : ℝ) (hτ : 0<τ)
    (hheight : 4*τ<(1/200:ℝ)*D.cost) (hpad : padding+2*D.t ≤ 1/10000000000)
    (n : ℕ) (η : Character) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀idx grid : FreeRow→ℕ,
    selected D F padding τ n η Z idx grid →
    ∀k∈smallDyadicIndices (Z^(Geometry.h+padding)),∀i∈Finset.range (n+1),∀j : ℕ,
    (cellRows D F padding Z idx grid k i j).Nonempty →
    let d:=sourceDyadConductor Z D.t k
    let a:ℝ:=51/100+D.e*j
    let rows:=cellRows D F padding Z idx grid k i j
    (1/100:ℝ) ≤ d ∧ d ≤ 7/8 ∧ 51/100<a ∧ a ≤ 7/8 ∧
    (∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u) ∧
    ∀z : ℂ,z.re=17/50 → |z.im| ≤ (3*i+1:ℕ)*Z^τ →
    ∀bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t,
    (amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty →
    ∀t₀ γ : ℝ,0 ≤ γ → 1 ≤ t₀-γ → t₀ ≤ 3/2 →
      Nonempty (CellBank D F η Z d a rows z bin t₀ γ τ i) := by
  have hbank:=actual_source_bank F.modulus ⊤ le_top F.S F.exclusions F.maximal η
    (1/200) (7/8) τ D.ε D.e D.witnessKappa D.cost D.t n
    (by norm_num) (by norm_num) hτ (witness_zero_height_from_budget D hheight) hheight
    D.epsilon_pos D.e_pos D.e_small D.witnessKappa_pos D.witnessKappa_small
    D.cost_pos.le D.t_pos D.detector_budget
  filter_upwards [hbank,actual_cell_conductor D F padding,
    QRH.Cycle092.PacketJoin.actual_cell_e49_data D F P padding τ hτ hheight hpad n η]
    with Z hbank hcond hcell
  refine ⟨hcell.1,?_⟩
  intro idx grid hsel k hk i hi j hne
  dsimp only
  let d:=sourceDyadConductor Z D.t k
  let a:ℝ:=51/100+D.e*j
  let rows:=cellRows D F padding Z idx grid k i j
  have hc:=hcond idx grid k hk i j hne
  have hg:=hcell.2 idx grid hsel k hk i hi j hne
  refine ⟨hc.1,hg.1,hg.2.1,hg.2.2.1,fun u hu=>(hg.2.2.2.1 u hu).1,?_⟩
  intro z hz him bin hneCell t₀ γ hγ ht ht'
  have hsub : amplitudeCell D F Z d a rows (fun _=>z) bin ⊆ rows:=Finset.filter_subset _ _
  have hrow (u : FreeRow) (hu : u∈rows) :
      u∈SelectedActualIntegral.selectedRows D F padding Z grid ∧ idx u=i ∧ grid u=j := by
    have hb:=(mem_cubeBinRows _ idx grid i j u).mp hu
    exact ⟨(Finset.mem_inter.mp hb.1).1,hb.2⟩
  have hband (u : FreeRow) (hu : u∈rows) :=
    (mem_supportedNonfloorRows F.S F.maximal _ grid u).mp (hrow u hu).1
  have hrows : amplitudeCell D F Z d a rows (fun _=>z) bin ⊆
      rowBand (Z^(1/100:ℝ)) (Z^(Geometry.h+padding)):=fun u hu=>(hband u (hsub hu)).1
  have hcal (u : FreeRow) (hu : u∈amplitudeCell D F Z d a rows (fun _=>z) bin) :=
    (hband u (hsub hu)).2.1
  have hnorm (u : FreeRow) (hu : u∈amplitudeCell D F Z d a rows (fun _=>z) bin) :=
    (hc.2.2 u (hsub hu)).2
  have hcur (u : FreeRow) (hu : u∈amplitudeCell D F Z d a rows (fun _=>z) bin) :
      a ≤ detectorMaximum (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        ((3*i:ℕ)*Z^τ) := by
    simpa only [a,(hrow u (hsub hu)).2.1,(hrow u (hsub hu)).2.2,Nat.cast_mul,Nat.cast_ofNat]
      using (hsel.2.1 u).2.2.1
  have hnext (u : FreeRow) (hu : u∈amplitudeCell D F Z d a rows (fun _=>z) bin) :
      detectorMaximum (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(i+1:ℕ)*Z^τ)<a+2*D.e := by
    simpa only [a,(hrow u (hsub hu)).2.1,(hrow u (hsub hu)).2.2,Nat.cast_mul,Nat.cast_ofNat]
      using (hsel.2.1 u).2.2.2.2.1
  obtain ⟨B⟩:=hbank d ((by norm_num : (1/200:ℝ) ≤ 1/100).trans hc.1) hg.1
    (Z^(Geometry.h+padding)) _ hrows hcal hnorm a i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    hg.2.1 (hg.2.2.1.trans (by norm_num)) hnext hcur t₀ γ hγ ht ht'
  refine ⟨⟨B,hneCell,?_⟩⟩
  intro u hu
  exact (hnorm u hu).trans (Real.rpow_le_rpow_of_exponent_le hcell.1.le (by linarith [D.t_pos]))

#print axioms CellBank.layout
#print axioms actual_selected_cell_banks
end
end QRH.Cycle092.MixedUpperFinal
