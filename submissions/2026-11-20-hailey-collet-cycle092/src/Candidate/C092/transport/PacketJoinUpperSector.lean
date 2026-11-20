/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Native packets with the finite prefactors paid from an early power reserve. -/
import Candidate.C092.transport.PacketJoinUpperHelpers
import Candidate.C092.transport.PacketJoinOldPaddedFinalFee
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeDetectorWitnessRows HeckeDetectorBatch
open ProbePhysical HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.ProbeAssembly QRH.Cycle092.SelectedNonfloor
open QRH.Cycle092.Direct QRH.Cycle092.DirectCount QRH.Coverage
namespace QRH.Cycle092.PacketJoin
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

theorem actual_upper_sector_phase_sum_final_fee (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1 ≤ Direct.kap)
    (affineError : ℝ) (haff : 0<affineError) (loss : ℝ) (hloss : 0 < loss) :
    ∃ mc : ℝ→ℝ,(∀ t,0<t → 0 < mc t) ∧ ∃ mp : ℝ,0 < mp ∧
    ∀ (D : BaselineData) (F : BaselineSourceData D),
    (∀ s,D.length s ≤  mc D.t/200) → (∀ s,D.length s ≤ Cycle25.sourceMesh D.t/200) →
    (∀ s,D.length s ≤  mp/200) → (∀ s,D.length s ≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4)/200) →
    2*HeckeZeroSupremum.beta-1 ≤ D.momentKappa →
    ∀ η : Character,∃ m : ℕ,∃ C0 : ℝ,0 < C0 ∧
    ∀ (P : TransportParameters D) (padding τ : ℝ),0<τ →
    4*τ<(1/200:ℝ)*D.cost → padding+2*D.t ≤ 1/10000000000 → ∀ n : ℕ,
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀ idx grid : FreeRow→ℕ,
    selected D F padding τ n η Z idx grid →
    ∀ k∈smallDyadicIndices (Z^(Geometry.h+padding)),∀ i∈Finset.range (n+1),∀ j : ℕ,
    (cellRows D F padding Z idx grid k i j).Nonempty →
    let d := sourceDyadConductor Z D.t k
    let a : ℝ := 51/100+D.e*j
    let rows := cellRows D F padding Z idx grid k i j
    (1/2:ℝ) ≤ d → d ≤ Geometry.h+Cycle090.rowPad → ∀ (x z : ℂ),x.re=a+16*D.e → z.re=17/50 → |z.im| ≤ (3*i+1:ℕ)*Z^τ →
    ∀ bins : Finset (BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t),
    (∀ bin∈bins,
      (MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty →
      upperSectorAdmission (2*a-1) (classMean Finset.univ ((2*a-1)/2) D.t
          (fun s=>D.length s/d) bin/(2*a-1))) → Cycle090.hLower ≤ Geometry.h → Geometry.h ≤ Cycle090.hUpper →
    Geometry.ell=Physical.ell → ∀ eps : ℝ,0  ≤  eps → 0  ≤  P.mesh →
    159*D.ε+12*D.t+P.mesh+16*D.e+2*eps+affineError/4+loss+2*Cycle090.rowPad  ≤  1/250000000 →
    (∑ bin∈bins,packetNorm D F (MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) bin)
      η Z x z (Z^Geometry.y))  ≤ 
      C0*(3+(3*i+1:ℕ)*Z^τ)^m*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*
        (Z^d)^(finalPower a d Cycle090.sourceCost (16*D.e+2*eps*d+17*D.t/25) (Cycle090.theta-1/250000000)) := by
  obtain ⟨mco,hmco,mpo,hmpo,hpo⟩ := actual_old_padded_phase_sum_final_fee hβ hκβ affineError haff loss hloss
  obtain ⟨mcn,hmcn,mpn,hmpn,hpn⟩ := actual_native_padded_phase_sum_final_fee hβ affineError haff loss hloss
  obtain ⟨mcf,hmcf,mpf,hmpf,hpf⟩ := actual_fixed_padded_phase_sum_final_fee hβ affineError haff loss hloss
  obtain ⟨mcp,hmcp,mpp,hmpp,hpp⟩ := actual_e49_padded_phase_sum_final_fee hβ affineError haff loss hloss
  let mc : ℝ→ℝ := fun t=>min (mco t) (min (mcn t) (min (mcf t) (mcp t)))
  let mp : ℝ := min mpo (min mpn (min mpf mpp))
  refine ⟨mc,?_,mp,?_,?_⟩
  · intro t ht
    exact lt_min (hmco t ht) (lt_min (hmcn t ht) (lt_min (hmcf t ht) (hmcp t ht)))
  · exact lt_min hmpo (lt_min hmpn (lt_min hmpf hmpp))
  intro D F hfCount hfSource hfPacket hfCommon hkβ η
  have co : mc D.t ≤ mco D.t := min_le_left _ _
  have cn : mc D.t ≤ mcn D.t := (min_le_right _ _).trans (min_le_left _ _)
  have cf : mc D.t ≤ mcf D.t := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have cp : mc D.t ≤ mcp D.t := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have po : mp ≤ mpo := min_le_left _ _
  have pn : mp ≤ mpn := (min_le_right _ _).trans (min_le_left _ _)
  have pf : mp ≤ mpf := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have pp : mp ≤ mpp := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have fineCount (m : ℝ) (h : mc D.t ≤ m) : ∀s,D.length s ≤ m/200 :=
    fun s=>(hfCount s).trans (div_le_div_of_nonneg_right h (by norm_num))
  have finePacket (m : ℝ) (h : mp ≤ m) : ∀s,D.length s ≤ m/200 :=
    fun s=>(hfPacket s).trans (div_le_div_of_nonneg_right h (by norm_num))
  obtain ⟨mo,Co,hCo,hpo⟩ := hpo D F (fineCount _ co) hfSource (finePacket _ po) hfCommon hkβ η
  obtain ⟨mn,Cn,hCn,hpn⟩ := hpn D F (fineCount _ cn) hfSource (finePacket _ pn) hfCommon hkβ η
  obtain ⟨mf,Cf,hCf,hpf⟩ := hpf D F (fineCount _ cf) hfSource (finePacket _ pf) hfCommon hkβ η
  obtain ⟨mp',Cp,hCp,hpp⟩ := hpp D F (fineCount _ cp) hfSource (finePacket _ pp) hfCommon hkβ η
  let m : ℕ := mo+mn+mf+mp'
  let S : ℝ := Co+Cn+Cf+Cp
  have hS : 0<S := by dsimp [S];linarith
  refine ⟨m,4*S,by positivity,?_⟩
  intro P padding τ hτ hheight hpad n
  filter_upwards [hpo P padding τ hτ hheight hpad n,hpn P padding τ hτ hheight hpad n,
    hpf P padding τ hτ hheight hpad n,hpp P padding τ hτ hheight hpad n] with Z ho hn hf hp
  refine ⟨ho.1,?_⟩
  intro idx grid hs k hk i hi j hneCell
  dsimp only
  intro hd hdh x z hx hz him bins hbins hh hh' hell eps heps hm hreserve
  let d := sourceDyadConductor Z D.t k
  let a : ℝ := 51/100+D.e*j
  let rows := cellRows D F padding Z idx grid k i j
  let response := fun b : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t=>
    classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) b/(2*a-1)
  let A := fun b=>routeTopAdmission .old (2*a-1) (response b)
  let B := fun b=>routeTopAdmission .native (2*a-1) (response b)
  let C := fun b=>fixedTopAdmission (2*a-1) (response b)
  let bo := bins.filter A
  let bn := (bins.filter (fun b=>¬A b)).filter B
  let bf := ((bins.filter (fun b=>¬A b)).filter (fun b=>¬B b)).filter C
  let bp := ((bins.filter (fun b=>¬A b)).filter (fun b=>¬B b)).filter (fun b=>¬C b)
  have hbo : ∀ b∈bo,(MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) b).Nonempty →
      routeTopAdmission .old (2*a-1) (response b) := by
    intro b hb hne
    exact (Finset.mem_filter.mp hb).2
  have hbn : ∀ b∈bn,(MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) b).Nonempty →
      routeTopAdmission .native (2*a-1) (response b) := by
    intro b hb hne
    exact (Finset.mem_filter.mp hb).2
  have hbf : ∀ b∈bf,(MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) b).Nonempty →
      fixedTopAdmission (2*a-1) (response b) := by
    intro b hb hne
    exact (Finset.mem_filter.mp hb).2
  have hbp : ∀ b∈bp,(MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) b).Nonempty →
      pairedUpperAdmission (2*a-1) (response b) := by
    intro b hb hne
    obtain ⟨hb,hnotC⟩ := Finset.mem_filter.mp hb
    obtain ⟨hb,hnotB⟩ := Finset.mem_filter.mp hb
    obtain ⟨hb,hnotA⟩ := Finset.mem_filter.mp hb
    rcases hbins b hb hne with ho|hn|hf|hp
    · exact False.elim (hnotA ho)
    · exact False.elim (hnotB hn)
    · exact False.elim (hnotC hf)
    · exact hp
  have hrbig : 159*D.ε+12*D.t+P.mesh+16*D.e+2*eps+affineError/4+loss+2*Cycle090.rowPad ≤ 1/5000000 :=
    hreserve.trans (by norm_num)
  have hbo' := ho.2 idx grid hs k hk i hi j hneCell hd hdh x z hx hz him bo hbo hh hh' hell eps heps hm hrbig
  have hbn' := hn.2 idx grid hs k hk i hi j hneCell hd hdh x z hx hz him bn hbn hh hh' hell eps heps hm hrbig
  have hbf' := hf.2 idx grid hs k hk i hi j hneCell hd hdh x z hx hz him bf hbf hh hh' hell eps heps hm hrbig
  have hbp' := hp.2 idx grid hs k hk i hi j hneCell hd hdh x z hx hz him bp hbp hh hh' hell eps heps hm hreserve
  let rhs := fun (C : ℝ) (m : ℕ) (target : ℝ)=>C*(3+(3*i+1:ℕ)*Z^τ)^m*
    (Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*
      (Z^d)^(finalPower a d Cycle090.sourceCost (16*D.e+2*eps*d+17*D.t/25) target)
  have hd0 : 0<d := by dsimp [d];linarith
  have normalize (C : ℝ) (j : ℕ) (target : ℝ) (hC : 0 ≤ C) (hCS : C ≤ S) (hj : j ≤ m)
      (ht : target ≤ Cycle090.theta-1/250000000) :
      rhs C j target ≤ rhs S m (Cycle090.theta-1/250000000) :=
    upper_normalized_rhs_mono ho.1.le hd0 hC hCS hj ht
  have ho' := hbo'.trans (normalize Co mo _ hCo.le (by dsimp [S];linarith) (by dsimp [m];omega) (by linarith))
  have hn' := hbn'.trans (normalize Cn mn _ hCn.le (by dsimp [S];linarith) (by dsimp [m];omega) (by linarith))
  have hf' := hbf'.trans (normalize Cf mf _ hCf.le (by dsimp [S];linarith) (by dsimp [m];omega) (by linarith))
  have hp' := hbp'.trans (normalize Cp mp' _ hCp.le (by dsimp [S];linarith) (by dsimp [m];omega) le_rfl)
  rw [four_filter_sum bins A B C]
  calc
    _  ≤  rhs S m (Cycle090.theta-1/250000000)+rhs S m (Cycle090.theta-1/250000000)+
        rhs S m (Cycle090.theta-1/250000000)+rhs S m (Cycle090.theta-1/250000000) :=
      add_le_add (add_le_add (add_le_add ho' hn') hf') hp'
    _ = _ := by dsimp [rhs];ring

end QRH.Cycle092.PacketJoin
#print axioms QRH.Cycle092.PacketJoin.actual_upper_sector_phase_sum_final_fee
