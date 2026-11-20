/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Natural packets with the finite prefactors paid from an early power reserve. -/
import Candidate.C092.transport.NaturalPacketLowFixedFinalFee
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
open QRH.Cycle092.PacketJoin
namespace QRH.Cycle092.NaturalPacketLow
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- The actual two lower-sector public edges cover the entire fixed rectangle. -/
lemma lower_fixed_certificates {δ p : ℝ} (hd : 0≤δ) (hd' : δ≤3/8)
    (hp : 0≤p) (hp' : p≤1/2) :
    ∃ cS cA : DirectCertificate,cS∈directCertificates ∧ cA∈directCertificates ∧
      cS.route=.fixedS ∧ cA.route=.fixedA ∧ cS.edge=1 ∧ cA.edge=1 ∧
      cS.box.Contains (δ,p) ∧ cA.box.Contains (δ,p) := by
  let cS : DirectCertificate := ⟨.fixedS,1,⟨0,3/8,0,1/2⟩⟩
  let cA : DirectCertificate := ⟨.fixedA,1,⟨0,3/8,0,1/2⟩⟩
  refine ⟨cS,cA,?_,?_,rfl,rfl,rfl,rfl,?_,?_⟩
  · norm_num [cS,directCertificates]
  · norm_num [cA,directCertificates]
  · norm_num [cS,Box.Contains]
    exact ⟨hd,hd',hp,hp'⟩
  · norm_num [cA,Box.Contains]
    exact ⟨hd,hd',hp,hp'⟩

/-- The old lower public edge covers the complementary entire rectangle. -/
lemma lower_old_certificate {δ p : ℝ} (hd : 3/8≤δ) (hd' : δ≤3/4)
    (hp : 0≤p) (hp' : p≤1/2) :
    ∃ c : DirectCertificate,c∈directCertificates ∧ c.route=.old ∧ c.edge=1 ∧ c.box.Contains (δ,p) := by
  refine ⟨⟨.old,1,⟨3/8,3/4,0,1/2⟩⟩,?_,rfl,rfl,?_⟩
  · norm_num [directCertificates]
  · norm_num [Box.Contains]
    exact ⟨hd,hd',hp,hp'⟩

/-- Natural phase slices with the exact two integration fees and one reserve
chosen ahead of the live scale. All finite costs are already in C0. -/
theorem actual_natural_fixed_lower_phase_sum_final_fee (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hkβ : 2*HeckeZeroSupremum.beta-1≤kap) (loss : ℝ) (hloss : 0<loss) :
    ∃ mc : ℝ→ℝ,(∀ t,0<t → 0 < mc t) ∧
    ∀ (D : BaselineData) (F : BaselineSourceData D),
    (∀ s,D.length s≤ mc D.t/200) → (∀ s,D.length s≤Cycle25.sourceMesh D.t/200) →
    ∀ η : Character,∃ m : ℕ,∃ C0 : ℝ,0 < C0 ∧
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
    ∀ bins : Finset (BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t),
    2*a-1≤3/8 → Cycle090.hLower≤Geometry.h → Geometry.h≤Cycle090.hUpper →
    Geometry.ell=Physical.ell → ∀ eps : ℝ,0 ≤ eps → 0 ≤ P.mesh →
    159*D.ε+12*D.t+P.mesh+16*D.e+2*eps+loss ≤ 1/5000000 →
    (∑ bin∈bins,packetNorm D F (MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) bin)
      η Z x z (Z^Geometry.y)) ≤
      C0*(3+(3*i+1:ℕ)*Z^τ)^m*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*
        (Z^d)^(finalPower a d Cycle090.sourceCost (16*D.e+2*eps*d+17*D.t/25) (Cycle090.theta-1/5000000)) := by
  obtain ⟨mc,hmc,hpacket⟩ := actual_natural_fixed_phase_sum_final_fee hβ hkβ loss hloss
  refine ⟨mc,hmc,?_⟩
  intro D F hfCount hfSource η
  obtain ⟨m,C0,hC0,hpacket⟩ := hpacket D F hfCount hfSource η
  refine ⟨m,C0,hC0,?_⟩
  intro P padding τ hτ hheight hpad n
  filter_upwards [hpacket P padding τ hτ hheight hpad n,
    actual_cell_fixed_data D F P padding τ hτ hheight hpad n η,actual_cell_conductor D F padding] with Z hp hg hcond
  refine ⟨hp.1,?_⟩
  intro idx grid hs k hk i hi j hn
  dsimp only
  intro hdtop x z hx hz him bins hδtop hh hh' hell eps heps hm hreserve
  obtain ⟨hdhi,ha,ha',hrest⟩ := hg.2 idx grid hs k hk i hi j hn
  have hdlo := (hcond idx grid k hk i j hn).1
  have hδ : 0<2*(51/100+D.e*j)-1 := by linarith
  have hd0 : 0<sourceDyadConductor Z D.t k := by change (1/100:ℝ) ≤ sourceDyadConductor Z D.t k at hdlo;linarith
  apply hp.2 idx grid hs k hk i hi j hn hdtop x z hx hz him bins _ hh hh' hell eps heps hm hreserve
  intro bin hb hne
  have hsum : 0<∑ s∈(Finset.univ : Finset (Fin D.N)),D.length s/sourceDyadConductor Z D.t k := by
    rw [←Finset.sum_div,D.slots_sum]
    exact div_pos Geometry.ell_pos hd0
  have hq := classMean_bounds (cellRows D F padding Z idx grid k i j) Finset.univ
    (Z^sourceDyadConductor Z D.t k) (2*(51/100+D.e*j)-1) D.t D.t_pos
    (fun s=>D.length s/sourceDyadConductor Z D.t k)
    (MediumWitness.originalPhysical D F Z (sourceDyadConductor Z D.t k) (fun _=>z)) bin hδ.le
    (fun s _=>(div_pos (D.slots_pos s) hd0).le) hsum hne
  exact lower_fixed_certificates hδ.le hδtop (div_nonneg hq.1 hδ.le)
    ((div_le_iff₀ hδ).mpr (by linarith [hq.2]))

end QRH.Cycle092.NaturalPacketLow
#print axioms QRH.Cycle092.NaturalPacketLow.actual_natural_fixed_lower_phase_sum_final_fee
