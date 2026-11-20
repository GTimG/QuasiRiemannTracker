/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A genuine natural direct slice instance of the final physical packet sum. -/
import Candidate.C092.transport.NaturalPacketLowPrice
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths
open ProbePhysical HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.ProbeAssembly QRH.Cycle092.SelectedNonfloor
open QRH.Cycle092.Direct QRH.Cycle092.DirectCount QRH.Coverage
open QRH.Cycle092.PacketJoin
namespace QRH.Cycle092.NaturalPacketLow
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- Actual natural direct slice, all original error masks summed through
packet_of_partition_prices. The only scalar budget is the explicit small
source/count/contour fee, paid against the public certificate's strict reserve.
No Batch, actual amplitude bound, source moment, cardinality or packet result
is assumed. Its exact finite prefactor is retained for later absorption. -/
theorem actual_natural_slice_final_power (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hkβ : 2*HeckeZeroSupremum.beta-1≤kap) :
    ∃ mc : ℝ→ℝ,(∀ t,0<t → 0 < mc t) ∧
    ∀ (D : BaselineData) (F : BaselineSourceData D),
    (∀ s,D.length s≤ mc D.t/200) → (∀ s,D.length s≤Cycle25.sourceMesh D.t/200) →
    ∃ K : ℝ,0≤K ∧ ∀ η : Character,∃ Jc : ℕ,∃ Cc : ℝ,0<Cc ∧
    ∃ degree : Finset (Fin D.N)→ℕ,∃ C : Finset (Fin D.N)→ℝ,(∀ J,0<C J) ∧
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
    slice.Nonempty → ∀ c : DirectCertificate,c∈directCertificates → c.route=.old → c.edge=1 →
    c.box.Contains (2*a-1,p) → Cycle090.hLower≤Geometry.h → Geometry.h≤Cycle090.hUpper →
    Geometry.ell=Physical.ell → ∀ fee : ℝ,
    d*(3*(159*D.ε+8*D.t+P.mesh)/4+(2*D.t)/4+nativeMass D a d)+fee≤1/5000000 →
    packetNorm D F slice η Z x z (Z^Geometry.y) ≤
      (∑ J∈Finset.univ.powerset,actualMaskWeight D F J K Cc (C J) Jc (degree J) Z d a τ i)*
        (Z^d)^(finalPower a d Cycle090.sourceCost fee (Cycle090.theta-1/5000000)) := by
  obtain ⟨mc,hmc,hpacket⟩ := actual_natural_mask_bound hβ hkβ
  refine ⟨mc,hmc,?_⟩
  intro D F hfCount hfSource
  obtain ⟨K,hK,hpacket⟩ := hpacket D F hfCount hfSource
  refine ⟨K,hK,?_⟩
  intro η
  obtain ⟨Jc,Cc,hCc,hpacket⟩ := hpacket η
  choose degree C hC hpacket using hpacket
  refine ⟨Jc,Cc,hCc,degree,C,hC,?_⟩
  intro P padding τ hτ hheight hpad n
  have hpAll := Filter.eventually_all.mpr (fun J=>hpacket J P padding τ hτ hheight hpad n)
  filter_upwards [hpAll,actual_cell_old_data D F P padding τ hτ hheight hpad n η] with Z hp hc
  refine ⟨(hp ∅).1,?_⟩
  intro idx grid hs k hk i hi j hn
  dsimp only
  intro hdtop x z hx hz him bin hne c hcCert hr he hpbox hh hh' hell fee hbudget
  let d := sourceDyadConductor Z D.t k
  let a : ℝ := 51/100+D.e*j
  let rows := cellRows D F padding Z idx grid k i j
  let slice := MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) bin
  let p := classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)
  have hZ := (hp ∅).1
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  obtain ⟨hdlo,hdhi,ha,ha',hrow,hrest⟩ := hc.2 idx grid hs k hk i hi j hn
  have hd0 : 0<d := by change 1/100≤d at hdlo; linarith
  change 51/100<a at ha
  change a≤7/8 at ha'
  have hδ : 0<2*a-1 := by linarith
  have hsum : 0<∑ s∈(Finset.univ : Finset (Fin D.N)),D.length s/d := by
    rw [←Finset.sum_div,D.slots_sum]
    exact div_pos Geometry.ell_pos hd0
  have hq := classMean_bounds rows Finset.univ (Z^d) (2*a-1) D.t D.t_pos
    (fun s=>D.length s/d) (MediumWitness.originalPhysical D F Z d (fun _=>z)) bin hδ.le
    (fun s _=>(div_pos (D.slots_pos s) hd0).le) hsum hne
  have hp0 : 0≤p := div_nonneg hq.1 hδ.le
  have hp1 : p≤1/2 := (div_le_iff₀ hδ).mpr (by linarith [hq.2])
  have hprice := natural_price_with_losses D P hcCert hr he hpbox hh hh' hell ha ha' hp0 hp1 hdtop hbudget
  let W := fun J=>actualMaskWeight D F J K Cc (C J) Jc (degree J) Z d a τ i
  have hW (J : Finset (Fin D.N)) : 0≤W J := by
    have hCJ := hC J
    have hCP : 0≤nativeCountPrefactor D F K Cc Jc Z d a τ i :=
      zero_le_one.trans (le_max_left _ _)
    have hH : 0≤nativeHeight Z d τ i := by unfold nativeHeight;positivity
    dsimp only [W,actualMaskWeight]
    unfold mainFront
    positivity
  have hpower := (natural_power_le_final_iff a p (naturalR D P (2*a-1) p) d
    (2*D.t) (nativeMass D a d) fee (Cycle090.theta-1/5000000) hd0).2 hprice
  change (∑ J∈Finset.univ.powerset,maskNorm D F J slice η Z x z (Z^Geometry.y)) ≤ _
  calc
    _ ≤ ∑ J∈Finset.univ.powerset,W J*(Z^d)^(finalPower a d Cycle090.sourceCost fee (Cycle090.theta-1/5000000)) := by
      apply Finset.sum_le_sum
      intro J hJ
      have hm := (hp J).2 idx grid hs k hk i hi j hn hdtop x z hx hz him bin hne
      exact hm.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
        (Real.one_le_rpow hZ.le hd0.le) hpower) (hW J))
    _ = _ := by rw [Finset.sum_mul]

end QRH.Cycle092.NaturalPacketLow
#print axioms QRH.Cycle092.NaturalPacketLow.actual_natural_slice_final_power
