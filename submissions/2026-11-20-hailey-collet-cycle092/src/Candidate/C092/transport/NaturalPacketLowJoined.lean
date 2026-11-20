/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Natural packets with the finite prefactors paid from an early power reserve. -/
import Candidate.C092.transport.NaturalPacketLowOldSector
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

/-- Natural phase slices with the exact two integration fees and one reserve
chosen ahead of the live scale. All finite costs are already in C0. -/
theorem actual_natural_lower_phase_sum_final_fee (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hkβ : 2*HeckeZeroSupremum.beta-1 ≤ kap) (loss : ℝ) (hloss : 0<loss) :
    ∃ mc : ℝ→ℝ,(∀ t,0<t → 0 < mc t) ∧
    ∀ (D : BaselineData) (F : BaselineSourceData D),
    (∀ s,D.length s ≤  mc D.t/200) → (∀ s,D.length s ≤ Cycle25.sourceMesh D.t/200) →
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
    d ≤ 19/25 → ∀ (x z : ℂ),x.re=a+16*D.e → z.re=17/50 → |z.im| ≤ (3*i+1:ℕ)*Z^τ →
    ∀ bins : Finset (BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t),
    Cycle090.hLower ≤ Geometry.h → Geometry.h ≤ Cycle090.hUpper →
    Geometry.ell=Physical.ell → ∀ eps : ℝ,0  ≤  eps → 0  ≤  P.mesh →
    159*D.ε+12*D.t+P.mesh+16*D.e+2*eps+loss  ≤  1/5000000 →
    (∑ bin∈bins,packetNorm D F (MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) bin)
      η Z x z (Z^Geometry.y))  ≤ 
      C0*(3+(3*i+1:ℕ)*Z^τ)^m*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*
        (Z^d)^(finalPower a d Cycle090.sourceCost (16*D.e+2*eps*d+17*D.t/25) (Cycle090.theta-1/5000000)) := by
  obtain ⟨ms,hms,hs⟩ := actual_natural_fixed_lower_phase_sum_final_fee hβ hkβ loss hloss
  obtain ⟨mo,hmo,ho⟩ := actual_natural_old_lower_phase_sum_final_fee hβ hkβ loss hloss
  let mc : ℝ→ℝ := fun t=>min (ms t) (mo t)
  refine ⟨mc,fun t ht=>lt_min (hms t ht) (hmo t ht),?_⟩
  intro D F hfCount hfSource η
  have hfs : ∀ s,D.length s ≤ ms D.t/200 := fun s=>(hfCount s).trans
    (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hfo : ∀ s,D.length s ≤ mo D.t/200 := fun s=>(hfCount s).trans
    (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  obtain ⟨ks,Cs,hCs,hs⟩ := hs D F hfs hfSource η
  obtain ⟨ko,Co,hCo,ho⟩ := ho D F hfo hfSource η
  refine ⟨ks+ko,Cs+Co,add_pos hCs hCo,?_⟩
  intro P padding τ hτ hheight hpad n
  filter_upwards [hs P padding τ hτ hheight hpad n,ho P padding τ hτ hheight hpad n] with Z hs ho
  refine ⟨hs.1,?_⟩
  intro idx grid hsel k hk i hi j hn
  dsimp only
  intro hdtop x z hx hz him bins hh hh' hell eps heps hm hreserve
  have hZ0 : 0<Z := zero_lt_one.trans hs.1
  have hheightbase : 1 ≤ 3+(3*i+1:ℕ)*Z^τ := by
    have h0 : (0:ℝ) ≤ (3*i+1:ℕ)*Z^τ := by positivity
    linarith
  have hmon (c c' : ℝ) (m m' : ℕ) (hc : 0 ≤ c) (hcc' : c ≤ c') (hmm' : m ≤ m') :
      c*(3+(3*i+1:ℕ)*Z^τ)^m*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*
        (Z^sourceDyadConductor Z D.t k)^(finalPower (51/100+D.e*j) (sourceDyadConductor Z D.t k)
          Cycle090.sourceCost (16*D.e+2*eps*sourceDyadConductor Z D.t k+17*D.t/25) (Cycle090.theta-1/5000000))  ≤ 
      c'*(3+(3*i+1:ℕ)*Z^τ)^m'*(Z^Geometry.y)^(-(1/2:ℝ))*Z^(-(4/25:ℝ)*Geometry.ell)*
        (Z^sourceDyadConductor Z D.t k)^(finalPower (51/100+D.e*j) (sourceDyadConductor Z D.t k)
          Cycle090.sourceCost (16*D.e+2*eps*sourceDyadConductor Z D.t k+17*D.t/25) (Cycle090.theta-1/5000000)) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul hcc' (pow_le_pow_right₀ hheightbase hmm') (by positivity) (hc.trans hcc')
  by_cases hδ : 2*(51/100+D.e*j)-1 ≤ 3/8
  · exact (hs.2 idx grid hsel k hk i hi j hn hdtop x z hx hz him bins hδ hh hh' hell eps heps hm hreserve).trans
      (hmon Cs (Cs+Co) ks (ks+ko) hCs.le (by linarith) (by omega))
  · exact (ho.2 idx grid hsel k hk i hi j hn hdtop x z hx hz him bins (le_of_lt (lt_of_not_ge hδ)) hh hh' hell eps heps hm hreserve).trans
      (hmon Co (Cs+Co) ko (ks+ko) hCo.le (by linarith) (by omega))

end QRH.Cycle092.NaturalPacketLow
#print axioms QRH.Cycle092.NaturalPacketLow.actual_natural_lower_phase_sum_final_fee
