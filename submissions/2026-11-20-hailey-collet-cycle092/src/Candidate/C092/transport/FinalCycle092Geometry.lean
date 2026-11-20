/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FinalCycle092Interface
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths
open ProbePhysical HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open QRH.Cycle092.SelectedNonfloor QRH.Cycle092.PacketJoin QRH.Coverage
namespace QRH.Cycle092.Final
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

/-- Every nonempty original amplitude bin is a point of the closed Q domain. -/
lemma amplitude_original_domain (D : BaselineData) (F : BaselineSourceData D)
    (Z d a : ℝ) (rows : Finset FreeRow) (z : ℂ)
    (bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t)
    (hd : 0<d) (ha : (51/100:ℝ)≤a) (ha' : a≤7/8)
    (hne : (MediumWitness.amplitudeCell D F Z d a rows (fun _=>z) bin).Nonempty) :
    QRH.PhysicalCertificate.originalDomain.Contains
      (2*a-1,classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)) := by
  have hsum : 0 < ∑s:Fin D.N,D.length s/d := by
    rw [←Finset.sum_div,D.slots_sum]
    exact div_pos Geometry.ell_pos hd
  have hb := classMean_bounds rows Finset.univ (Z^d) (2*a-1) D.t D.t_pos
    (fun s=>D.length s/d) (MediumWitness.originalPhysical D F Z d (fun _=>z)) bin
    (by linarith) (fun s _=>(div_pos (D.slots_pos s) hd).le) hsum hne
  have hδ : 0<2*a-1 := by linarith
  norm_num only [QRH.PhysicalCertificate.originalDomain,Box.Contains,Rat.cast_zero,
    Rat.cast_div,Rat.cast_ofNat,Prod.fst,Prod.snd]
  change (0:ℝ)≤2*a-1 ∧ 2*a-1≤3/4 ∧
    0≤classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1) ∧
    classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1)≤1/2
  exact ⟨hδ.le,by linarith,div_nonneg hb.1 hδ.le,(div_le_iff₀ hδ).mpr (by linarith [hb.2])⟩

lemma phase_sum_split {ι : Type*} (s : Finset ι) (A : ι→Prop) (f : ι→ℝ) :
    (∑b∈s,f b)=(∑b∈s.filter A,f b)+(∑b∈s.filter (fun b=>¬A b),f b) := by
  simp only [Finset.sum_filter]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases h:A b <;> simp [h]

lemma transport_eps_le_t (D : BaselineData)
    (P : Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly.TransportParameters D) :
    P.eps ≤ D.t/100 := by
  have hn : (0:ℝ)≤D.N := Nat.cast_nonneg _
  nlinarith [P.eps_budget,P.eps_pos]

end QRH.Cycle092.Final
