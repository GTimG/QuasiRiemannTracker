/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Natural source count applied to the entire original physical error packet.
The packet keeps the original full amplitude subpartition and all error tuples. -/
import Candidate.C092.transport.NaturalPacketLowCurrent
import Candidate.C092.transport.ConductorActual
import Candidate.C092.transport.PacketJoinOldCount
import Candidate.C092.transport.PacketJoinMean
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical BigOperators ContDiff
open Filter
open OAI OAI.SevenEighths QRH.Record12518109Count
open ProbePhysical HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open HeckeDetectorWitnessRows HeckeDetectorRawFiber
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Cycle25.Weighted.Numerator Cycle25.Numerator Cycle25DetectorRowCount
open QRH.Cycle090 QRH.Cycle092.Direct QRH.Cycle092.DirectCount
open QRH.Cycle092.PacketJoin
namespace QRH.Cycle092.NaturalPacketLow
variable [Geometry.Parameters] [ActualGeometry.WidenedCoreBounds]

lemma natural_mean_power_mono {d qMain qFull : ℝ}
    (hd : (1/200:ℝ) ≤ d) (hdhi : d ≤ 19/25) (hq : qMain ≤ qFull) :
    qMain*(Geometry.ell/d)-qMain*baseCapacity kap d/2 ≤
      qFull*(Geometry.ell/d)-qFull*baseCapacity kap d/2 := by
  have hd0 : 0 < d := by linarith
  have hc := capOld_le_supply q_kappa_bounds.1 ⟨hd,hdhi⟩ (le_refl (0:ℝ))
  have hb : 0 ≤ baseCapacity kap d := by
    unfold baseCapacity
    apply div_nonneg
    · have hy := (physical_y_range ⟨hd,hdhi⟩).1
      exact le_min (by norm_num) (by rw [mul_div_assoc]; linarith)
    · have hk := q_kappa_bounds.1; positivity
  have heq : capOld kap d 0 = baseCapacity kap d := by
    unfold capOld baseCapacity at *
    simp only [mul_zero,sub_zero,max_eq_right hb]
  rw [heq] at hc
  have hp : 0 ≤ Geometry.ell/d-baseCapacity kap d/2 := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hq hp]

/-- Natural direct branch on an authentic source Batch: both the original full
class count and the full original coefficient packet are proved. Neither a
cardinality estimate nor a moment/packet estimate is a premise. The Batch
properties are precisely those supplied by original_shared_batches_of_selected.
The main-factor mean is kept distinct from the natural full-class mean. -/
theorem q_natural_label_packet (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hkβ : 2*HeckeZeroSupremum.beta-1 ≤ kap) :
    ∃ meshCount : ℝ → ℝ, (∀ t,0<t → 0 < meshCount t) ∧
    ∀ (D : BaselineData) (F : BaselineSourceData D),
    (∀ j,D.length j ≤ meshCount D.t/200) →
    (∀ j,D.length j ≤ Cycle25.sourceMesh D.t/200) →
    ∃ K : ℝ,0 ≤ K ∧ ∀ η : Character, ∃ Jc : ℕ, ∃ Cc : ℝ,0<Cc ∧
    ∀ J : Finset (Fin D.N),∃ degree : ℕ,∃ C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,
    1<Z ∧ ∀ (rows : Finset FreeRow) (d : ℝ),
    (1/200:ℝ) ≤ d → d ≤ 19/25 →
    (∀ u∈rows,Z^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ Z^d) →
    (∀ u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1) →
    (∀ P : ∀ j:J,sourcePrimePool F Z j.val,Function.Injective (fun j=>(P j).val)) →
    (∀ j P,P∈sourcePrimePool F Z j → IsCoprime P.val η.modulus) →
    (∀ j:J,sourcePrimePool F Z j.val) →
    ∀ (x z : ℂ) (a T allowance ν height : ℝ) (i : ℕ),
    51/100<a → a ≤ 7/8 → x.re=a+16*D.e → z.re=17/50 →
    0<ν → ν ≤ 1/10000000 → 0 ≤ height → |z.im| ≤ height →
    2*Real.pi*allowance+(3*i:ℕ)*T ≤ height →
    ∀ bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t,
    let Q := fun (u : FreeRow) j => HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length j)) z
    let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun j=>D.length j/d) Q bin
    let qFull := classMean Finset.univ ((2*a-1)/2) D.t (fun j=>D.length j/d) bin
    let main := (Finset.univ : Finset (Fin D.N))\J
    rows'.Nonempty →
    ∀ B : HeckeDetectorBatch.Batch F.modulus ⊤ (Sum Bool (RayQuotient.Characters F.modulus ⊤))
      (Fin D.N) (Z^d) a D.ε (Cycle25DetectorRowCount.cutoff (2*a-1) (qFull/(2*a-1)) kap) T allowance i,
    B.rows=rows' → B.data=sourceMomentData F.modulus ⊤ le_top F.S F.exclusions.prime η →
    B.profile=(fun _ r=>(F.w r:ℂ)) → B.widths=(fun j=>D.length j/d) →
    B.upper=(fun _=>2) → (∀ j,(B.external j).re=17/50) →
    (∀ j,|(B.external j).im| ≤ height) →
    (∀ u∈B.rows,rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
      (physical F.modulus ⊤ (fun u:FreeRow=>u.val) B.profile B.upper B.widths B.external (Z^d)) u=qFull) →
    (∀ u∈rows',∀ j,‖Q u j‖ ≤ (Z^(D.length j))^
      (HeckePrimeAmplitudeBins.amplitude (Z^(D.length j)) ((2*a-1)/2) D.t (Q u j)+D.t)) →
    let CP := max 1 ((Fintype.card (Sum Bool (RayQuotient.Characters F.modulus ⊤)):ℝ)*
      (dyadicLength (Z^d):ℝ)^2*fiberConstant (Cc*(1+height)^Jc) height K*(Fintype.card B.Bin:ℝ))
    (∑ u : rows',‖labelPolynomialPacket F.S F.exclusions η u.val
      (fun j:J=>sourcePrimePool F Z j.val) (fun j=>source_prime_pool_outside F Z j.val)
      (fun _=>F.W) (fun j=>Z^(D.length j.val)) x z F.W ((Z^d)^(Geometry.y/d))*(∏ j∈main,Q u.val j)‖) ≤
      C*CP*(1+height)^degree*((Z^d)^(Geometry.y/d))^(-(1/2:ℝ))*
        (∏ j:J,(Z^(D.length j.val))^(-(4/25:ℝ)))*
        (Z^d)^(D.t+qFull*(Geometry.ell/d)-qFull*baseCapacity kap d/2+
          (3*(directCount .old (2*a-1) (qFull/(2*a-1))+159*D.ε+D.t+B.mesh+7*ν)+1+D.t+D.t)/4+
          (2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*(D.t+D.t)/2+D.t*(Geometry.ell/d)) := by
  obtain ⟨mc,hmc,hcount⟩ := PacketJoin.q_old_batch_count hβ
  refine ⟨mc,hmc,?_⟩
  intro D F hmcD hsourceD
  obtain ⟨K,hK,hcount⟩ := hcount D.toMomentData F hmcD hsourceD D.epsilon_count_small
    kap q_kappa_bounds.1 q_kappa_bounds.2 hkβ
  refine ⟨K,hK,?_⟩
  intro η
  obtain ⟨Jc,Cc,hCc,hcount⟩ := hcount η
  refine ⟨Jc,Cc,hCc,?_⟩
  intro J
  obtain ⟨degree,C,hC,hpacket⟩ := q_natural_packet_amplitude_class D F hβ hkβ hsourceD J
  obtain ⟨U0,hU0⟩ := eventually_atTop.mp hpacket
  have hscaled : ∀ᶠ Z : ℝ in atTop,∀ d : ℝ,(1/200:ℝ)≤d → U0≤Z^d := by
    filter_upwards [(tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/200)).eventually
      (eventually_ge_atTop U0),eventually_ge_atTop (1:ℝ)] with Z hZ hZone
    intro d hd
    exact hZ.trans (Real.rpow_le_rpow_of_exponent_le hZone hd)
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hcount,hscaled] with Z hc hscaled
  refine ⟨hc.1,?_⟩
  intro rows d hd hdhi hrows hrow hdis hη Pbase x z a T allowance ν height i ha hahi hx hz hν hνhi hh him hf bin
  dsimp only
  intro hne B hBr hdata hprofile hwidth hupper hreal hBim hmean hphase
  let CP := (Fintype.card (Sum Bool (RayQuotient.Characters F.modulus ⊤)):ℝ)*
    (dyadicLength (Z^d):ℝ)^2*fiberConstant (Cc*(1+height)^Jc) height K*(Fintype.card B.Bin:ℝ)
  have hZ0 : 0 < Z := zero_lt_one.trans hc.1
  have hsub : B.rows ⊆ rows := by rw [hBr]; exact Finset.filter_subset _ _
  have hcard := hc.2 rows (fun u hu=>(hrows u hu).1) d (by linarith) a T allowance ν height
    (classMean Finset.univ ((2*a-1)/2) D.t (fun j=>D.length j/d) bin) i
    ha (by linarith) hν hνhi hh hf B (hBr ▸ hne) hsub hdata hprofile hwidth hupper hreal hBim hmean
  have hδ : 0 < 2*a-1 := by linarith
  have hsum : 0 < ∑ s ∈ (Finset.univ : Finset (Fin D.N)),D.length s/d := by
    rw [←Finset.sum_div,D.slots_sum]
    exact div_pos Geometry.ell_pos (by linarith)
  have hq := classMean_bounds rows Finset.univ (Z^d) (2*a-1) D.t D.t_pos
    (fun s=>D.length s/d)
    (fun u s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z)
    bin hδ.le (fun s _=>(div_pos (D.slots_pos s) (by linarith : 0<d)).le) hsum hne
  have hp0 : 0 ≤ classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1) := div_nonneg hq.1 hδ.le
  have hp1 : classMean Finset.univ ((2*a-1)/2) D.t (fun s=>D.length s/d) bin/(2*a-1) ≤ 1/2 :=
    (div_le_iff₀ hδ).mpr (by linarith [hq.2])
  rw [PacketJoin.old_rowCount_eq (2*a-1) _ kap hδ.le (by linarith) hp0 hp1 q_kappa_bounds.1 q_kappa_bounds.2] at hcard
  have hcard' : ((amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos
      (fun j=>D.length j/d) (fun u j=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length j)) z) bin).card:ℝ) ≤
      max 1 CP*(Z^d)^(directCount .old (2*a-1)
        ((classMean Finset.univ ((2*a-1)/2) D.t (fun j=>D.length j/d) bin)/(2*a-1))+159*D.ε+D.t+B.mesh+7*ν) := by
    rw [←hBr]
    change _ ≤ CP*_ at hcard
    exact hcard.trans (mul_le_mul_of_nonneg_right (le_max_right 1 CP) (by positivity))
  have hrows' (u : FreeRow) (hu : u∈rows) : (Z^d)^(1/100:ℝ)≤rowNorm u ∧ rowNorm u≤Z^d := by
    refine ⟨?_,(hrows u hu).2⟩
    rw [←Real.rpow_mul (zero_lt_one.trans hc.1).le]
    exact (Real.rpow_le_rpow_of_exponent_le hc.1.le (by linarith)).trans (hrows u hu).1
  have hraw := (hU0 (Z^d) (hscaled d hd)).2 Z d hc.1 hd hdhi rfl η x z a height ha.le hahi hx hz hh him
    rows hrows' hrow hdis hη Pbase bin hne _ (max 1 CP) (le_max_left _ _) hcard' hphase
  have hmeanpower := natural_mean_power_mono hd hdhi
    (PacketJoin.masked_class_mean_le D F Z d (2*a-1) (by linarith) (by linarith) z rows
      (Finset.univ\J) bin hne)
  apply hraw.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le (Real.one_le_rpow hc.1.le (by linarith))
  linarith only [hmeanpower]

end QRH.Cycle092.NaturalPacketLow
#print axioms QRH.Cycle092.NaturalPacketLow.q_natural_label_packet
