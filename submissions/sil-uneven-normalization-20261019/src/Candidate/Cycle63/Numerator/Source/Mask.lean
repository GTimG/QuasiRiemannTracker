import Candidate.Cycle63.Numerator.Source.Parameters
import Candidate.Cycle25.Numerator.SourceSelection
import Candidate.Cycle63.Numerator.Source.SelectedBin
import Candidate.Cycle63.Numerator.Source.Ledger
import Candidate.Cycle25.Numerator.PhysicalCollect
import Candidate.Cycle25.Numerator.SourceScalar

/- Original module: Candidate.Cycle63.Numerator.Source.Selection. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

noncomputable section
open scoped Classical BigOperators
namespace Cycle63.Numerator.Source
open Cycle63.Arithmetic Cycle63.Numerator.Capacity
open Cycle25.Numerator
open OAI OAI.SevenEighths Cycle63DetectorCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst
open HeckeDetectorFiberPartition ProbeHighRowFamily Cycle25ProbeFinalAssembly Cycle25DetectorRowCount
open ProbePhysical HeckeFamily HeckeInverseAmplification

lemma scheduled_whole_slots (D : BaselineData)
    (hfine : ∀j,D.length j ≤ Cycle25.sourceMesh D.t/200)
    (d v delta : ℝ) (hd : dMinus ≤ d ∧ d ≤ dPlus) (hv : 0 ≤ v) (hdelta : 0 ≤ delta)
    (main : Finset (Fin D.N)) (g : Fin D.N → ℝ)
    (hg : ∀j,0 ≤ g j ∧ g j ≤ delta/2) (herror : ∀j,j ∉ main → g j=0) :
    let widths := fun j=>D.length j/d
    let q := weightedMean Finset.univ widths g
    q=(∑j,widths j*g j)/(ell/d) ∧ 0 ≤ q ∧ q ≤ delta/2 ∧
    ∃selected : Finset (Fin D.N),selected ⊆ main ∧ (∀j∈selected,0<g j) ∧
      (∑j∈selected,widths j) ≤ scheduledCapacity d v ∧
      q*scheduledCapacity d v-(delta/2)*Cycle25.sourceMesh D.t ≤ ∑j∈selected,widths j*g j ∧
      q*scheduledCapacity d v-(delta/2)*Cycle25.sourceMesh D.t ≤ ∑j∈selected,widths j*g j ∧
      ∀U:ℝ,1 ≤ U → ∀Q:Fin D.N → ℂ,
        (∀j,0<g j → U^(2*widths j*g j) ≤ ‖Q j‖^2) → 
        U^(2*q*scheduledCapacity d v-delta*Cycle25.sourceMesh D.t) ≤ ‖∏j∈selected,Q j‖^2 := by
  have hdp:=Cycle63.Physical.physical_d_pos hd.1
  let widths:=fun j=>D.length j/d
  have hsum:(∑j,widths j)=ell/d:=by dsimp [widths];rw [←Finset.sum_div,D.slots_sum]
  have hL:0<∑j,widths j:=by rw [hsum];exact div_pos ell_pos hdp
  have hw (j:Fin D.N):0 ≤ widths j:=(div_pos (D.slots_pos j) hdp).le
  have hm:=Cycle25.sourceMesh_pos D.t_pos
  have hwm (j:Fin D.N):widths j ≤ Cycle25.sourceMesh D.t :=
    Cycle63.Numerator.Fourth.rescaled_slot_mesh D (Cycle25.sourceMesh D.t) d
      ((by norm_num [dMinus,h] : (1/200:ℝ) ≤ dMinus).trans hd.1) hfine j
  have hcap:scheduledCapacity d v ≤ ∑j,widths j:=by rw [hsum];exact scheduledCapacity_le_supply hd hv
  obtain ⟨hq,hqtop⟩:=weightedMean_bounds Finset.univ widths g delta (fun j _=>hw j) hL (fun j _=>hg j)
  obtain ⟨T,_,hT,hTpos,hTcap,hgain,hspike⟩:=SlotSelection.zero_error_whole_slots
    Finset.univ main widths g delta (Cycle25.sourceMesh D.t) (scheduledCapacity d v)
    hdelta hm.le (fun j _=>hw j) (fun j _=>hwm j) hL (fun j _=>hg j)
    (fun j _=>herror j) (scheduledCapacity_nonneg hd hv) hcap
  refine ⟨?_,hq,hqtop,T,hT,hTpos,hTcap,hgain,hgain,?_⟩
  · unfold weightedMean;rw [hsum]
  · intro U hU Q hQ;exact hspike U hU Q (fun j _=>hQ j)

theorem source_class_main_selection (D : BaselineData)
    (F : BaselineSourceData D)
    (hfine : ∀j,D.length j  ≤  Cycle25.sourceMesh D.t/200)
    (Z d v δ : ℝ) (hZ : 1 < Z) (hd : dMinus  ≤  d ∧ d  ≤  dPlus) (hv : 0  ≤  v) (hδ : 0  ≤  δ)
    (z : ℂ) (rows : Finset FreeRow) (main : Finset (Fin D.N))
    (bin : BinLabel (Finset.univ : Finset (Fin D.N)) (δ/2) D.t)
    (hne : (amplitudeRows rows Finset.univ (Z^d) (δ/2) D.t D.t_pos (fun j=>D.length j/d)
      (fun u j=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length j)) z) bin).Nonempty) :
    let Q := fun (u : FreeRow) j=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length j)) z
    let rows' := amplitudeRows rows Finset.univ (Z^d) (δ/2) D.t D.t_pos (fun j=>D.length j/d) Q bin
    let g := binValue Finset.univ (δ/2) D.t bin
    let q := weightedMean Finset.univ (fun j=>D.length j/d) (maskedGain main g)
    0  ≤  q ∧ q  ≤  δ/2 ∧ ∃selected : Finset (Fin D.N),selected ⊆ main ∧
      (∑j∈selected,D.length j/d)  ≤  scheduledCapacity d v ∧
      ∀u∈rows',
        (Z^d)^(2*q*scheduledCapacity d v-
          δ*Cycle25.sourceMesh D.t)  ≤  ‖∏j∈selected,Q u j‖^2 ∧
        ((∀j,‖Q u j‖  ≤  (Z^(D.length j))^(HeckePrimeAmplitudeBins.amplitude (Z^(D.length j)) (δ/2) D.t (Q u j)+D.t))  → 
          ‖∏j∈main,Q u j‖  ≤  (Z^d)^(q*(Cycle63.Arithmetic.ell/d)+D.t*(Cycle63.Arithmetic.ell/d))) := by
  dsimp only
  let Q := fun (u : FreeRow) j=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length j)) z
  let rows' := amplitudeRows rows Finset.univ (Z^d) (δ/2) D.t D.t_pos (fun j=>D.length j/d) Q bin
  let g := binValue Finset.univ (δ/2) D.t bin
  have hdpos : 0 < d := Cycle63.Physical.physical_d_pos hd.1
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hU : 1 < Z^d := Real.one_lt_rpow hZ hdpos
  have hscale (j : Fin D.N) : (Z^d)^(D.length j/d)=Z^(D.length j) := by
    rw [←Real.rpow_mul hZpos.le,mul_div_cancel₀ _ hdpos.ne']
  have hgfull : ∀j,0  ≤  g j ∧ g j  ≤  δ/2 := by
    obtain ⟨u,hu⟩ := hne
    intro j
    have he := amplitude_class_value rows Finset.univ (Z^d) (δ/2) D.t D.t_pos
      (fun j=>D.length j/d) Q bin u hu j (Finset.mem_univ j)
    dsimp only [g]
    rw [←he]
    exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by positivity)
  have hg : ∀j,0  ≤  maskedGain main g j ∧ maskedGain main g j  ≤  δ/2 := by
    intro j
    unfold maskedGain
    split_ifs
    · exact hgfull j
    · exact ⟨le_rfl,by positivity⟩
  obtain ⟨hqeq,hq0,hqtop,T,hT,hTpos,hTcap,hgain,hgain',hspike⟩ :=
    scheduled_whole_slots D hfine d v δ hd hv hδ main
      (maskedGain main g) hg (fun j hj=>by simp [maskedGain,hj])
  refine ⟨hq0,hqtop,T,hT,hTcap,?_⟩
  intro u hu
  have hgrow (j : Fin D.N) : HeckePrimeAmplitudeBins.amplitude (Z^(D.length j)) (δ/2) D.t (Q u j)=g j := by
    have he := amplitude_class_value rows Finset.univ (Z^d) (δ/2) D.t D.t_pos
      (fun j=>D.length j/d) Q bin u hu j (Finset.mem_univ j)
    simpa only [hscale] using he
  refine ⟨?_,?_⟩
  · apply hspike (Z^d) hU.le (Q u)
    intro j hj
    have hjmain : j∈main := by
      by_contra hm
      simp only [maskedGain,ite_eq_right hm,lt_self_iff_false] at hj
    have hgm : maskedGain main g j=g j := by simp [maskedGain,hjmain]
    have hpos : 0 < HeckePrimeAmplitudeBins.amplitude ((Z^d)^(D.length j/d)) (δ/2) D.t (Q u j) := by
      rw [hscale,hgrow]
      rwa [hgm] at hj
    have hh := HeckePrimeAmplitudeBins.squared_spike (Z^d) (D.length j/d) (δ/2) D.t
      (Q u j) hU (div_pos (D.slots_pos j) hdpos) D.t_pos hpos
    simpa only [hscale,hgrow,hgm] using hh
  · intro hupper
    have hL : (∑j,D.length j/d)=ell/d := by rw [←Finset.sum_div,D.slots_sum]
    have hh := masked_main_product_upper main (fun j=>D.length j/d) g (Z^d) D.t (Q u)
      hU.le D.t_pos.le (fun j=>(div_pos (D.slots_pos j) hdpos).le)
      (by rw [hL];exact div_pos Cycle63.Arithmetic.ell_pos hdpos) (by
        intro j hj
        calc
          _  ≤  (Z^(D.length j))^(g j+D.t) := by
            have he := hupper j
            change ‖Q u j‖  ≤  (Z^(D.length j))^(HeckePrimeAmplitudeBins.amplitude (Z^(D.length j)) (δ/2) D.t (Q u j)+D.t) at he
            rwa [hgrow] at he
          _ = _ := by rw [←hscale j,←Real.rpow_mul (by positivity)])
    simpa only [hL] using hh


theorem source_selected_product_crude (D : BaselineData)
    (Z d δ : ℝ) (hZ : 1 < Z) (hd : dMinus  ≤  d) (hδ : 0  ≤  δ) (hδ' : δ  ≤  3/4)
    (selected : Finset (Fin D.N)) (Q : Fin D.N → ℂ)
    (hQ : ∀j,‖Q j‖  ≤  (Z^(D.length j))^
      (HeckePrimeAmplitudeBins.amplitude (Z^(D.length j)) (δ/2) D.t (Q j)+D.t)) :
    ‖∏j∈selected,Q j‖  ≤  Z^d := by
  have hdhalf : (1/2:ℝ) ≤ d := (by norm_num [dMinus,h] : (1/2:ℝ) ≤ dMinus).trans hd
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have ht := D.t_pos
  have hlength : ∑j∈selected,D.length j  ≤  (1/5:ℝ) := by
    apply le_trans _ (by norm_num [Cycle63.Arithmetic.ell] : Cycle63.Arithmetic.ell ≤ (1/5:ℝ))
    rw [←D.slots_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ selected)
      (fun j _ _=>(D.slots_pos j).le)
  calc
    _  ≤  ∏j∈selected,Z^(D.length j*(δ/2+D.t)) := by
      rw [norm_prod]
      apply Finset.prod_le_prod₀ (fun j _=>norm_nonneg _)
      intro j hj
      have ha := (HeckePrimeAmplitudeBins.amplitude_bounds
        (Z^(D.length j)) (δ/2) D.t (Q j) (by positivity)).2
      apply (hQ j).trans
      rw [←Real.rpow_mul hZ0.le]
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      exact mul_le_mul_of_nonneg_left (by linarith :
        HeckePrimeAmplitudeBins.amplitude (Z^(D.length j)) (δ/2) D.t (Q j)+D.t  ≤  δ/2+D.t)
        (D.slots_pos j).le
    _ = Z^((∑j∈selected,D.length j)*(δ/2+D.t)) := by
      rw [←Real.rpow_sum_of_pos hZ0,←Finset.sum_mul]
    _  ≤  Z^d := by
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      have hh := mul_le_mul_of_nonneg_right hlength
        (by positivity : 0  ≤  δ/2+D.t)
      nlinarith only [hh,hδ',D.t_small,hdhalf]


end Cycle63.Numerator.Source
end

/- Original module: Candidate.Cycle63.Numerator.Source.Class. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

noncomputable section
set_option maxHeartbeats 2600000
open scoped Classical BigOperators ContDiff
open Filter
namespace Cycle63.Numerator.Source
open Cycle63.Arithmetic Cycle63.Numerator.Capacity Cycle63.Numerator.Fourth
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open Cycle63DetectorCount Cycle25DetectorRowCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

/-- Fully selected actual amplitude-class packet estimate. The remaining count
premise concerns the original full class, while error slots have zero gain only
in the mean used for prime selection. -/
theorem source_packet_amplitude_class (D:BaselineData)
    (F:BaselineSourceData D) (hbeta:(51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hkbeta : 2*HeckeZeroSupremum.beta-1 ≤ D.momentKappa)
    (bPhi mesh affineError : ℝ) (haff : 0<affineError)
    (hsPhi : Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ → ℂ) ⊆ Set.Iic bPhi)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0<Ci)
    (hinput : ∀ᶠU:ℝ in atTop,AffineAt F bPhi mesh affineError U di control Ci)
    (hfineAffine : ∀j,D.length j ≤  mesh/200)
    (hfine:∀j,D.length j ≤ Cycle25.sourceMesh D.t/200) (J:Finset (Fin D.N)) :
    ∃degree:ℕ,∃C:ℝ,0<C ∧ ∀ᶠU:ℝ in atTop,
      1<U ∧ ∀(Z d:ℝ),1<Z  →  dMinus ≤ d  →  d ≤ dPlus  →  U=Z^d  → 
      ∀(η:Character) (x z:ℂ) (a height:ℝ),(51/100:ℝ) ≤ a  →  a ≤ 7/8  → 
      x.re=a+16*D.e  →  z.re=17/50  →  0 ≤ height  →  |z.im| ≤ height  → 
      ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U)  → 
      (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1)  → 
      (∀P:∀i:J,sourcePrimePool F Z i.val,Function.Injective (fun i=>(P i).val))  → 
      (∀i P,P∈sourcePrimePool F Z i → IsCoprime P.val η.modulus)  → 
      (∀i:J,sourcePrimePool F Z i.val)  → 
      ∀bin:BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let Q := fun (u:FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.length s/d) Q bin
      let main := (Finset.univ:Finset (Fin D.N)) \ J
      let q := weightedMean Finset.univ (fun s=>D.length s/d)
        (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
      rows'.Nonempty  →  ∀R Ccount:ℝ,1 ≤ Ccount  →  (rows'.card:ℝ) ≤ Ccount*U^R  → 
      (∀u∈rows',∀s,‖Q u s‖ ≤ (Z^(D.length s))^
        (HeckePrimeAmplitudeBins.amplitude (Z^(D.length s)) ((2*a-1)/2) D.t (Q u s)+D.t))  → 
      (∑i:rows',‖labelPolynomialPacket F.S F.exclusions η i.val
        (fun s:J=>sourcePrimePool F Z s.val) (fun s=>source_prime_pool_outside F Z s.val)
        (fun _=>F.W) (fun s=>Z^(D.length s.val)) x z F.W (U^(y/d))*(∏s∈main,Q i.val s)‖)  ≤ 
        C*Ccount*(1+height)^degree*(U^(y/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ)))*
          U^(D.t+q*(Cycle63.Arithmetic.ell/d)-q*zeroCapacity d/2+
            (3*R+1+D.t+affineError+D.t)/4+(2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*(D.t+D.t)/2+D.t*(Cycle63.Arithmetic.ell/d)) := by
  obtain ⟨degree,C,hC,hbin⟩ := source_packet_selected_bin D F hbeta hkbeta bPhi mesh affineError haff hsPhi di control Ci hCi hinput hfineAffine hfine J
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hbin] with U hbin
  refine ⟨hbin.1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow hdis hη Pbase bin
  dsimp only
  let Q := fun (u:FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.length s/d) Q bin
  let main := (Finset.univ:Finset (Fin D.N)) \ J
  let q := weightedMean Finset.univ (fun s=>D.length s/d)
    (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
  intro hne R Ccount hCc hcard hupper
  have hδ : 0 ≤ 2*a-1 := by linarith
  have hδtop : 2*a-1 ≤ 3/4 := by linarith
  have hU0 : 0<U := zero_lt_one.trans hbin.1
  have hsub : rows' ⊆ rows := Finset.filter_subset _ _
  have ht : 0 < D.t := D.t_pos
  have hselection (j:ℕ) := source_class_main_selection D F hfine Z d (2*((j:ℝ)*D.t+D.t+D.t)) (2*a-1)
    hZ ⟨hd,hdmax⟩ (by positivity) hδ z rows main bin hne
  have hq0 : 0 ≤ q := (hselection 0).1
  have hqtop : q ≤ (2*a-1)/2 := (hselection 0).2.1
  have hchoices (j:ℕ) : ∃selected:Finset (Fin D.N),selected ⊆ main ∧
      (∑s∈selected,D.length s/d) ≤ scheduledCapacity d (2*((j:ℝ)*D.t+D.t+D.t)) ∧
      ∀u∈rows',
        (Z^d)^(2*q*scheduledCapacity d (2*((j:ℝ)*D.t+D.t+D.t))-
          (2*a-1)*Cycle25.sourceMesh D.t) ≤ ‖∏s∈selected,Q u s‖^2 ∧
        ((∀s,‖Q u s‖ ≤ (Z^(D.length s))^
          (HeckePrimeAmplitudeBins.amplitude (Z^(D.length s)) ((2*a-1)/2) D.t (Q u s)+D.t))  → 
          ‖∏s∈main,Q u s‖ ≤ (Z^d)^(q*(Cycle63.Arithmetic.ell/d)+D.t*(Cycle63.Arithmetic.ell/d))) := (hselection j).2.2
  choose selected hselectedMain hcapacity hselected using hchoices
  let Pmain (i:rows') := ∏s∈main,Q i.val s
  let Pnorm (i:rows') := Pmain i / (((U^(D.t*(Cycle63.Arithmetic.ell/d)):ℝ)):ℂ)
  have hfull (i:rows') : ‖Pnorm i‖ ≤ U^(q*(Cycle63.Arithmetic.ell/d)) := by
    apply upper_bin_normalized (Pmain i) U (q*(Cycle63.Arithmetic.ell/d)) (D.t*(Cycle63.Arithmetic.ell/d)) hU0
    rw [hUZ]
    exact (hselected 0 i.val i.property).2 (hupper i.val i.property)
  have hcap (j:ℕ) (_:j∈Finset.range (coefficientBoxCount D.t+1)) :
      (∑s∈selected j,D.length s/d)  ≤  scheduledCapacity d (2*((j:ℝ)*D.t+D.t+D.t)) := by
    exact hcapacity j
  have hlow (j:ℕ) (_:j∈Finset.range (coefficientBoxCount D.t+1)) (i:rows') :
      U^(q*scheduledCapacity d (2*((j:ℝ)*D.t+D.t+D.t))-
        ((2*a-1)*Cycle25.sourceMesh D.t/2))  ≤  ‖∏s∈selected j,Q i.val s‖ := by
    rw [hUZ]
    exact squared_selected_lower (Z^d) q _ (2*a-1) (Cycle25.sourceMesh D.t) _
      (by rw [←hUZ];exact hU0) (hselected j i.val i.property).1
  have hcrude (j:ℕ) (_:j∈Finset.range (coefficientBoxCount D.t+1)) (i:rows') :
      ‖∏s∈selected j,Q i.val s‖ ≤ U := by
    rw [hUZ]
    exact source_selected_product_crude D Z d (2*a-1) hZ hd hδ hδtop (selected j) (Q i.val)
      (hupper i.val i.property)
  have hb := hbin.2 Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim
    rows' (fun u hu=>hrows u (hsub hu)) (fun u hu=>hrow u (hsub hu)) hdis hη Pbase selected Pnorm
    q R ((2*a-1)*Cycle25.sourceMesh D.t/2) Ccount hq0 hqtop hCc hcard hfull hcap hlow hcrude
  have hrestore := restore_upper_bin_loss Finset.univ
    (fun i:rows'=>labelPolynomialPacket F.S F.exclusions η i.val
      (fun s:J=>sourcePrimePool F Z s.val) (fun s=>source_prime_pool_outside F Z s.val)
      (fun _=>F.W) (fun s=>Z^(D.length s.val)) x z F.W (U^(y/d))) Pmain U (D.t*(Cycle63.Arithmetic.ell/d))
    (D.t+q*(Cycle63.Arithmetic.ell/d)-q*zeroCapacity d/2+
      (3*R+1+D.t+affineError+D.t)/4+((2*a-1)*Cycle25.sourceMesh D.t/2)/2+(2*a-1)*(D.t+D.t)/2)
    (C*Ccount*(1+height)^degree*(U^(y/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ))))
    hU0 hb
  have he : ((2*a-1)*Cycle25.sourceMesh D.t/2)/2=(2*a-1)*Cycle25.sourceMesh D.t/4 := by ring
  simpa only [he,Pmain] using hrestore


end Cycle63.Numerator.Source
end

/- Original module: Candidate.Cycle63.Numerator.Source.Mask. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

noncomputable section
set_option maxHeartbeats 2800000
open scoped Classical BigOperators ContDiff
open Filter
namespace Cycle63.Numerator.Source
open Cycle63.Arithmetic Cycle63.Arithmetic.Bernstein Cycle63.Numerator.Capacity Cycle63.Numerator.Fourth
open Cycle63.Numerator.Scalar
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open Cycle63DetectorCount Cycle25DetectorRowCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

/-- A literal physical error-mask sum has the uniform pre-height certificate
exponent, with only the original full-class count and actual scalar as inputs. -/
theorem source_mask_amplitude_class (D:BaselineData)
    (hgap:theta < HeckeZeroSupremum.beta)
    (hbetatop : HeckeZeroSupremum.beta ≤ 7/8)
    (hkap : D.momentKappa=2*HeckeZeroSupremum.beta-1)
    (F:BaselineSourceData D) (hbeta:(51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (bPhi mesh affineError : ℝ) (haff : 0<affineError)
    (hsPhi : Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ → ℂ) ⊆ Set.Iic bPhi)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0<Ci)
    (hinput : ∀ᶠU:ℝ in atTop,AffineAt F bPhi mesh affineError U di control Ci)
    (hfineAffine : ∀j,D.length j ≤  mesh/200)
    (eps sigma : ℝ) (heps : 0<eps) (hsigma : 0 ≤ sigma)
    (hbudget : 16*D.e+2*eps+3*sigma/4+affineError/4+8*D.t ≤ (HeckeZeroSupremum.beta-theta)/4)
    (hfine:∀j,D.length j ≤  Cycle25.sourceMesh D.t/200) (J:Finset (Fin D.N)) :
    ∃degree:ℕ,∃C:ℝ,0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀(Z d:ℝ),1 < Z  →  dMinus ≤ d  →  d ≤ dPlus  →  U=Z^d  → 
      ∀(η:Character) (x z:ℂ) (a height:ℝ),(51/100:ℝ) ≤ a  →  a ≤ 7/8  → 
      x.re=a+16*D.e  →  z.re=17/50  →  0 ≤ height  →  |z.im| ≤ height  → 
      ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U)  → 
      (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1)  → 
      (∀P:∀i:J,sourcePrimePool F Z i.val,Function.Injective (fun i=>(P i).val))  → 
      (∀i P,P∈sourcePrimePool F Z i → IsCoprime P.val η.modulus)  → 
      (∀i P,P∈sourcePrimePool F Z i → (4:ℝ) ≤ P.val.absNorm)  → 
      (∀i,∀P∈F.S,(P.absNorm:ℝ) ≤ Z^(D.length i))  → 
      (∀i:J,sourcePrimePool F Z i.val)  → 
      ∀bin:BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let Q := fun (u:FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.length s/d) Q bin
      let main := (Finset.univ:Finset (Fin D.N)) \ J
      let q := weightedMean Finset.univ (fun s=>D.length s/d)
        (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
      rows'.Nonempty  →  ∀Cs K C0:ℝ,0 ≤ Cs  →  1 ≤ K  →  1 ≤ C0  → 
      (rows'.card:ℝ) ≤ K*C0*Z^(3*D.t)*U^(countingR D.momentKappa (2*a-1) (q/(2*a-1))+sigma)  → 
      (∀u∈rows',‖frequencyWeight z ⟨u.val,u.property.1⟩*numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z‖ ≤ 
        Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*U^(2*eps)*U^(-(17/50:ℝ))*Z^((17/25)*D.t))  → 
      (∀u∈rows',∀s,‖Q u s‖ ≤ (Z^(D.length s))^
        (HeckePrimeAmplitudeBins.amplitude (Z^(D.length s)) ((2*a-1)/2) D.t (Q u s)+D.t))  → 
      ‖sourceMaskContribution F η rows' J Z x z (Z^Cycle63.Arithmetic.y)‖  ≤ 
        (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^((degree:ℝ)+2*eps)*
          Z^(Assembly.signal HeckeZeroSupremum.beta-499/5000000000-(HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e) := by
  obtain ⟨degree,C,hC,hclass⟩ := source_packet_amplitude_class D F hbeta (by rw [hkap]) bPhi mesh affineError haff hsPhi di control Ci hCi hinput hfineAffine hfine J
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hclass] with U hclass
  refine ⟨hclass.1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow hdis hη hQ hS Pbase bin
  dsimp only
  let Q := fun (u:FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.length s/d) Q bin
  let main := (Finset.univ:Finset (Fin D.N)) \ J
  let q := weightedMean Finset.univ (fun s=>D.length s/d)
    (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
  intro hne Cs K C0 hCs hK hC0 hcard hscalar hupper
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hU0 : 0 < U := zero_lt_one.trans hclass.1
  have hd0 : 0 < d := Cycle63.Physical.physical_d_pos hd
  have hδ : 0 < 2*a-1 := by linarith
  have hsub : rows' ⊆ rows := Finset.filter_subset _ _
  have hY : U^(Cycle63.Arithmetic.y/d)=Z^Cycle63.Arithmetic.y := by
    rw [hUZ,←Real.rpow_mul hZ0.le,mul_div_cancel₀ _ hd0.ne']
  have hcount1 : 1 ≤ K*C0*Z^(3*D.t) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK hC0)
      (Real.one_le_rpow hZ.le (by have := D.t_pos;positivity))
  have hb := hclass.2 Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow
    hdis hη Pbase bin hne (countingR D.momentKappa (2*a-1) (q/(2*a-1))+sigma)
    (K*C0*Z^(3*D.t)) hcount1 hcard hupper
  have heq (u:FreeRow) (hu:u∈rows') := errorLabelNumerator_eq_packet F.S F.exclusions (4*D.e) F.first η u
    (hrow u (hsub hu)) J (sourcePrimePool F Z) (fun s=>source_prime_pool_outside F Z s) hdis hη hQ
    (fun _=>F.W) (fun s=>Z^(D.length s)) x z (by rw [hx];linarith [D.e_pos]) hz.ge
    (by rw [hx];linarith [D.e_pos]) F.W 1 2 (by norm_num) F.complex_support (F.W.smooth ⊤)
    (Z^Cycle63.Arithmetic.y) (Real.rpow_pos_of_pos hZ0 _)
  have hlabel : (∑u∈rows',‖errorLabelNumerator F.S F.exclusions η u J (sourcePrimePool F Z)
      (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.length s)) x z F.W (Z^Cycle63.Arithmetic.y)*
      (∏s∈main,Q u s)‖)  ≤ 
    C*(K*C0*Z^(3*D.t))*(1+height)^degree*(U^(Cycle63.Arithmetic.y/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ)))*
      U^(D.t+q*(Cycle63.Arithmetic.ell/d)-q*zeroCapacity d/2+
        (3*(countingR D.momentKappa (2*a-1) (q/(2*a-1))+sigma)+1+D.t+affineError+D.t)/4+
        (2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*(D.t+D.t)/2+D.t*(Cycle63.Arithmetic.ell/d)) := by
    convert hb using 1
    calc
      _ = ∑i:rows',‖errorLabelNumerator F.S F.exclusions η i.val J (sourcePrimePool F Z)
          (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.length s)) x z F.W (Z^Cycle63.Arithmetic.y)*
          (∏s∈main,Q i.val s)‖ := (Finset.sum_coe_sort rows' _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [heq i.val i.property,hY]
  let A := Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*U^(2*eps)*
    U^(-(17/50:ℝ))*Z^((17/25)*D.t)
  have hA : 0 ≤ A := by dsimp only [A];positivity
  have hphysical := source_mask_physical_front F η rows' J Z hZ0 x z hz (Z^Cycle63.Arithmetic.y) hS A _ hA hscalar hlabel
  have hselection := source_class_main_selection D F hfine Z d 0 (2*a-1) hZ ⟨hd,hdmax⟩ (by norm_num) hδ.le z rows main bin hne
  have hq0 : 0 ≤ q := hselection.1
  have hqmax : q ≤ (2*a-1)/2 := hselection.2.1
  have he := Scalar.source_packet_multiplicative_identity J D.length D.slots_sum Z D.momentKappa d
    (newCapacity d) (2*a-1) q (C*K*C0*((1+height)^degree)) (physicalLoss D eps sigma affineError)
    hZ0 hd0.ne' hδ.ne'
  have hcapscale : newCapacity d/d=zeroCapacity d := by
    have hh:=scaled_zeroCapacity hd0.ne'
    unfold newCapacity
    apply (div_eq_iff hd0.ne').mpr
    nlinarith only [hh]
  rw [hcapscale] at he
  dsimp [physicalLoss] at he
  have hcollapse : A*Z^(-(4/25:ℝ)*(∑j:{i:Fin D.N//i ∉ J},D.length j.val))*
      (C*(K*C0*Z^(3*D.t))*(1+height)^degree*(U^(Cycle63.Arithmetic.y/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ)))*
      U^(D.t+q*(Cycle63.Arithmetic.ell/d)-q*zeroCapacity d/2+
        (3*(countingR D.momentKappa (2*a-1) (q/(2*a-1))+sigma)+1+D.t+affineError+D.t)/4+
        (2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*(D.t+D.t)/2+D.t*(Cycle63.Arithmetic.ell/d))) =
      (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*(1+height)^degree*
        Z^(numeratorExponent D.momentKappa d (newCapacity d) (2*a-1) (q/(2*a-1))+
          weightedSourceLoss d (2*a-1) (physicalLoss D eps sigma affineError)) := by
    dsimp only [A]
    rw [hUZ]
    calc
      _ = (Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps))*
          (((Z^d)^(2*eps)*(Z^d)^(-(17/50:ℝ))*Z^((17/25)*D.t)*
            Z^(-(4/25:ℝ)*(∑j:{i:Fin D.N//i ∉ J},D.length j.val)))*
          (C*(K*C0*Z^(3*D.t))*(1+height)^degree*((Z^d)^(Cycle63.Arithmetic.y/d))^(-(1/2:ℝ))*
            (∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ)))*
            (Z^d)^(D.t+q*(Cycle63.Arithmetic.ell/d)-q*zeroCapacity d/2+
              (3*(countingR D.momentKappa (2*a-1) (q/(2*a-1))+sigma)+1+D.t+affineError+D.t)/4+
              (2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*(D.t+D.t)/2+D.t*(Cycle63.Arithmetic.ell/d)))) := by ring
      _ = _ := by
        have hex : (2*a-1)*(Cycle25.sourceMesh D.t+4*D.t)/4 =
          (2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*(D.t+D.t)/2 := by ring
        rw [hex] at he
        have hat : (Finset.univ : Finset J)=J.attach := rfl
        rw [←hat] at he
        dsimp only [physicalLoss]
        simp only [add_zero,zero_div,add_assoc] at he
        convert congrArg
          (fun r : ℝ => (Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps))*r) he using 1 <;> ring
  have hphysical' := hphysical.trans_eq hcollapse
  have hheightpow : (1+height)^degree  ≤  (3+height)^(degree:ℝ) := by
    rw [Real.rpow_natCast]
    exact pow_le_pow_left₀ (by linarith) (by linarith) _
  have hcert := physical_packet_certificate D eps sigma affineError d a q hgap hbetatop hkap heps.le hsigma haff.le hbudget ⟨hd,hdmax⟩ ha hatop ⟨hq0,hqmax⟩
  apply hphysical'.trans
  calc
    _  ≤  (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*(3+height)^(degree:ℝ)*
        Z^(Assembly.signal HeckeZeroSupremum.beta-499/5000000000-(HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hheightpow (by positivity)
      · exact Real.rpow_le_rpow_of_exponent_le hZ.le hcert
      · positivity
      · positivity
    _ = _ := by rw [Real.rpow_add (by linarith : 0 < 3+height) (degree:ℝ) (2*eps)];ring


end Cycle63.Numerator.Source
end
