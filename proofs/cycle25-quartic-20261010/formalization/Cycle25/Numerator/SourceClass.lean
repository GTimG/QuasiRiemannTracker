import Cycle25.Numerator.SourceBin

/-! The actual full amplitude class supplies the selected-prime and upper-product
premises of the original-numerator packet estimate. The class count remains an
explicit premise and is not recomputed on an error-dependent or selected subset. -/
noncomputable section
set_option maxHeartbeats 2600000
open scoped Classical BigOperators ContDiff
open Filter
namespace Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open Cycle25DetectorRowCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

lemma source_box_capacity_eq (kap d t:ℝ) (j:ℕ) :
    SlotSelection.reflectedCapacity kap d ((j:ℝ)*t+2*t)=
      selectedCapacity kap ((2*(ly/d)-1)/(6*kap)-t/(3*kap)) ((j:ℝ)*t+t) := by
  unfold SlotSelection.reflectedCapacity SlotSelection.baseCapacity selectedCapacity
  congr 1
  ring

/-- Fully selected actual amplitude-class packet estimate. The remaining count
premise concerns the original full class, while error slots have zero gain only
in the mean used for prime selection. -/
theorem source_packet_amplitude_class {Δ:ℝ} (D:HighParameters.HighData Δ)
    (F:WeightedSourceData D.toMomentData) (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hfine:∀j,D.ell j≤Cycle25.sourceMesh D.t/200) (J:Finset (Fin D.N)) :
    ∃degree:ℕ,∃C:ℝ,0<C ∧ ∀ᶠU:ℝ in atTop,
      1<U ∧ ∀(Z d:ℝ),1<Z → (1/2:ℝ)≤d → d≤Cycle25.h+rowExtension → U=Z^d →
      ∀(η:Character) (x z:ℂ) (a height:ℝ),(51/100:ℝ)≤a → a≤7/8 →
      x.re=a+16*D.e → z.re=17/50 → 0≤height → |z.im|≤height →
      ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ)≤rowNorm u ∧ rowNorm u≤U) →
      (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1) →
      (∀P:∀i:J,sourcePrimePool F Z i.val,Function.Injective (fun i=>(P i).val)) →
      (∀i P,P∈sourcePrimePool F Z i→IsCoprime P.val η.modulus) →
      (∀i:J,sourcePrimePool F Z i.val) →
      ∀bin:BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let Q := fun (u:FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell s)) z
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.ell s/d) Q bin
      let main := (Finset.univ:Finset (Fin D.N)) \ J
      let q := weightedMean Finset.univ (fun s=>D.ell s/d)
        (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
      rows'.Nonempty → ∀R Ccount:ℝ,1≤Ccount → (rows'.card:ℝ)≤Ccount*U^R →
      (∀u∈rows',∀s,‖Q u s‖≤(Z^(D.ell s))^
        (HeckePrimeAmplitudeBins.amplitude (Z^(D.ell s)) ((2*a-1)/2) D.t (Q u s)+D.t)) →
      (∑i:rows',‖labelPolynomialPacket F.S F.exclusions η i.val
        (fun s:J=>sourcePrimePool F Z s.val) (fun s=>source_prime_pool_outside F Z s.val)
        (fun _=>F.W) (fun s=>Z^(D.ell s.val)) x z F.W (U^(ly/d))*(∏s∈main,Q i.val s)‖) ≤
        C*Ccount*(1+height)^degree*(U^(ly/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.ell s.val))^(-(4/25:ℝ)))*
          U^(D.t+q*(ell/d)-q*((2*(ly/d)-1)/(6*D.momentKappa)-D.t/(3*D.momentKappa))/2+
            (3*R+1+2*D.t)/4+(2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*D.t/4+D.t*(ell/d)) := by
  obtain ⟨degree,C,hC,hbin⟩ := source_packet_selected_bin D F hbeta hfine J
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hbin] with U hbin
  refine ⟨hbin.1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow hdis hη Pbase bin
  dsimp only
  let Q := fun (u:FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell s)) z
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.ell s/d) Q bin
  let main := (Finset.univ:Finset (Fin D.N)) \ J
  let q := weightedMean Finset.univ (fun s=>D.ell s/d)
    (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
  intro hne R Ccount hCc hcard hupper
  have hδ : 0≤2*a-1 := by linarith
  have hδtop : 2*a-1≤3/4 := by linarith
  have hU0 : 0<U := zero_lt_one.trans hbin.1
  have hsub : rows'⊆rows := Finset.filter_subset _ _
  have ht : 0 < D.t := D.t_pos
  have hselection (j:ℕ) := source_class_main_selection D F hfine Z d ((j:ℝ)*D.t+2*D.t) (2*a-1)
    hZ hd (by positivity) hδ z rows main bin hne
  have hq0 : 0≤q := (hselection 0).1
  have hqtop : q≤(2*a-1)/2 := (hselection 0).2.1
  have hchoices (j:ℕ) : ∃selected:Finset (Fin D.N),selected⊆main ∧
      (∑s∈selected,D.ell s/d)≤SlotSelection.reflectedCapacity D.momentKappa d ((j:ℝ)*D.t+2*D.t) ∧
      ∀u∈rows',
        (Z^d)^(2*q*SlotSelection.reflectedCapacity D.momentKappa d ((j:ℝ)*D.t+2*D.t)-
          (2*a-1)*Cycle25.sourceMesh D.t)≤‖∏s∈selected,Q u s‖^2 ∧
        ((∀s,‖Q u s‖≤(Z^(D.ell s))^
          (HeckePrimeAmplitudeBins.amplitude (Z^(D.ell s)) ((2*a-1)/2) D.t (Q u s)+D.t)) →
          ‖∏s∈main,Q u s‖≤(Z^d)^(q*(ell/d)+D.t*(ell/d))) := (hselection j).2.2
  choose selected hselectedMain hcapacity hselected using hchoices
  let Pmain (i:rows') := ∏s∈main,Q i.val s
  let Pnorm (i:rows') := Pmain i / (((U^(D.t*(ell/d)):ℝ)):ℂ)
  have hfull (i:rows') : ‖Pnorm i‖≤U^(q*(ell/d)) := by
    apply upper_bin_normalized (Pmain i) U (q*(ell/d)) (D.t*(ell/d)) hU0
    rw [hUZ]
    exact (hselected 0 i.val i.property).2 (hupper i.val i.property)
  have hcap (j:ℕ) (_:j∈Finset.range (coefficientBoxCount D.t+1)) :
      (∑s∈selected j,D.ell s/d) ≤ selectedCapacity D.momentKappa ((2*(ly/d)-1)/(6*D.momentKappa)-D.t/(3*D.momentKappa)) ((j:ℝ)*D.t+D.t) := by
    rw [←source_box_capacity_eq]
    exact hcapacity j
  have hlow (j:ℕ) (_:j∈Finset.range (coefficientBoxCount D.t+1)) (i:rows') :
      U^(q*selectedCapacity D.momentKappa ((2*(ly/d)-1)/(6*D.momentKappa)-D.t/(3*D.momentKappa)) ((j:ℝ)*D.t+D.t)-
        ((2*a-1)*Cycle25.sourceMesh D.t/2)) ≤ ‖∏s∈selected j,Q i.val s‖ := by
    rw [hUZ,←source_box_capacity_eq]
    exact squared_selected_lower (Z^d) q _ (2*a-1) (Cycle25.sourceMesh D.t) _
      (by rw [←hUZ];exact hU0) (hselected j i.val i.property).1
  have hcrude (j:ℕ) (_:j∈Finset.range (coefficientBoxCount D.t+1)) (i:rows') :
      ‖∏s∈selected j,Q i.val s‖≤U := by
    rw [hUZ]
    exact source_selected_product_crude D Z d (2*a-1) hZ hd hδ hδtop (selected j) (Q i.val)
      (hupper i.val i.property)
  have hb := hbin.2 Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim
    rows' (fun u hu=>hrows u (hsub hu)) (fun u hu=>hrow u (hsub hu)) hdis hη Pbase selected Pnorm
    q R ((2*a-1)*Cycle25.sourceMesh D.t/2) Ccount hq0 hqtop hCc hcard hfull hcap hlow hcrude
  have hrestore := restore_upper_bin_loss Finset.univ
    (fun i:rows'=>labelPolynomialPacket F.S F.exclusions η i.val
      (fun s:J=>sourcePrimePool F Z s.val) (fun s=>source_prime_pool_outside F Z s.val)
      (fun _=>F.W) (fun s=>Z^(D.ell s.val)) x z F.W (U^(ly/d))) Pmain U (D.t*(ell/d))
    (D.t+q*(ell/d)-q*((2*(ly/d)-1)/(6*D.momentKappa)-D.t/(3*D.momentKappa))/2+
      (3*R+1+2*D.t)/4+((2*a-1)*Cycle25.sourceMesh D.t/2)/2+(2*a-1)*D.t/4)
    (C*Ccount*(1+height)^degree*(U^(ly/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.ell s.val))^(-(4/25:ℝ))))
    hU0 hb
  have he : ((2*a-1)*Cycle25.sourceMesh D.t/2)/2=(2*a-1)*Cycle25.sourceMesh D.t/4 := by ring
  simpa only [he,Pmain] using hrestore

end Cycle25.Numerator
end

/- Adapted from weighted-numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. Variable moment parameter, genuine physical source. -/
