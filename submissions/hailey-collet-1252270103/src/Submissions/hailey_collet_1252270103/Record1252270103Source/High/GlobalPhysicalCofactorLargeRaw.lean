/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual frozen centered family enters the large-slot RAW count with its
original row weights. The small slots are paid from the same actual zero bin. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalNaturalCofactorRaw
import Submissions.hailey_collet_1252270103.Record12518109Natural.TwoCommonLargeSlotShell
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open Set Filter HeckeFamily ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion CenteredMomentRetainedProfile
open CenteredMomentCommonMaskExpansion CenteredMomentHeckeSlots Cycle61Moment
open QRH.Record1252270103Low QRH.Record1252270103Restoration QRH.Record1252270103KernelMass
open Record1252270103Source Record1252270103Second HeckePrimeAnnular
open Record12518109Natural Record12518109Natural.WeightedHigh Record12518109Natural.MarkedPlain
local notation "O"=>ActualEisensteinCubic.O
variable (M:Ideal O) [NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)

def originalRawCoefficient {α:Type*} (η₀:Character) (W:ℝ→ℂ) (Z:ℝ)
    (w σ v:α→ℝ) (θ:α→RayQuotient.Characters M H) (j:α) : Ideal O→ℂ :=
  fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
    annularWeight W (Z^(w j)) (σ j) (v j) I

theorem eventual_cofactor_large_raw (ap bp:ℝ) (hap:0<ap) (N:ℕ) :
    ∃bound:ℕ→ℝ,(∀k,0<bound k) ∧
    ∀P:HighSourceParameters,P.profileBound=bound→P.B₀=2→
    8*P.τ≤P.d*P.vslot→16*P.τ≤P.d*P.vplain→
    ∃control:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
    ∀η₀:Character,∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀{Row α:Type}[Fintype α][DecidableEq α]
      (rows:Finset Row)(ι:Row→Type)[∀u,Fintype (ι u)]
      (s:∀u,Input (ι u)) (A₁ A₂ R:Row→Ideal O) (S A:Finset (Ideal O))
      (T:Finset α)(w σ v:α→ℝ)(θ:α→RayQuotient.Characters M H)
      (st:Row→NaturalState Z P.Bmask P.bΦ)
      (hQM:∀u,(st u).fixedModulus≤M)(hQη:∀u,(st u).fixedModulus≤η₀.modulus)
      (z:Row→O)(hz:∀u,(st u).radial.keep (z u))
      (p:Row→Profiles ap bp)(t base weight:Row→ℝ)
      (a b δ B Kcontrol wmin:ℝ)(i:ℕ),
    Fintype.card α≤N→51/100≤a→a≤1→(i:ℝ)≤Z^P.τ→
    0≤b→bp≤b→0<δ→0≤B→0≤Kcontrol→GoodPair (newtonDivisorPair S A)→
    (∀u∈rows,A₁ u≠0)→(∀u∈rows,A₂ u≠0)→(∀u∈rows,A₁ u*A₂ u∣R u)→
    (∀u∈rows,(st u).puncture=R u*((newtonDivisorPair S A).1*(newtonDivisorPair S A).2))→
    (∀u∈rows,(st u).width≤P.Mcap)→
    (∀u∈rows,(st u).radial.profile (‖eisEmbedding (z u)‖^2/(st u).radial.scale)≠0)→
    (∀u∈rows,HeckeDetectorZeros.zeroMaximum
      (wholeSourceFamily M H hH η₀ (excluded (naturalRow (st u).character (z u) ((st u).row_ne_zero (z u) (hz u))).character (st u).puncture))
      (whole_source_family_nonprincipal M H hH (st u) η₀ (hQM u) (hQη u) (z u) (hz u) _)
      (3*(i+1:ℕ)*Z^P.τ)<a+2*P.e)→
    (∀j,0≤w j)→(∀j,w j/P.d≤P.Rwidth)→
    (∀j,P.σmin≤σ j)→(∀j,σ j≤P.σmax)→
    (∀u∈rows,∀j,|t u+v j|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ)→
    (∀u∈rows,|t u|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ)→
    (∀j∈T,∀I∈CenteredMomentPrimeSlot.primePool M H 2 (Z^(w j)),IsCoprime I ((newtonDivisorPair S A).1*(newtonDivisorPair S A).2))→
    (∀u∈rows,(s u).W₁=((p u).profile 0:ℝ→ℂ))→
    (∀u∈rows,(s u).W₂=((p u).profile 1:ℝ→ℂ))→
    (∀u∈rows,(s u).X₁≤Z^(P.d*P.Rplain) ∧ (s u).X₂≤Z^(P.d*P.Rplain) ∧
      (s u).Y₁≤Z^(P.d*P.Rplain) ∧ (s u).Y₂≤Z^(P.d*P.Rplain))→
    (∀u∈rows,b^2*(s u).X₁*(s u).X₂≤Z^B)→
    (∀u∈rows,((p u).control control)^2≤Kcontrol)→
    (∀u∈rows,0≤weight u)→
    (∀u∈rows,(s u).X₁*(s u).X₂≤Z^(base u-∑j∈T,w j))→
    (∑u∈rows,‖newtonCofactorPlain (s u) (A₁ u) (A₂ u) (R u) b S A (st u).character (t u) (z u)*
      (∏j:T,normalizedSlot (st u).character (fixedBadMask*idealGenerator (R u)) 1 (z u)
        (CenteredMomentPrimeSlot.primePool M H 2 (Z^(w j))) (originalRawCoefficient M H hH η₀ P.Wslot Z w σ v θ j) (t u) (Z^(w j)))‖^2*weight u)≤
    cofactorRestorationCost δ B Z*C*Kcontrol*Z^(2*P.εplain*P.d+(2*P.εslot*P.d)*N)*
      ∑u∈rows,weight u*Z^((2*a-1)*(base u-∑j∈largeSlots T w wmin,w j))*
        (∏j∈largeSlots T w wmin,max 1 ‖labeledRawSlot M H hH η₀ P.Wslot Z w σ v t θ
          (fun u=>excluded (naturalRow (st u).character (z u) ((st u).row_ne_zero (z u) (hz u))).character (st u).puncture) u j‖)^2 := by
  obtain ⟨bound,hbound,hsource⟩:=eventual_natural_cofactor_raw M H hH ap bp hap
  refine ⟨bound,hbound,?_⟩
  intro P hpeq hB₀ hslot hplain
  obtain ⟨control,Cp,hCp,hcof⟩:=hsource P hpeq hslot hplain
  obtain ⟨Cs,hCs,hcaps⟩:=actual_retained_slot_caps M H hH P hslot hplain
  refine ⟨control,Cp*Cs^N,mul_pos hCp (pow_pos (zero_lt_one.trans_le hCs) _),?_⟩
  intro η₀
  filter_upwards [hcof η₀,hcaps η₀] with Z hc hs
  refine ⟨hc.1,?_⟩
  intro Row α _ _ rows ι _ s A₁ A₂ R S A T w σ v θ st hQM hQη z hz p t base weight
    a b δ B Kcontrol wmin i hN ha ha' hi hb hbp hδ hB hK hd hA₁ hA₂ hAR hpuncture hwidth hradial
    hupper hw hwr hσlo hσhi hfreq hplainfreq havoid hW₁ hW₂ hscales hcut hcontrol hwgt hbase
  have hZp:0<Z:=zero_lt_one.trans hc.1
  have hν:0≤2*a-1:=by linarith
  let amp:=labeledRawSlot M H hH η₀ P.Wslot Z w σ v t θ
    (fun u=>excluded (naturalRow (st u).character (z u) ((st u).row_ne_zero (z u) (hz u))).character (st u).puncture)
  have hcap (u:Row)(hu:u∈rows)(j:α) : (max 1 ‖amp u j‖)^2≤Cs*Z^((2*a-1)*w j+2*P.εslot*P.d) := by
    have hh:=hs.2 (st u) (hwidth u hu) (hQM u) (hQη u) (z u) (hz u) a i ha ha' hi
      (hradial u hu) (hupper u hu) (w j) (σ j) (t u) (v j) (θ j)
      (hw j) (hwr j) (hσlo j) (hσhi j) (hfreq u hu j)
    simpa only [amp,labeledRawSlot,hB₀] using hh
  have hsum : (∑u∈rows,‖newtonCofactorPlain (s u) (A₁ u) (A₂ u) (R u) b S A (st u).character (t u) (z u)*
      (∏j:T,normalizedSlot (st u).character (fixedBadMask*idealGenerator (R u)) 1 (z u)
        (CenteredMomentPrimeSlot.primePool M H 2 (Z^(w j))) (originalRawCoefficient M H hH η₀ P.Wslot Z w σ v θ j) (t u) (Z^(w j)))‖^2*weight u)≤
      (cofactorRestorationCost δ B Z*Cp*Kcontrol)*
      ∑u∈rows,weight u*Z^((2*a-1)*(base u-∑j∈T,w j)+2*P.εplain*P.d)*
        (∏j∈T,max 1 ‖amp u j‖)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u hu
    have hh:=hc.2 (st u) (hQM u) (hQη u) (z u) (hz u) (hwidth u hu) (hradial u hu)
      a i ha ha' hi (hupper u hu) (s u) (A₁ u) (A₂ u) (R u) S A
      (fun j:T=>CenteredMomentPrimeSlot.primePool M H 2 (Z^(w j)))
      (fun j:T=>originalRawCoefficient M H hH η₀ P.Wslot Z w σ v θ j)
      (fun j:T=>Z^(w j)) (hA₁ u hu) (hA₂ u hu) (hAR u hu) hd (hpuncture u hu)
      (fun j=>Real.rpow_pos_of_pos hZp _) (fun j I hI=>havoid j j.property I hI)
      (p u) (t u) b δ B (hW₁ u hu) (hW₂ u hu) hb hbp
      (hscales u hu).1 (hscales u hu).2.1 (hscales u hu).2.2.1 (hscales u hu).2.2.2
      (hplainfreq u hu) hδ hB (hcut u hu)
    have hprod : (∏j:T,max 1 ‖naturalSlot (excluded (naturalRow (st u).character (z u) ((st u).row_ne_zero (z u) (hz u))).character (st u).puncture)
        (CenteredMomentPrimeSlot.primePool M H 2 (Z^(w j))) (CenteredMomentCommonMaskEnergy.heightCoefficient
          (originalRawCoefficient M H hH η₀ P.Wslot Z w σ v θ j) (t u)) (Z^(w j))‖)=
        ∏j∈T,max 1 ‖amp u j‖ := by
      change (∏j:T,max 1 ‖amp u j‖)=_
      exact Finset.prod_attach T (fun j=>max 1 ‖amp u j‖)
    rw [hprod] at hh
    have hr : ((s u).X₁*(s u).X₂)^(2*a-1)≤Z^((2*a-1)*(base u-∑j∈T,w j)) := by
      have he:=Real.rpow_le_rpow (mul_pos (s u).X₁_pos (s u).X₂_pos).le (hbase u hu) hν
      rw [←Real.rpow_mul hZp.le] at he
      simpa only [mul_comm] using he
    have hcst:0≤cofactorRestorationCost δ B Z:=by unfold cofactorRestorationCost;positivity
    have hp : Cp*((p u).control control)^2*((s u).X₁*(s u).X₂)^(2*a-1)≤
        Cp*Kcontrol*Z^((2*a-1)*(base u-∑j∈T,w j)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hcontrol u hu) hCp.le) hr
        (Real.rpow_nonneg (mul_pos (s u).X₁_pos (s u).X₂_pos).le _) (mul_nonneg hCp.le hK)
    apply (mul_le_mul_of_nonneg_right hh (hwgt u hu)).trans
    have he:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hZp.le (2*P.εplain*P.d))) (sq_nonneg (∏j∈T,max 1 ‖amp u j‖))) hcst)
      (hwgt u hu)
    simpa only [Real.rpow_add hZp,mul_assoc,mul_comm,mul_left_comm] using he
  have hdsc:=weighted_normalized_products_discard rows (fun _=>T) (fun _=>largeSlots T w wmin)
    (fun _ _=>Finset.filter_subset _ _) w amp base weight Z Cs (2*a-1) (2*P.εslot*P.d) (2*P.εplain*P.d)
    hc.1 hCs (mul_nonneg (mul_nonneg (by norm_num) P.hεs.le) P.hd.le) N (fun _ _=>(Finset.card_le_univ T).trans hN) hwgt (fun u hu j _=>hcap u hu j)
  have hcst:0≤cofactorRestorationCost δ B Z*Cp*Kcontrol:=by unfold cofactorRestorationCost;positivity
  apply hsum.trans
  apply (mul_le_mul_of_nonneg_left hdsc hcst).trans_eq
  dsimp only [amp]
  ring

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.eventual_cofactor_large_raw
