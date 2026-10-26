/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual frozen centered cofactor rows from the same natural zero bin and
literal RAW slots. No ordinary-row energy estimate is assumed. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalCofactorRestoration
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.RegularPositiveRawNatural
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
open CenteredMomentCommonMaskExpansion
open CenteredMomentHeckeSlots Cycle61Moment
open QRH.Record1252270103Low QRH.Record1252270103Restoration QRH.Record1252270103KernelMass
open Record1252270103Source Record1252270103Second
local notation "O"=>ActualEisensteinCubic.O
variable (M:Ideal O) [NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)

theorem eventual_natural_cofactor_raw (ap bp:ℝ) (hap:0<ap) :
    ∃bound:ℕ→ℝ,(∀k,0<bound k) ∧
    ∀P:HighSourceParameters,P.profileBound=bound→
    8*P.τ≤P.d*P.vslot→16*P.τ≤P.d*P.vplain→
    ∃control:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
    ∀η₀:Character,∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(st:NaturalState Z P.Bmask P.bΦ)
      (hQM:st.fixedModulus≤M) (hQη:st.fixedModulus≤η₀.modulus)
      (z:O) (hz:st.radial.keep z),
    st.width≤P.Mcap→st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)≠0→
    ∀(a:ℝ)(i:ℕ),51/100≤a→a≤1→(i:ℝ)≤Z^P.τ→
    HeckeDetectorZeros.zeroMaximum
      (wholeSourceFamily M H hH η₀ (excluded (naturalRow st.character z (st.row_ne_zero z hz)).character st.puncture))
      (whole_source_family_nonprincipal M H hH st η₀ hQM hQη z hz _)
      (3*(i+1:ℕ)*Z^P.τ)<a+2*P.e→
    ∀{ι J:Type*}[Fintype ι][Fintype J][DecidableEq J]
      (s:Input ι)(A₁ A₂ R:Ideal O)(S A:Finset (Ideal O))
      (slots:J→Finset (Ideal O))(coeff:J→Ideal O→ℂ)(scale:J→ℝ),
    A₁≠0→A₂≠0→A₁*A₂∣R→GoodPair (newtonDivisorPair S A)→
    st.puncture=R*((newtonDivisorPair S A).1*(newtonDivisorPair S A).2)→
    (∀j,0<scale j)→
    (∀j I,I∈slots j→IsCoprime I ((newtonDivisorPair S A).1*(newtonDivisorPair S A).2))→
    ∀(p:Profiles ap bp)(t b δ B:ℝ),
    s.W₁=(p.profile 0:ℝ→ℂ)→s.W₂=(p.profile 1:ℝ→ℂ)→0≤b→bp≤b→
    s.X₁≤Z^(P.d*P.Rplain)→s.X₂≤Z^(P.d*P.Rplain)→
    s.Y₁≤Z^(P.d*P.Rplain)→s.Y₂≤Z^(P.d*P.Rplain)→
    |t|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ→0<δ→0≤B→b^2*s.X₁*s.X₂≤Z^B→
    ‖newtonCofactorPlain s A₁ A₂ R b S A st.character t z*
      (∏j,normalizedSlot st.character (fixedBadMask*idealGenerator R) 1 z (slots j) (coeff j) t (scale j))‖^2≤
    cofactorRestorationCost δ B Z*
      (C*(p.control control)^2*(s.X₁*s.X₂)^(2*a-1)*Z^(2*P.εplain*P.d)*
        (∏j,max 1 ‖naturalSlot (excluded (naturalRow st.character z (st.row_ne_zero z hz)).character st.puncture)
          (slots j) (CenteredMomentCommonMaskEnergy.heightCoefficient (coeff j) t) (scale j)‖)^2) := by
  obtain ⟨bound,hbound,hsource⟩:=eventual_natural_positive_raw M H hH ap bp hap
  refine ⟨bound,hbound,?_⟩
  intro P hboundeq hslot hplain
  obtain ⟨control,C,hC,hraw⟩:=hsource P hboundeq hslot hplain
  refine ⟨control,C,hC,?_⟩
  intro η₀
  filter_upwards [hraw η₀] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro st hQM hQη z hz hwidth hradial a i ha ha' hi hupper ι J _ _ _ s A₁ A₂ R S A slots coeff scale
    hA₁ hA₂ hAR hd hpuncture hscale havoid p t b δ B hW₁ hW₂ hb hbp hx₁ hx₂ hy₁ hy₂ hfreq hδ hB hcut
  have hν:0≤2*a-1:=by linarith
  have hZp:0<Z:=zero_lt_one.trans hZ.1
  have hprodpos:0<s.X₁*s.X₂:=mul_pos s.X₁_pos s.X₂_pos
  let raw:= (∏j,max 1 ‖naturalSlot (excluded (naturalRow st.character z (st.row_ne_zero z hz)).character st.puncture)
    (slots j) (CenteredMomentCommonMaskEnergy.heightCoefficient (coeff j) t) (scale j)‖)^2
  let budget:=C*(p.control control)^2*(s.X₁*s.X₂)^(2*a-1)*Z^(2*P.εplain*P.d)*raw
  apply newton_cofactor_pointwise_from_ordinary s A₁ A₂ R hA₁ hA₂ hAR S A hd st.character t z b hb
    (p.profile 0) (p.profile 1) hW₁ hW₂ (fun x hx=>(p.support 0 hx).2.trans hbp)
    (fun x hx=>(p.support 1 hx).2.trans hbp) slots coeff scale hscale havoid budget δ B Z
    (by dsimp [budget,raw];positivity) hδ hB hZ.1.le
  · apply le_trans _ hcut
    exact mul_le_mul (mul_le_mul_of_nonneg_left (shorten_positive s.X₁_pos hd.1).2 (sq_nonneg _))
      (shorten_positive s.X₂_pos hd.2.1).2 (shorten_positive s.X₂_pos hd.2.1).1.le
      (mul_nonneg (sq_nonneg _) s.X₁_pos.le)
  · intro X₁ X₂ hX₁ hX₂ hshort
    have hcap : X₁≤Z^(P.d*P.Rplain) ∧ X₂≤Z^(P.d*P.Rplain) := by
      rcases hshort with h|h
      · exact ⟨h.1.trans ((shorten_positive s.X₁_pos hd.1).2.trans hx₁),
          h.2.trans ((shorten_positive s.X₂_pos hd.2.1).2.trans hx₂)⟩
      · exact ⟨h.1.trans ((shorten_positive s.Y₁_pos hd.1).2.trans hy₁),
          h.2.trans ((shorten_positive s.Y₂_pos hd.2.1).2.trans hy₂)⟩
    have hprod : X₁*X₂≤s.X₁*s.X₂ := by
      rcases hshort with h|h
      · exact mul_le_mul (h.1.trans (shorten_positive s.X₁_pos hd.1).2)
          (h.2.trans (shorten_positive s.X₂_pos hd.2.1).2) hX₂.le s.X₁_pos.le
      · rw [←s.same_product]
        exact mul_le_mul (h.1.trans (shorten_positive s.Y₁_pos hd.1).2)
          (h.2.trans (shorten_positive s.Y₂_pos hd.2.1).2) hX₂.le s.Y₁_pos.le
    have hh:=hZ.2 st hQM hQη z hz hwidth hradial a i ha ha' hi hupper slots coeff scale hscale
      p ![X₁,X₂] t (by intro j;fin_cases j <;> assumption)
      (by intro j;fin_cases j;exact hcap.1;exact hcap.2) hfreq
    change ‖CenteredMomentRetainedEnergy.positiveSlotRow st.character st.mask 1 z _ _ _ _ _ t X₁ X₂‖^2≤_ at hh
    have hm : st.mask=fixedBadMask*idealGenerator (R*((newtonDivisorPair S A).1*(newtonDivisorPair S A).2)) := by
      change fixedBadMask*idealGenerator st.puncture=_
      rw [hpuncture]
    rw [hm] at hh
    apply hh.trans
    dsimp only [budget,raw]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (mul_pos hX₁ hX₂).le hprod hν)
          (mul_nonneg hC.le (sq_nonneg _))) (Real.rpow_nonneg hZp.le _)) (sq_nonneg _)

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.eventual_natural_cofactor_raw
