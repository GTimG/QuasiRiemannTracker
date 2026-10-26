/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The literal LOW and all buffered HIGH budgets use one original profile
control and one height degree. All finite costs precede the moving family. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalBufferedBudget
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.BandMonotonicity
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBandMonotonicity
open Record12518109Natural LocalMoment Cycle61InitialMass

def regularProfileControl (SL SH:Finset (ℕ×ℕ)):Finset (ℕ×ℕ):=
  insert (0,0) (SL∪SH)

theorem regular_profile_control {a b:ℝ}(p:Profiles a b)(SL SH:Finset (ℕ×ℕ)):
    (0,0)∈regularProfileControl SL SH ∧
    (p.control SL)^2≤(p.control (regularProfileControl SL SH))^2 ∧
    (p.control SH)^2≤(p.control (regularProfileControl SL SH))^2 := by
  have hL:SL⊆regularProfileControl SL SH:=
    Finset.subset_union_left.trans (Finset.subset_insert _ _)
  have hH:SH⊆regularProfileControl SL SH:=
    Finset.subset_union_right.trans (Finset.subset_insert _ _)
  exact ⟨Finset.mem_insert_self _ _,
    pow_le_pow_left₀ (p.control_nonneg _) (profile_control_mono p hL) 2,
    pow_le_pow_left₀ (p.control_nonneg _) (profile_control_mono p hH) 2⟩

def regularLowBudget (N J:ℕ)(C Cpref Cslot pc geometry control height Z exponent:ℝ):ℝ:=
  C*control*height^J*(Cpref*geometry*pc*(max 1 pc)^2)*Cslot^N*Z^exponent

/-- One common coefficient pays the two centered LOW corners (factor four)
and the full HIGH density sum. The only premises here are scalar ledgers;
the genuine source estimates supply precisely the two displayed budgets. -/
theorem regular_budget_common_control
    (N I JL JH:ℕ)(δ B τ upper e q saving:ℝ)
    (CL Cpref Cslot CH pcCap box:ℝ)(SL SH:Finset (ℕ×ℕ))
    (hCL:0≤CL)(hCpref:0≤Cpref)(hCslot:0≤Cslot)(hCH:0≤CH)
    (hpcCap:0≤pcCap)(hbox:0≤box)(hu:1≤upper)(hq:1/2≤q)(hτ:0≤τ):
    ∃C:ℝ,0<C ∧ ∀{a b:ℝ}(p:Profiles a b)(Z height pc geometry omega err errv fee reserve other pref lowExponent:ℝ),
      1<Z→1≤height→0≤pc→pc≤pcCap→0≤geometry→0≤omega→0≤err→
      lowExponent≤-saving→
      pref+2*δ+τ*(JH:ℝ)+omega+err+errv+other+saving≤fee+reserve→
      4*regularLowBudget N JL CL Cpref Cslot pc geometry ((p.control SL)^2) height Z lowExponent+
        (∑k∈BufferedSelectedPaidSome.highBins e q,
          bufferedPaidBudget N I JH δ B τ upper Z e omega err errv fee reserve other pref
            CH pc geometry ((p.control SH)^2) box k)≤
      C*geometry*(p.control (regularProfileControl SL SH))^2*height^JL*Z^(-saving) := by
  let KL:=CL*Cpref*Cslot^N*pcCap*(max 1 pcCap)^2
  let KH:=((BufferedSelectedPaidSome.highBins e q).card:ℝ)*
    (CH*pcCap*(max 1 pcCap)^2*cofactorFixedRestoration δ B*
      bufferedHeightConstant I JH*upper^(3*N)*box)
  have hr:0≤cofactorFixedRestoration δ B:=by unfold cofactorFixedRestoration;positivity
  have hh:0≤bufferedHeightConstant I JH:=by unfold bufferedHeightConstant;positivity
  have hKL:0≤KL:=by dsimp [KL];positivity
  have hKH:0≤KH:=by dsimp [KH];positivity
  refine ⟨1+4*KL+KH,by positivity,?_⟩
  intro a b p Z height pc geometry omega err errv fee reserve other pref lowExponent
    hZ hheight hpc hpc' hgeometry homega herr hlow hhigh
  have hp:=regular_profile_control p SL SH
  have ht:1≤height^JL:=one_le_pow₀ hheight
  have hSL:=profile_control_mono p (show SL⊆regularProfileControl SL SH from Finset.subset_union_left.trans (Finset.subset_insert _ _))
  have hSH:=profile_control_mono p (show SH⊆regularProfileControl SL SH from Finset.subset_union_right.trans (Finset.subset_insert _ _))
  have hL:regularLowBudget N JL CL Cpref Cslot pc geometry ((p.control SL)^2) height Z lowExponent≤
      KL*geometry*(p.control (regularProfileControl SL SH))^2*height^JL*Z^(-saving):=by
    dsimp only [regularLowBudget,KL]
    calc
      _≤CL*(p.control (regularProfileControl SL SH))^2*height^JL*
        (Cpref*geometry*pcCap*(max 1 pcCap)^2)*Cslot^N*Z^(-saving):=by
          gcongr <;> first | exact p.control_nonneg _ | exact hSL | exact hZ.le
      _=_:=by ring
  have hH:=buffered_paid_sum N I JH δ B τ upper Z e q omega err errv fee reserve other pref saving
    CH pc geometry ((p.control SH)^2) box hZ hτ hu hq hCH hpc hgeometry (sq_nonneg _) hbox
    homega herr hhigh
  have hH':(∑k∈BufferedSelectedPaidSome.highBins e q,
      bufferedPaidBudget N I JH δ B τ upper Z e omega err errv fee reserve other pref
        CH pc geometry ((p.control SH)^2) box k)≤
      KH*geometry*(p.control (regularProfileControl SL SH))^2*height^JL*Z^(-saving):=by
    refine hH.trans ?_
    calc
      _≤KH*geometry*(p.control (regularProfileControl SL SH))^2*Z^(-saving):=by
        dsimp only [KH]
        gcongr <;> first | exact p.control_nonneg _ | exact hSH
      _≤_:=by
        have hmul:=mul_le_mul_of_nonneg_left ht
          (show 0≤KH*geometry*(p.control (regularProfileControl SL SH))^2*Z^(-saving) by positivity)
        convert hmul using 1 <;> ring
  have hfac:0≤geometry*(p.control (regularProfileControl SL SH))^2*height^JL*Z^(-saving):=by positivity
  calc
    _≤4*(KL*geometry*(p.control (regularProfileControl SL SH))^2*height^JL*Z^(-saving))+
        KH*geometry*(p.control (regularProfileControl SL SH))^2*height^JL*Z^(-saving):=by linarith only [hL,hH']
    _≤_:=by nlinarith only [hfac]
end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_profile_control
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_budget_common_control
