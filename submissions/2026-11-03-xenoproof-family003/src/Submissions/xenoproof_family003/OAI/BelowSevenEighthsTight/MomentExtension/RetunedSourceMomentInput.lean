/- UNVERIFIED source moment input and late height choice for rational retuning. -/
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.MomentExtension.RetunedSourceMoments
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedSourceData
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RetunedCountParameters
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RationalCertificate

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters
open HeckeInverseAmplification

def SourceMomentBound_retuned {Δ total margin mesh : ℝ} {D : _root_.BelowSevenEighthsTight.Parameters.RetunedHighData Δ total margin mesh} (F : _root_.BelowSevenEighthsTight.Parameters.RetunedSourceData D)
    (counts : _root_.BelowSevenEighthsTight.FiberExtension.RetunedCountParameters F.modulus ⊤ D.t) (η : Character)
    (Z τ C height : ℝ) : Prop :=
  ∀rows : Finset FreeRow,∀d a : ℝ, (1/200:ℝ)≤d → d≤7/8 → 51/100<a → a≤1 →
    (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-D.t)) →
    ∀i : ℕ,∀z : ℂ,z.re=17/50 → |z.im|≤height →
    SourceMomentsAt_retuned F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell (fun _ y=>(F.w y:ℂ))
      Z d a D.ε τ (7/8) 2 D.t D.t i z _root_.BelowSevenEighthsTight.kappaRat (_root_.BelowSevenEighthsTight.kappaRat+2*Δ)
      (if 2*a-1≤5/6 then counts.cB else counts.cH)
      (if 2*a-1≤5/6 then counts.kB else counts.kH) C height D.t

lemma SourceMomentBound_retuned.mono_constant {Δ total margin mesh : ℝ} {D : _root_.BelowSevenEighthsTight.Parameters.RetunedHighData Δ total margin mesh} {F : _root_.BelowSevenEighthsTight.Parameters.RetunedSourceData D}
    {counts : _root_.BelowSevenEighthsTight.FiberExtension.RetunedCountParameters F.modulus ⊤ D.t} {η : Character} {Z τ C C' height : ℝ}
    (hZ : 0≤Z) (h : SourceMomentBound_retuned F counts η Z τ C height) (hC : C≤C') :
    SourceMomentBound_retuned F counts η Z τ C' height := by
  intro rows d a hd hd' ha ha' hrows i z hz hzh
  exact sourceMomentsAt_retuned_mono_constant F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell
    (fun _ y=>(F.w y:ℂ)) Z d a D.ε τ (7/8) 2 D.t D.t i z _root_.BelowSevenEighthsTight.kappaRat (_root_.BelowSevenEighthsTight.kappaRat+2*Δ) _ _ C C' height D.t
    hZ hC (h rows d a hd hd' ha ha' hrows i z hz hzh)

lemma polynomial_height_absorption_retuned (C Z τ J t : ℝ)
    (hC : 0≤C) (hZ : 1≤Z) (hτ : 0≤τ) (hJ : 0≤J) (hbudget : 2*τ*(1+J)≤t) :
    C*(1+Z^(2*τ))^J≤(C*2^J)*Z^t := by
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hscale : 1≤Z^(2*τ) := Real.one_le_rpow hZ (by positivity)
  calc
    _≤C*(2*Z^(2*τ))^J := by gcongr;linarith
    _=(C*2^J)*Z^(2*τ*J) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Real.rpow_nonneg hZp.le _),←Real.rpow_mul hZp.le]
      ring
    _≤(C*2^J)*Z^t := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)

theorem chosen_source_height_retuned {Δ total margin mesh : ℝ}
    (D : _root_.BelowSevenEighthsTight.Parameters.RetunedHighData Δ total margin mesh)
    (F : _root_.BelowSevenEighthsTight.Parameters.RetunedSourceData D)
    (counts : _root_.BelowSevenEighthsTight.FiberExtension.RetunedCountParameters F.modulus ⊤ D.t)
    (h : ∃J : ℝ,0≤J ∧ ∀η : Character,∃C : ℝ,0<C ∧
      ∀τ : ℝ,0<τ → τ≤1 → ∀ᶠZ : ℝ in atTop,
        SourceMomentBound_retuned F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))) :
    ∃τ : ℝ,0<τ ∧ τ<(1/200:ℝ)/2 ∧ 4*τ<(1/200:ℝ)*D.cost ∧ τ<D.t ∧
      2*τ≤D.t ∧ τ*(2+4*D.eps)<D.t ∧
      ∀η : Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
        SourceMomentBound_retuned F counts η Z τ (C*Z^D.t) (Z^(2*τ)) := by
  obtain ⟨J,hJ,hbound⟩ := h
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτJ,hτeps⟩ := D.height_choice J hJ
  have htau1 : τ≤1 := by linarith
  refine ⟨τ,hτ,hτd,hτcost,hτt,by nlinarith,hτeps,?_⟩
  intro η
  obtain ⟨C,hC,hbound⟩ := hbound η
  refine ⟨C*2^J,by positivity,?_⟩
  filter_upwards [hbound τ hτ htau1,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  exact hb.mono_constant (by linarith) (polynomial_height_absorption_retuned C Z τ J D.t hC.le hZ hτ.le hJ hτJ)

end SevenEighths.ProbeFinalAssembly

end

end OAI

#print axioms OAI.SevenEighths.ProbeFinalAssembly.SourceMomentBound_retuned.mono_constant
#print axioms OAI.SevenEighths.ProbeFinalAssembly.polynomial_height_absorption_retuned
#print axioms OAI.SevenEighths.ProbeFinalAssembly.chosen_source_height_retuned
