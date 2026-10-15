/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B001
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B030
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B033
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B042
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B058
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B059
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B060
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalPhysicalRemainder
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CanonicalCubeReduction
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeFiniteIntegral
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowFullBudget

/- BEGIN ORIGINAL MODULE Global.Low.Reflection.LowFullBudget ; sha256 09d0bcab2e8737c470a56f92596261b1a5a5be1e63bc32f0fdf21f325acafdb7 -/
section



/-! Adapted from OpenAI/math family003, pinned original module Reflection.LowFullBudget.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

namespace LowReflection
open InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_low_sector_full_budget
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0< lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤ Lpool)
    (Lcap saving : ℝ) (hδ : 0<δ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0< C ∧ 1< Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot : ℝ),
      Z₀≤ Z → 0< Ck → 0< CO → 0< CH → 0< X → 0< QK → 0< QP →
      (Ideal.absNorm I:ℝ)≤ Ck*Z^((1-Submission20261012.Global.ell)-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤ O₀+η → normWidth Z Q≤η →
      0≤ d → d≤ Submission20261012.Global.ell → ell0≤ Submission20261012.Global.ell-d+η → 0≤ O₀ → za≤ ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤δ → δ≤η → QK≤ Z^Lrow → (QP/2)≤ Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      X⁻¹≤ Z^Lcap → QK≤ Z^Lcap → QP≤ Z^Lcap → -saving≤((1-Submission20261012.Global.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2 →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤ Z^Lcap →
      (familyRawScale G s X QK QP)⁻¹≤ Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤ Z^Lpool →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤ QK → 2≤ QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤ QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤ QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖literalWholeRow G K.val (hrows K.val K.property) S j Pset
        (E.completion K) s hc₀ W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(((1-Submission20261012.Global.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2) := by
  obtain ⟨Adecay,htail⟩ := actual_finite_source_tail_budget s Lcap δ saving hδ
  obtain ⟨degree,degreeTail,Cm,Ct,Z₀,hCm,hCt,hZ₀,henergy⟩ := original_low_sector_full_energy
    (Nlevel:=Nlevel) Adecay ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
    κ δ Lscale Lpool hκ hδL hLpool
  let cusp := 27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c₀}):ℝ)^2
  let deg := max degree (degreeTail*2)
  refine ⟨deg,Cm+2*Ct^2*cusp^4+1,max Z₀ 128,by positivity,
    lt_of_lt_of_le hZ₀ (le_max_left _ _),?_⟩
  intro σ _ J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
  dsimp only
  intro hFcap hscap hpool rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let G := (poolPrimeFamily J Q Q₀).restrict A
  have hz' : 1< Z := lt_of_lt_of_le hZ₀ ((le_max_left _ _).trans hZ)
  have hzpos : 0< Z := lt_trans zero_lt_one hz'
  have h128 : 128≤ Z := (le_max_right _ _).trans hZ
  have hs := henergy J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    ((le_max_left _ _).trans hZ) hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hscap hpool
    rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  have ht := htail G rows Pset Z X QK QP h128 hX hqk (by linarith only [hqp])
    (fun K hK => ⟨(hrows K hK).1,(hKr K hK).2⟩)
    (fun P hP => ⟨(hPr P hP).1.1.ne_zero,(hPr P hP).2.2⟩) hFcap hKcap hPcap hXi
  have hheight : 1≤1+‖θ‖ := by linarith only [norm_nonneg θ]
  have hdm : (1+‖θ‖)^degree≤(1+‖θ‖)^deg := pow_le_pow_right₀ hheight (le_max_left _ _)
  have hdt : (1+‖θ‖)^(degreeTail*2)≤(1+‖θ‖)^deg := pow_le_pow_right₀ hheight (le_max_right _ _)
  have he := Real.rpow_le_rpow_of_exponent_le hz'.le hexp
  apply hs.trans
  have htailbound : 2*rows.card*(Pset.card*Ct*(1+‖θ‖)^degreeTail*
        ((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*(Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹)^2≤
      (2*Ct^2*cusp^4)*(1+‖θ‖)^deg*Z^(((1-Submission20261012.Global.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2) := by
    calc
      _ = (2*Ct^2*(1+‖θ‖)^(degreeTail*2))*
          (rows.card*(Pset.card*((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*
            (Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹)^2) := by rw [pow_mul];ring
      _ ≤ (2*Ct^2*(1+‖θ‖)^(degreeTail*2))*(cusp^4*Z^(-saving)) := by
        exact mul_le_mul_of_nonneg_left ht (by positivity)
      _ ≤ (2*Ct^2*(1+‖θ‖)^deg)*(cusp^4*Z^(((1-Submission20261012.Global.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2)) := by gcongr
      _ = _ := by ring
  have hmain : Cm*(1+‖θ‖)^degree*Z^(((1-Submission20261012.Global.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2)≤
      Cm*(1+‖θ‖)^deg*Z^(((1-Submission20261012.Global.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2) := by gcongr
  apply (add_le_add hmain htailbound).trans
  have hp : 0≤(1+‖θ‖)^deg*Z^(((1-Submission20261012.Global.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2) := by positivity
  nlinarith only [hp]
end
end LowReflection

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Reflection.LowFullBudget -/

/- BEGIN ORIGINAL MODULE Global.Transport.CanonicalCubeReduction ; sha256 ded75512f5b170dedcd08b32f730aa982d50136053bbc585722fa9c9f4d56beb -/
section
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/





open OAI OAI.SevenEighths

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace Submission20261012.Global.HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem canonical_probe_minus_cube (K : ℕ) (e δ a b B ζ saving τ : ℝ)
    (he : 0 < e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0 < a) (hb : 0 < b) (hB : 0≤ B) (hβ : HeckeZeroSupremum.beta≤(7/8:ℝ))
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0 < C ∧ ∀(η : Character) (Z : ℝ),1≤ Z →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤ length i) → (∑i,length i)=(Submission20261012.Global.ell:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤ b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤ B) →
      ∀(alpha base H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character),
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((Submission20261012.Global.h:ℝ)+ζ)),
        (51/100:ℝ)≤ alpha u ∧ alpha u≤1 ∧ 2 < base u ∧ Z^τ≤ H u ∧ H u≤(3*idx u+2:ℕ)*base u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*base u) < alpha u+2*e) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=> canonicalSlotSupport (T i)) W (fun i=> Z^(length i)) (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=> Z^(length i)) W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/100:ℝ)) (Z^((Submission20261012.Global.h:ℝ)+ζ))) T hT W (fun i=> Z^(length i))
          W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z e alpha H‖≤
        C*(η.modulus.absNorm:ℝ)^2*(Z^((7/8:ℝ)-(4+Submission20261012.Global.b)/6-(Submission20261012.Global.ly/2-Submission20261012.Global.h*(17/50-1/6)-1/50)+8*e)+Z^(-saving)) := by
  obtain ⟨C0,hC0,h0⟩ := canonical_probe_minus_central K e δ a b B ζ saving he he' hδ hδ' hζ ha hb hB hβ
    S hS hmax (hfirst.mono_parameter (by linarith)) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨C1,hC1,h1⟩ := finite_cube_arbitrary_saving (ι:=ι) K τ saving b ζ B hτ hb hζ' hB e he he'
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C0+C1,add_pos_of_pos_of_nonneg hC0 hC1,?_⟩
  intro η Z hZ T hT hdis length hl0 hl hpool W hWS hWB alpha base H idx ψ hbin
  have h0' := h0 η Z hZ T hT hdis length hl0 hl W hWS hWB
  let R := rowBand (Z^(1/100:ℝ)) (Z^((Submission20261012.Global.h:ℝ)+ζ))
  have hR (u : FreeRow) (hu : u∈R) : u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤ Z^((Submission20261012.Global.h:ℝ)+ζ) :=
    ⟨(mem_rowBand.mp hu).1,(mem_rowBand.mp hu).2.2.le⟩
  have h1' := h1 η Z hZ R hR T hT hdis length hl hpool W hWB alpha base H idx ψ hbin
  have hQ := HeckeLogarithmicInput.modulus_norm_ge_one η
  have hQδ : (η.modulus.absNorm:ℝ)^δ≤(η.modulus.absNorm:ℝ)^2 := by
    rw [←Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hQ (by linarith)
  let E := Z^((7/8:ℝ)-(4+Submission20261012.Global.b)/6-(Submission20261012.Global.ly/2-Submission20261012.Global.h*(17/50-1/6)-1/50)+8*e)+Z^(-saving)
  have hE : 0≤ E := by dsimp [E];positivity
  have hsave : Z^(-saving)≤ E := by dsimp [E];have : 0≤ Z^((7/8:ℝ)-(4+Submission20261012.Global.b)/6-(Submission20261012.Global.ly/2-Submission20261012.Global.h*(17/50-1/6)-1/50)+8*e) := Real.rpow_nonneg (by linarith) _;linarith
  have h0'' : ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=> canonicalSlotSupport (T i)) W (fun i=> Z^(length i)) (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=> Z^(length i)) W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z-
        finitePhysicalRows S hmax η R T W (fun i=> Z^(length i)) W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z‖≤
      C0*(η.modulus.absNorm:ℝ)^2*E :=
    h0'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQδ hC0.le) hE)
  have h1'' := h1'.trans (mul_le_mul_of_nonneg_left hsave (mul_nonneg hC1 (sq_nonneg (η.modulus.absNorm:ℝ))))
  apply (norm_sub_le_norm_sub_add_norm_sub _
    (finitePhysicalRows S hmax η R T W (fun i=> Z^(length i)) W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z) _).trans
  exact (add_le_add h0'' h1'').trans_eq (by dsimp [E];ring)

end Submission20261012.Global.HighRowFamily

end


end
/- END ORIGINAL MODULE Global.Transport.CanonicalCubeReduction -/

/- BEGIN ORIGINAL MODULE Global.Transport.PrincipalRemainderPhysicalBounds ; sha256 530ab65047eb2dff9d6988eaa60540540de85b1643a17f6b435a5a2c4344cb00 -/
section
/- Adapted from Submission20261012.Global.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/




noncomputable section
open scoped Classical BigOperators
open Complex MeasureTheory
namespace Submission20261012.Global.Transport.PrincipalPhysical
open OAI OAI.SevenEighths OAI.SevenEighths.ProbePrincipalPhysical
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbeMellinBoundary ProbePrincipalContours
open Submission20261012.Global.Transport.PrincipalFiniteProduct Submission20261012.Global.Transport.PrincipalContours
local notation "Id" => Ideal HeckeFamily.O

theorem physical_principal_residue_remainder {K : ℕ}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B : ℝ) (hc : 0< c) (hd : c ≤ d) (hB : 0 ≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (e : ℝ) (he : 0< e) (hehi : e ≤ 1/1000)
    (ha : theta < HeckeZeroSupremum.beta+e) (ha2 : HeckeZeroSupremum.beta+e ≤ 2) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0< C ∧ ∀slotEll : Fin K→ℝ,(∑j,slotEll j)=ell → ∀W : Fin K→ℝ→ℝ,
    (∀j x,0 ≤ W j x ∧ W j x ≤ B) → (∀j,Function.support (W j)⊆Set.Icc c d) →
    ∀T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal,(∀j p,p∈T j→p.val∉S) →
    (∀P:(∀j,T j),Function.Injective (fun j=>(P j).val)) →
    ∀Z : ℝ,1 ≤ Z → (∀j,480 ≤ c*Z^(slotEll j)) → (∀j,(Ideal.absNorm η.modulus:ℝ)< c*Z^(slotEll j)) →
    ‖(∑P:(∀j,T j),(∏j,(W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(slotEll j)):ℂ))*
        principalRowIntegral η S (fun j=> primaryGenerator (P j).val.val)
          W0 W1 (Z^(lx:ℝ)) (Z^(ly:ℝ)) Z)-
      sourceResidueIntegral W0 W1 (∏p∈S,p) (η.excludePrimes S hS.prime)
        (HeckeZeroSupremum.beta+e) (Z^(lx:ℝ)) (Z^(ly:ℝ)) Z
        (globalClosedCorrection η S)
        (windowMultiplier η Finset.univ T (fun j x=>(W j x:ℂ)) (fun j=> Z^(slotEll j)))‖ ≤
      C/e*Z^(HeckeZeroSupremum.beta-(4+b)/6-1/4000) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hbound⟩ := Submission20261012.Global.Transport.PrincipalRemainderBounds.source_remainders_strict_saving η S hS
    (Finset.univ : Finset (Fin K)) c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ⟨ha.le,ha2⟩
  refine ⟨2*C,by positivity,?_⟩
  intro slotEll hell W hW hsupp T hT hdis Z hZ hthreshold hmod
  have hZ0 : 0< Z := by linarith [Submission20261012.Global.Transport.theta_bounds]
  have hb := hbound slotEll hell W (fun j _=> hW j) (fun j _=> hsupp j) T (fun j _ p hp=> hT j p hp)
    Z hZ (fun j _=> hthreshold j) (fun j _=> hmod j)
  dsimp only at hb
  have heq := Submission20261012.Global.Transport.PrincipalPhysical.principal_physical_pool_ordered η S hS T hT hdis
    (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/Z^(slotEll j)):ℂ)) W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 (Z^(lx:ℝ)) (Z^(ly:ℝ)) Z (HeckeZeroSupremum.beta+e) e
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0 ha (by linarith [Submission20261012.Global.Transport.theta_bounds]) (by linarith [Submission20261012.Global.Transport.theta_bounds]) he (by linarith [Submission20261012.Global.Transport.theta_bounds])
  dsimp only at heq
  have hres (F : ℂ→ℂ) :
      (HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1)^2/6*
        verticalIntegral (HeckeZeroSupremum.beta+e) F=
      verticalIntegral (HeckeZeroSupremum.beta+e) (fun s=> fixedPrincipalResidue (∏p∈S,p)^2/6*F s) := by
    rw [verticalIntegral,verticalIntegral,integral_const_mul]
    dsimp only [fixedPrincipalResidue,fixedPrincipal,fixedSourcePrincipal]
    ring
  rw [heq]
  unfold sourceResidueIntegral windowMultiplier
  rw [hres,add_sub_cancel_right]
  have hn := (norm_add_le _ _).trans (add_le_add hb.1 hb.2)
  change _ ≤ (2*C)/e*Z^(HeckeZeroSupremum.beta-(4+b)/6-1/4000)
  apply hn.trans
  have hCe : C ≤ C/e := (le_div_iff₀ he).mpr (by nlinarith)
  have hzpow : 0 ≤ Z^(HeckeZeroSupremum.beta-(4+b)/6-1/4000) := Real.rpow_nonneg hZ0.le _
  have htwo : (2*C)/e=2*(C/e) := by ring
  rw [htwo]
  nlinarith
end Submission20261012.Global.Transport.PrincipalPhysical
end

end
/- END ORIGINAL MODULE Global.Transport.PrincipalRemainderPhysicalBounds -/

/- BEGIN ORIGINAL MODULE Analytic.JointBufferedFibers ; sha256 b3b189bac29a5eb360eb50124a0e0ee89ad808c1f42c8316e6b3a5779cf2c51f -/
section



/-! Finite allocation fibers for the literal buffered high-bin products.
A selected branch on a finite support extends to the existing full-function
API by changing only unused rows outside that support. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification CenteredMomentNaturalRowSource
local notation "O" => HeckeFamily.O

namespace SurvivingBufferedData
variable {η : Character} {w : NonzeroElement} {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
  {orders : Finset Slot → ℕ} {profileBound : ℕ → ℝ} {a e : ℝ}

/-- Used only to extend selected data away from the finite summation set. -/
def rebase (D : SurvivingBufferedData η w Slot orders profileBound a e) (w' : NonzeroElement) :
    SurvivingBufferedData η w' Slot orders profileBound a e where
  slots := D.slots
  data := {D.data with natural := naturalRow D.data.parent.val w'.val w'.property}

end SurvivingBufferedData

/-- The complete allocation sum uses the one jointly counted estimate on
selected branches. Only the extraction-weight mass is paid. -/
theorem joint_buffered_product_fibers
    {α : Type*} [DecidableEq α] {β : α → Type*}
    {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (η : Character) (η₀ : Slot → Character) (V : Slot → ℝ → ℂ) (Bprofile : Slot → ℝ)
    (orders : Finset Slot → ℕ) (profileBound : ℕ → ℝ) (a e Z d : ℝ)
    (labels : Finset α) (w : α → NonzeroElement) (fiber : (v : α) → Finset (β v))
    (DL DR : (v : α) → β v → SurvivingBufferedData η (w v) Slot orders profileBound a e)
    (weight : (v : α) → β v → ℝ) (B E : ℝ) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (gate : (v : α) → SurvivingBufferedData η (w v) Slot orders profileBound a e →
      SurvivingBufferedData η (w v) Slot orders profileBound a e → Prop)
    (hweight : ∀ v ∈ labels, ∀ b ∈ fiber v, 0 ≤ weight v b)
    (hmass : ∀ v ∈ labels, (∑ b ∈ fiber v, weight v b) ≤ B)
    (hgate : ∀ v ∈ labels, ∀ b ∈ fiber v, gate v (DL v b) (DR v b))
    (hmain : ∀ (S : Finset α), S ⊆ labels →
      ∀ FL FR : (v : α) → SurvivingBufferedData η (w v) Slot orders profileBound a e,
      (∀ v ∈ S, gate v (FL v) (FR v)) →
      (∑ v ∈ S, ‖(FL v).value M H η₀ V Bprofile Z d‖ *
        ‖(FR v).value M H η₀ V Bprofile Z d‖) ≤ E) :
    (∑ v ∈ labels, ∑ b ∈ fiber v, weight v b*
      (‖(DL v b).value M H η₀ V Bprofile Z d‖ *
        ‖(DR v b).value M H η₀ V Bprofile Z d‖)) ≤ B*E := by
  apply joint_weighted_fibers labels fiber weight
    (fun v b => ‖(DL v b).value M H η₀ V Bprofile Z d‖ *
      ‖(DR v b).value M H η₀ V Bprofile Z d‖) B E hB hweight
    (fun _ _ _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hmass
  intro S hS pick hpick
  by_cases hne : S.Nonempty
  · obtain ⟨v₀,hv₀⟩ := hne
    let left₀ := DL v₀ (pick ⟨v₀,hv₀⟩)
    let right₀ := DR v₀ (pick ⟨v₀,hv₀⟩)
    let FL : (v : α) → SurvivingBufferedData η (w v) Slot orders profileBound a e :=
      fun v => if hv : v ∈ S then DL v (pick ⟨v,hv⟩) else left₀.rebase (w v)
    let FR : (v : α) → SurvivingBufferedData η (w v) Slot orders profileBound a e :=
      fun v => if hv : v ∈ S then DR v (pick ⟨v,hv⟩) else right₀.rebase (w v)
    have hFL (v : S) : FL v = DL v (pick v) := by dsimp only [FL]; rw [dif_pos v.property]
    have hFR (v : S) : FR v = DR v (pick v) := by dsimp only [FR]; rw [dif_pos v.property]
    have hb := hmain S hS FL FR (fun v hv => by
      rw [hFL ⟨v,hv⟩,hFR ⟨v,hv⟩]
      exact hgate v (hS hv) (pick ⟨v,hv⟩) (hpick ⟨v,hv⟩))
    rw [← Finset.sum_coe_sort S (fun v =>
      ‖(FL v).value M H η₀ V Bprofile Z d‖ * ‖(FR v).value M H η₀ V Bprofile Z d‖)] at hb
    simpa only [hFL,hFR] using hb
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst S
    simpa using hE

#print axioms joint_buffered_product_fibers
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointBufferedFibers -/

/- BEGIN ORIGINAL MODULE Analytic.JointBufferedReindex ; sha256 f7c8f7e2a409291fb961b33b294bc43ce14387ab99d88786596baf46c9b936d8 -/
section


/-! Surviving slots are embedded back into the original fixed slot type.
Reindexing preserves the literal product and its total logarithmic length. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification
local notation "O" => HeckeFamily.O

namespace JointBufferedProductData
variable {η : Character} {w : NonzeroElement} {ι κ : Type*}
  {n : ℕ} {profileBound : ℕ → ℝ} {a e : ℝ}

def reindex (D : JointBufferedProductData η w ι n profileBound a e) (f : κ ≃ ι) :
    JointBufferedProductData η w κ n profileBound a e :=
  { D with r := fun j => D.r (f j), σ := fun j => D.σ (f j), v := fun j => D.v (f j) }

variable [Fintype ι] [Fintype κ]

theorem reindex_length (D : JointBufferedProductData η w ι n profileBound a e) (f : κ ≃ ι) :
    (D.reindex f).length = D.length := by
  unfold length reindex
  congr 1
  exact Fintype.sum_equiv f _ _ (fun _ => rfl)

theorem reindex_value (D : JointBufferedProductData η w ι n profileBound a e) (f : κ ≃ ι)
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (η₀ : ι → Character) (V : ι → ℝ → ℂ) (B : ι → ℝ) (Z d : ℝ) :
    (D.reindex f).value M H (fun j => η₀ (f j)) (fun j => V (f j)) (fun j => B (f j)) Z d =
      D.value M H η₀ V B Z d := by
  unfold value reindex
  congr 1
  exact Fintype.prod_equiv f _ _ (fun _ => rfl)

theorem reindex_admissible (D : JointBufferedProductData η w ι n profileBound a e)
    (f : κ ≃ ι) (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (η₀ : ι → Character)
    (A B : ι → ℝ) (Rwidth τ ηaux σmin σmax Z d T : ℝ)
    (hD : D.Admissible M H hH η₀ A B Rwidth τ ηaux σmin σmax Z d T) :
    (D.reindex f).Admissible M H hH (fun j => η₀ (f j))
      (fun j => A (f j)) (fun j => B (f j)) Rwidth τ ηaux σmin σmax Z d T := by
  refine ⟨hD.r₁_nonneg,hD.r₁_le,hD.r₂_nonneg,hD.r₂_le,
    fun j => hD.slots (f j),?_,hD.freq₁,hD.freq₂,
    fun j => hD.freq_slots (f j),hD.height_four,hD.height_two,
    fun j => hD.log_scale (f j),hD.buffer_height⟩
  rintro (_ | ⟨j,θ⟩)
  · exact hD.conductor none
  · exact hD.conductor (some (f j,θ))

end JointBufferedProductData

def embeddedSlots {ι Slot : Type*} [Fintype ι] (f : ι ↪ Slot) : Finset Slot :=
  Finset.univ.map f

def embeddedSlotsEquiv {ι Slot : Type*} [Fintype ι] (f : ι ↪ Slot) : ι ≃ embeddedSlots f :=
  Equiv.ofBijective (fun i => ⟨f i, Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩) (by
    constructor
    · intro i j h
      exact f.injective (congrArg Subtype.val h)
    · rintro ⟨j,hj⟩
      obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hj
      exact ⟨i,rfl⟩)

@[simp] theorem embeddedSlotsEquiv_val {ι Slot : Type*} [Fintype ι] (f : ι ↪ Slot) (i : ι) :
    (embeddedSlotsEquiv f i).val = f i := rfl

@[simp] theorem embeddedSlotsEquiv_symm_val {ι Slot : Type*} [Fintype ι]
    (f : ι ↪ Slot) (j : embeddedSlots f) : f ((embeddedSlotsEquiv f).symm j) = j.val := by
  exact congrArg Subtype.val ((embeddedSlotsEquiv f).apply_symm_apply j)

def embeddedBufferedData {η : Character} {w : NonzeroElement} {ι Slot : Type*}
    [Fintype ι] [Fintype Slot] [DecidableEq Slot]
    (f : ι ↪ Slot) (orders : Finset Slot → ℕ) (profileBound : ℕ → ℝ) (a e : ℝ)
    (D : JointBufferedProductData η w ι (orders (embeddedSlots f)) profileBound a e) :
    SurvivingBufferedData η w Slot orders profileBound a e where
  slots := embeddedSlots f
  data := D.reindex (embeddedSlotsEquiv f).symm

theorem embeddedBufferedData_length {η : Character} {w : NonzeroElement} {ι Slot : Type*}
    [Fintype ι] [Fintype Slot] [DecidableEq Slot]
    (f : ι ↪ Slot) (orders : Finset Slot → ℕ) (profileBound : ℕ → ℝ) (a e : ℝ)
    (D : JointBufferedProductData η w ι (orders (embeddedSlots f)) profileBound a e) :
    (embeddedBufferedData f orders profileBound a e D).length = D.length :=
  D.reindex_length _

theorem embeddedBufferedData_value {η : Character} {w : NonzeroElement} {ι Slot : Type*}
    [Fintype ι] [Fintype Slot] [DecidableEq Slot]
    (f : ι ↪ Slot) (orders : Finset Slot → ℕ) (profileBound : ℕ → ℝ) (a e : ℝ)
    (D : JointBufferedProductData η w ι (orders (embeddedSlots f)) profileBound a e)
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (η₀ : Slot → Character) (V : Slot → ℝ → ℂ) (B : Slot → ℝ) (Z d : ℝ) :
    (embeddedBufferedData f orders profileBound a e D).value M H η₀ V B Z d =
      D.value M H (fun i => η₀ (f i)) (fun i => V (f i)) (fun i => B (f i)) Z d := by
  unfold embeddedBufferedData SurvivingBufferedData.value
    JointBufferedProductData.value JointBufferedProductData.reindex
  congr 1
  apply Fintype.prod_equiv (embeddedSlotsEquiv f).symm
  intro j
  simp only [embeddedSlotsEquiv_symm_val]

theorem embeddedBufferedData_admissible {η : Character} {w : NonzeroElement} {ι Slot : Type*}
    [Fintype ι] [Fintype Slot] [DecidableEq Slot]
    (f : ι ↪ Slot) (orders : Finset Slot → ℕ) (profileBound : ℕ → ℝ) (a e : ℝ)
    (D : JointBufferedProductData η w ι (orders (embeddedSlots f)) profileBound a e)
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (η₀ : Slot → Character)
    (A B : Slot → ℝ) (Rwidth τ ηaux σmin σmax Z d T : ℝ)
    (hD : D.Admissible M H hH (fun j => η₀ (f j))
      (fun j => A (f j)) (fun j => B (f j)) Rwidth τ ηaux σmin σmax Z d T) :
    (embeddedBufferedData f orders profileBound a e D).Admissible M H hH η₀ A B
      Rwidth τ ηaux σmin σmax Z d T := by
  have h := D.reindex_admissible (embeddedSlotsEquiv f).symm M H hH
    (fun j => η₀ (f j)) (fun j => A (f j)) (fun j => B (f j))
    Rwidth τ ηaux σmin σmax Z d T hD
  simpa only [SurvivingBufferedData.Admissible, embeddedBufferedData,
    embeddedSlotsEquiv_symm_val] using h

/-- Both allocation stages use the original slot by this injective map. -/
def nestedSlotEmbedding {Slot : Type*} (J : Finset Slot) (K : Finset J) : K ↪ Slot where
  toFun i := i.val.val
  inj' := fun i j h => Subtype.ext (Subtype.ext h)

#print axioms embeddedBufferedData_value
#print axioms embeddedBufferedData_length
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointBufferedReindex -/

/- BEGIN ORIGINAL MODULE Analytic.JointBufferedShortSlots ; sha256 422015551b6fd9f39666761f6af9a133cbfd240fe0bdc89cb20cec6cf676aa90 -/
section



/-! Bounded prime scales are removed before the high product estimate.
The original profiles are constructed at the order of the final subset,
so removing slots does not require a false monotonicity of Mellin bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification HeckePrimeAnnular
open HeckeDyadic CenteredMomentHeckeHeight
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentWholeSlotDeletion ConcretePrimeRowBridge
open CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

namespace SurvivingBufferedData
variable {η : Character} {w : NonzeroElement} {Slot : Type*}
  [Fintype Slot] [DecidableEq Slot]
  {orders : Finset Slot → ℕ} {profileBound : ℕ → ℝ} {a e : ℝ}

def restrictSlots (T : Finset Slot)
    (D : SurvivingBufferedData η w Slot (fun S => orders (S ∩ T)) profileBound a e) :
    SurvivingBufferedData η w Slot orders profileBound a e where
  slots := D.slots ∩ T
  data := { D.data with
    r := fun j => D.data.r ⟨j.val,(Finset.mem_inter.mp j.property).1⟩
    σ := fun j => D.data.σ ⟨j.val,(Finset.mem_inter.mp j.property).1⟩
    v := fun j => D.data.v ⟨j.val,(Finset.mem_inter.mp j.property).1⟩ }

theorem restrictSlots_length_le (T : Finset Slot)
    (D : SurvivingBufferedData η w Slot (fun S => orders (S ∩ T)) profileBound a e)
    (hr : ∀ j, 0 ≤ D.data.r j) :
    (D.restrictSlots T).length ≤ D.length := by
  let r : Slot → ℝ := fun j => if hj : j ∈ D.slots then D.data.r ⟨j,hj⟩ else 0
  have hsum (S : Finset Slot) (hS : S ⊆ D.slots) :
      (∑ j : S, D.data.r ⟨j.val,hS j.property⟩) = ∑ j ∈ S,r j := by
    rw [← Finset.sum_coe_sort S r]
    apply Finset.sum_congr rfl
    intro j _
    simp only [r,dif_pos (hS j.property)]
  dsimp only [length,restrictSlots,JointBufferedProductData.length]
  rw [hsum (D.slots ∩ T) Finset.inter_subset_left,hsum D.slots (fun _ h => h)]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left
  intro j hj _
  simpa only [r,dif_pos hj] using hr ⟨j,hj⟩

/-- Every admissibility field except the logarithmic lower cap. -/
structure ShortSlotGates (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (η₀ : Slot → Character)
    (Rwidth τ ηaux σmin σmax Z d T : ℝ)
    {orders' : Finset Slot → ℕ}
    (D : SurvivingBufferedData η w Slot orders' profileBound a e) : Prop where
  r₁_nonneg : 0 ≤ D.data.r₁
  r₁_le : D.data.r₁ ≤ Rwidth
  r₂_nonneg : 0 ≤ D.data.r₂
  r₂_le : D.data.r₂ ≤ Rwidth
  slots : ∀ j, 0 ≤ D.data.r j ∧ D.data.r j ≤ Rwidth ∧
    σmin ≤ D.data.σ j ∧ D.data.σ j ≤ σmax
  conductor : ∀ label, (bufferedProductFamily M H hH (fun j : D.slots => η₀ j.val)
    (excluded D.data.natural.character D.data.puncture) label).modulus.absNorm ≤ Z^d
  freq₁ : |D.data.plain₁.freq|+Z^τ/2 ≤ (3*D.data.bin+2 : ℕ)*Z^τ
  freq₂ : |D.data.plain₂.freq|+Z^τ/2 ≤ (3*D.data.bin+2 : ℕ)*Z^τ
  freq_slots : ∀ j, |D.data.t+D.data.v j|+Z^τ/2 ≤ (3*D.data.bin+2 : ℕ)*Z^τ
  height_four : (3+(3*D.data.bin+2 : ℕ)*Z^τ)^4 ≤ (Z^d)^ηaux
  height_two : (3+(3*D.data.bin+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηaux
  buffer_height : 3*(D.data.bin+1 : ℕ)*Z^τ ≤ T

theorem restrict_large_admissible
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (η₀ : Slot → Character)
    (A B P : Slot → ℝ) (Rwidth τ ηaux σmin σmax Z d T : ℝ)
    (D : SurvivingBufferedData η w Slot
      (fun S => orders (S ∩ largePrimeSlots A B P)) profileBound a e)
    (hscale : ∀ j : D.slots, (Z^d)^(D.data.r j) = P j.val)
    (hD : D.ShortSlotGates M H hH η₀ Rwidth τ ηaux σmin σmax Z d T) :
    (D.restrictSlots (largePrimeSlots A B P)).Admissible M H hH η₀ A B
      Rwidth τ ηaux σmin σmax Z d T := by
  refine ⟨hD.r₁_nonneg,hD.r₁_le,hD.r₂_nonneg,hD.r₂_le,
    (fun j => hD.slots ⟨j.val,(Finset.mem_inter.mp j.property).1⟩),?_,
    hD.freq₁,hD.freq₂,
    (fun j => hD.freq_slots ⟨j.val,(Finset.mem_inter.mp j.property).1⟩),
    hD.height_four,hD.height_two,?_,hD.buffer_height⟩
  · rintro (_ | ⟨j,θ⟩)
    · exact hD.conductor none
    · exact hD.conductor (some (⟨j.val,(Finset.mem_inter.mp j.property).1⟩,θ))
  · intro j
    change _ ≤ Real.log ((Z^d)^(D.data.r ⟨j.val,(Finset.mem_inter.mp j.property).1⟩))
    rw [hscale]
    exact largePrimeSlots_log_scale A B P j.val (Finset.mem_inter.mp j.property).2

end SurvivingBufferedData

/-- One fixed constant handles all bounded slots, including width zero,
before rows, masks, profiles, heights, scales and allocation subsets vary. -/
theorem survivingBufferedData_remove_short {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (V : Slot → ℝ → ℂ) (A B : Slot → ℝ) (lo hi : ℝ)
    (hA : ∀ j, 0 < A j) (hVs : ∀ j, Function.support (V j) ⊆ Icc (A j) (B j))
    (hV : ∀ j, Continuous (V j)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (η : Character) (w : NonzeroElement)
      (orders : Finset Slot → ℕ) (profileBound : ℕ → ℝ) (a e : ℝ)
      (η₀ : Slot → Character) (P : Slot → ℝ) (Z d : ℝ)
      (D : SurvivingBufferedData η w Slot
        (fun S => orders (S ∩ largePrimeSlots A B P)) profileBound a e),
      (∀ j : D.slots, (Z^d)^(D.data.r j) = P j.val) →
      (∀ j ∈ D.slots, 1 ≤ P j) →
      (∀ j : D.slots, lo ≤ D.data.σ j ∧ D.data.σ j ≤ hi) →
      ‖D.value M H η₀ V B Z d‖ ≤
        C*‖(D.restrictSlots (largePrimeSlots A B P)).value M H η₀ V B Z d‖ := by
  obtain ⟨C,hC,hremove⟩ := normalized_prime_slots_remove_small M H V A B lo hi hA hVs hV
  refine ⟨C,hC,?_⟩
  intro η w orders profileBound a e η₀ P Z d D hscale hP hσ
  let σ : Slot → ℝ := fun j => if hj : j ∈ D.slots then D.data.σ ⟨j,hj⟩ else 0
  let v : Slot → ℝ := fun j => if hj : j ∈ D.slots then D.data.v ⟨j,hj⟩ else 0
  let x : Slot → ℂ := fun j => normalizedSlot D.data.parent.val
    (fixedBadMask*idealGenerator D.data.puncture) 1 w.val (primePool M H (B j) (P j))
    (fun I => idealCoeff (η₀ j).inverse I*annularWeight (V j) (P j) (σ j) (v j) I)
    D.data.t (P j)
  have hp := hremove D.slots D.data.parent.val (fun j => (η₀ j).inverse)
    (fixedBadMask*idealGenerator D.data.puncture) 1 w.val P σ v D.data.t hP
    (fun j hj => by simpa only [σ,dif_pos hj] using hσ ⟨j,hj⟩)
  change ‖∏ j ∈ D.slots,x j‖ ≤ C*‖∏ j ∈ D.slots ∩ largePrimeSlots A B P,x j‖ at hp
  have hprod (S : Finset Slot) (hS : S ⊆ D.slots) :
      (∏ j : S, normalizedSlot D.data.parent.val
        (fixedBadMask*idealGenerator D.data.puncture) 1 w.val
        (primePool M H (B j.val) ((Z^d)^(D.data.r ⟨j.val,hS j.property⟩)))
        (fun I => idealCoeff (η₀ j.val).inverse I * annularWeight (V j.val)
          ((Z^d)^(D.data.r ⟨j.val,hS j.property⟩))
          (D.data.σ ⟨j.val,hS j.property⟩) (D.data.v ⟨j.val,hS j.property⟩) I)
        D.data.t ((Z^d)^(D.data.r ⟨j.val,hS j.property⟩))) = ∏ j ∈ S,x j := by
    rw [← Finset.prod_coe_sort S x]
    apply Finset.prod_congr rfl
    intro j _
    simp only [x,σ,v,dif_pos (hS j.property),hscale]
  unfold SurvivingBufferedData.value JointBufferedProductData.value
    SurvivingBufferedData.restrictSlots
  rw [hprod D.slots (fun _ h => h),hprod (D.slots ∩ largePrimeSlots A B P) Finset.inter_subset_left]
  simp only [norm_mul]
  have hb := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (norm_nonneg ((Real.sqrt ((Z^d)^D.data.r₁) : ℂ)⁻¹ *
      rowTwistedSum D.data.parent.val (fixedBadMask*idealGenerator D.data.puncture) 1 w.val
        (twistProfile D.data.plain₁.W D.data.plain₁.σ D.data.plain₁.freq) 0 ((Z^d)^D.data.r₁)))
      (norm_nonneg ((Real.sqrt ((Z^d)^D.data.r₂) : ℂ)⁻¹ *
      rowTwistedSum D.data.parent.val (fixedBadMask*idealGenerator D.data.puncture) 1 w.val
        (twistProfile D.data.plain₂.W D.data.plain₂.σ D.data.plain₂.freq) 0 ((Z^d)^D.data.r₂))))
  simpa only [norm_mul,mul_assoc,mul_left_comm,mul_comm] using hb

#print axioms survivingBufferedData_remove_short
#print axioms SurvivingBufferedData.restrictSlots_length_le
#print axioms SurvivingBufferedData.restrict_large_admissible
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointBufferedShortSlots -/
