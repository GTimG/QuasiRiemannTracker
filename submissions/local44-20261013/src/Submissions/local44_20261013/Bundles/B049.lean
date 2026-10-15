/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B010
import Submissions.local44_20261013.Bundles.B030
import Submissions.local44_20261013.Bundles.B033
import Submissions.local44_20261013.Bundles.B037
import Submissions.local44_20261013.Bundles.B038
import Submissions.local44_20261013.Bundles.B042
import Submissions.local44_20261013.Bundles.B045
import Submissions.local44_20261013.Bundles.B046
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.CentralExponent
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FiniteProductX
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalResidueActual
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorGlobalIntegral
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.LargeSaving
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorArithmetic
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowSector

/- BEGIN ORIGINAL MODULE Global.Low.Reflection.LowSector ; sha256 952cbfeb6af112251d0c72864197fbf3309c52e282081194e0730d5d17c341b2 -/
section



/-! Adapted from OpenAI/math family003, pinned original module Reflection.LowSector.
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

theorem original_low_sector_literal_energy
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0< lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0< C ∧ 1< Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z O₀ H za Nstar d ell0 shift δ π Ck CO CH X QK QP Lscale Lrow Lslot : ℝ)
      (i : ℕ×ℕ×ℕ),
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
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤ Z^Lscale →
      i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ) →
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
    ∀ (u : Eisˣ) (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤ QK → 2≤ QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤ QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤ QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖literalDyadicRow G K.val (hrows K.val K.property) S j Pset
        (E.completion K) s hc₀ u i W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(((1-Submission20261012.Global.ell)-d)+200*η+π-O₀/2) := by
  obtain ⟨degree,C₀,Cs,Zs,hC₀,hCs,hZs,henergy⟩ := sector_normalized_literal_energy
    (N:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ η hηpos
  obtain ⟨Zb,Cb,hZb,hCb,hbranch⟩ := original_surviving_low_energy_sum s hc₀ ρ hρ 1 (1/2) η
    (by norm_num) (by norm_num) hηpos
  let Kc := (Real.exp (Real.log 2/2+Real.log 2))^2*(6*Cs)
  have hKc : 0< Kc := by dsimp [Kc];positivity
  refine ⟨degree*2,Kc*Cb*C₀^2+1,max Zs Zb,by positivity,lt_of_lt_of_le hZs (le_max_left _ _),?_⟩
  intro σ _ J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift δ π Ck CO CH X QK QP Lscale Lrow Lslot i
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ hδη hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hret rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar u θ r aw hqk hqp hKr hPr hr haw
  have hzpos : 0< Z := lt_trans zero_lt_one (lt_of_lt_of_le hZs ((le_max_left _ _).trans hZ))
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  have hpair := (poolPrimeFamily J Q Q₀).restrict_pairwise (poolPrimeFamily_pairwise J Q Q₀) A
  have hj : ∀ b : A,j b<6 := by intro b;exact Nat.mod_lt _ (by norm_num)
  have hs := henergy Z ((le_max_left _ _).trans hZ) G j hNlevel hbase hac hpair hGN hGchar hj
    rows Pset S hrows E hrowcop hprod hScop hSN hSchar u i X θ QK QP r aw hX hqk hqp hKr hPr hr haw
  have hb := hbranch J I F Q Q₀ hJ hI hQ hpower hmask A (actualCuspColumn E.referenceArithmetic s hc₀ u i.1)
    Z O₀ H za Nstar d ell0 shift δ π Ck CO CH X QK QP ε Lscale Lrow Lslot i
    ((le_max_right _ _).trans hZ) hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift hNs
    (by simpa only [one_mul] using heH) (by simpa only [one_div,mul_comm,mul_inv_rev,div_eq_mul_inv,one_mul] using heza)
    heN hδ hδη hε.le
    (by simpa only [one_mul] using hrowcap) (by simpa only [one_div,mul_comm,mul_inv_rev,div_eq_mul_inv,one_mul] using hslotcap)
    hconst hbudget hscap hret
  dsimp only at hs hb
  rw [←heH,←heza,←heN] at hs
  simp_rw [←Finset.mul_sum] at hs
  apply hs.trans
  calc
    _ = Kc*((survivingFrozenBranches G j (actualCuspColumn E.referenceArithmetic s hc₀ u i.1)
        (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)).card*
      ∑ e∈survivingFrozenBranches G j (actualCuspColumn E.referenceArithmetic s hc₀ u i.1)
        (reflectedNDyad i.2.2) (reflectedBDyad i.2.1),
        Z^(InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
          (normWidth Z (frozenExtracted G j e 2)) za
          (Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1)))
          (Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2)))
          (ramifiedWidth Z i.1) (terminalDualWidth Z H za Nstar G.ideal j e)+
          ε*(H+Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1))+
            Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2))+za)+η/2))*(C₀*(1+‖θ‖)^degree)^2 := by dsimp [Kc,G,j];ring
    _ ≤ Kc*(Cb*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(((1-Submission20261012.Global.ell)-d)+200*η+π-O₀/2))*(C₀*(1+‖θ‖)^degree)^2 := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hKc.le) (sq_nonneg _)
    _ = (Kc*Cb*C₀^2)*(1+‖θ‖)^(degree*2)*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(((1-Submission20261012.Global.ell)-d)+200*η+π-O₀/2) := by rw [mul_pow,←pow_mul];ring
    _ ≤ _ := by gcongr;linarith
end
end LowReflection

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Reflection.LowSector -/

/- BEGIN ORIGINAL MODULE Global.Transport.CubeFloorGlobalIntegral ; sha256 799a2baadb56a102aea4491831ec4afb379cbe80040d7b081ee304cead36f667 -/
section
/- Adapted from weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/






open OAI OAI.SevenEighths

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace Submission20261012.Global.HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

omit [NeZero M] in
private theorem globalFloorIntegralPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem actual_global_floor_cube_norm (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0 < e) (he1 : e<1/1000) (heps : 0 < eps) (hc : 0 < c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0 < dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0 < rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0 < mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε < rmin*mesh) (hmargin : 0 < margin)
    (hheight : 2*τ < dmin*cost) (hloss : τ*(2+4*eps) < loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤ A)
    (hellsum : ∑j,ell j=Submission20261012.Global.ell)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0 < C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v : ℝ),0≤ v → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,rowNorm u≤ Z^v) →
      ∀i : ℕ,i≤ n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<51/100+2*e) →
      let Yp : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Yp j)
      ‖finiteCentralCubeRows S hS hmax η rows T (globalFloorIntegralPoolOutside M H S N c b Yp) W Yp
        W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z e (fun _=>51/100) (fun _=>(3*i+1:ℕ)*Z^τ)‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(Submission20261012.Global.Transport.floorSourceExponent v+
            Submission20261012.Global.Transport.floorRealLoss N v e eps loss mesh) := by
  obtain ⟨Ca,hCa,hbound⟩ := actual_global_floor_cube_arithmetic M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
  obtain ⟨Cp,hCp,hprofile⟩ := actual_common_cube_aggregate_norm W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨Cp*Ca,mul_pos hCp hCa,?_⟩
  intro η
  filter_upwards [hbound η,source_cube_height_eventually τ hτ] with Z hb hZ
  intro d hd hd' v hv rows hrows hnorm i hi hbin
  dsimp only
  have hZp : 0 < Z := zero_lt_one.trans_le hZ.1
  let Yp : Fin N→ℝ := fun j=> Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Yp j)
  have hheight : (3*i+1:ℕ)*Z^τ≤(3*i+2:ℕ)*Z^τ := by
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZp.le _)
    exact_mod_cast (show 3*i+1≤3*i+2 by omega)
  let mass : ℝ := Ca*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(v*(67/100+12*e+eps*(N+8))+loss-(3*Submission20261012.Global.ell/20)+mesh*Submission20261012.Global.ell)
  have hp := hprofile e (51/100) (Z^τ) ((3*i+1:ℕ)*Z^τ) i he he1 le_rfl (by norm_num)
    hZ.2 hheight S hS hmax hfirst η rows (fun u hu=>(hrows u hu).1) T
    (globalFloorIntegralPoolOutside M H S N c b Yp) (rayCubeFamily M H hH) hbin W Yp
    (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z (by positivity) (by positivity) hZp mass (by dsimp [mass];positivity)
    (hb d hd hd' v hv rows hrows hnorm i hi hbin)
  apply hp.trans_eq
  rw [Submission20261012.Global.Transport.physical_scale_identity Z (51/100) e hZp]
  have hpowers : Z^(Submission20261012.Global.Transport.centralScale (51/100) e)*
      Z^(v*(67/100+12*e+eps*(N+8))+loss-(3*Submission20261012.Global.ell/20)+mesh*Submission20261012.Global.ell)=
      Z^(Submission20261012.Global.Transport.floorSourceExponent v+
        Submission20261012.Global.Transport.floorRealLoss N v e eps loss mesh) := by
    rw [←Real.rpow_add hZp]
    congr 1
    unfold Submission20261012.Global.Transport.floorSourceExponent Submission20261012.Global.Transport.floorRealLoss Submission20261012.Global.Transport.centralScale
    ring
  dsimp [mass]
  calc
    _ = (Cp*Ca)*(η.modulus.absNorm:ℝ)^(2*eps)*(Z^(Submission20261012.Global.Transport.centralScale (51/100) e)*
      Z^(v*(67/100+12*e+eps*(N+8))+loss-(3*Submission20261012.Global.ell/20)+mesh*Submission20261012.Global.ell)) := by ring
    _ = _ := by rw [hpowers]

end Submission20261012.Global.HighRowFamily

end


end
/- END ORIGINAL MODULE Global.Transport.CubeFloorGlobalIntegral -/

/- BEGIN ORIGINAL MODULE Global.Transport.LargeSaving ; sha256 777e9e10b994800dc7499c0a85a3ac455ff72d6e79848944f9d03b9a0104dfe4 -/
section
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/



open OAI OAI.SevenEighths

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace Submission20261012.Global.HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem large_physical_tail_arbitrary_saving (K : ℕ) (δ a b B ζ saving : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hζ : 0<ζ)
    (ha : 0 < a) (hb : 0 < b) (hB : 0≤ B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃r C : ℝ,(17/50:ℝ)≤ r ∧ 0 < C ∧ ∀(η : Character) (Z : ℝ),1≤ Z → ∀R : ℕ→Finset FreeRow,
      (∀n u,u∈R n → u.val≠1 ∧ Z^((Submission20261012.Global.h:ℝ)+ζ)*(2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(Z^((Submission20261012.Global.h:ℝ)+ζ)*(2:ℝ)^n)) →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤ length i) → (∑i,length i)=(Submission20261012.Global.ell:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤ B) →
      Summable (fun n=> absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=> Z^(length i)) W0 W1
        (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z 2 2 r) ∧
      (∑'n,absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=> Z^(length i)) W0 W1
        (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z 2 2 r)
      ≤ C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving) := by
  obtain ⟨r,hr,hr',hpower⟩ := exists_large_tail_line ζ δ saving hζ
  obtain ⟨C,hC,hmain⟩ := large_physical_dyads_summable K δ a b B r ζ hδ hδ' hr hr' hζ ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨r,C,hr,hC,?_⟩
  intro η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  obtain ⟨hs,hb⟩ := hmain η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  refine ⟨hs,hb.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hpower) (by positivity)

end Submission20261012.Global.HighRowFamily
end


end
/- END ORIGINAL MODULE Global.Transport.LargeSaving -/

/- BEGIN ORIGINAL MODULE Global.Transport.NonfloorArithmetic ; sha256 78f8debace2d11e37cf4e1215993c6eb212a14386a48f33994935eb30d94a298 -/
section
/- Adapted from weighted upstream PR6; original proof structure retained. -/




open OAI OAI.SevenEighths

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace Submission20261012.Global.HighRowFamily
open ProbeFinalAssembly
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem actual_nonfloor_cube_arithmetic (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0 < e) (he1 : e<1/1000) (heps : 0 < eps) (hc : 0 < c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0 < dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0 < rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0 < mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε < rmin*mesh) (hmargin : 0 < margin)
    (hheight : 2*τ < dmin*cost) (hloss : τ*(2+4*eps) < loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤ A)
    (hellsum : ∑j,ell j=Submission20261012.Global.ell)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ < dmin/2) (hτheight : 4*τ < dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hν : 0<ν)
    (hlog : 0 < logCost) (hMomentHeight : τ < heightCost)
    (μ : ℝ)
    (hfinal : (159*ε+εm+R+7*ν)+(12*e+eps*(N+8))+
      (logCost+heightCost+momentCost+loss+mesh*Submission20261012.Global.ell+(16-6*Submission20261012.Global.ly)*e)+μ≤1/4000) (counts : CountParameters M H εm) :
    ∃C : ℝ,0 < C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v a C0 : ℝ),0≤ v → v≤ d → d-v≤μ →
      51/100 < a → a≤7/8 → Submission20261012.Global.Transport.OriginalBranch d a → 0≤ C0 → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,Z^v≤ rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤ n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ) < a+2*e) →
      (∀u∈rows,a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^τ)) →
      let Y : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      SourceMomentsAt M H hH S hS.prime η rows ell W Z d a ε τ dmax b R mesh i
        ((17/50:ℂ)+t.1.2*Complex.I) 0
        (if 2*a-1≤5/6 then counts.cB else counts.cH) (if 2*a-1≤5/6 then counts.kB else counts.kH)
        (C0*Z^momentCost) (Z^heightCost) εm →
      ‖cubeArithmeticSum S hS hmax η rows T (nonfloorPoolOutside M H S N c b Y) W Y a e t‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(Submission20261012.Global.signal Submission20261012.Global.theta-1/4000-Submission20261012.Global.Transport.centralScale a e) := by
  obtain ⟨C,hC,hclass⟩ :=
    actual_nonfloor_class_from_raw_moments M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm 0 ν logCost heightCost momentCost hεm (by norm_num) (by norm_num) hν hlog hMomentHeight counts
  let cardCost : ℝ := (HeckeDetectorClassBudget.alphabetBound mesh:ℝ)^N
  have hcardCost : 0≤ cardCost := by dsimp [cardCost];positivity
  refine ⟨(cardCost+1)*C,by positivity,?_⟩
  intro η
  filter_upwards [hclass η,eventually_gt_atTop (1:ℝ)] with Z hclass hZ
  intro d hd hd' v a C0 hv hv' hdv ha ha' hbranch hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only
  intro t ht hmom
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let Y : Fin N→ℝ := fun j=> Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
  let Q := physical M H (fun u : FreeRow=> u.val) W (fun _=> b) (fun j=> ell j/d) (fun _=> z) (Z^d)
  let bound : ℝ := C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
    Z^(Submission20261012.Global.signal Submission20261012.Global.theta-1/4000-Submission20261012.Global.Transport.centralScale a e)
  have hb : 0≤ bound := by dsimp [bound];positivity
  have hpart := cubeArithmeticSum_class_uniform S hS hmax η rows T
    (nonfloorPoolOutside M H S N c b Y) W Y a e t Finset.univ (Z^d) ((2*a-1)/2) mesh hmesh
    (by linarith) (fun j=> ell j/d) Q bound hb (by
      intro bin hne
      have hp := hclass d hd hd' v a C0 hv ha (by linarith) hC0 rows hrows hnorm i hi hnext hcurrent t ht hmom bin hne
      dsimp only at hp
      let q := classMean Finset.univ ((2*a-1)/2) mesh (fun j=> ell j/d) bin
      have hs := Submission20261012.Global.Transport.actual_central_class_saving N
        (hdmin.le.trans hd) hv hv' hdv ha ha' hp.1 hp.2.1 hbranch
        hε.le hεm.le hR hν.le he.le heps.le hfinal
      apply hp.2.2.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      linarith)
  simp only [Finset.card_univ,Fintype.card_fin] at hpart
  calc
    _ ≤ cardCost*bound := hpart
    _ ≤ (cardCost+1)*bound := mul_le_mul_of_nonneg_right (by linarith) hb
    _ = _ := by dsimp [bound];ring

end Submission20261012.Global.HighRowFamily

end


end
/- END ORIGINAL MODULE Global.Transport.NonfloorArithmetic -/

/- BEGIN ORIGINAL MODULE Global.Transport.PrincipalRemainderFiniteProductX ; sha256 a338f07df83df4ae7010c6f949ececa2ec7ba8ba77d2227b93b92fc2f8a27ff1 -/
section
/- Adapted from Submission20261012.Global.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/



noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory
namespace Submission20261012.Global.Transport.PrincipalFiniteProductX
open OAI OAI.SevenEighths OAI.SevenEighths.ProbeFiniteProductX
open ActualEisensteinCubic CompletedGauss ProbePhysical ProbeEuler ProbeLocal
open HeckeFamily PrincipalMellinResidues ProbeFiniteProductBounds
open Submission20261012.Global.Transport.PrincipalFiniteProduct
local notation "Id" => Ideal ActualEisensteinCubic.O

lemma marked_differentiableAt_x (η : Character) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : theta ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun x => idealMarkedClosed η P x w z) x := by
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith [Submission20261012.Global.Transport.theta_bounds]
  have hd := remainder_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hr := coordR_differentiable (Ideal.absNorm P.val) hQ0
    (actualAPhase η (primaryGenerator P.val)) z
  have hd' := coordD_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) 1
  have hk := coordK_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) w
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

theorem local_analytic_x (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => localMultiplier η P x w z) {x : ℂ | theta < x.re} := by
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith [Submission20261012.Global.Transport.theta_bounds]
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hc := remainder_unramifiedClosed_analytic_x (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 w z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hz
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := remainder_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx.le hz
  have hm := marked_differentiableAt_x η P x w z hQ hx.le hz
  have hcc : DifferentiableAt ℂ (fun x => idealClosedCorrection η P x w z) x :=
    (hc x hx).differentiableAt
  have hh := correction_ne_zero η S hS P hP x w z hx.le hw hz
  have hd' := coordD_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) 1
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

theorem slot_analytic_x {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => slotMultiplier η J T b x w z) {x : ℂ | theta < x.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (local_analytic_x η S hS P (hT j hj P hp) w z hw hz)

theorem continued_source_analytic_x {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0< Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z x w z)
      {x : ℂ | max (theta : ℝ) HeckeZeroSupremum.beta < x.re} := by
  have hn : (Z:ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hx' : (theta : ℝ)< x.re := lt_of_le_of_lt (le_max_left _ _) hx
  have hβ : HeckeZeroSupremum.beta< x.re := lt_of_le_of_lt (le_max_right _ _) hx
  have hH := (remainder_globalClosedCorrection_analytic_x η S hS.tail w z hw hz x hx').differentiableAt
  have hB := (slot_analytic_x η S hS.tail J T b hT w z hw hz x hx').differentiableAt
  have hR := HeckeReciprocal.reciprocal_differentiableAt (η.excludePrimes S hS.prime) hβ
  apply DifferentiableAt.differentiableWithinAt
  unfold continuedSourceMultiplier
  fun_prop (disch := first | assumption | exact Or.inl hn)

theorem continued_source_eq_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ)
    (hx0 : x≠0) (hx1 : x≠1) :
    continuedSourceMultiplier η S hS J T b W0 W1 X Y Z x w z =
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) x
        (globalClosedCorrection η S x) (slotMultiplier η J T b x) w z := by
  simp only [continuedSourceMultiplier,sourceMultiplier,
    HeckeReciprocal.reciprocal_eq_inv _ hx0 hx1,div_eq_mul_inv]

theorem continued_source_differentiable_strip {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0< Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) {a c : ℝ}
    (ha : theta < a) (hβ : HeckeZeroSupremum.beta< a) :
    DifferentiableOn ℂ (fun x => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z x w z)
      {x : ℂ | a≤ x.re ∧ x.re≤ c} := by
  apply (continued_source_analytic_x η S hS J T b hT W0 W1 X Y Z hZ w z hw hz).differentiableOn.mono
  intro x hx
  exact lt_of_lt_of_le (max_lt ha hβ) hx.1

end Submission20261012.Global.Transport.PrincipalFiniteProductX
end

end
/- END ORIGINAL MODULE Global.Transport.PrincipalRemainderFiniteProductX -/

/- BEGIN ORIGINAL MODULE Global.Transport.PrincipalRemainderResidueActual ; sha256 04260b4a9c95afe0eac4a94a12d1add2d059f23993fc592cd72b1886da483950 -/
section
/- Adapted from Submission20261012.Global.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/




noncomputable section
open scoped Classical BigOperators
open Complex MeasureTheory
namespace Submission20261012.Global.Transport.PrincipalResidueActual
open OAI OAI.SevenEighths OAI.SevenEighths.ProbePrincipalResidueActual
open HeckeFamily PrincipalMellinResidues PrincipalSignalComparison
open ProbeFiniteProductBounds ProbeEuler ProbeLocal HeckeSignal ProbePhysical Continuation
open ActualEisensteinCubic CompletedGauss
open Submission20261012.Global.Transport.PrincipalFiniteProduct Submission20261012.Global.Transport.PrincipalSignal


theorem actual_window_residue {κ : Type*} (η : Character) (S : Finset κ)
    (T : κ → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (W : κ → ℝ → ℝ) (scale : κ → ℝ) (s : ℂ) :
    windowMultiplier η S T (fun j t => (W j t : ℂ)) scale s 1 (1/6) =
      slotProduct S T (residueWeights W scale) (fun _ p => Ideal.absNorm p.val)
        (fun _ p => actualAPhase η (primaryGenerator p.val))
        (fun _ p => idealCoeff η p.val) s := by
  exact Submission20261012.Global.Transport.PrincipalFiniteProduct.window_at_residue η S T W scale s

theorem normalized_actual_window_residue {κ : Type*}
    (E : Finset (Ideal HeckeFamily.O)) (hE : SourceExclusions E) (η : Character)
    {a : ℝ} (ha : theta < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta< a) (S : Finset κ) :
    letI : NeZero (∏p∈E,p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    ∃D : ℝ, 0 ≤ D ∧ ∀ (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ),
      0< a0 → 0< a1 → Function.support W0⊆Set.Icc a0 b0 →
      Function.support W1⊆Set.Icc a1 b1 →
      (∀y,(W0 y).im=0) → (∀y,(W1 y).im=0) →
      (∀y,0 ≤ (W0 y).re) → (∀y,0 ≤ (W1 y).re) → W0≠0 → W1≠0 →
      ∀ (T : κ → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (W : κ → ℝ → ℝ) (scale : κ → ℝ) (P Y Z : ℝ),
      480 ≤ P → 1440*P^(-(theta  : ℝ)) ≤ 1 →
      (∀j∈S,∀p∈T j,0 ≤ W j ((Ideal.absNorm p.val : ℝ)/scale j)) →
      (∀j∈S,∀p∈T j,P ≤ (Ideal.absNorm p.val : ℝ)) →
      (∀j∈S,∀p∈T j,IsCoprime p.val η.modulus) →
      (∀j∈S,0< slotMass T (residueWeights W scale) j) → 1 ≤ Z →
      let B := windowMultiplier η S T (fun j t => (W j t : ℂ)) scale
      let normer := sourceResidueConstant W0 W1 (∏p∈E,p) *
        (Probe.principalScalar S Z ell (slotMass T (residueWeights W scale)) : ℂ)
      normer≠0 ∧
      Integrable (fun t : ℝ => fixedPrincipalResidue (∏p∈E,p)^2/6 *
        sourceMultiplier W0 W1 (Z^(lx : ℝ)) Y Z (η.excludePrimes E hE.prime)
          ((a : ℂ)+t*I) (globalClosedCorrection η E ((a : ℂ)+t*I))
          (B ((a : ℂ)+t*I)) 1 (1/6)) ∧
      ‖sourceResidueIntegral W0 W1 (∏p∈E,p) (η.excludePrimes E hE.prime)
          a (Z^(lx : ℝ)) Y Z (globalClosedCorrection η E) B / normer -
          HeckeSignal.signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (PrincipalSignal.signalShift) Z‖  ≤ 
        D*Z^(a+PrincipalSignal.signalShift)*P^(-(theta  : ℝ)) := by
  dsimp only
  let : NeZero (∏p∈E,p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
  obtain ⟨D,hD,hbound⟩ := Submission20261012.Global.Transport.PrincipalSignal.exists_normalized_actual_source_bound E hE η ha ha2 hβ S
  refine ⟨D,hD,?_⟩
  intro W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    T W scale P Y Z hP hsmall hW hnorm hcop hmass hZ
  refine hbound W0 W1 T (residueWeights W scale) P Y Z
    (windowMultiplier η S T (fun j t => (W j t : ℂ)) scale)
    hP hsmall ?_ hnorm hcop hmass hZ ?_ ?_
  · intro j hj p hp
    exact mul_nonneg (hW j hj p hp) (Real.rpow_nonneg (by positivity) _)
  · exact ProbePrincipalNormalizer.sourceResidueConstant_ne_zero (∏p∈E,p)
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
  · intro t
    exact actual_window_residue η S T W scale _

end Submission20261012.Global.Transport.PrincipalResidueActual
end

end
/- END ORIGINAL MODULE Global.Transport.PrincipalRemainderResidueActual -/
