import ZetaZeroFree.Analytic.Probe.Transport
import ZetaZeroFree.Analytic.Probe.Central
import ZetaZeroFree.Analytic.Rows.SourceCount

namespace ZetaZeroFree.Analytic.Probe
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeDetectorSupportedWitness HeckeDetectorProfiles
open HeckeDetectorInverseFiberCount HeckeDetectorDyadicProfiles HeckeInverseAmplification HeckeDetectorWitnessRows
open HeckeDetectorRowwisePolynomial HeckeDetectorCoefficientTransfer ProbeHighRowFamily
open ZetaZeroFree.Analytic.Rows
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local instance : Fintype (Sum Bool (RayQuotient.Characters M H)) := Fintype.ofFinite _
open ProbePhysical ProbeRaySlots

theorem actual_source_shell_power_from_plain
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀ P ∈ S, P.IsMaximal)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (dmin dmax δlo τ ε e κ heightCost margin εm : ℝ) (I : ℕ)
    (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) (hδlo : 0 < δlo) (hτ : 0 < τ)
    (hτzero : τ < dmin / 2) (hτheight : 4 * τ < dmin * heightCost)
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 1000) (he : 0 < e) (he' : e < 1 / 1000)
    (hκ : 0 < κ) (hκ' : κ ≤ 1) (hheightCost : 0 ≤ heightCost)
    (hmargin : 0 < margin) (hεm : 0 < εm)
    (hbudget : 12 * e * ((22 : ℝ) + 2) + 8 * κ + 2 * heightCost ≤ ε / 2) :
    ∃ A : ℕ, ∀ η : Character, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
      ∀ d : ℝ, dmin ≤ d → d ≤ dmax → ∀ (v q physicalUpper a height Cs : ℝ)
        (rows : Finset FreeRow), 0<Z → q≤2 → rows ⊆ rowBand (Z ^ δlo) physicalUpper →
      (∀ u ∈ rows, (calibrationForSet S hmax).residueMonoid u.val ≠ 0) →
      (∀ u ∈ rows, rowNorm u ≤ Z ^ (d - margin)) →
      ∀ i : ℕ, i ≤ I → 51 / 100 < a → 2 * a - 1 ≤ 5 / 6 →
      (∀ u ∈ rows, detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3 * (i + 1 : ℕ) * Z ^ τ) < a + 2 * e) →
      (∀ u ∈ rows, a ≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3 * i : ℕ) * Z ^ τ)) →
      0 ≤ height → 0 ≤ Cs →
      2 * Real.pi * (Z ^ d) ^ (τ / (2 * dmax)) + (3 * i : ℕ) * Z ^ τ ≤ height →
      SourcePlainAt M H hH S hS.prime η rows (Z ^ d) ε height εm Cs →
      (∀u∈rows,Z^v≤rowNorm u ∧ rowNorm u≤2*Z^v) →
      (∑u∈rows,rowNorm u^q) ≤ 4 * (Fintype.card (Sum Bool (RayQuotient.Characters M H)) : ℝ) *
        (dyadicLength (Z ^ d) : ℝ) ^ 2 *
        max (C * (1 + height) ^ A) (192 * (1 + height) * Cs) *
          Z ^ (d*(Exponent.R0 (2 * a - 1) + 6 * ε + εm)+v*q) := by
  obtain ⟨A,hend⟩ := actual_source_count_from_plain M H hH S hS hmax φ hφ hφc hφp hφ0 hφne
    a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB dmin dmax δlo τ ε e κ heightCost margin εm I
    hdmin hdmax hδlo hτ hτzero hτheight hε hεsmall he he' hκ hκ' hheightCost hmargin hεm hbudget
  refine ⟨A,?_⟩
  intro η
  obtain ⟨C,hC,hcount⟩ := hend η
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount] with Z hc
  intro d hd hd' v q physicalUpper a height Cs rows hZ hq hrows hcal hrow i hi ha hδu hnext hcurrent
    hh hCs hf hplain hshell
  have hcard := hc d hd hd' physicalUpper a height Cs rows hrows hcal hrow i hi ha hδu hnext hcurrent
    hh hCs hf hplain
  rw [←Real.rpow_mul hZ.le] at hcard
  have hs := row_shell_sum hZ hq rows hshell hcard
  simpa only [mul_assoc] using hs

theorem actual_source_central_cube_from_plain (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A) 
    (ell : Fin N→ℝ) (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (hellsum : ∑j,ell j=(5/33:ℝ)) 
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) 
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) (hdRange : dmin≤dmax) (hεsmall : ε≤1/1000)
    (hκ1 : κ≤1) (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*cost)
    (hcountbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (hepsBudget : eps*(N+8)≤1) :
    ∃order : ℕ,∃D : ℝ,0<D ∧ ∀η : Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(v physicalUpper a height Cs : ℝ) (rows : Finset FreeRow),
      rows⊆rowBand (Z^δ) physicalUpper →
      (∀u∈rows,(calibrationForSet S hmax).residueMonoid u.val≠0) →
      (∀u∈rows,rowNorm u≤Z^(d-margin)) →
      (∀u∈rows,Z^v≤rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤n → 51/100<a → 2*a-1≤5/6 →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^τ)) →
      0≤height → 0≤Cs → 2*Real.pi*(Z^d)^(τ/(2*dmax))+(3*i:ℕ)*Z^τ≤height →
      SourcePlainAt M H hH S hS.prime η rows (Z^d) ε height εm Cs →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      (∀j l,j≠l → Disjoint (T j) (T l)) →
      ‖finiteCentralCubeRows S hS hmax η rows T (sourcePoolOutside M H S N c b Y) W Y W0 W1
        (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z e (fun _=>a) (fun _=>(3*i+1:ℕ)*Z^τ)‖≤
        D*(Fintype.card (Sum Bool (RayQuotient.Characters M H)):ℝ)*(dyadicLength (Z^d):ℝ)^2*
          max (C*(1+height)^order) (192*(1+height)*Cs)*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(((6/11)*a-197/330+(146/11)*e)+(5/33)*(-(4/25:ℝ)+(a-1/2)+mesh)+loss+
            d*(Exponent.R0 (2*a-1)+6*ε+εm)+v*(a-1/2+12*e+eps*(N+8)-17/50)) := by
  obtain ⟨D,hD,hcentral⟩ := actual_fixed_scale_central_integral M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax W hWs hW hWB ell hello hellhi hellsum W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨order,hcount⟩ := actual_source_shell_power_from_plain M H hH S hS hmax φ hφ hφc hφp hφ0 hφne
    a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB dmin dmax δ τ ε e κ cost margin εm n
    hdmin hdRange hδ hτ hτzero hτheight hε hεsmall he he1 hκ hκ1 hcost hmargin hεm hcountbudget
  refine ⟨order,4*D,by positivity,?_⟩
  intro η
  obtain ⟨C,hC,hcount⟩ := hcount η
  refine ⟨C,hC,?_⟩
  filter_upwards [hcentral η,hcount,eventually_gt_atTop (0:ℝ)] with Z hz hcZ hZ
  intro d hd hd' v physicalUpper a height Cs rows hrows hcal hrow hshell i hi ha hδu hnext hcurrent hh hCs hf hplain
  dsimp only
  intro hdis
  have ha1 : a≤1 := by linarith
  have hq : a-1/2+12*e+eps*(N+8)-17/50≤2 := by linarith
  have hw := hcZ d hd hd' v (a-1/2+12*e+eps*(N+8)-17/50) physicalUpper a height Cs rows
    hZ hq hrows hcal hrow i hi ha hδu hnext hcurrent hh hCs hf hplain hshell
  have hp := hz d hd hd' rows (by
    intro u hu
    have hb := mem_rowBand.mp (hrows hu)
    exact ⟨hb.1,hb.2.1,hcal u hu,hrow u hu⟩) a i hi ha.le ha1 (by
      intro u hu
      convert hnext u hu using 1
      exact congrArg (fun inst : Fintype (Sum Bool (RayQuotient.Characters M H)) =>
        @detectorMaximum (Sum Bool (RayQuotient.Characters M H)) inst
          (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(i+1:ℕ)*Z^τ))
        (Subsingleton.elim _ _)) hdis
  apply hp.trans
  calc
    _ ≤ D*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(((6/11)*a-197/330+(146/11)*e)+(5/33)*(-(4/25:ℝ)+(a-1/2)+mesh)+loss)*
          (4*(Fintype.card (Sum Bool (RayQuotient.Characters M H)):ℝ)*(dyadicLength (Z^d):ℝ)^2*
            max (C*(1+height)^order) (192*(1+height)*Cs)*
            Z^(d*(Exponent.R0 (2*a-1)+6*ε+εm)+v*(a-1/2+12*e+eps*(N+8)-17/50))) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ = _ := by
      have hz : Z^(((6/11)*a-197/330+(146/11)*e)+(5/33)*(-(4/25:ℝ)+(a-1/2)+mesh)+loss)*
          Z^(d*(Exponent.R0 (2*a-1)+6*ε+εm)+v*(a-1/2+12*e+eps*(N+8)-17/50))=
          Z^(((6/11)*a-197/330+(146/11)*e)+(5/33)*(-(4/25:ℝ)+(a-1/2)+mesh)+loss+
            d*(Exponent.R0 (2*a-1)+6*ε+εm)+v*(a-1/2+12*e+eps*(N+8)-17/50)) := by
        rw [←Real.rpow_add hZ]
        congr 1
        ring
      calc
        _ = (4*D*(Fintype.card (Sum Bool (RayQuotient.Characters M H)):ℝ)*(dyadicLength (Z^d):ℝ)^2*
            max (C*(1+height)^order) (192*(1+height)*Cs)*(η.modulus.absNorm:ℝ)^(2*eps))*
            (Z^(((6/11)*a-197/330+(146/11)*e)+(5/33)*(-(4/25:ℝ)+(a-1/2)+mesh)+loss)*
             Z^(d*(Exponent.R0 (2*a-1)+6*ε+εm)+v*(a-1/2+12*e+eps*(N+8)-17/50))) := by ring
        _ = _ := by rw [hz]

theorem actual_source_central_cube_with_shell_bound (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A) 
    (ell : Fin N→ℝ) (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (hellsum : ∑j,ell j=(5/33:ℝ)) 
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃D : ℝ,0<D ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      ∀(a : ℝ) (i : ℕ),i≤n → 51/100≤a → a≤1 →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      (∀j l,j≠l → Disjoint (T j) (T l)) →
      ∀C t : ℝ,0≤C →
      (∑u∈rows,rowNorm u^(a-1/2+12*e+eps*(N+8)-17/50))≤C*Z^t →
      ‖finiteCentralCubeRows S hS hmax η rows T (sourcePoolOutside M H S N c b Y) W Y W0 W1
        (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z e (fun _=>a) (fun _=>(3*i+1:ℕ)*Z^τ)‖≤
        D*C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(((6/11)*a-197/330+(146/11)*e)+(5/33)*(-(4/25:ℝ)+(a-1/2)+mesh)+loss+t) := by
  obtain ⟨D,hD,hcentral⟩ := actual_fixed_scale_central_integral M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax W hWs hW hWB ell hello hellhi hellsum W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨D,hD,?_⟩
  intro η
  filter_upwards [hcentral η,eventually_gt_atTop (0:ℝ)] with Z hz hZ
  intro d hd hd' rows hrows a i hi ha ha1 hnext
  dsimp only
  intro hdis C t hC hs
  have hp := hz d hd hd' rows hrows a i hi ha ha1 (by
    intro u hu
    convert hnext u hu using 1
    exact congrArg (fun inst : Fintype (Sum Bool (RayQuotient.Characters M H)) =>
      @detectorMaximum (Sum Bool (RayQuotient.Characters M H)) inst
        (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(i+1:ℕ)*Z^τ))
      (Subsingleton.elim _ _)) hdis
  apply hp.trans
  calc
    _ ≤ D*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(((6/11)*a-197/330+(146/11)*e)+(5/33)*(-(4/25:ℝ)+(a-1/2)+mesh)+loss)*(C*Z^t) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by
      rw [Real.rpow_add hZ (((6/11)*a-197/330+(146/11)*e)+(5/33)*(-(4/25:ℝ)+(a-1/2)+mesh)+loss) t]
      ring

lemma central_halo_cost {d v q μ : ℝ} (hq : -1≤q) (hvd : v≤d) (hμ : d-v≤μ) :
    v*q≤d*q+μ := by
  have hh := mul_nonneg (sub_nonneg.mpr hvd) (by linarith : 0≤q+1)
  nlinarith

end
end ZetaZeroFree.Analytic.Probe
