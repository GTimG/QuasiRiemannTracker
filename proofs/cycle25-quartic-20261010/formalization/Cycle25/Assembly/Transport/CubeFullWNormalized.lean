/- Adapted from weighted upstream PR6; original proof structure retained. -/
import Cycle25.Assembly.Transport.CubeFullWTransfer
import Cycle25.Assembly.Transport.CanonicalRayCube
import Cycle25.Assembly.Low.Normalizer
import OAI.NumberTheory.DirichletL.PrimeRows.CubeNormalizer

namespace OAI
noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.Cycle25HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

omit [NeZero M] in
private theorem transferPoolOutside (S : Finset (Ideal O)) (K : ℕ) (a b : ℝ) (Y : Fin K→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S a b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S a b (Y j) P).mp hP |>.2.2.2

theorem actual_normalized_cube_fullW_arbitrary_saving
    (K : ℕ) (τ saving a b B ζ nu : ℝ)
    (hτ : 0 < τ) (ha : 0 < a) (hab : a ≤ b) (hB : 0 ≤ B) (hζ : ζ ≤ 1/48) (hnu : 0 < nu)
    (e : ℝ) (he : 0 < e) (he' : e < 1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (ell : Fin K→ℝ) (hell : ∀j,0 < ell j) (hellinj : Function.Injective ell)
    (hellsum : ∑j,ell j=Cycle25.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Ioo a b)
    (hWB : ∀j y,0 ≤ W j y ∧ W j y ≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0 ≤ (W0 y).re) (hp1 : ∀y,0 ≤ (W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0 ≤ C ∧ ∀ᶠ Z : ℝ in atTop,∀η : Character,
      ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ≤ Z^((Cycle25.h:ℝ)+ζ)) →
      ∀(alpha base height : FreeRow→ℝ) (idx : FreeRow→ℕ),
      (∀u∈R,(51/100:ℝ) ≤ alpha u ∧ alpha u ≤ 1 ∧ 2 < base u ∧
        Z^τ ≤ height u ∧ height u ≤ (3*idx u+2:ℕ)*base u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          (3*(idx u+1:ℕ)*base u) < alpha u+2*e) →
      let Y : Fin K→ℝ := fun j=>Z^(ell j)
      let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Y j)
      let hT := transferPoolOutside M H S K a b Y
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (Cycle25.ell)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
      normer≠0 ∧
      ‖finiteCentralCubeRows S hS hmax η R T hT WC Y W0 W1
          (Z^(Cycle25.lx:ℝ)) (Z^(Cycle25.ly:ℝ)) Z e alpha height/normer-
        Cycle25.Weighted.FullWContour.finiteCentralFullWRows S hS hmax η R T hT WC Y W0 W1
          (Z^(Cycle25.lx:ℝ)) (Z^(Cycle25.ly:ℝ)) Z e alpha height/normer‖ ≤
        C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨Ct,hCt,htransfer⟩ := finite_cube_fullW_arbitrary_saving
    (ι:=RayQuotient.Characters M H) K τ (saving+nu) b ζ B hτ (ha.trans_le hab) hζ hB
    e he he' S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨Cn,hCn,hnormalizer⟩ := Cycle25WeightedLowNormalizer.actual_ray_normalizer_inverse M H hH S hS a b ha hab ell
    hell hellsum W hW hcompact hsupp (fun j y=>(hWB j y).1) hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  refine ⟨Ct*Cn,mul_nonneg hCt hCn.le,?_⟩
  filter_upwards [hnormalizer,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass M H) S
      (fun _ : Fin K=>a) (fun _=>b) ell (fun _=>ha) (fun _=>hab) hellinj,
    eventually_ge_atTop (1:ℝ)] with Z hnorm hdis hZ
  intro η R hR alpha base height idx hbin
  dsimp only at hnorm ⊢
  refine ⟨hnorm.1,?_⟩
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  let Y : Fin K→ℝ := fun j=>Z^(ell j)
  let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Y j)
  let hT := transferPoolOutside M H S K a b Y
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hpool (j : Fin K) (P : ProbePhysical.PrimeIdeal) (hP : P∈T j) :
      (P.val.absNorm:ℝ) ≤ b*Z^(ell j) := by
    have hh := (pool_norm_bounds (RayQuotient.identityClass M H) S ha.le hab
      (Real.rpow_pos_of_pos hZ0 (ell j)) P hP).2
    simpa only [mul_comm] using hh
  have hWCB (j : Fin K) (y : ℝ) : ‖WC j y‖ ≤ B := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  have hb := htransfer η Z hZ R hR T hT hdis ell hellsum hpool WC hWCB
    alpha base height idx (rayCubeFamily M H hH) hbin
  rw [←sub_div,div_eq_mul_inv,norm_mul]
  apply (mul_le_mul hb hnorm.2 (norm_nonneg _) (by positivity)).trans_eq
  have hp : Z^(-(saving+nu))*Z^nu=Z^(-saving) := by
    rw [←Real.rpow_add hZ0]
    congr 1
    ring
  calc
    _ = (Ct*Cn*(η.modulus.absNorm:ℝ)^2)*(Z^(-(saving+nu))*Z^nu) := by ring
    _ = _ := by rw [hp]

end SevenEighths.Cycle25HighRowFamily
end
end OAI
