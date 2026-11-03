/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Analysis/EllipticEquations/DivergenceForm/WeakSolutions.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Analysis.SmoothFunctions.CompactOpenHolomorphyAndMeromorphy

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPContLocalEnergy.SobolevEnergyEstimates.Raw

open MeasureTheory
open KPContLocalNorm

def zeroIndex (n k : ℕ) : MultiIndex n k := ⟨fun _ => 0, by simp⟩

def firstIndex {n : ℕ} (i : Fin n) : MultiIndex n 1 :=
  ⟨fun j => if j = i then 1 else 0, by
    simp only [apply_ite Fin.val, Fin.val_one, Fin.val_zero]
    simp⟩

def value {n k : ℕ} {B : LocalBall n} (u : IntegerSobolev B k) : BallL2 B :=
  u.derivatives (zeroIndex n k)

def gradient {n : ℕ} {B : LocalBall n} (u : IntegerSobolev B 1)
    (i : Fin n) : BallL2 B :=
  u.derivatives (firstIndex i)

structure Coefficients {n : ℕ} (B : LocalBall n) (cρ Cρ κ Λ : ℝ) where
  density : Space n → ℝ
  matrix : Space n → Matrix (Fin n) (Fin n) ℝ
  density_smooth : ContDiffOn ℝ (⊤ : ℕ∞) density B.carrier
  matrix_smooth : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => matrix x i j) B.carrier
  density_bounds : ∀ x ∈ B.carrier, cρ ≤ density x ∧ density x ≤ Cρ
  symmetric : ∀ x ∈ B.carrier, ∀ i j, matrix x i j = matrix x j i
  ellipticity : ∀ x ∈ B.carrier, ∀ ξ : Space n,
    κ * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, matrix x i j * ξ i * ξ j
  upper_bound : ∀ x ∈ B.carrier, ∀ ξ : Space n,
    (∑ i, ∑ j, matrix x i j * ξ i * ξ j) ≤ Λ * ‖ξ‖ ^ 2

def divergenceOperator {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) (u : Space n → ℂ) : Space n → ℂ :=
  fun x => -(D.density x : ℂ)⁻¹ * ∑ i,
    fderiv ℝ (fun y => (D.density y : ℂ) *
      ∑ j, (D.matrix y i j : ℂ) * coordinateDerivativeList [j] u y) x
        (EuclideanSpace.single i 1)

def WeakEquation {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) (z : ℂ)
    (u : IntegerSobolev B 1) (h : BallL2 B) : Prop :=
  ∀ φ : TestFunction B.toOpens ℂ ⊤,
    (∫ x in B.carrier, (D.density x : ℂ) *
      ∑ i, ∑ j, (D.matrix x i j : ℂ) * gradient u j x *
        star (coordinateDerivativeList [i] (fun y => φ y) x)) -
      z * (∫ x in B.carrier, (D.density x : ℂ) * value u x * star (φ x)) =
        ∫ x in B.carrier, (D.density x : ℂ) * h x * star (φ x)

def Represents {n k : ℕ} {B : LocalBall n} (u : IntegerSobolev B k)
    (f : Space n → ℂ) : Prop :=
  ∀ᵐ x ∂volume.restrict B.carrier, value u x = f x

def RepresentsClassicalDerivatives {n k : ℕ} {B : LocalBall n}
    (u : IntegerSobolev B k) (f : Space n → ℂ) : Prop :=
  ∀ α : MultiIndex n k,
    ∀ᵐ x ∂volume.restrict B.carrier, u.derivatives α x = coordinateDerivative α f x

def functionL2Norm {n : ℕ} (B : LocalBall n) (f : Space n → ℂ) : ℝ :=
  Real.sqrt (∫ x in B.carrier, ‖f x‖ ^ 2)

end DedekindZetaZeroFree.KPContLocalEnergy.SobolevEnergyEstimates.Raw

end
