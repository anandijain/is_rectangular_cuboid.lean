-- import Mathlib.Algebra.BigOperators.Ring
-- import Mathlib.Data.Real.Basic
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Vector.Defs
import Mathlib.Analysis.Convex.Side
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.LinearAlgebra.AffineSpace.Basis
import Mathlib.LinearAlgebra.FiniteDimensional
open scoped Affine EuclideanGeometry Real RealInnerProductSpace ComplexConjugate
open Module Complex EuclideanGeometry
open AffineSubspace Module
open Affine

-- section AffineSpace'

-- variable (k : Type*) {V : Type*} {P : Type*}
-- variable {ι : Type*}

-- open AffineSubspace Module

-- variable [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]
-- variable [AddCommGroup V] [MetricSpace P] [hd2 : Fact (finrank k V = 2)] [Module.Oriented ℝ V (Fin 2)]

variable (k : Type*) {V : Type*} {P : Type*}
variable {ι : Type*}

-- variable [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P] [Invertible (2 : k)]
-- variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
-- variable [Module ℝ V]
-- variable [hd2 : Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [hd2 : Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

variable (a b : P)
def s : Set P := {a, b}
#check s
-- theorem collinear_pair (p₁ p₂ : P) : Collinear k ({p₁, p₂} : Set P) := by
theorem ab_collinear (a b : P) : Collinear ℝ ({a, b} : Set P) := collinear_pair ℝ a b

#eval EuclideanGeometry.oangle a b (midpoint ℝ a b)
#check EuclideanGeometry.oangle a b (midpoint ℝ a b)
-- #check (AffineMap.lineMap a b)

theorem midpoint_collinear (a b : P) : Collinear ℝ ({a, b, midpoint ℝ a b} : Set P) := by
  have m :=  midpoint ℝ a b
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  use a, b -ᵥ a
  intro p hp
  rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  cases' hp with hp hp
  · use 0
    simp [hp]
  cases' hp with hp hp
  . use 1
    simp [hp]
  . use (1/2 : ℝ)
    simp [hp]
    rw [midpoint, AffineMap.lineMap]
    simp
