
-- import Mathlib.Geometry.Euclidean.Basic
-- import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
-- import Mathlib.LinearAlgebra.FiniteDimensional
-- import Mathlib.Data.Vector.Basic
-- import Mathlib.Data.Vector.Defs

-- -- import Nat
-- #check Nat

-- variable {V : Type*} {P : Type*}
-- variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
-- variable [NormedAddTorsor V P]
-- variable [DivisionRing V]
-- variable {α W Q : Type*} [NormedAddCommGroup W] [MetricSpace Q] [NormedAddTorsor W Q]

-- #check MetricSpace ℝ
-- def hello := "world"

-- #check 1 + 1 = 2
-- #check 1 + 1
-- #eval 1+1

-- variable (p₁ p₂ : P)
-- variable (a b : P)

-- -- #eval dist () p₁ p₂

-- theorem one_plus_one_is_two : (1 + 1 = 2) := by
--   rw [Nat.add_succ]


-- -- prove that the midpoint is colinear with the segment AB
-- -- where A is -1 and B is 1

-- #check (-1: ℝ)
-- #check ({-1, 1} : Set ℝ)
-- -- variable s ({-1, 1} : Set ℝ)
-- #check vectorSpan ℝ ({-1, 1} : Set ℝ)
-- -- #check midpoint (2 : P) (1 : ℝ)
-- #check midpoint ℝ p₁ p₂
-- #check midpoint ℝ (-1 : ℝ)  1
-- #reduce midpoint ℝ (-1 : ℝ)  1

-- -- #check {-1, midpoint -1 1, 1} : Set ℝ
-- -- Collinear
-- -- #check Collinear ({a, b, midpoint ℝ a b} : Set P)
-- -- #check Collinear ({a, b} : Set P)
-- -- #check Module ℝ ℝ  -- Does ℝ have a module structure over itself?
-- -- inferInstance
-- -- noncomputable
-- -- #eval Module.finrank ℝ ℝ  -- Output: 1

-- -- #check ℝ^3
-- #check Fin 4 → ℝ

-- def v1 : ℝ × ℝ × ℝ := (1.0, 2.0, 3.0)
-- #check v1

-- #eval v1
-- -- #check (((1.0 : ℝ), (2.0: ℝ )) : Vector ℝ 2) -- why is Vector not found


-- def myList : List ℕ := [1, 2, 3, 4, 5]
-- #eval myList.get? 0

-- #check myList
-- def my_set : Set ℝ := {-1, 1}
-- -- def my_p_set : Set P := {2, 1}
-- #check my_set
-- #check vectorSpan ℝ my_set
-- -- Collinear
-- -- #eval vectorSpan ℝ my_set
-- -- #check Collinear ({a, b, midpoint ℝ a b} : Set P)
-- #check Collinear ℝ my_set
-- #check Collinear ℝ ({(0: ℝ ) , (1: ℝ), midpoint ℝ 0 1} : Set ℝ)
-- -- #check IsPrime
-- #check midpoint
-- variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] [NormedSpace 𝕜 V]
-- #check 𝕜
-- #check Type u_6
-- -- variable [Invertible (2 : V)]
-- -- variable [Module V V]
-- #check line[ℝ, p₁, p₂]
-- -- collinear_pair
-- -- theorem ab_colinear_imp_ab_mid_ab_collinear


-- -- #check EuclideanGeometry.oangle_self_left_right a b
-- theorem midpoint_collinear (a b : P) : Collinear ℝ ({a, b} : Set P) := by
--   rw [EuclideanGeometry.oangle_self_left a b, oangle_eq_zero_or_eq_pi_iff_collinear]

-- -- subgoal is to provide a list/set of line segments in R2
-- -- and check if they form a rectangle by
-- -- orthogonality of each adjacent line segment pair
-- -- that it forms a signle closed loop

-- -- is_rectangular_cuboid : ()
