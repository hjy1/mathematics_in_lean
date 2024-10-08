import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic

set_option warningAsError false

variable {G : Type*} [Group G]

namespace MyGroup

theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  have h : (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) = 1 := by
    rw [mul_assoc, ← mul_assoc a⁻¹ a, inv_mul_cancel, one_mul, inv_mul_cancel]
  rw [← h, ← mul_assoc, inv_mul_cancel, one_mul]

theorem mul_one (a : G) : a * 1 = a := by
  rw [← inv_mul_cancel a, ← mul_assoc, mul_inv_cancel, one_mul]

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have h1 : (a * b) * (b⁻¹ * a⁻¹) = 1 := by
    rw [mul_assoc, <- mul_assoc b, mul_inv_cancel, one_mul, mul_inv_cancel]
  rw [← inv_unique h1]
