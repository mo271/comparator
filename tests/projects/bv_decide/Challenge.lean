import Std.Tactic.BVDecide

def f (x : BitVec 32) := x + 1
theorem test_bv_decide (x : BitVec 32) : x + 0 = x := by sorry
