def f (x : Nat) := x + 1

axiom test_native_decide._native.native_decide.ax_1_1 : decide (f 5 = 6) = true

theorem test_native_decide : f 5 = 6 := by sorry
