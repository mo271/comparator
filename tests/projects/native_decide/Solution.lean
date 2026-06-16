def f (x : Nat) := x + 1

theorem test_native_decide : f 5 = 6 := by native_decide

