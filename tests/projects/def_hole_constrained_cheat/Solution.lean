def myAnswer : Prop := 1 + 1 = 2

theorem myThm : myAnswer ↔ 1 + 1 = 2 := by
  unfold myAnswer
  rfl
