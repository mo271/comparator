def myAnswer : Prop := True

theorem myThm : myAnswer ↔ 1 + 1 = 2 := by
  unfold myAnswer
  decide
