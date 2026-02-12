import Batteries.Data.List.Basic

theorem splitOn_append_separator [DecidableEq α] (L R : List α) (sep : α) (h : sep ∉ L) :
  (L ++ sep :: R).splitOn sep = L :: R.splitOn sep := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp [List.splitOn]
    simp at h
    have ⟨h1, h2⟩ := h
    simp [h1]
    -- Wait, List.splitOn is defined via a loop usually.
    -- Let's see how Batteries defines it.
    sorry

#check List.splitOn
