
theorem fullMain : type_of% @OMA.S_oeis_a381423.main := by
  refine ⟨?_, source_difference, drop_characterization, ?_, source_growth⟩
  · intro n
    exact ⟨source_unique n, source_formula n⟩
  · intro q hq
    exact ⟨five_end_succ q hq, five_end_shift_eight q hq, four_count_shift_eight q hq⟩

end A381423Certificate

theorem OMA.solution : type_of% @OMA.S_oeis_a381423.main := by
  exact A381423Certificate.fullMain
