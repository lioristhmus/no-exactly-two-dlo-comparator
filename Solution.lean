import NoExactlyTwoDlo.FO.Main2

open FirstOrder Language BoundedFormula

namespace ExactTwoDLO.Comparator

/-- The proposition-level witness to the formalization's Type-valued endpoint. -/
theorem derivable :
    Nonempty (ExactThreeDLO.FO.Provable ExactThreeDLO.FO.Zsep (∼ FO.spec2Sentence)) :=
  ⟨FO.zsep_proves_not_spec2Sentence⟩

end ExactTwoDLO.Comparator
