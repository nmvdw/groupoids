Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     general_category bicategory.bicategory.

Section TerminalBiCategory.
  Definition terminal_cat : PreCategory.
  Proof.
    simple refine (@Build_PreCategory
                     Unit
                     (fun _ _ => Unit)
                     (fun _ => tt)
                     (fun _ _ _ _ _ => tt)
                     _ _ _ _)
    ; intros ; apply path_ishprop.
  Defined.

  Definition terminal_d : BiCategory_d.
  Proof.
    make_bicategory.
    - exact Unit.
    - exact (fun _ _ => terminal_cat).
    - intros [ ] ; simpl in *.
      exact tt.
    - intros [ ] [ ] [ ] [[ ] [ ]] ; simpl in *.
      exact tt.
    - intros [ ] [ ] [ ] [[ ] [ ]] [[ ] [ ]] [[ ] [ ]] ; simpl in *.
      exact tt.
    - intros [ ] [ ] [ ] ; simpl in *.
      exact tt.
    - intros [ ] [ ] [ ] ; simpl in *.
      exact tt.
    - intros [ ] [ ] [ ] ; simpl in *.
      exact tt.
    - intros [ ] [ ] [ ] ; simpl in *.
      exact tt.
    - intros [ ] [ ] [ ] [ ] [ ] [ ] [ ] ; simpl in *.
      exact tt.
    - intros [ ] [ ] [ ] [ ] [ ] [ ] [ ] ; simpl in *.
      exact tt.
  Defined.

  Definition terminal_is_bicategory : is_bicategory terminal_d.
  Proof.
    make_is_bicategory ; try reflexivity.
    - intros [ ] [ ] [ ] [[ ] [ ]] ; simpl in *.
      reflexivity.
    - intros [ ] [ ] [ ] [[ ] [ ]] [[ ] [ ]] [[ ] [ ]] [[ ] [ ]] [[ ] [ ]] ; simpl in *.
      reflexivity.
    - intros [ ] [ ] [ ] [ ] [ ] ; simpl in *.
      reflexivity.
  Qed.

  Definition terminal_bicategory : BiCategory
    := Build_BiCategory terminal_d terminal_is_bicategory.
End TerminalBiCategory.
