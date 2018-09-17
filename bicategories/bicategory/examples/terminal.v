Require Import HoTT.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
     bicategory.adjoint
     bicategory.adjoint_unique
     bicategory.univalent.

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

  Global Instance locally_univalent_terminal_bicategory
    : LocallyUnivalent terminal_bicategory.
  Proof.
    intros [ ] [ ] [ ] [ ].
    cbn.
    simple refine (isequiv_adjointify _ _ _ _).
    - simple refine (fun _ => idpath).
    - intros iso ; cbn.
      apply path_isomorphic ; cbn.
      apply path_ishprop.
    - intros p ; cbn.
      apply path_ishprop.      
  Qed.

  Global Instance univalent_0_terminal_bicategory
         `{Funext}
    : Univalent_0 terminal_bicategory.
  Proof.
    intros [ ] [ ] ; cbn.
    simple refine (isequiv_adjointify _ _ _ _).
    - exact (fun _ => idpath).
    - intros x.
      cbn in *.
      apply path_adjoint_equivalence.
      apply path_ishprop.
    - intros x ; cbn.
      apply path_ishprop.
  Qed.

  Global Instance univalent_terminal_bicategory
         `{Funext}
    : Univalent terminal_bicategory.
  Proof.
    split ; apply _.
  Qed.
End TerminalBiCategory.
