Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
Require Import GR.bicategories.bicategories.
Require Import GR.bicategories.lax_functors.
Require Import GR.bicategories.lax_transformations.
Require Import GR.bicategories.modifications.

Record BiAdjunction_d
       `{Univalence}
       (C D : BiCategory)
  := Build_BiAdjunction_d
       { left_adjoint_d : PseudoFunctor C D ;
         right_adjoint_d : PseudoFunctor D C ;
         unit_d : PseudoTransformation
                    (lax_id_functor C)
                    (lax_comp right_adjoint_d left_adjoint_d) ;
         counit_d : PseudoTransformation
                      (lax_comp left_adjoint_d right_adjoint_d)
                      (lax_id_functor D) ;
       }.

Arguments Build_BiAdjunction_d {_ C D} _ _ _ _.
Ltac make_biadjunction := simple refine (Build_BiAdjunction_d _ _ _ _).
Arguments left_adjoint_d {_ C D}.
Arguments right_adjoint_d {_ C D}.
Arguments unit_d {_ C D}.
Arguments counit_d {_ C D}.

Definition triangle_l_lhs
           `{Univalence}
           {C D : BiCategory}
           (F : BiAdjunction_d C D)
  : LaxTransformation (left_adjoint_d F) (left_adjoint_d F)
  := compose
       (lax_right_identity_inv (left_adjoint_d F))
       (compose
          (whisker_L (left_adjoint_d F) (unit_d F))
          (compose
             (lax_associativity_inv _ _ _)
             (compose
                (whisker_R (left_adjoint_d F) (counit_d F))
                (lax_left_identity (left_adjoint_d F))
             )
          )
       ).

Definition triangle_r_lhs
           `{Univalence}
           {C D : BiCategory}
           (F : BiAdjunction_d C D)
  : LaxTransformation (right_adjoint_d F) (right_adjoint_d F)
  := compose
       (lax_left_identity_inv (right_adjoint_d F))
       (compose
          (whisker_R (right_adjoint_d F) (unit_d F))
          (compose
             (lax_associativity _ _ _)
             (compose
                (whisker_L (right_adjoint_d F) (counit_d F))
                (lax_right_identity (right_adjoint_d F))
             )
          )
       ).

Record is_biadjunction
       `{Univalence}
       {C D : BiCategory}
       (F : BiAdjunction_d C D)
  := Build_is_biadjunction
       {
         adj_triangle_l_p :
           PseudoModification
             (triangle_l_lhs F)
             (identity_transformation (left_adjoint_d F)) ;
         adj_triangle_r_p :
           PseudoModification
             (triangle_r_lhs F)
             (identity_transformation (right_adjoint_d F))
       }.

Arguments Build_is_biadjunction {_ C D F} _ _.
Ltac make_is_biadjunction := simple refine (Build_is_biadjunction _ _).
Arguments adj_triangle_l_p {_ C D F} _.
Arguments adj_triangle_r_p {_ C D F} _.

Definition BiAdjunction
           `{Univalence}
           (C D : BiCategory)
  : Type
  := {F : BiAdjunction_d C D & is_biadjunction F}.

Definition Build_BiAdjunction
           `{Univalence}
           {C D : BiCategory}
           (F : BiAdjunction_d C D)
           (HF : is_biadjunction F)
  : BiAdjunction C D
  := (F;HF).

Definition left_adjoint
           `{Univalence}
           {C D : BiCategory}
           (F : BiAdjunction C D)
  : PseudoFunctor C D
  := left_adjoint_d F.1.

Definition right_adjoint
           `{Univalence}
           {C D : BiCategory}
           (F : BiAdjunction C D)
  : PseudoFunctor D C
  := right_adjoint_d F.1.

Definition unit
           `{Univalence}
           {C D : BiCategory}
           (F : BiAdjunction C D)
  := unit_d F.1.

Definition counit
           `{Univalence}
           {C D : BiCategory}
           (F : BiAdjunction C D)
  := counit_d F.1.

Definition adj_triangle_l
           `{Univalence}
           {C D : BiCategory}
           (F : BiAdjunction C D)
  : PseudoModification
      (triangle_l_lhs F.1)
      (identity_transformation (left_adjoint F))
  := adj_triangle_l_p F.2.

Definition adj_triangle_r
           `{Univalence}
           {C D : BiCategory}
           (F : BiAdjunction C D)
  : PseudoModification
      (triangle_r_lhs F.1)
      (identity_transformation (right_adjoint F))
  := adj_triangle_r_p F.2.

Section Restriction.
  Context `{Univalence}
          {C D : BiCategory}.
  Variable (adj : BiAdjunction C D)
           (P : C -> hProp)
           (HP : forall (x : D), P(right_adjoint adj x)).

  Definition restriction_left_adjoint := pseudo_restriction (left_adjoint adj) P.

  Definition restriction_right_adjoint := pseudo_factor (right_adjoint adj) P HP.

  Definition restriction_unit_d
    : LaxTransformation_d
        (lax_id_functor (full_sub C P))
        (lax_comp restriction_right_adjoint restriction_left_adjoint).
  Proof.
    make_lax_transformation.
    - exact (fun X => unit adj X.1).
    - exact (fun X Y f => laxnaturality_of (unit adj) f).
  Defined.

  Definition is_lax_restriction_unit_d
    : is_lax_transformation restriction_unit_d.
  Proof.
    make_is_lax_transformation.
    - intros X Y f g α ; simpl in *.
      exact (laxnaturality_natural (unit adj) α).
    - intros X.
      exact (transformation_unit (unit adj) X.1).
    - intros X Y Z f g.
      exact (transformation_assoc (unit adj) f g).
  Qed.

  Definition restriction_unit
    : PseudoTransformation
        (lax_id_functor (full_sub C P))
        (lax_comp restriction_right_adjoint restriction_left_adjoint).
  Proof.
    make_pseudo_transformation_lax.
    - exact (Build_LaxTransformation restriction_unit_d is_lax_restriction_unit_d).
    - intros [X PX] [Y PY] f ; cbn in *.
      exact (laxnaturality_of_is_iso (unit adj) f).
  Defined.

  Definition restriction_counit_d
    : LaxTransformation_d
        (lax_comp restriction_left_adjoint restriction_right_adjoint)
        (lax_id_functor D).
  Proof.
    make_lax_transformation.
    - exact (counit adj).
    - intros X Y f ; cbn.
      exact (laxnaturality_of (counit adj) f).
  Defined.

  Definition is_lax_restriction_counit_d
    : is_lax_transformation restriction_counit_d.
  Proof.
    make_is_lax_transformation.
    - intros X Y f g p.
      exact (laxnaturality_natural (counit adj) p).
    - intros X ; simpl.
      exact (transformation_unit (counit adj) X).
    - intros X Y Z f g.
      exact (transformation_assoc (counit adj) f g).
  Qed.

  Definition restriction_counit
    : PseudoTransformation
        (lax_comp restriction_left_adjoint restriction_right_adjoint)
        (lax_id_functor D).
  Proof.
    make_pseudo_transformation_lax.
    - exact (Build_LaxTransformation restriction_counit_d is_lax_restriction_counit_d).
    - intros X Y f ; cbn in *.
      exact (laxnaturality_of_is_iso (counit adj) f).
  Defined.

  Definition restrict_adjunction_d : BiAdjunction_d (full_sub C P) D
    := Build_BiAdjunction_d
         restriction_left_adjoint
         restriction_right_adjoint
         restriction_unit
         restriction_counit.

  Local Notation restriction_triangle_l_d
    := (fun (A : (full_sub C P)) =>
          mod_component (adj_triangle_l adj) A.1
          : (triangle_l_lhs restrict_adjunction_d A)
              ==>
              identity_transformation (left_adjoint_d restrict_adjunction_d) A).

  Definition restrict_triangle_l_lhs
             {X Y : full_sub C P}
             (f : full_sub C P ⟦X,Y⟧)
    : laxnaturality_of (triangle_l_lhs adj.1) f
      =
      laxnaturality_of (triangle_l_lhs restrict_adjunction_d) f
    := idpath.

  Definition restriction_triangle_l_is_mod
    : is_modification restriction_triangle_l_d.
  Proof.
    intros X Y f.
    exact (mod_commute (adj_triangle_l adj) f).
  Qed.

  Definition restriction_triangle_l
    : PseudoModification
        (triangle_l_lhs restrict_adjunction_d)
        (identity_transformation (left_adjoint_d restrict_adjunction_d)).
  Proof.
    make_pseudo_modification.
    - exact (Build_Modification restriction_triangle_l_d restriction_triangle_l_is_mod).
    - intros [X PX] ; cbn in *.
      exact (mod_component_is_iso_pseudo (adj_triangle_l adj) X).
  Defined.

  Local Notation restriction_triangle_r_d
    := (fun (A : D) =>
          mod_component (adj_triangle_r adj) A
          : (triangle_r_lhs restrict_adjunction_d A)
              ==> identity_transformation (right_adjoint_d restrict_adjunction_d) A).

  Definition restriction_triangle_r_lhs
             {X Y : D}
             (f : D⟦X,Y⟧)
    : laxnaturality_of (triangle_r_lhs adj.1) f
      =
      laxnaturality_of (triangle_r_lhs restrict_adjunction_d) f
    := idpath.
  
  Definition restriction_triangle_r_is_mod
    : is_modification restriction_triangle_r_d.
  Proof.
    intros X Y f.
    exact (mod_commute (adj_triangle_r adj) f).
  Qed.

  Definition restriction_triangle_r
    : PseudoModification
        (triangle_r_lhs restrict_adjunction_d)
        (identity_transformation (right_adjoint_d restrict_adjunction_d)).
  Proof.
    make_pseudo_modification.
    - exact (Build_Modification restriction_triangle_r_d restriction_triangle_r_is_mod).
    - intros X ; cbn in *.
      exact (mod_component_is_iso_pseudo (adj_triangle_r adj) X).
  Defined.

  Definition restrict_adjunction : BiAdjunction (full_sub C P) D.
  Proof.
    simple refine (Build_BiAdjunction restrict_adjunction_d _).
    make_is_biadjunction.
    - exact restriction_triangle_l.
    - exact restriction_triangle_r.
  Defined.
End Restriction.
