Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories.bicategory Require Import
     bicategory
     examples.lax_functors_bicat
     adjoint
     equivalence
     examples.full_sub.
From GR.bicategories.lax_functor Require Import
     lax_functor
     examples.restriction
     examples.factor_full_sub
     examples.identity
     examples.composition.
From GR.bicategories.lax_transformation Require Import
     lax_transformation
     examples.whisker_L
     examples.whisker_R
     examples.right_identity
     examples.left_identity
     examples.associativity
     examples.right_identity_inv
     examples.left_identity_inv
     examples.associativity_inv
     examples.restriction
     examples.identity
     examples.composition.
From GR.bicategories.modification Require Import
     modification
     examples.composition.

Record BiAdjunction_d
       `{Funext}
       (C D : BiCategory)
  := Build_BiAdjunction_d
       { left_adjoint_d : LaxFunctor C D ;
         left_adjoint_pseudo_d : is_pseudo left_adjoint_d ;
         right_adjoint_d : LaxFunctor D C ;
         right_adjoint_pseudo_d : is_pseudo right_adjoint_d ;
         unit_d : LaxTransformation
                    (lax_id_functor C)
                    (lax_comp right_adjoint_d left_adjoint_d) ;
         counit_d : LaxTransformation
                      (lax_comp left_adjoint_d right_adjoint_d)
                      (lax_id_functor D) ;
       }.

Arguments Build_BiAdjunction_d {_ C D} _ _ _ _ _ _.
Ltac make_biadjunction := simple refine (Build_BiAdjunction_d _ _ _ _ _ _).
Arguments left_adjoint_d {_ C D}.
Arguments right_adjoint_d {_ C D}.
Arguments unit_d {_ C D}.
Arguments counit_d {_ C D}.

Global Instance left_adjoint_pseudo_functor
       `{Funext}
       {C D : BiCategory}
       (F : BiAdjunction_d C D)
  : is_pseudo (left_adjoint_d F).
Proof.
  apply left_adjoint_pseudo_d.
Defined.

Global Instance right_adjoint_pseudo_functor
       `{Funext}
       {C D : BiCategory}
       (F : BiAdjunction_d C D)
  : is_pseudo (right_adjoint_d F).
Proof.
  apply right_adjoint_pseudo_d.
Defined.

Definition triangle_l_lhs
           `{Funext}
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
           `{Funext}
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
       `{Funext}
       {C D : BiCategory}
       (F : BiAdjunction_d C D)
  := Build_is_biadjunction
       {
         unit_pseudo_p : is_pseudo_transformation (unit_d F) ;
         counit_pseudo_p : is_pseudo_transformation (counit_d F) ;
         adj_triangle_l_p :
           modification
             (triangle_l_lhs F)
             (identity_transformation (left_adjoint_d F)) ;
         adj_triangle_l_p_pseudo : is_pseudo_modification adj_triangle_l_p ;
         adj_triangle_r_p :
           modification
             (triangle_r_lhs F)
             (identity_transformation (right_adjoint_d F)) ;
         adj_triangle_r_p_pseudo : is_pseudo_modification adj_triangle_r_p
       }.

Arguments Build_is_biadjunction {_ C D F} _ _ _ _ _ _.
Ltac make_is_biadjunction := simple refine (Build_is_biadjunction _ _ _ _ _ _).
Arguments unit_pseudo_p {_ C D F} _.
Arguments counit_pseudo_p {_ C D F} _.
Arguments adj_triangle_l_p {_ C D F} _.
Arguments adj_triangle_l_p_pseudo {_ C D F} _.
Arguments adj_triangle_r_p {_ C D F} _.
Arguments adj_triangle_r_p_pseudo {_ C D F} _.

Definition BiAdjunction
           `{Funext}
           (C D : BiCategory)
  : Type
  := {F : BiAdjunction_d C D & is_biadjunction F}.

Definition Build_BiAdjunction
           `{Funext}
           {C D : BiCategory}
           (F : BiAdjunction_d C D)
           (HF : is_biadjunction F)
  : BiAdjunction C D
  := (F;HF).

Definition left_adjoint
           `{Funext}
           {C D : BiCategory}
           (F : BiAdjunction C D)
  := left_adjoint_d F.1.

Global Instance left_adjoint_pseudo
       `{Funext}
       {C D : BiCategory}
       (F : BiAdjunction C D)
  : is_pseudo (left_adjoint F)
  := left_adjoint_pseudo_d _ _ F.1.

Definition right_adjoint
           `{Funext}
           {C D : BiCategory}
           (F : BiAdjunction C D)
  := right_adjoint_d F.1.

Global Instance right_adjoint_pseudo
       `{Funext}
       {C D : BiCategory}
       (F : BiAdjunction C D)
  : is_pseudo (right_adjoint F)
  := right_adjoint_pseudo_d _ _ F.1.

Definition unit
           `{Funext}
           {C D : BiCategory}
           (F : BiAdjunction C D)
  := unit_d F.1.

Global Instance unit_pseudo
       `{Funext}
       {C D : BiCategory}
       (F : BiAdjunction C D)
  : is_pseudo_transformation (unit F)
  := unit_pseudo_p F.2.

Definition counit
           `{Funext}
           {C D : BiCategory}
           (F : BiAdjunction C D)
  := counit_d F.1.

Global Instance counit_pseudo
       `{Funext}
       {C D : BiCategory}
       (F : BiAdjunction C D)
  : is_pseudo_transformation (counit F)
  := counit_pseudo_p F.2.

Definition adj_triangle_l
           `{Funext}
           {C D : BiCategory}
           (F : BiAdjunction C D)
  : modification
      (triangle_l_lhs F.1)
      (identity_transformation (left_adjoint F))
  := adj_triangle_l_p F.2.

Global Instance adj_triangle_l_pseudo
       `{Funext}
       {C D : BiCategory}
       (F : BiAdjunction C D)
  : is_pseudo_modification (adj_triangle_l F)
  := adj_triangle_l_p_pseudo F.2.

Definition adj_triangle_r
           `{Funext}
           {C D : BiCategory}
           (F : BiAdjunction C D)
  : modification
      (triangle_r_lhs F.1)
      (identity_transformation (right_adjoint F))
  := adj_triangle_r_p F.2.

Global Instance adj_triangle_r_pseudo
       `{Funext}
       {C D : BiCategory}
       (F : BiAdjunction C D)
  : is_pseudo_modification (adj_triangle_r F)
  := adj_triangle_r_p_pseudo F.2.

Section Restriction.
  Context `{Funext}
          {C D : BiCategory}.
  Variable (adj : BiAdjunction C D)
           (P : C -> hProp)
           (HP : forall (x : D), P(right_adjoint adj x)).

  Definition restriction_left_adjoint := lax_restriction (left_adjoint adj) P.

  Definition restriction_right_adjoint := lax_factor (right_adjoint adj) P HP.

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
    : LaxTransformation
        (lax_id_functor (full_sub C P))
        (lax_comp restriction_right_adjoint restriction_left_adjoint)
    := Build_LaxTransformation restriction_unit_d is_lax_restriction_unit_d.

  Global Instance restriction_unit_is_pseudo
    : is_pseudo_transformation restriction_unit.
  Proof.
    split.
    intros [X PX] [Y PY] f ; cbn in *.
    apply adj.
  Qed.

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
    : LaxTransformation
        (lax_comp restriction_left_adjoint restriction_right_adjoint)
        (lax_id_functor D)
    := Build_LaxTransformation restriction_counit_d is_lax_restriction_counit_d.

  Global Instance restriction_counit_is_pseudo
    : is_pseudo_transformation restriction_counit.
  Proof.
    split.
    intros X Y f ; cbn in *.
    apply adj.
  Qed.

  Definition restrict_adjunction_d : BiAdjunction_d (full_sub C P) D
    := Build_BiAdjunction_d
         restriction_left_adjoint
         _
         restriction_right_adjoint
         _
         restriction_unit
         restriction_counit.

  Definition restriction_triangle_l_d
    : modification_d
        (triangle_l_lhs restrict_adjunction_d)
        (identity_transformation (left_adjoint_d restrict_adjunction_d))
    := fun X => mod_component (adj_triangle_l adj) X.1.

  Definition restrict_triangle_l_lhs
             {X Y : full_sub C P}
             (f : Hom (full_sub C P) X Y)
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
    : modification
        (triangle_l_lhs restrict_adjunction_d)
        (identity_transformation (left_adjoint_d restrict_adjunction_d))
    := Build_Modification restriction_triangle_l_d restriction_triangle_l_is_mod.

  Global Instance restriction_triangle_l_pseudo
    : is_pseudo_modification restriction_triangle_l.
  Proof.
    split.
    intros [X PX] ; cbn in *.
    apply adj_triangle_l_pseudo.
  Qed.

  Definition restriction_triangle_r_d
    : modification_d
        (triangle_r_lhs restrict_adjunction_d)
        (identity_transformation (right_adjoint_d restrict_adjunction_d))
    := fun X => mod_component (adj_triangle_r adj) X.

  Definition restriction_triangle_r_lhs
             {X Y : D}
             (f : Hom D X Y)
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
    : modification
        (triangle_r_lhs restrict_adjunction_d)
        (identity_transformation (right_adjoint_d restrict_adjunction_d))
    := Build_Modification restriction_triangle_r_d restriction_triangle_r_is_mod.

  Global Instance restriction_triangle_r_pseudo
    : is_pseudo_modification restriction_triangle_r.
  Proof.
    split.
    intros X ; cbn in *.
    apply adj_triangle_r_pseudo.
  Qed.

  Definition restrict_adjunction : BiAdjunction (full_sub C P) D.
  Proof.
    simple refine (Build_BiAdjunction restrict_adjunction_d _).
    make_is_biadjunction.
  Defined.
End Restriction.
