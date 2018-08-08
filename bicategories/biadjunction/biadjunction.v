Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories.bicategory Require Import
     bicategory
     equivalence
     examples.full_sub.
Require Import GR.bicategories.lax_functor.lax_functor.
Require Import GR.bicategories.lax_functor.examples.restriction.
Require Import GR.bicategories.lax_functor.examples.factor_full_sub.
Require Import GR.bicategories.lax_functor.examples.identity.
Require Import GR.bicategories.lax_functor.examples.composition.
From GR.bicategories.lax_transformation Require Import
     lax_transformation
     examples.equal_transformation
     examples.whisker_L
     examples.whisker_R
     examples.right_identity
     examples.left_identity
     examples.associativity
     examples.right_identity_inv
     examples.left_identity_inv
     examples.associativity_inv.
Require Import GR.bicategories.lax_transformation.examples.restriction.
Require Import GR.bicategories.lax_transformation.examples.identity.
Require Import GR.bicategories.lax_transformation.examples.composition.
From GR.bicategories Require Import
     modification.modification.

Record BiAdjunction_d
       `{Univalence}
       (C D : BiCategory)
  := Build_BiAdjunction_d
       { left_adjoint_d : LaxFunctor C D ;
         left_adjoint_pseudo_d : is_pseudo_functor left_adjoint_d ;
         right_adjoint_d : LaxFunctor D C ;
         right_adjoint_pseudo_d : is_pseudo_functor right_adjoint_d ;
         unit_d : LaxTransformation
                    (lax_id_functor C)
                    (lax_comp right_adjoint_d left_adjoint_d) ;
         counit_d : LaxTransformation
                    (lax_comp left_adjoint_d right_adjoint_d)
                    (lax_id_functor D) ;
       }.

Arguments Build_BiAdjunction_d {_ C D} _ _ _ _ _ _.
Arguments left_adjoint_d {_ C D}.
Arguments right_adjoint_d {_ C D}.
Arguments unit_d {_ C D}.
Arguments counit_d {_ C D}.

Global Instance left_adjoint_pseudo_functor
       `{Univalence}
       {C D : BiCategory}
       (F : BiAdjunction_d C D)
  : is_pseudo_functor (left_adjoint_d F).
Proof.
  apply left_adjoint_pseudo_d.
Defined.

Global Instance right_adjoint_pseudo_functor
       `{Univalence}
       {C D : BiCategory}
       (F : BiAdjunction_d C D)
  : is_pseudo_functor (right_adjoint_d F).
Proof.
  apply right_adjoint_pseudo_d.
Defined.

Definition triangle_l_lhs
           `{Univalence}
           {C D : BiCategory}
           (F : BiAdjunction_d C D)
  : LaxTransformation (left_adjoint_d F) (left_adjoint_d F)
  := compose
       (lax_right_identity_inv (left_adjoint_d F))
       (compose
          (whisker_R (left_adjoint_d F) (unit_d F))
          (compose
             (lax_associativity_inv _ _ _)
             (compose
                (whisker_L (left_adjoint_d F) (counit_d F))
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
          (whisker_L (right_adjoint_d F) (unit_d F))
          (compose
             (lax_associativity _ _ _)
             (compose
                (whisker_R (right_adjoint_d F) (counit_d F))
                (lax_right_identity (right_adjoint_d F))
             )
          )
       ).
       
Definition is_biadjunction
           `{Univalence}
           {C D : BiCategory}
           (F : BiAdjunction_d C D)
  : Type.
Proof.
  refine (_ * _).
  - exact {m : modification
                  (triangle_l_lhs F)
                  (identity_transformation (left_adjoint_d F))
               & is_pseudo_modification m}.
  - exact {m : modification
                 (triangle_r_lhs F)
                 (identity_transformation (right_adjoint_d F))
               & is_pseudo_modification m}.
Defined.

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
  := left_adjoint_d F.1.

Global Instance left_adjoint_pseudo
       `{Univalence}
       {C D : BiCategory}
       (F : BiAdjunction C D)
  : is_pseudo_functor (left_adjoint F)
  := left_adjoint_pseudo_d _ _ F.1.

Definition right_adjoint
           `{Univalence}
           {C D : BiCategory}
           (F : BiAdjunction C D)
  := right_adjoint_d F.1.

Global Instance right_adjoint_pseudo
       `{Univalence}
       {C D : BiCategory}
       (F : BiAdjunction C D)
  : is_pseudo_functor (right_adjoint F)
  := right_adjoint_pseudo_d _ _ F.1.

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
  := Datatypes.fst F.2.

Definition adj_triangle_r
           `{Univalence}
           {C D : BiCategory}
           (F : BiAdjunction C D)
  := Datatypes.snd F.2.

Section Restriction.
  Context `{Univalence}
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
    simple refine (Build_LaxTransformation_d _ _).
    - intros X ; cbn in *.
      apply (unit adj).
    - intros X Y ; cbn in *.
      simple refine (Build_NaturalTransformation _ _ _ _).
      + intros f.
        apply (laxnaturality_of (unit adj) f).
      + intros f g p.
        apply (commutes (laxnaturality_of (unit adj)) _ _ p).
  Defined.

  Definition is_lax_restriction_unit_d
    : is_lax_transformation restriction_unit_d.
  Proof.
    split.
    - intros X.
      apply (Datatypes.fst (unit adj).2 X.1).
    - intros X Y Z f g.
      cbn in f, g.
      pose (Datatypes.snd (unit adj).2 X.1 Y.1 Z.1 f g) as p.
      cbn in p.
      rewrite p.
      f_ap ; f_ap ; f_ap.
      apply iso_moveL_1V.
      apply Morphisms.iso_moveR_Vp.
      rewrite right_identity.
      reflexivity.
  Qed.

  Definition restriction_unit
    : LaxTransformation
        (lax_id_functor (full_sub C P))
        (lax_comp restriction_right_adjoint restriction_left_adjoint)
    := Build_LaxTransformation restriction_unit_d is_lax_restriction_unit_d.

  Definition restriction_counit_d
    : LaxTransformation_d
        (lax_comp restriction_left_adjoint restriction_right_adjoint)
        (lax_id_functor D).
  Proof.
    simple refine (Build_LaxTransformation_d _ _).
    - intros X ; cbn.
      apply counit_d.
    - intros X Y ; cbn.
      simple refine (Build_NaturalTransformation _ _ _ _).
      + intros f.
        apply (laxnaturality_of (counit adj) f).
      + intros f g p.
        apply (commutes (laxnaturality_of (counit adj)) _ _ p).
  Defined.

  Definition is_lax_restriction_counit_d
    : is_lax_transformation restriction_counit_d.
  Proof.
    split.
    - intros X ; cbn.
      apply (Datatypes.fst (counit adj).2 X).
    - intros X Y Z f g.
      pose (Datatypes.snd (counit adj).2 X Y Z f g) as p.
      cbn in p.
      rewrite p.
      reflexivity.
  Qed.

  Definition restriction_counit
    : LaxTransformation
        (lax_comp restriction_left_adjoint restriction_right_adjoint)
        (lax_id_functor D)
    := Build_LaxTransformation restriction_counit_d is_lax_restriction_counit_d.

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
    := fun X => mod_component (Datatypes.fst adj.2).1 X.1.

  Definition restrict_triangle_l_lhs
             {X Y : full_sub C P}
             (f : Hom (full_sub C P) X Y)
    : laxnaturality_of (triangle_l_lhs adj.1) f
      =
      laxnaturality_of (triangle_l_lhs restrict_adjunction_d) f.
  Proof.
  Admitted.

  Definition restriction_triangle_l_is_mod
    : is_modification restriction_triangle_l_d.
  Proof.
    intros X Y f.
    pose (mod_commute (Datatypes.fst (adj.2)).1 X.1 Y.1 f) as p.
    Opaque identity_transformation triangle_l_lhs.
    simpl in *.
    rewrite p ; clear p.
    unfold restriction_left_adjoint, bc_whisker_l.
    rewrite restrict_triangle_l_lhs.
    f_ap.
  Qed.

  Definition restriction_triangle_l
    : modification
        (triangle_l_lhs restrict_adjunction_d)
        (identity_transformation (left_adjoint_d restrict_adjunction_d))
    := Build_Modification restriction_triangle_l_d restriction_triangle_l_is_mod.

  Definition restriction_triangle_r_d
    : modification_d
        (triangle_r_lhs restrict_adjunction_d)
        (identity_transformation (right_adjoint_d restrict_adjunction_d))
    := fun X => mod_component (Datatypes.snd adj.2).1 X.

  Definition restriction_triangle_r_lhs
             {X Y : D}
             (f : Hom D X Y)
    : laxnaturality_of (triangle_r_lhs adj.1) f
      =
      laxnaturality_of (triangle_r_lhs restrict_adjunction_d) f.
  Proof.
    unfold triangle_r_lhs.
    simpl in *.
  Admitted.
  
  Definition restriction_triangle_r_is_mod
    : is_modification restriction_triangle_r_d.
  Proof.
    intros X Y f.
    pose (mod_commute (Datatypes.snd (adj.2)).1 X Y f) as p.
    Opaque identity_transformation triangle_r_lhs.
    simpl in *.
    rewrite p ; clear p.
    rewrite restriction_triangle_r_lhs.
    f_ap.
  Qed.

  Definition restriction_triangle_r
    : modification
        (triangle_r_lhs restrict_adjunction_d)
        (identity_transformation (right_adjoint_d restrict_adjunction_d))
    := Build_Modification restriction_triangle_r_d restriction_triangle_r_is_mod.

  Definition restrict_adjunction : BiAdjunction (full_sub C P) D.
  Proof.
    simple refine (Build_BiAdjunction restrict_adjunction_d _).
    split.
    - exists restriction_triangle_l.
      simple refine {|mc_iso := _|}.
      intros.
      apply (Datatypes.fst adj.2).2.
    - exists restriction_triangle_r.
      simple refine {|mc_iso := _|}.
      intros.
      apply (Datatypes.snd adj.2).2.
  Defined.
End Restriction.