Require Import HoTT.
Require Import GR.bicategories.bicategories.
Require Import GR.bicategories.lax_functors.
Require Import GR.bicategories.lax_transformations.
Require Import GR.bicategories.modifications.

Record BiAdjunction_d
       `{Univalence}
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
       `{Univalence}
       {C D : BiCategory}
       (F : BiAdjunction_d C D)
  : is_pseudo (left_adjoint_d F).
Proof.
  apply left_adjoint_pseudo_d.
Defined.

Global Instance right_adjoint_pseudo_functor
       `{Univalence}
       {C D : BiCategory}
       (F : BiAdjunction_d C D)
  : is_pseudo (right_adjoint_d F).
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
          (whisker_L (left_adjoint_d F) (unit_d F))
          (compose
             (lax_associativity_inv _ _ _)
             (compose
                (whisker_R (left_adjoint_d F) (counit_d F))
                (lax_left_identity (left_adjoint_d F))
             )
          )
       ).

(*
Definition laxnaturality_of_triangle_l_lhs
           `{Univalence}
           {C D : BiCategory}
           (F : BiAdjunction_d C D)
           {X Y : C}
           (f : C⟦X,Y⟧)
  : laxnaturality_of (triangle_l_lhs F) f
    =
    (assoc_inv _ _ _)
      ∘ (_ ◅ (left_unit_inv _ ∘ right_unit _))
      ∘ assoc _ _ _
      ∘ ((assoc_inv _ _ _)
           ∘ _ ◅ ((Fcomp₁_inv _ _ _)
                    ∘ (_ ₂ (laxnaturality_of (unit_d F) f))
                    ∘ Fcomp₁ _ _ _)
           ∘ assoc _ _ _
           ∘ ((assoc_inv _ _ _)
                ∘ _ ◅ (left_unit_inv _ ∘ right_unit _)
                ∘ assoc _ _ _
                ∘ ((assoc_inv _ _ _)
                     ∘ _ ◅ (laxnaturality_of (counit_d F) _)
                     ∘ assoc _ _ _
                     ∘ (left_unit_inv _ ∘ right_unit _) ▻ _
                     ∘ assoc_inv _ _ _) ▻ _
                ∘ assoc_inv _ _ _) ▻ _
           ∘ assoc_inv _ _ _) ▻ _
      ∘ assoc_inv _ _ _.
Proof.
  reflexivity.
Qed.
*)

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

(*
Definition laxnaturality_of_triangle_r_lhs
           `{Univalence}
           {C D : BiCategory}
           (F : BiAdjunction_d C D)
           {X Y : D}
           (f : D⟦X,Y⟧)
  : laxnaturality_of (triangle_r_lhs F) f = ?
 *)
Record is_biadjunction
       `{Univalence}
       {C D : BiCategory}
       (F : BiAdjunction_d C D)
  := Build_is_biadjunction
       {
         unit_pseudo_p : is_pseudo_transformation (unit_d F) ;
         counit_pseudo_p : is_pseudo_transformation (counit_d F) ;
         adj_triangle_l_p :
           IsoModification
             (triangle_l_lhs F)
             (identity_transformation (left_adjoint_d F)) ;
         adj_triangle_r_p :
           IsoModification
             (triangle_r_lhs F)
             (identity_transformation (right_adjoint_d F))
       }.

Arguments Build_is_biadjunction {_ C D F} _ _ _ _.
Ltac make_is_biadjunction := simple refine (Build_is_biadjunction _ _ _ _).
Arguments unit_pseudo_p {_ C D F} _.
Arguments counit_pseudo_p {_ C D F} _.
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
  : LaxFunctor C D
  := left_adjoint_d F.1.

Global Instance left_adjoint_pseudo
       `{Univalence}
       {C D : BiCategory}
       (F : BiAdjunction C D)
  : is_pseudo (left_adjoint F)
  := _.

Definition right_adjoint
           `{Univalence}
           {C D : BiCategory}
           (F : BiAdjunction C D)
  : LaxFunctor D C
  := right_adjoint_d F.1.

Global Instance right_adjoint_pseudo
       `{Univalence}
       {C D : BiCategory}
       (F : BiAdjunction C D)
  : is_pseudo (right_adjoint F)
  := _.

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
  : IsoModification
      (triangle_l_lhs F.1)
      (identity_transformation (left_adjoint F))
  := adj_triangle_l_p F.2.

Definition adj_triangle_r
           `{Univalence}
           {C D : BiCategory}
           (F : BiAdjunction C D)
  : IsoModification
      (triangle_r_lhs F.1)
      (identity_transformation (right_adjoint F))
  := adj_triangle_r_p F.2.

Definition is_biequivalence
           `{Univalence}
           {C D : BiCategory}
           (F : BiAdjunction C D)
  : Type
  := (@is_adjoint_equivalence (Lax C C)
                              (lax_id_functor C).1
                              (lax_comp (right_adjoint F) (left_adjoint F))
                              (unit F))
     *
     (@is_adjoint_equivalence (Lax D D)
                              (lax_comp (left_adjoint F) (right_adjoint F))
                              (lax_id_functor D).1
                              (counit F)).

Ltac make_is_biequivalence := split.

Definition BiEquivalence
       `{Univalence}
       (C D : BiCategory)
  := {F : BiAdjunction C D & is_biequivalence F}.

Ltac make_biequivalence := simple refine (_;_).