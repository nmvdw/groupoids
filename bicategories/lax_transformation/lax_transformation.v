Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory lax_functor.lax_functor general_category.

Definition postcomp
           {C : BiCategory}
           {Y Z : C}
           (f : C⟦Y,Z⟧)
           (X : C)
  : Functor (C⟦X,Y⟧) (C⟦X,Z⟧)
  := hcomp X Y Z o Functor.prod (const_functor f) 1.

Definition precomp
           {C : BiCategory}
           {Y Z : C}
           (f : C⟦Y,Z⟧)
           (X : C)
  : Functor (C⟦Z,X⟧) (C⟦Y,X⟧)
  := hcomp Y Z X o Functor.prod 1 (const_functor f).

Record LaxTransformation_d {C D : BiCategory} (F G : LaxFunctor C D) :=
  Build_LaxTransformation_d
    {
      laxcomponent_of_d :> forall (X : C), D⟦F X,G X⟧ ;
      laxnaturality_of_d :
        forall {X Y : C} (f : C⟦X,Y⟧),
          (G ₁ f) · laxcomponent_of_d X ==> laxcomponent_of_d Y · (F ₁ f)
    }.

Arguments Build_LaxTransformation_d {C D F G} _ _.
Arguments laxcomponent_of_d {C D F G} η X : rename.
Arguments laxnaturality_of_d {C D F G} η {X Y} f : rename.

Ltac make_lax_transformation := simple refine (Build_LaxTransformation_d _ _).

Record is_lax_transformation
       {C D : BiCategory}
       {F G : LaxFunctor C D}
       (η : LaxTransformation_d F G)
  := Build_is_lax_transformation
       {
         laxnaturality_natural_p :
           forall {X Y : C} {f g : C⟦X,Y⟧} (α : f ==> g),
             (laxnaturality_of_d η) g ∘ ((G ₂ α) * id₂ (η X)) =
             id₂ (η Y) * (F ₂ α) ∘ (laxnaturality_of_d η) f ;
         transformation_unit_p : forall (X : C),
             (laxnaturality_of_d η (id₁ X))
               ∘ ((Fid G X) * (id₂ (η X)))
             =
             (id₂ (η X) * (Fid F X))
               ∘ (right_unit_inv (η X))
               ∘ (left_unit (η X)) ;
         transformation_assoc_p :
           forall {X Y Z : C}
                  (f : C⟦X,Y⟧) (g : C⟦Y,Z⟧),
             (laxnaturality_of_d η (g · f))
               ∘ (Fcomp₁ G g f * id₂ _)
             = (id₂ _ * Fcomp₁ F g f)
                 ∘ (assoc (η Z) (F ₁ g) (F ₁ f))
                 ∘ (laxnaturality_of_d η g * id₂ _)
                 ∘ (assoc_inv (G ₁ g) (η Y) (F ₁ f))
                 ∘ (id₂ _ * laxnaturality_of_d η f)
                 ∘ (assoc (G ₁ g) (G ₁ f) (η X))
       }.

Arguments laxnaturality_natural_p {C D F G η} _ {X Y f g} α.
Arguments transformation_unit_p {C D F G η} _ X.
Arguments transformation_assoc_p {C D F G η} _ {X Y Z} f g.
Arguments Build_is_lax_transformation {C D F G η} _ _ _.
Ltac make_is_lax_transformation := simple refine (Build_is_lax_transformation _ _ _).

Definition LaxTransformation {C D : BiCategory} (F G : LaxFunctor C D)
  := {η : LaxTransformation_d F G & is_lax_transformation η}.

Definition Build_LaxTransformation
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           (η : LaxTransformation_d F G)
           (Hη : is_lax_transformation η)
  : LaxTransformation F G
  := (η;Hη).

Definition laxcomponent_of
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           (η : LaxTransformation F G)
  : forall X, D⟦F X,G X⟧
  := laxcomponent_of_d η.1.

Coercion laxcomponent_of : LaxTransformation >-> Funclass.

Definition laxnaturality_of
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           (η : LaxTransformation F G)
           {X Y : C}
           (f : C⟦X,Y⟧)
  : (G ₁ f) · laxcomponent_of η X ==> laxcomponent_of η Y · (F ₁ f)
  := laxnaturality_of_d η.1 f.

Definition laxnaturality_natural
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           (η : LaxTransformation F G)
           {X Y : C}
           {f g : C⟦X,Y⟧}
           (α : f ==> g)
  : (laxnaturality_of η) g ∘ ((G ₂ α) * id₂ (η X)) =
    id₂ (η Y) * (F ₂ α) ∘ (laxnaturality_of η) f
  := laxnaturality_natural_p η.2 α.

Definition laxnaturality_transformation
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           (η : LaxTransformation F G)
           (X Y : C)
  : NaturalTransformation
      (precomp (laxcomponent_of η X) (G Y) (* (σX)^* *)
               o Fmor G X Y)%functor
      (postcomp (laxcomponent_of η Y) (F X) (* (σY)_* *)
                o Fmor F X Y).
Proof.
  simple refine (Build_NaturalTransformation _ _ _ _).
  - intros f ; simpl in *.
    exact (laxnaturality_of η f).
  - intros f g α ; simpl in *.
    exact (laxnaturality_natural η α).
Defined.

Definition transformation_unit
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           (η : LaxTransformation F G)
           (X : C)
  : (laxnaturality_of η (id₁ X))
      ∘ ((Fid G X) * (id₂ (η X)))
    =
    (id₂ (η X) * (Fid F X))
      ∘ (right_unit_inv (η X))
      ∘ (left_unit (η X))
  := transformation_unit_p η.2 X.

Definition transformation_assoc
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           (η : LaxTransformation F G)
           {X Y Z : C}
           (f : C⟦X,Y⟧) (g : C⟦Y,Z⟧)
  : (laxnaturality_of η (g · f))
      ∘ (Fcomp₁ G g f * id₂ _)
    = (id₂ _ * Fcomp₁ F g f)
        ∘ (assoc (η Z) (F ₁ g) (F ₁ f))
        ∘ (laxnaturality_of η g * id₂ _)
        ∘ (assoc_inv (G ₁ g) (η Y) (F ₁ f))
        ∘ (id₂ _ * laxnaturality_of η f)
        ∘ (assoc (G ₁ g) (G ₁ f) (η X))
  := transformation_assoc_p η.2 f g.

Class is_pseudo_transformation
      {C D : BiCategory}
      {F G : LaxFunctor C D}
      (η : LaxTransformation F G)
  := { laxnaturality_of_iso : forall {X Y : C} (f : C⟦X,Y⟧),
         IsIsomorphism (laxnaturality_of η f)
     }.

Global Instance laxnaturality_of_is_iso
       {C D : BiCategory}
       {F G : LaxFunctor C D}
       (η : LaxTransformation F G)
       {X Y : C}
       (f : C⟦X,Y⟧)
       `{is_pseudo_transformation _ _ _ _ η}
  : IsIsomorphism (laxnaturality_of η f)
  := laxnaturality_of_iso f.

Global Instance laxnaturality_transformationis_iso
       `{Univalence}
       {C D : BiCategory}
       {F G : LaxFunctor C D}
       (η : LaxTransformation F G)
       (X Y : C)
       `{is_pseudo_transformation _ _ _ _ η}
  : @IsIsomorphism (_ -> _) _ _ (laxnaturality_transformation η X Y).
Proof.
  apply isisomorphism_natural_transformation.
  apply _.
Defined.

Record PseudoTransformation_d
       {C D : BiCategory}
       (F G : LaxFunctor C D)
  := Build_PseudoTransformation_d
       { laxcomponent_of_pd :> forall (X : C), D⟦F X,G X⟧ ;
         laxnaturality_of_pd : forall {X Y : C} (f : C⟦X,Y⟧),
             (G ₁ f) · laxcomponent_of_pd X ==> laxcomponent_of_pd Y · (F ₁ f) ;
         laxnaturality_of_inv_pd : forall {X Y : C} (f : C⟦X,Y⟧),
             laxcomponent_of_pd Y · (F ₁ f) ==> (G ₁ f) · laxcomponent_of_pd X ;
       }.

Arguments Build_PseudoTransformation_d {C D F G} _ _ _.
Ltac make_pseudo_transformation := simple refine (Build_PseudoTransformation_d _ _ _).
Arguments laxcomponent_of_pd {C D F G} _ X.
Arguments laxnaturality_of_pd {C D F G} _ {X Y} f.
Arguments laxnaturality_of_inv_pd {C D F G} _ {X Y} f.

Record is_pseudo_transformation_p
       {C D : BiCategory}
       {F G : LaxFunctor C D}
       (η : PseudoTransformation_d F G)
  := Build_is_pseudo_transformation_p
       {
         laxnaturality_natural_pp :
           forall {X Y : C} {f g : C⟦X,Y⟧} (α : f ==> g),
             (laxnaturality_of_pd η) g ∘ ((G ₂ α) * id₂ (η X)) =
             id₂ (η Y) * (F ₂ α) ∘ (laxnaturality_of_pd η) f ;
         transformation_unit_pp : forall (X : C),
             (laxnaturality_of_pd η (id₁ X))
               ∘ ((Fid G X) * (id₂ (η X)))
             =
             (id₂ (η X) * (Fid F X))
               ∘ (right_unit_inv (η X))
               ∘ (left_unit (η X)) ;
         transformation_assoc_pp :
           forall {X Y Z : C}
                  (f : C⟦X,Y⟧) (g : C⟦Y,Z⟧),
             (laxnaturality_of_pd η (g · f))
               ∘ (Fcomp₁ G g f * id₂ _)
             = (id₂ _ * Fcomp₁ F g f)
                 ∘ (assoc (η Z) (F ₁ g) (F ₁ f))
                 ∘ (laxnaturality_of_pd η g * id₂ _)
                 ∘ (assoc_inv (G ₁ g) (η Y) (F ₁ f))
                 ∘ (id₂ _ * laxnaturality_of_pd η f)
                 ∘ (assoc (G ₁ g) (G ₁ f) (η X)) ;
         laxnaturality_left_p :
           forall {X Y : C} (f : C⟦X,Y⟧),
             laxnaturality_of_pd η f ∘ laxnaturality_of_inv_pd η f
             =
             id₂ (η Y · (F ₁ f)) ;
         laxnaturality_right_p :
           forall {X Y : C} (f : C⟦X,Y⟧),
             laxnaturality_of_inv_pd η f ∘ laxnaturality_of_pd η f
             =
             id₂ ((G ₁ f) · η X)
       }.

Arguments Build_is_pseudo_transformation_p {C D F G η} _ _ _ _ _.
Ltac make_is_pseudo_transformation := simple refine (Build_is_pseudo_transformation_p _ _ _ _ _).

Definition Build_PseudoTransformation
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           (η : PseudoTransformation_d F G)
           (Hη : is_pseudo_transformation_p η)
  : LaxTransformation F G.
Proof.
  simple refine (Build_LaxTransformation _ _).
  - make_lax_transformation.
    + exact (laxcomponent_of_pd η).
    + intros X Y f.
      exact (laxnaturality_of_pd η f).
  - make_is_lax_transformation ; apply Hη. 
Defined.

Global Instance Build_Pseudo_is_pseudo
       {C D : BiCategory}
       {F G : LaxFunctor C D}
       (η : PseudoTransformation_d F G)
       (Hη : is_pseudo_transformation_p η)
  : is_pseudo_transformation (Build_PseudoTransformation η Hη).
Proof.
  split.
  intros X Y f.
  simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
  - exact (laxnaturality_of_inv_pd η f).
  - apply Hη.
  - apply Hη.
Defined.