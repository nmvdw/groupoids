Require Import HoTT.
From HoTT.Categories Require Import
     Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
     lax_functor.lax_functor.

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

Definition LaxTransformation_d
           {C D : BiCategory}
           (F G : LaxFunctor C D)
  := {η : (forall (X : C), D⟦F X,G X⟧)
          & forall {X Y : C} (f : C⟦X,Y⟧),
          (G ₁ f) · η X ==> η Y · (F ₁ f) }.

Definition laxcomponent_of_d
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           (η : LaxTransformation_d F G)
  : forall (X : C), D⟦F X,G X⟧
  := η.1.

Coercion laxcomponent_of_d : LaxTransformation_d >-> Funclass.

Definition laxnaturality_of_d
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           (η : LaxTransformation_d F G)
  : forall {X Y : C} (f : C⟦X,Y⟧),
    (G ₁ f) · η X ==> η Y · (F ₁ f)
  := η.2.

Definition Build_LaxTransformation_d
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           (laxcomponent : forall (X : C), D⟦F X,G X⟧)
           (laxnaturality :
              forall {X Y : C} (f : C⟦X,Y⟧),
                (G ₁ f) · laxcomponent X ==> laxcomponent Y · (F ₁ f))
  : LaxTransformation_d F G.
Proof.
  exact (laxcomponent;laxnaturality).
Defined.
              
(*
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
*)

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

Global Instance is_hprop_is_lax_transformation
       `{Funext}
       {C D : BiCategory}
       {F G : LaxFunctor C D}
       (η : LaxTransformation_d F G)
  : IsHProp (is_lax_transformation η).
Proof.
  apply hprop_allpath.
  intros [x₁ y₁ z₁] [x₂ y₂ z₂].
  assert (x₁ = x₂) as ->.
  { apply path_ishprop. }
  assert (y₁ = y₂) as ->.
  { apply path_ishprop. }
  assert (z₁ = z₂) as ->.
  { apply path_ishprop. }
  reflexivity.
Qed.

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

Definition laxnaturality_of_build
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           (η : LaxTransformation_d F G)
           (Hη : is_lax_transformation η)
           {X Y : C}
           (f : C⟦X,Y⟧)
  : laxnaturality_of (Build_LaxTransformation η Hη) f = laxnaturality_of_d η f
  := idpath.

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
  := laxnaturality_of_iso : forall {X Y : C} (f : C⟦X,Y⟧),
      IsIsomorphism (laxnaturality_of η f).

Global Instance is_hrop_is_pseudo_transformation
       `{Univalence}
       {C D : BiCategory}
       {F G : LaxFunctor C D}
       (η : LaxTransformation F G)
  : IsHProp (is_pseudo_transformation η).
Proof.
  unfold is_pseudo_transformation.
  apply _.
Qed.

Definition PseudoTransformation
           `{Univalence}
           {C D : BiCategory}
           (F G : LaxFunctor C D)
  : Type
  := {η : LaxTransformation F G & is_pseudo_transformation η}.

Ltac make_pseudo_transformation_lax := simple refine (_;_).

Coercion pseudo_transformation_to_lax_transformation
         `{Univalence}
         {C D : BiCategory}
         {F G : LaxFunctor C D}
         (η : PseudoTransformation F G)
  : LaxTransformation F G
  := η.1.

Global Instance is_pseudo_pseudo_transformation
       `{Univalence}
       {C D : BiCategory}
       {F G : LaxFunctor C D}
       (η : PseudoTransformation F G)
  : is_pseudo_transformation η
  := η.2.

Global Instance laxnaturality_of_is_iso
       {C D : BiCategory}
       {F G : LaxFunctor C D}
       (η : LaxTransformation F G)
       `{is_pseudo_transformation _ _ _ _ η}
       {X Y : C}
       (f : C⟦X,Y⟧)
  : IsIsomorphism (laxnaturality_of η f)
  := laxnaturality_of_iso f.

Global Instance laxnaturality_transformationis_iso
       `{Funext}
       {C D : BiCategory}
       {F G : LaxFunctor C D}
       (η : LaxTransformation F G)
       `{is_pseudo_transformation _ _ _ _ η}
       (X Y : C)
  : @IsIsomorphism (_ -> _) _ _ (laxnaturality_transformation η X Y).
Proof.
  apply isisomorphism_natural_transformation.
  apply _.
Defined.

Definition laxnaturality_of_inv
           `{Univalence}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           (η : PseudoTransformation F G)
           {X Y : C}
           (f : C⟦X,Y⟧)
  : laxcomponent_of η Y · (F ₁ f) ==> (G ₁ f) · laxcomponent_of η X
  := (laxnaturality_of η f)^-1.

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
           `{Univalence}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           (η : PseudoTransformation_d F G)
           (Hη : is_pseudo_transformation_p η)
  : PseudoTransformation F G.
Proof.
  make_pseudo_transformation_lax.
  - simple refine (Build_LaxTransformation _ _).
    + make_lax_transformation.
      * exact (laxcomponent_of_pd η).
      * intros X Y f.
        exact (laxnaturality_of_pd η f).
    + make_is_lax_transformation ; apply Hη.
  - simpl.
    intros X Y f.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    + exact (laxnaturality_of_inv_pd η f).
    + apply Hη.
    + apply Hη.
Defined.

Definition path_laxtransformation_d_raw
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {η₁ η₂ : LaxTransformation_d F G}
           (p_comp : laxcomponent_of_d η₁ = laxcomponent_of_d η₂)
           (p_natural :
              transport
                (fun η : forall X : C, D ⟦ F X, G X ⟧ =>
                   forall (X Y : C)
                          (f : C ⟦ X, Y ⟧),
                     (Fmor G X Y) f · η X ==> η Y · (Fmor F X Y) f)
                p_comp
                η₁.2
              =
              η₂.2)
  : η₁ = η₂
  := path_sigma' _ p_comp p_natural.

Definition path_laxtransformation_d_raw_1
           `{Funext}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           (η : LaxTransformation_d F G)
           p
  : path_laxtransformation_d_raw idpath p = (idpath : η = η).
Proof.
  assert (p = idpath) as ->.
  { apply path_ishprop. }
  reflexivity.
Qed.

Definition ap_laxcomponent_path_laxtransformation_d_raw
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {η₁ η₂ : LaxTransformation_d F G}
           (p_comp : laxcomponent_of_d η₁ = laxcomponent_of_d η₂)
           (p_natural :
              transport
                (fun η : forall X : C, D ⟦ F X, G X ⟧ =>
                   forall (X Y : C)
                          (f : C ⟦ X, Y ⟧),
                     (Fmor G X Y) f · η X ==> η Y · (Fmor F X Y) f)
                p_comp
                η₁.2
              =
              η₂.2)
           (X : C)
  : ap (fun η => laxcomponent_of_d η X)
       (path_laxtransformation_d_raw p_comp p_natural)
    = ap (fun η => η X) p_comp.
Proof.
  rewrite (ap_compose (fun η => η.1) (fun η => η X)).
  unfold laxcomponent_of_d, path_laxtransformation_d_raw, path_sigma', LaxTransformation_d.
  pose @pr1_path_sigma.
  unfold pr1_path, Overture.pr1 in p.
  rewrite p.
  reflexivity.
Qed.

Definition path_laxtransformation_help
           `{Funext}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {η₁ η₂ : LaxTransformation F G}
           (p_comp : laxcomponent_of η₁ = η₂)
           (p_natural :
              forall (A B : C) (f : C⟦A,B⟧),
                (laxnaturality_of η₂ f)
                  ∘ (G ₁ f) ◅ idtoiso _ (ap (fun f => f A) p_comp)
                = (idtoiso _ (ap (fun f => f B) p_comp) ▻ (F ₁ f))
                    ∘ laxnaturality_of η₁ f)
  : η₁ = η₂.
Proof.
  apply path_sigma_hprop.
  simple refine (path_laxtransformation_d_raw _ _).
  - exact p_comp.
  - destruct η₁ as [η₁ ?], η₂ as [η₂ ?] ; cbn in *.
    destruct η₁, η₂ ; cbn in *.
    induction p_comp ; cbn in *.
    funext X Y f.
    pose (p_natural X Y f) as p.
    unfold bc_whisker_l, bc_whisker_r in p.
    rewrite !hcomp_id₂, vcomp_right_identity, vcomp_left_identity in p.
    apply p^.
Defined.

Definition path_laxtransformation_help_1
           `{Funext}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           (η : LaxTransformation F G)
           p
  : path_laxtransformation_help idpath p = (idpath : η = η).
Proof.
  unfold path_laxtransformation_help.
  rewrite path_laxtransformation_d_raw_1.
  apply path_sigma_hprop_1.
Qed.

Definition ap_laxcomponent_path_laxtransformation_help
           `{Funext}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {η₁ η₂ : LaxTransformation F G}
           (p_comp : laxcomponent_of η₁ = η₂)
           (p_natural :
              forall (A B : C) (f : C⟦A,B⟧),
                (laxnaturality_of η₂ f)
                  ∘ (G ₁ f) ◅ idtoiso _ (ap (fun f => f A) p_comp)
                = (idtoiso _ (ap (fun f => f B) p_comp) ▻ (F ₁ f))
                    ∘ laxnaturality_of η₁ f)
           (X : C)
  : ap (fun η => laxcomponent_of η X)
       (path_laxtransformation_help p_comp p_natural)
    = ap (fun η => η X) p_comp.
Proof.
  rewrite (ap_compose (fun η => laxcomponent_of η) (fun η => η X)).
  rewrite (ap_compose (fun η => η.1) (fun η => η.1)).
  unfold laxcomponent_of_d, path_laxtransformation_d_raw, path_sigma', LaxTransformation_d.
  pose @pr1_path_path_sigma_hprop.
  unfold pr1_path, Overture.pr1 in p.
  rewrite p.
  rewrite <- (ap_compose (fun η => laxcomponent_of_d η) (fun η => η X)).
  apply ap_laxcomponent_path_laxtransformation_d_raw.
Qed.

Definition path_laxtransformation
           `{Funext}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {η₁ η₂ : LaxTransformation F G}
           (p_comp : forall (X : C), η₁ X = η₂ X)
           (p_natural :
              forall (A B : C) (f : C⟦A,B⟧),
                (laxnaturality_of η₂ f)
                  ∘ (G ₁ f) ◅ idtoiso _ (p_comp A)
                = (idtoiso _ (p_comp B)) ▻ (F ₁ f)
                    ∘ laxnaturality_of η₁ f)
  : η₁ = η₂.
Proof.
  simple refine (path_laxtransformation_help _ _).
  - funext X.
    exact (p_comp X).
  - intros A B f ; cbn in *.
    rewrite !(@ap_apply_lD C (fun x => D⟦F x,G x⟧)).
    rewrite !apD10_path_forall.
    apply p_natural.
Defined.

Definition path_laxtransformation_help_eq
           `{Funext}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {η₁ η₂ : LaxTransformation F G}
           {p_comp₁ p_comp₂ : laxcomponent_of η₁ = η₂}
           (p_natural :
              forall (A B : C) (f : C⟦A,B⟧),
                (laxnaturality_of η₂ f)
                  ∘ (G ₁ f) ◅ idtoiso _ (ap (fun f => f A) p_comp₁)
                = (idtoiso _ (ap (fun f => f B) p_comp₁) ▻ (F ₁ f))
                    ∘ laxnaturality_of η₁ f)
           (Hp : p_comp₁ = p_comp₂)
  : path_laxtransformation_help p_comp₁ p_natural
    =
    path_laxtransformation_help
      p_comp₂
      (fun A B f => transport (fun z => _) Hp (p_natural A B f)).
Proof.
  induction Hp ; simpl.
  reflexivity.
Defined.

Definition path_laxtransformation_1_help
           `{Funext}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           (η : LaxTransformation F G)
           p
  : path_laxtransformation (fun X => idpath) p = (idpath : η = η).
Proof.
  unfold path_laxtransformation.
  rewrite (path_laxtransformation_help_eq _ (path_forall_1 _)).
  apply path_laxtransformation_help_1.
Qed.

Definition path_laxtransformation_eq
           `{Funext}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {η₁ η₂ : LaxTransformation F G}
           {p_comp₁ p_comp₂ : forall (X : C), η₁ X = η₂ X}
           (p_natural :
              forall (A B : C) (f : C⟦A,B⟧),
                (laxnaturality_of η₂ f)
                  ∘ (G ₁ f) ◅ idtoiso _ (p_comp₁ A)
                = (idtoiso _ (p_comp₁ B)) ▻ (F ₁ f)
                    ∘ laxnaturality_of η₁ f)
           (Hp : p_comp₁ = p_comp₂)
  : path_laxtransformation p_comp₁ p_natural
    =
    path_laxtransformation p_comp₂
                           (fun A B f => transport (fun z => _) Hp (p_natural A B f)).
Proof.
  induction Hp ; simpl.
  reflexivity.
Qed.

Definition path_laxtransformation_1
           `{Funext}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           (η : LaxTransformation F G)
           (p_comp : forall (X : C), η X = η X)
           p
           (q : forall (X : C), p_comp X = idpath)
  : path_laxtransformation (fun X => p_comp X) p = (idpath : η = η).
Proof.
  rewrite (path_laxtransformation_eq _ (path_forall _ _ q)).
  unfold path_laxtransformation.
  apply path_laxtransformation_1_help.
Qed.

Definition ap_laxcomponent_path_laxtransformation
           `{Funext}
           {C D : BiCategory}
           {F G : LaxFunctor C D}
           {η₁ η₂ : LaxTransformation F G}
           (p_comp : forall (X : C), η₁ X = η₂ X)
           (p_natural :
              forall (A B : C) (f : C⟦A,B⟧),
                (laxnaturality_of η₂ f)
                  ∘ (G ₁ f) ◅ idtoiso _ (p_comp A)
                = (idtoiso _ (p_comp B)) ▻ (F ₁ f)
                                         ∘ laxnaturality_of η₁ f)
           (X : C)
  : ap (fun η => laxcomponent_of η X) (path_laxtransformation p_comp p_natural) = p_comp X.
Proof.
  rewrite ap_laxcomponent_path_laxtransformation_help.
  rewrite !(@ap_apply_lD C (fun x => D⟦F x,G x⟧)).
  rewrite !apD10_path_forall.
  reflexivity.
Qed.