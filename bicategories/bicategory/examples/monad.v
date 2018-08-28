Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories.bicategory Require Import
     bicategory
     bicategory_laws
     examples.terminal
     examples.precat
     examples.lax_functors_bicat.
From GR.bicategories.lax_functor Require Import
     lax_functor.
From GR.bicategories.lax_transformation Require Import
     lax_transformation
     examples.identity
     examples.composition.
From GR.bicategories.modification Require Import
     modification
     examples.associativity
     examples.identity
     examples.composition
     examples.left_identity
     examples.right_identity
     examples.whisker_L
     examples.whisker_R.
Require Import GR.bicategories.biadjunction.biadjunction.
Require Import general_category.

Section Monad.
  Context `{Funext}.
  Variable (C : BiCategory).

  Definition monad := Lax terminal_bicategory C.

  Section MonadData.
    Variable (m : monad).
    
    Definition under_m :  C
      := Fobj m tt.

    Definition endo_m : C⟦under_m,under_m⟧
      := m ₁ tt.

    Definition unit : id₁ under_m ==> endo_m
      := Fid m tt.

    Definition bind : endo_m · endo_m ==> endo_m
      := Fcomp₁ m tt tt.

    Definition bind_unit
      : bind ∘ (unit ▻ endo_m) ∘ left_unit_inv endo_m
        =
        id₂ endo_m.
    Proof.
      unfold bind, unit, endo_m, bc_whisker_l ; cbn.
      rewrite <- left_unit_left.
      f_ap.
      rewrite left_unit_left.
      rewrite F_left_unit.      
      rewrite Fmor₂_id₂.
      rewrite vcomp_left_identity.
      reflexivity.
    Qed.

    Definition unit_bind
      : bind ∘ (endo_m ◅ unit) ∘ right_unit_inv endo_m
        =
        id₂ endo_m.
    Proof.
      unfold bind, unit, endo_m, bc_whisker_r ; cbn.
      rewrite <- right_unit_left.
      f_ap.
      rewrite right_unit_left.
      rewrite F_right_unit.
      rewrite Fmor₂_id₂.
      rewrite vcomp_left_identity.
      reflexivity.
    Qed.

    Definition bind_bind
      : bind ∘ (bind ▻ endo_m)
        =
        bind ∘ (endo_m ◅ bind) ∘ assoc endo_m endo_m endo_m.
    Proof.
      unfold bind, endo_m, bc_whisker_l, bc_whisker_r ; cbn.
      rewrite F_assoc.
      cbn.
      f_ap.
      rewrite Fmor₂_id₂.
      rewrite vcomp_left_identity.
      reflexivity.
    Qed.
  End MonadData.

  Definition monad_morphism (m₁ m₂ : monad)
    := monad⟦m₁,m₂⟧.

  Section MorphismData.
    Context {m₁ m₂ : monad}.
    Variable (η : monad_morphism m₁ m₂).

    Definition under_mm : C⟦under_m m₁,under_m m₂⟧
      := laxcomponent_of η tt.

    Definition under_mm_natural
      : endo_m m₂ · under_mm ==> under_mm · endo_m m₁
      := laxnaturality_of η tt.

    Definition under_mm_unit
      : under_mm_natural ∘ unit m₂ * id₂ under_mm
        =
        (id₂ under_mm * unit m₁ ∘ right_unit_inv under_mm) ∘ left_unit under_mm
      := transformation_unit η tt.

    Definition under_mm_bind
      : under_mm_natural ∘ bind m₂ * id₂ under_mm
        =
        (id₂ under_mm * bind m₁ ∘ assoc under_mm (endo_m m₁) (endo_m m₁))
          ∘ (under_mm_natural * id₂ (endo_m m₁))
          ∘ assoc_inv (endo_m m₂) under_mm (endo_m m₁)
          ∘ (id₂ (endo_m m₂) * under_mm_natural)
          ∘ assoc (endo_m m₂) (endo_m m₂) under_mm
      := transformation_assoc η tt tt.
  End MorphismData.

  Definition monad_transformation {m₁ m₂ : monad} (η₁ η₂ : monad_morphism m₁ m₂)
    := η₁ ==> η₂.

  Section TransformationData.
    Context {m₁ m₂ : monad}
            {η₁ η₂ : monad_morphism m₁ m₂}.
    Variable (σ : monad_transformation η₁ η₂).

    Definition under_mmm : under_mm η₁ ==> under_mm η₂
      := mod_component σ tt.

    Definition under_mmm_natural
      : under_mm_natural η₂ ∘ (endo_m m₂ ◅ under_mmm)
        =
        (under_mmm ▻ endo_m m₁) ∘ under_mm_natural η₁
      := mod_commute σ tt.
  End TransformationData.  
End Monad.

Definition id_monad_d
           {C : BiCategory}
           (X : C)
  : LaxFunctor_d terminal_bicategory C.
Proof.
  make_laxfunctor.
  - exact (fun _ => X).
  - intros ; cbn.
    simple refine (Build_Functor _ _ _ _ _ _).
    * exact (fun _ => id₁ X).
    * exact (fun _ _ _ => id₂ (id₁ X)).
    * intros ; cbn.
      rewrite right_identity.
      reflexivity.
    * reflexivity.
  - intros ; cbn.
    exact (left_unit (id₁ X)).
  - intros ; cbn.
    exact (id₂ (id₁ X)).
Defined.

Definition id_monad_is_lax
           `{Funext}
           {C : BiCategory}
           (X : C)
  : is_lax (id_monad_d X).
Proof.
  make_is_lax ; intros ; cbn.
  - apply left_unit_natural.
  - rewrite hcomp_id₂, vcomp_left_identity, vcomp_right_identity.
    reflexivity.
  - rewrite hcomp_id₂, vcomp_left_identity, vcomp_right_identity.
    apply left_unit_is_right_unit.
  - rewrite vcomp_left_identity, <- triangle_l.
    rewrite !vcomp_assoc.
    rewrite assoc_right, vcomp_right_identity, left_unit_is_right_unit.
    reflexivity.
Qed.

Definition id_monad
           `{Funext}
           {C : BiCategory}
           (X : C)
  : monad C
  := Build_LaxFunctor (id_monad_d X) (id_monad_is_lax X).

Definition id_monad_transformation_d
           `{Funext}
           {C : BiCategory}
           {X Y : C}
           (f : C⟦X,Y⟧)
  : LaxTransformation_d (id_monad X) (id_monad Y).
Proof.
  make_lax_transformation ; intros ; cbn.
  - exact f.
  - exact (right_unit_inv f ∘ left_unit f).
Defined.

Definition id_monad_transformation_is_lax
           `{Funext}
           {C : BiCategory}
           {X Y : C}
           (f : C⟦X,Y⟧)
  : is_lax_transformation (id_monad_transformation_d f).
Proof.
  make_is_lax_transformation.
  - intros ; cbn.
    rewrite !vcomp_assoc.
    rewrite left_unit_natural.
    rewrite <- !vcomp_assoc.
    rewrite right_unit_inv_natural.
    reflexivity.
  - intros ; cbn.
    rewrite !vcomp_assoc.
    rewrite left_unit_natural.
    rewrite <- !vcomp_assoc.
    rewrite right_unit_inv_natural.
    reflexivity.
  - intros ; cbn.
    rewrite <- (vcomp_left_identity (id₂ (id₁ Y))).
    rewrite interchange.
    rewrite !vcomp_assoc.
    rewrite <- triangle_r.
    rewrite <- !vcomp_assoc.
    rewrite <- triangle_r.
    rewrite !vcomp_assoc.
    rewrite <- (vcomp_left_identity (id₂ (id₁ X))).
    rewrite interchange, !vcomp_left_identity.
    rewrite <- !vcomp_assoc.
    rewrite <- interchange.
    rewrite right_unit_left.
    rewrite vcomp_left_identity, hcomp_id₂, vcomp_left_identity.
    rewrite left_unit_is_right_unit.
    f_ap.
    rewrite !vcomp_assoc.
    rewrite <- right_unit_inv_assoc.
    rewrite <- right_unit_inv_natural.
    reflexivity.
Qed.

Definition id_monad_transformation
           `{Funext}
           {C : BiCategory}
           {X Y : C}
           (f : C⟦X,Y⟧)
  : LaxTransformation (id_monad X) (id_monad Y)
  := Build_LaxTransformation (id_monad_transformation_d f) (id_monad_transformation_is_lax f).

Definition id_monad_modification_d
           `{Funext}
           {C : BiCategory}
           {X Y : C}
           {f g : C⟦X,Y⟧}
           (α : f ==> g)
  : modification_d (id_monad_transformation f) (id_monad_transformation g)
  := fun _ => α.

Definition id_monad_modification_is_modification
           `{Funext}
           {C : BiCategory}
           {X Y : C}
           {f g : C⟦X,Y⟧}
           (α : f ==> g)
  : is_modification (id_monad_modification_d α).
Proof.
  intros [ ] [ ] [ ] ; cbn.
  unfold bc_whisker_l, bc_whisker_r, id_monad_modification_d.
  rewrite !vcomp_assoc.
  rewrite left_unit_natural.
  rewrite <- !vcomp_assoc.
  rewrite right_unit_inv_natural.
  reflexivity.
Qed.

Definition id_monad_modification
           `{Funext}
           {C : BiCategory}
           {X Y : C}
           {f g : C⟦X,Y⟧}
           (α : f ==> g)
  : modification (id_monad_transformation f) (id_monad_transformation g)
  := Build_Modification (id_monad_modification_d α)
                        (id_monad_modification_is_modification α).

Definition id_transformation_compose_d
           `{Funext}
           {C : BiCategory}
           {X Y Z : C}
           (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
  : modification_d
      (compose (id_monad_transformation f) (id_monad_transformation g))
      (id_monad_transformation (g · f))
  := fun _ => id₂ _.

Definition id_transformation_compose_is_modifcation
           `{Funext}
           {C : BiCategory}
           {X Y Z : C}
           (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
  : is_modification (id_transformation_compose_d g f).
Proof.
  intros [ ] [ ] [ ] ; cbn.
  unfold bc_whisker_l, bc_whisker_r, id_transformation_compose_d.
  rewrite !hcomp_id₂.
  rewrite vcomp_left_identity, vcomp_right_identity.
  rewrite <- (vcomp_left_identity (id₂ g)), <- (vcomp_left_identity (id₂ f)).
  rewrite !interchange.
  rewrite !vcomp_assoc.
  rewrite !(ap (fun z => _ ∘ (_ ∘ z)) (vcomp_assoc _ _ _)^).
  rewrite <- triangle_r.
  rewrite <- interchange.
  rewrite right_unit_left.
  rewrite vcomp_left_identity, hcomp_id₂, vcomp_left_identity.
  rewrite <- !vcomp_assoc.
  rewrite right_unit_inv_assoc.
  rewrite !vcomp_assoc.
  repeat f_ap.
  pose @left_unit_assoc as p.
  unfold bc_whisker_l in p.
  rewrite p.
  rewrite !vcomp_assoc.
  rewrite assoc_left, vcomp_right_identity.
  reflexivity.
Qed.

Definition id_transformation_compose
           `{Funext}
           {C : BiCategory}
           {X Y Z : C}
           (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
  : modification
      (compose (id_monad_transformation f) (id_monad_transformation g))
      (id_monad_transformation (g · f))
  := Build_Modification (id_transformation_compose_d g f)
                        (id_transformation_compose_is_modifcation g f).

Definition id_monad_transformation_id_d
           `{Funext}
           {C : BiCategory}
           (X : C)
  : modification_d (identity_transformation (id_monad X))
                   (id_monad_transformation (id₁ X))
  := fun _ => id₂ (id₁ X).

Definition id_monad_transformation_id_is_modification
           `{Funext}
           {C : BiCategory}
           (X : C)
  : is_modification (id_monad_transformation_id_d X).
Proof.
  intros [ ] [ ] [ ] ; cbn.
  unfold bc_whisker_l, bc_whisker_r.
  rewrite !hcomp_id₂.
  rewrite vcomp_right_identity, vcomp_left_identity.
  rewrite left_unit_is_right_unit, left_unit_inv_is_right_unit_inv.
  reflexivity.
Qed.

Definition id_monad_transformation_id
           `{Funext}
           {C : BiCategory}
           (X : C)
  : modification (identity_transformation (id_monad X))
                 (id_monad_transformation (id₁ X))
  := Build_Modification (id_monad_transformation_id_d X)
                        (id_monad_transformation_id_is_modification X).

Definition id_transformation_compose_inv_d
           `{Funext}
           {C : BiCategory}
           {X Y Z : C}
           (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
  : modification_d
      (id_monad_transformation (g · f))
      (compose (id_monad_transformation f) (id_monad_transformation g))
  := fun _ => id₂ _.

Definition id_transformation_compose_inv_is_modifcation
           `{Funext}
           {C : BiCategory}
           {X Y Z : C}
           (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
  : is_modification (id_transformation_compose_inv_d g f).
Proof.
  intros [ ] [ ] [ ] ; cbn.
  unfold bc_whisker_l, bc_whisker_r, id_transformation_compose_d.
  rewrite !hcomp_id₂.
  rewrite vcomp_left_identity, vcomp_right_identity.
  rewrite <- (vcomp_left_identity (id₂ g)), <- (vcomp_left_identity (id₂ f)).
  rewrite !interchange.
  rewrite !vcomp_assoc.
  rewrite !(ap (fun z => _ ∘ (_ ∘ z)) (vcomp_assoc _ _ _)^).
  rewrite <- triangle_r.
  rewrite <- interchange.
  rewrite right_unit_left.
  rewrite vcomp_left_identity, hcomp_id₂, vcomp_left_identity.
  rewrite <- !vcomp_assoc.
  rewrite right_unit_inv_assoc.
  rewrite !vcomp_assoc.
  repeat f_ap.
  pose @left_unit_assoc as p.
  unfold bc_whisker_l in p.
  rewrite p.
  rewrite !vcomp_assoc.
  rewrite assoc_left, vcomp_right_identity.
  reflexivity.
Qed.

Definition id_transformation_compose_inv
           `{Funext}
           {C : BiCategory}
           {X Y Z : C}
           (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
  : modification
      (id_monad_transformation (g · f))
      (compose (id_monad_transformation f) (id_monad_transformation g))
  := Build_Modification (id_transformation_compose_inv_d g f)
                        (id_transformation_compose_inv_is_modifcation g f).

Definition id_monad_transformation_id_inv_d
           `{Funext}
           {C : BiCategory}
           (X : C)
  : modification_d (id_monad_transformation (id₁ X))
                   (identity_transformation (id_monad X))
  := fun _ => id₂ (id₁ X).

Definition id_monad_transformation_id_inv_is_modification
           `{Funext}
           {C : BiCategory}
           (X : C)
  : is_modification (id_monad_transformation_id_inv_d X).
Proof.
  intros [ ] [ ] [ ] ; cbn.
  unfold bc_whisker_l, bc_whisker_r.
  rewrite !hcomp_id₂.
  rewrite vcomp_right_identity, vcomp_left_identity.
  rewrite left_unit_is_right_unit, left_unit_inv_is_right_unit_inv.
  reflexivity.
Qed.

Definition id_monad_transformation_id_inv
           `{Funext}
           {C : BiCategory}
           (X : C)
  : modification (id_monad_transformation (id₁ X))
                 (identity_transformation (id_monad X))
  := Build_Modification (id_monad_transformation_id_inv_d X)
                        (id_monad_transformation_id_inv_is_modification X).

Definition inclusion_d
           `{Funext}
           (C : BiCategory)
  : PseudoFunctor_d C (monad C).
Proof.
  make_pseudo_functor.
  - exact id_monad.
  - exact (fun _ _ => id_monad_transformation).
  - exact (fun _ _ _ _ => id_monad_modification).
  - exact (fun _ _ _ => id_transformation_compose).
  - exact id_monad_transformation_id.
  - exact (fun _ _ _ => id_transformation_compose_inv).
  - exact id_monad_transformation_id_inv.
Defined.

Definition inclusion_is_pseudo
           `{Funext}
           (C : BiCategory)
  : is_pseudo_functor_p (inclusion_d C).
Proof.
  make_is_pseudo ; intros ; cbn.
  - apply path_modification.
    funext x.
    reflexivity.
  - apply path_modification.
    funext x.
    reflexivity.
  - apply path_modification.
    funext x ; cbn.
    unfold comp_modification, comp_modification_d ; cbn.
    unfold id_transformation_compose_d, whisker_R_mod_d, whisker_L_mod_d ; cbn.
    unfold bc_whisker_l, bc_whisker_r, id_monad_modification_d.
    rewrite <- interchange.
    rewrite !vcomp_left_identity, !vcomp_right_identity.
    reflexivity.
  - apply path_modification.
    funext x ; cbn.
    unfold right_identity_mod_d.
    unfold comp_modification, comp_modification_d ; cbn.
    unfold id_transformation_compose_d, whisker_R_mod_d, whisker_L_mod_d ; cbn.
    unfold bc_whisker_l, bc_whisker_r, id_modification_d, id_monad_transformation_id_d.
    rewrite !hcomp_id₂.
    rewrite !vcomp_right_identity.
    reflexivity.
  - apply path_modification.
    funext x ; cbn.
    unfold left_identity_mod_d.
    unfold comp_modification, comp_modification_d ; cbn.
    unfold id_transformation_compose_d, whisker_R_mod_d, whisker_L_mod_d ; cbn.
    unfold bc_whisker_l, bc_whisker_r, id_modification_d, id_monad_transformation_id_d.
    rewrite !hcomp_id₂.
    rewrite !vcomp_right_identity.
    reflexivity.
  - apply path_modification.
    funext x ; cbn.
    unfold comp_modification, comp_modification_d ; cbn.
    unfold id_transformation_compose_d, whisker_R_mod_d, whisker_L_mod_d ; cbn.
    unfold bc_whisker_l, bc_whisker_r, id_modification_d, id_monad_transformation_id_d.
    rewrite !hcomp_id₂.    
    rewrite !vcomp_right_identity, !vcomp_left_identity.
    reflexivity.
  - apply path_modification.
    funext x ; cbn.
    unfold comp_modification, comp_modification_d ; cbn.
    unfold id_transformation_compose_inv_d, id_transformation_compose_d, id_modification_d.
    cbn.
    apply vcomp_left_identity.
  - apply path_modification.
    funext x ; cbn.
    unfold comp_modification, comp_modification_d ; cbn.
    unfold id_transformation_compose_inv_d, id_transformation_compose_d, id_modification_d.
    cbn.
    apply vcomp_left_identity.
  - apply path_modification.
    funext x ; cbn.
    unfold comp_modification, comp_modification_d ; cbn.
    unfold id_monad_transformation_id_d, id_monad_transformation_id_inv_d, id_modification_d.
    cbn.
    apply vcomp_left_identity.
  - apply path_modification.
    funext x ; cbn.
    unfold comp_modification, comp_modification_d ; cbn.
    unfold id_monad_transformation_id_d, id_monad_transformation_id_inv_d, id_modification_d.
    cbn.
    apply vcomp_left_identity.
Qed.

Definition inclusion
           `{Funext}
           (C : BiCategory)
  : LaxFunctor C (monad C)
  := Build_PseudoFunctor (inclusion_d C) (inclusion_is_pseudo C).

Global Instance inclusion_is_pseudo_functor
       `{Funext}
       (C : BiCategory)
  : is_pseudo (inclusion C)
  := _.

Definition underlying_d
           `{Funext}
           (C : BiCategory)
  : PseudoFunctor_d (monad C) C.
Proof.
  make_pseudo_functor.
  - exact (under_m C).
  - exact (fun _ _ => under_mm C).
  - exact (fun _ _ _ _ => under_mmm C).
  - exact (fun _ _ _ _ _ => id₂ _).
  - exact (fun _ => id₂ _).
  - exact (fun _ _ _ _ _ => id₂ _).
  - exact (fun _ => id₂ _).
Defined.

Definition underlying_is_pseudo
           `{Funext}
           (C : BiCategory)
  : is_pseudo_functor_p (underlying_d C).
Proof.
  make_is_pseudo ; intros ; cbn.
  - reflexivity.
  - reflexivity.
  - unfold comp_modification_d ; cbn.
    unfold whisker_R_mod_d, whisker_L_mod_d ; cbn.
    unfold bc_whisker_l, bc_whisker_r.
    rewrite <- interchange.
    rewrite !vcomp_left_identity, !vcomp_right_identity.
    reflexivity.
  - rewrite hcomp_id₂, !vcomp_right_identity.
    reflexivity.
  - rewrite hcomp_id₂, !vcomp_right_identity.
    reflexivity.
  - rewrite !hcomp_id₂, !vcomp_right_identity, !vcomp_left_identity.
    reflexivity.
  - rewrite !vcomp_left_identity.
    reflexivity.
  - rewrite !vcomp_left_identity.
    reflexivity.
  - rewrite !vcomp_left_identity.
    reflexivity.
  - rewrite !vcomp_left_identity.
    reflexivity.
Qed.

Definition underlying
           `{Funext}
           (C : BiCategory)
  : LaxFunctor (monad C) C
  := Build_PseudoFunctor (underlying_d C) (underlying_is_pseudo C).

Global Instance underlying_is_pseudo_functor
       `{Funext}
       (C : BiCategory)
  : is_pseudo (underlying C)
  := _.


Definition F_left_unit_help
           {C D : BiCategory}
           (F : LaxFunctor C D)
           {X Y : C}
           (f : C⟦X,Y⟧)
  : (F ₂ (left_unit_inv f)) ∘ left_unit (F ₁ f)
    =
    (Fcomp₁ F (id₁ Y) f)
      ∘ ((Fid F Y) * (id₂ (F ₁ f))).
Proof.
  rewrite F_left_unit.
  rewrite <- !vcomp_assoc.
  rewrite <- Fmor₂_vcomp.
  rewrite left_unit_right.
  rewrite Fmor₂_id₂, vcomp_left_identity.
  reflexivity.
Qed.

Definition F_left_unit_inv_help
           `{Funext}
           {C D : BiCategory}
           (F : LaxFunctor C D)
           {X Y : C}
           (f : C⟦X,Y⟧)
  : (Fcomp₁ F (id₁ Y) f)
      ∘ ((Fid F Y) * (id₂ (F ₁ f)))
      ∘ left_unit_inv (F ₁ f)
    =
    F ₂ (left_unit_inv f).
Proof.
  pose @F_left_unit as p.
  rewrite <- !inverse_of_left_unit.
  rewrite inverse_of.
  refine (_ @ right_identity _ _ _ _).
  refine (Morphisms.iso_moveL_Mp _ _ _) ; simpl.
  rewrite <- !associativity.
  refine (Morphisms.iso_moveR_pM _ _ _) ; simpl.
  unfold vcomp in *.
  rewrite p.
  rewrite left_identity.
  reflexivity.
Qed.

Definition F_right_unit_help
           {C D : BiCategory}
           (F : LaxFunctor C D)
           `{is_pseudo _ _ F}
           {X Y : C}
           (f : C⟦X,Y⟧)
  : (Fcomp₁_inv F f (id₁ X))
      ∘ (F ₂ (right_unit_inv f))
      ∘ (right_unit (F ₁ f))
    =
    (id₂ (F ₁ f)) * (Fid F X).
Proof.
  rewrite F_right_unit.
  rewrite !vcomp_assoc.
  rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
  rewrite <- Fmor₂_vcomp.
  rewrite right_unit_right, Fmor₂_id₂, vcomp_left_identity.
  rewrite <- !vcomp_assoc.
  unfold Fcomp₁_inv, vcomp.
  rewrite left_inverse, left_identity.
  reflexivity.
Qed.  

Definition monad_biadjunction_d
           `{Funext}
           (C : BiCategory)
  : BiAdjunction_d (monad C) C.
Proof.
  make_biadjunction.
  - simple refine (Build_LaxTransformation _ _).
    + make_lax_transformation.
      * intros X ; cbn.
        simple refine (Build_LaxTransformation _ _).
        ** make_lax_transformation.
           *** intros [ ] ; cbn.
               apply id₁.
           *** intros [ ] [ ] [ ] ; cbn.
               apply bc_whisker_r.
               exact (unit _ X).
        ** make_is_lax_transformation.
           *** intros [ ] [ ] [ ] [ ] [ ] ; cbn.
               unfold bc_whisker_r.
               rewrite <- !interchange.
               rewrite Fmor₂_id₂.
               rewrite !vcomp_left_identity, vcomp_right_identity.
               reflexivity.
           *** intros [ ] ; cbn.
               unfold bc_whisker_r.
               rewrite hcomp_id₂, vcomp_right_identity.
               rewrite !vcomp_assoc.
               rewrite <- left_unit_is_right_unit, right_unit_right, vcomp_right_identity.
               reflexivity.
           *** intros [ ] [ ] [ ] [ ] [ ] ; cbn.
               unfold bc_whisker_r.
               rewrite !vcomp_assoc.
               rewrite !(ap (fun z => _ ∘ (_ ∘ (_ ∘ z))) (vcomp_assoc _ _ _)^).
               rewrite assoc_inv_natural.
               rewrite !vcomp_assoc.
               rewrite assoc_right, hcomp_id₂, !vcomp_right_identity.
               rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
               rewrite assoc_natural.
               rewrite <- !vcomp_assoc.
               rewrite <- !interchange.
               rewrite !vcomp_left_identity, !vcomp_right_identity.
               rewrite !vcomp_assoc.
               unfold under_m, unit.
               rewrite <- F_left_unit_help.
               rewrite <- (vcomp_left_identity (id₂ _)).
               rewrite interchange.
               rewrite vcomp_assoc.
               rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
               rewrite <- triangle_r.
               rewrite <- !vcomp_assoc.
               rewrite <- interchange.
               rewrite vcomp_left_identity, left_unit_is_right_unit.
               rewrite <- interchange.
               rewrite !vcomp_right_identity.
               f_ap.
               rewrite <- F_left_unit_inv_help.
               pose bind_unit as p.
               unfold bind, endo_m, unit, bc_whisker_l in p.
               rewrite p.
               rewrite vcomp_left_identity.
               reflexivity.
      *
        rewrite !vcomp_