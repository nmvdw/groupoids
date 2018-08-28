Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory
     bicategory.bicategory_laws
     lax_functor.lax_functor
     lax_functor.examples.constant
     lax_transformation.lax_transformation
     lax_transformation.transformation_category.

Definition right_unit_assoc_inv
           {C : BiCategory}
           {X Y Z : C}
           (g : C⟦Y, Z⟧) (f : C⟦X,Y⟧)
  : right_unit (g · f) ∘ assoc_inv g f (id₁ X) = g ◅ right_unit f.
Proof.
  rewrite right_unit_assoc.
  rewrite !vcomp_assoc.
  rewrite assoc_left.
  apply vcomp_right_identity.
Qed.

Definition pseudo_cone
           `{Funext}
           {D C : BiCategory}
           (F : LaxFunctor D C)
           `{is_pseudo _ _ F}
           (Y : C)
  : Type
  := LaxTransformation (lax_constant Y) F.

Section ConeData.
  Context `{Funext}
          {D C : BiCategory}.
  Variable (F : LaxFunctor D C)
           (Y : C).
  Context `{is_pseudo _ _ F}.
  Variable (cone : pseudo_cone F Y).

  Definition maps (X : D) : C⟦Y, F X⟧
    := laxcomponent_of cone X.

  Definition commutes {X₁ X₂ : D} (f : D⟦X₁,X₂⟧)
    : (F ₁ f) · maps X₁ ==> maps X₂
    := right_unit (maps X₂) ∘ laxnaturality_of cone f.

  Definition commutes_natural
             {X₁ X₂ : D}
             {f g : D⟦X₁,X₂⟧}
             (α : f ==> g)
    : commutes g ∘ (F ₂ α) * id₂ (maps X₁) = commutes f.
  Proof.
    unfold commutes.
    rewrite !vcomp_assoc.
    f_ap.
    pose (laxnaturality_natural cone α) as p.
    rewrite hcomp_id₂, vcomp_left_identity in p.
    exact p.
  Qed.

  Definition commutes_unit
             (X : D)
    : commutes (id₁ X) ∘ Fid F X * id₂ (maps X) = left_unit (maps X).
  Proof.
    unfold commutes.
    pose (transformation_unit cone X) as p.
    cbn in p.
    rewrite hcomp_id₂, vcomp_left_identity in p.
    rewrite !vcomp_assoc.
    rewrite p ; clear p.
    rewrite <- !vcomp_assoc.
    rewrite right_unit_left.
    apply vcomp_left_identity.
  Qed.

  Definition commutes_assoc
             {X₁ X₂ X₃ : D}
             (g : D⟦X₂,X₃⟧) (f : D⟦X₁,X₂⟧)
    : commutes (g · f) ∘ Fcomp₁ F g f * id₂ (maps X₁)
      =
      (commutes g)
        ∘ (id₂ (F ₁ g) * commutes f)
        ∘ assoc (F ₁ g) (F ₁ f) (maps X₁).
  Proof.
    unfold commutes.
    rewrite !vcomp_assoc.
    rewrite (transformation_assoc cone f g).
    rewrite <- !vcomp_assoc.
    cbn.
    rewrite <- triangle_l.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ (_ ∘ z)) (vcomp_assoc _ _ _)^).
    rewrite assoc_right.
    rewrite vcomp_left_identity.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ z) (vcomp_assoc _ _ _)^).
    rewrite <- interchange.
    rewrite vcomp_left_identity.
    rewrite <- !vcomp_assoc.
    rewrite right_unit_natural.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ (_ ∘ z)) (vcomp_assoc _ _ _)^).
    rewrite right_unit_assoc_inv.
    rewrite !vcomp_assoc.
    rewrite !(ap (fun z => _ ∘ (_ ∘ z)) (vcomp_assoc _ _ _)^).
    rewrite <- interchange.
    rewrite vcomp_left_identity.
    reflexivity.
  Qed.
End ConeData.