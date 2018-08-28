Require Import HoTT.
From HoTT.Categories Require Export
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     general_category bicategory.bicategory.

Definition cancel_left
           {C : PreCategory}
           {X Y Z : C}
           {f g : morphism C X Y}
           (h : morphism C Y Z)
           `{IsIsomorphism _ _ _ h}
  : (h o f = h o g)%morphism -> f = g.
Proof.
  intros Hhf.
  refine ((left_identity _ _ _ _)^ @ _ @ left_identity _ _ _ _).
  rewrite <- (@left_inverse _ _ _ h _).
  rewrite !associativity.
  rewrite Hhf.
  reflexivity.
Defined.

Definition cancel_right
           {C : PreCategory}
           {X Y Z : C}
           {f g : morphism C Y Z}
           (h : morphism C X Y)
           `{IsIsomorphism _ _ _ h}
  : (f o h = g o h)%morphism -> f = g.
Proof.
  intros Hfh.
  refine ((right_identity _ _ _ _)^ @ _ @ right_identity _ _ _ _).
  rewrite <- (@right_inverse _ _ _ h _).
  rewrite <- !associativity.
  rewrite Hfh.
  reflexivity.
Defined.

Section laws.
  Context {C : BiCategory}.

  Definition move_assoc_L
             {W X Y Z : C}
             (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧)
             {k : C⟦W,Z⟧}
             (α : k ==> (h · g) · f)
             (β : k ==> h · (g · f))
    : assoc_inv h g f ∘ β = α -> β = assoc h g f ∘ α.
  Proof.
    intros H.
    rewrite <- (vcomp_left_identity β).
    rewrite <- assoc_left.
    rewrite vcomp_assoc.
    apply ap.
    exact H.
  Qed.

  Definition move_assoc_inv_L
             {W X Y Z : C}
             (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧)
             {k : C⟦W,Z⟧}
             (α : k ==> h · (g · f))
             (β : k ==> (h · g) · f)
    : assoc h g f ∘ β = α -> β = assoc_inv h g f ∘ α.
  Proof.
    intros H.
    rewrite <- (vcomp_left_identity β).
    rewrite <- assoc_right.
    rewrite vcomp_assoc.
    apply ap.
    exact H.
  Qed.

  Definition cancel_assoc_L
             {W X Y Z : C}
             (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧)
             {k : C⟦W,Z⟧}
             (α : k ==> (h · g) · f)
             (β : k ==> (h · g) · f)
    : assoc h g f ∘ β = assoc h g f ∘ α -> β = α.
  Proof. apply cancel_left. apply _. Qed.

  Definition cancel_assoc_R
             {W X Y Z : C}
             (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧)
             {k : C⟦W,Z⟧}
             (α : h · (g · f) ==> k)
             (β : h · (g · f) ==> k)
    : β ∘ assoc h g f = α ∘ assoc h g f -> β = α.
  Proof. apply cancel_right. apply _. Qed.

  Definition assoc_hcomp_left
             {V W X Y Z : C}
             (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧) (k : C⟦V, W⟧)
    : assoc h g f * id₂ k ∘ assoc_inv h g f * id₂ k = id₂ ((h · (g · f)) · k).
  Proof.
    rewrite <- interchange.
    rewrite assoc_left, vcomp_left_identity.
    apply hcomp_id₂.
  Qed.

  Definition assoc_hcomp_right
             {V W X Y Z : C}
             (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧) (k : C⟦V, W⟧)
    : assoc_inv h g f * id₂ k ∘ assoc h g f * id₂ k = id₂ (((h · g) · f) · k).
  Proof.
    rewrite <- interchange.
    rewrite assoc_right, vcomp_left_identity.
    apply hcomp_id₂.
  Qed.

  Definition move_assoc_hcomp_L
             {V W X Y Z : C}
             (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧) (k : C⟦V, W⟧)
             {l : C⟦V,Z⟧}
             (α : l ==> ((h · g) · f) · k)
             (β : l ==> (h · (g · f)) · k)
    : (assoc_inv h g f * id₂ k) ∘ β = α -> β = (assoc h g f * id₂ k) ∘ α.
  Proof.
    intros H.
    rewrite <- (vcomp_left_identity β).
    rewrite <- assoc_hcomp_left.
    rewrite vcomp_assoc.
    apply ap.
    exact H.
  Qed.

  Definition move_assoc_inv_hcomp_L
             {V W X Y Z : C}
             (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧) (k : C⟦V, W⟧)
             {l : C⟦V,Z⟧}
             (α : l ==> (h · (g · f)) · k)
             (β : l ==> ((h · g) · f) · k)
    : (assoc h g f * id₂ k) ∘ β = α -> β = (assoc_inv h g f * id₂ k) ∘ α.
  Proof.
    intros H.
    rewrite <- (vcomp_left_identity β).
    rewrite <- assoc_hcomp_right.
    rewrite vcomp_assoc.
    apply ap.
    exact H.
  Qed.

  Definition cancel_assoc_hcomp_L
             {V W X Y Z : C}
             (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧) (k : C⟦V, W⟧)
             {l : C⟦V,Z⟧}
             (α : l ==> ((h · g) · f) · k)
             (β : l ==> ((h · g) · f) · k)
    : (assoc h g f * id₂ k) ∘ β = (assoc h g f * id₂ k) ∘ α -> β = α.
  Proof.
    intros H.
    rewrite <- (vcomp_left_identity α), <- (vcomp_left_identity β).
    rewrite <- !assoc_hcomp_right.
    rewrite !vcomp_assoc.
    rewrite H.
    reflexivity.
  Qed.
  
  Definition cancel_assoc_hcomp_R
             {V W X Y Z : C}
             (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧) (k : C⟦V, W⟧)
             {l : C⟦V,Z⟧}
             (α : (h · (g · f)) · k ==> l)
             (β : (h · (g · f)) · k ==> l)
    : β ∘ assoc h g f * id₂ k  = α ∘ assoc h g f * id₂ k -> β = α.
  Proof.
    intros H.
    rewrite <- (vcomp_right_identity α), <- (vcomp_right_identity β).
    rewrite <- !assoc_hcomp_left.
    rewrite <- !vcomp_assoc.
    rewrite H.
    reflexivity.
  Qed.

  Definition inverse_pentagon
             {V W X Y Z : C}
             (k : C⟦Y,Z⟧) (h : C⟦X,Y⟧)
             (g : C⟦W,X⟧) (f : C⟦V,W⟧)
    : assoc_inv (k · h) g f ∘ assoc_inv k h (g · f)
      =
      assoc_inv k h g * id₂ f ∘ assoc_inv k (h · g) f ∘ id₂ k * assoc_inv h g f.
  Proof.
    unfold vcomp, id₂.
    rewrite <- !inverse_of_assoc.
    rewrite <- !inverse_id.
    rewrite <- !hcomp_inverse.
    rewrite <- !inverse_compose.
    apply path_inverse.
    rewrite <- !associativity.
    apply pentagon.
  Qed.

  Definition inverse_pentagon_2
             {V W X Y Z : C}
             (k : C⟦Y,Z⟧) (h : C⟦X,Y⟧)
             (g : C⟦W,X⟧) (f : C⟦V,W⟧)
    : assoc_inv k h (g · f) ∘ id₂ k * assoc h g f
      =
      assoc (k · h) g f ∘ assoc_inv k h g * id₂ f ∘ assoc_inv k (h · g) f.
  Proof.
    rewrite <- !inverse_of_assoc.
    refine (Morphisms.iso_moveR_Mp _ _ _).
    rewrite <- associativity.
    refine (Morphisms.iso_moveL_pM _ _ _).
    rewrite <- associativity.
    refine (Morphisms.iso_moveL_pM _ _ _).
    simpl.
    symmetry ; apply pentagon.
  Qed.

  Definition inverse_pentagon_3
             {V W X Y Z : C}
             (k : C⟦Y,Z⟧) (h : C⟦X,Y⟧)
             (g : C⟦W,X⟧) (f : C⟦V,W⟧)
    : assoc_inv (k · h) g f ∘ assoc_inv k h (g · f) ∘ id₂ k * assoc h g f
      =
      assoc_inv k h g * id₂ f ∘ assoc_inv k (h · g) f.
  Proof.
    unfold vcomp, id₂.
    refine (Morphisms.iso_moveR_pM _ _ _).
    simpl.
    apply inverse_pentagon.
  Qed.

  Definition inverse_pentagon_4
             {V W X Y Z : C}
             (k : C⟦Y,Z⟧) (h : C⟦X,Y⟧)
             (g : C⟦W,X⟧) (f : C⟦V,W⟧)
    : (assoc k h g * id₂ f) ∘ assoc_inv (k · h) g f
      =
      assoc_inv k (h · g) f ∘ id₂ k * assoc_inv h g f ∘ assoc k h (g · f).
  Proof.
    rewrite <- !inverse_of_assoc.
    refine (Morphisms.iso_moveR_pM _ _ _).
    rewrite !associativity.
    refine (Morphisms.iso_moveL_Mp _ _ _).
    refine (Morphisms.iso_moveL_Mp _ _ _).
    simpl.
    rewrite <- !associativity.
    symmetry ; apply pentagon.
  Qed.

  Definition inverse_pentagon_5
             {V W X Y Z : C}
             (k : C⟦Y,Z⟧) (h : C⟦X,Y⟧)
             (g : C⟦W,X⟧) (f : C⟦V,W⟧)
    : assoc (k · h) g f ∘ (assoc_inv k h g * id₂ f)
      =
      assoc_inv k h (g · f) ∘ (id₂ k * assoc h g f) ∘ assoc k (h · g) f.
  Proof.
    rewrite <- !inverse_of_assoc.
    refine (Morphisms.iso_moveR_pM _ _ _).
    rewrite !associativity.
    refine (Morphisms.iso_moveL_Mp _ _ _).
    simpl.
    rewrite <- !associativity.
    apply pentagon.
  Qed.

  Definition pentagon_2
             {V W X Y Z : C}
             (k : C⟦Y,Z⟧) (h : C⟦X,Y⟧)
             (g : C⟦W,X⟧) (f : C⟦V,W⟧)
    : assoc k (h · g) f ∘ assoc k h g * id₂ f
      =
      id₂ k * assoc_inv h g f ∘ assoc k h (g · f) ∘ assoc (k · h) g f.
  Proof.
    unfold vcomp.
    rewrite <- !inverse_of_assoc.
    rewrite !associativity.
    refine (Morphisms.iso_moveL_Mp _ _ _).
    simpl.
    rewrite <- !associativity.
    symmetry ; apply pentagon.
  Qed.

  Definition triangle_r_inv
             {X Y Z : C}
             (g : C ⟦ Y, Z ⟧) (f : C ⟦ X, Y ⟧)
    : right_unit_inv g * id₂ f
      =
      assoc_inv g (id₁ Y) f ∘ id₂ g * left_unit_inv f.
  Proof.
    unfold vcomp, id₂.
    rewrite <- inverse_of_right_unit, <- inverse_of_left_unit.
    rewrite <- inverse_of_assoc.
    rewrite <- !inverse_id.
    rewrite <- !hcomp_inverse.
    rewrite <- inverse_compose.
    apply path_inverse.
    apply triangle_r.
  Qed.
  
  Definition triangle_l
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : right_unit g * id₂ f ∘ assoc_inv g (id₁ Y) f = id₂ g * left_unit f.
  Proof.
    rewrite triangle_r.
    rewrite vcomp_assoc.
    rewrite assoc_left.
    rewrite vcomp_right_identity.
    reflexivity.
  Qed.

  Definition bc_whisker_r_compose
             {X Y Z : C}
             (f : C⟦X,Y⟧)
             {g₁ g₂ g₃ : C⟦Y,Z⟧}
             (p₁ : g₁ ==> g₂) (p₂ : g₂ ==> g₃)
    : (p₂ ∘ p₁) ▻ f = (p₂ ▻ f) ∘ (p₁ ▻ f).
  Proof.
    rewrite <- interchange.
    rewrite vcomp_left_identity.
    reflexivity.
  Qed.

  Definition bc_whisker_l_compose
             {X Y Z : C}
             {f₁ f₂ f₃ : C⟦X,Y⟧}
             (g : C⟦Y,Z⟧)
             (p₁ : f₁ ==> f₂) (p₂ : f₂ ==> f₃)
    : g ◅ (p₂ ∘ p₁) = (g ◅ p₂) ∘ (g ◅ p₁).
  Proof.
    rewrite <- interchange.
    rewrite vcomp_left_identity.
    reflexivity.
  Qed.

  Definition whisker_l_cancel_id
             {X Y : C}
             {f g : C⟦X,Y⟧}
             (η₁ η₂ : f ==> g)
             (Hη : (id₁ Y) ◅ η₁ = (id₁ Y) ◅ η₂)
    : η₁ = η₂.
  Proof.
    refine ((vcomp_left_identity η₁)^ @ _ @ vcomp_left_identity η₂).
    rewrite <- !left_unit_left.
    rewrite !vcomp_assoc.
    rewrite (left_unit_inv_natural η₁), (left_unit_inv_natural η₂).
    unfold bc_whisker_l in Hη.
    rewrite Hη.
    reflexivity.
  Qed.

  Definition whisker_r_cancel_id
             {X Y : C}
             {f g : C⟦X,Y⟧}
             (η₁ η₂ : f ==> g)
             (Hη : η₁ ▻ (id₁ X) = η₂ ▻ (id₁ X))
    : η₁ = η₂.
  Proof.
    refine ((vcomp_right_identity η₁)^ @ _ @ vcomp_right_identity η₂).
    rewrite <- !right_unit_left.
    rewrite <- !vcomp_assoc.
    rewrite <- (right_unit_natural η₁), <- (right_unit_natural η₂).
    unfold bc_whisker_r in Hη.
    rewrite Hη.
    reflexivity.
  Defined.

  Definition left_unit_assoc
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : (left_unit g) ▻ f = left_unit (g · f) ∘ assoc (id₁ Z) g f.
  Proof.
    apply whisker_l_cancel_id.
    unfold bc_whisker_l, bc_whisker_r.
    rewrite <- (vcomp_left_identity (id₂ (id₁ Z))).
    rewrite interchange.
    apply cancel_assoc_R.
    apply cancel_assoc_hcomp_R.
    rewrite vcomp_left_identity.
    rewrite <- assoc_natural.
    rewrite <- triangle_l.
    rewrite !vcomp_assoc.
    rewrite <- interchange.
    rewrite vcomp_left_identity.
    pose (pentagon (id₁ Z) (id₁ Z) g f) as p.
    rewrite !vcomp_assoc in p.
    rewrite <- p ; clear p.
    rewrite <- !vcomp_assoc.
    rewrite <- triangle_r.
    rewrite !vcomp_assoc.
    rewrite assoc_right.
    rewrite vcomp_right_identity.
    rewrite assoc_natural.
    rewrite hcomp_id₂.
    reflexivity.
  Qed.

  Definition left_unit_inv_assoc
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : (left_unit_inv g) ▻ f = assoc_inv (id₁ Z) g f ∘ left_unit_inv (g · f).
  Proof.
    unfold bc_whisker_r, vcomp, id₂.
    rewrite <- !inverse_of_left_unit.
    rewrite <- inverse_of_assoc.
    rewrite <- inverse_compose.
    rewrite <- inverse_id.
    rewrite <- hcomp_inverse.
    apply path_inverse.
    apply left_unit_assoc.
  Qed.
  
  Definition right_unit_assoc
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : right_unit (g · f) = g ◅ (right_unit f) ∘ assoc g f (id₁ X).
  Proof.
    apply whisker_r_cancel_id.
    unfold bc_whisker_l, bc_whisker_r.
    rewrite <- (vcomp_left_identity (id₂ (id₁ X))).
    rewrite interchange.
    apply cancel_assoc_L.
    rewrite <- !vcomp_assoc.
    rewrite assoc_natural.
    rewrite triangle_r.
    rewrite <- (vcomp_left_identity (id₂ g)).
    rewrite interchange.
    rewrite !vcomp_assoc.
    pose (pentagon g f (id₁ X) (id₁ X)) as p.
    rewrite !vcomp_assoc in p.
    rewrite <- p ; clear p.
    rewrite vcomp_right_identity.
    rewrite <- !vcomp_assoc.
    rewrite <- assoc_natural.
    rewrite hcomp_id₂.
    rewrite <- triangle_l.
    rewrite !vcomp_assoc.
    rewrite assoc_right.
    rewrite vcomp_right_identity.
    reflexivity.
  Qed.
  
  Definition right_unit_inv_assoc
             {X Y Z : C}
             (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
    : right_unit_inv (g · f) = assoc_inv g f (id₁ X) ∘ (g ◅ (right_unit_inv f)).
  Proof.
    unfold bc_whisker_l, vcomp, id₂.
    rewrite <- !inverse_of_right_unit.
    rewrite <- inverse_of_assoc.
    rewrite <- inverse_id.
    rewrite <- hcomp_inverse.
    rewrite <- inverse_compose.    
    apply path_inverse.
    apply right_unit_assoc.
  Qed.

  Definition right_unit_id_is_left_unit_id
             `{Funext}
             (X : C)
    : right_unit (id₁ X) = left_unit (id₁ X).
  Proof.
    apply whisker_l_cancel_id.
    refine (_ @ vcomp_right_identity _).
    rewrite <- assoc_left.
    rewrite <- vcomp_assoc.
    rewrite <- inverse_of_assoc.
    apply Morphisms.iso_moveL_pV.
    rewrite <- triangle_r.
    refine ((vcomp_left_identity _)^ @ _ @ vcomp_left_identity _).
    rewrite <- right_unit_right.
    rewrite !vcomp_assoc.
    apply ap.
    pose @right_unit_assoc as p.
    unfold bc_whisker_l, vcomp in p.
    rewrite <- p ; clear p.
    rewrite (right_unit_natural (right_unit (id₁ X))).
    reflexivity.
  Qed.

  Definition right_unit_V_id_is_left_unit_V_id
             `{Funext}
             (X : C)
    : right_unit_inv (id₁ X) = left_unit_inv (id₁ X).
  Proof.
    symmetry.
    refine ((vcomp_right_identity _)^ @ _ @ vcomp_left_identity _).
    rewrite <- right_unit_left.
    rewrite <- vcomp_assoc.
    f_ap.
    rewrite right_unit_id_is_left_unit_id.
    apply left_unit_right.
  Qed.
End laws.
