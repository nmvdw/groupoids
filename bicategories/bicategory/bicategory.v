Require Import HoTT.
From HoTT.Categories Require Export
     Category Functor NaturalTransformation FunctorCategory.
From HoTT.Categories Require Import
     GroupoidCategory.
From GR.bicategories Require Import general_category.

Record BiCategory_d :=
  Build_BiCategory_d {
      Obj_d :> Type ;
      Hom_d : Obj_d -> Obj_d -> PreCategory ;
      id₁_d : forall (X : Obj_d), Hom_d X X ;
      hcomp_obj : forall {X Y Z : Obj_d},
          Hom_d Y Z * Hom_d X Y -> Hom_d X Z ;
      hcomp_hom : forall {X Y Z : Obj_d}
                        {f g : Hom_d Y Z * Hom_d X Y}
                        (η : morphism (Hom_d Y Z) (fst f) (fst g) *
                             morphism (Hom_d X Y) (snd f) (snd g)),
          morphism (Hom_d X Z) (hcomp_obj f) (hcomp_obj g) ;
      left_unit_d : forall {X Y : Obj_d}
                         (f : Hom_d X Y),
          morphism (Hom_d X Y) (hcomp_obj (id₁_d Y, f)) f ;
      left_unit_inv_d : forall {X Y : Obj_d}
                         (f : Hom_d X Y),
          morphism (Hom_d X Y) f (hcomp_obj (id₁_d Y, f)) ;
      right_unit_d : forall {X Y : Obj_d}
                         (f : Hom_d X Y),
          morphism (Hom_d X Y) (hcomp_obj (f, id₁_d X)) f ;
      right_unit_inv_d : forall {X Y : Obj_d}
                          (f : Hom_d X Y),
          morphism (Hom_d X Y) f (hcomp_obj (f, id₁_d X)) ;
      assoc_d : forall {W X Y Z : Obj_d}
                         (h : Hom_d Y Z)
                         (g : Hom_d X Y)
                         (f : Hom_d W X),
          morphism (Hom_d W Z)
                   (hcomp_obj (hcomp_obj (h, g), f))
                   (hcomp_obj (h, hcomp_obj (g, f))) ;
      assoc_inv_d : forall {W X Y Z : Obj_d}
                             (h : Hom_d Y Z)
                             (g : Hom_d X Y)
                             (f : Hom_d W X),
          morphism (Hom_d W Z)
                   (hcomp_obj (h, hcomp_obj (g, f)))
                   (hcomp_obj (hcomp_obj (h, g), f))
    }.

Ltac make_bicategory := simple refine (Build_BiCategory_d _ _ _ _ _ _ _ _ _ _ _).

Record is_bicategory (C : BiCategory_d)
  := Build_is_bicategory {
         hcomp_id_p :
           forall {X Y Z : C}
                  (f : Hom_d C Y Z * Hom_d C X Y),
           (hcomp_hom C (1 : morphism (Hom_d C Y Z * Hom_d C X Y) f f) = 1)%morphism ;
         hcomp_comp_p :
           forall {X Y Z : C}
                  {f g h : Hom_d C Y Z * Hom_d C X Y}
                  (η₂ : morphism (Hom_d C Y Z * Hom_d C X Y) g h)
                  (η₁ : morphism (Hom_d C Y Z * Hom_d C X Y) f g),
             (hcomp_hom C (η₂ o η₁) = hcomp_hom C η₂ o hcomp_hom C η₁)%morphism ;
         left_unit_natural_p :
           forall {X Y : C}
                  {f g : Hom_d C X Y}
                  (η : morphism (Hom_d C X Y) f g),
             ((left_unit_d C g)
                o @hcomp_hom C X Y Y (id₁_d C Y, f) (id₁_d C Y, g) (1,η)
              = η o left_unit_d C f)%morphism ;
         left_unit_inv_natural_p :
           forall {X Y : C}
                  {f g : Hom_d C X Y}
                  (η : morphism (Hom_d C X Y) f g),
             (left_unit_inv_d C g o η
              =
              (@hcomp_hom C X Y Y (id₁_d C Y, f) (id₁_d C Y, g) (1,η))
                o left_unit_inv_d C f)%morphism ;
         right_unit_natural_p :
           forall {X Y : C}
                  {f g : Hom_d C X Y}
                  (η : morphism (Hom_d C X Y) f g),
             ((right_unit_d C g)
                o @hcomp_hom C X X Y (f,id₁_d C X) (g,id₁_d C X) (η,1)
              = η o right_unit_d C f)%morphism ;
         right_unit_inv_natural_p :
           forall {X Y : C}
                  {f g : Hom_d C X Y}
                  (η : morphism (Hom_d C X Y) f g),
             (right_unit_inv_d C g o η
              =
              (@hcomp_hom C X X Y (f,id₁_d C X) (g,id₁_d C X) (η,1))
                o right_unit_inv_d C f)%morphism ;
         left_unit_left_p : forall {X Y : C}
                                 (f : Hom_d C X Y),
             (left_unit_d C f o left_unit_inv_d C f = 1)%morphism ;
         left_unit_right_p : forall {X Y : C}
                                 (f : Hom_d C X Y),
             (left_unit_inv_d C f o left_unit_d C f = 1)%morphism ;
         right_unit_left_p : forall {X Y : C}
                                 (f : Hom_d C X Y),
             (right_unit_d C f o right_unit_inv_d C f = 1)%morphism ;
         right_unit_right_p : forall {X Y : C}
                                 (f : Hom_d C X Y),
             (right_unit_inv_d C f o right_unit_d C f = 1)%morphism ;
         assoc_natural_p :
           forall {W X Y Z : C}
                  {h₁ h₂ : Hom_d C Y Z}
                  {g₁ g₂ : Hom_d C X Y}
                  {f₁ f₂ : Hom_d C W X}
                  (ηh : morphism (Hom_d C Y Z) h₁ h₂)
                  (ηg : morphism (Hom_d C X Y) g₁ g₂)
                  (ηf : morphism (Hom_d C W X) f₁ f₂),
             ((assoc_d C h₂ g₂ f₂)
                o (@hcomp_hom
                     C W X Z (_,f₁) (_,f₂)
                     (@hcomp_hom
                        C X Y Z (h₁,g₁) (h₂,g₂) 
                        (ηh, ηg), ηf)) =
              (@hcomp_hom
                 C W Y Z (h₁,_) (h₂,_)
                 (ηh, @hcomp_hom
                        C W X Y (g₁,f₁) (g₂,f₂)
                        (ηg, ηf)))
                o assoc_d C h₁ g₁ f₁)%morphism ;
         assoc_inv_natural_p :
           forall {W X Y Z : C}
                  {h₁ h₂ : Hom_d C Y Z}
                  {g₁ g₂ : Hom_d C X Y}
                  {f₁ f₂ : Hom_d C W X}
                  (ηh : morphism (Hom_d C Y Z) h₁ h₂)
                  (ηg : morphism (Hom_d C X Y) g₁ g₂)
                  (ηf : morphism (Hom_d C W X) f₁ f₂),
             ((assoc_inv_d C h₂ g₂ f₂)
                o (@hcomp_hom
                     C W Y Z (h₁,_) (h₂,_) 
                     (ηh, @hcomp_hom
                            C W X Y (g₁,f₁) (g₂,f₂)
                            (ηg, ηf))) =
              (@hcomp_hom
                 C W X Z (_,f₁) (_,f₂)
                 (@hcomp_hom
                    C X Y Z (h₁,g₁) (h₂,g₂)
                    (ηh, ηg), ηf))
                o assoc_inv_d C h₁ g₁ f₁)%morphism ;
         assoc_left_p :
           forall {W X Y Z : C}
                  (f : Hom_d C Y Z)
                  (g : Hom_d C X Y)
                  (h : Hom_d C W X),
             (assoc_d C f g h o assoc_inv_d C f g h = 1)%morphism ;
         assoc_right_p :
           forall {W X Y Z : C}
                  (f : Hom_d C Y Z)
                  (g : Hom_d C X Y)
                  (h : Hom_d C W X),
             (assoc_inv_d C f g h o assoc_d C f g h = 1)%morphism ;
         triangle_r_p :
           forall {X Y Z : C}
                  (g : Hom_d C Y Z)
                  (f : Hom_d C X Y),
             (@hcomp_hom
                C X Y Z (_,f) (g,f)
                (right_unit_d C g, 1) =
              (@hcomp_hom
                 C X Y Z (g,hcomp_obj C _) (g,f)
                (1, left_unit_d C f))
                o assoc_d C g (id₁_d C Y) f)%morphism ;
         pentagon_p :
           forall {V W X Y Z : C}
                  (k : Hom_d C Y Z) (h : Hom_d C X Y)
                  (g : Hom_d C W X) (f : Hom_d C V W),
             ((assoc_d C k h (hcomp_obj C (g, f)))
                o assoc_d C (hcomp_obj C (k, h)) g f
              =
              (@hcomp_hom
                 C V Y Z
                 (k,hcomp_obj C (hcomp_obj C (h, g), f))
                 (k,hcomp_obj C (h, hcomp_obj C (g, f)))
                 (1, assoc_d C h g f))
                o assoc_d C k (hcomp_obj C (h, g)) f
                o (@hcomp_hom
                     C _ _ _
                     (_,_) (_,_)
                     (assoc_d C k h g, 1)))%morphism
       }.

Ltac make_is_bicategory := simple refine (Build_is_bicategory _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).

Arguments hcomp_id_p {C} _ {X Y Z} f.
Arguments hcomp_comp_p {C} _ {X Y Z f g h} _ _.
Arguments left_unit_natural_p {C} _ {X Y f g} η.
Arguments left_unit_inv_natural_p {C} _ {X Y f g} η.
Arguments left_unit_left_p {C} _ {X Y} f.
Arguments left_unit_right_p {C} _ {X Y} f.
Arguments right_unit_natural_p {C} _ {X Y f g} η.
Arguments right_unit_inv_natural_p {C} _ {X Y f g} η.
Arguments right_unit_left_p {C} _ {X Y} f.
Arguments right_unit_right_p {C} _ {X Y} f.
Arguments assoc_natural_p {C} _ {W X Y Z h₁ h₂ g₁ g₂ f₁ f₂} ηh ηg ηf.
Arguments assoc_inv_natural_p {C} _ {W X Y Z h₁ h₂ g₁ g₂ f₁ f₂} ηh ηg ηf.
Arguments assoc_left_p {C} _ {W X Y Z} f g h.
Arguments assoc_right_p {C} _ {W X Y Z} f g h.
Arguments triangle_r_p {C} _ {X Y Z} g f.
Arguments pentagon_p {C} _ {V W X Y Z} k h g f.

Definition BiCategory
  := {C : BiCategory_d & is_bicategory C}.

Delimit Scope bicategory_scope with bicategory.
Bind Scope bicategory_scope with BiCategory.
Open Scope bicategory_scope.

Definition Build_BiCategory
           (C : BiCategory_d)
           (HC : is_bicategory C)
  : BiCategory
  := (C;HC).

Definition Obj : BiCategory -> Type
  := fun C => Obj_d C.1.

Coercion Obj : BiCategory >-> Sortclass.

Definition Hom (C : BiCategory)
  : Obj C -> Obj C -> PreCategory
  := Hom_d C.1.

Notation "C ⟦ X , Y ⟧ " := (Hom C X Y) (at level 60) : bicategory_scope.
Notation "f ==> g" := (morphism (Hom _ _ _) f g) (at level 60) : bicategory_scope.

Definition vcomp
           {C : BiCategory}
           {X Y : C}
           {f g h : C⟦X,Y⟧}
           (η₂ : g ==> h)
           (η₁ : f ==> g)
  : f ==> h
  := (η₂ o η₁)%morphism.

Arguments vcomp {C X Y f g h} η₂%bicategory η₁%bicategory.
Notation "η₂ '∘' η₁" := (vcomp η₂ η₁) (at level 41, left associativity) : bicategory_scope.

Definition vcomp_assoc
           {C : BiCategory}
           {X Y : C}
           {f g h k : C⟦X,Y⟧}
           (η₃ : h ==> k)
           (η₂ : g ==> h)
           (η₁ : f ==> g)
  : (η₃ ∘ η₂) ∘ η₁ = η₃ ∘ (η₂ ∘ η₁).
Proof.
  apply associativity.
Defined.

Definition id₂
           {C : BiCategory}
           {X Y : C}
           (f : C⟦X,Y⟧)
  : f ==> f
  := 1%morphism.

Definition vcomp_left_identity
           {C : BiCategory}
           {X Y : C}
           {f g : C⟦X,Y⟧}
           (η : f ==> g)
  : id₂ g ∘ η = η
  := left_identity _ _ _ _.

Definition vcomp_right_identity
           {C : BiCategory}
           {X Y : C}
           {f g : C⟦X,Y⟧}
           (η : f ==> g)
  : η ∘ id₂ f = η
  := right_identity _ _ _ _.

Definition id₁ {C : BiCategory}
  : forall (X : C), C⟦X,X⟧
  := id₁_d C.1.

Definition hcomp1 {C : BiCategory} {X Y Z : C}
  : C⟦Y,Z⟧ -> C⟦X,Y⟧ -> C⟦X,Z⟧
  := fun g f => hcomp_obj C.1 (g,f).

Arguments hcomp1 {C X Y Z} g%bicategory f%bicategory.
Notation "f '·' g" := (hcomp1 f g) (at level 41, left associativity) : bicategory_scope.

Definition hcomp2
           {C : BiCategory}
           {X Y Z : C}
           {f₁ g₁ : C⟦X,Y⟧}
           {f₂ g₂ : C⟦Y,Z⟧}
           (η₂ : f₂ ==> g₂)
           (η₁ : f₁ ==> g₁)
  : f₂ · f₁ ==> g₂ · g₁.
Proof.
  apply (hcomp_hom C.1) ; simpl.
  exact (η₂,η₁).
Defined.

Arguments hcomp2 {C X Y Z f₁ g₁ f₂ g₂} η₂%bicategory η₁%bicategory.
Notation "η₁ '*' η₂" := (hcomp2 η₁ η₂) (at level 40, left associativity) : bicategory_scope.

Definition interchange
           {C : BiCategory}
           {X Y Z : C}
           {f₁ g₁ h₁ : C⟦Y,Z⟧}
           {f₂ g₂ h₂ : C⟦X,Y⟧}
           (η₁ : f₁ ==> g₁) (η₂ : f₂ ==> g₂)
           (ε₁ : g₁ ==> h₁) (ε₂ : g₂ ==> h₂)
  : (ε₁ ∘ η₁) * (ε₂ ∘ η₂) = (ε₁ * ε₂) ∘ (η₁ * η₂)
  := @hcomp_comp_p _ C.2 X Y Z (f₁,f₂) (g₁,g₂) (h₁,h₂) (ε₁,ε₂) (η₁,η₂).

Definition hcomp_id₂
           {C : BiCategory}
           {X Y Z : C}
           (f₂ : C⟦Y, Z⟧) (f₁ : C⟦X,Y⟧)
  : id₂ f₂ * id₂ f₁ = id₂ (f₂ · f₁).
Proof.
  apply (hcomp_id_p C.2).
Defined.

Definition hcomp {C : BiCategory} (X Y Z : C)
  : Functor (Category.prod (C⟦Y,Z⟧) (C⟦X,Y⟧)) (C⟦X,Z⟧).
Proof.
  simple refine (Build_Functor _ _ _ _ _ _).
  - intros [g f].
    exact (g · f).
  - intros [f₁ f₂] [g₁ g₂] [η₁ η₂].
    exact (η₁ * η₂).
  - intros [f₁ f₂] [g₁ g₂] [h₁ h₂] [η₁ η₂] [ε₁ ε₂].
    cbn in *.
    apply interchange.
  - intros [f₁ f₂].
    cbn in *.
    apply hcomp_id₂.
Defined.

Definition left_unit
           {C : BiCategory}
           {X Y : C}
           (f : C⟦X, Y⟧)
  : id₁ Y · f ==> f
  := left_unit_d C.1 f.

Definition left_unit_natural
           {C : BiCategory}
           {X Y : C}
           {f g : C⟦X, Y⟧}
           (η : f ==> g)
  : left_unit g ∘ (id₂ (id₁ Y) * η) = η ∘ left_unit f
  := left_unit_natural_p C.2 η.

Definition left_unitor {C : BiCategory} (X Y : C)
  : NaturalTransformation
      (hcomp X Y Y o (const_functor (id₁ Y) * 1))
      1.
Proof.
  simple refine (Build_NaturalTransformation _ _ _ _).
  - exact left_unit.
  - intros ; apply left_unit_natural.
Defined.

Definition left_unit_inv
           {C : BiCategory}
           {X Y : C}
           (f : C⟦X, Y⟧)
  : f ==> id₁ Y · f
  := left_unit_inv_d C.1 f.

Definition left_unit_inv_natural
           {C : BiCategory}
           {X Y : C}
           {f g : C⟦X, Y⟧}
           (η : f ==> g)
  : left_unit_inv g ∘ η = (id₂ (id₁ Y) * η) ∘ left_unit_inv f
  := left_unit_inv_natural_p C.2 η.

Definition left_unitor_inv {C : BiCategory} (X Y : C)
  : NaturalTransformation
      1
      (hcomp X Y Y o (const_functor (id₁ Y) * 1)).
Proof.
  simple refine (Build_NaturalTransformation _ _ _ _).
  - exact left_unit_inv.
  - intros ; apply left_unit_inv_natural.
Defined.

Definition left_unit_left
           {C : BiCategory}
           {X Y : C}
           (f : C⟦X, Y⟧)
  : left_unit f ∘ left_unit_inv f = id₂ f
  := left_unit_left_p C.2 f.

Definition left_unitor_left `{Univalence} {C : BiCategory} (X Y : C)
  : (left_unitor X Y o left_unitor_inv X Y = 1)%natural_transformation.
Proof.
  apply path_natural_transformation.
  intros f ; cbn in *.
  exact (left_unit_left f).
Defined.

Definition left_unit_right
           {C : BiCategory}
           {X Y : C}
           (f : C⟦X, Y⟧)
  : left_unit_inv f ∘ left_unit f = id₂ (id₁ Y · f)
  := left_unit_right_p C.2 f.

Definition left_unitor_right `{Univalence} {C : BiCategory} (X Y : C)
  : (left_unitor_inv X Y o left_unitor X Y = 1)%natural_transformation.
Proof.
  apply path_natural_transformation.
  intros f ; cbn in *.
  exact (left_unit_right f).
Defined.

Definition right_unit
           {C : BiCategory}
           {X Y : C}
           (f : C⟦X, Y⟧)
  : f · id₁ X ==> f
  := right_unit_d C.1 f.

Definition right_unit_natural
           {C : BiCategory}
           {X Y : C}
           {f g : C⟦X, Y⟧}
           (η : f ==> g)
  : right_unit g ∘ (η * id₂ (id₁ X)) = η ∘ right_unit f
  := right_unit_natural_p C.2 η.

Definition right_unitor {C : BiCategory} (X Y : C)
  : NaturalTransformation
      (hcomp X X Y o (1 * const_functor (id₁ X)))
      1.
Proof.
  simple refine (Build_NaturalTransformation _ _ _ _).
  - exact right_unit.
  - intros ; apply right_unit_natural.
Defined.

Definition right_unit_inv
           {C : BiCategory}
           {X Y : C}
           (f : C⟦X, Y⟧)
  : f ==> f · id₁ X
  := right_unit_inv_d C.1 f.

Definition right_unit_inv_natural
           {C : BiCategory}
           {X Y : C}
           {f g : C⟦X, Y⟧}
           (η : f ==> g)
  : right_unit_inv g ∘ η = (η * id₂ (id₁ X)) ∘ right_unit_inv f
  := right_unit_inv_natural_p C.2 η.

Definition right_unitor_inv {C : BiCategory} (X Y : C)
  : NaturalTransformation
      1
      (hcomp X X Y o (1 * const_functor (id₁ X))).
Proof.
  simple refine (Build_NaturalTransformation _ _ _ _).
  - exact right_unit_inv.
  - intros ; apply right_unit_inv_natural.
Defined.

Definition right_unit_left
           {C : BiCategory}
           {X Y : C}
           (f : C⟦X, Y⟧)
  : right_unit f ∘ right_unit_inv f = id₂ f
  := right_unit_left_p C.2 f.

Definition right_unitor_left `{Univalence} {C : BiCategory} (X Y : C)
  : (right_unitor X Y o right_unitor_inv X Y = 1)%natural_transformation.
Proof.
  apply path_natural_transformation.
  intros f ; cbn in *.
  apply right_unit_left.
Qed.

Definition right_unit_right
           {C : BiCategory}
           {X Y : C}
           (f : C⟦X, Y⟧)
  : right_unit_inv f ∘ right_unit f = id₂ (f · id₁ X)
  := right_unit_right_p C.2 f.

Definition right_unitor_right `{Univalence} {C : BiCategory} (X Y : C)
  : (right_unitor_inv X Y o right_unitor X Y = 1)%natural_transformation.
Proof.
  apply path_natural_transformation.
  intros f ; cbn in *.
  apply right_unit_right.
Qed.

Definition assoc
           {C : BiCategory}
           {W X Y Z : C}
           (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧)
  : (h · g) · f ==> h · (g · f)
  := assoc_d C.1 h g f.

Definition assoc_natural
           {C : BiCategory}
           {W X Y Z : C}
           {h₁ h₂ : C⟦Y,Z⟧} {g₁ g₂ : C⟦X,Y⟧} {f₁ f₂ : C⟦W,X⟧}
           (ηh : h₁ ==> h₂)
           (ηg : g₁ ==> g₂)
           (ηf : f₁ ==> f₂)
  : assoc h₂ g₂ f₂ ∘ ((ηh * ηg) * ηf) = (ηh * (ηg * ηf)) ∘ assoc h₁ g₁ f₁
  := assoc_natural_p C.2 ηh ηg ηf.

Definition associator {C : BiCategory} (W X Y Z : C)
  : NaturalTransformation
      (hcomp W X Z o (hcomp X Y Z,1))
      ((hcomp W Y Z)
         o (1,hcomp W X Y)
         o assoc_prod (Hom C Y Z) (Hom C X Y) (Hom C W X)).
Proof.
  simple refine (Build_NaturalTransformation _ _ _ _).
  - intros [[h g] f] ; simpl in *.
    apply assoc.
  - intros [[h₁ g₁] f₁] [[h₂ g₂] f₂] [[ηh ηg] ηf] ; simpl in *.
    apply assoc_natural.
Defined.

Definition assoc_inv
           {C : BiCategory}
           {W X Y Z : C}
           (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧)
  : h · (g · f) ==> (h · g) · f
  := assoc_inv_d C.1 h g f.

Definition assoc_inv_natural
           {C : BiCategory}
           {W X Y Z : C}
           {h₁ h₂ : C⟦Y,Z⟧} {g₁ g₂ : C⟦X,Y⟧} {f₁ f₂ : C⟦W,X⟧}
           (ηh : h₁ ==> h₂)
           (ηg : g₁ ==> g₂)
           (ηf : f₁ ==> f₂)
  : assoc_inv h₂ g₂ f₂ ∘ (ηh * (ηg * ηf)) = ((ηh * ηg) * ηf) ∘ assoc_inv h₁ g₁ f₁
  := assoc_inv_natural_p C.2 ηh ηg ηf.

Definition associator_inv {C : BiCategory} (W X Y Z : Obj C)
  : NaturalTransformation
      ((hcomp W Y Z)
         o (1,hcomp W X Y)
         o assoc_prod (Hom C Y Z) (Hom C X Y) (Hom C W X))
      (hcomp W X Z o (hcomp X Y Z,1)).
Proof.
  simple refine (Build_NaturalTransformation _ _ _ _).
  - intros [[h g] f] ; simpl in *.
    apply assoc_inv.
  - intros [[h₁ g₁] f₁] [[h₂ g₂] f₂] [[ηh ηg] ηf] ; simpl in *.
    apply assoc_inv_natural.
Defined.

Definition assoc_left
           {C : BiCategory}
           {W X Y Z : C}
           (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧)
  : assoc h g f ∘ assoc_inv h g f = id₂ (h · (g · f))
  := assoc_left_p C.2 h g f.

Definition associator_left `{Univalence} {C : BiCategory} (W X Y Z : C)
  : (associator W X Y Z o associator_inv W X Y Z = 1)%natural_transformation.
Proof.
  apply path_natural_transformation.
  intros f.
  apply assoc_left.
Qed.

Definition assoc_right
           {C : BiCategory}
           {W X Y Z : C}
           (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧)
  : assoc_inv h g f ∘ assoc h g f = id₂ ((h · g) · f)
  := assoc_right_p C.2 h g f.

Definition associator_right `{Univalence} {C : BiCategory} (W X Y Z : C)
  : (associator_inv W X Y Z o associator W X Y Z = 1)%natural_transformation.
Proof.
  apply path_natural_transformation.
  intros f.
  apply assoc_right.
Qed.

Instance left_unit_iso
         {C : BiCategory}
         {X Y : C}
         (f : C⟦X,Y⟧)
  : IsIsomorphism (left_unit f).
Proof.
  simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
  - exact (left_unit_inv f).
  - apply left_unit_right.
  - apply left_unit_left.
Defined.

Instance left_unit_inv_iso
         {C : BiCategory}
         {X Y : C}
         (f : C⟦X,Y⟧)
  : IsIsomorphism (left_unit_inv f).
Proof.
  simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
  - exact (left_unit f).
  - apply left_unit_left.
  - apply left_unit_right.
Defined.

Definition inverse_of_left_unit
           {C : BiCategory}
           {X Y : C}
           (f : C⟦X,Y⟧)
  : morphism_inverse (left_unit f) = left_unit_inv f
  := idpath.

Instance left_unitor_iso `{Univalence} {C : BiCategory} (X Y : C)
  : @IsIsomorphism (_ -> _) _ _ (left_unitor X Y).
Proof.
  simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
  - exact (left_unitor_inv X Y).
  - apply left_unitor_right.
  - apply left_unitor_left.
Defined.

Definition inverse_of_left_unitor
           `{Univalence}
           {C : BiCategory}
           (X Y : C)
  : @morphism_inverse (_ -> _) _ _ (left_unitor X Y) _ = left_unitor_inv X Y
  := idpath.

Instance right_unit_iso
         {C : BiCategory}
         {X Y : C}
         (f : C⟦X,Y⟧)
  : IsIsomorphism (right_unit f).
Proof.
  simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
  - exact (right_unit_inv f).
  - apply right_unit_right.
  - apply right_unit_left.
Defined.

Instance right_unit_inv_iso
         {C : BiCategory}
         {X Y : C}
         (f : C⟦X,Y⟧)
  : IsIsomorphism (right_unit_inv f).
Proof.
  simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
  - exact (right_unit f).
  - apply right_unit_left.
  - apply right_unit_right.
Defined.

Definition inverse_of_right_unit
           {C : BiCategory}
           {X Y : C}
           (f : C⟦X,Y⟧)
  : morphism_inverse (right_unit f) = right_unit_inv f
  := idpath.

Instance right_unitor_iso `{Univalence} {C : BiCategory} (X Y : C)
  : @IsIsomorphism (_ -> _) _ _ (right_unitor X Y).
Proof.
  simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
  - exact (right_unitor_inv X Y).
  - apply right_unitor_right.
  - apply right_unitor_left.
Defined.

Definition inverse_of_right_unitor
           `{Univalence}
           {C : BiCategory}
           (X Y : C)
  : @morphism_inverse (_ -> _) _ _ (right_unitor X Y) _ = right_unitor_inv X Y
  := idpath.

Instance assoc_iso
         {C : BiCategory}
         {W X Y Z : C}
         (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧)
  : IsIsomorphism (assoc h g f).
Proof.
  simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
  - exact (assoc_inv h g f).
  - apply assoc_right.
  - apply assoc_left.
Defined.

Instance assoc_inv_iso
         {C : BiCategory}
         {W X Y Z : C}
         (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧)
  : IsIsomorphism (assoc_inv h g f).
Proof.
  simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
  - exact (assoc h g f).
  - apply assoc_left.
  - apply assoc_right.
Defined.

Definition inverse_of_assoc
           {C : BiCategory}
           {W X Y Z : C}
           (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧)
  : morphism_inverse (assoc h g f) = assoc_inv h g f
  := idpath.

Instance associator_iso
         `{Univalence}
         {C : BiCategory}
         (W X Y Z : C)
  : @IsIsomorphism (_ -> _) _ _ (associator W X Y Z).
Proof.
  simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
  - exact (associator_inv W X Y Z).
  - apply associator_right.
  - apply associator_left.
Defined.

Definition inverse_of_associator
           `{Univalence}
           {C : BiCategory}
           (W X Y Z : C)
  : @morphism_inverse (_ -> _) _ _ (associator W X Y Z) _ = associator_inv W X Y Z
  := idpath.

Definition triangle_r
           {C : BiCategory}
           {X Y Z : C}
           (g : C⟦Y,Z⟧)
           (f : C⟦X,Y⟧)
  : right_unit g * id₂ f = (id₂ g * left_unit f) ∘ assoc g (id₁ Y) f
  := triangle_r_p C.2 g f.

Definition pentagon
           {C : BiCategory}
           {V W X Y Z : C}
           (k : C⟦Y,Z⟧) (h : C⟦X,Y⟧) (g : C⟦W,X⟧) (f : C⟦V,W⟧)
  : (assoc k h (g · f) ∘ assoc (k · h) g f)
    =
    (id₂ k * assoc h g f) ∘ assoc k (h · g) f ∘ (assoc k h g * id₂ f)
  := pentagon_p C.2 k h g f.

Global Instance hcomp_iso
       {C : BiCategory}
       {X Y Z : C}
       {f₁ g₁ : C⟦Y,Z⟧} {f₂ g₂ : C⟦X,Y⟧}
       (η₁ : f₁ ==> g₁) (η₂ : f₂ ==> g₂)
       `{IsIsomorphism _ _ _ η₁} `{IsIsomorphism _ _ _ η₂}
  : IsIsomorphism (η₁ * η₂).
Proof.
  apply (@Morphisms.iso_functor _ _ (hcomp X Y Z) (f₁,f₂) (g₁,g₂) (η₁,η₂)).
  apply iso_pair ; assumption.
Defined.

Definition hcomp_inverse
           {C : BiCategory}
           {X Y Z : C}
           {f₁ g₁ : C⟦Y,Z⟧} {f₂ g₂ : C⟦X,Y⟧}
           (η₁ : f₁ ==> g₁) (η₂ : f₂ ==> g₂)
           `{IsIsomorphism _ _ _ η₁} `{IsIsomorphism _ _ _ η₂}
  : ((η₁ * η₂)^-1 = η₁^-1 * η₂^-1)%morphism
  := idpath.

Definition bc_whisker_l
           {C : BiCategory}
           {X Y Z : C}
           {f₁ : C⟦X,Y⟧} {f₂ : C⟦X,Y⟧}
           (g : C⟦Y,Z⟧)
           (α : f₁ ==> f₂)
  : (g · f₁) ==> (g · f₂)
  := id₂ g * α.

Notation "g '◅' α" := (bc_whisker_l g α) (at level 40) : bicategory_scope.

Definition bc_whisker_l_id₂
           {C : BiCategory}
           {X Y Z : C}
           (f : C⟦X,Y⟧)
           (g : C⟦Y,Z⟧)
  : g ◅ (id₂ f) = id₂ (g · f)
  := hcomp_id₂ g f.

Definition bc_whisker_r
           {C : BiCategory}
           {X Y Z : C}
           {g₁ : C⟦Y,Z⟧} {g₂ : C⟦Y,Z⟧}
           (β : g₁ ==> g₂)
           (f : C⟦X,Y⟧)
  : (g₁ · f) ==> (g₂ · f)
  := β * id₂ f.

Notation "β '▻' f" := (bc_whisker_r β f) (at level 40) : bicategory_scope.

Definition bc_whisker_r_id₂
           {C : BiCategory}
           {X Y Z : C}
           (f : C⟦X,Y⟧)
           (g : C⟦Y,Z⟧)
  : (id₂ g) ▻ f = id₂ (g · f)
  := hcomp_id₂ g f.

Definition is_21 `{Funext} (C : BiCategory)
  : hProp
  := BuildhProp (forall (X Y : C), IsGroupoid (C⟦X,Y⟧)).
