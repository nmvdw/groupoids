Require Import HoTT.
Require Import HoTT.Categories.Functor.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory_laws
     bicategory.adjoint.

Class LocallyUnivalent (C : BiCategory)
  := locally_univalent :> forall (X Y : C), IsCategory (C⟦X,Y⟧).

Global Instance ishprop_LocallyUnivalent `{Funext} (C : BiCategory)
  : IsHProp (LocallyUnivalent C).
Proof.
  unfold LocallyUnivalent.
  apply _.
Defined.

Class Univalent_0 `{Funext} (C : BiCategory)
  := univalent_0 :> forall (X Y : C), IsEquiv(id_to_adjequiv X Y).

Notation adjequiv_to_id X Y e := ((id_to_adjequiv X Y)^-1%function e).

Global Instance ishprop_Univalent_0 `{Funext} (C : BiCategory)
  : IsHProp (Univalent_0 C).
Proof.
  unfold Univalent_0.
  apply _.
Defined.

Class Univalent `{Funext} (C : BiCategory)
  := { Univalent_Univalent_0 :> Univalent_0 C;
       Univalent_LocallyUnivalent :> LocallyUnivalent C }.

Global Instance univalent_hprop `{Funext} (C : BiCategory)
  : IsHProp (Univalent C).
Proof.
  apply hprop_allpath.
  intros x y.
  destruct x as [x1 x2], y as [y1 y2].
  assert (x1 = y1) as ->.
  { apply path_ishprop. }
  assert (x2 = y2) as ->.
  { apply path_ishprop. }
  reflexivity.
Defined.

Global Instance hom_locally_univalent_cat
       `{Univalence}
       {C : BiCategory}
       {UC : LocallyUnivalent C}
       (X Y : C)
  : IsTrunc 1 (C⟦X,Y⟧)
  := _.

Global Instance obj_univalent_cat
       `{Univalence}
       (C : BiCategory)
       `{Univalent C}
  : IsTrunc 2 C.
Proof.
  intros X Y.
  rewrite (path_universe (id_to_adjequiv X Y)).
  apply _.
Defined.

Definition strict_left_unit
           `{Univalence}
           {C : BiCategory}
           `{LocallyUnivalent C}
           {X Y : C}
           (f : C⟦X, Y⟧)
  : id₁ Y · f = f.
Proof.
  apply (isotoid (C⟦X,Y⟧) _ _).
  exact {| morphism_isomorphic := left_unit f |}.
Defined.

Definition strict_right_unit
           `{Univalence}
           {C : BiCategory}
           `{LocallyUnivalent C}
           {X Y : C}
           (f : C⟦X, Y⟧)
  : f · id₁ X = f.
Proof.
  apply (isotoid (C⟦X,Y⟧) _ _).
  exact {| morphism_isomorphic := right_unit f |}.
Defined.

Definition strict_assoc
           `{Univalence}
           {C : BiCategory}
           `{LocallyUnivalent C}
           {W X Y Z : C}
           (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧)
  : (h · g) · f = h · (g · f).
Proof.
  apply (isotoid (C⟦W,Z⟧) _ _).
  exact {| morphism_isomorphic := assoc h g f |}.
Defined.

Definition whisker_l_functor
           {C : BiCategory}
           `{LocallyUnivalent C}
           {Y Z : C}
           (X : C)
           (g : C⟦Y,Z⟧)
  : Functor (C⟦X,Y⟧) (C⟦X,Z⟧).
Proof.
  simple refine (Build_Functor _ _ _ _ _ _).
  - exact (fun f => g · f).
  - intros ? ? q.
    exact (g ◅ q).
  - intros ; cbn.
    apply bc_whisker_l_compose.
  - intros ; cbn.
    apply hcomp_id₂.
Defined.

Definition transport_whisker_l
           `{Funext}
           {C : BiCategory}
           `{LocallyUnivalent C}
           {X Y Z : C}
           (g : C⟦Y,Z⟧)
           {f₁ f₂ : C⟦X,Y⟧}
           (q : f₁ ==> f₂)
           `{IsIsomorphism _ _ _ q}
  : ap (fun z => g · z) (isotoid (C⟦X,Y⟧) f₁ f₂ {| morphism_isomorphic := q|})
    =
    isotoid (C⟦X,Z⟧) (g · f₁) (g · f₂) {|morphism_isomorphic := g ◅ q|}.
Proof.
  symmetry.
  rewrite <- (eissect (@Category.idtoiso (C⟦X,Z⟧) (g · f₁) (g · f₂))).
  f_ap.
  simple refine (path_isomorphic _ _ _).
  rewrite <- (idtoiso_functor _ (whisker_l_functor X g)) ; cbn.
  rewrite eisretr.
  reflexivity.
Defined.

Definition whisker_r_functor
           {C : BiCategory}
           `{LocallyUnivalent C}
           {X Y : C}
           (Z : C)
           (g : C⟦X,Y⟧)
  : Functor (C⟦Y,Z⟧) (C⟦X,Z⟧).
Proof.
  simple refine (Build_Functor _ _ _ _ _ _).
  - exact (fun f => f · g).
  - intros ? ? q ; cbn.
    exact (q ▻ g).
  - intros ; cbn.
    apply bc_whisker_r_compose.
  - intros ; cbn.
    apply hcomp_id₂.
Defined.

Definition transport_whisker_r
           `{Funext}
           {C : BiCategory}
           `{LocallyUnivalent C}
           {X Y Z : C}
           (g : C⟦X,Y⟧)
           {f₁ f₂ : C⟦Y,Z⟧}
           (q : f₁ ==> f₂)
           `{IsIsomorphism _ _ _ q}
  : ap (fun z => z · g) (isotoid (C⟦Y,Z⟧) f₁ f₂ {| morphism_isomorphic := q|})
    =
    isotoid (C⟦X,Z⟧) (f₁ · g) (f₂ · g) {|morphism_isomorphic := q ▻ g|}.
Proof.
  symmetry.
  rewrite <- (eissect (@Category.idtoiso (C⟦X,Z⟧) (f₁ · g) (f₂ · g))).
  f_ap.
  simple refine (path_isomorphic _ _ _).
  rewrite <- (idtoiso_functor _ (whisker_r_functor Z g)) ; cbn.
  rewrite eisretr.
  reflexivity.
Defined.

Definition isotoid_compose
           {C : PreCategory}
           {X Y Z : C}
           (f : (X <~=~> Y)%category) (g : (Y <~=~> Z)%category)
           `{IsCategory C}
  : isotoid C X Z (isomorphic_trans f g)
    =
    isotoid C X Y f @ isotoid C Y Z g.
Proof.
  rewrite <- (eissect (@Category.Morphisms.idtoiso C X Z)).
  f_ap.
  apply path_isomorphic.
  rewrite <- idtoiso_comp.
  rewrite !eisretr ; simpl.
  reflexivity.
Qed.

Definition strict_triangle_r
           `{Univalence}
           {C : BiCategory}
           `{LocallyUnivalent C}
           {X Y Z : C}
           (g : C⟦Y,Z⟧)
           (f : C⟦X,Y⟧)
  : ap (fun z => z · f) (strict_right_unit g)
    =
    strict_assoc g (id₁ Y) f @ ap (fun z => g · z) (strict_left_unit f).
Proof.
  rewrite transport_whisker_l, transport_whisker_r.
  unfold strict_assoc.
  rewrite <- isotoid_compose.
  f_ap.
  apply path_isomorphic ; cbn.
  apply triangle_r.
Qed.

Definition strict_pentagon
           `{Univalence}
           {C : BiCategory}
           `{LocallyUnivalent C}
           {V W X Y Z : C}
           (k : C⟦Y,Z⟧) (h : C⟦X,Y⟧)
           (g : C⟦W,X⟧) (f : C⟦V,W⟧)
  : strict_assoc (k · h) g f @ strict_assoc k h (g · f)
    = (ap (fun z => z · f) (strict_assoc k h g))
        @ ((strict_assoc k (h · g) f)
             @ ap (fun z => k · z) (strict_assoc h g f)).
Proof.
  rewrite transport_whisker_l, transport_whisker_r.
  unfold strict_assoc.
  rewrite <- !isotoid_compose.
  f_ap.
  apply path_isomorphic ; cbn.
  apply pentagon.
Qed.