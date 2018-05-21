(** A 2-category is a bicategory in which every Hom-set is a Category.
    In a 2-category the axioms for composition hold "on the nose". *)
Require Import HoTT.
From GR.bicategories Require Import bicategory.bicategory.
From HoTT.Categories Require Import Category.Univalent.

Notation Is2Category B := (forall s d : Obj B, IsCategory (Hom _ s d)).

Section TwoCategoryAxioms.
  Context `{Univalence}.
  Local Open Scope bicategory_scope.

  Variable (B : BiCategory).
  Context `{Is2Category B}.

  Lemma un_l_eq {X Y : B} (f : Hom _ X Y) :
    id_m Y ⋅ f = f.
  Proof.
    apply (isotoid (Hom _ X Y) _ _).
    simple refine {| morphism_isomorphic := un_l X Y f |}.
  Defined.

  Lemma un_r_eq {X Y : B} (f : Hom _ X Y) :
    f ⋅ id_m X = f.
  Proof.
    apply (isotoid (Hom _ X Y) _ _).
    simple refine {| morphism_isomorphic := un_r X Y f |}.
  Defined.

  Lemma asssoc_eq {W X Y Z : B}
          (f : Hom _ W X)
          (g : Hom _ X Y)
          (h : Hom _ Y Z) :
    (h ⋅ g) ⋅ f = h ⋅ (g ⋅ f).
  Proof.
    apply (isotoid (Hom _ W Z) _ _).
    simple refine {| morphism_isomorphic := assoc W X Y Z (h, g, f) |}.
  Defined.
End TwoCategoryAxioms.
