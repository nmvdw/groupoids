Require Import HoTT.
From GR.bicategories Require Import
     yoneda_lemma
     bicategory.bicategory
     bicategory.strict
     bicategory.locally_strict
     bicategory.examples.arrow_subcategory
     bicategory.examples.full_sub
     bicategory.examples.image
     bicategory.examples.lax_functors_bicat
     bicategory.examples.pseudo_functors_bicat
     lax_functor.lax_functor
     lax_functor.weak_equivalence
     lax_functor.examples.yoneda
     lax_functor.examples.restrict_image_functor
     lax_functor.examples.image_restriction.

Definition rezk_completion
           `{Univalence}
           (C : BiCategory)
  : weak_equivalence (restrict_image (yoneda C)).
Proof.
  split.
  - refine (image_local_equivalence _ _).
    apply yoneda_local_equivalence.
  - apply image_essentialy_surjective.
Defined.

Definition strict_rezk_completion
           `{Univalence}
           (C : BiCategory)
           `{LocallyStrict C}
  : {D : BiCategory & {F : LaxFunctor C D & weak_equivalence F * is_2category D}}%type.
Proof.
  exists (image (strict_yoneda C)).
  exists (restrict_image (strict_yoneda C)).
  split.
  - split.
    + refine (restrict_image_functor_local_equivalence _ _ _ _).
      apply yoneda_local_equivalence.
    + apply image_essentialy_surjective.
  - apply _.
Defined.